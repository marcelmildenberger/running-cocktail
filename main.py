# running_cocktail_scheduler.py
# -*- coding: utf-8 -*-
"""
Planer für 'Running Cocktail' Mannheim

Funktionen:
- CSV einlesen (deutsche Spaltennamen)
- Entfernungen via OpenStreetMap-Dienste:
    * Nominatim (Geocoding) — kostenlos, bitte eigenen User-Agent/Email setzen
    * OSRM Table API (Distanzmatrix)
- Gruppen in 3 Ringe (außen/mittel/innen) einteilen
- 3 Runden mit Stations-Trios (Host + 2 Gäste) planen:
    * jede Gruppe hostet genau 1x
    * niemand trifft dieselbe Gruppe zweimal
    * Fachschaften (FIM/VWL) möglichst gemischt
    * Weg verläuft für alle: außen -> innen
- Itineraries & Runden-Übersichten exportieren (CSV/Excel)

Aufruf:
    python main.py RuCo.csv result

Benötigte Pakete: pandas, requests, (optional) openpyxl
"""

import os
import random
import argparse
import itertools
import time
from collections import defaultdict

import pandas as pd
import requests
import re


# ----------------------------
# Konfiguration
# ----------------------------

# Spaltennamen (so wie du sie beschrieben hast)
COL_FACHSCHAFT = "faculty"
COL_NAME_1 = "nameregistered"
COL_MAIL = "email"
COL_PHONE = "phone"
COL_NAME_2 = "namepartner"
COL_ALK = "alcohol"
COL_ALLERGY = "allergies"
COL_KLINGEL = "ring"
COL_STREET = "address"
COL_PLZ = "zip"
COL_STADTTEIL = "neighbourhood"
COL_STADT = "city"

# Schloss Mannheim – wird (best effort) geokodiert; falls offline: Fallback-Koordinaten
SCHLOSS_QUERY = "Parkring 39"

# Standard: je Station 2 Gäste (Host + 2 Gäste = 3 Gruppen)
DEFAULT_GUESTS_PER_HOST = 2

# Reise-Distanz-Grenzen (Meter) zwischen zwei Runden
TRAVEL_SOFT_LIMIT_M = 1200    # alles darunter gilt als unkritisch
TRAVEL_HARD_LIMIT_M = 2600    # darüber nur wenn keine Alternative existiert
TRAVEL_FAILOVER_PENALTY = 1e6


# ----------------------------
# Hilfsfunktionen
# ----------------------------

def normalize_fachschaft(s: str) -> str:
    if not isinstance(s, str):
        return "UNBEKANNT"
    s_low = s.strip().lower()
    if "vwl" in s_low:
        return "VWL"
    if "fim" in s_low:
        return "FIM"
    if "split" in s_low:
        return "SPLIT"
    if "mkw" in s_low:
        return "MKW"
    # Fallback: erstes Wort groß
    return s.strip().upper()


def build_full_address(row) -> str:
    """Baut eine Adresse für Geocoding/OSRM: "Straße Hausnr, PLZ Stadt, Germany".
    Wichtige Regeln:
      - **neighbourhood wird NICHT eingefügt** (führt häufig zu Fehlertreffern)
      - Mannheimer Quadrate wie "F4, 16" / "F 4, 16" -> "F4 16"
      - Falls im Straßenfeld Kommas vorkommen (z.B. "Steubenstraße 80, 304"), wird nur der **erste** Teil verwendet
      - ß -> ss als Fallback
    """
    def _norm_quadrate(s: str) -> str:
        if not isinstance(s, str):
            return ""
        s = " ".join(s.strip().split())
        # Nur ersten Teil vor einem Komma nehmen (Apartment/Suite entfernen)
        if "," in s:
            s = s.split(",", 1)[0].strip()
        # Muster: "F4, 16" / "F 4, 16" / "F4,16" -> "F4 16"
        s = re.sub(r"^([A-Za-z])\s*([0-9]+)\s*,\s*([0-9]+)(\b|$)", r"\1\2 \3", s)
        # Muster: "F 4 16" -> "F4 16"
        s = re.sub(r"^([A-Za-z])\s+([0-9]+)\s+([0-9]+)(\b|$)", r"\1\2 \3", s)
        # Fallback: ß -> ss, verbessert teils die Trefferquote
        s = s.replace("ß", "ss")
        return s

    street_raw = (row.get(COL_STREET) or "").strip()
    street = _norm_quadrate(street_raw)

    plz = (row.get(COL_PLZ) or "").strip()
    city = (row.get(COL_STADT) or "").strip() or "Mannheim"
    city = city.replace("ß", "ss")

    # Keine Verwendung von neighbourhood (COL_STADTTEIL) — explizit weglassen!

    # Rechte Seite (PLZ Stadt) sauber bauen
    right = f"{plz} {city}".strip()
    right = " ".join(right.split())

    if street and right:
        addr = f"{street}, {right}, Germany"
    elif street:
        addr = f"{street}, Mannheim, Germany"
    elif right:
        addr = f"{right}, Germany"
    else:
        addr = "Mannheim, Germany"

    return " ".join(addr.split())


def compute_travel_penalty(distance_m):
    """
    Liefert eine Strafzahl für den Weg zwischen zwei Runden.
    Kleinere Werte sind besser – sie werden vom Score subtrahiert.
    """
    if distance_m is None:
        return TRAVEL_FAILOVER_PENALTY

    km = distance_m / 1000.0
    # Bis zur soften Grenze: moderate lineare Penalty
    if distance_m <= TRAVEL_SOFT_LIMIT_M:
        return km * 0.8

    # Zwischen softem und hartem Limit: Penalty steigt deutlich stärker
    over_soft = distance_m - TRAVEL_SOFT_LIMIT_M
    penalty = (TRAVEL_SOFT_LIMIT_M / 1000.0) * 0.8
    penalty += over_soft / 320.0  # ~3 Zusatzpunkte pro km oberhalb Soft-Limit

    if distance_m >= TRAVEL_HARD_LIMIT_M:
        over_hard = distance_m - TRAVEL_HARD_LIMIT_M
        penalty += 8.0 + over_hard / 120.0  # hohe Strafe für sehr lange Wege

    return penalty


def is_faculty_mix_valid(host_id, guest_ids, groups):
    """
    Prüft, ob Host + Gäste nicht ausschließlich aus derselben Fachschaft bestehen,
    sobald mindestens drei Gruppen beteiligt sind.
    """
    faculties = [groups[host_id]["Fach"]]
    faculties.extend(groups[g]["Fach"] for g in guest_ids)
    if len(faculties) < 3:
        return True
    return len(set(faculties)) > 1


def split_into_three_bands_by_distance(df: pd.DataFrame, dist_col: str, seed: int):
    """
    Teilt DataFrame-Index (Gruppen) in 3 Bänder (außen, mittel, innen),
    wobei die Größen sich nur um höchstens 1 unterscheiden.
    Sortiert nach Distanz absteigend (außen zuerst).
    Gibt dict: group_id -> host_round (1=außen, 2=mittel, 3=innen)
    """
    # Sortiert nach Distanz absteigend (außen zuerst) und NICHT mischen,
    # damit Runde 1 wirklich außen, Runde 2 mittel, Runde 3 innen ist.
    df_sorted = df.sort_values(dist_col, ascending=False).copy()
    n = len(df_sorted)
    base = n // 3
    rem = n % 3
    sizes = [base + (1 if i < rem else 0) for i in range(3)]  # Summe = n, so balanciert wie möglich

    idxs = list(df_sorted.index)

    bands = {}
    start = 0
    for i, size in enumerate(sizes, start=1):
        for gid in idxs[start:start+size]:
            bands[gid] = i  # 1, 2 oder 3
        start += size
    return bands


def compute_host_capacities(num_hosts: int, num_available_guests: int, default_per_host=2):
    """
    Verteilt die verfügbaren Gäste-Slots fair auf Hosts.
    Rückgabe: Liste mit Kapazitäten (z.B. [2,2,2,...] oder [2,2,3,2,...])
    Summe == num_available_guests
    """
    if num_hosts <= 0:
        return []
    base = num_available_guests // num_hosts
    rem = num_available_guests % num_hosts

    # In der Praxis soll base ≈ 2 sein
    caps = [base] * num_hosts
    for i in range(rem):
        caps[i] += 1  # ein paar Hosts bekommen +1 Gast
    return caps


def collect_allergy_notes(group_ids, groups, exclude_ids=None):
    """
    Liefert eine formattierte Liste an Allergie-Hinweisen für die angegebenen Gruppen.
    exclude_ids: optionale Iterable von Gruppen, die ignoriert werden sollen.
    """
    exclude = set(exclude_ids or [])
    notes = []
    for gid in group_ids:
        if gid in exclude:
            continue
        text = (groups.get(gid, {}).get("Allergien") or "").strip()
        if not text:
            continue
        notes.append(text)
    # Doppelte Einträge entfernen, Reihenfolge beibehalten
    seen = []
    for note in notes:
        if note not in seen:
            seen.append(note)
    return " | ".join(seen)


def schedule_round(host_ids, guest_ids, groups, round_no, rng, encounters, prev_locations, addr_dist_map, center_addr):
    """
    Weist jedem Host eine Anzahl Gäste (1..3) zu, so dass:
      - Jeder Gast genau 1x in dieser Runde zugeteilt wird.
      - Wiederholte Begegnungen vermieden werden.
      - Strecken möglichst kurz bleiben (kontinuierliche Wege zwischen Runden).
    'groups' ist ein Dict group_id -> dict mit 'Fach', 'Name', 'Adresse', etc.
    encounters[group_id] = set(bisher getroffene Gruppen)
    prev_locations[group_id] = Adresse (letzter Standort nach voriger Runde)
    addr_dist_map: dict[Adresse][Adresse] = Distanz in Meter (int|None)
    center_addr: Adresse des Zentrums (Schloss)
    """
    rng.shuffle(host_ids)
    rng.shuffle(guest_ids)

    n_hosts = len(host_ids)
    caps = compute_host_capacities(n_hosts, len(guest_ids), DEFAULT_GUESTS_PER_HOST)

    assignments = []  # Liste von dicts: {"host": h, "guests":[g1,g2,...]}
    guest_pool = set(guest_ids)

    def has_repeat_encounter(h, g, co_guests):
        """Return True if host or any already chosen guests met candidate before."""
        if g in encounters[h]:
            return True
        for other in co_guests:
            if g in encounters[other]:
                return True
        return False

    def pair_score(h, g, co_guests):
        # Höhere Punkte = besser
        # Vermeide Wiederholungs-Begegnungen hart, halte Fachschaften gemischt,
        # bestrafe lange Laufwege und ziehe Runde-3-Hosts Richtung Schloss.
        score = 0.0
        if has_repeat_encounter(h, g, co_guests):
            return float("-inf")

        if not is_faculty_mix_valid(h, co_guests + [g], groups):
            return float("-inf")

        prev_addr = prev_locations.get(g, groups[g]["Adresse"])
        host_addr = groups[h]["Adresse"]
        d = addr_dist_map.get(prev_addr, {}).get(host_addr)
        score -= compute_travel_penalty(d)

        if round_no == 3:
            d_center = addr_dist_map.get(host_addr, {}).get(center_addr)
            if d_center is None:
                d_center = 1e6
            score -= 0.3 * (d_center / 1000.0)

        score += rng.random() * 1e-3
        return score

    # Zuteilung pro Host
    for host, cap in zip(host_ids, caps):
        chosen = []
        # Wähle 'cap' Gäste nacheinander
        for _ in range(cap):
            if not guest_pool:
                break
            # Kandidaten: alle noch freien Gäste
            best_g = None
            best_s = float("-inf")
            for g in guest_pool:
                s = pair_score(host, g, chosen)
                if s > best_s:
                    best_s = s
                    best_g = g
            if best_g is None:
                break
            chosen.append(best_g)
            guest_pool.remove(best_g)

        assignments.append({"host": host, "guests": chosen})

        if chosen:
            # Begegnungen registrieren (Host <-> Gäste und Gäste untereinander)
            for g in chosen:
                encounters[host].add(g)
                encounters[g].add(host)
            for a, b in itertools.combinations(chosen, 2):
                encounters[a].add(b)
                encounters[b].add(a)

    # Falls aus irgendeinem Grund noch Gäste übrig sind (sollte nicht passieren, aber safety net):
    if guest_pool:
        # Hänge übrig gebliebene Gäste an Hosts mit der kleinsten Belegung
        for g in list(guest_pool):
            placed = False
            for pack in sorted(assignments, key=lambda x: len(x["guests"])):
                h = pack["host"]
                if has_repeat_encounter(h, g, pack["guests"]):
                    continue
                if not is_faculty_mix_valid(h, pack["guests"] + [g], groups):
                    continue
                pack["guests"].append(g)
                guest_pool.remove(g)
                placed = True
                # Begegnungen nachtragen
                encounters[h].add(g)
                encounters[g].add(h)
                for cg in pack["guests"]:
                    if cg == g:
                        continue
                    encounters[cg].add(g)
                    encounters[g].add(cg)
                break
            if not placed:
                raise RuntimeError("Fachschafts-Mix konnte nicht eingehalten werden. Bitte mehr gemischte Gruppen anmelden oder manuell nachbessern.")

    return assignments



# --- OpenStreetMap helpers (Nominatim + OSRM) ---

def _chunk(lst, n):
    for i in range(0, len(lst), n):
        yield lst[i:i+n]


NOMINATIM_URL = "https://nominatim.openstreetmap.org/search"
OSRM_BASE_URL = "https://router.project-osrm.org"
OSRM_MAX_LOCATIONS_PER_REQUEST = 50  # max. Quellen/Ziele pro Request, damit wir <100 Koordinaten bleiben
try:
    NOMINATIM_REQUEST_DELAY = float(os.environ.get("NOMINATIM_REQUEST_DELAY", "1.0"))
except ValueError:
    NOMINATIM_REQUEST_DELAY = 1.0

OSRM_MODE_MAP = {
    "walking": "walking",
    "walk": "walking",
    "foot": "walking",
    "driving": "driving",
    "car": "driving",
    "bicycling": "cycling",
    "bicycle": "cycling",
    "bike": "cycling",
    "transit": "walking",  # Transit gibt es nicht -> laufen als best-effort
}


def _nominatim_headers():
    email = os.environ.get("NOMINATIM_EMAIL", "").strip()
    ua = os.environ.get("NOMINATIM_USER_AGENT", "").strip()
    if not ua:
        contact_hint = email or "set NOMINATIM_EMAIL"
        ua = f"running-cocktail-scheduler/1.0 ({contact_hint})"
    headers = {"User-Agent": ua}
    if email:
        headers["From"] = email
    return headers


def geocode_address(address: str, session=None):
    """Geokodiert eine Adresse via Nominatim, liefert (lat, lon) oder None."""
    session = session or requests.Session()
    params = {
        "q": address,
        "format": "jsonv2",
        "limit": 1,
        "countrycodes": "de",
        "addressdetails": 0,
    }
    resp = session.get(NOMINATIM_URL, params=params, headers=_nominatim_headers(), timeout=30)
    if resp.status_code == 429:
        raise RuntimeError("Nominatim Rate-Limit (HTTP 429). Bitte kurz warten oder die Pausenzeit erhöhen.")
    resp.raise_for_status()
    data = resp.json()
    if not data:
        return None
    try:
        lat = float(data[0]["lat"])
        lon = float(data[0]["lon"])
        return (lat, lon)
    except (KeyError, ValueError, TypeError):
        return None


def geocode_addresses(addresses, pause_seconds=NOMINATIM_REQUEST_DELAY):
    """
    Geokodiert eine Liste von Adressen seriell (Nominatim bitte nicht flooden).
    Gibt (coords_map, failures) zurück:
      coords_map[address] = (lat, lon)
      failures[address] = Grund (String)
    """
    session = requests.Session()
    coords = {}
    failures = {}
    seen = set()
    unique_addrs = []
    for addr in addresses:
        if addr in seen:
            continue
        seen.add(addr)
        unique_addrs.append(addr)

    for idx, addr in enumerate(unique_addrs):
        try:
            res = geocode_address(addr, session=session)
            if res is None:
                failures[addr] = "NOT_FOUND"
            else:
                coords[addr] = res
        except Exception as e:
            failures[addr] = str(e)
        if pause_seconds and idx + 1 < len(unique_addrs):
            time.sleep(pause_seconds)

    return coords, failures


def _osrm_table_chunk(origins, destinations, coords_map, profile="walking"):
    """
    Holt eine Distanzmatrix (Meter) für einen kleinen Chunk via OSRM Table API.
    coords_map[address] = (lat, lon)
    """
    out = {o: {d: None for d in destinations} for o in origins}

    coord_list = []
    coord_indices = {}
    for addr in origins + destinations:
        if addr in coord_indices:
            continue
        coord = coords_map.get(addr)
        if coord is None:
            coord_indices[addr] = None
            continue
        lat, lon = coord
        coord_indices[addr] = len(coord_list)
        coord_list.append((lon, lat))  # OSRM erwartet lon,lat

    source_addrs = [o for o in origins if coord_indices.get(o) is not None]
    dest_addrs = [d for d in destinations if coord_indices.get(d) is not None]
    if not source_addrs or not dest_addrs:
        return out

    coord_str = ";".join(f"{lon},{lat}" for lon, lat in coord_list)
    params = {
        "sources": ";".join(str(coord_indices[o]) for o in source_addrs),
        "destinations": ";".join(str(coord_indices[d]) for d in dest_addrs),
        "annotations": "distance",
    }
    url = f"{OSRM_BASE_URL}/table/v1/{profile}/{coord_str}"
    resp = requests.get(url, params=params, timeout=30)
    resp.raise_for_status()
    data = resp.json()
    if data.get("code") != "Ok":
        raise RuntimeError(f"OSRM Table API Error: {data.get('message', 'unknown')}")
    distances = data.get("distances")
    if not distances:
        return out

    for row_idx, o in enumerate(source_addrs):
        row = distances[row_idx]
        if row is None:
            continue
        for col_idx, d in enumerate(dest_addrs):
            val = row[col_idx]
            if val is None:
                continue
            try:
                out[o][d] = int(round(float(val)))
            except Exception:
                out[o][d] = None
    return out


def osrm_distance_matrix(origins, destinations, coords_map, mode="walking", max_locations=OSRM_MAX_LOCATIONS_PER_REQUEST):
    """
    Batcht Requests gegen die OSRM Table API.
    Rückgabe: dict[origin][destination] = distance_m (int|None)
    """
    profile = OSRM_MODE_MAP.get((mode or "walking").lower(), "walking")
    result = {o: {} for o in origins}
    origin_list = list(origins)
    dest_list = list(destinations)
    for o_chunk in _chunk(origin_list, max_locations):
        for d_chunk in _chunk(dest_list, max_locations):
            chunk_map = _osrm_table_chunk(o_chunk, d_chunk, coords_map, profile=profile)
            for o in o_chunk:
                result[o].update(chunk_map.get(o, {}))
    return result


def distances_to_center(addresses, center_address, coords_map, mode="walking"):
    dmap = osrm_distance_matrix(addresses, [center_address], coords_map, mode=mode)
    return [dmap[a].get(center_address) for a in addresses]


def build_itineraries(round_assignments, groups):
    """
    round_assignments: Liste [round1, round2, round3]
      roundX = [{"host": host_id, "guests":[g1,g2,...]}, ...]
    Rückgabe: dict group_id -> Liste mit 3 Einträgen (eine pro Runde)
    """
    itineraries = {gid: [] for gid in groups.keys()}

    for rnd_idx, packs in enumerate(round_assignments, start=1):
        # Map host->guests
        for pack in packs:
            host = pack["host"]
            guests = pack["guests"]
            host_allergy_notes = collect_allergy_notes(guests, groups)
            # Host-Eintrag
            itineraries[host].append({
                "Runde": rnd_idx,
                "Rolle": "HOST",
                "Ort_Name": groups[host]["Klingel"],
                "Ort_Adresse": groups[host]["Adresse"],
                "Ort_Bezug": "Eigene Location",
                "Mit_Gruppen": [groups[g]["Name"] for g in guests],
                "Mit_Fachschaften": [groups[g]["Fach"] for g in guests],
                "Allergie_Hinweise": host_allergy_notes,
            })
            # Gast-Einträge
            for g in guests:
                others = [x for x in guests if x != g]
                guest_allergy_notes = collect_allergy_notes([host] + others, groups, exclude_ids=[g])
                itineraries[g].append({
                    "Runde": rnd_idx,
                    "Rolle": "GAST",
                    "Ort_Name": groups[host]["Klingel"],
                    "Ort_Adresse": groups[host]["Adresse"],
                    "Ort_Bezug": f"Bei {groups[host]['Name']}",
                    "Mit_Gruppen": [groups[host]["Name"]] + [groups[o]["Name"] for o in others],
                    "Mit_Fachschaften": [groups[host]["Fach"]] + [groups[o]["Fach"] for o in others],
                    "Allergie_Hinweise": guest_allergy_notes,
                })
    # Nach Runde sortieren
    for gid in itineraries:
        itineraries[gid] = sorted(itineraries[gid], key=lambda x: x["Runde"])
    return itineraries


# ----------------------------------------
# Robustes CSV-Lesen mit automatischer oder expliziter Trennzeichenerkennung
# ----------------------------------------
def read_csv_robust(path, explicit_sep=None):
    """Liest CSV robust ein und probiert unterschiedliche Trennzeichen.
    Bevorzugt: vom Nutzer vorgegebenes Trennzeichen, sonst Auto-Detect, dann ; , \t |
    Liest alles als String (dtype=str), behält führende Nullen (PLZ), und ignoriert NA-Autokonvertierung.
    """
    seps = [explicit_sep] if explicit_sep is not None else [None, ';', ',', '\t', '|']
    last_err = None
    for sep in seps:
        try:
            if sep is None:
                df = pd.read_csv(
                    path,
                    sep=None,              # Auto-Detect
                    engine='python',
                    dtype=str,
                    keep_default_na=False,
                    encoding='utf-8-sig'
                )
                print("[INFO] CSV gelesen mit automatischer Trennzeichen-Erkennung.")
            else:
                df = pd.read_csv(
                    path,
                    sep=sep,
                    dtype=str,
                    keep_default_na=False,
                    encoding='utf-8-sig'
                )
                print(f"[INFO] CSV gelesen mit sep='{sep}'.")
            return df
        except pd.errors.ParserError as e:
            last_err = e
            print(f"[WARN] ParserError mit sep='{sep}': {e}")
            continue
        except Exception as e:
            last_err = e
            print(f"[WARN] Fehler beim Lesen mit sep='{sep}': {e}")
            continue
    raise last_err if last_err is not None else RuntimeError("CSV konnte nicht gelesen werden.")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("csv_path", help="Pfad zur Eingabe-CSV")
    parser.add_argument("out_dir", help="Ausgabeverzeichnis")
    parser.add_argument("--seed", type=int, default=42, help="Zufalls-Seed für reproduzierbare Zuteilung")
    parser.add_argument("--sep", type=str, default=None, help="CSV-Trennzeichen erzwingen (z.B. ';' für deutsche Excel-CSV). Wenn nicht gesetzt, wird automatisch erkannt.")
    args = parser.parse_args()

    rng = random.Random(args.seed)
    os.makedirs(args.out_dir, exist_ok=True)

    # CSV laden
    df = read_csv_robust(args.csv_path, explicit_sep=args.sep)

    if len(df) < 3:
        raise ValueError("Zu wenige Gruppen in der CSV (mindestens 3 benötigt).")

    # Pflichtspalten prüfen (minimal)
    needed = [COL_FACHSCHAFT, COL_STREET, COL_PLZ, COL_STADT]
    for c in needed:
        if c not in df.columns:
            raise ValueError(f"Spalte fehlt in CSV: {c}")

    # Normalisiere Fachschaft + Adresse bauen
    df["Fach_norm"] = df[COL_FACHSCHAFT].apply(normalize_fachschaft)
    df["Adresse"] = df.apply(build_full_address, axis=1)

    # Optionalspalten robust behandeln
    if COL_KLINGEL in df.columns:
        df["Klingel"] = df[COL_KLINGEL].fillna("").astype(str).str.strip()
    else:
        df["Klingel"] = ""

    first = df[COL_NAME_1] if COL_NAME_1 in df.columns else pd.Series([""] * len(df))
    second = df[COL_NAME_2] if COL_NAME_2 in df.columns else pd.Series([""] * len(df))
    df["Name"] = (
        first.fillna("").astype(str).str.strip()
        + " & "
        + second.fillna("").astype(str).str.strip()
    ).str.strip(" & ")

    if COL_ALLERGY in df.columns:
        df["Allergien_norm"] = df[COL_ALLERGY].fillna("").astype(str).str.strip()
    else:
        df["Allergien_norm"] = ""

    # Geocoding + Distanzmatrix
    addresses = df["Adresse"].tolist()
    all_addresses_for_geocoding = addresses + [SCHLOSS_QUERY]
    coords_map, geocode_failures = geocode_addresses(all_addresses_for_geocoding)

    if geocode_failures:
        rows = [{"Adresse": addr, "Grund_Code": "GEOCODE_FAILED", "Grund_Message": reason} for addr, reason in geocode_failures.items()]
        pd.DataFrame(rows).to_csv(os.path.join(args.out_dir, "geocoding_failed.csv"), index=False)
        print(f"[WARN] {len(geocode_failures)} Adressen konnten nicht geokodiert werden -> geocoding_failed.csv")

    if SCHLOSS_QUERY not in coords_map:
        raise RuntimeError("Schloss-Adresse konnte nicht geokodiert werden. Bitte Adresse prüfen oder später erneut versuchen (Nominatim Rate-Limit?).")

    # Distanzen zum Schloss (für Band-Einteilung) und Distanzmatrix
    try:
        addr_dist_map = osrm_distance_matrix(addresses, addresses + [SCHLOSS_QUERY], coords_map, mode="walking")
    except Exception as e:
        print("\n[ERROR] Distanzmatrix via OSRM fehlgeschlagen.")
        print("       Prüfe Internetverbindung oder versuche es später erneut (öffentlicher OSRM-Server).")
        print(f"       Technische Fehlermeldung: {e}\n")
        raise

    dist_center_list = [addr_dist_map.get(a, {}).get(SCHLOSS_QUERY) for a in addresses]
    failed_rows = []
    for a, d in zip(addresses, dist_center_list):
        if a not in coords_map:
            failed_rows.append({"Adresse": a, "Grund_Code": "GEOCODE_FAILED", "Grund_Message": geocode_failures.get(a, "Nominatim lieferte keine Koordinate")})
        elif d is None:
            failed_rows.append({"Adresse": a, "Grund_Code": "NO_ROUTE", "Grund_Message": "OSRM lieferte keine Distanz"})
    if failed_rows:
        pd.DataFrame(failed_rows).to_csv(os.path.join(args.out_dir, "center_distance_failed.csv"), index=False)
        print(f"[WARN] {len(failed_rows)} Adressen konnten nicht zum Schloss aufgelöst werden -> center_distance_failed.csv")
    df["dist_m_schloss"] = [d if d is not None else 10**9 for d in dist_center_list]

    # 3 Bänder bestimmen (host_round = 1 außen, 2 mittel, 3 innen)
    bands = split_into_three_bands_by_distance(df, "dist_m_schloss", args.seed)
    if len(bands) != len(df):
        raise RuntimeError("Interne Zuordnungslogik fehlgeschlagen: Nicht alle Gruppen wurden einem Host-Ring zugeteilt.")
    df["host_round"] = df.index.map(bands)

    # Datenstruktur groups
    groups = {}
    for gid, row in df.iterrows():
        groups[gid] = {
            "Fach": row["Fach_norm"],
            "Name": row["Name"] if isinstance(row["Name"], str) and row["Name"].strip() else f"Gruppe {gid}",
            "Adresse": row["Adresse"],
            "Klingel": row["Klingel"] if row["Klingel"] else row["Name"],
            "dist": float(row["dist_m_schloss"]),
            "host_round": int(row["host_round"]),
            "Allergien": row.get("Allergien_norm", "").strip(),
        }

    # Runden: Host-Sets pro Runde
    # Start-Standort jeder Gruppe: eigene Adresse
    prev_locations = {gid: groups[gid]["Adresse"] for gid in groups}

    round_assignments = []
    encounters = defaultdict(set)     # group_id -> set(partner_ids)

    all_ids = list(groups.keys())
    for r in [1, 2, 3]:
        hosts = [gid for gid in all_ids if groups[gid]["host_round"] == r]
        guests = [gid for gid in all_ids if groups[gid]["host_round"] != r]

        assignments = schedule_round(hosts, guests, groups, r, rng, encounters, prev_locations, addr_dist_map, SCHLOSS_QUERY)
        round_assignments.append(assignments)

        # Nach der Zuteilung die letzten Standorte aller Teilnehmer aktualisieren
        # Hosts bleiben an ihrer Adresse; Gäste wechseln zum Host-Standort dieser Runde.
        for pack in assignments:
            h = pack["host"]
            h_addr = groups[h]["Adresse"]
            prev_locations[h] = h_addr
            for g in pack["guests"]:
                prev_locations[g] = h_addr

    # Itineraries bauen
    itineraries = build_itineraries(round_assignments, groups)

    # Exporte
    # 1) Adressen + Distanz zum Schloss
    df_out = df.copy()
    df_out.to_csv(os.path.join(args.out_dir, "addresses_with_center_distance.csv"), index=False)

    # 2) Rundenübersichten
    for i, packs in enumerate(round_assignments, start=1):
        rows = []
        for pack in packs:
            h = pack["host"]
            rows.append({
                "Runde": i,
                "Host_Name": groups[h]["Name"],
                "Host_Fach": groups[h]["Fach"],
                "Host_Adresse": groups[h]["Adresse"],
                "Gast_Namen": " | ".join(groups[g]["Name"] for g in pack["guests"]),
                "Gast_Fachschaften": " | ".join(groups[g]["Fach"] for g in pack["guests"]),
                "Gast_Allergien": collect_allergy_notes(pack["guests"], groups),
            })
        pd.DataFrame(rows).to_csv(os.path.join(args.out_dir, f"round_{i}.csv"), index=False)

    # 3) Itineraries pro Gruppe
    rows = []
    for gid, entries in itineraries.items():
        for ent in entries:
            rows.append({
                "Gruppe": groups[gid]["Name"],
                "Fachschaft": groups[gid]["Fach"],
                "Runde": ent["Runde"],
                "Rolle": ent["Rolle"],
                "Ort_Name/Klingel": ent["Ort_Name"],
                "Ort_Adresse": ent["Ort_Adresse"],
                "Mit_Gruppen": " | ".join(ent["Mit_Gruppen"]),
                "Mit_Fachschaften": " | ".join(ent["Mit_Fachschaften"]),
                "Allergie_Hinweise": ent.get("Allergie_Hinweise", ""),
            })
    df_it = pd.DataFrame(rows).sort_values(["Gruppe", "Runde"])
    df_it.to_csv(os.path.join(args.out_dir, "itineraries_per_group.csv"), index=False)
    try:
        df_it.to_excel(os.path.join(args.out_dir, "itineraries_per_group.xlsx"), index=False)
    except Exception:
        pass

    print("Fertig! Dateien liegen in:", args.out_dir)
    print("Beispiel: itineraries_per_group.csv, round_1.csv, round_2.csv, round_3.csv")


if __name__ == "__main__":
    main()
