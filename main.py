# running_cocktail_scheduler.py
# -*- coding: utf-8 -*-
"""
Planer für 'Running Cocktail' Mannheim

Funktionen:
- CSV einlesen (deutsche Spaltennamen)
- Entfernungen via Google Maps Distance Matrix (kein Geocoding, nur Adressen)
- Gruppen in 3 Ringe (außen/mittel/innen) einteilen
- 3 Runden mit Stations-Trios (Host + 2 Gäste) planen:
    * jede Gruppe hostet genau 1x
    * niemand trifft dieselbe Gruppe zweimal
    * Fachschaften (FIM/VWL) möglichst gemischt
    * Weg verläuft für alle: außen -> innen
- Itineraries & Runden-Übersichten exportieren (CSV/Excel)

Aufruf:
    python main.py RuCo.csv resultcle

Benötigte Pakete: pandas, numpy, requests, (optional) openpyxl
"""

import os
import sys
import random
import argparse
import itertools
from collections import defaultdict

import pandas as pd
import numpy as np
import requests
import json
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
SCHLOSS_QUERY = "Mannheimer Schloss, 68161 Mannheim, Germany"

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
    # Fallback: erstes Wort groß
    return s.strip().upper()


def build_full_address(row) -> str:
    """Baut eine Adresse für Google Routes: "Straße Hausnr, PLZ Stadt, Germany".
    Wichtige Regeln:
      - **neighbourhood wird NICHT eingefügt** (führt häufig zu NO_ELEMENT bei RouteMatrix)
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



# --- Google Routes API helper ---

def get_routes_api_key():
    """
    Bezieht den API-Key bevorzugt aus der Umgebung (GOOGLE_MAPS_API_KEY oder GOOGLE_ROUTES_API_KEY).
    Fällt – nur falls vorhanden – auf den im Code hinterlegten Key zurück.
    """
    for var_name in ("GOOGLE_ROUTES_API_KEY", "GOOGLE_MAPS_API_KEY", "GOOGLE_MAPS_DISTANCE_MATRIX_API_KEY"):
        candidate = os.environ.get(var_name)
        if candidate and candidate.strip():
            return candidate.strip()

    # Historischer Fallback-Key (z.B. für lokale Tests). Bitte durch eigenen Key ersetzen.
    fallback_key = ""
    if fallback_key:
        return fallback_key

    raise RuntimeError("Kein Google Routes API Key gefunden. Setze z.B. GOOGLE_ROUTES_API_KEY in deiner Umgebung.")



def _chunk(lst, n):
    for i in range(0, len(lst), n):
        yield lst[i:i+n]

ROUTES_DM_URL = "https://routes.googleapis.com/distanceMatrix/v2:computeRouteMatrix"

_MODE_MAP = {
    "walking": "WALK",
    "driving": "DRIVE",
    "bicycling": "BICYCLE",
    "bicycle": "BICYCLE",
    "transit": "TRANSIT",
}

def _parse_route_matrix_response(text, origins, destinations):
    """Parst die JSON-Lines Antwort der Routes API und liefert zwei Maps:
    - dist_out[origin][destination] = distanceMeters | None
    - status_out[origin][destination] = {"code": int|str, "message": str}
      Für fehlende Elemente wird ein Dummy-Status gesetzt.
    """
    def _collect_entries(obj, bucket):
        if isinstance(obj, dict):
            if "originIndex" in obj and "destinationIndex" in obj:
                bucket.append(obj)
            else:
                for val in obj.values():
                    _collect_entries(val, bucket)
        elif isinstance(obj, list):
            for item in obj:
                _collect_entries(item, bucket)

    raw = (text or "")
    elements = []
    for line in raw.strip().splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("data:"):
            stripped = stripped[5:].strip()
        try:
            candidate = json.loads(stripped)
        except Exception:
            continue
        _collect_entries(candidate, elements)

    if not elements:
        # Fallback: einige Responses kommen als JSON-Objekt statt JSON-Lines
        try:
            payload = json.loads(raw)
        except Exception:
            payload = None
        if payload is not None:
            _collect_entries(payload, elements)

    result = {}
    status_map_idx = {}
    for el in elements:
        if not isinstance(el, dict):
            continue
        oi = el.get("originIndex")
        di = el.get("destinationIndex")
        if oi is None or di is None:
            continue
        status_obj = el.get("status") or {}
        status_code = status_obj.get("code", 0)
        status_map_idx.setdefault(oi, {})[di] = {
            "code": status_code,
            "message": status_obj.get("message", "")
        }
        dist = el.get("distanceMeters") if status_code == 0 else None
        result.setdefault(oi, {})[di] = dist

    # In adressbasierte Maps umwandeln
    dist_out = {o: {} for o in origins}
    status_out = {o: {} for o in origins}
    for oi in range(len(origins)):
        for di in range(len(destinations)):
            dist = None
            status_obj = status_map_idx.get(oi, {}).get(di)
            if status_obj is None:
                # Element fehlte komplett in der Antwort
                status_obj = {"code": "NO_ELEMENT", "message": "Pair missing in response"}
            else:
                dist = result.get(oi, {}).get(di)
            dist_out[origins[oi]][destinations[di]] = dist
            status_out[origins[oi]][destinations[di]] = status_obj
    return dist_out, status_out


def _gm_distance_matrix_chunk_routes(api_key, origins, destinations, mode="walking"):
    out, _status = _gm_distance_matrix_chunk_routes_with_status(api_key, origins, destinations, mode=mode)
    return out


def _gm_distance_matrix_chunk_routes_with_status(api_key, origins, destinations, mode="walking"):
    travel_mode = _MODE_MAP.get((mode or "walking").lower(), "WALK")
    headers = {
        "Content-Type": "application/json",
        "Accept": "application/json",
        "X-Goog-Api-Key": api_key,
        # FieldMask ist Pflicht, sonst 400
        "X-Goog-FieldMask": "originIndex,destinationIndex,distanceMeters,duration,status",
    }
    body = {
        "origins": [{"waypoint": {"address": o}} for o in origins],
        "destinations": [{"waypoint": {"address": d}} for d in destinations],
        "travelMode": travel_mode,
        "regionCode": "DE",
    }
    if travel_mode == "DRIVE":
        body["routingPreference"] = "TRAFFIC_AWARE_OPTIMAL"
    resp = requests.post(ROUTES_DM_URL, headers=headers, data=json.dumps(body), timeout=60)
    if not resp.ok:
        snippet = resp.text[:800].replace("\n", " ")
        raise RuntimeError(f"Routes API HTTP {resp.status_code}. Body: {snippet}")
    resp.raise_for_status()

    return _parse_route_matrix_response(resp.text, origins, destinations)



def gm_distance_matrix(api_key, origins, destinations, mode="walking"):
    """Batcht Requests gegen Routes API, liefert dict[origin][destination] = distance_m (int|None)."""
    result = {o: {} for o in origins}
    for o_chunk in _chunk(origins, 25):
        for d_chunk in _chunk(destinations, 25):
            chunk_map = _gm_distance_matrix_chunk_routes(api_key, o_chunk, d_chunk, mode=mode)
            # Merge
            for o in o_chunk:
                result[o].update(chunk_map.get(o, {}))
    return result


def gm_distance_matrix_with_status(api_key, origins, destinations, mode="walking"):
    """Wie gm_distance_matrix, liefert zusätzlich Status-Infos je Paar.
    Rückgabe: (dist_map, status_map)
    dist_map[o][d] = int|None, status_map[o][d] = {code, message}
    """
    dist_result = {o: {} for o in origins}
    status_result = {o: {} for o in origins}
    for o_chunk in _chunk(origins, 25):
        for d_chunk in _chunk(destinations, 25):
            dist_chunk, status_chunk = _gm_distance_matrix_chunk_routes_with_status(api_key, o_chunk, d_chunk, mode=mode)
            for o in o_chunk:
                dist_result[o].update(dist_chunk.get(o, {}))
                status_result[o].update(status_chunk.get(o, {}))
    return dist_result, status_result



def distances_to_center(api_key, addresses, center_address, mode="walking"):
    dmap = gm_distance_matrix(api_key, addresses, [center_address], mode=mode)
    return [dmap[a].get(center_address) for a in addresses]


def distances_to_center_with_status(api_key, addresses, center_address, mode="walking"):
    dist_map, status_map = gm_distance_matrix_with_status(api_key, addresses, [center_address], mode=mode)
    dists = [dist_map[a].get(center_address) for a in addresses]
    # status_map[a][center] ist bereits {code, message}
    reason_map = {a: {center_address: status_map[a].get(center_address)} for a in addresses}
    return dists, reason_map


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

    # Google Routes API Key
    api_key = get_routes_api_key()

    # Distanzen zum Schloss (für Band-Einteilung) und Distanzmatrix mit Fehlerdiagnose
    addresses = df["Adresse"].tolist()
    try:
        dist_center_list, status_map_center = distances_to_center_with_status(api_key, addresses, SCHLOSS_QUERY, mode="walking")
        failed_rows = []
        for a, d in zip(addresses, dist_center_list):
            if d is None:
                st = (status_map_center.get(a, {}).get(SCHLOSS_QUERY)) or {}
                code = st.get("code", "UNKNOWN")
                message = st.get("message", "")
                failed_rows.append({"Adresse": a, "Grund_Code": code, "Grund_Message": message})
        if failed_rows:
            pd.DataFrame(failed_rows).to_csv(os.path.join(args.out_dir, "center_distance_failed.csv"), index=False)
            print(f"[WARN] {len(failed_rows)} Adressen konnten nicht zum Schloss aufgelöst werden -> center_distance_failed.csv")
        df["dist_m_schloss"] = [d if d is not None else 10**9 for d in dist_center_list]

        # 3 Bänder bestimmen (host_round = 1 außen, 2 mittel, 3 innen)
        bands = split_into_three_bands_by_distance(df, "dist_m_schloss", args.seed)
        if len(bands) != len(df):
            raise RuntimeError("Interne Zuordnungslogik fehlgeschlagen: Nicht alle Gruppen wurden einem Host-Ring zugeteilt.")
        df["host_round"] = df.index.map(bands)

        # Vollständige Adress-Distanzmatrix (Adresse->Adresse), für Wege zwischen Runden & Zuteilung
        addr_dist_map = gm_distance_matrix(api_key, addresses, addresses + [SCHLOSS_QUERY], mode="walking")
    except Exception as e:
        print("\n[ERROR] Google Routes Distance Matrix fehlgeschlagen.")
        print("       Häufige Ursachen: 'Routes API' nicht aktiviert, Billing fehlt, oder API-Key ist restriktiert (HTTP-Referrer/IP).")
        print("       Bitte in Google Cloud Console prüfen: API 'Routes API' aktivieren, Billing aktiv, Key ohne App-Restriktion oder passende Server-IP freischalten.")
        print(f"       Technische Fehlermeldung: {e}\n")
        raise

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
