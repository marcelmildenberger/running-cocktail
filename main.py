# running_cocktail_scheduler.py
# -*- coding: utf-8 -*-
"""
Planer für 'Running Cocktail' Mannheim

Funktionen:
- CSV einlesen (deutsche Spaltennamen)
- Geokodierung (OSM/Nominatim)
- Entfernung zum Mannheimer Schloss berechnen
- Gruppen in 3 Ringe (außen/mittel/innen) einteilen
- 3 Runden mit Stations-Trios (Host + 2 Gäste) planen:
    * jede Gruppe hostet genau 1x
    * niemand trifft dieselbe Gruppe zweimal
    * Fachschaften (FIM/VWL) möglichst gemischt
    * Weg verläuft für alle: außen -> innen
- Itineraries & Runden-Übersichten exportieren (CSV/Excel)

Aufruf:
    python main.py RuCo.csv resultcle

Benötigte Pakete: pandas, numpy, geopy, (optional) openpyxl
"""

import os
import sys
import math
import random
import argparse
import itertools
from collections import defaultdict, Counter

import pandas as pd
import numpy as np

# Optionale Geokodierer
try:
    from geopy.geocoders import Nominatim
    from geopy.extra.rate_limiter import RateLimiter
except Exception:
    Nominatim = None
    RateLimiter = None


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
SCHLOSS_QUERY = "Mannheimer Schloss, 68161 Mannheim, Deutschland"
SCHLOSS_FALLBACK = (49.4837, 8.4620)  # robuste Näherung

# Standard: je Station 2 Gäste (Host + 2 Gäste = 3 Gruppen)
DEFAULT_GUESTS_PER_HOST = 2


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
    parts = []
    for col in [COL_STREET, COL_PLZ, COL_STADTTEIL, COL_STADT]:
        val = row.get(col)
        if isinstance(val, str) and val.strip():
            parts.append(val.strip())
    # Sicherheitshalber 'Mannheim' anhängen, falls nicht vorhanden
    addr = ", ".join(parts)
    if "mannheim" not in addr.lower():
        addr = addr + ", Mannheim"
    return addr


def haversine_m(lat1, lon1, lat2, lon2) -> float:
    # Meter
    R = 6371000.0
    p1 = math.radians(lat1)
    p2 = math.radians(lat2)
    dp = math.radians(lat2 - lat1)
    dl = math.radians(lon2 - lon1)
    a = math.sin(dp/2)**2 + math.cos(p1)*math.cos(p2)*math.sin(dl/2)**2
    c = 2 * math.atan2(math.sqrt(a), math.sqrt(1-a))
    return R * c


def geocode_one(address: str, osm_geocoder=None):
    # OSM/Nominatim
    if osm_geocoder:
        try:
            loc = osm_geocoder.geocode(address)
            if loc:
                return loc.latitude, loc.longitude
        except Exception:
            pass
    return None, None


def geocode_center(osm_geocoder=None):
    lat, lng = geocode_one(SCHLOSS_QUERY, osm_geocoder)
    if lat is None:
        lat, lng = SCHLOSS_FALLBACK
    return lat, lng


def split_into_three_bands_by_distance(df: pd.DataFrame, dist_col: str, seed: int):
    """
    Teilt DataFrame-Index (Gruppen) in 3 Bänder (außen, mittel, innen),
    wobei die Größen sich nur um höchstens 1 unterscheiden.
    Sortiert nach Distanz absteigend (außen zuerst).
    Gibt dict: group_id -> host_round (1=außen, 2=mittel, 3=innen)
    """
    rng = random.Random(seed)
    df_sorted = df.sort_values(dist_col, ascending=False).copy()
    n = len(df_sorted)
    base = n // 3
    rem = n % 3
    sizes = [base + (1 if i < rem else 0) for i in range(3)]  # Summe = n, so balanciert wie möglich

    idxs = list(df_sorted.index)
    # Um gleich entfernte besser zu verteilen, leicht mischen (stabil genug)
    rng.shuffle(idxs)

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


def schedule_round(host_ids, guest_ids, groups, round_no, rng, encounters, fach_counts):
    """
    Weist jedem Host eine Anzahl Gäste (1..3) zu, so dass:
      - Jeder Gast genau 1x in dieser Runde zugeteilt wird.
      - Wiederholte Begegnungen vermieden werden.
      - Fachschaften gemischt bevorzugt werden.
    'groups' ist ein Dict group_id -> dict mit 'Fach', 'Name', 'lat','lng','dist','addr', etc.
    encounters[group_id] = set(bisher getroffene Gruppen)
    fach_counts[group_id] = Counter({"FIM":x,"VWL":y}) der bisher getroffenen Gegenüber
    """
    rng.shuffle(host_ids)
    rng.shuffle(guest_ids)

    n_hosts = len(host_ids)
    caps = compute_host_capacities(n_hosts, len(guest_ids), DEFAULT_GUESTS_PER_HOST)

    assignments = []  # Liste von dicts: {"host": h, "guests":[g1,g2,...]}
    guest_pool = set(guest_ids)

    def pair_score(h, g, co_guests):
        # Höhere Punkte = besser
        score = 0.0
        # Nicht doppelt begegnen
        if g in encounters[h]:
            score -= 100.0
        # Fachschaften mischen
        if groups[h]["Fach"] != groups[g]["Fach"]:
            score += 5.0
        else:
            score -= 1.0
        # Gäste untereinander: lieber neue Begegnungen & gemischte Fachschaften
        for cg in co_guests:
            if g in encounters[cg]:
                score -= 30.0
            if groups[cg]["Fach"] != groups[g]["Fach"]:
                score += 2.0
            else:
                score -= 0.5
        # Ausgewogenheit für den Gast selbst (nicht 3x dieselbe Fachschaft treffen)
        fc = fach_counts[g]
        # angenommen: er trifft jetzt Host h und die co_guests
        projected_same = fc[groups[h]["Fach"]] + sum(1 for cg in co_guests if groups[cg]["Fach"] == groups[h]["Fach"])
        projected_other = sum(fc.values()) - fc[groups[h]["Fach"]] + sum(1 for cg in co_guests if groups[cg]["Fach"] != groups[h]["Fach"])
        # leichte Präferenz für Ausgleich
        if projected_same > projected_other + 1:
            score -= 2.0
        # leichte Zufallskomponente zur Diversifizierung
        score += rng.random() * 0.01
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
            best_s = -1e9
            for g in guest_pool:
                s = pair_score(host, g, chosen)
                if s > best_s:
                    best_s = s
                    best_g = g
            if best_g is None:
                break
            chosen.append(best_g)
            guest_pool.remove(best_g)

        if chosen:
            assignments.append({"host": host, "guests": chosen})

            # Begegnungen registrieren (Host <-> Gäste und Gäste untereinander)
            for g in chosen:
                encounters[host].add(g)
                encounters[g].add(host)
                fach_counts[host][groups[g]["Fach"]] += 1
                fach_counts[g][groups[host]["Fach"]] += 1
            for a, b in itertools.combinations(chosen, 2):
                encounters[a].add(b)
                encounters[b].add(a)
                fach_counts[a][groups[b]["Fach"]] += 1
                fach_counts[b][groups[a]["Fach"]] += 1

    # Falls aus irgendeinem Grund noch Gäste übrig sind (sollte nicht passieren, aber safety net):
    if guest_pool:
        # Hänge übrig gebliebene Gäste an Hosts mit der kleinsten Belegung
        by_load = sorted(assignments, key=lambda x: len(x["guests"]))
        for g in list(guest_pool):
            for pack in by_load:
                pack["guests"].append(g)
                guest_pool.remove(g)
                # Begegnungen nachtragen
                h = pack["host"]
                encounters[h].add(g); encounters[g].add(h)
                fach_counts[h][groups[g]["Fach"]] += 1
                fach_counts[g][groups[h]["Fach"]] += 1
                for cg in pack["guests"]:
                    if cg == g:
                        continue
                    encounters[cg].add(g); encounters[g].add(cg)
                    fach_counts[cg][groups[g]["Fach"]] += 1
                    fach_counts[g][groups[cg]["Fach"]] += 1
                break

    return assignments


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
            # Host-Eintrag
            itineraries[host].append({
                "Runde": rnd_idx,
                "Rolle": "HOST",
                "Ort_Name": groups[host]["Klingel"],
                "Ort_Adresse": groups[host]["Adresse"],
                "Ort_Bezug": "Eigene Location",
                "Mit_Gruppen": [groups[g]["Name"] for g in guests],
                "Mit_Fachschaften": [groups[g]["Fach"] for g in guests]
            })
            # Gast-Einträge
            for g in guests:
                others = [x for x in guests if x != g]
                itineraries[g].append({
                    "Runde": rnd_idx,
                    "Rolle": "GAST",
                    "Ort_Name": groups[host]["Klingel"],
                    "Ort_Adresse": groups[host]["Adresse"],
                    "Ort_Bezug": f"Bei {groups[host]['Name']}",
                    "Mit_Gruppen": [groups[host]["Name"]] + [groups[o]["Name"] for o in others],
                    "Mit_Fachschaften": [groups[host]["Fach"]] + [groups[o]["Fach"] for o in others]
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

    # Pflichtspalten prüfen (minimal)
    needed = [COL_FACHSCHAFT, COL_STREET, COL_PLZ, COL_STADT]
    for c in needed:
        if c not in df.columns:
            raise ValueError(f"Spalte fehlt in CSV: {c}")

    # Normalisiere Fachschaft + Adresse bauen
    df["Fach_norm"] = df[COL_FACHSCHAFT].apply(normalize_fachschaft)
    df["Adresse"] = df.apply(build_full_address, axis=1)
    df["Klingel"] = df[COL_KLINGEL].fillna("").apply(lambda s: s.strip() if isinstance(s, str) else "")
    df["Name"] = (df[COL_NAME_1].fillna("").astype(str).str.strip()
                  + " & "
                  + df[COL_NAME_2].fillna("").astype(str).str.strip()).str.strip(" & ")

    # Geokodierung via OSM/Nominatim (kein Google Maps)
    osm_geocoder = None
    if Nominatim is not None:
        osm = Nominatim(user_agent="running_cocktail_mannheim")
        osm_geocoder = RateLimiter(osm.geocode, min_delay_seconds=1, max_retries=2, swallow_exceptions=True)

    lat_s, lon_s = geocode_center(osm_geocoder)

    lats, lons = [], []
    for addr in df["Adresse"]:
        lat, lon = geocode_one(addr, osm_geocoder)
        lats.append(lat); lons.append(lon)
    df["lat"] = lats
    df["lon"] = lons

    # Fallback: falls Geokodierung fehlgeschlagen, grobe Näherung ignorieren (Filter)
    if df["lat"].isna().any():
        # Minimal: fehlende Zeilen an Schloss kleben => Distanz 0 (damit sie inner landen)
        df["lat"] = df["lat"].fillna(lat_s)
        df["lon"] = df["lon"].fillna(lon_s)

    # Distanz zum Schloss
    df["dist_m_schloss"] = df.apply(lambda r: haversine_m(r["lat"], r["lon"], lat_s, lon_s), axis=1)

    # 3 Bänder bestimmen (host_round = 1 außen, 2 mittel, 3 innen)
    bands = split_into_three_bands_by_distance(df, "dist_m_schloss", args.seed)
    df["host_round"] = df.index.map(bands)

    # Datenstruktur groups
    groups = {}
    for gid, row in df.iterrows():
        groups[gid] = {
            "Fach": row["Fach_norm"],
            "Name": row["Name"] if isinstance(row["Name"], str) and row["Name"].strip() else f"Gruppe {gid}",
            "Adresse": row["Adresse"],
            "Klingel": row["Klingel"] if row["Klingel"] else row["Name"],
            "lat": float(row["lat"]),
            "lon": float(row["lon"]),
            "dist": float(row["dist_m_schloss"]),
            "host_round": int(row["host_round"]),
        }

    # Runden: Host-Sets pro Runde
    round_assignments = []
    encounters = defaultdict(set)     # group_id -> set(partner_ids)
    fach_counts = defaultdict(Counter)

    all_ids = list(groups.keys())
    for r in [1, 2, 3]:
        hosts = [gid for gid in all_ids if groups[gid]["host_round"] == r]
        guests = [gid for gid in all_ids if groups[gid]["host_round"] != r]

        # Sicherheit: genügend Gäste-Slots schaffen
        assignments = schedule_round(hosts, guests, groups, r, rng, encounters, fach_counts)
        round_assignments.append(assignments)

    # Itineraries bauen
    itineraries = build_itineraries(round_assignments, groups)

    # Exporte
    # 1) Geokodierte Gruppen
    df_out = df.copy()
    df_out.to_csv(os.path.join(args.out_dir, "geocoded_groups.csv"), index=False)

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