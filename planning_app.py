# -*- coding: utf-8 -*-
"""
GÉNÉRATEUR DE PLANNING DE PARTICIPATION — application Streamlit locale
=======================================================================

INSTALLATION
    python -m venv .venv
    source .venv/bin/activate          # Windows : .venv\\Scripts\\activate
    pip install -r requirements.txt

LANCEMENT
    streamlit run planning_app.py

PARCOURS UTILISATEUR (une seule page, 5 étapes qui se débloquent dans l'ordre)
    1. Import du document de base + des plannings externes (autres services)
    2. Saisie / import des noms des membres du service
    3. Configuration des tâches et des personnes habilitées
    4. Période, créneaux et REMARQUES libres (absences, interdits, imposés, quotas…)
    5. Vérification des indisponibilités/consignes, génération, export

PRINCIPE DE L'ALGORITHME
    Pour chaque créneau, chaque tâche reçoit le nombre de personnes demandé,
    choisies parmi les personnes habilitées ET disponibles (pas déjà sollicitées
    dans un planning externe). Les candidats sont classés par :
        1) nombre de fois où ils ont déjà fait CETTE tâche  (rotation équitable)
        2) présence sur le créneau précédent                (évite l'enchaînement)
        3) nombre total de participations                   (équité globale)
        4) tirage aléatoire                                 (départage les égalités)
    L'opération est répétée N fois ; le tirage le plus équitable est conservé.
"""

from __future__ import annotations

import hashlib
import io
import random
import re
import time
import unicodedata
from datetime import date, datetime, timedelta
from itertools import combinations

import pandas as pd
import streamlit as st

# ======================================================================
# CONSTANTES
# ======================================================================
EVERYONE = "👥 Tout le monde"
UNFILLED = "⚠️ Non pourvu"
WEEKDAYS_FR = ["Lundi", "Mardi", "Mercredi", "Jeudi", "Vendredi", "Samedi", "Dimanche"]
FILE_TYPES = ["xlsx", "xls", "csv", "txt", "pdf"]

_MONTHS = {
    "janvier": 1, "fevrier": 2, "mars": 3, "avril": 4, "mai": 5, "juin": 6,
    "juillet": 7, "aout": 8, "septembre": 9, "octobre": 10, "novembre": 11, "decembre": 12,
}
# Formats de dates reconnus (sur texte normalisé : minuscules, sans accents)
RE_ISO = re.compile(r"(?<![\d/\-.])(\d{4})-(\d{1,2})-(\d{1,2})(?!\d)")
RE_TEXT = re.compile(r"\b(\d{1,2})(?:er)?\s+(" + "|".join(_MONTHS) + r")(?:\s+(\d{4}))?\b")
RE_FR_Y = re.compile(r"(?<![\d/\-.])(\d{1,2})[/\-.](\d{1,2})[/\-.](\d{4}|\d{2})(?!\d|[/\-.]\d)")
RE_FR = re.compile(r"(?<![\d/\-.])(\d{1,2})/(\d{1,2})(?!\d|[/\-.]\d)")
RE_RANGE = re.compile(r"\bau\b|jusqu|->|→|–|—|\s-\s|\ba\b")

# Contenus de cellule qui ne signifient PAS « occupé »
IGNORED_CELLS = {"", "nan", "none", "nat", "-", "—", "–", "libre", "dispo", "disponible"}

NAME_PRIORITY = [
    "nom prenom", "prenom nom", "nom complet", "nom", "noms", "name", "names", "membre",
    "membres", "personne", "personnes", "agent", "agents", "collaborateur",
    "collaborateurs", "employe", "employes", "prenom", "prenoms",
]
NAME_HEADERS = set(NAME_PRIORITY)

WEEKDAY_IDX = {w.lower(): i for i, w in enumerate(WEEKDAYS_FR)}
WEEKDAY_RE = re.compile(r"\b(lundi|mardi|mercredi|jeudi|vendredi|samedi|dimanche)s?\b")
# Mots qui signifient « indisponible » même si une tâche est citée
STRONG_ABSENCE_RE = re.compile(r"\babsent|\bindisponible|\bconge|\bmalade|\bformation|\bdeplacement|\bmission|\brepos\b")
NEG_RE = re.compile(r"\bpas\b|\bjamais\b|\bdispense|\bexclu|\bevit|\bsans\b")
APART_CUE_RE = re.compile(r"ensemble|\bavec\b|meme creneau|meme temps|separ|incompatible")
APART_STRONG_RE = re.compile(r"separ|incompatible|evit")
IMPOSE_RE = re.compile(r"\bdoi(?:t|vent)\b|obligatoire|\bimpos|\baffect|\bassign|\bprogramm|\bassure\b|\bfera\b|\bfait\b|\bprend\b|\btient\b|\bsera\b")
NUM_WORDS = {"un": 1, "une": 1, "deux": 2, "trois": 3, "quatre": 4, "cinq": 5, "six": 6}

# Types de consignes (tableau « Consignes » de l'étape 5)
T_FORBID = "Interdit (tâche)"
T_FORCE = "Imposé (affectation)"
T_QUOTA = "Quota maximum"
T_APART = "Ne pas associer"
CONS_TYPES = [T_FORBID, T_FORCE, T_QUOTA, T_APART]
CONS_COLUMNS = ["Type", "Personne", "Autre personne", "Tâche", "Date", "Créneau", "Quota", "Source"]


def _stretch() -> dict:
    """Compatibilité entre versions de Streamlit pour l'étirement des tableaux."""
    try:
        major, minor = (int(x) for x in st.__version__.split(".")[:2])
    except Exception:
        return {}
    return {"width": "stretch"} if (major, minor) >= (1, 50) else {"use_container_width": True}


STRETCH = _stretch()


# ======================================================================
# 1. OUTILS DE TEXTE, DE DATES ET DE NOMS
# ======================================================================
def normalize(text) -> str:
    """Minuscules + suppression des accents (pour comparer sans se soucier de la saisie)."""
    s = unicodedata.normalize("NFKD", str(text))
    s = "".join(ch for ch in s if not unicodedata.combining(ch))
    return s.replace("\u00a0", " ").lower()


def tokens(text) -> list[str]:
    return re.findall(r"[a-z0-9]+", normalize(text))


def fmt_date(d: date) -> str:
    return f"{WEEKDAYS_FR[d.weekday()]} {d:%d/%m/%Y}"


def _mk(y, m, d):
    try:
        return date(int(y), int(m), int(d))
    except (ValueError, TypeError):
        return None


def extract_dates(text: str, default_year: int) -> list[date]:
    """Extrait toutes les dates d'un texte (ISO, 12/11/2026, 12/11, « 12 novembre 2026 »)."""
    s = normalize(text)
    found: list[tuple[int, date]] = []

    def take(regex, builder):
        nonlocal s
        for m in list(regex.finditer(s)):
            d = builder(m)
            if d is not None:
                found.append((m.start(), d))
                # on « masque » la date trouvée pour éviter qu'un autre motif la relise
                s = s[: m.start()] + " " * (m.end() - m.start()) + s[m.end():]

    take(RE_ISO, lambda m: _mk(m[1], m[2], m[3]))
    take(RE_TEXT, lambda m: _mk(m[3] or default_year, _MONTHS[m[2]], m[1]))
    take(RE_FR_Y, lambda m: _mk(int(m[3]) + (2000 if len(m[3]) == 2 else 0), m[2], m[1]))
    take(RE_FR, lambda m: _mk(default_year, m[2], m[1]))
    found.sort(key=lambda x: x[0])
    return [d for _, d in found]


def cell_text(c) -> str:
    if c is None:
        return ""
    try:
        if pd.isna(c):
            return ""
    except (TypeError, ValueError):
        pass
    if isinstance(c, (datetime, date)):
        return c.strftime("%d/%m/%Y")
    return str(c).strip()


def cell_dates(c, default_year: int) -> list[date]:
    """Dates contenues dans une cellule (vraie date Excel ou texte)."""
    if c is None:
        return []
    try:
        if pd.isna(c):
            return []
    except (TypeError, ValueError):
        pass
    if isinstance(c, datetime):          # couvre aussi pd.Timestamp
        return [c.date()]
    if isinstance(c, date):
        return [c]
    if isinstance(c, str):
        return extract_dates(c, default_year)
    return []


def expand_dates(dates: list[date], text: str, is_table: bool) -> list[date]:
    """Deux dates = une plage (du 10/11 au 14/11) → on la déplie jour par jour."""
    uniq = list(dict.fromkeys(dates))
    if len(uniq) == 2 and uniq[0] <= uniq[1] and (is_table or RE_RANGE.search(normalize(text))):
        n = (uniq[1] - uniq[0]).days
        if n <= 366:
            return [uniq[0] + timedelta(days=i) for i in range(n + 1)]
    return uniq


def detect_slot(text: str) -> str | None:
    """Détecte un créneau dans un texte : Matin / Après-midi / Soir / « * » (journée)."""
    n = normalize(text).replace("-", " ")
    matin = bool(re.search(r"\bmatin", n))
    apm = bool(re.search(r"apres ?midi|\baprem\b", n))
    soir = bool(re.search(r"\bsoir", n))
    if "journee" in n or (matin and apm):
        return "*"
    if matin:
        return "Matin"
    if apm:
        return "Après-midi"
    if soir:
        return "Soir"
    return None


def slot_kind(label: str | None) -> str | None:
    n = normalize(label or "*").replace("-", " ").strip()
    if n in ("", "*", "jour", "all") or "journee" in n:
        return "jour"
    if "apres midi" in n or "aprem" in n:
        return "apm"
    if "matin" in n:
        return "matin"
    if "soir" in n:
        return "soir"
    return None


def slot_conflict(entry_slot: str | None, slot_label: str) -> bool:
    """Une indisponibilité bloque-t-elle ce créneau ? (logique volontairement prudente)"""
    ek, lk = slot_kind(entry_slot), slot_kind(slot_label)
    if ek == "jour" or lk == "jour":
        return True
    if ek is None and lk is None:       # libellés personnalisés → comparaison textuelle
        a = normalize(entry_slot).strip()
        b = normalize(slot_label).strip()
        return a == b or a in b or b in a
    if ek is None or lk is None:        # libellé inconnu d'un côté → par prudence on bloque
        return True
    return ek == lk


def build_member_index(members: list[str]) -> list[tuple[str, set[str]]]:
    return [(m, set(tokens(m))) for m in members]


def match_members(text: str, index) -> list[str]:
    """Membres reconnus dans un texte (tous les mots du nom doivent y figurer)."""
    toks = set(tokens(text))
    hits = [(m, mt) for m, mt in index if mt and mt <= toks]
    # si « Marie » et « Marie Dupont » matchent, on garde le plus précis
    return [m for m, mt in hits if not any(mt < other for _, other in hits)]


def match_members_loose(text: str, index) -> tuple[list[str], list[str]]:
    """
    Comme match_members, mais accepte aussi un prénom ou un nom SEUL quand il identifie
    un seul membre (« Marie ne peut pas… »). Retourne (membres reconnus, mots ambigus).
    Réservé aux remarques : plus pratique à écrire, donc un peu moins strict.
    """
    exact = match_members(text, index)
    toks = set(tokens(text))
    used = set().union(*[mt for m, mt in index if m in exact]) if exact else set()
    owners: dict[str, list[str]] = {}
    for m, mt in index:
        for t in mt:
            if len(t) >= 3:
                owners.setdefault(t, []).append(m)
    found, ambiguous = set(exact), []
    for t in toks - used:
        if t in owners:
            if len(owners[t]) == 1:
                found.add(owners[t][0])
            else:
                ambiguous.append(t)
    return [m for m, _ in index if m in found], sorted(ambiguous)


def parse_names(text: str) -> list[str]:
    """Liste de noms saisis : un par ligne, ou séparés par , ou ; (doublons retirés)."""
    seen, out = set(), []
    for part in re.split(r"[\n;,]+", text or ""):
        p = re.sub(r"\s+", " ", part).strip()
        k = normalize(p)
        if p and k not in seen:
            seen.add(k)
            out.append(p)
    return out


# ======================================================================
# 2. LECTURE DES DOCUMENTS (Excel, CSV, TXT, PDF)
# ======================================================================
def decode_bytes(data: bytes) -> str:
    for enc in ("utf-8-sig", "cp1252"):
        try:
            return data.decode(enc)
        except UnicodeDecodeError:
            continue
    return data.decode("latin-1", errors="ignore")


def load_document(name: str, data: bytes) -> tuple[list[pd.DataFrame], list[str]]:
    """Retourne (tableaux, lignes de texte) quel que soit le format du fichier."""
    ext = name.rsplit(".", 1)[-1].lower() if "." in name else ""
    tables: list[pd.DataFrame] = []
    lines: list[str] = []

    if ext in ("xlsx", "xlsm", "xls"):
        sheets = pd.read_excel(io.BytesIO(data), sheet_name=None, header=None, dtype=object)
        tables = [df for df in sheets.values() if not df.empty]
    elif ext in ("csv", "tsv"):
        text = decode_bytes(data)
        try:
            df = pd.read_csv(io.StringIO(text), sep=None, engine="python", header=None, dtype=object)
        except Exception:
            df = pd.read_csv(io.StringIO(text), sep=";", header=None, dtype=object, on_bad_lines="skip")
        tables = [df]
    elif ext in ("txt", "md", "text"):
        lines = decode_bytes(data).splitlines()
    elif ext == "pdf":
        try:
            import pdfplumber
        except ImportError as exc:
            raise RuntimeError("Le module « pdfplumber » est requis pour lire les PDF : pip install pdfplumber") from exc
        with pdfplumber.open(io.BytesIO(data)) as pdf:
            for page in pdf.pages:
                lines.extend((page.extract_text() or "").splitlines())
                for tbl in page.extract_tables() or []:
                    df = pd.DataFrame(tbl)
                    if not df.empty:
                        tables.append(df)
    else:
        raise RuntimeError(f"Format non pris en charge : .{ext}")
    return tables, lines


# ---------- noms des membres depuis le document de base ----------
def clean_name_line(line: str) -> str:
    return re.sub(r"^\s*(?:[-*•·–]|\d+[.)])\s*", "", line).strip()


def looks_like_name(s: str) -> bool:
    """Filtre grossier : écarte les phrases de règles, chiffres, e-mails, etc."""
    s = s.strip()
    if not s or len(s) > 40 or len(s.split()) > 4:
        return False
    return not re.search(r"[\d:@/]", s)


def names_from_dataframe(df: pd.DataFrame) -> list[str]:
    if df.empty:
        return []
    first = [normalize(cell_text(c)).strip() for c in df.iloc[0].tolist()]
    body, col = df, 0
    if any(c in NAME_HEADERS for c in first):          # la 1re ligne est un en-tête
        body = df.iloc[1:]
        idx: dict[str, int] = {}
        for i, c in enumerate(first):
            idx.setdefault(c, i)
        if "nom" in idx and "prenom" in idx:
            return [f"{cell_text(p)} {cell_text(n)}".strip()
                    for p, n in zip(body.iloc[:, idx["prenom"]], body.iloc[:, idx["nom"]])]
        col = next((idx[k] for k in NAME_PRIORITY if k in idx), 0)
    return [cell_text(v) for v in body.iloc[:, col]]


def extract_member_names(name: str, data: bytes) -> list[str]:
    tables, lines = load_document(name, data)
    raw: list[str] = names_from_dataframe(tables[0]) if tables else []
    if not any(r.strip() for r in raw):
        raw = [clean_name_line(l) for l in lines if l.strip()]
        if len(raw) == 1:                               # « Marie, Paul, Léa » sur une ligne
            raw = re.split(r"[;,]", raw[0])
    seen, out = set(), []
    for r in raw:
        r = re.sub(r"\s+", " ", r).strip()
        if looks_like_name(r) and normalize(r) not in seen:
            seen.add(normalize(r))
            out.append(r)
    return out


# ---------- indisponibilités depuis les plannings externes ----------
def scan_rows(rows, index, default_year, source, is_table) -> list[dict]:
    """
    Parcourt des lignes (tableau ou texte) et repère « qui est occupé quand ».
    Deux logiques, choisies automatiquement :
      • grille « dates en colonnes » (≥ 3 dates sur une ligne d'en-tête) :
        un membre est occupé si son nom apparaît dans la ligne ou dans la case ;
      • lignes libres : tout nom de membre rencontré sur une ligne contenant une
        date (ou sous une ligne de titre portant la date) est occupé ce jour-là.
    Le créneau (matin / après-midi / soir) est lu dans le texte, sinon = journée.
    """
    found: list[dict] = []
    header = None                          # {n° colonne: (dates, créneau)}
    carry_days: list[date] = []            # dernière date « titre » rencontrée
    carry_slot: str | None = None

    def add(person, days, slot):
        for d in days:
            found.append({"Nom": person, "Date": d, "Créneau": slot, "Source": source})

    for row in rows:
        texts = [cell_text(c) for c in row]
        if not any(texts):
            continue
        row_text = " | ".join(t for t in texts if t)
        names = match_members(row_text, index)
        cell_days = [cell_dates(c, default_year) for c in row]
        n_date_cells = sum(1 for d in cell_days if d)

        # (a) ligne d'en-tête d'une grille « dates en colonnes »
        if is_table and n_date_cells >= 3 and not names:
            header = {j: (d, detect_slot(texts[j])) for j, d in enumerate(cell_days) if d}
            continue

        # (b) ligne appartenant à une grille
        if header:
            first_col = min(header)
            label_names = match_members(" ".join(texts[:first_col]), index)
            for j, (days, header_slot) in header.items():
                if j >= len(texts) or normalize(texts[j]).strip() in IGNORED_CELLS:
                    continue
                who = match_members(texts[j], index) or label_names
                slot = detect_slot(texts[j]) or header_slot or "*"
                for person in who:
                    add(person, days, slot)
            continue

        # (c) lignes libres
        all_dates = [d for ds in cell_days for d in ds]
        if not names:
            if all_dates:                                   # ligne de titre : on retient la date
                carry_days = expand_dates(all_dates, row_text, is_table)
                carry_slot = detect_slot(row_text)
            continue
        if all_dates:
            days = expand_dates(all_dates, row_text, is_table)
            slot = detect_slot(row_text) or "*"
            if is_table:                                    # cellules de date fusionnées
                carry_days, carry_slot = days, None
        else:
            days = carry_days
            slot = detect_slot(row_text) or carry_slot or "*"
        for person in names:
            add(person, days, slot)
    return found


@st.cache_data(show_spinner=False)
def parse_external_file(name: str, data: bytes, members: tuple, default_year: int) -> list[dict]:
    """Analyse un planning externe → liste d'indisponibilités (dédoublonnées)."""
    index = build_member_index(list(members))
    tables, lines = load_document(name, data)
    records: list[dict] = []
    for df in tables:
        records += scan_rows(df.values.tolist(), index, default_year, name, True)
    if lines:
        records += scan_rows([[l] for l in lines], index, default_year, name, False)
    seen, out = set(), []
    for r in records:
        key = (r["Nom"], r["Date"], r["Créneau"])
        if key not in seen:
            seen.add(key)
            out.append(r)
    return out


def clean_unavailabilities(df: pd.DataFrame, members: list[str]) -> list[tuple[str, date, str]]:
    """Tableau éditable → liste propre de (nom, date, créneau)."""
    out = []
    for _, r in df.iterrows():
        nom, d, c = r.get("Nom"), r.get("Date"), r.get("Créneau")
        if pd.isna(nom) or pd.isna(d) or nom not in members:
            continue
        c = "*" if pd.isna(c) or not str(c).strip() else str(c).strip()
        out.append((str(nom), pd.to_datetime(d).date(), c))
    return out


# ---------- remarques et consignes en texte libre ----------
def parse_quota(n: str) -> int | None:
    """« maximum 2 fois », « pas plus de 3 », « une seule fois »… (texte normalisé)."""
    m = re.search(r"(?:maximum|max\.?|au plus|pas plus de|limitee? a)\s*(?:de\s+)?(\d+|un|une|deux|trois|quatre|cinq|six)\b", n)
    if not m:
        m = re.search(r"\b(\d+|un|une|deux|trois|quatre|cinq|six)\s+(?:seule\s+)?fois\s*(?:maximum|max|au plus)", n)
    if m:
        v = m.group(1)
        return int(v) if v.isdigit() else NUM_WORDS[v]
    return 1 if "seule fois" in n else None


def notes_from_file(file) -> str:
    """Texte d'un fichier de remarques (TXT, PDF, Excel, CSV) : une remarque par ligne."""
    tables, lines = load_document(file.name, file.getvalue())
    out = [l.strip() for l in lines if l.strip()]
    for df in tables:
        for row in df.values.tolist():
            cells = [cell_text(c) for c in row if cell_text(c)]
            if cells:
                out.append(" ".join(cells))
    return "\n".join(dict.fromkeys(out))


def interpret_remarks(text, members, task_names, default_year, period_days):
    """
    Transforme des remarques écrites en consignes pour l'algorithme.
    Retourne {absences, rules, understood, ignored}.
      • absence / indisponibilité  → s'ajoute au tableau des indisponibilités
      • interdit (tâche)           → « Paul ne fait pas l'Accueil »
      • imposé (affectation)       → « Léa doit faire l'Accueil le 12/11 »
      • quota maximum              → « Marie maximum 2 fois »
      • ne pas associer            → « Marie et Paul pas ensemble »
    """
    midx, tidx = build_member_index(members), build_member_index(task_names)
    absences: list[dict] = []
    rules: list[dict] = []
    understood: list[tuple[str, str]] = []
    ignored: list[tuple[str, str]] = []

    def rule(typ, p, other=None, task=None, d=None, slot="*", quota=None):
        rules.append({"Type": typ, "Personne": p, "Autre personne": other, "Tâche": task,
                      "Date": d, "Créneau": slot, "Quota": quota, "Source": "Remarque"})

    for raw in re.split(r"[\n;]+|(?<!\d)\.\s+", text or ""):
        line = clean_name_line(raw)
        if len(line) < 3:
            continue
        n = normalize(line)
        people, ambiguous = match_members_loose(line, midx)
        if ambiguous:
            ignored.append((line, f"nom ambigu (« {', '.join(ambiguous)} ») : précisez le nom complet"))
            continue
        if not people and re.search(r"tout le monde|chacun|\btous\b|\btoutes\b", n):
            people = list(members)
        if not people:
            ignored.append((line, "aucun membre reconnu"))
            continue
        who = ", ".join(people) if len(people) <= 4 else f"{len(people)} personnes"
        found_tasks = match_members(line, tidx)
        dates_raw = extract_dates(line, default_year)
        days = expand_dates(dates_raw, line, False)
        weekdays = [] if dates_raw else sorted({WEEKDAY_IDX[w] for w in WEEKDAY_RE.findall(n)})
        wd_days = [d for d in period_days if d.weekday() in weekdays] if weekdays else []
        slot = detect_slot(line) or "*"
        slot_lbl = "journée" if slot == "*" else slot.lower()

        # 1) quota maximum
        quota = parse_quota(n)
        if quota is not None:
            for p in people:
                rule(T_QUOTA, p, quota=quota)
            understood.append((line, f"Quota : {who} — {quota} participation(s) maximum sur la période"))
            continue

        # 2) ne pas associer
        if len(people) >= 2 and APART_CUE_RE.search(n) and (NEG_RE.search(n) or APART_STRONG_RE.search(n)):
            for a, b in combinations(people, 2):
                rule(T_APART, a, other=b)
            understood.append((line, f"Ne pas mettre ensemble : {' / '.join(people)}"))
            continue

        # 3) absence ou tâche interdite
        strong, neg = STRONG_ABSENCE_RE.search(n), NEG_RE.search(n)
        if strong or neg:
            targets = days or wd_days
            if found_tasks and not strong:
                for p in people:
                    for t in found_tasks:
                        for d in (targets or [None]):
                            rule(T_FORBID, p, task=t, d=d, slot=slot)
                when = f"{len(targets)} jour(s)" if targets else "toute la période"
                understood.append((line, f"Tâche interdite : {who} ↛ {', '.join(found_tasks)} ({when})"))
                continue
            if targets:
                for p in people:
                    for d in targets:
                        absences.append({"Nom": p, "Date": d, "Créneau": slot, "Source": "Remarque"})
                understood.append((line, f"Indisponible : {who} — {len(targets)} jour(s), {slot_lbl}"))
                continue
            ignored.append((line, "précisez une date ou un jour de la semaine"))
            continue

        # 4) affectation imposée
        if IMPOSE_RE.search(n):
            if len(found_tasks) != 1:
                ignored.append((line, "indiquez une seule tâche exactement"))
            elif not days:
                ignored.append((line, "indiquez la date de l'affectation"))
            else:
                for p in people:
                    for d in days:
                        rule(T_FORCE, p, task=found_tasks[0], d=d, slot=slot)
                understood.append((line, f"Imposé : {who} → {found_tasks[0]} ({len(days)} jour(s), {slot_lbl})"))
            continue

        ignored.append((line, "formulation non reconnue (simple information ?)"))

    # dédoublonnage
    seen, uniq_abs = set(), []
    for a in absences:
        k = (a["Nom"], a["Date"], a["Créneau"])
        if k not in seen:
            seen.add(k)
            uniq_abs.append(a)
    seen, uniq_rules = set(), []
    for r in rules:
        k = tuple(str(r[c]) for c in CONS_COLUMNS)
        if k not in seen:
            seen.add(k)
            uniq_rules.append(r)
    return {"absences": uniq_abs, "rules": uniq_rules, "understood": understood, "ignored": ignored}


def clean_constraints(df: pd.DataFrame, members: list[str], task_names: list[str]) -> dict:
    """Tableau « Consignes » (éditable) → structures utilisées par l'algorithme."""
    out = {"forbid": [], "force": [], "caps": {}, "apart": []}
    for _, r in df.iterrows():
        typ, p = r.get("Type"), r.get("Personne")
        if pd.isna(typ) or pd.isna(p) or p not in members:
            continue
        tn = r.get("Tâche")
        d = r.get("Date")
        d = None if pd.isna(d) else pd.to_datetime(d).date()
        c = r.get("Créneau")
        slot = "*" if pd.isna(c) or not str(c).strip() else str(c).strip()
        if typ == T_FORBID and tn in task_names:
            out["forbid"].append((p, tn, d, slot))
        elif typ == T_FORCE and tn in task_names and d is not None:
            out["force"].append((p, tn, d, slot))
        elif typ == T_QUOTA:
            q = r.get("Quota")
            if not pd.isna(q) and int(q) >= 1:
                out["caps"][p] = min(out["caps"].get(p, 10**9), int(q))
        elif typ == T_APART:
            o = r.get("Autre personne")
            if o in members and o != p:
                out["apart"].append((p, o))
    return out


def constraints_to_frame(cons: dict) -> pd.DataFrame:
    """Version lisible des consignes appliquées (affichage + export)."""
    lab = lambda s: "Journée" if s == "*" else s
    fd = lambda d: d.strftime("%d/%m/%Y") if d else "Toute la période"
    rec = []
    for p, tn, d, s in cons["forbid"]:
        rec.append((T_FORBID, p, "", tn, fd(d), lab(s), None))
    for p, tn, d, s in cons["force"]:
        rec.append((T_FORCE, p, "", tn, fd(d), lab(s), None))
    for p, q in cons["caps"].items():
        rec.append((T_QUOTA, p, "", "", "", "", q))
    for a, b in cons["apart"]:
        rec.append((T_APART, a, b, "", "", "", None))
    df = pd.DataFrame(rec, columns=["Type", "Personne", "Autre personne", "Tâche", "Date", "Créneau", "Quota"])
    df["Quota"] = pd.to_numeric(df["Quota"]).astype("Int64")
    return df


# ======================================================================
# 3. ALGORITHME DE GÉNÉRATION
# ======================================================================
def compute_busy_per_slot(slots, unavailabilities) -> list[set[str]]:
    """Pour chaque créneau : ensemble des personnes déjà sollicitées ailleurs."""
    by_date: dict[date, list[tuple[str, str]]] = {}
    for nom, d, c in unavailabilities:
        by_date.setdefault(d, []).append((nom, c))
    return [{n for n, c in by_date.get(d, []) if slot_conflict(c, label)} for d, label in slots]


def plan_constraints(slots, tasks, busy_per_slot, cons, allow_multi) -> dict:
    """
    Prépare les consignes avant les tirages : blocages par tâche, affectations
    imposées (avec contrôle des conflits), quotas, paires à séparer.
    Les indisponibilités externes restent PRIORITAIRES sur les affectations imposées.
    """
    nb = {t["name"]: t["nb"] for t in tasks}
    warnings: list[str] = []

    task_blocks: list[dict[str, set[str]]] = [dict() for _ in slots]
    for person, tn, d, slot in cons["forbid"]:
        for i, (sd, label) in enumerate(slots):
            if (d is None or sd == d) and slot_conflict(slot, label):
                task_blocks[i].setdefault(tn, set()).add(person)

    forced: list[dict[str, list[str]]] = [dict() for _ in slots]
    for person, tn, d, slot in cons["force"]:
        matched = [i for i, (sd, label) in enumerate(slots) if sd == d and slot_conflict(slot, label)]
        if not matched:
            warnings.append(f"Consigne ignorée : {person} → {tn} le {d:%d/%m/%Y} ne correspond à aucun créneau de la période.")
            continue
        for i in matched:
            sd, label = slots[i]
            where = f"{tn}, {fmt_date(sd)} ({label})"
            if person in busy_per_slot[i]:
                warnings.append(f"Affectation non appliquée : {person} est indisponible ({where}).")
            elif person in task_blocks[i].get(tn, ()):
                warnings.append(f"Affectation non appliquée : {person} est aussi interdit(e) sur cette tâche ({where}).")
            elif not allow_multi and any(person in ps for ps in forced[i].values()):
                warnings.append(f"Affectation non appliquée : {person} est déjà imposé(e) sur une autre tâche ({where}).")
            elif person in forced[i].get(tn, []):
                continue
            elif len(forced[i].get(tn, [])) >= nb[tn]:
                warnings.append(f"Affectation non appliquée : la tâche est déjà complète ({where}, {person}).")
            else:
                forced[i].setdefault(tn, []).append(person)

    partners: dict[str, set[str]] = {}
    for a, b in cons["apart"]:
        partners.setdefault(a, set()).add(b)
        partners.setdefault(b, set()).add(a)

    return {"task_blocks": task_blocks, "forced": forced, "caps": dict(cons["caps"]),
            "partners": partners, "warnings": warnings}


def _single_attempt(members, tasks, slots, busy_per_slot, plan, rng, avoid_consec, allow_multi):
    task_blocks, forced = plan["task_blocks"], plan["forced"]
    caps, partners = plan["caps"], plan["partners"]
    count_task = {(m, t["name"]): 0 for m in members for t in tasks}
    count_total = {m: 0 for m in members}
    last_any = {m: -99 for m in members}
    last_task = {(m, t["name"]): -99 for m in members for t in tasks}
    consec = {"any": 0, "task": 0}
    rows, unfilled = [], 0

    def assign(m, tn, s_idx, taken, bucket):
        if last_any[m] == s_idx - 1:
            consec["any"] += 1
        if last_task[(m, tn)] == s_idx - 1:
            consec["task"] += 1
        count_task[(m, tn)] += 1
        count_total[m] += 1
        last_any[m] = last_task[(m, tn)] = s_idx
        taken.add(m)
        bucket.append(m)

    for s_idx, (d, label) in enumerate(slots):
        busy, taken = busy_per_slot[s_idx], set()
        bucket_of = {t["name"]: [] for t in tasks}

        # a) affectations imposées d'abord
        for tn, persons in forced[s_idx].items():
            for m in persons:
                assign(m, tn, s_idx, taken, bucket_of[tn])

        # b) le reste est tiré au sort
        blocks = task_blocks[s_idx]
        avail = {t["name"]: [m for m in t["eligible"] if m not in busy and m not in blocks.get(t["name"], ())]
                 for t in tasks}
        # on sert d'abord la tâche la plus contrainte
        order = sorted(tasks, key=lambda t: (
            len(avail[t["name"]]) / max(t["nb"] - len(bucket_of[t["name"]]), 1), rng.random()))
        row = {}
        for t in order:
            tn, bucket = t["name"], bucket_of[t["name"]]
            if len(bucket) < t["nb"]:
                pool = [m for m in avail[tn]
                        if m not in bucket
                        and (allow_multi or m not in taken)
                        and count_total[m] < caps.get(m, 10**9)]               # quota maximum
                pool.sort(key=lambda m: (
                    count_task[(m, tn)],                                       # 1) rotation par tâche
                    1 if (avoid_consec and last_any[m] == s_idx - 1) else 0,   # 2) pas d'enchaînement
                    count_total[m],                                            # 3) équité globale
                    rng.random(),                                              # 4) hasard
                ))
                for m in pool:
                    if len(bucket) >= t["nb"]:
                        break
                    if partners.get(m) and partners[m] & taken:                # paires à séparer
                        continue
                    assign(m, tn, s_idx, taken, bucket)
            missing = max(t["nb"] - len(bucket), 0)
            unfilled += missing
            row[tn] = bucket + [UNFILLED] * missing
        rows.append((d, label, row))

    # score : plus il est bas, plus le tirage est équitable
    totals = [count_total[m] for m in members if any(m in t["eligible"] for t in tasks)]
    spread_total = (max(totals) - min(totals)) if totals else 0
    spread_tasks = 0
    for t in tasks:
        c = [count_task[(m, t["name"])] for m in t["eligible"]]
        spread_tasks += (max(c) - min(c)) if c else 0
    cost = 1000 * unfilled + 20 * spread_total + 5 * spread_tasks
    if avoid_consec:
        cost += 3 * consec["any"] + 2 * consec["task"]
    return rows, cost, unfilled


def generate_schedule(members, tasks, slots, busy_per_slot, plan, attempts, seed, avoid_consec, allow_multi):
    """Répète le tirage `attempts` fois et garde le plus équitable."""
    rng = random.Random(seed if seed else None)
    best, started = None, time.time()
    for k in range(attempts):
        result = _single_attempt(members, tasks, slots, busy_per_slot, plan, rng, avoid_consec, allow_multi)
        if best is None or result[1] < best[1]:
            best = result
        if not seed and k >= 5 and time.time() - started > 10:      # garde-fou de durée
            break
    return best


# ======================================================================
# 4. CONSTRUCTION DES TABLEAUX DE SORTIE ET EXPORTS
# ======================================================================
def build_outputs(members, tasks, slots, rows, busy_per_slot, unavailabilities):
    task_names = [t["name"] for t in tasks]
    planning_rec, detail_rec = [], []
    for d, label, row in rows:
        rec = {"Date": fmt_date(d), "Créneau": label}
        for tn in task_names:
            rec[tn] = ", ".join(row.get(tn, []))
            for person in row.get(tn, []):
                detail_rec.append({"Date": fmt_date(d), "Créneau": label, "Tâche": tn, "Personne": person})
        planning_rec.append(rec)
    planning = pd.DataFrame(planning_rec)
    detail = pd.DataFrame(detail_rec, columns=["Date", "Créneau", "Tâche", "Personne"])

    stats = pd.DataFrame(0, index=members, columns=task_names)
    for _, r in detail.iterrows():
        if r["Personne"] in stats.index:
            stats.loc[r["Personne"], r["Tâche"]] += 1
    stats["Total"] = stats[task_names].sum(axis=1)
    stats["Créneaux bloqués (plannings externes)"] = [sum(1 for b in busy_per_slot if m in b) for m in members]
    stats.index.name = "Membre"

    unav = pd.DataFrame(
        [{"Nom": n, "Date": d.strftime("%d/%m/%Y"), "Créneau": "Journée" if c == "*" else c}
         for n, d, c in sorted(unavailabilities, key=lambda x: (x[1], x[0]))],
        columns=["Nom", "Date", "Créneau"],
    )
    return planning, stats, detail, unav


def build_csv(planning: pd.DataFrame) -> bytes:
    """CSV compatible Excel français (séparateur « ; », UTF-8 avec BOM)."""
    return planning.to_csv(index=False, sep=";").encode("utf-8-sig")


def build_excel(planning, stats, detail, unav, cons_df, remarks_lines) -> bytes:
    from openpyxl.styles import Alignment, Font, PatternFill

    buf = io.BytesIO()
    with pd.ExcelWriter(buf, engine="openpyxl") as writer:
        planning.to_excel(writer, sheet_name="Planning", index=False)
        stats.to_excel(writer, sheet_name="Récapitulatif")
        detail.to_excel(writer, sheet_name="Détail", index=False)
        unav.to_excel(writer, sheet_name="Indisponibilités", index=False)
        cons_df.to_excel(writer, sheet_name="Consignes", index=False)
        pd.DataFrame({"Remarque": remarks_lines}).to_excel(writer, sheet_name="Remarques", index=False)
        for ws in writer.book.worksheets:
            for cell in ws[1]:
                cell.font = Font(bold=True, color="FFFFFF")
                cell.fill = PatternFill("solid", fgColor="3A7BD5")
                cell.alignment = Alignment(vertical="center", wrap_text=True)
            for col in ws.columns:
                width = max((len(str(c.value)) for c in col if c.value is not None), default=0)
                ws.column_dimensions[col[0].column_letter].width = min(max(12, width + 2), 60)
            ws.freeze_panes = "A2"
    return buf.getvalue()


# ======================================================================
# 5. INTERFACE STREAMLIT
# ======================================================================
CSS = """
<style>
.hero{background:linear-gradient(135deg,#1f3c88,#3a7bd5);color:#fff;padding:1.3rem 1.6rem;
      border-radius:14px;margin-bottom:.8rem}
.hero h1{margin:0;font-size:1.65rem;color:#fff;padding:0}
.hero p{margin:.3rem 0 0;opacity:.92}
.step{display:flex;align-items:center;gap:.75rem;margin:1.8rem 0 .6rem}
.step .num{background:#3a7bd5;color:#fff;min-width:2.1rem;height:2.1rem;border-radius:50%;
           display:flex;align-items:center;justify-content:center;font-weight:700}
.step.done .num{background:#2e9e5b}
.step .title{font-size:1.3rem;font-weight:700}
.step .opt{font-size:.85rem;font-weight:400;opacity:.65}
</style>
"""


def step_html(n: int, title: str, done: bool = False, optional: bool = False) -> str:
    cls = "step done" if done else "step"
    opt = " <span class='opt'>(optionnel)</span>" if optional else ""
    mark = "✓" if done else n
    return f"<div class='{cls}'><div class='num'>{mark}</div><div class='title'>{title}{opt}</div></div>"


def preview_document(file) -> None:
    try:
        tables, lines = load_document(file.name, file.getvalue())
    except Exception as exc:
        st.warning(f"Lecture impossible : {exc}")
        return
    if tables:
        df = tables[0].head(20).fillna("").astype(str)
        df.columns = [str(c) for c in df.columns]
        st.dataframe(df, hide_index=True, **STRETCH)
        if len(tables) > 1:
            st.caption(f"{len(tables)} feuilles/tableaux détectés — seul le premier est affiché.")
    elif lines:
        st.text("\n".join(lines[:25]))
    else:
        st.caption("Document vide ou illisible.")


def append_names(new_names: list[str]) -> None:
    """Callback : ajoute des noms à la zone de saisie (sans doublons)."""
    merged = parse_names(st.session_state.get("names_text", "") + "\n" + "\n".join(new_names))
    st.session_state["names_text"] = "\n".join(merged)


def import_names_button(label: str, file, key: str) -> None:
    if file is None:
        return
    try:
        names = extract_member_names(file.name, file.getvalue())
    except Exception as exc:
        st.warning(f"Lecture impossible : {exc}")
        return
    if names:
        st.button(f"{label} ({len(names)})", key=key, on_click=append_names, args=(names,))
    else:
        st.caption("Aucun nom détecté dans ce fichier.")


def show_result(res: dict) -> None:
    planning, stats, task_names = res["planning"], res["stats"], res["task_names"]

    c1, c2, c3, c4 = st.columns(4)
    c1.metric("Créneaux planifiés", len(planning))
    c2.metric("Tâches", len(task_names))
    c3.metric("Membres", len(stats))
    c4.metric("Postes non pourvus", res["unfilled"])
    if res["unfilled"]:
        st.warning("Certains postes n'ont pas pu être pourvus (trop peu de personnes disponibles, habilitées ou "
                   "sous quota). Ils sont signalés par « ⚠️ Non pourvu » dans le tableau.")
    else:
        st.success("Planning généré : aucun conflit avec les plannings externes ni avec vos consignes.")
    if res["warnings"]:
        with st.expander(f"⚠️ {len(res['warnings'])} consigne(s) non appliquée(s)", expanded=True):
            for w in res["warnings"]:
                st.write("• " + w)

    tab1, tab2, tab3, tab4 = st.tabs(["📅 Planning", "⚖️ Équité", "🚫 Indisponibilités", "📝 Consignes appliquées"])
    with tab1:
        styler = planning.style
        painter = getattr(styler, "map", None) or styler.applymap
        styled = painter(lambda v: "background-color:#ffe3e3;color:#a30000" if UNFILLED in str(v) else "",
                         subset=task_names)
        st.dataframe(styled, hide_index=True, **STRETCH)
    with tab2:
        st.caption("Nombre de participations par personne et par tâche.")
        st.dataframe(stats, **STRETCH)
        st.bar_chart(stats["Total"])
    with tab3:
        if res["unav"].empty:
            st.caption("Aucune indisponibilité sur la période.")
        else:
            st.dataframe(res["unav"], hide_index=True, **STRETCH)
    with tab4:
        if res["cons"].empty:
            st.caption("Aucune consigne particulière.")
        else:
            st.dataframe(res["cons"], hide_index=True, **STRETCH)

    st.markdown("##### 📥 Export")
    d1, d2 = st.columns(2)
    d1.download_button("⬇️ Télécharger en Excel (.xlsx)", data=res["xlsx"], file_name=f"{res['basename']}.xlsx",
                       mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
    d2.download_button("⬇️ Télécharger en CSV (.csv)", data=res["csv"], file_name=f"{res['basename']}.csv",
                       mime="text/csv")


def main() -> None:
    st.set_page_config(page_title="Planning de participation", page_icon="🗓️", layout="wide")
    st.markdown(CSS, unsafe_allow_html=True)
    st.session_state.setdefault("names_text", "")

    # ---------------- Barre latérale ----------------
    with st.sidebar:
        st.header("🧭 Progression")
        progress_box = st.empty()
        st.divider()
        st.caption("Formats lus : Excel (.xlsx / .xls), CSV, TXT, PDF (texte ou tableaux).")
        if st.button("↺ Tout réinitialiser"):
            st.session_state.clear()
            st.rerun()

    st.markdown(
        "<div class='hero'><h1>🗓️ Générateur de planning de participation</h1>"
        "<p>Tirage aléatoire équitable, sans répétition abusive et sans conflit avec les autres services.</p></div>",
        unsafe_allow_html=True,
    )

    members = parse_names(st.session_state.get("names_text", ""))

    # =================== ÉTAPE 1 : IMPORTATION ===================
    ph1 = st.empty()
    col_a, col_b = st.columns(2)
    with col_a:
        base_file = st.file_uploader(
            "📘 Document de base du service", type=FILE_TYPES, key="base_file",
            help="Liste des membres et/ou règles du service. Les noms détectés peuvent être repris à l'étape 2.")
    with col_b:
        ext_files = st.file_uploader(
            "🔄 Plannings d'autres services (synchronisation)", type=FILE_TYPES, key="ext_files",
            accept_multiple_files=True,
            help="Toute personne qui y figure à une date donnée sera considérée comme indisponible.")
    with st.expander("⚙️ Options d'analyse des fichiers"):
        default_year = int(st.number_input(
            "Année à utiliser pour les dates sans année (ex. « 12/11 »)", 2000, 2100,
            date.today().year, key="default_year"))

    if base_file is not None:
        with st.expander("👁️ Aperçu du document de base"):
            preview_document(base_file)
            st.caption("Les règles écrites du document ne sont pas interprétées automatiquement : "
                       "elles servent de référence, et les noms sont repris à l'étape 2.")

    ext_records: list[dict] = []
    if ext_files and members:
        for f in ext_files:
            try:
                recs = parse_external_file(f.name, f.getvalue(), tuple(members), default_year)
                ext_records += recs
                st.caption(f"📄 **{f.name}** → {len(recs)} indisponibilité(s) détectée(s)")
            except Exception as exc:
                st.warning(f"⚠️ {f.name} : lecture impossible ({exc})")
    elif ext_files:
        st.caption("ℹ️ L'analyse des plannings externes démarrera dès que la liste des membres sera saisie (étape 2).")

    step1_done = base_file is not None or bool(ext_files)
    ph1.markdown(step_html(1, "Importation des bases de référence", step1_done, optional=True),
                 unsafe_allow_html=True)

    # =================== ÉTAPE 2 : RESSOURCES HUMAINES ===================
    ph2 = st.empty()
    left, right = st.columns([3, 2])
    with left:
        st.text_area(
            "Noms des membres du service (un par ligne, ou séparés par , ou ;)",
            key="names_text", height=230, placeholder="Marie Dupont\nPaul Martin\nLéa Bernard")
    with right:
        st.markdown("**Raccourcis d'import**")
        import_names_button("➕ Reprendre les noms du document de base", base_file, "btn_names_base")
        list_file = st.file_uploader("Ou importer une liste de noms", type=FILE_TYPES, key="names_file")
        import_names_button("➕ Ajouter les noms de ce fichier", list_file, "btn_names_list")
    members = parse_names(st.session_state.get("names_text", ""))
    st.caption(f"👥 {len(members)} membre(s) enregistré(s)")
    ph2.markdown(step_html(2, "Saisie des ressources humaines", bool(members)), unsafe_allow_html=True)

    # =================== ÉTAPE 3 : TÂCHES ===================
    ph3 = st.empty()
    tasks: list[dict] = []
    tasks_valid = False
    if not members:
        st.info("➡️ Saisissez au moins un nom à l'étape 2 pour configurer les tâches.")
    else:
        sig = hashlib.md5("|".join(members).encode()).hexdigest()[:8]   # réinitialise les listes si les noms changent
        n_tasks = int(st.number_input("Nombre de tâches différentes à couvrir", 1, 20, 2, key="n_tasks"))
        problems: list[str] = []
        for i in range(n_tasks):
            with st.container(border=True):
                c1, c2, c3 = st.columns([2, 1, 3])
                name = c1.text_input(f"Nom de la tâche {i + 1}", value=f"Tâche {i + 1}", key=f"task_name_{i}").strip()
                nb = int(c2.number_input("Personnes par créneau", 1, max(len(members), 1), 1, key=f"task_nb_{i}_{sig}"))
                sel = c3.multiselect(
                    "Personnes habilitées", [EVERYONE] + members, default=[EVERYONE], key=f"task_elig_{i}_{sig}",
                    help="Retirez « Tout le monde » pour choisir des personnes précises.")
                eligible = list(members) if EVERYONE in sel else list(sel)
                c3.caption(f"✅ {len(eligible)} personne(s) habilitée(s)")
                if not name:
                    problems.append(f"Tâche {i + 1} : le nom est vide.")
                if not eligible:
                    problems.append(f"Tâche « {name or i + 1} » : aucune personne habilitée.")
                elif nb > len(eligible):
                    problems.append(f"Tâche « {name} » : {nb} personnes demandées pour {len(eligible)} habilitée(s).")
                tasks.append({"name": name, "eligible": eligible, "nb": nb})
        names_norm = [normalize(t["name"]) for t in tasks]
        if len(set(names_norm)) != len(names_norm):
            problems.append("Deux tâches portent le même nom.")
        if any(n in ("date", "creneau") for n in names_norm):
            problems.append("Les noms « Date » et « Créneau » sont réservés.")
        for p in problems:
            st.error(p)
        tasks_valid = not problems
    ph3.markdown(step_html(3, "Configuration des tâches", tasks_valid), unsafe_allow_html=True)

    # =================== ÉTAPE 4 : PÉRIODE, CRÉNEAUX ET REMARQUES ===================
    ph4 = st.empty()
    ready = bool(members) and tasks_valid
    task_names = [t["name"] for t in tasks]
    errors: list[str] = []
    slots: list[tuple[date, str]] = []
    remark_absences: list[dict] = []
    remark_rules: list[dict] = []
    note_text = ""
    start = end = date.today()
    attempts, seed, avoid_consec, allow_multi = 300, 0, True, False

    if not ready:
        st.info("➡️ Complétez les étapes 2 et 3 pour définir la période et vos remarques.")
    else:
        st.markdown("##### Période et créneaux")
        p1, p2, p3 = st.columns(3)
        start = p1.date_input("Début de la période", value=date.today(), key="p_start", format="DD/MM/YYYY")
        end = p2.date_input("Fin de la période", value=date.today() + timedelta(days=13),
                            key="p_end", format="DD/MM/YYYY")
        days_sel = p3.multiselect("Jours concernés", WEEKDAYS_FR, default=WEEKDAYS_FR[:5], key="p_days")
        slots_txt = st.text_input("Créneaux par jour (séparés par des virgules)", value="Journée", key="p_slots",
                                  help="Exemples : « Journée » ou « Matin, Après-midi ». Les libellés Matin / "
                                       "Après-midi / Soir / Journée sont reconnus pour croiser les indisponibilités.")
        with st.expander("🎛️ Options avancées"):
            attempts = st.slider("Nombre de tirages comparés (le plus équitable est gardé)", 20, 1000, 300, 20)
            seed = int(st.number_input("Graine aléatoire (0 = résultat différent à chaque génération)",
                                       0, 10**9, 0, key="seed"))
            avoid_consec = st.checkbox("Éviter qu'une personne soit placée sur deux créneaux consécutifs", True)
            allow_multi = st.checkbox("Autoriser une même personne sur plusieurs tâches dans un même créneau", False)

        period_days: list[date] = []
        if end < start:
            errors.append("La date de fin précède la date de début.")
        elif (end - start).days > 730:
            errors.append("La période ne peut pas dépasser 2 ans.")
        else:
            period_days = [start + timedelta(days=i) for i in range((end - start).days + 1)]
            labels = parse_names(slots_txt)
            slots = [(d, lab) for d in period_days if WEEKDAYS_FR[d.weekday()] in days_sel for lab in labels]
            if not slots:
                errors.append("Aucun créneau : vérifiez la période, les jours et les libellés de créneaux.")
            elif len(slots) > 1500:
                errors.append(f"{len(slots)} créneaux : réduisez la période (maximum 1500).")

        # ---- remarques et informations libres ----
        st.markdown("##### 📝 Remarques et consignes")
        st.caption("Optionnel : écrivez, une par ligne, les informations qui doivent orienter le tirage. "
                   "Elles sont interprétées ci-dessous et restent modifiables à l'étape 5.")
        r1, r2 = st.columns([3, 2])
        with r1:
            st.text_area("Vos remarques", key="remarks_text", height=180,
                         placeholder="Marie est en congé du 16/11 au 18/11\n"
                                     "Paul ne peut pas le mardi matin\n"
                                     "Omar ne fait pas Compte-rendu\n"
                                     "Léa doit faire Accueil le 12/11\n"
                                     "Sophie maximum 2 fois\n"
                                     "Marie et Paul pas ensemble")
        with r2:
            notes_file = st.file_uploader("Ou importer un fichier de remarques", type=FILE_TYPES, key="notes_file")
            with st.expander("💡 Formulations comprises"):
                st.markdown(
                    "- **Absence** : « Marie absente le 12/11 », « Paul en congé du 16/11 au 18/11 », "
                    "« Léa ne peut pas le lundi matin »\n"
                    "- **Tâche interdite** : « Omar ne fait pas Compte-rendu » (avec une date : ce jour-là seulement)\n"
                    "- **Affectation imposée** : « Léa doit faire Accueil le 12/11 »\n"
                    "- **Quota** : « Sophie maximum 2 fois », « tout le monde max 3 fois »\n"
                    "- **Séparer** : « Marie et Paul pas ensemble »")
        note_text = st.session_state.get("remarks_text", "")
        if notes_file is not None:
            try:
                note_text += "\n" + notes_from_file(notes_file)
            except Exception as exc:
                st.warning(f"Lecture du fichier de remarques impossible : {exc}")
        if note_text.strip():
            interp = interpret_remarks(note_text, members, task_names, default_year, period_days)
            remark_absences, remark_rules = interp["absences"], interp["rules"]
            if interp["understood"]:
                with st.expander(f"✅ {len(interp['understood'])} remarque(s) interprétée(s)", expanded=True):
                    for line, summary in interp["understood"]:
                        st.write(f"• « {line} » → {summary}")
            if interp["ignored"]:
                with st.expander(f"⚠️ {len(interp['ignored'])} ligne(s) non interprétée(s) — ignorées par l'algorithme",
                                 expanded=True):
                    for line, why in interp["ignored"]:
                        st.write(f"• « {line} » — {why}")
                    st.caption("Reformulez la remarque, ou ajoutez la consigne à la main dans les tableaux de l'étape 5.")
        for e in errors:
            st.error(e)
    ph4.markdown(step_html(4, "Période, créneaux et remarques", ready and not errors), unsafe_allow_html=True)

    # =================== ÉTAPE 5 : VÉRIFICATION, GÉNÉRATION, EXPORT ===================
    ph5 = st.empty()
    if not ready:
        st.info("➡️ Complétez les étapes précédentes pour débloquer la génération.")
    else:
        sig5 = hashlib.md5(f"{'|'.join(members)}|{'|'.join(task_names)}|{start}|{end}".encode()).hexdigest()[:8]

        # ---- indisponibilités : plannings externes + remarques ----
        st.markdown("##### Indisponibilités")
        st.caption("Détectées dans les plannings externes et dans vos remarques ; corrigez, supprimez ou ajoutez des "
                   "lignes. Créneau « * » = toute la journée.")
        base_df = pd.DataFrame(ext_records + remark_absences, columns=["Nom", "Date", "Créneau", "Source"])
        if not base_df.empty and not errors:
            base_df = base_df[(base_df["Date"] >= start) & (base_df["Date"] <= end)]
        if not base_df.empty:
            base_df = base_df.sort_values(["Date", "Nom"]).reset_index(drop=True)
        base_df["Date"] = pd.to_datetime(base_df["Date"])
        base_df["Nom"] = base_df["Nom"].astype(object)
        key_unav = "unav_" + hashlib.md5(f"{base_df.to_csv()}|{sig5}".encode()).hexdigest()[:10]
        edited = st.data_editor(
            base_df, num_rows="dynamic", hide_index=True, key=key_unav, **STRETCH,
            column_config={
                "Nom": st.column_config.SelectboxColumn("Nom", options=members, required=True),
                "Date": st.column_config.DateColumn("Date", format="DD/MM/YYYY", required=True),
                "Créneau": st.column_config.TextColumn("Créneau", default="*"),
                "Source": st.column_config.TextColumn("Source", disabled=True),
            })
        unavailabilities = clean_unavailabilities(edited, members)

        # ---- consignes issues des remarques ----
        st.markdown("##### Consignes")
        st.caption("Interdictions de tâche, affectations imposées, quotas et personnes à ne pas associer. "
                   "Les indisponibilités ci-dessus restent prioritaires sur les affectations imposées.")
        cons_df = pd.DataFrame(remark_rules, columns=CONS_COLUMNS)
        cons_df["Date"] = pd.to_datetime(cons_df["Date"])
        cons_df["Quota"] = pd.to_numeric(cons_df["Quota"])
        key_cons = "cons_" + hashlib.md5(f"{cons_df.to_csv()}|{sig5}".encode()).hexdigest()[:10]
        edited_cons = st.data_editor(
            cons_df, num_rows="dynamic", hide_index=True, key=key_cons, **STRETCH,
            column_config={
                "Type": st.column_config.SelectboxColumn("Type", options=CONS_TYPES, required=True),
                "Personne": st.column_config.SelectboxColumn("Personne", options=members, required=True),
                "Autre personne": st.column_config.SelectboxColumn("Autre personne", options=members,
                                                                   help="Pour « Ne pas associer »"),
                "Tâche": st.column_config.SelectboxColumn("Tâche", options=task_names,
                                                          help="Pour « Interdit » et « Imposé »"),
                "Date": st.column_config.DateColumn("Date", format="DD/MM/YYYY",
                                                    help="Obligatoire pour « Imposé » ; vide = toute la période"),
                "Créneau": st.column_config.TextColumn("Créneau", default="*"),
                "Quota": st.column_config.NumberColumn("Quota", min_value=1, step=1, format="%d",
                                                       help="Pour « Quota maximum » (total sur la période)"),
                "Source": st.column_config.TextColumn("Source", disabled=True),
            })

        st.markdown("##### Génération")
        if st.button("🎲 Générer le planning", type="primary", disabled=bool(errors)):
            with st.spinner("Tirage en cours…"):
                cons = clean_constraints(edited_cons, members, task_names)
                busy = compute_busy_per_slot(slots, unavailabilities)
                plan = plan_constraints(slots, tasks, busy, cons, allow_multi)
                rows, _cost, unfilled = generate_schedule(
                    members, tasks, slots, busy, plan, attempts, seed, avoid_consec, allow_multi)
                planning, stats, detail, unav = build_outputs(members, tasks, slots, rows, busy, unavailabilities)
                cons_view = constraints_to_frame(cons)
                remarks_lines = [l.strip() for l in re.split(r"[\n;]+", note_text) if l.strip()]
                st.session_state["result"] = {
                    "planning": planning, "stats": stats, "unav": unav, "cons": cons_view,
                    "unfilled": unfilled, "warnings": plan["warnings"],
                    "task_names": task_names,
                    "xlsx": build_excel(planning, stats, detail, unav, cons_view, remarks_lines),
                    "csv": build_csv(planning),
                    "basename": f"planning_{start:%Y%m%d}_{end:%Y%m%d}",
                }
        if "result" in st.session_state:
            st.divider()
            show_result(st.session_state["result"])
    ph5.markdown(step_html(5, "Vérification, génération et export", "result" in st.session_state),
                 unsafe_allow_html=True)

    # ---------------- Progression (barre latérale) ----------------
    checks = [
        ("Import des documents", step1_done),
        ("Membres saisis", bool(members)),
        ("Tâches configurées", tasks_valid),
        ("Période et remarques", ready and not errors),
        ("Planning généré", "result" in st.session_state),
    ]
    progress_box.markdown("\n\n".join(f"{'✅' if ok else '⬜'} {label}" for label, ok in checks))


if __name__ == "__main__":
    from streamlit.runtime import exists as _streamlit_running

    if _streamlit_running():
        main()
    else:
        # Lancé avec « python planning_app.py » ou le bouton Run de l'éditeur
        print("\n⚠️  Ce programme doit être lancé avec Streamlit :\n\n"
              "    streamlit run planning_app.py\n")
