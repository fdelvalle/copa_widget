# -*- coding: utf-8 -*-
"""
Copa Widget — gadget de Copa do Mundo em tempo real para Windows.
Bandeja do sistema + painel com abas: Ao Vivo / Hoje / Classificacao.
Bandeiras das selecoes (flagcdn) e detalhe do jogo com jogadores/posicoes.
Fonte de dados: football-data.org (v4). Time favorito destacado.
"""
import os
import json
import threading
import datetime as dt
from urllib.request import Request, urlopen
from urllib.error import HTTPError, URLError

try:
    import winsound
except Exception:  # noqa
    winsound = None

import tkinter as tk
from tkinter import ttk, simpledialog

from PIL import Image, ImageTk

import pystray
from PIL import ImageDraw

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.path.join(BASE_DIR, "config.json")
FLAGS_DIR = os.path.join(BASE_DIR, "flags")
API_BASE = "https://api.football-data.org/v4"

# ---- paleta ----
BG = "#0f1419"
CARD = "#1b2430"
CARD_ALT = "#161f2b"
FG = "#e6edf3"
MUTED = "#8b98a5"
ACCENT = "#3fb950"      # verde campo
LIVE = "#f85149"        # vermelho ao vivo
FAV = "#d29922"         # dourado time favorito
HEADER = "#58a6ff"

LIVE_STATUSES = {"LIVE", "IN_PLAY", "PAUSED"}
FLAG_H = 16  # altura da bandeira em px

# codigo FIFA (tla) -> codigo do pais no flagcdn (ISO 3166-1 alpha-2 / subdivisao)
FLAG_ISO = {
    "BIH": "ba", "PAN": "pa", "CPV": "cv", "COD": "cd", "CIV": "ci",
    "URY": "uy", "GER": "de", "ESP": "es", "PAR": "py", "ARG": "ar",
    "GHA": "gh", "BRA": "br", "POR": "pt", "JPN": "jp", "MEX": "mx",
    "ENG": "gb-eng", "USA": "us", "KOR": "kr", "FRA": "fr", "RSA": "za",
    "ALG": "dz", "AUS": "au", "NZL": "nz", "SUI": "ch", "ECU": "ec",
    "SWE": "se", "CZE": "cz", "CRO": "hr", "KSA": "sa", "TUN": "tn",
    "TUR": "tr", "QAT": "qa", "SEN": "sn", "JOR": "jo", "BEL": "be",
    "IRQ": "iq", "UZB": "uz", "MAR": "ma", "AUT": "at", "COL": "co",
    "EGY": "eg", "CAN": "ca", "HAI": "ht", "IRN": "ir", "NED": "nl",
    "NOR": "no", "SCO": "gb-sct", "CUW": "cw", "WAL": "gb-wls",
    "NIR": "gb-nir", "ITA": "it", "NGA": "ng", "CMR": "cm", "POL": "pl",
    "DEN": "dk", "SRB": "rs", "CHI": "cl", "PER": "pe", "VEN": "ve",
}

# traducao de posicoes (en -> pt) para o detalhe
POS_PT = {
    "Goalkeeper": "Goleiro",
    "Centre-Back": "Zagueiro", "Defence": "Defensor", "Defender": "Defensor",
    "Left-Back": "Lateral-esq.", "Right-Back": "Lateral-dir.",
    "Defensive Midfield": "Volante", "Central Midfield": "Meia-central",
    "Attacking Midfield": "Meia-atac.", "Midfield": "Meio-campo",
    "Left Midfield": "Meia-esq.", "Right Midfield": "Meia-dir.",
    "Left Winger": "Ponta-esq.", "Right Winger": "Ponta-dir.",
    "Centre-Forward": "Centroavante", "Offence": "Atacante", "Forward": "Atacante",
}


def bucket(pos):
    """Agrupa a posicao em um dos baldes ordenados."""
    p = (pos or "").lower()
    if "keeper" in p:
        return (0, "Goleiros")
    if "back" in p or "defen" in p:
        return (1, "Defensores")
    if "midfield" in p:
        return (2, "Meio-campo")
    if any(k in p for k in ("forward", "winger", "offence", "striker", "attack")):
        return (3, "Atacantes")
    return (4, "Outros")


def lines_counts(formation):
    """'4-3-3' -> [4,3,3]; vazio/invalido -> [4,3,3]."""
    nums = [int(x) for x in str(formation or "").split("-") if x.strip().isdigit()]
    return nums if nums else [4, 3, 3]


def short_name(name):
    parts = (name or "").split()
    s = parts[-1] if parts else (name or "?")
    return s[:11]


def load_config():
    with open(CONFIG_PATH, "r", encoding="utf-8") as f:
        return json.load(f)


def save_config(cfg):
    with open(CONFIG_PATH, "w", encoding="utf-8") as f:
        json.dump(cfg, f, indent=2, ensure_ascii=False)


def api_get(path, token):
    req = Request(API_BASE + path, headers={"X-Auth-Token": token})
    try:
        with urlopen(req, timeout=20) as resp:
            return json.loads(resp.read().decode("utf-8")), None
    except HTTPError as e:
        if e.code == 403:
            return None, "Token invalido ou sem acesso (403)."
        if e.code == 429:
            return None, "Limite de chamadas (429). Aguarde 1 min."
        if e.code == 404:
            return None, "Nao encontrado (404)."
        return None, f"Erro HTTP {e.code}."
    except URLError as e:
        return None, f"Sem conexao: {e.reason}"
    except Exception as e:  # noqa
        return None, f"Falha: {e}"


def parse_utc(s):
    try:
        return dt.datetime.fromisoformat(s.replace("Z", "+00:00")).astimezone()
    except Exception:
        return None


class CopaWidget:
    def __init__(self):
        self.cfg = load_config()
        self.matches = []
        self.standings = []
        self.last_update = None
        self.flag_imgs = {}      # iso -> PhotoImage (mantem referencia)
        self.squad_cache = {}    # team_id -> squad list
        self.prev_match = {}     # match_id -> {status, h, a}
        self.events = {}         # match_id -> [eventos da timeline]
        self._apifb_fixture = {} # match_id -> fixture id (API-Football)
        self._has_live = False
        self._first_apply = True
        os.makedirs(FLAGS_DIR, exist_ok=True)

        self.root = tk.Tk()
        self.root.title("Copa Widget")
        self.root.configure(bg=BG)
        self.root.geometry("440x580")
        self.root.minsize(400, 440)
        self.root.protocol("WM_DELETE_WINDOW", self.hide_window)

        self._build_styles()
        self._build_ui()

        if not self.cfg.get("token"):
            self.root.after(200, self.ask_token)

        self._build_tray()
        self.refresh_async()
        self._schedule_refresh()

    # ---------- estilos ----------
    def _build_styles(self):
        st = ttk.Style()
        try:
            st.theme_use("clam")
        except tk.TclError:
            pass
        st.configure("TNotebook", background=BG, borderwidth=0)
        st.configure("TNotebook.Tab", background=CARD_ALT, foreground=MUTED,
                     padding=(14, 7), borderwidth=0, font=("Segoe UI", 10, "bold"))
        st.map("TNotebook.Tab", background=[("selected", CARD)],
               foreground=[("selected", FG)])
        st.configure("Treeview", background=CARD, fieldbackground=CARD,
                     foreground=FG, borderwidth=0, rowheight=24, font=("Segoe UI", 9))
        st.configure("Treeview.Heading", background=CARD_ALT, foreground=MUTED,
                     font=("Segoe UI", 9, "bold"), borderwidth=0)
        st.map("Treeview", background=[("selected", "#243447")])

    # ---------- scroll helper ----------
    def _make_scroll(self, parent):
        canvas = tk.Canvas(parent, bg=BG, highlightthickness=0)
        sb = ttk.Scrollbar(parent, orient="vertical", command=canvas.yview)
        inner = tk.Frame(canvas, bg=BG)
        inner.bind("<Configure>",
                   lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        win = canvas.create_window((0, 0), window=inner, anchor="nw")
        canvas.bind("<Configure>", lambda e: canvas.itemconfig(win, width=e.width))
        canvas.configure(yscrollcommand=sb.set)
        canvas.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")

        def on_wheel(e):
            canvas.yview_scroll(int(-e.delta / 120), "units")
        canvas.bind("<Enter>", lambda e: canvas.bind_all("<MouseWheel>", on_wheel))
        canvas.bind("<Leave>", lambda e: canvas.unbind_all("<MouseWheel>"))
        return inner

    # ---------- UI ----------
    def _build_ui(self):
        top = tk.Frame(self.root, bg=BG)
        top.pack(fill="x", padx=10, pady=(10, 4))
        tk.Label(top, text="⚽  COPA — tempo real", bg=BG, fg=ACCENT,
                 font=("Segoe UI", 13, "bold")).pack(side="left")
        tk.Button(top, text="↻", command=self.refresh_async, bg=CARD, fg=FG, bd=0,
                  font=("Segoe UI", 12), activebackground=CARD_ALT,
                  activeforeground=ACCENT, cursor="hand2", width=3).pack(side="right")
        tk.Button(top, text="⚙", command=self.open_settings, bg=CARD, fg=FG, bd=0,
                  font=("Segoe UI", 11), activebackground=CARD_ALT,
                  activeforeground=ACCENT, cursor="hand2", width=3
                  ).pack(side="right", padx=(0, 6))

        self.status = tk.Label(self.root, text="Carregando...", bg=BG, fg=MUTED,
                               anchor="w", font=("Segoe UI", 8))
        self.status.pack(fill="x", padx=12)

        self.nb = ttk.Notebook(self.root)
        self.nb.pack(fill="both", expand=True, padx=8, pady=8)

        self.tab_live = tk.Frame(self.nb, bg=BG)
        self.nb.add(self.tab_live, text="Ao Vivo")
        self.live_inner = self._make_scroll(self.tab_live)

        self.tab_today = tk.Frame(self.nb, bg=BG)
        self.nb.add(self.tab_today, text="Hoje")
        self.today_inner = self._make_scroll(self.tab_today)

        self.tab_table = tk.Frame(self.nb, bg=BG)
        self.nb.add(self.tab_table, text="Classificação")
        self._build_table_tab()

    def _build_table_tab(self):
        cols = ("J", "V", "E", "D", "SG", "P")
        self.tree = ttk.Treeview(self.tab_table, columns=cols, show="tree headings")
        self.tree.heading("#0", text="Grupo / Time")
        self.tree.column("#0", width=200, anchor="w")
        for c in cols:
            self.tree.heading(c, text=c)
            self.tree.column(c, width=32, anchor="center")
        self.tree.column("P", width=38)
        self.tree.tag_configure("group", background=CARD_ALT, foreground=HEADER,
                                font=("Segoe UI", 9, "bold"))
        self.tree.tag_configure("fav", foreground=FAV, font=("Segoe UI", 9, "bold"))
        sb = ttk.Scrollbar(self.tab_table, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True, padx=(6, 0), pady=6)
        sb.pack(side="right", fill="y", pady=6)

    # ---------- bandeja ----------
    def _make_icon_image(self):
        img = Image.new("RGB", (64, 64), BG)
        d = ImageDraw.Draw(img)
        d.ellipse((6, 6, 58, 58), fill="#ffffff", outline="#222222", width=2)
        d.polygon([(32, 20), (44, 30), (39, 45), (25, 45), (20, 30)], fill="#1b1b1b")
        return img

    def _build_tray(self):
        menu = pystray.Menu(
            pystray.MenuItem("Abrir painel", self._tray_show, default=True),
            pystray.MenuItem("Atualizar agora",
                             lambda i, t: self.root.after(0, self.refresh_async)),
            pystray.MenuItem("Configurações",
                             lambda i, t: self.root.after(0, self.open_settings)),
            pystray.MenuItem("Testar alerta ⚽",
                             lambda i, t: self.root.after(0, lambda: self._alert(
                                 "kickoff", self.cfg.get("favorite_team") or "Seu time"))),
            pystray.Menu.SEPARATOR,
            pystray.MenuItem("Sair", self._tray_quit),
        )
        self.icon = pystray.Icon("CopaWidget", self._make_icon_image(),
                                 "Copa Widget", menu)
        threading.Thread(target=self.icon.run, daemon=True).start()

    def _tray_show(self, icon=None, item=None):
        self.root.after(0, self.show_window)

    def _tray_quit(self, icon=None, item=None):
        self.icon.stop()
        self.root.after(0, self.root.destroy)

    def show_window(self):
        self.root.deiconify()
        self.root.lift()
        self.root.focus_force()

    def hide_window(self):
        self.root.withdraw()

    # ---------- config / token ----------
    def ask_token(self):
        token = simpledialog.askstring(
            "Configurar API",
            "Cole sua API key gratuita do football-data.org:\n"
            "(registre em https://www.football-data.org/client/register)",
            parent=self.root)
        if token:
            self.cfg["token"] = token.strip()
            save_config(self.cfg)
            self.refresh_async()

    def open_settings(self):
        win = tk.Toplevel(self.root)
        win.title("Configurações")
        win.configure(bg=BG)
        win.geometry("400x400")
        win.transient(self.root)

        def row(label, value):
            tk.Label(win, text=label, bg=BG, fg=MUTED,
                     font=("Segoe UI", 9)).pack(anchor="w", padx=14, pady=(12, 0))
            e = tk.Entry(win, bg=CARD, fg=FG, insertbackground=FG, bd=0,
                         font=("Segoe UI", 10))
            e.insert(0, value)
            e.pack(fill="x", padx=14, ipady=4)
            return e

        e_token = row("API key (football-data.org)", self.cfg.get("token", ""))
        e_team = row("Time favorito (ex: Brazil)", self.cfg.get("favorite_team", ""))
        e_ref = row("Atualizar a cada (segundos)", str(self.cfg.get("refresh_seconds", 60)))
        e_apifb = row("API-Football key (opcional — lances reais)",
                      self.cfg.get("apifootball_key", ""))

        alerts_var = tk.BooleanVar(value=self.cfg.get("alerts", True))
        sound_var = tk.BooleanVar(value=self.cfg.get("sound", True))

        def check(text, var):
            cb = tk.Checkbutton(win, text=text, variable=var, bg=BG, fg=FG,
                                selectcolor=CARD, activebackground=BG,
                                activeforeground=ACCENT, bd=0, anchor="w",
                                font=("Segoe UI", 9))
            cb.pack(fill="x", padx=12, pady=(8, 0))

        check("Avisar quando meu time entrar em campo / marcar gol", alerts_var)
        check("Tocar som no alerta", sound_var)

        def save():
            self.cfg["token"] = e_token.get().strip()
            self.cfg["favorite_team"] = e_team.get().strip()
            try:
                self.cfg["refresh_seconds"] = max(30, int(e_ref.get()))
            except ValueError:
                self.cfg["refresh_seconds"] = 60
            self.cfg["alerts"] = alerts_var.get()
            self.cfg["sound"] = sound_var.get()
            self.cfg["apifootball_key"] = e_apifb.get().strip()
            self._apifb_fixture.clear()
            save_config(self.cfg)
            win.destroy()
            self.refresh_async()

        tk.Button(win, text="Salvar", command=save, bg=ACCENT, fg="#06210d", bd=0,
                  font=("Segoe UI", 10, "bold"), cursor="hand2",
                  activebackground="#2ea043").pack(pady=16, padx=14, fill="x", ipady=4)

    # ---------- favorito ----------
    def _is_fav(self, team):
        fav = (self.cfg.get("favorite_team") or "").strip().lower()
        if not fav or not team:
            return False
        for key in ("name", "shortName", "tla"):
            v = (team.get(key) or "").lower()
            if v and (fav in v or v in fav):
                return True
        return False

    # ---------- bandeiras ----------
    def _iso_for(self, team):
        return FLAG_ISO.get((team or {}).get("tla"))

    def get_flag(self, iso):
        """Retorna PhotoImage da bandeira (do cache em memoria/disco) ou None."""
        if not iso:
            return None
        if iso in self.flag_imgs:
            return self.flag_imgs[iso]
        path = os.path.join(FLAGS_DIR, iso + ".png")
        if os.path.exists(path):
            try:
                im = Image.open(path).convert("RGBA")
                w = max(1, int(im.width * FLAG_H / im.height))
                im = im.resize((w, FLAG_H), Image.LANCZOS)
                ph = ImageTk.PhotoImage(im)
                self.flag_imgs[iso] = ph
                return ph
            except Exception:
                return None
        return None

    def _prefetch_flags(self):
        """Baixa em background as bandeiras que faltam e re-renderiza ao terminar."""
        needed = set()
        for m in self.matches:
            for side in ("homeTeam", "awayTeam"):
                iso = self._iso_for(m.get(side, {}))
                if iso:
                    needed.add(iso)
        for s in self.standings:
            for r in s.get("table", []):
                iso = self._iso_for(r.get("team", {}))
                if iso:
                    needed.add(iso)
        missing = [i for i in needed
                   if not os.path.exists(os.path.join(FLAGS_DIR, i + ".png"))]
        if not missing:
            return

        def worker():
            ok = 0
            for iso in missing:
                url = f"https://flagcdn.com/h40/{iso}.png"
                try:
                    with urlopen(url, timeout=15) as r:
                        data = r.read()
                    with open(os.path.join(FLAGS_DIR, iso + ".png"), "wb") as f:
                        f.write(data)
                    ok += 1
                except Exception:
                    pass
            if ok:
                self.root.after(0, self._render_all)
        threading.Thread(target=worker, daemon=True).start()

    # ---------- dados ----------
    def _schedule_refresh(self):
        base = int(self.cfg.get("refresh_seconds", 60))
        secs = min(base, 30) if self._has_live else base  # mais rápido se há jogo
        self.root.after(secs * 1000, self._tick)

    def _tick(self):
        self.refresh_async()
        self._schedule_refresh()

    def refresh_async(self):
        token = self.cfg.get("token")
        if not token:
            self.status.config(text="Configure sua API key (⚙).", fg=LIVE)
            return
        self.status.config(text="Atualizando...", fg=MUTED)
        threading.Thread(target=self._fetch, args=(token,), daemon=True).start()

    def _fetch(self, token):
        comp = self.cfg.get("competition", "WC")
        matches, err1 = api_get(f"/competitions/{comp}/matches", token)
        standings, err2 = api_get(f"/competitions/{comp}/standings", token)
        data = {
            "matches": (matches or {}).get("matches", []) if matches else [],
            "standings": (standings or {}).get("standings", []) if standings else [],
            "error": err1 or err2,
        }
        self.root.after(0, lambda: self._apply(data))

    def _apply(self, data):
        if data["error"] and not data["matches"]:
            self.status.config(text="⚠ " + data["error"], fg=LIVE)
            return
        self.matches = data["matches"]
        self.standings = data["standings"]
        self.last_update = dt.datetime.now()
        live_n = sum(1 for m in self.matches if m.get("status") in LIVE_STATUSES)
        txt = f"Atualizado {self.last_update:%H:%M:%S}  ·  {live_n} ao vivo"
        if data["error"]:
            txt += "  ·  (classificação indisponível)"
        self._has_live = live_n > 0
        self.status.config(text=txt, fg=ACCENT if live_n else MUTED)
        self._process_live()
        self._update_tray_title()
        self._prefetch_flags()
        self._render_all()

    # ---------- tooltip da bandeja com placar ----------
    def _abbr(self, team):
        return (team.get("tla") or (team.get("shortName") or team.get("name") or "?")
                )[:3].upper()

    def _tray_title(self):
        def fmt(m):
            ht, at = m.get("homeTeam", {}), m.get("awayTeam", {})
            sc = m.get("score", {}).get("fullTime", {})
            h = sc.get("home")
            a = sc.get("away")
            h = "-" if h is None else h
            a = "-" if a is None else a
            minute = m.get("minute")
            if minute:
                tail = f" {minute}'"
            elif m.get("status") == "PAUSED":
                tail = " Int"
            else:
                tail = ""
            return f"{self._abbr(ht)} {h}x{a} {self._abbr(at)}{tail}"

        live = [m for m in self.matches if m.get("status") in LIVE_STATUSES]
        if live:
            fav = [m for m in live if self._is_fav(m.get("homeTeam", {}))
                   or self._is_fav(m.get("awayTeam", {}))]
            chosen = fav[0] if fav else live[0]
            base = fmt(chosen)
            if len(live) > 1:
                base += f"  (+{len(live) - 1} ao vivo)"
            return base

        # sem jogo ao vivo: mostra o próximo do time favorito
        now = dt.datetime.now().astimezone()
        upcoming = []
        for m in self.matches:
            if m.get("status") in ("TIMED", "SCHEDULED"):
                local = parse_utc(m.get("utcDate", ""))
                if (local and local >= now
                        and (self._is_fav(m.get("homeTeam", {}))
                             or self._is_fav(m.get("awayTeam", {})))):
                    upcoming.append((local, m))
        if upcoming:
            upcoming.sort(key=lambda x: x[0])
            local, m = upcoming[0]
            return (f"Copa · {self._abbr(m.get('homeTeam', {}))}x"
                    f"{self._abbr(m.get('awayTeam', {}))} {local:%d/%m %H:%M}")
        return "Copa Widget"

    def _update_tray_title(self):
        try:
            self.icon.title = self._tray_title()
        except Exception:
            pass

    # ---------- timeline de lances + alertas ----------
    def _process_live(self):
        alerts = self.cfg.get("alerts", True)
        new_prev = {}
        for m in self.matches:
            mid = m.get("id")
            st = m.get("status")
            ht, at = m.get("homeTeam", {}), m.get("awayTeam", {})
            sc = m.get("score", {}).get("fullTime", {})
            h, a = sc.get("home"), sc.get("away")
            minute = m.get("minute")
            new_prev[mid] = {"status": st, "h": h, "a": a}
            if self._first_apply:
                continue
            prev = self.prev_match.get(mid)

            # B) fonte externa (API-Football) tem prioridade quando configurada
            ext = self._external_events(m)
            if ext is not None:
                self.events[mid] = ext

            if prev is None:
                continue
            evs = self.events.setdefault(mid, []) if ext is None else None

            def add(icon, text, key):
                if evs is None:
                    return
                if any(e.get("key") == key for e in evs):
                    return
                evs.append({"min": minute, "icon": icon, "text": text, "key": key})

            # A) timeline derivada das mudancas de estado/placar
            if st in LIVE_STATUSES and prev["status"] not in LIVE_STATUSES:
                add("🟢", "Bola rolando!", f"ko-{st}")
                if alerts and (self._is_fav(ht) or self._is_fav(at)):
                    self._alert("kickoff",
                                ht.get("name") if self._is_fav(ht) else at.get("name"))
            if h is not None and prev["h"] is not None and h > prev["h"]:
                add("⚽", f"GOL! {ht.get('name')}  ({h}-{a})", f"gh-{h}")
                if alerts and self._is_fav(ht):
                    self._alert("goal", ht.get("name"))
            if a is not None and prev["a"] is not None and a > prev["a"]:
                add("⚽", f"GOL! {at.get('name')}  ({h}-{a})", f"ga-{a}")
                if alerts and self._is_fav(at):
                    self._alert("goal", at.get("name"))
            if st == "PAUSED" and prev["status"] != "PAUSED":
                add("⏸", f"Intervalo  ({h}-{a})", "ht")
            if st == "IN_PLAY" and prev["status"] == "PAUSED":
                add("▶", "Começou o 2º tempo", "2h")
            if st == "FINISHED" and prev["status"] != "FINISHED":
                add("🏁", f"Fim de jogo  ({h}-{a})", "ft")
        self.prev_match = new_prev
        self._first_apply = False

    # ---------- B) integração API-Football (ativa quando houver key) ----------
    def _apifb_get(self, path, key):
        req = Request("https://v3.football.api-sports.io" + path,
                      headers={"x-apisports-key": key})
        with urlopen(req, timeout=15) as r:
            return json.loads(r.read().decode("utf-8"))

    def _external_events(self, m):
        """Retorna lista de eventos reais (gol c/ autor, cartão, subst) ou None.
        Ativa apenas se 'apifootball_key' estiver preenchida nas configurações."""
        key = self.cfg.get("apifootball_key")
        if not key:
            return None
        mid = m.get("id")
        try:
            fid = self._apifb_fixture.get(mid)
            if fid is None:  # descobre o fixture id 1x e guarda em cache
                local = parse_utc(m.get("utcDate", "")) or dt.datetime.now()
                data = self._apifb_get(f"/fixtures?date={local:%Y-%m-%d}", key)
                fid = self._apifb_find_fixture(data, m) or 0
                self._apifb_fixture[mid] = fid
            if not fid:
                return None
            data = self._apifb_get(f"/fixtures/events?fixture={fid}", key)
            return self._apifb_parse(data)
        except Exception:
            return None

    def _apifb_find_fixture(self, data, m):
        htn = (m.get("homeTeam", {}).get("name") or "").lower()
        for fx in (data or {}).get("response", []):
            home = (fx.get("teams", {}).get("home", {}).get("name") or "").lower()
            if htn and (htn in home or home in htn):
                return fx.get("fixture", {}).get("id")
        return None

    def _apifb_parse(self, data):
        out = []
        for ev in (data or {}).get("response", []):
            minute = (ev.get("time") or {}).get("elapsed")
            typ = (ev.get("type") or "").lower()
            detail = ev.get("detail") or ""
            player = (ev.get("player") or {}).get("name") or ""
            team = (ev.get("team") or {}).get("name") or ""
            if typ == "goal":
                icon, text = "⚽", f"GOL! {team} — {player}"
            elif typ == "card":
                icon = "🟨" if "yellow" in detail.lower() else "🟥"
                text = f"{detail} — {player} ({team})"
            elif typ == "subst":
                icon, text = "🔁", f"Substituição — {player} ({team})"
            else:
                icon, text = "•", f"{detail} {player}".strip()
            out.append({"min": minute, "icon": icon, "text": text,
                        "key": f"{minute}-{typ}-{player}"})
        return out

    def _play(self, kind):
        if not winsound or not self.cfg.get("sound", True):
            return

        def run():
            try:
                seq = ((660, 150), (880, 150), (990, 180), (1320, 280)) if kind == "goal" \
                    else ((523, 150), (659, 150), (784, 220))
                for freq, dur in seq:
                    winsound.Beep(freq, dur)
            except Exception:
                pass
        threading.Thread(target=run, daemon=True).start()

    def _alert(self, kind, team):
        team = team or "Seu time"
        if kind == "goal":
            title, msg = "⚽ GOOOL!", f"Gol do {team}!"
        else:
            title, msg = "🟢 Bola rolando!", f"{team} entrou em campo!"
        self._play(kind)
        try:
            self.icon.notify(msg, title)
        except Exception:
            pass
        self.show_window()
        # realce: pisca a janela rapidamente
        self._flash(title)

    def _flash(self, title, n=6):
        cur = self.root.title()
        def step(i):
            self.root.title(title if i % 2 else "Copa Widget")
            if i < n:
                self.root.after(400, lambda: step(i + 1))
            else:
                self.root.title(cur)
        step(0)

    def _render_all(self):
        self._render_live()
        self._render_today()
        self._render_table()

    # ---------- render ----------
    def _clear(self, frame):
        for w in frame.winfo_children():
            w.destroy()

    def _bind_click(self, widget, match):
        widget.configure(cursor="hand2")
        widget.bind("<Button-1>", lambda e, mm=match: self.open_detail(mm))
        for ch in widget.winfo_children():
            self._bind_click(ch, match)

    def _match_card(self, parent, m, show_time=True):
        status = m.get("status")
        is_live = status in LIVE_STATUSES
        ht, at = m.get("homeTeam", {}), m.get("awayTeam", {})
        fav = self._is_fav(ht) or self._is_fav(at)
        bg = "#2a2410" if fav else CARD
        card = tk.Frame(parent, bg=bg)
        card.pack(fill="x", padx=8, pady=3)

        if is_live:
            minute = m.get("minute")
            label = f"● {minute}'" if minute else "● AO VIVO"
            if status == "PAUSED":
                label = "● Intervalo"
            stcolor = LIVE
        elif status == "FINISHED":
            label, stcolor = "Encerrado", MUTED
        elif status in ("TIMED", "SCHEDULED"):
            local = parse_utc(m.get("utcDate", ""))
            label = local.strftime("%d/%m %H:%M") if (local and show_time) else "Agendado"
            stcolor = HEADER
        else:
            label, stcolor = status or "", MUTED
        grp = (m.get("group") or m.get("stage") or "")
        grp = grp.replace("_", " ").title() if grp else ""

        head = tk.Frame(card, bg=bg)
        head.pack(fill="x", padx=10, pady=(6, 0))
        tk.Label(head, text=label, bg=bg, fg=stcolor,
                 font=("Segoe UI", 8, "bold")).pack(side="left")
        tk.Label(head, text="ver elenco ›", bg=bg, fg=MUTED,
                 font=("Segoe UI", 8)).pack(side="right")
        if grp:
            tk.Label(head, text=grp + "   ", bg=bg, fg=MUTED,
                     font=("Segoe UI", 8)).pack(side="right")

        sc = m.get("score", {}).get("fullTime", {})
        hs, as_ = sc.get("home"), sc.get("away")
        score_txt = f"{hs} × {as_}" if hs is not None and as_ is not None else "– × –"

        row = tk.Frame(card, bg=bg)
        row.pack(fill="x", padx=10, pady=(2, 8))
        row.columnconfigure(0, weight=1)
        row.columnconfigure(4, weight=1)
        # nome casa (col0, alinhado a direita) | bandeira (col1) | placar (col2)
        tk.Label(row, text=ht.get("name") or "?", bg=bg,
                 fg=FAV if self._is_fav(ht) else FG, anchor="e",
                 font=("Segoe UI", 10, "bold" if self._is_fav(ht) else "normal")
                 ).grid(row=0, column=0, sticky="e", padx=(0, 4))
        fh = self.get_flag(self._iso_for(ht))
        lbl_fh = tk.Label(row, image=fh, bg=bg)
        lbl_fh.image = fh
        lbl_fh.grid(row=0, column=1)
        tk.Label(row, text=score_txt, bg=bg, fg=FG,
                 font=("Segoe UI", 12, "bold"), width=7).grid(row=0, column=2)
        fa = self.get_flag(self._iso_for(at))
        lbl_fa = tk.Label(row, image=fa, bg=bg)
        lbl_fa.image = fa
        lbl_fa.grid(row=0, column=3)
        tk.Label(row, text=at.get("name") or "?", bg=bg,
                 fg=FAV if self._is_fav(at) else FG, anchor="w",
                 font=("Segoe UI", 10, "bold" if self._is_fav(at) else "normal")
                 ).grid(row=0, column=4, sticky="w", padx=(4, 0))

        self._bind_click(card, m)

    def _empty(self, frame, text):
        tk.Label(frame, text=text, bg=BG, fg=MUTED,
                 font=("Segoe UI", 10), pady=30).pack(fill="x")

    def _render_live(self):
        self._clear(self.live_inner)
        live = [m for m in self.matches if m.get("status") in LIVE_STATUSES]
        live.sort(key=lambda m: m.get("utcDate", ""))
        if not live:
            self._empty(self.live_inner, "Nenhum jogo ao vivo agora.")
            return
        for m in live:
            self._match_card(self.live_inner, m)
            self._render_feed(self.live_inner, m.get("id"))

    def _render_feed(self, parent, mid):
        evs = self.events.get(mid)
        if not evs:
            return
        box = tk.Frame(parent, bg=BG)
        box.pack(fill="x", padx=16, pady=(0, 8))
        tk.Label(box, text="Lances", bg=BG, fg=MUTED, anchor="w",
                 font=("Segoe UI", 8, "bold")).pack(fill="x")
        for e in evs[-12:]:
            ln = tk.Frame(box, bg=BG)
            ln.pack(fill="x")
            mn = f"{e['min']}'" if e.get("min") is not None else ""
            tk.Label(ln, text=mn, bg=BG, fg=ACCENT, width=4, anchor="e",
                     font=("Segoe UI", 8, "bold")).pack(side="left")
            tk.Label(ln, text=f"  {e['icon']} {e['text']}", bg=BG, fg=FG, anchor="w",
                     font=("Segoe UI", 9)).pack(side="left", fill="x", expand=True)

    def _render_today(self):
        self._clear(self.today_inner)
        today = dt.date.today()
        items = []
        for m in self.matches:
            local = parse_utc(m.get("utcDate", ""))
            if local and local.date() == today:
                items.append((local, m))
        items.sort(key=lambda x: x[0])
        if not items:
            self._empty(self.today_inner, "Nenhum jogo hoje.")
            return
        for _, m in items:
            self._match_card(self.today_inner, m)

    def _render_table(self):
        for i in self.tree.get_children():
            self.tree.delete(i)
        totals = [s for s in self.standings if s.get("type") == "TOTAL"] or self.standings
        if not totals:
            self.tree.insert("", "end", text="  Classificação indisponível",
                             tags=("group",))
            return
        for s in totals:
            grp = (s.get("group") or "Tabela").replace("_", " ").title()
            node = self.tree.insert("", "end", text=grp, open=True, tags=("group",))
            for r in s.get("table", []):
                team = r.get("team", {})
                name = team.get("name") or team.get("tla") or "?"
                pos = r.get("position", "")
                vals = (r.get("playedGames", 0), r.get("won", 0), r.get("draw", 0),
                        r.get("lost", 0), r.get("goalDifference", 0), r.get("points", 0))
                tags = ("fav",) if self._is_fav(team) else ()
                flag = self.get_flag(self._iso_for(team))
                kw = {"image": flag} if flag else {}
                self.tree.insert(node, "end", text=f" {pos}. {name}",
                                 values=vals, tags=tags, **kw)

    # ---------- detalhe do jogo (jogadores + posicao + campo) ----------
    def open_detail(self, m):
        win = tk.Toplevel(self.root)
        ht, at = m.get("homeTeam", {}), m.get("awayTeam", {})
        win.title(f"{ht.get('name','?')} x {at.get('name','?')}")
        win.configure(bg=BG)
        win.geometry("680x640")
        win.transient(self.root)

        hdr = tk.Frame(win, bg=BG)
        hdr.pack(fill="x", padx=12, pady=(10, 4))
        self._team_badge(hdr, ht, "left")
        tk.Label(hdr, text="x", bg=BG, fg=MUTED,
                 font=("Segoe UI", 12, "bold")).pack(side="left", expand=True)
        self._team_badge(hdr, at, "right")

        # alternancia Campo / Lista
        toggle = tk.Frame(win, bg=BG)
        toggle.pack(padx=12)
        state = {"data": None, "mode": "campo"}
        btns = {}

        info = tk.Label(win, text="Carregando jogadores...", bg=BG, fg=MUTED,
                        font=("Segoe UI", 8))
        info.pack(fill="x", padx=12, pady=(2, 0))

        body = tk.Frame(win, bg=BG)
        body.pack(fill="both", expand=True, padx=8, pady=6)

        def render():
            for w in body.winfo_children():
                w.destroy()
            data = state["data"]
            if not data:
                tk.Label(body, text="Carregando...", bg=BG, fg=MUTED,
                         font=("Segoe UI", 10), pady=30).pack()
                return
            left = tk.Frame(body, bg=BG)
            left.pack(side="left", fill="both", expand=True, padx=(0, 4))
            right = tk.Frame(body, bg=BG)
            right.pack(side="left", fill="both", expand=True, padx=(4, 0))
            if state["mode"] == "campo":
                self._build_pitch(left, data["home"])
                self._build_pitch(right, data["away"])
            else:
                self._fill_detail(self._make_scroll(left),
                                  data["home"]["team"], data["home"]["players"])
                self._fill_detail(self._make_scroll(right),
                                  data["away"]["team"], data["away"]["players"])

        def set_mode(mode):
            state["mode"] = mode
            for k, b in btns.items():
                on = (k == mode)
                b.config(bg=ACCENT if on else CARD, fg="#06210d" if on else FG)
            render()

        for key, lbl in (("campo", "Campo ⚽"), ("lista", "Lista")):
            b = tk.Button(toggle, text=lbl, bd=0, cursor="hand2", width=10,
                          font=("Segoe UI", 9, "bold"),
                          command=lambda k=key: set_mode(k))
            b.pack(side="left", padx=3, pady=4, ipady=2)
            btns[key] = b
        set_mode("campo")

        def done(data):
            state["data"] = data
            note = ("Escalação oficial do jogo." if data["source"] == "escalação"
                    else "Pré-Copa: escalação ainda não disponível — "
                         "mostrando o elenco (formação é uma prévia).")
            info.config(text=note)
            render()

        threading.Thread(target=lambda: self._load_detail(m, done),
                         daemon=True).start()

    def _team_badge(self, parent, team, side):
        fr = tk.Frame(parent, bg=BG)
        fr.pack(side=side)
        flag = self.get_flag(self._iso_for(team))
        if flag:
            lb = tk.Label(fr, image=flag, bg=BG)
            lb.image = flag
            lb.pack(side="left", padx=(0, 6))
        tk.Label(fr, text=team.get("name") or "?", bg=BG,
                 fg=FAV if self._is_fav(team) else FG,
                 font=("Segoe UI", 12, "bold")).pack(side="left")

    def _load_detail(self, m, done):
        token = self.cfg.get("token")
        mid = m.get("id")
        ht, at = m.get("homeTeam", {}), m.get("awayTeam", {})
        detail, _ = api_get(f"/matches/{mid}", token) if mid else (None, None)
        source = "elenco"
        h_line = a_line = h_form = a_form = None
        if detail:
            dh = (detail.get("homeTeam") or {})
            da = (detail.get("awayTeam") or {})
            if (dh.get("lineup") or da.get("lineup")):
                h_line, a_line = dh.get("lineup") or [], da.get("lineup") or []
                h_form, a_form = dh.get("formation"), da.get("formation")
                source = "escalação"
        if source == "escalação":
            home = {"team": ht, "players": h_line, "formation": h_form, "lineup": True}
            away = {"team": at, "players": a_line, "formation": a_form, "lineup": True}
        else:
            home = {"team": ht, "players": self._squad(ht.get("id"), token),
                    "formation": "4-3-3", "lineup": False}
            away = {"team": at, "players": self._squad(at.get("id"), token),
                    "formation": "4-3-3", "lineup": False}
        self.root.after(0, lambda: done({"home": home, "away": away, "source": source}))

    # ---------- desenho do campo ----------
    def _xi_lines(self, side):
        """Retorna lista de linhas (GK -> ataque), cada uma com jogadores."""
        players = side["players"] or []
        nums = lines_counts(side["formation"])
        if side["lineup"]:
            counts, lines, idx = [1] + nums, [], 0
            for c in counts:
                lines.append(players[idx:idx + c])
                idx += c
            return lines
        # previa a partir do elenco: agrupa por balde de posicao
        by = {0: [], 1: [], 2: [], 3: [], 4: []}
        for p in players:
            by[bucket(p.get("position"))[0]].append(p)
        pool = by[1] + by[2] + by[3] + by[4]
        lines, idx = [by[0][:1]], 0
        for c in nums:
            lines.append(pool[idx:idx + c])
            idx += c
        return lines

    def _build_pitch(self, parent, side):
        team = side["team"]
        W, H, pad = 312, 392, 10
        cv = tk.Canvas(parent, width=W, height=H, bg="#1f7a3a",
                       highlightthickness=0)
        cv.pack(fill="both", expand=True)
        line = "#bfe6c9"
        cv.create_rectangle(pad, pad, W - pad, H - pad, outline=line, width=2)
        cv.create_line(pad, H / 2, W - pad, H / 2, fill=line)
        cv.create_oval(W / 2 - 34, H / 2 - 34, W / 2 + 34, H / 2 + 34, outline=line)
        cv.create_oval(W / 2 - 3, H / 2 - 3, W / 2 + 3, H / 2 + 3, fill=line, outline=line)
        cv.create_rectangle(W / 2 - 58, pad, W / 2 + 58, pad + 46, outline=line)
        cv.create_rectangle(W / 2 - 58, H - pad - 46, W / 2 + 58, H - pad, outline=line)

        lines = self._xi_lines(side)
        fav = self._is_fav(team)
        n = len(lines)
        top_y, bot_y = 46, H - 42
        for li, row in enumerate(lines):
            y = bot_y if n <= 1 else bot_y - li * (bot_y - top_y) / (n - 1)
            mlen = len(row)
            for j, p in enumerate(row):
                x = W * (j + 1) / (mlen + 1)
                self._draw_player(cv, x, y, p, fav)

        form = "-".join(str(c) for c in lines_counts(side["formation"]))
        tag = form + ("" if side["lineup"] else "  (prévia)")
        cv.create_text(W / 2, H - 12, text=tag, fill=line,
                       font=("Segoe UI", 8, "bold"))

    def _draw_player(self, cv, x, y, p, fav):
        r = 13
        fill = FAV if fav else "#ffffff"
        cv.create_oval(x - r, y - r, x + r, y + r, fill=fill, outline="#0b3d1c", width=2)
        num = p.get("shirtNumber")
        if num is not None:
            cv.create_text(x, y, text=str(num), fill="#0f1419",
                           font=("Segoe UI", 8, "bold"))
        cv.create_text(x, y + r + 8, text=short_name(p.get("name")),
                       fill="#ffffff", font=("Segoe UI", 7))

    def _squad(self, team_id, token):
        if not team_id:
            return []
        if team_id in self.squad_cache:
            return self.squad_cache[team_id]
        data, _ = api_get(f"/teams/{team_id}", token)
        squad = (data or {}).get("squad", []) if data else []
        self.squad_cache[team_id] = squad
        return squad

    def _fill_detail(self, frame, team, players):
        self._clear(frame)
        if not players:
            tk.Label(frame, text="Sem dados de jogadores.", bg=BG, fg=MUTED,
                     font=("Segoe UI", 9), pady=14).pack()
            return
        # agrupa por balde de posicao
        groups = {}
        for p in players:
            order, name = bucket(p.get("position"))
            groups.setdefault((order, name), []).append(p)
        for (order, gname) in sorted(groups):
            tk.Label(frame, text=gname.upper(), bg=BG, fg=HEADER, anchor="w",
                     font=("Segoe UI", 9, "bold")).pack(fill="x", padx=8, pady=(8, 2))
            for p in groups[(order, gname)]:
                rowf = tk.Frame(frame, bg=CARD)
                rowf.pack(fill="x", padx=8, pady=1)
                num = p.get("shirtNumber")
                numtxt = f"{num:>2}" if num is not None else "  "
                tk.Label(rowf, text=numtxt, bg=CARD, fg=ACCENT, width=3,
                         font=("Consolas", 9, "bold")).pack(side="left", padx=(6, 4))
                tk.Label(rowf, text=p.get("name") or "?", bg=CARD, fg=FG, anchor="w",
                         font=("Segoe UI", 9)).pack(side="left", fill="x", expand=True)
                pos = p.get("position") or ""
                tk.Label(rowf, text=POS_PT.get(pos, pos), bg=CARD, fg=MUTED,
                         font=("Segoe UI", 8)).pack(side="right", padx=6)

    def run(self):
        self.root.mainloop()


if __name__ == "__main__":
    CopaWidget().run()
