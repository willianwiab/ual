#!/usr/bin/env python3
"""Coletor do Ual: lê feeds RSS, tira política e notícia ruim, separa por editoria,
acha a foto de cada matéria e grava news.json. Só biblioteca padrão."""
import concurrent.futures as cf
import email.utils
import gzip
import hashlib
import html
import json
import re
import time
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timezone
from pathlib import Path

RAIZ = Path(__file__).resolve().parent.parent
SAIDA = RAIZ / "news.json"
UA = "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130 Safari/537.36"
DIAS = 4          # quanto tempo uma notícia fica na capa
MAX_POR_CAT = 40
MAX_CAT = {"cinema": 80, "ccxp": 60}
DIAS_CAT = {"ccxp": 21}  # notícia de CCXP fica mais tempo: a aba do evento junta tudo até dezembro

# (url, nome da fonte, editoria padrão). None = decide pelas palavras do título.
FEEDS = [
    ("https://ge.globo.com/rss/ge/futebol/times/corinthians/", "ge", "corinthians"),
    ("https://www.meutimao.com.br/rss", "Meu Timão", "corinthians"),
    ("https://ge.globo.com/rss/ge/", "ge", "esportes"),
    ("https://rss.uol.com.br/feed/esporte.xml", "UOL", "esportes"),
    ("https://agenciabrasil.ebc.com.br/rss/esportes/feed.xml", "Agência Brasil", "esportes"),
    ("https://agenciabrasil.ebc.com.br/rss/saude/feed.xml", "Agência Brasil", "saude"),
    ("https://saude.abril.com.br/feed/", "Veja Saúde", "saude"),
    ("https://drauziovarella.uol.com.br/feed/", "Drauzio Varella", "saude"),
    ("https://olhardigital.com.br/medicina-e-saude/feed/", "Olhar Digital", "saude"),
    ("https://olhardigital.com.br/ciencia-e-espaco/feed/", "Olhar Digital", "ciencia"),
    ("https://super.abril.com.br/feed/", "Superinteressante", "ciencia"),
    ("https://br.ign.com/feed.xml", "IGN Brasil", "games"),
    ("https://g1.globo.com/rss/g1/tecnologia/", "g1", "tecnologia"),
    ("https://rss.uol.com.br/feed/tecnologia.xml", "UOL", "tecnologia"),
    ("https://olhardigital.com.br/feed/", "Olhar Digital", "tecnologia"),
    ("https://tecnoblog.net/feed/", "Tecnoblog", "tecnologia"),
    ("https://canaltech.com.br/rss/", "Canaltech", "tecnologia"),
    ("https://g1.globo.com/rss/g1/pop-arte/cinema/", "g1", "cinema"),
    ("https://g1.globo.com/rss/g1/pop-arte/", "g1", "pop"),
    ("https://cinepop.com.br/feed/", "Cinepop", "cinema"),
    ("https://pipocamoderna.com.br/feed/", "Pipoca Moderna", "cinema"),
    ("https://cinemacomrapadura.com.br/feed/", "Cinema com Rapadura", "cinema"),
    ("https://observatoriodocinema.com.br/feed/", "Observatório do Cinema", "cinema"),
    ("https://filmeb.com.br/rss.xml", "Filme B", "cinema"),
    ("https://www.metsul.com/feed/", "MetSul", "clima"),
    ("https://castnews.com.br/feed/", "Castnews", "podcasts"),
    ("https://news.google.com/rss/search?q=CCXP+when:7d&hl=pt-BR&gl=BR&ceid=BR:pt-419", "Google Notícias", "evento"),
    # Google Notícias: só entra o que citar um evento da lista EVENTOS
    ("https://news.google.com/rss/search?q=CCXP+OR+%22Brasil+Game+Show%22+OR+%22Game+XP%22+OR+%22Anime+Friends%22+OR+%22Bienal+do+Livro%22+OR+Lollapalooza+OR+%22Rock+in+Rio%22+OR+%22The+Town%22+OR+%22The+Game+Awards%22+when:3d&hl=pt-BR&gl=BR&ceid=BR:pt-419", "Google Notícias", "evento"),
    ("https://agenciabrasil.ebc.com.br/rss/geral/feed.xml", "Agência Brasil", None),
    ("https://www.bbc.com/portuguese/index.xml", "BBC Brasil", None),
    ("https://g1.globo.com/rss/g1/", "g1", None),
]

# Palavras inteiras (sem diferenciar maiúsculas). Termine com * para valer como prefixo: "deputad*".
POLITICA = ["lula", "bolsonaro", "bolsonarista*", "bolsonaris*", "lulis*", "petis*", "trump", "stf", "congresso", "senado", "senador*",
            "câmara dos deputados", "deputad*", "ministro", "ministra", "eleiç*", "eleitora*", "eleitor*",
            "partido*", "pt", "pl", "psdb", "governo federal", "planalto", "presidente da república",
            "impeachment", "cpi", "tarcísio", "haddad", "moraes", "alckmin", "nikolas", "prefeit*", "governador*",
            "vereador*", "itamaraty", "oposição", "polític*", "golpe", "anistia", "tse", "stj", "pec",
            "reforma tributária", "tarifaço", "putin", "netanyahu", "milei", "maduro", "casa branca", "kremlin",
            "guerra*", "hamas", "gaza", "ucrânia", "israel", "irã", "ataque*", "sanç*", "otan", "pf",
            "polícia federal", "ministério", "sarney", "dilma", "temer", "ciro gomes", "marina silva"]
# notícia ruim que não é obituário nem clima
RUIM = ["assassin*", "homicídio*", "estupr*", "tiroteio*", "baleado*", "a tiros", "chacina*", "esfaque*",
        "sequestr*", "assalt*", "roub*", "furt*", "tráfico", "facç*", "pres[oa]s?", "prisão", "polícia*",
        "policia*", "feminicídio*", "violênci*", "abus*", "golpista*", "fraude*", "corrupç*", "investiga*",
        "denúncia*", "denunci*", "acident*", "atropel*", "suicíd*", "brig*", "agress*", "racis*", "injúria*",
        "encontrad[oa]s? mort[oa]s?", "dívida*", "penhor*", "despejad*", "mort[oa] em casa", "bets?", "apostas?", "process[oa]*", "condenad*", "justiça", "bbb", "a fazenda", "fofoca*", "traição", "trai", "luto", "pena de morte",
        # propaganda disfarçada de notícia
        "descontos?", "ofertas?", "menor preço", "promoç*", "cupo*", "black friday", "mercado livre", "amazon",
        "preço arrasador", "somente hoje", "imperdível"]
OBITO = ["morre", "morreu", "morte de", "falece*", "faleceu", "velório", "enterro", "sepultad*",
         "adeus a", "despede-se de"]
CLIMA = ["chuvas?", "chuvos[oa]", "temporal", "temporais", "calor", "frio", "previsão do tempo", "frentes? frias?",
         "granizo", "ciclone*", "tempestade*", "massa de ar", "inmet", "climatempo", "el niño", "la niña",
         "temperatura*", "geada*", "neve", "seca", "estiagem", "umidade"]
IA = ["inteligência artificial", "ia", "ias", "chatgpt", "openai", "gpt*", "claude", "anthropic", "gemini",
      "copilot", "llm*", "deepseek", "grok", "midjourney", "sora"]
GAMES = ["games?", "gamers?", "videogames?", "playstation", "ps5", "ps6", "xbox", "nintendo", "switch 2", "steam",
         "gta*", "minecraft", "fortnite", "roblox", "pokémon", "pokemon", "e-sports", "esports", "jogos grátis",
         "consoles?", "master system", "mega drive", "zelda", "mario"]
ESPORTE = ["onde assistir", "futebol", "campeonato", "brasileirão", "libertadores", "escalaç*", "partidas?"]
CIENCIA = ["nasa", "espaço", "espacia*", "astronom*", "planetas?", "galáxias?", "estrelas?", "cometas?",
           "asteroides?", "lua", "marte", "telescópio*", "cientistas?", "pesquisadores", "descoberta*",
           "fóssei?s?", "fóssil", "dinossauro*", "arqueolog*", "física", "universo", "eclipse*", "meteor*", "foguete*"]
SAUDE = ["saúde", "doenç*", "vacin*", "câncer", "médic*", "hospita*", "sus", "dieta*", "sono", "exercício*",
         "coração", "diabetes", "alzheimer", "tratamento*", "remédio*", "anvisa", "pacientes?", "nutri*",
         "obesidade"]
POP = ["podcasts?", "videocasts?", "ccxp", "netflix", "séries?", "filmes?", "cinema", "shows?", "turnê",
       "álbum", "festival", "marvel", "star wars", "animes?", "streaming", "disney", "hbo", "oscar", "grammy"]
CINEMA = ["filmes?", "cinemas?", "cinematográfic*", "estreia*", "estrei[ao]u?", "bilheteria*", "trailer*",
          "hollywood", "diretor*", "diretora*", "longa-metragem", "oscar", "festival de cannes", "cannes",
          "veneza", "sundance", "marvel", "dc studios", "pixar", "sequência", "remake", "elenco",
          "atores", "ator", "atriz", "atrizes", "protagoniz*", "personagem", "bastidores", "pôster"]
# notícia "de gente": ator/atriz em destaque na página de Cinema
ATORES = ["atores", "ator", "atriz", "atrizes", "astro", "estrela de", "elenco", "escalad[oa]s?", "protagoniz*",
          "interpret*", "papel", "vive [a-z]", "viverá", "revela", "relembra", "desabafa", "diz que", "conta que",
          "entrevista", "carreira", "descarta retorno", "volta ao papel", "aniversário", "homenage*"]
SERIE = ["séries?", "temporadas?", "episódios?", "animes?", "minissérie", "novela", "reality", "netflix",
         "hbo max", "apple tv", "prime video", "disney\\+", "paramount\\+", "globoplay", "showrunner"]
EVENTOS = ["podcasts?", "videocasts?", "ccxp", "brasil game show", "bgs", "game xp", "anime friends", "comic[- ]con",
           "bienal do livro", "lollapalooza", "rock in rio", "the town", "primavera sound", "gamescom",
           "the game awards", "summer game fest", "tokyo game show", "campus party", "web summit", "sxsw"]
CORINTHIANS = ["corinthians", "timão", "neo química", "yuri alberto", "memphis"]

_RX = {}


def tem(texto, palavras):
    k = tuple(palavras)  # não usar id(): lista criada na hora pode reaproveitar o id de outra
    if k not in _RX:
        partes = [re.escape(p[:-1]).replace(r"\[", "[").replace(r"\]", "]") + r"\w*" if p.endswith("*")
                  else p for p in palavras]
        _RX[k] = re.compile(r"(?<![\wÀ-ÿ])(?:" + "|".join(partes) + r")(?![\wÀ-ÿ])", re.I)
    return bool(_RX[k].search(texto))


def classificar(titulo, desc, padrao):
    t = titulo + " " + desc[:200]
    if tem(titulo, POLITICA) or tem(desc[:300], POLITICA[:40]) or tem(titulo, RUIM):
        return None
    if tem(titulo, ["ccxp*", "spoiler night"]):
        return "ccxp"
    if tem(titulo, OBITO):
        return "obituario"
    if tem(titulo, CORINTHIANS):
        return "corinthians"
    if padrao == "corinthians":
        return "corinthians"
    if padrao == "podcasts":
        return "podcasts"
    if padrao == "evento":
        return "podcasts" if tem(titulo, EVENTOS) else None
    if padrao == "cinema":
        return "cinema"
    if padrao in ("pop", None) and tem(titulo, CINEMA):
        return "cinema"
    if padrao not in ("games", "esportes") and tem(titulo, EVENTOS):
        return "podcasts"
    if tem(titulo, IA):
        return "ia"
    if padrao in ("tecnologia", None) and tem(titulo, ESPORTE):
        return "esportes"
    if padrao in ("tecnologia", None) and tem(t, GAMES):
        return "games"
    if padrao == "clima" or tem(titulo, CLIMA):
        return "clima"
    if padrao in ("tecnologia", "ciencia", None) and tem(titulo, CIENCIA):
        return "ciencia"
    if padrao in ("tecnologia", "pop", None) and tem(titulo, POP):
        return "pop"
    if padrao is None:
        if tem(titulo, CORINTHIANS):
            return "corinthians"
        if tem(titulo, SAUDE):
            return "saude"
        return None  # geral sem editoria clara = fora
    if padrao == "saude" and tem(titulo, CIENCIA):
        return "ciencia"
    return padrao


def baixar(url, timeout=20):
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept-Encoding": "gzip", "Accept-Language": "pt-BR"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        dados = r.read()
        if r.headers.get("Content-Encoding") == "gzip" or dados[:2] == b"\x1f\x8b":
            dados = gzip.decompress(dados)
        return dados, r.headers.get_content_charset()


def texto_limpo(s):
    s = re.sub(r"<[^>]+>", " ", s or "")
    return re.sub(r"\s+", " ", html.unescape(s)).strip()


MESES = {"jan": "Jan", "fev": "Feb", "mar": "Mar", "abr": "Apr", "mai": "May", "jun": "Jun", "jul": "Jul",
         "ago": "Aug", "set": "Sep", "out": "Oct", "nov": "Nov", "dez": "Dec"}


def data_ts(s):
    if not s:
        return None
    s = s.strip()
    try:
        return int(email.utils.parsedate_to_datetime(s).timestamp() * 1000)
    except Exception:
        pass
    m = re.search(r"(\d{1,2}) (\w{3}) (\d{4}) (\d{2}:\d{2}(?::\d{2})?)\s*([+-]\d{4})?", s)
    if m:  # data em português (UOL)
        mes = MESES.get(m.group(2).lower()[:3], m.group(2))
        try:
            return int(email.utils.parsedate_to_datetime(
                f"{m.group(1)} {mes} {m.group(3)} {m.group(4)} {m.group(5) or '-0300'}").timestamp() * 1000)
        except Exception:
            return None
    try:
        return int(datetime.fromisoformat(s.replace("Z", "+00:00")).timestamp() * 1000)
    except Exception:
        return None


def foto_do_item(item_xml):
    for pad in [r'<media:content[^>]+url="([^"]+)"', r'<media:thumbnail[^>]+url="([^"]+)"',
                r'<enclosure[^>]+url="([^"]+)"[^>]*type="image', r'<enclosure[^>]+type="image[^"]*"[^>]+url="([^"]+)"',
                r'<img[^>]+src=["\']([^"\']+)["\']', r'&lt;img[^&]+src=&quot;([^&]+)&quot;']:
        m = re.search(pad, item_xml, re.I)
        if m and m.group(1).startswith("http") and not re.search(r"\.gif|pixel|tracker|feedburner", m.group(1), re.I):
            return html.unescape(m.group(1))
    return None


def ler_feed(url, fonte, padrao):
    try:
        dados, cs = baixar(url)
    except Exception as e:
        print(f"  ✗ {fonte} {url}: {e}")
        return []
    bruto = None
    for enc in [cs, "utf-8", "iso-8859-1"]:
        if not enc:
            continue
        try:
            bruto = dados.decode(enc)
            break
        except Exception:
            continue
    blocos = re.findall(r"<item[\s>].*?</item>", bruto, re.S) or re.findall(r"<entry[\s>].*?</entry>", bruto, re.S)
    out = []
    for b in blocos:
        def campo(tag):
            m = re.search(rf"<{tag}[^>]*>(.*?)</{tag}>", b, re.S)
            if not m:
                return ""
            v = m.group(1).strip()
            return v.replace("<![CDATA[", "").replace("]]>", "")
        titulo = texto_limpo(campo("title"))
        link = texto_limpo(campo("link"))
        if not link:
            m = re.search(r'<link[^>]+href="([^"]+)"', b)
            link = m.group(1) if m else ""
        desc_raw = campo("description") or campo("summary")
        sub = texto_limpo(campo("atom:subtitle"))
        desc = sub or texto_limpo(desc_raw)
        ts = data_ts(campo("pubDate") or campo("published") or campo("updated") or campo("dc:date"))
        if not ts:  # ge não manda data: usa a do endereço (/2026/10/31/); o coletor guarda a 1ª vez que viu
            m = re.search(r"/(20\d\d)/(\d\d)/(\d\d)/", link)
            if m and m.group(0) != time.strftime("/%Y/%m/%d/"):
                ts = int(datetime(int(m.group(1)), int(m.group(2)), int(m.group(3)), 15, tzinfo=timezone.utc).timestamp() * 1000)
        fonte_item = fonte
        if "news.google." in url:
            m = re.search(r"<source[^>]*>(.*?)</source>", b, re.S)
            fonte_item = texto_limpo(m.group(1)) if m else fonte
            titulo = re.sub(r"\s+-\s+[^-]+$", "", titulo)
            desc, desc_raw = "", ""
            if len(titulo.split()) < 5:  # páginas de artista da CCXP etc.
                continue
        if not titulo or not link.startswith("http") or re.search(r"globoesporte\.com\s*$", titulo):
            continue  # páginas de "ao vivo" do ge vêm sem foto e com título de sistema
        cat = classificar(titulo, desc, padrao)
        if not cat:
            continue
        foto = foto_do_item(b) or foto_do_item(html.unescape(desc_raw))
        out.append({"id": hashlib.md5(link.encode()).hexdigest()[:12], "t": titulo, "u": link,
                    "d": desc[:220], "ts": ts, "sem_data": not ts, "cat": cat, "src": fonte_item, "img": foto})
        # "Selma Blair quebra o silêncio…": título que abre com nome de gente também conta
        gente = re.match(r"^(?:[‘'\"][^’'\"]+[’'\"]: )?[A-ZÀ-Ý][a-zà-ÿ]+(?: (?:de |da |do )?[A-ZÀ-Ý][a-zà-ÿ]+){1,2} [a-zà-ÿ]{3,}", titulo)
        if cat in ("cinema", "obituario", "pop") and (tem(titulo, ATORES) or (cat == "cinema" and gente)):
            out[-1]["ator"] = 1
        if cat == "cinema" and tem(titulo, SERIE) and not tem(titulo, ["filmes?", "cinemas?", "bilheteria"]):
            out[-1]["serie"] = 1
    print(f"  ✓ {fonte:15} {len(out):3}/{len(blocos):3}  {url}")
    return out


def og_image(url):
    try:
        dados, cs = baixar(url, timeout=12)
        pg = dados[:400_000].decode(cs or "utf-8", "ignore")
    except Exception:
        return None
    for pad in [r'<meta[^>]+property=["\']og:image(?::secure_url)?["\'][^>]+content=["\']([^"\']+)',
                r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+property=["\']og:image',
                r'<meta[^>]+name=["\']twitter:image["\'][^>]+content=["\']([^"\']+)']:
        m = re.search(pad, pg, re.I)
        if m and m.group(1).startswith("http"):
            return html.unescape(m.group(1))
    return None


def ler_omelete_ccxp():
    """Página de CCXP do Omelete (não tem RSS): lista as matérias e lê foto/data de cada uma."""
    try:
        pg = baixar("https://www.omelete.com.br/ccxp")[0].decode("utf-8", "ignore")
    except Exception as e:
        print(f"  ✗ Omelete CCXP: {e}")
        return []
    urls = list(dict.fromkeys(re.findall(r'href="(/ccxp/[a-z0-9-]{15,})"', pg)))[:20]
    def le(u):
        try:
            a = baixar("https://www.omelete.com.br" + u, timeout=12)[0][:300_000].decode("utf-8", "ignore")
        except Exception:
            return None
        meta = lambda k: (re.search(rf'(?:property|name)="{k}" content="([^"]+)"', a) or [None, None])[1]
        titulo, quando = html.unescape(meta("og:title") or ""), meta("article:published_time")
        ts = data_ts(quando.replace(" ", "T", 1)) if quando else None
        if not titulo or not ts:
            return None
        link = "https://www.omelete.com.br" + u
        return {"id": hashlib.md5(link.encode()).hexdigest()[:12], "t": titulo, "u": link,
                "d": html.unescape(meta("og:description") or "")[:220], "ts": ts, "sem_data": False,
                "cat": "ccxp", "src": "Omelete", "img": meta("og:image")}
    with cf.ThreadPoolExecutor(8) as ex:
        out = [i for i in ex.map(le, urls) if i and classificar(i["t"], i["d"], "ccxp")]
    print(f"  ✓ {'Omelete CCXP':15} {len(out):3}/{len(urls):3}")
    return out


INGRESSO = "https://api-content.ingresso.com/v0"


def filme(f):
    """Resume um filme da Ingresso.com no que a página de Cinema usa."""
    imgs = {i.get("type"): i.get("url") for i in f.get("images") or []}
    trailer = next((t.get("url") for t in f.get("trailers") or [] if t.get("url")), None)
    pd = f.get("premiereDate") or {}
    return {"id": f.get("id"), "t": (f.get("title") or "").strip(), "orig": f.get("originalTitle"),
            "data": (pd.get("localDate") or "")[:10] or None, "gen": f.get("genres") or [],
            "poster": imgs.get("PosterPortrait"), "wide": imgs.get("PosterHorizontal") or f.get("imageFeatured"),
            "trailer": trailer, "sin": re.sub(r"\s+", " ", f.get("synopsis") or "").strip()[:400],
            "elenco": f.get("cast") or "", "dir": f.get("director") or "", "class": f.get("contentRating") or "",
            "min": f.get("duration") or "", "pais": f.get("countryOrigin") or "",
            "u": f.get("siteURL") or f"https://www.ingresso.com/filme/{f.get('urlKey')}",
            "salas": f.get("countIsPlaying") or 0, "pre": bool(f.get("inPreSale")), "prio": f.get("priority") or 0}


def coletar_cinema():
    """Estreias e filmes em cartaz em São Paulo (cidade 1) pela Ingresso.com."""
    nao_filme = re.compile(r"live viewing|world tour|\btour\b|ao vivo|concerto|show|ópera|ballet|balé", re.I)
    def lista(caminho):
        dados, _ = baixar(f"{INGRESSO}/{caminho}")
        return [filme(f) for f in json.loads(dados).get("items", [])
                if f.get("type", "Filme") == "Filme" and not nao_filme.search(f.get("title") or "")
                and not set(f.get("genres") or []) & {"Show", "Concerto"}]
    hoje = time.strftime("%Y-%m-%d")
    limite = time.strftime("%Y-%m-%d", time.localtime(time.time() + 120 * 86400))
    estreias = sorted((f for f in lista("templates/soon/1/partnership/home")
                       if f["data"] and hoje <= f["data"] <= limite and f["poster"]),
                      key=lambda f: (f["data"], -f["prio"]))
    cartaz = sorted((f for f in lista("events/city/1/partnership/home") if f["poster"] and f["salas"]),
                    key=lambda f: (-f["salas"], -f["prio"]))[:30]
    for f in estreias + cartaz:
        f.pop("prio", None)
    print(f"cinema: {len(estreias)} estreias, {len(cartaz)} em cartaz")
    return {"estreias": estreias, "cartaz": cartaz}


def chave_titulo(t):
    return re.sub(r"[^a-z0-9]", "", t.lower())[:60]


VAZIAS = set("""para pela pelo pelos pelas com sem sobre após antes entre como mais menos muito muita
quando onde qual quais quem isso esse essa este esta aquele aquela seus suas dele dela eles elas
será serão foram estão está ainda também já não sim novo nova novos novas diz afirma veja saiba
vai pode podem deve devem fazer feito anos hoje ontem amanhã contra desde até""".split())


def palavras(t):
    """Palavras que contam para achar a mesma notícia em fontes diferentes."""
    t = re.sub(r"[̀-ͯ]", "", __import__("unicodedata").normalize("NFD", t.lower()))
    return {w for w in re.findall(r"[a-z0-9]+", t) if (len(w) >= 4 or w.isdigit()) and w not in VAZIAS}


def mesma_noticia(a, b):
    comum = len(a & b)
    return comum >= 3 and comum / min(len(a), len(b)) >= 0.6


ESPN = "https://site.api.espn.com/apis"
COMP = {"Brazil Serie A": "Brasileirão", "Brazil Serie B": "Série B", "Brazil Copa do Brasil": "Copa do Brasil",
        "CONMEBOL Libertadores": "Libertadores", "CONMEBOL Sudamericana": "Sul-Americana",
        "Brazil Campeonato Paulista": "Paulistão"}


def jogo(e, time_id="874"):
    c = e["competitions"][0]
    lados = {x["homeAway"]: x for x in c["competitors"]}
    nosso = next(x for x in c["competitors"] if x["team"]["id"] == time_id)
    outro = next(x for x in c["competitors"] if x["team"]["id"] != time_id)
    def placar(x):
        sc = x.get("score")
        return (sc.get("displayValue") if isinstance(sc, dict) else sc) if sc is not None else None
    def logo(t):
        return (t.get("logos") or [{}])[0].get("href") or t.get("logo")
    liga = (e.get("league") or {}).get("abbreviation") or (e.get("seasonType") or {}).get("name") or ""
    st = c["status"]["type"]
    return {"data": e["date"], "comp": COMP.get(liga, liga.replace("Brazil ", "")),
            "casa": nosso["homeAway"] == "home", "adv": outro["team"].get("shortDisplayName") or outro["team"]["displayName"],
            "advLogo": logo(outro["team"]), "nos": placar(nosso), "eles": placar(outro),
            "fim": st.get("completed", False), "aoVivo": st.get("state") == "in",
            "mandante": lados["home"]["team"].get("shortDisplayName"), "visitante": lados["away"]["team"].get("shortDisplayName")}


def coletar_timao():
    """Próximos jogos, últimos resultados e tabela do Brasileirão pela API aberta da ESPN."""
    def pega(caminho):
        return json.loads(baixar(f"{ESPN}/{caminho}")[0])
    passados = sorted(pega("site/v2/sports/soccer/all/teams/874/schedule").get("events", []), key=lambda e: e["date"])
    futuros = sorted(pega("site/v2/sports/soccer/all/teams/874/schedule?fixture=true").get("events", []), key=lambda e: e["date"])
    ultimos = [jogo(e) for e in passados if e["competitions"][0]["status"]["type"].get("completed")][-5:][::-1]
    proximos = [jogo(e) for e in futuros if not e["competitions"][0]["status"]["type"].get("completed")][:3]
    tabela = []
    for x in pega("v2/sports/soccer/bra.1/standings")["children"][0]["standings"]["entries"]:
        st = {k["name"]: k.get("displayValue") for k in x["stats"]}
        tabela.append({"pos": int(st.get("rank") or 0), "id": x["team"]["id"],
                       "time": x["team"].get("shortDisplayName") or x["team"]["displayName"],
                       "logo": (x["team"].get("logos") or [{}])[0].get("href"),
                       "pts": st.get("points"), "j": st.get("gamesPlayed"), "v": st.get("wins"),
                       "e": st.get("ties"), "d": st.get("losses"), "sg": st.get("pointDifferential")})
    tabela.sort(key=lambda t: t["pos"])
    print(f"corinthians: {len(proximos)} próximos, {len(ultimos)} últimos, tabela com {len(tabela)}")
    return {"proximos": proximos, "ultimos": ultimos, "tabela": tabela}


INPEACE = "https://admin.inpeaceapp.com"
IGREJA_SITE = "https://lugardoencontro.inpeaceapp.com"


def coletar_igreja():
    """Agenda e mensagens da Lugar do Encontro (app InPeace, dados públicos)."""
    ev = json.loads(baixar(f"{INPEACE}/bff/events/pub/churches/ebbb8dd1-3d61-11ef-9c2d-02a781b073cb")[0]).get("data", [])
    agenda = [{"id": e["id"], "t": e["name"].strip(), "ini": e["startDate"], "fim": e.get("endDate"),
               "img": (e.get("image") or {}).get("url"), "pago": "paid" in (e.get("categories") or []),
               "gratis": "free" in (e.get("categories") or []), "online": e.get("modality") == "online",
               "vagas": "few-vacancies" in (e.get("categories") or []), "u": f"{IGREJA_SITE}/events/{e['id']}"}
              for e in ev]
    agenda.sort(key=lambda e: e["ini"])
    vd = json.loads(baixar(f"{INPEACE}/api/v1/video/avsantoandre")[0]).get("items", [])
    videos = [{"t": v["snippet"]["title"].strip(), "ts": v["snippet"]["publishedAt"], "img": v["snippet"].get("image"),
               "u": f"https://www.youtube.com/watch?v={v['contentDetails']['videoId']}"}
              for v in vd if (v.get("status") or {}).get("privacyStatus", "public") == "public"][:24]
    print(f"igreja: {len(agenda)} eventos, {len(videos)} mensagens")
    return {"agenda": agenda, "videos": videos}


def main():
    antigos = {}
    if SAIDA.exists():
        try:
            antigos = {i["id"]: i for i in json.loads(SAIDA.read_text())["items"]}
        except Exception:
            pass
    novos = []
    for url, fonte, cat in FEEDS:
        novos += ler_feed(url, fonte, cat)
    novos += ler_omelete_ccxp()

    agora = int(time.time() * 1000)
    limite = agora - DIAS * 86400_000
    todos = dict(antigos)
    for i in novos:
        velho = todos.get(i["id"])
        if velho and not i["img"]:
            i["img"] = velho.get("img")
        if i.pop("sem_data"):
            i["ts"] = velho["ts"] if velho else agora
        todos[i["id"]] = i
    # tira itens velhos, do futuro e repetidos (mesmo título em fontes diferentes)
    # a mesma notícia em várias fontes vira um card só, com as outras em "alt"
    vistos, itens, chaves = set(), [], []
    for i in sorted(todos.values(), key=lambda x: (x["img"] is None, -x["ts"])):
        k = chave_titulo(i["t"])
        i.pop("alt", None)
        if i["ts"] < agora - DIAS_CAT.get(i["cat"], DIAS) * 86400_000 or k in vistos or i["t"].rstrip().endswith("globoesporte.com") or classificar(i["t"], i.get("d", ""), i["cat"]) is None:
            continue
        pw = palavras(i["t"])
        par = next((j for j, pj in zip(itens, chaves) if abs(j["ts"] - i["ts"]) < 2 * 86400_000 and mesma_noticia(pw, pj)), None)
        if par:
            if i["src"] != par["src"] and all(a["src"] != i["src"] for a in par.get("alt", [])):
                par.setdefault("alt", []).append({"src": i["src"], "u": i["u"]})
            continue
        i["ts"] = min(i["ts"], agora)
        vistos.add(k)
        itens.append(i)
        chaves.append(pw)

    sem_foto = [i for i in itens if not i["img"] and "news.google." not in i["u"]]
    print(f"buscando foto de {len(sem_foto)} matérias…")
    with cf.ThreadPoolExecutor(12) as ex:
        for i, img in zip(sem_foto, ex.map(lambda x: og_image(x["u"]), sem_foto)):
            i["img"] = img

    itens.sort(key=lambda x: -x["ts"])
    por_cat, final = {}, []
    for i in itens:
        if por_cat.get(i["cat"], 0) < MAX_CAT.get(i["cat"], MAX_POR_CAT):
            por_cat[i["cat"]] = por_cat.get(i["cat"], 0) + 1
            final.append(i)
    SAIDA.write_text(json.dumps({"updatedAt": agora, "items": final}, ensure_ascii=False, separators=(",", ":")))
    try:
        cine = coletar_cinema()
        cine["updatedAt"] = agora
        (RAIZ / "cinema.json").write_text(json.dumps(cine, ensure_ascii=False, separators=(",", ":")))
    except Exception as e:  # se a Ingresso cair, fica a lista anterior
        print(f"  ✗ cinema: {e}")
    try:
        timao = coletar_timao()
        timao["updatedAt"] = agora
        (RAIZ / "time.json").write_text(json.dumps(timao, ensure_ascii=False, separators=(",", ":")))
    except Exception as e:  # se a ESPN cair, fica o placar anterior
        print(f"  ✗ corinthians: {e}")
    try:
        ig = coletar_igreja()
        ig["updatedAt"] = agora
        (RAIZ / "igreja.json").write_text(json.dumps(ig, ensure_ascii=False, separators=(",", ":")))
    except Exception as e:  # se o app da igreja cair, fica a agenda anterior
        print(f"  ✗ igreja: {e}")
    print(f"notícias juntadas: {sum(len(i.get('alt', [])) for i in final)}")
    print("por editoria:", json.dumps(por_cat, ensure_ascii=False))
    print(f"com foto: {sum(1 for i in final if i['img'])}/{len(final)}")


if __name__ == "__main__":
    main()
