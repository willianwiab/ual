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
    ("https://g1.globo.com/rss/g1/pop-arte/", "g1", "pop"),
    ("https://www.metsul.com/feed/", "MetSul", "clima"),
    ("https://agenciabrasil.ebc.com.br/rss/geral/feed.xml", "Agência Brasil", None),
    ("https://www.bbc.com/portuguese/index.xml", "BBC Brasil", None),
    ("https://g1.globo.com/rss/g1/", "g1", None),
]

# Palavras inteiras (sem diferenciar maiúsculas). Termine com * para valer como prefixo: "deputad*".
POLITICA = ["lula", "bolsonaro", "bolsonarista*", "trump", "stf", "congresso", "senado", "senador*",
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
        "bets?", "apostas?", "process[oa]*", "condenad*", "justiça", "bbb", "a fazenda", "fofoca*", "traição", "trai", "luto", "pena de morte",
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
CORINTHIANS = ["corinthians", "timão", "neo química", "yuri alberto", "memphis"]

_RX = {}


def tem(texto, palavras):
    k = id(palavras)
    if k not in _RX:
        partes = [re.escape(p[:-1]).replace(r"\[", "[").replace(r"\]", "]") + r"\w*" if p.endswith("*")
                  else p for p in palavras]
        _RX[k] = re.compile(r"(?<![\wÀ-ÿ])(?:" + "|".join(partes) + r")(?![\wÀ-ÿ])", re.I)
    return bool(_RX[k].search(texto))


def classificar(titulo, desc, padrao):
    t = titulo + " " + desc[:200]
    if tem(titulo, POLITICA) or tem(desc[:300], POLITICA[:40]) or tem(titulo, RUIM):
        return None
    if tem(titulo, OBITO):
        return "obituario"
    if tem(titulo, CORINTHIANS):
        return "corinthians"
    if padrao == "corinthians":
        return "corinthians"
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
        if not titulo or not link.startswith("http"):
            continue
        cat = classificar(titulo, desc, padrao)
        if not cat:
            continue
        foto = foto_do_item(b) or foto_do_item(html.unescape(desc_raw))
        out.append({"id": hashlib.md5(link.encode()).hexdigest()[:12], "t": titulo, "u": link,
                    "d": desc[:220], "ts": ts, "sem_data": not ts, "cat": cat, "src": fonte, "img": foto})
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


def chave_titulo(t):
    return re.sub(r"[^a-z0-9]", "", t.lower())[:60]


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
    vistos, itens = set(), []
    for i in sorted(todos.values(), key=lambda x: (x["img"] is None, -x["ts"])):
        k = chave_titulo(i["t"])
        if i["ts"] < limite or k in vistos or classificar(i["t"], i.get("d", ""), i["cat"]) is None:
            continue
        i["ts"] = min(i["ts"], agora)
        vistos.add(k)
        itens.append(i)

    sem_foto = [i for i in itens if not i["img"]]
    print(f"buscando foto de {len(sem_foto)} matérias…")
    with cf.ThreadPoolExecutor(12) as ex:
        for i, img in zip(sem_foto, ex.map(lambda x: og_image(x["u"]), sem_foto)):
            i["img"] = img

    itens.sort(key=lambda x: -x["ts"])
    por_cat, final = {}, []
    for i in itens:
        if por_cat.get(i["cat"], 0) < MAX_POR_CAT:
            por_cat[i["cat"]] = por_cat.get(i["cat"], 0) + 1
            final.append(i)
    SAIDA.write_text(json.dumps({"updatedAt": agora, "items": final}, ensure_ascii=False, separators=(",", ":")))
    print("por editoria:", json.dumps(por_cat, ensure_ascii=False))
    print(f"com foto: {sum(1 for i in final if i['img'])}/{len(final)}")


if __name__ == "__main__":
    main()
