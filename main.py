# -*- coding: utf-8 -*-
"""
Toplu PDF E-İmza v5.0 (E-Tuğra / AKİS, akisp11.dll) - Yeni tasarım arayüz
"""
import io
import os
import re
import sys
import tempfile
import time
import ctypes
import math
import random
import hashlib
import faulthandler
import threading
import traceback
from itertools import accumulate
from operator import add
import tkinter as tk
import tkinter.font as tkfont
from tkinter import filedialog, messagebox, simpledialog

import pkcs11
from pkcs11 import Attribute, ObjectClass
from PIL import Image, ImageChops, ImageDraw, ImageFilter, ImageFont, ImageOps, ImageTk

try:
    import pymupdf as fitz
except ImportError:
    import fitz

from pyhanko.pdf_utils import images
from pyhanko.pdf_utils.incremental_writer import IncrementalPdfFileWriter
from pyhanko.pdf_utils.layout import (
    AxisAlignment, InnerScaling, Margins, SimpleBoxLayoutRule,
)
from pyhanko.sign import fields, signers
from pyhanko.sign.pkcs11 import PKCS11Signer, open_pkcs11_session
from pyhanko.stamp import TextStampStyle

# ------------------------- AYARLAR -------------------------
DLL_SECENEKLERI = {
    "E-Tuğra": r"C:\Windows\System32\akisp11.dll",
    "TÜRKTRUST": r"C:\Windows\System32\turktrustpkcs11.dll",
}
IMZALAYAN_AD = "BATUHAN MARAŞLI"
SOL_METIN = IMZALAYAN_AD                                  
SAG_METIN = f"Dijital olarak imzalayan {IMZALAYAN_AD}"   

BASE_DIR = os.path.dirname(os.path.abspath(sys.argv[0]))

# ------------------------- HATA GÜNLÜĞÜ -------------------------
# Uygulama beklenmedik biçimde kapanırsa nedeni e_imza_hata.log dosyasına yazılır
# (Python hataları + token DLL'inden gelen çökmeler dahil).
def _log_ac():
    for klasor in (BASE_DIR, tempfile.gettempdir()):
        try:
            yol = os.path.join(klasor, "e_imza_hata.log")
            kip = "w" if os.path.exists(yol) and os.path.getsize(yol) > 512 * 1024 else "a"
            return yol, open(yol, kip, encoding="utf-8", buffering=1)
        except OSError:
            continue
    return None, None


LOG_YOLU, _LOG_DOSYA = _log_ac()


def hata_yaz(baslik, metin=None):
    if _LOG_DOSYA is None:
        return
    try:
        _LOG_DOSYA.write(f"\n=== {time.strftime('%Y-%m-%d %H:%M:%S')} | {baslik} ===\n")
        if metin:
            _LOG_DOSYA.write(metin.rstrip() + "\n")
    except Exception:
        pass


def _kok_hata(tur, deger, tb):
    hata_yaz("Yakalanmamış hata", "".join(traceback.format_exception(tur, deger, tb)))


sys.excepthook = _kok_hata
if hasattr(threading, "excepthook"):
    threading.excepthook = lambda a: _kok_hata(a.exc_type, a.exc_value, a.exc_traceback)
# Python 3.10'daki faulthandler, token DLL'inin kendi içinde yakalayıp geçtiği zararsız
# istisnaları (örn. 0x80000003) da "fatal" diye log'a yazıyor. Gerçek çökmeleri main()
# içindeki işaret dosyası zaten tespit ediyor. Düşük seviyeli çökme izi gerekirse True yapın.
FAULTHANDLER_AKTIF = False
if FAULTHANDLER_AKTIF and _LOG_DOSYA is not None:
    try:
        faulthandler.enable(file=_LOG_DOSYA, all_threads=True)
    except Exception:
        pass
FONT_ADAYLARI = [
    r"C:\Windows\Fonts\segoeui.ttf",
    r"C:\Windows\Fonts\arial.ttf",
]
FONT_YAZI = next((f for f in FONT_ADAYLARI if os.path.exists(f)), FONT_ADAYLARI[0])

KUTU_GENISLIK = 250    # pt
KUTU_YUKSEKLIK = 92    # pt
KENAR_BOSLUK = 18      # pt 
ARAMA_ADIMI = 4        # pt  (boş yer arama hassasiyeti)
IZGARA_HUCRE = 4       # px  (doluluk haritası hücre boyutu)
TEMIZ_PAYI = 6         # pt  (imza ile içerik arasında bırakılacak boşluk)
DOLULUK_ESIGI = 25     # zemin renginden bu kadar farklı piksel = dolu
KUTU_OLCEKLERI = (1.0, 0.85, 0.7, 0.55)   # tam boy sığmazsa kutu küçültülür

# --- Geliştirilmiş Koyu Tema Renkleri ---
KEY = "#010203"            # şeffaf (pencere köşeleri) için anahtar renk
C_BG = "#020617"
C_CARD = "#091128"
C_INPUT = "#040814"
C_BORDER = "#1e3a8a"
C_BORDER_GLOW = "#3b82f6"
C_TEXT = "#ffffff"
C_MUTED = "#93c5fd"
C_SOFT = "#e0e7ff"
C_ACCENT = "#2563eb"
C_ACCENT_HOVER = "#3b82f6"
C_OK = "#10b981"
C_WARN = "#f59e0b"
C_ERR = "#ef4444"
C_DANGER = "#b91c1c"

# --- Tasarım ölçüleri (tasarım birimi; pencere ekrana K ile ölçeklenir) ---
DW, DH = 1489, 968
SS = 3                     # süper-örnekleme (kenar yumuşatma)
PENCERE_OLCEK = 0.78       # pencere boyutu: 1.0 = tam boy, 0.78 = küçük (0.6-1.0 arası deneyebilirsiniz)

# --- Yazı tipi dosyaları ---
def _font_bul(adaylar):
    return next((f for f in adaylar if os.path.exists(f)), None)

FONT_KALIN = _font_bul([
    r"C:\Windows\Fonts\segoeuib.ttf",
    r"C:\Windows\Fonts\arialbd.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
])


def _pil_font(yol, px):
    try:
        if yol:
            return ImageFont.truetype(yol, max(1, int(px)))
        return ImageFont.load_default(max(1, int(px)))
    except Exception:
        return ImageFont.load_default()


# ===================== ÇİZİM ALTYAPISI =====================
def _c(renk, a=255):
    if isinstance(renk, str):
        h = renk.lstrip("#")
        return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4)) + (a,)
    return tuple(renk) if len(renk) == 4 else tuple(renk) + (a,)


def _ara(duraklar, t):
    if t <= duraklar[0][0]:
        return duraklar[0][1]
    for (p0, c0), (p1, c1) in zip(duraklar, duraklar[1:]):
        if t <= p1:
            u = (t - p0) / (p1 - p0) if p1 > p0 else 0
            return tuple(int(round(a + (b - a) * u)) for a, b in zip(c0, c1))
    return duraklar[-1][1]


def gradyan(boyut, duraklar, yon="h"):
    duraklar = [(p, _c(c)) for p, c in duraklar]
    w, h = boyut
    if yon == "d":
        return Image.blend(gradyan(boyut, [(p, c) for p, c in duraklar], "h"),
                           gradyan(boyut, [(p, c) for p, c in duraklar], "v"), 0.5)
    n = w if yon == "h" else h
    serit = Image.new("RGBA", (n, 1) if yon == "h" else (1, n))
    px = serit.load()
    for i in range(n):
        renk = _ara(duraklar, i / max(1, n - 1))
        px[(i, 0) if yon == "h" else (0, i)] = renk
    return serit.resize((w, h), Image.NEAREST)


def _parlat(img, f=0.16):
    r, g, b, a = img.split()
    rgb = Image.blend(Image.merge("RGB", (r, g, b)), Image.new("RGB", img.size, (255, 255, 255)), f)
    out = rgb.convert("RGBA")
    out.putalpha(a)
    return out


def _bez(p0, p1, p2, p3, n=28):
    pts = []
    for i in range(n + 1):
        t = i / n
        u = 1 - t
        pts.append((
            u**3 * p0[0] + 3 * u * u * t * p1[0] + 3 * u * t * t * p2[0] + t**3 * p3[0],
            u**3 * p0[1] + 3 * u * u * t * p1[1] + 3 * u * t * t * p2[1] + t**3 * p3[1],
        ))
    return pts


class Cizim:
    def __init__(self, w, h, k, ss=SS):
        self.dw, self.dh, self.k, self.ss = w, h, k, ss
        self.s = k * ss
        self.img = Image.new("RGBA", (max(1, round(w * self.s)), max(1, round(h * self.s))), (0, 0, 0, 0))
        self.d = ImageDraw.Draw(self.img)

    def t(self, v):
        return v * self.s

    def _bx(self, b):
        return [int(round(self.t(v))) for v in b]

    def yap(self, katman, x0, y0):
        W, H = self.img.size
        lx0, ly0 = max(0, -x0), max(0, -y0)
        lx1, ly1 = min(katman.width, W - x0), min(katman.height, H - y0)
        if lx1 <= lx0 or ly1 <= ly0:
            return
        self.img.alpha_composite(katman.crop((lx0, ly0, lx1, ly1)), (x0 + lx0, y0 + ly0))

    def _rr(self, b, r):
        x0, y0, x1, y1 = self._bx(b)
        w, h = x1 - x0, y1 - y0
        m = Image.new("L", (w, h), 0)
        ImageDraw.Draw(m).rounded_rectangle((0, 0, w - 1, h - 1), radius=int(self.t(r)), fill=255)
        return m, x0, y0

    def rrect(self, b, r, fill=None, grad=None, outline=None, ow=2):
        m, x0, y0 = self._rr(b, r)
        if grad is not None or fill is not None:
            katman = gradyan(m.size, grad[0], grad[1]) if grad else Image.new("RGBA", m.size, _c(fill))
            katman.putalpha(ImageChops.multiply(katman.getchannel("A"), m))
            self.yap(katman, x0, y0)
        if outline is not None:
            w, h = m.size
            halka = Image.new("L", m.size, 0)
            ImageDraw.Draw(halka).rounded_rectangle(
                (0, 0, w - 1, h - 1), radius=int(self.t(r)), outline=255, width=max(1, int(self.t(ow))))
            oc = _c(outline)
            katman = Image.new("RGBA", m.size, oc)
            katman.putalpha(halka.point(lambda p: p * oc[3] // 255))
            self.yap(katman, x0, y0)

    def isik(self, b, r, renk, blur, ow=3, alpha=0.6, dolu=False, dy=0):
        pad = int(self.t(blur * 3))
        x0, y0, x1, y1 = self._bx((b[0], b[1] + dy, b[2], b[3] + dy))
        m = Image.new("L", (x1 - x0 + 2 * pad, y1 - y0 + 2 * pad), 0)
        kutu = (pad, pad, pad + x1 - x0 - 1, pad + y1 - y0 - 1)
        d = ImageDraw.Draw(m)
        if dolu:
            d.rounded_rectangle(kutu, radius=int(self.t(r)), fill=255)
        else:
            d.rounded_rectangle(kutu, radius=int(self.t(r)), outline=255, width=max(1, int(self.t(ow))))
        m = m.filter(ImageFilter.GaussianBlur(self.t(blur))).point(lambda p: int(p * alpha))
        katman = Image.new("RGBA", m.size, _c(renk)[:3] + (255,))
        katman.putalpha(m)
        self.yap(katman, x0 - pad, y0 - pad)

    def radyal(self, cx, cy, rad, renk, alpha):
        d = max(2, int(self.t(rad * 2)))
        g = Image.radial_gradient("L").resize((d, d), Image.BILINEAR)
        m = g.point(lambda p: int((max(0, 255 - p) / 255) ** 2 * 255 * alpha))
        katman = Image.new("RGBA", (d, d), _c(renk)[:3] + (255,))
        katman.putalpha(m)
        self.yap(katman, int(self.t(cx)) - d // 2, int(self.t(cy)) - d // 2)

    def L(self, pts, w, renk, kapali=False):
        pp = [(self.t(x), self.t(y)) for x, y in pts]
        if kapali:
            pp.append(pp[0])
        rc = _c(renk)
        gen = max(1, int(self.t(w)))
        self.d.line(pp, fill=rc, width=gen, joint="curve")
        r = self.t(w) / 2
        for (x, y) in (pp[0], pp[-1]):
            self.d.ellipse((x - r, y - r, x + r, y + r), fill=rc)

    def E(self, cx, cy, r, fill=None, outline=None, w=0):
        x, y, rr = self.t(cx), self.t(cy), self.t(r)
        self.d.ellipse((x - rr, y - rr, x + rr, y + rr),
                       fill=_c(fill) if fill else None,
                       outline=_c(outline) if outline else None,
                       width=max(1, int(self.t(w))) if outline else 0)

    def poly(self, pts, fill):
        self.d.polygon([(self.t(x), self.t(y)) for x, y in pts], fill=_c(fill))

    def arc(self, cx, cy, r, a0, a1, w, renk):
        x, y, rr = self.t(cx), self.t(cy), self.t(r)
        self.d.arc((x - rr, y - rr, x + rr, y + rr), a0, a1, fill=_c(renk), width=max(1, int(self.t(w))))

    def yazi(self, x, y, metin, px, renk, anchor="mm"):
        self.d.text((self.t(x), self.t(y)), metin, font=_pil_font(FONT_KALIN, self.t(px)),
                    fill=_c(renk), anchor=anchor)

    def bitir(self):
        return self.img.resize((round(self.dw * self.k), round(self.dh * self.k)), Image.LANCZOS)


# ===================== MODERN İMLEÇ (FARE İŞARETİ) =====================
# Tema ile uyumlu: koyu lacivert zemin üstünde neon-mavi parlamalı oklar.
# İmleçler çalışma anında PIL ile çizilip .cur dosyasına yazılır; harici dosya gerekmez.
# Gerçek sistem imleci olduğu için gecikmesiz çalışır, diyaloglarda da geçerlidir.
IMLEC = {"ok": "arrow", "el": "hand2", "yazi": "xterm"}   # başarısız olursa sistem imleci kalır
IMLEC_BOYUT = 32
_IMLEC_SS = 8                                              # süper-örnekleme
IMLEC_OLCEK = 1.2          # imleç büyüklüğü (1.0 = eski boyut; 32x32 tuvale sığması için en fazla ~1.22)
IMLEC_UC = (4, 2)          # okun ucunun (hotspot) tuvaldeki yeri


def _imlec_maske(cizim_fn):
    b = IMLEC_BOYUT * _IMLEC_SS
    m = Image.new("L", (b, b), 0)
    cizim_fn(ImageDraw.Draw(m), _IMLEC_SS)
    # köşeleri yumuşat (hafif yuvarlatma)
    return m.filter(ImageFilter.GaussianBlur(_IMLEC_SS * 0.45)).point(lambda v: 255 if v > 127 else 0)


def _imlec_f():
    return max(0.5, min(IMLEC_OLCEK, 1.22))


def _ok_cizim(d, s):
    f, (tx, ty) = _imlec_f(), IMLEC_UC
    p = [(4, 3), (4, 23), (9.0, 18.3), (12.4, 26.0), (15.6, 24.6), (12.3, 17.2), (19.2, 17.2)]
    d.polygon([((tx + (x - 4) * f) * s, (ty + (y - 3) * f) * s) for x, y in p], fill=255)


def _yazi_cizim(d, s):
    f = _imlec_f()

    def k(v):                       # (16, 16) merkezi etrafında ölçekle
        return (16 + (v - 16) * f) * s

    r = s * 0.8 * f
    d.rounded_rectangle([k(15), k(6), k(17), k(26)], radius=r, fill=255)
    d.rounded_rectangle([k(11), k(5), k(21), k(7.4)], radius=r, fill=255)
    d.rounded_rectangle([k(11), k(24.6), k(21), k(27)], radius=r, fill=255)


# --- Yanıp sönme (nabız) efekti ayarları ---
IMLEC_YANIP_SONME = False  # False yaparsanız imleç sabit renkte kalır
IMLEC_KARE_SAYISI = 16     # bir yanıp sönme turundaki kare sayısı
IMLEC_ARALIK_MS = 55       # kareler arası süre (16 x 55 ms ≈ 0,9 sn / tur)
IMLEC_YANIP_RENGI = "kirmizi"   # turuncu | sari | kirmizi | pembe | yesil | mor | camgobegi

# renk: (açık ton, ana ton, hale rengi)  -> yanıp sönmenin "tepe" rengi
_YANIP_PALETLER = {
    "turuncu":   ("#fde047", "#f97316", "#fb923c"),
    "sari":      ("#fef9c3", "#facc15", "#fde047"),
    "kirmizi":   ("#fecaca", "#ef4444", "#f87171"),
    "pembe":     ("#fbcfe8", "#ec4899", "#f472b6"),
    "yesil":     ("#bbf7d0", "#22c55e", "#4ade80"),
    "mor":       ("#e9d5ff", "#a855f7", "#c084fc"),
    "camgobegi": ("#a5f3fc", "#06b6d4", "#22d3ee"),
}


def _yanip_tepe():
    acik, ana, hale = _YANIP_PALETLER.get(IMLEC_YANIP_RENGI, _YANIP_PALETLER["turuncu"])
    return {
        "ok":   (acik, ana, "#ffffff", hale, 255),
        "el":   (acik, ana, "#0a1236", hale, 255),
        "yazi": (acik, ana, "#ffffff", hale, 255),
    }
IMLEC_KARELERI = {}        # {'ok': ["@yol_00", "@yol_01", ...], ...}


def _renk_karistir(a, b, u):
    ca, cb = _c(a), _c(b)
    return "#%02x%02x%02x" % tuple(int(round(x + (y - x) * u)) for x, y in zip(ca[:3], cb[:3]))


def _imlec_katmanlari(maske, kenar_kal):
    """Renkten bağımsız (yalnızca şekle bağlı) katmanlar: bir kez hesaplanır, tüm karelerde kullanılır."""
    s = _IMLEC_SS
    hale = maske.filter(ImageFilter.MaxFilter(2 * int(s * 1.3) + 1)).filter(ImageFilter.GaussianBlur(s * 1.5))
    gen = maske.filter(ImageFilter.MaxFilter(2 * int(s * kenar_kal) + 1))
    ic = maske.filter(ImageFilter.MinFilter(2 * int(s * 0.9) + 1))
    return hale, gen, ImageChops.subtract(maske, ic)


def _imlec_kare(maske, katmanlar, ust, alt, kenar, parlama, parlama_a):
    """maske: şekil. ust/alt: dolgu gradyanı. kenar: dış çizgi. parlama: neon hale."""
    hale_m, gen, parilti = katmanlar
    b = maske.size
    # 1) dış neon parlama
    img = Image.new("RGBA", b, _c(parlama)[:3] + (0,))
    img.putalpha(hale_m.point(lambda v: int(v * parlama_a / 255)))
    # 2) kenar çizgisi (şeklin biraz genişletilmişi)
    kc = Image.new("RGBA", b, _c(kenar)[:3] + (0,))
    kc.putalpha(gen)
    img.alpha_composite(kc)
    # 3) gradyan dolgu
    dolgu = gradyan(b, [(0, ust), (1, alt)], "v")
    dolgu.putalpha(maske)
    img.alpha_composite(dolgu)
    # 4) üst kenarda ince ışık çizgisi
    ust_isik = Image.new("RGBA", b, (255, 255, 255, 0))
    ust_isik.putalpha(parilti.point(lambda v: int(v * 0.35)))
    img.alpha_composite(ust_isik)
    return img.resize((IMLEC_BOYUT, IMLEC_BOYUT), Image.LANCZOS)


# tip: (şekil, hotspot, kenar kalınlığı, DİNLENME paleti)  — TEPE paleti _yanip_tepe()'den gelir
# palet: (dolgu üst, dolgu alt, kenar, hale rengi, hale opaklığı)
_IMLEC_TANIM = {
    # Normal ok: beyaz/buz mavisi
    "ok": (_ok_cizim, IMLEC_UC, 1.25,
           ("#ffffff", "#bfdbfe", "#0a1236", "#3b82f6", 150)),
    # Tıklanabilir el: mavi
    "el": (_ok_cizim, IMLEC_UC, 1.1,
           ("#7dd3fc", "#2563eb", "#ffffff", "#38bdf8", 190)),
    # Metin girişi: I-beam
    "yazi": (_yazi_cizim, (16, 16), 0.9,
             ("#ffffff", "#dbeafe", "#0a1236", "#3b82f6", 130)),
}


def imlec_goruntuleri():
    """{'ok','el','yazi'} -> [(RGBA görsel, (hotspot_x, hotspot_y)), ...]  (yanıp sönme kareleri)"""
    n = IMLEC_KARE_SAYISI if IMLEC_YANIP_SONME else 1
    sonuc = {}
    tepe = _yanip_tepe()
    for ad, (cizim, hs, kalin, a) in _IMLEC_TANIM.items():
        b = tepe[ad]
        maske = _imlec_maske(cizim)
        katmanlar = _imlec_katmanlari(maske, kalin)
        kareler = []
        for k in range(n):
            u = 0.5 - 0.5 * math.cos(2 * math.pi * k / n)   # 0 = dinlenme, 1 = tepe
            u = min(1.0, max(0.0, (u - 0.5) * 1.7 + 0.5))   # geçişi hızlandır, uçlarda bekle
            u = u * u * (3 - 2 * u)                          # yumuşat -> net bir yanıp sönme
            ust, alt, kenar, parlama = (_renk_karistir(a[i], b[i], u) for i in range(4))
            alfa = int(a[4] + (b[4] - a[4]) * u)
            kareler.append((_imlec_kare(maske, katmanlar, ust, alt, kenar, parlama, alfa), hs))
        sonuc[ad] = kareler
    return sonuc


def cur_yaz(img, hotspot, yol):
    """RGBA görseli 32-bit alfa kanallı Windows .cur dosyasına yazar (atomik: yarım dosya kalmaz)."""
    import struct
    w, h = img.size
    piksel = img.transpose(Image.FLIP_TOP_BOTTOM).tobytes("raw", "BGRA")
    and_maske = bytes(((w + 31) // 32 * 4) * h)
    dib = struct.pack("<IiiHHIIiiII", 40, w, h * 2, 1, 32, 0,
                      len(piksel) + len(and_maske), 0, 0, 0, 0) + piksel + and_maske
    gecici = yol + ".tmp"
    with open(gecici, "wb") as f:
        f.write(struct.pack("<HHH", 0, 2, 1))
        f.write(struct.pack("<BBBBHHII", w, h, 0, 0, hotspot[0], hotspot[1], len(dib), 22))
        f.write(dib)
    os.replace(gecici, yol)


def _kisa_yol(yol):
    """Türkçe karakter/boşluk sorunlarını önlemek için 8.3 kısa yol (olmazsa olduğu gibi)."""
    try:
        tampon = ctypes.create_unicode_buffer(520)
        if ctypes.windll.kernel32.GetShortPathNameW(yol, tampon, 520):
            yol = tampon.value
    except Exception:
        pass
    return yol.replace("\\", "/")


def _imlec_parmak_izi():
    ham = repr((IMLEC_BOYUT, IMLEC_OLCEK, IMLEC_YANIP_SONME, IMLEC_KARE_SAYISI,
                IMLEC_YANIP_RENGI, IMLEC_UC, "v3"))
    return hashlib.md5(ham.encode()).hexdigest()[:8]


def imlecleri_hazirla(pencere):
    """Modern imleçleri üretir ve IMLEC sözlüğünü günceller. Sorun olursa sistem imleci kalır.
    Dosyalar ayara göre önbelleğe alınır: ayar değişmedikçe her açılışta yeniden çizilmez."""
    if sys.platform != "win32":
        return IMLEC
    try:
        n = IMLEC_KARE_SAYISI if IMLEC_YANIP_SONME else 1
        klasor = os.path.join(tempfile.gettempdir(), "batuhan_imza_imlec_" + _imlec_parmak_izi())
        os.makedirs(klasor, exist_ok=True)
        yollar = {ad: [os.path.join(klasor, f"{ad}_{k:02d}.cur") for k in range(n)] for ad in _IMLEC_TANIM}
        hazir = all(os.path.isfile(y) and os.path.getsize(y) > 0 for l in yollar.values() for y in l)
        if not hazir:
            for ad, liste in imlec_goruntuleri().items():
                for (img, hs), yol in zip(liste, yollar[ad]):
                    cur_yaz(img, hs, yol)
        yeni, kareler = {}, {}
        for ad, liste in yollar.items():
            degerler = ["@" + _kisa_yol(y) for y in liste]
            pencere.configure(cursor=degerler[0])      # geçersizse TclError verir
            kareler[ad] = degerler
            yeni[ad] = degerler[0]
        pencere.configure(cursor="")
        IMLEC_KARELERI.update(kareler)
        IMLEC.update(yeni)
    except Exception:
        hata_yaz("İmleç hazırlanamadı", traceback.format_exc())
        IMLEC_KARELERI.clear()
    return IMLEC


def imlec_animasyonunu_baslat(kok):
    """İmleç karelerini sırayla değiştirerek rengin yanıp sönmesini sağlar."""
    # Yanıp sönme kapalıysa her imleç için tek kare üretilir; animasyona gerek yok.
    if not IMLEC_YANIP_SONME or not IMLEC_KARELERI or IMLEC_KARE_SAYISI < 2:
        return
    durum = {"i": 0}

    def uygula(w, esle):
        try:
            yeni = esle.get(str(w.cget("cursor")))
            if yeni:
                w.configure(cursor=yeni)
            alt = w.winfo_children()
        except tk.TclError:
            return
        for c in alt:
            uygula(c, esle)

    def adim():
        try:
            if not kok.winfo_exists():
                return
        except tk.TclError:
            return
        bekle = IMLEC_ARALIK_MS
        try:
            if not kok.winfo_viewable():          # simge durumunda boşuna çalışma
                bekle = 300
            else:
                durum["i"] = (durum["i"] + 1) % IMLEC_KARE_SAYISI
                esle = {}
                for ad, liste in IMLEC_KARELERI.items():
                    if not liste:
                        continue
                    yeni = liste[durum["i"] % len(liste)]   # liste kısaysa taşmasın
                    IMLEC[ad] = yeni
                    # herhangi bir eski kare -> güncel kare (takılı kalmış öğeler de kendini toparlar)
                    esle.update({k: yeni for k in liste if k != yeni})
                uygula(kok, esle)
        except tk.TclError:
            pass
        except Exception:
            hata_yaz("İmleç animasyonu", traceback.format_exc())
            bekle = 500
        try:
            kok.after(bekle, adim)
        except tk.TclError:
            pass

    kok.after(IMLEC_ARALIK_MS, adim)


def imza_gorseli_olustur(sol_metin=None, sag_metin=None) -> Image.Image:
    sol_metin = sol_metin or SOL_METIN
    sag_metin = sag_metin or SAG_METIN
    S = 6  
    w, h = KUTU_GENISLIK * S, KUTU_YUKSEKLIK * S
    img = Image.new("RGB", (w, h), (255, 255, 255))

    d = ImageDraw.Draw(img)
    pad = 4 * S
    sol_gen = int(w * 0.50) - pad
    sag_x = int(w * 0.53)
    sag_gen = w - sag_x - pad
    kullan_h = h - 2 * pad

    def satir_yuksekligi(font):
        asc, desc = font.getmetrics()
        return asc + desc

    sol_satirlar = sol_metin.split()
    px = int(h * 0.45)
    while px > 8:
        f = ImageFont.truetype(FONT_YAZI, px)
        en_genis = max(d.textlength(t, font=f) for t in sol_satirlar)
        if en_genis <= sol_gen and len(sol_satirlar) * satir_yuksekligi(f) <= kullan_h:
            break
        px -= 2
    f_sol = ImageFont.truetype(FONT_YAZI, px)
    lh = satir_yuksekligi(f_sol)
    y = (h - lh * len(sol_satirlar)) / 2
    for t in sol_satirlar:
        d.text((pad, y), t, font=f_sol, fill=(0, 0, 0), anchor="la")
        y += lh

    px = int(h * 0.34)
    while px > 8:
        f = ImageFont.truetype(FONT_YAZI, px)
        satirlar = _sar(d, sag_metin, f, sag_gen)
        sigiyor = all(d.textlength(t, font=f) <= sag_gen for t in satirlar)
        if sigiyor and len(satirlar) * satir_yuksekligi(f) <= kullan_h:
            break
        px -= 2
    f_sag = ImageFont.truetype(FONT_YAZI, px)
    satirlar = _sar(d, sag_metin, f_sag, sag_gen)
    lh = satir_yuksekligi(f_sag)
    y = (h - lh * len(satirlar)) / 2
    for t in satirlar:
        d.text((sag_x, y), t, font=f_sag, fill=(0, 0, 0), anchor="la")
        y += lh

    return img


def _sar(d, metin, font, maks):
    satirlar, cur = [], ""
    for kelime in metin.split():
        deneme = (cur + " " + kelime).strip()
        if cur == "" or d.textlength(deneme, font=font) <= maks:
            cur = deneme
        else:
            satirlar.append(cur)
            cur = kelime
    if cur:
        satirlar.append(cur)
    return satirlar


def stil_olustur(gorsel: Image.Image) -> TextStampStyle:
    return TextStampStyle(
        stamp_text=" ",
        background=images.PdfImage(gorsel),
        background_opacity=1.0,
        background_layout=SimpleBoxLayoutRule(
            x_align=AxisAlignment.ALIGN_MID,
            y_align=AxisAlignment.ALIGN_MID,
            margins=Margins.uniform(0),
            inner_content_scaling=InnerScaling.STRETCH_FILL,
        ),
        border_width=0,
    )


_DOLU_TABLO = bytes([0]) + bytes([1]) * 255


def _doluluk_izgarasi(page):
    """Sayfayı görüntüye çevirip dolu (yazı/çizgi/resim/dolgu) hücreleri işaretler.
    İçerik nasıl üretilmiş olursa olsun gözle görünen her şey engel sayılır.
    Hızlı sorgu için integral görüntü (toplam tablosu) döner."""
    pix = page.get_pixmap(matrix=fitz.Matrix(1, 1), colorspace=fitz.csGRAY, alpha=False)
    img = Image.frombuffer("L", (pix.width, pix.height), pix.samples, "raw", "L", pix.stride, 1)

    # Sayfanın zemin rengi (en sık görülen gri ton); renkli/gri zeminli sayfalar da çalışsın
    hist = img.histogram()
    zemin = max(range(256), key=hist.__getitem__)
    maske = img.point([255 if abs(v - zemin) > DOLULUK_ESIGI else 0 for v in range(256)])

    gw = max(1, -(-pix.width // IZGARA_HUCRE))
    gh = max(1, -(-pix.height // IZGARA_HUCRE))
    kucuk = maske.resize((gw, gh), Image.BOX)       # hücrede 1 piksel bile doluysa > 0
    veri = kucuk.tobytes().translate(_DOLU_TABLO)   # 0/1 baytları

    # integral görüntü: satır başına C hızında accumulate/map (eski çift döngüden çok daha hızlı)
    I = [[0] * (gw + 1)]
    for y in range(gh):
        I.append([0] + list(map(add, I[y][1:], accumulate(veri[y * gw:(y + 1) * gw]))))
    return I, gw, gh, pix.width / gw, pix.height / gh


def _bos_yer_bul(page, bw, bh, m):
    """Sağ alt köşeye en yakın, tamamen boş (bw x bh) alanı bulur. Yer yoksa None döner."""
    W, H = page.rect.width, page.rect.height
    I, gw, gh, cw, ch = _doluluk_izgarasi(page)
    pay = TEMIZ_PAYI

    def dolu_sayisi(x0, y0, x1, y1):
        cx0 = max(0, int(math.floor((x0 - pay) / cw)))
        cy0 = max(0, int(math.floor((y0 - pay) / ch)))
        cx1 = min(gw, int(math.ceil((x1 + pay) / cw)))
        cy1 = min(gh, int(math.ceil((y1 + pay) / ch)))
        if cx1 <= cx0 or cy1 <= cy0:
            return 0
        return I[cy1][cx1] - I[cy0][cx1] - I[cy1][cx0] + I[cy0][cx0]

    for olcek in KUTU_OLCEKLERI:
        w, h = bw * olcek, bh * olcek
        ax, ay = W - m - w, H - m - h          # tercih edilen konum: sağ alt köşe
        if ax < m or ay < m:
            continue
        en_iyi = None
        y = ay
        while y >= m:
            dy2 = (1.5 * (ay - y)) ** 2        # aşağıda kalmayı, sola kaymaya tercih et
            if en_iyi is not None and dy2 >= en_iyi[0]:
                break                          # bundan yukarıdaki satırlar daha uzak: aramayı bitir
            x = ax
            while x >= m:
                if dolu_sayisi(x, y, x + w, y + h) == 0:
                    uzaklik = (ax - x) ** 2 + dy2
                    if en_iyi is None or uzaklik < en_iyi[0]:
                        en_iyi = (uzaklik, x, y)
                    break                      # satırda sağdan ilk boş konum en yakın olandır
                x -= ARAMA_ADIMI
            y -= ARAMA_ADIMI
        if en_iyi is not None:
            _, x, y = en_iyi
            return fitz.Rect(x, y, x + w, y + h)

    # Hiçbir ölçekte tamamen boş yer yok: bu sayfa imzalanmayacak
    return None


def sayfa_kutulari_hesapla(pdf_yolu, sayfalar=None):
    """(kutular, atlanan) döner. atlanan: boş yer bulunamayan sayfa numaraları (1'den başlar)."""
    kutular = []
    atlanan = []
    doc = fitz.open(pdf_yolu)
    try:
        for idx, page in enumerate(doc):
            if sayfalar is not None and (idx + 1) not in sayfalar:
                continue
            page.set_rotation(0)
            secilen = _bos_yer_bul(page, KUTU_GENISLIK, KUTU_YUKSEKLIK, KENAR_BOSLUK)
            if secilen is None:
                atlanan.append(idx + 1)
                continue

            pdf_r = fitz.Rect(secilen).transform(~page.transformation_matrix)
            pdf_r.normalize()
            kutular.append((idx, (pdf_r.x0, pdf_r.y0, pdf_r.x1, pdf_r.y1)))
    finally:
        doc.close()
    return kutular, atlanan


def sayfa_metnini_coz(metin):
    sonuc = set()
    for parca in metin.replace(" ", "").replace(";", ",").split(","):
        if not parca:
            continue
        m = re.fullmatch(r"(\d+)(?:-(\d+))?", parca)
        if not m:
            raise ValueError(f"Geçersiz ifade: '{parca}'")
        a = int(m.group(1))
        b = int(m.group(2) or a)
        if a < 1 or b < a:
            raise ValueError(f"Geçersiz aralık: '{parca}'")
        sonuc.update(range(a, b + 1))
    if not sonuc:
        raise ValueError("Sayfa numarası girilmedi.")
    return sorted(sonuc)


def anahtar_bul(session, ana=None):
    anahtarlar = list(session.get_objects({Attribute.CLASS: ObjectClass.PRIVATE_KEY}))
    if not anahtarlar:
        raise RuntimeError("Token üzerinde özel anahtar bulunamadı.")
    if len(anahtarlar) > 1:
        satirlar = [f"{i}: {a.label}" for i, a in enumerate(anahtarlar)]
        secim = simpledialog.askinteger(
            "Sertifika seçimi", "Hangi anahtar kullanılsın?\n\n" + "\n".join(satirlar),
            minvalue=0, maxvalue=len(anahtarlar) - 1, parent=ana,
        )
        if secim is None:
            raise RuntimeError("Sertifika seçilmedi.")
        return anahtarlar[secim]
    return anahtarlar[0]


def _koyu_baslik_uygula(pencere):
    try:
        pencere.update_idletasks()
        hwnd = ctypes.windll.user32.GetParent(pencere.winfo_id())
        deger = ctypes.c_int(1)
        for attr in (20, 19):
            ctypes.windll.dwmapi.DwmSetWindowAttribute(
                hwnd, attr, ctypes.byref(deger), ctypes.sizeof(deger))
    except Exception:
        pass


def koyu_diyalog(ana, baslik, aciklama, gizli=False, secenekler=None, secili=None, ilk=""):
    sonuc = {"deger": None}
    d = tk.Toplevel(ana)
    d.title(baslik)
    d.configure(bg=C_CARD, cursor=IMLEC["ok"])
    d.resizable(False, False)
    d.attributes("-topmost", True)

    tk.Label(d, text=aciklama, bg=C_CARD, fg=C_SOFT, font=("Segoe UI", 10),
             justify="left", wraplength=360).pack(anchor="w", padx=22, pady=(20, 12))

    secim = tk.StringVar(value=secili or (secenekler[0] if secenekler else ""))
    if secenekler:
        satir = tk.Frame(d, bg=C_CARD)
        satir.pack(fill="x", padx=22, pady=(0, 12))
        for s in secenekler:
            tk.Radiobutton(
                satir, text=s, value=s, variable=secim, indicatoron=False,
                bg=C_INPUT, fg=C_TEXT, selectcolor=C_ACCENT,
                activebackground=C_ACCENT_HOVER, activeforeground="white",
                relief="flat", bd=0, highlightthickness=0, cursor=IMLEC["el"],
                font=("Segoe UI", 10, "bold"), padx=16, pady=7,
            ).pack(side="left", padx=(0, 8))

    giris = tk.Entry(
        d, show="●" if gizli else "", font=("Segoe UI", 11), bg=C_INPUT, fg=C_TEXT,
        insertbackground=C_TEXT, relief="flat", bd=0, highlightthickness=1,
        highlightbackground=C_BORDER, highlightcolor=C_ACCENT_HOVER, cursor=IMLEC["yazi"],
    )
    giris.pack(fill="x", padx=22, ipady=8)
    giris.insert(0, ilk)

    def tamam(_=None):
        sonuc["deger"] = (secim.get(), giris.get().strip())
        d.destroy()

    def iptal(_=None):
        d.destroy()

    alt = tk.Frame(d, bg=C_CARD)
    alt.pack(fill="x", padx=22, pady=(16, 20))
    for metin, komut, bg, hv in (("Tamam", tamam, C_ACCENT, C_ACCENT_HOVER),
                                 ("İptal", iptal, C_INPUT, C_BORDER)):
        b = tk.Button(alt, text=metin, command=komut, bg=bg, fg="white", activebackground=hv,
                      activeforeground="white", font=("Segoe UI", 10, "bold"), relief="flat",
                      bd=0, cursor=IMLEC["el"], padx=20, pady=6)
        b.pack(side="right", padx=(8, 0))
        b.bind("<Enter>", lambda e, b=b, hv=hv: b.config(bg=hv))
        b.bind("<Leave>", lambda e, b=b, bg=bg: b.config(bg=bg))

    d.bind("<Return>", tamam)
    d.bind("<Escape>", iptal)

    d.update_idletasks()
    gen, yuk = max(d.winfo_reqwidth(), 420), d.winfo_reqheight()
    x = ana.winfo_x() + (ana.winfo_width() - gen) // 2
    y = ana.winfo_y() + (ana.winfo_height() - yuk) // 3
    d.geometry(f"{gen}x{yuk}+{max(0, x)}+{max(0, y)}")
    _koyu_baslik_uygula(d)

    try:
        d.wait_visibility()
        d.grab_set()
    except tk.TclError:
        pass
    d.lift()
    giris.focus_set()
    ana.wait_window(d)
    try:                      # çerçevesiz ana pencere diyalogdan sonra arkada kalmasın
        ana.lift()
        ana.focus_force()
    except tk.TclError:
        pass
    return sonuc["deger"]


# ===================== YENİ ARAYÜZ (tasarım görseli + canlı widget'lar) =====================
# Pencerenin sabit kısmı (başlık, kenar çubuğu, afiş, kart çerçeveleri, butonlar) tasarım görselinden
# gömülü arka plan olarak çizilir. Değişen her şey (dosya listesi, imza alanları, DLL seçimi, hover
# efektleri, sürükle-bırak) gerçek widget / canvas nesnesi olarak üstüne eklenir.
# Aşağıdaki tüm koordinatlar tasarım görseli (1536x1024) uzayındadır; pencere sol-üst köşesi (OX, OY).
OX, OY = 25, 25
PENCERE_YARICAP = 30

R_DOSYA_SEC = (549, 668, 789, 724)      # "Dosya Seç" butonu
R_BASLAT = (295, 860, 810, 948)         # "Toplu PDF İmzalamaya Başlat"
R_BIRAK = (312, 491, 1020, 733)         # sürükle-bırak alanının iç yüzü
R_LISTE = (320, 499, 1012, 725)         # dosya listesi (liste modunda)
R_AD = (1158, 505, 1467, 547)           # İmzalayan Adı kutusu
R_SOL = (1158, 588, 1467, 629)          # Sol Metin kutusu
R_SAG = (1158, 665, 1467, 725)          # Sağ Metin kutusu (2 satır)
R_DLL = (1143, 769, 1467, 810)          # DLL seçenekleri
R_KAPAT = (1449, 30, 1501, 74)
R_BUYUT = (1377, 30, 1429, 74)
R_KUCULT = (1303, 28, 1355, 72)
R_YAN = {                               # kenar çubuğu öğeleri
    "b_ayarlar": (42, 289, 229, 352),
    "b_hakkinda": (42, 361, 229, 424),
    "b_yardim": (42, 432, 229, 495),
}
BASLIK_ALTI = 158                       # bu çizginin üstü sürükleme (taşıma) alanı

FORM_ZEMIN = "#040c21"                  # giriş kutularının iç rengi (arka planla aynı)
LISTE_ZEMIN = "#091439"                 # dosya listesi zemini
YAZI_FONT = "Segoe UI"


def arkaplan_gorseli():
    """Gömülü tasarım görselini (DW x DH, RGBA) döndürür."""
    import base64
    foto = Image.open(io.BytesIO(base64.b64decode(ARKAPLAN_WEBP_B64))).convert("RGBA")
    if foto.size != (DW, DH):
        foto = foto.resize((DW, DH), Image.LANCZOS)
    return foto


def yuvarlak_maske(w, h, r, ss=4):
    """Kenarı yumuşatılmış yuvarlatılmış dikdörtgen maskesi."""
    w, h = max(1, int(w)), max(1, int(h))
    m = Image.new("L", (w * ss, h * ss), 0)
    ImageDraw.Draw(m).rounded_rectangle((0, 0, w * ss - 1, h * ss - 1), radius=int(r * ss), fill=255)
    return m.resize((w, h), Image.LANCZOS)


def ik_asagi(c, cx, cy, renk="#93c5fd", w=2.4):
    c.L([(cx - 6, cy - 3), (cx, cy + 3), (cx + 6, cy - 3)], w, renk)


def dugme_gorseli(K, w, h, r, ust, alt, kenar, ikon=None, glow=None):
    c = Cizim(w, h, K)
    if glow:
        c.isik((3, 3, w - 3, h - 3), r, glow, 5, ow=3, alpha=.50)
    c.rrect((0, 0, w, h), r, grad=([(0, ust), (1, alt)], "v"))
    c.rrect((0, 0, w, h), r, outline=_c(kenar), ow=2)
    if ikon:
        ikon(c)
    return c.bitir()


# ===================== YILDIZLI FARE İZİ (parlama efekti) =====================
# Fare pencerenin üstünde gezerken arkasında küçük yıldızlar / parıltılar bırakır, imlecin
# peşinden gecikmeli yumuşak bir ışık halesi gelir, tıklayınca küçük bir yıldız patlaması olur.
# Her şey ön-çizilmiş küçük PNG sprite'larla yapılır (PIL), canvas öğeleri havuzdan yeniden
# kullanılır; fare durunca zamanlayıcı yavaşlar, pencere simge durumundayken tamamen uyur.
IZ_AKTIF = True                 # False: efekt tamamen kapalı
IZ_YOGUNLUK = 1.0               # 0.5 seyrek · 1.0 normal · 2.0 yoğun
IZ_MAKS_PARCACIK = 56           # aynı anda ekranda en fazla kaç yıldız
IZ_HALE = True                  # imleci gecikmeyle izleyen yumuşak ışık
IZ_TIKLAMA_PATLAMASI = True     # tıklayınca yıldız patlaması
IZ_RENKLER = ("#ffffff", "#dbeafe", "#93c5fd", "#7dd3fc", "#c4b5fd", "#fde68a")
IZ_HALE_RENGI = (96, 165, 250)  # ışık halesinin rengi (RGB)
IZ_KARE_MS = 16                 # hareket varken kare aralığı (~60 FPS)
IZ_BOSTA_MS = 70                # hiçbir şey olmuyorken bekleme aralığı


class _Parcacik:
    __slots__ = ("oge", "x", "y", "vx", "vy", "yas", "omur", "boyut", "renk", "tip", "faz", "anahtar")


class YildizIzi:
    BOYUTLAR = (2.4, 3.6, 5.2, 7.2, 9.8)          # yıldız yarıçapları (px, ölçek=1)
    ALFALAR = (1.0, 0.8, 0.6, 0.42, 0.26, 0.12)   # parlaklık basamakları

    def __init__(self, kok, cv, K, W, H, kose_r):
        self.kok, self.cv, self.W, self.H = kok, cv, W, H
        self.kose_r = kose_r
        self.olcek = max(0.8, K)
        self.aktif = True
        self._taban, self._foto = {}, {}      # sprite önbellekleri (PIL / PhotoImage)
        self.havuz, self.canli = [], []
        self.son = None                       # imlecin bir önceki konumu
        self.hxy = None                       # ışık halesinin (gecikmeli) konumu
        self.hale_cizili = None
        self.hale_gorunur = False
        self.t_son = time.perf_counter()
        self._hata = 0
        self._after = None

        self.hale = None
        if IZ_HALE:
            self._hale_foto = self._hale_olustur()
            self.hale = cv.create_image(0, 0, image=self._hale_foto, state="hidden", tags=("iz",))
        if IZ_TIKLAMA_PATLAMASI:
            kok.bind_all("<ButtonPress-1>", self._tikla, add="+")
        self._after = kok.after(IZ_KARE_MS, self._adim)

    # ------------------------- sprite üretimi -------------------------
    def _hale_olustur(self):
        r = int(34 * self.olcek)
        d = 2 * r + 1
        g = Image.radial_gradient("L").resize((d, d), Image.BILINEAR)
        a = g.point([int(((255 - p) / 255) ** 1.9 * 255 * 0.36) for p in range(256)])
        img = Image.new("RGBA", (d, d), IZ_HALE_RENGI + (0,))
        img.putalpha(a)
        return ImageTk.PhotoImage(img)

    def _yildiz_pil(self, renk, R, tip):
        SS = 4
        pad = int(math.ceil(R * 2.4))
        D = pad * 2 + 1
        N = D * SS
        c = N / 2
        rgb = _c(renk)[:3]
        # 1) yumuşak hale
        g = Image.radial_gradient("L").resize((N, N), Image.BILINEAR)
        ha = 0.8 if tip == "nokta" else 0.55
        img = Image.new("RGBA", (N, N), rgb + (0,))
        img.putalpha(g.point([int(((255 - p) / 255) ** 2.6 * 255 * ha) for p in range(256)]))
        # 2) yıldız gövdesi (astroid eğrisi = ince uçlu dört köşeli yıldız)
        kat = Image.new("RGBA", (N, N), (0, 0, 0, 0))
        d = ImageDraw.Draw(kat)
        beyaz = tuple(int(v + (255 - v) * 0.72) for v in rgb)

        def astroid(rr, p, donme=0.0, n=72):
            pts = []
            for i in range(n):
                t = 2 * math.pi * i / n
                ct, st = math.cos(t), math.sin(t)
                x = rr * math.copysign(abs(ct) ** p, ct)
                y = rr * math.copysign(abs(st) ** p, st)
                if donme:
                    x, y = (x * math.cos(donme) - y * math.sin(donme),
                            x * math.sin(donme) + y * math.cos(donme))
                pts.append((c + x, c + y))
            return pts

        if tip == "yildiz":
            d.polygon(astroid(R * SS, 2.4), fill=beyaz + (255,))
            d.polygon(astroid(R * SS * 0.55, 2.4, math.pi / 4), fill=beyaz + (225,))
            rc = R * SS * 0.2
        else:
            rc = R * SS * 0.45
        d.ellipse((c - rc, c - rc, c + rc, c + rc), fill=(255, 255, 255, 255))
        img.alpha_composite(kat)
        return img.resize((D, D), Image.LANCZOS)

    def _sprite(self, renk, bi, tip, ai):
        k = (renk, bi, tip, ai)
        ph = self._foto.get(k)
        if ph is None:
            tb = self._taban.get((renk, bi, tip))
            if tb is None:
                tb = self._taban[(renk, bi, tip)] = self._yildiz_pil(renk, self.BOYUTLAR[bi] * self.olcek, tip)
            f = self.ALFALAR[ai]
            if f < 1.0:
                r, g, b, a = tb.split()
                tb = Image.merge("RGBA", (r, g, b, a.point([int(v * f) for v in range(256)])))
            ph = self._foto[k] = ImageTk.PhotoImage(tb)
        return ph

    # ------------------------- yardımcılar -------------------------
    def _gorunur(self, x, y):
        """Nokta pencerenin içinde mi? (yuvarlak köşelerin şeffaf kısmına çizim yapılmaz)"""
        if x < -4 or y < -4 or x > self.W + 4 or y > self.H + 4:
            return False
        r = self.kose_r
        cx = r if x < r else (self.W - r if x > self.W - r else None)
        cy = r if y < r else (self.H - r if y > self.H - r else None)
        if cx is None or cy is None:
            return True
        ic = max(2, r - 14 * self.olcek)
        return (x - cx) ** 2 + (y - cy) ** 2 <= ic * ic

    def _uret(self, x, y, hiz=0.0, guc=1.0):
        if len(self.canli) >= IZ_MAKS_PARCACIK or not self._gorunur(x, y):
            return
        a = random.uniform(0, 2 * math.pi)
        sp = random.uniform(10, 38) * (0.6 + 0.8 * min(1.0, hiz)) * guc
        p = _Parcacik()
        p.oge = self.havuz.pop() if self.havuz else self.cv.create_image(0, 0, state="hidden", tags=("iz",))
        p.x, p.y = x + random.uniform(-3, 3), y + random.uniform(-3, 3)
        p.vx, p.vy = math.cos(a) * sp, math.sin(a) * sp - 8
        p.yas, p.omur = 0.0, random.uniform(0.45, 0.95)
        p.boyut = random.random()
        p.renk = random.choice(IZ_RENKLER)
        p.tip = "yildiz" if random.random() < 0.7 else "nokta"
        p.faz = random.uniform(0, 6.28)
        p.anahtar = None
        self.canli.append(p)

    def _yol_boyunca(self, a, b):
        dx, dy = b[0] - a[0], b[1] - a[1]
        d = math.hypot(dx, dy)
        if d < 1.0:
            return False
        n = d / (11.0 / IZ_YOGUNLUK)
        adet = min(6, int(n) + (1 if random.random() < n - int(n) else 0))
        for k in range(adet):
            t = (k + random.random()) / adet
            self._uret(a[0] + dx * t, a[1] + dy * t, d / 60)
        return True

    def _birak(self, p):
        self.cv.itemconfigure(p.oge, state="hidden")
        self.havuz.append(p.oge)

    def _hepsini_birak(self):
        for p in self.canli:
            self._birak(p)
        self.canli = []
        if self.hale is not None and self.hale_gorunur:
            self.cv.itemconfigure(self.hale, state="hidden")
            self.hale_gorunur = False
        self.hxy = None

    # ------------------------- ana döngü -------------------------
    def _adim(self):
        self._after = None
        if not self.aktif:
            return
        try:
            if not self.kok.winfo_exists():
                return
            bekle = self._guncelle()
            self._hata = 0
        except (tk.TclError, RuntimeError):
            return                                  # pencere kapandı
        except Exception:
            self._hata += 1
            hata_yaz("Fare izi", traceback.format_exc())
            if self._hata >= 5:                     # sürekli hata veriyorsa efekti kapat, uygulama etkilenmesin
                self.durdur()
                return
            bekle = 120
        try:
            if self.aktif and self.kok.winfo_exists():
                self._after = self.kok.after(bekle, self._adim)
        except (tk.TclError, RuntimeError):
            pass

    def _guncelle(self):
        kok, cv = self.kok, self.cv
        if not kok.winfo_exists() or not kok.winfo_viewable(): # simge durumu veya kapanış
            if self.canli or self.hale_gorunur:
                self._hepsini_birak()
            self.son = None
            self.t_son = time.perf_counter()
            return 250

        simdi = time.perf_counter()
        dt = min(0.05, simdi - self.t_son)
        self.t_son = simdi
        px, py = kok.winfo_pointerxy()
        x, y = px - cv.winfo_rootx(), py - cv.winfo_rooty()
        icinde = self._gorunur(x, y)
        hareketli = False

        if icinde:
            if self.son is not None:
                hareketli = self._yol_boyunca(self.son, (x, y))
                if not hareketli and not self.canli and random.random() < 0.05 * IZ_YOGUNLUK:
                    self._uret(x + random.uniform(-7, 7), y + random.uniform(-7, 7), 0.2)
            self.son = (x, y)
        else:
            self.son = None

        # --- yıldızları ilerlet ---
        sur = 1.0 - min(1.0, 2.4 * dt)
        yasayan = []
        nb = len(self.BOYUTLAR) - 1
        na = len(self.ALFALAR)
        for p in self.canli:
            p.yas += dt
            if p.yas >= p.omur or not self._gorunur(p.x, p.y):
                self._birak(p)
                continue
            p.vx *= sur
            p.vy = p.vy * sur + 60 * dt
            p.x += p.vx * dt
            p.y += p.vy * dt
            tw = 0.5 + 0.5 * math.sin(p.faz + p.yas * 16)
            kal = 1.0 - (p.yas / p.omur)
            bi = int(round(p.boyut * (kal ** 0.6) * (0.78 + 0.22 * tw) * nb))
            ai = min(na - 1, int((1.0 - (kal ** 0.8) * (0.82 + 0.18 * tw)) * na))
            anahtar = (p.renk, bi, p.tip, ai)
            try:
                if anahtar != p.anahtar:
                    spr = self._sprite(*anahtar)
                    cv.itemconfigure(p.oge, image=spr, state="disabled")
                    p.anahtar = anahtar
                cv.coords(p.oge, round(p.x), round(p.y))
                yasayan.append(p)
            except (tk.TclError, RuntimeError):
                pass
        self.canli = yasayan

        # --- gecikmeli ışık halesi ---
        hale_hareketli = False
        if self.hale is not None:
            if icinde:
                if self.hxy is None:
                    self.hxy = [x, y]
                else:
                    k = 1.0 - math.exp(-dt * 14)             # kare hızından bağımsız yumuşatma
                    self.hxy[0] += (x - self.hxy[0]) * k
                    self.hxy[1] += (y - self.hxy[1]) * k
                hx, hy = round(self.hxy[0]), round(self.hxy[1])
                if (hx, hy) != self.hale_cizili:
                    cv.coords(self.hale, hx, hy)
                    self.hale_cizili = (hx, hy)
                    hale_hareketli = abs(x - hx) + abs(y - hy) > 1
                if not self.hale_gorunur:
                    cv.itemconfigure(self.hale, state="disabled")
                    self.hale_gorunur = True
            elif self.hale_gorunur:
                cv.itemconfigure(self.hale, state="hidden")
                self.hale_gorunur = False
                self.hxy = None

        return IZ_KARE_MS if (self.canli or hareketli or hale_hareketli) else IZ_BOSTA_MS

    def _tikla(self, olay):
        if not self.aktif:
            return
        try:
            x = olay.x_root - self.cv.winfo_rootx()
            y = olay.y_root - self.cv.winfo_rooty()
        except tk.TclError:
            return
        if self._gorunur(x, y):
            for _ in range(max(1, int(12 * IZ_YOGUNLUK))):
                self._uret(x, y, 1.0, guc=2.6)

    def durdur(self):
        self.aktif = False
        if self._after is not None:
            try:
                self.kok.after_cancel(self._after)
            except tk.TclError:
                pass
            self._after = None


class ImzaArayuz:
    def __init__(self):
        self.dosyalar = []
        self.pin = None
        self.token_tipi = next(iter(DLL_SECENEKLERI))
        self.sayfalar = None
        self._resimler = []
        self._fontlar = []
        self.mesgul = False            # imzalama sürerken True
        self._iptal = False
        self._kapat_istendi = False
        self.iz = None

        self.root = tk.Tk()
        self.root.withdraw()
        self.root.title("Toplu PDF E-İmza")

        def _hata_goster(tur, deger, tb):
            metin = "".join(traceback.format_exception(tur, deger, tb))
            hata_yaz("Arayüz hatası", metin)
            try:
                messagebox.showerror("Hata", metin[-1500:], parent=self.root)
            except Exception:
                pass
        self.root.report_callback_exception = _hata_goster

        ekran_g, ekran_y = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        self.K = max(0.5, min(PENCERE_OLCEK, (ekran_y - 90) / DH, (ekran_g - 40) / DW))
        self.W, self.H = round(DW * self.K), round(DH * self.K)

        imlecleri_hazirla(self.root)
        imlec_animasyonunu_baslat(self.root)
        self.root.overrideredirect(True)
        self.root.configure(bg=KEY, cursor=IMLEC["ok"])
        try:
            self.root.attributes("-transparentcolor", KEY)
        except tk.TclError:
            pass
        x = max(0, (ekran_g - self.W) // 2)
        y = max(0, (ekran_y - self.H) // 2 - 20)
        self.root.geometry(f"{self.W}x{self.H}+{x}+{y}")

        self.cv = tk.Canvas(self.root, width=self.W, height=self.H, bg=KEY,
                            bd=0, highlightthickness=0, cursor=IMLEC["ok"])
        self.cv.pack()

        self._arayuzu_kur()

        self.root.deiconify()
        self.root.update_idletasks()
        self._gorev_cubugunda_goster()
        self._dosya_birak_kur()
        self.root.protocol("WM_DELETE_WINDOW", self._kapat)
        if IZ_AKTIF:
            try:
                self.iz = YildizIzi(self.root, self.cv, self.K, self.W, self.H, self._w(PENCERE_YARICAP))
            except Exception:
                hata_yaz("Yıldız izi başlatılamadı", traceback.format_exc())

    # ------------------------- yardımcılar -------------------------
    def _x(self, v):
        return round((v - OX) * self.K)

    def _y(self, v):
        return round((v - OY) * self.K)

    def _w(self, v):
        return max(1, round(v * self.K))

    def _foto(self, pil):
        ph = ImageTk.PhotoImage(pil)
        self._resimler.append(ph)
        return ph

    def _font(self, px, kalin=False):
        f = tkfont.Font(family=YAZI_FONT, size=-max(8, round(px * self.K)),
                        weight="bold" if kalin else "normal")
        self._fontlar.append(f)
        return f

    def _yaz(self, x, y, metin, px, renk, kalin=False, anchor="w", tags=(), state="normal"):
        return self.cv.create_text(self._x(x), self._y(y), text=metin, font=self._font(px, kalin),
                                   fill=renk, anchor=anchor, tags=tags, state=state)

    def _nesne(self, etiket, px, py, normal_pil, hover_pil, komut, tags=(), state="normal"):
        """Tıklanabilir canvas nesnesi: normal/hover görüntüsü ve tıklama komutu."""
        normal, hover = self._foto(normal_pil), self._foto(hover_pil)
        cv = self.cv
        oge = cv.create_image(px, py, image=normal, anchor="nw", tags=(etiket,) + tuple(tags), state=state)

        def giris(_):
            cv.itemconfigure(oge, image=hover)
            cv.configure(cursor=IMLEC["el"])

        def cikis(_):
            cv.itemconfigure(oge, image=normal)
            cv.configure(cursor=IMLEC["ok"])

        if komut:
            cv.tag_bind(etiket, "<Enter>", giris)
            cv.tag_bind(etiket, "<Leave>", cikis)
            basili = [False]

            def bas(_):
                basili[0] = True

            def birak(e):
                # yalnızca düğmenin üstünde basılıp yine üstünde bırakılırsa çalışır
                # (sürüklerken yanlışlıkla kapatma / başlatma olmaz)
                if not basili[0]:
                    return
                basili[0] = False
                kutu = cv.bbox(oge)
                if kutu and kutu[0] <= e.x < kutu[2] and kutu[1] <= e.y < kutu[3]:
                    komut()

            cv.tag_bind(etiket, "<ButtonPress-1>", bas)
            cv.tag_bind(etiket, "<ButtonRelease-1>", birak)
        return oge

    def _alan(self, etiket, kutu, komut, yaricap=14, mod="parlat", renk=None, kenar=None, tags=()):
        """Arka plandaki bir bölgeye görünmez tıklama alanı + hover efekti ekler."""
        px0, py0, px1, py1 = self._x(kutu[0]), self._y(kutu[1]), self._x(kutu[2]), self._y(kutu[3])
        w, h = px1 - px0, py1 - py0
        bos = Image.new("RGBA", (w, h), (0, 0, 0, 0))
        if mod == "parlat":
            hv = _parlat(self._taban.crop((px0, py0, px1, py1)), 0.15)
            hv.putalpha(yuvarlak_maske(w, h, self._w(yaricap)))
        else:
            ss = 3
            hv = Image.new("RGBA", (w * ss, h * ss), (0, 0, 0, 0))
            ImageDraw.Draw(hv).rounded_rectangle(
                (0, 0, w * ss - 1, h * ss - 1), radius=int(self._w(yaricap) * ss), fill=renk,
                outline=kenar, width=max(1, ss))
            hv = hv.resize((w, h), Image.LANCZOS)
        return self._nesne(etiket, px0, py0, bos, hv, komut, tags=tags)

    def _chip(self, etiket, x, y, w, h, metin, komut, ikon=None):
        """Liste modunda kart başlığında görünen küçük buton; metin nesnesinin kimliğini döndürür."""
        pil = dugme_gorseli(self.K, w, h, 10, "#1e3a8a", "#172554", "#3b82f6", ikon=ikon)
        self._nesne(etiket, self._x(x), self._y(y), pil, _parlat(pil), komut,
                    tags=("dolu",), state="hidden")
        if ikon:
            return self._yaz(x + 16, y + h / 2, metin, 15, "#eaf2ff", kalin=True, anchor="w",
                             tags=(etiket, "dolu"), state="hidden")
        return self._yaz(x + w / 2, y + h / 2, metin, 15, "#eaf2ff", kalin=True, anchor="center",
                         tags=(etiket, "dolu"), state="hidden")

    # ------------------------- arayüzü kur -------------------------
    def _arayuzu_kur(self):
        K, cv = self.K, self.cv

        # --- arka plan: gömülü tasarım görseli, yuvarlatılmış pencere köşeleriyle ---
        taban = arkaplan_gorseli().resize((self.W, self.H), Image.LANCZOS)
        taban.putalpha(yuvarlak_maske(self.W, self.H, self._w(PENCERE_YARICAP)))
        self._taban = taban
        cv.create_image(0, 0, image=self._foto(taban), anchor="nw")

        # --- pencere düğmeleri (görsel arka planda; burada yalnızca hover + tıklama) ---
        self._alan("b_kucult", R_KUCULT, self._kucult, 12, "renk", (255, 255, 255, 40), (255, 255, 255, 70))
        self._alan("b_buyut", R_BUYUT, None, 12, "renk", (255, 255, 255, 0), (255, 255, 255, 0))
        self._alan("b_kapat_x", R_KAPAT, self._kapat, 12, "renk", (239, 68, 68, 120), (252, 165, 165, 160))

        # --- kenar çubuğu ---
        self._alan("b_ayarlar", R_YAN["b_ayarlar"], self._ayarlar_menusu, 14, "renk",
                   (59, 130, 246, 46), (96, 165, 250, 100))
        self._alan("b_hakkinda", R_YAN["b_hakkinda"], self.hakkinda, 14, "renk",
                   (59, 130, 246, 46), (96, 165, 250, 100))
        self._alan("b_yardim", R_YAN["b_yardim"], self.yardim, 14, "renk",
                   (59, 130, 246, 46), (96, 165, 250, 100))

        # --- sürükle-bırak alanı: boş durumun üstüne gelen "liste yaması" ---
        yama, yx, yy = self._liste_yamasi()
        self._yama_ph = self._foto(yama)
        cv.create_image(yx, yy, image=self._yama_ph, anchor="nw", tags=("dolu",), state="hidden")

        # "Dosya Seç" (yalnızca boş durumda)
        self._alan("b_sec", R_DOSYA_SEC, self.pdf_sec, 24, "parlat", tags=("bos",))

        # --- dosya listesi ---
        self.liste_cerceve = tk.Frame(self.root, bg=LISTE_ZEMIN)
        self.liste = tk.Listbox(
            self.liste_cerceve, bg=LISTE_ZEMIN, fg="#e6eeff", selectbackground="#1e40af",
            selectforeground="white", font=(YAZI_FONT, max(9, round(18 * K * 0.85))),
            relief="flat", bd=0, highlightthickness=0, activestyle="none",
            selectmode="extended", cursor=IMLEC["ok"],
        )
        self.kaydirma = tk.Canvas(self.liste_cerceve, width=10, bg=LISTE_ZEMIN, bd=0,
                                  highlightthickness=0, cursor=IMLEC["ok"])
        self.kaydirma.pack(side="right", fill="y", padx=(0, 4), pady=4)
        self.liste.pack(side="left", fill="both", expand=True, padx=(10, 0), pady=4)
        self._kaydirma_son = (0.0, 1.0)
        self.liste.config(yscrollcommand=self._kaydirma_guncelle)
        self.kaydirma.bind("<Configure>", lambda e: self._kaydirma_guncelle(*self._kaydirma_son))
        self.kaydirma.bind("<Button-1>", self._kaydirma_tikla)
        self.kaydirma.bind("<B1-Motion>", self._kaydirma_tikla)
        self.liste.bind("<Delete>", self._secilileri_sil)
        self.liste.bind("<Double-Button-1>", self._dosya_cift_tikla)
        self.liste.bind("<Button-3>", self._dosya_sag_tik)
        self.liste_penceresi = cv.create_window(
            self._x(R_LISTE[0]), self._y(R_LISTE[1]), window=self.liste_cerceve, anchor="nw",
            width=self._w(R_LISTE[2] - R_LISTE[0]), height=self._w(R_LISTE[3] - R_LISTE[1]),
            tags=("dolu",), state="hidden")

        # --- kart başlığındaki liste araçları (yalnızca dosya varken) ---
        self.t_sayac = self._yaz(516, 447, "", 17, "#7fa6ff", kalin=True, tags=("dolu",), state="hidden")
        self._chip("b_ekle", 606, 430, 118, 34, "Dosya Ekle", self.pdf_sec)
        self.t_sayfa = self._chip("b_sayfa", 734, 430, 188, 34, "Sayfalar: Tümü", self._sayfa_menusu,
                                  ikon=lambda c: ik_asagi(c, 188 - 20, 17))
        self._chip("b_temizle", 932, 430, 98, 34, "Temizle", self.listeyi_temizle)

        # --- imza bilgileri (arka planda kutular boş; gerçek giriş alanları üstte) ---
        ad = IMZALAYAN_AD
        self.e_ad = self._giris(R_AD, ad)
        self.e_sol = self._giris(R_SOL, SOL_METIN)
        self.e_sag = self._metin_kutusu(R_SAG, SAG_METIN)
        self.e_ad.bind("<KeyRelease>", self._ad_degisti)
        self.e_sol.bind("<KeyRelease>", lambda e: self._onizleme_guncelle())
        self.e_sag.bind("<KeyRelease>", lambda e: self._onizleme_guncelle())

        # --- Canlı İmza Önizleme Butonu & Popup Kartı ---
        self._onizleme_butonu_kur()

        # --- DLL seçenekleri ---
        self._alan("b_dll", R_DLL, self._dll_menusu, 10, "renk", (59, 130, 246, 30), (96, 165, 250, 80))
        self.t_dll = self._yaz(1162, 789, self.token_tipi, 18, "#ffffff", tags=("b_dll",))

        # --- imzalamayı başlat ---
        self._alan("b_baslat", R_BASLAT, self.baslat, 26, "parlat")

        # --- Neon İlerleme Barı (Progress Bar) ---
        self._ilerleme_bari_kur()

        cv.bind("<ButtonPress-1>", self._surukle_basla, add="+")
        cv.bind("<B1-Motion>", self._surukle, add="+")

        self._kapat_dugmesi_kur()
        self._imza_yazisi_kur()

        self._liste_yenile()

    # ------------------------- kapat düğmesi + efektli geliştirici yazısı -------------------------
    def _kapat_dugmesi_kur(self):
        """Sol menüde, Yardım'ın altında belirgin bir 'Kapat' düğmesi."""
        w, h = 187, 56

        def ikon(c):
            cx, cy = 44, h / 2
            c.L([(cx - 7, cy - 7), (cx + 7, cy + 7)], 2.8, "#fecaca")
            c.L([(cx - 7, cy + 7), (cx + 7, cy - 7)], 2.8, "#fecaca")
            c.yazi(cx + 22, cy, "Kapat", 19, "#ffffff", anchor="lm")

        pil = dugme_gorseli(self.K, w, h, 14, "#7f1d1d", "#450a0a", "#ef4444", ikon=ikon)
        self._nesne("b_kapat", self._x(42), self._y(507), pil, _parlat(pil, 0.18), self._kapat)

    def _imza_yazisi_kur(self):
        """'Geliştirici: Batuhan Maraşlı | 2026' yazısı: harf harf ilerleyen ışık dalgası + yıldız parıltısı."""
        self._yz_metin = "© 2026 Batuhan Maraşlı | E-Tuğra / TürkTrust"
        f = self._font(26, kalin=True)
        toplam = f.measure(self._yz_metin)
        x0 = self._x(955) - toplam / 2
        y = self._y(90)
        self._yz_taban, self._yz_tepe = "#e0f2fe", "#fde047"
        self._yz_renkler = [_renk_karistir(self._yz_taban, self._yz_tepe, i / 10) for i in range(11)]
        # koyu, yarı saydam zemin: yazı arka plandaki dalgalı çizgilerin üstünde de net okunur
        ph_w, ph_h = toplam / self.K + 36, 36
        c = Cizim(ph_w, ph_h, self.K)
        c.rrect((0, 0, ph_w, ph_h), 18, fill=(3, 8, 26, 215))
        c.rrect((0, 0, ph_w, ph_h), 18, outline=(96, 165, 250, 150), ow=1.6)
        self.cv.create_image(round(x0 - 18 * self.K), round(y - ph_h * self.K / 2),
                             image=self._foto(c.bitir()), anchor="nw", state="disabled")
        self._yz_ogeler, self._yz_seviye = [], []
        for i, ch in enumerate(self._yz_metin):
            px = x0 + f.measure(self._yz_metin[:i])
            self._yz_ogeler.append(self.cv.create_text(px, y, text=ch, font=f, fill=self._yz_renkler[0],
                                                       anchor="w", state="disabled"))
            self._yz_seviye.append(0)
        self._yz_x0, self._yz_y, self._yz_f = x0, y, f
        self._yz_t0 = time.perf_counter()
        self._yz_son_parilti = 0.0
        self.root.after(60, self._imza_yazisi_adim)

    def _imza_yazisi_adim(self):
        try:
            if not self.root.winfo_viewable():
                self.root.after(300, self._imza_yazisi_adim)
                return
            n = len(self._yz_ogeler)
            donem = 3.4                                           # bir turun süresi (sn)
            t = (time.perf_counter() - self._yz_t0) % donem
            poz = t / donem * (n + 14) - 7                        # ışığın harf konumu (ekran dışından girer/çıkar)
            for i, oge in enumerate(self._yz_ogeler):
                u = max(0.0, 1.0 - abs(i - poz) / 5.0)             # tepe etrafında yumuşak düşüş
                u = u * u * (3 - 2 * u)
                sev = int(u * 10 + 0.5)
                if sev != self._yz_seviye[i]:
                    self._yz_seviye[i] = sev
                    self.cv.itemconfigure(oge, fill=self._yz_renkler[sev])
            # ışık tepesi harfin üstünden geçerken küçük yıldızlar saç
            simdi = time.perf_counter()
            if self.iz and 0 <= poz < n and simdi - self._yz_son_parilti > 0.11:
                self._yz_son_parilti = simdi
                px = self._yz_x0 + self._yz_f.measure(self._yz_metin[:int(poz)])
                self.iz._uret(px + random.uniform(-4, 4), self._yz_y + random.uniform(-9, 9), 0.4)
            self.root.after(40, self._imza_yazisi_adim)
        except tk.TclError:
            return                                                 # pencere kapandı
        except Exception:
            hata_yaz("Geliştirici yazısı", traceback.format_exc())
            # Hata sonrası animasyonu durdurmak yerine kısa gecikmeyle sürdür
            try:
                self.root.after(500, self._imza_yazisi_adim)
            except tk.TclError:
                pass

    def _liste_yamasi(self):
        """Boş durum (ikon, yazılar, buton) üstünü kapatan düz zemin; dikey tonu arka plandan alınır."""
        x0, y0, x1, y1 = R_BIRAK
        px0, py0, px1, py1 = self._x(x0), self._y(y0), self._x(x1), self._y(y1)
        w, h = px1 - px0, py1 - py0
        serit = self._taban.crop((self._x(330), py0, self._x(340), py1)).convert("RGB").resize((1, h), Image.BOX)
        yama = serit.resize((w, h), Image.NEAREST).convert("RGBA")
        yama.putalpha(yuvarlak_maske(w, h, self._w(10)))
        return yama, px0, py0

    # ------------------------- giriş alanları -------------------------
    def _giris(self, kutu, metin):
        x0, y0, x1, y1 = kutu
        e = tk.Entry(self.root, font=self._font(17), bg=FORM_ZEMIN, fg="#ffffff",
                     insertbackground="#ffffff", selectbackground="#1e40af", selectforeground="white",
                     relief="flat", bd=0, highlightthickness=0, cursor=IMLEC["yazi"])
        e.insert(0, metin)
        self.cv.create_window(self._x(x0 + 14), self._y(y0 + 4), window=e, anchor="nw",
                              width=self._w(x1 - x0 - 18), height=self._w(y1 - y0 - 8))
        return e

    def _metin_kutusu(self, kutu, metin):
        x0, y0, x1, y1 = kutu
        t = tk.Text(self.root, font=self._font(17), bg=FORM_ZEMIN, fg="#ffffff", wrap="word",
                    insertbackground="#ffffff", selectbackground="#1e40af", selectforeground="white",
                    relief="flat", bd=0, highlightthickness=0, padx=0, pady=self._w(4),
                    cursor=IMLEC["yazi"], undo=True)
        t.insert("1.0", metin)
        t.bind("<Return>", lambda e: "break")
        self.cv.create_window(self._x(x0 + 14), self._y(y0 + 4), window=t, anchor="nw",
                              width=self._w(x1 - x0 - 18), height=self._w(y1 - y0 - 8))
        return t

    def _ad_degisti(self, _=None):
        """İmzalayan adı değişince sol/sağ metin varsayılan biçimde güncellenir."""
        ad = self.e_ad.get().strip()
        self.e_sol.delete(0, "end")
        self.e_sol.insert(0, ad)
        self.e_sag.delete("1.0", "end")
        self.e_sag.insert("1.0", f"Dijital olarak imzalayan {ad}".strip())
        self._onizleme_guncelle()

    def _onizleme_butonu_kur(self):
        """DLL ve ayar yazılarına basmayan, sağa hizalı şık 'İmzayı Önizle' butonu."""
        bx = 1320
        by = 730
        bw, bh = 145, 34
        pil = dugme_gorseli(self.K, bw, bh, 8, "#1e3a8a", "#0f172a", "#3b82f6")
        self._nesne("b_onizle", self._x(bx), self._y(by), pil, _parlat(pil), self.imza_onizleme_penceresi)
        self._yaz(bx + bw / 2, by + bh / 2, "👁 Damga Önizle", 13, "#e0f2fe", kalin=True, anchor="center", tags=("b_onizle",))

    def imza_onizleme_penceresi(self):
        """Orijinal arka plana taşmadan bağımsız açılan şık neon önizleme penceresi."""
        d = tk.Toplevel(self.root)
        d.title("İmza Damgası Önizleme")
        d.configure(bg="#091128")
        d.resizable(False, False)
        d.attributes("-topmost", True)

        sol = self.e_sol.get().strip() or SOL_METIN
        sag = self._sag_metin() or SAG_METIN
        img = imza_gorseli_olustur(sol, sag)
        
        # Orijinal kutu ebatlarında göster
        w, h = 380, 140
        kucuk = img.resize((w, h), Image.LANCZOS)
        self._popup_ph = ImageTk.PhotoImage(kucuk)

        tk.Label(d, text="PDF ÜZERİNE BASILACAK DAMGA GÖRÜNÜMÜ", font=("Segoe UI", 10, "bold"),
                 bg="#091128", fg="#93c5fd").pack(pady=(16, 8))

        cerceve = tk.Frame(d, bg="#ffffff", bd=0, highlightthickness=2, highlightbackground="#3b82f6")
        cerceve.pack(padx=20, pady=10)
        lbl = tk.Label(cerceve, image=self._popup_ph, bg="#ffffff", bd=0)
        lbl.pack()

        tk.Button(d, text="Kapat", command=d.destroy, font=("Segoe UI", 10, "bold"),
                  bg="#1e3a8a", fg="#ffffff", activebackground="#2563eb", activeforeground="#ffffff",
                  relief="flat", bd=0, padx=24, pady=6, cursor="hand2").pack(pady=(10, 16))

        d.update_idletasks()
        x = self.root.winfo_x() + (self.root.winfo_width() - d.winfo_reqwidth()) // 2
        y = self.root.winfo_y() + (self.root.winfo_height() - d.winfo_reqheight()) // 2
        d.geometry(f"+{max(0, x)}+{max(0, y)}")
        _koyu_baslik_uygula(d)

    def _onizleme_guncelle(self):
        pass

    def _ilerleme_bari_kur(self):
        """Alt kısımda modern neon parlayan ilerleme çubuğu."""
        bw, bh = self._w(515), self._w(12)
        bx, by = self._x(295), self._y(954)
        self.pbar_bg = self.cv.create_rectangle(bx, by, bx + bw, by + bh, fill="#040c21", outline="#1e3a8a", width=1)
        self.pbar_fill = self.cv.create_rectangle(bx, by, bx, by + bh, fill="#3b82f6", outline="")
        self.pbar_txt = self.cv.create_text(bx + bw // 2, by - self._w(10), text="", font=self._font(13, True), fill="#93c5fd", anchor="center")
        self._pbar_bx = bx
        self._pbar_by = by
        self._pbar_bw = bw
        self._pbar_bh = bh

    def _pbar_guncelle(self, n, toplam):
        if toplam <= 0:
            return
        oran = max(0.0, min(1.0, n / toplam))
        w = round(self._pbar_bw * oran)
        self.cv.coords(self.pbar_fill, self._pbar_bx, self._pbar_by, self._pbar_bx + w, self._pbar_by + self._pbar_bh)
        yuzde = int(oran * 100)
        self.cv.itemconfig(self.pbar_txt, text=f"⚡ İmzalanıyor: {n}/{toplam} Belge (%{yuzde})")
        try:
            self.root.update_idletasks()
        except tk.TclError:
            pass

    def _dosya_cift_tikla(self, event=None):
        """Listede çift tıklanan PDF dosyasını varsayılan okuyucu ile açar."""
        secilenler = self.liste.curselection()
        if not secilenler:
            return
        idx = secilenler[0]
        if 0 <= idx < len(self.dosyalar):
            yol = self.dosyalar[idx]
            cikis = os.path.join(os.path.dirname(yol), "E_" + os.path.basename(yol))
            hedef = cikis if os.path.exists(cikis) else yol
            try:
                os.startfile(hedef)
            except Exception as e:
                messagebox.showerror("Hata", f"Dosya açılamadı:\n{e}", parent=self.root)

    def _dosya_sag_tik(self, event):
        """Listede sağ tıklanan dosya için menü: Aç, Klasörde Göster, Sil."""
        idx = self.liste.nearest(event.y)
        if idx < 0 or idx >= len(self.dosyalar):
            return
        self.liste.selection_clear(0, "end")
        self.liste.selection_set(idx)
        yol = self.dosyalar[idx]
        cikis = os.path.join(os.path.dirname(yol), "E_" + os.path.basename(yol))

        menu = self._menu()
        menu.add_command(label="📄 Belgeyi Aç", command=self._dosya_cift_tikla)
        if os.path.exists(cikis):
            menu.add_command(label="✅ İmzalı Belgeyi Aç", command=lambda: os.startfile(cikis))
        menu.add_command(label="📁 Klasörde Göster", command=lambda: os.system(f'explorer /select,"{os.path.abspath(yol)}"'))
        menu.add_separator()
        menu.add_command(label="🗑 Listeden Çıkar", command=self._secilileri_sil)

        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def _sag_metin(self):
        return " ".join(self.e_sag.get("1.0", "end-1c").split())

    # ------------------------- DLL seçimi -------------------------
    def _menu(self):
        return tk.Menu(self.root, tearoff=0, bg=C_CARD, fg=C_TEXT, activebackground="#1e40af",
                       activeforeground="white", bd=0, relief="flat", font=(YAZI_FONT, 10))

    def _dll_menusu(self):
        menu = self._menu()
        for ad in DLL_SECENEKLERI:
            menu.add_command(label=("✓  " if ad == self.token_tipi else "     ") + ad,
                             command=lambda a=ad: self._dll_sec(a))
        x = self.cv.winfo_rootx() + self._x(R_DLL[0])
        y = self.cv.winfo_rooty() + self._y(R_DLL[3])
        try:
            menu.tk_popup(x, y)
        finally:
            menu.grab_release()

    def _dll_sec(self, ad):
        if ad != self.token_tipi:
            self.token_tipi = ad
            self.pin = None            # farklı token: eski PIN'i kullanma (yanlış PIN token'ı kilitleyebilir)
        self.cv.itemconfigure(self.t_dll, text=ad)

    # ------------------------- kenar çubuğu -------------------------
    def _ayarlar_menusu(self):
        menu = self._menu()
        menu.add_command(label="Token / PIN…", command=self.token_ayarla)
        menu.add_separator()
        menu.add_command(label="Sayfalar: Tümü", command=lambda: self._sayfa_sec(None))
        menu.add_command(label="Sayfalar: Belirli sayfalar…", command=lambda: self._sayfa_sec("ozel"))
        x = self.cv.winfo_rootx() + self._x(R_YAN["b_ayarlar"][2]) - self._w(30)
        y = self.cv.winfo_rooty() + self._y(R_YAN["b_ayarlar"][3])
        try:
            menu.tk_popup(x, y)
        finally:
            menu.grab_release()

    def hakkinda(self):
        messagebox.showinfo(
            "Hakkında",
            "Toplu PDF E-İmza  v5.0\n\n"
            "E-Tuğra / AKİS ve TürkTrust (PKCS#11) ile\n"
            "birden fazla PDF dosyasını tek seferde imzalar.\n\n"
            "© 2026 Batuhan Maraşlı | PDF İmzalama Sistemi",
            parent=self.root)

    def yardim(self):
        messagebox.showinfo(
            "Yardım",
            "1) PDF dosyalarını \"Dosya Seç\" ile ekleyin.\n"
            "2) İmza Bilgileri bölümünden imzalayan adı ve metinleri kontrol edin.\n"
            "3) DLL Seçenekleri'nden token türünü seçin (E-Tuğra / TÜRKTRUST).\n"
            "4) \"Toplu PDF İmzalamaya Başlat\" düğmesine basın ve PIN'inizi girin.\n\n"
            "• Belirli sayfaları imzalamak için dosya eklendikten sonra \"Sayfalar\" düğmesini kullanın.\n"
            "• Listeden dosya çıkarmak için seçip Delete tuşuna basın.\n"
            "• İmzalı dosyalar, kaynak dosyanın yanına \"E_\" önekiyle kaydedilir.",
            parent=self.root)

    # ------------------------- sürükle-bırak (Windows, ek paket gerekmez) -------------------------
    def _dosya_birak_kur(self):
        """Pencereye dosya bırakmayı etkinleştirir. Küçült/geri getir sonrası pencere yeniden
        oluştuğunda tekrar çağrılabilir (zaten bağlı pencereye ikinci kez bağlanmaz)."""
        if sys.platform != "win32":
            return
        try:
            from ctypes import wintypes
            user32, shell32 = ctypes.windll.user32, ctypes.windll.shell32
            if not hasattr(user32, "SetWindowLongPtrW"):        # 32-bit Python: desteklenmez
                return
            WM_DROPFILES, WM_COPYGLOBALDATA, GWLP_WNDPROC = 0x0233, 0x0049, -4

            if not hasattr(self, "_wndproc"):
                LRESULT = ctypes.c_ssize_t
                WNDPROC = ctypes.WINFUNCTYPE(LRESULT, wintypes.HWND, wintypes.UINT,
                                             wintypes.WPARAM, wintypes.LPARAM)
                user32.SetWindowLongPtrW.restype = ctypes.c_void_p
                user32.SetWindowLongPtrW.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_void_p]
                user32.GetWindowLongPtrW.restype = ctypes.c_void_p
                user32.GetWindowLongPtrW.argtypes = [wintypes.HWND, ctypes.c_int]
                user32.CallWindowProcW.restype = LRESULT
                user32.CallWindowProcW.argtypes = [ctypes.c_void_p, wintypes.HWND, wintypes.UINT,
                                                   wintypes.WPARAM, wintypes.LPARAM]
                user32.DefWindowProcW.restype = LRESULT
                user32.DefWindowProcW.argtypes = [wintypes.HWND, wintypes.UINT,
                                                  wintypes.WPARAM, wintypes.LPARAM]
                user32.IsWindow.argtypes = [wintypes.HWND]
                user32.GetParent.restype = wintypes.HWND
                user32.GetParent.argtypes = [wintypes.HWND]
                shell32.DragAcceptFiles.argtypes = [wintypes.HWND, wintypes.BOOL]
                shell32.DragQueryFileW.argtypes = [ctypes.c_void_p, wintypes.UINT, wintypes.LPWSTR, wintypes.UINT]
                shell32.DragQueryFileW.restype = wintypes.UINT
                shell32.DragFinish.argtypes = [ctypes.c_void_p]

                eski = self._eski = {}

                def proc(hwnd, msg, wp, lp):
                    if msg == WM_DROPFILES:
                        yollar = []
                        try:
                            adet = shell32.DragQueryFileW(wp, 0xFFFFFFFF, None, 0)
                            for i in range(adet):
                                uz = shell32.DragQueryFileW(wp, i, None, 0)
                                tampon = ctypes.create_unicode_buffer(uz + 1)
                                shell32.DragQueryFileW(wp, i, tampon, uz + 1)
                                yollar.append(tampon.value)
                        except Exception:
                            hata_yaz("WM_DROPFILES", traceback.format_exc())
                        finally:
                            try:
                                shell32.DragFinish(wp)
                            except Exception:
                                pass
                        if yollar:
                            self.root.after(10, lambda y=yollar: self._dosyalari_ekle(y))
                        return 0
                    onceki = eski.get(hwnd)
                    if onceki:
                        return user32.CallWindowProcW(onceki, hwnd, msg, wp, lp)
                    return user32.DefWindowProcW(hwnd, msg, wp, lp)

                self._wndproc = WNDPROC(proc)            # GC'ye karşı referans tut

            benim = ctypes.cast(self._wndproc, ctypes.c_void_p).value
            kok = self.root.winfo_id()
            for hwnd in {self.cv.winfo_id(), kok, user32.GetParent(kok)}:
                if not hwnd or not user32.IsWindow(hwnd):
                    continue
                if hwnd in self._eski:
                    continue
                cur_proc = user32.GetWindowLongPtrW(hwnd, GWLP_WNDPROC)
                if cur_proc == benim:
                    continue
                onceki = user32.SetWindowLongPtrW(hwnd, GWLP_WNDPROC, benim)
                if not onceki:
                    continue
                self._eski[hwnd] = onceki
                shell32.DragAcceptFiles(hwnd, True)
                try:        # yönetici olarak çalışırken de sürüklemeye izin ver
                    for mesaj in (WM_DROPFILES, WM_COPYGLOBALDATA):
                        user32.ChangeWindowMessageFilterEx(hwnd, mesaj, 1, None)
                except Exception:
                    pass
        except Exception:
            hata_yaz("Sürükle-bırak kurulamadı", traceback.format_exc())   # "Dosya Seç" yine çalışır

    # ------------------------- pencere davranışı -------------------------
    def _gorev_cubugunda_goster(self):
        try:
            GWL_EXSTYLE, WS_EX_APPWINDOW, WS_EX_TOOLWINDOW = -20, 0x00040000, 0x00000080
            hwnd = ctypes.windll.user32.GetParent(self.root.winfo_id())
            stil = ctypes.windll.user32.GetWindowLongW(hwnd, GWL_EXSTYLE)
            stil = (stil & ~WS_EX_TOOLWINDOW) | WS_EX_APPWINDOW
            ctypes.windll.user32.SetWindowLongW(hwnd, GWL_EXSTYLE, stil)
            self.root.withdraw()
            self.root.after(10, self.root.deiconify)
        except Exception:
            pass

    def _kucult(self):
        self.root.overrideredirect(False)
        self.root.iconify()
        self._map_id = self.root.bind("<Map>", self._geri_geldi)

    def _geri_geldi(self, olay):
        # Bazı Windows sürümlerinde <Map> birden fazla widget için tetiklenebilir;
        # yalnızca kök pencere için işlem yap.
        if getattr(olay, "widget", None) is not self.root:
            return
        try:
            self.root.unbind("<Map>", self._map_id)
        except tk.TclError:
            pass
        self.root.after(10, self._cerceveyi_gizle)

    def _cerceveyi_gizle(self):
        self.root.overrideredirect(True)
        self._gorev_cubugunda_goster()
        self.root.after(120, self._dosya_birak_kur)

    def _kapat(self):
        if self.mesgul:
            if messagebox.askyesno("Çıkış", "İmzalama devam ediyor.\nİşlem durdurulup uygulama kapatılsın mı?",
                                   parent=self.root):
                self._iptal = True
                self._kapat_istendi = True      # güvenli noktada (dosya/sayfa arası) kapanır
            return
        if self.iz:
            self.iz.durdur()
        try:
            self.root.destroy()
        except tk.TclError:
            pass

    def _surukle_basla(self, olay):
        try:
            etiketler = self.cv.gettags("current")
        except tk.TclError:
            return
        if any(t.startswith("b_") for t in etiketler):
            self._surukleniyor = False
            return
        self._surukleniyor = olay.y < self._y(BASLIK_ALTI)
        self._sx = olay.x_root - self.root.winfo_x()
        self._sy = olay.y_root - self.root.winfo_y()

    def _surukle(self, olay):
        if getattr(self, "_surukleniyor", False):
            self.root.geometry(f"+{olay.x_root - self._sx}+{olay.y_root - self._sy}")

    # ------------------------- dosya listesi -------------------------
    def _kaydirma_guncelle(self, a, b):
        a, b = float(a), float(b)
        self._kaydirma_son = (a, b)
        k = self.kaydirma
        k.delete("all")
        if b - a >= 0.999:
            return
        h = k.winfo_height()
        y0, y1 = a * h, max(a * h + 24, b * h)
        k.create_rectangle(3, y0, 8, y1, fill="#3b82f6", outline="")

    def _kaydirma_tikla(self, olay):
        a, b = self._kaydirma_son
        h = max(1, self.kaydirma.winfo_height())
        self.liste.yview_moveto(olay.y / h - (b - a) / 2)

    def _secilileri_sil(self, _=None):
        if self.mesgul:
            return
        for i in reversed(self.liste.curselection()):
            del self.dosyalar[i]
        self._liste_yenile()

    def _liste_yenile(self):
        self.liste.delete(0, "end")
        n = len(self.dosyalar)
        if n > 0:
            for yol in self.dosyalar:
                self.liste.insert("end", "  📄  " + os.path.basename(yol))
            self.cv.itemconfigure(self.t_sayac, text=f"{n} dosya")
            self.cv.itemconfigure("bos", state="hidden")
            self.cv.itemconfigure("dolu", state="normal")
        else:
            self.cv.itemconfigure("dolu", state="hidden")
            self.cv.itemconfigure("bos", state="normal")
            self.cv.configure(cursor=IMLEC["ok"])

    def _dosyalari_ekle(self, yollar):
        if self.mesgul:
            return
        eklenen = 0
        for yol in yollar:
            adaylar = []
            if os.path.isdir(yol):
                try:
                    adaylar = [os.path.join(yol, a) for a in sorted(os.listdir(yol))]
                except OSError:
                    adaylar = []
            else:
                adaylar = [yol]
            for a in adaylar:
                if a.lower().endswith(".pdf") and os.path.isfile(a) and a not in self.dosyalar:
                    self.dosyalar.append(a)
                    eklenen += 1
        if eklenen:
            self._liste_yenile()
        elif yollar:
            messagebox.showwarning("Uyarı", "Yalnızca PDF dosyaları eklenebilir.", parent=self.root)

    def pdf_sec(self):
        if self.mesgul:
            return
        secilen = filedialog.askopenfilenames(
            parent=self.root,
            title="PDF Dosyalarını Seç",
            filetypes=[("PDF Dosyaları", "*.pdf")],
        )
        if secilen:
            self._dosyalari_ekle(list(secilen))

    def listeyi_temizle(self):
        if self.mesgul:
            return
        self.dosyalar = []
        self._liste_yenile()

    # ------------------------- token / PIN / sayfalar -------------------------
    def token_ayarla(self):
        sonuc = koyu_diyalog(
            self.root, "Token / PIN",
            f"{self.token_tipi} için PIN'inizi girin.\nPIN yalnızca imzalama oturumu için kullanılır.",
            gizli=True,
        )
        if not sonuc:
            return False
        _, pin = sonuc
        if not pin:
            messagebox.showwarning("Uyarı", "Lütfen geçerli bir PIN giriniz.", parent=self.root)
            return False
        self.pin = pin
        return True

    def _sayfa_menusu(self):
        menu = self._menu()
        menu.add_command(label="Tümü", command=lambda: self._sayfa_sec(None))
        menu.add_command(label="Belirli sayfalar…", command=lambda: self._sayfa_sec("ozel"))
        x = self.cv.winfo_rootx() + self._x(734)
        y = self.cv.winfo_rooty() + self._y(464)
        try:
            menu.tk_popup(x, y)
        finally:
            menu.grab_release()

    def _sayfa_sec(self, mod):
        if mod is None:
            self.sayfalar = None
            self.cv.itemconfigure(self.t_sayfa, text="Sayfalar: Tümü")
            return
        sonuc = koyu_diyalog(
            self.root, "Sayfa seçimi",
            "İmzalanacak sayfaları girin.\nÖrnek:  1-3, 5, 8-10",
            ilk="1",
        )
        if not sonuc or not sonuc[1]:
            return
        try:
            sayfalar = sayfa_metnini_coz(sonuc[1])
        except ValueError as e:
            messagebox.showwarning("Uyarı", str(e), parent=self.root)
            return
        self.sayfalar = sayfalar
        etiket = sonuc[1].replace(" ", "")
        self.cv.itemconfigure(self.t_sayfa, text="Sayfalar: " + (etiket if len(etiket) <= 7 else etiket[:6] + "…"))

    # ------------------------- imzalamayı başlat -------------------------
    _SIMGE = {"bekliyor": "📄", "calisiyor": "⏳", "ok": "✅", "hata": "❌", "atla": "⚠️"}

    def _satir_yaz(self, yol, durum, ek=""):
        """Listedeki dosya satırının durumunu günceller (⏳ sürüyor, ✅ bitti, ❌ hata, ⚠️ atlandı)."""
        try:
            i = self.dosyalar.index(yol)
        except ValueError:
            return
        metin = f"  {self._SIMGE[durum]}  {os.path.basename(yol)}" + (f"   ({ek})" if ek else "")
        self.liste.delete(i)
        self.liste.insert(i, metin)
        self.liste.see(i)
        # root.update() yerine update_idletasks(): yeniden giriş (re-entrant) riskini önler,
        # pencere donmuş görünmez ama beklenmedik kapanma tetiklemez.
        try:
            self.root.update_idletasks()
        except tk.TclError:
            pass

    def _ilerleme(self, n, toplam):
        self.cv.itemconfigure(self.t_sayac, text=f"{n}/{toplam}")
        self._pbar_guncelle(n, toplam)
        try:
            self.root.update_idletasks()
        except tk.TclError:
            pass

    @staticmethod
    def _kisalt(satirlar, en_fazla=15):
        if len(satirlar) <= en_fazla:
            return "\n".join(satirlar)
        return "\n".join(satirlar[:en_fazla]) + f"\n… ve {len(satirlar) - en_fazla} satır daha"

    def baslat(self):
        if self.mesgul:
            return
        try:
            if not self.dosyalar:
                messagebox.showwarning("Uyarı", "Lütfen PDF seçiniz.", parent=self.root)
                return

            ad = self.e_ad.get().strip()
            sol = self.e_sol.get().strip()
            sag = self._sag_metin()
            if not (ad and sol and sag):
                messagebox.showwarning(
                    "Uyarı", "İmzalayan adı, sol metin ve sağ metin boş bırakılamaz.", parent=self.root)
                return

            if not self.pin:
                if not self.token_ayarla():
                    return

            self._imzala(ad, sol, sag)
        except Exception:
            hata_yaz("baslat", traceback.format_exc())
            messagebox.showerror("Hata", traceback.format_exc()[-1500:], parent=self.root)
            self.mesgul = False

    def _imzala(self, ad, sol, sag):
        """İmzalama pencere AÇIKKEN yapılır: uygulama kendiliğinden kaybolmaz, ilerleme listede görünür."""
        global IMZALAYAN_AD, SOL_METIN, SAG_METIN
        IMZALAYAN_AD, SOL_METIN, SAG_METIN = ad, sol, sag      # imza görseli bu değerlerle üretilir

        dosyalar = list(self.dosyalar)
        self.mesgul, self._iptal = True, False
        sonuc = None
        hata_yaz("İZ: imzalama başladı", f"{len(dosyalar)} dosya, token={self.token_tipi}")
        try:
            sonuc = imzalama_yurut(dosyalar, self.pin, self.sayfalar, self.token_tipi, self.root,
                                   self._ilerleme, self._satir_yaz, lambda: self._iptal)
        except pkcs11.exceptions.PinIncorrect:
            self.pin = None            # yanlış PIN'i bir daha denemeyelim: token kilitlenebilir
            messagebox.showerror("Hata", "PIN yanlış! Birkaç yanlış denemede token kilitlenebilir.\n"
                                         "İmzalamayı yeniden başlattığınızda PIN tekrar sorulacak.", parent=self.root)
        except _PIN_DIGER as e:
            self.pin = None
            messagebox.showerror("Hata", f"PIN / token hatası:\n{e}", parent=self.root)
        except Exception as e:
            hata_yaz("İmzalama hatası", traceback.format_exc())
            messagebox.showerror("Hata", f"Token/imza hatası:\n{e}", parent=self.root)
        finally:
            self.mesgul = False
            hata_yaz("İZ: imzalama bitti (token oturumu kapandı)")

        if sonuc is not None:
            basarili, hatali, atlanmis, imzali = sonuc
            self.dosyalar = [d for d in self.dosyalar if d not in imzali]     # imzalananlar listeden çıkar
            self._liste_yenile()
            self.cv.coords(self.pbar_fill, self._pbar_bx, self._pbar_by, self._pbar_bx, self._pbar_by + self._pbar_bh)
            self.cv.itemconfig(self.pbar_txt, text="")
            mesaj = f"{len(basarili)} dosya imzalandı:\n" + self._kisalt(basarili)
            if atlanmis:
                mesaj += "\n\nBoş yer olmadığı için imzalanmayan sayfalar:\n" + self._kisalt(atlanmis)
            if hatali:
                mesaj += "\n\nHatalılar:\n" + self._kisalt(hatali)
            if self._iptal:
                mesaj = "İşlem kullanıcı tarafından durduruldu.\n\n" + mesaj
            hata_yaz("İZ: sonuç penceresi gösteriliyor")
            messagebox.showinfo("Tamamlandı", mesaj, parent=self.root)
            hata_yaz("İZ: sonuç penceresi kapatıldı")
        else:
            self._liste_yenile()

        if self._kapat_istendi:
            self._kapat()
            return
        try:
            self.root.lift()
            self.root.focus_force()
        except tk.TclError:
            pass

    def run(self):
        self.root.mainloop()


# ===================== GÖMÜLÜ ARKA PLAN (tasarım görseli, WebP) =====================
ARKAPLAN_WEBP_B64 = (
    "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"
    "5K7gcQPdbPZPplV7rxLX4BzMBZLtiFyXos61g2jUfP0EguzhImBWB7Kcy82ubsC/6YCNUZ6czHf0fdk8lqai8XB60KsPu/e0yDGvTdGRCfEcov"
    "nmP+cOLKC7ZU+a3/3Rbrq9FKu6+qRCuUAdtP9D8t6uZQ3jseTsNc0Lfrzw3EeDCyF80/kPEsT7/GQjYTaejW09jvoWGweClFIGR3vmlY4tIh5L"
    "gy1C7ita7llzZlH3T828mFs+pI/xz8a/KY9rHf/UHcwVxAKy1hhNJ72rEf0MG7av2Tc3l+e83L6iHLuYWQk4LH+CAuSTSEdpRR9LRBuyIiA+Ps"
    "CMy97pKiEvhY94+Xt38Olhzicyot12plbiyZJwE4cCo5sEt3Mh/idSdu6TF/i7A3nmPFrdOlkJzDUjaQJuEtV0UwGStFfWUz6OF+ncltZl/vea"
    "oLXxSFIKfw/TeGtEaj0g52K5wIeAw9B9O3QG/r2tsiG+fZQ7fEtEF3LuKqcJ1xBf1tuRm2EWal0oIOgmO1J5e2RaNDfuq8V1kYJdvETCJeYOGh"
    "8ph0w8GohofhcA6Vj5lYqs8gkIXBv80hj6sIWu76MGW1ZPbP0ks4yr5bt9rwOES2NXAExWuOeP4Xhqt3vonN92hGw2rm/xrxu9W4g88p/jXPie"
    "uQdoQnjoEeflO3J1cDfJiHws0k3e1BUt9PR6lLoybJsqjKUQIrlT3Bhl2hpnP3acD0On2o6JoyT1qqvi4GQylBcvHiHXSKTNpaRLzSb4fdQlAx"
    "qZLesyrn4A1eSRTI4cASSX5MXXWcKtbRJvFWzQYq/djH0QdM7VrD7YCTEK/0M3RYHn6zEOFct70lwzL+kcvWdpQE1yXsHElcYiFbe3rFT1ffp3"
    "de1hxeorgVXcicfBI9gSu8j862Oc4Td+oiOLOWyFSDSVgNXB85FgfIy/n/LEJh6T5WsA1pqIytepswrGlBjAOPRJAT82OS1eAtFK+AVMk2sx/u"
    "o/RFEikv/7BSPO5Z/UqV64SnJi5x/A601dpi5xN/yVkv2lUfGDryE0uRi65Ph3GVdbJyIXjyGgexErg2Z2tjH+er96/dLypVDjsOLmFkkybMn2"
    "MPpDdFI7rZlaxiTrYjeWUbbVO8Iy6sq1zaINofQMTSlGPjeH9bJSLdJOTVVuNLtnfCqlyMjdiHs5JPyj8/NH7XEstcjLPDQ85Sn8KmjRJ7154b"
    "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"
    "gisnVuDtjhX3YAAAA="
)


# ===================== İMZALAMA İŞİ (arayüzden bağımsız) =====================
class _Durduruldu(Exception):
    pass


# PIN kaynaklı diğer hatalar (kitli token vb.); kütüphane sürümünde yoksa atlanır
_PIN_DIGER = tuple(getattr(pkcs11.exceptions, n) for n in ("PinLocked", "PinExpired", "PinInvalid", "PinLenRange")
                   if hasattr(pkcs11.exceptions, n))


def imzalama_yurut(dosyalar, pin, sayfalar, token_tipi, ana, ilerleme, durum, iptal):
    """Seçilen PDF'leri imzalar. Döner: (basarili, hatali, atlanmis, imzali_yollar).
    ilerleme(n, toplam) ve durum(yol, durum, ek) geri çağrılarıyla arayüze bilgi verir."""
    pkcs11_dll = DLL_SECENEKLERI[token_tipi]
    for yol, ad in ((pkcs11_dll, f"{token_tipi} PKCS#11 kütüphanesi (DLL)"),
                    (FONT_YAZI, "yazı fontu (segoeui/arial)")):
        if not os.path.exists(yol):
            raise FileNotFoundError(f"{ad} bulunamadı:\n{yol}")

    gorsel = imza_gorseli_olustur()
    basarili, hatali, atlanmis, imzali = [], [], [], []

    with open_pkcs11_session(pkcs11_dll, user_pin=pin) as session:
        anahtar = anahtar_bul(session, ana)
        signer = PKCS11Signer(
            session,
            key_id=anahtar[Attribute.ID],
            cert_id=anahtar[Attribute.ID],
            use_raw_mechanism=True,
        )

        toplam = len(dosyalar)
        for sira_dosya, pdf in enumerate(dosyalar, start=1):
            if iptal():
                break
            ad = os.path.basename(pdf)
            cikis = os.path.join(os.path.dirname(pdf), "E_" + ad)
            ilerleme(sira_dosya, toplam)
            durum(pdf, "calisiyor")
            try:
                kutular, atlanan = sayfa_kutulari_hesapla(pdf, sayfalar)
                if not kutular and not atlanan:
                    raise RuntimeError("Seçilen sayfa numaraları bu PDF'de bulunamadı.")
                if atlanan:
                    atlanmis.append(
                        f"{ad}: sayfa {', '.join(map(str, atlanan))}"
                        + (" (hiçbir sayfa imzalanmadı)" if not kutular else "")
                    )
                if not kutular:
                    durum(pdf, "atla")
                    continue   # hiçbir sayfada boş yer yok: dosyaya dokunma
                with open(pdf, "rb") as f:
                    veri = f.read()

                on_ek = f"Imza_BM_{int(time.time())}"
                for sira, (i, kutu) in enumerate(kutular, start=1):
                    if iptal():
                        raise _Durduruldu()
                    durum(pdf, "calisiyor", f"sayfa {sira}/{len(kutular)}")
                    alan_adi = f"{on_ek}_{i + 1}"
                    writer = IncrementalPdfFileWriter(io.BytesIO(veri), strict=False)
                    pdf_signer = signers.PdfSigner(
                        signers.PdfSignatureMetadata(field_name=alan_adi),
                        signer=signer,
                        stamp_style=stil_olustur(gorsel),
                        new_field_spec=fields.SigFieldSpec(
                            sig_field_name=alan_adi,
                            on_page=i,
                            box=kutu,
                        ),
                    )
                    cikti = pdf_signer.sign_pdf(writer, output=io.BytesIO())
                    veri = cikti.getvalue()

                with open(cikis, "wb") as f:
                    f.write(veri)
                basarili.append(f"{os.path.basename(cikis)} ({len(kutular)} sayfa)")
                imzali.append(pdf)
                durum(pdf, "ok")
            except _Durduruldu:
                durum(pdf, "bekliyor")
                break
            except Exception as e:
                hata_yaz(f"İmza hatası: {ad}", traceback.format_exc())
                hatali.append(f"{ad}: {e}")
                durum(pdf, "hata")

    return basarili, hatali, atlanmis, imzali


# ===================== ANA PROGRAM =====================
def main():
    import atexit
    # Çökme tespiti: normal kapanışta silinen bir işaret dosyası. Bir sonraki açılışta hâlâ
    # duruyorsa önceki oturum çökmüş (ya da zorla kapatılmış) demektir.
    isaret = (LOG_YOLU + ".calisiyor") if LOG_YOLU else None
    if isaret:
        if os.path.exists(isaret):
            hata_yaz("İZ: ÖNCEKİ OTURUM BEKLENMEDİK KAPANDI (çökme)")
        try:
            with open(isaret, "w") as f:
                f.write(str(os.getpid()))
        except OSError:
            isaret = None

    def _normal_cikis():
        hata_yaz("İZ: uygulama NORMAL kapandı")
        if isaret:
            try:
                os.remove(isaret)
            except OSError:
                pass

    hata_yaz("İZ: uygulama başladı")
    atexit.register(_normal_cikis)
    ImzaArayuz().run()
    hata_yaz("İZ: mainloop düzgün sonlandı")


if __name__ == "__main__":
    try:
        main()
    except Exception:
        hata_yaz("main", traceback.format_exc())
        try:
            messagebox.showerror(
                "Hata", "Uygulama beklenmedik bir hatayla karşılaştı.\n\nAyrıntılar günlük dosyasında:\n"
                        + str(LOG_YOLU) + "\n\n" + traceback.format_exc()[-800:])
        except Exception:
            pass
