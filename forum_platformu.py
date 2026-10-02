#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
OYLAMALI KONU PLATFORMU - PROTOTİP (yalnızca standart Python kütüphanesi)

Çözülmeye çalışılan asıl problem: ÇOĞUNLUK AZINLIĞI NASIL YUTMAZ?

Ana ilke (asimetri): Çoğunluk neyin KABUL edileceğine karar verebilir ama
neyin SİLİNECEĞİNE ve kimin KONUŞABİLECEĞİNE tek başına karar veremez.

Azınlık koruma mekanizmaları (kodda ilgili yerler [KORUMA-n] ile işaretli):
  1  Karar türüne göre kademeli eşik (basit çoğunluk / 2/3 / 3/4)
  2  Silme yalnızca ontolojideki dar ihlal kategorileriyle açılabilir
  3  Değiştirilemez çekirdek ilkeler (eleştiri/azınlık görüşü asla silinemez)
  4  Reddedilen konu silinmez, arşivde kalır
  5  Muhalefet şerhi (azınlığın gerekçesi kalıcı kayda girer)
  6  Azınlık imzayla kararı bir kez yeniden incelemeye zorlayabilir
  7  Oy yoğunluğu (kuadratik oy): çok önemseyen azınlık daha güçlü oy verebilir
  8  Gizli ara sonuç + minimum oylama süresi + asgari katılım
  9  Bölgesel karar: sadece etkilenen bölge oy verir, ülke geneli ise herkes
 10  Graf analizi: birbirine bağlı hesap kümelerinin oyu azaltılır (sahte çoğunluk)
 11  Bilir kişi: karar vermez, yalnızca geciktirici veto (bir kez)
 12  Yapay zeka: yalnızca danışman, hiçbir şeyi kendisi silmez/engellemez
 13  Hash zincirli defter: sadece ekleme yapılır, gizlice değişiklik fark edilir

Kişisel veri (KVKK mantığı): ad, soyad, doğum tarihi, adres alınır ama HAM HALİYLE
SAKLANMAZ ve hiçbir çıktıda görünmez. Sadece tuzlu hash'ler ve il bilgisi
(bölgesel oy hakkı için gerekli) tutulur. Dışarıya yalnızca takma ad görünür.
"""

import hashlib
import hmac
import itertools
import json
import math
import re
import secrets
from datetime import date
from enum import Enum


# --------------------------------------------------------------------------
# 1) YÖNETMELİK / ONTOLOJİ
# --------------------------------------------------------------------------
# Silme gerekçesi sadece bu kategorilerden biri olabilir.
# "silinebilir": False olanlar ASLA silme oylamasına konamaz.
ONTOLOJI_BASLANGIC = {
    "HAKARET":             {"tanim": "Kişiye yönelik aşağılayıcı ifade", "silinebilir": True},
    "KISISEL_VERI_IFSASI": {"tanim": "Başkasının kişisel verisini yayma", "silinebilir": True},
    "SPAM":                {"tanim": "Tekrarlayan veya reklam amaçlı içerik", "silinebilir": True},
    "NEFRET_SOYLEMI":      {"tanim": "Gruba yönelik nefret söylemi", "silinebilir": True},
    "SIDDETE_TESVIK":      {"tanim": "Şiddeti teşvik eden içerik", "silinebilir": True},
    "ELESTIRI":            {"tanim": "Sert da olsa eleştiri", "silinebilir": False},
    "AZINLIK_GORUSU":      {"tanim": "Azınlıkta kalan görüş", "silinebilir": False},
    "UNPOPULER_GORUS":     {"tanim": "Popüler olmayan görüş", "silinebilir": False},
}
# [KORUMA-3] Bu kategoriler yönetmelik değişikliğiyle bile silinebilir yapılamaz.
KORUNAN_CEKIRDEK = {"ELESTIRI", "AZINLIK_GORUSU", "UNPOPULER_GORUS"}


class Karar(Enum):
    KONU = "konu_kabul"
    ALT_KONU = "alt_konu_kabul"
    DUZENLEME = "duzenleme"
    SILME = "tartisma_silme"
    YONETMELIK = "yonetmelik_degisikligi"


# [KORUMA-1] Karar türüne göre eşik (kabul için "evet oranı" bunu AŞMALI)
ESIK = {Karar.KONU: 0.50, Karar.ALT_KONU: 0.50, Karar.DUZENLEME: 0.50,
        Karar.SILME: 2 / 3, Karar.YONETMELIK: 0.75}
# [KORUMA-8] Asgari katılım (azınlığın boş salonda karar çıkarmasını da önler)
MIN_KATILIM = {Karar.KONU: 0.10, Karar.ALT_KONU: 0.10, Karar.DUZENLEME: 0.10,
               Karar.SILME: 0.20, Karar.YONETMELIK: 0.30}
# [KORUMA-8] Minimum oylama süresi (gün)
MIN_SURE = {Karar.KONU: 1, Karar.ALT_KONU: 1, Karar.DUZENLEME: 1,
            Karar.SILME: 3, Karar.YONETMELIK: 7}


class KuralIhlali(Exception):
    """Sistem kurallarına aykırı işlem."""


class YetkiHatasi(KuralIhlali):
    """Kullanıcının bu işlem/oylama için yetkisi yok."""


# --------------------------------------------------------------------------
# 2) YARDIMCILAR
# --------------------------------------------------------------------------
def norm(s):
    """Türkçe harfleri de doğru küçülten normalleştirme."""
    s = s.replace("İ", "i").replace("I", "ı").lower()
    return re.sub(r"\s+", " ", s).strip()


def sha(metin):
    return hashlib.sha256(metin.encode("utf-8")).hexdigest()


# --------------------------------------------------------------------------
# 3) DAĞITIK DEFTER (hash zincirli, sadece ekleme)  [KORUMA-13]
# --------------------------------------------------------------------------
class Defter:
    """Gerçek blockchain yerine hash zinciri ile simüle edilir.
    Her kayıt bir öncekinin hash'ini taşır; geçmişi değiştirmek zinciri bozar.
    Deftere KİŞİSEL VERİ ASLA yazılmaz."""

    def __init__(self):
        self.kayitlar = []

    @staticmethod
    def _hesapla(no, tur, veri, onceki):
        govde = json.dumps({"no": no, "tur": tur, "veri": veri, "onceki": onceki},
                           sort_keys=True, ensure_ascii=False)
        return sha(govde)

    def ekle(self, tur, veri):
        onceki = self.kayitlar[-1]["hash"] if self.kayitlar else "0" * 64
        no = len(self.kayitlar)
        self.kayitlar.append({"no": no, "tur": tur, "veri": veri, "onceki": onceki,
                              "hash": self._hesapla(no, tur, veri, onceki)})

    def dogrula(self):
        onceki = "0" * 64
        for k in self.kayitlar:
            if k["onceki"] != onceki or k["hash"] != self._hesapla(
                    k["no"], k["tur"], k["veri"], k["onceki"]):
                return False
            onceki = k["hash"]
        return True


# --------------------------------------------------------------------------
# 4) YAPAY ZEKA DANIŞMANI (kural tabanlı simülasyon)  [KORUMA-12]
# --------------------------------------------------------------------------
class YapayZekaDanisman:
    """Sadece İŞARETLER. Silmez, engellemez, karar vermez."""
    HAKARET = {"aptal", "salak", "gerizekalı", "şerefsiz"}

    def incele(self, metin):
        bayrak = []
        kelimeler = re.findall(r"\w+", norm(metin))
        if any(k in self.HAKARET for k in kelimeler):
            bayrak.append("HAKARET")
        if re.search(r"\b\d{11}\b|\b05\d{9}\b|[\w.]+@[\w.]+\.\w+", metin):
            bayrak.append("KISISEL_VERI_IFSASI")
        if metin.lower().count("http") >= 3 or (
                kelimeler and max(kelimeler.count(k) for k in set(kelimeler)) >= 6):
            bayrak.append("SPAM")
        return bayrak


# --------------------------------------------------------------------------
# 5) VERİ MODELLERİ
# --------------------------------------------------------------------------
class Kullanici:
    """Kişisel veriler burada HAM tutulmaz; yazdırıldığında yalnızca takma ad görünür."""

    def __init__(self, kid, takma_ad, kimlik_hash, adres_hash, il, kayit_gunu, kredi):
        self.kid = kid
        self.takma_ad = takma_ad
        self._kimlik_hash = kimlik_hash   # çift hesabı engellemek için
        self._adres_hash = adres_hash     # graf analizi için (geri döndürülemez)
        self._il = il                     # sadece bölgesel oy hakkı için
        self.kayit_gunu = kayit_gunu
        self.uzmanlik = set()
        self.kredi = kredi

    def __repr__(self):
        return f"Kullanici(takma_ad={self.takma_ad!r})"

    __str__ = __repr__


class Oylama:
    def __init__(self, oid, tur, kapsam, hedef, acan, baslangic, alan=None):
        self.id = oid
        self.tur = tur
        self.kapsam = kapsam          # "ULUSAL" veya "IL:<il>"
        self.hedef = hedef            # neyin oylandığı
        self.acan = acan
        self.alan = alan              # bilir kişi alanı
        self.baslangic = baslangic
        self.durum = "ACIK"           # ACIK -> SONUCLANDI -> KESIN
        self.tur_no = 1               # veto / yeniden inceleme ile artar
        self.oylar = {}               # kid -> {"evet","yogunluk","gerekce"}
        self.veto_kullanildi = False
        self.yeniden_inceleme_kullanildi = False
        self.imzalar = set()
        self.sonuc = None
        self.detay = {}
        self.kapanis = None
        self.serhler = []             # [KORUMA-5] muhalefet şerhleri
        self.veto_gerekcesi = None

    @property
    def min_sure(self):
        return MIN_SURE[self.tur]


# --------------------------------------------------------------------------
# 6) PLATFORM
# --------------------------------------------------------------------------
class Platform:
    ITIRAZ_SURESI = 3        # sonuçtan sonra kesinleşmeden önce bekleme (gün)
    IMZA_ORANI = 0.10        # [KORUMA-6] yeniden inceleme için gereken imza oranı
    DONEM_KREDISI = 20       # [KORUMA-7] dönemlik oy kredisi
    KUME_ESIGI = 60          # graf kenarı için benzerlik puanı eşiği

    def __init__(self):
        self.simdi = 0                      # simüle gün sayacı
        self.kullanicilar = {}
        self._kimlikler = set()
        self._takma_adlar = set()
        self.konular = {}
        self.tartismalar = {}
        self.oylamalar = {}
        self.gecmis = {}                    # kid -> {oylama_id: evet?} (graf için)
        self.ontoloji = {k: dict(v) for k, v in ONTOLOJI_BASLANGIC.items()}
        self.defter = Defter()
        self.yz = YapayZekaDanisman()
        self._tuz = secrets.token_hex(16)
        self._sayac = itertools.count(1)

    # ---- kimlik / gizlilik ------------------------------------------------
    def _anon(self, kid, oid):
        """Oylama başına farklı anonim kimlik: oylar birbirine bağlanamaz."""
        return hmac.new(self._tuz.encode(), f"{kid}|{oid}".encode(),
                        hashlib.sha256).hexdigest()[:10]

    def kayit(self, ad, soyad, dogum, il, ilce, acik_adres, takma_ad):
        if not all(str(x).strip() for x in (ad, soyad, il, ilce, acik_adres, takma_ad)):
            raise ValueError("Tüm alanlar zorunludur.")
        yas = (date.today() - dogum).days // 365
        if yas < 18:
            raise KuralIhlali("Kayıt için 18 yaş ve üzeri olmak gerekir.")
        if norm(takma_ad) in self._takma_adlar:
            raise KuralIhlali("Bu takma ad kullanılıyor.")
        kimlik = sha(f"{self._tuz}|{norm(ad)}|{norm(soyad)}|{dogum.isoformat()}")
        if kimlik in self._kimlikler:
            raise KuralIhlali("Bu kişi için zaten bir hesap var (çoklu hesap engeli).")
        adres = sha(f"{self._tuz}|{norm(il)}|{norm(ilce)}|{norm(acik_adres)}")
        kid = next(self._sayac)
        # Ham ad/soyad/doğum/adres burada atılır; sadece hash ve il kalır.
        u = Kullanici(kid, takma_ad, kimlik, adres, norm(il), self.simdi, self.DONEM_KREDISI)
        self.kullanicilar[kid] = u
        self._kimlikler.add(kimlik)
        self._takma_adlar.add(norm(takma_ad))
        self.gecmis[kid] = {}
        self.defter.ekle("KAYIT", {"takma_ad": takma_ad, "gun": self.simdi})
        return u

    def profil(self, kid):
        """Dışarıya açılan tek görünüm: kişisel veri YOK."""
        u = self.kullanicilar[kid]
        return {"takma_ad": u.takma_ad, "kayit_gunu": u.kayit_gunu}

    def uzman_ata(self, kid, alan):
        # Gerçekte: graf tabanlı itibar + dönemlik seçim. Burada doğrudan atanır.
        self.kullanicilar[kid].uzmanlik.add(alan)

    def donem_yenile(self):
        for u in self.kullanicilar.values():
            u.kredi = self.DONEM_KREDISI

    # ---- bölgesel / ulusal oy hakkı --------------------------------------
    @staticmethod
    def _kapsam(il):
        return "ULUSAL" if il is None else f"IL:{norm(il)}"

    @staticmethod
    def _secmen_mi(u, kapsam):
        # [KORUMA-9] Bölgesel karar: sadece o ilin sakinleri. Ulusal: herkes.
        return kapsam == "ULUSAL" or kapsam == f"IL:{u._il}"

    def _secmenler(self, kapsam):
        return [u for u in self.kullanicilar.values() if self._secmen_mi(u, kapsam)]

    # ---- oylama açma ------------------------------------------------------
    def _oylama_ac(self, tur, kapsam, hedef, kid, alan=None):
        oid = next(self._sayac)
        o = Oylama(oid, tur, kapsam, hedef, kid, self.simdi, alan)
        self.oylamalar[oid] = o
        self.defter.ekle("OYLAMA_ACILDI", {"oylama": oid, "tur": tur.value,
                                           "kapsam": kapsam, "hedef": hedef})
        return o

    def konu_ac(self, kid, baslik, aciklama, il=None, alan=None, ust_konu=None):
        """Herkes konu açabilir; konu ancak oylamayla kabul edilirse 'KABUL' olur."""
        if kid not in self.kullanicilar:
            raise KuralIhlali("Kullanıcı yok.")
        tur = Karar.KONU
        if ust_konu is not None:
            if self.konular.get(ust_konu, {}).get("durum") != "KABUL":
                raise KuralIhlali("Alt konu sadece kabul edilmiş konuya önerilebilir.")
            tur = Karar.ALT_KONU
        kapsam = self._kapsam(il)
        kno = next(self._sayac)
        self.konular[kno] = {"id": kno, "baslik": baslik, "kapsam": kapsam, "alan": alan,
                             "durum": "OYLAMADA", "ust": ust_konu,
                             "surumler": [aciklama], "tartismalar": []}
        o = self._oylama_ac(tur, kapsam, {"konu": kno, "baslik": baslik}, kid, alan)
        self.konular[kno]["oylama"] = o.id
        return kno, o.id

    def duzenleme_oner(self, kid, kno, yeni_metin):
        k = self.konular[kno]
        if k["durum"] != "KABUL":
            raise KuralIhlali("Sadece kabul edilmiş konular düzenlenebilir.")
        o = self._oylama_ac(Karar.DUZENLEME, k["kapsam"],
                            {"konu": kno, "yeni_metin_hash": sha(yeni_metin)}, kid, k["alan"])
        o.hedef_metin = yeni_metin
        return o.id

    def yonetmelik_oner(self, kid, kategori, tanim, silinebilir):
        # [KORUMA-3] Çekirdek ilkelere dokunulamaz: çoğunluk kuralı kendisi aşamaz.
        if norm(kategori).upper() in KORUNAN_CEKIRDEK or kategori.upper() in KORUNAN_CEKIRDEK:
            raise KuralIhlali(f"{kategori} değiştirilemez çekirdek ilkedir; oylamaya açılamaz.")
        return self._oylama_ac(Karar.YONETMELIK, "ULUSAL",
                               {"kategori": kategori.upper(), "tanim": tanim,
                                "silinebilir": bool(silinebilir)}, kid).id

    # ---- tartışma ---------------------------------------------------------
    def tartisma_yaz(self, kid, kno, metin):
        """Tartışmalar kalıcıdır. YZ sadece işaret koyar, engellemez [KORUMA-12]."""
        u = self.kullanicilar[kid]
        tid = next(self._sayac)
        bayrak = self.yz.incele(metin)
        self.tartismalar[tid] = {"id": tid, "konu": kno, "yazar": u.takma_ad,
                                 "metin": metin, "gizli": None, "yz": bayrak}
        self.konular[kno]["tartismalar"].append(tid)
        self.defter.ekle("TARTISMA", {"id": tid, "konu": kno, "yazar": u.takma_ad,
                                      "icerik_hash": sha(metin), "yz_isaret": bayrak})
        return tid

    def silme_oner(self, kid, tid, kategori, gerekce):
        """[KORUMA-2] 'Bu görüş popüler değil' gerekçesiyle silme oylaması açılamaz."""
        kategori = kategori.upper()
        if kategori not in self.ontoloji:
            raise KuralIhlali("Silme gerekçesi yönetmelikte tanımlı bir kategori olmalı.")
        if not self.ontoloji[kategori]["silinebilir"]:
            raise KuralIhlali(f"'{kategori}' kategorisi silme gerekçesi olamaz; "
                              "popüler olmayan/eleştirel görüş korunur.")
        t = self.tartismalar[tid]
        k = self.konular[t["konu"]]
        o = self._oylama_ac(Karar.SILME, k["kapsam"],
                            {"tartisma": tid, "kategori": kategori, "gerekce": gerekce,
                             "yz_gorusu": t["yz"]}, kid, k["alan"])
        return o.id

    def tartisma_goster(self, kno):
        for tid in self.konular[kno]["tartismalar"]:
            t = self.tartismalar[tid]
            if t["gizli"]:
                print(f"   #{tid} [{t['yazar']}] [içerik gizlendi: {t['gizli']}; "
                      f"kayıt defterde duruyor]")
            else:
                print(f"   #{tid} [{t['yazar']}] {t['metin']}")

    # ---- oylama -----------------------------------------------------------
    def oy_ver(self, kid, oid, evet, yogunluk=1, gerekce=""):
        u, o = self.kullanicilar[kid], self.oylamalar[oid]
        if o.durum != "ACIK":
            raise KuralIhlali("Oylama açık değil.")
        if not self._secmen_mi(u, o.kapsam):
            raise YetkiHatasi(f"{u.takma_ad} bu oylamada oy kullanamaz "
                              f"(oylama kapsamı: {o.kapsam}).")
        if kid in o.oylar:
            raise KuralIhlali("Zaten oy kullandınız.")
        if yogunluk not in (1, 2, 3):
            raise ValueError("Yoğunluk 1, 2 veya 3 olmalıdır.")
        maliyet = yogunluk ** 2        # [KORUMA-7] kuadratik maliyet
        if u.kredi < maliyet:
            raise KuralIhlali("Yeterli oy krediniz yok.")
        u.kredi -= maliyet
        o.oylar[kid] = {"evet": evet, "yogunluk": yogunluk, "gerekce": gerekce,
                        "maliyet": maliyet}

    def ara_sonuc(self, oid):
        # [KORUMA-8] Oylama bitene kadar sonuç görünmez (sürü etkisini kırar).
        if self.oylamalar[oid].durum == "ACIK":
            raise KuralIhlali("Oylama sürerken ara sonuç gösterilmez.")
        return self.oylamalar[oid].detay

    def _oylari_sifirla(self, o):
        for kid, oy in o.oylar.items():
            self.kullanicilar[kid].kredi += oy["maliyet"]   # kredi iade
        o.oylar = {}
        o.imzalar = set()
        o.tur_no += 1
        o.baslangic = self.simdi
        o.durum = "ACIK"

    # ---- graf analizi  [KORUMA-10] ---------------------------------------
    def _benzerlik(self, a, b):
        puan = 0
        if a._adres_hash == b._adres_hash:
            puan += 40
        if abs(a.kayit_gunu - b.kayit_gunu) <= 1:
            puan += 20
        ga, gb = self.gecmis[a.kid], self.gecmis[b.kid]
        ortak = set(ga) & set(gb)
        if len(ortak) >= 3 and sum(ga[x] == gb[x] for x in ortak) / len(ortak) >= 0.95:
            puan += 40
        return puan

    def _kume_agirliklari(self, secmenler, oylayanlar):
        """Bağlı bileşenleri bul; n kişilik kümenin toplam gücü sqrt(n) olur
        (her üyenin ağırlığı 1/sqrt(n)). 50 sahte hesap ≈ 7 oy eder."""
        ebeveyn = {u.kid: u.kid for u in secmenler}

        def bul(x):
            while ebeveyn[x] != x:
                ebeveyn[x] = ebeveyn[ebeveyn[x]]
                x = ebeveyn[x]
            return x

        for i, a in enumerate(secmenler):
            for b in secmenler[i + 1:]:
                if self._benzerlik(a, b) >= self.KUME_ESIGI:
                    ebeveyn[bul(a.kid)] = bul(b.kid)

        gruplar = {}
        for kid in oylayanlar:
            gruplar.setdefault(bul(kid), []).append(kid)
        agirlik, supheli = {}, []
        for uyeler in gruplar.values():
            for kid in uyeler:
                agirlik[kid] = 1 / math.sqrt(len(uyeler))
            if len(uyeler) >= 3:
                supheli.append(len(uyeler))
        return agirlik, supheli

    # ---- sonuçlandırma ----------------------------------------------------
    def kapat(self, oid):
        o = self.oylamalar[oid]
        if o.durum != "ACIK":
            raise KuralIhlali("Oylama zaten kapalı.")
        if self.simdi - o.baslangic < o.min_sure:
            raise KuralIhlali(f"Minimum oylama süresi dolmadı ({o.min_sure} gün).")
        secmenler = self._secmenler(o.kapsam)
        agirlik, supheli = self._kume_agirliklari(secmenler, list(o.oylar))

        evet = hayir = ham_evet = ham_hayir = 0.0
        for kid, oy in o.oylar.items():
            guc = oy["yogunluk"] * agirlik[kid]
            if oy["evet"]:
                evet += guc
                ham_evet += 1
            else:
                hayir += guc
                ham_hayir += 1
        katilim = len(o.oylar) / max(1, len(secmenler))
        oran = evet / (evet + hayir) if (evet + hayir) else 0.0

        if katilim < MIN_KATILIM[o.tur]:
            sonuc = "GECERSIZ_KATILIM_YETERSIZ"
        elif oran > ESIK[o.tur]:
            sonuc = "KABUL"
        else:
            sonuc = "RED"

        # [KORUMA-5] Azınlıkta kalan tarafın gerekçeleri kalıcı olarak kaydedilir.
        kazanan_evet = sonuc == "KABUL"
        o.serhler = [oy["gerekce"] for oy in o.oylar.values()
                     if oy["gerekce"] and oy["evet"] != kazanan_evet]

        o.detay = {"agirlikli_evet": round(evet, 2), "agirlikli_hayir": round(hayir, 2),
                   "ham_evet": int(ham_evet), "ham_hayir": int(ham_hayir),
                   "evet_orani": round(oran, 3), "esik": round(ESIK[o.tur], 3),
                   "katilim": round(katilim, 3), "secmen_sayisi": len(secmenler),
                   "koordinasyon_suphesi_kume": supheli}
        o.sonuc, o.durum, o.kapanis = sonuc, "SONUCLANDI", self.simdi

        for kid, oy in o.oylar.items():
            self.gecmis[kid][oid] = oy["evet"]
        self.defter.ekle("OYLAMA_SONUCU", {
            "oylama": oid, "tur_no": o.tur_no, "sonuc": sonuc, "detay": o.detay,
            "oylar": sorted((self._anon(k, oid), v["evet"], v["yogunluk"])
                            for k, v in o.oylar.items()),
            "muhalefet_serhleri": o.serhler})
        return sonuc

    def veto(self, kid, oid, gerekce):
        """[KORUMA-11] Bilir kişi KARAR VERMEZ; oylamayı bir kez durdurup yeniden oylatır."""
        u, o = self.kullanicilar[kid], self.oylamalar[oid]
        if o.durum != "ACIK":
            raise KuralIhlali("Veto sadece süren oylamada kullanılır.")
        if o.alan is None or o.alan not in u.uzmanlik:
            raise YetkiHatasi("Bu konunun alanında bilir kişi değilsiniz.")
        if o.veto_kullanildi:
            raise KuralIhlali("Bu oylamada veto zaten kullanıldı (tek sefer).")
        if not gerekce.strip():
            raise KuralIhlali("Veto gerekçesi herkese açık yazılmak zorundadır.")
        o.veto_kullanildi, o.veto_gerekcesi = True, gerekce
        self.defter.ekle("VETO", {"oylama": oid, "uzman": u.takma_ad, "gerekce": gerekce})
        self._oylari_sifirla(o)

    def imza_ver(self, kid, oid):
        """[KORUMA-6] Azınlıkta kalanların %10'u imzalarsa karar bir kez yeniden incelenir."""
        o = self.oylamalar[oid]
        if o.durum != "SONUCLANDI":
            raise KuralIhlali("İmza sadece itiraz süresi içindeki sonuçlara verilir.")
        if o.sonuc.startswith("GECERSIZ") or o.yeniden_inceleme_kullanildi:
            raise KuralIhlali("Bu oylama yeniden incelemeye uygun değil.")
        oy = o.oylar.get(kid)
        if oy is None or oy["evet"] == (o.sonuc == "KABUL"):
            raise YetkiHatasi("Sadece azınlıkta kalan taraf imza verebilir.")
        o.imzalar.add(kid)
        gerekli = max(1, math.ceil(self.IMZA_ORANI * len(self._secmenler(o.kapsam))))
        if len(o.imzalar) >= gerekli:
            o.yeniden_inceleme_kullanildi = True
            self.defter.ekle("YENIDEN_INCELEME", {"oylama": oid, "imza": len(o.imzalar)})
            self._oylari_sifirla(o)
            return True
        return False

    def ilerle(self, gun):
        """Zamanı ilerletir; itiraz süresi dolan sonuçlar kesinleşir."""
        self.simdi += gun
        for o in self.oylamalar.values():
            if o.durum == "SONUCLANDI" and self.simdi - o.kapanis >= self.ITIRAZ_SURESI:
                self._uygula(o)

    def _uygula(self, o):
        o.durum = "KESIN"
        kabul = o.sonuc == "KABUL"
        h = o.hedef
        if o.tur in (Karar.KONU, Karar.ALT_KONU):
            # [KORUMA-4] Red de olsa konu ve tartışmaları ARŞİVDE KALIR.
            self.konular[h["konu"]]["durum"] = "KABUL" if kabul else "REDDEDILDI_ARSIV"
        elif kabul and o.tur == Karar.DUZENLEME:
            self.konular[h["konu"]]["surumler"].append(o.hedef_metin)  # eski sürümler durur
        elif kabul and o.tur == Karar.SILME:
            self.tartismalar[h["tartisma"]]["gizli"] = h["kategori"]   # defterde kalır
        elif kabul and o.tur == Karar.YONETMELIK:
            self.ontoloji[h["kategori"]] = {"tanim": h["tanim"], "silinebilir": h["silinebilir"]}
        self.defter.ekle("KESINLESTI", {"oylama": o.id, "sonuc": o.sonuc})

    def ozet(self, oid):
        o = self.oylamalar[oid]
        d = o.detay
        print(f"   Oylama #{oid} ({o.tur.value}, kapsam={o.kapsam}, tur {o.tur_no}) -> {o.sonuc}")
        print(f"   ham oy: {d['ham_evet']} evet / {d['ham_hayir']} hayır | "
              f"ağırlıklı: {d['agirlikli_evet']} evet / {d['agirlikli_hayir']} hayır | "
              f"evet oranı {d['evet_orani']} (eşik {d['esik']}) | katılım {d['katilim']}")
        if d["koordinasyon_suphesi_kume"]:
            print(f"   YZ UYARISI: koordinasyon şüphesi, küme boyutları "
                  f"{d['koordinasyon_suphesi_kume']} (oyları azaltıldı)")
        for s in o.serhler:
            print(f"   Muhalefet şerhi: \"{s}\"")


# --------------------------------------------------------------------------
# 7) DEMO SENARYOLARI
# --------------------------------------------------------------------------
def baslik(s):
    print("\n" + "=" * 74 + f"\n{s}\n" + "=" * 74)


def demo():
    p = Platform()
    dg = date(1995, 3, 14)

    def kayit(ad, il, ilce, adres, takma):
        return p.kayit(ad, "Test", dg, il, ilce, adres, takma)

    # --- kullanıcılar ---
    ankara = []
    for i in range(1, 6):
        ankara.append(kayit(f"A{i}", "Ankara", "Çankaya", f"Sokak {i} No:{i}", f"ankaralı{i}"))
        p.ilerle(2)
    uzman = kayit("Havacı", "Ankara", "Yenimahalle", "Uzman Cd. 9", "havacilik_uzmani")
    p.uzman_ata(uzman.kid, "havacilik")
    p.ilerle(2)
    istanbul = []
    for i in range(1, 11):
        istanbul.append(kayit(f"I{i}", "İstanbul", "Kadıköy", f"Cadde {i} Daire {i}", f"istanbullu{i}"))
        p.ilerle(2)
    p.ilerle(5)
    botlar = [kayit(f"B{i}", "İstanbul", "Esenyurt", "Sahte Sk. No:1", f"bot{i}") for i in range(6)]
    p.ilerle(5)

    baslik("0) GİZLİLİK: kişisel veriler hiçbir yerde görünmez")
    print("   print(kullanici)  ->", ankara[0])
    print("   profil()          ->", p.profil(ankara[0].kid))
    print("   Defter ilk kayıt  ->", p.defter.kayitlar[0]["veri"])
    try:
        p.kayit("A1", "Test", dg, "Ankara", "Çankaya", "Başka Sk", "yeni_ad")
    except KuralIhlali as e:
        print("   Aynı kişi 2. hesap ->", e)

    # --------------------------------------------------------------
    baslik("1) BÖLGESEL KARAR: Ankara'ya havalimanı (sadece Ankaralılar oy verir)")
    kno, oid = p.konu_ac(ankara[0].kid, "Ankara'ya yeni havalimanı yapılsın",
                         "Ek havalimanı önerisi", il="Ankara", alan="havacilik")
    try:
        p.oy_ver(istanbul[0].kid, oid, True)
    except YetkiHatasi as e:
        print("   İstanbullu oy vermeye çalıştı ->", e)
    for u in ankara[:4]:
        p.oy_ver(u.kid, oid, True)
    p.oy_ver(ankara[4].kid, oid, False, yogunluk=2,
             gerekce="Tarım arazisi ve gürültü etkisi yeterince incelenmedi.")
    try:
        p.ara_sonuc(oid)
    except KuralIhlali as e:
        print("   Ara sonuç istendi ->", e)
    p.veto(uzman.kid, oid, "Çevresel etki raporundaki uçuş trafiği verisi hatalı.")
    print("   Bilir kişi vetosu: oylama sıfırlandı, tur =", p.oylamalar[oid].tur_no)
    for u in ankara[:4]:
        p.oy_ver(u.kid, oid, True)
    p.oy_ver(ankara[4].kid, oid, False, yogunluk=2,
             gerekce="Tarım arazisi ve gürültü etkisi yeterince incelenmedi.")
    p.oy_ver(uzman.kid, oid, False, yogunluk=1, gerekce="Veri düzeltilmeden karar verilmemeli.")
    p.ilerle(1)
    p.kapat(oid)
    p.ozet(oid)
    print("   Azınlık imza veriyor -> yeniden inceleme tetiklendi mi?",
          p.imza_ver(ankara[4].kid, oid))
    for u in ankara[:4]:
        p.oy_ver(u.kid, oid, True)
    p.oy_ver(ankara[4].kid, oid, False, yogunluk=2)
    p.oy_ver(uzman.kid, oid, False)
    p.ilerle(1)
    p.kapat(oid)
    p.ozet(oid)
    p.ilerle(Platform.ITIRAZ_SURESI)
    print("   Konu durumu:", p.konular[kno]["durum"])

    # --------------------------------------------------------------
    baslik("2) ULUSAL KARAR + SAHTE ÇOĞUNLUK (Sybil) SALDIRISI")
    kno2, oid2 = p.konu_ac(istanbul[0].kid, "Zorunlu dijital kimlik uygulaması",
                           "Tüm vatandaşlar için zorunlu olsun")
    for u in botlar:
        p.oy_ver(u.kid, oid2, True)               # 6 sahte hesap
    for u in istanbul[:3]:
        p.oy_ver(u.kid, oid2, True)
    for u in istanbul[3:10]:
        p.oy_ver(u.kid, oid2, False, gerekce="Mahremiyet riskleri çözülmeden zorunlu olamaz.")
    p.ilerle(1)
    p.kapat(oid2)
    p.ozet(oid2)
    print("   (Ham sayımla 9 evet - 7 hayır ile KABUL olacaktı; graf analizi bunu engelledi.)")
    p.ilerle(Platform.ITIRAZ_SURESI)
    print("   Konu durumu:", p.konular[kno2]["durum"], "(tartışmalar arşivde görünür kalır)")

    # --------------------------------------------------------------
    baslik("3) TARTIŞMA SİLME: eleştiri silinemez, hakaret 2/3 ile silinir")
    t1 = p.tartisma_yaz(istanbul[5].kid, kno2,
                        "Bu proje halkı fişlemeye açık kapı bırakıyor, çok yanlış.")
    t2 = p.tartisma_yaz(botlar[0].kid, kno2, "Karşı çıkanlar aptal ve salak insanlar.")
    print("   YZ işareti (danışman, engellemez):", p.tartismalar[t2]["yz"])
    try:
        p.silme_oner(istanbul[0].kid, t1, "ELESTIRI", "Çoğunluğun hoşuna gitmiyor")
    except KuralIhlali as e:
        print("   Eleştiriyi silme teklifi ->", e)
    try:
        p.yonetmelik_oner(istanbul[0].kid, "ELESTIRI", "artık silinebilir", True)
    except KuralIhlali as e:
        print("   Çekirdek ilkeyi değiştirme ->", e)
    so = p.silme_oner(istanbul[0].kid, t2, "HAKARET", "Kişilere yönelik aşağılama")
    for u in istanbul[:8]:
        p.oy_ver(u.kid, so, True)
    for u in botlar[:3]:
        p.oy_ver(u.kid, so, False)
    p.ilerle(3)
    p.kapat(so)
    p.ozet(so)
    p.ilerle(Platform.ITIRAZ_SURESI)
    print("   Tartışma görünümü:")
    p.tartisma_goster(kno2)

    # --------------------------------------------------------------
    baslik("4) DEFTER BÜTÜNLÜĞÜ")
    print(f"   Defterde {len(p.defter.kayitlar)} kayıt; zincir geçerli mi? {p.defter.dogrula()}")
    p.defter.kayitlar[10]["veri"] = {"oynama": "gizlice değiştirildi"}
    print("   Bir kayıt gizlice değiştirildi; zincir geçerli mi?", p.defter.dogrula())


if __name__ == "__main__":
    demo()
