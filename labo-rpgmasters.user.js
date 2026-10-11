// ==UserScript==
// @name         Labo RpgMasters — collecteur
// @namespace    labo-rpgmasters
// @version      2.11.11
// @description  Enregistre en lecture seule tes combats RpgMasters (monstres, boss, mécaniques, tours, dégâts, butin), prévient quand un boss connu revient et exporte pour le Labo. N'envoie aucune action au jeu.
// @match        https://rpgmasters.houk.fr/*
// @updateURL    https://venominones.github.io/Dofusrpg/labo-rpgmasters.user.js
// @downloadURL  https://venominones.github.io/Dofusrpg/labo-rpgmasters.user.js
// @run-at       document-start
// @grant        none
// ==/UserScript==

(function () {
  'use strict';
  const BUILDS_KEY = 'labo-builds-v1';
  // Deux persos suivis séparément : le principal et le perso de saison (Héroïque)
  let PROFILE = 'principal'; try { PROFILE = localStorage.getItem('labo-profile') === 'saison' ? 'saison' : 'principal'; } catch (e) {}
  const keyFor = p => p === 'saison' ? 'labo-rec-v1-saison' : 'labo-rec-v1';
  const floorKey = () => PROFILE === 'saison' ? 'labo-floor-saison' : 'labo-floor';
  const MAX_FIGHTS = 3000;
  // ---------- Stockage : IndexedDB (le localStorage du site est limité à ~5 Mo et partagé avec le jeu) ----------
  // Copie en mémoire (REC) pour une lecture synchrone ; écriture asynchrone dans IndexedDB ; l'ancienne clé localStorage est migrée puis libérée.
  const REC = {}; let idbP = null;
  function idb() { if (idbP) return idbP; idbP = new Promise((res, rej) => { try { const rq = indexedDB.open('labo-rpgmasters-rec', 1); rq.onupgradeneeded = () => rq.result.createObjectStore('kv'); rq.onsuccess = () => res(rq.result); rq.onerror = () => rej(rq.error); } catch (e) { rej(e); } }); return idbP; }
  function idbGet(k) { return idb().then(d => new Promise((res, rej) => { const rq = d.transaction('kv').objectStore('kv').get(k); rq.onsuccess = () => res(rq.result); rq.onerror = () => rej(rq.error); })); }
  function idbPut(k, v) { return idb().then(d => new Promise((res, rej) => { const tx = d.transaction('kv', 'readwrite'); tx.objectStore('kv').put(v, k); tx.oncomplete = () => res(); tx.onerror = () => rej(tx.error); })); }
  function recGet(k) { if (REC[k] != null) return REC[k]; try { return localStorage.getItem(k); } catch (e) { return null; } }
  let recOk = true;
  function recSet(k, str) { REC[k] = str; return idbPut(k, str).then(() => { recOk = true; try { localStorage.removeItem(k); } catch (e) {} }).catch(e => { recOk = false; try { localStorage.setItem(k, str); } catch (e2) {} }); }
  const REC_KEYS = ['labo-rec-v1', 'labo-rec-v1-saison', 'labo-vitrines'];
  const recReady = Promise.all(REC_KEYS.map(k => idbGet(k).then(v => { if (typeof v === 'string') REC[k] = v; }).catch(() => {}))).catch(() => {});
  // fusion de deux historiques (combats dédoublonnés par date)
  function mergeRec(a, b) {
    if (!a) return b; if (!b) return a;
    const seen = new Set(a.fights.map(f => f.t)); const fights = a.fights.concat(b.fights.filter(f => !seen.has(f.t))).sort((x, y) => (x.t || 0) - (y.t || 0));
    const bl = new Set((a.bossLogs || []).map(x => x.t)); const bossLogs = (a.bossLogs || []).concat((b.bossLogs || []).filter(x => !bl.has(x.t)));
    return Object.assign({}, a, b, { fights, bossLogs, monsters: Object.assign({}, a.monsters, b.monsters), floors: Object.assign({}, a.floors, b.floors), seen: [...new Set((a.seen || []).concat(b.seen || []))], bossSamples: Object.assign({}, a.bossSamples, b.bossSamples) });
  }
  const started = Date.now();
  const KNOWN_LOG = new Set(['round', 'turn', 'play', 'dmg', 'heal', 'shield', 'buff', 'draw', 'intent', 'death', 'end', 'evade', 'rage', 'weaken', 'ap', 'mechanic']);
  const KNOWN_INTENT = new Set(['attack', 'heavy', 'guard', 'rage', 'drain']);

  // ---------- Moteur de simulation du Labo (copie intégrée automatiquement à la construction, ne pas modifier ici) ----------
  /*__ENGINE_BEGIN__*/ const LR = (function () { const __labo = {};
// RpgMasters — moteur de simulation (reconstitué à partir des échanges observés)
// Utilisable dans le navigateur (window.RPG) et dans Node (module.exports).
(function (root) {
  'use strict';

  // ---------- Constantes du jeu (lues dans le bundle client) ----------
  const FUSION_BONUS = [0, 10, 20, 25, 30, 35, 40, 45];
  const FUSION_EXCLUDED = ['pa', 'pm', 'po', 'invocations'];
  const NOT_SCALED = ['pa', 'pm', 'po', 'invocations'];
  const CARAC_OF_EL = ['force', 'force', 'intelligence', 'chance', 'agilite'];
  const EL_NAMES = ['Neutre', 'Terre', 'Feu', 'Eau', 'Air'];
  const RES_FIX = ['resNeutre', 'resTerre', 'resFeu', 'resEau', 'resAir'];
  const RES_PCT = ['resPctNeutre', 'resPctTerre', 'resPctFeu', 'resPctEau', 'resPctAir'];
  const PRESTIGE_COMBAT = [{ pa: 1 }, { po: 2 }, { pm: 2 }, { pa: 1 }, { po: 3 }, { pm: 3 }, { pa: 1 }];
  // Sorts de zone : la cible principale prend 100 %, chaque autre cible 60 % (mesuré dans le journal, résistances retirées)
  // critiques des monstres : fréquence observée dans le journal, multiplicateur supposé égal à celui du joueur
  const MON_CRIT_P = 0.06, MON_CRIT_MULT = 1.2;
  let ZONE_SEC = 0.6, WEAPON_LAST = false, WEAPON_MODE = 'normal';
  let AUTO_ORDER = 'eff';
  const CAP3 = ['dmgPctDistance', 'dmgPctMelee', 'resPctDistance', 'resPctMelee'];
  const PA_CAPS = [[2, 13], [5, 14], [8, 15]];
  const SUSTAIN = { maxPctHp: 25, perTurn: 2 };
  const RES_PCT_CAP_PLAYER = 50;
  const HAND_SIZE = 5;
  const DRAWS_MAX = 3;
  const CLASS_SPECTRAL = { 9: 26 }; // Crâ : Œil de lynx (patch du 10/10 : 18 → 26 %, plafond 60 %)
  // Passifs de classe observés en combat : 8 = « Enchaînement » (+15 % sur les sorts de dégâts suivants du tour, cumulable)
  const CLASS_PASSIVE = { 8: { chainPct: 15 } };
  // Passifs de classe (texte du client, patch du 10/10) — clé par breedId
  const BREED_KEY = { 1: 'feca', 2: 'osamodas', 3: 'enutrof', 4: 'sram', 5: 'xelor', 6: 'ecaflip', 7: 'eniripsa', 8: 'iop', 9: 'cra', 10: 'sadida', 11: 'sacrieur', 12: 'pandawa', 13: 'roublard', 14: 'zobal', 15: 'steamer', 16: 'eliotrope', 17: 'huppermage', 18: 'ouginak', 20: 'forgelance' };
  const BREED_NAME = { 1: 'Féca', 2: 'Osamodas', 3: 'Enutrof', 4: 'Sram', 5: 'Xélor', 6: 'Ecaflip', 7: 'Eniripsa', 8: 'Iop', 9: 'Crâ', 10: 'Sadida', 11: 'Sacrieur', 12: 'Pandawa', 13: 'Roublard', 14: 'Zobal', 15: 'Steamer', 16: 'Eliotrope', 17: 'Huppermage', 18: 'Ouginak', 20: 'Forgelance' }; const CHAIN_MAX = 3; const CARACS_ALL = ['force', 'intelligence', 'chance', 'agilite'];
  const SPECTRAL_PER_PO = 0.4, SPECTRAL_MAX = 60;
  const DOFAWA_P = 0.001; // Dofawa : 0,1 % par coup
  const POINTS_PER_LEVEL = 5;
  const CARAC_TIERS = [[0, 1], [100, 2], [200, 3], [300, 4]];
  const STAT_TIERS = { vitalite: [[0, 1]], sagesse: [[0, 3]], force: CARAC_TIERS, intelligence: CARAC_TIERS, chance: CARAC_TIERS, agilite: CARAC_TIERS };
  // Monstres (observés)
  const INTENT_MULT = { attack: 1, heavy: 1.7, drain: 0.8 };
  // Calibré sur les journaux de combat : un critique sans valeurs critiques propres multiplie la base du sort par ~1,15
  let CRIT_MULT = 1.2;
  const RAGE_STEP = 0.3, GUARD_PCT = 0.97, WEAKEN_PER_PA = 15;

  const jsRound = Math.round;

  // ---------- Statistiques ----------
  function itemStats(it, f) {
    f = f || 0;
    if (!f) return Object.assign({}, it.st);
    const o = {};
    if (it.s === 'dofus' && f >= 7) {
      for (const k in it.st) o[k] = it.st[k] > 0 ? jsRound(it.st[k] * 2) : it.st[k];
      return o;
    }
    const m = 1 + FUSION_BONUS[Math.min(7, f)] / 100;
    for (const k in it.st) {
      const v = it.st[k];
      o[k] = v > 0 && !FUSION_EXCLUDED.includes(k) ? Math.max(v + 1, jsRound(v * m)) : v;
    }
    if (f >= 2 && it.s !== 'dofus' && (o.pa || 0) > 0) o.pa = Math.max(o.pa, 2);
    return o;
  }
  function weaponWithFusion(w, f) {
    if (!f || !w) return w;
    const m = 1 + FUSION_BONUS[Math.min(7, f)] / 100;
    const a = v => Math.max(v + 1, jsRound(v * m));
    return Object.assign({}, w, { lines: w.lines.map(l => l.k === 'apRemove' ? l : Object.assign({}, l, { min: l.min > 0 ? a(l.min) : l.min, max: l.max > 0 ? a(l.max) : l.max })) });
  }
  function tierCost(tiers, from, n) {
    let cost = 0, cur = from, left = n;
    while (left > 0) {
      let t = tiers[0];
      for (const s of tiers) if (cur >= s[0]) t = s;
      cost += t[1]; cur += 1; left -= 1;
    }
    return cost;
  }
  // Bouclier de forge (page Forgemagie, « Paliers du bouclier ») : courbe exponentielle, ×1,287 tous les 10 niveaux,
  // +1,25 % au niv. 10, +12,1 % au niv. 100, +150 % au niv. 200 (écart < 0,05 point sur les 20 paliers). Additif au Prestige, hors PA/PM/PO/invocations.
  const FORGE_K = Math.log(150 / 1.25) / 190;
  // XP de l'Infini cumulée pour atteindre chaque dizaine de niveaux (page Forgemagie) ; plafond 2 500 orbes/jour
  const FORGE_XP = { 1: 0, 10: 247, 20: 816, 30: 1606, 40: 2580, 50: 3717, 60: 5003, 70: 6428, 80: 7982, 90: 9659, 100: 11453, 110: 13359, 120: 15374, 130: 17492, 140: 19712, 150: 22029, 160: 24442, 170: 26948, 180: 29544, 190: 32229, 200: 35000 };
  function forgeXpAt(level) { const L = Math.max(1, Math.min(200, level)); const a = L <= 10 ? 1 : Math.floor(L / 10) * 10, b = Math.min(200, a === 1 ? 10 : a + 10); if (L === a) return FORGE_XP[a]; return FORGE_XP[a] + (FORGE_XP[b] - FORGE_XP[a]) * (L - a) / (b - a); }
  function forgeDaysTo(target, level, xp) { const need = Math.max(0, forgeXpAt(target) - forgeXpAt(level) - (xp || 0)); return Math.ceil(need / 2500); }
  function forgePctFor(level, known) {
    if (known != null && isFinite(known)) return known;
    const L = Math.max(0, Math.min(200, level || 0));
    return L < 1 ? 0 : Math.round(150 * Math.exp(FORGE_K * (L - 200)) * 100) / 100;
  }
  function pointsTotal(level) { return (level - 1) * POINTS_PER_LEVEL; }
  function allocCost(alloc) {
    let c = 0;
    for (const k in STAT_TIERS) c += tierCost(STAT_TIERS[k], 0, alloc[k] || 0);
    return c;
  }

  // gear : [{item, f}] ; ctx : {prestige, discordPct, scrolls, alloc, level, breedId}
  // Dofus à effet spécial (patch du 10/10) : repérés par leur nom
  const DOFUS_FX = { emeraude: /meraude/i, pourpre: /pourpre/i, turquoise: /turquoise/i, ocre: /ocre/i, vulbis: /vulbis/i, ivoire: /ivoire/i, glaces: /glace/i, ebene: /b[eè]ne/i, kaliptus: /kaliptus/i, tachete: /tachet/i, dofawa: /dofawa/i };
  function dofusFx(names) { const o = {}; for (const n of names) { if (!/dofus|dofawa|kaliptus/i.test(n)) continue; for (const [k, re] of Object.entries(DOFUS_FX)) if (re.test(n)) o[k] = true; } return o; }
  function computeStats(gear, ctx) {
    // Prestige : +25 % par Prestige ; Bouclier de forge : jusqu'à +150 % au niveau 200 (cumul supposé additif, à confirmer)
    const pMult = 1 + 0.25 * (ctx.prestige || 0) + (ctx.forgePct || 0) / 100 + (ctx.companionPct || 0) / 100; // Compagnon (patch du 10/10) : jusqu'à +100 % au niveau 400, cumul supposé additif comme le Bouclier
    const tot = {}, raw3 = {};
    for (const g of gear) {
      if (!g || !g.item) continue;
      const st = itemStats(g.item, g.f);
      for (const k in st) {
        const v = st[k];
        // Pénétration / Réduction : seuls les bonus comptent, multiplicateur total plafonné à ×3
        if (CAP3.includes(k)) { if (v > 0) raw3[k] = (raw3[k] || 0) + v; continue; }
        if (NOT_SCALED.includes(k)) { tot[k] = (tot[k] || 0) + v; continue; }
        tot[k] = (tot[k] || 0) + (v > 0 ? jsRound(v * pMult) : v);
      }
    }
    // Bonus de panoplie : traités comme un objet de plus (même effet du Prestige), palier connu le plus proche
    if (ctx.setTiers) {
      const cnt = {};
      for (const g of gear) if (g && g.item && g.item.setId) cnt[g.item.setId] = (cnt[g.item.setId] || 0) + 1;
      for (const id in cnt) {
        const tiers = ctx.setTiers[id]; if (!tiers || cnt[id] < 2) continue;
        let k = cnt[id]; while (k >= 2 && !tiers[k]) k--;
        const st = tiers[k]; if (!st) continue;
        for (const key in st) { const v = st[key]; tot[key] = (tot[key] || 0) + (NOT_SCALED.includes(key) || v <= 0 ? v : jsRound(v * pMult)); }
      }
    }
    const d = 1 + (ctx.discordPct || 0) / 100;
    const s = {};
    for (const k in tot) s[k] = (tot[k] > 0 && !NOT_SCALED.includes(k)) ? jsRound(tot[k] * d) : tot[k];
    const m3 = Math.min(3, pMult * d);
    for (const k of CAP3) if (raw3[k]) s[k] = jsRound(raw3[k] * m3);
    for (const k in (ctx.scrolls || {})) s[k] = (s[k] || 0) + (ctx.scrolls[k] || 0);
    for (const k in (ctx.alloc || {})) s[k] = (s[k] || 0) + (ctx.alloc[k] || 0);
    const pb = { pa: 0, pm: 0, po: 0 };
    for (let i = 0; i < Math.min(ctx.prestige || 0, PRESTIGE_COMBAT.length); i++) for (const k in PRESTIGE_COMBAT[i]) pb[k] += PRESTIGE_COMBAT[i][k];
    s.pa = (s.pa || 0) + pb.pa; s.pm = (s.pm || 0) + pb.pm; s.po = (s.po || 0) + pb.po;
    let cap = 12; for (const [p, c] of PA_CAPS) if ((ctx.prestige || 0) >= p) cap = Math.max(cap, c);
    s._paTotal = Math.min(cap, ((ctx.level || 200) >= 100 ? 7 : 6) + s.pa);
    s._maxHp = 50 + 5 * (ctx.level || 200) + (s.vitalite || 0);
    s._breed = ctx.breedId;
    s._spectral = Math.min(SPECTRAL_MAX, (CLASS_SPECTRAL[ctx.breedId] || 0) + SPECTRAL_PER_PO * (s.po || 0));
    s._dodge = Math.min(50, Math.max(0, 3 + (s.pm || 0)));
    // Règles de la fiche personnage
    s._pen = Math.min(50, (s.dmgPctDistance || 0) + (s.dmgPctMelee || 0)) * 0.8;   // % de résistance élémentaire ignorée
    s._red = Math.min(50, (s.resPctDistance || 0) + (s.resPctMelee || 0));          // % de dégâts subis en moins, avant résistances
    s._perfo = Math.max(0, Math.min(25, ((s.fuite || 0) + (s.tacle || 0)) * 0.05));  // % des dégâts qui traversent les boucliers ennemis
    s._ero = Math.max(0, Math.min(25, ((s.dommagesPoussee || 0) + (s.resPoussee || 0)) * 0.05)); // % des dégâts retirés aux PV max
    s._pp = 100 + (s.prospection || 0) + Math.floor((s.chance || 0) / 10);
    s._dofus = dofusFx(gear.filter(g => g && g.item && (g.item.s === 'dofus' || /dofus/i.test(g.item.n || ''))).map(g => g.item.n || ''));
    if (s._dofus.ebene) s._perfo = Math.min(32.5, s._perfo * 1.3);
    return s;
  }

  // Stats de combat telles que le jeu les envoie (combat en cours, builds enregistrés) → champs dérivés du moteur
  function deriveStats(stats, o) {
    o = o || {}; const S = Object.assign({}, stats);
    if (o.maxHp) S._maxHp = o.maxHp; if (o.basePa) S._paTotal = o.basePa; S._breed = o.breedId;
    S._dodge = Math.min(50, Math.max(0, 3 + (S.pm || 0)));
    S._spectral = Math.min(SPECTRAL_MAX, (CLASS_SPECTRAL[o.breedId] || 0) + SPECTRAL_PER_PO * (S.po || 0));
    S._pp = 100 + (S.prospection || 0) + Math.floor((S.chance || 0) / 10);
    S._pen = Math.min(50, (S.dmgPctDistance || 0) + (S.dmgPctMelee || 0)) * 0.8;
    S._red = Math.min(50, (S.resPctDistance || 0) + (S.resPctMelee || 0));
    S._perfo = Math.max(0, Math.min(25, ((S.fuite || 0) + (S.tacle || 0)) * 0.05));
    S._ero = Math.max(0, Math.min(25, ((S.dommagesPoussee || 0) + (S.resPoussee || 0)) * 0.05));
    S._dofus = dofusFx(o.dofus || []); if (S._dofus.ebene) S._perfo = Math.min(32.5, S._perfo * 1.3);
    return S;
  }

  // ---------- Dégâts ----------
  function dmgLine(S, line, crit, buffPuiss, dmgPct, spectral, resPct, withFixed, isWeapon, extra) {
    const base = line.min + RND() * (line.max - line.min + 1);
    const b = Math.min(line.max, Math.floor(base));
    const carac = (S[CARAC_OF_EL[line.el || 0]] || 0) + (S.puissance || 0) + buffPuiss + ((S._cb && S._cb[CARAC_OF_EL[line.el || 0]]) || 0);
    let fixed = 0;
    if (withFixed) fixed = (S.dommages || 0) + (S['dommages' + EL_NAMES[line.el || 0]] || 0) + (crit ? (S.dommagesCritiques || 0) : 0);
    let v = (b * (1 + carac / 100) * (crit === 'boost' ? CRIT_MULT : 1) + fixed) * (1 + ((isWeapon ? (S.dmgPctArmes || 0) : dmgPct) + (extra || 0)) / 100) * (spectral ? 2 : 1) * (1 - resPct / 100);
    return Math.max(0, Math.floor(v));
  }
  // Valeur moyenne attendue d'une ligne (pour la politique de jeu)
  function expLine(S, line, critP, buffPuiss, dmgPct, specP, resPct, withFixed, isWeapon, critLine, extra) {
    const avg = l => (l.min + l.max) / 2;
    const carac = (S[CARAC_OF_EL[line.el || 0]] || 0) + (S.puissance || 0) + buffPuiss + ((S._cb && S._cb[CARAC_OF_EL[line.el || 0]]) || 0);
    const fixed = withFixed ? (S.dommages || 0) + (S['dommages' + EL_NAMES[line.el || 0]] || 0) : 0;
    const nc = avg(line) * (1 + carac / 100) + fixed;
    const cl = critLine || line;
    const cr = avg(cl) * (1 + carac / 100) * (critLine ? 1 : CRIT_MULT) + fixed + (withFixed ? (S.dommagesCritiques || 0) : 0);
    const v = ((1 - critP) * nc + critP * cr) * (1 + ((isWeapon ? (S.dmgPctArmes || 0) : dmgPct) + (extra || 0)) / 100) * (1 + (isWeapon ? 0 : specP)) * (1 - resPct / 100);
    return Math.max(0, v);
  }

  // ---------- Préparation des cartes ----------
  function prepCard(c, uid) {
    const isDmg = l => l.k === 'dmg' || l.k === 'steal';
    // Gain de PA : immédiat (Précipitation, vérifié en jeu), sauf si la description dit « au tour suivant » (Odorat)
    const apLater = /PA au tour suivant|augmenter les PA au tour suivant/i.test(String(c.d || c.desc || ''));
    const eff = (c.eff || []).map(l => l.k === 'apGain' ? Object.assign({}, l, { now: !apLater }) : l);
    const chanceLines = eff.filter(l => l.chance);
    return {
      uid, id: c.id, name: c.n || c.name, ap: c.ap, cc: c.cc || 0, eff, crit: c.crit || null,
      weapon: !!c.weapon, chanceLines,
      dmgLines: eff.filter(isDmg),
      isSustain: eff.some(l => ['heal', 'healPct', 'shieldHp', 'shieldLvl'].includes(l.k)) && !eff.some(isDmg),
      hasDmg: eff.some(l => isDmg(l) || l.k === 'bomb' || l.k === 'dmgCasterHp'),
      isBuff: eff.some(l => l.k === 'buff') && !eff.some(isDmg),
    };
  }
  function weaponCard(item, f) {
    const w = weaponWithFusion(item.w, f);
    if (!w) return null;
    const lines = w.lines.map(l => Object.assign({ tgt: 'enemy' }, l));
    const cl = lines.map(l => l.k === 'apRemove' ? l : Object.assign({}, l, { min: l.min + (w.ccBonus || 0), max: l.max + (w.ccBonus || 0) }));
    return prepCard({ id: item.id, n: item.n, ap: w.ap, cc: w.cc, eff: lines, crit: cl, weapon: true }, 'w');
  }

  // ---------- Combat ----------
  function makeMonster(m, i) {
    const hp = Math.round((m.hpMin + m.hpMax) / 2);
    return { mech: m.mech || null, id: 'm' + i, name: m.name, hp, maxHp: hp, cap: hp, atk: m.atk, el: m.element, pattern: m.pattern, idx: (m.pattern && m.pattern.length > 1 && !m.fixedStart) ? Math.floor(RND() * m.pattern.length) : 0, /* le cycle d'intentions ne commence pas toujours au début (observé : 15 combats sur 18) */ res: m.stats || {}, rage: 0, weaken: 0, shield: 0, alive: true, isBoss: !!m.isBoss, bombs: [], noOS: !!m.noOneShot || hp > 5e6 };
  }

  // opts: {S, deck:[cards], weapon, monsters:[defs], maxRounds}
  function simulateFight(opts) {
    const S = opts.S, maxHp = S._maxHp;
    const P = { hp: Math.min(maxHp, opts.startHp > 0 ? opts.startHp : maxHp), shields: [], apNext: 0 };
    const mons = opts.monsters.map(makeMonster);
    let pile = shuffle(opts.deck.slice()), discard = [], hand = [];
    const shieldCap = Math.floor(maxHp * SUSTAIN.maxPctHp / 100);
    const specP = S._spectral / 100;
    let dmgDone = 0, hpLost = 0;
    const perCard = {};
    const trace = {};
    const er = r => r > 0 ? r * (1 - (S._pen || 0) / 100) : r; // Pénétration : jamais sous 0, les faiblesses restent entières
    const wMode = opts.weaponMode || (WEAPON_LAST ? 'last' : WEAPON_MODE);
    const chainPct = opts.chainPct != null ? opts.chainPct : ((CLASS_PASSIVE[S._breed] || {}).chainPct || 0);
    const T = { buffP: 0, buffC: 0, dmgPct: 0, sustainLeft: 0, weaponUsed: false, inv: false, invS: false, half: false, cards: 0, lastEl: null, round: 0 };
    const DF = S._dofus || {}; const pers = []; S._cb = {}; /* bonus qui durent plusieurs tours (Prélude au Fer, Évolution…) et caracs volées (Drain Élémentaire) */ let vulb = 0, critTurn = false, pourpreUsed = !DF.pourpre, emeraudeUsed = !DF.emeraude;
    // ----- passif de classe -----
    const PK = opts.passive !== undefined ? opts.passive : (BREED_KEY[S._breed] || null);
    const C = { n: 0, prey: null, preyN: 0, att: 0, runes: new Set(), cur: null, firstDone: false, ougPa: false, bombN: 0 };
    const missPct = () => Math.max(0, 100 - P.hp * 100 / maxHp);
    // bonus % de dégâts du passif contre m (c = carte jouée, null pour une bombe qui explose)
    const clsPct = (m, c, bomb) => {
      if (!PK) return 0; const w = c && c.weapon, cur = C.cur || {};
      switch (PK) {
        case 'feca': return 6 * C.n;
        case 'enutrof': return 5 * C.n;
        case 'xelor': return 6 * C.n;
        case 'eniripsa': return 9 * C.n;
        case 'pandawa': return 5 * C.n;
        case 'sram': { const r = m ? m.hp / m.maxHp : 1; return r < 0.25 ? 60 : r < 0.5 ? 30 : 0; }
        case 'sacrieur': return Math.min(63, 7 * Math.floor(missPct() / 10));
        case 'roublard': return (bomb ? 50 : 0) + 10 * Math.min(3, C.bombN);
        case 'zobal': { const k = (T.round - 1) % 3; return k === 0 ? 10 : k === 1 ? 25 : 0; }
        case 'steamer': return 7 * Math.min(6, Math.max(0, T.round - 1));
        case 'eliotrope': return cur.portal ? 50 : 0;
        case 'huppermage': return 11 * Math.min(4, C.runes.size);
        case 'ouginak': return m && m === C.prey ? 12 * C.preyN : 0;
        case 'forgelance': return cur.lance && !w ? 45 : 0;
      }
      return 0;
    };
    const clsTaken = () => PK === 'feca' ? 6 * C.n : PK === 'zobal' ? [10, 0, 25][(T.round - 1) % 3] : 0; // % de dégâts subis en moins
    const ECA = PK === 'ecaflip';
    const saved = () => { if (P.hp <= 0 && !emeraudeUsed) { emeraudeUsed = true; P.hp = Math.max(1, Math.round(maxHp * 0.2)); } return P.hp > 0; }; // Émeraude : survit une fois avec 20 % de PV
    // Mécaniques de boss : chaque boss encore debout applique les siennes (bestiaire + mécaniques apprises en combat)
    const alive = () => mons.filter(x => x.alive);
    const mk = (k) => { for (const m of mons) if (m.alive && m.mech && m.mech[k] != null && m.mech[k] !== false) return m.mech; return null; };
    const mv = (k, d) => { const x = mk(k); return x ? x[k] : d; };
    const every = (k, round) => k > 0 && round % k === 0;
    const rageAt = opts.rageTurn || 0;
    for (let round = 1; round <= (opts.maxRounds || 30); round++) {
      T.round = round;
      // échange de vie au début du tour
      for (const m of alive()) if (m.mech && m.mech.swapTurn === round) {
        const mp = m.hp / m.maxHp, pp = P.hp / maxHp;
        if (mp < pp) { const nm = m.mech.swapHalf ? mp + (pp - mp) / 2 : pp, np = m.mech.swapHalf ? pp - (pp - mp) / 2 : mp; m.hp = Math.max(1, Math.round(nm * m.maxHp)); const nh = Math.max(1, Math.round(np * maxHp)); if (nh < P.hp) hpLost += P.hp - nh; P.hp = nh; }
      }
      // ----- tour du joueur -----
      let ap = S._paTotal + P.apNext + (critTurn ? 1 : 0); P.apNext = 0; critTurn = false; // Turquoise : +1 PA (au-delà du plafond) le tour après un critique
      while (hand.length < HAND_SIZE + (round === 1 && DF.ocre ? 1 : 0)) { const c = draw(); if (!c) break; hand.push(c); }
      C.firstDone = false; C.ougPa = false; if (PK === 'pandawa' && C.n) P.hp = Math.min(maxHp, P.hp + Math.floor(maxHp * C.n / 100)); // Ivresse : soin non réductible
      T.buffP = 0; T.buffC = 0; T.chainN = 0; T.dmgPct = S.dmgPctSorts || 0; S._cb = {};
      for (const b of pers) if (b.until >= round) { if (b.stat === 'puissance') T.buffP += b.v; else if (b.stat === 'critique') T.buffC += b.v; else if (b.stat === 'dmgPctSorts') T.dmgPct += b.v; else S._cb[b.stat] = (S._cb[b.stat] || 0) + b.v; } T.sustainLeft = SUSTAIN.perTurn; T.weaponUsed = false; T.cards = 0; let drawsLeft = DRAWS_MAX;
      const invFrom = opts.invertFrom || mv('invertFrom', 0), sealPa = opts.sealPa || mv('sealPa', 0), sealFrom = opts.sealFrom || mv('sealFrom', 1);
      const halfFrom = mv('healHalfFrom', 0);
      T.inv = invFrom > 0 && round >= invFrom; T.invS = T.inv && !!(opts.invertShields || mv('invertShields', false)); T.seal = (sealPa > 0 && round >= sealFrom) ? sealPa : 0;
      T.half = halfFrom > 0 && round >= halfFrom;
      // vol de PA
      const stealEvery = mv('apStealEvery', 0); let tachete = !!DF.tachete; // Tacheté : annule le premier effet de contrôle du tour
      if (stealEvery ? every(stealEvery, round) : (mv('apSteal', 0) && round >= mv('apStealFrom', 1))) { if (tachete) tachete = false; else ap = Math.max(0, ap - (mv('apSteal', 0) || 1)); }
      // carte scellée pour le tour : la plus chère de la main
      const sealEvery = mv('sealEvery', 0);
      const sealOn = sealEvery ? every(sealEvery, round) : (mv('sealCard', false) && round >= mv('sealCardFrom', 1));
      const sealedCard = sealOn && hand.length && !(tachete && !(tachete = false)) ? hand.reduce((a, c) => (c.ap > a.ap ? c : a), hand[0]) : null;
      // PA comptés : finir le tour avec exactement N PA
      const paM = mk('paTurn'), paNeed = paM && paM.paTurn === round ? paM.paLeft : null;
      // Fureur : au-delà de N cartes (hors arme) dans le tour, sa prochaine attaque est multipliée
      const furyCap = Math.min(99, ...alive().filter(m => m.mech && m.mech.furyCards).map(m => m.mech.furyCards));
      // bombes posées au tour précédent
      for (const m of mons) if (m.alive && m.bombs.length) { for (const b of m.bombs) { C.cur = null; hit(m, b, 'Bombe', { bomb: true }); if (PK === 'roublard') C.bombN++; } m.bombs = []; }
      for (let guard = 0; guard < 20; guard++) {
        if (!mons.some(m => m.alive)) break;
        const cost = c => c.ap + (T.seal && !c.weapon ? T.seal : 0);
        const room = paNeed != null && !opts.auto ? ap - paNeed : ap;
        const capped = !opts.auto && T.cards >= furyCap;
        const opts2 = capped ? [] : hand.filter(c => c !== sealedCard).map(c => ({ c, v: opts.auto ? 0 : valueOf(c) })) /* en auto, l'ordre vient de rank() : inutile d'estimer chaque carte deux fois */.filter(o => cost(o.c) <= room && (opts.auto || o.v > 0));
        if (!T.weaponUsed && opts.weapon && opts.weapon.ap <= room && !(opts.auto && wMode === 'never')) { const wv = opts.auto ? 0 : valueOf(opts.weapon); if (opts.auto || wv > 0) opts2.push({ c: opts.weapon, v: wv }); }
        if (!opts2.length) {
          if (!capped && drawsLeft > 0 && hand.length < 8) { const c = draw(); drawsLeft--; if (c) { hand.push(c); continue; } }
          break;
        }
        if (opts.auto) {
          // Ordre observé du mode auto : boucliers/soins d'abord, puis dégâts du plus fort au plus faible
          // (cartes de PA au milieu), bonus purs en dernier ; il joue tout ce qui est payable, même inutile.
          const maxD = Math.max(1, ...opts2.map(o => o.c.hasDmg ? dmgCardValue(o.c, T.buffP, T.buffC, T.dmgPct) : 0));
          // Ordre réglé par le joueur (page Deck, « Ordre de l'Auto ») : premier sort utile de la liste, arme après les sorts sauf « Prioritaire »
          if (opts.ranked) { const idx = c => c.weapon ? (wMode === 'prio' ? -1 : 1e6) : (parseInt(String(c.uid).slice(1), 10) || 0); const useless = c => c.isSustain && T.sustainLeft <= 0; const rk2 = new Map(opts2.map(o => [o, useless(o.c) ? 2e6 : idx(o.c)])); opts2.sort((a, b) => rk2.get(a) - rk2.get(b)); } else {
          const rank = c => (T.sustainLeft > 0 && c.eff && c.eff.some(l => /^(shieldHp|shieldLvl|heal|healPct)$/.test(l.k))) ? 3e9
            // Réglage « Arme en auto » du jeu : Prioritaire / Normale (selon l'efficacité) / En dernier / Jamais
            : c.weapon && wMode === 'prio' ? 2e9
            : c.weapon && wMode === 'last' ? -1
            : c.hasDmg ? 1e9 + (AUTO_ORDER === 'hand' ? 1e6 - hand.indexOf(c) : AUTO_ORDER === 'eff' ? dmgCardValue(c, T.buffP, T.buffC, T.dmgPct) / Math.max(1, c.ap) : AUTO_ORDER === 'effmono' ? dmgCardValue(c, T.buffP, T.buffC, T.dmgPct, true) / Math.max(1, c.ap) : AUTO_ORDER === 'mono' ? dmgCardValue(c, T.buffP, T.buffC, T.dmgPct, true) : dmgCardValue(c, T.buffP, T.buffC, T.dmgPct))
            : (c.eff && c.eff.some(l => l.k === 'apGain' && l.now && l.max > c.ap)) ? 2.5e9 // gain de PA immédiat : d'abord, il paie les sorts suivants
            : (c.eff && c.eff.some(l => l.k === 'apGain' || l.k === 'apRemove')) ? 1e9 + (AUTO_ORDER === 'eff' ? 0 : maxD * 0.5) : 0;
          const rk = new Map(opts2.map(o => [o, rank(o.c)])); opts2.sort((a, b) => rk.get(b) - rk.get(a)); } // valeur calculée une fois par carte
        } else opts2.sort((a, b) => b.v / Math.max(1, cost(b.c)) - a.v / Math.max(1, cost(a.c)) || b.v - a.v);
        let pick = opts2[0].c;
        // À la main : rotation optimale du tour (ordre bonus → dégâts, PA gardés, arme au bon moment)
        if (!opts.auto && opts.plan !== false && opts2.length > 1) {
          const seq = planTurn(opts2.map(o => o.c), room, cost, capped ? 0 : furyCap - T.cards, paNeed != null ? paNeed : null, ap);
          if (seq && seq.length) pick = seq[0];
        }
        play(pick); passiveAfter(pick); if (chainPct && (T.chainN || 0) < CHAIN_MAX) { T.dmgPct += chainPct; T.chainN = (T.chainN || 0) + 1; } // Enchaînement (Iop) : chaque sort lancé (et l'arme, observé) +15 % aux suivants du tour, 3 fois au plus (+45 %) — texte du jeu // l'arme compte aussi dans l'Enchaînement (observé)
        if (opts.trace) (trace[round] = trace[round] || []).push(pick.name + (pick.weapon ? ' (arme)' : ''));
        if (!pick.weapon) T.cards++;
        if (T.apNow) { ap += T.apNow; T.apNow = 0; } // PA gagnés tout de suite (Précipitation)
        if (P.hp <= 0 && !saved()) return result(false, round);
        ap -= cost(pick); if (!pick.weapon) T.seal = 0;
        if (pick.weapon) T.weaponUsed = true; else { hand.splice(hand.indexOf(pick), 1); discard.push(pick); }
      }
      if (!mons.some(m => m.alive)) return result(true, round);
      // PA comptés : sinon il te pulvérise
      if (paNeed != null && ap !== paNeed && (opts.auto || ap < paNeed)) { hpLost += P.hp; P.hp = 0; return result(false, round); }
      // Fureur déclenchée ?
      for (const m of alive()) if (m.mech && m.mech.furyCards && T.cards > m.mech.furyCards) m.furyNext = Math.max(m.furyNext || 1, m.mech.furyMult || 1.5);
      // expiration boucliers
      P.shields = P.shields.filter(s => (s.turns -= 1) >= 0 && s.value > 0);
      // Rage : au tour N il t'achève
      const rg = rageAt || mv('rageTurn', 0);
      if (rg && round >= rg) { hpLost += P.hp; P.hp = 0; return result(false, round); }
      // ----- tour des monstres -----
      for (const m of mons) {
        if (!m.alive) continue;
        if (m.poison && m.poison.length) { // Sadida : poison en % des PV max au début du tour du monstre
          const pct = Math.min(m.isBoss ? 3 : 12, m.poison.length * 3); // 3 % par charge, 12 % max (boss : 3 %)
          const d = Math.min(m.hp, Math.floor(m.maxHp * pct / 100)); m.hp -= d; dmgDone += d; perCard['Poison (passif)'] = (perCard['Poison (passif)'] || 0) + d;
          m.poison = m.poison.map(x => x - 1).filter(x => x > 0);
          if (m.hp <= 0) { m.hp = 0; down(m); if (!m.alive) continue; }
        }
        const intent = m.pattern[m.idx % m.pattern.length]; m.idx++;
        m.shield = 0;
        if (intent === 'rage') { m.rage++; continue; }
        if (intent === 'guard') { m.shield = Math.round(m.atk * GUARD_PCT); continue; }
        const fury = intent === 'drain' ? 1 : (m.furyNext || 1); if (intent !== 'drain') m.furyNext = 0;
        // Fureur : observé en Ascension, le coup « déchaîné » vaut ~×fureur l'attaque de base (il remplace le bonus de l'intention)
        const mult = (fury > 1 && intent !== 'drain' ? fury : (INTENT_MULT[intent] || 1)) * (1 + RAGE_STEP * m.rage) * (1 - Math.min(100, m.weaken) / 100) * (DF.glaces && (m.glaces || 0) >= round ? 0.9 : 1); // Glaces : la cible touchée frappe 10 % moins fort pendant 2 tours
        m.weaken = 0;
        if (RND() * 100 < Math.min(DF.vulbis ? 75 : 100, S._dodge + vulb)) continue;
        if (DF.vulbis) vulb += 2; // Vulbis : +2 % d'esquive par coup non esquivé
        const rf = S[RES_FIX[m.el]] || 0, rp = Math.min(RES_PCT_CAP_PLAYER, S[RES_PCT[m.el]] || 0);
        let dmg = Math.max(0, Math.floor((m.atk * mult * (1 - (S._red || 0) / 100) * (1 - clsTaken() / 100) - rf) * (1 - rp / 100)));
        // coup critique du monstre (rare, observé ~6 %) : la Résistance Critiques retire sa valeur au coup critique reçu
        if (RND() < MON_CRIT_P) dmg = Math.max(0, Math.floor(dmg * MON_CRIT_MULT) - (S.resCritiques || 0));
        if (opts.mlog) { opts.mlog.hits = (opts.mlog.hits || 0) + 1; opts.mlog.raw = (opts.mlog.raw || 0) + dmg; if (round === 1) opts.mlog.r1 = (opts.mlog.r1 || 0) + 1; }
        for (const s of P.shields) { const a = Math.min(s.value, dmg); s.value -= a; dmg -= a; if (!dmg) break; }
        if (DF.ivoire) dmg = Math.min(dmg, Math.floor(maxHp * 0.35)); // Ivoire : aucun coup ordinaire au-delà de 35 % des PV max
        P.hp -= dmg; hpLost += dmg;
        if (intent === 'drain') m.hp = Math.min(m.cap, m.hp + dmg);
        if (S.renvoi > 0 && dmg > 0) { const r = Math.min(m.hp, S.renvoi, dmg); /* au plus les dégâts reçus */ m.hp -= r; dmgDone += r; if (m.hp <= 0) { m.hp = 0; down(m); } }
        if (P.hp <= 0 && !saved()) return result(false, round);
      }
      if (!mons.some(m => m.alive)) return result(true, round);
    }
    return result(false, opts.maxRounds || 30);

    function result(win, rounds) { const tm = mons.reduce((a, m) => a + m.maxHp, 0) || 1; return { trace, win, rounds, hpLost, dmgDone, perCard, progress: win ? 1 : 1 - mons.reduce((a, m) => a + (m.alive ? Math.max(0, m.hp) + (m.mech && m.mech.revive && !m.revived ? m.maxHp * (m.mech.revivePct != null ? m.mech.revivePct / 100 : 0.5) : 0) : 0), 0) / tm, kills: mons.filter(m => !m.alive).length }; }
    function healP(a) { if (T.inv) { P.hp -= a; hpLost += a; } else P.hp = Math.min(maxHp, P.hp + (T.half ? Math.floor(a / 2) : a)); }
    function draw() { if (!pile.length) { if (!discard.length) return null; pile = shuffle(discard); discard = []; } return pile.pop(); }
    function reflects(m) { return !!(m.mech && m.mech.reflectFrom && T.round >= m.mech.reflectFrom && (!m.mech.reflectTo || T.round <= m.mech.reflectTo)); }
    // Mode auto : le jeu vise le premier boss encore debout. Mode manuel : le plus entamé, en évitant celui qui renvoie les coups.
    function target() {
      if (opts.auto) return mons.find(m => m.alive) || null;
      let t = null; for (const m of mons) if (m.alive && !reflects(m) && (!t || m.hp < t.hp)) t = m;
      return t || mons.find(m => m.alive) || null;
    }
    function shieldTotal() { return P.shields.reduce((a, s) => a + s.value, 0); }
    function incomingNext() {
      let tot = 0;
      for (const m of mons) {
        if (!m.alive) continue;
        const intent = m.pattern[m.idx % m.pattern.length];
        if (intent === 'rage' || intent === 'guard') continue;
        const mult = (INTENT_MULT[intent] || 1) * (1 + RAGE_STEP * m.rage) * (1 - Math.min(100, m.weaken) / 100);
        const rf = S[RES_FIX[m.el]] || 0, rp = Math.min(RES_PCT_CAP_PLAYER, S[RES_PCT[m.el]] || 0);
        tot += Math.max(0, (m.atk * mult * (1 - (S._red || 0) / 100) * (1 - clsTaken() / 100) - rf) * (1 - rp / 100));
      }
      return tot;
    }
    function dmgCardValue(c, puiss, crit, dpct, mono) {
      const t = target(); if (!t) return 0;
      const critP = c.cc > 0 ? Math.min(1, (c.cc + (S.critique || 0) + crit) / 100) : 0;
      const lines = c.chanceLines.length ? [c.chanceLines[0]] : c.dmgLines;
      let v = 0, first = true;
      if (!c._clMap) { c._clMap = new Map(); for (const l of lines) c._clMap.set(l, c.crit ? c.crit.filter(x => x.k === l.k)[c.dmgLines.indexOf(l) >= 0 ? c.dmgLines.filter(x => x.k === l.k).indexOf(l) : 0] || null : null); }
      lines.forEach((l, i) => {
        const cl = c._clMap.has(l) ? c._clMap.get(l) : null;
        const withFixed = c.weapon ? true : first; first = false;
        let lv = 0;
        if (l.zone && !mono) { for (const m of mons) if (m.alive) lv += Math.min(m.hp + m.shield, (m === t ? 1 : ZONE_SEC) * expLine(S, l, critP, puiss, dpct, c.weapon ? 0 : specP, er(m.res[RES_PCT[l.el || 0]] || 0), withFixed, c.weapon, cl, estPct(m, c)) * ecaF(c)); }
        else lv = expLine(S, l, critP, puiss, dpct, c.weapon ? 0 : specP, er(t.res[RES_PCT[l.el || 0]] || 0), withFixed, c.weapon, cl, estPct(t, c)) * ecaF(c);
        v += lv;
      });
      for (const l of c.eff) if (l.k === 'bomb') v += 0.8 * expLine(S, l, 0, puiss, dpct, 0, er(t.res[RES_PCT[l.el || 0]] || 0), true, false, null, PK ? clsPct(t, null, true) : 0);
      return v;
    }
    // Recherche de la meilleure séquence de cartes pour le tour (profondeur limitée), avec les bonus appliqués aux cartes suivantes
    function planTurn(cands, apRoom, cost, cardsLeft, paNeed, apNow) {
      const tot = mons.filter(m => m.alive).reduce((a, m) => a + m.hp + m.shield, 0);
      const base = new Map(cands.map(c => [c, valueOf(c)]));
      const dmgNow = new Map(cands.map(c => [c, c.hasDmg ? Math.min(dmgCardValue(c, T.buffP, T.buffC, T.dmgPct), tot) : 0]));
      const buffOnly = c => !c.hasDmg && c.eff.every(l => l.k === 'buff' && l.tgt === 'self');
      let best = { v: -Infinity, seq: null }, nodes = 0;
      const seq = [], used = new Set();
      const rec = (apLeft, bp, bc, dp, v, dealt, nCards) => {
        if (++nodes > (opts.planNodes || 120)) return;
        const endOk = paNeed == null || apNow - (apRoom - apLeft) === paNeed || apLeft < Math.min(...cands.map(cost));
        if (seq.length && endOk && v > best.v) best = { v, seq: seq.slice() };
        for (const c of cands) {
          if (used.has(c)) continue;
          const k = cost(c); if (k > apLeft) continue;
          if (!c.weapon && nCards >= cardsLeft) continue;
          let dv, nbp = bp, nbc = bc, ndp = dp, nd = dealt;
          for (const l of c.eff) if (l.k === 'buff' && l.tgt === 'self') { if (l.stat === 'puissance') nbp += l.max; else if (l.stat === 'critique') nbc += l.max; else if (l.stat === 'dmgPctSorts') ndp += l.max; }
          if (buffOnly(c)) dv = 0;
          else if (c.hasDmg) { const raw = Math.min(dmgCardValue(c, bp, bc, dp), Math.max(0, tot - dealt)); nd += raw; dv = raw + (base.get(c) - dmgNow.get(c)); ndp += chainPct; }
          else dv = base.get(c);
          used.add(c); seq.push(c);
          rec(apLeft - k, nbp, nbc, ndp, v + dv, nd, nCards + (c.weapon ? 0 : 1));
          seq.pop(); used.delete(c);
        }
      };
      rec(apRoom, T.buffP, T.buffC, T.dmgPct, 0, 0, 0);
      return best.v > 0 ? best.seq : null;
    }
    function valueOf(c) {
      let v = 0;
      if (c.hasDmg) {
        const raw = dmgCardValue(c, T.buffP, T.buffC, T.dmgPct);
        const tot = mons.filter(m => m.alive).reduce((a, m) => a + m.hp + m.shield, 0);
        v += Math.min(raw, tot);
      }
      for (const l of c.eff) {
        if (l.k === 'buff' && l.tgt === 'self') {
          const others = hand.filter(h => h !== c && h.hasDmg);
          if (!others.length && !(opts.weapon && !T.weaponUsed)) continue;
          const pool = others.concat(opts.weapon && !T.weaponUsed ? [opts.weapon] : []);
          let gain = 0;
          for (const o of pool.slice(0, 3)) {
            const base = dmgCardValue(o, T.buffP, T.buffC, T.dmgPct);
            const withB = dmgCardValue(o, T.buffP + (l.stat === 'puissance' ? l.max : 0), T.buffC + (l.stat === 'critique' ? l.max : 0), T.dmgPct + (l.stat === 'dmgPctSorts' ? l.max : 0));
            gain += withB - base;
          }
          v += gain * 0.9;
        }
        if ((l.k === 'shieldHp' || l.k === 'shieldLvl') && T.invS) { v -= (l.k === 'shieldHp' ? maxHp * l.max / 100 : (opts.level || 200) * l.max / 100); continue; }
        if ((l.k === 'heal' || l.k === 'healPct') && l.tgt === 'self' && T.inv) { v -= (l.k === 'healPct' ? maxHp * l.max / 100 : (l.max + (S.soins || 0))); continue; }
        if (l.k === 'steal' && T.inv) { v -= 0.5 * expLine(S, l, 0, T.buffP, T.dmgPct, 0, 0, false, c.weapon); }
        if ((l.k === 'shieldHp' || l.k === 'shieldLvl') && T.sustainLeft > 0) {
          const amount = l.k === 'shieldHp' ? maxHp * l.max / 100 : (opts.level || 200) * l.max / 100;
          const room = Math.max(0, shieldCap - shieldTotal());
          v += Math.min(amount, room, incomingNext()) * 0.8;
        }
        if ((l.k === 'heal' || l.k === 'healPct') && l.tgt === 'self' && T.sustainLeft > 0 && !c.hasDmg) {
          const amount = l.k === 'healPct' ? maxHp * l.max / 100 : (l.max + (S.soins || 0));
          v += Math.min(amount, maxHp - P.hp) * 0.8;
        }
        if (l.k === 'apRemove' && l.tgt === 'enemy') {
          const t = c.weapon ? null : target();
          if (t) v += incomingNext() / Math.max(1, mons.filter(m => m.alive).length) * (WEAKEN_PER_PA * Math.max(0, l.max)) / 100 * 0.8;
        }
        if (l.k === 'apGain') v += l.max * 60;
      }
      if (c.hasDmg && !c.weapon) {
        // Onde de choc : deux sorts de dégâts du même élément d'affilée te blessent
        const sh = mv('shockPct', 0);
        if (sh && T.lastEl != null && mainEl(c) === T.lastEl) v -= maxHp * sh / 100 * 1.5;
        // Miroir : une zone qui touche le boss qui renvoie te blesse
        const rf = alive().find(reflects);
        if (rf && c.dmgLines.some(l => l.zone)) v -= dmgCardValue(c, T.buffP, T.buffC, T.dmgPct) / Math.max(1, alive().length) * 1.5;
      }
      // Peau dure : sans bouclier, tes dégâts sont réduits ; le bouclier devient prioritaire
      if (shieldTotal() <= 0 && alive().some(m => m.mech && m.mech.hardSkin) && c.eff.some(l => l.k === 'shieldHp' || l.k === 'shieldLvl')) v += 5000;
      return v;
    }
    // estimation du bonus de passif si on joue c maintenant (planification)
    function estPct(m, c) {
      if (!PK) return 0; const sv = C.cur; const w = c.weapon;
      C.cur = { portal: PK === 'eliotrope' && (C.att + 1) % 2 === 0, lance: PK === 'forgelance' && !C.firstDone && !w };
      let v = clsPct(m, c);
      if (PK === 'huppermage' && !w && c.hasDmg && !C.runes.has(mainEl(c)) && C.runes.size < 4) v += 11;
      if (PK === 'ouginak' && !w && m !== C.prey) v = 0;
      C.cur = sv; return v;
    }
    function ecaF(c) { return ECA && !c.weapon && c.hasDmg ? 1.31 : 1; }
    // charges du passif après un sort
    function passiveAfter(c) {
      if (!PK) return; const w = c.weapon;
      const has = k => c.eff.some(l => k.includes(l.k));
      if (PK === 'feca' && !w && (has(['shieldHp', 'shieldLvl', 'heal', 'healPct']) || c.eff.some(l => l.k === 'buff' && /^res/.test(l.stat || '')))) C.n = Math.min(5, C.n + 1);
      else if (PK === 'enutrof' && !w && c.ap <= 2) C.n = Math.min(10, C.n + 1);
      else if (PK === 'xelor') { const n = c.eff.filter(l => l.k === 'apRemove' || l.k === 'apSteal').reduce((a, l) => a + (l.max || 0), 0); C.n = Math.min(10, C.n + n); }
      else if (PK === 'eniripsa' && !w && has(['shieldHp', 'shieldLvl', 'heal', 'healPct'])) C.n = Math.min(5, C.n + 1);
      else if (PK === 'pandawa' && !w) C.n = Math.min(6, C.n + 1);
      else if (PK === 'huppermage' && !w && c.hasDmg) C.runes.add(mainEl(c));
      else if (PK === 'ouginak' && !w && c.hasDmg && C.lastTgt) { if (C.prey !== C.lastTgt) { C.prey = C.lastTgt; C.preyN = 0; } C.preyN = Math.min(5, C.preyN + 1); }
      if (PK === 'forgelance' && !w && c.hasDmg) C.firstDone = true;
      C.cur = null;
    }
    function mainEl(c) { const l = c.dmgLines && c.dmgLines[0]; return l ? (l.el || 0) : null; }
    // Mort d'un monstre ; certains boss se relèvent une fois (« se relève, fou de rage ») avec une part de leurs PV (inconnue : 50 % par défaut)
    function down(m) {
      if (m.mech && m.mech.revive && !m.revived) { m.revived = true; m.hp = Math.max(1, Math.round(m.cap * (m.mech.revivePct != null ? m.mech.revivePct / 100 : opts.revivePct != null ? opts.revivePct : 0.5))); m.rage += m.mech.reviveRage === 0 ? 0 : 2; m.shield = 0; m.bombs = []; return; }
      m.alive = false;
      if (PK === 'ouginak' && m === C.prey && C.inTurn && !C.ougPa) { C.ougPa = true; T.apNow = (T.apNow || 0) + 2; } // Proie tuée pendant son tour : +2 PA
    }
    function hit(m, line, label, opt) {
      opt = opt || {};
      const rp = er(m.res[RES_PCT[line.el || 0]] || 0);
      let d = dmgLine(S, line, opt.crit, T.buffP, T.dmgPct, opt.spec, rp, opt.fixed !== false, opt.weapon, PK ? clsPct(m, opt.card || null, opt.bomb) : 0);
      if (opt.luck) d = Math.floor(d * opt.luck);
      if (opt.sec) d = Math.floor(d * ZONE_SEC);
      if (opt.x2) d *= 2;
      if (m.mech && m.mech.hardSkin && shieldTotal() <= 0) d = Math.floor(d * m.mech.hardSkin / 100);
      // Dofawa : chaque coup a 0,1 % de chances de tuer net la cible (effet caché rapporté par les joueurs ; le Kralamoure de la Faille est supposé immunisé)
      if (DF.dofawa && d > 0 && !opt.bomb && !m.noOS && RND() < DOFAWA_P) d = m.hp + m.shield;
      if (reflects(m)) {
        // « renvoie le coup » : le monstre ne prend rien et te renvoie les dégâts (tes boucliers absorbent)
        let back = d; for (const s of P.shields) { const a = Math.min(s.value, back); s.value -= a; back -= a; if (!back) break; }
        P.hp -= back; hpLost += back; return 0;
      }
      const absorbed = Math.min(m.shield, Math.floor(d * (1 - (S._perfo || 0) / 100))); m.shield -= absorbed; const real = Math.min(m.hp, d - absorbed);
      if (opts.log) opts.log.push([T.round, label, m.name, d, !!opt.crit, !!opt.sec]);
      if (DF.glaces && real > 0) m.glaces = T.round + 1;
      m.hp -= real; if (S._ero) m.cap = Math.max(1, m.cap - real * S._ero / 100); dmgDone += real; perCard[label] = (perCard[label] || 0) + real;
      if (m.hp <= 0) { m.hp = 0; down(m); }
      return real;
    }
    function play(c) {
      const critP = c.cc > 0 ? Math.min(100, c.cc + (S.critique || 0) + T.buffC) : 0;
      const crit = RND() * 100 < critP;
      if (crit && DF.turquoise) critTurn = true;
      const x2 = !pourpreUsed && c.hasDmg && !c.weapon; if (x2) pourpreUsed = true; // Pourpre : le premier sort de dégâts du combat ×2
      const critArg = crit ? ((c.crit && c.crit.length) ? true : 'boost') : false;
      const lines = crit && c.crit ? c.crit : c.eff;
      if (PK && c.hasDmg) { C.att++; C.cur = { portal: PK === 'eliotrope' && C.att % 2 === 0, lance: PK === 'forgelance' && !C.firstDone && !c.weapon }; } else C.cur = null;
      C.inTurn = true;
      let luck = 1; if (ECA && !c.weapon && c.hasDmg) { const r = RND(); luck = r < 0.32 ? 2 : r < 0.34 ? 0.5 : 1; } // Chance d'Ecaflip
      const spec = !c.weapon && c.hasDmg && RND() < specP;  // Vision spectrale : tout le sort est doublé (toutes cibles et lignes, vérifié dans le journal)
      if (c.hasDmg && !c.weapon) {
        const el = mainEl(c), sh = mv('shockPct', 0);
        if (sh && T.lastEl != null && el === T.lastEl) { let d = Math.floor(maxHp * sh / 100); for (const s2 of P.shields) { const a = Math.min(s2.value, d); s2.value -= a; d -= a; if (!d) break; } P.hp -= d; hpLost += d; }
        T.lastEl = el;
      }
      let first = true; let tgt = target();
      const chosen = c.chanceLines.length ? [c.chanceLines[Math.floor(RND() * c.chanceLines.length)]] : null;
      let sustainUsed = false;
      for (const l of lines) {
        if (chosen && l.chance && l !== chosen[0] && !(crit && c.crit)) continue;
        if (l.k === 'dmg' || l.k === 'steal') {
          const withFixed = c.weapon ? true : first; first = false;
          if (l.zone) { if (!tgt || !tgt.alive) tgt = target(); for (const m of [tgt, ...mons.filter(x => x !== tgt)]) if (m && m.alive) { hit(m, l, c.name, { crit: critArg, spec, fixed: withFixed, weapon: c.weapon, sec: m !== tgt, x2, card: c, luck }); } }
          else {
            if (!tgt || !tgt.alive) tgt = target(); if (!tgt) break;
            const r = hit(tgt, l, c.name, { crit: critArg, spec, fixed: withFixed, weapon: c.weapon, x2, card: c, luck });
            if (l.k === 'steal') healP(Math.floor(r / 2));
          }
        } else if (l.k === 'dmgCasterHp') {
          if (!tgt || !tgt.alive) tgt = target(); if (!tgt) break;
          const d = Math.floor(maxHp * l.max / 100 * (1 - (tgt.res.resPctNeutre || 0) / 100));
          const real = Math.min(tgt.hp, d); tgt.hp -= real; dmgDone += real; perCard[c.name] = (perCard[c.name] || 0) + real; if (tgt.hp <= 0) { tgt.hp = 0; down(tgt); }
        } else if (l.k === 'bomb') {
          if (!tgt || !tgt.alive) tgt = target(); if (tgt) tgt.bombs.push(l);
        } else if (l.k === 'buff' && l.tgt === 'self') {
          if (l.stat === 'puissance') T.buffP += l.max; else if (l.stat === 'critique') T.buffC += l.max; else if (l.stat === 'dmgPctSorts') T.dmgPct += l.max; else if (CARACS_ALL.includes(l.stat)) S._cb[l.stat] = (S._cb[l.stat] || 0) + l.max;
          if ((l.dur || 1) > 1) pers.push({ stat: l.stat, v: l.max, until: T.round + l.dur - 1 });
        } else if (l.k === 'stealStat' && CARACS_ALL.includes(l.stat)) {
          // Vol de caractéristique : la carac volée s'ajoute à la tienne pendant la durée (dès ce tour)
          S._cb[l.stat] = (S._cb[l.stat] || 0) + l.max; if ((l.dur || 1) > 1) pers.push({ stat: l.stat, v: l.max, until: T.round + l.dur - 1 });
        } else if (l.k === 'shieldHp' || l.k === 'shieldLvl') {
          if (T.sustainLeft <= 0 && !sustainUsed) continue;
          sustainUsed = true;
          const amount = Math.floor(l.k === 'shieldHp' ? maxHp * l.max / 100 : (opts.level || 200) * l.max / 100);
          if (T.invS) { P.hp -= amount; hpLost += amount; continue; }
          const room = Math.max(0, shieldCap - shieldTotal());
          P.shields.push({ value: Math.min(amount, room), turns: l.dur || 1 });
        } else if ((l.k === 'heal' || l.k === 'healPct') && l.tgt === 'self') {
          if (!c.hasDmg) { if (T.sustainLeft <= 0 && !sustainUsed) continue; sustainUsed = true; }
          const amount = Math.floor((l.k === 'healPct' ? maxHp * l.max / 100 : (l.max + (S.soins || 0))) * (PK === 'eniripsa' ? 1 + 0.09 * C.n : 1));
          healP(amount);
        } else if (l.k === 'apRemove' && l.tgt === 'enemy') {
          const n = l.max; if (n <= 0) continue;
          if (l.zone || !c.weapon) { for (const m of mons) if (m.alive && (l.zone || m === tgt || !tgt)) m.weaken = Math.min(100, m.weaken + WEAKEN_PER_PA * n); }
          else if (tgt) tgt.weaken = Math.min(100, tgt.weaken + WEAKEN_PER_PA * n);
        } else if (l.k === 'apGain') { if (l.now) T.apNow = (T.apNow || 0) + l.max; else P.apNext += l.max; }
      }
      if (sustainUsed) T.sustainLeft--;
      if (PK && c.hasDmg && !c.weapon) { const t0 = tgt && tgt.alive ? tgt : null; C.lastTgt = tgt || null;
        if (PK === 'sadida' && t0) { t0.poison = t0.poison || []; if (t0.poison.length < 4) t0.poison.push(3); else { t0.poison.sort((a, b) => a - b); t0.poison[0] = 3; } } }
      C.inTurn = false;
    }
  }

  // Tirages : aléatoires par défaut ; avec une graine, chaque combat i rejoue les mêmes tirages d'un build à l'autre
  // (nombres aléatoires communs : les écarts mesurés entre deux builds viennent du build, pas de la chance)
  let RND = Math.random;
  function mulberry32(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
  function shuffle(a) { for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(RND() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; }

  function runMany(opts, n) {
    let wins = 0, rounds = 0, hp = 0, dmg = 0, prog = 0, kills = 0; const per = {}; const hist = {};
    const seeded = opts.seed != null;
    for (let i = 0; i < n; i++) {
      if (seeded) RND = mulberry32(opts.seed * 1000003 + i);
      let r; try { r = simulateFight(opts); } finally { if (seeded) RND = Math.random; }
      if (r.win) { wins++; rounds += r.rounds; hist[r.rounds] = (hist[r.rounds] || 0) + 1; }
      hp += r.hpLost; dmg += r.dmgDone; prog += r.progress || 0; kills += r.kills || 0;
      for (const k in r.perCard) per[k] = (per[k] || 0) + r.perCard[k];
    }
    for (const k in per) per[k] = per[k] / n;
    return { n, winRate: wins / n, avgRounds: wins ? rounds / wins : Infinity, avgHpLost: hp / n, avgDmg: dmg / n, perCard: per, hist, progress: prog / n, avgKills: kills / n };
  }


  // ---------- Mécaniques cachées du bestiaire ----------
  // Une entrée : {mn, d:'F'|'N'|'D'|'C'|combinaisons, asc:[a,b], ch, beyond, zone, second, + un code (fu, pd, oc, ms, sc, ds, mi, pa, ra, vp, ev)}
  function diffForFloor(fl) { return fl <= 2 ? 'F' : fl <= 5 ? 'N' : fl <= 8 ? 'D' : 'C'; }
  function bestiaryEntries(card, ctx) {
    if (!card || !card.m) return [];
    ctx = ctx || {};
    if (ctx.floor) {
      const d = diffForFloor(ctx.floor);
      const asc = card.m.filter(e => e.asc && ctx.floor >= e.asc[0] && ctx.floor <= e.asc[1]);
      if (asc.length) return asc;
      return card.m.filter(e => !e.asc && String(e.d).includes(d));
    }
    if (ctx.diff) return card.m.filter(e => String(e.d).includes(ctx.diff) && (!ctx.second || true));
    return card.m;
  }
  function mechFromEntries(list) {
    const o = {};
    for (const e of list || []) {
      if (e.fu) { o.furyCards = e.fu[0]; o.furyMult = e.fu[1]; }
      if (e.pd) o.hardSkin = e.pd;
      if (e.oc) o.shockPct = e.oc;
      if (e.ms) { if (e.ms[1] === 'half') o.healHalfFrom = e.ms[0]; else o.invertFrom = e.ms[0]; }
      if (e.sc) o.sealEvery = e.sc;
      if (e.ds) { o.revive = true; o.revivePct = e.ds[0]; o.reviveRage = e.ds[1] ? 1 : 0; }
      if (e.mi) { o.reflectFrom = e.mi[0]; o.reflectTo = e.mi[1]; }
      if (e.pa) { o.paTurn = e.pa[0]; o.paLeft = e.pa[1]; }
      if (e.ra) o.rageTurn = e.ra;
      if (e.vp) { o.apStealEvery = e.vp; o.apSteal = 1; }
      if (e.ev) { o.swapTurn = e.ev[0]; o.swapHalf = !!e.ev[1]; }
    }
    return o;
  }
  function mechText(e) {
    const t = [];
    if (e.fu) t.push(`Fureur : plus de ${e.fu[0]} cartes dans le tour (arme exclue) → sa prochaine attaque ×${String(e.fu[1]).replace('.', ',')}`);
    if (e.pd) t.push(`Peau dure : sans bouclier sur toi, seuls ${e.pd} % de tes dégâts passent`);
    if (e.oc) t.push(`Onde de choc : deux sorts de dégâts du même élément d'affilée → ${e.oc} % de tes PV max`);
    if (e.ms) t.push(e.ms[1] === 'half' ? `Malédiction : soins divisés par deux dès le tour ${e.ms[0]}` : `Malédiction : tes soins te blessent dès le tour ${e.ms[0]}`);
    if (e.sc) t.push(`Sceau : ${e.sc === 1 ? 'à chaque tour' : 'tous les ' + e.sc + ' tours'}, ta carte la plus chère est scellée`);
    if (e.ds) t.push(`Deuxième souffle : se relève avec ${e.ds[0]} % de PV${e.ds[1] ? ', fou de rage' : ''}`);
    if (e.mi) t.push(`Miroir : ${e.mi[0] === e.mi[1] ? 'au tour ' + e.mi[0] : 'aux tours ' + e.mi[0] + ' à ' + e.mi[1]}, chaque coup porté t'est renvoyé`);
    if (e.pa) t.push(`PA comptés : au tour ${e.pa[0]}, finis avec exactement ${e.pa[1]} PA`);
    if (e.ra) t.push(`Rage : au tour ${e.ra}, il t'achève`);
    if (e.vp) t.push(`Vol de PA : ${e.vp === 1 ? 'à chaque tour' : 'tous les ' + e.vp + ' tours'}, −1 PA`);
    if (e.ev) t.push(`Échange de vie au tour ${e.ev[0]}${e.ev[1] ? ' (à moitié)' : ''} s'il est plus entamé que toi`);
    return t.join(' · ');
  }
  // Ce que le mode auto ne sait pas gérer (le jeu à la main est alors conseillé)
  function autoWarnings(mech) {
    const w = [];
    if (mech.furyCards) w.push(`l'auto joue toutes ses cartes : la Fureur (> ${mech.furyCards} cartes) se déclenche à chaque tour`);
    if (mech.reflectFrom) w.push(`l'auto continue de frapper pendant le Miroir (tour${mech.reflectTo && mech.reflectTo !== mech.reflectFrom ? 's ' + mech.reflectFrom + '-' + mech.reflectTo : ' ' + mech.reflectFrom})`);
    if (mech.paTurn) w.push(`l'auto ne compte pas ses PA au tour ${mech.paTurn}`);
    if (mech.shockPct) w.push(`l'auto n'alterne pas les éléments (Onde de choc)`);
    return w;
  }
  const api = { BREED_KEY, BREED_NAME, CLASS_SPECTRAL, deriveStats, setAutoOrder: v => { AUTO_ORDER = v; }, setTuning: o => { if (o.crit != null) CRIT_MULT = o.crit; if (o.zoneSec != null) ZONE_SEC = o.zoneSec; if (o.weaponLast != null) WEAPON_LAST = o.weaponLast; if (o.weaponMode) WEAPON_MODE = o.weaponMode; }, CLASS_PASSIVE, dofusFx, forgePctFor, forgeDaysTo, forgeXpAt, diffForFloor, bestiaryEntries, mechFromEntries, mechText, autoWarnings, itemStats, weaponWithFusion, tierCost, allocCost, pointsTotal, computeStats, prepCard, weaponCard, simulateFight, runMany, STAT_TIERS, CARAC_OF_EL, EL_NAMES, RES_PCT, RES_FIX };
  if (typeof module !== 'undefined' && module.exports) module.exports = api; else root.RPG = api;
})(__labo);
  return __labo.RPG; })(); /*__ENGINE_END__*/

  // ---------- Stockage local (navigateur uniquement) ----------
  let db = load(); let recLoaded = false;
  // relecture de l'historique complet dans IndexedDB, puis fusion avec ce qui a été enregistré entre-temps
  recReady.then(() => {
    for (const k of ['labo-rec-v1', 'labo-rec-v1-saison']) { if (REC[k] == null) { let l = null; try { l = localStorage.getItem(k); } catch (e) {} if (l) recSet(k, l); } else { try { const l = localStorage.getItem(k); if (l) { const a = JSON.parse(REC[k]), b = JSON.parse(l); if (a && b && a.fights && b.fights) recSet(k, JSON.stringify(mergeRec(a, b))); else localStorage.removeItem(k); } } catch (e) {} } }
    try { const v = localStorage.getItem('labo-vitrines'); if (v && REC['labo-vitrines'] == null) recSet('labo-vitrines', v); else if (v) localStorage.removeItem('labo-vitrines'); } catch (e) {}
    const stored = load(); db = (stored.fights.length || Object.keys(stored.monsters).length) ? mergeRec(stored, db) : db; recLoaded = true; save();
    try { render(); } catch (e) {}
  });
  // relecture des textes déjà vus avec les nouvelles règles (ex. « renvoie le coup »)
  try {
    for (const m of Object.values(db.monsters)) if (m.mech && m.mech.texts) {
      const tx = Object.keys(m.mech.texts);
      // ancien faux positif : les dégâts renvoyés étaient pris pour des soins inversés
      if (tx.some(t => /renvoie le coup/i.test(t)) && !tx.some(t => /Malédiction|Inversion des soins\s*!/i.test(t))) { for (const t of tx) if (/^Inversion des soins : /.test(t)) delete m.mech.texts[t]; m.mech.parsed = {}; }
      m.mech.parsed = m.mech.parsed || {};
      for (const [t, v] of Object.entries(m.mech.texts)) parseMechanic(m.mech.parsed, t, (v && v.firstRound) || 1);
    }
  } catch (e) {}
  // v2.6.1 : nettoyage des étages pollués par des boss de donjon (comptés à tort comme étages d'Ascension)
  try {
    if (!db.migAsc1) {
      const nm = k => String(k).split('#')[0];
      const stN = f => (f.bossStats || []).map(b => nm(b.k));
      const pageRead = f => !!(f.power || f.difficulty || (stN(f).length && (f.bosses || []).length && !stN(f).some(x => f.bosses.includes(x))));
      const maxPage = Math.max(0, ...Object.values(db.floors).filter(pageRead).map(f => +f.floor));
      let maxOk = 0;
      for (const [n, f] of Object.entries(db.floors)) {
        if (+n > maxPage && !pageRead(f)) { delete db.floors[n]; continue; }
        const sn = stN(f);
        if (sn.length && (f.bosses || []).length && !sn.some(x => f.bosses.includes(x))) { delete f.bossStats; delete f.bossKeys; f.attempts = 0; f.wins = 0; for (const k of Object.keys(f.mech || {})) if (!f.bosses.includes(nm(k))) delete f.mech[k]; }
        maxOk = Math.max(maxOk, +n);
      }
      for (const b of db.bossLogs || []) if (b.floor && (!db.floors[b.floor] || !(b.mons || []).some(m => (db.floors[b.floor].bosses || []).includes(nm(m.k))))) b.floor = null;
      try { const cf = +localStorage.getItem(floorKey()) || 0; if (cf > maxOk + 1) localStorage.setItem(floorKey(), String(maxOk + 1)); } catch (e) {}
      db.migAsc1 = 1;
    }
  } catch (e) {}
  try { for (const b of db.bossLogs || []) if (b.floor && db.floors[b.floor] && !db.floors[b.floor].bossStats && b.mons) db.floors[b.floor].bossStats = b.mons.map(m => ({ k: m.k, maxHp: m.maxHp, atk: m.atk })); } catch (e) {}
  setTimeout(() => { try { save(); } catch (e) {} }, 1500);
  function load() {
    try { const d = JSON.parse(recGet(keyFor(PROFILE)) || 'null'); if (d && d.fights && d.monsters) { d.bossSamples = d.bossSamples || {}; d.seen = d.seen || []; d.floors = d.floors || {}; d.bossLogs = d.bossLogs || []; return d; } } catch (e) {}
    return { fights: [], monsters: {}, seen: [], bossSamples: {}, floors: {}, bossLogs: [] };
  }
  function loadBuilds() { try { return JSON.parse(localStorage.getItem(BUILDS_KEY) || 'null') || { builds: [] }; } catch (e) { return { builds: [] }; } }
  let saveTimer = null;
  function save() {
    clearTimeout(saveTimer);
    saveTimer = setTimeout(() => {
      if (db.fights.length > MAX_FIGHTS) db.fights.splice(0, db.fights.length - MAX_FIGHTS);
      if (db.seen.length > 500) db.seen.splice(0, db.seen.length - 500);
      // IndexedDB : pas de plafond de 5 Mo, rien n'est plus supprimé pour faire de la place (v2.9.6)
      if (!recLoaded) return; // tant que l'historique complet n'est pas relu, on n'écrase pas IndexedDB avec la version partielle
      recSet(keyFor(PROFILE), JSON.stringify(db));
    }, 400);
  }

  // ---------- Lecture des réponses du jeu ----------
  function parseRsc(text) {
    const out = [];
    for (const line of text.split('\n')) {
      const m = line.match(/^([0-9a-f]+):([\[{].*)$/);
      if (!m) continue;
      try { out.push(JSON.parse(m[2])); } catch (e) {}
    }
    return out;
  }
  function resolveIn(root, v) {
    if (typeof v === 'string' && /^\$1:/.test(v)) { let c = root; for (const k of v.slice(3).split(':')) c = c && c[k]; return c; }
    return v;
  }
  let context = {};
  function screenContext(screen) {
    const c = {};
    if (!screen) return c;
    for (const [k, v] of Object.entries(screen)) {
      if (v === null || typeof v === 'object') continue;
      if (/^(onPath|onAscension|huntZone|prestige|level)$/.test(k) || /asc|etage|floor|stage|abys|faille|boss|path|zone|dimension|vague|wave|guild/i.test(k)) c[k] = v;
    }
    return c;
  }
  function onPayload(text) {
    if (text.indexOf('"state"') < 0 && text.indexOf('"screen"') < 0) return;
    for (const obj of parseRsc(text)) {
      if (obj && obj.screen) { context = screenContext(obj.screen); context.ascScreen = !!context.onAscension; if (context.onAscension) { const fl = currentFloor(); if (fl) context.floor = fl; } }
      const st = obj && (obj.state || (obj.screen && obj.screen.initial));
      if (!st || !st.fighters) continue;
      const root = obj;
      trackTurn(st);
      if (st.kind === 'boss' || st.ascension) { const af = ascFloorFor(st); context.onAscension = !!af; context.floor = af; }
      collectMonsters(st, root);
      learnMechanics(st, root);
      maybeWarn(st, root);
      if (st.status && st.status !== 'active' && st.status !== 'ongoing' && st.status !== 'pending') collectFight(st, root, obj.rewards);
    }
  }

  // ---------- Tours du joueur (pour apprendre comment le mode auto choisit ses cartes) ----------
  // Lecture seule : on note la main en début de tour, les PA, puis les cartes réellement jouées et dans quel ordre.
  const turnBuf = {};
  function fightId(st) { const mons = Object.values(st.fighters).filter(f => f && f.kind !== 'player'); return [st.kind, mons.map(m => (m.name || '') + m.maxHp).join(',')].join('|'); }
  function cardName(P, uid) { const c = P.cards && P.cards[uid]; return c ? c.name : uid; }
  function trackTurn(st) {
    try {
      const P = st.fighters && st.fighters.p; if (!P || !Array.isArray(P.hand)) return;
      const id = fightId(st); let b = turnBuf[id] = turnBuf[id] || { turns: {} };
      if (b.logged && (st.status === 'ongoing' || st.status === 'active')) b = turnBuf[id] = { turns: {} };
      const r = st.round; const T = b.turns[r] = b.turns[r] || { r, hand: null, ap: null, auto: false };
      if (st.auto) T.auto = true;
      if (st.currentId === 'p' && !(P.cardsThisTurn > 0) && !T.hand) {
        T.hand = P.hand.map(u => { const c = P.cards && P.cards[u]; return c ? { n: c.name, ap: c.ap } : { n: u }; });
        T.ap = P.ap; T.hp = P.hp; T.maxHp = P.maxHp; T.sealed = (P.sealed || []).map(u => cardName(P, u));
        T.mons = Object.values(st.fighters).filter(f => f && f.kind !== 'player' && f.alive).map(f => ({ n: f.name, hp: f.hp, max: f.maxHp, sh: (f.shields || []).reduce((a, x) => a + (x.value || 0), 0) }));
      }
      if (P.played && P.played.length) T.played = P.played.map(u => cardName(P, u));
      if (P.weaponUsed) T.weapon = true;
      if (st.status && st.status !== 'ongoing' && st.status !== 'active' && st.status !== 'pending' && !b.logged) {
        b.logged = true;
        // ordre exact depuis le journal
        let cur = 0; const order = {};
        for (const e of st.log || []) { if (e.t === 'round') cur = e.round; if (e.t === 'play' && e.who === 'p') (order[cur] = order[cur] || []).push(e.card); }
        const turns = Object.values(b.turns).map(t => Object.assign(t, { order: order[t.r] || t.played || [] })).filter(t => t.hand || t.order.length);
        if (turns.length) { db.turnLogs = (db.turnLogs || []).concat(turns.map(t => Object.assign({ t: Date.now(), kind: st.kind, asc: !!st.ascension, won: st.status === 'won', autoUsed: !!st.autoUsed }, t))); if (db.turnLogs.length > 600) db.turnLogs.splice(0, db.turnLogs.length - 600); }
        const ids = Object.keys(turnBuf); if (ids.length > 20) delete turnBuf[ids[0]];
      }
    } catch (e) {}
  }
  function autoTurnCount(st) { const b = turnBuf[fightId(st)]; return b ? Object.values(b.turns).filter(t => t.auto).length : null; }
  function monsterKey(f) { return f.name + '#' + f.grade; }
  function collectMonsters(st, root) {
    for (const f of Object.values(st.fighters)) {
      if (!f || f.kind !== 'monster') continue;
      const pattern = resolveIn(root, f.pattern), stats = resolveIn(root, f.stats);
      if (!Array.isArray(pattern) || typeof stats !== 'object') continue;
      const k = monsterKey(f);
      const m = db.monsters[k];
      const ctx = Object.keys(context).length ? JSON.stringify(context) : null;
      if (!m) db.monsters[k] = { name: f.name, monsterId: f.monsterId, level: f.level, grade: f.grade, hpMin: f.maxHp, hpMax: f.maxHp, atk: f.atk, element: f.element, pattern, stats, isBoss: !!f.isBoss, xp: f.xp, gfx: imgField(f), seen: 1, ctx: ctx ? [ctx] : [] };
      else {
        m.hpMin = Math.min(m.hpMin, f.maxHp); m.hpMax = Math.max(m.hpMax, f.maxHp); m.seen = (m.seen || 0) + 1; m.isBoss = m.isBoss || !!f.isBoss; if (!m.gfx) m.gfx = imgField(f);
        if (ctx && !(m.ctx || []).includes(ctx)) (m.ctx = m.ctx || []).push(ctx);
      }
      // champs inconnus d'un boss : on garde un échantillon pour analyse
      if (f.isBoss && !db.bossSamples[k]) { try { db.bossSamples[k] = JSON.stringify(f).slice(0, 20000); } catch (e) {} }
    }
  }

  // ---------- Étage d'Ascension (lu sur la page Ascension) ----------
  // Étage d'Ascension d'un combat : seulement si l'écran dit Ascension (ou si les boss correspondent à ceux lus sur la page de l'étage).
  // Un boss de donjon (kind 'boss' hors Ascension) n'est jamais compté comme étage.
  function ascFloorFor(st) {
    const fl = context.floor || currentFloor(); if (!fl) return 0;
    const names = Object.values(st.fighters || {}).filter(f => f && f.kind === 'monster').map(f => f.name);
    const f = db.floors[fl], page = f && f.bosses && f.bosses.length ? f.bosses : null;
    if (page) return names.some(n => page.includes(n)) ? fl : 0;
    return (st.ascension || context.ascScreen) ? fl : 0;
  }
  function currentFloor() { try { return +localStorage.getItem(floorKey()) || 0; } catch (e) { return 0; } }
  function readAscensionPage() {
    if (!/\/ascension/.test(location.pathname) || !document.body) return;
    const txt = document.body.innerText || '';
    const m = txt.match(/ÉTAGE ACTUEL\s*(\d+)/i) || txt.match(/Étage\s+(\d+)\s*·/);
    if (!m) return;
    const fl = +m[1];
    try { localStorage.setItem(floorKey(), String(fl)); } catch (e) {}
    const f = db.floors[fl] = db.floors[fl] || { floor: fl, bosses: [], attempts: 0, wins: 0, hints: [], mech: {} };
    const pw = txt.match(/puissance ×\s*([\d.,]+)/); if (pw) f.power = parseFloat(pw[1].replace(',', '.'));
    const diff = txt.match(/difficulté\s+([A-Za-zÀ-ÿ]+)/); if (diff) f.difficulty = diff[1];
    const after = txt.split(/ÉTAGE\s+\d+\s*·[^\n]*\n/i)[1] || '';
    const names = [...after.matchAll(/^(.+)\n\s*Boss\s*$/gm)].map(x => x[1].trim()).slice(0, 3);
    if (names.length) f.bosses = names;
    save();
    previewAscension(fl, f);
  }
  let lastPreview = '';
  function previewAscension(fl, f) {
    const names = (f.bosses || []).filter(Boolean); if (!names.length) return;
    const B = loadBest();
    if ((!B || !B.mech || Date.now() - (B.t || 0) > 864e5) && !bestFetching && Date.now() - bestTriedAt > 6e5) { bestFetching = true; bestTriedAt = Date.now(); fetchBestiary(false).then(() => { bestFetching = false; lastPreview = ''; previewAscension(fl, f); }).catch(() => { bestFetching = false; }); }
    const sig = fl + '|' + names.join(',') + '|' + (B && B.t || 0);
    if (sig === lastPreview) return; lastPreview = sig;
    const hidden = names.map(n => ({ n, e: bestEntriesFor(n, fl) })).filter(x => x.e && x.e.length);
    const known = Object.values(db.monsters).filter(m => names.includes(m.name) && mechSummary(m).length);
    const keys = Object.keys(db.monsters).filter(k => names.includes(db.monsters[k].name));
    const builds = loadBuilds().builds.filter(b => (b.targets || []).some(t => keys.includes(t)));
    if (!hidden.length && !known.length && !builds.length) return;
    showBanner(known, builds, f, hidden, fl, null, true);
  }
  setInterval(readAscensionPage, 3000);


  // ---------- Bonus de panoplie (lus sur la page Personnage, palier par palier) ----------
  const SETS_KEY = 'labo-sets-v1';
  const STAT_FR = { vitalite: 'vitalite', sagesse: 'sagesse', force: 'force', intelligence: 'intelligence', chance: 'chance', agilite: 'agilite', puissance: 'puissance', critique: 'critique', dommages: 'dommages', dommagesneutre: 'dommagesNeutre', dommagesterre: 'dommagesTerre', dommagesfeu: 'dommagesFeu', dommageseau: 'dommagesEau', dommagesair: 'dommagesAir', dommagescritiques: 'dommagesCritiques', dommagespoussee: 'dommagesPoussee', soins: 'soins', prospection: 'prospection', initiative: 'initiative', resistancecritiques: 'resCritiques', resistancepoussee: 'resPoussee', tacle: 'tacle', fuite: 'fuite', pa: 'pa', pm: 'pm', po: 'po', portee: 'po', invocations: 'invocations', invocation: 'invocations', retraitpa: 'retraitPA', retraitpm: 'retraitPM', esquivepa: 'esquivePA', esquivepm: 'esquivePM' };
  function statKey(label, pct) {
    const n = label.normalize('NFD').replace(/[̀-ͯ]/g, '').toLowerCase().replace(/[^a-z]/g, '');
    const r = n.match(/^resistance(neutre|terre|feu|eau|air)$/);
    if (r) return (pct ? 'resPct' : 'res') + r[1][0].toUpperCase() + r[1].slice(1);
    return STAT_FR[n] || null;
  }
  function loadSets() { try { return JSON.parse(localStorage.getItem(SETS_KEY) || '{}') || {}; } catch (e) { return {}; } }
  function readSetsPage() {
    if (!/\/personnage/.test(location.pathname) || !document.body) return;
    const t = document.body.innerText || ''; const i = t.indexOf('PANOPLIES'); if (i < 0) return;
    const seg = t.slice(i, i + 3000);
    const sets = loadSets(); let changed = false;
    for (const m of seg.matchAll(/^(.+?)\s*\((\d+)\/(\d+)\)\s*\n\s*(\d+)\s*objets?\s*:\s*(.+)$/gm)) {
      const name = m[1].trim(), size = +m[3], k = +m[4], st = {};
      for (const part of m[5].split('·')) { const x = part.trim().match(/^([+-]?\d+)\s*(%?)\s*(.+)$/); if (!x) continue; const key = statKey(x[3], !!x[2]); if (key) st[key] = (st[key] || 0) + (+x[1]); }
      if (!Object.keys(st).length) continue;
      const o = sets[name] = sets[name] || { size, tiers: {} }; o.size = size;
      if (JSON.stringify(o.tiers[k]) !== JSON.stringify(st)) { o.tiers[k] = st; changed = true; }
    }
    if (changed) try { localStorage.setItem(SETS_KEY, JSON.stringify(sets)); } catch (e) {}
  }
  setInterval(readSetsPage, 3000);
  // v2.11.2 : « Équipements enregistrés » (page Personnage) lus à l'écran : nom, objets, caracs. Le jeu ne les envoie pas dans les données de la page.
  const PRESETS_DOM_KEY = 'labo-presets-dom';
  const CAR_FR = { vita: 'vitalite', vitalite: 'vitalite', 'vitalité': 'vitalite', chance: 'chance', force: 'force', intel: 'intelligence', intelligence: 'intelligence', agi: 'agilite', 'agilité': 'agilite', agilite: 'agilite', sagesse: 'sagesse', sag: 'sagesse' };
  function readPresetsPage() {
    if (!/\/personnage/.test(location.pathname) || !document.body) return;
    const head = [...document.querySelectorAll('h1,h2,h3,h4,h5,h6,div,span,p')].find(e => e.children.length === 0 && /^\s*équipements enregistrés\s*$/i.test(e.textContent || ''));
    if (!head) return;
    let box = head; for (let k = 0; k < 6 && box && box.querySelectorAll('input').length < 2; k++) box = box.parentElement;
    if (!box) return;
    const out = [];
    for (const inp of box.querySelectorAll('input')) {
      let card = inp; for (let k = 0; k < 5 && card.parentElement && card.parentElement.querySelectorAll('input').length === 1; k++) card = card.parentElement;
      const leaves = [...card.querySelectorAll('*')].filter(e => e.children.length === 0).map(e => (e.textContent || '').trim()).filter(Boolean);
      const listTxt = leaves.find(x => /^\d+\s*objets?\s*:/i.test(x)) || '';
      const items = listTxt ? listTxt.replace(/^\d+\s*objets?\s*:\s*/i, '').split(/\s*,\s*/).map(s => s.replace(/[.…]+$/, '').trim()).filter(Boolean) : [];
      const car = {}; for (const x of leaves) for (const m of x.matchAll(/(Vita(?:lité)?|Chance|Force|Intel(?:ligence)?|Agi(?:lité)?|Sag(?:esse)?)\s+(\d+)/gi)) { const k2 = CAR_FR[m[1].toLowerCase()]; if (k2) car[k2] = +m[2]; }
      out.push({ name: (inp.value || '').trim() || (inp.placeholder || '').trim(), n: +((listTxt.match(/^(\d+)/) || [])[1] || 0), items, car, empty: !items.length });
    }
    if (out.length) { try { localStorage.setItem(PRESETS_DOM_KEY, JSON.stringify({ t: Date.now(), presets: out })); } catch (e) {} }
  }
  setInterval(readPresetsPage, 3000);
  function presetsFromDom(I, best) {
    let raw = null; try { raw = JSON.parse(localStorage.getItem(PRESETS_DOM_KEY) || 'null'); } catch (e) {}
    if (!raw || !raw.presets) return null;
    const byName = {}; const add = (it, f) => { if (!it || !it.n) return; const o = byName[it.n]; if (!o || (f || 0) > o.f) byName[it.n] = { id: it.id, s: it.s, f: f || 0 }; };
    for (const e of (I.entries || [])) add(e.item, e.fusion); for (const e of (I.slots || [])) add(e.item, e.fusion); for (const it of ((best && best.items) || [])) if (!byName[it.n]) add(it, 0);
    return raw.presets.map((p, i) => {
      const gear = {}, cnt = {}; const miss = [];
      for (const nm of p.items) { const x = byName[nm]; if (!x) { miss.push(nm); continue; } let slot = x.s; if (x.s === 'anneau') slot = gear.anneau1 ? 'anneau2' : 'anneau1'; else if (x.s === 'dofus') { let k = 1; while (gear['dofus' + k] && k < 6) k++; slot = 'dofus' + k; } if (!gear[slot]) gear[slot] = { id: x.id, f: x.f }; }
      return { i, name: p.name || ('Équipement ' + (i + 1)), gear, alloc: Object.keys(p.car || {}).length ? p.car : null, src: 'dom', missing: miss, listed: p.n, t: raw.t };
    });
  }


  // ---------- Panoplies d'origine (base publique DofusDB : mêmes identifiants que le jeu) ----------
  // Observé : au palier k objets, le jeu donne le bonus DOFUS de k+1 objets (plafonné à la panoplie complète).
  const DOFUS_SETS_KEY = 'labo-dofus-sets-v1';
  const CHAR_KEY = { 1: 'pa', 10: 'force', 11: 'vitalite', 12: 'sagesse', 13: 'chance', 14: 'agilite', 15: 'intelligence', 16: 'dommages', 18: 'critique', 19: 'po', 23: 'pm', 25: 'puissance', 26: 'invocations', 27: 'esquivePA', 28: 'esquivePM', 33: 'resPctTerre', 34: 'resPctFeu', 35: 'resPctEau', 36: 'resPctAir', 37: 'resPctNeutre', 44: 'initiative', 48: 'prospection', 49: 'soins', 54: 'resTerre', 55: 'resFeu', 56: 'resEau', 57: 'resAir', 58: 'resNeutre', 78: 'fuite', 79: 'tacle', 82: 'retraitPA', 83: 'retraitPM', 84: 'dommagesPoussee', 85: 'resPoussee', 86: 'dommagesCritiques', 87: 'resCritiques', 88: 'dommagesTerre', 89: 'dommagesFeu', 90: 'dommagesEau', 91: 'dommagesAir', 92: 'dommagesNeutre' };
  const MALUS_EFFECTS = new Set([116, 145, 152, 153, 154, 155, 156, 157, 168, 169, 171, 175, 176, 179, 186, 215, 216, 217, 218, 219, 245, 246, 247, 248, 249, 411, 413, 415, 417, 419, 421, 423, 425, 427, 429, 431, 433, 435, 437, 439, 441, 443]);
  async function fetchDofusSets(ids) {
    let cache = {}; try { cache = JSON.parse(localStorage.getItem(DOFUS_SETS_KEY) || '{}') || {}; } catch (e) {}
    const todo = [...new Set(ids)].filter(id => id && !cache[id]);
    for (let i = 0; i < todo.length; i += 40) {
      const q = todo.slice(i, i + 40).map(id => 'id[$in][]=' + id).join('&');
      try {
        const j = await origFetch('https://api.dofusdb.fr/item-sets?$limit=50&' + q).then(r => r.json());
        for (const set of (j.data || [])) {
          const tiers = {};
          (set.effects || []).forEach((eff, idx) => { const st = {}; for (const e of eff || []) { const k = CHAR_KEY[e.characteristic]; if (!k) continue; st[k] = (st[k] || 0) + (MALUS_EFFECTS.has(e.effectId) ? -1 : 1) * (e.from || 0); } if (Object.keys(st).length) tiers[idx + 1] = st; });
          cache[set.id] = { n: set.name && (set.name.fr || set.name.en), size: (set.items || []).length || (set.effects || []).length, tiers };
        }
      } catch (e) { break; }
    }
    try { localStorage.setItem(DOFUS_SETS_KEY, JSON.stringify(cache)); } catch (e) {}
    return cache;
  }

  // ---------- Apprentissage des mécaniques spéciales ----------
  function learnMechanics(st, root) {
    const mons = Object.values(st.fighters).filter(f => f && f.kind === 'monster');
    if (!mons.length) return;
    const order = (st.order || []).filter(id => st.fighters[id] && st.fighters[id].kind === 'monster');
    const ordered = order.length ? order.map(id => st.fighters[id]) : mons;
    const bosses = ordered.filter(f => f.isBoss);
    const dead = new Set();
    const source = () => { const b = bosses.find(f => !dead.has(f.id)); return b ? [monsterKey(b)] : (bosses.length ? [] : ordered.map(monsterKey)); };
    const floor = context.onAscension ? context.floor : 0;
    let round = 1, changed = false, who = null, lastCard = null, lastCardHeals = false;
    const Pf = st.fighters.p || {};
    const healNames = new Set(Object.values(resolveIn(root, Pf.cards) || {}).concat(Pf.weaponCard ? [Pf.weaponCard] : [])
      .filter(c => c && Array.isArray(c.eff) && c.eff.some(l => ['heal', 'healPct', 'steal', 'shieldHp', 'shieldLvl'].includes(l.k))).map(c => c.name));
    const named = text => { const hit = ordered.filter(f => text.indexOf(f.name) >= 0); return hit.length ? [...new Set(hit.map(monsterKey))] : null; };
    const note = (text, r, keys) => {
      for (const k of (keys || named(text) || source())) {
        const m = db.monsters[k]; if (!m) continue;
        m.mech = m.mech || { texts: {}, intents: {}, parsed: {} };
        const t = m.mech.texts[text] || (m.mech.texts[text] = { n: 0, firstRound: r });
        t.n++; t.firstRound = Math.min(t.firstRound, r);
        parseMechanic(m.mech.parsed, text, r);
        if (floor) { const f = db.floors[floor] = db.floors[floor] || { floor, bosses: [], attempts: 0, wins: 0, hints: [], mech: {} }; const fm = f.mech[k] = f.mech[k] || { texts: {}, parsed: {} }; fm.texts[text] = Math.min(fm.texts[text] || 99, r); parseMechanic(fm.parsed, text, r); }
        changed = true;
      }
    };
    let reflected = false;
    for (const e of st.log || []) {
      if (e.t === 'round') round = e.round || round;
      if (e.t === 'turn') { who = e.who; lastCard = null; lastCardHeals = false; reflected = false; }
      if (e.t === 'death' && e.who) dead.add(e.who);
      if (e.t === 'play' && e.who === 'p') { lastCard = e.card; lastCardHeals = healNames.has(e.card); reflected = false; }
      if (e.t === 'mechanic' && /renvoie le coup/i.test(e.text || '')) reflected = true;
      // soin inversé sans prévention : le joueur se blesse pendant son propre tour juste après un soin, un vol de vie ou un bouclier
      if (e.t === 'dmg' && e.who === 'p' && who === 'p' && lastCard && lastCardHeals && !reflected) note('Inversion des soins : ' + lastCard + ' a blessé au lieu de soigner', round);
      if (e.t === 'mechanic' && e.text && !/Vision spectrale/.test(e.text)) note(e.text.replace(/\d{3,}/g, 'N'), round);
      if (e.t === 'intent' && e.k && !KNOWN_INTENT.has(e.k)) note('Intention spéciale : ' + e.k, round);
      if (e.t && !KNOWN_LOG.has(e.t)) note('Événement : ' + e.t + (e.text ? ' — ' + e.text : ''), round);
    }
    const P = st.fighters.p;
    if (P && Array.isArray(P.sealed) && P.sealed.length) note('Sceau actif sur tes cartes', st.round || 1);
    if (P && P.exhaustArmed) note('Épuisement : passe ton tour, attaquer soigne le boss', st.round || 1);
    // indice affiché à la mort
    let hint = typeof st.hint === 'string' ? st.hint : (st.hint && (st.hint.text || st.hint.message)) || null;
    if (hint && /^\$/.test(hint)) hint = null;
    if (hint && st.status && st.status !== 'active') {
      const keys = source().length ? source() : ordered.map(monsterKey);
      for (const k of keys) { const m = db.monsters[k]; if (!m) continue; m.mech = m.mech || { texts: {}, intents: {}, parsed: {} }; m.mech.hints = m.mech.hints || []; if (!m.mech.hints.includes(hint)) m.mech.hints.push(hint); parseMechanic(m.mech.parsed, hint, st.round || 1); }
      if (floor) { const f = db.floors[floor] = db.floors[floor] || { floor, bosses: [], attempts: 0, wins: 0, hints: [], mech: {} }; if (!f.hints.includes(hint)) f.hints.push(hint); }
      changed = true;
    }
    if (changed) save();
  }
  function parseMechanic(p, text, r) {
    const tm = String(text).match(/tour\s+(\d+)/i); if (tm) r = +tm[1];
    if (/Inversion|soins?.{0,40}(blessent|blessé|blessaient|dégâts)/i.test(text)) { p.invertFrom = Math.min(p.invertFrom || 99, r); if (/bouclier/i.test(text)) p.invertShields = true; }
    const seal = text.match(/Sceau[^0-9+]*\+?\s*(\d+)\s*PA/i);
    if (seal) { p.sealPa = Math.max(p.sealPa || 0, +seal[1]); p.sealFrom = Math.min(p.sealFrom || 99, r); }
    if (/Échange de PV/i.test(text)) p.hpSwapFrom = Math.min(p.hpSwapFrom || 99, r);
    if (/Épuisement/i.test(text)) p.exhaust = true;
    if (/scelle .+ pour ce tour/i.test(text)) { p.sealCard = true; p.sealCardFrom = Math.min(p.sealCardFrom || 99, r); }
    const steal = text.match(/vole\s+(\d+)\s*PA/i); if (steal) { p.apSteal = Math.max(p.apSteal || 0, +steal[1]); p.apStealFrom = Math.min(p.apStealFrom || 99, r); }
    if (/se relève/i.test(text)) p.revive = true;
    if (/renvoie le coup/i.test(text)) p.reflectFrom = Math.min(p.reflectFrom || 99, r);
    if (/Malédiction.*soins.*bless/i.test(text)) { p.invertFrom = Math.min(p.invertFrom || 99, r); }
    if (/Enragé/i.test(text)) p.enraged = true;
  }
  function mechSummary(m) {
    if (!m || !m.mech) return [];
    const p = m.mech.parsed || {}, out = [];
    if (p.invertFrom) out.push(`Soins inversés dès le tour ${p.invertFrom}${p.invertShields ? ', boucliers compris' : ''} : pas de soin ni de vol de vie`);
    if (p.sealPa) out.push(`Sceau : +${p.sealPa} PA sur ta 1re carte de chaque tour (dès le tour ${p.sealFrom})`);
    if (p.hpSwapFrom) out.push(`Échange de PV dès le tour ${p.hpSwapFrom} : garde peu de PV d'avance`);
    if (p.exhaust) out.push('Épuisement : passe ton tour quand il est annoncé, attaquer le soigne');
    if (p.enraged) out.push('Enragé : combat manuel obligatoire');
    if (p.sealCard) out.push(`Scelle une de tes cartes chaque tour (dès le tour ${p.sealCardFrom})`);
    if (p.apSteal) out.push(`Te vole ${p.apSteal} PA (dès le tour ${p.apStealFrom})`);
    if (p.reflectFrom) out.push(`Renvoie les coups dès le tour ${p.reflectFrom} : le tuer avant, ou arrêter de le frapper`);
    if (p.revive) out.push('Se relève une fois, fou de rage, avec une 2e mécanique');
    for (const [t, v] of Object.entries(m.mech.texts || {})) if (!/Inversion|Sceau|Échange de PV|Épuisement|Enragé|scelle|vole \d+ PA|se relève|Malédiction|renvoie le coup/i.test(t)) out.push(`${t} (vu ${v.n} fois, dès le tour ${v.firstRound})`);
    for (const h of (m.mech.hints || []).filter(x => x && !/^\$|undefined/.test(x)).slice(-2)) out.push('Indice à la mort : ' + String(h).replace(/^Indice\s*:\s*/i, ''));
    return out.slice(0, 7);
  }

  // ---------- Alerte quand un boss connu revient ----------
  let lastWarnSig = '';
  function maybeWarn(st, root) {
    if (st.status && st.status !== 'active' && st.status !== 'ongoing') return;
    const mons = Object.values(st.fighters).filter(f => f && f.kind === 'monster');
    const sig = mons.map(f => f.id).join(','); // pas les PV max : l'érosion les baisse à chaque coup (le calcul se relançait en boucle)
    if (!mons.length || sig === lastWarnSig) return;
    lastWarnSig = sig;
    const keys = [...new Set(mons.map(monsterKey))];
    const known = keys.map(k => db.monsters[k]).filter(m => m && (mechSummary(m).length || m.isBoss));
    const builds = loadBuilds().builds.filter(b => (b.targets || []).some(t => keys.includes(t)));
    const fl = context.onAscension && context.floor ? db.floors[context.floor] : null;
    const flN = context.onAscension ? (context.floor || 0) : 0;
    // mécaniques cachées connues par le bestiaire (cache local, rafraîchi au plus une fois par jour)
    const B = loadBest();
    if ((!B || !B.mech || Date.now() - (B.t || 0) > 864e5) && !bestFetching && Date.now() - bestTriedAt > 6e5 && mons.some(m => m.isBoss)) {
      bestFetching = true; bestTriedAt = Date.now(); fetchBestiary(false).then(() => { bestFetching = false; lastWarnSig = null; maybeWarn(st, root); }).catch(() => { bestFetching = false; });
    }
    const hidden = [...new Set(mons.filter(m => m.isBoss).map(m => m.name))].map(n => ({ n, e: bestEntriesFor(n, flN) })).filter(x => x.e && x.e.length);
    const g = guardCheck(st, root, flN, () => { lastWarnSig = null; maybeWarn(st, root); });
    if (!known.length && !builds.length && !(fl && fl.attempts) && !hidden.length && !g) return;
    showBanner(known, builds, fl, hidden, flN, !!(st.auto || st.autoUsed), false, g);
  }
  let banner = null;
  function showBanner(known, builds, fl, hidden, flN, isAuto, preview, guard) {
    hidden = hidden || [];
    if (!document.documentElement) return;
    const prevBanner = banner;
    banner = document.createElement('div');
    banner.setAttribute('role', 'status');
    banner.setAttribute('style', 'position:fixed;top:72px;right:12px;z-index:2147483001;width:min(400px,94vw);max-height:72vh;overflow:auto;font:13px/1.45 system-ui,sans-serif;color:#efe6d6;background:rgba(21,18,13,.97);border:1px solid #e0b04f;border-radius:10px;padding:8px 12px;box-shadow:0 6px 20px rgba(0,0,0,.5)');
    const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
    let folded = true; try { folded = localStorage.getItem('labo-banner-open') !== '1'; } catch (e) {}
    const title = `Labo · ${fl ? 'Ascension étage ' + fl.floor : flN ? 'Ascension étage ' + flN : 'adversaire connu'}${preview ? ' · avant le combat' : ''}`;
    // résumé court (toujours visible)
    let sum = '';
    const trapCount = hidden.reduce((a, x) => a + x.e.filter(e => e.fu || e.mi || e.pa || e.oc).length, 0);
    for (const x of hidden) sum += `<div><strong>${esc(x.n)}</strong> : ${x.e.map(e => esc(e.mn)).join(', ')}</div>`;
    if (!hidden.length) for (const m of known) { const n = mechSummary(m).length; if (n) sum += `<div><strong>${esc(m.name)}</strong> : ${n} mécanique${n > 1 ? 's' : ''} relevée${n > 1 ? 's' : ''}</div>`; }
    if (trapCount) sum += `<div style="color:#ec7a70">${trapCount} piège${trapCount > 1 ? 's' : ''} que le mode auto ne gère pas</div>`;
    if (builds.length) sum += `<div style="color:#8fc98a">Build conseillé disponible : ${esc(builds[0].label || '')}</div>`;
    let h = '';
    if (PROFILE === 'saison') sum = `<div style="color:#ec7a70;font-weight:600">Perso Héroïque : une défaite ici = mort définitive.</div>` + sum;
    if (guard) sum = guardHtml(guard, isAuto) + sum;
    if (fl) h += `<div style="color:#a89a85">${fl.attempts} tentative${fl.attempts > 1 ? 's' : ''} · ${fl.wins} victoire${fl.wins > 1 ? 's' : ''}${fl.power ? ' · puissance ×' + fl.power : ''}${fl.difficulty ? ' · ' + esc(fl.difficulty) : ''}</div>${(fl.hints || []).length ? '<div style="margin-top:4px">Indices relevés : ' + fl.hints.slice(-3).map(esc).join(' · ') + '</div>' : ''}`;
    if (hidden.length) {
      const d = flN ? ({ F: 'Facile', N: 'Normale', D: 'Difficile', C: 'Cauchemar' })[diffForFloor(flN)] : '';
      h += `<div style="margin-top:6px;border:1px solid #4a3f30;border-radius:8px;padding:6px 8px"><div style="color:#e0b04f;font-weight:600">Mécaniques cachées (bestiaire)${d ? ' · ' + d : ''}</div>`;
      const autoBad = [];
      for (const x of hidden) {
        h += `<div style="margin-top:3px"><strong>${esc(x.n)}</strong><ul style="margin:2px 0 0 18px;padding:0">${x.e.map(e => `<li><strong>${esc(e.mn)}</strong> : ${esc((e.x || '').replace(/\s+/g, ' '))}</li>`).join('')}</ul></div>`;
        for (const e of x.e) { if (e.fu) autoBad.push(`Fureur de ${x.n} : joue au plus ${e.fu[0]} cartes par tour (l'arme ne compte pas)`); if (e.mi) autoBad.push(`Miroir de ${x.n} : ne le frappe pas au${e.mi[0] === e.mi[1] ? ' tour ' + e.mi[0] : 'x tours ' + e.mi[0] + ' à ' + e.mi[1]}, zones comprises`); if (e.pa) autoBad.push(`PA comptés (${x.n}) : au tour ${e.pa[0]}, finis avec ${e.pa[1]} PA`); if (e.oc) autoBad.push(`Onde de choc (${x.n}) : alterne les éléments`); }
      }
      if (autoBad.length) h += `<div style="margin-top:5px;color:#ec7a70">${isAuto ? 'Le mode auto ne gère pas ça, passe en manuel :' : 'À jouer à la main :'}</div><ul style="margin:2px 0 0 18px;padding:0;color:#ec7a70">${autoBad.map(t => `<li>${esc(t)}</li>`).join('')}</ul>`;
      h += `</div>`;
    }
    for (const m of known) {
      const lines = mechSummary(m);
      h += `<div style="margin-top:6px"><strong>${esc(m.name)}</strong>${m.isBoss ? ' <span style="color:#ec7a70">boss</span>' : ''} · vu ${m.seen || 1} fois${lines.length ? '<ul style="margin:3px 0 0 18px;padding:0">' + lines.map(l => `<li>${esc(l)}</li>`).join('') + '</ul>' : '<div style="color:#a89a85">Aucune mécanique spéciale relevée pour l’instant.</div>'}</div>`;
    }
    for (const b of builds.slice(0, 2)) {
      h += `<div style="margin-top:8px;border-top:1px solid #4a3f30;padding-top:6px"><strong>Build conseillé : ${esc(b.label || 'sans nom')}</strong>${b.winRate != null ? ` · ${Math.round(b.winRate * 100)} % de victoires estimées` : ''}${b.note ? `<div style="color:#a89a85">${esc(b.note)}</div>` : ''}
        <div style="display:flex;gap:6px;flex-wrap:wrap;margin-top:4px">${b.gearCode ? `<button data-copy="${esc(b.gearCode)}" style="${btn(true)}">Copier le code d’équipement</button>` : ''}${b.deckCode ? `<button data-copy="${esc(b.deckCode)}" style="${btn()}">Copier le code de deck</button>` : ''}</div>${b.points ? `<div style="color:#a89a85;margin-top:3px">Points : ${esc(b.points)}</div>` : ''}</div>`;
    }
    h += `<div data-msg style="color:#a89a85;min-height:1em;margin-top:4px"></div>`;
    banner.innerHTML = `<div style="display:flex;justify-content:space-between;gap:8px;align-items:center"><strong style="color:#e0b04f">${esc(title)}</strong><span style="display:flex;gap:4px;flex:none"><button data-fold style="${btn()}">${folded ? 'Détails ▾' : 'Réduire ▴'}</button><button data-x style="cursor:pointer;background:none;border:0;color:#a89a85;font-size:16px;line-height:1" aria-label="Fermer">×</button></span></div><div style="margin-top:4px">${sum}</div><div data-body style="${folded ? 'display:none' : ''}">${h}</div>`;
    banner.addEventListener('click', async (ev) => {
      const tf = ev.target.closest && ev.target.closest('[data-fold]');
      if (tf) { const b = banner.querySelector('[data-body]'); const open = b.style.display === 'none'; b.style.display = open ? '' : 'none'; tf.textContent = open ? 'Réduire ▴' : 'Détails ▾'; try { localStorage.setItem('labo-banner-open', open ? '1' : '0'); } catch (e) {} return; }
      const t = ev.target;
      if (t.dataset.x !== undefined) { banner.remove(); banner = null; return; }
      if (t.dataset.copy) { try { await navigator.clipboard.writeText(t.dataset.copy); banner.querySelector('[data-msg]').textContent = 'Copié. Colle-le dans le jeu.'; } catch (e) { banner.querySelector('[data-msg]').textContent = t.dataset.copy; } }
    });
    // même contenu qu'affiché : on garde la fenêtre telle quelle (pas de clignotement)
    if (prevBanner && prevBanner.isConnected && prevBanner._html === banner.innerHTML) { banner = prevBanner; return; }
    banner._html = banner.innerHTML; if (prevBanner) prevBanner.remove();
    document.documentElement.appendChild(banner);
  }


  // ---------- Garde-fou : victoire estimée dès le début d'un combat de boss (calcul local, lecture seule) ----------
  // Le script relit tes cartes et ton arme (pages Deck et Inventaire, comme une page vue), puis simule le combat avec le moteur du Labo.
  const CAT_KEY = () => 'labo-cat-v1-' + PROFILE;
  function loadCat() { try { return JSON.parse(localStorage.getItem(CAT_KEY()) || 'null'); } catch (e) { return null; } }
  async function fetchCatalog() {
    const deck = await rsc('/deck'), inv = await rsc('/inventaire');
    const D = deck.find(p => p.collection && p.initialDecks), I = inv.find(p => p.entries && p.slots);
    if (!D) return null;
    const cat = { t: Date.now(), breedId: D.breedId, level: (I && I.level) || 200, cards: {}, weapons: {} };
    for (const c of D.collection) if (c.card && c.card.n) cat.cards[c.card.n] = { n: c.card.n, ap: c.card.ap, cc: c.card.cc, eff: c.card.eff, crit: c.card.crit || null };
    if (I) for (const x of (I.slots || []).concat(I.entries || [])) if (x && x.item && x.item.w) cat.weapons[x.item.n] = { id: x.item.id, n: x.item.n, w: x.item.w, f: x.fusion || 0 };
    try { localStorage.setItem(CAT_KEY(), JSON.stringify(cat)); } catch (e) {}
    return cat;
  }
  // simulation découpée en petits paquets pour ne jamais figer la page du jeu
  function runChunked(opts, n, done) {
    let left = n, acc = null;
    const step = () => {
      const k = Math.min(40, left); const r = LR.runMany(opts, k); left -= k;
      if (!acc) acc = { n: 0, wins: 0, rounds: 0, hp: 0, prog: 0 };
      acc.n += k; acc.wins += r.winRate * k; acc.rounds += isFinite(r.avgRounds) ? r.avgRounds * r.winRate * k : 0; acc.hp += r.avgHpLost * k; acc.prog += (r.progress || 0) * k;
      if (left > 0) setTimeout(step, 0); else done({ winRate: acc.wins / acc.n, avgRounds: acc.wins ? acc.rounds / acc.wins : Infinity, avgHpLost: acc.hp / acc.n, progress: acc.prog / acc.n });
    };
    setTimeout(step, 0);
  }
  let guardSig = '', guardRes = null;
  function guardCheck(st, root, flN, refresh) {
    try {
      if (!LR) return null;
      const P = st.fighters && st.fighters.p; if (!P) return null;
      const mons = Object.values(st.fighters).filter(f => f && f.kind === 'monster' && f.alive !== false);
      if (!mons.length || !(mons.some(m => m.isBoss) || st.kind === 'boss' || st.ascension)) return null;
      const sig = PROFILE + '|' + mons.map(m => m.id).join(','); // recalcul seulement quand un monstre meurt, pas à chaque coup
      if (sig === guardSig) return guardRes;
      guardSig = sig; guardRes = { pending: true };
      (async () => {
        try {
          const cardsObj = resolveIn(root, P.cards) || {};
          const names = Object.values(cardsObj).map(c => c && c.name).filter(Boolean);
          const wc = resolveIn(root, P.weaponCard); const wn = wc && wc.name;
          let cat = loadCat();
          if (!cat || Date.now() - cat.t > 6 * 36e5 || names.some(n => !cat.cards[n]) || (wn && !cat.weapons[wn])) { try { cat = (await fetchCatalog()) || cat; } catch (e) {} }
          if (!cat) { guardRes = { err: 'cartes introuvables (ouvre la page Deck une fois)' }; refresh(); return; }
          const deck = names.map(n => cat.cards[n]).filter(c => c && c.eff && c.eff.length).map((c, i) => LR.prepCard(c, 'c' + i));
          const wi = wn && cat.weapons[wn]; const weapon = wi ? LR.weaponCard(wi, wi.f || 0) : null;
          const S = LR.deriveStats(resolveIn(root, P.stats) || {}, { maxHp: P.maxHp, basePa: P.basePa, breedId: cat.breedId });
          const B = loadBest();
          const defs = mons.map(m => {
            const card = B && B.mech && B.mech.find(c => c.n === m.name);
            const es = card ? LR.bestiaryEntries(card, { floor: flN || 0 }) : [];
            const k = monsterKey(m), learned = (db.monsters[k] && db.monsters[k].mech && db.monsters[k].mech.parsed) || {};
            const hp = m.hp != null ? m.hp : m.maxHp;
            return { name: m.name, hpMin: hp, hpMax: hp, atk: m.atk, element: m.element, pattern: resolveIn(root, m.pattern), stats: resolveIn(root, m.stats) || {}, isBoss: !!m.isBoss, mech: Object.assign({}, learned, LR.mechFromEntries(es)) };
          });
          if (!deck.length || defs.some(d => !Array.isArray(d.pattern) || !d.pattern.length)) { guardRes = { err: 'données du combat incomplètes' }; refresh(); return; }
          const base = { S, deck, weapon, monsters: defs, level: cat.level || 200, startHp: P.hp };
          runChunked(Object.assign({ auto: true }, base), 400, ra => {
            guardRes = { auto: ra, missing: names.length - deck.length, pending: 'manual' }; refresh();
            runChunked(Object.assign({ auto: false }, base), 200, rm => { guardRes = { auto: ra, manual: rm, missing: names.length - deck.length }; refresh(); });
          });
        } catch (e) { guardRes = { err: e.message }; refresh(); }
      })();
      return guardRes;
    } catch (e) { return null; }
  }
  function guardHtml(g, isAuto) {
    if (!g) return '';
    if (g.err) return `<div style="color:#a89a85">Chances de victoire : calcul impossible (${g.err}).</div>`;
    if (g.pending === true) return `<div style="color:#a89a85">Calcul de tes chances de victoire…</div>`;
    const col = w => w >= 0.99 ? '#8fc98a' : w >= 0.9 ? '#e0b04f' : '#ec7a70';
    const pc = w => (w >= 0.995 && w < 1 ? '>99' : Math.round(w * 100)) + ' %';
    const a = g.auto.winRate, m = g.manual ? g.manual.winRate : null;
    let h = `<div style="margin-bottom:3px">Victoire estimée : <strong style="color:${col(a)}">${pc(a)} en auto</strong>${m != null ? ` · <strong style="color:${col(m)}">${pc(m)} à la main</strong>` : g.pending ? ' · à la main : calcul…' : ''}</div>`;
    const best = Math.max(a, m != null ? m : 0);
    if (PROFILE === 'saison' && (m != null ? best : a) < 0.99) h += `<div style="color:#ec7a70;font-weight:700;margin-bottom:3px">Risque de mort définitive : ${Math.round((1 - (m != null ? best : a)) * 100)} % au mieux. Ne joue pas ce combat avec ce build : quitte-le si le jeu le permet sans pénalité, puis prépare un build dans le Labo (onglet Ascension).</div>`;
    else if (m != null && m - a >= 0.05) h += `<div style="color:#e0b04f;margin-bottom:3px">Mieux à la main (+${Math.round((m - a) * 100)} points) : évite le mode auto ici.</div>`;
    if (g.missing) h += `<div style="color:#a89a85">${g.missing} carte${g.missing > 1 ? 's' : ''} non reconnue${g.missing > 1 ? 's' : ''}, estimation moins sûre.</div>`;
    return h + `<div style="color:#a89a85;font-size:11px;margin-bottom:4px">Simulation du Labo (marge d'environ 5 %), mécaniques du bestiaire comprises.</div>`;
  }

  // Calibrage : on garde une fois les stats de combat et le deck de chaque build utilisé (pour comparer simulation et réalité)
  function buildSig(P, root) {
    try {
      const stats = resolveIn(root, P.stats) || {}; const cards = resolveIn(root, P.cards) || {};
      const deck = Object.values(cards).map(c => c && c.name).filter(Boolean).sort();
      const wc = resolveIn(root, P.weaponCard); const weapon = wc && wc.name || null;
      const keep = {}; for (const [k, v] of Object.entries(stats)) if (typeof v === 'number' && v) keep[k] = v;
      // signature sans la vitalité ni les PV max (ils bougent de quelques points à chaque combat) : un même build garde la même fiche ; les PV max sont notés sur chaque combat
      const core = Object.assign({}, keep); delete core.vitalite;
      const sig = 'b2:' + JSON.stringify([core, deck, weapon, P.basePa]).length + ':' + deck.join('|').length + ':' + Object.values(core).reduce((a, v) => a + v, 0);
      db.builds = db.builds || {};
      if (!db.builds[sig]) { db.builds[sig] = { t: Date.now(), stats: keep, deck, weapon, maxHp: P.maxHp, basePa: P.basePa }; const ks = Object.keys(db.builds); if (ks.length > 150) delete db.builds[ks[0]]; }
      return sig;
    } catch (e) { return null; }
  }

  // Journal détaillé : derniers combats (événements compacts) + catalogue de tous les messages de combat (passifs, mécaniques, effets de sorts)
  function journalFight(st, mons) {
    try {
      const names = {}; for (const [id, f] of Object.entries(st.fighters || {})) if (f) names[id] = f.kind === 'player' ? 'moi' : (f.name || id);
      let round = 0, card = null; const ev = [];
      db.texts = db.texts || {};
      for (const e of st.log || []) {
        if (e.t === 'round') { round = e.round; continue; }
        if (e.t === 'play') card = e.who === 'p' ? e.card : null;
        if (e.t === 'turn' && e.who !== 'p') card = null;
        const x = [round, names[e.who] || e.who || '', e.t];
        if (e.card) x.push(e.card); if (e.v != null) x.push(e.v); if (e.el != null) x.push('el' + e.el); if (e.crit) x.push('crit'); if (e.absorbed) x.push('abs' + e.absorbed); if (e.k) x.push(e.k); if (e.text) x.push(e.text);
        if (ev.length < 600) ev.push(x);
        if (e.text) {
          const key = String(e.text).replace(/\d+([.,]\d+)?/g, '#').slice(0, 160);
          const o = db.texts[key] = db.texts[key] || { n: 0, ex: String(e.text).slice(0, 220), who: names[e.who] || e.who || '', cards: {} };
          o.n++; if (card) o.cards[card] = (o.cards[card] || 0) + 1;
        }
      }
      const ks = Object.keys(db.texts); if (ks.length > 400) for (const k of ks.slice(0, ks.length - 400)) delete db.texts[k];
      db.journal = db.journal || [];
      db.journal.push({ t: Date.now(), kind: st.kind, status: st.status, rounds: st.round, auto: !!(st.auto || st.autoUsed), mons: mons.map(monsterKey), ev });
      if (db.journal.length > 25) db.journal.splice(0, db.journal.length - 25);
    } catch (e) {}
  }
  function collectFight(st, root, rewards) {
    const P = st.fighters.p; if (!P) return;
    const mons = Object.values(st.fighters).filter(f => f && f.kind === 'monster');
    // empreinte du combat : les dégâts tirés au hasard rendent chaque combat unique (en AFK, le même groupe revient avec le même nombre de tours et les mêmes PV)
    let lh = 0x811c9dc5; for (const e of st.log || []) { const x = (e.t || '') + (e.who || '') + (e.card || '') + (e.v != null ? e.v : ''); for (let i = 0; i < x.length; i++) { lh ^= x.charCodeAt(i); lh = Math.imul(lh, 16777619); } }
    const sig = [st.kind, mons.map(m => m.id + m.maxHp).join(','), st.logCount, st.round, P.hp, (lh >>> 0).toString(36)].join('|');
    if (db.seen.includes(sig)) return;
    db.seen.push(sig);
    journalFight(st, mons);
    const perCard = {}; let cur = null, crits = 0, plays = 0, spectral = 0, dmgTaken = 0, healTaken = 0;
    for (const e of st.log || []) {
      if (e.t === 'play' && e.who === 'p') { cur = e.card; plays++; if (e.crit) crits++; }
      if (e.t === 'turn' && e.who !== 'p') cur = null;
      if (e.t === 'mechanic' && /Vision spectrale/.test(e.text || '')) spectral++;
      if (e.t === 'dmg' && e.who !== 'p' && cur) perCard[cur] = (perCard[cur] || 0) + (e.v || 0);
      if (e.t === 'dmg' && e.who === 'p') dmgTaken += (e.v || 0);
      if (e.t === 'heal' && e.who === 'p') healTaken += (e.v || 0);
    }
    const flFight = context.onAscension ? (context.floor || null) : null;
    if (st.kind === 'boss' || st.ascension) {
      const fl = flFight;
      if (fl) {
        const f = db.floors[fl] = db.floors[fl] || { floor: fl, bosses: [], attempts: 0, wins: 0, hints: [], mech: {} };
        f.attempts++; if (st.status === 'won') f.wins++; f.bossKeys = mons.map(monsterKey); f.bossStats = mons.map(m => ({ k: monsterKey(m), maxHp: m.maxHp, atk: m.atk, stats: resolveIn(root, m.stats), pattern: resolveIn(root, m.pattern) })); if (!f.bosses || !f.bosses.length) f.bosses = mons.map(m => m.name);
        if (st.status === 'won') { try { localStorage.setItem(floorKey(), String(fl + 1)); } catch (e) {} }
      }
      db.bossLogs.push({ t: Date.now(), floor: fl || null, status: st.status, round: st.round, mons: mons.map(m => ({ k: monsterKey(m), maxHp: m.maxHp, atk: m.atk })), log: (st.log || []).slice(0, 1500) });
      if (db.bossLogs.length > 12) db.bossLogs.splice(0, db.bossLogs.length - 12);
      context.floor = 0;
    }
    const rw = rewards || {};
    db.fights.push({
      bsig: buildSig(P, root), t: Date.now(), hid: typeof document !== 'undefined' && document.hidden ? 1 : 0, kind: st.kind, status: st.status, rounds: st.round, auto: !!(st.auto || st.autoUsed), afk: !!st.autoAfk, autoTurns: autoTurnCount(st), ctx: Object.assign({}, context), floor: flFight,
      mons: mons.map(monsterKey), boss: mons.some(m => m.isBoss),
      hpEnd: P.hp, maxHp: P.maxHp, dmgTaken, healTaken, plays, crits, spectral, perCard,
      xp: rw.xp || 0, kamas: rw.kamas || 0, items: (rw.items || []).map(i => (i && (i.n || (i.item && i.item.n))) || '?'), card: rw.card ? (rw.card.n || rw.card.name || '?') : null,
      level: rw.newLevel || P.level
    });
    save(); render();
  }


  // ---------- Perso suivi (principal / saison) ----------
  function profileLocked() { try { return localStorage.getItem('labo-profile-lock') === '1'; } catch (e) { return false; } }
  function setProfile(p, manual) {
    if (p !== 'saison') p = 'principal';
    if (manual) { try { localStorage.setItem('labo-profile-lock', '1'); } catch (e) {} }
    if (p === PROFILE) return;
    if (recLoaded) recSet(keyFor(PROFILE), JSON.stringify(db));
    PROFILE = p; try { localStorage.setItem('labo-profile', p); } catch (e) {}
    context = {}; // le contexte (zone, niveau, étage) de l'autre perso ne doit pas être réutilisé
    db = load(); lastWarnSig = ''; lastPreview = '';
    if (p === 'principal' && !bestFetching && Date.now() - bestTriedAt > 6e5) { bestFetching = true; bestTriedAt = Date.now(); fetchBestiary(false).then(() => { bestFetching = false; }).catch(() => { bestFetching = false; }); }
    try { render(); } catch (e) {}
  }
  // Le jeu indique dans ses données de page si c'est le perso de saison qui est joué (« seasonChar »)
  // La détection du jeu gagne toujours : un choix manuel contraire (clic par erreur) est annulé automatiquement.
  function detectProfile(text) {
    if (typeof text !== 'string' || text.indexOf('"seasonChar"') < 0) return;
    const all = [...text.matchAll(/"seasonChar":(true|false|null|\{|"\$)/g)];
    if (!all.length) return;
    const v = all[all.length - 1][1];
    const p = v === 'false' || v === 'null' ? 'principal' : 'saison';
    if (profileLocked() && p !== PROFILE) { try { localStorage.removeItem('labo-profile-lock'); } catch (e) {} profileFixed = `Corrigé : le jeu indique ton perso ${p === 'saison' ? 'Héroïque' : 'principal'}, le choix manuel a été annulé.`; }
    setProfile(p);
  }
  let profileFixed = '';
  setInterval(() => { try { const a = self.__next_f; if (Array.isArray(a) && a.length !== detectProfile.n) { detectProfile.n = a.length; const txt = a.map(x => Array.isArray(x) ? x[1] || '' : '').join(''); detectProfile(txt); onPayload(txt); } } catch (e) {} }, 3000);

  // Interception passive de fetch : on lit une copie de la réponse, la requête n'est pas modifiée
  const origFetch = window.fetch;
  window.fetch = async function (...args) {
    const res = await origFetch.apply(this, args);
    try {
      const req = args[0], init = args[1] || {};
      const method = (init.method || (req && req.method) || 'GET').toUpperCase();
      if (method === 'POST') res.clone().text().then(t => { detectProfile(t); onPayload(t); try { if (/\/bestiaire/.test(location.pathname)) { const L = JSON.parse(localStorage.getItem('labo-sniff') || '[]'); const h = {}; try { const H = init.headers || {}; for (const k in H) if (/^next-|^rsc|content-type/i.test(k)) h[k] = String(H[k]).slice(0, 300); } catch (e) {} L.unshift({ t: Date.now(), url: String(req && req.url || req).slice(0, 300), body: typeof init.body === 'string' ? init.body.slice(0, 600) : null, headers: h, resp: t.slice(0, 1500) }); localStorage.setItem('labo-sniff', JSON.stringify(L.slice(0, 4))); } } catch (e) {} }).catch(() => {});
      else if (/x-component/.test(res.headers && res.headers.get ? (res.headers.get('content-type') || '') : '')) res.clone().text().then(t => { detectProfile(t); onPayload(t); }).catch(() => {});
      const u0 = String(req && req.url || req);
      if (/\/bestiaire/.test(location.pathname) && !/\/api\/(chat|file)/.test(u0)) res.clone().text().then(t => { const got = harvestItems(t, method + ' ' + u0.slice(0, 120)); try { const L = JSON.parse(localStorage.getItem('labo-sniff') || '[]'); L.unshift({ t: Date.now(), m: method, url: u0.slice(0, 300), ct: res.headers.get('content-type'), len: t.length, lvl: (t.match(/"lvl"/g) || []).length, got, body: typeof init.body === 'string' ? init.body.slice(0, 400) : null, resp: t.slice(0, 800) }); localStorage.setItem('labo-sniff', JSON.stringify(L.slice(0, 15))); } catch (e) {} }).catch(() => {}); // rafraîchissements (ex. Auto AFK après rechargement)
    } catch (e) {}
    return res;
  };

  // ---------- Statistiques ----------
  function lastAgo() { const f = db.fights[db.fights.length - 1]; if (!f || !f.t) return 'aucun'; const s = Math.round((Date.now() - f.t) / 1000); return s < 90 ? `il y a ${s} s` : s < 5400 ? `il y a ${Math.round(s / 60)} min` : `il y a ${Math.round(s / 3600)} h`; }
  setInterval(() => { try { if (panel && !minimized && view === 'stats') render(); } catch (e) {} }, 15000);
  function summary(sinceMs) {
    const fs = db.fights.filter(f => f.t >= (sinceMs || 0));
    const won = fs.filter(f => f.status === 'won');
    const span = fs.length ? Math.max(60e3, Date.now() - Math.min(sinceMs || Infinity, fs[0].t)) : 0;
    const sum = (a, k) => a.reduce((s, f) => s + (f[k] || 0), 0);
    return {
      fights: fs.length, wins: won.length, winRate: fs.length ? won.length / fs.length : 0,
      avgRounds: won.length ? sum(won, 'rounds') / won.length : 0,
      xpH: span ? sum(fs, 'xp') / span * 3600e3 : 0, kamasH: span ? sum(fs, 'kamas') / span * 3600e3 : 0,
      items: fs.reduce((s, f) => s + f.items.length, 0), cards: fs.filter(f => f.card).length,
      monsters: Object.keys(db.monsters).length,
      bosses: Object.values(db.monsters).filter(m => m.isBoss).length
    };
  }

  // ---------- Export pour le Labo (lecture seule des pages Inventaire, Deck, Personnage) ----------
  async function exportForLabo() {
    const inv = await rsc('/inventaire'), deck = await rsc('/deck'), perso = await rsc('/personnage');
    let best = null; try { best = await fetchBestiary(true); } catch (e) { best = loadBest(); }
    const I = inv.find(p => p.entries && p.slots), D = deck.find(p => p.collection && p.initialDecks);
    const Pp = perso.find(p => p.rows && 'pointsFree' in p), H = perso.find(p => 'prestige' in p && 'level' in p && 'equipped' in p) || {};
    if (!I || !D || !Pp) throw new Error('pages introuvables (es-tu connecté ?)');
    let forge = null; try { const fp = await rsc('/forgemagie'); const F = fp.find(p => 'orbs' in p && 'level' in p && 'xp' in p); if (F) { forge = { level: F.level, xp: F.xp }; for (const k in F) { const v = F[k]; if (typeof v === 'number' && !(k in forge)) forge[k] = v; else if (Array.isArray(v) && v.length && v.length <= 250 && JSON.stringify(v).length < 20000) forge[k] = v; } } } catch (e) {}
    // Compagnon (patch du 10/10, perso principal) : niveau et bonus d'équipement, lus sur sa page si elle existe ; structure encore inconnue, on garde un extrait brut pour l'analyse
    let companion = null; if (PROFILE !== 'saison') for (const path of ['/compagnon', '/companion']) { try { const cp = await rsc(path); const holder = cp.find(p => p && p.initial && typeof p.initial === 'object' && ('kibble' in p.initial || 'bonusPct' in p.initial)); const C = (holder && holder.initial) || cp.find(p => p && typeof p === 'object' && !Array.isArray(p) && Object.keys(p).some(k => /croq|kibble|compan|pet|food/i.test(k))) || cp.find(p => p && typeof p === 'object' && 'level' in p && Object.keys(p).some(k => /bonus|pct|percent|mult/i.test(k))); if (C) { companion = { path }; for (const [k, v] of Object.entries(C)) { if (typeof v === 'number' || typeof v === 'string' && v.length < 60) companion[k] = v; } const pk = Object.keys(C).find(k => /bonus|pct|percent|statmult|mult/i.test(k) && typeof C[k] === 'number'); if ('bonusPct' in C) companion.pct = C.bonusPct; else if (pk) companion.pct = C[pk]; companion.raw = JSON.stringify(C).slice(0, 2000); break; } } catch (e) {} }
    let vitrines = null; try { vitrines = await fetchVitrines(false); } catch (e) {}
    let dofusSets = null; try { const ids = ((best && best.items) || []).map(x => x.setId).concat((I.sets || []).map(x => x.id)).concat((I.entries || []).map(e => e.item && e.item.setId).concat((I.slots || []).map(e => e.item && e.item.setId))); dofusSets = await fetchDofusSets(ids.filter(Boolean)); } catch (e) {}
    const it = (x) => ({ id: x.item.id, n: x.item.n, lvl: x.item.lvl, s: x.item.s, r: x.item.r, setId: x.item.setId || null, st: x.item.st, w: x.item.w || null, icon: x.item.icon || x.item.gfx || null });
    return {
      meta: { scriptV: (typeof GM_info !== 'undefined' && GM_info.script && GM_info.script.version) || '2.11.10', profile: PROFILE, forge, companion, level: I.level || 200, prestige: H.prestige || 0, breedId: D.breedId, deckSize: D.deckSize, discordBonus: 5, scrolls: I.scrollValues || {}, rows: Pp.rows.map(r => ({ key: r.key, base: r.base, bonus: r.bonus, tiers: r.tiers })), pointsFree: Pp.pointsFree, decks: D.initialDecks, deckNames: D.initialNames, active: D.initialActive, ranked: D.initialRanked || null, presets: (() => { try { return findPresets(perso) || presetsFromDom(I, best); } catch (e) { return null; } })(), presetsRaw: (() => { try { return presetsRaw(perso); } catch (e) { return null; } })(), diag: (() => { try { const s = Object.values(db.bossSamples || {})[0]; const o = s ? JSON.parse(s) : null; let pd = null; try { pd = JSON.parse(localStorage.getItem('labo-presets-dom') || 'null'); } catch (e) {} let ai = null; try { ai = JSON.parse(localStorage.getItem('labo-allitems-diag') || 'null'); } catch (e) {} let live = null; try { const L = JSON.parse(localStorage.getItem('labo-allitems-live') || 'null'); live = L ? { n: (L.items || []).length, log: L.log } : null; } catch (e) {} const objRaw = localStorage.getItem('labo-objets-raw'); let sn = null; try { sn = JSON.parse(localStorage.getItem('labo-sniff') || 'null'); } catch (e) {} return { allItems: ai, live, objRaw, sniff: sn, fighterKeys: o ? Object.keys(o) : null, mech: best && best.diag || null, presetsDom: pd ? { t: pd.t, n: (pd.presets || []).length } : null }; } catch (e) { return null; } })() },
      worn: I.slots.filter(s => s.item).map(s => Object.assign(it(s), { slot: s.slot, f: s.fusion })),
      items: I.entries.map(e => Object.assign(it(e), { f: e.fusion, q: e.qty })),
      cards: D.collection.map(c => ({ key: c.key, id: c.card.id, n: c.card.n, ap: c.card.ap, cc: c.card.cc, cls: c.card.cls, r: c.card.r, f: c.card.f, eff: c.card.eff, crit: c.card.crit || null, sig: !!c.card.sig, d: (c.card.d || '').slice(0, 180), ic: cardIcon(c.card) })),
      monsters: Object.values(db.monsters).map(m => Object.assign({}, m, { mech: m.mech ? Object.assign({}, m.mech.parsed, { texts: Object.keys(m.mech.texts || {}), hints: m.mech.hints || [] }) : undefined })),
      fights: db.fights.map(f => ({ rounds: f.rounds, status: f.status, hpEnd: f.hpEnd, mons: f.mons, kind: f.kind, ctx: f.ctx, boss: f.boss, t: f.t, floor: f.floor, auto: f.auto, afk: f.afk, hid: f.hid, bsig: f.bsig, perCard: f.perCard, plays: f.plays, crits: f.crits, dmgTaken: f.dmgTaken, maxHp: f.maxHp, xp: f.xp, kamas: f.kamas, items: f.items, card: f.card, level: f.level })),
      builds: db.builds || {},
      journal: db.journal || [],
      texts: db.texts || {},
      floors: Object.values(db.floors),
      turnLogs: db.turnLogs || [],
      setBonus: loadSets(),
      dofusSets,
      vitrines,
      setsList: (I.sets || []).map(x => ({ id: x.id, n: x.n, size: x.size, owned: x.owned })),
      bestiary: best
    };
  }

  // ---------- Vitrines publiques (stuffs les plus aimés) : lecture seule, une fois par jour au plus ----------
  async function rawRsc(path) {
    const h = await origFetch(path, { credentials: 'include' }).then(r => r.text());
    return [...h.matchAll(/self\.__next_f\.push\(\[1,"((?:[^"\\]|\\.)*)"\]\)/g)].map(m => { try { return JSON.parse('"' + m[1] + '"'); } catch (e) { return ''; } }).join('');
  }
  function jsonAt(t, i) { let d = 0, inS = false; for (let k = i; k < t.length; k++) { const c = t[k]; if (inS) { if (c === '\\') { k++; continue; } if (c === '"') inS = false; continue; } if (c === '"') { inS = true; continue; } if (c === '{') d++; else if (c === '}') { d--; if (!d) return t.slice(i, k + 1); } } return null; }
  async function fetchVitrines(force) {
    const KEY = 'labo-vitrines';
    await recReady; try { const c = JSON.parse(recGet(KEY) || 'null'); if (!force && c && Date.now() - c.t < 864e5) return c; } catch (e) {}
    const lst = await rawRsc('/vitrines?tri=meilleures');
    const ids = [...new Set([...lst.matchAll(/\/vitrines\/([0-9a-f-]{36})/g)].map(m => m[1]))].slice(0, 30);
    const items = {}, cards = {}, builds = [];
    for (const id of ids) {
      try {
        const t = await rawRsc('/vitrines/' + id);
        const its = []; let i = -1;
        while ((i = t.indexOf('"item":{', i + 1)) >= 0) { try { const o = JSON.parse(jsonAt(t, i + 7)); if (o && o.id && o.st) { items[o.id] = { id: o.id, n: o.n, lvl: o.lvl, s: o.s, r: o.r, st: o.st, w: o.w || null, setId: o.setId || null, icon: o.icon || o.gfx || null }; its.push(o.id); } } catch (e) {} }
        const deck = [...t.matchAll(/\["\$","div","(\d+)",\{"type":"\$undefined","onClick":"\$undefined","disabled":"\$undefined","title":"((?:[^"\\]|\\.)*)"[\s\S]{0,1500}?"aria-label":"(\d+) PA"[\s\S]{0,900}?line-clamp-2","children":"((?:[^"\\]|\\.)*)"\}\],\["\$","\$L[0-9a-z]+",null,\{"lines":(\[[^\]]*\])/g)].map(m => { const c = { id: +m[1], n: m[4], ap: +m[3], lines: (() => { try { return JSON.parse(m[5]); } catch (e) { return []; } })() }; cards[c.id] = c; return c.id; });
        const codes = [...new Set([...t.matchAll(/DM-[ES]-[0-9A-Z]+-[0-9A-Z]{4}/g)].map(m => m[0]))];
        const head = (t.match(/"h1"[^\]]{0,300}"children":"([^"]+)"/) || [])[1] || '';
        const likes = +((t.match(/"likes":(\d+)/) || [])[1] || 0);
        const breed = +((t.match(/\/img\/breeds\/symbol_(\d+)\.png"[^\]]{0,200}"alt":"[^"]+"/) || [])[1] || 0) || null;
        builds.push({ id, head, likes, breed, codes, items: its, deck });
      } catch (e) {}
      await new Promise(r => setTimeout(r, 300)); // poli avec le serveur
    }
    const out = { t: Date.now(), items: Object.values(items), cards: Object.values(cards), builds };
    recSet(KEY, JSON.stringify(out));
    return out;
  }
  // v2.11 : image des sorts (le n° d'image diffère du n° de sort) et équipements enregistrés de la page Personnage
  // n° ou chemin d'image d'un objet du jeu (monstre, boss) : premier champ qui y ressemble
  function imgField(o) {
    if (!o || typeof o !== 'object') return null;
    for (const k of ['gfx', 'gfxId', 'look', 'img', 'image', 'icon', 'sprite', 'skin', 'avatar', 'pic']) { const v = o[k]; if (v != null && v !== '' && (typeof v === 'number' || typeof v === 'string')) return v; }
    for (const k in o) { const v = o[k]; if ((typeof v === 'number' || typeof v === 'string') && /gfx|look|img|icon|sprite|skin|avatar|bone|pic/i.test(k)) return v; if (typeof v === 'string' && /\/img\/monsters\//.test(v)) return v; }
    return null;
  }
  function cardIcon(c) {
    if (!c) return null;
    for (const k of ['icon', 'img', 'image', 'gfx', 'sprite', 'pic', 'iconId', 'spellIcon', 'spellId', 'sid']) { const v = c[k]; if (v != null && v !== '' && (typeof v === 'number' || typeof v === 'string')) return String(v); }
    for (const k in c) { const v = c[k]; if (typeof v === 'string' && /sort_\d+/.test(v)) return v.match(/sort_\d+/)[0]; }
    return null;
  }
  const PRE_SLOTS = ['chapeau', 'cape', 'amulette', 'anneau1', 'anneau2', 'ceinture', 'bottes', 'arme', 'bouclier', 'familier', 'dofus1', 'dofus2', 'dofus3', 'dofus4', 'dofus5', 'dofus6'];
  const PRE_CAR = ['vitalite', 'sagesse', 'force', 'intelligence', 'chance', 'agilite'];
  function preItem(v) {
    if (v == null) return null;
    if (typeof v === 'number') return { id: v, f: 0 };
    if (typeof v === 'string' && /^\d+$/.test(v)) return { id: +v, f: 0 };
    if (typeof v === 'object') { const it = v.item && typeof v.item === 'object' ? v.item : v; const id = it.id || v.itemId || v.item_id || v.iid || (typeof v.item === 'number' ? v.item : null); if (!id) return null; return { id: +id, f: +(v.fusion ?? v.f ?? it.fusion ?? it.f ?? 0) || 0 }; }
    return null;
  }
  function preGear(x, d = 0, out = {}) {
    if (!x || typeof x !== 'object' || d > 6) return out;
    if (Array.isArray(x)) { for (const e of x) { if (e && typeof e === 'object' && typeof e.slot === 'string' && PRE_SLOTS.includes(e.slot)) { const it = preItem(e); if (it) out[e.slot] = it; } else preGear(e, d + 1, out); } return out; }
    const ks = Object.keys(x).filter(k => PRE_SLOTS.includes(k));
    if (ks.length >= 2) { for (const k of ks) { const it = preItem(x[k]); if (it) out[k] = it; } return out; }
    for (const k in x) preGear(x[k], d + 1, out);
    return out;
  }
  function preAlloc(x, d = 0) {
    if (!x || typeof x !== 'object' || d > 6) return null;
    if (!Array.isArray(x)) { const ks = PRE_CAR.filter(k => typeof x[k] === 'number'); if (ks.length >= 3) { const o = {}; for (const k of ks) o[k] = x[k]; return o; } }
    if (Array.isArray(x) && x.length && x.every(r => r && typeof r === 'object' && PRE_CAR.includes(r.key))) { const o = {}; for (const r of x) o[r.key] = +(r.base ?? r.value ?? r.v ?? 0) || 0; return o; }
    for (const k in x) { const r = preAlloc(x[k], d + 1); if (r) return r; }
    return null;
  }
  function preName(x) { for (const k of ['name', 'nom', 'label', 'title', 'n']) if (typeof x[k] === 'string') return x[k]; return null; }
  function presetArrays(perso) {
    const found = [];
    const visit = (v, d) => { if (!v || typeof v !== 'object' || d > 9) return; if (Array.isArray(v)) { if (v.length >= 1 && v.length <= 12 && v.some(x => x && typeof x === 'object' && !Array.isArray(x)) && v.every(x => x == null || (typeof x === 'object' && !Array.isArray(x)))) { const n = v.filter(x => x && Object.keys(preGear(x)).length >= 2).length; if (n) found.push({ n, v }); } v.forEach(x => visit(x, d + 1)); return; } for (const k in v) visit(v[k], d + 1); };
    visit(perso, 0); return found.sort((a, b) => b.n - a.n);
  }
  function findPresets(perso) {
    const f = presetArrays(perso)[0]; if (!f) return null;
    return f.v.map((x, i) => x ? { i, name: preName(x) || ('Équipement ' + (i + 1)), gear: preGear(x), alloc: preAlloc(x) } : { i, name: 'Équipement ' + (i + 1), gear: {}, alloc: null });
  }
  function presetsRaw(perso) { const f = presetArrays(perso)[0]; if (f) return JSON.stringify(f.v).slice(0, 40000); const s = JSON.stringify(perso); const m = s.match(/.{0,200}(preset|loadout|enregistr|saved|equipSet)[^]{0,3000}/i); return m ? m[0].slice(0, 6000) : null; }
  async function rsc(path, asRsc) {
      const h = await origFetch(path, asRsc ? { credentials: 'include', headers: { RSC: '1' } } : { credentials: 'include' }).then(r => r.text());
      return parseRsc(h);
  }
  function parseRsc(h) {
      const txt = !/self\.__next_f/.test(h) ? h : [...h.matchAll(/self\.__next_f\.push\(\[1,"((?:[^"\\]|\\.)*)"\]\)/g)].map(m => { try { return JSON.parse('"' + m[1] + '"'); } catch (e) { return ''; } }).join('');
      const rows = {};
      for (const l of txt.split('\n')) { const m = l.match(/^([0-9a-f]+):([\[{].*)$/); if (m) { try { rows[m[1]] = JSON.parse(m[2]); } catch (e) {} } }
      const res = (v) => { if (typeof v === 'string' && /^\$[@L][0-9a-f]+$/.test(v)) return rows[v.slice(2)]; if (typeof v === 'string' && /^\$[0-9a-f]+:/.test(v)) { const p = v.slice(1).split(':'); let c = rows[p[0]]; for (const k of p.slice(1)) c = (Array.isArray(c) && c[0] === '$' && k === 'props') ? c[3] : (c ? c[k] : c); return c; } return v; };
      const deep = (v, d = 0) => { v = res(v); if (d > 9 || !v || typeof v !== 'object') return v; if (Array.isArray(v)) return v.map(x => deep(x, d + 1)); const o = {}; for (const k in v) o[k] = deep(v[k], d + 1); return o; };
      const found = [];
      const walk = (v, d) => { if (d > 16 || !v || typeof v !== 'object') return; if (Array.isArray(v) && v[0] === '$' && v[3] && typeof v[3] === 'object') found.push(v[3]); (Array.isArray(v) ? v : Object.values(v)).forEach(x => walk(x, d + 1)); };
      Object.values(rows).forEach(v => walk(v, 0));
      return { find: (pred) => { const p = found.find(pred); return p ? deep(p) : null; }, all: () => found.map(p => deep(p)), raw: () => Object.values(rows).map(v => deep(v)), size: h.length };
    }

  // ---------- Bestiaire (lecture seule, comme une page vue) ----------
  const BEST_KEY = 'labo-best-v1';
  function loadBest() { try { return JSON.parse(localStorage.getItem(BEST_KEY) || 'null'); } catch (e) { return null; } }
  function parseMechEntry(n, x, w) {
    const num = v => v ? +String(v).replace(',', '.') : 0; let m; const o = { mn: n };
    const [d, rest = ''] = String(w).split(' · ');
    o.d = d.split(' et ').map(v => ({ Initiation: 'I', Facile: 'F', Normale: 'N', Difficile: 'D', Cauchemar: 'C' })[v] || v).join('');
    if ((m = rest.match(/Ascension, étages (\d+)-(\d+)/))) o.asc = [+m[1], +m[2]];
    if ((m = rest.match(/Chemin \(boss n°(\d+)\)/))) o.ch = +m[1];
    if ((m = rest.match(/au-delà du boss n°(\d+)/))) o.beyond = +m[1];
    if (/boss de zone/.test(rest)) o.zone = 1;
    if (/deuxième mécanique/.test(rest)) o.second = 1;
    if (/Faille|Abysse/i.test(rest)) o.faille = 1;
    try {
      switch (n) {
        case 'Fureur': m = x.match(/plus de (\d+) cartes.*×([\d,]+)/); o.fu = [num(m[1]), num(m[2])]; break;
        case 'Peau dure': m = x.match(/seuls (\d+) %/); o.pd = num(m[1]); break;
        case 'Onde de choc': m = x.match(/de (\d+) % de tes PV/); o.oc = num(m[1]); break;
        case 'Malédiction des soins': m = x.match(/tour (\d+)/); o.ms = [num(m[1]), /divisés/.test(x) ? 'half' : 'inv']; break;
        case 'Sceau': m = x.match(/Tous les (\d+) tours/); o.sc = m ? num(m[1]) : 1; break;
        case 'Deuxième souffle': m = x.match(/(\d+) % de ses PV/); o.ds = [num(m[1]), /fou de rage/.test(x) ? 1 : 0]; break;
        case 'Miroir': m = x.match(/tours? (\d+)(?: à (\d+))?/); o.mi = [num(m[1]), num(m[2] || m[1])]; break;
        case 'PA comptés': m = x.match(/Au tour (\d+), finis ton tour avec exactement (\d+)/); o.pa = [num(m[1]), num(m[2])]; break;
        case 'Rage': m = x.match(/tour (\d+)/); o.ra = num(m[1]); break;
        case 'Vol de PA': m = x.match(/Tous les (\d+) tours/); o.vp = m ? num(m[1]) : 1; break;
        case 'Échange de vie': m = x.match(/tour (\d+)/); o.ev = [num(m[1]), /à moitié/.test(x) ? 1 : 0]; break;
        default: o.raw = x;
      }
    } catch (e) { o.raw = x; }
    o.x = x;
    return o;
  }
  // v2.11.3 : catalogue complet des objets (onglet Objets du bestiaire, ~3 300 objets), lu page par page si besoin ; gardé 24 h
  const ALLITEMS_KEY = 'labo-allitems-v2';
  function itemArrays(v, out, d = 0) {
    if (!v || typeof v !== 'object' || d > 12) return out;
    if (Array.isArray(v)) { if (v.length >= 20 && v.filter(x => x && typeof x === 'object' && x.id != null && typeof (x.n || x.name) === 'string').length >= v.length * 0.8) out.push(v); for (const x of v) itemArrays(x, out, d + 1); return out; }
    for (const k in v) itemArrays(v[k], out, d + 1); return out;
  }
  const slimItem = x => { const it = x.item && typeof x.item === 'object' ? Object.assign({}, x.item, x) : x; return { id: it.id, n: it.n || it.name, lvl: it.lvl ?? it.level ?? it.l, s: it.s || it.slot || it.type || it.cat || null, icon: it.icon ?? it.gfx ?? it.img ?? null, r: it.r ?? it.rarity ?? 0, st: it.st || it.stats || it.carac || {}, setName: it.setName || null, setId: it.setId || null, w: it.w || null, src: typeof (it.src || it.source || it.how) === 'string' ? (it.src || it.source || it.how).slice(0, 200) : undefined }; };
  const looksItem = a => a.some(x => x && (x.s || x.slot) && (x.lvl != null || x.level != null)) || a.some(x => x && x.item && x.item.s);
  // v2.11.8 : l'onglet Objets du jeu envoie une carte par objet ({item:{id,n,lvl,s,icon,r,st}} + texte « où le trouver »),
  // paginée par le paramètre n (20, 40, 60…). On demande tout d'un coup (n=5000) au format RSC, comme le fait le jeu.
  function rscRows(h) {
    const txt = !/self\.__next_f/.test(h) ? h : [...h.matchAll(/self\.__next_f\.push\(\[1,"((?:[^"\\]|\\.)*)"\]\)/g)].map(m => { try { return JSON.parse('"' + m[1] + '"'); } catch (e) { return ''; } }).join('');
    const rows = []; for (const l of txt.split('\n')) { const m = l.match(/^([0-9a-f]+):([\[{].*)$/); if (m) { try { rows.push(JSON.parse(m[2])); } catch (e) {} } } return rows;
  }
  function flatText(v, out) { if (v == null || v === false) return out; if (typeof v === 'string') { if (!/^\$/.test(v)) out.push(v); return out; } if (typeof v === 'number') { out.push(String(v)); return out; } if (Array.isArray(v)) { if (v[0] === '$' && v[3] && typeof v[3] === 'object') return flatText(v[3].children, out); for (const x of v) flatText(x, out); } return out; }
  function extractItems(h) {
    const out = new Map(); const rows = rscRows(h);
    const visit = (v, d, card) => {
      if (!v || typeof v !== 'object' || d > 80) return;
      if (Array.isArray(v)) {
        if (v[0] === '$' && v[3] && typeof v[3] === 'object') {
          const p = v[3]; let c = card;
          if (typeof p.className === 'string' && /__card/.test(p.className)) { c = { item: null, src: [] }; visit(p.children, d + 1, c); if (c.item) { const s = slimItem(c.item); if (c.src.length) s.src = c.src.join(' · ').slice(0, 300); if (s.id != null) out.set(s.id, s); } return; }
          if (p.item && typeof p.item === 'object' && p.item.id != null && p.item.n) { if (c) c.item = c.item || p.item; else { const s = slimItem(p.item); out.set(s.id, s); } }
          if (c && v[1] === 'li') { const ch = Array.isArray(p.children) ? p.children : [p.children]; const head = ch[0] && Array.isArray(ch[0]) && ch[0][0] === '$' ? flatText(ch[0], []).join('').trim() : ''; const body = flatText(head ? ch.slice(1) : ch, []).join('').replace(/\s+/g, ' ').trim(); const tx = (head ? head + ' : ' : '') + body; if (tx.trim()) c.src.push(tx.trim()); return; }
          visit(p.children, d + 1, c); return;
        }
        for (const x of v) visit(x, d + 1, card); return;
      }
      for (const k in v) visit(v[k], d + 1, card);
    };
    for (const r of rows) visit(r, 0, null);
    return out;
  }
  function harvestItems(text, how) {
    try {
      if (!text || text.length < 2000 || !/lvl/.test(text)) return 0;
      const got = extractItems(text);
      let st = null; try { st = JSON.parse(localStorage.getItem('labo-allitems-live') || 'null'); } catch (e) {}
      const m = new Map(((st && st.items) || []).map(x => [x.id, x])); let n = 0;
      for (const [id, s] of got) { if (!m.has(id)) n++; m.set(id, Object.assign({}, m.get(id) || {}, s)); }
      const lg = ((st && st.log) || []).slice(0, 9); lg.unshift({ t: Date.now(), how, len: text.length, found: got.size, added: n });
      localStorage.setItem('labo-allitems-live', JSON.stringify({ t: Date.now(), items: [...m.values()], log: lg }));
      return n;
    } catch (e) { return 0; }
  }
  function harvestDocument() {
    if (!/\/bestiaire/.test(location.pathname) || !document.documentElement) return;
    const s = [...document.querySelectorAll('script')].map(x => x.textContent || '').filter(x => x.includes('__next_f')).join('\n');
    if (s && s.length !== harvestDocument.len) { harvestDocument.len = s.length; harvestItems('<x>' + s + '</x>', 'page ' + location.search); }
  }
  setInterval(harvestDocument, 4000);
  // Le serveur plafonne n à 200 objets par réponse : on découpe par emplacement, puis par tranche de niveau (bisection),
  // puis par rareté, jusqu'à ce que chaque réponse contienne tout ce qu'elle annonce (« shown »).
  async function fetchAllItems() {
    try { const c = JSON.parse(localStorage.getItem(ALLITEMS_KEY) || 'null'); if (c && c.items && c.items.length > 3000 && Date.now() - c.t < 7 * 864e5) return c.items; } catch (e) {}
    const got = new Map(); const diag = []; let calls = 0;
    const ask = async (q) => { calls++; const h = await origFetch('/bestiaire?onglet=objets&n=200' + q, { credentials: 'include', headers: { RSC: '1' } }).then(r => r.text()); const g = extractItems(h); for (const [id, x] of g) got.set(id, x); const shown = +((h.match(/"shown":(\d+)/) || [])[1] || 0), total = +((h.match(/"total":(\d+)/) || [])[1] || 0); return { found: g.size, shown, total }; };
    try {
      const first = await ask(''); diag.push(Object.assign({ q: 'tout' }, first));
      const queue = [];
      const capped = r => r.shown ? r.shown > r.found : r.found >= 200;
      if (capped(first)) for (const s of ['arme', 'amulette', 'anneau', 'bottes', 'ceinture', 'chapeau', 'cape', 'dofus', 'familier', 'bouclier', 'parchemin']) queue.push({ s, lo: 1, hi: 200, r: null });
      while (queue.length && calls < 150) {
        const x = queue.shift(); const q = '&emplacement=' + x.s + (x.lo > 1 || x.hi < 200 ? '&min=' + x.lo + '&max=' + x.hi : '') + (x.r != null ? '&rarete=' + x.r : '');
        const r = await ask(q); diag.push(Object.assign({ q }, r));
        if (capped(r)) {
          if (x.hi > x.lo) { const m = Math.floor((x.lo + x.hi) / 2); queue.push({ s: x.s, lo: x.lo, hi: m, r: x.r }, { s: x.s, lo: m + 1, hi: x.hi, r: x.r }); }
          else if (x.r == null) for (let k = 0; k <= 5; k++) queue.push({ s: x.s, lo: x.lo, hi: x.hi, r: k });
          else { const r2 = await ask(q + '&tri=level-desc'); diag.push(Object.assign({ q: q + '&tri=level-desc' }, r2)); }
        }
        await new Promise(res => setTimeout(res, 120));
      }
    } catch (e) { diag.push({ err: String(e).slice(0, 200) }); }
    let items = [...got.values()];
    if (items.length < 1000) { try { const L = JSON.parse(localStorage.getItem('labo-allitems-live') || 'null'); if (L && L.items && L.items.length > items.length) items = L.items; } catch (e) {} }
    diag.unshift({ calls, items: items.length });
    try { localStorage.setItem('labo-allitems-diag', JSON.stringify(diag).slice(0, 20000)); } catch (e) {}
    if (items.length > 1000) { try { localStorage.setItem(ALLITEMS_KEY, JSON.stringify({ t: Date.now(), items })); } catch (e) {} }
    return items;
  }
  async function fetchBestiary(full) {
    const out = loadBest() || {};
    const mp = await rsc('/bestiaire?onglet=mecaniques');
    const C = mp.find(p => Array.isArray(p.cards) && p.tagLabels);
    if (C) {
      // les mécaniques ne sont révélées qu'aux persos qui ont battu le boss : on garde celles déjà connues (perso principal)
      const prev = Object.fromEntries((out.mech || []).map(c => [c.id, c]));
      out.mech = C.cards.map(c => { const m = (c.m || []).map(e => parseMechEntry(e.n, e.x, e.w)); const p = prev[c.id]; return { id: c.id, n: c.n, l: c.l, t: c.t, u: c.u ? 1 : (p && p.u) || 0, v: c.v, g: c.g || imgField(c) || (p && p.g) || null, m: m.length ? m : (p && p.m) || [] }; });
      out.tagLabels = C.tagLabels; out.t = Date.now(); try { out.diag = { mechKeys: Object.keys(C.cards[0] || {}), mechSample: JSON.stringify(C.cards[0]).slice(0, 1500) }; } catch (e) {}
    }
    if (full) {
      try { const all = await fetchAllItems(); if (all && all.length) out.allItems = all; } catch (e) {}
      const bp = await rsc('/bestiaire');
      const B = bp.find(p => Array.isArray(p.monsters) && Array.isArray(p.zones));
      if (B) { out.monsters = B.monsters; out.items = B.items; out.zones = B.zones; out.pp = B.prospection; out.tFull = Date.now(); }
    }
    try { localStorage.setItem(BEST_KEY, JSON.stringify(Object.assign({}, out, { allItems: undefined }))); } catch (e) { try { localStorage.setItem(BEST_KEY, JSON.stringify({ mech: out.mech, t: out.t })); } catch (e2) {} }
    return out;
  }
  const diffForFloor = fl => fl <= 2 ? 'F' : fl <= 5 ? 'N' : fl <= 8 ? 'D' : 'C';
  function bestEntriesFor(name, floor) {
    const B = loadBest(); const card = B && B.mech && B.mech.find(c => c.n === name);
    if (!card || !card.m) return null;
    if (floor) { const asc = card.m.filter(e => e.asc && floor >= e.asc[0] && floor <= e.asc[1]); if (asc.length) return asc; const d = diffForFloor(floor); return card.m.filter(e => !e.asc && String(e.d).includes(d)); }
    return card.m;
  }
  let bestFetching = false, bestTriedAt = 0;

  // ---------- Comparateur d'équipement (calcul local, lecture seule) ----------
  // Pour chaque objet de l'inventaire : on l'équipe à la place de l'objet porté, on simule les combats habituels, on garde les gains
  let cmp = { status: 'idle' };
  function setTiersFor(I) {
    const out = {}; let dc = {}; try { dc = JSON.parse(localStorage.getItem(DOFUS_SETS_KEY) || '{}') || {}; } catch (e) {}
    for (const [id, o] of Object.entries(dc)) { if (!o || !o.tiers) continue; const t = {}; for (let k = 2; k <= Math.max(2, o.size || 2); k++) { const src = o.tiers[Math.min(o.size || k + 1, k + 1)]; if (src) t[k] = src; } out[id] = t; }
    const byName = {}; for (const x of (I.sets || [])) byName[x.n] = x.id;
    const B = loadBest(); for (const i of (B && B.items) || []) if (i.setName && i.setId) byName[i.setName] = i.setId;
    for (const [n, o] of Object.entries(loadSets())) { const id = byName[n]; if (id && o && o.tiers) out[id] = Object.assign(out[id] || {}, o.tiers); }
    return out;
  }
  function benchGroup() {
    // adversaires habituels : le groupe le plus combattu parmi les 60 derniers combats hors boss
    const cnt = {}; for (const f of db.fights.slice(-60)) { if (f.boss || f.kind === 'boss' || !f.mons || !f.mons.length) continue; const k = f.mons.slice().sort().join('+'); cnt[k] = (cnt[k] || 0) + 1; }
    const best = Object.entries(cnt).sort((a, b) => b[1] - a[1])[0]; if (!best) return null;
    const defs = best[0].split('+').map(k => db.monsters[k]).filter(Boolean).map(m => ({ name: m.name, hpMin: m.hpMin, hpMax: m.hpMax, atk: m.atk, element: m.element, pattern: m.pattern, stats: m.stats || {}, isBoss: !!m.isBoss, mech: (m.mech && m.mech.parsed) || null }));
    return defs.length === best[0].split('+').length ? { defs, label: best[0].replace(/#\d+/g, '').split('+').join(' + '), n: best[1] } : null;
  }
  async function runCompare() {
    if (!LR) { cmp = { status: 'err', msg: 'moteur indisponible' }; render(); return; }
    cmp = { status: 'load' }; render();
    try {
      const inv = await rsc('/inventaire'), deck = await rsc('/deck'), perso = await rsc('/personnage');
      const I = inv.find(p => p.entries && p.slots), D = deck.find(p => p.collection && p.initialDecks), Pp = perso.find(p => p.rows && 'pointsFree' in p), H = perso.find(p => 'prestige' in p && 'level' in p && 'equipped' in p) || {};
      if (!I || !D || !Pp) throw new Error('pages introuvables (es-tu connecté ?)');
      let forgeLv = 0; try { const fp = await rsc('/forgemagie'); const F = fp.find(p => 'orbs' in p && 'level' in p && 'xp' in p); if (F) forgeLv = F.level; } catch (e) {}
      const bench = benchGroup(); if (!bench) throw new Error('pas encore assez de combats enregistrés pour savoir contre qui comparer');
      const level = I.level || 200;
      const ctx = { prestige: H.prestige || 0, discordPct: 5, scrolls: I.scrollValues || {}, level, breedId: D.breedId, setTiers: setTiersFor(I), forgePct: LR.forgePctFor(forgeLv), alloc: Object.fromEntries(Pp.rows.map(r => [r.key, r.base])) };
      const cards = {}; for (const c of D.collection) cards[c.key] = c.card;
      const deckCards = (D.initialDecks[D.initialActive] || []).map(k => cards[k]).filter(c => c && c.eff && c.eff.length).map((c, i) => LR.prepCard({ id: c.id, n: c.n, ap: c.ap, cc: c.cc, eff: c.eff, crit: c.crit || null }, 'c' + i));
      const gear = {}; for (const x of I.slots) if (x.item) gear[x.slot] = Object.assign({}, x.item, { f: x.fusion || 0 });
      const slotsOf = t => Object.keys(gear).concat(I.slots.map(x => x.slot)).filter((v, i, a) => a.indexOf(v) === i).filter(sl => sl.replace(/\d+$/, '') === t || (I.slots.find(x => x.slot === sl) || {}).type === t);
      const evalGear = g => {
        const S = LR.computeStats(Object.values(g).filter(Boolean).map(it => ({ item: it, f: it.f || 0 })), ctx);
        const w = g.arme && g.arme.w ? LR.weaponCard(g.arme, g.arme.f || 0) : null;
        const r = LR.runMany({ S, deck: deckCards, weapon: w, monsters: bench.defs, level, auto: true, seed: 3 }, 150);
        return { r, S, score: r.winRate * 1000 - (isFinite(r.avgRounds) ? r.avgRounds : 30) * 22 - r.avgHpLost / Math.max(1, S._maxHp) * 350 };
      };
      const base = evalGear(gear);
      const jobs = [];
      for (const e of I.entries) {
        const it = e.item; if (!it || !it.st || (it.lvl || 0) > level) continue;
        for (const sl of slotsOf(it.s)) { const cur = gear[sl]; if (cur && cur.id === it.id && (cur.f || 0) === (e.fusion || 0)) continue; if (Object.entries(gear).some(([k, g]) => k !== sl && g && g.id === it.id && (it.s === 'anneau' || it.s === 'dofus'))) continue; jobs.push({ sl, it: Object.assign({}, it, { f: e.fusion || 0 }), cur }); }
      }
      cmp = { status: 'run', done: 0, of: jobs.length, bench, base, rows: [] }; render();
      let k = 0; const t0 = Date.now();
      const step = () => {
        const end = Math.min(jobs.length, k + 6);
        for (; k < end; k++) { const j = jobs[k]; const g = Object.assign({}, gear, { [j.sl]: j.it }); const e = evalGear(g); if (e.score > base.score + 3) cmp.rows.push({ j, e }); }
        cmp.done = k; if (k < jobs.length) { if (Date.now() - (cmp.lastR || 0) > 400) { cmp.lastR = Date.now(); render(); } setTimeout(step, 0); }
        else { cmp.rows.sort((a, b) => b.e.score - a.e.score); const seen = new Set(); cmp.rows = cmp.rows.filter(x => { const key = x.j.it.id + ':' + x.j.it.f; if (seen.has(key)) return false; seen.add(key); return true; }).slice(0, 10); cmp.status = 'done'; cmp.ms = Date.now() - t0; render(); }
      };
      setTimeout(step, 0);
    } catch (e) { cmp = { status: 'err', msg: e.message }; render(); }
  }
  function compareHtml() {
    const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
    const L = { chapeau: 'chapeau', cape: 'cape', amulette: 'amulette', anneau1: 'anneau 1', anneau2: 'anneau 2', ceinture: 'ceinture', bottes: 'bottes', arme: 'arme', bouclier: 'bouclier', familier: 'familier' };
    const head = `<div style="display:flex;justify-content:space-between;align-items:center;gap:8px;margin-bottom:4px"><strong style="color:#e0b04f">Comparer mon inventaire</strong><button data-a="back" style="${btn()}">Retour</button></div>`;
    if (cmp.status === 'idle') return head + `<div style="color:#a89a85">Teste chaque objet de ton inventaire à la place de ce que tu portes, contre tes adversaires habituels, et liste les échanges qui améliorent ton build. Calcul local, rien n'est équipé.</div><div style="margin-top:6px"><button data-a="cmprun" style="${btn(true)}">Lancer la comparaison</button></div>`;
    if (cmp.status === 'load') return head + `<div style="color:#a89a85">Lecture de l'inventaire, du deck et du personnage…</div>`;
    if (cmp.status === 'err') return head + `<div style="color:#ec7a70">Comparaison impossible : ${esc(cmp.msg)}</div><div style="margin-top:6px"><button data-a="cmprun" style="${btn()}">Réessayer</button></div>`;
    const b = cmp.base.r, pc = x => Math.round(x * 100) + ' %';
    let h = head + `<div style="color:#a89a85">Contre <strong>${esc(cmp.bench.label)}</strong> (ton groupe le plus combattu) · build actuel : ${pc(b.winRate)} de victoires, ${isFinite(b.avgRounds) ? b.avgRounds.toFixed(2) : '—'} tours, ${Math.round(b.avgHpLost)} PV perdus</div>`;
    if (cmp.status === 'run') return h + `<div style="margin-top:6px">Calcul… ${cmp.done} / ${cmp.of} essais</div><div style="height:4px;background:#4a3f30;border-radius:3px;margin-top:4px"><div style="height:4px;width:${Math.round(cmp.done / Math.max(1, cmp.of) * 100)}%;background:#e0b04f;border-radius:3px"></div></div>`;
    if (!cmp.rows.length) return h + `<div style="margin-top:6px;color:#8fc98a">Aucun objet de ton inventaire ne fait mieux en échange simple : ton équipement est déjà le meilleur contre ce groupe.</div><div style="margin-top:6px"><button data-a="cmprun" style="${btn()}">Relancer</button></div>`;
    h += `<div style="margin-top:6px;display:grid;gap:4px">` + cmp.rows.map(({ j, e }) => { const r = e.r; const dT = (isFinite(r.avgRounds) && isFinite(b.avgRounds)) ? r.avgRounds - b.avgRounds : null; const dH = r.avgHpLost - b.avgHpLost; const dW = r.winRate - b.winRate;
      return `<div style="border:1px solid #4a3f30;border-radius:8px;padding:4px 8px"><div><strong>${esc(j.it.n)}</strong>${j.it.f ? ' +' + j.it.f : ''} <span style="color:#a89a85">(${L[j.sl] || esc(j.sl)}${j.cur ? ', à la place de ' + esc(j.cur.n) : ''})</span></div><div style="color:#8fc98a">${dW > 0.004 ? '+' + pc(dW) + ' de victoires · ' : ''}${dT != null && Math.abs(dT) >= 0.01 ? (dT < 0 ? '' : '+') + dT.toFixed(2) + ' tours · ' : ''}${Math.abs(dH) >= 1 ? (dH < 0 ? '' : '+') + Math.round(dH) + ' PV perdus' : ''}</div></div>`; }).join('') + `</div><div style="color:#a89a85;margin-top:4px">Échange d'un seul objet à la fois, ${cmp.of} essais en ${Math.round(cmp.ms / 1000)} s. Pour des changements combinés (panoplies, deck, points), utilise l'Optimiseur du Labo.</div><div style="margin-top:6px"><button data-a="cmprun" style="${btn()}">Relancer</button></div>`;
    return h;
  }

  // ---------- Panneau ----------
  let panel = null, minimized = false, view = 'stats';
  try { minimized = localStorage.getItem('labo-min') === '1'; } catch (e) {}
  const fmt = (n, d = 0) => Number(n).toLocaleString('fr-FR', { maximumFractionDigits: d, minimumFractionDigits: d });
  function build() {
    panel = document.createElement('div');
    panel.id = 'labo-panel';
    panel.setAttribute('style', 'position:fixed;left:10px;bottom:10px;z-index:2147483000;font:12px/1.4 system-ui,sans-serif;color:#efe6d6;background:rgba(21,18,13,.94);border:1px solid #4a3f30;border-radius:8px;padding:8px 10px;min-width:210px;max-width:280px;box-shadow:0 4px 14px rgba(0,0,0,.45)');
    document.documentElement.appendChild(panel);
    setInterval(() => { if (!document.documentElement.contains(panel)) document.documentElement.appendChild(panel); }, 2000);
    panel.addEventListener('click', onClick);
    render();
  }
  function render() {
    if (!panel) return;
    const s = summary(started), all = summary(0);
    if (minimized) { panel.innerHTML = `<button data-a="max" style="${btn()}">Labo · ${s.fights} combats</button>`; return; }
    if (view === 'compare') { panel.innerHTML = compareHtml() + '<div id="labo-msg" style="margin-top:4px;color:#a89a85;min-height:1em"></div>'; return; }
    if (view === 'labourl') {
      panel.innerHTML = `<div style="display:flex;justify-content:space-between;align-items:center;gap:8px;margin-bottom:4px"><strong style="color:#e0b04f">Adresse de ton Labo</strong><button data-a="back" style="${btn()}">Retour</button></div>
        <div style="color:#a89a85">Colle l'adresse de ton Labo en ligne (ex. https://ton-pseudo.github.io/labo-rpgmasters/). « Envoyer au Labo » l'ouvrira et y importera tes données sans copier-coller.</div>
        <input id="labo-url" value="${String(laboUrl() || '').replace(/"/g, '&quot;')}" placeholder="https://…" style="width:100%;margin-top:6px;font:12px system-ui;padding:4px 6px;box-sizing:border-box">
        <div style="display:flex;gap:6px;margin-top:6px"><button data-a="saveurl" style="${btn(true)}">Enregistrer</button></div>
        <div id="labo-msg" style="margin-top:4px;color:#a89a85;min-height:1em"></div>`;
      return;
    }
    if (view === 'backup') {
      const at = backupAt();
      panel.innerHTML = `<div style="display:flex;justify-content:space-between;align-items:center;gap:8px;margin-bottom:4px"><strong style="color:#e0b04f">Sauvegarde</strong><button data-a="back" style="${btn()}">Retour</button></div>
        <div style="color:#a89a85">Ton historique (combats, monstres, étages, builds) est gardé par ton navigateur : il survit à l'extinction de l'ordi. Il disparaît seulement si tu vides les données du site / l'historique, en navigation privée, ou sur un autre navigateur ou PC. Ce fichier permet de tout remettre en un clic.</div>
        <div style="margin-top:4px">Dernière sauvegarde : <strong>${at ? new Date(at).toLocaleString('fr-FR') : 'jamais'}</strong></div>
        <div style="display:flex;gap:6px;margin-top:6px;flex-wrap:wrap"><button data-a="bkdl" style="${btn(true)}">Télécharger la sauvegarde</button><button data-a="bkrest" style="${btn()}">Restaurer un fichier</button></div>
        <input type="file" id="labo-bkfile" accept=".json,application/json" style="display:none">
        <div id="labo-msg" style="margin-top:4px;color:#a89a85;min-height:1em"></div>`;
      const fi = panel.querySelector('#labo-bkfile');
      fi.onchange = () => { const f = fi.files && fi.files[0]; if (!f) return; const rd = new FileReader(); rd.onload = () => { try { const n = restoreBackup(String(rd.result)); panel.querySelector('#labo-msg').textContent = n + ' éléments restaurés. Recharge la page du jeu.'; } catch (e) { panel.querySelector('#labo-msg').textContent = 'Fichier illisible : ' + e.message; } }; rd.readAsText(f); };
      return;
    }
    if (view === 'builds') {
      const n = loadBuilds().builds.length;
      panel.innerHTML = `<div style="display:flex;justify-content:space-between;align-items:center;gap:8px;margin-bottom:4px"><strong style="color:#e0b04f">Builds conseillés · ${n}</strong><button data-a="back" style="${btn()}">Retour</button></div>
        <div style="color:#a89a85">Colle ici le pack de builds exporté depuis le Labo (onglet Ascension). Il s'affichera quand tu croiseras les adversaires concernés.</div>
        <textarea id="labo-bin" style="width:100%;height:70px;margin-top:6px;font:11px monospace"></textarea>
        <div style="display:flex;gap:6px;margin-top:6px"><button data-a="saveb" style="${btn(true)}">Enregistrer</button><button data-a="clearb" style="${btn()}">Tout effacer</button></div>
        <div id="labo-msg" style="margin-top:4px;color:#a89a85;min-height:1em"></div>`;
      return;
    }
    panel.innerHTML = `
      <div style="display:flex;justify-content:space-between;align-items:center;gap:8px;margin-bottom:4px"><strong style="color:#e0b04f">Labo · cette session</strong><button data-a="min" style="${btn()}" title="Réduire">–</button></div>
      <div style="display:flex;gap:4px;align-items:center;margin-bottom:6px"><span style="color:#a89a85">Perso :</span><button data-a="prof-principal" style="${btn(PROFILE === 'principal')}">Principal</button><button data-a="prof-saison" style="${btn(PROFILE === 'saison')}">Saison</button>${profileLocked() ? '<button data-a="prof-auto" style="' + btn() + '" title="Détection automatique">auto</button>' : ''}</div>${profileFixed ? '<div style="color:#e0b04f;margin-bottom:4px">' + profileFixed + '</div>' : ''}${PROFILE === 'saison' ? '<div style="color:#ec7a70;margin-bottom:4px">Héroïque : une défaite contre un boss = mort définitive.</div>' : ''}
      <div style="display:grid;grid-template-columns:1fr auto;gap:1px 10px;font-variant-numeric:tabular-nums">
        <span>Combats</span><span>${s.fights} (${fmt(s.winRate * 100)} % gagnés)</span>
        <span>Tours moyens</span><span>${s.wins ? fmt(s.avgRounds, 2) : '—'}</span>
        <span>XP / heure</span><span>${fmt(s.xpH)}</span>
        <span>Kamas / heure</span><span>${fmt(s.kamasH)}</span>
        <span>Objets · cartes</span><span>${s.items} · ${s.cards}</span>
      </div>
      <div style="margin-top:4px;color:#a89a85">Dernier combat enregistré : ${lastAgo()}</div>${typeof document !== 'undefined' && document.hidden ? '' : (() => { const r = db.fights.slice(-30); const h = r.filter(f => f.hid).length; return h >= 5 ? `<div style="color:#e0b04f">${h} des 30 derniers combats ont eu lieu onglet caché : le navigateur ralentit alors le jeu (et l'Auto AFK).</div>` : ''; })()}
      <div style="margin-top:2px;color:#a89a85">Total : ${all.fights} combats · ${all.monsters} monstres · ${all.bosses} boss</div>
      <div style="display:flex;gap:6px;margin-top:6px;flex-wrap:wrap"><button data-a="export" style="${btn(true)}">Exporter pour le Labo</button><button data-a="send" style="${btn(true)}" title="Ouvre ton Labo en ligne et y importe tes données directement">Envoyer au Labo ↗</button><button data-a="seturl" style="${btn()}" title="Adresse de ton Labo en ligne">⚙</button><button data-a="compare" style="${btn()}" title="Teste chaque objet de ton inventaire à la place de ton équipement">Comparer</button><button data-a="builds" style="${btn()}">Builds</button><button data-a="backup" style="${btn()}" title="Copie de sécurité de tout ton historique dans un fichier">Sauvegarde</button><button data-a="reset" style="${btn()}">Vider</button></div>${backupNag(all.fights)}
      <div id="labo-msg" style="margin-top:4px;color:#a89a85;min-height:1em"></div>`;
  }
  // ---------- Sauvegarde complète (toutes les données labo-* de ce site) ----------
  function backupAt() { try { return +localStorage.getItem('labo-backup-at') || 0; } catch (e) { return 0; } }
  function backupNag(nFights) {
    const at = backupAt(), days = at ? (Date.now() - at) / 864e5 : Infinity;
    if (nFights < 200 || days < 7) return '';
    return `<div style="margin-top:4px;color:#e0b04f">${at ? 'Dernière sauvegarde il y a ' + Math.floor(days) + ' j' : 'Aucune sauvegarde de ton historique'} : <span data-a="backup" style="text-decoration:underline;cursor:pointer">en faire une</span></div>`;
  }
  function makeBackup() {
    save();
    const data = {}; for (let i = 0; i < localStorage.length; i++) { const k = localStorage.key(i); if (/^labo/.test(k) && k !== 'labo-backup-at') data[k] = localStorage.getItem(k); }
    if (recLoaded) data[keyFor(PROFILE)] = JSON.stringify(db); for (const k of REC_KEYS) if (REC[k] != null && !data[k]) data[k] = REC[k];
    return JSON.stringify({ kind: 'labo-sauvegarde', v: 1, t: Date.now(), origin: location.origin, data });
  }
  function restoreBackup(txt) {
    const b = JSON.parse(txt); if (!b || b.kind !== 'labo-sauvegarde' || !b.data) throw new Error('ce n’est pas une sauvegarde du Labo');
    let n = 0; for (const [k, v] of Object.entries(b.data)) if (/^labo/.test(k) && typeof v === 'string') { if (REC_KEYS.includes(k)) recSet(k, v); else localStorage.setItem(k, v); n++; }
    try { const d = JSON.parse(recGet(keyFor(PROFILE)) || 'null'); if (d && d.fights) { Object.assign(db, mergeRec(d, db)); recLoaded = true; } } catch (e) {}
    return n;
  }
  function downloadText(name, txt) {
    const a = document.createElement('a'); a.href = URL.createObjectURL(new Blob([txt], { type: 'application/json' })); a.download = name;
    document.body.appendChild(a); a.click(); setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 1000);
  }
  function btn(primary) { return `cursor:pointer;font:600 12px system-ui,sans-serif;border-radius:6px;padding:3px 8px;border:1px solid ${primary ? '#e0b04f' : '#4a3f30'};background:${primary ? '#e0b04f' : 'transparent'};color:${primary ? '#15120d' : '#efe6d6'}`; }
  function laboUrl() { try { return localStorage.getItem('labo-url') || ''; } catch (e) { return ''; } }
  let resetArmed = false;
  async function onClick(ev) {
    const a = ev.target && ev.target.dataset && ev.target.dataset.a; if (!a) return;
    const msg = () => panel.querySelector('#labo-msg');
    if (a === 'min' || a === 'max') { minimized = a === 'min'; try { localStorage.setItem('labo-min', minimized ? '1' : '0'); } catch (e) {} render(); return; }
    if (a === 'builds') { view = 'builds'; render(); return; }
    if (a === 'backup') { view = 'backup'; render(); return; }
    if (a === 'bkdl') { try { const txt = makeBackup(); downloadText('labo-sauvegarde-' + new Date().toISOString().slice(0, 10) + '.json', txt); localStorage.setItem('labo-backup-at', String(Date.now())); render(); panel.querySelector('#labo-msg').textContent = 'Sauvegarde téléchargée (' + Math.round(txt.length / 1024) + ' Ko). Garde le fichier.'; } catch (e) { msg().textContent = 'Sauvegarde impossible : ' + e.message; } return; }
    if (a === 'bkrest') { const fi = panel.querySelector('#labo-bkfile'); if (fi) fi.click(); return; }
    if (a === 'compare') { view = 'compare'; render(); return; }
    if (a === 'cmprun') { runCompare(); return; }
    if (a === 'seturl') { view = 'labourl'; render(); return; }
    if (a === 'saveurl') { const v = (panel.querySelector('#labo-url').value || '').trim(); if (v && !/^https:\/\//.test(v)) { msg().textContent = 'L’adresse doit commencer par https://'; return; } try { localStorage.setItem('labo-url', v); } catch (e) {} view = 'stats'; render(); return; }
    if (a === 'send') {
      const url = laboUrl(); if (!url) { view = 'labourl'; render(); return; }
      // la fenêtre s'ouvre tout de suite (sinon le navigateur la bloque), les données suivent dès que le Labo est prêt
      const origin = new URL(url).origin; const fresh = (() => { try { const u = new URL(url); u.searchParams.set('v', Date.now().toString(36)); return u.toString(); } catch (e) { return url; } })(); // paramètre unique : le navigateur recharge toujours la dernière version du Labo
      const w = window.open(fresh, 'labo-rpgmasters');
      if (!w) { msg().textContent = 'Fenêtre bloquée par le navigateur : autorise les pop-ups pour ce site.'; return; }
      let json = null, ready = false, sent = false;
      const trySend = () => { if (json && ready && !sent) { sent = true; w.postMessage({ type: 'labo-export', json }, origin); msg().textContent = 'Envoyé au Labo ✓'; window.removeEventListener('message', onMsg); } };
      const onMsg = e => { if (e.origin === origin && e.data && e.data.type === 'labo-ready') { ready = true; trySend(); } };
      window.addEventListener('message', onMsg);
      msg().textContent = 'Lecture de l’inventaire, du deck et du personnage…';
      try { json = JSON.stringify(await exportForLabo()); msg().textContent = 'En attente du Labo…'; trySend(); } catch (e) { msg().textContent = 'Export impossible : ' + e.message; return; }
      setTimeout(() => { if (!sent) { window.removeEventListener('message', onMsg); navigator.clipboard.writeText(json).then(() => { msg().textContent = 'Le Labo n’a pas répondu : export copié, fais Ctrl+V sur le Labo.'; }).catch(() => { msg().textContent = 'Le Labo n’a pas répondu. Vérifie son adresse avec le bouton ⚙.'; }); } }, 25000);
      return;
    }
    if (a === 'back') { view = 'stats'; render(); return; }
    if (a === 'saveb') {
      try { const d = JSON.parse(panel.querySelector('#labo-bin').value); if (!Array.isArray(d.builds)) throw new Error('champ « builds » manquant'); localStorage.setItem(BUILDS_KEY, JSON.stringify(d)); view = 'stats'; render(); msg().textContent = d.builds.length + ' builds enregistrés.'; }
      catch (e) { msg().textContent = 'Pack illisible : ' + e.message; }
      return;
    }
    if (a === 'prof-principal' || a === 'prof-saison') { setProfile(a === 'prof-saison' ? 'saison' : 'principal', true); render(); return; }
    if (a === 'prof-auto') { try { localStorage.removeItem('labo-profile-lock'); } catch (e) {} detectProfile.n = -1; render(); return; }
    if (a === 'clearb') { try { localStorage.removeItem(BUILDS_KEY); } catch (e) {} render(); return; }
    if (a === 'reset') {
      if (!resetArmed) { resetArmed = true; msg().textContent = 'Clique encore sur Vider pour effacer les combats (les monstres et mécaniques sont gardés).'; setTimeout(() => { resetArmed = false; }, 4000); return; }
      db.fights = []; db.seen = []; save(); resetArmed = false; render(); return;
    }
    if (a === 'export') {
      msg().textContent = 'Lecture de l’inventaire, du deck et du personnage…';
      try {
        const json = JSON.stringify(await exportForLabo());
        try { await navigator.clipboard.writeText(json); msg().textContent = 'Copié. Colle-le dans le Labo, onglet Mes données.'; }
        catch (e) { showText(json); msg().textContent = 'Copie refusée : sélectionne le texte affiché.'; }
      } catch (e) { msg().textContent = 'Export impossible : ' + e.message; }
    }
  }
  function showText(t) {
    const ta = document.createElement('textarea'); ta.value = t; ta.readOnly = true;
    ta.setAttribute('style', 'width:100%;height:80px;margin-top:6px;font:11px monospace');
    panel.appendChild(ta); ta.select();
  }

  // Accès en lecture pour le pont Claude in Chrome
  window.LaboRec = { db, summary, exportForLabo, mechSummary, version: '1.3.0' };

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', build); else build();
})();
