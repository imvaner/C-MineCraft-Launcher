// ============================================================
// main.js — главный процесс C Minerva Launcher
// ============================================================
// Функционал:
//  - сборки Vanilla: список версий Mojang, скачивание в ver/<Сборка>/
//  - аккаунты (offline-профили) — ver/accounts.json
//  - авто-скачивание Java (Eclipse Temurin) нужной версии — ver/java/<major>/
//  - запуск сборки: natives, classpath, аргументы, лог игры
// ============================================================

const { app, BrowserWindow, ipcMain, dialog, shell } = require('electron');
const path = require('path');
const fs = require('fs');
const os = require('os');
const https = require('https');
const http = require('http');
const crypto = require('crypto');
const zlib = require('zlib');
const { spawn, spawnSync } = require('child_process');

const tar = require('tar');
const AdmZip = require('adm-zip');

const fsp = fs.promises;

// ---------- пути (всё внутри папки лаунчера) ----------
// В упакованной версии (exe) — рядом с самим exe, т.к. app.asar только для чтения.
const ROOT           = app.isPackaged ? path.dirname(process.execPath) : __dirname;
const VER_DIR        = path.join(ROOT, 'ver');
const CACHE_DIR      = path.join(VER_DIR, 'cache');
const VERSIONS_DIR   = path.join(VER_DIR, 'versions');
const LIB_DIR        = path.join(VER_DIR, 'libraries');
const ASSETS_DIR     = path.join(VER_DIR, 'assets');
const JAVA_DIR       = path.join(VER_DIR, 'java');
const BUILDS_FILE    = path.join(VER_DIR, 'builds.json');
const ACCOUNTS_FILE  = path.join(VER_DIR, 'accounts.json');
const SETTINGS_FILE  = path.join(VER_DIR, 'settings.json');
const MANIFEST_CACHE = path.join(CACHE_DIR, 'version_manifest.json');

const MANIFEST_URL   = 'https://piston-meta.mojang.com/mc/game/version_manifest_v2.json';
const ADOPTIUM_API   = 'https://api.adoptium.net/v3/assets/latest';

// загрузчики модов
const FABRIC_META    = 'https://meta.fabricmc.net/v2';
const QUILT_META     = 'https://meta.quiltmc.org/v3';
const FORGE_MAVEN    = 'https://maven.minecraftforge.net';
const NEOFORGE_MAVEN = 'https://maven.neoforged.net/releases';
const LOADERS        = ['vanilla', 'fabric', 'quilt', 'forge', 'neoforge'];
// подписи загрузчиков для интерфейса
const LOADER_LABELS  = {
  vanilla: 'Vanilla',
  fabric: 'Fabric',
  quilt: 'Quilt',
  forge: 'Forge',
  neoforge: 'NeoForge'
};

// источники контента (CurseForge требует API-ключ из настроек)
const MODRINTH_API   = 'https://api.modrinth.com/v2';
const CURSEFORGE_API = 'https://api.curseforge.com/v1';
const CURSEFORGE_GAME = 432;                       // Minecraft
const CURSEFORGE_CLASS = {                         // классы CurseForge
  mods: 6,
  modpacks: 4471,
  resourcepacks: 12,
  texturepacks: 12,
  worlds: 17,
  shaders: 65558
};
// CurseForge «releaseType» → человекочитаемо
const CF_LOADER_TYPE = { 1: 'forge', 4: 'fabric', 5: 'quilt', 6: 'neoforge' };

// игровые подпапки по типу содержимого
const CONTENT_DIR = {
  mods: 'mods',
  modpacks: 'modpacks',
  resourcepacks: 'resourcepacks',
  texturepacks: 'resourcepacks',
  worlds: 'saves',
  shaders: 'shaderpacks'
};

// адреса по умолчанию; могут быть переопределены в настройках (пункт «Загрузки»)
const RESOURCES_BASE_DEFAULT = 'https://resources.download.minecraft.net';
const LIBRARIES_BASE_DEFAULT = 'https://libraries.minecraft.net';

// ---------- серверы (папка serv/ рядом с лаунчером) ----------
const SERV_DIR     = path.join(ROOT, 'serv');
const SERVERS_FILE = path.join(SERV_DIR, 'servers.json');
const PAPER_API    = 'https://fill.papermc.io/v3';
const PURPUR_API   = 'https://api.purpurmc.org/v2';

// доступные ядра серверов
const SERVER_CORES = [
  { id: 'vanilla', label: 'Vanilla', note: 'официальное ядро Mojang' },
  { id: 'paper',   label: 'Paper',   note: 'оптимизация и плагины' },
  { id: 'purpur',  label: 'Purpur',  note: 'Paper + доп. настройки' },
  { id: 'fabric',  label: 'Fabric',  note: 'моды (Fabric)' },
  { id: 'forge',   label: 'Forge',   note: 'моды (Forge)' }
];
const SERVER_CORE_LABELS = {
  vanilla: 'Vanilla', paper: 'Paper', purpur: 'Purpur', fabric: 'Fabric', forge: 'Forge'
};

// стандартные ключи server.properties
function defaultServerProperties(port, motd) {
  return {
    'server-port': String(clampInt(port, 1, 65535, 25565)),
    'motd': motd && String(motd).trim() ? String(motd).trim().slice(0, 120) : 'C Minerva Server',
    'online-mode': 'true',
    'max-players': '20',
    'difficulty': 'easy',
    'gamemode': 'survival',
    'pvp': 'true',
    'white-list': 'false',
    'allow-flight': 'false',
    'spawn-protection': '16',
    'view-distance': '10',
    'simulation-distance': '10',
    'level-name': 'world',
    'enable-command-block': 'false'
  };
}

// версии Java, которые можно выбрать вручную в настройках
const JAVA_MAJORS = [8, 11, 17, 21, 25];

const OS_NAME = process.platform === 'win32' ? 'windows'
              : process.platform === 'darwin' ? 'osx'
              : 'linux';
const IS_64 = process.arch === 'x64' || process.arch === 'arm64';

let mainWindow = null;

// ============================================================
// ОКНО — кастомная рамка, фиксация геометрии для Windows
// (сохраняет позицию/размер между запусками, чинит «улетевшее»
//  окно при смене масштаба/DPI или разрешения экрана)
// ============================================================
const WINDOW_BOUNDS_FILE = () => path.join(app.getPath('userData'), 'window.json');

function validBounds(b) {
  if (!b || !Number.isFinite(b.x) || !Number.isFinite(b.y)) return null;
  return b;
}

function loadWindowBounds() {
  try {
    return validBounds(JSON.parse(fs.readFileSync(WINDOW_BOUNDS_FILE(), 'utf8')));
  } catch (_) { return null; }
}
function saveWindowBounds() {
  if (!mainWindow || mainWindow.isDestroyed()) return;
  try {
    const b = mainWindow.getBounds();
    fs.writeFileSync(WINDOW_BOUNDS_FILE(), JSON.stringify(b));
  } catch (_) {}
}

/** Окно обязательно должно быть хотя бы частично видно на любом мониторе */
function clampToVisibleScreen(b) {
  b.width = 1080; b.height = 650;      // размер окна всегда фиксирован
  const screens = require('electron').screen.getAllDisplays();
  const visible = screens.some((d) => {
    const a = d.workArea;
    return b.x < a.x + a.width && b.x + b.width > a.x &&
           b.y < a.y + a.height && b.y + b.height > a.y;
  });
  if (!visible) {
    const d = screens[0] || { workArea: { x: 0, y: 0, width: 1280, height: 720 } };
    b.x = Math.round(d.workArea.x + (d.workArea.width - b.width) / 2);
    b.y = Math.round(d.workArea.y + (d.workArea.height - b.height) / 2);
  }
  return b;
}

function createWindow() {
  const saved = loadWindowBounds() || { x: undefined, y: undefined };
  if (!Number.isFinite(saved.x) || !Number.isFinite(saved.y)) {
    saved.x = undefined; saved.y = undefined;   // центрируем на первом показе
  }
  mainWindow = new BrowserWindow(Object.assign({
    width: 1080,
    height: 650,
    frame: false,                    // кастомная рамка — кнопки в шапке приложения
    resizable: false,                // размер окна фиксирован
    maximizable: false,
    fullscreenable: false,
    autoHideMenuBar: true,
    backgroundColor: '#0a100c',
    webPreferences: {
      contextIsolation: true,
      nodeIntegration: false,
      preload: path.join(__dirname, 'preload.js')
    }
  }, clampToVisibleScreen(saved)));

  mainWindow.setMenuBarVisibility(false);
  mainWindow.loadFile(path.join(__dirname, 'index.html'));

  // масштаб интерфейса из настроек
  mainWindow.webContents.on('did-finish-load', () => {
    try { mainWindow.webContents.setZoomFactor(readSettings().ui.scale); } catch (_) {}
  });

  // запоминаем позицию при завершении работы (Windows DPI-баг с «улетевшим» окном)
  mainWindow.on('move', saveWindowBounds);
  mainWindow.on('close', saveWindowBounds);

  mainWindow.on('closed', () => { mainWindow = null; });
}

function sendEvent(channel, payload) {
  if (mainWindow && !mainWindow.isDestroyed()) {
    mainWindow.webContents.send(channel, payload);
  }
}

// ============================================================
// КАСТОМНАЯ РАМКА — кнопки свернуть/закрыть
// ============================================================
ipcMain.on('win:minimize', () => { if (mainWindow && !mainWindow.isDestroyed()) mainWindow.minimize(); });
ipcMain.on('win:close', () => { if (mainWindow && !mainWindow.isDestroyed()) mainWindow.close(); });

// ============================================================
// HTTP-помощники
// ============================================================
const UA = 'C-Minerva-Launcher';
const REQUEST_DEADLINE = 60000;  // максимум на получение ответа (заголовков)
const BODY_IDLE_TIMEOUT = 30000; // максимум без единого байта тела
const MAX_ATTEMPTS = 3;          // попыток на один запрос/файл (значение по умолчанию)

/** Сколько попыток делать (настраивается во вкладке «Загрузки») */
function maxAttempts() {
  const n = Number(readSettings().downloads.attempts);
  return Number.isFinite(n) ? Math.max(1, Math.min(10, Math.round(n))) : MAX_ATTEMPTS;
}

function sleep(ms) {
  return new Promise((r) => setTimeout(r, ms));
}

/** Повторяет операцию при ошибке с нарастающей паузой (авто-восстановление без перезапуска) */
async function withRetry(fn, label, onRetry, attempts) {
  const max = attempts || maxAttempts();
  let lastErr = null;
  for (let i = 0; i < max; i++) {
    try {
      return await fn();
    } catch (err) {
      lastErr = err;
      if (i >= max - 1) break;
      const wait = Math.min(800 * Math.pow(2, i), 8000) + Math.floor(Math.random() * 400);
      if (onRetry) onRetry('повтор ' + (i + 1) + '/' + (max - 1) + ' через ' + (wait / 1000).toFixed(1) + ' с');
      await sleep(wait);
    }
  }
  throw lastErr;
}

function fetchRaw(url, opts = {}, redirect = 0) {
  const headers = Object.assign({ 'User-Agent': UA }, opts.headers || {});

  return new Promise((resolve, reject) => {
    let settled = false;
    let deadline = null;

    const finish = (fn, arg) => {
      if (settled) return;
      settled = true;
      clearTimeout(deadline);
      fn(arg);
    };

    // текстуры ely.by могут отдаваться по http:// — выбираем модуль по протоколу
    const mod = url.startsWith('http:') ? http : https;
    const req = mod.get(url, { headers }, (res) => {
      const code = res.statusCode;
      if (code >= 300 && code < 400 && res.headers.location) {
        res.resume();
        if (redirect >= 5) return finish(reject, new Error('Слишком много редиректов: ' + url));
        const next = new URL(res.headers.location, url).href;
        return fetchRaw(next, opts, redirect + 1).then(
          (r) => finish(resolve, r),
          (e) => finish(reject, e)
        );
      }
      // 200 — полный ответ, 206 — частичный (докачка)
      if (code !== 200 && code !== 206) {
        res.resume();
        return finish(reject, new Error('HTTP ' + code + ' для ' + url));
      }
      finish(resolve, res);
    });

    // жёсткий общий дедлайн: даже «висящий» сокет/DNS будет оборван
    deadline = setTimeout(() => {
      try { req.destroy(); } catch (_) {}
      finish(reject, new Error('Сервер не отвечает (' + (REQUEST_DEADLINE / 1000) + ' с): ' + url));
    }, REQUEST_DEADLINE);

    // таймаут простоя сокета
    req.setTimeout(BODY_IDLE_TIMEOUT, () => {
      try { req.destroy(); } catch (_) {}
      finish(reject, new Error('Таймаут соединения: ' + url));
    });
    req.on('error', (e) => finish(reject, e));
  });
}

async function fetchJSON(url, attempts) {
  return withRetry(async () => {
    const res = await fetchRaw(url);
    const chunks = [];
    for await (const chunk of res) chunks.push(chunk);
    return JSON.parse(Buffer.concat(chunks).toString('utf8'));
  }, url, null, attempts);
}

/** fetchJSON с дополнительными заголовками (нужно для CurseForge API-ключа) */
async function fetchJSONHeaders(url, headers, attempts) {
  return withRetry(async () => {
    const res = await fetchRaw(url, { headers });
    const chunks = [];
    for await (const chunk of res) chunks.push(chunk);
    return JSON.parse(Buffer.concat(chunks).toString('utf8'));
  }, url, null, attempts);
}

async function fetchText(url, attempts) {
  return withRetry(async () => {
    const res = await fetchRaw(url);
    const chunks = [];
    for await (const chunk of res) chunks.push(chunk);
    return Buffer.concat(chunks).toString('utf8');
  }, url, null, attempts);
}

/** POST JSON-запрос (нужен Modrinth /version_files — поиск файлов по хэшу) */
async function fetchJSONPost(url, body, attempts, extraHeaders) {
  return withRetry(async () => {
    const payload = Buffer.from(JSON.stringify(body), 'utf8');
    const res = await postRaw(url, payload, extraHeaders);
    const chunks = [];
    for await (const chunk of res) chunks.push(chunk);
    return JSON.parse(Buffer.concat(chunks).toString('utf8'));
  }, url, null, attempts);
}

function postRaw(url, payload, extraHeaders, redirect = 0) {
  const headers = Object.assign({
    'User-Agent': UA,
    'Content-Type': 'application/json',
    'Content-Length': payload.length
  }, extraHeaders || {});

  return new Promise((resolve, reject) => {
    let settled = false;
    let deadline = null;

    const finish = (fn, arg) => {
      if (settled) return;
      settled = true;
      clearTimeout(deadline);
      fn(arg);
    };

    const req = https.request(url, { method: 'POST', headers }, (res) => {
      const code = res.statusCode;
      if (code >= 300 && code < 400 && res.headers.location) {
        res.resume();
        if (redirect >= 5) return finish(reject, new Error('Слишком много редиректов: ' + url));
        const next = new URL(res.headers.location, url).href;
        return postRaw(next, payload, extraHeaders, redirect + 1).then(
          (r) => finish(resolve, r),
          (e) => finish(reject, e)
        );
      }
      if (code !== 200 && code !== 206) {
        res.resume();
        return finish(reject, new Error('HTTP ' + code + ' для ' + url));
      }
      finish(resolve, res);
    });

    deadline = setTimeout(() => {
      try { req.destroy(); } catch (_) {}
      finish(reject, new Error('Сервер не отвечает (' + (REQUEST_DEADLINE / 1000) + ' с): ' + url));
    }, REQUEST_DEADLINE);

    req.setTimeout(BODY_IDLE_TIMEOUT, () => {
      try { req.destroy(); } catch (_) {}
      finish(reject, new Error('Таймаут соединения: ' + url));
    });
    req.on('error', (e) => finish(reject, e));
    req.write(payload);
    req.end();
  });
}

/** XML-манифест maven → список <version> по порядку */
function parseMavenVersions(xml) {
  const out = [];
  const re = /<version>([^<]+)<\/version>/g;
  let m;
  while ((m = re.exec(xml))) out.push(m[1]);
  return out;
}

function fmtBytes(n) {
  if (!n) return '0 Б';
  if (n >= 1024 * 1024 * 1024) return (n / (1024 * 1024 * 1024)).toFixed(2) + ' ГБ';
  if (n >= 1024 * 1024) return (n / (1024 * 1024)).toFixed(1) + ' МБ';
  if (n >= 1024) return Math.round(n / 1024) + ' КБ';
  return n + ' Б';
}

/**
 * Скачивает файл в <dest>.part и переименовывает по завершении.
 *  - докачка с места обрыва (HTTP Range), недокачанный .part сохраняется;
 *  - обрыв при простое тела (BODY_IDLE_TIMEOUT) — вызывающий код повторит;
 *  - при 416 (файл уже больше, чем нужно) начинает заново.
 */
async function downloadFile(url, dest, onBytes) {
  await fsp.mkdir(path.dirname(dest), { recursive: true });
  const tmp = dest + '.part';

  for (let round = 0; round < 2; round++) {
    let already = 0;
    try { already = (await fsp.stat(tmp)).size; } catch (_) { already = 0; }

    const headers = already > 0 ? { Range: 'bytes=' + already + '-' } : {};
    let res;
    try {
      res = await fetchRaw(url, { headers });
    } catch (err) {
      if (already > 0 && /HTTP 416/.test(err.message)) {
        await fsp.rm(tmp, { force: true }).catch(() => {});
        continue;                              // начинаем заново
      }
      throw err;
    }

    const resuming = already > 0 && res.statusCode === 206;
    if (already > 0 && !resuming) {
      await fsp.rm(tmp, { force: true }).catch(() => {});   // сервер не поддержал Range
    }

    const base = resuming ? already : 0;
    const total = Number(res.headers['content-length'] || 0) + base;
    if (base && onBytes) onBytes(base, total || base);

    await new Promise((resolve, reject) => {
      const ws = fs.createWriteStream(tmp, { flags: resuming ? 'a' : 'w' });
      let got = base;
      let settled = false;
      let idle = null;

      const fail = (err) => {
        if (settled) return;
        settled = true;
        clearTimeout(idle);
        try { res.destroy(); } catch (_) {}
        try { ws.destroy(); } catch (_) {}
        // .part НЕ удаляем: следующий повтор докачает с этого места
        reject(err);
      };

      const done = () => {
        if (settled) return;
        settled = true;
        clearTimeout(idle);
        ws.close(() => resolve());
      };

      const idleMs = clampInt(readSettings().downloads.idleTimeout, 5, 600,
        DEFAULT_SETTINGS.downloads.idleTimeout) * 1000;
      const bump = () => {
        clearTimeout(idle);
        idle = setTimeout(
          () => fail(new Error('Данные не поступают (' + (idleMs / 1000) + ' с)')),
          idleMs
        );
      };
      bump();

      res.on('data', (c) => {
        got += c.length;
        bump();
        if (onBytes) onBytes(got, total || got);
      });
      res.on('error', fail);
      res.on('aborted', () => fail(new Error('Соединение прервано')));
      res.on('close', () => {
        if (!res.complete) fail(new Error('Соединение закрыто до получения всех данных'));
      });

      res.pipe(ws);
      ws.on('finish', done);
      ws.on('error', fail);
    });

    await fsp.rename(tmp, dest);
    return;
  }

  throw new Error('Не удалось скачать файл: ' + url);
}

/**
 * Пропускает файл, если он уже есть нужного размера; иначе скачивает с автоповторами.
 * opts: { attempts, onBytes, onRetry }
 */
async function downloadIfMissing(url, dest, size, opts = {}) {
  try {
    const st = await fsp.stat(dest);
    if (!size) return false;             // размер неизвестен — считаем готовым
    if (st.size === size) return false;  // уже скачано

    // файл есть, но не того размера: превращаем в .part, чтобы докачать с места
    if (st.size < size) await fsp.rename(dest, dest + '.part').catch(() => {});
    else await fsp.rm(dest, { force: true }).catch(() => {});
  } catch (_) { /* файла нет — качаем с нуля */ }

  const name = path.basename(dest);
  await withRetry(async () => {
    await downloadFile(url, dest, opts.onBytes);

    if (size) {
      const st = await fsp.stat(dest);
      if (st.size !== size) {
        if (st.size < size) {
          // недокачанный: вернём в .part, чтобы следующий повтор продолжил
          await fsp.rename(dest, dest + '.part').catch(() => {});
        } else {
          await fsp.rm(dest, { force: true }).catch(() => {});
        }
        throw new Error('Размер не совпал: получено ' + st.size + ' б вместо ' + size + ' б');
      }
    }
  }, name, opts.onRetry, opts.attempts || maxAttempts());

  return true;
}

// ============================================================
// МАНИФЕСТ ВЕРСИЙ
// ============================================================
async function getManifest() {
  // если есть кэш — не ждём сеть долго: одна попытка, при неудаче берём кэш
  let cached = null;
  try { cached = JSON.parse(await fsp.readFile(MANIFEST_CACHE, 'utf8')); } catch (_) {}
  if (cached && Array.isArray(cached.versions)) {
    try {
      const m = await fetchJSON(MANIFEST_URL, 1);
      if (m && Array.isArray(m.versions)) {
        await fsp.writeFile(MANIFEST_CACHE, JSON.stringify(m));
        return m;
      }
    } catch (_) { /* сеть недоступна — работаем из кэша */ }
    return cached;
  }

  try {
    const m = await fetchJSON(MANIFEST_URL);
    if (!m || !Array.isArray(m.versions)) throw new Error('некорректный манифест');
    await fsp.mkdir(CACHE_DIR, { recursive: true });
    await fsp.writeFile(MANIFEST_CACHE, JSON.stringify(m));
    return m;
  } catch (err) {
    throw new Error('Не удалось получить список версий Minecraft: ' + err.message);
  }
}

// ============================================================
// ПРАВИЛА (rules) — нужна ли библиотека/аргумент для этой ОС
// ============================================================
// включённые «фичи» лаунчера: demo-режим, кастомное разрешение и т.п. не используем,
// поэтому правила вида {"features":{"is_demo_user":true}} не должны применяться
const FEATURES = {};

function ruleAllowed(rules) {
  if (!rules || rules.length === 0) return true;
  let allowed = false;
  for (const r of rules) {
    let ok = true;
    if (r.os) {
      if (r.os.name && r.os.name !== OS_NAME) ok = false;
      if (r.os.arch === 'x86' && process.arch !== 'ia32') ok = false;
      try {
        if (r.os.version && !(new RegExp(r.os.version).test(os.version()))) ok = false;
      } catch (_) { /* некорректная регулярка — игнорируем условие */ }
    }
    if (ok && r.features) {
      for (const key of Object.keys(r.features)) {
        if (Boolean(FEATURES[key]) !== Boolean(r.features[key])) ok = false;
      }
    }
    if (ok) allowed = (r.action === 'allow');
  }
  return allowed;
}

// ============================================================
// БИБЛИОТЕКИ
// ============================================================
function mavenPath(name, classifier) {
  const [g, a, v, c] = name.split(':');
  const cls = classifier || c;
  return `${g.replace(/\./g, '/')}/${a}/${v}/${a}-${v}${cls ? '-' + cls : ''}.jar`;
}

function nativeClassifier(lib) {
  if (!lib.natives) return null;
  const tmpl = lib.natives[OS_NAME];
  if (!tmpl) return null;
  return tmpl.replace('${arch}', IS_64 ? '64' : '32');
}

function libPath(lib, classifier) {
  const art = lib.downloads && lib.downloads.artifact;
  if (!classifier && art && art.path) return art.path;
  if (classifier && lib.downloads && lib.downloads.classifiers) {
    const info = lib.downloads.classifiers[classifier];
    if (info && info.path) return info.path;
  }
  return mavenPath(lib.name, classifier);
}

async function downloadLibrary(lib) {
  const failed = [];
  const cls = nativeClassifier(lib);
  const art = lib.downloads && lib.downloads.artifact;

  // 1) обычный артефакт библиотеки
  if (art && art.url) {
    const rel = art.path || mavenPath(lib.name);
    try {
      await downloadIfMissing(art.url, path.join(LIB_DIR, rel), art.size);
    } catch (err) {
      // у «нативных» библиотек (lwjgl-platform и т.п.) artifact может отсутствовать — это нормально
      if (!cls) failed.push(lib.name + ' — artifact: ' + err.message);
    }
  } else if (!cls) {
    // старый формат манифеста: только name/url, путь по схеме maven
    const base = String(lib.url || librariesBase()).replace(/\/?$/, '/');
    const rel = mavenPath(lib.name);
    try {
      await downloadIfMissing(base + rel, path.join(LIB_DIR, rel), null);
    } catch (err) {
      failed.push(lib.name + ' — maven: ' + err.message);
    }
  }

  // 2) нативные библиотеки для текущей ОС — качаем отдельно и обязательно
  if (cls) {
    const info = lib.downloads && lib.downloads.classifiers && lib.downloads.classifiers[cls];
    const rel = (info && info.path) || mavenPath(lib.name, cls);
    const dest = path.join(LIB_DIR, rel);
    try {
      if (info && info.url) await downloadIfMissing(info.url, dest, info.size);
      else await downloadIfMissing(librariesBase() + '/' + rel, dest, null);
    } catch (err) {
      failed.push(lib.name + ' — ' + cls + ': ' + err.message);
    }
  }

  return failed;
}

/** Список нативных jar'ов текущей ОС, которых нет на диске */
function nativeJarsMissing(v) {
  const missing = [];
  for (const lib of (v.libraries || [])) {
    if (!ruleAllowed(lib.rules)) continue;
    const cls = nativeClassifier(lib);
    if (!cls) continue;
    const rel = libPath(lib, cls);
    if (!fs.existsSync(path.join(LIB_DIR, rel))) missing.push(rel.split('/').pop());
  }
  return missing;
}

// ============================================================
// РЕЕСТР СБОРОК
// ============================================================
function readBuilds() {
  try {
    const list = JSON.parse(fs.readFileSync(BUILDS_FILE, 'utf8'));
    return Array.isArray(list) ? list : [];
  } catch (_) {
    return [];
  }
}

function writeBuilds(list) {
  fs.mkdirSync(VER_DIR, { recursive: true });
  fs.writeFileSync(BUILDS_FILE, JSON.stringify(list, null, 2));
}

function updateBuild(name, patch) {
  const list = readBuilds();
  const b = list.find((x) => x.name === name);
  if (!b) return;
  Object.assign(b, patch);
  writeBuilds(list);
}

function cleanName(raw) {
  const s = String(raw || '').trim().replace(/\s+/g, ' ');
  if (!s) throw new Error('Введите название сборки');
  if (s.length > 40) throw new Error('Название слишком длинное (макс. 40 символов)');
  if (/[/\\:*?"<>|]/.test(s)) throw new Error('Название содержит запрещённые символы');
  if (s === '.' || s === '..') throw new Error('Недопустимое название');
  return s;
}

// ============================================================
// АККАУНТЫ (offline-профили)
// ============================================================
function readAccounts() {
  try {
    const list = JSON.parse(fs.readFileSync(ACCOUNTS_FILE, 'utf8'));
    return Array.isArray(list) ? list : [];
  } catch (_) {
    return [];
  }
}

function writeAccounts(list) {
  fs.mkdirSync(VER_DIR, { recursive: true });
  fs.writeFileSync(ACCOUNTS_FILE, JSON.stringify(list, null, 2));
}

function offlineUUID(name) {
  const h = crypto.createHash('md5').update('OfflinePlayer:' + name, 'utf8').digest();
  h[6] = (h[6] & 0x0f) | 0x30;
  h[8] = (h[8] & 0x3f) | 0x80;
  const hex = h.toString('hex');
  return [hex.slice(0, 8), hex.slice(8, 12), hex.slice(12, 16), hex.slice(16, 20), hex.slice(20)].join('-');
}

function cleanNick(raw) {
  const s = String(raw || '').trim();
  if (!s) throw new Error('Введите ник');
  if (!/^[A-Za-z0-9_]{3,16}$/.test(s)) {
    throw new Error('Ник: 3–16 символов, латиница, цифры и подчёркивание');
  }
  return s;
}

// ============================================================
// ELY.BY — реальная авторизация (authserver.ely.by, Yggdrasil API)
// ============================================================
const ELY_AUTH_BASE = 'https://authserver.ely.by';

/** POST на authserver.ely.by. Возвращает { status, body } (body — JSON или null). */
function elybyPost(endpoint, body) {
  const payload = Buffer.from(JSON.stringify(body), 'utf8');
  return new Promise((resolve, reject) => {
    const headers = {
      'User-Agent': UA,
      'Content-Type': 'application/json',
      'Content-Length': payload.length
    };
    const req = https.request(ELY_AUTH_BASE + endpoint, { method: 'POST', headers }, (res) => {
      const chunks = [];
      res.on('data', (c) => chunks.push(c));
      res.on('end', () => {
        const text = Buffer.concat(chunks).toString('utf8');
        let json = null;
        try { json = text ? JSON.parse(text) : null; } catch (_) {}
        resolve({ status: res.statusCode, body: json });
      });
    });
    req.on('error', reject);
    req.write(payload);
    req.end();
  });
}

/** Бросает понятную ошибку по ответу authserver; для 2FA — special-флаг needOtp */
function elybyThrow(res, context) {
  const b = res.body || {};
  if (b.errorMessage === 'Account protected with two factor auth.') {
    const e = new Error('Аккаунт защищён двухфакторной аутентификацией (2FA)');
    e.needOtp = true;
    throw e;
  }
  throw new Error(context + ': ' + (b.errorMessage || b.error || ('HTTP ' + res.status)));
}

/** "1a2b...32hex" → uuid с дефисами */
function dashUuid(id) {
  const h = String(id || '').replace(/-/g, '');
  return h.length === 32
    ? [h.slice(0, 8), h.slice(8, 12), h.slice(12, 16), h.slice(16, 20), h.slice(20)].join('-')
    : String(id || '');
}

/**
 * Публичный профиль ely.by по нику → uuid профиля (без входа).
 * GET authserver.ely.by/api/users/profiles/minecraft/{nick}; 204 — ника нет.
 * Нужен, чтобы игра нашла скин: текстуры ely.by привязаны к ely.by-uuid.
 */
async function elybyProfileUuid(nick) {
  try {
    const res = await fetchRaw(ELY_AUTH_BASE + '/api/users/profiles/minecraft/' + encodeURIComponent(nick));
    const chunks = [];
    for await (const c of res) chunks.push(c);
    const p = JSON.parse(Buffer.concat(chunks).toString('utf8'));
    return (p && p.id) ? dashUuid(p.id) : null;
  } catch (_) {
    return null;   // 204 (нет ника) или сеть — оставляем текущий uuid
  }
}

// ============================================================
// AUTHLIB-INJECTOR — реальные скины ely.by В ИГРЕ
// Агент переводит сессию и загрузку текстур клиента на ely.by:
// без него клиент идёт в Mojang и скин всегда Steve.
// ============================================================
const AUTHLIB_VERSION = '1.2.8';
const AUTHLIB_URL = 'https://github.com/yushijinhun/authlib-injector/releases/download/v' +
  AUTHLIB_VERSION + '/authlib-injector-' + AUTHLIB_VERSION + '.jar';
const AUTHLIB_SHA256 = '9c7f4343e6c82034958ffb48c14a2cb0c85928be7283103ce17da00c6d5a7b10';
const AUTHLIB_PATH = path.join(VER_DIR, 'authlib-injector-' + AUTHLIB_VERSION + '.jar');

/** Скачивает (однократно, с проверкой sha256) authlib-injector в ver/ и возвращает путь. */
async function ensureAuthlib(progress) {
  try {
    if (fs.existsSync(AUTHLIB_PATH) && fs.statSync(AUTHLIB_PATH).size > 100000) return AUTHLIB_PATH;
  } catch (_) {}
  if (progress) progress('Скачивание authlib-injector (скины ely.by)…', 100);
  const buf = await withRetry(async () => {
    const res = await fetchRaw(AUTHLIB_URL);
    const chunks = [];
    for await (const c of res) chunks.push(c);
    return Buffer.concat(chunks);
  }, AUTHLIB_URL, null, 2);
  const sha = crypto.createHash('sha256').update(buf).digest('hex');
  if (sha !== AUTHLIB_SHA256) throw new Error('файл authlib-injector повреждён (контрольная сумма)');
  if (buf[0] !== 0x50 || buf[1] !== 0x4b) throw new Error('authlib-injector — не jar-файл');
  fs.mkdirSync(VER_DIR, { recursive: true });
  fs.writeFileSync(AUTHLIB_PATH, buf);
  return AUTHLIB_PATH;
}

/**
 * Прямая авторизация на ELY.by: логин + пароль (для 2FA — "пароль:код").
 * Возвращает { accessToken, clientToken, uuid, profileName }.
 */
async function elybyAuthenticate(login, password) {
  const clientToken = crypto.randomBytes(16).toString('hex');
  const res = await elybyPost('/auth/authenticate', {
    username: login,
    password,
    clientToken,
    requestUser: true
  });
  if (res.status !== 200) elybyThrow(res, 'Вход в ELY.by');

  const b = res.body || {};
  const profiles = Array.isArray(b.availableProfiles) ? b.availableProfiles : [];
  const profile = b.selectedProfile ||
    profiles.find((p) => String(p.name).toLowerCase() === String(login).toLowerCase()) ||
    profiles[0];
  if (!profile) {
    throw new Error('На ELY.by не привязан профиль Minecraft к «' + login + '»');
  }
  return {
    accessToken: b.accessToken,
    clientToken: b.clientToken || clientToken,
    uuid: dashUuid(profile.id),
    profileName: profile.name
  };
}

/** Проверка токена: true — живой */
async function elybyTokenValid(accessToken) {
  try {
    const res = await elybyPost('/auth/validate', { accessToken });
    return res.status === 200;
  } catch (_) {
    return false; // нет сети — считаем токен пригодным, не блокируем запуск
  }
}

/** Обновление токена; при неудаче — null */
async function elybyTokenRefresh(accessToken, clientToken) {
  try {
    const res = await elybyPost('/auth/refresh', { accessToken, clientToken, requestUser: true });
    if (res.status !== 200 || !res.body || !res.body.accessToken) return null;
    return {
      accessToken: res.body.accessToken,
      clientToken: res.body.clientToken || clientToken,
      uuid: res.body.selectedProfile ? dashUuid(res.body.selectedProfile.id) : null
    };
  } catch (_) {
    return null;
  }
}

/**
 * Перед запуском: validate → refresh для ely.by-аккаунтов.
 * Мёртвый токен помечается (authed=false), запуск не блокируется.
 */
async function ensureElybyToken(account) {
  if (!account || account.type !== 'elyby' || !account.accessToken) return account;
  if (await elybyTokenValid(account.accessToken)) return account;

  const fresh = await elybyTokenRefresh(account.accessToken, account.clientToken);
  const accounts = readAccounts();
  const a = accounts.find((x) => x.name === account.name);
  if (fresh) {
    if (a) {
      a.accessToken = fresh.accessToken;
      a.clientToken = fresh.clientToken;
      if (fresh.uuid) a.uuid = fresh.uuid;
      writeAccounts(accounts);
    }
    return Object.assign({}, account, { accessToken: fresh.accessToken, uuid: fresh.uuid || account.uuid });
  }
  if (a) {
    a.authed = false;
    delete a.accessToken;
    writeAccounts(accounts);
  }
  return Object.assign({}, account, { authed: false, accessToken: null });
}

// ============================================================
// СКИНЫ — текстуры с ely.by + локальный кеш ver/skins/
// ============================================================
const SKINS_DIR = path.join(VER_DIR, 'skins');
// ручная папка пользователя — «skins» рядом с лаунчером/exe (только чтение)
const SKINS_USER_DIR = path.join(ROOT, 'skins');
const ELY_TEXTURES_BASE = 'https://skinsystem.ely.by';

/** Откуда читаются скины: ver/skins (+ папка «skins» рядом с лаунчером, если есть) */
function skinDirs() {
  const dirs = [SKINS_DIR];
  try {
    if (SKINS_USER_DIR !== SKINS_DIR && fs.statSync(SKINS_USER_DIR).isDirectory()) dirs.push(SKINS_USER_DIR);
  } catch (_) {}
  return dirs;
}

/** Ищет PNG скина в обеих папках; возвращает полный путь или null */
function findSkinFile(name) {
  const safe = path.basename(String(name || ''));
  if (!/\.png$/i.test(safe)) return null;
  for (const d of skinDirs()) {
    const p = path.join(d, safe);
    try { if (fs.existsSync(p)) return p; } catch (_) {}
  }
  return null;
}

function skinDataUrl(name) {
  const p = findSkinFile(name);
  return p ? 'data:image/png;base64,' + fs.readFileSync(p).toString('base64') : null;
}

/**
 * Текущие текстуры (скин/пелерина) игрока с ely.by по нику.
 * { status: 'ok', data } | { status: 'notfound' } | { status: 'error', error }
 */
function elyTextures(nick) {
  // отключено в настройках (Контент → скины ELY.by) — считаем «своего скина нет»
  if (readSettings().content.elyTextures === false) {
    return Promise.resolve({ status: 'notfound' });
  }
  return new Promise((resolve) => {
    const url = ELY_TEXTURES_BASE + '/textures/' + encodeURIComponent(nick);
    const req = https.get(url, { headers: { 'User-Agent': UA } }, (res) => {
      if (res.statusCode === 204 || res.statusCode === 404) {
        res.resume();
        return resolve({ status: 'notfound' });
      }
      const chunks = [];
      res.on('data', (c) => chunks.push(c));
      res.on('end', () => {
        if (res.statusCode !== 200) return resolve({ status: 'notfound' });
        try { resolve({ status: 'ok', data: JSON.parse(Buffer.concat(chunks).toString('utf8')) }); }
        catch (_) { resolve({ status: 'error', error: 'Непонятный ответ ely.by' }); }
      });
    });
    req.on('error', (e) => resolve({ status: 'error', error: e.message }));
    req.setTimeout(BODY_IDLE_TIMEOUT, () => {
      try { req.destroy(); } catch (_) {}
      resolve({ status: 'error', error: 'Сервер ely.by не отвечает' });
    });
  });
}

/** Скачивает PNG в ver/skins/<имя>. Возвращает { file, dataUrl }. */
async function downloadSkinPng(url, fileName) {
  const buf = await withRetry(async () => {
    const res = await fetchRaw(url);
    const chunks = [];
    for await (const c of res) chunks.push(c);
    return Buffer.concat(chunks);
  }, url, null, 2);
  fs.mkdirSync(SKINS_DIR, { recursive: true });
  const safe = path.basename(String(fileName)).replace(/[^A-Za-z0-9._-]/g, '_');
  fs.writeFileSync(path.join(SKINS_DIR, safe), buf);
  return { file: safe, dataUrl: 'data:image/png;base64,' + buf.toString('base64') };
}

/**
 * Текущий скин игрока с ely.by: качает текстуру в кеш.
 * Возвращает { skin: { file, model, capeFile }, dataUrl } или null (нет скина).
 * Бросает ошибку при недоступности сервера ely.by.
 */
async function elySkinForNick(nick, filePrefix) {
  const t = await elyTextures(nick);
  if (t.status === 'error') throw new Error('Не удалось получить скин с ely.by: ' + t.error);
  if (t.status !== 'ok' || !t.data || !t.data.SKIN || !t.data.SKIN.url) return null;
  const model = (t.data.SKIN.metadata && t.data.SKIN.metadata.model === 'slim') ? 'slim' : 'wide';
  const dl = await downloadSkinPng(t.data.SKIN.url, (filePrefix || nick) + '.png');
  const out = { file: dl.file, model, updated: new Date().toISOString() };
  if (t.data.CAPE && t.data.CAPE.url) {
    try {
      const cape = await downloadSkinPng(t.data.CAPE.url, (filePrefix || nick) + '-cape.png');
      out.capeFile = cape.file;
    } catch (_) { /* пелерина не обязательна */ }
  }
  return { skin: out, dataUrl: dl.dataUrl };
}

/** Привязывает свежий скин с ely.by к аккаунту (best-effort — не бросает). */
async function attachElySkin(accounts, acc) {
  try {
    const r = await elySkinForNick(acc.name, acc.name);
    if (r) { acc.skin = r.skin; writeAccounts(accounts); return r; }
  } catch (_) {}
  return null;
}

// ============================================================
// НАСТРОЙКИ — ver/settings.json
// ============================================================
// Модель (все поля необязательны — недостающие берутся из DEFAULT_SETTINGS):
//   java.mode       «auto» | «force»  — как выбирать Java для всех сборок
//   java.forceMajor номер версии Java при режиме «force»
//   java.requireExact  true — не принимать более новую Java, чем требуется
//   java.preferBundled true — сначала смотреть ver/java/, потом системную
//   java.jvmArgs    глобальные JVM-флаги (строка)
//   memory.auto     умное распределение ОЗУ (по версии и количеству модов)
//   memory.min/max  -Xms / -Xmx по умолчанию (ручные, когда auto выкл.)
//   perBuild        переопределения для конкретных сборок (java/память/флаги)
//   launch.*        обход LWJGL 2, доп. аргументы игры, поведение лаунчера
//   downloads.*     потоки, попытки, зеркала
//   ui.*            анимации, консоль

const DEFAULT_SETTINGS = {
  java: {
    mode: 'auto',          // auto | force
    forceMajor: 17,
    requireExact: false,
    preferBundled: true,
    jvmArgs: '',
    customPath: ''         // своя Java: путь к java/javaw (пусто = авто-подбор)
  },
  memory: {
    auto: true,           // сам подбирать ОЗУ по версии + модам
    min: '512M',
    max: '2G'
  },
  perBuild: {},            // { "Имя сборки": { javaMode, javaMajor, jvmArgs, memoryMin, memoryMax } }
  launch: {
    lwjgl2Fallback: 'auto',  // auto | always | never  (обход XRandR для LWJGL 2)
    extraGameArgs: '',
    minimizeOnLaunch: false,
    closeOnLaunch: false,    // закрыть лаунчер после запуска игры
    autoOpenConsole: true,
    logToFile: false,        // писать лог игры в ver/logs/
    width: 0,                // окно игры: 0 = как в игре
    height: 0,
    fullscreen: false
  },
  downloads: {
    concurrency: 12,
    attempts: MAX_ATTEMPTS,
    resourcesBase: RESOURCES_BASE_DEFAULT,
    librariesBase: LIBRARIES_BASE_DEFAULT,
    idleTimeout: 30          // секунд без байтов до обрыва закачки
  },
  content: {
    defaultSource: 'modrinth',  // modrinth | curseforge
    curseforgeKey: '',          // API-ключ CurseForge (нужен только для CurseForge)
    elyTextures: true           // ходить в скинсистему ELY.by за скинами
  },
  accounts: {
    validateOnLaunch: true      // обновлять сессию ELY.by (validate → refresh) перед запуском
  },
  servers: {
    memoryMin: '',               // ОЗУ серверов по умолчанию (пусто = как в общих)
    memoryMax: '',
    jvmArgs: ''                 // доп. JVM-флаги только для серверов
  },
  ui: {
    animations: true,
    consoleAutoscroll: true,
    scale: 1,                    // масштаб интерфейса 0.6–2.0
    confirmDelete: true,         // спрашивать подтверждение при удалении
    buildsGroup: 'none'          // группировка сборок по умолчанию
  }
};

function clampInt(value, min, max, fallback) {
  const n = Number(value);
  if (!Number.isFinite(n)) return fallback;
  return Math.max(min, Math.min(max, Math.round(n)));
}

function clampStr(value, maxLen, fallback) {
  if (typeof value !== 'string') return fallback;
  const s = value.trim();
  if (!s) return fallback;
  return s.slice(0, maxLen);
}

/** Нормализует настройки: отбрасывает мусор, чинит диапазоны, добивает значения по умолчанию */
function normalizeSettings(raw) {
  const src = (raw && typeof raw === 'object') ? raw : {};
  const j = (src.java && typeof src.java === 'object') ? src.java : {};
  const mem = (src.memory && typeof src.memory === 'object') ? src.memory : {};
  const launch = (src.launch && typeof src.launch === 'object') ? src.launch : {};
  const dl = (src.downloads && typeof src.downloads === 'object') ? src.downloads : {};
  const content = (src.content && typeof src.content === 'object') ? src.content : {};
  const acc = (src.accounts && typeof src.accounts === 'object') ? src.accounts : {};
  const srv = (src.servers && typeof src.servers === 'object') ? src.servers : {};
  const ui = (src.ui && typeof src.ui === 'object') ? src.ui : {};

  const memRe = /^\d{1,5}[kmgKMGT]?[bB]?$/;
  const memValue = (v, fb) => (typeof v === 'string' && memRe.test(v.trim())) ? v.trim() : fb;

  const out = {
    java: {
      mode: j.mode === 'force' ? 'force' : 'auto',
      forceMajor: clampInt(j.forceMajor, 8, 30, DEFAULT_SETTINGS.java.forceMajor),
      requireExact: j.requireExact === true,
      preferBundled: j.preferBundled !== false,
      jvmArgs: typeof j.jvmArgs === 'string' ? j.jvmArgs.trim().slice(0, 2000) : '',
      customPath: typeof j.customPath === 'string' ? j.customPath.trim().slice(0, 500) : ''
    },
    memory: {
      auto: mem.auto !== false,
      min: memValue(mem.min, DEFAULT_SETTINGS.memory.min),
      max: memValue(mem.max, DEFAULT_SETTINGS.memory.max)
    },
    perBuild: {},
    launch: {
      lwjgl2Fallback: ['auto', 'always', 'never'].includes(launch.lwjgl2Fallback)
        ? launch.lwjgl2Fallback : 'auto',
      extraGameArgs: typeof launch.extraGameArgs === 'string'
        ? launch.extraGameArgs.trim().slice(0, 2000) : '',
      minimizeOnLaunch: launch.minimizeOnLaunch === true,
      closeOnLaunch: launch.closeOnLaunch === true,
      autoOpenConsole: launch.autoOpenConsole !== false,
      logToFile: launch.logToFile === true,
      width: clampInt(launch.width, 0, 7680, 0),
      height: clampInt(launch.height, 0, 4320, 0),
      fullscreen: launch.fullscreen === true
    },
    downloads: {
      concurrency: clampInt(dl.concurrency, 1, 32, DEFAULT_SETTINGS.downloads.concurrency),
      attempts: clampInt(dl.attempts, 1, 10, DEFAULT_SETTINGS.downloads.attempts),
      resourcesBase: clampStr(dl.resourcesBase, 300, DEFAULT_SETTINGS.downloads.resourcesBase).replace(/\/+$/, ''),
      librariesBase: clampStr(dl.librariesBase, 300, DEFAULT_SETTINGS.downloads.librariesBase).replace(/\/+$/, ''),
      idleTimeout: clampInt(dl.idleTimeout, 5, 600, DEFAULT_SETTINGS.downloads.idleTimeout)
    },
    content: {
      defaultSource: content.defaultSource === 'curseforge' ? 'curseforge' : 'modrinth',
      // API-ключ не логируем и не обрезаем пробелами внутри, только по краям
      curseforgeKey: typeof content.curseforgeKey === 'string'
        ? content.curseforgeKey.trim().slice(0, 200) : '',
      elyTextures: content.elyTextures !== false
    },
    accounts: {
      validateOnLaunch: acc.validateOnLaunch !== false
    },
    servers: {
      memoryMin: memValue(srv.memoryMin, ''),
      memoryMax: memValue(srv.memoryMax, ''),
      jvmArgs: typeof srv.jvmArgs === 'string' ? srv.jvmArgs.trim().slice(0, 2000) : ''
    },
    ui: {
      animations: ui.animations !== false,
      consoleAutoscroll: ui.consoleAutoscroll !== false,
      scale: (() => {
        const n = Number(ui.scale);
        if (!Number.isFinite(n) || n <= 0) return 1;
        return Math.max(0.6, Math.min(2, Math.round(n * 100) / 100));
      })(),
      confirmDelete: ui.confirmDelete !== false,
      buildsGroup: ['none', 'version', 'loader', 'status'].includes(ui.buildsGroup)
        ? ui.buildsGroup : 'none'
    }
  };

  // переопределения по сборкам
  const per = (src.perBuild && typeof src.perBuild === 'object') ? src.perBuild : {};
  for (const name of Object.keys(per)) {
    if (!name || name.length > 60) continue;
    const o = per[name];
    if (!o || typeof o !== 'object') continue;
    const entry = {};
    if (o.javaMode === 'force') {
      entry.javaMode = 'force';
      entry.javaMajor = clampInt(o.javaMajor, 8, 30, DEFAULT_SETTINGS.java.forceMajor);
    }
    if (typeof o.jvmArgs === 'string' && o.jvmArgs.trim()) entry.jvmArgs = o.jvmArgs.trim().slice(0, 2000);
    const mn = memValue(o.memoryMin, '');
    const mx = memValue(o.memoryMax, '');
    if (mn) entry.memoryMin = mn;
    if (mx) entry.memoryMax = mx;
    if (Object.keys(entry).length) out.perBuild[name] = entry;
  }

  return out;
}

let settingsCache = null;

function readSettings() {
  if (settingsCache) return settingsCache;
  let raw = null;
  try {
    raw = JSON.parse(fs.readFileSync(SETTINGS_FILE, 'utf8'));
  } catch (_) { /* нет файла или битый json — берём умолчания */ }
  settingsCache = normalizeSettings(raw);
  return settingsCache;
}

function writeSettings(raw) {
  const clean = normalizeSettings(raw);
  fs.mkdirSync(VER_DIR, { recursive: true });
  fs.writeFileSync(SETTINGS_FILE, JSON.stringify(clean, null, 2));
  settingsCache = clean;
  return clean;
}

function resourcesBase() {
  return readSettings().downloads.resourcesBase || RESOURCES_BASE_DEFAULT;
}

function librariesBase() {
  return readSettings().downloads.librariesBase || LIBRARIES_BASE_DEFAULT;
}

/** API-ключ CurseForge (пусто = источник недоступен) */
function curseforgeKey() {
  return readSettings().content.curseforgeKey || '';
}

/** Источник контента по умолчанию (modrinth | curseforge) */
function defaultContentSource() {
  return readSettings().content.defaultSource === 'curseforge' ? 'curseforge' : 'modrinth';
}

function downloadConcurrency() {
  return clampInt(readSettings().downloads.concurrency, 1, 32, 12);
}

/** Разбирает строку с аргументами на список, понимая кавычки: -Dfoo="a b" → [-Dfoo=a b] */
function splitArgs(str) {
  const out = [];
  const s = String(str || '');
  let cur = '';
  let quote = null;
  let has = false;
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if (quote) {
      if (c === quote) quote = null;
      else cur += c;
    } else if (c === '"' || c === "'") {
      quote = c;
      has = true;
    } else if (/\s/.test(c)) {
      if (cur || has) out.push(cur);
      cur = ''; has = false;
    } else {
      cur += c;
    }
  }
  if (cur || has) out.push(cur);
  return out;
}

/**
 * Умное распределение ОЗУ: база по версии Minecraft + запас под моды,
 * с ограничением по физической памяти системы (оставляем системе ~2 ГБ)
 * и разумным потолком (больше ~12–16 ГБ игре не нужно — растёт пауза GC).
 * Возвращает { min, max } в мегабайтах.
 */
function smartMemoryMb(mcVersion, modCount) {
  // --- база по версии ---
  let base = 3072;
  const m = String(mcVersion || '').match(/^(\d+)\.(\d+)/);
  if (m) {
    const major = Number(m[1]), minor = Number(m[2]);
    if (major === 1 && minor <= 12) base = 1536;   // ≤1.12 — лёгкие версии
    else if (major === 1 && minor <= 16) base = 2048; // 1.13–1.16
    else if (major === 1 && minor <= 18) base = 3072; // 1.17–1.18 (тяжелее)
  }

  let total = base;
  const mods = Math.max(0, Math.floor(Number(modCount) || 0));
  if (mods > 0) {
    total += 1024;                                     // запас под мод-загрузчик
    total += Math.min(Math.ceil(mods / 30) * 768, 6144); // +0,75 ГБ на каждые 30 модов (макс. +6 ГБ)
  }

  // --- ограничение по системе ---
  const osTotal = Math.round(os.totalmem() / 1048576);
  const cap = Math.min(Math.max(osTotal - 2048, 1024), osTotal >= 24 ? 16384 : 12288);
  total = Math.min(total, cap);
  total = Math.max(total, 1024);                       // минимум 1 ГБ
  total = Math.ceil(total / 512) * 512;                // округляем вверх до 512 МБ

  const min = Math.max(512, Math.floor((total / 2) / 512) * 512); // Xms = половина Xmx
  return { min, max: total };
}

/** "3072" → "3G", "1536" → "1536M" */
function formatMemMb(mb) {
  return (mb >= 1024 && mb % 1024 === 0) ? (mb / 1024) + 'G' : mb + 'M';
}

/** Сколько модов стоит в сборке (ver/<сборка>/mods/*.jar) */
function countBuildMods(name) {
  try {
    return fs.readdirSync(path.join(VER_DIR, name, 'mods'))
      .filter((f) => /\.jar$/i.test(f)).length;
  } catch (_) { return 0; }
}

/**
 * Настройки для конкретной сборки: переопределения поверх глобальных.
 * Возвращает всё, что нужно для запуска JVM.
 */
function buildLaunchSettings(name, v) {
  const s = readSettings();
  const per = s.perBuild[name] || {};
  const required = (v && v.javaVersion && v.javaVersion.majorVersion) || 8;

  // какая Java нужна: переопределение сборки → глобальное «принудительно» → авто
  let major = required;
  let source = 'авто (по версии Minecraft)';
  if (per.javaMode === 'force') {
    major = per.javaMajor;
    source = 'вручную для этой сборки';
  } else if (s.java.mode === 'force') {
    major = s.java.forceMajor;
    source = 'принудительно для всех сборок';
  }

  const jvmArgs = [].concat(splitArgs(s.java.jvmArgs) || [], splitArgs(per.jvmArgs));

  // память: явное переопределение сборки → умный подбор (если вкл.) → ручные поля
  let memoryMin = per.memoryMin || s.memory.min;
  let memoryMax = per.memoryMax || s.memory.max;
  let memorySource = per.memoryMax ? 'вручную для этой сборки' : 'настройки по умолчанию';
  if (!per.memoryMax && s.memory.auto !== false) {
    const mc = String((v && v.id) || '').match(/^\d+\.\d+(\.\d+)?/) || [];
    const mods = countBuildMods(name);
    const smart = smartMemoryMb(mc[0], mods);
    memoryMax = formatMemMb(smart.max);
    memoryMin = per.memoryMin || formatMemMb(smart.min);
    memorySource = 'авто (версия ' + (mc[0] || '?') + (mods ? ', модов: ' + mods : '') + ')';
  }

  return {
    major,
    required,
    source,
    jvmArgs,
    memoryMin,
    memoryMax,
    memorySource,
    requireExact: s.java.requireExact,
    preferBundled: s.java.preferBundled
  };
}

// ============================================================
// JAVA — поиск, системная, авто-скачивание Temurin
// ============================================================
const JAVA_EXEC = process.platform === 'win32' ? 'java.exe' : 'java';

function findBundledJava(majorDir) {
  const marker = path.join(majorDir, '.java-path');
  try {
    const p = fs.readFileSync(marker, 'utf8').trim();
    if (p && fs.existsSync(p)) return p;
  } catch (_) {}
  try {
    for (const entry of fs.readdirSync(majorDir)) {
      const p = path.join(majorDir, entry, 'bin', JAVA_EXEC);
      if (fs.existsSync(p)) return p;
    }
  } catch (_) {}
  return null;
}

function detectSystemJava() {
  try {
    const r = spawnSync('java', ['-version'], { encoding: 'utf8' });
    const out = String(r.stderr || '') + String(r.stdout || '');
    const m = out.match(/version "(\d+)(?:\.(\d+))?/);
    if (!m) return null;
    return { path: 'java', major: m[1] === '1' ? Number(m[2]) : Number(m[1]) };
  } catch (_) {
    return null;
  }
}

function adoptiumTarget() {
  const arch = process.arch === 'arm64' ? 'aarch64' : process.arch === 'ia32' ? 'x86' : 'x64';
  const osName = process.platform === 'win32' ? 'windows' : process.platform === 'darwin' ? 'mac' : 'linux';
  return { arch, osName };
}

/** Подходит ли найденная Java требуемой версии? */
function isJavaSuitable(found, required, exact) {
  if (found === required) return true;
  if (exact) return false;                       // разрешена только точная версия
  // старая Java не подойдёт никогда; для современных версий (16+) допустима более новая
  return required >= 16 && found > required;
}

/** Гарантирует наличие Java нужной мажорной версии; возвращает путь к java.
 *  opts: { requireExact, preferBundled } */
async function ensureJava(major, onStep, opts = {}) {
  const report = onStep || (() => {});
  const exact = opts.requireExact === true;
  const preferBundled = opts.preferBundled !== false;
  const majorDir = path.join(JAVA_DIR, String(major));

  // своя Java из настроек — главнее любого авто-подбора
  const custom = readSettings().java.customPath;
  if (custom) {
    if (fs.existsSync(custom)) {
      report('Java — своя: ' + custom, 100);
      return custom;
    }
    report('Своя Java не найдена (' + custom + ') — авто-подбор', 20);
  }

  const tryBundled = () => {
    const p = findBundledJava(majorDir);
    if (p) report('Java ' + major + ' — встроенная', 100);
    return p;
  };
  const trySystem = () => {
    const sys = detectSystemJava();
    if (sys && isJavaSuitable(sys.major, major, exact)) {
      report('Java ' + sys.major + ' — системная', 100);
      return sys.path;
    }
    return null;
  };

  const found = preferBundled ? (tryBundled() || trySystem()) : (trySystem() || tryBundled());
  if (found) return found;

  report('Поиск сборки Java ' + major + ' (Temurin)…', 0);
  const { arch, osName } = adoptiumTarget();
  const url = ADOPTIUM_API + '/' + major + '/hotspot?architecture=' + arch +
              '&image_type=jdk&os=' + osName + '&vendor=eclipse';
  const assets = await fetchJSON(url);
  if (!Array.isArray(assets) || !assets.length) {
    throw new Error('Не удалось найти Java ' + major + ' для вашей системы');
  }
  const pkg = assets[0].binary.package;

  await fsp.mkdir(majorDir, { recursive: true });
  const archive = path.join(majorDir, pkg.name);
  await downloadIfMissing(pkg.link, archive, pkg.size, {
    onBytes: (got, total) => {
      const size = total || pkg.size || 1;
      report('Скачивание Java ' + major + ' — ' + fmtBytes(got) + ' / ' + fmtBytes(size),
        Math.max(1, Math.min(96, Math.round((got / size) * 95))));
    },
    onRetry: (msg) => report('Java ' + major + ': ' + msg + '…', 50)
  });

  report('Распаковка Java ' + major + '…', 97);
  await tar.x({ file: archive, cwd: majorDir });
  await fsp.rm(archive, { force: true });

  const javaPath = findBundledJava(majorDir);
  if (!javaPath) throw new Error('Java распакована, но java не найдена');
  await fsp.writeFile(path.join(majorDir, '.java-path'), javaPath);
  report('Java ' + major + ' готова', 100);
  return javaPath;
}

// ============================================================
// ЗАПУСК ИГРЫ
// ============================================================
let gameProcess = null;
let gameBuildName = null;

/** Сколько нативных jar'ов нужно этой версии для текущей ОС */
function nativeJarCount(v) {
  return (v.libraries || []).filter((l) => ruleAllowed(l.rules) && nativeClassifier(l)).length;
}

/** Файлы в папке natives (без служебного маркера) */
function nativesFiles(nativesDir) {
  try {
    return fs.readdirSync(nativesDir).filter((f) => f !== '.ok');
  } catch (_) {
    return [];
  }
}

// ---------- обход особенности LWJGL 3 ----------
// LWJGL 3 не умеет загружать .so из пути с не-ASCII символами (кириллица и т. п.):
// «Failed to dynamically load library: .../libglfw.so(error = null)». LWJGL 2 грузит
// нативы через сам JVM и с таким путём работает, поэтому страдают только версии 1.13+.
// Решение: если путь сборки не-ASCII, отдаём игре ASCII-ссылку (или копию) на natives.

/** В пути только ASCII-символы? (любой не-ASCII занимает в UTF-8 больше байта) */
function isAsciiPath(p) {
  return typeof p === 'string' && Buffer.byteLength(p, 'utf8') === p.length;
}

/** На точке монтирования запрещён запуск (noexec)? Тогда .so оттуда не загрузятся */
function isNoExecMount(dir) {
  if (process.platform === 'win32' || process.platform === 'darwin') return false;
  try {
    let best = '';
    let opts = '';
    for (const line of fs.readFileSync('/proc/mounts', 'utf8').split('\n')) {
      const parts = line.split(' ');
      if (parts.length < 4) continue;
      const mp = parts[1].replace(/\\040/g, ' ');
      const inside = dir === mp || dir.startsWith(mp.endsWith('/') ? mp : mp + '/');
      if (inside && mp.length >= best.length) { best = mp; opts = parts[3]; }
    }
    return /(^|,)noexec(,|$)/.test(opts);
  } catch (_) {
    return false;
  }
}

/**
 * Путь к нативам, пригодный для LWJGL 3.
 * Если путь сборки содержит не-ASCII символы — возвращает ASCII-путь
 * (символическая ссылка, а если ссылки недоступны — копия файлов).
 */
function asciiNativesDir(nativesDir, buildName) {
  if (isAsciiPath(nativesDir)) return nativesDir;

  const tail = crypto.createHash('sha1').update(String(buildName)).digest('hex').slice(0, 8);
  const safe = (String(buildName).replace(/[^A-Za-z0-9._-]+/g, '_').replace(/^[._-]+/, '').slice(0, 48) || 'build') + '-' + tail;
  const bases = [
    path.join(os.tmpdir(), 'cmcl-natives'),
    path.join(os.homedir(), '.cmcl-natives'),
    '/tmp/cmcl-natives'
  ];

  for (const base of bases) {
    if (!base || !isAsciiPath(base) || isNoExecMount(base)) continue;
    try {
      fs.mkdirSync(base, { recursive: true });
      fs.accessSync(base, fs.constants.W_OK);
    } catch (_) {
      continue; // база недоступна — пробуем следующую
    }

    const link = path.join(base, safe);
    try { // убрать прошлое состояние (ссылку или копию)
      const st = fs.lstatSync(link);
      if (st.isSymbolicLink()) fs.unlinkSync(link);
      else fs.rmSync(link, { recursive: true, force: true });
    } catch (_) {}

    try { // 1) ссылка: путь ASCII, содержимое всегда актуально
      fs.symlinkSync(nativesDir, link, 'dir');
      return link;
    } catch (_) {}

    try { // 2) ссылки недоступны (например, Windows) — копируем файлы
      fs.mkdirSync(link, { recursive: true });
      for (const f of fs.readdirSync(nativesDir)) {
        fs.copyFileSync(path.join(nativesDir, f), path.join(link, f));
      }
      return link;
    } catch (_) {
      try { fs.rmSync(link, { recursive: true, force: true }); } catch (_) {}
    }
  }

  return nativesDir; // ничего не вышло — работаем как раньше
}

// ---------- проверки окружения для LWJGL 2 (Minecraft ≤ 1.12.2) ----------
// LWJGL 2 перечисляет видеорежимы, ЗАПУСКАЯ внешнюю утилиту `xrandr -q` и разбирая её текст
// (см. org.lwjgl.opengl.XRandR). Если утилиты нет, список экранов получается пустым, и LWJGL
// падает с «ArrayIndexOutOfBoundsException: 0» в LinuxDisplay.getAvailableDisplayModes —
// ровно так, как это выглядит у Minecraft 1.12.2. Обходим: просим LWJGL 2 использовать
// XF86VidMode (работает через JNI, без внешних программ).

/** Исполняемый файл с таким именем есть в PATH? */
function findInPath(name) {
  for (const dir of String(process.env.PATH || '').split(path.delimiter)) {
    if (!dir) continue;
    try {
      fs.accessSync(path.join(dir, name), fs.constants.X_OK);
      return path.join(dir, name);
    } catch (_) {}
  }
  return null;
}

/** Сборка на LWJGL 2? (группа «org.lwjgl.lwjgl»; у LWJGL 3 — «org.lwjgl») */
function isLwjgl2(v) {
  return (v.libraries || []).some((l) => /^org\.lwjgl\.lwjgl:/.test(l.name || ''));
}

/** Готовая команда установки xorg-xrandr для этого дистрибутива */
function xrandrInstallCommand() {
  let osr = '';
  try { osr = fs.readFileSync('/etc/os-release', 'utf8').toLowerCase(); } catch (_) {}
  const get = (k) => {
    const m = new RegExp('^' + k.toLowerCase() + '=(.*)$', 'm').exec(osr);
    return m ? m[1].replace(/"/g, '') : '';
  };
  const all = get('ID') + ' ' + get('ID_LIKE');
  if (/arch|manjaro|endeavour|garuda|cachyos|artix/.test(all)) return 'sudo pacman -S xorg-xrandr';
  if (/debian|ubuntu|mint|pop|kali|elementary|zorin/.test(all)) return 'sudo apt install xorg-xrandr';
  if (/fedora|rhel|centos|rocky|almalinux/.test(all)) return 'sudo dnf install xorg-xrandr';
  if (/opensuse|suse/.test(all)) return 'sudo zypper install xrandr';
  if (/gentoo/.test(all)) return 'sudo emerge x11-apps/xrandr';
  if (/void/.test(all)) return 'sudo xbps-install -S xrandr';
  return 'установите пакет xorg-xrandr';
}

/** Распаковка нативных библиотек (natives) в ver/<Сборка>/natives */
async function extractNatives(buildName, v) {
  const nativesDir = path.join(VER_DIR, buildName, 'natives');
  const marker = path.join(nativesDir, '.ok');
  const required = nativeJarCount(v);

  // уже распаковано и непусто (или нативы этой версии не нужны вовсе)
  if (fs.existsSync(marker) && (nativesFiles(nativesDir).length || !required)) {
    return nativesDir;
  }

  await fsp.rm(nativesDir, { recursive: true, force: true });
  await fsp.mkdir(nativesDir, { recursive: true });

  const problems = [];

  for (const lib of (v.libraries || [])) {
    if (!ruleAllowed(lib.rules)) continue;
    const cls = nativeClassifier(lib);
    if (!cls) continue;

    const rel = libPath(lib, cls);
    const jarPath = path.join(LIB_DIR, rel);
    if (!fs.existsSync(jarPath)) {
      problems.push('нет файла ' + rel.split('/').pop());
      continue;
    }

    // какие записи не распаковывать (в манифестах старых версий: META-INF/)
    const exclude = (lib.extract && Array.isArray(lib.extract.exclude)) ? lib.extract.exclude : ['META-INF/'];

    try {
      const zip = new AdmZip(jarPath);
      for (const entry of zip.getEntries()) {
        if (entry.isDirectory) continue;
        const name = entry.entryName;
        if (exclude.some((p) => name.startsWith(p))) continue;
        const out = path.join(nativesDir, name);
        if (!out.startsWith(nativesDir)) continue; // защита от выхода за папку
        await fsp.mkdir(path.dirname(out), { recursive: true });
        await fsp.writeFile(out, entry.getData());
      }
    } catch (err) {
      problems.push(rel.split('/').pop() + ' — ' + err.message);
    }
  }

  const extracted = nativesFiles(nativesDir);
  if (required && !extracted.length) {
    throw new Error('Нативные библиотеки не распаковались' +
      (problems.length ? ': ' + problems.slice(0, 2).join('; ') : '') +
      '. Удалите сборку и добавьте заново.');
  }

  await fsp.writeFile(marker, 'ok');
  return nativesDir;
}

/** Старые версии (до 1.6): индекс с map_to_resources → раскладываем объекты в <папка игры>/resources */
async function materializeResources(buildName, v) {
  const idxPath = path.join(ASSETS_DIR, 'indexes', (v.assetIndex && v.assetIndex.id || '') + '.json');
  if (!fs.existsSync(idxPath)) return { ok: false, reason: 'нет индекса ресурсов ' + (v.assetIndex && v.assetIndex.id) };

  const idx = JSON.parse(fs.readFileSync(idxPath, 'utf8'));
  if (!idx.map_to_resources) return { ok: true, skipped: true };

  const resDir = path.join(VER_DIR, buildName, 'resources');
  const marker = path.join(resDir, '.ok');
  if (fs.existsSync(marker)) return { ok: true, skipped: true };

  const objects = Object.entries(idx.objects || {});
  let copied = 0;
  const missing = [];
  for (const [name, info] of objects) {
    const src = path.join(ASSETS_DIR, 'objects', info.hash.slice(0, 2), info.hash);
    if (!fs.existsSync(src)) { missing.push(name); continue; }
    const dest = path.join(resDir, name);
    await fsp.mkdir(path.dirname(dest), { recursive: true });
    await fsp.copyFile(src, dest);
    copied++;
  }

  if (missing.length) {
    return { ok: false, reason: 'не хватает объектов: ' + missing.length + ' (например ' + missing[0] + ')' };
  }
  await fsp.writeFile(marker, 'ok');
  return { ok: true, copied };
}

/** classpath: библиотеки + клиент сборки */
function buildClasspath(v, buildDir) {
  const parts = [];
  const missing = [];

  for (const lib of (v.libraries || [])) {
    if (!ruleAllowed(lib.rules)) continue;
    const art = lib.downloads && lib.downloads.artifact;
    if (!art && nativeClassifier(lib)) continue;   // запись только с нативами — в classpath не нужна
    const rel = libPath(lib);
    const p = path.join(LIB_DIR, rel);
    if (fs.existsSync(p)) parts.push(p);
    else missing.push(rel.split('/').pop());
  }

  const jar = path.join(buildDir, 'client.jar');
  if (fs.existsSync(jar)) parts.push(jar);
  else missing.push('client.jar');

  return { classpath: parts.join(path.delimiter), missing };
}

function substitute(str, vars) {
  return String(str).replace(/\$\{([a-z_]+)\}/gi, (m, k) => (k in vars ? vars[k] : m));
}

function collectArgs(list, vars) {
  const out = [];
  for (const item of (list || [])) {
    if (typeof item === 'string') {
      out.push(substitute(item, vars));
    } else if (item && typeof item === 'object' && 'value' in item) {
      if (!ruleAllowed(item.rules)) continue;
      const vals = Array.isArray(item.value) ? item.value : [item.value];
      for (const x of vals) out.push(substitute(x, vars));
    }
  }
  return out;
}

async function launchBuild(name) {
  if (gameProcess) throw new Error('Игра уже запущена');

  const build = readBuilds().find((b) => b.name === name);
  if (!build) throw new Error('Сборка не найдена');
  if (build.status !== 'ready') throw new Error('Сборка ещё не готова');

  const accounts = readAccounts();
  let account = accounts.find((a) => a.selected) || accounts[0];
  if (!account) throw new Error('Сначала добавьте аккаунт во вкладке «Аккаунты»');

  // ELY.by: перед запуском проверяем токен (validate) и обновляем (refresh) при необходимости
  if (account.type === 'elyby' && account.accessToken && readSettings().accounts.validateOnLaunch !== false) {
    account = await ensureElybyToken(account);
  }

  // ELY.by: реальный uuid профиля — по нему игра подхватит скин (текстуры привязаны к нему)
  if (account.type === 'elyby') {
    const realUuid = await elybyProfileUuid(account.name);
    if (realUuid && realUuid !== account.uuid) {
      const all = readAccounts();
      const a = all.find((x) => x.name === account.name);
      if (a) { a.uuid = realUuid; writeAccounts(all); }
      account = Object.assign({}, account, { uuid: realUuid });
    }
  }

  const buildDir = path.join(VER_DIR, name);
  const versionFile = path.join(buildDir, 'version.json');
  if (!fs.existsSync(versionFile)) throw new Error('Файлы сборки повреждены: нет version.json');
  const v = JSON.parse(fs.readFileSync(versionFile, 'utf8'));

  const progress = (text, percent) => sendEvent('launch:progress', { build: name, text, percent });
  const state = (st, extra) => sendEvent('game:state', Object.assign({ build: name, state: st }, extra || {}));

  const log = (line) => {
    if (!line) return;
    for (const l of String(line).split(/\r?\n/)) {
      if (!l.trim()) continue;
      sendEvent('game:log', { build: name, line: l });
      if (logStream) { try { logStream.write(l + '\n'); } catch (_) {} }
    }
  };

  // лог игры в файл ver/logs/<сборка>-<время>.log (настройка «Запуск → лог в файл»)
  let logStream = null;
  try {
    if (readSettings().launch.logToFile) {
      const logsDir = path.join(VER_DIR, 'logs');
      fs.mkdirSync(logsDir, { recursive: true });
      const stamp = new Date().toISOString().replace(/[:.]/g, '-').slice(0, 19);
      logStream = fs.createWriteStream(path.join(logsDir, name + '-' + stamp + '.log'), { flags: 'a' });
      logStream.write('==== ' + new Date().toISOString() + ' — запуск ' + name + ' ====\n');
    }
  } catch (_) { logStream = null; }

  state('preparing');

  try {
    const ls = buildLaunchSettings(name, v);
    const javaPath = await ensureJava(ls.major, progress, {
      requireExact: ls.requireExact,
      preferBundled: ls.preferBundled
    });
    if (ls.major !== ls.required) {
      log('Java ' + ls.major + ' — ' + ls.source + ' (версии нужно ' + ls.required + ')');
    }
    if (ls.major < ls.required) {
      log('Внимание: выбранная Java ' + ls.major + ' старее требуемой ' + ls.required +
          ' — игра может не запуститься. Проверьте настройки Java.');
    }

    progress('Распаковка нативных библиотек…', 100);
    const nativesDir = await extractNatives(name, v);
    const nativeCount = nativesFiles(nativesDir).length;
    if (nativeJarCount(v)) log('Нативные библиотеки: ' + nativeCount + ' файлов → ' + nativesDir);

    // LWJGL 3 (1.13+) не грузит нативы из пути с не-ASCII символами — подменяем путь на ASCII
    const gameNativesDir = asciiNativesDir(nativesDir, name);
    if (gameNativesDir !== nativesDir) {
      log('Путь сборки содержит не-ASCII символы → игре нативы передаются по пути: ' + gameNativesDir);
    }

    // старые версии: ресурсы должны быть в папке игры
    if (v.assetIndex && v.assetIndex.id) {
      const res = await materializeResources(name, v);
      if (res.ok && res.copied) log('Ресурсы разложены (старая версия): ' + res.copied + ' файлов');
      else if (!res.ok) log('Внимание: ресурсы не готовы — ' + res.reason);
    }

    progress('Проверка файлов сборки…', 100);
    const cp = buildClasspath(v, buildDir);
    if (cp.missing.length) {
      throw new Error('Не хватает файлов (' + cp.missing.slice(0, 3).join(', ') +
        (cp.missing.length > 3 ? ' и др.' : '') + '). Удалите и скачайте сборку заново.');
    }

    const uuid = account.uuid || offlineUUID(account.name);
    const vars = {
      auth_player_name: account.name,
      version_name: v.id,
      game_directory: buildDir,
      assets_root: ASSETS_DIR,
      assets_index_name: v.assetIndex.id,
      auth_uuid: uuid.replace(/-/g, ''),
      auth_access_token: account.accessToken || '0',
      auth_session: '0',
      clientid: '',
      auth_xuid: '',
      user_type: account.type === 'elyby' ? 'mojang' : 'legacy',
      version_type: v.type || 'release',
      user_properties: '{}',
      natives_directory: gameNativesDir,
      launcher_name: 'CMinervaLauncher',
      launcher_version: '1.0.0',
      classpath: cp.classpath,
      classpath_separator: path.delimiter,
      library_directory: LIB_DIR
    };

    let jvmArgs;
    if (v.arguments && Array.isArray(v.arguments.jvm) && v.arguments.jvm.length) {
      // modern (1.13+): jvm-аргументы уже содержат -cp и -Djava.library.path
      jvmArgs = collectArgs(v.arguments.jvm, vars);
    } else {
      jvmArgs = ['-Djava.library.path=' + gameNativesDir, '-cp', cp.classpath];
    }

    // скины ely.by в игре: authlib-injector переводит сессию и текстуры на ely.by
    if (account.type === 'elyby') {
      try {
        const agentJar = await ensureAuthlib(progress);
        jvmArgs.unshift('-javaagent:' + agentJar + '=ely.by');
        log('Скины ely.by: подключён authlib-injector ' + AUTHLIB_VERSION + ' (сеанс и текстуры — через ely.by)');
      } catch (e) {
        log('Внимание: authlib-injector не подключён (' + e.message + ') — скин ely.by в игре не отобразится');
      }
    }

    const gameArgs = (v.arguments && Array.isArray(v.arguments.game))
      ? collectArgs(v.arguments.game, vars)
      : String(v.minecraftArguments || '').split(' ').filter(Boolean)
          .map((s) => substitute(s, vars))
          .concat(['--userProperties', '{}']);

    // LWJGL 2 (Minecraft ≤ 1.12.2) без утилиты xrandr падает при инициализации экрана.
    // Настройка «Запуск → обход LWJGL 2»: auto (только если утилиты нет) / always / never.
    const warn = readSettings().launch.lwjgl2Fallback;
    const wantFallback = warn === 'always' || (warn === 'auto' && !findInPath('xrandr'));
    if (process.platform === 'linux' && isLwjgl2(v) && wantFallback) {
      jvmArgs.unshift('-DLWJGL_DISABLE_XRANDR=true');
      if (warn === 'always') {
        log('Обход LWJGL 2 включён вручную → используется XF86VidMode');
      } else {
        log('Утилита xrandr не найдена → LWJGL 2 переключён на XF86VidMode');
        log('  Штатный путь вернётся после установки пакета: ' + xrandrInstallCommand());
      }
    }

    // порядок: пользовательские флаги → память (поля настроек считаются главными) → флаги манифеста
    const lst = readSettings().launch;
    const extraGameArgs = splitArgs(lst.extraGameArgs);
    // окно игры: размер и полный экран из настроек (0/пусто = как в игре)
    const winArgs = [];
    if (lst.fullscreen) winArgs.push('--fullscreen');
    if (lst.width > 0 && lst.height > 0) {
      winArgs.push('--width', String(lst.width), '--height', String(lst.height));
    }
    const args = [
      ...ls.jvmArgs,
      '-Xmx' + ls.memoryMax,
      '-Xms' + ls.memoryMin,
      ...jvmArgs,
      v.mainClass,
      ...winArgs,
      ...extraGameArgs,
      ...gameArgs
    ];

    log('Аккаунт: ' + account.name + (account.type === 'elyby'
      ? (account.accessToken ? ' (ely.by, вход по токену)' : ' (ely.by, только ник — токен не получен)')
      : ' (offline)'));
    log('Java: ' + javaPath);
    log('Память: -Xms' + ls.memoryMin + ' -Xmx' + ls.memoryMax + ' (' + (ls.memorySource || 'настройки') + ')');
    if (ls.jvmArgs.length) log('JVM-флаги: ' + ls.jvmArgs.join(' '));
    log('Запуск: ' + v.mainClass);

    gameBuildName = name;
    gameProcess = spawn(javaPath, args, { cwd: buildDir });
    const lsb = readSettings().launch;
    if (lsb.closeOnLaunch && mainWindow && !mainWindow.isDestroyed()) {
      setTimeout(() => { if (mainWindow && !mainWindow.isDestroyed()) mainWindow.close(); }, 700);
    } else if (lsb.minimizeOnLaunch && mainWindow && !mainWindow.isDestroyed()) {
      mainWindow.minimize();
    }

    gameProcess.stdout.on('data', (d) => log(d.toString()));
    gameProcess.stderr.on('data', (d) => log(d.toString()));
    gameProcess.on('error', (err) => {
      sendEvent('game:state', { build: name, state: 'error', message: err.message });
      gameProcess = null;
      gameBuildName = null;
      if (logStream) { try { logStream.end(); } catch (_) {} logStream = null; }
    });
    gameProcess.on('close', (code) => {
      log('Процесс завершён, код: ' + code);
      sendEvent('game:state', {
        build: name,
        state: code === 0 ? 'stopped' : 'exited',
        code
      });
      gameProcess = null;
      gameBuildName = null;
      if (logStream) { try { logStream.end(); } catch (_) {} logStream = null; }
    });

    state('running', { account: account.name, java: javaPath });
    return { ok: true };
  } catch (err) {
    state('error', { message: err.message });
    throw err;
  }
}

function stopGame() {
  if (!gameProcess) return { ok: false, error: 'Игра не запущена' };
  const proc = gameProcess;
  proc.kill('SIGTERM');
  setTimeout(() => {
    try { proc.kill('SIGKILL'); } catch (_) {}
  }, 5000);
  return { ok: true };
}

// ============================================================
// ЗАГРУЗЧИКИ: Vanilla / Fabric / Forge / NeoForge
// ============================================================

/** NeoForge для современных версий: 1.20.4 → «20.4», 1.21 → «21.0», 1.21.1 → «21.1» */
function neoforgePrefix(mc) {
  // современная схема: 26.3 -> NeoForge 26.3.x
  const modern = /^(\d{2,})\.(\d+)$/.exec(mc || '');
  if (modern) return modern[1] + '.' + modern[2];
  const m = /^1\.(\d+)(?:\.(\d+))?$/.exec(mc || '');
  if (!m) return null;
  const minor = Number(m[1]);
  const patch = Number(m[2] || 0);
  // 1.20.1 — особый случай: артефакт neoforge начинается только с 1.20.2
  if (minor === 20 && patch === 1) return null;
  // NeoForge (артефакт neoforge) существует только для 1.20.2+
  if (minor < 20) return null;
  return minor + '.' + patch;
}

/** Сортирует версии по убыванию; стабильные (без alpha/beta/rc/snapshot) — раньше пре-релизов */
function preferStableSorted(list) {
  const nums = (s) => String(s).split(/[-+]/)[0].split('.').map((x) => parseInt(x, 10) || 0);
  const isPre = (s) => /-(alpha|beta|rc|snapshot|pre|snapshot)/i.test(String(s)) ? 1 : 0;
  return list.slice().sort((a, b) => {
    const qa = isPre(a), qb = isPre(b);
    if (qa !== qb) return qa - qb;              // стабильные раньше пре-релизов
    const pa = nums(a), pb = nums(b);
    for (let i = 0; i < Math.max(pa.length, pb.length); i++) {
      const x = pa[i] || 0, y = pb[i] || 0;
      if (x !== y) return y - x;
    }
    return String(b).localeCompare(String(a));
  });
}

/** Список версий загрузчика для указанной версии Minecraft (новые/стабильные сверху) */
async function loaderVersions(loader, gameVersion) {
  if (loader === 'fabric' || loader === 'quilt') {
    const meta = loader === 'fabric' ? FABRIC_META : QUILT_META;
    const list = await fetchJSON(meta + '/versions/loader/' + gameVersion);
    if (!Array.isArray(list)) return [];
    const versions = list.map((x) => (x.loader && x.loader.version) || x.version).filter(Boolean);
    return preferStableSorted(versions);
  }
  if (loader === 'forge') {
    const xml = await fetchText(FORGE_MAVEN + '/net/minecraftforge/forge/maven-metadata.xml');
    const all = parseMavenVersions(xml);
    const versions = all.filter((v) => v.startsWith(gameVersion + '-'))
      .map((v) => v.slice(gameVersion.length + 1));
    return preferStableSorted(versions);
  }
  if (loader === 'neoforge') {
    const prefix = neoforgePrefix(gameVersion);
    if (!prefix) return [];
    const xml = await fetchText(NEOFORGE_MAVEN + '/net/neoforged/neoforge/maven-metadata.xml');
    const all = parseMavenVersions(xml);
    const versions = all.filter((v) => v === prefix || v.startsWith(prefix + '.'));
    return preferStableSorted(versions);
  }
  return [];
}

/** Сливает профиль загрузчика (inheritsFrom) с базовой версией Minecraft */
function mergeInherited(base, child) {
  const out = Object.assign({}, base);
  for (const k of Object.keys(child || {})) {
    if (k === 'libraries' || k === 'arguments' || k === 'inheritsFrom') continue;
    out[k] = child[k];
  }
  out.libraries = [].concat(base.libraries || [], (child && child.libraries) || []);
  const ba = base.arguments || {};
  const ca = (child && child.arguments) || {};
  const game = [].concat(ba.game || [], ca.game || []);
  const jvm = [].concat(ba.jvm || [], ca.jvm || []);
  out.arguments = {};
  if (game.length) out.arguments.game = game;
  if (jvm.length) out.arguments.jvm = jvm;
  if (!out.arguments.game && !out.arguments.jvm) delete out.arguments;
  delete out.inheritsFrom;
  if (!out.downloads) out.downloads = base.downloads;
  return out;
}


/**
 * Установка Forge/NeoForge: скачивает официальный установщик, распаковывает
 * version.json + install_profile.json, прогоняет processors и возвращает
 * готовый (слитый с ванилой) профиль версии.
 */
/** Запускает официальный установщик Forge/NeoForge в консольном режиме. */
function runInstallerCli(javaPath, installerPath, gameDir, buildName, label, onLine) {
  return new Promise((resolve, reject) => {
    const args = ['-Djava.awt.headless=true', '-jar', installerPath, '--installClient', gameDir];
    const proc = spawn(javaPath, args, { cwd: gameDir });
    let out = '';
    let lastLine = '';
    let settled = false;
    const onData = (chunk) => {
      out += chunk.toString();
      if (out.length > 40000) out = out.slice(-40000);
      if (cancelling.has(buildName)) { try { proc.kill('SIGKILL'); } catch (_) {} return; }
      const lines = out.split(/\r?\n/).map((s) => s.trim()).filter(Boolean);
      const cur = lines[lines.length - 1] || '';
      if (cur && cur !== lastLine) { lastLine = cur; if (onLine) onLine(label + ': ' + cur.slice(0, 110)); }
    };
    proc.stdout.on('data', onData);
    proc.stderr.on('data', onData);
    proc.on('error', (e) => { settled = true; reject(e); });
    const timer = setTimeout(() => {
      if (settled) return;
      try { proc.kill('SIGKILL'); } catch (_) {}
      settled = true;
      reject(new Error(label + ': установщик не завершился за 15 минут'));
    }, 15 * 60 * 1000);
    proc.on('close', (code) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      if (cancelling.has(buildName)) { reject(new Error('Установка отменена')); return; }
      if (code === 0) resolve(out);
      else reject(new Error(label + ': установщик завершился с кодом ' + code +
        (out ? ' — ' + out.trim().slice(-300) : '')));
    });
  });
}

/** Переносит библиотеки установщика в общий каталог лаунчера (без удаления). */
async function copyDirMerge(src, dst) {
  let entries = [];
  try { entries = await fsp.readdir(src, { withFileTypes: true }); } catch (_) { return; }
  await fsp.mkdir(dst, { recursive: true });
  for (const e of entries) {
    const s = path.join(src, e.name);
    const d = path.join(dst, e.name);
    if (e.isDirectory()) await copyDirMerge(s, d);
    else if (e.isFile()) { try { await fsp.copyFile(s, d); } catch (_) { /* пропускаем */ } }
  }
}

async function installForgeLike(name, spec, vanilla, step, javaPath) {
  const isNeo = spec.loader === 'neoforge';
  const mc = spec.version;
  const lv = spec.loaderVersion;
  const label = isNeo ? 'NeoForge' : 'Forge';
  const maven = isNeo ? NEOFORGE_MAVEN : FORGE_MAVEN;
  const grp = isNeo ? 'net/neoforged' : 'net/minecraftforge';
  const artifact = isNeo ? 'neoforge' : 'forge';
  const fullVer = isNeo ? lv : (mc + '-' + lv);
  const installerName = artifact + '-' + fullVer + '-installer.jar';
  const url = maven + '/' + grp + '/' + artifact + '/' + fullVer + '/' + installerName;

  step('downloading', 5, 'Загрузка установщика ' + label + '…');
  const installerPath = path.join(CACHE_DIR, 'installers', installerName);
  await downloadIfMissing(url, installerPath, null, {
    onBytes: (got, total) => step('downloading', 5,
      'Установщик ' + label + ' — ' + fmtBytes(got) + (total ? ' / ' + fmtBytes(total) : '')),
    onRetry: (m) => step('downloading', 5, 'Установщик ' + label + ': ' + m)
  });

  // Официальный установщик сам раскладывает патченный клиент и библиотеки,
  // поэтому запускаем его в консольном режиме (--installClient) внутри
  // временной игровой папки, а затем переносим результат в общий каталог.
  const buildDir = path.join(VER_DIR, name);
  const baseProfile = Object.assign({}, vanilla, { id: mc });
  const gameDir = path.join(CACHE_DIR, 'forge-install', fullVer);
  await fsp.rm(gameDir, { recursive: true, force: true });
  const vDir = path.join(gameDir, 'versions', mc);
  await fsp.mkdir(vDir, { recursive: true });
  await fsp.writeFile(path.join(vDir, mc + '.json'), JSON.stringify(baseProfile, null, 2));
  await fsp.copyFile(path.join(buildDir, 'client.jar'), path.join(vDir, mc + '.jar'));
  await fsp.writeFile(path.join(gameDir, 'launcher_profiles.json'),
    JSON.stringify({ profiles: {}, settings: {}, version: 3 }));

  step('downloading', 25, 'Установка ' + label + ' ' + lv + ' (это может занять минуту)…');
  await runInstallerCli(javaPath, installerPath, gameDir, name, label,
    (text) => step('downloading', 35, text));

  // готовый профиль, созданный официальным установщиком
  const versionsDir = path.join(gameDir, 'versions');
  let ids = [];
  try { ids = await fsp.readdir(versionsDir); } catch (_) {}
  const loaderId = ids.find((id) => id !== mc &&
    fs.existsSync(path.join(versionsDir, id, id + '.json')));
  if (!loaderId) throw new Error(label + ': установщик не создал профиль версии');

  // библиотеки (в т.ч. патченный клиент) — в общий каталог лаунчера
  step('downloading', 88, 'Библиотеки ' + label + '…');
  await copyDirMerge(path.join(gameDir, 'libraries'), LIB_DIR);

  const loaderJson = JSON.parse(
    await fsp.readFile(path.join(versionsDir, loaderId, loaderId + '.json'), 'utf8'));
  return mergeInherited(baseProfile, loaderJson);
}

// ============================================================
// КОНТЕНТ — поиск и установка (Modrinth + CurseForge)
// ============================================================

/** Соответствие категории UI → project_type Modrinth (миров в Modrinth нет) */
const MODRINTH_TYPE = {
  mods: 'mod',
  modpacks: 'modpack',
  resourcepacks: 'resourcepack',
  texturepacks: 'resourcepack',
  shaders: 'shader',
  worlds: null
};

// ---------- Modrinth ----------

async function modrinthSearch({ type, query, gameVersion, loader, offset }) {
  const ptype = MODRINTH_TYPE[type];
  if (!ptype) return { hits: [], total: 0 };
  const facets = [['project_type:' + ptype]];
  if (type === 'mods' || type === 'modpacks') {
    if (gameVersion) facets.push(['versions:' + gameVersion]);
    if (loader && loader !== 'vanilla') facets.push(['loaders:' + loader]);
  } else if (type === 'resourcepacks' || type === 'texturepacks' || type === 'shaders') {
    if (gameVersion) facets.push(['versions:' + gameVersion]);
  }
  const url = MODRINTH_API + '/search?query=' + encodeURIComponent(query || '') +
              '&limit=20&offset=' + (offset || 0) +
              '&facets=' + encodeURIComponent(JSON.stringify(facets));
  const res = await fetchJSON(url);
  const hits = (res.hits || []).map((h) => ({
    source: 'modrinth',
    projectId: h.project_id,
    title: h.title,
    slug: h.slug,
    description: h.description,
    icon: h.icon_url || null,
    downloads: h.downloads || 0,
    author: h.author || '',
    categories: h.categories || []
  }));
  return { hits, total: res.total_hits || 0 };
}

/** Проверки версии Modrinth под сборку (общие для выбора и списка версий) */
function mkGameOk(gameVersion) {
  return (v) => !gameVersion || (v.game_versions || []).includes(gameVersion);
}
function mkLoaderOk(type, loader) {
  return (v) => {
    if (type !== 'mods' && type !== 'modpacks') return true;
    if (!loader || loader === 'vanilla') return true;
    const ls = v.loaders || [];
    if (loader === 'neoforge') return ls.includes('neoforge');
    if (loader === 'forge') return ls.includes('forge') || ls.includes('neoforge');
    if (loader === 'quilt') return ls.includes('quilt') || ls.includes('fabric');
    return ls.includes('fabric') || ls.includes('quilt');
  };
}

/** Выбирает подходящую версию проекта Modrinth и её файл */
async function modrinthPickVersion(projectId, type, gameVersion, loader) {
  const list = await fetchJSON(MODRINTH_API + '/project/' + projectId + '/version');
  if (!Array.isArray(list) || !list.length) throw new Error('У проекта нет файлов');

  const loaderOk = mkLoaderOk(type, loader);
  const gameOk = mkGameOk(gameVersion);

  const pick = list.find((v) => gameOk(v) && loaderOk(v)) ||
               list.find((v) => gameOk(v)) ||
               list[0];
  const file = (pick.files || []).find((f) => f.primary) || (pick.files || [])[0];
  if (!file) throw new Error('У версии нет файла для скачивания');
  return { version: pick, file };
}

/** Список версий проекта Modrinth (для окна «Изменить версию») */
async function modrinthVersions(projectId, type, gameVersion, loader) {
  const list = await fetchJSON(MODRINTH_API + '/project/' + encodeURIComponent(projectId) + '/version');
  if (!Array.isArray(list)) throw new Error('У проекта нет версий');
  const loaderOk = mkLoaderOk(type, loader);
  const gameOk = mkGameOk(gameVersion);
  const out = [];
  for (const v of list) {
    const file = (v.files || []).find((f) => f.primary) || (v.files || [])[0];
    if (!file || !file.url) continue;
    out.push({
      source: 'modrinth', versionId: String(v.id),
      version: v.version_number || v.name || String(v.id),
      name: v.name || '',
      date: v.date_published || null,
      loaders: v.loaders || [], gameVersions: (v.game_versions || []).slice(0, 6),
      compatible: gameOk(v) && loaderOk(v),
      url: file.url, filename: file.filename, size: file.size || null
    });
  }
  return out;
}

/** Зависимости версии Modrinth: [{ projectId, versionId, dep }] */
async function modrinthDeps(projectId, versionId) {
  const list = await fetchJSON(MODRINTH_API + '/project/' + encodeURIComponent(projectId) + '/version');
  if (!Array.isArray(list) || !list.length) return [];
  const v = (versionId && list.find((x) => String(x.id) === String(versionId))) || list[0];
  return (v.dependencies || [])
    .filter((d) => d.project_id && d.dependency_type !== 'incompatible')
    .map((d) => ({
      projectId: String(d.project_id),
      versionId: d.version_id ? String(d.version_id) : null,
      dep: ['required', 'optional', 'embedded'].includes(d.dependency_type) ? d.dependency_type : 'other'
    }));
}

// ---------- CurseForge ----------

/** Заголовки CurseForge; ключ выдаётся на console.curseforge.com */
function cfHeaders() {
  return { 'x-api-key': curseforgeKey(), Accept: 'application/json' };
}

function cfEnsureKey() {
  if (!curseforgeKey()) {
    throw new Error('CurseForge недоступен: добавьте API-ключ в Настройках → Контент');
  }
}

async function cfJSON(pathname) {
  cfEnsureKey();
  try {
    return await fetchJSONHeaders(CURSEFORGE_API + pathname, cfHeaders(), 2);
  } catch (err) {
    const m = /HTTP (\d+)/.exec(String(err && err.message));
    if (m && m[1] === '403') throw new Error('CurseForge: ключ отклонён (403). Проверьте API-ключ в настройках');
    if (m && m[1] === '404') throw new Error('CurseForge: объект не найден');
    throw err;
  }
}

const CF_MODLOADER = { forge: 1, fabric: 4, quilt: 5, neoforge: 6 };

async function curseforgeSearch({ type, query, gameVersion, loader, offset }) {
  const classId = CURSEFORGE_CLASS[type];
  if (!classId) return { hits: [], total: 0 };
  const params = [
    'classId=' + classId,
    'searchFilter=' + encodeURIComponent(query || ''),
    'sortField=2',                     // популярность
    'sortOrder=desc',
    'index=' + (offset || 0),
    'pageSize=20'
  ];
  if (gameVersion) params.push('gameVersion=' + encodeURIComponent(gameVersion));
  if ((type === 'mods' || type === 'modpacks') && CF_MODLOADER[loader]) {
    params.push('modLoaderType=' + CF_MODLOADER[loader]);
  }
  const res = await cfJSON('/games/' + CURSEFORGE_GAME + '/mods/search?' + params.join('&'));
  const hits = (res.data || []).map((m) => ({
    source: 'curseforge',
    projectId: String(m.id),
    title: m.name,
    slug: m.slug,
    description: m.summary,
    icon: (m.logo && (m.logo.thumbnailUrl || m.logo.url)) || null,
    downloads: m.downloadCount || 0,
    author: (m.authors && m.authors[0] && m.authors[0].name) || '',
    categories: (m.categories || []).map((c) => c.name)
  }));
  const total = (res.pagination && res.pagination.totalCount) || hits.length;
  return { hits, total };
}

/** Выбирает файл CurseForge под версию игры/загрузчик */
async function curseforgePickFile(modId, type, gameVersion, loader) {
  const params = ['pageSize=50'];
  if (gameVersion) params.push('gameVersion=' + encodeURIComponent(gameVersion));
  if ((type === 'mods' || type === 'modpacks') && CF_MODLOADER[loader]) {
    params.push('modLoaderType=' + CF_MODLOADER[loader]);
  }
  const res = await cfJSON('/mods/' + encodeURIComponent(modId) + '/files?' + params.join('&'));
  let files = res.data || [];
  if (!files.length) {
    const all = await cfJSON('/mods/' + encodeURIComponent(modId) + '/files?pageSize=50');
    files = all.data || [];
  }
  const pick = files.find((f) => f.releaseType === 1) || files[0]; // 1 = release
  if (!pick) throw new Error('У проекта нет файлов');

  const url = pick.downloadUrl || cfCdnUrl(pick);
  if (!url) throw new Error('Автор запретил прямое скачивание на CurseForge — выберите другой проект');
  return {
    filename: pick.fileName, url, size: pick.fileLength || null,
    version: pick.displayName, id: pick.id, slug: pick.slug || null
  };
}

/** Резервный адрес файла CurseForge (edge CDN) */
function cfCdnUrl(file) {
  const id = Number(file && file.id);
  if (!Number.isFinite(id)) return null;
  const a = Math.floor(id / 1000);
  const b = id % 1000;
  return 'https://edge.forgecdn.net/files/' + a + '/' + b + '/' + encodeURIComponent(file.fileName);
}

/** Список файлов CurseForge-проекта (для окна «Изменить версию») */
async function curseforgeVersions(modId, type, gameVersion, loader) {
  const params = ['pageSize=50'];
  if (gameVersion) params.push('gameVersion=' + encodeURIComponent(gameVersion));
  if ((type === 'mods' || type === 'modpacks') && CF_MODLOADER[loader]) {
    params.push('modLoaderType=' + CF_MODLOADER[loader]);
  }
  let res = await cfJSON('/mods/' + encodeURIComponent(modId) + '/files?' + params.join('&'));
  let files = res.data || [];
  if (!files.length) {
    res = await cfJSON('/mods/' + encodeURIComponent(modId) + '/files?pageSize=50');
    files = res.data || [];
  }
  return files.map((f) => ({
    source: 'curseforge', versionId: String(f.id),
    version: f.displayName || String(f.id), name: f.displayName || '',
    date: f.fileDate || null,
    loaders: f.gameVersions || [], gameVersions: [],
    compatible: true,
    url: f.downloadUrl || cfCdnUrl(f), filename: f.fileName, size: f.fileLength || null
  })).filter((v) => v.url && v.filename);
}

// типы связей CurseForge → наши метки
const CF_RELATION = { 1: 'embedded', 2: 'required', 3: 'optional', 4: 'tool', 6: 'incompatible' };

/** Зависимости файла (или проекта) CurseForge */
async function curseforgeDeps(modId, fileId) {
  const f = fileId
    ? (await cfJSON('/mods/' + encodeURIComponent(modId) + '/files/' + encodeURIComponent(fileId))).data
    : (await cfJSON('/mods/' + encodeURIComponent(modId))).data;
  const rel = (f && f.dependencies) || [];
  return rel
    .filter((d) => d.modId && CF_RELATION[d.relationType] !== 'incompatible')
    .map((d) => ({
      projectId: String(d.modId), versionId: null,
      dep: CF_RELATION[d.relationType] || 'other'
    }));
}

// ---------- общий слой ----------

async function contentSearch(opts) {
  const source = opts.source === 'curseforge' ? 'curseforge' : (opts.source === 'modrinth' ? 'modrinth' : defaultContentSource());
  if (source === 'curseforge') return curseforgeSearch(opts);
  return modrinthSearch(opts);
}

/** Возвращает { url, filename, size, ... } — готовый к скачиванию файл выбранного проекта */
async function contentResolve({ source, projectId, type, gameVersion, loader }) {
  if (source === 'curseforge') {
    const f = await curseforgePickFile(projectId, type, gameVersion, loader);
    return {
      source: 'curseforge', url: f.url, filename: f.filename, size: f.size,
      title: f.version, version: f.version, versionId: f.id != null ? String(f.id) : null,
      projectId: String(projectId), slug: f.slug || null
    };
  }
  const picked = await modrinthPickVersion(projectId, type, gameVersion, loader);
  return {
    source: 'modrinth', url: picked.file.url, filename: picked.file.filename, size: picked.file.size,
    title: picked.version.name, version: picked.version.version_number || picked.version.name,
    versionId: picked.version.id, projectId: picked.version.project_id || String(projectId),
    slug: picked.version.slug || null
  };
}

/** Скачивает файл контента в нужную папку сборки */
async function contentInstallFile(build, type, file) {
  const dirName = CONTENT_DIR[type] || 'mods';
  const dest = path.join(VER_DIR, build, dirName, path.basename(file.filename));
  await downloadIfMissing(file.url, dest, file.size, { attempts: 4 });
  return dest;
}

/** Список версий проекта у выбранного источника (для смены версии) */
async function contentVersions({ source, projectId, type, gameVersion, loader }) {
  if (source === 'curseforge') return curseforgeVersions(projectId, type, gameVersion, loader);
  return modrinthVersions(projectId, type, gameVersion, loader);
}

/** Зависимости установленной версии проекта */
async function contentDeps({ source, projectId, type, versionId }) {
  if (source === 'curseforge') return curseforgeDeps(projectId, versionId);
  return modrinthDeps(projectId, versionId);
}

/** Краткая информация о проекте (название, иконка) */
async function contentProjectInfo(projectId, source) {
  if (source === 'curseforge') {
    const res = await cfJSON('/mods/' + encodeURIComponent(projectId));
    const m = res.data || {};
    return { title: m.name || null, icon: (m.logo && (m.logo.thumbnailUrl || m.logo.url)) || null };
  }
  const p = await fetchJSON(MODRINTH_API + '/project/' + encodeURIComponent(projectId));
  return { title: p.title || null, icon: p.icon_url || null };
}

// ============================================================
// УСТАНОВКА (СКАЧИВАНИЕ) СБОРКИ
// ============================================================
// сборки, которые пользователь попросил отменить (удаляются на лету)
const cancelling = new Set();

function throwIfCancelled(name) {
  if (cancelling.has(name)) {
    cancelling.delete(name);
    throw new Error('Загрузка отменена');
  }
}

/**
 * Временная (сетевая) ошибка — имеет смысл повторять автоматически.
 * Постоянные ошибки («версия не найдена», «отменена» и т.п.) не ретраим.
 */
function isRetryableInstallError(err) {
  const msg = String((err && err.message) || err || '');
  if (/отменена|не найдена в манифесте|уже существует|нет места|ENOSPC/i.test(msg)) return false;
  return /(таймаут|не отвечает|прерван|закрыто|данные не поступают|соединение|HTTP [0-9]|ECONN|EPIPE|ENOTFOUND|ETIMEDOUT|EAI_AGAIN|размер не совпал|Не удалось скачать|Unexpected end|JSON|нативные библиотеки)/i.test(msg);
}

/**
 * Обёртка над установкой: как только install завершился (успех, ошибка или
 * отмена), фоновые воркеры больше не могут писать статус сборки. Иначе
 * поздний прогресс-вызов перетирает итоговый 'error' обратно в 'downloading'
 * и сборка навсегда застывает на 96% («зомби»-загрузка без сети и без ошибки).
 */
async function installBuild(name, spec) {
  const install = { finished: false };
  try {
    return await runInstall(name, spec, install);
  } finally {
    install.finished = true;
  }
}

async function runInstall(name, spec, install) {
  const buildDir = path.join(VER_DIR, name);
  const step = (status, percent, text) => {
    if (install.finished) return;          // установка уже завершена — фону молчать
    if (cancelling.has(name)) return;      // отменённую сборку больше не трогаем
    updateBuild(name, { status, percent, text });
    sendEvent('builds:progress', { build: name, status, percent, text });
  };

  const loader = LOADERS.includes(spec.loader) ? spec.loader : 'vanilla';
  const versionId = spec.version;

  // 1. описание версии Minecraft (база для любого загрузчика)
  step('downloading', 2, 'Загрузка описания версии…');
  const manifest = await getManifest();
  const entry = manifest.versions.find((x) => x.id === versionId);
  if (!entry) throw new Error('Версия не найдена в манифесте: ' + versionId);

  const vanilla = await fetchJSON(entry.url);
  await fsp.mkdir(buildDir, { recursive: true });
  await fsp.mkdir(VERSIONS_DIR, { recursive: true });

  // 2. клиент (jar) — ванильный jar нужен и как основа для Forge/NeoForge
  const sharedJar = path.join(VERSIONS_DIR, vanilla.id, vanilla.id + '.jar');
  const jarInfo = vanilla.downloads && vanilla.downloads.client;
  step('downloading', 4, 'Скачивание клиента (jar)…');

  await downloadIfMissing(jarInfo.url, sharedJar, jarInfo.size, {
    onBytes: (got, total) => {
      const pct = 4 + Math.round((got / (total || jarInfo.size || 1)) * 12);
      step('downloading', Math.min(pct, 16),
        'Клиент (jar) — ' + fmtBytes(got) + (total ? ' / ' + fmtBytes(total) : ''));
    },
    onRetry: (msg) => step('downloading', 4, 'Клиент (jar): ' + msg)
  });
  await fsp.copyFile(sharedJar, path.join(buildDir, 'client.jar'));
  step('downloading', 16, 'Клиент (jar) загружен');

  // 3. профиль версии с учётом загрузчика
  let v;
  if (loader === 'fabric' || loader === 'quilt') {
    if (!spec.loaderVersion) throw new Error('Не выбрана версия ' + LOADER_LABELS[loader]);
    const label = LOADER_LABELS[loader];
    step('downloading', 17, 'Профиль ' + label + ' ' + spec.loaderVersion + '…');
    const meta = loader === 'fabric' ? FABRIC_META : QUILT_META;
    const profile = await fetchJSON(meta + '/versions/loader/' + versionId + '/' +
      spec.loaderVersion + '/profile/json');
    v = mergeInherited(vanilla, profile);
  } else if (loader === 'forge' || loader === 'neoforge') {
    if (!spec.loaderVersion) throw new Error('Не выбрана версия загрузчика');
    const major = (vanilla.javaVersion && vanilla.javaVersion.majorVersion) || 8;
    const javaPath = await ensureJava(major, (t, p) => step('downloading', p, t), { preferBundled: true });
    v = await installForgeLike(name, Object.assign({}, spec, { loader }), vanilla, step, javaPath);
  } else {
    v = vanilla;
  }

  const sharedVerJson = path.join(VERSIONS_DIR, v.id, v.id + '.json');
  await fsp.mkdir(path.dirname(sharedVerJson), { recursive: true });
  await fsp.writeFile(sharedVerJson, JSON.stringify(v, null, 2));
  await fsp.writeFile(path.join(buildDir, 'version.json'), JSON.stringify(v, null, 2));

  // 3. библиотеки
  const libs = (v.libraries || []).filter((l) => ruleAllowed(l.rules));
  let libDone = 0;
  const libProblems = [];
  for (const lib of libs) {
    throwIfCancelled(name);
    try {
      const failed = await downloadLibrary(lib);
      if (failed && failed.length) libProblems.push(...failed);
    } catch (err) {
      libProblems.push(lib.name + ' — ' + err.message);
    }
    libDone++;
    step('downloading', 20 + Math.round((libDone / Math.max(libs.length, 1)) * 22),
      'Библиотеки ' + libDone + '/' + libs.length +
      (libProblems.length ? ' (проблем: ' + libProblems.length + ')' : ''));
  }

  // нативные библиотеки обязательны для запуска — без них игра упадёт
  if (libProblems.length) {
    await fsp.writeFile(path.join(buildDir, 'install-log.txt'),
      libProblems.join('\n') + '\n', 'utf8').catch(() => {});
  }
  const missingNatives = nativeJarsMissing(v);
  if (missingNatives.length) {
    throw new Error('Не скачались нативные библиотеки (' + missingNatives.slice(0, 3).join(', ') +
      (missingNatives.length > 3 ? ' и др.' : '') + '). Подробности: ver/' + name + '/install-log.txt');
  }

  // 4. ресурсы (assets)
  step('downloading', 42, 'Загрузка индекса ресурсов…');
  const assetIndex = await fetchJSON(v.assetIndex.url);
  const idxDir = path.join(ASSETS_DIR, 'indexes');
  await fsp.mkdir(idxDir, { recursive: true });
  await fsp.writeFile(path.join(idxDir, v.assetIndex.id + '.json'), JSON.stringify(assetIndex));

  const objects = Object.values(assetIndex.objects || {});
  const totalAssets = objects.length;
  let assetsDone = 0;
  let lastSend = 0;
  let aborted = false;                      // если один поток не смог — останавливаем остальные
  const queue = objects.map((o) => ({ hash: o.hash, size: o.size }));

  const worker = async () => {
    while (queue.length && !aborted) {
      throwIfCancelled(name);
      const it = queue.shift();
      const rel = it.hash.slice(0, 2);
      const dest = path.join(ASSETS_DIR, 'objects', rel, it.hash);
      const url = resourcesBase() + '/' + rel + '/' + it.hash;
      const basePct = 42 + Math.round((assetsDone / Math.max(totalAssets, 1)) * 50);

      try {
        await downloadIfMissing(url, dest, it.size, {
          attempts: Math.max(4, maxAttempts()),
          onRetry: (msg) => step('downloading', basePct,
            'Ресурсы ' + (assetsDone + 1) + '/' + totalAssets + ' — ' + msg)
        });
      } catch (err) {
        if (!aborted) {
          aborted = true;
          throw new Error('Не удалось скачать ресурс ' + it.hash + ': ' + err.message);
        }
        return;
      }

      if (aborted) return;                 // проход уже прерван — статус больше не трогаем
      assetsDone++;
      const now = Date.now();
      if (now - lastSend > 120 || assetsDone === totalAssets) {
        lastSend = now;
        step('downloading',
          42 + Math.round((assetsDone / Math.max(totalAssets, 1)) * 50),
          'Ресурсы ' + assetsDone + '/' + totalAssets);
      }
    }
  };
  await Promise.all(Array.from({ length: downloadConcurrency() }, worker));

  // 4b. старые версии (до 1.6): ресурсы раскладываем в папку игры
  if (assetIndex.map_to_resources) {
    step('downloading', 97, 'Раскладка ресурсов старой версии…');
    try {
      const res = await materializeResources(name, v);
      if (!res.ok) {
        await fsp.writeFile(path.join(buildDir, 'install-log.txt'),
          'resources: ' + res.reason + '\n', { encoding: 'utf8', flag: 'a' }).catch(() => {});
      }
    } catch (_) { /* не критично для запуска */ }
  }

  // 5. конфиг логирования
  if (v.logging && v.logging.client && v.logging.client.configuration) {
    const conf = v.logging.client.configuration;
    try {
      const dest = path.join(ASSETS_DIR, 'log_configs', path.basename((conf.file && conf.file.id) || 'client.xml'));
      await downloadIfMissing(conf.url, dest, conf.file && conf.file.size);
    } catch (_) { /* не критично */ }
  }

  // 6. метаданные сборки
  step('downloading', 99, 'Сохранение сборки…');
  const info = {
    name,
    version: versionId,
    loader,
    loaderVersion: spec.loaderVersion || null,
    type: entry.type,
    created: new Date().toISOString(),
    assetIndex: v.assetIndex.id,
    mainClass: v.mainClass,
    java: (v.javaVersion && v.javaVersion.majorVersion) || 8,
    jar: 'client.jar'
  };
  await fsp.writeFile(path.join(buildDir, 'instance.json'), JSON.stringify(info, null, 2));

  // игровые подпапки для модов/ресурсов
  for (const dir of ['mods', 'resourcepacks', 'shaderpacks', 'saves']) {
    await fsp.mkdir(path.join(buildDir, dir), { recursive: true }).catch(() => {});
  }

  step('ready', 100, 'Готово');
}

// сериализация тяжёлых операций (по одной за раз)
let taskChain = Promise.resolve();
function serial(fn) {
  const run = taskChain.then(fn, fn);
  taskChain = run.then(() => {}, () => {});
  return run;
}

// ============================================================
// IPC: ВЕРСИИ И СБОРКИ
// ============================================================
ipcMain.handle('versions:list', async () => {
  try {
    const m = await getManifest();
    const versions = m.versions
      .map((v) => ({ id: v.id, type: v.type, releaseTime: v.releaseTime }))
      .sort((a, b) => new Date(b.releaseTime) - new Date(a.releaseTime));
    return { ok: true, versions };
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

ipcMain.handle('builds:list', () => {
  try {
    let builds = readBuilds()
      .slice()
      .sort((a, b) => new Date(b.created || 0) - new Date(a.created || 0));

    // актуализируем статус: помечаем сборки, у которых нет файлов
    let changed = false;
    for (const b of builds) {
      const ready = fs.existsSync(path.join(VER_DIR, b.name, 'client.jar'));
      if (b.status === 'ready' && !ready) {
        b.status = 'error';
        b.text = 'файлы сборки не найдены';
        changed = true;
      }
    }
    if (changed) writeBuilds(readBuilds().map((x) => {
      const upd = builds.find((y) => y.name === x.name);
      return upd ? Object.assign(x, { status: upd.status, text: upd.text }) : x;
    }));

    return { ok: true, builds };
  } catch (err) {
    return { ok: false, error: err.message, builds: [] };
  }
});

/** Общая логика создания сборки: валидация, запись в реестр, установка с автоповторами */
async function createBuild(spec) {
  const name = cleanName(spec && spec.name);
  const version = String((spec && spec.version) || '').trim();
  if (!version) throw new Error('Выберите версию Minecraft');
  const loader = LOADERS.includes(spec && spec.loader) ? spec.loader : 'vanilla';
  let loaderVersion = (spec && spec.loaderVersion) ? String(spec.loaderVersion).trim() : '';
  if (loader !== 'vanilla' && !loaderVersion) {
    const list = await loaderVersions(loader, version);
    if (list && list.length) loaderVersion = list[0];
    else throw new Error('Для версии ' + version + ' нет загрузчика ' + loader);
  }

  const builds = readBuilds();
  const existing = builds.find((b) => b.name.toLowerCase() === name.toLowerCase());

  if (existing) {
    // повтор/продолжение прерванной сборки (файлы уже скачаны — повторно не качаются)
    if (existing.status === 'downloading' || existing.status === 'queued') {
      throw new Error('Эта сборка уже скачивается');
    }
    if (existing.version !== version) {
      throw new Error('Сборка «' + existing.name + '» уже существует с версией ' + existing.version);
    }
    if ((existing.loader || 'vanilla') !== loader) {
      throw new Error('Сборка «' + existing.name + '» уже существует с загрузчиком ' + (existing.loader || 'vanilla'));
    }
    loaderVersion = existing.loaderVersion || loaderVersion;
    existing.status = 'queued';
    existing.percent = 0;
    existing.text = 'Продолжение загрузки…';
    existing.loader = loader;
    existing.loaderVersion = loaderVersion;
  } else {
    builds.push({
      name,
      version,
      loader,
      loaderVersion,
      status: 'queued',
      percent: 0,
      text: 'В очереди…',
      created: new Date().toISOString()
    });
  }
  writeBuilds(builds);

  const installSpec = { version, loader, loaderVersion };
  const MAX_PASSES = 3;
  let lastErr = null;

  for (let pass = 1; pass <= MAX_PASSES; pass++) {
    try {
      await installBuild(name, installSpec);
      lastErr = null;
      break;
    } catch (err) {
      lastErr = err;
      if (cancelling.has(name)) break;                            // пользователь отменил
      if (!readBuilds().some((b) => b.name === name)) break;      // удалили во время загрузки

      if (pass < MAX_PASSES && isRetryableInstallError(err)) {
        const wait = pass === 1 ? 4000 : 12000;
        const shortMsg = err.message.length > 90 ? err.message.slice(0, 90) + '…' : err.message;
        const msg = 'Сбой: ' + shortMsg + ' — автоповтор ' + pass + '/' + (MAX_PASSES - 1) +
                    ' через ' + (wait / 1000) + ' с';
        updateBuild(name, { status: 'downloading', percent: 0, text: msg });
        sendEvent('builds:progress', { build: name, status: 'downloading', percent: 0, text: msg });
        await sleep(wait);
      } else {
        break;
      }
    }
  }

  if (lastErr) {
    if (cancelling.has(name)) cancelling.delete(name);
    if (!readBuilds().some((b) => b.name === name)) return { ok: false, error: 'Загрузка отменена' };
    updateBuild(name, { status: 'error', percent: 0, text: lastErr.message });
    sendEvent('builds:progress', { build: name, status: 'error', percent: 0, text: lastErr.message });
    return { ok: false, error: lastErr.message };
  }
  return { ok: true, name };
}

ipcMain.handle('builds:add', (_e, payload) => serial(async () => {
  try {
    return await createBuild(payload || {});
  } catch (err) {
    return { ok: false, error: err.message };
  }
}));

// ============================================================
// IPC: ЗАГРУЗЧИКИ (список версий Fabric / Forge / NeoForge)
// ============================================================
ipcMain.handle('loaders:versions', async (_e, payload) => {
  try {
    const loader = String((payload && payload.loader) || 'vanilla');
    const version = String((payload && payload.version) || '').trim();
    if (loader === 'vanilla') return { ok: true, versions: [] };
    if (!version) return { ok: false, error: 'Не выбрана версия Minecraft', versions: [] };
    const versions = await loaderVersions(loader, version);
    return { ok: true, versions };
  } catch (err) {
    return { ok: false, error: err.message, versions: [] };
  }
});

// ============================================================
// IPC: РЕДАКТИРОВАНИЕ СБОРКИ (переименование)
// ============================================================
ipcMain.handle('builds:rename', (_e, payload) => serial(async () => {
  try {
    const oldName = cleanName(payload && payload.oldName);
    const newName = cleanName(payload && payload.newName);
    if (oldName === newName) return { ok: true, name: newName };

    if (gameBuildName === oldName) throw new Error('Эта сборка сейчас запущена');
    const builds = readBuilds();
    const b = builds.find((x) => x.name === oldName);
    if (!b) throw new Error('Сборка не найдена');
    if (builds.some((x) => x.name.toLowerCase() === newName.toLowerCase())) {
      throw new Error('Сборка с таким названием уже существует');
    }

    await fsp.rename(path.join(VER_DIR, oldName), path.join(VER_DIR, newName));

    b.name = newName;
    writeBuilds(builds);

    // имя в instance.json
    try {
      const inst = JSON.parse(await fsp.readFile(path.join(VER_DIR, newName, 'instance.json'), 'utf8'));
      inst.name = newName;
      await fsp.writeFile(path.join(VER_DIR, newName, 'instance.json'), JSON.stringify(inst, null, 2));
    } catch (_) {}

    // переносим переопределения настроек
    try {
      const s = readSettings();
      if (s.perBuild && s.perBuild[oldName]) {
        const next = JSON.parse(JSON.stringify(s));
        next.perBuild[newName] = next.perBuild[oldName];
        delete next.perBuild[oldName];
        writeSettings(next);
      }
    } catch (_) {}

    return { ok: true, name: newName };
  } catch (err) {
    return { ok: false, error: err.message };
  }
}));

ipcMain.handle('builds:delete', async (_e, name) => {
  try {
    const builds = readBuilds();
    const b = builds.find((x) => x.name === name);
    if (!b) return { ok: false, error: 'Сборка не найдена' };
    if (gameBuildName === name) return { ok: false, error: 'Эта сборка сейчас запущена' };

    // если идёт скачивание — просим его остановиться и удаляем сразу
    if (b.status === 'downloading' || b.status === 'queued') {
      cancelling.add(name);
      writeBuilds(builds.filter((x) => x.name !== name));
      sendEvent('builds:progress', { build: name, status: 'deleted', percent: 0, text: 'Загрузка отменена' });
    }

    await fsp.rm(path.join(VER_DIR, name), { recursive: true, force: true });
    if (!(b.status === 'downloading' || b.status === 'queued')) {
      writeBuilds(readBuilds().filter((x) => x.name !== name));
    }

    // подчищаем настройки, привязанные к этой сборке
    try {
      const s = readSettings();
      if (s.perBuild && s.perBuild[name]) {
        const next = JSON.parse(JSON.stringify(s));
        delete next.perBuild[name];
        writeSettings(next);
      }
    } catch (_) { /* не критично */ }

    // подчищаем недокачанные .part для этой сборки
    return { ok: true };
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

// ============================================================
// IPC: АККАУНТЫ
// ============================================================
ipcMain.handle('accounts:list', () => {
  try {
    const accounts = readAccounts();
    return { ok: true, accounts };
  } catch (err) {
    return { ok: false, error: err.message, accounts: [] };
  }
});

ipcMain.handle('accounts:add', async (_e, payload) => {
  try {
    const name = cleanNick(payload && payload.name);
    // offline — классический профиль без пароля; elyby — аккаунт ely.by:
    //  - с паролем → реальный вход через authserver.ely.by (токен + uuid профиля);
    //  - без пароля → только ник (для скина и т.п. позже).
    const type = (payload && payload.type === 'elyby') ? 'elyby' : 'offline';
    const password = (payload && typeof payload.password === 'string') ? payload.password : '';
    const accounts = readAccounts();
    if (accounts.some((a) => a.name.toLowerCase() === name.toLowerCase())) {
      throw new Error('Такой аккаунт уже добавлен');
    }

    const rec = {
      name,
      type,
      uuid: offlineUUID(name),
      selected: accounts.length === 0,
      created: new Date().toISOString()
    };

    if (type === 'elyby' && password) {
      let auth;
      try {
        auth = await elybyAuthenticate(name, password);
      } catch (err) {
        if (err.needOtp) return { ok: false, needOtp: true, error: err.message };
        throw err;
      }
      rec.name = auth.profileName || name;
      rec.uuid = auth.uuid;
      rec.accessToken = auth.accessToken;
      rec.clientToken = auth.clientToken;
      rec.authed = true;
      if (accounts.some((a) => a.name.toLowerCase() === rec.name.toLowerCase())) {
        throw new Error('Такой аккаунт уже добавлен');
      }
      // сразу подтягиваем текущий скин с ely.by (не блокирует добавление)
      try {
        const sk = await elySkinForNick(rec.name, rec.name);
        if (sk) rec.skin = sk.skin;
      } catch (_) {}
    } else if (type === 'elyby') {
      // ник без пароля: всё равно берём реальный uuid профиля ely.by (по нему
      // игра найдёт скин) и пробуем сразу забрать текущий скин
      const realUuid = await elybyProfileUuid(name);
      if (realUuid) rec.uuid = realUuid;
      try {
        const sk = await elySkinForNick(name, name);
        if (sk) rec.skin = sk.skin;
      } catch (_) {}
    }

    accounts.push(rec);
    writeAccounts(accounts);
    return { ok: true };
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

ipcMain.handle('accounts:select', async (_e, name) => {
  try {
    const accounts = readAccounts();
    if (!accounts.some((a) => a.name === name)) return { ok: false, error: 'Аккаунт не найден' };
    writeAccounts(accounts.map((a) => Object.assign(a, { selected: a.name === name })));
    return { ok: true };
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

// Повторный (или первый) вход в ELY.by для уже добавленного аккаунта — по паролю.
// 2FA: пароль "пароль:код" или повторный запрос кода (needOtp).
ipcMain.handle('accounts:elybyLogin', async (_e, payload) => {
  try {
    const name = String(payload && payload.name || '');
    const password = String(payload && payload.password || '');
    if (!password) return { ok: false, error: 'Введите пароль' };

    const accounts = readAccounts();
    const acc = accounts.find((a) => a.name === name && a.type === 'elyby');
    if (!acc) return { ok: false, error: 'ELY.by-аккаунт не найден' };

    let auth;
    try {
      auth = await elybyAuthenticate(acc.login || acc.name, password);
    } catch (err) {
      if (err.needOtp) return { ok: false, needOtp: true, error: err.message };
      throw err;
    }
    acc.accessToken = auth.accessToken;
    acc.clientToken = auth.clientToken;
    acc.uuid = auth.uuid;
    acc.authed = true;
    writeAccounts(accounts);
    // свежий скин с ely.by — вместе с входом
    await attachElySkin(accounts, acc);
    return { ok: true, skin: acc.skin || null };
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

// ============================================================
// IPC: СКИНЫ
// ============================================================
// Список для вкладки «Скины»: ver/skins + папка «skins» рядом с лаунчером, привязка к аккаунтам
ipcMain.handle('skins:list', () => {
  try {
    const accounts = readAccounts();
    const seen = new Map();   // имя файла (lower) → каноническое имя
    for (const d of skinDirs()) {
      let fl = [];
      try { fl = fs.readdirSync(d); } catch (_) { continue; }
      for (const f of fl) {
        if (/\.png$/i.test(f) && !/-cape\.png$/i.test(f) && !seen.has(f.toLowerCase())) {
          seen.set(f.toLowerCase(), f);
        }
      }
    }
    const files = [...seen.values()].sort();
    const byFile = {};
    for (const a of accounts) if (a.skin && a.skin.file) byFile[String(a.skin.file).toLowerCase()] = a;
    return {
      ok: true,
      dirs: skinDirs(),
      files: files.map((f) => {
        const a = byFile[f.toLowerCase()];
        return {
          file: f,
          model: (a && a.skin.model) === 'slim' ? 'slim' : 'wide',
          capeFile: (a && a.skin.capeFile) || null,
          owner: (a && a.name) || null
        };
      }),
      accounts: accounts.map((a) => ({
        name: a.name, type: a.type, selected: !!a.selected, skin: a.skin || null
      }))
    };
  } catch (err) {
    return { ok: false, error: err.message, files: [], accounts: [] };
  }
});

// Данные скина (dataUrl) — для отрисовки в 3D-просмотрщике
ipcMain.handle('skins:data', (_e, fileName) => {
  try {
    const url = skinDataUrl(fileName);
    if (!url) return { ok: false, error: 'Файл скина не найден' };
    return { ok: true, dataUrl: url };
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

// Взять текущий скин с ely.by по нику (привязывается к аккаунту с таким ником, если есть)
ipcMain.handle('skins:fetchEly', async (_e, payload) => {
  try {
    const nick = cleanNick(payload && payload.nick);
    const r = await elySkinForNick(nick, nick);
    if (!r) {
      return { ok: false, error: 'На ely.by у «' + nick + '» нет своего скина. ' +
        'Проверьте ник или добавьте скин файлом (кнопка «+ Файлы»).' };
    }
    const accounts = readAccounts();
    const acc = accounts.find((a) => a.name.toLowerCase() === nick.toLowerCase());
    if (acc) { acc.skin = r.skin; writeAccounts(accounts); }
    return { ok: true, skin: r.skin, dataUrl: r.dataUrl, account: acc ? acc.name : null };
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

// Обновить скины всех ELY.by-аккаунтов одним нажатием
ipcMain.handle('skins:refreshAll', async () => {
  const accounts = readAccounts();
  const elys = accounts.filter((a) => a.type === 'elyby');
  let updated = 0;
  const errors = [];
  for (const acc of elys) {
    try {
      const r = await attachElySkin(accounts, acc);
      if (r) updated++;
    } catch (err) { errors.push(acc.name + ': ' + err.message); }
  }
  return { ok: true, updated, total: elys.length, errors };
});

// Выбрать скин для активного аккаунта (1 клик)
ipcMain.handle('skins:select', (_e, payload) => {
  try {
    const file = path.basename(String(payload && payload.file || ''));
    if (!findSkinFile(file)) return { ok: false, error: 'Файл скина не найден' };
    const accounts = readAccounts();
    const acc = accounts.find((a) => a.selected) || accounts[0];
    if (!acc) return { ok: false, error: 'Сначала добавьте аккаунт' };
    const capeFile = payload.capeFile ? path.basename(String(payload.capeFile)) : null;
    acc.skin = {
      file,
      model: payload.model === 'slim' ? 'slim' : 'wide',
      capeFile: (capeFile && findSkinFile(capeFile)) ? capeFile : null,
      updated: new Date().toISOString()
    };
    writeAccounts(accounts);
    return { ok: true, account: acc.name };
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

// Текущий скин активного аккаунта (для просмотра/будущего использования)
ipcMain.handle('skins:current', () => {
  try {
    const accounts = readAccounts();
    const acc = accounts.find((a) => a.selected) || accounts[0];
    if (!acc || !acc.skin || !acc.skin.file) return { ok: true, skin: null, account: acc ? acc.name : null };
    const dataUrl = skinDataUrl(acc.skin.file);
    if (!dataUrl) return { ok: true, skin: null, account: acc.name };
    const capeUrl = acc.skin.capeFile ? skinDataUrl(acc.skin.capeFile) : null;
    return {
      ok: true,
      account: acc.name,
      skin: {
        file: acc.skin.file,
        model: acc.skin.model === 'slim' ? 'slim' : 'wide',
        capeFile: (capeUrl && acc.skin.capeFile) || null,
        dataUrl,
        capeDataUrl: capeUrl
      }
    };
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

// Открыть папку скинов лаунчера (создаёт ver/skins при необходимости)
ipcMain.handle('skins:openFolder', async () => {
  try {
    fs.mkdirSync(SKINS_DIR, { recursive: true });
    const err = await shell.openPath(SKINS_DIR);
    return err ? { ok: false, error: err } : { ok: true, dir: SKINS_DIR };
  } catch (e) {
    return { ok: false, error: e.message };
  }
});

// Добавить PNG-файлы скинов из любой папки (копируются в ver/skins)
ipcMain.handle('skins:addFiles', async () => {
  try {
    const r = await dialog.showOpenDialog({
      title: 'Выберите PNG-файлы скинов',
      filters: [{ name: 'Скины PNG', extensions: ['png'] }],
      properties: ['openFile', 'multiSelections']
    });
    if (r.canceled || !r.filePaths.length) return { ok: true, added: 0 };
    fs.mkdirSync(SKINS_DIR, { recursive: true });
    let added = 0;
    for (const p of r.filePaths) {
      const base = path.basename(p);
      if (!/\.png$/i.test(base)) continue;
      let dest = path.join(SKINS_DIR, base);
      let n = 1;
      while (fs.existsSync(dest)) {
        dest = path.join(SKINS_DIR, base.replace(/\.png$/i, '') + '-' + (n++) + '.png');
      }
      fs.copyFileSync(p, dest);
      added++;
    }
    return { ok: true, added };
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

ipcMain.handle('accounts:delete', async (_e, name) => {
  try {
    const accounts = readAccounts();
    if (!accounts.some((a) => a.name === name)) return { ok: false, error: 'Аккаунт не найден' };
    let rest = accounts.filter((a) => a.name !== name);
    if (rest.length && !rest.some((a) => a.selected)) rest[0].selected = true;
    writeAccounts(rest);
    return { ok: true };
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

// ============================================================
// IPC: НАСТРОЙКИ
// ============================================================
ipcMain.handle('settings:get', () => {
  try {
    return { ok: true, settings: readSettings(), javaMajors: JAVA_MAJORS, defaults: DEFAULT_SETTINGS };
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

ipcMain.handle('settings:save', (_e, payload) => {
  try {
    const clean = writeSettings(payload);
    // масштаб интерфейса применяется сразу, без перезапуска
    if (mainWindow && !mainWindow.isDestroyed()) {
      try { mainWindow.webContents.setZoomFactor(clean.ui.scale); } catch (_) {}
    }
    return { ok: true, settings: clean };
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

ipcMain.handle('settings:reset', () => {
  try {
    const clean = writeSettings(DEFAULT_SETTINGS);
    if (mainWindow && !mainWindow.isDestroyed()) {
      try { mainWindow.webContents.setZoomFactor(clean.ui.scale); } catch (_) {}
    }
    return { ok: true, settings: clean };
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

/** Выбрать файл Java (java/javaw) через системный диалог */
ipcMain.handle('settings:pickJava', async () => {
  const opts = {
    title: 'Выберите файл java',
    properties: ['openFile'],
    filters: process.platform === 'win32'
      ? [{ name: 'Java', extensions: ['exe'] }, { name: 'Все файлы', extensions: ['*'] }]
      : [{ name: 'Все файлы', extensions: ['*'] }]
  };
  const r = await dialog.showOpenDialog(mainWindow, opts);
  return (r.canceled || !r.filePaths[0]) ? null : r.filePaths[0];
});

/** Открыть служебную папку лаунчера в проводнике */ipcMain.handle('settings:openFolder', (_e, which) => {
  const map = { root: ROOT, ver: VER_DIR, serv: SERV_DIR, logs: path.join(VER_DIR, 'logs'),
    skins: SKINS_DIR, java: JAVA_DIR };
  const dir = map[which];
  if (!dir) return { ok: false, error: 'Неизвестная папка' };
  try {
    fs.mkdirSync(dir, { recursive: true });
    shell.openPath(dir);
    return { ok: true };
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

/** Требования по Java и текущий выбор — для вкладки «Настройки → Сборки» */
ipcMain.handle('settings:buildInfo', () => {
  try {
    const builds = readBuilds();
    const list = builds.map((b) => {
      let required = null;
      try {
        const v = JSON.parse(fs.readFileSync(path.join(VER_DIR, b.name, 'version.json'), 'utf8'));
        required = (v.javaVersion && v.javaVersion.majorVersion) || 8;
      } catch (_) {}
      return { name: b.name, version: b.version, status: b.status, requiredJava: required,
        loader: b.loader || 'vanilla', loaderVersion: b.loaderVersion || null };
    });
    return { ok: true, builds: list };
  } catch (err) {
    return { ok: false, error: err.message, builds: [] };
  }
});

// ============================================================
// IPC: МОДЫ / РЕСУРСЫ / ШЕЙДЕРЫ / МОДПАКИ (Modrinth + CurseForge)
// ============================================================
ipcMain.handle('mods:sources', async () => {
  return {
    ok: true,
    default: defaultContentSource(),
    curseforge: !!curseforgeKey()
  };
});

/** Приводит результаты поиска (Modrinth и CurseForge) к одному виду для интерфейса */
function normalizeHits(hits) {
  return (hits || []).map((h) => ({
    source: h.source || 'modrinth',
    projectId: String(h.projectId || h.project_id || h.slug || ''),
    slug: h.slug || '',
    title: h.title || '',
    description: h.description || h.summary || '',
    author: h.author || '',
    downloads: h.downloads || 0,
    icon: h.icon || h.icon_url || null
  }));
}

ipcMain.handle('mods:search', async (_e, payload) => {
  try {
    const res = await contentSearch(payload || {});
    return { ok: true, hits: normalizeHits(res.hits), total: res.total };
  } catch (err) {
    return { ok: false, error: err.message, hits: [], total: 0 };
  }
});

ipcMain.handle('mods:install', (_e, payload) => serial(async () => {
  try {
    const { build, projectId, type, source } = payload || {};
    const b = readBuilds().find((x) => x.name === build);
    if (!b) throw new Error('Сборка не найдена');
    const file = await contentResolve({
      source, projectId, type, gameVersion: b.version, loader: b.loader
    });
    const dest = await contentInstallFile(build, type, file);
    const filename = path.basename(dest);
    addContentRecord(build, {
      type, file: filename, source: file.source, projectId: file.projectId,
      slug: file.slug, title: file.title, version: file.version,
      versionId: file.versionId, size: file.size
    });
    return { ok: true, file: filename, title: file.title };
  } catch (err) {
    return { ok: false, error: err.message };
  }
}));

ipcMain.handle('mods:listInstalled', async (_e, payload) => {
  try {
    const { build, type } = payload || {};
    const dirName = CONTENT_DIR[type] || 'mods';
    const dir = path.join(VER_DIR, build, dirName);
    const records = readContent(build);
    const items = [];
    try {
      for (const name of await fsp.readdir(dir)) {
        const st = await fsp.stat(path.join(dir, name));
        if (!st.isFile()) continue;
        const rec = records.find((r) => (CONTENT_DIR[r.type] || 'mods') === dirName && r.file === name);
        items.push({
          name, size: st.size,
          source: rec ? rec.source || null : null,
          title: rec ? rec.title || null : null,
          version: rec ? rec.version || null : null,
          projectId: rec ? rec.projectId || null : null,
          versionId: rec ? rec.versionId || null : null
        });
      }
    } catch (_) { /* папки ещё нет */ }
    items.sort((a, b) => a.name.localeCompare(b.name));
    return { ok: true, items };
  } catch (err) {
    return { ok: false, error: err.message, items: [] };
  }
});

ipcMain.handle('mods:deleteInstalled', async (_e, payload) => {
  try {
    const { build, type, file } = payload || {};
    const dir = path.join(VER_DIR, build, CONTENT_DIR[type] || 'mods');
    const base = path.basename(String(file || ''));
    const target = path.join(dir, base);
    if (!target.startsWith(dir)) throw new Error('Недопустимый путь');
    await fsp.rm(target, { recursive: true, force: true });
    removeContentRecord(build, type, base);
    return { ok: true };
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

// Список версий установленного мода — для окна «Изменить версию»
ipcMain.handle('mods:versions', async (_e, payload) => {
  try {
    const { projectId, source, type, gameVersion, loader } = payload || {};
    if (!projectId) throw new Error('Для этого файла неизвестен проект — версию изменить нельзя');
    const versions = await contentVersions({ source, projectId, type, gameVersion, loader });
    return { ok: true, versions: versions.slice(0, 60) };
  } catch (err) {
    return { ok: false, error: err.message, versions: [] };
  }
});

// Установка выбранной версии мода поверх старого файла
ipcMain.handle('mods:changeVersion', (_e, payload) => serial(async () => {
  try {
    const { build, type, projectId, source, versionId, oldFile } = payload || {};
    const b = readBuilds().find((x) => x.name === build);
    if (!b) throw new Error('Сборка не найдена');
    const versions = await contentVersions({ source, projectId, type, gameVersion: b.version, loader: b.loader });
    const v = versions.find((x) => String(x.versionId) === String(versionId));
    if (!v) throw new Error('Такая версия проекта не найдена');
    if (!v.compatible) {
      throw new Error('Версия не подходит под ' + b.version + ' / ' + (b.loader || 'vanilla'));
    }
    const dest = await contentInstallFile(build, type, v);
    const filename = path.basename(dest);
    // старый файл мог называться иначе — убираем его и его запись
    if (oldFile && oldFile !== filename) {
      const dir = path.join(VER_DIR, build, CONTENT_DIR[type] || 'mods');
      await fsp.rm(path.join(dir, path.basename(String(oldFile))), { force: true });
      removeContentRecord(build, type, path.basename(String(oldFile)));
    }
    addContentRecord(build, {
      type, file: filename, source: v.source || source, projectId: String(projectId),
      title: v.name || v.version, version: v.version, versionId: v.versionId, size: v.size
    });
    return { ok: true, file: filename, version: v.version };
  } catch (err) {
    return { ok: false, error: err.message };
  }
}));

// Дерево зависимостей установленного мода (обязательные + опциональные)
ipcMain.handle('mods:deps', async (_e, payload) => {
  try {
    const { build, type, projectId, source, versionId, maxDepth } = payload || {};
    if (!projectId) throw new Error('Проект неизвестен — мод добавлен вручную?');
    const dirName = CONTENT_DIR[type] || 'mods';
    const installed = new Set(readContent(build)
      .filter((r) => (CONTENT_DIR[r.type] || 'mods') === dirName && r.projectId)
      .map((r) => String(r.projectId)));
    const seen = new Set([String(projectId)]);
    const stat = { nodes: 0 };
    const src = source === 'curseforge' ? 'curseforge' : 'modrinth';

    async function buildNode(pid, verId, dep, lvl) {
      const n = {
        projectId: String(pid), source: src, dep,
        title: null, icon: null, installed: installed.has(String(pid)),
        children: [], error: null
      };
      try {
        const info = await contentProjectInfo(pid, src);
        n.title = info.title;
        n.icon = info.icon;
      } catch (_) { n.title = String(pid); }
      if (lvl < (maxDepth || 3) && stat.nodes < 50) {
        let deps = [];
        try { deps = await contentDeps({ source: src, projectId: pid, type, versionId: verId }); }
        catch (e) { n.error = e.message; }
        for (const d of deps) {
          if (!d.projectId || seen.has(d.projectId) || stat.nodes >= 50) continue;
          seen.add(d.projectId);   // защита от циклов
          stat.nodes++;
          n.children.push(await buildNode(d.projectId, d.versionId, d.dep, lvl + 1));
        }
      }
      return n;
    }

    const root = await buildNode(String(projectId), versionId || null, 'root', 0);
    return { ok: true, tree: root };
  } catch (err) {
    return { ok: false, error: err.message, tree: null };
  }
});

/** Раскладывает overrides из zip-модпака в папку сборки */
async function extractModpackOverrides(zip, buildDir, folderNames) {
  for (const e of zip.getEntries()) {
    if (e.isDirectory) continue;
    let rel = null;
    for (const f of folderNames) {
      const m = new RegExp('^' + f + '/(.+)$').exec(e.entryName);
      if (m) { rel = m[1]; break; }
    }
    if (!rel) continue;
    const dest = path.join(buildDir, rel);
    if (!dest.startsWith(buildDir)) continue;         // защита от выхода за папку
    await fsp.mkdir(path.dirname(dest), { recursive: true });
    await fsp.writeFile(dest, e.getData());
  }
}

async function downloadModpackFiles(buildName, buildDir, entries) {
  const total = Math.max(entries.length, 1);
  let i = 0;
  for (const it of entries) {
    i++;
    const dest = path.join(buildDir, it.path);
    if (!dest.startsWith(buildDir)) continue;
    sendEvent('mods:progress', {
      build: buildName, percent: Math.round((i / total) * 100),
      text: 'Файлы модпака ' + i + '/' + total
    });
    try {
      await downloadIfMissing(it.url, dest, it.size || null, { attempts: 3 });
      const type = contentTypeFromPath(it.path);
      if (type) {
        addContentRecord(buildName, Object.assign({ type, file: path.basename(dest) }, it.rec || {}));
      }
    } catch (_) { /* отдельный файл не критичен — идём дальше */ }
  }
}

/** Обогащает провенанс файлов модпака Modrinth: опознаёт по sha1 (project/version) */
async function enrichModpackProvenanceModrinth(buildName) {
  const records = readContent(buildName).filter((r) => r.sha1 && (r.source === 'unknown' || !r.projectId));
  if (!records.length) return;
  const found = await modrinthIdentifyBySha1(records.map((r) => r.sha1));
  for (const r of records) {
    const ver = found[r.sha1];
    if (!ver || !ver.project_id) continue;
    addContentRecord(buildName, {
      type: r.type, file: r.file,
      source: 'modrinth', projectId: ver.project_id, slug: ver.slug || null,
      title: ver.name, version: ver.version_number || ver.name,
      versionId: ver.id, size: r.size, sha1: r.sha1
    });
  }
}

/** Установка модпака Modrinth (.mrpack) */
async function installModpackModrinth({ projectId, name }) {
  const list = await fetchJSON(MODRINTH_API + '/project/' + projectId + '/version');
  if (!Array.isArray(list) || !list.length) throw new Error('У модпака нет версий');
  const pick = list[0];
  const file = (pick.files || []).find((f) => f.primary) || (pick.files || [])[0];
  if (!file) throw new Error('У модпака нет файла');

  const tmp = path.join(CACHE_DIR, 'modpacks', file.filename);
  await downloadIfMissing(file.url, tmp, file.size, { attempts: 3 });

  const zip = new AdmZip(tmp);
  const idxEntry = zip.getEntry('modrinth.index.json');
  if (!idxEntry) throw new Error('Файл не является модпаком Modrinth');
  const index = JSON.parse(zip.readAsText(idxEntry));

  const deps = index.dependencies || {};
  const mc = deps.minecraft;
  if (!mc) throw new Error('В модпаке не указана версия Minecraft');
  let loader = 'vanilla', loaderVersion = null;
  if (deps['fabric-loader']) { loader = 'fabric'; loaderVersion = deps['fabric-loader']; }
  else if (deps['quilt-loader']) { loader = 'quilt'; loaderVersion = deps['quilt-loader']; }
  else if (deps.forge) { loader = 'forge'; loaderVersion = deps.forge; }
  else if (deps.neoforge) { loader = 'neoforge'; loaderVersion = deps.neoforge; }

  const buildName = cleanName(name || index.name || ('Modpack ' + projectId));
  const res = await createBuild({ name: buildName, version: mc, loader, loaderVersion });
  if (!res.ok) return res;

  const buildDir = path.join(VER_DIR, buildName);
  const entries = [];
  for (const f of (index.files || [])) {
    const env = f.env || {};
    if (env.client === 'unsupported') continue;
    const url = (f.downloads || [])[0];
    if (!url || !f.path) continue;
    entries.push({
      url, path: f.path, size: f.fileSize,
      rec: { source: 'modrinth', sha1: (f.hashes && f.hashes.sha1) || null }
    });
  }
  await downloadModpackFiles(buildName, buildDir, entries);
  await extractModpackOverrides(zip, buildDir, ['client-overrides', 'overrides']);
  await enrichModpackProvenanceModrinth(buildName);

  sendEvent('mods:progress', { build: buildName, percent: 100, text: 'Модпак установлен' });
  return { ok: true, name: buildName };
}

/** Установка модпака CurseForge (zip с manifest.json) */
async function installModpackCurseforge({ projectId, name }) {
  cfEnsureKey();
  const info = await cfJSON('/mods/' + encodeURIComponent(projectId));
  const mod = info.data || {};
  const filesRes = await cfJSON('/mods/' + encodeURIComponent(projectId) + '/files?pageSize=50');
  const pick = (filesRes.data || []).find((f) => f.releaseType === 1) || (filesRes.data || [])[0];
  if (!pick) throw new Error('У модпака нет файлов');
  const zipUrl = pick.downloadUrl || cfCdnUrl(pick);

  const tmp = path.join(CACHE_DIR, 'modpacks', pick.fileName);
  await downloadIfMissing(zipUrl, tmp, pick.fileLength || null, { attempts: 3 });

  const zip = new AdmZip(tmp);
  const manEntry = zip.getEntry('manifest.json');
  if (!manEntry) throw new Error('Файл не является модпаком CurseForge');
  const manifest = JSON.parse(zip.readAsText(manEntry));

  const mc = manifest.minecraft && manifest.minecraft.version;
  if (!mc) throw new Error('В модпаке не указана версия Minecraft');
  const ml = ((manifest.minecraft && manifest.minecraft.modLoaders) || [])
    .find((m) => m.primary) || ((manifest.minecraft && manifest.minecraft.modLoaders) || [])[0];
  let loader = 'vanilla', loaderVersion = null;
  if (ml && ml.id) {
    const dash = String(ml.id).indexOf('-');
    const kind = dash >= 0 ? ml.id.slice(0, dash) : ml.id;
    loaderVersion = dash >= 0 ? ml.id.slice(dash + 1) : null;
    if (kind === 'forge') loader = 'forge';
    else if (kind === 'neoforge') loader = 'neoforge';
    else if (kind === 'fabric') loader = 'fabric';
    else if (kind === 'quilt') loader = 'quilt';
  }

  const buildName = cleanName(name || mod.name || ('Modpack ' + projectId));
  const res = await createBuild({ name: buildName, version: mc, loader, loaderVersion });
  if (!res.ok) return res;

  const buildDir = path.join(VER_DIR, buildName);
  const entries = [];
  const list = manifest.files || [];
  for (let i = 0; i < list.length; i++) {
    const f = list[i];
    sendEvent('mods:progress', {
      build: buildName, percent: Math.round((i / Math.max(list.length, 1)) * 100),
      text: 'Поиск файлов модпака ' + (i + 1) + '/' + list.length
    });
    try {
      const fr = await cfJSON('/mods/' + f.projectID + '/files/' + f.fileID);
      const fd = fr.data || {};
      const url = fd.downloadUrl || cfCdnUrl(fd);
      if (url) entries.push({
        url, path: path.join('mods', fd.fileName), size: fd.fileLength || null,
        rec: {
          source: 'curseforge', projectId: String(f.projectID),
          versionId: String(f.fileID), version: fd.displayName || null, size: fd.fileLength || null
        }
      });
    } catch (_) { /* пропускаем недоступный файл */ }
  }
  await downloadModpackFiles(buildName, buildDir, entries);

  const overridesDir = manifest.overrides || 'overrides';
  await extractModpackOverrides(zip, buildDir, [overridesDir, 'overrides', 'client-overrides']);

  sendEvent('mods:progress', { build: buildName, percent: 100, text: 'Модпак установлен' });
  return { ok: true, name: buildName };
}

ipcMain.handle('mods:installModpack', (_e, payload) => serial(async () => {
  try {
    const p = payload || {};
    if (p.source === 'curseforge') return await installModpackCurseforge(p);
    return await installModpackModrinth(p);
  } catch (err) {
    return { ok: false, error: err.message };
  }
}));

// ============================================================
// ПРОИСХОЖДЕНИЕ КОНТЕНТА И ФОРМАТ .ccli
// ============================================================
// .ccli — единый текстовый файл сборки: версия игры и загрузчик, списки
// модов/ресурсов/шейдеров/миров (источник, проект, версия) и, по желанию,
// конфиги (одним сжатым блоком или полным текстом).

const CCLI_VERSION = 1;
const CCLI_EXT = '.ccli';
const CCLI_GROUPS = ['mods', 'resourcepacks', 'shaderpacks', 'worlds'];
const CCLI_GROUP_DIR = {
  mods: 'mods', resourcepacks: 'resourcepacks', shaderpacks: 'shaderpacks', worlds: 'saves'
};
const CCLI_CONFIG_DIRS = ['config', 'defaultconfigs'];
const CCLI_SOURCE_LABELS = { modrinth: 'Modrinth', curseforge: 'CurseForge', unknown: 'неизвестно' };

/** Файл провенанса контента сборки (кто откуда скачан) */
function contentFile(build) { return path.join(VER_DIR, build, 'content.json'); }

function readContent(build) {
  try {
    const list = JSON.parse(fs.readFileSync(contentFile(build), 'utf8'));
    return Array.isArray(list) ? list : [];
  } catch (_) { return []; }
}

function writeContent(build, list) {
  try {
    fs.mkdirSync(path.join(VER_DIR, build), { recursive: true });
    fs.writeFileSync(contentFile(build), JSON.stringify(list, null, 2));
  } catch (_) { /* не критично */ }
}

function contentKey(type, file) { return (CONTENT_DIR[type] || 'mods') + '/' + file; }

/** Записывает/обновляет сведения о скачанном файле сборки */
function addContentRecord(build, rec) {
  const list = readContent(build);
  const clean = {
    type: rec.type,
    file: rec.file,
    source: rec.source || 'unknown',
    projectId: rec.projectId != null ? String(rec.projectId) : null,
    slug: rec.slug || null,
    title: rec.title || null,
    version: rec.version || null,
    versionId: rec.versionId != null ? String(rec.versionId) : null,
    size: rec.size || null,
    sha1: rec.sha1 || null
  };
  const key = contentKey(clean.type, clean.file);
  const i = list.findIndex((r) => contentKey(r.type, r.file) === key);
  if (i >= 0) list[i] = Object.assign({}, list[i], clean);
  else list.push(clean);
  writeContent(build, list);
}

function removeContentRecord(build, type, file) {
  const key = contentKey(type, file);
  writeContent(build, readContent(build).filter((r) => contentKey(r.type, r.file) !== key));
}

/** Тип контента по пути внутри сборки (mods/x.jar → mods) */
function contentTypeFromPath(p) {
  const top = String(p || '').split(/[\\/]/)[0].toLowerCase();
  if (top === 'mods') return 'mods';
  if (top === 'resourcepacks' || top === 'texturepacks') return 'resourcepacks';
  if (top === 'shaderpacks') return 'shaderpacks';
  if (top === 'saves') return 'worlds';
  return null;
}

/** sha1 файла (распознавание и проверка целостности) */
async function fileSha1(abs) {
  try {
    const buf = await fsp.readFile(abs);
    return crypto.createHash('sha1').update(buf).digest('hex');
  } catch (_) { return null; }
}

/** Пакетное опознание файлов в Modrinth по sha1 (единственный источник с таким поиском) */
async function modrinthIdentifyBySha1(hashes) {
  const uniq = [...new Set((hashes || []).filter(Boolean))];
  if (!uniq.length) return {};
  try {
    return await fetchJSONPost(MODRINTH_API + '/version_files', { hashes: uniq, algorithm: 'sha1' }, 1);
  } catch (_) { return {}; }
}

/**
 * Собирает список контента сборки: записи content.json + файлы на диске,
 * которых нет в реестре (их пытаемся опознать в Modrinth по sha1).
 */
async function collectProvenance(name) {
  const records = readContent(name);
  const rows = [];
  const unknown = [];

  for (const group of CCLI_GROUPS) {
    const dirName = CCLI_GROUP_DIR[group];
    const dir = path.join(VER_DIR, name, dirName);
    let names = [];
    try { names = await fsp.readdir(dir); } catch (_) { continue; }
    for (const fn of names) {
      const abs = path.join(dir, fn);
      const st = await fsp.stat(abs).catch(() => null);
      if (!st || !st.isFile()) continue;
      const rec = records.find((r) => contentKey(r.type, r.file) === dirName + '/' + fn);
      const row = {
        group, file: fn, size: st.size,
        source: 'unknown', projectId: null, slug: null,
        title: null, version: null, versionId: null, sha1: null
      };
      if (rec) {
        row.source = rec.source || 'unknown';
        row.projectId = rec.projectId || null;
        row.slug = rec.slug || null;
        row.title = rec.title || null;
        row.version = rec.version || null;
        row.versionId = rec.versionId || null;
        row.sha1 = rec.sha1 || null;
      }
      if (row.source === 'unknown') unknown.push({ row, abs });
      rows.push(row);
    }
  }

  if (unknown.length) {
    for (const u of unknown) if (!u.row.sha1) u.row.sha1 = await fileSha1(u.abs);
    const found = await modrinthIdentifyBySha1(unknown.map((u) => u.row.sha1));
    for (const u of unknown) {
      const ver = u.row.sha1 ? found[u.row.sha1] : null;
      if (ver && ver.project_id) {
        u.row.source = 'modrinth';
        u.row.projectId = ver.project_id;
        u.row.versionId = ver.id;
        u.row.version = ver.version_number || ver.name || null;
        u.row.title = ver.name || null;
      }
    }
  }

  return rows;
}

// ---------- конфиги ----------

/** Рекурсивный обход файлов каталога (ошибки глотаются) */
async function walkFiles(root, onFile) {
  const rec = async (dir) => {
    let entries = [];
    try { entries = await fsp.readdir(dir, { withFileTypes: true }); } catch (_) { return; }
    for (const e of entries) {
      const abs = path.join(dir, e.name);
      if (e.isDirectory()) await rec(abs);
      else if (e.isFile()) await onFile(abs);
    }
  };
  await rec(root);
}

/** Собирает файлы конфигов сборки (config/, defaultconfigs/) */
async function collectConfigFiles(name) {
  const out = [];
  const base = path.join(VER_DIR, name);
  for (const top of CCLI_CONFIG_DIRS) {
    await walkFiles(path.join(base, top), async (abs) => {
      const buf = await fsp.readFile(abs).catch(() => null);
      if (!buf) return;
      out.push({ path: path.relative(base, abs).split(path.sep).join('/'), buf, size: buf.length });
    });
  }
  out.sort((a, b) => a.path.localeCompare(b.path));
  return out;
}

/** Похоже на текстовый файл (для «полного» режима конфигов) */
function isTextBuffer(buf) {
  if (buf.includes(0)) return false;
  return !buf.toString('utf8').includes('\uFFFD');
}

/** Разделитель, которого нет ни в одном конфиге (чтобы «полный» режим читался) */
function pickCcliDelimiter(files) {
  for (let i = 0; i < 50; i++) {
    const d = '@@@CCLI-' + crypto.randomBytes(4).toString('hex') + '@@@';
    if (!files.some((f) => f.buf.toString('utf8').includes(d))) return d;
  }
  return '@@@CCLI-' + Date.now().toString(16) + '@@@';
}

// ---------- экранирование ячеек ----------
function ccliCell(v) {
  return String(v == null ? '' : v).replace(/[\\\t\r\n]/g, (c) =>
    c === '\\' ? '\\\\' : c === '\t' ? '\\t' : c === '\r' ? '\\r' : '\\n');
}
function ccliUncell(v) {
  return String(v == null ? '' : v).replace(/\\(.)/g, (m, c) =>
    c === 'n' ? '\n' : c === 't' ? '\t' : c === 'r' ? '\r' : c === '\\' ? '\\' : c);
}

// ---------- экспорт ----------

/** Строит текст .ccli для сборки */
async function buildToCcli(name, opts) {
  const b = readBuilds().find((x) => x.name === name);
  if (!b) throw new Error('Сборка не найдена');
  const wantConfigs = !!(opts && opts.configs);
  const configMode = opts && opts.configMode === 'text' ? 'text' : 'gz';

  const rows = await collectProvenance(name);

  const L = [];
  L.push('# CCLI/' + CCLI_VERSION + ' — сборка C Minerva Launcher');
  L.push('# Формат: текстовый файл сборки. Разделы [mods]/[resourcepacks]/[shaderpacks]/[worlds].');
  L.push('# Строки контента (через табуляцию): source, projectId, slug, title, version, versionId, file, size, sha1');
  L.push('name=' + (b.name || name));
  L.push('mc=' + (b.version || ''));
  L.push('loader=' + (b.loader || 'vanilla'));
  L.push('loaderVersion=' + (b.loaderVersion || ''));
  L.push('created=' + new Date().toISOString());
  L.push('');

  for (const group of CCLI_GROUPS) {
    L.push('[' + group + ']');
    for (const r of rows.filter((x) => x.group === group)) {
      L.push([r.source, r.projectId, r.slug, r.title, r.version, r.versionId,
              r.file, r.size, r.sha1].map(ccliCell).join('\t'));
    }
    L.push('');
  }

  L.push('[config]');
  if (!wantConfigs) {
    L.push('mode=none');
  } else {
    const files = await collectConfigFiles(name);
    if (configMode === 'text') {
      const delim = pickCcliDelimiter(files);
      L.push('mode=text');
      L.push('delimiter=' + delim);
      let skipped = 0;
      for (const f of files) if (!isTextBuffer(f.buf)) skipped++;
      if (skipped) L.push('# пропущено бинарных файлов: ' + skipped + ' (используйте сжатый режим)');
      for (const f of files) {
        if (!isTextBuffer(f.buf)) continue;
        L.push(delim + ' ' + f.path);
        L.push(f.buf.toString('utf8').replace(/\r?\n/g, '\n'));
      }
      L.push(delim);
    } else {
      const payload = { version: CCLI_VERSION, files: {} };
      for (const f of files) payload.files[f.path] = f.buf.toString('base64');
      const gz = zlib.gzipSync(Buffer.from(JSON.stringify(payload), 'utf8'), { level: 9 });
      L.push('mode=gz');
      L.push('encoding=json+gzip+base64');
      L.push('data=' + gz.toString('base64'));
    }
  }
  L.push('');
  L.push('[end]');
  return L.join('\n') + '\n';
}

// ---------- разбор ----------

function parseCcliConfig(lines) {
  const kv = {};
  let bodyStart = 0;
  for (let i = 0; i < lines.length; i++) {
    const t = lines[i].trim();
    if (!t || t.startsWith('#')) { bodyStart = i + 1; continue; }
    const eq = lines[i].indexOf('=');
    const key = eq > 0 ? lines[i].slice(0, eq).trim().toLowerCase() : '';
    if (eq > 0 && /^[a-z0-9_+-]+$/.test(key)) {
      kv[key] = lines[i].slice(eq + 1).trim();
      bodyStart = i + 1;
    } else break;
  }

  const mode = (kv.mode || 'none').toLowerCase();
  if (mode === 'none') return { mode: 'none', files: [] };

  if (mode === 'gz') {
    if (!kv.data) return { mode: 'none', files: [] };
    let json;
    try {
      json = JSON.parse(zlib.gunzipSync(Buffer.from(kv.data, 'base64')).toString('utf8'));
    } catch (err) {
      throw new Error('Не удалось распаковать конфиги из .ccli: ' + errText(err));
    }
    const files = Object.keys(json.files || {}).map((p) => ({ path: p, b64: json.files[p] }));
    return { mode: 'gz', files };
  }

  if (mode === 'text') {
    const delim = kv.delimiter || '@@@CCLI@@@';
    const body = '\n' + lines.slice(bodyStart).join('\n');
    const parts = body.split('\n' + delim);
    const files = [];
    for (let i = 1; i < parts.length; i++) {
      const chunk = parts[i];
      const nl = chunk.indexOf('\n');
      const header = (nl >= 0 ? chunk.slice(0, nl) : chunk).trim();
      if (!header) continue;                    // финальный разделитель без файла
      files.push({ path: header, text: nl >= 0 ? chunk.slice(nl + 1) : '' });
    }
    return { mode: 'text', files };
  }

  return { mode: 'none', files: [] };
}

/** Разбирает .ccli в структуру { name, mc, loader, loaderVersion, items, config } */
function parseCcli(text) {
  const raw = String(text == null ? '' : text);
  if (!raw.trim()) throw new Error('Пустой файл .ccli');

  const vm = /^[\s\ufeff]*#\s*CCLI\/(\d+)/.exec(raw);
  const lines = raw.split(/\r?\n/);

  const head = {};
  const groups = {};
  for (const g of CCLI_GROUPS) groups[g] = [];

  let section = null;
  let configStart = -1, configEnd = -1;

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const t = line.trim();
    if (!t) continue;
    if (t === '[end]') { section = 'end'; if (configStart >= 0 && configEnd < 0) configEnd = i; continue; }
    const sec = /^\[([a-z0-9_-]+)\]$/i.exec(t);
    if (sec) {
      section = sec[1].toLowerCase();
      if (section === 'config') configStart = i;
      continue;
    }
    if (section === 'end' || t.startsWith('#')) continue;
    if (!section) {
      const eq = line.indexOf('=');
      if (eq > 0) head[line.slice(0, eq).trim().toLowerCase()] = line.slice(eq + 1).trim();
      continue;
    }
    if (section === 'config') continue;         // разбирается отдельно
    if (CCLI_GROUPS.includes(section)) {
      const cells = line.split('\t');
      while (cells.length < 9) cells.push('');
      const file = ccliUncell(cells[6]);
      if (!file) continue;
      groups[section].push({
        type: section,
        source: (ccliUncell(cells[0]) || 'unknown').toLowerCase(),
        projectId: ccliUncell(cells[1]) || null,
        slug: ccliUncell(cells[2]) || null,
        title: ccliUncell(cells[3]) || null,
        version: ccliUncell(cells[4]) || null,
        versionId: ccliUncell(cells[5]) || null,
        file,
        size: ccliUncell(cells[7]) ? Number(ccliUncell(cells[7])) : null,
        sha1: ccliUncell(cells[8]) || null
      });
    }
  }

  const hasHeader = Object.keys(head).length > 0;
  if (!head.mc) head.mc = head.minecraft || '';
  const items = CCLI_GROUPS.reduce((acc, g) => acc.concat(groups[g]), []);
  if (!hasHeader && !items.length) {
    throw new Error('Это не файл .ccli (нет заголовка и списков контента)');
  }

  let config = null;
  if (configStart >= 0) {
    const end = configEnd >= 0 ? configEnd : lines.length;
    config = parseCcliConfig(lines.slice(configStart + 1, end));
  }

  return {
    version: vm ? Number(vm[1]) : CCLI_VERSION,
    name: head.name || '',
    mc: head.mc || '',
    loader: head.loader || 'vanilla',
    loaderVersion: head.loaderVersion || '',
    items,
    config
  };
}

// ---------- применение конфигов ----------

/** Раскладывает конфиги из .ccli в папку сборки (безопасно к путям) */
async function applyCcliConfigs(buildName, config) {
  const base = path.join(VER_DIR, buildName);
  let written = 0;
  for (const f of (config && config.files) || []) {
    const rel = String(f.path || '').replace(/\\/g, '/').replace(/^\/+/, '');
    if (!rel || rel.includes('..')) continue;
    const dest = path.join(base, rel);
    if (dest !== base && !dest.startsWith(base + path.sep)) continue;
    const buf = f.b64 != null
      ? Buffer.from(String(f.b64), 'base64')
      : Buffer.from(f.text == null ? '' : String(f.text), 'utf8');
    try {
      await fsp.mkdir(path.dirname(dest), { recursive: true });
      await fsp.writeFile(dest, buf);
      written++;
    } catch (_) { /* отдельный файл не критичен */ }
  }
  return written;
}

// ---------- импорт ----------

/** Свободное имя сборки (добавляет « (2)» при совпадении) */
function uniqueBuildName(base) {
  const names = new Set(readBuilds().map((x) => String(x.name).toLowerCase()));
  const cut = String(base).slice(0, 40);
  if (!names.has(cut.toLowerCase())) return cut;
  for (let i = 2; i < 1000; i++) {
    const cand = (String(base).slice(0, 36) + ' (' + i + ')').slice(0, 40);
    if (!names.has(cand.toLowerCase())) return cand;
  }
  return (String(base).slice(0, 30) + ' ' + Date.now().toString(36)).slice(0, 40);
}

async function modrinthResolveForCcli(item, parsed) {
  if (item.versionId) {
    try {
      const ver = await fetchJSON(MODRINTH_API + '/version/' + encodeURIComponent(item.versionId), 2);
      const file = (ver.files || []).find((f) => f.primary) || (ver.files || [])[0];
      if (file) return {
        source: 'modrinth', url: file.url, size: file.size,
        projectId: ver.project_id, slug: ver.slug || item.slug || null,
        title: ver.name, version: ver.version_number || ver.name, versionId: ver.id
      };
    } catch (_) { /* попробуем другие способы */ }
  }
  if (item.sha1) {
    try {
      const ver = await fetchJSON(MODRINTH_API + '/version_file/' + encodeURIComponent(item.sha1), 1);
      const file = (ver.files || []).find((f) => f.primary) || (ver.files || [])[0];
      if (file) return {
        source: 'modrinth', url: file.url, size: file.size,
        projectId: ver.project_id, slug: ver.slug || item.slug || null,
        title: ver.name, version: ver.version_number || ver.name, versionId: ver.id
      };
    } catch (_) { /* идём дальше */ }
  }
  if (item.projectId) {
    const picked = await modrinthPickVersion(item.projectId, item.type, parsed.mc, parsed.loader);
    return {
      source: 'modrinth', url: picked.file.url, size: picked.file.size,
      projectId: picked.version.project_id || item.projectId,
      slug: picked.version.slug || item.slug || null,
      title: picked.version.name,
      version: picked.version.version_number || picked.version.name,
      versionId: picked.version.id
    };
  }
  return null;
}

async function curseforgeResolveForCcli(item, parsed) {
  if (!item.projectId) return null;
  if (item.versionId) {
    const r = await cfJSON('/mods/' + encodeURIComponent(item.projectId) + '/files/' + encodeURIComponent(item.versionId));
    const fd = r.data || {};
    const url = fd.downloadUrl || cfCdnUrl(fd);
    if (!url) throw new Error('автор запретил прямое скачивание на CurseForge');
    return {
      source: 'curseforge', url, size: fd.fileLength || null,
      projectId: String(item.projectId), slug: item.slug || null,
      title: item.title || fd.displayName, version: fd.displayName || item.version,
      versionId: fd.id != null ? String(fd.id) : item.versionId
    };
  }
  const f = await curseforgePickFile(item.projectId, item.type, parsed.mc, parsed.loader);
  return {
    source: 'curseforge', url: f.url, size: f.size,
    projectId: String(item.projectId), slug: f.slug || item.slug || null,
    title: item.title || f.version, version: f.version,
    versionId: f.id != null ? String(f.id) : null
  };
}

/** Скачивает один элемент контента из .ccli и записывает его происхождение */
async function importContentItem(buildName, parsed, item) {
  const dirName = CCLI_GROUP_DIR[item.type] || 'mods';
  const file = path.basename(String(item.file));
  const dest = path.join(VER_DIR, buildName, dirName, file);

  let resolved = null;
  if (item.source === 'curseforge') {
    if (!curseforgeKey()) throw new Error('нужен API-ключ CurseForge (Настройки → Контент)');
    resolved = await curseforgeResolveForCcli(item, parsed);
  } else if (item.source === 'modrinth') {
    resolved = await modrinthResolveForCcli(item, parsed);
  } else {
    resolved = await modrinthResolveForCcli(item, parsed);   // попытка по sha1
    if (!resolved) throw new Error('источник неизвестен, файл не найден в Modrinth');
  }
  if (!resolved || !resolved.url) throw new Error('не удалось получить ссылку на файл');

  await downloadIfMissing(resolved.url, dest, resolved.size || item.size || null, { attempts: 3 });
  addContentRecord(buildName, {
    type: item.type, file,
    source: resolved.source, projectId: resolved.projectId, slug: resolved.slug,
    title: resolved.title, version: resolved.version, versionId: resolved.versionId,
    size: resolved.size || item.size
  });
  return resolved;
}

/** Создаёт сборку из текста .ccli и скачивает её контент */
async function importBuildFromCcli(text, opts) {
  const parsed = parseCcli(text);
  if (!parsed.mc) throw new Error('В файле .ccli не указана версия Minecraft');
  const loader = LOADERS.includes(parsed.loader) ? parsed.loader : 'vanilla';
  const wantName = cleanName((opts && opts.name) || parsed.name || ('Импорт ' + parsed.mc));
  const name = uniqueBuildName(wantName);

  const res = await createBuild({ name, version: parsed.mc, loader, loaderVersion: parsed.loaderVersion || '' });
  if (!res.ok) return res;

  const summary = { installed: 0, skipped: 0, configs: 0, errors: [] };
  const items = parsed.items || [];

  for (let i = 0; i < items.length; i++) {
    const it = items[i];
    sendEvent('mods:progress', {
      build: name, percent: Math.round((i / Math.max(items.length, 1)) * 100),
      text: 'Импорт ' + (i + 1) + '/' + items.length + ': ' + it.file
    });
    try {
      await importContentItem(name, parsed, it);
      summary.installed++;
    } catch (err) {
      summary.skipped++;
      if (summary.errors.length < 30) summary.errors.push(it.file + ': ' + errText(err));
    }
  }

  const hasConfigs = !!(parsed.config && parsed.config.mode !== 'none');
  if (opts && opts.configs && hasConfigs) {
    summary.configs = await applyCcliConfigs(name, parsed.config);
  }

  sendEvent('mods:progress', { build: name, percent: 100, text: 'Импорт завершён' });
  return { ok: true, name, summary, hasConfigs };
}

// ---------- IPC: экспорт / импорт .ccli ----------

ipcMain.handle('builds:ccliInfo', async (_e, name) => {
  try {
    const rows = await collectProvenance(name);
    const configs = await collectConfigFiles(name);
    const counts = {};
    for (const g of CCLI_GROUPS) counts[g] = rows.filter((r) => r.group === g).length;
    return {
      ok: true, counts, total: rows.length,
      configs: configs.length, configsSize: configs.reduce((s, f) => s + f.size, 0)
    };
  } catch (err) {
    return { ok: false, error: errText(err) };
  }
});

ipcMain.handle('builds:inspectCcli', async (_e, text) => {
  try {
    const parsed = parseCcli(text);
    const counts = {};
    for (const g of CCLI_GROUPS) counts[g] = parsed.items.filter((r) => r.type === g).length;
    return {
      ok: true, name: parsed.name, mc: parsed.mc, loader: parsed.loader,
      loaderVersion: parsed.loaderVersion, total: parsed.items.length, counts,
      hasConfigs: !!(parsed.config && parsed.config.mode !== 'none'),
      configMode: parsed.config ? parsed.config.mode : 'none'
    };
  } catch (err) {
    return { ok: false, error: errText(err) };
  }
});

ipcMain.handle('builds:exportCcli', async (_e, payload) => {
  try {
    const name = String((payload && payload.build) || '');
    const text = await buildToCcli(name, {
      configs: !!(payload && payload.configs),
      configMode: payload && payload.configMode
    });
    const safe = name.replace(/[/\\:*?"<>|]/g, '_').trim() || 'build';
    const win = mainWindow && !mainWindow.isDestroyed() ? mainWindow : null;
    const out = await dialog.showSaveDialog(win, {
      title: 'Экспорт сборки в .ccli',
      defaultPath: safe + CCLI_EXT,
      filters: [
        { name: 'Сборка CMCL', extensions: ['ccli'] },
        { name: 'Все файлы', extensions: ['*'] }
      ]
    });
    if (out.canceled || !out.filePath) return { ok: false, canceled: true };
    let file = out.filePath;
    if (!/\.ccli$/i.test(file)) file += CCLI_EXT;
    await fsp.writeFile(file, text, 'utf8');
    return { ok: true, path: file, bytes: Buffer.byteLength(text, 'utf8') };
  } catch (err) {
    return { ok: false, error: errText(err) };
  }
});

ipcMain.handle('builds:importCcli', (_e, payload) => serial(async () => {
  try {
    const text = payload && payload.data;
    if (!text) throw new Error('Пустой файл .ccli');
    return await importBuildFromCcli(text, {
      name: payload && payload.name,
      configs: payload && payload.configs
    });
  } catch (err) {
    return { ok: false, error: errText(err) };
  }
}));

// ============================================================
// СЕРВЕРЫ — ядра (Vanilla/Paper/Purpur/Fabric/Forge) и панель управления
// ============================================================
let serverProcess = null;   // запущенный процесс сервера (только один за раз)
let serverRunName = null;   // имя запущенного сервера

function servDir(name) {
  return path.join(SERV_DIR, name);
}

function readServers() {
  try {
    const list = JSON.parse(fs.readFileSync(SERVERS_FILE, 'utf8'));
    return Array.isArray(list) ? list : [];
  } catch (_) { return []; }
}

function writeServers(list) {
  fs.mkdirSync(SERV_DIR, { recursive: true });
  fs.writeFileSync(SERVERS_FILE, JSON.stringify(list, null, 2));
}

function updateServer(name, patch) {
  const list = readServers();
  const s = list.find((x) => x.name === name);
  if (!s) return null;
  Object.assign(s, patch);
  writeServers(list);
  return s;
}

function cleanServerName(raw) {
  const s = String(raw || '').trim().replace(/\s+/g, ' ');
  if (!s) throw new Error('Введите название сервера');
  if (s.length > 40) throw new Error('Название слишком длинное (макс. 40 символов)');
  if (/[/\\:*?"<>|]/.test(s)) throw new Error('Название содержит запрещённые символы');
  if (s === '.' || s === '..') throw new Error('Недопустимое название');
  return s;
}

function isPreRelease(v) {
  return /-(alpha|beta|rc|snapshot|pre|experimental)/i.test(String(v));
}

/** Человекочитаемое сообщение об ошибке (не допускает пустой текст) */
function errText(err) {
  if (!err) return 'Неизвестная ошибка';
  if (typeof err === 'string') return err || 'Неизвестная ошибка';
  return (err.message && String(err.message).trim()) ? err.message : 'Неизвестная ошибка';
}

/** Требуемая мажорная версия Java для сервера указанной версии Minecraft */
function serverJavaMajor(mc) {
  const m = /^1\.(\d+)(?:\.(\d+))?/.exec(String(mc));
  if (!m) return 21;                                     // новая схема версий (26.x и т. п.)
  const minor = Number(m[1]);
  const patch = Number(m[2] || 0);
  if (minor > 20 || (minor === 20 && patch >= 5)) return 21;
  if (minor >= 17) return 17;
  return 8;
}

/** Список версий Minecraft, поддерживаемых выбранным ядром */
async function serverVersions(core) {
  if (core === 'vanilla' || core === 'fabric') {
    const m = await getManifest();
    return m.versions.filter((v) => v.type === 'release').map((v) => v.id);
  }
  if (core === 'paper') {
    const data = await fetchJSON(PAPER_API + '/projects/paper');
    const groups = (data && data.versions) || {};
    const all = [];
    for (const key of Object.keys(groups)) for (const v of groups[key]) all.push(v);
    return preferStableSorted([...new Set(all)].filter((v) => /^\d/.test(v) && !isPreRelease(v)));
  }
  if (core === 'purpur') {
    const data = await fetchJSON(PURPUR_API + '/purpur');
    return preferStableSorted(((data && data.versions) || []).filter((v) => !isPreRelease(v)));
  }
  if (core === 'forge') {
    const xml = await fetchText(FORGE_MAVEN + '/net/minecraftforge/forge/maven-metadata.xml');
    const set = new Set();
    for (const v of parseMavenVersions(xml)) {
      const i = v.indexOf('-');
      if (i > 0) set.add(v.slice(0, i));
    }
    return preferStableSorted([...set]);
  }
  return [];
}

/** Доступные версии загрузчика для ядра (fabric/forge) и версии Minecraft */
async function serverLoaderVersions(core, mc) {
  if (core === 'fabric') {
    const list = await fetchJSON(FABRIC_META + '/versions/loader/' + mc);
    if (!Array.isArray(list)) return [];
    const stable = [];
    const rest = [];
    for (const x of list) {
      const v = (x.loader && x.loader.version) || x.version;
      if (!v) continue;
      ((x.loader && x.loader.stable) ? stable : rest).push(v);
    }
    return [...new Set([...preferStableSorted(stable), ...preferStableSorted(rest)])];
  }
  if (core === 'forge') {
    const xml = await fetchText(FORGE_MAVEN + '/net/minecraftforge/forge/maven-metadata.xml');
    const vers = parseMavenVersions(xml)
      .filter((v) => v.startsWith(mc + '-'))
      .map((v) => v.slice(mc.length + 1));
    return preferStableSorted(vers);
  }
  return [];
}

/** Прямая ссылка на серверное ядро Vanilla (server.jar) */
async function vanillaServerUrl(mc) {
  const m = await getManifest();
  const entry = m.versions.find((x) => x.id === mc);
  if (!entry) throw new Error('Версия Minecraft не найдена: ' + mc);
  const v = await fetchJSON(entry.url);
  const s = v.downloads && v.downloads.server;
  if (!s || !s.url) throw new Error('У версии ' + mc + ' нет серверного ядра');
  return { url: s.url, size: s.size };
}

/** Запуск дочернего процесса и ожидание завершения (для установщика Forge) */
function runProcess(cmd, args, cwd, onLine) {
  return new Promise((resolve, reject) => {
    const p = spawn(cmd, args, { cwd });
    let out = '';
    const feed = (d) => {
      const s = d.toString();
      out += s;
      if (onLine) for (const l of s.split(/\r?\n/)) if (l.trim()) onLine(l);
    };
    p.stdout.on('data', feed);
    p.stderr.on('data', feed);
    p.on('error', reject);
    p.on('close', (code) => resolve({ code, out }));
  });
}

/** Скачивает и распаковывает выбранное ядро в папку сервера */
async function downloadServerCore(name, spec, step) {
  const dir = servDir(name);
  await fsp.mkdir(dir, { recursive: true });
  const core = spec.core;
  const mc = spec.version;
  const dl = (url, dest, size, label) => downloadIfMissing(url, dest, size, {
    onBytes: (got, total) => step(step.percent, label + ' — ' + fmtBytes(got) + (total ? ' / ' + fmtBytes(total) : '')),
    onRetry: (msg) => step(step.percent, label + ': ' + msg)
  });

  if (core === 'vanilla') {
    step.set(8, 'Получение ссылки на сервер Vanilla…');
    const srv = await vanillaServerUrl(mc);
    step.set(20, 'Скачивание Vanilla server.jar…');
    await dl(srv.url, path.join(dir, 'server.jar'), srv.size, 'Vanilla server.jar');
    step.set(88, 'Vanilla скачан');
    return;
  }

  if (core === 'paper') {
    step.set(8, 'Поиск актуальной сборки Paper…');
    const builds = await fetchJSON(PAPER_API + '/projects/paper/versions/' + mc + '/builds');
    if (!Array.isArray(builds) || !builds.length) throw new Error('Нет сборок Paper для версии ' + mc);
    const b = builds.find((x) => x.channel === 'STABLE') || builds[0];
    const dlInfo = b.downloads && (b.downloads['server:default'] || Object.values(b.downloads || {})[0]);
    if (!dlInfo || !dlInfo.url) throw new Error('Не найдена ссылка на ядро Paper');
    step.set(20, 'Скачивание Paper (сборка ' + (b.id || '') + ')…');
    await dl(dlInfo.url, path.join(dir, 'server.jar'), dlInfo.size, 'Paper server.jar');
    step.set(88, 'Paper скачан');
    return;
  }

  if (core === 'purpur') {
    step.set(8, 'Поиск актуальной сборки Purpur…');
    const info = await fetchJSON(PURPUR_API + '/purpur/' + mc);
    const build = info && info.builds && info.builds.latest;
    if (!build) throw new Error('Нет сборок Purpur для версии ' + mc);
    const url = PURPUR_API + '/purpur/' + mc + '/' + build + '/download';
    step.set(20, 'Скачивание Purpur (сборка ' + build + ')…');
    await dl(url, path.join(dir, 'server.jar'), null, 'Purpur server.jar');
    step.set(88, 'Purpur скачан');
    return;
  }

  if (core === 'fabric') {
    step.set(6, 'Получение Fabric-загрузчика…');
    const installerList = await fetchJSON(FABRIC_META + '/versions/installer');
    const installer = ((installerList.find((x) => x.stable) || installerList[0]) || {}).version;
    if (!installer) throw new Error('Не удалось определить версию установщика Fabric');
    const srv = await vanillaServerUrl(mc);
    step.set(16, 'Скачивание ядра Minecraft…');
    await dl(srv.url, path.join(dir, 'server.jar'), srv.size, 'Minecraft server.jar');
    step.set(55, 'Скачивание Fabric-загрузчика…');
    const fabricUrl = FABRIC_META + '/versions/loader/' + mc + '/' + spec.loaderVersion + '/' + installer + '/server/jar';
    await dl(fabricUrl, path.join(dir, 'fabric-server-launch.jar'), null, 'Fabric launcher');
    await fsp.writeFile(path.join(dir, 'fabric-server-launcher.properties'), 'serverJar=server.jar\n');
    step.set(88, 'Fabric скачан');
    return;
  }

  if (core === 'forge') {
    const full = mc + '-' + spec.loaderVersion;
    const instUrl = FORGE_MAVEN + '/net/minecraftforge/forge/' + full + '/forge-' + full + '-installer.jar';
    const instPath = path.join(dir, 'forge-installer.jar');
    step.set(6, 'Скачивание установщика Forge…');
    await dl(instUrl, instPath, null, 'Forge installer');
    step.set(30, 'Установка Forge (может занять несколько минут)…');
    const javaPath = await ensureJava(serverJavaMajor(mc),
      (text, percent) => step.set(30 + Math.round((percent || 0) * 0.25), text));
    const r = await runProcess(javaPath, ['-jar', 'forge-installer.jar', '--installServer'], dir,
      (line) => step.set(60, line.slice(0, 90)));
    if (r.code !== 0) {
      const tail = r.out.split(/\r?\n/).filter(Boolean).slice(-3).join(' ').slice(0, 220);
      throw new Error('Установщик Forge завершился с кодом ' + r.code + (tail ? ': ' + tail : ''));
    }
    await fsp.rm(instPath, { force: true }).catch(() => {});
    step.set(88, 'Forge установлен');
    return;
  }

  throw new Error('Неизвестное ядро: ' + core);
}

/** Находит args-файл установленного Forge/NeoForge (для запуска) */
function findForgeArgsFile(dir) {
  const osFile = OS_NAME === 'windows' ? 'win_args.txt' : 'unix_args.txt';
  const bases = [
    path.join(dir, 'libraries', 'net', 'minecraftforge', 'forge'),
    path.join(dir, 'libraries', 'net', 'neoforged', 'neoforge')
  ];
  for (const base of bases) {
    let entries;
    try { entries = fs.readdirSync(base); } catch (_) { continue; }
    for (const v of entries) {
      const f = path.join(base, v, osFile);
      if (fs.existsSync(f)) return f;
    }
  }
  return null;
}

/** Находит универсальный forge-*.jar (старые версии Forge) */
function findForgeJar(dir) {
  try {
    const jars = fs.readdirSync(dir)
      .filter((f) => /^forge-.*\.jar$/i.test(f) && !/installer/i.test(f));
    if (jars.length) return path.join(dir, jars.sort().pop());
  } catch (_) { /* нет папки */ }
  return null;
}

/** Аргументы запуска сервера (относительные пути — cwd = папка сервера) */
function serverArgs(name, s) {
  const dir = servDir(name);
  const st = readSettings();
  // ОЗУ сервера: своё у сервера → настройки «Серверы» → общие настройки памяти
  const memMin = (s && s.memoryMin) || st.servers.memoryMin || st.memory.min;
  const memMax = (s && s.memoryMax) || st.servers.memoryMax || st.memory.max;
  const args = [...splitArgs(st.java.jvmArgs), ...splitArgs(st.servers.jvmArgs),
    '-Xms' + memMin, '-Xmx' + memMax];

  if (s.core === 'forge') {
    const af = findForgeArgsFile(dir);
    if (af) {
      args.push('@' + path.relative(dir, af).replace(/\\/g, '/'));
    } else {
      const fj = findForgeJar(dir);
      args.push('-jar', fj ? path.basename(fj) : 'server.jar');
    }
  } else if (s.core === 'fabric' && fs.existsSync(path.join(dir, 'fabric-server-launch.jar'))) {
    args.push('-jar', 'fabric-server-launch.jar');
  } else {
    args.push('-jar', 'server.jar');
  }

  args.push('nogui');
  return args;
}

/** Готов ли сервер на диске (есть файлы ядра) */
function serverReadyOnDisk(s) {
  const dir = servDir(s.name);
  if (s.core === 'forge') return !!(findForgeArgsFile(dir) || findForgeJar(dir));
  if (s.core === 'fabric') return fs.existsSync(path.join(dir, 'fabric-server-launch.jar'));
  return fs.existsSync(path.join(dir, 'server.jar'));
}

function shellQuote(a) {
  return /[\s"'$`\\]/.test(a) ? "'" + String(a).replace(/'/g, "'\\''") + "'" : a;
}
function batQuote(a) {
  return /[\s"&^|<>]/.test(a) ? '"' + String(a).replace(/"/g, '""') + '"' : a;
}

/** Пишет готовые скрипты запуска start.sh и start.bat */
async function writeServerScripts(name, s, javaPath) {
  const dir = servDir(name);
  const args = serverArgs(name, s);
  const jp = javaPath || 'java';

  const sh = '#!/usr/bin/env bash\n' +
    '# Запуск сервера «' + name + '» (сгенерировано C Minerva Launcher)\n' +
    'cd "$(dirname "$0")"\n' +
    '"' + jp + '" ' + args.map(shellQuote).join(' ') + '\n';
  await fsp.writeFile(path.join(dir, 'start.sh'), sh);
  try { await fsp.chmod(path.join(dir, 'start.sh'), 0o755); } catch (_) { /* windows */ }

  const bat = '@echo off\r\n' +
    'rem Запуск сервера «' + name + '» (сгенерировано C Minerva Launcher)\r\n' +
    'cd /d "%~dp0"\r\n' +
    '"' + jp + '" ' + args.map(batQuote).join(' ') + '\r\n' +
    'pause\r\n';
  await fsp.writeFile(path.join(dir, 'start.bat'), bat);
}

/** Установка сервера: скачивание ядра, eula, properties, скрипты, метаданные */
async function installServer(name, spec) {
  const dir = servDir(name);
  const step = (percent, text) => {
    step.percent = percent;
    updateServer(name, { status: 'downloading', percent, text });
    sendEvent('servers:progress', { name, status: 'downloading', percent, text });
  };
  step.set = step;
  step.percent = 0;

  await fsp.mkdir(dir, { recursive: true });
  try {
    await downloadServerCore(name, spec, step);

    step(90, 'Настройка файлов сервера…');
    await fsp.writeFile(path.join(dir, 'eula.txt'),
      '# Согласие с Minecraft EULA — https://aka.ms/MinecraftEULA\neula=true\n');
    const propPath = path.join(dir, 'server.properties');
    if (!fs.existsSync(propPath)) {
      await fsp.writeFile(propPath, serializeProps(defaultServerProperties(spec.port, spec.motd)));
    }

    const s = readServers().find((x) => x.name === name) || { name, ...spec };
    let javaPath = 'java';
    try {
      javaPath = await ensureJava(serverJavaMajor(spec.version),
        (text, percent) => step(90 + Math.round((percent || 0) * 0.04), text));
    } catch (_) { /* scripts останутся с «java» */ }
    await writeServerScripts(name, s, javaPath);

    for (const d of ['plugins', 'mods', 'config', 'logs']) {
      await fsp.mkdir(path.join(dir, d), { recursive: true }).catch(() => {});
    }

    const info = {
      name,
      core: spec.core,
      version: spec.version,
      loaderVersion: spec.loaderVersion || null,
      port: clampInt(spec.port, 1, 65535, 25565),
      java: serverJavaMajor(spec.version),
      created: new Date().toISOString()
    };
    await fsp.writeFile(path.join(dir, 'instance.json'), JSON.stringify(info, null, 2));

    step(100, 'Готово');
    updateServer(name, { status: 'ready', percent: 100, text: 'Готово' });
    sendEvent('servers:progress', { name, status: 'ready', percent: 100, text: 'Готово' });
  } catch (err) {
    const msg = errText(err);
    updateServer(name, { status: 'error', percent: 0, text: msg });
    sendEvent('servers:progress', { name, status: 'error', percent: 0, text: msg });
    sendEvent('server:log', { name, line: '[ошибка установки] ' + msg });
    throw new Error(msg);
  }
}

/** Создание сервера: валидация, запись в реестр, установка */
async function createServer(spec) {
  const name = cleanServerName(spec.name);
  const core = SERVER_CORES.some((c) => c.id === spec.core) ? spec.core : 'vanilla';
  const version = String(spec.version || '').trim();
  if (!version) throw new Error('Выберите версию Minecraft');

  let loaderVersion = spec.loaderVersion ? String(spec.loaderVersion).trim() : '';
  if ((core === 'fabric' || core === 'forge') && !loaderVersion) {
    const list = await serverLoaderVersions(core, version);
    if (list && list.length) loaderVersion = list[0];
    else throw new Error('Для версии ' + version + ' нет ядра ' + SERVER_CORE_LABELS[core]);
  }

  const existing = readServers().find((s) => s.name.toLowerCase() === name.toLowerCase());
  if (existing && existing.status !== 'error') {
    throw new Error('Сервер «' + existing.name + '» уже существует');
  }
  const dir = servDir(name);
  if (fs.existsSync(dir) && !existing) {
    throw new Error('Папка serv/' + name + ' уже существует');
  }

  const record = existing || {};
  Object.assign(record, {
    name,
    core,
    version,
    loaderVersion: loaderVersion || null,
    port: clampInt(spec.port, 1, 65535, 25565),
    memoryMin: typeof spec.memoryMin === 'string' ? spec.memoryMin.trim().slice(0, 12) : '',
    memoryMax: typeof spec.memoryMax === 'string' ? spec.memoryMax.trim().slice(0, 12) : '',
    status: 'downloading',
    percent: 0,
    text: 'В очереди…',
    created: record.created || new Date().toISOString()
  });

  const list = readServers().filter((s) => s.name.toLowerCase() !== name.toLowerCase());
  list.push(record);
  writeServers(list);

  await installServer(name, {
    core, version,
    loaderVersion: record.loaderVersion,
    port: record.port,
    motd: spec.motd
  });

  return { ok: true, name };
}

// ---------- свойства server.properties ----------
function parseProps(text) {
  const rows = [];
  for (const line of String(text).split(/\r?\n/)) {
    const t = line.trim();
    if (!t || t.startsWith('#')) continue;
    const i = line.indexOf('=');
    if (i < 0) continue;
    rows.push({ key: line.slice(0, i).trim(), value: line.slice(i + 1) });
  }
  return rows;
}

function serializeProps(obj) {
  return Object.keys(obj).map((k) => k + '=' + obj[k]).join('\n') + '\n';
}

// ---------- запуск / остановка сервера ----------
function serverLog(name, line) {
  for (const l of String(line).split(/\r?\n/)) {
    if (l.trim()) sendEvent('server:log', { name, line: l });
  }
}

async function launchServer(name) {
  if (serverProcess) throw new Error('Уже запущен сервер «' + serverRunName + '»');
  if (gameProcess) throw new Error('Сначала закройте запущенную игру');

  const s = readServers().find((x) => x.name === name);
  if (!s) throw new Error('Сервер не найден');
  if (!serverReadyOnDisk(s)) throw new Error('Файлы сервера не найдены — создайте сервер заново');

  const dir = servDir(name);
  sendEvent('server:state', { name, state: 'preparing' });

  try {
    const javaPath = await ensureJava(serverJavaMajor(s.version),
      (text, percent) => sendEvent('servers:progress', { name, status: 'downloading', percent, text }));

    // EULA обязательна для запуска
    const eula = path.join(dir, 'eula.txt');
    let eulaOk = false;
    try { eulaOk = /eula\s*=\s*true/i.test(fs.readFileSync(eula, 'utf8')); } catch (_) {}
    if (!eulaOk) await fsp.writeFile(eula, 'eula=true\n');

    const args = serverArgs(name, s);
    serverLog(name, 'Запуск: ' + path.basename(javaPath) + ' ' + args.join(' '));

    serverRunName = name;
    serverProcess = spawn(javaPath, args, { cwd: dir });

    serverProcess.stdout.on('data', (d) => serverLog(name, d.toString()));
    serverProcess.stderr.on('data', (d) => serverLog(name, d.toString()));
    serverProcess.on('error', (err) => {
      sendEvent('server:state', { name, state: 'error', message: errText(err) });
      serverProcess = null;
      serverRunName = null;
    });
    serverProcess.on('close', (code) => {
      serverLog(name, 'Сервер остановлен (код ' + code + ')');
      sendEvent('server:state', { name, state: code === 0 ? 'stopped' : 'exited', code });
      serverProcess = null;
      serverRunName = null;
    });

    sendEvent('server:state', { name, state: 'running' });
    return { ok: true, name };
  } catch (err) {
    const msg = errText(err);
    sendEvent('server:state', { name, state: 'error', message: msg });
    throw new Error(msg);
  }
}

function stopServer() {
  if (!serverProcess) return { ok: false, error: 'Сервер не запущен' };
  const p = serverProcess;
  try { p.stdin.write('stop\n'); } catch (_) { /* уже закрыт */ }
  setTimeout(() => { try { p.kill('SIGTERM'); } catch (_) {} }, 10000);
  setTimeout(() => { try { p.kill('SIGKILL'); } catch (_) {} }, 20000);
  return { ok: true };
}

function sendServerCommand(name, command) {
  if (!serverProcess || serverRunName !== name) return { ok: false, error: 'Сервер не запущен' };
  const c = String(command || '').trim();
  if (!c) return { ok: false, error: 'Пустая команда' };
  try {
    serverProcess.stdin.write(c + '\n');
    return { ok: true };
  } catch (err) {
    return { ok: false, error: errText(err) };
  }
}

// ============================================================
// IPC: СЕРВЕРЫ
// ============================================================
ipcMain.handle('servers:cores', () => ({ ok: true, cores: SERVER_CORES }));

ipcMain.handle('servers:list', () => {
  try {
    const list = readServers().slice().sort((a, b) => new Date(b.created || 0) - new Date(a.created || 0));

    let changed = false;
    for (const s of list) {
      if (s.status === 'ready' && !serverReadyOnDisk(s)) {
        s.status = 'error';
        s.text = 'файлы сервера не найдены';
        changed = true;
      }
    }
    if (changed) {
      writeServers(readServers().map((x) => {
        const upd = list.find((y) => y.name === x.name);
        return upd ? Object.assign(x, { status: upd.status, text: upd.text }) : x;
      }));
    }

    return { ok: true, servers: list, running: serverRunName };
  } catch (err) {
    return { ok: false, error: errText(err), servers: [] };
  }
});

ipcMain.handle('servers:versions', async (_e, core) => {
  try {
    return { ok: true, versions: await serverVersions(core) };
  } catch (err) {
    return { ok: false, error: errText(err), versions: [] };
  }
});

ipcMain.handle('servers:loaderVersions', async (_e, payload) => {
  try {
    const p = payload || {};
    return { ok: true, versions: await serverLoaderVersions(p.core, p.version) };
  } catch (err) {
    return { ok: false, error: errText(err), versions: [] };
  }
});

ipcMain.handle('servers:create', (_e, payload) => serial(async () => {
  try {
    return await createServer(payload || {});
  } catch (err) {
    return { ok: false, error: errText(err) };
  }
}));

ipcMain.handle('servers:delete', async (_e, name) => {
  try {
    const s = readServers().find((x) => x.name === name);
    if (!s) return { ok: false, error: 'Сервер не найден' };
    if (serverRunName === name) return { ok: false, error: 'Сервер сейчас запущен' };
    await fsp.rm(servDir(name), { recursive: true, force: true });
    writeServers(readServers().filter((x) => x.name !== name));
    return { ok: true };
  } catch (err) {
    return { ok: false, error: errText(err) };
  }
});

ipcMain.handle('servers:start', async (_e, name) => {
  try {
    return await launchServer(name);
  } catch (err) {
    return { ok: false, error: errText(err) };
  }
});

ipcMain.handle('servers:stop', () => {
  try { return stopServer(); } catch (err) { return { ok: false, error: errText(err) }; }
});

ipcMain.handle('servers:command', (_e, payload) => {
  try {
    const p = payload || {};
    return sendServerCommand(p.name, p.command);
  } catch (err) {
    return { ok: false, error: errText(err) };
  }
});

ipcMain.handle('servers:properties', (_e, name) => {
  try {
    const p = path.join(servDir(name), 'server.properties');
    try {
      return { ok: true, rows: parseProps(fs.readFileSync(p, 'utf8')) };
    } catch (_) {
      return { ok: true, rows: [], missing: true };
    }
  } catch (err) {
    return { ok: false, error: errText(err) };
  }
});

ipcMain.handle('servers:saveProperties', (_e, payload) => {
  try {
    const p = payload || {};
    const rows = (p.rows || []).filter((r) => r && String(r.key).trim());
    const text = rows.map((r) => String(r.key).trim() + '=' + String(r.value)).join('\n') + '\n';
    fs.mkdirSync(servDir(p.name), { recursive: true });
    fs.writeFileSync(path.join(servDir(p.name), 'server.properties'), text);
    return { ok: true };
  } catch (err) {
    return { ok: false, error: errText(err) };
  }
});

ipcMain.handle('servers:saveMeta', async (_e, payload) => {
  try {
    const p = payload || {};
    updateServer(p.name, {
      memoryMin: typeof p.memoryMin === 'string' ? p.memoryMin.trim().slice(0, 12) : '',
      memoryMax: typeof p.memoryMax === 'string' ? p.memoryMax.trim().slice(0, 12) : ''
    });
    const s = readServers().find((x) => x.name === p.name);
    if (s) await writeServerScripts(p.name, s);
    return { ok: true };
  } catch (err) {
    return { ok: false, error: errText(err) };
  }
});

ipcMain.handle('servers:folder', async (_e, name) => {
  try {
    const dir = servDir(name);
    fs.mkdirSync(dir, { recursive: true });
    const err = await require('electron').shell.openPath(dir);
    return { ok: !err, error: err || undefined };
  } catch (err) {
    return { ok: false, error: errText(err) };
  }
});

// ============================================================
// IPC: JAVA И ЗАПУСК
// ============================================================
ipcMain.handle('java:ensure', (_e, name) => {
  sendEvent('launch:progress', { build: name, text: 'Проверка Java…', percent: 0 });
  return serial(async () => {
    try {
      const b = readBuilds().find((x) => x.name === name);
      if (!b) throw new Error('Сборка не найдена');

      const vPath = path.join(VER_DIR, name, 'version.json');
      if (!fs.existsSync(vPath)) throw new Error('Сначала скачайте сборку');
      const v = JSON.parse(fs.readFileSync(vPath, 'utf8'));

      const ls = buildLaunchSettings(name, v);
      const javaPath = await ensureJava(ls.major, (text, percent) =>
        sendEvent('launch:progress', { build: name, text, percent }),
        { requireExact: ls.requireExact, preferBundled: ls.preferBundled });

      return { ok: true, java: javaPath, major: ls.major, required: ls.required, source: ls.source };
    } catch (err) {
      return { ok: false, error: err.message };
    }
  });
});

ipcMain.handle('builds:launch', async (_e, name) => {
  try {
    return await launchBuild(name);
  } catch (err) {
    return { ok: false, error: err.message };
  }
});

ipcMain.handle('builds:stop', () => stopGame());

// ============================================================
// СТАРТ
// ============================================================
/** После перезапуска незавершённых загрузок быть не может — помечаем такие сборки как прерванные */
function normalizeBuildsOnStart() {
  try {
    const list = readBuilds();
    let changed = false;
    for (const b of list) {
      if (b.status === 'downloading' || b.status === 'queued') {
        b.status = 'error';
        b.percent = 0;
        b.text = 'загрузка была прервана — нажмите «Повторить»';
        changed = true;
      }
    }
    if (changed) writeBuilds(list);
  } catch (_) { /* не критично */ }
}

app.whenReady().then(() => {
  for (const dir of [VER_DIR, CACHE_DIR, VERSIONS_DIR, LIB_DIR, ASSETS_DIR, JAVA_DIR, SERV_DIR,
                     path.join(CACHE_DIR, 'installers'), path.join(CACHE_DIR, 'modpacks')]) {
    fs.mkdirSync(dir, { recursive: true });
  }

  normalizeBuildsOnStart();
  createWindow();

  app.on('activate', () => {
    if (BrowserWindow.getAllWindows().length === 0) createWindow();
  });
});

// при выходе гасим игру и сервер
app.on('before-quit', () => {
  if (gameProcess) {
    try { gameProcess.kill('SIGTERM'); } catch (_) {}
  }
  if (serverProcess) {
    try { serverProcess.stdin.write('stop\n'); } catch (_) {}
    try { serverProcess.kill('SIGTERM'); } catch (_) {}
  }
});

app.on('window-all-closed', () => {
  if (process.platform !== 'darwin') app.quit();
});
