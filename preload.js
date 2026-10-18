// ============================================================
// preload.js — мост между рендерером и главным процессом
// ============================================================
const { contextBridge, ipcRenderer } = require('electron');

const on = (channel) => (cb) => ipcRenderer.on(channel, (_e, data) => cb(data));

contextBridge.exposeInMainWorld('api', {
  // ---- версии ----
  getVersions: () => ipcRenderer.invoke('versions:list'),

  // ---- загрузчики ----
  loaderVersions: (opts) => ipcRenderer.invoke('loaders:versions', opts),

  // ---- сборки ----
  listBuilds: () => ipcRenderer.invoke('builds:list'),
  addBuild: (opts) => ipcRenderer.invoke('builds:add', opts),
  renameBuild: (opts) => ipcRenderer.invoke('builds:rename', opts),
  deleteBuild: (name) => ipcRenderer.invoke('builds:delete', name),

  // ---- формат .ccli (экспорт/импорт сборки) ----
  ccliInfo: (name) => ipcRenderer.invoke('builds:ccliInfo', name),
  inspectCcli: (text) => ipcRenderer.invoke('builds:inspectCcli', text),
  exportBuild: (opts) => ipcRenderer.invoke('builds:exportCcli', opts),
  importBuild: (opts) => ipcRenderer.invoke('builds:importCcli', opts),

  // ---- моды / ресурсы / шейдеры / модпаки ----
  modsSources: () => ipcRenderer.invoke('mods:sources'),
  modsSearch: (opts) => ipcRenderer.invoke('mods:search', opts),
  modsInstall: (opts) => ipcRenderer.invoke('mods:install', opts),
  modsListInstalled: (opts) => ipcRenderer.invoke('mods:listInstalled', opts),
  modsDeleteInstalled: (opts) => ipcRenderer.invoke('mods:deleteInstalled', opts),
  modsVersions: (opts) => ipcRenderer.invoke('mods:versions', opts),
  modsChangeVersion: (opts) => ipcRenderer.invoke('mods:changeVersion', opts),
  modsDeps: (opts) => ipcRenderer.invoke('mods:deps', opts),
  modpackInstall: (opts) => ipcRenderer.invoke('mods:installModpack', opts),

  // ---- аккаунты ----
  listAccounts: () => ipcRenderer.invoke('accounts:list'),
  addAccount: (opts) => ipcRenderer.invoke('accounts:add', opts),
  elybyLogin: (name, password) => ipcRenderer.invoke('accounts:elybyLogin', { name, password }),
  // скины
  skinsCurrent: () => ipcRenderer.invoke('skins:current'),
  skinsList: () => ipcRenderer.invoke('skins:list'),
  skinsData: (file) => ipcRenderer.invoke('skins:data', file),
  skinsSelect: (opts) => ipcRenderer.invoke('skins:select', opts),
  skinsFetchEly: (nick) => ipcRenderer.invoke('skins:fetchEly', { nick }),
  skinsRefreshAll: () => ipcRenderer.invoke('skins:refreshAll'),
  skinsOpenFolder: () => ipcRenderer.invoke('skins:openFolder'),
  skinsAddFiles: () => ipcRenderer.invoke('skins:addFiles'),
  selectAccount: (name) => ipcRenderer.invoke('accounts:select', name),
  deleteAccount: (name) => ipcRenderer.invoke('accounts:delete', name),

  // ---- Java и запуск ----
  ensureJava: (name) => ipcRenderer.invoke('java:ensure', name),
  launchBuild: (name) => ipcRenderer.invoke('builds:launch', name),
  stopBuild: () => ipcRenderer.invoke('builds:stop'),

  // ---- серверы ----
  serverCores: () => ipcRenderer.invoke('servers:cores'),
  listServers: () => ipcRenderer.invoke('servers:list'),
  serverVersions: (core) => ipcRenderer.invoke('servers:versions', core),
  serverLoaderVersions: (opts) => ipcRenderer.invoke('servers:loaderVersions', opts),
  serverCreate: (opts) => ipcRenderer.invoke('servers:create', opts),
  serverDelete: (name) => ipcRenderer.invoke('servers:delete', name),
  serverStart: (name) => ipcRenderer.invoke('servers:start', name),
  serverStop: () => ipcRenderer.invoke('servers:stop'),
  serverCommand: (opts) => ipcRenderer.invoke('servers:command', opts),
  serverProperties: (name) => ipcRenderer.invoke('servers:properties', name),
  serverSaveProperties: (opts) => ipcRenderer.invoke('servers:saveProperties', opts),
  serverSaveMeta: (opts) => ipcRenderer.invoke('servers:saveMeta', opts),
  serverFolder: (name) => ipcRenderer.invoke('servers:folder', name),

  // ---- настройки ----
  getSettings: () => ipcRenderer.invoke('settings:get'),
  saveSettings: (s) => ipcRenderer.invoke('settings:save', s),
  resetSettings: () => ipcRenderer.invoke('settings:reset'),
  buildInfo: () => ipcRenderer.invoke('settings:buildInfo'),
  pickJava: () => ipcRenderer.invoke('settings:pickJava'),
  openFolder: (which) => ipcRenderer.invoke('settings:openFolder', which),

  // ---- кастомная рамка окна ----
  winMinimize: () => ipcRenderer.send('win:minimize'),
  winClose: () => ipcRenderer.send('win:close'),

  // ---- события ----
  onProgress: on('builds:progress'),        // скачивание сборки
  onLaunchProgress: on('launch:progress'),  // Java/подготовка запуска
  onGameLog: on('game:log'),                // вывод игры
  onGameState: on('game:state'),            // preparing/running/stopped/exited/error
  onModsProgress: on('mods:progress'),      // установка модпака
  onServersProgress: on('servers:progress'),// установка сервера
  onServerLog: on('server:log'),            // вывод сервера
  onServerState: on('server:state')         // preparing/running/stopped/exited/error
});
