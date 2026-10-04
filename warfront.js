'use strict';

const canvas = document.getElementById('world');
const ctx = canvas.getContext('2d', { alpha: false });
const mapCanvas = document.createElement('canvas');
const mapCtx = mapCanvas.getContext('2d', { alpha: false });

const GRID_W = 124;
const GRID_H = 78;
const CELL = 5;
mapCanvas.width = GRID_W * CELL;
mapCanvas.height = GRID_H * CELL;

const TERRAIN = { OCEAN: 0, PLAINS: 1, FOREST: 2, MOUNTAIN: 3, DESERT: 4 };
const TERRAIN_COLORS = ['#071a28', '#31453d', '#243d35', '#4a4b46', '#5a4b35'];
const NATION_COLORS = [
  '#d95d5d','#5a86d6','#d5b94f','#6ec090','#ae70cc','#df8757','#61b6c5','#d4699e',
  '#809b4a','#8f72df','#c99557','#4e9e84','#cf6676','#638dc5','#a6a44f','#be7fb8',
  '#7db46d','#d27c47','#68a2a5','#b690db','#c1a05e','#5f88a7','#b77465','#87a655'
];
const PREFIX = ['Val','Nor','Aster','Kor','Bel','Eld','Sar','Thar','Vey','Mar','Ost','Cal','Ryn','Sol','Dra','Ily','Fen','Tor','Kas','Mer','Ard','Vel','Zen','Hal','Or'];
const SUFFIX = ['ia','or','en','ara','stan','os','um','eth','is','a','on','eria','gard','via','esh','yn'];
const BOT_NAMES = ['AtlasAI','Marauder_7','QuietGeneral','MapWatcher','RedSage','BorderScout','CobaltFox','IronArchivist'];

let owner = new Int16Array(GRID_W * GRID_H);
let terrain = new Uint8Array(GRID_W * GRID_H);
let scorch = new Uint8Array(GRID_W * GRID_H);
let nations = new Map();
let wars = new Map();
let alliances = new Set();
let history = [];
let nextNationId = 1;
let selectedNationId = 0;
let secondTargetId = 0;
let paused = false;
let speed = 1;
let tickCount = 0;
let year = 1;
let dirtyMap = true;
let currentScenario = 'Fractured Continents';
let godMode = false;
let godTool = '';
let roomCode = '';
let lobbyBots = [];
let botChat = [];
let audioReady = false;
let musicTimer = null;
let sfxVolume = 100;
let musicVolume = 75;
let chaos = 58;
let revoltRate = 45;
let camera = { x: 0, y: 0, zoom: 1 };
let pointerState = new Map();
let dragMoved = false;
let lastBorders = new Map();
let lastStats = new Map();
let simAccumulator = 0;
let lastFrame = performance.now();

for (let i=0;i<owner.length;i++) owner[i] = -1;

const $ = id => document.getElementById(id);
const pairKey = (a,b) => a < b ? `${a}:${b}` : `${b}:${a}`;
const idx = (x,y) => y * GRID_W + x;
const clamp = (v,a,b) => Math.max(a, Math.min(b, v));
const rand = (a=1,b=0) => Math.random() * (a-b) + b;
const irand = (a,b=0) => Math.floor(rand(a,b));
const choice = arr => arr[Math.floor(Math.random()*arr.length)];
const fmt = n => n >= 1e9 ? `${(n/1e9).toFixed(1)}B` : n >= 1e6 ? `${(n/1e6).toFixed(1)}M` : n >= 1e3 ? `${(n/1e3).toFixed(1)}K` : Math.round(n).toString();

function hashSeed(str){
  let h=2166136261>>>0;
  for(let i=0;i<str.length;i++){h^=str.charCodeAt(i);h=Math.imul(h,16777619)}
  return h>>>0;
}
function seeded(seed){
  let s = seed >>> 0;
  return () => { s += 0x6D2B79F5; let t=s; t=Math.imul(t^t>>>15,t|1); t^=t+Math.imul(t^t>>>7,t|61); return ((t^t>>>14)>>>0)/4294967296; };
}
function nationName(){
  let name = choice(PREFIX)+choice(SUFFIX);
  let used = new Set([...nations.values()].map(n=>n.name));
  if(used.has(name)) name += ` ${irand(9)+2}`;
  return name;
}

function terrainFactor(t){
  if(t===TERRAIN.MOUNTAIN) return 1.45;
  if(t===TERRAIN.FOREST) return 1.18;
  if(t===TERRAIN.DESERT) return 0.92;
  return 1;
}
function landValue(t){
  if(t===TERRAIN.PLAINS) return 1.25;
  if(t===TERRAIN.FOREST) return 1.1;
  if(t===TERRAIN.MOUNTAIN) return .82;
  if(t===TERRAIN.DESERT) return .66;
  return 0;
}
function neighbors(i){
  const x=i%GRID_W,y=Math.floor(i/GRID_W), out=[];
  if(x>0) out.push(i-1); if(x<GRID_W-1) out.push(i+1); if(y>0) out.push(i-GRID_W); if(y<GRID_H-1) out.push(i+GRID_W);
  return out;
}

function makeTerrain(seedText='borderfall', style='continents'){
  const r=seeded(hashSeed(seedText));
  for(let i=0;i<terrain.length;i++){terrain[i]=0; owner[i]=-1; scorch[i]=0;}
  const blobs=[];
  let count=style==='archipelago'?24:style==='pangaea'?9:style==='duel'?10:15;
  for(let b=0;b<count;b++){
    let cx,cy,rx,ry;
    if(style==='pangaea'){
      cx=GRID_W*.5+(r()-.5)*GRID_W*.28; cy=GRID_H*.52+(r()-.5)*GRID_H*.3; rx=15+r()*22; ry=11+r()*18;
    }else if(style==='duel'){
      cx=b<5?GRID_W*.28+(r()-.5)*22:GRID_W*.72+(r()-.5)*22; cy=GRID_H*.5+(r()-.5)*45; rx=10+r()*18; ry=8+r()*15;
    }else{
      cx=10+r()*(GRID_W-20); cy=8+r()*(GRID_H-16); rx=(style==='archipelago'?4:9)+r()*(style==='archipelago'?8:18); ry=(style==='archipelago'?4:7)+r()*(style==='archipelago'?7:14);
    }
    blobs.push({cx,cy,rx,ry,warp:r()*6.28});
  }
  for(let y=0;y<GRID_H;y++) for(let x=0;x<GRID_W;x++){
    let land=false, best=99;
    for(const b of blobs){
      const wx=x+Math.sin(y*.19+b.warp)*2.5, wy=y+Math.cos(x*.15+b.warp)*2;
      const d=((wx-b.cx)/b.rx)**2+((wy-b.cy)/b.ry)**2;
      if(d<1.04){land=true;best=Math.min(best,d)}
    }
    if(land){
      const n=r();
      if(best<.22 && n<.42) terrain[idx(x,y)]=TERRAIN.MOUNTAIN;
      else if(n<.26) terrain[idx(x,y)]=TERRAIN.FOREST;
      else if(n>.93) terrain[idx(x,y)]=TERRAIN.DESERT;
      else terrain[idx(x,y)]=TERRAIN.PLAINS;
    }
  }
  smoothLand(2);
}
function smoothLand(rounds){
  for(let q=0;q<rounds;q++){
    const copy=terrain.slice();
    for(let y=1;y<GRID_H-1;y++) for(let x=1;x<GRID_W-1;x++){
      const i=idx(x,y); let land=0;
      for(let yy=-1;yy<=1;yy++) for(let xx=-1;xx<=1;xx++) if(copy[idx(x+xx,y+yy)]!==TERRAIN.OCEAN) land++;
      if(copy[i]===TERRAIN.OCEAN && land>=6) terrain[i]=TERRAIN.PLAINS;
      if(copy[i]!==TERRAIN.OCEAN && land<=3) terrain[i]=TERRAIN.OCEAN;
    }
  }
}
function validSpawn(i,minDist=12){
  if(terrain[i]===TERRAIN.OCEAN || owner[i]>=0) return false;
  const x=i%GRID_W,y=Math.floor(i/GRID_W);
  for(const n of nations.values()){
    const nx=n.capital%GRID_W,ny=Math.floor(n.capital/GRID_W);
    if(Math.hypot(x-nx,y-ny)<minDist) return false;
  }
  return true;
}
function createNationAt(i, opts={}){
  if(terrain[i]===TERRAIN.OCEAN) return null;
  const id=nextNationId++;
  const nation={
    id,name:opts.name||nationName(),color:opts.color||NATION_COLORS[(id-1)%NATION_COLORS.length],capital:i,
    aggression:opts.aggression??Math.random(),diplomacy:opts.diplomacy??Math.random(),tech:opts.tech??rand(1.35,.7),
    stability:opts.stability??rand(96,62),treasury:opts.treasury??rand(1300,420),army:opts.army??rand(540,190),
    population:0,territory:0,income:0,warCapacity:0,born:year,dead:null,casualties:0,warsWon:0,relations:new Map(),
    adjective:opts.adjective||null
  };
  nations.set(id,nation);
  owner[i]=id;
  // Give a compact starting homeland.
  let frontier=[i], claimed=0, maxClaim=opts.startSize||irand(26,14);
  const seen=new Set([i]);
  while(frontier.length && claimed<maxClaim){
    const cur=frontier.shift();
    for(const nb of neighbors(cur).sort(()=>Math.random()-.5)){
      if(seen.has(nb)){continue} seen.add(nb);
      if(terrain[nb]!==TERRAIN.OCEAN && owner[nb]===-1 && Math.random()<.74){owner[nb]=id;frontier.push(nb);claimed++; if(claimed>=maxClaim)break;}
    }
  }
  for(const other of nations.values()) if(other.id!==id){
    const rel=rand(30,-30); nation.relations.set(other.id,rel); other.relations.set(id,rel);
  }
  dirtyMap=true;
  return nation;
}
function populateNations(count){
  let attempts=0;
  while(nations.size<count && attempts<5000){
    const i=irand(owner.length); attempts++;
    if(validSpawn(i,count>18?8:11)) createNationAt(i);
  }
  rebuildWorldStats(); rebuildBorders();
}
function resetWorld({style='continents',count=16,name='Fractured Continents',seed=Date.now().toString()}={}){
  nations.clear(); wars.clear(); alliances.clear(); history=[]; nextNationId=1; selectedNationId=0; secondTargetId=0; year=1; tickCount=0;
  currentScenario=name; makeTerrain(seed,style); populateNations(count); centerCamera();
  logEvent(`The world of ${name} begins with ${nations.size} nations.`, 'major');
  updateUI(); sfx('start');
}

function rebuildWorldStats(){
  const stats=new Map();
  for(const id of nations.keys()) stats.set(id,{territory:0,value:0});
  for(let i=0;i<owner.length;i++){
    const id=owner[i]; if(id>0 && stats.has(id)){const s=stats.get(id);s.territory++;s.value+=landValue(terrain[i]);}
  }
  lastStats=stats;
  for(const [id,n] of nations){
    const s=stats.get(id)||{territory:0,value:0};
    n.territory=s.territory;
    n.population=Math.max(0,s.value*rand(112000,88000));
    n.income=s.value*(1.2+n.tech*.62)*(0.55+n.stability/120);
    n.warCapacity=(n.army*(.65+n.tech*.5))*(.5+n.stability/150)+n.treasury*.08;
    if(n.territory<=0) eliminateNation(id,'ceased to exist');
  }
}
function rebuildBorders(){
  const borders=new Map(); for(const id of nations.keys()) borders.set(id,[]);
  for(let i=0;i<owner.length;i++){
    const id=owner[i]; if(id<=0 || !borders.has(id)) continue;
    for(const nb of neighbors(i)) if(owner[nb]!==id && terrain[nb]!==TERRAIN.OCEAN){borders.get(id).push(i);break;}
  }
  lastBorders=borders;
}
function borderingNations(id){
  const set=new Set(); const b=lastBorders.get(id)||[];
  for(const cell of b) for(const nb of neighbors(cell)){const oid=owner[nb];if(oid>0&&oid!==id)set.add(oid)}
  return [...set];
}
function areAtWar(a,b){return wars.has(pairKey(a,b));}
function areAllied(a,b){return alliances.has(pairKey(a,b));}
function setRelation(a,b,v){const A=nations.get(a),B=nations.get(b);if(!A||!B)return;A.relations.set(b,clamp(v,-100,100));B.relations.set(a,clamp(v,-100,100));}
function getRelation(a,b){return nations.get(a)?.relations.get(b)??0;}

function declareWar(a,b,forced=false){
  if(a===b||!nations.has(a)||!nations.has(b)||areAtWar(a,b)) return false;
  alliances.delete(pairKey(a,b));
  wars.set(pairKey(a,b),{a,b,start:year,casualtiesA:0,casualtiesB:0,initialA:nations.get(a).territory,initialB:nations.get(b).territory});
  setRelation(a,b,-100);
  logEvent(`${nations.get(a).name} declared war on ${nations.get(b).name}${forced?' by decree':''}.`,'war');
  sfx('war'); botReact('war',nations.get(a),nations.get(b)); return true;
}
function makePeace(a,b,reason='signed a peace treaty'){
  const k=pairKey(a,b); const w=wars.get(k); if(!w)return false;
  wars.delete(k); setRelation(a,b,rand(15,-15));
  const A=nations.get(a),B=nations.get(b); if(A&&B){
    const da=A.territory-w.initialA,db=B.territory-w.initialB;
    if(da>db)A.warsWon++; else if(db>da)B.warsWon++;
    logEvent(`${A.name} and ${B.name} ${reason}.`,'peace'); sfx('peace');
  } return true;
}
function formAlliance(a,b){
  if(a===b||!nations.has(a)||!nations.has(b)||areAtWar(a,b))return false;
  alliances.add(pairKey(a,b));setRelation(a,b,90);
  logEvent(`${nations.get(a).name} and ${nations.get(b).name} formed an alliance.`,'peace');sfx('ally');return true;
}

function economyStep(){
  rebuildWorldStats();
  for(const n of nations.values()){
    const growth=n.income*.036;
    n.treasury+=growth-n.army*.0021;
    const desired=n.territory*(18+n.tech*8)*(1+n.aggression*.7);
    n.army+=clamp(desired-n.army,-n.army*.025,Math.max(1,n.income*.018));
    n.tech=clamp(n.tech+n.income*.0000005+rand(.0005,0),.55,2.7);
    const warPressure=[...wars.values()].filter(w=>w.a===n.id||w.b===n.id).length;
    n.stability+=rand(.12,-.08)-warPressure*.025-(n.treasury<0?.12:0);
    n.stability=clamp(n.stability,0,100);
    if(n.treasury<0){n.army*=.997;n.treasury=Math.max(n.treasury,-1500)}
  }
}
function expansionAndWarStep(){
  if(tickCount%4===0) rebuildBorders();
  for(const n of nations.values()){
    const b=lastBorders.get(n.id)||[]; if(!b.length)continue;
    const tries=clamp(Math.floor(1+n.aggression*2+speed*.25),1,5);
    for(let t=0;t<tries;t++){
      const from=choice(b); if(from==null)continue;
      const candidates=neighbors(from).filter(j=>terrain[j]!==TERRAIN.OCEAN && owner[j]!==n.id);
      if(!candidates.length)continue;
      const to=choice(candidates); const oid=owner[to];
      if(oid===-1){
        const chance=.12+n.aggression*.08+(n.treasury>0?.03:0);
        if(Math.random()<chance){owner[to]=n.id;dirtyMap=true;}
      }else if(oid>0 && areAtWar(n.id,oid) && nations.has(oid)) battleCell(n.id,oid,from,to);
    }
  }
}
function battleCell(attackerId,defenderId,from,to){
  const A=nations.get(attackerId),D=nations.get(defenderId); if(!A||!D)return;
  const war=wars.get(pairKey(attackerId,defenderId)); if(!war)return;
  const attack=(A.warCapacity/Math.max(1,A.territory))*(.8+Math.random()*.55)*(1+A.aggression*.18);
  const defend=(D.warCapacity/Math.max(1,D.territory))*terrainFactor(terrain[to])*(.83+Math.random()*.5);
  const casualties=Math.max(1,Math.floor((attack+defend)*.018));
  A.army=Math.max(0,A.army-casualties*(attack<defend?.72:.38));
  D.army=Math.max(0,D.army-casualties*(attack>defend?.82:.46));
  A.casualties+=casualties*.45;D.casualties+=casualties*.55;
  if(war.a===attackerId){war.casualtiesA+=casualties*.45;war.casualtiesB+=casualties*.55}else{war.casualtiesB+=casualties*.45;war.casualtiesA+=casualties*.55}
  if(attack>defend*.93){owner[to]=attackerId; dirtyMap=true;}
  if(Math.random()<.025) sfx('battle');
}
function diplomacyStep(){
  const ids=[...nations.keys()];
  for(const n of nations.values()){
    for(const oid of borderingNations(n.id)){
      if(!nations.has(oid))continue;
      let rel=getRelation(n.id,oid);
      rel+=rand(2.2,-2.4)+(areAllied(n.id,oid)?.9:0)+(areAtWar(n.id,oid)?-3.4:0);
      setRelation(n.id,oid,rel);
      if(!areAtWar(n.id,oid)&&!areAllied(n.id,oid)){
        const hostility=(-rel/100)+n.aggression*.8+(chaos/100)*.45;
        if(rel<-25 && Math.random()<.007*hostility) declareWar(n.id,oid);
        else if(rel>55 && Math.random()<.0024*(n.diplomacy+.3)) formAlliance(n.id,oid);
      }
    }
  }
  for(const w of [...wars.values()]){
    const A=nations.get(w.a),B=nations.get(w.b); if(!A||!B)continue;
    const duration=year-w.start;
    const exhaustion=(A.stability+B.stability)/2;
    if(duration>2.5 && (exhaustion<42 || Math.random()<.0045*duration)) makePeace(w.a,w.b,'agreed to end their war');
  }
  // Occasionally alliances drag a partner into a border war.
  if(Math.random()<.03 && wars.size){
    const w=choice([...wars.values()]);
    for(const id of ids){
      if(id!==w.a&&areAllied(id,w.a)&&borderingNations(id).includes(w.b)&&!areAtWar(id,w.b)&&Math.random()<.18) declareWar(id,w.b);
    }
  }
}
function revoltStep(){
  if(revoltRate<=0)return;
  for(const n of [...nations.values()]){
    if(n.territory<24)continue;
    const p=((100-n.stability)/100)*(.0022+revoltRate/100*0.003);
    if(n.stability<48 && Math.random()<p){spawnRevolt(n.id);break;}
  }
}
function spawnRevolt(parentId,forced=false){
  const parent=nations.get(parentId); if(!parent||parent.territory<12)return null;
  const cells=[]; for(let i=0;i<owner.length;i++)if(owner[i]===parentId)cells.push(i);
  if(!cells.length)return null;
  let start=choice(cells.filter(i=>i!==parent.capital)); if(start==null)start=choice(cells);
  const rebel=createNationAt(start,{name:`${choice(PREFIX)} Free State`,aggression:rand(.9,.35),stability:rand(82,55),startSize:0});
  if(!rebel)return null;
  const want=Math.floor(parent.territory*rand(.28,.12)); const q=[start], seen=new Set([start]); let got=0;
  while(q.length&&got<want){const cur=q.shift();owner[cur]=rebel.id;got++;for(const nb of neighbors(cur).sort(()=>Math.random()-.5)){if(!seen.has(nb)&&owner[nb]===parentId){seen.add(nb);q.push(nb)}}}
  rebel.capital=start; parent.stability=clamp(parent.stability-10,0,100); rebel.stability=72;
  dirtyMap=true; rebuildWorldStats(); rebuildBorders();
  logEvent(`${rebel.name} rose in revolt against ${parent.name}${forced?' by decree':''}.`,'major');
  declareWar(rebel.id,parent.id,true); sfx('revolt'); botReact('revolt',rebel,parent); return rebel;
}
function eliminateNation(id,reason='collapsed'){
  const n=nations.get(id); if(!n)return;
  n.dead=year;
  for(const k of [...wars.keys()]){const w=wars.get(k);if(w.a===id||w.b===id)wars.delete(k)}
  for(const k of [...alliances])if(k.startsWith(`${id}:`)||k.endsWith(`:${id}`))alliances.delete(k);
  nations.delete(id);
  if(selectedNationId===id){selectedNationId=0;$('inspector').classList.add('hidden')}
  logEvent(`${n.name} ${reason}.`,'fall'); dirtyMap=true; sfx('fall');
}
function collapseNation(id){
  const n=nations.get(id); if(!n)return;
  for(let i=0;i<owner.length;i++)if(owner[i]===id)owner[i]=-1;
  eliminateNation(id,'collapsed into ungoverned territory');
}
function strategicStrike(id){
  const n=nations.get(id); if(!n||n.territory<2)return;
  const cells=[];for(let i=0;i<owner.length;i++)if(owner[i]===id)cells.push(i);const epic=choice(cells);if(epic==null)return;
  const ex=epic%GRID_W,ey=Math.floor(epic/GRID_W);let wiped=0;
  for(let y=Math.max(0,ey-4);y<=Math.min(GRID_H-1,ey+4);y++)for(let x=Math.max(0,ex-4);x<=Math.min(GRID_W-1,ex+4);x++){
    const d=Math.hypot(x-ex,y-ey);const i=idx(x,y);if(d<3.8&&terrain[i]!==TERRAIN.OCEAN&&Math.random()<(1-d/5)){if(owner[i]>0){const hit=nations.get(owner[i]);if(hit){hit.army*=.92;hit.stability-=8;hit.casualties+=rand(90000,20000)}}owner[i]=-1;scorch[i]=1;wiped++;}
  }
  logEvent(`A strategic strike devastated ${n.name}, erasing ${wiped} territorial sectors.`,'major');dirtyMap=true;sfx('nuke');botReact('nuke',n,null);
}
function maybeNaturalEvent(){
  if(Math.random()>.0018)return;
  const living=[...nations.values()]; if(!living.length)return; const n=choice(living);
  const events=[
    [`A financial panic struck ${n.name}.`,()=>{n.treasury*=.72;n.stability-=6}],
    [`A military reform strengthened ${n.name}.`,()=>{n.army*=1.14;n.tech+=.08}],
    [`A harvest boom enriched ${n.name}.`,()=>{n.treasury+=n.income*3;n.stability+=5}],
    [`A leadership crisis shook ${n.name}.`,()=>{n.stability-=12}],
    [`A scientific breakthrough advanced ${n.name}.`,()=>{n.tech+=.16}]
  ];
  const [text,fn]=choice(events);fn();logEvent(text,'major');
}
function simulationTick(){
  tickCount++; year+=.026;
  economyStep(); expansionAndWarStep();
  if(tickCount%10===0)diplomacyStep();
  if(tickCount%18===0)revoltStep();
  if(tickCount%25===0)maybeNaturalEvent();
  if(tickCount%8===0){updateUI();updateInspector()}
  if(nations.size<=1 && nations.size>0 && tickCount%20===0){const w=[...nations.values()][0];logEvent(`${w.name} stands as the sole surviving great power.`,'major');paused=true;$('pauseBtn').textContent='>'}
}

function renderMapTexture(){
  mapCtx.imageSmoothingEnabled=false;
  mapCtx.fillStyle='#06141f';mapCtx.fillRect(0,0,mapCanvas.width,mapCanvas.height);
  for(let y=0;y<GRID_H;y++)for(let x=0;x<GRID_W;x++){
    const i=idx(x,y), t=terrain[i], oid=owner[i];
    let c=TERRAIN_COLORS[t];
    mapCtx.fillStyle=c;mapCtx.fillRect(x*CELL,y*CELL,CELL,CELL);
    if(t!==TERRAIN.OCEAN && oid>0 && nations.has(oid)){
      const n=nations.get(oid);mapCtx.globalAlpha=scorch[i]?.54:.79;mapCtx.fillStyle=n.color;mapCtx.fillRect(x*CELL,y*CELL,CELL,CELL);mapCtx.globalAlpha=1;
    }
    if(scorch[i]){mapCtx.fillStyle='rgba(32,19,18,.55)';mapCtx.fillRect(x*CELL,y*CELL,CELL,CELL)}
  }
  // Borders
  mapCtx.lineWidth=1;mapCtx.strokeStyle='rgba(4,8,11,.88)';mapCtx.beginPath();
  for(let y=0;y<GRID_H;y++)for(let x=0;x<GRID_W;x++){
    const i=idx(x,y),a=owner[i];if(terrain[i]===TERRAIN.OCEAN)continue;
    if(x<GRID_W-1){const b=owner[i+1];if(a!==b&&terrain[i+1]!==TERRAIN.OCEAN){mapCtx.moveTo((x+1)*CELL,y*CELL);mapCtx.lineTo((x+1)*CELL,(y+1)*CELL)}}
    if(y<GRID_H-1){const b=owner[i+GRID_W];if(a!==b&&terrain[i+GRID_W]!==TERRAIN.OCEAN){mapCtx.moveTo(x*CELL,(y+1)*CELL);mapCtx.lineTo((x+1)*CELL,(y+1)*CELL)}}
  } mapCtx.stroke();
  // War borders glow.
  mapCtx.lineWidth=1.3;mapCtx.strokeStyle='rgba(255,221,175,.72)';mapCtx.beginPath();
  for(let y=0;y<GRID_H;y++)for(let x=0;x<GRID_W;x++){
    const i=idx(x,y),a=owner[i];if(a<=0)continue;
    if(x<GRID_W-1){const b=owner[i+1];if(b>0&&a!==b&&areAtWar(a,b)){mapCtx.moveTo((x+1)*CELL,y*CELL);mapCtx.lineTo((x+1)*CELL,(y+1)*CELL)}}
    if(y<GRID_H-1){const b=owner[i+GRID_W];if(b>0&&a!==b&&areAtWar(a,b)){mapCtx.moveTo(x*CELL,(y+1)*CELL);mapCtx.lineTo((x+1)*CELL,(y+1)*CELL)}}
  } mapCtx.stroke();
  // Capitals and selected outline
  for(const n of nations.values()){
    const x=n.capital%GRID_W,y=Math.floor(n.capital/GRID_W); if(owner[n.capital]!==n.id) continue;
    mapCtx.fillStyle='#f6e7b0';mapCtx.fillRect(x*CELL+1.6,y*CELL+1.6,2,2);
    if(n.id===selectedNationId){mapCtx.strokeStyle='#fff4c9';mapCtx.lineWidth=1;mapCtx.strokeRect(x*CELL-.5,y*CELL-.5,CELL+1,CELL+1)}
  }
  dirtyMap=false;
}
function render(){
  const dpr=Math.min(devicePixelRatio||1,2);const rect=canvas.getBoundingClientRect();
  const w=Math.floor(rect.width*dpr),h=Math.floor(rect.height*dpr);
  if(canvas.width!==w||canvas.height!==h){canvas.width=w;canvas.height=h;ctx.setTransform(dpr,0,0,dpr,0,0)}
  const cw=rect.width,ch=rect.height;
  ctx.setTransform(dpr,0,0,dpr,0,0);ctx.fillStyle='#07131d';ctx.fillRect(0,0,cw,ch);
  if(dirtyMap)renderMapTexture();
  const drawW=mapCanvas.width*camera.zoom,drawH=mapCanvas.height*camera.zoom;
  const dx=cw/2-drawW/2+camera.x,dy=ch/2-drawH/2+camera.y;
  ctx.imageSmoothingEnabled=false;ctx.drawImage(mapCanvas,dx,dy,drawW,drawH);
  // Coastline-ish subtle grid
  ctx.save();ctx.globalAlpha=.12;ctx.strokeStyle='#94b0bd';ctx.lineWidth=.5;
  if(camera.zoom>1.6){for(let x=0;x<=GRID_W;x+=4){const sx=dx+x*CELL*camera.zoom;ctx.beginPath();ctx.moveTo(sx,dy);ctx.lineTo(sx,dy+drawH);ctx.stroke()}for(let y=0;y<=GRID_H;y+=4){const sy=dy+y*CELL*camera.zoom;ctx.beginPath();ctx.moveTo(dx,sy);ctx.lineTo(dx+drawW,sy);ctx.stroke()}}
  ctx.restore();
  if($('unitsToggle').checked) drawFrontlineUnits(ctx,dx,dy,camera.zoom);
  if($('fogToggle').checked && selectedNationId) drawFog(ctx,dx,dy,camera.zoom);
}
function drawFrontlineUnits(c,dx,dy,z){
  if(z<.65)return; let shown=0;
  for(const w of wars.values()){
    for(const id of [w.a,w.b]){
      const border=lastBorders.get(id)||[];if(!border.length)continue;
      const sample=border[Math.floor((tickCount*3+id*7)%border.length)]; if(sample==null)continue;
      const x=sample%GRID_W,y=Math.floor(sample/GRID_W),n=nations.get(id);if(!n)continue;
      const sx=dx+(x+.5)*CELL*z,sy=dy+(y+.5)*CELL*z;
      c.fillStyle='#0b0f12';c.beginPath();c.arc(sx,sy,Math.max(2,2.2*z),0,Math.PI*2);c.fill();
      c.fillStyle=n.color;c.beginPath();c.arc(sx,sy,Math.max(1.2,1.35*z),0,Math.PI*2);c.fill();
      if(++shown>60)return;
    }
  }
}
function drawFog(c,dx,dy,z){
  const reveal=new Set([selectedNationId]);for(const id of nations.keys())if(areAllied(selectedNationId,id)||areAtWar(selectedNationId,id))reveal.add(id);
  c.save();c.fillStyle='rgba(1,5,8,.64)';
  for(let y=0;y<GRID_H;y++)for(let x=0;x<GRID_W;x++){const i=idx(x,y),o=owner[i];if(terrain[i]!==TERRAIN.OCEAN&&!reveal.has(o))c.fillRect(dx+x*CELL*z,dy+y*CELL*z,CELL*z+1,CELL*z+1)}
  c.restore();
}
function screenToCell(clientX,clientY){
  const rect=canvas.getBoundingClientRect();const cw=rect.width,ch=rect.height;const drawW=mapCanvas.width*camera.zoom,drawH=mapCanvas.height*camera.zoom;
  const dx=cw/2-drawW/2+camera.x,dy=ch/2-drawH/2+camera.y;
  const mx=(clientX-rect.left-dx)/camera.zoom,my=(clientY-rect.top-dy)/camera.zoom;
  const x=Math.floor(mx/CELL),y=Math.floor(my/CELL);if(x<0||y<0||x>=GRID_W||y>=GRID_H)return -1;return idx(x,y);
}
function centerCamera(){camera.x=0;camera.y=0;const r=canvas.getBoundingClientRect();camera.zoom=clamp(Math.min((r.width-20)/mapCanvas.width,(r.height-20)/mapCanvas.height),.55,1.65)}

function selectCell(i){
  if(i<0)return;const id=owner[i];
  if(godMode&&godTool==='paint'&&selectedNationId>0&&terrain[i]!==TERRAIN.OCEAN){owner[i]=selectedNationId;dirtyMap=true;return}
  if(id>0&&nations.has(id)) selectNation(id); else {selectedNationId=0;$('inspector').classList.add('hidden');}
}
function selectNation(id){
  if(!nations.has(id))return;
  if(godMode&&godTool){handleGodTarget(id);return}
  selectedNationId=id;$('inspector').classList.remove('hidden');updateInspector();dirtyMap=true;sfx('click');
}
function handleGodTarget(id){
  if(godTool==='boost'){const n=nations.get(id);n.treasury+=1500;n.army*=1.25;n.stability=clamp(n.stability+14,0,100);n.tech=clamp(n.tech+.12,0,3);logEvent(`${n.name} received a massive intervention package.`,'major');finishGodTool();sfx('boost');return}
  if(godTool==='collapse'){collapseNation(id);finishGodTool();return}
  if(godTool==='revolt'){spawnRevolt(id,true);finishGodTool();return}
  if(godTool==='nuke'){strategicStrike(id);finishGodTool();return}
  if(godTool==='paint'){selectedNationId=id;$('inspector').classList.remove('hidden');updateInspector();showToast(`Painting territory for ${nations.get(id).name}. Drag on the map.`);return}
  if(!secondTargetId){secondTargetId=id;showToast(`${nations.get(id).name} selected. Choose a second nation.`);return}
  if(secondTargetId===id){showToast('Choose a different nation.');return}
  const a=secondTargetId,b=id;
  if(godTool==='war')declareWar(a,b,true);
  if(godTool==='peace')makePeace(a,b,'were forced into peace');
  if(godTool==='ally')formAlliance(a,b);
  finishGodTool();
}
function finishGodTool(){secondTargetId=0;godTool='';document.querySelectorAll('[data-god]').forEach(b=>b.classList.remove('active'));}

function updateUI(){
  $('yearLabel').textContent=`YEAR ${Math.floor(year)}`;$('nationCount').textContent=`${nations.size} NATIONS`;$('warCount').textContent=`${wars.size} WARS`;
  $('chaosValue').textContent=chaos;$('revoltValue').textContent=revoltRate;
}
function updateInspector(){
  const n=nations.get(selectedNationId);if(!n)return;
  $('nationName').textContent=n.name;$('nationStatus').textContent=areNationAtWar(n.id)?'Nation at war':areNationAllied(n.id)?'Alliance member':'Independent state';$('flag').style.background=`linear-gradient(135deg,${n.color},${shade(n.color,-32)})`;
  $('mTerritory').textContent=n.territory;$('mPop').textContent=fmt(n.population);$('mArmy').textContent=fmt(n.army);$('mMoney').textContent=fmt(n.treasury);$('mTech').textContent=n.tech.toFixed(2);$('mStability').textContent=`${Math.round(n.stability)}%`;
  $('powerText').textContent=fmt(n.warCapacity);$('powerBar').style.width=`${clamp(n.warCapacity/Math.max(1,maxPower())*100,4,100)}%`;$('stabilityText').textContent=`${Math.round(n.stability)}%`;$('stabilityBar').style.width=`${n.stability}%`;
  const rows=[...nations.values()].filter(o=>o.id!==n.id).sort((a,b)=>Math.abs(getRelation(n.id,b.id))-Math.abs(getRelation(n.id,a.id))).slice(0,8);
  $('diplomacyList').innerHTML=rows.map(o=>`<div class="diplo-row"><i class="diplo-dot" style="background:${o.color}"></i><span>${escapeHtml(o.name)}<br><small>${areAtWar(n.id,o.id)?'AT WAR':areAllied(n.id,o.id)?'ALLIED':relationLabel(getRelation(n.id,o.id))}</small></span><b>${Math.round(getRelation(n.id,o.id))}</b></div>`).join('');
}
function maxPower(){let m=1;for(const n of nations.values())m=Math.max(m,n.warCapacity);return m}
function areNationAtWar(id){for(const w of wars.values())if(w.a===id||w.b===id)return true;return false}
function areNationAllied(id){for(const k of alliances){const [a,b]=k.split(':').map(Number);if(a===id||b===id)return true}return false}
function relationLabel(v){return v>55?'FRIENDLY':v>20?'WARM':v>-20?'NEUTRAL':v>-55?'TENSE':'HOSTILE'}
function shade(hex,amt){const n=parseInt(hex.slice(1),16),r=clamp((n>>16)+amt,0,255),g=clamp(((n>>8)&255)+amt,0,255),b=clamp((n&255)+amt,0,255);return `#${((1<<24)+(r<<16)+(g<<8)+b).toString(16).slice(1)}`}
function escapeHtml(s){return String(s).replace(/[&<>"']/g,m=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#039;'}[m]))}

function logEvent(text,type=''){
  history.unshift({year:Math.floor(year),text,type});history=history.slice(0,220);renderHistory();
}
function renderHistory(){
  $('eventLog').innerHTML=history.slice(0,60).map(e=>`<div class="event-line ${e.type}"><time>Y${e.year}</time><span>${escapeHtml(e.text)}</span></div>`).join('');
}
function showToast(text){const t=$('toast');t.textContent=text;t.classList.add('show');clearTimeout(t._timer);t._timer=setTimeout(()=>t.classList.remove('show'),2200)}

function showModal(html){$('modalContent').innerHTML=html;$('modal').classList.remove('hidden');sfx('click')}
function closeModal(){$('modal').classList.add('hidden')}
function scenarioModal(){
  showModal(`<h2>WORLD SCENARIOS</h2><p>Generate a fresh history. Every scenario uses new borders, nation personalities and diplomatic relationships.</p><div class="modal-grid">
    ${scenarioCard('FRACTURED CONTINENTS','16 rival states across several major landmasses.','continents',16)}
    ${scenarioCard('POWDER KEG','24 smaller states. High-contact borders become chaotic fast.','pangaea',24)}
    ${scenarioCard('TWIN EMPIRES','Two major continents with a narrow sea between them.','duel',18)}
    ${scenarioCard('ISLAND WARS','18 island powers fight through fragmented territory.','archipelago',18)}
    ${scenarioCard('TINY WORLD','A faster simulation with only 9 nations.','continents',9)}
    ${scenarioCard('MASSIVE RIVALRY','30 nations and constant diplomatic instability.','pangaea',30)}
  </div>`);
  document.querySelectorAll('[data-scenario]').forEach(b=>b.onclick=()=>{resetWorld({style:b.dataset.style,count:+b.dataset.count,name:b.dataset.scenario,seed:Date.now()+b.dataset.scenario});closeModal()});
}
function scenarioCard(name,desc,style,count){return `<div class="scenario-card"><h3>${name}</h3><p>${desc}</p><button data-scenario="${name}" data-style="${style}" data-count="${count}">GENERATE</button></div>`}
function statsModal(){
  const list=[...nations.values()].sort((a,b)=>b.territory-a.territory);
  const totalCas=[...nations.values()].reduce((s,n)=>s+n.casualties,0)+[...wars.values()].reduce((s,w)=>s+w.casualtiesA+w.casualtiesB,0);
  showModal(`<h2>WORLD STATISTICS</h2><p>${escapeHtml(currentScenario)} at Year ${Math.floor(year)}. ${wars.size} active wars, ${alliances.size} alliances, approximately ${fmt(totalCas)} recorded military casualties.</p><table class="stats-table"><thead><tr><th>RANK</th><th>NATION</th><th>LAND</th><th>ARMY</th><th>TECH</th><th>STABILITY</th><th>WINS</th></tr></thead><tbody>${list.slice(0,18).map((n,i)=>`<tr><td>${i+1}</td><td><span style="color:${n.color}">■</span> ${escapeHtml(n.name)}</td><td>${n.territory}</td><td>${fmt(n.army)}</td><td>${n.tech.toFixed(2)}</td><td>${Math.round(n.stability)}%</td><td>${n.warsWon}</td></tr>`).join('')}</tbody></table>`);
}
function settingsModal(){
  showModal(`<h2>SETTINGS</h2><p>Audio is generated live in the browser. iPhone and iPad require one tap before audio can begin.</p>
  <div class="form-row"><b>MUSIC VOLUME</b><input id="musicVol" type="range" min="0" max="2000" value="${musicVolume}"></div>
  <div class="form-row"><b>SFX VOLUME</b><input id="sfxVol" type="range" min="0" max="2000" value="${sfxVolume}"></div>
  <div class="form-row"><b>MAP ZOOM</b><input id="zoomSet" type="range" min="55" max="400" value="${Math.round(camera.zoom*100)}"></div>
  <p class="hint">Volume sliders intentionally support 0-2000%. Very high values are compressed to reduce clipping.</p>`);
  $('musicVol').oninput=e=>{musicVolume=+e.target.value;savePrefs()};$('sfxVol').oninput=e=>{sfxVolume=+e.target.value;savePrefs()};$('zoomSet').oninput=e=>{camera.zoom=+e.target.value/100};
}
function godModal(){
  showModal(`<h2>GOD MODE</h2><p>Intervene directly in the simulation. Select a tool, close this window, then tap nations on the map.</p><div class="modal-grid">
  <div class="tool-card"><h3>DIPLOMACY</h3><p>Force wars, peace treaties and alliances between any two nations.</p><button data-tool="war">FORCE WAR</button></div>
  <div class="tool-card"><h3>ECONOMIC MIRACLE</h3><p>Give a nation money, stability, technology and military strength.</p><button data-tool="boost">BOOST NATION</button></div>
  <div class="tool-card"><h3>REVOLUTION</h3><p>Split a rebel state out of an existing nation and begin a civil war.</p><button data-tool="revolt">SPAWN REVOLT</button></div>
  <div class="tool-card"><h3>COLLAPSE</h3><p>Dissolve a nation and leave its former territory ungoverned.</p><button data-tool="collapse">COLLAPSE NATION</button></div>
  </div>`);
  document.querySelectorAll('[data-tool]').forEach(b=>b.onclick=()=>{godMode=true;$('godTray').classList.remove('hidden');godTool=b.dataset.tool;secondTargetId=0;closeModal();document.querySelector(`[data-god="${godTool}"]`)?.classList.add('active');showToast('God Mode active. Tap a nation.')});
}
function lobbyModal(){
  const bots=lobbyBots.length?lobbyBots.map(b=>b.name).join(', '):'None';
  showModal(`<h2>SIMULATED MULTIPLAYER</h2><p>GitHub Pages cannot host a real game server by itself, so this mode uses AI observers that react to wars and major events. Private room codes with 5 or more characters intentionally stay empty.</p>
  <div class="room-card"><h3>ROOM CODE</h3><div class="form-row"><b>CODE</b><input id="roomInput" type="text" maxlength="16" value="${escapeHtml(roomCode)}" placeholder="Leave blank for public"></div><button id="joinRoomBtn">ENTER ROOM</button><p id="roomHelp">Current observers: ${escapeHtml(bots)}</p></div>
  <div id="botChat" class="chat">${renderBotChat()}</div>`);
  $('joinRoomBtn').onclick=()=>{roomCode=$('roomInput').value.trim();configureLobby();$('roomHelp').textContent=roomCode.length>=5?'Private room active: no AI observers are allowed in this room.':`Observers: ${lobbyBots.map(b=>b.name).join(', ')||'None'}`;$('botChat').innerHTML=renderBotChat();savePrefs()};
}
function renderBotChat(){return (botChat.length?botChat:[{name:'SYSTEM',text:'Observer chat is quiet.'}]).slice(-35).map(m=>`<div class="chat-line"><b>${escapeHtml(m.name)}:</b> ${escapeHtml(m.text)}</div>`).join('')}
function configureLobby(){
  if(roomCode.length>=5){lobbyBots=[];botChat.push({name:'SYSTEM',text:'Private room locked. No AI observers joined.'});$('roomState').textContent='PRIVATE';$('spectators').textContent='0 AI OBSERVERS';}
  else{const count=irand(6,3);lobbyBots=BOT_NAMES.slice().sort(()=>Math.random()-.5).slice(0,count).map(name=>({name}));$('roomState').textContent=roomCode?'SHORT CODE':'PUBLIC';$('spectators').textContent=`${count} AI OBSERVERS`;if(count)botChat.push({name:choice(lobbyBots).name,text:'Map loaded. I am watching the borders.'})}
}
function botReact(type,a,b){if(!lobbyBots.length||Math.random()>.7)return;const bot=choice(lobbyBots);let text='';if(type==='war')text=`${a.name} versus ${b.name}. That frontline could get ugly.`;if(type==='revolt')text=`That revolt just changed the whole balance of power.`;if(type==='nuke')text=`That strike erased an entire section of the map.`;if(text){botChat.push({name:bot.name,text});botChat=botChat.slice(-60)}}

function serializeWorld(){
  return {
    version:1,grid:[GRID_W,GRID_H],owner:Array.from(owner),terrain:Array.from(terrain),scorch:Array.from(scorch),year,tickCount,nextNationId,currentScenario,
    nations:[...nations.values()].map(n=>({...n,relations:[...n.relations.entries()]})),wars:[...wars.entries()],alliances:[...alliances],history,
    settings:{chaos,revoltRate,fog:$('fogToggle').checked,units:$('unitsToggle').checked}
  };
}
function applyWorld(data){
  if(!data||data.version!==1||!Array.isArray(data.owner)||data.owner.length!==owner.length)throw new Error('Unsupported save file');
  owner=Int16Array.from(data.owner);terrain=Uint8Array.from(data.terrain);scorch=Uint8Array.from(data.scorch||new Array(owner.length).fill(0));year=data.year||1;tickCount=data.tickCount||0;nextNationId=data.nextNationId||1;currentScenario=data.currentScenario||'Imported World';
  nations.clear();for(const raw of data.nations){raw.relations=new Map(raw.relations||[]);nations.set(raw.id,raw)}wars=new Map(data.wars||[]);alliances=new Set(data.alliances||[]);history=data.history||[];
  chaos=data.settings?.chaos??chaos;revoltRate=data.settings?.revoltRate??revoltRate;$('fogToggle').checked=!!data.settings?.fog;$('unitsToggle').checked=data.settings?.units!==false;
  rebuildWorldStats();rebuildBorders();dirtyMap=true;renderHistory();updateUI();selectedNationId=0;$('inspector').classList.add('hidden');showToast('World loaded.');sfx('start');
}
function saveWorld(){localStorage.setItem('borderfall-save',JSON.stringify(serializeWorld()));showToast('World saved to this device.');sfx('save')}
function loadWorld(){const s=localStorage.getItem('borderfall-save');if(!s){showToast('No local save exists yet.');return}try{applyWorld(JSON.parse(s))}catch(e){showToast('Save could not be loaded.')}}
function exportWorld(){const blob=new Blob([JSON.stringify(serializeWorld())],{type:'application/json'});const a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download=`borderfall-year-${Math.floor(year)}.json`;a.click();setTimeout(()=>URL.revokeObjectURL(a.href),1000);showToast('World exported.');sfx('save')}
function importWorld(file){const r=new FileReader();r.onload=()=>{try{applyWorld(JSON.parse(r.result))}catch(e){showToast('Invalid Borderfall world file.')}};r.readAsText(file)}
function savePrefs(){localStorage.setItem('borderfall-prefs',JSON.stringify({musicVolume,sfxVolume,roomCode}))}
function loadPrefs(){try{const p=JSON.parse(localStorage.getItem('borderfall-prefs')||'{}');musicVolume=p.musicVolume??75;sfxVolume=p.sfxVolume??100;roomCode=p.roomCode??''}catch{}}

// Procedural WebAudio: no external files, works offline after first user gesture.
let audioCtx=null,musicGain=null,sfxGain=null;
function audioInit(){
  if(audioReady)return; audioCtx=new (window.AudioContext||window.webkitAudioContext)();musicGain=audioCtx.createGain();sfxGain=audioCtx.createGain();musicGain.connect(audioCtx.destination);sfxGain.connect(audioCtx.destination);audioReady=true;startMusic();
}
function gainFrom(v,base=.045){if(v<=0)return 0;return Math.min(.75,Math.pow(v/100,.72)*base)}
function tone(freq,dur,type='sine',vol=.12,when=0,target=sfxGain){if(!audioReady)return;const o=audioCtx.createOscillator(),g=audioCtx.createGain();o.type=type;o.frequency.value=freq;g.gain.setValueAtTime(0,audioCtx.currentTime+when);g.gain.linearRampToValueAtTime(vol,audioCtx.currentTime+when+.01);g.gain.exponentialRampToValueAtTime(.0001,audioCtx.currentTime+when+dur);o.connect(g);g.connect(target);o.start(audioCtx.currentTime+when);o.stop(audioCtx.currentTime+when+dur+.04)}
function noiseHit(dur=.08,vol=.1,when=0){if(!audioReady)return;const len=Math.floor(audioCtx.sampleRate*dur),buf=audioCtx.createBuffer(1,len,audioCtx.sampleRate),d=buf.getChannelData(0);for(let i=0;i<len;i++)d[i]=(Math.random()*2-1)*(1-i/len);const s=audioCtx.createBufferSource(),g=audioCtx.createGain();s.buffer=buf;g.gain.value=vol;s.connect(g);g.connect(sfxGain);s.start(audioCtx.currentTime+when)}
function sfx(type){if(!audioReady)return;sfxGain.gain.value=gainFrom(sfxVolume,.07);if(type==='click')tone(320,.05,'square',.035);if(type==='war'){noiseHit(.15,.16);tone(92,.25,'sawtooth',.08)}if(type==='battle'){noiseHit(.07,.06);tone(70,.08,'square',.03)}if(type==='peace'){tone(392,.12,'sine',.05);tone(523,.22,'sine',.05,.08)}if(type==='ally'){tone(330,.08,'triangle',.05);tone(440,.14,'triangle',.05,.07)}if(type==='revolt'){tone(150,.18,'sawtooth',.06);tone(130,.22,'sawtooth',.05,.1)}if(type==='fall'){tone(180,.3,'triangle',.06);tone(120,.45,'triangle',.05,.18)}if(type==='nuke'){noiseHit(.55,.22);tone(48,.7,'sawtooth',.11)}if(type==='boost'){tone(260,.08,'sine',.05);tone(390,.14,'sine',.05,.07);tone(520,.2,'sine',.05,.14)}if(type==='save'){tone(420,.06,'sine',.04);tone(630,.12,'sine',.04,.05)}if(type==='start'){tone(110,.5,'triangle',.04);tone(165,.5,'triangle',.035,.12)}}
function startMusic(){if(musicTimer)return;let step=0;musicTimer=setInterval(()=>{if(!audioReady)return;musicGain.gain.value=gainFrom(musicVolume,.033);const scale=[55,65.41,73.42,82.41,98,110,82.41,73.42];const f=scale[step%scale.length];tone(f,.9,'triangle',.06,0,musicGain);if(step%2===0)tone(f*2,.32,'sine',.025,.16,musicGain);if(step%4===0){const old=sfxGain.gain.value;sfxGain.gain.value=gainFrom(musicVolume,.012);noiseHit(.05,.04);sfxGain.gain.value=old}step++;},620)}

document.addEventListener('pointerdown',()=>{audioInit();if(audioCtx?.state==='suspended')audioCtx.resume()},{once:false});

canvas.addEventListener('pointerdown',e=>{canvas.setPointerCapture(e.pointerId);pointerState.set(e.pointerId,{x:e.clientX,y:e.clientY,lastX:e.clientX,lastY:e.clientY,startX:e.clientX,startY:e.clientY});dragMoved=false});
canvas.addEventListener('pointermove',e=>{
  const p=pointerState.get(e.pointerId);if(!p)return;
  const pts=[...pointerState.values()];
  if(pts.length>=2){const a=pts[0],b=pts[1];const prev=Math.hypot(a.lastX-b.lastX,a.lastY-b.lastY)||1;if(pointerState.has(e.pointerId)){p.x=e.clientX;p.y=e.clientY}const nowPts=[...pointerState.values()];const na=nowPts[0],nb=nowPts[1],cur=Math.hypot(na.x-nb.x,na.y-nb.y);camera.zoom=clamp(camera.zoom*(cur/prev),.5,4);dragMoved=true;for(const q of pointerState.values()){q.lastX=q.x;q.lastY=q.y}return}
  const dx=e.clientX-p.lastX,dy=e.clientY-p.lastY;if(Math.hypot(e.clientX-p.startX,e.clientY-p.startY)>4)dragMoved=true;
  if(godMode&&godTool==='paint'&&selectedNationId){const i=screenToCell(e.clientX,e.clientY);if(i>=0&&terrain[i]!==TERRAIN.OCEAN){owner[i]=selectedNationId;dirtyMap=true}}
  else{camera.x+=dx;camera.y+=dy}
  p.lastX=e.clientX;p.lastY=e.clientY;p.x=e.clientX;p.y=e.clientY;
});
canvas.addEventListener('pointerup',e=>{const p=pointerState.get(e.pointerId);if(p&&!dragMoved&&pointerState.size===1)selectCell(screenToCell(e.clientX,e.clientY));pointerState.delete(e.pointerId)});
canvas.addEventListener('pointercancel',e=>pointerState.delete(e.pointerId));
canvas.addEventListener('wheel',e=>{e.preventDefault();camera.zoom=clamp(camera.zoom*(e.deltaY>0?.9:1.1),.5,4)},{passive:false});

$('pauseBtn').onclick=()=>{paused=!paused;$('pauseBtn').textContent=paused?'>':'II';sfx('click')};
document.querySelectorAll('.speed-btn').forEach(b=>b.onclick=()=>{speed=+b.dataset.speed;document.querySelectorAll('.speed-btn').forEach(x=>x.classList.toggle('active',x===b));sfx('click')});
$('newWorldBtn').onclick=()=>resetWorld({style:'continents',count:16,name:'Fractured Continents',seed:Date.now().toString()});
$('presetsBtn').onclick=scenarioModal;$('statsBtn').onclick=statsModal;$('settingsBtn').onclick=settingsModal;$('godBtn').onclick=godModal;
$('saveBtn').onclick=saveWorld;$('loadBtn').onclick=loadWorld;$('exportBtn').onclick=exportWorld;$('importBtn').onclick=()=>$('importFile').click();
$('importFile').onchange=e=>{if(e.target.files[0])importWorld(e.target.files[0]);e.target.value=''};
$('modalClose').onclick=closeModal;$('modal').onclick=e=>{if(e.target===$('modal'))closeModal()};$('closeInspector').onclick=()=>{$('inspector').classList.add('hidden');selectedNationId=0;dirtyMap=true};
$('clearLogBtn').onclick=()=>{history=[];renderHistory()};$('lobbyBtn').onclick=lobbyModal;
$('chaosSlider').oninput=e=>{chaos=+e.target.value;updateUI()};$('revoltSlider').oninput=e=>{revoltRate=+e.target.value;updateUI()};
$('fogToggle').onchange=()=>dirtyMap=true;$('unitsToggle').onchange=()=>dirtyMap=true;
$('godBtn').addEventListener('dblclick',()=>{godMode=!godMode;$('godTray').classList.toggle('hidden',!godMode)});
document.querySelectorAll('[data-god]').forEach(b=>b.onclick=()=>{godMode=true;godTool=b.dataset.god;secondTargetId=0;document.querySelectorAll('[data-god]').forEach(x=>x.classList.toggle('active',x===b));if(godTool==='paint'&&!selectedNationId)showToast('Select a nation first, then choose Paint Borders.');else showToast(godTool==='war'||godTool==='peace'||godTool==='ally'?'Choose the first nation.':'Choose a nation.');});

function gameLoop(now){
  const dt=Math.min(.05,(now-lastFrame)/1000);lastFrame=now;
  if(!paused){simAccumulator+=dt*speed;const step=.13;while(simAccumulator>=step){simulationTick();simAccumulator-=step}}
  render();requestAnimationFrame(gameLoop);
}
window.addEventListener('resize',()=>{centerCamera();dirtyMap=true});
if('serviceWorker' in navigator)window.addEventListener('load',()=>navigator.serviceWorker.register('sw.js').catch(()=>{}));

loadPrefs();configureLobby();resetWorld({style:'continents',count:16,name:'Fractured Continents',seed:Date.now().toString()});updateUI();requestAnimationFrame(gameLoop);
