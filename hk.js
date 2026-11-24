// ================= Chinese mahjong: Hong Kong Old Style =================
// Rules followed (Hong Kong scoring as described on Wikipedia's "Hong Kong mahjong scoring rules"):
//  - 144 tiles: three suits, four winds, three dragons (4 of each) and 8 bonus tiles (4 flowers, 4 seasons). No jokers.
//  - Bonus tiles are set aside as soon as they arrive and replaced from the back of the wall.
//  - Chow only from the player on your left; pung and kong from anyone; a win beats a pung or kong, which beats a chow;
//    if two players could win on the same discard, the one next in turn wins.
//  - A winning hand is 4 sets and a pair (or Thirteen Orphans, or Seven Pairs if turned on) worth the table minimum
//    (3 faan by default); faan are capped (10 by default). Both are settings.
//  - Points use the "half spicy" table. A discard win is paid by the discarder; a self-drawn win is paid by everyone
//    at half the table each (1.5x in total).
//  - The dealer keeps the deal after winning or a drawn hand; otherwise it passes to the right. The prevailing wind
//    moves on once every player has dealt.
// This file loads before the main script and only defines things; it runs inside the shared table code.

const HK_KINDS=[...['B','C','D'].flatMap(s=>[1,2,3,4,5,6,7,8,9].map(n=>s+n)),'E','S','W','N','R','G','0'];
const HKI=Object.fromEntries(HK_KINDS.map((k,i)=>[k,i]));
// Table rules (Settings > Chinese mahjong rules). Every faan counts toward the minimum, flowers included (New Style).
const HK_DEF={minFaan:3,cap:10,table:'half',discPay:'all',repeat:'always',sevenPairs:false,noLastCalls:false,chowOffer:'useful',callTimer:0,scoring:'new',bonusWin:false,penalties:false,pureGreen:false,selfTriplets:'limit'};
function hkR(){if(typeof NET!=='undefined'&&NET.mode==='client'&&NET.hkRules)return {...HK_DEF,...NET.hkRules};return {...HK_DEF,...((typeof settings!=='undefined'&&settings&&settings.hkRules)||{})}}
let HK_MIN=3,HK_MAX=10;
function hkApplyRules(){const r=hkR();HK_MIN=+r.minFaan;HK_MAX=+r.cap}
const HK_HALF=[1,2,4,8,16,24,32,48,64,96,128,192,256,384];   // half spicy, 0 to 13 faan
const HK_WINDK='ESWN',HK_WINDNAME=['East','South','West','North'];
const HK_FLOWER=['Plum','Orchid','Chrysanthemum','Bamboo'],HK_SEASON=['Spring','Summer','Autumn','Winter'];
const hkIsSuit=i=>i<27,hkIsTerm=i=>i<27&&(i%9===0||i%9===8),hkIsHonor=i=>i>=27,hkIsDragon=i=>i>=31,hkIsWind=i=>i>=27&&i<31;
let hkWind=0,hkRot=0;          // prevailing wind (0 East .. 3 North); dealer changes so far this wind
let hkLast={};                 // how the current player got their latest tile: {self, rep, claimed}
let hkFirst=true;              // no one has claimed or discarded more than once around yet (heavenly / earthly hands)
let hkKeep=false;              // the dealer keeps the deal next hand
let hkRepeat=0;                // hands in a row the same East has kept the deal
let hkMatchOver=false;         // the last hand of the North round has been played

function hkBuildWall(){
  let id=0;const w=[];
  for(const k of HK_KINDS)for(let c=0;c<4;c++)w.push({id:id++,k});
  for(let v=0;v<8;v++)w.push({id:id++,k:'F',v});
  for(let i=w.length-1;i>0;i--){const j=Math.floor(Math.random()*(i+1));[w[i],w[j]]=[w[j],w[i]]}
  return w;
}
const hkSeatWind=i=>(i-dealer+4)%4;      // 0 East .. 3 North
function hkFlowerName(t){return t.v<4?HK_FLOWER[t.v]+' (flower '+(t.v+1)+')':HK_SEASON[t.v-4]+' (season '+(t.v-3)+')'}
function hkCounts(tiles){const c=new Array(34).fill(0);for(const t of tiles)if(t.k!=='F'&&t.k!=='J')c[HKI[t.k]]++;return c}
const hkMeldTiles=p=>p.exp.reduce((s,e)=>s+(e.type==='kong'?3:e.tiles.length),0);   // a kong counts as a set of 3 for hand size

// ---- splitting a hand into sets and a pair ----
function hkDecomp(c,n){
  const out=[];
  for(let p=0;p<34;p++){if(c[p]<2)continue;c[p]-=2;hkSets(c,0,n,[],out,p);c[p]+=2}
  return out;
}
function hkSets(c,i,n,sets,out,pair){
  while(i<34&&!c[i])i++;
  if(i===34){if(sets.length===n)out.push({pair,sets:sets.slice()});return}
  if(sets.length>=n)return;
  if(c[i]>=3){c[i]-=3;sets.push({t:'pung',i});hkSets(c,i,n,sets,out,pair);sets.pop();c[i]+=3}
  if(i<27&&i%9<=6&&c[i+1]&&c[i+2]){c[i]--;c[i+1]--;c[i+2]--;sets.push({t:'chow',i});hkSets(c,i,n,sets,out,pair);sets.pop();c[i]++;c[i+1]++;c[i+2]++}
}
// shanten: how many tiles from ready (0 = ready, -1 = complete)
function hkShanten(c,m){
  const need=4-m;let best=99;
  const rec=(i,sets,parts,pair)=>{
    while(i<34&&!c[i])i++;
    if(i>=34){const s=Math.min(sets,need),pr=Math.min(parts,need-s);const v=2*(need-s)-pr-(pair?1:0);if(v<best)best=v;return}
    if(c[i]>=3){c[i]-=3;rec(i,sets+1,parts,pair);c[i]+=3}
    if(i<27&&i%9<=6&&c[i+1]&&c[i+2]){c[i]--;c[i+1]--;c[i+2]--;rec(i,sets+1,parts,pair);c[i]++;c[i+1]++;c[i+2]++}
    if(c[i]>=2){c[i]-=2;if(!pair)rec(i,sets,parts,true);rec(i,sets,parts+1,pair);c[i]+=2}
    if(i<27&&i%9<=7&&c[i+1]){c[i]--;c[i+1]--;rec(i,sets,parts+1,pair);c[i]++;c[i+1]++}
    if(i<27&&i%9<=6&&c[i+2]){c[i]--;c[i+2]--;rec(i,sets,parts+1,pair);c[i]++;c[i+2]++}
    c[i]--;rec(i+1,sets,parts,pair);c[i]++;
  };
  rec(0,0,0,false);
  if(m===0){   // Thirteen Orphans
    const O=[0,8,9,17,18,26,27,28,29,30,31,32,33];let have=0,dup=false;for(const i of O){if(c[i])have++;if(c[i]>1)dup=true}
    best=Math.min(best,13-have-(dup?1:0));
  }
  return best;
}

// ---- faan ----
// ctx: {self, rob, rep, last, heaven, earth, win:kind index of the winning tile}
function hkEval(seat,hand,ctx={}){
  const p=players[seat],melds=p.exp,n=4-melds.length;
  if(hand.length+3*melds.length!==14)return null;
  const c=hkCounts(hand);let best=null;
  const consider=r=>{if(r&&(!best||r.faan>best.faan))best=r};
  if(!melds.length){
    const O=[0,8,9,17,18,26,27,28,29,30,31,32,33];
    if(O.every(i=>c[i]>=1)&&O.reduce((s,i)=>s+c[i],0)===14)consider(hkLimit(seat,'Thirteen Orphans',13,ctx));
  }
  if(!melds.length&&hkR().sevenPairs&&c.filter(x=>x===2).length===7&&c.every(x=>x===0||x===2))consider(hkSevenPairs(seat,c,ctx));
  for(const d of hkDecomp(c,n))consider(hkScore(seat,d,c,ctx));
  return best;
}
// bonus-tile faan: none at all, your own flower and season, or a full set of four
function hkFlowerItems(seat){
  const it=[],fl=players[seat].flowers||[],sx=hkSeatWind(seat),fv=new Set(fl.map(t=>t.v));
  if(!fl.length)it.push(['No flowers or seasons',1]);
  const old=hkR().scoring==='old';
  if([0,1,2,3].every(v=>fv.has(v)))it.push(['All four flowers',2]);if(fv.has(sx)&&(old||![0,1,2,3].every(v=>fv.has(v))))it.push(['Own flower',1]);
  if([4,5,6,7].every(v=>fv.has(v)))it.push(['All four seasons',2]);if(fv.has(4+sx)&&(old||![4,5,6,7].every(v=>fv.has(v))))it.push(['Own season',1]);
  return it;
}
const HK_BONUS_ITEMS=['No flowers or seasons','Own flower','Own season','All four flowers','All four seasons'];
// is this hand worth enough to win? (Old Style leaves flower faan out of the minimum)
function hkEnough(r){if(!r)return false;let f=r.faan;if(hkR().scoring==='old')f-=r.items.filter(x=>HK_BONUS_ITEMS.includes(x[0])).reduce((a,x)=>a+x[1],0);return f>=HK_MIN}
// Seven Pairs: always concealed, so it never takes the concealed-hand faan
function hkSevenPairs(seat,c,ctx){
  const ks=[];c.forEach((x,i)=>{if(x===2)ks.push(i)});
  const suits=new Set(ks.filter(hkIsSuit).map(i=>Math.floor(i/9))),honors=ks.some(hkIsHonor);
  if(!suits.size)return hkLimit(seat,'All honors',10,ctx);
  if(ctx.heaven||ctx.earth)return hkLimit(seat,ctx.heaven?'Heavenly Hand':'Earthly Hand',0,ctx);
  const it=[['Seven pairs',4]];
  if(suits.size===1)it.push(honors?['Mixed one suit',3]:['All one suit',7]);
  it.push(...hkFlowerItems(seat),...hkCond(seat,ctx,false));
  const raw=it.reduce((s,x)=>s+x[1],0);
  return {faan:Math.min(HK_MAX,raw),raw,items:it,limit:false};
}
function hkCond(seat,ctx,concealed){
  const it=[];
  if(ctx.heaven)it.push(['Heavenly Hand',13]);
  if(ctx.earth)it.push(['Earthly Hand',13]);
  if(ctx.self)it.push(['Self-drawn',1]);
  if(concealed)it.push(['Concealed hand',1]);
  if(ctx.rob)it.push(['Robbing the kong',1]);
  if(ctx.last)it.push([ctx.self?'Last tile from the wall':'Last discard',1]);
  if(ctx.rep>=2)it.push(['Win on a double-kong replacement',8]);else if(ctx.rep)it.push(['Win on a kong replacement',1]);
  return it;
}
function hkLimit(seat,name,val,ctx){
  // limit hands score the hand and how it was won; winds, dragons and flowers add nothing
  const items=[...(val?[[name,val]]:[]),...hkCond(seat,ctx,false)];
  const raw=items.reduce((s,x)=>s+x[1],0);
  return {faan:Math.min(HK_MAX,raw),raw,items,limit:true};
}
function hkScore(seat,d,c,ctx){
  const p=players[seat];
  const sets=[...p.exp.map(e=>({t:e.type==='chow'?'chow':'pung',i:HKI[e.k],open:!e.conc,kong:e.type==='kong'})),
              ...d.sets.map(s=>({t:s.t,i:s.i,open:false,kong:false}))];
  // a pung finished by someone else's discard counts as open (unless the discard finished the pair)
  if(!ctx.self&&ctx.win!=null&&d.pair!==ctx.win){const s=sets.find(x=>!x.open&&x.t==='pung'&&x.i===ctx.win&&!p.exp.some(e=>HKI[e.k]===x.i));if(s)s.open=true}
  const pair=d.pair,all=[...sets.map(s=>s.i),pair];
  const suits=new Set(all.filter(hkIsSuit).map(i=>Math.floor(i/9)));
  const honors=all.some(hkIsHonor);
  const pungs=sets.filter(s=>s.t==='pung'),chows=sets.filter(s=>s.t==='chow');
  const concealedHand=p.exp.every(e=>e.conc);
  const sw=27+hkSeatWind(seat),pw=27+hkWind;
  const dragP=pungs.filter(s=>hkIsDragon(s.i)).length,windP=pungs.filter(s=>hkIsWind(s.i)).length;
  // limit hands
  const lim=[];
  if(!suits.size)lim.push(['All honors',10]);
  if(hkR().selfTriplets!=='normal'&&!chows.length&&pungs.every(s=>!s.open)&&!(ctx.win!=null&&!ctx.self&&d.pair!==ctx.win))lim.push(['Self triplets',10]);
  if(hkR().pureGreen){const G=new Set([1,2,3,5,7,32]);const tl=[d.pair,...sets.flatMap(x=>x.t==='chow'?[x.i,x.i+1,x.i+2]:[x.i])];if(tl.every(x=>G.has(x)))lim.push(['Pure Green',13])}
  if(!chows.length&&!honors&&all.every(hkIsTerm))lim.push(['All terminals',10]);
  if(windP===4)lim.push(['Great Four Winds',13]);
  if(sets.filter(s=>s.kong).length===4)lim.push(['Four kongs',13]);
  if(!p.exp.length&&suits.size===1&&!honors){const s=[...suits][0]*9,base=[3,1,1,1,1,1,1,1,3];let extra=0,ok=true;
    for(let k=0;k<9;k++){const x=c[s+k]-base[k];if(x<0)ok=false;extra+=Math.max(0,x)}if(ok&&extra===1)lim.push(['Nine Gates',10])}
  if(ctx.heaven||ctx.earth)lim.push(['(limit)',0]);
  if(lim.length){const top=lim.filter(x=>x[1]>0).sort((a,b)=>b[1]-a[1])[0];
    if(top)return hkLimit(seat,top[0],top[1],ctx);
    return hkLimit(seat,ctx.heaven?'Heavenly Hand':'Earthly Hand',0,{...ctx});}
  const it=[];
  if(!pungs.length)it.push(['All chows',1]);
  if(!chows.length)it.push(['All pungs',3]);
  if(suits.size===1)it.push(honors?['Mixed one suit',3]:['All one suit',7]);
  if(!chows.length&&honors&&suits.size&&all.every(i=>hkIsHonor(i)||hkIsTerm(i)))it.push(['Mixed terminals and honors',1]);
  if(dragP===3)it.push(['Great Three Dragons',8]);
  else if(dragP===2&&hkIsDragon(pair))it.push(['Small Three Dragons',5]);
  else if(dragP)it.push([dragP===1?'Dragon pung':'Dragon pungs',dragP]);
  if(windP===3&&hkIsWind(pair))it.push(['Small Four Winds',6]);
  if(pungs.some(s=>s.i===sw))it.push(['Seat wind pung',1]);
  if(pungs.some(s=>s.i===pw))it.push(['Prevailing wind pung',1]);
  it.push(...hkFlowerItems(seat));
  it.push(...hkCond(seat,ctx,concealedHand));
  const raw=it.reduce((s,x)=>s+x[1],0);
  return {faan:Math.min(HK_MAX,raw),raw,items:it,limit:false};
}
const hkPoints=f=>{f=Math.min(HK_MAX,Math.max(0,f));return hkR().table==='full'?Math.pow(2,f):HK_HALF[f]};

// ---- dealing and turns ----
function hkNewGame(){
  gid++;closeModal();Sound.init();undoStack=[];homeOpen=false;godNext={};godDraw={};godDrawFor=null;
  wall=hkBuildWall();discards=[];logs=[];logVer++;sel=new Set();selected=null;callState=null;newIds=new Set();flyQueue=[];
  hkApplyRules();
  if(hkMatchOver){hkMatchOver=false;pendingStart=true;scores=[0,0,0,0];shown=[0,0,0,0];hkKeep=false;hkHistory=[]}
  if(pendingStart){dealer=(4-settings.startWind)%4;pendingStart=false;hkWind=0;hkRot=0;hkRepeat=0}
  else if(!hkKeep){dealer=(dealer+1)%4;hkRot++;if(hkRot%4===0)hkWind=Math.min(3,hkWind+1)}
  hkKeep=false;
  dead=[false,false,false,false];building=null;turnSrc=null;hkLast={};hkFirst=true;
  players=[0,1,2,3].map(()=>({hand:[],exp:[],flowers:[]}));phase='shuffle';turn=0;step='discard';hkSaveProgress();
  log(`Hong Kong mahjong. ${HK_WINDNAME[hkWind]} round. Washing the tiles…`);
  render();Sound.wash();
  later(hkDeal,REDUCED?60:1550);
}
function hkTakeFlowers(i,quiet){
  const p=players[i];let got=0;
  for(let guard=0;guard<12;guard++){
    const f=p.hand.filter(t=>t.k==='F');if(!f.length)break;
    for(const t of f){p.hand.splice(p.hand.indexOf(t),1);p.flowers.push(t);got++;
      if(!quiet)log(`${NAMES[i]} set aside ${hkFlowerName(t)}.`);
      if(!wall.length)return got;const r=wall.shift();p.hand.push(r);if(i===0)newIds.add(r.id)}
  }
  return got;
}
function hkDeal(){hkShortWarned=false;
  for(let r=0;r<13;r++)for(let i=0;i<4;i++)players[(dealer+i)%4].hand.push(wall.pop());
  players[dealer].hand.push(wall.pop());
  for(let x=0;x<4;x++)hkTakeFlowers((dealer+x)%4,true);
  players.forEach(p=>sortHand(p.hand));
  phase='play';turn=dealer;step='discard';hkLast={self:true,deal:true};
  const fl=players.map((p,i)=>p.flowers.length?`${NAMES[i]} ${p.flowers.length}`:'').filter(Boolean);
  log(`Fresh deal. ${dealer===0?"You're East and throw first.":`${NAMES[dealer]} is East and throws first. You're ${windOf(0)}.`}${fl.length?' Bonus tiles set aside: '+fl.join(', ')+'.':''}`);
  dealAnim=true;render();for(let i=0;i<14;i++)later(()=>Sound.tap(),120+i*45);
  later(()=>toast(dealer===0?"You're East":`${NAMES[dealer]} is East · you're ${windOf(0)}`),700);
  // a deal with 7 or more flowers and seasons wins at once (house rule)
  for(let x=0;x<4;x++){const q=(dealer+x)%4;if(hkBonusCheck(q))return}
  if(!HUMAN[dealer])later(()=>hkBotAct(dealer),SPEED+600);
}
function hkStartTurn(i){
  if(phase!=='play')return;
  if(!wall.length){hkDrawGame();return}
  turnSrc=null;callState=null;
  const p=players[i];let t=godPull(i)||wall.pop();
  while(t&&t.k==='F'){p.flowers.push(t);log(`${NAMES[i]} drew ${hkFlowerName(t)} and takes a replacement.`);if(i===0)toast(HK_FLOWER[t.v]||HK_SEASON[t.v-4]);
    if(hkBonusCheck(i))return;
    if(!wall.length){hkDrawGame();return}t=wall.shift()}
  p.hand.push(t);if(!HUMAN[i])sortHand(p.hand);turn=i;step='discard';hkLast={self:true,rep:0};
  if(i===0){newIds=new Set([t.id]);selected=null;log(`You drew ${tname(t.k)}.`);queueFly(t,rectOf('#wallStack'),0,460);render();Sound.tap()}
  else if(HUMAN[i])render();   // another person's turn: wait for their move
  else{render();later(()=>hkBotAct(i),SPEED)}
}
// house rule: collect 7 flowers and seasons and you win at once (3 faan); all 8 is a limit win
function hkBonusCheck(i){if(!hkR().bonusWin||phase!=='play')return false;const n=(players[i].flowers||[]).length;if(n<7)return false;
  const raw=n>=8?13:3,r={faan:Math.min(HK_MAX,raw),raw,items:[[n>=8?'All eight flowers and seasons':'Seven flowers and seasons',raw]],limit:n>=8,bonus:true};
  log(`${NAMES[i]} collected ${n} flowers and seasons!`);hkSettle(i,null,r);return true}
function hkReplacement(i){
  const p=players[i];const chain=(hkLast.rep||0)+1;
  for(let g=0;g<12;g++){
    if(!wall.length){hkDrawGame();return false}
    const t=wall.shift();
    if(t.k==='F'){p.flowers.push(t);log(`${NAMES[i]} set aside ${hkFlowerName(t)}.`);if(hkBonusCheck(i))return false;continue}
    p.hand.push(t);if(!HUMAN[i])sortHand(p.hand);if(i===0)newIds=new Set([t.id]);hkLast={self:true,rep:chain};return true;
  }
  return false;
}
function hkCtxSelf(i){return {self:true,rep:hkLast.rep||0,last:!wall.length,heaven:hkFirst&&i===dealer&&!discards.length&&!!hkLast.deal}}
function hkSelfWin(i){const p=players[i];if(hkLast.claimed)return null;const r=hkEval(i,p.hand,hkCtxSelf(i));return r&&hkEnough(r)?r:null}
function hkKongOptions(i){
  const p=players[i];if(hkLast.claimed||!wall.length)return[];
  const c=hkCounts(p.hand),out=[];
  HK_KINDS.forEach((k,x)=>{if(c[x]===4)out.push({kind:'conc',k})});
  for(const e of p.exp)if(e.type==='pung'&&p.hand.some(t=>t.k===e.k))out.push({kind:'add',k:e.k});
  return out;
}
// concealed kong, or adding your own drawn tile to an exposed pung (which others may rob)
function hkDoKong(i,o){
  const p=players[i];
  if(o.kind==='conc'){
    const tiles=p.hand.filter(t=>t.k===o.k).slice(0,4);tiles.forEach(t=>p.hand.splice(p.hand.indexOf(t),1));
    p.exp.push({type:'kong',k:o.k,tiles,n:4,conc:true});
    log(`${NAMES[i]} declared a concealed kong.`);toastAll(v=>`${nameV(i,v)}: Kong!`);Sound.chime();
    hkFirst=false;if(hkReplacement(i))hkAfterDraw(i);return;
  }
  const t=p.hand.find(x=>x.k===o.k);if(!t)return;
  // anyone who can win on this tile may rob the kong
  const order=[1,2,3].map(d=>(i+d)%4);
  for(const j of order){
    const r=hkEval(j,[...players[j].hand,t],{rob:true,win:HKI[t.k],last:!wall.length});
    if(!r||!hkEnough(r))continue;
    if(HUMAN[j]){const o={win:r.faan,pung:false,kong:false,chows:[]};const cs={hk:true,rob:{j:i,tid:t.id,who:j},i,t,offers:{[j]:o},choices:{},o:j===0?o:null};callState=cs;render();
      if(MP()){cs.deadline=Date.now()+CALL_MS;later(()=>{if(callState===cs)hkAnswerSeat(j,'pass')},CALL_MS)}return}
    if(!godPow('noWin')){p.hand.splice(p.hand.indexOf(t),1);players[j].hand.push(t);log(`${NAMES[j]} robbed ${NAMES[i]}'s kong!`);hkWin(j,i,{rob:true,win:HKI[t.k],last:!wall.length});return}
  }
  hkFinishAddKong(i,t);
}
function hkFinishAddKong(i,t){
  const p=players[i];const e=p.exp.find(x=>x.type==='pung'&&x.k===t.k);if(!e)return;
  p.hand.splice(p.hand.indexOf(t),1);e.tiles.push(t);e.type='kong';e.n=4;
  log(`${NAMES[i]} added a fourth ${tname(t.k)} to make a kong.`);toastAll(v=>`${nameV(i,v)}: Kong!`);Sound.chime();
  hkFirst=false;if(hkReplacement(i))hkAfterDraw(i);
}
function hkAfterDraw(i){if(phase!=='play')return;render();if(!HUMAN[i])later(()=>hkBotAct(i),SPEED)}

// ---- computer players ----
function hkPlan(i){
  const p=players[i];const all=[...p.hand,...p.exp.flatMap(e=>e.tiles)].filter(t=>t.k!=='F');
  const sc=[0,0,0];let hon=0;for(const t of all){const x=HKI[t.k];if(x<27)sc[Math.floor(x/9)]++;else hon++}
  const s=sc.indexOf(Math.max(...sc));const offOpen=p.exp.some(e=>HKI[e.k]<27&&Math.floor(HKI[e.k]/9)!==s);
  return {suit:(sc[s]+hon>=9&&!offOpen)?s:-1};
}
function hkValuable(i,x){return hkIsDragon(x)||x===27+hkSeatWind(i)||x===27+hkWind}
function hkDiscardScore(i,c,m,x,plan){
  c[x]--;let s=hkShanten(c,m)*10;c[x]++;
  if(plan.suit>=0){if(x<27&&Math.floor(x/9)!==plan.suit)s-=4;else if(x<27)s+=3}
  if(hkValuable(i,x)&&c[x]>=2)s+=5;
  if(hkIsHonor(x)&&c[x]===1&&!hkValuable(i,x))s-=1;
  return s;
}
function hkChooseDiscard(i){
  const p=players[i],lv=botLevel(i);const c=hkCounts(p.hand),m=p.exp.length,plan=hkPlan(i);
  if(godOn()&&godNext[i]!=null){const f=p.hand.find(t=>t.id===godNext[i]);delete godNext[i];if(f)return f}
  if(lv===0&&Math.random()<.3)return p.hand[Math.floor(Math.random()*p.hand.length)];
  let best=null,bs=Infinity;
  for(let x=0;x<34;x++){if(!c[x])continue;let s=hkDiscardScore(i,c,m,x,plan);
    if(lv===2){c[x]--;const sh=hkShanten(c,m);let uk=0;for(let y=0;y<34;y++){if(c[y]>=4)continue;c[y]++;if(hkShanten(c,m)<sh)uk+=4-c[y]+1;c[y]--}c[x]++;s-=uk*.05}
    s+=Math.random()*.2;if(s<bs){bs=s;best=x}}
  return p.hand.find(t=>t.k===HK_KINDS[best])||p.hand[0];
}
function hkBotAct(i){
  if(phase!=='play'||turn!==i||step!=='discard'||callState||HUMAN[i])return;
  const p=players[i];
  if(!godPow('noWin')){const w=hkSelfWin(i);if(w){hkWin(i,null,hkCtxSelf(i));return}}
  for(const o of hkKongOptions(i)){if(o.kind==='add'||botLevel(i)>0||Math.random()<.5){hkDoKong(i,o);return}}
  const t=hkChooseDiscard(i);hkFirst=hkFirst&&i!==(dealer+3)%4;hkLast={};
  discard(i,t);
}
function hkBotClaim(j,t,from){
  if(godPow('noCall'))return null;
  const p=players[j],x=HKI[t.k],c=hkCounts(p.hand),m=p.exp.length,lv=botLevel(j);
  if(lv===0&&Math.random()<.5)return null;
  const sh=hkShanten(c,m),plan=hkPlan(j);
  const fits=x>=27||plan.suit<0||Math.floor(x/9)===plan.suit;
  if(c[x]>=2&&fits){
    c[x]-=2;const after=hkShanten(c,m+1);c[x]+=2;
    if(hkValuable(j,x)||(after<sh&&(plan.suit>=0||p.exp.some(e=>hkValuable(j,HKI[e.k]))||c[x]>=3)))return {t:c[x]>=3&&wall.length?'kong':'pung'};
  }
  if(j===(from+1)%4&&x<27&&plan.suit===Math.floor(x/9)){
    for(const s of hkChowSets(c,x)){s.forEach(y=>c[y]--);const after=hkShanten(c,m+1);s.forEach(y=>c[y]++);if(after<sh)return {t:'chow',s}}
  }
  return null;
}
function hkChowSets(c,x){const out=[];if(x>=27)return out;const r=x%9;
  for(const st of [x-2,x-1,x]){if(st<0||Math.floor(st/9)!==Math.floor(x/9)||st%9>6)continue;const need=[st,st+1,st+2].filter(y=>y!==x);
    if(need.every(y=>c[y]>0))out.push(need)}
  return out}

// ---- discards and claims ----
function hkResolve(i,t){
  if(phase!=='play')return;
  const order=[1,2,3].map(d=>(i+d)%4),pos=j=>order.indexOf(j);
  const ctxFor=j=>({win:HKI[t.k],last:!wall.length,earth:hkFirst&&i===dealer&&discards.length===1&&j!==dealer});
  let botWin=null,botPung=null,botChow=null;const noCalls=hkR().noLastCalls&&!wall.length;
  if(!godPow('noWin'))for(const j of order){if(HUMAN[j])continue;const r=hkEval(j,[...players[j].hand,t],ctxFor(j));if(r&&hkEnough(r)){botWin={j};break}}
  if(!noCalls)for(const j of order){if(HUMAN[j])continue;const cl=hkBotClaim(j,t,i);if(!cl)continue;
    if(cl.t==='chow'){if(!botChow)botChow={j,s:cl.s}}else if(!botPung)botPung={j,t:cl.t}}
  const offers={};
  for(const j of order){if(!HUMAN[j])continue;const p=players[j],c=hkCounts(p.hand),x=HKI[t.k];const r=hkEval(j,[...p.hand,t],ctxFor(j));
    const o={win:r&&hkEnough(r)&&!(botWin&&pos(botWin.j)<pos(j))?r.faan:0,
       winShort:r&&!hkEnough(r)?r.faan:null,
       pung:c[x]>=2&&!botWin&&!noCalls,kong:c[x]>=3&&!botWin&&wall.length>0&&!noCalls,
       chows:(j===(i+1)%4&&!botWin&&!botPung&&!noCalls&&hkR().chowOffer!=='never')?hkChowSets(c,x).filter(s=>{if(hkR().chowOffer==='all')return true;
         // helpful: it brings you closer to a ready hand
         const m=p.exp.length,sh=hkShanten(c,m);s.forEach(y=>c[y]--);const a=hkShanten(c,m+1);s.forEach(y=>c[y]++);return a<sh}):[]};
    if(j===0&&!o.win&&o.winShort!=null&&!botWin&&!hkShortWarned){hkShortWarned=true;toast(`That ${tname(t.k)} would finish your hand, but only for ${o.winShort} faan (you need ${HK_MIN})`)}
    if(o.win||o.pung||o.kong||o.chows.length)offers[j]=o}
  const cs={hk:true,i,t,order,offers,choices:{},o:offers[0]||null,botWin,botPung,botChow};
  if(Object.keys(offers).length){callState=cs;if(cs.o)Sound.chime();render();
    // rooms: everyone gets the same time to answer; solo: the optional call timer
    if(MP()){cs.deadline=Date.now()+CALL_MS;cs.tok=++callTok;later(()=>{if(callState===cs){for(const x in cs.offers)if(!(x in cs.choices))cs.choices[x]='pass';hkFinish(cs)}},CALL_MS)}
    else hkStartCallTimer(cs);
    return}
  hkFinish(cs);
}
// optional call timer: let the tile go if you don't answer in time (waits while a window is open)
let hkShortWarned=false;
function hkStartCallTimer(cs){const n=+hkR().callTimer;if(!n)return;let left=n*1000;
  const tick=()=>{if(callState!==cs||phase!=='play')return;if(document.querySelector('#modal .modal'))return setTimeout(tick,500);left-=250;if(left<=0){hkAnswer('pass');return}setTimeout(tick,250)};setTimeout(tick,250)}
function hkAnswer(c){hkAnswerSeat(0,c)}
// a person's answer to a call (you, or someone in your room); once everyone asked has answered, the best claim wins
function hkAnswerSeat(seat,c){
  const cs=callState;if(!cs||!cs.hk)return;const o=cs.offers&&cs.offers[seat];if(!o||seat in cs.choices)return;
  if(!(c==='pass'||(c==='win'&&o.win)||(c==='pung'&&o.pung)||(c==='kong'&&o.kong)||(typeof c==='string'&&c.startsWith('chow:')&&o.chows[+c.slice(5)])))return;
  if(seat===0)takeSnap();
  if(cs.rob){callState=null;const k=players[cs.rob.j];const t=k.hand.find(x=>x.id===cs.rob.tid);
    if(c==='win'&&t){k.hand.splice(k.hand.indexOf(t),1);players[seat].hand.push(t);log(`${NAMES[seat]} robbed ${NAMES[cs.rob.j]}'s kong!`);hkWin(seat,cs.rob.j,{rob:true,win:HKI[t.k],last:!wall.length});return}
    if(t)hkFinishAddKong(cs.rob.j,t);return}
  cs.choices[seat]=c;if(seat===0)cs.o=null;
  if(Object.keys(cs.offers).every(x=>x in cs.choices))hkFinish(cs);else render();
}
function hkFinish(cs){
  callState=null;const {i,t}=cs;const order=[1,2,3].map(d=>(i+d)%4),pos=j=>order.indexOf(j);const ch=cs.choices||{};
  const ctx={win:HKI[t.k],last:!wall.length,earth:hkFirst&&i===dealer&&discards.length===1};
  // a win beats everything (closest to the thrower first), then a pung or kong, then a chow
  let winner=null;for(const x in ch)if(ch[x]==='win'&&(winner==null||pos(+x)<pos(winner)))winner=+x;
  if(cs.botWin&&(winner==null||pos(cs.botWin.j)<pos(winner)))winner=cs.botWin.j;
  if(winner!=null){discards.pop();players[winner].hand.push(t);hkWin(winner,i,{...ctx,earth:ctx.earth&&winner!==dealer});return}
  for(const x in ch)if(ch[x]==='pung'||ch[x]==='kong'){hkClaim(+x,ch[x],null,i);return}
  if(cs.botPung){hkClaim(cs.botPung.j,cs.botPung.t,null,i);return}
  for(const x in ch)if(typeof ch[x]==='string'&&ch[x].startsWith('chow:')){const s=cs.offers[x].chows[+ch[x].slice(5)];if(s){hkClaim(+x,'chow',s,i);return}}
  if(cs.botChow){hkClaim(cs.botChow.j,'chow',cs.botChow.s,i);return}
  hkStartTurn((i+1)%4);
}
function hkClaim(j,type,s,from){
  const p=players[j];const t=discards.pop();const fromT=tileRect(t.id);const x=HKI[t.k];
  let need=type==='chow'?s.map(y=>HK_KINDS[y]):Array(type==='kong'?3:2).fill(t.k);
  const tiles=[t];for(const k of need){const h=p.hand.findIndex(z=>z.k===k);tiles.push(p.hand.splice(h,1)[0])}
  if(type==='chow')tiles.sort((a,b)=>HKI[a.k]-HKI[b.k]);
  p.exp.push({type,k:type==='chow'?tiles[0].k:t.k,tiles,n:tiles.length,conc:false,from});
  queueFly(t,fromT,0,480);hkFirst=false;
  log(`${NAMES[j]} called ${tname(t.k)} for a ${type}.`);toastAll(v=>`${nameV(j,v)}: ${type[0].toUpperCase()+type.slice(1)}!`);Sound.chime();
  turn=j;step='discard';selected=null;newIds=new Set();turnSrc=from;hkLast={claimed:true};
  if(type==='kong'&&!hkReplacement(j))return;
  render();if(!HUMAN[j])later(()=>hkBotAct(j),SPEED);
}

// ---- end of a hand ----
function hkWin(j,from,ctx){
  const p=players[j];const r=hkEval(j,p.hand,ctx);if(!r)return;
  hkSettle(j,from,r,ctx);
}
const hkOldBase=f=>f>=10?8:f>=7?4:f>=4?2:1;   // Old Style: 3 faan = 1, 4-6 = 2, 7-9 = 4, 10 or more = 8
// ---- score history: every hand of the match, kept with your saved progress ----
let hkHistory=[];
function hkHist(j,from,r,pay,note){hkHistory.push({n:hkHistory.length+1,wind:hkWind,east:dealer,winner:j,from,faan:r?r.faan:0,how:r?(r.bonus?r.items[0][0]:from==null?'Self-drawn':'Discard'):'Draw',top:r?r.items.slice().sort((a,b)=>b[1]-a[1])[0][0]:'',pay:pay.slice(),total:scores.slice(),note:note||''});if(hkHistory.length>200)hkHistory.shift()}
function hkSettle(j,from,r,ctx={}){
  const p=players[j];
  phase='over';callState=null;sortHand(p.hand);
  const R=hkR();let pts,pay=[0,0,0,0],note='';
  if(R.scoring==='old'){pts=hkOldBase(r.faan);
    // everyone pays; doubled for a self-draw, for the discarder, and when East wins or loses (these stack)
    for(let q=0;q<4;q++)if(q!==j){const a=pts*(from==null?2:1)*(q===from?2:1)*((j===dealer||q===dealer)?2:1);pay[q]-=a;pay[j]+=a}}
  else{pts=hkPoints(r.faan);
    if(from==null){for(let q=0;q<4;q++)if(q!==j){pay[q]-=pts/2;pay[j]+=pts/2}}
    else if(R.discPay==='half'){pay[j]+=pts;for(let q=0;q<4;q++)if(q!==j)pay[q]-=q===from?pts/2:pts/4}
    else{pay[from]-=pts;pay[j]+=pts}}
  // penalty payments: one player covers the whole win
  if(R.penalties&&!r.bonus){let liable=null;
    const claimed=p.exp.filter(e=>!e.conc&&e.from!=null);
    if(r.items.some(x=>x[0]==='All one suit')){
      if(from!=null&&claimed.length>=3){liable=from;note=`${from===0?'You':NAMES[from]} fed a one-suit hand that already showed three sets, so ${from===0?'you pay':'they pay'} it all.`}
      else if(from==null&&claimed.length===4){liable=claimed[3].from;note=`${liable===0?'You':NAMES[liable]} gave up the fourth set of a one-suit hand, so ${liable===0?'you pay':'they pay'} it all.`}}
    if(liable==null&&from!=null&&!ctx.rob&&(ctx.wallAtDiscard??wall.length)<=5){const k=HK_KINDS[ctx.win];
      const seen=discards.filter(t=>t.k===k).length+players.reduce((a,q)=>a+q.exp.reduce((b,e)=>b+e.tiles.filter(t=>t.k===k).length,0),0);
      if(!seen){liable=from;note=`${from===0?'You':NAMES[from]} threw a tile nobody had seen yet with ${wall.length} left in the wall, so ${from===0?'you pay':'they pay'} it all.`}}
    if(liable!=null&&liable!==j){const tot=pay[j];pay=[0,0,0,0];pay[j]=tot;pay[liable]=-tot}}
  for(let q=0;q<4;q++)scores[q]+=pay[q];
  hkHist(j,from,r,pay,note);
  hkDecideKeep(j===dealer);hkSaveProgress();
  log(`${NAMES[j]} won with ${r.faan} faan${r.raw>r.faan?' (capped)':''}.`);
  if(j===0){Sound.fanfare();confetti();toast('Mah Jongg!','big')}else{Sound.sad();toast(`${NAMES[j]}: Mah Jongg`)}
  render();later(()=>{hkShowResult(j,from,r,pts,pay,note);hkNetResult(j,from,r,pts,pay,note)},1300);
}
// East keeps the deal after winning or a drawn hand, unless the table caps or turns off repeats
function hkDecideKeep(want){const r=hkR().repeat;const ok=want&&(r==='always'||(r==='cap3'&&hkRepeat<3));
  hkKeep=ok;hkRepeat=ok?hkRepeat+1:0;hkMatchOver=!ok&&hkWind===3&&hkRot%4===3}
function hkEastNote(){return hkMatchOver?'':hkKeep?`${dealer===0?'You stay':NAMES[dealer]+' stays'} East.`:`East passes to ${NAMES[(dealer+1)%4]==='You'?'you':NAMES[(dealer+1)%4]}.`}
function hkMatchHTML(){if(!hkMatchOver)return '';const order=[0,1,2,3].sort((a,b)=>scores[b]-scores[a]);
  return `<div class="matchend"><h3>That's the match: all four rounds played</h3><ol>${order.map(q=>`<li>${NAMES[q]} <b>${scores[q]}</b></li>`).join('')}</ol></div>`}
function hkDrawGame(){
  phase='over';callState=null;hkHist(null,null,null,[0,0,0,0]);hkDecideKeep(true);if(NET.mode==='host')later(()=>netBroadcast({t:'modal',kind:'hkdraw'}),400);hkSaveProgress();log(`The wall is empty. Drawn hand: no one pays${hkKeep?' and East keeps the deal':''}.`);Sound.sad();render();
  openModal(`<h2>Drawn hand</h2><p>The wall ran out before anyone won, so no points change hands. ${hkEastNote()}</p>${hkMatchHTML()}
   <div class="mrow">${NET.mode==='client'?`<span class="waitnote">Waiting for ${esc(NAMES[NET.hostView]||'the host')} to deal</span>`:`<button class="btn btn-gold" onclick="newGame()">${hkMatchOver?'New match':'Next hand'}</button>`}${canUndo()?'<button class="btn btn-ghost" onclick="undoMove()">Undo</button>':''}<button class="btn btn-ghost" onclick="hkShowHistory()">Score history</button><button class="btn btn-ghost" onclick="closeModal()">Look at the table</button></div>`);
}
function hkShowResult(j,from,r,pts,pay,note=''){
  const p=players[j];
  const tiles=[...p.exp.flatMap(e=>e.tiles),...p.hand];
  openModal(`<h2>${j===0?'You won!':NAMES[j]+' won'}</h2>
   <p>${r.bonus?'Bonus tiles win: everyone pays, as for a self-draw.':hkR().scoring==='old'?`Old Style: ${r.faan} faan is worth ${pts} ${pts===1?'point':'points'}. Everyone pays, doubled for ${[from==null?'a self-draw':'the discarder',(j===dealer?'East winning':'East paying')].join(' and ')}.`:from==null?'Self-drawn, so everyone pays half each.':hkR().discPay==='half'?`Won on ${from===0?'your':NAMES[from]+"'s"} discard: ${from===0?'you pay':NAMES[from]+' pays'} half and the other two split the rest.`:`Won on ${from===0?'your':NAMES[from]+"'s"} discard, so ${from===0?'you pay':NAMES[from]+' pays'} it all.`}
    <b>${r.faan} faan</b>${r.raw>r.faan?` (${r.raw} capped at ${HK_MAX})`:''}${hkR().scoring==='old'?'':` = <b>${pts}</b> points`}.</p>${note?`<p class="hknote">${note}</p>`:''}
   <div class="faanlist">${r.items.filter(x=>x[1]>0).map(([n,f])=>`<span>${n}</span><b>${f}</b>`).join('')}</div>
   <div class="win-tiles">${tiles.map(t=>tileHTML(t,'md')).join('')}${(p.flowers||[]).map(t=>tileHTML(t,'md flowerbonus')).join('')}</div>
   <div class="pay">${NAMES.map((n,i)=>`<span>${n} <b class="${pay[i]>0?'plus':pay[i]<0?'minus':''}">${pay[i]>0?'+':''}${pay[i]}</b></span>`).join('')}</div>
   <p class="setnote">${hkEastNote()}</p>${hkMatchHTML()}
   <div class="mrow">${NET.mode==='client'?`<span class="waitnote">Waiting for ${esc(NAMES[NET.hostView]||'the host')} to deal</span>`:`<button class="btn btn-gold" onclick="newGame()">${hkMatchOver?'New match':'Next hand'}</button>`}${canUndo()?'<button class="btn btn-ghost" onclick="undoMove()">Undo</button>':''}<button class="btn btn-ghost" onclick="hkShowHistory()">Score history</button><button class="btn btn-ghost" onclick="closeModal()">Look at the table</button></div>`);
}

// the score history: every hand of this match
function hkShowHistory(){
  const nm=i=>i===0?'You':NAMES[i];
  const rows=hkHistory.slice().reverse().map(h=>`<tr><td>${h.n}</td><td>${HK_WINDNAME[h.wind]}</td><td>${h.winner==null?'<i>Drawn</i>':`<b>${nm(h.winner)}</b>`}<small>${h.winner==null?'Nobody pays':`${h.how==='Discard'?`on ${h.from===0?'your':NAMES[h.from]+"'s"} discard`:h.how.toLowerCase()} · ${h.faan} faan${h.top?' · '+h.top:''}`}${h.note?' · penalty':''}</small></td>${h.pay.map(v=>`<td class="${v>0?'plus':v<0?'minus':''}">${v>0?'+':''}${v||'–'}</td>`).join('')}</tr>`).join('');
  openModal(`<div class="help"><h2>Score history</h2>
   <p class="setnote">This match, newest hand first. ${HK_WINDNAME[hkWind]} round now.</p>
   ${hkHistory.length?`<div class="histwrap"><table class="hist"><thead><tr><th>#</th><th>Round</th><th>Result</th>${[0,1,2,3].map(i=>`<th>${nm(i)}</th>`).join('')}</tr></thead><tbody>${rows}</tbody>
     <tfoot><tr><td colspan="3">Totals</td>${scores.map(v=>`<td>${v}</td>`).join('')}</tr></tfoot></table></div>`:'<p>No hands finished yet this match.</p>'}
   <div class="mrow"><button class="btn btn-gold" onclick="closeModal()">Done</button></div></div>`);
}

// ---- moves from people in your room (checked here on the host) ----
function hkActWin(seat){const w=hkSelfWin(seat);if(w&&phase==='play'&&turn===seat&&step==='discard'&&!callState)hkWin(seat,null,hkCtxSelf(seat))}
function hkActKong(seat,k,kind){const o=hkKongOptions(seat).find(x=>x.k===k&&x.kind===kind);if(o&&phase==='play'&&turn===seat&&step==='discard'&&!callState)hkDoKong(seat,o)}
// results reach everyone in the room
function hkNetResult(j,from,r,pts,pay,note){if(NET.mode!=='host')return;
  for(const c of Object.values(NET.conns)){if(c.seat==null||!c.live)continue;const s=c.seat,R=x=>x==null?null:(x-s+4)%4;
    netTo(c,{t:'hkresult',j:R(j),from:R(from),r:{faan:r.faan,raw:r.raw,items:r.items,bonus:!!r.bonus,limit:!!r.limit},pts,pay:[0,1,2,3].map(x=>pay[(x+s)%4]),note})}}

// ---- your moves ----
function hkHumanWin(){if(NET.mode==='client'){netSend({t:'act',a:'hkwin'});return}const w=hkSelfWin(0);if(!w||phase!=='play'||turn!==0||step!=='discard'||callState)return;takeSnap();hkWin(0,null,hkCtxSelf(0))}
function hkHumanKong(x){const o=hkKongOptions(0)[x];if(NET.mode==='client'){if(o)netSend({t:'act',a:'hkkong',k:o.k,kind:o.kind});return}if(!o||phase!=='play'||turn!==0||step!=='discard'||callState)return;takeSnap();selected=null;hkDoKong(0,o)}

// ---- what you see ----
function hkWaits(seat){
  const p=players[seat];if(p.hand.length+3*p.exp.length!==13)return[];
  const out=[];for(const k of HK_KINDS){const r=hkEval(seat,[...p.hand,{k}],{win:HKI[k]});if(r)out.push({k,faan:r.faan,ok:hkEnough(r)})}
  return out;
}
function hkCoach(){
  const p=players[0];if(phase!=='play'&&phase!=='over')return null;
  const c=hkCounts(p.hand),m=p.exp.length;
  if(p.hand.length+3*m===14){   // your turn: what to throw
    if(hkSelfWin(0))return {ready:true,win:true,text:'You have a winning hand. Hit Mah Jongg!'};
    const sh=hkShanten(c,m);const t=hkChooseDiscardFor(0);
    return {sh,suggest:t,text:sh<=0?'Throw the suggested tile and you\'re ready.':`${sh} tile${sh>1?'s':''} from ready after a good discard.`};
  }
  const sh=hkShanten(c,m),w=sh===0?hkWaits(0):[];
  return {sh,waits:w,text:sh===0?(w.some(x=>x.ok)?'Ready! You win on:':`Ready, but not with ${HK_MIN} faan yet:`):`${sh} tile${sh>1?'s':''} from ready.`};
}
function hkChooseDiscardFor(i){const lv=0;const p=players[i];const c=hkCounts(p.hand),m=p.exp.length,plan=hkPlan(i);let best=null,bs=Infinity;
  for(let x=0;x<34;x++){if(!c[x])continue;const s=hkDiscardScore(i,c,m,x,plan);if(s<bs){bs=s;best=x}}
  return best==null?null:p.hand.find(t=>t.k===HK_KINDS[best])}
function hkStatus(){
  let status='',sub='',acts='',dir=null;const p=players[0];
  if(phase==='idle'){status='Pull up a chair';sub='Hit Deal me in to start a Hong Kong hand.';acts='<button class="btn btn-gold" id="bStart2">Deal me in</button>'}
  else if(phase==='shuffle'){status='Washing the tiles';sub='All 144 tiles, flowers and seasons included, get mixed before the deal.'}
  else if(phase==='play'){
    const cs=callState;
    if(cs&&cs.hk&&cs.o){
      const o=cs.o;status=cs.rob?`${NAMES[cs.rob.j]} is making a kong with ${tname(cs.t.k)}`:`${NAMES[cs.i]} threw ${tname(cs.t.k)}`;
      sub=cs.rob?'You can win by robbing the kong.':o.win?'You can win on this tile!':o.winShort!=null&&!o.pung&&!o.kong&&!o.chows.length?`It finishes your hand, but that's only ${o.winShort} faan (you need ${HK_MIN}).`:'Claim it or let it go.';
      const cb=(s)=>`<span class="chowopt">${s.map(y=>tileHTML(HK_KINDS[y],'xs')).join('')}</span>`;
      acts=`<div class="callbar">${+hkR().callTimer?`<i class="ctimer" style="animation-duration:${+hkR().callTimer}s"></i>`:''}${tileHTML(cs.t,'md')}<span>${o.win?'Win?':'Call it?'}</span>
        ${o.win?`<button class="btn btn-red" data-call="win">Mah Jongg! (${o.win} faan)</button>`:''}
        ${o.kong?'<button class="btn btn-ghost" data-call="kong">KONG</button>':''}
        ${o.pung?'<button class="btn btn-ghost" data-call="pung">PUNG</button>':''}
        ${o.chows.map((s,x)=>`<button class="btn btn-ghost" data-call="chow:${x}">CHOW ${cb(s)}</button>`).join('')}
        <button class="btn btn-gold" data-call="pass">Let it go</button></div>`;
    }else if(turn===0&&step==='discard'){
      status='Your turn';sub=hkLast.claimed?'Now throw a tile.':settings.dblDiscard?'Tap a tile, then hit Discard. Or tap it twice to throw it.':'Tap a tile to select it, then hit Discard.';
      const t=p.hand.find(x=>x.id===selected);const w=hkSelfWin(0);
      const r=!w&&!hkLast.claimed?hkEval(0,p.hand,hkCtxSelf(0)):null;
      if(r&&!hkEnough(r))sub=`Your tiles are complete but only ${r.faan} faan. You need ${HK_MIN} to win, so keep going.`;
      acts=`${w?`<button class="btn btn-red" id="bHkWin">Mah Jongg! (${w.faan} faan)</button>`:''}<button class="btn btn-gold" id="bDis" ${t?'':'disabled'}>Discard</button>${hkKongOptions(0).map((o,x)=>`<button class="btn btn-ghost" data-hkkong="${x}">${o.kind==='conc'?'Concealed kong':'Add to kong'} ${tileHTML(o.k,'xs')}</button>`).join('')}`;
    }else{status=`${NAMES[turn]} is playing`;sub=`${windOf(turn)} seat · ${HK_WINDNAME[hkWind]} round`}
  }else{status='Hand over';acts='<button class="btn btn-gold" id="bNext">Next hand</button>'}
  return {status,sub,acts,dir};
}
// ---- the faan counter: what your hand is worth right now ----
// A complete hand shows its exact faan. A ready hand shows the best tile it can win on.
// Otherwise it adds up what you already hold: dragon and wind pungs, flowers, one suit, a concealed hand.
let hkFaanOpen=false;
addEventListener('pointerdown',e=>{if(hkFaanOpen&&!e.target.closest('.faanbub')){hkFaanOpen=false;render()}},true);
// the coach (how close you are, what to throw) is its own switch, off unless you turn it on
const hkCoachOn=()=>settings.hkCoach===true;
function hkFaanNow(){
  const p=players[0];if(!p||phase!=='play')return null;
  const n=p.hand.length+3*p.exp.length;
  if(n===14&&turn===0&&!hkLast.claimed){const r=hkEval(0,p.hand,hkCtxSelf(0));if(r)return {faan:r.faan,items:r.items,kind:'win'}}
  if(n===13){const w=hkWaits(0);if(w.length){const top=w.reduce((a,b)=>b.faan>a.faan?b:a);const r=hkEval(0,[...p.hand,{k:top.k}],{win:HKI[top.k]});
    return {faan:top.faan,items:r?r.items:[],kind:'ready',k:top.k}}}
  const c=hkCounts(p.hand),it=[];
  const pung=x=>c[x]>=3||p.exp.some(e=>e.type!=='chow'&&HKI[e.k]===x);
  const dr=[31,32,33].filter(pung).length;if(dr)it.push([dr===1?'Dragon pung':'Dragon pungs',dr]);
  const sw=27+hkSeatWind(0),pw=27+hkWind;
  if(pung(sw))it.push(['Seat wind pung',1]);if(pung(pw))it.push(['Prevailing wind pung',1]);
  const all=[...p.hand,...p.exp.flatMap(e=>e.tiles)].filter(t=>t.k!=='F').map(t=>HKI[t.k]);
  const suits=new Set(all.filter(hkIsSuit).map(i=>Math.floor(i/9)));
  if(suits.size===1)it.push(all.some(hkIsHonor)?['Mixed one suit so far',3]:['All one suit so far',7]);
  it.push(...hkFlowerItems(0));
  if(p.exp.every(e=>e.conc))it.push(['Concealed so far',1]);
  return {faan:Math.min(HK_MAX,it.reduce((a,x)=>a+x[1],0)),items:it,kind:'sofar'};
}
// what each line in the faan bubble means
function hkFaanDesc(n){
  const seat=windOf(0),num=['East','South','West','North'].indexOf(seat)+1;
  const d={
    'Dragon pung':'You have a pung of Red, Green or White dragons.','Dragon pungs':'One faan for each pung of dragons you have.',
    'Seat wind pung':`A pung of your seat's wind (${seat}).`,'Prevailing wind pung':`A pung of this round's wind (${HK_WINDNAME[hkWind]}).`,
    'Mixed one suit so far':'All your suit tiles are one suit, plus winds or dragons. Keep it that way and you get 3.',
    'All one suit so far':'Every tile is one suit with no winds or dragons. Keep it that way and you get 7.',
    'No flowers or seasons':'You have no flowers or seasons. Drawing one takes this away.',
    'Own flower':`You have flower ${num}, the one for your seat (${seat}).`,'Own season':`You have season ${num}, the one for your seat (${seat}).`,
    'All four flowers':'You have all four flowers.','All four seasons':'You have all four seasons.',
    'Concealed so far':'You haven\'t claimed a discard yet. Claiming one (pung, chow or kong) loses this.',
    'Concealed hand':'You didn\'t claim any discards.','Self-drawn':'You drew the winning tile yourself.',
    'Last tile from the wall':'You won on the last tile of the wall.','Last discard':'You won on the last discard of the hand.',
    'Robbing the kong':'You won on a tile someone added to make a kong.','Win on a kong replacement':'You won on the tile drawn after a kong.',
    'Win on a double-kong replacement':'You won on the replacement tile after two kongs in a row.',
    'Small Three Dragons':'Pungs of two dragons and a pair of the third.','Great Three Dragons':'Pungs of all three dragons.',
  };
  if(d[n])return d[n];const row=hkScoringRows().find(r=>r[0]===n);return row?row[2]:'';
}
// what your tiles could still add (only ideas the tiles you hold make realistic)
function hkFaanIdeas(){
  const p=players[0],c=hkCounts(p.hand),out=[];
  const has=x=>p.exp.some(e=>e.type!=='chow'&&HKI[e.k]===x);
  for(const x of [31,32,33])if(c[x]===2&&!has(x))out.push([`A third ${['Red','Green','White'][x-31]} dragon`,'+1','You have a pair. A pung of any dragon is worth 1.']);
  const sw=27+hkSeatWind(0),pw=27+hkWind;
  for(const x of [...new Set([sw,pw])])if(c[x]===2&&!has(x))out.push([`A third ${HK_WINDNAME[x-27]} wind`,sw===pw?'+2':'+1',x===sw&&x===pw?'Your seat wind and the round wind: worth 2 as a pung.':x===sw?'Your seat\'s wind: worth 1 as a pung.':'This round\'s wind: worth 1 as a pung.']);
  const all=[...p.hand,...p.exp.flatMap(e=>e.tiles)].filter(t=>t.k!=='F').map(t=>HKI[t.k]);
  const sc=[0,0,0];let hon=0;for(const x of all){if(x<27)sc[Math.floor(x/9)]++;else hon++}
  const main=sc.indexOf(Math.max(...sc)),off=sc.reduce((a,v,k)=>k===main?a:a+v,0);
  const lockedOff=p.exp.some(e=>HKI[e.k]<27&&Math.floor(HKI[e.k]/9)!==main);
  const SUIT=['Bamboos','Characters','Dots'][main]||'one suit';
  if(off>0&&off<=4&&!lockedOff)out.push(['Mixed one suit','+3',`Get rid of your ${off} tile${off>1?'s':''} outside ${SUIT}, and keep winds and dragons if you like.`]);
  if(off>0&&off<=3&&hon<=2&&!lockedOff)out.push(['All one suit','+7',`Only ${SUIT}: also drop your ${hon?hon+' wind and dragon tile'+(hon>1?'s':''):'other tiles'}.`]);
  const pairs=c.filter(v=>v>=2).length;
  if(!p.exp.some(e=>e.type==='chow')&&pairs>=3)out.push(['All pungs','+3',`No runs: turn your pairs into pungs. You have ${pairs} pairs or pungs.`]);
  out.push(['Self-drawn','+1','Win on a tile you draw yourself instead of a discard.']);
  return out.slice(0,5);
}
function hkFaanHTML(){
  if(settings.hkFaan===false)return '';
  const f=hkFaanNow();if(!f)return '';
  const ok=f.kind==='sofar'?f.faan>=HK_MIN:hkEnough(f),label=f.kind==='win'?'Your hand':f.kind==='ready'?'Ready, best win':'So far';
  const note=f.kind==='ready'?`on ${tileHTML(f.k,'xs')}`:f.kind==='win'?(ok?'<span class="pill done">Enough to win</span>':`<span class="pill">need ${HK_MIN}</span>`):`<span class="fneed">need ${HK_MIN}</span>`;
  return `<div class="bubble faanbub${ok?' ok':''}"><button class="bhead" onclick="hkFaanOpen=!hkFaanOpen;render()" aria-expanded="${hkFaanOpen}" title="Tap to see what counts"><span class="bk">Faan</span><b class="fnum">${f.faan}</b><span class="flab">${label}</span>${note}</button>
    ${hkFaanOpen?`<div class="flist">${f.kind==='ready'?`<p class="fsub">Your best win: ${tileHTML(f.k,'xs')} for ${f.faan} faan.</p>`:f.kind==='win'?'<p class="fsub">Your hand right now:</p>':'<p class="fsub">What you already have:</p>'}
      ${f.items.length?f.items.map(([n,v])=>`<div class="frow"><span>${n}<small>${hkFaanDesc(n)}</small></span><b>${v}</b></div>`).join(''):'<div class="frow"><span>Nothing yet<small>Dragon or wind pungs, flowers and one-suit hands add faan.</small></span><b>0</b></div>'}
      ${f.kind!=='win'?`<p class="fsub">Could still add:</p>${hkFaanIdeas().map(([n,v,d])=>`<div class="frow idea"><span>${n}<small>${d}</small></span><b>${v}</b></div>`).join('')}`:''}</div>`:''}</div>`;
}
// the faan details float just above the Faan bubble (fixed to the screen, so the bubble row can't cut them off)
function hkPlaceFaan(){const f=document.querySelector('.faanbub .flist'),b=document.querySelector('.faanbub .bhead');if(!f||!b)return;
  const r=b.getBoundingClientRect(),w=f.offsetWidth,h=f.offsetHeight;let left=Math.max(8,Math.min(innerWidth-w-8,r.left));
  let top=r.top-h-8;if(top<8)top=Math.min(innerHeight-h-8,r.bottom+8);f.style.left=left+'px';f.style.top=top+'px';f.style.bottom='auto';f.classList.add('placed')}
function hkBubbleHTML(){if(hkFaanOpen)requestAnimationFrame(hkPlaceFaan);
  if(phase!=='play')return '';
  const fb=hkFaanHTML();if(!hkCoachOn())return fb?`<div class="bubbles">${fb}</div>`:'';
  const co=hkCoach();if(!co)return fb?`<div class="bubbles">${fb}</div>`:'';
  const pill=co.win?'<span class="pill done">Mah Jongg!</span>':co.sh===0||co.ready?'<span class="pill done">Ready</span>':`<span class="pill">${co.sh} from ready</span>`;
  return `<div class="bubbles">${fb}<div class="bubble"><div class="bhead hkbub"><span class="bk">Coach</span>${pill}<span class="hkbt">${co.suggest?'Throw '+tileHTML(co.suggest,'xs'):co.waits&&co.waits.length?co.waits.map(w=>tileHTML(w.k,'xs')).join(''):''}</span></div></div></div>`;
}
// the Scoring panel: each way to score, what it's worth, and what it means (matches how hkScore counts them)
function hkScoringRows(){
  const lim=HK_MAX>=13?'10–13':String(HK_MAX);
  const rows=[
    ['All chows',1,'All four sets are runs (chows) of one suit, like 3-4-5 of Dots.'],
    ['All pungs',3,'All four sets are pungs or kongs (three or four of the same tile). No runs.'],
    ['Mixed one suit',3,'Every tile is from one suit (Dots, Bamboos or Characters) plus winds and dragons.'],
    ['All one suit',7,'Every tile is from one suit, with no winds or dragons at all.'],
    ['Dragon pung (each)',1,'A pung or kong of Red, Green or White dragons. Each one counts.'],
    ['Seat or prevailing wind pung',1,'A pung of your own seat\'s wind, or of this round\'s wind. If it\'s both, it counts twice.'],
    ['Small / Great Three Dragons','5 / 8','Small: pungs of two dragons and a pair of the third. Great: pungs of all three. These replace the 1 per dragon pung.'],
    ['Small Four Winds',6,'Pungs of three winds and a pair of the fourth. (Pungs of all four winds is a limit hand.)'],
    ['Mixed terminals and honors',1,'Every set is a pung of 1s, 9s, winds or dragons, with tiles from at least one suit. You also get the 3 for All pungs.'],
    ['Self-drawn',1,'You win on a tile you drew yourself, not on someone\'s discard. Everyone pays you.'],
    ['Concealed hand',1,'You didn\'t claim any discards before winning. Kongs you made from your own tiles still count as concealed.'],
    ['No flowers',1,'You got no flowers or seasons at all this hand.'],
    ['Own flower or season',1,`The flower or season with your seat\'s number: East 1, South 2, West 3, North 4. You\'re ${windOf(0)}.`],
    ['All four flowers or seasons',2,'All four flowers, or all four seasons. Replaces the 1 for your own one.'],
    ['Win on a kong replacement',1,'You win with the extra tile you draw after making a kong. Two kongs in a row: 8.'],
    ['Robbing a kong',1,'You win by taking the tile someone adds to their pung to make a kong.'],
    ['Last tile',1,'You win on the very last tile from the wall, or on the discard right after it.'],
  ];
  if(hkR().sevenPairs)rows.push(['Seven Pairs',4,'Seven different pairs, all from your own tiles.']);
  if(hkR().bonusWin)rows.push(['Seven or eight flowers and seasons','3 / '+Math.min(HK_MAX,13),'Collect 7 bonus tiles and you win right away for 3 faan; all 8 is a limit win. Everyone pays.']);
  rows.push(['Limit hands',lim,`Rare hands that score the top amount on their own${HK_MAX<13?` (capped at ${HK_MAX})`:''}: Thirteen Orphans, All honors, ${hkR().selfTriplets!=='normal'?'Self triplets (four pungs all from your own tiles), ':''}All terminals (only 1s and 9s), Nine Gates, Great Four Winds, Four kongs, ${hkR().pureGreen?'Pure Green (only green Bamboos and Green Dragons), ':''}and winning on the deal (Heavenly or Earthly hand).`]);
  return rows;
}
function hkRenderSide(){
  const p=players[0];
  $('#stars').innerHTML=`<div class="ph"><h3>Scoring</h3><span class="sub">${HK_MIN} faan to win · max ${HK_MAX} · <a href="#" class="histlink" onclick="hkShowHistory();return false">Score history</a></span></div>
   <div class="faanref">${hkScoringRows().map(([n,f,d])=>`<span>${n}<small>${d}</small></span><b>${f}</b>`).join('')}</div>`;
  let body;
  if(!hkCoachOn())body='<div class="muted-note">The coach is off. Turn it on to see how close you are and what to throw.</div>';
  else if(phase!=='play')body='<div class="muted-note">Tips show up once the tiles are dealt.</div>';
  else{const co=hkCoach();
    body=`<div class="hkcoach"><p><b>${co.text}</b></p>
      ${co.suggest?`<div class="hkrow">Suggested throw: ${tileHTML(co.suggest,'md')}</div>`:''}
      ${co.waits&&co.waits.length?`<div class="hkwaits">${co.waits.map(w=>`<div class="${w.ok?'':'short'}">${tileHTML(w.k,'md')}<span>${w.faan} faan</span></div>`).join('')}</div>`:''}
      <p class="setnote">Flowers and seasons: ${p.flowers.length?p.flowers.map(t=>HK_FLOWER[t.v]||HK_SEASON[t.v-4]).join(', '):'none yet (worth 1 faan if you win without any)'}. Your wind: ${windOf(0)}. Round: ${HK_WINDNAME[hkWind]}.</p></div>`}
  $('#hints').innerHTML=`<div class="ph"><h3>Coach</h3><label class="switch" for="hintToggle"><input type="checkbox" id="hintToggle" ${hkCoachOn()?'checked':''}><span class="track"><span class="knob"></span></span><span>${hkCoachOn()?'On':'Off'}</span></label></div>${body}`;
  $('#hintToggle').onchange=e=>{settings.hkCoach=e.target.checked;saveSettings();render()};
}
function hkShowRules(){
  pauseGame();
  openModal(`<div class="help"><h2>Hong Kong mahjong</h2>
   <p><b>Goal:</b> make 4 sets and a pair (14 tiles) worth at least ${HK_MIN} faan. A set is a <b>pung</b> (three alike), a <b>kong</b> (four alike) or a <b>chow</b> (three in a row in one suit).</p>
   <p><b>Your turn:</b> you draw, then throw one tile. Flowers and seasons are set aside the moment you get them, and you draw a replacement.</p>
   <p><b>Calling:</b> you can take the tile just thrown to make a pung or kong from anyone, or a chow only from the player on your left. Calling exposes that set. A win beats a pung or kong, and a pung beats a chow.</p>
   <p><b>Kongs:</b> four alike, declared on your turn (concealed) or by adding a drawn tile to your exposed pung. Either way you draw a replacement tile. If you add to a pung, anyone who wins on that tile can rob it.</p>
   <h3>Faan</h3>
   <div class="faanlist">${[['All chows',1],['All pungs',3],['Mixed one suit (one suit plus honors)',3],['All one suit',7],['Mixed terminals and honors (plus 3 for all pungs)',1],['Seven pairs (if turned on)',4],['Each dragon pung',1],['Small Three Dragons (two pungs, pair of the third)',5],['Great Three Dragons',8],['Small Four Winds',6],['Seat wind pung',1],['Prevailing wind pung',1],['No flowers or seasons',1],['Own flower / own season',1],['All four flowers / seasons',2],['Self-drawn',1],['Concealed hand',1],['Robbing a kong, last tile or discard, kong replacement','1 each'],['Win on a double-kong replacement',8],['Limit hands: all honors, self triplets, all terminals, Nine Gates, Thirteen Orphans, Four Kongs, Great Four Winds, Heavenly / Earthly Hand',HK_MAX]].map(([n,f])=>`<span>${n}</span><b>${f}</b>`).join('')}</div>
   <p class="setnote">${hkR().scoring==='old'?`Flower and season faan don't count toward the ${HK_MIN}-faan minimum (Old Style).`:`Every faan counts toward the ${HK_MIN}-faan minimum, flowers included.`} Faan are capped at ${HK_MAX}.${hkR().sevenPairs?' Seven Pairs (4 faan) is on.':''}</p>
   <h3>Paying</h3>
   <p>${hkR().scoring==='old'?'Old Style: 3 faan = 1 point, 4–6 = 2, 7–9 = 4, 10 or more = 8. Everyone pays the winner. Payments double for a self-draw, for the player who threw the winning tile, and when East wins or loses (doubles stack).':''}${hkR().penalties?' Penalty payments are on: feeding a one-suit hand its last set, or throwing a never-seen winning tile with 5 or fewer left, makes you pay it all.':''}${hkR().bonusWin?' Seven flowers and seasons win at once for 3 faan; all eight is a limit win.':''}</p>
   <p ${hkR().scoring==='old'?'hidden':''}>${hkR().table==='full'?'Full spicy: points double with every faan (3 = 8, 4 = 16, 5 = 32, 6 = 64…).':'Half spicy: 3 faan = 8, 4 = 16, 5 = 24, 6 = 32, 7 = 48, 8 = 64, 9 = 96, 10 = 128.'} ${hkR().discPay==='half'?'Win on a discard and the thrower pays half; the other two split the rest.':'Win on a discard and the thrower pays it all.'} Draw it yourself and each other player pays half the table value (1.5× in total).</p>
   <h3>Rounds</h3>
   <p>A match is four rounds: East, South, West and North. ${hkR().repeat==='never'?'The deal always passes to the right.':hkR().repeat==='cap3'?'East keeps the deal after winning or a drawn hand, up to 3 times in a row; otherwise it moves to the right.':'East keeps the deal after winning or a drawn hand; otherwise it moves to the right.'} The round wind changes after everyone has been East.${hkR().noLastCalls?' No pung, kong or chow on the last discard.':''}</p>
   <div class="mrow"><button class="btn btn-gold" onclick="closeModal()">Got it</button></div></div>`);
}

// ---- saved progress ----
function hkSaveProgress(){
  if(!settings.save||MP())return;
  try{
    localStorage.setItem('amj_progress_hk',JSON.stringify({scores,dealer,hkWind,hkRot,hkKeep,hkRepeat,hkMatchOver,hist:hkHistory}));
    if(phase==='over'){localStorage.removeItem('amj_game_hk');return}
    if(phase==='play'&&turn===0&&step==='discard'&&!callState)localStorage.setItem('amj_game_hk',JSON.stringify({wall,players,discards,dealer,turn,hkWind,hkRot,hkLast,hkFirst,turnSrc}));
  }catch(e){}
}
function hkSavedGame(){if(!settings.save)return null;try{const g=JSON.parse(localStorage.getItem('amj_game_hk'));return g&&Array.isArray(g.players)?g:null}catch(e){return null}}
function hkResume(){
  const g=hkSavedGame();if(!g)return false;
  gid++;Sound.init();hkApplyRules();
  ({wall,players,discards,dealer,turn,hkWind,hkRot,hkLast,hkFirst,turnSrc}=g);
  phase='play';step='discard';pendingStart=false;sel=new Set();selected=null;callState=null;newIds=new Set();flyQueue=[];logs=[];logVer++;
  log('Picked up where you left off.');$('#splash').classList.add('hide');render();return true;
}
