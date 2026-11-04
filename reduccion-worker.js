/* Quiniela Lab: reducciones por cobertura. Toda garantía se comprueba por fuerza bruta antes de devolverse. */
function engine(radices,k,seed){
  const m=radices.length,mul=[];let N=1;for(let i=0;i<m;i++){mul[i]=N;N*=radices[i]}
  const dig=(c,i)=>Math.floor(c/mul[i])%radices[i];
  const ball=c=>{const out=[c];const rec=(cur,start,left)=>{if(!left)return;for(let i=start;i<m;i++){const d=dig(cur,i);for(let v=0;v<radices[i];v++){if(v===d)continue;const nx=cur+(v-d)*mul[i];out.push(nx);rec(nx,i+1,left-1)}}};rec(c,0,k);return out};
  let s=(seed>>>0)||1;const rnd=()=>{s=(s*1664525+1013904223)>>>0;return s/4294967296};
  return {radices,m,N,mul,dig,ball,rnd};
}
function greedy(E){
  const {N,ball,rnd}=E,cov=new Uint8Array(N),balls=new Array(N),bl=c=>balls[c]||(balls[c]=ball(c));let unc=N;const picks=[],items=[];
  for(let c=0;c<N;c++)items.push({c,g:bl(c).length+rnd()*.5});items.sort((a,b)=>b.g-a.g);
  while(unc>0){
    let best=-1,bg=-1,scan=0;
    for(const it of items){if(it.g<=bg)break;let g=0;for(const x of bl(it.c))if(!cov[x])g++;it.g=g+rnd()*.5;if(it.g>bg){bg=it.g;best=it.c}if(++scan>4000)break}
    if(best<0||bg<1){for(let c=0;c<N;c++)if(!cov[c]){best=c;break}}
    picks.push(best);for(const x of bl(best))if(!cov[x]){cov[x]=1;unc--}
    items.sort((a,b)=>b.g-a.g);
  }
  return picks;
}
function prune(E,picks){
  const cnt=new Int32Array(E.N);for(const c of picks)for(const x of E.ball(c))cnt[x]++;
  const out=[];picks.slice().sort(()=>E.rnd()-.5).forEach(c=>{const b=E.ball(c);if(b.every(x=>cnt[x]>=2))b.forEach(x=>cnt[x]--);else out.push(c)});return out;
}
function anneal(E,start,ms){
  let cur=start.slice(),best=cur.slice();const end=Date.now()+ms,cnt=new Int32Array(E.N);
  const add=(c,d)=>{for(const x of E.ball(c))cnt[x]+=d};cur.forEach(c=>add(c,1));
  while(Date.now()<end&&cur.length>1){
    const rm=Math.floor(E.rnd()*cur.length);add(cur[rm],-1);cur[rm]=cur[cur.length-1];cur.pop();
    let unc=0;for(let i=0;i<E.N;i++)if(!cnt[i])unc++;
    let T=1.2,it=0;
    while(unc>0&&Date.now()<end&&it<600000){
      it++;const i=Math.floor(E.rnd()*cur.length),old=cur[i],pos=Math.floor(E.rnd()*E.m),r=E.radices[pos],d=E.dig(old,pos),v=(d+1+Math.floor(E.rnd()*(r-1)))%r,nx=old+(v-d)*E.mul[pos];
      const oB=E.ball(old),nB=E.ball(nx);let dU=0;
      for(const x of oB){cnt[x]--;if(cnt[x]===0)dU++}
      for(const x of nB){if(cnt[x]===0)dU--;cnt[x]++}
      if(dU<=0||E.rnd()<Math.exp(-dU/T)){cur[i]=nx;unc+=dU}else{for(const x of nB)cnt[x]--;for(const x of oB)cnt[x]++}
      T=Math.max(.15,T*.99997);
    }
    if(unc===0)best=cur.slice();else break;
  }
  return best;
}
function single(radices,k,ms,seed){
  const E=engine(radices,k,seed),t0=Date.now();let best=null;
  do{const p=prune(E,greedy(E));if(!best||p.length<best.length)best=p}while(Date.now()-t0<ms*.35&&best.length>1);
  return anneal(E,best,Math.max(0,ms-(Date.now()-t0)));
}
/* Producto de dos códigos: suma los fallos admitidos y mantiene la garantía. */
function product(radices,k,ms){
  if(k<2||radices.length<4)return null;
  const h=radices.length>>1,a=radices.slice(0,h),b=radices.slice(h),A=single(a,1,ms/2,11),B=single(b,k-1,ms/2,29);let na=1;a.forEach(r=>na*=r);
  const out=[];A.forEach(x=>B.forEach(y=>out.push(x+y*na)));return out;
}
function verify(radices,k,cols){
  const digs=c=>{const a=[];let x=c;for(const r of radices){a.push(x%r);x=Math.floor(x/r)}return a},C=cols.map(digs);
  let N=1;radices.forEach(r=>N*=r);let worst=0;
  for(let o=0;o<N;o++){const d=digs(o);let b=1e9;for(const c of C){let t=0;for(let i=0;i<d.length;i++)if(c[i]!==d[i])t++;if(t<b)b=t;if(!b)break}if(b>worst)worst=b;if(worst>k)break}
  return {ok:worst<=k,worst,N};
}
function run(radices,k,ms){
  if(!radices.length)return {cols:[0],ver:{ok:true,worst:0,N:1}};
  let N=1;radices.forEach(r=>N*=r);if(k>=radices.length)return {cols:[0],ver:{ok:true,worst:radices.length,N}};
  const sh=k>=2&&radices.length>=4?ms*.5:ms;let best=single(radices,k,sh,7);const pr=product(radices,k,ms-sh);if(pr&&pr.length<best.length)best=pr;
  const ver=verify(radices,k,best);return {cols:best,ver};
}
if(typeof self!=='undefined'&&self.postMessage&&typeof window==='undefined'){self.onmessage=e=>{const {radices,k,ms}=e.data;try{self.postMessage({ok:true,...run(radices,k,ms)})}catch(err){self.postMessage({ok:false,error:String(err)})}}}
if(typeof module!=='undefined')module.exports={run,verify};
