/* Quiniela Lab: reducciones por cobertura. Toda garantía se comprueba por fuerza bruta antes de devolverse. */
/* Búsqueda local con pesos sobre las combinaciones sin cubrir: no se para hasta agotar el tiempo. */
function buildBalls(radices,k){
  const m=radices.length,mul=[];let N=1;for(let i=0;i<m;i++){mul[i]=N;N*=radices[i]}
  let size=1,c1=[1];for(let i=0;i<m;i++){const n=c1.slice();n.push(0);for(let j=c1.length;j>=1;j--)n[j]=(n[j]||0)+c1[j-1]*(radices[i]-1);c1=n}
  size=0;for(let j=0;j<=k&&j<c1.length;j++)size+=c1[j];
  const B=new Int32Array(N*size);
  for(let c=0;c<N;c++){let p=c*size;B[p++]=c;const rec=(cur,start,left)=>{if(!left)return;for(let i=start;i<m;i++){const d=Math.floor(cur/mul[i])%radices[i];for(let v=0;v<radices[i];v++){if(v===d)continue;const nx=cur+(v-d)*mul[i];B[p++]=nx;rec(nx,i+1,left-1)}}};rec(c,0,k)}
  return {N,size,B};
}
function rwls(radices,k,ms,seed,start,onBest){
  const {N,size,B}=buildBalls(radices,k),end=Date.now()+ms;let s=(seed>>>0)||1;const rnd=n=>{s^=s<<13;s>>>=0;s^=s>>>17;s^=s<<5;s>>>=0;return s%n};
  const w=new Int32Array(N).fill(1),cov=new Int32Array(N),inS=new Uint8Array(N),score=new Float64Array(N),stamp=new Float64Array(N),can=new Uint8Array(N).fill(1);
  const sol=[],pos=new Int32Array(N).fill(-1);const unc=[],upos=new Int32Array(N).fill(-1);
  const uadd=e=>{upos[e]=unc.length;unc.push(e)},udel=e=>{const i=upos[e],l=unc.pop();if(l!==e){unc[i]=l;upos[l]=i}upos[e]=-1};
  for(let e=0;e<N;e++)uadd(e);for(let c=0;c<N;c++)score[c]=size;
  const add=c=>{inS[c]=1;pos[c]=sol.length;sol.push(c);score[c]=-score[c];
    for(let i=c*size,a=i+size;i<a;i++){const e=B[i],we=w[e];
      if(cov[e]===0){udel(e);for(let j=e*size,b=j+size;j<b;j++){const d=B[j];if(d!==c){score[d]-=we;can[d]=1}}}
      else if(cov[e]===1){for(let j=e*size,b=j+size;j<b;j++){const d=B[j];if(inS[d]&&d!==c){score[d]+=we;break}}}
      cov[e]++}};
  const del=c=>{inS[c]=0;const i0=pos[c],l=sol.pop();if(l!==c){sol[i0]=l;pos[l]=i0}pos[c]=-1;score[c]=-score[c];can[c]=0;
    for(let i=c*size,a=i+size;i<a;i++){const e=B[i],we=w[e];cov[e]--;
      if(cov[e]===0){uadd(e);for(let j=e*size,b=j+size;j<b;j++){const d=B[j];if(d!==c){score[d]+=we;can[d]=1}}}
      else if(cov[e]===1){for(let j=e*size,b=j+size;j<b;j++){const d=B[j];if(inS[d]){score[d]-=we;break}}}}};
  if(start)for(const c of start)add(c);
  while(unc.length){let bc=-1,bs=-1;const e=unc[rnd(unc.length)];for(let j=e*size,b=j+size;j<b;j++){const d=B[j];if(score[d]>bs||(score[d]===bs&&rnd(2))){bs=score[d];bc=d}}add(bc)}
  let best=sol.slice(),it=0,tabu=-1;
  const pickRem=()=>{let bc=-1,bs=-Infinity,bt=Infinity;for(let i=0;i<sol.length;i++){const c=sol[i];if(c===tabu)continue;const sc=score[c];if(sc>bs||(sc===bs&&stamp[c]<bt)){bc=c;bs=sc;bt=stamp[c]}}return bc};
  while(true){
    if(!(++it&255)&&Date.now()>=end)break;
    if(!unc.length){best=sol.slice();if(onBest)onBest(best,it);if(sol.length<=1)break;del(pickRem());continue}
    const r=pickRem();if(r<0)break;del(r);stamp[r]=it;
    const e=unc[rnd(unc.length)];let bc=-1,bs=-1,bt=Infinity;
    for(let j=e*size,b=j+size;j<b;j++){const d=B[j];if(!can[d])continue;const sc=score[d];if(sc>bs||(sc===bs&&stamp[d]<bt)){bc=d;bs=sc;bt=stamp[d]}}
    if(bc<0)bc=B[e*size+rnd(size)];
    add(bc);stamp[bc]=it;tabu=bc;
    for(let i=0;i<unc.length;i++){const x=unc[i];w[x]++;for(let j=x*size,b=j+size;j<b;j++)score[B[j]]++}
  }
  return {cols:best,it};
}
/* Producto de dos códigos: suma los fallos admitidos y mantiene la garantía. */
function product(radices,k,ms){
  if(k<2||radices.length<4)return null;
  const h=radices.length>>1,a=radices.slice(0,h),b=radices.slice(h),A=rwls(a,1,ms/2,11).cols,B=rwls(b,k-1,ms/2,29).cols;let na=1;a.forEach(r=>na*=r);
  const out=[];A.forEach(x=>B.forEach(y=>out.push(x+y*na)));return out;
}
function verify(radices,k,cols){
  const digs=c=>{const a=[];let x=c;for(const r of radices){a.push(x%r);x=Math.floor(x/r)}return a},C=cols.map(digs);
  let N=1;radices.forEach(r=>N*=r);let worst=0;
  for(let o=0;o<N;o++){const d=digs(o);let b=1e9;for(const c of C){let t=0;for(let i=0;i<d.length;i++)if(c[i]!==d[i])t++;if(t<b)b=t;if(!b)break}if(b>worst)worst=b;if(worst>k)break}
  return {ok:worst<=k,worst,N};
}
function search(radices,k,ms,seed){
  const pr=product(radices,k,ms*.1);if(!pr)return rwls(radices,k,ms,seed).cols;
  const a=rwls(radices,k,ms*.45,seed).cols,st=pr.length<a.length?pr:a,b=rwls(radices,k,ms*.45,seed+1,st).cols;
  return [a,b,pr].reduce((x,y)=>y.length<x.length?y:x);
}
function run(radices,k,ms,seed){
  if(!radices.length)return {cols:[0],ver:{ok:true,worst:0,N:1}};
  let N=1;radices.forEach(r=>N*=r);if(k>=radices.length)return {cols:[0],ver:{ok:true,worst:radices.length,N}};
  const best=search(radices,k,ms,seed||7),ver=verify(radices,k,best);return {cols:best,ver};
}
if(typeof self!=='undefined'&&self.postMessage&&typeof window==='undefined'){self.onmessage=e=>{const {radices,k,ms}=e.data;try{self.postMessage({ok:true,...run(radices,k,ms)})}catch(err){self.postMessage({ok:false,error:String(err)})}}}
if(typeof module!=='undefined')module.exports={run,verify,rwls};
