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
/* Cambiar qué signo corresponde a cada dígito no altera la garantía; se elige el reparto con más probabilidad de pleno. */
function score(cols,radices,w){let v=0;for(const c of cols){let x=c,q=1;for(let j=0;j<radices.length;j++){const r=radices[j];q*=w[j][x%r];x=Math.floor(x/r)}v+=q}return v}
function bestLabels(cols,radices,w){
  const m=radices.length,dg=cols.map(c=>{const a=[];let x=c;for(const r of radices){a.push(x%r);x=Math.floor(x/r)}return a});
  const perms=r=>r===2?[[0,1],[1,0]]:r===3?[[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]]:[[0]];
  const cur=radices.map(r=>perms(r)[0]),obj=()=>{let v=0;for(const d of dg){let q=1;for(let j=0;j<m;j++)q*=w[j][cur[j][d[j]]];v+=q}return v};
  let best=obj(),imp=true;while(imp){imp=false;for(let j=0;j<m;j++)for(const pm of perms(radices[j])){const old=cur[j];cur[j]=pm;const v=obj();if(v>best*(1+1e-12)){best=v;imp=true}else cur[j]=old}}
  return dg.map(d=>{let x=0,mul=1;for(let j=0;j<m;j++){x+=cur[j][d[j]]*mul;mul*=radices[j]}return x});
}
/* Máxima probabilidad cubierta con un número fijo de columnas. No da garantía. */
function budgetSearch(radices,k,B,w,ms,seed,target){
  const {N,size,B:L}=buildBalls(radices,k),wt=new Float64Array(N);for(let c=0;c<N;c++){let x=c,q=1;for(let j=0;j<radices.length;j++){const r=radices[j];q*=w[j][x%r];x=Math.floor(x/r)}wt[c]=q}
  let s=(seed>>>0)||1;const rnd=n=>{s^=s<<13;s>>>=0;s^=s>>>17;s^=s<<5;s>>>=0;return s%n};
  const cov=new Int32Array(N),inS=new Uint8Array(N),gain=new Float64Array(N),loss=new Float64Array(N),stamp=new Float64Array(N),sol=[],bonus=.2;
  const recompute=()=>{for(let c=0;c<N;c++){const on=inS[c];let v=on?bonus*wt[c]:bonus*wt[c];for(let i=c*size,a=i+size;i<a;i++){const e=L[i];if(on?cov[e]===1:cov[e]===0)v+=wt[e]}if(on){loss[c]=v;gain[c]=0}else{gain[c]=v;loss[c]=0}}};
  const put=c=>{inS[c]=1;sol.push(c);for(let i=c*size,a=i+size;i<a;i++)cov[L[i]]++},take=c=>{inS[c]=0;sol.splice(sol.indexOf(c),1);for(let i=c*size,a=i+size;i<a;i++)cov[L[i]]--};
  const bestAdd=lim=>{let bc=-1,bg=-1;for(let c=0;c<N;c++)if(!inS[c]&&stamp[c]<=lim&&gain[c]>bg){bg=gain[c];bc=c}return bc};
  const value=()=>{let v=0;for(let e=0;e<N;e++)if(cov[e])v+=wt[e];for(const c of sol)v+=bonus*wt[c];return v};
  const total=wt.reduce((a,b)=>a+b,0),share=()=>{let v=0;for(let e=0;e<N;e++)if(cov[e])v+=wt[e];return v/total};
  if(target){while(share()<target&&sol.length<N){recompute();put(bestAdd(0))}B=sol.length}
  else for(let i=0;i<Math.min(B,N);i++){recompute();put(bestAdd(0))}
  let best=sol.slice(),bv=value(),it=0;const end=Date.now()+ms;
  if(target){let goal=sol.slice();while(Date.now()<end&&sol.length>1){
      recompute();let bc=-1,bl=Infinity;for(const c of sol)if(loss[c]<bl){bl=loss[c];bc=c}take(bc);
      let found=share()>=target,last=Infinity;
      while(!found&&Date.now()<end){it++;const n=1+rnd(3);for(let q=0;q<n&&sol.length;q++){recompute();let c0=-1,l0=Infinity;for(const c of sol){const l=loss[c]*(1+rnd(600)/1000);if(l<l0&&stamp[c]<it){l0=l;c0=c}}if(c0<0)c0=sol[rnd(sol.length)];take(c0);stamp[c0]=it+3}
        for(let q=0;q<n;q++){recompute();let c1=bestAdd(it-1);if(c1<0)c1=bestAdd(Infinity);put(c1)}found=share()>=target}
      if(found)goal=sol.slice();else break}
    best=goal;B=N}
  while(Date.now()<end&&B<N){it++;const n=1+rnd(3);
    for(let q=0;q<n&&sol.length;q++){recompute();let bc=-1,bl=Infinity;for(const c of sol){const l=loss[c]*(1+rnd(600)/1000);if(l<bl&&stamp[c]<it){bl=l;bc=c}}if(bc<0)bc=sol[rnd(sol.length)];take(bc);stamp[bc]=it+3}
    for(let q=0;q<n;q++){recompute();let bc=bestAdd(it-1);if(bc<0)bc=bestAdd(Infinity);put(bc)}
    const v=value();if(v>bv*(1+1e-12)){bv=v;best=sol.slice()}else if(v<bv*.995){for(const c of sol.slice())take(c);for(const c of best)put(c)}
  }
  cov.fill(0);for(const c of best)for(let i=c*size,a=i+size;i<a;i++)cov[L[i]]=1;let cw=0,tw=0,cn=0;for(let e=0;e<N;e++){tw+=wt[e];if(cov[e]){cw+=wt[e];cn++}}
  return {cols:best,covered:cw/tw,coveredN:cn,N};
}
function run(radices,k,ms,seed){
  if(!radices.length)return {cols:[0],ver:{ok:true,worst:0,N:1}};
  let N=1;radices.forEach(r=>N*=r);if(k>=radices.length)return {cols:[0],ver:{ok:true,worst:radices.length,N}};
  const best=search(radices,k,ms,seed||7),ver=verify(radices,k,best);return {cols:best,ver};
}
/* Cubre solo una lista condicionada. Las columnas pueden salir de tus signos o, si se pide, de la propia lista. */
function condReduce(cols,k,ms,seed,inside){
  const SG=['1','X','2'],n=cols[0].length,mul=[];for(let i=0,m=1;i<n;i++,m*=3)mul[i]=m;
  const code=c=>{let x=0;for(let i=0;i<n;i++)x+=SG.indexOf(c[i])*mul[i];return x},T=[...new Set(cols)],codes=T.map(code),ids=new Map(codes.map((c,i)=>[c,i]));
  const marks=[];for(let i=0;i<n;i++){const u=new Set();for(const c of T)u.add(SG.indexOf(c[i]));marks.push([...u])}
  const build=only=>{const cand=new Map();let tot=0,over=false;
    const push=(y,e)=>{let a=cand.get(y);if(!a){a=[];cand.set(y,a)}a.push(e);tot++};
    for(let e=0;e<codes.length&&!over;e++){const rec=(cur,st,left)=>{if(!only||ids.has(cur))push(cur,e);if(!left||tot>7e6){if(tot>7e6)over=true;return}for(let i=st;i<n;i++){const d=Math.floor(cur/mul[i])%3;for(const v of marks[i]){if(v===d)continue;rec(cur+(v-d)*mul[i],i+1,left-1)}}};rec(codes[e],0,k)}
    return over?null:cand};
  let used=!!inside,cand=build(used);if(!cand){used=true;cand=build(true)}if(!cand)throw new Error('too big');
  const cc=[...cand.keys()],CV=cc.map(y=>Int32Array.from(cand.get(y))),E=codes.length,tmp=Array.from({length:E},()=>[]);CV.forEach((l,j)=>{for(let i=0;i<l.length;i++)tmp[l[i]].push(j)});const inv=tmp.map(a=>Int32Array.from(a));
  const M=cc.length,w=new Int32Array(E).fill(1),cov=new Int32Array(E),inS=new Uint8Array(M),score=new Float64Array(M),st=new Float64Array(M),can=new Uint8Array(M).fill(1),sol=[],pos=new Int32Array(M).fill(-1),unc=[],up=new Int32Array(E).fill(-1);
  let s=(seed>>>0)||1;const rnd=m=>{s^=s<<13;s>>>=0;s^=s>>>17;s^=s<<5;s>>>=0;return s%m};
  const ua=e=>{up[e]=unc.length;unc.push(e)},ud=e=>{const i=up[e],l=unc.pop();if(l!==e){unc[i]=l;up[l]=i}up[e]=-1};for(let e=0;e<E;e++)ua(e);CV.forEach((l,j)=>score[j]=l.length);
  const add=c=>{inS[c]=1;pos[c]=sol.length;sol.push(c);score[c]=-score[c];const l=CV[c];for(let q=0;q<l.length;q++){const e=l[q],we=w[e],iv=inv[e];if(cov[e]===0){ud(e);for(let t=0;t<iv.length;t++){const d=iv[t];if(d!==c){score[d]-=we;can[d]=1}}}else if(cov[e]===1){for(let t=0;t<iv.length;t++){const d=iv[t];if(inS[d]&&d!==c){score[d]+=we;break}}}cov[e]++}};
  const del=c=>{inS[c]=0;const i0=pos[c],l0=sol.pop();if(l0!==c){sol[i0]=l0;pos[l0]=i0}pos[c]=-1;score[c]=-score[c];can[c]=0;const l=CV[c];for(let q=0;q<l.length;q++){const e=l[q],we=w[e],iv=inv[e];cov[e]--;if(cov[e]===0){ua(e);for(let t=0;t<iv.length;t++){const d=iv[t];if(d!==c){score[d]+=we;can[d]=1}}}else if(cov[e]===1){for(let t=0;t<iv.length;t++){const d=iv[t];if(inS[d]){score[d]-=we;break}}}}};
  while(unc.length){const e=unc[rnd(unc.length)],iv=inv[e];let bc=-1,bs=-1;for(let t=0;t<iv.length;t++){const d=iv[t];if(score[d]>bs||(score[d]===bs&&rnd(2))){bs=score[d];bc=d}}add(bc)}
  let best=sol.slice(),it=0,tabu=-1;const end=Date.now()+ms;
  const pick=()=>{let bc=-1,bs=-Infinity,bt=Infinity;for(let i=0;i<sol.length;i++){const c=sol[i];if(c===tabu)continue;const sc=score[c];if(sc>bs||(sc===bs&&st[c]<bt)){bc=c;bs=sc;bt=st[c]}}return bc};
  while(sol.length>0){if(!(++it&63)&&Date.now()>=end)break;if(!unc.length){best=sol.slice();if(sol.length<=1)break;del(pick());continue}if(sol.length<1)break;const r=pick();if(r<0)break;del(r);st[r]=it;const e=unc[rnd(unc.length)],iv=inv[e];let bc=-1,bs=-1,bt=Infinity;for(let t=0;t<iv.length;t++){const d=iv[t];if(!can[d])continue;const sc=score[d];if(sc>bs||(sc===bs&&st[d]<bt)){bc=d;bs=sc;bt=st[d]}}if(bc<0)bc=iv[rnd(iv.length)];add(bc);st[bc]=it;tabu=bc;for(let i=0;i<unc.length;i++){const x=unc[i];w[x]++;const v=inv[x];for(let t=0;t<v.length;t++)score[v[t]]++}}
  const str=y=>{let o='',x=y;for(let i=0;i<n;i++){o+=SG[x%3];x=Math.floor(x/3)}return o},out=best.map(j=>str(cc[j]));
  let worst=0;for(const t of T){let b=n;for(const c of out){let f=0;for(let i=0;i<n;i++)if(t[i]!==c[i])f++;if(f<b){b=f;if(b===0)break}}if(b>worst)worst=b}
  return {cols:out,total:T.length,worst,ok:worst<=k,inside:used,forcedInside:used&&!inside};
}
function job({radices,k,ms,seed,w,budget,target,cond}){
  if(cond)return condReduce(cond.cols,k,ms,seed,cond.inside);
  if(budget){const x=budgetSearch(radices,k,budget,w,ms,seed||7);return {...x,budget:true,p14:score(x.cols,radices,w)}}
  if(target){const x=budgetSearch(radices,k,0,w,ms,seed||7,target);return {...x,budget:true,target,p14:score(x.cols,radices,w)}}
  const x=run(radices,k,ms,seed);if(!w)return x;
  const cols=bestLabels(x.cols,radices,w);return {cols,ver:verify(radices,k,cols),p14:score(cols,radices,w)};
}
if(typeof self!=='undefined'&&self.postMessage&&typeof window==='undefined'){self.onmessage=e=>{try{self.postMessage({ok:true,...job(e.data)})}catch(err){self.postMessage({ok:false,error:String(err)})}}}
if(typeof module!=='undefined')module.exports={run,verify,rwls,job,bestLabels,budgetSearch,score,condReduce};
