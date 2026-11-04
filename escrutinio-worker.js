/* Quiniela Lab: escrutinio exacto. Calcula los fallos de la mejor columna para todos los resultados posibles. */
function bfs(lists,cols){
  const n=lists.length,r=lists.map(l=>l.length),mul=[];let N=1;for(let i=0;i<n;i++){mul[i]=N;N*=r[i]}
  const map=lists.map(l=>Object.fromEntries(l.map((s,i)=>[s,i]))),d=new Uint8Array(N).fill(255),q=new Int32Array(N);let h=0,t=0;
  for(const c of cols){let x=0;for(let i=0;i<n;i++)x+=map[i][c[i]]*mul[i];if(d[x]===255){d[x]=0;q[t++]=x}}
  while(h<t){const x=q[h++],dx=d[x];for(let i=0;i<n;i++){const ri=r[i];if(ri<2)continue;const m=mul[i],base=x-(Math.floor(x/m)%ri)*m;for(let v=0;v<ri;v++){const y=base+v*m;if(d[y]===255){d[y]=dx+1;q[t++]=y}}}}
  return {d,N};
}
const LIMIT=15000000;
function analyze(cols,n,probs){
  const marks=[];for(let i=0;i<n;i++){const u=new Set();for(const c of cols)u.add(c[i]);marks.push(['1','X','2'].filter(s=>u.has(s)))}
  let sizeM=1;for(const l of marks)sizeM*=l.length;if(sizeM>LIMIT)return {tooBig:true};
  const a=bfs(marks,cols),counts=new Array(n+1).fill(0);let worst=0;for(let i=0;i<a.N;i++){const v=a.d[i];counts[v]++;if(v>worst)worst=v}
  const out={counts,worst,N:a.N};
  if(probs){
    out.pMarks=marks.reduce((x,l,i)=>x*l.reduce((y,s)=>y+probs[i][s],0),1);
    if(Math.pow(3,n)<=LIMIT){
      const all=Array.from({length:n},()=>['1','X','2']),b=bfs(all,cols),h=n>>1;
      const prods=(from,to)=>{let w=[1];for(let i=from;i<to;i++){const nx=new Float64Array(w.length*3);for(let k=0;k<3;k++){const pk=probs[i][all[i][k]];for(let j=0;j<w.length;j++)nx[j+k*w.length]=w[j]*pk}w=nx}return w};
      const lo=prods(0,h),hi=prods(h,n),pd=new Array(n+1).fill(0);let x=0;for(let j=0;j<hi.length;j++){const hj=hi[j];for(let i=0;i<lo.length;i++)pd[b.d[x++]]+=lo[i]*hj}
      out.pd=pd;
    }
  }
  return out;
}
/* Agrupa columnas sencillas en boletos con dobles y triples, sin añadir ni repetir apuestas. */
function groupCols(cols,ms,seed0){
  const SG=['1','X','2'],n=cols[0].length,mul=[];for(let i=0,m=1;i<n;i++,m*=3)mul[i]=m;
  const code=c=>{let x=0;for(let i=0;i<n;i++)x+=SG.indexOf(c[i])*mul[i];return x},all=[...new Set(cols.map(code))],dig=(x,i)=>Math.floor(x/mul[i])%3;
  let s=(seed0>>>0)||1;const rnd=k=>{s^=s<<13;s>>>=0;s^=s>>>17;s^=s<<5;s>>>=0;return s%k};
  const moves=[];for(let i=0;i<n;i++)for(let v=0;v<3;v++)moves.push([i,v]);
  const grow=(seedC,rem)=>{let el=[seedC];const mask=Array.from({length:n},(_,i)=>1<<dig(seedC,i)),base=Array.from({length:n},(_,i)=>dig(seedC,i));
    for(let i=moves.length-1;i>0;i--){const j=rnd(i+1),t=moves[i];moves[i]=moves[j];moves[j]=t}
    let changed=true;while(changed){changed=false;for(const [i,v] of moves){if(mask[i]&(1<<v))continue;const add=[];let ok=true;for(const e of el){if(dig(e,i)!==base[i])continue;const y=e+(v-base[i])*mul[i];if(!rem.has(y)){ok=false;break}add.push(y)}if(ok){mask[i]|=1<<v;el=el.concat(add);changed=true}}}
    return {el,mask}};
  let best=null;const end=Date.now()+ms;
  do{const rem=new Set(all);let list=all.slice();const boxes=[];
    while(rem.size){list=list.filter(x=>rem.has(x));let top=null;const K=Math.min(list.length,32);for(let t=0;t<K;t++){const g=grow(list[t===0?0:rnd(list.length)],rem);if(!top||g.el.length>top.el.length)top=g;if(top.el.length===rem.size)break}for(const e of top.el)rem.delete(e);boxes.push({mask:top.mask,size:top.el.length});if(best&&boxes.length>=best.length)break}
    if(!rem.size&&(!best||boxes.length<best.length))best=boxes;
  }while(Date.now()<end&&best.length>1);
  const signs=b=>b.mask.map(m=>SG.filter((_,v)=>m&(1<<v)).join(''));
  const seen=new Set(),target=new Set(all);let ok=true;for(const b of best){const sg=signs(b);let exp=[0];sg.forEach((p,i)=>{const nx=[];for(const x of exp)for(const c of p)nx.push(x+SG.indexOf(c)*mul[i]);exp=nx});for(const x of exp){if(seen.has(x)||!target.has(x))ok=false;seen.add(x)}}if(seen.size!==target.size)ok=false;
  return {ok,boxes:best.map(b=>({signs:signs(b),size:b.size})).sort((a,b)=>b.size-a.size),total:all.length};
}
if(typeof self!=='undefined'&&self.postMessage&&typeof window==='undefined'){self.onmessage=e=>{try{const d=e.data;if(d.group){const g=groupCols(d.cols,d.ms||1500,d.seed||7);self.postMessage({ok:g.ok,group:true,...g});return}const {cols,n,probs}=d;self.postMessage({ok:true,...analyze(cols,n,probs)})}catch(err){self.postMessage({ok:false,error:String(err)})}}}
if(typeof module!=='undefined')module.exports={analyze,groupCols};
