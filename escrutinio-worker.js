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
if(typeof self!=='undefined'&&self.postMessage&&typeof window==='undefined'){self.onmessage=e=>{try{const {cols,n,probs}=e.data;self.postMessage({ok:true,...analyze(cols,n,probs)})}catch(err){self.postMessage({ok:false,error:String(err)})}}}
if(typeof module!=='undefined')module.exports={analyze};
