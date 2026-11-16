// Exact degree-12 square completion, requiring four field assignments.
const rawFmul=(a,b)=>[add(mul(a[0],b[0]),scale(mul(a[1],b[1]),2)),add(mul(a[0],b[1]),mul(a[1],b[0]))];
function rawPolynomial6(coeff,basis){
 let out=fc(0);
 for(let k=0;k<coeff.length;k++){
  let term=k<=3?basis[k]:rawFmul(basis[3],basis[k-3]);
  out=fadd(out,fscale(term,coeff[k]));
 }
 return out;
}
let squareQ=Array.from({length:7},()=>Q(0));squareQ[6]=Q(1);
for(let j=5;j>=0;j--){let known=Q(0);for(let a=j+1;a<=6;a++)for(let b=j+1;b<=6;b++)if(a+b===j+6)known=qadd(known,qmul(squareQ[a],squareQ[b]));squareQ[j]=qmul(qadd(qmul(aCoeffs[j+6],qinv(aCoeffs[12])),qneg(known)),Q(1,2));}
let squareR=aCoeffs.slice();for(let a=0;a<=6;a++)for(let b=0;b<=6;b++)squareR[a+b]=qadd(squareR[a+b],qneg(qmul(aCoeffs[12],qmul(squareQ[a],squareQ[b]))));
if(squareR.slice(6).some(c=>c[0]))throw Error('square completion identity failed');
function log(name,p,e){
 let w=fmul(name+'.w',D,fsq(name+'.fSquare',p.f));
 if(e===52){
  let w2=fsq(name+'.wPower2',w),w3=fmul(name+'.wPower3',w2,w),basis=[fc(1),w,w2,w3];
  let rawq=rawPolynomial6(squareQ,basis),q=saveF(name+'.squareRootPolynomial',rawq.map((v,j)=>assign(name+'.squareRootPolynomial.'+j,v)));
  let rawout=fadd(fscale(rawFmul(q,q),aCoeffs[12]),rawPolynomial6(squareR.slice(0,6),basis));
  let out=saveF(name+'.polynomial',rawout.map((v,j)=>assign(name+'.polynomial.'+j,v)));
  return fmul(name,p.z,out);
 }
 let w2=fsq(name+'.wPower2',w),rawout=rawPolynomial6(aCoeffs.slice(0,4),[fc(1),w,w2,rawFmul(w2,w)]);
 let out=saveF(name+'.polynomial',rawout.map((v,j)=>assign(name+'.polynomial.'+j,v)));
 return fmul(name,p.z,out);
}
