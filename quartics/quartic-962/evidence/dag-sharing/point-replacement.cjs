// Quartic coordinates for the halfpoint. half[n].x represents t=y/x,
// and half[n].y represents h=x/t-t/2. Both are elements of Q(sqrt(2)).
let points={};for(let n of names){
 const t=half[n].x,h=half[n].y,u=fsq(n+'.chart.tSquare',t),x=fsq(n+'.chart.x',h);
 const rhs=fsub(x,fscale(u,Q(1,4)));
 residual(n+'.chart.equation.0',sub(add(mul(u[0],rhs[0]),scale(mul(u[1],rhs[1]),2)),D[0]));
 residual(n+'.chart.equation.1',sub(add(mul(u[0],rhs[1]),mul(u[1],rhs[0])),D[1]));
 const y=fmul(n+'.chart.y',h,fsub(fscale(u,Q(1,2)),x));
 points[n]={x:saveF(n+'.x',x),y:saveF(n+'.y',y)};
}
