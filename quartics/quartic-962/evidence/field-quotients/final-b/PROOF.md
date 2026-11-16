# Fusing the last weight multiplication

This add-on reduces the initial combined candidate from 1,025 to 1,016
coordinates. Its nine new equations are quadratic. It saves one coordinate
in each detector, independently of the 49 savings in the first quotient patch.

The previous equations defined R=di/ep, n=nw, s=n², B=R*s. Replace the
three coordinates R,s,B with two coordinates v,B and the equations

    ep*v=di*n,     B=n*v.

Keep the equation that defines n and the original trace inverse.
The existing positive-scale proof gives ep nonzero on every candidate zero,
since F*ep=(A*delta)^5 is nonzero. Thus v=di*n/ep=R*n, so both systems
give exactly B=di*n²/ep. From an old solution set v=R*n. From a new solution
restore R=di/ep and s=n². These maps preserve every other semantic value
and the input. No extra nonzero assumption is imposed on n.

`patch.json` records the two exact replacements. `verification.json` checks
all 958 raw gates, replays the 927 reduction operations, and checks both
the numerator and denominator of every emitted new quotient against its
named values. `measured-census.json` gives the count and degree.
