# Why the Lucas equation forces a long orbit

This is a self-contained elementary explanation of the Lucas step already
present in upstream `lem:o8-lucas`, not a new theorem. It clarifies which
part of the larger proof can be understood without a deep external input.
The exposition has AI authorship and self-review, not independent human review.

## Precise statement

Let s,t,z be integers with a=|s|>=7 and z!=0. If

    t²-s(s-2)tz+(s-2)²z²=1,

then |t|>exp(a-3). Conversely, for every such s there are positive
integers t,z satisfying this equation.

Put w=sgn(s)*(s-2)*z. Since sgn(s)*(s-2)>0, this gives

    t²-a*t*w+w²=1,       |s-2| divides w,       w!=0.

The divisibility is essential. The cubic norm equation by itself has
the small solution t=a,w=1 for every integer a. That family would
destroy the exponential-growth conclusion.

## Every solution runs along one recurrence

Let rho=(a+sqrt(a²-4))/2. It satisfies rho>1 and rho+rho^(-1)=a.
The integer a²-4 is not a square for a>=7: it lies strictly between
(a-1)² and a². Thus Z[rho] is a quadratic order and the displayed
equation says that t-w*rho has norm one.

Here one does not need a general unit theorem. Any positive element
v of Z[rho] of norm one can be multiplied by an integral power of rho
to obtain 1<=v<rho. This multiplication stays in the order because
rho^(-1)=a-rho also belongs to it. Write the resulting element as
A+B*rho with A,B integers. Its conjugate is v^(-1), so

    B=(v-v^(-1))/(rho-rho^(-1)).

The function x-x^(-1) increases on positive x. Hence 0<=B<1,
forcing B=0 and v=1. Undoing the multiplication shows that all positive
norm-one elements are powers of rho. If the original element is
negative, change its sign first; absolute values of t,w are unaffected.

Define integers U0=0, U1=1, and U(k+1)=a*Uk-U(k-1). Induction gives

    rho^k=Uk*rho-U(k-1).

Comparing coefficients for positive and negative powers shows that a
solution with w!=0 has, for some k>=1,

    |w|=Uk,       |t| in {U(k-1), U(k+1)}.

This is the orbit: successive solutions correspond to successive powers
of one explicitly known unit, rather than arbitrary points of a conic.

## Divisibility forces many steps

Modulo a-2 the recurrence becomes U(k+1)=2Uk-U(k-1), so Uk=k.
Modulo a+2 it becomes U(k+1)=-2Uk-U(k-1), so
Uk=(-1)^(k-1)*k. Both formulas follow immediately by induction.

When s>0, |s-2|=a-2 divides Uk, hence k is a positive multiple of a-2.
When s<0, |s-2|=a+2 divides Uk, hence k is a positive multiple of a+2.
In either case k>=a-2.

The recurrence is increasing and gives Uk>=(a-1)^(k-1) for k>=1.
Consequently

    |t| >= (a-1)^(a-4) > exp(a-3).

For the last strict inequality, a>=7 implies log(a-1)>3/2 and
(3/2)*(a-4)>a-3. The elementary estimate e<3 proves log(6)>3/2,
since 3^(3/2)<6. No asymptotic estimate is being used.

For existence choose k=a-2 if s>0, or k=a+2 if s<0. Set
t=U(k+1), w=Uk and z=w/|s-2|. These are positive integers,
and the recurrence (or the norm identity for rho powers) gives the
required equation. This proves both directions of the stated lemma.

## Why the obvious cubic rewrite does not yet reduce precision

Introducing w=(s-2)z changes the quartic expression into

    t²-s*t*w+w²-1=0,       w-(s-2)z=0.

It is tempting to use the first expression's ordinary degree three to
lower comparison precision from 40 to 32. But if w is only an auxiliary
rational expression, and B bounds the original integer labels, its
available bound is |w|<=(B+2)B, of order B². Assigning weight two to w
restores weighted degree four to the first expression. The previous
height threshold is therefore unchanged.

Alternatively, w could be a new hidden integer label with its own
elliptic point and contact-to-height control. Then degree three really
could be used, but one must also enforce the second relation and pay
for the additional point, comparisons and scales. That is a distinct
construction whose total cost and completeness are unassessed here.
The counterexample t=s,w=1 rules out dropping the divisibility relation,
not this more elaborate possible construction.

## Place in the full proof

The local tests and first height contradiction force the original
integer-label discrepancy to vanish. Only then does this elementary
lemma give log B>|s|-3. The second height contradiction compares that
growth with the small scalar height and forces beta to equal its integer
label. See `../overnight-20261107/COMPARISON_LEMMA.md` and
`../overnight-20261106/INTUITIVE_PROOF.md` for those interfaces.

The elliptic-curve integer-label calculation, the contact-to-height
theorem, and the simultaneous-prime construction for a common witness
are not established by this argument. They remain separate indispensable
inputs to the current architecture. This note expands the elementary
Lucas ingredient rather than obscuring those dependencies.
