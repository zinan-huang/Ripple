\\ Second-order (Masser) extraction of c58 = 1103/26390 from Psi_29 at the smooth point (T0, T0).
\\ Notation (CHUD-PAPER 4.2): a = eta(t)^24, b = eta(2t)^24, x = 256ab/(a+64b)^2, T = 256/x - 104,
\\ s = (a-64b)/(a+64b), Z = 2E2(2t) - E2(t), w = D log x, g = D T, dF = D F - k E2 F/12 (Serre).
default(parisize, 10^9); default(realprecision, 200);
Psi = read("psi29.txt");
T0 = 256*99^4 - 104; x0 = 1/99^4;
dX = deriv(Psi, X); dXX = deriv(dX, X); dXY = deriv(dX, Y);
ev(P) = substvec(P, [X, Y], [T0, T0]);
B = ev(dX); A = ev(dXX) - ev(dXY);
print("Psi(T0,T0) = ", ev(Psi), ";  Psi_X(T0,T0) != 0: ", B != 0, ";  bits of Psi_X, A: ", #binary(abs(B)), ", ", #binary(abs(A)));
r = -2*A/B; print("-2A/B = ", r);
\\ q-series identities (checked to O(q^41)): w = Z s, dZ = Z^2 (1/12 - s/4)
N = 40;
E2q = 1 - 24*sum(n = 1, N, sigma(n)*q^n) + O(q^(N+1));
Zq = 2*subst(E2q, q, q^2) - E2q;
et = prod(n = 1, N, 1 - q^n + O(q^(N+1)));
aq = q*et^24; bq = q^2*subst(et, q, q^2)^24;
xq = 256*aq*bq/(aq + 64*bq)^2; sq = (aq - 64*bq)/(aq + 64*bq);
Dq(f) = q*deriv(f, q);
print("w - Z s: O(q^", valuation(Dq(xq)/xq - Zq*sq, q), ");  dZ - Z^2(1/12 - s/4): O(q^", valuation(Dq(Zq) - E2q*Zq/6 - Zq^2*(1/12 - sq/4), q), ")");
\\ exact evaluation in Q(s0), s0 = sqrt(1 - x0) > 0 at tau58
m = sv^2 - (1 - x0);
dgg = Mod(-x0*(sv/12 - 5*(1 - x0)/4 - x0/2)/(256*(1 - x0)), m);    \\ dg/g^2
E2g = 3*(r - 2*dgg);                                                 \\ E2*/g from 2 dg/g^2 + E2*/(3g) = -2A/B
c = -E2g*(-256/x0)/6 - Mod((1/12 - sv/4)/sv, m);                     \\ c58 = -E2*/(6w) - dZ/(wZ)
print("c58 = ", lift(c), ";  == 1103/26390: ", lift(c) == 1103/26390);
\\ numerical cross-check at tau58 of every intermediate quantity
t = I*sqrt(58)/2; y = sqrt(58)/2; qn = exp(2*Pi*I*t);
E2n(z) = 1 - 24*suminf(n = 1, sigma(n)*exp(2*Pi*I*n*z));
E4n(z) = 1 + 240*suminf(n = 1, sigma(n,3)*exp(2*Pi*I*n*z));
DE2n(z) = (E2n(z)^2 - E4n(z))/12;
an = eta(t,1)^24; bn = eta(2*t,1)^24; xn = 256*an*bn/(an + 64*bn)^2; sn = (an - 64*bn)/(an + 64*bn);
Zn = 2*E2n(2*t) - E2n(t); wn = Zn*sn; gn = -256*wn/xn;
DZn = 4*DE2n(2*t) - DE2n(t); dZn = DZn - E2n(t)*Zn/6;
Dwn = DZn*sn + Zn*(-xn*Zn/2); Dgn = -256*(Dwn/xn - wn^2/xn); dgn = Dgn - E2n(t)*gn/6;
E2st = E2n(t) - 3/(Pi*y);
print("x(tau58) - x0: ", abs(xn - x0));
print("dZ - Z^2(1/12 - s/4) at tau58: ", abs(dZn - Zn^2*(1/12 - sn/4)));
print("2dg/g^2 + E2*/(3g) - (-2A/B): ", abs(2*dgn/gn^2 + E2st/(3*gn) - r));
print("c58 numeric - 1103/26390: ", abs(-E2st/(6*wn) - dZn/(wn*Zn) - 1103/26390));
