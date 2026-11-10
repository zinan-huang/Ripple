\\ The cleared form F = sum c_ij P^i Q^(30-i)(t) P^j Q^(30-j)(29t), P = 3600 T Delta2, Q = 3600 Delta2,
\\ in the E4 basis; exact check of the first N coefficients and the heights that fix the packing widths.
default(parisize, 4*10^9);
Psi = read("psi29.txt");      \\ Psi(T(29t), T(t)) = 0 with X = T(29 t) side? symmetric anyway
N = 3600; K = N\29 + 1;
e = 1 + 240*sum(n = 1, N, sigma(n,3)*q^n) + O(q^(N+1)); f = subst(e, q, q^2);
P = 248*e^2 - 616*e*f + 3968*f^2; Q = -e^2 + 17*e*f - 16*f^2;
ec = 1 + 240*sum(n = 1, K, sigma(n,3)*q^n) + O(q^(K+1)); fc = subst(ec, q, q^2);
Pc = 248*ec^2 - 616*ec*fc + 3968*fc^2; Qc = -ec^2 + 17*ec*fc - 16*fc^2;
absS(s) = my(v = Vec(s)); Ser(apply(abs, v), q) + O(q^(#v));
mh(s) = vecmax(apply(c -> #binary(abs(c)), Vec(truncate(s))));
\\ compact side: T_y = sum_x c_{x,y} Pc^x Qc^(30-x), y = power on the wide side
PcP = vector(31, i, Pc^(i-1)); QcP = vector(31, i, Qc^(i-1));
Ty = vector(31, y1, sum(x = 0, 30, polcoeff(polcoeff(Psi, x, X), y1 - 1, Y) * PcP[x+1]*QcP[31-x]));
TyA = vector(31, y1, sum(x = 0, 30, abs(polcoeff(polcoeff(Psi, x, X), y1 - 1, Y)) * absS(PcP[x+1]*QcP[31-x])));
print("compact: max bits of T_y coefficients ", vecmax(apply(mh, Ty)), " (abs bound ", vecmax(apply(mh, TyA)), ")");
\\ wide side
t0 = getwalltime();
PP = vector(31, i, if (i == 1, 1 + O(q^(N+1)), 0)); for (i = 2, 31, PP[i] = PP[i-1]*P);
QQ = vector(31, i, if (i == 1, 1 + O(q^(N+1)), 0)); for (i = 2, 31, QQ[i] = QQ[i-1]*Q);
F = sum(y = 0, 30, PP[y+1]*QQ[31-y]*subst(Ty[y+1], q, q^29));
print("F: first nonzero coefficient index ", valuation(F, q), " (precision ", N, "), ", getwalltime() - t0, " ms");
print("wide: max bits of P^y Q^(30-y) ", vecmax(vector(31, y, mh(PP[y]*QQ[32-y]))));
FA = sum(y = 0, 30, absS(PP[y+1]*QQ[31-y])*subst(TyA[y+1], q, q^29));
print("abs bound on F coefficients: max bits ", mh(FA));
print("bits of P, Q coefficients at N: ", mh(P), " ", mh(Q));
