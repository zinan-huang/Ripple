\\ Degree-29 modular equation Psi_29(X,Y) for the Gamma0(2)+ Hauptmodul
\\ T = (eta(t)/eta(2t))^24 + 24 + 4096 (eta(2t)/eta(t))^24 = 256/x2 - 104 = 1/q + 4372 q + ...
\\ Psi_29(T(t), T(29 t)) = 0; computed from power sums of T((t+k)/29), T(29 t).
default(parisize, 2*10^9);
p = 29; D = p + 1; M = p*D; N = M + 2;
ps = prod(n = 1, N, 1 + q^n + O(q^(N+1)));
h = ps^(-24) / q;                         \\ (eta(t)/eta(2t))^24 = 1/q - 24 + 276 q - ...
T = h + 24 + 4096 / h;
U = q*T;                                  \\ 1 + 0 q + 4372 q^2 + ...
\\ Upow[j+1] = U^j mod q^(M+1)
Upow = vector(M + 1); Upow[1] = 1 + O(q^(M+1)); for (j = 1, M, Upow[j+1] = Upow[j]*U);
\\ coefficient of q^e in T^j  (e >= -j)
cT(j, e) = polcoeff(truncate(Upow[j+1]), e + j);
\\ reduce a principal part (vector pp[k+1] = coeff of q^(-k), k = 0..K) to a polynomial in Y = T
{reduce(pp) = my(K = #pp - 1, P = 0, v = pp, d);
  forstep (j = K, 0, -1, d = v[j+1]; if (d, P += d*Y^j;
    for (k = 0, j, v[k+1] -= d*cT(j, -k))));
  P;}
s = vector(D);
{for (m = 1, D,
  my(pp = vector(p*m + 1));
  \\ T(29 t)^m: terms q^(29 e), e in [-m, 0]
  for (ee = -m, 0, pp[-p*ee + 1] += cT(m, ee));
  \\ sum_k T((t+k)/29)^m = 29 * sum_{e = 0 mod 29} [q^e]T^m q^(e/29): e = 0 and e = -29 (if m >= 29)
  pp[1] += p*cT(m, 0);
  if (m >= p, pp[2] += p*cT(m, -p));
  s[m] = reduce(pp));}
e = vector(D + 1); e[1] = 1;
for (k = 1, D, e[k+1] = sum(i = 1, k, (-1)^(i-1) * e[k-i+1] * s[i]) / k);
Psi = sum(k = 0, D, (-1)^k * e[k+1] * X^(D-k));
print("degX ", poldegree(Psi, X), " degY ", poldegree(Psi, Y));
print("symmetric ", Psi == substvec(Psi, [X, Y], [Y, X]));
co = concat(vector(D + 1, a, Vec(polcoeff(Psi, a-1, X))));
nz = select(c -> c != 0, co);
print("nonzero coefficients ", #nz);
print("max bits ", vecmax(apply(c -> #binary(abs(c)), nz)));
print("total bits ", vecsum(apply(c -> #binary(abs(c)), nz)));
T0 = 256*99^4 - 104;
print("Psi(T0,T0) = ", subst(subst(Psi, X, T0), Y, T0));
P1 = subst(Psi, Y, X);
print("multiplicity of T0 in Psi(X,X): ", valuation(P1, X - T0));
print("dPsi/dX(T0,T0) = ", subst(subst(deriv(Psi, X), X, T0), Y, T0) != 0);
f = factor(P1); print("factor degrees of Psi(X,X): ", vector(#f~, i, [poldegree(f[i,1]), f[i,2]]));
system(": > psi29.txt"); write("psi29.txt", Psi);   \\ truncate first: write appends
