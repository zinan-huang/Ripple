\\ Diagonal Psi_29(X, X): factorization over Q and separation of the simple root T0 = 256*99^4 - 104.
default(parisize, 10^9); default(realprecision, 60);
Psi = read("psi29.txt"); T0 = 256*99^4 - 104;
P1 = subst(Psi, Y, X); f = factor(P1);
print("degree ", poldegree(P1), "; factors [degree, multiplicity]: ", vector(#f~, i, [poldegree(f[i,1]), f[i,2]]));
print("multiplicity of T0: ", valuation(P1, X - T0));
print("distance from T0 to the nearest other root: ", vecmin(apply(z -> abs(z - T0), polroots(P1/(X - T0)))));
