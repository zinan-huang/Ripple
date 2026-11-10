\\ R5: real roots of the cofactor C = Psi_29(X,X)/(X - T0) and its Taylor coefficients at a = 1.1e10.
default(parisize, 10^9); default(realprecision, 60);
Psi = read("psi29.txt"); T0 = 256*99^4 - 104;
P1 = subst(Psi, Y, X); C = P1/(X - T0);
r = polrootsreal(C); print("real roots of cofactor: ", #r);
print(apply(z->round(z), r));
print("sturm count of cofactor roots in [2*10^10, 3*10^10]: ", polsturm(C, [2*10^10, 3*10^10]));
print("sturm count of P1 roots in [2*10^10, 3*10^10]: ", polsturm(P1, [2*10^10, 3*10^10]));
print("lead sign ", sign(pollead(C)), " deg ", poldegree(C));
rr = polroots(C); print("max real part of roots: ", vecmax(apply(real, rr)));
for(k=0,2, a = [10^10*11/10, 2*10^10, 15*10^9][k+1]; D = subst(C, X, X + a); v = Vec(D); print("a=",a," signs: ", vecsort(Set(apply(sign, v))), " min bits ", vecmin(apply(z->if(z, log(abs(z))/log(2), 0), v))));
print("bits of coefficients of C: ", vecmax(apply(z->if(z,log(abs(z))/log(2),0), Vec(C))));
