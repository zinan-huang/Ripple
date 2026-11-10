\\ M8(Gamma0(2)) in the basis E4(t)^2, E4(t)E4(2t), E4(2t)^2: Delta2 = (eta(t)eta(2t))^8 and P = T*Delta2.
N = 30;
e = 1 + 240*sum(n = 1, N, sigma(n,3)*q^n) + O(q^(N+1)); f = subst(e, q, q^2);
et = prod(n = 1, N, 1 - q^n + O(q^(N+1)));
D2 = q*et^8*subst(et, q, q^2)^8;
a = q*et^24; b = q^2*subst(et, q, q^2)^24;
P = (a^2 + 24*a*b + 4096*b^2)/(a*b) * D2;
M = matrix(3, 3, i, j, polcoeff([e^2, e*f, f^2][j], i - 1));
cD = matsolve(M, vector(3, i, polcoeff(D2, i - 1))~);
cP = matsolve(M, vector(3, i, polcoeff(P, i - 1))~);
print("Delta2 = ", cD, " . [e^2, ef, f^2]   residual O(q^", valuation(D2 - cD[1]*e^2 - cD[2]*e*f - cD[3]*f^2, q), ")");
print("P      = ", cP, " . [e^2, ef, f^2]   residual O(q^", valuation(P - cP[1]*e^2 - cP[2]*e*f - cP[3]*f^2, q), ")");
print("Delta2^3 - a b: O(q^", valuation(D2^3 - a*b, q), ")");
