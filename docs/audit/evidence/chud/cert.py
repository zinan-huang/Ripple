from sympy import *
e2,e4,e6,P,s,Ii,D20,D21,D30,u1,u2=symbols('e2 e4 e6 pc s I D20 D21 D30 u1 u2')
L=-(81+s*Ii)/82
m=-(1-s*Ii)**3/6724
den=e4**3-e6**2
J1=-2*P*Ii*1728*e4**2*e6
J2=2*1728*P**2*(e2*e4**2*e6/3-4*e4*e6**2/3-e4**4)
A=3*D21-Rational(122,41)*D30
Q=(1+L)*L*(u1**2*A-Rational(489,82)*D20*u2)+3*u1*m*D20*(Rational(81,82)+L)
cinv=-(61+20*s*Ii)/41
R=163*D20*den*(-P*e2*e4*e6+Rational(6,163)*s*e4*e6+P*(3*e4**3+4*e6**2))+6912*P*e4**3*e6**2*(122*D30-123*D21)
# Step R: 1728*pc*e4*R = 41*cinv*den^2*Q - c1*(u1*den-J1) + c2*(u2*den-J2) - Cs*(s^2-163) - CI*(I^2+1)
c1=41*cinv*((1+L)*L*A*(u1*den+J1)+3*m*D20*(Rational(81,82)+L)*den)
c2=41*cinv*(1+L)*L*Rational(489,82)*D20*den
rest=expand(41*cinv*den**2*Q - c1*(u1*den-J1) + c2*(u2*den-J2) - 1728*P*e4*R)
# rest should be in ideal (s^2-163, I^2+1)
G=[s**2-163, Ii**2+1]
qs,r=reduced(rest,G,s,Ii,u1,u2,e2,e4,e6,P,D20,D21,D30)
print("step R remainder:", r)
Cs,CI=qs
# verify
chk=expand(41*cinv*den**2*Q - c1*(u1*den-J1) + c2*(u2*den-J2) - Cs*(s**2-163) - CI*(Ii**2+1) - 1728*P*e4*R)
print("step R check:", chk)
print("Cs terms", len(Add.make_args(expand(Cs))), "CI terms", len(Add.make_args(expand(CI))))
open('certR.txt','w').write("c1 := "+str(factor(c1))+"\nc2 := "+str(factor(c2))+"\nCs := "+str(factor(Cs))+"\nCI := "+str(factor(CI))+"\n")
# Step T
N=-640320**3
T=90856689*e4*(e2*P*s-6)-77265280*e6*P*s
K6=90856689*((7*N-6912)*163*D20+2*N*(244*D30-246*D21)*(N-1728))-77265280*(N-1728)*163*D20
hrel=N*e6**2-(N-1728)*e4**3   # from j0*den = 1728 e4^3 with j0=N
M=163*D20*den*e6
Z=expand(M*T+90856689*s*R)
G2=[e6**2-Rational(N-1728,N)*e4**3, s**2-163, D30-solve(K6,D30)[0]]
qq,r2=reduced(Z,G2,e6,s,D30,e2,e4,P,D20,D21)
print("step T remainder:", simplify(r2))
q_rel,q_s,q_K=qq
# express in terms of original hrel, K6 polys: e6^2 - c e4^3 = hrel/N ; D30 - sol = K6/coeff(K6,D30)
kc=Poly(K6,D30).coeffs()[0]
chk2=expand(M*T+90856689*s*R - q_rel*hrel/N - q_s*(s**2-163) - q_K*K6/kc)
print("step T check:", chk2)
open('certT.txt','w').write("q_rel/N := "+str(factor(q_rel/N))+"\nq_s := "+str(factor(q_s))+"\nq_K/kc := "+str(factor(q_K/kc))+"\n")
print("kc", kc)
