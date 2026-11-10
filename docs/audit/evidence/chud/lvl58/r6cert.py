from sympy import *
Z,A,s,c,t,T1,T2 = symbols('Z A s c t T1 T2')
x0 = Rational(1,99**4); T0 = 256*99**4-104; sig = 1-x0
r = Rational(66716347,787408797714739200)
E = Z**2*(5-3*s)/2; F = Z**2*(5+3*s)/8
B = (Z+A)/2
E6a = Z**3*(9*s-7)/2; E6b = Z**3*(7+9*s)/16
e1 = c/3*(A*E-E6a); f1 = 2*c/3*(B*F-E6b)
e2 = c/3*(c/12*(A**2-E)*E + A*e1 - c/2*(A*E6a-E**2))
f2 = 2*c/3*(2*c/12*(B**2-F)*F + B*f1 - c*(B*E6b-F**2))
P0 = 248*E**2-616*E*F+3968*F**2; Q0 = -E**2+17*E*F-16*F**2
P1 = (496*E-616*F)*e1+(-616*E+7936*F)*f1; Q1 = (-2*E+17*F)*e1+(17*E-32*F)*f1
P2 = 496*e1**2-1232*e1*f1+7936*f1**2+(496*E-616*F)*e2+(-616*E+7936*F)*f2
Q2 = -2*e1**2+34*e1*f1-32*f1**2+(-2*E+17*F)*e2+(17*E-32*F)*f2
def quo(expr, var, rel_const):
    # divide expr (poly in var) by var**2 - rel_const, return quotient, check remainder 0
    q_, rem = div(Poly(expand(expr), var), Poly(var**2 - rel_const, var))
    assert expand(rem.as_expr()) == 0, ("nonzero remainder", factor(rem.as_expr()))
    return q_.as_expr()
def L(e):
    return str(expand(e)).replace('**','^')
out = {}
# hs2 from hR5: P0 - T0*Q0 = kap*(s^2-sig)
kap = quo(P0 - T0*Q0, s, sig); out['kap'] = factor(kap)
# Q0 value
out['k0'] = quo(Q0 - Rational(225,16)*Z**4*x0, s, sig)
T1v = -24591257856*Z*c*s
N1 = P1*Q0-P0*Q1
out['m1'] = quo(N1 - T1v*Q0**2, s, sig)
T2v = -192*Z*c**2*(21346578*A*s + 10673289*Z*s - 160099334*Z)
N2 = (P2*Q0-P0*Q2)*Q0**2-(P1*Q0-P0*Q1)*(2*Q0*Q1)
out['m2'] = quo(N2 - T2v*Q0**4, s, sig)
hMsub = t*(2*T2v - r*T1v**2) + 2*T1v
Aexpr = 215622*A*c*s*t + 107811*Z*c*s*t - 269360*Z*c*t + 1293732*s
D = expand(-38016*Z*c*Aexpr - hMsub)
# D = k1*(s^2-sig) + k2*(t^2+29/2)
k2, rem = div(Poly(D, t), Poly(t**2 + Rational(29,2), t)); rem = rem.as_expr(); k2 = k2.as_expr()
k1 = quo(rem, s, sig)
out['k1']=k1; out['k2']=k2
inner = 13236*Z*s*c*t + 26390*(2*A - 3*Z*s + Z)*c*t + 316680
lam = Rational(26390,107811)
out['mu'] = quo(expand(inner*s - lam*Aexpr), s, sig)
for k,v in out.items():
    print(k, ':=', L(v)); print()
