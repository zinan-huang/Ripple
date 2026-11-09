import cmath, math
def q_of(t): return cmath.exp(2j*math.pi*t)
def sig(n, k): return sum(d**k for d in range(1, n+1) if n % d == 0)
def E(k, c, t, N=200):
    q = q_of(t); return 1 + c*sum(sig(n, k-1)*q**n for n in range(1, N))
E2 = lambda t: E(2, -24, t); E4 = lambda t: E(4, 240, t); E6 = lambda t: E(6, -504, t)
def eta24(t, N=400):
    q = q_of(t); p = 1
    for n in range(1, N): p *= (1 - q**n)
    return q*p**24
def x2(t):
    a, b = eta24(t), eta24(2*t); return 256*a*b/(a+64*b)**2
def F21(a, b, c, x, N=400):
    s, term = 0, 1
    for n in range(N):
        s += term; term *= (a+n)*(b+n)/((c+n)*(n+1))*x
    return s
def F32(x, N=400):
    s, term = 0, 1
    for n in range(N):
        s += term; term *= (0.25+n)*(0.5+n)*(0.75+n)/((1+n)**3)*x
    return s
Z2 = lambda t: 2*E2(2*t) - E2(t)
for t in [complex(0.1, 0.9), complex(0, math.sqrt(58)/2)]:
    x = x2(t)
    print("tau", t, "x2", x, "3F2", F32(x), "Z", Z2(t), "2F1^2", F21(1/8, 3/8, 1, x)**2)
t = complex(0, math.sqrt(58)/2)
print("x2(tau58)*99^4 =", x2(t)*99**4)
t = (1 + 1j*math.sqrt(163))/2; y = math.sqrt(163)/2
print("s2(tau163)", E4(t)/E6(t)*(E2(t) - 3/(math.pi*y)), 77265280/90856689)
# level-2 s-value at tau58
t = complex(0, math.sqrt(58)/2); y = t.imag
DE2 = lambda s: (E2(s)**2 - E4(s))/12
a, b = eta24(t), eta24(2*t)
Da, Db = a*E2(t), 2*b*E2(2*t)
w = E2(t) + 2*E2(2*t) - 2*(Da + 64*Db)/(a + 64*b)
Z = Z2(t); DZ = 2*2*DE2(2*t) - DE2(t)
x = x2(t)
print("w^2/(Z^2(1-x)) =", w**2/(Z**2*(1-x)))
E2s = E2(t) - 3/(math.pi*y)
c = -E2s/(6*w) - (DZ - E2(t)*Z/6)/(w*Z)
print("c(tau58) =", c, " 1103/26390 =", 1103/26390)
