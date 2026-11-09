import re, sys
from fractions import Fraction as Fr
from math import comb
src = open(sys.argv[1]).read()
terms = [(int(c), int(x), int(y)) for c, x, y in re.findall(r"⟨\((-?\d+) : Int\), (\d+), (\d+)⟩", src)]
print("terms", len(terms), "max deg", max(t[1] for t in terms), max(t[2] for t in terms),
      "max coeff digits", max(len(str(abs(t[0]))) for t in terms))
j0 = -640320**3
def beta(a, b):
    s = 0
    for c, x, y in terms:
        if x >= a and y >= b:
            s += c * comb(x, a) * comb(y, b) * j0**(x - a + y - b)
    return s
B = {}
for a in range(4):
    for b in range(4):
        if a + b <= 3:
            B[(a, b)] = beta(a, b)
print("beta00 == 0:", B[(0,0)] == 0)
print("beta10, beta01 zero:", B[(1,0)] == 0, B[(0,1)] == 0)
print("symmetry 20/02, 21/12, 30/03:", B[(2,0)] == B[(0,2)], B[(2,1)] == B[(1,2)], B[(3,0)] == B[(0,3)])
print("beta20 != 0:", B[(2,0)] != 0, "digits", len(str(abs(B[(2,0)]))))
print("41*beta11 == 81*beta20:", 41 * B[(1,1)] == 81 * B[(2,0)])
C = Fr(244 * B[(3,0)] - 82 * B[(2,1)], 163 * B[(2,0)])
s2 = Fr(7 * j0 - 6912, j0 - 1728) + 6 * j0 * C
print("C3/D =", C)
print("s2 =", s2, " target 77265280/90856689 match:", s2 == Fr(77265280, 90856689))
print("(1-s2)/6 =", (1 - s2) / 6, " == 13591409/545140134:", (1 - s2) / 6 == Fr(13591409, 545140134))
