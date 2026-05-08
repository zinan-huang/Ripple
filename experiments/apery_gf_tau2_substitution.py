"""
Check the x = τ² substitution for the Apéry GF holonomic ODE.

Original:  x²(4−x) f'''(x) + x(10−3x) f''(x) + (2−x) f'(x) = 1
Substitute x = τ², let g(τ) = f(τ²).

Chain rule:
    g'(τ)   = 2τ f'(τ²)
    g''(τ)  = 2 f'(τ²) + 4τ² f''(τ²)
    g'''(τ) = 12τ f''(τ²) + 8τ³ f'''(τ²)

Solve for f', f'', f''' in terms of g', g'', g''' (with τ²=x).

Then we ask:
  1. What is the resulting ODE in τ for g?
  2. What is the indicial polynomial at τ = 0?
  3. Are the indicial roots in ℤ (no Puiseux)?
"""

import sympy as sp

tau = sp.Symbol('tau', positive=True)
g = sp.Function('g')

# Chain rule: express f', f'', f''' at x = τ² in terms of g at τ
gp = sp.diff(g(tau), tau)
gpp = sp.diff(g(tau), tau, 2)
gppp = sp.diff(g(tau), tau, 3)

# f' = g' / (2τ)
fp = gp / (2*tau)
# f'' from g'' = 2 f' + 4τ² f''
fpp = (gpp - 2*fp) / (4*tau**2)
# f''' from g''' = 12τ f'' + 8τ³ f'''
fppp = (gppp - 12*tau*fpp) / (8*tau**3)

x = tau**2

# Original LHS at x=τ²
lhs = x**2 * (4 - x) * fppp + x * (10 - 3*x) * fpp + (2 - x) * fp
rhs = 1

# Simplify: clear denominators, get polynomial form
lhs_simplified = sp.together(sp.simplify(lhs))
print("=== LHS in τ (before clearing denominators) ===")
print(lhs_simplified)

# Multiply through to clear τ denominators
# The lowest power of τ in denominators: fppp has 1/(8τ³), so multiply by 8τ³
# But we want the cleanest polynomial form
lhs_expanded = sp.expand(lhs)
print("\n=== LHS expanded ===")
print(lhs_expanded)

# Multiply both sides by 8τ³ to clear denominators
cleared_lhs = sp.expand(8 * tau**3 * lhs)
cleared_rhs = sp.expand(8 * tau**3 * rhs)
print("\n=== After multiplying by 8τ³ ===")
print("LHS:", cleared_lhs)
print("RHS:", cleared_rhs)

# Collect by g derivatives
print("\n=== Coefficients of g''', g'', g' ===")
for k, label in [(3, "g'''"), (2, "g''"), (1, "g'")]:
    coeff = cleared_lhs.coeff(sp.diff(g(tau), tau, k))
    print(f"  [{label}]: {sp.expand(coeff)}")

# Indicial analysis at τ=0: substitute g = τ^r and look at leading behavior
r = sp.Symbol('r')
h = tau**r

gp_h = sp.diff(h, tau)
gpp_h = sp.diff(h, tau, 2)
gppp_h = sp.diff(h, tau, 3)

# Homogeneous part: drop the RHS=1, plug τ^r into homogeneous equation
# Use the original form (not multiplied)
fp_h = gp_h / (2*tau)
fpp_h = (gpp_h - 2*fp_h) / (4*tau**2)
fppp_h = (gppp_h - 12*tau*fpp_h) / (8*tau**3)

homog = x**2 * (4 - x) * fppp_h + x * (10 - 3*x) * fpp_h + (2 - x) * fp_h
homog_simplified = sp.simplify(homog)
print("\n=== Homogeneous plug-in g = τ^r ===")
print(homog_simplified)

# Extract leading τ power. For indicial roots, take the lowest power of τ and set coefficient to 0.
homog_expanded = sp.expand(homog_simplified / tau**(r-2))  # normalize
print("\nDivide by τ^(r-2):")
print(sp.expand(homog_expanded))

# At τ → 0 (i.e., lowest power), the surviving terms come from 4 x² f''' + 10x f'' + 2 f' (the leading-order part)
# 4 x² f''' contributes: 4 τ^4 · f''' where f''' comes from g'''/8τ³ + lower-order
# Let's compute the "leading" indicial polynomial directly: substitute g=τ^r into the operator
# x²(4) f''' + x·10·f'' + 2 f' at x=τ²

leading = 4 * x**2 * fppp_h + 10 * x * fpp_h + 2 * fp_h
leading_simp = sp.simplify(leading)
leading_over_taur = sp.simplify(leading_simp / tau**r)
print("\n=== Indicial polynomial (coefficient of τ^r in leading terms) ===")
print(f"  P(r) = {sp.factor(leading_over_taur)}")
print(f"       = {sp.expand(leading_over_taur)}")

# Find roots
roots = sp.solve(leading_over_taur, r)
print(f"\n  Indicial roots: {roots}")
