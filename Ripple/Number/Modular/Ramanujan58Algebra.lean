import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The algebra of R6 (`c₅₈ = 1103/26390`)

Values at `τ₅₈` in the chart (`z ∈ ℂ`, derivative `d/dz`, `c = 2πi`): `E = E₄(τ)`, `F = E₄(2τ)`,
`A = E₂(τ)`, `B = E₂(2τ)`, `E6a = E₆(τ)`, `E6b = E₆(2τ)`, `Z = 2B − A`. The first and second
chart derivatives of `E`, `F` are `l58e1`, `l58f1`, `l58e2`, `l58f2` (Ramanujan's identities and
the chain rule at `2z`); those of `P(E,F)`, `Q(E,F)` are `l58P1`, `l58Q1`, `l58P2`, `l58Q2`.
`ramanujan58_algebra`: from the level-2 identities, `T(τ₅₈) = T₀` and the second-order equation
`t(2T″ − r T′²) + 2T′ = 0` (`r = 66716347/787408797714739200`, `t = τ₅₈`), with
`s = (4F − E)/(3Z²)`: `s² = 1 − 1/99⁴` and `1103 Z + 26390·99⁻⁴·Z′/x₂′ = −26390/(c t s)`.
Certificates computed with sympy (`docs/audit/evidence/chud/lvl58/r6cert.py`).
-/

namespace Ripple.Number.Modular

noncomputable section

def l58e1 (c A E E6a : ℂ) : ℂ := c / 3 * (A * E - E6a)

def l58f1 (c B F E6b : ℂ) : ℂ := 2 * c / 3 * (B * F - E6b)

def l58e2 (c A E E6a : ℂ) : ℂ :=
  c / 3 * (c / 12 * (A ^ 2 - E) * E + A * l58e1 c A E E6a - c / 2 * (A * E6a - E ^ 2))

def l58f2 (c B F E6b : ℂ) : ℂ :=
  2 * c / 3 * (2 * c / 12 * (B ^ 2 - F) * F + B * l58f1 c B F E6b - c * (B * E6b - F ^ 2))

def l58P0 (E F : ℂ) : ℂ := 248 * E ^ 2 - 616 * E * F + 3968 * F ^ 2

def l58Q0 (E F : ℂ) : ℂ := -E ^ 2 + 17 * E * F - 16 * F ^ 2

def l58P1 (E F e1 f1 : ℂ) : ℂ := (496 * E - 616 * F) * e1 + (-616 * E + 7936 * F) * f1

def l58Q1 (E F e1 f1 : ℂ) : ℂ := (-2 * E + 17 * F) * e1 + (17 * E - 32 * F) * f1

def l58P2 (E F e1 f1 e2 f2 : ℂ) : ℂ :=
  496 * e1 ^ 2 - 1232 * e1 * f1 + 7936 * f1 ^ 2 + (496 * E - 616 * F) * e2 +
    (-616 * E + 7936 * F) * f2

def l58Q2 (E F e1 f1 e2 f2 : ℂ) : ℂ :=
  -2 * e1 ^ 2 + 34 * e1 * f1 - 32 * f1 ^ 2 + (-2 * E + 17 * F) * e2 + (17 * E - 32 * F) * f2

/-- The chart derivative of `Z = 2E₂(2z) − E₂(z)`. -/
def l58Zp (c A B E F : ℂ) : ℂ := 2 * (2 * c / 12 * (B ^ 2 - F)) - c / 12 * (A ^ 2 - E)

set_option maxHeartbeats 4000000 in
-- `linear_combination` on polynomials of degree about 20.
theorem ramanujan58_algebra (Z A B E F E6a E6b s c t T1 T2 : ℂ)
    (hZ : Z = 2 * B - A) (hJ1 : E + 4 * F = 5 * Z ^ 2)
    (hJ2 : 2 * E6a = 3 * Z * (4 * F - E) - 7 * Z ^ 3)
    (hJ3 : 16 * E6b = 7 * Z ^ 3 + 3 * Z * (4 * F - E))
    (hsdef : 4 * F - E = 3 * s * Z ^ 2)
    (hR5 : l58P0 E F = (256 * 99 ^ 4 - 104) * l58Q0 E F)
    (hZ0 : Z ≠ 0) (hc : c ≠ 0) (ht0 : t ≠ 0)
    (hT1 : T1 = (l58P1 E F (l58e1 c A E E6a) (l58f1 c B F E6b) * l58Q0 E F -
        l58P0 E F * l58Q1 E F (l58e1 c A E E6a) (l58f1 c B F E6b)) / l58Q0 E F ^ 2)
    (hT2 : T2 = ((l58P2 E F (l58e1 c A E E6a) (l58f1 c B F E6b) (l58e2 c A E E6a)
          (l58f2 c B F E6b) * l58Q0 E F -
        l58P0 E F * l58Q2 E F (l58e1 c A E E6a) (l58f1 c B F E6b) (l58e2 c A E E6a)
          (l58f2 c B F E6b)) * l58Q0 E F ^ 2 -
        (l58P1 E F (l58e1 c A E E6a) (l58f1 c B F E6b) * l58Q0 E F -
          l58P0 E F * l58Q1 E F (l58e1 c A E E6a) (l58f1 c B F E6b)) *
          (2 * l58Q0 E F * l58Q1 E F (l58e1 c A E E6a) (l58f1 c B F E6b))) /
        (l58Q0 E F ^ 2) ^ 2)
    (hM : t * (2 * T2 - 66716347 / 787408797714739200 * T1 ^ 2) + 2 * T1 = 0) :
    s ^ 2 = 1 - 1 / 99 ^ 4 ∧ T1 = -24591257856 * Z * c * s ∧
      1103 * Z + 26390 * (1 / 99 ^ 4) * l58Zp c A B E F / (-256 * T1 / (256 * 99 ^ 4) ^ 2) =
        -26390 / (c * t * s) := by
  have hB : B = (Z + A) / 2 := by linear_combination -hZ / 2
  have hE : E = Z ^ 2 * (5 - 3 * s) / 2 := by linear_combination hJ1 / 2 - hsdef / 2
  have hF : F = Z ^ 2 * (5 + 3 * s) / 8 := by linear_combination hJ1 / 8 + hsdef / 8
  have hE6a : E6a = Z ^ 3 * (9 * s - 7) / 2 := by
    linear_combination hJ2 / 2 + 3 * Z * hsdef / 2
  have hE6b : E6b = Z ^ 3 * (7 + 9 * s) / 16 := by
    linear_combination hJ3 / 16 + 3 * Z * hsdef / 16
  subst hB hE hF hE6a hE6b
  simp only [l58e1, l58f1, l58e2, l58f2, l58P0, l58Q0, l58P1, l58Q1, l58P2, l58Q2] at hR5 hT1 hT2
  have hs2 : s ^ 2 = 1 - 1 / 99 ^ 4 := by
    have h : (345814563600 * Z ^ 4) * (s ^ 2 - (1 - 1 / 99 ^ 4)) = 0 := by
      linear_combination hR5
    have h4 : (345814563600 : ℂ) * Z ^ 4 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 4 hZ0)
    linear_combination (mul_eq_zero.mp h).resolve_left h4
  set Q0e : ℂ := -(Z ^ 2 * (5 - 3 * s) / 2) ^ 2 + 17 * (Z ^ 2 * (5 - 3 * s) / 2) *
      (Z ^ 2 * (5 + 3 * s) / 8) - 16 * (Z ^ 2 * (5 + 3 * s) / 8) ^ 2 with hQ0e
  have hQv : Q0e = 225 / 16 * Z ^ 4 * (1 / 99 ^ 4) := by
    rw [hQ0e]
    linear_combination (-225 * Z ^ 4 / 16) * hs2
  have hQ0 : Q0e ≠ 0 := by
    rw [hQv]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hZ0)) (by norm_num)
  rw [eq_div_iff (pow_ne_zero 2 hQ0)] at hT1
  rw [eq_div_iff (pow_ne_zero 2 (pow_ne_zero 2 hQ0))] at hT2
  have hT1v : T1 = -24591257856 * Z * c * s := by
    have h : (T1 - -24591257856 * Z * c * s) * Q0e ^ 2 = 0 := by
      rw [hQ0e]
      linear_combination hT1 +
        (4863017300625 * Z ^ 9 * c * s ^ 3 - 4863017300625 * Z ^ 9 * c * s) * hs2
    linear_combination (mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 hQ0)
  refine ⟨hs2, hT1v, ?_⟩
  have hT2v :
      T2 = -192 * Z * c ^ 2 * (21346578 * A * s + 10673289 * Z * s - 160099334 * Z) := by
    have h : (T2 - -192 * Z * c ^ 2 * (21346578 * A * s + 10673289 * Z * s - 160099334 * Z)) *
        (Q0e ^ 2) ^ 2 = 0 := by
      rw [hQ0e]
      linear_combination hT2 + (
        82063416948046875*A*Z^17*c^2*s^7/512 - 246190250844140625*A*Z^17*c^2*s^5/512 +
        246190250844140625*A*Z^17*c^2*s^3/512 - 82063416948046875*A*Z^17*c^2*s/512 +
        82063416948046875*Z^18*c^2*s^7/1024 - 1230951254220703125*Z^18*c^2*s^6/1024 -
        246190250844140625*Z^18*c^2*s^5/1024 + 3692853762662109375*Z^18*c^2*s^4/1024 +
        246190250844140625*Z^18*c^2*s^3/1024 - 3692853762662109375*Z^18*c^2*s^2/1024 -
        82063416948046875*Z^18*c^2*s/1024 + 1230951254220703125*Z^18*c^2/1024) * hs2
    linear_combination (mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 (pow_ne_zero 2 hQ0))
  have hA : 215622 * A * c * s * t + 107811 * Z * c * s * t - 269360 * Z * c * t +
      1293732 * s = 0 := by
    rw [hT1v, hT2v] at hM
    have h : (-38016 * Z * c) * (215622 * A * c * s * t + 107811 * Z * c * s * t -
        269360 * Z * c * t + 1293732 * s) = 0 := by
      linear_combination hM + (307619792303882256 * Z ^ 2 * c ^ 2 * t / 6003725) * hs2
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) hZ0) hc)
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs2
    norm_num at hs2
  have hinner : 13236 * Z * s * c * t + 26390 * (2 * A - 3 * Z * s + Z) * c * t + 316680 = 0 := by
    have h : (13236 * Z * s * c * t + 26390 * (2 * A - 3 * Z * s + Z) * c * t + 316680) * s =
        0 := by
      linear_combination (26390 / 107811 : ℂ) * hA + (-65934 * Z * c * t) * hs2
    exact (mul_eq_zero.mp h).resolve_right hs0
  rw [hT1v]
  have key : 1103 * Z + 26390 * (1 / 99 ^ 4) * l58Zp c A ((Z + A) / 2) (Z ^ 2 * (5 - 3 * s) / 2)
        (Z ^ 2 * (5 + 3 * s) / 8) / (-256 * (-24591257856 * Z * c * s) / (256 * 99 ^ 4) ^ 2) -
      -26390 / (c * t * s) =
      (13236 * Z * s * c * t + 26390 * (2 * A - 3 * Z * s + Z) * c * t + 316680) /
        (12 * s * c * t) := by
    simp only [l58Zp]
    field_simp
    ring
  rw [hinner, zero_div] at key
  linear_combination key

end

end Ripple.Number.Modular
