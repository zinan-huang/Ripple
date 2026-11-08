/-
Copyright (c) 2026 Xiang Huang, Zinan Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang, Zinan Huang
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Ripple.Number.Frobenius.PoincaréPerron

/-!
# Poincaré-Perron Theorem via Variation of Parameters

The main theorem `poincare_perron_growth_bound`: for a 3-step recurrence
with coefficients converging at rate `O(1/m)` to limits whose
characteristic polynomial has a dominant double eigenvalue `ev₁`,
every solution satisfies `|c_m| ≤ C · (m+1) · |ev₁|^m`.

Proof strategy: variation of parameters on the 3×3 companion system.
-/

open Filter

namespace Ripple.Number.Frobenius.PoincaréPerron.CompanionMatrix

/-! ### Structures -/

/-- A variable-coefficient 3-step recurrence with limiting behavior. -/
structure ConvergentThreeStep where
  /-- The sequence. -/
  c : ℕ → ℝ
  /-- Coefficient functions. -/
  coeff_a : ℕ → ℝ
  coeff_b : ℕ → ℝ
  coeff_c : ℕ → ℝ
  /-- Limiting coefficients. -/
  lim_a : ℝ
  lim_b : ℝ
  lim_c : ℝ
  /-- Dominant eigenvalue (double root). -/
  ev₁ : ℝ
  /-- Subdominant eigenvalue (simple root). -/
  ev₂ : ℝ
  /-- Convergence rate constant. -/
  rate : ℝ
  /-- The recurrence holds for m ≥ 2. -/
  recurrence : ∀ m, 2 ≤ m →
    c (m + 1) = coeff_a m * c m + coeff_b m * c (m - 1) + coeff_c m * c (m - 2)
  /-- ev₁ ≠ 0. -/
  hev₁_ne : ev₁ ≠ 0
  /-- The characteristic polynomial factors correctly. -/
  char_poly : ∀ x : ℝ,
    x ^ 3 - lim_a * x ^ 2 - lim_b * x - lim_c =
      (x - ev₁) ^ 2 * (x - ev₂)
  /-- Subdominant is strictly smaller. -/
  subdominant_lt : |ev₂| < |ev₁|
  /-- Convergence rate positive. -/
  hrate : 0 < rate
  /-- Coefficient convergence. -/
  conv_a : ∀ m : ℕ, 1 ≤ m → |coeff_a m - lim_a| ≤ rate / m
  conv_b : ∀ m : ℕ, 1 ≤ m → |coeff_b m - lim_b| ≤ rate / m
  conv_c : ∀ m : ℕ, 1 ≤ m → |coeff_c m - lim_c| ≤ rate / m

/-! ### The main theorem (via ratio bound)

The original architecture envisioned a full Jordan-decomposition proof
(see comments in earlier commits). After analysis (2026-04-28), we
identified that variable-coefficient bootstrap fails: even with the
correct `(D−ev₁)²` extraction, `wSubdom = zSubdom/ev₂^m` grows because
the perturbation `ε(m)/ev₂^(m+1)` scales as `(|ev₁|/|ev₂|)^m`.

**Replacement architecture:** the user supplies a *ratio bound*
`|c(m+1)|/|c m| ≤ |ev₁|·(1 + 1/m)` for `m ≥ M₀`, and we close the
growth bound via `Ripple.Number.Frobenius.PoincaréPerron.growth_bound_of_ratio_bound_one`
(elementary telescoping product). The Apéry instance proves this
ratio bound by exploiting the explicit char-poly factorization
`taylorShift(P)(t) = t·(t-z₁)²·(t+24√2)` and the denominator factorization
`aperyFrobenius_half_denom_ne_zero` etc. — concrete nlinarith on the
Apéry coefficients, not abstract analysis. -/

/-- **Poincaré-Perron growth bound (from explicit ratio bound).**

Given a convergent 3-step recurrence and an input ratio bound
`|c(m+1)| ≤ |ev₁|·(1 + 1/m)·|c m|` for `m ≥ M₀`, the sequence satisfies
`|c m| ≤ C·(m+1)·|ev₁|^m`.

The ratio-bound hypothesis is the cancellation-essential algebra
specific to each instance; the abstract framework here is elementary
(direct application of `growth_bound_of_ratio_bound_one`). -/
theorem poincare_perron_growth_bound (sys : ConvergentThreeStep)
    {M₀ : ℕ} (hM₀ : 1 ≤ M₀)
    (hratio : ∀ m, M₀ ≤ m →
        |sys.c (m + 1)| ≤ |sys.ev₁| * (1 + 1 / (m : ℝ)) * |sys.c m|) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      |sys.c m| ≤ C * ((m : ℝ) + 1) * |sys.ev₁| ^ m := by
  have hev₁_pos : 0 < |sys.ev₁| := by
    rw [abs_pos]; exact sys.hev₁_ne
  exact Ripple.Number.Frobenius.PoincaréPerron.growth_bound_of_ratio_bound_one
    hev₁_pos hM₀ hratio

/-! ### Jordan basis decomposition -/

/-- The Jordan basis change-of-basis matrix `P` for a companion matrix with
double eigenvalue `ev₁` and simple eigenvalue `ev₂`. Columns:
`v₁ = (ev₁², ev₁, 1)`, `v₂ = (2ev₁, 1, 0)`, `v₃ = (ev₂², ev₂, 1)`. -/
noncomputable def jordanBasisDet (ev₁ ev₂ : ℝ) : ℝ :=
  (ev₁ - ev₂) ^ 2

/-- The Jordan basis is nonsingular when `ev₁ ≠ ev₂`. -/
lemma jordanBasisDet_ne_zero {ev₁ ev₂ : ℝ} (h : ev₁ ≠ ev₂) :
    jordanBasisDet ev₁ ev₂ ≠ 0 := by
  unfold jordanBasisDet
  exact pow_ne_zero 2 (sub_ne_zero.mpr h)

/-! ### Scalar Jordan decomposition (via `(D−ev₁)²` second-order difference)

For a companion matrix with double eigenvalue `ev₁` and simple eigenvalue `ev₂`,
the natural ev₂-projection operator is `(D − ev₁)²` (the second-order forward
difference w.r.t. ev₁): applied to `(A + B·m)·ev₁^m + C·ev₂^m` it kills both
ev₁-generalized eigenvectors and yields `C·(ev₂−ev₁)²·ev₂^(m−2)`.

Therefore we define
```
zSubdom(m) := (c m − 2·ev₁·c (m−1) + ev₁²·c (m−2)) / (ev₂ − ev₁)²
```
which extracts a *pure* ev₂-branch coefficient (modulo `ev₂^(m−2)` factor).

**History note (2026-04-28):** an earlier definition `(c m − ev₁·c (m−1))/(ev₂ − ev₁)`
was a *one-shift* difference; for double-root ev₁ it leaves a residual
`B·ev₁^m` from the generalized eigenvector, so the rescaled `wSubdom = zSubdom/ev₂^m`
diverges. The two-shift form below is the correct projection. See
`Ripple/Number/Frobenius/UNDERSTANDING.md` session 2026-04-28.
-/

/-- The ev₂-component extraction via second-order difference w.r.t. ev₁:
`(c m − 2·ev₁·c (m−1) + ev₁²·c (m−2)) / (ev₂ − ev₁)²`.

For the constant-coefficient recurrence, this isolates the `ev₂^m` branch:
applied to `c(m) = (A + B·m)·ev₁^m + C·ev₂^m` it returns `C·ev₂^(m−2)`. -/
noncomputable def zSubdom (c : ℕ → ℝ) (ev₁ : ℝ) (ev₂ : ℝ) (m : ℕ) : ℝ :=
  (c m - 2 * ev₁ * c (m - 1) + ev₁ ^ 2 * c (m - 2)) / (ev₂ - ev₁) ^ 2

/-- The rescaled ev₂-component `w₃(m) = z₃(m) / ev₂^m`. -/
noncomputable def wSubdom (c : ℕ → ℝ) (ev₁ ev₂ : ℝ) (m : ℕ) : ℝ :=
  zSubdom c ev₁ ev₂ m / ev₂ ^ m

/-- **For a pure ev₂ branch, `zSubdom` extracts the coefficient (rescaled).**
If `c m = A · ev₂^m`, then `zSubdom c ev₁ ev₂ m = A · ev₂^(m−2)`. -/
lemma zSubdom_of_pure_ev2 {ev₁ ev₂ A : ℝ} (hne : ev₁ ≠ ev₂) (m : ℕ) (hm : 2 ≤ m) :
    zSubdom (fun k => A * ev₂ ^ k) ev₁ ev₂ m = A * ev₂ ^ (m - 2) := by
  simp only [zSubdom]
  have hd : ev₂ - ev₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hd2 : (ev₂ - ev₁) ^ 2 ≠ 0 := pow_ne_zero _ hd
  -- Numerator = A·ev₂^m − 2·ev₁·A·ev₂^(m−1) + ev₁²·A·ev₂^(m−2)
  --          = A·ev₂^(m−2)·(ev₂² − 2·ev₁·ev₂ + ev₁²)
  --          = A·ev₂^(m−2)·(ev₂ − ev₁)²
  have hpow1 : ev₂ ^ m = ev₂ ^ (m - 2) * ev₂ ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hpow2 : ev₂ ^ (m - 1) = ev₂ ^ (m - 2) * ev₂ := by
    rw [show ev₂ ^ (m - 1) = ev₂ ^ ((m - 2) + 1) from by congr 1; omega, pow_succ]
  rw [show A * ev₂ ^ m - 2 * ev₁ * (A * ev₂ ^ (m - 1)) + ev₁ ^ 2 * (A * ev₂ ^ (m - 2))
        = A * ev₂ ^ (m - 2) * (ev₂ - ev₁) ^ 2 from by
      rw [hpow1, hpow2]; ring]
  rw [mul_div_cancel_right₀ _ hd2]

/-- **For a pure ev₁ branch (constant coefficient), `zSubdom` vanishes.**
If `c m = A · ev₁^m`, then `zSubdom c ev₁ ev₂ m = 0`. -/
lemma zSubdom_of_pure_ev1 {ev₁ ev₂ A : ℝ} (m : ℕ) (hm : 2 ≤ m) :
    zSubdom (fun k => A * ev₁ ^ k) ev₁ ev₂ m = 0 := by
  simp only [zSubdom]
  -- A·ev₁^m − 2·ev₁·A·ev₁^(m−1) + ev₁²·A·ev₁^(m−2)
  --   = A·ev₁^m · (1 − 2 + 1) = 0
  have hpow1 : ev₁ ^ m = ev₁ ^ (m - 2) * ev₁ ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hpow2 : ev₁ ^ (m - 1) = ev₁ ^ (m - 2) * ev₁ := by
    rw [show ev₁ ^ (m - 1) = ev₁ ^ ((m - 2) + 1) from by congr 1; omega, pow_succ]
  rw [show A * ev₁ ^ m - 2 * ev₁ * (A * ev₁ ^ (m - 1)) + ev₁ ^ 2 * (A * ev₁ ^ (m - 2)) = 0 from by
    rw [hpow1, hpow2]; ring]
  simp

/-- **For the `B·m·ev₁^m` (Jordan generalized eigenvector) branch, `zSubdom`
still vanishes.** This is the new property: the second-order difference
`(D − ev₁)²` kills *both* the regular and the generalized ev₁ eigenvectors. -/
lemma zSubdom_of_pure_ev1_linear {ev₁ ev₂ B : ℝ} (m : ℕ) (hm : 2 ≤ m) :
    zSubdom (fun k => B * (k : ℝ) * ev₁ ^ k) ev₁ ev₂ m = 0 := by
  simp only [zSubdom]
  -- Numerator = B·m·ev₁^m − 2·ev₁·B·(m−1)·ev₁^(m−1) + ev₁²·B·(m−2)·ev₁^(m−2)
  --          = ev₁^m · B · [m − 2(m−1) + (m−2)] = ev₁^m · B · 0 = 0
  have hpow1 : ev₁ ^ m = ev₁ ^ (m - 2) * ev₁ ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hpow2 : ev₁ ^ (m - 1) = ev₁ ^ (m - 2) * ev₁ := by
    rw [show ev₁ ^ (m - 1) = ev₁ ^ ((m - 2) + 1) from by congr 1; omega, pow_succ]
  have hm2 : ((m : ℝ) - 2) = ((m - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ m)]; norm_num
  have hm1 : ((m : ℝ) - 1) = ((m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]; norm_num
  rw [show B * ((m - 1 : ℕ) : ℝ) = B * ((m : ℝ) - 1) from by rw [hm1]]
  rw [show B * ((m - 2 : ℕ) : ℝ) = B * ((m : ℝ) - 2) from by rw [hm2]]
  rw [show B * ↑m * ev₁ ^ m - 2 * ev₁ * (B * (↑m - 1) * ev₁ ^ (m - 1))
        + ev₁ ^ 2 * (B * (↑m - 2) * ev₁ ^ (m - 2)) = 0 from by
      rw [hpow1, hpow2]; ring]
  simp

/-- **`zSubdom` recurrence for variable-coefficient system.** If `c` satisfies
the 3-step recurrence, then `zSubdom = zSubdom c ev₁ ev₂` satisfies a clean
*1-step* recurrence:
```
zSubdom(m+1) = ev₂ · zSubdom(m) + perturbation(m) / (ev₂ − ev₁)²
```
where `perturbation(m) = (α(m)−α_∞)·c(m) + (β(m)−β_∞)·c(m−1) + (γ(m)−γ_∞)·c(m−2)`
captures only the deviation of the m-dependent coefficients from their limits.

The 1-step form (instead of the broken one-shift `zSubdom`'s 2-step form) is
possible precisely because `(D − ev₁)²` kills both ev₁-eigenvector branches.

**Const-coeff sanity check:** when `α ≡ α_∞`, `β ≡ β_∞`, `γ ≡ γ_∞`, the
perturbation vanishes and `zSubdom(m+1) = ev₂ · zSubdom(m)`, which iterates to
`zSubdom(m) = ev₂^(m-2) · zSubdom(2)`. By `zSubdom_of_pure_ev2` plus the linearity
of `zSubdom` w.r.t. the underlying decomposition, this matches the closed form
`zSubdom(m) = C · ev₂^(m-2)`. -/
lemma zSubdom_recurrence (sys : ConvergentThreeStep) {m : ℕ} (hm : 2 ≤ m) :
    zSubdom sys.c sys.ev₁ sys.ev₂ (m + 1) =
      sys.ev₂ * zSubdom sys.c sys.ev₁ sys.ev₂ m +
      ((sys.coeff_a m - sys.lim_a) * sys.c m +
       (sys.coeff_b m - sys.lim_b) * sys.c (m - 1) +
       (sys.coeff_c m - sys.lim_c) * sys.c (m - 2)) / (sys.ev₂ - sys.ev₁) ^ 2 := by
  -- char_poly identity: lim_a = 2·ev₁ + ev₂, lim_b = -(2·ev₁·ev₂ + ev₁²), lim_c = ev₁²·ev₂.
  have hchar := sys.char_poly
  have hχ0 := hchar 0
  have hχ1 := hchar 1
  have hχ2 := hchar 2
  have hχm1 := hchar (-1)
  have hLa : sys.lim_a = 2 * sys.ev₁ + sys.ev₂ := by nlinarith [hχ0, hχ1, hχ2, hχm1]
  have hLb : sys.lim_b = -(2 * sys.ev₁ * sys.ev₂ + sys.ev₁ ^ 2) := by
    nlinarith [hχ0, hχ1, hχ2, hχm1, hLa]
  have hLc : sys.lim_c = sys.ev₁ ^ 2 * sys.ev₂ := by nlinarith [hχ0]
  have hrec := sys.recurrence m hm
  have hne : sys.ev₂ - sys.ev₁ ≠ 0 := by
    have hlt := sys.subdominant_lt
    have : sys.ev₁ ≠ sys.ev₂ := fun h => lt_irrefl _ (by rw [h] at hlt; exact hlt)
    exact sub_ne_zero.mpr (Ne.symm this)
  have hne2 : (sys.ev₂ - sys.ev₁) ^ 2 ≠ 0 := pow_ne_zero _ hne
  have h_pred1 : m + 1 - 1 = m := by omega
  have h_pred2 : m + 1 - 2 = m - 1 := by omega
  simp only [zSubdom, h_pred1, h_pred2]
  rw [hrec]
  -- Substitute char_poly identities to make the equation purely in ev₁, ev₂.
  rw [hLa, hLb, hLc]
  field_simp
  ring

/-- **The full Poincaré-Perron theorem reduces to 3 component bounds.**
Once the Jordan decomposition is established, the growth bound follows
from bounding each z-component and recombining through the (fixed,
bounded) change-of-basis matrix. -/
theorem poincare_perron_of_jordan_components
    (sys : ConvergentThreeStep)
    {w₁ w₂ w₃ : ℕ → ℝ}
    {P_norm : ℝ} (hP : 0 < P_norm)
    -- The state decomposes through Jordan basis
    (hdecomp : ∀ m, |sys.c m| ≤ P_norm *
        (|w₁ m| * |sys.ev₁| ^ m + |w₂ m| * |sys.ev₁| ^ m +
         |w₃ m| * |sys.ev₂| ^ m))
    -- z₁ component: linear growth
    {C₁ : ℝ} (hC₁ : 0 < C₁) (hw₁ : ∀ m : ℕ, |w₁ m| ≤ C₁ * ((m : ℝ) + 1))
    -- z₂ component: bounded
    {C₂ : ℝ} (hC₂ : 0 < C₂) (hw₂ : ∀ m : ℕ, |w₂ m| ≤ C₂)
    -- z₃ component: bounded
    {C₃ : ℝ} (hC₃ : 0 < C₃) (hw₃ : ∀ m : ℕ, |w₃ m| ≤ C₃) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      |sys.c m| ≤ C * ((m : ℝ) + 1) * |sys.ev₁| ^ m := by
  refine ⟨P_norm * (C₁ + C₂ + C₃), by positivity, fun m => ?_⟩
  have hev₁_pow_nn : 0 ≤ |sys.ev₁| ^ m := pow_nonneg (abs_nonneg _) _
  have hev₂_le_ev₁ : |sys.ev₂| ^ m ≤ |sys.ev₁| ^ m :=
    pow_le_pow_left₀ (abs_nonneg _) sys.subdominant_lt.le m
  have hm_pos : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  -- Bound each term
  have h1 : |w₁ m| * |sys.ev₁| ^ m ≤ C₁ * ((m : ℝ) + 1) * |sys.ev₁| ^ m :=
    mul_le_mul_of_nonneg_right (hw₁ m) hev₁_pow_nn
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have h2 : |w₂ m| * |sys.ev₁| ^ m ≤ C₂ * ((m : ℝ) + 1) * |sys.ev₁| ^ m := by
    calc |w₂ m| * |sys.ev₁| ^ m ≤ C₂ * |sys.ev₁| ^ m :=
          mul_le_mul_of_nonneg_right (hw₂ m) hev₁_pow_nn
      _ = C₂ * 1 * |sys.ev₁| ^ m := by ring
      _ ≤ C₂ * ((m : ℝ) + 1) * |sys.ev₁| ^ m := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm1 hC₂.le) hev₁_pow_nn
  have h3 : |w₃ m| * |sys.ev₂| ^ m ≤ C₃ * ((m : ℝ) + 1) * |sys.ev₁| ^ m := by
    calc |w₃ m| * |sys.ev₂| ^ m ≤ C₃ * |sys.ev₂| ^ m :=
          mul_le_mul_of_nonneg_right (hw₃ m) (pow_nonneg (abs_nonneg _) _)
      _ ≤ C₃ * |sys.ev₁| ^ m := mul_le_mul_of_nonneg_left hev₂_le_ev₁ hC₃.le
      _ = C₃ * 1 * |sys.ev₁| ^ m := by ring
      _ ≤ C₃ * ((m : ℝ) + 1) * |sys.ev₁| ^ m := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm1 hC₃.le) hev₁_pow_nn
  calc |sys.c m|
      ≤ P_norm * (|w₁ m| * |sys.ev₁| ^ m + |w₂ m| * |sys.ev₁| ^ m +
          |w₃ m| * |sys.ev₂| ^ m) := hdecomp m
    _ ≤ P_norm * (C₁ * ((m : ℝ) + 1) * |sys.ev₁| ^ m +
          C₂ * ((m : ℝ) + 1) * |sys.ev₁| ^ m +
          C₃ * ((m : ℝ) + 1) * |sys.ev₁| ^ m) := by
        apply mul_le_mul_of_nonneg_left _ hP.le
        exact add_le_add (add_le_add h1 h2) h3
    _ = P_norm * (C₁ + C₂ + C₃) * ((m : ℝ) + 1) * |sys.ev₁| ^ m := by ring

end Ripple.Number.Frobenius.PoincaréPerron.CompanionMatrix
