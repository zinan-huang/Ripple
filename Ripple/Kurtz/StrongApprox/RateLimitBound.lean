-- Ripple/Kurtz/StrongApprox/RateLimitBound.lean
import Ripple.Kurtz.StrongApprox.DiffusionClockComparison

/-!
# The limiting rates inherit the bounds of the chain rates

T. G. Kurtz, "Strong approximation theorems for density dependent Markov
chains", Stochastic Process. Appl. 6 (1978), Section 3.  The chain rates
`f_l^N` satisfy `0 ≤ f_l^N ≤ ε_l` (assumption (3.1), p. 230) and approximate
the limiting rates `f_l` as `|f_l - f_l^N| ≤ Γ ε_l / N` (assumption (3.2),
p. 230).  Letting `N → ∞` (Archimedean argument, no regularity of `f_l^N`
needed) gives `0 ≤ f_l ≤ ε_l`, so the limiting rates lie in the same compact
interval; this removes a separate sign hypothesis on `f_l` in Theorem 3.3.
-/

namespace Ripple.Kurtz.StrongApprox

/-- Bounds (3.1) and (3.2), at all integer scales, imply the same upper bound
for the limiting rate. No continuity or sign assumption is needed here. -/
theorem rate_limit_le
    {ι State : Type*} {f : ι → State → ℝ}
    {fN : ℕ → ι → State → ℝ} {eps : ι → ℝ} {Gamma : ℝ}
    (hbound : ∀ N : ℕ, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (hpert : ∀ N : ℕ, 2 ≤ N → ∀ l x,
      |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    (l : ι) (x : State) : f l x ≤ eps l := by
  by_contra hle
  have hgap : 0 < f l x - eps l := sub_pos.mpr (lt_of_not_ge hle)
  obtain ⟨n, hn⟩ := exists_nat_gt (max 2 (Gamma * eps l / (f l x - eps l)))
  have hnTwo : (2 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hnTwoNat : 2 ≤ n := by exact_mod_cast hnTwo.le
  have hnPos : (0 : ℝ) < n := by linarith
  have hnLarge : Gamma * eps l / (f l x - eps l) < (n : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hn
  have hsmall : Gamma * eps l / (n : ℝ) < f l x - eps l := by
    apply (div_lt_iff₀ hnPos).2
    have h := (div_lt_iff₀ hgap).1 hnLarge
    nlinarith
  have happrox := (le_abs_self (f l x - fN n l x)).trans
    (hpert n hnTwoNat l x)
  have hupper := hbound n hnTwoNat l x
  linarith

/-- Nonnegativity of the chain rates and (3.2) imply nonnegativity of the
limiting rate. -/
theorem rate_limit_nonneg
    {ι State : Type*} {f : ι → State → ℝ}
    {fN : ℕ → ι → State → ℝ} {eps : ι → ℝ} {Gamma : ℝ}
    (hfN : ∀ N : ℕ, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (hpert : ∀ N : ℕ, 2 ≤ N → ∀ l x,
      |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    (l : ι) (x : State) : 0 ≤ f l x := by
  by_contra hneg
  have hgap : 0 < -f l x := neg_pos.mpr (lt_of_not_ge hneg)
  obtain ⟨n, hn⟩ := exists_nat_gt (max 2 (Gamma * eps l / (-f l x)))
  have hnTwo : (2 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hnTwoNat : 2 ≤ n := by exact_mod_cast hnTwo.le
  have hnPos : (0 : ℝ) < n := by linarith
  have hnLarge : Gamma * eps l / (-f l x) < (n : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hn
  have hsmall : Gamma * eps l / (n : ℝ) < -f l x := by
    apply (div_lt_iff₀ hnPos).2
    have h := (div_lt_iff₀ hgap).1 hnLarge
    nlinarith
  have hlow := (abs_le.mp (hpert n hnTwoNat l x)).1
  have hnonneg := hfN n hnTwoNat l x
  linarith

/-- Nonnegative limiting rates lie in the same compact rate interval. -/
theorem rate_limit_mem_Icc
    {ι State : Type*} {f : ι → State → ℝ}
    {fN : ℕ → ι → State → ℝ} {eps : ι → ℝ} {Gamma : ℝ}
    (hf : ∀ l x, 0 ≤ f l x)
    (hbound : ∀ N : ℕ, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (hpert : ∀ N : ℕ, 2 ≤ N → ∀ l x,
      |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    (l : ι) (x : State) : f l x ∈ Set.Icc 0 (eps l) :=
  ⟨hf l x, rate_limit_le hbound hpert l x⟩


end Ripple.Kurtz.StrongApprox
