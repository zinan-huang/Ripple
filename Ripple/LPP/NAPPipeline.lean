/-
  Ripple.LPP.NAPPipeline — the slack trick and the r²-trick at the coefficient level
  (the PP-to-NAP write-up, §4 Steps 1–2 and the combinatorial half of Theorem 2).

  From a syntactic quadratic protocol `g` on `n` species, a shrunk species `j₀` and `λ > 0`, the
  lifted quartic field on `n + 1` species (slot `0` = slack `r`, slot `j.succ` = original species
  `j`, with `u = λ x_{j₀}` in slot `j₀.succ`) has coefficient table
    `coef' 0        (r² ⊕ μ) = (1 − λ) λ^{−μ_{j₀}} g.coef j₀ μ`,
    `coef' j.succ   (r² ⊕ μ) = [j = j₀ ? λ : 1] λ^{−μ_{j₀}} g.coef j μ`,
  and `0` on every monomial whose slack exponent is not `2`. It is conservative and syntactic
  (`liftR2 : QuarticPP (n+1)`), and satisfies (C1),(C2) for the trivial reason that `y³k` and `y⁴`
  never have slack exponent `2`. Hence (`exists_nap_realizing_pipeline`) the cubed system of the
  pipeline always has a non-autocatalytic realisation. The ODE content of Theorem 2 (time change,
  conjugacy on the Veronese image) is not formalised here.
-/

import Ripple.LPP.NAPCriterion

namespace Ripple
namespace NAPTransport

open Finset

variable (n : ℕ)

/-- A syntactic quadratic protocol field on `n` species, as a coefficient table. -/
structure QuadPP where
  coef : Fin n → MI n 2 → ℚ
  conservative : ∀ μ, ∑ j, coef j μ = 0
  sign : ∀ j μ, coef j μ < 0 → 0 < (μ.1 j : ℕ)

/-- The tail of a weight-4 index on `n+1` species whose slack exponent is `2`. -/
def tail (μ' : MI (n + 1) 4) (h : (μ'.1 0 : ℕ) = 2) : MI n 2 :=
  MI.ofFun n (fun j => (μ'.1 j.succ : ℕ))
    (fun j => by
      have := MI.two_entries_le (n + 1) μ' (Fin.succ_ne_zero j)
      dsimp only
      omega)
    (by
      have hw := μ'.2
      rw [Fin.sum_univ_succ] at hw
      dsimp only
      omega)

/-- The lifted (slack-trick + r²-trick) coefficient table. -/
noncomputable def liftCoef (g : QuadPP n) (j₀ : Fin n) (lam : ℚ) (j' : Fin (n + 1))
    (μ' : MI (n + 1) 4) : ℚ :=
  if h : (μ'.1 0 : ℕ) = 2 then
    Fin.cases
      ((1 - lam) * lam⁻¹ ^ ((tail n μ' h).1 j₀ : ℕ) * g.coef j₀ (tail n μ' h))
      (fun j => (if j = j₀ then lam else 1) * lam⁻¹ ^ ((tail n μ' h).1 j₀ : ℕ) *
        g.coef j (tail n μ' h)) j'
  else 0

theorem liftCoef_sum (g : QuadPP n) (j₀ : Fin n) (lam : ℚ) (μ' : MI (n + 1) 4) :
    ∑ j', liftCoef n g j₀ lam j' μ' = 0 := by
  unfold liftCoef
  by_cases h : (μ'.1 0 : ℕ) = 2
  · simp only [dif_pos h]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    set sc := lam⁻¹ ^ ((tail n μ' h).1 j₀ : ℕ)
    set μ := tail n μ' h
    have hsplit : ∀ j, (if j = j₀ then lam else 1) * sc * g.coef j μ
        = sc * g.coef j μ + (if j = j₀ then (lam - 1) * sc * g.coef j μ else 0) := by
      intro j
      split_ifs <;> ring
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ j₀, Finset.mem_univ,
      if_true, ← Finset.mul_sum, g.conservative μ, mul_zero, zero_add]
    ring
  · simp [dif_neg h]

theorem liftCoef_sign (g : QuadPP n) (j₀ : Fin n) (lam : ℚ) (hlam : 0 < lam) (j' : Fin (n + 1))
    (μ' : MI (n + 1) 4) (hneg : liftCoef n g j₀ lam j' μ' < 0) : 0 < (μ'.1 j' : ℕ) := by
  unfold liftCoef at hneg
  by_cases h : (μ'.1 0 : ℕ) = 2
  · simp only [dif_pos h] at hneg
    have hsc : 0 < lam⁻¹ ^ ((tail n μ' h).1 j₀ : ℕ) := pow_pos (inv_pos.mpr hlam) _
    induction j' using Fin.cases with
    | zero => omega
    | succ j =>
      simp only [Fin.cases_succ] at hneg
      have hfac : 0 < (if j = j₀ then lam else 1) * lam⁻¹ ^ ((tail n μ' h).1 j₀ : ℕ) := by
        apply mul_pos _ hsc
        split_ifs <;> linarith
      have hg : g.coef j (tail n μ' h) < 0 := by
        by_contra hcon
        rw [not_lt] at hcon
        have := mul_nonneg hfac.le hcon
        linarith
      have := g.sign j _ hg
      simpa [tail] using this
  · simp [dif_neg h] at hneg

/-- The lifted quartic protocol field. -/
noncomputable def liftR2 (g : QuadPP n) (j₀ : Fin n) (lam : ℚ) (hlam : 0 < lam) :
    QuarticPP (n + 1) where
  coef := liftCoef n g j₀ lam
  conservative := liftCoef_sum n g j₀ lam
  sign := liftCoef_sign n g j₀ lam hlam

/-- The slack exponent of `y³k` is never `2`. -/
theorem two_slack_ne (y k : Fin (n + 1)) (h : y ≠ k) :
    ((MI.two (n + 1) 3 1 y k h).1 0 : ℕ) ≠ 2 := by
  simp only [MI.two, MI.ofFun_val]
  split_ifs <;> omega

/-- The slack exponent of `y⁴` is never `2`. -/
theorem pow_slack_ne (y : Fin (n + 1)) : ((MI.pow (n + 1) 4 y).1 0 : ℕ) ≠ 2 := by
  simp only [MI.pow, MI.ofFun_val]
  split_ifs <;> omega

theorem liftCoef_eq_zero_of_slack (g : QuadPP n) (j₀ : Fin n) (lam : ℚ) (j' : Fin (n + 1))
    (μ' : MI (n + 1) 4) (h : (μ'.1 0 : ℕ) ≠ 2) : liftCoef n g j₀ lam j' μ' = 0 := by
  unfold liftCoef
  rw [dif_neg h]

/-- (C1) for the pipeline. -/
theorem liftR2_C1 (g : QuadPP n) (j₀ : Fin n) (lam : ℚ) (hlam : 0 < lam) :
    ∀ (y k : Fin (n + 1)) (h : y ≠ k),
      (liftR2 n g j₀ lam hlam).coef y (MI.two (n + 1) 3 1 y k h) ≤ 0 := by
  intro y k h
  show liftCoef n g j₀ lam y _ ≤ 0
  rw [liftCoef_eq_zero_of_slack n g j₀ lam y _ (two_slack_ne n y k h)]

/-- (C2) for the pipeline. -/
theorem liftR2_C2 (g : QuadPP n) (j₀ : Fin n) (lam : ℚ) (hlam : 0 < lam) :
    ∀ (y k : Fin (n + 1)) (h : y ≠ k),
      (liftR2 n g j₀ lam hlam).coef k (MI.two (n + 1) 3 1 y k h)
        + 2 * (liftR2 n g j₀ lam hlam).coef y (MI.pow (n + 1) 4 y) ≤ 0 := by
  intro y k h
  show liftCoef n g j₀ lam k _ + 2 * liftCoef n g j₀ lam y _ ≤ 0
  rw [liftCoef_eq_zero_of_slack n g j₀ lam k _ (two_slack_ne n y k h),
    liftCoef_eq_zero_of_slack n g j₀ lam y _ (pow_slack_ne n y)]
  norm_num

/-- **Theorem 2, combinatorial half.** The cubed system of the pipeline (slack trick at `j₀` with
parameter `λ > 0`, then the r²-trick) of any syntactic quadratic protocol has a non-negative
non-autocatalytic weighted realisation. -/
theorem exists_nap_realizing_pipeline (g : QuadPP n) (j₀ : Fin n) (lam : ℚ) (hlam : 0 < lam) :
    ∃ w : WProtocol (MI (n + 1) 3), (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧
      Realizes (veroneseLift (n + 1) 3) w (demand (n + 1) (liftR2 n g j₀ lam hlam)) :=
  exists_nap_realizing_of_C1C2 (n + 1) (liftR2 n g j₀ lam hlam)
    (liftR2_C1 n g j₀ lam hlam) (liftR2_C2 n g j₀ lam hlam)

end NAPTransport
end Ripple
