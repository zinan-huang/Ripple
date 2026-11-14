/-
  Ripple.LPP.NAPSquaringCF24 — the CF'24 protocol satisfies the squaring condition of Theorem 3
  (the PP-to-NAP write-up §5) for the shrunk set `J₀ = {z₀₀}`.

  * `cf24PP : QuadPP 3`, the coefficient table of `Ripple.CF24.field`
    (`ż₀₀ = −2z₀₀² + 7z₀₀z₀₁ − 2z₀₀z₁₁`, `ż₀₁ = 2z₀₀² − 8z₀₀z₀₁ + 16z₀₀z₁₁ − z₀₁z₁₁`,
    `ż₁₁ = z₀₀z₀₁ − 14z₀₀z₁₁ + z₀₁z₁₁`), with `quadFun_cf24PP : quadFun 3 cf24PP = CF24.field`;
  * `cf24_squaring_condition`: `[y²] f_{z₀₀} ≤ 0` for every `y`;
  * `cf24_squaring`: for every rational `λ ∈ (0,1)` the squared system of `r · g` (slack trick at
    `z₀₀`) has a non-negative non-autocatalytic realisation on the `C(5,2) = 10` weight-2
    multi-indices of 4 species.
-/

import Ripple.LPP.NAPSquaring

namespace Ripple
namespace NAPTransport

open Finset

/-- The six quadratic monomials on `(z₀₀, z₀₁, z₁₁)`:
`z₀₀², z₀₀z₀₁, z₀₀z₁₁, z₀₁², z₀₁z₁₁, z₁₁²`. -/
def cf24Mono : Fin 6 → MI 3 2 :=
  ![⟨![2, 0, 0], by decide⟩, ⟨![1, 1, 0], by decide⟩, ⟨![1, 0, 1], by decide⟩,
    ⟨![0, 2, 0], by decide⟩, ⟨![0, 1, 1], by decide⟩, ⟨![0, 0, 2], by decide⟩]

/-- The CF'24 coefficient matrix (rows `ż₀₀, ż₀₁, ż₁₁`, columns `cf24Mono`). -/
def cf24Table : Fin 3 → Fin 6 → ℤ :=
  ![![-2, 7, -2, 0, 0, 0], ![2, -8, 16, 0, -1, 0], ![0, 1, -14, 0, 1, 0]]

theorem cf24Mono_inj : ∀ t t' : Fin 6, cf24Mono t = cf24Mono t' → t = t' := by decide

theorem cf24Table_col : ∀ t : Fin 6, cf24Table 0 t + cf24Table 1 t + cf24Table 2 t = 0 := by
  decide

theorem cf24Table_sign : ∀ (j : Fin 3) (t : Fin 6), cf24Table j t < 0 →
    0 < ((cf24Mono t).1 j : ℕ) := by decide

/-- The CF'24 coefficient table on weight-2 multi-indices. -/
def cf24Coef (j : Fin 3) (μ : MI 3 2) : ℚ :=
  ∑ t, if μ = cf24Mono t then (cf24Table j t : ℚ) else 0

theorem cf24Coef_mono (j : Fin 3) (t : Fin 6) : cf24Coef j (cf24Mono t) = cf24Table j t := by
  unfold cf24Coef
  rw [Finset.sum_eq_single t]
  · simp
  · intro t' _ ht'
    rw [if_neg]
    intro h
    exact ht' (cf24Mono_inj t t' h).symm
  · intro h; exact absurd (Finset.mem_univ t) h

theorem cf24Coef_of_not_mem (j : Fin 3) (μ : MI 3 2) (h : ∀ t, μ ≠ cf24Mono t) :
    cf24Coef j μ = 0 := by
  unfold cf24Coef
  exact Finset.sum_eq_zero fun t _ => if_neg (h t)

/-- CF'24 as a syntactic quadratic protocol. -/
def cf24PP : QuadPP 3 where
  coef := cf24Coef
  conservative μ := by
    by_cases hμ : ∃ t, μ = cf24Mono t
    · obtain ⟨t, rfl⟩ := hμ
      rw [Fin.sum_univ_three, cf24Coef_mono, cf24Coef_mono, cf24Coef_mono]
      exact_mod_cast cf24Table_col t
    · push Not at hμ
      simp [cf24Coef_of_not_mem _ μ hμ]
  sign j μ hneg := by
    by_cases hμ : ∃ t, μ = cf24Mono t
    · obtain ⟨t, rfl⟩ := hμ
      rw [cf24Coef_mono] at hneg
      exact cf24Table_sign j t (by exact_mod_cast hneg)
    · push Not at hμ
      rw [cf24Coef_of_not_mem j μ hμ] at hneg
      exact absurd hneg (lt_irrefl 0)

theorem quadFun_cf24PP_eq_sum (x : Fin 3 → ℝ) (j : Fin 3) :
    quadFun 3 cf24PP x j = ∑ t, (cf24Table j t : ℝ) * mono2 3 x (cf24Mono t) := by
  unfold quadFun
  have hc : ∀ μ : MI 3 2, ((cf24PP.coef j μ : ℚ) : ℝ)
      = ∑ t, if μ = cf24Mono t then (cf24Table j t : ℝ) else 0 := by
    intro μ
    show ((cf24Coef j μ : ℚ) : ℝ) = _
    unfold cf24Coef
    push_cast
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> simp
  simp only [hc, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_eq_single (cf24Mono t)]
  · simp
  · intro μ _ hμ
    simp [hμ]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The coefficient table `cf24PP` is the CF'24 field of `Ripple.CF24`. -/
theorem quadFun_cf24PP : quadFun 3 cf24PP = CF24.field := by
  funext x j
  rw [quadFun_cf24PP_eq_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, mono2, Fin.prod_univ_succ, Fin.prod_univ_zero]
  fin_cases j <;>
    simp [cf24Table, cf24Mono, CF24.field] <;> ring

/-- **The CF'24 squaring condition.** `Σ_{j ∈ {z₀₀}} [y²] f_j ≤ 0` for every species `y`. -/
theorem cf24_squaring_condition :
    ∀ y : Fin 3, ∑ j ∈ ({0} : Finset (Fin 3)), cf24PP.coef j (MI.pow 3 2 y) ≤ 0 := by
  have h : ∀ y : Fin 3, ∃ t, MI.pow 3 2 y = cf24Mono t ∧ cf24Table 0 t ≤ 0 := by decide
  intro y
  obtain ⟨t, ht, hle⟩ := h y
  rw [Finset.sum_singleton, ht]
  show cf24Coef 0 (cf24Mono t) ≤ 0
  rw [cf24Coef_mono]
  exact_mod_cast hle

/-- **Theorem 3 for CF'24.** For every rational `λ ∈ (0,1)`, the squared system of the r-trick
protocol of CF'24 (shrunk set `{z₀₀}`) has a non-negative non-autocatalytic weighted realisation
on the 10 weight-2 multi-indices of the 4 species `(r, u, z₀₁, z₁₁)`. -/
theorem cf24_squaring (lam : ℚ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ w : WProtocol (MI 4 2), (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧
      Realizes (veroneseLift 4 2) w (demandSq 4 (liftR1Set 3 cf24PP {0} lam hlam0)) :=
  exists_nap_realizing_squaring 3 cf24PP {0} lam hlam0 hlam1 cf24_squaring_condition

end NAPTransport
end Ripple
