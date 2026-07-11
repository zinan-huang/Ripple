/-
  Ripple.LPP.Stochastic — Bridging PLPP Balance Equations to Kurtz's Framework

  Connects the algebraic LPP/PLPP constructions (Stages 1–4) to
  stochastic convergence via Kurtz's mean-field theorem.

  Two notions of LPP computability:

  1. **Extended (Huang-Huls, [LPP])**: Continuum of equilibria allowed.
     The ODE trajectory from a fixed rational initial condition has its
     marked-state readout converging to ν. No isolated equilibrium needed.
     Formalized as `PLPPContinuumComputation`.

  2. **Classical (BFK, [Koegler])**: Finitely many equilibria, one is
     exponentially stable. Needed for Koegler Corollary 2 concentration
     bounds. Formalized as `PLPPIsolatedComputation`.

  The double-limit structure:
    - Exchanged order: lim_{t→∞} lim_{N→∞} X̄^N(t) = lim_{t→∞} x(t) = ν
      (works for both notions)
    - Standard order: for large N and t, X̄^N(t) ≈ ν w.h.p.
      (needs isolated/exponential version)

  References:
  - [BFK] Bournez-Fraigniaud-Koegler, MFCS 2012.
  - [LPP] Huang-Huls, DNA 28, 2022.
  - [Koegler] PhD thesis, Paris Diderot, 2012.
-/

import Ripple.LPP.Defs
import Ripple.Kurtz.MeanField
import Ripple.Kurtz.PopulationProtocol

namespace Ripple

open Kurtz

/-! ## PLPPTransitions → RateSpec -/

namespace PLPPTransitions

variable {n : ℕ} (tr : PLPPTransitions n)

/-- The net change vector when pair (i,j) transitions to (k,l). -/
def netChange (i j k l : Fin n) : Fin n → ℤ := fun r =>
  (if k = r then 1 else 0) + (if l = r then 1 else 0)
  - (if i = r then 1 else 0) - (if j = r then 1 else 0)

theorem netChange_sum_zero (i j k l : Fin n) :
    ∑ r, netChange i j k l r = 0 := by
  simp [netChange, Finset.sum_add_distrib, Finset.sum_sub_distrib]

def rateSpecJumps (_tr : PLPPTransitions n) : Finset (Fin n → ℤ) :=
  Finset.univ.image fun ijkl : Fin n × Fin n × Fin n × Fin n =>
    netChange ijkl.1 ijkl.2.1 ijkl.2.2.1 ijkl.2.2.2

noncomputable def toRateSpec : RateSpec n where
  jumps := tr.rateSpecJumps
  rate ℓ x :=
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
      if netChange i j k l = ℓ then (tr.α i j k l : ℝ) * x i * x j
      else 0
  rate_nonneg := by
    intro ℓ _ x hx
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    apply Finset.sum_nonneg; intro k _
    apply Finset.sum_nonneg; intro l _
    split_ifs
    · exact mul_nonneg (mul_nonneg (by exact_mod_cast tr.nonneg i j k l) (hx i)) (hx j)
    · exact le_refl 0
  rate_support := by
    intro ℓ hℓ
    ext x
    simp only [rateSpecJumps, Finset.mem_image, Finset.mem_univ, true_and] at hℓ
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    apply Finset.sum_eq_zero; intro k _
    apply Finset.sum_eq_zero; intro l _
    have : netChange i j k l ≠ ℓ := fun heq => hℓ ⟨(i, j, k, l), heq⟩
    simp [this]
  rate_lipschitz := by
    intro ℓ _ R hR
    let S : ℝ :=
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        (tr.α i j k l : ℝ) * (2 * R)
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      apply Finset.sum_nonneg; intro i _
      apply Finset.sum_nonneg; intro j _
      apply Finset.sum_nonneg; intro k _
      apply Finset.sum_nonneg; intro l _
      exact mul_nonneg (by exact_mod_cast tr.nonneg i j k l)
        (mul_nonneg (by norm_num) (le_of_lt hR))
    refine ⟨S + 1, by linarith, ?_⟩
    intro x y hx hy
    rw [Real.norm_eq_abs]
    have bilinear : ∀ i j : Fin n,
        |x i * x j - y i * y j| ≤ 2 * R * ‖x - y‖ := by
      intro i j
      have split : x i * x j - y i * y j =
          x i * (x j - y j) + (x i - y i) * y j := by ring
      rw [split]
      calc |x i * (x j - y j) + (x i - y i) * y j|
          ≤ |x i * (x j - y j)| + |(x i - y i) * y j| :=
            abs_add_le _ _
        _ = |x i| * |x j - y j| + |x i - y i| * |y j| := by
            rw [abs_mul, abs_mul]
        _ ≤ R * ‖x - y‖ + ‖x - y‖ * R := by
            gcongr
            · exact (norm_le_pi_norm x i).trans hx
            · rw [show x j - y j = (x - y) j from by simp [Pi.sub_apply]]
              exact norm_le_pi_norm (x - y) j
            · rw [show x i - y i = (x - y) i from by simp [Pi.sub_apply]]
              exact norm_le_pi_norm (x - y) i
            · exact (norm_le_pi_norm y j).trans hy
        _ = 2 * R * ‖x - y‖ := by ring
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    have hsum : |∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ((if netChange i j k l = ℓ then (tr.α i j k l : ℝ) * x i * x j else 0) -
         (if netChange i j k l = ℓ then (tr.α i j k l : ℝ) * y i * y j else 0))|
        ≤ S * ‖x - y‖ := by
      calc
        |∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          ((if netChange i j k l = ℓ then (tr.α i j k l : ℝ) * x i * x j else 0) -
           (if netChange i j k l = ℓ then (tr.α i j k l : ℝ) * y i * y j else 0))|
            ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
              |(if netChange i j k l = ℓ then (tr.α i j k l : ℝ) * x i * x j else 0) -
               (if netChange i j k l = ℓ then (tr.α i j k l : ℝ) * y i * y j else 0)| := by
              repeat first
                | exact Finset.abs_sum_le_sum_abs _ _
                | apply (Finset.abs_sum_le_sum_abs _ _).trans
                  apply Finset.sum_le_sum
                  intro _ _
        _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
              (tr.α i j k l : ℝ) * (2 * R * ‖x - y‖) := by
            apply Finset.sum_le_sum; intro i _
            apply Finset.sum_le_sum; intro j _
            apply Finset.sum_le_sum; intro k _
            apply Finset.sum_le_sum; intro l _
            by_cases h : netChange i j k l = ℓ
            · have hα : 0 ≤ (tr.α i j k l : ℝ) := by
                exact_mod_cast tr.nonneg i j k l
              simp only [h, ↓reduceIte]
              have hrewrite :
                  (tr.α i j k l : ℝ) * x i * x j -
                    (tr.α i j k l : ℝ) * y i * y j =
                  (tr.α i j k l : ℝ) * (x i * x j - y i * y j) := by
                ring
              rw [hrewrite, abs_mul, abs_of_nonneg hα]
              exact mul_le_mul_of_nonneg_left (bilinear i j) hα
            · have hα : 0 ≤ (tr.α i j k l : ℝ) := by
                exact_mod_cast tr.nonneg i j k l
              simp only [h, ↓reduceIte, sub_self, abs_zero]
              exact mul_nonneg hα
                (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hR)) (norm_nonneg _))
        _ = S * ‖x - y‖ := by
            dsimp [S]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro j _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro k _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro l _
            ring
    linarith [norm_nonneg (x - y)]

/-- The drift of the induced `RateSpec` equals the PLPP's balance field.

Re-indexing the drift sum by (i,j,k,l) and expanding netChange gives:
  F(x)_r = ∑_{i,j,k,l} (δ_{k,r}+δ_{l,r}-δ_{i,r}-δ_{j,r}) · α · x_i x_j
         = [∑_{i,j} x_i x_j (∑_l α_{i,j,r,l} + ∑_k α_{i,j,k,r})]
           - 2 x_r (∑_j x_j)
where the consumption uses ∑_{k,l} α_{i,j,k,l} = 1. -/
theorem toRateSpec_drift_eq_balanceField :
    tr.toRateSpec.drift = tr.balanceField := by
  ext x r
  simp only [RateSpec.drift, toRateSpec, rateSpecJumps, PLPPTransitions.balanceField]
  have hcollapse :
      (∑ ℓ ∈ Finset.univ.image (fun ijkl : Fin n × Fin n × Fin n × Fin n =>
        netChange ijkl.1 ijkl.2.1 ijkl.2.2.1 ijkl.2.2.2),
        (ℓ r : ℝ) *
          ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            if netChange i j k l = ℓ then
              (tr.α i j k l : ℝ) * x i * x j
            else 0) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        (netChange i j k l r : ℝ) * ((tr.α i j k l : ℝ) * x i * x j) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    let target : Fin n → ℤ := netChange i j k l
    have htarget_mem :
        target ∈ Finset.univ.image (fun ijkl : Fin n × Fin n × Fin n × Fin n =>
          netChange ijkl.1 ijkl.2.1 ijkl.2.2.1 ijkl.2.2.2) := by
      exact Finset.mem_image.mpr ⟨(i, j, k, l), Finset.mem_univ _, rfl⟩
    have hsingle :
        (∑ ℓ ∈ Finset.univ.image (fun ijkl : Fin n × Fin n × Fin n × Fin n =>
          netChange ijkl.1 ijkl.2.1 ijkl.2.2.1 ijkl.2.2.2),
          if netChange i j k l = ℓ then
            (ℓ r : ℝ) * ((tr.α i j k l : ℝ) * x i * x j)
          else 0) =
        (target r : ℝ) * ((tr.α i j k l : ℝ) * x i * x j) := by
      have hsingle' :
          (∑ ℓ ∈ Finset.univ.image (fun ijkl : Fin n × Fin n × Fin n × Fin n =>
            netChange ijkl.1 ijkl.2.1 ijkl.2.2.1 ijkl.2.2.2),
            if netChange i j k l = ℓ then
              (ℓ r : ℝ) * ((tr.α i j k l : ℝ) * x i * x j)
            else 0) =
          (if netChange i j k l = target then
            (target r : ℝ) * ((tr.α i j k l : ℝ) * x i * x j)
          else 0) := by
        refine Finset.sum_eq_single
          (s := Finset.univ.image (fun ijkl : Fin n × Fin n × Fin n × Fin n =>
            netChange ijkl.1 ijkl.2.1 ijkl.2.2.1 ijkl.2.2.2))
          (f := fun ℓ : Fin n → ℤ =>
            if netChange i j k l = ℓ then
              (ℓ r : ℝ) * ((tr.α i j k l : ℝ) * x i * x j)
            else 0)
          target ?_ ?_
        · intro ℓ hℓ hne
          have hneq : netChange i j k l ≠ ℓ := by
            intro h
            exact hne h.symm
          simp [hneq]
        · intro hnot
          exact False.elim (hnot htarget_mem)
      simpa [target] using hsingle'
    simpa [target] using hsingle
  rw [hcollapse]
  simp only [netChange]
  norm_num
  simp only [sub_mul, add_mul]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]
  have hsum_real : ∀ i j : Fin n,
      ∑ k : Fin n, ∑ l : Fin n, (tr.α i j k l : ℝ) = 1 := by
    intro i j
    exact_mod_cast tr.sum_one i j
  have hprod₁ :
      (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
        (tr.α i j r l : ℝ) * x i * x j) =
      ∑ i : Fin n, ∑ j : Fin n,
        x i * x j * ∑ l : Fin n, (tr.α i j r l : ℝ) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  have hprod₂ :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (tr.α i j k r : ℝ) * x i * x j) =
      ∑ i : Fin n, ∑ j : Fin n,
        x i * x j * ∑ k : Fin n, (tr.α i j k r : ℝ) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  have hcons₁ :
      (∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        (tr.α r j k l : ℝ) * x r * x j) =
      ∑ j : Fin n, x r * x j := by
    apply Finset.sum_congr rfl; intro j _
    calc
      (∑ k : Fin n, ∑ l : Fin n, (tr.α r j k l : ℝ) * x r * x j)
          = (∑ k : Fin n, ∑ l : Fin n, (tr.α r j k l : ℝ)) * x r * x j := by
            simp_rw [show ∀ k l : Fin n,
              (tr.α r j k l : ℝ) * x r * x j =
                (tr.α r j k l : ℝ) * (x r * x j) from by
                  intro k l; ring]
            calc
              (∑ k : Fin n, ∑ l : Fin n, (tr.α r j k l : ℝ) * (x r * x j))
                  = ∑ k : Fin n, (∑ l : Fin n, (tr.α r j k l : ℝ)) * (x r * x j) := by
                    apply Finset.sum_congr rfl; intro k _
                    rw [← Finset.sum_mul]
              _ = (∑ k : Fin n, ∑ l : Fin n, (tr.α r j k l : ℝ)) * (x r * x j) := by
                    rw [← Finset.sum_mul]
              _ = (∑ k : Fin n, ∑ l : Fin n, (tr.α r j k l : ℝ)) * x r * x j := by
                    ring
      _ = x r * x j := by rw [hsum_real r j]; ring
  have hcons₂ :
      (∑ i : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        (tr.α i r k l : ℝ) * x i * x r) =
      ∑ i : Fin n, x r * x i := by
    apply Finset.sum_congr rfl; intro i _
    calc
      (∑ k : Fin n, ∑ l : Fin n, (tr.α i r k l : ℝ) * x i * x r)
          = x r * (∑ k : Fin n, ∑ l : Fin n, (tr.α i r k l : ℝ)) * x i := by
            simp_rw [show ∀ k l : Fin n,
              (tr.α i r k l : ℝ) * x i * x r =
                (tr.α i r k l : ℝ) * (x r * x i) from by
                  intro k l; ring]
            calc
              (∑ k : Fin n, ∑ l : Fin n, (tr.α i r k l : ℝ) * (x r * x i))
                  = ∑ k : Fin n, (∑ l : Fin n, (tr.α i r k l : ℝ)) * (x r * x i) := by
                    apply Finset.sum_congr rfl; intro k _
                    rw [← Finset.sum_mul]
              _ = (∑ k : Fin n, ∑ l : Fin n, (tr.α i r k l : ℝ)) * (x r * x i) := by
                    rw [← Finset.sum_mul]
              _ = x r * (∑ k : Fin n, ∑ l : Fin n, (tr.α i r k l : ℝ)) * x i := by
                    ring
      _ = x r * x i := by rw [hsum_real i r]; ring
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hprod₁, hprod₂, hcons₁, hcons₂]
  have hprod_sum :
      (∑ i : Fin n, ∑ j : Fin n,
        x i * x j * (∑ k : Fin n, (tr.α i j r k : ℝ) +
          ∑ k : Fin n, (tr.α i j k r : ℝ))) =
      (∑ i : Fin n, ∑ j : Fin n,
        x i * x j * ∑ l : Fin n, (tr.α i j r l : ℝ)) +
      (∑ i : Fin n, ∑ j : Fin n,
        x i * x j * ∑ k : Fin n, (tr.α i j k r : ℝ)) := by
    simp_rw [mul_add]
    conv_lhs =>
      arg 2
      intro i
      rw [Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib]
  have htwice :
      (∑ i : Fin n, 2 * x r * x i) =
      (∑ j : Fin n, x r * x j) + (∑ j : Fin n, x r * x j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    ring
  rw [hprod_sum, htwice]
  ring

/-- The balance field is Lipschitz on bounded balls. -/
theorem balanceField_lipschitz_on_ball (R : ℝ) (hR : 0 < R) :
    ∃ L > 0, ∀ x y : Fin n → ℝ, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖tr.balanceField x - tr.balanceField y‖ ≤ L * ‖x - y‖ := by
  rw [← tr.toRateSpec_drift_eq_balanceField]
  exact tr.toRateSpec.drift_lipschitz_on_ball R hR

theorem rateSpecJumps_conservative :
    ∀ ℓ ∈ tr.rateSpecJumps, ∑ i, ℓ i = 0 := by
  intro ℓ hℓ
  simp only [rateSpecJumps, Finset.mem_image, Finset.mem_univ, true_and] at hℓ
  obtain ⟨⟨i, j, k, l⟩, rfl⟩ := hℓ
  exact netChange_sum_zero i j k l

end PLPPTransitions

/-! ## The Probability Simplex -/

def Simplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-! ## Extended Computability (Huang-Huls, continuum of equilibria)

Definition 9 of [LPP]: a number ν is computable by a PLPP if, from
a fixed rational initialization on the simplex, the marked-state
readout of the ODE trajectory converges to ν.

No isolated equilibrium is required. The initial condition for the
Stage 2 construction is x = (1, 0, 0, ..., 0). -/

/-- A PLPP continuum computation: a concrete ODE trajectory from rational
initial data whose marked-state readout converges to ν.

This is the extended notion from [LPP] Definition 9, compatible with
systems having a continuum of equilibria. -/
structure PLPPContinuumComputation {n : ℕ}
    (tr : PLPPTransitions n) (marked : Finset (Fin n)) (ν : ℝ) where
  /-- The ODE solution trajectory. -/
  sol : ℝ → Fin n → ℝ
  /-- Initial condition has rational coordinates. -/
  init_rational : ∀ i, ∃ q : ℚ, sol 0 i = (q : ℝ)
  /-- Initial condition is on the simplex. -/
  init_simplex : ∑ i, sol 0 i = 1
  /-- Initial condition is non-negative. -/
  init_nonneg : ∀ i, 0 ≤ sol 0 i
  /-- The trajectory stays on the simplex (conservation). -/
  simplex : ∀ t, 0 ≤ t → ∑ i, sol t i = 1
  /-- The trajectory stays non-negative. -/
  nonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ sol t i
  /-- The trajectory satisfies the balance equation ODE. -/
  ode : ∀ t, 0 ≤ t → HasDerivAt sol (tr.balanceField (sol t)) t
  /-- The marked-state readout converges to the target. -/
  readout_tendsto :
    Filter.Tendsto (fun t => ∑ i ∈ marked, sol t i)
      Filter.atTop (nhds ν)

namespace PLPPContinuumComputation

/-- A continuum PLPP computation is a Kurtz mean-field solution for the
`RateSpec` induced by the same transition table. -/
noncomputable def toMeanFieldSolution {n : ℕ}
    {tr : PLPPTransitions n} {marked : Finset (Fin n)} {ν : ℝ}
    (C : PLPPContinuumComputation tr marked ν) :
    Kurtz.MeanFieldSolution n tr.toRateSpec where
  x₀ := C.sol 0
  sol := C.sol
  sol_init := rfl
  sol_ode := by
    intro t ht
    rw [tr.toRateSpec_drift_eq_balanceField]
    exact C.ode t ht

end PLPPContinuumComputation

/-! ## Classical Computability (BFK, isolated equilibria)

For the finite-equilibria setting of [BFK], we keep the stronger
isolated-equilibrium structure needed for Koegler Corollary 2. -/

structure SimplexEquilibrium {n : ℕ} (tr : PLPPTransitions n) where
  point : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ point i
  sum_one : ∑ i, point i = 1
  is_eq : tr.balanceField point = 0

structure PLPPIsolatedComputation {n : ℕ}
    (tr : PLPPTransitions n) (marked : Finset (Fin n)) (ν : ℝ) where
  /-- The isolated stable equilibrium. -/
  eq : SimplexEquilibrium tr
  /-- The marked-state proportion at equilibrium equals the target. -/
  target_eq : ∑ i ∈ marked, eq.point i = ν
  /-- Basin of attraction (simplex-relative). -/
  basin : Set (Fin n → ℝ)
  basin_subset_simplex : basin ⊆ Simplex n
  basin_rel_open : ∃ U : Set (Fin n → ℝ), IsOpen U ∧ basin = U ∩ Simplex n
  point_mem_basin : eq.point ∈ basin
  /-- Every ODE trajectory starting in the basin converges to the equilibrium. -/
  converges : ∀ sol : ℝ → Fin n → ℝ,
    sol 0 ∈ basin →
    (∀ t ≥ 0, HasDerivAt sol (tr.balanceField (sol t)) t) →
    Filter.Tendsto sol Filter.atTop (nhds eq.point)
  /-- Exponential convergence rate. -/
  exp_decay : ∃ C lam : ℝ, 0 < C ∧ 0 < lam ∧ ∀ sol : ℝ → Fin n → ℝ,
    sol 0 ∈ basin →
    (∀ t ≥ 0, HasDerivAt sol (tr.balanceField (sol t)) t) →
    ∀ t ≥ 0, ‖sol t - eq.point‖ ≤ C * ‖sol 0 - eq.point‖ * Real.exp (-lam * t)

namespace PLPPIsolatedComputation

/-- Any trajectory satisfying the isolated-computation balance ODE is a Kurtz
mean-field solution for the `RateSpec` induced by the same transition table. -/
noncomputable def toMeanFieldSolution {n : ℕ}
    {tr : PLPPTransitions n} {marked : Finset (Fin n)} {ν : ℝ}
    (_hcomp : PLPPIsolatedComputation tr marked ν)
    (sol : ℝ → Fin n → ℝ)
    (hsol_ode : ∀ t ≥ 0, HasDerivAt sol (tr.balanceField (sol t)) t) :
    Kurtz.MeanFieldSolution n tr.toRateSpec where
  x₀ := sol 0
  sol := sol
  sol_init := rfl
  sol_ode := by
    intro t ht
    rw [tr.toRateSpec_drift_eq_balanceField]
    exact hsol_ode t ht

/-- Turn an isolated-computation certificate into the readout-level continuum
notion, once a concrete rational-initialized trajectory in the basin is
provided.

`PLPPIsolatedComputation` itself does not include a rational initial point or
an ODE existence witness, so those data must be supplied separately.  The
isolated convergence field then gives the required marked-readout convergence. -/
noncomputable def toContinuum_of_solution {n : ℕ}
    {tr : PLPPTransitions n} {marked : Finset (Fin n)} {ν : ℝ}
    (hcomp : PLPPIsolatedComputation tr marked ν)
    (sol : ℝ → Fin n → ℝ)
    (init_rational : ∀ i, ∃ q : ℚ, sol 0 i = (q : ℝ))
    (init_simplex : ∑ i, sol 0 i = 1)
    (init_nonneg : ∀ i, 0 ≤ sol 0 i)
    (simplex : ∀ t, 0 ≤ t → ∑ i, sol t i = 1)
    (nonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ sol t i)
    (hsol_init : sol 0 ∈ hcomp.basin)
    (hsol_ode : ∀ t, 0 ≤ t → HasDerivAt sol (tr.balanceField (sol t)) t) :
    PLPPContinuumComputation tr marked ν where
  sol := sol
  init_rational := init_rational
  init_simplex := init_simplex
  init_nonneg := init_nonneg
  simplex := simplex
  nonneg := nonneg
  ode := hsol_ode
  readout_tendsto := by
    have hconv := hcomp.converges sol hsol_init hsol_ode
    have hread_cont : Continuous fun y : Fin n → ℝ => ∑ i ∈ marked, y i :=
      continuous_finset_sum _ fun i _ => continuous_apply i
    simpa [hcomp.target_eq] using (hread_cont.tendsto hcomp.eq.point).comp hconv

end PLPPIsolatedComputation

/-! ## Readout concentration interfaces -/

/-- Marked-state readout. -/
noncomputable def markedReadout {n : ℕ} (marked : Finset (Fin n))
    (x : Fin n → ℝ) : ℝ :=
  ∑ i ∈ marked, x i

/-- The marked-state readout is Lipschitz with constant `marked.card` for the
ambient finite-dimensional norm. -/
theorem markedReadout_lipschitz_bound {n : ℕ} (marked : Finset (Fin n))
    (x y : Fin n → ℝ) :
    |markedReadout marked x - markedReadout marked y| ≤
      (marked.card : ℝ) * ‖x - y‖ := by
  classical
  simp only [markedReadout]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ marked, (x i - y i)|
        ≤ ∑ i ∈ marked, |x i - y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ marked, ‖x - y‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [show x i - y i = (x - y) i by rfl, ← Real.norm_eq_abs]
        exact norm_le_pi_norm (x - y) i
    _ = (marked.card : ℝ) * ‖x - y‖ := by
        rw [Finset.sum_const, nsmul_eq_mul]

private theorem eventually_le_of_tendsto_ennreal_zero
    {f : ℕ → ENNReal}
    (hf : Filter.Tendsto f Filter.atTop (nhds 0))
    {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, f N ≤ ENNReal.ofReal η := by
  have hη' : (0 : ENNReal) < ENNReal.ofReal η := ENNReal.ofReal_pos.mpr hη
  have hev : ∀ᶠ N in Filter.atTop, f N < ENNReal.ofReal η :=
    hf.eventually (Iio_mem_nhds hη')
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  exact ⟨N₀, fun N hN => le_of_lt (hN₀ N hN)⟩

/-- Fixed-time Kurtz convergence in probability, stated in the exact
epsilon/eta form used by the LPP stochastic wrappers.  This is the honest
interface supplied by finite-horizon Kurtz: for each fixed time horizon `T`,
the population threshold `N₀` may depend on `T`. -/
def FixedTimeKurtzConvergence {n : ℕ} (tr : PLPPTransitions n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : (N : ℕ) → Kurtz.DensityProcess n tr.toRateSpec N μ)
    (sol : ℝ → Fin n → ℝ) : Prop :=
  ∀ T > 0, ∀ δ > 0, ∀ η > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    μ {ω | ‖(X N).process T ω - sol T‖ > δ} ≤ ENNReal.ofReal η

/-- An ODE trajectory with a derivative at every non-negative time is bounded
on each compact interval. -/
private theorem exists_solution_norm_bound_on_Icc {n : ℕ}
    (sol : ℝ → Fin n → ℝ)
    (hsol_deriv : ∀ t ≥ 0, ∃ v : Fin n → ℝ, HasDerivAt sol v t)
    {T : ℝ} (_hT : 0 < T) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ T → ‖sol t‖ ≤ B := by
  have hcont : ContinuousOn sol (Set.Icc (0 : ℝ) T) := by
    intro t ht
    obtain ⟨v, hv⟩ := hsol_deriv t ht.1
    exact hv.continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨B, fun t ht0 htT => hB t ⟨ht0, htT⟩⟩

/-- Finite-horizon endpoint errors have a real upper bound.  The stochastic
process is bounded by the `DensityProcess` density invariant, while the ODE
trajectory is bounded on compact intervals by differentiability. -/
private theorem finiteHorizonError_bddAbove {n : ℕ}
    {tr : PLPPTransitions n}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : (N : ℕ) → Kurtz.DensityProcess n tr.toRateSpec N μ)
    (sol : ℝ → Fin n → ℝ)
    (hsol_deriv : ∀ t ≥ 0, ∃ v : Fin n → ℝ, HasDerivAt sol v t)
    (T : ℝ) (hT : 0 < T) (N : ℕ) (ω : Ω) :
    BddAbove (Set.range fun t : ℝ =>
      ⨆ (_ : 0 ≤ t ∧ t ≤ T), ‖(X N).process t ω - sol t‖) := by
  obtain ⟨B₀, hB₀⟩ := exists_solution_norm_bound_on_Icc sol hsol_deriv hT
  let B : ℝ := 1 + max B₀ 0
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨B, ?_⟩
  rintro y ⟨t, rfl⟩
  refine Real.iSup_le ?_ hB_nonneg
  intro ht
  calc
    ‖(X N).process t ω - sol t‖
        ≤ ‖(X N).process t ω‖ + ‖sol t‖ := norm_sub_le _ _
    _ ≤ 1 + B₀ := by
      exact add_le_add ((X N).process_norm_le_one t ω) (hB₀ t ht.1 ht.2)
    _ ≤ B := by
      dsimp [B]
      exact add_le_add (le_refl 1) (le_max_left B₀ 0)

/-- The fixed-time bad event is contained in the finite-horizon supremum bad
event, once the real-valued supremum is known to be bounded above. -/
private theorem fixedTime_event_measure_le_sup_event_measure {n : ℕ}
    {tr : PLPPTransitions n}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : (N : ℕ) → Kurtz.DensityProcess n tr.toRateSpec N μ)
    (sol : ℝ → Fin n → ℝ)
    (hsol_deriv : ∀ t ≥ 0, ∃ v : Fin n → ℝ, HasDerivAt sol v t)
    (T : ℝ) (hT : 0 < T) (δ : ℝ) (_hδ : 0 < δ) (N : ℕ) :
    μ {ω | ‖(X N).process T ω - sol T‖ > δ} ≤
      μ {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        ‖(X N).process t ω - sol t‖ > δ} := by
  refine MeasureTheory.measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hinner_bdd :
      BddAbove (Set.range fun _ : 0 ≤ T ∧ T ≤ T =>
        ‖(X N).process T ω - sol T‖) := by
    refine ⟨‖(X N).process T ω - sol T‖, ?_⟩
    rintro y ⟨_, rfl⟩
    exact le_rfl
  have hpoint_le_inner :
      ‖(X N).process T ω - sol T‖ ≤
        ⨆ (_ : 0 ≤ T ∧ T ≤ T), ‖(X N).process T ω - sol T‖ := by
    exact le_ciSup hinner_bdd ⟨le_of_lt hT, le_rfl⟩
  have hinner_le_sup :
      (⨆ (_ : 0 ≤ T ∧ T ≤ T), ‖(X N).process T ω - sol T‖) ≤
        ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), ‖(X N).process t ω - sol t‖ := by
    exact le_ciSup (finiteHorizonError_bddAbove μ X sol hsol_deriv T hT N ω) T
  exact lt_of_lt_of_le hω (hpoint_le_inner.trans hinner_le_sup)

/-- Filter-form fixed-time Kurtz convergence implies the epsilon/eta form. -/
theorem fixedTimeKurtzConvergence_of_tendsto {n : ℕ}
    {tr : PLPPTransitions n}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : (N : ℕ) → Kurtz.DensityProcess n tr.toRateSpec N μ)
    (sol : ℝ → Fin n → ℝ)
    (hKurtz : ∀ T > 0, ∀ δ > 0,
      Filter.Tendsto
        (fun N : ℕ => μ {ω | ‖(X N).process T ω - sol T‖ > δ})
        Filter.atTop (nhds 0)) :
    FixedTimeKurtzConvergence tr μ X sol := by
  intro T hT δ hδ η hη
  exact eventually_le_of_tendsto_ennreal_zero (hKurtz T hT δ hδ) hη

/-- Fixed-time convergence follows from finite-horizon supremum convergence.
The endpoint-vs-sup event comparison is proved internally from the density
path bound in `DensityProcess` and compact-interval boundedness of the ODE
trajectory. -/
theorem fixedTimeKurtzConvergence_of_sup_tendsto {n : ℕ}
    {tr : PLPPTransitions n}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : (N : ℕ) → Kurtz.DensityProcess n tr.toRateSpec N μ)
    (sol : ℝ → Fin n → ℝ)
    (hsol_deriv : ∀ t ≥ 0, ∃ v : Fin n → ℝ, HasDerivAt sol v t)
    (hSup : ∀ T > 0, ∀ δ > 0,
      Filter.Tendsto
        (fun N : ℕ => μ {ω |
          ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
            ‖(X N).process t ω - sol t‖ > δ})
        Filter.atTop (nhds 0)) :
    FixedTimeKurtzConvergence tr μ X sol := by
  intro T hT δ hδ η hη
  obtain ⟨N₀, hN₀⟩ :=
    eventually_le_of_tendsto_ennreal_zero (hSup T hT δ hδ) hη
  refine ⟨N₀, fun N hN => ?_⟩
  exact (fixedTime_event_measure_le_sup_event_measure
    μ X sol hsol_deriv T hT δ hδ N).trans (hN₀ N hN)

/-- Bridge from the existing Kurtz finite-horizon theorem to the LPP
fixed-time API.

The packaged `DensityProcessFamily` carries the uniform QV bound and the
uniform deterministic Gronwall event inclusion.  The Gronwall-Markov bound
itself is constructed internally by `Kurtz.kurtz_gm_of_density_process_family`,
and the endpoint/sup comparison is discharged from the density path bound and
the mean-field ODE regularity. -/
theorem fixedTimeKurtzConvergence_of_kurtz_convergence_for_density_dep_ctmc {n : ℕ}
    {tr : PLPPTransitions n}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (mf : Kurtz.MeanFieldSolution n tr.toRateSpec)
    (X : Kurtz.DensityProcessFamily n tr.toRateSpec μ)
    (h_init : ∀ ε > 0,
      Filter.Tendsto
        (fun N => μ {ω | ‖(X.densityProcess N).init ω - mf.x₀‖ > ε})
        Filter.atTop (nhds 0)) :
    FixedTimeKurtzConvergence tr μ X.densityProcess mf.sol := by
  refine fixedTimeKurtzConvergence_of_sup_tendsto μ X.densityProcess mf.sol ?_ ?_
  · intro t ht
    exact ⟨tr.toRateSpec.drift (mf.sol t), mf.sol_ode t ht⟩
  intro T hT δ hδ
  exact Kurtz.kurtz_convergence_for_density_process_family
    mf X hT h_init δ hδ

/-- Named LPP bridge: a packaged uniform `DensityProcessFamily` gives the LPP
`FixedTimeKurtzConvergence` API once the initial laws converge. -/
theorem densityProcess_gives_fixedTimeKurtz {n : ℕ}
    {tr : PLPPTransitions n} {marked : Finset (Fin n)} {ν : ℝ}
    (hcomp : PLPPIsolatedComputation tr marked ν)
    (sol : ℝ → Fin n → ℝ)
    (hsol_ode : ∀ t ≥ 0, HasDerivAt sol (tr.balanceField (sol t)) t)
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : Kurtz.DensityProcessFamily n tr.toRateSpec μ)
    (h_init : ∀ ε > 0,
      Filter.Tendsto
        (fun N => μ {ω | ‖(X.densityProcess N).init ω - sol 0‖ > ε})
        Filter.atTop (nhds 0)) :
    FixedTimeKurtzConvergence tr μ X.densityProcess sol := by
  let mf := hcomp.toMeanFieldSolution sol hsol_ode
  exact fixedTimeKurtzConvergence_of_kurtz_convergence_for_density_dep_ctmc
    μ mf X h_init

/-! ## Double Limit Theorems

### Theorem A: Exchanged order (works for both notions)

  lim_{t→∞} [lim_{N→∞} readout(X̄^N(t))] = lim_{t→∞} readout(x(t)) = ν

For the extended notion, readout convergence is the assumption itself.
For the isolated notion, it follows from full-state convergence.

### Theorem B: Standard order (isolated notion only)

  For large N and t, readout(X̄^N(t)) ≈ ν with high probability.
  Needs exponential stability + Koegler Corollary 2. -/

/-- Theorem A (extended): The exchanged double limit.
The readout convergence is a direct field of `PLPPContinuumComputation`. -/
theorem exchanged_limit_readout {n : ℕ}
    {tr : PLPPTransitions n} {marked : Finset (Fin n)} {ν : ℝ}
    (C : PLPPContinuumComputation tr marked ν) :
    Filter.Tendsto (fun t => ∑ i ∈ marked, C.sol t i)
      Filter.atTop (nhds ν) :=
  C.readout_tendsto

/-- Theorem A (isolated): Full-state convergence implies readout convergence. -/
theorem exchanged_limit_isolated {n : ℕ}
    {tr : PLPPTransitions n} {marked : Finset (Fin n)} {ν : ℝ}
    (hcomp : PLPPIsolatedComputation tr marked ν)
    (sol : ℝ → Fin n → ℝ)
    (hsol_init : sol 0 ∈ hcomp.basin)
    (hsol_ode : ∀ t ≥ 0, HasDerivAt sol (tr.balanceField (sol t)) t) :
    Filter.Tendsto (fun t => ∑ i ∈ marked, sol t i)
      Filter.atTop (nhds ν) := by
  have hconv := hcomp.converges sol hsol_init hsol_ode
  have hcont : Continuous fun y : Fin n → ℝ => ∑ i ∈ marked, y i :=
    continuous_finset_sum _ fun i _ => continuous_apply i
  simpa [hcomp.target_eq] using (hcont.tendsto hcomp.eq.point).comp hconv

/-- Stochastic exchanged-limit theorem (combining Kurtz + ODE readout).

For a PLPPContinuumComputation with trajectory `sol`, finite-horizon Kurtz
gives `readout(X̄^N(t)) → readout(sol(t))` in probability for each fixed t.
The ODE readout convergence `readout(sol(t)) → ν` then gives:

  lim_{t→∞} lim_{N→∞} readout(X̄^N(t)) = ν

This is the full exchanged-order double limit. The inner limit (Kurtz)
eliminates stochasticity; the outer limit is deterministic.

In the formalization, we express this as: for any ε > 0 and T > 0,
there exists N₀ such that for N ≥ N₀,
  P(|readout(X̄^N(T)) - readout(sol(T))| > ε) is small.
Combined with readout_tendsto, the double limit follows. -/
theorem stochastic_exchanged_limit {n : ℕ}
    {tr : PLPPTransitions n} {marked : Finset (Fin n)} {ν : ℝ}
    (C : PLPPContinuumComputation tr marked ν)
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : (N : ℕ) → Kurtz.DensityProcess n tr.toRateSpec N μ)
    (T : ℝ) (_hT : 0 < T)
    (hKurtz : ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      μ {ω | ‖(X N).process T ω - C.sol T‖ > ε} ≤
        ENNReal.ofReal ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      μ {ω | |markedReadout marked ((X N).process T ω) -
              markedReadout marked (C.sol T)| > ε} ≤
        ENNReal.ofReal (ε / ((marked.card : ℝ) + 1)) := by
  let δ := ε / ((marked.card : ℝ) + 1)
  have hδ : 0 < δ := by positivity
  obtain ⟨N₀, hN₀⟩ := hKurtz δ hδ
  refine ⟨N₀, fun N hN => ?_⟩
  refine (MeasureTheory.measure_mono ?_).trans (hN₀ N hN)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hread := markedReadout_lipschitz_bound marked ((X N).process T ω) (C.sol T)
  by_contra hnot
  have hnorm_le : ‖(X N).process T ω - C.sol T‖ ≤ δ := le_of_not_gt hnot
  have : |markedReadout marked ((X N).process T ω) -
          markedReadout marked (C.sol T)| < ε := by
    calc |markedReadout marked ((X N).process T ω) -
            markedReadout marked (C.sol T)|
        ≤ (marked.card : ℝ) * ‖(X N).process T ω - C.sol T‖ := hread
      _ ≤ (marked.card : ℝ) * δ := by gcongr
      _ < ε := by dsimp [δ]; field_simp; nlinarith [Nat.cast_nonneg (α := ℝ) marked.card]
  exact not_lt_of_ge (le_of_lt this) hω

/-- Exchanged-order stochastic convergence all the way to the target `ν`.

This is the precise epsilon/eta form of
`lim_{t→∞} lim_{N→∞} markedReadout(X̄^N(t)) = ν`: once `T` is large enough
for the deterministic ODE readout to be near `ν`, finite-time Kurtz
concentration at that fixed `T` makes the stochastic readout near the ODE
readout with arbitrarily high probability. -/
theorem stochastic_exchanged_limit_to_target {n : ℕ}
    {tr : PLPPTransitions n} {marked : Finset (Fin n)} {ν : ℝ}
    (C : PLPPContinuumComputation tr marked ν)
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : (N : ℕ) → Kurtz.DensityProcess n tr.toRateSpec N μ)
    (hKurtz : ∀ T > 0, ∀ δ > 0, ∀ η > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      μ {ω | ‖(X N).process T ω - C.sol T‖ > δ} ≤ ENNReal.ofReal η)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T ≥ T₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      μ {ω | |markedReadout marked ((X N).process T ω) - ν| > ε} ≤
        ENNReal.ofReal η := by
  classical
  let ρ : ℝ := ε / 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have htend := C.readout_tendsto
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨Traw, hTraw⟩ := htend ρ hρ
  let T₀ : ℝ := max Traw 1
  have hT₀_pos : 0 < T₀ := lt_of_lt_of_le zero_lt_one (le_max_right Traw 1)
  refine ⟨T₀, hT₀_pos, ?_⟩
  intro T hT
  have hTraw_le : Traw ≤ T := (le_max_left Traw 1).trans hT
  have hT_pos : 0 < T := hT₀_pos.trans_le hT
  have hode :
      |markedReadout marked (C.sol T) - ν| < ρ := by
    simpa [markedReadout, Real.dist_eq] using hTraw T hTraw_le
  let δ : ℝ := ρ / ((marked.card : ℝ) + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨N₀, hN₀⟩ := hKurtz T hT_pos δ hδ η hη
  refine ⟨N₀, fun N hN => ?_⟩
  refine (MeasureTheory.measure_mono ?_).trans (hN₀ N hN)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hnot
  have hnorm_le : ‖(X N).process T ω - C.sol T‖ ≤ δ := le_of_not_gt hnot
  have hread := markedReadout_lipschitz_bound marked ((X N).process T ω) (C.sol T)
  have hread_lt :
      |markedReadout marked ((X N).process T ω) -
          markedReadout marked (C.sol T)| < ρ := by
    calc
      |markedReadout marked ((X N).process T ω) -
          markedReadout marked (C.sol T)|
          ≤ (marked.card : ℝ) * ‖(X N).process T ω - C.sol T‖ := hread
      _ ≤ (marked.card : ℝ) * δ := by
          gcongr
      _ < ρ := by
          dsimp [δ]
          have hden : 0 < (marked.card : ℝ) + 1 := by positivity
          field_simp [hden.ne']
          nlinarith [Nat.cast_nonneg (α := ℝ) marked.card, hρ]
  have htri :
      |markedReadout marked ((X N).process T ω) - ν| ≤
        |markedReadout marked ((X N).process T ω) -
          markedReadout marked (C.sol T)| +
        |markedReadout marked (C.sol T) - ν| := by
    have hsplit :
        markedReadout marked ((X N).process T ω) - ν =
          (markedReadout marked ((X N).process T ω) -
            markedReadout marked (C.sol T)) +
          (markedReadout marked (C.sol T) - ν) := by
      ring
    rw [hsplit]
    exact abs_add_le _ _
  have hmain : |markedReadout marked ((X N).process T ω) - ν| < ε := by
    calc
      |markedReadout marked ((X N).process T ω) - ν|
          ≤ |markedReadout marked ((X N).process T ω) -
              markedReadout marked (C.sol T)| +
            |markedReadout marked (C.sol T) - ν| := htri
      _ < ρ + ρ := add_lt_add hread_lt hode
      _ = ε := by
          dsimp [ρ]
          ring
  exact not_lt_of_ge (le_of_lt hmain) hω

/-- Same exchanged-order theorem as `stochastic_exchanged_limit_to_target`,
but with the finite-time Kurtz input stated in the usual filter form:
for each fixed `T`, the deviation probability tends to zero as `N → ∞`. -/
theorem stochastic_exchanged_limit_to_target_of_tendsto {n : ℕ}
    {tr : PLPPTransitions n} {marked : Finset (Fin n)} {ν : ℝ}
    (C : PLPPContinuumComputation tr marked ν)
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : (N : ℕ) → Kurtz.DensityProcess n tr.toRateSpec N μ)
    (hKurtz : ∀ T > 0, ∀ δ > 0,
      Filter.Tendsto
        (fun N : ℕ => μ {ω | ‖(X N).process T ω - C.sol T‖ > δ})
        Filter.atTop (nhds 0))
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T ≥ T₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      μ {ω | |markedReadout marked ((X N).process T ω) - ν| > ε} ≤
        ENNReal.ofReal η := by
  exact stochastic_exchanged_limit_to_target C μ X
    (fun T hT δ hδ η hη =>
      eventually_le_of_tendsto_ennreal_zero (hKurtz T hT δ hδ) hη)
    ε η hε hη

/-- Exchanged-order stochastic convergence to `ν` for the isolated-equilibrium
API.  The proof is the same epsilon/eta argument as
`stochastic_exchanged_limit_to_target`, with the deterministic readout
convergence supplied by `exchanged_limit_isolated`. -/
theorem stochastic_exchanged_limit_isolated_to_target {n : ℕ}
    {tr : PLPPTransitions n} {marked : Finset (Fin n)} {ν : ℝ}
    (hcomp : PLPPIsolatedComputation tr marked ν)
    (sol : ℝ → Fin n → ℝ)
    (hsol_init : sol 0 ∈ hcomp.basin)
    (hsol_ode : ∀ t ≥ 0, HasDerivAt sol (tr.balanceField (sol t)) t)
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : (N : ℕ) → Kurtz.DensityProcess n tr.toRateSpec N μ)
    (hKurtz : ∀ T > 0, ∀ δ > 0, ∀ η > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      μ {ω | ‖(X N).process T ω - sol T‖ > δ} ≤ ENNReal.ofReal η)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T ≥ T₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      μ {ω | |markedReadout marked ((X N).process T ω) - ν| > ε} ≤
        ENNReal.ofReal η := by
  classical
  let ρ : ℝ := ε / 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have htend := exchanged_limit_isolated hcomp sol hsol_init hsol_ode
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨Traw, hTraw⟩ := htend ρ hρ
  let T₀ : ℝ := max Traw 1
  have hT₀_pos : 0 < T₀ := lt_of_lt_of_le zero_lt_one (le_max_right Traw 1)
  refine ⟨T₀, hT₀_pos, ?_⟩
  intro T hT
  have hTraw_le : Traw ≤ T := (le_max_left Traw 1).trans hT
  have hT_pos : 0 < T := hT₀_pos.trans_le hT
  have hode :
      |markedReadout marked (sol T) - ν| < ρ := by
    simpa [markedReadout, Real.dist_eq] using hTraw T hTraw_le
  let δ : ℝ := ρ / ((marked.card : ℝ) + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨N₀, hN₀⟩ := hKurtz T hT_pos δ hδ η hη
  refine ⟨N₀, fun N hN => ?_⟩
  refine (MeasureTheory.measure_mono ?_).trans (hN₀ N hN)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hnot
  have hnorm_le : ‖(X N).process T ω - sol T‖ ≤ δ := le_of_not_gt hnot
  have hread := markedReadout_lipschitz_bound marked ((X N).process T ω) (sol T)
  have hread_lt :
      |markedReadout marked ((X N).process T ω) -
          markedReadout marked (sol T)| < ρ := by
    calc
      |markedReadout marked ((X N).process T ω) -
          markedReadout marked (sol T)|
          ≤ (marked.card : ℝ) * ‖(X N).process T ω - sol T‖ := hread
      _ ≤ (marked.card : ℝ) * δ := by
          gcongr
      _ < ρ := by
          dsimp [δ]
          have hden : 0 < (marked.card : ℝ) + 1 := by positivity
          field_simp [hden.ne']
          nlinarith [Nat.cast_nonneg (α := ℝ) marked.card, hρ]
  have htri :
      |markedReadout marked ((X N).process T ω) - ν| ≤
        |markedReadout marked ((X N).process T ω) -
          markedReadout marked (sol T)| +
        |markedReadout marked (sol T) - ν| := by
    have hsplit :
        markedReadout marked ((X N).process T ω) - ν =
          (markedReadout marked ((X N).process T ω) -
            markedReadout marked (sol T)) +
          (markedReadout marked (sol T) - ν) := by
      ring
    rw [hsplit]
    exact abs_add_le _ _
  have hmain : |markedReadout marked ((X N).process T ω) - ν| < ε := by
    calc
      |markedReadout marked ((X N).process T ω) - ν|
          ≤ |markedReadout marked ((X N).process T ω) -
              markedReadout marked (sol T)| +
            |markedReadout marked (sol T) - ν| := htri
      _ < ρ + ρ := add_lt_add hread_lt hode
      _ = ε := by
          dsimp [ρ]
          ring
  exact not_lt_of_ge (le_of_lt hmain) hω

/-- Filter-form version of
`stochastic_exchanged_limit_isolated_to_target`. -/
theorem stochastic_exchanged_limit_isolated_to_target_of_tendsto {n : ℕ}
    {tr : PLPPTransitions n} {marked : Finset (Fin n)} {ν : ℝ}
    (hcomp : PLPPIsolatedComputation tr marked ν)
    (sol : ℝ → Fin n → ℝ)
    (hsol_init : sol 0 ∈ hcomp.basin)
    (hsol_ode : ∀ t ≥ 0, HasDerivAt sol (tr.balanceField (sol t)) t)
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : (N : ℕ) → Kurtz.DensityProcess n tr.toRateSpec N μ)
    (hKurtz : ∀ T > 0, ∀ δ > 0,
      Filter.Tendsto
        (fun N : ℕ => μ {ω | ‖(X N).process T ω - sol T‖ > δ})
        Filter.atTop (nhds 0))
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T ≥ T₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      μ {ω | |markedReadout marked ((X N).process T ω) - ν| > ε} ≤
        ENNReal.ofReal η := by
  exact stochastic_exchanged_limit_isolated_to_target hcomp sol hsol_init hsol_ode μ X
    (fun T hT δ hδ η hη =>
      eventually_le_of_tendsto_ennreal_zero (hKurtz T hT δ hδ) hη)
    ε η hε hη

/-- Single-time state concentration near the isolated ODE equilibrium.

This is the corrected K3 shape.  It is an exchanged-order statement:
first choose a large deterministic time `T`, then choose `N` large enough for
that fixed `T`.  The threshold `N₀` is allowed to depend on `T`; no
uniform-in-all-large-times stochastic stability is claimed here. -/
theorem single_time_state_concentration {n : ℕ}
    {tr : PLPPTransitions n} {marked : Finset (Fin n)} {ν : ℝ}
    (hcomp : PLPPIsolatedComputation tr marked ν)
    (sol : ℝ → Fin n → ℝ)
    (hsol_init : sol 0 ∈ hcomp.basin)
    (hsol_ode : ∀ t ≥ 0, HasDerivAt sol (tr.balanceField (sol t)) t)
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : (N : ℕ) → Kurtz.DensityProcess n tr.toRateSpec N μ)
    (hKurtz : FixedTimeKurtzConvergence tr μ X sol)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T ≥ T₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
        μ {ω | ‖(X N).process T ω - hcomp.eq.point‖ > ε} ≤
          ENNReal.ofReal η := by
  classical
  let ρ : ℝ := ε / 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have htend := hcomp.converges sol hsol_init hsol_ode
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨Traw, hTraw⟩ := htend ρ hρ
  let T₀ : ℝ := max Traw 1
  have hT₀_pos : 0 < T₀ := lt_of_lt_of_le zero_lt_one (le_max_right Traw 1)
  refine ⟨T₀, hT₀_pos, ?_⟩
  intro T hT
  have hTraw_le : Traw ≤ T := (le_max_left Traw 1).trans hT
  have hT_pos : 0 < T := hT₀_pos.trans_le hT
  have hode : ‖sol T - hcomp.eq.point‖ < ρ := by
    simpa [dist_eq_norm] using hTraw T hTraw_le
  obtain ⟨N₀, hN₀⟩ := hKurtz T hT_pos ρ hρ η hη
  refine ⟨N₀, fun N hN => ?_⟩
  refine (MeasureTheory.measure_mono ?_).trans (hN₀ N hN)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hnot
  have hnorm_le : ‖(X N).process T ω - sol T‖ ≤ ρ := le_of_not_gt hnot
  have htri :
      ‖(X N).process T ω - hcomp.eq.point‖ ≤
        ‖(X N).process T ω - sol T‖ + ‖sol T - hcomp.eq.point‖ := by
    have hsplit :
        (X N).process T ω - hcomp.eq.point =
          ((X N).process T ω - sol T) + (sol T - hcomp.eq.point) := by
      ext i
      simp
    rw [hsplit]
    exact norm_add_le _ _
  have hmain : ‖(X N).process T ω - hcomp.eq.point‖ < ε := by
    calc
      ‖(X N).process T ω - hcomp.eq.point‖
          ≤ ‖(X N).process T ω - sol T‖ + ‖sol T - hcomp.eq.point‖ := htri
      _ < ρ + ρ := add_lt_add_of_le_of_lt hnorm_le hode
      _ = ε := by
          dsimp [ρ]
          ring
  exact not_lt_of_ge (le_of_lt hmain) hω

/-- Single-time state concentration from the usual filter-form fixed-time
Kurtz convergence. -/
theorem single_time_state_concentration_of_tendsto {n : ℕ}
    {tr : PLPPTransitions n} {marked : Finset (Fin n)} {ν : ℝ}
    (hcomp : PLPPIsolatedComputation tr marked ν)
    (sol : ℝ → Fin n → ℝ)
    (hsol_init : sol 0 ∈ hcomp.basin)
    (hsol_ode : ∀ t ≥ 0, HasDerivAt sol (tr.balanceField (sol t)) t)
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : (N : ℕ) → Kurtz.DensityProcess n tr.toRateSpec N μ)
    (hKurtz : ∀ T > 0, ∀ δ > 0,
      Filter.Tendsto
        (fun N : ℕ => μ {ω | ‖(X N).process T ω - sol T‖ > δ})
        Filter.atTop (nhds 0))
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T ≥ T₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
        μ {ω | ‖(X N).process T ω - hcomp.eq.point‖ > ε} ≤
          ENNReal.ofReal η :=
  single_time_state_concentration hcomp sol hsol_init hsol_ode μ X
    (fixedTimeKurtzConvergence_of_tendsto μ X sol hKurtz) ε η hε hη

/-- Corrected K3 readout concentration.

This keeps the useful conclusion formerly associated with the standard-order
API, but with the honest quantifier order supported by finite-horizon Kurtz:
`∃ T₀, ∀ T ≥ T₀, ∃ N₀, ∀ N ≥ N₀`. -/
theorem standard_limit_readout_concentration {n : ℕ}
    {tr : PLPPTransitions n} {marked : Finset (Fin n)} {ν : ℝ}
    (hcomp : PLPPIsolatedComputation tr marked ν)
    (sol : ℝ → Fin n → ℝ)
    (hsol_init : sol 0 ∈ hcomp.basin)
    (hsol_ode : ∀ t ≥ 0, HasDerivAt sol (tr.balanceField (sol t)) t)
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : (N : ℕ) → Kurtz.DensityProcess n tr.toRateSpec N μ)
    (hKurtz : FixedTimeKurtzConvergence tr μ X sol)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T ≥ T₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
        μ {ω | |markedReadout marked ((X N).process T ω) - ν| > ε} ≤
          ENNReal.ofReal η :=
  stochastic_exchanged_limit_isolated_to_target hcomp sol hsol_init hsol_ode μ X
    hKurtz ε η hε hη

/-- End-to-end isolated readout concentration from a packaged uniform
`DensityProcessFamily`, without exposing `FixedTimeKurtzConvergence`, the
aggregated Gronwall-Markov `h_gm` hypothesis, or its lower-level uniform QV and
event-inclusion components.

The endpoint bad event is compared with the finite-horizon supremum bad event
internally, using the density path bound in each `DensityProcess` and
compact-time boundedness of the ODE trajectory. -/
theorem end_to_end_readout_concentration {n : ℕ}
    {tr : PLPPTransitions n} {marked : Finset (Fin n)} {ν : ℝ}
    (hcomp : PLPPIsolatedComputation tr marked ν)
    (sol : ℝ → Fin n → ℝ)
    (hsol_init : sol 0 ∈ hcomp.basin)
    (hsol_ode : ∀ t ≥ 0, HasDerivAt sol (tr.balanceField (sol t)) t)
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : Kurtz.DensityProcessFamily n tr.toRateSpec μ)
    (h_init : ∀ ε > 0,
      Filter.Tendsto
        (fun N => μ {ω | ‖(X.densityProcess N).init ω - sol 0‖ > ε})
        Filter.atTop (nhds 0))
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T ≥ T₀,
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        μ {ω | |markedReadout marked ((X.densityProcess N).process T ω) - ν| > ε} ≤
          ENNReal.ofReal η := by
  classical
  exact stochastic_exchanged_limit_isolated_to_target
    hcomp sol hsol_init hsol_ode μ X.densityProcess
    (densityProcess_gives_fixedTimeKurtz hcomp sol hsol_ode μ X
      h_init)
    ε η hε hη

end Ripple
