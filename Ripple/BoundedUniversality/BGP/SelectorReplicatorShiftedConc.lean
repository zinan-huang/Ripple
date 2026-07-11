import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledHaltGen
import Ripple.BoundedUniversality.BGP.SelectorReplicatorRecovery
import Ripple.BoundedUniversality.BGP.SelectorReplicatorStatic
import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledZ
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
# SelectorReplicatorShiftedConc

Shifted concentration pipeline for the mid-window anchor.

The standard settled construction uses `selectorMUWriteStartTime` as the
concentration anchor.  This file shifts the anchor to `selectorMUSelectStartTime`
(= WriteStart + 10⁻⁵ rad), where the winner lambda has recovered to `1/N`.

## Pipeline
1. `hqL` on `[selectStart, WriteRead]` — from recovery + barrier (input)
2. `loser_mass_small_on_settled_window` on `[selectStart → WriteHold → WriteRead]`
   — produces loser mass ≤ `epsLamSettled(1/N, gap, N, K_shifted, G, selectStart, WriteHold)`
3. `epsLamSettled_tendsto_zero_duhamel` — shifted ΔG = G(WriteHold) - G(selectStart) → ∞
4. Feed into `solMURepl_settled_hstart_gen` — get z-coordinate convergence
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance UniversalMachine Filter Set
open scoped BigOperators Topology

/-- Shifted loser-mass radius: `epsLamSettled` anchored at `selectStart` instead
of `WriteStart`.  The Kreset integral runs to `WriteHold` — this is the tight
bound that tends to zero.  For the loser mass bound on `[WriteHold, WriteRead]`,
the product `(R0 + Kreset) * exp(-gap*ΔG)` is monotone decreasing in the
evaluation point, so the WriteHold value upper-bounds the whole window. -/
def epsLamShiftedAt
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (gap R0 : ℝ) (j : ℕ) : ℝ :=
  epsLamSettled (V := UniversalLocalView)
    (1 / (Fintype.card UniversalLocalView : ℝ))
    gap R0
    (∫ s in (selectorMUSelectStartTime j)..(selectorMUWriteHoldTime j),
      Real.exp (gap * ((sol w).G s - (sol w).G (selectorMUSelectStartTime j))) *
        (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)))
    (sol w).G
    (selectorMUSelectStartTime j)
    (selectorMUWriteHoldTime j)

/-- Shifted loser-mass radius at the early z-write subwindow start. -/
def epsLamShiftedEarlyAt
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (gap R0 : ℝ) (j : ℕ) : ℝ :=
  epsLamSettled (V := UniversalLocalView)
    (1 / (Fintype.card UniversalLocalView : ℝ))
    gap R0
    (∫ s in (selectorMUSelectStartTime j)..(selectorMUEarlyWriteSubStart j),
      Real.exp (gap * ((sol w).G s - (sol w).G (selectorMUSelectStartTime j))) *
        (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)))
    (sol w).G
    (selectorMUSelectStartTime j)
    (selectorMUEarlyWriteSubStart j)

/-- Pointwise linear lower bound for the shifted gain interval
`[SelectStart, WriteHold]`. -/
theorem shifted_deltaG_linear_lower_bound
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (hg₀ : 0 < (g₀ : ℝ)) :
    let c : ℝ :=
      ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ) *
        Real.exp (bgpParams38.cα *
          (Real.pi / 6 + selectorMURecoveryDelta)) *
        (Real.pi / 3 - selectorMURecoveryDelta) *
        (2 * Real.pi * bgpParams38.cα)
    ∀ j : ℕ, c * (j : ℝ) ≤
      (sol w).G (selectorMUWriteHoldTime j) -
        (sol w).G (selectorMUSelectStartTime j) := by
  dsimp
  have hcα : 0 < bgpParams38.cα := by norm_num [bgpParams38]
  set a₀ : ℝ := Real.pi / 6 + selectorMURecoveryDelta with ha₀_def
  set ww : ℝ := Real.pi / 3 - selectorMURecoveryDelta with hww_def
  have hw_pos : 0 < ww := by
    rw [hww_def]
    simp [selectorMURecoveryDelta]
    nlinarith [Real.pi_gt_three]
  have ha₀_pos : 0 < a₀ := by
    rw [ha₀_def]
    simp [selectorMURecoveryDelta]
    positivity
  have hℓ_pos : 0 < (3 / 4 : ℝ) ^ Mcy := by positivity
  exact selector_replicator_gain_linear_growth
    (sol := sol w)
    (aw := fun j => selectorMUSelectStartTime j)
    (bw := fun j => selectorMUWriteHoldTime j)
    (hcα := hcα) (hℓ := hℓ_pos) (hg₀ := hg₀)
    (hw := hw_pos) (ha₀ := ha₀_pos.le)
    (ha := by intro j; simp [selectorMUSelectStartTime, selectorMUWriteStartTime, a₀]; linarith)
    (hbw := by
      intro j
      simp only [selectorMUSelectStartTime, selectorMUWriteHoldTime,
        selectorMUWriteStartTime, ww]
      linarith)
    (hab := fun j => le_of_lt (selectorMUSelectStart_lt_hold j))
    (hdom := by
      intro j t ht
      simp only [selectorSchedule, Set.mem_Ici]
      have : 0 ≤ selectorMUSelectStartTime j := by
        simp only [selectorMUSelectStartTime, selectorMUWriteStartTime]
        have := Real.pi_pos
        have := selectorMURecoveryDelta_pos
        have := Nat.cast_nonneg (α := ℝ) j
        nlinarith
      linarith [ht.1])
    (hgain := fun _ => rfl) (hcont := by fun_prop)
    (hchi := by
      intro j t ht
      have hsin : (1 : ℝ) / 2 ≤ Real.sin t := by
        refine sin_ge_half_of_gate_window j ?_
        refine ⟨?_, ht.2⟩
        calc 2 * Real.pi * ↑j + Real.pi / 6
            ≤ selectorMUSelectStartTime j := by
              simp only [selectorMUSelectStartTime, selectorMUWriteStartTime]
              linarith [selectorMURecoveryDelta_pos]
          _ ≤ t := ht.1
      exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4)
        (by linarith : (3 / 4 : ℝ) ≤ (1 + Real.sin t) / 2) Mcy)

/-- Exponential decay bound induced by the shifted linear gain lower bound. -/
theorem shifted_deltaG_exp_decay_le_linear
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) {gap : ℝ} (hg₀ : 0 < (g₀ : ℝ)) (hgap0 : 0 < gap) :
    let c : ℝ :=
      ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ) *
        Real.exp (bgpParams38.cα *
          (Real.pi / 6 + selectorMURecoveryDelta)) *
        (Real.pi / 3 - selectorMURecoveryDelta) *
        (2 * Real.pi * bgpParams38.cα)
    ∀ j : ℕ,
      Real.exp (-(gap *
        ((sol w).G (selectorMUWriteHoldTime j) -
          (sol w).G (selectorMUSelectStartTime j)))) ≤
        Real.exp (-(gap * c * (j : ℝ))) := by
  dsimp
  intro j
  have hlin := shifted_deltaG_linear_lower_bound sol w hg₀
  dsimp at hlin
  have hΔ := hlin j
  have hmul :
      gap *
          (((3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) *
              Real.exp (bgpParams38.cα *
                (Real.pi / 6 + selectorMURecoveryDelta)) *
              (Real.pi / 3 - selectorMURecoveryDelta) *
              (2 * Real.pi * bgpParams38.cα)) * (j : ℝ)) ≤
        gap * ((sol w).G (selectorMUWriteHoldTime j) -
          (sol w).G (selectorMUSelectStartTime j)) :=
    mul_le_mul_of_nonneg_left hΔ hgap0.le
  have hneg :
      -(gap *
        ((sol w).G (selectorMUWriteHoldTime j) -
          (sol w).G (selectorMUSelectStartTime j))) ≤
        -(gap *
          (((3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) *
              Real.exp (bgpParams38.cα *
                (Real.pi / 6 + selectorMURecoveryDelta)) *
              (Real.pi / 3 - selectorMURecoveryDelta) *
              (2 * Real.pi * bgpParams38.cα)) * (j : ℝ))) := by
    linarith
  calc
    Real.exp (-(gap *
        ((sol w).G (selectorMUWriteHoldTime j) -
          (sol w).G (selectorMUSelectStartTime j))))
        ≤ Real.exp (-(gap *
          (((3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) *
              Real.exp (bgpParams38.cα *
                (Real.pi / 6 + selectorMURecoveryDelta)) *
              (Real.pi / 3 - selectorMURecoveryDelta) *
              (2 * Real.pi * bgpParams38.cα)) * (j : ℝ)))) :=
          Real.exp_le_exp.mpr hneg
    _ = Real.exp (-(gap *
          ((3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) *
            Real.exp (bgpParams38.cα *
              (Real.pi / 6 + selectorMURecoveryDelta)) *
            (Real.pi / 3 - selectorMURecoveryDelta) *
            (2 * Real.pi * bgpParams38.cα)) * (j : ℝ))) := by ring_nf

/-- Pointwise linear lower bound for the shifted gain interval
`[SelectStart, EarlySubStart]`. -/
theorem shifted_early_deltaG_linear_lower_bound
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (hg₀ : 0 < (g₀ : ℝ)) :
    let c : ℝ :=
      ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ) *
        Real.exp (bgpParams38.cα *
          (Real.pi / 6 + selectorMURecoveryDelta)) *
        (Real.pi / 12 - selectorMURecoveryDelta) *
        (2 * Real.pi * bgpParams38.cα)
    ∀ j : ℕ, c * (j : ℝ) ≤
      (sol w).G (selectorMUEarlyWriteSubStart j) -
        (sol w).G (selectorMUSelectStartTime j) := by
  dsimp
  have hcα : 0 < bgpParams38.cα := by norm_num [bgpParams38]
  set a₀ : ℝ := Real.pi / 6 + selectorMURecoveryDelta with ha₀_def
  set ww : ℝ := Real.pi / 12 - selectorMURecoveryDelta with hww_def
  have hw_pos : 0 < ww := by
    rw [hww_def]
    simp [selectorMURecoveryDelta]
    nlinarith [Real.pi_gt_three]
  have ha₀_pos : 0 < a₀ := by
    rw [ha₀_def]
    simp [selectorMURecoveryDelta]
    positivity
  have hℓ_pos : 0 < (3 / 4 : ℝ) ^ Mcy := by positivity
  exact selector_replicator_gain_linear_growth
    (sol := sol w)
    (aw := fun j => selectorMUSelectStartTime j)
    (bw := fun j => selectorMUEarlyWriteSubStart j)
    (hcα := hcα) (hℓ := hℓ_pos) (hg₀ := hg₀)
    (hw := hw_pos) (ha₀ := ha₀_pos.le)
    (ha := by intro j; simp [selectorMUSelectStartTime, selectorMUWriteStartTime, a₀]; linarith)
    (hbw := by
      intro j
      simp only [selectorMUSelectStartTime, selectorMUEarlyWriteSubStart,
        selectorMUWriteStartTime, ww]
      linarith)
    (hab := fun j => by
      unfold selectorMUSelectStartTime selectorMUWriteStartTime
        selectorMUEarlyWriteSubStart
      simp [selectorMURecoveryDelta]
      nlinarith [Real.pi_gt_three])
    (hdom := by
      intro j t ht
      simp only [selectorSchedule, Set.mem_Ici]
      have : 0 ≤ selectorMUSelectStartTime j := by
        simp only [selectorMUSelectStartTime, selectorMUWriteStartTime]
        have := Real.pi_pos
        have := selectorMURecoveryDelta_pos
        have := Nat.cast_nonneg (α := ℝ) j
        nlinarith
      linarith [ht.1])
    (hgain := fun _ => rfl) (hcont := by fun_prop)
    (hchi := by
      intro j t ht
      have hsin : (1 : ℝ) / 2 ≤ Real.sin t := by
        refine sin_ge_half_of_gate_window j ?_
        refine ⟨?_, ?_⟩
        · calc 2 * Real.pi * ↑j + Real.pi / 6
              ≤ selectorMUSelectStartTime j := by
                simp only [selectorMUSelectStartTime, selectorMUWriteStartTime]
                linarith [selectorMURecoveryDelta_pos]
            _ ≤ t := ht.1
        · have hright : t ≤ selectorMUWriteHoldTime j := by
            exact le_trans ht.2 (selectorMUEarlySubStart_le_writeHold j)
          exact hright
      exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4)
        (by linarith : (3 / 4 : ℝ) ≤ (1 + Real.sin t) / 2) Mcy)

/-- Exponential decay bound induced by the shifted-early linear gain lower
bound. -/
theorem shifted_early_deltaG_exp_decay_le_linear
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) {gap : ℝ} (hg₀ : 0 < (g₀ : ℝ)) (hgap0 : 0 < gap) :
    let c : ℝ :=
      ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ) *
        Real.exp (bgpParams38.cα *
          (Real.pi / 6 + selectorMURecoveryDelta)) *
        (Real.pi / 12 - selectorMURecoveryDelta) *
        (2 * Real.pi * bgpParams38.cα)
    ∀ j : ℕ,
      Real.exp (-(gap *
        ((sol w).G (selectorMUEarlyWriteSubStart j) -
          (sol w).G (selectorMUSelectStartTime j)))) ≤
        Real.exp (-(gap * c * (j : ℝ))) := by
  dsimp
  intro j
  have hlin := shifted_early_deltaG_linear_lower_bound sol w hg₀
  dsimp at hlin
  have hΔ := hlin j
  have hmul :
      gap *
          (((3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) *
              Real.exp (bgpParams38.cα *
                (Real.pi / 6 + selectorMURecoveryDelta)) *
              (Real.pi / 12 - selectorMURecoveryDelta) *
              (2 * Real.pi * bgpParams38.cα)) * (j : ℝ)) ≤
        gap * ((sol w).G (selectorMUEarlyWriteSubStart j) -
          (sol w).G (selectorMUSelectStartTime j)) :=
    mul_le_mul_of_nonneg_left hΔ hgap0.le
  have hneg :
      -(gap *
        ((sol w).G (selectorMUEarlyWriteSubStart j) -
          (sol w).G (selectorMUSelectStartTime j))) ≤
        -(gap *
          (((3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) *
              Real.exp (bgpParams38.cα *
                (Real.pi / 6 + selectorMURecoveryDelta)) *
              (Real.pi / 12 - selectorMURecoveryDelta) *
              (2 * Real.pi * bgpParams38.cα)) * (j : ℝ))) := by
    linarith
  calc
    Real.exp (-(gap *
        ((sol w).G (selectorMUEarlyWriteSubStart j) -
          (sol w).G (selectorMUSelectStartTime j))))
        ≤ Real.exp (-(gap *
          (((3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) *
              Real.exp (bgpParams38.cα *
                (Real.pi / 6 + selectorMURecoveryDelta)) *
              (Real.pi / 12 - selectorMURecoveryDelta) *
              (2 * Real.pi * bgpParams38.cα)) * (j : ℝ)))) :=
          Real.exp_le_exp.mpr hneg
    _ = Real.exp (-(gap *
          ((3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) *
            Real.exp (bgpParams38.cα *
              (Real.pi / 6 + selectorMURecoveryDelta)) *
            (Real.pi / 12 - selectorMURecoveryDelta) *
            (2 * Real.pi * bgpParams38.cα)) * (j : ℝ))) := by ring_nf

/-- The shifted gain integral `G(WriteHold) - G(selectStart)` tends to ∞. -/
theorem shifted_deltaG_tendsto_atTop
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (hg₀ : 0 < (g₀ : ℝ)) :
    Tendsto
      (fun j : ℕ => (sol w).G (selectorMUWriteHoldTime j) -
        (sol w).G (selectorMUSelectStartTime j))
      atTop atTop := by
  have hcα : 0 < bgpParams38.cα := by norm_num [bgpParams38]
  have hpi := Real.pi_pos
  have hδ := selectorMURecoveryDelta_pos
  set a₀ : ℝ := Real.pi / 6 + selectorMURecoveryDelta with ha₀_def
  set ww : ℝ := Real.pi / 3 - selectorMURecoveryDelta with hww_def
  have hw_pos : 0 < ww := by
    rw [hww_def]; simp [selectorMURecoveryDelta]; nlinarith [Real.pi_gt_three]
  have ha₀_pos : 0 < a₀ := by rw [ha₀_def]; simp [selectorMURecoveryDelta]; positivity
  have hℓ_pos : 0 < (3 / 4 : ℝ) ^ Mcy := by positivity
  have hc_pos : 0 < (3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) * Real.exp (bgpParams38.cα * a₀) *
      ww * (2 * Real.pi * bgpParams38.cα) :=
    mul_pos (mul_pos (mul_pos (mul_pos hℓ_pos hg₀) (Real.exp_pos _)) hw_pos)
      (mul_pos (by positivity) hcα)
  refine selectorOneHotDeltaG_tendsto_atTop_of_linear hc_pos ?_
  intro j
  exact selector_replicator_gain_linear_growth
    (sol := sol w)
    (aw := fun j => selectorMUSelectStartTime j)
    (bw := fun j => selectorMUWriteHoldTime j)
    (hcα := hcα) (hℓ := hℓ_pos) (hg₀ := hg₀)
    (hw := hw_pos) (ha₀ := ha₀_pos.le)
    (ha := by intro j; simp [selectorMUSelectStartTime, selectorMUWriteStartTime, a₀]; linarith)
    (hbw := by
      intro j
      simp only [selectorMUSelectStartTime, selectorMUWriteHoldTime,
        selectorMUWriteStartTime, ww]
      linarith)
    (hab := fun j => le_of_lt (selectorMUSelectStart_lt_hold j))
    (hdom := by
      intro j t ht
      simp only [selectorSchedule, Set.mem_Ici]
      have : 0 ≤ selectorMUSelectStartTime j := by
        simp only [selectorMUSelectStartTime, selectorMUWriteStartTime]
        have := Real.pi_pos; have := selectorMURecoveryDelta_pos
        have := Nat.cast_nonneg (α := ℝ) j
        nlinarith
      linarith [ht.1])
    (hgain := fun _ => rfl) (hcont := by fun_prop)
    (hchi := by
      intro j t ht
      have hsin : (1 : ℝ) / 2 ≤ Real.sin t := by
        refine sin_ge_half_of_gate_window j ?_
        refine ⟨?_, ht.2⟩
        calc 2 * Real.pi * ↑j + Real.pi / 6
            ≤ selectorMUSelectStartTime j := by
              simp only [selectorMUSelectStartTime, selectorMUWriteStartTime]
              linarith [selectorMURecoveryDelta_pos]
          _ ≤ t := ht.1
      exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4)
        (by linarith : (3 / 4 : ℝ) ≤ (1 + Real.sin t) / 2) Mcy) j

/-- The shifted gain integral from `SelectStart` to the early z-write subwindow
start tends to ∞. -/
theorem shifted_early_deltaG_tendsto_atTop
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (hg₀ : 0 < (g₀ : ℝ)) :
    Tendsto
      (fun j : ℕ => (sol w).G (selectorMUEarlyWriteSubStart j) -
        (sol w).G (selectorMUSelectStartTime j))
      atTop atTop := by
  have hcα : 0 < bgpParams38.cα := by norm_num [bgpParams38]
  set a₀ : ℝ := Real.pi / 6 + selectorMURecoveryDelta with ha₀_def
  set ww : ℝ := Real.pi / 12 - selectorMURecoveryDelta with hww_def
  have hw_pos : 0 < ww := by
    rw [hww_def]
    simp [selectorMURecoveryDelta]
    nlinarith [Real.pi_gt_three]
  have ha₀_pos : 0 < a₀ := by
    rw [ha₀_def]
    simp [selectorMURecoveryDelta]
    positivity
  have hℓ_pos : 0 < (3 / 4 : ℝ) ^ Mcy := by positivity
  have hc_pos : 0 < (3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) *
      Real.exp (bgpParams38.cα * a₀) * ww * (2 * Real.pi * bgpParams38.cα) :=
    mul_pos (mul_pos (mul_pos (mul_pos hℓ_pos hg₀) (Real.exp_pos _)) hw_pos)
      (mul_pos (by positivity) hcα)
  refine selectorOneHotDeltaG_tendsto_atTop_of_linear hc_pos ?_
  intro j
  exact selector_replicator_gain_linear_growth
    (sol := sol w)
    (aw := fun j => selectorMUSelectStartTime j)
    (bw := fun j => selectorMUEarlyWriteSubStart j)
    (hcα := hcα) (hℓ := hℓ_pos) (hg₀ := hg₀)
    (hw := hw_pos) (ha₀ := ha₀_pos.le)
    (ha := by
      intro j
      simp [selectorMUSelectStartTime, selectorMUWriteStartTime, a₀]
      linarith)
    (hbw := by
      intro j
      simp only [selectorMUSelectStartTime, selectorMUWriteStartTime,
        selectorMUEarlyWriteSubStart, ww]
      linarith)
    (hab := by
      intro j
      unfold selectorMUSelectStartTime selectorMUWriteStartTime
        selectorMUEarlyWriteSubStart
      simp [selectorMURecoveryDelta]
      nlinarith [Real.pi_gt_three])
    (hdom := by
      intro j t ht
      simp only [selectorSchedule, Set.mem_Ici]
      have hsel0 : 0 ≤ selectorMUSelectStartTime j :=
        le_trans (selectorMUWriteStartTime_nonneg j)
          (selectorMUWriteStart_le_selectStart j)
      linarith [ht.1])
    (hgain := fun _ => rfl) (hcont := by fun_prop)
    (hchi := by
      intro j t ht
      have hsin : (1 : ℝ) / 2 ≤ Real.sin t := by
        refine sin_ge_half_of_gate_window j ?_
        refine ⟨?_, ?_⟩
        · calc 2 * Real.pi * ↑j + Real.pi / 6
              ≤ selectorMUSelectStartTime j := by
                simp [selectorMUSelectStartTime, selectorMUWriteStartTime]
                linarith [selectorMURecoveryDelta_pos]
            _ ≤ t := ht.1
        · exact le_trans ht.2 (selectorMUEarlySubStart_le_writeHold j)
      exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4)
        (by linarith : (3 / 4 : ℝ) ≤ (1 + Real.sin t) / 2) Mcy) j

/-- The shifted loser-mass radius tends to zero. -/
theorem epsLamShifted_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) {gap R0 : ℝ}
    (hg₀ : 0 < (g₀ : ℝ))
    (hgap0 : 0 < gap)
    (hR0_nonneg : 0 ≤ R0)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ)) :
    Tendsto (epsLamShiftedAt sol w gap R0) atTop (𝓝 0) := by
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hcα : 0 < bgpParams38.cα := by norm_num [bgpParams38]
  have hdeltaG := shifted_deltaG_tendsto_atTop sol w hg₀
  have hLmin0_pos := solMURepl_concLmin_floor
  -- Step 1: K_hold * exp(-gap * ΔG) → 0 via forward_reset_integral_mul_decay_le
  have hDuhamel_pre :
      Tendsto (fun j =>
        (∫ s in (selectorMUSelectStartTime j)..(selectorMUWriteHoldTime j),
          Real.exp (gap * ((sol w).G s - (sol w).G (selectorMUSelectStartTime j))) *
            (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))) *
        Real.exp (-(gap * ((sol w).G (selectorMUWriteHoldTime j) -
          (sol w).G (selectorMUSelectStartTime j))))) atTop (𝓝 0) := by
    have hstart_atTop :
        Tendsto (fun j : ℕ => selectorMUWriteStartTime j) atTop atTop := by
      have hlin := tendsto_natCast_atTop_atTop.const_mul_atTop
        (by positivity : (0 : ℝ) < 2 * Real.pi)
      simpa [selectorMUWriteStartTime, mul_assoc] using
        Filter.tendsto_atTop_add_const_right atTop (Real.pi / 6) hlin
    have hdecay :
        Tendsto (fun j : ℕ =>
          (1 / gap) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)))
          atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul
        (Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr
          (hstart_atTop.const_mul_atTop hcα)))
    refine squeeze_zero' ?_ ?_ hdecay
    · filter_upwards [] with j
      have hab := le_of_lt (selectorMUSelectStart_lt_hold j)
      have hC_nonneg : 0 ≤ (1 : ℝ) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) :=
        mul_nonneg zero_le_one (Real.exp_pos _).le
      exact (forward_reset_integral_mul_decay_le
        (G := (sol w).G)
        (cg := fun t => ((1 + Real.sin t) / 2) ^ Mcy * ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
        (reset := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
        hab hgap0 hC_nonneg
        (sol w).cont_G
        (fun t ht => (sol w).G_hasDeriv t (by
          simp only [selectorSchedule, Set.mem_Ici]
          have := selectorMUWriteStartTime_nonneg j
          have := selectorMUWriteStart_le_selectStart j
          linarith [ht.1]))
        (by fun_prop) (by fun_prop)
        (fun t ht => mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos t]) Mcy)
          hκ₀_nonneg)
        (fun t ht => by
          have := solMURepl_static_hratio_bound hκ₀_nonneg hg₀.le
            hscale
            0 j t ⟨le_trans (selectorMUWriteStart_le_selectStart j) ht.1, ht.2⟩
          simpa [mul_assoc] using this)).1
    · filter_upwards [] with j
      have hab := le_of_lt (selectorMUSelectStart_lt_hold j)
      have hC_nonneg : 0 ≤ (1 : ℝ) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) :=
        mul_nonneg zero_le_one (Real.exp_pos _).le
      have hbound := (forward_reset_integral_mul_decay_le
        (G := (sol w).G)
        (cg := fun t => ((1 + Real.sin t) / 2) ^ Mcy * ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
        (reset := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
        hab hgap0 hC_nonneg
        (sol w).cont_G
        (fun t ht => (sol w).G_hasDeriv t (by
          simp only [selectorSchedule, Set.mem_Ici]
          have := selectorMUWriteStartTime_nonneg j
          have := selectorMUWriteStart_le_selectStart j
          linarith [ht.1]))
        (by fun_prop) (by fun_prop)
        (fun t ht => mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos t]) Mcy)
          hκ₀_nonneg)
        (fun t ht => by
          have := solMURepl_static_hratio_bound hκ₀_nonneg hg₀.le
            hscale
            0 j t ⟨le_trans (selectorMUWriteStart_le_selectStart j) ht.1, ht.2⟩
          simpa [mul_assoc] using this)).2
      have hrw : 1 * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap =
          1 / gap * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) := by ring
      linarith [hbound, hrw]
  -- Step 2: Apply the generic duhamel convergence
  have hcore := epsLamSettled_tendsto_zero_duhamel (V := UniversalLocalView)
    (Lmin := fun _ => 1 / (Fintype.card UniversalLocalView : ℝ))
    (gap := fun _ => gap) (R0 := fun _ => R0)
    (Kreset := fun j => ∫ s in (selectorMUSelectStartTime j)..(selectorMUWriteHoldTime j),
      Real.exp (gap * ((sol w).G s - (sol w).G (selectorMUSelectStartTime j))) *
        (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)))
    (deltaG := fun j => (sol w).G (selectorMUWriteHoldTime j) -
      (sol w).G (selectorMUSelectStartTime j))
    hgap0
    (Eventually.of_forall (fun _ => le_refl _))
    hdeltaG
    hLmin0_pos
    (Eventually.of_forall (fun _ => le_refl _))
    (Eventually.of_forall (fun _ => hR0_nonneg))
    (Eventually.of_forall (fun _ => le_refl _))
    (by simpa only [neg_mul] using hDuhamel_pre)
  refine hcore.congr (fun j => ?_)
  simp only [epsLamShiftedAt, epsLamSettled, selectorSettledRatioEps, neg_mul]

/-- Pointwise shifted loser-mass radius bound obtained by exposing the
Duhamel cancellation used in `epsLamShifted_tendsto_zero`. -/
theorem epsLamShiftedAt_le_reset_decay_bound
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) {gap R0 : ℝ}
    (hg₀ : 0 < (g₀ : ℝ))
    (hgap0 : 0 < gap)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ)) :
    ∀ j : ℕ,
      epsLamShiftedAt sol w gap R0 j ≤
        ((Fintype.card UniversalLocalView : ℝ) - 1) *
          (R0 * Real.exp (-(gap *
              ((sol w).G (selectorMUWriteHoldTime j) -
                (sol w).G (selectorMUSelectStartTime j)))) +
            Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  intro j
  let a : ℝ := selectorMUSelectStartTime j
  let b : ℝ := selectorMUWriteHoldTime j
  let K : ℝ :=
    ∫ s in a..b,
      Real.exp (gap * ((sol w).G s - (sol w).G a)) *
        (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))
  let E : ℝ := Real.exp (-(gap * ((sol w).G b - (sol w).G a)))
  have hab : a ≤ b := le_of_lt (by simpa [a, b] using selectorMUSelectStart_lt_hold j)
  have hC_nonneg :
      0 ≤ (1 : ℝ) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) :=
    mul_nonneg zero_le_one (Real.exp_pos _).le
  have hK_decay :
      K * E ≤
        Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap := by
    have hbound := (forward_reset_integral_mul_decay_le
      (G := (sol w).G)
      (cg := fun t => ((1 + Real.sin t) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
      (reset := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
      hab hgap0 hC_nonneg
      (sol w).cont_G
      (fun t ht => (sol w).G_hasDeriv t (by
        simp only [selectorSchedule, Set.mem_Ici]
        have hstart0 := selectorMUWriteStartTime_nonneg j
        have hstart_select := selectorMUWriteStart_le_selectStart j
        dsimp [a] at ht
        linarith [hstart0, hstart_select, ht.1]))
      (by fun_prop) (by fun_prop)
      (fun t _ht =>
        mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos t]) Mcy)
          hκ₀_nonneg)
      (fun t ht => by
        have hratio := solMURepl_static_hratio_bound hκ₀_nonneg hg₀.le
          hscale 0 j t
          ⟨le_trans (selectorMUWriteStart_le_selectStart j)
              (by simpa [a] using ht.1),
            by simpa [b] using ht.2⟩
        simpa [mul_assoc] using hratio)).2
    simpa [K, E, a, b] using hbound
  have hcard_nonneg :
      0 ≤ (Fintype.card UniversalLocalView : ℝ) - 1 := by
    have hcard_pos_nat :
        0 < Fintype.card UniversalLocalView :=
      Fintype.card_pos_iff.mpr inferInstance
    have hcard_one : (1 : ℝ) ≤ Fintype.card UniversalLocalView := by
      exact_mod_cast hcard_pos_nat
    linarith
  have hcore :
      ((R0 + K) * E) ≤
        R0 * E +
          Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap := by
    calc
      (R0 + K) * E = R0 * E + K * E := by ring
      _ ≤ R0 * E +
          Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap :=
        by linarith [hK_decay]
  have heq :
      epsLamShiftedAt sol w gap R0 j =
        ((Fintype.card UniversalLocalView : ℝ) - 1) * ((R0 + K) * E) := by
    dsimp [epsLamShiftedAt, K, E, a, b]
    simpa using
      epsLamSettled_card_inv (V := UniversalLocalView)
        gap R0
        (∫ s in (selectorMUSelectStartTime j)..(selectorMUWriteHoldTime j),
          Real.exp (gap * ((sol w).G s -
            (sol w).G (selectorMUSelectStartTime j))) *
            (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)))
        (sol w).G
        (selectorMUSelectStartTime j)
        (selectorMUWriteHoldTime j)
  rw [heq]
  exact mul_le_mul_of_nonneg_left hcore hcard_nonneg

/-- The early shifted loser-mass radius tends to zero. -/
theorem epsLamShiftedEarly_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) {gap R0 : ℝ}
    (hg₀ : 0 < (g₀ : ℝ))
    (hgap0 : 0 < gap)
    (hR0_nonneg : 0 ≤ R0)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ)) :
    Tendsto (epsLamShiftedEarlyAt sol w gap R0) atTop (𝓝 0) := by
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hcα : 0 < bgpParams38.cα := by norm_num [bgpParams38]
  have hdeltaG := shifted_early_deltaG_tendsto_atTop sol w hg₀
  have hLmin0_pos := solMURepl_concLmin_floor
  have hselect_early : ∀ j,
      selectorMUSelectStartTime j ≤ selectorMUEarlyWriteSubStart j := by
    intro j
    unfold selectorMUSelectStartTime selectorMUWriteStartTime
      selectorMUEarlyWriteSubStart
    simp [selectorMURecoveryDelta]
    nlinarith [Real.pi_gt_three]
  have hDuhamel_pre :
      Tendsto (fun j =>
        (∫ s in (selectorMUSelectStartTime j)..(selectorMUEarlyWriteSubStart j),
          Real.exp (gap * ((sol w).G s - (sol w).G (selectorMUSelectStartTime j))) *
            (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))) *
        Real.exp (-(gap * ((sol w).G (selectorMUEarlyWriteSubStart j) -
          (sol w).G (selectorMUSelectStartTime j))))) atTop (𝓝 0) := by
    have hstart_atTop :
        Tendsto (fun j : ℕ => selectorMUWriteStartTime j) atTop atTop := by
      have hlin := tendsto_natCast_atTop_atTop.const_mul_atTop
        (by positivity : (0 : ℝ) < 2 * Real.pi)
      simpa [selectorMUWriteStartTime, mul_assoc] using
        Filter.tendsto_atTop_add_const_right atTop (Real.pi / 6) hlin
    have hdecay :
        Tendsto (fun j : ℕ =>
          (1 / gap) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)))
          atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul
        (Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr
          (hstart_atTop.const_mul_atTop hcα)))
    refine squeeze_zero' ?_ ?_ hdecay
    · filter_upwards [] with j
      have hab := hselect_early j
      have hC_nonneg :
          0 ≤ (1 : ℝ) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) :=
        mul_nonneg zero_le_one (Real.exp_pos _).le
      exact (forward_reset_integral_mul_decay_le
        (G := (sol w).G)
        (cg := fun t => ((1 + Real.sin t) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
        (reset := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
        hab hgap0 hC_nonneg
        (sol w).cont_G
        (fun t ht => (sol w).G_hasDeriv t (by
          simp only [selectorSchedule, Set.mem_Ici]
          have := selectorMUWriteStartTime_nonneg j
          have := selectorMUWriteStart_le_selectStart j
          linarith [ht.1]))
        (by fun_prop) (by fun_prop)
        (fun t _ht => mul_nonneg
          (pow_nonneg (by nlinarith [Real.neg_one_le_cos t]) Mcy)
          hκ₀_nonneg)
        (fun t ht => by
          have := solMURepl_static_hratio_bound hκ₀_nonneg hg₀.le
            hscale
            0 j t
            ⟨le_trans (selectorMUWriteStart_le_selectStart j) ht.1,
              le_trans ht.2 (selectorMUEarlySubStart_le_writeHold j)⟩
          simpa [mul_assoc] using this)).1
    · filter_upwards [] with j
      have hab := hselect_early j
      have hC_nonneg :
          0 ≤ (1 : ℝ) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) :=
        mul_nonneg zero_le_one (Real.exp_pos _).le
      have hbound := (forward_reset_integral_mul_decay_le
        (G := (sol w).G)
        (cg := fun t => ((1 + Real.sin t) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
        (reset := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
        hab hgap0 hC_nonneg
        (sol w).cont_G
        (fun t ht => (sol w).G_hasDeriv t (by
          simp only [selectorSchedule, Set.mem_Ici]
          have := selectorMUWriteStartTime_nonneg j
          have := selectorMUWriteStart_le_selectStart j
          linarith [ht.1]))
        (by fun_prop) (by fun_prop)
        (fun t _ht => mul_nonneg
          (pow_nonneg (by nlinarith [Real.neg_one_le_cos t]) Mcy)
          hκ₀_nonneg)
        (fun t ht => by
          have := solMURepl_static_hratio_bound hκ₀_nonneg hg₀.le
            hscale
            0 j t
            ⟨le_trans (selectorMUWriteStart_le_selectStart j) ht.1,
              le_trans ht.2 (selectorMUEarlySubStart_le_writeHold j)⟩
          simpa [mul_assoc] using this)).2
      have hrw : 1 * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap =
          1 / gap * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) := by ring
      linarith [hbound, hrw]
  have hcore := epsLamSettled_tendsto_zero_duhamel (V := UniversalLocalView)
    (Lmin := fun _ => 1 / (Fintype.card UniversalLocalView : ℝ))
    (gap := fun _ => gap) (R0 := fun _ => R0)
    (Kreset := fun j => ∫ s in (selectorMUSelectStartTime j)..(selectorMUEarlyWriteSubStart j),
      Real.exp (gap * ((sol w).G s - (sol w).G (selectorMUSelectStartTime j))) *
        (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)))
    (deltaG := fun j => (sol w).G (selectorMUEarlyWriteSubStart j) -
      (sol w).G (selectorMUSelectStartTime j))
    hgap0
    (Eventually.of_forall (fun _ => le_refl _))
    hdeltaG
    hLmin0_pos
    (Eventually.of_forall (fun _ => le_refl _))
    (Eventually.of_forall (fun _ => hR0_nonneg))
    (Eventually.of_forall (fun _ => le_refl _))
    (by simpa only [neg_mul] using hDuhamel_pre)
  refine hcore.congr (fun j => ?_)
  simp only [epsLamShiftedEarlyAt, epsLamSettled, selectorSettledRatioEps, neg_mul]

/-- Pointwise shifted-early loser-mass radius bound obtained by exposing the
Duhamel cancellation used in `epsLamShiftedEarly_tendsto_zero`. -/
theorem epsLamShiftedEarlyAt_le_reset_decay_bound
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) {gap R0 : ℝ}
    (hg₀ : 0 < (g₀ : ℝ))
    (hgap0 : 0 < gap)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ)) :
    ∀ j : ℕ,
      epsLamShiftedEarlyAt sol w gap R0 j ≤
        ((Fintype.card UniversalLocalView : ℝ) - 1) *
          (R0 * Real.exp (-(gap *
              ((sol w).G (selectorMUEarlyWriteSubStart j) -
                (sol w).G (selectorMUSelectStartTime j)))) +
            Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  intro j
  let a : ℝ := selectorMUSelectStartTime j
  let b : ℝ := selectorMUEarlyWriteSubStart j
  let K : ℝ :=
    ∫ s in a..b,
      Real.exp (gap * ((sol w).G s - (sol w).G a)) *
        (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))
  let E : ℝ := Real.exp (-(gap * ((sol w).G b - (sol w).G a)))
  have hab : a ≤ b := by
    dsimp [a, b]
    unfold selectorMUSelectStartTime selectorMUWriteStartTime
      selectorMUEarlyWriteSubStart
    simp [selectorMURecoveryDelta]
    nlinarith [Real.pi_gt_three]
  have hC_nonneg :
      0 ≤ (1 : ℝ) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) :=
    mul_nonneg zero_le_one (Real.exp_pos _).le
  have hK_decay :
      K * E ≤
        Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap := by
    have hbound := (forward_reset_integral_mul_decay_le
      (G := (sol w).G)
      (cg := fun t => ((1 + Real.sin t) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
      (reset := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
      hab hgap0 hC_nonneg
      (sol w).cont_G
      (fun t ht => (sol w).G_hasDeriv t (by
        simp only [selectorSchedule, Set.mem_Ici]
        have hstart0 := selectorMUWriteStartTime_nonneg j
        have hstart_select := selectorMUWriteStart_le_selectStart j
        dsimp [a] at ht
        linarith [hstart0, hstart_select, ht.1]))
      (by fun_prop) (by fun_prop)
      (fun t _ht =>
        mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos t]) Mcy)
          hκ₀_nonneg)
      (fun t ht => by
        have hratio := solMURepl_static_hratio_bound hκ₀_nonneg hg₀.le
          hscale 0 j t
          ⟨le_trans (selectorMUWriteStart_le_selectStart j)
              (by simpa [a] using ht.1),
            le_trans (by simpa [b] using ht.2)
              (selectorMUEarlySubStart_le_writeHold j)⟩
        simpa [mul_assoc] using hratio)).2
    simpa [K, E, a, b] using hbound
  have hcard_nonneg :
      0 ≤ (Fintype.card UniversalLocalView : ℝ) - 1 := by
    have hcard_pos_nat :
        0 < Fintype.card UniversalLocalView :=
      Fintype.card_pos_iff.mpr inferInstance
    have hcard_one : (1 : ℝ) ≤ Fintype.card UniversalLocalView := by
      exact_mod_cast hcard_pos_nat
    linarith
  have hcore :
      ((R0 + K) * E) ≤
        R0 * E +
          Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap := by
    calc
      (R0 + K) * E = R0 * E + K * E := by ring
      _ ≤ R0 * E +
          Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap :=
        by linarith [hK_decay]
  have heq :
      epsLamShiftedEarlyAt sol w gap R0 j =
        ((Fintype.card UniversalLocalView : ℝ) - 1) * ((R0 + K) * E) := by
    dsimp [epsLamShiftedEarlyAt, K, E, a, b]
    simpa using
      epsLamSettled_card_inv (V := UniversalLocalView)
        gap R0
        (∫ s in (selectorMUSelectStartTime j)..(selectorMUEarlyWriteSubStart j),
          Real.exp (gap * ((sol w).G s -
            (sol w).G (selectorMUSelectStartTime j))) *
            (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)))
        (sol w).G
        (selectorMUSelectStartTime j)
        (selectorMUEarlyWriteSubStart j)
  rw [heq]
  exact mul_le_mul_of_nonneg_left hcore hcard_nonneg

/-- The tail Duhamel residual on `[WriteHold, WriteRead]` from the
reset/gate ratio bound.  This is the additional additive term beyond
`epsLamShiftedAt` that arises because the reset source produces new
loser mass on the tail interval. -/
def epsLamShiftedTailAt
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (gap : ℝ) (j : ℕ) : ℝ :=
  ((Fintype.card UniversalLocalView : ℝ) - 1) *
    (Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap)

/-- Combined shifted loser-mass bound = concentration at WriteHold + tail residual. -/
def epsLamShiftedFullAt
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (gap R0 : ℝ) (j : ℕ) : ℝ :=
  epsLamShiftedAt sol w gap R0 j + epsLamShiftedTailAt (Mcy := Mcy) (κ₀ := κ₀) (g₀ := g₀) gap j

/-- Pointwise bound for the combined shifted loser-mass radius. -/
theorem epsLamShiftedFullAt_le_reset_decay_bound
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) {gap R0 : ℝ}
    (hg₀ : 0 < (g₀ : ℝ))
    (hgap0 : 0 < gap)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ)) :
    ∀ j : ℕ,
      epsLamShiftedFullAt sol w gap R0 j ≤
        ((Fintype.card UniversalLocalView : ℝ) - 1) *
          (R0 * Real.exp (-(gap *
              ((sol w).G (selectorMUWriteHoldTime j) -
                (sol w).G (selectorMUSelectStartTime j)))) +
            Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap) +
        ((Fintype.card UniversalLocalView : ℝ) - 1) *
          (Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap) := by
  intro j
  have hmain :=
    epsLamShiftedAt_le_reset_decay_bound
      (R0 := R0)
      sol w hg₀ hgap0 hκ₀_nonneg hscale j
  unfold epsLamShiftedFullAt epsLamShiftedTailAt
  exact add_le_add hmain le_rfl

/-- Pointwise shifted loser-mass bound with the gain term replaced by the
linear-in-cycle exponential decay supplied by the write-window gain lower
bound. -/
theorem epsLamShiftedFullAt_le_linear_decay_bound
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) {gap R0 : ℝ}
    (hg₀ : 0 < (g₀ : ℝ))
    (hgap0 : 0 < gap)
    (hR0_nonneg : 0 ≤ R0)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ)) :
    let c : ℝ :=
      ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ) *
        Real.exp (bgpParams38.cα *
          (Real.pi / 6 + selectorMURecoveryDelta)) *
        (Real.pi / 3 - selectorMURecoveryDelta) *
        (2 * Real.pi * bgpParams38.cα)
    ∀ j : ℕ,
      epsLamShiftedFullAt sol w gap R0 j ≤
        ((Fintype.card UniversalLocalView : ℝ) - 1) *
          (R0 * Real.exp (-(gap * c) * (j : ℝ)) +
            Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap) +
        ((Fintype.card UniversalLocalView : ℝ) - 1) *
          (Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap) := by
  dsimp
  intro j
  have hreset :=
    epsLamShiftedFullAt_le_reset_decay_bound
      (sol := sol) (w := w) (gap := gap) (R0 := R0)
      hg₀ hgap0 hκ₀_nonneg hscale j
  have hdecay := shifted_deltaG_exp_decay_le_linear
      (sol := sol) (w := w) (gap := gap) hg₀ hgap0
  dsimp at hdecay
  have hRdecay :
      R0 * Real.exp (-(gap *
        ((sol w).G (selectorMUWriteHoldTime j) -
          (sol w).G (selectorMUSelectStartTime j)))) ≤
      R0 * Real.exp (-(gap *
        ((3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) *
          Real.exp (bgpParams38.cα *
            (Real.pi / 6 + selectorMURecoveryDelta)) *
          (Real.pi / 3 - selectorMURecoveryDelta) *
          (2 * Real.pi * bgpParams38.cα)) * (j : ℝ))) :=
    mul_le_mul_of_nonneg_left (hdecay j) hR0_nonneg
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hcard_nonneg :
      0 ≤ (Fintype.card UniversalLocalView : ℝ) - 1 := by
    have hcard_pos_nat :
        0 < Fintype.card UniversalLocalView :=
      Fintype.card_pos_iff.mpr inferInstance
    have hcard_one : (1 : ℝ) ≤ Fintype.card UniversalLocalView := by
      exact_mod_cast hcard_pos_nat
    linarith
  have hinner :
      R0 * Real.exp (-(gap *
          ((sol w).G (selectorMUWriteHoldTime j) -
            (sol w).G (selectorMUSelectStartTime j)))) +
        Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap ≤
      R0 * Real.exp (-(gap *
          ((3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) *
            Real.exp (bgpParams38.cα *
              (Real.pi / 6 + selectorMURecoveryDelta)) *
            (Real.pi / 3 - selectorMURecoveryDelta) *
            (2 * Real.pi * bgpParams38.cα)) * (j : ℝ))) +
        Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap := by
    linarith
  have hmain :
      ((Fintype.card UniversalLocalView : ℝ) - 1) *
        (R0 * Real.exp (-(gap *
            ((sol w).G (selectorMUWriteHoldTime j) -
              (sol w).G (selectorMUSelectStartTime j)))) +
          Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap) ≤
      ((Fintype.card UniversalLocalView : ℝ) - 1) *
        (R0 * Real.exp (-(gap *
            ((3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) *
              Real.exp (bgpParams38.cα *
                (Real.pi / 6 + selectorMURecoveryDelta)) *
              (Real.pi / 3 - selectorMURecoveryDelta) *
              (2 * Real.pi * bgpParams38.cα)) * (j : ℝ))) +
          Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap) :=
    mul_le_mul_of_nonneg_left hinner hcard_nonneg
  refine le_trans hreset ?_
  simpa [mul_assoc] using
    add_le_add_right hmain
      (((Fintype.card UniversalLocalView : ℝ) - 1) *
        (Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap))

/-- Combined early shifted loser-mass bound at `EarlySubStart` plus tail
residual. -/
def epsLamShiftedEarlyFullAt
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (gap R0 : ℝ) (j : ℕ) : ℝ :=
  epsLamShiftedEarlyAt sol w gap R0 j +
    epsLamShiftedTailAt (Mcy := Mcy) (κ₀ := κ₀) (g₀ := g₀) gap j

/-- Pointwise bound for the combined early shifted loser-mass radius. -/
theorem epsLamShiftedEarlyFullAt_le_reset_decay_bound
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) {gap R0 : ℝ}
    (hg₀ : 0 < (g₀ : ℝ))
    (hgap0 : 0 < gap)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ)) :
    ∀ j : ℕ,
      epsLamShiftedEarlyFullAt sol w gap R0 j ≤
        ((Fintype.card UniversalLocalView : ℝ) - 1) *
          (R0 * Real.exp (-(gap *
              ((sol w).G (selectorMUEarlyWriteSubStart j) -
                (sol w).G (selectorMUSelectStartTime j)))) +
            Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap) +
        ((Fintype.card UniversalLocalView : ℝ) - 1) *
          (Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap) := by
  intro j
  have hearly :=
    epsLamShiftedEarlyAt_le_reset_decay_bound
      (R0 := R0)
      sol w hg₀ hgap0 hκ₀_nonneg hscale j
  unfold epsLamShiftedEarlyFullAt epsLamShiftedTailAt
  exact add_le_add hearly le_rfl

/-- Pointwise early shifted loser-mass bound with the gain term replaced by the
linear-in-cycle exponential decay supplied by the early gain lower bound. -/
theorem epsLamShiftedEarlyFullAt_le_linear_decay_bound
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) {gap R0 : ℝ}
    (hg₀ : 0 < (g₀ : ℝ))
    (hgap0 : 0 < gap)
    (hR0_nonneg : 0 ≤ R0)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ)) :
    let c : ℝ :=
      ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ) *
        Real.exp (bgpParams38.cα *
          (Real.pi / 6 + selectorMURecoveryDelta)) *
        (Real.pi / 12 - selectorMURecoveryDelta) *
        (2 * Real.pi * bgpParams38.cα)
    ∀ j : ℕ,
      epsLamShiftedEarlyFullAt sol w gap R0 j ≤
        ((Fintype.card UniversalLocalView : ℝ) - 1) *
          (R0 * Real.exp (-(gap * c) * (j : ℝ)) +
            Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap) +
        ((Fintype.card UniversalLocalView : ℝ) - 1) *
          (Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap) := by
  dsimp
  intro j
  have hreset :=
    epsLamShiftedEarlyFullAt_le_reset_decay_bound
      (sol := sol) (w := w) (gap := gap) (R0 := R0)
      hg₀ hgap0 hκ₀_nonneg hscale j
  have hdecay := shifted_early_deltaG_exp_decay_le_linear
      (sol := sol) (w := w) (gap := gap) hg₀ hgap0
  dsimp at hdecay
  have hRdecay :
      R0 * Real.exp (-(gap *
        ((sol w).G (selectorMUEarlyWriteSubStart j) -
          (sol w).G (selectorMUSelectStartTime j)))) ≤
      R0 * Real.exp (-(gap *
        ((3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) *
          Real.exp (bgpParams38.cα *
            (Real.pi / 6 + selectorMURecoveryDelta)) *
          (Real.pi / 12 - selectorMURecoveryDelta) *
          (2 * Real.pi * bgpParams38.cα)) * (j : ℝ))) :=
    mul_le_mul_of_nonneg_left (hdecay j) hR0_nonneg
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hcard_nonneg :
      0 ≤ (Fintype.card UniversalLocalView : ℝ) - 1 := by
    have hcard_pos_nat :
        0 < Fintype.card UniversalLocalView :=
      Fintype.card_pos_iff.mpr inferInstance
    have hcard_one : (1 : ℝ) ≤ Fintype.card UniversalLocalView := by
      exact_mod_cast hcard_pos_nat
    linarith
  have hinner :
      R0 * Real.exp (-(gap *
          ((sol w).G (selectorMUEarlyWriteSubStart j) -
            (sol w).G (selectorMUSelectStartTime j)))) +
        Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap ≤
      R0 * Real.exp (-(gap *
          ((3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) *
            Real.exp (bgpParams38.cα *
              (Real.pi / 6 + selectorMURecoveryDelta)) *
            (Real.pi / 12 - selectorMURecoveryDelta) *
            (2 * Real.pi * bgpParams38.cα)) * (j : ℝ))) +
        Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap := by
    linarith
  have hmain :
      ((Fintype.card UniversalLocalView : ℝ) - 1) *
        (R0 * Real.exp (-(gap *
            ((sol w).G (selectorMUEarlyWriteSubStart j) -
              (sol w).G (selectorMUSelectStartTime j)))) +
          Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap) ≤
      ((Fintype.card UniversalLocalView : ℝ) - 1) *
        (R0 * Real.exp (-(gap *
            ((3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) *
              Real.exp (bgpParams38.cα *
                (Real.pi / 6 + selectorMURecoveryDelta)) *
              (Real.pi / 12 - selectorMURecoveryDelta) *
              (2 * Real.pi * bgpParams38.cα)) * (j : ℝ))) +
          Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap) :=
    mul_le_mul_of_nonneg_left hinner hcard_nonneg
  refine le_trans hreset ?_
  simpa [mul_assoc] using
    add_le_add_right hmain
      (((Fintype.card UniversalLocalView : ℝ) - 1) *
        (Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap))

/-- The tail residual tends to zero. -/
theorem epsLamShiftedTail_tendsto_zero
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {gap : ℝ} (hgap0 : 0 < gap) :
    Tendsto (epsLamShiftedTailAt (Mcy := Mcy) (κ₀ := κ₀) (g₀ := g₀) gap) atTop (𝓝 0) := by
  have hcα : 0 < bgpParams38.cα := by norm_num [bgpParams38]
  have hstart_atTop :
      Tendsto (fun j : ℕ => selectorMUWriteStartTime j) atTop atTop := by
    have hlin := tendsto_natCast_atTop_atTop.const_mul_atTop
      (by positivity : (0 : ℝ) < 2 * Real.pi)
    simpa [selectorMUWriteStartTime, mul_assoc] using
      Filter.tendsto_atTop_add_const_right atTop (Real.pi / 6) hlin
  unfold epsLamShiftedTailAt
  have hdecay :
      Tendsto (fun j : ℕ =>
        Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) / gap)
        atTop (𝓝 0) := by
    rw [show (0 : ℝ) = 0 / gap from (zero_div gap).symm]
    exact Filter.Tendsto.div_const
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr
        (hstart_atTop.const_mul_atTop hcα))) gap
  simpa using tendsto_const_nhds.mul hdecay

/-- The combined shifted bound tends to zero. -/
theorem epsLamShiftedFull_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) {gap R0 : ℝ}
    (hg₀ : 0 < (g₀ : ℝ))
    (hgap0 : 0 < gap)
    (hR0_nonneg : 0 ≤ R0)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ)) :
    Tendsto (epsLamShiftedFullAt sol w gap R0) atTop (𝓝 0) := by
  unfold epsLamShiftedFullAt
  simpa [add_zero] using (epsLamShifted_tendsto_zero sol w hg₀ hgap0 hR0_nonneg hκ₀_nonneg hscale).add
    (epsLamShiftedTail_tendsto_zero hgap0)

/-- The combined early shifted bound tends to zero. -/
theorem epsLamShiftedEarlyFull_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) {gap R0 : ℝ}
    (hg₀ : 0 < (g₀ : ℝ))
    (hgap0 : 0 < gap)
    (hR0_nonneg : 0 ≤ R0)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ)) :
    Tendsto (epsLamShiftedEarlyFullAt sol w gap R0) atTop (𝓝 0) := by
  unfold epsLamShiftedEarlyFullAt
  simpa [add_zero] using
    (epsLamShiftedEarly_tendsto_zero sol w hg₀ hgap0 hR0_nonneg hκ₀_nonneg hscale).add
      (epsLamShiftedTail_tendsto_zero hgap0)

/-- Nonnegativity of the combined early shifted bound. -/
theorem epsLamShiftedEarlyFullAt_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) {gap R0 : ℝ}
    (hgap0 : 0 < gap)
    (hR0_nonneg : 0 ≤ R0)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ)) :
    ∀ j, 0 ≤ epsLamShiftedEarlyFullAt sol w gap R0 j := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  intro j
  unfold epsLamShiftedEarlyFullAt
  refine add_nonneg ?_ ?_
  · unfold epsLamShiftedEarlyAt epsLamSettled selectorSettledRatioEps
      selectorSettledRatioCoeff
    refine mul_nonneg ?_ ?_
    · have hcard_pos_nat :
          0 < Fintype.card UniversalLocalView :=
        Fintype.card_pos_iff.mpr inferInstance
      have hcard_one : (1 : ℝ) ≤ Fintype.card UniversalLocalView := by
        exact_mod_cast hcard_pos_nat
      linarith
    · refine mul_nonneg ?_ (Real.exp_pos _).le
      refine add_nonneg hR0_nonneg ?_
      refine div_nonneg ?_ ?_
      · exact intervalIntegral.integral_nonneg_of_forall
          (by
            unfold selectorMUSelectStartTime selectorMUWriteStartTime
              selectorMUEarlyWriteSubStart
            simp [selectorMURecoveryDelta]
            nlinarith [Real.pi_gt_three])
          (fun s =>
            mul_nonneg (Real.exp_pos _).le
              (mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) _)
                hκ₀_nonneg))
      · positivity
  · unfold epsLamShiftedTailAt
    refine mul_nonneg ?_ ?_
    · have hcard_pos_nat :
          0 < Fintype.card UniversalLocalView :=
        Fintype.card_pos_iff.mpr inferInstance
      have hcard_one : (1 : ℝ) ≤ Fintype.card UniversalLocalView := by
        exact_mod_cast hcard_pos_nat
      linarith
    · exact div_nonneg (Real.exp_pos _).le hgap0.le

/-- Loser mass bound on `[EarlySubStart, WriteHold]` from shifted
concentration.  This is the prefix analogue of
`hloser_of_shifted_concentration`; it uses the shorter positive gain interval
from `SelectStart` to `EarlySubStart`. -/
theorem hloser_of_shifted_concentration_from_early
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → UConf} (w : ℕ) (j : ℕ)
    {gap R0 : ℝ}
    (hgap0 : 0 < gap)
    (hR0_nonneg : 0 ≤ R0)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hdom : ∀ t ∈ Icc (selectorMUSelectStartTime j) (selectorMUWriteHoldTime j),
      t ∈ selectorSchedule.domain)
    (hqL : ∀ t ∈ Icc (selectorMUSelectStartTime j) (selectorMUWriteHoldTime j),
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (cfg j)) t)
    (hlam_nonneg : ∀ v : UniversalLocalView,
      ∀ t ∈ Icc (selectorMUSelectStartTime j) (selectorMUWriteHoldTime j),
        0 ≤ (sol w).lam v t)
    (hsum : ∀ t ∈ Icc (selectorMUSelectStartTime j) (selectorMUWriteHoldTime j),
      (∑ v : UniversalLocalView, (sol w).lam v t) = 1)
    (hgap_cond : ∀ v : UniversalLocalView, v ≠ localViewU (cfg j) →
      ∀ t ∈ Ico (selectorMUSelectStartTime j) (selectorMUWriteHoldTime j),
        universalPval eta heta v ((sol w).u t) -
          universalPval eta heta (localViewU (cfg j)) ((sol w).u t) ≤ -gap)
    (hRa : ∀ v : UniversalLocalView, v ≠ localViewU (cfg j) →
      (sol w).lam v (selectorMUSelectStartTime j) /
        (sol w).lam (localViewU (cfg j)) (selectorMUSelectStartTime j) ≤ R0) :
    ∀ t ∈ Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (cfg j))).sum (fun v => (sol w).lam v t) ≤
          epsLamShiftedEarlyFullAt sol w gap R0 j := by
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hg₀_nonneg : 0 ≤ (g₀ : ℝ) := by
    have h34 : 0 < (3 / 4 : ℝ) ^ Mcy := by positivity
    nlinarith [hscale, hκ₀_nonneg]
  set a := selectorMUSelectStartTime j
  set bH := selectorMUEarlyWriteSubStart j
  set bR := selectorMUWriteHoldTime j
  have hab : a ≤ bH := by
    dsimp [a, bH]
    unfold selectorMUSelectStartTime selectorMUWriteStartTime
      selectorMUEarlyWriteSubStart
    simp [selectorMURecoveryDelta]
    nlinarith [Real.pi_gt_three]
  have hLmin := solMURepl_concLmin_floor
  intro t ht
  have hat : a ≤ t := le_trans hab ht.1
  have htR : t ∈ Icc a bR := ⟨hat, ht.2⟩
  set Kt := ∫ s in a..t,
    Real.exp (gap * ((sol w).G s - (sol w).G a)) *
      (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) with hKt_def
  have hKt_nonneg : 0 ≤ Kt := by
    rw [hKt_def]
    exact intervalIntegral.integral_nonneg_of_forall hat (fun s =>
      mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) _)
          hκ₀_nonneg))
  have h1 := loser_mass_small_on_settled_window (sol w) (localViewU (cfg j))
    (selectStart := a) (writeStart := t) (readStart := t) (Kreset := Kt)
    hat (le_refl t)
    hLmin (le_of_lt hgap0) hR0_nonneg hKt_nonneg
    (fun s hs => hdom s ⟨hs.1, le_trans hs.2 ht.2⟩)
    (by fun_prop)
    (fun s hs => hqL s ⟨hs.1, le_trans hs.2 ht.2⟩)
    (fun v s hs => hlam_nonneg v s ⟨hs.1, le_trans hs.2 ht.2⟩)
    (fun s hs => hsum s ⟨hs.1, le_trans hs.2 ht.2⟩)
    (fun s _ =>
      mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) _) hκ₀_nonneg)
    (fun s _ =>
      mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_sin s]) _)
        (mul_nonneg hg₀_nonneg (Real.exp_pos _).le))
    (fun v hv s hs => hgap_cond v hv s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩)
    (fun v hv => hRa v hv)
    (fun s hs => by have := le_antisymm hs.2 hs.1; subst this; exact le_refl _)
    (fun s hs => by have := le_antisymm hs.2 hs.1; subst this; exact le_refl _)
    t ⟨le_refl _, le_refl _⟩
  exact le_trans h1 (by
    rw [epsLamSettled_card_inv]
    unfold epsLamShiftedEarlyFullAt epsLamShiftedEarlyAt epsLamShiftedTailAt
    rw [epsLamSettled_card_inv]
    rw [← mul_add]
    have hcard_sub_one_nonneg :
        0 ≤ (Fintype.card UniversalLocalView : ℝ) - 1 := by
      have hcard_pos_nat :
          0 < Fintype.card UniversalLocalView :=
        Fintype.card_pos_iff.mpr inferInstance
      have hcard_one : (1 : ℝ) ≤ Fintype.card UniversalLocalView := by
        exact_mod_cast hcard_pos_nat
      linarith
    have hG_mono : (sol w).G bH ≤ (sol w).G t := by
      have hacc := selector_replicator_gain_accumulation (sol w) ht.1
        (fun _ => (0 : ℝ))
        (fun s hs => hdom s ⟨le_trans hab hs.1, le_trans hs.2 ht.2⟩)
        (by fun_prop) continuous_const
        (fun s _hs =>
          mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_sin s]) _)
            (mul_nonneg hg₀_nonneg (Real.exp_pos _).le))
      have hdiff : 0 ≤ (sol w).G t - (sol w).G bH := by
        simpa using hacc
      linarith
    have hsplit := hold_tail_split_decay_le
      (a := a) (bH := bH) (t := t) (gap := gap)
      (C := (1 : ℝ) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)))
      (R0 := R0) (G := (sol w).G)
      (cg := fun s =>
        ((1 + Real.sin s) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s)))
      (reset := fun s => ((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))
      hab ht.1 hgap0
      (mul_nonneg zero_le_one (Real.exp_pos _).le)
      hR0_nonneg
      (sol w).cont_G
      (fun s hs => (sol w).G_hasDeriv s
        (hdom s ⟨hs.1, le_trans hs.2 ht.2⟩))
      (by fun_prop) (by fun_prop)
      (fun s _hs =>
        mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) _)
          hκ₀_nonneg)
      (fun s _hs =>
        mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_sin s]) _)
          (mul_nonneg hg₀_nonneg (Real.exp_pos _).le))
      (fun s hs => by
        have := solMURepl_static_hratio_bound_full hκ₀_nonneg hg₀_nonneg
          hscale 0 j s
          ⟨le_trans (selectorMUWriteStart_le_selectStart j)
              (le_trans hab hs.1),
            le_trans (le_trans hs.2 ht.2) (selectorMUWriteHold_le_read j)⟩
        simpa [mul_assoc] using this)
      hG_mono
    exact mul_le_mul_of_nonneg_left (by
      simpa [Kt, hKt_def, one_mul] using hsplit) hcard_sub_one_nonneg)

/-- Pointwise Duhamel loser-mass bound on the active early-write suffix.

This is the source-aware version of
`hloser_of_shifted_concentration_from_early`: it keeps the Duhamel radius at the
current time `t` instead of replacing it by the coarser endpoint/tail envelope
`epsLamShiftedEarlyFullAt`.  It is the right surface for weighted active-late
Hoff estimates, where the reset-source convolution must remain inside the
integral. -/
theorem hloser_of_shifted_concentration_from_early_duhamel
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → UConf} (w : ℕ) (j : ℕ)
    {gap R0 : ℝ}
    (hgap0 : 0 < gap)
    (hR0_nonneg : 0 ≤ R0)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hdom : ∀ t ∈ Icc (selectorMUSelectStartTime j) (selectorMUWriteHoldTime j),
      t ∈ selectorSchedule.domain)
    (hqL : ∀ t ∈ Icc (selectorMUSelectStartTime j) (selectorMUWriteHoldTime j),
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (cfg j)) t)
    (hlam_nonneg : ∀ v : UniversalLocalView,
      ∀ t ∈ Icc (selectorMUSelectStartTime j) (selectorMUWriteHoldTime j),
        0 ≤ (sol w).lam v t)
    (hsum : ∀ t ∈ Icc (selectorMUSelectStartTime j) (selectorMUWriteHoldTime j),
      (∑ v : UniversalLocalView, (sol w).lam v t) = 1)
    (hgap_cond : ∀ v : UniversalLocalView, v ≠ localViewU (cfg j) →
      ∀ t ∈ Ico (selectorMUSelectStartTime j) (selectorMUWriteHoldTime j),
        universalPval eta heta v ((sol w).u t) -
          universalPval eta heta (localViewU (cfg j)) ((sol w).u t) ≤ -gap)
    (hRa : ∀ v : UniversalLocalView, v ≠ localViewU (cfg j) →
      (sol w).lam v (selectorMUSelectStartTime j) /
        (sol w).lam (localViewU (cfg j)) (selectorMUSelectStartTime j) ≤ R0) :
    ∀ t ∈ Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (cfg j))).sum (fun v => (sol w).lam v t) ≤
          epsLamSettled (V := UniversalLocalView)
            (1 / (Fintype.card UniversalLocalView : ℝ)) gap R0
            (∫ s in (selectorMUSelectStartTime j)..t,
              Real.exp (gap *
                ((sol w).G s - (sol w).G (selectorMUSelectStartTime j))) *
                (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)))
            (sol w).G (selectorMUSelectStartTime j) t := by
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hg₀_nonneg : 0 ≤ (g₀ : ℝ) := by
    have h34 : 0 < (3 / 4 : ℝ) ^ Mcy := by positivity
    nlinarith [hscale, hκ₀_nonneg]
  set a := selectorMUSelectStartTime j
  set bH := selectorMUEarlyWriteSubStart j
  set bR := selectorMUWriteHoldTime j
  have hab : a ≤ bH := by
    dsimp [a, bH]
    unfold selectorMUSelectStartTime selectorMUWriteStartTime
      selectorMUEarlyWriteSubStart
    simp [selectorMURecoveryDelta]
    nlinarith [Real.pi_gt_three]
  have hLmin := solMURepl_concLmin_floor
  intro t ht
  have hat : a ≤ t := le_trans hab ht.1
  set Kt := ∫ s in a..t,
    Real.exp (gap * ((sol w).G s - (sol w).G a)) *
      (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) with hKt_def
  have hKt_nonneg : 0 ≤ Kt := by
    rw [hKt_def]
    exact intervalIntegral.integral_nonneg_of_forall hat (fun s =>
      mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) _)
          hκ₀_nonneg))
  have h1 := loser_mass_small_on_settled_window (sol w) (localViewU (cfg j))
    (selectStart := a) (writeStart := t) (readStart := t) (Kreset := Kt)
    hat (le_refl t)
    hLmin (le_of_lt hgap0) hR0_nonneg hKt_nonneg
    (fun s hs => hdom s ⟨hs.1, le_trans hs.2 ht.2⟩)
    (by fun_prop)
    (fun s hs => hqL s ⟨hs.1, le_trans hs.2 ht.2⟩)
    (fun v s hs => hlam_nonneg v s ⟨hs.1, le_trans hs.2 ht.2⟩)
    (fun s hs => hsum s ⟨hs.1, le_trans hs.2 ht.2⟩)
    (fun s _ =>
      mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) _) hκ₀_nonneg)
    (fun s _ =>
      mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_sin s]) _)
        (mul_nonneg hg₀_nonneg (Real.exp_pos _).le))
    (fun v hv s hs => hgap_cond v hv s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩)
    (fun v hv => hRa v hv)
    (fun s hs => by have := le_antisymm hs.2 hs.1; subst this; exact le_refl _)
    (fun s hs => by have := le_antisymm hs.2 hs.1; subst this; exact le_refl _)
    t ⟨le_refl _, le_refl _⟩
  simpa [a, Kt, hKt_def] using h1

/-- Pointwise Duhamel loser-mass bound on the select-to-early prefix.

Unlike `hloser_of_shifted_concentration_from_early`, this does not replace the
time-dependent Duhamel radius by its endpoint value at
`selectorMUEarlyWriteSubStart`.  It is the correct pointwise surface for
weighted post-select integrals over `[SelectStart, EarlyWriteSubStart]`. -/
theorem hloser_of_shifted_concentration_prefix_duhamel
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → UConf} (w : ℕ) (j : ℕ)
    {gap R0 : ℝ}
    (hgap0 : 0 < gap)
    (hR0_nonneg : 0 ≤ R0)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hdom : ∀ t ∈ Icc (selectorMUSelectStartTime j)
        (selectorMUEarlyWriteSubStart j), t ∈ selectorSchedule.domain)
    (hqL : ∀ t ∈ Icc (selectorMUSelectStartTime j)
        (selectorMUEarlyWriteSubStart j),
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (cfg j)) t)
    (hlam_nonneg : ∀ v : UniversalLocalView,
      ∀ t ∈ Icc (selectorMUSelectStartTime j)
          (selectorMUEarlyWriteSubStart j),
        0 ≤ (sol w).lam v t)
    (hsum : ∀ t ∈ Icc (selectorMUSelectStartTime j)
        (selectorMUEarlyWriteSubStart j),
      (∑ v : UniversalLocalView, (sol w).lam v t) = 1)
    (hgap_cond : ∀ v : UniversalLocalView, v ≠ localViewU (cfg j) →
      ∀ t ∈ Ico (selectorMUSelectStartTime j)
          (selectorMUEarlyWriteSubStart j),
        universalPval eta heta v ((sol w).u t) -
          universalPval eta heta (localViewU (cfg j)) ((sol w).u t) ≤ -gap)
    (hRa : ∀ v : UniversalLocalView, v ≠ localViewU (cfg j) →
      (sol w).lam v (selectorMUSelectStartTime j) /
        (sol w).lam (localViewU (cfg j)) (selectorMUSelectStartTime j) ≤ R0) :
    ∀ t ∈ Icc (selectorMUSelectStartTime j) (selectorMUEarlyWriteSubStart j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (cfg j))).sum (fun v => (sol w).lam v t) ≤
          epsLamSettled (V := UniversalLocalView)
            (1 / (Fintype.card UniversalLocalView : ℝ)) gap R0
            (∫ s in (selectorMUSelectStartTime j)..t,
              Real.exp (gap *
                ((sol w).G s - (sol w).G (selectorMUSelectStartTime j))) *
                (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)))
            (sol w).G (selectorMUSelectStartTime j) t := by
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hg₀_nonneg : 0 ≤ (g₀ : ℝ) := by
    have h34 : 0 < (3 / 4 : ℝ) ^ Mcy := by positivity
    nlinarith [hscale, hκ₀_nonneg]
  exact
    loser_mass_small_on_prefix_pointwise
      (sol := sol w) (vstar := localViewU (cfg j))
      (a := selectorMUSelectStartTime j)
      (b := selectorMUEarlyWriteSubStart j)
      (Lmin := 1 / (Fintype.card UniversalLocalView : ℝ))
      (gap := gap) (R0 := R0)
      solMURepl_concLmin_floor
      (le_of_lt hgap0)
      hR0_nonneg
      hdom
      (by fun_prop)
      hqL
      hlam_nonneg
      hsum
      (fun s _hs =>
        mul_nonneg
          (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) _)
          hκ₀_nonneg)
      (fun s _hs =>
        mul_nonneg
          (pow_nonneg (by nlinarith [Real.neg_one_le_sin s]) _)
          (mul_nonneg hg₀_nonneg (Real.exp_pos _).le))
      hgap_cond
      hRa

/-- Loser mass bound on `[WriteHold, WriteRead]` from shifted concentration.

The bound uses `epsLamShiftedFullAt = epsLamShiftedAt + epsLamShiftedTailAt`:
- `epsLamShiftedAt` covers the concentration from `[selectStart, WriteHold]`
- `epsLamShiftedTailAt` covers the Duhamel tail on `[WriteHold, t]` -/
theorem hloser_of_shifted_concentration
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → UConf} (w : ℕ) (j : ℕ)
    {gap R0 : ℝ}
    (hgap0 : 0 < gap)
    (hR0_nonneg : 0 ≤ R0)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hdom : ∀ t ∈ Icc (selectorMUSelectStartTime j) (selectorMUWriteReadTime j),
      t ∈ selectorSchedule.domain)
    (hqL : ∀ t ∈ Icc (selectorMUSelectStartTime j) (selectorMUWriteReadTime j),
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (cfg j)) t)
    (hlam_nonneg : ∀ v : UniversalLocalView,
      ∀ t ∈ Icc (selectorMUSelectStartTime j) (selectorMUWriteReadTime j),
        0 ≤ (sol w).lam v t)
    (hsum : ∀ t ∈ Icc (selectorMUSelectStartTime j) (selectorMUWriteReadTime j),
      (∑ v : UniversalLocalView, (sol w).lam v t) = 1)
    (hgap_cond : ∀ v : UniversalLocalView, v ≠ localViewU (cfg j) →
      ∀ t ∈ Ico (selectorMUSelectStartTime j) (selectorMUWriteReadTime j),
        universalPval eta heta v ((sol w).u t) -
          universalPval eta heta (localViewU (cfg j)) ((sol w).u t) ≤ -gap)
    (hRa : ∀ v : UniversalLocalView, v ≠ localViewU (cfg j) →
      (sol w).lam v (selectorMUSelectStartTime j) /
        (sol w).lam (localViewU (cfg j)) (selectorMUSelectStartTime j) ≤ R0) :
    ∀ t ∈ Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (cfg j))).sum (fun v => (sol w).lam v t) ≤
          epsLamShiftedFullAt sol w gap R0 j := by
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hg₀_nonneg : 0 ≤ (g₀ : ℝ) := by
    have h34 : 0 < (3 / 4 : ℝ) ^ Mcy := by positivity
    nlinarith [hscale, hκ₀_nonneg]
  set a := selectorMUSelectStartTime j
  set bH := selectorMUWriteHoldTime j
  set bR := selectorMUWriteReadTime j
  have hab := le_of_lt (selectorMUSelectStart_lt_hold j) -- a ≤ bH
  have hLmin := solMURepl_concLmin_floor
  intro t ht -- t ∈ [bH, bR]
  have hat : a ≤ t := le_trans hab ht.1
  have htR : t ∈ Icc a bR := ⟨hat, ht.2⟩
  -- Step 1: pointwise ratio bound at t via loser_mass_small_on_settled_window [a, t, t]
  set Kt := ∫ s in a..t,
    Real.exp (gap * ((sol w).G s - (sol w).G a)) *
      (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) with hKt_def
  have hKt_nonneg : 0 ≤ Kt := by
    rw [hKt_def]
    exact intervalIntegral.integral_nonneg_of_forall hat (fun s =>
      mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) _) hκ₀_nonneg))
  have h1 := loser_mass_small_on_settled_window (sol w) (localViewU (cfg j))
    (selectStart := a) (writeStart := t) (readStart := t) (Kreset := Kt)
    hat (le_refl t)
    hLmin (le_of_lt hgap0) hR0_nonneg hKt_nonneg
    (fun s hs => hdom s ⟨hs.1, le_trans hs.2 ht.2⟩)
    (by fun_prop)
    (fun s hs => hqL s ⟨hs.1, le_trans hs.2 ht.2⟩)
    (fun v s hs => hlam_nonneg v s ⟨hs.1, le_trans hs.2 ht.2⟩)
    (fun s hs => hsum s ⟨hs.1, le_trans hs.2 ht.2⟩)
    (fun s _ =>
      mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) _) hκ₀_nonneg)
    (fun s _ =>
      mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_sin s]) _)
        (mul_nonneg hg₀_nonneg (Real.exp_pos _).le))
    (fun v hv s hs => hgap_cond v hv s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩)
    (fun v hv => hRa v hv)
    (fun s hs => by have := le_antisymm hs.2 hs.1; subst this; exact le_refl _)
    (fun s hs => by have := le_antisymm hs.2 hs.1; subst this; exact le_refl _)
    t ⟨le_refl _, le_refl _⟩
  -- h1 : loser_mass ≤ epsLamSettled (1/N) gap R0 Kt G a t
  -- Step 2: bound epsLamSettled ... Kt ... a t ≤ epsLamShiftedFullAt
  -- The proof reduces to showing the epsLamSettled value at t with Kt
  -- is ≤ the epsLamSettled value at WriteHold with K_hold + a tail residual.
  exact le_trans h1 (by
    rw [epsLamSettled_card_inv]
    unfold epsLamShiftedFullAt epsLamShiftedAt epsLamShiftedTailAt
    rw [epsLamSettled_card_inv]
    rw [← mul_add]
    have hcard_sub_one_nonneg :
        0 ≤ (Fintype.card UniversalLocalView : ℝ) - 1 := by
      have hcard_pos_nat :
          0 < Fintype.card UniversalLocalView :=
        Fintype.card_pos_iff.mpr inferInstance
      have hcard_one : (1 : ℝ) ≤ Fintype.card UniversalLocalView := by
        exact_mod_cast hcard_pos_nat
      linarith
    have hG_mono : (sol w).G bH ≤ (sol w).G t := by
      have hacc := selector_replicator_gain_accumulation (sol w) ht.1
        (fun _ => (0 : ℝ))
        (fun s hs => hdom s ⟨le_trans hab hs.1, le_trans hs.2 ht.2⟩)
        (by fun_prop) continuous_const
        (fun s _hs =>
          mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_sin s]) _)
            (mul_nonneg hg₀_nonneg (Real.exp_pos _).le))
      have hdiff : 0 ≤ (sol w).G t - (sol w).G bH := by
        simpa using hacc
      linarith
    have hsplit := hold_tail_split_decay_le
      (a := a) (bH := bH) (t := t) (gap := gap)
      (C := (1 : ℝ) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)))
      (R0 := R0) (G := (sol w).G)
      (cg := fun s =>
        ((1 + Real.sin s) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s)))
      (reset := fun s => ((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))
      hab ht.1 hgap0
      (mul_nonneg zero_le_one (Real.exp_pos _).le)
      hR0_nonneg
      (sol w).cont_G
      (fun s hs => (sol w).G_hasDeriv s
        (hdom s ⟨hs.1, le_trans hs.2 ht.2⟩))
      (by fun_prop) (by fun_prop)
      (fun s _hs =>
        mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) _)
          hκ₀_nonneg)
      (fun s _hs =>
        mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_sin s]) _)
          (mul_nonneg hg₀_nonneg (Real.exp_pos _).le))
      (fun s hs => by
        have := solMURepl_static_hratio_bound_full hκ₀_nonneg hg₀_nonneg
          hscale 0 j s
          ⟨le_trans (selectorMUWriteStart_le_selectStart j)
              (le_trans hab hs.1),
            le_trans hs.2 ht.2⟩
        simpa [mul_assoc] using this)
      hG_mono
    exact mul_le_mul_of_nonneg_left (by
      simpa [Kt, hKt_def, one_mul] using hsplit) hcard_sub_one_nonneg)

end Ripple.BoundedUniversality.BGP
