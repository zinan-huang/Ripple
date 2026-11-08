/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-7 three-band multiplicative-drift survival

The paper's Phase 7 drains the naturally available bands among `l,l+1,l+2`.
Each exact-band stage uses the two-orientation cancellation rate
`2 E7 / (n(n-1))`, spends one sixth of the inverse-square budget on drift,
and keeps its killed-window escape budget separate.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.DriftHorizon
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7BandDropSum
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7BandStages

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase7BandSurvival

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {L K : ℕ}

open Phase7BandDefs Phase7BandStages

/-- A uniform killed-kernel escape bound for every naturally available
exact-band stage. -/
structure Phase7BandEscapeBound
    (n : ℕ) (σ : Sign) (l E7 : ℕ) (η : ℝ≥0∞) : Prop where
  hesc :
    ∀ (j : Fin (L + 1)), l ≤ j.val → j.val < l + 3 →
      ∀ c, Phase7StageReady (L := L) (K := K) n σ l E7 j c →
        (NonuniformMajority L K).transitionKernel c
          {c' | ¬ Phase7StageReady (L := L) (K := K) n σ l E7 j c'} ≤ η

/-- One exact-band multiplicative-drift stage.  Its public precondition is the
ready gate itself; the automatic count bound `bandCountN ≤ card = n` is hidden
inside the constructor. -/
noncomputable def phase7BandStageSurvival
    {n : ℕ} (hn : 2 ≤ n)
    (σ : Sign) (l E7 : ℕ) (j : Fin (L + 1))
    (hjl : l ≤ j.val) (hjtop : j.val < l + 3)
    (hEpos : 1 ≤ E7) (hEtop : 2 * E7 ≤ n * (n - 1))
    (η : ℝ≥0∞)
    (hesc : Phase7BandEscapeBound (L := L) (K := K) n σ l E7 η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel := by
  let Inv : Config (AgentState L K) → Prop :=
    fun c => Phase7StageReady (L := L) (K := K) n σ l E7 j c
  let Φ : Config (AgentState L K) → ℕ :=
    fun c => bandCountN (L := L) (K := K) σ j c
  let r : ℝ≥0∞ :=
    1 - ENNReal.ofReal (((2 * E7 : ℕ) : ℝ) /
      ((n : ℝ) * ((n : ℝ) - 1)))
  let T : ℕ := DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6
  have hB0 : (0 : ℝ) < ((2 * E7 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 2 * E7 by omega)
  have hBtop : ((2 * E7 : ℕ) : ℝ) ≤
      (n : ℝ) * ((n : ℝ) - 1) := by
    calc
      ((2 * E7 : ℕ) : ℝ) ≤ ((n * (n - 1) : ℕ) : ℝ) := by
        exact_mod_cast hEtop
      _ = (n : ℝ) * ((n : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega)]
        norm_num
  have hr : r ≤ 1 := by
    dsimp [r]
    exact tsub_le_self
  have hdrift :
      ∀ c, Inv c →
        ∫⁻ c', (Φ c' : ℝ≥0∞) ∂((NonuniformMajority L K).transitionKernel c)
          ≤ r * (Φ c : ℝ≥0∞) := by
    simpa [Inv, Φ, r] using
      (Phase7BandDropSum.phase7_band_weighted_drift
        (L := L) (K := K) n σ l E7 j hn hjl hjtop)
  have hdrain :
      r ^ T * (n : ℝ≥0∞) ≤
        (DriftSurvival.driftBudgetNN 6 n : ℝ≥0∞) := by
    simpa [r, T] using
      (DriftSurvival.drift_pow_le_budget_sub
        (B := ((2 * E7 : ℕ) : ℝ)) (n := n) (Φmax := n) (D := 6)
        hn (by omega) (by norm_num) hB0 hBtop)
  let base : PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
    DriftSurvival.driftSurvivalPhase
      (NonuniformMajority L K).transitionKernel Inv Φ r hr hdrift
      η (hesc.hesc j hjl hjtop) T n (DriftSurvival.driftBudgetNN 6 n)
      escapeε hdrain (by simpa [T] using hescε)
  exact
    { Pre := Inv
      Post := fun c => Inv c ∧ Φ c = 0
      t := T
      ε := DriftSurvival.driftBudgetNN 6 n + escapeε
      convergence := by
        intro c hc
        have hΦ : Φ c ≤ n := by
          exact (bandCountN_le_card (L := L) (K := K) σ j c).trans_eq hc.honest.1
        exact base.convergence c ⟨hc, hΦ⟩ }

@[simp] theorem phase7BandStageSurvival_t
    {n : ℕ} (hn : 2 ≤ n)
    (σ : Sign) (l E7 : ℕ) (j : Fin (L + 1))
    (hjl : l ≤ j.val) (hjtop : j.val < l + 3)
    (hEpos : 1 ≤ E7) (hEtop : 2 * E7 ≤ n * (n - 1))
    (η : ℝ≥0∞)
    (hesc : Phase7BandEscapeBound (L := L) (K := K) n σ l E7 η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    (phase7BandStageSurvival (L := L) (K := K) hn σ l E7 j hjl hjtop
      hEpos hEtop η hesc escapeε hescε).t =
      DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 := rfl

@[simp] theorem phase7BandStageSurvival_epsilon
    {n : ℕ} (hn : 2 ≤ n)
    (σ : Sign) (l E7 : ℕ) (j : Fin (L + 1))
    (hjl : l ≤ j.val) (hjtop : j.val < l + 3)
    (hEpos : 1 ≤ E7) (hEtop : 2 * E7 ≤ n * (n - 1))
    (η : ℝ≥0∞)
    (hesc : Phase7BandEscapeBound (L := L) (K := K) n σ l E7 η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    (phase7BandStageSurvival (L := L) (K := K) hn σ l E7 j hjl hjtop
      hEpos hEtop η hesc escapeε hescε).ε =
      DriftSurvival.driftBudgetNN 6 n + escapeε := rfl

/-- The naturally truncated family of one to three exact-band stages. -/
noncomputable def phase7BandStages
    {n : ℕ} (hn : 2 ≤ n)
    (σ : Sign) (l E7 : ℕ) (hlL : l ≤ L)
    (hEpos : 1 ≤ E7) (hEtop : 2 * E7 ≤ n * (n - 1))
    (η : ℝ≥0∞)
    (hesc : Phase7BandEscapeBound (L := L) (K := K) n σ l E7 η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    Fin (phase7StageCount L l) →
      PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun q =>
    phase7BandStageSurvival (L := L) (K := K) hn σ l E7
      (phase7StageIndex (L := L) l hlL q)
      (phase7StageIndex_range (L := L) l hlL q).1
      (phase7StageIndex_range (L := L) l hlL q).2
      hEpos hEtop η hesc escapeε hescε

/-- Compose the naturally available exact-band stages and recut the final
raw stage postcondition to the public cumulative `Post7Bands`. -/
noncomputable def phase7BandsSurvival
    {n : ℕ} (hn : 2 ≤ n)
    (σ : Sign) (l E7 : ℕ) (hlL : l ≤ L)
    (hEpos : 1 ≤ E7) (hEtop : 2 * E7 ≤ n * (n - 1))
    (η : ℝ≥0∞)
    (hesc : Phase7BandEscapeBound (L := L) (K := K) n σ l E7 η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel := by
  let m := phase7StageCount L l
  let stages := phase7BandStages (L := L) (K := K) hn σ l E7 hlL
    hEpos hEtop η hesc escapeε hescε
  have hm : 0 < m := phase7StageCount_pos (L := L) l hlL
  have hchain :
      ∀ (q : Fin m) (hq : q.val + 1 < m),
        ∀ c, (stages q).Post c →
          (stages ⟨q.val + 1, hq⟩).Pre c := by
    intro q hq c hc
    apply stageReady_succ_of_post
      (L := L) (K := K)
      (phase7StageIndex_succ (L := L) l hlL q hq).symm
    simpa [stages, phase7BandStages] using hc
  exact
    { Pre := (stages ⟨0, hm⟩).Pre
      Post := Post7Bands (L := L) (K := K) n σ l
      t := ∑ q : Fin m, (stages q).t
      ε := ∑ q : Fin m, (stages q).ε
      convergence := by
        intro c hc
        have hcomp := composeW_n_phases
          (K := (NonuniformMajority L K).transitionKernel)
          hm stages hchain c hc
        have hsubset :
            {c' | ¬ Post7Bands (L := L) (K := K) n σ l c'} ⊆
              {c' | ¬(stages ⟨m - 1, by omega⟩).Post c'} := by
          intro c' hc'
          intro hlast
          apply hc'
          apply post7Bands_of_last_stage_post (L := L) (K := K) hlL
          simpa [stages, phase7BandStages, phase7LastStageIndex] using hlast
        have hε :
            (((∑ q : Fin m, (stages q).ε : ℝ≥0)) : ℝ≥0∞) =
              ∑ q : Fin m, ((stages q).ε : ℝ≥0∞) := by
          push_cast
          rfl
        calc
          ((NonuniformMajority L K).transitionKernel ^
                (∑ q : Fin m, (stages q).t)) c
              {c' | ¬ Post7Bands (L := L) (K := K) n σ l c'}
              ≤ ((NonuniformMajority L K).transitionKernel ^
                  (∑ q : Fin m, (stages q).t)) c
                {c' | ¬(stages ⟨m - 1, by omega⟩).Post c'} :=
            measure_mono hsubset
          _ ≤ ∑ q : Fin m, ((stages q).ε : ℝ≥0∞) := hcomp
          _ = (((∑ q : Fin m, (stages q).ε : ℝ≥0)) : ℝ≥0∞) := hε.symm }

@[simp] theorem phase7BandsSurvival_t
    {n : ℕ} (hn : 2 ≤ n)
    (σ : Sign) (l E7 : ℕ) (hlL : l ≤ L)
    (hEpos : 1 ≤ E7) (hEtop : 2 * E7 ≤ n * (n - 1))
    (η : ℝ≥0∞)
    (hesc : Phase7BandEscapeBound (L := L) (K := K) n σ l E7 η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    (phase7BandsSurvival (L := L) (K := K) hn σ l E7 hlL hEpos hEtop
      η hesc escapeε hescε).t =
      phase7StageCount L l *
        DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 := by
  simp [phase7BandsSurvival, phase7BandStages]

@[simp] theorem phase7BandsSurvival_epsilon
    {n : ℕ} (hn : 2 ≤ n)
    (σ : Sign) (l E7 : ℕ) (hlL : l ≤ L)
    (hEpos : 1 ≤ E7) (hEtop : 2 * E7 ≤ n * (n - 1))
    (η : ℝ≥0∞)
    (hesc : Phase7BandEscapeBound (L := L) (K := K) n σ l E7 η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    (phase7BandsSurvival (L := L) (K := K) hn σ l E7 hlL hEpos hEtop
      η hesc escapeε hescε).ε =
      (phase7StageCount L l : ℝ≥0) *
        (DriftSurvival.driftBudgetNN 6 n + escapeε) := by
  simp [phase7BandsSurvival, phase7BandStages, mul_add]

/-- Three sixth-shares (drift plus an equally-sized escape share) fit the
single inverse-square Phase-7 budget. -/
theorem phase7BandsSurvival_epsilon_le_inv_sq
    {n : ℕ} (hn : 2 ≤ n)
    (σ : Sign) (l E7 : ℕ) (hlL : l ≤ L)
    (hEpos : 1 ≤ E7) (hEtop : 2 * E7 ≤ n * (n - 1))
    (η : ℝ≥0∞)
    (hesc : Phase7BandEscapeBound (L := L) (K := K) n σ l E7 η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞))
    (hescape : escapeε ≤ DriftSurvival.driftBudgetNN 6 n) :
    ((phase7BandsSurvival (L := L) (K := K) hn σ l E7 hlL hEpos hEtop
      η hesc escapeε hescε).ε : ℝ≥0∞) ≤
        1 / (n : ℝ≥0∞) ^ 2 := by
  rw [phase7BandsSurvival_epsilon, ENNReal.coe_mul, ENNReal.coe_add]
  have hm : (phase7StageCount L l : ℝ≥0∞) ≤ 3 := by
    exact_mod_cast phase7StageCount_le_three L l
  have he : (escapeε : ℝ≥0∞) ≤
      (DriftSurvival.driftBudgetNN 6 n : ℝ≥0∞) := by
    exact_mod_cast hescape
  calc
    (phase7StageCount L l : ℝ≥0∞) *
          ((DriftSurvival.driftBudgetNN 6 n : ℝ≥0∞) + (escapeε : ℝ≥0∞))
        ≤ 3 * ((DriftSurvival.driftBudgetNN 6 n : ℝ≥0∞) +
          (DriftSurvival.driftBudgetNN 6 n : ℝ≥0∞)) := by gcongr
    _ = 6 * (DriftSurvival.driftBudgetNN 6 n : ℝ≥0∞) := by ring
    _ = 1 / (n : ℝ≥0∞) ^ 2 :=
      DriftSurvival.natCast_mul_driftBudgetNN_eq_inv_sq
        (D := 6) (n := n) (by norm_num) (by omega)

#print axioms phase7BandStageSurvival
#print axioms phase7BandsSurvival
#print axioms phase7BandsSurvival_t
#print axioms phase7BandsSurvival_epsilon
#print axioms phase7BandsSurvival_epsilon_le_inv_sq

end Phase7BandSurvival
end Ripple.PopulationProtocol.ExactMajority
