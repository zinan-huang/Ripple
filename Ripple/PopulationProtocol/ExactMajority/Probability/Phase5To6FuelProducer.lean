/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-5 to Phase-6 two-level fuel producer

Deterministic transport and the narrow sampling interface needed to turn the
Phase-3 upper-tail estimate into the persistent Phase-6 fuel ledger.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6FuelEntry
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Post3
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase4Convergence

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase5To6FuelProducer

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

-- Exact `Fin 11` max rewrites below intentionally keep proof terms
-- syntactically aligned.  Proof irrelevance makes the embedded `decide`
-- witnesses redundant, which triggers these two tactic linters despite the
-- witnesses being needed for the rewrite shape.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## Phase-3 algebra needed at the Phase-3/4 seam -/

/-- Positive signed mass is nonincreasing under the concrete Phase-3 pair
rule.  This is the half-sum of total-mass monotonicity and signed-gap
conservation. -/
theorem Phase3Transition_agentPosMassQ_pair_le
    (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    P3DeterministicAlgebra.agentPosMassQ (L := L) (K := K)
          (Phase3Transition L K s t).1 +
        P3DeterministicAlgebra.agentPosMassQ (L := L) (K := K)
          (Phase3Transition L K s t).2 ≤
      P3DeterministicAlgebra.agentPosMassQ (L := L) (K := K) s +
        P3DeterministicAlgebra.agentPosMassQ (L := L) (K := K) t := by
  have hmass := P3DeterministicAlgebra.p3_totalMass_pair_le
    (L := L) (K := K) s t hs ht
  have hgap := P3DeterministicAlgebra.p3_biasSum_pair_eq
    (L := L) (K := K) s t hs ht
  simp only [P3DeterministicAlgebra.pairMassQ,
    P3DeterministicAlgebra.agentMassQ,
    P3DeterministicAlgebra.biasMassQ] at hmass
  simp only [P3DeterministicAlgebra.Bias.toRat_eq_pos_sub_neg] at hgap
  unfold P3DeterministicAlgebra.agentPosMassQ
  linarith

/-- Negative signed mass is nonincreasing under the concrete Phase-3 pair
rule. -/
theorem Phase3Transition_agentNegMassQ_pair_le
    (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    P3DeterministicAlgebra.agentNegMassQ (L := L) (K := K)
          (Phase3Transition L K s t).1 +
        P3DeterministicAlgebra.agentNegMassQ (L := L) (K := K)
          (Phase3Transition L K s t).2 ≤
      P3DeterministicAlgebra.agentNegMassQ (L := L) (K := K) s +
        P3DeterministicAlgebra.agentNegMassQ (L := L) (K := K) t := by
  have hmass := P3DeterministicAlgebra.p3_totalMass_pair_le
    (L := L) (K := K) s t hs ht
  have hgap := P3DeterministicAlgebra.p3_biasSum_pair_eq
    (L := L) (K := K) s t hs ht
  simp only [P3DeterministicAlgebra.pairMassQ,
    P3DeterministicAlgebra.agentMassQ,
    P3DeterministicAlgebra.biasMassQ] at hmass
  simp only [P3DeterministicAlgebra.Bias.toRat_eq_pos_sub_neg] at hgap
  unfold P3DeterministicAlgebra.agentNegMassQ
  linarith

/-- At phase 3 the clock counter can enter only Phase 4, whose initializer
does not alter the role. -/
theorem stdCounterSubroutine_role_of_phase_three
    (a : AgentState L K) (ha : a.phase.val = 3) :
    (stdCounterSubroutine L K a).role = a.role := by
  unfold stdCounterSubroutine
  split_ifs
  · unfold advancePhaseWithInit advancePhase
    simp [ha, phaseInit]
  · rfl

/-- Cancel/split changes only bias and hour, never roles. -/
theorem phase3CancelSplit_roles
    (s t : AgentState L K) :
    (phase3CancelSplit L K s t).1.role = s.role ∧
      (phase3CancelSplit L K s t).2.role = t.role := by
  unfold phase3CancelSplit
  match s.bias, t.bias with
  | .zero, .zero => simp
  | .zero, .dyadic _ _ => simp; split_ifs <;> simp
  | .dyadic _ _, .zero => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .neg _ => simp

/-- Phase 3 never changes either participant's role. -/
theorem Phase3Transition_roles
    (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    (Phase3Transition L K s t).1.role = s.role ∧
      (Phase3Transition L K s t).2.role = t.role := by
  let s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else stdCounterSubroutine L K s
  else s
  let t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then t
    else stdCounterSubroutine L K t
  else t
  let s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1 : s1.role = s.role := by
    dsimp [s1]
    split_ifs <;> simp [stdCounterSubroutine_role_of_phase_three, hs]
  have ht1 : t1.role = t.role := by
    dsimp [t1]
    split_ifs <;> simp [stdCounterSubroutine_role_of_phase_three, ht]
  have hs2 : s2.role = s1.role := by
    dsimp [s2]
    split_ifs <;> simp
  have ht2 : t2.role = t1.role := by
    dsimp [t2]
    split_ifs <;> simp
  have hfinal :
      (Phase3Transition L K s t).1.role = s2.role ∧
        (Phase3Transition L K s t).2.role = t2.role := by
    unfold Phase3Transition
    change
      (if s2.role = .main ∧ t2.role = .main then
          phase3CancelSplit L K s2 t2 else (s2, t2)).1.role = s2.role ∧
        (if s2.role = .main ∧ t2.role = .main then
          phase3CancelSplit L K s2 t2 else (s2, t2)).2.role = t2.role
    by_cases hmain : s2.role = .main ∧ t2.role = .main
    · simpa [hmain] using phase3CancelSplit_roles (L := L) (K := K) s2 t2
    · simp [hmain]
  exact ⟨hfinal.1.trans (hs2.trans hs1),
    hfinal.2.trans (ht2.trans ht1)⟩

/-- If the input pair is not Main×Main, Phase 3 changes neither bias.  The
only bias-changing rule is the final cancel/split block, whose guard is then
false because the preceding clock/hour rules preserve roles. -/
theorem Phase3Transition_biases_of_not_both_main
    (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (hnot : ¬ (s.role = .main ∧ t.role = .main)) :
    (Phase3Transition L K s t).1.bias = s.bias ∧
      (Phase3Transition L K s t).2.bias = t.bias := by
  let s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else stdCounterSubroutine L K s
  else s
  let t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then t
    else stdCounterSubroutine L K t
  else t
  let s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1bias : s1.bias = s.bias := by
    dsimp [s1]
    split_ifs <;>
      simp [stdCounterSubroutine_preserves_bias_of_phase_three, hs]
  have ht1bias : t1.bias = t.bias := by
    dsimp [t1]
    split_ifs <;>
      simp [stdCounterSubroutine_preserves_bias_of_phase_three, ht]
  have hs1role : s1.role = s.role := by
    dsimp [s1]
    split_ifs <;> simp [stdCounterSubroutine_role_of_phase_three, hs]
  have ht1role : t1.role = t.role := by
    dsimp [t1]
    split_ifs <;> simp [stdCounterSubroutine_role_of_phase_three, ht]
  have hs2bias : s2.bias = s1.bias := by
    dsimp [s2]
    split_ifs <;> simp
  have ht2bias : t2.bias = t1.bias := by
    dsimp [t2]
    split_ifs <;> simp
  have hs2role : s2.role = s1.role := by
    dsimp [s2]
    split_ifs <;> simp
  have ht2role : t2.role = t1.role := by
    dsimp [t2]
    split_ifs <;> simp
  have hnot2 : ¬ (s2.role = .main ∧ t2.role = .main) := by
    intro hmain
    apply hnot
    constructor
    · rw [← hs1role, ← hs2role]
      exact hmain.1
    · rw [← ht1role, ← ht2role]
      exact hmain.2
  unfold Phase3Transition
  change
    (if s2.role = .main ∧ t2.role = .main then
        phase3CancelSplit L K s2 t2 else (s2, t2)).1.bias = s.bias ∧
      (if s2.role = .main ∧ t2.role = .main then
        phase3CancelSplit L K s2 t2 else (s2, t2)).2.bias = t.bias
  simp only [hnot2, if_false]
  exact ⟨hs2bias.trans hs1bias, ht2bias.trans ht1bias⟩

/-- Main-restricted rational upper-tail observable. -/
noncomputable def agentMainMassAboveQ
    (l : ℕ) (a : AgentState L K) : ℚ :=
  if a.role = .main then
    P3DeterministicAlgebra.agentMassAboveQ (L := L) (K := K) l a
  else 0

/-- The Main-restricted rational upper tail is nonincreasing under a concrete
Phase-3 pair update. -/
theorem Phase3Transition_agentMainMassAboveQ_pair_le
    (l : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    agentMainMassAboveQ (L := L) (K := K) l
          (Phase3Transition L K s t).1 +
        agentMainMassAboveQ (L := L) (K := K) l
          (Phase3Transition L K s t).2 ≤
      agentMainMassAboveQ (L := L) (K := K) l s +
        agentMainMassAboveQ (L := L) (K := K) l t := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · have hroles := Phase3Transition_roles
      (L := L) (K := K) s t hs ht
    have hq := P3DeterministicAlgebra.p3_massAbove_pair_le
      (L := L) (K := K) l s t hs ht
    simpa [agentMainMassAboveQ,
      hmain.1, hmain.2, hroles.1, hroles.2,
      P3DeterministicAlgebra.pairMassAboveQ] using hq
  · have hroles := Phase3Transition_roles
      (L := L) (K := K) s t hs ht
    have hbias := Phase3Transition_biases_of_not_both_main
      (L := L) (K := K) s t hs ht hmain
    unfold agentMainMassAboveQ P3DeterministicAlgebra.agentMassAboveQ
    rw [hroles.1, hroles.2, hbias.1, hbias.2]

/-- The natural scaled observable used by Lemma 6.15 is exactly `2^l` times
the Main-restricted rational Phase-3 upper-tail observable. -/
theorem agentMassAboveScaledW_cast_eq
    (l : ℕ) (a : AgentState L K) :
    (Lemma615MassAbove.agentMassAboveScaledW
        (L := L) (K := K) l a : ℚ) =
      (2 : ℚ) ^ l * agentMainMassAboveQ (L := L) (K := K) l a := by
  by_cases hr : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [Lemma615MassAbove.agentMassAboveScaledW,
          Lemma615MassAbove.biasMassAboveScaledW,
          agentMainMassAboveQ, P3DeterministicAlgebra.agentMassAboveQ,
          P3DeterministicAlgebra.biasMassAboveQ, hr, hb]
    | dyadic σ i =>
        by_cases hi : i.val < l
        · have hle : i.val ≤ l := Nat.le_of_lt hi
          have hpow :
              (2 : ℚ) ^ (l - i.val) * (2 : ℚ) ^ i.val =
                (2 : ℚ) ^ l :=
            pow_sub_mul_pow (2 : ℚ) hle
          simp only [Lemma615MassAbove.agentMassAboveScaledW, hr, if_true,
            Lemma615MassAbove.biasMassAboveScaledW, hb, hi,
            agentMainMassAboveQ, P3DeterministicAlgebra.agentMassAboveQ,
            P3DeterministicAlgebra.biasMassAboveQ,
            P3DeterministicAlgebra.weightQ,
            Nat.cast_pow, Nat.cast_ofNat]
          have hden : (2 : ℚ) ^ i.val ≠ 0 := by positivity
          field_simp [hden]
          exact hpow
        · simp [Lemma615MassAbove.agentMassAboveScaledW,
            Lemma615MassAbove.biasMassAboveScaledW,
            agentMainMassAboveQ, P3DeterministicAlgebra.agentMassAboveQ,
            P3DeterministicAlgebra.biasMassAboveQ, hr, hb, hi]
  · simp [Lemma615MassAbove.agentMassAboveScaledW,
      agentMainMassAboveQ, hr]

/-- Phase 3 therefore makes the exact natural scaled upper-tail mass
nonincreasing pairwise. -/
theorem Phase3Transition_agentMassAboveScaledW_pair_le
    (l : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Phase3Transition L K s t).1 +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Phase3Transition L K s t).2 ≤
      Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l s +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l t := by
  have hq := Phase3Transition_agentMainMassAboveQ_pair_le
    (L := L) (K := K) l s t hs ht
  have hpow : (0 : ℚ) ≤ (2 : ℚ) ^ l := by positivity
  have hscaled :
      (2 : ℚ) ^ l *
          (agentMainMassAboveQ (L := L) (K := K) l
              (Phase3Transition L K s t).1 +
            agentMainMassAboveQ (L := L) (K := K) l
              (Phase3Transition L K s t).2) ≤
        (2 : ℚ) ^ l *
          (agentMainMassAboveQ (L := L) (K := K) l s +
            agentMainMassAboveQ (L := L) (K := K) l t) := by
    exact mul_le_mul_of_nonneg_left hq hpow
  rw [mul_add, mul_add] at hscaled
  rw [← agentMassAboveScaledW_cast_eq,
      ← agentMassAboveScaledW_cast_eq,
      ← agentMassAboveScaledW_cast_eq,
      ← agentMassAboveScaledW_cast_eq] at hscaled
  exact_mod_cast hscaled

/-! ## The Phase-3/4 epidemic seam -/

/-- Entering Phase 4 changes only phase/output, hence preserves role and bias. -/
theorem phaseInit_four_role_bias
    (a : AgentState L K) :
    (phaseInit L K ⟨4, by decide⟩ a).role = a.role ∧
      (phaseInit L K ⟨4, by decide⟩ a).bias = a.bias := by
  simp [phaseInit]

/-- Exact epidemic normalization for a Phase-3/Phase-4 interaction. -/
theorem phaseEpidemicUpdate_eq_of_three_four
    (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 4) :
    phaseEpidemicUpdate L K s t =
      (phaseInit L K ⟨4, by decide⟩ {s with phase := ⟨4, by decide⟩},
        {t with phase := ⟨4, by decide⟩}) := by
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨4, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hsp, htp]
  simp only [max_eq_right
    (by decide : (⟨3, by decide⟩ : Fin 11) ≤ ⟨4, by decide⟩)]
  unfold runInitsBetween
  have h34 : (List.range 11).filter (fun k => 3 < k ∧ k ≤ 4) = [4] := by
    decide
  have h44 : (List.range 11).filter (fun k => 4 < k ∧ k ≤ 4) = [] := by
    decide
  rw [h34, h44]
  simp [phaseInit]

/-- Symmetric Phase-4/Phase-3 epidemic normalization. -/
theorem phaseEpidemicUpdate_eq_of_four_three
    (s t : AgentState L K)
    (hs : s.phase.val = 4) (ht : t.phase.val = 3) :
    phaseEpidemicUpdate L K s t =
      ({s with phase := ⟨4, by decide⟩},
        phaseInit L K ⟨4, by decide⟩ {t with phase := ⟨4, by decide⟩}) := by
  have hsp : s.phase = ⟨4, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨3, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hsp, htp]
  simp only [max_eq_left
    (by decide : (⟨3, by decide⟩ : Fin 11) ≤ ⟨4, by decide⟩)]
  unfold runInitsBetween
  have h44 : (List.range 11).filter (fun k => 4 < k ∧ k ≤ 4) = [] := by
    decide
  have h34 : (List.range 11).filter (fun k => 3 < k ∧ k ≤ 4) = [4] := by
    decide
  rw [h44, h34]
  simp [phaseInit]

/-! ## Main-bias staticity through Phases 4 and 5 -/

/-- Phase-5 Init preserves `role` (only `counter`/`hour` are written). -/
private lemma phaseInit_five_role (a : AgentState L K)
    (p : Fin 11) (hp : p.val = 5) :
    (phaseInit L K p a).role = a.role := by
  unfold phaseInit
  rw [dif_neg (show ¬ p.val = 1 by omega), dif_neg (show ¬ p.val = 2 by omega),
      dif_neg (show ¬ p.val = 3 by omega), dif_neg (show ¬ p.val = 4 by omega),
      dif_pos hp]
  split_ifs <;> rfl

/-- `advancePhaseWithInit` from a phase-4 agent preserves `role` and `bias`:
the destination is phase 5, whose Init touches only `counter`/`hour`
(2026-07-16 faithfulness fixes). -/
private lemma apwi_role_bias_of_phase4 (a : AgentState L K) (ha : a.phase.val = 4) :
    (advancePhaseWithInit L K a).role = a.role ∧
      (advancePhaseWithInit L K a).bias = a.bias := by
  unfold advancePhaseWithInit
  have hr : (advancePhase L K a).role = a.role := by
    unfold advancePhase; split <;> rfl
  have hb : (advancePhase L K a).bias = a.bias := by
    unfold advancePhase; split <;> rfl
  have hp5 : ((advancePhase L K a).phase).val = 5 := by
    unfold advancePhase
    rw [dif_pos (show a.phase.val < 10 by omega)]
    show a.phase.val.succ = 5
    omega
  constructor
  · rw [phaseInit_five_role (L := L) (K := K) (advancePhase L K a) _ hp5, hr]
  · rw [phaseInit_five_bias (L := L) (K := K) (advancePhase L K a) _ hp5, hb]

/-- The Phase-4 local rule changes only phase/counter/hour fields (never
role/bias) when fired from a phase-4 agent. -/
theorem Phase4Transition_agentMassAboveScaledW_fst
    (l : ℕ) (s t : AgentState L K) (hs : s.phase.val = 4) :
    Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
        (Phase4Transition L K s t).1 =
      Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l s := by
  obtain ⟨hr, hb⟩ := apwi_role_bias_of_phase4 (L := L) (K := K) s hs
  unfold Phase4Transition
  dsimp
  split_ifs
  · unfold Lemma615MassAbove.agentMassAboveScaledW
    rw [hr, hb]
  · rfl

/-- Right-output version of `Phase4Transition_agentMassAboveScaledW_fst`. -/
theorem Phase4Transition_agentMassAboveScaledW_snd
    (l : ℕ) (s t : AgentState L K) (ht : t.phase.val = 4) :
    Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
        (Phase4Transition L K s t).2 =
      Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l t := by
  obtain ⟨hr, hb⟩ := apwi_role_bias_of_phase4 (L := L) (K := K) t ht
  unfold Phase4Transition
  dsimp
  split_ifs
  · unfold Lemma615MassAbove.agentMassAboveScaledW
    rw [hr, hb]
  · rfl

/-- Phase 4 preserves each participant's role and bias (phase-4 inputs). -/
theorem Phase4Transition_role_bias
    (s t : AgentState L K) (hs : s.phase.val = 4) (ht : t.phase.val = 4) :
    (Phase4Transition L K s t).1.role = s.role ∧
      (Phase4Transition L K s t).1.bias = s.bias ∧
      (Phase4Transition L K s t).2.role = t.role ∧
      (Phase4Transition L K s t).2.bias = t.bias := by
  obtain ⟨hsr, hsb⟩ := apwi_role_bias_of_phase4 (L := L) (K := K) s hs
  obtain ⟨htr, htb⟩ := apwi_role_bias_of_phase4 (L := L) (K := K) t ht
  unfold Phase4Transition
  dsimp
  split_ifs
  · exact ⟨hsr, hsb, htr, htb⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The real dispatcher retains the Phase-3 upper-tail inequality on a
Phase-3/Phase-3 input pair. -/
theorem Transition_agentMassAboveScaledW_pair_le_of_three_three
    (l : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Transition L K s t).1 +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Transition L K s t).2 ≤
      Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l s +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l t := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3
    (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hp3 := Phase3Transition_agentMassAboveScaledW_pair_le
    (L := L) (K := K) l s t hs ht
  unfold Transition
  rw [hepi]
  simp only [hsp]
  simpa only [Lemma615MassAbove.agentMassAboveScaledW,
    finishPhase10Entry_role, finishPhase10Entry_bias] using hp3

/-- Positive-mass version of the full Phase-3 dispatcher inequality. -/
theorem Transition_agentPosMassQ_pair_le_of_three_three
    (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    P3DeterministicAlgebra.agentPosMassQ (L := L) (K := K)
          (Transition L K s t).1 +
        P3DeterministicAlgebra.agentPosMassQ (L := L) (K := K)
          (Transition L K s t).2 ≤
      P3DeterministicAlgebra.agentPosMassQ (L := L) (K := K) s +
        P3DeterministicAlgebra.agentPosMassQ (L := L) (K := K) t := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3
    (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hp3 := Phase3Transition_agentPosMassQ_pair_le
    (L := L) (K := K) s t hs ht
  unfold Transition
  rw [hepi]
  simp only [hsp]
  simpa only [P3DeterministicAlgebra.agentPosMassQ,
    finishPhase10Entry_bias] using hp3

/-- Negative-mass version of the full Phase-3 dispatcher inequality. -/
theorem Transition_agentNegMassQ_pair_le_of_three_three
    (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    P3DeterministicAlgebra.agentNegMassQ (L := L) (K := K)
          (Transition L K s t).1 +
        P3DeterministicAlgebra.agentNegMassQ (L := L) (K := K)
          (Transition L K s t).2 ≤
      P3DeterministicAlgebra.agentNegMassQ (L := L) (K := K) s +
        P3DeterministicAlgebra.agentNegMassQ (L := L) (K := K) t := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3
    (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hp3 := Phase3Transition_agentNegMassQ_pair_le
    (L := L) (K := K) s t hs ht
  unfold Transition
  rw [hepi]
  simp only [hsp]
  simpa only [P3DeterministicAlgebra.agentNegMassQ,
    finishPhase10Entry_bias] using hp3

/-- The full dispatcher preserves both participants' role/bias fields on a
Phase-4/Phase-4 pair. -/
theorem Transition_role_bias_of_four_four
    (s t : AgentState L K)
    (hs : s.phase.val = 4) (ht : t.phase.val = 4) :
    (Transition L K s t).1.role = s.role ∧
      (Transition L K s t).1.bias = s.bias ∧
      (Transition L K s t).2.role = t.role ∧
      (Transition L K s t).2.bias = t.bias := by
  have hepi := Phase4Convergence.phaseEpidemicUpdate_eq_self_of_phase4
    (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨4, by decide⟩ := Fin.ext hs
  have h4 := Phase4Transition_role_bias (L := L) (K := K) s t hs ht
  unfold Transition
  rw [hepi]
  simp only [hsp, finishPhase10Entry_role, finishPhase10Entry_bias]
  exact h4

/-- Mixed Phase-3/4 epidemic entry and Phase-4 dispatch preserve role/bias. -/
theorem Transition_role_bias_of_three_four
    (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 4) :
    (Transition L K s t).1.role = s.role ∧
      (Transition L K s t).1.bias = s.bias ∧
      (Transition L K s t).2.role = t.role ∧
      (Transition L K s t).2.bias = t.bias := by
  let s4 := phaseInit L K ⟨4, by decide⟩
    {s with phase := ⟨4, by decide⟩}
  let t4 : AgentState L K := {t with phase := ⟨4, by decide⟩}
  have hepi : phaseEpidemicUpdate L K s t = (s4, t4) := by
    simpa [s4, t4] using phaseEpidemicUpdate_eq_of_three_four
      (L := L) (K := K) s t hs ht
  have hs4p : s4.phase = ⟨4, by decide⟩ := by
    simp [s4, phaseInit]
  have hs4fields : s4.role = s.role ∧ s4.bias = s.bias := by
    dsimp [s4]
    simpa using phaseInit_four_role_bias
      (L := L) (K := K) {s with phase := ⟨4, by decide⟩}
  have ht4fields : t4.role = t.role ∧ t4.bias = t.bias := by
    simp [t4]
  have hs4v : s4.phase.val = 4 := by rw [hs4p]
  have ht4v : t4.phase.val = 4 := by simp [t4, phaseInit]
  have h4 := Phase4Transition_role_bias (L := L) (K := K) s4 t4 hs4v ht4v
  unfold Transition
  rw [hepi]
  simp only [hs4p, finishPhase10Entry_role, finishPhase10Entry_bias]
  exact ⟨h4.1.trans hs4fields.1,
    h4.2.1.trans hs4fields.2,
    h4.2.2.1.trans ht4fields.1,
    h4.2.2.2.trans ht4fields.2⟩

/-- Symmetric mixed Phase-4/3 role/bias preservation. -/
theorem Transition_role_bias_of_four_three
    (s t : AgentState L K)
    (hs : s.phase.val = 4) (ht : t.phase.val = 3) :
    (Transition L K s t).1.role = s.role ∧
      (Transition L K s t).1.bias = s.bias ∧
      (Transition L K s t).2.role = t.role ∧
      (Transition L K s t).2.bias = t.bias := by
  let s4 : AgentState L K := {s with phase := ⟨4, by decide⟩}
  let t4 := phaseInit L K ⟨4, by decide⟩
    {t with phase := ⟨4, by decide⟩}
  have hepi : phaseEpidemicUpdate L K s t = (s4, t4) := by
    simpa [s4, t4] using phaseEpidemicUpdate_eq_of_four_three
      (L := L) (K := K) s t hs ht
  have hs4p : s4.phase = ⟨4, by decide⟩ := by simp [s4]
  have hs4fields : s4.role = s.role ∧ s4.bias = s.bias := by simp [s4]
  have ht4fields : t4.role = t.role ∧ t4.bias = t.bias := by
    dsimp [t4]
    simpa using phaseInit_four_role_bias
      (L := L) (K := K) {t with phase := ⟨4, by decide⟩}
  have hs4v : s4.phase.val = 4 := by rw [hs4p]
  have ht4v : t4.phase.val = 4 := by simp [t4, phaseInit]
  have h4 := Phase4Transition_role_bias (L := L) (K := K) s4 t4 hs4v ht4v
  unfold Transition
  rw [hepi]
  simp only [hs4p, finishPhase10Entry_role, finishPhase10Entry_bias]
  exact ⟨h4.1.trans hs4fields.1,
    h4.2.1.trans hs4fields.2,
    h4.2.2.1.trans ht4fields.1,
    h4.2.2.2.trans ht4fields.2⟩

/-- The Phase-5 sampling rule freezes each input agent's Main-bias weight. -/
theorem Phase5Transition_agentMassAboveScaledW_pair
    (l : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 5) :
    Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Phase5Transition L K s t).1 +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Phase5Transition L K s t).2 =
      Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l s +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l t := by
  have hr1 := Phase5Convergence.Phase5Transition_fst_role_eq
    (L := L) (K := K) s t hs
  have hb1 := Phase5Convergence.Phase5Transition_fst_bias_eq
    (L := L) (K := K) s t hs
  have hr2 := Phase5Convergence.Phase5Transition_snd_role_eq
    (L := L) (K := K) s t ht
  have hb2 := Phase5Convergence.Phase5Transition_snd_bias_eq
    (L := L) (K := K) s t ht
  unfold Lemma615MassAbove.agentMassAboveScaledW
  rw [hr1, hb1, hr2, hb2]

/-- Entering Phase 5 does not alter the Main-bias upper-tail weight. -/
theorem phaseInit_five_agentMassAboveScaledW
    (l : ℕ) (a : AgentState L K) :
    Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
        (phaseInit L K ⟨5, by decide⟩ a) =
      Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l a := by
  unfold Lemma615MassAbove.agentMassAboveScaledW phaseInit
  simp
  split_ifs <;> rfl

/-- Entering Phase 5 preserves every exact signed Main class. -/
theorem phaseInit_five_biasedMainClass_iff
    (σ : Sign) (i : Fin (L + 1)) (a : AgentState L K) :
    Phase5Convergence.biasedMainClass (L := L) (K := K) σ i
        (phaseInit L K ⟨5, by decide⟩ a) ↔
      Phase5Convergence.biasedMainClass (L := L) (K := K) σ i a := by
  unfold Phase5Convergence.biasedMainClass
  rw [Phase5Convergence.phaseInit_role_ge_five
        (L := L) (K := K) ⟨5, by decide⟩ a
        (show 5 ≤ (⟨5, by decide⟩ : Fin 11).val from by decide),
      Phase5Convergence.phaseInit_bias_ge_five
        (L := L) (K := K) ⟨5, by decide⟩ a
        (show 5 ≤ (⟨5, by decide⟩ : Fin 11).val from by decide)]

/-- Phase 4 preserves every exact signed Main class in its left output. -/
theorem Phase4Transition_biasedMainClass_fst_iff
    (σ : Sign) (i : Fin (L + 1)) (s t : AgentState L K) (hs : s.phase.val = 4) :
    Phase5Convergence.biasedMainClass (L := L) (K := K) σ i
        (Phase4Transition L K s t).1 ↔
      Phase5Convergence.biasedMainClass (L := L) (K := K) σ i s := by
  obtain ⟨hr, hb⟩ := apwi_role_bias_of_phase4 (L := L) (K := K) s hs
  unfold Phase4Transition
  dsimp
  split_ifs
  · unfold Phase5Convergence.biasedMainClass
    rw [hr, hb]
  · rfl

/-- Phase 4 preserves every exact signed Main class in its right output. -/
theorem Phase4Transition_biasedMainClass_snd_iff
    (σ : Sign) (i : Fin (L + 1)) (s t : AgentState L K) (ht : t.phase.val = 4) :
    Phase5Convergence.biasedMainClass (L := L) (K := K) σ i
        (Phase4Transition L K s t).2 ↔
      Phase5Convergence.biasedMainClass (L := L) (K := K) σ i t := by
  obtain ⟨hr, hb⟩ := apwi_role_bias_of_phase4 (L := L) (K := K) t ht
  unfold Phase4Transition
  dsimp
  split_ifs
  · unfold Phase5Convergence.biasedMainClass
    rw [hr, hb]
  · rfl

/-- Exact epidemic normalization for a Phase-4/Phase-5 interaction.  The
Phase-4 agent runs precisely the Phase-5 initializer; the Phase-5 agent is
unchanged apart from the already-present phase field. -/
theorem phaseEpidemicUpdate_eq_of_four_five
    (s t : AgentState L K)
    (hs : s.phase.val = 4) (ht : t.phase.val = 5) :
    phaseEpidemicUpdate L K s t =
      (phaseInit L K ⟨5, by decide⟩ {s with phase := ⟨5, by decide⟩},
        {t with phase := ⟨5, by decide⟩}) := by
  have hsp : s.phase = ⟨4, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨5, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hsp, htp]
  simp only [max_eq_right
    (by decide : (⟨4, by decide⟩ : Fin 11) ≤ ⟨5, by decide⟩)]
  unfold runInitsBetween
  have h45 : (List.range 11).filter (fun k => 4 < k ∧ k ≤ 5) = [5] := by
    decide
  have h55 : (List.range 11).filter (fun k => 5 < k ∧ k ≤ 5) = [] := by
    decide
  rw [h45, h55]
  simp only [List.foldl_cons, List.foldl_nil,
    show (5 < 11) from by decide, dite_true]
  by_cases hsc : s.role = .clock
  · simp [phaseInit, hsc]
  · by_cases hsr : s.role = .reserve <;> simp [phaseInit, hsc, hsr]

/-- Symmetric epidemic normalization for a Phase-5/Phase-4 interaction. -/
theorem phaseEpidemicUpdate_eq_of_five_four
    (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 4) :
    phaseEpidemicUpdate L K s t =
      ({s with phase := ⟨5, by decide⟩},
        phaseInit L K ⟨5, by decide⟩ {t with phase := ⟨5, by decide⟩}) := by
  have hsp : s.phase = ⟨5, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨4, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hsp, htp]
  simp only [max_eq_left
    (by decide : (⟨4, by decide⟩ : Fin 11) ≤ ⟨5, by decide⟩)]
  unfold runInitsBetween
  have h55 : (List.range 11).filter (fun k => 5 < k ∧ k ≤ 5) = [] := by
    decide
  have h45 : (List.range 11).filter (fun k => 4 < k ∧ k ≤ 5) = [5] := by
    decide
  rw [h55, h45]
  simp only [List.foldl_cons, List.foldl_nil,
    show (5 < 11) from by decide, dite_true]
  by_cases htc : t.role = .clock
  · simp [phaseInit, htc]
  · by_cases htr : t.role = .reserve <;> simp [phaseInit, htc, htr]

/-- The epidemic lift from a Phase-4/Phase-5 pair to Phase 5 freezes the
Main-bias profile. -/
theorem phaseEpidemicUpdate_agentMassAboveScaledW_pair_of_four_five
    (l : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 4) (ht : t.phase.val = 5) :
    Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (phaseEpidemicUpdate L K s t).1 +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (phaseEpidemicUpdate L K s t).2 =
      Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l s +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l t := by
  have hsp : s.phase = ⟨4, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨5, by decide⟩ := Fin.ext ht
  have h45 : (List.range 11).filter (fun k => 4 < k ∧ k ≤ 5) = [5] := by
    decide
  have h55 : (List.range 11).filter (fun k => 5 < k ∧ k ≤ 5) = [] := by
    decide
  have hfields :
      (phaseEpidemicUpdate L K s t).1.role = s.role ∧
        (phaseEpidemicUpdate L K s t).1.bias = s.bias ∧
        (phaseEpidemicUpdate L K s t).2.role = t.role ∧
        (phaseEpidemicUpdate L K s t).2.bias = t.bias := by
    unfold phaseEpidemicUpdate
    rw [hsp, htp]
    simp only [max_eq_right
      (by decide : (⟨4, by decide⟩ : Fin 11) ≤ ⟨5, by decide⟩)]
    unfold runInitsBetween
    rw [h45, h55]
    simp only [List.foldl_cons, List.foldl_nil,
      show (5 < 11) from by decide, dite_true]
    split_ifs <;>
      by_cases hsc : s.role = .clock <;>
        by_cases hsr : s.role = .reserve <;> simp_all [phaseInit]
  unfold Lemma615MassAbove.agentMassAboveScaledW
  rw [hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2]

/-! ## Full-kernel transport on the Phase-4/Phase-5 seam -/

/-- A mixed Phase-4/Phase-5 interaction dispatches the epidemic-normalized
pair through the actual Phase-5 rule. -/
theorem Transition_eq_Phase5Transition_of_four_five
    (s t : AgentState L K)
    (hs : s.phase.val = 4) (ht : t.phase.val = 5) :
    Transition L K s t =
      Phase5Transition L K
        (phaseInit L K ⟨5, by decide⟩ {s with phase := ⟨5, by decide⟩})
        {t with phase := ⟨5, by decide⟩} := by
  let s5 := phaseInit L K ⟨5, by decide⟩ {s with phase := ⟨5, by decide⟩}
  let t5 : AgentState L K := {t with phase := ⟨5, by decide⟩}
  have hepi : phaseEpidemicUpdate L K s t = (s5, t5) := by
    simpa [s5, t5] using phaseEpidemicUpdate_eq_of_four_five
      (L := L) (K := K) s t hs ht
  have hs5 : s5.phase.val = 5 := by
    show (phaseInit L K ⟨5, by decide⟩ {s with phase := ⟨5, by decide⟩}).phase.val = 5
    rw [phaseInit_five_phase (L := L) (K := K) _ ⟨5, by decide⟩ (by decide)]
  have ht5 : t5.phase.val = 5 := by simp [t5]
  obtain ⟨hle1, hle2⟩ := ReserveSampling.Phase5Transition_phase_le_six
    (L := L) (K := K) s5 t5 hs5 ht5
  have hs5p : s5.phase = ⟨5, by decide⟩ := Fin.ext hs5
  unfold Transition
  rw [hepi]
  simp only [hs5p]
  rw [finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) s5 _ (by omega),
      finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) t5 _ (by omega)]

/-- Symmetric mixed Phase-5/Phase-4 dispatcher reduction. -/
theorem Transition_eq_Phase5Transition_of_five_four
    (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 4) :
    Transition L K s t =
      Phase5Transition L K
        {s with phase := ⟨5, by decide⟩}
        (phaseInit L K ⟨5, by decide⟩ {t with phase := ⟨5, by decide⟩}) := by
  let s5 : AgentState L K := {s with phase := ⟨5, by decide⟩}
  let t5 := phaseInit L K ⟨5, by decide⟩ {t with phase := ⟨5, by decide⟩}
  have hepi : phaseEpidemicUpdate L K s t = (s5, t5) := by
    simpa [s5, t5] using phaseEpidemicUpdate_eq_of_five_four
      (L := L) (K := K) s t hs ht
  have hs5 : s5.phase.val = 5 := by simp [s5]
  have ht5 : t5.phase.val = 5 := by
    show (phaseInit L K ⟨5, by decide⟩ {t with phase := ⟨5, by decide⟩}).phase.val = 5
    rw [phaseInit_five_phase (L := L) (K := K) _ ⟨5, by decide⟩ (by decide)]
  obtain ⟨hle1, hle2⟩ := ReserveSampling.Phase5Transition_phase_le_six
    (L := L) (K := K) s5 t5 hs5 ht5
  have hs5p : s5.phase = ⟨5, by decide⟩ := Fin.ext hs5
  unfold Transition
  rw [hepi]
  simp only [hs5p]
  rw [finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) s5 _ (by omega),
      finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) t5 _ (by omega)]

/-- The real kernel preserves the scaled upper-tail mass across a mixed
Phase-4/Phase-5 interaction. -/
theorem Transition_agentMassAboveScaledW_pair_of_four_five
    (l : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 4) (ht : t.phase.val = 5) :
    Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Transition L K s t).1 +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Transition L K s t).2 =
      Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l s +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l t := by
  rw [Transition_eq_Phase5Transition_of_four_five
    (L := L) (K := K) s t hs ht]
  let s5 := phaseInit L K ⟨5, by decide⟩ {s with phase := ⟨5, by decide⟩}
  let t5 : AgentState L K := {t with phase := ⟨5, by decide⟩}
  have hs5 : s5.phase.val = 5 := by
    show (phaseInit L K ⟨5, by decide⟩ {s with phase := ⟨5, by decide⟩}).phase.val = 5
    rw [phaseInit_five_phase (L := L) (K := K) _ ⟨5, by decide⟩ (by decide)]
  have ht5 : t5.phase.val = 5 := by simp [t5]
  calc
    _ = Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l s5 +
          Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l t5 :=
      Phase5Transition_agentMassAboveScaledW_pair
        (L := L) (K := K) l s5 t5 hs5 ht5
    _ = _ := by
      rw [phaseInit_five_agentMassAboveScaledW]
      simp [t5, Lemma615MassAbove.agentMassAboveScaledW]

/-- Symmetric mixed Phase-5/Phase-4 mass transport. -/
theorem Transition_agentMassAboveScaledW_pair_of_five_four
    (l : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 4) :
    Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Transition L K s t).1 +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Transition L K s t).2 =
      Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l s +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l t := by
  rw [Transition_eq_Phase5Transition_of_five_four
    (L := L) (K := K) s t hs ht]
  let s5 : AgentState L K := {s with phase := ⟨5, by decide⟩}
  let t5 := phaseInit L K ⟨5, by decide⟩ {t with phase := ⟨5, by decide⟩}
  have hs5 : s5.phase.val = 5 := by simp [s5]
  have ht5 : t5.phase.val = 5 := by
    show (phaseInit L K ⟨5, by decide⟩ {t with phase := ⟨5, by decide⟩}).phase.val = 5
    rw [phaseInit_five_phase (L := L) (K := K) _ ⟨5, by decide⟩ (by decide)]
  calc
    _ = Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l s5 +
          Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l t5 :=
      Phase5Transition_agentMassAboveScaledW_pair
        (L := L) (K := K) l s5 t5 hs5 ht5
    _ = _ := by
      rw [phaseInit_five_agentMassAboveScaledW]
      simp [s5, Lemma615MassAbove.agentMassAboveScaledW]

/-- Phase 4 preserves the scaled upper-tail mass under the full dispatcher. -/
theorem Transition_agentMassAboveScaledW_pair_of_four_four
    (l : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 4) (ht : t.phase.val = 4) :
    Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Transition L K s t).1 +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Transition L K s t).2 =
      Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l s +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l t := by
  have hepi := Phase4Convergence.phaseEpidemicUpdate_eq_self_of_phase4
    (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨4, by decide⟩ := Fin.ext hs
  unfold Transition
  rw [hepi]
  simp only [hsp]
  have h1 := Phase4Transition_agentMassAboveScaledW_fst
    (L := L) (K := K) l s t hs
  have h2 := Phase4Transition_agentMassAboveScaledW_snd
    (L := L) (K := K) l s t ht
  unfold Lemma615MassAbove.agentMassAboveScaledW at h1 h2 ⊢
  simp only [finishPhase10Entry_role, finishPhase10Entry_bias]
  exact congrArg₂ (· + ·) h1 h2

/-- Phase 5 preserves the scaled upper-tail mass under the full dispatcher. -/
theorem Transition_agentMassAboveScaledW_pair_of_five_five
    (l : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 5) :
    Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Transition L K s t).1 +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Transition L K s t).2 =
      Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l s +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l t := by
  rw [ReserveSampling.Transition_eq_Phase5Transition_of_phase5
    (L := L) (K := K) s t hs ht]
  exact Phase5Transition_agentMassAboveScaledW_pair
    (L := L) (K := K) l s t hs ht

/-- Uniform pairwise statement for the real kernel while both inputs lie in
the Phase-4/Phase-5 window. -/
theorem Transition_agentMassAboveScaledW_pair_of_phase_four_or_five
    (l : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 4 ∨ s.phase.val = 5)
    (ht : t.phase.val = 4 ∨ t.phase.val = 5) :
    Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Transition L K s t).1 +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Transition L K s t).2 =
      Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l s +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l t := by
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact Transition_agentMassAboveScaledW_pair_of_four_four
      (L := L) (K := K) l s t hs ht
  · exact Transition_agentMassAboveScaledW_pair_of_four_five
      (L := L) (K := K) l s t hs ht
  · exact Transition_agentMassAboveScaledW_pair_of_five_four
      (L := L) (K := K) l s t hs ht
  · exact Transition_agentMassAboveScaledW_pair_of_five_five
      (L := L) (K := K) l s t hs ht

/-- Uniform upper-tail monotonicity on the real Phase-3/4 seam. -/
theorem Transition_agentMassAboveScaledW_pair_le_of_phase_three_or_four
    (l : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 3 ∨ s.phase.val = 4)
    (ht : t.phase.val = 3 ∨ t.phase.val = 4) :
    Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Transition L K s t).1 +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l
          (Transition L K s t).2 ≤
      Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l s +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l t := by
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact Transition_agentMassAboveScaledW_pair_le_of_three_three
      (L := L) (K := K) l s t hs ht
  · have h := Transition_role_bias_of_three_four
      (L := L) (K := K) s t hs ht
    unfold Lemma615MassAbove.agentMassAboveScaledW
    rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · have h := Transition_role_bias_of_four_three
      (L := L) (K := K) s t hs ht
    unfold Lemma615MassAbove.agentMassAboveScaledW
    rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · have h := Transition_role_bias_of_four_four
      (L := L) (K := K) s t hs ht
    unfold Lemma615MassAbove.agentMassAboveScaledW
    rw [h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- Uniform positive signed-mass monotonicity on the real Phase-3/4 seam. -/
theorem Transition_agentPosMassQ_pair_le_of_phase_three_or_four
    (s t : AgentState L K)
    (hs : s.phase.val = 3 ∨ s.phase.val = 4)
    (ht : t.phase.val = 3 ∨ t.phase.val = 4) :
    P3DeterministicAlgebra.agentPosMassQ (L := L) (K := K)
          (Transition L K s t).1 +
        P3DeterministicAlgebra.agentPosMassQ (L := L) (K := K)
          (Transition L K s t).2 ≤
      P3DeterministicAlgebra.agentPosMassQ (L := L) (K := K) s +
        P3DeterministicAlgebra.agentPosMassQ (L := L) (K := K) t := by
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact Transition_agentPosMassQ_pair_le_of_three_three
      (L := L) (K := K) s t hs ht
  · have h := Transition_role_bias_of_three_four
      (L := L) (K := K) s t hs ht
    unfold P3DeterministicAlgebra.agentPosMassQ
    rw [h.2.1, h.2.2.2]
  · have h := Transition_role_bias_of_four_three
      (L := L) (K := K) s t hs ht
    unfold P3DeterministicAlgebra.agentPosMassQ
    rw [h.2.1, h.2.2.2]
  · have h := Transition_role_bias_of_four_four
      (L := L) (K := K) s t hs ht
    unfold P3DeterministicAlgebra.agentPosMassQ
    rw [h.2.1, h.2.2.2]

/-- Uniform negative signed-mass monotonicity on the real Phase-3/4 seam. -/
theorem Transition_agentNegMassQ_pair_le_of_phase_three_or_four
    (s t : AgentState L K)
    (hs : s.phase.val = 3 ∨ s.phase.val = 4)
    (ht : t.phase.val = 3 ∨ t.phase.val = 4) :
    P3DeterministicAlgebra.agentNegMassQ (L := L) (K := K)
          (Transition L K s t).1 +
        P3DeterministicAlgebra.agentNegMassQ (L := L) (K := K)
          (Transition L K s t).2 ≤
      P3DeterministicAlgebra.agentNegMassQ (L := L) (K := K) s +
        P3DeterministicAlgebra.agentNegMassQ (L := L) (K := K) t := by
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact Transition_agentNegMassQ_pair_le_of_three_three
      (L := L) (K := K) s t hs ht
  · have h := Transition_role_bias_of_three_four
      (L := L) (K := K) s t hs ht
    unfold P3DeterministicAlgebra.agentNegMassQ
    rw [h.2.1, h.2.2.2]
  · have h := Transition_role_bias_of_four_three
      (L := L) (K := K) s t hs ht
    unfold P3DeterministicAlgebra.agentNegMassQ
    rw [h.2.1, h.2.2.2]
  · have h := Transition_role_bias_of_four_four
      (L := L) (K := K) s t hs ht
    unfold P3DeterministicAlgebra.agentNegMassQ
    rw [h.2.1, h.2.2.2]

/-! ## Exact signed-class transport on the same seam -/

/-- Natural indicator of one exact signed Main class. -/
noncomputable def agentBiasedMainClassW
    (σ : Sign) (i : Fin (L + 1)) (a : AgentState L K) : ℕ :=
  if Phase5Convergence.biasedMainClass (L := L) (K := K) σ i a then 1 else 0

/-- The final phase-10 entry wrapper does not alter role or bias. -/
theorem finishPhase10Entry_biasedMainClass_iff
    (σ : Sign) (i : Fin (L + 1)) (before after : AgentState L K) :
    Phase5Convergence.biasedMainClass (L := L) (K := K) σ i
        (finishPhase10Entry L K before after) ↔
      Phase5Convergence.biasedMainClass (L := L) (K := K) σ i after := by
  unfold Phase5Convergence.biasedMainClass
  rw [finishPhase10Entry_role, finishPhase10Entry_bias]

/-- The exact signed-class indicator is pairwise invariant for a Phase-4
interaction under the real dispatcher. -/
theorem Transition_agentBiasedMainClassW_pair_of_four_four
    (σ : Sign) (i : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 4) (ht : t.phase.val = 4) :
    agentBiasedMainClassW (L := L) (K := K) σ i (Transition L K s t).1 +
        agentBiasedMainClassW (L := L) (K := K) σ i (Transition L K s t).2 =
      agentBiasedMainClassW (L := L) (K := K) σ i s +
        agentBiasedMainClassW (L := L) (K := K) σ i t := by
  have hepi := Phase4Convergence.phaseEpidemicUpdate_eq_self_of_phase4
    (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨4, by decide⟩ := Fin.ext hs
  have hfst := (finishPhase10Entry_biasedMainClass_iff
      (L := L) (K := K) σ i s (Phase4Transition L K s t).1).trans
    (Phase4Transition_biasedMainClass_fst_iff
      (L := L) (K := K) σ i s t hs)
  have hsnd := (finishPhase10Entry_biasedMainClass_iff
      (L := L) (K := K) σ i t (Phase4Transition L K s t).2).trans
    (Phase4Transition_biasedMainClass_snd_iff
      (L := L) (K := K) σ i s t ht)
  unfold Transition
  rw [hepi]
  simp only [hsp, agentBiasedMainClassW]
  rw [if_congr hfst rfl rfl, if_congr hsnd rfl rfl]

/-- The exact signed-class indicator is pairwise invariant for a Phase-5
interaction under the real dispatcher. -/
theorem Transition_agentBiasedMainClassW_pair_of_five_five
    (σ : Sign) (i : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 5) :
    agentBiasedMainClassW (L := L) (K := K) σ i (Transition L K s t).1 +
        agentBiasedMainClassW (L := L) (K := K) σ i (Transition L K s t).2 =
      agentBiasedMainClassW (L := L) (K := K) σ i s +
        agentBiasedMainClassW (L := L) (K := K) σ i t := by
  rw [ReserveSampling.Transition_eq_Phase5Transition_of_phase5
    (L := L) (K := K) s t hs ht]
  have hfst := Phase5Convergence.biasedMainClass_fst_iff
    (L := L) (K := K) σ i s t hs
  have hsnd := Phase5Convergence.biasedMainClass_snd_iff
    (L := L) (K := K) σ i s t ht
  simp only [agentBiasedMainClassW]
  rw [if_congr hfst rfl rfl, if_congr hsnd rfl rfl]

/-- The exact signed-class indicator is pairwise invariant for a mixed
Phase-4/Phase-5 interaction. -/
theorem Transition_agentBiasedMainClassW_pair_of_four_five
    (σ : Sign) (i : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 4) (ht : t.phase.val = 5) :
    agentBiasedMainClassW (L := L) (K := K) σ i (Transition L K s t).1 +
        agentBiasedMainClassW (L := L) (K := K) σ i (Transition L K s t).2 =
      agentBiasedMainClassW (L := L) (K := K) σ i s +
        agentBiasedMainClassW (L := L) (K := K) σ i t := by
  rw [Transition_eq_Phase5Transition_of_four_five
    (L := L) (K := K) s t hs ht]
  let s5 := phaseInit L K ⟨5, by decide⟩ {s with phase := ⟨5, by decide⟩}
  let t5 : AgentState L K := {t with phase := ⟨5, by decide⟩}
  have hs5 : s5.phase.val = 5 := by
    show (phaseInit L K ⟨5, by decide⟩ {s with phase := ⟨5, by decide⟩}).phase.val = 5
    rw [phaseInit_five_phase (L := L) (K := K) _ ⟨5, by decide⟩ (by decide)]
  have ht5 : t5.phase.val = 5 := by simp [t5]
  have hs5class :
      Phase5Convergence.biasedMainClass (L := L) (K := K) σ i s5 ↔
        Phase5Convergence.biasedMainClass (L := L) (K := K) σ i s := by
    dsimp [s5]
    exact (phaseInit_five_biasedMainClass_iff
      (L := L) (K := K) σ i {s with phase := ⟨5, by decide⟩}).trans (by
        unfold Phase5Convergence.biasedMainClass
        simp)
  have ht5class :
      Phase5Convergence.biasedMainClass (L := L) (K := K) σ i t5 ↔
        Phase5Convergence.biasedMainClass (L := L) (K := K) σ i t := by
    simp [t5, Phase5Convergence.biasedMainClass]
  have hfst := (Phase5Convergence.biasedMainClass_fst_iff
      (L := L) (K := K) σ i s5 t5 hs5).trans hs5class
  have hsnd := (Phase5Convergence.biasedMainClass_snd_iff
      (L := L) (K := K) σ i s5 t5 ht5).trans ht5class
  simp only [s5, t5, agentBiasedMainClassW] at hfst hsnd ⊢
  rw [if_congr hfst rfl rfl, if_congr hsnd rfl rfl]

/-- Symmetric mixed Phase-5/Phase-4 exact-class transport. -/
theorem Transition_agentBiasedMainClassW_pair_of_five_four
    (σ : Sign) (i : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 4) :
    agentBiasedMainClassW (L := L) (K := K) σ i (Transition L K s t).1 +
        agentBiasedMainClassW (L := L) (K := K) σ i (Transition L K s t).2 =
      agentBiasedMainClassW (L := L) (K := K) σ i s +
        agentBiasedMainClassW (L := L) (K := K) σ i t := by
  rw [Transition_eq_Phase5Transition_of_five_four
    (L := L) (K := K) s t hs ht]
  let s5 : AgentState L K := {s with phase := ⟨5, by decide⟩}
  let t5 := phaseInit L K ⟨5, by decide⟩ {t with phase := ⟨5, by decide⟩}
  have hs5 : s5.phase.val = 5 := by simp [s5]
  have ht5 : t5.phase.val = 5 := by
    show (phaseInit L K ⟨5, by decide⟩ {t with phase := ⟨5, by decide⟩}).phase.val = 5
    rw [phaseInit_five_phase (L := L) (K := K) _ ⟨5, by decide⟩ (by decide)]
  have hs5class :
      Phase5Convergence.biasedMainClass (L := L) (K := K) σ i s5 ↔
        Phase5Convergence.biasedMainClass (L := L) (K := K) σ i s := by
    simp [s5, Phase5Convergence.biasedMainClass]
  have ht5class :
      Phase5Convergence.biasedMainClass (L := L) (K := K) σ i t5 ↔
        Phase5Convergence.biasedMainClass (L := L) (K := K) σ i t := by
    dsimp [t5]
    exact (phaseInit_five_biasedMainClass_iff
      (L := L) (K := K) σ i {t with phase := ⟨5, by decide⟩}).trans (by
        unfold Phase5Convergence.biasedMainClass
        simp)
  have hfst := (Phase5Convergence.biasedMainClass_fst_iff
      (L := L) (K := K) σ i s5 t5 hs5).trans hs5class
  have hsnd := (Phase5Convergence.biasedMainClass_snd_iff
      (L := L) (K := K) σ i s5 t5 ht5).trans ht5class
  simp only [s5, t5, agentBiasedMainClassW] at hfst hsnd ⊢
  rw [if_congr hfst rfl rfl, if_congr hsnd rfl rfl]

/-- Uniform exact signed-class transport for all four input combinations in
the Phase-4/Phase-5 window. -/
theorem Transition_agentBiasedMainClassW_pair_of_phase_four_or_five
    (σ : Sign) (i : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 4 ∨ s.phase.val = 5)
    (ht : t.phase.val = 4 ∨ t.phase.val = 5) :
    agentBiasedMainClassW (L := L) (K := K) σ i (Transition L K s t).1 +
        agentBiasedMainClassW (L := L) (K := K) σ i (Transition L K s t).2 =
      agentBiasedMainClassW (L := L) (K := K) σ i s +
        agentBiasedMainClassW (L := L) (K := K) σ i t := by
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact Transition_agentBiasedMainClassW_pair_of_four_four
      (L := L) (K := K) σ i s t hs ht
  · exact Transition_agentBiasedMainClassW_pair_of_four_five
      (L := L) (K := K) σ i s t hs ht
  · exact Transition_agentBiasedMainClassW_pair_of_five_four
      (L := L) (K := K) σ i s t hs ht
  · exact Transition_agentBiasedMainClassW_pair_of_five_five
      (L := L) (K := K) σ i s t hs ht

/-! ## Configuration-level Phase-3/Phase-4 seam transport -/

/-- One protocol step preserves any additive observable pair inequality. -/
theorem stepRel_sumOf_le_of_pair
    {Λ M : Type*} [Fintype Λ] [DecidableEq Λ]
    [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    {P : Protocol Λ} {f : Λ → M} {c d : Config Λ}
    (hδ : ∀ r₁ r₂, let p := P.δ r₁ r₂;
      f p.1 + f p.2 ≤ f r₁ + f r₂)
    (hstep : P.StepRel c d) :
    d.sumOf f ≤ c.sumOf f := by
  rcases hstep with ⟨r₁, r₂, happ, hd⟩
  dsimp at hd
  rcases hpair : P.δ r₁ r₂ with ⟨p₁, p₂⟩
  subst d
  have hδ' : f p₁ + f p₂ ≤ f r₁ + f r₂ := by
    simpa [hpair] using hδ r₁ r₂
  dsimp [Config.sumOf]
  change ((c - ({r₁, r₂} : Multiset Λ) +
      ({(P.δ r₁ r₂).1, (P.δ r₁ r₂).2} : Multiset Λ)).map f).sum ≤
    (c.map f).sum
  rw [hpair]
  calc
    ((c - ({r₁, r₂} : Multiset Λ) + ({p₁, p₂} : Multiset Λ)).map f).sum
        = ((c - ({r₁, r₂} : Multiset Λ)).map f).sum +
            (({p₁, p₂} : Multiset Λ).map f).sum := by
          rw [Multiset.map_add, Multiset.sum_add]
    _ = ((c - ({r₁, r₂} : Multiset Λ)).map f).sum +
          (f p₁ + f p₂) := by simp
    _ ≤ ((c - ({r₁, r₂} : Multiset Λ)).map f).sum +
          (f r₁ + f r₂) := add_le_add_right hδ' _
    _ = ((c - ({r₁, r₂} : Multiset Λ)).map f).sum +
          (({r₁, r₂} : Multiset Λ).map f).sum := by simp
    _ = (((c - ({r₁, r₂} : Multiset Λ)) +
          ({r₁, r₂} : Multiset Λ)).map f).sum := by
          rw [Multiset.map_add, Multiset.sum_add]
    _ = (c.map f).sum := by rw [Multiset.sub_add_cancel happ]

/-- Reflexive-transitive closure of the preceding pair inequality. -/
theorem reachable_sumOf_le_of_pair
    {Λ M : Type*} [Fintype Λ] [DecidableEq Λ]
    [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    {P : Protocol Λ} {f : Λ → M} {c d : Config Λ}
    (hδ : ∀ r₁ r₂, let p := P.δ r₁ r₂;
      f p.1 + f p.2 ≤ f r₁ + f r₂)
    (hreach : P.Reachable c d) :
    d.sumOf f ≤ c.sumOf f := by
  induction hreach with
  | refl => exact le_rfl
  | tail _ hstep ih =>
      exact (stepRel_sumOf_le_of_pair hδ hstep).trans ih

/-- State predicate for the deterministic Phase-3/Phase-4 seam window. -/
def InPhase34 (a : AgentState L K) : Prop :=
  a.phase.val = 3 ∨ a.phase.val = 4

/-- Guarded copy of the real kernel on Phase-3/4 pairs. -/
noncomputable def Phase34Protocol (L K : ℕ) : Protocol (AgentState L K) where
  δ := fun s t =>
    if InPhase34 s ∧ InPhase34 t then Transition L K s t else (s, t)

/-- Pairwise scaled-tail monotonicity for the guarded Phase-3/4 kernel. -/
theorem Phase34Protocol_agentMassAboveScaledW_pair_le
    (l : ℕ) (s t : AgentState L K) :
    let p := (Phase34Protocol L K).δ s t
    Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l p.1 +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l p.2 ≤
      Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l s +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l t := by
  by_cases h34 : InPhase34 s ∧ InPhase34 t
  · simpa [Phase34Protocol, h34] using
      Transition_agentMassAboveScaledW_pair_le_of_phase_three_or_four
        (L := L) (K := K) l s t h34.1 h34.2
  · simp [Phase34Protocol, h34]

/-- Positive signed-mass monotonicity for the guarded Phase-3/4 kernel. -/
theorem Phase34Protocol_agentPosMassQ_pair_le
    (s t : AgentState L K) :
    let p := (Phase34Protocol L K).δ s t
    P3DeterministicAlgebra.agentPosMassQ (L := L) (K := K) p.1 +
        P3DeterministicAlgebra.agentPosMassQ (L := L) (K := K) p.2 ≤
      P3DeterministicAlgebra.agentPosMassQ (L := L) (K := K) s +
        P3DeterministicAlgebra.agentPosMassQ (L := L) (K := K) t := by
  by_cases h34 : InPhase34 s ∧ InPhase34 t
  · simpa [Phase34Protocol, h34] using
      Transition_agentPosMassQ_pair_le_of_phase_three_or_four
        (L := L) (K := K) s t h34.1 h34.2
  · simp [Phase34Protocol, h34]

/-- Negative signed-mass monotonicity for the guarded Phase-3/4 kernel. -/
theorem Phase34Protocol_agentNegMassQ_pair_le
    (s t : AgentState L K) :
    let p := (Phase34Protocol L K).δ s t
    P3DeterministicAlgebra.agentNegMassQ (L := L) (K := K) p.1 +
        P3DeterministicAlgebra.agentNegMassQ (L := L) (K := K) p.2 ≤
      P3DeterministicAlgebra.agentNegMassQ (L := L) (K := K) s +
        P3DeterministicAlgebra.agentNegMassQ (L := L) (K := K) t := by
  by_cases h34 : InPhase34 s ∧ InPhase34 t
  · simpa [Phase34Protocol, h34] using
      Transition_agentNegMassQ_pair_le_of_phase_three_or_four
        (L := L) (K := K) s t h34.1 h34.2
  · simp [Phase34Protocol, h34]

/-- Every state of a configuration lies in Phase 3 or Phase 4. -/
def AllPhase34 (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, InPhase34 a

/-- A real step from an all-Phase-3/4 source is a guarded seam step. -/
theorem phase34Protocol_stepRel_of_real_step
    {c d : Config (AgentState L K)}
    (hc : AllPhase34 c)
    (hstep : (NonuniformMajority L K).StepRel c d) :
    (Phase34Protocol L K).StepRel c d := by
  rcases hstep with ⟨r₁, r₂, happ, hd⟩
  have hr₁ : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂ : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  refine ⟨r₁, r₂, happ, ?_⟩
  simpa [Phase34Protocol, hc r₁ hr₁, hc r₂ hr₂,
    NonuniformMajority] using hd

/-- Real reachability whose every source stays in the Phase-3/4 seam.  The
last step may land in Phase 5. -/
def ReachableThroughPhase34
    (c d : Config (AgentState L K)) : Prop :=
  Relation.ReflTransGen
    (fun x y => (NonuniformMajority L K).StepRel x y ∧ AllPhase34 x) c d

/-- Convert the real seam route to guarded-protocol reachability. -/
theorem phase34Reachable_of_reachableThroughPhase34
    {c d : Config (AgentState L K)}
    (hreach : ReachableThroughPhase34 (L := L) (K := K) c d) :
    (Phase34Protocol L K).Reachable c d := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih
        (phase34Protocol_stepRel_of_real_step
          (L := L) (K := K) hstep.2 hstep.1)

/-- Scaled upper-tail mass is nonincreasing on a real Phase-3/4 route. -/
theorem massAboveScaled_le_of_reachableThroughPhase34
    (l : ℕ) (c d : Config (AgentState L K))
    (hreach : ReachableThroughPhase34 (L := L) (K := K) c d) :
    Lemma615MassAbove.massAboveScaled (L := L) (K := K) l d ≤
      Lemma615MassAbove.massAboveScaled (L := L) (K := K) l c := by
  unfold Lemma615MassAbove.massAboveScaled
  exact reachable_sumOf_le_of_pair
    (Phase34Protocol_agentMassAboveScaledW_pair_le
      (L := L) (K := K) l)
    (phase34Reachable_of_reachableThroughPhase34
      (L := L) (K := K) hreach)

/-- Positive signed mass is nonincreasing on a real Phase-3/4 route. -/
theorem betaPlusQ_le_of_reachableThroughPhase34
    (c d : Config (AgentState L K))
    (hreach : ReachableThroughPhase34 (L := L) (K := K) c d) :
    P3DeterministicAlgebra.betaPlusQ (L := L) (K := K) d ≤
      P3DeterministicAlgebra.betaPlusQ (L := L) (K := K) c := by
  unfold P3DeterministicAlgebra.betaPlusQ
  exact reachable_sumOf_le_of_pair
    (Phase34Protocol_agentPosMassQ_pair_le (L := L) (K := K))
    (phase34Reachable_of_reachableThroughPhase34
      (L := L) (K := K) hreach)

/-- Negative signed mass is nonincreasing on a real Phase-3/4 route. -/
theorem betaMinusQ_le_of_reachableThroughPhase34
    (c d : Config (AgentState L K))
    (hreach : ReachableThroughPhase34 (L := L) (K := K) c d) :
    P3DeterministicAlgebra.betaMinusQ (L := L) (K := K) d ≤
      P3DeterministicAlgebra.betaMinusQ (L := L) (K := K) c := by
  unfold P3DeterministicAlgebra.betaMinusQ
  exact reachable_sumOf_le_of_pair
    (Phase34Protocol_agentNegMassQ_pair_le (L := L) (K := K))
    (phase34Reachable_of_reachableThroughPhase34
      (L := L) (K := K) hreach)

/-- The majority-sign minority mass is nonincreasing on the same seam. -/
theorem minorityMass_le_of_reachableThroughPhase34
    (σ : Sign) (c d : Config (AgentState L K))
    (hreach : ReachableThroughPhase34 (L := L) (K := K) c d) :
    Phase3Post3.minorityMass (L := L) (K := K) σ d ≤
      Phase3Post3.minorityMass (L := L) (K := K) σ c := by
  cases σ with
  | neg =>
      change
        (P3DeterministicAlgebra.betaPlusQ (L := L) (K := K) d : ℝ) ≤
          (P3DeterministicAlgebra.betaPlusQ (L := L) (K := K) c : ℝ)
      exact_mod_cast betaPlusQ_le_of_reachableThroughPhase34
        (L := L) (K := K) c d hreach
  | pos =>
      change
        (P3DeterministicAlgebra.betaMinusQ (L := L) (K := K) d : ℝ) ≤
          (P3DeterministicAlgebra.betaMinusQ (L := L) (K := K) c : ℝ)
      exact_mod_cast betaMinusQ_le_of_reachableThroughPhase34
        (L := L) (K := K) c d hreach

/-! ## Configuration-level Phase-4/Phase-5 transport -/

/-- State predicate for the deterministic Phase-4/Phase-5 transport window. -/
def InPhase45 (a : AgentState L K) : Prop :=
  a.phase.val = 4 ∨ a.phase.val = 5

/-- A guarded copy of the real kernel.  It executes `Transition` exactly on
Phase-4/Phase-5 pairs and is the identity elsewhere.  This lets the generic
additive-invariant infrastructure express a route that stops when Phase 6 is
first reached. -/
noncomputable def Phase45Protocol (L K : ℕ) : Protocol (AgentState L K) where
  δ := fun s t =>
    if InPhase45 s ∧ InPhase45 t then Transition L K s t else (s, t)

/-- The guarded Phase-4/Phase-5 kernel preserves the upper-tail observable on
every pair, including its identity branch. -/
theorem Phase45Protocol_agentMassAboveScaledW_pair
    (l : ℕ) (s t : AgentState L K) :
    let p := (Phase45Protocol L K).δ s t
    Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l p.1 +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l p.2 =
      Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l s +
        Lemma615MassAbove.agentMassAboveScaledW (L := L) (K := K) l t := by
  by_cases h45 : InPhase45 s ∧ InPhase45 t
  · simpa [Phase45Protocol, h45] using
      Transition_agentMassAboveScaledW_pair_of_phase_four_or_five
        (L := L) (K := K) l s t h45.1 h45.2
  · simp [Phase45Protocol, h45]

/-- The guarded Phase-4/5 protocol also preserves each exact signed Main
class, not merely the aggregate upper-tail mass. -/
theorem Phase45Protocol_agentBiasedMainClassW_pair
    (σ : Sign) (i : Fin (L + 1)) (s t : AgentState L K) :
    let p := (Phase45Protocol L K).δ s t
    agentBiasedMainClassW (L := L) (K := K) σ i p.1 +
        agentBiasedMainClassW (L := L) (K := K) σ i p.2 =
      agentBiasedMainClassW (L := L) (K := K) σ i s +
        agentBiasedMainClassW (L := L) (K := K) σ i t := by
  by_cases h45 : InPhase45 s ∧ InPhase45 t
  · simpa [Phase45Protocol, h45] using
      Transition_agentBiasedMainClassW_pair_of_phase_four_or_five
        (L := L) (K := K) σ i s t h45.1 h45.2
  · simp [Phase45Protocol, h45]

/-- Scaled upper-tail mass is transported exactly along any sequence of real
Phase-4/Phase-5 pair updates, up to and including the first update whose
outputs enter Phase 6. -/
theorem massAboveScaled_eq_of_phase45Reachable
    (l : ℕ) (c d : Config (AgentState L K))
    (hreach : (Phase45Protocol L K).Reachable c d) :
    Lemma615MassAbove.massAboveScaled (L := L) (K := K) l d =
      Lemma615MassAbove.massAboveScaled (L := L) (K := K) l c := by
  unfold Lemma615MassAbove.massAboveScaled
  exact Protocol.reachable_sumOf_eq
    (Phase45Protocol_agentMassAboveScaledW_pair
      (L := L) (K := K) l) hreach

/-- `biasedMainClassU` is the configuration sum of its natural indicator. -/
theorem biasedMainClassU_eq_sumOf
    (σ : Sign) (i : Fin (L + 1)) (c : Config (AgentState L K)) :
    Phase5Convergence.biasedMainClassU (L := L) (K := K) σ i c =
      c.sumOf (agentBiasedMainClassW (L := L) (K := K) σ i) := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [Phase5Convergence.biasedMainClassU, Config.sumOf]
  | @cons a c ih =>
      unfold Phase5Convergence.biasedMainClassU at ih ⊢
      unfold Config.sumOf at ih ⊢
      rw [Multiset.countP_cons, Multiset.map_cons, Multiset.sum_cons, ih]
      simp [agentBiasedMainClassW, Nat.add_comm]

/-- Each exact signed Main class count is static along guarded Phase-4/5
reachability. -/
theorem biasedMainClassU_eq_of_phase45Reachable
    (σ : Sign) (i : Fin (L + 1)) (c d : Config (AgentState L K))
    (hreach : (Phase45Protocol L K).Reachable c d) :
    Phase5Convergence.biasedMainClassU (L := L) (K := K) σ i d =
      Phase5Convergence.biasedMainClassU (L := L) (K := K) σ i c := by
  rw [biasedMainClassU_eq_sumOf, biasedMainClassU_eq_sumOf]
  exact Protocol.reachable_sumOf_eq
    (Phase45Protocol_agentBiasedMainClassW_pair
      (L := L) (K := K) σ i) hreach

/-- Every state of a configuration lies in Phase 4 or Phase 5. -/
def AllPhase45 (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, InPhase45 a

/-- A real protocol step from an all-Phase-4/5 configuration is also a step of
the guarded transport protocol. -/
theorem phase45Protocol_stepRel_of_real_step
    {c d : Config (AgentState L K)}
    (hc : AllPhase45 c)
    (hstep : (NonuniformMajority L K).StepRel c d) :
    (Phase45Protocol L K).StepRel c d := by
  rcases hstep with ⟨r₁, r₂, happ, hd⟩
  have hr₁ : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂ : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  refine ⟨r₁, r₂, happ, ?_⟩
  simpa [Phase45Protocol, hc r₁ hr₁, hc r₂ hr₂,
    NonuniformMajority] using hd

/-- Real reachability whose every source configuration stays in the
Phase-4/Phase-5 window.  The last step may land in Phase 6. -/
def ReachableThroughPhase45
    (c d : Config (AgentState L K)) : Prop :=
  Relation.ReflTransGen
    (fun x y => (NonuniformMajority L K).StepRel x y ∧ AllPhase45 x) c d

/-- The real-kernel formulation of deterministic Phase-4/5 mass transport. -/
theorem massAboveScaled_eq_of_reachableThroughPhase45
    (l : ℕ) (c d : Config (AgentState L K))
    (hreach : ReachableThroughPhase45 (L := L) (K := K) c d) :
    Lemma615MassAbove.massAboveScaled (L := L) (K := K) l d =
      Lemma615MassAbove.massAboveScaled (L := L) (K := K) l c := by
  apply massAboveScaled_eq_of_phase45Reachable (L := L) (K := K) l c d
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih
        (phase45Protocol_stepRel_of_real_step
          (L := L) (K := K) hyz.2 hyz.1)

/-- Exact signed Main classes are static on the same real Phase-4/5 route. -/
theorem biasedMainClassU_eq_of_reachableThroughPhase45
    (σ : Sign) (i : Fin (L + 1)) (c d : Config (AgentState L K))
    (hreach : ReachableThroughPhase45 (L := L) (K := K) c d) :
    Phase5Convergence.biasedMainClassU (L := L) (K := K) σ i d =
      Phase5Convergence.biasedMainClassU (L := L) (K := K) σ i c := by
  apply biasedMainClassU_eq_of_phase45Reachable
    (L := L) (K := K) σ i c d
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih
        (phase45Protocol_stepRel_of_real_step
          (L := L) (K := K) hyz.2 hyz.1)

/-- Real-valued `muAbove` is consequently static on the same route. -/
theorem muAbove_eq_of_reachableThroughPhase45
    (l : ℕ) (c d : Config (AgentState L K))
    (hreach : ReachableThroughPhase45 (L := L) (K := K) c d) :
    Lemma615MassAbove.muAbove (L := L) (K := K) l d =
      Lemma615MassAbove.muAbove (L := L) (K := K) l c := by
  unfold Lemma615MassAbove.muAbove
  rw [massAboveScaled_eq_of_reachableThroughPhase45
    (L := L) (K := K) l c d hreach]

/-! ## Reading the Phase-3 `muAbove` certificate as an integer-mass bound -/

/-- Cancelling the strictly positive dyadic scaling factor converts a bound on
`muAbove` into the corresponding bound on the cast scaled mass. -/
theorem massAboveScaled_cast_le_of_muAbove_le
    (l : ℕ) (c : Config (AgentState L K)) (B : ℝ)
    (hmu : Lemma615MassAbove.muAbove (L := L) (K := K) l c ≤
      B * (2 : ℝ) ^ (-(l : ℤ))) :
    (Lemma615MassAbove.massAboveScaled (L := L) (K := K) l c : ℝ) ≤ B := by
  unfold Lemma615MassAbove.muAbove at hmu
  have hpow : 0 < (2 : ℝ) ^ (-(l : ℤ)) := zpow_pos (by norm_num) _
  nlinarith

/-- The exact `.002 M` scaled upper-tail readout contained in
`Snapshot617`. -/
theorem Snapshot617.massAboveScaled_cast_le
    {n l : ℕ} {M g₀ : ℝ} {σ : Sign}
    {c : Config (AgentState L K)}
    (hs : Phase3Post3.Snapshot617
      (L := L) (K := K) n l M g₀ σ c) :
    (Lemma615MassAbove.massAboveScaled (L := L) (K := K) l c : ℝ) ≤
      (1 / 500 : ℝ) * M := by
  apply massAboveScaled_cast_le_of_muAbove_le
    (L := L) (K := K) l c ((1 / 500 : ℝ) * M)
  simpa [mul_assoc] using hs.muAbove_bound

/-- Integer rounding form of the snapshot tail bound.  Supplying any natural
`Btail` strictly above the real `.002 M` cap yields the exact natural-number
bound consumed by the fuel accounting. -/
theorem Snapshot617.massAboveScaled_le_natCap
    {n l Btail : ℕ} {M g₀ : ℝ} {σ : Sign}
    {c : Config (AgentState L K)}
    (hs : Phase3Post3.Snapshot617
      (L := L) (K := K) n l M g₀ σ c)
    (hround : (1 / 500 : ℝ) * M < (Btail + 1 : ℕ)) :
    Lemma615MassAbove.massAboveScaled (L := L) (K := K) l c ≤ Btail := by
  have hcast := Snapshot617.massAboveScaled_cast_le (hs := hs)
  have hlt :
      (Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) l c : ℝ) < (Btail + 1 : ℕ) :=
    lt_of_le_of_lt hcast hround
  have hnat : Lemma615MassAbove.massAboveScaled
      (L := L) (K := K) l c < Btail + 1 := by
    exact_mod_cast hlt
  omega

/-- Transport the Phase-3 scaled-tail estimate through an explicit seam and
then through the real Phase-4/5 kernel.  The seam nonincrease is kept visible:
it is the exact remaining bridge from the Phase-3 snapshot endpoint to the
first all-Phase-4 configuration. -/
theorem Snapshot617.massAboveScaled_cast_le_after_phase45
    {n l : ℕ} {M g₀ : ℝ} {σ : Sign}
    {c3 c4 d : Config (AgentState L K)}
    (hs : Phase3Post3.Snapshot617
      (L := L) (K := K) n l M g₀ σ c3)
    (hseam : Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) l c4 ≤
      Lemma615MassAbove.massAboveScaled (L := L) (K := K) l c3)
    (hreach : ReachableThroughPhase45 (L := L) (K := K) c4 d) :
    (Lemma615MassAbove.massAboveScaled (L := L) (K := K) l d : ℝ) ≤
      (1 / 500 : ℝ) * M := by
  rw [massAboveScaled_eq_of_reachableThroughPhase45
    (L := L) (K := K) l c4 d hreach]
  have hseamR :
      (Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) l c4 : ℝ) ≤
      (Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) l c3 : ℝ) := by
    exact_mod_cast hseam
  exact hseamR.trans (Snapshot617.massAboveScaled_cast_le (hs := hs))

/-- Integer-cap transport version of
`Snapshot617.massAboveScaled_cast_le_after_phase45`. -/
theorem Snapshot617.massAboveScaled_le_natCap_after_phase45
    {n l Btail : ℕ} {M g₀ : ℝ} {σ : Sign}
    {c3 c4 d : Config (AgentState L K)}
    (hs : Phase3Post3.Snapshot617
      (L := L) (K := K) n l M g₀ σ c3)
    (hseam : Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) l c4 ≤
      Lemma615MassAbove.massAboveScaled (L := L) (K := K) l c3)
    (hreach : ReachableThroughPhase45 (L := L) (K := K) c4 d)
    (hround : (1 / 500 : ℝ) * M < (Btail + 1 : ℕ)) :
    Lemma615MassAbove.massAboveScaled (L := L) (K := K) l d ≤ Btail := by
  rw [massAboveScaled_eq_of_reachableThroughPhase45
    (L := L) (K := K) l c4 d hreach]
  exact hseam.trans
    (Snapshot617.massAboveScaled_le_natCap (hs := hs) hround)

/-- The same tail transport with the Phase-3/4 seam inequality discharged by
an actual real-kernel route, followed by the exact Phase-4/5 transport. -/
theorem Snapshot617.massAboveScaled_cast_le_after_phase34_phase45
    {n l : ℕ} {M g₀ : ℝ} {σ : Sign}
    {c3 c4 d : Config (AgentState L K)}
    (hs : Phase3Post3.Snapshot617
      (L := L) (K := K) n l M g₀ σ c3)
    (h34 : ReachableThroughPhase34 (L := L) (K := K) c3 c4)
    (h45 : ReachableThroughPhase45 (L := L) (K := K) c4 d) :
    (Lemma615MassAbove.massAboveScaled (L := L) (K := K) l d : ℝ) ≤
      (1 / 500 : ℝ) * M := by
  rw [massAboveScaled_eq_of_reachableThroughPhase45
    (L := L) (K := K) l c4 d h45]
  have h34R :
      (Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) l c4 : ℝ) ≤
      (Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) l c3 : ℝ) := by
    exact_mod_cast massAboveScaled_le_of_reachableThroughPhase34
      (L := L) (K := K) l c3 c4 h34
  exact h34R.trans (Snapshot617.massAboveScaled_cast_le (hs := hs))

/-- Natural-cap version with both deterministic routes explicit and no seam
inequality parameter. -/
theorem Snapshot617.massAboveScaled_le_natCap_after_phase34_phase45
    {n l Btail : ℕ} {M g₀ : ℝ} {σ : Sign}
    {c3 c4 d : Config (AgentState L K)}
    (hs : Phase3Post3.Snapshot617
      (L := L) (K := K) n l M g₀ σ c3)
    (h34 : ReachableThroughPhase34 (L := L) (K := K) c3 c4)
    (h45 : ReachableThroughPhase45 (L := L) (K := K) c4 d)
    (hround : (1 / 500 : ℝ) * M < (Btail + 1 : ℕ)) :
    Lemma615MassAbove.massAboveScaled (L := L) (K := K) l d ≤ Btail := by
  rw [massAboveScaled_eq_of_reachableThroughPhase45
    (L := L) (K := K) l c4 d h45]
  exact (massAboveScaled_le_of_reachableThroughPhase34
    (L := L) (K := K) l c3 c4 h34).trans
      (Snapshot617.massAboveScaled_le_natCap (hs := hs) hround)

/-! ## Adjacent-level accounting -/

/-- The rational Phase-3 dyadic weight and the real `zpow` notation used by
`Snapshot617` are the same quantity. -/
theorem cast_weightQ_eq_zpow (i : Fin (L + 1)) :
    ((P3DeterministicAlgebra.weightQ (L := L) i : ℚ) : ℝ) =
      (2 : ℝ) ^ (-(i.val : ℤ)) := by
  simp [P3DeterministicAlgebra.weightQ, zpow_neg, div_eq_mul_inv]

/-- One exact signed Main class contributes its class indicator times the
dyadic weight to the corresponding signed mass. -/
theorem biasedMainClass_indicator_mul_weight_le_agentSignMass
    (σ : Sign) (i : Fin (L + 1)) (a : AgentState L K) :
    ((if Phase5Convergence.biasedMainClass
          (L := L) (K := K) σ i a then 1 else 0 : ℕ) : ℝ) *
        (2 : ℝ) ^ (-(i.val : ℤ)) ≤
      match σ with
      | .pos => (P3DeterministicAlgebra.agentPosMassQ
          (L := L) (K := K) a : ℝ)
      | .neg => (P3DeterministicAlgebra.agentNegMassQ
          (L := L) (K := K) a : ℝ) := by
  cases σ with
  | neg =>
      change
        ((if Phase5Convergence.biasedMainClass
              (L := L) (K := K) .neg i a then 1 else 0 : ℕ) : ℝ) *
            (2 : ℝ) ^ (-(i.val : ℤ)) ≤
          (P3DeterministicAlgebra.agentNegMassQ
            (L := L) (K := K) a : ℝ)
      by_cases hc : Phase5Convergence.biasedMainClass
        (L := L) (K := K) .neg i a
      · rcases hc with ⟨hr, hb⟩
        simp [Phase5Convergence.biasedMainClass,
          hr, hb,
          P3DeterministicAlgebra.agentNegMassQ,
          P3DeterministicAlgebra.biasNegMassQ, cast_weightQ_eq_zpow]
      · cases hb : a.bias with
        | zero => simp [hc, hb, P3DeterministicAlgebra.agentNegMassQ,
            P3DeterministicAlgebra.biasNegMassQ]
        | dyadic τ j =>
            cases τ with
            | neg =>
                have hw : (0 : ℝ) ≤
                    (P3DeterministicAlgebra.weightQ (L := L) j : ℝ) := by
                  exact_mod_cast P3DeterministicAlgebra.weightQ_nonneg
                    (L := L) j
                simpa [hc, hb, P3DeterministicAlgebra.agentNegMassQ,
                  P3DeterministicAlgebra.biasNegMassQ] using hw
            | pos =>
                simp [hc, hb, P3DeterministicAlgebra.agentNegMassQ,
                  P3DeterministicAlgebra.biasNegMassQ]
  | pos =>
      change
        ((if Phase5Convergence.biasedMainClass
              (L := L) (K := K) .pos i a then 1 else 0 : ℕ) : ℝ) *
            (2 : ℝ) ^ (-(i.val : ℤ)) ≤
          (P3DeterministicAlgebra.agentPosMassQ
            (L := L) (K := K) a : ℝ)
      by_cases hc : Phase5Convergence.biasedMainClass
        (L := L) (K := K) .pos i a
      · rcases hc with ⟨hr, hb⟩
        simp [Phase5Convergence.biasedMainClass,
          hr, hb,
          P3DeterministicAlgebra.agentPosMassQ,
          P3DeterministicAlgebra.biasPosMassQ, cast_weightQ_eq_zpow]
      · cases hb : a.bias with
        | zero => simp [hc, hb, P3DeterministicAlgebra.agentPosMassQ,
            P3DeterministicAlgebra.biasPosMassQ]
        | dyadic τ j =>
            cases τ with
            | neg =>
                simp [hc, hb, P3DeterministicAlgebra.agentPosMassQ,
                  P3DeterministicAlgebra.biasPosMassQ]
            | pos =>
                have hw : (0 : ℝ) ≤
                    (P3DeterministicAlgebra.weightQ (L := L) j : ℝ) := by
                  exact_mod_cast P3DeterministicAlgebra.weightQ_nonneg
                    (L := L) j
                simpa [hc, hb, P3DeterministicAlgebra.agentPosMassQ,
                  P3DeterministicAlgebra.biasPosMassQ] using hw

/-- Configuration-level class-mass lower bound: the signed mass contains at
least the exact class count times its dyadic weight. -/
theorem biasedMainClassU_mul_weight_le_signedMass
    (σ : Sign) (i : Fin (L + 1)) (c : Config (AgentState L K)) :
    (Phase5Convergence.biasedMainClassU
        (L := L) (K := K) σ i c : ℝ) *
        (2 : ℝ) ^ (-(i.val : ℤ)) ≤
      match σ with
      | .pos => Phase3Post3.betaPlus (L := L) (K := K) c
      | .neg => Phase3Post3.betaMinus (L := L) (K := K) c := by
  cases σ with
  | neg =>
      induction c using Multiset.induction_on with
      | empty =>
          simp [Phase5Convergence.biasedMainClassU,
            Phase3Post3.betaMinus, P3DeterministicAlgebra.betaMinusQ,
            Config.sumOf]
      | @cons a c ih =>
          have ha := biasedMainClass_indicator_mul_weight_le_agentSignMass
            (L := L) (K := K) .neg i a
          simp only [Phase5Convergence.biasedMainClassU,
            Multiset.countP_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
            Nat.cast_zero, Phase3Post3.betaMinus,
            P3DeterministicAlgebra.betaMinusQ, Config.sumOf,
            Multiset.map_cons, Multiset.sum_cons, Rat.cast_add] at ih ⊢
          change
            ((if Phase5Convergence.biasedMainClass
                (L := L) (K := K) .neg i a then 1 else 0 : ℕ) : ℝ) *
                (2 : ℝ) ^ (-(i.val : ℤ)) ≤
              (P3DeterministicAlgebra.agentNegMassQ
                (L := L) (K := K) a : ℝ) at ha
          simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at ha
          rw [add_mul]
          linarith

  | pos =>
      induction c using Multiset.induction_on with
      | empty =>
          simp [Phase5Convergence.biasedMainClassU,
            Phase3Post3.betaPlus, P3DeterministicAlgebra.betaPlusQ,
            Config.sumOf]
      | @cons a c ih =>
          have ha := biasedMainClass_indicator_mul_weight_le_agentSignMass
            (L := L) (K := K) .pos i a
          simp only [Phase5Convergence.biasedMainClassU,
            Multiset.countP_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
            Nat.cast_zero, Phase3Post3.betaPlus,
            P3DeterministicAlgebra.betaPlusQ, Config.sumOf,
            Multiset.map_cons, Multiset.sum_cons, Rat.cast_add] at ih ⊢
          change
            ((if Phase5Convergence.biasedMainClass
                (L := L) (K := K) .pos i a then 1 else 0 : ℕ) : ℝ) *
                (2 : ℝ) ^ (-(i.val : ℤ)) ≤
              (P3DeterministicAlgebra.agentPosMassQ
                (L := L) (K := K) a : ℝ) at ha
          simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at ha
          rw [add_mul]
          linarith

/-- Majority-sign rendering of the previous result: the opposite-sign exact
class is bounded by `minorityMass`. -/
theorem minorityClassU_mul_weight_le_minorityMass
    (σ : Sign) (i : Fin (L + 1)) (c : Config (AgentState L K)) :
    (Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) i c : ℝ) *
        (2 : ℝ) ^ (-(i.val : ℤ)) ≤
      Phase3Post3.minorityMass (L := L) (K := K) σ c := by
  cases σ with
  | neg =>
      simpa [Phase3Post3.minoritySignOfMajority,
        Phase3Post3.minorityMass] using
        (biasedMainClassU_mul_weight_le_signedMass
          (L := L) (K := K) .pos i c)
  | pos =>
      simpa [Phase3Post3.minoritySignOfMajority,
        Phase3Post3.minorityMass] using
        (biasedMainClassU_mul_weight_le_signedMass
          (L := L) (K := K) .neg i c)

/-- `Snapshot617`'s `.004 M · 2⁻ˡ` minority-mass bound implies the exact
minority-sign class count at level `l` is at most `.004 M`. -/
theorem Snapshot617.minorityClassU_cast_le
    {n l : ℕ} {M g₀ : ℝ} {σ : Sign}
    {c : Config (AgentState L K)}
    (hs : Phase3Post3.Snapshot617
      (L := L) (K := K) n l M g₀ σ c)
    (hl : l ≤ L) :
    (Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) ⟨l, by omega⟩ c : ℝ) ≤
      (1 / 250 : ℝ) * M := by
  let i : Fin (L + 1) := ⟨l, by omega⟩
  have hclass := minorityClassU_mul_weight_le_minorityMass
    (L := L) (K := K) σ i c
  have hscaled := hclass.trans hs.minority_bound
  have hpow : 0 < (2 : ℝ) ^ (-(l : ℤ)) := zpow_pos (by norm_num) _
  change
    (Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) i c : ℝ) ≤
      (1 / 250 : ℝ) * M
  dsimp [i] at hscaled
  nlinarith

/-- Natural rounding form of `Snapshot617.minorityClassU_cast_le`. -/
theorem Snapshot617.minorityClassU_le_natCap
    {n l Bminority : ℕ} {M g₀ : ℝ} {σ : Sign}
    {c : Config (AgentState L K)}
    (hs : Phase3Post3.Snapshot617
      (L := L) (K := K) n l M g₀ σ c)
    (hl : l ≤ L)
    (hround : (1 / 250 : ℝ) * M < (Bminority + 1 : ℕ)) :
    Phase5Convergence.biasedMainClassU (L := L) (K := K)
      (Phase3Post3.minoritySignOfMajority σ) ⟨l, by omega⟩ c ≤
        Bminority := by
  have hcast := Snapshot617.minorityClassU_cast_le (hs := hs) hl
  have hlt :
      (Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) ⟨l, by omega⟩ c : ℝ) <
          (Bminority + 1 : ℕ) :=
    lt_of_le_of_lt hcast hround
  have hnat :
      Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) ⟨l, by omega⟩ c <
          Bminority + 1 := by
    exact_mod_cast hlt
  omega

/-- Transport the snapshot's minority exact-class estimate through an
explicit Phase-3/4 seam and the real Phase-4/5 route.  As with the upper-tail
transport, the seam nonincrease remains the sole deterministic bridge
obligation outside this file. -/
theorem Snapshot617.minorityClassU_cast_le_after_phase45
    {n l : ℕ} {M g₀ : ℝ} {σ : Sign}
    {c3 c4 d : Config (AgentState L K)}
    (hs : Phase3Post3.Snapshot617
      (L := L) (K := K) n l M g₀ σ c3)
    (hl : l ≤ L)
    (hseam : Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) ⟨l, by omega⟩ c4 ≤
      Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) ⟨l, by omega⟩ c3)
    (hreach : ReachableThroughPhase45 (L := L) (K := K) c4 d) :
    (Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) ⟨l, by omega⟩ d : ℝ) ≤
      (1 / 250 : ℝ) * M := by
  let i : Fin (L + 1) := ⟨l, by omega⟩
  have hroute := biasedMainClassU_eq_of_reachableThroughPhase45
    (L := L) (K := K) (Phase3Post3.minoritySignOfMajority σ) i c4 d hreach
  have hseamR :
      (Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) i c4 : ℝ) ≤
      (Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) i c3 : ℝ) := by
    exact_mod_cast hseam
  change
    (Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) i d : ℝ) ≤
      (1 / 250 : ℝ) * M
  rw [hroute]
  exact hseamR.trans (Snapshot617.minorityClassU_cast_le (hs := hs) hl)

/-- Natural rounding form of the transported minority exact-class cap. -/
theorem Snapshot617.minorityClassU_le_natCap_after_phase45
    {n l Bminority : ℕ} {M g₀ : ℝ} {σ : Sign}
    {c3 c4 d : Config (AgentState L K)}
    (hs : Phase3Post3.Snapshot617
      (L := L) (K := K) n l M g₀ σ c3)
    (hl : l ≤ L)
    (hseam : Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) ⟨l, by omega⟩ c4 ≤
      Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) ⟨l, by omega⟩ c3)
    (hreach : ReachableThroughPhase45 (L := L) (K := K) c4 d)
    (hround : (1 / 250 : ℝ) * M < (Bminority + 1 : ℕ)) :
    Phase5Convergence.biasedMainClassU (L := L) (K := K)
      (Phase3Post3.minoritySignOfMajority σ) ⟨l, by omega⟩ d ≤
        Bminority := by
  let i : Fin (L + 1) := ⟨l, by omega⟩
  have hroute := biasedMainClassU_eq_of_reachableThroughPhase45
    (L := L) (K := K) (Phase3Post3.minoritySignOfMajority σ) i c4 d hreach
  change Phase5Convergence.biasedMainClassU (L := L) (K := K)
      (Phase3Post3.minoritySignOfMajority σ) i d ≤ Bminority
  rw [hroute]
  exact hseam.trans
    (Snapshot617.minorityClassU_le_natCap (hs := hs) hl hround)

/-- Discharge the minority-class seam from real Phase-3/4 reachability:
minority signed mass is nonincreasing there, so the snapshot's `.004 M·2⁻ˡ`
bound still controls the exact level-`l` class; Phase 4/5 then preserves that
class exactly. -/
theorem Snapshot617.minorityClassU_cast_le_after_phase34_phase45
    {n l : ℕ} {M g₀ : ℝ} {σ : Sign}
    {c3 c4 d : Config (AgentState L K)}
    (hs : Phase3Post3.Snapshot617
      (L := L) (K := K) n l M g₀ σ c3)
    (hl : l ≤ L)
    (h34 : ReachableThroughPhase34 (L := L) (K := K) c3 c4)
    (h45 : ReachableThroughPhase45 (L := L) (K := K) c4 d) :
    (Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) ⟨l, by omega⟩ d : ℝ) ≤
      (1 / 250 : ℝ) * M := by
  let i : Fin (L + 1) := ⟨l, by omega⟩
  have hclass := minorityClassU_mul_weight_le_minorityMass
    (L := L) (K := K) σ i c4
  have hminor := minorityMass_le_of_reachableThroughPhase34
    (L := L) (K := K) σ c3 c4 h34
  have hscaled := hclass.trans (hminor.trans hs.minority_bound)
  have hpow : 0 < (2 : ℝ) ^ (-(l : ℤ)) := zpow_pos (by norm_num) _
  have hroute := biasedMainClassU_eq_of_reachableThroughPhase45
    (L := L) (K := K) (Phase3Post3.minoritySignOfMajority σ) i c4 d h45
  change
    (Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) i d : ℝ) ≤
      (1 / 250 : ℝ) * M
  rw [hroute]
  dsimp [i] at hscaled
  nlinarith

/-- Natural-cap version with both real deterministic routes explicit. -/
theorem Snapshot617.minorityClassU_le_natCap_after_phase34_phase45
    {n l Bminority : ℕ} {M g₀ : ℝ} {σ : Sign}
    {c3 c4 d : Config (AgentState L K)}
    (hs : Phase3Post3.Snapshot617
      (L := L) (K := K) n l M g₀ σ c3)
    (hl : l ≤ L)
    (h34 : ReachableThroughPhase34 (L := L) (K := K) c3 c4)
    (h45 : ReachableThroughPhase45 (L := L) (K := K) c4 d)
    (hround : (1 / 250 : ℝ) * M < (Bminority + 1 : ℕ)) :
    Phase5Convergence.biasedMainClassU (L := L) (K := K)
      (Phase3Post3.minoritySignOfMajority σ) ⟨l, by omega⟩ d ≤
        Bminority := by
  have hcast := Snapshot617.minorityClassU_cast_le_after_phase34_phase45
    (hs := hs) hl h34 h45
  have hlt :
      (Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) ⟨l, by omega⟩ d : ℝ) <
          (Bminority + 1 : ℕ) :=
    lt_of_le_of_lt hcast hround
  have hnat :
      Phase5Convergence.biasedMainClassU (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority σ) ⟨l, by omega⟩ d <
          Bminority + 1 := by
    exact_mod_cast hlt
  omega

/-- A Main agent whose dyadic exponent is exactly `i`, of either sign. -/
def MainAtLevel (i : Fin (L + 1)) (a : AgentState L K) : Prop :=
  a.role = .main ∧ ∃ σ : Sign, a.bias = .dyadic σ i

/-- Indicator for `MainAtLevel`. -/
noncomputable def agentMainAtLevelW
    (i : Fin (L + 1)) (a : AgentState L K) : ℕ :=
  if MainAtLevel i a then 1 else 0

/-- Number of Main agents at exactly exponent `i`, with both signs included. -/
noncomputable def mainAtLevelU (i : Fin (L + 1))
    (c : Config (AgentState L K)) : ℕ :=
  (c.map (agentMainAtLevelW (L := L) (K := K) i)).sum

/-- Pointwise adjacent-level identity.  Raising the scaled cutoff from `i` to
`i+1` doubles the old upper tail and adds weight two for every Main exactly at
level `i`. -/
theorem agentMassAboveScaledW_succ
    (i : Fin (L + 1)) (a : AgentState L K) :
    Lemma615MassAbove.agentMassAboveScaledW
        (L := L) (K := K) (i.val + 1) a =
      2 * Lemma615MassAbove.agentMassAboveScaledW
          (L := L) (K := K) i.val a +
        2 * agentMainAtLevelW (L := L) (K := K) i a := by
  by_cases hr : a.role = .main
  · simp only [Lemma615MassAbove.agentMassAboveScaledW, hr, if_pos]
    cases hb : a.bias with
    | zero => simp [Lemma615MassAbove.biasMassAboveScaledW,
        agentMainAtLevelW, MainAtLevel, hr, hb]
    | dyadic σ j =>
        by_cases hjlt : j.val < i.val
        · have hjlt' : j.val < i.val + 1 := by omega
          have hji : j ≠ i := by
            intro h
            subst j
            omega
          have hnot : ¬ MainAtLevel (L := L) (K := K) i a := by
            intro h
            rcases h.2 with ⟨τ, hτ⟩
            rw [hb] at hτ
            injection hτ with _ hidx
            exact hji hidx
          have hsub : i.val + 1 - j.val = (i.val - j.val) + 1 := by
            omega
          simp [Lemma615MassAbove.biasMassAboveScaledW, hjlt, hjlt',
            agentMainAtLevelW, hnot, hsub, pow_succ]
          omega
        · by_cases hji : j = i
          · subst j
            have hex : MainAtLevel (L := L) (K := K) i a :=
              ⟨hr, ⟨σ, hb⟩⟩
            simp [Lemma615MassAbove.biasMassAboveScaledW,
              agentMainAtLevelW, hex]
          · have hij : i.val < j.val := by
              have hne : j.val ≠ i.val := by
                intro h
                exact hji (Fin.ext h)
              omega
            have hnot : ¬ MainAtLevel (L := L) (K := K) i a := by
              intro h
              rcases h.2 with ⟨τ, hτ⟩
              rw [hb] at hτ
              injection hτ with _ hidx
              exact hji hidx
            simp [Lemma615MassAbove.biasMassAboveScaledW, hjlt,
              show ¬j.val < i.val + 1 by omega,
              agentMainAtLevelW, hnot]
  · simp [Lemma615MassAbove.agentMassAboveScaledW,
      agentMainAtLevelW, MainAtLevel, hr]

/-- Configuration-level adjacent-cutoff identity. -/
theorem massAboveScaled_succ
    (i : Fin (L + 1)) (c : Config (AgentState L K)) :
    Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) (i.val + 1) c =
      2 * Lemma615MassAbove.massAboveScaled
          (L := L) (K := K) i.val c +
        2 * mainAtLevelU (L := L) (K := K) i c := by
  induction c using Multiset.induction_on with
  | empty => simp [Lemma615MassAbove.massAboveScaled, mainAtLevelU]
  | @cons a c ih =>
      simp only [Lemma615MassAbove.massAboveScaled, mainAtLevelU,
        Multiset.map_cons, Multiset.sum_cons] at ih ⊢
      rw [agentMassAboveScaledW_succ (L := L) (K := K) i a, ih]
      omega

/-- The exact-level count is the sum of the positive and negative biased-Main
classes already exposed by the Phase-5 sampling development. -/
theorem mainAtLevelU_eq_biasedMainClassU_add
    (i : Fin (L + 1)) (c : Config (AgentState L K)) :
    mainAtLevelU (L := L) (K := K) i c =
      Phase5Convergence.biasedMainClassU (L := L) (K := K) .pos i c +
        Phase5Convergence.biasedMainClassU (L := L) (K := K) .neg i c := by
  induction c using Multiset.induction_on with
  | empty => simp [mainAtLevelU, Phase5Convergence.biasedMainClassU]
  | @cons a c ih =>
      simp only [mainAtLevelU, Phase5Convergence.biasedMainClassU,
        Multiset.map_cons, Multiset.sum_cons, Multiset.countP_cons] at ih ⊢
      rw [ih]
      by_cases hr : a.role = .main
      · cases hb : a.bias with
        | zero =>
            simp [agentMainAtLevelW, MainAtLevel,
              Phase5Convergence.biasedMainClass, hr, hb]
        | dyadic σ j =>
            cases σ <;> by_cases hji : j = i
            · subst j
              simp [agentMainAtLevelW, MainAtLevel,
                Phase5Convergence.biasedMainClass, hr, hb]
              omega
            · simp [agentMainAtLevelW, MainAtLevel,
                Phase5Convergence.biasedMainClass, hr, hb, hji]
            · subst j
              simp [agentMainAtLevelW, MainAtLevel,
                Phase5Convergence.biasedMainClass, hr, hb]
              omega
            · simp [agentMainAtLevelW, MainAtLevel,
                Phase5Convergence.biasedMainClass, hr, hb, hji]
      · simp [agentMainAtLevelW, MainAtLevel,
          Phase5Convergence.biasedMainClass, hr]

/-- Majority/minority-sign rendering of the exact-level decomposition. -/
theorem mainAtLevelU_eq_majority_add_minority
    (σ : Sign) (i : Fin (L + 1)) (c : Config (AgentState L K)) :
    mainAtLevelU (L := L) (K := K) i c =
      Phase5Convergence.biasedMainClassU (L := L) (K := K) σ i c +
        Phase5Convergence.biasedMainClassU (L := L) (K := K)
          (Phase3Post3.minoritySignOfMajority σ) i c := by
  rw [mainAtLevelU_eq_biasedMainClassU_add (L := L) (K := K) i c]
  cases σ <;> simp [Phase3Post3.minoritySignOfMajority, Nat.add_comm]

/-- Paper Lemma 7.2's case discriminator: the majority-sign Main class at
level `l` contains more than `.19 M` agents. -/
noncomputable def LowerClassLarge
    (σ : Sign) (l : Fin (L + 1)) (M : ℝ)
    (c : Config (AgentState L K)) : Prop :=
  (19 / 100 : ℝ) * M <
    (Phase5Convergence.biasedMainClassU
      (L := L) (K := K) σ l c : ℝ)

/-- In the small-lower-class branch, a rounded `.19 M` majority-class cap
plus a minority-class cap bounds the total exact-level population. -/
theorem mainAtLevelU_le_of_not_lowerClassLarge
    (σ : Sign) (l : Fin (L + 1)) (M : ℝ)
    (Bmajority Bminority : ℕ) (c : Config (AgentState L K))
    (hsmall : ¬ LowerClassLarge (L := L) (K := K) σ l M c)
    (hmajorityRound : (19 / 100 : ℝ) * M < (Bmajority + 1 : ℕ))
    (hminority : Phase5Convergence.biasedMainClassU
      (L := L) (K := K) (Phase3Post3.minoritySignOfMajority σ) l c ≤
        Bminority) :
    mainAtLevelU (L := L) (K := K) l c ≤ Bmajority + Bminority := by
  have hmajorityR :
      (Phase5Convergence.biasedMainClassU
        (L := L) (K := K) σ l c : ℝ) ≤ (19 / 100 : ℝ) * M := by
    exact le_of_not_gt hsmall
  have hmajorityLt :
      (Phase5Convergence.biasedMainClassU
        (L := L) (K := K) σ l c : ℝ) < (Bmajority + 1 : ℕ) :=
    lt_of_le_of_lt hmajorityR hmajorityRound
  have hmajority : Phase5Convergence.biasedMainClassU
      (L := L) (K := K) σ l c ≤ Bmajority := by
    have hnat : Phase5Convergence.biasedMainClassU
        (L := L) (K := K) σ l c < Bmajority + 1 := by
      exact_mod_cast hmajorityLt
    omega
  rw [mainAtLevelU_eq_majority_add_minority
    (L := L) (K := K) σ l c]
  omega

/-- The two class-specific concentration outputs needed at the seam.  These
are deliberately separate from the bare one-class `ReserveSampleGood`: both
sampled levels used by the paper's dichotomy must be certified. -/
structure TwoClassSampleFloors
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (Rlo Rhi : ℕ) (c : Config (AgentState L K)) : Prop where
  lower : Rlo ≤ Phase6FuelLedger.reserveFuel (L := L) (K := K) l c
  higher : Rhi ≤ Phase6FuelLedger.reserveFuel
    (L := L) (K := K) (Phase6FuelLedger.highIndex l hl) c

/-- Build the two concentration outputs from the public sampled-class counts. -/
theorem TwoClassSampleFloors.of_sampledClassU
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (Rlo Rhi : ℕ) (c : Config (AgentState L K))
    (hlower : Rlo ≤ Phase5Convergence.sampledReserveClassU
      (L := L) (K := K) l c)
    (hhigher : Rhi ≤ Phase5Convergence.sampledReserveClassU
      (L := L) (K := K) (Phase6FuelLedger.highIndex l hl) c) :
    TwoClassSampleFloors (L := L) (K := K) l hl Rlo Rhi c := by
  constructor
  · simpa [Phase6FuelLedger.reserveFuel_eq_sampledReserveClassU] using hlower
  · simpa [Phase6FuelLedger.reserveFuel_eq_sampledReserveClassU] using hhigher

/-- Two separately proved Phase-5 postconditions supply the two concentration
floors.  A single `ReserveSampleGood` supplies only one of these fields. -/
theorem TwoClassSampleFloors.of_two_reserveSampleGood
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (Rlo Rhi : ℕ) (c : Config (AgentState L K))
    (hlower : Phase5Convergence.ReserveSampleGood
      (L := L) (K := K) l Rlo c)
    (hhigher : Phase5Convergence.ReserveSampleGood
      (L := L) (K := K) (Phase6FuelLedger.highIndex l hl) Rhi c) :
    TwoClassSampleFloors (L := L) (K := K) l hl Rlo Rhi c := by
  apply TwoClassSampleFloors.of_sampledClassU
    (L := L) (K := K) l hl Rlo Rhi c
  · exact hlower.2
  · exact hhigher.2

/-! ### A one-class post cannot be reused as the second class event -/

namespace OneClassSampleObstruction

/-- A lower sample index with a distinct two-level-higher index. -/
def lowerIndex : Fin 5 := ⟨1, by decide⟩

theorem lowerIndex_two_le : lowerIndex.val + 2 ≤ 4 := by
  decide

/-- A single sampled Reserve at `lowerIndex`, and no Reserve at the higher
index.  The other fields are immaterial to the sampled-class predicates. -/
def lowerReserve : AgentState 4 0 :=
  { input := .A
    output := .A
    phase := ⟨5, by decide⟩
    role := .reserve
    assigned := true
    bias := .zero
    smallBias := ⟨3, by decide⟩
    hour := lowerIndex
    minute := ⟨0, by decide⟩
    full := false
    opinions := ⟨0, by decide⟩
    counter := ⟨1, by decide⟩ }

def c : Config (AgentState 4 0) :=
  {lowerReserve}

/-- The one-class Phase-5 post holds with a nonzero lower threshold. -/
theorem lower_reserveSampleGood :
    Phase5Convergence.ReserveSampleGood
      (L := 4) (K := 0) lowerIndex 1 c := by
  constructor
  · unfold ReserveSampling.ReserveSampled
      ReserveSampling.unsampledReserveU
    change Multiset.countP _ (lowerReserve ::ₘ 0) = 0
    rw [Multiset.countP_cons, Multiset.countP_zero]
    norm_num [ReserveSampling.unsampled, lowerReserve, lowerIndex]
  · unfold Phase5Convergence.sampledFloor
      Phase5Convergence.sampledReserveClassU
    change 1 ≤ Multiset.countP _ (lowerReserve ::ₘ 0)
    rw [Multiset.countP_cons, Multiset.countP_zero]
    norm_num [Phase5Convergence.sampledReserveClass,
      lowerReserve, lowerIndex]

/-- The distinct higher-class floor fails on the same configuration. -/
theorem higher_sampledFloor_fails :
    ¬ Phase5Convergence.sampledFloor
      (L := 4) (K := 0)
        (Phase6FuelLedger.highIndex lowerIndex lowerIndex_two_le) 1 c := by
  unfold Phase5Convergence.sampledFloor
    Phase5Convergence.sampledReserveClassU
  change ¬ 1 ≤ Multiset.countP _ (lowerReserve ::ₘ 0)
  rw [Multiset.countP_cons, Multiset.countP_zero]
  norm_num [Phase5Convergence.sampledReserveClass,
    Phase6FuelLedger.highIndex, lowerReserve, lowerIndex]

/-- Formal obstruction to treating one `ReserveSampleGood` proof as both
sampled-class events. -/
theorem one_class_post_not_two_class :
    Phase5Convergence.ReserveSampleGood
        (L := 4) (K := 0) lowerIndex 1 c ∧
      ¬ TwoClassSampleFloors
        (L := 4) (K := 0) lowerIndex lowerIndex_two_le 1 1 c := by
  refine ⟨lower_reserveSampleGood, ?_⟩
  intro htwo
  apply higher_sampledFloor_fails
  simpa only [Phase5Convergence.sampledFloor,
    Phase6FuelLedger.reserveFuel_eq_sampledReserveClassU] using htwo.higher

end OneClassSampleObstruction

/-- Minimal same-horizon producer for precisely the two sample floors consumed
by `twoLevelFuelLedger_of_snapshot_route`.  It assumes one class-tail theorem
at `l` and a second class-tail theorem at `highIndex l hl`, then applies a
two-event union bound.  In particular it does not inherit the known-false
`Phase5AllWin` closure premise of the older all-sampled convergence wrapper.

The two tail hypotheses have the exact `Phase035Endpoints.hConcDemand` shape and
may be generated by separate calls to the single-index
`SamplingRateFloor.hConcDemand_of_floors_and_escape`.  Their per-index clock-separation and
escape inputs remain genuine residuals in HEAD. -/
noncomputable def twoClassSampleFloorsConvergence
    (n : ℕ) (l : Fin (L + 1)) (hl : l.val + 2 ≤ L) (Rlo Rhi M₀ t : ℕ)
    (εLo εHi : ℝ≥0)
    (hConcLo : ∀ c₀,
      ReserveSampling.Phase5AllWin (L := L) (K := K) n c₀ →
      ReserveSampling.unsampledReserveU (L := L) (K := K) c₀ ≤ M₀ →
      ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ Phase5Convergence.sampledFloor
          (L := L) (K := K) l Rlo c} ≤ (εLo : ℝ≥0∞))
    (hConcHi : ∀ c₀,
      ReserveSampling.Phase5AllWin (L := L) (K := K) n c₀ →
      ReserveSampling.unsampledReserveU (L := L) (K := K) c₀ ≤ M₀ →
      ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ Phase5Convergence.sampledFloor
          (L := L) (K := K) (Phase6FuelLedger.highIndex l hl) Rhi c} ≤
            (εHi : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := ReserveSampling.Phase5AllWin (L := L) (K := K) n c ∧
    ReserveSampling.unsampledReserveU (L := L) (K := K) c ≤ M₀
  Post c := TwoClassSampleFloors (L := L) (K := K) l hl Rlo Rhi c
  t := t
  ε := εLo + εHi
  convergence := by
    intro c₀ hPre
    have hcover :
        {c : Config (AgentState L K) |
          ¬ TwoClassSampleFloors (L := L) (K := K) l hl Rlo Rhi c} ⊆
          {c | ¬ Phase5Convergence.sampledFloor
            (L := L) (K := K) l Rlo c} ∪
          {c | ¬ Phase5Convergence.sampledFloor
            (L := L) (K := K)
              (Phase6FuelLedger.highIndex l hl) Rhi c} := by
      intro c hc
      simp only [Set.mem_setOf_eq, Set.mem_union] at hc ⊢
      by_cases hLo : Phase5Convergence.sampledFloor
          (L := L) (K := K) l Rlo c
      · by_cases hHi : Phase5Convergence.sampledFloor
            (L := L) (K := K) (Phase6FuelLedger.highIndex l hl) Rhi c
        · exact False.elim (hc
            (TwoClassSampleFloors.of_sampledClassU
              (L := L) (K := K) l hl Rlo Rhi c hLo hHi))
        · exact Or.inr hHi
      · exact Or.inl hLo
    calc
      ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | ¬ TwoClassSampleFloors
            (L := L) (K := K) l hl Rlo Rhi c}
        ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
            ({c | ¬ Phase5Convergence.sampledFloor
              (L := L) (K := K) l Rlo c} ∪
             {c | ¬ Phase5Convergence.sampledFloor
              (L := L) (K := K)
                (Phase6FuelLedger.highIndex l hl) Rhi c}) :=
          measure_mono hcover
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
              {c | ¬ Phase5Convergence.sampledFloor
                (L := L) (K := K) l Rlo c} +
            ((NonuniformMajority L K).transitionKernel ^ t) c₀
              {c | ¬ Phase5Convergence.sampledFloor
                (L := L) (K := K)
                  (Phase6FuelLedger.highIndex l hl) Rhi c} :=
          measure_union_le _ _
      _ ≤ (εLo : ℝ≥0∞) + (εHi : ℝ≥0∞) := by
          gcongr
          · exact hConcLo c₀ hPre.1 hPre.2
          · exact hConcHi c₀ hPre.1 hPre.2
      _ = ((εLo + εHi : ℝ≥0) : ℝ≥0∞) := by
          simp only [ENNReal.coe_add]

/-- Deterministic mass/count side of paper Lemma 7.2.  The upper branch is
written using the exact adjacent-level identity, making the otherwise hidden
count of *both signs* at level `l` explicit. -/
structure Lemma72MassCountBounds
    (σ : Sign) (l : Fin (L + 1)) (M : ℝ)
    (K₀ Rlo Rhi : ℕ) (c : Config (AgentState L K)) : Prop where
  lower : LowerClassLarge (L := L) (K := K) σ l M c →
    K₀ + Lemma615MassAbove.massAboveScaled
      (L := L) (K := K) l.val c ≤ Rlo
  higher : ¬ LowerClassLarge (L := L) (K := K) σ l M c →
    K₀ +
        (2 * Lemma615MassAbove.massAboveScaled
          (L := L) (K := K) l.val c +
        2 * mainAtLevelU (L := L) (K := K) l c) ≤ Rhi

/-- A convenient producer for the deterministic branch bounds.  It exposes
the three integer facts that the paper's real inequalities must ultimately
round to: an upper-tail cap, an exact-level count cap in the small-class case,
and the two numerical budget inequalities. -/
theorem Lemma72MassCountBounds.of_caps
    (σ : Sign) (l : Fin (L + 1)) (M : ℝ)
    (K₀ Rlo Rhi Btail Blevel : ℕ) (c : Config (AgentState L K))
    (htail : Lemma615MassAbove.massAboveScaled
      (L := L) (K := K) l.val c ≤ Btail)
    (hlevel : ¬ LowerClassLarge (L := L) (K := K) σ l M c →
      mainAtLevelU (L := L) (K := K) l c ≤ Blevel)
    (hlowerBudget : K₀ + Btail ≤ Rlo)
    (hhigherBudget : K₀ + (2 * Btail + 2 * Blevel) ≤ Rhi) :
    Lemma72MassCountBounds
      (L := L) (K := K) σ l M K₀ Rlo Rhi c := by
  constructor
  · intro _
    omega
  · intro hsmall
    have hlevel' := hlevel hsmall
    omega

/-- Paper-shaped producer for the branch arithmetic.  Relative to the
snapshot tail cap, the only profile fact left explicit is the rounded
minority-sign class count at level `l`; the `.19 M` majority part follows
directly from the case split. -/
theorem Lemma72MassCountBounds.of_paper_caps
    (σ : Sign) (l : Fin (L + 1)) (M : ℝ)
    (K₀ Rlo Rhi Btail Bmajority Bminority : ℕ)
    (c : Config (AgentState L K))
    (htail : Lemma615MassAbove.massAboveScaled
      (L := L) (K := K) l.val c ≤ Btail)
    (hmajorityRound : (19 / 100 : ℝ) * M < (Bmajority + 1 : ℕ))
    (hminority : Phase5Convergence.biasedMainClassU
      (L := L) (K := K) (Phase3Post3.minoritySignOfMajority σ) l c ≤
        Bminority)
    (hlowerBudget : K₀ + Btail ≤ Rlo)
    (hhigherBudget :
      K₀ + (2 * Btail + 2 * (Bmajority + Bminority)) ≤ Rhi) :
    Lemma72MassCountBounds
      (L := L) (K := K) σ l M K₀ Rlo Rhi c := by
  apply Lemma72MassCountBounds.of_caps
    (L := L) (K := K) σ l M K₀ Rlo Rhi Btail
      (Bmajority + Bminority) c htail
  · intro hsmall
    exact mainAtLevelU_le_of_not_lowerClassLarge
      (L := L) (K := K) σ l M Bmajority Bminority c
      hsmall hmajorityRound hminority
  · exact hlowerBudget
  · exact hhigherBudget

/-- Phase-3-snapshot producer for all deterministic Lemma-7.2 branch
arithmetic.  Both the upper-tail and minority exact-class estimates are
transported through the real Phase-4/5 kernel; only their explicit Phase-3/4
seam inequalities, integer roundings, and final numerical budgets remain. -/
theorem Lemma72MassCountBounds.of_snapshot_route
    {n : ℕ} (σ : Sign) (l : Fin (L + 1)) (M g₀ : ℝ)
    (K₀ Rlo Rhi Btail Bmajority Bminority : ℕ)
    (c3 c4 d : Config (AgentState L K))
    (hs : Phase3Post3.Snapshot617
      (L := L) (K := K) n l.val M g₀ σ c3)
    (htailSeam : Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) l.val c4 ≤
      Lemma615MassAbove.massAboveScaled (L := L) (K := K) l.val c3)
    (hminoritySeam : Phase5Convergence.biasedMainClassU
        (L := L) (K := K) (Phase3Post3.minoritySignOfMajority σ) l c4 ≤
      Phase5Convergence.biasedMainClassU
        (L := L) (K := K) (Phase3Post3.minoritySignOfMajority σ) l c3)
    (hreach : ReachableThroughPhase45 (L := L) (K := K) c4 d)
    (htailRound : (1 / 500 : ℝ) * M < (Btail + 1 : ℕ))
    (hmajorityRound : (19 / 100 : ℝ) * M < (Bmajority + 1 : ℕ))
    (hminorityRound : (1 / 250 : ℝ) * M < (Bminority + 1 : ℕ))
    (hlowerBudget : K₀ + Btail ≤ Rlo)
    (hhigherBudget :
      K₀ + (2 * Btail + 2 * (Bmajority + Bminority)) ≤ Rhi) :
    Lemma72MassCountBounds
      (L := L) (K := K) σ l M K₀ Rlo Rhi d := by
  apply Lemma72MassCountBounds.of_paper_caps
    (L := L) (K := K) σ l M K₀ Rlo Rhi
      Btail Bmajority Bminority d
  · exact Snapshot617.massAboveScaled_le_natCap_after_phase45
      (hs := hs) htailSeam hreach htailRound
  · exact hmajorityRound
  · exact Snapshot617.minorityClassU_le_natCap_after_phase45
      (hs := hs) (by omega) hminoritySeam hreach hminorityRound
  · exact hlowerBudget
  · exact hhigherBudget

/-- Fully route-based snapshot producer.  The two former Phase-3/4 seam
inequalities are consequences of `ReachableThroughPhase34`: the scaled tail
is directly nonincreasing, and the minority exact class is controlled via
nonincreasing minority signed mass. -/
theorem Lemma72MassCountBounds.of_snapshot_phase_routes
    {n : ℕ} (σ : Sign) (l : Fin (L + 1)) (M g₀ : ℝ)
    (K₀ Rlo Rhi Btail Bmajority Bminority : ℕ)
    (c3 c4 d : Config (AgentState L K))
    (hs : Phase3Post3.Snapshot617
      (L := L) (K := K) n l.val M g₀ σ c3)
    (h34 : ReachableThroughPhase34 (L := L) (K := K) c3 c4)
    (h45 : ReachableThroughPhase45 (L := L) (K := K) c4 d)
    (htailRound : (1 / 500 : ℝ) * M < (Btail + 1 : ℕ))
    (hmajorityRound : (19 / 100 : ℝ) * M < (Bmajority + 1 : ℕ))
    (hminorityRound : (1 / 250 : ℝ) * M < (Bminority + 1 : ℕ))
    (hlowerBudget : K₀ + Btail ≤ Rlo)
    (hhigherBudget :
      K₀ + (2 * Btail + 2 * (Bmajority + Bminority)) ≤ Rhi) :
    Lemma72MassCountBounds
      (L := L) (K := K) σ l M K₀ Rlo Rhi d := by
  apply Lemma72MassCountBounds.of_paper_caps
    (L := L) (K := K) σ l M K₀ Rlo Rhi
      Btail Bmajority Bminority d
  · exact Snapshot617.massAboveScaled_le_natCap_after_phase34_phase45
      (hs := hs) h34 h45 htailRound
  · exact hmajorityRound
  · exact Snapshot617.minorityClassU_le_natCap_after_phase34_phase45
      (hs := hs) (by omega) h34 h45 hminorityRound
  · exact hlowerBudget
  · exact hhigherBudget

/-- Full deterministic assembly of the Phase-6 entry ledger from exactly the
two sampled-class floors and the paper's two mass/count inequalities. -/
theorem twoLevelFuelLedger_of_two_class_floors
    (σ : Sign) (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (M : ℝ) (K₀ Rlo Rhi : ℕ) (c : Config (AgentState L K))
    (hsample : TwoClassSampleFloors
      (L := L) (K := K) l hl Rlo Rhi c)
    (hmass : Lemma72MassCountBounds
      (L := L) (K := K) σ l M K₀ Rlo Rhi c) :
    Phase6FuelLedger.TwoLevelFuelLedger
      (L := L) (K := K) l K₀ c := by
  apply Phase6FuelEntry.twoLevelFuelLedger_of_massAbove_cases
    (L := L) (K := K) l hl K₀ c
  by_cases hlarge : LowerClassLarge (L := L) (K := K) σ l M c
  · exact Or.inl ((hmass.lower hlarge).trans hsample.lower)
  · right
    calc
      K₀ + Lemma615MassAbove.massAboveScaled
          (L := L) (K := K)
          (Phase6FuelLedger.highIndex l hl).val c =
          K₀ + (2 * Lemma615MassAbove.massAboveScaled
            (L := L) (K := K) l.val c +
            2 * mainAtLevelU (L := L) (K := K) l c) := by
              simp only [Phase6FuelLedger.highIndex]
              rw [massAboveScaled_succ (L := L) (K := K) l c]
      _ ≤ Rhi := hmass.higher hlarge
      _ ≤ Phase6FuelLedger.reserveFuel
          (L := L) (K := K) (Phase6FuelLedger.highIndex l hl) c :=
        hsample.higher
      _ ≤ Phase6FuelLedger.twoReserveFuel (L := L) (K := K) l c := by
        rw [Phase6FuelLedger.twoReserveFuel_eq_reserveFuel_add
          (L := L) (K := K) l hl c]
        omega

/-- End-to-end deterministic Phase-5-to-6 entry producer.  Its only
probabilistic inputs are the two class-specific sample floors.  Both
Phase-3/4 seam inequalities have been discharged from the actual real-kernel
route; the remaining non-probabilistic inputs are reachability and elementary
integer rounding/budget obligations. -/
theorem twoLevelFuelLedger_of_snapshot_route
    {n : ℕ} (σ : Sign) (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (M g₀ : ℝ) (K₀ Rlo Rhi Btail Bmajority Bminority : ℕ)
    (c3 c4 d : Config (AgentState L K))
    (hsample : TwoClassSampleFloors
      (L := L) (K := K) l hl Rlo Rhi d)
    (hs : Phase3Post3.Snapshot617
      (L := L) (K := K) n l.val M g₀ σ c3)
    (h34 : ReachableThroughPhase34 (L := L) (K := K) c3 c4)
    (h45 : ReachableThroughPhase45 (L := L) (K := K) c4 d)
    (htailRound : (1 / 500 : ℝ) * M < (Btail + 1 : ℕ))
    (hmajorityRound : (19 / 100 : ℝ) * M < (Bmajority + 1 : ℕ))
    (hminorityRound : (1 / 250 : ℝ) * M < (Bminority + 1 : ℕ))
    (hlowerBudget : K₀ + Btail ≤ Rlo)
    (hhigherBudget :
      K₀ + (2 * Btail + 2 * (Bmajority + Bminority)) ≤ Rhi) :
    Phase6FuelLedger.TwoLevelFuelLedger
      (L := L) (K := K) l K₀ d := by
  apply twoLevelFuelLedger_of_two_class_floors
    (L := L) (K := K) σ l hl M K₀ Rlo Rhi d hsample
  exact Lemma72MassCountBounds.of_snapshot_phase_routes
    (L := L) (K := K) σ l M g₀ K₀ Rlo Rhi
      Btail Bmajority Bminority c3 c4 d hs h34 h45
      htailRound hmajorityRound hminorityRound hlowerBudget hhigherBudget

#print axioms Transition_agentMassAboveScaledW_pair_of_phase_four_or_five
#print axioms massAboveScaled_eq_of_reachableThroughPhase45
#print axioms biasedMainClassU_eq_of_reachableThroughPhase45
#print axioms Snapshot617.massAboveScaled_le_natCap_after_phase45
#print axioms Snapshot617.minorityClassU_le_natCap_after_phase45
#print axioms massAboveScaled_le_of_reachableThroughPhase34
#print axioms minorityMass_le_of_reachableThroughPhase34
#print axioms massAboveScaled_succ
#print axioms mainAtLevelU_eq_majority_add_minority
#print axioms OneClassSampleObstruction.one_class_post_not_two_class
#print axioms twoClassSampleFloorsConvergence
#print axioms twoLevelFuelLedger_of_snapshot_route

end Phase5To6FuelProducer
end Ripple.PopulationProtocol.ExactMajority
