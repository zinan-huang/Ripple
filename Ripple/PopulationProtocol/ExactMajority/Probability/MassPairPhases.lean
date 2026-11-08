/-
Per-pair conservation of the signed dyadic bias sum for the phase transitions
not yet covered elsewhere in the codebase.

For each two-agent transition of phases 5, 6, 7 (plus the phase-independent
dispatch helpers Phase2/Phase10), we prove that the sum
`Bias.toRat s.bias + Bias.toRat t.bias` of the interacting pair is invariant.

These mirror `Phase4Transition_preserves_dyadicBiasSum_pair` and
`phase3CancelSplit_preserves_dyadicBiasSum_pair` from
`Protocol/Transition.lean`.
-/

import Ripple.PopulationProtocol.ExactMajority.Protocol.Transition

namespace Ripple.PopulationProtocol.ExactMajority
namespace MassPairPhases

variable {L K : ℕ}

/-! ## Local dyadic arithmetic (private copies of the `Protocol` helpers) -/

private lemma dyadic_split_pos_div (n : ℕ) :
    (1 : ℚ) / (2 ^ n) =
      (1 : ℚ) / (2 ^ (n + 1)) + (1 : ℚ) / (2 ^ (n + 1)) := by
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  rw [pow_succ]
  field_simp [pow_ne_zero n htwo]
  ring

private lemma dyadic_split_neg_div (n : ℕ) :
    -(1 : ℚ) / (2 ^ n) =
      -(1 : ℚ) / (2 ^ (n + 1)) + -(1 : ℚ) / (2 ^ (n + 1)) := by
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  rw [pow_succ]
  field_simp [pow_ne_zero n htwo]
  ring

/-! ## Bias preservation of the counter subroutine from phase ≥ 3 -/

/-- `advancePhase` only rewrites the `phase` field, so it preserves `bias`. -/
private lemma advancePhase_bias (a : AgentState L K) :
    (advancePhase L K a).bias = a.bias := by
  unfold advancePhase
  split_ifs <;> rfl

/-- `phaseInit` only rewrites `bias` at target phase 3; for target phase ≥ 4 it
leaves `bias` untouched. -/
private lemma phaseInit_bias_of_phase_ge_four (p : Fin 11) (a : AgentState L K)
    (hp : 4 ≤ p.val) : (phaseInit L K p a).bias = a.bias := by
  have h1 : ¬ (p.val = 1) := by omega
  have h2 : ¬ (p.val = 2) := by omega
  have h3 : ¬ (p.val = 3) := by omega
  unfold phaseInit
  rw [dif_neg h1, dif_neg h2, dif_neg h3]
  split_ifs <;> simp_all [enterPhase10] <;> split_ifs <;> rfl

/-- The phase after `advancePhase` from a phase `≥ 3` is `≥ 4`. -/
private lemma advancePhase_phase_ge_four (a : AgentState L K)
    (h : 3 ≤ a.phase.val) : 4 ≤ (advancePhase L K a).phase.val := by
  unfold advancePhase
  split_ifs with hlt
  · simp only []
    omega
  · omega

/-- From phase ≥ 3, the standard counter subroutine preserves `bias`: the only
phase-advancing branch runs `advancePhaseWithInit`, whose destination phase is
`≥ 4`, and `phaseInit` touches `bias` only at target phase 3. -/
theorem stdCounterSubroutine_bias_of_phase_ge_three (a : AgentState L K)
    (h : 3 ≤ a.phase.val) :
    (stdCounterSubroutine L K a).bias = a.bias := by
  unfold stdCounterSubroutine
  split_ifs with hc
  · unfold advancePhaseWithInit
    rw [phaseInit_bias_of_phase_ge_four _ _
      (advancePhase_phase_ge_four a h)]
    exact advancePhase_bias a
  · rfl

/-- The per-agent clock guard used at the tail of phases 5–8 preserves `bias`
whenever the agent is in phase ≥ 3. -/
private lemma clockGuard_bias (a : AgentState L K) (h : 3 ≤ a.phase.val) :
    (if a.role = .clock then stdCounterSubroutine L K a else a).bias = a.bias := by
  split_ifs with hc
  · exact stdCounterSubroutine_bias_of_phase_ge_three a h
  · rfl

/-! ## Phase 5 -/

/-- Phase 5 preserves the paired signed dyadic bias sum: `doSample` writes only
`hour`, and the tail clock guard preserves bias (lemma 1). -/
theorem Phase5Transition_preserves_dyadicBiasSum_pair (s t : AgentState L K)
    (hs : 3 ≤ s.phase.val) (ht : 3 ≤ t.phase.val) :
    Bias.toRat (Phase5Transition L K s t).1.bias +
      Bias.toRat (Phase5Transition L K s t).2.bias =
    Bias.toRat s.bias + Bias.toRat t.bias := by
  let doSample : AgentState L K → AgentState L K →
      AgentState L K × AgentState L K := fun r m =>
    if r.hour.val = L then ({ r with hour := exponentOf L m.bias }, m) else (r, m)
  let s1 := if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero) then
      (doSample s t).1
    else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero) then
      (doSample t s).2
    else s
  let t1 := if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero) then
      (doSample s t).2
    else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero) then
      (doSample t s).1
    else t
  have hs1b : s1.bias = s.bias := by
    dsimp only [s1, doSample]; split_ifs <;> rfl
  have ht1b : t1.bias = t.bias := by
    dsimp only [t1, doSample]; split_ifs <;> rfl
  have hs1p : s1.phase.val = s.phase.val := by
    dsimp only [s1, doSample]; split_ifs <;> rfl
  have ht1p : t1.phase.val = t.phase.val := by
    dsimp only [t1, doSample]; split_ifs <;> rfl
  have hfinal : Phase5Transition L K s t =
      (if s1.role = .clock then stdCounterSubroutine L K s1 else s1,
       if t1.role = .clock then stdCounterSubroutine L K t1 else t1) := rfl
  rw [hfinal]
  show Bias.toRat (if s1.role = .clock then stdCounterSubroutine L K s1 else s1).bias
      + Bias.toRat (if t1.role = .clock then stdCounterSubroutine L K t1 else t1).bias
      = Bias.toRat s.bias + Bias.toRat t.bias
  rw [clockGuard_bias s1 (by rw [hs1p]; exact hs),
      clockGuard_bias t1 (by rw [ht1p]; exact ht), hs1b, ht1b]

/-! ## Phase 6 -/

/-- `doSplit` conserves the paired bias sum when the reserve `r` starts unbiased:
before the split the mass is `σ·2^{-j}` carried entirely by `m`; after the split
both outputs carry `σ·2^{-(j+1)}`, and `2·σ·2^{-(j+1)} = σ·2^{-j}`. -/
private lemma doSplit_bias_sum (r m : AgentState L K) (hr : r.bias = Bias.zero) :
    Bias.toRat (doSplit L K r m).1.bias + Bias.toRat (doSplit L K r m).2.bias
      = Bias.toRat r.bias + Bias.toRat m.bias := by
  unfold doSplit
  match hm : m.bias with
  | Bias.zero => simp [hm]
  | Bias.dyadic sgn j =>
    simp only []
    split_ifs with hg hjL
    · cases sgn
      · simp only [Bias.toRat, hr]
        rw [zero_add]
        exact (dyadic_split_pos_div j.val).symm
      · simp only [Bias.toRat, hr]
        rw [zero_add]
        exact (dyadic_split_neg_div j.val).symm
    · simp [hm]
    · simp [hm]

/-- Phase 6 preserves the paired signed dyadic bias sum. When a Reserve+Main
split fires, the Reserve's old bias is zero by hypothesis, so the mass is halved
into two copies (`doSplit_bias_sum`); the tail clock guard preserves bias. -/
theorem Phase6Transition_preserves_dyadicBiasSum_pair (s t : AgentState L K)
    (hs : 3 ≤ s.phase.val) (ht : 3 ≤ t.phase.val)
    (hsres : s.role = .reserve → s.bias = .zero)
    (htres : t.role = .reserve → t.bias = .zero) :
    Bias.toRat (Phase6Transition L K s t).1.bias +
      Bias.toRat (Phase6Transition L K s t).2.bias =
    Bias.toRat s.bias + Bias.toRat t.bias := by
  let s1 := if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero) then
      (doSplit L K s t).1
    else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero) then
      (doSplit L K t s).2
    else s
  let t1 := if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero) then
      (doSplit L K s t).2
    else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero) then
      (doSplit L K t s).1
    else t
  have hs1p : 3 ≤ s1.phase.val := by
    dsimp only [s1]
    split_ifs with hG1 hG2
    · exact le_trans hs (doSplit_phase_nondec L K s t).1
    · exact le_trans hs (doSplit_phase_nondec L K t s).2
    · exact hs
  have ht1p : 3 ≤ t1.phase.val := by
    dsimp only [t1]
    split_ifs with hG1 hG2
    · exact le_trans ht (doSplit_phase_nondec L K s t).2
    · exact le_trans ht (doSplit_phase_nondec L K t s).1
    · exact ht
  have hsum : Bias.toRat s1.bias + Bias.toRat t1.bias =
      Bias.toRat s.bias + Bias.toRat t.bias := by
    dsimp only [s1, t1]
    split_ifs with hG1 hG2
    · exact doSplit_bias_sum s t (hsres hG1.1)
    · have h := doSplit_bias_sum t s (htres hG2.1)
      linarith [h]
    · rfl
  have hfinal : Phase6Transition L K s t =
      (if s1.role = .clock then stdCounterSubroutine L K s1 else s1,
       if t1.role = .clock then stdCounterSubroutine L K t1 else t1) := rfl
  rw [hfinal]
  show Bias.toRat (if s1.role = .clock then stdCounterSubroutine L K s1 else s1).bias
      + Bias.toRat (if t1.role = .clock then stdCounterSubroutine L K t1 else t1).bias
      = Bias.toRat s.bias + Bias.toRat t.bias
  rw [clockGuard_bias s1 hs1p, clockGuard_bias t1 ht1p]
  exact hsum

/-! ## Phase 7 -/

/-- `cancelSplit` conserves the paired signed dyadic bias sum across all five
reaction branches (equal-index cancel, the two gap-1 mirrors, and the two gap-2
mirrors), plus the no-op fall-through. -/
private lemma cancelSplit_bias_sum (s t : AgentState L K) :
    Bias.toRat (cancelSplit L K s t).1.bias +
      Bias.toRat (cancelSplit L K s t).2.bias
      = Bias.toRat s.bias + Bias.toRat t.bias := by
  cases hs : s.bias with
  | zero => simp [cancelSplit, hs]
  | dyadic sgn_s i =>
    cases ht : t.bias with
    | zero => simp [cancelSplit, hs, ht]
    | dyadic sgn_t j =>
      cases sgn_s <;> cases sgn_t
      · simp [cancelSplit, hs, ht, Bias.toRat]
      · simp only [cancelSplit, hs, ht, Bias.toRat]
        split_ifs with h1 h2 h3 h4 h5 h6
        · dsimp only [Bias.toRat]; rw [h2]; ring
        · dsimp only [Bias.toRat]; rw [← h3]
          simp only [pow_add, pow_one]; field_simp; ring
        · dsimp only [Bias.toRat]; rw [← h4]
          simp only [pow_add, pow_one]; field_simp; ring
        · dsimp only [Bias.toRat]; rw [← h5]
          simp only [pow_add, pow_one]; field_simp; ring
        · dsimp only [Bias.toRat]; rw [← h6]
          simp only [pow_add, pow_one]; field_simp; ring
        · simp only [hs, ht]
        · simp only [hs, ht]
      · simp only [cancelSplit, hs, ht, Bias.toRat]
        split_ifs with h1 h2 h3 h4 h5 h6
        · dsimp only [Bias.toRat]; rw [h2]; ring
        · dsimp only [Bias.toRat]; rw [← h3]
          simp only [pow_add, pow_one]; field_simp; ring
        · dsimp only [Bias.toRat]; rw [← h4]
          simp only [pow_add, pow_one]; field_simp; ring
        · dsimp only [Bias.toRat]; rw [← h5]
          simp only [pow_add, pow_one]; field_simp; ring
        · dsimp only [Bias.toRat]; rw [← h6]
          simp only [pow_add, pow_one]; field_simp; ring
        · simp only [hs, ht]
        · simp only [hs, ht]
      · simp [cancelSplit, hs, ht, Bias.toRat]

/-- Phase 7 preserves the paired signed dyadic bias sum: the two-Main
cancel/split conserves mass (`cancelSplit_bias_sum`), and the tail clock guard
preserves bias. -/
theorem Phase7Transition_preserves_dyadicBiasSum_pair (s t : AgentState L K)
    (hs : 3 ≤ s.phase.val) (ht : 3 ≤ t.phase.val) :
    Bias.toRat (Phase7Transition L K s t).1.bias +
      Bias.toRat (Phase7Transition L K s t).2.bias =
    Bias.toRat s.bias + Bias.toRat t.bias := by
  let s1 := if s.role = .main ∧ t.role = .main then (cancelSplit L K s t).1 else s
  let t1 := if s.role = .main ∧ t.role = .main then (cancelSplit L K s t).2 else t
  have hs1p : 3 ≤ s1.phase.val := by
    dsimp only [s1]; split_ifs with h
    · exact le_trans hs (cancelSplit_phase_nondec L K s t).1
    · exact hs
  have ht1p : 3 ≤ t1.phase.val := by
    dsimp only [t1]; split_ifs with h
    · exact le_trans ht (cancelSplit_phase_nondec L K s t).2
    · exact ht
  have hsum : Bias.toRat s1.bias + Bias.toRat t1.bias =
      Bias.toRat s.bias + Bias.toRat t.bias := by
    dsimp only [s1, t1]; split_ifs with h
    · exact cancelSplit_bias_sum s t
    · rfl
  have hfinal : Phase7Transition L K s t =
      (if s1.role = .clock then stdCounterSubroutine L K s1 else s1,
       if t1.role = .clock then stdCounterSubroutine L K t1 else t1) := rfl
  rw [hfinal]
  show Bias.toRat (if s1.role = .clock then stdCounterSubroutine L K s1 else s1).bias
      + Bias.toRat (if t1.role = .clock then stdCounterSubroutine L K t1 else t1).bias
      = Bias.toRat s.bias + Bias.toRat t.bias
  rw [clockGuard_bias s1 hs1p, clockGuard_bias t1 ht1p]
  exact hsum

/-! ## Phase 2 / Phase 9 dispatch -/

/-- From phase ≥ 3, `advancePhaseWithInit` preserves `bias`: the destination
phase is ≥ 4, and `phaseInit` touches `bias` only at target phase 3. -/
private lemma advancePhaseWithInit_bias_of_phase_ge_three (a : AgentState L K)
    (h : 3 ≤ a.phase.val) : (advancePhaseWithInit L K a).bias = a.bias := by
  unfold advancePhaseWithInit
  rw [phaseInit_bias_of_phase_ge_four _ _ (advancePhase_phase_ge_four a h)]
  exact advancePhase_bias a

/-- Phase 2 (and hence Phase 9, which dispatches to it) preserves each agent's
`bias` from phase ≥ 3: it only rewrites `opinions`/`output`, or advances via
`advancePhaseWithInit`, whose init target ≥ 4 keeps `bias`. -/
theorem Phase2Transition_preserves_bias_pair_of_phase_ge_three
    (s t : AgentState L K) (hs : 3 ≤ s.phase.val) (ht : 3 ≤ t.phase.val) :
    (Phase2Transition L K s t).1.bias = s.bias ∧
      (Phase2Transition L K s t).2.bias = t.bias := by
  unfold Phase2Transition
  dsimp only
  split_ifs
  · exact ⟨advancePhaseWithInit_bias_of_phase_ge_three _ hs,
          advancePhaseWithInit_bias_of_phase_ge_three _ ht⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-! ## Phase 10 -/

/-- Phase 10 only rewrites `output` and `full`, so it preserves each agent's
`bias`. -/
theorem Phase10Transition_preserves_bias_pair (s t : AgentState L K) :
    (Phase10Transition L K s t).1.bias = s.bias ∧
      (Phase10Transition L K s t).2.bias = t.bias := by
  unfold Phase10Transition
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl⟩

/-! ## Axiom audit -/

#print axioms stdCounterSubroutine_bias_of_phase_ge_three
#print axioms Phase5Transition_preserves_dyadicBiasSum_pair
#print axioms Phase6Transition_preserves_dyadicBiasSum_pair
#print axioms Phase7Transition_preserves_dyadicBiasSum_pair
#print axioms Phase2Transition_preserves_bias_pair_of_phase_ge_three
#print axioms Phase10Transition_preserves_bias_pair

end MassPairPhases
end Ripple.PopulationProtocol.ExactMajority
