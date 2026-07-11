/-
Deterministic phase-chain assembly lemmas for the Doty et al. exact-majority
protocol.

This module composes local phase-progress witnesses with the phase epidemic.
It deliberately proves only the chain fragments justified by the current
formal interfaces: timed-phase progress produces an agent in the next phase,
then the epidemic can synchronize the configuration to a common phase at least
that high.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.PhaseProgress
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Phase10Backup
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.StableEndpoints

open Multiset

namespace ExactMajority

variable {L K : ℕ}

private lemma phase_le_maxPhase_of_mem_chain {c : Config (AgentState L K)}
    {a : AgentState L K} (ha : a ∈ c) :
    a.phase.val ≤ maxPhase c := by
  unfold maxPhase
  exact Finset.le_sup (f := fun a : AgentState L K => a.phase.val) (by simpa using ha)

private lemma maxPhase_le_ten_chain (c : Config (AgentState L K)) :
    maxPhase c ≤ 10 := by
  unfold maxPhase
  refine Finset.sup_le ?_
  intro a _ha
  exact Nat.le_of_lt_succ a.phase.isLt

private def clockCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.role = .clock) c

private lemma countP_singleton_of_dc
    {α : Type*} {p : α → Prop} [DecidablePred p] {a : α} (ha : p a) :
    Multiset.countP p ({a} : Multiset α) = 1 := by
  have h :
      Multiset.countP p ({a} : Multiset α) =
        Multiset.card ({a} : Multiset α) :=
    (Multiset.countP_eq_card (p := p) (s := ({a} : Multiset α))).2
      (by
        intro b hb
        have hb_eq : b = a := by simpa using hb
        simpa [hb_eq] using ha)
  simpa using h

private lemma countP_singleton_of_dc_not
    {α : Type*} {p : α → Prop} [DecidablePred p] {a : α} (ha : ¬ p a) :
    Multiset.countP p ({a} : Multiset α) = 0 :=
  (Multiset.countP_eq_zero (p := p) (s := ({a} : Multiset α))).2
    (by
      intro b hb hp
      have hb_eq : b = a := by simpa using hb
      exact ha (by simpa [hb_eq] using hp))

private theorem pair_le_of_mem_ne
    {α : Type*} [DecidableEq α] {c : Multiset α} {a b : α}
    (ha : a ∈ c) (hb : b ∈ c) (hne : a ≠ b) :
    ({a, b} : Multiset α) ≤ c := by
  have hnot : a ∉ ({b} : Multiset α) := by
    simp [hne]
  change a ::ₘ ({b} : Multiset α) ≤ c
  rw [Multiset.cons_le_of_notMem hnot]
  exact ⟨ha, Multiset.singleton_le.2 hb⟩

private lemma exists_applicable_pair_left_of_mem_card_ge_two
    {c : Config (AgentState L K)} {a : AgentState L K}
    (ha : a ∈ c) (hcard : 2 ≤ c.card) :
    ∃ b, Protocol.Applicable c a b := by
  have herase_pos : 0 < (c.erase a).card := by
    have hcard_erase := Multiset.card_erase_add_one ha
    omega
  rcases Multiset.card_pos_iff_exists_mem.mp herase_pos with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  change a ::ₘ ({b} : Multiset (AgentState L K)) ≤ c
  rw [← Multiset.cons_erase ha]
  exact Multiset.cons_le_cons a (Multiset.singleton_le.mpr hb)

private lemma hasMinusOne_opinionsUnion_left
    (x y : Fin 8) (hx : hasMinusOne x = true) :
    hasMinusOne (opinionsUnion x y) = true := by
  fin_cases x <;> simp [hasMinusOne] at hx ⊢ <;> fin_cases y <;> decide

private lemma hasPlusOne_opinionsUnion_left
    (x y : Fin 8) (hx : hasPlusOne x = true) :
    hasPlusOne (opinionsUnion x y) = true := by
  fin_cases x <;> simp [hasPlusOne] at hx ⊢ <;> fin_cases y <;> decide

private lemma hasPlusOne_opinionsUnion_right
    (x y : Fin 8) (hy : hasPlusOne y = true) :
    hasPlusOne (opinionsUnion x y) = true := by
  fin_cases y <;> simp [hasPlusOne] at hy ⊢ <;> fin_cases x <;> decide

private lemma hasMinusOne_opinionsUnion_right
    (x y : Fin 8) (hy : hasMinusOne y = true) :
    hasMinusOne (opinionsUnion x y) = true := by
  fin_cases y <;> simp [hasMinusOne] at hy ⊢ <;> fin_cases x <;> decide

private lemma hasPlusOne_opinionsUnion_false_chain
    (x y : Fin 8) (hx : hasPlusOne x = false) (hy : hasPlusOne y = false) :
    hasPlusOne (opinionsUnion x y) = false := by
  fin_cases x <;> simp [hasPlusOne] at hx ⊢ <;>
    fin_cases y <;> simp [opinionsUnion, hasPlusOne] at hy ⊢

private lemma hasMinusOne_opinionsUnion_false_chain
    (x y : Fin 8) (hx : hasMinusOne x = false) (hy : hasMinusOne y = false) :
    hasMinusOne (opinionsUnion x y) = false := by
  fin_cases x <;> simp [hasMinusOne] at hx ⊢ <;>
    fin_cases y <;> simp [opinionsUnion, hasMinusOne] at hy ⊢

private lemma no_phase4HasBigBias_iff
    (a : AgentState L K) :
    ¬ phase4HasBigBias (L := L) (K := K) a ↔
      ∀ sgn i, a.bias = Bias.dyadic sgn i → ¬ i.val < L := by
  constructor
  · intro h sgn i hbias hi
    exact h ⟨sgn, i, hbias, hi⟩
  · intro h hbig
    rcases hbig with ⟨sgn, i, hbias, hi⟩
    exact h sgn i hbias hi

theorem phaseInit_two_hasPlusOne_of_smallBias_pos_one
    (a : AgentState L K) (hsmall : a.smallBias.val = 4) :
    hasPlusOne (phaseInit L K ⟨2, by decide⟩ a).opinions = true := by
  unfold phaseInit
  simp [hsmall, hasPlusOne]

theorem phaseInit_two_hasMinusOne_of_smallBias_neg_one
    (a : AgentState L K) (hsmall : a.smallBias.val = 2) :
    hasMinusOne (phaseInit L K ⟨2, by decide⟩ a).opinions = true := by
  unfold phaseInit
  simp [hsmall, hasMinusOne]

theorem phaseInit_two_opinion_eq_zero_of_smallBias_zero
    (a : AgentState L K) (hsmall : a.smallBias.val = 3) :
    (phaseInit L K ⟨2, by decide⟩ a).opinions = phase2OpinionT := by
  unfold phaseInit phase2OpinionT
  simp [hsmall]

private theorem phaseInit_two_hasPlusOne_false_of_not_pos
    (a : AgentState L K)
    (hphase : (phaseInit L K ⟨2, by decide⟩ a).phase.val = 2)
    (hsmall : ¬ 3 < (phaseInit L K ⟨2, by decide⟩ a).smallBias.val) :
    hasPlusOne (phaseInit L K ⟨2, by decide⟩ a).opinions = false := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  fin_cases smallBias <;>
    simp [phaseInit, enterPhase10, hasPlusOne] at hphase hsmall ⊢

private theorem phaseInit_two_hasMinusOne_false_of_not_neg
    (a : AgentState L K)
    (hphase : (phaseInit L K ⟨2, by decide⟩ a).phase.val = 2)
    (hsmall : ¬ (phaseInit L K ⟨2, by decide⟩ a).smallBias.val < 3) :
    hasMinusOne (phaseInit L K ⟨2, by decide⟩ a).opinions = false := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  fin_cases smallBias <;>
    simp [phaseInit, enterPhase10, hasMinusOne] at hphase hsmall ⊢

private lemma opinionsUnion_phase2OpinionT_self :
    opinionsUnion phase2OpinionT phase2OpinionT = phase2OpinionT := by
  apply Fin.ext
  decide

private def phase2NeutralSupport (a : AgentState L K) : Prop :=
  a.smallBias.val = 3 → a.opinions = phase2OpinionT

private theorem phase2NeutralSupport_phaseInit_two
    (a : AgentState L K) :
    phase2NeutralSupport (phaseInit L K ⟨2, by decide⟩ a) := by
  intro hsmall
  have hpres := phaseInit_preserves_smallBias (L := L) (K := K)
    ⟨2, by decide⟩ a
  exact phaseInit_two_opinion_eq_zero_of_smallBias_zero (L := L) (K := K) a
    (by simpa [← hpres] using hsmall)

private theorem Phase2Transition_neutral_left
    (a b : AgentState L K)
    (ha : phase2NeutralSupport a) (hb : phase2NeutralSupport b)
    (hsmall_a : (Phase2Transition L K a b).1.smallBias.val = 3)
    (hsmall_b : (Phase2Transition L K a b).2.smallBias.val = 3) :
    (Phase2Transition L K a b).1.opinions = phase2OpinionT := by
  have hsmall := Phase2Transition_preserves_smallBias (L := L) (K := K) a b
  have ha_op : a.opinions = phase2OpinionT := ha (by simpa [hsmall.1] using hsmall_a)
  have hb_op : b.opinions = phase2OpinionT := hb (by simpa [hsmall.2] using hsmall_b)
  have hunion : opinionsUnion a.opinions b.opinions = phase2OpinionT := by
    simpa [ha_op, hb_op] using opinionsUnion_phase2OpinionT_self
  simp [Phase2Transition, hunion, phase2OpinionT, hasMinusOne, hasPlusOne]

private theorem Phase2Transition_neutral_right
    (a b : AgentState L K)
    (ha : phase2NeutralSupport a) (hb : phase2NeutralSupport b)
    (hsmall_a : (Phase2Transition L K a b).1.smallBias.val = 3)
    (hsmall_b : (Phase2Transition L K a b).2.smallBias.val = 3) :
    (Phase2Transition L K a b).2.opinions = phase2OpinionT := by
  have hsmall := Phase2Transition_preserves_smallBias (L := L) (K := K) a b
  have ha_op : a.opinions = phase2OpinionT := ha (by simpa [hsmall.1] using hsmall_a)
  have hb_op : b.opinions = phase2OpinionT := hb (by simpa [hsmall.2] using hsmall_b)
  have hunion : opinionsUnion a.opinions b.opinions = phase2OpinionT := by
    simpa [ha_op, hb_op] using opinionsUnion_phase2OpinionT_self
  simp [Phase2Transition, hunion, phase2OpinionT, hasMinusOne, hasPlusOne]

private theorem Phase10Transition_preserves_smallBias_pair
    (s t : AgentState L K) :
    (Phase10Transition L K s t).1.smallBias = s.smallBias ∧
      (Phase10Transition L K s t).2.smallBias = t.smallBias := by
  unfold Phase10Transition
  dsimp only
  refine ⟨?_, ?_⟩ <;> split_ifs <;> simp_all

private lemma phase3CancelSplit_preserves_smallBias_pair
    (s t : AgentState L K) :
    (phase3CancelSplit L K s t).1.smallBias = s.smallBias ∧
      (phase3CancelSplit L K s t).2.smallBias = t.smallBias := by
  unfold phase3CancelSplit
  match s.bias, t.bias with
  | .zero, .zero => simp
  | .zero, .dyadic _ _ => simp; split_ifs <;> simp
  | .dyadic _ _, .zero => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .neg _ => simp

private lemma Phase3Transition_preserves_smallBias_pair
    (s t : AgentState L K) :
    (Phase3Transition L K s t).1.smallBias = s.smallBias ∧
      (Phase3Transition L K s t).2.smallBias = t.smallBias := by
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
    have h_hour_lt : hVal < L + 1 :=
      (Nat.max_lt).mpr ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 :=
      (Nat.max_lt).mpr ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1 : s1.smallBias = s.smallBias := by
    dsimp [s1]
    split_ifs <;> simp [stdCounterSubroutine_smallBias]
  have ht1 : t1.smallBias = t.smallBias := by
    dsimp [t1]
    split_ifs <;> simp [stdCounterSubroutine_smallBias]
  have hs2 : s2.smallBias = s1.smallBias := by
    dsimp [s2]
    split_ifs <;> simp
  have ht2 : t2.smallBias = t1.smallBias := by
    dsimp [t2]
    split_ifs <;> simp
  rcases phase3CancelSplit_preserves_smallBias_pair (L := L) (K := K) s2 t2 with
    ⟨hcs_s, hcs_t⟩
  unfold Phase3Transition
  change
    (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
      else (s2, t2)).1.smallBias = s.smallBias ∧
    (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
      else (s2, t2)).2.smallBias = t.smallBias
  by_cases hmain : s2.role = .main ∧ t2.role = .main
  · simp [hmain, hcs_s, hcs_t, hs2, ht2, hs1, ht1]
  · simp [hmain, hs2, ht2, hs1, ht1]

private lemma doSplit_preserves_smallBias_pair
    (r m : AgentState L K) :
    (doSplit L K r m).1.smallBias = r.smallBias ∧
      (doSplit L K r m).2.smallBias = m.smallBias := by
  unfold doSplit
  match m.bias with
  | .zero => simp
  | .dyadic _ _ => simp; split_ifs <;> simp

private lemma cancelSplit_preserves_smallBias_pair
    (s t : AgentState L K) :
    (cancelSplit L K s t).1.smallBias = s.smallBias ∧
      (cancelSplit L K s t).2.smallBias = t.smallBias := by
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic _ _, .dyadic _ _ => simp; split_ifs <;> simp

private lemma absorbConsume_preserves_smallBias_pair
    (s t : AgentState L K) :
    (absorbConsume L K s t).1.smallBias = s.smallBias ∧
      (absorbConsume L K s t).2.smallBias = t.smallBias := by
  unfold absorbConsume
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp

private lemma Phase5Transition_preserves_smallBias_pair
    (s t : AgentState L K) :
    (Phase5Transition L K s t).1.smallBias = s.smallBias ∧
      (Phase5Transition L K s t).2.smallBias = t.smallBias := by
  unfold Phase5Transition
  dsimp only
  constructor <;> split_ifs <;> simp [stdCounterSubroutine_smallBias]

private lemma Phase6Transition_preserves_smallBias_pair
    (s t : AgentState L K) :
    (Phase6Transition L K s t).1.smallBias = s.smallBias ∧
      (Phase6Transition L K s t).2.smallBias = t.smallBias := by
  unfold Phase6Transition
  dsimp only
  constructor <;> split_ifs <;>
    simp [stdCounterSubroutine_smallBias, doSplit_preserves_smallBias_pair]

private lemma Phase7Transition_preserves_smallBias_pair
    (s t : AgentState L K) :
    (Phase7Transition L K s t).1.smallBias = s.smallBias ∧
      (Phase7Transition L K s t).2.smallBias = t.smallBias := by
  unfold Phase7Transition
  dsimp only
  constructor <;> split_ifs <;>
    simp [stdCounterSubroutine_smallBias, cancelSplit_preserves_smallBias_pair]

private lemma Phase8Transition_preserves_smallBias_pair
    (s t : AgentState L K) :
    (Phase8Transition L K s t).1.smallBias = s.smallBias ∧
      (Phase8Transition L K s t).2.smallBias = t.smallBias := by
  unfold Phase8Transition
  dsimp only
  constructor <;> split_ifs <;>
    simp [stdCounterSubroutine_smallBias, absorbConsume_preserves_smallBias_pair]

private theorem Transition_left_smallBias_eq_of_phase2_to_phase2
    (s t : AgentState L K) (hs : s.phase.val = 2)
    (hphase : (Transition L K s t).1.phase.val = 2) :
    (Transition L K s t).1.smallBias = s.smallBias := by
  have ht_le : t.phase.val ≤ 2 := by
    have hmax := Transition_left_phase_ge_pair_max (L := L) (K := K) s t
    rw [hphase] at hmax
    omega
  have hs_epi_not_high :=
    phaseEpidemicUpdate_left_phase_le_two_or_ten_of_phases_le_two
      (L := L) (K := K) s t (by omega) ht_le
  have hs_epi_ge :=
    phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
  have hs_epi_small := (phaseEpidemicUpdate_preserves_smallBias L K s t).1
  unfold Transition
  generalize he : phaseEpidemicUpdate L K s t = e
  rcases e with ⟨s', t'⟩
  have hs'_not_high : s'.phase.val ≤ 2 ∨ s'.phase.val = 10 := by
    simpa [he] using hs_epi_not_high
  have hs'_ge : 2 ≤ s'.phase.val := by
    have hge : max s.phase.val t.phase.val ≤ s'.phase.val := by
      simpa [he] using hs_epi_ge
    omega
  have hs'_small : s'.smallBias = s.smallBias := by
    simpa [he] using hs_epi_small
  simp [Transition, he] at hphase
  change
    (finishPhase10Entry L K s'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).1).smallBias = s.smallBias
  generalize hp : s'.phase = p
  fin_cases p
  · have : s'.phase.val = 0 := by simpa [hp]
    omega
  · have : s'.phase.val = 1 := by simpa [hp]
    omega
  · have hsmall := (Phase2Transition_preserves_smallBias L K s' t').1
    change (finishPhase10Entry L K s' (Phase2Transition L K s' t').1).smallBias =
      s.smallBias
    unfold finishPhase10Entry
    by_cases hfinish :
        s'.phase.val < 10 ∧ (Phase2Transition L K s' t').1.phase.val = 10
    · have hbad : (enterPhase10 L K (Phase2Transition L K s' t').1).phase.val = 2 := by
        simpa [hp, hfinish] using hphase
      simp [enterPhase10_phase_val] at hbad
    · simp [hfinish, hsmall, hs'_small]
  · have : s'.phase.val = 3 := by simpa [hp]
    rcases hs'_not_high with h | h <;> omega
  · have : s'.phase.val = 4 := by simpa [hp]
    rcases hs'_not_high with h | h <;> omega
  · have : s'.phase.val = 5 := by simpa [hp]
    rcases hs'_not_high with h | h <;> omega
  · have : s'.phase.val = 6 := by simpa [hp]
    rcases hs'_not_high with h | h <;> omega
  · have : s'.phase.val = 7 := by simpa [hp]
    rcases hs'_not_high with h | h <;> omega
  · have : s'.phase.val = 8 := by simpa [hp]
    rcases hs'_not_high with h | h <;> omega
  · have : s'.phase.val = 9 := by simpa [hp]
    rcases hs'_not_high with h | h <;> omega
  · have hmono := (Phase10Transition_phase_nondec (L := L) (K := K) s' t').1
    have hout : (Phase10Transition L K s' t').1.phase.val = 2 := by
      simpa [hp] using hphase
    have hpval : s'.phase.val = 10 := by simpa [hp]
    omega

private theorem Transition_right_smallBias_eq_of_phase2_to_phase2
    (s t : AgentState L K) (ht : t.phase.val = 2)
    (hphase : (Transition L K s t).2.phase.val = 2) :
    (Transition L K s t).2.smallBias = t.smallBias := by
  have hs_le : s.phase.val ≤ 2 := by
    have hmax := Transition_right_phase_ge_pair_max (L := L) (K := K) s t
    rw [hphase] at hmax
    omega
  have ht_epi_not_high :=
    phaseEpidemicUpdate_right_phase_le_two_or_ten_of_phases_le_two
      (L := L) (K := K) s t hs_le (by omega)
  have ht_epi_ge :=
    phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) s t
  have ht_epi_small := (phaseEpidemicUpdate_preserves_smallBias L K s t).2
  have hs_epi_not_high :=
    phaseEpidemicUpdate_left_phase_le_two_or_ten_of_phases_le_two
      (L := L) (K := K) s t hs_le (by omega)
  have hs_epi_ge :=
    phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
  unfold Transition
  generalize he : phaseEpidemicUpdate L K s t = e
  rcases e with ⟨s', t'⟩
  have ht'_not_high : t'.phase.val ≤ 2 ∨ t'.phase.val = 10 := by
    simpa [he] using ht_epi_not_high
  have ht'_ge : 2 ≤ t'.phase.val := by
    have hge : max s.phase.val t.phase.val ≤ t'.phase.val := by
      simpa [he] using ht_epi_ge
    omega
  have hs'_not_high : s'.phase.val ≤ 2 ∨ s'.phase.val = 10 := by
    simpa [he] using hs_epi_not_high
  have hs'_ge : 2 ≤ s'.phase.val := by
    have hge : max s.phase.val t.phase.val ≤ s'.phase.val := by
      simpa [he] using hs_epi_ge
    omega
  have ht'_small : t'.smallBias = t.smallBias := by
    simpa [he] using ht_epi_small
  simp [Transition, he] at hphase
  change
    (finishPhase10Entry L K t'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).2).smallBias = t.smallBias
  generalize hp : s'.phase = p
  fin_cases p
  · have : s'.phase.val = 0 := by simpa [hp]
    omega
  · have : s'.phase.val = 1 := by simpa [hp]
    omega
  · have hsmall := (Phase2Transition_preserves_smallBias L K s' t').2
    change (finishPhase10Entry L K t' (Phase2Transition L K s' t').2).smallBias =
      t.smallBias
    unfold finishPhase10Entry
    by_cases hfinish :
        t'.phase.val < 10 ∧ (Phase2Transition L K s' t').2.phase.val = 10
    · have hbad : (enterPhase10 L K (Phase2Transition L K s' t').2).phase.val = 2 := by
        simpa [hp, hfinish] using hphase
      simp [enterPhase10_phase_val] at hbad
    · simp [hfinish, hsmall, ht'_small]
  · have : s'.phase.val = 3 := by simpa [hp]
    rcases hs'_not_high with h | h <;> omega
  · have : s'.phase.val = 4 := by simpa [hp]
    rcases hs'_not_high with h | h <;> omega
  · have : s'.phase.val = 5 := by simpa [hp]
    rcases hs'_not_high with h | h <;> omega
  · have : s'.phase.val = 6 := by simpa [hp]
    rcases hs'_not_high with h | h <;> omega
  · have : s'.phase.val = 7 := by simpa [hp]
    rcases hs'_not_high with h | h <;> omega
  · have : s'.phase.val = 8 := by simpa [hp]
    rcases hs'_not_high with h | h <;> omega
  · have : s'.phase.val = 9 := by simpa [hp]
    rcases hs'_not_high with h | h <;> omega
  · have hpval : s'.phase.val = 10 := by simpa [hp]
    by_cases ht2 : t'.phase.val = 2
    · have hsmall := (Phase10Transition_preserves_smallBias_pair
        (L := L) (K := K) s' t').2
      have hphase_eq := (Phase10Transition_phase_eq (L := L) (K := K) s' t').2
      have hafter_ne : (Phase10Transition L K s' t').2.phase.val ≠ 10 := by
        rw [hphase_eq]
        omega
      simp [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K)
        t' (Phase10Transition L K s' t').2 hafter_ne, hsmall, ht'_small]
    · have ht10 : t'.phase.val = 10 := by
        rcases ht'_not_high with hle | hten
        · omega
        · exact hten
      have hmono := (Phase10Transition_phase_nondec (L := L) (K := K) s' t').2
      have hout : (Phase10Transition L K s' t').2.phase.val = 2 := by
        simpa [hp] using hphase
      omega

private theorem Transition_left_smallBias_eq_epidemic_of_epidemic_phase_ge_two
    (s t : AgentState L K)
    (hep_ge2 : 2 ≤ (phaseEpidemicUpdate L K s t).1.phase.val) :
    (Transition L K s t).1.smallBias = (phaseEpidemicUpdate L K s t).1.smallBias := by
  have hs'_small := (phaseEpidemicUpdate_preserves_smallBias L K s t).1
  unfold Transition
  generalize he : phaseEpidemicUpdate L K s t = e
  rcases e with ⟨s', t'⟩
  have hs'_ge : 2 ≤ s'.phase.val := by simpa [he] using hep_ge2
  change
    (finishPhase10Entry L K s'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).1).smallBias = s'.smallBias
  generalize hp : s'.phase = p
  fin_cases p
  · have : s'.phase.val = 0 := by simpa [hp]
    omega
  · have : s'.phase.val = 1 := by simpa [hp]
    omega
  all_goals first
    | (have hsmall := (Phase2Transition_preserves_smallBias L K s' t').1
       simpa [hp, finishPhase10Entry_smallBias, hsmall])
    | (have hsmall := (Phase3Transition_preserves_smallBias_pair (L := L) (K := K) s' t').1
       simpa [hp, finishPhase10Entry_smallBias, hsmall])
    | (have hsmall := (Phase4Transition_preserves_smallBias L K s' t').1
       simpa [hp, finishPhase10Entry_smallBias, hsmall])
    | (have hsmall := (Phase5Transition_preserves_smallBias_pair (L := L) (K := K) s' t').1
       simpa [hp, finishPhase10Entry_smallBias, hsmall])
    | (have hsmall := (Phase6Transition_preserves_smallBias_pair (L := L) (K := K) s' t').1
       simpa [hp, finishPhase10Entry_smallBias, hsmall])
    | (have hsmall := (Phase7Transition_preserves_smallBias_pair (L := L) (K := K) s' t').1
       simpa [hp, finishPhase10Entry_smallBias, hsmall])
    | (have hsmall := (Phase8Transition_preserves_smallBias_pair (L := L) (K := K) s' t').1
       simpa [hp, finishPhase10Entry_smallBias, hsmall])
    | (have hsmall := (Phase9Transition_preserves_smallBias L K s' t').1
       simpa [hp, finishPhase10Entry_smallBias, hsmall])
    | (have hsmall := (Phase10Transition_preserves_smallBias_pair (L := L) (K := K) s' t').1
       simpa [hp, finishPhase10Entry_smallBias, hsmall])

private theorem Transition_right_smallBias_eq_epidemic_of_epidemic_phase_ge_two
    (s t : AgentState L K)
    (hep_ge2 : 2 ≤ (phaseEpidemicUpdate L K s t).1.phase.val) :
    (Transition L K s t).2.smallBias = (phaseEpidemicUpdate L K s t).2.smallBias := by
  have ht'_small := (phaseEpidemicUpdate_preserves_smallBias L K s t).2
  unfold Transition
  generalize he : phaseEpidemicUpdate L K s t = e
  rcases e with ⟨s', t'⟩
  have hs'_ge : 2 ≤ s'.phase.val := by simpa [he] using hep_ge2
  change
    (finishPhase10Entry L K t'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).2).smallBias = t'.smallBias
  generalize hp : s'.phase = p
  fin_cases p
  · have : s'.phase.val = 0 := by simpa [hp]
    omega
  · have : s'.phase.val = 1 := by simpa [hp]
    omega
  all_goals first
    | (have hsmall := (Phase2Transition_preserves_smallBias L K s' t').2
       simpa [hp, finishPhase10Entry_smallBias, hsmall])
    | (have hsmall := (Phase3Transition_preserves_smallBias_pair (L := L) (K := K) s' t').2
       simpa [hp, finishPhase10Entry_smallBias, hsmall])
    | (have hsmall := (Phase4Transition_preserves_smallBias L K s' t').2
       simpa [hp, finishPhase10Entry_smallBias, hsmall])
    | (have hsmall := (Phase5Transition_preserves_smallBias_pair (L := L) (K := K) s' t').2
       simpa [hp, finishPhase10Entry_smallBias, hsmall])
    | (have hsmall := (Phase6Transition_preserves_smallBias_pair (L := L) (K := K) s' t').2
       simpa [hp, finishPhase10Entry_smallBias, hsmall])
    | (have hsmall := (Phase7Transition_preserves_smallBias_pair (L := L) (K := K) s' t').2
       simpa [hp, finishPhase10Entry_smallBias, hsmall])
    | (have hsmall := (Phase8Transition_preserves_smallBias_pair (L := L) (K := K) s' t').2
       simpa [hp, finishPhase10Entry_smallBias, hsmall])
    | (have hsmall := (Phase9Transition_preserves_smallBias L K s' t').2
       simpa [hp, finishPhase10Entry_smallBias, hsmall])
    | (have hsmall := (Phase10Transition_preserves_smallBias_pair (L := L) (K := K) s' t').2
       simpa [hp, finishPhase10Entry_smallBias, hsmall])

private theorem stdCounterSubroutine_phase2_opinion_T_of_smallBias_three
    (a : AgentState L K) (hphase_one : a.phase.val = 1)
    (hphase_two : (stdCounterSubroutine L K a).phase.val = 2)
    (hsmall : (stdCounterSubroutine L K a).smallBias.val = 3) :
    (stdCounterSubroutine L K a).opinions = phase2OpinionT := by
  by_cases hcounter : a.counter.val = 0
  · have hsmall_phase :
        (phaseInit L K ⟨2, by decide⟩ ({ a with phase := ⟨2, by decide⟩ })).smallBias.val = 3 := by
      simpa [stdCounterSubroutine, hcounter, advancePhaseWithInit, advancePhase,
        hphase_one] using hsmall
    have hsmall_pre :
        ({ a with phase := ⟨2, by decide⟩ } : AgentState L K).smallBias.val = 3 := by
      have hpres := phaseInit_preserves_smallBias (L := L) (K := K)
        ⟨2, by decide⟩ ({ a with phase := ⟨2, by decide⟩ })
      rw [hpres] at hsmall_phase
      exact hsmall_phase
    simp [stdCounterSubroutine, hcounter, advancePhaseWithInit, advancePhase,
      hphase_one] at hphase_two ⊢
    exact phaseInit_two_opinion_eq_zero_of_smallBias_zero (L := L) (K := K)
      ({ a with phase := ⟨2, by decide⟩ }) hsmall_pre
  · simp [stdCounterSubroutine, hcounter] at hphase_two
    omega

private theorem clockCounterStep_phase2_opinion_T_of_smallBias_three
    (a : AgentState L K) (hphase_one : a.phase.val = 1)
    (hphase_two : (clockCounterStep L K a).phase.val = 2)
    (hsmall : (clockCounterStep L K a).smallBias.val = 3) :
    (clockCounterStep L K a).opinions = phase2OpinionT := by
  by_cases hclock : a.role = .clock
  · have hsmall' : (stdCounterSubroutine L K a).smallBias.val = 3 := by
      simpa [clockCounterStep, hclock] using hsmall
    simp [clockCounterStep, hclock] at hphase_two ⊢
    exact stdCounterSubroutine_phase2_opinion_T_of_smallBias_three
      (L := L) (K := K) a hphase_one hphase_two hsmall'
  · simp [clockCounterStep, hclock] at hphase_two
    omega

private theorem Phase1Transition_left_phase2_opinion_T_of_smallBias_three
    (s t : AgentState L K) (hs_phase : s.phase.val = 1)
    (hphase : (Phase1Transition L K s t).1.phase.val = 2)
    (hsmall : (Phase1Transition L K s t).1.smallBias.val = 3) :
    (Phase1Transition L K s t).1.opinions = phase2OpinionT := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · simp [Phase1Transition, hmain, clockCounterStep, hs_phase] at hphase
  · have hsmall' : (clockCounterStep L K s).smallBias.val = 3 := by
      simpa [Phase1Transition, hmain] using hsmall
    simp [Phase1Transition, hmain] at hphase ⊢
    exact clockCounterStep_phase2_opinion_T_of_smallBias_three
      (L := L) (K := K) s hs_phase hphase hsmall'

private theorem Phase1Transition_right_phase2_opinion_T_of_smallBias_three
    (s t : AgentState L K) (ht_phase : t.phase.val = 1)
    (hphase : (Phase1Transition L K s t).2.phase.val = 2)
    (hsmall : (Phase1Transition L K s t).2.smallBias.val = 3) :
    (Phase1Transition L K s t).2.opinions = phase2OpinionT := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · simp [Phase1Transition, hmain, clockCounterStep, ht_phase] at hphase
  · have hsmall' : (clockCounterStep L K t).smallBias.val = 3 := by
      simpa [Phase1Transition, hmain] using hsmall
    simp [Phase1Transition, hmain] at hphase ⊢
    exact clockCounterStep_phase2_opinion_T_of_smallBias_three
      (L := L) (K := K) t ht_phase hphase hsmall'

private theorem stdCounterSubroutine_phase2_noPlus_of_not_pos
    (a : AgentState L K) (hphase_one : a.phase.val = 1)
    (hphase_two : (stdCounterSubroutine L K a).phase.val = 2)
    (hsmall : ¬ 3 < (stdCounterSubroutine L K a).smallBias.val) :
    hasPlusOne (stdCounterSubroutine L K a).opinions = false := by
  by_cases hcounter : a.counter.val = 0
  · have hphase_init :
        (phaseInit L K ⟨2, by decide⟩ ({ a with phase := ⟨2, by decide⟩ })).phase.val = 2 := by
      simpa [stdCounterSubroutine, hcounter, advancePhaseWithInit, advancePhase,
        hphase_one] using hphase_two
    have hsmall_init :
        ¬ 3 <
          (phaseInit L K ⟨2, by decide⟩ ({ a with phase := ⟨2, by decide⟩ })).smallBias.val := by
      simpa [stdCounterSubroutine, hcounter, advancePhaseWithInit, advancePhase,
        hphase_one] using hsmall
    simp [stdCounterSubroutine, hcounter, advancePhaseWithInit, advancePhase,
      hphase_one] at hphase_two ⊢
    exact phaseInit_two_hasPlusOne_false_of_not_pos (L := L) (K := K)
      ({ a with phase := ⟨2, by decide⟩ }) hphase_init hsmall_init
  · simp [stdCounterSubroutine, hcounter] at hphase_two
    omega

private theorem stdCounterSubroutine_phase2_noMinus_of_not_neg
    (a : AgentState L K) (hphase_one : a.phase.val = 1)
    (hphase_two : (stdCounterSubroutine L K a).phase.val = 2)
    (hsmall : ¬ (stdCounterSubroutine L K a).smallBias.val < 3) :
    hasMinusOne (stdCounterSubroutine L K a).opinions = false := by
  by_cases hcounter : a.counter.val = 0
  · have hphase_init :
        (phaseInit L K ⟨2, by decide⟩ ({ a with phase := ⟨2, by decide⟩ })).phase.val = 2 := by
      simpa [stdCounterSubroutine, hcounter, advancePhaseWithInit, advancePhase,
        hphase_one] using hphase_two
    have hsmall_init :
        ¬ (phaseInit L K ⟨2, by decide⟩ ({ a with phase := ⟨2, by decide⟩ })).smallBias.val < 3 := by
      simpa [stdCounterSubroutine, hcounter, advancePhaseWithInit, advancePhase,
        hphase_one] using hsmall
    simp [stdCounterSubroutine, hcounter, advancePhaseWithInit, advancePhase,
      hphase_one] at hphase_two ⊢
    exact phaseInit_two_hasMinusOne_false_of_not_neg (L := L) (K := K)
      ({ a with phase := ⟨2, by decide⟩ }) hphase_init hsmall_init
  · simp [stdCounterSubroutine, hcounter] at hphase_two
    omega

private theorem clockCounterStep_phase2_noPlus_of_not_pos
    (a : AgentState L K) (hphase_one : a.phase.val = 1)
    (hphase_two : (clockCounterStep L K a).phase.val = 2)
    (hsmall : ¬ 3 < (clockCounterStep L K a).smallBias.val) :
    hasPlusOne (clockCounterStep L K a).opinions = false := by
  by_cases hclock : a.role = .clock
  · have hsmall' : ¬ 3 < (stdCounterSubroutine L K a).smallBias.val := by
      simpa [clockCounterStep, hclock] using hsmall
    simp [clockCounterStep, hclock] at hphase_two ⊢
    exact stdCounterSubroutine_phase2_noPlus_of_not_pos
      (L := L) (K := K) a hphase_one hphase_two hsmall'
  · simp [clockCounterStep, hclock] at hphase_two
    omega

private theorem clockCounterStep_phase2_noMinus_of_not_neg
    (a : AgentState L K) (hphase_one : a.phase.val = 1)
    (hphase_two : (clockCounterStep L K a).phase.val = 2)
    (hsmall : ¬ (clockCounterStep L K a).smallBias.val < 3) :
    hasMinusOne (clockCounterStep L K a).opinions = false := by
  by_cases hclock : a.role = .clock
  · have hsmall' : ¬ (stdCounterSubroutine L K a).smallBias.val < 3 := by
      simpa [clockCounterStep, hclock] using hsmall
    simp [clockCounterStep, hclock] at hphase_two ⊢
    exact stdCounterSubroutine_phase2_noMinus_of_not_neg
      (L := L) (K := K) a hphase_one hphase_two hsmall'
  · simp [clockCounterStep, hclock] at hphase_two
    omega

private theorem Phase1Transition_left_phase2_noPlus_of_not_pos
    (s t : AgentState L K) (hs_phase : s.phase.val = 1)
    (hphase : (Phase1Transition L K s t).1.phase.val = 2)
    (hsmall : ¬ 3 < (Phase1Transition L K s t).1.smallBias.val) :
    hasPlusOne (Phase1Transition L K s t).1.opinions = false := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · simp [Phase1Transition, hmain, clockCounterStep, hs_phase] at hphase
  · have hsmall' : ¬ 3 < (clockCounterStep L K s).smallBias.val := by
      simpa [Phase1Transition, hmain] using hsmall
    simp [Phase1Transition, hmain] at hphase ⊢
    exact clockCounterStep_phase2_noPlus_of_not_pos
      (L := L) (K := K) s hs_phase hphase hsmall'

private theorem Phase1Transition_right_phase2_noPlus_of_not_pos
    (s t : AgentState L K) (ht_phase : t.phase.val = 1)
    (hphase : (Phase1Transition L K s t).2.phase.val = 2)
    (hsmall : ¬ 3 < (Phase1Transition L K s t).2.smallBias.val) :
    hasPlusOne (Phase1Transition L K s t).2.opinions = false := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · simp [Phase1Transition, hmain, clockCounterStep, ht_phase] at hphase
  · have hsmall' : ¬ 3 < (clockCounterStep L K t).smallBias.val := by
      simpa [Phase1Transition, hmain] using hsmall
    simp [Phase1Transition, hmain] at hphase ⊢
    exact clockCounterStep_phase2_noPlus_of_not_pos
      (L := L) (K := K) t ht_phase hphase hsmall'

private theorem Phase1Transition_left_phase2_noMinus_of_not_neg
    (s t : AgentState L K) (hs_phase : s.phase.val = 1)
    (hphase : (Phase1Transition L K s t).1.phase.val = 2)
    (hsmall : ¬ (Phase1Transition L K s t).1.smallBias.val < 3) :
    hasMinusOne (Phase1Transition L K s t).1.opinions = false := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · simp [Phase1Transition, hmain, clockCounterStep, hs_phase] at hphase
  · have hsmall' : ¬ (clockCounterStep L K s).smallBias.val < 3 := by
      simpa [Phase1Transition, hmain] using hsmall
    simp [Phase1Transition, hmain] at hphase ⊢
    exact clockCounterStep_phase2_noMinus_of_not_neg
      (L := L) (K := K) s hs_phase hphase hsmall'

private theorem Phase1Transition_right_phase2_noMinus_of_not_neg
    (s t : AgentState L K) (ht_phase : t.phase.val = 1)
    (hphase : (Phase1Transition L K s t).2.phase.val = 2)
    (hsmall : ¬ (Phase1Transition L K s t).2.smallBias.val < 3) :
    hasMinusOne (Phase1Transition L K s t).2.opinions = false := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · simp [Phase1Transition, hmain, clockCounterStep, ht_phase] at hphase
  · have hsmall' : ¬ (clockCounterStep L K t).smallBias.val < 3 := by
      simpa [Phase1Transition, hmain] using hsmall
    simp [Phase1Transition, hmain] at hphase ⊢
    exact clockCounterStep_phase2_noMinus_of_not_neg
      (L := L) (K := K) t ht_phase hphase hsmall'

private theorem phaseInit_two_sign_support
    (a : AgentState L K)
    (hphase : (phaseInit L K ⟨2, by decide⟩ a).phase.val = 2) :
    (3 < (phaseInit L K ⟨2, by decide⟩ a).smallBias.val →
        hasPlusOne (phaseInit L K ⟨2, by decide⟩ a).opinions = true) ∧
      ((phaseInit L K ⟨2, by decide⟩ a).smallBias.val < 3 →
        hasMinusOne (phaseInit L K ⟨2, by decide⟩ a).opinions = true) := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  fin_cases smallBias <;>
    simp [phaseInit, enterPhase10, hasPlusOne, hasMinusOne] at hphase ⊢

set_option maxHeartbeats 1200000 in
private theorem advancePhaseWithInit_preserves_hasPlusOne_of_small_pos
    (a : AgentState L K) (h : hasPlusOne a.opinions = true)
    (hsmall : 3 < a.smallBias.val) :
    hasPlusOne (advancePhaseWithInit L K a).opinions = true := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  fin_cases phase <;> cases role <;> fin_cases smallBias <;>
    simp [advancePhaseWithInit, advancePhase, phaseInit, enterPhase10,
      hasPlusOne] at h hsmall ⊢ <;> try exact h

set_option maxHeartbeats 1200000 in
private theorem advancePhaseWithInit_preserves_hasMinusOne_of_small_neg
    (a : AgentState L K) (h : hasMinusOne a.opinions = true)
    (hsmall : a.smallBias.val < 3) :
    hasMinusOne (advancePhaseWithInit L K a).opinions = true := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  fin_cases phase <;> cases role <;> fin_cases smallBias <;>
    simp [advancePhaseWithInit, advancePhase, phaseInit, enterPhase10,
      hasMinusOne] at h hsmall ⊢ <;> try exact h

private theorem Phase2Transition_preserves_hasPlusOne_left
    (a b : AgentState L K) (h : hasPlusOne a.opinions = true)
    (hsmall : 3 < a.smallBias.val) :
    hasPlusOne (Phase2Transition L K a b).1.opinions = true := by
  have hunion : hasPlusOne (opinionsUnion a.opinions b.opinions) = true :=
    hasPlusOne_opinionsUnion_left a.opinions b.opinions h
  by_cases hminus : hasMinusOne (opinionsUnion a.opinions b.opinions) = true
  · simpa [Phase2Transition, hunion, hminus] using
      advancePhaseWithInit_preserves_hasPlusOne_of_small_pos
        (L := L) (K := K) ({ a with opinions := opinionsUnion a.opinions b.opinions })
        (by simpa [hunion]) (by simpa using hsmall)
  · have hminus_false : hasMinusOne (opinionsUnion a.opinions b.opinions) = false := by
      cases hm : hasMinusOne (opinionsUnion a.opinions b.opinions) <;> simp [hm] at hminus ⊢
    simp [Phase2Transition, hunion, hminus_false]

private theorem Phase2Transition_preserves_hasPlusOne_right
    (a b : AgentState L K) (h : hasPlusOne b.opinions = true)
    (hsmall : 3 < b.smallBias.val) :
    hasPlusOne (Phase2Transition L K a b).2.opinions = true := by
  have hunion : hasPlusOne (opinionsUnion a.opinions b.opinions) = true :=
    hasPlusOne_opinionsUnion_right a.opinions b.opinions h
  by_cases hminus : hasMinusOne (opinionsUnion a.opinions b.opinions) = true
  · simpa [Phase2Transition, hunion, hminus] using
      advancePhaseWithInit_preserves_hasPlusOne_of_small_pos
        (L := L) (K := K) ({ b with opinions := opinionsUnion a.opinions b.opinions })
        (by simpa [hunion]) (by simpa using hsmall)
  · have hminus_false : hasMinusOne (opinionsUnion a.opinions b.opinions) = false := by
      cases hm : hasMinusOne (opinionsUnion a.opinions b.opinions) <;> simp [hm] at hminus ⊢
    simp [Phase2Transition, hunion, hminus_false]

private theorem Phase2Transition_preserves_hasMinusOne_left
    (a b : AgentState L K) (h : hasMinusOne a.opinions = true)
    (hsmall : a.smallBias.val < 3) :
    hasMinusOne (Phase2Transition L K a b).1.opinions = true := by
  have hunion : hasMinusOne (opinionsUnion a.opinions b.opinions) = true :=
    hasMinusOne_opinionsUnion_left a.opinions b.opinions h
  by_cases hplus : hasPlusOne (opinionsUnion a.opinions b.opinions) = true
  · simpa [Phase2Transition, hunion, hplus] using
      advancePhaseWithInit_preserves_hasMinusOne_of_small_neg
        (L := L) (K := K) ({ a with opinions := opinionsUnion a.opinions b.opinions })
        (by simpa [hunion]) (by simpa using hsmall)
  · have hplus_false : hasPlusOne (opinionsUnion a.opinions b.opinions) = false := by
      cases hp : hasPlusOne (opinionsUnion a.opinions b.opinions) <;> simp [hp] at hplus ⊢
    simp [Phase2Transition, hunion, hplus_false]

private theorem Phase2Transition_preserves_hasMinusOne_right
    (a b : AgentState L K) (h : hasMinusOne b.opinions = true)
    (hsmall : b.smallBias.val < 3) :
    hasMinusOne (Phase2Transition L K a b).2.opinions = true := by
  have hunion : hasMinusOne (opinionsUnion a.opinions b.opinions) = true :=
    hasMinusOne_opinionsUnion_right a.opinions b.opinions h
  by_cases hplus : hasPlusOne (opinionsUnion a.opinions b.opinions) = true
  · simpa [Phase2Transition, hunion, hplus] using
      advancePhaseWithInit_preserves_hasMinusOne_of_small_neg
        (L := L) (K := K) ({ b with opinions := opinionsUnion a.opinions b.opinions })
        (by simpa [hunion]) (by simpa using hsmall)
  · have hplus_false : hasPlusOne (opinionsUnion a.opinions b.opinions) = false := by
      cases hp : hasPlusOne (opinionsUnion a.opinions b.opinions) <;> simp [hp] at hplus ⊢
    simp [Phase2Transition, hunion, hplus_false]

private theorem phase2SignSupport_phaseInit_two
    (a : AgentState L K)
    (hphase : (phaseInit L K ⟨2, by decide⟩ a).phase.val = 2) :
    phase2SignSupport (phaseInit L K ⟨2, by decide⟩ a) :=
  phaseInit_two_sign_support (L := L) (K := K) a hphase

private theorem phase2SignSupport_phaseInit_nine
    (a : AgentState L K)
    (hphase : (phaseInit L K ⟨9, by decide⟩ a).phase.val = 9) :
    phase2SignSupport (phaseInit L K ⟨9, by decide⟩ a) := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  fin_cases smallBias <;>
    simp [phase2SignSupport, phaseInit, enterPhase10, hasPlusOne, hasMinusOne] at hphase ⊢

private theorem phaseInit_two_phase_val_eq_two_or_ten
    (a : AgentState L K) (hphase : a.phase.val = 2) :
    (phaseInit L K ⟨2, by decide⟩ a).phase.val = 2 ∨
      (phaseInit L K ⟨2, by decide⟩ a).phase.val = 10 := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  simp only at hphase
  cases role <;> fin_cases smallBias <;>
    simp [phaseInit, enterPhase10, phase10, hphase]

private theorem phase2SignSupport_phase_update
    (a : AgentState L K) (p : Fin 11) (h : phase2SignSupport a) :
    phase2SignSupport ({ a with phase := p }) := by
  simpa [phase2SignSupport] using h

private theorem phase2SignSupport_runInitsBetween_to_two
    (oldP : ℕ) (a : AgentState L K) (hold : oldP ≤ 2)
    (hsupport : oldP = 2 → phase2SignSupport a)
    (hphase :
      (runInitsBetween L K oldP 2 ({ a with phase := ⟨2, by decide⟩ })).phase.val = 2) :
    phase2SignSupport
      (runInitsBetween L K oldP 2 ({ a with phase := ⟨2, by decide⟩ })) := by
  interval_cases oldP
  · unfold runInitsBetween
    have hlist :
        (List.range 11).filter (fun k => 0 < k ∧ k ≤ 2) = [1, 2] := by decide
    rw [hlist]
    simpa using
      phase2SignSupport_phaseInit_two (L := L) (K := K)
        (phaseInit L K ⟨1, by decide⟩ ({ a with phase := ⟨2, by decide⟩ }))
        hphase
  · unfold runInitsBetween
    have hlist :
        (List.range 11).filter (fun k => 1 < k ∧ k ≤ 2) = [2] := by decide
    rw [hlist]
    simpa using
      phase2SignSupport_phaseInit_two (L := L) (K := K)
        ({ a with phase := ⟨2, by decide⟩ }) hphase
  · unfold runInitsBetween
    have hlist :
        (List.range 11).filter (fun k => 2 < k ∧ k ≤ 2) = [] := by decide
    rw [hlist]
    simpa [phase2SignSupport] using hsupport rfl

private theorem phase2OpinionT_runInitsBetween_to_two_of_lt
    (oldP : ℕ) (a : AgentState L K) (hold : oldP < 2)
    (hphase :
      (runInitsBetween L K oldP 2 ({ a with phase := ⟨2, by decide⟩ })).phase.val = 2)
    (hsmall :
      (runInitsBetween L K oldP 2 ({ a with phase := ⟨2, by decide⟩ })).smallBias.val = 3) :
    (runInitsBetween L K oldP 2 ({ a with phase := ⟨2, by decide⟩ })).opinions =
      phase2OpinionT := by
  interval_cases oldP
  · unfold runInitsBetween at hphase hsmall ⊢
    have hlist :
        (List.range 11).filter (fun k => 0 < k ∧ k ≤ 2) = [1, 2] := by decide
    rw [hlist] at hphase hsmall ⊢
    have hpres := phaseInit_preserves_smallBias (L := L) (K := K)
      ⟨2, by decide⟩
      (phaseInit L K ⟨1, by decide⟩ ({ a with phase := ⟨2, by decide⟩ }))
    have hsmall_final :
        (phaseInit L K ⟨2, by decide⟩
          (phaseInit L K ⟨1, by decide⟩
            ({ a with phase := ⟨2, by decide⟩ }))).smallBias.val = 3 := by
      simpa using hsmall
    have hsmall_pre :
        (phaseInit L K ⟨1, by decide⟩
          ({ a with phase := ⟨2, by decide⟩ })).smallBias.val = 3 := by
      rw [hpres] at hsmall_final
      exact hsmall_final
    exact phaseInit_two_opinion_eq_zero_of_smallBias_zero (L := L) (K := K)
      (phaseInit L K ⟨1, by decide⟩ ({ a with phase := ⟨2, by decide⟩ }))
      hsmall_pre
  · unfold runInitsBetween at hphase hsmall ⊢
    have hlist :
        (List.range 11).filter (fun k => 1 < k ∧ k ≤ 2) = [2] := by decide
    rw [hlist] at hphase hsmall ⊢
    have hpres := phaseInit_preserves_smallBias (L := L) (K := K)
      ⟨2, by decide⟩ ({ a with phase := ⟨2, by decide⟩ })
    have hsmall_final :
        (phaseInit L K ⟨2, by decide⟩
          ({ a with phase := ⟨2, by decide⟩ })).smallBias.val = 3 := by
      simpa using hsmall
    have hsmall_pre :
        ({ a with phase := ⟨2, by decide⟩ } : AgentState L K).smallBias.val = 3 := by
      rw [hpres] at hsmall_final
      exact hsmall_final
    exact phaseInit_two_opinion_eq_zero_of_smallBias_zero (L := L) (K := K)
      ({ a with phase := ⟨2, by decide⟩ })
      hsmall_pre

private theorem runInitsBetween_to_nine_eq_phaseInit_nine
    (oldP : ℕ) (a : AgentState L K) (hold : oldP < 9) :
    runInitsBetween L K oldP 9 a =
      phaseInit L K ⟨9, by decide⟩ (runInitsBetween L K oldP 8 a) := by
  interval_cases oldP
  · unfold runInitsBetween
    have hlist :
        (List.range 11).filter (fun k => 0 < k ∧ k ≤ 9) =
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 8) ++ [9] := by decide
    rw [hlist, List.foldl_append]
    simp
  · unfold runInitsBetween
    have hlist :
        (List.range 11).filter (fun k => 1 < k ∧ k ≤ 9) =
          (List.range 11).filter (fun k => 1 < k ∧ k ≤ 8) ++ [9] := by decide
    rw [hlist, List.foldl_append]
    simp
  · unfold runInitsBetween
    have hlist :
        (List.range 11).filter (fun k => 2 < k ∧ k ≤ 9) =
          (List.range 11).filter (fun k => 2 < k ∧ k ≤ 8) ++ [9] := by decide
    rw [hlist, List.foldl_append]
    simp
  · unfold runInitsBetween
    have hlist :
        (List.range 11).filter (fun k => 3 < k ∧ k ≤ 9) =
          (List.range 11).filter (fun k => 3 < k ∧ k ≤ 8) ++ [9] := by decide
    rw [hlist, List.foldl_append]
    simp
  · unfold runInitsBetween
    have hlist :
        (List.range 11).filter (fun k => 4 < k ∧ k ≤ 9) =
          (List.range 11).filter (fun k => 4 < k ∧ k ≤ 8) ++ [9] := by decide
    rw [hlist, List.foldl_append]
    simp
  · unfold runInitsBetween
    have hlist :
        (List.range 11).filter (fun k => 5 < k ∧ k ≤ 9) =
          (List.range 11).filter (fun k => 5 < k ∧ k ≤ 8) ++ [9] := by decide
    rw [hlist, List.foldl_append]
    simp
  · unfold runInitsBetween
    have hlist :
        (List.range 11).filter (fun k => 6 < k ∧ k ≤ 9) =
          (List.range 11).filter (fun k => 6 < k ∧ k ≤ 8) ++ [9] := by decide
    rw [hlist, List.foldl_append]
    simp
  · unfold runInitsBetween
    have hlist :
        (List.range 11).filter (fun k => 7 < k ∧ k ≤ 9) =
          (List.range 11).filter (fun k => 7 < k ∧ k ≤ 8) ++ [9] := by decide
    rw [hlist, List.foldl_append]
    simp
  · unfold runInitsBetween
    have hlist :
        (List.range 11).filter (fun k => 8 < k ∧ k ≤ 9) =
          (List.range 11).filter (fun k => 8 < k ∧ k ≤ 8) ++ [9] := by decide
    rw [hlist, List.foldl_append]
    simp

private theorem phase2SignSupport_runInitsBetween_to_nine_of_lt
    (oldP : ℕ) (a : AgentState L K) (hold : oldP < 9)
    (hphase :
      (runInitsBetween L K oldP 9 ({ a with phase := ⟨9, by decide⟩ })).phase.val = 9) :
    phase2SignSupport
      (runInitsBetween L K oldP 9 ({ a with phase := ⟨9, by decide⟩ })) := by
  rw [runInitsBetween_to_nine_eq_phaseInit_nine (L := L) (K := K)
    oldP ({ a with phase := ⟨9, by decide⟩ }) hold] at hphase ⊢
  exact phase2SignSupport_phaseInit_nine (L := L) (K := K)
    (runInitsBetween L K oldP 8 ({ a with phase := ⟨9, by decide⟩ })) hphase

private theorem phaseInit_phase_eq_or_ten_of_eq_or_ten
    (p : Fin 11) (a : AgentState L K) (n : ℕ)
    (h : a.phase.val = n ∨ a.phase.val = 10) :
    (phaseInit L K p a).phase.val = n ∨
      (phaseInit L K p a).phase.val = 10 := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  fin_cases p <;> cases role <;> fin_cases smallBias <;>
    simp [phaseInit, enterPhase10, phase10] at h ⊢ <;> omega

private theorem runInitsBetween_phase_eq_start_or_ten
    (oldP newP n : ℕ) (a : AgentState L K)
    (h : a.phase.val = n ∨ a.phase.val = 10) :
    (runInitsBetween L K oldP newP a).phase.val = n ∨
      (runInitsBetween L K oldP newP a).phase.val = 10 := by
  unfold runInitsBetween
  set lst := (List.range 11).filter (fun k => oldP < k ∧ k ≤ newP)
  change
    (lst.foldl
      (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
      a).phase.val = n ∨
    (lst.foldl
      (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
      a).phase.val = 10
  induction lst generalizing a with
  | nil => simpa using h
  | cons k ks ih =>
      simp [List.foldl]
      by_cases hk : k < 11
      · simpa [hk] using ih (phaseInit L K ⟨k, hk⟩ a)
          (phaseInit_phase_eq_or_ten_of_eq_or_ten (L := L) (K := K)
            ⟨k, hk⟩ a n h)
      · simp [hk]
        exact ih a h

private theorem phaseEpidemicUpdate_left_phase2NeutralSupport_of_entered
    (s t : AgentState L K)
    (hs : s.phase.val < 2)
    (hout : (phaseEpidemicUpdate L K s t).1.phase.val = 2)
    (hneut : s.smallBias.val = 3) :
    (phaseEpidemicUpdate L K s t).1.opinions = phase2OpinionT := by
  unfold phaseEpidemicUpdate at hout ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hp_le : p.val ≤ 2 := by
    by_cases h10 :
        (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (s0.phase.val = 10 ∨ t0.phase.val = 10)
    · have hs_before : s.phase.val < 10 := by omega
      have hten : (phase10EpidemicEntry L K s s0).phase.val = 10 := by
        simp [phase10EpidemicEntry, hs_before]
      have htwo : (phase10EpidemicEntry L K s s0).phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      omega
    · have hs0_phase : s0.phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      have hs_ge : p.val ≤ s0.phase.val := by
        calc
          p.val = ({ s with phase := p } : AgentState L K).phase.val := by simp
          _ ≤ (runInitsBetween L K s.phase.val p.val ({ s with phase := p })).phase.val :=
            runInitsBetween_phase_nondec (L := L) (K := K)
              s.phase.val p.val ({ s with phase := p })
          _ = s0.phase.val := by rfl
      omega
  have hs0_small : s0.smallBias.val = 3 := by
    have hpres := runInitsBetween_preserves_smallBias
      (L := L) (K := K) s.phase.val p.val ({ s with phase := p })
    simpa [s0, hpres] using hneut
  have hs0_op : s0.opinions = phase2OpinionT := by
    by_cases h10 :
        (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (s0.phase.val = 10 ∨ t0.phase.val = 10)
    · have hs_before : s.phase.val < 10 := by omega
      have hten : (phase10EpidemicEntry L K s s0).phase.val = 10 := by
        simp [phase10EpidemicEntry, hs_before]
      have htwo : (phase10EpidemicEntry L K s s0).phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      omega
    · have hs0_phase : s0.phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      have hshape :
          s0.phase.val = p.val ∨ s0.phase.val = 10 := by
        simpa [s0] using
          runInitsBetween_phase_eq_start_or_ten (L := L) (K := K)
            s.phase.val p.val p.val ({ s with phase := p }) (Or.inl (by simp))
      have hp2 : p.val = 2 := by
        rcases hshape with hp | hten <;> omega
      have hp_eq : p = ⟨2, by decide⟩ := Fin.ext hp2
      have hs0_rw :
          s0 =
            runInitsBetween L K s.phase.val 2
              ({ s with phase := ⟨2, by decide⟩ }) := by
        simp [s0, hp_eq]
      rw [hs0_rw] at hs0_phase hs0_small ⊢
      exact phase2OpinionT_runInitsBetween_to_two_of_lt
        (L := L) (K := K) s.phase.val s hs hs0_phase hs0_small
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have hs_before : s.phase.val < 10 := by omega
    have hten : (phase10EpidemicEntry L K s s0).phase.val = 10 := by
      simp [phase10EpidemicEntry, hs_before]
    have htwo : (phase10EpidemicEntry L K s s0).phase.val = 2 := by
      simpa [h10, s0, t0] using hout
    omega
  · simpa [h10, s0, t0] using hs0_op

private theorem phaseEpidemicUpdate_right_phase2NeutralSupport_of_entered
    (s t : AgentState L K)
    (ht : t.phase.val < 2)
    (hout : (phaseEpidemicUpdate L K s t).2.phase.val = 2)
    (hneut : t.smallBias.val = 3) :
    (phaseEpidemicUpdate L K s t).2.opinions = phase2OpinionT := by
  unfold phaseEpidemicUpdate at hout ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hp_le : p.val ≤ 2 := by
    by_cases h10 :
        (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (s0.phase.val = 10 ∨ t0.phase.val = 10)
    · have ht_before : t.phase.val < 10 := by omega
      have hten : (phase10EpidemicEntry L K t t0).phase.val = 10 := by
        simp [phase10EpidemicEntry, ht_before]
      have htwo : (phase10EpidemicEntry L K t t0).phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      omega
    · have ht0_phase : t0.phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      have ht_ge : p.val ≤ t0.phase.val := by
        calc
          p.val = ({ t with phase := p } : AgentState L K).phase.val := by simp
          _ ≤ (runInitsBetween L K t.phase.val p.val ({ t with phase := p })).phase.val :=
            runInitsBetween_phase_nondec (L := L) (K := K)
              t.phase.val p.val ({ t with phase := p })
          _ = t0.phase.val := by rfl
      omega
  have ht0_small : t0.smallBias.val = 3 := by
    have hpres := runInitsBetween_preserves_smallBias
      (L := L) (K := K) t.phase.val p.val ({ t with phase := p })
    simpa [t0, hpres] using hneut
  have ht0_op : t0.opinions = phase2OpinionT := by
    by_cases h10 :
        (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (s0.phase.val = 10 ∨ t0.phase.val = 10)
    · have ht_before : t.phase.val < 10 := by omega
      have hten : (phase10EpidemicEntry L K t t0).phase.val = 10 := by
        simp [phase10EpidemicEntry, ht_before]
      have htwo : (phase10EpidemicEntry L K t t0).phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      omega
    · have ht0_phase : t0.phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      have hshape :
          t0.phase.val = p.val ∨ t0.phase.val = 10 := by
        simpa [t0] using
          runInitsBetween_phase_eq_start_or_ten (L := L) (K := K)
            t.phase.val p.val p.val ({ t with phase := p }) (Or.inl (by simp))
      have hp2 : p.val = 2 := by
        rcases hshape with hp | hten <;> omega
      have hp_eq : p = ⟨2, by decide⟩ := Fin.ext hp2
      have ht0_rw :
          t0 =
            runInitsBetween L K t.phase.val 2
              ({ t with phase := ⟨2, by decide⟩ }) := by
        simp [t0, hp_eq]
      rw [ht0_rw] at ht0_phase ht0_small ⊢
      exact phase2OpinionT_runInitsBetween_to_two_of_lt
        (L := L) (K := K) t.phase.val t ht ht0_phase ht0_small
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have ht_before : t.phase.val < 10 := by omega
    have hten : (phase10EpidemicEntry L K t t0).phase.val = 10 := by
      simp [phase10EpidemicEntry, ht_before]
    have htwo : (phase10EpidemicEntry L K t t0).phase.val = 2 := by
      simpa [h10, s0, t0] using hout
    omega
  · simpa [h10, s0, t0] using ht0_op

private theorem phaseEpidemicUpdate_left_phase_le_nine_or_ten_of_phases_le_nine
    (s t : AgentState L K) (hs : s.phase.val ≤ 9) (ht : t.phase.val ≤ 9) :
    (phaseEpidemicUpdate L K s t).1.phase.val ≤ 9 ∨
      (phaseEpidemicUpdate L K s t).1.phase.val = 10 := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hp_le : p.val ≤ 9 := by
    have hmax : max s.phase.val t.phase.val ≤ 9 := max_le hs ht
    simpa [p] using hmax
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · right
    have hs_before : s.phase.val < 10 := by omega
    rw [if_pos h10]
    simp [phase10EpidemicEntry, hs_before]
  · have hshape :
        s0.phase.val = p.val ∨ s0.phase.val = 10 := by
      simpa [s0] using
        runInitsBetween_phase_eq_start_or_ten (L := L) (K := K)
          s.phase.val p.val p.val ({ s with phase := p }) (Or.inl (by simp))
    rw [if_neg h10]
    rcases hshape with hphase | hphase
    · left
      rw [hphase]
      exact hp_le
    · right
      exact hphase

private theorem phaseEpidemicUpdate_right_phase_le_nine_or_ten_of_phases_le_nine
    (s t : AgentState L K) (hs : s.phase.val ≤ 9) (ht : t.phase.val ≤ 9) :
    (phaseEpidemicUpdate L K s t).2.phase.val ≤ 9 ∨
      (phaseEpidemicUpdate L K s t).2.phase.val = 10 := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hp_le : p.val ≤ 9 := by
    have hmax : max s.phase.val t.phase.val ≤ 9 := max_le hs ht
    simpa [p] using hmax
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · right
    have ht_before : t.phase.val < 10 := by omega
    rw [if_pos h10]
    simp [phase10EpidemicEntry, ht_before]
  · have hshape :
        t0.phase.val = p.val ∨ t0.phase.val = 10 := by
      simpa [t0] using
        runInitsBetween_phase_eq_start_or_ten (L := L) (K := K)
          t.phase.val p.val p.val ({ t with phase := p }) (Or.inl (by simp))
    rw [if_neg h10]
    rcases hshape with hphase | hphase
    · left
      rw [hphase]
      exact hp_le
    · right
      exact hphase

private theorem phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
    (s t : AgentState L K) (hs : s.phase.val ≤ 9) (ht : t.phase.val ≤ 9)
    (hs_not_ten : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10)
    (ht_not_ten : (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10) :
    (phaseEpidemicUpdate L K s t).1.phase.val =
      (phaseEpidemicUpdate L K s t).2.phase.val := by
  unfold phaseEpidemicUpdate at hs_not_ten ht_not_ten ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hshape_s :
      s0.phase.val = p.val ∨ s0.phase.val = 10 := by
    simpa [s0] using
      runInitsBetween_phase_eq_start_or_ten (L := L) (K := K)
        s.phase.val p.val p.val ({ s with phase := p }) (Or.inl (by simp))
  have hshape_t :
      t0.phase.val = p.val ∨ t0.phase.val = 10 := by
    simpa [t0] using
      runInitsBetween_phase_eq_start_or_ten (L := L) (K := K)
        t.phase.val p.val p.val ({ t with phase := p }) (Or.inl (by simp))
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have hs_before : s.phase.val < 10 := by omega
    rw [if_pos h10] at hs_not_ten ht_not_ten ⊢
    have hbad : (phase10EpidemicEntry L K s s0).phase.val = 10 := by
      simp [phase10EpidemicEntry, hs_before]
    exact False.elim (hs_not_ten hbad)
  · rw [if_neg h10] at hs_not_ten ht_not_ten ⊢
    rcases hshape_s with hs0 | hs0
    · rcases hshape_t with ht0 | ht0
      · rw [hs0, ht0]
      · exact False.elim (ht_not_ten ht0)
    · exact False.elim (hs_not_ten hs0)

private theorem phaseEpidemicUpdate_left_opinions_of_phase9_right_le_nine
    (s t : AgentState L K) (hs : s.phase.val = 9) (ht : t.phase.val ≤ 9) :
    (phaseEpidemicUpdate L K s t).1.opinions = s.opinions := by
  have hle : t.phase ≤ s.phase := by
    rw [Fin.le_iff_val_le_val]
    omega
  have hp : max s.phase t.phase = s.phase := max_eq_left hle
  simp [phaseEpidemicUpdate, hp, runInitsBetween_self_api, phase10EpidemicEntry, hs]
  split_ifs <;> simp

private theorem phaseEpidemicUpdate_right_opinions_of_phase9_left_le_nine
    (s t : AgentState L K) (ht : t.phase.val = 9) (hs : s.phase.val ≤ 9) :
    (phaseEpidemicUpdate L K s t).2.opinions = t.opinions := by
  have hle : s.phase ≤ t.phase := by
    rw [Fin.le_iff_val_le_val]
    omega
  have hp : max s.phase t.phase = t.phase := max_eq_right hle
  simp [phaseEpidemicUpdate, hp, runInitsBetween_self_api, phase10EpidemicEntry, ht]
  split_ifs <;> simp

private theorem phaseEpidemicUpdate_left_phase9_support_of_right_le_nine
    (s t : AgentState L K) (hs : s.phase.val = 9) (ht : t.phase.val ≤ 9)
    (hss : phase2SignSupport s) :
    phase2SignSupport (phaseEpidemicUpdate L K s t).1 ∧
      ((phaseEpidemicUpdate L K s t).1.phase.val = 9 ∨
        (phaseEpidemicUpdate L K s t).1.phase.val = 10) := by
  have hop := phaseEpidemicUpdate_left_opinions_of_phase9_right_le_nine
    (L := L) (K := K) s t hs ht
  have hsmall := (phaseEpidemicUpdate_preserves_smallBias L K s t).1
  constructor
  · constructor
    · intro hpos
      have hpos_s : 3 < s.smallBias.val := by simpa [hsmall] using hpos
      simpa [hop] using hss.1 hpos_s
    · intro hneg
      have hneg_s : s.smallBias.val < 3 := by simpa [hsmall] using hneg
      simpa [hop] using hss.2 hneg_s
  · have hle :=
      phaseEpidemicUpdate_left_phase_le_nine_or_ten_of_phases_le_nine
        (L := L) (K := K) s t (by omega) ht
    have hge := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
    rcases hle with hle | hten
    · left
      change max s.phase.val t.phase.val ≤
        (phaseEpidemicUpdate L K s t).1.phase.val at hge
      omega
    · right
      exact hten

private theorem phaseEpidemicUpdate_right_phase9_support_of_left_le_nine
    (s t : AgentState L K) (ht : t.phase.val = 9) (hs : s.phase.val ≤ 9)
    (htt : phase2SignSupport t) :
    phase2SignSupport (phaseEpidemicUpdate L K s t).2 ∧
      ((phaseEpidemicUpdate L K s t).2.phase.val = 9 ∨
        (phaseEpidemicUpdate L K s t).2.phase.val = 10) := by
  have hop := phaseEpidemicUpdate_right_opinions_of_phase9_left_le_nine
    (L := L) (K := K) s t ht hs
  have hsmall := (phaseEpidemicUpdate_preserves_smallBias L K s t).2
  constructor
  · constructor
    · intro hpos
      have hpos_t : 3 < t.smallBias.val := by simpa [hsmall] using hpos
      simpa [hop] using htt.1 hpos_t
    · intro hneg
      have hneg_t : t.smallBias.val < 3 := by simpa [hsmall] using hneg
      simpa [hop] using htt.2 hneg_t
  · have hle :=
      phaseEpidemicUpdate_right_phase_le_nine_or_ten_of_phases_le_nine
        (L := L) (K := K) s t hs (by omega)
    have hge := phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) s t
    rcases hle with hle | hten
    · left
      change max s.phase.val t.phase.val ≤
        (phaseEpidemicUpdate L K s t).2.phase.val at hge
      omega
    · right
      exact hten

private theorem phaseEpidemicUpdate_left_phase9SignSupport_of_entered
    (s t : AgentState L K)
    (hs : s.phase.val < 9)
    (hout : (phaseEpidemicUpdate L K s t).1.phase.val = 9) :
    phase2SignSupport (phaseEpidemicUpdate L K s t).1 := by
  unfold phaseEpidemicUpdate at hout ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hnot10 :
      ¬ ((s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)) := by
    intro h10
    have hs_before : s.phase.val < 10 := by omega
    have hten : (phase10EpidemicEntry L K s s0).phase.val = 10 := by
      simp [phase10EpidemicEntry, hs_before, enterPhase10_phase_val]
    have hphase10 :
        (phase10EpidemicEntry L K s s0).phase.val = 9 := by
      simpa [h10, s0, t0] using hout
    omega
  have hs0_phase : s0.phase.val = 9 := by
    simpa [hnot10, s0, t0] using hout
  have hshape :
      s0.phase.val = p.val ∨ s0.phase.val = 10 := by
    simpa [s0] using
      runInitsBetween_phase_eq_start_or_ten (L := L) (K := K)
        s.phase.val p.val p.val ({ s with phase := p }) (Or.inl (by simp))
  have hp9 : p.val = 9 := by
    rcases hshape with hp | hten
    · omega
    · omega
  have hp_eq : p = ⟨9, by decide⟩ := Fin.ext hp9
  have hs0_support : phase2SignSupport s0 := by
    have hs0_rw :
        s0 =
          runInitsBetween L K s.phase.val 9
            ({ s with phase := ⟨9, by decide⟩ }) := by
      simp [s0, hp_eq]
    have hphase_run := hs0_phase
    rw [hs0_rw] at hphase_run
    rw [hs0_rw]
    exact phase2SignSupport_runInitsBetween_to_nine_of_lt
      (L := L) (K := K) s.phase.val s hs
      hphase_run
  simpa [hnot10, s0, t0] using hs0_support

private theorem phaseEpidemicUpdate_right_phase9SignSupport_of_entered
    (s t : AgentState L K)
    (ht : t.phase.val < 9)
    (hout : (phaseEpidemicUpdate L K s t).2.phase.val = 9) :
    phase2SignSupport (phaseEpidemicUpdate L K s t).2 := by
  unfold phaseEpidemicUpdate at hout ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hnot10 :
      ¬ ((s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)) := by
    intro h10
    have ht_before : t.phase.val < 10 := by omega
    have hten : (phase10EpidemicEntry L K t t0).phase.val = 10 := by
      simp [phase10EpidemicEntry, ht_before, enterPhase10_phase_val]
    have hphase10 :
        (phase10EpidemicEntry L K t t0).phase.val = 9 := by
      simpa [h10, s0, t0] using hout
    omega
  have ht0_phase : t0.phase.val = 9 := by
    simpa [hnot10, s0, t0] using hout
  have hshape :
      t0.phase.val = p.val ∨ t0.phase.val = 10 := by
    simpa [t0] using
      runInitsBetween_phase_eq_start_or_ten (L := L) (K := K)
        t.phase.val p.val p.val ({ t with phase := p }) (Or.inl (by simp))
  have hp9 : p.val = 9 := by
    rcases hshape with hp | hten
    · omega
    · omega
  have hp_eq : p = ⟨9, by decide⟩ := Fin.ext hp9
  have ht0_support : phase2SignSupport t0 := by
    have ht0_rw :
        t0 =
          runInitsBetween L K t.phase.val 9
            ({ t with phase := ⟨9, by decide⟩ }) := by
      simp [t0, hp_eq]
    have hphase_run := ht0_phase
    rw [ht0_rw] at hphase_run
    rw [ht0_rw]
    exact phase2SignSupport_runInitsBetween_to_nine_of_lt
      (L := L) (K := K) t.phase.val t ht
      hphase_run
  simpa [hnot10, s0, t0] using ht0_support

private theorem Phase2Transition_preserves_phase2SignSupport_left
    (a b : AgentState L K) (h : phase2SignSupport a) :
    phase2SignSupport (Phase2Transition L K a b).1 := by
  constructor
  · intro hpos
    have hsmall := (Phase2Transition_preserves_smallBias L K a b).1
    have hpos_a : 3 < a.smallBias.val := by simpa [hsmall] using hpos
    exact Phase2Transition_preserves_hasPlusOne_left (L := L) (K := K) a b
      (h.1 hpos_a) hpos_a
  · intro hneg
    have hsmall := (Phase2Transition_preserves_smallBias L K a b).1
    have hneg_a : a.smallBias.val < 3 := by simpa [hsmall] using hneg
    exact Phase2Transition_preserves_hasMinusOne_left (L := L) (K := K) a b
      (h.2 hneg_a) hneg_a

private theorem Phase2Transition_preserves_phase2SignSupport_right
    (a b : AgentState L K) (h : phase2SignSupport b) :
    phase2SignSupport (Phase2Transition L K a b).2 := by
  constructor
  · intro hpos
    have hsmall := (Phase2Transition_preserves_smallBias L K a b).2
    have hpos_b : 3 < b.smallBias.val := by simpa [hsmall] using hpos
    exact Phase2Transition_preserves_hasPlusOne_right (L := L) (K := K) a b
      (h.1 hpos_b) hpos_b
  · intro hneg
    have hsmall := (Phase2Transition_preserves_smallBias L K a b).2
    have hneg_b : b.smallBias.val < 3 := by simpa [hsmall] using hneg
    exact Phase2Transition_preserves_hasMinusOne_right (L := L) (K := K) a b
      (h.2 hneg_b) hneg_b

private theorem Phase9Transition_preserves_phase2SignSupport_left
    (a b : AgentState L K) (h : phase2SignSupport a) :
    phase2SignSupport (Phase9Transition L K a b).1 := by
  simpa [Phase9Transition] using
    Phase2Transition_preserves_phase2SignSupport_left (L := L) (K := K) a b h

private theorem Phase9Transition_preserves_phase2SignSupport_right
    (a b : AgentState L K) (h : phase2SignSupport b) :
    phase2SignSupport (Phase9Transition L K a b).2 := by
  simpa [Phase9Transition] using
    Phase2Transition_preserves_phase2SignSupport_right (L := L) (K := K) a b h

private theorem phase10EpidemicEntry_preserves_phase2SignSupport
    (before after : AgentState L K) (h : phase2SignSupport after) :
    phase2SignSupport (phase10EpidemicEntry L K before after) := by
  simpa [phase2SignSupport] using h

private theorem finishPhase10Entry_preserves_phase2SignSupport
    (before after : AgentState L K) (h : phase2SignSupport after) :
    phase2SignSupport (finishPhase10Entry L K before after) := by
  simpa [phase2SignSupport] using h

private theorem Phase10Transition_preserves_phase2SignSupport_left
    (a b : AgentState L K) (h : phase2SignSupport a) :
    phase2SignSupport (Phase10Transition L K a b).1 := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  simp [phase2SignSupport, Phase10Transition] at h ⊢
  split_ifs <;> simp_all

private theorem Phase10Transition_preserves_phase2SignSupport_right
    (a b : AgentState L K) (h : phase2SignSupport b) :
    phase2SignSupport (Phase10Transition L K a b).2 := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  simp [phase2SignSupport, Phase10Transition] at h ⊢
  split_ifs <;> simp_all

private theorem stdCounterSubroutine_phase2SignSupport_of_phase_one
    (a : AgentState L K) (hphase_one : a.phase.val = 1)
    (hphase_two : (stdCounterSubroutine L K a).phase.val = 2) :
    phase2SignSupport (stdCounterSubroutine L K a) := by
  by_cases hcounter : a.counter.val = 0
  · simp [stdCounterSubroutine, hcounter, advancePhaseWithInit, advancePhase,
      hphase_one] at hphase_two ⊢
    exact phase2SignSupport_phaseInit_two (L := L) (K := K)
      ({ a with phase := ⟨2, by decide⟩ }) hphase_two
  · simp [stdCounterSubroutine, hcounter] at hphase_two ⊢
    omega

private theorem clockCounterStep_phase2SignSupport_of_phase_one
    (a : AgentState L K) (hphase_one : a.phase.val = 1)
    (hphase_two : (clockCounterStep L K a).phase.val = 2) :
    phase2SignSupport (clockCounterStep L K a) := by
  by_cases hclock : a.role = .clock
  · simp [clockCounterStep, hclock] at hphase_two ⊢
    exact stdCounterSubroutine_phase2SignSupport_of_phase_one
      (L := L) (K := K) a hphase_one hphase_two
  · simp [clockCounterStep, hclock] at hphase_two ⊢
    omega

private theorem Phase1Transition_left_phase2SignSupport
    (s t : AgentState L K) (hs_phase : s.phase.val = 1)
    (hphase : (Phase1Transition L K s t).1.phase.val = 2) :
    phase2SignSupport (Phase1Transition L K s t).1 := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · simp [Phase1Transition, hmain, clockCounterStep, hs_phase] at hphase
  · simp [Phase1Transition, hmain] at hphase ⊢
    exact clockCounterStep_phase2SignSupport_of_phase_one (L := L) (K := K)
      s hs_phase hphase

private theorem Phase1Transition_right_phase2SignSupport
    (s t : AgentState L K) (ht_phase : t.phase.val = 1)
    (hphase : (Phase1Transition L K s t).2.phase.val = 2) :
    phase2SignSupport (Phase1Transition L K s t).2 := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · simp [Phase1Transition, hmain, clockCounterStep, ht_phase] at hphase
  · simp [Phase1Transition, hmain] at hphase ⊢
    exact clockCounterStep_phase2SignSupport_of_phase_one (L := L) (K := K)
      t ht_phase hphase

private theorem stdCounterSubroutine_phase9SignSupport_of_phase_eight
    (a : AgentState L K) (hphase_eight : a.phase.val = 8)
    (hphase_nine : (stdCounterSubroutine L K a).phase.val = 9) :
    phase2SignSupport (stdCounterSubroutine L K a) := by
  by_cases hcounter : a.counter.val = 0
  · simp [stdCounterSubroutine, hcounter, advancePhaseWithInit, advancePhase,
      hphase_eight] at hphase_nine ⊢
    exact phase2SignSupport_phaseInit_nine (L := L) (K := K)
      ({ a with phase := ⟨9, by decide⟩ }) hphase_nine
  · simp [stdCounterSubroutine, hcounter] at hphase_nine
    omega

private theorem clockCounterStep_phase9SignSupport_of_phase_eight
    (a : AgentState L K) (hphase_eight : a.phase.val = 8)
    (hphase_nine : (clockCounterStep L K a).phase.val = 9) :
    phase2SignSupport (clockCounterStep L K a) := by
  by_cases hclock : a.role = .clock
  · simp [clockCounterStep, hclock] at hphase_nine ⊢
    exact stdCounterSubroutine_phase9SignSupport_of_phase_eight
      (L := L) (K := K) a hphase_eight hphase_nine
  · simp [clockCounterStep, hclock] at hphase_nine
    omega

private theorem absorbConsume_left_role_phase_of_main
    (s t : AgentState L K) (hs : s.role = .main) :
    (absorbConsume L K s t).1.role = .main ∧
      (absorbConsume L K s t).1.phase = s.phase := by
  rcases s with
    ⟨sinput, soutput, sphase, srole, sassigned, sbias, ssmallBias,
      shour, sminute, sfull, sopinions, scounter⟩
  rcases t with
    ⟨tinput, toutput, tphase, trole, tassigned, tbias, tsmallBias,
      thour, tminute, tfull, topinions, tcounter⟩
  simp at hs
  subst srole
  match sbias, tbias with
  | .zero, .zero => simp [absorbConsume]
  | .zero, .dyadic _ _ => simp [absorbConsume]
  | .dyadic _ _, .zero => simp [absorbConsume]
  | .dyadic .pos _, .dyadic .pos _ => simp [absorbConsume]
  | .dyadic .neg _, .dyadic .neg _ => simp [absorbConsume]
  | .dyadic .pos _, .dyadic .neg _ =>
      simp [absorbConsume]
      split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ =>
      simp [absorbConsume]
      split_ifs <;> simp

private theorem absorbConsume_right_role_phase_of_main
    (s t : AgentState L K) (ht : t.role = .main) :
    (absorbConsume L K s t).2.role = .main ∧
      (absorbConsume L K s t).2.phase = t.phase := by
  rcases s with
    ⟨sinput, soutput, sphase, srole, sassigned, sbias, ssmallBias,
      shour, sminute, sfull, sopinions, scounter⟩
  rcases t with
    ⟨tinput, toutput, tphase, trole, tassigned, tbias, tsmallBias,
      thour, tminute, tfull, topinions, tcounter⟩
  simp at ht
  subst trole
  match sbias, tbias with
  | .zero, .zero => simp [absorbConsume]
  | .zero, .dyadic _ _ => simp [absorbConsume]
  | .dyadic _ _, .zero => simp [absorbConsume]
  | .dyadic .pos _, .dyadic .pos _ => simp [absorbConsume]
  | .dyadic .neg _, .dyadic .neg _ => simp [absorbConsume]
  | .dyadic .pos _, .dyadic .neg _ =>
      simp [absorbConsume]
      split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ =>
      simp [absorbConsume]
      split_ifs <;> simp

private theorem Phase8Transition_left_phase9SignSupport
    (s t : AgentState L K) (hs_phase : s.phase.val = 8)
    (hphase : (Phase8Transition L K s t).1.phase.val = 9) :
    phase2SignSupport (Phase8Transition L K s t).1 := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · rcases hmain with ⟨hs_main, ht_main⟩
    have hrt := absorbConsume_left_role_phase_of_main (L := L) (K := K)
      s t hs_main
    have hnot_clock : (absorbConsume L K s t).1.role ≠ .clock := by
      simp [hs_main]
    have hphase_abs : (absorbConsume L K s t).1.phase.val = 9 := by
      simpa [Phase8Transition, hs_main, ht_main, hnot_clock] using hphase
    rw [hrt.2] at hphase_abs
    omega
  · simp [Phase8Transition, hmain] at hphase ⊢
    exact clockCounterStep_phase9SignSupport_of_phase_eight (L := L) (K := K)
      s hs_phase hphase

private theorem Phase8Transition_right_phase9SignSupport
    (s t : AgentState L K) (ht_phase : t.phase.val = 8)
    (hphase : (Phase8Transition L K s t).2.phase.val = 9) :
    phase2SignSupport (Phase8Transition L K s t).2 := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · rcases hmain with ⟨hs_main, ht_main⟩
    have hrt := absorbConsume_right_role_phase_of_main (L := L) (K := K)
      s t ht_main
    have hnot_clock : (absorbConsume L K s t).2.role ≠ .clock := by
      simp [ht_main]
    have hphase_abs : (absorbConsume L K s t).2.phase.val = 9 := by
      simpa [Phase8Transition, hs_main, ht_main, hnot_clock] using hphase
    rw [hrt.2] at hphase_abs
    omega
  · simp [Phase8Transition, hmain] at hphase ⊢
    exact clockCounterStep_phase9SignSupport_of_phase_eight (L := L) (K := K)
      t ht_phase hphase

private theorem stdCounterSubroutine_phase_ne_nine_of_phase_le_seven
    (a : AgentState L K) (ha : a.phase.val ≤ 7) :
    (stdCounterSubroutine L K a).phase.val ≠ 9 := by
  intro hphase
  by_cases hcounter : a.counter.val = 0
  · let b := advancePhase L K a
    have hb_phase : b.phase.val = a.phase.val + 1 := by
      dsimp [b]
      simp [advancePhase, show a.phase.val < 10 by omega]
    have hshape :
        (phaseInit L K b.phase b).phase.val = b.phase.val ∨
          (phaseInit L K b.phase b).phase.val = 10 :=
      phaseInit_phase_eq_or_ten_of_eq_or_ten (L := L) (K := K)
        b.phase b b.phase.val (Or.inl rfl)
    have hout :
        (stdCounterSubroutine L K a).phase.val =
          (phaseInit L K b.phase b).phase.val := by
      simp [stdCounterSubroutine, hcounter, advancePhaseWithInit, b]
    rcases hshape with hsame | hten
    · rw [hout, hsame, hb_phase] at hphase
      omega
    · rw [hout, hten] at hphase
      omega
  · have hout :
        (stdCounterSubroutine L K a).phase.val = a.phase.val := by
      simp [stdCounterSubroutine, hcounter]
    omega

private theorem advancePhase_phase_ne_nine_of_phase_le_seven
    (a : AgentState L K) (ha : a.phase.val ≤ 7) :
    (advancePhase L K a).phase.val ≠ 9 := by
  intro hphase
  by_cases h : a.phase.val < 10
  · simp [advancePhase, h] at hphase
    omega
  · simp [advancePhase, h] at hphase
    omega

private theorem advancePhaseWithInit_phase_ne_nine_of_phase_le_seven
    (a : AgentState L K) (ha : a.phase.val ≤ 7) :
    (advancePhaseWithInit L K a).phase.val ≠ 9 := by
  intro hphase
  let b := advancePhase L K a
  have hb_le : b.phase.val ≤ 8 := by
    dsimp [b]
    by_cases hlt : a.phase.val < 10
    · simp [advancePhase, hlt]
      omega
    · simp [advancePhase, hlt]
      omega
  have hshape :
      (phaseInit L K b.phase b).phase.val = b.phase.val ∨
        (phaseInit L K b.phase b).phase.val = 10 :=
    phaseInit_phase_eq_or_ten_of_eq_or_ten (L := L) (K := K)
      b.phase b b.phase.val (Or.inl rfl)
  have hout :
      (advancePhaseWithInit L K a).phase.val =
        (phaseInit L K b.phase b).phase.val := by
    simp [advancePhaseWithInit, b]
  rcases hshape with hsame | hten
  · rw [hout, hsame] at hphase
    omega
  · rw [hout, hten] at hphase
    omega

private theorem clockCounterStep_phase_ne_nine_of_phase_le_seven
    (a : AgentState L K) (ha : a.phase.val ≤ 7) :
    (clockCounterStep L K a).phase.val ≠ 9 := by
  intro hphase
  by_cases hclock : a.role = .clock
  · exact stdCounterSubroutine_phase_ne_nine_of_phase_le_seven
      (L := L) (K := K) a ha (by simpa [clockCounterStep, hclock] using hphase)
  · simp [clockCounterStep, hclock] at hphase
    omega

private theorem Phase1Transition_left_phase_ne_nine_of_phase_le_seven
    (s t : AgentState L K) (hs : s.phase.val ≤ 7) :
    (Phase1Transition L K s t).1.phase.val ≠ 9 := by
  intro hphase
  by_cases hmain : s.role = .main ∧ t.role = .main
  · exact clockCounterStep_phase_ne_nine_of_phase_le_seven
      (L := L) (K := K)
      ({ s with smallBias := (avgFin7 s.smallBias t.smallBias).1 })
      (by simpa using hs)
      (by simpa [Phase1Transition, hmain] using hphase)
  · exact clockCounterStep_phase_ne_nine_of_phase_le_seven
      (L := L) (K := K) s hs
      (by simpa [Phase1Transition, hmain] using hphase)

private theorem Phase1Transition_right_phase_ne_nine_of_phase_le_seven
    (s t : AgentState L K) (ht : t.phase.val ≤ 7) :
    (Phase1Transition L K s t).2.phase.val ≠ 9 := by
  intro hphase
  by_cases hmain : s.role = .main ∧ t.role = .main
  · exact clockCounterStep_phase_ne_nine_of_phase_le_seven
      (L := L) (K := K)
      ({ t with smallBias := (avgFin7 s.smallBias t.smallBias).2 })
      (by simpa using ht)
      (by simpa [Phase1Transition, hmain] using hphase)
  · exact clockCounterStep_phase_ne_nine_of_phase_le_seven
      (L := L) (K := K) t ht
      (by simpa [Phase1Transition, hmain] using hphase)

private theorem Phase2Transition_left_phase_ne_nine_of_phase_le_seven
    (s t : AgentState L K) (hs : s.phase.val ≤ 7) :
    (Phase2Transition L K s t).1.phase.val ≠ 9 := by
  intro hphase
  unfold Phase2Transition at hphase
  dsimp at hphase
  split at hphase
  · exact advancePhaseWithInit_phase_ne_nine_of_phase_le_seven
      (L := L) (K := K) ({ s with opinions := opinionsUnion s.opinions t.opinions })
      (by simpa using hs) hphase
  · split_ifs at hphase <;> simp at hphase <;> omega

private theorem Phase2Transition_right_phase_ne_nine_of_phase_le_seven
    (s t : AgentState L K) (ht : t.phase.val ≤ 7) :
    (Phase2Transition L K s t).2.phase.val ≠ 9 := by
  intro hphase
  unfold Phase2Transition at hphase
  dsimp at hphase
  split at hphase
  · exact advancePhaseWithInit_phase_ne_nine_of_phase_le_seven
      (L := L) (K := K) ({ t with opinions := opinionsUnion s.opinions t.opinions })
      (by simpa using ht) hphase
  · split_ifs at hphase <;> simp at hphase <;> omega

private theorem Phase4Transition_left_phase_ne_nine_of_phase_le_seven
    (s t : AgentState L K) (hs : s.phase.val ≤ 7) :
    (Phase4Transition L K s t).1.phase.val ≠ 9 := by
  intro hphase
  unfold Phase4Transition at hphase
  dsimp at hphase
  split_ifs at hphase
  · exact advancePhase_phase_ne_nine_of_phase_le_seven (L := L) (K := K) s hs hphase
  · simp at hphase
    omega

private theorem Phase4Transition_right_phase_ne_nine_of_phase_le_seven
    (s t : AgentState L K) (ht : t.phase.val ≤ 7) :
    (Phase4Transition L K s t).2.phase.val ≠ 9 := by
  intro hphase
  unfold Phase4Transition at hphase
  dsimp at hphase
  split_ifs at hphase
  · exact advancePhase_phase_ne_nine_of_phase_le_seven (L := L) (K := K) t ht hphase
  · simp at hphase
    omega

private theorem Phase5Transition_left_phase_ne_nine_of_phase_le_seven
    (s t : AgentState L K) (hs : s.phase.val ≤ 7) :
    (Phase5Transition L K s t).1.phase.val ≠ 9 := by
  intro hphase
  let doSample (r m : AgentState L K) : AgentState L K × AgentState L K :=
    if r.hour.val = L then ({ r with hour := exponentOf L m.bias }, m) else (r, m)
  let s1 := if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero) then
    (doSample s t).1
    else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero) then
    (doSample t s).2
    else s
  have hs1 : s1.phase.val = s.phase.val := by
    dsimp [s1, doSample]
    split_ifs <;> rfl
  change (if s1.role = .clock then stdCounterSubroutine L K s1 else s1).phase.val = 9 at hphase
  by_cases hclock : s1.role = .clock
  · exact stdCounterSubroutine_phase_ne_nine_of_phase_le_seven
      (L := L) (K := K) s1 (by omega) (by simpa [hclock] using hphase)
  · simp [hclock] at hphase
    omega

private theorem Phase5Transition_right_phase_ne_nine_of_phase_le_seven
    (s t : AgentState L K) (ht : t.phase.val ≤ 7) :
    (Phase5Transition L K s t).2.phase.val ≠ 9 := by
  intro hphase
  let doSample (r m : AgentState L K) : AgentState L K × AgentState L K :=
    if r.hour.val = L then ({ r with hour := exponentOf L m.bias }, m) else (r, m)
  let t1 := if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero) then
    (doSample s t).2
    else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero) then
    (doSample t s).1
    else t
  have ht1 : t1.phase.val = t.phase.val := by
    dsimp [t1, doSample]
    split_ifs <;> rfl
  change (if t1.role = .clock then stdCounterSubroutine L K t1 else t1).phase.val = 9 at hphase
  by_cases hclock : t1.role = .clock
  · exact stdCounterSubroutine_phase_ne_nine_of_phase_le_seven
      (L := L) (K := K) t1 (by omega) (by simpa [hclock] using hphase)
  · simp [hclock] at hphase
    omega

private theorem doSplit_phase_eq_chain
    (r m : AgentState L K) :
    (doSplit L K r m).1.phase = r.phase ∧
      (doSplit L K r m).2.phase = m.phase := by
  unfold doSplit
  match m.bias with
  | Bias.zero => simp
  | Bias.dyadic _ _ => simp; split_ifs <;> simp

private theorem cancelSplit_phase_eq_chain
    (s t : AgentState L K) :
    (cancelSplit L K s t).1.phase = s.phase ∧
      (cancelSplit L K s t).2.phase = t.phase := by
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic sgn_s i, .dyadic sgn_t j => simp; split_ifs <;> simp

private theorem phase3CancelSplit_phase_eq_chain
    (s t : AgentState L K) :
    (phase3CancelSplit L K s t).1.phase = s.phase ∧
      (phase3CancelSplit L K s t).2.phase = t.phase := by
  unfold phase3CancelSplit
  match s.bias, t.bias with
  | .zero, .zero => simp
  | .zero, .dyadic _ _ => simp; split_ifs <;> simp
  | .dyadic _ _, .zero => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .neg _ => simp

private theorem Phase6Transition_left_phase_ne_nine_of_phase_le_seven
    (s t : AgentState L K) (hs : s.phase.val ≤ 7) :
    (Phase6Transition L K s t).1.phase.val ≠ 9 := by
  intro hphase
  let s1 := if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero) then
    (doSplit L K s t).1
    else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero) then
    (doSplit L K t s).2
    else s
  have hs1 : s1.phase.val = s.phase.val := by
    dsimp [s1]
    rcases doSplit_phase_eq_chain (L := L) (K := K) s t with ⟨hst, htt⟩
    rcases doSplit_phase_eq_chain (L := L) (K := K) t s with ⟨hts, hss⟩
    split_ifs <;> simp [hst, hss]
  change (if s1.role = .clock then stdCounterSubroutine L K s1 else s1).phase.val = 9 at hphase
  by_cases hclock : s1.role = .clock
  · exact stdCounterSubroutine_phase_ne_nine_of_phase_le_seven
      (L := L) (K := K) s1 (by omega) (by simpa [hclock] using hphase)
  · simp [hclock] at hphase
    omega

private theorem Phase6Transition_right_phase_ne_nine_of_phase_le_seven
    (s t : AgentState L K) (ht : t.phase.val ≤ 7) :
    (Phase6Transition L K s t).2.phase.val ≠ 9 := by
  intro hphase
  let t1 := if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero) then
    (doSplit L K s t).2
    else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero) then
    (doSplit L K t s).1
    else t
  have ht1 : t1.phase.val = t.phase.val := by
    dsimp [t1]
    rcases doSplit_phase_eq_chain (L := L) (K := K) s t with ⟨hst, htt⟩
    rcases doSplit_phase_eq_chain (L := L) (K := K) t s with ⟨hts, hss⟩
    split_ifs <;> simp [htt, hts]
  change (if t1.role = .clock then stdCounterSubroutine L K t1 else t1).phase.val = 9 at hphase
  by_cases hclock : t1.role = .clock
  · exact stdCounterSubroutine_phase_ne_nine_of_phase_le_seven
      (L := L) (K := K) t1 (by omega) (by simpa [hclock] using hphase)
  · simp [hclock] at hphase
    omega

private theorem Phase7Transition_left_phase_ne_nine_of_phase_le_seven
    (s t : AgentState L K) (hs : s.phase.val ≤ 7) :
    (Phase7Transition L K s t).1.phase.val ≠ 9 := by
  intro hphase
  let s1 := if s.role = .main ∧ t.role = .main then (cancelSplit L K s t).1 else s
  have hs1 : s1.phase.val = s.phase.val := by
    dsimp [s1]
    rcases cancelSplit_phase_eq_chain (L := L) (K := K) s t with ⟨hst, htt⟩
    split_ifs <;> simp [hst]
  change (if s1.role = .clock then stdCounterSubroutine L K s1 else s1).phase.val = 9 at hphase
  by_cases hclock : s1.role = .clock
  · exact stdCounterSubroutine_phase_ne_nine_of_phase_le_seven
      (L := L) (K := K) s1 (by omega) (by simpa [hclock] using hphase)
  · simp [hclock] at hphase
    omega

private theorem Phase7Transition_right_phase_ne_nine_of_phase_le_seven
    (s t : AgentState L K) (ht : t.phase.val ≤ 7) :
    (Phase7Transition L K s t).2.phase.val ≠ 9 := by
  intro hphase
  let t1 := if s.role = .main ∧ t.role = .main then (cancelSplit L K s t).2 else t
  have ht1 : t1.phase.val = t.phase.val := by
    dsimp [t1]
    rcases cancelSplit_phase_eq_chain (L := L) (K := K) s t with ⟨hst, htt⟩
    split_ifs <;> simp [htt]
  change (if t1.role = .clock then stdCounterSubroutine L K t1 else t1).phase.val = 9 at hphase
  by_cases hclock : t1.role = .clock
  · exact stdCounterSubroutine_phase_ne_nine_of_phase_le_seven
      (L := L) (K := K) t1 (by omega) (by simpa [hclock] using hphase)
  · simp [hclock] at hphase
    omega

private theorem Phase3Transition_left_phase_ne_nine_of_phase_le_seven
    (s t : AgentState L K) (hs : s.phase.val ≤ 7) :
    (Phase3Transition L K s t).1.phase.val ≠ 9 := by
  intro hphase
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
    have h_hour_lt : hVal < L + 1 :=
      (Nat.max_lt).mpr ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 :=
      (Nat.max_lt).mpr ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1_ne : s1.phase.val ≠ 9 := by
    dsimp [s1]
    split_ifs <;>
      first
      | exact stdCounterSubroutine_phase_ne_nine_of_phase_le_seven (L := L) (K := K) s hs
      | intro h
        have : s.phase.val = 9 := by simpa using h
        omega
  have hs2_ne : s2.phase.val ≠ 9 := by
    dsimp [s2]
    split_ifs <;> exact hs1_ne
  change
    (if s2.role = .main ∧ t2.role = .main then
      phase3CancelSplit L K s2 t2 else (s2, t2)).1.phase.val = 9 at hphase
  by_cases hmain : s2.role = .main ∧ t2.role = .main
  · have hcs := (phase3CancelSplit_phase_eq_chain (L := L) (K := K) s2 t2).1
    rw [if_pos hmain] at hphase
    simp [hcs] at hphase
    exact hs2_ne hphase
  · rw [if_neg hmain] at hphase
    exact hs2_ne hphase

private theorem Phase3Transition_right_phase_ne_nine_of_phase_le_seven
    (s t : AgentState L K) (ht : t.phase.val ≤ 7) :
    (Phase3Transition L K s t).2.phase.val ≠ 9 := by
  intro hphase
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
    have h_hour_lt : hVal < L + 1 :=
      (Nat.max_lt).mpr ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 :=
      (Nat.max_lt).mpr ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have ht1_ne : t1.phase.val ≠ 9 := by
    dsimp [t1]
    split_ifs <;>
      first
      | exact stdCounterSubroutine_phase_ne_nine_of_phase_le_seven (L := L) (K := K) t ht
      | intro h
        have : t.phase.val = 9 := by simpa using h
        omega
  have ht2_ne : t2.phase.val ≠ 9 := by
    dsimp [t2]
    split_ifs <;> exact ht1_ne
  change
    (if s2.role = .main ∧ t2.role = .main then
      phase3CancelSplit L K s2 t2 else (s2, t2)).2.phase.val = 9 at hphase
  by_cases hmain : s2.role = .main ∧ t2.role = .main
  · have hcs := (phase3CancelSplit_phase_eq_chain (L := L) (K := K) s2 t2).2
    rw [if_pos hmain] at hphase
    simp [hcs] at hphase
    exact ht2_ne hphase
  · rw [if_neg hmain] at hphase
    exact ht2_ne hphase

set_option maxHeartbeats 4000000 in
private lemma Phase0Transition_both_clock_fst_phase
    (s t : AgentState L K) (hs : s.role = .clock) (ht : t.role = .clock) :
    (Phase0Transition L K s t).1.phase = (stdCounterSubroutine L K s).phase := by
  unfold Phase0Transition
  simp only [hs, ht, show ¬(Role.clock = Role.mcr) from by decide,
    show ¬(Role.clock = Role.cr) from by decide,
    show ¬(Role.clock = Role.main) from by decide,
    false_and, and_false, true_and, ↓reduceIte, ite_self]

set_option maxHeartbeats 4000000 in
private lemma Phase0Transition_both_clock_snd_phase
    (s t : AgentState L K) (hs : s.role = .clock) (ht : t.role = .clock) :
    (Phase0Transition L K s t).2.phase = (stdCounterSubroutine L K t).phase := by
  unfold Phase0Transition
  simp only [hs, ht, show ¬(Role.clock = Role.mcr) from by decide,
    show ¬(Role.clock = Role.cr) from by decide,
    show ¬(Role.clock = Role.main) from by decide,
    false_and, and_false, true_and, ↓reduceIte, ite_self]

set_option maxHeartbeats 8000000 in
private lemma Phase0Transition_phase_eq_of_not_both_clock
    (s t : AgentState L K) (h : ¬(s.role = .clock ∧ t.role = .clock)) :
    (Phase0Transition L K s t).1.phase = s.phase ∧
    (Phase0Transition L K s t).2.phase = t.phase := by
  rcases s with
    ⟨sinput, soutput, sphase, srole, sassigned, sbias, ssmallBias,
      shour, sminute, sfull, sopinions, scounter⟩
  rcases t with
    ⟨tinput, toutput, tphase, trole, tassigned, tbias, tsmallBias,
      thour, tminute, tfull, topinions, tcounter⟩
  simp only [not_and] at h
  cases srole <;> cases trole <;> cases sassigned <;> cases tassigned <;>
    simp_all [Phase0Transition, stdCounterSubroutine]
set_option maxHeartbeats 4000000 in
private theorem Phase0Transition_left_phase_ne_nine_of_phase_le_seven
    (s t : AgentState L K) (hs : s.phase.val ≤ 7) :
    (Phase0Transition L K s t).1.phase.val ≠ 9 := by
  by_cases h : s.role = .clock ∧ t.role = .clock
  · -- Both clocks: Phase0Transition output = stdCounterSubroutine(s)
    rw [congrArg Fin.val (Phase0Transition_both_clock_fst_phase (L := L) (K := K) s t h.1 h.2)]
    exact stdCounterSubroutine_phase_ne_nine_of_phase_le_seven (L := L) (K := K) s hs
  · have heq := (Phase0Transition_phase_eq_of_not_both_clock (L := L) (K := K) s t h).1
    rw [congrArg Fin.val heq]; omega

set_option maxHeartbeats 4000000 in
private theorem Phase0Transition_right_phase_ne_nine_of_phase_le_seven
    (s t : AgentState L K) (ht : t.phase.val ≤ 7) :
    (Phase0Transition L K s t).2.phase.val ≠ 9 := by
  by_cases h : s.role = .clock ∧ t.role = .clock
  · rw [congrArg Fin.val (Phase0Transition_both_clock_snd_phase (L := L) (K := K) s t h.1 h.2)]
    exact stdCounterSubroutine_phase_ne_nine_of_phase_le_seven (L := L) (K := K) t ht
  · have heq := (Phase0Transition_phase_eq_of_not_both_clock (L := L) (K := K) s t h).2
    rw [congrArg Fin.val heq]; omega

private theorem advancePhaseWithInit_phase_ne_two_of_phase_zero
    (a : AgentState L K) (ha : a.phase.val = 0) :
    (advancePhaseWithInit L K a).phase.val ≠ 2 := by
  intro hphase
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  rcases phase with ⟨p, hp⟩
  simp only at ha
  subst p
  cases role <;>
    simp [advancePhaseWithInit, advancePhase, phaseInit, enterPhase10, phase10] at hphase

private theorem stdCounterSubroutine_phase_ne_two_of_phase_zero
    (a : AgentState L K) (ha : a.phase.val = 0) :
    (stdCounterSubroutine L K a).phase.val ≠ 2 := by
  intro hphase
  unfold stdCounterSubroutine at hphase
  split_ifs at hphase
  · exact advancePhaseWithInit_phase_ne_two_of_phase_zero (L := L) (K := K) a ha hphase
  · simp [ha] at hphase

private lemma no_phase_init_between_same (p : ℕ) :
    (List.range 11).filter (fun k => p < k ∧ k ≤ p) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro k _ hk
  simp only [decide_eq_true_eq] at hk
  exact Nat.not_lt_of_ge hk.2 hk.1

private lemma runInitsBetween_self_chain (p : ℕ) (a : AgentState L K) :
    runInitsBetween L K p p a = a := by
  unfold runInitsBetween
  rw [no_phase_init_between_same p]
  simp

private theorem phaseEpidemicUpdate_left_opinions_of_phase2_right_le_two
    (s t : AgentState L K) (hs : s.phase.val = 2) (ht : t.phase.val ≤ 2) :
    (phaseEpidemicUpdate L K s t).1.opinions = s.opinions := by
  rcases ht_cases : t.phase with ⟨n, hn⟩
  have hnle : n ≤ 2 := by simpa [ht_cases] using ht
  have hs_phase : s.phase = ⟨2, by decide⟩ := Fin.ext hs
  interval_cases n
  · have h02 :
        (List.range 11).filter (fun k => decide (0 < k) && decide (k ≤ 2)) = [1, 2] := by
      decide
    have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, hs_phase, ht_cases, runInitsBetween, h02, h22]
    split_ifs <;> simp [phase10EpidemicEntry, hs]
  · have h12 :
        (List.range 11).filter (fun k => decide (1 < k) && decide (k ≤ 2)) = [2] := by
      decide
    have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, hs_phase, ht_cases, runInitsBetween, h12, h22]
    split_ifs <;> simp [phase10EpidemicEntry, hs]
  · have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, hs_phase, ht_cases, runInitsBetween, h22]

private theorem phaseEpidemicUpdate_left_phase_two_or_ten_of_phase2_right_le_two
    (s t : AgentState L K) (hs : s.phase.val = 2) (ht : t.phase.val ≤ 2) :
    (phaseEpidemicUpdate L K s t).1.phase.val = 2 ∨
      (phaseEpidemicUpdate L K s t).1.phase.val = 10 := by
  rcases ht_cases : t.phase with ⟨n, hn⟩
  have hnle : n ≤ 2 := by simpa [ht_cases] using ht
  have hs_phase : s.phase = ⟨2, by decide⟩ := Fin.ext hs
  interval_cases n
  · have h02 :
        (List.range 11).filter (fun k => decide (0 < k) && decide (k ≤ 2)) = [1, 2] := by
      decide
    have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, hs_phase, ht_cases, runInitsBetween, h02, h22]
    split_ifs
    · right
      simp [phase10EpidemicEntry, hs]
    · left
      simp
  · have h12 :
        (List.range 11).filter (fun k => decide (1 < k) && decide (k ≤ 2)) = [2] := by
      decide
    have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, hs_phase, ht_cases, runInitsBetween, h12, h22]
    split_ifs
    · right
      simp [phase10EpidemicEntry, hs]
    · left
      simp
  · have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, hs_phase, ht_cases, runInitsBetween, h22]

private theorem phaseEpidemicUpdate_left_phase2_support_of_right_le_two
    (s t : AgentState L K) (hs : s.phase.val = 2) (ht : t.phase.val ≤ 2)
    (hss : phase2SignSupport s) :
    phase2SignSupport (phaseEpidemicUpdate L K s t).1 ∧
      ((phaseEpidemicUpdate L K s t).1.phase.val = 2 ∨
        (phaseEpidemicUpdate L K s t).1.phase.val = 10) := by
  have hop := phaseEpidemicUpdate_left_opinions_of_phase2_right_le_two
    (L := L) (K := K) s t hs ht
  have hsmall := (phaseEpidemicUpdate_preserves_smallBias L K s t).1
  constructor
  · constructor
    · intro hpos
      have hpos_s : 3 < s.smallBias.val := by simpa [hsmall] using hpos
      simpa [hop] using hss.1 hpos_s
    · intro hneg
      have hneg_s : s.smallBias.val < 3 := by simpa [hsmall] using hneg
      simpa [hop] using hss.2 hneg_s
  · exact phaseEpidemicUpdate_left_phase_two_or_ten_of_phase2_right_le_two
      (L := L) (K := K) s t hs ht

private theorem Transition_phase2_to_phase2_preserves_signSupport
    (s t : AgentState L K) (hs : s.phase.val = 2)
    (hss : phase2SignSupport s)
    (hphase : (Transition L K s t).1.phase.val = 2) :
    phase2SignSupport (Transition L K s t).1 := by
  have ht_le : t.phase.val ≤ 2 := by
    have hmax := Transition_left_phase_ge_pair_max (L := L) (K := K) s t
    rw [hphase] at hmax
    omega
  have hs_epi :=
    phaseEpidemicUpdate_left_phase2_support_of_right_le_two (L := L) (K := K)
      s t hs ht_le hss
  unfold Transition
  generalize he : phaseEpidemicUpdate L K s t = e
  rcases e with ⟨s', t'⟩
  have hs'_support : phase2SignSupport s' := by
    simpa [he] using hs_epi.1
  have hs'_phase : s'.phase.val = 2 ∨ s'.phase.val = 10 := by
    simpa [he] using hs_epi.2
  change phase2SignSupport
    (finishPhase10Entry L K s'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).1)
  generalize hp : s'.phase = p
  fin_cases p
  · have : s'.phase.val = 0 := by simpa [hp]
    omega
  · have : s'.phase.val = 1 := by simpa [hp]
    omega
  · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
      s' (Phase2Transition L K s' t').1
      (Phase2Transition_preserves_phase2SignSupport_left (L := L) (K := K)
        s' t' hs'_support)
  · have : s'.phase.val = 3 := by simpa [hp]
    omega
  · have : s'.phase.val = 4 := by simpa [hp]
    omega
  · have : s'.phase.val = 5 := by simpa [hp]
    omega
  · have : s'.phase.val = 6 := by simpa [hp]
    omega
  · have : s'.phase.val = 7 := by simpa [hp]
    omega
  · have : s'.phase.val = 8 := by simpa [hp]
    omega
  · have : s'.phase.val = 9 := by simpa [hp]
    omega
  · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
      s' (Phase10Transition L K s' t').1
      (Phase10Transition_preserves_phase2SignSupport_left (L := L) (K := K)
        s' t' hs'_support)

private theorem phaseEpidemicUpdate_right_opinions_of_phase2_left_le_two
    (s t : AgentState L K) (ht : t.phase.val = 2) (hs : s.phase.val ≤ 2) :
    (phaseEpidemicUpdate L K s t).2.opinions = t.opinions := by
  rcases hs_cases : s.phase with ⟨n, hn⟩
  have hnle : n ≤ 2 := by simpa [hs_cases] using hs
  have ht_phase : t.phase = ⟨2, by decide⟩ := Fin.ext ht
  interval_cases n
  · have h02 :
        (List.range 11).filter (fun k => decide (0 < k) && decide (k ≤ 2)) = [1, 2] := by
      decide
    have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, ht_phase, hs_cases, runInitsBetween, h02, h22]
    split_ifs <;> simp [phase10EpidemicEntry, ht]
  · have h12 :
        (List.range 11).filter (fun k => decide (1 < k) && decide (k ≤ 2)) = [2] := by
      decide
    have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, ht_phase, hs_cases, runInitsBetween, h12, h22]
    split_ifs <;> simp [phase10EpidemicEntry, ht]
  · have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, ht_phase, hs_cases, runInitsBetween, h22]

private theorem phaseEpidemicUpdate_right_phase_two_or_ten_of_phase2_left_le_two
    (s t : AgentState L K) (ht : t.phase.val = 2) (hs : s.phase.val ≤ 2) :
    (phaseEpidemicUpdate L K s t).2.phase.val = 2 ∨
      (phaseEpidemicUpdate L K s t).2.phase.val = 10 := by
  rcases hs_cases : s.phase with ⟨n, hn⟩
  have hnle : n ≤ 2 := by simpa [hs_cases] using hs
  have ht_phase : t.phase = ⟨2, by decide⟩ := Fin.ext ht
  interval_cases n
  · have h02 :
        (List.range 11).filter (fun k => decide (0 < k) && decide (k ≤ 2)) = [1, 2] := by
      decide
    have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, ht_phase, hs_cases, runInitsBetween, h02, h22]
    split_ifs
    · right
      simp [phase10EpidemicEntry, ht]
    · left
      simp
  · have h12 :
        (List.range 11).filter (fun k => decide (1 < k) && decide (k ≤ 2)) = [2] := by
      decide
    have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, ht_phase, hs_cases, runInitsBetween, h12, h22]
    split_ifs
    · right
      simp [phase10EpidemicEntry, ht]
    · left
      simp
  · have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, ht_phase, hs_cases, runInitsBetween, h22]

private theorem phaseEpidemicUpdate_left_phase_two_or_ten_of_right_phase2_left_le_two
    (s t : AgentState L K) (ht : t.phase.val = 2) (hs : s.phase.val ≤ 2) :
    (phaseEpidemicUpdate L K s t).1.phase.val = 2 ∨
      (phaseEpidemicUpdate L K s t).1.phase.val = 10 := by
  rcases hs_cases : s.phase with ⟨n, hn⟩
  have hnle : n ≤ 2 := by simpa [hs_cases] using hs
  have ht_phase : t.phase = ⟨2, by decide⟩ := Fin.ext ht
  interval_cases n
  · have h02 :
        (List.range 11).filter (fun k => decide (0 < k) && decide (k ≤ 2)) = [1, 2] := by
      decide
    have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, ht_phase, hs_cases, runInitsBetween, h02, h22]
    split_ifs with hten
    · right
      simp [phase10EpidemicEntry, hs_cases]
    · left
      rcases s with
        ⟨sinput, soutput, sphase, srole, sassigned, sbias, ssmallBias,
          shour, sminute, sfull, sopinions, scounter⟩
      cases srole <;> fin_cases ssmallBias <;>
        simp [phaseInit, enterPhase10, phase10] at hten ⊢
  · have h12 :
        (List.range 11).filter (fun k => decide (1 < k) && decide (k ≤ 2)) = [2] := by
      decide
    have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, ht_phase, hs_cases, runInitsBetween, h12, h22]
    split_ifs with hten
    · right
      simp [phase10EpidemicEntry, hs_cases]
    · left
      have hphase_or :=
        phaseInit_two_phase_val_eq_two_or_ten (L := L) (K := K)
          ({ s with phase := ⟨2, by decide⟩ }) (by simp)
      rcases hphase_or with hphase_two | hphase_ten
      · simpa using hphase_two
      · exact False.elim (hten hphase_ten)
  · have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, ht_phase, hs_cases, runInitsBetween, h22]

private theorem phaseEpidemicUpdate_right_phase2_support_of_left_le_two
    (s t : AgentState L K) (ht : t.phase.val = 2) (hs : s.phase.val ≤ 2)
    (hss : phase2SignSupport t) :
    phase2SignSupport (phaseEpidemicUpdate L K s t).2 ∧
      ((phaseEpidemicUpdate L K s t).2.phase.val = 2 ∨
        (phaseEpidemicUpdate L K s t).2.phase.val = 10) := by
  have hop := phaseEpidemicUpdate_right_opinions_of_phase2_left_le_two
    (L := L) (K := K) s t ht hs
  have hsmall := (phaseEpidemicUpdate_preserves_smallBias L K s t).2
  constructor
  · constructor
    · intro hpos
      have hpos_t : 3 < t.smallBias.val := by simpa [hsmall] using hpos
      simpa [hop] using hss.1 hpos_t
    · intro hneg
      have hneg_t : t.smallBias.val < 3 := by simpa [hsmall] using hneg
      simpa [hop] using hss.2 hneg_t
  · exact phaseEpidemicUpdate_right_phase_two_or_ten_of_phase2_left_le_two
      (L := L) (K := K) s t ht hs

private theorem phaseEpidemicUpdate_left_phase2_opinion_T_of_right_le_two
    (s t : AgentState L K) (hs_le : s.phase.val ≤ 2) (ht_le : t.phase.val ≤ 2)
    (hprev : s.phase.val = 2 → s.smallBias.val = 3 → s.opinions = phase2OpinionT)
    (hphase : (phaseEpidemicUpdate L K s t).1.phase.val = 2)
    (hsmall : (phaseEpidemicUpdate L K s t).1.smallBias.val = 3) :
    (phaseEpidemicUpdate L K s t).1.opinions = phase2OpinionT := by
  by_cases hs : s.phase.val = 2
  · have hop := phaseEpidemicUpdate_left_opinions_of_phase2_right_le_two
      (L := L) (K := K) s t hs ht_le
    have hsmall_pres := (phaseEpidemicUpdate_preserves_smallBias L K s t).1
    have hs_small : s.smallBias.val = 3 := by
      simpa [hsmall_pres] using hsmall
    simpa [hop] using hprev hs hs_small
  · have hs_lt : s.phase.val < 2 := by omega
    have hsmall_pres := (phaseEpidemicUpdate_preserves_smallBias L K s t).1
    have hs_small : s.smallBias.val = 3 := by
      simpa [hsmall_pres] using hsmall
    exact phaseEpidemicUpdate_left_phase2NeutralSupport_of_entered
      (L := L) (K := K) s t hs_lt hphase hs_small

private theorem phaseEpidemicUpdate_right_phase2_opinion_T_of_left_le_two
    (s t : AgentState L K) (hs_le : s.phase.val ≤ 2) (ht_le : t.phase.val ≤ 2)
    (hprev : t.phase.val = 2 → t.smallBias.val = 3 → t.opinions = phase2OpinionT)
    (hphase : (phaseEpidemicUpdate L K s t).2.phase.val = 2)
    (hsmall : (phaseEpidemicUpdate L K s t).2.smallBias.val = 3) :
    (phaseEpidemicUpdate L K s t).2.opinions = phase2OpinionT := by
  by_cases ht : t.phase.val = 2
  · have hop := phaseEpidemicUpdate_right_opinions_of_phase2_left_le_two
      (L := L) (K := K) s t ht hs_le
    have hsmall_pres := (phaseEpidemicUpdate_preserves_smallBias L K s t).2
    have ht_small : t.smallBias.val = 3 := by
      simpa [hsmall_pres] using hsmall
    simpa [hop] using hprev ht ht_small
  · have ht_lt : t.phase.val < 2 := by omega
    have hsmall_pres := (phaseEpidemicUpdate_preserves_smallBias L K s t).2
    have ht_small : t.smallBias.val = 3 := by
      simpa [hsmall_pres] using hsmall
    exact phaseEpidemicUpdate_right_phase2NeutralSupport_of_entered
      (L := L) (K := K) s t ht_lt hphase ht_small

/-- One protocol step preserves the "Phase-4 agents output `.T`" property for the
left output.  If the left output of `Transition` lands in Phase 4, then either
the epidemic update already had it in Phase 4 (output `.T` carried over from the
source by `hs_prev`/`ht_prev` through the epidemic), or it just entered Phase 4
via `phaseInit ⟨4⟩` (which sets output `.T`).  Earlier phases cannot reach
Phase 4 in one step; later phases contradict the Phase-4 hypothesis. -/
private theorem Transition_left_phase4_output_T_of_phase_four
    (s t : AgentState L K)
    (hs_prev : s.phase.val = 4 → s.output = .T)
    (ht_prev : t.phase.val = 4 → t.output = .T)
    (hphase : (Transition L K s t).1.phase.val = 4) :
    (Transition L K s t).1.output = .T := by
  have hphase0 : (Transition L K s t).1.phase.val = 4 := hphase
  have hout_le : (Transition L K s t).1.phase.val ≤ 4 := by omega
  -- Epidemic phase ≤ output phase = 4.
  have hep_le : (phaseEpidemicUpdate L K s t).1.phase.val ≤ 4 :=
    le_trans (phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s t).1
      hout_le
  -- The epidemic output has output `.T` if it is in Phase 4.
  have hep_out_T : (phaseEpidemicUpdate L K s t).1.phase.val = 4 →
      (phaseEpidemicUpdate L K s t).1.output = .T := fun h =>
    phaseEpidemicUpdate_left_output_T_of_phase_four (L := L) (K := K) s t hs_prev h
  -- Now decompose `Transition`.
  unfold Transition at hphase ⊢
  generalize he : phaseEpidemicUpdate L K s t = e at hep_le hep_out_T hphase ⊢
  rcases e with ⟨s', t'⟩
  have hs'_le : s'.phase.val ≤ 4 := by simpa [he] using hep_le
  have hs'_out_T : s'.phase.val = 4 → s'.output = .T := by
    simpa [he] using hep_out_T
  -- Reduce the `finishPhase10Entry` wrapper: output phase = 4 ≠ 10.
  set out :=
    (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')) with hout_def
  have hne_ten : out.1.phase.val = 4 := by
    simpa [finishPhase10Entry_phase_val] using hphase
  show (finishPhase10Entry L K s' out.1).output = .T
  rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s' out.1 (by omega)]
  rw [hout_def]
  -- Case on the epidemic-output phase.
  rw [hout_def] at hne_ten
  rcases hsp : s'.phase with ⟨n, hn⟩
  simp only [hsp] at hne_ten hs'_le hs'_out_T ⊢
  interval_cases n
  · -- Phase 0: local output cannot reach Phase 4.
    exfalso
    have hbound :=
      Transition_left_phase_le_two_of_epidemic_phase_lt_two
        (L := L) (K := K) s t (by rw [he]; simp [hsp]) hout_le
    omega
  · -- Phase 1: local output cannot reach Phase 4.
    exfalso
    have hbound :=
      Transition_left_phase_le_two_of_epidemic_phase_lt_two
        (L := L) (K := K) s t (by rw [he]; simp [hsp]) hout_le
    omega
  · -- Phase 2: `Phase2Transition` cannot reach Phase 4.
    exact absurd hne_ten
      (Phase2Transition_left_phase_ne_four_of_phase_two (L := L) (K := K) s' t'
        (by simp [hsp]))
  · -- Phase 3: entered Phase 4 via `phaseInit ⟨4⟩`, output `.T`.
    exact Phase3Transition_left_output_T_of_phase_four (L := L) (K := K) s' t'
      (by simp [hsp]) hne_ten
  · -- Phase 4: `Phase4Transition` is the identity here, output `.T` carried over.
    rw [Phase4Transition_left_output_eq_of_phase_four (L := L) (K := K) s' t'
      (by simp [hsp]) hne_ten]
    exact hs'_out_T (by simp [hsp])
  all_goals (exfalso; omega)

/-- Right-agent version of `Transition_left_phase4_output_T_of_phase_four`. -/
private theorem Transition_right_phase4_output_T_of_phase_four
    (s t : AgentState L K)
    (hs_prev : s.phase.val = 4 → s.output = .T)
    (ht_prev : t.phase.val = 4 → t.output = .T)
    (hphase : (Transition L K s t).2.phase.val = 4) :
    (Transition L K s t).2.output = .T := by
  have hphase0 : (Transition L K s t).2.phase.val = 4 := hphase
  have hout_le : (Transition L K s t).2.phase.val ≤ 4 := by omega
  have hep_le : (phaseEpidemicUpdate L K s t).2.phase.val ≤ 4 :=
    le_trans (phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s t).2
      hout_le
  have hep_out_T : (phaseEpidemicUpdate L K s t).2.phase.val = 4 →
      (phaseEpidemicUpdate L K s t).2.output = .T := fun h =>
    phaseEpidemicUpdate_right_output_T_of_phase_four (L := L) (K := K) s t ht_prev h
  -- Both epidemic outputs share the same phase (each ≤ 4); fix it before
  -- generalizing the epidemic update away.
  have hleft_le : (phaseEpidemicUpdate L K s t).1.phase.val ≤ 4 :=
    phaseEpidemicUpdate_left_phase_le_four_of_right_le_four (L := L) (K := K) s t hep_le
  have hphase_eq :
      (phaseEpidemicUpdate L K s t).1.phase = (phaseEpidemicUpdate L K s t).2.phase :=
    phaseEpidemicUpdate_phases_eq_of_outputs_le_four (L := L) (K := K) s t
      hleft_le hep_le
  unfold Transition at hphase ⊢
  generalize he : phaseEpidemicUpdate L K s t = e at hep_le hep_out_T hphase hphase_eq ⊢
  rcases e with ⟨s', t'⟩
  have ht'_le : t'.phase.val ≤ 4 := by simpa [he] using hep_le
  have ht'_out_T : t'.phase.val = 4 → t'.output = .T := by
    simpa [he] using hep_out_T
  set out :=
    (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')) with hout_def
  have hne_ten : out.2.phase.val = 4 := by
    simpa [finishPhase10Entry_phase_val] using hphase
  show (finishPhase10Entry L K t' out.2).output = .T
  rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t' out.2 (by omega)]
  rw [hout_def]
  rw [hout_def] at hne_ten
  -- The local transition is dispatched on `s'.phase`; both outputs share phase.
  have hs't' : s'.phase = t'.phase := hphase_eq
  rcases hsp : s'.phase with ⟨n, hn⟩
  have htp : t'.phase = ⟨n, hn⟩ := by rw [← hs't', hsp]
  simp only [hsp] at hne_ten ⊢
  have ht'_phase_val : t'.phase.val = n := by rw [htp]
  interval_cases n
  · exfalso
    have hepi : (phaseEpidemicUpdate L K s t).1.phase.val < 2 := by
      rw [he]; show s'.phase.val < 2; simp [hsp]
    have hbound :=
      Transition_right_phase_le_two_of_epidemic_phase_lt_two
        (L := L) (K := K) s t hepi hout_le
    omega
  · exfalso
    have hepi : (phaseEpidemicUpdate L K s t).1.phase.val < 2 := by
      rw [he]; show s'.phase.val < 2; simp [hsp]
    have hbound :=
      Transition_right_phase_le_two_of_epidemic_phase_lt_two
        (L := L) (K := K) s t hepi hout_le
    omega
  · exact absurd hne_ten
      (Phase2Transition_right_phase_ne_four_of_phase_two (L := L) (K := K) s' t'
        (by simp [htp]))
  · exact Phase3Transition_right_output_T_of_phase_four (L := L) (K := K) s' t'
      (by simp [htp]) hne_ten
  · rw [Phase4Transition_right_output_eq_of_phase_four (L := L) (K := K) s' t'
      (by simp [htp]) hne_ten]
    exact ht'_out_T (by simp [htp])
  all_goals (exfalso; omega)

private theorem Transition_left_phase2_opinion_T_of_neutral_outputs
    (s t : AgentState L K)
    (hs_prev : s.phase.val = 2 → s.smallBias.val = 3 → s.opinions = phase2OpinionT)
    (ht_prev : t.phase.val = 2 → t.smallBias.val = 3 → t.opinions = phase2OpinionT)
    (hout_left_le : (Transition L K s t).1.phase.val ≤ 2)
    (hout_right_le : (Transition L K s t).2.phase.val ≤ 2)
    (hneut_left :
      (Transition L K s t).1.phase.val = 2 →
        (Transition L K s t).1.smallBias.val = 3)
    (hneut_right :
      (Transition L K s t).2.phase.val = 2 →
        (Transition L K s t).2.smallBias.val = 3)
    (hphase : (Transition L K s t).1.phase.val = 2) :
    (Transition L K s t).1.opinions = phase2OpinionT := by
  have hsmall_final : (Transition L K s t).1.smallBias.val = 3 :=
    hneut_left hphase
  have hs_le : s.phase.val ≤ 2 := by
    have hmax := Transition_left_phase_ge_pair_max (L := L) (K := K) s t
    rw [hphase] at hmax
    omega
  have ht_le : t.phase.val ≤ 2 := by
    have hmax := Transition_left_phase_ge_pair_max (L := L) (K := K) s t
    rw [hphase] at hmax
    omega
  unfold Transition at hout_left_le hout_right_le hneut_left hneut_right hphase hsmall_final ⊢
  generalize he : phaseEpidemicUpdate L K s t = e
  rcases e with ⟨s', t'⟩
  rw [he] at hout_left_le hout_right_le hneut_left hneut_right hphase hsmall_final
  have hs'_le_or_ten : s'.phase.val ≤ 2 ∨ s'.phase.val = 10 := by
    simpa [he] using
      phaseEpidemicUpdate_left_phase_le_two_or_ten_of_phases_le_two
        (L := L) (K := K) s t hs_le ht_le
  have ht'_le_or_ten : t'.phase.val ≤ 2 ∨ t'.phase.val = 10 := by
    simpa [he] using
      phaseEpidemicUpdate_right_phase_le_two_or_ten_of_phases_le_two
        (L := L) (K := K) s t hs_le ht_le
  change
    (finishPhase10Entry L K s'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).1).opinions = phase2OpinionT
  generalize hp : s'.phase = p
  fin_cases p
  · have hpval : s'.phase.val = 0 := by simpa [hp]
    have hlocal : (Phase0Transition L K s' t').1.phase.val = 2 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    exact False.elim
      (Phase0Transition_left_phase_ne_two_of_phase_zero
        (L := L) (K := K) s' t' hpval hlocal)
  · have hpval : s'.phase.val = 1 := by simpa [hp]
    have hlocal_phase : (Phase1Transition L K s' t').1.phase.val = 2 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have hlocal_small : (Phase1Transition L K s' t').1.smallBias.val = 3 := by
      have hne : (Phase1Transition L K s' t').1.phase.val ≠ 10 := by omega
      simpa [hp, finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) s' (Phase1Transition L K s' t').1 hne] using hsmall_final
    have hop := Phase1Transition_left_phase2_opinion_T_of_smallBias_three
      (L := L) (K := K) s' t' hpval hlocal_phase hlocal_small
    simpa [hp, finishPhase10Entry_eq_self_of_after_ne_10
      (L := L) (K := K) s' (Phase1Transition L K s' t').1 (by omega)] using hop
  · have hpval : s'.phase.val = 2 := by simpa [hp]
    have hlocal_left_phase : (Phase2Transition L K s' t').1.phase.val = 2 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have hlocal_left_small : (Phase2Transition L K s' t').1.smallBias.val = 3 := by
      have hne : (Phase2Transition L K s' t').1.phase.val ≠ 10 := by omega
      simpa [hp, finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) s' (Phase2Transition L K s' t').1 hne] using hsmall_final
    have hright_phase_le : (Phase2Transition L K s' t').2.phase.val ≤ 2 := by
      simpa [hp, finishPhase10Entry_phase_val] using hout_right_le
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase2Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase2Transition L K s' t').2.phase.val at hmono
      omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
        (L := L) (K := K) s t hs_le ht_le
        (by simpa [he, hp] using (by omega : s'.phase.val ≠ 10))
        (by simpa [he] using ht'_not_ten)
    have ht'_phase : t'.phase.val = 2 := by
      have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
      omega
    have hlocal_right_phase : (Phase2Transition L K s' t').2.phase.val = 2 := by
      have hmono := (Phase2Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase2Transition L K s' t').2.phase.val at hmono
      omega
    have hright_final_phase :
        (finishPhase10Entry L K t' (Phase2Transition L K s' t').2).phase.val = 2 := by
      simpa [finishPhase10Entry_phase_val] using hlocal_right_phase
    have hright_final_small :
        (finishPhase10Entry L K t' (Phase2Transition L K s' t').2).smallBias.val = 3 := by
      have hsmall0 := hneut_right (by simpa [hp] using hright_final_phase)
      simpa [hp] using hsmall0
    have hlocal_right_small : (Phase2Transition L K s' t').2.smallBias.val = 3 := by
      have hne : (Phase2Transition L K s' t').2.phase.val ≠ 10 := by omega
      simpa [finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) t' (Phase2Transition L K s' t').2 hne] using
        hright_final_small
    have hs'_small : s'.smallBias.val = 3 := by
      have hpres := (Phase2Transition_preserves_smallBias L K s' t').1
      simpa [hpres] using hlocal_left_small
    have ht'_small : t'.smallBias.val = 3 := by
      have hpres := (Phase2Transition_preserves_smallBias L K s' t').2
      simpa [hpres] using hlocal_right_small
    have hs'_op0 := phaseEpidemicUpdate_left_phase2_opinion_T_of_right_le_two
      (L := L) (K := K) s t hs_le ht_le hs_prev
      (by simpa [he] using hpval) (by simpa [he] using hs'_small)
    have ht'_op0 := phaseEpidemicUpdate_right_phase2_opinion_T_of_left_le_two
      (L := L) (K := K) s t hs_le ht_le ht_prev
      (by simpa [he] using ht'_phase) (by simpa [he] using ht'_small)
    have hs'_op : s'.opinions = phase2OpinionT := by
      simpa [he] using hs'_op0
    have ht'_op : t'.opinions = phase2OpinionT := by
      simpa [he] using ht'_op0
    have hop := Phase2Transition_neutral_left (L := L) (K := K) s' t'
      (by intro _; exact hs'_op) (by intro _; exact ht'_op)
      hlocal_left_small hlocal_right_small
    simpa [hp, finishPhase10Entry_eq_self_of_after_ne_10
      (L := L) (K := K) s' (Phase2Transition L K s' t').1 (by omega)] using hop
  · have hpval : s'.phase.val = 3 := by simpa [hp]
    rcases hs'_le_or_ten with hle | hten <;> omega
  · have hpval : s'.phase.val = 4 := by simpa [hp]
    rcases hs'_le_or_ten with hle | hten <;> omega
  · have hpval : s'.phase.val = 5 := by simpa [hp]
    rcases hs'_le_or_ten with hle | hten <;> omega
  · have hpval : s'.phase.val = 6 := by simpa [hp]
    rcases hs'_le_or_ten with hle | hten <;> omega
  · have hpval : s'.phase.val = 7 := by simpa [hp]
    rcases hs'_le_or_ten with hle | hten <;> omega
  · have hpval : s'.phase.val = 8 := by simpa [hp]
    rcases hs'_le_or_ten with hle | hten <;> omega
  · have hpval : s'.phase.val = 9 := by simpa [hp]
    rcases hs'_le_or_ten with hle | hten <;> omega
  · have hpval : s'.phase.val = 10 := by simpa [hp]
    have hmono := (Phase10Transition_phase_nondec (L := L) (K := K) s' t').1
    have hlocal : (Phase10Transition L K s' t').1.phase.val = 2 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    omega

private theorem Transition_right_phase2_opinion_T_of_neutral_outputs
    (s t : AgentState L K)
    (hs_prev : s.phase.val = 2 → s.smallBias.val = 3 → s.opinions = phase2OpinionT)
    (ht_prev : t.phase.val = 2 → t.smallBias.val = 3 → t.opinions = phase2OpinionT)
    (hout_left_le : (Transition L K s t).1.phase.val ≤ 2)
    (hout_right_le : (Transition L K s t).2.phase.val ≤ 2)
    (hneut_left :
      (Transition L K s t).1.phase.val = 2 →
        (Transition L K s t).1.smallBias.val = 3)
    (hneut_right :
      (Transition L K s t).2.phase.val = 2 →
        (Transition L K s t).2.smallBias.val = 3)
    (hphase : (Transition L K s t).2.phase.val = 2) :
    (Transition L K s t).2.opinions = phase2OpinionT := by
  have hsmall_final : (Transition L K s t).2.smallBias.val = 3 :=
    hneut_right hphase
  have hs_le : s.phase.val ≤ 2 := by
    have hmax := Transition_right_phase_ge_pair_max (L := L) (K := K) s t
    rw [hphase] at hmax
    omega
  have ht_le : t.phase.val ≤ 2 := by
    have hmax := Transition_right_phase_ge_pair_max (L := L) (K := K) s t
    rw [hphase] at hmax
    omega
  unfold Transition at hout_left_le hout_right_le hneut_left hneut_right hphase hsmall_final ⊢
  generalize he : phaseEpidemicUpdate L K s t = e
  rcases e with ⟨s', t'⟩
  rw [he] at hout_left_le hout_right_le hneut_left hneut_right hphase hsmall_final
  have hs'_le_or_ten : s'.phase.val ≤ 2 ∨ s'.phase.val = 10 := by
    simpa [he] using
      phaseEpidemicUpdate_left_phase_le_two_or_ten_of_phases_le_two
        (L := L) (K := K) s t hs_le ht_le
  have ht'_le_or_ten : t'.phase.val ≤ 2 ∨ t'.phase.val = 10 := by
    simpa [he] using
      phaseEpidemicUpdate_right_phase_le_two_or_ten_of_phases_le_two
        (L := L) (K := K) s t hs_le ht_le
  change
    (finishPhase10Entry L K t'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).2).opinions = phase2OpinionT
  generalize hp : s'.phase = p
  fin_cases p
  · have hpval : s'.phase.val = 0 := by simpa [hp]
    have hlocal : (Phase0Transition L K s' t').2.phase.val = 2 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase0Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase0Transition L K s' t').2.phase.val at hmono
      omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
        (L := L) (K := K) s t hs_le ht_le
        (by simpa [he, hp] using (by omega : s'.phase.val ≠ 10))
        (by simpa [he] using ht'_not_ten)
    have ht0 : t'.phase.val = 0 := by
      have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
      omega
    exact False.elim
      (Phase0Transition_right_phase_ne_two_of_phase_zero
        (L := L) (K := K) s' t' ht0 hlocal)
  · have hpval : s'.phase.val = 1 := by simpa [hp]
    have hlocal_phase : (Phase1Transition L K s' t').2.phase.val = 2 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have hlocal_small : (Phase1Transition L K s' t').2.smallBias.val = 3 := by
      have hne : (Phase1Transition L K s' t').2.phase.val ≠ 10 := by omega
      simpa [hp, finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) t' (Phase1Transition L K s' t').2 hne] using hsmall_final
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase1Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase1Transition L K s' t').2.phase.val at hmono
      omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
        (L := L) (K := K) s t hs_le ht_le
        (by simpa [he, hp] using (by omega : s'.phase.val ≠ 10))
        (by simpa [he] using ht'_not_ten)
    have ht'_phase : t'.phase.val = 1 := by
      have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
      omega
    have hop := Phase1Transition_right_phase2_opinion_T_of_smallBias_three
      (L := L) (K := K) s' t' ht'_phase hlocal_phase hlocal_small
    simpa [hp, finishPhase10Entry_eq_self_of_after_ne_10
      (L := L) (K := K) t' (Phase1Transition L K s' t').2 (by omega)] using hop
  · have hpval : s'.phase.val = 2 := by simpa [hp]
    have hlocal_right_phase : (Phase2Transition L K s' t').2.phase.val = 2 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have hlocal_right_small : (Phase2Transition L K s' t').2.smallBias.val = 3 := by
      have hne : (Phase2Transition L K s' t').2.phase.val ≠ 10 := by omega
      simpa [hp, finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) t' (Phase2Transition L K s' t').2 hne] using hsmall_final
    have hleft_phase_le : (Phase2Transition L K s' t').1.phase.val ≤ 2 := by
      simpa [hp, finishPhase10Entry_phase_val] using hout_left_le
    have hlocal_left_phase : (Phase2Transition L K s' t').1.phase.val = 2 := by
      have hmono := (Phase2Transition_phase_nondec (L := L) (K := K) s' t').1
      change s'.phase.val ≤ (Phase2Transition L K s' t').1.phase.val at hmono
      omega
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase2Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase2Transition L K s' t').2.phase.val at hmono
      omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
        (L := L) (K := K) s t hs_le ht_le
        (by simpa [he, hp] using (by omega : s'.phase.val ≠ 10))
        (by simpa [he] using ht'_not_ten)
    have ht'_phase : t'.phase.val = 2 := by
      have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
      omega
    have hleft_final_phase :
        (finishPhase10Entry L K s' (Phase2Transition L K s' t').1).phase.val = 2 := by
      simpa [finishPhase10Entry_phase_val] using hlocal_left_phase
    have hleft_final_small :
        (finishPhase10Entry L K s' (Phase2Transition L K s' t').1).smallBias.val = 3 := by
      have hsmall0 := hneut_left (by simpa [hp] using hleft_final_phase)
      simpa [hp] using hsmall0
    have hlocal_left_small : (Phase2Transition L K s' t').1.smallBias.val = 3 := by
      have hne : (Phase2Transition L K s' t').1.phase.val ≠ 10 := by omega
      simpa [finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) s' (Phase2Transition L K s' t').1 hne] using
        hleft_final_small
    have hs'_small : s'.smallBias.val = 3 := by
      have hpres := (Phase2Transition_preserves_smallBias L K s' t').1
      simpa [hpres] using hlocal_left_small
    have ht'_small : t'.smallBias.val = 3 := by
      have hpres := (Phase2Transition_preserves_smallBias L K s' t').2
      simpa [hpres] using hlocal_right_small
    have hs'_op0 := phaseEpidemicUpdate_left_phase2_opinion_T_of_right_le_two
      (L := L) (K := K) s t hs_le ht_le hs_prev
      (by simpa [he] using hpval) (by simpa [he] using hs'_small)
    have ht'_op0 := phaseEpidemicUpdate_right_phase2_opinion_T_of_left_le_two
      (L := L) (K := K) s t hs_le ht_le ht_prev
      (by simpa [he] using ht'_phase) (by simpa [he] using ht'_small)
    have hs'_op : s'.opinions = phase2OpinionT := by
      simpa [he] using hs'_op0
    have ht'_op : t'.opinions = phase2OpinionT := by
      simpa [he] using ht'_op0
    have hop := Phase2Transition_neutral_right (L := L) (K := K) s' t'
      (by intro _; exact hs'_op) (by intro _; exact ht'_op)
      hlocal_left_small hlocal_right_small
    simpa [hp, finishPhase10Entry_eq_self_of_after_ne_10
      (L := L) (K := K) t' (Phase2Transition L K s' t').2 (by omega)] using hop
  · have hpval : s'.phase.val = 3 := by simpa [hp]
    rcases hs'_le_or_ten with hle | hten <;> omega
  · have hpval : s'.phase.val = 4 := by simpa [hp]
    rcases hs'_le_or_ten with hle | hten <;> omega
  · have hpval : s'.phase.val = 5 := by simpa [hp]
    rcases hs'_le_or_ten with hle | hten <;> omega
  · have hpval : s'.phase.val = 6 := by simpa [hp]
    rcases hs'_le_or_ten with hle | hten <;> omega
  · have hpval : s'.phase.val = 7 := by simpa [hp]
    rcases hs'_le_or_ten with hle | hten <;> omega
  · have hpval : s'.phase.val = 8 := by simpa [hp]
    rcases hs'_le_or_ten with hle | hten <;> omega
  · have hpval : s'.phase.val = 9 := by simpa [hp]
    rcases hs'_le_or_ten with hle | hten <;> omega
  · have hpval : s'.phase.val = 10 := by simpa [hp]
    have hlocal_phase : (Phase10Transition L K s' t').2.phase.val = 2 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have ht'_phase : t'.phase.val = 2 := by
      have heq := (Phase10Transition_phase_eq (L := L) (K := K) s' t').2
      have hval : (Phase10Transition L K s' t').2.phase.val = t'.phase.val := by
        rw [heq]
      omega
    have hlocal_small : (Phase10Transition L K s' t').2.smallBias.val = 3 := by
      have hne : (Phase10Transition L K s' t').2.phase.val ≠ 10 := by omega
      simpa [hp, finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) t' (Phase10Transition L K s' t').2 hne] using
        hsmall_final
    have ht'_small : t'.smallBias.val = 3 := by
      have hpres := (Phase10Transition_preserves_smallBias_pair (L := L) (K := K) s' t').2
      simpa [hpres] using hlocal_small
    have ht'_op0 := phaseEpidemicUpdate_right_phase2_opinion_T_of_left_le_two
      (L := L) (K := K) s t hs_le ht_le ht_prev
      (by simpa [he] using ht'_phase) (by simpa [he] using ht'_small)
    have ht'_op : t'.opinions = phase2OpinionT := by
      simpa [he] using ht'_op0
    have hop_local : (Phase10Transition L K s' t').2.opinions = t'.opinions := by
      unfold Phase10Transition
      dsimp only
      split_ifs <;> rfl
    simpa [hp, finishPhase10Entry_eq_self_of_after_ne_10
      (L := L) (K := K) t' (Phase10Transition L K s' t').2 (by omega),
      hop_local, ht'_op]

private theorem Transition_second_phase2_to_phase2_preserves_signSupport
    (s t : AgentState L K) (ht : t.phase.val = 2)
    (hss : phase2SignSupport t)
    (hphase : (Transition L K s t).2.phase.val = 2) :
    phase2SignSupport (Transition L K s t).2 := by
  have hs_le : s.phase.val ≤ 2 := by
    have hmax := Transition_right_phase_ge_pair_max (L := L) (K := K) s t
    rw [hphase] at hmax
    omega
  have ht_epi :=
    phaseEpidemicUpdate_right_phase2_support_of_left_le_two (L := L) (K := K)
      s t ht hs_le hss
  have hs_epi_phase :=
    phaseEpidemicUpdate_left_phase_two_or_ten_of_right_phase2_left_le_two
      (L := L) (K := K) s t ht hs_le
  unfold Transition
  generalize he : phaseEpidemicUpdate L K s t = e
  rcases e with ⟨s', t'⟩
  have ht'_support : phase2SignSupport t' := by
    simpa [he] using ht_epi.1
  have ht'_phase : t'.phase.val = 2 ∨ t'.phase.val = 10 := by
    simpa [he] using ht_epi.2
  have hs'_phase : s'.phase.val = 2 ∨ s'.phase.val = 10 := by
    simpa [he] using hs_epi_phase
  change phase2SignSupport
    (finishPhase10Entry L K t'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).2)
  generalize hp : s'.phase = p
  fin_cases p
  · have hs'_le : s'.phase.val = 0 := by simpa [hp]
    rcases hs'_phase with hs' | hs' <;> omega
  · have hs'_le : s'.phase.val = 1 := by simpa [hp]
    rcases hs'_phase with hs' | hs' <;> omega
  · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
      t' (Phase2Transition L K s' t').2
      (Phase2Transition_preserves_phase2SignSupport_right (L := L) (K := K)
        s' t' ht'_support)
  · have hs'_val : s'.phase.val = 3 := by simpa [hp]
    rcases hs'_phase with hs' | hs' <;> omega
  · have hs'_val : s'.phase.val = 4 := by simpa [hp]
    rcases hs'_phase with hs' | hs' <;> omega
  · have hs'_val : s'.phase.val = 5 := by simpa [hp]
    rcases hs'_phase with hs' | hs' <;> omega
  · have hs'_val : s'.phase.val = 6 := by simpa [hp]
    rcases hs'_phase with hs' | hs' <;> omega
  · have hs'_val : s'.phase.val = 7 := by simpa [hp]
    rcases hs'_phase with hs' | hs' <;> omega
  · have hs'_val : s'.phase.val = 8 := by simpa [hp]
    rcases hs'_phase with hs' | hs' <;> omega
  · have hs'_val : s'.phase.val = 9 := by simpa [hp]
    rcases hs'_phase with hs' | hs' <;> omega
  · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
      t' (Phase10Transition L K s' t').2
      (Phase10Transition_preserves_phase2SignSupport_right (L := L) (K := K)
        s' t' ht'_support)

private theorem Transition_left_phase2SignSupport
    (s t : AgentState L K)
    (hsupport : s.phase.val = 2 → phase2SignSupport s)
    (hphase : (Transition L K s t).1.phase.val = 2) :
    phase2SignSupport (Transition L K s t).1 := by
  have hphase_orig := hphase
  by_cases hs_lt : s.phase.val < 2
  · unfold Transition at hphase ⊢
    generalize he : phaseEpidemicUpdate L K s t = e at hphase ⊢
    rcases e with ⟨s', t'⟩
    have ht_le : t.phase.val ≤ 2 := by
      have hmax := Transition_left_phase_ge_pair_max (L := L) (K := K) s t
      rw [hphase_orig] at hmax
      omega
    have hs'_not_high : s'.phase.val ≤ 2 ∨ s'.phase.val = 10 := by
      simpa [he] using
        phaseEpidemicUpdate_left_phase_le_two_or_ten_of_phases_le_two
          (L := L) (K := K) s t (by omega) ht_le
    have hs'_entered :
        s'.phase.val = 2 → phase2SignSupport s' := by
      intro hs'_phase
      simpa [he] using
        phaseEpidemicUpdate_left_phase2SignSupport_of_entered
          (L := L) (K := K) s t hs_lt (by simpa [he] using hs'_phase)
    change phase2SignSupport
      (finishPhase10Entry L K s'
        (match s'.phase with
        | ⟨0, _⟩ => Phase0Transition L K s' t'
        | ⟨1, _⟩ => Phase1Transition L K s' t'
        | ⟨2, _⟩ => Phase2Transition L K s' t'
        | ⟨3, _⟩ => Phase3Transition L K s' t'
        | ⟨4, _⟩ => Phase4Transition L K s' t'
        | ⟨5, _⟩ => Phase5Transition L K s' t'
        | ⟨6, _⟩ => Phase6Transition L K s' t'
        | ⟨7, _⟩ => Phase7Transition L K s' t'
        | ⟨8, _⟩ => Phase8Transition L K s' t'
        | ⟨9, _⟩ => Phase9Transition L K s' t'
        | ⟨10, _⟩ => Phase10Transition L K s' t'
        | _ => (s', t')).1)
    generalize hp : s'.phase = p
    fin_cases p
    · have hpval : s'.phase.val = 0 := by simpa [hp]
      have hlocal : (Phase0Transition L K s' t').1.phase.val = 2 := by
        simpa [hp] using hphase
      exact False.elim
        (Phase0Transition_left_phase_ne_two_of_phase_zero
          (L := L) (K := K) s' t' hpval hlocal)
    · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
        s' (Phase1Transition L K s' t').1
        (Phase1Transition_left_phase2SignSupport (L := L) (K := K)
          s' t' (by simpa [hp]) (by simpa [hp] using hphase))
    · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
        s' (Phase2Transition L K s' t').1
        (Phase2Transition_preserves_phase2SignSupport_left (L := L) (K := K)
          s' t' (hs'_entered (by simpa [hp])))
    · have hpval : s'.phase.val = 3 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 4 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 5 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 6 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 7 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 8 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 9 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 10 := by simpa [hp]
      have hmono := (Phase10Transition_phase_nondec (L := L) (K := K) s' t').1
      have hout : (Phase10Transition L K s' t').1.phase.val = 2 := by
        simpa [hp, finishPhase10Entry_phase_val] using hphase
      have hphase_eq := (Phase10Transition_phase_eq (L := L) (K := K) s' t').1
      rw [hphase_eq] at hout
      omega

  · have hs_ge : 2 ≤ s.phase.val := by omega
    have hs_eq : s.phase.val = 2 := by
      have hmono := (Transition_phase_monotone (L := L) (K := K) s t).1
      change s.phase.val ≤ (Transition L K s t).1.phase.val at hmono
      rw [hphase_orig] at hmono
      omega
    exact Transition_phase2_to_phase2_preserves_signSupport (L := L) (K := K)
      s t hs_eq (hsupport hs_eq) hphase

private theorem Transition_right_phase2SignSupport
    (s t : AgentState L K)
    (htupport : t.phase.val = 2 → phase2SignSupport t)
    (hphase : (Transition L K s t).2.phase.val = 2) :
    phase2SignSupport (Transition L K s t).2 := by
  have hphase_orig := hphase
  by_cases ht_lt : t.phase.val < 2
  · unfold Transition at hphase ⊢
    generalize he : phaseEpidemicUpdate L K s t = e at hphase ⊢
    rcases e with ⟨s', t'⟩
    have hs_le : s.phase.val ≤ 2 := by
      have hmax := Transition_right_phase_ge_pair_max (L := L) (K := K) s t
      rw [hphase_orig] at hmax
      omega
    have ht'_not_high : t'.phase.val ≤ 2 ∨ t'.phase.val = 10 := by
      simpa [he] using
        phaseEpidemicUpdate_right_phase_le_two_or_ten_of_phases_le_two
          (L := L) (K := K) s t hs_le (by omega)
    have hs'_not_high : s'.phase.val ≤ 2 ∨ s'.phase.val = 10 := by
      simpa [he] using
        phaseEpidemicUpdate_left_phase_le_two_or_ten_of_phases_le_two
          (L := L) (K := K) s t hs_le (by omega)
    have ht'_entered :
        t'.phase.val = 2 → phase2SignSupport t' := by
      intro ht'_phase
      simpa [he] using
        phaseEpidemicUpdate_right_phase2SignSupport_of_entered
          (L := L) (K := K) s t ht_lt (by simpa [he] using ht'_phase)
    change phase2SignSupport
      (finishPhase10Entry L K t'
        (match s'.phase with
        | ⟨0, _⟩ => Phase0Transition L K s' t'
        | ⟨1, _⟩ => Phase1Transition L K s' t'
        | ⟨2, _⟩ => Phase2Transition L K s' t'
        | ⟨3, _⟩ => Phase3Transition L K s' t'
        | ⟨4, _⟩ => Phase4Transition L K s' t'
        | ⟨5, _⟩ => Phase5Transition L K s' t'
        | ⟨6, _⟩ => Phase6Transition L K s' t'
        | ⟨7, _⟩ => Phase7Transition L K s' t'
        | ⟨8, _⟩ => Phase8Transition L K s' t'
        | ⟨9, _⟩ => Phase9Transition L K s' t'
        | ⟨10, _⟩ => Phase10Transition L K s' t'
        | _ => (s', t')).2)
    generalize hp : s'.phase = p
    fin_cases p
    · have hs0 : s'.phase.val = 0 := by simpa [hp]
      have hlocal : (Phase0Transition L K s' t').2.phase.val = 2 := by
        simpa [hp] using hphase
      have ht'_not_ten : t'.phase.val ≠ 10 := by
        intro ht_ten
        have hmono := (Phase0Transition_phase_nondec (L := L) (K := K) s' t').2
        change t'.phase.val ≤ (Phase0Transition L K s' t').2.phase.val at hmono
        omega
      have hs'_not_ten : s'.phase.val ≠ 10 := by omega
      have hsync :=
        phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
          (L := L) (K := K) s t hs_le (by omega)
          (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
      have hsync' : s'.phase.val = t'.phase.val := by
        simpa [he] using hsync
      have ht0 : t'.phase.val = 0 := by omega
      exact False.elim
        (Phase0Transition_right_phase_ne_two_of_phase_zero
          (L := L) (K := K) s' t' ht0 hlocal)
    · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
        t' (Phase1Transition L K s' t').2
        (Phase1Transition_right_phase2SignSupport (L := L) (K := K)
          s' t' (by
            have hs1 : s'.phase.val = 1 := by simpa [hp]
            have ht'_not_ten : t'.phase.val ≠ 10 := by
              intro ht_ten
              have hmono := (Phase1Transition_phase_nondec (L := L) (K := K) s' t').2
              change t'.phase.val ≤ (Phase1Transition L K s' t').2.phase.val at hmono
              have hlocal : (Phase1Transition L K s' t').2.phase.val = 2 := by
                simpa [hp] using hphase
              omega
            have hs'_not_ten : s'.phase.val ≠ 10 := by omega
            have hsync :=
              phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
                (L := L) (K := K) s t hs_le (by omega)
                (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
            have hsync' : s'.phase.val = t'.phase.val := by
              simpa [he] using hsync
            omega)
          (by simpa [hp] using hphase))
    · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
        t' (Phase2Transition L K s' t').2
        (Phase2Transition_preserves_phase2SignSupport_right (L := L) (K := K)
          s' t' (ht'_entered (by
            have hs2 : s'.phase.val = 2 := by simpa [hp]
            have ht'_not_ten : t'.phase.val ≠ 10 := by
              intro ht_ten
              have hmono := (Phase2Transition_phase_nondec (L := L) (K := K) s' t').2
              change t'.phase.val ≤ (Phase2Transition L K s' t').2.phase.val at hmono
              have hlocal : (Phase2Transition L K s' t').2.phase.val = 2 := by
                simpa [hp] using hphase
              omega
            have hs'_not_ten : s'.phase.val ≠ 10 := by omega
            have hsync :=
              phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
                (L := L) (K := K) s t hs_le (by omega)
                (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
            have hsync' : s'.phase.val = t'.phase.val := by
              simpa [he] using hsync
            omega)))
    · have hpval : s'.phase.val = 3 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 4 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 5 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 6 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 7 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 8 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 9 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 10 := by simpa [hp]
      rcases hs'_not_high with hle | hten
      · omega
      · have ht2 : t'.phase.val = 2 := by
          have hout : (Phase10Transition L K s' t').2.phase.val = 2 := by
            simpa [hp] using hphase
          have hphase_eq := (Phase10Transition_phase_eq (L := L) (K := K) s' t').2
          have hval : (Phase10Transition L K s' t').2.phase.val = t'.phase.val := by
            rw [hphase_eq]
          omega
        change phase2SignSupport
          (finishPhase10Entry L K t' (Phase10Transition L K s' t').2)
        exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
          t' (Phase10Transition L K s' t').2
          (Phase10Transition_preserves_phase2SignSupport_right (L := L) (K := K)
            s' t' (ht'_entered ht2))
  · have ht_eq : t.phase.val = 2 := by
      have hmono := (Transition_phase_monotone (L := L) (K := K) s t).2
      change t.phase.val ≤ (Transition L K s t).2.phase.val at hmono
      rw [hphase_orig] at hmono
      omega
    exact Transition_second_phase2_to_phase2_preserves_signSupport
      (L := L) (K := K) s t ht_eq (htupport ht_eq) hphase

private theorem StepRel_phase2SignSupport
    {c c' : Config (AgentState L K)}
    (hc : ∀ a ∈ c, a.phase.val = 2 → phase2SignSupport a)
    (hstep : (NonuniformMajority L K).StepRel c c') :
    ∀ a ∈ c', a.phase.val = 2 → phase2SignSupport a := by
  rcases hstep with ⟨s, t, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
  have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
  rw [hc']
  intro a ha hphase
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with h_old | h_new
  · exact hc a (Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) h_old) hphase
  · rcases h_new with h_eq | h_eq
    · subst a
      exact Transition_left_phase2SignSupport (L := L) (K := K) s t
        (fun hs => hc s hs_mem hs) hphase
    · subst a
      exact Transition_right_phase2SignSupport (L := L) (K := K) s t
        (fun ht => hc t ht_mem ht) hphase

theorem reachable_phase2SignSupport
    (init c : Config (AgentState L K))
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c) :
    ∀ a ∈ c, a.phase.val = 2 → phase2SignSupport a := by
  induction hreach with
  | refl =>
      intro a ha hphase
      have hphase0 := (hvalid a ha).1
      have hval0 : a.phase.val = 0 := by
        simpa [hphase0]
      omega
  | tail _ hstep ih =>
      exact StepRel_phase2SignSupport (L := L) (K := K) ih hstep

private theorem clockCounterStep_phase2_smallBias_noerror
    (a : AgentState L K)
    (hphase : a.phase.val = 1)
    (hout : (clockCounterStep L K a).phase.val = 2) :
    (clockCounterStep L K a).smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  have hphase_eq : phase = ⟨1, by decide⟩ := Fin.ext hphase
  subst phase
  cases role
  · simp [clockCounterStep] at hout
  · simp [clockCounterStep] at hout
  · by_cases hcounter : counter.val = 0
    · let a2 : AgentState L K :=
        { input := input, output := output, phase := ⟨2, by decide⟩,
          role := Role.clock, assigned := assigned, bias := bias,
          smallBias := smallBias, hour := hour, minute := minute,
          full := full, opinions := opinions, counter := counter }
      have hinit_phase : (phaseInit L K ⟨2, by decide⟩ a2).phase.val = 2 := by
        simpa [a2, clockCounterStep, stdCounterSubroutine, advancePhaseWithInit,
          advancePhase, hcounter] using hout
      have hno := phaseInit_two_smallBias_noerror (L := L) (K := K) a2 hinit_phase
      simpa [a2, clockCounterStep, stdCounterSubroutine, advancePhaseWithInit,
        advancePhase, hcounter] using hno
    · simp [clockCounterStep, stdCounterSubroutine, hcounter] at hout
  · simp [clockCounterStep] at hout
  · simp [clockCounterStep] at hout

private theorem Phase2Transition_left_preserves_smallBias_noerror
    (s t : AgentState L K)
    (hs : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    (Phase2Transition L K s t).1.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  have hsmall := (Phase2Transition_preserves_smallBias L K s t).1
  rw [hsmall]
  exact hs

private theorem Phase2Transition_right_preserves_smallBias_noerror
    (s t : AgentState L K)
    (ht : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    (Phase2Transition L K s t).2.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  have hsmall := (Phase2Transition_preserves_smallBias L K s t).2
  rw [hsmall]
  exact ht

private theorem Transition_phase2_to_phase2_preserves_smallBias_noerror_left
    (s t : AgentState L K) (hs : s.phase.val = 2)
    (hsmall : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hphase : (Transition L K s t).1.phase.val = 2) :
    (Transition L K s t).1.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  have heq := Transition_left_smallBias_eq_of_phase2_to_phase2
    (L := L) (K := K) s t hs hphase
  rw [heq]
  exact hsmall

private theorem Transition_phase2_to_phase2_preserves_smallBias_noerror_right
    (s t : AgentState L K) (ht : t.phase.val = 2)
    (hsmall : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hphase : (Transition L K s t).2.phase.val = 2) :
    (Transition L K s t).2.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  have heq := Transition_right_smallBias_eq_of_phase2_to_phase2
    (L := L) (K := K) s t ht hphase
  rw [heq]
  exact hsmall

theorem Transition_left_phase2_smallBias_noerror
    (s t : AgentState L K)
    (hsupport : s.phase.val = 2 →
      s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hphase : (Transition L K s t).1.phase.val = 2) :
    (Transition L K s t).1.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  have hphase_orig := hphase
  by_cases hs_lt : s.phase.val < 2
  · unfold Transition at hphase ⊢
    generalize he : phaseEpidemicUpdate L K s t = e
    rcases e with ⟨s', t'⟩
    rw [he] at hphase
    have ht_le : t.phase.val ≤ 2 := by
      have hmax := Transition_left_phase_ge_pair_max (L := L) (K := K) s t
      rw [hphase_orig] at hmax
      omega
    have hs'_not_high : s'.phase.val ≤ 2 ∨ s'.phase.val = 10 := by
      simpa [he] using
        phaseEpidemicUpdate_left_phase_le_two_or_ten_of_phases_le_two
          (L := L) (K := K) s t (by omega) ht_le
    have hs'_entered :
        s'.phase.val = 2 →
          s'.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
      intro hs'_phase
      simpa [he] using
        phaseEpidemicUpdate_left_smallBias_noerror_of_entered
          (L := L) (K := K) s t hs_lt (by simpa [he] using hs'_phase)
    change (finishPhase10Entry L K s'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).1).smallBias.val ∈ ({2, 3, 4} : Finset ℕ)
    generalize hp : s'.phase = p
    fin_cases p
    · have hpval : s'.phase.val = 0 := by simpa [hp]
      have hlocal : (Phase0Transition L K s' t').1.phase.val = 2 := by
        simpa [hp] using hphase
      exact False.elim
        (Phase0Transition_left_phase_ne_two_of_phase_zero
          (L := L) (K := K) s' t' hpval hlocal)
    · have hlocal := Phase1Transition_left_phase2_smallBias_noerror
        (L := L) (K := K) s' t' (by simpa [hp]) (by simpa [hp] using hphase)
      simpa [hp, finishPhase10Entry_smallBias] using hlocal
    · have hsmall :=
        Phase2Transition_left_preserves_smallBias_noerror
          (L := L) (K := K) s' t' (hs'_entered (by simpa [hp]))
      simpa [hp, finishPhase10Entry_smallBias] using hsmall
    · have hpval : s'.phase.val = 3 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 4 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 5 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 6 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 7 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 8 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 9 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 10 := by simpa [hp]
      have hmono := (Phase10Transition_phase_nondec (L := L) (K := K) s' t').1
      have hout : (Phase10Transition L K s' t').1.phase.val = 2 := by
        simpa [hp] using hphase
      omega
  · have hs_eq : s.phase.val = 2 := by
      have hmono := (Transition_phase_monotone (L := L) (K := K) s t).1
      have hphase_nat : (Transition L K s t).1.phase.val = 2 := hphase
      change s.phase.val ≤ (Transition L K s t).1.phase.val at hmono
      rw [hphase_nat] at hmono
      omega
    exact Transition_phase2_to_phase2_preserves_smallBias_noerror_left
      (L := L) (K := K) s t hs_eq (hsupport hs_eq) hphase

theorem Transition_right_phase2_smallBias_noerror
    (s t : AgentState L K)
    (htupport : t.phase.val = 2 →
      t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hphase : (Transition L K s t).2.phase.val = 2) :
    (Transition L K s t).2.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  have hphase_orig := hphase
  by_cases ht_lt : t.phase.val < 2
  · unfold Transition at hphase ⊢
    generalize he : phaseEpidemicUpdate L K s t = e at hphase ⊢
    rcases e with ⟨s', t'⟩
    have hs_le : s.phase.val ≤ 2 := by
      have hmax := Transition_right_phase_ge_pair_max (L := L) (K := K) s t
      rw [hphase_orig] at hmax
      omega
    have ht'_not_high : t'.phase.val ≤ 2 ∨ t'.phase.val = 10 := by
      simpa [he] using
        phaseEpidemicUpdate_right_phase_le_two_or_ten_of_phases_le_two
          (L := L) (K := K) s t hs_le (by omega)
    have hs'_not_high : s'.phase.val ≤ 2 ∨ s'.phase.val = 10 := by
      simpa [he] using
        phaseEpidemicUpdate_left_phase_le_two_or_ten_of_phases_le_two
          (L := L) (K := K) s t hs_le (by omega)
    have ht'_entered :
        t'.phase.val = 2 →
          t'.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
      intro ht'_phase
      simpa [he] using
        phaseEpidemicUpdate_right_smallBias_noerror_of_entered
          (L := L) (K := K) s t ht_lt (by simpa [he] using ht'_phase)
    change (finishPhase10Entry L K t'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).2).smallBias.val ∈ ({2, 3, 4} : Finset ℕ)
    generalize hp : s'.phase = p
    fin_cases p
    · have hs0 : s'.phase.val = 0 := by simpa [hp]
      have hlocal : (Phase0Transition L K s' t').2.phase.val = 2 := by
        simpa [hp] using hphase
      have ht'_not_ten : t'.phase.val ≠ 10 := by
        intro ht_ten
        have hmono := (Phase0Transition_phase_nondec (L := L) (K := K) s' t').2
        omega
      have hs'_not_ten : s'.phase.val ≠ 10 := by omega
      have hsync :=
        phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
          (L := L) (K := K) s t hs_le (by omega)
          (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
      have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
      have ht0 : t'.phase.val = 0 := by omega
      exact False.elim
        (Phase0Transition_right_phase_ne_two_of_phase_zero
          (L := L) (K := K) s' t' ht0 hlocal)
    · have hlocal := Phase1Transition_right_phase2_smallBias_noerror
        (L := L) (K := K) s' t'
        (by
          have hs1 : s'.phase.val = 1 := by simpa [hp]
          have ht'_not_ten : t'.phase.val ≠ 10 := by
            intro ht_ten
            have hmono := (Phase1Transition_phase_nondec (L := L) (K := K) s' t').2
            have hlocal : (Phase1Transition L K s' t').2.phase.val = 2 := by
              simpa [hp] using hphase
            omega
          have hs'_not_ten : s'.phase.val ≠ 10 := by omega
          have hsync :=
            phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
              (L := L) (K := K) s t hs_le (by omega)
              (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
          have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
          omega)
        (by simpa [hp] using hphase)
      simpa [hp, finishPhase10Entry_smallBias] using hlocal
    · have ht2 : t'.phase.val = 2 := by
        have hs2 : s'.phase.val = 2 := by simpa [hp]
        have ht'_not_ten : t'.phase.val ≠ 10 := by
          intro ht_ten
          have hmono := (Phase2Transition_phase_nondec (L := L) (K := K) s' t').2
          have hlocal : (Phase2Transition L K s' t').2.phase.val = 2 := by
            simpa [hp] using hphase
          omega
        have hs'_not_ten : s'.phase.val ≠ 10 := by omega
        have hsync :=
          phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
            (L := L) (K := K) s t hs_le (by omega)
            (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
        have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
        omega
      have hsmall :=
        Phase2Transition_right_preserves_smallBias_noerror
          (L := L) (K := K) s' t' (ht'_entered ht2)
      simpa [hp, finishPhase10Entry_smallBias] using hsmall
    · have hpval : s'.phase.val = 3 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 4 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 5 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 6 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 7 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 8 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 9 := by simpa [hp]
      rcases hs'_not_high with hle | hten <;> omega
    · have hpval : s'.phase.val = 10 := by simpa [hp]
      have hout : (Phase10Transition L K s' t').2.phase.val = 2 := by
        simpa [hp, finishPhase10Entry_phase_val] using hphase
      have hphase_eq := (Phase10Transition_phase_eq (L := L) (K := K) s' t').2
      have ht2 : t'.phase.val = 2 := by
        rw [hphase_eq] at hout
        exact hout
      have hsmall := ht'_entered ht2
      have hpres := (Phase10Transition_preserves_smallBias_pair (L := L) (K := K) s' t').2
      simpa [hp, finishPhase10Entry_smallBias, hpres] using hsmall
  · have ht_eq : t.phase.val = 2 := by
      have hmono := (Transition_phase_monotone (L := L) (K := K) s t).2
      have hphase_nat : (Transition L K s t).2.phase.val = 2 := hphase
      change t.phase.val ≤ (Transition L K s t).2.phase.val at hmono
      rw [hphase_nat] at hmono
      omega
    exact Transition_phase2_to_phase2_preserves_smallBias_noerror_right
      (L := L) (K := K) s t ht_eq (htupport ht_eq) hphase

private theorem StepRel_phase2_smallBias_noerror
    {c c' : Config (AgentState L K)}
    (hc : ∀ a ∈ c, a.phase.val = 2 →
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hstep : (NonuniformMajority L K).StepRel c c') :
    ∀ a ∈ c', a.phase.val = 2 →
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  rcases hstep with ⟨s, t, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
  have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
  rw [hc']
  intro a ha hphase
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with h_old | h_new
  · exact hc a (Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) h_old) hphase
  · rcases h_new with h_eq | h_eq
    · subst a
      exact Transition_left_phase2_smallBias_noerror (L := L) (K := K) s t
        (fun hs => hc s hs_mem hs) hphase
    · subst a
      exact Transition_right_phase2_smallBias_noerror (L := L) (K := K) s t
        (fun ht => hc t ht_mem ht) hphase

theorem reachable_phase2_smallBias_noerror
    (init c : Config (AgentState L K))
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c) :
    ∀ a ∈ c, a.phase.val = 2 →
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  induction hreach with
  | refl =>
      intro a ha hphase
      have hphase0 := (hvalid a ha).1
      have hval0 : a.phase.val = 0 := by simpa [hphase0]
      omega
  | tail _ hstep ih =>
      exact StepRel_phase2_smallBias_noerror (L := L) (K := K) ih hstep


/-- Broader noerror invariant: in reachable configs with all phases ≤ 4,
every agent with phase ≥ 2 has smallBias ∈ {2,3,4}. -/
theorem reachable_phase_ge2_smallBias_noerror_of_phases_le_four
    (init c : Config (AgentState L K))
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase_le4 : ∀ a ∈ c, a.phase.val ≤ 4) :
    ∀ a ∈ c, 2 ≤ a.phase.val →
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  induction hreach with
  | refl =>
      intro a ha hge2
      have hphase0 := (hvalid a ha).1
      have hval0 : a.phase.val = 0 := by simpa [hphase0]
      omega
  | tail hprev hstep ih =>
      have hphase_prev :=
        StepRel_phase_le_of_next_phase_le_four (L := L) (K := K) _ _ hstep hphase_le4
      have ih_prev := ih hphase_prev
      rcases hstep with ⟨r₁, r₂, happ, hc'⟩
      dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
      have hr₁_mem : r₁ ∈ _ := Multiset.mem_of_le happ (by simp)
      have hr₂_mem : r₂ ∈ _ := Multiset.mem_of_le happ (by simp)
      rw [hc']
      intro a ha hge2
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
      rcases ha with h_old | h_new
      · exact ih_prev a (Multiset.mem_of_le (Multiset.sub_le_self _ {r₁, r₂}) h_old) hge2
      · rcases h_new with h_eq | h_eq
        · subst a
          by_cases hr₁_ge2 : 2 ≤ r₁.phase.val
          · have hpres := Transition_left_preserves_smallBias_of_phase_ge_two
              (L := L) (K := K) r₁ r₂ hr₁_ge2
            rw [hpres]
            exact ih_prev r₁ hr₁_mem hr₁_ge2
          · push_neg at hr₁_ge2
            have hout1_le4 : (Transition L K r₁ r₂).1.phase.val ≤ 4 := by
              apply hphase_le4
              rw [hc']; exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_self _ _))
            have hep_small := (phaseEpidemicUpdate_preserves_smallBias L K r₁ r₂).1
            have hep_le := (phaseEpidemicUpdate_phase_le_Transition_phase
              (L := L) (K := K) r₁ r₂).1
            by_cases hep_ge2 : 2 ≤ (phaseEpidemicUpdate L K r₁ r₂).1.phase.val
            · have hep_le4 : (phaseEpidemicUpdate L K r₁ r₂).1.phase.val ≤ 4 :=
                le_trans hep_le hout1_le4
              have hnoerr := phaseEpidemicUpdate_left_smallBias_noerror_of_entered_to_four
                (L := L) (K := K) r₁ r₂ hr₁_ge2 hep_ge2 hep_le4
              have hpres := Transition_left_smallBias_eq_epidemic_of_epidemic_phase_ge_two
                (L := L) (K := K) r₁ r₂ hep_ge2
              rw [hpres]
              exact hnoerr
            · push_neg at hep_ge2
              have hout1_le2 :=
                Transition_left_phase_le_two_of_epidemic_phase_lt_two
                  (L := L) (K := K) r₁ r₂ hep_ge2 (by
                    apply hphase_le4
                    rw [hc']; exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_self _ _)))
              have hout1_eq2 : (Transition L K r₁ r₂).1.phase.val = 2 := by omega
              exact Transition_left_phase2_smallBias_noerror
                (L := L) (K := K) r₁ r₂ (by intro h; omega) hout1_eq2
        · subst a
          by_cases hr₂_ge2 : 2 ≤ r₂.phase.val
          · have hpres := Transition_right_preserves_smallBias_of_phase_ge_two
              (L := L) (K := K) r₁ r₂ hr₂_ge2
            rw [hpres]
            exact ih_prev r₂ hr₂_mem hr₂_ge2
          · push_neg at hr₂_ge2
            have hout2_le4 : (Transition L K r₁ r₂).2.phase.val ≤ 4 := by
              apply hphase_le4
              rw [hc']; exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_of_mem (by simp)))
            have hep_small := (phaseEpidemicUpdate_preserves_smallBias L K r₁ r₂).2
            have hep_le := (phaseEpidemicUpdate_phase_le_Transition_phase
              (L := L) (K := K) r₁ r₂).2
            by_cases hep_ge2 : 2 ≤ (phaseEpidemicUpdate L K r₁ r₂).1.phase.val
            · have hep_le4 : (phaseEpidemicUpdate L K r₁ r₂).2.phase.val ≤ 4 :=
                le_trans hep_le hout2_le4
              have hep1_le4 : (phaseEpidemicUpdate L K r₁ r₂).1.phase.val ≤ 4 := by
                apply le_trans (phaseEpidemicUpdate_phase_le_Transition_phase
                  (L := L) (K := K) r₁ r₂).1
                apply hphase_le4
                rw [hc']; exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_self _ _))
              have hphase_eq := phaseEpidemicUpdate_phases_eq_of_outputs_le_four
                (L := L) (K := K) r₁ r₂ hep1_le4 hep_le4
              have hep2_ge2 : 2 ≤ (phaseEpidemicUpdate L K r₁ r₂).2.phase.val := by
                rw [← hphase_eq]; exact hep_ge2
              have hnoerr := phaseEpidemicUpdate_right_smallBias_noerror_of_entered_to_four
                (L := L) (K := K) r₁ r₂ hr₂_ge2 hep2_ge2 hep_le4
              have hpres := Transition_right_smallBias_eq_epidemic_of_epidemic_phase_ge_two
                (L := L) (K := K) r₁ r₂ hep_ge2
              rw [hpres]
              exact hnoerr
            · push_neg at hep_ge2
              have hout2_le2 :=
                Transition_right_phase_le_two_of_epidemic_phase_lt_two
                  (L := L) (K := K) r₁ r₂ hep_ge2 (by
                    apply hphase_le4
                    rw [hc']; exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_of_mem (by simp))))
              have hout2_eq2 : (Transition L K r₁ r₂).2.phase.val = 2 := by omega
              exact Transition_right_phase2_smallBias_noerror
                (L := L) (K := K) r₁ r₂ (by intro h; omega) hout2_eq2

private lemma prePhase4Mass_phaseInit_three_of_carrier_chain
    (a : AgentState L K)
    (hcarrier : nonMainCarrierSmallBiasZeroAgent a)
    (hmcr : a.role ≠ .mcr)
    (hsmall : a.smallBias.val = 2 ∨ a.smallBias.val = 3 ∨ a.smallBias.val = 4) :
    prePhase4Mass (phaseInit L K ⟨3, by decide⟩ a) =
      (AgentState.smallBiasInt a : ℚ) := by
  rcases hsmall with h2 | h34
  · cases hrole : a.role <;>
      simp [prePhase4Mass, phaseInit, AgentState.smallBiasInt, Bias.toRat,
        hrole, h2, nonMainCarrierSmallBiasZeroAgent] at hcarrier hmcr ⊢
  · rcases h34 with h3 | h4
    · cases hrole : a.role <;>
        simp [prePhase4Mass, phaseInit, AgentState.smallBiasInt, Bias.toRat,
          hrole, h3, nonMainCarrierSmallBiasZeroAgent] at hcarrier hmcr ⊢
    · cases hrole : a.role <;>
        simp [prePhase4Mass, phaseInit, AgentState.smallBiasInt, Bias.toRat,
          hrole, h4, nonMainCarrierSmallBiasZeroAgent] at hcarrier hmcr ⊢

private lemma prePhase4Mass_advancePhaseWithInit_of_phase_two
    (a : AgentState L K)
    (hphase : a.phase.val = 2)
    (hcarrier : nonMainCarrierSmallBiasZeroAgent a)
    (hmcr : a.role ≠ .mcr)
    (hsmall : a.smallBias.val = 2 ∨ a.smallBias.val = 3 ∨ a.smallBias.val = 4) :
    prePhase4Mass (advancePhaseWithInit L K a) =
      (AgentState.smallBiasInt a : ℚ) := by
  have hphase_eq : a.phase = ⟨2, by decide⟩ := Fin.ext hphase
  have hcarrier' :
      nonMainCarrierSmallBiasZeroAgent
        ({ a with phase := ⟨3, by decide⟩ } : AgentState L K) := by
    simpa [nonMainCarrierSmallBiasZeroAgent] using hcarrier
  have hmcr' :
      ({ a with phase := ⟨3, by decide⟩ } : AgentState L K).role ≠ .mcr := by
    simpa using hmcr
  have hsmall' :
      ({ a with phase := ⟨3, by decide⟩ } : AgentState L K).smallBias.val = 2 ∨
        ({ a with phase := ⟨3, by decide⟩ } : AgentState L K).smallBias.val = 3 ∨
        ({ a with phase := ⟨3, by decide⟩ } : AgentState L K).smallBias.val = 4 := by
    simpa using hsmall
  have hinit :=
    prePhase4Mass_phaseInit_three_of_carrier_chain
      (L := L) (K := K) ({ a with phase := ⟨3, by decide⟩ } : AgentState L K)
      hcarrier' hmcr' hsmall'
  simpa [advancePhaseWithInit, advancePhase, hphase_eq, AgentState.smallBiasInt]
    using hinit

private lemma Phase2Transition_preserves_prePhase4Mass_pair_of_phase_two
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hs_carrier : nonMainCarrierSmallBiasZeroAgent s)
    (ht_carrier : nonMainCarrierSmallBiasZeroAgent t)
    (hs_mcr : s.role ≠ .mcr) (ht_mcr : t.role ≠ .mcr)
    (hs_small : s.smallBias.val = 2 ∨ s.smallBias.val = 3 ∨ s.smallBias.val = 4)
    (ht_small : t.smallBias.val = 2 ∨ t.smallBias.val = 3 ∨ t.smallBias.val = 4) :
    prePhase4Mass (Phase2Transition L K s t).1 +
      prePhase4Mass (Phase2Transition L K s t).2 =
    prePhase4Mass s + prePhase4Mass t := by
  let univ := opinionsUnion s.opinions t.opinions
  let s' : AgentState L K := { s with opinions := univ }
  let t' : AgentState L K := { t with opinions := univ }
  have hs'_phase : s'.phase.val = 2 := by simp [s', hs_phase]
  have ht'_phase : t'.phase.val = 2 := by simp [t', ht_phase]
  have hs'_carrier : nonMainCarrierSmallBiasZeroAgent s' := by
    simpa [s', nonMainCarrierSmallBiasZeroAgent] using hs_carrier
  have ht'_carrier : nonMainCarrierSmallBiasZeroAgent t' := by
    simpa [t', nonMainCarrierSmallBiasZeroAgent] using ht_carrier
  have hs'_mcr : s'.role ≠ .mcr := by simpa [s'] using hs_mcr
  have ht'_mcr : t'.role ≠ .mcr := by simpa [t'] using ht_mcr
  have hs'_small :
      s'.smallBias.val = 2 ∨ s'.smallBias.val = 3 ∨ s'.smallBias.val = 4 := by
    simpa [s'] using hs_small
  have ht'_small :
      t'.smallBias.val = 2 ∨ t'.smallBias.val = 3 ∨ t'.smallBias.val = 4 := by
    simpa [t'] using ht_small
  have hs_pre : prePhase4Mass s = (AgentState.smallBiasInt s : ℚ) := by
    simp [prePhase4Mass, hs_phase]
  have ht_pre : prePhase4Mass t = (AgentState.smallBiasInt t : ℚ) := by
    simp [prePhase4Mass, ht_phase]
  have hs'_pre : prePhase4Mass s' = (AgentState.smallBiasInt s : ℚ) := by
    simp [prePhase4Mass, s', hs_phase, AgentState.smallBiasInt]
  have ht'_pre : prePhase4Mass t' = (AgentState.smallBiasInt t : ℚ) := by
    simp [prePhase4Mass, t', ht_phase, AgentState.smallBiasInt]
  have hs_adv :
      prePhase4Mass (advancePhaseWithInit L K s') =
        (AgentState.smallBiasInt s : ℚ) := by
    simpa [s', AgentState.smallBiasInt] using
      prePhase4Mass_advancePhaseWithInit_of_phase_two
        (L := L) (K := K) s' hs'_phase hs'_carrier hs'_mcr hs'_small
  have ht_adv :
      prePhase4Mass (advancePhaseWithInit L K t') =
        (AgentState.smallBiasInt t : ℚ) := by
    simpa [t', AgentState.smallBiasInt] using
      prePhase4Mass_advancePhaseWithInit_of_phase_two
        (L := L) (K := K) t' ht'_phase ht'_carrier ht'_mcr ht'_small
  have hs'_A_pre :
      prePhase4Mass ({ s' with output := .A } : AgentState L K) =
        (AgentState.smallBiasInt s : ℚ) := by
    simpa using hs'_pre
  have ht'_A_pre :
      prePhase4Mass ({ t' with output := .A } : AgentState L K) =
        (AgentState.smallBiasInt t : ℚ) := by
    simpa using ht'_pre
  have hs'_B_pre :
      prePhase4Mass ({ s' with output := .B } : AgentState L K) =
        (AgentState.smallBiasInt s : ℚ) := by
    simpa using hs'_pre
  have ht'_B_pre :
      prePhase4Mass ({ t' with output := .B } : AgentState L K) =
        (AgentState.smallBiasInt t : ℚ) := by
    simpa using ht'_pre
  have hs'_T_pre :
      prePhase4Mass ({ s' with output := .T } : AgentState L K) =
        (AgentState.smallBiasInt s : ℚ) := by
    simpa using hs'_pre
  have ht'_T_pre :
      prePhase4Mass ({ t' with output := .T } : AgentState L K) =
        (AgentState.smallBiasInt t : ℚ) := by
    simpa using ht'_pre
  unfold Phase2Transition
  change
    prePhase4Mass
        (if hasMinusOne univ && hasPlusOne univ then
          (advancePhaseWithInit L K s', advancePhaseWithInit L K t')
        else if hasPlusOne univ then
          ({ s' with output := .A }, { t' with output := .A })
        else if hasMinusOne univ then
          ({ s' with output := .B }, { t' with output := .B })
        else if univ.val = 2 then
          ({ s' with output := .T }, { t' with output := .T })
        else (s', t')).1 +
      prePhase4Mass
        (if hasMinusOne univ && hasPlusOne univ then
          (advancePhaseWithInit L K s', advancePhaseWithInit L K t')
        else if hasPlusOne univ then
          ({ s' with output := .A }, { t' with output := .A })
        else if hasMinusOne univ then
          ({ s' with output := .B }, { t' with output := .B })
        else if univ.val = 2 then
          ({ s' with output := .T }, { t' with output := .T })
        else (s', t')).2 =
      prePhase4Mass s + prePhase4Mass t
  cases hminus : hasMinusOne univ <;> cases hplus : hasPlusOne univ
  · by_cases htie : univ.val = 2
    · simp [hminus, hplus, htie, hs'_T_pre, ht'_T_pre, hs_pre, ht_pre]
    · simp [hminus, hplus, htie, hs'_pre, ht'_pre, hs_pre, ht_pre]
  · simp [hminus, hplus, hs'_A_pre, ht'_A_pre, hs_pre, ht_pre]
  · simp [hminus, hplus, hs'_B_pre, ht'_B_pre, hs_pre, ht_pre]
  · simp [hminus, hplus, hs_adv, ht_adv, hs_pre, ht_pre]

private lemma Phase3Transition_preserves_prePhase4Mass_pair_of_phase_three_chain
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3) :
    prePhase4Mass (Phase3Transition L K s t).1 +
      prePhase4Mass (Phase3Transition L K s t).2 =
    prePhase4Mass s + prePhase4Mass t := by
  have hpair :=
    Phase3Transition_preserves_dyadicBiasSum_pair_of_phase_three
      (L := L) (K := K) s t hs_phase ht_phase
  have hmono := Phase3Transition_phase_nondec (L := L) (K := K) s t
  have hs_not : ¬ s.phase.val < 3 := by omega
  have ht_not : ¬ t.phase.val < 3 := by omega
  have hs_out_not : ¬ (Phase3Transition L K s t).1.phase.val < 3 := by
    omega
  have ht_out_not : ¬ (Phase3Transition L K s t).2.phase.val < 3 := by
    omega
  simpa [prePhase4Mass, hs_not, ht_not, hs_out_not, ht_out_not] using hpair

private lemma Phase4Transition_preserves_prePhase4Mass_pair_of_phase_four_chain
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 4) (ht_phase : t.phase.val = 4) :
    prePhase4Mass (Phase4Transition L K s t).1 +
      prePhase4Mass (Phase4Transition L K s t).2 =
    prePhase4Mass s + prePhase4Mass t := by
  have hpair := Phase4Transition_preserves_dyadicBiasSum_pair
    (L := L) (K := K) s t
  have hmono := Phase4Transition_phase_nondec (L := L) (K := K) s t
  have hs_not : ¬ s.phase.val < 3 := by omega
  have ht_not : ¬ t.phase.val < 3 := by omega
  have hs_out_not : ¬ (Phase4Transition L K s t).1.phase.val < 3 := by
    omega
  have ht_out_not : ¬ (Phase4Transition L K s t).2.phase.val < 3 := by
    omega
  simpa [prePhase4Mass, hs_not, ht_not, hs_out_not, ht_out_not] using hpair

theorem reachable_phase2_neutral_opinions_of_all_neutral
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase_le : ∀ a ∈ c, a.phase.val ≤ 2)
    (hneut : ∀ a ∈ c, a.phase.val = 2 → a.smallBias.val = 3) :
    ∀ a ∈ c, a.phase.val = 2 → a.opinions = phase2OpinionT := by
  classical
  induction hreach with
  | refl =>
      intro a ha hphase
      have hphase0 := (hinit a ha).1
      have hval0 : a.phase.val = 0 := by
        simpa [hphase0]
      omega
  | tail hreach_prev hstep ih =>
      rename_i cprev cnext
      rcases hstep with ⟨s, t, happ, hc'⟩
      dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
      have hs_mem : s ∈ cprev := Multiset.mem_of_le happ (by simp)
      have ht_mem : t ∈ cprev := Multiset.mem_of_le happ (by simp)
      have hout_left_mem : (Transition L K s t).1 ∈ cnext := by
        rw [hc']
        simp
      have hout_right_mem : (Transition L K s t).2 ∈ cnext := by
        rw [hc']
        simp
      have residual_mem {a : AgentState L K} (ha : a ∈ cprev)
          (has : a ≠ s) (hat : a ≠ t) :
          a ∈ cprev - ({s, t} : Multiset (AgentState L K)) := by
        have h1 : a ∈ cprev.erase s := (Multiset.mem_erase_of_ne has).2 ha
        have h2 : a ∈ (cprev.erase s).erase t :=
          (Multiset.mem_erase_of_ne hat).2 h1
        simpa using h2
      have hphase_le_prev : ∀ a ∈ cprev, a.phase.val ≤ 2 := by
        intro a ha
        by_cases has : a = s
        · subst a
          have hmono := (Transition_phase_monotone (L := L) (K := K) s t).1
          change s.phase.val ≤ (Transition L K s t).1.phase.val at hmono
          have hout_le := hphase_le (Transition L K s t).1 hout_left_mem
          omega
        · by_cases hat : a = t
          · subst a
            have hmono := (Transition_phase_monotone (L := L) (K := K) s t).2
            change t.phase.val ≤ (Transition L K s t).2.phase.val at hmono
            have hout_le := hphase_le (Transition L K s t).2 hout_right_mem
            omega
          · have ha_res :
                a ∈ cprev - ({s, t} : Multiset (AgentState L K)) :=
              residual_mem ha has hat
            have ha_next : a ∈ cnext := by
              rw [hc']
              exact Multiset.mem_add.2 (Or.inl ha_res)
            exact hphase_le a ha_next
      have hneut_prev : ∀ a ∈ cprev, a.phase.val = 2 → a.smallBias.val = 3 := by
        intro a ha hphase
        by_cases has : a = s
        · subst a
          have hout_phase : (Transition L K s t).1.phase.val = 2 := by
            have hmono := (Transition_phase_monotone (L := L) (K := K) s t).1
            change s.phase.val ≤ (Transition L K s t).1.phase.val at hmono
            have hout_le := hphase_le (Transition L K s t).1 hout_left_mem
            omega
          have hout_small := hneut (Transition L K s t).1 hout_left_mem hout_phase
          have hsmall_eq :=
            Transition_left_smallBias_eq_of_phase2_to_phase2
              (L := L) (K := K) s t hphase hout_phase
          rw [hsmall_eq] at hout_small
          exact hout_small
        · by_cases hat : a = t
          · subst a
            have hout_phase : (Transition L K s t).2.phase.val = 2 := by
              have hmono := (Transition_phase_monotone (L := L) (K := K) s t).2
              change t.phase.val ≤ (Transition L K s t).2.phase.val at hmono
              have hout_le := hphase_le (Transition L K s t).2 hout_right_mem
              omega
            have hout_small := hneut (Transition L K s t).2 hout_right_mem hout_phase
            have hsmall_eq :=
              Transition_right_smallBias_eq_of_phase2_to_phase2
                (L := L) (K := K) s t hphase hout_phase
            rw [hsmall_eq] at hout_small
            exact hout_small
          · have ha_res :
                a ∈ cprev - ({s, t} : Multiset (AgentState L K)) :=
              residual_mem ha has hat
            have ha_next : a ∈ cnext := by
              rw [hc']
              exact Multiset.mem_add.2 (Or.inl ha_res)
            exact hneut a ha_next hphase
      intro a ha hphase
      rw [hc'] at ha
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
      rcases ha with ha_old | ha_new
      · exact ih hphase_le_prev hneut_prev a
          (Multiset.mem_of_le
            (Multiset.sub_le_self cprev ({s, t} : Multiset (AgentState L K))) ha_old)
          hphase
      · rcases ha_new with h_eq | h_eq
        · subst a
          exact Transition_left_phase2_opinion_T_of_neutral_outputs
            (L := L) (K := K) s t
            (fun hs _ => ih hphase_le_prev hneut_prev s hs_mem hs)
            (fun ht _ => ih hphase_le_prev hneut_prev t ht_mem ht)
            (hphase_le (Transition L K s t).1 hout_left_mem)
            (hphase_le (Transition L K s t).2 hout_right_mem)
            (fun hp => hneut (Transition L K s t).1 hout_left_mem hp)
            (fun hp => hneut (Transition L K s t).2 hout_right_mem hp)
            hphase
        · subst a
          exact Transition_right_phase2_opinion_T_of_neutral_outputs
            (L := L) (K := K) s t
            (fun hs _ => ih hphase_le_prev hneut_prev s hs_mem hs)
            (fun ht _ => ih hphase_le_prev hneut_prev t ht_mem ht)
            (hphase_le (Transition L K s t).1 hout_left_mem)
            (hphase_le (Transition L K s t).2 hout_right_mem)
            (fun hp => hneut (Transition L K s t).1 hout_left_mem hp)
            (fun hp => hneut (Transition L K s t).2 hout_right_mem hp)
            hphase

/-- In any reachable configuration whose agents are all in a phase `≤ 4`, every
Phase-4 agent reports `.T`.  Phase 4 is entered only via `phaseInit ⟨4⟩` (which
sets the output to `.T`) and the Phase-4 transition is the identity on no-big-bias
agents, so the property is preserved by every protocol step. -/
theorem reachable_phase4_output_T
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase_le : ∀ a ∈ c, a.phase.val ≤ 4) :
    ∀ a ∈ c, a.phase.val = 4 → a.output = .T := by
  classical
  induction hreach with
  | refl =>
      intro a ha hphase
      have hphase0 := (hinit a ha).1
      have hval0 : a.phase.val = 0 := by simpa [hphase0]
      omega
  | tail hreach_prev hstep ih =>
      rename_i cprev cnext
      rcases hstep with ⟨s, t, happ, hc'⟩
      dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
      have hs_mem : s ∈ cprev := Multiset.mem_of_le happ (by simp)
      have ht_mem : t ∈ cprev := Multiset.mem_of_le happ (by simp)
      have hout_left_mem : (Transition L K s t).1 ∈ cnext := by rw [hc']; simp
      have hout_right_mem : (Transition L K s t).2 ∈ cnext := by rw [hc']; simp
      have residual_mem {a : AgentState L K} (ha : a ∈ cprev)
          (has : a ≠ s) (hat : a ≠ t) :
          a ∈ cprev - ({s, t} : Multiset (AgentState L K)) := by
        have h1 : a ∈ cprev.erase s := (Multiset.mem_erase_of_ne has).2 ha
        have h2 : a ∈ (cprev.erase s).erase t :=
          (Multiset.mem_erase_of_ne hat).2 h1
        simpa using h2
      -- Source phases are also `≤ 4` (the transition is phase-monotone and the
      -- output phases are `≤ 4`).
      have hphase_le_prev : ∀ a ∈ cprev, a.phase.val ≤ 4 := by
        intro a ha
        by_cases has : a = s
        · subst a
          have hmono := (Transition_phase_monotone (L := L) (K := K) s t).1
          change s.phase.val ≤ (Transition L K s t).1.phase.val at hmono
          have hout_le := hphase_le (Transition L K s t).1 hout_left_mem
          omega
        · by_cases hat : a = t
          · subst a
            have hmono := (Transition_phase_monotone (L := L) (K := K) s t).2
            change t.phase.val ≤ (Transition L K s t).2.phase.val at hmono
            have hout_le := hphase_le (Transition L K s t).2 hout_right_mem
            omega
          · have ha_res :
                a ∈ cprev - ({s, t} : Multiset (AgentState L K)) :=
              residual_mem ha has hat
            have ha_next : a ∈ cnext := by
              rw [hc']; exact Multiset.mem_add.2 (Or.inl ha_res)
            exact hphase_le a ha_next
      -- Reach-back of the output-T property to the source agents.
      have hs_prev : s.phase.val = 4 → s.output = .T :=
        fun hp => ih hphase_le_prev s hs_mem hp
      have ht_prev : t.phase.val = 4 → t.output = .T :=
        fun hp => ih hphase_le_prev t ht_mem hp
      intro a ha hphase
      rw [hc'] at ha
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
      rcases ha with ha_old | ha_new
      · exact ih hphase_le_prev a
          (Multiset.mem_of_le
            (Multiset.sub_le_self cprev ({s, t} : Multiset (AgentState L K))) ha_old)
          hphase
      · rcases ha_new with h_eq | h_eq
        · subst a
          exact Transition_left_phase4_output_T_of_phase_four
            (L := L) (K := K) s t hs_prev ht_prev hphase
        · subst a
          exact Transition_right_phase4_output_T_of_phase_four
            (L := L) (K := K) s t hs_prev ht_prev hphase

private theorem Transition_phase9_to_phase9_preserves_signSupport
    (s t : AgentState L K) (hs : s.phase.val = 9)
    (hss : phase2SignSupport s)
    (hphase : (Transition L K s t).1.phase.val = 9) :
    phase2SignSupport (Transition L K s t).1 := by
  have ht_le : t.phase.val ≤ 9 := by
    have hmax := Transition_left_phase_ge_pair_max (L := L) (K := K) s t
    rw [hphase] at hmax
    omega
  have hs_epi :=
    phaseEpidemicUpdate_left_phase9_support_of_right_le_nine (L := L) (K := K)
      s t hs ht_le hss
  unfold Transition
  generalize he : phaseEpidemicUpdate L K s t = e
  rcases e with ⟨s', t'⟩
  have hs'_support : phase2SignSupport s' := by
    simpa [he] using hs_epi.1
  have hs'_phase : s'.phase.val = 9 ∨ s'.phase.val = 10 := by
    simpa [he] using hs_epi.2
  change phase2SignSupport
    (finishPhase10Entry L K s'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).1)
  generalize hp : s'.phase = p
  fin_cases p
  · have : s'.phase.val = 0 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have : s'.phase.val = 1 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have : s'.phase.val = 2 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have : s'.phase.val = 3 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have : s'.phase.val = 4 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have : s'.phase.val = 5 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have : s'.phase.val = 6 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have : s'.phase.val = 7 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have : s'.phase.val = 8 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
      s' (Phase9Transition L K s' t').1
      (Phase9Transition_preserves_phase2SignSupport_left (L := L) (K := K)
        s' t' hs'_support)
  · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
      s' (Phase10Transition L K s' t').1
      (Phase10Transition_preserves_phase2SignSupport_left (L := L) (K := K)
        s' t' hs'_support)

private theorem Transition_second_phase9_to_phase9_preserves_signSupport
    (s t : AgentState L K) (ht : t.phase.val = 9)
    (htt : phase2SignSupport t)
    (hphase : (Transition L K s t).2.phase.val = 9) :
    phase2SignSupport (Transition L K s t).2 := by
  have hs_le : s.phase.val ≤ 9 := by
    have hmax := Transition_right_phase_ge_pair_max (L := L) (K := K) s t
    rw [hphase] at hmax
    omega
  have ht_epi :=
    phaseEpidemicUpdate_right_phase9_support_of_left_le_nine (L := L) (K := K)
      s t ht hs_le htt
  have hs_epi_phase_le :=
    phaseEpidemicUpdate_left_phase_le_nine_or_ten_of_phases_le_nine
      (L := L) (K := K) s t hs_le (by omega)
  have hs_epi_ge := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
  unfold Transition
  generalize he : phaseEpidemicUpdate L K s t = e
  rcases e with ⟨s', t'⟩
  have ht'_support : phase2SignSupport t' := by
    simpa [he] using ht_epi.1
  have ht'_phase : t'.phase.val = 9 ∨ t'.phase.val = 10 := by
    simpa [he] using ht_epi.2
  have hs'_phase : s'.phase.val = 9 ∨ s'.phase.val = 10 := by
    have hge : max s.phase.val t.phase.val ≤ s'.phase.val := by
      simpa [he] using hs_epi_ge
    have hle_or : s'.phase.val ≤ 9 ∨ s'.phase.val = 10 := by
      simpa [he] using hs_epi_phase_le
    rcases hle_or with hle | hten
    · left
      omega
    · right
      exact hten
  change phase2SignSupport
    (finishPhase10Entry L K t'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).2)
  generalize hp : s'.phase = p
  fin_cases p
  · have hpval : s'.phase.val = 0 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 1 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 2 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 3 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 4 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 5 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 6 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 7 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hs8 : s'.phase.val = 8 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
      t' (Phase9Transition L K s' t').2
      (Phase9Transition_preserves_phase2SignSupport_right (L := L) (K := K)
        s' t' ht'_support)
  · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
      t' (Phase10Transition L K s' t').2
      (Phase10Transition_preserves_phase2SignSupport_right (L := L) (K := K)
        s' t' ht'_support)

private theorem Transition_left_phase9SignSupport_of_input_support
    (s t : AgentState L K)
    (hsupport : s.phase.val = 9 → phase2SignSupport s)
    (htsupport : t.phase.val = 9 → phase2SignSupport t)
    (hphase : (Transition L K s t).1.phase.val = 9) :
    phase2SignSupport (Transition L K s t).1 := by
  have hphase_orig := hphase
  by_cases hs_lt : s.phase.val < 9
  · unfold Transition at hphase ⊢
    generalize he : phaseEpidemicUpdate L K s t = e
    rcases e with ⟨s', t'⟩
    rw [he] at hphase
    have ht_le : t.phase.val ≤ 9 := by
      have hmax := Transition_left_phase_ge_pair_max (L := L) (K := K) s t
      rw [hphase_orig] at hmax
      omega
    have hs'_not_high : s'.phase.val ≤ 9 ∨ s'.phase.val = 10 := by
      simpa [he] using
        phaseEpidemicUpdate_left_phase_le_nine_or_ten_of_phases_le_nine
          (L := L) (K := K) s t (by omega) ht_le
    have hs'_entered :
        s'.phase.val = 9 → phase2SignSupport s' := by
      intro hs'_phase
      simpa [he] using
        phaseEpidemicUpdate_left_phase9SignSupport_of_entered
          (L := L) (K := K) s t hs_lt (by simpa [he] using hs'_phase)
    change phase2SignSupport
      (finishPhase10Entry L K s'
        (match s'.phase with
        | ⟨0, _⟩ => Phase0Transition L K s' t'
        | ⟨1, _⟩ => Phase1Transition L K s' t'
        | ⟨2, _⟩ => Phase2Transition L K s' t'
        | ⟨3, _⟩ => Phase3Transition L K s' t'
        | ⟨4, _⟩ => Phase4Transition L K s' t'
        | ⟨5, _⟩ => Phase5Transition L K s' t'
        | ⟨6, _⟩ => Phase6Transition L K s' t'
        | ⟨7, _⟩ => Phase7Transition L K s' t'
        | ⟨8, _⟩ => Phase8Transition L K s' t'
        | ⟨9, _⟩ => Phase9Transition L K s' t'
        | ⟨10, _⟩ => Phase10Transition L K s' t'
        | _ => (s', t')).1)
    generalize hp : s'.phase = p
    fin_cases p
    · have hpval : s'.phase.val = 0 := by simpa [hp]
      have hlocal : (Phase0Transition L K s' t').1.phase.val = 9 := by
        simpa [hp] using hphase
      exact False.elim
        (Phase0Transition_left_phase_ne_nine_of_phase_le_seven
          (L := L) (K := K) s' t' (by omega) hlocal)
    · have hpval : s'.phase.val = 1 := by simpa [hp]
      have hlocal : (Phase1Transition L K s' t').1.phase.val = 9 := by
        simpa [hp] using hphase
      exact False.elim
        (Phase1Transition_left_phase_ne_nine_of_phase_le_seven
          (L := L) (K := K) s' t' (by omega) hlocal)
    · have hpval : s'.phase.val = 2 := by simpa [hp]
      have hlocal : (Phase2Transition L K s' t').1.phase.val = 9 := by
        simpa [hp] using hphase
      exact False.elim
        (Phase2Transition_left_phase_ne_nine_of_phase_le_seven
          (L := L) (K := K) s' t' (by omega) hlocal)
    · have hpval : s'.phase.val = 3 := by simpa [hp]
      have hlocal : (Phase3Transition L K s' t').1.phase.val = 9 := by
        simpa [hp] using hphase
      exact False.elim
        (Phase3Transition_left_phase_ne_nine_of_phase_le_seven
          (L := L) (K := K) s' t' (by omega) hlocal)
    · have hpval : s'.phase.val = 4 := by simpa [hp]
      have hlocal : (Phase4Transition L K s' t').1.phase.val = 9 := by
        simpa [hp] using hphase
      exact False.elim
        (Phase4Transition_left_phase_ne_nine_of_phase_le_seven
          (L := L) (K := K) s' t' (by omega) hlocal)
    · have hpval : s'.phase.val = 5 := by simpa [hp]
      have hlocal : (Phase5Transition L K s' t').1.phase.val = 9 := by
        simpa [hp] using hphase
      exact False.elim
        (Phase5Transition_left_phase_ne_nine_of_phase_le_seven
          (L := L) (K := K) s' t' (by omega) hlocal)
    · have hpval : s'.phase.val = 6 := by simpa [hp]
      have hlocal : (Phase6Transition L K s' t').1.phase.val = 9 := by
        simpa [hp] using hphase
      exact False.elim
        (Phase6Transition_left_phase_ne_nine_of_phase_le_seven
          (L := L) (K := K) s' t' (by omega) hlocal)
    · have hpval : s'.phase.val = 7 := by simpa [hp]
      have hlocal : (Phase7Transition L K s' t').1.phase.val = 9 := by
        simpa [hp] using hphase
      exact False.elim
        (Phase7Transition_left_phase_ne_nine_of_phase_le_seven
          (L := L) (K := K) s' t' (by omega) hlocal)
    · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
        s' (Phase8Transition L K s' t').1
        (Phase8Transition_left_phase9SignSupport (L := L) (K := K)
          s' t' (by simpa [hp]) (by simpa [hp] using hphase))
    · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
        s' (Phase9Transition L K s' t').1
        (Phase9Transition_preserves_phase2SignSupport_left (L := L) (K := K)
          s' t' (hs'_entered (by simpa [hp])))
    · have hpval : s'.phase.val = 10 := by simpa [hp]
      have hmono := (Phase10Transition_phase_nondec (L := L) (K := K) s' t').1
      have hout : (Phase10Transition L K s' t').1.phase.val = 9 := by
        simpa [hp] using hphase
      omega
  · have hs_eq : s.phase.val = 9 := by
      have hmono := (Transition_phase_monotone (L := L) (K := K) s t).1
      change s.phase.val ≤ (Transition L K s t).1.phase.val at hmono
      rw [hphase_orig] at hmono
      omega
    exact Transition_phase9_to_phase9_preserves_signSupport (L := L) (K := K)
      s t hs_eq (hsupport hs_eq) hphase

private theorem Transition_right_phase9SignSupport_of_input_support
    (s t : AgentState L K)
    (hsupport : s.phase.val = 9 → phase2SignSupport s)
    (htsupport : t.phase.val = 9 → phase2SignSupport t)
    (hphase : (Transition L K s t).2.phase.val = 9) :
    phase2SignSupport (Transition L K s t).2 := by
  have hphase_orig := hphase
  by_cases ht_lt : t.phase.val < 9
  · unfold Transition at hphase ⊢
    generalize he : phaseEpidemicUpdate L K s t = e
    rcases e with ⟨s', t'⟩
    rw [he] at hphase
    have hs_le : s.phase.val ≤ 9 := by
      have hmax := Transition_right_phase_ge_pair_max (L := L) (K := K) s t
      rw [hphase_orig] at hmax
      omega
    have ht'_not_high : t'.phase.val ≤ 9 ∨ t'.phase.val = 10 := by
      simpa [he] using
        phaseEpidemicUpdate_right_phase_le_nine_or_ten_of_phases_le_nine
          (L := L) (K := K) s t hs_le (by omega)
    have hs'_not_high : s'.phase.val ≤ 9 ∨ s'.phase.val = 10 := by
      simpa [he] using
        phaseEpidemicUpdate_left_phase_le_nine_or_ten_of_phases_le_nine
          (L := L) (K := K) s t hs_le (by omega)
    have ht'_entered :
        t'.phase.val = 9 → phase2SignSupport t' := by
      intro ht'_phase
      simpa [he] using
        phaseEpidemicUpdate_right_phase9SignSupport_of_entered
          (L := L) (K := K) s t ht_lt (by simpa [he] using ht'_phase)
    change phase2SignSupport
      (finishPhase10Entry L K t'
        (match s'.phase with
        | ⟨0, _⟩ => Phase0Transition L K s' t'
        | ⟨1, _⟩ => Phase1Transition L K s' t'
        | ⟨2, _⟩ => Phase2Transition L K s' t'
        | ⟨3, _⟩ => Phase3Transition L K s' t'
        | ⟨4, _⟩ => Phase4Transition L K s' t'
        | ⟨5, _⟩ => Phase5Transition L K s' t'
        | ⟨6, _⟩ => Phase6Transition L K s' t'
        | ⟨7, _⟩ => Phase7Transition L K s' t'
        | ⟨8, _⟩ => Phase8Transition L K s' t'
        | ⟨9, _⟩ => Phase9Transition L K s' t'
        | ⟨10, _⟩ => Phase10Transition L K s' t'
        | _ => (s', t')).2)
    generalize hp : s'.phase = p
    fin_cases p
    · have hs0 : s'.phase.val = 0 := by simpa [hp]
      have hlocal : (Phase0Transition L K s' t').2.phase.val = 9 := by
        simpa [hp] using hphase
      have ht'_not_ten : t'.phase.val ≠ 10 := by
        intro ht_ten
        have hmono := (Phase0Transition_phase_nondec (L := L) (K := K) s' t').2
        change t'.phase.val ≤ (Phase0Transition L K s' t').2.phase.val at hmono
        omega
      have hs'_not_ten : s'.phase.val ≠ 10 := by omega
      have hsync :=
        phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
          (L := L) (K := K) s t hs_le (by omega)
          (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
      have ht0 : t'.phase.val = 0 := by
        have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
        omega
      exact False.elim
        (Phase0Transition_right_phase_ne_nine_of_phase_le_seven
          (L := L) (K := K) s' t' (by omega) hlocal)
    · have hs1 : s'.phase.val = 1 := by simpa [hp]
      have hlocal : (Phase1Transition L K s' t').2.phase.val = 9 := by
        simpa [hp] using hphase
      have ht'_not_ten : t'.phase.val ≠ 10 := by
        intro ht_ten
        have hmono := (Phase1Transition_phase_nondec (L := L) (K := K) s' t').2
        change t'.phase.val ≤ (Phase1Transition L K s' t').2.phase.val at hmono
        omega
      have hs'_not_ten : s'.phase.val ≠ 10 := by omega
      have hsync :=
        phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
          (L := L) (K := K) s t hs_le (by omega)
          (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
      have ht1 : t'.phase.val = 1 := by
        have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
        omega
      exact False.elim
        (Phase1Transition_right_phase_ne_nine_of_phase_le_seven
          (L := L) (K := K) s' t' (by omega) hlocal)
    · have hs2 : s'.phase.val = 2 := by simpa [hp]
      have hlocal : (Phase2Transition L K s' t').2.phase.val = 9 := by
        simpa [hp] using hphase
      have ht'_not_ten : t'.phase.val ≠ 10 := by
        intro ht_ten
        have hmono := (Phase2Transition_phase_nondec (L := L) (K := K) s' t').2
        change t'.phase.val ≤ (Phase2Transition L K s' t').2.phase.val at hmono
        omega
      have hs'_not_ten : s'.phase.val ≠ 10 := by omega
      have hsync :=
        phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
          (L := L) (K := K) s t hs_le (by omega)
          (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
      have ht2 : t'.phase.val = 2 := by
        have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
        omega
      exact False.elim
        (Phase2Transition_right_phase_ne_nine_of_phase_le_seven
          (L := L) (K := K) s' t' (by omega) hlocal)
    · have hs3 : s'.phase.val = 3 := by simpa [hp]
      have hlocal : (Phase3Transition L K s' t').2.phase.val = 9 := by
        simpa [hp] using hphase
      have ht'_not_ten : t'.phase.val ≠ 10 := by
        intro ht_ten
        have hmono := (Phase3Transition_phase_nondec (L := L) (K := K) s' t').2
        change t'.phase.val ≤ (Phase3Transition L K s' t').2.phase.val at hmono
        omega
      have hs'_not_ten : s'.phase.val ≠ 10 := by omega
      have hsync :=
        phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
          (L := L) (K := K) s t hs_le (by omega)
          (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
      have ht3 : t'.phase.val = 3 := by
        have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
        omega
      exact False.elim
        (Phase3Transition_right_phase_ne_nine_of_phase_le_seven
          (L := L) (K := K) s' t' (by omega) hlocal)
    · have hs4 : s'.phase.val = 4 := by simpa [hp]
      have hlocal : (Phase4Transition L K s' t').2.phase.val = 9 := by
        simpa [hp] using hphase
      have ht'_not_ten : t'.phase.val ≠ 10 := by
        intro ht_ten
        have hmono := (Phase4Transition_phase_nondec (L := L) (K := K) s' t').2
        change t'.phase.val ≤ (Phase4Transition L K s' t').2.phase.val at hmono
        omega
      have hs'_not_ten : s'.phase.val ≠ 10 := by omega
      have hsync :=
        phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
          (L := L) (K := K) s t hs_le (by omega)
          (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
      have ht4 : t'.phase.val = 4 := by
        have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
        omega
      exact False.elim
        (Phase4Transition_right_phase_ne_nine_of_phase_le_seven
          (L := L) (K := K) s' t' (by omega) hlocal)
    · have hs5 : s'.phase.val = 5 := by simpa [hp]
      have hlocal : (Phase5Transition L K s' t').2.phase.val = 9 := by
        simpa [hp] using hphase
      have ht'_not_ten : t'.phase.val ≠ 10 := by
        intro ht_ten
        have hmono := (Phase5Transition_phase_nondec (L := L) (K := K) s' t').2
        change t'.phase.val ≤ (Phase5Transition L K s' t').2.phase.val at hmono
        omega
      have hs'_not_ten : s'.phase.val ≠ 10 := by omega
      have hsync :=
        phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
          (L := L) (K := K) s t hs_le (by omega)
          (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
      have ht5 : t'.phase.val = 5 := by
        have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
        omega
      exact False.elim
        (Phase5Transition_right_phase_ne_nine_of_phase_le_seven
          (L := L) (K := K) s' t' (by omega) hlocal)
    · have hs6 : s'.phase.val = 6 := by simpa [hp]
      have hlocal : (Phase6Transition L K s' t').2.phase.val = 9 := by
        simpa [hp] using hphase
      have ht'_not_ten : t'.phase.val ≠ 10 := by
        intro ht_ten
        have hmono := (Phase6Transition_phase_nondec (L := L) (K := K) s' t').2
        change t'.phase.val ≤ (Phase6Transition L K s' t').2.phase.val at hmono
        omega
      have hs'_not_ten : s'.phase.val ≠ 10 := by omega
      have hsync :=
        phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
          (L := L) (K := K) s t hs_le (by omega)
          (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
      have ht6 : t'.phase.val = 6 := by
        have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
        omega
      exact False.elim
        (Phase6Transition_right_phase_ne_nine_of_phase_le_seven
          (L := L) (K := K) s' t' (by omega) hlocal)
    · have hs7 : s'.phase.val = 7 := by simpa [hp]
      have hlocal : (Phase7Transition L K s' t').2.phase.val = 9 := by
        simpa [hp] using hphase
      have ht'_not_ten : t'.phase.val ≠ 10 := by
        intro ht_ten
        have hmono := (Phase7Transition_phase_nondec (L := L) (K := K) s' t').2
        change t'.phase.val ≤ (Phase7Transition L K s' t').2.phase.val at hmono
        omega
      have hs'_not_ten : s'.phase.val ≠ 10 := by omega
      have hsync :=
        phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
          (L := L) (K := K) s t hs_le (by omega)
          (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
      have ht7 : t'.phase.val = 7 := by
        have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
        omega
      exact False.elim
        (Phase7Transition_right_phase_ne_nine_of_phase_le_seven
          (L := L) (K := K) s' t' (by omega) hlocal)
    · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
        t' (Phase8Transition L K s' t').2
        (Phase8Transition_right_phase9SignSupport (L := L) (K := K)
          s' t' (by
            have hs8 : s'.phase.val = 8 := by simpa [hp]
            have ht'_not_ten : t'.phase.val ≠ 10 := by
              intro ht_ten
              have hmono := (Phase8Transition_phase_nondec (L := L) (K := K) s' t').2
              change t'.phase.val ≤ (Phase8Transition L K s' t').2.phase.val at hmono
              have hlocal : (Phase8Transition L K s' t').2.phase.val = 9 := by
                simpa [hp] using hphase
              omega
            have hs'_not_ten : s'.phase.val ≠ 10 := by omega
            have hsync :=
              phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
                (L := L) (K := K) s t hs_le (by omega)
                (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
            have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
            omega)
          (by simpa [hp] using hphase))
    · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
        t' (Phase9Transition L K s' t').2
        (Phase9Transition_preserves_phase2SignSupport_right (L := L) (K := K)
          s' t' (ht'_entered (by
            have hs9 : s'.phase.val = 9 := by simpa [hp]
            have ht'_not_ten : t'.phase.val ≠ 10 := by
              intro ht_ten
              have hmono := (Phase9Transition_phase_nondec (L := L) (K := K) s' t').2
              change t'.phase.val ≤ (Phase9Transition L K s' t').2.phase.val at hmono
              have hlocal : (Phase9Transition L K s' t').2.phase.val = 9 := by
                simpa [hp] using hphase
              omega
            have hs'_not_ten : s'.phase.val ≠ 10 := by omega
            have hsync :=
              phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
                (L := L) (K := K) s t hs_le (by omega)
                (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
            have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
            omega)))
    · have hpval : s'.phase.val = 10 := by simpa [hp]
      rcases hs'_not_high with hle | hten
      · omega
      · exact finishPhase10Entry_preserves_phase2SignSupport (L := L) (K := K)
          t' (Phase10Transition L K s' t').2
          (Phase10Transition_preserves_phase2SignSupport_right (L := L) (K := K)
            s' t' (ht'_entered (by
              have hout : (Phase10Transition L K s' t').2.phase.val = 9 := by
                simpa [hp] using hphase
              have hphase_eq := (Phase10Transition_phase_eq (L := L) (K := K) s' t').2
              have hval : (Phase10Transition L K s' t').2.phase.val = t'.phase.val := by
                rw [hphase_eq]
              omega)))
  · have ht_eq : t.phase.val = 9 := by
      have hmono := (Transition_phase_monotone (L := L) (K := K) s t).2
      change t.phase.val ≤ (Transition L K s t).2.phase.val at hmono
      rw [hphase_orig] at hmono
      omega
    exact Transition_second_phase9_to_phase9_preserves_signSupport
      (L := L) (K := K) s t ht_eq (htsupport ht_eq) hphase

private theorem StepRel_phase9SignSupport
    {c c' : Config (AgentState L K)}
    (hc : ∀ a ∈ c, a.phase.val = 9 → phase2SignSupport a)
    (hstep : (NonuniformMajority L K).StepRel c c') :
    ∀ a ∈ c', a.phase.val = 9 → phase2SignSupport a := by
  rcases hstep with ⟨s, t, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
  have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
  rw [hc']
  intro a ha hphase
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with h_old | h_new
  · exact hc a (Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) h_old) hphase
  · rcases h_new with h_eq | h_eq
    · subst a
      exact Transition_left_phase9SignSupport_of_input_support (L := L) (K := K) s t
        (fun hs => hc s hs_mem hs) (fun ht => hc t ht_mem ht) hphase
    · subst a
      exact Transition_right_phase9SignSupport_of_input_support (L := L) (K := K) s t
        (fun hs => hc s hs_mem hs) (fun ht => hc t ht_mem ht) hphase

theorem reachable_phase9SignSupport
    (init c : Config (AgentState L K))
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c) :
    ∀ a ∈ c, a.phase.val = 9 → phase2SignSupport a := by
  induction hreach with
  | refl =>
      intro a ha hphase
      have hphase0 := (hvalid a ha).1
      have hval0 : a.phase.val = 0 := by
        simpa [hphase0]
      omega
  | tail _ hstep ih =>
      exact StepRel_phase9SignSupport (L := L) (K := K) ih hstep

theorem phaseInit_nine_hasPlusOne_of_smallBias_pos_one
    (a : AgentState L K) (hsmall : a.smallBias.val = 4) :
    hasPlusOne (phaseInit L K ⟨9, by decide⟩ a).opinions = true := by
  unfold phaseInit
  simp [hsmall, hasPlusOne]

theorem phaseInit_nine_hasMinusOne_of_smallBias_neg_one
    (a : AgentState L K) (hsmall : a.smallBias.val = 2) :
    hasMinusOne (phaseInit L K ⟨9, by decide⟩ a).opinions = true := by
  unfold phaseInit
  simp [hsmall, hasMinusOne]

theorem phaseInit_nine_opinion_eq_zero_of_smallBias_zero
    (a : AgentState L K) (hsmall : a.smallBias.val = 3) :
    (phaseInit L K ⟨9, by decide⟩ a).opinions = phase2OpinionT := by
  unfold phaseInit phase2OpinionT
  simp [hsmall]

private theorem Phase9Transition_neutral_left
    (a b : AgentState L K)
    (ha : phase2NeutralSupport a) (hb : phase2NeutralSupport b)
    (hsmall_a : (Phase9Transition L K a b).1.smallBias.val = 3)
    (hsmall_b : (Phase9Transition L K a b).2.smallBias.val = 3) :
    (Phase9Transition L K a b).1.opinions = phase2OpinionT := by
  simpa [Phase9Transition] using
    Phase2Transition_neutral_left (L := L) (K := K) a b ha hb
      hsmall_a hsmall_b

private theorem Phase9Transition_neutral_right
    (a b : AgentState L K)
    (ha : phase2NeutralSupport a) (hb : phase2NeutralSupport b)
    (hsmall_a : (Phase9Transition L K a b).1.smallBias.val = 3)
    (hsmall_b : (Phase9Transition L K a b).2.smallBias.val = 3) :
    (Phase9Transition L K a b).2.opinions = phase2OpinionT := by
  simpa [Phase9Transition] using
    Phase2Transition_neutral_right (L := L) (K := K) a b ha hb
      hsmall_a hsmall_b

private theorem Phase10Transition_preserves_opinion_T_left
    (a b : AgentState L K) (h : a.opinions = phase2OpinionT) :
    (Phase10Transition L K a b).1.opinions = phase2OpinionT := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  simp [Phase10Transition] at h ⊢
  split_ifs <;> simp_all

private theorem Phase10Transition_preserves_opinion_T_right
    (a b : AgentState L K) (h : b.opinions = phase2OpinionT) :
    (Phase10Transition L K a b).2.opinions = phase2OpinionT := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  simp [Phase10Transition] at h ⊢
  split_ifs <;> simp_all

private theorem stdCounterSubroutine_phase9_opinion_T_of_phase_eight_smallBias_three
    (a : AgentState L K) (hphase_eight : a.phase.val = 8)
    (hphase_nine : (stdCounterSubroutine L K a).phase.val = 9)
    (hsmall : (stdCounterSubroutine L K a).smallBias.val = 3) :
    (stdCounterSubroutine L K a).opinions = phase2OpinionT := by
  by_cases hcounter : a.counter.val = 0
  · have hpres := phaseInit_preserves_smallBias (L := L) (K := K)
      ⟨9, by decide⟩ ({ a with phase := ⟨9, by decide⟩ })
    have hsmall_pre :
        ({ a with phase := ⟨9, by decide⟩ } : AgentState L K).smallBias.val = 3 := by
      have hsmall_init :
          (phaseInit L K ⟨9, by decide⟩
            ({ a with phase := ⟨9, by decide⟩ } : AgentState L K)).smallBias.val = 3 := by
        simpa [stdCounterSubroutine, hcounter, advancePhaseWithInit,
          advancePhase, hphase_eight] using hsmall
      rw [hpres] at hsmall_init
      exact hsmall_init
    have hop := phaseInit_nine_opinion_eq_zero_of_smallBias_zero
      (L := L) (K := K) ({ a with phase := ⟨9, by decide⟩ }) hsmall_pre
    simpa [stdCounterSubroutine, hcounter, advancePhaseWithInit,
      advancePhase, hphase_eight] using hop
  · simp [stdCounterSubroutine, hcounter] at hphase_nine
    omega

private theorem clockCounterStep_phase9_opinion_T_of_phase_eight_smallBias_three
    (a : AgentState L K) (hphase_eight : a.phase.val = 8)
    (hphase_nine : (clockCounterStep L K a).phase.val = 9)
    (hsmall : (clockCounterStep L K a).smallBias.val = 3) :
    (clockCounterStep L K a).opinions = phase2OpinionT := by
  by_cases hclock : a.role = .clock
  · have hphase_std : (stdCounterSubroutine L K a).phase.val = 9 := by
      simpa [clockCounterStep, hclock] using hphase_nine
    have hsmall_std : (stdCounterSubroutine L K a).smallBias.val = 3 := by
      simpa [clockCounterStep, hclock] using hsmall
    have hop := stdCounterSubroutine_phase9_opinion_T_of_phase_eight_smallBias_three
      (L := L) (K := K) a hphase_eight hphase_std hsmall_std
    simpa [clockCounterStep, hclock] using hop
  · simp [clockCounterStep, hclock] at hphase_nine
    omega

private theorem Phase8Transition_left_phase9_opinion_T_of_smallBias_three
    (s t : AgentState L K) (hs_phase : s.phase.val = 8)
    (hphase : (Phase8Transition L K s t).1.phase.val = 9)
    (hsmall : (Phase8Transition L K s t).1.smallBias.val = 3) :
    (Phase8Transition L K s t).1.opinions = phase2OpinionT := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · rcases hmain with ⟨hs_main, ht_main⟩
    have hrt := absorbConsume_left_role_phase_of_main (L := L) (K := K)
      s t hs_main
    have hnot_clock : (absorbConsume L K s t).1.role ≠ .clock := by
      simp [hs_main]
    have hphase_abs : (absorbConsume L K s t).1.phase.val = 9 := by
      simpa [Phase8Transition, hs_main, ht_main, hnot_clock] using hphase
    rw [hrt.2] at hphase_abs
    omega
  · simp [Phase8Transition, hmain] at hphase hsmall ⊢
    exact clockCounterStep_phase9_opinion_T_of_phase_eight_smallBias_three
      (L := L) (K := K) s hs_phase hphase hsmall

private theorem Phase8Transition_right_phase9_opinion_T_of_smallBias_three
    (s t : AgentState L K) (ht_phase : t.phase.val = 8)
    (hphase : (Phase8Transition L K s t).2.phase.val = 9)
    (hsmall : (Phase8Transition L K s t).2.smallBias.val = 3) :
    (Phase8Transition L K s t).2.opinions = phase2OpinionT := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · rcases hmain with ⟨hs_main, ht_main⟩
    have hrt := absorbConsume_right_role_phase_of_main (L := L) (K := K)
      s t ht_main
    have hnot_clock : (absorbConsume L K s t).2.role ≠ .clock := by
      simp [ht_main]
    have hphase_abs : (absorbConsume L K s t).2.phase.val = 9 := by
      simpa [Phase8Transition, hs_main, ht_main, hnot_clock] using hphase
    rw [hrt.2] at hphase_abs
    omega
  · simp [Phase8Transition, hmain] at hphase hsmall ⊢
    exact clockCounterStep_phase9_opinion_T_of_phase_eight_smallBias_three
      (L := L) (K := K) t ht_phase hphase hsmall

private theorem phase2OpinionT_runInitsBetween_to_nine_of_lt
    (oldP : ℕ) (a : AgentState L K) (hold : oldP < 9)
    (hphase :
      (runInitsBetween L K oldP 9 ({ a with phase := ⟨9, by decide⟩ })).phase.val = 9)
    (hsmall :
      (runInitsBetween L K oldP 9 ({ a with phase := ⟨9, by decide⟩ })).smallBias.val = 3) :
    (runInitsBetween L K oldP 9 ({ a with phase := ⟨9, by decide⟩ })).opinions =
      phase2OpinionT := by
  rw [runInitsBetween_to_nine_eq_phaseInit_nine (L := L) (K := K)
    oldP ({ a with phase := ⟨9, by decide⟩ }) hold] at hphase hsmall ⊢
  have hpres := phaseInit_preserves_smallBias (L := L) (K := K)
    ⟨9, by decide⟩
    (runInitsBetween L K oldP 8 ({ a with phase := ⟨9, by decide⟩ }))
  have hsmall_final :
      (phaseInit L K ⟨9, by decide⟩
        (runInitsBetween L K oldP 8
          ({ a with phase := ⟨9, by decide⟩ }))).smallBias.val = 3 := by
    simpa using hsmall
  have hsmall_pre :
      (runInitsBetween L K oldP 8
        ({ a with phase := ⟨9, by decide⟩ })).smallBias.val = 3 := by
    rw [hpres] at hsmall_final
    exact hsmall_final
  exact phaseInit_nine_opinion_eq_zero_of_smallBias_zero (L := L) (K := K)
    (runInitsBetween L K oldP 8 ({ a with phase := ⟨9, by decide⟩ }))
    hsmall_pre

private theorem phaseEpidemicUpdate_left_phase9NeutralSupport_of_entered
    (s t : AgentState L K)
    (hs : s.phase.val < 9)
    (hout : (phaseEpidemicUpdate L K s t).1.phase.val = 9)
    (hneut : s.smallBias.val = 3) :
    (phaseEpidemicUpdate L K s t).1.opinions = phase2OpinionT := by
  unfold phaseEpidemicUpdate at hout ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hnot10 :
      ¬ ((s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)) := by
    intro h10
    have hs_before : s.phase.val < 10 := by omega
    have hten : (phase10EpidemicEntry L K s s0).phase.val = 10 := by
      simp [phase10EpidemicEntry, hs_before]
    have hphase10 :
        (phase10EpidemicEntry L K s s0).phase.val = 9 := by
      simpa [h10, s0, t0] using hout
    omega
  have hs0_phase : s0.phase.val = 9 := by
    simpa [hnot10, s0, t0] using hout
  have hshape :
      s0.phase.val = p.val ∨ s0.phase.val = 10 := by
    simpa [s0] using
      runInitsBetween_phase_eq_start_or_ten (L := L) (K := K)
        s.phase.val p.val p.val ({ s with phase := p }) (Or.inl (by simp))
  have hp9 : p.val = 9 := by
    rcases hshape with hp | hten
    · omega
    · omega
  have hp_eq : p = ⟨9, by decide⟩ := Fin.ext hp9
  have hs0_small : s0.smallBias.val = 3 := by
    have hpres := runInitsBetween_preserves_smallBias
      (L := L) (K := K) s.phase.val p.val ({ s with phase := p })
    simpa [s0, hpres] using hneut
  have hs0_op : s0.opinions = phase2OpinionT := by
    have hs0_rw :
        s0 =
          runInitsBetween L K s.phase.val 9
            ({ s with phase := ⟨9, by decide⟩ }) := by
      simp [s0, hp_eq]
    have hphase_run := hs0_phase
    have hsmall_run := hs0_small
    rw [hs0_rw] at hphase_run hsmall_run
    rw [hs0_rw]
    exact phase2OpinionT_runInitsBetween_to_nine_of_lt
      (L := L) (K := K) s.phase.val s hs
      hphase_run hsmall_run
  simpa [hnot10, s0, t0] using hs0_op

private theorem phaseEpidemicUpdate_right_phase9NeutralSupport_of_entered
    (s t : AgentState L K)
    (ht : t.phase.val < 9)
    (hout : (phaseEpidemicUpdate L K s t).2.phase.val = 9)
    (hneut : t.smallBias.val = 3) :
    (phaseEpidemicUpdate L K s t).2.opinions = phase2OpinionT := by
  unfold phaseEpidemicUpdate at hout ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hnot10 :
      ¬ ((s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)) := by
    intro h10
    have ht_before : t.phase.val < 10 := by omega
    have hten : (phase10EpidemicEntry L K t t0).phase.val = 10 := by
      simp [phase10EpidemicEntry, ht_before]
    have hphase10 :
        (phase10EpidemicEntry L K t t0).phase.val = 9 := by
      simpa [h10, s0, t0] using hout
    omega
  have ht0_phase : t0.phase.val = 9 := by
    simpa [hnot10, s0, t0] using hout
  have hshape :
      t0.phase.val = p.val ∨ t0.phase.val = 10 := by
    simpa [t0] using
      runInitsBetween_phase_eq_start_or_ten (L := L) (K := K)
        t.phase.val p.val p.val ({ t with phase := p }) (Or.inl (by simp))
  have hp9 : p.val = 9 := by
    rcases hshape with hp | hten
    · omega
    · omega
  have hp_eq : p = ⟨9, by decide⟩ := Fin.ext hp9
  have ht0_small : t0.smallBias.val = 3 := by
    have hpres := runInitsBetween_preserves_smallBias
      (L := L) (K := K) t.phase.val p.val ({ t with phase := p })
    simpa [t0, hpres] using hneut
  have ht0_op : t0.opinions = phase2OpinionT := by
    have ht0_rw :
        t0 =
          runInitsBetween L K t.phase.val 9
            ({ t with phase := ⟨9, by decide⟩ }) := by
      simp [t0, hp_eq]
    have hphase_run := ht0_phase
    have hsmall_run := ht0_small
    rw [ht0_rw] at hphase_run hsmall_run
    rw [ht0_rw]
    exact phase2OpinionT_runInitsBetween_to_nine_of_lt
      (L := L) (K := K) t.phase.val t ht
      hphase_run hsmall_run
  simpa [hnot10, s0, t0] using ht0_op

private theorem phaseEpidemicUpdate_left_phase9_opinion_T_of_right_le_nine
    (s t : AgentState L K) (hs_le : s.phase.val ≤ 9) (ht_le : t.phase.val ≤ 9)
    (hprev : s.phase.val = 9 → s.smallBias.val = 3 → s.opinions = phase2OpinionT)
    (hphase : (phaseEpidemicUpdate L K s t).1.phase.val = 9)
    (hsmall : (phaseEpidemicUpdate L K s t).1.smallBias.val = 3) :
    (phaseEpidemicUpdate L K s t).1.opinions = phase2OpinionT := by
  by_cases hs : s.phase.val = 9
  · have hop := phaseEpidemicUpdate_left_opinions_of_phase9_right_le_nine
      (L := L) (K := K) s t hs ht_le
    have hsmall_pres := (phaseEpidemicUpdate_preserves_smallBias L K s t).1
    have hs_small : s.smallBias.val = 3 := by
      simpa [hsmall_pres] using hsmall
    simpa [hop] using hprev hs hs_small
  · have hs_lt : s.phase.val < 9 := by omega
    have hsmall_pres := (phaseEpidemicUpdate_preserves_smallBias L K s t).1
    have hs_small : s.smallBias.val = 3 := by
      simpa [hsmall_pres] using hsmall
    exact phaseEpidemicUpdate_left_phase9NeutralSupport_of_entered
      (L := L) (K := K) s t hs_lt hphase hs_small

private theorem phaseEpidemicUpdate_right_phase9_opinion_T_of_left_le_nine
    (s t : AgentState L K) (hs_le : s.phase.val ≤ 9) (ht_le : t.phase.val ≤ 9)
    (hprev : t.phase.val = 9 → t.smallBias.val = 3 → t.opinions = phase2OpinionT)
    (hphase : (phaseEpidemicUpdate L K s t).2.phase.val = 9)
    (hsmall : (phaseEpidemicUpdate L K s t).2.smallBias.val = 3) :
    (phaseEpidemicUpdate L K s t).2.opinions = phase2OpinionT := by
  by_cases ht : t.phase.val = 9
  · have hop := phaseEpidemicUpdate_right_opinions_of_phase9_left_le_nine
      (L := L) (K := K) s t ht hs_le
    have hsmall_pres := (phaseEpidemicUpdate_preserves_smallBias L K s t).2
    have ht_small : t.smallBias.val = 3 := by
      simpa [hsmall_pres] using hsmall
    simpa [hop] using hprev ht ht_small
  · have ht_lt : t.phase.val < 9 := by omega
    have hsmall_pres := (phaseEpidemicUpdate_preserves_smallBias L K s t).2
    have ht_small : t.smallBias.val = 3 := by
      simpa [hsmall_pres] using hsmall
    exact phaseEpidemicUpdate_right_phase9NeutralSupport_of_entered
      (L := L) (K := K) s t ht_lt hphase ht_small

private theorem Transition_left_phase9_opinion_T_of_neutral_outputs
    (s t : AgentState L K)
    (hs_prev : s.phase.val = 9 → s.smallBias.val = 3 → s.opinions = phase2OpinionT)
    (ht_prev : t.phase.val = 9 → t.smallBias.val = 3 → t.opinions = phase2OpinionT)
    (hout_left_le : (Transition L K s t).1.phase.val ≤ 9)
    (hout_right_le : (Transition L K s t).2.phase.val ≤ 9)
    (hneut_left :
      (Transition L K s t).1.phase.val = 9 →
        (Transition L K s t).1.smallBias.val = 3)
    (hneut_right :
      (Transition L K s t).2.phase.val = 9 →
        (Transition L K s t).2.smallBias.val = 3)
    (hphase : (Transition L K s t).1.phase.val = 9) :
    (Transition L K s t).1.opinions = phase2OpinionT := by
  have hsmall_final : (Transition L K s t).1.smallBias.val = 3 :=
    hneut_left hphase
  have hs_le : s.phase.val ≤ 9 := by
    have hmax := Transition_left_phase_ge_pair_max (L := L) (K := K) s t
    rw [hphase] at hmax
    omega
  have ht_le : t.phase.val ≤ 9 := by
    have hmax := Transition_left_phase_ge_pair_max (L := L) (K := K) s t
    rw [hphase] at hmax
    omega
  unfold Transition at hout_left_le hout_right_le hneut_left hneut_right hphase hsmall_final ⊢
  generalize he : phaseEpidemicUpdate L K s t = e
  rcases e with ⟨s', t'⟩
  rw [he] at hout_left_le hout_right_le hneut_left hneut_right hphase hsmall_final
  change
    (finishPhase10Entry L K s'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).1).opinions = phase2OpinionT
  generalize hp : s'.phase = p
  fin_cases p
  · have hpval : s'.phase.val = 0 := by simpa [hp]
    have hlocal : (Phase0Transition L K s' t').1.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    exact False.elim
      (Phase0Transition_left_phase_ne_nine_of_phase_le_seven
        (L := L) (K := K) s' t' (by omega) hlocal)
  · have hpval : s'.phase.val = 1 := by simpa [hp]
    have hlocal : (Phase1Transition L K s' t').1.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    exact False.elim
      (Phase1Transition_left_phase_ne_nine_of_phase_le_seven
        (L := L) (K := K) s' t' (by omega) hlocal)
  · have hpval : s'.phase.val = 2 := by simpa [hp]
    have hlocal : (Phase2Transition L K s' t').1.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    exact False.elim
      (Phase2Transition_left_phase_ne_nine_of_phase_le_seven
        (L := L) (K := K) s' t' (by omega) hlocal)
  · have hpval : s'.phase.val = 3 := by simpa [hp]
    have hlocal : (Phase3Transition L K s' t').1.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    exact False.elim
      (Phase3Transition_left_phase_ne_nine_of_phase_le_seven
        (L := L) (K := K) s' t' (by omega) hlocal)
  · have hpval : s'.phase.val = 4 := by simpa [hp]
    have hlocal : (Phase4Transition L K s' t').1.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    exact False.elim
      (Phase4Transition_left_phase_ne_nine_of_phase_le_seven
        (L := L) (K := K) s' t' (by omega) hlocal)
  · have hpval : s'.phase.val = 5 := by simpa [hp]
    have hlocal : (Phase5Transition L K s' t').1.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    exact False.elim
      (Phase5Transition_left_phase_ne_nine_of_phase_le_seven
        (L := L) (K := K) s' t' (by omega) hlocal)
  · have hpval : s'.phase.val = 6 := by simpa [hp]
    have hlocal : (Phase6Transition L K s' t').1.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    exact False.elim
      (Phase6Transition_left_phase_ne_nine_of_phase_le_seven
        (L := L) (K := K) s' t' (by omega) hlocal)
  · have hpval : s'.phase.val = 7 := by simpa [hp]
    have hlocal : (Phase7Transition L K s' t').1.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    exact False.elim
      (Phase7Transition_left_phase_ne_nine_of_phase_le_seven
        (L := L) (K := K) s' t' (by omega) hlocal)
  · have hlocal_phase : (Phase8Transition L K s' t').1.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have hlocal_small : (Phase8Transition L K s' t').1.smallBias.val = 3 := by
      simpa [hp, finishPhase10Entry_smallBias] using hsmall_final
    have hop := Phase8Transition_left_phase9_opinion_T_of_smallBias_three
      (L := L) (K := K) s' t' (by simpa [hp]) hlocal_phase hlocal_small
    simpa [hp, finishPhase10Entry_opinions] using hop
  · have hpval : s'.phase.val = 9 := by simpa [hp]
    have hlocal_left_phase : (Phase9Transition L K s' t').1.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have hlocal_left_small : (Phase9Transition L K s' t').1.smallBias.val = 3 := by
      simpa [hp, finishPhase10Entry_smallBias] using hsmall_final
    have hright_final_le :
        (finishPhase10Entry L K t' (Phase9Transition L K s' t').2).phase.val ≤ 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hout_right_le
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase9Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase9Transition L K s' t').2.phase.val at hmono
      have hlocal_right_le : (Phase9Transition L K s' t').2.phase.val ≤ 9 := by
        simpa [finishPhase10Entry_phase_val] using hright_final_le
      omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
        (L := L) (K := K) s t hs_le ht_le
        (by simpa [he, hp] using (by omega : s'.phase.val ≠ 10))
        (by simpa [he] using ht'_not_ten)
    have ht'_phase : t'.phase.val = 9 := by
      have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
      omega
    have hlocal_right_phase : (Phase9Transition L K s' t').2.phase.val = 9 := by
      have hmono := (Phase9Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase9Transition L K s' t').2.phase.val at hmono
      have hlocal_right_le : (Phase9Transition L K s' t').2.phase.val ≤ 9 := by
        simpa [finishPhase10Entry_phase_val] using hright_final_le
      omega
    have hright_final_phase :
        (finishPhase10Entry L K t' (Phase9Transition L K s' t').2).phase.val = 9 := by
      simpa [finishPhase10Entry_phase_val] using hlocal_right_phase
    have hright_final_small :
        (finishPhase10Entry L K t' (Phase9Transition L K s' t').2).smallBias.val = 3 := by
      have hsmall0 := hneut_right (by simpa [hp] using hright_final_phase)
      simpa [hp] using hsmall0
    have hlocal_right_small : (Phase9Transition L K s' t').2.smallBias.val = 3 := by
      simpa [finishPhase10Entry_smallBias] using hright_final_small
    have hs'_small : s'.smallBias.val = 3 := by
      have hpres := (Phase9Transition_preserves_smallBias L K s' t').1
      simpa [hpres] using hlocal_left_small
    have ht'_small : t'.smallBias.val = 3 := by
      have hpres := (Phase9Transition_preserves_smallBias L K s' t').2
      simpa [hpres] using hlocal_right_small
    have hs'_op0 := phaseEpidemicUpdate_left_phase9_opinion_T_of_right_le_nine
      (L := L) (K := K) s t hs_le ht_le hs_prev
      (by simpa [he] using hpval) (by simpa [he] using hs'_small)
    have ht'_op0 := phaseEpidemicUpdate_right_phase9_opinion_T_of_left_le_nine
      (L := L) (K := K) s t hs_le ht_le ht_prev
      (by simpa [he] using ht'_phase) (by simpa [he] using ht'_small)
    have hs'_op : s'.opinions = phase2OpinionT := by
      simpa [he] using hs'_op0
    have ht'_op : t'.opinions = phase2OpinionT := by
      simpa [he] using ht'_op0
    have hop := Phase9Transition_neutral_left (L := L) (K := K) s' t'
      (by intro _; exact hs'_op) (by intro _; exact ht'_op)
      hlocal_left_small hlocal_right_small
    simpa [hp, finishPhase10Entry_opinions] using hop
  · have hpval : s'.phase.val = 10 := by simpa [hp]
    have hlocal_phase : (Phase10Transition L K s' t').1.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have hphase_eq := (Phase10Transition_phase_eq (L := L) (K := K) s' t').1
    have hval : (Phase10Transition L K s' t').1.phase.val = s'.phase.val := by
      rw [hphase_eq]
    omega

private theorem Transition_right_phase9_opinion_T_of_neutral_outputs
    (s t : AgentState L K)
    (hs_prev : s.phase.val = 9 → s.smallBias.val = 3 → s.opinions = phase2OpinionT)
    (ht_prev : t.phase.val = 9 → t.smallBias.val = 3 → t.opinions = phase2OpinionT)
    (hout_left_le : (Transition L K s t).1.phase.val ≤ 9)
    (hout_right_le : (Transition L K s t).2.phase.val ≤ 9)
    (hneut_left :
      (Transition L K s t).1.phase.val = 9 →
        (Transition L K s t).1.smallBias.val = 3)
    (hneut_right :
      (Transition L K s t).2.phase.val = 9 →
        (Transition L K s t).2.smallBias.val = 3)
    (hphase : (Transition L K s t).2.phase.val = 9) :
    (Transition L K s t).2.opinions = phase2OpinionT := by
  have hsmall_final : (Transition L K s t).2.smallBias.val = 3 :=
    hneut_right hphase
  have hs_le : s.phase.val ≤ 9 := by
    have hmax := Transition_right_phase_ge_pair_max (L := L) (K := K) s t
    rw [hphase] at hmax
    omega
  have ht_le : t.phase.val ≤ 9 := by
    have hmax := Transition_right_phase_ge_pair_max (L := L) (K := K) s t
    rw [hphase] at hmax
    omega
  unfold Transition at hout_left_le hout_right_le hneut_left hneut_right hphase hsmall_final ⊢
  generalize he : phaseEpidemicUpdate L K s t = e
  rcases e with ⟨s', t'⟩
  rw [he] at hout_left_le hout_right_le hneut_left hneut_right hphase hsmall_final
  change
    (finishPhase10Entry L K t'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).2).opinions = phase2OpinionT
  generalize hp : s'.phase = p
  fin_cases p
  · have hs0 : s'.phase.val = 0 := by simpa [hp]
    have hlocal : (Phase0Transition L K s' t').2.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase0Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase0Transition L K s' t').2.phase.val at hmono
      omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
        (L := L) (K := K) s t hs_le ht_le
        (by simpa [he, hp] using (by omega : s'.phase.val ≠ 10))
        (by simpa [he] using ht'_not_ten)
    have ht0 : t'.phase.val = 0 := by
      have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
      omega
    exact False.elim
      (Phase0Transition_right_phase_ne_nine_of_phase_le_seven
        (L := L) (K := K) s' t' (by omega) hlocal)
  · have hs1 : s'.phase.val = 1 := by simpa [hp]
    have hlocal : (Phase1Transition L K s' t').2.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase1Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase1Transition L K s' t').2.phase.val at hmono
      omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
        (L := L) (K := K) s t hs_le ht_le
        (by simpa [he, hp] using (by omega : s'.phase.val ≠ 10))
        (by simpa [he] using ht'_not_ten)
    have ht1 : t'.phase.val = 1 := by
      have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
      omega
    exact False.elim
      (Phase1Transition_right_phase_ne_nine_of_phase_le_seven
        (L := L) (K := K) s' t' (by omega) hlocal)
  · have hs2 : s'.phase.val = 2 := by simpa [hp]
    have hlocal : (Phase2Transition L K s' t').2.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase2Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase2Transition L K s' t').2.phase.val at hmono
      omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
        (L := L) (K := K) s t hs_le ht_le
        (by simpa [he, hp] using (by omega : s'.phase.val ≠ 10))
        (by simpa [he] using ht'_not_ten)
    have ht2 : t'.phase.val = 2 := by
      have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
      omega
    exact False.elim
      (Phase2Transition_right_phase_ne_nine_of_phase_le_seven
        (L := L) (K := K) s' t' (by omega) hlocal)
  · have hs3 : s'.phase.val = 3 := by simpa [hp]
    have hlocal : (Phase3Transition L K s' t').2.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase3Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase3Transition L K s' t').2.phase.val at hmono
      omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
        (L := L) (K := K) s t hs_le ht_le
        (by simpa [he, hp] using (by omega : s'.phase.val ≠ 10))
        (by simpa [he] using ht'_not_ten)
    have ht3 : t'.phase.val = 3 := by
      have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
      omega
    exact False.elim
      (Phase3Transition_right_phase_ne_nine_of_phase_le_seven
        (L := L) (K := K) s' t' (by omega) hlocal)
  · have hs4 : s'.phase.val = 4 := by simpa [hp]
    have hlocal : (Phase4Transition L K s' t').2.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase4Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase4Transition L K s' t').2.phase.val at hmono
      omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
        (L := L) (K := K) s t hs_le ht_le
        (by simpa [he] using (by omega : s'.phase.val ≠ 10))
        (by simpa [he] using ht'_not_ten)
    have ht4 : t'.phase.val = 4 := by
      have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
      omega
    exact False.elim
      (Phase4Transition_right_phase_ne_nine_of_phase_le_seven
        (L := L) (K := K) s' t' (by omega) hlocal)
  · have hs5 : s'.phase.val = 5 := by simpa [hp]
    have hlocal : (Phase5Transition L K s' t').2.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase5Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase5Transition L K s' t').2.phase.val at hmono
      omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
        (L := L) (K := K) s t hs_le ht_le
        (by simpa [he] using (by omega : s'.phase.val ≠ 10))
        (by simpa [he] using ht'_not_ten)
    have ht5 : t'.phase.val = 5 := by
      have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
      omega
    exact False.elim
      (Phase5Transition_right_phase_ne_nine_of_phase_le_seven
        (L := L) (K := K) s' t' (by omega) hlocal)
  · have hs6 : s'.phase.val = 6 := by simpa [hp]
    have hlocal : (Phase6Transition L K s' t').2.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase6Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase6Transition L K s' t').2.phase.val at hmono
      omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
        (L := L) (K := K) s t hs_le ht_le
        (by simpa [he] using (by omega : s'.phase.val ≠ 10))
        (by simpa [he] using ht'_not_ten)
    have ht6 : t'.phase.val = 6 := by
      have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
      omega
    exact False.elim
      (Phase6Transition_right_phase_ne_nine_of_phase_le_seven
        (L := L) (K := K) s' t' (by omega) hlocal)
  · have hs7 : s'.phase.val = 7 := by simpa [hp]
    have hlocal : (Phase7Transition L K s' t').2.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase7Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase7Transition L K s' t').2.phase.val at hmono
      omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
        (L := L) (K := K) s t hs_le ht_le
        (by simpa [he] using (by omega : s'.phase.val ≠ 10))
        (by simpa [he] using ht'_not_ten)
    have ht7 : t'.phase.val = 7 := by
      have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
      omega
    exact False.elim
      (Phase7Transition_right_phase_ne_nine_of_phase_le_seven
        (L := L) (K := K) s' t' (by omega) hlocal)
  · have hlocal_phase : (Phase8Transition L K s' t').2.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have hlocal_small : (Phase8Transition L K s' t').2.smallBias.val = 3 := by
      simpa [hp, finishPhase10Entry_smallBias] using hsmall_final
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase8Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase8Transition L K s' t').2.phase.val at hmono
      omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
        (L := L) (K := K) s t hs_le ht_le
        (by simpa [he, hp] using (by omega : s'.phase.val ≠ 10))
        (by simpa [he] using ht'_not_ten)
    have ht'_phase : t'.phase.val = 8 := by
      have hs8 : s'.phase.val = 8 := by simpa [hp]
      have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
      omega
    have hop := Phase8Transition_right_phase9_opinion_T_of_smallBias_three
      (L := L) (K := K) s' t' ht'_phase hlocal_phase hlocal_small
    simpa [hp, finishPhase10Entry_opinions] using hop
  · have hpval : s'.phase.val = 9 := by simpa [hp]
    have hlocal_right_phase : (Phase9Transition L K s' t').2.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have hlocal_right_small : (Phase9Transition L K s' t').2.smallBias.val = 3 := by
      simpa [hp, finishPhase10Entry_smallBias] using hsmall_final
    have hleft_final_le :
        (finishPhase10Entry L K s' (Phase9Transition L K s' t').1).phase.val ≤ 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hout_left_le
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase9Transition_phase_nondec (L := L) (K := K) s' t').2
      change t'.phase.val ≤ (Phase9Transition L K s' t').2.phase.val at hmono
      omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_nine_not_ten
        (L := L) (K := K) s t hs_le ht_le
        (by simpa [he, hp] using (by omega : s'.phase.val ≠ 10))
        (by simpa [he] using ht'_not_ten)
    have ht'_phase : t'.phase.val = 9 := by
      have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
      omega
    have hlocal_left_phase : (Phase9Transition L K s' t').1.phase.val = 9 := by
      have hmono := (Phase9Transition_phase_nondec (L := L) (K := K) s' t').1
      change s'.phase.val ≤ (Phase9Transition L K s' t').1.phase.val at hmono
      have hlocal_left_le : (Phase9Transition L K s' t').1.phase.val ≤ 9 := by
        simpa [finishPhase10Entry_phase_val] using hleft_final_le
      omega
    have hleft_final_phase :
        (finishPhase10Entry L K s' (Phase9Transition L K s' t').1).phase.val = 9 := by
      simpa [finishPhase10Entry_phase_val] using hlocal_left_phase
    have hleft_final_small :
        (finishPhase10Entry L K s' (Phase9Transition L K s' t').1).smallBias.val = 3 := by
      have hsmall0 := hneut_left (by simpa [hp] using hleft_final_phase)
      simpa [hp] using hsmall0
    have hlocal_left_small : (Phase9Transition L K s' t').1.smallBias.val = 3 := by
      simpa [finishPhase10Entry_smallBias] using hleft_final_small
    have hs'_small : s'.smallBias.val = 3 := by
      have hpres := (Phase9Transition_preserves_smallBias L K s' t').1
      simpa [hpres] using hlocal_left_small
    have ht'_small : t'.smallBias.val = 3 := by
      have hpres := (Phase9Transition_preserves_smallBias L K s' t').2
      simpa [hpres] using hlocal_right_small
    have hs'_op0 := phaseEpidemicUpdate_left_phase9_opinion_T_of_right_le_nine
      (L := L) (K := K) s t hs_le ht_le hs_prev
      (by simpa [he] using hpval) (by simpa [he] using hs'_small)
    have ht'_op0 := phaseEpidemicUpdate_right_phase9_opinion_T_of_left_le_nine
      (L := L) (K := K) s t hs_le ht_le ht_prev
      (by simpa [he] using ht'_phase) (by simpa [he] using ht'_small)
    have hs'_op : s'.opinions = phase2OpinionT := by
      simpa [he] using hs'_op0
    have ht'_op : t'.opinions = phase2OpinionT := by
      simpa [he] using ht'_op0
    have hop := Phase9Transition_neutral_right (L := L) (K := K) s' t'
      (by intro _; exact hs'_op) (by intro _; exact ht'_op)
      hlocal_left_small hlocal_right_small
    simpa [hp, finishPhase10Entry_opinions] using hop
  · have hpval : s'.phase.val = 10 := by simpa [hp]
    have hlocal_phase : (Phase10Transition L K s' t').2.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have ht'_phase : t'.phase.val = 9 := by
      have hphase_eq := (Phase10Transition_phase_eq (L := L) (K := K) s' t').2
      have hval : (Phase10Transition L K s' t').2.phase.val = t'.phase.val := by
        rw [hphase_eq]
      omega
    have hlocal_small : (Phase10Transition L K s' t').2.smallBias.val = 3 := by
      simpa [hp, finishPhase10Entry_smallBias] using hsmall_final
    have ht'_small : t'.smallBias.val = 3 := by
      have hpres := Phase10Transition_preserves_smallBias_pair (L := L) (K := K) s' t'
      simpa [hpres.2] using hlocal_small
    have ht'_op0 := phaseEpidemicUpdate_right_phase9_opinion_T_of_left_le_nine
      (L := L) (K := K) s t hs_le ht_le ht_prev
      (by simpa [he] using ht'_phase) (by simpa [he] using ht'_small)
    have ht'_op : t'.opinions = phase2OpinionT := by
      simpa [he] using ht'_op0
    have hop := Phase10Transition_preserves_opinion_T_right
      (L := L) (K := K) s' t' ht'_op
    simpa [hp, finishPhase10Entry_opinions] using hop

private theorem Transition_left_smallBias_eq_of_phase9_to_phase9
    (s t : AgentState L K) (hs : s.phase.val = 9)
    (hphase : (Transition L K s t).1.phase.val = 9) :
    (Transition L K s t).1.smallBias = s.smallBias := by
  have ht_le : t.phase.val ≤ 9 := by
    have hmax := Transition_left_phase_ge_pair_max (L := L) (K := K) s t
    rw [hphase] at hmax
    omega
  unfold Transition at hphase ⊢
  generalize he : phaseEpidemicUpdate L K s t = e at hphase ⊢
  rcases e with ⟨s', t'⟩
  have hs'_phase : s'.phase.val = 9 ∨ s'.phase.val = 10 := by
    have hle :=
      phaseEpidemicUpdate_left_phase_le_nine_or_ten_of_phases_le_nine
        (L := L) (K := K) s t (by omega) ht_le
    have hge := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
    rcases hle with hle | hten
    · left
      change max s.phase.val t.phase.val ≤
        (phaseEpidemicUpdate L K s t).1.phase.val at hge
      have hphase9 : (phaseEpidemicUpdate L K s t).1.phase.val = 9 := by
        omega
      simpa [he] using hphase9
    · right
      simpa [he] using hten
  have hs_epi_small := (phaseEpidemicUpdate_preserves_smallBias L K s t).1
  change
    (finishPhase10Entry L K s'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).1).smallBias = s.smallBias
  generalize hp : s'.phase = p
  fin_cases p
  · have hpval : s'.phase.val = 0 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 1 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 2 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 3 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 4 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 5 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 6 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 7 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 8 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hlocal_small := (Phase9Transition_preserves_smallBias L K s' t').1
    have hs'_small : s'.smallBias = s.smallBias := by
      simpa [he] using hs_epi_small
    simpa [hp, finishPhase10Entry_smallBias, hlocal_small, hs'_small]
  · have hlocal_phase : (Phase10Transition L K s' t').1.phase.val = 9 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have hphase_eq := (Phase10Transition_phase_eq (L := L) (K := K) s' t').1
    have hval : (Phase10Transition L K s' t').1.phase.val = s'.phase.val := by
      rw [hphase_eq]
    have hpval : s'.phase.val = 10 := by simpa [hp]
    omega

private theorem Transition_right_smallBias_eq_of_phase9_to_phase9
    (s t : AgentState L K) (ht : t.phase.val = 9)
    (hphase : (Transition L K s t).2.phase.val = 9) :
    (Transition L K s t).2.smallBias = t.smallBias := by
  have hs_le : s.phase.val ≤ 9 := by
    have hmax := Transition_right_phase_ge_pair_max (L := L) (K := K) s t
    rw [hphase] at hmax
    omega
  unfold Transition at hphase ⊢
  generalize he : phaseEpidemicUpdate L K s t = e at hphase ⊢
  rcases e with ⟨s', t'⟩
  have hs'_phase : s'.phase.val = 9 ∨ s'.phase.val = 10 := by
    have hle :=
      phaseEpidemicUpdate_left_phase_le_nine_or_ten_of_phases_le_nine
        (L := L) (K := K) s t hs_le (by omega)
    have hge := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
    rcases hle with hle | hten
    · left
      change max s.phase.val t.phase.val ≤
        (phaseEpidemicUpdate L K s t).1.phase.val at hge
      have hphase9 : (phaseEpidemicUpdate L K s t).1.phase.val = 9 := by
        omega
      simpa [he] using hphase9
    · right
      simpa [he] using hten
  have ht_epi_small := (phaseEpidemicUpdate_preserves_smallBias L K s t).2
  change
    (finishPhase10Entry L K t'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).2).smallBias = t.smallBias
  generalize hp : s'.phase = p
  fin_cases p
  · have hpval : s'.phase.val = 0 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 1 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 2 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 3 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 4 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 5 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 6 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 7 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hpval : s'.phase.val = 8 := by simpa [hp]
    rcases hs'_phase with h | h <;> omega
  · have hlocal_small := (Phase9Transition_preserves_smallBias L K s' t').2
    have ht'_small : t'.smallBias = t.smallBias := by
      simpa [he] using ht_epi_small
    simpa [hp, finishPhase10Entry_smallBias, hlocal_small, ht'_small]
  · have hlocal_small := (Phase10Transition_preserves_smallBias_pair
      (L := L) (K := K) s' t').2
    have ht'_small : t'.smallBias = t.smallBias := by
      simpa [he] using ht_epi_small
    simpa [hp, finishPhase10Entry_smallBias, hlocal_small, ht'_small]

theorem reachable_phase9_neutral_opinions_of_all_neutral
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase_le : ∀ a ∈ c, a.phase.val ≤ 9)
    (hneut : ∀ a ∈ c, a.phase.val = 9 → a.smallBias.val = 3) :
    ∀ a ∈ c, a.phase.val = 9 → a.opinions = phase2OpinionT := by
  classical
  induction hreach with
  | refl =>
      intro a ha hphase
      have hphase0 := (hinit a ha).1
      have hval0 : a.phase.val = 0 := by
        simpa [hphase0]
      omega
  | tail hreach_prev hstep ih =>
      rename_i cprev cnext
      rcases hstep with ⟨s, t, happ, hc'⟩
      dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
      have hs_mem : s ∈ cprev := Multiset.mem_of_le happ (by simp)
      have ht_mem : t ∈ cprev := Multiset.mem_of_le happ (by simp)
      have hout_left_mem : (Transition L K s t).1 ∈ cnext := by
        rw [hc']
        simp
      have hout_right_mem : (Transition L K s t).2 ∈ cnext := by
        rw [hc']
        simp
      have residual_mem {a : AgentState L K} (ha : a ∈ cprev)
          (has : a ≠ s) (hat : a ≠ t) :
          a ∈ cprev - ({s, t} : Multiset (AgentState L K)) := by
        have h1 : a ∈ cprev.erase s := (Multiset.mem_erase_of_ne has).2 ha
        have h2 : a ∈ (cprev.erase s).erase t :=
          (Multiset.mem_erase_of_ne hat).2 h1
        simpa using h2
      have hphase_le_prev : ∀ a ∈ cprev, a.phase.val ≤ 9 := by
        intro a ha
        by_cases has : a = s
        · subst a
          have hmono := (Transition_phase_monotone (L := L) (K := K) s t).1
          change s.phase.val ≤ (Transition L K s t).1.phase.val at hmono
          have hout_le := hphase_le (Transition L K s t).1 hout_left_mem
          omega
        · by_cases hat : a = t
          · subst a
            have hmono := (Transition_phase_monotone (L := L) (K := K) s t).2
            change t.phase.val ≤ (Transition L K s t).2.phase.val at hmono
            have hout_le := hphase_le (Transition L K s t).2 hout_right_mem
            omega
          · have ha_res :
                a ∈ cprev - ({s, t} : Multiset (AgentState L K)) :=
              residual_mem ha has hat
            have ha_next : a ∈ cnext := by
              rw [hc']
              exact Multiset.mem_add.2 (Or.inl ha_res)
            exact hphase_le a ha_next
      have hneut_prev : ∀ a ∈ cprev, a.phase.val = 9 → a.smallBias.val = 3 := by
        intro a ha hphase
        by_cases has : a = s
        · subst a
          have hout_phase : (Transition L K s t).1.phase.val = 9 := by
            have hmono := (Transition_phase_monotone (L := L) (K := K) s t).1
            change s.phase.val ≤ (Transition L K s t).1.phase.val at hmono
            have hout_le := hphase_le (Transition L K s t).1 hout_left_mem
            omega
          have hout_small := hneut (Transition L K s t).1 hout_left_mem hout_phase
          have hsmall_eq :=
            Transition_left_smallBias_eq_of_phase9_to_phase9
              (L := L) (K := K) s t hphase hout_phase
          rw [hsmall_eq] at hout_small
          exact hout_small
        · by_cases hat : a = t
          · subst a
            have hout_phase : (Transition L K s t).2.phase.val = 9 := by
              have hmono := (Transition_phase_monotone (L := L) (K := K) s t).2
              change t.phase.val ≤ (Transition L K s t).2.phase.val at hmono
              have hout_le := hphase_le (Transition L K s t).2 hout_right_mem
              omega
            have hout_small := hneut (Transition L K s t).2 hout_right_mem hout_phase
            have hsmall_eq :=
              Transition_right_smallBias_eq_of_phase9_to_phase9
                (L := L) (K := K) s t hphase hout_phase
            rw [hsmall_eq] at hout_small
            exact hout_small
          · have ha_res :
                a ∈ cprev - ({s, t} : Multiset (AgentState L K)) :=
              residual_mem ha has hat
            have ha_next : a ∈ cnext := by
              rw [hc']
              exact Multiset.mem_add.2 (Or.inl ha_res)
            exact hneut a ha_next hphase
      intro a ha hphase
      rw [hc'] at ha
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
      rcases ha with ha_old | ha_new
      · exact ih hphase_le_prev hneut_prev a
          (Multiset.mem_of_le
            (Multiset.sub_le_self cprev ({s, t} : Multiset (AgentState L K))) ha_old)
          hphase
      · rcases ha_new with h_eq | h_eq
        · subst a
          exact Transition_left_phase9_opinion_T_of_neutral_outputs
            (L := L) (K := K) s t
            (fun hs _ => ih hphase_le_prev hneut_prev s hs_mem hs)
            (fun ht _ => ih hphase_le_prev hneut_prev t ht_mem ht)
            (hphase_le (Transition L K s t).1 hout_left_mem)
            (hphase_le (Transition L K s t).2 hout_right_mem)
            (fun hp => hneut (Transition L K s t).1 hout_left_mem hp)
            (fun hp => hneut (Transition L K s t).2 hout_right_mem hp)
            hphase
        · subst a
          exact Transition_right_phase9_opinion_T_of_neutral_outputs
            (L := L) (K := K) s t
            (fun hs _ => ih hphase_le_prev hneut_prev s hs_mem hs)
            (fun ht _ => ih hphase_le_prev hneut_prev t ht_mem ht)
            (hphase_le (Transition L K s t).1 hout_left_mem)
            (hphase_le (Transition L K s t).2 hout_right_mem)
            (fun hp => hneut (Transition L K s t).1 hout_left_mem hp)
            (fun hp => hneut (Transition L K s t).2 hout_right_mem hp)
            hphase

private lemma exists_applicable_pair_of_countP_ge_two
    {α : Type*} {p : α → Prop} [DecidablePred p]
    {c : Multiset α} (h : 2 ≤ Multiset.countP p c) :
    ∃ s t, ({s, t} : Multiset α) ≤ c ∧ p s ∧ p t := by
  classical
  let good := c.filter p
  have hgood_card : 2 ≤ good.card := by
    simpa [good, Multiset.countP_eq_card_filter] using h
  have hgood_pos : 0 < good.card := by omega
  rcases Multiset.card_pos_iff_exists_mem.mp hgood_pos with ⟨s, hs⟩
  have herase_pos : 0 < (good.erase s).card := by
    have hcard := Multiset.card_erase_add_one hs
    omega
  rcases Multiset.card_pos_iff_exists_mem.mp herase_pos with ⟨t, ht⟩
  have ht_good : t ∈ good := Multiset.mem_of_mem_erase ht
  have hpair_good : ({s, t} : Multiset α) ≤ good := by
    change s ::ₘ ({t} : Multiset α) ≤ good
    rw [← Multiset.cons_erase hs]
    exact Multiset.cons_le_cons s (Multiset.singleton_le.mpr ht)
  exact ⟨s, t, le_trans hpair_good (Multiset.filter_le p c),
    (Multiset.mem_filter.mp hs).2, (Multiset.mem_filter.mp ht_good).2⟩

private lemma clockCount_ge_two_of_applicable_clocks
    {c : Config (AgentState L K)} {i j : AgentState L K}
    (happ : Protocol.Applicable c i j) (hi : i.role = .clock)
    (hj : j.role = .clock) :
    2 ≤ clockCount (L := L) (K := K) c := by
  have hpair :
      Multiset.countP (fun a : AgentState L K => a.role = .clock)
        ({i, j} : Multiset (AgentState L K)) = 2 := by
    rw [show ({i, j} : Multiset (AgentState L K)) =
        ({i} : Multiset _) + {j} by rfl,
      Multiset.countP_add,
      countP_singleton_of_dc (p := fun a : AgentState L K => a.role = .clock) hi,
      countP_singleton_of_dc (p := fun a : AgentState L K => a.role = .clock) hj]
  have hle := Multiset.countP_le_of_le
    (p := fun a : AgentState L K => a.role = .clock) happ
  unfold clockCount
  omega

private lemma exists_applicable_clock_pair_of_clockCount_ge_two
    {c : Config (AgentState L K)}
    (h : 2 ≤ clockCount (L := L) (K := K) c) :
    ∃ i j, Protocol.Applicable c i j ∧ i.role = .clock ∧ j.role = .clock := by
  rcases exists_applicable_pair_of_countP_ge_two
      (p := fun a : AgentState L K => a.role = .clock)
      (by simpa [clockCount] using h) with
    ⟨i, j, happ, hi, hj⟩
  exact ⟨i, j, happ, hi, hj⟩

private lemma Phase0Transition_preserves_clock_role_left
    (s t : AgentState L K) (hs : s.role = .clock) :
    (Phase0Transition L K s t).1.role = .clock := by
  rcases s with
    ⟨sinput, soutput, sphase, srole, sassigned, sbias, ssmallBias,
      shour, sminute, sfull, sopinions, scounter⟩
  rcases t with
    ⟨tinput, toutput, tphase, trole, tassigned, tbias, tsmallBias,
      thour, tminute, tfull, topinions, tcounter⟩
  cases srole <;> simp at hs
  cases trole <;> cases sassigned <;> cases tassigned <;>
    simp [Phase0Transition]

private lemma Phase0Transition_preserves_clock_role_right
    (s t : AgentState L K) (ht : t.role = .clock) :
    (Phase0Transition L K s t).2.role = .clock := by
  rcases s with
    ⟨sinput, soutput, sphase, srole, sassigned, sbias, ssmallBias,
      shour, sminute, sfull, sopinions, scounter⟩
  rcases t with
    ⟨tinput, toutput, tphase, trole, tassigned, tbias, tsmallBias,
      thour, tminute, tfull, topinions, tcounter⟩
  cases trole <;> simp at ht
  cases srole <;> cases sassigned <;> cases tassigned <;>
    simp [Phase0Transition]

private theorem Transition_preserves_clock_role_left
    (a b : AgentState L K) (ha_clock : a.role = .clock) :
    (Transition L K a b).1.role = .clock := by
  unfold Transition
  generalize he : phaseEpidemicUpdate L K a b = e
  rcases e with ⟨a', b'⟩
  have ha'_clock : a'.role = .clock := by
    simpa [he] using phaseEpidemicUpdate_first_preserves_clock_role
      (L := L) (K := K) a b ha_clock
  change (finishPhase10Entry L K a'
    (match a'.phase with
    | ⟨0, _⟩ => Phase0Transition L K a' b'
    | ⟨1, _⟩ => Phase1Transition L K a' b'
    | ⟨2, _⟩ => Phase2Transition L K a' b'
    | ⟨3, _⟩ => Phase3Transition L K a' b'
    | ⟨4, _⟩ => Phase4Transition L K a' b'
    | ⟨5, _⟩ => Phase5Transition L K a' b'
    | ⟨6, _⟩ => Phase6Transition L K a' b'
    | ⟨7, _⟩ => Phase7Transition L K a' b'
    | ⟨8, _⟩ => Phase8Transition L K a' b'
    | ⟨9, _⟩ => Phase9Transition L K a' b'
    | ⟨10, _⟩ => Phase10Transition L K a' b'
    | _ => (a', b')).1).role = .clock
  generalize hphase : a'.phase = p
  fin_cases p <;> simp
  · simpa [ha'_clock] using
      Phase0Transition_preserves_clock_role_left (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase1Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase2Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase3Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase4Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase5Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase6Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase7Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase8Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase9Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase10Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock

private theorem Transition_preserves_clock_role_right
    (a b : AgentState L K) (hb_clock : b.role = .clock) :
    (Transition L K a b).2.role = .clock := by
  unfold Transition
  generalize he : phaseEpidemicUpdate L K a b = e
  rcases e with ⟨a', b'⟩
  have hb'_clock : b'.role = .clock := by
    simpa [he] using phaseEpidemicUpdate_second_preserves_clock_role
      (L := L) (K := K) a b hb_clock
  change (finishPhase10Entry L K b'
    (match a'.phase with
    | ⟨0, _⟩ => Phase0Transition L K a' b'
    | ⟨1, _⟩ => Phase1Transition L K a' b'
    | ⟨2, _⟩ => Phase2Transition L K a' b'
    | ⟨3, _⟩ => Phase3Transition L K a' b'
    | ⟨4, _⟩ => Phase4Transition L K a' b'
    | ⟨5, _⟩ => Phase5Transition L K a' b'
    | ⟨6, _⟩ => Phase6Transition L K a' b'
    | ⟨7, _⟩ => Phase7Transition L K a' b'
    | ⟨8, _⟩ => Phase8Transition L K a' b'
    | ⟨9, _⟩ => Phase9Transition L K a' b'
    | ⟨10, _⟩ => Phase10Transition L K a' b'
    | _ => (a', b')).2).role = .clock
  generalize hphase : a'.phase = p
  fin_cases p <;> simp
  · simpa [hb'_clock] using
      Phase0Transition_preserves_clock_role_right (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase1Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase2Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase3Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase4Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase5Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase6Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase7Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase8Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase9Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase10Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock

private lemma transition_clock_pair_count_le_outputs_any
    (s t : AgentState L K) :
    Multiset.countP (fun a : AgentState L K => a.role = .clock)
        ({s, t} : Multiset (AgentState L K)) ≤
      Multiset.countP (fun a : AgentState L K => a.role = .clock)
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) := by
  classical
  by_cases hs_clock : s.role = .clock <;> by_cases ht_clock : t.role = .clock
  · have hs_out := Transition_preserves_clock_role_left
      (L := L) (K := K) s t hs_clock
    have ht_out := Transition_preserves_clock_role_right
      (L := L) (K := K) s t ht_clock
    rw [show ({s, t} : Multiset (AgentState L K)) =
        ({s} : Multiset _) + {t} by rfl,
      show ({(Transition L K s t).1, (Transition L K s t).2} :
        Multiset (AgentState L K)) =
          ({(Transition L K s t).1} : Multiset _) +
          {(Transition L K s t).2} by rfl,
      Multiset.countP_add, Multiset.countP_add,
      countP_singleton_of_dc
        (p := fun a : AgentState L K => a.role = .clock) hs_clock,
      countP_singleton_of_dc
        (p := fun a : AgentState L K => a.role = .clock) ht_clock,
      countP_singleton_of_dc
        (p := fun a : AgentState L K => a.role = .clock) hs_out,
      countP_singleton_of_dc
        (p := fun a : AgentState L K => a.role = .clock) ht_out]
  · have hs_out := Transition_preserves_clock_role_left
      (L := L) (K := K) s t hs_clock
    have hpair :
        Multiset.countP (fun a : AgentState L K => a.role = .clock)
          ({s, t} : Multiset (AgentState L K)) = 1 := by
      rw [show ({s, t} : Multiset (AgentState L K)) =
          ({s} : Multiset _) + {t} by rfl,
        Multiset.countP_add,
        countP_singleton_of_dc
          (p := fun a : AgentState L K => a.role = .clock) hs_clock,
        countP_singleton_of_dc_not
          (p := fun a : AgentState L K => a.role = .clock) ht_clock]
    have hout_one : 1 ≤
        Multiset.countP (fun a : AgentState L K => a.role = .clock)
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) := by
      have hsingle :
          Multiset.countP (fun a : AgentState L K => a.role = .clock)
            ({(Transition L K s t).1} : Multiset (AgentState L K)) = 1 :=
        countP_singleton_of_dc
          (p := fun a : AgentState L K => a.role = .clock) hs_out
      have hle := Multiset.countP_le_of_le
        (p := fun a : AgentState L K => a.role = .clock)
        (show ({(Transition L K s t).1} : Multiset (AgentState L K)) ≤
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) by simp)
      omega
    omega
  · have ht_out := Transition_preserves_clock_role_right
      (L := L) (K := K) s t ht_clock
    have hpair :
        Multiset.countP (fun a : AgentState L K => a.role = .clock)
          ({s, t} : Multiset (AgentState L K)) = 1 := by
      rw [show ({s, t} : Multiset (AgentState L K)) =
          ({s} : Multiset _) + {t} by rfl,
        Multiset.countP_add,
        countP_singleton_of_dc_not
          (p := fun a : AgentState L K => a.role = .clock) hs_clock,
        countP_singleton_of_dc
          (p := fun a : AgentState L K => a.role = .clock) ht_clock]
    have hout_one : 1 ≤
        Multiset.countP (fun a : AgentState L K => a.role = .clock)
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) := by
      have hsingle :
          Multiset.countP (fun a : AgentState L K => a.role = .clock)
            ({(Transition L K s t).2} : Multiset (AgentState L K)) = 1 :=
        countP_singleton_of_dc
          (p := fun a : AgentState L K => a.role = .clock) ht_out
      have hle := Multiset.countP_le_of_le
        (p := fun a : AgentState L K => a.role = .clock)
        (show ({(Transition L K s t).2} : Multiset (AgentState L K)) ≤
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) by simp)
      omega
    omega
  · rw [show ({s, t} : Multiset (AgentState L K)) =
        ({s} : Multiset _) + {t} by rfl,
      Multiset.countP_add,
      countP_singleton_of_dc_not
        (p := fun a : AgentState L K => a.role = .clock) hs_clock,
      countP_singleton_of_dc_not
        (p := fun a : AgentState L K => a.role = .clock) ht_clock]
    omega

private lemma transition_clock_pair_count_le_outputs
    (s t : AgentState L K) (hs_phase : 1 ≤ s.phase.val)
    (ht_phase : 1 ≤ t.phase.val) :
    Multiset.countP (fun a : AgentState L K => a.role = .clock)
        ({s, t} : Multiset (AgentState L K)) ≤
      Multiset.countP (fun a : AgentState L K => a.role = .clock)
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) := by
  classical
  by_cases hs_clock : s.role = .clock <;> by_cases ht_clock : t.role = .clock
  · have hs_out := Transition_preserves_clock_role_of_phase_ge_1
      (L := L) (K := K) s t hs_phase ht_phase hs_clock
    have ht_out := Transition_second_preserves_clock_role_of_phase_ge_1
      (L := L) (K := K) s t hs_phase ht_phase ht_clock
    rw [show ({s, t} : Multiset (AgentState L K)) =
        ({s} : Multiset _) + {t} by rfl,
      show ({(Transition L K s t).1, (Transition L K s t).2} :
        Multiset (AgentState L K)) =
          ({(Transition L K s t).1} : Multiset _) +
          {(Transition L K s t).2} by rfl,
      Multiset.countP_add, Multiset.countP_add,
      countP_singleton_of_dc
        (p := fun a : AgentState L K => a.role = .clock) hs_clock,
      countP_singleton_of_dc
        (p := fun a : AgentState L K => a.role = .clock) ht_clock,
      countP_singleton_of_dc
        (p := fun a : AgentState L K => a.role = .clock) hs_out,
      countP_singleton_of_dc
        (p := fun a : AgentState L K => a.role = .clock) ht_out]
  · have hs_out := Transition_preserves_clock_role_of_phase_ge_1
      (L := L) (K := K) s t hs_phase ht_phase hs_clock
    have hpair :
        Multiset.countP (fun a : AgentState L K => a.role = .clock)
          ({s, t} : Multiset (AgentState L K)) = 1 := by
      rw [show ({s, t} : Multiset (AgentState L K)) =
          ({s} : Multiset _) + {t} by rfl,
        Multiset.countP_add,
        countP_singleton_of_dc
          (p := fun a : AgentState L K => a.role = .clock) hs_clock,
        countP_singleton_of_dc_not
          (p := fun a : AgentState L K => a.role = .clock) ht_clock]
    have hout_one : 1 ≤
        Multiset.countP (fun a : AgentState L K => a.role = .clock)
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) := by
      have hsingle :
          Multiset.countP (fun a : AgentState L K => a.role = .clock)
            ({(Transition L K s t).1} : Multiset (AgentState L K)) = 1 :=
        countP_singleton_of_dc
          (p := fun a : AgentState L K => a.role = .clock) hs_out
      have hle := Multiset.countP_le_of_le
        (p := fun a : AgentState L K => a.role = .clock)
        (show ({(Transition L K s t).1} : Multiset (AgentState L K)) ≤
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) by simp)
      omega
    omega
  · have ht_out := Transition_second_preserves_clock_role_of_phase_ge_1
      (L := L) (K := K) s t hs_phase ht_phase ht_clock
    have hpair :
        Multiset.countP (fun a : AgentState L K => a.role = .clock)
          ({s, t} : Multiset (AgentState L K)) = 1 := by
      rw [show ({s, t} : Multiset (AgentState L K)) =
          ({s} : Multiset _) + {t} by rfl,
        Multiset.countP_add,
        countP_singleton_of_dc_not
          (p := fun a : AgentState L K => a.role = .clock) hs_clock,
        countP_singleton_of_dc
          (p := fun a : AgentState L K => a.role = .clock) ht_clock]
    have hout_one : 1 ≤
        Multiset.countP (fun a : AgentState L K => a.role = .clock)
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) := by
      have hsingle :
          Multiset.countP (fun a : AgentState L K => a.role = .clock)
            ({(Transition L K s t).2} : Multiset (AgentState L K)) = 1 :=
        countP_singleton_of_dc
          (p := fun a : AgentState L K => a.role = .clock) ht_out
      have hle := Multiset.countP_le_of_le
        (p := fun a : AgentState L K => a.role = .clock)
        (show ({(Transition L K s t).2} : Multiset (AgentState L K)) ≤
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) by simp)
      omega
    omega
  · rw [show ({s, t} : Multiset (AgentState L K)) =
        ({s} : Multiset _) + {t} by rfl,
      Multiset.countP_add,
      countP_singleton_of_dc_not
        (p := fun a : AgentState L K => a.role = .clock) hs_clock,
      countP_singleton_of_dc_not
        (p := fun a : AgentState L K => a.role = .clock) ht_clock]
    omega

private lemma StepRel_phase_ge_one
    {c c' : Config (AgentState L K)}
    (hphase : ∀ a ∈ c, 1 ≤ a.phase.val)
    (hstep : (NonuniformMajority L K).StepRel c c') :
    ∀ a ∈ c', 1 ≤ a.phase.val := by
  intro a ha
  rcases hstep with ⟨s, t, happ, hc'⟩
  dsimp at hc'
  subst c'
  rcases Multiset.mem_add.mp ha with ha_old | ha_new
  · exact hphase a (Multiset.mem_of_le
      (Multiset.sub_le_self c ({s, t} : Multiset (AgentState L K))) ha_old)
  · have ha_new' : a = (Transition L K s t).1 ∨
        a = (Transition L K s t).2 := by
      simpa using ha_new
    have hs_phase : 1 ≤ s.phase.val := hphase s (Multiset.mem_of_le happ (by simp))
    have ht_phase : 1 ≤ t.phase.val := hphase t (Multiset.mem_of_le happ (by simp))
    have hmono := Transition_phase_monotone (L := L) (K := K) s t
    rcases ha_new' with rfl | rfl
    · exact le_trans hs_phase hmono.1
    · exact le_trans ht_phase hmono.2

private lemma StepRel_clockCount_ge_two
    {c c' : Config (AgentState L K)}
    (hphase : ∀ a ∈ c, 1 ≤ a.phase.val)
    (hcount : 2 ≤ clockCount (L := L) (K := K) c)
    (hstep : (NonuniformMajority L K).StepRel c c') :
    2 ≤ clockCount (L := L) (K := K) c' := by
  rcases hstep with ⟨s, t, happ, hc'⟩
  dsimp at hc'
  subst c'
  have hs_phase : 1 ≤ s.phase.val := hphase s (Multiset.mem_of_le happ (by simp))
  have ht_phase : 1 ≤ t.phase.val := hphase t (Multiset.mem_of_le happ (by simp))
  have hout_ge := transition_clock_pair_count_le_outputs
    (L := L) (K := K) s t hs_phase ht_phase
  unfold clockCount at hcount ⊢
  change 2 ≤ Multiset.countP (fun a : AgentState L K => a.role = .clock)
    (c - ({s, t} : Multiset (AgentState L K)) +
      ({(Transition L K s t).1, (Transition L K s t).2} :
        Multiset (AgentState L K)))
  rw [Multiset.countP_add,
    Multiset.countP_sub happ (fun a : AgentState L K => a.role = .clock)]
  omega

private lemma StepRel_clockCount_ge_two_any
    {c c' : Config (AgentState L K)}
    (hcount : 2 ≤ clockCount (L := L) (K := K) c)
    (hstep : (NonuniformMajority L K).StepRel c c') :
    2 ≤ clockCount (L := L) (K := K) c' := by
  rcases hstep with ⟨s, t, happ, hc'⟩
  dsimp at hc'
  subst c'
  have hout_ge := transition_clock_pair_count_le_outputs_any
    (L := L) (K := K) s t
  unfold clockCount at hcount ⊢
  change 2 ≤ Multiset.countP (fun a : AgentState L K => a.role = .clock)
    (c - ({s, t} : Multiset (AgentState L K)) +
      ({(Transition L K s t).1, (Transition L K s t).2} :
        Multiset (AgentState L K)))
  rw [Multiset.countP_add,
    Multiset.countP_sub happ (fun a : AgentState L K => a.role = .clock)]
  omega

private lemma reachable_phase_ge_one_and_clockCount_ge_two
    {c c' : Config (AgentState L K)}
    (hphase : ∀ a ∈ c, 1 ≤ a.phase.val)
    (hcount : 2 ≤ clockCount (L := L) (K := K) c)
    (hreach : (NonuniformMajority L K).Reachable c c') :
    (∀ a ∈ c', 1 ≤ a.phase.val) ∧
      2 ≤ clockCount (L := L) (K := K) c' := by
  induction hreach with
  | refl =>
      exact ⟨hphase, hcount⟩
  | tail _ hstep ih =>
      rcases ih with ⟨hphase_mid, hcount_mid⟩
      exact ⟨StepRel_phase_ge_one (L := L) (K := K) hphase_mid hstep,
        StepRel_clockCount_ge_two (L := L) (K := K) hphase_mid hcount_mid hstep⟩

private lemma reachable_clockCount_ge_two_any
    {c c' : Config (AgentState L K)}
    (hcount : 2 ≤ clockCount (L := L) (K := K) c)
    (hreach : (NonuniformMajority L K).Reachable c c') :
    2 ≤ clockCount (L := L) (K := K) c' := by
  induction hreach with
  | refl =>
      exact hcount
  | tail _ hstep ih =>
      exact StepRel_clockCount_ge_two_any (L := L) (K := K) ih hstep

/-- Once the population is past Phase 0, reachability preserves the existence
of two clock agents that form an applicable ordered pair. -/
theorem clock_pair_preserved_by_reachable
    (c c' : Config (AgentState L K)) {i j : AgentState L K}
    (hclocks : Protocol.Applicable c i j ∧ i.role = .clock ∧ j.role = .clock)
    (hphase_ge1 : ∀ a ∈ c, 1 ≤ a.phase.val)
    (hreach : (NonuniformMajority L K).Reachable c c') :
    ∃ i' j', Protocol.Applicable c' i' j' ∧
      i'.role = .clock ∧ j'.role = .clock := by
  have hcount : 2 ≤ clockCount (L := L) (K := K) c :=
    clockCount_ge_two_of_applicable_clocks
      (L := L) (K := K) hclocks.1 hclocks.2.1 hclocks.2.2
  exact exists_applicable_clock_pair_of_clockCount_ge_two (L := L) (K := K)
    (reachable_phase_ge_one_and_clockCount_ge_two
      (L := L) (K := K) hphase_ge1 hcount hreach).2

/-- Clock roles are preserved by every transition, including the Phase-0 clock
counter subroutine.  Therefore an applicable clock-clock pair remains available
after arbitrary reachability from a configuration that already has two clocks. -/
theorem clock_pair_preserved_by_reachable_any
    (c c' : Config (AgentState L K)) {i j : AgentState L K}
    (hclocks : Protocol.Applicable c i j ∧ i.role = .clock ∧ j.role = .clock)
    (hreach : (NonuniformMajority L K).Reachable c c') :
    ∃ i' j', Protocol.Applicable c' i' j' ∧
      i'.role = .clock ∧ j'.role = .clock := by
  have hcount : 2 ≤ clockCount (L := L) (K := K) c :=
    clockCount_ge_two_of_applicable_clocks
      (L := L) (K := K) hclocks.1 hclocks.2.1 hclocks.2.2
  exact exists_applicable_clock_pair_of_clockCount_ge_two (L := L) (K := K)
    (reachable_clockCount_ge_two_any (L := L) (K := K) hcount hreach)

/-- Phase-2 local stability rules out simultaneous minus- and plus-opinions in
any population with at least two agents.  Equivalently, all agents have no
minus opinion or all agents have no plus opinion. -/
theorem phase2LocallyStable_opinion_compatibility
    (c : Config (AgentState L K))
    (hcard : 2 ≤ c.card)
    (hstable : phase2LocallyStable (L := L) (K := K) c) :
    (∀ a ∈ c, hasMinusOne a.opinions = false) ∨
      (∀ a ∈ c, hasPlusOne a.opinions = false) := by
  classical
  by_cases hminus : ∃ a, a ∈ c ∧ hasMinusOne a.opinions = true
  · refine Or.inr ?_
    intro b hb
    by_cases hplus : hasPlusOne b.opinions = true
    · rcases hminus with ⟨a, ha, haminus⟩
      have hcontra :
          hasMinusOne (opinionsUnion a.opinions b.opinions) = true ∧
            hasPlusOne (opinionsUnion a.opinions b.opinions) = true := by
        exact ⟨hasMinusOne_opinionsUnion_left a.opinions b.opinions haminus,
          hasPlusOne_opinionsUnion_right a.opinions b.opinions hplus⟩
      by_cases hab : a = b
      · subst b
        rcases exists_applicable_pair_left_of_mem_card_ge_two
            (L := L) (K := K) ha hcard with ⟨d, happ⟩
        have hcontra' :
            hasMinusOne (opinionsUnion a.opinions d.opinions) = true ∧
              hasPlusOne (opinionsUnion a.opinions d.opinions) = true :=
          ⟨hasMinusOne_opinionsUnion_left a.opinions d.opinions haminus,
            hasPlusOne_opinionsUnion_left a.opinions d.opinions hplus⟩
        exact False.elim ((hstable.2 a d happ) hcontra')
      · exact False.elim ((hstable.2 a b (pair_le_of_mem_ne ha hb hab)) hcontra)
    · cases hp : hasPlusOne b.opinions
      · rfl
      · exact False.elim (hplus hp)
  · refine Or.inl ?_
    intro a ha
    by_cases hma : hasMinusOne a.opinions = true
    · exact False.elim (hminus ⟨a, ha, hma⟩)
    · cases hm : hasMinusOne a.opinions
      · rfl
      · exact False.elim (hma hm)

/-- Phase-9 has the same local opinion-compatibility consequence as Phase 2. -/
theorem phase9LocallyStable_opinion_compatibility
    (c : Config (AgentState L K))
    (hcard : 2 ≤ c.card)
    (hstable : phase9LocallyStable (L := L) (K := K) c) :
    (∀ a ∈ c, hasMinusOne a.opinions = false) ∨
      (∀ a ∈ c, hasPlusOne a.opinions = false) := by
  classical
  by_cases hminus : ∃ a, a ∈ c ∧ hasMinusOne a.opinions = true
  · refine Or.inr ?_
    intro b hb
    by_cases hplus : hasPlusOne b.opinions = true
    · rcases hminus with ⟨a, ha, haminus⟩
      have hcontra :
          hasMinusOne (opinionsUnion a.opinions b.opinions) = true ∧
            hasPlusOne (opinionsUnion a.opinions b.opinions) = true := by
        exact ⟨hasMinusOne_opinionsUnion_left a.opinions b.opinions haminus,
          hasPlusOne_opinionsUnion_right a.opinions b.opinions hplus⟩
      by_cases hab : a = b
      · subst b
        rcases exists_applicable_pair_left_of_mem_card_ge_two
            (L := L) (K := K) ha hcard with ⟨d, happ⟩
        have hcontra' :
            hasMinusOne (opinionsUnion a.opinions d.opinions) = true ∧
              hasPlusOne (opinionsUnion a.opinions d.opinions) = true :=
          ⟨hasMinusOne_opinionsUnion_left a.opinions d.opinions haminus,
            hasPlusOne_opinionsUnion_left a.opinions d.opinions hplus⟩
        exact False.elim ((hstable.2 a d happ) hcontra')
      · exact False.elim ((hstable.2 a b (pair_le_of_mem_ne ha hb hab)) hcontra)
    · cases hp : hasPlusOne b.opinions
      · rfl
      · exact False.elim (hplus hp)
  · refine Or.inl ?_
    intro a ha
    by_cases hma : hasMinusOne a.opinions = true
    · exact False.elim (hminus ⟨a, ha, hma⟩)
    · cases hm : hasMinusOne a.opinions
      · rfl
      · exact False.elim (hma hm)

/-- In populations of size at least two, Phase-4 local stability implies that
no individual agent has the Phase-4 big-bias trigger. -/
theorem phase4LocallyStable_no_bigBias
    (c : Config (AgentState L K))
    (hcard : 2 ≤ c.card)
    (hstable : phase4LocallyStable (L := L) (K := K) c) :
    ∀ a ∈ c, ¬ phase4HasBigBias (L := L) (K := K) a := by
  intro a ha hbig
  rcases exists_applicable_pair_left_of_mem_card_ge_two
      (L := L) (K := K) ha hcard with ⟨b, happ⟩
  have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
  exact (hstable.2 a ha b hb happ) (Or.inl hbig)

private theorem phase2LocallyStable_of_all_A_signs
    (c : Config (AgentState L K))
    (h : ∀ a ∈ c, a.phase.val = 2 ∧ a.output = .A ∧
      hasPlusOne a.opinions = true ∧ hasMinusOne a.opinions = false) :
    phase2LocallyStable (L := L) (K := K) c := by
  constructor
  · intro a ha
    exact (h a ha).1
  · intro a b happ hbad
    have ha : a ∈ c := Multiset.mem_of_le happ (by simp)
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have hminus :
        hasMinusOne (opinionsUnion a.opinions b.opinions) = false :=
      hasMinusOne_opinionsUnion_false_chain a.opinions b.opinions
        (h a ha).2.2.2 (h b hb).2.2.2
    simp [hminus] at hbad

private theorem phase2LocallyStable_of_all_B_signs
    (c : Config (AgentState L K))
    (h : ∀ a ∈ c, a.phase.val = 2 ∧ a.output = .B ∧
      hasMinusOne a.opinions = true ∧ hasPlusOne a.opinions = false) :
    phase2LocallyStable (L := L) (K := K) c := by
  constructor
  · intro a ha
    exact (h a ha).1
  · intro a b happ hbad
    have ha : a ∈ c := Multiset.mem_of_le happ (by simp)
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have hplus :
        hasPlusOne (opinionsUnion a.opinions b.opinions) = false :=
      hasPlusOne_opinionsUnion_false_chain a.opinions b.opinions
        (h a ha).2.2.2 (h b hb).2.2.2
    simp [hplus] at hbad

private theorem phase2LocallyStable_of_all_T_signs
    (c : Config (AgentState L K))
    (h : ∀ a ∈ c, a.phase.val = 2 ∧ a.output = .T ∧
      hasMinusOne a.opinions = false ∧ hasPlusOne a.opinions = false) :
    phase2LocallyStable (L := L) (K := K) c := by
  constructor
  · intro a ha
    exact (h a ha).1
  · intro a b happ hbad
    have ha : a ∈ c := Multiset.mem_of_le happ (by simp)
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have hminus :
        hasMinusOne (opinionsUnion a.opinions b.opinions) = false :=
      hasMinusOne_opinionsUnion_false_chain a.opinions b.opinions
        (h a ha).2.2.1 (h b hb).2.2.1
    have hplus :
        hasPlusOne (opinionsUnion a.opinions b.opinions) = false :=
      hasPlusOne_opinionsUnion_false_chain a.opinions b.opinions
        (h a ha).2.2.2 (h b hb).2.2.2
    simp [hminus, hplus] at hbad

private theorem phase9LocallyStable_of_all_A_signs
    (c : Config (AgentState L K))
    (h : ∀ a ∈ c, a.phase.val = 9 ∧ a.output = .A ∧
      hasPlusOne a.opinions = true ∧ hasMinusOne a.opinions = false) :
    phase9LocallyStable (L := L) (K := K) c := by
  constructor
  · intro a ha
    exact (h a ha).1
  · intro a b happ hbad
    have ha : a ∈ c := Multiset.mem_of_le happ (by simp)
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have hminus :
        hasMinusOne (opinionsUnion a.opinions b.opinions) = false :=
      hasMinusOne_opinionsUnion_false_chain a.opinions b.opinions
        (h a ha).2.2.2 (h b hb).2.2.2
    simp [hminus] at hbad

private theorem phase9LocallyStable_of_all_B_signs
    (c : Config (AgentState L K))
    (h : ∀ a ∈ c, a.phase.val = 9 ∧ a.output = .B ∧
      hasMinusOne a.opinions = true ∧ hasPlusOne a.opinions = false) :
    phase9LocallyStable (L := L) (K := K) c := by
  constructor
  · intro a ha
    exact (h a ha).1
  · intro a b happ hbad
    have ha : a ∈ c := Multiset.mem_of_le happ (by simp)
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have hplus :
        hasPlusOne (opinionsUnion a.opinions b.opinions) = false :=
      hasPlusOne_opinionsUnion_false_chain a.opinions b.opinions
        (h a ha).2.2.2 (h b hb).2.2.2
    simp [hplus] at hbad

private theorem phase9LocallyStable_of_all_T_signs
    (c : Config (AgentState L K))
    (h : ∀ a ∈ c, a.phase.val = 9 ∧ a.output = .T ∧
      hasMinusOne a.opinions = false ∧ hasPlusOne a.opinions = false) :
    phase9LocallyStable (L := L) (K := K) c := by
  constructor
  · intro a ha
    exact (h a ha).1
  · intro a b happ hbad
    have ha : a ∈ c := Multiset.mem_of_le happ (by simp)
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have hminus :
        hasMinusOne (opinionsUnion a.opinions b.opinions) = false :=
      hasMinusOne_opinionsUnion_false_chain a.opinions b.opinions
        (h a ha).2.2.1 (h b hb).2.2.1
    have hplus :
        hasPlusOne (opinionsUnion a.opinions b.opinions) = false :=
      hasPlusOne_opinionsUnion_false_chain a.opinions b.opinions
        (h a ha).2.2.2 (h b hb).2.2.2
    simp [hminus, hplus] at hbad

private lemma phase_eq_two_chain (a : AgentState L K) (h : a.phase.val = 2) :
    a.phase = ⟨2, by decide⟩ :=
  Fin.ext h

private lemma phaseEpidemicUpdate_eq_self_of_phase2_chain
    (s t : AgentState L K)
    (hs_phase : s.phase = ⟨2, by decide⟩)
    (ht_phase : t.phase = ⟨2, by decide⟩) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  unfold phaseEpidemicUpdate
  rw [hs_phase, ht_phase, max_self]
  simp [runInitsBetween_self_api]
  cases s
  cases t
  simp_all

private theorem Transition_phase2_A_from_plus_chain
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hs_plus : hasPlusOne s.opinions = true)
    (hs_minus : hasMinusOne s.opinions = false)
    (ht_minus : hasMinusOne t.opinions = false) :
    ((Transition L K s t).1.phase.val = 2 ∧
      (Transition L K s t).1.output = .A ∧
      hasPlusOne (Transition L K s t).1.opinions = true ∧
      hasMinusOne (Transition L K s t).1.opinions = false) ∧
    ((Transition L K s t).2.phase.val = 2 ∧
      (Transition L K s t).2.output = .A ∧
      hasPlusOne (Transition L K s t).2.opinions = true ∧
      hasMinusOne (Transition L K s t).2.opinions = false) := by
  have hs_phase_eq := phase_eq_two_chain (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_two_chain (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase2_chain
    (L := L) (K := K) s t hs_phase_eq ht_phase_eq
  have hplus_union :
      hasPlusOne (opinionsUnion s.opinions t.opinions) = true :=
    hasPlusOne_opinionsUnion_left s.opinions t.opinions hs_plus
  have hminus_union :
      hasMinusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasMinusOne_opinionsUnion_false_chain s.opinions t.opinions hs_minus ht_minus
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase2Transition,
    hplus_union, hminus_union]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry, hplus_union, hminus_union]

private theorem Transition_phase2_B_from_minus_chain
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hs_minus : hasMinusOne s.opinions = true)
    (hs_plus : hasPlusOne s.opinions = false)
    (ht_plus : hasPlusOne t.opinions = false) :
    ((Transition L K s t).1.phase.val = 2 ∧
      (Transition L K s t).1.output = .B ∧
      hasMinusOne (Transition L K s t).1.opinions = true ∧
      hasPlusOne (Transition L K s t).1.opinions = false) ∧
    ((Transition L K s t).2.phase.val = 2 ∧
      (Transition L K s t).2.output = .B ∧
      hasMinusOne (Transition L K s t).2.opinions = true ∧
      hasPlusOne (Transition L K s t).2.opinions = false) := by
  have hs_phase_eq := phase_eq_two_chain (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_two_chain (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase2_chain
    (L := L) (K := K) s t hs_phase_eq ht_phase_eq
  have hminus_union :
      hasMinusOne (opinionsUnion s.opinions t.opinions) = true :=
    hasMinusOne_opinionsUnion_left s.opinions t.opinions hs_minus
  have hplus_union :
      hasPlusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasPlusOne_opinionsUnion_false_chain s.opinions t.opinions hs_plus ht_plus
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase2Transition,
    hplus_union, hminus_union]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry, hplus_union, hminus_union]

private theorem phase2_output_closure_A_from_plus_chain
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 2)
    (hnoMinus : ∀ a ∈ c, hasMinusOne a.opinions = false)
    (hplus : ∃ a ∈ c, hasPlusOne a.opinions = true)
    (hcard : 2 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = 2 ∧ a.output = .A ∧
        hasPlusOne a.opinions = true ∧ hasMinusOne a.opinions = false) := by
  classical
  rcases hplus with ⟨a, ha, ha_plus⟩
  by_cases ha_out : a.output = .A
  · exact phase2_output_closure_A (L := L) (K := K) c hphase hnoMinus
      ⟨a, ha, ha_out, ha_plus⟩
  · rcases exists_applicable_pair_left_of_mem_card_ge_two
      (L := L) (K := K) ha hcard with ⟨b, happ⟩
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c a b
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have htrans := Transition_phase2_A_from_plus_chain (L := L) (K := K) a b
      (hphase a ha) (hphase b hb) ha_plus (hnoMinus a ha) (hnoMinus b hb)
    have hstep :
        c' =
          c - ({a, b} : Multiset (AgentState L K)) +
            ({(Transition L K a b).1, (Transition L K a b).2} :
              Multiset (AgentState L K)) := by
      unfold c' Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hphase' : ∀ x ∈ c', x.phase.val = 2 := by
      intro x hx
      rw [hstep] at hx
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with hx_old | hx_new
      · exact hphase x (Multiset.mem_of_le
          (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K))) hx_old)
      · have hx_new' :
            x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
          simpa using hx_new
        rcases hx_new' with h_eq1 | h_eq2
        · simpa [h_eq1] using htrans.1.1
        · simpa [h_eq2] using htrans.2.1
    have hnoMinus' : ∀ x ∈ c', hasMinusOne x.opinions = false := by
      intro x hx
      rw [hstep] at hx
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with hx_old | hx_new
      · exact hnoMinus x (Multiset.mem_of_le
          (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K))) hx_old)
      · have hx_new' :
            x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
          simpa using hx_new
        rcases hx_new' with h_eq1 | h_eq2
        · simpa [h_eq1] using htrans.1.2.2.2
        · simpa [h_eq2] using htrans.2.2.2.2
    have hcarrier' :
        ∃ x ∈ c', x.output = .A ∧ hasPlusOne x.opinions = true := by
      refine ⟨(Transition L K a b).1, ?_, htrans.1.2.1, htrans.1.2.2.1⟩
      rw [hstep]
      simp
    rcases phase2_output_closure_A (L := L) (K := K) c'
        hphase' hnoMinus' hcarrier' with ⟨final, hreach, hgood⟩
    exact ⟨final, Relation.ReflTransGen.trans
      (Protocol.reachable_stepOrSelf c a b) hreach, hgood⟩

private theorem phase2_output_closure_B_from_minus_chain
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 2)
    (hnoPlus : ∀ a ∈ c, hasPlusOne a.opinions = false)
    (hminus : ∃ a ∈ c, hasMinusOne a.opinions = true)
    (hcard : 2 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = 2 ∧ a.output = .B ∧
        hasMinusOne a.opinions = true ∧ hasPlusOne a.opinions = false) := by
  classical
  rcases hminus with ⟨a, ha, ha_minus⟩
  by_cases ha_out : a.output = .B
  · exact phase2_output_closure_B (L := L) (K := K) c hphase hnoPlus
      ⟨a, ha, ha_out, ha_minus⟩
  · rcases exists_applicable_pair_left_of_mem_card_ge_two
      (L := L) (K := K) ha hcard with ⟨b, happ⟩
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c a b
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have htrans := Transition_phase2_B_from_minus_chain (L := L) (K := K) a b
      (hphase a ha) (hphase b hb) ha_minus (hnoPlus a ha) (hnoPlus b hb)
    have hstep :
        c' =
          c - ({a, b} : Multiset (AgentState L K)) +
            ({(Transition L K a b).1, (Transition L K a b).2} :
              Multiset (AgentState L K)) := by
      unfold c' Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hphase' : ∀ x ∈ c', x.phase.val = 2 := by
      intro x hx
      rw [hstep] at hx
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with hx_old | hx_new
      · exact hphase x (Multiset.mem_of_le
          (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K))) hx_old)
      · have hx_new' :
            x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
          simpa using hx_new
        rcases hx_new' with h_eq1 | h_eq2
        · simpa [h_eq1] using htrans.1.1
        · simpa [h_eq2] using htrans.2.1
    have hnoPlus' : ∀ x ∈ c', hasPlusOne x.opinions = false := by
      intro x hx
      rw [hstep] at hx
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with hx_old | hx_new
      · exact hnoPlus x (Multiset.mem_of_le
          (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K))) hx_old)
      · have hx_new' :
            x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
          simpa using hx_new
        rcases hx_new' with h_eq1 | h_eq2
        · simpa [h_eq1] using htrans.1.2.2.2
        · simpa [h_eq2] using htrans.2.2.2.2
    have hcarrier' :
        ∃ x ∈ c', x.output = .B ∧ hasMinusOne x.opinions = true := by
      refine ⟨(Transition L K a b).1, ?_, htrans.1.2.1, htrans.1.2.2.1⟩
      rw [hstep]
      simp
    rcases phase2_output_closure_B (L := L) (K := K) c'
        hphase' hnoPlus' hcarrier' with ⟨final, hreach, hgood⟩
    exact ⟨final, Relation.ReflTransGen.trans
      (Protocol.reachable_stepOrSelf c a b) hreach, hgood⟩

theorem phase2LocallyStable_reachable_to_phase2ConsensusEndpoint_of_initialGap_pos
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hcard : 2 ≤ c.card)
    (hgap : 0 < initialGap init)
    (hstable : phase2LocallyStable (L := L) (K := K) c) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      phase2ConsensusEndpoint (L := L) (K := K) init final := by
  classical
  have hsum_eq :
      smallBiasSum c = initialGap init :=
    reachable_smallBiasSum_eq_initialGap_all_phases
      (L := L) (K := K) init c hinit hreach
  have hsum_pos : 0 < smallBiasSum c := by
    rw [hsum_eq]
    exact hgap
  rcases smallBiasSum_pos_implies_exists_positive_smallBias
      (L := L) (K := K) c hsum_pos with
    ⟨a, ha, ha_pos⟩
  have ha_phase : a.phase.val = 2 := hstable.1 a ha
  have ha_plus : hasPlusOne a.opinions = true :=
    (reachable_phase2SignSupport (L := L) (K := K) init c hinit hreach
      a ha ha_phase).1 ha_pos
  have hplus : ∃ a ∈ c, hasPlusOne a.opinions = true := ⟨a, ha, ha_plus⟩
  have hnoMinus : ∀ a ∈ c, hasMinusOne a.opinions = false := by
    rcases phase2LocallyStable_opinion_compatibility
        (L := L) (K := K) c hcard hstable with hnoMinus | hnoPlus
    · exact hnoMinus
    · have hcontr : hasPlusOne a.opinions = false := hnoPlus a ha
      rw [hcontr] at ha_plus
      cases ha_plus
  rcases phase2_output_closure_A_from_plus_chain
      (L := L) (K := K) c hstable.1 hnoMinus hplus hcard with
    ⟨final, hreach_final, hfinal⟩
  refine ⟨final, hreach_final, ?_⟩
  exact phase2ConsensusEndpoint_of_A (L := L) (K := K) init final
    (majorityVerdict_eq_A_of_initialGap_pos (L := L) (K := K) init hgap)
    (phase2LocallyStable_of_all_A_signs (L := L) (K := K) final hfinal)
    (fun a ha => ⟨(hfinal a ha).2.1, (hfinal a ha).2.2.1,
      (hfinal a ha).2.2.2⟩)

theorem phase2LocallyStable_reachable_to_phase2ConsensusEndpoint_of_initialGap_neg
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hcard : 2 ≤ c.card)
    (hgap : initialGap init < 0)
    (hstable : phase2LocallyStable (L := L) (K := K) c) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      phase2ConsensusEndpoint (L := L) (K := K) init final := by
  classical
  have hsum_eq :
      smallBiasSum c = initialGap init :=
    reachable_smallBiasSum_eq_initialGap_all_phases
      (L := L) (K := K) init c hinit hreach
  have hsum_neg : smallBiasSum c < 0 := by
    rw [hsum_eq]
    exact hgap
  rcases smallBiasSum_neg_implies_exists_negative_smallBias
      (L := L) (K := K) c hsum_neg with
    ⟨a, ha, ha_neg⟩
  have ha_phase : a.phase.val = 2 := hstable.1 a ha
  have ha_minus : hasMinusOne a.opinions = true :=
    (reachable_phase2SignSupport (L := L) (K := K) init c hinit hreach
      a ha ha_phase).2 ha_neg
  have hminus : ∃ a ∈ c, hasMinusOne a.opinions = true := ⟨a, ha, ha_minus⟩
  have hnoPlus : ∀ a ∈ c, hasPlusOne a.opinions = false := by
    rcases phase2LocallyStable_opinion_compatibility
        (L := L) (K := K) c hcard hstable with hnoMinus | hnoPlus
    · have hcontr : hasMinusOne a.opinions = false := hnoMinus a ha
      rw [hcontr] at ha_minus
      cases ha_minus
    · exact hnoPlus
  rcases phase2_output_closure_B_from_minus_chain
      (L := L) (K := K) c hstable.1 hnoPlus hminus hcard with
    ⟨final, hreach_final, hfinal⟩
  refine ⟨final, hreach_final, ?_⟩
  exact phase2ConsensusEndpoint_of_B (L := L) (K := K) init final
    (majorityVerdict_eq_B_of_initialGap_neg (L := L) (K := K) init hgap)
    (phase2LocallyStable_of_all_B_signs (L := L) (K := K) final hfinal)
    (fun a ha => ⟨(hfinal a ha).2.1, (hfinal a ha).2.2.1,
      (hfinal a ha).2.2.2⟩)

theorem phase9LocallyStable_reachable_to_phase9ConsensusEndpoint_of_initialGap_pos
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hcard : 2 ≤ c.card)
    (hgap : 0 < initialGap init)
    (hstable : phase9LocallyStable (L := L) (K := K) c) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      phase9ConsensusEndpoint (L := L) (K := K) init final := by
  classical
  have hsum_eq :
      smallBiasSum c = initialGap init :=
    reachable_smallBiasSum_eq_initialGap_all_phases
      (L := L) (K := K) init c hinit hreach
  have hsum_pos : 0 < smallBiasSum c := by
    rw [hsum_eq]
    exact hgap
  rcases smallBiasSum_pos_implies_exists_positive_smallBias
      (L := L) (K := K) c hsum_pos with
    ⟨a, ha, ha_pos⟩
  have ha_phase : a.phase.val = 9 := hstable.1 a ha
  have ha_plus : hasPlusOne a.opinions = true :=
    (reachable_phase9SignSupport (L := L) (K := K) init c hinit hreach
      a ha ha_phase).1 ha_pos
  have hplus : ∃ a ∈ c, hasPlusOne a.opinions = true := ⟨a, ha, ha_plus⟩
  have hnoMinus : ∀ a ∈ c, hasMinusOne a.opinions = false := by
    rcases phase9LocallyStable_opinion_compatibility
        (L := L) (K := K) c hcard hstable with hnoMinus | hnoPlus
    · exact hnoMinus
    · have hcontr : hasPlusOne a.opinions = false := hnoPlus a ha
      rw [hcontr] at ha_plus
      cases ha_plus
  rcases phase9_output_closure_A_from_plus
      (L := L) (K := K) c hstable.1 hnoMinus hplus hcard with
    ⟨final, hreach_final, hfinal⟩
  refine ⟨final, hreach_final, ?_⟩
  exact phase9ConsensusEndpoint_of_A (L := L) (K := K) init final
    (majorityVerdict_eq_A_of_initialGap_pos (L := L) (K := K) init hgap)
    (phase9LocallyStable_of_all_A_signs (L := L) (K := K) final hfinal)
    (fun a ha => ⟨(hfinal a ha).2.1, (hfinal a ha).2.2.1,
      (hfinal a ha).2.2.2⟩)

theorem phase9LocallyStable_reachable_to_phase9ConsensusEndpoint_of_initialGap_neg
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hcard : 2 ≤ c.card)
    (hgap : initialGap init < 0)
    (hstable : phase9LocallyStable (L := L) (K := K) c) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      phase9ConsensusEndpoint (L := L) (K := K) init final := by
  classical
  have hsum_eq :
      smallBiasSum c = initialGap init :=
    reachable_smallBiasSum_eq_initialGap_all_phases
      (L := L) (K := K) init c hinit hreach
  have hsum_neg : smallBiasSum c < 0 := by
    rw [hsum_eq]
    exact hgap
  rcases smallBiasSum_neg_implies_exists_negative_smallBias
      (L := L) (K := K) c hsum_neg with
    ⟨a, ha, ha_neg⟩
  have ha_phase : a.phase.val = 9 := hstable.1 a ha
  have ha_minus : hasMinusOne a.opinions = true :=
    (reachable_phase9SignSupport (L := L) (K := K) init c hinit hreach
      a ha ha_phase).2 ha_neg
  have hminus : ∃ a ∈ c, hasMinusOne a.opinions = true := ⟨a, ha, ha_minus⟩
  have hnoPlus : ∀ a ∈ c, hasPlusOne a.opinions = false := by
    rcases phase9LocallyStable_opinion_compatibility
        (L := L) (K := K) c hcard hstable with hnoMinus | hnoPlus
    · have hcontr : hasMinusOne a.opinions = false := hnoMinus a ha
      rw [hcontr] at ha_minus
      cases ha_minus
    · exact hnoPlus
  rcases phase9_output_closure_B_from_minus
      (L := L) (K := K) c hstable.1 hnoPlus hminus hcard with
    ⟨final, hreach_final, hfinal⟩
  refine ⟨final, hreach_final, ?_⟩
  exact phase9ConsensusEndpoint_of_B (L := L) (K := K) init final
    (majorityVerdict_eq_B_of_initialGap_neg (L := L) (K := K) init hgap)
    (phase9LocallyStable_of_all_B_signs (L := L) (K := K) final hfinal)
    (fun a ha => ⟨(hfinal a ha).2.1, (hfinal a ha).2.2.1,
      (hfinal a ha).2.2.2⟩)

private theorem smallBiasSum_nonneg_of_no_negative
    (c : Config (AgentState L K))
    (hnone : ∀ a ∈ c, ¬ a.smallBias.val < 3) :
    0 ≤ smallBiasSum c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [smallBiasSum]
  | cons a c ih =>
      have ha_nonneg : 0 ≤ AgentState.smallBiasInt a := by
        unfold AgentState.smallBiasInt
        have ha := hnone a (Multiset.mem_cons_self a c)
        omega
      have hc_nonneg : 0 ≤ (c.map AgentState.smallBiasInt).sum := by
        simpa [smallBiasSum] using
          ih (by
            intro b hb hneg
            exact hnone b (Multiset.mem_cons_of_mem hb) hneg)
      simp [smallBiasSum]
      omega

private theorem smallBiasSum_nonpos_of_no_positive
    (c : Config (AgentState L K))
    (hnone : ∀ a ∈ c, ¬ 3 < a.smallBias.val) :
    smallBiasSum c ≤ 0 := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [smallBiasSum]
  | cons a c ih =>
      have ha_nonpos : AgentState.smallBiasInt a ≤ 0 := by
        unfold AgentState.smallBiasInt
        have ha := hnone a (Multiset.mem_cons_self a c)
        omega
      have hc_nonpos : (c.map AgentState.smallBiasInt).sum ≤ 0 := by
        simpa [smallBiasSum] using
          ih (by
            intro b hb hpos
            exact hnone b (Multiset.mem_cons_of_mem hb) hpos)
      simp [smallBiasSum]
      omega

private theorem smallBiasSum_pos_of_exists_positive_no_negative
    (c : Config (AgentState L K))
    (hpos : ∃ a ∈ c, 3 < a.smallBias.val)
    (hnone : ∀ a ∈ c, ¬ a.smallBias.val < 3) :
    0 < smallBiasSum c := by
  induction c using Multiset.induction_on with
  | empty =>
      rcases hpos with ⟨a, ha, _⟩
      simpa using ha
  | cons a c ih =>
      rcases hpos with ⟨b, hb, hbpos⟩
      have ha_nonneg : 0 ≤ AgentState.smallBiasInt a := by
        unfold AgentState.smallBiasInt
        have ha := hnone a (Multiset.mem_cons_self a c)
        omega
      by_cases hba : b = a
      · subst b
        have ha_pos : 0 < AgentState.smallBiasInt a := by
          unfold AgentState.smallBiasInt
          omega
        have hc_nonneg : 0 ≤ (c.map AgentState.smallBiasInt).sum := by
          simpa [smallBiasSum] using
            smallBiasSum_nonneg_of_no_negative
              (L := L) (K := K) c
              (by
                intro x hx hneg
                exact hnone x (Multiset.mem_cons_of_mem hx) hneg)
        simp [smallBiasSum]
        omega
      · have hb_tail : b ∈ c := by
          have hb_or : b = a ∨ b ∈ c := by simpa using hb
          rcases hb_or with h | h
          · exact False.elim (hba h)
          · exact h
        have hc_pos : 0 < (c.map AgentState.smallBiasInt).sum := by
          simpa [smallBiasSum] using
            ih ⟨b, hb_tail, hbpos⟩
              (by
                intro x hx hneg
                exact hnone x (Multiset.mem_cons_of_mem hx) hneg)
        simp [smallBiasSum]
        omega

private theorem smallBiasSum_neg_of_exists_negative_no_positive
    (c : Config (AgentState L K))
    (hneg : ∃ a ∈ c, a.smallBias.val < 3)
    (hnone : ∀ a ∈ c, ¬ 3 < a.smallBias.val) :
    smallBiasSum c < 0 := by
  induction c using Multiset.induction_on with
  | empty =>
      rcases hneg with ⟨a, ha, _⟩
      simpa using ha
  | cons a c ih =>
      rcases hneg with ⟨b, hb, hbneg⟩
      have ha_nonpos : AgentState.smallBiasInt a ≤ 0 := by
        unfold AgentState.smallBiasInt
        have ha := hnone a (Multiset.mem_cons_self a c)
        omega
      by_cases hba : b = a
      · subst b
        have ha_neg : AgentState.smallBiasInt a < 0 := by
          unfold AgentState.smallBiasInt
          omega
        have hc_nonpos : (c.map AgentState.smallBiasInt).sum ≤ 0 := by
          simpa [smallBiasSum] using
            smallBiasSum_nonpos_of_no_positive
              (L := L) (K := K) c
              (by
                intro x hx hpos
                exact hnone x (Multiset.mem_cons_of_mem hx) hpos)
        simp [smallBiasSum]
        omega
      · have hb_tail : b ∈ c := by
          have hb_or : b = a ∨ b ∈ c := by simpa using hb
          rcases hb_or with h | h
          · exact False.elim (hba h)
          · exact h
        have hc_neg : (c.map AgentState.smallBiasInt).sum < 0 := by
          simpa [smallBiasSum] using
            ih ⟨b, hb_tail, hbneg⟩
              (by
                intro x hx hpos
                exact hnone x (Multiset.mem_cons_of_mem hx) hpos)
        simp [smallBiasSum]
        omega

private theorem phase2LocallyStable_zero_all_smallBias_three
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hcard : 2 ≤ c.card)
    (hzero : initialGap init = 0)
    (hstable : phase2LocallyStable (L := L) (K := K) c) :
    ∀ a ∈ c, a.smallBias.val = 3 := by
  classical
  have hsum_eq :
      smallBiasSum c = initialGap init :=
    reachable_smallBiasSum_eq_initialGap_all_phases
      (L := L) (K := K) init c hinit hreach
  have hsum_zero : smallBiasSum c = 0 := by
    rw [hsum_eq, hzero]
  have hsupport :=
    reachable_phase2SignSupport (L := L) (K := K) init c hinit hreach
  rcases phase2LocallyStable_opinion_compatibility
      (L := L) (K := K) c hcard hstable with hnoMinus | hnoPlus
  · have hnoNegSmall : ∀ a ∈ c, ¬ a.smallBias.val < 3 := by
      intro a ha hneg
      have hphase : a.phase.val = 2 := hstable.1 a ha
      have hminus : hasMinusOne a.opinions = true :=
        (hsupport a ha hphase).2 hneg
      rw [hnoMinus a ha] at hminus
      cases hminus
    have hnoPosSmall : ∀ a ∈ c, ¬ 3 < a.smallBias.val := by
      intro a ha hpos
      have hsum_pos : 0 < smallBiasSum c :=
        smallBiasSum_pos_of_exists_positive_no_negative
          (L := L) (K := K) c ⟨a, ha, hpos⟩ hnoNegSmall
      omega
    intro a ha
    have hnot_neg := hnoNegSmall a ha
    have hnot_pos := hnoPosSmall a ha
    omega
  · have hnoPosSmall : ∀ a ∈ c, ¬ 3 < a.smallBias.val := by
      intro a ha hpos
      have hphase : a.phase.val = 2 := hstable.1 a ha
      have hplus : hasPlusOne a.opinions = true :=
        (hsupport a ha hphase).1 hpos
      rw [hnoPlus a ha] at hplus
      cases hplus
    have hnoNegSmall : ∀ a ∈ c, ¬ a.smallBias.val < 3 := by
      intro a ha hneg
      have hsum_neg : smallBiasSum c < 0 :=
        smallBiasSum_neg_of_exists_negative_no_positive
          (L := L) (K := K) c ⟨a, ha, hneg⟩ hnoPosSmall
      omega
    intro a ha
    have hnot_neg := hnoNegSmall a ha
    have hnot_pos := hnoPosSmall a ha
    omega

private theorem phase9LocallyStable_zero_all_smallBias_three
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hcard : 2 ≤ c.card)
    (hzero : initialGap init = 0)
    (hstable : phase9LocallyStable (L := L) (K := K) c) :
    ∀ a ∈ c, a.smallBias.val = 3 := by
  classical
  have hsum_eq :
      smallBiasSum c = initialGap init :=
    reachable_smallBiasSum_eq_initialGap_all_phases
      (L := L) (K := K) init c hinit hreach
  have hsum_zero : smallBiasSum c = 0 := by
    rw [hsum_eq, hzero]
  have hsupport :=
    reachable_phase9SignSupport (L := L) (K := K) init c hinit hreach
  rcases phase9LocallyStable_opinion_compatibility
      (L := L) (K := K) c hcard hstable with hnoMinus | hnoPlus
  · have hnoNegSmall : ∀ a ∈ c, ¬ a.smallBias.val < 3 := by
      intro a ha hneg
      have hphase : a.phase.val = 9 := hstable.1 a ha
      have hminus : hasMinusOne a.opinions = true :=
        (hsupport a ha hphase).2 hneg
      rw [hnoMinus a ha] at hminus
      cases hminus
    have hnoPosSmall : ∀ a ∈ c, ¬ 3 < a.smallBias.val := by
      intro a ha hpos
      have hsum_pos : 0 < smallBiasSum c :=
        smallBiasSum_pos_of_exists_positive_no_negative
          (L := L) (K := K) c ⟨a, ha, hpos⟩ hnoNegSmall
      omega
    intro a ha
    have hnot_neg := hnoNegSmall a ha
    have hnot_pos := hnoPosSmall a ha
    omega
  · have hnoPosSmall : ∀ a ∈ c, ¬ 3 < a.smallBias.val := by
      intro a ha hpos
      have hphase : a.phase.val = 9 := hstable.1 a ha
      have hplus : hasPlusOne a.opinions = true :=
        (hsupport a ha hphase).1 hpos
      rw [hnoPlus a ha] at hplus
      cases hplus
    have hnoNegSmall : ∀ a ∈ c, ¬ a.smallBias.val < 3 := by
      intro a ha hneg
      have hsum_neg : smallBiasSum c < 0 :=
        smallBiasSum_neg_of_exists_negative_no_positive
          (L := L) (K := K) c ⟨a, ha, hneg⟩ hnoPosSmall
      omega
    intro a ha
    have hnot_neg := hnoNegSmall a ha
    have hnot_pos := hnoPosSmall a ha
    omega

theorem phase2LocallyStable_reachable_to_phase2ConsensusEndpoint_of_initialGap_zero
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hcard : 2 ≤ c.card)
    (hgap : initialGap init = 0)
    (hstable : phase2LocallyStable (L := L) (K := K) c) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      phase2ConsensusEndpoint (L := L) (K := K) init final := by
  classical
  have hsmall : ∀ a ∈ c, a.smallBias.val = 3 :=
    phase2LocallyStable_zero_all_smallBias_three
      (L := L) (K := K) init c hinit hreach hcard hgap hstable
  have hneutral :=
    reachable_phase2_neutral_opinions_of_all_neutral
      (L := L) (K := K) init c hinit hreach
      (fun a ha => by
        have hphase := hstable.1 a ha
        omega)
      (fun a ha _ => hsmall a ha)
  have hop : ∀ a ∈ c, a.opinions = phase2OpinionT := by
    intro a ha
    exact hneutral a ha (hstable.1 a ha)
  rcases phase2_output_closure_T
      (L := L) (K := K) c hstable.1 hop hcard with
    ⟨final, hreach_final, hfinal⟩
  refine ⟨final, hreach_final, ?_⟩
  exact phase2ConsensusEndpoint_of_T (L := L) (K := K) init final
    (majorityVerdict_eq_T_of_initialGap_zero (L := L) (K := K) init hgap)
    (phase2LocallyStable_of_all_T_signs (L := L) (K := K) final hfinal)
    (fun a ha => ⟨(hfinal a ha).2.1, (hfinal a ha).2.2.1,
      (hfinal a ha).2.2.2⟩)

theorem phase9LocallyStable_reachable_to_phase9ConsensusEndpoint_of_initialGap_zero
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hcard : 2 ≤ c.card)
    (hgap : initialGap init = 0)
    (hstable : phase9LocallyStable (L := L) (K := K) c) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      phase9ConsensusEndpoint (L := L) (K := K) init final := by
  classical
  have hsmall : ∀ a ∈ c, a.smallBias.val = 3 :=
    phase9LocallyStable_zero_all_smallBias_three
      (L := L) (K := K) init c hinit hreach hcard hgap hstable
  have hneutral :=
    reachable_phase9_neutral_opinions_of_all_neutral
      (L := L) (K := K) init c hinit hreach
      (fun a ha => by
        have hphase := hstable.1 a ha
        omega)
      (fun a ha _ => hsmall a ha)
  have hop : ∀ a ∈ c, a.opinions = phase2OpinionT := by
    intro a ha
    exact hneutral a ha (hstable.1 a ha)
  rcases phase9_output_closure_T
      (L := L) (K := K) c hstable.1 hop hcard with
    ⟨final, hreach_final, hfinal⟩
  refine ⟨final, hreach_final, ?_⟩
  exact phase9ConsensusEndpoint_of_T (L := L) (K := K) init final
    (majorityVerdict_eq_T_of_initialGap_zero (L := L) (K := K) init hgap)
    (phase9LocallyStable_of_all_T_signs (L := L) (K := K) final hfinal)
    (fun a ha => ⟨(hfinal a ha).2.1, (hfinal a ha).2.2.1,
      (hfinal a ha).2.2.2⟩)

theorem phase2LocallyStable_to_phase2ConsensusEndpoint_of_unanimous_A
    (init c : Config (AgentState L K))
    (hstable : phase2LocallyStable (L := L) (K := K) c)
    (hmajor : majorityVerdict init = outputTripleOfOutput .A)
    (hunanim : ∀ a ∈ c, a.opinions = phase2OpinionA ∧ a.output = .A) :
    phase2ConsensusEndpoint (L := L) (K := K) init c :=
  phase2ConsensusEndpoint_of_A (L := L) (K := K) init c hmajor hstable
    (fun a ha => by
      rcases hunanim a ha with ⟨hop, hout⟩
      exact ⟨hout, by simp [hop, phase2OpinionA, hasPlusOne],
        by simp [hop, phase2OpinionA, hasMinusOne]⟩)

theorem phase2LocallyStable_to_phase2ConsensusEndpoint_of_unanimous_B
    (init c : Config (AgentState L K))
    (hstable : phase2LocallyStable (L := L) (K := K) c)
    (hmajor : majorityVerdict init = outputTripleOfOutput .B)
    (hunanim : ∀ a ∈ c, a.opinions = phase2OpinionB ∧ a.output = .B) :
    phase2ConsensusEndpoint (L := L) (K := K) init c :=
  phase2ConsensusEndpoint_of_B (L := L) (K := K) init c hmajor hstable
    (fun a ha => by
      rcases hunanim a ha with ⟨hop, hout⟩
      exact ⟨hout, by simp [hop, phase2OpinionB, hasMinusOne],
        by simp [hop, phase2OpinionB, hasPlusOne]⟩)

theorem phase2LocallyStable_to_phase2ConsensusEndpoint_of_unanimous_T
    (init c : Config (AgentState L K))
    (hstable : phase2LocallyStable (L := L) (K := K) c)
    (hmajor : majorityVerdict init = outputTripleOfOutput .T)
    (hunanim : ∀ a ∈ c, a.opinions = phase2OpinionT ∧ a.output = .T) :
    phase2ConsensusEndpoint (L := L) (K := K) init c :=
  phase2ConsensusEndpoint_of_T (L := L) (K := K) init c hmajor hstable
    (fun a ha => by
      rcases hunanim a ha with ⟨hop, hout⟩
      exact ⟨hout, by simp [hop, phase2OpinionT, hasMinusOne],
        by simp [hop, phase2OpinionT, hasPlusOne]⟩)

theorem phase9LocallyStable_to_phase9ConsensusEndpoint_of_unanimous_A
    (init c : Config (AgentState L K))
    (hstable : phase9LocallyStable (L := L) (K := K) c)
    (hmajor : majorityVerdict init = outputTripleOfOutput .A)
    (hunanim : ∀ a ∈ c, a.opinions = phase2OpinionA ∧ a.output = .A) :
    phase9ConsensusEndpoint (L := L) (K := K) init c :=
  phase9ConsensusEndpoint_of_A (L := L) (K := K) init c hmajor hstable
    (fun a ha => by
      rcases hunanim a ha with ⟨hop, hout⟩
      exact ⟨hout, by simp [hop, phase2OpinionA, hasPlusOne],
        by simp [hop, phase2OpinionA, hasMinusOne]⟩)

theorem phase9LocallyStable_to_phase9ConsensusEndpoint_of_unanimous_B
    (init c : Config (AgentState L K))
    (hstable : phase9LocallyStable (L := L) (K := K) c)
    (hmajor : majorityVerdict init = outputTripleOfOutput .B)
    (hunanim : ∀ a ∈ c, a.opinions = phase2OpinionB ∧ a.output = .B) :
    phase9ConsensusEndpoint (L := L) (K := K) init c :=
  phase9ConsensusEndpoint_of_B (L := L) (K := K) init c hmajor hstable
    (fun a ha => by
      rcases hunanim a ha with ⟨hop, hout⟩
      exact ⟨hout, by simp [hop, phase2OpinionB, hasMinusOne],
        by simp [hop, phase2OpinionB, hasPlusOne]⟩)

theorem phase9LocallyStable_to_phase9ConsensusEndpoint_of_unanimous_T
    (init c : Config (AgentState L K))
    (hstable : phase9LocallyStable (L := L) (K := K) c)
    (hmajor : majorityVerdict init = outputTripleOfOutput .T)
    (hunanim : ∀ a ∈ c, a.opinions = phase2OpinionT ∧ a.output = .T) :
    phase9ConsensusEndpoint (L := L) (K := K) init c :=
  phase9ConsensusEndpoint_of_T (L := L) (K := K) init c hmajor hstable
    (fun a ha => by
      rcases hunanim a ha with ⟨hop, hout⟩
      exact ⟨hout, by simp [hop, phase2OpinionT, hasMinusOne],
        by simp [hop, phase2OpinionT, hasPlusOne]⟩)

theorem phase4LocallyStable_to_phase4TieEndpoint_of_outputs
    (init c : Config (AgentState L K))
    (hcard : 2 ≤ c.card)
    (hstable : phase4LocallyStable (L := L) (K := K) c)
    (hmajor : majorityVerdict init = outputTripleOfOutput .T)
    (hout : ∀ a ∈ c, a.output = .T) :
    phase4TieEndpoint (L := L) (K := K) init c := by
  refine phase4TieEndpoint_of_data (L := L) (K := K) init c hmajor ?_
  intro a ha
  exact ⟨hstable.1 a ha, hout a ha,
      (no_phase4HasBigBias_iff (L := L) (K := K) a).mp
      (phase4LocallyStable_no_bigBias (L := L) (K := K) c hcard hstable a ha)⟩

private theorem dyadicBiasSum_map_phaseInit3_eq_smallBiasSum_of_agentwise
    (c : Config (AgentState L K))
    (hagent : ∀ a ∈ c,
      Bias.toRat (phaseInit L K ⟨3, by decide⟩ a).bias =
        (AgentState.smallBiasInt a : ℚ)) :
    dyadicBiasSum (c.map (phaseInit L K ⟨3, by decide⟩)) =
      (smallBiasSum c : ℚ) := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [dyadicBiasSum, smallBiasSum]
  | cons a c ih =>
      have ha := hagent a (Multiset.mem_cons_self a c)
      have htail :
          ∀ x ∈ c,
            Bias.toRat (phaseInit L K ⟨3, by decide⟩ x).bias =
              (AgentState.smallBiasInt x : ℚ) := by
        intro x hx
        exact hagent x (Multiset.mem_cons_of_mem hx)
      calc
        dyadicBiasSum ((a ::ₘ c).map (phaseInit L K ⟨3, by decide⟩))
            = Bias.toRat (phaseInit L K ⟨3, by decide⟩ a).bias +
                dyadicBiasSum (c.map (phaseInit L K ⟨3, by decide⟩)) := by
                simp [dyadicBiasSum]
        _ = (AgentState.smallBiasInt a : ℚ) + (smallBiasSum c : ℚ) := by
                rw [ha, ih htail]
        _ = (smallBiasSum (a ::ₘ c) : ℚ) := by
                simp [smallBiasSum]

/-- Phase-3 initialization converts the conserved integer small-bias mass into
the rational dyadic mass used by the split/cancel dynamics.  The non-main
roles contribute zero because the reachable carrier invariant fixes their
`smallBias` field at the neutral value. -/
theorem phaseInit3_dyadicBiasSum_eq_smallBiasSum
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase2 : ∀ a ∈ c, a.phase.val = 2) :
    dyadicBiasSum (c.map (phaseInit L K ⟨3, by decide⟩)) =
      (smallBiasSum c : ℚ) := by
  have hnoerror : ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
    intro a ha
    exact reachable_phase2_smallBias_noerror (L := L) (K := K)
      init c hinit hreach a ha (hphase2 a ha)
  refine dyadicBiasSum_map_phaseInit3_eq_smallBiasSum_of_agentwise
    (L := L) (K := K) c ?_
  intro a ha
  have hroles := post_phase_zero_role_partition (L := L) (K := K)
    init c hinit hreach (by
      intro x hx
      have := hphase2 x hx
      omega)
  have hcarrier := reachable_nonMain_smallBias_zero (L := L) (K := K)
    init c hinit hreach
  have hsmall_cases : a.smallBias.val = 2 ∨
      a.smallBias.val = 3 ∨ a.smallBias.val = 4 := by
    have hmem := hnoerror a ha
    simp at hmem
    omega
  rcases hroles a ha with hmain | hrest
  · rcases hsmall_cases with h2 | h34
    · simp [phaseInit, AgentState.smallBiasInt, Bias.toRat, hmain, h2]
    · rcases h34 with h3 | h4
      · simp [phaseInit, AgentState.smallBiasInt, Bias.toRat, hmain, h3]
      · simp [phaseInit, AgentState.smallBiasInt, Bias.toRat, hmain, h4]
  · rcases hrest with hreserve | hrest
    · have hsmall : a.smallBias.val = 3 := hcarrier a ha (Or.inl hreserve)
      simp [phaseInit, AgentState.smallBiasInt, Bias.toRat, hreserve, hsmall]
    · rcases hrest with hclock | hphase10
      · have hsmall : a.smallBias.val = 3 := hcarrier a ha (Or.inr hclock)
        simp [phaseInit, AgentState.smallBiasInt, Bias.toRat, hclock, hsmall]
      · have hphase := hphase2 a ha
        omega

/-- In a nontrivial locally stable Phase-4 configuration every dyadic exponent
is at least `L`; otherwise that agent would provide a Phase-4 big-bias trigger
with any interaction partner. -/
theorem phase4LocallyStable_all_exponents_ge_L
    (c : Config (AgentState L K))
    (hcard : 2 ≤ c.card)
    (hstable : phase4LocallyStable (L := L) (K := K) c) :
    ∀ a ∈ c, match a.bias with
      | .dyadic _ i => L ≤ i.val
      | .zero => True := by
  intro a ha
  have hnot :
      ¬ phase4HasBigBias (L := L) (K := K) a :=
    phase4LocallyStable_no_bigBias (L := L) (K := K) c hcard hstable a ha
  cases hbias : a.bias with
  | zero =>
      trivial
  | dyadic sgn i =>
      have hge_or := (no_phase4HasBigBias_iff (L := L) (K := K) a).mp hnot sgn i hbias
      omega

private lemma Bias_abs_toRat_le_inv_pow_of_exponent_ge
    (b : Bias L)
    (h : match b with | .dyadic _ i => L ≤ i.val | .zero => True) :
    |Bias.toRat b| ≤ (1 : ℚ) / (2 ^ L) := by
  cases b with
  | zero =>
      have hpos : (0 : ℚ) ≤ (1 : ℚ) / (2 ^ L) := by positivity
      simpa [Bias.toRat] using hpos
  | dyadic sgn i =>
    have hpow : (2 : ℚ) ^ L ≤ (2 : ℚ) ^ (i : ℕ) := by
      have hpowNat : 2 ^ L ≤ 2 ^ (i : ℕ) :=
        Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h
      exact_mod_cast hpowNat
    have hposL : 0 < (2 : ℚ) ^ L := pow_pos (by norm_num) _
    have hposi : 0 < (2 : ℚ) ^ (i : ℕ) := pow_pos (by norm_num) _
    have hle : (1 : ℚ) / (2 ^ (i : ℕ)) ≤ (1 : ℚ) / (2 ^ L) := by
      rw [one_div, one_div]
      exact (inv_le_inv₀ hposi hposL).2 hpow
    cases sgn
    · calc
        |Bias.toRat (Bias.dyadic Sign.pos i)| =
            (1 : ℚ) / (2 ^ (i : ℕ)) := by
              rw [Bias.toRat, abs_of_nonneg]
              positivity
        _ ≤ (1 : ℚ) / (2 ^ L) := hle
    · calc
        |Bias.toRat (Bias.dyadic Sign.neg i)| =
            (1 : ℚ) / (2 ^ (i : ℕ)) := by
              have hnonpos : (-1 : ℚ) / (2 ^ (i : ℕ)) ≤ 0 :=
                div_nonpos_of_nonpos_of_nonneg (by norm_num) (le_of_lt hposi)
              have habs : |(-1 : ℚ) / (2 ^ (i : ℕ))| =
                  (1 : ℚ) / (2 ^ (i : ℕ)) := by
                rw [abs_of_nonpos hnonpos]
                ring
              simpa [Bias.toRat] using habs
        _ ≤ (1 : ℚ) / (2 ^ L) := hle

private lemma abs_dyadicBiasSum_le_card_div_pow
    (c : Config (AgentState L K))
    (hexp : ∀ a ∈ c, match a.bias with | .dyadic _ i => L ≤ i.val | .zero => True) :
    |dyadicBiasSum c| ≤ (c.card : ℚ) / (2 ^ L) := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [dyadicBiasSum]
  | cons a c ih =>
      have ha : |Bias.toRat a.bias| ≤ (1 : ℚ) / (2 ^ L) :=
        Bias_abs_toRat_le_inv_pow_of_exponent_ge (L := L) a.bias
          (hexp a (Multiset.mem_cons_self a c))
      have htail_exp :
          ∀ x ∈ c, match x.bias with | .dyadic _ i => L ≤ i.val | .zero => True := by
        intro x hx
        exact hexp x (Multiset.mem_cons_of_mem hx)
      have htail := ih htail_exp
      have habs :
          |Bias.toRat a.bias + dyadicBiasSum c| ≤
            |Bias.toRat a.bias| + |dyadicBiasSum c| :=
        abs_add_le _ _
      calc
        |dyadicBiasSum (a ::ₘ c)|
            = |Bias.toRat a.bias + dyadicBiasSum c| := by
                simp [dyadicBiasSum]
        _ ≤ |Bias.toRat a.bias| + |dyadicBiasSum c| := habs
        _ ≤ (1 : ℚ) / (2 ^ L) + (c.card : ℚ) / (2 ^ L) := by
                gcongr
        _ = ((a ::ₘ c).card : ℚ) / (2 ^ L) := by
                rw [Multiset.card_cons]
                norm_num [Nat.cast_add]
                ring

theorem dyadicBiasSum_lt_one_of_exponents_ge_L
    (c : Config (AgentState L K))
    (hexp : ∀ a ∈ c, match a.bias with | .dyadic _ i => L ≤ i.val | .zero => True)
    (hcard : c.card < 2 ^ L) :
    |dyadicBiasSum c| < 1 := by
  have hbound := abs_dyadicBiasSum_le_card_div_pow (L := L) (K := K) c hexp
  have hpos : (0 : ℚ) < (2 : ℚ) ^ L := pow_pos (by norm_num) _
  have hdiv : (c.card : ℚ) / (2 ^ L) < 1 := by
    rw [div_lt_one hpos]
    exact_mod_cast hcard
  exact lt_of_le_of_lt hbound hdiv

/-- Helper: once an agent reaches phase 10, the `runInitsBetween` fold leaves
phase 10 unchanged. Each `phaseInit` is phase non-decreasing, so applying it
to a phase-10 agent keeps phase ≥ 10; with phase ≤ 10 from `Fin 11`, phase = 10. -/
private lemma fold_phaseInit_preserves_ten
    (lst : List ℕ) (a : AgentState L K) (ha : a.phase.val = 10) :
    (lst.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
      a).phase.val = 10 := by
  induction lst generalizing a with
  | nil => exact ha
  | cons k l ih =>
    simp only [List.foldl_cons]
    apply ih
    by_cases hk : k < 11
    · simp only [hk, dite_true]
      have h_nondec := phaseInit_phase_nondec (L := L) (K := K) ⟨k, hk⟩ a
      have h_le : (phaseInit L K ⟨k, hk⟩ a).phase.val ≤ 10 := by
        have := (phaseInit L K ⟨k, hk⟩ a).phase.2; omega
      omega
    · simp only [hk, dite_false]
      exact ha

/-- Helper: `runInitsBetween 0 target` applied to an MCR agent (with phase set
to `target` ≥ 1, ≤ 10) yields phase 10. The first iteration applies
`phaseInit(1)` which on MCR triggers `enterPhase10` (phase → 10); subsequent
iterations preserve phase 10 via `fold_phaseInit_preserves_ten`. -/
private lemma runInitsBetween_mcr_zero_target_phase_ten
    (a : AgentState L K) (target : ℕ)
    (ha_role : a.role = .mcr)
    (htarget_ge1 : 1 ≤ target) (htarget_le10 : target ≤ 10) :
    (runInitsBetween L K 0 target
      ({ a with phase := ⟨target, by omega⟩ } : AgentState L K)).phase.val = 10 := by
  unfold runInitsBetween
  -- Show the filtered list decomposes as 1 :: <rest>, since for target ≥ 1
  -- and oldP = 0, k=1 passes the filter and is the smallest such k.
  have h_filter_decompose :
      (List.range 11).filter (fun k => decide (0 < k ∧ k ≤ target)) =
      1 :: ((List.range 11).filter (fun k => decide (1 < k ∧ k ≤ target))) := by
    interval_cases target <;> decide
  rw [h_filter_decompose]
  simp only [List.foldl_cons, show (1 : ℕ) < 11 from by decide, dite_true]
  -- After phaseInit(1) on MCR agent, phase = 10
  have h_init1 :
      (phaseInit L K ⟨1, by decide⟩
        ({ a with phase := ⟨target, by omega⟩ } : AgentState L K)).phase.val = 10 := by
    simp [phaseInit, ha_role, enterPhase10, phase10]
  -- Subsequent fold iterations preserve phase 10
  exact fold_phaseInit_preserves_ten _ _ h_init1

/-- Reachability invariant: `prePhase4MassSum = (initialGap : ℚ)` for
configs where all phases are ≤ 4. Uses backward phase bound + pair
preservation. -/
theorem reachable_prePhase4MassSum_eq_initialGap_of_phase_le_four
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase : ∀ a ∈ c, a.phase.val ≤ 4) :
    prePhase4MassSum c = (initialGap init : ℚ) := by
  induction hreach with
  | refl =>
      exact prePhase4MassSum_validInitial_eq_initialGap (L := L) (K := K) init hinit
  | tail hprev hstep ih =>
      rename_i b c_next
      have hphase_prev :=
        StepRel_phase_le_of_next_phase_le_four (L := L) (K := K) _ _ hstep hphase
      have hprev_sum := ih hphase_prev
      rcases hstep with ⟨r₁, r₂, happ, hc'⟩
      dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
      have hr₁_mem : r₁ ∈ b := Multiset.mem_of_le happ (by simp)
      have hr₂_mem : r₂ ∈ b := Multiset.mem_of_le happ (by simp)
      have hout1 : (Transition L K r₁ r₂).1.phase.val ≤ 4 := by
        apply hphase
        rw [hc']; exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_self _ _))
      have hout2 : (Transition L K r₁ r₂).2.phase.val ≤ 4 := by
        apply hphase
        rw [hc']; exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_of_mem (by simp)))
      -- Reachability invariants needed for the pair lemma
      have hwf := reachable_preserves_well_formed_agents
        (L := L) (K := K) init _ hinit hprev
      have hcarrier_inv := reachable_nonMainCarrierSmallBiasZeroAgent
        (L := L) (K := K) init _ hinit hprev
      have hnoerr_inv := reachable_phase_ge2_smallBias_noerror_of_phases_le_four
        (L := L) (K := K) init _ hinit hprev hphase_prev
      -- MCR ⇒ phase 0 (from role_phase_invariant + phase ≤ 4)
      have hr1_mcr_imp_phase0 : r₁.role = .mcr → r₁.phase.val = 0 := by
        intro h
        rcases (hwf r₁ hr₁_mem).1 (Or.inl h) with h0 | h10
        · exact h0
        · have := hphase_prev r₁ hr₁_mem; omega
      have hr2_mcr_imp_phase0 : r₂.role = .mcr → r₂.phase.val = 0 := by
        intro h
        rcases (hwf r₂ hr₂_mem).1 (Or.inl h) with h0 | h10
        · exact h0
        · have := hphase_prev r₂ hr₂_mem; omega
      -- Establish pair preservation: prePhase4Mass for the transitioning pair
      -- is preserved by the Transition.
      have hpair : prePhase4Mass (Transition L K r₁ r₂).1 +
          prePhase4Mass (Transition L K r₁ r₂).2 =
          prePhase4Mass r₁ + prePhase4Mass r₂ := by
        by_cases hboth_ge1 : 1 ≤ r₁.phase.val ∧ 1 ≤ r₂.phase.val
        · -- Case A: both phase ≥ 1. Neither is MCR (since MCR ⇒ phase 0). Pair lemma.
          obtain ⟨hr1_ge1, hr2_ge1⟩ := hboth_ge1
          have hr1_mcr : r₁.role ≠ .mcr := by
            intro h; have := hr1_mcr_imp_phase0 h; omega
          have hr2_mcr : r₂.role ≠ .mcr := by
            intro h; have := hr2_mcr_imp_phase0 h; omega
          have hr1_carrier : r₁.role ≠ .main → r₁.smallBias.val = 3 := by
            intro hnot_main
            have hcr_set : r₁.role = .cr ∨ r₁.role = .reserve ∨ r₁.role = .clock := by
              cases hrole : r₁.role with
              | main => exact absurd hrole hnot_main
              | reserve => right; left; rfl
              | clock => right; right; rfl
              | mcr => exact absurd hrole hr1_mcr
              | cr => left; rfl
            exact hcarrier_inv r₁ hr₁_mem hcr_set
          have hr2_carrier : r₂.role ≠ .main → r₂.smallBias.val = 3 := by
            intro hnot_main
            have hcr_set : r₂.role = .cr ∨ r₂.role = .reserve ∨ r₂.role = .clock := by
              cases hrole : r₂.role with
              | main => exact absurd hrole hnot_main
              | reserve => right; left; rfl
              | clock => right; right; rfl
              | mcr => exact absurd hrole hr2_mcr
              | cr => left; rfl
            exact hcarrier_inv r₂ hr₂_mem hcr_set
          exact Transition_preserves_prePhase4Mass_pair (L := L) (K := K) r₁ r₂
            hr1_mcr hr2_mcr hr1_carrier hr2_carrier
            (hnoerr_inv r₁ hr₁_mem) (hnoerr_inv r₂ hr₂_mem) hout1 hout2
        · -- Case B: some has phase = 0. We split on epidemic phase.
          push_neg at hboth_ge1
          by_cases hep_lt2 : (phaseEpidemicUpdate L K r₁ r₂).1.phase.val < 2
          · -- Epidemic phase < 2: max(r₁, r₂) ≤ 1, output phases ≤ 2 (via the
            -- Transition_*_phase_le_two_of_epidemic_phase_lt_two lemma).
            -- All four phases < 3, so prePhase4Mass = smallBiasInt, and the pair
            -- smallBiasInt sum is preserved by smallBiasSum_step_invariant_of_quota.
            have hout1_le2 := Transition_left_phase_le_two_of_epidemic_phase_lt_two
              (L := L) (K := K) r₁ r₂ hep_lt2 hout1
            have hout2_le2 := Transition_right_phase_le_two_of_epidemic_phase_lt_two
              (L := L) (K := K) r₁ r₂ hep_lt2 hout2
            have hmax_le : max r₁.phase.val r₂.phase.val ≤ 1 := by
              have hge := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) r₁ r₂
              omega
            have hr1_le1 : r₁.phase.val ≤ 1 := le_trans (le_max_left _ _) hmax_le
            have hr2_le1 : r₂.phase.val ≤ 1 := le_trans (le_max_right _ _) hmax_le
            have hr1_lt3 : r₁.phase.val < 3 := by omega
            have hr2_lt3 : r₂.phase.val < 3 := by omega
            have hout1_lt3 : (Transition L K r₁ r₂).1.phase.val < 3 := by omega
            have hout2_lt3 : (Transition L K r₁ r₂).2.phase.val < 3 := by omega
            have hpre_r1 : prePhase4Mass r₁ = (AgentState.smallBiasInt r₁ : ℚ) := by
              simp [prePhase4Mass, hr1_lt3]
            have hpre_r2 : prePhase4Mass r₂ = (AgentState.smallBiasInt r₂ : ℚ) := by
              simp [prePhase4Mass, hr2_lt3]
            have hpre_out1 : prePhase4Mass (Transition L K r₁ r₂).1 =
                (AgentState.smallBiasInt (Transition L K r₁ r₂).1 : ℚ) := by
              simp [prePhase4Mass, hout1_lt3]
            have hpre_out2 : prePhase4Mass (Transition L K r₁ r₂).2 =
                (AgentState.smallBiasInt (Transition L K r₁ r₂).2 : ℚ) := by
              simp [prePhase4Mass, hout2_lt3]
            have hquota := reachable_preserves_well_formed_agent_quota
              (L := L) (K := K) init _ hinit hprev
            have hpair_int := smallBiasSum_step_invariant_of_quota
              (L := L) (K := K) r₁ r₂ (hquota r₁ hr₁_mem) (hquota r₂ hr₂_mem)
            rw [hpre_out1, hpre_out2, hpre_r1, hpre_r2]
            exact_mod_cast hpair_int.symm
          · -- Epidemic phase ≥ 2 with `hboth_ge1` (some phase 0): apply the pair lemma.
            -- We show r₁.role ≠ .mcr and r₂.role ≠ .mcr by contradiction. The key
            -- contradiction: if `r.role = .mcr` with phase 0 and partner phase ≥ 1, then
            -- `runInitsBetween_mcr_zero_target_phase_ten` gives the post-epidemic phase = 10,
            -- forcing `Transition` output phase = 10 (via `phaseEpidemicUpdate_phase_le_Transition_phase`),
            -- contradicting `hout ≤ 4`.
            push_neg at hep_lt2
            -- Helper: deriving the MCR contradiction
            have mcr_contra_left : ∀ r other : AgentState L K,
                r.phase.val = 0 → 1 ≤ other.phase.val →
                r.role = .mcr →
                (Transition L K r other).1.phase.val ≤ 4 → False := by
              intro r other hr_phase0 hother_ge1 hr_mcr hout_le4
              -- Show ep.1.phase = 10 via the runInitsBetween-MCR helper
              have hot_le10 : other.phase.val ≤ 10 := by
                have := other.phase.2; omega
              have hep_10 : (phaseEpidemicUpdate L K r other).1.phase.val = 10 := by
                unfold phaseEpidemicUpdate
                set p := max r.phase other.phase with hp_def
                have hp_val : p.val = other.phase.val := by
                  simp [p, Fin.le_iff_val_le_val, hr_phase0]
                have hp_eq : p = ⟨other.phase.val, by have := other.phase.2; omega⟩ := by
                  apply Fin.ext; exact hp_val
                -- s' = runInitsBetween r.phase.val p.val {r with phase := p}
                -- We show s'.phase = 10 using the MCR helper.
                have hs'_phase :
                    (runInitsBetween L K r.phase.val p.val
                      ({ r with phase := p } : AgentState L K)).phase.val = 10 := by
                  rw [hr_phase0, hp_eq]
                  exact runInitsBetween_mcr_zero_target_phase_ten
                    r other.phase.val hr_mcr hother_ge1 hot_le10
                -- Guard: (r.phase < 10 ∨ other.phase < 10) ∧ (s'.phase = 10 ∨ t'.phase = 10)
                -- Both conjuncts hold: r.phase = 0 < 10 and s'.phase = 10.
                have hguard :
                    (r.phase.val < 10 ∨ other.phase.val < 10) ∧
                    ((runInitsBetween L K r.phase.val p.val
                        ({ r with phase := p } : AgentState L K)).phase.val = 10 ∨
                     (runInitsBetween L K other.phase.val p.val
                        ({ other with phase := p } : AgentState L K)).phase.val = 10) :=
                  ⟨Or.inl (by omega), Or.inl hs'_phase⟩
                rw [if_pos hguard]
                simp [phase10EpidemicEntry, hr_phase0, enterPhase10, phase10]
              -- ep.1.phase = 10, but Transition.1.phase ≥ ep.1.phase, ≤ 4
              have hmono := (phaseEpidemicUpdate_phase_le_Transition_phase
                (L := L) (K := K) r other).1
              omega
            -- Symmetric for right side: MCR on r and other on left
            have mcr_contra_right : ∀ r other : AgentState L K,
                r.phase.val = 0 → 1 ≤ other.phase.val →
                r.role = .mcr →
                (Transition L K other r).2.phase.val ≤ 4 → False := by
              intro r other hr_phase0 hother_ge1 hr_mcr hout_le4
              have hot_le10 : other.phase.val ≤ 10 := by
                have := other.phase.2; omega
              have hep_10 : (phaseEpidemicUpdate L K other r).2.phase.val = 10 := by
                unfold phaseEpidemicUpdate
                set p := max other.phase r.phase with hp_def
                have hp_val : p.val = other.phase.val := by
                  simp [p, Fin.le_iff_val_le_val, hr_phase0]
                have hp_eq : p = ⟨other.phase.val, by have := other.phase.2; omega⟩ := by
                  apply Fin.ext; exact hp_val
                have ht'_phase :
                    (runInitsBetween L K r.phase.val p.val
                      ({ r with phase := p } : AgentState L K)).phase.val = 10 := by
                  rw [hr_phase0, hp_eq]
                  exact runInitsBetween_mcr_zero_target_phase_ten
                    r other.phase.val hr_mcr hother_ge1 hot_le10
                have hguard :
                    (other.phase.val < 10 ∨ r.phase.val < 10) ∧
                    ((runInitsBetween L K other.phase.val p.val
                        ({ other with phase := p } : AgentState L K)).phase.val = 10 ∨
                     (runInitsBetween L K r.phase.val p.val
                        ({ r with phase := p } : AgentState L K)).phase.val = 10) :=
                  ⟨Or.inr (by omega), Or.inr ht'_phase⟩
                rw [if_pos hguard]
                simp [phase10EpidemicEntry, hr_phase0, enterPhase10, phase10]
              have hmono := (phaseEpidemicUpdate_phase_le_Transition_phase
                (L := L) (K := K) other r).2
              omega
            -- Now derive r₁.role ≠ .mcr and r₂.role ≠ .mcr.
            -- We need: from hboth_ge1, exactly one of r₁, r₂ has phase 0 (and other ≥ 1),
            -- since both phase 0 implies ep = 0 contradicting hep_lt2 ≥ 2.
            have hwf_r1 := hwf r₁ hr₁_mem
            have hwf_r2 := hwf r₂ hr₂_mem
            have hphase_r1 := hphase_prev r₁ hr₁_mem
            have hphase_r2 := hphase_prev r₂ hr₂_mem
            -- Show neither r₁ nor r₂ is MCR.
            have hr1_mcr : r₁.role ≠ .mcr := by
              intro h_mcr
              -- r₁ MCR ⇒ r₁.phase = 0 (via role_phase_invariant, with phase ≤ 4)
              have hr1_phase0 : r₁.phase.val = 0 := by
                rcases hwf_r1.1 (Or.inl h_mcr) with h0 | h10
                · exact h0
                · omega
              -- Case on r₂.phase: 0 vs ≥ 1
              by_cases hr2_ge1 : 1 ≤ r₂.phase.val
              · -- r₂ ≥ 1: apply mcr_contra_left
                exact mcr_contra_left r₁ r₂ hr1_phase0 hr2_ge1 h_mcr hout1
              · push_neg at hr2_ge1
                have hr2_phase0 : r₂.phase.val = 0 := by omega
                -- Both phase 0: ep = 0 (no inits run), contradicts hep_lt2
                have hep0 : (phaseEpidemicUpdate L K r₁ r₂).1.phase.val = 0 := by
                  unfold phaseEpidemicUpdate
                  set p := max r₁.phase r₂.phase
                  have hp_val : p.val = 0 := by
                    show max r₁.phase.val r₂.phase.val = 0
                    omega
                  set s' := runInitsBetween L K r₁.phase.val p.val ({ r₁ with phase := p })
                  set t' := runInitsBetween L K r₂.phase.val p.val ({ r₂ with phase := p })
                  have hs'_eq : s' = ({ r₁ with phase := p } : AgentState L K) := by
                    show runInitsBetween L K r₁.phase.val p.val _ = _
                    rw [show r₁.phase.val = 0 from hr1_phase0,
                        show p.val = 0 from hp_val]
                    exact runInitsBetween_self_api (L := L) (K := K) 0 _
                  have ht'_eq : t' = ({ r₂ with phase := p } : AgentState L K) := by
                    show runInitsBetween L K r₂.phase.val p.val _ = _
                    rw [show r₂.phase.val = 0 from hr2_phase0,
                        show p.val = 0 from hp_val]
                    exact runInitsBetween_self_api (L := L) (K := K) 0 _
                  have hs'_phase : s'.phase.val = 0 := by rw [hs'_eq]; exact hp_val
                  have ht'_phase : t'.phase.val = 0 := by rw [ht'_eq]; exact hp_val
                  have h_guard_fails :
                      ¬ ((r₁.phase.val < 10 ∨ r₂.phase.val < 10) ∧
                         (s'.phase.val = 10 ∨ t'.phase.val = 10)) := by
                    intro ⟨_, h⟩
                    rcases h with h1 | h2
                    · rw [hs'_phase] at h1; omega
                    · rw [ht'_phase] at h2; omega
                  rw [if_neg h_guard_fails]
                  exact hs'_phase
                omega
            have hr2_mcr : r₂.role ≠ .mcr := by
              intro h_mcr
              have hr2_phase0 : r₂.phase.val = 0 := by
                rcases hwf_r2.1 (Or.inl h_mcr) with h0 | h10
                · exact h0
                · omega
              by_cases hr1_ge1 : 1 ≤ r₁.phase.val
              · -- r₁ ≥ 1: apply mcr_contra_right (with r₂ as the MCR, r₁ as other)
                exact mcr_contra_right r₂ r₁ hr2_phase0 hr1_ge1 h_mcr hout2
              · push_neg at hr1_ge1
                have hr1_phase0 : r₁.phase.val = 0 := by omega
                -- Both phase 0: ep = 0
                have hep0 : (phaseEpidemicUpdate L K r₁ r₂).1.phase.val = 0 := by
                  unfold phaseEpidemicUpdate
                  set p := max r₁.phase r₂.phase
                  have hp_val : p.val = 0 := by
                    show max r₁.phase.val r₂.phase.val = 0
                    omega
                  set s' := runInitsBetween L K r₁.phase.val p.val ({ r₁ with phase := p })
                  set t' := runInitsBetween L K r₂.phase.val p.val ({ r₂ with phase := p })
                  have hs'_eq : s' = ({ r₁ with phase := p } : AgentState L K) := by
                    show runInitsBetween L K r₁.phase.val p.val _ = _
                    rw [show r₁.phase.val = 0 from hr1_phase0,
                        show p.val = 0 from hp_val]
                    exact runInitsBetween_self_api (L := L) (K := K) 0 _
                  have ht'_eq : t' = ({ r₂ with phase := p } : AgentState L K) := by
                    show runInitsBetween L K r₂.phase.val p.val _ = _
                    rw [show r₂.phase.val = 0 from hr2_phase0,
                        show p.val = 0 from hp_val]
                    exact runInitsBetween_self_api (L := L) (K := K) 0 _
                  have hs'_phase : s'.phase.val = 0 := by rw [hs'_eq]; exact hp_val
                  have ht'_phase : t'.phase.val = 0 := by rw [ht'_eq]; exact hp_val
                  have h_guard_fails :
                      ¬ ((r₁.phase.val < 10 ∨ r₂.phase.val < 10) ∧
                         (s'.phase.val = 10 ∨ t'.phase.val = 10)) := by
                    intro ⟨_, h⟩
                    rcases h with h1 | h2
                    · rw [hs'_phase] at h1; omega
                    · rw [ht'_phase] at h2; omega
                  rw [if_neg h_guard_fails]
                  exact hs'_phase
                omega
            -- Apply pair lemma
            have hr1_carrier : r₁.role ≠ .main → r₁.smallBias.val = 3 := by
              intro hnot_main
              have hcr_set : r₁.role = .cr ∨ r₁.role = .reserve ∨ r₁.role = .clock := by
                cases hrole : r₁.role with
                | main => exact absurd hrole hnot_main
                | reserve => right; left; rfl
                | clock => right; right; rfl
                | mcr => exact absurd hrole hr1_mcr
                | cr => left; rfl
              exact hcarrier_inv r₁ hr₁_mem hcr_set
            have hr2_carrier : r₂.role ≠ .main → r₂.smallBias.val = 3 := by
              intro hnot_main
              have hcr_set : r₂.role = .cr ∨ r₂.role = .reserve ∨ r₂.role = .clock := by
                cases hrole : r₂.role with
                | main => exact absurd hrole hnot_main
                | reserve => right; left; rfl
                | clock => right; right; rfl
                | mcr => exact absurd hrole hr2_mcr
                | cr => left; rfl
              exact hcarrier_inv r₂ hr₂_mem hcr_set
            exact Transition_preserves_prePhase4Mass_pair (L := L) (K := K) r₁ r₂
              hr1_mcr hr2_mcr hr1_carrier hr2_carrier
              (hnoerr_inv r₁ hr₁_mem) (hnoerr_inv r₂ hr₂_mem) hout1 hout2
      -- Multiset decomposition: prePhase4MassSum c = prePhase4MassSum prev + pair diff,
      -- and pair diff = 0 by hpair.
      rw [hc']
      have hrestore : b - r₁ ::ₘ {r₂} + r₁ ::ₘ {r₂} = b := Multiset.sub_add_cancel happ
      have hsum_prev_decomp : prePhase4MassSum b =
          prePhase4MassSum (b - r₁ ::ₘ {r₂}) +
            (prePhase4Mass r₁ + prePhase4Mass r₂) := by
        rw [← hrestore]
        simp [prePhase4MassSum, add_left_comm]
      have hsum_curr_decomp :
          prePhase4MassSum (b - r₁ ::ₘ {r₂} +
            (Transition L K r₁ r₂).1 ::ₘ {(Transition L K r₁ r₂).2}) =
          prePhase4MassSum (b - r₁ ::ₘ {r₂}) +
            (prePhase4Mass (Transition L K r₁ r₂).1 +
              prePhase4Mass (Transition L K r₁ r₂).2) := by
        simp [prePhase4MassSum, add_left_comm]
      rw [hsum_curr_decomp, hpair, ← hsum_prev_decomp]
      exact hprev_sum

/-- When Phase 4 is locally stable, the initial gap must be zero. -/
theorem phase4LocallyStable_initialGap_zero
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase4 : ∀ a ∈ c, a.phase.val = 4)
    (hn : 2 ≤ c.card)
    (hstable : phase4LocallyStable (L := L) (K := K) c)
    (hsmall_n : c.card < 2 ^ L) :
    initialGap init = 0 := by
  have hphase_le4 : ∀ a ∈ c, a.phase.val ≤ 4 := by
    intro a ha; have := hphase4 a ha; omega
  have hphase_ge3 : ∀ a ∈ c, 3 ≤ a.phase.val := by
    intro a ha; have := hphase4 a ha; omega
  have hmass := reachable_prePhase4MassSum_eq_initialGap_of_phase_le_four
    (L := L) (K := K) init c hinit hreach hphase_le4
  have hconvert := prePhase4MassSum_eq_dyadicBiasSum_of_phase_ge_three
    (L := L) (K := K) c hphase_ge3
  have hexp := phase4LocallyStable_all_exponents_ge_L (L := L) (K := K) c hn hstable
  have hdyadic_lt := dyadicBiasSum_lt_one_of_exponents_ge_L
    (L := L) (K := K) c hexp hsmall_n
  have hdyadic_eq : dyadicBiasSum c = (initialGap init : ℚ) := by
    rw [← hconvert, hmass]
  rw [hdyadic_eq] at hdyadic_lt
  -- hdyadic_lt : |(initialGap init : ℚ)| < 1
  -- initialGap init is ℤ, |(x : ℚ)| < 1 for x ∈ ℤ → x = 0
  have : initialGap init = 0 ∨ initialGap init ≠ 0 := eq_or_ne _ _
  rcases this with h | h
  · exact h
  · exfalso
    have h1 : (1 : ℤ) ≤ |initialGap init| := Int.one_le_abs h
    have h2 : (1 : ℚ) ≤ ((|initialGap init| : ℤ) : ℚ) := by exact_mod_cast h1
    rw [Int.cast_abs] at h2
    linarith

private theorem advance_step_then_epidemic
    (c : Config (AgentState L K)) (pnext : ℕ)
    (hadvance : ∃ d, (NonuniformMajority L K).Reachable c d ∧
      ∃ a ∈ d, pnext ≤ a.phase.val)
    (hn : 2 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = maxPhase final) ∧
      pnext ≤ maxPhase final := by
  rcases hadvance with ⟨d, hreach_d, a, ha_mem, ha_phase⟩
  have hn_d : 2 ≤ d.card := by
    rw [Protocol.reachable_card_eq (P := NonuniformMajority L K) hreach_d]
    exact hn
  rcases phase_epidemic_reachability_from_config (L := L) (K := K) d hn_d with
    ⟨final, hreach_final, hall, hmax⟩
  have hp_le_max_d : pnext ≤ maxPhase d :=
    le_trans ha_phase (phase_le_maxPhase_of_mem_chain (L := L) (K := K) ha_mem)
  exact ⟨final, Relation.ReflTransGen.trans hreach_d hreach_final,
    hall, le_trans hp_le_max_d hmax⟩

/-- Timed local progress followed by the phase epidemic.  Starting from a
configuration whose agents are all in the same standard timed phase and which
contains two distinct clock states, one can first schedule the timed counter
progress and then schedule the phase epidemic so that all agents share a common
phase at least `p + 1`.

This is the reusable deterministic chain fragment for phases
`0, 1, 5, 6, 7, 8`; it does not assert the separate global facts needed to
produce the clock pair at every phase. -/
theorem timed_phase_progress_then_epidemic_of_two_clocks
    (c : Config (AgentState L K))
    (p : ℕ) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (hphase : ∀ a ∈ c, a.phase.val = p)
    (hclocks :
      ∃ i j, i ∈ c ∧ j ∈ c ∧ i ≠ j ∧ i.role = .clock ∧ j.role = .clock)
    (hn : 2 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = maxPhase final) ∧
      p + 1 ≤ maxPhase final := by
  rcases timed_phase_progress_of_two_clocks
      (L := L) (K := K) c p hp hphase hclocks with
    ⟨d, hreach_d, a, ha_mem, ha_phase⟩
  have hn_d : 2 ≤ d.card := by
    rw [Protocol.reachable_card_eq (P := NonuniformMajority L K) hreach_d]
    exact hn
  rcases phase_epidemic_reachability_from_config (L := L) (K := K) d hn_d with
    ⟨final, hreach_final, hall, hmax⟩
  have hnext_le_max_d : p + 1 ≤ maxPhase d :=
    le_trans ha_phase (phase_le_maxPhase_of_mem_chain (L := L) (K := K) ha_mem)
  exact ⟨final, Relation.ReflTransGen.trans hreach_d hreach_final,
    hall, le_trans hnext_le_max_d hmax⟩

/-- Phase-1 specialization of the timed-progress/epidemic chain: from an
all-Phase-1 configuration with two distinct clocks, deterministic scheduling
can reach a synchronized configuration whose common phase is at least 2. -/
theorem phase1_progress_then_epidemic_of_two_clocks
    (c : Config (AgentState L K))
    (hphase1 : ∀ a ∈ c, a.phase.val = 1)
    (hclocks :
      ∃ i j, i ∈ c ∧ j ∈ c ∧ i ≠ j ∧ i.role = .clock ∧ j.role = .clock)
    (hn : 2 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = maxPhase final) ∧
      2 ≤ maxPhase final := by
  have hp1 : (1 : ℕ) ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ) := by simp
  simpa using
    timed_phase_progress_then_epidemic_of_two_clocks
      (L := L) (K := K) c 1 hp1 hphase1 hclocks hn

/-- Non-stable Phase-2 branch composed with the phase epidemic: if an
all-Phase-2 configuration has an applicable opposite-sign trigger, schedule one
local step and then synchronize everyone to a common phase at least 3. -/
theorem phase2_nonstable_branch_then_epidemic
    (c : Config (AgentState L K))
    (hphase2 : ∀ a ∈ c, a.phase.val = 2)
    (hnot : ¬ phase2LocallyStable (L := L) (K := K) c)
    (hn : 2 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = maxPhase final) ∧
      3 ≤ maxPhase final :=
  advance_step_then_epidemic (L := L) (K := K) c 3
    (phase2_advance_of_not_locallyStable (L := L) (K := K) c hphase2 hnot) hn

/-- Non-stable Phase-4 branch composed with the phase epidemic: a big-bias
trigger reaches Phase at least 5, then the epidemic synchronizes the population
to a common phase at least 5. -/
theorem phase4_nonstable_branch_then_epidemic
    (c : Config (AgentState L K))
    (hphase4 : ∀ a ∈ c, a.phase.val = 4)
    (hnot : ¬ phase4LocallyStable (L := L) (K := K) c)
    (hn : 2 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = maxPhase final) ∧
      5 ≤ maxPhase final :=
  advance_step_then_epidemic (L := L) (K := K) c 5
    (phase4_advance_of_not_locallyStable (L := L) (K := K) c hphase4 hnot) hn

/-- Non-stable Phase-9 branch composed with the phase epidemic: an
opposite-sign trigger reaches Phase 10, then the epidemic synchronizes the
population to Phase 10. -/
theorem phase9_nonstable_branch_then_epidemic
    (c : Config (AgentState L K))
    (hphase9 : ∀ a ∈ c, a.phase.val = 9)
    (hnot : ¬ phase9LocallyStable (L := L) (K := K) c)
    (hn : 2 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = maxPhase final) ∧
      10 ≤ maxPhase final :=
  advance_step_then_epidemic (L := L) (K := K) c 10
    (phase9_advance_of_not_locallyStable (L := L) (K := K) c hphase9 hnot) hn

/-- Phase-10 backup liveness viewed as a `majorityStableEndpoint` branch. -/
theorem phase10_backup_majorityStableEndpoint
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase10 : ∀ a ∈ c, a.phase.val = 10) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      majorityStableEndpoint (L := L) (K := K) init final := by
  rcases phase10_backup_reachability
      (L := L) (K := K) init c hinit hreach hphase10 with
    ⟨final, hreach_final, hwitness⟩
  exact ⟨final, hreach_final, Or.inr (Or.inr (Or.inr hwitness))⟩

/-- From a valid initial configuration of size at least eight, deterministic
Phase-0 role allocation can create clocks, run one Phase-0 clock counter far
enough to leave Phase 0, and then use the phase epidemic to synchronize the
population at a common phase at least one.  Clock roles are preserved along the
whole path, so the synchronized checkpoint still has an applicable clock-clock
pair. -/
theorem validInitial_to_checkpoint
    (init : Config (AgentState L K))
    (hinit : validInitial init) (hn : 8 ≤ init.card) :
    ∃ mid, (NonuniformMajority L K).Reachable init mid ∧
      (∀ a ∈ mid, a.phase.val = maxPhase mid) ∧
      1 ≤ maxPhase mid ∧
      (∃ i j, Protocol.Applicable mid i j ∧ i.role = .clock ∧ j.role = .clock) := by
  have hphase0 : ∀ a ∈ init, a.phase.val = 0 := by
    intro a ha
    exact congrArg Fin.val (hinit a ha).1
  have hmcr : ∀ a ∈ init, a.role = .mcr := by
    intro a ha
    exact (hinit a ha).2.1
  rcases phase0_creates_two_clocks (L := L) (K := K) init hphase0 hmcr hn with
    ⟨c₀, hreach₀, hphase₀, i, j, happ, hi_clock, hj_clock⟩
  have hp0 : (0 : ℕ) ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ) := by simp
  have hi_mem : i ∈ c₀ := Multiset.mem_of_le happ (by simp)
  have hj_mem : j ∈ c₀ := Multiset.mem_of_le happ (by simp)
  rcases timed_phase_progress_of_applicable_two_clocks
      (L := L) (K := K) c₀ 0 hp0 i j happ
      (hphase₀ i hi_mem) (hphase₀ j hj_mem) hi_clock hj_clock with
    ⟨d, hreach_timed, a, ha_mem, ha_phase⟩
  have hreach_init_d : (NonuniformMajority L K).Reachable init d :=
    Relation.ReflTransGen.trans hreach₀ hreach_timed
  have hn_d : 2 ≤ d.card := by
    rw [Protocol.reachable_card_eq (P := NonuniformMajority L K) hreach_init_d]
    omega
  rcases phase_epidemic_reachability_from_config (L := L) (K := K) d hn_d with
    ⟨mid, hreach_epidemic, hsync, hmax_mono⟩
  have hreach_c₀_mid : (NonuniformMajority L K).Reachable c₀ mid :=
    Relation.ReflTransGen.trans hreach_timed hreach_epidemic
  have hclock_mid :
      ∃ i' j', Protocol.Applicable mid i' j' ∧
        i'.role = .clock ∧ j'.role = .clock :=
    clock_pair_preserved_by_reachable_any
      (L := L) (K := K) c₀ mid ⟨happ, hi_clock, hj_clock⟩ hreach_c₀_mid
  have hmax_d_ge_one : 1 ≤ maxPhase d := by
    exact le_trans ha_phase (phase_le_maxPhase_of_mem_chain (L := L) (K := K) ha_mem)
  exact ⟨mid, Relation.ReflTransGen.trans hreach₀ hreach_c₀_mid,
    hsync, le_trans hmax_d_ge_one hmax_mono, hclock_mid⟩

/-- Strongest currently assembled deterministic chain from a synchronized
checkpoint.

Starting from a reachable configuration whose agents all have the same phase
`maxPhase c`, with common phase at least `1`, and with an applicable pair of
clock agents, the existing deterministic phase-progress lemmas reach one of
the certified stable endpoints.  The only correctness hypothesis exposed here
is the genuine remaining §5 gap: when phases 2, 4, or 9 are locally stable,
the corresponding branch must be able to reach the correct endpoint relative
to the initial majority verdict.

This theorem intentionally does not start from an arbitrary valid initial
configuration.  The current formal interfaces still need a separate bridge from
Phase 0/role allocation to such a synchronized checkpoint carrying clocks. -/
theorem synchronized_checkpoint_deterministic_liveness
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach_init : (NonuniformMajority L K).Reachable init c)
    (hn : 2 ≤ c.card)
    (hsync : ∀ a ∈ c, a.phase.val = maxPhase c)
    (hphase_ge_one : 1 ≤ maxPhase c)
    (hclocks :
      ∃ i j, Protocol.Applicable c i j ∧ i.role = .clock ∧ j.role = .clock)
    (hcorrect : ∀ c' : Config (AgentState L K),
      (NonuniformMajority L K).Reachable init c' →
        phase4LocallyStable (L := L) (K := K) c' →
          ∃ final, (NonuniformMajority L K).Reachable c' final ∧
            phase4TieEndpoint (L := L) (K := K) init final) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      majorityStableEndpoint (L := L) (K := K) init final := by
  classical
  let deficit := 10 - maxPhase c
  have main :
      ∀ n, ∀ c : Config (AgentState L K),
        10 - maxPhase c = n →
        (NonuniformMajority L K).Reachable init c →
        2 ≤ c.card →
        (∀ a ∈ c, a.phase.val = maxPhase c) →
        1 ≤ maxPhase c →
        (∃ i j, Protocol.Applicable c i j ∧ i.role = .clock ∧ j.role = .clock) →
        ∃ final, (NonuniformMajority L K).Reachable c final ∧
          majorityStableEndpoint (L := L) (K := K) init final := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hdef hreach_c hn_c hsync_c hphase_pos hclocks_c
      have hmax_le : maxPhase c ≤ 10 := maxPhase_le_ten_chain (L := L) (K := K) c
      have hphase_ge_all : ∀ a ∈ c, 1 ≤ a.phase.val := by
        intro a ha
        rw [hsync_c a ha]
        exact hphase_pos
      have hcontinue :
          ∀ d : Config (AgentState L K),
            (NonuniformMajority L K).Reachable c d →
            (∀ a ∈ d, a.phase.val = maxPhase d) →
            maxPhase c < maxPhase d →
            ∃ final, (NonuniformMajority L K).Reachable c final ∧
              majorityStableEndpoint (L := L) (K := K) init final := by
        intro d hreach_cd hsync_d hnext
        have hreach_init_d :
            (NonuniformMajority L K).Reachable init d :=
          Relation.ReflTransGen.trans hreach_c hreach_cd
        have hn_d : 2 ≤ d.card := by
          rw [Protocol.reachable_card_eq (P := NonuniformMajority L K) hreach_cd]
          exact hn_c
        have hphase_d : 1 ≤ maxPhase d := by omega
        rcases hclocks_c with ⟨ci, cj, hcapp, hci_clock, hcj_clock⟩
        have hclocks_d :
            ∃ i j, Protocol.Applicable d i j ∧ i.role = .clock ∧ j.role = .clock :=
          clock_pair_preserved_by_reachable
            (L := L) (K := K) c d ⟨hcapp, hci_clock, hcj_clock⟩
            hphase_ge_all hreach_cd
        have hdef_lt : 10 - maxPhase d < n := by
          have hd_le : maxPhase d ≤ 10 := maxPhase_le_ten_chain (L := L) (K := K) d
          rw [← hdef]
          omega
        rcases ih (10 - maxPhase d) hdef_lt d rfl hreach_init_d hn_d
            hsync_d hphase_d hclocks_d with
          ⟨final, hreach_df, hfinal⟩
        exact ⟨final, Relation.ReflTransGen.trans hreach_cd hreach_df, hfinal⟩
      have hcases :
          maxPhase c = 1 ∨ maxPhase c = 2 ∨ maxPhase c = 3 ∨
          maxPhase c = 4 ∨ maxPhase c = 5 ∨ maxPhase c = 6 ∨
          maxPhase c = 7 ∨ maxPhase c = 8 ∨ maxPhase c = 9 ∨
          maxPhase c = 10 := by
        omega
      rcases hcases with hmax | hmax | hmax | hmax | hmax | hmax | hmax | hmax | hmax | hmax
      · rcases hclocks_c with ⟨i, j, happ, hi_clock, hj_clock⟩
        have hi_mem : i ∈ c := Multiset.mem_of_le happ (by simp)
        have hj_mem : j ∈ c := Multiset.mem_of_le happ (by simp)
        have hp : (1 : ℕ) ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ) := by simp
        have hi_phase : i.phase.val = 1 := by rw [hsync_c i hi_mem, hmax]
        have hj_phase : j.phase.val = 1 := by rw [hsync_c j hj_mem, hmax]
        rcases advance_step_then_epidemic (L := L) (K := K) c 2
            (timed_phase_progress_of_applicable_two_clocks
              (L := L) (K := K) c 1 hp i j happ
              hi_phase hj_phase hi_clock hj_clock)
            hn_c with
          ⟨d, hreach_cd, hsync_d, hmax_d⟩
        exact hcontinue d hreach_cd hsync_d (by omega)
      · have hphase2 : ∀ a ∈ c, a.phase.val = 2 := by
          intro a ha
          rw [hsync_c a ha, hmax]
        rcases phase2_progress_or_locallyStable (L := L) (K := K) c hphase2 with
          hstable | hadvance
        · by_cases hpos : 0 < initialGap init
          · rcases phase2LocallyStable_reachable_to_phase2ConsensusEndpoint_of_initialGap_pos
                (L := L) (K := K) init c hinit hreach_c hn_c hpos hstable with
              ⟨final, hreach_final, hendpoint⟩
            exact ⟨final, hreach_final, Or.inl hendpoint⟩
          · by_cases hneg : initialGap init < 0
            · rcases phase2LocallyStable_reachable_to_phase2ConsensusEndpoint_of_initialGap_neg
                  (L := L) (K := K) init c hinit hreach_c hn_c hneg hstable with
                ⟨final, hreach_final, hendpoint⟩
              exact ⟨final, hreach_final, Or.inl hendpoint⟩
            · have hzero : initialGap init = 0 := by omega
              rcases phase2LocallyStable_reachable_to_phase2ConsensusEndpoint_of_initialGap_zero
                  (L := L) (K := K) init c hinit hreach_c hn_c hzero hstable with
                ⟨final, hreach_final, hendpoint⟩
              exact ⟨final, hreach_final, Or.inl hendpoint⟩
        · rcases advance_step_then_epidemic (L := L) (K := K) c 3 hadvance hn_c with
            ⟨d, hreach_cd, hsync_d, hmax_d⟩
          exact hcontinue d hreach_cd hsync_d (by omega)
      · rcases hclocks_c with ⟨i, j, happ, hi_clock, hj_clock⟩
        have hi_mem : i ∈ c := Multiset.mem_of_le happ (by simp)
        have hj_mem : j ∈ c := Multiset.mem_of_le happ (by simp)
        have hi_phase : i.phase.val = 3 := by rw [hsync_c i hi_mem, hmax]
        have hj_phase : j.phase.val = 3 := by rw [hsync_c j hj_mem, hmax]
        rcases advance_step_then_epidemic (L := L) (K := K) c 4
            (phase3_progress_of_applicable_two_clocks
              (L := L) (K := K) c i j happ
              hi_phase hj_phase hi_clock hj_clock)
            hn_c with
          ⟨d, hreach_cd, hsync_d, hmax_d⟩
        exact hcontinue d hreach_cd hsync_d (by omega)
      · have hphase4 : ∀ a ∈ c, a.phase.val = 4 := by
          intro a ha
          rw [hsync_c a ha, hmax]
        rcases phase4_progress_or_locallyStable (L := L) (K := K) c hphase4 with
          hstable | hadvance
        · rcases hcorrect c hreach_c hstable with
            ⟨final, hreach_final, hendpoint⟩
          exact ⟨final, hreach_final, Or.inr (Or.inl hendpoint)⟩
        · rcases advance_step_then_epidemic (L := L) (K := K) c 5 hadvance hn_c with
            ⟨d, hreach_cd, hsync_d, hmax_d⟩
          exact hcontinue d hreach_cd hsync_d (by omega)
      · rcases hclocks_c with ⟨i, j, happ, hi_clock, hj_clock⟩
        have hi_mem : i ∈ c := Multiset.mem_of_le happ (by simp)
        have hj_mem : j ∈ c := Multiset.mem_of_le happ (by simp)
        have hp : (5 : ℕ) ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ) := by simp
        have hi_phase : i.phase.val = 5 := by rw [hsync_c i hi_mem, hmax]
        have hj_phase : j.phase.val = 5 := by rw [hsync_c j hj_mem, hmax]
        rcases advance_step_then_epidemic (L := L) (K := K) c 6
            (timed_phase_progress_of_applicable_two_clocks
              (L := L) (K := K) c 5 hp i j happ
              hi_phase hj_phase hi_clock hj_clock)
            hn_c with
          ⟨d, hreach_cd, hsync_d, hmax_d⟩
        exact hcontinue d hreach_cd hsync_d (by omega)
      · rcases hclocks_c with ⟨i, j, happ, hi_clock, hj_clock⟩
        have hi_mem : i ∈ c := Multiset.mem_of_le happ (by simp)
        have hj_mem : j ∈ c := Multiset.mem_of_le happ (by simp)
        have hp : (6 : ℕ) ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ) := by simp
        have hi_phase : i.phase.val = 6 := by rw [hsync_c i hi_mem, hmax]
        have hj_phase : j.phase.val = 6 := by rw [hsync_c j hj_mem, hmax]
        rcases advance_step_then_epidemic (L := L) (K := K) c 7
            (timed_phase_progress_of_applicable_two_clocks
              (L := L) (K := K) c 6 hp i j happ
              hi_phase hj_phase hi_clock hj_clock)
            hn_c with
          ⟨d, hreach_cd, hsync_d, hmax_d⟩
        exact hcontinue d hreach_cd hsync_d (by omega)
      · rcases hclocks_c with ⟨i, j, happ, hi_clock, hj_clock⟩
        have hi_mem : i ∈ c := Multiset.mem_of_le happ (by simp)
        have hj_mem : j ∈ c := Multiset.mem_of_le happ (by simp)
        have hp : (7 : ℕ) ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ) := by simp
        have hi_phase : i.phase.val = 7 := by rw [hsync_c i hi_mem, hmax]
        have hj_phase : j.phase.val = 7 := by rw [hsync_c j hj_mem, hmax]
        rcases advance_step_then_epidemic (L := L) (K := K) c 8
            (timed_phase_progress_of_applicable_two_clocks
              (L := L) (K := K) c 7 hp i j happ
              hi_phase hj_phase hi_clock hj_clock)
            hn_c with
          ⟨d, hreach_cd, hsync_d, hmax_d⟩
        exact hcontinue d hreach_cd hsync_d (by omega)
      · rcases hclocks_c with ⟨i, j, happ, hi_clock, hj_clock⟩
        have hi_mem : i ∈ c := Multiset.mem_of_le happ (by simp)
        have hj_mem : j ∈ c := Multiset.mem_of_le happ (by simp)
        have hp : (8 : ℕ) ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ) := by simp
        have hi_phase : i.phase.val = 8 := by rw [hsync_c i hi_mem, hmax]
        have hj_phase : j.phase.val = 8 := by rw [hsync_c j hj_mem, hmax]
        rcases advance_step_then_epidemic (L := L) (K := K) c 9
            (timed_phase_progress_of_applicable_two_clocks
              (L := L) (K := K) c 8 hp i j happ
              hi_phase hj_phase hi_clock hj_clock)
            hn_c with
          ⟨d, hreach_cd, hsync_d, hmax_d⟩
        exact hcontinue d hreach_cd hsync_d (by omega)
      · have hphase9 : ∀ a ∈ c, a.phase.val = 9 := by
          intro a ha
          rw [hsync_c a ha, hmax]
        rcases phase9_progress_or_locallyStable (L := L) (K := K) c hphase9 with
          hstable | hadvance
        · by_cases hpos : 0 < initialGap init
          · rcases phase9LocallyStable_reachable_to_phase9ConsensusEndpoint_of_initialGap_pos
                (L := L) (K := K) init c hinit hreach_c hn_c hpos hstable with
              ⟨final, hreach_final, hendpoint⟩
            exact ⟨final, hreach_final, Or.inr (Or.inr (Or.inl hendpoint))⟩
          · by_cases hneg : initialGap init < 0
            · rcases phase9LocallyStable_reachable_to_phase9ConsensusEndpoint_of_initialGap_neg
                  (L := L) (K := K) init c hinit hreach_c hn_c hneg hstable with
                ⟨final, hreach_final, hendpoint⟩
              exact ⟨final, hreach_final, Or.inr (Or.inr (Or.inl hendpoint))⟩
            · have hzero : initialGap init = 0 := by omega
              rcases phase9LocallyStable_reachable_to_phase9ConsensusEndpoint_of_initialGap_zero
                  (L := L) (K := K) init c hinit hreach_c hn_c hzero hstable with
                ⟨final, hreach_final, hendpoint⟩
              exact ⟨final, hreach_final, Or.inr (Or.inr (Or.inl hendpoint))⟩
        · rcases advance_step_then_epidemic (L := L) (K := K) c 10 hadvance hn_c with
            ⟨d, hreach_cd, hsync_d, hmax_d⟩
          exact hcontinue d hreach_cd hsync_d (by omega)
      · have hphase10 : ∀ a ∈ c, a.phase.val = 10 := by
          intro a ha
          rw [hsync_c a ha, hmax]
        exact phase10_backup_majorityStableEndpoint
          (L := L) (K := K) init c hinit hreach_c hphase10
  exact main deficit c rfl hreach_init hn hsync hphase_ge_one hclocks

/-- End-to-end deterministic liveness from a large valid initial configuration,
conditional only on the still-open branch-correctness reachability invariant
for locally stable Phase 2/4/9 checkpoints. -/
theorem full_deterministic_liveness_from_initial
    (init : Config (AgentState L K))
    (hinit : validInitial init) (hn : 8 ≤ init.card)
    (hcorrect : ∀ c' : Config (AgentState L K),
      (NonuniformMajority L K).Reachable init c' →
        phase4LocallyStable (L := L) (K := K) c' →
          ∃ final, (NonuniformMajority L K).Reachable c' final ∧
            phase4TieEndpoint (L := L) (K := K) init final) :
    ∃ final, (NonuniformMajority L K).Reachable init final ∧
      majorityStableEndpoint (L := L) (K := K) init final := by
  rcases validInitial_to_checkpoint (L := L) (K := K) init hinit hn with
    ⟨mid, hreach_mid, hsync, hphase_ge_one, hclocks⟩
  have hn_mid : 2 ≤ mid.card := by
    rw [Protocol.reachable_card_eq (P := NonuniformMajority L K) hreach_mid]
    omega
  rcases synchronized_checkpoint_deterministic_liveness
      (L := L) (K := K) init mid hinit hreach_mid hn_mid hsync
      hphase_ge_one hclocks hcorrect with
    ⟨final, hreach_final, hendpoint⟩
  exact ⟨final, Relation.ReflTransGen.trans hreach_mid hreach_final, hendpoint⟩

set_option maxHeartbeats 4000000 in
private lemma transition_phase_zero_of_not_both_clock
    (s t : AgentState L K) (hs : s.phase.val = 0) (ht : t.phase.val = 0)
    (h : ¬(s.role = .clock ∧ t.role = .clock)) :
    (Transition L K s t).1.phase.val = 0 ∧
    (Transition L K s t).2.phase.val = 0 := by
  -- Step 1: phaseEpidemicUpdate when both phases are 0
  have h_phase_eq : s.phase = t.phase := Fin.ext (by omega)
  -- Simplify phaseEpidemicUpdate using same-phase facts
  have hmax : max s.phase t.phase = s.phase := by rw [h_phase_eq, max_self]
  -- After epidemic update, s' and t' have phase = s.phase (and hence val = 0)
  -- and preserve roles (since runInitsBetween p p = id)
  set e := phaseEpidemicUpdate L K s t with he_def
  set s' := e.1 with hs'_def
  set t' := e.2 with ht'_def
  -- Prove s'.phase = s.phase
  have hs'_phase : s'.phase = s.phase := by
    rw [hs'_def, he_def]
    unfold phaseEpidemicUpdate
    rw [hmax]
    have hrib_s : runInitsBetween L K s.phase.val s.phase.val
        ({ s with phase := s.phase } : AgentState L K) =
        { s with phase := s.phase } :=
      runInitsBetween_self_api (L := L) (K := K) s.phase.val _
    have hrib_t : runInitsBetween L K t.phase.val s.phase.val
        ({ t with phase := s.phase } : AgentState L K) =
        { t with phase := s.phase } := by
      rw [show t.phase.val = s.phase.val from by rw [h_phase_eq]]
      exact runInitsBetween_self_api (L := L) (K := K) s.phase.val _
    simp only [hrib_s, hrib_t]
    have hcond : ¬ ((s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (({ s with phase := s.phase } : AgentState L K).phase.val = 10 ∨
         ({ t with phase := s.phase } : AgentState L K).phase.val = 10)) := by
      rw [h_phase_eq]; omega
    rw [if_neg hcond]
  have hs'_phase_val : s'.phase.val = 0 := by
    have := congrArg Fin.val hs'_phase; simp at this; rw [this, hs]
  -- Prove s'.role = s.role
  have hs'_role : s'.role = s.role := by
    rw [hs'_def, he_def]
    unfold phaseEpidemicUpdate
    rw [hmax]
    have hrib_s : runInitsBetween L K s.phase.val s.phase.val
        ({ s with phase := s.phase } : AgentState L K) =
        { s with phase := s.phase } :=
      runInitsBetween_self_api (L := L) (K := K) s.phase.val _
    have hrib_t : runInitsBetween L K t.phase.val s.phase.val
        ({ t with phase := s.phase } : AgentState L K) =
        { t with phase := s.phase } := by
      rw [show t.phase.val = s.phase.val from by rw [h_phase_eq]]
      exact runInitsBetween_self_api (L := L) (K := K) s.phase.val _
    simp only [hrib_s, hrib_t]
    have hcond : ¬ ((s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (({ s with phase := s.phase } : AgentState L K).phase.val = 10 ∨
         ({ t with phase := s.phase } : AgentState L K).phase.val = 10)) := by
      rw [h_phase_eq]; omega
    rw [if_neg hcond]
  -- Prove t'.role = t.role
  have ht'_role : t'.role = t.role := by
    rw [ht'_def, he_def]
    unfold phaseEpidemicUpdate
    rw [hmax]
    have hrib_s : runInitsBetween L K s.phase.val s.phase.val
        ({ s with phase := s.phase } : AgentState L K) =
        { s with phase := s.phase } :=
      runInitsBetween_self_api (L := L) (K := K) s.phase.val _
    have hrib_t : runInitsBetween L K t.phase.val s.phase.val
        ({ t with phase := s.phase } : AgentState L K) =
        { t with phase := s.phase } := by
      rw [show t.phase.val = s.phase.val from by rw [h_phase_eq]]
      exact runInitsBetween_self_api (L := L) (K := K) s.phase.val _
    simp only [hrib_s, hrib_t]
    have hcond : ¬ ((s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (({ s with phase := s.phase } : AgentState L K).phase.val = 10 ∨
         ({ t with phase := s.phase } : AgentState L K).phase.val = 10)) := by
      rw [h_phase_eq]; omega
    rw [if_neg hcond]
  -- ¬ both clock transfers to s', t'
  have h' : ¬(s'.role = .clock ∧ t'.role = .clock) := by
    rw [hs'_role, ht'_role]; exact h
  -- Step 2: Show dispatch goes to Phase0Transition (since s'.phase.val = 0)
  have hs'0 : s'.phase = ⟨0, by omega⟩ := Fin.ext hs'_phase_val
  -- Step 3: Phase0Transition preserves phase when ¬both-clock
  have hp0 := Phase0Transition_phase_eq_of_not_both_clock (L := L) (K := K) s' t' h'
  -- Step 4: Connect Transition to finishPhase10Entry ∘ Phase0Transition
  have hT1 : (Transition L K s t).1 =
      finishPhase10Entry L K s' (Phase0Transition L K s' t').1 := by
    unfold Transition
    show finishPhase10Entry L K s'
      (match s'.phase with
       | ⟨0, _⟩ => Phase0Transition L K s' t'
       | ⟨1, _⟩ => Phase1Transition L K s' t'
       | ⟨2, _⟩ => Phase2Transition L K s' t'
       | ⟨3, _⟩ => Phase3Transition L K s' t'
       | ⟨4, _⟩ => Phase4Transition L K s' t'
       | ⟨5, _⟩ => Phase5Transition L K s' t'
       | ⟨6, _⟩ => Phase6Transition L K s' t'
       | ⟨7, _⟩ => Phase7Transition L K s' t'
       | ⟨8, _⟩ => Phase8Transition L K s' t'
       | ⟨9, _⟩ => Phase9Transition L K s' t'
       | ⟨10, _⟩ => Phase10Transition L K s' t'
       | _ => (s', t')).1 = _
    rw [hs'0]
  have hT2 : (Transition L K s t).2 =
      finishPhase10Entry L K t' (Phase0Transition L K s' t').2 := by
    unfold Transition
    show finishPhase10Entry L K t'
      (match s'.phase with
       | ⟨0, _⟩ => Phase0Transition L K s' t'
       | ⟨1, _⟩ => Phase1Transition L K s' t'
       | ⟨2, _⟩ => Phase2Transition L K s' t'
       | ⟨3, _⟩ => Phase3Transition L K s' t'
       | ⟨4, _⟩ => Phase4Transition L K s' t'
       | ⟨5, _⟩ => Phase5Transition L K s' t'
       | ⟨6, _⟩ => Phase6Transition L K s' t'
       | ⟨7, _⟩ => Phase7Transition L K s' t'
       | ⟨8, _⟩ => Phase8Transition L K s' t'
       | ⟨9, _⟩ => Phase9Transition L K s' t'
       | ⟨10, _⟩ => Phase10Transition L K s' t'
       | _ => (s', t')).2 = _
    rw [hs'0]
  constructor
  · -- First component phase = 0
    rw [hT1, finishPhase10Entry_phase_val]
    have := congrArg Fin.val hp0.1
    simp at this
    rw [this, hs'_phase_val]
  · -- Second component phase = 0
    rw [hT2, finishPhase10Entry_phase_val]
    have := congrArg Fin.val hp0.2
    simp at this
    -- hp0.2 says (Phase0Transition L K s' t').2.phase = t'.phase
    -- t'.phase.val = ?
    -- We need t'.phase.val = 0
    -- We know s'.phase = s.phase and s.phase.val = 0
    -- t'.phase: we didn't directly prove this, but we can derive it
    have ht'_phase_val : t'.phase.val = 0 := by
      have ht'_phase : t'.phase = t.phase := by
        rw [ht'_def, he_def]
        unfold phaseEpidemicUpdate
        rw [hmax]
        have hrib_s : runInitsBetween L K s.phase.val s.phase.val
            ({ s with phase := s.phase } : AgentState L K) =
            { s with phase := s.phase } :=
          runInitsBetween_self_api (L := L) (K := K) s.phase.val _
        have hrib_t : runInitsBetween L K t.phase.val s.phase.val
            ({ t with phase := s.phase } : AgentState L K) =
            { t with phase := s.phase } := by
          rw [show t.phase.val = s.phase.val from by rw [h_phase_eq]]
          exact runInitsBetween_self_api (L := L) (K := K) s.phase.val _
        simp only [hrib_s, hrib_t]
        have hcond : ¬ ((s.phase.val < 10 ∨ t.phase.val < 10) ∧
            (({ s with phase := s.phase } : AgentState L K).phase.val = 10 ∨
             ({ t with phase := s.phase } : AgentState L K).phase.val = 10)) := by
          rw [h_phase_eq]; omega
        rw [if_neg hcond]
        simp [h_phase_eq]
      rw [congrArg Fin.val ht'_phase, ht]
    rw [this, ht'_phase_val]

private theorem reachable_clockCount_ge_two_or_all_phase_zero
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c) :
    2 ≤ clockCount (L := L) (K := K) c ∨ (∀ a ∈ c, a.phase.val = 0) := by
  induction hreach with
  | refl =>
      right
      intro a ha
      exact congrArg Fin.val (hinit a ha).1
  | tail _ hstep ih =>
      rcases ih with hcount | hphase0
      · left
        exact StepRel_clockCount_ge_two_any (L := L) (K := K) hcount hstep
      · rcases hstep with ⟨s, t, happ, hc'⟩
        dsimp at hc'
        subst hc'
        have hs0 : s.phase.val = 0 := hphase0 s (Multiset.mem_of_le happ (by simp))
        have ht0 : t.phase.val = 0 := hphase0 t (Multiset.mem_of_le happ (by simp))
        have hmono := Transition_phase_monotone (L := L) (K := K) s t
        by_cases hp1 : (Transition L K s t).1.phase.val = 0 ∧
            (Transition L K s t).2.phase.val = 0
        · right
          intro a ha
          rcases Multiset.mem_add.mp ha with ha_old | ha_new
          · exact hphase0 a (Multiset.mem_of_le
              (Multiset.sub_le_self _ _) ha_old)
          · rcases Multiset.mem_cons.mp ha_new with rfl | ht_mem
            · exact hp1.1
            · rw [Multiset.mem_singleton.mp ht_mem]
              exact hp1.2
        · left
          push_neg at hp1
          have : s.role = .clock ∧ t.role = .clock := by
            by_contra h
            have ⟨h1, h2⟩ := transition_phase_zero_of_not_both_clock
              (L := L) (K := K) s t hs0 ht0 h
            exact absurd h2 (hp1 h1)
          have hcount := clockCount_ge_two_of_applicable_clocks
              (L := L) (K := K) happ this.1 this.2
          exact StepRel_clockCount_ge_two_any (L := L) (K := K) hcount
            ⟨s, t, happ, rfl⟩

private theorem all_phase_zero_implies_maxPhase_zero
    (c : Config (AgentState L K))
    (h : ∀ a ∈ c, a.phase.val = 0) :
    maxPhase c = 0 := by
  unfold maxPhase
  apply le_antisymm
  · exact Finset.sup_le (fun a ha => by
      rw [h a (Multiset.mem_toFinset.mp ha)])
  · exact Nat.zero_le _


/-! ### Phase 0 general two-clock construction helpers -/

/-- Count agents of a given role.  Local to this module because the identical
definition in `PhaseProgress.lean` is private. -/
private def roleCountG (r : Role) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a : AgentState L K => a.role = r) c

/-- Two agents of a given role can always be found as an applicable pair. -/
private lemma exists_applicable_pair_of_roleCountG_ge_two
    (r : Role) {c : Config (AgentState L K)}
    (h : 2 ≤ roleCountG (L := L) (K := K) r c) :
    ∃ s t, Protocol.Applicable c s t ∧ s.role = r ∧ t.role = r := by
  rcases exists_applicable_pair_of_countP_ge_two
      (p := fun a : AgentState L K => a.role = r) h with
    ⟨s, t, hpair, hs, ht⟩
  exact ⟨s, t, hpair, hs, ht⟩

/-- Per-agent contribution to the Phase-0 potential Φ = MCR + 3·CR + 6·Clock. -/
private def agentPhi (a : AgentState L K) : ℕ :=
  match a.role with
  | .mcr => 1
  | .cr => 3
  | .clock => 6
  | _ => 0

/-- Per-agent indicator: 1 if the agent is unassigned and not Main/MCR, 0 otherwise.
These are exactly the agents targetable by Rule 3. -/
private def agentSurplus (a : AgentState L K) : ℕ :=
  if a.role ≠ .main ∧ a.role ≠ .mcr ∧ a.assigned = false then 1 else 0

/-- Count of unassigned non-Main/MCR agents in a configuration. -/
private def surplusCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a : AgentState L K =>
    a.role ≠ .main ∧ a.role ≠ .mcr ∧ a.assigned = false) c

/-- The epidemic update is identity when both agents share the same phase < 10.
Local reproof of the private lemma in PhaseProgress.lean. -/
private lemma phaseEpidemicUpdate_eq_self_of_same_phase
    (ph : Fin 11) (hph10 : ph.val ≠ 10)
    (s t : AgentState L K)
    (hs_phase : s.phase = ph) (ht_phase : t.phase = ph) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  unfold phaseEpidemicUpdate
  rw [hs_phase, ht_phase, max_self]
  simp only [runInitsBetween_self_api]
  cases s; cases t; simp_all

set_option maxHeartbeats 8000000 in
private lemma phaseInit_assigned_eq (p : Fin 11) (a : AgentState L K) :
    (phaseInit L K p a).assigned = a.assigned := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  cases role <;> fin_cases p <;> simp [phaseInit, enterPhase10] <;>
    repeat' split_ifs <;> simp [enterPhase10]

private lemma advancePhase_assigned_eq (a : AgentState L K) :
    (advancePhase L K a).assigned = a.assigned := by
  unfold advancePhase; split <;> simp

private lemma advancePhaseWithInit_assigned_eq (a : AgentState L K) :
    (advancePhaseWithInit L K a).assigned = a.assigned := by
  unfold advancePhaseWithInit
  rw [phaseInit_assigned_eq, advancePhase_assigned_eq]

private lemma stdCounterSubroutine_assigned_eq (a : AgentState L K) :
    (stdCounterSubroutine L K a).assigned = a.assigned := by
  unfold stdCounterSubroutine
  split
  · exact advancePhaseWithInit_assigned_eq a
  · rfl

-- Key per-pair lemma: Phase0Transition preserves the adjusted potential
-- Phi - surplus.  Each rule either preserves or increases Phi - surplus.
set_option maxHeartbeats 16000000 in
private lemma Phase0Transition_adjusted_potential_nondec
    (s t : AgentState L K) :
    agentPhi (L := L) (K := K) (Phase0Transition L K s t).1 +
      agentPhi (L := L) (K := K) (Phase0Transition L K s t).2 +
      agentSurplus (L := L) (K := K) s + agentSurplus (L := L) (K := K) t ≥
    agentPhi (L := L) (K := K) s + agentPhi (L := L) (K := K) t +
      agentSurplus (L := L) (K := K) (Phase0Transition L K s t).1 +
      agentSurplus (L := L) (K := K) (Phase0Transition L K s t).2 := by
  rcases s with
    ⟨si, so, sp, sr, sa, sb, ssb, sh, sm, sf, sop, sc⟩
  rcases t with
    ⟨ti, to_, tp, tr, ta, tb, tsb, th, tm, tf, top, tc⟩
  simp only [agentPhi, agentSurplus]
  cases sr <;> cases tr <;> cases sa <;> cases ta <;>
    simp [Phase0Transition, stdCounterSubroutine_assigned_eq,
      stdCounterSubroutine_clock_role_eq] <;>
    omega

/-
-/

private lemma Transition_adjusted_potential_nondec_phase0
    (s t : AgentState L K)
    (hs : s.phase.val = 0) (ht : t.phase.val = 0) :
    agentPhi (L := L) (K := K) (Transition L K s t).1 +
      agentPhi (L := L) (K := K) (Transition L K s t).2 +
      agentSurplus (L := L) (K := K) s + agentSurplus (L := L) (K := K) t ≥
    agentPhi (L := L) (K := K) s + agentPhi (L := L) (K := K) t +
      agentSurplus (L := L) (K := K) (Transition L K s t).1 +
      agentSurplus (L := L) (K := K) (Transition L K s t).2 := by
  -- When both agents have phase 0, phaseEpidemicUpdate is identity
  have hs_phase : s.phase = ⟨0, by decide⟩ := by ext; exact hs
  have ht_phase : t.phase = ⟨0, by decide⟩ := by ext; exact ht
  have hepid : phaseEpidemicUpdate L K s t = (s, t) :=
    phaseEpidemicUpdate_eq_self_of_same_phase ⟨0, by decide⟩ (by decide) s t hs_phase ht_phase
  -- So Transition dispatches to Phase0Transition, then finishPhase10Entry
  simp only [Transition, hepid, hs_phase]
  -- finishPhase10Entry preserves role and assigned, so agentPhi/agentSurplus are preserved
  simp only [agentPhi, agentSurplus, finishPhase10Entry_role, finishPhase10Entry_assigned]
  exact Phase0Transition_adjusted_potential_nondec s t

-- Helper: the Multiset sum of agentPhi over a config
private def phiTotal (c : Config (AgentState L K)) : ℕ :=
  (c.map (agentPhi (L := L) (K := K))).sum

-- Helper: the Multiset sum of agentSurplus over a config
private def surplusTotal (c : Config (AgentState L K)) : ℕ :=
  (c.map (agentSurplus (L := L) (K := K))).sum

private lemma phiTotal_eq_roleCountG (c : Config (AgentState L K)) :
    phiTotal (L := L) (K := K) c =
      roleCountG (L := L) (K := K) .mcr c +
        3 * roleCountG (L := L) (K := K) .cr c +
          6 * roleCountG (L := L) (K := K) .clock c := by
  unfold phiTotal roleCountG agentPhi
  induction c using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.countP_cons]
    cases a.role <;> simp_all <;> omega

private lemma phiTotal_add (c d : Config (AgentState L K)) :
    phiTotal (L := L) (K := K) (c + d) =
      phiTotal (L := L) (K := K) c + phiTotal (L := L) (K := K) d := by
  unfold phiTotal
  simp [Multiset.map_add, Multiset.sum_add]

private lemma surplusTotal_add (c d : Config (AgentState L K)) :
    surplusTotal (L := L) (K := K) (c + d) =
      surplusTotal (L := L) (K := K) c + surplusTotal (L := L) (K := K) d := by
  unfold surplusTotal
  simp [Multiset.map_add, Multiset.sum_add]

private lemma phiTotal_singleton (a : AgentState L K) :
    phiTotal (L := L) (K := K) {a} = agentPhi (L := L) (K := K) a := by
  unfold phiTotal; simp

private lemma surplusTotal_singleton (a : AgentState L K) :
    surplusTotal (L := L) (K := K) {a} = agentSurplus (L := L) (K := K) a := by
  unfold surplusTotal; simp

private lemma phiTotal_pair (a b : AgentState L K) :
    phiTotal (L := L) (K := K) ({a, b} : Multiset _) =
      agentPhi (L := L) (K := K) a + agentPhi (L := L) (K := K) b := by
  show phiTotal (L := L) (K := K) (({a} : Multiset _) + {b}) = _
  rw [phiTotal_add, phiTotal_singleton, phiTotal_singleton]

private lemma surplusTotal_pair (a b : AgentState L K) :
    surplusTotal (L := L) (K := K) ({a, b} : Multiset _) =
      agentSurplus (L := L) (K := K) a + agentSurplus (L := L) (K := K) b := by
  show surplusTotal (L := L) (K := K) (({a} : Multiset _) + {b}) = _
  rw [surplusTotal_add, surplusTotal_singleton, surplusTotal_singleton]

private lemma phiTotal_sub_le (c d : Config (AgentState L K)) (h : d ≤ c) :
    phiTotal (L := L) (K := K) (c - d) + phiTotal (L := L) (K := K) d =
      phiTotal (L := L) (K := K) c := by
  have : c - d + d = c := Multiset.sub_add_cancel h
  calc phiTotal (L := L) (K := K) (c - d) + phiTotal (L := L) (K := K) d
      = phiTotal (L := L) (K := K) (c - d + d) := by rw [phiTotal_add]
    _ = phiTotal (L := L) (K := K) c := by rw [this]

private lemma surplusTotal_sub_le (c d : Config (AgentState L K)) (h : d ≤ c) :
    surplusTotal (L := L) (K := K) (c - d) + surplusTotal (L := L) (K := K) d =
      surplusTotal (L := L) (K := K) c := by
  have : c - d + d = c := Multiset.sub_add_cancel h
  calc surplusTotal (L := L) (K := K) (c - d) + surplusTotal (L := L) (K := K) d
      = surplusTotal (L := L) (K := K) (c - d + d) := by rw [surplusTotal_add]
    _ = surplusTotal (L := L) (K := K) c := by rw [this]

-- Stronger invariant: phiTotal - surplusTotal ≥ init.card
-- We prove phiTotal(c) ≥ init.card + surplusTotal(c)
set_option maxHeartbeats 8000000 in
private lemma phase0_adjusted_potential_invariant
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase0 : ∀ a ∈ c, a.phase.val = 0) :
    phiTotal (L := L) (K := K) c ≥
      init.card + surplusTotal (L := L) (K := K) c := by
  induction hreach with
  | refl =>
    -- Base: all MCR with assigned = false ⟹ Phi = init.card, surplus = 0
    suffices h : phiTotal (L := L) (K := K) init = init.card ∧
        surplusTotal (L := L) (K := K) init = 0 by omega
    constructor
    · unfold phiTotal
      induction init using Multiset.induction with
      | empty => simp
      | cons a s ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
        have ha : a ∈ (a ::ₘ s) := Multiset.mem_cons_self a s
        have hdata := hinit a ha
        have hrole : a.role = .mcr := hdata.2.1
        have hih : (Multiset.map (agentPhi (L := L) (K := K)) s).sum = s.card := by
          apply ih
          · intro b hb
            exact hinit b (Multiset.mem_cons_of_mem hb)
          · intro b hb
            exact hphase0 b (Multiset.mem_cons_of_mem hb)
        have ha_phi : agentPhi (L := L) (K := K) a = 1 := by
          simp [agentPhi, hrole]
        rw [ha_phi, hih]; omega
    · unfold surplusTotal
      induction init using Multiset.induction with
      | empty => simp
      | cons a s ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons]
        have ha : a ∈ (a ::ₘ s) := Multiset.mem_cons_self a s
        have hdata := hinit a ha
        have hrole : a.role = .mcr := hdata.2.1
        have hih : (Multiset.map (agentSurplus (L := L) (K := K)) s).sum = 0 := by
          apply ih
          · intro b hb
            exact hinit b (Multiset.mem_cons_of_mem hb)
          · intro b hb
            exact hphase0 b (Multiset.mem_cons_of_mem hb)
        have ha_surp : agentSurplus (L := L) (K := K) a = 0 := by
          simp [agentSurplus, hrole]
        rw [ha_surp, hih]
  | tail hreach_prev hstep ih =>
    rename_i cprev cnext
    rcases hstep with ⟨s, t, happ, hc'⟩
    dsimp at hc'
    -- Don't subst; instead use hc' to rewrite
    have hs_mem : s ∈ cprev := Multiset.mem_of_le happ (Multiset.mem_cons_self _ _)
    have ht_mem : t ∈ cprev := Multiset.mem_of_le happ
      (Multiset.mem_cons.2 (Or.inr (Multiset.mem_singleton_self t)))
    -- Prove all of cprev is phase 0 (backward from hphase0 on cnext)
    have hphase0_cnext := hphase0
    rw [hc'] at hphase0_cnext
    have hphase0_prev : ∀ a ∈ cprev, a.phase.val = 0 := by
      intro a ha
      have hmono := Transition_phase_monotone (L := L) (K := K) s t
      by_cases has : a = s
      · subst a
        have hout : (Transition L K s t).1.phase.val = 0 :=
          hphase0_cnext _ (Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_self _ _)))
        omega
      · by_cases hat : a = t
        · subst a
          have hout : (Transition L K s t).2.phase.val = 0 :=
            hphase0_cnext _ (Multiset.mem_add.2 (Or.inr
              (Multiset.mem_cons.2 (Or.inr (Multiset.mem_singleton_self _)))))
          omega
        · have ha_res : a ∈ cprev - ({s, t} : Multiset (AgentState L K)) := by
            have h1 : a ∈ cprev.erase s := (Multiset.mem_erase_of_ne has).2 ha
            have h2 : a ∈ (cprev.erase s).erase t :=
              (Multiset.mem_erase_of_ne hat).2 h1
            simpa using h2
          exact hphase0_cnext a (Multiset.mem_add.2 (Or.inl ha_res))
    have ih_bound := ih hphase0_prev
    -- Decompose the new config
    -- cnext = cprev - {s,t} + {s', t'} where s' = (Transition L K s t).1
    -- phiTotal(cnext) and surplusTotal(cnext) decompose
    have hphi_cnext : phiTotal (L := L) (K := K) cnext =
        phiTotal (L := L) (K := K) (cprev - ({s, t} : Multiset _)) +
          (agentPhi (L := L) (K := K) (Transition L K s t).1 +
           agentPhi (L := L) (K := K) (Transition L K s t).2) := by
      conv_lhs => rw [hc']
      unfold phiTotal NonuniformMajority
      simp [Multiset.map_add, Multiset.sum_add, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_singleton, Multiset.sum_singleton]
      omega
    have hsurp_cnext : surplusTotal (L := L) (K := K) cnext =
        surplusTotal (L := L) (K := K) (cprev - ({s, t} : Multiset _)) +
          (agentSurplus (L := L) (K := K) (Transition L K s t).1 +
           agentSurplus (L := L) (K := K) (Transition L K s t).2) := by
      conv_lhs => rw [hc']
      unfold surplusTotal NonuniformMajority
      simp [Multiset.map_add, Multiset.sum_add, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_singleton, Multiset.sum_singleton]
      omega
    -- Decompose cprev
    have hphi_prev := phiTotal_sub_le (L := L) (K := K) cprev ({s, t} : Multiset _) happ
    have hsurp_prev := surplusTotal_sub_le (L := L) (K := K) cprev ({s, t} : Multiset _) happ
    rw [phiTotal_pair] at hphi_prev
    rw [surplusTotal_pair] at hsurp_prev
    -- Per-pair inequality
    have hs0 := hphase0_prev s hs_mem
    have ht0 := hphase0_prev t ht_mem
    have hpair := Transition_adjusted_potential_nondec_phase0 (L := L) (K := K) s t hs0 ht0
    -- Combine everything
    omega

set_option maxHeartbeats 8000000 in
private lemma phase0_potential_bound
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase0 : ∀ a ∈ c, a.phase.val = 0)
    (hn : 11 ≤ init.card) :
    roleCountG (L := L) (K := K) .mcr c +
      3 * (roleCountG (L := L) (K := K) .cr c +
           2 * roleCountG (L := L) (K := K) .clock c) ≥
      init.card := by
  have hinv := phase0_adjusted_potential_invariant (L := L) (K := K) init c hinit hreach hphase0
  have hphi_eq := phiTotal_eq_roleCountG (L := L) (K := K) c
  omega

/-- From any reachable all-phase-0 config with enough agents, we can reach a
config with two applicable clocks while staying in phase 0.  Generalizes
`phase0_creates_two_clocks` by dropping the all-MCR precondition.
The bound 16 leaves margin for MCR waste through Rule 3 interactions.

Proof strategy: from the potential bound MCR + 3·(CR+2·Clock) ≥ 16, case-split
on the clock count.  If clock ≥ 2: done.  If CR+2·Clock ≥ 4: at most two CR+CR
steps suffice (each creates one Clock via `phase0_cr_step_data`).  Otherwise
CR+2·Clock ≤ 3 and MCR ≥ 7, so 1–4 MCR+MCR steps (via `phase0_mcr_step_data`)
boost CR+2·Clock past 4, then CR+CR finishes. -/
private lemma roleCountG_eq_roleCount (r : Role) (c : Config (AgentState L K)) :
    roleCountG (L := L) (K := K) r c = roleCount (L := L) (K := K) r c := by
  rfl

/-- One MCR+MCR step from a phase-0 config preserves phase 0 and the potential bound,
while increasing CR by 1 and decreasing MCR by 2.  Wraps `phase0_mcr_step_data`
with `roleCountG` statements. -/
private lemma phase0_mcr_step_general
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 0)
    (hmcr : 2 ≤ roleCountG (L := L) (K := K) .mcr c) :
    ∃ c', (NonuniformMajority L K).Reachable c c' ∧
      (∀ a ∈ c', a.phase.val = 0) ∧
      roleCountG (L := L) (K := K) .mcr c' =
        roleCountG (L := L) (K := K) .mcr c - 2 ∧
      roleCountG (L := L) (K := K) .cr c' =
        roleCountG (L := L) (K := K) .cr c + 1 ∧
      roleCountG (L := L) (K := K) .clock c' =
        roleCountG (L := L) (K := K) .clock c := by
  simp only [roleCountG_eq_roleCount] at hmcr ⊢
  rcases exists_applicable_pair_of_roleCount_ge_two
      (L := L) (K := K) .mcr (c := c) hmcr with
    ⟨s, t, happ, hs, ht⟩
  rcases phase0_mcr_step_data
      (L := L) (K := K) c s t happ hphase hs ht with
    ⟨hreach, hphase', hmcr', hcr', hclock'⟩
  exact ⟨_, hreach, hphase', hmcr', hcr', hclock'⟩

/-- One CR+CR step from a phase-0 config preserves phase 0 while
increasing Clock by 1, decreasing CR by 2, and leaving MCR unchanged. -/
private lemma phase0_cr_step_general
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 0)
    (hcr : 2 ≤ roleCountG (L := L) (K := K) .cr c) :
    ∃ c', (NonuniformMajority L K).Reachable c c' ∧
      (∀ a ∈ c', a.phase.val = 0) ∧
      roleCountG (L := L) (K := K) .mcr c' =
        roleCountG (L := L) (K := K) .mcr c ∧
      roleCountG (L := L) (K := K) .cr c' =
        roleCountG (L := L) (K := K) .cr c - 2 ∧
      roleCountG (L := L) (K := K) .clock c' =
        roleCountG (L := L) (K := K) .clock c + 1 := by
  simp only [roleCountG_eq_roleCount] at hcr ⊢
  rcases exists_applicable_pair_of_roleCount_ge_two
      (L := L) (K := K) .cr (c := c) hcr with
    ⟨s, t, happ, hs, ht⟩
  have hs_phase : s.phase.val = 0 := hphase s (Multiset.mem_of_le happ (by simp))
  have ht_phase : t.phase.val = 0 := hphase t (Multiset.mem_of_le happ (by simp))
  have htr := Transition_phase0_cr_cr_roles
    (L := L) (K := K) s t hs_phase ht_phase hs ht
  rcases phase0_cr_step_data
      (L := L) (K := K) c s t happ hphase hs ht with
    ⟨hreach, hphase', hcr', hclock'⟩
  refine ⟨_, hreach, hphase', ?_, hcr', hclock'⟩
  -- MCR is unchanged: input pair has 0 MCR agents, output pair has 0 MCR agents
  change roleCount (L := L) (K := K) .mcr
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) =
    roleCount (L := L) (K := K) .mcr c
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
      c - ({s, t} : Multiset (AgentState L K)) +
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  rw [hstep]
  unfold roleCount
  rw [Multiset.countP_add,
    Multiset.countP_sub happ (fun a : AgentState L K => a.role = .mcr)]
  -- Input pair: both CR, so 0 MCR
  have hpair_mcr :
      Multiset.countP (fun a : AgentState L K => a.role = .mcr)
        ({s, t} : Multiset (AgentState L K)) = 0 := by
    rw [show ({s, t} : Multiset (AgentState L K)) = ({s} : Multiset _) + {t} by rfl,
      Multiset.countP_add,
      countP_singleton_of_dc_not (p := fun a : AgentState L K => a.role = .mcr)
        (by simp [hs]),
      countP_singleton_of_dc_not (p := fun a : AgentState L K => a.role = .mcr)
        (by simp [ht])]
  -- Output pair: Clock + Reserve, so 0 MCR
  have hout_mcr :
      Multiset.countP (fun a : AgentState L K => a.role = .mcr)
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [show ({(Transition L K s t).1, (Transition L K s t).2} :
        Multiset (AgentState L K)) =
          ({(Transition L K s t).1} : Multiset _) + {(Transition L K s t).2} by rfl,
      Multiset.countP_add,
      countP_singleton_of_dc_not (p := fun a : AgentState L K => a.role = .mcr)
        (by simp [htr.1]),
      countP_singleton_of_dc_not (p := fun a : AgentState L K => a.role = .mcr)
        (by simp [htr.2.2.1])]
  rw [hpair_mcr, hout_mcr]
  omega

/-- Auxiliary loop for `phase0_creates_two_clocks_general`.  Given any reachable
all-phase-0 config with MCR + 3·(CR+2·Clock) ≥ 11, reaches a config with
Clock ≥ 2 while staying in phase 0.  Terminates because MCR+CR strictly
decreases at each step (MCR+MCR: −2+1=−1; CR+CR: MCR same, CR −2). -/
private lemma phase0_reach_two_clocks_aux
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach_init : (NonuniformMajority L K).Reachable init c)
    (hphase0 : ∀ a ∈ c, a.phase.val = 0)
    (hn : 11 ≤ init.card)
    (fuel : ℕ)
    (hfuel : roleCountG (L := L) (K := K) .mcr c +
      roleCountG (L := L) (K := K) .cr c ≤ fuel) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = 0) ∧
      2 ≤ roleCountG (L := L) (K := K) .clock final := by
  -- Get the potential bound
  have hpot := phase0_potential_bound (L := L) (K := K) init c hinit hreach_init hphase0 hn
  set MCR := roleCountG (L := L) (K := K) .mcr c with hMCR_def
  set CR := roleCountG (L := L) (K := K) .cr c with hCR_def
  set CLK := roleCountG (L := L) (K := K) .clock c with hCLK_def
  by_cases hclk : 2 ≤ CLK
  · -- Clock ≥ 2: done
    exact ⟨c, Relation.ReflTransGen.refl, hphase0, hclk⟩
  · push_neg at hclk
    -- Clock < 2, so MCR + 3·CR ≥ 10
    by_cases hcr : 2 ≤ CR
    · -- CR ≥ 2: do one CR+CR step
      rcases phase0_cr_step_general (L := L) (K := K) c hphase0
          (by rw [← hCR_def]; exact hcr) with
        ⟨c', hreach', hphase', hmcr_eq, hcr', hclock'⟩
      have hreach_init' : (NonuniformMajority L K).Reachable init c' :=
        Relation.ReflTransGen.trans hreach_init hreach'
      have hfuel' : roleCountG (L := L) (K := K) .mcr c' +
          roleCountG (L := L) (K := K) .cr c' ≤ fuel - 1 := by
        rw [hmcr_eq, hcr']; omega
      have hfuel_pos : 0 < fuel := by omega
      rcases phase0_reach_two_clocks_aux init c' hinit hreach_init' hphase' hn
        (fuel - 1) hfuel' with ⟨final, hreach_final, hphase_final, hclock_final⟩
      exact ⟨final, Relation.ReflTransGen.trans hreach' hreach_final,
        hphase_final, hclock_final⟩
    · -- CR < 2 and Clock < 2
      -- From bound: MCR + 3*(CR + 2*CLK) ≥ init.card ≥ 11 with CR ≤ 1, CLK ≤ 1
      -- MCR ≥ 11 - 3*(1 + 2) = 2, so MCR ≥ 2 (11 is the tight floor)
      push_neg at hcr
      have hmcr : 2 ≤ MCR := by omega
      -- Do one MCR+MCR step
      rcases phase0_mcr_step_general (L := L) (K := K) c hphase0
          (by rw [← hMCR_def]; exact hmcr) with
        ⟨c', hreach', hphase', hmcr', hcr', hclock'⟩
      have hreach_init' : (NonuniformMajority L K).Reachable init c' :=
        Relation.ReflTransGen.trans hreach_init hreach'
      have hfuel' : roleCountG (L := L) (K := K) .mcr c' +
          roleCountG (L := L) (K := K) .cr c' ≤ fuel - 1 := by
        rw [hmcr', hcr']; omega
      have hfuel_pos : 0 < fuel := by omega
      rcases phase0_reach_two_clocks_aux init c' hinit hreach_init' hphase' hn
        (fuel - 1) hfuel' with ⟨final, hreach_final, hphase_final, hclock_final⟩
      exact ⟨final, Relation.ReflTransGen.trans hreach' hreach_final,
        hphase_final, hclock_final⟩
termination_by fuel
decreasing_by all_goals omega

/-- From any reachable all-phase-0 config with enough agents, we can reach a
config with two applicable clocks while staying in phase 0.  Generalizes
`phase0_creates_two_clocks` by dropping the all-MCR precondition.
The bound 11 is the tight floor for the surplus-aware potential argument:
in the worst case (CR ≤ 1, Clock ≤ 1) the adjusted-potential invariant gives
MCR ≥ init.card − 9, so init.card ≥ 11 guarantees an MCR+MCR step is available. -/
private theorem phase0_creates_two_clocks_general
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase0 : ∀ a ∈ c, a.phase.val = 0)
    (hn : 11 ≤ init.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = 0) ∧
      (∃ i j, Protocol.Applicable final i j ∧ i.role = .clock ∧ j.role = .clock) := by
  rcases phase0_reach_two_clocks_aux (L := L) (K := K) init c hinit hreach hphase0 hn
      (roleCountG (L := L) (K := K) .mcr c + roleCountG (L := L) (K := K) .cr c)
      (le_refl _) with
    ⟨final, hreach_final, hphase_final, hclk_final⟩
  rcases exists_applicable_pair_of_roleCountG_ge_two
      (L := L) (K := K) .clock (c := final) hclk_final with
    ⟨i, j, happ, hi, hj⟩
  exact ⟨final, hreach_final, hphase_final, i, j, happ, hi, hj⟩

private theorem reachable_to_checkpoint
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hn : 11 ≤ init.card) :
    ∃ mid, (NonuniformMajority L K).Reachable c mid ∧
      (∀ a ∈ mid, a.phase.val = maxPhase mid) ∧
      1 ≤ maxPhase mid ∧
      (∃ i j, Protocol.Applicable mid i j ∧ i.role = .clock ∧ j.role = .clock) := by
  have hcard_eq : c.card = init.card :=
    Protocol.reachable_card_eq (P := NonuniformMajority L K) hreach
  have hn_c : 2 ≤ c.card := by omega
  rcases reachable_clockCount_ge_two_or_all_phase_zero
      (L := L) (K := K) init c hinit hreach with hcount | hphase0
  · have hmax_pos : 0 < maxPhase c ∨ maxPhase c = 0 := by omega
    rcases hmax_pos with hmax_pos | hmax_zero
    · rcases phase_epidemic_reachability_from_config (L := L) (K := K) c hn_c with
        ⟨mid, hreach_c_mid, hsync_mid, hmax_mono⟩
      have hphase_mid : 1 ≤ maxPhase mid := by omega
      have hcount_mid : 2 ≤ clockCount (L := L) (K := K) mid :=
        reachable_clockCount_ge_two_any (L := L) (K := K) hcount
          hreach_c_mid
      exact ⟨mid, hreach_c_mid, hsync_mid, hphase_mid,
        exists_applicable_clock_pair_of_clockCount_ge_two
          (L := L) (K := K) hcount_mid⟩
    · have hphase0 : ∀ a ∈ c, a.phase.val = 0 := by
        intro a ha
        have := phase_le_maxPhase_of_mem_chain (L := L) (K := K) ha
        omega
      have hp0 : (0 : ℕ) ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ) := by simp
      have hclocks := exists_applicable_clock_pair_of_clockCount_ge_two
        (L := L) (K := K) hcount
      rcases hclocks with ⟨i, j, happ, hi_clock, hj_clock⟩
      have hi_mem : i ∈ c := Multiset.mem_of_le happ (by simp)
      have hj_mem : j ∈ c := Multiset.mem_of_le happ (by simp)
      rcases timed_phase_progress_of_applicable_two_clocks
          (L := L) (K := K) c 0 hp0 i j happ
          (hphase0 i hi_mem) (hphase0 j hj_mem) hi_clock hj_clock with
        ⟨d, hreach_cd, a, ha_mem, ha_phase⟩
      have hn_d : 2 ≤ d.card := by
        rw [Protocol.reachable_card_eq (P := NonuniformMajority L K) hreach_cd]
        exact hn_c
      rcases phase_epidemic_reachability_from_config (L := L) (K := K) d hn_d with
        ⟨mid, hreach_d_mid, hsync_mid, hmax_mono⟩
      have hreach_c_mid : (NonuniformMajority L K).Reachable c mid :=
        Relation.ReflTransGen.trans hreach_cd hreach_d_mid
      have hphase_mid : 1 ≤ maxPhase mid := by
        have := phase_le_maxPhase_of_mem_chain (L := L) (K := K) ha_mem
        omega
      have hcount_d : 2 ≤ clockCount (L := L) (K := K) d :=
        reachable_clockCount_ge_two_any (L := L) (K := K) hcount hreach_cd
      have hcount_mid : 2 ≤ clockCount (L := L) (K := K) mid :=
        reachable_clockCount_ge_two_any (L := L) (K := K) hcount_d hreach_d_mid
      exact ⟨mid, hreach_c_mid, hsync_mid, hphase_mid,
        exists_applicable_clock_pair_of_clockCount_ge_two
          (L := L) (K := K) hcount_mid⟩
  · -- All agents have phase 0.  First reach a config with ≥ 2 clocks,
    -- then advance phase and sync via the epidemic.
    rcases phase0_creates_two_clocks_general
        (L := L) (K := K) init c hinit hreach hphase0 hn with
      ⟨c₀, hreach₀, hphase₀, i, j, happ, hi_clock, hj_clock⟩
    have hp0 : (0 : ℕ) ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ) := by simp
    have hi_mem : i ∈ c₀ := Multiset.mem_of_le happ (by simp)
    have hj_mem : j ∈ c₀ := Multiset.mem_of_le happ (by simp)
    rcases timed_phase_progress_of_applicable_two_clocks
        (L := L) (K := K) c₀ 0 hp0 i j happ
        (hphase₀ i hi_mem) (hphase₀ j hj_mem) hi_clock hj_clock with
      ⟨d, hreach_cd, a, ha_mem, ha_phase⟩
    have hreach_c_d : (NonuniformMajority L K).Reachable c d :=
      Relation.ReflTransGen.trans hreach₀ hreach_cd
    have hn_d : 2 ≤ d.card := by
      rw [Protocol.reachable_card_eq (P := NonuniformMajority L K) hreach_c_d]
      exact hn_c
    rcases phase_epidemic_reachability_from_config (L := L) (K := K) d hn_d with
      ⟨mid, hreach_d_mid, hsync_mid, hmax_mono⟩
    have hreach_c_mid : (NonuniformMajority L K).Reachable c mid :=
      Relation.ReflTransGen.trans hreach_c_d hreach_d_mid
    have hphase_mid : 1 ≤ maxPhase mid := by
      have := phase_le_maxPhase_of_mem_chain (L := L) (K := K) ha_mem
      omega
    have hcount_c₀ : 2 ≤ clockCount (L := L) (K := K) c₀ :=
      clockCount_ge_two_of_applicable_clocks (L := L) (K := K) happ hi_clock hj_clock
    have hcount_d : 2 ≤ clockCount (L := L) (K := K) d :=
      reachable_clockCount_ge_two_any (L := L) (K := K) hcount_c₀ hreach_cd
    have hcount_mid : 2 ≤ clockCount (L := L) (K := K) mid :=
      reachable_clockCount_ge_two_any (L := L) (K := K) hcount_d hreach_d_mid
    exact ⟨mid, hreach_c_mid, hsync_mid, hphase_mid,
      exists_applicable_clock_pair_of_clockCount_ge_two
        (L := L) (K := K) hcount_mid⟩

/-- The Phase-4 tie callback for the deterministic-liveness driver, discharged
under the paper's size hypothesis `init.card < 2 ^ L`.  At a Phase-4 locally
stable configuration `c'` reachable from a valid initial configuration with
`init.card < 2 ^ L`, the initial gap is zero (so the verdict is a tie) and every
agent already reports `.T`; hence `c'` itself is a Phase-4 tie endpoint. -/
private theorem phase4_tie_callback_of_size
    (init : Config (AgentState L K))
    (hinit : validInitial init)
    (hsize_init : init.card < 2 ^ L)
    (c' : Config (AgentState L K))
    (hreach_c' : (NonuniformMajority L K).Reachable init c')
    (hstable : phase4LocallyStable (L := L) (K := K) c')
    (hn_c' : 2 ≤ c'.card) :
    ∃ final, (NonuniformMajority L K).Reachable c' final ∧
      phase4TieEndpoint (L := L) (K := K) init final := by
  have hphase4 : ∀ a ∈ c', a.phase.val = 4 := hstable.1
  have hcard_c' : c'.card = init.card :=
    Protocol.reachable_card_eq (P := NonuniformMajority L K) hreach_c'
  have hsmall_n : c'.card < 2 ^ L := by rw [hcard_c']; exact hsize_init
  have hgap : initialGap init = 0 :=
    phase4LocallyStable_initialGap_zero (L := L) (K := K) init c' hinit hreach_c'
      hphase4 hn_c' hstable hsmall_n
  have hmajor : majorityVerdict init = outputTripleOfOutput .T :=
    majorityVerdict_eq_T_of_initialGap_zero (L := L) (K := K) init hgap
  have hphase_le : ∀ a ∈ c', a.phase.val ≤ 4 := fun a ha => by
    have := hphase4 a ha; omega
  have hout : ∀ a ∈ c', a.output = .T := fun a ha =>
    reachable_phase4_output_T (L := L) (K := K) init c' hinit hreach_c' hphase_le
      a ha (hphase4 a ha)
  exact ⟨c', Relation.ReflTransGen.refl,
    phase4LocallyStable_to_phase4TieEndpoint_of_outputs
      (L := L) (K := K) init c' hn_c' hstable hmajor hout⟩

/-- **Doty Theorem 3.1 (correctness), faithful nonuniform form**: under the
paper's two assumptions — the size hypothesis `init.card < 2 ^ L` (i.e.
`L = ⌈log₂ n⌉`) and the "sufficiently large `n`" hypothesis `11 ≤ init.card`
— the nonuniform majority protocol stably computes majority.

The size hypothesis is the paper's own assumption: the protocol stores the bias
exponent in `L` bits and the tie test `|gap| < 1` is valid exactly when
`card < 2 ^ L`.  Without it the unconditional statement is false (e.g. `L = 0`
forces `card < 1`, so any nonempty population breaks `phase4LocallyStable`'s
`|gap| ≤ card / 2^L < 1` argument).

The lower-bound hypothesis `11 ≤ init.card` is the formal counterpart of the
paper's "the bounds only hold for sufficiently large `n`": `11` is the exact
clock-formation floor of the deterministic role-allocation argument
(`reachable_to_checkpoint`).  Below it the all-MCR fuel is insufficient to
build the two clock agents that drive the phase clock, so the protocol's
clock-synchronized correctness route does not apply — exactly the small-`n`
regime the paper excludes.  Both hypotheses are jointly satisfiable
(`11 ≤ card < 2 ^ L` whenever `L ≥ 4`, i.e. `Θ(log n)` states). -/
theorem stable_majority_correct (L K : ℕ)
    (hlow : ∀ init : Config (AgentState L K), validInitial init → 11 ≤ init.card)
    (hsize : ∀ init : Config (AgentState L K), validInitial init → init.card < 2 ^ L) :
    Protocol.StablyComputes (NonuniformMajority L K) (doutPartition L K)
      (validInitial) (majorityVerdict) :=
  stable_majority_correct_of_majorityStableEndpoint_reachability
    (fun init hinit c hreach => by
      have hsize_init : init.card < 2 ^ L := hsize init hinit
      have hlow_init : 11 ≤ init.card := hlow init hinit
      have hcard_eq : c.card = init.card :=
        Protocol.reachable_card_eq (P := NonuniformMajority L K) hreach
      by_cases hn : 11 ≤ init.card
      · rcases reachable_to_checkpoint (L := L) (K := K) init c hinit hreach hn with
          ⟨mid, hreach_c_mid, hsync_mid, hphase_mid, hclocks_mid⟩
        have hreach_init_mid : (NonuniformMajority L K).Reachable init mid :=
          Relation.ReflTransGen.trans hreach hreach_c_mid
        have hn_mid : 2 ≤ mid.card := by
          rw [Protocol.reachable_card_eq (P := NonuniformMajority L K) hreach_c_mid]
          rw [hcard_eq]; omega
        rcases synchronized_checkpoint_deterministic_liveness
            (L := L) (K := K) init mid hinit hreach_init_mid hn_mid hsync_mid
            hphase_mid hclocks_mid
            (fun c' hreach_c' hstable => by
              have hn_c' : 2 ≤ c'.card := by
                rw [Protocol.reachable_card_eq (P := NonuniformMajority L K) hreach_c']
                omega
              exact phase4_tie_callback_of_size (L := L) (K := K) init hinit hsize_init
                c' hreach_c' hstable hn_c') with
          ⟨final, hreach_mid_final, hendpoint⟩
        exact ⟨final, Relation.ReflTransGen.trans hreach_c_mid hreach_mid_final, hendpoint⟩
      · -- Small-population regime `init.card ≤ 10`, excluded by the paper's
        -- "sufficiently large `n`" hypothesis `hlow_init : 11 ≤ init.card`.
        exact absurd hlow_init (by omega))

/-- Synonym. -/
theorem nonuniform_majority_correctness (L K : ℕ)
    (hlow : ∀ init : Config (AgentState L K), validInitial init → 11 ≤ init.card)
    (hsize : ∀ init : Config (AgentState L K), validInitial init → init.card < 2 ^ L) :
    Protocol.StablyComputes (NonuniformMajority L K) (doutPartition L K)
      (validInitial) (majorityVerdict) :=
  stable_majority_correct L K hlow hsize

end ExactMajority
