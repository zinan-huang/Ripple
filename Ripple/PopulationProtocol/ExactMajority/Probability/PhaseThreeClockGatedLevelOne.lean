import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockGatedLaw

/-!
# The gated level-one law: mixed active/inactive Clock pairs (N12, step 2 remainder)

PHASE3 Lemma P2, equation (25a). On the virtual continuation a Clock pair in the
regime (phases in `1..3`, Clock small bias `3`, i.e. `safeSmall` with neutral small
bias) in which at least one endpoint is already in Phase 3 behaves, in effective
minutes, exactly like an active pair: the inactive endpoint is initialized by the
wrapper's phase epidemic (`phaseInit 3` resets its minute to zero and its counter to
`50 (L + 1)`) and then the Phase-3 rule is dispatched in the same interaction. A pair
of two inactive Clocks is not dispatched at Phase 3 and never raises any front.

Contents.
* `phaseInit_one_clock`, `phaseInit_two_safe`, `phaseInit_three_clock`,
  `runInitsBetween_clock_up`: the initializer chain Phase 1/2 → 3 on a Clock.
* `phaseEpidemicUpdate_clock_regime`: the phase epidemic on a Clock pair in the regime
  keeps roles and small biases, sets both phases to the maximum, and preserves both
  effective minutes.
* `virtualRule_clock_pair_some_active`: the exact outcome of the virtual rule on a
  Clock pair with at least one active endpoint, in effective minutes.
* `frontCount_ruleUpdate_clock_pair_some_active`: the one-pair increment, `1 ≤ ℓ ≤ Q`.
* `GatedTick`: a raising tick with at least one active endpoint;
  `goodPairs_gatedTick_card_add`: its count is the ungated count minus `I (I - 1)`
  (equation (25a)); `goodPairs_gatedTick_eq_of_two_le`: for `2 ≤ ℓ` the gate is void.
* `gatedTick_conditional_law`: the conditional law of a gated tick given the pair log.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockGatedLevelOne

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual PhaseThreeClockGatedLaw

variable {L K : ℕ}

/-! ## The initializer chain on a Clock -/

theorem phaseInit_one_clock (a : AgentState L K) (hr : a.role = .clock) :
    phaseInit L K ⟨1, by omega⟩ a = { a with counter := ⟨50 * (L + 1), by omega⟩ } := by
  unfold phaseInit
  simp [hr]

theorem phaseInit_two_safe (a : AgentState L K) (hsb : a.smallBias.val = 3) :
    phaseInit L K ⟨2, by omega⟩ a = { a with opinions := ⟨2, by decide⟩ } := by
  unfold phaseInit
  simp [hsb]

theorem phaseInit_three_clock (a : AgentState L K) (hr : a.role = .clock) :
    phaseInit L K ⟨3, by omega⟩ a =
      { a with bias := .zero, minute := ⟨0, by omega⟩,
               counter := ⟨50 * (L + 1), by omega⟩ } := by
  unfold phaseInit
  simp [hr]

/-- The initializers run by the phase epidemic on a Clock with neutral small bias
climbing from `oldP ∈ {1, 2}` to `newP ≤ 3`. -/
theorem runInitsBetween_clock_up (oldP newP : ℕ) (h1 : 1 ≤ oldP) (hlt : oldP < newP)
    (h3 : newP ≤ 3) (a : AgentState L K) (hr : a.role = .clock) (hsb : a.smallBias.val = 3) :
    (runInitsBetween L K oldP newP a).role = .clock ∧
    (runInitsBetween L K oldP newP a).phase = a.phase ∧
    (runInitsBetween L K oldP newP a).smallBias = a.smallBias ∧
    (runInitsBetween L K oldP newP a).minute.val = (if newP = 3 then 0 else a.minute.val) ∧
    (newP = 3 → (runInitsBetween L K oldP newP a).counter.val = 50 * (L + 1)) := by
  have hold : oldP ≤ 2 := by omega
  interval_cases oldP <;> interval_cases newP
  · have hl : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 2) = [2] := by decide
    unfold runInitsBetween
    rw [hl]
    simp only [List.foldl]
    rw [dif_pos (by norm_num : (2 : ℕ) < 11), phaseInit_two_safe a hsb]
    simp [hr]
  · have hl : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 3) = [2, 3] := by decide
    unfold runInitsBetween
    rw [hl]
    simp only [List.foldl]
    rw [dif_pos (by norm_num : (2 : ℕ) < 11), dif_pos (by norm_num : (3 : ℕ) < 11),
      phaseInit_two_safe a hsb, phaseInit_three_clock _ (by simpa using hr)]
    simp [hr]
  · have hl : (List.range 11).filter (fun k => 2 < k ∧ k ≤ 3) = [3] := by decide
    unfold runInitsBetween
    rw [hl]
    simp only [List.foldl]
    rw [dif_pos (by norm_num : (3 : ℕ) < 11), phaseInit_three_clock a hr]
    simp [hr]

/-! ## The phase epidemic on a Clock pair in the regime -/

/-- The regime of a Clock during the clock analysis: a Clock in phase `1..3` with the
neutral small bias (`nonmain_zero` of `SeedProfile`). -/
structure ClockRegime (a : AgentState L K) : Prop where
  role : a.role = .clock
  phase_ge : 1 ≤ a.phase.val
  phase_le : a.phase.val ≤ 3
  small : a.smallBias.val = 3

theorem effMinute_eq_zero_of_lt_three (a : AgentState L K) (h : a.phase.val < 3) :
    effMinute a = 0 := by
  unfold effMinute
  rw [if_neg (by omega)]

theorem effMinute_eq_minute_of_three (a : AgentState L K) (h : a.phase.val = 3) :
    effMinute a = a.minute.val := by
  unfold effMinute
  rw [if_pos (by omega)]

/-- One initialized endpoint: the Clock `a` is raised to the phase `p` of its partner. -/
theorem initialized_clock_facts (a : AgentState L K) (ha : ClockRegime a) (p : Fin 11)
    (hlt : a.phase.val < p.val) (hp : p.val ≤ 3) :
    (runInitsBetween L K a.phase.val p.val { a with phase := p }).role = .clock ∧
    (runInitsBetween L K a.phase.val p.val { a with phase := p }).phase.val = p.val ∧
    (runInitsBetween L K a.phase.val p.val { a with phase := p }).smallBias = a.smallBias ∧
    effMinute (runInitsBetween L K a.phase.val p.val { a with phase := p }) = effMinute a := by
  obtain ⟨hr, hp1, -, hsb⟩ := ha
  have h := runInitsBetween_clock_up a.phase.val p.val hp1 hlt hp { a with phase := p }
    (by simpa using hr) (by simpa using hsb)
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  refine ⟨h1, by rw [h2], by simpa using h3, ?_⟩
  rw [effMinute_eq_zero_of_lt_three a (by omega)]
  unfold effMinute
  rw [h2]
  simp only []
  by_cases hp3 : p.val = 3
  · rw [if_pos (by omega), h4, if_pos hp3]
  · rw [if_neg (by omega)]

theorem phaseEpidemicUpdate_clock_regime (s t : AgentState L K)
    (hs : ClockRegime s) (ht : ClockRegime t) :
    (phaseEpidemicUpdate L K s t).1.role = .clock ∧
    (phaseEpidemicUpdate L K s t).2.role = .clock ∧
    (phaseEpidemicUpdate L K s t).1.phase.val = max s.phase.val t.phase.val ∧
    (phaseEpidemicUpdate L K s t).2.phase.val = max s.phase.val t.phase.val ∧
    (phaseEpidemicUpdate L K s t).1.smallBias = s.smallBias ∧
    (phaseEpidemicUpdate L K s t).2.smallBias = t.smallBias ∧
    effMinute (phaseEpidemicUpdate L K s t).1 = effMinute s ∧
    effMinute (phaseEpidemicUpdate L K s t).2 = effMinute t := by
  -- the two candidate outputs before the error test
  have key : ∀ s' t' : AgentState L K,
      s' = runInitsBetween L K s.phase.val (max s.phase t.phase).val
        { s with phase := max s.phase t.phase } →
      t' = runInitsBetween L K t.phase.val (max s.phase t.phase).val
        { t with phase := max s.phase t.phase } →
      s'.role = .clock ∧ t'.role = .clock ∧
      s'.phase.val = max s.phase.val t.phase.val ∧ t'.phase.val = max s.phase.val t.phase.val ∧
      s'.smallBias = s.smallBias ∧ t'.smallBias = t.smallBias ∧
      effMinute s' = effMinute s ∧ effMinute t' = effMinute t := by
    intro s' t' hs' ht'
    rcases lt_trichotomy s.phase.val t.phase.val with hlt | heq | hgt
    · have hmax : max s.phase t.phase = t.phase :=
        max_eq_right (Fin.le_iff_val_le_val.mpr hlt.le)
      have hmaxv : max s.phase.val t.phase.val = t.phase.val := max_eq_right hlt.le
      rw [hmax] at hs' ht'
      rw [runInitsBetween_self] at ht'
      obtain ⟨h1, h2, h3, h4⟩ := initialized_clock_facts s hs t.phase hlt ht.phase_le
      subst hs' ht'
      exact ⟨h1, ht.role, by rw [h2, hmaxv], by show t.phase.val = _; rw [hmaxv], h3, rfl,
        h4, rfl⟩
    · have hst : s.phase = t.phase := Fin.ext heq
      have hmax : max s.phase t.phase = s.phase := by rw [hst, max_self]
      have hmaxv : max s.phase.val t.phase.val = s.phase.val := by rw [heq, max_self]
      rw [hmax] at hs' ht'
      rw [runInitsBetween_self] at hs'
      rw [heq, runInitsBetween_self, hst] at ht'
      subst hs' ht'
      exact ⟨hs.role, ht.role, by show s.phase.val = _; rw [hmaxv],
        by show t.phase.val = _; rw [hmaxv, heq], rfl, rfl, rfl, rfl⟩
    · have hmax : max s.phase t.phase = s.phase :=
        max_eq_left (Fin.le_iff_val_le_val.mpr hgt.le)
      have hmaxv : max s.phase.val t.phase.val = s.phase.val := max_eq_left hgt.le
      rw [hmax] at hs' ht'
      rw [runInitsBetween_self] at hs'
      obtain ⟨h1, h2, h3, h4⟩ := initialized_clock_facts t ht s.phase hgt hs.phase_le
      subst hs' ht'
      exact ⟨hs.role, h1, by show s.phase.val = _; rw [hmaxv], by rw [h2, hmaxv], rfl, h3,
        rfl, h4⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := key _ _ rfl rfl
  have hmax3 : max s.phase.val t.phase.val ≤ 3 := max_le hs.phase_le ht.phase_le
  unfold phaseEpidemicUpdate
  simp only []
  split_ifs with h10
  · exfalso
    rcases h10 with ⟨-, h | h⟩
    · rw [h3] at h; omega
    · rw [h4] at h; omega
  · exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## The virtual rule on a Clock pair with an active endpoint -/

/-- The virtual rule on a pair is the virtual rule on the dispatched pair, when both
dispatched endpoints are Phase-3 Clocks and neither is at the cap counter branch. -/
theorem virtualRule_eq_virtualRule_dispatched (s t : AgentState L K)
    (h3 : (phaseEpidemicUpdate L K s t).1.phase.val = 3)
    (h3' : (phaseEpidemicUpdate L K s t).2.phase.val = 3)
    (hnc : ¬ CapCounterPair s t) :
    virtualRule s t =
      virtualRule (phaseEpidemicUpdate L K s t).1 (phaseEpidemicUpdate L K s t).2 := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3
    (phaseEpidemicUpdate L K s t).1 (phaseEpidemicUpdate L K s t).2 h3 h3'
  have hnc' : ¬ CapCounterPair (phaseEpidemicUpdate L K s t).1 (phaseEpidemicUpdate L K s t).2 := by
    intro h
    apply hnc
    unfold CapCounterPair at h ⊢
    rw [hepi] at h
    exact h
  unfold virtualRule
  rw [if_neg hnc, if_neg hnc', transition_eq_phase3_of_dispatch s t h3,
    transition_eq_phase3_of_dispatch _ _ (by rw [hepi]; exact h3), hepi]

/-- PHASE3 P2 at a mixed pair: in effective minutes, a Clock pair in the regime with
an active endpoint behaves exactly as an active pair (initialize, then copy or drip). -/
theorem virtualRule_clock_pair_some_active (s t : AgentState L K) (hK : 0 < K)
    (hs : ClockRegime s) (ht : ClockRegime t)
    (hact : s.phase.val = 3 ∨ t.phase.val = 3) :
    (virtualRule s t).1.role = .clock ∧ (virtualRule s t).2.role = .clock ∧
    (virtualRule s t).1.phase.val = 3 ∧ (virtualRule s t).2.phase.val = 3 ∧
    (virtualRule s t).1.minute.val =
      (if effMinute s ≠ effMinute t then max (effMinute s) (effMinute t)
        else if effMinute s < K * (L + 1) then effMinute s + 1 else effMinute s) ∧
    (virtualRule s t).2.minute.val =
      (if effMinute s ≠ effMinute t then max (effMinute s) (effMinute t)
        else effMinute t) := by
  obtain ⟨h1, h2, h3, h4, -, -, h7, h8⟩ := phaseEpidemicUpdate_clock_regime s t hs ht
  have hmax : max s.phase.val t.phase.val = 3 := by
    rcases hact with h | h
    · exact le_antisymm (max_le hs.phase_le ht.phase_le) (h ▸ le_max_left _ _)
    · exact le_antisymm (max_le hs.phase_le ht.phase_le) (h ▸ le_max_right _ _)
  rw [hmax] at h3 h4
  set s' := (phaseEpidemicUpdate L K s t).1 with hs'
  set t' := (phaseEpidemicUpdate L K s t).2 with ht'
  have hsm : s'.minute.val = effMinute s := by
    rw [← h7, effMinute_eq_minute_of_three s' h3]
  have htm : t'.minute.val = effMinute t := by
    rw [← h8, effMinute_eq_minute_of_three t' h4]
  have hv : virtualRule s t = virtualRule s' t' := by
    by_cases hboth : s.phase.val = 3 ∧ t.phase.val = 3
    · have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hboth.1 hboth.2
      rw [hs', ht', hepi]
    · apply virtualRule_eq_virtualRule_dispatched s t h3 h4
      intro hcap
      obtain ⟨-, -, -, -, hmin, hcapv⟩ := hcap
      have hpos : 0 < K * (L + 1) := Nat.mul_pos hK (Nat.succ_pos L)
      rcases hact with h | h
      · have htlt : t.phase.val < 3 := by
          rcases Nat.lt_or_ge t.phase.val 3 with h' | h'
          · exact h'
          · exact absurd ⟨h, by omega⟩ hboth
        have : t'.minute.val = 0 := by
          rw [htm, effMinute_eq_zero_of_lt_three t htlt]
        rw [ht'] at this
        rw [hmin] at hcapv
        omega
      · have hslt : s.phase.val < 3 := by
          rcases Nat.lt_or_ge s.phase.val 3 with h' | h'
          · exact h'
          · exact absurd ⟨by omega, h⟩ hboth
        have : s'.minute.val = 0 := by
          rw [hsm, effMinute_eq_zero_of_lt_three s hslt]
        rw [hs'] at this
        omega
  rw [hv]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := virtualRule_active_clock_pair s' t' h3 h4 h1 h2
  rw [hsm, htm] at a5 a6
  exact ⟨a1, a2, a3, a4, a5, a6⟩

/-! ## The one-pair increment with an active endpoint -/

variable {m : ℕ}

theorem frontCount_ruleUpdate_clock_pair_some_active (f : Fin m → AgentState L K)
    (hK : 0 < K) (i j : Fin m) (hij : i ≠ j)
    (hi : ClockRegime (f i)) (hj : ClockRegime (f j))
    (hact : (f i).phase.val = 3 ∨ (f j).phase.val = 3)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ K * (L + 1)) :
    frontCount (ruleUpdate virtualRule f i j) ℓ =
      frontCount f ℓ + if RaisingTick ℓ f i j then 1 else 0 := by
  obtain ⟨har, hbr, ha3, hb3, ham, hbm⟩ :=
    virtualRule_clock_pair_some_active (f i) (f j) hK hi hj hact
  have hsum := sum_update_pair (frontInd ℓ) f i j hij
    (virtualRule (f i) (f j)).1 (virtualRule (f i) (f j)).2
  rw [frontCount_eq_sum, frontCount_eq_sum]
  unfold ruleUpdate
  suffices hkey : frontInd ℓ (virtualRule (f i) (f j)).1 + frontInd ℓ (virtualRule (f i) (f j)).2 =
      frontInd ℓ (f i) + frontInd ℓ (f j) + if RaisingTick ℓ f i j then 1 else 0 by
    omega
  have hRT : RaisingTick ℓ f i j ↔
      (effMinute (f i) < ℓ ∧ ℓ ≤ effMinute (f j)) ∨
      (ℓ ≤ effMinute (f i) ∧ effMinute (f j) < ℓ) ∨
      (effMinute (f i) = ℓ - 1 ∧ effMinute (f j) = ℓ - 1) := by
    simp only [RaisingTick, belowSet, aboveSet, exactSet, Finset.mem_filter, Finset.mem_univ,
      true_and, hi.role, hj.role, not_le]
  have e1 : frontInd ℓ (f i) = if ℓ ≤ effMinute (f i) then 1 else 0 := by
    simp [frontInd, hi.role]
  have e2 : frontInd ℓ (f j) = if ℓ ≤ effMinute (f j) then 1 else 0 := by
    simp [frontInd, hj.role]
  have e3 : frontInd ℓ (virtualRule (f i) (f j)).1 =
      if ℓ ≤ (virtualRule (f i) (f j)).1.minute.val then 1 else 0 := by
    simp [frontInd, effMinute, har, ha3]
  have e4 : frontInd ℓ (virtualRule (f i) (f j)).2 =
      if ℓ ≤ (virtualRule (f i) (f j)).2.minute.val then 1 else 0 := by
    simp [frontInd, effMinute, hbr, hb3]
  have hRT' : (if RaisingTick ℓ f i j then (1 : ℕ) else 0) =
      if (effMinute (f i) < ℓ ∧ ℓ ≤ effMinute (f j)) ∨
        (ℓ ≤ effMinute (f i) ∧ effMinute (f j) < ℓ) ∨
        (effMinute (f i) = ℓ - 1 ∧ effMinute (f j) = ℓ - 1) then 1 else 0 :=
    if_congr hRT rfl rfl
  rw [e1, e2, e3, e4, hRT', ham, hbm]
  split_ifs <;> omega

/-! ## The gate: raising ticks with an active endpoint -/

/-- A raising tick with at least one active endpoint. Two inactive Clocks are never
dispatched at Phase 3; at level one every ordered inactive pair is a formal drip. -/
def GatedTick (ℓ : ℕ) (f : Fin m → AgentState L K) (i j : Fin m) : Prop :=
  RaisingTick ℓ f i j ∧ (3 ≤ (f i).phase.val ∨ 3 ≤ (f j).phase.val)

instance (ℓ : ℕ) (f : Fin m → AgentState L K) (i j : Fin m) :
    Decidable (GatedTick ℓ f i j) := by
  unfold GatedTick
  infer_instance

/-- Inactive Clock labels (`I` of PHASE3 (25a)). -/
def inactiveSet (f : Fin m → AgentState L K) : Finset (Fin m) :=
  Finset.univ.filter fun i => (f i).role = .clock ∧ (f i).phase.val < 3

def inactiveCount (f : Fin m → AgentState L K) : ℕ := (inactiveSet f).card

theorem goodPairs_raisingTick_one_eq (f : Fin m → AgentState L K) :
    goodPairs (RaisingTick 1) f =
      goodPairs (GatedTick 1) f ∪ (inactiveSet f).offDiag := by
  ext ⟨i, j⟩
  simp only [goodPairs, GatedTick, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_offDiag, inactiveSet]
  constructor
  · rintro ⟨hij, hR⟩
    by_cases hact : 3 ≤ (f i).phase.val ∨ 3 ≤ (f j).phase.val
    · exact Or.inl ⟨hij, hR, hact⟩
    · have hi3 : (f i).phase.val < 3 := by omega
      have hj3 : (f j).phase.val < 3 := by omega
      have hi : (f i).role = .clock := by
        rcases hR with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
          simp only [belowSet, aboveSet, exactSet, Finset.mem_filter, Finset.mem_univ,
            true_and] at h <;> exact h.1
      have hj : (f j).role = .clock := by
        rcases hR with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
          simp only [belowSet, aboveSet, exactSet, Finset.mem_filter, Finset.mem_univ,
            true_and] at h <;> exact h.1
      exact Or.inr ⟨⟨hi, hi3⟩, ⟨hj, hj3⟩, hij⟩
  · rintro (⟨hij, hR, -⟩ | ⟨⟨hi, hi3⟩, ⟨hj, hj3⟩, hij⟩)
    · exact ⟨hij, hR⟩
    · refine ⟨hij, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
      · simp only [exactSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hi, effMinute_eq_zero_of_lt_three _ hi3⟩
      · simp only [exactSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hj, effMinute_eq_zero_of_lt_three _ hj3⟩

/-- PHASE3 (25a): the gated level-one count is the ungated count minus `I (I - 1)`. -/
theorem goodPairs_gatedTick_card_add (f : Fin m → AgentState L K) :
    (goodPairs (GatedTick 1) f).card + inactiveCount f * (inactiveCount f - 1) =
      2 * frontCount f 1 * (clockCount f - frontCount f 1) +
        exactCount f 0 * (exactCount f 0 - 1) := by
  have hdisj : Disjoint (goodPairs (GatedTick 1) f) (inactiveSet f).offDiag := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ h1 h2
    simp only [goodPairs, GatedTick, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_offDiag, inactiveSet] at h1 h2
    rcases h1.2.2 with h | h
    · have := h2.1.2; omega
    · have := h2.2.1.2; omega
  have h := goodPairs_raisingTick_card f 1
  rw [goodPairs_raisingTick_one_eq, Finset.card_union_of_disjoint hdisj, Finset.offDiag_card] at h
  unfold inactiveCount
  rw [Nat.mul_sub_one]
  simpa using h

/-- For `2 ≤ ℓ` the gate is void: both endpoints of a raising tick are active. -/
theorem goodPairs_gatedTick_eq_of_two_le (f : Fin m → AgentState L K) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    goodPairs (GatedTick ℓ) f = goodPairs (RaisingTick ℓ) f := by
  ext ⟨i, j⟩
  simp only [goodPairs, GatedTick, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hij, hR, -⟩
    exact ⟨hij, hR⟩
  · rintro ⟨hij, hR⟩
    refine ⟨hij, hR, ?_⟩
    by_contra hact
    have hi := effMinute_eq_zero_of_lt_three (f i) (by omega)
    have hj := effMinute_eq_zero_of_lt_three (f j) (by omega)
    rcases hR with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      simp only [belowSet, aboveSet, exactSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at h <;> omega

open Classical in
/-- The conditional law of a gated tick given the pair log. -/
theorem gatedTick_conditional_law (init : Cfg L K) (hc : 2 ≤ init.card) (ℓ t : ℕ) :
    (law init)[fun ω =>
      if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
          GatedTick ℓ (auxLabels init virtualRule ω t) i j
      then (1 : ℝ) else 0 | pairLogFiltration L K t]
      =ᵐ[law init]
    (fun ω => ((goodPairs (GatedTick ℓ) (auxLabels init virtualRule ω t)).card : ℝ) /
      ((init.card : ℝ) * ((init.card : ℝ) - 1))) := by
  have h := aux_pair_conditional_probability init hc virtualRule (GatedTick ℓ) t
  convert h using 3 with ω
  congr!

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockGatedLevelOne

end
