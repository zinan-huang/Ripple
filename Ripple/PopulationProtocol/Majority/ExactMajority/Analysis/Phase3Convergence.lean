import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DriftPhaseOfDescent
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Scheduler
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.TransitionMonotonicity
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Phase0Convergence

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

variable {L K : ℕ}

def Phase3TiePre (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, 3 ≤ a.phase.val

def Phase3TiePost (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, 4 ≤ a.phase.val

/-! ### Auxiliary lemmas for the drift-phase construction -/

/-- `phaseBelowCount k c ≤ c.card`: the count of agents with phase < k is at most
the total population. -/
lemma phaseBelowCount_le_card (k : ℕ) (c : Config (AgentState L K)) :
    phaseBelowCount k c ≤ c.card := by
  unfold phaseBelowCount
  exact Multiset.card_le_card (Multiset.filter_le _ c)

/-- `Phase3TiePost c` holds iff `phaseBelowCount 4 c = 0`: all agents have phase ≥ 4
iff no agent has phase < 4. -/
lemma Phase3TiePost_iff_phaseBelowCount_zero (c : Config (AgentState L K)) :
    Phase3TiePost c ↔ phaseBelowCount 4 c = 0 := by
  unfold Phase3TiePost phaseBelowCount
  constructor
  · intro h
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro a ha
    simp only [decide_eq_true_eq, not_lt]
    exact h a ha
  · intro h a ha
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil] at h
    have := h a ha
    simp only [decide_eq_true_eq, not_lt] at this
    exact this

/-- Under `Phase3TiePre` and `¬Phase3TiePost`, there exists an agent with phase
exactly 3 (phase < 4). This is immediate from the definitions. -/
lemma exists_phase3_agent (c : Config (AgentState L K))
    (hpre : Phase3TiePre c) (hnotpost : ¬Phase3TiePost c) :
    ∃ a ∈ c, a.phase.val = 3 := by
  rw [Phase3TiePost] at hnotpost
  push Not at hnotpost
  obtain ⟨a, ha_mem, ha_phase⟩ := hnotpost
  have h3 := hpre a ha_mem
  exact ⟨a, ha_mem, by omega⟩

/-- Under `Phase3TiePre` and `¬Phase3TiePost`, `phaseBelowCount 4 c ≥ 1`:
at least one agent has phase < 4. -/
lemma phaseBelowCount_pos_of_not_post (c : Config (AgentState L K))
    (_hpre : Phase3TiePre c) (hnotpost : ¬Phase3TiePost c) :
    0 < phaseBelowCount 4 c := by
  rw [Phase3TiePost_iff_phaseBelowCount_zero] at hnotpost
  exact Nat.pos_of_ne_zero hnotpost

/-! ### Local proofs of Transition phase ≥ max for the pair -/

set_option maxHeartbeats 2000000 in
/-- Local version: after Transition, the first output's phase ≥ max of input phases.
Uses `phaseEpidemicUpdate_left_phase_ge_max_api` + dispatch monotonicity. -/
private theorem Transition_left_phase_ge_pair_max' (s t : AgentState L K) :
    max s.phase.val t.phase.val ≤ (Transition L K s t).1.phase.val := by
  have h_ep := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
  unfold Transition
  rcases hpe : phaseEpidemicUpdate L K s t with ⟨s', t'⟩
  simp only [hpe] at h_ep ⊢
  let out :=
    match s'.phase with
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
    | _ => (s', t')
  change max s.phase.val t.phase.val ≤ (finishPhase10Entry L K s' out.1).phase.val
  have hdispatch : s'.phase.val ≤ out.1.phase.val := by
    dsimp [out]
    rcases h_phase : s'.phase with ⟨n, hn⟩
    match n, hn with
    | 0, _ => simp
    | 1, _ => simpa [h_phase] using (Phase1Transition_phase_nondec L K s' t').1
    | 2, _ => simpa [h_phase] using (Phase2Transition_phase_nondec L K s' t').1
    | 3, _ => simpa [h_phase] using (Phase3Transition_phase_nondec L K s' t').1
    | 4, _ => simpa [h_phase] using (Phase4Transition_phase_nondec L K s' t').1
    | 5, _ => simpa [h_phase] using (Phase5Transition_phase_nondec L K s' t').1
    | 6, _ => simpa [h_phase] using (Phase6Transition_phase_nondec L K s' t').1
    | 7, _ => simpa [h_phase] using (Phase7Transition_phase_nondec L K s' t').1
    | 8, _ => simpa [h_phase] using (Phase8Transition_phase_nondec L K s' t').1
    | 9, _ => simpa [h_phase] using (Phase9Transition_phase_nondec L K s' t').1
    | 10, _ => simpa [h_phase] using (Phase10Transition_phase_nondec L K s' t').1
    | n + 11, hn => omega
  exact le_trans h_ep (by simpa using hdispatch)

set_option maxHeartbeats 2000000 in
/-- Local version: after Transition, the second output's phase ≥ max of input phases. -/
private theorem Transition_right_phase_ge_pair_max' (s t : AgentState L K) :
    max s.phase.val t.phase.val ≤ (Transition L K s t).2.phase.val := by
  have h_ep := phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) s t
  unfold Transition
  rcases hpe : phaseEpidemicUpdate L K s t with ⟨s', t'⟩
  simp only [hpe] at h_ep ⊢
  let out :=
    match s'.phase with
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
    | _ => (s', t')
  change max s.phase.val t.phase.val ≤ (finishPhase10Entry L K t' out.2).phase.val
  have hdispatch : t'.phase.val ≤ out.2.phase.val := by
    dsimp [out]
    rcases h_phase : s'.phase with ⟨n, hn⟩
    match n, hn with
    | 0, _ => simpa [h_phase] using (Phase0Transition_phase_nondec L K s' t').2
    | 1, _ => simpa [h_phase] using (Phase1Transition_phase_nondec L K s' t').2
    | 2, _ => simpa [h_phase] using (Phase2Transition_phase_nondec L K s' t').2
    | 3, _ => simpa [h_phase] using (Phase3Transition_phase_nondec L K s' t').2
    | 4, _ => simpa [h_phase] using (Phase4Transition_phase_nondec L K s' t').2
    | 5, _ => simpa [h_phase] using (Phase5Transition_phase_nondec L K s' t').2
    | 6, _ => simpa [h_phase] using (Phase6Transition_phase_nondec L K s' t').2
    | 7, _ => simpa [h_phase] using (Phase7Transition_phase_nondec L K s' t').2
    | 8, _ => simpa [h_phase] using (Phase8Transition_phase_nondec L K s' t').2
    | 9, _ => simpa [h_phase] using (Phase9Transition_phase_nondec L K s' t').2
    | 10, _ => simpa [h_phase] using (Phase10Transition_phase_nondec L K s' t').2
    | n + 11, hn => omega
  exact le_trans h_ep (by simpa using hdispatch)

/-! ### Phase-3 epidemic descent -/

/-- When one agent has phase < 4 and the other has phase ≥ 4, both Transition
outputs have phase ≥ 4 (from the epidemic mechanism), so the pair-level
phaseBelowCount 4 strictly decreases. -/
private lemma Transition_phaseBelowCount4_pair_lt
    (r₁ r₂ : AgentState L K)
    (hr₁ : r₁.phase.val < 4) (hr₂ : 4 ≤ r₂.phase.val) :
    phaseBelowCount 4
      ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} : Config (AgentState L K)) <
    phaseBelowCount 4 ({r₁, r₂} : Config (AgentState L K)) := by
  -- Both outputs have phase ≥ max(r₁.phase, r₂.phase) ≥ 4
  have hmax : 4 ≤ max r₁.phase.val r₂.phase.val :=
    le_trans hr₂ (le_max_right _ _)
  have hout1 : 4 ≤ (Transition L K r₁ r₂).1.phase.val :=
    le_trans hmax (Transition_left_phase_ge_pair_max' (L := L) (K := K) r₁ r₂)
  have hout2 : 4 ≤ (Transition L K r₁ r₂).2.phase.val :=
    le_trans hmax (Transition_right_phase_ge_pair_max' (L := L) (K := K) r₁ r₂)
  -- phaseBelowCount 4 of output pair = 0
  show phaseBelowCount 4 ({(Transition L K r₁ r₂).1} + {(Transition L K r₁ r₂).2}) <
    phaseBelowCount 4 ({r₁} + {r₂})
  rw [phaseBelowCount_add, phaseBelowCount_add]
  simp only [phaseBelowCount, Multiset.filter_singleton]
  simp only [decide_eq_true_eq]
  have h1 : ¬ (Transition L K r₁ r₂).1.phase.val < 4 := not_lt.mpr hout1
  have h2 : ¬ (Transition L K r₁ r₂).2.phase.val < 4 := not_lt.mpr hout2
  simp [h1, h2, hr₁, not_lt.mpr hr₂]

/-- When one agent has phase < 4 and the other has phase ≥ 4 (in either order),
both Transition outputs have phase ≥ 4. -/
private lemma Transition_phaseBelowCount4_pair_lt'
    (r₁ r₂ : AgentState L K)
    (h : (r₁.phase.val < 4 ∧ 4 ≤ r₂.phase.val) ∨
         (4 ≤ r₁.phase.val ∧ r₂.phase.val < 4)) :
    phaseBelowCount 4
      ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} : Config (AgentState L K)) <
    phaseBelowCount 4 ({r₁, r₂} : Config (AgentState L K)) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Transition_phaseBelowCount4_pair_lt r₁ r₂ h1 h2
  · -- Same argument with roles swapped
    have hmax : 4 ≤ max r₁.phase.val r₂.phase.val :=
      le_trans h1 (le_max_left _ _)
    have hout1 : 4 ≤ (Transition L K r₁ r₂).1.phase.val :=
      le_trans hmax (Transition_left_phase_ge_pair_max' (L := L) (K := K) r₁ r₂)
    have hout2 : 4 ≤ (Transition L K r₁ r₂).2.phase.val :=
      le_trans hmax (Transition_right_phase_ge_pair_max' (L := L) (K := K) r₁ r₂)
    show phaseBelowCount 4 ({(Transition L K r₁ r₂).1} + {(Transition L K r₁ r₂).2}) <
      phaseBelowCount 4 ({r₁} + {r₂})
    rw [phaseBelowCount_add, phaseBelowCount_add]
    simp only [phaseBelowCount, Multiset.filter_singleton]
    simp only [decide_eq_true_eq]
    have h1' : ¬ (Transition L K r₁ r₂).1.phase.val < 4 := not_lt.mpr hout1
    have h2' : ¬ (Transition L K r₁ r₂).2.phase.val < 4 := not_lt.mpr hout2
    simp [h1', h2', h2, not_lt.mpr h1]

/-- Config-level phaseBelowCount 4 strictly decreases when a "mixed" pair interacts. -/
private lemma phaseBelowCount4_config_decrease
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (h_sub : {r₁, r₂} ≤ c)
    (h : (r₁.phase.val < 4 ∧ 4 ≤ r₂.phase.val) ∨
         (4 ≤ r₁.phase.val ∧ r₂.phase.val < 4)) :
    phaseBelowCount 4
      (c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}) <
    phaseBelowCount 4 c := by
  have h_restore : c - {r₁, r₂} + {r₁, r₂} = c := Multiset.sub_add_cancel h_sub
  have h_pair_lt := Transition_phaseBelowCount4_pair_lt' r₁ r₂ h
  calc phaseBelowCount 4
        (c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2})
      = phaseBelowCount 4 (c - {r₁, r₂}) + phaseBelowCount 4
          {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := phaseBelowCount_add _ _ _
    _ < phaseBelowCount 4 (c - {r₁, r₂}) + phaseBelowCount 4 {r₁, r₂} :=
        Nat.add_lt_add_left h_pair_lt _
    _ = phaseBelowCount 4 (c - {r₁, r₂} + {r₁, r₂}) := (phaseBelowCount_add _ _ _).symm
    _ = phaseBelowCount 4 c := by rw [h_restore]

/-- Auxiliary: distinct members of a multiset form an applicable pair. -/
private lemma applicable_of_mem_ne {c : Config (AgentState L K)}
    {a b : AgentState L K} (ha : a ∈ c) (hb : b ∈ c) (hab : a ≠ b) :
    Protocol.Applicable c a b := by
  rw [Protocol.Applicable]
  rw [Multiset.le_iff_count]
  intro x
  by_cases hxa : x = a
  · subst x
    have ha_pos : 0 < Multiset.count a c := Multiset.count_pos.2 ha
    simp [hab, Nat.succ_le_iff, ha_pos]
  · by_cases hxb : x = b
    · subst x
      have hb_pos : 0 < Multiset.count b c := Multiset.count_pos.2 hb
      simp [hxa, Nat.succ_le_iff, hb_pos]
    · simp [hxa, hxb]

/-- The scheduled step for an applicable "mixed" pair maps into the descent target. -/
private lemma scheduledStep_mixed_in_target
    (c : Config (AgentState L K))
    (r₁ r₂ : AgentState L K)
    (hr₁ : r₁ ∈ c) (hr₂ : r₂ ∈ c) (hne : r₁ ≠ r₂)
    (h : (r₁.phase.val < 4 ∧ 4 ≤ r₂.phase.val) ∨
         (4 ≤ r₁.phase.val ∧ r₂.phase.val < 4)) :
    (NonuniformMajority L K).scheduledStep c (r₁, r₂) ∈
      {c' | phaseBelowCount 4 c' < phaseBelowCount 4 c} := by
  have happ : Protocol.Applicable c r₁ r₂ := applicable_of_mem_ne hr₁ hr₂ hne
  simp only [Set.mem_setOf_eq, Protocol.scheduledStep]
  -- stepOrSelf with applicable pair = c - {r₁,r₂} + {output pair}
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ =
    c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
    unfold Protocol.stepOrSelf NonuniformMajority
    simp only [if_pos happ]
  rw [hstep]
  exact phaseBelowCount4_config_decrease c r₁ r₂ happ h

/-- When `¬Phase3TiePost c`, there exists an agent with phase < 4. -/
lemma exists_phase_lt4_agent (c : Config (AgentState L K))
    (hnotpost : ¬Phase3TiePost c) :
    ∃ a ∈ c, a.phase.val < 4 := by
  rw [Phase3TiePost] at hnotpost
  push_neg at hnotpost
  obtain ⟨a, ha_mem, ha_phase⟩ := hnotpost
  exact ⟨a, ha_mem, by omega⟩

lemma phase3_descent_prob (c : Config (AgentState L K))
    (hn : 8 ≤ c.card) (hpre : Phase3TiePre c)
    (hnotpost : ¬Phase3TiePost c)
    (h_source : ∃ a ∈ c, 4 ≤ a.phase.val) :
    (NonuniformMajority L K).transitionKernel c
      {c' | phaseBelowCount 4 c' < phaseBelowCount 4 c} ≥
    ENNReal.ofReal (2 / ((c.card : ℝ) * ((c.card : ℝ) - 1))) := by
  -- Step 1: Extract witnesses
  obtain ⟨a, ha_mem, ha_phase⟩ := exists_phase3_agent c hpre hnotpost
  obtain ⟨b, hb_mem, hb_phase⟩ := h_source
  have hab : a ≠ b := by intro heq; subst heq; omega
  have hc : 2 ≤ c.card := by omega
  -- Step 2: Define the "good" set as just {(a, b), (b, a)}
  set good : Set (AgentState L K × AgentState L K) :=
    {(a, b), (b, a)} with good_def
  -- Step 3: Apply stepDistOrSelf_toMeasure_ge
  have h_target := stepDistOrSelf_toMeasure_ge c hc
    {c' | phaseBelowCount 4 c' < phaseBelowCount 4 c}
    good
    (by
      intro pair hpair
      simp only [good_def, Set.mem_insert_iff, Set.mem_singleton_iff] at hpair
      rcases hpair with rfl | rfl
      · exact scheduledStep_mixed_in_target c a b ha_mem hb_mem hab
          (Or.inl ⟨by omega, hb_phase⟩)
      · exact scheduledStep_mixed_in_target c b a hb_mem ha_mem hab.symm
          (Or.inr ⟨hb_phase, by omega⟩))
  -- Step 4: Bound the interactionPMF.toMeasure of good from below
  -- transitionKernel c = stepDistOrSelf c . toMeasure
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ ≥ _
  calc ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | phaseBelowCount 4 c' < phaseBelowCount 4 c}
      ≥ (c.interactionPMF hc).toMeasure good := h_target
    _ ≥ (c.interactionPMF hc) (a, b) + (c.interactionPMF hc) (b, a) := by
        -- toMeasure of {(a,b), (b,a)} = sum of the PMF values (disjoint singletons)
        have hab_ne : (a, b) ≠ (b, a) := by
          intro h; exact hab (Prod.mk.inj h).1
        -- {(a,b), (b,a)} = {(a,b)} ∪ {(b,a)}
        have hpair : ({(a, b), (b, a)} : Set _) = {(a, b)} ∪ {(b, a)} := by
          ext x; simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]
        have h_disj : Disjoint ({(a, b)} : Set _) {(b, a)} :=
          Set.disjoint_singleton.mpr hab_ne
        rw [good_def, hpair, measure_union h_disj
          (DiscreteMeasurableSpace.forall_measurableSet _),
          PMF.toMeasure_apply_singleton _ _ (DiscreteMeasurableSpace.forall_measurableSet _),
          PMF.toMeasure_apply_singleton _ _ (DiscreteMeasurableSpace.forall_measurableSet _)]
    _ ≥ ENNReal.ofReal (2 / ((c.card : ℝ) * ((c.card : ℝ) - 1))) := by
        -- PMF value = interactionProb = interactionCount / totalPairs
        have hpmf_ab : (c.interactionPMF hc) (a, b) = c.interactionProb a b := rfl
        have hpmf_ba : (c.interactionPMF hc) (b, a) = c.interactionProb b a := rfl
        rw [hpmf_ab, hpmf_ba]
        simp only [Config.interactionProb, Config.interactionCount, hab, hab.symm, ite_false]
        -- interactionCount a b = count a * count b ≥ 1
        have ha_count : 0 < c.count a := Multiset.count_pos.mpr ha_mem
        have hb_count : 0 < c.count b := Multiset.count_pos.mpr hb_mem
        have h_ab : 1 ≤ c.count a * c.count b :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        have h_ba : 1 ≤ c.count b * c.count a :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        -- Each term ≥ 1 / totalPairs
        have h1 : (↑(c.count a * c.count b) : ENNReal) /
            (c.totalPairs : ENNReal) ≥ 1 / (c.totalPairs : ENNReal) := by
          apply ENNReal.div_le_div_right
          exact_mod_cast h_ab
        have h2 : (↑(c.count b * c.count a) : ENNReal) /
            (c.totalPairs : ENNReal) ≥ 1 / (c.totalPairs : ENNReal) := by
          apply ENNReal.div_le_div_right
          exact_mod_cast h_ba
        -- Sum ≥ 2 / totalPairs = 2 / (n * (n-1))
        calc (↑(c.count a * c.count b) : ENNReal) /
                (c.totalPairs : ENNReal) +
              (↑(c.count b * c.count a) : ENNReal) /
                (c.totalPairs : ENNReal)
            ≥ 1 / (c.totalPairs : ENNReal) + 1 / (c.totalPairs : ENNReal) :=
              add_le_add h1 h2
          _ = 2 / (c.totalPairs : ENNReal) := by
              rw [show (1 : ENNReal) / c.totalPairs + 1 / c.totalPairs =
                (1 + 1) / c.totalPairs from by
                rw [ENNReal.add_div]
              ]
              norm_num
          _ = ENNReal.ofReal (2 / ((c.card : ℝ) * ((c.card : ℝ) - 1))) := by
              -- totalPairs = card * (card - 1)
              -- We prove this by converting both sides to ENNReal
              -- LHS: 2 / ↑(c.card * (c.card - 1))
              -- RHS: ENNReal.ofReal (2 / (c.card * (c.card - 1)))
              have hcard_pos : (0 : ℝ) < c.card :=
                Nat.cast_pos.mpr (by omega)
              have hcard_sub_pos : (0 : ℝ) < (c.card : ℝ) - 1 := by
                have h8 : (8 : ℝ) ≤ c.card := by exact_mod_cast hn
                linarith
              have hprod_pos : (0 : ℝ) < (c.card : ℝ) * ((c.card : ℝ) - 1) :=
                mul_pos hcard_pos hcard_sub_pos
              -- Convert RHS
              rw [ENNReal.ofReal_div_of_pos hprod_pos]
              congr 1
              · exact (ENNReal.ofReal_ofNat 2).symm
              · -- ↑c.totalPairs = ENNReal.ofReal (c.card * (c.card - 1))
                unfold Config.totalPairs
                have h1le : 1 ≤ c.card := by omega
                rw [show (c.card : ℝ) * ((c.card : ℝ) - 1) =
                    ((c.card * (c.card - 1) : ℕ) : ℝ) from by
                  push_cast [Nat.cast_sub h1le]; ring]
                exact (ENNReal.ofReal_natCast _).symm

/-- Generalized descent: no Phase3TiePre needed, only ¬Phase3TiePost and source. -/
lemma phase3_descent_prob' (c : Config (AgentState L K))
    (hn : 8 ≤ c.card)
    (hnotpost : ¬Phase3TiePost c)
    (h_source : ∃ a ∈ c, 4 ≤ a.phase.val) :
    (NonuniformMajority L K).transitionKernel c
      {c' | phaseBelowCount 4 c' < phaseBelowCount 4 c} ≥
    ENNReal.ofReal (2 / ((c.card : ℝ) * ((c.card : ℝ) - 1))) := by
  -- Step 1: Extract witnesses — use exists_phase_lt4_agent instead of Phase3TiePre
  obtain ⟨a, ha_mem, ha_phase⟩ := exists_phase_lt4_agent c hnotpost
  obtain ⟨b, hb_mem, hb_phase⟩ := h_source
  have hab : a ≠ b := by intro heq; subst heq; omega
  have hc : 2 ≤ c.card := by omega
  -- Step 2: Define the "good" set as just {(a, b), (b, a)}
  set good : Set (AgentState L K × AgentState L K) :=
    {(a, b), (b, a)} with good_def
  -- Step 3: Apply stepDistOrSelf_toMeasure_ge
  have h_target := stepDistOrSelf_toMeasure_ge c hc
    {c' | phaseBelowCount 4 c' < phaseBelowCount 4 c}
    good
    (by
      intro pair hpair
      simp only [good_def, Set.mem_insert_iff, Set.mem_singleton_iff] at hpair
      rcases hpair with rfl | rfl
      · exact scheduledStep_mixed_in_target c a b ha_mem hb_mem hab
          (Or.inl ⟨ha_phase, hb_phase⟩)
      · exact scheduledStep_mixed_in_target c b a hb_mem ha_mem hab.symm
          (Or.inr ⟨hb_phase, ha_phase⟩))
  -- Step 4: Same PMF bound as phase3_descent_prob
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ ≥ _
  calc ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | phaseBelowCount 4 c' < phaseBelowCount 4 c}
      ≥ (c.interactionPMF hc).toMeasure good := h_target
    _ ≥ (c.interactionPMF hc) (a, b) + (c.interactionPMF hc) (b, a) := by
        have hab_ne : (a, b) ≠ (b, a) := by
          intro h; exact hab (Prod.mk.inj h).1
        have hpair : ({(a, b), (b, a)} : Set _) = {(a, b)} ∪ {(b, a)} := by
          ext x; simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]
        have h_disj : Disjoint ({(a, b)} : Set _) {(b, a)} :=
          Set.disjoint_singleton.mpr hab_ne
        rw [good_def, hpair, measure_union h_disj
          (DiscreteMeasurableSpace.forall_measurableSet _),
          PMF.toMeasure_apply_singleton _ _ (DiscreteMeasurableSpace.forall_measurableSet _),
          PMF.toMeasure_apply_singleton _ _ (DiscreteMeasurableSpace.forall_measurableSet _)]
    _ ≥ ENNReal.ofReal (2 / ((c.card : ℝ) * ((c.card : ℝ) - 1))) := by
        have hpmf_ab : (c.interactionPMF hc) (a, b) = c.interactionProb a b := rfl
        have hpmf_ba : (c.interactionPMF hc) (b, a) = c.interactionProb b a := rfl
        rw [hpmf_ab, hpmf_ba]
        simp only [Config.interactionProb, Config.interactionCount, hab, hab.symm, ite_false]
        have ha_count : 0 < c.count a := Multiset.count_pos.mpr ha_mem
        have hb_count : 0 < c.count b := Multiset.count_pos.mpr hb_mem
        have h_ab : 1 ≤ c.count a * c.count b :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        have h_ba : 1 ≤ c.count b * c.count a :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        have h1 : (↑(c.count a * c.count b) : ENNReal) /
            (c.totalPairs : ENNReal) ≥ 1 / (c.totalPairs : ENNReal) := by
          apply ENNReal.div_le_div_right
          exact_mod_cast h_ab
        have h2 : (↑(c.count b * c.count a) : ENNReal) /
            (c.totalPairs : ENNReal) ≥ 1 / (c.totalPairs : ENNReal) := by
          apply ENNReal.div_le_div_right
          exact_mod_cast h_ba
        calc (↑(c.count a * c.count b) : ENNReal) /
                (c.totalPairs : ENNReal) +
              (↑(c.count b * c.count a) : ENNReal) /
                (c.totalPairs : ENNReal)
            ≥ 1 / (c.totalPairs : ENNReal) + 1 / (c.totalPairs : ENNReal) :=
              add_le_add h1 h2
          _ = 2 / (c.totalPairs : ENNReal) := by
              rw [show (1 : ENNReal) / c.totalPairs + 1 / c.totalPairs =
                (1 + 1) / c.totalPairs from by
                rw [ENNReal.add_div]
              ]
              norm_num
          _ = ENNReal.ofReal (2 / ((c.card : ℝ) * ((c.card : ℝ) - 1))) := by
              have hcard_pos : (0 : ℝ) < c.card :=
                Nat.cast_pos.mpr (by omega)
              have hcard_sub_pos : (0 : ℝ) < (c.card : ℝ) - 1 := by
                have h8 : (8 : ℝ) ≤ c.card := by exact_mod_cast hn
                linarith
              have hprod_pos : (0 : ℝ) < (c.card : ℝ) * ((c.card : ℝ) - 1) :=
                mul_pos hcard_pos hcard_sub_pos
              rw [ENNReal.ofReal_div_of_pos hprod_pos]
              congr 1
              · exact (ENNReal.ofReal_ofNat 2).symm
              · unfold Config.totalPairs
                have h1le : 1 ≤ c.card := by omega
                rw [show (c.card : ℝ) * ((c.card : ℝ) - 1) =
                    ((c.card * (c.card - 1) : ℕ) : ℝ) from by
                  push_cast [Nat.cast_sub h1le]; ring]
                exact (ENNReal.ofReal_natCast _).symm

/-! ### Extended potential and convergence

We define an ℝ≥0∞-valued potential that is `⊤` for configs without epidemic
source (no agent with phase ≥ 4). This makes the drift bound trivially hold
for such configs (r · ⊤ = ⊤ for r > 0), while the actual descent argument
only needs the source + ¬Phase3TiePost case. -/

/-- Source predicate: at least one agent has phase ≥ 4. -/
def hasSource (c : Config (AgentState L K)) : Prop :=
  ∃ a ∈ c, 4 ≤ a.phase.val

/-- Source is preserved by the one-step stochastic support: phase monotonicity
ensures that once an agent reaches phase ≥ 4, it stays there. -/
lemma hasSource_preserved_by_stepDistOrSelf
    (c c' : Config (AgentState L K))
    (hc : hasSource c) :
    c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → hasSource c' := by
  intro hsupp
  obtain ⟨a, ha_mem, ha_phase⟩ := hc
  -- c' is reachable from c in one step
  have hreach := Protocol.stepDistOrSelf_support_reachable
    (NonuniformMajority L K) c c' hsupp
  -- Phase monotonicity: a's phase only increases along reachable configs
  -- Use: every agent in c' either comes from c (with phase ≥ original) or
  -- is an output of Transition (with phase ≥ max of inputs ≥ original)
  -- Instead of unfolding, use the existing phase monotonicity on the step structure
  unfold Protocol.stepDistOrSelf at hsupp
  split_ifs at hsupp with h_size
  · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ hsupp
    subst heq
    -- c' = scheduledStep c (r₁,r₂)
    show hasSource (Protocol.scheduledStep (NonuniformMajority L K) c (r₁, r₂))
    unfold Protocol.scheduledStep Protocol.stepOrSelf
    split_ifs with h_app
    · -- Applicable: c' = c - {r₁,r₂} + {δ(r₁,r₂).1, δ(r₁,r₂).2}
      show ∃ a' ∈ c - {r₁, r₂} + {((NonuniformMajority L K).δ r₁ r₂).1,
        ((NonuniformMajority L K).δ r₁ r₂).2}, 4 ≤ a'.phase.val
      change ∃ a' ∈ c - {r₁, r₂} + {(Transition L K r₁ r₂).1,
        (Transition L K r₁ r₂).2}, 4 ≤ a'.phase.val
      by_cases ha_r1 : a = r₁
      · subst ha_r1
        refine ⟨(Transition L K a r₂).1, ?_, ?_⟩
        · exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_cons_self _ _))
        · exact le_trans ha_phase (Transition_phase_monotone (L := L) (K := K) a r₂).1
      · by_cases ha_r2 : a = r₂
        · subst ha_r2
          refine ⟨(Transition L K r₁ a).2, ?_, ?_⟩
          · exact Multiset.mem_add.mpr (Or.inr (by
              simp only [Multiset.insert_eq_cons]
              exact Multiset.mem_cons.mpr (Or.inr (Multiset.mem_singleton.mpr rfl))))
          · exact le_trans ha_phase (Transition_phase_monotone (L := L) (K := K) r₁ a).2
        · have ha_rem : a ∈ c - {r₁, r₂} := by
            rw [Multiset.mem_sub]
            simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
            simp [ha_r1, ha_r2]
            exact Multiset.count_pos.mpr ha_mem
          exact ⟨a, Multiset.mem_add.mpr (Or.inl ha_rem), ha_phase⟩
    · exact ⟨a, ha_mem, ha_phase⟩
  · rw [PMF.mem_support_pure_iff] at hsupp
    subst hsupp
    exact ⟨a, ha_mem, ha_phase⟩

/-- Source is maintained along any finite Markov-chain execution. -/
lemma hasSource_transitionKernel_pow_zero
    (c₀ : Config (AgentState L K)) (hc₀ : hasSource c₀) (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c' | ¬hasSource c'} = 0 :=
  Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
    (NonuniformMajority L K) hasSource
    (fun c c' hc hsupp => hasSource_preserved_by_stepDistOrSelf c c' hc hsupp)
    c₀ hc₀ t

/-- Extended potential: phaseBelowCount 4 when card = n and source exists,
⊤ when card = n and no source, 0 when card ≠ n. -/
noncomputable def phase3PotentialExt (n : ℕ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  if c.card ≠ n then 0
  else if hasSource c then (phaseBelowCount 4 c : ℝ≥0∞)
  else ⊤

/-! ### Global drift bound for phase3PotentialExt

The extended potential contracts under the transition kernel for ALL configs:
- Source + card = n + ¬Phase3TiePost: epidemic descent gives the bound.
- Source + card = n + Phase3TiePost: Φ = 0, absorbing, integral = 0.
- card ≠ n: Φ = 0, card preserved, integral = 0.
- No source + card = n: Φ = ⊤, r · ⊤ = ⊤, bound trivially holds. -/

set_option maxHeartbeats 4000000 in
lemma phase3PotentialExt_drift (n : ℕ) (hn : 8 ≤ n) (c : Config (AgentState L K)) :
    ∫⁻ c', phase3PotentialExt n c' ∂((NonuniformMajority L K).transitionKernel c) ≤
      (1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞)) *
        phase3PotentialExt n c := by
  haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel c) :=
    (inferInstance : IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure c
  set r := 1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞)
  -- Case 1: card ≠ n → Φ = 0, all successors have same card, so Φ' = 0
  by_cases hcard : c.card = n
  swap
  · have : phase3PotentialExt n c = 0 := by unfold phase3PotentialExt; simp [hcard]
    rw [this, mul_zero]
    apply le_of_eq
    apply lintegral_eq_zero_of_ae_eq_zero
    change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure,
      phase3PotentialExt n c' = 0
    rw [MeasureTheory.ae_iff,
      PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
    exact Set.disjoint_left.mpr fun c' hc' hbad => by
      simp only [Set.mem_setOf_eq, not_not] at hbad
      have hc'_card := Protocol.stepDistOrSelf_support_card_eq _ c c' hc'
      have : c'.card ≠ n := hc'_card ▸ hcard
      exact hbad (show phase3PotentialExt n c' = 0 from by
        unfold phase3PotentialExt; simp [this])
  -- Case 2: card = n, no source → Φ = ⊤, r · ⊤ = ⊤
  by_cases h_source : hasSource c
  swap
  · have : phase3PotentialExt n c = ⊤ := by
      unfold phase3PotentialExt; simp [hcard, h_source]
    rw [this]
    -- r * ⊤ ≥ ∫ Φ trivially since r * ⊤ = ⊤ (r > 0) or we can use le_top
    -- r ≠ 0: we show this using real arithmetic
    -- p := 2/(n*(n-1)), p/n = 2/(n²*(n-1)) < 1 for n ≥ 2.
    -- So ENNReal.ofReal p / n < 1, hence 1 - (ofReal p / n) > 0.
    -- But instead of proving r ≠ 0, we note r ≤ 1 (since we subtract a nonneg number),
    -- and r * ⊤ ≥ anything iff r > 0 or the LHS ≤ 0.
    -- Simpler: just bound ∫ Φ_ext by ⊤ and note r * ⊤ ≥ 0.
    -- Actually r * ⊤ = ⊤ when r > 0, and = 0 when r = 0.
    -- For any ℝ≥0∞, x ≤ ⊤. If r * ⊤ = ⊤, we're done.
    -- If r = 0: 0 * ⊤ = 0 in ENNReal. Then we'd need ∫ Φ ≤ 0 which isn't true in general.
    -- So we DO need r > 0. Let's prove it via the ℝ isomorphism.
    -- 1 - ofReal(p)/n corresponds to ofReal(1 - p/n) when p/n ≤ 1.
    -- And 1 - p/n > 0 for n ≥ 8 since p = 2/(n*(n-1)) and p/n = 2/(n²(n-1)).
    -- Convert r to ofReal form and show > 0.
    have hn_pos' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    -- We need to show r * ⊤ = ⊤ (since r > 0).
    -- r = 1 - ENNReal.ofReal(p) / n where p = 2/(n*(n-1)).
    -- Since p/n < 1, r > 0, so r * ⊤ = ⊤ ≥ any integral.
    -- Direct ENNReal computation is painful; instead convert to ℝ.
    set p_real := (2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))
    set x_real := p_real / (n : ℝ)
    have h8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn_pos' : (0 : ℝ) < n := by linarith
    have hn_sub_pos' : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hx_pos' : 0 < x_real := div_pos (div_pos two_pos (mul_pos hn_pos' hn_sub_pos')) hn_pos'
    have hx_lt_one : x_real < 1 := by
      show p_real / (n : ℝ) < 1
      show (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ) < 1
      rw [div_div, div_lt_one (by positivity)]
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    -- r as ENNReal.ofReal(1 - x_real)
    have h_ofReal_div : ENNReal.ofReal p_real / (n : ℝ≥0∞) = ENNReal.ofReal x_real := by
      rw [show (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) from (ENNReal.ofReal_natCast n).symm]
      exact (ENNReal.ofReal_div_of_pos hn_pos').symm
    have hr_eq : r = ENNReal.ofReal (1 - x_real) := by
      show 1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞) =
        ENNReal.ofReal (1 - x_real)
      rw [h_ofReal_div, ENNReal.ofReal_sub _ hx_pos'.le, ENNReal.ofReal_one]
    have hr_pos_real : (0 : ℝ) < 1 - x_real := by linarith
    rw [hr_eq]
    -- ENNReal.ofReal(1 - x_real) * ⊤ = ⊤ since 1 - x_real > 0
    have : ENNReal.ofReal (1 - x_real) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr hr_pos_real)
    rw [ENNReal.mul_top this]
    exact le_top
  -- Case 3: card = n, source exists
  by_cases hpost : Phase3TiePost c
  · -- Phase3TiePost: Φ = pbc = 0
    have hpbc : phaseBelowCount 4 c = 0 :=
      (Phase3TiePost_iff_phaseBelowCount_zero c).mp hpost
    have : phase3PotentialExt n c = 0 := by
      unfold phase3PotentialExt; simp [hcard, h_source, hpbc]
    rw [this, mul_zero]
    apply le_of_eq
    apply lintegral_eq_zero_of_ae_eq_zero
    -- Phase3TiePost absorbing + source maintained + card preserved → Φ' = 0
    have h_card_ae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        c'.card = n := by
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
      rw [MeasureTheory.ae_iff,
        PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact Set.disjoint_left.mpr fun c' hc' hbad =>
        hbad (Protocol.stepDistOrSelf_support_card_eq _ c c' hc' ▸ hcard)
    have h_post_ae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        Phase3TiePost c' := by
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
      rw [MeasureTheory.ae_iff,
        PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact Set.disjoint_left.mpr fun c' hc' hbad => by
        -- hbad : c' ∈ {c' | ¬Phase3TiePost c'}, goal : False
        -- Need to show Phase3TiePost c'
        simp only [Set.mem_setOf_eq] at hbad
        apply hbad; intro a' ha'
        unfold Protocol.stepDistOrSelf at hc'
        split_ifs at hc' with h_size
        · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ hc'
          subst heq
          unfold Protocol.scheduledStep Protocol.stepOrSelf at ha'
          split_ifs at ha' with h_app
          · rw [Multiset.mem_add] at ha'
            rcases ha' with h_rem | h_new
            · exact hpost a' (Multiset.mem_of_le (Multiset.sub_le_self _ _) h_rem)
            · simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
                Multiset.mem_singleton] at h_new
              rcases h_new with rfl | rfl
              · exact le_trans
                  (hpost r₁ (Multiset.mem_of_le h_app (by simp)))
                  (Transition_phase_monotone (L := L) (K := K) r₁ r₂).1
              · exact le_trans
                  (hpost r₂ (Multiset.mem_of_le h_app (by simp)))
                  (Transition_phase_monotone (L := L) (K := K) r₁ r₂).2
          · exact hpost a' ha'
        · simp at hc'; subst hc'; exact hpost a' ha'
    filter_upwards [h_card_ae, h_post_ae] with c' hc'_card hc'_post
    have hpbc' : phaseBelowCount 4 c' = 0 :=
      (Phase3TiePost_iff_phaseBelowCount_zero c').mp hc'_post
    show phase3PotentialExt n c' = 0
    unfold phase3PotentialExt
    rw [if_neg (not_not.mpr hc'_card)]
    have hc'_source : hasSource c' := by
      have hc'pos : 0 < c'.card := by omega
      obtain ⟨a, ha_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hc'pos
      exact ⟨a, ha_mem, hc'_post a ha_mem⟩
    rw [if_pos hc'_source, hpbc']
    simp
  · -- Main case: card = n, source, ¬Phase3TiePost
    -- phase3PotentialExt n c = phaseBelowCount 4 c
    have hΦ_eq : phase3PotentialExt n c = (phaseBelowCount 4 c : ℝ≥0∞) := by
      unfold phase3PotentialExt; simp [hcard, h_source]
    -- Integral of Φ_ext ≤ integral of phaseBelowCount (since Φ_ext ≤ pbc pointwise on
    -- source states, and K(c, {¬source}) = 0 for source c)
    -- Actually: ∫ Φ_ext ≤ ∫ pbc since Φ_ext ≤ pbc everywhere
    -- (Φ_ext = pbc when source ∧ card=n; Φ_ext = 0 when card≠n; Φ_ext = ⊤ when ¬source ∧ card=n)
    -- But ⊤ > pbc, so Φ_ext is NOT ≤ pbc everywhere. We need to use source preservation.
    -- Strategy: show ∫ Φ_ext = ∫_{source∧card=n} pbc (since K(c,{¬source})=0 and K(c,{card≠n})=0)
    have h_card_ae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        c'.card = n := by
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
      rw [MeasureTheory.ae_iff,
        PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact Set.disjoint_left.mpr fun c' hc' hbad =>
        hbad (Protocol.stepDistOrSelf_support_card_eq _ c c' hc' ▸ hcard)
    have h_source_ae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        hasSource c' := by
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
      rw [MeasureTheory.ae_iff,
        PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact Set.disjoint_left.mpr fun c' hc' hbad => by
        simp only [Set.mem_setOf_eq, not_not] at hbad
        exact hbad (hasSource_preserved_by_stepDistOrSelf c c' h_source hc')
    -- a.e., Φ_ext c' = pbc c'
    have h_eq_ae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        phase3PotentialExt n c' = (phaseBelowCount 4 c' : ℝ≥0∞) := by
      filter_upwards [h_card_ae, h_source_ae] with c' hc'_card hc'_source
      unfold phase3PotentialExt; simp [hc'_card, hc'_source]
    -- ∫ Φ_ext = ∫ pbc
    have h_int_eq : ∫⁻ c', phase3PotentialExt n c'
        ∂((NonuniformMajority L K).transitionKernel c) =
        ∫⁻ c', (phaseBelowCount 4 c' : ℝ≥0∞)
        ∂((NonuniformMajority L K).transitionKernel c) := by
      exact lintegral_congr_ae h_eq_ae
    rw [h_int_eq, hΦ_eq]
    -- Now we need: ∫ pbc dK(c) ≤ r · pbc(c)
    -- This follows from: pbc non-increasing a.e. + descent prob ≥ p
    -- Use phase3_descent_prob' (no Phase3TiePre needed)
    have h_pbc := phaseBelowCount_ae_noninc 4 c
    have h_noninc : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        phaseBelowCount 4 c' ≤ phaseBelowCount 4 c := h_pbc
    have h_desc_pbc : (NonuniformMajority L K).transitionKernel c
        {c' | phaseBelowCount 4 c' < phaseBelowCount 4 c} ≥
        ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) := by
      have := phase3_descent_prob' c (hcard ▸ hn) hpost h_source
      rwa [hcard] at this
    set p_ennr := ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1)))
    -- Apply lintegral_nat_le_of_descent
    have h_bound : ∫⁻ c', (phaseBelowCount 4 c' : ℝ≥0∞)
        ∂((NonuniformMajority L K).transitionKernel c) ≤
        (phaseBelowCount 4 c : ℝ≥0∞) - p_ennr := by
      exact lintegral_nat_le_of_descent
        ((NonuniformMajority L K).transitionKernel c)
        (phaseBelowCount 4) (phaseBelowCount 4 c)
        h_noninc
        p_ennr.toNNReal
        (by rw [ENNReal.coe_toNNReal (ENNReal.ofReal_ne_top)]; exact h_desc_pbc)
    -- Chain: E[pbc'] ≤ pbc - p ≤ pbc - (p/n)·pbc = (1 - p/n)·pbc = r·pbc
    have hv_le_M : (phaseBelowCount 4 c : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
      exact_mod_cast (hcard ▸ phaseBelowCount_le_card 4 c)
    have hM_ne_zero : (n : ℝ≥0∞) ≠ 0 := by simp [show n ≠ 0 by omega]
    have hM_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
    have hmul_le : p_ennr / (n : ℝ≥0∞) * (phaseBelowCount 4 c : ℝ≥0∞) ≤ p_ennr := by
      calc p_ennr / (n : ℝ≥0∞) * (phaseBelowCount 4 c : ℝ≥0∞)
          ≤ p_ennr / (n : ℝ≥0∞) * (n : ℝ≥0∞) := mul_le_mul_left' hv_le_M _
        _ = p_ennr := ENNReal.div_mul_cancel hM_ne_zero hM_ne_top
    have hsub_le : (phaseBelowCount 4 c : ℝ≥0∞) - p_ennr ≤
        (phaseBelowCount 4 c : ℝ≥0∞) -
          (p_ennr / (n : ℝ≥0∞) * (phaseBelowCount 4 c : ℝ≥0∞)) :=
      tsub_le_tsub_left hmul_le _
    have hmul_sub : r * (phaseBelowCount 4 c : ℝ≥0∞) =
        (phaseBelowCount 4 c : ℝ≥0∞) -
          (p_ennr / (n : ℝ≥0∞) * (phaseBelowCount 4 c : ℝ≥0∞)) := by
      show (1 - p_ennr / (n : ℝ≥0∞)) * (phaseBelowCount 4 c : ℝ≥0∞) = _
      simpa [one_mul] using
        ENNReal.sub_mul (a := 1) (b := p_ennr / (n : ℝ≥0∞))
          (c := (phaseBelowCount 4 c : ℝ≥0∞))
    calc ∫⁻ c', (phaseBelowCount 4 c' : ℝ≥0∞)
            ∂((NonuniformMajority L K).transitionKernel c)
        ≤ (phaseBelowCount 4 c : ℝ≥0∞) - p_ennr := h_bound
      _ ≤ (phaseBelowCount 4 c : ℝ≥0∞) -
            (p_ennr / (n : ℝ≥0∞) * (phaseBelowCount 4 c : ℝ≥0∞)) := hsub_le
      _ = r * (phaseBelowCount 4 c : ℝ≥0∞) := hmul_sub.symm

/-! ### Numerical bound: r^t · n ≤ 1/n²

Uses (1-x)^t ≤ exp(-xt) for 0 ≤ x ≤ 1, and then
exp(-2t/(n²(n-1))) · n ≤ 1/n² when t ≥ 2·n²·(n-1)·log(n). -/

private lemma ennreal_r_pow_mul_n_le (n t : ℕ) (hn : 8 ≤ n)
    (ht : (2 * (n : ℝ)^2 * ((n : ℝ) - 1) * Real.log (n : ℝ)) < ↑t) :
    (1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞)) ^ t *
      (n : ℝ≥0∞) ≤
    ENNReal.ofReal ((1 / (n : ℝ)^2)) := by
  -- Convert to ℝ arithmetic via ENNReal.ofReal
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn_sub_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith [show (8 : ℝ) ≤ n from by exact_mod_cast hn]
  have hprod_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := mul_pos hn_pos hn_sub_pos
  -- p = 2/(n*(n-1)), x = p/n = 2/(n²*(n-1))
  set p := (2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) with hp_def
  set x := p / (n : ℝ) with hx_def
  have hp_pos : 0 < p := div_pos two_pos hprod_pos
  have hx_pos : 0 < x := div_pos hp_pos hn_pos
  have hx_eq : x = 2 / ((n : ℝ)^2 * ((n : ℝ) - 1)) := by
    rw [hx_def, hp_def]; field_simp
  have hx_le_one : x ≤ 1 := by
    rw [hx_eq]
    have h_denom : 0 < (n : ℝ)^2 * ((n : ℝ) - 1) := mul_pos (sq_pos_of_pos hn_pos) hn_sub_pos
    rw [div_le_one h_denom]
    have : (8 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  -- r_real = 1 - x
  set r_real := 1 - x with hr_def
  have hr_nonneg : 0 ≤ r_real := by linarith
  have hr_le_one : r_real ≤ 1 := by linarith [hx_pos]
  -- Step 1: Show ENNReal r = ENNReal.ofReal (1 - x)
  have h_r_eq : (1 : ℝ≥0∞) - ENNReal.ofReal p / (n : ℝ≥0∞) =
      ENNReal.ofReal r_real := by
    rw [hr_def, hx_def]
    conv_lhs => rw [show (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) from
      (ENNReal.ofReal_natCast n).symm]
    rw [← ENNReal.ofReal_div_of_pos hn_pos]
    rw [ENNReal.ofReal_sub _ (hx_pos.le)]
    congr 1
    exact ENNReal.ofReal_one.symm
  -- Step 2: r^t ≤ exp(-x*t) via (1-x)^t ≤ exp(-x*t)
  have h_pow_eq : (ENNReal.ofReal r_real) ^ t = ENNReal.ofReal (r_real ^ t) := by
    rw [ENNReal.ofReal_pow hr_nonneg]
  -- exp(a)^k = exp(a*k)
  have exp_pow_eq : ∀ (a : ℝ) (k : ℕ), Real.exp a ^ k = Real.exp (a * k) := by
    intro a k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, ← Real.exp_add]; push_cast; ring_nf
  -- (1-x)^t ≤ exp(-x*t)
  have h_exp_bound : r_real ^ t ≤ Real.exp (-(x * t)) := by
    have h1x : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
    calc r_real ^ t = (1 - x) ^ t := rfl
      _ ≤ Real.exp (-(x : ℝ)) ^ t :=
          pow_le_pow_left₀ hr_nonneg h1x t
      _ = Real.exp (-(x * ↑t)) := by rw [exp_pow_eq, neg_mul]
  -- Step 3: exp(-x*t) * n ≤ 1/n² when x*t ≥ 3*ln(n)
  -- x*t = 2*t/(n²*(n-1)) and we need this ≥ 3*ln(n)
  -- From ht: t > 2*n²*(n-1)*ln(n), so x*t > 2*n²*(n-1)*ln(n) * 2/(n²*(n-1)) = 4*ln(n)
  -- Wait: x = 2/(n²*(n-1)), so x*t > x * 2*n²*(n-1)*ln(n) = 4*ln(n). Actually:
  -- x*t = (2/(n²*(n-1))) * t > (2/(n²*(n-1))) * 2*n²*(n-1)*ln(n) = 4*ln(n)
  -- We need x*t ≥ 3*ln(n) which is satisfied.
  -- Actually we need exp(-x*t)*n ≤ 1/n², i.e., exp(-x*t) ≤ 1/n³, i.e., x*t ≥ 3*ln(n).
  -- exp(-x*t)*n ≤ 1/n² ↔ exp(-x*t) ≤ n⁻³ ↔ x*t ≥ 3*ln(n)
  have hxt_bound : 3 * Real.log n ≤ x * t := by
    rw [hx_eq]
    have ht' : 2 * (n : ℝ)^2 * ((n : ℝ) - 1) * Real.log n < t := ht
    calc 3 * Real.log n
        ≤ 4 * Real.log n := by nlinarith [Real.log_pos (by linarith : (1 : ℝ) < n)]
      _ = 2 / ((n : ℝ)^2 * ((n : ℝ) - 1)) * (2 * (n : ℝ)^2 * ((n : ℝ) - 1) * Real.log n) := by
          field_simp
          ring
      _ ≤ 2 / ((n : ℝ)^2 * ((n : ℝ) - 1)) * t := by
          apply mul_le_mul_of_nonneg_left (le_of_lt ht')
          exact div_nonneg two_pos.le (mul_pos (sq_pos_of_pos hn_pos) hn_sub_pos).le
  have h_exp_n : Real.exp (-(x * ↑t)) * n ≤ 1 / (n : ℝ)^2 := by
    have hln_pos : 0 < Real.log n := Real.log_pos (by linarith : (1 : ℝ) < n)
    calc Real.exp (-(x * ↑t)) * ↑n
        ≤ Real.exp (-(3 * Real.log ↑n)) * n := by
          apply mul_le_mul_of_nonneg_right _ hn_pos.le
          exact Real.exp_le_exp_of_le (by linarith)
      _ = Real.exp (-(3 * Real.log ↑n)) * Real.exp (Real.log ↑n) := by
          rw [Real.exp_log hn_pos]
      _ = Real.exp (-(3 * Real.log ↑n) + Real.log ↑n) := by
          rw [← Real.exp_add]
      _ = Real.exp (-(2 * Real.log ↑n)) := by ring_nf
      _ = Real.exp (Real.log ((↑n : ℝ) ^ (-(2 : ℤ)))) := by
          rw [Real.log_zpow]; ring_nf
      _ = (↑n : ℝ) ^ (-(2 : ℤ)) := Real.exp_log (by positivity)
      _ = 1 / (↑n : ℝ) ^ 2 := by
          rw [zpow_neg, zpow_ofNat, one_div]
  -- Step 4: Assemble in ENNReal
  rw [h_r_eq, h_pow_eq]
  calc ENNReal.ofReal (r_real ^ t) * (n : ℝ≥0∞)
      ≤ ENNReal.ofReal (Real.exp (-(x * ↑t))) * (n : ℝ≥0∞) := by
        apply mul_le_mul_right'
        exact ENNReal.ofReal_le_ofReal h_exp_bound
    _ = ENNReal.ofReal (Real.exp (-(x * ↑t)) * n) := by
        rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) :=
        ENNReal.ofReal_le_ofReal h_exp_n

/-- Phase 3 convergence via direct geometric drift on the extended potential.

Uses `phase3PotentialExt` which is `⊤` for configs without an epidemic source
(no agent with phase ≥ 4). This makes the global drift bound hold trivially
for such configs, while the actual descent is proved via epidemic spread
for configs with source.

The source invariant ensures that from Pre (which includes source existence),
the no-source case is never reached, so the `⊤` values don't contribute.

The time hypothesis `2 * n² * (n-1) * log(n)` gives sufficient decay:
`r^t * n ≤ 1/n²` where `r = 1 - 2/(n²(n-1))`. -/
noncomputable def phase3TieConvergence (n : ℕ) (hn : 8 ≤ n) (t : ℕ)
    (ht : (2 * (n : ℝ)^2 * ((n : ℝ) - 1) * Real.log (n : ℝ)) < ↑t) :
    PhaseConvergence (NonuniformMajority L K).transitionKernel where
  Pre := fun c => c.card = n ∧ Phase3TiePre c ∧ (∃ a ∈ c, 4 ≤ a.phase.val)
  Post := Phase3TiePost
  t := t
  ε := ⟨(1 / (n : ℝ)^2).toNNReal, by positivity⟩
  post_absorbing := by
    intro c hc
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {y | Phase3TiePost y} = 1
    rw [((NonuniformMajority L K).stepDistOrSelf c).toMeasure_apply_eq_one_iff
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    intro c' hc' a' ha'
    unfold Protocol.stepDistOrSelf at hc'
    split_ifs at hc' with h_size
    · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ hc'
      subst heq
      unfold Protocol.scheduledStep Protocol.stepOrSelf at ha'
      split_ifs at ha' with h_app
      · rw [Multiset.mem_add] at ha'
        rcases ha' with h_rem | h_new
        · exact hc a' (Multiset.mem_of_le (Multiset.sub_le_self _ _) h_rem)
        · simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
            Multiset.mem_singleton] at h_new
          rcases h_new with rfl | rfl
          · exact le_trans
              (hc r₁ (Multiset.mem_of_le h_app (by simp)))
              (Transition_phase_monotone (L := L) (K := K) r₁ r₂).1
          · exact le_trans
              (hc r₂ (Multiset.mem_of_le h_app (by simp)))
              (Transition_phase_monotone (L := L) (K := K) r₁ r₂).2
      · exact hc a' ha'
    · simp at hc'; subst hc'; exact hc a' ha'
  convergence := by
    intro c₀ ⟨hcard₀, _, hsource₀⟩
    set ε_nnr : ℝ≥0 := ⟨(1 / (n : ℝ)^2).toNNReal, by positivity⟩
    set r := 1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞)
    -- Apply measure_potential_ge_one with phase3PotentialExt
    have h_drift : ∀ c, ∫⁻ c', phase3PotentialExt n c'
        ∂((NonuniformMajority L K).transitionKernel c) ≤
        r * phase3PotentialExt n c :=
      phase3PotentialExt_drift n hn
    have h_meas : Measurable (phase3PotentialExt n (L := L) (K := K)) :=
      Measurable.of_discrete
    have h_decay := PopProtoCommon.measure_potential_ge_one
      (NonuniformMajority L K).transitionKernel
      (phase3PotentialExt n) h_meas r h_drift t c₀
    -- {¬Phase3TiePost} ⊆ {Φ_ext ≥ 1} ∪ {card ≠ n} ∪ {¬source}
    -- From Pre: card = n maintained, source maintained
    -- So (K^t) c₀ {card ≠ n} = 0 and (K^t) c₀ {¬source} = 0
    have h_card_zero : ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c' | c'.card ≠ n} = 0 := by
      apply Protocol.transitionKernel_pow_eq_zero_of_forall_not_reachable
      intro c' hc' hreach
      exact hc' (Protocol.reachable_card_eq hreach ▸ hcard₀)
    have h_nosource_zero : ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c' | ¬hasSource c'} = 0 :=
      hasSource_transitionKernel_pow_zero c₀ hsource₀ t
    -- {card=n ∧ ¬Phase3TiePost} ⊆ {Φ_ext ≥ 1}
    have h_subset_ext : {c' : Config (AgentState L K) |
        c'.card = n ∧ hasSource c' ∧ ¬Phase3TiePost c'} ⊆
        {c' | 1 ≤ phase3PotentialExt n c'} := by
      intro c' ⟨hc'_card, hc'_source, hc'_not_post⟩
      simp only [Set.mem_setOf_eq]
      unfold phase3PotentialExt
      simp [hc'_card, hc'_source]
      rw [Phase3TiePost_iff_phaseBelowCount_zero] at hc'_not_post
      exact_mod_cast Nat.pos_of_ne_zero hc'_not_post
    -- Φ_ext(c₀) = pbc(c₀) ≤ n
    have h_source₀ : hasSource c₀ := hsource₀
    have hΦ_c₀ : phase3PotentialExt n c₀ = (phaseBelowCount 4 c₀ : ℝ≥0∞) := by
      unfold phase3PotentialExt; simp [hcard₀, h_source₀]
    have hΦ_le_n : phase3PotentialExt n c₀ ≤ (n : ℝ≥0∞) := by
      rw [hΦ_c₀]
      exact_mod_cast (hcard₀ ▸ phaseBelowCount_le_card 4 c₀)
    -- Numerical bound: r^t * n ≤ 1/n²
    have h_num : r ^ t * (n : ℝ≥0∞) ≤ ENNReal.ofReal (1 / (n : ℝ)^2) :=
      ennreal_r_pow_mul_n_le n t hn ht
    -- Main calculation
    calc ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | ¬Phase3TiePost c'}
        ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
            ({c' | c'.card = n ∧ hasSource c' ∧ ¬Phase3TiePost c'} ∪
             {c' | c'.card ≠ n} ∪ {c' | ¬hasSource c'}) := by
          apply measure_mono
          intro c' hc'
          by_cases hc'_card : c'.card = n
          · by_cases hc'_source : hasSource c'
            · left; left; exact ⟨hc'_card, hc'_source, hc'⟩
            · right; exact hc'_source
          · left; right; exact hc'_card
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
            ({c' | c'.card = n ∧ hasSource c' ∧ ¬Phase3TiePost c'} ∪
             {c' | c'.card ≠ n}) +
          ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | ¬hasSource c'} := measure_union_le _ _
      _ = ((NonuniformMajority L K).transitionKernel ^ t) c₀
            ({c' | c'.card = n ∧ hasSource c' ∧ ¬Phase3TiePost c'} ∪
             {c' | c'.card ≠ n}) + 0 := by
          rw [h_nosource_zero]
      _ = ((NonuniformMajority L K).transitionKernel ^ t) c₀
            ({c' | c'.card = n ∧ hasSource c' ∧ ¬Phase3TiePost c'} ∪
             {c' | c'.card ≠ n}) := add_zero _
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | c'.card = n ∧ hasSource c' ∧ ¬Phase3TiePost c'} +
          ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | c'.card ≠ n} := measure_union_le _ _
      _ = ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | c'.card = n ∧ hasSource c' ∧ ¬Phase3TiePost c'} + 0 := by
          rw [h_card_zero]
      _ = ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | c'.card = n ∧ hasSource c' ∧ ¬Phase3TiePost c'} := add_zero _
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | 1 ≤ phase3PotentialExt n c'} := measure_mono h_subset_ext
      _ ≤ r ^ t * phase3PotentialExt n c₀ := h_decay
      _ ≤ r ^ t * (n : ℝ≥0∞) := by gcongr
      _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := h_num
      _ = (ε_nnr : ℝ≥0∞) := by
          simp only [ε_nnr]
          rfl

end ExactMajority
