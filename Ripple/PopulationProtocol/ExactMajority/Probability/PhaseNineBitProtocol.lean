-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseNineBitProtocol.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.UniformRecovery
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoThresholds

/-!
Opinion bits in the actual Phase-9 transition.  Entering Phase 10 stops
every bit epidemic at its completed value.  Both ordered mixed rectangles
are counted, including multiplicities of physical agents.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseNineBitProtocol

open TimeTheorem PairLog AdvanceEpidemics UniformRecovery

variable {L K : ℕ}

def opinionBit (b : Fin 3) (u : Fin 8) : Prop :=
  Nat.testBit u.val b.val = true

instance (b : Fin 3) (u : Fin 8) : Decidable (opinionBit b u) := by
  unfold opinionBit
  infer_instance

def carriesBit (b : Fin 3) (a : AgentState L K) : Prop :=
  opinionBit b a.opinions

instance (b : Fin 3) (a : AgentState L K) : Decidable (carriesBit b a) := by
  unfold carriesBit
  infer_instance

set_option maxHeartbeats 400000 in
/-- There are only 192 concrete bit/union checks. -/
theorem opinionBit_union (b : Fin 3) (u v : Fin 8) :
    opinionBit b (opinionsUnion u v) ↔ opinionBit b u ∨ opinionBit b v := by
  fin_cases b <;> fin_cases u <;> fin_cases v <;> decide

set_option maxHeartbeats 200000 in
/-- Exhaust the 64 pairs of finite masks, comparing their three stored bits. -/
theorem opinion_eq_iff_bits (u v : Fin 8) :
    u = v ↔ ∀ b : Fin 3, opinionBit b u ↔ opinionBit b v := by
  fin_cases u <;> fin_cases v <;> decide

def bitCount (b : Fin 3) (c : Cfg L K) : ℕ :=
  Multiset.countP (carriesBit b) c

def Backup (c : Cfg L K) : Prop := ∃ a ∈ c, 10 ≤ a.phase.val

open Classical in
def infectionCount (b : Fin 3) (n : ℕ) (c : Cfg L K) : ℕ :=
  if Backup c then n else bitCount b c

theorem bitCount_le_card (b : Fin 3) (c : Cfg L K) :
    bitCount b c ≤ c.card :=
  Multiset.countP_le_card _ _

theorem infectionCount_le (b : Fin 3) (n : ℕ) (c : Cfg L K)
    (hcard : c.card = n) : infectionCount b n c ≤ n := by
  classical
  unfold infectionCount
  split_ifs
  · exact le_rfl
  · simpa only [hcard] using bitCount_le_card b c

theorem backup_iff_count (c : Cfg L K) :
    Backup c ↔ 0 < geCount 10 c := by
  exact Multiset.countP_pos.symm

theorem backup_step (c : Cfg L K) (s t : AgentState L K)
    (hc : Backup c) :
    Backup (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  apply (backup_iff_count _).2
  exact lt_of_lt_of_le ((backup_iff_count c).1 hc)
    (geCount_stepOrSelf_ge 10 c s t)

theorem pure_of_no_backup (n : ℕ) (c : Cfg L K)
    (hc : allPhaseGe 9 n c) (hnob : ¬ Backup c) : PurePhase 9 c := by
  intro a ha
  have hlo := hc.2 a ha
  have hhi : ¬ 10 ≤ a.phase.val := fun h => hnob ⟨a, ha, h⟩
  omega

theorem pair_count (b : Fin 3) (s t : AgentState L K) :
    Multiset.countP (carriesBit b) ({s, t} : Multiset (AgentState L K)) =
      (if carriesBit b s then 1 else 0) + (if carriesBit b t then 1 else 0) := by
  simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.countP_cons,
    Multiset.countP_zero, zero_add]
  exact add_comm _ _

theorem bit_count_step_accounting (b : Fin 3) (n : ℕ) (c : Cfg L K)
    (hc : allPhaseGe 9 n c) (hnob : ¬ Backup c)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t)
    (hout : ¬ Backup (Protocol.stepOrSelf (NonuniformMajority L K) c s t)) :
    bitCount b (Protocol.stepOrSelf (NonuniformMajority L K) c s t) +
        ((if carriesBit b s then 1 else 0) + (if carriesBit b t then 1 else 0)) =
      bitCount b c + 2 * (if carriesBit b s ∨ carriesBit b t then 1 else 0) := by
  classical
  have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
  have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hp := pure_of_no_backup n c hc hnob
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
      c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have hkeep :
      (Transition L K s t).1.opinions = opinionsUnion s.opinions t.opinions ∧
      (Transition L K s t).2.opinions = opinionsUnion s.opinions t.opinions := by
    rcases opinion_transition_union_or_exit 9 (Or.inr rfl) s t (hp s hs) (hp t ht)
      with h | h
    · exact ⟨h.1, h.2.1⟩
    · exfalso
      apply hout
      refine ⟨(Transition L K s t).1, ?_, by omega⟩
      rw [hstep]
      simp
  have hleft : carriesBit b (Transition L K s t).1 ↔
      carriesBit b s ∨ carriesBit b t := by
    simpa only [carriesBit, hkeep.1] using opinionBit_union b s.opinions t.opinions
  have hright : carriesBit b (Transition L K s t).2 ↔
      carriesBit b s ∨ carriesBit b t := by
    simpa only [carriesBit, hkeep.2] using opinionBit_union b s.opinions t.opinions
  have hpairle := Multiset.countP_le_of_le (carriesBit b) happ
  rw [pair_count] at hpairle
  unfold bitCount
  rw [hstep, Multiset.countP_add, Multiset.countP_sub happ, pair_count, pair_count]
  simp only [hleft, hright]
  omega

theorem infectionCount_step_mono (b : Fin 3) (n : ℕ) (c : Cfg L K)
    (hc : allPhaseGe 9 n c) (s t : AgentState L K) :
    infectionCount b n c ≤
      infectionCount b n (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  by_cases hpre : Backup c
  · simp only [infectionCount, if_pos hpre, if_pos (backup_step c s t hpre), le_refl]
  by_cases hpost : Backup (Protocol.stepOrSelf (NonuniformMajority L K) c s t)
  · simpa only [infectionCount, if_pos hpost] using infectionCount_le b n c hc.1
  simp only [infectionCount, if_neg hpre, if_neg hpost]
  by_cases happ : Protocol.Applicable c s t
  · have hcount := bit_count_step_accounting b n c hc hpre s t happ hpost
    by_cases hs : carriesBit b s <;> by_cases ht : carriesBit b t <;>
      simp only [hs, ht, if_true, if_false, true_or, false_or] at hcount <;> omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem infectionCount_zero_step (b : Fin 3) (n : ℕ) (c : Cfg L K)
    (hc : allPhaseGe 9 n c) (hz : infectionCount b n c = 0)
    (s t : AgentState L K) :
    infectionCount b n (Protocol.stepOrSelf (NonuniformMajority L K) c s t) = 0 ∨
      infectionCount b n (Protocol.stepOrSelf (NonuniformMajority L K) c s t) = n := by
  classical
  by_cases hpost : Backup (Protocol.stepOrSelf (NonuniformMajority L K) c s t)
  · exact Or.inr (by simp only [infectionCount, if_pos hpost])
  by_cases hpre : Backup c
  · exact False.elim (hpost (backup_step c s t hpre))
  left
  simp only [infectionCount, if_neg hpre] at hz
  simp only [infectionCount, if_neg hpost]
  by_cases happ : Protocol.Applicable c s t
  · have hall : ∀ a ∈ c, ¬ carriesBit b a := Multiset.countP_eq_zero.mp hz
    have hs := hall s (Multiset.mem_of_le happ (by simp))
    have ht := hall t (Multiset.mem_of_le happ (by simp))
    have h := bit_count_step_accounting b n c hc hpre s t happ hpost
    simp only [hs, ht, false_or, if_false, hz, zero_add, mul_zero] at h
    omega
  · simpa only [Protocol.stepOrSelf_eq_self_of_not_applicable happ] using hz

theorem infectionCount_step_advance (b : Fin 3) (n : ℕ) (c : Cfg L K)
    (hc : allPhaseGe 9 n c) (hnob : ¬ Backup c)
    (hi : infectionCount b n c < n)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t)
    (hmixed : (carriesBit b s ∧ ¬ carriesBit b t) ∨
      (¬ carriesBit b s ∧ carriesBit b t)) :
    infectionCount b n c + 1 ≤
      infectionCount b n (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  by_cases hpost : Backup (Protocol.stepOrSelf (NonuniformMajority L K) c s t)
  · simpa only [infectionCount, if_pos hpost] using Nat.succ_le_of_lt hi
  have hcount := bit_count_step_accounting b n c hc hnob s t happ hpost
  simp only [infectionCount, if_neg hnob, if_neg hpost]
  rcases hmixed with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> simp only [hs, ht,
    true_or, false_or, if_true, if_false] at hcount <;> omega

theorem step_support_mono (b : Fin 3) (n : ℕ) (c c' : Cfg L K)
    (hc : allPhaseGe 9 n c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    infectionCount b n c ≤ infectionCount b n c' := by
  classical
  by_cases htwo : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c =
        (NonuniformMajority L K).stepDist c htwo by
          unfold Protocol.stepDistOrSelf; rw [dif_pos htwo]] at hsupp
    obtain ⟨⟨s, t⟩, hst⟩ := Protocol.stepDist_support
      (NonuniformMajority L K) c htwo c' hsupp
    rw [← hst]
    exact infectionCount_step_mono b n c hc s t
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
      unfold Protocol.stepDistOrSelf; rw [dif_neg htwo]] at hsupp
    rw [PMF.mem_support_pure_iff] at hsupp
    subst c'
    exact le_rfl

theorem step_support_zero (b : Fin 3) (n : ℕ) (c c' : Cfg L K)
    (hc : allPhaseGe 9 n c) (hz : infectionCount b n c = 0)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    infectionCount b n c' = 0 ∨ infectionCount b n c' = n := by
  classical
  by_cases htwo : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c =
        (NonuniformMajority L K).stepDist c htwo by
          unfold Protocol.stepDistOrSelf; rw [dif_pos htwo]] at hsupp
    obtain ⟨⟨s, t⟩, hst⟩ := Protocol.stepDist_support
      (NonuniformMajority L K) c htwo c' hsupp
    rw [← hst]
    exact infectionCount_zero_step b n c hc hz s t
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
      unfold Protocol.stepDistOrSelf; rw [dif_neg htwo]] at hsupp
    rw [PMF.mem_support_pure_iff] at hsupp
    subst c'
    exact Or.inl hz

open Classical in
private theorem sum_count_predicate (c : Cfg L K) (P : AgentState L K → Prop) :
    (∑ a ∈ Finset.univ.filter P, c.count a) = Multiset.countP P c := by
  classical
  rw [Multiset.countP_eq_card_filter]
  have hcount : ∀ a ∈ Finset.univ.filter P,
      c.count a = Multiset.count a (c.filter P) := by
    intro a ha
    rw [Config.count, Multiset.count_filter, if_pos (Finset.mem_filter.mp ha).2]
  rw [Finset.sum_congr rfl hcount, Multiset.sum_count_eq_card]
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Multiset.mem_filter.mp ha).2⟩

private theorem advance_probability_of_rectangle (F : Cfg L K → ℕ) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hcardn : c.card = n)
    (R : Finset (AgentState L K × AgentState L K)) (N : ℕ)
    (hadv : ∀ p ∈ R, 1 ≤ c.count p.1 → 1 ≤ c.count p.2 → (p.1 = p.2 → 2 ≤ c.count p.1) →
      F c + 1 ≤ F (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2))
    (hcount : (N : ℕ) ≤ ∑ p ∈ R, c.interactionCount p.1 p.2) :
    ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | F c + 1 ≤ F c'} := by
  classical
  set j := F c with hjdef
  have hcard2 : 2 ≤ c.card := by rw [hcardn]; omega
  have hmeas : MeasurableSet {c' : Config (AgentState L K) | j + 1 ≤ F c'} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  set S : Finset (AgentState L K × AgentState L K) :=
    R.filter (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2 ∧ (p.1 = p.2 → 2 ≤ c.count p.1)) with hS
  have hsub : (↑S : Set (AgentState L K × AgentState L K)) ⊆
      (Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
        {c' | j + 1 ≤ F c'} := by
    intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hS] at hp
    obtain ⟨hpc, hp1, hp2, hp3⟩ := hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Protocol.scheduledStep]
    exact hadv p hpc hp1 hp2 hp3
  have hstepDist : (NonuniformMajority L K).stepDistOrSelf c
      = (NonuniformMajority L K).stepDist c hcard2 := by
    unfold Protocol.stepDistOrSelf
    rw [dif_pos hcard2]
  have hbase : ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | j + 1 ≤ F c'}
      = (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ F c'}) := by
    rw [hstepDist]
    unfold Protocol.stepDist
    rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hmeas]
  rw [hbase]
  have hmono : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      ≤ (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ F c'}) :=
    measure_mono hsub
  refine le_trans ?_ hmono
  have hSmeasure : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      = ∑ p ∈ S, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]
    rfl
  have hSsum : ∑ p ∈ S, c.interactionProb p.1 p.2
      = ∑ p ∈ R, c.interactionProb p.1 p.2 := by
    rw [hS]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hpc hpnot
    rw [Finset.mem_filter] at hpnot
    push Not at hpnot
    have hexcl := hpnot hpc
    have hzero : c.interactionCount p.1 p.2 = 0 := by
      unfold Config.interactionCount
      by_cases h1 : 1 ≤ c.count p.1
      · by_cases h2 : 1 ≤ c.count p.2
        · obtain ⟨hpe, hlt⟩ := hexcl h1 h2
          rw [if_pos hpe]
          have hc1 : c.count p.1 = 1 := by omega
          rw [hc1]
        · have hz2 : c.count p.2 = 0 := by omega
          by_cases hpe : p.1 = p.2
          · rw [if_pos hpe]
            rw [hpe, hz2, Nat.zero_mul]
          · rw [if_neg hpe, hz2, Nat.mul_zero]
      · have hz1 : c.count p.1 = 0 := by omega
        by_cases hpe : p.1 = p.2
        · rw [if_pos hpe, hz1, Nat.zero_mul]
        · rw [if_neg hpe, hz1, Nat.zero_mul]
    unfold Config.interactionProb
    rw [hzero]
    simp
  rw [hSmeasure, hSsum]
  have heqterm : ∀ p : AgentState L K × AgentState L K,
      c.interactionProb p.1 p.2
        = (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro p
    unfold Config.interactionProb
    rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun p _ => heqterm p), ← Finset.sum_mul, ← Nat.cast_sum]
  set M := ∑ p ∈ R, c.interactionCount p.1 p.2 with hM
  have htp : c.totalPairs = n * (n - 1) := by
    rw [Config.totalPairs, hcardn]
  rw [htp, ← div_eq_mul_inv]
  have hden_pos : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hdenR : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hstep1 : ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ ENNReal.ofReal (((M : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    rw [hdenR]
    have hNM : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcount
    have hposden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
      rw [← hdenR]
      exact hden_pos
    gcongr
  refine le_trans hstep1 ?_
  rw [← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_natCast (n * (n - 1)),
      ← ENNReal.ofReal_div_of_pos hden_pos]


theorem bit_advance_probability (b : Fin 3) (n : ℕ) (hn : 2 ≤ n)
    (c : Cfg L K) (hc : allPhaseGe 9 n c) (hi : infectionCount b n c < n) :
    ENNReal.ofReal
        (((2 * infectionCount b n c * (n - infectionCount b n c) : ℕ) : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {d | infectionCount b n c + 1 ≤ infectionCount b n d} := by
  classical
  have hnob : ¬ Backup c := by
    intro h
    rw [infectionCount, if_pos h] at hi
    exact Nat.lt_irrefl n hi
  have heq : infectionCount b n c = bitCount b c := by
    simp only [infectionCount, if_neg hnob]
  let A := Finset.univ.filter (carriesBit (L := L) (K := K) b)
  let B := Finset.univ.filter (fun a : AgentState L K => ¬ carriesBit b a)
  let R := (A ×ˢ B) ∪ (B ×ˢ A)
  have hAB : ∀ a ∈ A, ∀ d ∈ B, a ≠ d := by
    intro a ha d hd had
    exact (Finset.mem_filter.mp hd).2 (had ▸ (Finset.mem_filter.mp ha).2)
  have hBA : ∀ d ∈ B, ∀ a ∈ A, d ≠ a :=
    fun d hd a ha => (hAB a ha d hd).symm
  have hdisj : Disjoint (A ×ˢ B) (B ×ˢ A) := by
    refine Finset.disjoint_left.mpr ?_
    intro pr hpr hpr'
    exact hAB pr.1 (Finset.mem_product.mp hpr).1
      pr.1 (Finset.mem_product.mp hpr').1 rfl
  have hA : (∑ a ∈ A, c.count a) = infectionCount b n c := by
    rw [heq]
    unfold bitCount
    convert sum_count_predicate c (carriesBit b)
  have hB : (∑ a ∈ B, c.count a) = n - infectionCount b n c := by
    have hsum : (∑ a ∈ B, c.count a) =
        Multiset.countP (fun a => ¬ carriesBit b a) c := by
      convert sum_count_predicate c (fun a => ¬ carriesBit b a)
    have hsplit : c.card = bitCount b c +
        Multiset.countP (fun a => ¬ carriesBit b a) c := by
      exact Multiset.card_eq_countP_add_countP (carriesBit b) c
    rw [hc.1, ← heq] at hsplit
    rw [hsum]
    omega
  have hsum : (∑ pr ∈ R, c.interactionCount pr.1 pr.2) =
      2 * infectionCount b n c * (n - infectionCount b n c) := by
    rw [show R = (A ×ˢ B) ∪ (B ×ˢ A) from rfl, Finset.sum_union hdisj,
      sum_interactionCount_cross_disjoint c A B hAB,
      sum_interactionCount_cross_disjoint c B A hBA, hA, hB]
    ring
  apply advance_probability_of_rectangle (infectionCount b n) n hn c hc.1 R
    (2 * infectionCount b n c * (n - infectionCount b n c))
  · rintro ⟨s, t⟩ hpr hs ht _
    have hmixed : (carriesBit b s ∧ ¬ carriesBit b t) ∨
        (¬ carriesBit b s ∧ carriesBit b t) := by
      rcases Finset.mem_union.mp hpr with hpr | hpr
      · exact Or.inl ⟨(Finset.mem_filter.mp (Finset.mem_product.mp hpr).1).2,
          (Finset.mem_filter.mp (Finset.mem_product.mp hpr).2).2⟩
      · exact Or.inr ⟨(Finset.mem_filter.mp (Finset.mem_product.mp hpr).1).2,
          (Finset.mem_filter.mp (Finset.mem_product.mp hpr).2).2⟩
    have hne : s ≠ t := by
      intro h
      subst t
      rcases hmixed with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact ht hs
      · exact hs ht
    have happ : Protocol.Applicable c s t :=
      UniformRecovery.applicable_of_members_ne
        (Multiset.one_le_count_iff_mem.mp hs)
        (Multiset.one_le_count_iff_mem.mp ht) hne
    exact infectionCount_step_advance b n c hc hnob hi s t happ hmixed
  · rw [hsum]

theorem nonuniform_has_partial_bit (n : ℕ) (hn : 1 ≤ n) (c : Cfg L K)
    (hcard : c.card = n) (hnob : ¬ Backup c) (hnu : ¬ UniformOpinions c) :
    ∃ b : Fin 3, 1 ≤ infectionCount b n c ∧ infectionCount b n c < n := by
  classical
  by_contra hnone
  have hextreme (b : Fin 3) : bitCount b c = 0 ∨ bitCount b c = n := by
    have hle := bitCount_le_card b c
    rw [hcard] at hle
    have hnop : ¬ (1 ≤ bitCount b c ∧ bitCount b c < n) := by
      intro h
      apply hnone
      exact ⟨b, by simpa only [infectionCount, if_neg hnob] using h⟩
    omega
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp
    (show 0 < c.card by rw [hcard]; omega)
  apply hnu
  refine ⟨a.opinions, ?_⟩
  intro d hd
  apply (opinion_eq_iff_bits _ _).2
  intro b
  change carriesBit b d ↔ carriesBit b a
  rcases hextreme b with hz | hnall
  · have hall : ∀ x ∈ c, ¬ carriesBit b x := Multiset.countP_eq_zero.mp hz
    exact iff_of_false (hall d hd) (hall a ha)
  · have hsplit := Multiset.card_eq_countP_add_countP (carriesBit b) c
    have hzero : Multiset.countP (fun x => ¬ carriesBit b x) c = 0 := by
      change c.card = bitCount b c + _ at hsplit
      rw [hcard, hnall] at hsplit
      omega
    have hall : ∀ x ∈ c, ¬ ¬ carriesBit b x := Multiset.countP_eq_zero.mp hzero
    exact iff_of_true (not_not.mp (hall d hd)) (not_not.mp (hall a ha))

end Ripple.PopulationProtocol.ExactMajority.PhaseNineBitProtocol

end
