import Ripple.PopulationProtocol.ExactMajority.Probability.Phase10ExpectedTime
import Ripple.PopulationProtocol.ExactMajority.Probability.FinalRungStability
import Ripple.PopulationProtocol.ExactMajority.Probability.TraceDrain
import Ripple.PopulationProtocol.ExactMajority.Probability.WeightedDriftDropSum

/-!
# Strong-gap backup drift

The two ordered source-target rectangles are counted together. The invariant is
the signed backup gap, not the number of majority sources. The latter can fall
during cancellation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.StrongGapBackup

open TimeTheorem PairLog PairLogAuxiliary

variable {L K : ℕ}

inductive Stage
  | cancel
  | absorb
  | broadcast
  deriving DecidableEq

def majorityOutput : Sign → Output
  | .pos => .A
  | .neg => .B

def minorityOutput : Sign → Output
  | .pos => .B
  | .neg => .A

def Source (σ : Sign) (a : AgentState L K) : Prop :=
  a.full = true ∧ a.output = majorityOutput σ

instance sourceDecidable (σ : Sign) : DecidablePred (Source (L := L) (K := K) σ) := by
  intro a
  unfold Source
  infer_instance

def Target (σ : Sign) (stage : Stage) (a : AgentState L K) : Prop :=
  match stage with
  | .cancel => a.full = true ∧ a.output = minorityOutput σ
  | .absorb => IsActiveT a
  | .broadcast => a.output ≠ majorityOutput σ

instance targetDecidable (σ : Sign) (stage : Stage) :
    DecidablePred (Target (L := L) (K := K) σ stage) := by
  intro a
  cases stage <;> unfold Target <;> infer_instance

def Allowed (σ : Sign) (stage : Stage) (a : AgentState L K) : Prop :=
  match stage with
  | .cancel => True
  | .absorb => ¬ (a.full = true ∧ a.output = minorityOutput σ)
  | .broadcast =>
      ¬ (a.full = true ∧ a.output = minorityOutput σ) ∧ ¬ IsActiveT a

def sourceCount (σ : Sign) (c : Cfg L K) : ℕ := c.countP (Source σ)

def targetCount (σ : Sign) (stage : Stage) (c : Cfg L K) : ℕ :=
  c.countP (Target σ stage)

def signedGap (σ : Sign) (c : Cfg L K) : ℤ :=
  match σ with
  | .pos => phase10ActiveSignedSum c
  | .neg => -phase10ActiveSignedSum c

structure Domain (σ : Sign) (stage : Stage) (n d : ℕ) (c : Cfg L K) : Prop where
  card_eq : c.card = n
  phase : ∀ a ∈ c, a.phase.val = 10
  gap_floor : (d : ℤ) ≤ signedGap σ c
  allowed : ∀ a ∈ c, Allowed σ stage a

theorem source_count_floor (σ : Sign) (c : Cfg L K) (d : ℕ)
    (hgap : (d : ℤ) ≤ signedGap σ c) :
    d ≤ sourceCount σ c := by
  cases σ with
  | pos =>
      change (d : ℤ) ≤ phase10ActiveSignedSum c at hgap
      rw [phase10ActiveSignedSum_eq_activeACount_sub_activeBCount] at hgap
      change d ≤ activeACount c
      omega
  | neg =>
      change (d : ℤ) ≤ -phase10ActiveSignedSum c at hgap
      rw [phase10ActiveSignedSum_eq_activeACount_sub_activeBCount] at hgap
      change d ≤ activeBCount c
      omega

theorem source_not_target (σ : Sign) (stage : Stage) (a : AgentState L K)
    (hs : Source σ a) : ¬ Target σ stage a := by
  intro ht
  cases σ <;> cases stage <;>
    simp_all [Source, Target, majorityOutput, minorityOutput, IsActiveT]

private theorem count_pair {α : Type*} (P : α → Prop) [DecidablePred P] (a b : α) :
    Multiset.countP P ({a, b} : Multiset α) =
      (if P a then 1 else 0) + (if P b then 1 else 0) := by
  change Multiset.countP P (a ::ₘ ({b} : Multiset α)) = _
  rw [Multiset.countP_cons]
  have hb : Multiset.countP P ({b} : Multiset α) = if P b then 1 else 0 := by
    change Multiset.countP P (b ::ₘ (0 : Multiset α)) = _
    rw [Multiset.countP_cons]
    by_cases h : P b <;> simp [h]
  rw [hb]
  by_cases h : P a <;> simp [h, Nat.add_comm]

-- Each finite check enumerates two signs, three stages, two output fields,
-- and two activity bits. The local heartbeat cap covers these finite cases.
set_option maxHeartbeats 800000 in
theorem pair_target_nonincreasing (σ : Sign) (stage : Stage)
    (a b : AgentState L K)
    (ha : a.phase.val = 10) (hb : b.phase.val = 10)
    (hallowa : Allowed σ stage a) (hallowb : Allowed σ stage b) :
    Multiset.countP (Target σ stage)
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) ≤
      Multiset.countP (Target σ stage) ({a, b} : Multiset (AgentState L K)) := by
  rw [Transition_eq_Phase10Transition_of_phase10 a b ha hb]
  rw [count_pair, count_pair]
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases σ <;> cases stage <;>
    cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp_all [Phase10Transition, Source, Target, Allowed,
      majorityOutput, minorityOutput, IsActiveT]

set_option maxHeartbeats 800000 in
theorem pair_target_drops (σ : Sign) (stage : Stage)
    (a b : AgentState L K)
    (ha : a.phase.val = 10) (hb : b.phase.val = 10)
    (hallowa : Allowed σ stage a) (hallowb : Allowed σ stage b)
    (huseful : (Source σ a ∧ Target σ stage b) ∨
      (Target σ stage a ∧ Source σ b)) :
    Multiset.countP (Target σ stage)
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) <
      Multiset.countP (Target σ stage) ({a, b} : Multiset (AgentState L K)) := by
  rw [Transition_eq_Phase10Transition_of_phase10 a b ha hb]
  rw [count_pair, count_pair]
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases σ <;> cases stage <;>
    cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp_all [Phase10Transition, Source, Target, Allowed,
      majorityOutput, minorityOutput, IsActiveT]

set_option maxHeartbeats 800000 in
theorem pair_allowed_preserved (σ : Sign) (stage : Stage)
    (a b : AgentState L K)
    (ha : a.phase.val = 10) (hb : b.phase.val = 10)
    (hallowa : Allowed σ stage a) (hallowb : Allowed σ stage b) :
    Allowed σ stage (Transition L K a b).1 ∧
      Allowed σ stage (Transition L K a b).2 := by
  rw [Transition_eq_Phase10Transition_of_phase10 a b ha hb]
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases σ <;> cases stage <;>
    cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp_all [Phase10Transition, Source, Target, Allowed,
      majorityOutput, minorityOutput, IsActiveT]

theorem allowed_preserved_by_step (σ : Sign) (stage : Stage)
    (c c' : Cfg L K)
    (hphase : ∀ a ∈ c, a.phase.val = 10)
    (hallowed : ∀ a ∈ c, Allowed σ stage a)
    (hstep : (NonuniformMajority L K).StepRel c c') :
    ∀ a ∈ c', Allowed σ stage a := by
  rcases hstep with ⟨a, b, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have ha : a ∈ c := Multiset.mem_of_le happ (by simp)
  have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
  have hp := pair_allowed_preserved σ stage a b
    (hphase a ha) (hphase b hb) (hallowed a ha) (hallowed b hb)
  rw [hc']
  intro x hx
  rcases Multiset.mem_add.mp hx with hx | hx
  · exact hallowed x (Multiset.mem_of_le (Multiset.sub_le_self _ _) hx)
  · have hx' : x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
      simpa only [Multiset.mem_cons, Multiset.mem_singleton] using hx
    rcases hx' with rfl | rfl
    · exact hp.1
    · exact hp.2

theorem domain_preserved_by_reachable (σ : Sign) (stage : Stage)
    (n d : ℕ) (c c' : Cfg L K) (hc : Domain σ stage n d c)
    (hreach : (NonuniformMajority L K).Reachable c c') :
    Domain σ stage n d c' := by
  induction hreach with
  | refl => exact hc
  | tail _ hstep ih =>
      refine ⟨(Protocol.stepRel_card_eq hstep).trans ih.card_eq,
        phase10_phase_preserved_by_step _ _ ih.phase hstep, ?_,
        allowed_preserved_by_step σ stage _ _ ih.phase ih.allowed hstep⟩
      have hsum := phase10ActiveSignedSum_stepRel_eq _ _ ih.phase hstep
      cases σ <;> simpa only [signedGap, hsum] using ih.gap_floor

theorem target_step_le (σ : Sign) (stage : Stage) (n d : ℕ)
    (c : Cfg L K) (hc : Domain σ stage n d c) (a b : AgentState L K) :
    targetCount σ stage
        (Protocol.stepOrSelf (NonuniformMajority L K) c a b) ≤
      targetCount σ stage c := by
  classical
  by_cases happ : Protocol.Applicable c a b
  · have ha : a ∈ c := Multiset.mem_of_le happ (by simp)
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have hpair := pair_target_nonincreasing σ stage a b
      (hc.phase a ha) (hc.phase b hb) (hc.allowed a ha) (hc.allowed b hb)
    have hsplit :
        c.countP (Target σ stage) =
          (c - {a, b}).countP (Target σ stage) +
            ({a, b} : Multiset (AgentState L K)).countP (Target σ stage) := by
      rw [← Multiset.countP_add, Multiset.sub_add_cancel happ]
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    change ((c - {a, b}) +
      {(Transition L K a b).1, (Transition L K a b).2}).countP (Target σ stage) ≤
        c.countP (Target σ stage)
    rw [Multiset.countP_add, hsplit]
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem target_step_lt (σ : Sign) (stage : Stage) (n d : ℕ)
    (c : Cfg L K) (hc : Domain σ stage n d c) (a b : AgentState L K)
    (ha : a ∈ c) (hb : b ∈ c)
    (huseful : (Source σ a ∧ Target σ stage b) ∨
      (Target σ stage a ∧ Source σ b)) :
    targetCount σ stage
        (Protocol.stepOrSelf (NonuniformMajority L K) c a b) <
      targetCount σ stage c := by
  classical
  have hne : a ≠ b := by
    intro heq
    subst b
    rcases huseful with h | h
    · exact source_not_target σ stage a h.1 h.2
    · exact source_not_target σ stage a h.2 h.1
  have happ := Phase10Drop.applicable_of_mem_ne ha hb hne
  have hpair := pair_target_drops σ stage a b
    (hc.phase a ha) (hc.phase b hb) (hc.allowed a ha) (hc.allowed b hb) huseful
  have hsplit :
      c.countP (Target σ stage) =
        (c - {a, b}).countP (Target σ stage) +
          ({a, b} : Multiset (AgentState L K)).countP (Target σ stage) := by
    rw [← Multiset.countP_add, Multiset.sub_add_cancel happ]
  unfold Protocol.stepOrSelf
  rw [if_pos happ]
  change ((c - {a, b}) +
    {(Transition L K a b).1, (Transition L K a b).2}).countP (Target σ stage) <
      c.countP (Target σ stage)
  rw [Multiset.countP_add, hsplit]
  omega

def sourceStates (L K : ℕ) (σ : Sign) : Finset (AgentState L K) :=
  Finset.univ.filter (Source σ)

def targetStates (L K : ℕ) (σ : Sign) (stage : Stage) : Finset (AgentState L K) :=
  Finset.univ.filter (Target σ stage)

def usefulPairs (L K : ℕ) (σ : Sign) (stage : Stage) :
    Finset (AgentState L K × AgentState L K) :=
  (sourceStates L K σ ×ˢ targetStates L K σ stage) ∪
    (targetStates L K σ stage ×ˢ sourceStates L K σ)

theorem mem_usefulPairs (σ : Sign) (stage : Stage)
    (p : AgentState L K × AgentState L K) :
    p ∈ usefulPairs L K σ stage ↔
      (Source σ p.1 ∧ Target σ stage p.2) ∨
        (Target σ stage p.1 ∧ Source σ p.2) := by
  simp [usefulPairs, sourceStates, targetStates]

theorem useful_pair_ne (σ : Sign) (stage : Stage)
    (p : AgentState L K × AgentState L K) (hp : p ∈ usefulPairs L K σ stage) :
    p.1 ≠ p.2 := by
  intro heq
  have hu := (mem_usefulPairs σ stage p).mp hp
  rcases hu with hu | hu
  · have ht : Target σ stage p.1 := by rw [heq]; exact hu.2
    exact source_not_target σ stage p.1 hu.1 ht
  · have ht : Target σ stage p.2 := by rw [← heq]; exact hu.1
    exact source_not_target σ stage p.2 hu.2 ht

theorem sum_useful_interactionCount (σ : Sign) (stage : Stage) (c : Cfg L K) :
    (∑ p ∈ usefulPairs L K σ stage, c.interactionCount p.1 p.2) =
      2 * sourceCount σ c * targetCount σ stage c := by
  classical
  have hdisj :
      ∀ a ∈ sourceStates L K σ, ∀ b ∈ targetStates L K σ stage, a ≠ b := by
    intro a ha b hb heq
    have hs : Source σ a := (Finset.mem_filter.mp ha).2
    have ht : Target σ stage b := (Finset.mem_filter.mp hb).2
    subst b
    exact source_not_target σ stage a hs ht
  have hdisj' :
      ∀ b ∈ targetStates L K σ stage, ∀ a ∈ sourceStates L K σ, b ≠ a := by
    intro b hb a ha
    exact (hdisj a ha b hb).symm
  have hrect :
      Disjoint (sourceStates L K σ ×ˢ targetStates L K σ stage)
        (targetStates L K σ stage ×ˢ sourceStates L K σ) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hs : Source σ p.1 :=
      (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
    have ht : Target σ stage p.1 :=
      (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).2
    exact source_not_target σ stage p.1 hs ht
  have hs :
      (∑ a ∈ sourceStates L K σ, c.count a) = sourceCount σ c :=
    (HourCouplingAzuma.countP_eq_sum_count (Source σ) c).symm
  have ht :
      (∑ a ∈ targetStates L K σ stage, c.count a) = targetCount σ stage c :=
    (HourCouplingAzuma.countP_eq_sum_count (Target σ stage) c).symm
  rw [usefulPairs, Finset.sum_union hrect,
    ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj,
    ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj', hs, ht]
  ring

theorem sum_useful_interactionProb (σ : Sign) (stage : Stage) (c : Cfg L K) :
    (∑ p ∈ usefulPairs L K σ stage, c.interactionProb p.1 p.2) =
      (↑(2 * sourceCount σ c * targetCount σ stage c) : ℝ≥0∞) /
        (c.totalPairs : ℝ≥0∞) := by
  classical
  have hterm : ∀ p : AgentState L K × AgentState L K,
      c.interactionProb p.1 p.2 =
        (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro p
    unfold Config.interactionProb
    rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.sum_mul,
    ← Nat.cast_sum, sum_useful_interactionCount, ← div_eq_mul_inv]

theorem useful_mass_le_weighted_drop (σ : Sign) (stage : Stage) (n d : ℕ)
    (c : Cfg L K) (hc : Domain σ stage n d c) :
    (∑ p ∈ usefulPairs L K σ stage, c.interactionProb p.1 p.2) ≤
      WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K)
        (targetCount σ stage) c := by
  classical
  have hterm : ∀ p ∈ usefulPairs L K σ stage,
      c.interactionProb p.1 p.2 ≤
        ((targetCount σ stage c : ℝ≥0∞) -
          (targetCount σ stage
            (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) : ℝ≥0∞)) *
          c.interactionProb p.1 p.2 := by
    intro p hp
    have hne := useful_pair_ne σ stage p hp
    by_cases ha : 1 ≤ c.count p.1
    · by_cases hb : 1 ≤ c.count p.2
      · have hdrop := target_step_lt σ stage n d c hc p.1 p.2
          (Multiset.count_pos.mp ha) (Multiset.count_pos.mp hb)
          ((mem_usefulPairs σ stage p).mp hp)
        have hgap :
            1 ≤ targetCount σ stage c -
              targetCount σ stage
                (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) := by
          omega
        have hgapE :
            (1 : ℝ≥0∞) ≤ (targetCount σ stage c : ℝ≥0∞) -
              (targetCount σ stage
                (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) : ℝ≥0∞) := by
          have hnatCast : (1 : ℝ≥0∞) ≤
              ((targetCount σ stage c -
                targetCount σ stage
                  (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) : ℕ) : ℝ≥0∞) := by
            exact_mod_cast hgap
          simpa only [ENNReal.natCast_sub] using hnatCast
        calc c.interactionProb p.1 p.2 = 1 * c.interactionProb p.1 p.2 := by rw [one_mul]
          _ ≤ _ := mul_le_mul_right' hgapE _
      · have hz : c.count p.2 = 0 := by omega
        simp [Config.interactionProb, Config.interactionCount, hne, hz]
    · have hz : c.count p.1 = 0 := by omega
      simp [Config.interactionProb, Config.interactionCount, hne, hz]
  calc (∑ p ∈ usefulPairs L K σ stage, c.interactionProb p.1 p.2)
      ≤ ∑ p ∈ usefulPairs L K σ stage,
          ((targetCount σ stage c : ℝ≥0∞) -
            (targetCount σ stage
              (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) : ℝ≥0∞)) *
            c.interactionProb p.1 p.2 :=
        Finset.sum_le_sum hterm
    _ ≤ WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K)
        (targetCount σ stage) c := by
      unfold WeightedDriftDropSum.weightedDropSum
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intro p _ _
        exact zero_le)

def sourceRate (n d : ℕ) : ℝ≥0∞ :=
  (↑(2 * d) : ℝ≥0∞) / (↑(n * (n - 1)) : ℝ≥0∞)

theorem target_count_drift (σ : Sign) (stage : Stage) (n d : ℕ)
    (hn : 2 ≤ n) (c : Cfg L K) (hc : Domain σ stage n d c) :
    ∫⁻ c', (targetCount σ stage c' : ℝ≥0∞)
        ∂(NonuniformMajority L K).transitionKernel c ≤
      (1 - sourceRate n d) * targetCount σ stage c := by
  have hsource : d ≤ sourceCount σ c := source_count_floor σ c d hc.gap_floor
  have hden : n * (n - 1) ≠ 0 := by
    have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    omega
  have hfinite : sourceRate n d ≠ ∞ := by
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
      (by exact_mod_cast hden)
  apply WeightedDriftDropSum.weighted_dyadic_mass_drift_of_dropSum
    (NonuniformMajority L K) (targetCount σ stage) c
    (by simpa only [hc.card_eq] using hn)
    (sourceRate n d) hfinite
    (fun p => target_step_le σ stage n d c hc p.1 p.2)
  calc sourceRate n d * (targetCount σ stage c : ℝ≥0∞)
      = (↑(2 * d * targetCount σ stage c) : ℝ≥0∞) /
          (c.totalPairs : ℝ≥0∞) := by
        simp only [sourceRate, Config.totalPairs, hc.card_eq, Nat.cast_mul]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
    _ ≤ (↑(2 * sourceCount σ c * targetCount σ stage c) : ℝ≥0∞) /
        (c.totalPairs : ℝ≥0∞) := by
      gcongr
    _ = ∑ p ∈ usefulPairs L K σ stage, c.interactionProb p.1 p.2 :=
      (sum_useful_interactionProb σ stage c).symm
    _ ≤ _ := useful_mass_le_weighted_drop σ stage n d c hc

/-- The actual-law stage estimate retains the mass of the observed prefix. -/
theorem stage_tail_from_prefix (init : Cfg L K)
    (σ : Sign) (stage : Stage) (n d : ℕ) (hn : 2 ≤ n)
    (s N : ℕ) (A : Set ((k : Finset.Iic s) → Draw L K))
    (hA : ∀ p ∈ A, Domain σ stage n d (prefixCfg init s p)) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        1 ≤ targetCount σ stage (trace init ω (s + N))} ≤
      (1 - sourceRate n d) ^ N * n *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  have htail := TraceDrain.potential_drift_tail_from init (targetCount σ stage)
    (Domain σ stage n d) (sourceRate n d)
    (fun c hc => target_count_drift σ stage n d hn c hc) s N A n (by
      intro p hp
      have hcount := Multiset.countP_le_card (Target σ stage) (prefixCfg init s p)
      exact hcount.trans_eq (hA p hp).card_eq)
  refine (measure_mono ?_).trans htail
  rintro ω ⟨hprefix, htarget⟩
  refine ⟨hprefix, ?_, htarget⟩
  intro u hsu _
  exact domain_preserved_by_reachable σ stage n d
    (trace init ω s) (trace init ω u) (hA _ hprefix)
    (trace_reachable init ω hsu)

theorem absorb_domain_of_cancel_drained (σ : Sign) (n d : ℕ)
    (c : Cfg L K) (hc : Domain σ .cancel n d c)
    (hzero : targetCount σ .cancel c = 0) :
    Domain σ .absorb n d c := by
  refine ⟨hc.card_eq, hc.phase, hc.gap_floor, ?_⟩
  exact Multiset.countP_eq_zero.mp hzero

theorem broadcast_domain_of_absorb_drained (σ : Sign) (n d : ℕ)
    (c : Cfg L K) (hc : Domain σ .absorb n d c)
    (hzero : targetCount σ .absorb c = 0) :
    Domain σ .broadcast n d c := by
  refine ⟨hc.card_eq, hc.phase, hc.gap_floor, ?_⟩
  intro a ha
  exact ⟨hc.allowed a ha, (Multiset.countP_eq_zero.mp hzero) a ha⟩

theorem broadcast_drained_mem_stableDone (σ : Sign) (n d : ℕ) (hd : 0 < d)
    (init c : Cfg L K) (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hc : Domain σ .broadcast n d c)
    (hzero : targetCount σ .broadcast c = 0) :
    c ∈ StableDone L K init := by
  have hsum := phase10ActiveSignedSum_eq_initialGap_of_reachable
    init c hinit hreach hc.phase
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  cases σ with
  | pos =>
      have hpos : 0 < phase10ActiveSignedSum c :=
        lt_of_lt_of_le hdZ hc.gap_floor
      exact phase10Majority_drained_mem_stableDone init c
        (by rwa [← hsum]) ⟨hc.phase, hc.card_eq, hpos⟩ hzero
  | neg =>
      have hneg : phase10ActiveSignedSum c < 0 := by
        have hfloor := hc.gap_floor
        change (d : ℤ) ≤ -phase10ActiveSignedSum c at hfloor
        omega
      exact phase10BMajority_drained_mem_stableDone init c
        (by rwa [← hsum]) ⟨hc.phase, hc.card_eq, hneg⟩ hzero


end Ripple.PopulationProtocol.ExactMajority.StrongGapBackup

end
