-- Ripple/PopulationProtocol/ExactMajority/Probability/LateAcceptedCounterCoupling.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateAcceptedRectangleHazard
import Ripple.PopulationProtocol.ExactMajority.Probability.LateAcceptedTrialTail
import Ripple.PopulationProtocol.ExactMajority.Probability.LateFrozenPoolOriginalLaw

/-!
# The actual accepted-sample counter

The threshold on the number of frozen Mains is part of the reward predicates,
not the absorbing gate.  Hence the counter can start at the genuine Phase-4
prefix while counting only late accepted samples.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateAcceptedCounterCoupling

open TimeTheorem PairLog PairLogAuxiliary
open LateF6Acceptance LateF6Hazards LateF6OriginalLaw
open LateAcceptedRectangleHazard LateSamplingCounterTail
open LateSamplingEarlyRoles LateSamplingFirstHit
open LateSamplingClassGates LateFrozenPoolOriginalLaw

variable {L K n : ℕ}

/-- A newly accepted sample whose stored index lies outside `J`. -/
def actualPairBad (J : Finset (Fin (L + 1)))
    (f : Fin n → AgentState L K) (i j : Fin n) : Prop :=
  (Accepted (f i) (Transition L K (f i) (f j)).1 ∧
      (Transition L K (f i) (f j)).1.hour ∉ J) ∨
    (Accepted (f j) (Transition L K (f i) (f j)).2 ∧
      (Transition L K (f i) (f j)).2.hour ∉ J)

private theorem acceptedReserve_not_new
    (r r' : AgentState L K) (h : AcceptedReserve r) :
    ¬ Accepted r r' := by
  intro ha
  have h2 : r.phase.val = 5 := h.2.1
  have h3 : r.hour.val < L := h.2.2
  rcases ha.2.1 with hp | hh
  · omega
  · omega

/-- An accepted Reserve persists, and the only other way for the left output
 to be accepted is a genuine new `Accepted` write. -/
theorem acceptedReserve_left_iff (s t : AgentState L K)
    (hs : Window s) (ht : Window t) :
    AcceptedReserve (Transition L K s t).1 ↔
      AcceptedReserve s ∨ Accepted s (Transition L K s t).1 := by
  constructor
  · intro hout
    by_cases hold : AcceptedReserve s
    · exact Or.inl hold
    · right
      have hrole : s.role = .reserve :=
        (transition_roles s t hs ht).1.symm.trans hout.1
      refine ⟨hrole, ?_, hout.1, hout.2.1, hout.2.2⟩
      have hs5 : s.phase.val ≤ 5 := hs.2
      by_cases hp : s.phase.val = 5
      · right
        have hnot : ¬ s.hour.val < L := by
          intro hh
          exact hold ⟨hrole, hp, hh⟩
        have hle := s.hour.isLt
        omega
      · left
        omega
  · rintro (hold | hnew)
    · have hl := transition_locked_left s t hs ht hold.1 hold.2.1
        (Nat.ne_of_lt hold.2.2)
      refine ⟨hl.1, hl.2.1, ?_⟩
      simpa only [hl.2.2] using hold.2.2
    · exact ⟨hnew.2.2.1, hnew.2.2.2.1, hnew.2.2.2.2⟩

/-- Right-output version of `acceptedReserve_left_iff`. -/
theorem acceptedReserve_right_iff (s t : AgentState L K)
    (hs : Window s) (ht : Window t) :
    AcceptedReserve (Transition L K s t).2 ↔
      AcceptedReserve t ∨ Accepted t (Transition L K s t).2 := by
  constructor
  · intro hout
    by_cases hold : AcceptedReserve t
    · exact Or.inl hold
    · right
      have hrole : t.role = .reserve :=
        (transition_roles s t hs ht).2.symm.trans hout.1
      refine ⟨hrole, ?_, hout.1, hout.2.1, hout.2.2⟩
      have ht5 : t.phase.val ≤ 5 := ht.2
      by_cases hp : t.phase.val = 5
      · right
        have hnot : ¬ t.hour.val < L := by
          intro hh
          exact hold ⟨hrole, hp, hh⟩
        have hle := t.hour.isLt
        omega
      · left
        omega
  · rintro (hold | hnew)
    · have hr := transition_locked_right s t hs ht hold.1 hold.2.1
        (Nat.ne_of_lt hold.2.2)
      refine ⟨hr.1, hr.2.1, ?_⟩
      simpa only [hr.2.2] using hold.2.2
    · exact ⟨hnew.2.2.1, hnew.2.2.2.1, hnew.2.2.2.2⟩

/-- A bad stored sample also persists exactly; otherwise it is a genuine new
 accepted write outside `J`. -/
theorem badSample_left_iff (J : Finset (Fin (L + 1)))
    (s t : AgentState L K) (hs : Window s) (ht : Window t) :
    BadSample J (Transition L K s t).1 ↔
      BadSample J s ∨
        (Accepted s (Transition L K s t).1 ∧
          (Transition L K s t).1.hour ∉ J) := by
  constructor
  · rintro ⟨hout, hJ⟩
    rcases (acceptedReserve_left_iff s t hs ht).mp hout with hold | hnew
    · left
      have hl := transition_locked_left s t hs ht hold.1 hold.2.1
        (Nat.ne_of_lt hold.2.2)
      refine ⟨hold, ?_⟩
      intro hin
      apply hJ
      rw [hl.2.2]
      exact hin
    · exact Or.inr ⟨hnew, hJ⟩
  · rintro (hold | hnew)
    · have hl := transition_locked_left s t hs ht hold.1.1 hold.1.2.1
        (Nat.ne_of_lt hold.1.2.2)
      refine ⟨(acceptedReserve_left_iff s t hs ht).mpr (Or.inl hold.1), ?_⟩
      intro hin
      apply hold.2
      rw [← hl.2.2]
      exact hin
    · exact ⟨(acceptedReserve_left_iff s t hs ht).mpr (Or.inr hnew.1),
        hnew.2⟩

/-- Right-output version of `badSample_left_iff`. -/
theorem badSample_right_iff (J : Finset (Fin (L + 1)))
    (s t : AgentState L K) (hs : Window s) (ht : Window t) :
    BadSample J (Transition L K s t).2 ↔
      BadSample J t ∨
        (Accepted t (Transition L K s t).2 ∧
          (Transition L K s t).2.hour ∉ J) := by
  constructor
  · rintro ⟨hout, hJ⟩
    rcases (acceptedReserve_right_iff s t hs ht).mp hout with hold | hnew
    · left
      have hr := transition_locked_right s t hs ht hold.1 hold.2.1
        (Nat.ne_of_lt hold.2.2)
      refine ⟨hold, ?_⟩
      intro hin
      apply hJ
      rw [hr.2.2]
      exact hin
    · exact Or.inr ⟨hnew, hJ⟩
  · rintro (hold | hnew)
    · have hr := transition_locked_right s t hs ht hold.1.1 hold.1.2.1
        (Nat.ne_of_lt hold.1.2.2)
      refine ⟨(acceptedReserve_right_iff s t hs ht).mpr (Or.inl hold.1), ?_⟩
      intro hin
      apply hold.2
      rw [← hr.2.2]
      exact hin
    · exact ⟨(acceptedReserve_right_iff s t hs ht).mpr (Or.inr hnew.1),
        hnew.2⟩

private theorem actual_accepts_disjoint
    (f : Fin n → AgentState L K) (hw : ∀ i, Window (f i))
    (i j : Fin n)
    (hl : Accepted (f i) (Transition L K (f i) (f j)).1)
    (hr : Accepted (f j) (Transition L K (f i) (f j)).2) : False := by
  have hright := (transition_accept_right (f i) (f j) (hw i) (hw j)).mp hr
  have hmain : (f i).role = .main := by
    rcases hright.2 with h | h
    · exact h.2.2.1
    · exact h.2.2.1
  have he : (Role.reserve : Role) = .main := hl.1.symm.trans hmain
  cases he

/-- The output-index definition of a bad accepted sample is exactly the bad
 rectangle whose partner bias is outside `indexClass J`. -/
theorem actualPairBad_iff_badAcceptedRectangle
    (J : Finset (Fin (L + 1)))
    (f : Fin n → AgentState L K)
    (hw : ∀ i, Window (f i))
    (hcanonical : ∀ i, Eligible (f i) → 4 ≤ (f i).phase.val →
      (f i).phase.val = 5)
    (i j : Fin n) :
    actualPairBad J f i j ↔
      badAcceptedRectangle (indexClass J) f i j := by
  unfold actualPairBad badAcceptedRectangle contact badEligible badFrozenEligible
  constructor
  · rintro (⟨hl, hJ⟩ | ⟨hr, hJ⟩)
    · have hrect := (transition_accept_rectangles_left
        (f i) (f j) (hw i) (hw j) (hcanonical j)).mp hl
      have hnot : ¬ indexClass J (f j).bias := by
        intro hc
        exact hJ ((accepted_left_stores_indexClass J
          (f i) (f j) (hw i) (hw j) hl).mp hc)
      rcases hrect with hrect | hrect
      · exact Or.inl (Or.inl ⟨hrect.1, hrect.2, hnot⟩)
      · exact Or.inr (Or.inl ⟨hrect.1, hrect.2, hnot⟩)
    · have hrect := (transition_accept_rectangles_right
        (f i) (f j) (hw i) (hw j) (hcanonical i)).mp hr
      have hnot : ¬ indexClass J (f i).bias := by
        intro hc
        exact hJ ((accepted_right_stores_indexClass J
          (f i) (f j) (hw i) (hw j) hr).mp hc)
      rcases hrect with hrect | hrect
      · exact Or.inl (Or.inr ⟨⟨hrect.2, hnot⟩, hrect.1⟩)
      · exact Or.inr (Or.inr ⟨⟨hrect.2, hnot⟩, hrect.1⟩)
  · rintro ((⟨hr, he, hnot⟩ | ⟨⟨he, hnot⟩, hr⟩) |
      (⟨hr, he, hnot⟩ | ⟨⟨he, hnot⟩, hr⟩))
    · have hl := (transition_accept_rectangles_left
        (f i) (f j) (hw i) (hw j) (hcanonical j)).mpr
          (Or.inl ⟨hr, he⟩)
      refine Or.inl ⟨hl, ?_⟩
      intro hstored
      exact hnot ((accepted_left_stores_indexClass J
        (f i) (f j) (hw i) (hw j) hl).mpr hstored)
    · have hright := (transition_accept_rectangles_right
        (f i) (f j) (hw i) (hw j) (hcanonical i)).mpr
          (Or.inl ⟨hr, he⟩)
      refine Or.inr ⟨hright, ?_⟩
      intro hstored
      exact hnot ((accepted_right_stores_indexClass J
        (f i) (f j) (hw i) (hw j) hright).mpr hstored)
    · have hl := (transition_accept_rectangles_left
        (f i) (f j) (hw i) (hw j) (hcanonical j)).mpr
          (Or.inr ⟨hr, he⟩)
      refine Or.inl ⟨hl, ?_⟩
      intro hstored
      exact hnot ((accepted_left_stores_indexClass J
        (f i) (f j) (hw i) (hw j) hl).mpr hstored)
    · have hright := (transition_accept_rectangles_right
        (f i) (f j) (hw i) (hw j) (hcanonical i)).mpr
          (Or.inr ⟨hr, he⟩)
      refine Or.inr ⟨hright, ?_⟩
      intro hstored
      exact hnot ((accepted_right_stores_indexClass J
        (f i) (f j) (hw i) (hw j) hright).mpr hstored)

/-- Exact accepted-count update for one actual selected pair. -/
theorem acceptedCount_update
    (f : Fin n → AgentState L K)
    (hw : ∀ i, Window (f i))
    (hcanonical : ∀ i, Eligible (f i) → 4 ≤ (f i).phase.val →
      (f i).phase.val = 5)
    (i j : Fin n) (hij : i ≠ j) :
    acceptedCount (updateLabels f i j) =
      acceptedCount f + bitNat (acceptedRectangle f i j) := by
  have hbalance := pool_updateLabels_balance f AcceptedReserve i j hij
  change acceptedCount (updateLabels f i j) +
      bitNat (AcceptedReserve (f i)) + bitNat (AcceptedReserve (f j)) =
    acceptedCount f +
      bitNat (AcceptedReserve (Transition L K (f i) (f j)).1) +
      bitNat (AcceptedReserve (Transition L K (f i) (f j)).2) at hbalance
  have hl := bitNat_add_of_iff _ _ _
    (acceptedReserve_left_iff (f i) (f j) (hw i) (hw j))
    (fun hold hnew => acceptedReserve_not_new _ _ hold hnew)
  have hr := bitNat_add_of_iff _ _ _
    (acceptedReserve_right_iff (f i) (f j) (hw i) (hw j))
    (fun hold hnew => acceptedReserve_not_new _ _ hold hnew)
  rw [hl, hr] at hbalance
  have hnew : bitNat (acceptedRectangle f i j) =
      bitNat (Accepted (f i) (Transition L K (f i) (f j)).1) +
        bitNat (Accepted (f j) (Transition L K (f i) (f j)).2) := by
    have heq := propext (acceptedRectangle_iff_actual f hw hcanonical i j)
    rw [← heq]
    unfold actualPairAccepted
    exact bitNat_or_of_disjoint _ _
      (actual_accepts_disjoint f hw i j)
  omega

/-- Exact bad-sample update for one actual selected pair. -/
theorem badSampleCount_update
    (J : Finset (Fin (L + 1)))
    (f : Fin n → AgentState L K)
    (hw : ∀ i, Window (f i))
    (hcanonical : ∀ i, Eligible (f i) → 4 ≤ (f i).phase.val →
      (f i).phase.val = 5)
    (i j : Fin n) (hij : i ≠ j) :
    badSampleCount J (updateLabels f i j) =
      badSampleCount J f +
        bitNat (badAcceptedRectangle (indexClass J) f i j) := by
  have hbalance := pool_updateLabels_balance f (BadSample J) i j hij
  change badSampleCount J (updateLabels f i j) +
      bitNat (BadSample J (f i)) + bitNat (BadSample J (f j)) =
    badSampleCount J f +
      bitNat (BadSample J (Transition L K (f i) (f j)).1) +
      bitNat (BadSample J (Transition L K (f i) (f j)).2) at hbalance
  have hl := bitNat_add_of_iff _ _ _
    (badSample_left_iff J (f i) (f j) (hw i) (hw j))
    (fun hold hnew => acceptedReserve_not_new _ _ hold.1 hnew.1)
  have hr := bitNat_add_of_iff _ _ _
    (badSample_right_iff J (f i) (f j) (hw i) (hw j))
    (fun hold hnew => acceptedReserve_not_new _ _ hold.1 hnew.1)
  rw [hl, hr] at hbalance
  have hnew : bitNat (badAcceptedRectangle (indexClass J) f i j) =
      bitNat (Accepted (f i) (Transition L K (f i) (f j)).1 ∧
        (Transition L K (f i) (f j)).1.hour ∉ J) +
      bitNat (Accepted (f j) (Transition L K (f i) (f j)).2 ∧
        (Transition L K (f i) (f j)).2.hour ∉ J) := by
    have heq := propext
      (actualPairBad_iff_badAcceptedRectangle J f hw hcanonical i j)
    rw [← heq]
    unfold actualPairBad
    exact bitNat_or_of_disjoint _ _
      (fun h h' => actual_accepts_disjoint f hw i j h.1 h'.1)
  omega

/-- Draw-level accepted-count update, including the no-pair draw. -/
theorem acceptedCount_step
    (f : Fin n → AgentState L K)
    (hw : ∀ i, Window (f i))
    (hcanonical : ∀ i, Eligible (f i) → 4 ≤ (f i).phase.val →
      (f i).phase.val = 5)
    (d : Draw L K) :
    acceptedCount (stepLabels f d) = acceptedCount f +
      bitNat (chosen acceptedRectangle f d) := by
  simpa only [chosen] using
    count_step_of_update acceptedCount acceptedRectangle f
      (acceptedCount_update f hw hcanonical) d

/-- Draw-level bad-sample update. -/
theorem badSampleCount_step
    (J : Finset (Fin (L + 1)))
    (f : Fin n → AgentState L K)
    (hw : ∀ i, Window (f i))
    (hcanonical : ∀ i, Eligible (f i) → 4 ≤ (f i).phase.val →
      (f i).phase.val = 5)
    (d : Draw L K) :
    badSampleCount J (stepLabels f d) = badSampleCount J f +
      bitNat (chosen (badAcceptedRectangle (indexClass J)) f d) := by
  simpa only [chosen] using
    count_step_of_update (badSampleCount J)
      (badAcceptedRectangle (indexClass J)) f
      (badSampleCount_update J f hw hcanonical) d

theorem acceptedCount_le_card (f : Fin n → AgentState L K) :
    acceptedCount f ≤ n := by
  classical
  have hsub : pool f AcceptedReserve ⊆ (Finset.univ : Finset (Fin n)) :=
    fun _ _ => Finset.mem_univ _
  simpa [acceptedCount] using Finset.card_le_card hsub

theorem badSampleCount_le_accepted
    (J : Finset (Fin (L + 1))) (f : Fin n → AgentState L K) :
    badSampleCount J f ≤ acceptedCount f :=
  pool_mono f (BadSample J) AcceptedReserve (fun _ h => h.1)

theorem badSampleCount_le_card
    (J : Finset (Fin (L + 1))) (f : Fin n → AgentState L K) :
    badSampleCount J f ≤ n :=
  (badSampleCount_le_accepted J f).trans (acceptedCount_le_card f)

/-- Only accepted writes whose pre-state has at least `k` frozen Mains. -/
def lateAcceptedRectangle (k : ℕ)
    (f : Fin n → AgentState L K) (i j : Fin n) : Prop :=
  k ≤ frozenCount f ∧ acceptedRectangle f i j

/-- The corresponding late bad writes. -/
def lateBadAcceptedRectangle (k : ℕ) (J : Finset (Fin (L + 1)))
    (f : Fin n → AgentState L K) (i j : Fin n) : Prop :=
  k ≤ frozenCount f ∧ badAcceptedRectangle (indexClass J) f i j

private theorem badAcceptedRectangle_subset
    (C : Bias L → Prop) (f : Fin n → AgentState L K) (i j : Fin n) :
    badAcceptedRectangle C f i j → acceptedRectangle f i j := by
  unfold badAcceptedRectangle acceptedRectangle contact
  unfold badEligible badFrozenEligible
  tauto

/-- The class receipt retained in the absorbing gate. -/
def AcceptedGate (M A : ℕ) (J : Finset (Fin (L + 1))) (γ : ℝ)
    (f : Fin n → AgentState L K) : Prop :=
  mainCount f = M ∧
    A ≤ classCount (indexClass J) f ∧
    FrozenFloor (indexClass J) A M γ f

/-- The stopped counter instantiated with the two actual rectangles.
The threshold is deliberately in `event` and `bad`, not in `gate`. -/
def acceptedCounter (init : Cfg L K) (s k M A : ℕ)
    (J : Finset (Fin (L + 1))) (γ : ℝ) : CounterSpec init where
  start := s
  cap := init.card + 1
  debt := init.card
  gate := fun t p _ => AcceptedGate M A J γ (prefixLabels init t p)
  event := lateAcceptedRectangle k
  bad := lateBadAcceptedRectangle k J
  bad_subset := by
    intro f i j h
    exact ⟨h.1, badAcceptedRectangle_subset _ _ _ _ h.2⟩

private theorem label_mem_trace' (init : Cfg L K) (ω : Ω L K)
    (u : ℕ) (i : Fin init.card) :
    labelsAt init ω u i ∈ trace init ω u := by
  rw [← labelsAt_config init ω u]
  exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩

/-- The stopped accepted counter cannot count a write absent from the actual
accepted pool.  No gate-survival hypothesis is needed for this direction. -/
theorem acceptedCounter_count_le_actual
    {init : InputCfg n} {ω : InputLog n} {a s T : ℕ}
    (h : Prefix init ω a s T)
    (k M A : ℕ)
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (γ : ℝ) (u : ℕ) (hsu : s ≤ u) (huT : u ≤ T) :
    ((acceptedCounter init s k M A J γ).state ω u).1 ≤
      acceptedCount (labelsAt init ω u) := by
  set Q := acceptedCounter init s k M A J γ with hQ
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsu
  revert huT
  induction d with
  | zero =>
      intro _
      simp only [Nat.add_zero]
      rw [Q.state_before_start ω s (by simp [hQ, acceptedCounter])]
      simp
  | succ d ih =>
      intro hT
      have hi := ih (by omega)
      have hw0 := h.window (s + d) (h.start_order.trans (by omega)) (by omega)
      have hw : ∀ i, Window (labelsAt init ω (s + d) i) :=
        fun i => hw0 _ (label_mem_trace' init ω (s + d) i)
      have hc := h.canonical (s + d) (h.start_order.trans (by omega)) (by omega)
      have hstep := acceptedCount_step (labelsAt init ω (s + d)) hw hc
        (ω (s + d + 1))
      have hbit : Q.eventBit (s + d) ω ≤
          bitNat (chosen acceptedRectangle
            (labelsAt init ω (s + d)) (ω (s + d + 1))) := by
        unfold CounterSpec.eventBit
        apply bitNat_mono
        rintro ⟨_, hchosen⟩
        rcases hchosen with ⟨i, j, hsel, hlate⟩
        change k ≤ frozenCount (labelsAt init ω (s + d)) ∧
          acceptedRectangle (labelsAt init ω (s + d)) i j at hlate
        exact ⟨i, j, hsel, hlate.2⟩
      rw [show s + (d + 1) = (s + d) + 1 by omega,
        Q.count_succ, labelsAt_succ, hstep]
      omega

/-- Bad-counter counterpart of `acceptedCounter_count_le_actual`. -/
theorem acceptedCounter_bad_le_actual
    {init : InputCfg n} {ω : InputLog n} {a s T : ℕ}
    (h : Prefix init ω a s T)
    (k M A : ℕ)
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (γ : ℝ) (u : ℕ) (hsu : s ≤ u) (huT : u ≤ T) :
    ((acceptedCounter init s k M A J γ).state ω u).2.1 ≤
      badSampleCount J (labelsAt init ω u) := by
  set Q := acceptedCounter init s k M A J γ with hQ
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsu
  revert huT
  induction d with
  | zero =>
      intro _
      simp only [Nat.add_zero]
      rw [Q.state_before_start ω s (by simp [hQ, acceptedCounter])]
      simp
  | succ d ih =>
      intro hT
      have hi := ih (by omega)
      have hw0 := h.window (s + d) (h.start_order.trans (by omega)) (by omega)
      have hw : ∀ i, Window (labelsAt init ω (s + d) i) :=
        fun i => hw0 _ (label_mem_trace' init ω (s + d) i)
      have hc := h.canonical (s + d) (h.start_order.trans (by omega)) (by omega)
      have hstep := badSampleCount_step J (labelsAt init ω (s + d)) hw hc
        (ω (s + d + 1))
      have hbit : Q.badBit (s + d) ω ≤
          bitNat (chosen (badAcceptedRectangle (indexClass J))
            (labelsAt init ω (s + d)) (ω (s + d + 1))) := by
        unfold CounterSpec.badBit
        apply bitNat_mono
        rintro ⟨_, hchosen⟩
        rcases hchosen with ⟨i, j, hsel, hlate⟩
        change k ≤ frozenCount (labelsAt init ω (s + d)) ∧
          badAcceptedRectangle (indexClass J)
            (labelsAt init ω (s + d)) i j at hlate
        exact ⟨i, j, hsel, hlate.2⟩
      rw [show s + (d + 1) = (s + d) + 1 by omega,
        Q.bad_succ, labelsAt_succ, hstep]
      omega

/-- A surviving class receipt makes the counter live at every raw prefix.
The cap and debt side conditions are discharged from the actual finite pools. -/
theorem acceptedCounter_active
    {init : InputCfg n} {ω : InputLog n} {a s T : ℕ}
    (h : Prefix init ω a s T)
    (k M A : ℕ)
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (γ : ℝ)
    (hgate : ∀ u, s ≤ u → u < T →
      AcceptedGate M A J γ (labelsAt init ω u)) :
    ∀ u, s ≤ u → u < T →
      (acceptedCounter init s k M A J γ).active u ω := by
  set Q := acceptedCounter init s k M A J γ with hQ
  intro u hsu huT
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsu
  revert huT
  induction d with
  | zero =>
      intro hsT
      unfold CounterSpec.active CounterSpec.Enabled
      simp only [Nat.add_zero]
      rw [Q.state_before_start ω s (by simp [hQ, acceptedCounter])]
      refine ⟨by simp [hQ, acceptedCounter], rfl, ?_, ?_, ?_⟩
      · simpa [Q, acceptedCounter, labelsAt] using hgate s le_rfl hsT
      · simp [Q, acceptedCounter]
      · simp [Q, acceptedCounter]
  | succ d ih =>
      intro hT
      have hprev := ih (by omega) (by omega)
      have hlive := Q.live_succ ω (s + d) hprev
      have hcount : (Q.state ω (s + d + 1)).1 ≤
          acceptedCount (labelsAt init ω (s + d + 1)) :=
        acceptedCounter_count_le_actual h k M A J γ
          (s + d + 1) (by omega) (by omega)
      have hbad : (Q.state ω (s + d + 1)).2.1 ≤
          badSampleCount J (labelsAt init ω (s + d + 1)) :=
        acceptedCounter_bad_le_actual h k M A J γ
          (s + d + 1) (by omega) (by omega)
      have hcountCard := acceptedCount_le_card (labelsAt init ω (s + d + 1))
      have hbadCard := badSampleCount_le_card J (labelsAt init ω (s + d + 1))
      rw [show s + (d + 1) = (s + d) + 1 by omega]
      unfold CounterSpec.active CounterSpec.Enabled
      refine ⟨by show s ≤ s + d + 1; omega, hlive, ?_, ?_, ?_⟩
      · simpa [Q, acceptedCounter, labelsAt] using
          hgate (s + d + 1) (by omega) (by omega)
      · change (Q.state ω (s + d + 1)).1 < init.card + 1
        omega
      · change (Q.state ω (s + d + 1)).2.1 ≤ init.card
        omega

/-- Outside the shared early-role event, fewer than `k` accepted samples exist
at every prefix having fewer than `k` frozen Mains. -/
theorem acceptedCount_lt_earlyCap
    {init : InputCfg n} {ω : InputLog n} {a s T M R k : ℕ}
    (h : Prefix init ω a s T)
    (hM : mainCount (labelsAt init ω s) = M)
    (hR : reserveCount (labelsAt init ω s) = R)
    (hnot : ω ∉ EarlyRoleEvent init s M R k)
    (u : ℕ) (hsu : s ≤ u) (huT : u ≤ T)
    (hfrozen : frozenCount (labelsAt init ω u) < k) :
    acceptedCount (labelsAt init ω u) < k := by
  have hle := acceptedCount_le_reserveFrozenCount (labelsAt init ω u)
  by_contra hbad
  have hk : k ≤ reserveFrozenCount (labelsAt init ω u) := by omega
  apply hnot
  have hzero := prefix_start_counts_zero h
  refine ⟨hzero.2.2.1, hzero.2.2.2, u, hsu, ?_, hfrozen, hk⟩
  intro t hst htu
  have htT : t ≤ T := (le_of_lt htu).trans huT
  refine ⟨fun i => h.window t (h.start_order.trans hst) htT _
    (label_mem_trace' init ω t i), ?_, ?_⟩
  · exact (prefix_main_count h hst htT).trans hM
  · exact (prefix_reserve_count h hst htT).trans hR

/-- Simultaneous pathwise coupling.  The first component is needed to lower
bound the number of late trials; the second is the requested bad-sample bound. -/
theorem actual_counts_le_stopped_add_earlyCap
    {init : InputCfg n} {ω : InputLog n} {a s T M R k A : ℕ}
    (h : Prefix init ω a s T)
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (γ : ℝ)
    (hM : mainCount (labelsAt init ω s) = M)
    (hR : reserveCount (labelsAt init ω s) = R)
    (hk : 0 < k)
    (hgate : ∀ u, s ≤ u → u < T →
      AcceptedGate M A J γ (labelsAt init ω u))
    (hnot : ω ∉ EarlyRoleEvent init s M R k)
    (u : ℕ) (hsu : s ≤ u) (huT : u ≤ T) :
    acceptedCount (labelsAt init ω u) ≤
        ((acceptedCounter init s k M A J γ).state ω u).1 + k ∧
      badSampleCount J (labelsAt init ω u) ≤
        ((acceptedCounter init s k M A J γ).state ω u).2.1 + k := by
  set Q := acceptedCounter init s k M A J γ with hQ
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsu
  revert huT
  induction d with
  | zero =>
      intro _
      have hzero := prefix_start_counts_zero h
      have hbadzero := prefix_start_bad_counts_zero h (indexClass J) J
      simp only [Nat.add_zero]
      rw [Q.state_before_start ω s (by simp [hQ, acceptedCounter])]
      omega
  | succ d ih =>
      intro hT
      have hi := ih (by omega)
      have hw0 := h.window (s + d) (h.start_order.trans (by omega)) (by omega)
      have hw : ∀ i, Window (labelsAt init ω (s + d) i) :=
        fun i => hw0 _ (label_mem_trace' init ω (s + d) i)
      have hc := h.canonical (s + d) (h.start_order.trans (by omega)) (by omega)
      have haccStep := acceptedCount_step (labelsAt init ω (s + d)) hw hc
        (ω (s + d + 1))
      have hbadStep := badSampleCount_step J (labelsAt init ω (s + d)) hw hc
        (ω (s + d + 1))
      by_cases hlate : k ≤ frozenCount (labelsAt init ω (s + d))
      · have hactive := acceptedCounter_active h k M A J γ hgate
          (s + d) (by omega) (by omega)
        have heventProp :
            (Q.active (s + d) ω ∧
              chosen Q.event (labelsAt init ω (s + d)) (ω (s + d + 1))) ↔
            chosen acceptedRectangle
              (labelsAt init ω (s + d)) (ω (s + d + 1)) := by
          constructor
          · rintro ⟨_, i, j, hsel, hpred⟩
            change k ≤ frozenCount (labelsAt init ω (s + d)) ∧
              acceptedRectangle (labelsAt init ω (s + d)) i j at hpred
            exact ⟨i, j, hsel, hpred.2⟩
          · rintro ⟨i, j, hsel, hpred⟩
            refine ⟨hactive, i, j, hsel, ?_⟩
            exact ⟨hlate, hpred⟩
        have hbadProp :
            (Q.active (s + d) ω ∧
              chosen Q.bad (labelsAt init ω (s + d)) (ω (s + d + 1))) ↔
            chosen (badAcceptedRectangle (indexClass J))
              (labelsAt init ω (s + d)) (ω (s + d + 1)) := by
          constructor
          · rintro ⟨_, i, j, hsel, hpred⟩
            change k ≤ frozenCount (labelsAt init ω (s + d)) ∧
              badAcceptedRectangle (indexClass J)
                (labelsAt init ω (s + d)) i j at hpred
            exact ⟨i, j, hsel, hpred.2⟩
          · rintro ⟨i, j, hsel, hpred⟩
            refine ⟨hactive, i, j, hsel, ?_⟩
            exact ⟨hlate, hpred⟩
        have hevent : Q.eventBit (s + d) ω =
            bitNat (chosen acceptedRectangle
              (labelsAt init ω (s + d)) (ω (s + d + 1))) := by
          unfold CounterSpec.eventBit
          exact congrArg bitNat (propext heventProp)
        have hbadbit : Q.badBit (s + d) ω =
            bitNat (chosen (badAcceptedRectangle (indexClass J))
              (labelsAt init ω (s + d)) (ω (s + d + 1))) := by
          unfold CounterSpec.badBit
          exact congrArg bitNat (propext hbadProp)
        constructor
        · rw [show s + (d + 1) = (s + d) + 1 by omega,
            labelsAt_succ, haccStep, Q.count_succ, hevent]
          omega
        · rw [show s + (d + 1) = (s + d) + 1 by omega,
            labelsAt_succ, hbadStep, Q.bad_succ, hbadbit]
          omega
      · have hpre := acceptedCount_lt_earlyCap h hM hR hnot
          (s + d) (by omega) (by omega) (by omega)
        have hbit := bitNat_zero_one
          (chosen acceptedRectangle
            (labelsAt init ω (s + d)) (ω (s + d + 1)))
        have hpost : acceptedCount (labelsAt init ω (s + d + 1)) ≤ k := by
          rw [labelsAt_succ, haccStep]
          omega
        have hbadpost := badSampleCount_le_accepted J
          (labelsAt init ω (s + d + 1))
        rw [show s + (d + 1) = (s + d) + 1 by omega]
        constructor <;> omega

/-- Requested consumer form at the observed endpoint. -/
theorem actual_bad_le_stopped_late_bad_add_earlyCap
    {init : InputCfg n} {ω : InputLog n} {a s T M R k A : ℕ}
    (h : Prefix init ω a s T)
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (γ : ℝ)
    (hM : mainCount (labelsAt init ω s) = M)
    (hR : reserveCount (labelsAt init ω s) = R)
    (hk : 0 < k)
    (hgate : ∀ u, s ≤ u → u < T →
      AcceptedGate M A J γ (labelsAt init ω u))
    (hnot : ω ∉ EarlyRoleEvent init s M R k) :
    badSampleCount J (labelsAt init ω T) ≤
      ((acceptedCounter init s k M A J γ).state ω T).2.1 + k :=
  (actual_counts_le_stopped_add_earlyCap h J γ hM hR hk hgate hnot
    T h.observed le_rfl).2

end Ripple.PopulationProtocol.ExactMajority.LateAcceptedCounterCoupling

end
