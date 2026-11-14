-- Ripple/PopulationProtocol/ExactMajority/Probability/LateF6RoleArrivals.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6CountSteps
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6HazardBounds

noncomputable section
namespace Ripple.PopulationProtocol.ExactMajority.LateF6Hazards
open TimeTheorem PairLog PairLogAuxiliary LateF6Acceptance
variable {L K n : ℕ}

def TrackedFresh (R : Role → Prop) (a : AgentState L K) : Prop :=
  R a.role ∧ a.phase.val < 4
def TrackedFrozen (R : Role → Prop) (a : AgentState L K) : Prop :=
  R a.role ∧ 4 ≤ a.phase.val
def trackedCount (R : Role → Prop) (f : Fin n → AgentState L K) : ℕ :=
  (pool f (fun a => R a.role)).card
def trackedFrozenCount (R : Role → Prop) (f : Fin n → AgentState L K) : ℕ :=
  (pool f (TrackedFrozen R)).card
def trackedArrival (R : Role → Prop) (f : Fin n → AgentState L K)
    (i j : Fin n) : Prop := contact (TrackedFresh R) Infected f i j

theorem trackedFrozen_left_iff (R : Role → Prop)
    (hR : ∀ r, R r → r ≠ .clock) (s t : AgentState L K)
    (hs : Window s) (ht : Window t) :
    TrackedFrozen R (Transition L K s t).1 ↔
      TrackedFrozen R s ∨ (TrackedFresh R s ∧ Infected t) := by
  have hr := (transition_roles s t hs ht).1
  constructor
  · intro h
    have hrole : R s.role := by simpa only [hr] using h.1
    by_cases hp : 4 ≤ s.phase.val
    · exact Or.inl ⟨hrole, hp⟩
    · have hlt : s.phase.val < 4 := by omega
      exact Or.inr ⟨⟨hrole, hlt⟩,
        ((nonclock_freezes_left s t hs ht (hR _ hrole)).mp ⟨hlt, h.2⟩).2⟩
  · rintro (h | h)
    · refine ⟨by simpa only [hr] using h.1, ?_⟩
      exact h.2.trans ((le_max_left _ _).trans
        ((phaseEpidemicUpdate_left_phase_ge_max L K s t).trans
          (phaseEpidemicUpdate_phase_le_Transition_phase L K s t).1))
    · exact ⟨by simpa only [hr] using h.1.1,
        ((nonclock_freezes_left s t hs ht (hR _ h.1.1)).mpr ⟨h.1.2, h.2⟩).2⟩

theorem trackedFrozen_right_iff (R : Role → Prop)
    (hR : ∀ r, R r → r ≠ .clock) (s t : AgentState L K)
    (hs : Window s) (ht : Window t) :
    TrackedFrozen R (Transition L K s t).2 ↔
      TrackedFrozen R t ∨ (Infected s ∧ TrackedFresh R t) := by
  have hr := (transition_roles s t hs ht).2
  constructor
  · intro h
    have hrole : R t.role := by simpa only [hr] using h.1
    by_cases hp : 4 ≤ t.phase.val
    · exact Or.inl ⟨hrole, hp⟩
    · have hlt : t.phase.val < 4 := by omega
      exact Or.inr ⟨
        ((nonclock_freezes_right s t hs ht (hR _ hrole)).mp ⟨hlt, h.2⟩).2,
        ⟨hrole, hlt⟩⟩
  · rintro (h | h)
    · refine ⟨by simpa only [hr] using h.1, ?_⟩
      exact h.2.trans ((le_max_right _ _).trans
        ((phaseEpidemicUpdate_right_phase_ge_max L K s t).trans
          (phaseEpidemicUpdate_phase_le_Transition_phase L K s t).2))
    · exact ⟨by simpa only [hr] using h.2.1,
        ((nonclock_freezes_right s t hs ht (hR _ h.2.1)).mpr ⟨h.2.2, h.1⟩).2⟩

theorem trackedFrozenCount_update (R : Role → Prop)
    (hR : ∀ r, R r → r ≠ .clock) (f : Fin n → AgentState L K)
    (hw : ∀ i, Window (f i)) (i j : Fin n) (hij : i ≠ j) :
    trackedFrozenCount R (updateLabels f i j) =
      trackedFrozenCount R f + bitNat (trackedArrival R f i j) := by
  have h := pool_updateLabels_balance f (TrackedFrozen R) i j hij
  change trackedFrozenCount R (updateLabels f i j) +
      bitNat (TrackedFrozen R (f i)) + bitNat (TrackedFrozen R (f j)) =
    trackedFrozenCount R f + bitNat (TrackedFrozen R (Transition L K (f i) (f j)).1) +
      bitNat (TrackedFrozen R (Transition L K (f i) (f j)).2) at h
  have hl := bitNat_add_of_iff _ _ _
    (trackedFrozen_left_iff R hR (f i) (f j) (hw i) (hw j))
    (fun h h' => Nat.not_lt_of_ge h.2 h'.1.2)
  have hr := bitNat_add_of_iff _ _ _
    (trackedFrozen_right_iff R hR (f i) (f j) (hw i) (hw j))
    (fun h h' => Nat.not_lt_of_ge h.2 h'.2.2)
  rw [hl, hr] at h
  have hc := bitNat_contact f i j (TrackedFresh R) Infected
    (fun _ h h' => Nat.not_lt_of_ge h' h.2)
  change trackedFrozenCount R (updateLabels f i j) =
    trackedFrozenCount R f + bitNat (contact (TrackedFresh R) Infected f i j)
  omega

theorem tracked_partition (R : Role → Prop) (f : Fin n → AgentState L K) :
    (pool f (TrackedFresh R)).card + trackedFrozenCount R f = trackedCount R f := by
  simpa only [TrackedFresh, TrackedFrozen, trackedCount, trackedFrozenCount, not_lt] using
    pool_partition f (fun a => R a.role) (fun a => a.phase.val < 4)

theorem trackedArrival_card (R : Role → Prop) (f : Fin n → AgentState L K) :
    (goodPairs (trackedArrival R) f).card =
      2 * (trackedCount R f - trackedFrozenCount R f) * (pool f Infected).card := by
  change (goodPairs (contact (TrackedFresh R) Infected) f).card = _
  rw [contact_card f (TrackedFresh R) Infected
    (fun _ h h' => Nat.not_lt_of_ge h' h.2)]
  have he : (pool f (TrackedFresh R)).card =
      trackedCount R f - trackedFrozenCount R f := by
    have h := tracked_partition R f
    omega
  rw [he]

def mainOrReserve (r : Role) : Prop := r = .main ∨ r = .reserve
def reserveRole (r : Role) : Prop := r = .reserve
theorem mainOrReserve_ne_clock (r : Role) (h : mainOrReserve r) : r ≠ .clock := by
  rcases h with h | h <;> subst r <;> decide
theorem reserveRole_ne_clock (r : Role) (h : reserveRole r) : r ≠ .clock := by
  unfold reserveRole at h
  subst r
  decide

abbrev nonclockCount (f : Fin n → AgentState L K) := trackedCount mainOrReserve f
abbrev nonclockFrozenCount (f : Fin n → AgentState L K) :=
  trackedFrozenCount mainOrReserve f
abbrev reserveCount (f : Fin n → AgentState L K) := trackedCount reserveRole f
abbrev reserveFrozenCount (f : Fin n → AgentState L K) := trackedFrozenCount reserveRole f
abbrev nonclockArrival (f : Fin n → AgentState L K) (i j : Fin n) :=
  trackedArrival mainOrReserve f i j
abbrev reserveArrival (f : Fin n → AgentState L K) (i j : Fin n) :=
  trackedArrival reserveRole f i j

theorem nonclockCount_eq (f : Fin n → AgentState L K) :
    nonclockCount f = mainCount f + reserveCount f := by
  classical
  change (pool f (fun a => mainOrReserve a.role)).card =
    (pool f Main).card + (pool f (fun a => reserveRole a.role)).card
  have hu : pool f (fun a => mainOrReserve a.role) =
      pool f Main ∪ pool f (fun a => reserveRole a.role) := by
    ext i
    simp only [mem_pool, Finset.mem_union, mainOrReserve, Main, reserveRole]
  rw [hu, Finset.card_union_of_disjoint]
  apply pool_disjoint
  intro a hm hr
  have he : (Role.main : Role) = Role.reserve := hm.symm.trans hr
  cases he

theorem nonclockFrozenCount_eq (f : Fin n → AgentState L K) :
    nonclockFrozenCount f = frozenCount f + reserveFrozenCount f := by
  classical
  change (pool f (TrackedFrozen mainOrReserve)).card =
    (pool f FrozenMain).card + (pool f (TrackedFrozen reserveRole)).card
  have hu : pool f (TrackedFrozen mainOrReserve) =
      pool f FrozenMain ∪ pool f (TrackedFrozen reserveRole) := by
    ext i
    simp only [mem_pool, Finset.mem_union, TrackedFrozen, FrozenMain, Main,
      mainOrReserve, reserveRole]
    tauto
  rw [hu, Finset.card_union_of_disjoint]
  apply pool_disjoint
  intro a hm hr
  have he : (Role.main : Role) = Role.reserve := hm.1.symm.trans hr.1
  cases he

theorem acceptedCount_le_reserveFrozenCount (f : Fin n → AgentState L K) :
    acceptedCount f ≤ reserveFrozenCount f := by
  apply pool_mono f AcceptedReserve (TrackedFrozen reserveRole)
  intro a h
  exact ⟨h.1, by have hp := h.2.1; omega⟩

theorem reserveArrival_implies (f : Fin n → AgentState L K) (i j : Fin n) :
    reserveArrival f i j → nonclockArrival f i j := by
  unfold reserveArrival nonclockArrival trackedArrival contact TrackedFresh
  intro h
  rcases h with h | h
  · exact Or.inl ⟨⟨Or.inr h.1.1, h.1.2⟩, h.2⟩
  · exact Or.inr ⟨h.1, ⟨Or.inr h.2.1, h.2.2⟩⟩

def reserveArrivalRatio (f : Fin n → AgentState L K) : ℝ :=
  ((reserveCount f - reserveFrozenCount f : ℕ) : ℝ) /
    ((nonclockCount f - nonclockFrozenCount f : ℕ) : ℝ)

theorem reserve_arrival_fraction (f : Fin n → AgentState L K) (hn : 2 ≤ n) :
    pairFraction f reserveArrival ≤
      reserveArrivalRatio f * pairFraction f nonclockArrival := by
  have he (R : Role → Prop) : (pool f (TrackedFresh R)).card =
      trackedCount R f - trackedFrozenCount R f := by
    have h := tracked_partition R f
    omega
  have hbu : reserveCount f - reserveFrozenCount f ≤
      nonclockCount f - nonclockFrozenCount f := by
    rw [← he reserveRole, ← he mainOrReserve]
    exact pool_mono f _ _ (fun _ h => ⟨Or.inr h.1, h.2⟩)
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  change pairFraction f (trackedArrival reserveRole) ≤
    reserveArrivalRatio f * pairFraction f (trackedArrival mainOrReserve)
  unfold pairFraction
  rw [trackedArrival_card, trackedArrival_card]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  exact common_hazard_ratio
    (nonclockCount f - nonclockFrozenCount f) (reserveCount f - reserveFrozenCount f)
    (reserveCount f - reserveFrozenCount f) (pool f Infected).card
    ((n : ℝ) * ((n : ℝ) - 1)) hden hbu le_rfl

theorem allThree_tracked_zero (R : Role → Prop) (f : Fin n → AgentState L K)
    (h : ∀ i, (f i).phase.val = 3) : trackedFrozenCount R f = 0 := by
  classical
  simp [trackedFrozenCount, pool, TrackedFrozen, h]

theorem allThree_role_counts_zero (f : Fin n → AgentState L K)
    (h : ∀ i, (f i).phase.val = 3) :
    nonclockFrozenCount f = 0 ∧ reserveFrozenCount f = 0 :=
  ⟨allThree_tracked_zero _ f h, allThree_tracked_zero _ f h⟩

theorem allThree_update_role_counts_zero (f : Fin n → AgentState L K)
    (h : ∀ i, (f i).phase.val = 3) (i j : Fin n) (hij : i ≠ j) :
    nonclockFrozenCount (updateLabels f i j) = 0 ∧
      reserveFrozenCount (updateLabels f i j) = 0 := by
  have hw : ∀ i, Window (f i) := by intro i; constructor <;> simp [h i]
  have hz (R : Role → Prop) (hR : ∀ r, R r → r ≠ .clock) :
      trackedFrozenCount R (updateLabels f i j) = 0 := by
    rw [trackedFrozenCount_update R hR f hw i j hij, allThree_tracked_zero R f h]
    simp [trackedArrival, contact, Infected, h, bitNat]
  exact ⟨hz mainOrReserve mainOrReserve_ne_clock, hz reserveRole reserveRole_ne_clock⟩

/-- A no-draw step contributes zero; a selected pair uses the actual update
receipt. This statement is pointwise for every recorded next draw. -/
theorem count_step_of_update
    (C : (Fin n → AgentState L K) → ℕ)
    (A : (Fin n → AgentState L K) → Fin n → Fin n → Prop)
    (f : Fin n → AgentState L K)
    (h : ∀ i j, i ≠ j → C (updateLabels f i j) = C f + bitNat (A f i j))
    (d : Draw L K) :
    C (stepLabels f d) =
      C f + bitNat (∃ i j, selectLabels f d = some (i, j) ∧ A f i j) := by
  classical
  cases hs : selectLabels f d with
  | none => simp [stepLabels, hs, bitNat]
  | some z =>
      rcases z with ⟨i, j⟩
      simpa [stepLabels, hs] using h i j (selectLabels_distinct f d i j hs)

theorem frozenCount_step (f : Fin n → AgentState L K)
    (hw : ∀ i, Window (f i)) (d : Draw L K) :
    frozenCount (stepLabels f d) = frozenCount f +
      bitNat (∃ i j, selectLabels f d = some (i, j) ∧ freezePair (fun _ => True) f i j) :=
  count_step_of_update _ _ f (frozenCount_update f hw) d

theorem frozenBadCount_step (C : Bias L → Prop) (f : Fin n → AgentState L K)
    (hw : ∀ i, Window (f i)) (d : Draw L K) :
    frozenBadCount C (stepLabels f d) = frozenBadCount C f +
      bitNat (∃ i j, selectLabels f d = some (i, j) ∧ freezePair (fun b => ¬ C b) f i j) :=
  count_step_of_update _ _ f (frozenBadCount_update C f hw) d

theorem trackedFrozenCount_step (R : Role → Prop) (hR : ∀ r, R r → r ≠ .clock)
    (f : Fin n → AgentState L K) (hw : ∀ i, Window (f i)) (d : Draw L K) :
    trackedFrozenCount R (stepLabels f d) = trackedFrozenCount R f +
      bitNat (∃ i j, selectLabels f d = some (i, j) ∧ trackedArrival R f i j) :=
  count_step_of_update _ _ f (trackedFrozenCount_update R hR f hw) d

theorem allThree_step_role_counts_zero (f : Fin n → AgentState L K)
    (h : ∀ i, (f i).phase.val = 3) (d : Draw L K) :
    nonclockFrozenCount (stepLabels f d) = 0 ∧
      reserveFrozenCount (stepLabels f d) = 0 := by
  cases hs : selectLabels f d with
  | none => simpa only [stepLabels, hs] using allThree_role_counts_zero f h
  | some z =>
      rcases z with ⟨i, j⟩
      simpa only [stepLabels, hs] using
        allThree_update_role_counts_zero f h i j (selectLabels_distinct f d i j hs)

theorem allThree_step_counts_zero (f : Fin n → AgentState L K)
    (h : ∀ i, (f i).phase.val = 3) (d : Draw L K) :
    frozenCount (stepLabels f d) = 0 ∧ acceptedCount (stepLabels f d) = 0 := by
  obtain ⟨hn, hr⟩ := allThree_step_role_counts_zero f h d
  have he := nonclockFrozenCount_eq (stepLabels f d)
  have ha := acceptedCount_le_reserveFrozenCount (stepLabels f d)
  constructor <;> omega

end Ripple.PopulationProtocol.ExactMajority.LateF6Hazards
end
