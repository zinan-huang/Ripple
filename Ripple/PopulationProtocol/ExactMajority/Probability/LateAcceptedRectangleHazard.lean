-- Ripple/PopulationProtocol/ExactMajority/Probability/LateAcceptedRectangleHazard.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingClassGates
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6OriginalLaw
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingCounterTail

/-!
# Accepted-sample hazard from both real rectangles

The accepted pair set is the disjoint union

* ready Phase-5 Reserve × eligible Main, and
* dormant Reserve × frozen eligible Main,

with both orientations included by `contact`.  A live global class floor and
the frozen-pool floor imply the same bad-reward fraction on each
rectangle, hence on their weighted union.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateAcceptedRectangleHazard

open TimeTheorem PairLog PairLogAuxiliary
open LateF6Acceptance LateF6Hazards LateSamplingClassGates
open LateSamplingCounterTail

variable {L K m : ℕ}

def classEligible (C : Bias L → Prop) (a : AgentState L K) : Prop :=
  Eligible a ∧ C a.bias

def badEligible (C : Bias L → Prop) (a : AgentState L K) : Prop :=
  Eligible a ∧ ¬ C a.bias

def frozenClassEligible (C : Bias L → Prop) (a : AgentState L K) : Prop :=
  FrozenEligible a ∧ C a.bias

def badFrozenEligible (C : Bias L → Prop) (a : AgentState L K) : Prop :=
  FrozenEligible a ∧ ¬ C a.bias

/-- The two actual accepted rectangles, with both orientations. -/
def acceptedRectangle
    (f : Fin m → AgentState L K) (i j : Fin m) : Prop :=
  contact ReadyReserve Eligible f i j ∨
    contact DormantReserve FrozenEligible f i j

def badAcceptedRectangle (C : Bias L → Prop)
    (f : Fin m → AgentState L K) (i j : Fin m) : Prop :=
  contact ReadyReserve (badEligible C) f i j ∨
    contact DormantReserve (badFrozenEligible C) f i j

def actualPairAccepted
    (f : Fin m → AgentState L K) (i j : Fin m) : Prop :=
  Accepted (f i) (Transition L K (f i) (f j)).1 ∨
    Accepted (f j) (Transition L K (f i) (f j)).2

/-- The two one-sided acceptance equivalences combine to exactly the two
unoriented contact rectangles used by the probability calculation. -/
theorem acceptedRectangle_iff_actual
    (f : Fin m → AgentState L K)
    (hw : ∀ i, Window (f i))
    (hcanonical : ∀ i, Eligible (f i) → 4 ≤ (f i).phase.val →
      (f i).phase.val = 5)
    (i j : Fin m) :
    actualPairAccepted f i j ↔ acceptedRectangle f i j := by
  rw [actualPairAccepted,
    transition_accept_rectangles_left (f i) (f j) (hw i) (hw j)
      (hcanonical j),
    transition_accept_rectangles_right (f i) (f j) (hw i) (hw j)
      (hcanonical i)]
  unfold acceptedRectangle contact
  tauto

private theorem accepted_contacts_disjoint
    (f : Fin m → AgentState L K) :
    Disjoint
      (goodPairs (contact ReadyReserve Eligible) f)
      (goodPairs (contact DormantReserve FrozenEligible) f) := by
  apply Finset.disjoint_left.mpr
  classical
  intro ij hready hdormant
  simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hready hdormant
  have hr := hready.2
  have hd := hdormant.2
  rcases hr with hr | hr <;> rcases hd with hd | hd <;>
    simp_all [ReadyReserve, DormantReserve, FrozenEligible, Eligible] <;>
    omega

private theorem bad_contacts_disjoint
    (C : Bias L → Prop) (f : Fin m → AgentState L K) :
    Disjoint
      (goodPairs (contact ReadyReserve (badEligible C)) f)
      (goodPairs (contact DormantReserve (badFrozenEligible C)) f) := by
  apply Finset.disjoint_left.mpr
  classical
  intro ij hready hdormant
  simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hready hdormant
  have hr := hready.2
  have hd := hdormant.2
  rcases hr with hr | hr <;> rcases hd with hd | hd <;>
    simp_all [ReadyReserve, DormantReserve, badEligible,
      badFrozenEligible, FrozenEligible, Eligible] <;>
    omega

theorem acceptedRectangle_card
    (f : Fin m → AgentState L K) :
    (goodPairs acceptedRectangle f).card =
      2 * (pool f ReadyReserve).card * (pool f Eligible).card +
        2 * (pool f DormantReserve).card *
          (pool f FrozenEligible).card := by
  have hu : goodPairs acceptedRectangle f =
      goodPairs (contact ReadyReserve Eligible) f ∪
        goodPairs (contact DormantReserve FrozenEligible) f := by
    ext ij
    simp [goodPairs, acceptedRectangle, and_or_left]
  rw [hu, Finset.card_union_of_disjoint (accepted_contacts_disjoint f),
    contact_card f ReadyReserve Eligible,
    contact_card f DormantReserve FrozenEligible]
  all_goals
    intro a h1 h2
    simp_all [ReadyReserve, DormantReserve, FrozenEligible, Eligible]

theorem badAcceptedRectangle_card
    (C : Bias L → Prop) (f : Fin m → AgentState L K) :
    (goodPairs (badAcceptedRectangle C) f).card =
      2 * (pool f ReadyReserve).card * (pool f (badEligible C)).card +
        2 * (pool f DormantReserve).card *
          (pool f (badFrozenEligible C)).card := by
  have hu : goodPairs (badAcceptedRectangle C) f =
      goodPairs (contact ReadyReserve (badEligible C)) f ∪
        goodPairs (contact DormantReserve (badFrozenEligible C)) f := by
    ext ij
    simp [goodPairs, badAcceptedRectangle, and_or_left]
  rw [hu, Finset.card_union_of_disjoint (bad_contacts_disjoint C f),
    contact_card f ReadyReserve (badEligible C),
    contact_card f DormantReserve (badFrozenEligible C)]
  all_goals
    intro a h1 h2
    simp_all [ReadyReserve, DormantReserve, badEligible, badFrozenEligible,
      FrozenEligible, Eligible]

/-- Pure algebra behind the weighted union of the two rectangles. -/
theorem two_rectangle_bad_fraction
    {r d e ef c cf b bf k M A γ : ℝ}
    (hM : 0 < M) (hA : 0 ≤ A)
    (hr : 0 ≤ r) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hef : 0 ≤ ef) (hk : 0 ≤ k)
    (hγ : 0 ≤ γ) (hγA : γ ≤ A / M)
    (heM : e ≤ M) (hefk : ef ≤ k)
    (hactive : c + b = e) (hglobal : A ≤ c)
    (hfrozen : cf + bf = ef)
    (hfloor : (A / M - γ) * k ≤ cf) :
    r * b + d * bf ≤
      (1 - A / M + γ) * (r * e + d * ef) := by
  have hu : 0 ≤ A / M := div_nonneg hA hM.le
  have huE : (A / M) * e ≤ A := by
    calc
      (A / M) * e ≤ (A / M) * M :=
        mul_le_mul_of_nonneg_left heM hu
      _ = A := by field_simp [ne_of_gt hM]
  have hactiveBad : b ≤ (1 - A / M + γ) * e := by
    have hbase : b ≤ (1 - A / M) * e := by
      nlinarith [hactive, hglobal, huE]
    have hslack : (1 - A / M) * e ≤
        (1 - A / M + γ) * e := by
      nlinarith
    exact hbase.trans hslack
  have hclassNonneg : 0 ≤ A / M - γ := sub_nonneg.mpr hγA
  have hclassEf : (A / M - γ) * ef ≤ cf := by
    exact (mul_le_mul_of_nonneg_left hefk hclassNonneg).trans hfloor
  have hfrozenBad : bf ≤ (1 - A / M + γ) * ef := by
    nlinarith [hfrozen, hclassEf]
  calc
    r * b + d * bf ≤
        r * ((1 - A / M + γ) * e) +
          d * ((1 - A / M + γ) * ef) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hactiveBad hr)
        (mul_le_mul_of_nonneg_left hfrozenBad hd)
    _ = (1 - A / M + γ) * (r * e + d * ef) := by ring

private theorem classEligible_partition
    (C : Bias L → Prop) (f : Fin m → AgentState L K) :
    (pool f (classEligible C)).card +
        (pool f (badEligible C)).card =
      (pool f Eligible).card := by
  simpa [classEligible, badEligible] using
    pool_partition f Eligible (fun a => C a.bias)

private theorem frozenClassEligible_partition
    (C : Bias L → Prop) (f : Fin m → AgentState L K) :
    (pool f (frozenClassEligible C)).card +
        (pool f (badFrozenEligible C)).card =
      (pool f FrozenEligible).card := by
  simpa [frozenClassEligible, badFrozenEligible] using
    pool_partition f FrozenEligible (fun a => C a.bias)

/-- Cardinal version, with the live global and frozen class floors exposed as
precisely the gates later used by the stopped trial. -/
theorem accepted_bad_card_le_of_floors
    (C : Bias L → Prop) (f : Fin m → AgentState L K)
    (M A : ℕ) (γ : ℝ)
    (hM : 0 < M) (hA : A ≤ M)
    (hγ : 0 ≤ γ) (hγA : γ ≤ (A : ℝ) / M)
    (heligible : (pool f Eligible).card ≤ M)
    (hfrozenEligible :
      (pool f FrozenEligible).card ≤ frozenCount f)
    (hglobal : A ≤ (pool f (classEligible C)).card)
    (hfloor : ((A : ℝ) / M - γ) * frozenCount f ≤
      (pool f (frozenClassEligible C)).card) :
    ((goodPairs (badAcceptedRectangle C) f).card : ℝ) ≤
      (1 - (A : ℝ) / M + γ) *
        (goodPairs acceptedRectangle f).card := by
  have hpart := classEligible_partition C f
  have hfpart := frozenClassEligible_partition C f
  have halgebra := two_rectangle_bad_fraction
    (r := ((pool f ReadyReserve).card : ℝ))
    (d := ((pool f DormantReserve).card : ℝ))
    (e := ((pool f Eligible).card : ℝ))
    (ef := ((pool f FrozenEligible).card : ℝ))
    (c := ((pool f (classEligible C)).card : ℝ))
    (cf := ((pool f (frozenClassEligible C)).card : ℝ))
    (b := ((pool f (badEligible C)).card : ℝ))
    (bf := ((pool f (badFrozenEligible C)).card : ℝ))
    (k := (frozenCount f : ℝ))
    (M := (M : ℝ)) (A := (A : ℝ)) (γ := γ)
    (by exact_mod_cast hM) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hγ hγA
    (by exact_mod_cast heligible)
    (by exact_mod_cast hfrozenEligible)
    (by exact_mod_cast hpart)
    (by exact_mod_cast hglobal)
    (by exact_mod_cast hfpart) hfloor
  rw [acceptedRectangle_card, badAcceptedRectangle_card]
  push_cast
  nlinarith only [halgebra]

/-- Convert the global/frozen gates into the preceding cardinal gates. -/
theorem accepted_bad_pairMass_le
    (init : Cfg L K) (hn : 2 ≤ init.card)
    (C : Bias L → Prop)
    (hclassEligible : ∀ a : AgentState L K, MainClass C a → Eligible a)
    (hfrozenClassEligible : ∀ a : AgentState L K,
      FrozenMain a ∧ C a.bias → FrozenEligible a)
    (f : Fin init.card → AgentState L K)
    (M A : ℕ) (γ : ℝ)
    (hM : 0 < M) (hA : A ≤ M)
    (hγ : 0 ≤ γ) (hγA : γ ≤ (A : ℝ) / M)
    (hmains : mainCount f = M)
    (hglobal : A ≤ classCount C f)
    (hfloor : FrozenFloor C A M γ f) :
    pairMass init (badAcceptedRectangle C) f ≤
      (1 - (A : ℝ) / M + γ) *
        pairMass init acceptedRectangle f := by
  have heligible : (pool f Eligible).card ≤ M := by
    exact (pool_mono f Eligible Main (fun _ h => h.1)).trans_eq hmains
  have hfrozenEligible :
      (pool f FrozenEligible).card ≤ frozenCount f := by
    exact pool_mono f FrozenEligible FrozenMain
      (fun _ h => ⟨h.1.1, h.2⟩)
  have hglobal' : A ≤ (pool f (classEligible C)).card := by
    have heq : (pool f (classEligible C)).card = classCount C f := by
      apply congrArg Finset.card
      ext i
      simp only [mem_pool, classEligible]
      constructor
      · intro h
        exact ⟨h.1.1, h.2⟩
      · intro h
        exact ⟨hclassEligible _ h, h.2⟩
    rw [heq]
    exact hglobal
  have hfloor' : ((A : ℝ) / M - γ) * frozenCount f ≤
      (pool f (frozenClassEligible C)).card := by
    have heq : (pool f (frozenClassEligible C)).card =
        frozenClassCount C f := by
      apply congrArg Finset.card
      ext i
      simp only [mem_pool, frozenClassEligible, frozenClassCount]
      constructor
      · intro h
        exact ⟨⟨h.1.1.1, h.1.2⟩, h.2⟩
      · intro h
        exact ⟨hfrozenClassEligible _ h, h.2⟩
    rw [heq]
    exact hfloor
  have hcard := accepted_bad_card_le_of_floors C f M A γ
    hM hA hγ hγA heligible hfrozenEligible hglobal' hfloor'
  unfold pairMass
  have hden : 0 < (init.card : ℝ) * ((init.card : ℝ) - 1) := by
    have hcardTwo : (2 : ℝ) ≤ init.card := by exact_mod_cast hn
    exact mul_pos (by linarith) (by linarith)
  rw [← mul_div_assoc]
  exact (div_le_div_iff_of_pos_right hden).2 hcard

/-- Biases whose stored exponent belongs to `J`; zero and sentinel-index
biases are deliberately excluded. -/
def indexClass (J : Finset (Fin (L + 1))) : Bias L → Prop
  | .zero => False
  | .dyadic _ j => j ∈ J ∧ j.val < L

theorem indexClass_eligible
    (J : Finset (Fin (L + 1))) (a : AgentState L K)
    (h : MainClass (indexClass J) a) : Eligible a := by
  rcases h with ⟨hmain, hclass⟩
  cases hb : a.bias with
  | zero => simp [indexClass, hb] at hclass
  | dyadic σ j =>
      have hcl : j ∈ J ∧ j.val < L := by simpa [indexClass, hb] using hclass
      exact ⟨hmain, σ, j, hb, hcl.2⟩

theorem accepted_left_stores_indexClass
    (J : Finset (Fin (L + 1)))
    (r m : AgentState L K) (hr : Window r) (hm : Window m)
    (hacc : Accepted r (Transition L K r m).1) :
    indexClass J m.bias ↔ (Transition L K r m).1.hour ∈ J := by
  have he := (transition_accept_left r m hr hm).mp hacc
  have heligible : Eligible m := by
    rcases he.2 with h | h
    · exact h.2.2
    · exact h.2.2
  rcases heligible with ⟨_, σ, j, hb, hj⟩
  rw [transition_accepted_index_left r m hr hm hacc, hb]
  simp [indexClass, exponentOf, hj]

theorem accepted_right_stores_indexClass
    (J : Finset (Fin (L + 1)))
    (m r : AgentState L K) (hm : Window m) (hr : Window r)
    (hacc : Accepted r (Transition L K m r).2) :
    indexClass J m.bias ↔ (Transition L K m r).2.hour ∈ J := by
  have he := (transition_accept_right m r hm hr).mp hacc
  have heligible : Eligible m := by
    rcases he.2 with h | h
    · exact h.2.2
    · exact h.2.2
  rcases heligible with ⟨_, σ, j, hb, hj⟩
  rw [transition_accepted_index_right m r hm hr hacc, hb]
  simp [indexClass, exponentOf, hj]

/-- Consumer form for a stored-index class.  The exact sample-write lemmas
above identify this bias reward with membership of the newly stored index. -/
theorem stored_index_bad_pairMass_le
    (init : Cfg L K) (hn : 2 ≤ init.card)
    (J : Finset (Fin (L + 1)))
    (f : Fin init.card → AgentState L K)
    (M A : ℕ) (γ : ℝ)
    (hM : 0 < M) (hA : A ≤ M)
    (hγ : 0 ≤ γ) (hγA : γ ≤ (A : ℝ) / M)
    (hmains : mainCount f = M)
    (hglobal : A ≤ classCount (indexClass J) f)
    (hfloor : FrozenFloor (indexClass J) A M γ f) :
    pairMass init (badAcceptedRectangle (indexClass J)) f ≤
      (1 - (A : ℝ) / M + γ) *
        pairMass init acceptedRectangle f := by
  apply accepted_bad_pairMass_le init hn (indexClass J)
    (fun a h => indexClass_eligible J a h)
    (fun a h => ⟨indexClass_eligible J a ⟨h.1.1, h.2⟩, h.1.2⟩)
    f M A γ hM hA hγ hγA hmains hglobal hfloor

end Ripple.PopulationProtocol.ExactMajority.LateAcceptedRectangleHazard

end
