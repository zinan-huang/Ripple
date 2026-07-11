/-
  Backward coverability saturation loop.

  Module 6 of 7 for Theorem 4.2 (Petri net coverability decidability).

  Uses:
  - FiniteBasis.lean: Basis, up, minBasis, memUpBool
  - Saturation.lean: basisCovers, predecessorOfPetri, canProducePetri
  - WQOUpward.lean: wellFounded_finset_upClosure (termination)
  - PetriMonotone.lean: monotonicity of Petri net firing
-/
import Ripple.sCRNUniversality.Decidability.FiniteBasis
import Ripple.sCRNUniversality.Decidability.Saturation
import Ripple.sCRNUniversality.Decidability.WQOUpward
import Ripple.sCRNUniversality.Decidability.PetriMonotone
import Mathlib.Order.WellQuasiOrder

namespace Ripple.sCRNUniversality.Decidability

open Ripple.sCRNUniversality

variable {S : Type*} [Fintype S] [DecidableEq S]

-- ══════════════════════════════════════════════════════════════════
-- Strong closure: no canProducePetri guard
-- ══════════════════════════════════════════════════════════════════

/-- Strong closure: for EVERY basis element and EVERY transition,
    the predecessor is covered by the basis.

    Unlike `isClosed` (which guards with `canProducePetri`), this
    checks all transitions unconditionally. Since Nat subtraction
    handles the case where `P.post i s > b s` by returning 0,
    `predecessorOfPetri` is always well-defined and correct. -/
def isClosedStrong (P : PetriNet S) (B : Finset (State S)) : Prop :=
  ∀ b ∈ B, ∀ i : P.I,
    basisCovers B (predecessorOfPetri P i b)

instance (P : PetriNet S) (B : Finset (State S)) :
    Decidable (isClosedStrong P B) :=
  show Decidable (∀ b ∈ B, ∀ i : P.I,
    basisCovers B (predecessorOfPetri P i b)) from inferInstance

-- ══════════════════════════════════════════════════════════════════
-- Predecessor finset for a PetriNet
-- ══════════════════════════════════════════════════════════════════

/-- All predecessors of a single basis element across all transitions. -/
def petriPredecessorsOf (P : PetriNet S) (b : State S) : Finset (State S) :=
  Finset.univ.image fun i : P.I => predecessorOfPetri P i b

/-- All predecessors of all basis elements. -/
def petriPredecessorsFinset (P : PetriNet S) (B : Basis S) : Finset (State S) :=
  B.biUnion fun b => petriPredecessorsOf P b

-- ══════════════════════════════════════════════════════════════════
-- Saturation step
-- ══════════════════════════════════════════════════════════════════

/-- One saturation step: add all predecessors of current basis elements,
    then minimize. -/
def saturateStep (P : PetriNet S) (B : Basis S) : Basis S :=
  Basis.minBasis (B ∪ petriPredecessorsFinset P B)

-- ══════════════════════════════════════════════════════════════════
-- Fuel-based saturation loop
-- ══════════════════════════════════════════════════════════════════

/-- Fuel-based saturation: iterate until strongly closed or fuel exhausted. -/
def saturateFuel (P : PetriNet S) (fuel : ℕ) (B : Basis S) : Basis S :=
  match fuel with
  | 0 => B
  | n + 1 =>
    if isClosedStrong P B then B
    else saturateFuel P n (saturateStep P B)

-- ══════════════════════════════════════════════════════════════════
-- Properties of saturateFuel
-- ══════════════════════════════════════════════════════════════════

/-- If saturateFuel returns early (before fuel runs out), the result is closed. -/
theorem saturateFuel_of_isClosedStrong {P : PetriNet S} {B : Basis S}
    (hClosed : isClosedStrong P B) (fuel : ℕ) :
    saturateFuel P (fuel + 1) B = B := by
  show (if isClosedStrong P B then B else _) = B
  simp [hClosed]

/-- saturateFuel on fuel 0 is the identity. -/
@[simp] theorem saturateFuel_zero (P : PetriNet S) (B : Basis S) :
    saturateFuel P 0 B = B := rfl

-- ══════════════════════════════════════════════════════════════════
-- Connecting predecessorOfPetri to actual Petri net semantics
-- ══════════════════════════════════════════════════════════════════

/-- predecessorOfPetri fires transition i to produce a state covering b.
    Works for ALL b and i, even when ¬canProducePetri, because Nat subtraction
    handles the case b(s) < post(s) by clamping to 0. -/
theorem predecessorOfPetri_fires_covers
    {P : PetriNet S} {i : P.I} {b : State S} :
    P.enabled i (predecessorOfPetri P i b) ∧
    ∀ s, b s ≤ P.fire i (predecessorOfPetri P i b) s := by
  constructor
  · intro s
    show P.pre i s ≤ b s - P.post i s + P.pre i s
    omega
  · intro s
    show b s ≤ (b s - P.post i s + P.pre i s) - P.pre i s + P.post i s
    omega

/-- If w covers predecessorOfPetri, then w is enabled for i and firing i
    from w produces a state covering b. -/
theorem covers_predecessorOfPetri_fires_covers
    {P : PetriNet S} {i : P.I} {b w : State S}
    (hcov : Covers w (predecessorOfPetri P i b)) :
    P.enabled i w ∧ Covers (P.fire i w) b := by
  constructor
  · exact PetriNet.enabled_of_covers predecessorOfPetri_fires_covers.1 hcov
  · intro s
    have hfire_mono := PetriNet.fire_covers_fire_of_covers (i := i) hcov
    exact le_trans (predecessorOfPetri_fires_covers.2 s) (hfire_mono s)

/-- If w' fires transition i to reach w, and w covers b, then w' covers
    predecessorOfPetri P i b. -/
theorem covers_predecessor_of_stepAt_covers
    {P : PetriNet S} {i : P.I} {b w w' : State S}
    (hStep : P.StepAt i w' w) (hcov : Covers w b) :
    Covers w' (predecessorOfPetri P i b) := by
  intro s
  -- w = fire i w', so w s = w' s - pre s + post s
  have hw : w s = w' s - P.pre i s + P.post i s := by
    rw [hStep.2]; rfl
  -- w covers b: b s ≤ w s = w' s - pre s + post s
  have hbw := hcov s
  rw [hw] at hbw
  -- predecessorOfPetri P i b s = b s - post s + pre s
  -- We need: b s - post s + pre s ≤ w' s
  show b s - P.post i s + P.pre i s ≤ w' s
  -- w' is enabled: pre s ≤ w' s
  have hpre_le := hStep.1 s
  omega

-- ══════════════════════════════════════════════════════════════════
-- Soundness: every basis element can reach the target
-- ══════════════════════════════════════════════════════════════════

/-- The core soundness invariant: if every element of B satisfies
    "any state covering it can cover the target", then this invariant
    is preserved by saturateFuel. -/
theorem coverable_of_mem_up_saturateFuel
    (P : PetriNet S) (target : State S) :
    ∀ fuel B,
      (∀ b ∈ B, ∀ w, Covers w b → P.CoverableFrom w target) →
      ∀ b ∈ saturateFuel P fuel B,
        ∀ w, Covers w b → P.CoverableFrom w target := by
  intro fuel
  induction fuel with
  | zero => intro B hB b hb w hw; exact hB b hb w hw
  | succ n ih =>
    intro B hB
    show ∀ b ∈ (if isClosedStrong P B then B
      else saturateFuel P n (saturateStep P B)),
      ∀ w, Covers w b → P.CoverableFrom w target
    split
    · -- isClosedStrong: basis unchanged
      exact fun b hb w hw => hB b hb w hw
    · -- not closed: recurse on saturateStep P B
      apply ih
      intro b hb w hw
      -- b is in minBasis (B ∪ petriPredecessorsFinset P B)
      have hbOrig : b ∈ B ∪ petriPredecessorsFinset P B :=
        Basis.minBasis_subset _ hb
      rcases Finset.mem_union.mp hbOrig with hbB | hbPred
      · exact hB b hbB w hw
      · -- b came from predecessors
        simp only [petriPredecessorsFinset, Finset.mem_biUnion] at hbPred
        obtain ⟨b₀, hb₀B, hb₀pred⟩ := hbPred
        simp only [petriPredecessorsOf, Finset.mem_image] at hb₀pred
        obtain ⟨i, _, rfl⟩ := hb₀pred
        -- b = predecessorOfPetri P i b₀
        -- w covers predecessorOfPetri P i b₀
        -- So firing i from w gives a state covering b₀
        have ⟨hEnabled, hFireCovers⟩ := covers_predecessorOfPetri_fires_covers hw
        -- b₀ is coverable from fire i w
        have hCovb₀ : P.CoverableFrom (P.fire i w) target :=
          hB b₀ hb₀B (P.fire i w) hFireCovers
        -- w reaches fire i w
        exact PetriNet.CoverableFrom.of_reaches_left
          (PetriNet.reaches_of_stepAt ⟨hEnabled, rfl⟩) hCovb₀

/-- The initial basis {target} satisfies the invariant. -/
theorem coverable_of_covers_target
    {P : PetriNet S} {target : State S} {w : State S}
    (hw : Covers w target) :
    P.CoverableFrom w target :=
  PetriNet.coverable_of_initial_covers hw

-- ══════════════════════════════════════════════════════════════════
-- Completeness: strongly closed ↑B is backward-closed
-- ══════════════════════════════════════════════════════════════════

/-- In a strongly closed basis, the upward closure is backward-closed under
    every transition: if w ∈ ↑B and w' fires i to w, then w' ∈ ↑B. -/
theorem up_backward_closed_of_isClosedStrong
    {P : PetriNet S} {B : Finset (State S)}
    (hClosed : isClosedStrong P B) :
    ∀ w w' : State S, ∀ i : P.I,
      P.StepAt i w' w → w ∈ Basis.up B → w' ∈ Basis.up B := by
  intro w w' i hStep ⟨b, hb, hcov⟩
  -- w' covers predecessorOfPetri P i b
  have hw'_covers := covers_predecessor_of_stepAt_covers hStep hcov
  -- By strong closure, predecessorOfPetri P i b is covered by some a ∈ B
  have hpred_covered := hClosed b hb i
  -- basisCovers B (predecessorOfPetri P i b) means ∃ a ∈ B, stateLe a (pred...)
  rcases hpred_covered with ⟨a, ha, hale⟩
  -- a ≤ pred(i,b) ≤ w', so w' ∈ ↑B
  exact ⟨a, ha, fun s => le_trans (hale s) (hw'_covers s)⟩

-- ══════════════════════════════════════════════════════════════════
-- Monotonicity of the upward closure under saturation
-- ══════════════════════════════════════════════════════════════════

/-- The upward closure of a basis grows monotonically under saturation steps. -/
theorem saturateStep_up_mono (P : PetriNet S) (B : Basis S) :
    Basis.up B ⊆ Basis.up (saturateStep P B) := by
  intro m hm
  have : Basis.up B ⊆ Basis.up (B ∪ petriPredecessorsFinset P B) :=
    Basis.up_mono Finset.subset_union_left
  rw [saturateStep, Basis.up_minBasis]
  exact this hm

/-- The upward closure is monotone through any number of fuel steps. -/
theorem saturateFuel_up_mono (P : PetriNet S) :
    ∀ fuel B, Basis.up B ⊆ Basis.up (saturateFuel P fuel B) := by
  intro fuel
  induction fuel with
  | zero => intro B; exact le_refl _
  | succ n ih =>
    intro B
    show Basis.up B ⊆ Basis.up (if isClosedStrong P B then B
      else saturateFuel P n (saturateStep P B))
    split
    · exact le_refl _
    · exact le_trans (saturateStep_up_mono P B) (ih _)

-- ══════════════════════════════════════════════════════════════════
-- Dickson's lemma: State S is a WQO (under pointwise ≤)
-- ══════════════════════════════════════════════════════════════════

/-- The pointwise ≤ on State S = S → ℕ is a well-quasi-order when S is finite.
    This is Dickson's lemma.

    The proof uses the fact that ℕ is a WQO and that finite products of
    WQOs are WQOs (the WQO product theorem). -/
noncomputable instance stateWQO : WellQuasiOrderedLE (State S) :=
  Pi.wellQuasiOrderedLE

-- ══════════════════════════════════════════════════════════════════
-- Existence of sufficient fuel (via WQO)
-- ══════════════════════════════════════════════════════════════════

/-- There exists sufficient fuel for the saturation to reach a fixpoint.

    The proof idea: the sequence of bases B₀, B₁, ... has strictly growing
    upward closures (↑B₀ ⊊ ↑B₁ ⊊ ...) until closure is reached. By the
    WQO ascending chain stabilization theorem (wellFounded_finset_upClosure),
    this chain must terminate after finitely many steps. -/
private theorem up_strict_of_not_closed (P : PetriNet S) (B : Basis S)
    (h : ¬ isClosedStrong P B) :
    Basis.up B ⊂ Basis.up (saturateStep P B) := by
  refine ⟨saturateStep_up_mono P B, fun hle => h fun b hb i => ?_⟩
  have hmem : predecessorOfPetri P i b ∈ petriPredecessorsFinset P B :=
    Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have h_in : predecessorOfPetri P i b ∈ Basis.up (saturateStep P B) := by
    rw [saturateStep, Basis.up_minBasis]
    exact Basis.mem_up_self (Finset.mem_union_right _ hmem)
  exact hle h_in

theorem exists_fuel_saturates (P : PetriNet S) (target : State S) :
    ∃ fuel, isClosedStrong P (saturateFuel P fuel {target}) := by
  suffices h : ∀ B : Basis S, ∃ fuel, isClosedStrong P (saturateFuel P fuel B) from
    h {target}
  intro B
  apply (wellFounded_finset_upClosure (α := State S)).induction B
  intro B ih
  by_cases hClosed : isClosedStrong P B
  · exact ⟨0, by rw [saturateFuel]; exact hClosed⟩
  · have hStrict := up_strict_of_not_closed P B hClosed
    obtain ⟨fuel', hfuel'⟩ := ih (saturateStep P B) hStrict
    refine ⟨fuel' + 1, ?_⟩
    rw [saturateFuel]
    simp only [hClosed, ite_false]
    exact hfuel'

end Ripple.sCRNUniversality.Decidability
