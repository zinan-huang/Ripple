/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPrefix
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Identity witnesses for physical infection activations

The physical refinement needed by the activation-order argument retains the
actual coarse infection state and only the identities that are still
inactive. Active identities are irrelevant to the reveal order: active-only
reactions continue to evolve in the coarse coordinate.

Each coarse semantic event is refined by a finite witness fibre. Activation
events carry the identity or auxiliary fair ordering of the two identities
they activate. Forgetting this dependent witness recovers the original event
scheduler exactly.
-/

namespace Tri

/-- The minimal physical state carrying the remaining inactive identities. -/
structure InfectionRevealPhysicalState (n : ℕ) where
  coarse : InfectionState n
  inactive : InfectionInactiveView n
  hinactiveCard : inactive.ids.card = coarse.1.inactive
  hinactiveX : inactive.xIds.card = coarse.1.ix
  hinactiveY : inactive.yIds.card = coarse.1.iy

/-- Forget the extra inactive-identity view. -/
def infectionRevealPhysicalForget
    {n : ℕ} (s : InfectionRevealPhysicalState n) : InfectionState n :=
  s.coarse

/-- Every full identity state supplies the smaller reveal-only refinement. -/
def InfectionIdentityState.toRevealPhysical
    {n : ℕ} (s : InfectionIdentityState n) :
    InfectionRevealPhysicalState n where
  coarse := s.coarse
  inactive := s.inactive
  hinactiveCard := s.hinactiveCard
  hinactiveX := s.hinactiveX
  hinactiveY := s.hinactiveY

abbrev InfectionInactiveXId {n : ℕ}
    (s : InfectionRevealPhysicalState n) :=
  ↥s.inactive.xIds

abbrev InfectionInactiveYId {n : ℕ}
    (s : InfectionRevealPhysicalState n) :=
  ↥s.inactive.yIds

/-- An ordered distinct pair of inactive `X` identities. -/
def InfectionInactiveXX {n : ℕ}
    (s : InfectionRevealPhysicalState n) :=
  {p : InfectionInactiveXId s × InfectionInactiveXId s // p.1 ≠ p.2}

/-- An ordered mixed pair; both auxiliary orders occur. -/
def InfectionInactiveXY {n : ℕ}
    (s : InfectionRevealPhysicalState n) :=
  (InfectionInactiveXId s × InfectionInactiveYId s) ⊕
    (InfectionInactiveYId s × InfectionInactiveXId s)

/-- An ordered distinct pair of inactive `Y` identities. -/
def InfectionInactiveYY {n : ℕ}
    (s : InfectionRevealPhysicalState n) :=
  {p : InfectionInactiveYId s × InfectionInactiveYId s // p.1 ≠ p.2}

/-- Identity data refining one coarse semantic event. -/
def InfectionRevealWitness {n : ℕ}
    (s : InfectionRevealPhysicalState n) :
    InfectionEvent → Type
  | .activeXXX => PUnit
  | .activeXXY => PUnit
  | .activeXYY => PUnit
  | .activeYYY => PUnit
  | .activateOneX => InfectionInactiveXId s
  | .activateOneY => InfectionInactiveYId s
  | .activateTwoXX => InfectionInactiveXX s
  | .activateTwoXY => InfectionInactiveXY s
  | .activateTwoYY => InfectionInactiveYY s
  | .inactiveOnly => PUnit

noncomputable instance infectionRevealWitnessDecidableEq
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent) : DecidableEq (InfectionRevealWitness s e) := by
  cases e <;>
    unfold InfectionRevealWitness InfectionInactiveXX
      InfectionInactiveXY InfectionInactiveYY <;>
    infer_instance

noncomputable instance infectionRevealWitnessFintype
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent) : Fintype (InfectionRevealWitness s e) := by
  cases e <;>
    unfold InfectionRevealWitness InfectionInactiveXX
      InfectionInactiveXY InfectionInactiveYY <;>
    infer_instance

/-- The number of ordered distinct pairs in a finite type. -/
theorem card_ordered_distinct_pair
    (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card {p : α × α // p.1 ≠ p.2} =
      2 * Nat.choose (Fintype.card α) 2 := by
  change Fintype.card {(a, b) : α × α | a ≠ b} =
    2 * Nat.choose (Fintype.card α) 2
  calc
    Fintype.card {(a, b) : α × α | a ≠ b} =
        Fintype.card (Fin 2 ↪ α) :=
      (Fintype.card_congr
        (Function.Embedding.twoEmbeddingEquiv (α := α))).symm
    _ = 2 * Nat.choose (Fintype.card α) 2 := by
      rw [Fintype.card_embedding_eq, Fintype.card_fin,
        Nat.descFactorial_eq_factorial_mul_choose,
        Nat.factorial_two]

@[simp] theorem card_infectionRevealWitness_activateOneX
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    Fintype.card
        (InfectionRevealWitness s .activateOneX) =
      s.coarse.1.ix := by
  simpa [InfectionRevealWitness, InfectionInactiveXId] using s.hinactiveX

@[simp] theorem card_infectionRevealWitness_activateOneY
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    Fintype.card
        (InfectionRevealWitness s .activateOneY) =
      s.coarse.1.iy := by
  simpa [InfectionRevealWitness, InfectionInactiveYId] using s.hinactiveY

@[simp] theorem card_infectionRevealWitness_activateTwoXX
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    Fintype.card
        (InfectionRevealWitness s .activateTwoXX) =
      2 * Nat.choose s.coarse.1.ix 2 := by
  rw [show Fintype.card
      (InfectionRevealWitness s .activateTwoXX) =
        2 * Nat.choose
          (Fintype.card (InfectionInactiveXId s)) 2 by
    exact card_ordered_distinct_pair _]
  simp [InfectionInactiveXId, s.hinactiveX]

@[simp] theorem card_infectionRevealWitness_activateTwoXY
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    Fintype.card
        (InfectionRevealWitness s .activateTwoXY) =
      2 * s.coarse.1.ix * s.coarse.1.iy := by
  change Fintype.card
      ((InfectionInactiveXId s × InfectionInactiveYId s) ⊕
        (InfectionInactiveYId s × InfectionInactiveXId s)) =
    2 * s.coarse.1.ix * s.coarse.1.iy
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod]
  simp only [Fintype.card_coe, s.hinactiveX, s.hinactiveY]
  ring

@[simp] theorem card_infectionRevealWitness_activateTwoYY
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    Fintype.card
        (InfectionRevealWitness s .activateTwoYY) =
      2 * Nat.choose s.coarse.1.iy 2 := by
  rw [show Fintype.card
      (InfectionRevealWitness s .activateTwoYY) =
        2 * Nat.choose
          (Fintype.card (InfectionInactiveYId s)) 2 by
    exact card_ordered_distinct_pair _]
  simp [InfectionInactiveYId, s.hinactiveY]

/-- A positive coarse event weight guarantees an identity witness in its
matching fibre. -/
theorem infectionRevealWitness_nonempty_of_weight_ne_zero
    {n : ℕ} (s : InfectionRevealPhysicalState n) (e : InfectionEvent)
    (he : InfectionEvent.weight s.coarse.1 e ≠ 0) :
    Nonempty (InfectionRevealWitness s e) := by
  cases e with
  | activeXXX | activeXXY | activeXYY | activeYYY | inactiveOnly =>
      exact ⟨PUnit.unit⟩
  | activateOneX =>
      have hix : s.coarse.1.ix ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp (by
          simpa only [InfectionEvent.weight] using he)).2
      have hcard : 0 < s.inactive.xIds.card := by
        rw [s.hinactiveX]
        omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard
      exact ⟨⟨i, hi⟩⟩
  | activateOneY =>
      have hiy : s.coarse.1.iy ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp (by
          simpa only [InfectionEvent.weight] using he)).2
      have hcard : 0 < s.inactive.yIds.card := by
        rw [s.hinactiveY]
        omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard
      exact ⟨⟨i, hi⟩⟩
  | activateTwoXX =>
      have hchoose : Nat.choose s.coarse.1.ix 2 ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp (by
          simpa only [InfectionEvent.weight] using he)).2
      have hcard : 1 < s.inactive.xIds.card := by
        rw [s.hinactiveX]
        exact Nat.lt_of_succ_le (Nat.choose_ne_zero_iff.mp hchoose)
      obtain ⟨i, j, hi, hj, hij⟩ :=
        Finset.one_lt_card_iff.mp hcard
      exact ⟨⟨(⟨i, hi⟩, ⟨j, hj⟩), by
        intro h
        apply hij
        exact congrArg Subtype.val h⟩⟩
  | activateTwoXY =>
      have hmul :
          s.coarse.1.active * s.coarse.1.ix *
              s.coarse.1.iy ≠ 0 := by
        simpa only [InfectionEvent.weight] using he
      have hix : s.coarse.1.ix ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp
          (Nat.mul_ne_zero_iff.mp hmul).1).2
      have hiy : s.coarse.1.iy ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp hmul).2
      have hxcard : 0 < s.inactive.xIds.card := by
        rw [s.hinactiveX]
        omega
      have hycard : 0 < s.inactive.yIds.card := by
        rw [s.hinactiveY]
        omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hxcard
      obtain ⟨j, hj⟩ := Finset.card_pos.mp hycard
      exact ⟨Sum.inl (⟨i, hi⟩, ⟨j, hj⟩)⟩
  | activateTwoYY =>
      have hchoose : Nat.choose s.coarse.1.iy 2 ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp (by
          simpa only [InfectionEvent.weight] using he)).2
      have hcard : 1 < s.inactive.yIds.card := by
        rw [s.hinactiveY]
        exact Nat.lt_of_succ_le (Nat.choose_ne_zero_iff.mp hchoose)
      obtain ⟨i, j, hi, hj, hij⟩ :=
        Finset.one_lt_card_iff.mp hcard
      exact ⟨⟨(⟨i, hi⟩, ⟨j, hj⟩), by
        intro h
        apply hij
        exact congrArg Subtype.val h⟩⟩

/-- Conditional witness law. A zero-weight event uses an unreachable `none`;
a positive-weight event is uniform on its finite witness fibre. -/
noncomputable def infectionRevealWitnessPMF
    {n : ℕ} (s : InfectionRevealPhysicalState n) (e : InfectionEvent) :
    PMF (Option (InfectionRevealWitness s e)) :=
  if he : InfectionEvent.weight s.coarse.1 e = 0 then
    PMF.pure none
  else
    (@PMF.uniformOfFintype
      (InfectionRevealWitness s e)
      inferInstance
      (infectionRevealWitness_nonempty_of_weight_ne_zero s e he)).map some

/-- One coarse event together with its dependent identity witness. -/
structure InfectionRevealRecord {n : ℕ}
    (s : InfectionRevealPhysicalState n) where
  event : InfectionEvent
  witness : Option (InfectionRevealWitness s event)

def infectionRevealPhysicalTotalAtLeastThree
    (n : ℕ) (h3 : 3 ≤ n) (s : InfectionRevealPhysicalState n) :
    3 ≤ s.coarse.1.total := by
  have hs := s.coarse.2
  simp only [InfectionCfg.Inv] at hs
  omega

/-- Event-first joint law of a physical semantic event and its identity
witness. -/
noncomputable def infectionRevealRecordPMF
    (n : ℕ) (h3 : 3 ≤ n) (s : InfectionRevealPhysicalState n) :
    PMF (InfectionRevealRecord s) :=
  (infectionEventPMF s.coarse.1
      (infectionRevealPhysicalTotalAtLeastThree n h3 s)).bind fun e =>
    (infectionRevealWitnessPMF s e).map fun w =>
      { event := e, witness := w }

/-- Forgetting the identity witness recovers the original coarse event
scheduler exactly. -/
theorem infectionRevealRecordPMF_map_event
    (n : ℕ) (h3 : 3 ≤ n) (s : InfectionRevealPhysicalState n) :
    (infectionRevealRecordPMF n h3 s).map InfectionRevealRecord.event =
      infectionEventPMF s.coarse.1
        (infectionRevealPhysicalTotalAtLeastThree n h3 s) := by
  unfold infectionRevealRecordPMF
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  have hcomp :
      ∀ e : InfectionEvent,
        InfectionRevealRecord.event ∘
            (fun w : Option (InfectionRevealWitness s e) =>
              ({ event := e, witness := w } :
                InfectionRevealRecord s)) =
          Function.const (Option (InfectionRevealWitness s e)) e := by
    intro e
    rfl
  simp_rw [hcomp, PMF.map_const]
  exact PMF.bind_pure _

end Tri

#print axioms Tri.infectionRevealWitness_nonempty_of_weight_ne_zero
#print axioms Tri.infectionRevealRecordPMF_map_event
#print axioms Tri.card_ordered_distinct_pair
#print axioms Tri.card_infectionRevealWitness_activateOneX
#print axioms Tri.card_infectionRevealWitness_activateOneY
#print axioms Tri.card_infectionRevealWitness_activateTwoXX
#print axioms Tri.card_infectionRevealWitness_activateTwoXY
#print axioms Tri.card_infectionRevealWitness_activateTwoYY
