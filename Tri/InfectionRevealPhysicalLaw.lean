/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalBatch

/-!
# Exact laws of ordered physical activation batches

A raw infection interaction activates zero, one, or two previously inactive
identities. This file pushes the event-first physical record law onto that
ordered batch and begins the exact exchangeability calculation.

The first result is label-free: every fixed remaining inactive identity has
the same one-activation mass.
-/

namespace Tri

open scoped ENNReal

/-- The ordered identities activated by one physical interaction. -/
inductive InfectionRevealBatch {n : ℕ} (v : InfectionInactiveView n)
  | none
  | one (i : InfectionInactiveId v)
  | two (p : InfectionOrderedRevealTwo v)

noncomputable instance {n : ℕ} (v : InfectionInactiveView n) :
    DecidableEq (InfectionRevealBatch v) :=
  Classical.decEq _

noncomputable instance {n : ℕ} (v : InfectionInactiveView n) :
    Fintype (InfectionRevealBatch v) := by
  classical
  let e :
      InfectionRevealBatch v ≃
        Unit ⊕ InfectionInactiveId v ⊕
          InfectionOrderedRevealTwo v :=
    { toFun := fun x =>
        match x with
        | .none => .inl Unit.unit
        | .one i => .inr (.inl i)
        | .two p => .inr (.inr p)
      invFun := fun x =>
        match x with
        | .inl _ => .none
        | .inr (.inl i) => .one i
        | .inr (.inr p) => .two p
      left_inv := by
        intro x
        cases x <;> rfl
      right_inv := by
        intro x
        rcases x with _ | (_ | _) <;> rfl }
  exact Fintype.ofEquiv _ e.symm

/-- Forget the event label but retain its ordered activation identities. -/
noncomputable def infectionRevealBatchOf
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent) :
    Option (InfectionRevealWitness s e) →
      InfectionRevealBatch s.inactive
  | none => .none
  | some w =>
      match e with
      | .activeXXX | .activeXXY | .activeXYY | .activeYYY |
          .inactiveOnly => .none
      | .activateOneX => .one (infectionInactiveXToId w)
      | .activateOneY => .one (infectionInactiveYToId w)
      | .activateTwoXX => .two (infectionInactiveXXToOrdered w)
      | .activateTwoXY => .two (infectionInactiveXYToOrdered w)
      | .activateTwoYY => .two (infectionInactiveYYToOrdered w)

/-- The batch carried by a dependent physical record. -/
noncomputable def InfectionRevealRecord.batch
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s) :
    InfectionRevealBatch s.inactive :=
  infectionRevealBatchOf s r.event r.witness

/-- Event-first law of the ordered physical activation batch. -/
noncomputable def infectionRevealBatchPMF
    (n : ℕ) (h3 : 3 ≤ n) (s : InfectionRevealPhysicalState n) :
    PMF (InfectionRevealBatch s.inactive) :=
  (infectionEventPMF s.coarse.1
      (infectionRevealPhysicalTotalAtLeastThree n h3 s)).bind fun e =>
    (infectionRevealWitnessPMF s e).map
      (infectionRevealBatchOf s e)

/-- The batch law is exactly the pushforward of the physical record law. -/
theorem infectionRevealRecordPMF_map_batch
    (n : ℕ) (h3 : 3 ≤ n) (s : InfectionRevealPhysicalState n) :
    (infectionRevealRecordPMF n h3 s).map
        InfectionRevealRecord.batch =
      infectionRevealBatchPMF n h3 s := by
  unfold infectionRevealRecordPMF infectionRevealBatchPMF
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  rfl

theorem infectionRevealWitnessPMF_some
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent)
    (he : InfectionEvent.weight s.coarse.1 e ≠ 0)
    (w : InfectionRevealWitness s e) :
    infectionRevealWitnessPMF s e (some w) =
      (Fintype.card (InfectionRevealWitness s e) : ℝ≥0∞)⁻¹ := by
  unfold infectionRevealWitnessPMF
  rw [dif_neg he, PMF.map_apply, tsum_fintype]
  simp [PMF.uniformOfFintype_apply]

theorem infectionRevealWitnessPMF_none
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent)
    (he : InfectionEvent.weight s.coarse.1 e ≠ 0) :
    infectionRevealWitnessPMF s e none = 0 := by
  unfold infectionRevealWitnessPMF
  rw [dif_neg he, PMF.map_apply, tsum_fintype]
  simp

theorem pmf_map_apply_of_injective
    {α β : Type*} (p : PMF α) (f : α → β)
    (hf : Function.Injective f) (a : α) :
    (p.map f) (f a) = p a := by
  rw [PMF.map_apply]
  rw [tsum_eq_single a]
  · simp
  · intro b hba
    have hab : f a ≠ f b := fun h => hba (hf h).symm
    simp [hab]

theorem pmf_map_apply_eq_zero_of_not_mem_range
    {α β : Type*} (p : PMF α) (f : α → β) (b : β)
    (hb : ∀ a, b ≠ f a) :
    (p.map f) b = 0 := by
  rw [PMF.map_apply]
  simp [hb]

theorem infectionInactiveXToId_injective
    {n : ℕ} {s : InfectionRevealPhysicalState n} :
    Function.Injective
      (@infectionInactiveXToId n s) := by
  intro i j hij
  apply Subtype.ext
  exact congrArg
    (fun z : InfectionInactiveId s.inactive => z.1) hij

theorem infectionInactiveYToId_injective
    {n : ℕ} {s : InfectionRevealPhysicalState n} :
    Function.Injective
      (@infectionInactiveYToId n s) := by
  intro i j hij
  apply Subtype.ext
  exact congrArg
    (fun z : InfectionInactiveId s.inactive => z.1) hij

theorem infectionRevealBatchOf_activateOneX_injective
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    Function.Injective
      (infectionRevealBatchOf s .activateOneX) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some j => simp [infectionRevealBatchOf] at hab
  | some i =>
      cases b with
      | none => simp [infectionRevealBatchOf] at hab
      | some j =>
          simp only [infectionRevealBatchOf,
            InfectionRevealBatch.one.injEq] at hab
          congr
          exact infectionInactiveXToId_injective hab

theorem infectionRevealBatchOf_activateOneY_injective
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    Function.Injective
      (infectionRevealBatchOf s .activateOneY) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some j => simp [infectionRevealBatchOf] at hab
  | some i =>
      cases b with
      | none => simp [infectionRevealBatchOf] at hab
      | some j =>
          simp only [infectionRevealBatchOf,
            InfectionRevealBatch.one.injEq] at hab
          congr
          exact infectionInactiveYToId_injective hab

def infectionInactiveIdToX
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (i : InfectionInactiveId s.inactive)
    (hi : s.inactive.initialLabel i.1 = .X) :
    InfectionInactiveXId s :=
  ⟨i.1, Finset.mem_filter.mpr ⟨i.2, hi⟩⟩

def infectionInactiveIdToY
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (i : InfectionInactiveId s.inactive)
    (hi : s.inactive.initialLabel i.1 = .Y) :
    InfectionInactiveYId s :=
  ⟨i.1, Finset.mem_filter.mpr ⟨i.2, hi⟩⟩

theorem infectionRevealBatchOneX_apply
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (he : InfectionEvent.weight s.coarse.1 .activateOneX ≠ 0)
    (i : InfectionInactiveId s.inactive)
    (hi : s.inactive.initialLabel i.1 = .X) :
    ((infectionRevealWitnessPMF s .activateOneX).map
        (infectionRevealBatchOf s .activateOneX)) (.one i) =
      (s.coarse.1.ix : ℝ≥0∞)⁻¹ := by
  let x := infectionInactiveIdToX i hi
  have hx : infectionInactiveXToId x = i := by
    apply Subtype.ext
    rfl
  calc
    ((infectionRevealWitnessPMF s .activateOneX).map
        (infectionRevealBatchOf s .activateOneX)) (.one i) =
        ((infectionRevealWitnessPMF s .activateOneX).map
          (infectionRevealBatchOf s .activateOneX))
            (infectionRevealBatchOf s .activateOneX (some x)) := by
              rw [show infectionRevealBatchOf s .activateOneX (some x) =
                .one i by simp [infectionRevealBatchOf, hx]]
    _ = infectionRevealWitnessPMF s .activateOneX (some x) :=
      pmf_map_apply_of_injective _ _
        (infectionRevealBatchOf_activateOneX_injective s) _
    _ = (s.coarse.1.ix : ℝ≥0∞)⁻¹ := by
      rw [infectionRevealWitnessPMF_some s .activateOneX he x]
      simp

theorem infectionRevealBatchOneY_apply
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (he : InfectionEvent.weight s.coarse.1 .activateOneY ≠ 0)
    (i : InfectionInactiveId s.inactive)
    (hi : s.inactive.initialLabel i.1 = .Y) :
    ((infectionRevealWitnessPMF s .activateOneY).map
        (infectionRevealBatchOf s .activateOneY)) (.one i) =
      (s.coarse.1.iy : ℝ≥0∞)⁻¹ := by
  let y := infectionInactiveIdToY i hi
  have hy : infectionInactiveYToId y = i := by
    apply Subtype.ext
    rfl
  calc
    ((infectionRevealWitnessPMF s .activateOneY).map
        (infectionRevealBatchOf s .activateOneY)) (.one i) =
        ((infectionRevealWitnessPMF s .activateOneY).map
          (infectionRevealBatchOf s .activateOneY))
            (infectionRevealBatchOf s .activateOneY (some y)) := by
              rw [show infectionRevealBatchOf s .activateOneY (some y) =
                .one i by simp [infectionRevealBatchOf, hy]]
    _ = infectionRevealWitnessPMF s .activateOneY (some y) :=
      pmf_map_apply_of_injective _ _
        (infectionRevealBatchOf_activateOneY_injective s) _
    _ = (s.coarse.1.iy : ℝ≥0∞)⁻¹ := by
      rw [infectionRevealWitnessPMF_some s .activateOneY he y]
      simp

theorem infectionRevealBatchOneY_zero_of_X
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (i : InfectionInactiveId s.inactive)
    (hi : s.inactive.initialLabel i.1 = .X) :
    ((infectionRevealWitnessPMF s .activateOneY).map
        (infectionRevealBatchOf s .activateOneY)) (.one i) = 0 := by
  apply pmf_map_apply_eq_zero_of_not_mem_range
  intro w
  cases w with
  | none => simp [infectionRevealBatchOf]
  | some y =>
      simp only [infectionRevealBatchOf, ne_eq,
        InfectionRevealBatch.one.injEq]
      intro h
      have hlabel := congrArg
        (fun j : InfectionInactiveId s.inactive =>
          s.inactive.initialLabel j.1) h
      change s.inactive.initialLabel i.1 =
        s.inactive.initialLabel (infectionInactiveYToId y).1 at hlabel
      rw [hi, infectionInactiveYToId_label] at hlabel
      contradiction

theorem infectionRevealBatchOneX_zero_of_Y
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (i : InfectionInactiveId s.inactive)
    (hi : s.inactive.initialLabel i.1 = .Y) :
    ((infectionRevealWitnessPMF s .activateOneX).map
        (infectionRevealBatchOf s .activateOneX)) (.one i) = 0 := by
  apply pmf_map_apply_eq_zero_of_not_mem_range
  intro w
  cases w with
  | none => simp [infectionRevealBatchOf]
  | some x =>
      simp only [infectionRevealBatchOf, ne_eq,
        InfectionRevealBatch.one.injEq]
      intro h
      have hlabel := congrArg
        (fun j : InfectionInactiveId s.inactive =>
          s.inactive.initialLabel j.1) h
      change s.inactive.initialLabel i.1 =
        s.inactive.initialLabel (infectionInactiveXToId x).1 at hlabel
      rw [hi, infectionInactiveXToId_label] at hlabel
      contradiction

theorem infectionRevealBatchPMF_one_reduce
    {n : ℕ} (h3 : 3 ≤ n) (s : InfectionRevealPhysicalState n)
    (i : InfectionInactiveId s.inactive) :
    infectionRevealBatchPMF n h3 s (.one i) =
      infectionEventPMF s.coarse.1
          (infectionRevealPhysicalTotalAtLeastThree n h3 s)
          .activateOneX *
        ((infectionRevealWitnessPMF s .activateOneX).map
          (infectionRevealBatchOf s .activateOneX)) (.one i) +
      infectionEventPMF s.coarse.1
          (infectionRevealPhysicalTotalAtLeastThree n h3 s)
          .activateOneY *
        ((infectionRevealWitnessPMF s .activateOneY).map
          (infectionRevealBatchOf s .activateOneY)) (.one i) := by
  unfold infectionRevealBatchPMF
  rw [PMF.bind_apply, tsum_fintype]
  rw [show (Finset.univ : Finset InfectionEvent) =
    {InfectionEvent.activeXXX, InfectionEvent.activeXXY,
      InfectionEvent.activeXYY, InfectionEvent.activeYYY,
      InfectionEvent.activateOneX, InfectionEvent.activateOneY,
      InfectionEvent.activateTwoXX, InfectionEvent.activateTwoXY,
      InfectionEvent.activateTwoYY, InfectionEvent.inactiveOnly} from rfl]
  simp [infectionRevealBatchOf, PMF.map_apply, tsum_fintype]

theorem ennreal_nat_mul_div_mul_inv_cancel
    (a b d : ℕ) (hb : b ≠ 0) :
    ((a * b : ℕ) : ℝ≥0∞) / (d : ℝ≥0∞) *
        (b : ℝ≥0∞)⁻¹ =
      (a : ℝ≥0∞) / (d : ℝ≥0∞) := by
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    (a : ℝ≥0∞) * b * (d : ℝ≥0∞)⁻¹ * (b : ℝ≥0∞)⁻¹ =
        ((a : ℝ≥0∞) * (d : ℝ≥0∞)⁻¹) *
          ((b : ℝ≥0∞) * (b : ℝ≥0∞)⁻¹) := by
            ac_rfl
    _ = (a : ℝ≥0∞) * (d : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.mul_inv_cancel]
      · simp
      · exact_mod_cast hb
      · exact ENNReal.natCast_ne_top b

/-- Every fixed inactive identity has the same one-activation mass, regardless
of its immutable label. -/
theorem infectionRevealBatchPMF_one_apply
    {n : ℕ} (h3 : 3 ≤ n) (s : InfectionRevealPhysicalState n)
    (i : InfectionInactiveId s.inactive) :
    infectionRevealBatchPMF n h3 s (.one i) =
      (Nat.choose s.coarse.1.active 2 : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) := by
  rw [infectionRevealBatchPMF_one_reduce]
  have htotal : s.coarse.1.total = n := s.coarse.2
  cases hlabel :
      s.inactive.initialLabel i.1 with
  | X =>
      have hmem : i.1 ∈ s.inactive.xIds :=
        Finset.mem_filter.mpr ⟨i.2, hlabel⟩
      have hcard : 0 < s.inactive.xIds.card :=
        Finset.card_pos.mpr ⟨i.1, hmem⟩
      have hix : s.coarse.1.ix ≠ 0 := by
        rw [← s.hinactiveX]
        exact hcard.ne'
      by_cases ha : Nat.choose s.coarse.1.active 2 = 0
      · simp [infectionEventPMF_apply, InfectionEvent.weight, ha]
      · have he :
            InfectionEvent.weight s.coarse.1 .activateOneX ≠ 0 := by
            simpa only [InfectionEvent.weight] using
              Nat.mul_ne_zero ha hix
        rw [infectionRevealBatchOneX_apply s he i hlabel,
          infectionRevealBatchOneY_zero_of_X s i hlabel,
          mul_zero, add_zero, infectionEventPMF_apply]
        simp only [InfectionEvent.weight]
        rw [htotal]
        exact ennreal_nat_mul_div_mul_inv_cancel
          (Nat.choose s.coarse.1.active 2) s.coarse.1.ix
          (Nat.choose n 3) hix
  | Y =>
      have hmem : i.1 ∈ s.inactive.yIds :=
        Finset.mem_filter.mpr ⟨i.2, hlabel⟩
      have hcard : 0 < s.inactive.yIds.card :=
        Finset.card_pos.mpr ⟨i.1, hmem⟩
      have hiy : s.coarse.1.iy ≠ 0 := by
        rw [← s.hinactiveY]
        exact hcard.ne'
      by_cases ha : Nat.choose s.coarse.1.active 2 = 0
      · simp [infectionEventPMF_apply, InfectionEvent.weight, ha]
      · have he :
            InfectionEvent.weight s.coarse.1 .activateOneY ≠ 0 := by
            simpa only [InfectionEvent.weight] using
              Nat.mul_ne_zero ha hiy
        rw [infectionRevealBatchOneX_zero_of_Y s i hlabel,
          infectionRevealBatchOneY_apply s he i hlabel,
          mul_zero, zero_add, infectionEventPMF_apply]
        simp only [InfectionEvent.weight]
        rw [htotal]
        exact ennreal_nat_mul_div_mul_inv_cancel
          (Nat.choose s.coarse.1.active 2) s.coarse.1.iy
          (Nat.choose n 3) hiy

end Tri

#print axioms Tri.infectionRevealRecordPMF_map_batch
#print axioms Tri.infectionRevealWitnessPMF_some
#print axioms Tri.infectionRevealWitnessPMF_none
#print axioms Tri.pmf_map_apply_of_injective
#print axioms Tri.pmf_map_apply_eq_zero_of_not_mem_range
#print axioms Tri.infectionInactiveXToId_injective
#print axioms Tri.infectionInactiveYToId_injective
#print axioms Tri.infectionRevealBatchOf_activateOneX_injective
#print axioms Tri.infectionRevealBatchOf_activateOneY_injective
#print axioms Tri.infectionRevealBatchOneX_apply
#print axioms Tri.infectionRevealBatchOneY_apply
#print axioms Tri.infectionRevealBatchOneY_zero_of_X
#print axioms Tri.infectionRevealBatchOneX_zero_of_Y
#print axioms Tri.infectionRevealBatchPMF_one_reduce
#print axioms Tri.ennreal_nat_mul_div_mul_inv_cancel
#print axioms Tri.infectionRevealBatchPMF_one_apply
