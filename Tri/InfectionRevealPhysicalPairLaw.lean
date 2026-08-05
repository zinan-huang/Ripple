/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalLaw

/-!
# Exact laws of two-identity activation batches

The auxiliary order carried by a simultaneous physical activation makes every
fixed ordered pair of distinct inactive identities equiprobable. This file
first identifies the four immutable-label fibres and then cancels their
cardinalities against the corresponding coarse event weights.
-/

namespace Tri

open scoped ENNReal

theorem infectionInactiveXXToOrdered_injective
    {n : ℕ} {s : InfectionRevealPhysicalState n} :
    Function.Injective
      (@infectionInactiveXXToOrdered n s) := by
  intro p q hpq
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg
      (fun z : InfectionOrderedRevealTwo s.inactive => z.1.1.1) hpq
  · apply Subtype.ext
    exact congrArg
      (fun z : InfectionOrderedRevealTwo s.inactive => z.1.2.1) hpq

theorem infectionInactiveYYToOrdered_injective
    {n : ℕ} {s : InfectionRevealPhysicalState n} :
    Function.Injective
      (@infectionInactiveYYToOrdered n s) := by
  intro p q hpq
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg
      (fun z : InfectionOrderedRevealTwo s.inactive => z.1.1.1) hpq
  · apply Subtype.ext
    exact congrArg
      (fun z : InfectionOrderedRevealTwo s.inactive => z.1.2.1) hpq

theorem infectionInactiveXYToOrdered_injective
    {n : ℕ} {s : InfectionRevealPhysicalState n} :
    Function.Injective
      (@infectionInactiveXYToOrdered n s) := by
  intro p q hpq
  cases p with
  | inl p =>
      cases q with
      | inl q =>
          congr 1
          apply Prod.ext
          · apply Subtype.ext
            exact congrArg
              (fun z : InfectionOrderedRevealTwo s.inactive =>
                z.1.1.1) hpq
          · apply Subtype.ext
            exact congrArg
              (fun z : InfectionOrderedRevealTwo s.inactive =>
                z.1.2.1) hpq
      | inr q =>
          have hlabel := congrArg
            (fun z : InfectionOrderedRevealTwo s.inactive =>
              s.inactive.initialLabel z.1.1.1) hpq
          change s.inactive.initialLabel (infectionInactiveXToId p.1).1 =
            s.inactive.initialLabel (infectionInactiveYToId q.1).1 at hlabel
          rw [infectionInactiveXToId_label,
            infectionInactiveYToId_label] at hlabel
          contradiction
  | inr p =>
      cases q with
      | inl q =>
          have hlabel := congrArg
            (fun z : InfectionOrderedRevealTwo s.inactive =>
              s.inactive.initialLabel z.1.1.1) hpq
          change s.inactive.initialLabel (infectionInactiveYToId p.1).1 =
            s.inactive.initialLabel (infectionInactiveXToId q.1).1 at hlabel
          rw [infectionInactiveYToId_label,
            infectionInactiveXToId_label] at hlabel
          contradiction
      | inr q =>
          congr 1
          apply Prod.ext
          · apply Subtype.ext
            exact congrArg
              (fun z : InfectionOrderedRevealTwo s.inactive =>
                z.1.1.1) hpq
          · apply Subtype.ext
            exact congrArg
              (fun z : InfectionOrderedRevealTwo s.inactive =>
                z.1.2.1) hpq

theorem infectionRevealBatchOf_activateTwoXX_injective
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    Function.Injective
      (infectionRevealBatchOf s .activateTwoXX) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some q => simp [infectionRevealBatchOf] at hab
  | some p =>
      cases b with
      | none => simp [infectionRevealBatchOf] at hab
      | some q =>
          simp only [infectionRevealBatchOf,
            InfectionRevealBatch.two.injEq] at hab
          congr
          exact infectionInactiveXXToOrdered_injective hab

theorem infectionRevealBatchOf_activateTwoXY_injective
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    Function.Injective
      (infectionRevealBatchOf s .activateTwoXY) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some q => simp [infectionRevealBatchOf] at hab
  | some p =>
      cases b with
      | none => simp [infectionRevealBatchOf] at hab
      | some q =>
          simp only [infectionRevealBatchOf,
            InfectionRevealBatch.two.injEq] at hab
          congr
          exact infectionInactiveXYToOrdered_injective hab

theorem infectionRevealBatchOf_activateTwoYY_injective
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    Function.Injective
      (infectionRevealBatchOf s .activateTwoYY) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some q => simp [infectionRevealBatchOf] at hab
  | some p =>
      cases b with
      | none => simp [infectionRevealBatchOf] at hab
      | some q =>
          simp only [infectionRevealBatchOf,
            InfectionRevealBatch.two.injEq] at hab
          congr
          exact infectionInactiveYYToOrdered_injective hab

def infectionOrderedRevealToXX
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (p : InfectionOrderedRevealTwo s.inactive)
    (hfirst : s.inactive.initialLabel p.1.1.1 = .X)
    (hsecond : s.inactive.initialLabel p.1.2.1 = .X) :
    InfectionInactiveXX s :=
  ⟨(infectionInactiveIdToX p.1.1 hfirst,
      infectionInactiveIdToX p.1.2 hsecond), by
    intro h
    apply p.2
    apply Subtype.ext
    exact congrArg
      (fun i : InfectionInactiveXId s => i.1) h⟩

def infectionOrderedRevealToYY
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (p : InfectionOrderedRevealTwo s.inactive)
    (hfirst : s.inactive.initialLabel p.1.1.1 = .Y)
    (hsecond : s.inactive.initialLabel p.1.2.1 = .Y) :
    InfectionInactiveYY s :=
  ⟨(infectionInactiveIdToY p.1.1 hfirst,
      infectionInactiveIdToY p.1.2 hsecond), by
    intro h
    apply p.2
    apply Subtype.ext
    exact congrArg
      (fun i : InfectionInactiveYId s => i.1) h⟩

def infectionOrderedRevealToXY
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (p : InfectionOrderedRevealTwo s.inactive)
    (hfirst : s.inactive.initialLabel p.1.1.1 = .X)
    (hsecond : s.inactive.initialLabel p.1.2.1 = .Y) :
    InfectionInactiveXY s :=
  .inl (infectionInactiveIdToX p.1.1 hfirst,
    infectionInactiveIdToY p.1.2 hsecond)

def infectionOrderedRevealToYX
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (p : InfectionOrderedRevealTwo s.inactive)
    (hfirst : s.inactive.initialLabel p.1.1.1 = .Y)
    (hsecond : s.inactive.initialLabel p.1.2.1 = .X) :
    InfectionInactiveXY s :=
  .inr (infectionInactiveIdToY p.1.1 hfirst,
    infectionInactiveIdToX p.1.2 hsecond)

theorem infectionRevealBatchTwoXX_apply
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (he : InfectionEvent.weight s.coarse.1 .activateTwoXX ≠ 0)
    (p : InfectionOrderedRevealTwo s.inactive)
    (hfirst : s.inactive.initialLabel p.1.1.1 = .X)
    (hsecond : s.inactive.initialLabel p.1.2.1 = .X) :
    ((infectionRevealWitnessPMF s .activateTwoXX).map
        (infectionRevealBatchOf s .activateTwoXX)) (.two p) =
      (2 * Nat.choose s.coarse.1.ix 2 : ℝ≥0∞)⁻¹ := by
  let q := infectionOrderedRevealToXX p hfirst hsecond
  have hq : infectionInactiveXXToOrdered q = p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  calc
    ((infectionRevealWitnessPMF s .activateTwoXX).map
        (infectionRevealBatchOf s .activateTwoXX)) (.two p) =
        ((infectionRevealWitnessPMF s .activateTwoXX).map
          (infectionRevealBatchOf s .activateTwoXX))
            (infectionRevealBatchOf s .activateTwoXX (some q)) := by
              rw [show infectionRevealBatchOf s .activateTwoXX (some q) =
                .two p by simp [infectionRevealBatchOf, hq]]
    _ = infectionRevealWitnessPMF s .activateTwoXX (some q) :=
      pmf_map_apply_of_injective _ _
        (infectionRevealBatchOf_activateTwoXX_injective s) _
    _ = (2 * Nat.choose s.coarse.1.ix 2 : ℝ≥0∞)⁻¹ := by
      rw [infectionRevealWitnessPMF_some s .activateTwoXX he q]
      simp

theorem infectionRevealBatchTwoXY_apply
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (he : InfectionEvent.weight s.coarse.1 .activateTwoXY ≠ 0)
    (p : InfectionOrderedRevealTwo s.inactive)
    (hfirst : s.inactive.initialLabel p.1.1.1 = .X)
    (hsecond : s.inactive.initialLabel p.1.2.1 = .Y) :
    ((infectionRevealWitnessPMF s .activateTwoXY).map
        (infectionRevealBatchOf s .activateTwoXY)) (.two p) =
      (2 * s.coarse.1.ix * s.coarse.1.iy : ℝ≥0∞)⁻¹ := by
  let q := infectionOrderedRevealToXY p hfirst hsecond
  have hq : infectionInactiveXYToOrdered q = p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  calc
    ((infectionRevealWitnessPMF s .activateTwoXY).map
        (infectionRevealBatchOf s .activateTwoXY)) (.two p) =
        ((infectionRevealWitnessPMF s .activateTwoXY).map
          (infectionRevealBatchOf s .activateTwoXY))
            (infectionRevealBatchOf s .activateTwoXY (some q)) := by
              rw [show infectionRevealBatchOf s .activateTwoXY (some q) =
                .two p by simp [infectionRevealBatchOf, hq]]
    _ = infectionRevealWitnessPMF s .activateTwoXY (some q) :=
      pmf_map_apply_of_injective _ _
        (infectionRevealBatchOf_activateTwoXY_injective s) _
    _ = (2 * s.coarse.1.ix * s.coarse.1.iy : ℝ≥0∞)⁻¹ := by
      rw [infectionRevealWitnessPMF_some s .activateTwoXY he q]
      simp

theorem infectionRevealBatchTwoYX_apply
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (he : InfectionEvent.weight s.coarse.1 .activateTwoXY ≠ 0)
    (p : InfectionOrderedRevealTwo s.inactive)
    (hfirst : s.inactive.initialLabel p.1.1.1 = .Y)
    (hsecond : s.inactive.initialLabel p.1.2.1 = .X) :
    ((infectionRevealWitnessPMF s .activateTwoXY).map
        (infectionRevealBatchOf s .activateTwoXY)) (.two p) =
      (2 * s.coarse.1.ix * s.coarse.1.iy : ℝ≥0∞)⁻¹ := by
  let q := infectionOrderedRevealToYX p hfirst hsecond
  have hq : infectionInactiveXYToOrdered q = p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  calc
    ((infectionRevealWitnessPMF s .activateTwoXY).map
        (infectionRevealBatchOf s .activateTwoXY)) (.two p) =
        ((infectionRevealWitnessPMF s .activateTwoXY).map
          (infectionRevealBatchOf s .activateTwoXY))
            (infectionRevealBatchOf s .activateTwoXY (some q)) := by
              rw [show infectionRevealBatchOf s .activateTwoXY (some q) =
                .two p by simp [infectionRevealBatchOf, hq]]
    _ = infectionRevealWitnessPMF s .activateTwoXY (some q) :=
      pmf_map_apply_of_injective _ _
        (infectionRevealBatchOf_activateTwoXY_injective s) _
    _ = (2 * s.coarse.1.ix * s.coarse.1.iy : ℝ≥0∞)⁻¹ := by
      rw [infectionRevealWitnessPMF_some s .activateTwoXY he q]
      simp

theorem infectionRevealBatchTwoYY_apply
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (he : InfectionEvent.weight s.coarse.1 .activateTwoYY ≠ 0)
    (p : InfectionOrderedRevealTwo s.inactive)
    (hfirst : s.inactive.initialLabel p.1.1.1 = .Y)
    (hsecond : s.inactive.initialLabel p.1.2.1 = .Y) :
    ((infectionRevealWitnessPMF s .activateTwoYY).map
        (infectionRevealBatchOf s .activateTwoYY)) (.two p) =
      (2 * Nat.choose s.coarse.1.iy 2 : ℝ≥0∞)⁻¹ := by
  let q := infectionOrderedRevealToYY p hfirst hsecond
  have hq : infectionInactiveYYToOrdered q = p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  calc
    ((infectionRevealWitnessPMF s .activateTwoYY).map
        (infectionRevealBatchOf s .activateTwoYY)) (.two p) =
        ((infectionRevealWitnessPMF s .activateTwoYY).map
          (infectionRevealBatchOf s .activateTwoYY))
            (infectionRevealBatchOf s .activateTwoYY (some q)) := by
              rw [show infectionRevealBatchOf s .activateTwoYY (some q) =
                .two p by simp [infectionRevealBatchOf, hq]]
    _ = infectionRevealWitnessPMF s .activateTwoYY (some q) :=
      pmf_map_apply_of_injective _ _
        (infectionRevealBatchOf_activateTwoYY_injective s) _
    _ = (2 * Nat.choose s.coarse.1.iy 2 : ℝ≥0∞)⁻¹ := by
      rw [infectionRevealWitnessPMF_some s .activateTwoYY he q]
      simp

/-- Only the three two-activation events contribute to a two-identity batch. -/
theorem infectionRevealBatchPMF_two_reduce
    {n : ℕ} (h3 : 3 ≤ n) (s : InfectionRevealPhysicalState n)
    (p : InfectionOrderedRevealTwo s.inactive) :
    infectionRevealBatchPMF n h3 s (.two p) =
      infectionEventPMF s.coarse.1
          (infectionRevealPhysicalTotalAtLeastThree n h3 s)
          .activateTwoXX *
        ((infectionRevealWitnessPMF s .activateTwoXX).map
          (infectionRevealBatchOf s .activateTwoXX)) (.two p) +
      infectionEventPMF s.coarse.1
          (infectionRevealPhysicalTotalAtLeastThree n h3 s)
          .activateTwoXY *
        ((infectionRevealWitnessPMF s .activateTwoXY).map
          (infectionRevealBatchOf s .activateTwoXY)) (.two p) +
      infectionEventPMF s.coarse.1
          (infectionRevealPhysicalTotalAtLeastThree n h3 s)
          .activateTwoYY *
        ((infectionRevealWitnessPMF s .activateTwoYY).map
          (infectionRevealBatchOf s .activateTwoYY)) (.two p) := by
  unfold infectionRevealBatchPMF
  rw [PMF.bind_apply, tsum_fintype]
  rw [show (Finset.univ : Finset InfectionEvent) =
    {InfectionEvent.activeXXX, InfectionEvent.activeXXY,
      InfectionEvent.activeXYY, InfectionEvent.activeYYY,
      InfectionEvent.activateOneX, InfectionEvent.activateOneY,
      InfectionEvent.activateTwoXX, InfectionEvent.activateTwoXY,
      InfectionEvent.activateTwoYY, InfectionEvent.inactiveOnly} from rfl]
  simp [infectionRevealBatchOf, PMF.map_apply, tsum_fintype]
  ring

/-- Cancel an event-fibre cardinality after adding an auxiliary uniform order. -/
theorem ennreal_event_uniform_cancel
    (a c d k : ℕ) (hc : c ≠ 0) (hd : d ≠ 0) :
    (((a * c : ℕ) : ℝ≥0∞) / (d : ℝ≥0∞)) *
        (((k * c : ℕ) : ℝ≥0∞))⁻¹ =
      (a : ℝ≥0∞) / ((k * d : ℕ) : ℝ≥0∞) := by
  have hc0 : (c : ℝ≥0∞) ≠ 0 :=
    (Nat.cast_ne_zero (R := ℝ≥0∞)).mpr hc
  have hctop : (c : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hd0 : (d : ℝ≥0∞) ≠ 0 :=
    (Nat.cast_ne_zero (R := ℝ≥0∞)).mpr hd
  have hdtop : (d : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    (((a * c : ℕ) : ℝ≥0∞) / (d : ℝ≥0∞)) *
          (((k * c : ℕ) : ℝ≥0∞))⁻¹ =
        ((a : ℝ≥0∞) * (c : ℝ≥0∞)) /
          ((d : ℝ≥0∞) *
            ((k : ℝ≥0∞) * (c : ℝ≥0∞))) := by
              simp only [Nat.cast_mul, div_eq_mul_inv]
              rw [ENNReal.mul_inv
                (a := (d : ℝ≥0∞))
                (b := (k : ℝ≥0∞) * (c : ℝ≥0∞))
                (Or.inl hd0) (Or.inl hdtop)]
              simp only [mul_assoc, mul_comm]
    _ = ((c : ℝ≥0∞) * (a : ℝ≥0∞)) /
          ((c : ℝ≥0∞) *
            ((k : ℝ≥0∞) * (d : ℝ≥0∞))) := by
              congr 1 <;> ring
    _ = (a : ℝ≥0∞) /
          ((k : ℝ≥0∞) * (d : ℝ≥0∞)) :=
      ENNReal.mul_div_mul_left _ _ hc0 hctop
    _ = (a : ℝ≥0∞) /
          ((k * d : ℕ) : ℝ≥0∞) := by
      rw [Nat.cast_mul]

theorem infectionRevealBatchTwoXX_zero_of_firstY
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (p : InfectionOrderedRevealTwo s.inactive)
    (hfirst : s.inactive.initialLabel p.1.1.1 = .Y) :
    ((infectionRevealWitnessPMF s .activateTwoXX).map
        (infectionRevealBatchOf s .activateTwoXX)) (.two p) = 0 := by
  apply pmf_map_apply_eq_zero_of_not_mem_range
  intro w
  cases w with
  | none => simp [infectionRevealBatchOf]
  | some q =>
      simp only [infectionRevealBatchOf, ne_eq,
        InfectionRevealBatch.two.injEq]
      intro h
      have hlabel := congrArg
        (fun z : InfectionOrderedRevealTwo s.inactive =>
          s.inactive.initialLabel z.1.1.1) h
      change s.inactive.initialLabel p.1.1.1 =
        s.inactive.initialLabel
          (infectionInactiveXToId q.1.1).1 at hlabel
      rw [hfirst, infectionInactiveXToId_label] at hlabel
      contradiction

theorem infectionRevealBatchTwoXX_zero_of_secondY
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (p : InfectionOrderedRevealTwo s.inactive)
    (hsecond : s.inactive.initialLabel p.1.2.1 = .Y) :
    ((infectionRevealWitnessPMF s .activateTwoXX).map
        (infectionRevealBatchOf s .activateTwoXX)) (.two p) = 0 := by
  apply pmf_map_apply_eq_zero_of_not_mem_range
  intro w
  cases w with
  | none => simp [infectionRevealBatchOf]
  | some q =>
      simp only [infectionRevealBatchOf, ne_eq,
        InfectionRevealBatch.two.injEq]
      intro h
      have hlabel := congrArg
        (fun z : InfectionOrderedRevealTwo s.inactive =>
          s.inactive.initialLabel z.1.2.1) h
      change s.inactive.initialLabel p.1.2.1 =
        s.inactive.initialLabel
          (infectionInactiveXToId q.1.2).1 at hlabel
      rw [hsecond, infectionInactiveXToId_label] at hlabel
      contradiction

theorem infectionRevealBatchTwoYY_zero_of_firstX
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (p : InfectionOrderedRevealTwo s.inactive)
    (hfirst : s.inactive.initialLabel p.1.1.1 = .X) :
    ((infectionRevealWitnessPMF s .activateTwoYY).map
        (infectionRevealBatchOf s .activateTwoYY)) (.two p) = 0 := by
  apply pmf_map_apply_eq_zero_of_not_mem_range
  intro w
  cases w with
  | none => simp [infectionRevealBatchOf]
  | some q =>
      simp only [infectionRevealBatchOf, ne_eq,
        InfectionRevealBatch.two.injEq]
      intro h
      have hlabel := congrArg
        (fun z : InfectionOrderedRevealTwo s.inactive =>
          s.inactive.initialLabel z.1.1.1) h
      change s.inactive.initialLabel p.1.1.1 =
        s.inactive.initialLabel
          (infectionInactiveYToId q.1.1).1 at hlabel
      rw [hfirst, infectionInactiveYToId_label] at hlabel
      contradiction

theorem infectionRevealBatchTwoYY_zero_of_secondX
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (p : InfectionOrderedRevealTwo s.inactive)
    (hsecond : s.inactive.initialLabel p.1.2.1 = .X) :
    ((infectionRevealWitnessPMF s .activateTwoYY).map
        (infectionRevealBatchOf s .activateTwoYY)) (.two p) = 0 := by
  apply pmf_map_apply_eq_zero_of_not_mem_range
  intro w
  cases w with
  | none => simp [infectionRevealBatchOf]
  | some q =>
      simp only [infectionRevealBatchOf, ne_eq,
        InfectionRevealBatch.two.injEq]
      intro h
      have hlabel := congrArg
        (fun z : InfectionOrderedRevealTwo s.inactive =>
          s.inactive.initialLabel z.1.2.1) h
      change s.inactive.initialLabel p.1.2.1 =
        s.inactive.initialLabel
          (infectionInactiveYToId q.1.2).1 at hlabel
      rw [hsecond, infectionInactiveYToId_label] at hlabel
      contradiction

theorem infectionRevealBatchTwoXY_zero_of_XX
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (p : InfectionOrderedRevealTwo s.inactive)
    (hfirst : s.inactive.initialLabel p.1.1.1 = .X)
    (hsecond : s.inactive.initialLabel p.1.2.1 = .X) :
    ((infectionRevealWitnessPMF s .activateTwoXY).map
        (infectionRevealBatchOf s .activateTwoXY)) (.two p) = 0 := by
  apply pmf_map_apply_eq_zero_of_not_mem_range
  intro w
  cases w with
  | none => simp [infectionRevealBatchOf]
  | some q =>
      simp only [infectionRevealBatchOf, ne_eq,
        InfectionRevealBatch.two.injEq]
      intro h
      cases q with
      | inl q =>
          have hlabel := congrArg
            (fun z : InfectionOrderedRevealTwo s.inactive =>
              s.inactive.initialLabel z.1.2.1) h
          change s.inactive.initialLabel p.1.2.1 =
            s.inactive.initialLabel
              (infectionInactiveYToId q.2).1 at hlabel
          rw [hsecond, infectionInactiveYToId_label] at hlabel
          contradiction
      | inr q =>
          have hlabel := congrArg
            (fun z : InfectionOrderedRevealTwo s.inactive =>
              s.inactive.initialLabel z.1.1.1) h
          change s.inactive.initialLabel p.1.1.1 =
            s.inactive.initialLabel
              (infectionInactiveYToId q.1).1 at hlabel
          rw [hfirst, infectionInactiveYToId_label] at hlabel
          contradiction

theorem infectionRevealBatchTwoXY_zero_of_YY
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (p : InfectionOrderedRevealTwo s.inactive)
    (hfirst : s.inactive.initialLabel p.1.1.1 = .Y)
    (hsecond : s.inactive.initialLabel p.1.2.1 = .Y) :
    ((infectionRevealWitnessPMF s .activateTwoXY).map
        (infectionRevealBatchOf s .activateTwoXY)) (.two p) = 0 := by
  apply pmf_map_apply_eq_zero_of_not_mem_range
  intro w
  cases w with
  | none => simp [infectionRevealBatchOf]
  | some q =>
      simp only [infectionRevealBatchOf, ne_eq,
        InfectionRevealBatch.two.injEq]
      intro h
      cases q with
      | inl q =>
          have hlabel := congrArg
            (fun z : InfectionOrderedRevealTwo s.inactive =>
              s.inactive.initialLabel z.1.1.1) h
          change s.inactive.initialLabel p.1.1.1 =
            s.inactive.initialLabel
              (infectionInactiveXToId q.1).1 at hlabel
          rw [hfirst, infectionInactiveXToId_label] at hlabel
          contradiction
      | inr q =>
          have hlabel := congrArg
            (fun z : InfectionOrderedRevealTwo s.inactive =>
              s.inactive.initialLabel z.1.2.1) h
          change s.inactive.initialLabel p.1.2.1 =
            s.inactive.initialLabel
              (infectionInactiveXToId q.2).1 at hlabel
          rw [hsecond, infectionInactiveXToId_label] at hlabel
          contradiction

/-- Every fixed ordered pair of distinct inactive identities has the same
two-activation mass, independently of its immutable labels. -/
theorem infectionRevealBatchPMF_two_apply
    {n : ℕ} (h3 : 3 ≤ n) (s : InfectionRevealPhysicalState n)
    (p : InfectionOrderedRevealTwo s.inactive) :
    infectionRevealBatchPMF n h3 s (.two p) =
      (s.coarse.1.active : ℝ≥0∞) /
        ((2 * Nat.choose n 3 : ℕ) : ℝ≥0∞) := by
  rw [infectionRevealBatchPMF_two_reduce]
  have htotal : s.coarse.1.total = n := s.coarse.2
  have hd : Nat.choose n 3 ≠ 0 := (choose_three_pos h3).ne'
  cases hfirst :
      s.inactive.initialLabel p.1.1.1 <;>
    cases hsecond :
      s.inactive.initialLabel p.1.2.1
  case X.X =>
    have hmem1 : p.1.1.1 ∈ s.inactive.xIds :=
      Finset.mem_filter.mpr ⟨p.1.1.2, hfirst⟩
    have hmem2 : p.1.2.1 ∈ s.inactive.xIds :=
      Finset.mem_filter.mpr ⟨p.1.2.2, hsecond⟩
    have hne : p.1.1.1 ≠ p.1.2.1 := by
      intro h
      apply p.2
      exact Subtype.ext h
    have hcard : 1 < s.inactive.xIds.card :=
      Finset.one_lt_card.mpr
        ⟨p.1.1.1, hmem1, p.1.2.1, hmem2, hne⟩
    have hc : Nat.choose s.coarse.1.ix 2 ≠ 0 := by
      rw [Nat.choose_ne_zero_iff, ← s.hinactiveX]
      omega
    by_cases ha : s.coarse.1.active = 0
    · simp [infectionEventPMF_apply, InfectionEvent.weight, ha]
    · have he :
          InfectionEvent.weight s.coarse.1 .activateTwoXX ≠ 0 := by
        simpa only [InfectionEvent.weight] using Nat.mul_ne_zero ha hc
      rw [infectionRevealBatchTwoXX_apply s he p hfirst hsecond,
        infectionRevealBatchTwoXY_zero_of_XX s p hfirst hsecond,
        infectionRevealBatchTwoYY_zero_of_firstX s p hfirst,
        infectionEventPMF_apply]
      simp only [mul_zero, add_zero]
      simp only [InfectionEvent.weight]
      rw [htotal]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        ennreal_event_uniform_cancel s.coarse.1.active
          (Nat.choose s.coarse.1.ix 2) (Nat.choose n 3) 2 hc hd
  case X.Y =>
    have hxcard : 0 < s.inactive.xIds.card :=
      Finset.card_pos.mpr ⟨p.1.1.1,
        Finset.mem_filter.mpr ⟨p.1.1.2, hfirst⟩⟩
    have hycard : 0 < s.inactive.yIds.card :=
      Finset.card_pos.mpr ⟨p.1.2.1,
        Finset.mem_filter.mpr ⟨p.1.2.2, hsecond⟩⟩
    have hix : s.coarse.1.ix ≠ 0 := by
      rw [← s.hinactiveX]
      exact hxcard.ne'
    have hiy : s.coarse.1.iy ≠ 0 := by
      rw [← s.hinactiveY]
      exact hycard.ne'
    have hc : s.coarse.1.ix * s.coarse.1.iy ≠ 0 :=
      Nat.mul_ne_zero hix hiy
    by_cases ha : s.coarse.1.active = 0
    · simp [infectionEventPMF_apply, InfectionEvent.weight, ha]
    · have he :
          InfectionEvent.weight s.coarse.1 .activateTwoXY ≠ 0 := by
        simpa only [InfectionEvent.weight, Nat.mul_assoc] using
          Nat.mul_ne_zero ha hc
      rw [infectionRevealBatchTwoXX_zero_of_secondY s p hsecond,
        infectionRevealBatchTwoXY_apply s he p hfirst hsecond,
        infectionRevealBatchTwoYY_zero_of_firstX s p hfirst,
        infectionEventPMF_apply]
      simp only [mul_zero, zero_add, add_zero]
      rw [infectionEventPMF_apply]
      simp only [InfectionEvent.weight]
      rw [htotal]
      simpa only [Nat.mul_assoc, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
        ennreal_event_uniform_cancel s.coarse.1.active
          (s.coarse.1.ix * s.coarse.1.iy)
          (Nat.choose n 3) 2 hc hd
  case Y.X =>
    have hycard : 0 < s.inactive.yIds.card :=
      Finset.card_pos.mpr ⟨p.1.1.1,
        Finset.mem_filter.mpr ⟨p.1.1.2, hfirst⟩⟩
    have hxcard : 0 < s.inactive.xIds.card :=
      Finset.card_pos.mpr ⟨p.1.2.1,
        Finset.mem_filter.mpr ⟨p.1.2.2, hsecond⟩⟩
    have hiy : s.coarse.1.iy ≠ 0 := by
      rw [← s.hinactiveY]
      exact hycard.ne'
    have hix : s.coarse.1.ix ≠ 0 := by
      rw [← s.hinactiveX]
      exact hxcard.ne'
    have hc : s.coarse.1.ix * s.coarse.1.iy ≠ 0 :=
      Nat.mul_ne_zero hix hiy
    by_cases ha : s.coarse.1.active = 0
    · simp [infectionEventPMF_apply, InfectionEvent.weight, ha]
    · have he :
          InfectionEvent.weight s.coarse.1 .activateTwoXY ≠ 0 := by
        simpa only [InfectionEvent.weight, Nat.mul_assoc] using
          Nat.mul_ne_zero ha hc
      rw [infectionRevealBatchTwoXX_zero_of_firstY s p hfirst,
        infectionRevealBatchTwoYX_apply s he p hfirst hsecond,
        infectionRevealBatchTwoYY_zero_of_secondX s p hsecond,
        infectionEventPMF_apply]
      simp only [mul_zero, zero_add, add_zero]
      rw [infectionEventPMF_apply]
      simp only [InfectionEvent.weight]
      rw [htotal]
      simpa only [Nat.mul_assoc, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
        ennreal_event_uniform_cancel s.coarse.1.active
          (s.coarse.1.ix * s.coarse.1.iy)
          (Nat.choose n 3) 2 hc hd
  case Y.Y =>
    have hmem1 : p.1.1.1 ∈ s.inactive.yIds :=
      Finset.mem_filter.mpr ⟨p.1.1.2, hfirst⟩
    have hmem2 : p.1.2.1 ∈ s.inactive.yIds :=
      Finset.mem_filter.mpr ⟨p.1.2.2, hsecond⟩
    have hne : p.1.1.1 ≠ p.1.2.1 := by
      intro h
      apply p.2
      exact Subtype.ext h
    have hcard : 1 < s.inactive.yIds.card :=
      Finset.one_lt_card.mpr
        ⟨p.1.1.1, hmem1, p.1.2.1, hmem2, hne⟩
    have hc : Nat.choose s.coarse.1.iy 2 ≠ 0 := by
      rw [Nat.choose_ne_zero_iff, ← s.hinactiveY]
      omega
    by_cases ha : s.coarse.1.active = 0
    · simp [infectionEventPMF_apply, InfectionEvent.weight, ha]
    · have he :
          InfectionEvent.weight s.coarse.1 .activateTwoYY ≠ 0 := by
        simpa only [InfectionEvent.weight] using Nat.mul_ne_zero ha hc
      rw [infectionRevealBatchTwoXX_zero_of_firstY s p hfirst,
        infectionRevealBatchTwoXY_zero_of_YY s p hfirst hsecond,
        infectionRevealBatchTwoYY_apply s he p hfirst hsecond,
        infectionEventPMF_apply]
      simp only [mul_zero, zero_add, add_zero]
      rw [infectionEventPMF_apply]
      simp only [InfectionEvent.weight]
      rw [htotal]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        ennreal_event_uniform_cancel s.coarse.1.active
          (Nat.choose s.coarse.1.iy 2) (Nat.choose n 3) 2 hc hd

/-- An activation event contributes no mass to the empty batch.  If its event
weight is zero the outer coefficient vanishes; otherwise `none` has zero
conditional witness mass. -/
theorem infectionRevealActivationNoneContribution_zero
    {n : ℕ} (h3 : 3 ≤ n) (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent)
    (hf : Function.Injective (infectionRevealBatchOf s e)) :
    infectionEventPMF s.coarse.1
        (infectionRevealPhysicalTotalAtLeastThree n h3 s) e *
      ((infectionRevealWitnessPMF s e).map
        (infectionRevealBatchOf s e)) .none = 0 := by
  by_cases he : InfectionEvent.weight s.coarse.1 e = 0
  · simp [infectionEventPMF_apply, he]
  · change _ *
      ((infectionRevealWitnessPMF s e).map
        (infectionRevealBatchOf s e))
          (infectionRevealBatchOf s e none) = 0
    rw [pmf_map_apply_of_injective _ _ hf none,
      infectionRevealWitnessPMF_none s e he, mul_zero]

/-- A semantic no-activation event contributes its full event mass to the
empty batch. -/
theorem infectionRevealNoActivationNoneContribution
    {n : ℕ} (h3 : 3 ≤ n) (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent)
    (hf : ∀ w, infectionRevealBatchOf s e w = .none) :
    infectionEventPMF s.coarse.1
        (infectionRevealPhysicalTotalAtLeastThree n h3 s) e *
      ((infectionRevealWitnessPMF s e).map
        (infectionRevealBatchOf s e)) .none =
      infectionEventPMF s.coarse.1
        (infectionRevealPhysicalTotalAtLeastThree n h3 s) e := by
  have hfun :
      infectionRevealBatchOf s e =
        Function.const _ (InfectionRevealBatch.none) := by
    funext w
    exact hf w
  rw [hfun, PMF.map_const]
  simp

/-- Pointwise empty-batch contribution, classified only by activation count. -/
theorem infectionRevealBatchNoneContribution
    {n : ℕ} (h3 : 3 ≤ n) (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent) :
    infectionEventPMF s.coarse.1
        (infectionRevealPhysicalTotalAtLeastThree n h3 s) e *
      ((infectionRevealWitnessPMF s e).map
        (infectionRevealBatchOf s e)) .none =
      if e.activationInc = 0 then
        infectionEventPMF s.coarse.1
          (infectionRevealPhysicalTotalAtLeastThree n h3 s) e
      else 0 := by
  cases e with
  | activeXXX =>
      simpa [InfectionEvent.activationInc] using
        infectionRevealNoActivationNoneContribution h3 s .activeXXX
          (by intro w; cases w <;> rfl)
  | activeXXY =>
      simpa [InfectionEvent.activationInc] using
        infectionRevealNoActivationNoneContribution h3 s .activeXXY
          (by intro w; cases w <;> rfl)
  | activeXYY =>
      simpa [InfectionEvent.activationInc] using
        infectionRevealNoActivationNoneContribution h3 s .activeXYY
          (by intro w; cases w <;> rfl)
  | activeYYY =>
      simpa [InfectionEvent.activationInc] using
        infectionRevealNoActivationNoneContribution h3 s .activeYYY
          (by intro w; cases w <;> rfl)
  | activateOneX =>
      simpa [InfectionEvent.activationInc] using
        infectionRevealActivationNoneContribution_zero h3 s .activateOneX
          (infectionRevealBatchOf_activateOneX_injective s)
  | activateOneY =>
      simpa [InfectionEvent.activationInc] using
        infectionRevealActivationNoneContribution_zero h3 s .activateOneY
          (infectionRevealBatchOf_activateOneY_injective s)
  | activateTwoXX =>
      simpa [InfectionEvent.activationInc] using
        infectionRevealActivationNoneContribution_zero h3 s .activateTwoXX
          (infectionRevealBatchOf_activateTwoXX_injective s)
  | activateTwoXY =>
      simpa [InfectionEvent.activationInc] using
        infectionRevealActivationNoneContribution_zero h3 s .activateTwoXY
          (infectionRevealBatchOf_activateTwoXY_injective s)
  | activateTwoYY =>
      simpa [InfectionEvent.activationInc] using
        infectionRevealActivationNoneContribution_zero h3 s .activateTwoYY
          (infectionRevealBatchOf_activateTwoYY_injective s)
  | inactiveOnly =>
      simpa [InfectionEvent.activationInc] using
        infectionRevealNoActivationNoneContribution h3 s .inactiveOnly
          (by intro w; cases w <;> rfl)

/-- The empty physical batch is exactly the coarse no-activation event. -/
theorem infectionRevealBatchPMF_none_eq_noActivationMass
    {n : ℕ} (h3 : 3 ≤ n) (s : InfectionRevealPhysicalState n) :
    infectionRevealBatchPMF n h3 s .none =
      infectionNoActivationMass s.coarse.1
        (infectionRevealPhysicalTotalAtLeastThree n h3 s) := by
  unfold infectionRevealBatchPMF
  rw [PMF.bind_apply, tsum_fintype]
  calc
    ∑ e : InfectionEvent,
        infectionEventPMF s.coarse.1
            (infectionRevealPhysicalTotalAtLeastThree n h3 s) e *
          ((infectionRevealWitnessPMF s e).map
            (infectionRevealBatchOf s e)) .none =
        ∑ e : InfectionEvent,
          if e.activationInc = 0 then
            infectionEventPMF s.coarse.1
              (infectionRevealPhysicalTotalAtLeastThree n h3 s) e
          else 0 := by
            apply Finset.sum_congr rfl
            intro e he
            exact infectionRevealBatchNoneContribution h3 s e
    _ = infectionNoActivationMass s.coarse.1
          (infectionRevealPhysicalTotalAtLeastThree n h3 s) := by
      rw [show (Finset.univ : Finset InfectionEvent) =
        {InfectionEvent.activeXXX, InfectionEvent.activeXXY,
          InfectionEvent.activeXYY, InfectionEvent.activeYYY,
          InfectionEvent.activateOneX, InfectionEvent.activateOneY,
          InfectionEvent.activateTwoXX, InfectionEvent.activateTwoXY,
          InfectionEvent.activateTwoYY, InfectionEvent.inactiveOnly} from rfl]
      simp [InfectionEvent.activationInc, infectionNoActivationMass]
      ring

/-- Exact mass of the empty physical activation batch. -/
theorem infectionRevealBatchPMF_none_apply
    {n : ℕ} (h3 : 3 ≤ n) (s : InfectionRevealPhysicalState n) :
    infectionRevealBatchPMF n h3 s .none =
      ((Nat.choose s.coarse.1.active 3 +
          Nat.choose s.coarse.1.inactive 3 : ℕ) : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) := by
  rw [infectionRevealBatchPMF_none_eq_noActivationMass,
    infectionNoActivationMass_eq]
  rw [show s.coarse.1.total = n from s.coarse.2]

end Tri

#print axioms Tri.infectionInactiveXXToOrdered_injective
#print axioms Tri.infectionInactiveXYToOrdered_injective
#print axioms Tri.infectionInactiveYYToOrdered_injective
#print axioms Tri.infectionRevealBatchOf_activateTwoXX_injective
#print axioms Tri.infectionRevealBatchOf_activateTwoXY_injective
#print axioms Tri.infectionRevealBatchOf_activateTwoYY_injective
#print axioms Tri.infectionRevealBatchTwoXX_apply
#print axioms Tri.infectionRevealBatchTwoXY_apply
#print axioms Tri.infectionRevealBatchTwoYX_apply
#print axioms Tri.infectionRevealBatchTwoYY_apply
#print axioms Tri.infectionRevealBatchPMF_two_reduce
#print axioms Tri.ennreal_event_uniform_cancel
#print axioms Tri.infectionRevealBatchTwoXX_zero_of_firstY
#print axioms Tri.infectionRevealBatchTwoXX_zero_of_secondY
#print axioms Tri.infectionRevealBatchTwoYY_zero_of_firstX
#print axioms Tri.infectionRevealBatchTwoYY_zero_of_secondX
#print axioms Tri.infectionRevealBatchTwoXY_zero_of_XX
#print axioms Tri.infectionRevealBatchTwoXY_zero_of_YY
#print axioms Tri.infectionRevealBatchPMF_two_apply
#print axioms Tri.infectionRevealActivationNoneContribution_zero
#print axioms Tri.infectionRevealNoActivationNoneContribution
#print axioms Tri.infectionRevealBatchNoneContribution
#print axioms Tri.infectionRevealBatchPMF_none_eq_noActivationMass
#print axioms Tri.infectionRevealBatchPMF_none_apply
