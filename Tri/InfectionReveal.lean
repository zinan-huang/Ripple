/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionActivation
import Mathlib.Probability.Distributions.Uniform

/-!
# Stable identities and statewise reveal exchangeability

This identity-refined layer isolates the conditional law used by the
infection protocol's label analysis. For a fixed current inactive view, one
reveal is uniform on the remaining inactive identities and two reveals are
uniform on ordered distinct pairs. This is a statewise statement, not an
independence claim about active reactions.
-/

namespace Tri

open scoped ENNReal

/-- Immutable pre-activation opinion carried by a molecule identity. -/
inductive InfectionLabel
  | X
  | Y
  deriving DecidableEq, Fintype, Repr

/-- Stable identities and immutable labels of the molecules still inactive. -/
structure InfectionInactiveView (n : ℕ) where
  ids : Finset (Fin n)
  initialLabel : Fin n → InfectionLabel

namespace InfectionInactiveView

def xIds {n : ℕ} (v : InfectionInactiveView n) : Finset (Fin n) :=
  v.ids.filter fun i => v.initialLabel i = .X

def yIds {n : ℕ} (v : InfectionInactiveView n) : Finset (Fin n) :=
  v.ids.filter fun i => v.initialLabel i = .Y

end InfectionInactiveView

/-- Identity-level refinement of the existing four-count state.

Current labels may change on active identities. On inactive identities they
remain equal to the immutable initial labels. -/
structure InfectionIdentityState (n : ℕ) where
  coarse : InfectionState n
  currentLabel : Fin n → InfectionLabel
  activeIds : Finset (Fin n)
  inactive : InfectionInactiveView n
  hpartition : activeIds ∪ inactive.ids = Finset.univ
  hdisjoint : Disjoint activeIds inactive.ids
  hactiveCard : activeIds.card = coarse.1.active
  hinactiveCard : inactive.ids.card = coarse.1.inactive
  hactiveX :
    (activeIds.filter fun i => currentLabel i = .X).card = coarse.1.ax
  hactiveY :
    (activeIds.filter fun i => currentLabel i = .Y).card = coarse.1.ay
  hinactiveX : inactive.xIds.card = coarse.1.ix
  hinactiveY : inactive.yIds.card = coarse.1.iy
  hinactiveCurrent :
    ∀ i, i ∈ inactive.ids → currentLabel i = inactive.initialLabel i

def infectionIdentityForget
    {n : ℕ} (s : InfectionIdentityState n) : InfectionState n :=
  s.coarse

@[simp] theorem infectionIdentityForget_active
    {n : ℕ} (s : InfectionIdentityState n) :
    (infectionIdentityForget s).1.active = s.activeIds.card :=
  s.hactiveCard.symm

@[simp] theorem infectionIdentityForget_inactive
    {n : ℕ} (s : InfectionIdentityState n) :
    (infectionIdentityForget s).1.inactive = s.inactive.ids.card :=
  s.hinactiveCard.symm

@[simp] theorem infectionIdentityForget_ax
    {n : ℕ} (s : InfectionIdentityState n) :
    (infectionIdentityForget s).1.ax =
      (s.activeIds.filter fun i => s.currentLabel i = .X).card :=
  s.hactiveX.symm

@[simp] theorem infectionIdentityForget_ay
    {n : ℕ} (s : InfectionIdentityState n) :
    (infectionIdentityForget s).1.ay =
      (s.activeIds.filter fun i => s.currentLabel i = .Y).card :=
  s.hactiveY.symm

@[simp] theorem infectionIdentityForget_ix
    {n : ℕ} (s : InfectionIdentityState n) :
    (infectionIdentityForget s).1.ix = s.inactive.xIds.card :=
  s.hinactiveX.symm

@[simp] theorem infectionIdentityForget_iy
    {n : ℕ} (s : InfectionIdentityState n) :
    (infectionIdentityForget s).1.iy = s.inactive.yIds.card :=
  s.hinactiveY.symm

/-- A remaining inactive molecule, with stable identity. -/
abbrev InfectionInactiveId
    {n : ℕ} (v : InfectionInactiveView n) :=
  ↥v.ids

/-- Two successive revealed identities, sampled without replacement. -/
def InfectionOrderedRevealTwo
    {n : ℕ} (v : InfectionInactiveView n) :=
  {p : InfectionInactiveId v × InfectionInactiveId v // p.1 ≠ p.2}

noncomputable instance infectionOrderedRevealTwoDecidableEq
    {n : ℕ} (v : InfectionInactiveView n) :
    DecidableEq (InfectionOrderedRevealTwo v) :=
  Classical.decEq _

noncomputable instance infectionOrderedRevealTwoFintype
    {n : ℕ} (v : InfectionInactiveView n) :
    Fintype (InfectionOrderedRevealTwo v) := by
  unfold InfectionOrderedRevealTwo
  infer_instance

@[simp] theorem card_infectionInactiveId
    {n : ℕ} (v : InfectionInactiveView n) :
    Fintype.card (InfectionInactiveId v) = v.ids.card := by
  simp [InfectionInactiveId]

theorem infectionRevealOne_nonempty_of_card_pos
    {n : ℕ} (v : InfectionInactiveView n)
    (h : 0 < v.ids.card) :
    Nonempty (InfectionInactiveId v) :=
  Fintype.card_pos_iff.mp (by simpa using h)

theorem infectionRevealTwo_nonempty_of_pair
    {n : ℕ} (v : InfectionInactiveView n)
    (i j : InfectionInactiveId v) (hij : i ≠ j) :
    Nonempty (InfectionOrderedRevealTwo v) :=
  ⟨⟨(i, j), hij⟩⟩

noncomputable def infectionRevealOnePMF
    {n : ℕ} (v : InfectionInactiveView n)
    (h : Nonempty (InfectionInactiveId v)) :
    PMF (InfectionInactiveId v) :=
  @PMF.uniformOfFintype
    (InfectionInactiveId v)
    inferInstance
    h

noncomputable def infectionRevealTwoPMF
    {n : ℕ} (v : InfectionInactiveView n)
    (h : Nonempty (InfectionOrderedRevealTwo v)) :
    PMF (InfectionOrderedRevealTwo v) :=
  @PMF.uniformOfFintype
    (InfectionOrderedRevealTwo v)
    inferInstance
    h

@[simp] theorem infectionRevealOnePMF_apply
    {n : ℕ} (v : InfectionInactiveView n)
    (h : Nonempty (InfectionInactiveId v))
    (i : InfectionInactiveId v) :
    infectionRevealOnePMF v h i =
      (Fintype.card (InfectionInactiveId v) : ℝ≥0∞)⁻¹ := by
  letI : Nonempty (InfectionInactiveId v) := h
  unfold infectionRevealOnePMF
  rw [PMF.uniformOfFintype_apply]

@[simp] theorem infectionRevealTwoPMF_apply
    {n : ℕ} (v : InfectionInactiveView n)
    (h : Nonempty (InfectionOrderedRevealTwo v))
    (p : InfectionOrderedRevealTwo v) :
    infectionRevealTwoPMF v h p =
      (Fintype.card (InfectionOrderedRevealTwo v) : ℝ≥0∞)⁻¹ := by
  letI : Nonempty (InfectionOrderedRevealTwo v) := h
  unfold infectionRevealTwoPMF
  rw [PMF.uniformOfFintype_apply]

theorem infectionRevealOne_exchangeable
    {n : ℕ} (v : InfectionInactiveView n)
    (h : Nonempty (InfectionInactiveId v))
    (i j : InfectionInactiveId v) :
    infectionRevealOnePMF v h i = infectionRevealOnePMF v h j := by
  rw [infectionRevealOnePMF_apply, infectionRevealOnePMF_apply]

theorem infectionRevealTwo_exchangeable
    {n : ℕ} (v : InfectionInactiveView n)
    (h : Nonempty (InfectionOrderedRevealTwo v))
    (p q : InfectionOrderedRevealTwo v) :
    infectionRevealTwoPMF v h p = infectionRevealTwoPMF v h q := by
  rw [infectionRevealTwoPMF_apply, infectionRevealTwoPMF_apply]

theorem infectionRevealTwo_ne
    {n : ℕ} {v : InfectionInactiveView n}
    (p : InfectionOrderedRevealTwo v) :
    p.1.1 ≠ p.1.2 :=
  p.2

def infectionRevealOneLabel
    {n : ℕ} (v : InfectionInactiveView n)
    (i : InfectionInactiveId v) : InfectionLabel :=
  v.initialLabel i.1

def infectionRevealTwoLabels
    {n : ℕ} (v : InfectionInactiveView n)
    (p : InfectionOrderedRevealTwo v) :
    InfectionLabel × InfectionLabel :=
  (v.initialLabel p.1.1.1, v.initialLabel p.1.2.1)

noncomputable def infectionRevealOneLabelPMF
    {n : ℕ} (v : InfectionInactiveView n)
    (h : Nonempty (InfectionInactiveId v)) :
    PMF InfectionLabel :=
  (infectionRevealOnePMF v h).map (infectionRevealOneLabel v)

noncomputable def infectionRevealTwoLabelPMF
    {n : ℕ} (v : InfectionInactiveView n)
    (h : Nonempty (InfectionOrderedRevealTwo v)) :
    PMF (InfectionLabel × InfectionLabel) :=
  (infectionRevealTwoPMF v h).map (infectionRevealTwoLabels v)

theorem infectionRevealOneLabelPMF_congr
    {n : ℕ} {v w : InfectionInactiveView n}
    (hvw : v = w)
    (hv : Nonempty (InfectionInactiveId v))
    (hw : Nonempty (InfectionInactiveId w)) :
    infectionRevealOneLabelPMF v hv =
      infectionRevealOneLabelPMF w hw := by
  subst w
  cases Subsingleton.elim hv hw
  rfl

theorem infectionRevealTwoLabelPMF_congr
    {n : ℕ} {v w : InfectionInactiveView n}
    (hvw : v = w)
    (hv : Nonempty (InfectionOrderedRevealTwo v))
    (hw : Nonempty (InfectionOrderedRevealTwo w)) :
    infectionRevealTwoLabelPMF v hv =
      infectionRevealTwoLabelPMF w hw := by
  subst w
  cases Subsingleton.elim hv hw
  rfl

namespace InfectionIdentityState

/-- An active-only step may change active labels but preserves the complete
future inactive view. -/
def ActiveOnlyCompatible
    {n : ℕ} (s t : InfectionIdentityState n) : Prop :=
  s.activeIds = t.activeIds ∧ s.inactive = t.inactive

end InfectionIdentityState

theorem infectionRevealOneLabelPMF_eq_of_activeOnlyCompatible
    {n : ℕ} {s t : InfectionIdentityState n}
    (hst : s.ActiveOnlyCompatible t)
    (hs : Nonempty (InfectionInactiveId s.inactive))
    (ht : Nonempty (InfectionInactiveId t.inactive)) :
    infectionRevealOneLabelPMF s.inactive hs =
      infectionRevealOneLabelPMF t.inactive ht :=
  infectionRevealOneLabelPMF_congr hst.2 hs ht

theorem infectionRevealTwoLabelPMF_eq_of_activeOnlyCompatible
    {n : ℕ} {s t : InfectionIdentityState n}
    (hst : s.ActiveOnlyCompatible t)
    (hs : Nonempty (InfectionOrderedRevealTwo s.inactive))
    (ht : Nonempty (InfectionOrderedRevealTwo t.inactive)) :
    infectionRevealTwoLabelPMF s.inactive hs =
      infectionRevealTwoLabelPMF t.inactive ht :=
  infectionRevealTwoLabelPMF_congr hst.2 hs ht

end Tri

#print axioms Tri.infectionIdentityForget_active
#print axioms Tri.infectionIdentityForget_inactive
#print axioms Tri.infectionRevealOne_exchangeable
#print axioms Tri.infectionRevealTwo_exchangeable
#print axioms Tri.infectionRevealTwo_ne
#print axioms Tri.infectionRevealOneLabelPMF_eq_of_activeOnlyCompatible
#print axioms Tri.infectionRevealTwoLabelPMF_eq_of_activeOnlyCompatible
