/-
Ripple.BoundedUniversality.BGP.SelectorGates
------------------------
Gate-layer realization of SEL1 selector weights.

Design note status:
`notes/gpt-life-p13-encoding.md` is not present in this checkout.  The
construction below follows the checked-in SEL1 interface in
`SelectorPolynomial.lean` and the local-view coordinates exported by
`StackEncoding.lean`.

The atom layer is kept as a rational-polynomial package with explicit
sharpness hypotheses.  This is the Lean-cheapest boundary for plugging in the
dynamic/Bernstein machinery: `BernsteinSeparator.rational_bernstein_separator`
currently provides existential rational separators, while SEL1 only needs the
resulting working-domain range/on/off clauses.  View selectors are products of
the three atomic selectors: control, left top class, and right top class.
-/

import Ripple.BoundedUniversality.BGP.SelectorPolynomial
import Ripple.BoundedUniversality.BGP.StackEncoding

namespace Ripple.BoundedUniversality.BGP

open BigOperators
open Ripple.BoundedUniversality.Core

noncomputable section

/-! ## Atomic rational-polynomial selectors -/

/-- Dimension-parameterized rational multivariate polynomials. -/
abbrev Poly4 (d : ℕ) : Type := MvPolynomial (Fin d) ℚ

/-- Real evaluation of a dimension-parameterized rational polynomial. -/
def evalPoly4 {d : ℕ} (Z : Fin d → ℝ) (P : Poly4 d) : ℝ :=
  MvPolynomial.eval₂ (algebraMap ℚ ℝ) Z P

/--
An atomic selector family over a discrete label type.  The family is a
rational-polynomial realization, together with the working-domain range and
error constant supplied by the dynamic/Bernstein sharpening layer.
-/
structure AtomicSelectorData (d : ℕ) (A : Type) where
  poly : A → Poly4 d
  err : ℝ
  err_nonneg : 0 ≤ err
  domain : (Fin d → ℝ) → Prop
  range : ∀ a Z, domain Z → 0 ≤ evalPoly4 Z (poly a) ∧ evalPoly4 Z (poly a) ≤ 1

/-- A finite local view is determined by a control value and two stack-top classes. -/
structure GateViewSpec (V : Type) where
  q : V → ℤ
  leftTop : V → Option (Fin 2)
  rightTop : V → Option (Fin 2)
  ext :
    ∀ {v w : V}, q v = q w → leftTop v = leftTop w →
      rightTop v = rightTop w → v = w

/-- The three atom families used by the gate selector. -/
structure GateSelectorAtoms (d : ℕ) where
  control : AtomicSelectorData d ℤ
  left : AtomicSelectorData d (Option (Fin 2))
  right : AtomicSelectorData d (Option (Fin 2))

namespace GateSelectorAtoms

/-- The working domain on which all three atom families have `[0,1]` range. -/
def inWorkingDomain {d : ℕ} (A : GateSelectorAtoms d) (Z : Fin d → ℝ) : Prop :=
  A.control.domain Z ∧ A.left.domain Z ∧ A.right.domain Z

/-- Product-selector true-view error: one additive atom error per factor. -/
def errSel {d : ℕ} (A : GateSelectorAtoms d) : ℝ :=
  A.control.err + A.left.err + A.right.err

/-- Product-selector off-view error: the largest atom off-error. -/
def errOff {d : ℕ} (A : GateSelectorAtoms d) : ℝ :=
  max A.control.err (max A.left.err A.right.err)

/-- Sum-to-one error propagated from one true selector and all off selectors. -/
def errSum {d : ℕ} (V : Type) [Fintype V] (A : GateSelectorAtoms d) : ℝ :=
  errSel A + offViewCount V * errOff A

theorem errSel_nonneg {d : ℕ} (A : GateSelectorAtoms d) : 0 ≤ A.errSel := by
  unfold errSel
  exact add_nonneg (add_nonneg A.control.err_nonneg A.left.err_nonneg)
    A.right.err_nonneg

theorem errOff_nonneg {d : ℕ} (A : GateSelectorAtoms d) : 0 ≤ A.errOff := by
  unfold errOff
  exact le_max_of_le_left A.control.err_nonneg

theorem errSum_nonneg {d : ℕ} (V : Type) [Fintype V] (A : GateSelectorAtoms d) :
    0 ≤ A.errSum V := by
  unfold errSum
  exact add_nonneg A.errSel_nonneg
    (mul_nonneg (by simp [offViewCount]) A.errOff_nonneg)

end GateSelectorAtoms

/--
Sharpness clauses for the three atomic selectors at one selected view and one
input point.  The tube/local-extraction/Bernstein layer is expected to supply
these clauses; this file proves the product propagation into SEL1.
-/
structure GateAtomSharpness {d : ℕ} {V : Type} (spec : GateViewSpec V)
    (atoms : GateSelectorAtoms d) (Z : Fin d → ℝ) (vstar : V) : Prop where
  control_on :
    1 - atoms.control.err ≤ evalPoly4 Z (atoms.control.poly (spec.q vstar))
  left_on :
    1 - atoms.left.err ≤ evalPoly4 Z (atoms.left.poly (spec.leftTop vstar))
  right_on :
    1 - atoms.right.err ≤ evalPoly4 Z (atoms.right.poly (spec.rightTop vstar))
  control_off :
    ∀ v, spec.q v ≠ spec.q vstar →
      evalPoly4 Z (atoms.control.poly (spec.q v)) ≤ atoms.control.err
  left_off :
    ∀ v, spec.leftTop v ≠ spec.leftTop vstar →
      evalPoly4 Z (atoms.left.poly (spec.leftTop v)) ≤ atoms.left.err
  right_off :
    ∀ v, spec.rightTop v ≠ spec.rightTop vstar →
      evalPoly4 Z (atoms.right.poly (spec.rightTop v)) ≤ atoms.right.err

/-! ## View selector products -/

/-- Product selector polynomial for one view. -/
def viewSelectorPoly {d : ℕ} {V : Type} (spec : GateViewSpec V)
    (atoms : GateSelectorAtoms d) (v : V) : Poly4 d :=
  atoms.control.poly (spec.q v) *
    atoms.left.poly (spec.leftTop v) *
      atoms.right.poly (spec.rightTop v)

/-- Evaluated selector weight `Lambda_v(Z)`. -/
def Lambda {d : ℕ} {V : Type} (spec : GateViewSpec V)
    (atoms : GateSelectorAtoms d) (Z : Fin d → ℝ) (v : V) : ℝ :=
  evalPoly4 Z (viewSelectorPoly spec atoms v)

@[simp] theorem eval_viewSelectorPoly {d : ℕ} {V : Type} (spec : GateViewSpec V)
    (atoms : GateSelectorAtoms d) (Z : Fin d → ℝ) (v : V) :
    evalPoly4 Z (viewSelectorPoly spec atoms v) =
      evalPoly4 Z (atoms.control.poly (spec.q v)) *
        evalPoly4 Z (atoms.left.poly (spec.leftTop v)) *
          evalPoly4 Z (atoms.right.poly (spec.rightTop v)) := by
  simp [evalPoly4, viewSelectorPoly]

private theorem product_true_lower
    {a b c ea eb ec : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (_hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (_hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (ha : 1 - ea ≤ a) (hb : 1 - eb ≤ b) (hc : 1 - ec ≤ c) :
    1 - (ea + eb + ec) ≤ a * b * c := by
  have h1a : 1 - a ≤ ea := by linarith
  have h1b : 1 - b ≤ eb := by linarith
  have h1c : 1 - c ≤ ec := by linarith
  have h1b_nonneg : 0 ≤ 1 - b := by linarith
  have h1c_nonneg : 0 ≤ 1 - c := by linarith
  have hab_le_one : a * b ≤ 1 := by nlinarith
  have hterm_b : a * (1 - b) ≤ eb := by
    calc
      a * (1 - b) ≤ 1 * eb :=
        mul_le_mul ha1 h1b h1b_nonneg (by norm_num)
      _ = eb := by ring
  have hterm_c : a * b * (1 - c) ≤ ec := by
    calc
      a * b * (1 - c) ≤ 1 * ec :=
        mul_le_mul hab_le_one h1c h1c_nonneg (by norm_num)
      _ = ec := by ring
  have hdecomp :
      1 - a * b * c = (1 - a) + a * (1 - b) + a * b * (1 - c) := by
    ring
  have hupper : 1 - a * b * c ≤ ea + eb + ec := by
    rw [hdecomp]
    linarith
  linarith

private theorem mul3_le_of_first_le
    {a b c e : ℝ} (ha0 : 0 ≤ a) (hae : a ≤ e)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    a * b * c ≤ e := by
  have he0 : 0 ≤ e := le_trans ha0 hae
  have hab : a * b ≤ e := by
    calc
      a * b ≤ e * 1 := mul_le_mul hae hb1 hb0 he0
      _ = e := by ring
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  calc
    a * b * c ≤ e * 1 := mul_le_mul hab hc1 hc0 he0
    _ = e := by ring

private theorem mul3_le_of_second_le
    {a b c e : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hbe : b ≤ e)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    a * b * c ≤ e := by
  have he0 : 0 ≤ e := le_trans hb0 hbe
  have hab : a * b ≤ e := by
    calc
      a * b ≤ 1 * e := mul_le_mul ha1 hbe hb0 (by norm_num)
      _ = e := by ring
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  calc
    a * b * c ≤ e * 1 := mul_le_mul hab hc1 hc0 he0
    _ = e := by ring

private theorem mul3_le_of_third_le
    {a b c e : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hce : c ≤ e) :
    a * b * c ≤ e := by
  have he0 : 0 ≤ e := le_trans hc0 hce
  have hab : a * b ≤ 1 := by
    calc
      a * b ≤ 1 * 1 := mul_le_mul ha1 hb1 hb0 (by norm_num)
      _ = 1 := by ring
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  calc
    a * b * c ≤ 1 * e := mul_le_mul hab hce hc0 (by norm_num)
    _ = e := by ring

/-- Weierstrass-style product lower bound over a Finset: if every factor lies in
`[0,1]`, the product is at least `1` minus the sum of the per-factor defects. -/
theorem prod_one_sub_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, (1 - f i) ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert k s hk ih =>
      have h0' : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have h1' : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      have hfk0 : 0 ≤ f k := h0 k (Finset.mem_insert_self k s)
      have hfk1 : f k ≤ 1 := h1 k (Finset.mem_insert_self k s)
      have hprod_s : 1 - ∑ i ∈ s, (1 - f i) ≤ ∏ i ∈ s, f i := ih h0' h1'
      have hsum_nonneg : 0 ≤ ∑ i ∈ s, (1 - f i) :=
        Finset.sum_nonneg (fun i hi => by have := h1' i hi; linarith)
      have hprod_nonneg : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg h0'
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      have hstep : f k * (1 - ∑ i ∈ s, (1 - f i)) ≤ f k * ∏ i ∈ s, f i :=
        mul_le_mul_of_nonneg_left hprod_s hfk0
      nlinarith [hsum_nonneg, hprod_nonneg, hfk0, hfk1, hstep]

/-- Product upper bound over a Finset: if some factor is `≤ e` and every factor
lies in `[0,1]`, the whole product is `≤ e`. -/
theorem prod_le_of_mem_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {e : ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1)
    {k : ι} (hk : k ∈ s) (hke : f k ≤ e) (he : 0 ≤ e) :
    ∏ i ∈ s, f i ≤ e := by
  classical
  rw [← Finset.prod_erase_mul s f hk]
  have herase_le_one : ∏ i ∈ s.erase k, f i ≤ 1 :=
    Finset.prod_le_one (fun i hi => h0 i (Finset.mem_of_mem_erase hi))
      (fun i hi => h1 i (Finset.mem_of_mem_erase hi))
  have herase_nonneg : 0 ≤ ∏ i ∈ s.erase k, f i :=
    Finset.prod_nonneg (fun i hi => h0 i (Finset.mem_of_mem_erase hi))
  calc
    (∏ i ∈ s.erase k, f i) * f k ≤ 1 * e :=
      mul_le_mul herase_le_one hke (h0 k hk) (by norm_num)
    _ = e := by ring

private theorem viewSelector_range {d : ℕ} {V : Type} (spec : GateViewSpec V)
    (atoms : GateSelectorAtoms d) (Z : Fin d → ℝ)
    (hZ : atoms.inWorkingDomain Z) (v : V) :
    0 ≤ Lambda spec atoms Z v ∧ Lambda spec atoms Z v ≤ 1 := by
  let a := evalPoly4 Z (atoms.control.poly (spec.q v))
  let b := evalPoly4 Z (atoms.left.poly (spec.leftTop v))
  let c := evalPoly4 Z (atoms.right.poly (spec.rightTop v))
  have ha := atoms.control.range (spec.q v) Z hZ.1
  have hb := atoms.left.range (spec.leftTop v) Z hZ.2.1
  have hc := atoms.right.range (spec.rightTop v) Z hZ.2.2
  have hval : Lambda spec atoms Z v = a * b * c := by
    simp [Lambda, a, b, c]
  constructor
  · rw [hval]
    exact mul_nonneg (mul_nonneg ha.1 hb.1) hc.1
  · rw [hval]
    exact mul3_le_of_third_le ha.1 ha.2 hb.1 hb.2 hc.1 hc.2

private theorem viewSelector_true_lower {d : ℕ} {V : Type} (spec : GateViewSpec V)
    (atoms : GateSelectorAtoms d) (Z : Fin d → ℝ) (vstar : V)
    (hZ : atoms.inWorkingDomain Z)
    (hsharp : GateAtomSharpness spec atoms Z vstar) :
    1 - atoms.errSel ≤ Lambda spec atoms Z vstar := by
  let a := evalPoly4 Z (atoms.control.poly (spec.q vstar))
  let b := evalPoly4 Z (atoms.left.poly (spec.leftTop vstar))
  let c := evalPoly4 Z (atoms.right.poly (spec.rightTop vstar))
  have ha := atoms.control.range (spec.q vstar) Z hZ.1
  have hb := atoms.left.range (spec.leftTop vstar) Z hZ.2.1
  have hc := atoms.right.range (spec.rightTop vstar) Z hZ.2.2
  have hprod :
      1 - (atoms.control.err + atoms.left.err + atoms.right.err) ≤
        a * b * c :=
    product_true_lower ha.1 ha.2 hb.1 hb.2 hc.1 hc.2
      (by simpa [a] using hsharp.control_on)
      (by simpa [b] using hsharp.left_on)
      (by simpa [c] using hsharp.right_on)
  simpa [GateSelectorAtoms.errSel, Lambda, a, b, c] using hprod

private theorem viewSelector_off_upper {d : ℕ} {V : Type} (spec : GateViewSpec V)
    (atoms : GateSelectorAtoms d) (Z : Fin d → ℝ) (vstar v : V)
    (hZ : atoms.inWorkingDomain Z)
    (hsharp : GateAtomSharpness spec atoms Z vstar)
    (hv : v ≠ vstar) :
    Lambda spec atoms Z v ≤ atoms.errOff := by
  let a := evalPoly4 Z (atoms.control.poly (spec.q v))
  let b := evalPoly4 Z (atoms.left.poly (spec.leftTop v))
  let c := evalPoly4 Z (atoms.right.poly (spec.rightTop v))
  have ha := atoms.control.range (spec.q v) Z hZ.1
  have hb := atoms.left.range (spec.leftTop v) Z hZ.2.1
  have hc := atoms.right.range (spec.rightTop v) Z hZ.2.2
  have hdiff :
      spec.q v ≠ spec.q vstar ∨
        spec.leftTop v ≠ spec.leftTop vstar ∨
          spec.rightTop v ≠ spec.rightTop vstar := by
    by_contra h
    push Not at h
    exact hv (spec.ext h.1 h.2.1 h.2.2)
  have hval : Lambda spec atoms Z v = a * b * c := by
    simp [Lambda, a, b, c]
  rcases hdiff with hq | hl | hr
  · have hle : a * b * c ≤ atoms.control.err :=
      mul3_le_of_first_le ha.1 (by simpa [a] using hsharp.control_off v hq)
        hb.1 hb.2 hc.1 hc.2
    rw [hval]
    exact hle.trans (le_max_left _ _)
  · have hle : a * b * c ≤ atoms.left.err :=
      mul3_le_of_second_le ha.1 ha.2 hb.1
        (by simpa [b] using hsharp.left_off v hl) hc.1 hc.2
    rw [hval]
    exact hle.trans ((le_max_left _ _).trans (le_max_right _ _))
  · have hle : a * b * c ≤ atoms.right.err :=
      mul3_le_of_third_le ha.1 ha.2 hb.1 hb.2 hc.1
        (by simpa [c] using hsharp.right_off v hr)
    rw [hval]
    exact hle.trans ((le_max_right _ _).trans (le_max_right _ _))

private theorem gate_sum_off_eq_sub_singleton
    {V : Type} [Fintype V] [DecidableEq V] (vstar : V) (f : V → ℝ) :
    (Finset.univ.filter (fun v : V => v ≠ vstar)).sum f =
      (∑ v : V, f v) - f vstar := by
  have hset :
      Finset.univ.filter (fun v : V => v ≠ vstar) =
        (Finset.univ : Finset V).erase vstar := by
    ext v
    by_cases h : v = vstar <;> simp [h]
  rw [hset, Finset.sum_erase_eq_sub]
  simp

private theorem gate_off_card_le
    {V : Type} [Fintype V] [DecidableEq V] (vstar : V) :
    ((Finset.univ.filter (fun v : V => v ≠ vstar)).card : ℝ) ≤
      offViewCount V := by
  have hset :
      Finset.univ.filter (fun v : V => v ≠ vstar) =
        (Finset.univ : Finset V).erase vstar := by
    ext v
    by_cases h : v = vstar <;> simp [h]
  have hcard :
      (Finset.univ.filter (fun v : V => v ≠ vstar)).card =
        Fintype.card V - 1 := by
    rw [hset, Finset.card_erase_of_mem (by simp : vstar ∈ (Finset.univ : Finset V))]
    simp
  simp [offViewCount, hcard]

/--
The product-form gate selectors satisfy exactly the selector hypotheses used by
SEL1: selected-view lower bound, off-view upper/nonnegativity, and sum-to-one
error with explicit constants.
-/
structure GateSelectorSEL1Hypotheses
    {V : Type} [Fintype V] (Λ : V → ℝ) (vstar : V)
    (errSel errOff errSum : ℝ) : Prop where
  errSel_nonneg : 0 ≤ errSel
  errOff_nonneg : 0 ≤ errOff
  hsum : |(∑ v : V, Λ v) - 1| ≤ errSum
  htrue : 1 - errSel ≤ Λ vstar
  hoff : ∀ v, v ≠ vstar → 0 ≤ Λ v ∧ Λ v ≤ errOff

theorem gate_view_selectors_SEL1_hypotheses
    {d : ℕ} {V : Type} [Fintype V] [DecidableEq V]
    (spec : GateViewSpec V) (atoms : GateSelectorAtoms d)
    (Z : Fin d → ℝ) (vstar : V)
    (hZ : atoms.inWorkingDomain Z)
    (hsharp : GateAtomSharpness spec atoms Z vstar) :
    GateSelectorSEL1Hypotheses
      (Lambda spec atoms Z) vstar atoms.errSel atoms.errOff (atoms.errSum V) := by
  classical
  refine ⟨atoms.errSel_nonneg, atoms.errOff_nonneg, ?_, ?_, ?_⟩
  · let Λ : V → ℝ := Lambda spec atoms Z
    have htrue : 1 - atoms.errSel ≤ Λ vstar :=
      viewSelector_true_lower spec atoms Z vstar hZ hsharp
    have hnonneg : ∀ v, 0 ≤ Λ v := fun v => (viewSelector_range spec atoms Z hZ v).1
    have hle_one : Λ vstar ≤ 1 := (viewSelector_range spec atoms Z hZ vstar).2
    have hoffle : ∀ v, v ≠ vstar → Λ v ≤ atoms.errOff :=
      fun v hv => viewSelector_off_upper spec atoms Z vstar v hZ hsharp hv
    have hsum_lower : 1 - atoms.errSel ≤ ∑ v : V, Λ v := by
      calc
        1 - atoms.errSel ≤ Λ vstar := htrue
        _ ≤ ∑ v : V, Λ v :=
          Finset.single_le_sum (fun v _ => hnonneg v) (by simp)
    have hoff_sum :
        (Finset.univ.filter (fun v : V => v ≠ vstar)).sum Λ ≤
          offViewCount V * atoms.errOff := by
      calc
        (Finset.univ.filter (fun v : V => v ≠ vstar)).sum Λ
            ≤ (Finset.univ.filter (fun v : V => v ≠ vstar)).sum
                (fun _ => atoms.errOff) := by
              refine Finset.sum_le_sum (fun v hv => ?_)
              exact hoffle v (by simpa using (Finset.mem_filter.mp hv).2)
        _ = ((Finset.univ.filter (fun v : V => v ≠ vstar)).card : ℝ) *
              atoms.errOff := by simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ offViewCount V * atoms.errOff :=
              mul_le_mul_of_nonneg_right (gate_off_card_le vstar) atoms.errOff_nonneg
    have hsplit :
        ∑ v : V, Λ v =
          Λ vstar + (Finset.univ.filter (fun v : V => v ≠ vstar)).sum Λ := by
      have h := gate_sum_off_eq_sub_singleton vstar Λ
      linarith
    have hsum_upper :
        (∑ v : V, Λ v) - 1 ≤ offViewCount V * atoms.errOff := by
      calc
        (∑ v : V, Λ v) - 1 =
            (Λ vstar - 1) +
              (Finset.univ.filter (fun v : V => v ≠ vstar)).sum Λ := by
              rw [hsplit]
              ring
        _ ≤ 0 + offViewCount V * atoms.errOff := by
              exact add_le_add (by linarith) hoff_sum
        _ = offViewCount V * atoms.errOff := by ring
    rw [abs_le]
    constructor
    · have hleft : -atoms.errSel ≤ (∑ v : V, Λ v) - 1 := by linarith
      have hoff_nonneg : 0 ≤ offViewCount V * atoms.errOff :=
        mul_nonneg (by simp [offViewCount]) atoms.errOff_nonneg
      unfold GateSelectorAtoms.errSum
      linarith
    · unfold GateSelectorAtoms.errSum
      have herrSel_nonneg := atoms.errSel_nonneg
      linarith
  · exact viewSelector_true_lower spec atoms Z vstar hZ hsharp
  · intro v hv
    exact ⟨(viewSelector_range spec atoms Z hZ v).1,
      viewSelector_off_upper spec atoms Z vstar v hZ hsharp hv⟩

/-! ## N-atom generalization of the gate selector -/

/-- `evalPoly4` distributes over finite products (it is a ring homomorphism). -/
theorem evalPoly4_prod {d : ℕ} (Z : Fin d → ℝ) {ι : Type*} (s : Finset ι)
    (f : ι → Poly4 d) :
    evalPoly4 Z (∏ i ∈ s, f i) = ∏ i ∈ s, evalPoly4 Z (f i) := by
  show (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) Z) (∏ i ∈ s, f i) =
    ∏ i ∈ s, (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) Z) (f i)
  exact map_prod _ _ _

/-- An `n`-component finite local view, each component a `ℤ` code. -/
structure GateViewSpecN (V : Type) (n : ℕ) where
  comp : Fin n → V → ℤ
  ext : ∀ {v w : V}, (∀ k, comp k v = comp k w) → v = w

/-- An `n`-family of atom selectors, one per view component. -/
structure GateSelectorAtomsN (d n : ℕ) where
  atom : Fin n → AtomicSelectorData d ℤ

namespace GateSelectorAtomsN

variable {d n : ℕ}

def inWorkingDomain (A : GateSelectorAtomsN d n) (Z : Fin d → ℝ) : Prop :=
  ∀ k, (A.atom k).domain Z

/-- Summed per-atom error; also serves as the (loose) off-view bound. -/
def errSel (A : GateSelectorAtomsN d n) : ℝ := ∑ k, (A.atom k).err

theorem errSel_nonneg (A : GateSelectorAtomsN d n) : 0 ≤ A.errSel :=
  Finset.sum_nonneg (fun k _ => (A.atom k).err_nonneg)

def errSum (V : Type) [Fintype V] (A : GateSelectorAtomsN d n) : ℝ :=
  A.errSel + offViewCount V * A.errSel

theorem errSum_nonneg (V : Type) [Fintype V] (A : GateSelectorAtomsN d n) :
    0 ≤ A.errSum V := by
  unfold errSum
  exact add_nonneg A.errSel_nonneg
    (mul_nonneg (by simp [offViewCount]) A.errSel_nonneg)

end GateSelectorAtomsN

/-- Sharpness of the `n`-atom family at the true view. -/
structure GateAtomSharpnessN {d n : ℕ} {V : Type} (spec : GateViewSpecN V n)
    (atoms : GateSelectorAtomsN d n) (Z : Fin d → ℝ) (vstar : V) : Prop where
  on : ∀ k, 1 - (atoms.atom k).err ≤
    evalPoly4 Z ((atoms.atom k).poly (spec.comp k vstar))
  off : ∀ k v, spec.comp k v ≠ spec.comp k vstar →
    evalPoly4 Z ((atoms.atom k).poly (spec.comp k v)) ≤ (atoms.atom k).err

/-- Product selector polynomial over the `n` atoms. -/
def viewSelectorPolyN {d n : ℕ} {V : Type} (spec : GateViewSpecN V n)
    (atoms : GateSelectorAtomsN d n) (v : V) : Poly4 d :=
  ∏ k, (atoms.atom k).poly (spec.comp k v)

/-- Evaluated `n`-atom selector weight. -/
def LambdaN {d n : ℕ} {V : Type} (spec : GateViewSpecN V n)
    (atoms : GateSelectorAtomsN d n) (Z : Fin d → ℝ) (v : V) : ℝ :=
  evalPoly4 Z (viewSelectorPolyN spec atoms v)

theorem LambdaN_factor {d n : ℕ} {V : Type} (spec : GateViewSpecN V n)
    (atoms : GateSelectorAtomsN d n) (Z : Fin d → ℝ) (v : V) :
    LambdaN spec atoms Z v =
      ∏ k, evalPoly4 Z ((atoms.atom k).poly (spec.comp k v)) := by
  simp only [LambdaN, viewSelectorPolyN]
  exact evalPoly4_prod Z _ _

private theorem viewSelectorN_range {d n : ℕ} {V : Type} (spec : GateViewSpecN V n)
    (atoms : GateSelectorAtomsN d n) (Z : Fin d → ℝ)
    (hZ : atoms.inWorkingDomain Z) (v : V) :
    0 ≤ LambdaN spec atoms Z v ∧ LambdaN spec atoms Z v ≤ 1 := by
  rw [LambdaN_factor]
  constructor
  · exact Finset.prod_nonneg (fun k _ => ((atoms.atom k).range (spec.comp k v) Z (hZ k)).1)
  · exact Finset.prod_le_one (fun k _ => ((atoms.atom k).range (spec.comp k v) Z (hZ k)).1)
      (fun k _ => ((atoms.atom k).range (spec.comp k v) Z (hZ k)).2)

private theorem viewSelectorN_true_lower {d n : ℕ} {V : Type} (spec : GateViewSpecN V n)
    (atoms : GateSelectorAtomsN d n) (Z : Fin d → ℝ) (vstar : V)
    (hZ : atoms.inWorkingDomain Z) (hsharp : GateAtomSharpnessN spec atoms Z vstar) :
    1 - atoms.errSel ≤ LambdaN spec atoms Z vstar := by
  rw [LambdaN_factor]
  have hbound :
      1 - ∑ k, (1 - evalPoly4 Z ((atoms.atom k).poly (spec.comp k vstar))) ≤
        ∏ k, evalPoly4 Z ((atoms.atom k).poly (spec.comp k vstar)) :=
    prod_one_sub_le _ _
      (fun k _ => ((atoms.atom k).range (spec.comp k vstar) Z (hZ k)).1)
      (fun k _ => ((atoms.atom k).range (spec.comp k vstar) Z (hZ k)).2)
  have hsum_le : ∑ k, (1 - evalPoly4 Z ((atoms.atom k).poly (spec.comp k vstar))) ≤
      atoms.errSel := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    have := hsharp.on k
    linarith
  linarith

private theorem viewSelectorN_off_upper {d n : ℕ} {V : Type} (spec : GateViewSpecN V n)
    (atoms : GateSelectorAtomsN d n) (Z : Fin d → ℝ) (vstar v : V)
    (hZ : atoms.inWorkingDomain Z) (hsharp : GateAtomSharpnessN spec atoms Z vstar)
    (hv : v ≠ vstar) :
    LambdaN spec atoms Z v ≤ atoms.errSel := by
  rw [LambdaN_factor]
  obtain ⟨k, hk⟩ : ∃ k, spec.comp k v ≠ spec.comp k vstar := by
    by_contra h
    push_neg at h
    exact hv (spec.ext h)
  have hke : evalPoly4 Z ((atoms.atom k).poly (spec.comp k v)) ≤ (atoms.atom k).err :=
    hsharp.off k v hk
  have herr_le : (atoms.atom k).err ≤ atoms.errSel :=
    Finset.single_le_sum (fun j _ => (atoms.atom j).err_nonneg) (Finset.mem_univ k)
  refine le_trans (prod_le_of_mem_le _ _
    (fun j _ => ((atoms.atom j).range (spec.comp j v) Z (hZ j)).1)
    (fun j _ => ((atoms.atom j).range (spec.comp j v) Z (hZ j)).2)
    (Finset.mem_univ k) hke (le_trans (atoms.atom k).err_nonneg le_rfl)) herr_le

/-- N-atom analogue of `gate_view_selectors_SEL1_hypotheses`. -/
theorem gate_view_selectorsN_SEL1_hypotheses
    {d n : ℕ} {V : Type} [Fintype V] [DecidableEq V]
    (spec : GateViewSpecN V n) (atoms : GateSelectorAtomsN d n)
    (Z : Fin d → ℝ) (vstar : V)
    (hZ : atoms.inWorkingDomain Z)
    (hsharp : GateAtomSharpnessN spec atoms Z vstar) :
    GateSelectorSEL1Hypotheses
      (LambdaN spec atoms Z) vstar atoms.errSel atoms.errSel (atoms.errSum V) := by
  classical
  refine ⟨atoms.errSel_nonneg, atoms.errSel_nonneg, ?_, ?_, ?_⟩
  · let Λ : V → ℝ := LambdaN spec atoms Z
    have htrue : 1 - atoms.errSel ≤ Λ vstar :=
      viewSelectorN_true_lower spec atoms Z vstar hZ hsharp
    have hnonneg : ∀ v, 0 ≤ Λ v := fun v => (viewSelectorN_range spec atoms Z hZ v).1
    have hle_one : Λ vstar ≤ 1 := (viewSelectorN_range spec atoms Z hZ vstar).2
    have hoffle : ∀ v, v ≠ vstar → Λ v ≤ atoms.errSel :=
      fun v hv => viewSelectorN_off_upper spec atoms Z vstar v hZ hsharp hv
    have hsum_lower : 1 - atoms.errSel ≤ ∑ v : V, Λ v := by
      calc
        1 - atoms.errSel ≤ Λ vstar := htrue
        _ ≤ ∑ v : V, Λ v := Finset.single_le_sum (fun v _ => hnonneg v) (by simp)
    have hoff_sum :
        (Finset.univ.filter (fun v : V => v ≠ vstar)).sum Λ ≤
          offViewCount V * atoms.errSel := by
      calc
        (Finset.univ.filter (fun v : V => v ≠ vstar)).sum Λ
            ≤ (Finset.univ.filter (fun v : V => v ≠ vstar)).sum (fun _ => atoms.errSel) := by
              refine Finset.sum_le_sum (fun v hv => ?_)
              exact hoffle v (by simpa using (Finset.mem_filter.mp hv).2)
        _ = ((Finset.univ.filter (fun v : V => v ≠ vstar)).card : ℝ) * atoms.errSel := by
              simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ offViewCount V * atoms.errSel :=
              mul_le_mul_of_nonneg_right (gate_off_card_le vstar) atoms.errSel_nonneg
    have hsplit :
        ∑ v : V, Λ v =
          Λ vstar + (Finset.univ.filter (fun v : V => v ≠ vstar)).sum Λ := by
      have h := gate_sum_off_eq_sub_singleton vstar Λ
      linarith
    have hsum_upper : (∑ v : V, Λ v) - 1 ≤ offViewCount V * atoms.errSel := by
      calc
        (∑ v : V, Λ v) - 1 =
            (Λ vstar - 1) + (Finset.univ.filter (fun v : V => v ≠ vstar)).sum Λ := by
              rw [hsplit]; ring
        _ ≤ 0 + offViewCount V * atoms.errSel :=
              add_le_add (by linarith) hoff_sum
        _ = offViewCount V * atoms.errSel := by ring
    rw [abs_le]
    have hoff_nonneg : 0 ≤ offViewCount V * atoms.errSel :=
      mul_nonneg (by simp [offViewCount]) atoms.errSel_nonneg
    constructor
    · unfold GateSelectorAtomsN.errSum; linarith
    · unfold GateSelectorAtomsN.errSum
      have := atoms.errSel_nonneg; linarith
  · exact viewSelectorN_true_lower spec atoms Z vstar hZ hsharp
  · exact fun v hv =>
      ⟨(viewSelectorN_range spec atoms Z hZ v).1,
        viewSelectorN_off_upper spec atoms Z vstar v hZ hsharp hv⟩

/-! ## Total polynomial and SEL1 composition -/

/--
The concrete rational-polynomial field obtained by substituting the product
selectors into the branch reassembly.
-/
def selectorTotalPoly
    {d : ℕ} {V : Type} [Fintype V] {B : ℕ}
    (branch : V → BranchData d B) (spec : GateViewSpec V)
    (atoms : GateSelectorAtoms d) (i : Fin d) : Poly4 d :=
  ∑ v : V, viewSelectorPoly spec atoms v * BranchData.branchPoly (branch v) i

/-- `selectorTotalPoly` is a rational multivariate polynomial by construction. -/
theorem selectorTotalPoly_polynomial
    {d : ℕ} {V : Type} [Fintype V] {B : ℕ}
    (branch : V → BranchData d B) (spec : GateViewSpec V)
    (atoms : GateSelectorAtoms d) (i : Fin d) :
    ∃ P : Poly4 d, P = selectorTotalPoly branch spec atoms i := by
  exact ⟨selectorTotalPoly branch spec atoms i, rfl⟩

@[simp] theorem eval_selectorTotalPoly
    {d : ℕ} {V : Type} [Fintype V] {B : ℕ}
    (branch : V → BranchData d B) (spec : GateViewSpec V)
    (atoms : GateSelectorAtoms d) (Z : Fin d → ℝ) (i : Fin d) :
    evalPoly4 Z (selectorTotalPoly branch spec atoms i) =
      selectorF branch Z (Lambda spec atoms Z) i := by
  classical
  simp [selectorTotalPoly, selectorF, Lambda, evalPoly4]

/-- Gate selectors plus SEL1 reassembly give the branch-value error bound. -/
theorem gate_selector_reassembly
    {d : ℕ} {V : Type} [Fintype V] [DecidableEq V] {B : ℕ}
    (branch : V → BranchData d B) (spec : GateViewSpec V)
    (atoms : GateSelectorAtoms d) (Z : Fin d → ℝ) (vstar : V)
    (i : Fin d) {spread : ℝ}
    (hZ : atoms.inWorkingDomain Z)
    (hsharp : GateAtomSharpness spec atoms Z vstar)
    (hspread : BranchSpread branch Z vstar i spread) :
    |evalPoly4 Z (selectorTotalPoly branch spec atoms i) -
        BranchData.evalBranch (branch vstar) Z i| ≤
      selectorReassemblyCoeff (V := V)
        atoms.errSel atoms.errOff (atoms.errSum V) * spread := by
  classical
  have hsel := gate_view_selectors_SEL1_hypotheses spec atoms Z vstar hZ hsharp
  rw [eval_selectorTotalPoly]
  exact selector_reassembly branch Z (Lambda spec atoms Z) vstar i
    hsel.errSel_nonneg hsel.errOff_nonneg hsel.hsum hsel.htrue hsel.hoff hspread

/--
Composed SEL2/S3 coordinate clause: the single rational polynomial
`selectorTotalPoly` satisfies SEL1's variable-`mu` diagonal clause once the
atom-sharpness package supplies the selector bounds.
-/
theorem gate_selector_varMu_coord_clause
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {E : StackMachineEncoding d nS M}
    {V : Type} [Fintype V] [DecidableEq V]
    (branch : V → BranchData d E.k) (spec : GateViewSpec V)
    (atoms : GateSelectorAtoms d) (Z : Fin d → ℝ)
    (c : Conf) (vstar : V) (i : Fin d)
    {spread theta : ℝ}
    (hZ : atoms.inWorkingDomain Z)
    (hsharp : GateAtomSharpness spec atoms Z vstar)
    (htheta :
      selectorEpsTotal (V := V) atoms.errSel atoms.errOff (atoms.errSum V) spread ≤
        theta)
    (hspread : BranchSpread branch Z vstar i spread)
    (hcontract : BranchContractClause E c (branch vstar)) :
    |evalPoly4 Z (selectorTotalPoly branch spec atoms i) -
        E.enc (M.step c) i| ≤
      (E.k : ℝ) ^ E.coordDelta c i * |Z i - E.enc c i| + theta := by
  classical
  have hsel := gate_view_selectors_SEL1_hypotheses spec atoms Z vstar hZ hsharp
  rw [eval_selectorTotalPoly]
  exact selector_varMu_coord_clause branch Z (Lambda spec atoms Z) c vstar i
    hsel.errSel_nonneg hsel.errOff_nonneg htheta
    hsel.hsum hsel.htrue hsel.hoff hspread hcontract

/-! ## N-atom total polynomial and SEL1 composition -/

/-- Product-selector reassembly polynomial for the `n`-atom gate family. -/
def selectorTotalPolyN
    {d n : ℕ} {V : Type} [Fintype V] {B : ℕ}
    (branch : V → BranchData d B) (spec : GateViewSpecN V n)
    (atoms : GateSelectorAtomsN d n) (i : Fin d) : Poly4 d :=
  ∑ v : V, viewSelectorPolyN spec atoms v * BranchData.branchPoly (branch v) i

theorem selectorTotalPolyN_polynomial
    {d n : ℕ} {V : Type} [Fintype V] {B : ℕ}
    (branch : V → BranchData d B) (spec : GateViewSpecN V n)
    (atoms : GateSelectorAtomsN d n) (i : Fin d) :
    ∃ P : Poly4 d, P = selectorTotalPolyN branch spec atoms i :=
  ⟨selectorTotalPolyN branch spec atoms i, rfl⟩

@[simp] theorem eval_selectorTotalPolyN
    {d n : ℕ} {V : Type} [Fintype V] {B : ℕ}
    (branch : V → BranchData d B) (spec : GateViewSpecN V n)
    (atoms : GateSelectorAtomsN d n) (Z : Fin d → ℝ) (i : Fin d) :
    evalPoly4 Z (selectorTotalPolyN branch spec atoms i) =
      selectorF branch Z (LambdaN spec atoms Z) i := by
  classical
  simp [selectorTotalPolyN, selectorF, LambdaN, viewSelectorPolyN, evalPoly4]

/-- Gate selectors plus SEL1 reassembly give the branch-value error bound
(N-atom version). -/
theorem gate_selector_reassemblyN
    {d n : ℕ} {V : Type} [Fintype V] [DecidableEq V] {B : ℕ}
    (branch : V → BranchData d B) (spec : GateViewSpecN V n)
    (atoms : GateSelectorAtomsN d n) (Z : Fin d → ℝ) (vstar : V)
    (i : Fin d) {spread : ℝ}
    (hZ : atoms.inWorkingDomain Z)
    (hsharp : GateAtomSharpnessN spec atoms Z vstar)
    (hspread : BranchSpread branch Z vstar i spread) :
    |evalPoly4 Z (selectorTotalPolyN branch spec atoms i) -
        BranchData.evalBranch (branch vstar) Z i| ≤
      selectorReassemblyCoeff (V := V)
        atoms.errSel atoms.errSel (atoms.errSum V) * spread := by
  classical
  have hsel := gate_view_selectorsN_SEL1_hypotheses spec atoms Z vstar hZ hsharp
  rw [eval_selectorTotalPolyN]
  exact selector_reassembly branch Z (LambdaN spec atoms Z) vstar i
    hsel.errSel_nonneg hsel.errOff_nonneg hsel.hsum hsel.htrue hsel.hoff hspread

/-- Composed SEL2/S3 coordinate clause for the `n`-atom gate family. -/
theorem gate_selector_varMu_coord_clauseN
    {d n nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {E : StackMachineEncoding d nS M}
    {V : Type} [Fintype V] [DecidableEq V]
    (branch : V → BranchData d E.k) (spec : GateViewSpecN V n)
    (atoms : GateSelectorAtomsN d n) (Z : Fin d → ℝ)
    (c : Conf) (vstar : V) (i : Fin d)
    {spread theta : ℝ}
    (hZ : atoms.inWorkingDomain Z)
    (hsharp : GateAtomSharpnessN spec atoms Z vstar)
    (htheta :
      selectorEpsTotal (V := V) atoms.errSel atoms.errSel (atoms.errSum V) spread ≤
        theta)
    (hspread : BranchSpread branch Z vstar i spread)
    (hcontract : BranchContractClause E c (branch vstar)) :
    |evalPoly4 Z (selectorTotalPolyN branch spec atoms i) -
        E.enc (M.step c) i| ≤
      (E.k : ℝ) ^ E.coordDelta c i * |Z i - E.enc c i| + theta := by
  classical
  have hsel := gate_view_selectorsN_SEL1_hypotheses spec atoms Z vstar hZ hsharp
  rw [eval_selectorTotalPolyN]
  exact selector_varMu_coord_clause branch Z (LambdaN spec atoms Z) c vstar i
    hsel.errSel_nonneg hsel.errOff_nonneg htheta
    hsel.hsum hsel.htrue hsel.hoff hspread hcontract

/-! ## Six-coordinate smoke specializations -/

abbrev BranchData6 (B : ℕ) : Type := BranchData 6 B

abbrev Poly6 : Type := Poly4 6

abbrev GateSelectorAtoms6 : Type := GateSelectorAtoms 6

theorem gate_selector_reassembly_d6
    {V : Type} [Fintype V] [DecidableEq V] {B : ℕ}
    (branch : V → BranchData6 B) (spec : GateViewSpec V)
    (atoms : GateSelectorAtoms6) (Z : Fin 6 → ℝ) (vstar : V)
    (i : Fin 6) {spread : ℝ}
    (hZ : atoms.inWorkingDomain Z)
    (hsharp : GateAtomSharpness spec atoms Z vstar)
    (hspread : BranchSpread branch Z vstar i spread) :
    |evalPoly4 Z (selectorTotalPoly branch spec atoms i) -
        BranchData.evalBranch (branch vstar) Z i| ≤
      selectorReassemblyCoeff (V := V)
        atoms.errSel atoms.errOff (atoms.errSum V) * spread :=
  gate_selector_reassembly branch spec atoms Z vstar i hZ hsharp hspread

end

end Ripple.BoundedUniversality.BGP
