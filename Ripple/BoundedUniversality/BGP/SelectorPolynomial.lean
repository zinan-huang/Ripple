/-
Ripple.BoundedUniversality.BGP.SelectorPolynomial
-----------------------------
Machine-generic selector-polynomial layer for the d-coordinate stack
encoding.

The requested design note `notes/gpt-life-p13-encoding.md` is not present in
this checkout.  This file follows the checked-in `StackEncoding`,
`RobustStepContract`, and `CycleTracking` interfaces: reset coordinates are
rebuilt by constant branch actions and therefore have diagonal multiplier `0`.
-/

import Ripple.BoundedUniversality.BGP.StackEncoding
import Ripple.BoundedUniversality.BGP.CycleTracking

namespace Ripple.BoundedUniversality.BGP

open BigOperators
open Ripple.BoundedUniversality.Core

noncomputable section

/-! ## Affine branch maps -/

/-- One-coordinate affine action used by a local branch. -/
structure BranchAction where
  scale : ℚ
  shift : ℚ
  deriving DecidableEq

namespace BranchAction

/-- Raw affine action with prescribed rational coefficients. -/
def affine (scale shift : ℚ) : BranchAction :=
  { scale := scale, shift := shift }

/-- Push digit action: `(dig + x) / B`. -/
def push (B : ℕ) (dig : ℚ) : BranchAction :=
  affine (1 / (B : ℚ)) (dig / (B : ℚ))

/-- Pop digit action: `B * x - dig`. -/
def pop (B : ℕ) (dig : ℚ) : BranchAction :=
  affine (B : ℚ) (-dig)

/-- Identity action. -/
def stay : BranchAction :=
  affine 1 0

/-- Constant reset action. -/
def const (value : ℚ) : BranchAction :=
  affine 0 value

/-- In-place symbol replacement action: `x + delta`. -/
def replace (delta : ℚ) : BranchAction :=
  affine 1 delta

/-- Rational evaluation of a one-coordinate branch action. -/
def evalQ (_B : ℕ) (a : BranchAction) (x : ℚ) : ℚ :=
  a.scale * x + a.shift

/-- Real evaluation of a one-coordinate branch action. -/
def evalReal (_B : ℕ) (a : BranchAction) (x : ℝ) : ℝ :=
  (a.scale : ℝ) * x + (a.shift : ℝ)

/-- Polynomial realization of a one-coordinate branch action. -/
def poly (d _B : ℕ) (i : Fin d) (a : BranchAction) : MvPolynomial (Fin d) ℚ :=
  MvPolynomial.C a.scale * MvPolynomial.X i + MvPolynomial.C a.shift

/-- Diagonal Lipschitz multiplier carried by one action. -/
def multiplier (_B : ℕ) (a : BranchAction) : ℝ :=
  |(a.scale : ℝ)|

@[simp] theorem eval₂_poly (d B : ℕ) (a : BranchAction) (i : Fin d)
    (x : Fin d → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (poly d B i a) =
      evalReal B a (x i) := by
  simp [poly, evalReal]

@[simp] theorem evalReal_of_rat (B : ℕ) (a : BranchAction) (x : ℚ) :
    evalReal B a (x : ℝ) = (evalQ B a x : ℝ) := by
  simp [evalReal, evalQ]

theorem affine_lipschitz (B : ℕ) (a : BranchAction) (x y : ℝ) :
    |evalReal B a x - evalReal B a y| = |(a.scale : ℝ)| * |x - y| := by
  have hdiff :
      evalReal B a x - evalReal B a y = (a.scale : ℝ) * (x - y) := by
    simp [evalReal]
    ring
  rw [hdiff, abs_mul]

/-- Derivative of one affine branch action. -/
theorem evalReal_hasDerivAt (B : ℕ) (a : BranchAction)
    {f : ℝ → ℝ} {f' t : ℝ}
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun τ => evalReal B a (f τ)) ((a.scale : ℝ) * f') t := by
  have hmul := (hasDerivAt_const t (a.scale : ℝ)).mul hf
  have h := hmul.add_const (a.shift : ℝ)
  simpa [evalReal] using h

/-- Uniform diagonal Lipschitz inequality for all branch-action cases. -/
theorem lipschitz_le_multiplier (B : ℕ) (_hB : 0 < B) (a : BranchAction)
    (x y : ℝ) :
    |evalReal B a x - evalReal B a y| ≤ multiplier B a * |x - y| := by
  rw [affine_lipschitz]
  rfl

theorem push_multiplier_eq_zpow (B : ℕ) (hB : 0 < B) (dig : ℚ) :
    multiplier B (push B dig) = (B : ℝ) ^ (-1 : ℤ) := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  simp [multiplier, push, affine, zpow_neg, one_div, abs_of_pos hBpos]

theorem pop_multiplier_eq_zpow (B : ℕ) (dig : ℚ) :
    multiplier B (pop B dig) = (B : ℝ) ^ (1 : ℤ) := by
  have hBnonneg : (0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast Nat.zero_le B
  simp [multiplier, pop, affine, abs_of_nonneg hBnonneg]

theorem stay_multiplier_eq_zpow (B : ℕ) :
    multiplier B stay = (B : ℝ) ^ (0 : ℤ) := by
  simp [multiplier, stay, affine]

theorem replace_multiplier_eq_zpow (B : ℕ) (delta : ℚ) :
    multiplier B (replace delta) = (B : ℝ) ^ (0 : ℤ) := by
  simp [multiplier, replace, affine]

theorem const_multiplier_zero (B : ℕ) (value : ℚ) :
    multiplier B (const value) = 0 := by
  simp [multiplier, const, affine]

theorem multiplier_eq_zpow_of_scale
    (B : ℕ) (a : BranchAction) (δ : ℤ)
    (hscale : |(a.scale : ℝ)| = (B : ℝ) ^ δ) :
    multiplier B a = (B : ℝ) ^ δ := by
  simpa [multiplier] using hscale

end BranchAction

/-- A local branch gives an affine action for each coordinate. -/
structure BranchData (d B : ℕ) where
  action : Fin d → BranchAction

namespace BranchData

/-- Rational branch evaluation. -/
def evalBranchQ {d B : ℕ} (D : BranchData d B) (Z : Fin d → ℚ) :
    Fin d → ℚ :=
  fun i => BranchAction.evalQ B (D.action i) (Z i)

/-- Real branch evaluation. -/
def evalBranch {d B : ℕ} (D : BranchData d B) (Z : Fin d → ℝ) :
    Fin d → ℝ :=
  fun i => BranchAction.evalReal B (D.action i) (Z i)

/-- Polynomial realization of one output coordinate of a branch. -/
def branchPoly {d B : ℕ} (D : BranchData d B) (i : Fin d) :
    MvPolynomial (Fin d) ℚ :=
  BranchAction.poly d B i (D.action i)

@[simp] theorem eval₂_branchPoly {d B : ℕ} (D : BranchData d B) (i : Fin d)
    (Z : Fin d → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) Z (branchPoly D i) =
      evalBranch D Z i := by
  simp [branchPoly, evalBranch, BranchAction.eval₂_poly]

@[simp] theorem evalBranch_of_rat {d B : ℕ} (D : BranchData d B)
    (Z : Fin d → ℚ) (i : Fin d) :
    evalBranch D (fun j => (Z j : ℝ)) i = (evalBranchQ D Z i : ℝ) := by
  simp [evalBranch, evalBranchQ]

theorem coord_lipschitz {d B : ℕ} (hB : 0 < B) (D : BranchData d B)
    (Z W : Fin d → ℝ) (i : Fin d) :
    |evalBranch D Z i - evalBranch D W i| ≤
      BranchAction.multiplier B (D.action i) * |Z i - W i| := by
  exact BranchAction.lipschitz_le_multiplier B hB (D.action i) (Z i) (W i)

/-- Derivative of one output coordinate of an affine branch. -/
theorem evalBranch_hasDerivAt {d B : ℕ} (D : BranchData d B)
    {u : ℝ → Fin d → ℝ} {u' t : ℝ} (i : Fin d)
    (hu : HasDerivAt (fun τ => u τ i) u' t) :
    HasDerivAt (fun τ => evalBranch D (u τ) i)
      (((D.action i).scale : ℝ) * u') t := by
  simpa [evalBranch] using
    BranchAction.evalReal_hasDerivAt B (D.action i) hu

end BranchData

/-! ## Selector reassembly over a finite view family -/

/-- Selector-weighted affine branch family. -/
def selectorF {V : Type} [Fintype V] {d B : ℕ} (branch : V → BranchData d B)
    (Z : Fin d → ℝ) (Λ : V → ℝ) : Fin d → ℝ :=
  fun i => ∑ v : V, Λ v * BranchData.evalBranch (branch v) Z i

/-- Number of views other than the selected view, as a real scalar. -/
def offViewCount (V : Type) [Fintype V] : ℝ := (Fintype.card V - 1 : ℕ)

/-- Linear selector error budget multiplying a branch-value spread bound. -/
def selectorReassemblyCoeff {V : Type} [Fintype V]
    (errSel errOff errSum : ℝ) : ℝ :=
  errSum + errSel + offViewCount V * errOff

/-- Branch-value spread assumptions needed by selector reassembly. -/
def BranchSpread {V : Type} {d B : ℕ} (branch : V → BranchData d B)
    (Z : Fin d → ℝ) (vstar : V) (i : Fin d) (R : ℝ) : Prop :=
  |BranchData.evalBranch (branch vstar) Z i| ≤ R ∧
    ∀ v, v ≠ vstar →
      |BranchData.evalBranch (branch v) Z i -
        BranchData.evalBranch (branch vstar) Z i| ≤ R

private theorem sum_off_eq_sub_singleton {V : Type} [Fintype V] [DecidableEq V]
    (vstar : V) (f : V → ℝ) :
    (Finset.univ.filter (fun v : V => v ≠ vstar)).sum f =
      (∑ v : V, f v) - f vstar := by
  have hset :
      Finset.univ.filter (fun v : V => v ≠ vstar) =
        (Finset.univ : Finset V).erase vstar := by
    ext v
    by_cases h : v = vstar <;> simp [h]
  rw [hset, Finset.sum_erase_eq_sub]
  simp

private theorem off_card_le (V : Type) [Fintype V] [DecidableEq V] (vstar : V) :
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

theorem selector_reassembly
    {V : Type} [Fintype V] [DecidableEq V] {d B : ℕ}
    (branch : V → BranchData d B) (Z : Fin d → ℝ) (Λ : V → ℝ)
    (vstar : V) (i : Fin d)
    {errSel errOff errSum R : ℝ}
    (herrSel_nonneg : 0 ≤ errSel)
    (herrOff_nonneg : 0 ≤ errOff)
    (hsum : |(∑ v : V, Λ v) - 1| ≤ errSum)
    (_htrue : 1 - errSel ≤ Λ vstar)
    (hoff : ∀ v, v ≠ vstar → 0 ≤ Λ v ∧ Λ v ≤ errOff)
    (hspread : BranchSpread branch Z vstar i R) :
    |selectorF branch Z Λ i - BranchData.evalBranch (branch vstar) Z i| ≤
      selectorReassemblyCoeff (V := V) errSel errOff errSum * R := by
  let A : V → ℝ := fun v => BranchData.evalBranch (branch v) Z i
  have hR_abs : 0 ≤ R := (abs_nonneg (A vstar)).trans hspread.1
  have herrSum_nonneg : 0 ≤ errSum := (abs_nonneg ((∑ v : V, Λ v) - 1)).trans hsum
  have hcoeff_core :
      |selectorF branch Z Λ i - A vstar| ≤
        (errSum + offViewCount V * errOff) * R := by
    let g : V → ℝ := fun v => Λ v * (A v - A vstar)
    have hoffeq :
        (Finset.univ.filter (fun v : V => v ≠ vstar)).sum g =
          ∑ v : V, g v := by
      rw [sum_off_eq_sub_singleton vstar g]
      simp [g]
    have hdecomp :
        selectorF branch Z Λ i - A vstar =
          ((∑ v : V, Λ v) - 1) * A vstar +
            (Finset.univ.filter (fun v : V => v ≠ vstar)).sum g := by
      have hfull :
          selectorF branch Z Λ i - A vstar =
            ((∑ v : V, Λ v) - 1) * A vstar + ∑ v : V, g v := by
        calc
          selectorF branch Z Λ i - A vstar
              = (∑ v : V, Λ v * A v) - A vstar := by simp [selectorF, A]
          _ = (∑ v : V, (g v + Λ v * A vstar)) - A vstar := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro v _hv
                simp [g]
                ring
          _ = (∑ v : V, g v) + (∑ v : V, Λ v * A vstar) - A vstar := by
                rw [Finset.sum_add_distrib]
          _ = (∑ v : V, g v) + (∑ v : V, Λ v) * A vstar - A vstar := by
                rw [Finset.sum_mul]
          _ = ((∑ v : V, Λ v) - 1) * A vstar + ∑ v : V, g v := by ring
      rw [hfull, hoffeq]
    have hsum_abs :
        |((∑ v : V, Λ v) - 1) * A vstar| ≤ errSum * R := by
      calc
        |((∑ v : V, Λ v) - 1) * A vstar|
            = |(∑ v : V, Λ v) - 1| * |A vstar| := abs_mul _ _
        _ ≤ errSum * R :=
            mul_le_mul hsum hspread.1 (abs_nonneg _) herrSum_nonneg
    have hoff_sum :
        |(Finset.univ.filter (fun v : V => v ≠ vstar)).sum (fun v =>
            Λ v * (A v - A vstar))| ≤ offViewCount V * errOff * R := by
      calc
        |(Finset.univ.filter (fun v : V => v ≠ vstar)).sum (fun v =>
            Λ v * (A v - A vstar))|
            ≤ (Finset.univ.filter (fun v : V => v ≠ vstar)).sum (fun v =>
                |Λ v * (A v - A vstar)|) := Finset.abs_sum_le_sum_abs _ _
        _ ≤ (Finset.univ.filter (fun v : V => v ≠ vstar)).sum (fun _ =>
              errOff * R) := by
              refine Finset.sum_le_sum (fun v hv => ?_)
              have hvne : v ≠ vstar := by simpa using
                (Finset.mem_filter.mp hv).2
              have hLam := hoff v hvne
              calc
                |Λ v * (A v - A vstar)|
                    = |Λ v| * |A v - A vstar| := abs_mul _ _
                _ = Λ v * |A v - A vstar| := by rw [abs_of_nonneg hLam.1]
                _ ≤ errOff * R :=
                    mul_le_mul hLam.2 (hspread.2 v hvne) (abs_nonneg _) herrOff_nonneg
        _ = ((Finset.univ.filter (fun v : V => v ≠ vstar)).card : ℝ) *
              (errOff * R) := by simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ offViewCount V * errOff * R := by
              have hcount := off_card_le V vstar
              have hmul_nonneg : 0 ≤ errOff * R := mul_nonneg herrOff_nonneg hR_abs
              calc
                ((Finset.univ.filter (fun v : V => v ≠ vstar)).card : ℝ) *
                    (errOff * R)
                    ≤ offViewCount V * (errOff * R) :=
                      mul_le_mul_of_nonneg_right hcount hmul_nonneg
                _ = offViewCount V * errOff * R := by ring
    calc
      |selectorF branch Z Λ i - A vstar|
          = |((∑ v : V, Λ v) - 1) * A vstar +
              (Finset.univ.filter (fun v : V => v ≠ vstar)).sum (fun v =>
                Λ v * (A v - A vstar))| := by rw [hdecomp]
      _ ≤ |((∑ v : V, Λ v) - 1) * A vstar| +
            |(Finset.univ.filter (fun v : V => v ≠ vstar)).sum (fun v =>
              Λ v * (A v - A vstar))| := abs_add_le _ _
      _ ≤ errSum * R + offViewCount V * errOff * R :=
            add_le_add hsum_abs hoff_sum
      _ = (errSum + offViewCount V * errOff) * R := by ring
  have hselR_nonneg : 0 ≤ errSel * R := mul_nonneg herrSel_nonneg hR_abs
  calc
    |selectorF branch Z Λ i - BranchData.evalBranch (branch vstar) Z i|
        = |selectorF branch Z Λ i - A vstar| := by simp [A]
    _ ≤ (errSum + offViewCount V * errOff) * R := hcoeff_core
    _ ≤ selectorReassemblyCoeff (V := V) errSel errOff errSum * R := by
          simp [selectorReassemblyCoeff]
          nlinarith

/-- Selector reassembly plus a true-branch diagonal estimate. -/
theorem selector_diagonal_bound
    {V : Type} [Fintype V] [DecidableEq V] {d B : ℕ}
    (branch : V → BranchData d B) (Z enc nextEnc : Fin d → ℝ) (Λ : V → ℝ)
    (vstar : V) (i : Fin d)
    {errSel errOff errSum R mult : ℝ}
    (herrSel_nonneg : 0 ≤ errSel)
    (herrOff_nonneg : 0 ≤ errOff)
    (hsum : |(∑ v : V, Λ v) - 1| ≤ errSum)
    (htrue : 1 - errSel ≤ Λ vstar)
    (hoff : ∀ v, v ≠ vstar → 0 ≤ Λ v ∧ Λ v ≤ errOff)
    (hspread : BranchSpread branch Z vstar i R)
    (hdiag :
      |BranchData.evalBranch (branch vstar) Z i - nextEnc i| ≤
        mult * |Z i - enc i|) :
    |selectorF branch Z Λ i - nextEnc i| ≤
      mult * |Z i - enc i| +
        selectorReassemblyCoeff (V := V) errSel errOff errSum * R := by
  have hsel := selector_reassembly branch Z Λ vstar i
    herrSel_nonneg herrOff_nonneg hsum htrue hoff hspread
  have htri :
      |selectorF branch Z Λ i - nextEnc i| ≤
        |selectorF branch Z Λ i - BranchData.evalBranch (branch vstar) Z i| +
          |BranchData.evalBranch (branch vstar) Z i - nextEnc i| := by
    have hsum' :
        selectorF branch Z Λ i - nextEnc i =
          (selectorF branch Z Λ i - BranchData.evalBranch (branch vstar) Z i) +
            (BranchData.evalBranch (branch vstar) Z i - nextEnc i) := by ring
    rw [hsum']
    exact abs_add_le _ _
  calc
    |selectorF branch Z Λ i - nextEnc i|
        ≤ |selectorF branch Z Λ i - BranchData.evalBranch (branch vstar) Z i| +
          |BranchData.evalBranch (branch vstar) Z i - nextEnc i| := htri
    _ ≤ selectorReassemblyCoeff (V := V) errSel errOff errSum * R +
          mult * |Z i - enc i| := add_le_add hsel hdiag
    _ = mult * |Z i - enc i| +
          selectorReassemblyCoeff (V := V) errSel errOff errSum * R := by ring

/-! ## Contract-clause bridge -/

/--
Compatibility of the selected branch with the machine encoding at one
configuration.  The multiplier inequality is where stack actions are matched
to `k ^ delta`, while reset coordinates must be constant actions to fit the
contract's zero amplifier.
-/
structure BranchContractClause
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    (E : StackMachineEncoding d nS M) (c : Conf) (D : BranchData d E.k) where
  exact_next :
    ∀ i, BranchData.evalBranch D (E.enc c) i = E.enc (M.step c) i
  multiplier_le :
    ∀ i, BranchAction.multiplier E.k (D.action i) ≤ E.coordMultiplier c i

namespace BranchContractClause

theorem diagonal
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {E : StackMachineEncoding d nS M} {c : Conf} {D : BranchData d E.k}
    (H : BranchContractClause E c D) (Z : Fin d → ℝ) (i : Fin d) :
    |BranchData.evalBranch D Z i - E.enc (M.step c) i| ≤
      E.coordMultiplier c i * |Z i - E.enc c i| := by
  have hkpos : 0 < E.k := lt_of_lt_of_le (by decide : 0 < 4) E.hk
  have hlip := BranchData.coord_lipschitz hkpos D Z (E.enc c) i
  calc
    |BranchData.evalBranch D Z i - E.enc (M.step c) i|
        = |BranchData.evalBranch D Z i - BranchData.evalBranch D (E.enc c) i| := by
            rw [H.exact_next i]
    _ ≤ BranchAction.multiplier E.k (D.action i) * |Z i - E.enc c i| := hlip
    _ ≤ E.coordMultiplier c i * |Z i - E.enc c i| :=
          mul_le_mul_of_nonneg_right (H.multiplier_le i) (abs_nonneg _)

theorem zpow_diagonal
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {E : StackMachineEncoding d nS M} {c : Conf} {D : BranchData d E.k}
    (H : BranchContractClause E c D) (Z : Fin d → ℝ) (i : Fin d) :
    |BranchData.evalBranch D Z i - E.enc (M.step c) i| ≤
      (E.k : ℝ) ^ E.coordDelta c i * |Z i - E.enc c i| := by
  exact (H.diagonal Z i).trans
    (E.coordMultiplier_error_le_zpow c i Z)

theorem reset_diagonal_zero
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {E : StackMachineEncoding d nS M} {c : Conf} {D : BranchData d E.k}
    (H : BranchContractClause E c D) {i : Fin d}
    (hi : E.coordStackIndex i = none) (Z : Fin d → ℝ) :
    |BranchData.evalBranch D Z i - E.enc (M.step c) i| ≤ 0 := by
  have hdiag := H.diagonal Z i
  simpa [StackMachineEncoding.coordMultiplier, hi] using hdiag

end BranchContractClause

/-- Selector error term used by the robust-step bridge. -/
def selectorEpsTotal {V : Type} [Fintype V]
    (errSel errOff errSum spread : ℝ) : ℝ :=
  selectorReassemblyCoeff (V := V) errSel errOff errSum * spread

/--
Machine-generic bridge into the diagonal `RobustStepContract` clause shape.
The dynamic gate layer is represented only by hypotheses on the selector
weights; the extraction layer is represented by the supplied selected view
`vstar`, which later comes from `localExtract_tube`.
-/
theorem selector_robustStep_diagonal_clause
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {E : StackMachineEncoding d nS M}
    {V : Type} [Fintype V] [DecidableEq V]
    (branch : V → BranchData d E.k) (Z : Fin d → ℝ) (Λ : V → ℝ)
    (c : Conf) (vstar : V) (i : Fin d)
    {errSel errOff errSum spread : ℝ}
    (herrSel_nonneg : 0 ≤ errSel)
    (herrOff_nonneg : 0 ≤ errOff)
    (hsum : |(∑ v : V, Λ v) - 1| ≤ errSum)
    (htrue : 1 - errSel ≤ Λ vstar)
    (hoff : ∀ v, v ≠ vstar → 0 ≤ Λ v ∧ Λ v ≤ errOff)
    (hspread : BranchSpread branch Z vstar i spread)
    (hcontract : BranchContractClause E c (branch vstar)) :
    |selectorF branch Z Λ i - E.enc (M.step c) i| ≤
      E.coordMultiplier c i * |Z i - E.enc c i| +
        selectorEpsTotal (V := V) errSel errOff errSum spread := by
  simpa [selectorEpsTotal] using
    selector_diagonal_bound branch Z (E.enc c) (E.enc (M.step c)) Λ vstar i
      herrSel_nonneg herrOff_nonneg hsum htrue hoff hspread
      (hcontract.diagonal Z i)

/--
The same bridge in the zpow coordinate shape used by `CycleTracking`.
-/
theorem selector_varMu_coord_clause
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {E : StackMachineEncoding d nS M}
    {V : Type} [Fintype V] [DecidableEq V]
    (branch : V → BranchData d E.k) (Z : Fin d → ℝ) (Λ : V → ℝ)
    (c : Conf) (vstar : V) (i : Fin d)
    {errSel errOff errSum spread theta : ℝ}
    (herrSel_nonneg : 0 ≤ errSel)
    (herrOff_nonneg : 0 ≤ errOff)
    (htheta :
      selectorEpsTotal (V := V) errSel errOff errSum spread ≤ theta)
    (hsum : |(∑ v : V, Λ v) - 1| ≤ errSum)
    (htrue : 1 - errSel ≤ Λ vstar)
    (hoff : ∀ v, v ≠ vstar → 0 ≤ Λ v ∧ Λ v ≤ errOff)
    (hspread : BranchSpread branch Z vstar i spread)
    (hcontract : BranchContractClause E c (branch vstar)) :
    |selectorF branch Z Λ i - E.enc (M.step c) i| ≤
      (E.k : ℝ) ^ E.coordDelta c i * |Z i - E.enc c i| + theta := by
  have hrob := selector_robustStep_diagonal_clause branch Z Λ c vstar i
    herrSel_nonneg herrOff_nonneg hsum htrue hoff hspread hcontract
  have hzpow := E.coordMultiplier_error_le_zpow c i Z
  calc
    |selectorF branch Z Λ i - E.enc (M.step c) i|
        ≤ E.coordMultiplier c i * |Z i - E.enc c i| +
          selectorEpsTotal (V := V) errSel errOff errSum spread := hrob
    _ ≤ (E.k : ℝ) ^ E.coordDelta c i * |Z i - E.enc c i| + theta :=
          add_le_add hzpow htheta

/--
Reset-coordinate bridge: when `coordStackIndex i = none`, the contract
multiplier is zero, so the selector layer contributes only the explicit
selector error budget.
-/
theorem selector_varMu_reset_clause
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {E : StackMachineEncoding d nS M}
    {V : Type} [Fintype V] [DecidableEq V]
    (branch : V → BranchData d E.k) (Z : Fin d → ℝ) (Λ : V → ℝ)
    (c : Conf) (vstar : V) {i : Fin d}
    (hi : E.coordStackIndex i = none)
    {errSel errOff errSum spread theta : ℝ}
    (herrSel_nonneg : 0 ≤ errSel)
    (herrOff_nonneg : 0 ≤ errOff)
    (htheta :
      selectorEpsTotal (V := V) errSel errOff errSum spread ≤ theta)
    (hsum : |(∑ v : V, Λ v) - 1| ≤ errSum)
    (htrue : 1 - errSel ≤ Λ vstar)
    (hoff : ∀ v, v ≠ vstar → 0 ≤ Λ v ∧ Λ v ≤ errOff)
    (hspread : BranchSpread branch Z vstar i spread)
    (hcontract : BranchContractClause E c (branch vstar)) :
    |selectorF branch Z Λ i - E.enc (M.step c) i| ≤ theta := by
  have hrob := selector_robustStep_diagonal_clause branch Z Λ c vstar i
    herrSel_nonneg herrOff_nonneg hsum htrue hoff hspread hcontract
  have hzero : E.coordMultiplier c i * |Z i - E.enc c i| = 0 := by
    simp [StackMachineEncoding.coordMultiplier, hi]
  calc
    |selectorF branch Z Λ i - E.enc (M.step c) i|
        ≤ E.coordMultiplier c i * |Z i - E.enc c i| +
          selectorEpsTotal (V := V) errSel errOff errSum spread := hrob
    _ = selectorEpsTotal (V := V) errSel errOff errSum spread := by rw [hzero, zero_add]
    _ ≤ theta := htheta

end

end Ripple.BoundedUniversality.BGP
