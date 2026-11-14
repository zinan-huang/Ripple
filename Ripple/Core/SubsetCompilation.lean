import Ripple.Core.ShiftedClockCompilation
import Ripple.Core.MaximalPIVP
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.BooleanAlgebra

/-!
# General subset compilation for BAC Remark 3.7

The coordinate equivalence puts retained coordinates on the left and clocked
coordinates on the right. Retained coordinates follow their actual scaled
source equations. An arbitrary finite family of source coordinates can also
be retained as output copies.

The S-degree bound controls the surrogate lift. The independent total-degree
bound controls the compiled degree and the explicit field estimate. The
coefficient majorant Cp and the retained bound K are parameters of the
maximal-source theorems.

The exact solution is exported through SubsetSolution: its clock covers the
whole maximal source interval and its trajectory equations hold at every
nonnegative compiled time. Uniqueness follows from polynomial ODE uniqueness.
All even N are supported, in particular the requested even N at least two.
-/

noncomputable section

namespace Ripple.SubsetCompilation

open MvPolynomial Filter Set MeasureTheory Topology
open scoped BigOperators ENNReal

/-! ## A concrete finite partition -/

/-- Enumerate the complement first and the selected subset second. -/
def subsetPartition {d : ℕ} (S : Finset (Fin d)) :
    Fin d ≃ (Fin (Sᶜ).card ⊕ Fin S.card) := by
  classical
  let eR : {i : Fin d // i ∉ S} ≃ (Sᶜ : Finset (Fin d)) :=
    { toFun := fun i => ⟨i.1, Finset.mem_compl.mpr i.2⟩
      invFun := fun i => ⟨i.1, Finset.mem_compl.mp i.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  exact (Equiv.sumCompl (fun i : Fin d => i ∈ S)).symm.trans
    ((Equiv.sumCongr S.equivFin (eR.trans (Sᶜ).equivFin)).trans
      (Equiv.sumComm _ _))

@[simp] theorem subsetPartition_retained {d : ℕ}
    (S : Finset (Fin d)) (j : Fin (Sᶜ).card) :
    (subsetPartition S).symm (Sum.inl j) =
      ((Sᶜ).equivFin.symm j).1 := rfl

@[simp] theorem subsetPartition_source {d : ℕ}
    (S : Finset (Fin d)) (j : Fin S.card) :
    (subsetPartition S).symm (Sum.inr j) =
      (S.equivFin.symm j).1 := rfl

theorem subsetPartition_retained_not_mem {d : ℕ}
    (S : Finset (Fin d)) (j : Fin (Sᶜ).card) :
    (subsetPartition S).symm (Sum.inl j) ∉ S := by
  rw [subsetPartition_retained]
  exact Finset.mem_compl.mp ((Sᶜ).equivFin.symm j).2

theorem subsetPartition_source_mem {d : ℕ}
    (S : Finset (Fin d)) (j : Fin S.card) :
    (subsetPartition S).symm (Sum.inr j) ∈ S := by
  rw [subsetPartition_source]
  exact (S.equivFin.symm j).2

/-! ## Rational polynomial construction and its quantitative bounds -/

variable {d r s m N D : ℕ}

abbrev SubsetIndex (r s m N : ℕ) :=
  Fin r ⊕ (Fin m ⊕ SurrogateIndex s N)

abbrev subsetDim (r s m N : ℕ) :=
  Fintype.card (SubsetIndex r s m N)

def subsetRetained {α : Type*} (e : Fin d ≃ (Fin r ⊕ Fin s))
    (y : Fin d → α) : Fin r → α :=
  fun j => y (e.symm (Sum.inl j))

def subsetSource {α : Type*} (e : Fin d ≃ (Fin r ⊕ Fin s))
    (y : Fin d → α) : Fin s → α :=
  fun i => y (e.symm (Sum.inr i))

theorem subset_reassemble {α : Type*} (e : Fin d ≃ (Fin r ⊕ Fin s))
    (y : Fin d → α) :
    (Sum.elim (subsetRetained e y) (subsetSource e y)) ∘ e = y := by
  have h : Sum.elim (subsetRetained e y) (subsetSource e y) = y ∘ e.symm := by
    funext j
    cases j <;> rfl
  rw [h]
  funext i
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

def subsetClock (e : Fin d ≃ (Fin r ⊕ Fin s)) (N : ℕ)
    (y : Fin d → ℝ) : ℝ :=
  jointClock N (subsetSource e y)

theorem subsetClock_ge_one (e : Fin d ≃ (Fin r ⊕ Fin s))
    {N : ℕ} (hN : Even N) (y : Fin d → ℝ) :
    1 ≤ subsetClock e N y :=
  jointClock_ge_one hN _

theorem subsetClock_pos (e : Fin d ≃ (Fin r ⊕ Fin s))
    {N : ℕ} (hN : Even N) (y : Fin d → ℝ) :
    0 < subsetClock e N y :=
  jointClock_pos hN _

theorem continuous_subsetRetained (e : Fin d ≃ (Fin r ⊕ Fin s)) :
    Continuous (subsetRetained e : (Fin d → ℝ) → Fin r → ℝ) :=
  continuous_pi fun j => continuous_apply _

theorem continuous_subsetSource (e : Fin d ≃ (Fin r ⊕ Fin s)) :
    Continuous (subsetSource e : (Fin d → ℝ) → Fin s → ℝ) :=
  continuous_pi fun i => continuous_apply _

theorem continuous_subsetClock (e : Fin d ≃ (Fin r ⊕ Fin s)) (N : ℕ) :
    Continuous (subsetClock e N) :=
  (continuous_jointClock N).comp (continuous_subsetSource e)

/-- The maximum total exponent among the clocked variables in a support monomial. -/
def subsetSDegree (q : MvPolynomial (Fin r ⊕ Fin s) ℚ) : ℕ :=
  q.support.sup (fun b => ∑ i : Fin s, b (Sum.inr i))

theorem subsetSDegree_mem {q : MvPolynomial (Fin r ⊕ Fin s) ℚ}
    {b : (Fin r ⊕ Fin s) →₀ ℕ} (hb : b ∈ q.support) :
    (∑ i : Fin s, b (Sum.inr i)) ≤ subsetSDegree q :=
  Finset.le_sup (f := fun b : (Fin r ⊕ Fin s) →₀ ℕ => ∑ i : Fin s, b (Sum.inr i)) hb

theorem subset_degree_split_le {q : MvPolynomial (Fin r ⊕ Fin s) ℚ}
    {b : (Fin r ⊕ Fin s) →₀ ℕ} (hb : b ∈ q.support) :
    (∑ j : Fin r, b (Sum.inl j)) + (∑ i : Fin s, b (Sum.inr i)) ≤
      q.totalDegree := by
  have h := le_totalDegree hb
  rwa [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sum_type] at h

def subsetExponent (b : (Fin r ⊕ Fin s) →₀ ℕ)
    (hb : (∑ i : Fin s, b (Sum.inr i)) ≤ N) : SurrogateIndex s N :=
  ⟨fun i => ⟨b (Sum.inr i), Nat.lt_succ_of_le
    ((Finset.single_le_sum (f := fun j : Fin s => b (Sum.inr j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hb)⟩,
    by unfold MIndex.degree; exact hb⟩

def subsetMonomial (N : ℕ) (b : (Fin r ⊕ Fin s) →₀ ℕ) :
    MvPolynomial (SubsetIndex r s m N) ℚ :=
  if hb : (∑ i : Fin s, b (Sum.inr i)) ≤ N then
    X (Sum.inr (Sum.inr (subsetExponent b hb)))
  else 0

/-- One clocked monomial is replaced by one surrogate; retained factors remain variables. -/
def subsetLift (N : ℕ) (q : MvPolynomial (Fin r ⊕ Fin s) ℚ) :
    MvPolynomial (SubsetIndex r s m N) ℚ :=
  ∑ b ∈ q.support,
    C (q.coeff b) * (∏ j : Fin r, X (Sum.inl j) ^ b (Sum.inl j)) *
      subsetMonomial N b

theorem subsetLift_eval {q : MvPolynomial (Fin r ⊕ Fin s) ℚ}
    (hS : subsetSDegree q ≤ N) (c : Fin r → ℝ) (z : Fin s → ℝ)
    (v : SubsetIndex r s m N → ℝ)
    (hc : ∀ j, v (Sum.inl j) = c j)
    (hw : ∀ a, v (Sum.inr (Sum.inr a)) = jointSurrogate N a z) :
    (subsetLift N q).eval₂ (Rat.castHom ℝ) v =
      q.eval₂ (Rat.castHom ℝ) (Sum.elim c z) / jointClock N z := by
  classical
  rw [MvPolynomial.eval₂_eq' (Rat.castHom ℝ) (Sum.elim c z) q, Finset.sum_div]
  unfold subsetLift
  rw [eval₂_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hdegree := (subsetSDegree_mem hb).trans hS
  simp only [subsetMonomial, dif_pos hdegree, eval₂_mul, eval₂_C,
    eval₂_prod, eval₂_pow, eval₂_X, hc, hw, jointSurrogate,
    subsetExponent, MIndex.eval, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  ring

theorem subsetLift_totalDegree_le (N : ℕ)
    (q : MvPolynomial (Fin r ⊕ Fin s) ℚ) :
    (subsetLift (m := m) N q).totalDegree ≤ q.totalDegree + 1 := by
  classical
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun b hb => ?_)
  have hdegree := subset_degree_split_le hb
  have hp : (∏ j : Fin r, X (Sum.inl j) ^ b (Sum.inl j) :
      MvPolynomial (SubsetIndex r s m N) ℚ).totalDegree ≤
        ∑ j : Fin r, b (Sum.inl j) :=
    (totalDegree_finsetProd _ _).trans
      (Finset.sum_le_sum fun j _ => (totalDegree_X_pow _ _).le)
  have hz : (subsetMonomial (m := m) N b).totalDegree ≤ 1 := by
    unfold subsetMonomial
    split_ifs
    · exact (totalDegree_X _).le
    · simp
  refine (totalDegree_mul _ _).trans ?_
  have hprod := totalDegree_mul (C (q.coeff b))
    (∏ j : Fin r, X (Sum.inl j) ^ b (Sum.inl j) :
      MvPolynomial (SubsetIndex r s m N) ℚ)
  rw [totalDegree_C, zero_add] at hprod
  omega

def subsetFieldLift (P : PolyPIVP d) (e : Fin d ≃ (Fin r ⊕ Fin s))
    (N : ℕ) (i : Fin d) : MvPolynomial (SubsetIndex r s m N) ℚ :=
  subsetLift N (rename e (P.field i))

theorem subsetFieldLift_eval (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) {N : ℕ}
    (hS : ∀ i, subsetSDegree (rename e (P.field i)) ≤ N)
    (y : Fin d → ℝ) (v : SubsetIndex r s m N → ℝ)
    (hR : ∀ j, v (Sum.inl j) = subsetRetained e y j)
    (hW : ∀ a, v (Sum.inr (Sum.inr a)) =
      jointSurrogate N a (subsetSource e y)) (i : Fin d) :
    (subsetFieldLift P e N i).eval₂ (Rat.castHom ℝ) v =
      P.evalField y i / subsetClock e N y := by
  simpa only [subsetFieldLift, eval₂_rename, subset_reassemble, subsetClock,
    PolyPIVP.evalField] using
      subsetLift_eval (hS i) (subsetRetained e y) (subsetSource e y) v hR hW

def subsetField (P : PolyPIVP d) (e : Fin d ≃ (Fin r ⊕ Fin s))
    (o : Fin m → Fin d) (N : ℕ) :
    SubsetIndex r s m N → MvPolynomial (SubsetIndex r s m N) ℚ
  | Sum.inl j => subsetFieldLift P e N (e.symm (Sum.inl j))
  | Sum.inr (Sum.inl j) => subsetFieldLift P e N (o j)
  | Sum.inr (Sum.inr a) =>
      ∑ i : Fin s, C (((a.1 i : ℕ) : ℚ)) *
        X (Sum.inr (Sum.inr (a.decr i))) *
          subsetFieldLift P e N (e.symm (Sum.inr i)) -
      C ((N : ℚ)) * X (Sum.inr (Sum.inr a)) *
        ∑ i : Fin s, X (Sum.inr (Sum.inr (SurrogateIndex.powIdx N i))) *
          subsetFieldLift P e N (e.symm (Sum.inr i))

def subsetInit (P : PolyPIVP d) (e : Fin d ≃ (Fin r ⊕ Fin s))
    (o : Fin m → Fin d) (N : ℕ) : SubsetIndex r s m N → ℚ
  | Sum.inl j => P.init (e.symm (Sum.inl j))
  | Sum.inr (Sum.inl j) => P.init (o j)
  | Sum.inr (Sum.inr a) =>
      (∏ i : Fin s, P.init (e.symm (Sum.inr i)) ^ (a.1 i : ℕ)) /
        (1 + ∑ i : Fin s, P.init (e.symm (Sum.inr i)) ^ N)

def subsetOutputIndex : Fin r ⊕ Fin m → SubsetIndex r s m N
  | Sum.inl j => Sum.inl j
  | Sum.inr j => Sum.inr (Sum.inl j)

def subsetCompile (P : PolyPIVP d) (e : Fin d ≃ (Fin r ⊕ Fin s))
    (o : Fin m → Fin d) (N : ℕ) (out : Fin r ⊕ Fin m) :
    PolyPIVP (subsetDim r s m N) :=
  PolyPIVP.ofIndexed (subsetField P e o N) (subsetInit P e o N)
    (subsetOutputIndex out)

theorem subsetDim_eq (r s m N : ℕ) :
    subsetDim r s m N = r + (s + N).choose N + m := by
  simp [subsetDim, SubsetIndex, Fintype.card_sum, card_surrogateIndex,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem subsetField_totalDegree_le (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d) (N : ℕ)
    {D : ℕ} (hD : ∀ i, (P.field i).totalDegree ≤ D)
    (k : SubsetIndex r s m N) :
    (subsetField P e o N k).totalDegree ≤ 3 + D := by
  classical
  have hl : ∀ i, (subsetFieldLift (m := m) P e N i).totalDegree ≤ D + 1 :=
    fun i => (subsetLift_totalDegree_le N _).trans
      (Nat.add_le_add_right ((totalDegree_rename_le e _).trans (hD i)) 1)
  rcases k with j | j | a
  · exact (hl (e.symm (Sum.inl j))).trans (by omega)
  · exact (hl (o j)).trans (by omega)
  · change (∑ i : Fin s, C (((a.1 i : ℕ) : ℚ)) *
        X (Sum.inr (Sum.inr (a.decr i))) *
          subsetFieldLift P e N (e.symm (Sum.inr i)) -
      C ((N : ℚ)) * X (Sum.inr (Sum.inr a)) *
        ∑ i : Fin s, X (Sum.inr (Sum.inr (SurrogateIndex.powIdx N i))) *
          subsetFieldLift P e N (e.symm (Sum.inr i)) :
      MvPolynomial (SubsetIndex r s m N) ℚ).totalDegree ≤ 3 + D
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
      have hfirst := totalDegree_C_mul_X_le (((a.1 i : ℕ) : ℚ))
        (Sum.inr (Sum.inr (a.decr i)) : SubsetIndex r s m N)
      have hsecond := hl (e.symm (Sum.inr i))
      exact (totalDegree_mul _ _).trans (by omega)
    · have hfirst := totalDegree_C_mul_X_le ((N : ℚ))
        (Sum.inr (Sum.inr a) : SubsetIndex r s m N)
      have hsecond : (∑ i : Fin s,
          X (Sum.inr (Sum.inr (SurrogateIndex.powIdx N i))) *
            subsetFieldLift P e N (e.symm (Sum.inr i)) :
          MvPolynomial (SubsetIndex r s m N) ℚ).totalDegree ≤ D + 2 := by
        refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
        have hthird := hl (e.symm (Sum.inr i))
        refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]
        omega
      exact (totalDegree_mul _ _).trans (by omega)

theorem subsetCompile_totalDegree_le (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d) (N : ℕ)
    (out : Fin r ⊕ Fin m) {D : ℕ}
    (hD : ∀ i, (P.field i).totalDegree ≤ D)
    (j : Fin (subsetDim r s m N)) :
    ((subsetCompile P e o N out).field j).totalDegree ≤ 3 + D := by
  exact (totalDegree_rename_le _ _).trans
    (subsetField_totalDegree_le P e o N hD _)

theorem subsetCompile_init_is_rational (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d) (N : ℕ)
    (out : Fin r ⊕ Fin m) (j : Fin (subsetDim r s m N)) :
    ∃ q : ℚ, (subsetCompile P e o N out).toPIVP.init j = (q : ℝ) :=
  PolyPIVP.init_is_rational _ j

def subsetCoefficientSum (q : MvPolynomial (Fin r ⊕ Fin s) ℚ) : ℝ :=
  ∑ b ∈ q.support, |((q.coeff b : ℚ) : ℝ)|

theorem subsetCoefficientSum_nonneg (q : MvPolynomial (Fin r ⊕ Fin s) ℚ) :
    0 ≤ subsetCoefficientSum q :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The maximum of the finite list of coefficient absolute sums in split coordinates. -/
def subsetCoefficientMaximum (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) : ℝ :=
  sSup (Set.range (fun i : Fin d => subsetCoefficientSum (rename e (P.field i))))

theorem subsetCoefficientSum_le_maximum (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (i : Fin d) :
    subsetCoefficientSum (rename e (P.field i)) ≤ subsetCoefficientMaximum P e := by
  change subsetCoefficientSum (rename e (P.field i)) ≤
    sSup (Set.range (fun j : Fin d => subsetCoefficientSum (rename e (P.field j))))
  exact le_csSup (Set.finite_range _).bddAbove ⟨i, rfl⟩

theorem subsetCoefficientMaximum_nonneg (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) :
    0 ≤ subsetCoefficientMaximum P e :=
  (subsetCoefficientSum_nonneg _).trans (subsetCoefficientSum_le_maximum P e P.output)

/-- A retained monomial costs at most K^D and its clocked factor costs at most P_S. -/
theorem subset_abs_eval_le {q : MvPolynomial (Fin r ⊕ Fin s) ℚ}
    {N D : ℕ} (hN : Even N) (hS : subsetSDegree q ≤ N) (hD : q.totalDegree ≤ D)
    (c : Fin r → ℝ) (z : Fin s → ℝ) {K : ℝ}
    (hK : 1 ≤ K) (hc : ∀ j, |c j| ≤ K) :
    |q.eval₂ (Rat.castHom ℝ) (Sum.elim c z)| ≤
      subsetCoefficientSum q * K ^ D * jointClock N z := by
  classical
  have hKzero : 0 ≤ K := zero_le_one.trans hK
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hterm : ∀ b ∈ q.support,
      |(Rat.castHom ℝ) (q.coeff b) *
        ∏ j : Fin r ⊕ Fin s, (Sum.elim c z) j ^ b j| ≤
      |((q.coeff b : ℚ) : ℝ)| * K ^ D * jointClock N z := by
    intro b hb
    have hsplit := (subset_degree_split_le hb).trans hD
    have hRdegree : (∑ j : Fin r, b (Sum.inl j)) ≤ D := by omega
    have hSdegree := (subsetSDegree_mem hb).trans hS
    let aR : MIndex r D := fun j =>
      ⟨b (Sum.inl j), Nat.lt_succ_of_le
        ((Finset.single_le_sum (f := fun k : Fin r => b (Sum.inl k))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hRdegree)⟩
    have hRbound : |∏ j : Fin r, c j ^ b (Sum.inl j)| ≤ K ^ D := by
      have h := aR.eval_bounded c K hKpos hc
      change |∏ j : Fin r, c j ^ b (Sum.inl j)| ≤
        K ^ (∑ j : Fin r, b (Sum.inl j)) at h
      exact h.trans (pow_le_pow_right₀ hK hRdegree)
    have hSbound : |∏ i : Fin s, z i ^ b (Sum.inr i)| ≤ jointClock N z := by
      exact abs_eval_le_jointClock hN (subsetExponent b hSdegree).1
        (subsetExponent b hSdegree).2 z
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, eq_ratCast, abs_mul]
    calc
      _ ≤ |((q.coeff b : ℚ) : ℝ)| * (K ^ D * jointClock N z) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hRbound hSbound (abs_nonneg _) (pow_nonneg hKzero _))
          (abs_nonneg _)
      _ = _ := by ring
  rw [MvPolynomial.eval₂_eq' (Rat.castHom ℝ) (Sum.elim c z) q]
  calc
    _ ≤ ∑ b ∈ q.support,
        |(Rat.castHom ℝ) (q.coeff b) *
          ∏ j : Fin r ⊕ Fin s, (Sum.elim c z) j ^ b j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ q.support, |((q.coeff b : ℚ) : ℝ)| * K ^ D * jointClock N z :=
      Finset.sum_le_sum hterm
    _ = subsetCoefficientSum q * K ^ D * jointClock N z := by
      simp only [subsetCoefficientSum, Finset.sum_mul]

theorem subsetField_abs_le (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) {N D : ℕ} (hN : Even N)
    (hS : ∀ i, subsetSDegree (rename e (P.field i)) ≤ N)
    (hD : ∀ i, (P.field i).totalDegree ≤ D) {K : ℝ} (hK : 1 ≤ K)
    (y : Fin d → ℝ) (hR : ∀ j, |subsetRetained e y j| ≤ K) (i : Fin d) :
    |P.evalField y i| ≤
      subsetCoefficientMaximum P e * K ^ D * subsetClock e N y := by
  have h := subset_abs_eval_le hN (hS i)
    ((totalDegree_rename_le e _).trans (hD i))
    (subsetRetained e y) (subsetSource e y) hK hR
  have hfirst : |P.evalField y i| ≤
      subsetCoefficientSum (rename e (P.field i)) * K ^ D * subsetClock e N y := by
    simpa only [eval₂_rename, subset_reassemble, PolyPIVP.evalField, subsetClock] using h
  exact hfirst.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (subsetCoefficientSum_le_maximum P e i)
        (pow_nonneg (zero_le_one.trans hK) _))
      (subsetClock_pos e hN y).le)

/-! ## A clock controlled by an explicit field bound -/

open MaximalPIVP

/-- The coordinate displacement is controlled by the clock integral.
The factor A is explicit, and the field estimate is required only on
the actual forward source interval. -/
theorem forward_coordinate_displacement_le_clock {d : ℕ} {P : PolyPIVP d}
    (u : ForwardSolution P) (q : (Fin d → ℝ) → ℝ)
    (hqc : Continuous q) (A : ℝ)
    (hbound : ∀ t ∈ forwardInterval u.lifetime, ∀ i,
      |P.evalField (u.trajectory t) i| ≤ A * q (u.trajectory t))
    {t : ℝ} (ht : t ∈ forwardInterval u.lifetime) (i : Fin d) :
    |u.trajectory t i - u.trajectory 0 i| ≤
      A * clockIntegral (fun v => q (u.trajectory v)) t := by
  have hmem : ∀ v ∈ Set.Icc 0 t, v ∈ forwardInterval u.lifetime :=
    fun v hv => ⟨hv.1, (ENNReal.ofReal_le_ofReal hv.2).trans_lt ht.2⟩
  have hyc : ContinuousOn u.trajectory (Set.Icc 0 t) :=
    fun v hv => (u.ode v (hmem v hv)).continuousAt.continuousWithinAt
  have hfc : ContinuousOn (fun v => P.evalField (u.trajectory v) i)
      (Set.Icc 0 t) :=
    ((continuous_apply i).comp P.continuous_evalField).comp_continuousOn hyc
  have hderiv : ∀ v ∈ Set.uIcc 0 t,
      HasDerivAt (fun w => u.trajectory w i)
        (P.evalField (u.trajectory v) i) v := by
    intro v hv
    rw [Set.uIcc_of_le ht.1] at hv
    exact hasDerivAt_pi.mp (u.ode v (hmem v hv)) i
  have hftc :
      (∫ v in (0 : ℝ)..t, P.evalField (u.trajectory v) i) =
        u.trajectory t i - u.trajectory 0 i :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hfc.intervalIntegrable_of_Icc ht.1)
  rw [← hftc]
  calc
    |∫ v in (0 : ℝ)..t, P.evalField (u.trajectory v) i|
        ≤ ∫ v in (0 : ℝ)..t, |P.evalField (u.trajectory v) i| :=
      intervalIntegral.abs_integral_le_integral_abs ht.1
    _ ≤ ∫ v in (0 : ℝ)..t, A * q (u.trajectory v) :=
      intervalIntegral.integral_mono_on (μ := volume) ht.1
        (hfc.abs.intervalIntegrable_of_Icc ht.1)
        ((continuousOn_const.mul
          (hqc.comp_continuousOn hyc)).intervalIntegrable_of_Icc ht.1)
        (fun v hv => hbound v (hmem v hv) i)
    _ = A * clockIntegral (fun v => q (u.trajectory v)) t := by
      unfold clockIntegral
      exact intervalIntegral.integral_const_mul _ _

/-- Finite maximality forces this clock integral to be unbounded.
No norm blow-up or clock-divergence hypothesis is assumed. -/
theorem clockIntegral_not_bddAbove_of_finite {d : ℕ} {P : PolyPIVP d}
    (u : MaximalSolution P) (hfin : u.lifetime ≠ ⊤)
    (q : (Fin d → ℝ) → ℝ) (hqc : Continuous q)
    (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ t ∈ forwardInterval u.lifetime, ∀ i,
      |P.evalField (u.trajectory t) i| ≤ A * q (u.trajectory t)) :
    ¬ BddAbove
      (clockIntegral (fun v => q (u.trajectory v)) ''
        Set.Ico 0 u.lifetime.toReal) := by
  rintro ⟨B, hB⟩
  apply u.not_bddAbove_of_finite hfin
  refine ⟨(∑ i, |u.trajectory 0 i|) + A * max B 0, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have htmem : t ∈ forwardInterval u.lifetime := by
    rwa [forwardInterval_finite u.positive hfin]
  have hclock :
      clockIntegral (fun v => q (u.trajectory v)) t ≤ max B 0 :=
    (hB ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  have hcoord : ∀ i,
      |u.trajectory t i| ≤ |u.trajectory 0 i| + A * max B 0 := by
    intro i
    have hd := forward_coordinate_displacement_le_clock
      u.toForwardSolution q hqc A hbound htmem i
    have ha := abs_sub_abs_le_abs_sub (u.trajectory t i) (u.trajectory 0 i)
    have hb := mul_le_mul_of_nonneg_left hclock hA
    linarith
  refine (pi_norm_le_iff_of_nonneg ?_).mpr fun i => ?_
  · exact add_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)
      (mul_nonneg hA (le_max_right _ _))
  · rw [Real.norm_eq_abs]
    have hi : |u.trajectory 0 i| ≤ ∑ j, |u.trajectory 0 j| :=
      Finset.single_le_sum (f := fun j => |u.trajectory 0 j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    exact (hcoord i).trans (by linarith)

/-- Complete inverse-clock data for a forward source. The continuous total
curve agrees with the supplied source representative at nonnegative
compiled times. -/
structure ForwardClockChange {d : ℕ} {P : PolyPIVP d}
    (u : ForwardSolution P) (q : (Fin d → ℝ) → ℝ) where
  inverse : ℝ → ℝ
  inverse_zero : inverse 0 = 0
  inverse_continuous : Continuous inverse
  inverse_strictMono : StrictMono inverse
  inverse_mem : ∀ τ, 0 ≤ τ → inverse τ ∈ forwardInterval u.lifetime
  left_inverse : ∀ t ∈ forwardInterval u.lifetime,
    inverse (clockIntegral (fun v => q (u.trajectory v)) t) = t
  right_inverse : ∀ τ, 0 ≤ τ →
    clockIntegral (fun v => q (u.trajectory v)) (inverse τ) = τ
  inverse_deriv : ∀ τ, 0 ≤ τ →
    HasDerivAt inverse (q (u.trajectory (inverse τ)))⁻¹ τ
  inverse_limit : Tendsto inverse atTop (endpointFilter u.lifetime)
  curve : ℝ → Fin d → ℝ
  curve_continuous : Continuous curve
  curve_eq : ∀ τ, 0 ≤ τ → curve τ = u.trajectory (inverse τ)
  curve_initial : curve 0 = fun i => (P.init i : ℝ)
  curve_deriv : ∀ τ, 0 ≤ τ → ∀ i,
    HasDerivAt (fun σ => curve σ i)
      (P.evalField (curve τ) i / q (curve τ)) τ

/-- Infinite source lifespans require only a continuous clock at least one. -/
theorem exists_forwardClockChange_of_global {d : ℕ} {P : PolyPIVP d}
    (u : ForwardSolution P) (htop : u.lifetime = ⊤)
    (q : (Fin d → ℝ) → ℝ) (hqc : Continuous q)
    (hqone : ∀ y, 1 ≤ q y) :
    Nonempty (ForwardClockChange u q) := by
  let sol := u.toGlobal htop
  obtain ⟨solc, hcont, heq⟩ := sol.exists_continuous
  have hagree : ∀ t, 0 ≤ t → solc.trajectory t = u.trajectory t :=
    fun t ht => heq t ht
  have hρc : Continuous (fun t => q (solc.trajectory t)) :=
    hqc.comp hcont
  have hρ : ∀ t, 1 ≤ q (solc.trajectory t) :=
    fun t => hqone _
  obtain ⟨s, hs, hsd, hsc, hsm, hst, hsθ, hθs⟩ :=
    exists_inverse_timeChange hρc hρ
  have hnonneg : ∀ τ, 0 ≤ τ → 0 ≤ s τ :=
    fun τ hτ => hs ▸ hsm.monotone hτ
  have hclock : ∀ t, 0 ≤ t →
      clockIntegral (fun v => q (u.trajectory v)) t =
        clockIntegral (fun v => q (solc.trajectory v)) t := by
    intro t ht
    unfold clockIntegral
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le ht] at hv
    change q (u.trajectory v) = q (solc.trajectory v)
    rw [hagree v hv.1]
  refine ⟨{
    inverse := s
    inverse_zero := hs
    inverse_continuous := hsc
    inverse_strictMono := hsm
    inverse_mem := fun τ hτ => ⟨hnonneg τ hτ, by simp [htop]⟩
    left_inverse := ?_
    right_inverse := ?_
    inverse_deriv := ?_
    inverse_limit := by simpa only [endpointFilter, if_pos htop] using hst
    curve := fun τ => solc.trajectory (s τ)
    curve_continuous := hcont.comp hsc
    curve_eq := fun τ hτ => hagree (s τ) (hnonneg τ hτ)
    curve_initial := by rw [hs, solc.init_cond]; rfl
    curve_deriv := ?_ }⟩
  · intro t ht
    rw [hclock t ht.1]
    exact hsθ t
  · intro τ hτ
    rw [hclock (s τ) (hnonneg τ hτ)]
    exact hθs τ
  · intro τ hτ
    simpa only [hagree (s τ) (hnonneg τ hτ)] using hsd τ
  · intro τ hτ i
    have h := (solc.is_solution (s τ) (hnonneg τ hτ)).scomp τ (hsd τ)
    refine (hasDerivAt_pi.mp h i).congr_deriv ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_eq_inv_mul]; rfl

/-- A global supplied solution is admitted without an extra maximality
or negative-time continuity premise. -/
theorem exists_globalClockChange {d : ℕ} {P : PolyPIVP d}
    (sol : PIVP.Solution P.toPIVP) (q : (Fin d → ℝ) → ℝ)
    (hqc : Continuous q) (hqone : ∀ y, 1 ≤ q y) :
    Nonempty (ForwardClockChange (ForwardSolution.ofGlobal sol) q) :=
  exists_forwardClockChange_of_global (ForwardSolution.ofGlobal sol)
    rfl q hqc hqone

/-- A single interface for finite and infinite maximal source lifespans.
The finite branch derives divergence from maximality and the explicit
constant A controlling the field. -/
theorem exists_maximalClockChange {d : ℕ} {P : PolyPIVP d}
    (u : MaximalSolution P) (q : (Fin d → ℝ) → ℝ)
    (hqc : Continuous q) (hqone : ∀ y, 1 ≤ q y)
    (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ t ∈ forwardInterval u.lifetime, ∀ i,
      |P.evalField (u.trajectory t) i| ≤ A * q (u.trajectory t)) :
    Nonempty (ForwardClockChange u.toForwardSolution q) := by
  classical
  by_cases htop : u.lifetime = ⊤
  · exact exists_forwardClockChange_of_global u.toForwardSolution htop q hqc hqone
  · have hT := u.finite_time_pos htop
    obtain ⟨y, hc, hagree, hd⟩ :=
      exists_extension_Iio hT u.trajectory (u.ode_finite htop)
    have hclock : ∀ t, 0 ≤ t →
        clockIntegral (fun v => q (u.trajectory v)) t =
          clockIntegral (fun v => q (y v)) t := by
      intro t ht
      unfold clockIntegral
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le ht] at hv
      change q (u.trajectory v) = q (y v)
      rw [hagree v hv.1]
    have hunb := clockIntegral_not_bddAbove_of_finite u htop q hqc A hA hbound
    have hθunb : ¬ BddAbove
        (clockIntegral (fun v => q (y v)) '' Set.Ico 0 u.lifetime.toReal) := by
      rintro ⟨B, hB⟩
      apply hunb
      refine ⟨B, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      rw [hclock t ht.1]
      exact hB ⟨t, ht, rfl⟩
    have hρc : ContinuousOn (fun t => q (y t)) (Set.Iio u.lifetime.toReal) :=
      hqc.comp_continuousOn hc
    have hρ : ∀ t, 1 ≤ q (y t) := fun t => hqone _
    obtain ⟨s, hs, hsT, hsd, hsc, hsm, hst, hsθ⟩ :=
      exists_inverse_timeChange_Iio hT hρc hρ hθunb
    have hnonneg : ∀ τ, 0 ≤ τ → 0 ≤ s τ :=
      fun τ hτ => hs ▸ hsm.monotone hτ
    have hmem : ∀ τ, 0 ≤ τ → s τ ∈ forwardInterval u.lifetime := by
      intro τ hτ
      rw [forwardInterval_finite u.positive htop]
      exact ⟨hnonneg τ hτ, hsT τ⟩
    have hθs : ∀ τ, clockIntegral (fun v => q (y v)) (s τ) = τ :=
      fun τ => hsm.injective (hsθ (s τ) (hsT τ))
    refine ⟨{
      inverse := s
      inverse_zero := hs
      inverse_continuous := hsc
      inverse_strictMono := hsm
      inverse_mem := hmem
      left_inverse := ?_
      right_inverse := ?_
      inverse_deriv := ?_
      inverse_limit := by simpa only [endpointFilter, if_neg htop] using hst
      curve := fun τ => y (s τ)
      curve_continuous := hc.comp_continuous hsc (fun τ => hsT τ)
      curve_eq := fun τ hτ => hagree (s τ) (hnonneg τ hτ)
      curve_initial := by rw [hs, hagree 0 le_rfl, u.initial]
      curve_deriv := ?_ }⟩
    · intro t ht
      have ht' : t ∈ Set.Ico 0 u.lifetime.toReal := by
        rwa [forwardInterval_finite u.positive htop] at ht
      rw [hclock t ht'.1]
      exact hsθ t ht'.2
    · intro τ hτ
      rw [hclock (s τ) (hnonneg τ hτ)]
      exact hθs τ
    · intro τ hτ
      simpa only [hagree (s τ) (hnonneg τ hτ)] using hsd τ
    · intro τ hτ i
      have h := (hd (s τ) ⟨hnonneg τ hτ, hsT τ⟩).scomp τ (hsd τ)
      refine (hasDerivAt_pi.mp h i).congr_deriv ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_eq_inv_mul]

theorem forward_clockIntegral_nonneg {d : ℕ} {P : PolyPIVP d}
    (u : ForwardSolution P) (q : (Fin d → ℝ) → ℝ)
    (hqone : ∀ y, 1 ≤ q y) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ clockIntegral (fun v => q (u.trajectory v)) t :=
  intervalIntegral.integral_nonneg ht
    (fun v _ => zero_le_one.trans (hqone (u.trajectory v)))

theorem ForwardClockChange.clock_strictMonoOn {d : ℕ} {P : PolyPIVP d}
    {u : ForwardSolution P} {q : (Fin d → ℝ) → ℝ}
    (tc : ForwardClockChange u q) :
    StrictMonoOn (clockIntegral (fun v => q (u.trajectory v)))
      (forwardInterval u.lifetime) := by
  intro a ha b hb hab
  by_contra h
  have hm := tc.inverse_strictMono.monotone (not_lt.mp h)
  rw [tc.left_inverse b hb, tc.left_inverse a ha] at hm
  exact (not_le_of_gt hab) hm

theorem ForwardClockChange.clock_bijOn {d : ℕ} {P : PolyPIVP d}
    {u : ForwardSolution P} {q : (Fin d → ℝ) → ℝ}
    (tc : ForwardClockChange u q) (hqone : ∀ y, 1 ≤ q y) :
    Set.BijOn (clockIntegral (fun v => q (u.trajectory v)))
      (forwardInterval u.lifetime) (Set.Ici 0) := by
  refine ⟨fun t ht => forward_clockIntegral_nonneg u q hqone ht.1, ?_, ?_⟩
  · intro a ha b hb hab
    have h := congrArg tc.inverse hab
    simpa only [tc.left_inverse a ha, tc.left_inverse b hb] using h
  · intro τ hτ
    exact ⟨tc.inverse τ, tc.inverse_mem τ hτ, tc.right_inverse τ hτ⟩

theorem ForwardClockChange.inverse_image {d : ℕ} {P : PolyPIVP d}
    {u : ForwardSolution P} {q : (Fin d → ℝ) → ℝ}
    (tc : ForwardClockChange u q) (hqone : ∀ y, 1 ≤ q y) :
    tc.inverse '' Set.Ici 0 = forwardInterval u.lifetime := by
  ext t
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact tc.inverse_mem τ hτ
  · intro ht
    exact ⟨clockIntegral (fun v => q (u.trajectory v)) t,
      forward_clockIntegral_nonneg u q hqone ht.1, tc.left_inverse t ht⟩

/-- The actual inverse derivative lies in (0,1] at every forward compiled time. -/
theorem ForwardClockChange.inverse_derivative_bounds {d : ℕ} {P : PolyPIVP d}
    {u : ForwardSolution P} {q : (Fin d → ℝ) → ℝ}
    (tc : ForwardClockChange u q) (hqone : ∀ y, 1 ≤ q y)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    0 < deriv tc.inverse τ ∧ deriv tc.inverse τ ≤ 1 := by
  rw [(tc.inverse_deriv τ hτ).deriv]
  have hp : 0 < q (u.trajectory (tc.inverse τ)) :=
    zero_lt_one.trans_le (hqone _)
  refine ⟨inv_pos.mpr hp, ?_⟩
  simpa only [one_div] using (div_le_one hp).mpr (hqone _)

/-- The source clock tends to infinity at its finite or infinite endpoint. -/
theorem ForwardClockChange.clock_tendsto {d : ℕ} {P : PolyPIVP d}
    {u : ForwardSolution P} {q : (Fin d → ℝ) → ℝ}
    (tc : ForwardClockChange u q) :
    Tendsto (clockIntegral (fun v => q (u.trajectory v)))
      (endpointFilter u.lifetime) atTop := by
  classical
  rw [Filter.tendsto_atTop]
  intro B
  let τ : ℝ := max B 0
  have hτ : 0 ≤ τ := le_max_right _ _
  have hmem := tc.inverse_mem τ hτ
  by_cases htop : u.lifetime = ⊤
  · simp only [endpointFilter, if_pos htop]
    filter_upwards [eventually_gt_atTop (tc.inverse τ)] with t ht
    have htmem : t ∈ forwardInterval u.lifetime :=
      ⟨hmem.1.trans ht.le, by simp [htop]⟩
    have hθ := tc.clock_strictMonoOn hmem htmem ht
    rw [tc.right_inverse τ hτ] at hθ
    exact (le_max_left B 0).trans hθ.le
  · have hmem' : tc.inverse τ ∈ Set.Ico 0 u.lifetime.toReal := by
      rwa [forwardInterval_finite u.positive htop] at hmem
    have hlarge : ∀ᶠ t in nhdsWithin u.lifetime.toReal (Set.Iio u.lifetime.toReal),
        tc.inverse τ < t :=
      (show ∀ᶠ t in 𝓝 u.lifetime.toReal, tc.inverse τ < t from
        Ioi_mem_nhds hmem'.2).filter_mono nhdsWithin_le_nhds
    simp only [endpointFilter, if_neg htop]
    filter_upwards [hlarge, self_mem_nhdsWithin] with t ht hT
    have htmem : t ∈ forwardInterval u.lifetime := by
      rw [forwardInterval_finite u.positive htop]
      exact ⟨hmem'.1.trans ht.le, hT⟩
    have hθ := tc.clock_strictMonoOn (tc.inverse_mem τ hτ) htmem ht
    rw [tc.right_inverse τ hτ] at hθ
    exact (le_max_left B 0).trans hθ.le

theorem ForwardClockChange.coordinate_limit {d : ℕ} {P : PolyPIVP d}
    {u : ForwardSolution P} {q : (Fin d → ℝ) → ℝ}
    (tc : ForwardClockChange u q) (i : Fin d) {L : ℝ}
    (hlim : Tendsto (fun t => u.trajectory t i)
      (endpointFilter u.lifetime) (𝓝 L)) :
    Tendsto (fun τ => u.trajectory (tc.inverse τ) i) atTop (𝓝 L) :=
  hlim.comp tc.inverse_limit

/-! ## Exact trajectories, evolving retained coordinates, and boundedness -/

/-- The actual retained coordinates, copied outputs, and subset surrogates. -/
def subsetMap (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    (N : ℕ) (y : Fin d → ℝ) : SubsetIndex r s m N → ℝ
  | Sum.inl j => subsetRetained e y j
  | Sum.inr (Sum.inl j) => y (o j)
  | Sum.inr (Sum.inr a) => jointSurrogate N a (subsetSource e y)

def subsetCurve (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    (N : ℕ) (z : ℝ → Fin d → ℝ) (τ : ℝ) :
    SubsetIndex r s m N → ℝ :=
  subsetMap e o N (z τ)

/-- The original coordinate represented by the selected retained or copied output. -/
def subsetOutputSource (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d) :
    Fin r ⊕ Fin m → Fin d
  | Sum.inl j => e.symm (Sum.inl j)
  | Sum.inr j => o j

theorem subsetCompile_output (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    (N : ℕ) (out : Fin r ⊕ Fin m) :
    (subsetCompile P e o N out).output =
      Fintype.equivFin (SubsetIndex r s m N) (subsetOutputIndex out) := rfl

theorem subsetMap_output (e : Fin d ≃ (Fin r ⊕ Fin s))
    (o : Fin m → Fin d) (N : ℕ) (out : Fin r ⊕ Fin m) (y : Fin d → ℝ) :
    subsetMap e o N y (subsetOutputIndex out) = y (subsetOutputSource e o out) := by
  cases out <;> rfl

theorem subsetMap_initial (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    (N : ℕ) (k : SubsetIndex r s m N) :
    subsetMap e o N (fun i => (P.init i : ℝ)) k =
      (subsetInit P e o N k : ℝ) := by
  rcases k with j | j | a
  · rfl
  · rfl
  · simp [subsetMap, subsetInit, subsetSource, jointSurrogate, jointClock, MIndex.eval]

theorem subsetMap_continuous (e : Fin d ≃ (Fin r ⊕ Fin s))
    (o : Fin m → Fin d) {N : ℕ} (hN : Even N) :
    Continuous (subsetMap e o N) := by
  refine continuous_pi fun k => ?_
  rcases k with j | j | a
  · exact continuous_apply (e.symm (Sum.inl j))
  · exact continuous_apply (o j)
  · exact (continuous_jointSurrogate hN a).comp (continuous_subsetSource e)

/-- Retained coordinates satisfy their scaled source equations; they need not be constant. -/
theorem subsetCurve_hasDerivAt (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    {N : ℕ} (hN : Even N)
    (hS : ∀ i, subsetSDegree (rename e (P.field i)) ≤ N)
    (z : ℝ → Fin d → ℝ) (τ : ℝ)
    (hz : ∀ i, HasDerivAt (fun σ => z σ i)
      (P.evalField (z τ) i / subsetClock e N (z τ)) τ)
    (k : SubsetIndex r s m N) :
    HasDerivAt (fun σ => subsetCurve e o N z σ k)
      ((subsetField P e o N k).eval₂ (Rat.castHom ℝ)
        (subsetCurve e o N z τ)) τ := by
  have hl : ∀ i,
      (subsetFieldLift P e N i).eval₂ (Rat.castHom ℝ)
        (subsetCurve e o N z τ) =
      P.evalField (z τ) i / subsetClock e N (z τ) :=
    fun i => subsetFieldLift_eval P e hS (z τ)
      (subsetCurve e o N z τ) (fun _ => rfl) (fun _ => rfl) i
  rcases k with j | j | a
  · change HasDerivAt (fun σ => z σ (e.symm (Sum.inl j)))
      ((subsetFieldLift P e N (e.symm (Sum.inl j))).eval₂
        (Rat.castHom ℝ) (subsetCurve e o N z τ)) τ
    rw [hl]
    exact hz (e.symm (Sum.inl j))
  · change HasDerivAt (fun σ => z σ (o j))
      ((subsetFieldLift P e N (o j)).eval₂
        (Rat.castHom ℝ) (subsetCurve e o N z τ)) τ
    rw [hl]
    exact hz (o j)
  · have hzS : ∀ i, HasDerivAt (fun σ => subsetSource e (z σ) i)
        (P.evalField (z τ) (e.symm (Sum.inr i)) /
          jointClock N (subsetSource e (z τ))) τ := by
      intro i
      exact hz (e.symm (Sum.inr i))
    have hd := hasDerivAt_jointSurrogate_of hN a
      (fun σ => subsetSource e (z σ)) τ
      (fun i => P.evalField (z τ) (e.symm (Sum.inr i))) hzS
    refine hd.congr_deriv ?_
    simp only [subsetField, eval₂_sub, eval₂_mul, eval₂_sum, eval₂_C, eval₂_X,
      hl, eq_ratCast, Rat.cast_natCast] <;> rfl

/-- The complete indexed trajectory solves the rational compiled PIVP.
Forward uniqueness is a consequence of polynomial ODE uniqueness. -/
theorem subsetCompile_solution_of_curve (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    {N : ℕ} (out : Fin r ⊕ Fin m) (hN : Even N)
    (hS : ∀ i, subsetSDegree (rename e (P.field i)) ≤ N)
    (z : ℝ → Fin d → ℝ)
    (hzInitial : z 0 = fun i => (P.init i : ℝ))
    (hz : ∀ τ, 0 ≤ τ → ∀ i, HasDerivAt (fun σ => z σ i)
      (P.evalField (z τ) i / subsetClock e N (z τ)) τ) :
    ∃ sol : PIVP.Solution (subsetCompile P e o N out).toPIVP,
      (∀ τ k, sol.trajectory τ (Fintype.equivFin (SubsetIndex r s m N) k) =
        subsetCurve e o N z τ k) ∧
      (Continuous z → Continuous sol.trajectory) ∧
      (∀ other : PIVP.Solution (subsetCompile P e o N out).toPIVP,
        Set.EqOn other.trajectory sol.trajectory (Set.Ici 0)) := by
  have hInitial : ∀ k, subsetCurve e o N z 0 k = (subsetInit P e o N k : ℝ) := by
    intro k
    change subsetMap e o N (z 0) k = _
    rw [hzInitial]
    exact subsetMap_initial P e o N k
  have hDerivative : ∀ τ, 0 ≤ τ → ∀ k,
      HasDerivAt (fun σ => subsetCurve e o N z σ k)
        ((subsetField P e o N k).eval₂ (Rat.castHom ℝ)
          (subsetCurve e o N z τ)) τ :=
    fun τ hτ k => subsetCurve_hasDerivAt P e o hN hS z τ (hz τ hτ) k
  obtain ⟨sol, hsol⟩ := PolyPIVP.ofIndexed_solution
    (subsetField P e o N) (subsetInit P e o N) (subsetOutputIndex out)
    (subsetCurve e o N z) hInitial hDerivative
  refine ⟨sol, ?_, ?_, ?_⟩
  · intro τ k
    rw [hsol]
    simp only [Equiv.symm_apply_apply]
  · intro hzc
    rw [hsol]
    have hZ : Continuous (subsetCurve e o N z) :=
      (subsetMap_continuous e o hN).comp hzc
    exact continuous_pi fun j => (continuous_apply _).comp hZ
  · intro other
    exact MaximalPIVP.global_solution_unique _ other sol

/-- A uniform bound for every coordinate, including the evolving retained block. -/
theorem subsetMap_norm_le (e : Fin d ≃ (Fin r ⊕ Fin s))
    (o : Fin m → Fin d) {N : ℕ} (hN : Even N) (y : Fin d → ℝ)
    {K M : ℝ} (hR : ∀ j, |subsetRetained e y j| ≤ K)
    (hO : ∀ j, |y (o j)| ≤ M) :
    ‖subsetMap e o N y‖ ≤ max (max K M) 1 := by
  refine (pi_norm_le_iff_of_nonneg
    (zero_le_one.trans (le_max_right (max K M) 1))).mpr ?_
  intro k
  rw [Real.norm_eq_abs]
  rcases k with j | j | a
  · exact (hR j).trans ((le_max_left K M).trans (le_max_left (max K M) 1))
  · exact (hO j).trans ((le_max_right K M).trans (le_max_left (max K M) 1))
  · exact (jointSurrogate_abs_le_one hN a (subsetSource e y)).trans
      (le_max_right (max K M) 1)

theorem subsetCompile_norm_le (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    {N : ℕ} (out : Fin r ⊕ Fin m) (hN : Even N)
    (sol : PIVP.Solution (subsetCompile P e o N out).toPIVP)
    (z : ℝ → Fin d → ℝ)
    (hcoord : ∀ τ, 0 ≤ τ → ∀ k,
      sol.trajectory τ (Fintype.equivFin (SubsetIndex r s m N) k) =
        subsetCurve e o N z τ k)
    {K M : ℝ}
    (hR : ∀ τ, 0 ≤ τ → ∀ j, |subsetRetained e (z τ) j| ≤ K)
    (hO : ∀ τ, 0 ≤ τ → ∀ j, |z τ (o j)| ≤ M) :
    ∀ τ, 0 ≤ τ → ‖sol.trajectory τ‖ ≤ max (max K M) 1 := by
  intro τ hτ
  refine (pi_norm_le_iff_of_nonneg
    (zero_le_one.trans (le_max_right (max K M) 1))).mpr ?_
  intro j
  obtain ⟨k, rfl⟩ := (Fintype.equivFin (SubsetIndex r s m N)).surjective j
  rw [hcoord τ hτ]
  exact (norm_le_pi_norm (subsetMap e o N (z τ)) k).trans
    (subsetMap_norm_le e o hN (z τ) (hR τ hτ) (hO τ hτ))

theorem subsetCompile_isBounded (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    {N : ℕ} (out : Fin r ⊕ Fin m) (hN : Even N)
    (sol : PIVP.Solution (subsetCompile P e o N out).toPIVP)
    (z : ℝ → Fin d → ℝ)
    (hcoord : ∀ τ, 0 ≤ τ → ∀ k,
      sol.trajectory τ (Fintype.equivFin (SubsetIndex r s m N) k) =
        subsetCurve e o N z τ k)
    {K M : ℝ}
    (hR : ∀ τ, 0 ≤ τ → ∀ j, |subsetRetained e (z τ) j| ≤ K)
    (hO : ∀ τ, 0 ≤ τ → ∀ j, |z τ (o j)| ≤ M) :
    (subsetCompile P e o N out).toPIVP.IsBounded sol.trajectory :=
  ⟨max (max K M) 1, lt_max_of_lt_right one_pos,
    subsetCompile_norm_le P e o out hN sol z hcoord hR hO⟩

/-- Feed an actual inverse-clock solution into the indexed polynomial compiler. -/
theorem subsetCompile_solution_of_clock (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    {N : ℕ} (out : Fin r ⊕ Fin m) (hN : Even N)
    (hS : ∀ i, subsetSDegree (rename e (P.field i)) ≤ N)
    (u : MaximalPIVP.ForwardSolution P)
    (tc : ForwardClockChange u (subsetClock e N)) :
    ∃ sol : PIVP.Solution (subsetCompile P e o N out).toPIVP,
      Continuous sol.trajectory ∧
      (∀ τ, 0 ≤ τ → ∀ k,
        sol.trajectory τ (Fintype.equivFin (SubsetIndex r s m N) k) =
          subsetCurve e o N (fun σ => u.trajectory (tc.inverse σ)) τ k) ∧
      (∀ other : PIVP.Solution (subsetCompile P e o N out).toPIVP,
        Set.EqOn other.trajectory sol.trajectory (Set.Ici 0)) := by
  obtain ⟨sol, hcoord, hc, hu⟩ :=
    subsetCompile_solution_of_curve P e o out hN hS
      tc.curve tc.curve_initial tc.curve_deriv
  refine ⟨sol, hc tc.curve_continuous, ?_, hu⟩
  intro τ hτ k
  rw [hcoord τ k]
  change subsetMap e o N (tc.curve τ) k =
    subsetMap e o N (u.trajectory (tc.inverse τ)) k
  rw [tc.curve_eq τ hτ]

/-- Every retained or copied readout preserves its finite source endpoint limit. -/
theorem subsetCompile_readout_limit (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    {N : ℕ} (out : Fin r ⊕ Fin m)
    (u : MaximalPIVP.ForwardSolution P)
    (tc : ForwardClockChange u (subsetClock e N))
    (sol : PIVP.Solution (subsetCompile P e o N out).toPIVP)
    (hcoord : ∀ τ, 0 ≤ τ → ∀ k,
      sol.trajectory τ (Fintype.equivFin (SubsetIndex r s m N) k) =
        subsetCurve e o N (fun σ => u.trajectory (tc.inverse σ)) τ k)
    (readout : Fin r ⊕ Fin m) {L : ℝ}
    (hlim : Tendsto (fun t => u.trajectory t (subsetOutputSource e o readout))
      (MaximalPIVP.endpointFilter u.lifetime) (𝓝 L)) :
    Tendsto (fun τ => sol.trajectory τ
      (Fintype.equivFin (SubsetIndex r s m N) (subsetOutputIndex readout)))
      atTop (𝓝 L) := by
  refine (hlim.comp tc.inverse_limit).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
  have hout :
      sol.trajectory τ
          (Fintype.equivFin (SubsetIndex r s m N) (subsetOutputIndex readout)) =
        u.trajectory (tc.inverse τ) (subsetOutputSource e o readout) := by
    rw [hcoord τ hτ]
    exact subsetMap_output e o N readout _
  exact hout.symm

/-- The selected original coordinate has exactly the same finite endpoint limit. -/
theorem subsetCompile_output_limit (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    {N : ℕ} (out : Fin r ⊕ Fin m)
    (u : MaximalPIVP.ForwardSolution P)
    (tc : ForwardClockChange u (subsetClock e N))
    (sol : PIVP.Solution (subsetCompile P e o N out).toPIVP)
    (hcoord : ∀ τ, 0 ≤ τ → ∀ k,
      sol.trajectory τ (Fintype.equivFin (SubsetIndex r s m N) k) =
        subsetCurve e o N (fun σ => u.trajectory (tc.inverse σ)) τ k)
    {L : ℝ}
    (hlim : Tendsto (fun t => u.trajectory t (subsetOutputSource e o out))
      (MaximalPIVP.endpointFilter u.lifetime) (𝓝 L)) :
    Tendsto (fun τ => sol.trajectory τ (subsetCompile P e o N out).output)
      atTop (𝓝 L) := by
  refine (hlim.comp tc.inverse_limit).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
  have hout :
      sol.trajectory τ (subsetCompile P e o N out).output =
        u.trajectory (tc.inverse τ) (subsetOutputSource e o out) := by
    rw [subsetCompile_output, hcoord τ hτ]
    exact subsetMap_output e o N out _
  exact hout.symm

/-- A finite endpoint limit bounds a coordinate on the entire forward interval. -/
theorem forward_coordinate_bounded_of_limit (P : PolyPIVP d)
    (u : MaximalPIVP.ForwardSolution P) (i : Fin d) {L : ℝ}
    (hlim : Tendsto (fun t => u.trajectory t i)
      (MaximalPIVP.endpointFilter u.lifetime) (𝓝 L)) :
    ∃ M : ℝ, 0 < M ∧ ∀ t ∈ MaximalPIVP.forwardInterval u.lifetime,
      |u.trajectory t i| ≤ M := by
  by_cases htop : u.lifetime = ⊤
  · have hlim' : Tendsto (fun t => u.trajectory t i) atTop (𝓝 L) := by
      simpa [MaximalPIVP.endpointFilter, htop] using hlim
    obtain ⟨M, hM, hb⟩ := exists_abs_le_of_tendsto
      (fun t ht => (continuous_apply i).continuousAt.comp
        ((u.ode t ⟨ht, by simp [htop]⟩).continuousAt)) hlim'
    exact ⟨M, hM, fun t ht => hb t ht.1⟩
  · have hT : 0 < u.lifetime.toReal :=
      ENNReal.toReal_pos u.positive.ne' htop
    have hlim' : Tendsto (fun t => u.trajectory t i)
        (nhdsWithin u.lifetime.toReal (Set.Iio u.lifetime.toReal)) (𝓝 L) := by
      simpa [MaximalPIVP.endpointFilter, htop] using hlim
    obtain ⟨M, hM, hb⟩ := exists_abs_le_of_tendsto_Iio hT
      (fun t ht => (continuous_apply i).continuousAt.comp
        ((u.ode t (by
          rw [MaximalPIVP.forwardInterval_finite u.positive htop]
          exact ht)).continuousAt)) hlim'
    refine ⟨M, hM, fun t ht => hb t ?_⟩
    rwa [MaximalPIVP.forwardInterval_finite u.positive htop] at ht

/-- A finite family of copied coordinates with finite limits has one common bound. -/
theorem subsetOutputCopies_bounded_of_limits (P : PolyPIVP d)
    (u : MaximalPIVP.ForwardSolution P) (o : Fin m → Fin d)
    (L : Fin m → ℝ)
    (hlim : ∀ j, Tendsto (fun t => u.trajectory t (o j))
      (MaximalPIVP.endpointFilter u.lifetime) (𝓝 (L j))) :
    ∃ M : ℝ, 0 < M ∧
      ∀ t ∈ MaximalPIVP.forwardInterval u.lifetime, ∀ j, |u.trajectory t (o j)| ≤ M := by
  classical
  have hex : ∀ j : Fin m, ∃ M : ℝ, 0 < M ∧
      ∀ t ∈ MaximalPIVP.forwardInterval u.lifetime, |u.trajectory t (o j)| ≤ M :=
    fun j => forward_coordinate_bounded_of_limit P u (o j) (hlim j)
  choose M hM hb using hex
  have hsum : 0 ≤ ∑ j : Fin m, M j :=
    Finset.sum_nonneg fun j _ => (hM j).le
  refine ⟨1 + ∑ j : Fin m, M j, by linarith, ?_⟩
  intro t ht j
  have hj : M j ≤ ∑ k : Fin m, M k :=
    Finset.single_le_sum (f := fun k : Fin m => M k)
      (fun k _ => (hM k).le) (Finset.mem_univ j)
  exact (hb j t ht).trans (by linarith)

/-! ## Subset-specific constants and complete solution certificates -/

/-- Each compiled semantic field component is explicitly a polynomial over the rationals. -/
theorem subsetCompile_field_is_rational (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    (N : ℕ) (out : Fin r ⊕ Fin m) (j : Fin (subsetDim r s m N)) :
    ∃ q : MvPolynomial (Fin (subsetDim r s m N)) ℚ,
      ∀ y, (subsetCompile P e o N out).toPIVP.field y j =
        q.eval₂ (Rat.castHom ℝ) y :=
  ⟨(subsetCompile P e o N out).field j, fun _ => rfl⟩

theorem subsetCompile_init_eq_subsetMap (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    (N : ℕ) (out : Fin r ⊕ Fin m) (k : SubsetIndex r s m N) :
    (subsetCompile P e o N out).toPIVP.init
        (Fintype.equivFin (SubsetIndex r s m N) k) =
      subsetMap e o N (fun i => (P.init i : ℝ)) k := by
  change (subsetInit P e o N
    ((Fintype.equivFin (SubsetIndex r s m N)).symm
      (Fintype.equivFin (SubsetIndex r s m N) k)) : ℝ) = _
  rw [Equiv.symm_apply_apply]
  exact (subsetMap_initial P e o N k).symm

/-- The field estimate with any explicitly supplied coefficient majorant. -/
theorem subsetField_abs_le_with_constants (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) {N D : ℕ} (hN : Even N)
    (hS : ∀ i, subsetSDegree (rename e (P.field i)) ≤ N)
    (hD : ∀ i, (P.field i).totalDegree ≤ D)
    (K Cp : ℝ) (hK : 1 ≤ K) (hCp : subsetCoefficientMaximum P e ≤ Cp)
    (y : Fin d → ℝ) (hR : ∀ j, |subsetRetained e y j| ≤ K) (i : Fin d) :
    |P.evalField y i| ≤ Cp * K ^ D * subsetClock e N y :=
  (subsetField_abs_le P e hN hS hD hK y hR i).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCp (pow_nonneg (zero_le_one.trans hK) D))
      (subsetClock_pos e hN y).le)

/-- The actual displacement estimate that forces finite-endpoint clock divergence. -/
theorem subset_displacement_le (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) {N D : ℕ} (hN : Even N)
    (hS : ∀ i, subsetSDegree (rename e (P.field i)) ≤ N)
    (hD : ∀ i, (P.field i).totalDegree ≤ D)
    (u : ForwardSolution P) (K Cp : ℝ) (hK : 1 ≤ K)
    (hCp : subsetCoefficientMaximum P e ≤ Cp)
    (hR : ∀ t ∈ forwardInterval u.lifetime, ∀ j,
      |subsetRetained e (u.trajectory t) j| ≤ K)
    {t : ℝ} (ht : t ∈ forwardInterval u.lifetime) (i : Fin d) :
    |u.trajectory t i - (P.init i : ℝ)| ≤
      (Cp * K ^ D) * clockIntegral (fun v => subsetClock e N (u.trajectory v)) t := by
  have h := forward_coordinate_displacement_le_clock u
    (subsetClock e N) (continuous_subsetClock e N) (Cp * K ^ D)
    (fun v hv j => subsetField_abs_le_with_constants P e hN hS hD
      K Cp hK hCp (u.trajectory v) (hR v hv) j) ht i
  simpa only [u.initial] using h

/-- Maximality, bounded retained coordinates, and the explicit polynomial constants
supply a complete inverse clock for either source lifespan. -/
theorem exists_subsetClockChange (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) {N D : ℕ} (hN : Even N)
    (hS : ∀ i, subsetSDegree (rename e (P.field i)) ≤ N)
    (hD : ∀ i, (P.field i).totalDegree ≤ D)
    (u : MaximalSolution P) (K Cp : ℝ) (hK : 1 ≤ K)
    (hCp : subsetCoefficientMaximum P e ≤ Cp)
    (hR : ∀ t ∈ forwardInterval u.lifetime, ∀ j,
      |subsetRetained e (u.trajectory t) j| ≤ K) :
    Nonempty (ForwardClockChange u.toForwardSolution (subsetClock e N)) := by
  have hA : 0 ≤ Cp * K ^ D :=
    mul_nonneg ((subsetCoefficientMaximum_nonneg P e).trans hCp)
      (pow_nonneg (zero_le_one.trans hK) D)
  exact exists_maximalClockChange u (subsetClock e N)
    (continuous_subsetClock e N) (subsetClock_ge_one e hN)
    (Cp * K ^ D) hA
    (fun t ht i => subsetField_abs_le_with_constants P e hN hS hD
      K Cp hK hCp (u.trajectory t) (hR t ht) i)

theorem subsetClock_tendsto_of_maximal (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) {N D : ℕ} (hN : Even N)
    (hS : ∀ i, subsetSDegree (rename e (P.field i)) ≤ N)
    (hD : ∀ i, (P.field i).totalDegree ≤ D)
    (u : MaximalSolution P) (K Cp : ℝ) (hK : 1 ≤ K)
    (hCp : subsetCoefficientMaximum P e ≤ Cp)
    (hR : ∀ t ∈ forwardInterval u.lifetime, ∀ j,
      |subsetRetained e (u.trajectory t) j| ≤ K) :
    Tendsto (clockIntegral (fun v => subsetClock e N (u.trajectory v)))
      (endpointFilter u.lifetime) atTop := by
  obtain ⟨tc⟩ := exists_subsetClockChange P e hN hS hD u K Cp hK hCp hR
  exact tc.clock_tendsto

theorem subsetClock_tendsto_of_finite_maximal (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) {N D : ℕ} (hN : Even N)
    (hS : ∀ i, subsetSDegree (rename e (P.field i)) ≤ N)
    (hD : ∀ i, (P.field i).totalDegree ≤ D)
    (u : MaximalSolution P) (hfin : u.lifetime ≠ ⊤)
    (K Cp : ℝ) (hK : 1 ≤ K) (hCp : subsetCoefficientMaximum P e ≤ Cp)
    (hR : ∀ t ∈ forwardInterval u.lifetime, ∀ j,
      |subsetRetained e (u.trajectory t) j| ≤ K) :
    Tendsto (clockIntegral (fun v => subsetClock e N (u.trajectory v)))
      (nhdsWithin u.lifetime.toReal (Set.Iio u.lifetime.toReal)) atTop := by
  simpa only [endpointFilter, if_neg hfin] using
    subsetClock_tendsto_of_maximal P e hN hS hD u K Cp hK hCp hR

/-- One actual inverse clock and its unique forward compiled trajectory. -/
structure SubsetSolution (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    (N : ℕ) (out : Fin r ⊕ Fin m) (u : ForwardSolution P) where
  clock : ForwardClockChange u (subsetClock e N)
  solution : PIVP.Solution (subsetCompile P e o N out).toPIVP
  continuous : Continuous solution.trajectory
  trajectory_eq : ∀ τ, 0 ≤ τ → ∀ k,
    solution.trajectory τ (Fintype.equivFin (SubsetIndex r s m N) k) =
      subsetCurve e o N (fun σ => u.trajectory (clock.inverse σ)) τ k
  unique : ∀ other : PIVP.Solution (subsetCompile P e o N out).toPIVP,
    Set.EqOn other.trajectory solution.trajectory (Set.Ici 0)

theorem exists_subsetSolution_of_clock (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    {N : ℕ} (out : Fin r ⊕ Fin m) (hN : Even N)
    (hS : ∀ i, subsetSDegree (rename e (P.field i)) ≤ N)
    (u : ForwardSolution P) (tc : ForwardClockChange u (subsetClock e N)) :
    Nonempty (SubsetSolution P e o N out u) := by
  obtain ⟨sol, hc, heq, hu⟩ := subsetCompile_solution_of_clock P e o out hN hS u tc
  exact ⟨⟨tc, sol, hc, heq, hu⟩⟩

/-- The arbitrary supplied global source is preserved on every nonnegative compiled time. -/
theorem exists_subsetSolution_of_global (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    {N : ℕ} (out : Fin r ⊕ Fin m) (hN : Even N)
    (hS : ∀ i, subsetSDegree (rename e (P.field i)) ≤ N)
    (sol : PIVP.Solution P.toPIVP) :
    Nonempty (SubsetSolution P e o N out (ForwardSolution.ofGlobal sol)) := by
  obtain ⟨tc⟩ := exists_globalClockChange sol (subsetClock e N)
    (continuous_subsetClock e N) (subsetClock_ge_one e hN)
  exact exists_subsetSolution_of_clock P e o out hN hS (ForwardSolution.ofGlobal sol) tc

/-- General B12 compilation, including a finite actual maximal source lifespan. -/
theorem exists_subsetSolution_of_maximal (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    {N D : ℕ} (out : Fin r ⊕ Fin m) (hN : Even N)
    (hS : ∀ i, subsetSDegree (rename e (P.field i)) ≤ N)
    (hD : ∀ i, (P.field i).totalDegree ≤ D)
    (u : MaximalSolution P) (K Cp : ℝ) (hK : 1 ≤ K)
    (hCp : subsetCoefficientMaximum P e ≤ Cp)
    (hR : ∀ t ∈ forwardInterval u.lifetime, ∀ j,
      |subsetRetained e (u.trajectory t) j| ≤ K) :
    Nonempty (SubsetSolution P e o N out u.toForwardSolution) := by
  obtain ⟨tc⟩ := exists_subsetClockChange P e hN hS hD u K Cp hK hCp hR
  exact exists_subsetSolution_of_clock P e o out hN hS u.toForwardSolution tc

/-- The finite-lifespan specialization displays the exact inverse endpoint and interval. -/
theorem exists_subsetSolution_of_finite_maximal (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    {N D : ℕ} (out : Fin r ⊕ Fin m) (hN : Even N)
    (hS : ∀ i, subsetSDegree (rename e (P.field i)) ≤ N)
    (hD : ∀ i, (P.field i).totalDegree ≤ D)
    (u : MaximalSolution P) (hfin : u.lifetime ≠ ⊤)
    (K Cp : ℝ) (hK : 1 ≤ K) (hCp : subsetCoefficientMaximum P e ≤ Cp)
    (hR : ∀ t ∈ forwardInterval u.lifetime, ∀ j,
      |subsetRetained e (u.trajectory t) j| ≤ K) :
    ∃ w : SubsetSolution P e o N out u.toForwardSolution,
      Tendsto w.clock.inverse atTop
        (nhdsWithin u.lifetime.toReal (Set.Iio u.lifetime.toReal)) ∧
      (∀ τ, 0 ≤ τ → w.clock.inverse τ ∈ Set.Ico 0 u.lifetime.toReal) := by
  obtain ⟨w⟩ := exists_subsetSolution_of_maximal P e o out hN hS hD u K Cp hK hCp hR
  refine ⟨w, ?_, ?_⟩
  · simpa only [endpointFilter, if_neg hfin] using w.clock.inverse_limit
  · intro τ hτ
    have h := w.clock.inverse_mem τ hτ
    rwa [forwardInterval_finite u.positive hfin] at h

namespace SubsetSolution

variable {P : PolyPIVP d} {e : Fin d ≃ (Fin r ⊕ Fin s)}
  {o : Fin m → Fin d} {out : Fin r ⊕ Fin m}
  {u : ForwardSolution P}

/-- Every solution of the compiled PIVP has the displayed forward trajectory. -/
theorem other_trajectory_eq (w : SubsetSolution P e o N out u)
    (other : PIVP.Solution (subsetCompile P e o N out).toPIVP)
    (τ : ℝ) (hτ : 0 ≤ τ) (k : SubsetIndex r s m N) :
    other.trajectory τ (Fintype.equivFin (SubsetIndex r s m N) k) =
      subsetCurve e o N (fun σ => u.trajectory (w.clock.inverse σ)) τ k := by
  rw [w.unique other (Set.mem_Ici.mpr hτ)]
  exact w.trajectory_eq τ hτ k

theorem norm_le (w : SubsetSolution P e o N out u)
    (hN : Even N) {K M : ℝ}
    (hR : ∀ t ∈ forwardInterval u.lifetime, ∀ j,
      |subsetRetained e (u.trajectory t) j| ≤ K)
    (hO : ∀ t ∈ forwardInterval u.lifetime, ∀ j, |u.trajectory t (o j)| ≤ M) :
    ∀ τ, 0 ≤ τ → ‖w.solution.trajectory τ‖ ≤ max (max K M) 1 :=
  subsetCompile_norm_le P e o out hN w.solution
    (fun σ => u.trajectory (w.clock.inverse σ)) w.trajectory_eq
    (fun τ hτ j => hR _ (w.clock.inverse_mem τ hτ) j)
    (fun τ hτ j => hO _ (w.clock.inverse_mem τ hτ) j)

theorem isBounded (w : SubsetSolution P e o N out u)
    (hN : Even N) {K M : ℝ}
    (hR : ∀ t ∈ forwardInterval u.lifetime, ∀ j,
      |subsetRetained e (u.trajectory t) j| ≤ K)
    (hO : ∀ t ∈ forwardInterval u.lifetime, ∀ j, |u.trajectory t (o j)| ≤ M) :
    (subsetCompile P e o N out).toPIVP.IsBounded w.solution.trajectory :=
  ⟨max (max K M) 1, lt_max_of_lt_right one_pos, w.norm_le hN hR hO⟩

theorem isBounded_of_output_limits (w : SubsetSolution P e o N out u)
    (hN : Even N) {K : ℝ}
    (hR : ∀ t ∈ forwardInterval u.lifetime, ∀ j,
      |subsetRetained e (u.trajectory t) j| ≤ K)
    (L : Fin m → ℝ)
    (hlim : ∀ j, Tendsto (fun t => u.trajectory t (o j))
      (endpointFilter u.lifetime) (𝓝 (L j))) :
    (subsetCompile P e o N out).toPIVP.IsBounded w.solution.trajectory := by
  obtain ⟨M, _, hO⟩ := subsetOutputCopies_bounded_of_limits P u o L hlim
  exact w.isBounded hN hR hO

theorem readout_limit (w : SubsetSolution P e o N out u)
    (readout : Fin r ⊕ Fin m) {L : ℝ}
    (hlim : Tendsto (fun t => u.trajectory t (subsetOutputSource e o readout))
      (endpointFilter u.lifetime) (𝓝 L)) :
    Tendsto (fun τ => w.solution.trajectory τ
      (Fintype.equivFin (SubsetIndex r s m N) (subsetOutputIndex readout)))
      atTop (𝓝 L) :=
  subsetCompile_readout_limit P e o out u w.clock w.solution w.trajectory_eq readout hlim

theorem output_limit (w : SubsetSolution P e o N out u) {L : ℝ}
    (hlim : Tendsto (fun t => u.trajectory t (subsetOutputSource e o out))
      (endpointFilter u.lifetime) (𝓝 L)) :
    Tendsto (fun τ => w.solution.trajectory τ (subsetCompile P e o N out).output)
      atTop (𝓝 L) :=
  subsetCompile_output_limit P e o out u w.clock w.solution w.trajectory_eq hlim

/-- Selecting the original designated output gives the semantic computation statement. -/
theorem computes (w : SubsetSolution P e o N out u)
    (hout : subsetOutputSource e o out = P.output) {L : ℝ}
    (hlim : Tendsto (fun t => u.trajectory t P.output)
      (endpointFilter u.lifetime) (𝓝 L)) :
    (subsetCompile P e o N out).toPIVP.Computes w.solution L := by
  change Tendsto (fun τ => w.solution.trajectory τ (subsetCompile P e o N out).output)
    atTop (𝓝 L)
  apply w.output_limit
  simpa only [hout] using hlim

end SubsetSolution

/-- The maximal-source theorem with an explicit bound on the entire compiled state. -/
theorem subsetCompile_of_maximal_bounded (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    {N D : ℕ} (out : Fin r ⊕ Fin m) (hN : Even N)
    (hS : ∀ i, subsetSDegree (rename e (P.field i)) ≤ N)
    (hD : ∀ i, (P.field i).totalDegree ≤ D)
    (u : MaximalSolution P) (K Cp M : ℝ) (hK : 1 ≤ K)
    (hCp : subsetCoefficientMaximum P e ≤ Cp)
    (hR : ∀ t ∈ forwardInterval u.lifetime, ∀ j,
      |subsetRetained e (u.trajectory t) j| ≤ K)
    (hO : ∀ t ∈ forwardInterval u.lifetime, ∀ j, |u.trajectory t (o j)| ≤ M) :
    ∃ w : SubsetSolution P e o N out u.toForwardSolution,
      (∀ τ, 0 ≤ τ → ‖w.solution.trajectory τ‖ ≤ max (max K M) 1) ∧
      (subsetCompile P e o N out).toPIVP.IsBounded w.solution.trajectory := by
  obtain ⟨w⟩ := exists_subsetSolution_of_maximal P e o out hN hS hD u K Cp hK hCp hR
  exact ⟨w, w.norm_le hN hR hO, w.isBounded hN hR hO⟩

/-- Finite output limits suffice for boundedness; all retained or copied
finite limits are preserved by the same compiled solution. -/
theorem subsetCompile_of_maximal_limits (P : PolyPIVP d)
    (e : Fin d ≃ (Fin r ⊕ Fin s)) (o : Fin m → Fin d)
    {N D : ℕ} (out : Fin r ⊕ Fin m) (hN : Even N)
    (hS : ∀ i, subsetSDegree (rename e (P.field i)) ≤ N)
    (hD : ∀ i, (P.field i).totalDegree ≤ D)
    (u : MaximalSolution P) (K Cp : ℝ) (hK : 1 ≤ K)
    (hCp : subsetCoefficientMaximum P e ≤ Cp)
    (hR : ∀ t ∈ forwardInterval u.lifetime, ∀ j,
      |subsetRetained e (u.trajectory t) j| ≤ K)
    (L : Fin m → ℝ)
    (hlim : ∀ j, Tendsto (fun t => u.trajectory t (o j))
      (endpointFilter u.lifetime) (𝓝 (L j))) :
    ∃ w : SubsetSolution P e o N out u.toForwardSolution,
      (subsetCompile P e o N out).toPIVP.IsBounded w.solution.trajectory ∧
      (∀ readout : Fin r ⊕ Fin m, ∀ α : ℝ,
        Tendsto (fun t => u.trajectory t (subsetOutputSource e o readout))
          (endpointFilter u.lifetime) (𝓝 α) →
        Tendsto (fun τ => w.solution.trajectory τ
          (Fintype.equivFin (SubsetIndex r s m N) (subsetOutputIndex readout)))
          atTop (𝓝 α)) := by
  obtain ⟨w⟩ := exists_subsetSolution_of_maximal P e o out hN hS hD u K Cp hK hCp hR
  exact ⟨w, w.isBounded_of_output_limits hN hR L hlim,
    fun readout α hα => w.readout_limit readout hα⟩

end Ripple.SubsetCompilation
