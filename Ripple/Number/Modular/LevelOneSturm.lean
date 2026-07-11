/-
  Stage 1 scaffold: Sturm bound for level Γ(1) = SL₂(ℤ).

  Statement: for `f ∈ M_k(Γ(1))` with `k ≥ 0`, if `coeff_n (qExpansion f) = 0`
  for every `n ≤ k / 12`, then `f = 0`.

  Strategy (the open Stage 1 obligation): consider `g = f / Δ^j` for
  `j = ⌊k/12⌋ + 1`.  This has weight `k - 12 j < 0`, is holomorphic on `ℍ`
  (since `Δ ≠ 0` there), and bounded at the cusp (since `f` vanishes to
  order `≥ j` at `∞`).  Then `g = 0` by
  `ModularFormClass.levelOne_neg_weight_eq_zero`, hence `f = 0`.  Mathlib
  carries the `j = 1` case for cusp forms of fixed weight (see the
  `cuspForm{Cube,Square}DivDelta*` infrastructure in `CMEvaluation163.lean`
  and `ModularPolynomialQExpansion.lean`); generalising this to arbitrary
  `j` is the substantive part of Stage 1.

  This file currently exposes:
    * `LevelOneSturmBound` — the statement as a `Prop`.
    * `levelOne_eq_zero_of_neg_weight` — the trivial negative-weight case
      lifted from Mathlib's `levelOne_neg_weight_eq_zero`.
  The general `k > 0` case is the open Stage 1 obligation.
-/
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.NumberTheory.ModularForms.QExpansion

namespace Ripple
namespace Number
namespace Modular

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane

open scoped MatrixGroups

/-- The level-one Sturm bound, expressed as a single `Prop`.

For `f : ModularForm Γ(1) k` with `k ≥ 0`, if every `q`-expansion coefficient
`a_n` with `n ≤ k / 12` vanishes, then `f = 0`. -/
def LevelOneSturmBound : Prop :=
  ∀ {k : ℤ} (_hk : 0 ≤ k) (f : ModularForm (Gamma 1) k),
    (∀ n : ℕ, n ≤ k.toNat / 12 →
      (UpperHalfPlane.qExpansion 1 f.toFun).coeff n = 0) →
    f = 0

/-- Trivial case: a holomorphic level-one modular form of negative weight is
zero, restated at the `f = 0` level (Mathlib's `levelOne_neg_weight_eq_zero`
gives only the function equality). -/
theorem levelOne_eq_zero_of_neg_weight {k : ℤ} (hk : k < 0)
    (f : ModularForm (Gamma 1) k) : f = 0 := by
  have inst : ModularFormClass (ModularForm (Gamma 1) k) 𝒮ℒ k :=
    Gamma_one_coe_eq_SL ▸ (inferInstance : ModularFormClass (ModularForm (Gamma 1) k) _ k)
  have hcoe : ⇑f = 0 := ModularFormClass.levelOne_neg_weight_eq_zero hk f
  ext z
  simpa using congrFun hcoe z

/-- Trivial case: a level-one weight-zero modular form whose value at `∞`
is zero must be the zero form.  (Phrased via `valueAtInfty` rather than
the q-expansion coefficient to avoid expensive elaboration of the
`qExpansion` signature.) -/
theorem levelOne_weightZero_eq_zero_of_valueAtInfty_zero
    (f : ModularForm (Gamma 1) 0)
    (h0 : UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) = 0) :
    f = 0 := by
  have inst : ModularFormClass (ModularForm (Gamma 1) 0) 𝒮ℒ 0 :=
    Gamma_one_coe_eq_SL ▸ (inferInstance : ModularFormClass (ModularForm (Gamma 1) 0) _ 0)
  obtain ⟨c, hc⟩ := levelOne_weight_zero_const (F := ModularForm (Gamma 1) 0) f
  -- `valueAtInfty (const c) = c`.
  have hvalue : UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) = c := by
    refine Filter.Tendsto.limUnder_eq ?_
    have hfc : (f : ℍ → ℂ) = fun _ => c := hc
    rw [hfc]
    exact tendsto_const_nhds
  have hc_zero : c = 0 := hvalue ▸ h0
  ext z
  have hfz : (f : ℍ → ℂ) z = c := congrFun hc z
  simp [hfz, hc_zero]

/-- Odd weights at level 1 vanish.  Proof: under the action of
`-I ∈ SL(2, ℤ)`, the slash relation yields `f z = (-1)^k · f z`; for
odd `k`, this forces `f z = 0`. -/
theorem levelOne_eq_zero_of_odd_weight {k : ℤ} (hk : Odd k)
    (f : ModularForm (Gamma 1) k) : f = 0 := by
  ext z
  have hneg : (-1 : SL(2, ℤ)) ∈ Gamma 1 := by
    rw [CongruenceSubgroup.Gamma_one_top]; exact Subgroup.mem_top _
  have hSL := SlashInvariantForm.slash_action_eqn_SL'' f hneg z
  -- (-1) • z = z.
  have hsmul : (-1 : SL(2, ℤ)) • z = z := by
    show -(1 : SL(2, ℤ)) • z = z
    rw [ModularGroup.SL_neg_smul, one_smul]
  -- denom (-1) z = -1: the (1, 0) entry of -I is 0, the (1, 1) entry is -1.
  have hdenom : UpperHalfPlane.denom
      (((-1 : SL(2, ℤ)) : Matrix.GeneralLinearGroup (Fin 2) ℝ)) z = -1 := by
    rw [ModularGroup.denom_apply]
    simp [Matrix.SpecialLinearGroup.coe_neg]
  rw [hsmul, hdenom, hk.neg_one_zpow] at hSL
  have h2 : (2 : ℂ) * (f : ℍ → ℂ) z = 0 := by linear_combination hSL
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  have hfz : (f : ℍ → ℂ) z = 0 :=
    (mul_eq_zero.mp h2).resolve_left h2ne
  simpa using hfz

/-- Unified trivial-case theorem: a level-1 modular form of weight `k`
vanishes whenever `k < 0` or `k` is odd.  Combines
`levelOne_eq_zero_of_neg_weight` and `levelOne_eq_zero_of_odd_weight`.
For `k ≥ 0` even, the (full) Sturm bound is needed; this is handled
uniformly in `LevelOneSturmGeneric.lean` via the `f^a / Δ^b` construction
parametrised by `k mod 12 ∈ {0, 2, 4, 6, 8, 10}`. -/
theorem levelOne_eq_zero_of_neg_or_odd_weight
    {k : ℤ} (hk : k < 0 ∨ Odd k)
    (f : ModularForm (Gamma 1) k) : f = 0 := by
  rcases hk with hneg | hodd
  · exact levelOne_eq_zero_of_neg_weight hneg f
  · exact levelOne_eq_zero_of_odd_weight hodd f

end Modular
end Number
end Ripple
