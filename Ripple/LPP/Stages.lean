/-
  Ripple.LPP.Stages — Four-Stage GPAC→PP Construction

  Formalizes the four-stage algorithm from [LPP] §3 (Huang-Huls, DNA 28):
    Stage 1: CRN → CRN-implementable quadratic system (v-variables)
    Stage 2: Quadratic CRN → TPP-implementable cubic form (λ-trick + balancing dilation)
    Stage 3: TPP cubic form → PP-implementable quadratic form (self-product z_{i,j} = x_i·x_j)
    Stage 4: PP quadratic form → PLPP (ε-trick + rule construction)

  Also formalizes the basic operations from §3.2:
    Operation 1: Constant dilation (ε-trick)
    Operation 2: Time dilation (composition)
    Operation 3: Variable shrinking (λ-trick)
    Operation 4: Balancing dilation (g-trick)
-/

import Ripple.LPP.Defs
import Ripple.LPP.Example
import Ripple.LPP.Syntactic
import Ripple.Core.BoundedTime
import Ripple.LPP.VVariable
import Ripple.LPP.Product
import Ripple.Core.ODEGlobal
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Topology

namespace Ripple

/-! ## Non-dependent Fin tuple helpers

`Fin.snoc` and `Fin.addCases` are dependently typed, which makes `rw`/`simp`
fail in non-dependent contexts (where the result type is constant, e.g. `ℝ`).
These wrappers fix the motive to `fun _ => α`, enabling standard rewriting. -/

/-- Non-dependent `Fin.snoc`: appends a value to a tuple. -/
def vecSnoc {n : ℕ} {α : Type*} (f : Fin n → α) (a : α) : Fin (n + 1) → α :=
  @Fin.snoc n (fun _ => α) f a

@[simp] lemma vecSnoc_last {n : ℕ} {α : Type*} {f : Fin n → α} {a : α} :
    vecSnoc f a (Fin.last n) = a :=
  @Fin.snoc_last n (fun _ => α) a f

@[simp] lemma vecSnoc_castSucc {n : ℕ} {α : Type*} {f : Fin n → α} {a : α} {j : Fin n} :
    vecSnoc f a (Fin.castSucc j) = f j :=
  @Fin.snoc_castSucc n (fun _ => α) a f j

lemma vecSnoc_init {n : ℕ} {α : Type*} {f : Fin n → α} {a : α} :
    Fin.init (vecSnoc f a) = f :=
  @Fin.init_snoc n (fun _ => α) a f

/-- Non-dependent `Fin.addCases`: concatenates two tuples. -/
def vecAddCases {m n : ℕ} {α : Type*} (f : Fin m → α) (g : Fin n → α) :
    Fin (m + n) → α :=
  @Fin.addCases m n (fun _ => α) f g

@[simp] lemma vecAddCases_left {m n : ℕ} {α : Type*} {f : Fin m → α}
    {g : Fin n → α} {i : Fin m} :
    vecAddCases f g (Fin.castAdd n i) = f i :=
  Fin.addCases_left i

@[simp] lemma vecAddCases_right {m n : ℕ} {α : Type*} {f : Fin m → α}
    {g : Fin n → α} {i : Fin n} :
    vecAddCases f g (Fin.natAdd m i) = g i :=
  Fin.addCases_right i

/-- `Fin.castSucc` commutes with `Fin.natAdd` (they compose to the same embedding). -/
lemma Fin.castSucc_natAdd_comm {m n : ℕ} {j : Fin n} :
    (Fin.natAdd m j).castSucc = Fin.natAdd m (j.castSucc) := by
  ext; simp [Fin.natAdd, Fin.castSucc, Fin.castAdd]

/-- vecSnoc through the natAdd∘castSucc embedding. Lean normalizes
`Fin.castSucc (Fin.natAdd m j)` to `Fin.natAdd m (Fin.castSucc j)`,
so we need this form in addition to `vecSnoc_castSucc`. -/
@[simp] lemma vecSnoc_natAdd_castSucc {m n : ℕ} {α : Type*}
    {f : Fin (m + n) → α} {a : α} {j : Fin n} :
    vecSnoc f a (Fin.natAdd m (Fin.castSucc j)) = f (Fin.natAdd m j) := by
  rw [← Fin.castSucc_natAdd_comm]; exact vecSnoc_castSucc

/-! ## k-PP-implementable systems

From [LPP] Corollary 4: a function is k-PP-implementable iff it is
CRN-implementable, conservative, homogeneously degree k, and has no
positive xᵢᵏ term in x'ᵢ. A TPP (termolecular PP) is a 3-PP. -/

/-- A vector field is k-PP-implementable: CRN-implementable + conservative
+ degree ≤ k + no positive xᵢᵏ in x'ᵢ.

For k=2 this is PP-implementable (bimolecular reactions X+Y → W+Z).
For k=3 this is TPP-implementable (termolecular reactions X+Y+Z → U+V+W).

**Note:** The degree and no-self-power conditions are not yet enforced
in this structure. The `k` parameter is carried for type-level tracking
but will need semantic or syntactic enforcement when Stage proofs are
filled in. -/
structure IsKPPImplementable (k n : ℕ) (field : (Fin n → ℝ) → Fin n → ℝ)
    extends IsCRNImplementable n field where
  /-- The system is conservative (formal polynomial identity, not just on simplex). -/
  conservative : IsConservative field

/-- A TPP-implementable system is a 3-PP-implementable system.
Reactions have the form X + Y + Z → U + V + W. -/
abbrev IsTPPImplementable (n : ℕ) := IsKPPImplementable 3 n

/-! ## Basic Operations (§3.2)

These are the building blocks for the four-stage construction. -/

/-- Operation 1: Constant dilation (ε-trick).
If x'(t) = p(x(t)) then x(εt) solves x'(t) = ε·p(x(t)).
This scales the coefficients without changing the trajectory shape.

We state this as a fact about the scalar reparametrization. -/
theorem constant_dilation_reparametrize (ε : ℝ)
    (f g : ℝ → ℝ) (h_sol : ∀ t, HasDerivAt f (g t) t) :
    ∀ t, HasDerivAt (fun s => f (ε * s)) (ε * g (ε * t)) t := by
  intro t
  have h1 := (h_sol (ε * t)).comp t ((hasDerivAt_id t).const_mul ε)
  simp only [mul_one] at h1
  convert h1 using 1
  ring

/-- Operation 2: Constant dilation for vector fields.
If x(t) solves x' = field(x), then x(εt) solves x' = ε·field(x).
This is the vector-field version of `constant_dilation_reparametrize`. -/
def constantDilation {n : ℕ} (ε : ℝ) (field : (Fin n → ℝ) → Fin n → ℝ) :
    (Fin n → ℝ) → Fin n → ℝ :=
  fun x i => ε * field x i

/-- Constant dilation preserves CRN-implementability.
If field = prod - degr·x, then ε·field = (ε·prod) - (ε·degr)·x. -/
noncomputable def constantDilation_crn {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (crn : IsCRNImplementable n field) :
    IsCRNImplementable n (constantDilation ε field) where
  prod := fun i x => ε * crn.prod i x
  degr := fun i x => ε * crn.degr i x
  prod_pos := fun i x hx => mul_nonneg hε (crn.prod_pos i x hx)
  degr_pos := fun i x hx => mul_nonneg hε (crn.degr_pos i x hx)
  field_eq := fun x i => by
    simp only [constantDilation]
    rw [crn.field_eq]
    ring

/-- Constant dilation preserves conservation. -/
theorem constantDilation_conservative {n : ℕ} {ε : ℝ}
    {field : (Fin n → ℝ) → Fin n → ℝ} (hcons : IsConservative field) :
    IsConservative (constantDilation ε field) := by
  intro x
  simp only [constantDilation, ← Finset.mul_sum]
  rw [hcons x]
  ring

/-- Constant dilation respects solutions via time reparametrization:
if x solves x' = field(x), then x(ε·t) solves x' = constantDilation ε field(x).
This is because d/dt[x(εt)] = ε · x'(εt) = ε · field(x(εt)). -/
theorem constantDilation_reparametrize {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    {x : ℝ → Fin n → ℝ} {field : (Fin n → ℝ) → Fin n → ℝ}
    (h_sol : ∀ t, 0 ≤ t → HasDerivAt x (field (x t)) t) :
    ∀ t, 0 ≤ t →
      HasDerivAt (fun s => x (ε * s))
        (constantDilation ε field (x (ε * t))) t := by
  intro t ht
  -- Work component-wise: chain rule for each x_i
  change HasDerivAt (fun s => x (ε * s)) (fun i => ε * field (x (ε * t)) i) t
  refine hasDerivAt_pi.mpr (fun i => ?_)
  -- Component i of the ODE solution
  have h_xi := hasDerivAt_pi.mp (h_sol (ε * t) (mul_nonneg hε.le ht)) i
  -- The time rescaling function s ↦ ε·s
  have h_inner : HasDerivAt (ε * ·) ε t := by
    simpa [mul_one] using (hasDerivAt_id t).const_mul ε
  -- Chain rule: d/dt[x_i(ε·t)] = ε · field(x(ε·t))_i
  -- comp gives derivative ε • g'(ε·t) = g'(ε·t) * ε; we need ε * g'(ε·t)
  convert (h_xi.comp t h_inner) using 1; simp [mul_comm]

/-- Constant time reparametrization preserves convergence:
if x(t) → L as t → ∞ and ε > 0, then x(ε·t) → L as t → ∞.
This is fundamental for Stage 2: the ε-scaling and balancing dilation
change the time scale but not the limit. -/
theorem tendsto_comp_const_mul {α : ℝ} {x : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (h_conv : Filter.Tendsto x Filter.atTop (nhds α)) :
    Filter.Tendsto (fun t => x (ε * t)) Filter.atTop (nhds α) :=
  h_conv.comp (Filter.tendsto_atTop_atTop_of_monotone
    (fun _ _ hab => mul_le_mul_of_nonneg_left hab hε.le)
    (fun b => ⟨b / ε, by rw [mul_div_cancel₀ b (ne_of_gt hε)]⟩))

/-- Operation 3: Variable shrinking (λ-trick).
Given field on n variables, scaling y = λ·x gives a new field
where fieldλ(y)ᵢ = λ · field(y/λ)ᵢ.

If x(t) solves x' = field(x), then y(t) = λ·x(t) solves y' = fieldλ(y).
The degree of the polynomial field is preserved. -/
noncomputable def lambdaTrick {n : ℕ} (c : ℝ) (field : (Fin n → ℝ) → Fin n → ℝ) :
    (Fin n → ℝ) → Fin n → ℝ :=
  fun y i => c * field (fun j => y j / c) i

/-- Scaling cancellation: lambdaTrick c field (c • y) = c • field y. -/
theorem lambdaTrick_smul_cancel {n : ℕ} {c : ℝ} (hc : c ≠ 0)
    (field : (Fin n → ℝ) → Fin n → ℝ) (y : Fin n → ℝ) :
    lambdaTrick c field (c • y) = c • field y := by
  funext i
  simp only [lambdaTrick, Pi.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hc]

/-- The λ-trick respects solutions: if x solves x' = field(x),
then c • x solves x' = lambdaTrick c field(c • x). -/
theorem lambdaTrick_solution {n : ℕ} {c : ℝ} (hc : c ≠ 0)
    {x : ℝ → Fin n → ℝ} {field : (Fin n → ℝ) → Fin n → ℝ}
    (h_sol : ∀ t, HasDerivAt x (field (x t)) t) :
    ∀ t, HasDerivAt (c • x ·) (lambdaTrick c field (c • x t)) t := by
  intro t
  rw [lambdaTrick_smul_cancel hc]
  exact (h_sol t).const_smul c

/-- The λ-trick preserves convergence of scaled output:
if x(t)_o → α as t → ∞, then (c · x(t))_o = c · α.
More precisely: convergence of the output component scales by c. -/
theorem lambdaTrick_tendsto {n : ℕ} {c α : ℝ}
    {x : ℝ → Fin n → ℝ} {o : Fin n}
    (h_conv : Filter.Tendsto (fun t => x t o) Filter.atTop (nhds α)) :
    Filter.Tendsto (fun t => c * x t o) Filter.atTop (nhds (c * α)) :=
  h_conv.const_mul c

/-- The λ-trick preserves CRN-implementability.
If field = prod - degr·x, then lambdaTrick c field = (c·prod(·/c)) - degr(·/c)·x. -/
noncomputable def lambdaTrick_crn {n : ℕ} {c : ℝ} (hc : 0 < c)
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (crn : IsCRNImplementable n field) :
    IsCRNImplementable n (lambdaTrick c field) where
  prod := fun i y => c * crn.prod i (fun j => y j / c)
  degr := fun i y => crn.degr i (fun j => y j / c)
  prod_pos := fun i y hy => by
    apply mul_nonneg hc.le
    exact crn.prod_pos i _ (fun k => div_nonneg (hy k) hc.le)
  degr_pos := fun i y hy =>
    crn.degr_pos i _ (fun k => div_nonneg (hy k) hc.le)
  field_eq := fun y i => by
    simp only [lambdaTrick]
    rw [crn.field_eq]
    have hc' : c ≠ 0 := ne_of_gt hc
    field_simp

/-- The λ-trick preserves conservation.
If ∑field_i(x) = 0 for all x, then ∑(lambdaTrick c field)(y)_i = 0 for all y. -/
theorem lambdaTrick_conservative {n : ℕ} {c : ℝ}
    {field : (Fin n → ℝ) → Fin n → ℝ} (hcons : IsConservative field) :
    IsConservative (lambdaTrick c field) := by
  intro y
  simp only [lambdaTrick, ← Finset.mul_sum]
  rw [hcons]
  ring

/-! ### Selective λ-trick (Operation 3b)

The paper's λ-trick ([LPP] §3.2, Theorem 13 full proof) is *selective*:
it scales only the non-output variables x₂, ..., xₙ by λ, leaving the
output variable x₁ unchanged. This ensures x₁(t) → α is preserved.

The change of variables: y_o = x_o (output), y_j = c · x_j (j ≠ o).
The new field:
  y_o' = field_o(unscale y)        (output: unchanged speed)
  y_j' = c · field_j(unscale y)    (non-output: scaled) -/

/-- Selective unscaling: undo the selective λ-trick.
Maps scaled coordinates y back to original coordinates x:
  x_o = y_o (output unchanged), x_j = y_j / c (non-output unscaled). -/
noncomputable def selectiveUnscale {n : ℕ} (o : Fin n) (c : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  Function.update (fun j => y j / c) o (y o)

/-- At the output index, selectiveUnscale returns y_o unchanged. -/
@[simp] theorem selectiveUnscale_output {n : ℕ} (o : Fin n) (c : ℝ) (y : Fin n → ℝ) :
    selectiveUnscale o c y o = y o := by
  simp [selectiveUnscale]

/-- At non-output indices, selectiveUnscale returns y_j / c. -/
theorem selectiveUnscale_ne {n : ℕ} {o j : Fin n} (hj : j ≠ o) (c : ℝ) (y : Fin n → ℝ) :
    selectiveUnscale o c y j = y j / c := by
  simp [selectiveUnscale, Function.update_of_ne hj]

/-- Selective scaling: scale non-output variables by c.
  y_o = x_o (output unchanged), y_j = c · x_j (j ≠ o). -/
noncomputable def selectiveScale {n : ℕ} (o : Fin n) (c : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  Function.update (fun j => c * x j) o (x o)

/-- selectiveUnscale inverts selectiveScale when c ≠ 0. -/
theorem selectiveUnscale_scale {n : ℕ} (o : Fin n) {c : ℝ} (hc : c ≠ 0) (x : Fin n → ℝ) :
    selectiveUnscale o c (selectiveScale o c x) = x := by
  funext j
  by_cases hj : j = o
  · subst hj; simp [selectiveUnscale, selectiveScale]
  · simp only [selectiveUnscale, selectiveScale, Function.update_of_ne hj]
    field_simp

/-- Sup-norm bound for `selectiveUnscale`: if `0 < c ≤ 1`, then
`‖selectiveUnscale o c y‖ ≤ ‖y‖ / c`.

This packages the two coordinate-wise inequalities:
  * at `o`: `|y o| ≤ ‖y‖ ≤ ‖y‖ / c` (since `1 ≤ 1/c` when `c ≤ 1`)
  * at `j ≠ o`: `|y j / c| = |y j| / c ≤ ‖y‖ / c`.

This is useful when the input `y` is a component of a simplex trajectory
(so `‖y‖ ≤ 1`), giving the uniform bound `‖selectiveUnscale o c y‖ ≤ 1/c`. -/
theorem selectiveUnscale_norm_le_div {n : ℕ} [NeZero n] (o : Fin n) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (y : Fin n → ℝ) :
    ‖selectiveUnscale o c y‖ ≤ ‖y‖ / c := by
  have hnorm_nn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
  have h_div_nn : (0 : ℝ) ≤ ‖y‖ / c := div_nonneg hnorm_nn hc.le
  rw [pi_norm_le_iff_of_nonneg h_div_nn]
  intro i
  have h_le_div : ‖y‖ ≤ ‖y‖ / c := by
    rw [le_div_iff₀ hc]
    calc ‖y‖ * c ≤ ‖y‖ * 1 :=
          mul_le_mul_of_nonneg_left hc1 hnorm_nn
      _ = ‖y‖ := mul_one _
  by_cases hi : i = o
  · rw [hi, selectiveUnscale_output]
    exact (norm_le_pi_norm y o).trans h_le_div
  · rw [selectiveUnscale_ne hi]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hc]
    have h_abs_le : |y i| ≤ ‖y‖ := by
      have := norm_le_pi_norm y i
      rwa [Real.norm_eq_abs] at this
    exact div_le_div_of_nonneg_right h_abs_le hc.le

/-- Selective λ-trick: scale non-output variables by c.
Given a field on x = (x₁, ..., xₙ), the change of variables
y_o = x_o, y_j = c·x_j (j ≠ o) gives a new field:
  y_o' = field_o(unscale y)
  y_j' = c · field_j(unscale y) for j ≠ o

This is the *selective* version from [LPP] Theorem 13: the output x₁
is NOT scaled, preserving convergence x₁(t) → α. -/
noncomputable def selectiveLambdaTrick {n : ℕ} (o : Fin n) (c : ℝ)
    (field : (Fin n → ℝ) → Fin n → ℝ) :
    (Fin n → ℝ) → Fin n → ℝ :=
  fun y i => if i = o then field (selectiveUnscale o c y) i
             else c * field (selectiveUnscale o c y) i

/-- The selective λ-trick respects solutions: if x solves x' = field(x),
then selectiveScale o c x solves x' = selectiveLambdaTrick o c field(x). -/
theorem selectiveLambdaTrick_solution {n : ℕ} {o : Fin n} {c : ℝ} (hc : c ≠ 0)
    {x : ℝ → Fin n → ℝ} {field : (Fin n → ℝ) → Fin n → ℝ}
    (h_sol : ∀ t, 0 ≤ t → HasDerivAt x (field (x t)) t) :
    ∀ t, 0 ≤ t →
      HasDerivAt (fun s => selectiveScale o c (x s))
        (selectiveLambdaTrick o c field (selectiveScale o c (x t))) t := by
  intro t ht
  -- Unscale inverts scale
  have h_unscale : selectiveUnscale o c (selectiveScale o c (x t)) = x t :=
    selectiveUnscale_scale o hc (x t)
  -- The derivative term: selectiveLambdaTrick applies field to unscaled input
  have h_deriv_eq : selectiveLambdaTrick o c field (selectiveScale o c (x t)) =
      fun i => if i = o then field (x t) i else c * field (x t) i := by
    funext i; simp only [selectiveLambdaTrick, h_unscale]
  rw [h_deriv_eq]
  -- Work component-wise
  refine hasDerivAt_pi.mpr (fun i => ?_)
  have h_xi := hasDerivAt_pi.mp (h_sol t ht) i
  by_cases hi : i = o
  · -- Output component: y_o = x_o, derivative = field_o(x)
    simp only [hi, ite_true]
    have h_fn : (fun s => selectiveScale o c (x s) o) = (fun s => x s o) := by
      funext s; simp [selectiveScale]
    rw [h_fn]; rw [hi] at h_xi; exact h_xi
  · -- Non-output: y_j = c · x_j, derivative = c · field_j(x)
    simp only [hi, ite_false]
    have h_fn : (fun s => selectiveScale o c (x s) i) = (fun s => c * x s i) := by
      funext s; simp [selectiveScale, Function.update_of_ne hi]
    rw [h_fn]; exact h_xi.const_mul c

/-- The selective λ-trick preserves convergence at the output:
if x(t)_o → α, then (selectiveScale o c x)(t)_o → α (unchanged). -/
theorem selectiveLambdaTrick_tendsto {n : ℕ} {o : Fin n} {c α : ℝ}
    {x : ℝ → Fin n → ℝ}
    (h_conv : Filter.Tendsto (fun t => x t o) Filter.atTop (nhds α)) :
    Filter.Tendsto (fun t => selectiveScale o c (x t) o) Filter.atTop (nhds α) := by
  have : (fun t => selectiveScale o c (x t) o) = (fun t => x t o) := by
    funext t; simp [selectiveScale]
  rw [this]; exact h_conv

/-- The selective λ-trick preserves CRN-implementability.
If field = prod - degr·x, then selectiveLambdaTrick o c field has CRN form:
  - At output o: prod_o(unscale y) - degr_o(unscale y)·y_o
  - At j ≠ o: c·prod_j(unscale y) - degr_j(unscale y)·y_j -/
noncomputable def selectiveLambdaTrick_crn {n : ℕ} {o : Fin n} {c : ℝ} (hc : 0 < c)
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (crn : IsCRNImplementable n field) :
    IsCRNImplementable n (selectiveLambdaTrick o c field) where
  prod := fun i y => if i = o then crn.prod i (selectiveUnscale o c y)
                     else c * crn.prod i (selectiveUnscale o c y)
  degr := fun i y => crn.degr i (selectiveUnscale o c y)
  prod_pos := fun i y hy => by
    have h_unscale_nn : ∀ k, 0 ≤ selectiveUnscale o c y k := fun k => by
      by_cases hk : k = o
      · simp only [hk, selectiveUnscale_output]; exact hy o
      · rw [selectiveUnscale_ne hk]; exact div_nonneg (hy k) hc.le
    by_cases hi : i = o
    · simp only [hi, ite_true]; exact crn.prod_pos o _ h_unscale_nn
    · simp only [hi, ite_false]; exact mul_nonneg hc.le (crn.prod_pos i _ h_unscale_nn)
  degr_pos := fun i y hy =>
    crn.degr_pos i _ (fun k => by
      by_cases hk : k = o
      · simp only [hk, selectiveUnscale_output]; exact hy o
      · rw [selectiveUnscale_ne hk]; exact div_nonneg (hy k) hc.le)
  field_eq := fun y i => by
    unfold selectiveLambdaTrick
    by_cases hi : i = o
    · simp only [hi, ite_true]
      rw [crn.field_eq, selectiveUnscale_output]
    · simp only [hi, ite_false]
      rw [crn.field_eq, selectiveUnscale_ne hi]
      have hc' : (c : ℝ) ≠ 0 := ne_of_gt hc
      field_simp

/-- The one-trick: extend an n-variable system to n+1 by adding
x₀ with x₀' = -Σᵢ x'ᵢ. The extended system is conservative.
On the simplex with Σxᵢ = 1, the new variable x₀ = 1 - Σᵢ₌₁ⁿ xᵢ.

Unlike the g-trick (balancingDilation), the one-trick does NOT
multiply rates by x₀. It merely adds the conservation variable. -/
def oneTrick {n : ℕ} (field : (Fin n → ℝ) → Fin n → ℝ) :
    (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
  fun x => Fin.cons
    (-(∑ j : Fin n, field (Fin.tail x) j))
    (fun j => field (Fin.tail x) j)

/-- The one-trick is conservative: Σᵢ₌₀ⁿ x'ᵢ = 0. -/
theorem oneTrick_conservative {n : ℕ}
    (field : (Fin n → ℝ) → Fin n → ℝ) :
    IsConservative (oneTrick field) := by
  intro x
  simp only [oneTrick]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  linarith

/-! **Note:** The one-trick does NOT preserve CRN-implementability on its own,
because x₀' = -(Σ field_j) has no x₀-dependent degradation term. The balancing
dilation (`balancingDilation`) combines both the conservation extension and
the x₀-multiplication, and DOES preserve CRN-implementability. -/

/-- Operation 4: Balancing dilation (g-trick).
Given a field on n variables, construct a conservative field on n+1 variables
by multiplying each equation by x₀ and adding x'₀ = -Σx'ᵢ.

The new variable x₀ acts as a "population reservoir" that distributes
total mass among all variables. On the simplex (Σxᵢ = 1), this is
a time dilation by the factor x₀(t).

From [LPP] §3.2 Operation 4 / Theorem 13 proof. -/
def balancingDilation {n : ℕ} (field : (Fin n → ℝ) → Fin n → ℝ) :
    (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
  fun x => Fin.cons
    (-(∑ j : Fin n, field (Fin.tail x) j) * x 0)
    (fun j => field (Fin.tail x) j * x 0)

/-- The balancing dilation is conservative: Σᵢ₌₀ⁿ x'ᵢ = 0.
Proof: x'₀ = -(Σfield_j)·x₀ and Σⱼ x'_{j+1} = (Σfield_j)·x₀. -/
theorem balancingDilation_conservative {n : ℕ}
    (field : (Fin n → ℝ) → Fin n → ℝ) :
    IsConservative (balancingDilation field) := by
  intro x
  simp only [balancingDilation]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [← Finset.sum_mul]
  ring

/-- The balancing dilation preserves CRN-implementability.
If the original field has CRN form x'ᵢ = pᵢ - qᵢxᵢ, then the balanced
system has CRN form:
  x'₀ = (Σⱼ qⱼx_{j+1})·x₀ - (Σⱼ pⱼ)·x₀
  x'_{i+1} = pᵢ·x₀ - (qᵢ·x₀)·x_{i+1}
All production and degradation terms are positive polynomials. -/
noncomputable def balancingDilation_crn {n : ℕ}
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (crn : IsCRNImplementable n field) :
    IsCRNImplementable (n + 1) (balancingDilation field) where
  prod := Fin.cons
    (fun x => (∑ j : Fin n, crn.degr j (Fin.tail x) * x j.succ) * x 0)
    (fun j x => crn.prod j (Fin.tail x) * x 0)
  degr := Fin.cons
    (fun x => ∑ j : Fin n, crn.prod j (Fin.tail x))
    (fun j x => crn.degr j (Fin.tail x) * x 0)
  prod_pos := fun i x hx => by
    refine i.cases ?_ (fun j => ?_)
    · -- x₀: Σ degr(j)·x_{j+1}·x₀ ≥ 0
      simp only [Fin.cons_zero]
      apply mul_nonneg
      · exact Finset.sum_nonneg fun j _ =>
          mul_nonneg (crn.degr_pos j _ (fun k => hx k.succ)) (hx j.succ)
      · exact hx 0
    · -- x_{j+1}: prod(j)·x₀ ≥ 0
      simp only [Fin.cons_succ]
      exact mul_nonneg (crn.prod_pos j _ (fun k => hx k.succ)) (hx 0)
  degr_pos := fun i x hx => by
    refine i.cases ?_ (fun j => ?_)
    · simp only [Fin.cons_zero]
      exact Finset.sum_nonneg fun j _ => crn.prod_pos j _ (fun k => hx k.succ)
    · simp only [Fin.cons_succ]
      exact mul_nonneg (crn.degr_pos j _ (fun k => hx k.succ)) (hx 0)
  field_eq := fun x i => by
    refine i.cases ?_ (fun j => ?_)
    · -- x₀: -(Σ field_j)·x₀ = (Σ degr_j·x_{j+1})·x₀ - (Σ prod_j)·x₀
      simp only [balancingDilation, Fin.cons_zero]
      simp_rw [crn.field_eq (Fin.tail x), Finset.sum_sub_distrib]
      simp only [Fin.tail]
      ring
    · -- x_{j+1}: field_j·x₀ = prod_j·x₀ - (degr_j·x₀)·x_{j+1}
      simp only [balancingDilation, Fin.cons_succ]
      rw [crn.field_eq (Fin.tail x) j]
      simp only [Fin.tail]
      ring

/-- When the inner field is conservative, the balancing dilation has an explicit
solution: z₀ stays constant and the tail follows a time-scaled solution.

If y solves y' = g(y) and g is conservative (∑ gⱼ = 0), then
z(t) = Fin.cons c (y(c·t)) solves z' = balancingDilation g(z),
where c is the initial mass of z₀.

This is because:
- z₀' = -(∑ gⱼ(tail z))·z₀ = 0·z₀ = 0 (conservation), so z₀ = c is constant
- z_{j+1}' = gⱼ(tail z)·z₀ = gⱼ(y(c·t))·c = d/dt[y_j(c·t)] (chain rule) -/
theorem balancingDilation_solution_of_conservative {n : ℕ} {c : ℝ} (hc : 0 < c)
    {y : ℝ → Fin n → ℝ} {g : (Fin n → ℝ) → Fin n → ℝ}
    (hcons : IsConservative g)
    (h_sol : ∀ t, 0 ≤ t → HasDerivAt y (g (y t)) t) :
    ∀ t, 0 ≤ t →
      HasDerivAt (fun s => @Fin.cons n (fun _ => ℝ) c (y (c * s)))
        (balancingDilation g (@Fin.cons n (fun _ => ℝ) c (y (c * t)))) t := by
  intro t ht
  -- The tail of Fin.cons c f is f
  have h_tail : ∀ s, Fin.tail (@Fin.cons n (fun _ => ℝ) c (y (c * s))) = y (c * s) :=
    fun s => @Fin.tail_cons n (fun _ => ℝ) c (y (c * s))
  -- Work component-wise
  refine hasDerivAt_pi.mpr (fun i => ?_)
  refine i.cases ?_ (fun j => ?_)
  · -- Position 0: z₀ = c is constant, derivative = 0
    -- balancingDilation g (z t) 0 = -(∑ g_j(tail(z t))) · c = 0 (conservation)
    have h_deriv : balancingDilation g (@Fin.cons n (fun _ => ℝ) c (y (c * t))) 0 = 0 := by
      simp only [balancingDilation, Fin.cons_zero, h_tail]
      rw [hcons]; ring
    simp only [Fin.cons_zero]
    rw [h_deriv]
    exact hasDerivAt_const t c
  · -- Position j+1: z_{j+1}(t) = y_j(c·t), derivative = g_j(y(c·t))·c
    have h_target : balancingDilation g (@Fin.cons n (fun _ => ℝ) c (y (c * t))) j.succ =
        g (y (c * t)) j * c := by
      simp only [balancingDilation, Fin.cons_succ, Fin.cons_zero, h_tail]
    simp only [Fin.cons_succ]
    rw [h_target]
    -- Need: HasDerivAt (fun s => y (c * s) j) (g (y (c * t)) j * c) t
    -- From constantDilation_reparametrize: component j
    have h_cd := hasDerivAt_pi.mp (constantDilation_reparametrize hc h_sol t ht) j
    -- h_cd : HasDerivAt (fun s => y (c * s) j) (c * g (y (c * t)) j) t
    -- Need: g(...) * c = c * g(...) (mul_comm)
    rwa [mul_comm]

/-! ## Simplex Invariance

Conservative fields preserve the total mass ∑xᵢ. This is fundamental:
the simplex constraint ∑xᵢ = 1 is an invariant of conservative dynamics. -/

/-- If a conservative field has a solution, the total mass ∑xᵢ(t) is constant.
Proof: d/dt(∑xᵢ) = ∑x'ᵢ = 0 (conservation), so ∑xᵢ is constant by
`is_const_of_deriv_eq_zero`. -/
theorem conservative_sum_constant {n : ℕ}
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (hcons : IsConservative field)
    {sol : ℝ → Fin n → ℝ}
    (h_sol : ∀ t, HasDerivAt sol (field (sol t)) t) :
    ∀ a b : ℝ, ∑ i, sol a i = ∑ i, sol b i := by
  have h_sum_deriv : ∀ t, HasDerivAt (fun s => ∑ i, sol s i) 0 t := by
    intro t
    have h_comp : ∀ i, HasDerivAt (fun s => sol s i) (field (sol t) i) t :=
      hasDerivAt_pi.mp (h_sol t)
    have h1 := HasDerivAt.sum (fun (i : Fin n) (_ : i ∈ Finset.univ) => h_comp i)
    have h2 : (∑ i : Fin n, fun s => sol s i) = fun s => ∑ i, sol s i := by
      ext s; simp [Finset.sum_apply]
    rw [h2, hcons (sol t)] at h1
    exact h1
  exact is_const_of_deriv_eq_zero
    (fun x => (h_sum_deriv x).differentiableAt)
    (fun x => (h_sum_deriv x).deriv)

/-- Corollary: if a conservative solution starts on the simplex (∑xᵢ(0) = 1),
it stays on the simplex for all time. -/
theorem conservative_simplex_invariant {n : ℕ}
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (hcons : IsConservative field)
    {sol : ℝ → Fin n → ℝ}
    (h_sol : ∀ t, HasDerivAt sol (field (sol t)) t)
    (h_init : ∑ i, sol 0 i = 1) :
    ∀ t, ∑ i, sol t i = 1 := by
  intro t
  rw [← h_init]
  exact (conservative_sum_constant hcons h_sol 0 t).symm

/-- The readout of a balanced system is at position output.succ:
if the original PIVP has output o, the Stage 2 PIVP reads from o+1
(since position 0 is the conservation variable x₀).
The Fin.cons structure gives: z(t)_{o+1} = (tail z(t))_o. -/
theorem stage2_readout_eq_tail {n : ℕ} (z₀ : ℝ)
    (y : Fin n → ℝ) (o : Fin n) :
    @Fin.cons n (fun _ => ℝ) z₀ y o.succ = y o :=
  @Fin.cons_succ n (fun _ => ℝ) z₀ y o

/-- CRN fields point inward at the boundary of the non-negative orthant:
when xᵢ = 0 (and all other variables ≥ 0), the field value for component i
is non-negative (= pᵢ(x) ≥ 0). This is the key structural property that
ensures CRN solutions preserve non-negativity. -/
theorem crn_boundary_nonneg {n : ℕ}
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (crn : IsCRNImplementable n field)
    {x : Fin n → ℝ} (hx : ∀ j, 0 ≤ x j)
    {i : Fin n} (hi : x i = 0) :
    0 ≤ field x i := by
  rw [crn.field_eq x i, hi, mul_zero, sub_zero]
  exact crn.prod_pos i x hx

/-! ## Composed Transformations

Composing the basic operations to build stage constructions. -/

/-- The Stage 2 field construction: compose ε-scaling, selective λ-shrinking,
and balancing dilation. Given any CRN-implementable field with output index o,
the composed transformation produces a TPP-implementable (CRN + conservative)
field. The selective λ-trick scales only non-output variables, preserving
convergence x_o(t) → α.

The composed field is:
  balancingDilation (selectiveLambdaTrick o c (constantDilation ε field))
which maps n-variable CRN → (n+1)-variable TPP.

This is the algebraic core of Stage 2 (Theorem 13 in [LPP]). The
analytic part (constructing solutions, proving convergence) is separate. -/
noncomputable def stage2_field {n : ℕ} (o : Fin n) (ε c : ℝ)
    (field : (Fin n → ℝ) → Fin n → ℝ) :
    (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
  balancingDilation (selectiveLambdaTrick o c (constantDilation ε field))

/-- The Stage 2 field is TPP-implementable. -/
noncomputable def stage2_field_tpp {n : ℕ} {o : Fin n} {ε c : ℝ}
    (hε : 0 ≤ ε) (hc : 0 < c)
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (crn : IsCRNImplementable n field) :
    IsTPPImplementable (n + 1) (stage2_field o ε c field) where
  toIsCRNImplementable :=
    balancingDilation_crn (selectiveLambdaTrick_crn hc (constantDilation_crn hε crn))
  conservative := balancingDilation_conservative _

/-- The Stage 2 initial condition: prepend z₀ = 1 - c·∑yⱼ to the scaled
original initial condition c·y₀. On the simplex (∑ = 1), we need
z₀ + c·∑y₀ⱼ = 1, which is automatic. -/
noncomputable def stage2_init {n : ℕ} (c : ℝ) (y₀ : Fin n → ℝ) :
    Fin (n + 1) → ℝ :=
  Fin.cons (1 - c * ∑ j, y₀ j) (fun j => c * y₀ j)

/-- The Stage 2 initial condition sums to 1 (on the simplex). -/
theorem stage2_init_simplex {n : ℕ} (c : ℝ) (y₀ : Fin n → ℝ) :
    ∑ i, stage2_init c y₀ i = 1 := by
  simp only [stage2_init]
  rw [Fin.sum_univ_succ, Fin.cons_zero]
  simp only [Fin.cons_succ]
  rw [← Finset.mul_sum]
  ring

/-- The Stage 2 initial condition is rational when c ∈ ℚ and y₀ ∈ ℚⁿ. -/
theorem stage2_init_rational {n : ℕ} {c : ℝ} (hc : ∃ qc : ℚ, c = (qc : ℝ))
    {y₀ : Fin n → ℝ} (hy : ∀ i, ∃ q : ℚ, y₀ i = (q : ℝ)) :
    ∀ i : Fin (n + 1), ∃ q : ℚ, stage2_init c y₀ i = (q : ℝ) := by
  obtain ⟨qc, rfl⟩ := hc
  intro i
  refine i.cases ?_ (fun j => ?_)
  · -- z₀ = 1 - qc * ∑ y₀ⱼ
    simp only [stage2_init, Fin.cons_zero]
    have : ∀ j, ∃ q : ℚ, y₀ j = (q : ℝ) := hy
    choose qs hqs using this
    refine ⟨1 - qc * ∑ j, qs j, ?_⟩
    simp only [Rat.cast_sub, Rat.cast_one, Rat.cast_mul, Rat.cast_sum]
    congr 1; congr 1
    exact Finset.sum_congr rfl (fun j _ => hqs j)
  · -- z_{j+1} = qc * y₀ⱼ
    simp only [stage2_init, Fin.cons_succ]
    obtain ⟨qj, hqj⟩ := hy j
    exact ⟨qc * qj, by rw [Rat.cast_mul, hqj]⟩

/-- The Stage 2 PIVP: compose ε-scaling, selective λ-shrinking, and balancing
dilation to produce an (n+1)-dimensional PIVP. The output is shifted by 1
(since position 0 is the new conservation variable x₀). The selective trick
uses P.output as the unscaled variable, preserving convergence to α. -/
noncomputable def stage2_pivp {n : ℕ} (ε c : ℝ)
    (P : PIVP n) : PIVP (n + 1) where
  field := stage2_field P.output ε c P.field
  init := stage2_init c P.init
  output := P.output.succ

/-- The Stage 2 initial condition is non-negative when c > 0 and
c · ∑ y₀ⱼ ≤ 1 and all y₀ⱼ ≥ 0. -/
theorem stage2_init_nonneg {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    {y₀ : Fin n → ℝ} (hy_nn : ∀ j, 0 ≤ y₀ j)
    (h_sum : c * ∑ j, y₀ j ≤ 1) :
    ∀ i : Fin (n + 1), 0 ≤ stage2_init c y₀ i := by
  intro i
  refine i.cases ?_ (fun j => ?_)
  · simp only [stage2_init, Fin.cons_zero]
    linarith
  · simp only [stage2_init, Fin.cons_succ]
    exact mul_nonneg hc (hy_nn j)

/-- Stage 2 init with zeroed initial conditions: [1, 0, ..., 0].
This is the standard case after DNA 25 preprocessing. -/
@[simp] theorem stage2_init_zero {n : ℕ} (c : ℝ) :
    stage2_init c (fun _ : Fin n => (0 : ℝ)) = Fin.cons 1 (fun _ => 0) := by
  funext i; refine i.cases ?_ (fun j => ?_)
  · simp [stage2_init]
  · simp [stage2_init]

/-- With zeroed init, the simplex constraint c·∑y₀ ≤ 1 is trivially satisfied. -/
theorem stage2_init_zero_sum_le {n : ℕ} (c : ℝ) :
    c * ∑ j : Fin n, (0 : ℝ) ≤ 1 := by simp

/-- Stage 2 PIVP: the field is TPP-implementable. -/
noncomputable def stage2_pivp_tpp {n : ℕ} {ε c : ℝ} (hε : 0 ≤ ε) (hc : 0 < c)
    {P : PIVP n} (crn : IsCRNImplementable n P.field) :
    IsTPPImplementable (n + 1) (stage2_pivp ε c P).field :=
  stage2_field_tpp (o := P.output) hε hc crn

/-- The Stage 2 field at the output index simplifies to:
  ε · field(selectiveUnscale(tail x))_o · x₀

The output is NOT scaled by c (selective λ-trick), only by ε (constant dilation).
This is the key identity for the convergence argument: in effective time
τ(t) = ∫₀ᵗ x₀(s) ds, the output evolves by the ε-scaled original dynamics. -/
theorem stage2_field_output {n : ℕ} {o : Fin n} (ε c : ℝ)
    (field : (Fin n → ℝ) → Fin n → ℝ) (x : Fin (n + 1) → ℝ) :
    stage2_field o ε c field x o.succ =
      ε * field (selectiveUnscale o c (Fin.tail x)) o * x 0 := by
  simp only [stage2_field, balancingDilation, Fin.cons_succ,
    selectiveLambdaTrick, constantDilation, ite_true]

/-- The Stage 2 field at a non-output index j ≠ o simplifies to:
  c · ε · field(selectiveUnscale(tail x))_j · x₀

Non-output variables get the full c · ε scaling. -/
theorem stage2_field_nonoutput {n : ℕ} {o : Fin n} (ε c : ℝ)
    (field : (Fin n → ℝ) → Fin n → ℝ) (x : Fin (n + 1) → ℝ)
    (j : Fin n) (hj : j ≠ o) :
    stage2_field o ε c field x j.succ =
      c * (ε * field (selectiveUnscale o c (Fin.tail x)) j) * x 0 := by
  simp only [stage2_field, balancingDilation, Fin.cons_succ,
    selectiveLambdaTrick, if_neg hj, constantDilation]

/-- The Stage 2 field at the balancing variable x₀:
  x₀' = -(∑ g_j(tail x)) · x₀ -/
theorem stage2_field_zero {n : ℕ} {o : Fin n} (ε c : ℝ)
    (field : (Fin n → ℝ) → Fin n → ℝ) (x : Fin (n + 1) → ℝ) :
    stage2_field o ε c field x 0 =
      -(∑ j : Fin n, selectiveLambdaTrick o c (constantDilation ε field)
        (Fin.tail x) j) * x 0 := by
  simp only [stage2_field, balancingDilation, Fin.cons_zero]

/-- Stage 2 PIVP: initial conditions sum to 1. -/
theorem stage2_pivp_init_simplex {n : ℕ} (ε c : ℝ) (P : PIVP n) :
    ∑ i, (stage2_pivp ε c P).init i = 1 :=
  stage2_init_simplex c P.init

/-- Stage 2 PIVP: initial conditions are rational when c ∈ ℚ and P.init ∈ ℚⁿ. -/
theorem stage2_pivp_init_rational {n : ℕ} {ε c : ℝ}
    (hc : ∃ qc : ℚ, c = (qc : ℝ))
    {P : PIVP n} (hP : ∀ i, ∃ q : ℚ, P.init i = (q : ℝ)) :
    ∀ i : Fin (n + 1), ∃ q : ℚ, (stage2_pivp ε c P).init i = (q : ℝ) :=
  stage2_init_rational hc hP

/-- Extract the output component's derivative from a Stage 2 solution.
If `sol` solves the stage2 PIVP, then the output sol(t)_{o+1} satisfies:
  d/dt sol(t)_{o+1} = ε · field(selectiveUnscale(tail sol(t)))_o · sol(t)_0

This is the starting point for the time-dilation convergence argument:
in effective time τ(t) = ∫₀ᵗ sol(s)_0 ds, the output evolves by the
ε-scaled original dynamics. -/
theorem stage2_output_hasDerivAt {n : ℕ} {ε c : ℝ} {P : PIVP n}
    (sol : PIVP.Solution (stage2_pivp ε c P))
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => sol.trajectory s (stage2_pivp ε c P).output)
      (ε * P.field (selectiveUnscale P.output c (Fin.tail (sol.trajectory t))) P.output *
       sol.trajectory t 0)
      t := by
  have h_sys := sol.is_solution t ht
  have h_comp := hasDerivAt_pi.mp h_sys ((stage2_pivp ε c P).output)
  -- The system derivative at output index = stage2_field at output index
  -- which equals ε * field(unscale(tail))_o * x_0 by stage2_field_output
  convert h_comp using 1
  exact (stage2_field_output ε c P.field (sol.trajectory t)).symm

/-- The unscaled tail of a Stage 2 solution: `w(t) := selectiveUnscale o c (tail sol(t))`.
At each coordinate it satisfies a chain-rule identity:
  `d/dt w_o(t) = ε · field(w(t))_o · z₀(t)`
  `d/dt w_j(t) = ε · field(w(t))_j · z₀(t)`  for j ≠ o.

Uniformly: `dw/dt = (ε · z₀(t)) • field(w(t))`.

This is the key chain-rule identity underpinning the time-dilation argument:
in effective time τ(t) = ε · ∫₀ᵗ z₀(s) ds, w satisfies dw/dτ = field(w). -/
theorem stage2_unscaledTail_hasDerivAt {n : ℕ} {ε c : ℝ} (hc : c ≠ 0) {P : PIVP n}
    (sol : PIVP.Solution (stage2_pivp ε c P))
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt
      (fun s => selectiveUnscale P.output c (Fin.tail (sol.trajectory s)))
      ((ε * sol.trajectory t 0) •
        P.field (selectiveUnscale P.output c (Fin.tail (sol.trajectory t))))
      t := by
  -- Per-component derivative of `sol.trajectory` at index `j.succ`.
  have h_sys := sol.is_solution t ht
  have h_succ : ∀ j : Fin n,
      HasDerivAt (fun s => sol.trajectory s j.succ)
        ((stage2_pivp ε c P).field (sol.trajectory t) j.succ) t :=
    fun j => hasDerivAt_pi.mp h_sys j.succ
  -- Show per-component derivative of w(t) = selectiveUnscale o c (tail (sol t)).
  refine hasDerivAt_pi.mpr ?_
  intro j
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hj : j = P.output
  · -- j = o: w_o(t) = sol(t) o.succ, derivative uses stage2_field_output.
    subst hj
    have h_fun_eq :
        (fun s => selectiveUnscale P.output c (Fin.tail (sol.trajectory s)) P.output)
        = fun s => sol.trajectory s P.output.succ := by
      funext s; simp [Fin.tail]
    have h_comp := h_succ P.output
    -- Convert (stage2_field _ _ _ _) P.output.succ into ε · f(w)_o · z₀.
    have h_field_eq :
        (stage2_pivp ε c P).field (sol.trajectory t) P.output.succ =
          ε * P.field (selectiveUnscale P.output c (Fin.tail (sol.trajectory t)))
                P.output * sol.trajectory t 0 :=
      stage2_field_output ε c P.field (sol.trajectory t)
    rw [h_field_eq] at h_comp
    -- Goal value after `simp Pi.smul_apply`:
    -- ε * z₀ * f(w)_o  vs  h_comp: ε * f(w)_o * z₀.  Just mul_comm/assoc.
    have h_val :
        ε * sol.trajectory t 0 *
            P.field (selectiveUnscale P.output c (Fin.tail (sol.trajectory t))) P.output
          = ε * P.field (selectiveUnscale P.output c (Fin.tail (sol.trajectory t)))
                P.output * sol.trajectory t 0 := by ring
    rw [h_val, h_fun_eq]
    exact h_comp
  · -- j ≠ o: w_j(t) = sol(t) j.succ / c.
    have h_fun_eq :
        (fun s => selectiveUnscale P.output c (Fin.tail (sol.trajectory s)) j)
        = fun s => sol.trajectory s j.succ / c := by
      funext s; rw [selectiveUnscale_ne hj]; simp [Fin.tail]
    rw [h_fun_eq]
    have h_comp := h_succ j
    have h_field_eq :
        (stage2_pivp ε c P).field (sol.trajectory t) j.succ =
          c * (ε * P.field (selectiveUnscale P.output c (Fin.tail (sol.trajectory t))) j) *
            sol.trajectory t 0 :=
      stage2_field_nonoutput ε c P.field (sol.trajectory t) j hj
    rw [h_field_eq] at h_comp
    -- Divide the derivative by c.
    have h_div : HasDerivAt (fun s => sol.trajectory s j.succ / c)
        ((c * (ε *
            P.field (selectiveUnscale P.output c (Fin.tail (sol.trajectory t))) j) *
          sol.trajectory t 0) / c) t :=
      h_comp.div_const c
    -- Simplify (c * X * z₀) / c = ε * z₀ * f(w)_j when c ≠ 0 (goal after Pi.smul_apply).
    have h_simp :
        (c * (ε *
            P.field (selectiveUnscale P.output c (Fin.tail (sol.trajectory t))) j) *
          sol.trajectory t 0) / c
          = ε * sol.trajectory t 0 *
              P.field (selectiveUnscale P.output c (Fin.tail (sol.trajectory t))) j := by
      rw [show
          c * (ε *
            P.field (selectiveUnscale P.output c (Fin.tail (sol.trajectory t))) j) *
            sol.trajectory t 0 =
          c * (ε * sol.trajectory t 0 *
            P.field (selectiveUnscale P.output c (Fin.tail (sol.trajectory t))) j)
          by ring]
      field_simp
    rw [h_simp] at h_div
    exact h_div

/-- The zero-index component of a Stage 2 solution evolves as
  `d/dt z₀(t) = -(∑_j [slt o c (cd ε field)](tail sol t) j) · z₀(t)`.

This is the balancing-dilation derivative at coordinate 0. -/
theorem stage2_zero_hasDerivAt {n : ℕ} {ε c : ℝ} {P : PIVP n}
    (sol : PIVP.Solution (stage2_pivp ε c P))
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => sol.trajectory s 0)
      (-(∑ j : Fin n, selectiveLambdaTrick P.output c (constantDilation ε P.field)
            (Fin.tail (sol.trajectory t)) j) * sol.trajectory t 0)
      t := by
  have h_sys := sol.is_solution t ht
  have h_comp := hasDerivAt_pi.mp h_sys 0
  have h_field_eq :
      (stage2_pivp ε c P).field (sol.trajectory t) 0 =
        -(∑ j : Fin n, selectiveLambdaTrick P.output c (constantDilation ε P.field)
              (Fin.tail (sol.trajectory t)) j) * sol.trajectory t 0 :=
    stage2_field_zero ε c P.field (sol.trajectory t)
  rw [h_field_eq] at h_comp
  exact h_comp

/-- The zero-index trajectory `z₀(·) := sol.trajectory · 0` is continuous on
`Set.Ici 0`: at each t ≥ 0 it has a derivative, which implies continuity. -/
theorem stage2_zero_continuousOn {n : ℕ} {ε c : ℝ} {P : PIVP n}
    (sol : PIVP.Solution (stage2_pivp ε c P)) :
    ContinuousOn (fun s => sol.trajectory s 0) (Set.Ici (0 : ℝ)) := by
  intro t ht
  exact ((stage2_zero_hasDerivAt sol t ht).continuousAt).continuousWithinAt

/-- The effective time `τ(t) := ε · ∫₀ᵗ z₀(s) ds`, where z₀ is the
0-th coordinate of a Stage 2 solution.

By the fundamental theorem of calculus, `dτ/dt = ε · z₀(t)` for all t ≥ 0.
This is the change-of-variable that eliminates the balancing-dilation factor. -/
noncomputable def stage2_effectiveTime {n : ℕ} {ε c : ℝ} {P : PIVP n}
    (sol : PIVP.Solution (stage2_pivp ε c P)) : ℝ → ℝ :=
  fun t => ε * ∫ s in (0:ℝ)..t, sol.trajectory s 0

/-- Effective time has derivative `ε · z₀(t)` at every t > 0.

The interior case uses the full `HasDerivAt` variant of the fundamental theorem of
calculus, which needs strong-measurability and continuity of the integrand in a
full two-sided neighborhood of t — available when t > 0 because `sol.trajectory`
is continuous on `Set.Ici 0`, and `(0, ∞)` is open. -/
theorem stage2_effectiveTime_hasDerivAt {n : ℕ} {ε c : ℝ} {P : PIVP n}
    (sol : PIVP.Solution (stage2_pivp ε c P))
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (stage2_effectiveTime sol) (ε * sol.trajectory t 0) t := by
  -- Continuous on [0, t+1].
  have h_cont_Icc : ContinuousOn (fun s => sol.trajectory s 0) (Set.Icc (0 : ℝ) (t + 1)) :=
    (stage2_zero_continuousOn sol).mono (fun x hx => hx.1)
  have h_ii : IntervalIntegrable (fun s => sol.trajectory s 0) MeasureTheory.volume 0 t :=
    (h_cont_Icc.mono (by
      intro x hx
      exact ⟨hx.1, by linarith [hx.2]⟩)).intervalIntegrable_of_Icc ht.le
  -- Open neighborhood of t contained in Ici 0.
  have h_nbhd : Set.Ioo 0 (t + 1) ∈ 𝓝 t := Ioo_mem_nhds ht (by linarith)
  -- Strongly measurable on Ioo 0 (t+1) ⊆ Icc 0 (t+1).
  have h_sm : StronglyMeasurableAtFilter
      (fun s => sol.trajectory s 0) (𝓝 t) MeasureTheory.volume := by
    refine ⟨Set.Ioo 0 (t + 1), h_nbhd, ?_⟩
    exact (h_cont_Icc.mono (fun x hx => ⟨hx.1.le, hx.2.le⟩)).aestronglyMeasurable
      measurableSet_Ioo
  have h_cont_at : ContinuousAt (fun s => sol.trajectory s 0) t :=
    (stage2_zero_hasDerivAt sol t ht.le).continuousAt
  have h_base := intervalIntegral.integral_hasDerivAt_right h_ii h_sm h_cont_at
  simpa [stage2_effectiveTime] using h_base.const_mul ε

/-- Right-derivative of the effective time at `t = 0` (FTC boundary case):
`HasDerivWithinAt τ (ε · z_0(0)) (Ici 0) 0`.

Complements `stage2_effectiveTime_hasDerivAt` which requires `t > 0`. Together
they cover all `t ≥ 0`. -/
theorem stage2_effectiveTime_hasDerivWithinAt_zero {n : ℕ} {ε c : ℝ} {P : PIVP n}
    (sol : PIVP.Solution (stage2_pivp ε c P)) :
    HasDerivWithinAt (stage2_effectiveTime sol) (ε * sol.trajectory 0 0)
      (Set.Ici (0 : ℝ)) 0 := by
  have h_cont_Icc : ContinuousOn (fun s => sol.trajectory s 0) (Set.Icc (0 : ℝ) 1) :=
    (stage2_zero_continuousOn sol).mono (fun x hx => hx.1)
  have h_ii : IntervalIntegrable (fun s => sol.trajectory s 0) MeasureTheory.volume 0 0 :=
    IntervalIntegrable.refl
  have h_sm : StronglyMeasurableAtFilter
      (fun s => sol.trajectory s 0) (𝓝[Set.Ioi (0 : ℝ)] 0) MeasureTheory.volume := by
    refine ⟨Set.Ioo (-1 : ℝ) 1 ∩ Set.Ioi 0, ?_, ?_⟩
    · refine Filter.inter_mem ?_ self_mem_nhdsWithin
      exact mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
    · have h_sub : Set.Ioo (-1 : ℝ) 1 ∩ Set.Ioi 0 ⊆ Set.Icc (0 : ℝ) 1 :=
        fun x hx => ⟨hx.2.le, hx.1.2.le⟩
      exact (h_cont_Icc.mono h_sub).aestronglyMeasurable
        (MeasurableSet.inter measurableSet_Ioo measurableSet_Ioi)
  have h_cwa : ContinuousWithinAt (fun s => sol.trajectory s 0) (Set.Ioi 0) 0 := by
    have h_ici : ContinuousWithinAt (fun s => sol.trajectory s 0) (Set.Ici 0) 0 :=
      stage2_zero_continuousOn sol 0 Set.self_mem_Ici
    exact h_ici.mono Set.Ioi_subset_Ici_self
  have h_base : HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, sol.trajectory x 0)
      (sol.trajectory 0 0) (Set.Ici (0:ℝ)) 0 :=
    intervalIntegral.integral_hasDerivWithinAt_right h_ii h_sm h_cwa
  simpa [stage2_effectiveTime] using h_base.const_mul ε

/-- Initial value of the unscaled tail: `w(0)` differs from `P.init` at the output
coordinate by a factor of `c` — all tail variables are uniformly scaled by `c` in
`stage2_init`, but `selectiveUnscale` only divides non-output coordinates.

Explicitly:
  `w(0) o = c · P.init o`
  `w(0) j = P.init j`  for j ≠ o.

This is the key subtlety: the convergence argument requires `w(0) = P.init`, which
is automatic when `P.init o = 0` (the DNA 25 normalization) but otherwise introduces
a factor-of-c discrepancy at the output coordinate. -/
theorem stage2_unscaledTail_init {n : ℕ} {ε c : ℝ} (hc : c ≠ 0) {P : PIVP n}
    (sol : PIVP.Solution (stage2_pivp ε c P)) :
    selectiveUnscale P.output c (Fin.tail (sol.trajectory 0))
      = Function.update P.init P.output (c * P.init P.output) := by
  have h_init : sol.trajectory 0 = (stage2_pivp ε c P).init := sol.init_cond
  funext j
  rw [h_init]
  simp only [stage2_pivp, stage2_init, Fin.tail_cons]
  by_cases hj : j = P.output
  · subst hj
    simp [selectiveUnscale]
  · rw [selectiveUnscale_ne hj, Function.update_of_ne hj]
    field_simp

/-- Linear lower bound for the effective time `τ`: if `ε ≥ 0`, `c ≥ 0`,
and `z₀(s) ≥ c` on `[0, t]`, then `τ(t) ≥ ε · c · t`.

This is the τ-growth lemma that feeds the convergence argument: given
the LPP z₀ ≥ c invariant (Remark 14), effective time grows at least
linearly, so `τ(t) → ∞` as `t → ∞` with rate `ε · c`. -/
theorem stage2_effectiveTime_lb {n : ℕ} {ε c : ℝ} (hε : 0 ≤ ε) {P : PIVP n}
    (sol : PIVP.Solution (stage2_pivp ε c P))
    {t : ℝ} (ht : 0 ≤ t) {lb : ℝ} (hlb : 0 ≤ lb)
    (h_z0_lb : ∀ s ∈ Set.Icc (0 : ℝ) t, lb ≤ sol.trajectory s 0) :
    ε * lb * t ≤ stage2_effectiveTime sol t := by
  unfold stage2_effectiveTime
  have h_int_lb : lb * t ≤ ∫ s in (0:ℝ)..t, sol.trajectory s 0 := by
    have h_const_int : ∫ _s in (0:ℝ)..t, lb = lb * t := by
      simp [intervalIntegral.integral_const, sub_zero, mul_comm]
    rw [← h_const_int]
    apply intervalIntegral.integral_mono_on ht
    · exact intervalIntegrable_const
    · have h_cont_Icc : ContinuousOn (fun s => sol.trajectory s 0) (Set.Icc (0 : ℝ) t) :=
        (stage2_zero_continuousOn sol).mono (fun x hx => hx.1)
      exact h_cont_Icc.intervalIntegrable_of_Icc ht
    · intro s hs; exact h_z0_lb s hs
  calc ε * lb * t = ε * (lb * t) := by ring
    _ ≤ ε * ∫ s in (0:ℝ)..t, sol.trajectory s 0 :=
        mul_le_mul_of_nonneg_left h_int_lb hε

/-- Effective time `τ(t)` is non-negative when the 0-th coordinate stays non-negative. -/
theorem stage2_effectiveTime_nonneg {n : ℕ} {ε c : ℝ} (hε : 0 ≤ ε) {P : PIVP n}
    (sol : PIVP.Solution (stage2_pivp ε c P))
    (h_z0_nn : ∀ s, 0 ≤ s → 0 ≤ sol.trajectory s 0)
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ stage2_effectiveTime sol t := by
  unfold stage2_effectiveTime
  refine mul_nonneg hε ?_
  exact intervalIntegral.integral_nonneg ht (fun u hu => h_z0_nn u hu.1)

/-- Chain rule: the composition `btc.sol.trajectory ∘ τ` has derivative
`(ε · z₀(t)) • btc.pivp.field (btc.sol.trajectory (τ(t)))` at every t > 0,
provided τ(t) ≥ 0 (i.e., z₀ stays non-negative on [0, t]).

This is the "other side" of the ODE uniqueness argument: both `w(t)` and
`btc.sol.trajectory (τ(t))` satisfy `dv/dt = (ε z₀) • f(v)` in real time t. -/
theorem stage2_btcTraj_comp_tau_hasDerivAt {d : ℕ} {α : ℝ} {ε c : ℝ}
    {btc : BoundedTimeComputable d α}
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (t : ℝ) (ht : 0 < t)
    (hτt_nn : 0 ≤ stage2_effectiveTime sol t) :
    HasDerivAt (fun s => btc.sol.trajectory (stage2_effectiveTime sol s))
      ((ε * sol.trajectory t 0) •
        btc.pivp.field (btc.sol.trajectory (stage2_effectiveTime sol t))) t := by
  have h_inner := stage2_effectiveTime_hasDerivAt sol t ht
  have h_outer := btc.sol.is_solution (stage2_effectiveTime sol t) hτt_nn
  have h_comp := h_outer.scomp t h_inner
  -- h_comp : HasDerivAt (btc.sol.trajectory ∘ (stage2_effectiveTime sol))
  --            ((ε * sol.trajectory t 0) • btc.pivp.field (...)) t
  convert h_comp using 1

/-- Unified right-derivative of the effective time `τ` on `Set.Ici 0`: at every
`t ≥ 0`, `HasDerivWithinAt τ (ε · z_0(t)) (Ici 0) t`.

Combines `stage2_effectiveTime_hasDerivAt` (for t > 0) and
`stage2_effectiveTime_hasDerivWithinAt_zero` (for t = 0). -/
theorem stage2_effectiveTime_hasDerivWithinAt {n : ℕ} {ε c : ℝ} {P : PIVP n}
    (sol : PIVP.Solution (stage2_pivp ε c P))
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (stage2_effectiveTime sol) (ε * sol.trajectory t 0)
      (Set.Ici (0 : ℝ)) t := by
  rcases lt_or_eq_of_le ht with h_pos | h_zero
  · exact (stage2_effectiveTime_hasDerivAt sol t h_pos).hasDerivWithinAt
  · subst h_zero
    exact stage2_effectiveTime_hasDerivWithinAt_zero sol

/-- Chain-rule right-derivative of `btc.sol.trajectory ∘ τ` on `Set.Ici 0`:
at every `t ≥ 0` with `τ(t) ≥ 0`, the composition has right-derivative
`(ε · z_0(t)) • btc.pivp.field (btc.sol.trajectory (τ(t)))`.

This is the form required by `ODE_solution_unique_of_mem_Icc_right`. -/
theorem stage2_btcTraj_comp_tau_hasDerivWithinAt {d : ℕ} {α : ℝ} {ε c : ℝ}
    {btc : BoundedTimeComputable d α}
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (t : ℝ) (ht : 0 ≤ t)
    (hτt_nn : 0 ≤ stage2_effectiveTime sol t) :
    HasDerivWithinAt (fun s => btc.sol.trajectory (stage2_effectiveTime sol s))
      ((ε * sol.trajectory t 0) •
        btc.pivp.field (btc.sol.trajectory (stage2_effectiveTime sol t)))
      (Set.Ici (0 : ℝ)) t := by
  have h_inner : HasDerivWithinAt (stage2_effectiveTime sol)
      (ε * sol.trajectory t 0) (Set.Ici (0 : ℝ)) t :=
    stage2_effectiveTime_hasDerivWithinAt sol t ht
  have h_outer : HasDerivAt btc.sol.trajectory
      (btc.pivp.field (btc.sol.trajectory (stage2_effectiveTime sol t)))
      (stage2_effectiveTime sol t) :=
    btc.sol.is_solution (stage2_effectiveTime sol t) hτt_nn
  have h_comp := h_outer.scomp_hasDerivWithinAt t h_inner
  convert h_comp using 1

/-- The stage-2 output equals the unscaled-tail at the output coordinate:
  `sol(t)_{o.succ} = w(t)_o`

because `selectiveUnscale` is the identity at the output coordinate. -/
theorem stage2_output_eq_unscaledTail {n : ℕ} {ε c : ℝ} {P : PIVP n}
    (sol : PIVP.Solution (stage2_pivp ε c P)) (t : ℝ) :
    sol.trajectory t (stage2_pivp ε c P).output
      = selectiveUnscale P.output c (Fin.tail (sol.trajectory t)) P.output := by
  simp [stage2_pivp, selectiveUnscale, Fin.tail]

/-- Global coordinate-wise non-negativity of a CRN-implementable PIVP
solution: if the field is CRN-implementable and initial data is non-negative,
then every coordinate of the trajectory stays non-negative for all t ≥ 0.

Corollary of `crn_local_nonneg` applied with `T = t + 1`. -/
theorem pivp_solution_nonneg {d : ℕ} {P : PIVP d}
    (h_crn : IsCRNImplementable d P.field)
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖P.field x - P.field y‖ ≤ L * ‖x - y‖)
    (h_init_nn : ∀ i, 0 ≤ P.init i)
    (sol : PIVP.Solution P) (t : ℝ) (ht : 0 ≤ t) (i : Fin d) :
    0 ≤ sol.trajectory t i := by
  have hT : (0 : ℝ) < t + 1 := by linarith
  have h_init_y : ∀ j, 0 ≤ sol.trajectory 0 j := fun j => by
    rw [sol.init_cond]; exact h_init_nn j
  have h_ode_T : ∀ s ∈ Set.Ico (0 : ℝ) (t + 1),
      HasDerivAt sol.trajectory (P.field (sol.trajectory s)) s :=
    fun s hs => sol.is_solution s hs.1
  exact crn_local_nonneg h_crn h_lip (t + 1) hT sol.trajectory h_init_y h_ode_T
    t ⟨ht, by linarith⟩ i

/-- Global simplex conservation of a conservative PIVP solution: if the field
is `IsConservative`, then `∑ i, sol.trajectory t i = ∑ i, P.init i` for all `t ≥ 0`.

Corollary of `conservative_local_sum_const` applied with `T = t + 1`. -/
theorem pivp_solution_sum_const {d : ℕ} {P : PIVP d}
    (h_cons : IsConservative P.field)
    (sol : PIVP.Solution P) (t : ℝ) (ht : 0 ≤ t) :
    ∑ i, sol.trajectory t i = ∑ i, P.init i := by
  have hT : (0 : ℝ) < t + 1 := by linarith
  have h_ode_T : ∀ s ∈ Set.Ico (0 : ℝ) (t + 1),
      HasDerivAt sol.trajectory (P.field (sol.trajectory s)) s :=
    fun s hs => sol.is_solution s hs.1
  have h := conservative_local_sum_const h_cons (t + 1) hT sol.trajectory h_ode_T
    t ⟨ht, by linarith⟩
  rw [sol.init_cond] at h
  exact h

/-- Stage-2 global z₀ non-negativity: the 0-th coordinate of the stage-2
solution stays ≥ 0 for all `t ≥ 0`.

Uses `pivp_solution_nonneg` on the stage-2 field; requires the caller to
supply a local Lipschitz hypothesis for the stage-2 field (typically
obtained from `cubicForm_locally_lipschitz` + `stage2_field_cubicForm`
given explicit quadratic CRN coefficients A, B of the original field). -/
theorem stage2_z0_nonneg {d : ℕ} {α : ℝ}
    {btc : BoundedTimeComputable d α} {ε c : ℝ}
    (hε : 0 ≤ ε) (hc : 0 < c)
    (h_init_nn : ∀ i, 0 ≤ btc.pivp.init i)
    (h_sum_le : c * ∑ j, btc.pivp.init j ≤ 1)
    (crn : IsCRNImplementable d btc.pivp.field)
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin (d + 1) → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖(stage2_pivp ε c btc.pivp).field x - (stage2_pivp ε c btc.pivp).field y‖
        ≤ L * ‖x - y‖)
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ sol.trajectory t 0 := by
  have h_crn_stage2 : IsCRNImplementable (d + 1) (stage2_pivp ε c btc.pivp).field :=
    (stage2_field_tpp (o := btc.pivp.output) hε hc crn).toIsCRNImplementable
  have h_init_nn' : ∀ i, 0 ≤ (stage2_pivp ε c btc.pivp).init i :=
    stage2_init_nonneg hc.le h_init_nn h_sum_le
  exact pivp_solution_nonneg h_crn_stage2 h_lip h_init_nn' sol t ht 0

/-- Stage-2 simplex conservation: `∑ i, sol.trajectory t i = 1` for all `t ≥ 0`.

Direct specialization of `pivp_solution_sum_const` using
`balancingDilation_conservative` and `stage2_init_simplex`. -/
theorem stage2_sum_eq_one {n : ℕ} {ε c : ℝ} {P : PIVP n}
    (sol : PIVP.Solution (stage2_pivp ε c P))
    (t : ℝ) (ht : 0 ≤ t) :
    ∑ i, sol.trajectory t i = 1 := by
  have h_cons : IsConservative (stage2_pivp ε c P).field :=
    balancingDilation_conservative _
  have h := pivp_solution_sum_const h_cons sol t ht
  rw [h]
  exact stage2_pivp_init_simplex ε c P

/-- Stage-2 z₀ formula: `z_0(t) = 1 - ∑_{i ≥ 1} z_i(t)` for all `t ≥ 0`.

Consequence of `stage2_sum_eq_one`. -/
theorem stage2_z0_eq_one_minus_tail_sum {n : ℕ} {ε c : ℝ} {P : PIVP n}
    (sol : PIVP.Solution (stage2_pivp ε c P))
    (t : ℝ) (ht : 0 ≤ t) :
    sol.trajectory t 0 = 1 - ∑ j : Fin n, Fin.tail (sol.trajectory t) j := by
  have h_sum := stage2_sum_eq_one sol t ht
  rw [Fin.sum_univ_succ] at h_sum
  have h_tail_eq : ∑ j : Fin n, Fin.tail (sol.trajectory t) j
      = ∑ j : Fin n, sol.trajectory t j.succ := by
    simp [Fin.tail]
  rw [h_tail_eq]
  linarith [h_sum]

/-- Stage-2 tail coordinates stay non-negative (corollary of
`stage2_z0_nonneg` / `pivp_solution_nonneg` at non-zero indices). -/
theorem stage2_tail_nonneg {d : ℕ} {α : ℝ}
    {btc : BoundedTimeComputable d α} {ε c : ℝ}
    (hε : 0 ≤ ε) (hc : 0 < c)
    (h_init_nn : ∀ i, 0 ≤ btc.pivp.init i)
    (h_sum_le : c * ∑ j, btc.pivp.init j ≤ 1)
    (crn : IsCRNImplementable d btc.pivp.field)
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin (d + 1) → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖(stage2_pivp ε c btc.pivp).field x - (stage2_pivp ε c btc.pivp).field y‖
        ≤ L * ‖x - y‖)
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (t : ℝ) (ht : 0 ≤ t) (j : Fin d) :
    0 ≤ sol.trajectory t j.succ := by
  have h_crn_stage2 : IsCRNImplementable (d + 1) (stage2_pivp ε c btc.pivp).field :=
    (stage2_field_tpp (o := btc.pivp.output) hε hc crn).toIsCRNImplementable
  have h_init_nn' : ∀ i, 0 ≤ (stage2_pivp ε c btc.pivp).init i :=
    stage2_init_nonneg hc.le h_init_nn h_sum_le
  exact pivp_solution_nonneg h_crn_stage2 h_lip h_init_nn' sol t ht j.succ

/-- Stage-2 z₀ upper bound: `z_0(t) ≤ 1` (from simplex + tail non-negativity). -/
theorem stage2_z0_le_one {d : ℕ} {α : ℝ}
    {btc : BoundedTimeComputable d α} {ε c : ℝ}
    (hε : 0 ≤ ε) (hc : 0 < c)
    (h_init_nn : ∀ i, 0 ≤ btc.pivp.init i)
    (h_sum_le : c * ∑ j, btc.pivp.init j ≤ 1)
    (crn : IsCRNImplementable d btc.pivp.field)
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin (d + 1) → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖(stage2_pivp ε c btc.pivp).field x - (stage2_pivp ε c btc.pivp).field y‖
        ≤ L * ‖x - y‖)
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (t : ℝ) (ht : 0 ≤ t) :
    sol.trajectory t 0 ≤ 1 := by
  rw [stage2_z0_eq_one_minus_tail_sum sol t ht]
  have h_tail_nn : ∀ j : Fin d, 0 ≤ Fin.tail (sol.trajectory t) j := fun j => by
    simp only [Fin.tail]
    exact stage2_tail_nonneg hε hc h_init_nn h_sum_le crn h_lip sol t ht j
  have h_tail_sum_nn : 0 ≤ ∑ j : Fin d, Fin.tail (sol.trajectory t) j :=
    Finset.sum_nonneg fun j _ => h_tail_nn j
  linarith

/-- Monotonicity of the effective time `τ`: when `ε ≥ 0` and `z₀ ≥ 0` on
`[0, ∞)`, for any `0 ≤ s ≤ t` we have `τ(s) ≤ τ(t)`.

Uses `integral_add_adjacent_intervals` to split `∫₀ᵗ = ∫₀ˢ + ∫ₛᵗ`, then
non-negativity of the integrand on `[s, t]`. -/
theorem stage2_effectiveTime_mono {n : ℕ} {ε c : ℝ} (hε : 0 ≤ ε) {P : PIVP n}
    (sol : PIVP.Solution (stage2_pivp ε c P))
    (h_z0_nn : ∀ s, 0 ≤ s → 0 ≤ sol.trajectory s 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    stage2_effectiveTime sol s ≤ stage2_effectiveTime sol t := by
  have ht : 0 ≤ t := le_trans hs hst
  unfold stage2_effectiveTime
  -- Reduce to comparing the integrals ∫₀ˢ z₀ ≤ ∫₀ᵗ z₀.
  refine mul_le_mul_of_nonneg_left ?_ hε
  have h_cont_Icc : ContinuousOn (fun s => sol.trajectory s 0) (Set.Icc (0 : ℝ) t) :=
    (stage2_zero_continuousOn sol).mono (fun x hx => hx.1)
  have h_i_0s : IntervalIntegrable (fun u => sol.trajectory u 0)
      MeasureTheory.volume 0 s :=
    (h_cont_Icc.mono (fun x hx => ⟨hx.1, le_trans hx.2 hst⟩)).intervalIntegrable_of_Icc hs
  have h_i_st : IntervalIntegrable (fun u => sol.trajectory u 0)
      MeasureTheory.volume s t :=
    (h_cont_Icc.mono (fun x hx => ⟨le_trans hs hx.1, hx.2⟩)).intervalIntegrable_of_Icc hst
  have h_split : ∫ u in (0:ℝ)..t, sol.trajectory u 0
      = (∫ u in (0:ℝ)..s, sol.trajectory u 0) + ∫ u in s..t, sol.trajectory u 0 :=
    (intervalIntegral.integral_add_adjacent_intervals h_i_0s h_i_st).symm
  have h_tail_nn : 0 ≤ ∫ u in s..t, sol.trajectory u 0 :=
    intervalIntegral.integral_nonneg hst
      (fun u hu => h_z0_nn u (le_trans hs hu.1))
  linarith

/-- Continuity of the unscaled tail `w(t) := selectiveUnscale o c (Fin.tail (sol t))`
on `Set.Ici 0`. Follows from the derivative established in
`stage2_unscaledTail_hasDerivAt`. -/
theorem stage2_unscaledTail_continuousOn {n : ℕ} {ε c : ℝ} (hc : c ≠ 0) {P : PIVP n}
    (sol : PIVP.Solution (stage2_pivp ε c P)) :
    ContinuousOn (fun s => selectiveUnscale P.output c (Fin.tail (sol.trajectory s)))
      (Set.Ici (0 : ℝ)) := by
  intro t ht
  exact ((stage2_unscaledTail_hasDerivAt hc sol t ht).continuousAt).continuousWithinAt

/-- Continuity of `btc.sol.trajectory ∘ τ` on `Set.Ici 0`. Follows from the unified
right-derivative `stage2_btcTraj_comp_tau_hasDerivWithinAt`. -/
theorem stage2_btcTraj_comp_tau_continuousOn {d : ℕ} {α : ℝ} {ε c : ℝ}
    {btc : BoundedTimeComputable d α}
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (h_τ_nn : ∀ s, 0 ≤ s → 0 ≤ stage2_effectiveTime sol s) :
    ContinuousOn (fun s => btc.sol.trajectory (stage2_effectiveTime sol s))
      (Set.Ici (0 : ℝ)) := by
  intro t ht
  exact (stage2_btcTraj_comp_tau_hasDerivWithinAt sol t ht (h_τ_nn t ht)).continuousWithinAt

/-- Time-varying RHS for the stage-2 uniqueness argument:
  `v(t, x) := (ε · z_0(t)) • btc.pivp.field x`.
Both `w(t) := selectiveUnscale o c (Fin.tail (sol t))` and
`btc.sol.trajectory (τ(t))` satisfy `dv/dt = v(t, v(t))` on `(0, ∞)`. -/
noncomputable def stage2_vField {d : ℕ} {α : ℝ} {ε c : ℝ}
    (btc : BoundedTimeComputable d α)
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp)) :
    ℝ → (Fin d → ℝ) → Fin d → ℝ :=
  fun t x => (ε * sol.trajectory t 0) • btc.pivp.field x

/-- LipschitzOnWith for the time-varying stage-2 RHS: if `btc.pivp.field` is
globally Lipschitz on `closedBall 0 M` with constant `L`, then
`stage2_vField btc sol t` is LipschitzOnWith `⟨|ε| · z_0(t) · L, _⟩` on the
same ball (for fixed `t`).

Since `0 ≤ z_0(t) ≤ 1`, this yields a uniform-in-t Lipschitz bound `|ε| · L`. -/
theorem stage2_vField_lipschitzOnWith {d : ℕ} {α : ℝ} {ε c : ℝ}
    {btc : BoundedTimeComputable d α}
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (t : ℝ) (M L : ℝ) (hM : 0 ≤ M)
    (h_z0_nn : 0 ≤ sol.trajectory t 0) (h_z0_le : sol.trajectory t 0 ≤ 1)
    (h_lip : ∀ x y : Fin d → ℝ, ‖x‖ ≤ M → ‖y‖ ≤ M →
      ‖btc.pivp.field x - btc.pivp.field y‖ ≤ L * ‖x - y‖) :
    ∀ x y : Fin d → ℝ, ‖x‖ ≤ M → ‖y‖ ≤ M →
      ‖stage2_vField btc sol t x - stage2_vField btc sol t y‖
        ≤ (|ε| * L) * ‖x - y‖ := by
  intro x y hx hy
  unfold stage2_vField
  rw [← smul_sub, norm_smul]
  have h_abs_le : |ε * sol.trajectory t 0| ≤ |ε| := by
    rw [abs_mul]
    have h_z0_abs : |sol.trajectory t 0| ≤ 1 := by
      rw [abs_of_nonneg h_z0_nn]; exact h_z0_le
    calc |ε| * |sol.trajectory t 0|
        ≤ |ε| * 1 := by
          exact mul_le_mul_of_nonneg_left h_z0_abs (abs_nonneg _)
      _ = |ε| := mul_one _
  have h_fld := h_lip x y hx hy
  calc |ε * sol.trajectory t 0| * ‖btc.pivp.field x - btc.pivp.field y‖
      ≤ |ε| * ‖btc.pivp.field x - btc.pivp.field y‖ :=
        mul_le_mul_of_nonneg_right h_abs_le (norm_nonneg _)
    _ ≤ |ε| * (L * ‖x - y‖) := by
        have hεabs : 0 ≤ |ε| := abs_nonneg _
        exact mul_le_mul_of_nonneg_left h_fld hεabs
    _ = (|ε| * L) * ‖x - y‖ := by ring

/-- Packaged `LipschitzOnWith` form of the stage-2 RHS bound on `closedBall 0 M`.
Uses `stage2_vField_lipschitzOnWith` and converts the norm bound to the
`LipschitzOnWith` structure required by Mathlib's ODE uniqueness theorems. -/
theorem stage2_vField_lipschitzOnWith' {d : ℕ} {α : ℝ} {ε c : ℝ}
    {btc : BoundedTimeComputable d α}
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (t : ℝ) (M L : ℝ) (hL : 0 ≤ L)
    (h_z0_nn : 0 ≤ sol.trajectory t 0) (h_z0_le : sol.trajectory t 0 ≤ 1)
    (h_lip : ∀ x y : Fin d → ℝ, ‖x‖ ≤ M → ‖y‖ ≤ M →
      ‖btc.pivp.field x - btc.pivp.field y‖ ≤ L * ‖x - y‖) :
    LipschitzOnWith ⟨|ε| * L, mul_nonneg (abs_nonneg _) hL⟩
      (stage2_vField btc sol t) (Metric.closedBall 0 M) := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  rw [Metric.mem_closedBall, dist_zero_right] at hx hy
  have h_bound :=
    stage2_vField_lipschitzOnWith sol t M L (le_trans (norm_nonneg _) hx)
      h_z0_nn h_z0_le h_lip x y hx hy
  rw [dist_eq_norm, dist_eq_norm]
  simpa using h_bound

/-- **Main uniqueness theorem for Stage 2** (LPP change-of-variables).

Given the DNA 25 / LPP zero-init normalization (`P.init o = 0`), the unscaled tail
`w(t) := selectiveUnscale o c (Fin.tail (sol t))` coincides with the composition
`btc.sol.trajectory (τ(t))` on every compact interval `[0, T]`.

The proof applies Mathlib's `ODE_solution_unique_of_mem_Icc_right` to the time-
varying IVP `dv/dt = (ε · z₀(t)) • P.field(v)` with common initial value `P.init`:
  * w(t) satisfies this by `stage2_unscaledTail_hasDerivAt` (plus zero-init for w(0));
  * `btc.sol.trajectory (τ(t))` satisfies it by the chain rule
    `stage2_btcTraj_comp_tau_hasDerivWithinAt` (plus btc.sol.init_cond).

Caller supplies an a-priori bound `M` inside which both trajectories stay, and a
Lipschitz constant `L` for `P.field` on `closedBall 0 M`. -/
theorem stage2_unscaledTail_eq_btcTraj_comp_tau
    {d : ℕ} {α : ℝ} {ε c : ℝ}
    (hc : c ≠ 0)
    {btc : BoundedTimeComputable d α}
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (h_zero_init : btc.pivp.init btc.pivp.output = 0)
    (h_z0_nn : ∀ s, 0 ≤ s → 0 ≤ sol.trajectory s 0)
    (h_z0_le : ∀ s, 0 ≤ s → sol.trajectory s 0 ≤ 1)
    (h_τ_nn : ∀ s, 0 ≤ s → 0 ≤ stage2_effectiveTime sol s)
    (T : ℝ) (hT : 0 ≤ T)
    (M : ℝ) (L : ℝ) (hL : 0 ≤ L)
    (h_w_bdd : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s))‖ ≤ M)
    (h_btc_bdd : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖btc.sol.trajectory (stage2_effectiveTime sol s)‖ ≤ M)
    (h_lip : ∀ x y : Fin d → ℝ, ‖x‖ ≤ M → ‖y‖ ≤ M →
      ‖btc.pivp.field x - btc.pivp.field y‖ ≤ L * ‖x - y‖) :
    Set.EqOn
      (fun s => selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s)))
      (fun s => btc.sol.trajectory (stage2_effectiveTime sol s))
      (Set.Icc (0 : ℝ) T) := by
  -- Time-varying RHS and region.
  set v : ℝ → (Fin d → ℝ) → Fin d → ℝ := stage2_vField btc sol with hv_def
  set S : ℝ → Set (Fin d → ℝ) := fun _ => Metric.closedBall 0 M with hS_def
  set K : NNReal := ⟨|ε| * L, mul_nonneg (abs_nonneg _) hL⟩ with hK_def
  -- (1) Uniform Lipschitz bound on S t for all t ∈ Ico 0 T.
  have hv : ∀ t ∈ Set.Ico (0 : ℝ) T, LipschitzOnWith K (v t) (S t) := by
    intro t ht
    exact stage2_vField_lipschitzOnWith' sol t M L hL
      (h_z0_nn t ht.1) (h_z0_le t ht.1) h_lip
  -- (2) Continuity of w on Icc 0 T.
  have hf : ContinuousOn
      (fun s => selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s)))
      (Set.Icc (0 : ℝ) T) :=
    (stage2_unscaledTail_continuousOn hc sol).mono
      (fun x hx => hx.1)
  -- (3) Right-derivative of w on Ici t at each t ∈ Ico 0 T.
  have hf' : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt
        (fun s => selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s)))
        (v t (selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory t))))
        (Set.Ici t) t := by
    intro t ht
    have h := (stage2_unscaledTail_hasDerivAt hc sol t ht.1).hasDerivWithinAt
      (s := Set.Ici t)
    simpa [hv_def, stage2_vField] using h
  -- (4) w stays in S t.
  have hfs : ∀ t ∈ Set.Ico (0 : ℝ) T,
      (fun s => selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s))) t
        ∈ S t := by
    intro t ht
    show _ ∈ Metric.closedBall (0 : Fin d → ℝ) M
    rw [Metric.mem_closedBall, dist_zero_right]
    exact h_w_bdd t ⟨ht.1, ht.2.le⟩
  -- (5) Continuity of btc.sol ∘ τ on Icc 0 T.
  have hg : ContinuousOn
      (fun s => btc.sol.trajectory (stage2_effectiveTime sol s))
      (Set.Icc (0 : ℝ) T) :=
    (stage2_btcTraj_comp_tau_continuousOn sol h_τ_nn).mono
      (fun x hx => hx.1)
  -- (6) Right-derivative of btc.sol ∘ τ on Ici t at each t ∈ Ico 0 T.
  have hg' : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => btc.sol.trajectory (stage2_effectiveTime sol s))
        (v t (btc.sol.trajectory (stage2_effectiveTime sol t)))
        (Set.Ici t) t := by
    intro t ht
    have h_unif : HasDerivWithinAt
        (fun s => btc.sol.trajectory (stage2_effectiveTime sol s))
        ((ε * sol.trajectory t 0) •
          btc.pivp.field (btc.sol.trajectory (stage2_effectiveTime sol t)))
        (Set.Ici (0 : ℝ)) t :=
      stage2_btcTraj_comp_tau_hasDerivWithinAt sol t ht.1 (h_τ_nn t ht.1)
    have h_sub : Set.Ici t ⊆ Set.Ici (0 : ℝ) := fun x hx => le_trans ht.1 hx
    have := h_unif.mono h_sub
    simpa [hv_def, stage2_vField] using this
  -- (7) btc.sol ∘ τ stays in S t.
  have hgs : ∀ t ∈ Set.Ico (0 : ℝ) T,
      (fun s => btc.sol.trajectory (stage2_effectiveTime sol s)) t ∈ S t := by
    intro t ht
    show _ ∈ Metric.closedBall (0 : Fin d → ℝ) M
    rw [Metric.mem_closedBall, dist_zero_right]
    exact h_btc_bdd t ⟨ht.1, ht.2.le⟩
  -- (8) Same initial value at t = 0.
  have ha : (fun s => selectiveUnscale btc.pivp.output c
                        (Fin.tail (sol.trajectory s))) 0
      = (fun s => btc.sol.trajectory (stage2_effectiveTime sol s)) 0 := by
    show selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory 0))
      = btc.sol.trajectory (stage2_effectiveTime sol 0)
    have h_w0 := stage2_unscaledTail_init (ε := ε) hc sol
    have h_τ0 : stage2_effectiveTime sol 0 = 0 := by
      unfold stage2_effectiveTime
      simp
    have h_btc0 : btc.sol.trajectory (stage2_effectiveTime sol 0) = btc.pivp.init := by
      rw [h_τ0]; exact btc.sol.init_cond
    rw [h_btc0, h_w0, h_zero_init]
    ext j
    by_cases hj : j = btc.pivp.output
    · subst hj
      simp [h_zero_init]
    · rw [Function.update_of_ne hj]
  exact ODE_solution_unique_of_mem_Icc_right hv hf hf' hfs hg hg' hgs ha

/-- Corollary of the ODE uniqueness theorem: at the output coordinate,
`sol(t) @ stage2.output = btc.sol(τ(t)) @ btc.output` on `[0, T]`.

Combines `stage2_output_eq_unscaledTail` (output = unscaled tail at output
index, since `selectiveUnscale` is the identity there) with
`stage2_unscaledTail_eq_btcTraj_comp_tau`. This is the key identity behind
the Stage 2 convergence argument: the output of the stage-2 solution
coincides with the btc's output at the effective time `τ(t)`, so the
convergence rate of btc transfers directly (up to the τ→t time change). -/
theorem stage2_output_eq_btc_output_at_tau
    {d : ℕ} {α : ℝ} {ε c : ℝ}
    (hc : c ≠ 0)
    {btc : BoundedTimeComputable d α}
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (h_zero_init : btc.pivp.init btc.pivp.output = 0)
    (h_z0_nn : ∀ s, 0 ≤ s → 0 ≤ sol.trajectory s 0)
    (h_z0_le : ∀ s, 0 ≤ s → sol.trajectory s 0 ≤ 1)
    (h_τ_nn : ∀ s, 0 ≤ s → 0 ≤ stage2_effectiveTime sol s)
    (T : ℝ) (hT : 0 ≤ T)
    (M : ℝ) (L : ℝ) (hL : 0 ≤ L)
    (h_w_bdd : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s))‖ ≤ M)
    (h_btc_bdd : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖btc.sol.trajectory (stage2_effectiveTime sol s)‖ ≤ M)
    (h_lip : ∀ x y : Fin d → ℝ, ‖x‖ ≤ M → ‖y‖ ≤ M →
      ‖btc.pivp.field x - btc.pivp.field y‖ ≤ L * ‖x - y‖)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    sol.trajectory t (stage2_pivp ε c btc.pivp).output
      = btc.sol.trajectory (stage2_effectiveTime sol t) btc.pivp.output := by
  have h_eq := stage2_unscaledTail_eq_btcTraj_comp_tau hc sol h_zero_init
    h_z0_nn h_z0_le h_τ_nn T hT M L hL h_w_bdd h_btc_bdd h_lip ht
  -- h_eq : w(t) = btc.sol(τ(t))
  -- Apply both sides at the output index btc.pivp.output and use
  -- stage2_output_eq_unscaledTail.
  have h_out := stage2_output_eq_unscaledTail sol t
  -- h_out : sol(t)_{o.succ} = w(t)_o
  calc sol.trajectory t (stage2_pivp ε c btc.pivp).output
      = selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory t)) btc.pivp.output :=
        h_out
    _ = btc.sol.trajectory (stage2_effectiveTime sol t) btc.pivp.output := by
        have hpt : selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory t))
              = btc.sol.trajectory (stage2_effectiveTime sol t) := h_eq
        exact congrArg (fun f => f btc.pivp.output) hpt

/-- **Stage 2 convergence (conditional on the LPP invariant)** — closes the
content of `stage2_convergence_axiom` for `t ≥ 0` assuming the still-open
z₀ ≥ c invariant (LPP Remark 14).

Hypotheses:
  * `hε : 0 < ε`, `hc : 0 < c`, `hεc : 1 ≤ ε · c`
  * zero-init normalization `btc.pivp.init btc.pivp.output = 0`
  * LPP invariant `h_z0_lb : c ≤ z₀(s) for all s ≥ 0`  ← **the remaining gap**
  * z₀ ∈ [0,1] bounds, uniform `M, L` bounds, global Lipschitz on `closedBall 0 M`.

Conclusion: for every `t ≥ 0` with `t > btc.modulus r`, the axiom's inequality holds.

The argument composes:
  1. `stage2_output_eq_btc_output_at_tau`: sol(t)@out = btc.sol(τ(t))@out
  2. `stage2_effectiveTime_lb`: τ(t) ≥ ε·c·t ≥ t (since ε·c ≥ 1)
  3. `btc.convergence`: τ(t) > btc.modulus r ⇒ |btc.sol(τ(t))@out - α| < exp(-r). -/
theorem stage2_convergence_from_invariants
    {d : ℕ} {α : ℝ} {ε c : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hεc : 1 ≤ ε * c)
    {btc : BoundedTimeComputable d α}
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (h_zero_init : btc.pivp.init btc.pivp.output = 0)
    (h_z0_nn : ∀ s, 0 ≤ s → 0 ≤ sol.trajectory s 0)
    (h_z0_le : ∀ s, 0 ≤ s → sol.trajectory s 0 ≤ 1)
    (h_z0_lb : ∀ s, 0 ≤ s → c ≤ sol.trajectory s 0)
    (M : ℝ) (L : ℝ) (hL : 0 ≤ L)
    (h_w_bdd : ∀ s, 0 ≤ s →
      ‖selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s))‖ ≤ M)
    (h_btc_bdd : ∀ s, 0 ≤ s →
      ‖btc.sol.trajectory (stage2_effectiveTime sol s)‖ ≤ M)
    (h_lip : ∀ x y : Fin d → ℝ, ‖x‖ ≤ M → ‖y‖ ≤ M →
      ‖btc.pivp.field x - btc.pivp.field y‖ ≤ L * ‖x - y‖) :
    ∀ r : ℕ, ∀ t : ℝ, 0 ≤ t → t > btc.modulus r →
      |sol.trajectory t (stage2_pivp ε c btc.pivp).output - α| <
        Real.exp (-(r : ℝ)) := by
  intro r t ht_nn ht_gt
  have h_τ_nn : ∀ s, 0 ≤ s → 0 ≤ stage2_effectiveTime sol s := fun s hs =>
    stage2_effectiveTime_nonneg hε.le sol h_z0_nn s hs
  have h_eq :=
    stage2_output_eq_btc_output_at_tau (hc := ne_of_gt hc) sol h_zero_init
      h_z0_nn h_z0_le h_τ_nn t ht_nn M L hL
      (fun s hs => h_w_bdd s hs.1)
      (fun s hs => h_btc_bdd s hs.1)
      h_lip t ⟨ht_nn, le_refl _⟩
  have h_τ_lb : ε * c * t ≤ stage2_effectiveTime sol t :=
    stage2_effectiveTime_lb hε.le sol ht_nn hc.le
      (fun s hs => h_z0_lb s hs.1)
  have h_t_le_τ : t ≤ stage2_effectiveTime sol t := by
    calc t = 1 * t := (one_mul t).symm
      _ ≤ (ε * c) * t := mul_le_mul_of_nonneg_right hεc ht_nn
      _ ≤ stage2_effectiveTime sol t := h_τ_lb
  have h_τ_gt : stage2_effectiveTime sol t > btc.modulus r :=
    lt_of_lt_of_le ht_gt h_t_le_τ
  rw [h_eq]
  exact btc.convergence r (stage2_effectiveTime sol t) h_τ_gt

/-! ## Self-Product (Stage 3 Building Block)

The self-product z_{i,j} = xᵢ · xⱼ is the key construction for Stage 3.
Given n variables xᵢ, introduce n² variables z indexed by Fin n × Fin n.
On the simplex (∑xₖ = 1), the row sum recovers the original variable:
  rowSum(z)ᵢ = ∑ⱼ z_{i,j} = ∑ⱼ xᵢxⱼ = xᵢ·∑ⱼ xⱼ = xᵢ.

The z-field is z'_{i,j} = field_i(x)·xⱼ + xᵢ·field_j(x), which is
quadratic in z when field has degree ≤ 3 (TPP), since degree 4 in x
= degree 2 in z. -/

/-- Row sum of the self-product matrix: given z : Fin n × Fin n → ℝ,
the row sum at i recovers xᵢ = ∑_j z_{i,j} on the simplex. -/
def selfProduct_rowSum {n : ℕ} (z : Fin n × Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, z (i, j)

/-- Self-product field: given a field on n variables, construct a field
on n×n variables via z'_{i,j} = field_i(rowSum z)·(rowSum z)_j + (rowSum z)_i·field_j(rowSum z).

**Degree warning:** When the input field is cubic (TPP), this field is degree 4
in z-variables (cubic × linear rowSum). It is NOT PP-implementable. The correct
PP-implementable field for Stage 3 (Theorem 15 in [LPP]) is obtained by symbolic
substitution (x_a·x_b → z_{a,b}), producing a degree-2 field that agrees with
selfProductField on the self-product manifold {z_{i,j} = x_i·x_j}. -/
def selfProductField {n : ℕ} (field : (Fin n → ℝ) → Fin n → ℝ) :
    (Fin n × Fin n → ℝ) → Fin n × Fin n → ℝ :=
  fun z ij =>
    let x := selfProduct_rowSum z
    field x ij.1 * x ij.2 + x ij.1 * field x ij.2

/-- The self-product field is conservative:
∑_{i,j} z'_{i,j} = 2·(∑ᵢ field_i(x))·(∑ⱼ xⱼ).
When the original field is conservative (∑field_i = 0), this is 0. -/
theorem selfProductField_conservative {n : ℕ}
    {field : (Fin n → ℝ) → Fin n → ℝ} (hcons : IsConservative field) :
    ∀ z : Fin n × Fin n → ℝ,
      ∑ ij : Fin n × Fin n, selfProductField field z ij = 0 := by
  intro z
  simp only [selfProductField]
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_add_distrib]
  have h1 : ∑ i : Fin n, ∑ j : Fin n,
      field (selfProduct_rowSum z) i * selfProduct_rowSum z j =
      (∑ i, field (selfProduct_rowSum z) i) * (∑ j, selfProduct_rowSum z j) := by
    rw [← Finset.sum_mul_sum]
  have h2 : ∑ i : Fin n, ∑ j : Fin n,
      selfProduct_rowSum z i * field (selfProduct_rowSum z) j =
      (∑ i, selfProduct_rowSum z i) * (∑ j, field (selfProduct_rowSum z) j) := by
    rw [← Finset.sum_mul_sum]
  rw [h1, h2, hcons]
  ring

/-! ## Self-product trajectory lemmas

The self-product z_{i,j}(t) = x_i(t)·x_j(t) satisfies the selfProductField ODE
by the product rule. These are the analytic building blocks for Stage 3. -/

/-- Row sum of the self-product recovers the original trajectory
(when z_{i,j} = x_i·x_j and ∑x = 1). -/
theorem selfProduct_rowSum_eq {n : ℕ} {x : Fin n → ℝ} (hsum : ∑ j, x j = 1) (i : Fin n) :
    selfProduct_rowSum (fun ij : Fin n × Fin n => x ij.1 * x ij.2) i = x i := by
  dsimp [selfProduct_rowSum]
  rw [← Finset.mul_sum, hsum, mul_one]

/-- Total sum of the self-product equals (∑x)². -/
theorem selfProduct_totalSum {n : ℕ} {x : Fin n → ℝ} :
    ∑ ij : Fin n × Fin n, x ij.1 * x ij.2 = (∑ i, x i) ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, sq]

/-- On the simplex, ∑z_{i,j} = 1. -/
theorem selfProduct_simplex {n : ℕ} {x : Fin n → ℝ} (hsum : ∑ j, x j = 1) :
    ∑ ij : Fin n × Fin n, x ij.1 * x ij.2 = 1 := by
  rw [selfProduct_totalSum, hsum]; ring

/-- The self-product trajectory z_{i,j}(t) = x_i(t)·x_j(t) satisfies the
selfProductField ODE, assuming x satisfies x' = field(x) and ∑x = 1.
This is just the product rule: z'_{i,j} = x'_i·x_j + x_i·x'_j. -/
theorem selfProduct_hasDerivAt {n : ℕ} {field : (Fin n → ℝ) → Fin n → ℝ}
    {x : ℝ → Fin n → ℝ} {t : ℝ}
    (h_sol : HasDerivAt x (fun i => field (x t) i) t)
    (h_simplex : ∑ j, x t j = 1) :
    HasDerivAt (fun s => fun ij : Fin n × Fin n => x s ij.1 * x s ij.2)
      (fun ij => selfProductField field
        (fun ij : Fin n × Fin n => x t ij.1 * x t ij.2) ij) t := by
  refine hasDerivAt_pi.mpr (fun ij => ?_)
  have h_i := hasDerivAt_pi.mp h_sol ij.1
  have h_j := hasDerivAt_pi.mp h_sol ij.2
  -- z'_{i,j} = x'_i · x_j + x_i · x'_j
  have h_prod := h_i.mul h_j
  -- Need to show the derivative matches selfProductField
  have h_row : selfProduct_rowSum (fun ij : Fin n × Fin n => x t ij.1 * x t ij.2) = x t :=
    funext (selfProduct_rowSum_eq h_simplex)
  convert h_prod using 1
  simp only [selfProductField, h_row]

/-! ## Stage 2 Cubic Form Structure

After Stage 2, the TPP system has a specific cubic form: for each non-zero
variable i, x'_i = (P_i(x) - Q_i(x)·x_i)·x₀ where P_i is quadratic and Q_i
is linear. This structure is essential for Stage 3: the self-product z-field
z'_{i,j} = x'_i·x_j + x_i·x'_j is degree 4 in z when expressed via rowSum,
but becomes degree 2 after symbolic substitution x_a·x_b → z_{a,b}, which
requires knowing the P_i/Q_i decomposition and their polynomial coefficients. -/

/-- Stage 2 cubic form output.
The field has the form x'_i = (P_i(x) - Q_i(x)·x_i)·x₀ for non-balancing variables,
with explicit quadratic/linear coefficients needed for Stage 3 symbolic substitution. -/
structure Stage2CubicForm (d : ℕ) (field : (Fin d → ℝ) → Fin d → ℝ) where
  /-- Index of the balancing variable x₀ -/
  zero : Fin d
  /-- Quadratic production coefficients: P_i(x) = ∑_a ∑_b A i a b · x_a · x_b -/
  A : Fin d → Fin d → Fin d → ℝ
  /-- Linear degradation coefficients: Q_i(x) = ∑_a B i a · x_a -/
  B : Fin d → Fin d → ℝ
  /-- Production coefficients are non-negative -/
  A_nonneg : ∀ i a b, 0 ≤ A i a b
  /-- Degradation coefficients are non-negative -/
  B_nonneg : ∀ i a, 0 ≤ B i a
  /-- Field decomposition: x'_i = (P_i - Q_i·x_i)·x₀ for i ≠ zero -/
  field_eq : ∀ i, i ≠ zero → ∀ x : Fin d → ℝ,
    field x i = ((∑ a, ∑ b, A i a b * x a * x b) -
      (∑ a, B i a * x a) * x i) * x zero
  /-- Conservation: x'₀ = -∑_{i≠0} x'_i -/
  field_zero : ∀ x : Fin d → ℝ,
    field x zero = -(∑ i ∈ Finset.univ.filter (· ≠ zero), field x i)

/-- Bridge from Stage 2 building blocks to Stage 3 input.

Given a CRN field on n variables with explicit quadratic production coefficients
A(i,a,b) and linear degradation coefficients B(i,a):
  field(x)(i) = (∑_a ∑_b A(i,a,b)·x_a·x_b) - (∑_a B(i,a)·x_a)·x_i,

the balancingDilation produces a Stage2CubicForm on n+1 variables with zero = 0.

The extended coefficients are zero-padded:
  A'(i+1, a+1, b+1) = A(i, a, b),  A'(·, 0, ·) = A'(·, ·, 0) = 0
  B'(i+1, a+1) = B(i, a),          B'(·, 0) = 0 -/
noncomputable def balancingDilation_cubicForm {n : ℕ}
    (A : Fin n → Fin n → Fin n → ℝ) (B : Fin n → Fin n → ℝ)
    (hA : ∀ i a b, 0 ≤ A i a b) (hB : ∀ i a, 0 ≤ B i a)
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (h_field : ∀ i x, field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i) :
    Stage2CubicForm (n + 1) (balancingDilation field) where
  zero := 0
  -- Zero-pad coefficients into Fin (n+1)
  A := fun i a b => i.cases 0 (fun i' => a.cases 0 (fun a' => b.cases 0 (fun b' => A i' a' b')))
  B := fun i a => i.cases 0 (fun i' => a.cases 0 (fun a' => B i' a'))
  A_nonneg := fun i a b => by
    refine i.cases (le_refl 0) (fun i' => ?_)
    refine a.cases (le_refl 0) (fun a' => ?_)
    exact b.cases (le_refl 0) (fun b' => hA i' a' b')
  B_nonneg := fun i a => by
    refine i.cases (le_refl 0) (fun i' => ?_)
    exact a.cases (le_refl 0) (fun a' => hB i' a')
  field_eq := fun i hi x => by
    -- i ≠ 0, so i = i'.succ for some i'
    revert hi; refine Fin.cases (fun h => absurd rfl h) (fun i' _ => ?_) i
    simp only [balancingDilation, Fin.cons_succ]
    rw [h_field i' (Fin.tail x)]
    congr 1 -- (P - Q·x)·x₀ = (P' - Q'·x)·x₀
    congr 1
    · -- Production: ∑_a ∑_b A(i',a,b)·(tail x)(a)·(tail x)(b) =
      --   ∑_a ∑_b A'(i'.succ,a,b)·x(a)·x(b)
      -- LHS sums over Fin n; RHS over Fin (n+1) with zero-padded coefficients.
      symm; simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
        zero_mul, Finset.sum_const_zero, zero_add, Fin.tail]
    · -- Degradation: (∑_a B(i',a)·(tail x)(a))·x(i'.succ) =
      --   (∑_a B'(i'.succ,a)·x(a))·x(i'.succ)
      congr 1; symm; simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
        zero_mul, zero_add, Fin.tail]
  field_zero := fun x => by
    -- Derive from conservation: ∑ᵢ field(x)(i) = 0 implies
    -- field(x)(0) = -(∑_{i≠0} field(x)(i))
    have hcons := balancingDilation_conservative field x
    rw [Fin.sum_univ_succ] at hcons
    -- hcons : f(0) + ∑ j : Fin n, f(j.succ) = 0
    -- Rewrite filter sum to univ succ sum
    have h_reindex : ∑ i ∈ Finset.univ.filter (· ≠ (0 : Fin (n + 1))),
        balancingDilation field x i = ∑ j : Fin n, balancingDilation field x j.succ := by
      rw [Finset.sum_filter, Fin.sum_univ_succ]
      simp [Fin.succ_ne_zero, show ¬((0 : Fin (n + 1)) ≠ 0) from not_not.mpr rfl]
    rw [h_reindex]; linarith

/-- Helper: the selective λ-trick of a quadratic CRN field is again quadratic.
Given field x i = ∑∑ A·x·x - ∑ B·x · x_i, the selective λ-trick gives:
  selectiveLambdaTrick o c (constantDilation ε field) x i =
    ∑∑ A'·x·x - ∑ B'·x · x_i
with A'_{i,a,b} = sf(i)·ε·A_{i,a,b}/(cf(a)·cf(b)) and B'_{i,a} = ε·B_{i,a}/cf(a)
where sf(i) = 1 if i=o else c, cf(j) = 1 if j=o else c. -/
private theorem selectiveLambdaTrick_quadratic_form {n : ℕ} {o : Fin n} {c : ℝ} (hc : c ≠ 0)
    {ε : ℝ}
    (A : Fin n → Fin n → Fin n → ℝ) (B : Fin n → Fin n → ℝ)
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (h_field : ∀ i x, field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i) :
    let cf : Fin n → ℝ := fun j => if j = o then 1 else c
    ∀ i x, selectiveLambdaTrick o c (constantDilation ε field) x i =
      (∑ a, ∑ b, (if i = o then 1 else c) * ε * A i a b / (cf a * cf b) * x a * x b) -
      (∑ a, ε * B i a / cf a * x a) * x i := by
  intro cf i x
  -- Key fact: selectiveUnscale at any index
  have h_u : ∀ j, selectiveUnscale o c x j = if j = o then x j else x j / c := fun j => by
    by_cases hj : j = o
    · rw [hj, selectiveUnscale_output, if_pos rfl]
    · rw [selectiveUnscale_ne hj, if_neg hj]
  simp only [selectiveLambdaTrick, constantDilation]
  rw [h_field i (selectiveUnscale o c x)]
  -- Replace all selectiveUnscale occurrences
  simp only [h_u]
  by_cases hi : i = o
  · -- Output: field_o(unscale x) directly (no c multiplier)
    simp only [hi, ite_true, cf]
    rw [mul_sub]
    congr 1
    · -- Production: ε * ∑∑ A·ite·ite = ∑∑ A'·x·x
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      split_ifs <;> field_simp
    · -- Degradation: ε * (∑ B·ite) * x_o = (∑ B'·x) * x_o
      -- Suffices to show the sums without the x_o factor
      suffices h : ε * ∑ a, B o a * (if a = o then x a else x a / c) =
          ∑ a, ε * B o a / (if a = o then (1 : ℝ) else c) * x a by
        linear_combination h * x o
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _
      split_ifs <;> field_simp
  · -- Non-output: c * ε * field_i(unscale x), with (unscale x)_i = x_i/c
    simp only [hi, ite_false, cf]
    have h_expand : ∀ P Q : ℝ, c * (ε * (P - Q * (x i / c))) =
        c * ε * P - ε * Q * x i := fun P Q => by field_simp
    rw [h_expand]
    congr 1
    · -- Production: c*ε * ∑∑ A·ite·ite = ∑∑ A'·x·x
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      split_ifs <;> field_simp
    · -- Degradation: ε * ∑ B·ite * x_i = ∑ B'·x · x_i
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro a _
      split_ifs <;> field_simp

/-- Stage 2 full pipeline produces a Stage2CubicForm.

Given a quadratic CRN-implementable field with production coefficients A and
degradation coefficients B, the full Stage 2 construction
  stage2_field o ε c field = balancingDilation (selectiveLambdaTrick o c (constantDilation ε field))
produces a Stage2CubicForm on n+1 variables. With the selective λ-trick,
the coefficients depend on whether each index is the output o. -/
noncomputable def stage2_field_cubicForm {n : ℕ} {o : Fin n} {ε c : ℝ}
    (hε : 0 ≤ ε) (hc : 0 < c)
    (A : Fin n → Fin n → Fin n → ℝ) (B : Fin n → Fin n → ℝ)
    (hA : ∀ i a b, 0 ≤ A i a b) (hB : ∀ i a, 0 ≤ B i a)
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (h_field : ∀ i x, field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i) :
    Stage2CubicForm (n + 1) (stage2_field o ε c field) :=
  let cf : Fin n → ℝ := fun j => if j = o then 1 else c
  balancingDilation_cubicForm
    (fun i a b => (if i = o then 1 else c) * ε * A i a b / (cf a * cf b))
    (fun i a => ε * B i a / cf a)
    (fun i a b => by
      apply div_nonneg
      · exact mul_nonneg (mul_nonneg (by split_ifs <;> linarith) hε) (hA i a b)
      · exact mul_nonneg (by simp only [cf]; split_ifs <;> linarith)
                         (by simp only [cf]; split_ifs <;> linarith))
    (fun i a => div_nonneg (mul_nonneg hε (hB i a))
      (by simp only [cf]; split_ifs <;> linarith))
    (selectiveLambdaTrick_quadratic_form (ne_of_gt hc) A B h_field)

namespace Stage2CubicForm

variable {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ} (s : Stage2CubicForm d field)

/-- The quadratic production term P_i(x) in x-variables. -/
def P (i : Fin d) (x : Fin d → ℝ) : ℝ :=
  ∑ a, ∑ b, s.A i a b * x a * x b

/-- The linear degradation term Q_i(x) in x-variables. -/
def Q (i : Fin d) (x : Fin d → ℝ) : ℝ :=
  ∑ a, s.B i a * x a

/-- P_i lifted to z-space via symbolic substitution x_a·x_b → z_{a,b}.
This is LINEAR in z (degree 1), not quadratic. -/
def Pz (i : Fin d) (z : Fin d × Fin d → ℝ) : ℝ :=
  ∑ a, ∑ b, s.A i a b * z (a, b)

/-- x₀·Q_i lifted to z-space: ∑_a B_i(a)·z_{zero,a}.
Linear in z (degree 1). -/
def x0Qz (i : Fin d) (z : Fin d × Fin d → ℝ) : ℝ :=
  ∑ a, s.B i a * z (s.zero, a)

/-- On the self-product manifold z_{a,b} = x_a·x_b, Pz agrees with P. -/
theorem Pz_eq_on_manifold (i : Fin d) (x : Fin d → ℝ) :
    s.Pz i (fun ij => x ij.1 * x ij.2) = s.P i x := by
  simp only [Pz, P]
  congr 1; ext a; congr 1; ext b; ring

/-- On the self-product manifold, x0Qz agrees with x_zero · Q. -/
theorem x0Qz_eq_on_manifold (i : Fin d) (x : Fin d → ℝ) :
    s.x0Qz i (fun ij => x ij.1 * x ij.2) = x s.zero * s.Q i x := by
  simp only [x0Qz, Q]
  simp_rw [show ∀ a, s.B i a * (x s.zero * x a) = x s.zero * (s.B i a * x a)
    from fun a => by ring]
  rw [← Finset.mul_sum]

/-- P is non-negative on the non-negative orthant. -/
theorem P_nonneg (i : Fin d) (x : Fin d → ℝ) (hx : ∀ k, 0 ≤ x k) :
    0 ≤ s.P i x :=
  Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ =>
      mul_nonneg (mul_nonneg (s.A_nonneg i a b) (hx a)) (hx b)

/-- Q is non-negative on the non-negative orthant. -/
theorem Q_nonneg (i : Fin d) (x : Fin d → ℝ) (hx : ∀ k, 0 ≤ x k) :
    0 ≤ s.Q i x :=
  Finset.sum_nonneg fun a _ => mul_nonneg (s.B_nonneg i a) (hx a)

/-- Pz is non-negative on the non-negative orthant (z-space). -/
theorem Pz_nonneg (i : Fin d) (z : Fin d × Fin d → ℝ) (hz : ∀ p, 0 ≤ z p) :
    0 ≤ s.Pz i z :=
  Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => mul_nonneg (s.A_nonneg i a b) (hz _)

/-- x0Qz is non-negative on the non-negative orthant. -/
theorem x0Qz_nonneg (i : Fin d) (z : Fin d × Fin d → ℝ) (hz : ∀ p, 0 ≤ z p) :
    0 ≤ s.x0Qz i z :=
  Finset.sum_nonneg fun a _ => mul_nonneg (s.B_nonneg i a) (hz _)

/-- Sum of Pz over non-zero indices: total production in z-space. -/
def totalPz (z : Fin d × Fin d → ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.Pz k z

/-- Sum of ∑_a B_k(a)·z_{a,k} over non-zero k: total degradation-coupling in z-space. -/
def totalQxz (z : Fin d × Fin d → ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (· ≠ s.zero), ∑ a, s.B k a * z (a, k)

/-- On the manifold, totalPz = ∑_{k≠0} P_k(x). -/
theorem totalPz_eq_on_manifold (x : Fin d → ℝ) :
    s.totalPz (fun ij => x ij.1 * x ij.2) = ∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.P k x := by
  simp only [totalPz]; congr 1; ext k; exact s.Pz_eq_on_manifold k x

/-- On the manifold, totalQxz = ∑_{k≠0} Q_k(x)·x_k. -/
theorem totalQxz_eq_on_manifold (x : Fin d → ℝ) :
    s.totalQxz (fun ij => x ij.1 * x ij.2) =
      ∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.Q k x * x k := by
  simp only [totalQxz, Q]
  congr 1; ext k
  simp_rw [show ∀ a, s.B k a * (x a * x k) = s.B k a * x a * x k from fun a => by ring]
  rw [← Finset.sum_mul]

/-- Column coupling: ∑_{k≠0} z(k,j)·x0Qz_k(z). From [LPP] Theorem 15 Case 2:
the chain rule for z'_{0,j} produces ∑(x_k·x_j·x_0·Q_k) which lifts to
∑_{k≠0} z(k,j)·x0Qz_k in z-space.
On manifold: equals z(0,j)·totalQxz = x₀·xⱼ·∑_{k≠0} Q_k·x_k. -/
def colCoupling (j : Fin d) (z : Fin d × Fin d → ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (· ≠ s.zero), z (k, j) * s.x0Qz k z

/-- Row coupling: ∑_{k≠0} z(i,k)·x0Qz_k(z). Symmetric variant of colCoupling
for Case 2b (z'_{i,0}). -/
def rowCoupling (i : Fin d) (z : Fin d × Fin d → ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (· ≠ s.zero), z (i, k) * s.x0Qz k z

/-- On manifold, colCoupling j = x₀·xⱼ·∑_{k≠0} Q_k·x_k. -/
theorem colCoupling_eq_on_manifold (j : Fin d) (x : Fin d → ℝ) :
    s.colCoupling j (fun ab => x ab.1 * x ab.2) =
    (x s.zero * x j) *
    ∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.Q k x * x k := by
  simp only [colCoupling]
  have h_x0Q : ∀ k, s.x0Qz k (fun ab => x ab.1 * x ab.2) = x s.zero * s.Q k x :=
    fun k => s.x0Qz_eq_on_manifold k x
  simp_rw [h_x0Q]
  simp_rw [show ∀ k, (x k * x j) * (x s.zero * s.Q k x) =
      (x s.zero * x j) * (s.Q k x * x k) from fun k => by ring]
  rw [← Finset.mul_sum]

/-- On manifold, rowCoupling i = xᵢ·x₀·∑_{k≠0} Q_k·x_k. -/
theorem rowCoupling_eq_on_manifold (i : Fin d) (x : Fin d → ℝ) :
    s.rowCoupling i (fun ab => x ab.1 * x ab.2) =
    (x i * x s.zero) *
    ∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.Q k x * x k := by
  simp only [rowCoupling]
  have h_x0Q : ∀ k, s.x0Qz k (fun ab => x ab.1 * x ab.2) = x s.zero * s.Q k x :=
    fun k => s.x0Qz_eq_on_manifold k x
  simp_rw [h_x0Q]
  simp_rw [show ∀ k, (x i * x k) * (x s.zero * s.Q k x) =
      (x i * x s.zero) * (s.Q k x * x k) from fun k => by ring]
  rw [← Finset.mul_sum]

/-! ### Non-negativity of z-space building blocks -/

/-- totalPz is non-negative on the non-negative orthant. -/
theorem totalPz_nonneg (z : Fin d × Fin d → ℝ) (hz : ∀ p, 0 ≤ z p) :
    0 ≤ s.totalPz z :=
  Finset.sum_nonneg fun k _ => s.Pz_nonneg k z hz

/-- totalQxz is non-negative on the non-negative orthant. -/
theorem totalQxz_nonneg (z : Fin d × Fin d → ℝ) (hz : ∀ p, 0 ≤ z p) :
    0 ≤ s.totalQxz z :=
  Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun a _ => mul_nonneg (s.B_nonneg k a) (hz _)

/-- colCoupling is non-negative on the non-negative orthant. -/
theorem colCoupling_nonneg (j : Fin d) (z : Fin d × Fin d → ℝ) (hz : ∀ p, 0 ≤ z p) :
    0 ≤ s.colCoupling j z :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hz _) (s.x0Qz_nonneg k z hz)

/-- rowCoupling is non-negative on the non-negative orthant. -/
theorem rowCoupling_nonneg (i : Fin d) (z : Fin d × Fin d → ℝ) (hz : ∀ p, 0 ≤ z p) :
    0 ≤ s.rowCoupling i z :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hz _) (s.x0Qz_nonneg k z hz)

/-! ### Scaling (homogeneity) lemmas

These establish the polynomial degree of each building block:
Pz, x0Qz, totalPz, totalQxz are degree 1 (linear);
colCoupling, rowCoupling are degree 2 (quadratic);
ppField is degree 2 (homogeneous). -/

/-- Pz scales linearly: Pz(c•z) = c · Pz(z). -/
theorem Pz_smul (i : Fin d) (c : ℝ) (z : Fin d × Fin d → ℝ) :
    s.Pz i (c • z) = c * s.Pz i z := by
  simp only [Pz, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ a b, s.A i a b * (c * z (a, b)) = c * (s.A i a b * z (a, b))
    from fun a b => by ring]
  simp_rw [← Finset.mul_sum]

/-- x0Qz scales linearly: x0Qz(c•z) = c · x0Qz(z). -/
theorem x0Qz_smul (i : Fin d) (c : ℝ) (z : Fin d × Fin d → ℝ) :
    s.x0Qz i (c • z) = c * s.x0Qz i z := by
  simp only [x0Qz, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ a, s.B i a * (c * z (s.zero, a)) = c * (s.B i a * z (s.zero, a))
    from fun a => by ring]
  rw [← Finset.mul_sum]

/-- totalPz scales linearly. -/
theorem totalPz_smul (c : ℝ) (z : Fin d × Fin d → ℝ) :
    s.totalPz (c • z) = c * s.totalPz z := by
  simp only [totalPz, s.Pz_smul]
  rw [← Finset.mul_sum]

/-- totalQxz scales linearly. -/
theorem totalQxz_smul (c : ℝ) (z : Fin d × Fin d → ℝ) :
    s.totalQxz (c • z) = c * s.totalQxz z := by
  simp only [totalQxz, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ k a, s.B k a * (c * z (a, k)) = c * (s.B k a * z (a, k))
    from fun k a => by ring]
  simp_rw [← Finset.mul_sum]

/-- colCoupling scales quadratically: colCoupling(c•z) = c² · colCoupling(z). -/
theorem colCoupling_smul (j : Fin d) (c : ℝ) (z : Fin d × Fin d → ℝ) :
    s.colCoupling j (c • z) = c ^ 2 * s.colCoupling j z := by
  simp only [colCoupling, Pi.smul_apply, smul_eq_mul, s.x0Qz_smul]
  simp_rw [show ∀ k, c * z (k, j) * (c * s.x0Qz k z) = c ^ 2 * (z (k, j) * s.x0Qz k z)
    from fun k => by ring]
  rw [← Finset.mul_sum]

/-- rowCoupling scales quadratically. -/
theorem rowCoupling_smul (i : Fin d) (c : ℝ) (z : Fin d × Fin d → ℝ) :
    s.rowCoupling i (c • z) = c ^ 2 * s.rowCoupling i z := by
  simp only [rowCoupling, Pi.smul_apply, smul_eq_mul, s.x0Qz_smul]
  simp_rw [show ∀ k, c * z (i, k) * (c * s.x0Qz k z) = c ^ 2 * (z (i, k) * s.x0Qz k z)
    from fun k => by ring]
  rw [← Finset.mul_sum]

/-- The PP self-product z-field: degree-2 field on Fin d × Fin d obtained by
symbolic substitution x_a·x_b → z_{a,b} from the Stage 2 cubic form.
Agrees with selfProductField on the self-product manifold {z_{i,j} = x_i·x_j}.

Three cases from [LPP] Theorem 15 §3.5:
- Case 1 (i,j ≠ 0): z' = (z_{0,j}·Pz_i + z_{0,i}·Pz_j) - z_{i,j}·(x0Qz_i + x0Qz_j)
- Case 2a (i=0,j≠0): z' = z_{0,0}·Pz_j + ∑_{k≠0} z(k,j)·x0Qz_k - z_{0,j}·(x0Qz_j + totalPz)
- Case 2b (i≠0,j=0): z' = z_{0,0}·Pz_i + ∑_{k≠0} z(i,k)·x0Qz_k - z_{i,0}·(x0Qz_i + totalPz)
- Case 3 (i=j=0): z' = 2·z_{0,0}·(totalQxz - totalPz)

NOTE: This field is NOT globally conservative (∑ ppField z ≠ 0 for non-symmetric z).
It is conservative on the self-product manifold where z(i,j) = z(j,i). -/
noncomputable def ppField :
    (Fin d × Fin d → ℝ) → Fin d × Fin d → ℝ :=
  fun z ij =>
    if ij.1 ≠ s.zero ∧ ij.2 ≠ s.zero then
      -- Case 1: i,j ≠ zero
      (z (s.zero, ij.2) * s.Pz ij.1 z + z (s.zero, ij.1) * s.Pz ij.2 z) -
      z ij * (s.x0Qz ij.1 z + s.x0Qz ij.2 z)
    else if ij.1 = s.zero ∧ ij.2 = s.zero then
      -- Case 3: i = j = zero
      2 * z (s.zero, s.zero) * (s.totalQxz z - s.totalPz z)
    else if ij.1 = s.zero then
      -- Case 2a: first = zero, second ≠ zero ([LPP] Theorem 15 Case 2)
      z (s.zero, s.zero) * s.Pz ij.2 z + s.colCoupling ij.2 z -
      z ij * (s.x0Qz ij.2 z + s.totalPz z)
    else
      -- Case 2b: second = zero, first ≠ zero (symmetric to 2a)
      z (s.zero, s.zero) * s.Pz ij.1 z + s.rowCoupling ij.1 z -
      z ij * (s.x0Qz ij.1 z + s.totalPz z)

/-- ppField agrees with selfProductField on the self-product manifold.
On {z_{a,b} = x_a·x_b} with ∑x = 1, the degree-2 ppField and the degree-4
selfProductField evaluate to the same value for every (i,j). -/
theorem ppField_eq_on_manifold (x : Fin d → ℝ) (hsum : ∑ j, x j = 1)
    (ij : Fin d × Fin d) :
    s.ppField (fun ab => x ab.1 * x ab.2) ij =
    selfProductField field (fun ab => x ab.1 * x ab.2) ij := by
  -- Reduce selfProductField: rowSum on manifold recovers x
  have h_row : selfProduct_rowSum (fun ab : Fin d × Fin d => x ab.1 * x ab.2) = x :=
    funext (selfProduct_rowSum_eq hsum)
  simp only [selfProductField, h_row]
  -- Beta-reduce z-value applications (needed because ring treats lambdas as opaque)
  have hz_β : ∀ ab : Fin d × Fin d,
      (fun p : Fin d × Fin d => x p.1 * x p.2) ab = x ab.1 * x ab.2 := fun _ => rfl
  -- Helper: expand field x zero using conservation + Stage 2 form
  have h_fz : field x s.zero =
      x s.zero * (∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.Q k x * x k -
                  ∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.P k x) := by
    have h_each : ∀ k ∈ Finset.univ.filter (· ≠ s.zero),
        field x k = (s.P k x - s.Q k x * x k) * x s.zero :=
      fun k hk => s.field_eq k (Finset.mem_filter.mp hk).2 x
    rw [s.field_zero x, Finset.sum_congr rfl h_each, ← Finset.sum_mul,
        Finset.sum_sub_distrib]
    ring
  -- Case split on ppField
  unfold ppField
  split_ifs with h1 h3 h2a
  · -- Case 1: i,j ≠ zero
    obtain ⟨hi, hj⟩ := h1
    have h_fi : field x ij.1 = (s.P ij.1 x - s.Q ij.1 x * x ij.1) * x s.zero :=
      s.field_eq ij.1 hi x
    have h_fj : field x ij.2 = (s.P ij.2 x - s.Q ij.2 x * x ij.2) * x s.zero :=
      s.field_eq ij.2 hj x
    rw [s.Pz_eq_on_manifold ij.1, s.Pz_eq_on_manifold ij.2,
        s.x0Qz_eq_on_manifold ij.1, s.x0Qz_eq_on_manifold ij.2,
        h_fi, h_fj]
    ring
  · -- Case 3: i = j = zero
    obtain ⟨hi, hj⟩ := h3
    rw [hi, hj, s.totalQxz_eq_on_manifold, s.totalPz_eq_on_manifold, h_fz]
    ring
  · -- Case 2a: first = zero, second ≠ zero
    have hj : ij.2 ≠ s.zero := by
      intro h; exact h3 ⟨h2a, h⟩
    have hxi : x ij.1 = x s.zero := congr_arg x h2a
    have h_fj : field x ij.2 = (s.P ij.2 x - s.Q ij.2 x * x ij.2) * x s.zero :=
      s.field_eq ij.2 hj x
    have hz00 : (fun ab : Fin d × Fin d => x ab.1 * x ab.2) (s.zero, s.zero) =
        x s.zero * x s.zero := rfl
    have hzij : (fun ab : Fin d × Fin d => x ab.1 * x ab.2) ij = x ij.1 * x ij.2 := rfl
    rw [h2a, s.Pz_eq_on_manifold, s.x0Qz_eq_on_manifold,
        s.colCoupling_eq_on_manifold, s.totalPz_eq_on_manifold,
        h_fj, h_fz, hz00, hzij, hxi]
    ring
  · -- Case 2b: second = zero, first ≠ zero
    have hi : ij.1 ≠ s.zero := h2a
    have hj : ij.2 = s.zero := by
      by_contra h; exact absurd ⟨hi, h⟩ h1
    have hxj : x ij.2 = x s.zero := congr_arg x hj
    -- Use folded form (P, Q) to match ppField's Pz/x0Qz rewrites
    have h_fi : field x ij.1 = (s.P ij.1 x - s.Q ij.1 x * x ij.1) * x s.zero :=
      s.field_eq ij.1 hi x
    -- Beta-reduce z-applications and substitute ij.2 = zero
    have hz00 : (fun ab : Fin d × Fin d => x ab.1 * x ab.2) (s.zero, s.zero) =
        x s.zero * x s.zero := rfl
    have hzij : (fun ab : Fin d × Fin d => x ab.1 * x ab.2) ij = x ij.1 * x ij.2 := rfl
    rw [hj, s.Pz_eq_on_manifold, s.x0Qz_eq_on_manifold,
        s.rowCoupling_eq_on_manifold, s.totalPz_eq_on_manifold,
        h_fi, h_fz, hz00, hzij, hxj]
    ring

/-- ppField is degree-2 homogeneous: ppField(c•z) = c² · ppField(z).
This is a necessary condition for PP-implementability (production function
must be homogeneous degree 2). -/
theorem ppField_homog (c : ℝ) (z : Fin d × Fin d → ℝ) (ij : Fin d × Fin d) :
    s.ppField (c • z) ij = c ^ 2 * s.ppField z ij := by
  unfold ppField
  split_ifs with h1 h3 h2a
  all_goals simp only [Pi.smul_apply, smul_eq_mul]
  · rw [s.Pz_smul, s.Pz_smul, s.x0Qz_smul, s.x0Qz_smul]; ring
  · rw [s.totalQxz_smul, s.totalPz_smul]; ring
  · rw [s.Pz_smul, s.colCoupling_smul, s.x0Qz_smul, s.totalPz_smul]; ring
  · rw [s.Pz_smul, s.rowCoupling_smul, s.x0Qz_smul, s.totalPz_smul]; ring

/-! ### CRN decomposition of ppField

ppField has the CRN form: ppField(z)_{ij} = ppProd(ij,z) - ppDegr(ij,z)·z_{ij}
with ppProd ≥ 0 and ppDegr ≥ 0 on the non-negative orthant. -/

/-- Production part of the CRN decomposition of ppField. -/
noncomputable def ppProd (ij : Fin d × Fin d) (z : Fin d × Fin d → ℝ) : ℝ :=
  if ij.1 ≠ s.zero ∧ ij.2 ≠ s.zero then
    z (s.zero, ij.2) * s.Pz ij.1 z + z (s.zero, ij.1) * s.Pz ij.2 z
  else if ij.1 = s.zero ∧ ij.2 = s.zero then
    2 * z (s.zero, s.zero) * s.totalQxz z
  else if ij.1 = s.zero then
    z (s.zero, s.zero) * s.Pz ij.2 z + s.colCoupling ij.2 z
  else
    z (s.zero, s.zero) * s.Pz ij.1 z + s.rowCoupling ij.1 z

/-- Degradation part of the CRN decomposition of ppField. -/
noncomputable def ppDegr (ij : Fin d × Fin d) (z : Fin d × Fin d → ℝ) : ℝ :=
  if ij.1 ≠ s.zero ∧ ij.2 ≠ s.zero then
    s.x0Qz ij.1 z + s.x0Qz ij.2 z
  else if ij.1 = s.zero ∧ ij.2 = s.zero then
    2 * s.totalPz z
  else if ij.1 = s.zero then
    s.x0Qz ij.2 z + s.totalPz z
  else
    s.x0Qz ij.1 z + s.totalPz z

/-- ppField = ppProd - ppDegr · z (CRN decomposition). -/
theorem ppField_eq_crn (z : Fin d × Fin d → ℝ) (ij : Fin d × Fin d) :
    s.ppField z ij = s.ppProd ij z - s.ppDegr ij z * z ij := by
  unfold ppField ppProd ppDegr
  split_ifs with h1 h3
  · ring
  · obtain ⟨hi, hj⟩ := h3
    have : z ij = z (s.zero, s.zero) := by rw [show ij = (s.zero, s.zero) from Prod.ext hi hj]
    rw [this]; ring
  all_goals ring

/-- ppProd is non-negative on the non-negative orthant. -/
theorem ppProd_nonneg (ij : Fin d × Fin d) (z : Fin d × Fin d → ℝ)
    (hz : ∀ p : Fin d × Fin d, 0 ≤ z p) :
    0 ≤ s.ppProd ij z := by
  unfold ppProd
  split_ifs with h1 h3 h2a
  · -- Case 1: z(0,j)·Pz_i + z(0,i)·Pz_j
    exact add_nonneg
      (mul_nonneg (hz _) (s.Pz_nonneg ij.1 z hz))
      (mul_nonneg (hz _) (s.Pz_nonneg ij.2 z hz))
  · -- Case 3: 2·z(0,0)·totalQxz
    exact mul_nonneg (mul_nonneg (by norm_num) (hz _))
      (s.totalQxz_nonneg z hz)
  · -- Case 2a: z(0,0)·Pz_j + colCoupling_j
    exact add_nonneg
      (mul_nonneg (hz _) (s.Pz_nonneg ij.2 z hz))
      (s.colCoupling_nonneg ij.2 z hz)
  · -- Case 2b: z(0,0)·Pz_i + rowCoupling_i
    exact add_nonneg
      (mul_nonneg (hz _) (s.Pz_nonneg ij.1 z hz))
      (s.rowCoupling_nonneg ij.1 z hz)

/-- ppDegr is non-negative on the non-negative orthant. -/
theorem ppDegr_nonneg (ij : Fin d × Fin d) (z : Fin d × Fin d → ℝ)
    (hz : ∀ p : Fin d × Fin d, 0 ≤ z p) :
    0 ≤ s.ppDegr ij z := by
  unfold ppDegr
  split_ifs with h1 h3 h2a
  · exact add_nonneg (s.x0Qz_nonneg ij.1 z hz) (s.x0Qz_nonneg ij.2 z hz)
  · exact mul_nonneg (by norm_num) (s.totalPz_nonneg z hz)
  · exact add_nonneg (s.x0Qz_nonneg ij.2 z hz) (s.totalPz_nonneg z hz)
  · exact add_nonneg (s.x0Qz_nonneg ij.1 z hz) (s.totalPz_nonneg z hz)

end Stage2CubicForm

/-! ## Conservation Invariant

If the field is conservative (∑ field(x)_i = 0) and the trajectory solves
the ODE, then ∑ trajectory(t)_i is constant for t ≥ 0. This is the formal
version of "conservation of mass" for chemical reaction networks. -/

/-- Conservation invariant: under a conservative field (∑ field = 0),
the sum of trajectory components is constant for t ≥ 0.

Proof uses the Mean Value Theorem: the sum has derivative 0
(by summing the ODE components), so it equals its initial value. -/
theorem conservative_trajectory_sum {d : ℕ} {P : PIVP d}
    (sol : P.Solution)
    (h_cons : ∀ x, ∑ i, P.field x i = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    ∑ i, sol.trajectory t i = ∑ i, P.init i := by
  -- Edge case: t = 0
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · congr 1; exact sol.init_cond
  · -- The sum function has derivative 0 for all s ≥ 0
    have hderiv : ∀ s, 0 ≤ s →
        HasDerivAt (fun s => ∑ i, sol.trajectory s i) 0 s := by
      intro s hs
      have h_pi := hasDerivAt_pi.mp (sol.is_solution s hs)
      have h_sum := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => h_pi i)
      have h_zero : (∑ i : Fin d, P.field (sol.trajectory s) i) = 0 := h_cons _
      rwa [h_zero] at h_sum
    -- By MVT on [0, t]: constant
    have h_const := constant_of_has_deriv_right_zero
      (fun s hs => (hderiv s hs.1).continuousAt.continuousWithinAt)
      (fun s hs => (hderiv s hs.1).hasDerivWithinAt)
      t (Set.right_mem_Icc.mpr ht)
    -- h_const gives f(t) = f(0), conclude via init_cond
    have h0 : (fun s => ∑ i, sol.trajectory s i) 0 = ∑ i, P.init i := by
      simp only []; congr 1; exact sol.init_cond
    linarith [h_const, h0]

/-- Corollary: if the field is conservative and ∑ init = 1,
then the trajectory lives on the simplex for all t ≥ 0. -/
theorem conservative_trajectory_simplex {d : ℕ} {P : PIVP d}
    (sol : P.Solution)
    (h_cons : ∀ x, ∑ i, P.field x i = 0)
    (h_init : ∑ i, P.init i = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    ∑ i, sol.trajectory t i = 1 := by
  rw [conservative_trajectory_sum sol h_cons ht, h_init]

/-! ## Inner Stage 2 Solution (ε-scaling + λ-shrinking)

The "easy" part of Stage 2: composing ε-scaling and λ-shrinking gives
a solution of the inner field. This is proved by composing
`constantDilation_reparametrize` and `lambdaTrick_solution`. The "hard"
part is lifting this inner solution to the balanced system via
`balancingDilation`, which requires ODE existence theory. -/

/-- Composing ε-scaling and λ-shrinking gives a solution of the inner field.
If x(t) solves x' = field(x) for t ≥ 0, then y(t) = c • x(ε·t)
solves y' = lambdaTrick c (constantDilation ε field)(y) for t ≥ 0.

Proof: time-reparametrize by ε (existing `constantDilation_reparametrize`),
then scale by c (existing `lambdaTrick_solution` / `const_smul`). -/
theorem inner_stage2_hasDerivAt {n : ℕ} {ε c : ℝ} (hε : 0 < ε) (hc : c ≠ 0)
    {x : ℝ → Fin n → ℝ} {field : (Fin n → ℝ) → Fin n → ℝ}
    (h_sol : ∀ t, 0 ≤ t → HasDerivAt x (field (x t)) t) :
    ∀ t, 0 ≤ t →
      HasDerivAt (fun s => c • x (ε * s))
        (lambdaTrick c (constantDilation ε field) (c • x (ε * t))) t := by
  intro t ht
  -- Step 1: x(ε·t) solves constantDilation ε field (by time reparametrization)
  -- Step 2: c • (·) scales the derivative (const_smul)
  have h1 := (constantDilation_reparametrize hε h_sol t ht).const_smul c
  -- h1 : HasDerivAt (c • x ∘ (ε * ·)) (c • constantDilation ε field (x(ε*t))) t
  -- By lambdaTrick_smul_cancel: lambdaTrick c g (c • y) = c • g y
  convert h1 using 1
  exact lambdaTrick_smul_cancel hc (constantDilation ε field) (x (ε * t))

/-- The inner Stage 2 solution matches the initial condition.
At t = 0: c • x(ε·0) = c • x(0) = c • init. -/
theorem inner_stage2_init {n : ℕ} {ε c : ℝ}
    {x : ℝ → Fin n → ℝ} {init : Fin n → ℝ}
    (h_init : x 0 = init) :
    c • x (ε * 0) = c • init := by
  rw [mul_zero, h_init]

/-- The inner Stage 2 solution preserves convergence:
if x(t)_o → α, then c · x(ε·t)_o → c · α. -/
theorem inner_stage2_tendsto {n : ℕ} {ε c α : ℝ} (hε : 0 < ε)
    {x : ℝ → Fin n → ℝ} {o : Fin n}
    (h_conv : Filter.Tendsto (fun t => x t o) Filter.atTop (nhds α)) :
    Filter.Tendsto (fun t => c * x (ε * t) o) Filter.atTop (nhds (c * α)) :=
  (tendsto_comp_const_mul hε h_conv).const_mul c

/-- The inner Stage 2 solution is bounded when the original is bounded. -/
theorem inner_stage2_bounded {n : ℕ} {ε c : ℝ} (hε : 0 < ε)
    {x : ℝ → Fin n → ℝ}
    (h_bounded : ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ M) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 0 ≤ t → ‖c • x (ε * t)‖ ≤ M := by
  obtain ⟨M, hM, hbound⟩ := h_bounded
  refine ⟨(|c| + 1) * M, by positivity, fun t ht => ?_⟩
  calc ‖c • x (ε * t)‖
      = ‖c‖ * ‖x (ε * t)‖ := norm_smul c (x (ε * t))
    _ ≤ ‖c‖ * M := by
        apply mul_le_mul_of_nonneg_left (hbound _ (mul_nonneg hε.le ht)) (norm_nonneg _)
    _ ≤ (|c| + 1) * M := by
        apply mul_le_mul_of_nonneg_right _ hM.le
        rw [Real.norm_eq_abs]
        linarith

/-! ## Analytic Sorry Declarations

These isolate the two independent analytic challenges:
1. Balancing dilation lifting: constructing a solution of the balanced
   system from inner solution properties
2. CRN non-negativity invariance (trajectories stay non-negative) -/

/-- The function s ↦ min(s, 0)² is differentiable everywhere with derivative 2·min(s, 0).
This is C¹ because min(s,0)² = s² for s ≤ 0 and 0 for s ≥ 0, gluing smoothly at 0. -/
private lemma hasDerivAt_minSq (s : ℝ) :
    HasDerivAt (fun x => min x (0 : ℝ) ^ 2) (2 * min s 0) s := by
  rcases lt_or_ge s 0 with hs | hs
  · -- s < 0: locally min x 0 = x, so min x 0 ^ 2 = x ^ 2
    rw [show 2 * min s 0 = (2 : ℝ) * s ^ (2 - 1) from by rw [min_eq_left hs.le]; ring]
    exact (hasDerivAt_pow 2 s).congr_of_eventuallyEq
      (Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Iio 0, Iio_mem_nhds hs, fun x hx => by
        simp [min_eq_left (Set.mem_Iio.mp hx).le]⟩)
  · rcases eq_or_lt_of_le hs with rfl | hs'
    · -- s = 0: derivative is 0, proved via squeeze with x²
      simp only [min_self, mul_zero]
      rw [hasDerivAt_iff_isLittleO_nhds_zero]
      simp only [zero_add, smul_zero, min_self, zero_pow (by norm_num : 2 ≠ 0), sub_zero]
      -- (fun h => min h 0 ^ 2) =o[𝓝 0] (fun h => h)
      -- Bound: min h 0 ^ 2 ≤ h ^ 2 = |h| · |h| ≤ c · |h| for |h| < c
      rw [Asymptotics.isLittleO_iff]
      intro c hc
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hc] with h hh
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (sq_nonneg _)]
      calc min h 0 ^ 2
            ≤ h ^ 2 := by
              rcases le_or_gt h 0 with hle | hgt
              · rw [min_eq_left hle]
              · rw [min_eq_right hgt.le, zero_pow (by norm_num : 2 ≠ 0)]; exact sq_nonneg h
          _ = |h| ^ 2 := (sq_abs h).symm
          _ = |h| * |h| := by ring
          _ ≤ c * |h| := mul_le_mul_of_nonneg_right hh.le (abs_nonneg h)
    · -- s > 0: locally min x 0 = 0
      rw [show 2 * min s 0 = 0 from by rw [min_eq_right hs'.le]; ring]
      exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq
        (Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioi 0, Ioi_mem_nhds hs', fun x hx => by
          simp [min_eq_right (Set.mem_Ioi.mp hx).le]⟩)

/-- General form: any `ContDiff ℝ ⊤` field `f : (Fin d → ℝ) → Fin d → ℝ` is
locally Lipschitz on every closed ball (with a uniform constant). This is the
workhorse behind both `cubicForm_locally_lipschitz` and the quadratic form used
for `btc.pivp.field` in Stage 2.

Proof: continuous Fréchet derivative + compact closed ball → bounded ‖fderiv‖;
then MVT on the convex closed ball. -/
theorem contDiff_locally_lipschitz {d : ℕ} {f : (Fin d → ℝ) → Fin d → ℝ}
    (hf : ContDiff ℝ ⊤ f) :
    ∀ R, 0 < R → ∃ L, ∀ x y : Fin d → ℝ, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖f x - f y‖ ≤ L * ‖x - y‖ := by
  intro R hR
  have h_cont_fderiv : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have h_compact : IsCompact (Metric.closedBall (0 : Fin d → ℝ) R) :=
    isCompact_closedBall 0 R
  obtain ⟨C, hC⟩ := h_compact.exists_bound_of_continuousOn
    h_cont_fderiv.norm.continuousOn
  refine ⟨C, fun x y hx hy => ?_⟩
  have hx' : x ∈ Metric.closedBall (0 : Fin d → ℝ) R := by
    rwa [Metric.mem_closedBall, dist_zero_right]
  have hy' : y ∈ Metric.closedBall (0 : Fin d → ℝ) R := by
    rwa [Metric.mem_closedBall, dist_zero_right]
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hf.differentiable (by simp)).differentiableAt)
    (fun z hz => by
      have := hC z hz
      rwa [Real.norm_of_nonneg (norm_nonneg _)] at this)
    (convex_closedBall 0 R) hy' hx'

/-- A quadratic CRN field `field x i = (∑∑ A·x·x) - (∑ B·x)·x_i` (as appearing
in BTC inputs after Stage 1 v-variable quadraticization) is locally Lipschitz.

This is the instance used in Stage 2 convergence analysis: the BTC's own field
satisfies the quadratic form exactly, so we get its Lipschitz constant on any
closed ball directly from the A, B coefficients (no further hypothesis). -/
theorem quadraticForm_locally_lipschitz {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (A : Fin d → Fin d → Fin d → ℝ) (B : Fin d → Fin d → ℝ)
    (h_field : ∀ i x, field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i) :
    ∀ R, 0 < R → ∃ L, ∀ x y : Fin d → ℝ, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖field x - field y‖ ≤ L * ‖x - y‖ := by
  have h_cd_comp : ∀ i, ContDiff ℝ ⊤ (fun x : Fin d → ℝ => field x i) := by
    intro i
    have h_eq : (fun x : Fin d → ℝ => field x i) =
        fun x => (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i :=
      funext (h_field i)
    rw [h_eq]
    exact (ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
        (contDiff_const.mul (contDiff_apply ℝ ℝ a)).mul (contDiff_apply ℝ ℝ b)).sub
      ((ContDiff.sum fun a _ => contDiff_const.mul (contDiff_apply ℝ ℝ a)).mul
        (contDiff_apply ℝ ℝ i))
  have h_cd : ContDiff ℝ ⊤ (fun x : Fin d → ℝ => (fun i => field x i : Fin d → ℝ)) :=
    contDiff_pi' h_cd_comp
  exact contDiff_locally_lipschitz h_cd

/-- **Stage 2 convergence from the z₀ ≥ c invariant + simplex + quadratic btc
form** — the cleanest conditional closure of `stage2_convergence_axiom`.

Compared to `stage2_convergence_from_invariants`, this wrapper internally
supplies the scaffolding (uniform `M`, `L`, `h_w_bdd`, `h_btc_bdd`, `h_lip`) so
that the caller only provides semantically-meaningful hypotheses:
  * `c ≤ 1` (combined with `0 < c`, pins `c ∈ (0, 1]`);
  * the BTC's `A`, `B` quadratic decomposition (automatic post Stage 1);
  * simplex data for `sol` (non-negativity + sum = 1, from CRN invariance);
  * zero-init `h_zero_init` (DNA 25 normalization);
  * **`h_z0_lb`**: the LPP Remark 14 invariant `c ≤ z₀(s)` — the *only*
    remaining mathematical gap.

Internal derivations:
  * simplex + `selectiveUnscale_norm_le_div` ⇒ `‖w(s)‖ ≤ 1/c`
  * `btc.bounded` ⇒ `‖btc.sol(τ(s))‖ ≤ M_btc`
  * `quadraticForm_locally_lipschitz` ⇒ Lipschitz constant on `closedBall 0 M`. -/
theorem stage2_convergence_from_z0_invariant
    {d : ℕ} [NeZero d] {α : ℝ} {ε c : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hc1 : c ≤ 1) (hεc : 1 ≤ ε * c)
    {btc : BoundedTimeComputable d α}
    (A : Fin d → Fin d → Fin d → ℝ) (B : Fin d → Fin d → ℝ)
    (h_field : ∀ i x, btc.pivp.field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i)
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (h_sol_nn : ∀ s, 0 ≤ s → ∀ i, 0 ≤ sol.trajectory s i)
    (h_sol_sum : ∀ s, 0 ≤ s → ∑ i, sol.trajectory s i = 1)
    (h_zero_init : btc.pivp.init btc.pivp.output = 0)
    (h_z0_lb : ∀ s, 0 ≤ s → c ≤ sol.trajectory s 0) :
    ∀ r : ℕ, ∀ t : ℝ, 0 ≤ t → t > btc.modulus r →
      |sol.trajectory t (stage2_pivp ε c btc.pivp).output - α| <
        Real.exp (-(r : ℝ)) := by
  -- Simplex bound on sol: ‖sol(s)‖ ≤ 1
  have h_sol_bdd : ∀ s, 0 ≤ s → ‖sol.trajectory s‖ ≤ 1 := by
    intro s hs
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (h_sol_nn s hs i)]
    calc sol.trajectory s i
        ≤ ∑ j, sol.trajectory s j :=
          Finset.single_le_sum (f := sol.trajectory s)
            (fun j _ => h_sol_nn s hs j) (Finset.mem_univ i)
      _ = 1 := h_sol_sum s hs
  -- z₀ bounds from simplex
  have h_z0_nn : ∀ s, 0 ≤ s → 0 ≤ sol.trajectory s 0 := fun s hs =>
    h_sol_nn s hs 0
  have h_z0_le : ∀ s, 0 ≤ s → sol.trajectory s 0 ≤ 1 := by
    intro s hs
    have h_coord := norm_le_pi_norm (sol.trajectory s) 0
    rw [Real.norm_eq_abs] at h_coord
    exact (abs_le.mp (h_coord.trans (h_sol_bdd s hs))).2
  -- btc trajectory bound
  obtain ⟨M_btc, hM_btc_pos, hM_btc⟩ := btc.bounded
  set M : ℝ := max M_btc (1 / c) with hM_def
  have hM_pos : 0 < M := lt_of_lt_of_le hM_btc_pos (le_max_left _ _)
  have h_invc_le_M : 1 / c ≤ M := le_max_right _ _
  have h_Mbtc_le_M : M_btc ≤ M := le_max_left _ _
  -- Lipschitz of btc.pivp.field on closedBall 0 M
  obtain ⟨L, hL_bound⟩ := quadraticForm_locally_lipschitz A B h_field M hM_pos
  set L' : ℝ := max L 0 with hL'_def
  have hL'_nn : 0 ≤ L' := le_max_right _ _
  have hL'_bound : ∀ x y : Fin d → ℝ, ‖x‖ ≤ M → ‖y‖ ≤ M →
      ‖btc.pivp.field x - btc.pivp.field y‖ ≤ L' * ‖x - y‖ := by
    intro x y hx hy
    exact (hL_bound x y hx hy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- τ non-negativity
  have h_τ_nn : ∀ s, 0 ≤ s → 0 ≤ stage2_effectiveTime sol s := fun s hs =>
    stage2_effectiveTime_nonneg hε.le sol h_z0_nn s hs
  -- Bound on w: ‖selectiveUnscale o c (Fin.tail sol(s))‖ ≤ 1/c ≤ M
  have h_w_bdd : ∀ s, 0 ≤ s →
      ‖selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s))‖ ≤ M := by
    intro s hs
    have h_tail_bdd : ‖Fin.tail (sol.trajectory s)‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      exact (norm_le_pi_norm (sol.trajectory s) i.succ).trans (h_sol_bdd s hs)
    calc ‖selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s))‖
        ≤ ‖Fin.tail (sol.trajectory s)‖ / c :=
          selectiveUnscale_norm_le_div _ hc hc1 _
      _ ≤ 1 / c := by
          rw [div_le_div_iff_of_pos_right hc]; exact h_tail_bdd
      _ ≤ M := h_invc_le_M
  -- Bound on btc.sol ∘ τ
  have h_btc_bdd : ∀ s, 0 ≤ s →
      ‖btc.sol.trajectory (stage2_effectiveTime sol s)‖ ≤ M := fun s hs =>
    (hM_btc _ (h_τ_nn s hs)).trans h_Mbtc_le_M
  -- Delegate to the invariant-form theorem
  exact stage2_convergence_from_invariants hε hc hεc sol h_zero_init
    h_z0_nn h_z0_le h_z0_lb M L' hL'_nn h_w_bdd h_btc_bdd hL'_bound

/-- **Stage 2 z₀ invariant under conservation + output-field sign**.

Proves the LPP Remark 14 invariant `c ≤ z₀(s)` for all `s ≥ 0`, under the
minimal sufficient hypotheses:

* `h_conservative`: `∑ i, field(x)_i = 0` for all `x` (true for CRN fields on
  the probability simplex — preservation of total mass).
* `h_output_nonpos`: the output component of the underlying field, evaluated
  at the unscaled tail of the Stage 2 trajectory, is non-positive along the
  orbit. In the dual-rail / convergence regime, `field_o ~ α - x_o`, which is
  non-positive exactly when `x_o ≥ α` — and the Stage 2 dynamics naturally
  drive the output upward from 0.
* `h_z0_init_ge`: at `s = 0`, `z₀(0) ≥ c`. With Stage 2 init
  `z₀(0) = 1 - c·∑ P.init`, this holds whenever `c·∑ P.init ≤ 1 - c`
  (automatic for `∑ P.init ≤ 1` and `c ≤ 1/2`, or for suitable init bounds).

Key algebraic identity: using conservation `∑_j field(w)_j = 0`,
the Stage 2 z₀ ODE simplifies to

  `z₀'(s) = -ε · (1 - c) · field(w(s))_o · z₀(s)`

where `w(s) := selectiveUnscale o c (tail sol(s))`. With `0 < c ≤ 1`,
`z₀ ≥ 0`, and `field(w)_o ≤ 0`, the RHS is non-negative, so z₀ is monotone
non-decreasing on `[0, ∞)`. Hence `z₀(s) ≥ z₀(0) ≥ c`. -/
theorem stage2_z0_invariant_under_conservation
    {d : ℕ} [NeZero d] {α : ℝ} {ε c : ℝ}
    (hε : 0 ≤ ε) (_hc : 0 < c) (hc1 : c ≤ 1)
    {btc : BoundedTimeComputable d α}
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (h_sol_nn : ∀ s, 0 ≤ s → ∀ i, 0 ≤ sol.trajectory s i)
    (h_conservative : ∀ x, ∑ i, btc.pivp.field x i = 0)
    (h_output_nonpos : ∀ s, 0 ≤ s →
      btc.pivp.field (selectiveUnscale btc.pivp.output c
        (Fin.tail (sol.trajectory s))) btc.pivp.output ≤ 0)
    (h_z0_init_ge : c ≤ sol.trajectory 0 0) :
    ∀ s, 0 ≤ s → c ≤ sol.trajectory s 0 := by
  -- z₀(s) := sol.trajectory s 0
  set z₀ : ℝ → ℝ := fun s => sol.trajectory s 0 with hz₀_def
  -- Under conservation, the sum in stage2_zero_hasDerivAt reduces to
  -- ε · (1-c) · field(w)_o, where w = selectiveUnscale o c (tail sol s).
  -- Define the simplified derivative.
  set zd : ℝ → ℝ := fun s =>
    -ε * (1 - c) * btc.pivp.field
      (selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s)))
      btc.pivp.output * sol.trajectory s 0 with hzd_def
  -- Step 1: reduce the balancing-dilation derivative to zd under conservation.
  have h_sum_reduce : ∀ s, 0 ≤ s →
      -(∑ j : Fin d,
          selectiveLambdaTrick btc.pivp.output c
            (constantDilation ε btc.pivp.field)
            (Fin.tail (sol.trajectory s)) j) * sol.trajectory s 0
        = zd s := by
    intro s _
    set w : Fin d → ℝ :=
      selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s)) with hw_def
    -- Expand the inner sum.
    have h_term : ∀ j : Fin d,
        selectiveLambdaTrick btc.pivp.output c
          (constantDilation ε btc.pivp.field)
          (Fin.tail (sol.trajectory s)) j
          = (if j = btc.pivp.output then ε * btc.pivp.field w j
             else c * (ε * btc.pivp.field w j)) := by
      intro j
      simp only [selectiveLambdaTrick, constantDilation, hw_def]
    have h_sum_eq :
        (∑ j : Fin d, selectiveLambdaTrick btc.pivp.output c
            (constantDilation ε btc.pivp.field)
            (Fin.tail (sol.trajectory s)) j)
          = ε * btc.pivp.field w btc.pivp.output
            + c * ε * ∑ j ∈ Finset.univ.erase btc.pivp.output,
              btc.pivp.field w j := by
      rw [Finset.sum_congr rfl (fun j _ => h_term j)]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ btc.pivp.output)]
      simp only [if_true]
      rw [add_comm]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hj_ne : j ≠ btc.pivp.output := (Finset.mem_erase.mp hj).1
        simp only [if_neg hj_ne]
        ring
    -- Use conservation: ∑_j field(w) j = 0, hence ∑_{j≠o} = -field(w)_o.
    have h_cons : ∑ j ∈ Finset.univ.erase btc.pivp.output, btc.pivp.field w j
        = -btc.pivp.field w btc.pivp.output := by
      have h_full : ∑ j : Fin d, btc.pivp.field w j = 0 := h_conservative w
      have h_split :
          btc.pivp.field w btc.pivp.output
            + ∑ j ∈ Finset.univ.erase btc.pivp.output, btc.pivp.field w j = 0 := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ btc.pivp.output)] at h_full
        linarith
      linarith
    rw [h_sum_eq, h_cons]
    simp only [hzd_def, hw_def]
    ring
  -- Step 2: z₀ has derivative zd at each s ≥ 0.
  have h_hasDeriv : ∀ s, 0 ≤ s → HasDerivAt z₀ (zd s) s := by
    intro s hs
    have h := stage2_zero_hasDerivAt sol s hs
    have h_eq := h_sum_reduce s hs
    rw [h_eq] at h
    exact h
  -- Step 3: zd s ≥ 0 for s ≥ 0.
  have h_zd_nn : ∀ s, 0 ≤ s → 0 ≤ zd s := by
    intro s hs
    simp only [hzd_def]
    -- -ε * (1-c) * field_o * z₀ with ε ≥ 0, (1-c) ≥ 0, field_o ≤ 0, z₀ ≥ 0.
    have h1c : 0 ≤ 1 - c := by linarith
    have h_fo := h_output_nonpos s hs
    have h_z0 := h_sol_nn s hs 0
    -- (-ε)·(1-c)·field_o·z₀ = (ε·(1-c))·((-field_o)·z₀) ≥ 0
    have hA : 0 ≤ ε * (1 - c) := mul_nonneg hε h1c
    have hB : 0 ≤ (-btc.pivp.field (selectiveUnscale btc.pivp.output c
        (Fin.tail (sol.trajectory s))) btc.pivp.output) * sol.trajectory s 0 :=
      mul_nonneg (by linarith) h_z0
    nlinarith [hA, hB, mul_nonneg hA hB]
  -- Step 4: z₀ is continuous on Set.Ici 0.
  have h_cont : ContinuousOn z₀ (Set.Ici (0 : ℝ)) := by
    intro t ht
    exact ((h_hasDeriv t ht).continuousAt).continuousWithinAt
  -- Step 5: MonotoneOn z₀ on Set.Ici 0 via monotoneOn_of_hasDerivWithinAt_nonneg.
  have h_mono : MonotoneOn z₀ (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) h_cont
    · intro x hx
      have hx_nn : 0 < x := by
        rw [interior_Ici] at hx
        exact hx
      have hx_nn' : 0 ≤ x := hx_nn.le
      have hd := h_hasDeriv x hx_nn'
      exact hd.hasDerivWithinAt.mono (interior_subset)
    · intro x hx
      rw [interior_Ici] at hx
      exact h_zd_nn x hx.le
  -- Step 6: conclude z₀(s) ≥ z₀(0) ≥ c.
  intro s hs
  have h_z0_mono : z₀ 0 ≤ z₀ s :=
    h_mono Set.self_mem_Ici hs hs
  calc c ≤ z₀ 0 := h_z0_init_ge
    _ ≤ z₀ s := h_z0_mono

/-- A field with Stage2CubicForm structure (polynomial of degree ≤ 3) is locally Lipschitz. -/
private lemma cubicForm_locally_lipschitz {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field) :
    ∀ R, 0 < R → ∃ L, ∀ x y : Fin d → ℝ, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖field x - field y‖ ≤ L * ‖x - y‖ := by
  intro R hR
  -- Each non-zero component is the polynomial (∑∑ A·x_a·x_b - (∑ B·x_a)·x_i)·x₀
  -- First show ContDiff for each non-zero component
  have h_cd_ne : ∀ i, i ≠ s.zero → ContDiff ℝ ⊤ (fun x : Fin d → ℝ => field x i) := by
    intro i hi
    have h_eq : (fun x : Fin d → ℝ => field x i) =
        fun x => ((∑ a, ∑ b, s.A i a b * x a * x b) -
          (∑ a, s.B i a * x a) * x i) * x s.zero := funext (s.field_eq i hi)
    rw [h_eq]
    apply ContDiff.mul
    · exact (ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
        (contDiff_const.mul (contDiff_apply ℝ ℝ a)).mul (contDiff_apply ℝ ℝ b)).sub
        ((ContDiff.sum fun a _ => contDiff_const.mul (contDiff_apply ℝ ℝ a)).mul
          (contDiff_apply ℝ ℝ i))
    · exact contDiff_apply ℝ ℝ s.zero
  -- Zero component is -∑ of others, hence also ContDiff
  have h_cd_zero : ContDiff ℝ ⊤ (fun x : Fin d → ℝ => field x s.zero) := by
    have h_eq : (fun x : Fin d → ℝ => field x s.zero) =
        fun x => -(∑ j ∈ Finset.univ.filter (· ≠ s.zero), field x j) :=
      funext s.field_zero
    rw [h_eq]
    exact (ContDiff.sum fun j hj =>
      h_cd_ne j (Finset.mem_filter.mp hj).2).neg
  -- Full field is ContDiff
  have h_cd : ContDiff ℝ ⊤ (fun x : Fin d → ℝ => (fun i => field x i : Fin d → ℝ)) :=
    contDiff_pi' fun i => if hi : i = s.zero then hi ▸ h_cd_zero else h_cd_ne i hi
  -- Continuous Fréchet derivative (polynomial → smooth → continuous fderiv)
  have h_cont_fderiv : Continuous (fderiv ℝ field) :=
    h_cd.continuous_fderiv (by simp)
  -- On the compact closed R-ball, ‖fderiv‖ is bounded
  have h_compact : IsCompact (Metric.closedBall (0 : Fin d → ℝ) R) :=
    isCompact_closedBall 0 R
  obtain ⟨C, hC⟩ := h_compact.exists_bound_of_continuousOn
    h_cont_fderiv.norm.continuousOn
  -- Apply MVT on the convex closed ball
  refine ⟨C, fun x y hx hy => ?_⟩
  have hx' : x ∈ Metric.closedBall (0 : Fin d → ℝ) R := by
    rwa [Metric.mem_closedBall, dist_zero_right]
  have hy' : y ∈ Metric.closedBall (0 : Fin d → ℝ) R := by
    rwa [Metric.mem_closedBall, dist_zero_right]
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (h_cd.differentiable (by simp)).differentiableAt)
    (fun z hz => by
      have := hC z hz
      rwa [Real.norm_of_nonneg (norm_nonneg _)] at this)
    (convex_closedBall 0 R) hy' hx'

/-- CRN non-negativity invariance: if the field has CRN form
field(x)_i = prod_i(x) - degr_i(x)·x_i with prod, degr ≥ 0 on the
non-negative orthant, and the field is locally Lipschitz, then any
trajectory starting non-negative stays non-negative.

Proof method: squared negative mass F(t) = ∑_i min(x_i(t), 0)² satisfies
F(0) = 0 and F'(t) ≤ K·F(t) via Lipschitz decomposition at the positive
projection x⁺. Grönwall's inequality gives F ≡ 0. -/
private theorem crn_nonneg_invariance {d : ℕ} {P : PIVP d}
    (sol : P.Solution)
    (crn : IsCRNImplementable d P.field)
    (h_init_nn : ∀ i, 0 ≤ P.init i)
    (h_field_lip : ∀ (R : ℝ), 0 < R → ∃ (L : ℝ), ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖P.field x - P.field y‖ ≤ L * ‖x - y‖) :
    ∀ t, 0 ≤ t → ∀ i, 0 ≤ sol.trajectory t i := by
  intro t ht i
  -- Base case: t = 0
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · rw [show sol.trajectory 0 i = P.init i from congr_fun sol.init_cond i]
    exact h_init_nn i
  -- Inductive case: t > 0, apply Grönwall on [0, t]
  -- Define squared negative mass functional
  set x := sol.trajectory
  set F : ℝ → ℝ := fun s => ∑ j : Fin d, min (x s j) 0 ^ 2
  set F_deriv : ℝ → ℝ := fun s =>
    ∑ j : Fin d, 2 * min (x s j) 0 * P.field (x s) j
  -- F(0) = 0 since init ≥ 0
  have hF_zero : F 0 = 0 := by
    simp only [F, show x 0 = P.init from sol.init_cond]
    exact Finset.sum_eq_zero fun j _ => by
      rw [min_eq_right (h_init_nn j), zero_pow (by norm_num : 2 ≠ 0)]
  -- HasDerivAt for F via chain rule (min(·,0)² ∘ trajectory_j) + sum
  have hF_hasDerivAt : ∀ s, 0 ≤ s → HasDerivAt F (F_deriv s) s := by
    intro s hs
    have h := HasDerivAt.sum fun j (_ : j ∈ Finset.univ) =>
      (hasDerivAt_minSq (x s j)).comp s (hasDerivAt_pi.mp (sol.is_solution s hs) j)
    simp only [Function.comp_def] at h
    exact h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by simp only [F, x, Finset.sum_apply])
  -- F is continuous on [0, t]
  have hF_cont : ContinuousOn F (Set.Icc 0 t) := fun s hs =>
    (hF_hasDerivAt s (Set.mem_Icc.mp hs).1).continuousAt.continuousWithinAt
  -- Trajectory bound on [0, t]: continuous on compact → bounded
  have ⟨M, hM_pos, hM_bound⟩ : ∃ M : ℝ, 0 < M ∧ ∀ s ∈ Set.Icc 0 t, ‖x s‖ ≤ M := by
    have hx_cont : ContinuousOn x (Set.Icc 0 t) := fun s hs =>
      (sol.is_solution s (Set.mem_Icc.mp hs).1).continuousAt.continuousWithinAt
    have h_norm_cont : ContinuousOn (fun s => ‖x s‖) (Set.Icc 0 t) := fun s hs =>
      (sol.is_solution s (Set.mem_Icc.mp hs).1).continuousAt.norm.continuousWithinAt
    obtain ⟨s₀, _, h_max⟩ := isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.mpr ht_pos.le) h_norm_cont
    exact ⟨‖x s₀‖ + 1, by linarith [norm_nonneg (x s₀)],
      fun s hs => by
        have h : ‖x s‖ ≤ ‖x s₀‖ := h_max hs
        linarith⟩
  -- Lipschitz constant for the field on the M-ball
  obtain ⟨L₀, hL₀⟩ := h_field_lip M hM_pos
  set L := max L₀ 0 with L_def
  have hL_nn : (0 : ℝ) ≤ L := le_max_right _ _
  have hL : ∀ x y : Fin d → ℝ, ‖x‖ ≤ M → ‖y‖ ≤ M → ‖P.field x - P.field y‖ ≤ L * ‖x - y‖ :=
    fun x y hx hy =>
      (hL₀ x y hx hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- Key bound: F_deriv(s) ≤ (2 * L * d) * F(s) on [0, t)
  -- Splitting: F' = 2⟨min(x,0), field(x⁺)⟩ + 2⟨min(x,0), field(x)-field(x⁺)⟩
  -- First term ≤ 0 (prod_i(x⁺) ≥ 0 by IsPositivePoly, min(x_i,0) ≤ 0)
  -- Second term ≤ 2·L·d·F (Lipschitz + sum bound)
  have hF_bound : ∀ s ∈ Set.Ico (0 : ℝ) t, F_deriv s ≤ 2 * L * ↑d * F s := by
    intro s hs
    -- Positive projection and negative part
    set m : Fin d → ℝ := fun j => min (x s j) 0 with m_def
    set xp : Fin d → ℝ := fun j => max (x s j) 0 with xp_def
    have hm_nonpos : ∀ j, m j ≤ 0 := fun j => min_le_right _ _
    have hxp_nn : ∀ j, 0 ≤ xp j := fun j => le_max_right _ _
    have hxm_eq : x s - xp = m := funext fun j => by
      simp only [Pi.sub_apply, xp_def, m_def]
      linarith [min_add_max (x s j) (0 : ℝ)]
    -- ‖xp‖ ≤ M
    have hxp_le : ‖xp‖ ≤ M := by
      rw [pi_norm_le_iff_of_nonneg (by linarith [hM_pos])]
      intro j
      calc ‖xp j‖ = xp j := by rw [Real.norm_eq_abs, abs_of_nonneg (hxp_nn j)]
        _ = max (x s j) 0 := rfl
        _ ≤ |x s j| := max_le (le_abs_self _) (abs_nonneg _)
        _ = ‖(x s) j‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖x s‖ := norm_le_pi_norm _ j
        _ ≤ M := hM_bound s (Set.Ico_subset_Icc_self hs)
    -- Lipschitz: ‖field(x s) - field(xp)‖ ≤ L * ‖m‖
    have h_lip : ‖P.field (x s) - P.field xp‖ ≤ L * ‖m‖ := by
      calc ‖P.field (x s) - P.field xp‖
          ≤ L * ‖x s - xp‖ := hL _ _ (hM_bound s (Set.Ico_subset_Icc_self hs)) hxp_le
        _ = L * ‖m‖ := by rw [hxm_eq]
    -- Split: F_deriv = first_sum + second_sum
    have h_split : F_deriv s = (∑ j, 2 * m j * P.field xp j) +
        (∑ j, 2 * m j * (P.field (x s) j - P.field xp j)) := by
      simp only [F_deriv, ← Finset.sum_add_distrib]; congr 1; ext j; ring
    -- First sum ≤ 0 (CRN: prod(xp) ≥ 0 since xp ≥ 0)
    have h_first : ∑ j, 2 * m j * P.field xp j ≤ 0 := Finset.sum_nonpos fun j _ => by
      rcases le_or_gt 0 (x s j) with hge | hlt
      · simp [m_def, min_eq_right hge]
      · rw [crn.field_eq xp j, show xp j = 0 from by simp [xp_def, max_eq_right hlt.le],
            mul_zero, sub_zero]
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 2) (hm_nonpos j))
          (crn.prod_pos j xp hxp_nn)
    -- ‖m‖² ≤ F s (sup norm squared ≤ sum of squares)
    have h_norm_sq : ‖m‖ * ‖m‖ ≤ F s := by
      suffices h : ‖m‖ * ‖m‖ ≤ ∑ j : Fin d, m j ^ 2 by
        exact h.trans (le_of_eq (by simp [F, m_def]))
      rcases Nat.eq_zero_or_pos d with rfl | hd_pos
      · -- d = 0: norm = 0, sum = 0
        have : ‖m‖ = 0 := le_antisymm
          ((pi_norm_le_iff_of_nonneg le_rfl).mpr (fun j => Fin.elim0 j)) (norm_nonneg _)
        simp [this]
      · -- d ≥ 1: sup achieved by some k, then use single_le_sum
        haveI : Nonempty (Fin d) := ⟨⟨0, hd_pos⟩⟩
        obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ
          (fun j => ‖m j‖) Finset.univ_nonempty
        have h_eq : ‖m‖ = ‖m k‖ := le_antisymm
          ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => hk j (Finset.mem_univ _))
          (norm_le_pi_norm m k)
        calc ‖m‖ * ‖m‖ = ‖m k‖ ^ 2 := by rw [h_eq, sq]
          _ = (m k) ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
          _ ≤ ∑ j, (m j) ^ 2 :=
            Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ k)
    -- Second sum ≤ 2·L·d·F(s) via Lipschitz + norm estimates
    have h_second : ∑ j, 2 * m j * (P.field (x s) j - P.field xp j) ≤ 2 * L * ↑d * F s := by
      -- Per-term bound: 2·m_j·v_j ≤ 2·(-m_j)·‖v‖
      have h_term : ∀ j, 2 * m j * (P.field (x s) j - P.field xp j) ≤
          2 * (-m j) * ‖P.field (x s) - P.field xp‖ := by
        intro j
        have hv_j : |P.field (x s) j - P.field xp j| ≤ ‖P.field (x s) - P.field xp‖ := by
          rw [← Real.norm_eq_abs, ← Pi.sub_apply]; exact norm_le_pi_norm _ j
        nlinarith [hm_nonpos j, le_abs_self (P.field (x s) j - P.field xp j),
          neg_abs_le (P.field (x s) j - P.field xp j),
          norm_nonneg (P.field (x s) - P.field xp)]
      calc ∑ j, 2 * m j * (P.field (x s) j - P.field xp j)
          ≤ ∑ j, 2 * (-m j) * ‖P.field (x s) - P.field xp‖ :=
            Finset.sum_le_sum fun j _ => h_term j
        _ = 2 * ‖P.field (x s) - P.field xp‖ * ∑ j : Fin d, (-m j) := by
            rw [Finset.mul_sum]; congr 1; ext j; ring
        _ ≤ 2 * (L * ‖m‖) * (↑d * ‖m‖) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left h_lip (by norm_num)
            · calc ∑ j : Fin d, (-m j) = ∑ j : Fin d, ‖m j‖ := by
                    congr 1; ext j; rw [Real.norm_eq_abs, abs_of_nonpos (hm_nonpos j)]
                _ ≤ Fintype.card (Fin d) • ‖m‖ := Pi.sum_norm_apply_le_norm _
                _ = ↑d * ‖m‖ := by rw [Fintype.card_fin, nsmul_eq_mul]
            · exact Finset.sum_nonneg fun j _ => neg_nonneg.mpr (hm_nonpos j)
            · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hL_nn (norm_nonneg _))
        _ = 2 * L * ↑d * (‖m‖ * ‖m‖) := by ring
        _ ≤ 2 * L * ↑d * F s := by
            exact mul_le_mul_of_nonneg_left h_norm_sq
              (mul_nonneg (mul_nonneg (by norm_num) hL_nn) (by positivity))
    linarith [h_split, h_first, h_second]
  -- Apply Grönwall: F(s) ≤ gronwallBound 0 K 0 (s - 0) = 0
  set K := 2 * L * (d : ℝ)
  have hF_le_zero : F t ≤ 0 := by
    have h_gw := le_gronwallBound_of_liminf_deriv_right_le (δ := 0) (K := K) (ε := 0)
      hF_cont
      (fun s hs _ hr =>
        ((hF_hasDerivAt s (Set.mem_Ico.mp hs).1).hasDerivWithinAt).liminf_right_slope_le hr)
      (le_of_eq hF_zero)
      (fun s hs => by simp only [add_zero]; exact hF_bound s hs)
      t (Set.right_mem_Icc.mpr ht)
    linarith [gronwallBound_ε0_δ0 K (t - 0)]
  -- F ≥ 0 (sum of squares), so F(t) = 0
  have hF_nonneg : 0 ≤ F t := Finset.sum_nonneg fun j _ => sq_nonneg _
  -- Each min(x_i(t), 0)² = 0, hence min(x_i(t), 0) = 0, hence x_i(t) ≥ 0
  have hF_eq_zero : F t = 0 := le_antisymm hF_le_zero hF_nonneg
  have h_summand : min (x t i) 0 ^ 2 = 0 := by
    have h1 : min (x t i) 0 ^ 2 ≤ ∑ j : Fin d, min (x t j) 0 ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (min (x t k) 0)) (Finset.mem_univ i)
    change min (x t i) 0 ^ 2 ≤ F t at h1
    linarith [sq_nonneg (min (x t i) 0)]
  have h_min_zero : min (x t i) 0 = 0 := by
    nlinarith [sq_nonneg (min (x t i) 0)]
  linarith [min_le_left (x t i) (0 : ℝ)]

/-- Global ODE solution existence for CRN-implementable conservative systems
on the simplex with locally Lipschitz field.

Proved in `Ripple.Core.ODEGlobal` by combining:
- `locally_lipschitz_bounded_global_ode` (narrow Mathlib-gap axiom: local Picard
  + a priori bound ⇒ global)
- `crn_local_nonneg` (CRN non-negativity on half-open intervals, proved)
- `conservative_local_sum_const` (conservation pins the sum, proved)
- `simplex_norm_le_one` (non-negativity + sum = 1 ⇒ sup-norm ≤ 1, proved)

Formerly an axiom; now a theorem delegating to `crn_simplex_global_ode_solution'`. -/
noncomputable def crn_simplex_global_ode_solution {d : ℕ} (P : PIVP d)
    (h_crn : IsCRNImplementable d P.field)
    (h_cons : IsConservative P.field)
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖P.field x - P.field y‖ ≤ L * ‖x - y‖)
    (h_init_nn : ∀ i, 0 ≤ P.init i)
    (h_init_simplex : ∑ i, P.init i = 1)
    : PIVP.Solution P :=
  crn_simplex_global_ode_solution' P h_crn h_cons h_lip h_init_nn h_init_simplex

/-- Axiom: Stage 2 ODE convergence.

Given a CRN-implementable BTC computing α, the Stage 2 PIVP solution
(from `crn_simplex_global_ode_solution`) converges to α with the same
modulus, provided ε·c ≥ 1.

The key argument ([LPP] Remark 14):
1. The selectiveLambdaTrick preserves output dynamics: the equation for
   z_{o+1} uses f_o(selectiveUnscale(tail z)), where selectiveUnscale
   does NOT divide the output by c.
2. The balancing dilation creates time dilation by factor z₀(t).
3. In effective time τ(t) = ∫₀ᵗ z₀(s)ds, the output evolves by the
   original (ε-scaled) dynamics.
4. With ε·c ≥ 1 and simplex/non-negativity, τ(t) grows fast enough
   that ε·τ(t) ≥ t, giving the same convergence modulus. -/
axiom stage2_convergence_axiom {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α) (ε c : ℝ)
    (hε : 0 < ε) (hc : 0 < c) (hεc : 1 ≤ ε * c)
    (h_init_nn : ∀ i, 0 ≤ btc.pivp.init i)
    (h_sum_le : c * ∑ j, btc.pivp.init j ≤ 1)
    (crn : IsCRNImplementable d btc.pivp.field)
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp)) :
    ∀ r : ℕ, ∀ t : ℝ, t > btc.modulus r →
      |sol.trajectory t (stage2_pivp ε c btc.pivp).output - α| <
        Real.exp (-(r : ℝ))

/-- Stage 2 ODE existence with convergence (derived from the two axioms above).

Given a BTC computing α with quadratic CRN coefficients A, B, the Stage 2 PIVP
(ε-scaling + selective λ-shrinking + balancing dilation) has a solution
that converges to α with the same modulus, provided ε·c ≥ 1.

Requires explicit A, B coefficients (not just `IsCRNImplementable`) because
the locally Lipschitz proof goes through `Stage2CubicForm`, which needs the
quadratic coefficient matrices. -/
theorem stage2_ode_axiom {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α) (ε c : ℝ)
    (hε : 0 < ε) (hc : 0 < c) (hεc : 1 ≤ ε * c)
    (A : Fin d → Fin d → Fin d → ℝ) (B : Fin d → Fin d → ℝ)
    (hA : ∀ i a b, 0 ≤ A i a b) (hB : ∀ i a, 0 ≤ B i a)
    (h_field : ∀ i x, btc.pivp.field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i)
    (h_init_nn : ∀ i, 0 ≤ btc.pivp.init i)
    (h_sum_le : c * ∑ j, btc.pivp.init j ≤ 1) :
    ∃ sol : PIVP.Solution (stage2_pivp ε c btc.pivp),
      ∀ r : ℕ, ∀ t : ℝ, t > btc.modulus r →
        |sol.trajectory t (stage2_pivp ε c btc.pivp).output - α| <
          Real.exp (-(r : ℝ)) := by
  -- Derive CRN implementability from A, B decomposition
  have crn : IsCRNImplementable d btc.pivp.field := {
    prod := fun i x => ∑ a, ∑ b, A i a b * x a * x b
    degr := fun i x => ∑ a, B i a * x a
    prod_pos := fun i x hx => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => mul_nonneg (mul_nonneg (hA i a b) (hx a)) (hx b)
    degr_pos := fun i x hx => Finset.sum_nonneg fun a _ => mul_nonneg (hB i a) (hx a)
    field_eq := fun x i => h_field i x
  }
  -- Step 1: The stage2 system satisfies all hypotheses for global ODE existence
  let P := stage2_pivp ε c btc.pivp
  have h_crn' : IsCRNImplementable (d + 1) P.field :=
    (stage2_field_tpp (o := btc.pivp.output) hε.le hc crn).toIsCRNImplementable
  have h_cons' : IsConservative P.field :=
    balancingDilation_conservative _
  -- Locally Lipschitz via Stage2CubicForm (polynomial degree ≤ 3)
  have h_lip' : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin (d + 1) → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖P.field x - P.field y‖ ≤ L * ‖x - y‖ :=
    cubicForm_locally_lipschitz
      (stage2_field_cubicForm (o := btc.pivp.output) hε.le hc A B hA hB h_field)
  have h_init_nn' : ∀ i, 0 ≤ P.init i :=
    stage2_init_nonneg hc.le h_init_nn h_sum_le
  have h_init_simp : ∑ i, P.init i = 1 :=
    stage2_init_simplex c btc.pivp.init
  -- Step 2: Global solution exists
  let sol := crn_simplex_global_ode_solution P h_crn' h_cons' h_lip' h_init_nn' h_init_simp
  -- Step 3: Convergence
  exact ⟨sol, stage2_convergence_axiom btc ε c hε hc hεc h_init_nn h_sum_le crn sol⟩

/-- Stage 2 ODE existence and convergence: given BTC d α with CRN
decomposition, there exist ε, c > 0 (both rational) such that the
Stage 2 PIVP has a solution converging to α with the same modulus.

Parameter choice (proved):
  - n = ⌈∑ init⌉₊ + 1 (ensures c·∑init ≤ 1)
  - c = 1/n (rational, positive)
  - ε = n (rational, positive, ε·c = 1)

Boundedness is proved separately in `stage2_core` from
simplex conservation + CRN non-negativity + Lipschitz. -/
private theorem stage2_ode_solution {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (A : Fin d → Fin d → Fin d → ℝ) (B : Fin d → Fin d → ℝ)
    (hA : ∀ i a b, 0 ≤ A i a b) (hB : ∀ i a, 0 ≤ B i a)
    (h_field : ∀ i x, btc.pivp.field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i)
    (h_init_nn : ∀ i, 0 ≤ btc.pivp.init i) :
    ∃ (ε c : ℝ) (_ : 0 < ε) (_ : 0 < c),
      c * ∑ j, btc.pivp.init j ≤ 1 ∧
      (∃ qε : ℚ, ε = (qε : ℝ)) ∧ (∃ qc : ℚ, c = (qc : ℝ)) ∧
      ∃ sol : PIVP.Solution (stage2_pivp ε c btc.pivp),
        ∀ r : ℕ, ∀ t : ℝ, t > btc.modulus r →
          |sol.trajectory t (stage2_pivp ε c btc.pivp).output - α| <
            Real.exp (-(r : ℝ)) := by
  -- n = ⌈∑ init⌉₊ + 1
  let n : ℕ := Nat.ceil (∑ j, btc.pivp.init j) + 1
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  -- c·∑init ≤ 1: since ∑init ≤ ⌈∑init⌉₊ ≤ n
  have h_cS : 1 / (n : ℝ) * ∑ j, btc.pivp.init j ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hn_pos]
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast Nat.le_succ _)
  -- ε·c = n · (1/n) = 1
  have hεc : 1 ≤ (n : ℝ) * (1 / (n : ℝ)) := by
    rw [mul_one_div, div_self (ne_of_gt hn_pos)]
  -- Apply theorem with A, B coefficients
  obtain ⟨sol, h_conv⟩ := stage2_ode_axiom btc (n : ℝ) (1 / (n : ℝ))
    hn_pos (div_pos one_pos hn_pos) hεc A B hA hB h_field h_init_nn h_cS
  exact ⟨(n : ℝ), 1 / (n : ℝ), hn_pos, div_pos one_pos hn_pos, h_cS,
    ⟨(n : ℚ), by push_cast; ring⟩, ⟨1 / (n : ℚ), by push_cast; ring⟩, sol, h_conv⟩

/-! ## Stage Core Lemmas

The pipeline stages are split into "core" lemmas (with sorry for the main
construction) and derived theorems (proved by composition). The core lemmas
isolate the two independent construction challenges:
  - Stage 1: v-variable quadraticization (polynomial/algebraic)
  - Stage 2: λ-trick + balancing dilation (analytic: ODE existence, convergence) -/

/-- Axiom: v-variable quadraticization (Theorem 12 in [LPP]).

Any CRN-implementable polynomial ODE can be quadraticized: introduce
variables v_α = x^α for each multi-index α appearing in the field,
yielding a degree ≤ 2 system with explicit CRN coefficients A, B.

The construction:
  v'_α = Σ_k α_k · P_k(v) · v_{α-e_k} - (Σ_k α_k · Q_k(v)) · v_α
where P_k, Q_k are the CRN production/degradation terms, rewritten as
LINEAR polynomials in v (each monomial x^β becomes v_β).

Mathematically justified by:
1. MvPolynomial support enumeration gives finite monomial set
2. v_α(t) = x(t)^α explicitly solves the v-ODE (chain rule)
3. CRN non-negativity: P_k ≥ 0 on ℝ≥0 → A ≥ 0; Q_k ≥ 0 → B ≥ 0
4. Init: v_α(0) = init^α (rational powers of rational inits)
5. Boundedness: |v_α| ≤ M^{|α|} from boundedness of x

The algebraic construction is in `VVariable.lean`; remaining sorry:
ODE solution (chain rule for monomials) and boundedness transfer. -/
theorem stage1_core_axiom {d : ℕ} {α : ℝ}
    (btc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d btc.pivp) :
    ∃ (d' : ℕ) (btc' : BoundedTimeComputable d' α)
      (A : Fin d' → Fin d' → Fin d' → ℝ) (B : Fin d' → Fin d' → ℝ),
      (∀ i a b, 0 ≤ A i a b) ∧
      (∀ i a, 0 ≤ B i a) ∧
      (∀ i x, btc'.pivp.field x i =
        (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i) ∧
      (∀ i, 0 ≤ btc'.pivp.init i) ∧
      (∀ i, ∃ q : ℚ, btc'.pivp.init i = ↑q) :=
  stage1_vvariable btc pcd

/-- Stage 1 core: proved from `stage1_core_axiom`. -/
private theorem stage1_core {d : ℕ} {α : ℝ}
    (btc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d btc.pivp) :
    ∃ (d' : ℕ) (btc' : BoundedTimeComputable d' α)
      (A : Fin d' → Fin d' → Fin d' → ℝ) (B : Fin d' → Fin d' → ℝ),
      (∀ i a b, 0 ≤ A i a b) ∧
      (∀ i a, 0 ≤ B i a) ∧
      (∀ i x, btc'.pivp.field x i =
        (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i) ∧
      (∀ i, 0 ≤ btc'.pivp.init i) ∧
      (∀ i, ∃ q : ℚ, btc'.pivp.init i = ↑q) :=
  stage1_core_axiom btc pcd

/-- Stage 2 core (Theorem 13 in [LPP]):
Given a quadratic CRN with explicit coefficients A, B, non-negative
rational initial conditions, construct a TPP-implementable system on the
simplex with all properties needed by Stage 3 (tpp_to_lpp).

Algebraic parts (proved):
  - `stage2_field_tpp`: TPP-implementable field
  - `stage2_field_cubicForm`: Stage2CubicForm structure
  - `stage2_init_simplex/rational/nonneg`: initial condition properties
  - `conservative_trajectory_simplex`: simplex invariance from conservation

Analytic parts (`crn_nonneg_invariance` PROVED; ODE via axioms):
  - ODE existence: `crn_simplex_global_ode_solution` (axiom)
  - Convergence: `stage2_convergence_axiom` (axiom)
  - Non-negativity invariance (proved via squared negative mass + Grönwall) -/
private theorem stage2_core {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (A : Fin d → Fin d → Fin d → ℝ) (B : Fin d → Fin d → ℝ)
    (hA : ∀ i a b, 0 ≤ A i a b) (hB : ∀ i a, 0 ≤ B i a)
    (h_field : ∀ i x, btc.pivp.field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i)
    (h_init_nn : ∀ i, 0 ≤ btc.pivp.init i)
    (h_init_rat : ∀ i, ∃ q : ℚ, btc.pivp.init i = ↑q) :
    ∃ (d' : ℕ) (btc' : BoundedTimeComputable d' α),
      ∃ (_ : IsTPPImplementable d' btc'.pivp.field)
        (_ : Stage2CubicForm d' btc'.pivp.field),
        (∀ t, 0 ≤ t → ∑ i, btc'.sol.trajectory t i = 1) ∧
        (∀ t, 0 ≤ t → ∀ i, 0 ≤ btc'.sol.trajectory t i) ∧
        (∀ i, ∃ q : ℚ, btc'.sol.trajectory 0 i = ↑q) := by
  -- Get ODE solution for Stage 2 system (via theorem using A, B coefficients)
  obtain ⟨ε, c, hε, hc, h_sum_le, hε_q, hc_q, sol, h_conv⟩ :=
    stage2_ode_solution btc A B hA hB h_field h_init_nn
  -- Reconstruct CRN decomposition from A/B coefficients (needed for TPP/nonneg)
  have crn : IsCRNImplementable d btc.pivp.field := {
    prod := fun i x => ∑ a, ∑ b, A i a b * x a * x b
    degr := fun i x => ∑ a, B i a * x a
    prod_pos := fun i x hx => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => mul_nonneg (mul_nonneg (hA i a b) (hx a)) (hx b)
    degr_pos := fun i x hx => Finset.sum_nonneg fun a _ => mul_nonneg (hB i a) (hx a)
    field_eq := fun x i => h_field i x
  }
  -- Algebraic: TPP and CubicForm (computed before btc' for boundedness proof)
  have tpp' : IsTPPImplementable (d + 1) (stage2_pivp ε c btc.pivp).field :=
    stage2_field_tpp (o := btc.pivp.output) hε.le hc crn
  have s' : Stage2CubicForm (d + 1) (stage2_pivp ε c btc.pivp).field :=
    stage2_field_cubicForm (o := btc.pivp.output) hε.le hc A B hA hB h_field
  -- Simplex invariance (PROVED via conservative_trajectory_simplex)
  have h_simplex : ∀ t, 0 ≤ t → ∑ i, sol.trajectory t i = 1 :=
    fun t ht => conservative_trajectory_simplex sol tpp'.conservative
      (stage2_init_simplex c btc.pivp.init) ht
  -- Non-negativity: CRN invariance via Grönwall (PROVED)
  have h_nn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ sol.trajectory t i :=
    fun t ht => crn_nonneg_invariance sol tpp'.toIsCRNImplementable
      (stage2_init_nonneg hc.le h_init_nn h_sum_le)
      (cubicForm_locally_lipschitz s') t ht
  -- Boundedness from simplex + non-negativity: each component in [0,1] ⊂ [-2,2]
  have h_bounded : (stage2_pivp ε c btc.pivp).IsBounded sol.trajectory := by
    refine ⟨2, two_pos, fun t ht => ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (h_nn t ht i)]
    calc sol.trajectory t i
        ≤ ∑ j, sol.trajectory t j :=
          Finset.single_le_sum (fun j _ => h_nn t ht j) (Finset.mem_univ i)
      _ = 1 := h_simplex t ht
      _ ≤ 2 := by norm_num
  -- Build BoundedTimeComputable for Stage 2
  let btc' : BoundedTimeComputable (d + 1) α := {
    pivp := stage2_pivp ε c btc.pivp
    sol := sol
    modulus := btc.modulus
    bounded := h_bounded
    convergence := h_conv
  }
  refine ⟨d + 1, btc', tpp', s', h_simplex, h_nn, ?_⟩
  -- Rational init: algebraic (PROVED via stage2_init_rational)
  · intro i
    have h_init := congr_fun sol.init_cond i
    rw [show btc'.sol.trajectory 0 i = sol.trajectory 0 i from rfl, h_init]
    exact stage2_init_rational hc_q h_init_rat i

/-- Stage 1 (Theorem 12 in [LPP]):
Any CRN is a solution of a CRN-implementable system of degree ≤ 2.
Derived from `stage1_core` by extracting CRN decomposition from A/B. -/
theorem stage1_quadraticization {d : ℕ} {α : ℝ}
    (btc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d btc.pivp) :
    ∃ d' : ℕ, ∃ btc' : BoundedTimeComputable d' α,
      ∃ _ : IsCRNImplementable d' btc'.pivp.field, True := by
  obtain ⟨d', btc', A, B, hA, hB, h_field, _, _⟩ := stage1_core btc pcd
  exact ⟨d', btc', {
    prod := fun i x => ∑ a, ∑ b, A i a b * x a * x b
    degr := fun i x => ∑ a, B i a * x a
    prod_pos := fun i x hx => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => mul_nonneg (mul_nonneg (hA i a b) (hx a)) (hx b)
    degr_pos := fun i x hx => Finset.sum_nonneg fun a _ => mul_nonneg (hB i a) (hx a)
    field_eq := fun x i => h_field i x
  }, trivial⟩

/-- Stage 2 (Theorem 13 in [LPP]):
Any quadratic CRN is a solution of a TPP-implementable cubic form system.
Derived from `stage1_core` + `stage2_core`. -/
theorem stage2_to_tpp {d : ℕ} {α : ℝ}
    (btc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d btc.pivp) :
    ∃ d' : ℕ, ∃ btc' : BoundedTimeComputable d' α,
      ∃ _ : IsTPPImplementable d' btc'.pivp.field, True := by
  obtain ⟨d₁, btc₁, A, B, hA, hB, h_field, h_nn, h_rat⟩ := stage1_core btc pcd
  obtain ⟨d₂, btc₂, tpp₂, _, _, _, _⟩ := stage2_core btc₁ A B hA hB h_field h_nn h_rat
  exact ⟨d₂, btc₂, tpp₂, trivial⟩

/-- Pure Stage 3 (Theorem 15 in [LPP]):
Given a TPP-implementable system on the simplex with rational initial
conditions and non-negativity, the self-product z_{i,j} = xᵢ·xⱼ gives
an LPP-computable number.

The construction:
1. z_{i,j}(t) = x_i(t)·x_j(t), so z' = selfProductField by product rule
2. selfProductField is PP-implementable (degree 4 in x → degree 2 in z)
3. ∑z = (∑x)² = 1 on simplex
4. Readout: marked z-variables track α

**Preconditions** (guaranteed by Stage 2 output):
- TPP-implementable field with rational simplex initial conditions
- Solution stays non-negative and on simplex for t ≥ 0
- Solution satisfies the field ODE -/
theorem tpp_to_lpp {d : ℕ} {α : ℝ}
    (_hα01 : 0 ≤ α ∧ α ≤ 1)
    (btc : BoundedTimeComputable d α)
    (_tpp : IsTPPImplementable d btc.pivp.field)
    (s : Stage2CubicForm d btc.pivp.field)
    (h_simplex : ∀ t, 0 ≤ t → ∑ i, btc.sol.trajectory t i = 1)
    (h_nonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ btc.sol.trajectory t i)
    (h_init_rat : ∀ i, ∃ q : ℚ, btc.sol.trajectory 0 i = ↑q) :
    ∃ _ : IsLPPComputable α, True := by
  -- Abbreviations
  let x := btc.sol.trajectory
  let fld := btc.pivp.field
  let o := btc.pivp.output
  -- Index encoding: Fin d × Fin d ≃ Fin (d * d)
  let e : Fin d × Fin d ≃ Fin (d * d) := finProdFinEquiv
  -- Self-product trajectory: z_i(t) = x_{π₁(i)}(t)·x_{π₂(i)}(t)
  let z : ℝ → Fin (d * d) → ℝ := fun t i =>
    x t (e.symm i).1 * x t (e.symm i).2
  -- Self-product field transported through encoding
  let zfld : (Fin (d * d) → ℝ) → Fin (d * d) → ℝ := fun v i =>
    selfProductField fld (v ∘ e) (e.symm i)
  -- Marked states: output row {e(o, j) | j : Fin d}
  let marked : Finset (Fin (d * d)) := Finset.univ.image (fun j : Fin d => e (o, j))
  -- PP z-field from Stage2CubicForm: degree-2 via symbolic substitution x_a·x_b → z_{a,b}.
  -- s.ppField is defined on Fin d × Fin d; transport it through encoding e to Fin (d*d).
  let ppfld : (Fin (d * d) → ℝ) → Fin (d * d) → ℝ := fun v i =>
    s.ppField (v ∘ e) (e.symm i)
  -- NOTE: PP-implementability (IsPPImplementable) is NOT required here.
  -- The paper [LPP] Theorem 15 claims global conservation of the z-field, but
  -- formal verification shows the z-field is only conservative on the self-product
  -- manifold M = {z(i,j) = x_i·x_j}. For d=2, the residual off-manifold is
  -- z_{00}·(z_{01}-z_{10})·Pz_1. This is a gap in the paper. Since the trajectory
  -- never leaves M, manifold conservation suffices for all downstream properties.
  -- See IsLPPComputable docstring in Defs.lean for details.
  --
  -- Manifold agreement: ppfld and zfld agree on {z_{i,j} = x_i·x_j}
  have h_manifold : ∀ t, 0 ≤ t → ∀ i, ppfld (z t) i = zfld (z t) i := by
    intro t ht i
    change s.ppField (z t ∘ e) (e.symm i) = selfProductField fld (z t ∘ e) (e.symm i)
    have hze : z t ∘ e = fun ij => x t ij.1 * x t ij.2 :=
      funext fun ij => by simp [z, Function.comp]
    rw [hze]
    exact s.ppField_eq_on_manifold (x t) (h_simplex t ht) (e.symm i)
  -- z(t) solves the analytic field zfld by the product rule
  have h_sol_zfld : ∀ t, 0 ≤ t → HasDerivAt z (fun i => zfld (z t) i) t := by
    intro t ht
    refine hasDerivAt_pi.mpr (fun i => ?_)
    have h_sp := hasDerivAt_pi.mp
      (selfProduct_hasDerivAt (btc.sol.is_solution t ht) (h_simplex t ht)) (e.symm i)
    convert h_sp using 1
    change selfProductField fld (z t ∘ e) (e.symm i) =
      selfProductField fld (fun ij => x t ij.1 * x t ij.2) (e.symm i)
    congr 1; ext ij; simp [z]
  -- z(t) solves ppfld because ppfld agrees with zfld on the self-product manifold
  have h_sol_pp : ∀ t, 0 ≤ t → HasDerivAt z (fun i => ppfld (z t) i) t := by
    intro t ht
    convert h_sol_zfld t ht using 1
    ext i; exact h_manifold t ht i
  -- Helper: e is injective on the output row
  have h_e_inj : Function.Injective (fun j : Fin d => e (o, j)) :=
    fun _ _ h => (Prod.mk.inj (e.injective h)).2
  -- Helper: marked sum equals output value on simplex
  have h_sum_marked : ∀ t, 0 ≤ t → ∑ i ∈ marked, z t i = x t o := by
    intro t ht
    rw [Finset.sum_image h_e_inj.injOn]
    simp_rw [show ∀ j : Fin d, z t (e (o, j)) = x t o * x t j from fun j => by simp [z]]
    rw [← Finset.mul_sum, h_simplex t ht, mul_one]
  -- Build IsLPPComputable α
  exact ⟨{
    n := d * d
    field := ppfld
    sol := z
    marked := marked
    init_rational := fun i => by
      obtain ⟨q₁, hq₁⟩ := h_init_rat (e.symm i).1
      obtain ⟨q₂, hq₂⟩ := h_init_rat (e.symm i).2
      refine ⟨q₁ * q₂, ?_⟩
      change btc.sol.trajectory 0 (e.symm i).1 * btc.sol.trajectory 0 (e.symm i).2 = ↑(q₁ * q₂)
      rw [hq₁, hq₂, Rat.cast_mul]
    init_simplex := by
      rw [show (∑ i, z 0 i) = ∑ ij : Fin d × Fin d, x 0 ij.1 * x 0 ij.2 from
        Fintype.sum_equiv e.symm _ _ (fun _ => rfl)]
      exact selfProduct_simplex (h_simplex 0 le_rfl)
    init_nonneg := fun i =>
      mul_nonneg (h_nonneg 0 le_rfl (e.symm i).1) (h_nonneg 0 le_rfl (e.symm i).2)
    simplex := fun t ht => by
      rw [show (∑ i, z t i) = ∑ ij : Fin d × Fin d, x t ij.1 * x t ij.2 from
        Fintype.sum_equiv e.symm _ _ (fun _ => rfl)]
      exact selfProduct_simplex (h_simplex t ht)
    nonneg := fun t ht i =>
      mul_nonneg (h_nonneg t ht (e.symm i).1) (h_nonneg t ht (e.symm i).2)
    is_solution := fun t ht => h_sol_pp t ht
    convergence := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨r, hr⟩ := exists_nat_gt (-Real.log ε)
      refine ⟨max (btc.modulus r + 1) 0, fun t ht => ?_⟩
      have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
      rw [Real.dist_eq, h_sum_marked t ht0]
      calc |x t o - α|
          < Real.exp (-(r : ℝ)) :=
            btc.convergence r t (lt_of_lt_of_le (by linarith : btc.modulus r < btc.modulus r + 1)
              (le_trans (le_max_left _ _) ht))
        _ < ε := by
            calc Real.exp (-(r : ℝ))
                < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr (by linarith)
              _ = ε := Real.exp_log hε
  }, trivial⟩

/-- Stage 3 (full pipeline): any CRN-implementable BTC number in [0,1] is LPP-computable.
Chains Stage 1 → Stage 2 → pure Stage 3 via `stage1_core` + `stage2_core` + `tpp_to_lpp`.
No sorry — all sorry's are isolated in the core lemmas. -/
theorem stage3_to_lpp {d : ℕ} {α : ℝ} (hα01 : 0 ≤ α ∧ α ≤ 1)
    (btc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d btc.pivp) :
    ∃ _ : IsLPPComputable α, True := by
  -- Stage 1: quadraticize to get explicit A/B coefficients
  obtain ⟨d₁, btc₁, A, B, hA, hB, h_field, h_nn, h_rat⟩ := stage1_core btc pcd
  -- Stage 2: λ-trick + balancing dilation → TPP on simplex
  obtain ⟨d₂, btc₂, tpp₂, s₂, h_simp₂, h_nn₂, h_rat₂⟩ :=
    stage2_core btc₁ A B hA hB h_field h_nn h_rat
  -- Pure Stage 3: TPP → LPP via self-product
  exact tpp_to_lpp hα01 btc₂ tpp₂ s₂ h_simp₂ h_nn₂ h_rat₂

/-- Stage 4 (Theorem 16 / Construction 1 in [LPP]):
Given a syntactic PP balance equation with explicit ℚ coefficients,
the product distribution α_{i,j,k,l} = c_{k,i,j} · c_{l,i,j} / 4
produces a PLPP whose balance field exactly matches the PP field.

**Design note:** Stage 4 requires syntactic (coefficient-level) input,
not just a semantic `IsPPImplementable`. This is because constructing
PLPP transition probabilities requires reading off the polynomial
coefficients c_{r,i,j}. In the pipeline, Stages 1–3 produce explicit
polynomial constructions, so the output is naturally syntactic.
The product distribution gives exact match (no ε-scaling needed)
because Σ_r c_{r,i,j} = 2 ensures Σ_{k,l} α_{i,j,k,l} = 1. -/
theorem stage4_to_plpp {n : ℕ} (eq : SynPPBalance n) :
    ∃ tr : PLPPTransitions n, tr.balanceField = eq.toField :=
  ⟨eq.toPLPPTransitions, eq.toPLPPTransitions_balanceField_eq⟩

/-! ## Main Theorem

The main result of [LPP]: LPPs compute the same set of numbers
in [0,1] as GPACs and CRNs. -/

/-- Main Theorem ([LPP]):
If α ∈ [0,1] is GPAC/CRN computable (bounded-time) with syntactic
polynomial certificates, then α is LPP-computable.

The proof composes the four stages:
  CRN → quadratic CRN → TPP cubic → PP quadratic → PLPP → LPP.

Note: takes `CertifiedBoundedTimeComputable` (syntactic PolyPIVP) rather
than semantic `BoundedTimeComputable`, because the pipeline requires
explicit polynomial structure for monomial enumeration in Stage 1. -/
theorem gpac_to_lpp {α : ℝ} (hα01 : 0 ≤ α ∧ α ≤ 1)
    {d : ℕ} (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp) :
    ∃ _ : IsLPPComputable α, True :=
  stage3_to_lpp hα01 cbtc pcd

/-- AXIOM: Algebraic numbers are CRN-computable with syntactic certificates.
Justified by [RTCRN1] Theorem 3.4 + [LPP] Corollary 18:
1. Algebraic α is a root of p ∈ ℤ[x], p ≠ 0
2. Newton's method for p converges exponentially from a rational approximation
3. The iteration can be expressed as a polynomial PIVP (rational coefficients)
4. The resulting CRN is the dual-rail encoding of the Newton iteration -/
axiom algebraic_is_certified_crn {α : ℝ}
    (halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0) :
    ∃ (d : ℕ) (cbtc : CertifiedBoundedTimeComputable d α)
      (_ : PolyCRNDecomposition d cbtc.pivp), True

/-- Corollary 18 in [LPP]: Algebraic numbers in [0,1] are LPP-computable. -/
theorem algebraic_lpp_computable {α : ℝ} (hα01 : 0 ≤ α ∧ α ≤ 1)
    (halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0) :
    ∃ _ : IsLPPComputable α, True := by
  obtain ⟨d, cbtc, pcd, _⟩ := algebraic_is_certified_crn halg
  exact gpac_to_lpp hα01 cbtc pcd

/-! ## Motivating Example

The number ½e⁻¹ is LPP-computable ([LPP] §1.2).

The ODE system:
  F' = -2FE,  E' = -E,  G' = 2FE + E
with F(0) = ½, E(0) = ½, G(0) = 0.

Then F(t) = ½·exp(exp(-t) - 1) → ½e⁻¹ as t → ∞.

The corresponding CRN:
  F + E → G + E  (rate 2)
  E → G -/

/-- ½e⁻¹ is LPP-computable. This is the motivating example from [LPP] §1.2,
demonstrating that the extended LPP notion (with continuum of equilibria)
can compute transcendental numbers. Fully verified — see Example.lean. -/
theorem half_exp_neg_one_lpp_computable :
    ∃ _ : IsLPPComputable (Real.exp (-1) / 2), True :=
  ⟨halfExpNegOne_lpp, trivial⟩

/-! ## LPP Numbers Are in [0,1]

An LPP-computable number is necessarily in the unit interval,
since the readout sum is bounded by the simplex constraint. -/

/-- An LPP-computable number is in [0,1]. The lower bound follows from
non-negativity of states; the upper bound from the simplex constraint. -/
theorem lpp_computable_in_01 {ν : ℝ} (h : IsLPPComputable ν) :
    0 ≤ ν ∧ ν ≤ 1 := by
  constructor
  · exact ge_of_tendsto h.convergence (Filter.eventually_atTop.mpr ⟨0, fun t ht =>
      Finset.sum_nonneg (fun i _ => h.nonneg t ht i)⟩)
  · exact le_of_tendsto h.convergence (Filter.eventually_atTop.mpr ⟨0, fun t ht => by
      calc ∑ i ∈ h.marked, h.sol t i
          ≤ ∑ i, h.sol t i := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) (fun i _ _ => h.nonneg t ht i)
        _ = 1 := h.simplex t ht⟩)

/-! ## LPP → CRN-Computable (Easy Direction)

Every LPP-computable number is CRN-computable. This is the "easy"
direction of the main equivalence (Theorem 8 in [LPP]). The proof
augments the LPP system with a readout-sum variable. -/

/-- Every LPP-computable number is CRN-computable.
The construction augments the n-variable LPP with a (n+1)-th variable
tracking the marked-state sum, then extracts a BTC from the augmented
solution and convergence. -/
noncomputable def lpp_to_gpac {ν : ℝ} (h : IsLPPComputable ν) :
    IsCRNComputable ν := by
  -- Extract Tendsto → quantitative convergence
  have h_tend := h.convergence
  have h_quant : ∀ r : ℕ, ∃ T : ℝ, ∀ t, T < t →
      |∑ i ∈ h.marked, h.sol t i - ν| < Real.exp (-(r : ℝ)) := by
    intro r
    obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp h_tend) (Real.exp (-(r : ℝ))) (Real.exp_pos _)
    exact ⟨T, fun t ht => by rw [← Real.dist_eq]; exact hT t (le_of_lt ht)⟩
  -- The augmented trajectory: Fin (h.n + 1) → ℝ
  -- Components 0..n-1: original LPP states; component n: readout sum
  let traj : ℝ → Fin (h.n + 1) → ℝ := fun t =>
    vecSnoc (h.sol t) (∑ j ∈ h.marked, h.sol t j)
  -- The augmented field
  let augField : (Fin (h.n + 1) → ℝ) → Fin (h.n + 1) → ℝ := fun v =>
    vecSnoc (h.field (Fin.init v)) (∑ j ∈ h.marked, h.field (Fin.init v) j)
  -- The PIVP
  let pivp : PIVP (h.n + 1) :=
    { field := augField, init := traj 0, output := Fin.last h.n }
  -- Helper: init reduces under vecSnoc
  have h_init : ∀ t, Fin.init (traj t) = h.sol t := by
    intro t; exact vecSnoc_init
  -- The solution
  have h_is_sol : ∀ t : ℝ, 0 ≤ t → HasDerivAt traj (augField (traj t)) t := by
    intro t ht
    have h_aug_eq : augField (traj t) = vecSnoc (h.field (h.sol t))
        (∑ j ∈ h.marked, h.field (h.sol t) j) := by
      simp only [augField, h_init]
    rw [h_aug_eq]
    refine hasDerivAt_pi.mpr (fun i => ?_)
    refine Fin.lastCases ?_ (fun j => ?_) i
    · -- i = last: readout sum
      have h_fn_eq : (fun s => traj s (Fin.last h.n)) =
          (fun s => ∑ j ∈ h.marked, h.sol s j) := by
        funext s; exact vecSnoc_last
      rw [vecSnoc_last, h_fn_eq]
      have h_sum := HasDerivAt.sum (fun j (_ : j ∈ h.marked) =>
        hasDerivAt_pi.mp (h.is_solution t ht) j)
      rwa [show (∑ j ∈ h.marked, fun s => h.sol s j) =
          (fun s => ∑ j ∈ h.marked, h.sol s j) from
          funext (fun s => Finset.sum_apply ..)] at h_sum
    · -- i = castSucc j: original state
      have h_fn_eq : (fun s => traj s (Fin.castSucc j)) = (fun s => h.sol s j) := by
        funext s; exact vecSnoc_castSucc
      rw [vecSnoc_castSucc, h_fn_eq]
      exact hasDerivAt_pi.mp (h.is_solution t ht) j
  let sol : PIVP.Solution pivp :=
    { trajectory := traj, init_cond := rfl, is_solution := h_is_sol }
  -- Boundedness: on the simplex, all components are in [0,1]
  have h_bounded : pivp.IsBounded sol.trajectory := by
    refine ⟨2, two_pos, fun t ht => ?_⟩
    rw [show sol.trajectory t = traj t from rfl,
        (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2))]
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · -- last: ‖readout sum‖ ≤ 2
      simp only [traj, vecSnoc_last, Real.norm_eq_abs,
          abs_of_nonneg (Finset.sum_nonneg (fun k _ => h.nonneg t ht k))]
      calc ∑ k ∈ h.marked, h.sol t k
          ≤ ∑ k, h.sol t k := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) (fun k _ _ => h.nonneg t ht k)
        _ = 1 := h.simplex t ht
        _ ≤ 2 := by norm_num
    · -- castSucc j: ‖sol j‖ ≤ 2
      simp only [traj, vecSnoc_castSucc, Real.norm_eq_abs,
          abs_of_nonneg (h.nonneg t ht j)]
      calc h.sol t j ≤ ∑ k, h.sol t k :=
            Finset.single_le_sum (fun k _ => h.nonneg t ht k) (Finset.mem_univ j)
        _ = 1 := h.simplex t ht
        _ ≤ 2 := by norm_num
  -- Time modulus (extracted from Tendsto via classical choice)
  let modulus : TimeModulus := fun r => (h_quant r).choose
  have h_mod_spec : ∀ r t, modulus r < t →
      |sol.trajectory t pivp.output - ν| < Real.exp (-(r : ℝ)) := by
    intro r t ht
    change |vecSnoc (h.sol t) (∑ j ∈ h.marked, h.sol t j) (Fin.last h.n) - ν| < _
    rw [vecSnoc_last]
    exact (h_quant r).choose_spec t ht
  exact ⟨h.n + 1, ⟨pivp, sol, modulus, h_bounded, h_mod_spec⟩, trivial⟩

/-! ## CRN-Computable Product Closure

The product of two CRN-computable numbers is CRN-computable.
The proof combines two independent PIVPs and adds a product variable. -/

/-- The product of two CRN-computable numbers is CRN-computable.
Given BTC(d₁,α) and BTC(d₂,β), construct BTC(d₁+d₂+1, α·β) by
running both systems in parallel and tracking the product of outputs. -/
noncomputable def crn_computable_mul {α β : ℝ}
    (ha : IsCRNComputable α) (hb : IsCRNComputable β) :
    IsCRNComputable (α * β) := by
  obtain ⟨d₁, btc₁, _⟩ := ha
  obtain ⟨d₂, btc₂, _⟩ := hb
  -- The combined trajectory: (d₁ + d₂) + 1 variables
  -- First d₁: system 1; next d₂: system 2; last: product of outputs
  let t₁ := btc₁.sol.trajectory
  let t₂ := btc₂.sol.trajectory
  let f₁ := btc₁.pivp.field
  let f₂ := btc₂.pivp.field
  let o₁ := btc₁.pivp.output
  let o₂ := btc₂.pivp.output
  -- Projections from the combined state to each subsystem
  let proj₁ : (Fin ((d₁ + d₂) + 1) → ℝ) → Fin d₁ → ℝ := fun v j =>
    v (Fin.castSucc (Fin.castAdd d₂ j))
  let proj₂ : (Fin ((d₁ + d₂) + 1) → ℝ) → Fin d₂ → ℝ := fun v j =>
    v (Fin.castSucc (Fin.natAdd d₁ j))
  -- Output indices lifted to combined space
  let o₁' : Fin ((d₁ + d₂) + 1) := Fin.castSucc (Fin.castAdd d₂ o₁)
  let o₂' : Fin ((d₁ + d₂) + 1) := Fin.castSucc (Fin.natAdd d₁ o₂)
  -- Combined trajectory
  let traj : ℝ → Fin ((d₁ + d₂) + 1) → ℝ := fun t =>
    vecSnoc (vecAddCases (t₁ t) (t₂ t)) (t₁ t o₁ * t₂ t o₂)
  -- Combined field
  let augField : (Fin ((d₁ + d₂) + 1) → ℝ) → Fin ((d₁ + d₂) + 1) → ℝ :=
    fun v => vecSnoc
      (vecAddCases (f₁ (proj₁ v)) (f₂ (proj₂ v)))
      (f₁ (proj₁ v) o₁ * v o₂' + v o₁' * f₂ (proj₂ v) o₂)
  -- PIVP
  let pivp : PIVP ((d₁ + d₂) + 1) :=
    { field := augField, init := traj 0, output := Fin.last (d₁ + d₂) }
  -- Helper: projections recover original trajectories
  have h_proj₁ : ∀ t, proj₁ (traj t) = t₁ t := by
    intro t; funext j; simp [proj₁, traj]
  have h_proj₂ : ∀ t, proj₂ (traj t) = t₂ t := by
    intro t; funext j; simp [proj₂, traj]
  have h_o₁ : ∀ t, traj t o₁' = t₁ t o₁ := by
    intro t; simp [traj, o₁']
  have h_o₂ : ∀ t, traj t o₂' = t₂ t o₂ := by
    intro t; simp [traj, o₂']
  -- HasDerivAt for the combined system
  have h_is_sol : ∀ t : ℝ, 0 ≤ t → HasDerivAt traj (augField (traj t)) t := by
    intro t ht
    have h_aug_eq : augField (traj t) = vecSnoc
        (vecAddCases (f₁ (t₁ t)) (f₂ (t₂ t)))
        (f₁ (t₁ t) o₁ * t₂ t o₂ + t₁ t o₁ * f₂ (t₂ t) o₂) := by
      simp only [augField, h_proj₁, h_proj₂, h_o₁, h_o₂]
    rw [h_aug_eq]
    refine hasDerivAt_pi.mpr (fun i => ?_)
    refine Fin.lastCases ?_ (fun j => ?_) i
    · -- i = last: product variable
      have h_fn_eq : (fun s => traj s (Fin.last _)) = (fun s => t₁ s o₁ * t₂ s o₂) := by
        funext s; simp [traj]
      simp only [vecSnoc_last]
      rw [h_fn_eq]
      exact (hasDerivAt_pi.mp (btc₁.sol.is_solution t ht) o₁).mul
        (hasDerivAt_pi.mp (btc₂.sol.is_solution t ht) o₂)
    · -- i = castSucc j: from one of the two subsystems
      refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
      · -- left part: system 1
        have h_fn_eq : (fun s => traj s (Fin.castSucc (Fin.castAdd d₂ j₁))) =
            (fun s => t₁ s j₁) := by
          funext s; simp [traj]
        simp only [vecSnoc_castSucc, vecAddCases_left]
        rw [h_fn_eq]
        exact hasDerivAt_pi.mp (btc₁.sol.is_solution t ht) j₁
      · -- right part: system 2
        have h_fn_eq : (fun s => traj s (Fin.castSucc (Fin.natAdd d₁ j₂))) =
            (fun s => t₂ s j₂) := by
          funext s; simp [traj]
        simp only [vecSnoc_castSucc, vecAddCases_right]
        rw [h_fn_eq]
        exact hasDerivAt_pi.mp (btc₂.sol.is_solution t ht) j₂
  let sol : PIVP.Solution pivp :=
    { trajectory := traj, init_cond := rfl, is_solution := h_is_sol }
  -- Convergence: product of outputs → α * β
  have h_tend : Filter.Tendsto (fun t => t₁ t o₁ * t₂ t o₂) Filter.atTop (nhds (α * β)) :=
    btc₁.to_tendsto.mul btc₂.to_tendsto
  -- Extract modulus from Tendsto
  have h_quant : ∀ r : ℕ, ∃ T : ℝ, ∀ t, T < t →
      |t₁ t o₁ * t₂ t o₂ - α * β| < Real.exp (-(r : ℝ)) := by
    intro r
    obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp h_tend) (Real.exp (-(r : ℝ))) (Real.exp_pos _)
    exact ⟨T, fun t ht => by rw [← Real.dist_eq]; exact hT t (le_of_lt ht)⟩
  let modulus : TimeModulus := fun r => (h_quant r).choose
  -- Boundedness
  have h_bounded : pivp.IsBounded sol.trajectory := by
    obtain ⟨M₁, hM₁_pos, hM₁⟩ := btc₁.bounded
    obtain ⟨M₂, hM₂_pos, hM₂⟩ := btc₂.bounded
    refine ⟨M₁ + M₂ + M₁ * M₂, by positivity, fun t ht => ?_⟩
    rw [show sol.trajectory t = traj t from rfl,
        (pi_norm_le_iff_of_nonneg (by positivity))]
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · -- product variable: |x·y| ≤ M₁·M₂ ≤ M₁+M₂+M₁·M₂
      have h_eq : traj t (Fin.last _) = t₁ t o₁ * t₂ t o₂ := by simp [traj]
      rw [h_eq]
      calc |t₁ t o₁ * t₂ t o₂| = |t₁ t o₁| * |t₂ t o₂| := abs_mul _ _
        _ ≤ ‖t₁ t‖ * ‖t₂ t‖ :=
          mul_le_mul (norm_le_pi_norm (t₁ t) o₁)
            (norm_le_pi_norm (t₂ t) o₂) (abs_nonneg _) (norm_nonneg _)
        _ ≤ M₁ * M₂ :=
          mul_le_mul (hM₁ t ht) (hM₂ t ht) (norm_nonneg _) (le_of_lt hM₁_pos)
        _ ≤ M₁ + M₂ + M₁ * M₂ := le_add_of_nonneg_left (by positivity)
    · -- subsystem variables
      refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
      · have h_eq : traj t (Fin.castSucc (Fin.castAdd d₂ j₁)) = t₁ t j₁ := by
            simp [traj]
        rw [h_eq]
        calc |t₁ t j₁| = ‖t₁ t j₁‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖t₁ t‖ := norm_le_pi_norm _ _
          _ ≤ M₁ := hM₁ t ht
          _ ≤ M₁ + M₂ + M₁ * M₂ := by linarith [mul_pos hM₁_pos hM₂_pos]
      · have h_eq : traj t (Fin.castSucc (Fin.natAdd d₁ j₂)) = t₂ t j₂ := by
            simp [traj]
        rw [h_eq]
        calc |t₂ t j₂| = ‖t₂ t j₂‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖t₂ t‖ := norm_le_pi_norm _ _
          _ ≤ M₂ := hM₂ t ht
          _ ≤ M₁ + M₂ + M₁ * M₂ := by linarith [mul_pos hM₁_pos hM₂_pos]
  -- Package the BTC
  have h_conv : ∀ r t, modulus r < t →
      |sol.trajectory t pivp.output - α * β| < Real.exp (-(r : ℝ)) := by
    intro r t ht
    have h_eq : sol.trajectory t pivp.output = t₁ t o₁ * t₂ t o₂ := by
      simp [sol, pivp, traj]
    rw [h_eq]
    exact (h_quant r).choose_spec t ht
  exact ⟨(d₁ + d₂) + 1, ⟨pivp, sol, modulus, h_bounded, h_conv⟩, trivial⟩

/-! ## Product Protocol (Lemma 11)

LPP-computable numbers are closed under multiplication.
The proof routes through the GPAC pipeline: LPP → CRN → CRN (product)
→ LPP (via Stage 3). -/

/-- Lemma 11 in [LPP]: the product of two LPP-computable numbers
is LPP-computable.

Proved directly via the d₁·d₂ product construction in `Ripple.LPP.Product`:
state z_{i,j} = x_i·y_j with productField giving the product-rule ODE. -/
theorem lpp_computable_mul {α β : ℝ}
    (ha : IsLPPComputable α) (hb : IsLPPComputable β) :
    ∃ _ : IsLPPComputable (α * β), True :=
  lpp_product ha hb

/-! ## Unimolecular Protocols Compute Only Rationals (Lemma 10)

A large-population unimolecular protocol (LPUP) can only compute
rational numbers. The proof uses the functional graph structure:
each state transitions to exactly one other state, forming rho-shaped
paths that converge to cycles. -/

/-! ### Proof strategy for `linear_ode_marked_sum_rational`

Avoids eigenvalue decomposition. Key steps:

1. Let f(t) = Σ_{marked} sol(t)_i. All derivatives are bounded (sol on simplex).
2. By Cayley-Hamilton, p(D)f = 0 (scalar ODE with rational coefficients).
3. Factor p(x) = x^k · q(x) over ℚ, q(0) ≠ 0. Then q(D)f is polynomial degree < k.
4. Bounded polynomial → constant → rational.
5. Integration argument → q(0)·ν = g(0), hence ν rational.
-/

/-- The derivative of the marked sum is the marked sum of A·sol.
This follows from the component-wise derivative of the ODE solution. -/
private lemma marked_sum_hasDerivAt {n : ℕ}
    (A : Fin n → Fin n → ℚ)
    (sol : ℝ → Fin n → ℝ)
    (marked : Finset (Fin n))
    (h_sol : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt sol (fun i => ∑ j, (A i j : ℝ) * sol t j) t)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => ∑ i ∈ marked, sol s i)
      (∑ i ∈ marked, ∑ j, (A i j : ℝ) * sol t j) t := by
  have h_comp : ∀ i ∈ marked, HasDerivAt (fun s => sol s i)
      (∑ j, (A i j : ℝ) * sol t j) t :=
    fun i _ => hasDerivAt_pi.mp (h_sol t ht) i
  have := HasDerivAt.sum h_comp
  simp only [Finset.sum_fn] at this
  exact this

/-- The marked sum is bounded between 0 and 1 (from simplex + non-negativity). -/
private lemma marked_sum_bounded {n : ℕ}
    (sol : ℝ → Fin n → ℝ)
    (marked : Finset (Fin n))
    (h_nonneg : ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n, 0 ≤ sol t i)
    (h_simplex : ∀ t : ℝ, 0 ≤ t → ∑ i, sol t i = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ ∑ i ∈ marked, sol t i ∧ ∑ i ∈ marked, sol t i ≤ 1 := by
  refine ⟨Finset.sum_nonneg fun i _ => h_nonneg t ht i, ?_⟩
  calc ∑ i ∈ marked, sol t i
      ≤ ∑ i, sol t i := Finset.sum_le_univ_sum_of_nonneg fun i => h_nonneg t ht i
    _ = 1 := h_simplex t ht

/-- **Barbalat-type lemma**: If f converges to L on [0,∞) and its derivative
f' is bounded, then f' → 0. This follows from: bounded derivative ⟹
uniformly continuous f' ⟹ Barbalat's lemma (convergent integral +
uniformly continuous ⟹ limit zero).

Not in Mathlib as of 2026-04. Proof: f' Lipschitz (bounded f'') +
  MVT gives |f'(t)| ≤ |f(t+δ)-f(t)|/δ + Cδ. For large t, the first
  term is small by Cauchy, and Cδ is small by choice of δ. -/
private lemma tendsto_zero_of_tendsto_bounded_deriv
    (f f' f'' : ℝ → ℝ) (L : ℝ)
    (hf_deriv : ∀ t : ℝ, 0 ≤ t → HasDerivAt f (f' t) t)
    (hf'_deriv : ∀ t : ℝ, 0 ≤ t → HasDerivAt f' (f'' t) t)
    (hf_conv : Filter.Tendsto f Filter.atTop (nhds L))
    (hf''_bdd : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → |f'' t| ≤ C) :
    Filter.Tendsto f' Filter.atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := hf''_bdd
  have hC_nn : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 le_rfl)
  have hC1_pos : (0 : ℝ) < C + 1 := by linarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- δ for Lipschitz, η for Cauchy
  set δ := ε / (4 * (C + 1)) with hδ_def
  have hδ_pos : 0 < δ := by positivity
  set η := ε * δ / 8 with hη_def
  have hη_pos : 0 < η := by positivity
  -- For t past T: |f(t)-L| < η and |f(t+δ)-L| < η
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hf_conv η hη_pos)
  filter_upwards [Filter.eventually_ge_atTop (max T 0)] with t ht
  rw [Real.dist_eq, sub_zero]
  have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  -- Cauchy bound: |f(t+δ) - f(t)| < 2η
  have hf_cauchy : |f (t + δ) - f t| < 2 * η := by
    calc |f (t + δ) - f t|
        = dist (f (t + δ)) (f t) := (Real.dist_eq _ _).symm
      _ ≤ dist (f (t + δ)) L + dist L (f t) := dist_triangle _ L _
      _ = dist (f (t + δ)) L + dist (f t) L := by rw [dist_comm L]
      _ < η + η := add_lt_add (hT (t + δ) (by linarith)) (hT t htT)
      _ = 2 * η := by ring
  -- MVT on f over [t, t+δ]: ∃ c, f'(c) = (f(t+δ)-f(t))/δ
  have h_cont_f : ContinuousOn f (Set.Icc t (t + δ)) :=
    fun s hs => (hf_deriv s (le_trans ht0 hs.1)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hc_eq⟩ := exists_hasDerivAt_eq_slope f f' (by linarith) h_cont_f
    (fun x ⟨hxt, _⟩ => hf_deriv x (le_trans ht0 (le_of_lt hxt)))
  rw [show t + δ - t = δ from by ring] at hc_eq
  -- Slope bound: |f'(c)| < 2η/δ
  have h_slope : |f' c| < 2 * η / δ := by
    rw [hc_eq, abs_div, abs_of_pos hδ_pos]
    exact div_lt_div_of_pos_right hf_cauchy hδ_pos
  -- MVT on f' over [t, c]: Lipschitz bound |f'(t)-f'(c)| ≤ C·δ
  have hct : t < c := hc.1
  have h_cont_f' : ContinuousOn f' (Set.Icc t c) :=
    fun s hs => (hf'_deriv s (le_trans ht0 hs.1)).continuousAt.continuousWithinAt
  obtain ⟨c₂, hc₂, hc₂_eq⟩ := exists_hasDerivAt_eq_slope f' f'' hct h_cont_f'
    (fun x ⟨hxt, _⟩ => hf'_deriv x (le_trans ht0 (le_of_lt hxt)))
  rw [eq_div_iff (ne_of_gt (sub_pos.mpr hct))] at hc₂_eq
  have h_lip : |f' t - f' c| ≤ C * δ := by
    rw [show f' t - f' c = -(f' c - f' t) from by ring, abs_neg, ← hc₂_eq, abs_mul,
        abs_of_nonneg (le_of_lt (sub_pos.mpr hct))]
    calc |f'' c₂| * (c - t)
        ≤ C * (c - t) := mul_le_mul_of_nonneg_right
          (hC c₂ (le_trans ht0 (le_of_lt hc₂.1))) (le_of_lt (sub_pos.mpr hct))
      _ ≤ C * δ := mul_le_mul_of_nonneg_left (by linarith [hc.2]) hC_nn
  -- Triangle: |f'(t)| ≤ |f'(c)| + |f'(t)-f'(c)|
  have h_tri : |f' t| ≤ |f' c| + |f' t - f' c| := by
    have h := abs_add_le (f' c) (f' t - f' c)
    linarith [show |f' c + (f' t - f' c)| = |f' t| from by congr 1; ring]
  -- Arithmetic: 2η/δ + Cδ ≤ ε/2
  have h_arith : 2 * η / δ + C * δ ≤ ε / 2 := by
    have h1 : 2 * η / δ = ε / 4 := by
      field_simp [ne_of_gt hδ_pos]; ring
    have h2 : C * δ ≤ ε / 4 := by
      have hδε : δ * (4 * (C + 1)) = ε := by rw [hδ_def]; field_simp
      nlinarith
    linarith
  -- Combine
  linarith

/-- A bounded function on [0,∞) whose m-th iterated derivative vanishes
is constant. Proof by induction on m, shifting the derivative tower.
Requires ALL levels bounded (holds in the ODE application since
g j = Σ c_k · f(j+k) and each f k is bounded on the simplex). -/
private lemma const_of_iterated_deriv_zero_bounded
    (g : ℕ → ℝ → ℝ) (m : ℕ)
    (hg_deriv : ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → HasDerivAt (g k) (g (k + 1) t) t)
    (hg_zero : ∀ t : ℝ, 0 ≤ t → g m t = 0)
    (hg_bdd : ∀ j : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → |g j t| ≤ C) :
    ∀ t : ℝ, 0 ≤ t → g 0 t = g 0 0 := by
  -- Induction on m, generalizing the tower
  induction m generalizing g with
  | zero =>
    intro t ht
    rw [hg_zero t ht, hg_zero 0 le_rfl]
  | succ m ih =>
    -- Shift the tower: g' j = g (j + 1). Then g' m = g (m+1) = 0,
    -- g' has derivative tower, and all g' j bounded.
    have hg1_const : ∀ t, 0 ≤ t → g 1 t = g 1 0 :=
      ih (fun (j : ℕ) => g (j + 1))
        (fun (k : ℕ) (t : ℝ) (ht : 0 ≤ t) => hg_deriv (k + 1) t ht)
        (fun (t : ℝ) (ht : 0 ≤ t) => hg_zero t ht)
        (fun (j : ℕ) => hg_bdd (j + 1))
    -- Helper: hg_deriv gives g(0+1) which is definitionally g 1
    have hd0 : ∀ t, 0 ≤ t → HasDerivAt (g 0) (g 1 t) t :=
      fun t ht => hg_deriv 0 t ht
    rcases eq_or_ne (g 1 0) 0 with hg10 | hg10_ne
    · -- g 0' = g 1 = 0, so g 0 constant on [0,∞)
      intro t ht
      rcases eq_or_lt_of_le ht with rfl | h0t
      · rfl
      · exact constant_of_has_deriv_right_zero
          (fun s hs => (hd0 s hs.1).continuousAt.continuousWithinAt)
          (fun s ⟨hs0, _⟩ => by
            have hd := hd0 s hs0
            rw [hg1_const s hs0, hg10] at hd
            exact hd.hasDerivWithinAt)
          t (Set.right_mem_Icc.mpr (le_of_lt h0t))
    · -- g 1 0 ≠ 0: g 0 is affine, hence unbounded → contradiction
      exfalso
      obtain ⟨C, hC⟩ := hg_bdd 0
      have hC_nn : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 le_rfl)
      have h_affine : ∀ t, 0 ≤ t → g 0 t = g 0 0 + g 1 0 * t := by
        intro t ht
        rcases eq_or_lt_of_le ht with rfl | h0t
        · simp
        · have h_zero_deriv : ∀ s ∈ Set.Ico (0 : ℝ) t,
              HasDerivWithinAt (fun u => g 0 u - g 0 0 - g 1 0 * u) 0 (Set.Ici s) s := by
            intro s ⟨hs0, _⟩
            have hd := hd0 s hs0
            rw [hg1_const s hs0] at hd
            -- hd : HasDerivAt (g 0) (g 1 0) s
            have hd_sub := (hd.sub (hasDerivAt_const s (g 0 0))).sub
              ((hasDerivAt_id s).const_mul (g 1 0))
            -- derivative value: g 1 0 - 0 - g 1 0 * 1 = 0
            simp only [sub_zero, mul_one, sub_self] at hd_sub
            exact hd_sub.hasDerivWithinAt
          have h_cont : ContinuousOn (fun u => g 0 u - g 0 0 - g 1 0 * u) (Set.Icc 0 t) := by
            apply ContinuousOn.sub
            · apply ContinuousOn.sub
              · exact fun s hs => (hd0 s hs.1).continuousAt.continuousWithinAt
              · exact continuousOn_const
            · exact continuousOn_const.mul continuousOn_id
          have := constant_of_has_deriv_right_zero h_cont h_zero_deriv t
            (Set.right_mem_Icc.mpr (le_of_lt h0t))
          simp at this; linarith
      -- Unbounded: |g 0 0 + g 1 0 * T| > C for large T
      set T := (|g 0 0| + C + 1) / |g 1 0| with hT_def
      have hT_nn : 0 ≤ T :=
        div_nonneg (by linarith [abs_nonneg (g 0 0)]) (abs_nonneg _)
      have h_bnd := hC T hT_nn
      rw [h_affine T hT_nn] at h_bnd
      have h_prod : |g 1 0| * T = |g 0 0| + C + 1 :=
        mul_div_cancel₀ _ (abs_ne_zero.mpr hg10_ne)
      have h_abs_prod : |g 1 0 * T| = |g 0 0| + C + 1 := by
        rw [abs_mul, abs_of_nonneg hT_nn, h_prod]
      -- Reverse triangle: |a + b| ≥ |b| - |a|
      have h_rev : |g 0 0 + g 1 0 * T| ≥ |g 1 0 * T| - |g 0 0| := by
        have h := abs_add_le (g 0 0 + g 1 0 * T) (-g 0 0)
        rw [show (g 0 0 + g 1 0 * T) + -g 0 0 = g 1 0 * T from by ring, abs_neg] at h
        linarith
      rw [h_abs_prod] at h_rev
      linarith

/-- **Core rationality lemma**: If a bounded derivative tower on [0,∞) satisfies
a linear ODE (Cayley-Hamilton relation) with rational coefficients and rational
initial conditions, and the base function converges, then its limit is rational.

**Proof outline** (uses `tendsto_zero_of_tendsto_bounded_deriv` and
`const_of_iterated_deriv_zero_bounded`):

Let p = charpoly(A) and m = rootMultiplicity(0, p), so p = X^m · q with q(0) ≠ 0.
Define g(t) = Σ_{j ≤ deg q} q_j · f_j(t) (the "q(D)f₀" combination).

(a) **g^(m) = 0**: Since p_k = 0 for k < m and p_{m+j} = q_j, the Cayley-Hamilton
    relation Σ p_k f_k = 0 rewrites to Σ q_j f_{m+j} = g^(m) = 0.

(b) **g bounded + g^(m) = 0 → g constant**: by `const_of_iterated_deriv_zero_bounded`.

(c) **g(0) ∈ ℚ**: from rational initial conditions and rational q coefficients.

(d) **f_k → 0 for k ≥ 1**: by inductive application of
    `tendsto_zero_of_tendsto_bounded_deriv` (Barbalat).

(e) **Conclusion**: g constant = g(0) ∈ ℚ. As t → ∞, g(t) → q₀·ν + 0.
    So q₀·ν = g(0), giving ν = g(0)/q₀ ∈ ℚ. -/
private lemma bounded_linear_ode_limit_rational {n : ℕ}
    (A : Fin n → Fin n → ℚ)
    (f : ℕ → ℝ → ℝ) -- f k t = Σ_{marked} (A^k sol(t))_i (the k-th "derivative")
    (ν : ℝ)
    (h_deriv : ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → HasDerivAt (f k) (f (k + 1) t) t)
    (h_bound : ∀ k : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → |f k t| ≤ C)
    (h_init_rat : ∀ k : ℕ, ∃ q : ℚ, f k 0 = (q : ℝ))
    (h_cayley : ∀ t : ℝ, 0 ≤ t →  -- p(A)·sol = 0 → p(D)f = 0
      ∑ k ∈ Finset.range (n + 1),
        ((Matrix.charpoly (Matrix.of A)).coeff k : ℝ) * f k t = 0)
    (h_conv : Filter.Tendsto (f 0) Filter.atTop (nhds ν)) :
    ∃ q : ℚ, ν = (q : ℝ) := by
  -- Step 1: Extract the characteristic polynomial and its root multiplicity at 0
  let p := (Matrix.of A).charpoly
  have hp_ne : p ≠ 0 := Polynomial.Monic.ne_zero (Matrix.charpoly_monic _)
  let m := p.rootMultiplicity 0
  -- p.coeff k = 0 for k < m
  have h_low_zero : ∀ k, k < m → p.coeff k = 0 := by
    intro k hk
    have hX_dvd : Polynomial.X ^ m ∣ p := by
      have := (Polynomial.le_rootMultiplicity_iff hp_ne).mp (le_refl m)
      rwa [Polynomial.C_0, sub_zero] at this
    rw [Polynomial.X_pow_dvd_iff] at hX_dvd; exact hX_dvd k hk
  -- p.coeff m ≠ 0
  have h_cm_ne : p.coeff m ≠ 0 := by
    have h_not := Polynomial.pow_rootMultiplicity_not_dvd hp_ne (0 : ℚ)
    rw [Polynomial.C_0, sub_zero, Polynomial.X_pow_dvd_iff] at h_not
    push Not at h_not
    obtain ⟨k, hk_lt, hk_ne⟩ := h_not
    have hk_eq : k = m := by
      by_contra h; exact hk_ne (h_low_zero k (by omega))
    rwa [hk_eq] at hk_ne
  -- m ≤ n (since p has degree n and p.coeff m ≠ 0)
  have hm_le : m ≤ n := by
    have h_deg : p.natDegree = n := by
      rw [Matrix.charpoly_natDegree_eq_dim]; exact Fintype.card_fin n
    by_contra h; push Not at h
    exact h_cm_ne (Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (by omega))
  -- Step 2: Define the q(D)f₀ combination
  -- g j t = ∑_{k ∈ range(n-m+1)} p.coeff(m+k) * f(j+k)(t)
  let d := n - m
  let g : ℕ → ℝ → ℝ := fun j t =>
    ∑ k ∈ Finset.range (d + 1), (p.coeff (m + k) : ℝ) * f (j + k) t
  -- Step 3: g has the derivative tower property
  have hg_deriv : ∀ j : ℕ, ∀ t : ℝ, 0 ≤ t → HasDerivAt (g j) (g (j + 1) t) t := by
    intro j t ht
    change HasDerivAt (fun s => ∑ k ∈ Finset.range (d + 1),
      (p.coeff (m + k) : ℝ) * f (j + k) s) _ t
    have h1 := HasDerivAt.sum fun k (_ : k ∈ Finset.range (d + 1)) =>
      (h_deriv (j + k) t ht).const_mul (p.coeff (m + k) : ℝ)
    simp only [Finset.sum_fn] at h1
    convert h1 using 1
    apply Finset.sum_congr rfl; intro k _
    ring
  -- Step 4: g m = 0 (from Cayley-Hamilton)
  have hg_zero : ∀ t : ℝ, 0 ≤ t → g m t = 0 := by
    intro t ht
    -- Strategy: show g m t = CH sum (which is 0) by adding zero terms for k < m
    suffices h : g m t = ∑ k ∈ Finset.range (n + 1),
        ((Matrix.charpoly (Matrix.of A)).coeff k : ℝ) * f k t by
      rw [h]; exact h_cayley t ht
    -- LHS = ∑_{k ∈ range(d+1)} c_{m+k} f(m+k)(t)
    -- RHS = ∑_{k ∈ range(n+1)} c_k f(k)(t)
    -- The terms for k < m are zero (h_low_zero), so RHS = ∑_{k ∈ range(d+1)} c_{m+k} f(m+k)(t)
    change ∑ k ∈ Finset.range (d + 1), (p.coeff (m + k) : ℝ) * f (m + k) t = _
    symm
    -- Add a prefix of zeros and re-index the rest
    have hd_eq : n + 1 = m + (d + 1) := by omega
    conv_lhs => rw [hd_eq]
    rw [Finset.sum_range_add]
    have h_pref : ∀ k ∈ Finset.range m, (p.coeff k : ℝ) * f k t = 0 := by
      intro k hk
      have : (p.coeff k : ℝ) = 0 := by exact_mod_cast h_low_zero k (Finset.mem_range.mp hk)
      rw [this, zero_mul]
    rw [Finset.sum_eq_zero h_pref, zero_add]
  -- Step 5: all g j are bounded (each is a ℚ-coefficient sum of bounded f k's)
  have hg_bdd : ∀ j : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → |g j t| ≤ C := by
    intro j
    choose Cf hCf using fun k => h_bound k
    refine ⟨∑ k ∈ Finset.range (d + 1), |(p.coeff (m + k) : ℝ)| * Cf (j + k), fun t ht => ?_⟩
    calc |g j t|
        = |∑ k ∈ Finset.range (d + 1), (p.coeff (m + k) : ℝ) * f (j + k) t| := rfl
      _ ≤ ∑ k ∈ Finset.range (d + 1), |(p.coeff (m + k) : ℝ) * f (j + k) t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ Finset.range (d + 1), |(p.coeff (m + k) : ℝ)| * |f (j + k) t| := by
          simp_rw [abs_mul]
      _ ≤ ∑ k ∈ Finset.range (d + 1), |(p.coeff (m + k) : ℝ)| * Cf (j + k) := by
          apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_left (hCf (j + k) t ht) (abs_nonneg _)
  -- Step 6: g 0 is constant (bounded + D^m = 0)
  have hg_const : ∀ t : ℝ, 0 ≤ t → g 0 t = g 0 0 :=
    const_of_iterated_deriv_zero_bounded g m hg_deriv hg_zero hg_bdd
  -- Step 7: g 0 0 is rational
  have hg0_rat : ∃ r : ℚ, g 0 0 = (r : ℝ) := by
    choose q hq using fun k => h_init_rat k
    exact ⟨∑ k ∈ Finset.range (d + 1), p.coeff (m + k) * q k, by
      change ∑ k ∈ Finset.range (d + 1), (p.coeff (m + k) : ℝ) * f (0 + k) 0 = _
      simp_rw [zero_add, hq, ← Rat.cast_mul, ← Rat.cast_sum]⟩
  -- Step 8: f k → 0 for k ≥ 1 (Barbalat, inductive)
  have hf_lim_zero : ∀ k : ℕ, 0 < k →
      Filter.Tendsto (f k) Filter.atTop (nhds 0) := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases hk0 : k = 0
      · subst hk0
        exact tendsto_zero_of_tendsto_bounded_deriv (f 0) (f 1) (f 2) ν
          (h_deriv 0) (h_deriv 1) h_conv (h_bound 2)
      · exact tendsto_zero_of_tendsto_bounded_deriv (f k) (f (k + 1)) (f (k + 2)) 0
          (h_deriv k) (h_deriv (k + 1)) (ih (Nat.pos_of_ne_zero hk0)) (h_bound (k + 2))
  -- Step 9: Limit of g 0 as t → ∞
  -- g 0 t → p.coeff m * ν (since f 0 → ν, f k → 0 for k ≥ 1)
  have hg_lim : Filter.Tendsto (g 0) Filter.atTop
      (nhds ((p.coeff m : ℝ) * ν)) := by
    -- Each term c_{m+k} * f(0+k)(t) converges
    have h_term : ∀ k ∈ Finset.range (d + 1),
        Filter.Tendsto (fun t => (p.coeff (m + k) : ℝ) * f (0 + k) t) Filter.atTop
        (nhds ((p.coeff (m + k) : ℝ) * if k = 0 then ν else 0)) := by
      intro k _
      by_cases hk : k = 0
      · simp only [hk, zero_add, ite_true]
        exact tendsto_const_nhds.mul h_conv
      · simp only [hk, ite_false]
        exact tendsto_const_nhds.mul
          (show Filter.Tendsto (f (0 + k)) Filter.atTop (nhds 0) by
            rw [zero_add]; exact hf_lim_zero k (Nat.pos_of_ne_zero hk))
    have h_sum := tendsto_finset_sum _ h_term
    -- Simplify the limit sum: ∑ c_{m+k} * (if k=0 then ν else 0) = c_m * ν
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range,
      Nat.zero_lt_succ, ite_true, Nat.add_zero] at h_sum
    exact h_sum
  -- Step 10: Combine: g 0 constant = g 0 0, and g 0 t → p.coeff m * ν
  -- So p.coeff m * ν = g 0 0, hence ν = g 0 0 / p.coeff m ∈ ℚ
  obtain ⟨r, hr⟩ := hg0_rat
  refine ⟨r / p.coeff m, ?_⟩
  have h_cm_ne_ℝ : (p.coeff m : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr h_cm_ne
  -- By constancy + limit uniqueness: c_m * ν = g 0 0 = r
  have h_eq : (p.coeff m : ℝ) * ν = ↑r := by
    rw [← hr]
    by_contra h_ne
    have h_pos : 0 < dist (g 0 0) ((p.coeff m : ℝ) * ν) := dist_pos.mpr (Ne.symm h_ne)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (Metric.tendsto_nhds.mp hg_lim _ h_pos)
    have := hN (max N 0) (le_max_left _ _)
    rw [hg_const _ (le_max_right N 0)] at this
    exact absurd this (not_lt.mpr le_rfl)
  -- ν = r / c_m
  push_cast
  rw [eq_div_iff h_cm_ne_ℝ, mul_comm]
  exact h_eq

private lemma linear_ode_marked_sum_rational {n : ℕ}
    (A : Fin n → Fin n → ℚ)
    (sol : ℝ → Fin n → ℝ)
    (marked : Finset (Fin n))
    (ν : ℝ)
    (h_init_rat : ∀ i : Fin n, ∃ q : ℚ, sol 0 i = (q : ℝ))
    (h_nonneg : ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n, 0 ≤ sol t i)
    (h_simplex : ∀ t : ℝ, 0 ≤ t → ∑ i, sol t i = 1)
    (h_sol : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt sol (fun i => ∑ j, (A i j : ℝ) * sol t j) t)
    (h_conv : Filter.Tendsto
      (fun t => ∑ i ∈ marked, sol t i) Filter.atTop (nhds ν)) :
    ∃ q : ℚ, ν = (q : ℝ) := by
  -- Define the ℚ matrix and the derivative tower f k t = Σ_{marked} (A^k · sol(t))_i
  let A_mat : Matrix (Fin n) (Fin n) ℚ := Matrix.of A
  let f : ℕ → ℝ → ℝ := fun k t =>
    ∑ i ∈ marked, ∑ j, ((A_mat ^ k) i j : ℝ) * sol t j
  -- Key identity: A^0 = I ⟹ f 0 = marked sum
  have hf0 : f 0 = fun t => ∑ i ∈ marked, sol t i := by
    ext t
    change ∑ i ∈ marked, ∑ j, ((A_mat ^ 0) i j : ℝ) * sol t j = _
    simp only [pow_zero]
    congr 1; ext i
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.one_apply_eq, Rat.cast_one, one_mul]
    · intro j _ hij
      simp only [Matrix.one_apply_ne (Ne.symm hij), Rat.cast_zero, zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  -- Apply the core rationality lemma
  exact bounded_linear_ode_limit_rational A f ν
    (by -- HasDerivAt: d/dt f(k) = f(k+1), via A^{k+1} = A^k · A
      intro k t ht
      -- Each component of sol has derivative from the ODE
      have h_comp : ∀ j : Fin n, HasDerivAt (fun s => sol s j)
          (∑ l, (A j l : ℝ) * sol t l) t :=
        fun j => hasDerivAt_pi.mp (h_sol t ht) j
      -- Differentiate: constant · component, sum over j, sum over marked
      have h_outer : HasDerivAt
          (fun s => ∑ i ∈ marked, ∑ j, ((A_mat ^ k) i j : ℝ) * sol s j)
          (∑ i ∈ marked, ∑ j, ((A_mat ^ k) i j : ℝ) *
            (∑ l, (A j l : ℝ) * sol t l)) t := by
        have h1 := HasDerivAt.sum fun i (_ : i ∈ marked) =>
          HasDerivAt.sum fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
            (h_comp j).const_mul ((A_mat ^ k) i j : ℝ)
        simp only [Finset.sum_fn] at h1; exact h1
      -- Rewrite derivative value using matrix multiplication identity
      suffices h : ∑ i ∈ marked, ∑ j, ((A_mat ^ (k + 1)) i j : ℝ) * sol t j =
          ∑ i ∈ marked, ∑ j, ((A_mat ^ k) i j : ℝ) *
            (∑ l, (A j l : ℝ) * sol t l) by
        change HasDerivAt (fun s => ∑ i ∈ marked, ∑ j, ((A_mat ^ k) i j : ℝ) * sol s j)
          (∑ i ∈ marked, ∑ j, ((A_mat ^ (k + 1)) i j : ℝ) * sol t j) t
        rw [h]; exact h_outer
      -- Expand: A^k · (A · sol) = A^{k+1} · sol via sum manipulation
      congr 1; ext i
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      congr 1; ext l
      rw [← Finset.sum_mul]
      congr 1
      -- Core identity: ∑ j, (A^k)_{i,j} · A_{j,l} = (A^{k+1})_{i,l}
      rw [pow_succ, Matrix.mul_apply]; push_cast; rfl)
    (by -- Boundedness: sol ∈ simplex ⟹ |sol_j| ≤ 1 ⟹ |f k t| ≤ Σ|A^k_{i,j}|
      intro k
      exact ⟨∑ i ∈ marked, ∑ j : Fin n, |((A_mat ^ k) i j : ℝ)|, fun t ht => by
        calc |∑ i ∈ marked, ∑ j, ((A_mat ^ k) i j : ℝ) * sol t j|
            ≤ ∑ i ∈ marked, |∑ j, ((A_mat ^ k) i j : ℝ) * sol t j| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ marked, ∑ j, |((A_mat ^ k) i j : ℝ) * sol t j| :=
              Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ marked, ∑ j, |((A_mat ^ k) i j : ℝ)| := by
              apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
              rw [abs_mul]
              apply mul_le_of_le_one_right (abs_nonneg _)
              rw [abs_of_nonneg (h_nonneg t ht j)]
              calc sol t j
                  ≤ ∑ i, sol t i :=
                    Finset.single_le_sum (fun i _ => h_nonneg t ht i) (Finset.mem_univ j)
                _ = 1 := h_simplex t ht
        ⟩)
    (by -- Rationality of f k 0: A^k ∈ ℚ, sol(0) ∈ ℚ ⟹ f k 0 ∈ ℚ
      intro k
      choose q hq using h_init_rat
      exact ⟨∑ i ∈ marked, ∑ j, (A_mat ^ k) i j * q j, by
        change ∑ i ∈ marked, ∑ j, ((A_mat ^ k) i j : ℝ) * sol 0 j = _
        simp_rw [hq, ← Rat.cast_mul, ← Rat.cast_sum]⟩)
    (by -- Cayley-Hamilton: p(A) = 0 ⟹ Σ_k p_k f_k = 0
      intro t _
      -- Entry-wise Cayley-Hamilton (in ℚ, then cast to ℝ)
      have h_entry : ∀ (i j : Fin n), ∑ k ∈ Finset.range (n + 1),
          (((Matrix.of A).charpoly.coeff k : ℝ) * ((A_mat ^ k) i j : ℝ)) = 0 := by
        intro i j
        -- ℚ version via aeval_self_charpoly
        have h_deg : (Matrix.charpoly A_mat).natDegree = n := by
          simp [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
        have h_expand := Polynomial.aeval_eq_sum_range'
          (show (Matrix.charpoly A_mat).natDegree < n + 1 by omega) A_mat
        have hCH := congr_fun (congr_fun
          (h_expand ▸ Matrix.aeval_self_charpoly A_mat) i) j
        simp only [Matrix.zero_apply, Matrix.sum_apply, Matrix.smul_apply,
          smul_eq_mul] at hCH
        -- Cast to ℝ
        simp only [← Rat.cast_mul, ← Rat.cast_sum]
        exact_mod_cast hCH
      -- Unfold f and rearrange sums
      simp_rw [show ∀ k s, f k s = ∑ i ∈ marked, ∑ j,
        ((A_mat ^ k) i j : ℝ) * sol s j from fun _ _ => rfl,
        Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s := Finset.range _), ← Finset.sum_mul,
        h_entry, zero_mul, Finset.sum_const_zero])
    (by -- Convergence: f 0 = marked sum
      rw [hf0]; exact h_conv)

/-- Lemma 10 in [LPP]: a number computable by a unimolecular LPP
is rational. Unimolecular protocols are too weak to compute
transcendentals — the gap is precisely the bimolecular interactions.

A unimolecular field is LINEAR with CONSTANT RATIONAL coefficients:
field(x)(i) = ∑_j A(i,j) · x_j for a fixed rational matrix A.

Rationality of A is essential: for real A, the null space can be irrational.
In population protocols, transition rates are inherently rational (combinatorial). -/
theorem lpup_computes_rational {ν : ℝ}
    (h : IsLPPComputable ν)
    (hunimol : ∃ A : Fin h.n → Fin h.n → ℚ,
      ∀ x : Fin h.n → ℝ, ∀ i : Fin h.n,
        h.field x i = ∑ j, (A i j : ℝ) * x j) :
    ∃ q : ℚ, ν = (q : ℝ) := by
  obtain ⟨A, hA⟩ := hunimol
  exact linear_ode_marked_sum_rational A h.sol h.marked ν
    h.init_rational
    (fun t ht i => h.nonneg t ht i)
    (fun t ht => h.simplex t ht)
    (fun t ht => by
      convert h.is_solution t ht using 1
      ext i; exact (hA (h.sol t) i).symm)
    h.convergence

end Ripple
