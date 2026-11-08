/-
  Ripple.Core.BoundedTime — Bounded-Time Computability

  Defines time modulus and bounded-time complexity classes
  for bounded PIVPs.

  Key definition ([BAC] Def 2.1 + Def 2.3):
    A bounded PIVP y' = p(y), y(0) = y₀, with p a vector of polynomials with rational
    coefficients and y₀ ∈ ℚ^d, computes α with time modulus μ : ℕ → ℝ if
      |x(t) - α| < e^{-r}   whenever  t > μ(r).

  The time complexity of the computation is the asymptotic growth of μ(r).

  Growth classes of the modulus ([BAC] §5):
    real time:            μ(r) = O(r)        — e.g., e, π (`IsRealTimeComputable`)
    polynomial, degree n: μ(r) = O(rⁿ)       (`IsPolyTimeComputable α n`; n = 1 is real time)
    Lambert W:            μ(r) = Θ(r log r)
    Tower k:              μ(r) = Θ(exp^(k+1)(r))

  The paper predicates `IsCRNComputable`, `IsRealTimeComputable` and `IsPolyTimeComputable`
  are defined on `CertifiedBoundedTimeComputable`, whose system is a `PolyPIVP` (ℚ-polynomial
  field, ℚ initial value). The record `SemanticBTC` (arbitrary field, real initial value) is
  infrastructure only; it is not a paper notion, and no paper predicate unfolds to it.
-/

import Ripple.Core.PIVP
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.MvPolynomial.Rename

namespace Ripple

/-- A time modulus is a function μ : ℕ → ℝ such that μ(r) bounds the time
  needed to achieve r bits of precision. -/
def TimeModulus := ℕ → ℝ

/-- Semantic bounded-time record: a `PIVP` whose field is an arbitrary function
`(Fin d → ℝ) → (Fin d → ℝ)` and whose initial value is an arbitrary real vector, with a
bounded solution whose output converges to `α` with modulus `modulus`.

**This is not a paper notion.** Every real number has such a record (the constant system
`x' = 0`, `x(0) = α`), so no computability statement may be phrased with it. It is
infrastructure for constructions whose field is shown polynomial afterwards (for instance
`DualRail.btc_to_cbtc_pcd_of_unit_interval`, which takes an explicit ℚ-polynomial presentation
of the field and a zero initial value). The paper notion is
`CertifiedBoundedTimeComputable`. -/
structure SemanticBTC (d : ℕ) (α : ℝ) where
  /-- The underlying PIVP. -/
  pivp : PIVP d
  /-- The solution to the PIVP. -/
  sol : PIVP.Solution pivp
  /-- The time modulus. -/
  modulus : TimeModulus
  /-- The PIVP is bounded. -/
  bounded : pivp.IsBounded sol.trajectory
  /-- Convergence with the given time modulus. -/
  convergence : ∀ r : ℕ, ∀ t : ℝ, t > modulus r →
    |sol.trajectory t pivp.output - α| < Real.exp (-(r : ℝ))

/-- [BAC] Def 2.1 + Def 2.3: a bounded PIVP with ℚ-polynomial field and ℚ initial value
(`PolyPIVP`) whose designated output converges to `α` with time modulus `modulus`. -/
structure CertifiedBoundedTimeComputable (d : ℕ) (α : ℝ) where
  /-- The syntactic polynomial/rational PIVP. -/
  pivp : PolyPIVP d
  /-- A semantic solution of the associated ODE. -/
  sol : PIVP.Solution pivp.toPIVP
  /-- Time modulus. -/
  modulus : TimeModulus
  /-- Boundedness of the trajectory. -/
  bounded : pivp.toPIVP.IsBounded sol.trajectory
  /-- Continuity of the trajectory (derivable from Picard construction,
  materialized as a field so downstream consumers can use it without
  threading hypotheses). The `PIVP.Solution` bundle only guarantees
  `HasDerivAt` on `[0, ∞)`; this field extends to global continuity
  (with an arbitrary continuous extension at `t < 0` compatible with
  the value at `t = 0`). -/
  trajectory_continuous : Continuous sol.trajectory
  /-- Convergence to the target with the stated modulus. -/
  convergence : ∀ r : ℕ, ∀ t : ℝ, t > modulus r →
    |sol.trajectory t pivp.output - α| < Real.exp (-(r : ℝ))

/-- [BAC] Def 2.1 + Def 2.3: `α` is computed by a bounded PIVP with ℚ-polynomial field and
ℚ initial value, with some time modulus. For `α ∈ [0, 1]` such a system can be turned into a
mass-action CRN with the same limit (`DualRail.btc_to_cbtc_pcd_of_unit_interval`, [BAC] §7);
the name follows that usage. -/
def IsCRNComputable (α : ℝ) : Prop :=
  ∃ d : ℕ, Nonempty (CertifiedBoundedTimeComputable d α)

/-- Real-time computability: a computation in the sense of `IsCRNComputable` with a linear
time modulus, `μ(r) ≤ C(r+1)`. This is the class `R_RTGPAC` of [RTCRN2] §3 in the modulus
form; `isRealTimeComputable_iff_rtgpac` (`Ripple.Core.RealTimeGPAC`) proves it equal to the
paper-literal class (zero initial values, integer coefficients, error `≤ 2^{-t}` for `t ≥ 1`). -/
def IsRealTimeComputable (α : ℝ) : Prop :=
  ∃ d : ℕ, ∃ btc : CertifiedBoundedTimeComputable d α,
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, btc.modulus r ≤ C * (↑r + 1)

/-- Polynomial time of degree `n` ([BAC] §5): a computation in the sense of `IsCRNComputable`
with time modulus `μ(r) ≤ C(r+1)ⁿ` (`n = 1` is real time). -/
def IsPolyTimeComputable (α : ℝ) (n : ℕ) : Prop :=
  ∃ d : ℕ, ∃ btc : CertifiedBoundedTimeComputable d α,
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, btc.modulus r ≤ C * (↑r + 1) ^ n

/-- Forget the syntactic certificate and keep the semantic record (infrastructure). -/
noncomputable def CertifiedBoundedTimeComputable.toSemantic
    {d : ℕ} {α : ℝ} (btc : CertifiedBoundedTimeComputable d α) :
    SemanticBTC d α where
  pivp := btc.pivp.toPIVP
  sol := btc.sol
  modulus := btc.modulus
  bounded := btc.bounded
  convergence := btc.convergence

/-- The convergence condition of SemanticBTC implies Filter.Tendsto.
This converts the quantitative bound |sol(t) - α| < e^{-r} for t > μ(r)
into the topological statement sol(t) → α as t → ∞. -/
theorem SemanticBTC.to_tendsto {d : ℕ} {α : ℝ}
    (btc : SemanticBTC d α) :
    Filter.Tendsto (fun t => btc.sol.trajectory t btc.pivp.output)
      Filter.atTop (nhds α) := by
  rw [Metric.tendsto_atTop']
  intro ε hε
  -- Find r : ℕ such that exp(-r) < ε
  have h_exp : ∃ r : ℕ, Real.exp (-(r : ℝ)) < ε := by
    obtain ⟨n, hn⟩ := exists_nat_gt (-Real.log ε)
    exact ⟨n, by rwa [← Real.lt_log_iff_exp_lt hε, neg_lt]⟩
  obtain ⟨r, hr⟩ := h_exp
  exact ⟨btc.modulus r, fun t ht => by
    calc dist (btc.sol.trajectory t btc.pivp.output) α
        = |btc.sol.trajectory t btc.pivp.output - α| := Real.dist_eq _ _
      _ < Real.exp (-(r : ℝ)) := btc.convergence r t ht
      _ < ε := hr⟩

/-- The output of a certified computation converges to its target. -/
theorem CertifiedBoundedTimeComputable.to_tendsto {d : ℕ} {α : ℝ}
    (btc : CertifiedBoundedTimeComputable d α) :
    Filter.Tendsto (fun t => btc.sol.trajectory t btc.pivp.output)
      Filter.atTop (nhds α) :=
  btc.toSemantic.to_tendsto

/-- [BAC] Def 2.3, the modulus exists: a bounded `PolyPIVP` solution with continuous
trajectory whose output converges to `α` is a certified computation of `α`. The modulus is
read off the limit (for each `r`, a time after which the output is `e^{-r}`-close). -/
theorem CertifiedBoundedTimeComputable.exists_of_tendsto {d : ℕ} {α : ℝ}
    (P : PolyPIVP d) (sol : PIVP.Solution P.toPIVP)
    (hbd : P.toPIVP.IsBounded sol.trajectory) (hcont : Continuous sol.trajectory)
    (hlim : Filter.Tendsto (fun t => sol.trajectory t P.output) Filter.atTop (nhds α)) :
    ∃ btc : CertifiedBoundedTimeComputable d α,
      btc.pivp = P ∧ btc.sol.trajectory = sol.trajectory := by
  have hmod : ∀ r : ℕ, ∃ T : ℝ, ∀ t : ℝ, t > T →
      |sol.trajectory t P.output - α| < Real.exp (-(r : ℝ)) := by
    intro r
    obtain ⟨T, hT⟩ := (Metric.tendsto_atTop'.mp hlim) (Real.exp (-(r : ℝ))) (Real.exp_pos _)
    exact ⟨T, fun t ht => by simpa [Real.dist_eq] using hT t ht⟩
  choose mod hmod_spec using hmod
  refine ⟨{
    pivp := P
    sol := sol
    modulus := mod
    bounded := hbd
    trajectory_continuous := hcont
    convergence := hmod_spec }, rfl, rfl⟩

/-- `IsCRNComputable` from a bounded convergent `PolyPIVP` solution ([BAC] Def 2.3). -/
theorem isCRNComputable_of_tendsto {d : ℕ} {α : ℝ}
    (P : PolyPIVP d) (sol : PIVP.Solution P.toPIVP)
    (hbd : P.toPIVP.IsBounded sol.trajectory) (hcont : Continuous sol.trajectory)
    (hlim : Filter.Tendsto (fun t => sol.trajectory t P.output) Filter.atTop (nhds α)) :
    IsCRNComputable α := by
  obtain ⟨btc, -, -⟩ := CertifiedBoundedTimeComputable.exists_of_tendsto P sol hbd hcont hlim
  exact ⟨d, ⟨btc⟩⟩

/-- A semantic record whose field, initial value and output are those of a `PolyPIVP` `P`,
and whose trajectory is continuous, is a certified computation with the same trajectory and
modulus. The hypotheses carry the whole syntactic content (`hfield` says the field is the
evaluated ℚ-polynomial field of `P`, `hinit` that the initial value is `P`'s rational one). -/
noncomputable def SemanticBTC.certify {d : ℕ} {α : ℝ} (b : SemanticBTC d α) (P : PolyPIVP d)
    (hfield : ∀ x, P.evalField x = b.pivp.field x)
    (hinit : ∀ i, (P.init i : ℝ) = b.pivp.init i) (hout : P.output = b.pivp.output)
    (hcont : Continuous b.sol.trajectory) : CertifiedBoundedTimeComputable d α where
  pivp := P
  sol := {
    trajectory := b.sol.trajectory
    init_cond := by
      funext i
      rw [b.sol.init_cond]
      exact (hinit i).symm
    is_solution := fun t ht => by
      change HasDerivAt b.sol.trajectory (P.evalField (b.sol.trajectory t)) t
      rw [hfield]
      exact b.sol.is_solution t ht }
  modulus := b.modulus
  bounded := b.bounded
  trajectory_continuous := hcont
  convergence := by
    intro r t ht
    rw [hout]
    exact b.convergence r t ht

@[simp] theorem SemanticBTC.certify_modulus {d : ℕ} {α : ℝ} (b : SemanticBTC d α)
    (P : PolyPIVP d) (hfield : ∀ x, P.evalField x = b.pivp.field x)
    (hinit : ∀ i, (P.init i : ℝ) = b.pivp.init i) (hout : P.output = b.pivp.output)
    (hcont : Continuous b.sol.trajectory) :
    (b.certify P hfield hinit hout hcont).modulus = b.modulus := rfl

@[simp] theorem SemanticBTC.certify_pivp {d : ℕ} {α : ℝ} (b : SemanticBTC d α)
    (P : PolyPIVP d) (hfield : ∀ x, P.evalField x = b.pivp.field x)
    (hinit : ∀ i, (P.init i : ℝ) = b.pivp.init i) (hout : P.output = b.pivp.output)
    (hcont : Continuous b.sol.trajectory) :
    (b.certify P hfield hinit hout hcont).pivp = P := rfl

@[simp] theorem SemanticBTC.certify_trajectory {d : ℕ} {α : ℝ} (b : SemanticBTC d α)
    (P : PolyPIVP d) (hfield : ∀ x, P.evalField x = b.pivp.field x)
    (hinit : ∀ i, (P.init i : ℝ) = b.pivp.init i) (hout : P.output = b.pivp.output)
    (hcont : Continuous b.sol.trajectory) :
    (b.certify P hfield hinit hout hcont).sol.trajectory = b.sol.trajectory := rfl

/-- Clamped extension of a solution. If `y` solves `y' = F(y)` at every `t > -δ` (`δ > 0`),
then `t ↦ y (max t (-δ/2))` is continuous on all of `ℝ`, equals `y` on `[0, ∞)`, and solves
`y' = F(y)` at every `t ≥ 0`. Used to supply the global `trajectory_continuous` field for
closed-form solutions that are only defined (or only smooth) near `[0, ∞)`. -/
theorem hasDerivAt_clamp_extension {d : ℕ} {F : (Fin d → ℝ) → Fin d → ℝ}
    {y : ℝ → Fin d → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hy : ∀ t, -δ < t → HasDerivAt y (F (y t)) t) :
    Continuous (fun t => y (max t (-(δ / 2)))) ∧
      (∀ t, 0 ≤ t → y (max t (-(δ / 2))) = y t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (fun s => y (max s (-(δ / 2)))) (F (y t)) t) := by
  have hcont : ContinuousOn y (Set.Ioi (-δ)) := fun t ht =>
    (hy t ht).continuousAt.continuousWithinAt
  refine ⟨?_, ?_, ?_⟩
  · exact hcont.comp_continuous (continuous_id.max continuous_const)
      (fun t => show -δ < max t (-(δ / 2)) from
        lt_of_lt_of_le (by linarith) (le_max_right _ _))
  · intro t ht
    rw [max_eq_left (by linarith)]
  · intro t ht
    have hEv : (fun s => y (max s (-(δ / 2)))) =ᶠ[nhds t] y := by
      have hopen : IsOpen {s : ℝ | -(δ / 2) < s} := isOpen_lt continuous_const continuous_id
      refine Filter.eventuallyEq_of_mem (hopen.mem_nhds (show -(δ / 2) < t by linarith)) ?_
      intro s (hs : -(δ / 2) < s)
      simp only [max_eq_left hs.le]
    exact (hy t (by linarith)).congr_of_eventuallyEq hEv

/-- Every solution can be re-chosen for `t < 0` (linearly: `y(0) + t·F(y(0))`) to a solution
with globally continuous trajectory that agrees with it on `[0, ∞)`. So the
`trajectory_continuous` field of `CertifiedBoundedTimeComputable` never restricts which numbers
are computed. -/
theorem PIVP.Solution.exists_continuous {d : ℕ} {P : PIVP d} (sol : PIVP.Solution P) :
    ∃ sol' : PIVP.Solution P, Continuous sol'.trajectory ∧
      ∀ t, 0 ≤ t → sol'.trajectory t = sol.trajectory t := by
  set y := sol.trajectory with hy_def
  set v := P.field (y 0) with hv_def
  let z : ℝ → Fin d → ℝ := fun t => if 0 ≤ t then y t else y 0 + t • v
  have hz_pos : ∀ t, 0 ≤ t → z t = y t := fun t ht => if_pos ht
  have hz_neg : ∀ t, t ≤ 0 → z t = y 0 + t • v := by
    intro t ht
    by_cases h : 0 ≤ t
    · have h0 : t = 0 := le_antisymm ht h
      subst h0
      simp [z]
    · simp [z, h]
  have hlin : ∀ s : ℝ, HasDerivAt (fun t : ℝ => y 0 + t • v) v s := by
    intro s
    simpa using ((hasDerivAt_id s).smul_const v).const_add (y 0)
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt z (P.field (z t)) t := by
    intro t ht
    rcases ht.lt_or_eq with htpos | ht0
    · have hEv : z =ᶠ[nhds t] y :=
        Filter.eventuallyEq_of_mem (Ioi_mem_nhds htpos) (fun s hs => hz_pos s (le_of_lt hs))
      rw [hz_pos t ht]
      exact (sol.is_solution t ht).congr_of_eventuallyEq hEv
    · subst ht0
      rw [hz_pos 0 le_rfl]
      have h1 : HasDerivWithinAt z v (Set.Ici 0) 0 :=
        (sol.is_solution 0 le_rfl).hasDerivWithinAt.congr (fun s hs => hz_pos s hs)
          (hz_pos 0 le_rfl)
      have h2 : HasDerivWithinAt z v (Set.Iic 0) 0 :=
        (hlin 0).hasDerivWithinAt.congr (fun s hs => hz_neg s hs) (hz_neg 0 le_rfl)
      have h3 := h2.union h1
      rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at h3
      exact h3
  have hcont : Continuous z := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    by_cases ht : 0 ≤ t
    · exact (hderiv t ht).continuousAt
    · have hEv : (fun t : ℝ => y 0 + t • v) =ᶠ[nhds t] z :=
        Filter.eventuallyEq_of_mem (Iio_mem_nhds (lt_of_not_ge ht))
          (fun s hs => (hz_neg s (le_of_lt hs)).symm)
      exact (hlin t).continuousAt.congr hEv
  refine ⟨{
    trajectory := z
    init_cond := by
      rw [hz_pos 0 le_rfl]
      exact sol.init_cond
    is_solution := hderiv }, hcont, hz_pos⟩

/-- [BAC] Def 2.3 from a bounded `PolyPIVP` solution with a modulus: the certified record, with
the solution re-chosen on `t < 0` (`PIVP.Solution.exists_continuous`) and the modulus clipped at
`0`. -/
theorem CertifiedBoundedTimeComputable.exists_of_solution {d : ℕ} {α : ℝ}
    (P : PolyPIVP d) (sol : PIVP.Solution P.toPIVP)
    (hbd : P.toPIVP.IsBounded sol.trajectory) (modulus : TimeModulus)
    (hconv : ∀ r : ℕ, ∀ t : ℝ, t > modulus r →
      |sol.trajectory t P.output - α| < Real.exp (-(r : ℝ))) :
    ∃ btc : CertifiedBoundedTimeComputable d α,
      btc.pivp = P ∧ (∀ r, btc.modulus r = max 0 (modulus r)) ∧
      ∀ t, 0 ≤ t → btc.sol.trajectory t = sol.trajectory t := by
  obtain ⟨sol', hcont, heq⟩ := sol.exists_continuous
  refine ⟨{
    pivp := P
    sol := sol'
    modulus := fun r => max 0 (modulus r)
    bounded := ?_
    trajectory_continuous := hcont
    convergence := ?_ }, rfl, fun _ => rfl, heq⟩
  · obtain ⟨M, hM, hb⟩ := hbd
    exact ⟨M, hM, fun t ht => by rw [heq t ht]; exact hb t ht⟩
  · intro r t ht
    have ht0 : 0 ≤ t := le_of_lt (lt_of_le_of_lt (le_max_left _ _) ht)
    rw [heq t ht0]
    exact hconv r t (lt_of_le_of_lt (le_max_right _ _) ht)

/-- A real-time computation is a computation. -/
theorem IsRealTimeComputable.isCRNComputable {α : ℝ} (h : IsRealTimeComputable α) :
    IsCRNComputable α := by
  obtain ⟨d, btc, -⟩ := h
  exact ⟨d, ⟨btc⟩⟩

/-! ## Parallel composition of `PolyPIVP`s

The closure constructions of [RTCRN2] Lemmas 5-6 run two systems side by side and add one
tracker coordinate. On the syntactic side the two fields are renamed into the disjoint union
`Fin (d₁ + d₂ + 1)`; `parallel_evalField` says that the evaluated field is the pair of
evaluated fields plus the tracker. -/

namespace PolyPIVP

/-- The semantic field of a `PolyPIVP` is its evaluated polynomial field. -/
theorem toPIVP_field_eq {d : ℕ} (P : PolyPIVP d) : P.toPIVP.field = P.evalField := rfl

/-- Embedding of the first block into `Fin (d₁ + d₂ + 1)`. -/
def leftEmb (d₁ d₂ : ℕ) (j : Fin d₁) : Fin (d₁ + d₂ + 1) :=
  Fin.castSucc (Fin.castAdd d₂ j)

/-- Embedding of the second block into `Fin (d₁ + d₂ + 1)`. -/
def rightEmb (d₁ d₂ : ℕ) (j : Fin d₂) : Fin (d₁ + d₂ + 1) :=
  Fin.castSucc (Fin.natAdd d₁ j)

@[simp] theorem snoc_append_leftEmb {d₁ d₂ : ℕ} {β : Type*} (x₁ : Fin d₁ → β)
    (x₂ : Fin d₂ → β) (z : β) (j : Fin d₁) :
    (Fin.snoc (Fin.append x₁ x₂) z : Fin (d₁ + d₂ + 1) → β) (leftEmb d₁ d₂ j) = x₁ j := by
  simp only [leftEmb, Fin.snoc_castSucc, Fin.append_left]

@[simp] theorem snoc_append_rightEmb {d₁ d₂ : ℕ} {β : Type*} (x₁ : Fin d₁ → β)
    (x₂ : Fin d₂ → β) (z : β) (j : Fin d₂) :
    (Fin.snoc (Fin.append x₁ x₂) z : Fin (d₁ + d₂ + 1) → β) (rightEmb d₁ d₂ j) = x₂ j := by
  simp only [rightEmb, Fin.snoc_castSucc, Fin.append_right]

theorem snoc_append_comp_leftEmb {d₁ d₂ : ℕ} {β : Type*} (x₁ : Fin d₁ → β)
    (x₂ : Fin d₂ → β) (z : β) :
    (Fin.snoc (Fin.append x₁ x₂) z : Fin (d₁ + d₂ + 1) → β) ∘ leftEmb d₁ d₂ = x₁ :=
  funext fun j => snoc_append_leftEmb x₁ x₂ z j

theorem snoc_append_comp_rightEmb {d₁ d₂ : ℕ} {β : Type*} (x₁ : Fin d₁ → β)
    (x₂ : Fin d₂ → β) (z : β) :
    (Fin.snoc (Fin.append x₁ x₂) z : Fin (d₁ + d₂ + 1) → β) ∘ rightEmb d₁ d₂ = x₂ :=
  funext fun j => snoc_append_rightEmb x₁ x₂ z j

/-- Two `PolyPIVP`s side by side plus one tracker coordinate with polynomial field `tracker`
and rational initial value `z₀`; the output is the tracker. -/
noncomputable def parallel {d₁ d₂ : ℕ} (P₁ : PolyPIVP d₁) (P₂ : PolyPIVP d₂)
    (tracker : MvPolynomial (Fin (d₁ + d₂ + 1)) ℚ) (z₀ : ℚ) : PolyPIVP (d₁ + d₂ + 1) where
  field := Fin.snoc
    (Fin.append (fun j => MvPolynomial.rename (leftEmb d₁ d₂) (P₁.field j))
      (fun j => MvPolynomial.rename (rightEmb d₁ d₂) (P₂.field j))) tracker
  init := Fin.snoc (Fin.append P₁.init P₂.init) z₀
  output := Fin.last (d₁ + d₂)

@[simp] theorem parallel_output {d₁ d₂ : ℕ} (P₁ : PolyPIVP d₁) (P₂ : PolyPIVP d₂)
    (tracker : MvPolynomial (Fin (d₁ + d₂ + 1)) ℚ) (z₀ : ℚ) :
    (parallel P₁ P₂ tracker z₀).output = Fin.last (d₁ + d₂) := rfl

/-- The evaluated field of `parallel` on a joined state. -/
theorem parallel_evalField {d₁ d₂ : ℕ} (P₁ : PolyPIVP d₁) (P₂ : PolyPIVP d₂)
    (tracker : MvPolynomial (Fin (d₁ + d₂ + 1)) ℚ) (z₀ : ℚ)
    (x₁ : Fin d₁ → ℝ) (x₂ : Fin d₂ → ℝ) (z : ℝ) :
    (parallel P₁ P₂ tracker z₀).evalField (Fin.snoc (Fin.append x₁ x₂) z) =
      (Fin.snoc (Fin.append (P₁.evalField x₁) (P₂.evalField x₂))
        (tracker.eval₂ (Rat.castHom ℝ) (Fin.snoc (Fin.append x₁ x₂) z)) :
          Fin (d₁ + d₂ + 1) → ℝ) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [evalField, parallel, Fin.snoc_last]
  · refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
    · simp only [evalField, parallel, Fin.snoc_castSucc, Fin.append_left,
        MvPolynomial.eval₂_rename, snoc_append_comp_leftEmb]
    · simp only [evalField, parallel, Fin.snoc_castSucc, Fin.append_right,
        MvPolynomial.eval₂_rename, snoc_append_comp_rightEmb]

/-- The real initial value of `parallel` is the joined initial value. -/
theorem parallel_toPIVP_init {d₁ d₂ : ℕ} (P₁ : PolyPIVP d₁) (P₂ : PolyPIVP d₂)
    (tracker : MvPolynomial (Fin (d₁ + d₂ + 1)) ℚ) (z₀ : ℚ) :
    (parallel P₁ P₂ tracker z₀).toPIVP.init =
      (Fin.snoc (Fin.append P₁.toPIVP.init P₂.toPIVP.init) (z₀ : ℝ) :
        Fin (d₁ + d₂ + 1) → ℝ) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [toPIVP_init, parallel, Fin.snoc_last]
  · refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
    · simp only [toPIVP_init, parallel, Fin.snoc_castSucc, Fin.append_left]
    · simp only [toPIVP_init, parallel, Fin.snoc_castSucc, Fin.append_right]

end PolyPIVP

/-- The joined trajectory of two continuous trajectories and a continuous tracker is
continuous. -/
theorem continuous_snoc_append {d₁ d₂ : ℕ} {x₁ : ℝ → Fin d₁ → ℝ} {x₂ : ℝ → Fin d₂ → ℝ}
    {z : ℝ → ℝ} (h₁ : Continuous x₁) (h₂ : Continuous x₂) (hz : Continuous z) :
    Continuous (fun t => (Fin.snoc (Fin.append (x₁ t) (x₂ t)) (z t) :
      Fin (d₁ + d₂ + 1) → ℝ)) := by
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    exact hz
  · refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
    · simp only [Fin.snoc_castSucc, Fin.append_left]
      exact (continuous_apply j₁).comp h₁
    · simp only [Fin.snoc_castSucc, Fin.append_right]
      exact (continuous_apply j₂).comp h₂

namespace CertifiedBoundedTimeComputable

/-- Sum tracker ([RTCRN2] Lemma 5): run `c₁` and `c₂` side by side and add `z` with
`z' = p₁,out(x₁) + p₂,out(x₂)`, `z(0) = x₁,out(0) + x₂,out(0)`, so that `z = x₁,out + x₂,out`.
The field is the renamed input fields plus their sum, the initial value is rational. -/
theorem exists_add {d₁ d₂ : ℕ} {α β : ℝ} (c₁ : CertifiedBoundedTimeComputable d₁ α)
    (c₂ : CertifiedBoundedTimeComputable d₂ β) :
    ∃ c : CertifiedBoundedTimeComputable (d₁ + d₂ + 1) (α + β),
      ∀ r, c.modulus r = max (c₁.modulus (r + 1)) (c₂.modulus (r + 1)) := by
  refine ⟨{
    pivp := PolyPIVP.parallel c₁.pivp c₂.pivp
      (MvPolynomial.rename (PolyPIVP.leftEmb d₁ d₂) (c₁.pivp.field c₁.pivp.output) +
        MvPolynomial.rename (PolyPIVP.rightEmb d₁ d₂) (c₂.pivp.field c₂.pivp.output))
      (c₁.pivp.init c₁.pivp.output + c₂.pivp.init c₂.pivp.output)
    sol := {
      trajectory := fun t =>
        Fin.snoc (Fin.append (c₁.sol.trajectory t) (c₂.sol.trajectory t))
          (c₁.sol.trajectory t c₁.pivp.output + c₂.sol.trajectory t c₂.pivp.output)
      init_cond := ?_
      is_solution := ?_ }
    modulus := fun r => max (c₁.modulus (r + 1)) (c₂.modulus (r + 1))
    bounded := ?_
    trajectory_continuous := ?_
    convergence := ?_ }, fun r => rfl⟩
  · -- initial value
    simp only [PolyPIVP.parallel_toPIVP_init, c₁.sol.init_cond, c₂.sol.init_cond,
      PolyPIVP.toPIVP_init, Rat.cast_add]
  · -- the ODE
    intro t ht
    have hd₁ := hasDerivAt_pi.mp (c₁.sol.is_solution t ht)
    have hd₂ := hasDerivAt_pi.mp (c₂.sol.is_solution t ht)
    simp only [PolyPIVP.toPIVP_field_eq, PolyPIVP.parallel_evalField]
    refine hasDerivAt_pi.mpr fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, MvPolynomial.eval₂_add, MvPolynomial.eval₂_rename,
        PolyPIVP.snoc_append_comp_leftEmb, PolyPIVP.snoc_append_comp_rightEmb]
      exact (hd₁ c₁.pivp.output).add (hd₂ c₂.pivp.output)
    · refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
      · simp only [Fin.snoc_castSucc, Fin.append_left]
        exact hd₁ j₁
      · simp only [Fin.snoc_castSucc, Fin.append_right]
        exact hd₂ j₂
  · -- Bounded: all components bounded by M₁ + M₂
    obtain ⟨M₁, hM₁, hb₁⟩ := c₁.bounded
    obtain ⟨M₂, hM₂, hb₂⟩ := c₂.bounded
    refine ⟨M₁ + M₂, by linarith, fun t ht => ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by linarith)]
    refine Fin.lastCases ?_ (fun j => ?_)
    · -- Sum component
      simp only [Fin.snoc_last]
      rw [Real.norm_eq_abs]
      have h₁ : |c₁.sol.trajectory t c₁.pivp.output| ≤ M₁ := by
        have hcomp := norm_le_pi_norm (c₁.sol.trajectory t) c₁.pivp.output
        rw [Real.norm_eq_abs] at hcomp; linarith [hb₁ t ht]
      have h₂ : |c₂.sol.trajectory t c₂.pivp.output| ≤ M₂ := by
        have hcomp := norm_le_pi_norm (c₂.sol.trajectory t) c₂.pivp.output
        rw [Real.norm_eq_abs] at hcomp; linarith [hb₂ t ht]
      linarith [abs_add_le (c₁.sol.trajectory t c₁.pivp.output)
                           (c₂.sol.trajectory t c₂.pivp.output)]
    · -- Sub-PIVP components
      refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
      · simp only [Fin.snoc_castSucc, Fin.append_left]
        calc ‖c₁.sol.trajectory t j₁‖
            ≤ ‖c₁.sol.trajectory t‖ := norm_le_pi_norm _ _
          _ ≤ M₁ := hb₁ t ht
          _ ≤ M₁ + M₂ := le_add_of_nonneg_right (le_of_lt hM₂)
      · simp only [Fin.snoc_castSucc, Fin.append_right]
        calc ‖c₂.sol.trajectory t j₂‖
            ≤ ‖c₂.sol.trajectory t‖ := norm_le_pi_norm _ _
          _ ≤ M₂ := hb₂ t ht
          _ ≤ M₁ + M₂ := le_add_of_nonneg_left (le_of_lt hM₁)
  · -- continuity
    exact continuous_snoc_append c₁.trajectory_continuous c₂.trajectory_continuous
      (((continuous_apply c₁.pivp.output).comp c₁.trajectory_continuous).add
        ((continuous_apply c₂.pivp.output).comp c₂.trajectory_continuous))
  · -- Convergence: triangle inequality + 2e^{-(r+1)} ≤ e^{-r}
    intro r t ht
    simp only [PolyPIVP.parallel_output, Fin.snoc_last]
    have ht₁ : t > c₁.modulus (r + 1) := lt_of_le_of_lt (le_max_left _ _) ht
    have ht₂ : t > c₂.modulus (r + 1) := lt_of_le_of_lt (le_max_right _ _) ht
    have hc₁ := c₁.convergence (r + 1) t ht₁
    have hc₂ := c₂.convergence (r + 1) t ht₂
    have htri : |c₁.sol.trajectory t c₁.pivp.output +
        c₂.sol.trajectory t c₂.pivp.output - (α + β)|
      ≤ |c₁.sol.trajectory t c₁.pivp.output - α| +
        |c₂.sol.trajectory t c₂.pivp.output - β| := by
      have : c₁.sol.trajectory t c₁.pivp.output +
          c₂.sol.trajectory t c₂.pivp.output - (α + β) =
          (c₁.sol.trajectory t c₁.pivp.output - α) +
          (c₂.sol.trajectory t c₂.pivp.output - β) := by ring
      rw [this]; exact abs_add_le _ _
    have hexp : 2 * Real.exp (-(↑(r + 1) : ℝ)) ≤ Real.exp (-(↑r : ℝ)) := by
      have hcast : (-(↑(r + 1) : ℝ)) = -(↑r : ℝ) + (-1 : ℝ) := by push_cast; ring
      rw [hcast, Real.exp_add]
      have h2e : 2 * Real.exp (-1 : ℝ) ≤ 1 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos 1)]
        linarith [Real.add_one_le_exp (1 : ℝ)]
      calc 2 * (Real.exp (-(↑r : ℝ)) * Real.exp (-1))
          = Real.exp (-(↑r : ℝ)) * (2 * Real.exp (-1)) := by ring
        _ ≤ Real.exp (-(↑r : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left h2e (le_of_lt (Real.exp_pos _))
        _ = Real.exp (-(↑r : ℝ)) := mul_one _
    linarith

/-- Product tracker ([RTCRN2] Lemma 6): run `c₁` and `c₂` side by side and add `z` with
`z' = p₁,out(x₁)·x₂,out + x₁,out·p₂,out(x₂)`, `z(0) = x₁,out(0)·x₂,out(0)`, so that
`z = x₁,out·x₂,out`. The modulus is shifted by a constant `K` that absorbs the bounds. -/
theorem exists_mul {d₁ d₂ : ℕ} {α β : ℝ} (c₁ : CertifiedBoundedTimeComputable d₁ α)
    (c₂ : CertifiedBoundedTimeComputable d₂ β) :
    ∃ c : CertifiedBoundedTimeComputable (d₁ + d₂ + 1) (α * β), ∃ K : ℕ,
      ∀ r, c.modulus r = max 0 (max (c₁.modulus (r + K)) (c₂.modulus (r + K))) := by
  obtain ⟨M₁, hM₁, hb₁⟩ := c₁.bounded
  obtain ⟨M₂, hM₂, hb₂⟩ := c₂.bounded
  -- K : ℕ with e^K > M₁+M₂+1 (via 1+x ≤ e^x)
  set K := Nat.ceil (M₁ + M₂ + 1) with hK_def
  have hK : M₁ + M₂ + 1 ≤ (↑K : ℝ) := Nat.le_ceil _
  have hexp_K : M₁ + M₂ + 1 < Real.exp (↑K : ℝ) :=
    calc M₁ + M₂ + 1 ≤ (↑K : ℝ) := hK
      _ < (↑K : ℝ) + 1 := by linarith
      _ ≤ Real.exp (↑K : ℝ) := Real.add_one_le_exp _
  -- Component bound helpers
  have hx₁_bound : ∀ t, 0 ≤ t → |c₁.sol.trajectory t c₁.pivp.output| ≤ M₁ := by
    intro t ht
    have := norm_le_pi_norm (c₁.sol.trajectory t) c₁.pivp.output
    rw [Real.norm_eq_abs] at this; linarith [hb₁ t ht]
  have hx₂_bound : ∀ t, 0 ≤ t → |c₂.sol.trajectory t c₂.pivp.output| ≤ M₂ := by
    intro t ht
    have := norm_le_pi_norm (c₂.sol.trajectory t) c₂.pivp.output
    rw [Real.norm_eq_abs] at this; linarith [hb₂ t ht]
  refine ⟨{
    pivp := PolyPIVP.parallel c₁.pivp c₂.pivp
      (MvPolynomial.rename (PolyPIVP.leftEmb d₁ d₂) (c₁.pivp.field c₁.pivp.output) *
          MvPolynomial.X (PolyPIVP.rightEmb d₁ d₂ c₂.pivp.output) +
        MvPolynomial.X (PolyPIVP.leftEmb d₁ d₂ c₁.pivp.output) *
          MvPolynomial.rename (PolyPIVP.rightEmb d₁ d₂) (c₂.pivp.field c₂.pivp.output))
      (c₁.pivp.init c₁.pivp.output * c₂.pivp.init c₂.pivp.output)
    sol := {
      trajectory := fun t =>
        Fin.snoc (Fin.append (c₁.sol.trajectory t) (c₂.sol.trajectory t))
          (c₁.sol.trajectory t c₁.pivp.output * c₂.sol.trajectory t c₂.pivp.output)
      init_cond := ?_
      is_solution := ?_ }
    modulus := fun r => max 0 (max (c₁.modulus (r + K)) (c₂.modulus (r + K)))
    bounded := ?_
    trajectory_continuous := ?_
    convergence := ?_ }, K, fun r => rfl⟩
  · -- initial value
    simp only [PolyPIVP.parallel_toPIVP_init, c₁.sol.init_cond, c₂.sol.init_cond,
      PolyPIVP.toPIVP_init, Rat.cast_mul]
  · -- the ODE (product rule)
    intro t ht
    have hd₁ := hasDerivAt_pi.mp (c₁.sol.is_solution t ht)
    have hd₂ := hasDerivAt_pi.mp (c₂.sol.is_solution t ht)
    simp only [PolyPIVP.toPIVP_field_eq, PolyPIVP.parallel_evalField]
    refine hasDerivAt_pi.mpr fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X, MvPolynomial.eval₂_rename, PolyPIVP.snoc_append_comp_leftEmb,
        PolyPIVP.snoc_append_comp_rightEmb, PolyPIVP.snoc_append_leftEmb,
        PolyPIVP.snoc_append_rightEmb]
      exact (hd₁ c₁.pivp.output).mul (hd₂ c₂.pivp.output)
    · refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
      · simp only [Fin.snoc_castSucc, Fin.append_left]
        exact hd₁ j₁
      · simp only [Fin.snoc_castSucc, Fin.append_right]
        exact hd₂ j₂
  · -- Bounded
    refine ⟨M₁ * M₂ + M₁ + M₂, by positivity, fun t ht => ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    refine Fin.lastCases ?_ (fun j => ?_)
    · -- Product component
      simp only [Fin.snoc_last]
      rw [Real.norm_eq_abs, abs_mul]
      calc |c₁.sol.trajectory t c₁.pivp.output| *
            |c₂.sol.trajectory t c₂.pivp.output|
          ≤ M₁ * M₂ := mul_le_mul (hx₁_bound t ht) (hx₂_bound t ht)
              (abs_nonneg _) (le_of_lt hM₁)
        _ ≤ M₁ * M₂ + M₁ + M₂ := by linarith [hM₁, hM₂]
    · -- Sub-PIVP components
      refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
      · simp only [Fin.snoc_castSucc, Fin.append_left]
        calc ‖c₁.sol.trajectory t j₁‖
            ≤ ‖c₁.sol.trajectory t‖ := norm_le_pi_norm _ _
          _ ≤ M₁ := hb₁ t ht
          _ ≤ M₁ * M₂ + M₁ + M₂ := by nlinarith [hM₂]
      · simp only [Fin.snoc_castSucc, Fin.append_right]
        calc ‖c₂.sol.trajectory t j₂‖
            ≤ ‖c₂.sol.trajectory t‖ := norm_le_pi_norm _ _
          _ ≤ M₂ := hb₂ t ht
          _ ≤ M₁ * M₂ + M₁ + M₂ := by nlinarith [hM₁]
  · -- continuity
    exact continuous_snoc_append c₁.trajectory_continuous c₂.trajectory_continuous
      (((continuous_apply c₁.pivp.output).comp c₁.trajectory_continuous).mul
        ((continuous_apply c₂.pivp.output).comp c₂.trajectory_continuous))
  · -- Convergence: three-term decomposition + modulus shift by K
    intro r t ht
    simp only [PolyPIVP.parallel_output, Fin.snoc_last]
    have ht_pos : 0 < t := lt_of_le_of_lt (le_max_left 0 _) ht
    have ht₁ : t > c₁.modulus (r + K) :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right 0 _)) ht
    have ht₂ : t > c₂.modulus (r + K) :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right 0 _)) ht
    -- Abbreviations
    set x₁ := c₁.sol.trajectory t c₁.pivp.output
    set x₂ := c₂.sol.trajectory t c₂.pivp.output
    set e_rK := Real.exp (-(↑(r + K) : ℝ))
    have hc₁ : |x₁ - α| < e_rK := c₁.convergence (r + K) t ht₁
    have hc₂ : |x₂ - β| < e_rK := c₂.convergence (r + K) t ht₂
    have hx₁ : |x₁| ≤ M₁ := hx₁_bound t (le_of_lt ht_pos)
    have hx₂ : |x₂| ≤ M₂ := hx₂_bound t (le_of_lt ht_pos)
    -- Triangle: x₁x₂-αβ = x₁(x₂-β)+(x₁-α)x₂-(x₁-α)(x₂-β)
    have htri : |x₁ * x₂ - α * β| ≤
        |x₁| * |x₂ - β| + |x₁ - α| * |x₂| + |x₁ - α| * |x₂ - β| := by
      have heq : x₁ * x₂ - α * β =
        (x₁ * (x₂ - β) + (x₁ - α) * x₂) + (-(x₁ - α) * (x₂ - β)) := by ring
      calc |x₁ * x₂ - α * β|
          = |(x₁ * (x₂ - β) + (x₁ - α) * x₂) + (-(x₁ - α) * (x₂ - β))| := by rw [heq]
        _ ≤ |x₁ * (x₂ - β) + (x₁ - α) * x₂| + |-(x₁ - α) * (x₂ - β)| :=
            abs_add_le _ _
        _ ≤ (|x₁ * (x₂ - β)| + |(x₁ - α) * x₂|) + |-(x₁ - α) * (x₂ - β)| := by
            linarith [abs_add_le (x₁ * (x₂ - β)) ((x₁ - α) * x₂)]
        _ = |x₁| * |x₂ - β| + |x₁ - α| * |x₂| + |x₁ - α| * |x₂ - β| := by
            simp only [abs_mul, neg_mul, abs_neg]
    -- Bound each term
    have hb1 : |x₁| * |x₂ - β| ≤ M₁ * e_rK :=
      mul_le_mul hx₁ (le_of_lt hc₂) (abs_nonneg _) (le_of_lt hM₁)
    have hb2 : |x₁ - α| * |x₂| ≤ e_rK * M₂ :=
      mul_le_mul (le_of_lt hc₁) hx₂ (abs_nonneg _) (le_of_lt (Real.exp_pos _))
    have h_le_1 : e_rK ≤ 1 := by
      calc e_rK ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr (neg_nonpos.mpr (by positivity))
        _ = 1 := Real.exp_zero
    have hb3 : |x₁ - α| * |x₂ - β| ≤ e_rK := by
      calc |x₁ - α| * |x₂ - β|
          ≤ e_rK * e_rK :=
            mul_le_mul (le_of_lt hc₁) (le_of_lt hc₂) (abs_nonneg _)
              (le_of_lt (Real.exp_pos _))
        _ ≤ 1 * e_rK :=
            mul_le_mul_of_nonneg_right h_le_1 (le_of_lt (Real.exp_pos _))
        _ = e_rK := one_mul _
    -- Sum: ≤ (M₁+M₂+1)·e_rK
    have hsum : |x₁ * x₂ - α * β| ≤ (M₁ + M₂ + 1) * e_rK := by linarith
    -- Rate: (M₁+M₂+1)·e_rK < exp(-r) via e^K > M₁+M₂+1
    have hrate : (M₁ + M₂ + 1) * e_rK < Real.exp (-(↑r : ℝ)) := by
      have hfactor : e_rK = Real.exp (-(↑r : ℝ)) * Real.exp (-(↑K : ℝ)) := by
        change Real.exp (-(↑(r + K) : ℝ)) = _
        rw [show (-(↑(r + K) : ℝ)) = -(↑r : ℝ) + (-(↑K : ℝ)) from by push_cast; ring,
            Real.exp_add]
      rw [hfactor, show (M₁ + M₂ + 1) * (Real.exp (-(↑r : ℝ)) * Real.exp (-(↑K : ℝ))) =
        Real.exp (-(↑r : ℝ)) * ((M₁ + M₂ + 1) * Real.exp (-(↑K : ℝ))) from by ring]
      have hfrac : (M₁ + M₂ + 1) * Real.exp (-(↑K : ℝ)) < 1 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
        exact hexp_K
      calc Real.exp (-(↑r : ℝ)) * ((M₁ + M₂ + 1) * Real.exp (-(↑K : ℝ)))
          < Real.exp (-(↑r : ℝ)) * 1 :=
            mul_lt_mul_of_pos_left hfrac (Real.exp_pos _)
        _ = Real.exp (-(↑r : ℝ)) := mul_one _
    linarith

end CertifiedBoundedTimeComputable

/-- Addition closure for real-time computable numbers ([RTCRN2] Lemma 5).
  The sum tracker of `CertifiedBoundedTimeComputable.exists_add`; its modulus
  `max(μ₁(r+1), μ₂(r+1))` is linear when both inputs are. -/
theorem realtime_field_add {α β : ℝ} :
    IsRealTimeComputable α → IsRealTimeComputable β → IsRealTimeComputable (α + β) := by
  intro ⟨d₁, btc₁, C₁, hC₁, hmod₁⟩ ⟨d₂, btc₂, C₂, hC₂, hmod₂⟩
  obtain ⟨c, hc⟩ := CertifiedBoundedTimeComputable.exists_add btc₁ btc₂
  refine ⟨d₁ + d₂ + 1, c, 2 * max C₁ C₂, by positivity, fun r => ?_⟩
  rw [hc r]
  have h₁ : btc₁.modulus (r + 1) ≤ max C₁ C₂ * (↑r + 2) := by
    calc btc₁.modulus (r + 1)
        ≤ C₁ * (↑(r + 1) + 1) := hmod₁ (r + 1)
      _ = C₁ * (↑r + 2) := by push_cast; ring
      _ ≤ max C₁ C₂ * (↑r + 2) :=
          mul_le_mul_of_nonneg_right (le_max_left C₁ C₂)
            (by positivity)
  have h₂ : btc₂.modulus (r + 1) ≤ max C₁ C₂ * (↑r + 2) := by
    calc btc₂.modulus (r + 1)
        ≤ C₂ * (↑(r + 1) + 1) := hmod₂ (r + 1)
      _ = C₂ * (↑r + 2) := by push_cast; ring
      _ ≤ max C₁ C₂ * (↑r + 2) :=
          mul_le_mul_of_nonneg_right (le_max_right C₁ C₂)
            (by positivity)
  calc max (btc₁.modulus (r + 1)) (btc₂.modulus (r + 1))
      ≤ max C₁ C₂ * (↑r + 2) := max_le h₁ h₂
    _ ≤ max C₁ C₂ * (2 * (↑r + 1)) := by
        apply mul_le_mul_of_nonneg_left
        · have : (0 : ℝ) ≤ ↑r := Nat.cast_nonneg r; linarith
        · exact le_of_lt (lt_of_lt_of_le hC₁ (le_max_left C₁ C₂))
    _ = 2 * max C₁ C₂ * (↑r + 1) := by ring

/-- Multiplication closure for real-time computable numbers ([RTCRN2] Lemma 6).
  The product tracker of `CertifiedBoundedTimeComputable.exists_mul`; its modulus
  `max(0, μ₁(r+K), μ₂(r+K))` is linear when both inputs are. -/
theorem realtime_field_mul {α β : ℝ} :
    IsRealTimeComputable α → IsRealTimeComputable β → IsRealTimeComputable (α * β) := by
  intro ⟨d₁, btc₁, C₁, hC₁, hmod₁⟩ ⟨d₂, btc₂, C₂, hC₂, hmod₂⟩
  obtain ⟨c, K, hc⟩ := CertifiedBoundedTimeComputable.exists_mul btc₁ btc₂
  refine ⟨d₁ + d₂ + 1, c, max C₁ C₂ * (↑K + 1), by positivity, fun r => ?_⟩
  rw [hc r]
  have hcast : (↑(r + K) : ℝ) + 1 = ↑r + ↑K + 1 := by push_cast; ring
  have h₁ : btc₁.modulus (r + K) ≤ max C₁ C₂ * (↑r + ↑K + 1) := by
    have := hmod₁ (r + K); rw [hcast] at this
    exact le_trans this (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (by positivity))
  have h₂ : btc₂.modulus (r + K) ≤ max C₁ C₂ * (↑r + ↑K + 1) := by
    have := hmod₂ (r + K); rw [hcast] at this
    exact le_trans this (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (by positivity))
  have h_factor : (↑r : ℝ) + ↑K + 1 ≤ (↑K + 1) * (↑r + 1) := by
    have : (↑K + 1) * (↑r + 1) = ↑K * ↑r + ↑K + ↑r + 1 := by ring
    linarith [show (0 : ℝ) ≤ ↑K * ↑r from by positivity]
  calc max 0 (max (btc₁.modulus (r + K)) (btc₂.modulus (r + K)))
      ≤ max C₁ C₂ * (↑r + ↑K + 1) := max_le (by positivity) (max_le h₁ h₂)
    _ ≤ max C₁ C₂ * ((↑K + 1) * (↑r + 1)) :=
        mul_le_mul_of_nonneg_left h_factor
          (le_of_lt (lt_of_lt_of_le hC₁ (le_max_left C₁ C₂)))
    _ = max C₁ C₂ * (↑K + 1) * (↑r + 1) := by ring

/-- Addition closure of `IsCRNComputable` (the sum tracker, any modulus). -/
theorem crn_computable_add {α β : ℝ} (ha : IsCRNComputable α) (hb : IsCRNComputable β) :
    IsCRNComputable (α + β) := by
  obtain ⟨d₁, ⟨c₁⟩⟩ := ha
  obtain ⟨d₂, ⟨c₂⟩⟩ := hb
  obtain ⟨c, -⟩ := CertifiedBoundedTimeComputable.exists_add c₁ c₂
  exact ⟨_, ⟨c⟩⟩

/-- Multiplication closure of `IsCRNComputable` (the product tracker, any modulus). -/
theorem crn_computable_mul {α β : ℝ} (ha : IsCRNComputable α) (hb : IsCRNComputable β) :
    IsCRNComputable (α * β) := by
  obtain ⟨d₁, ⟨c₁⟩⟩ := ha
  obtain ⟨d₂, ⟨c₂⟩⟩ := hb
  obtain ⟨c, -, -⟩ := CertifiedBoundedTimeComputable.exists_mul c₁ c₂
  exact ⟨_, ⟨c⟩⟩

/-- A rational constant is real-time computable: the one-dimensional system with zero
polynomial field and initial value `q`. (An arbitrary real constant is not: the class is
countable.) -/
theorem realtime_rat_const (q : ℚ) :
    IsRealTimeComputable (q : ℝ) := by
  refine ⟨1, ?_, 1, by positivity, ?_⟩
  · exact {
      pivp := {
        field := fun _ => 0
        init := fun _ => q
        output := 0
      }
      sol := {
        trajectory := fun _ => ![(q : ℝ)]
        init_cond := by
          ext i
          fin_cases i
          simp [PolyPIVP.toPIVP]
        is_solution := fun t _ => by
          simpa [PolyPIVP.toPIVP, PolyPIVP.evalField] using
            (hasDerivAt_const t (![(q : ℝ)] : Fin 1 → ℝ))
      }
      modulus := fun _ => 0
      bounded := by
        refine ⟨|(q : ℝ)| + 1, by positivity, fun t _ => ?_⟩
        rw [pi_norm_le_iff_of_nonneg (by positivity)]
        intro i
        fin_cases i
        change ‖(q : ℝ)‖ ≤ |(q : ℝ)| + 1
        rw [Real.norm_eq_abs]
        linarith
      trajectory_continuous := continuous_const
      convergence := by
        intro r t _
        simp only [Matrix.cons_val_zero, sub_self, abs_zero]
        exact Real.exp_pos _
    }
  · intro r
    positivity

/-- A rational constant is CRN-computable. -/
theorem crn_rat_const (q : ℚ) :
    IsCRNComputable (q : ℝ) :=
  (realtime_rat_const q).isCRNComputable

/-- Negation closure: -α = (-1) * α, with the rational constant -1. -/
theorem realtime_field_neg {α : ℝ} (ha : IsRealTimeComputable α) :
    IsRealTimeComputable (-α) := by
  have h := realtime_field_mul (realtime_rat_const (-1)) ha
  have : ((-1 : ℚ) : ℝ) * α = -α := by push_cast; ring
  rwa [this] at h

/-- A one-sided exponential kernel has uniformly bounded mass. -/
private theorem integral_exp_decay_le {lam T t : ℝ} (hlam : 0 < lam) :
    ∫ s in T..t, Real.exp (-lam * (t - s)) ≤ 1 / lam := by
  have hderiv :
      ∀ s ∈ Set.uIcc T t,
        HasDerivAt (fun u => (1 / lam) * Real.exp (-lam * (t - u)))
          (Real.exp (-lam * (t - s))) s := by
    intro s hs
    have hinner : HasDerivAt (fun u => -lam * (t - u)) lam s := by
      convert (((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-lam)) using 1
      ring
    convert hinner.exp.const_mul (1 / lam) using 1
    field_simp [hlam.ne']
  have hint : IntervalIntegrable (fun s => Real.exp (-lam * (t - s))) MeasureTheory.volume T t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hcalc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc
    ∫ s in T..t, Real.exp (-lam * (t - s))
        = (1 / lam) - (1 / lam) * Real.exp (-lam * (t - T)) := by
            simpa [hlam.ne'] using hcalc
    _ ≤ 1 / lam := by
      have hnonneg : 0 ≤ (1 / lam) * Real.exp (-lam * (t - T)) := by positivity
      linarith

private theorem integral_prefix_split
    {g G : ℝ → ℝ} (hg_cont : Continuous g)
    (hG_def : G = fun t => ∫ s in (0 : ℝ)..t, g s) :
    ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → G t = G s + ∫ u in s..t, g u := by
  intro s t hs hst
  have hadd :
      (∫ u in (0 : ℝ)..s, g u) + ∫ u in s..t, g u = ∫ u in (0 : ℝ)..t, g u :=
    intervalIntegral.integral_add_adjacent_intervals
      (hg_cont.intervalIntegrable 0 s) (hg_cont.intervalIntegrable s t)
  simpa [hG_def] using hadd.symm

private theorem kernel_integral_eq_sub
    {g : ℝ → ℝ} {k : ℝ → ℝ → ℝ}
    (hg_cont : Continuous g)
    (hk_cont : ∀ t, Continuous (fun s => k t s))
    (hk_hd : ∀ t s, HasDerivAt (fun u => k t u) (g s * k t s) s) :
    ∀ {T t : ℝ}, T ≤ t → ∫ s in T..t, g s * k t s = k t t - k t T := by
  intro T t hTt
  have hderiv : ∀ s ∈ Set.uIcc T t, HasDerivAt (fun u => k t u) (g s * k t s) s := by
    intro s hs
    exact hk_hd t s
  have hint : IntervalIntegrable (fun s => g s * k t s) MeasureTheory.volume T t :=
    (hg_cont.mul (hk_cont t)).intervalIntegrable T t
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

private theorem integrating_factor_restart
    {G x : ℝ → ℝ} {k : ℝ → ℝ → ℝ}
    (hexpG : Continuous (fun s => Real.exp (G s)))
    (hk_exp : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → Real.exp (-G t) * Real.exp (G s) = k t s)
    (hx_def : x = fun t => Real.exp (-G t) * ∫ s in (0 : ℝ)..t, Real.exp (G s)) :
    ∀ {T t : ℝ}, 0 ≤ T → T ≤ t → x t = k t T * x T + ∫ s in T..t, k t s := by
  intro T t hT0 hTt
  have hfac : Real.exp (-G t) = k t T * Real.exp (-G T) := by
    calc
      Real.exp (-G t) = Real.exp (-G t) * (Real.exp (G T) * Real.exp (-G T)) := by
            rw [show Real.exp (G T) * Real.exp (-G T) = 1 by
              rw [← Real.exp_add, add_comm, neg_add_cancel, Real.exp_zero], mul_one]
      _ = (Real.exp (-G t) * Real.exp (G T)) * Real.exp (-G T) := by
            rw [mul_assoc]
      _ = k t T * Real.exp (-G T) := by
            rw [hk_exp hT0 hTt]
  set A : ℝ := ∫ s in (0 : ℝ)..T, Real.exp (G s)
  set B : ℝ := ∫ s in T..t, Real.exp (G s)
  have hsplit0 : A + B = ∫ s in (0 : ℝ)..t, Real.exp (G s) := by
    change (∫ s in (0 : ℝ)..T, Real.exp (G s)) +
      (∫ s in T..t, Real.exp (G s)) = ∫ s in (0 : ℝ)..t, Real.exp (G s)
    exact intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hexpG.intervalIntegrable 0 T) (hexpG.intervalIntegrable T t)
  have htail :
      Real.exp (-G t) * B = ∫ s in T..t, k t s := by
    dsimp [B]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Set.Icc T t := by simpa [Set.uIcc_of_le hTt] using hs
    have hs0 : 0 ≤ s := le_trans hT0 hsI.1
    have hst : s ≤ t := hsI.2
    simpa using hk_exp hs0 hst
  calc
    x t = Real.exp (-G t) * ∫ s in (0 : ℝ)..t, Real.exp (G s) := by
            rw [hx_def]
    _ = Real.exp (-G t) * (A + B) := by
            rw [← hsplit0]
    _ = Real.exp (-G t) * A + Real.exp (-G t) * B := by
            ring
    _ = Real.exp (-G t) * A + ∫ s in T..t, k t s := by
            rw [htail]
    _ = (k t T * Real.exp (-G T)) * A + ∫ s in T..t, k t s := by
            rw [hfac]
    _ = k t T * x T + ∫ s in T..t, k t s := by
            simp [hx_def, A]
            ring

private theorem kernel_from_antiderivative
    {g G : ℝ → ℝ} {k : ℝ → ℝ → ℝ}
    (hk_def : k = fun t s => Real.exp (-(∫ u in s..t, g u)))
    (hG_split : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → G t = G s + ∫ u in s..t, g u) :
    ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → Real.exp (-G t) * Real.exp (G s) = k t s := by
  intro s t hs hst
  have hsplit := hG_split hs hst
  calc
    Real.exp (-G t) * Real.exp (G s)
        = (Real.exp (-G s) * Real.exp (-(∫ u in s..t, g u))) * Real.exp (G s) := by
            rw [hsplit, neg_add, Real.exp_add]
    _ = Real.exp (-(∫ u in s..t, g u)) * (Real.exp (-G s) * Real.exp (G s)) := by
            ac_rfl
    _ = Real.exp (-(∫ u in s..t, g u)) := by
            rw [show Real.exp (-G s) * Real.exp (G s) = 1 from by
              rw [← Real.exp_add, neg_add_cancel, Real.exp_zero], mul_one]
    _ = k t s := by simp [hk_def]

private theorem forcing_integral_identity
    {α T t : ℝ} (hα_ne : α ≠ 0) {a b : ℝ → ℝ}
    (hinta : IntervalIntegrable a MeasureTheory.volume T t)
    (hintb : IntervalIntegrable b MeasureTheory.volume T t) :
    (∫ s in T..t, a s) - (1 / α) * ∫ s in T..t, b s
      = (1 / α) * ∫ s in T..t, (α * a s - b s) := by
  have hintaα : IntervalIntegrable (fun s => α * a s) MeasureTheory.volume T t :=
    hinta.const_mul α
  have hconstmul : ∫ s in T..t, α * a s = α * ∫ s in T..t, a s := by
    rw [intervalIntegral.integral_const_mul]
  calc
    (∫ s in T..t, a s) - (1 / α) * ∫ s in T..t, b s
        = (1 / α) * ((∫ s in T..t, α * a s) - ∫ s in T..t, b s) := by
            rw [hconstmul]
            field_simp [hα_ne]
    _ = (1 / α) * ∫ s in T..t, (α * a s - b s) := by
            rw [← intervalIntegral.integral_sub hintaα hintb]

private theorem forcing_integral_kernel_identity
    {α T t : ℝ} (hα_ne : α ≠ 0) {g k : ℝ → ℝ}
    (hintk : IntervalIntegrable k MeasureTheory.volume T t)
    (hintgk : IntervalIntegrable (fun s => g s * k s) MeasureTheory.volume T t) :
    (∫ s in T..t, k s) - (1 / α) * ∫ s in T..t, g s * k s =
      (1 / α) * ∫ s in T..t, (α - g s) * k s := by
  have hrewrite :
      ∫ s in T..t, (α * k s - g s * k s) = ∫ s in T..t, (α - g s) * k s := by
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  calc
    (∫ s in T..t, k s) - (1 / α) * ∫ s in T..t, g s * k s
        = (1 / α) * ∫ s in T..t, (α * k s - g s * k s) := by
            exact forcing_integral_identity hα_ne hintk hintgk
    _ = (1 / α) * ∫ s in T..t, (α - g s) * k s := by
            rw [hrewrite]

private theorem abs_sub_inv_le_of_nonneg_le
    {α B x : ℝ} (hα_pos : 0 < α) (hx_nonneg : 0 ≤ x) (hx_le : x ≤ B + 2 / α) :
    |x - α⁻¹| ≤ B + 3 / α := by
  have h_inv_nn : 0 ≤ α⁻¹ := le_of_lt (inv_pos.mpr hα_pos)
  calc
    |x - α⁻¹| ≤ |x| + |α⁻¹| := by
      simpa [sub_eq_add_neg, abs_neg] using (abs_add_le x (-α⁻¹))
    _ = x + α⁻¹ := by
      rw [abs_of_nonneg hx_nonneg, abs_of_nonneg h_inv_nn]
    _ ≤ B + 2 / α + α⁻¹ := by
      linarith
    _ = B + 3 / α := by
      rw [show α⁻¹ = (1 / α : ℝ) by simp]
      ring

private theorem abs_two_term_mul_le
    {a b u v : ℝ} (ha_nonneg : 0 ≤ a) (hb_nonneg : 0 ≤ b) :
    |a * u + b * v| ≤ a * |u| + b * |v| := by
  calc
    |a * u + b * v| ≤ |a * u| + |b * v| :=
      abs_add_le _ _
    _ = a * |u| + b * |v| := by
      rw [abs_mul, abs_of_nonneg ha_nonneg, abs_mul, abs_of_nonneg hb_nonneg]

private theorem exp_mul_le_exp_tail
    {A delay : ℝ} {r N : ℕ}
    (hA_le : A ≤ Real.exp (↑N : ℝ))
    (hdelay : delay > ↑r + ↑N + 1) :
    Real.exp (-delay) * A < Real.exp (-(↑(r + 1) : ℝ)) := by
  calc
    Real.exp (-delay) * A ≤ Real.exp (-delay) * Real.exp (↑N : ℝ) :=
      mul_le_mul_of_nonneg_left hA_le (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-delay + ↑N) := by
      rw [← Real.exp_add]
    _ < Real.exp (-(↑(r + 1) : ℝ)) := by
      apply Real.exp_lt_exp.mpr
      have hrewrite : (-(↑(r + 1) : ℝ)) = -(↑r : ℝ) - 1 := by
        push_cast
        ring
      rw [hrewrite]
      linarith

private theorem forcing_integral_abs_bound
    {g : ℝ → ℝ} {k : ℝ → ℝ → ℝ} {α T t : ℝ} {r Ntail : ℕ}
    (hg_cont : Continuous g)
    (hk_cont : ∀ t, Continuous (fun s => k t s))
    (hclose : ∀ s, T ≤ s → |g s - α| < Real.exp (-(↑(r + Ntail + 1) : ℝ)))
    (hk_le_exp : ∀ ⦃s : ℝ⦄, s ∈ Set.Icc T t →
      k t s ≤ Real.exp (-(α / 2) * (t - s)))
    (hk_nonneg : ∀ ⦃s : ℝ⦄, s ∈ Set.Icc T t → 0 ≤ k t s)
    (hTt : T ≤ t) :
    |∫ s in T..t, (α - g s) * k t s|
      ≤ Real.exp (-(↑(r + Ntail + 1) : ℝ)) *
          ∫ s in T..t, Real.exp (-(α / 2) * (t - s)) := by
  have hint_abs :
      IntervalIntegrable (fun s => |(α - g s) * k t s|) MeasureTheory.volume T t := by
    exact ((continuous_const.sub hg_cont).mul (hk_cont t)).norm.intervalIntegrable T t
  have hint_bound :
      IntervalIntegrable
        (fun s =>
          Real.exp (-(↑(r + Ntail + 1) : ℝ)) * Real.exp (-(α / 2) * (t - s)))
        MeasureTheory.volume T t := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    |∫ s in T..t, (α - g s) * k t s|
        ≤ ∫ s in T..t, |(α - g s) * k t s| :=
          intervalIntegral.abs_integral_le_integral_abs hTt
    _ ≤ ∫ s in T..t,
          Real.exp (-(↑(r + Ntail + 1) : ℝ)) * Real.exp (-(α / 2) * (t - s)) := by
            apply intervalIntegral.integral_mono_on hTt
            · exact hint_abs
            · exact hint_bound
            · intro s hs
              have hclose_s : |α - g s| < Real.exp (-(↑(r + Ntail + 1) : ℝ)) := by
                simpa [abs_sub_comm] using hclose s hs.1
              have hk_s := hk_le_exp hs
              have hk_nonneg_s := hk_nonneg hs
              rw [abs_mul, abs_of_nonneg hk_nonneg_s]
              exact mul_le_mul (le_of_lt hclose_s) hk_s hk_nonneg_s
                (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-(↑(r + Ntail + 1) : ℝ)) *
          ∫ s in T..t, Real.exp (-(α / 2) * (t - s)) := by
            rw [← intervalIntegral.integral_const_mul]

private theorem kernel_mass_le_two_div
    {α T t : ℝ} {φ : ℝ → ℝ}
    (hα_pos : 0 < α)
    (hintφ : IntervalIntegrable φ MeasureTheory.volume T t)
    (hφ_le : ∀ s ∈ Set.Icc T t, φ s ≤ Real.exp (-(α / 2) * (t - s)))
    (hTt : T ≤ t) :
    ∫ s in T..t, φ s ≤ 2 / α := by
  have hint_expdec :
      IntervalIntegrable (fun s => Real.exp (-(α / 2) * (t - s))) MeasureTheory.volume T t := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    ∫ s in T..t, φ s ≤ ∫ s in T..t, Real.exp (-(α / 2) * (t - s)) := by
      apply intervalIntegral.integral_mono_on hTt
      · exact hintφ
      · exact hint_expdec
      · intro s hs
        exact hφ_le s hs
    _ ≤ 1 / (α / 2) := integral_exp_decay_le (by positivity)
    _ = 2 / α := by
      field_simp [ne_of_gt hα_pos]

private theorem reciprocal_error_decomposition
    {α T t : ℝ} {x g : ℝ → ℝ} {k : ℝ → ℝ → ℝ}
    (hrestart : x t = k t T * x T + ∫ s in T..t, k t s)
    (hk_id : ∫ s in T..t, g s * k t s = 1 - k t T)
    (hcomb :
      (∫ s in T..t, k t s) - (1 / α) * ∫ s in T..t, g s * k t s =
        (1 / α) * ∫ s in T..t, (α - g s) * k t s) :
    x t - α⁻¹ =
      k t T * (x T - α⁻¹) + (1 / α) * ∫ s in T..t, (α - g s) * k t s := by
  have hconst : α⁻¹ = k t T * α⁻¹ + (1 / α) * ∫ s in T..t, g s * k t s := by
    calc
      α⁻¹ = (1 / α : ℝ) := by simp
      _ = (1 / α) * (k t T + ∫ s in T..t, g s * k t s) := by
            rw [hk_id]
            ring
      _ = k t T * α⁻¹ + (1 / α) * ∫ s in T..t, g s * k t s := by
            ring
  calc
    x t - α⁻¹
        = (k t T * x T + ∫ s in T..t, k t s) - α⁻¹ := by
            rw [hrestart]
    _ = (k t T * x T + ∫ s in T..t, k t s) -
          (k t T * α⁻¹ + (1 / α) * ∫ s in T..t, g s * k t s) := by
            simpa using congrArg
              (fun z => (k t T * x T + ∫ s in T..t, k t s) - z) hconst
    _ = k t T * (x T - α⁻¹) +
          ((∫ s in T..t, k t s) - (1 / α) * ∫ s in T..t, g s * k t s) := by
            ring
    _ = k t T * (x T - α⁻¹) + (1 / α) * ∫ s in T..t, (α - g s) * k t s := by
            rw [hcomb]

private theorem scaled_forcing_tail_le
    {α F I : ℝ} {r Ntail : ℕ}
    (hα_pos : 0 < α)
    (hforcing : F ≤ Real.exp (-(↑(r + Ntail + 1) : ℝ)) * I)
    (hI_le : I ≤ 2 / α)
    (hA2_exp : (2 / α ^ 2 : ℝ) ≤ Real.exp (↑Ntail : ℝ)) :
    (1 / α) * F ≤ Real.exp (-(↑(r + 1) : ℝ)) := by
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  calc
    (1 / α) * F ≤ (1 / α) * (Real.exp (-(↑(r + Ntail + 1) : ℝ)) * I) :=
      mul_le_mul_of_nonneg_left hforcing (by positivity)
    _ ≤ (1 / α) * (Real.exp (-(↑(r + Ntail + 1) : ℝ)) * (2 / α)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hI_le (le_of_lt (Real.exp_pos _))) (by positivity)
    _ = (2 / α ^ 2) * Real.exp (-(↑(r + Ntail + 1) : ℝ)) := by
      field_simp [hα_ne]
    _ ≤ Real.exp (↑Ntail : ℝ) * Real.exp (-(↑(r + Ntail + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_right hA2_exp (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-(↑(r + 1) : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring

private theorem two_mul_exp_succ_le_exp (r : ℕ) :
    2 * Real.exp (-(↑(r + 1) : ℝ)) ≤ Real.exp (-(↑r : ℝ)) := by
  have hcast : (-(↑(r + 1) : ℝ)) = -(↑r : ℝ) + (-1 : ℝ) := by
    push_cast
    ring
  rw [hcast, Real.exp_add]
  have h2e : 2 * Real.exp (-1 : ℝ) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos 1)]
    linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    2 * (Real.exp (-(↑r : ℝ)) * Real.exp (-1))
        = Real.exp (-(↑r : ℝ)) * (2 * Real.exp (-1)) := by
            ring
    _ ≤ Real.exp (-(↑r : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left h2e (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-(↑r : ℝ)) := by
          ring

private theorem add_tail_bounds_lt_exp
    {A B : ℝ} {r : ℕ}
    (hA : A < Real.exp (-(↑(r + 1) : ℝ)))
    (hB : B ≤ Real.exp (-(↑(r + 1) : ℝ))) :
    A + B < Real.exp (-(↑r : ℝ)) := by
  have hsum : A + B < 2 * Real.exp (-(↑(r + 1) : ℝ)) := by
    linarith
  exact lt_of_lt_of_le hsum (two_mul_exp_succ_le_exp r)

/-- Reciprocal closure (positive case): from [RTCRN2] Lemma 4.
  Extend a PIVP computing α > 0 with a variable x satisfying
  x' = 1 - f_out(t)·x, x(0) = 0. The integrating factor solution
  x(t) = e^{-F(t)} · ∫₀ᵗ e^{F(s)} ds converges to 1/α exponentially. -/
private theorem realtime_field_inv_pos {α : ℝ} (hα_pos : 0 < α)
    (ha : IsRealTimeComputable α) : IsRealTimeComputable α⁻¹ := by
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  obtain ⟨d, btc, C, hC, hmod⟩ := ha
  obtain ⟨M, hM, hbound⟩ := btc.bounded
  -- f(t) = trajectory output; g = continuous extension to all of ℝ
  set f : ℝ → ℝ := fun t => btc.sol.trajectory t btc.pivp.output with hf_def
  set g : ℝ → ℝ := fun t => f (max t 0) with hg_def
  have hg_cont : Continuous g := continuous_iff_continuousAt.mpr fun t => by
    have h1 : ContinuousAt f (max t 0) :=
      ((hasDerivAt_pi.mp (btc.sol.is_solution (max t 0) (le_max_right t 0)))
        btc.pivp.output).continuousAt
    have h2 : ContinuousAt (fun s => max s (0:ℝ)) t :=
      (continuous_id.max continuous_const).continuousAt
    exact ContinuousAt.comp (g := f) (f := fun s => max s (0:ℝ)) h1 h2
  have hg_eq : ∀ t, 0 ≤ t → g t = f t := fun t ht => by simp [hg_def, max_eq_left ht]
  have hf_bound : ∀ t, 0 ≤ t → |f t| ≤ M := fun t ht => by
    have := norm_le_pi_norm (btc.sol.trajectory t) btc.pivp.output
    rw [Real.norm_eq_abs] at this; linarith [hbound t ht]
  -- G(t) = ∫₀ᵗ g(s) ds (integrating factor)
  set G : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, g s with hG_def
  have hG_hd : ∀ t, HasDerivAt G (g t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hg_cont.intervalIntegrable 0 t)
      (hg_cont.stronglyMeasurableAtFilter _ _) hg_cont.continuousAt
  have hG_cont : Continuous G :=
    continuous_iff_continuousAt.mpr fun t => (hG_hd t).continuousAt
  have hexpG : Continuous (fun s => Real.exp (G s)) := Real.continuous_exp.comp hG_cont
  -- x(t) = e^{-G(t)} · ∫₀ᵗ e^{G(s)} ds (reciprocal trajectory)
  set x : ℝ → ℝ := fun t => Real.exp (-G t) * ∫ s in (0:ℝ)..t, Real.exp (G s) with hx_def
  have hx_zero : x 0 = 0 := by
    simp [hx_def, hG_def, intervalIntegral.integral_same]
  -- HasDerivAt x (1 - g(t)·x(t)) at each t
  have hx_hd : ∀ t, HasDerivAt x (1 - g t * x t) t := by
    intro t
    have h2 := (hG_hd t).neg.exp  -- d/dt exp(-G(t))
    have h3 := intervalIntegral.integral_hasDerivAt_right (hexpG.intervalIntegrable 0 t)
      (hexpG.stronglyMeasurableAtFilter _ _) hexpG.continuousAt
    have h4 := h2.mul h3
    -- Convert Pi.mul function form to x
    have hfun : (fun t => Real.exp ((-G) t)) * (fun u => ∫ s in (0:ℝ)..u, Real.exp (G s)) = x := by
      ext s; simp [hx_def, Pi.mul_apply]
    rw [hfun] at h4
    -- Now h4 : HasDerivAt x (...) t; fix derivative value
    convert h4 using 1
    simp only [hx_def, Pi.neg_apply]
    rw [show Real.exp (-G t) * Real.exp (G t) = 1 from by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]]
    ring
  set Npos : ℕ := Nat.ceil (2 / α) with hNpos_def
  set T0 : ℝ := C * (↑Npos + 1) + 1 with hT0_def
  set B0 : ℝ := Real.exp (M * T0) * (T0 * Real.exp (M * T0)) with hB0_def
  set Ninit : ℕ := Nat.ceil (B0 + 3 / α) with hNinit_def
  set Ntail : ℕ := Nat.ceil (2 / α ^ 2) with hNtail_def
  have hT0_pos : 0 < T0 := by
    rw [hT0_def]
    positivity
  have hNpos_ge : (2 / α : ℝ) ≤ Npos := Nat.le_ceil _
  have hNpos_exp : Real.exp (-(↑Npos : ℝ)) ≤ α / 2 := by
    have hplus : (↑Npos : ℝ) + 1 ≤ Real.exp (↑Npos : ℝ) := by
      simpa using Real.add_one_le_exp (↑Npos : ℝ)
    have hden_pos : 0 < (↑Npos : ℝ) + 1 := by positivity
    have h_inv : (1 : ℝ) / Real.exp (↑Npos : ℝ) ≤ 1 / ((↑Npos : ℝ) + 1) :=
      one_div_le_one_div_of_le hden_pos hplus
    have h_half : 1 / ((↑Npos : ℝ) + 1) ≤ α / 2 := by
      have htmp : (2 : ℝ) ≤ α * ((↑Npos : ℝ) + 1) := by
        have hmul := hNpos_ge
        field_simp [hα_ne] at hmul
        nlinarith [hmul, hα_pos]
      field_simp [hα_ne, hden_pos.ne']
      nlinarith
    simpa [Real.exp_neg] using le_trans h_inv h_half
  have hg_lower : ∀ t, T0 ≤ t → α / 2 ≤ g t := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hT0_pos.le ht
    have ht_mod : t > btc.modulus Npos := by
      have hlin := hmod Npos
      have : C * (↑Npos + 1) < t := by
        rw [hT0_def] at ht
        linarith
      exact lt_of_le_of_lt hlin this
    rw [hg_eq t ht0]
    have hconv := btc.convergence Npos t ht_mod
    have hclose : |f t - α| < α / 2 := lt_of_lt_of_le hconv hNpos_exp
    linarith [abs_lt.mp hclose]
  have hG_split : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → G t = G s + ∫ u in s..t, g u :=
    integral_prefix_split hg_cont hG_def
  set k : ℝ → ℝ → ℝ := fun t s => Real.exp (-(∫ u in s..t, g u)) with hk_def
  have hk_hd : ∀ t s, HasDerivAt (fun u => k t u) (g s * k t s) s := by
    intro t s
    have hleft :=
      intervalIntegral.integral_hasDerivAt_left (hg_cont.intervalIntegrable s t)
        (hg_cont.stronglyMeasurableAtFilter _ _) hg_cont.continuousAt
    simpa [k, hk_def, mul_comm] using hleft.neg.exp
  have hk_cont : ∀ t, Continuous (fun s => k t s) := by
    intro t
    exact continuous_iff_continuousAt.mpr fun s => (hk_hd t s).continuousAt
  have hk_integral : ∀ {T t : ℝ}, T ≤ t → ∫ s in T..t, g s * k t s = 1 - k t T := by
    intro T t hTt
    have hcalc := kernel_integral_eq_sub hg_cont hk_cont hk_hd hTt
    simpa [k, hk_def] using hcalc
  have hk_exp : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → Real.exp (-G t) * Real.exp (G s) = k t s :=
    kernel_from_antiderivative hk_def hG_split
  have hx_restart : ∀ {T t : ℝ}, 0 ≤ T → T ≤ t →
      x t = k t T * x T + ∫ s in T..t, k t s :=
    integrating_factor_restart hexpG hk_exp hx_def
  have hx_nonneg : ∀ t, 0 ≤ t → 0 ≤ x t := by
    intro t ht
    rw [hx_def]
    apply mul_nonneg
    · exact le_of_lt (Real.exp_pos _)
    · exact intervalIntegral.integral_nonneg ht (fun s hs => le_of_lt (Real.exp_pos _))
  have hG_abs_le : ∀ t, 0 ≤ t → t ≤ T0 → |G t| ≤ M * T0 := by
    intro t ht0 htT
    rw [hG_def]
    have h_abs_mono : ∫ s in (0 : ℝ)..t, |g s| ≤ ∫ s in (0 : ℝ)..t, M := by
      apply intervalIntegral.integral_mono_on ht0
      · exact hg_cont.norm.intervalIntegrable 0 t
      · exact continuous_const.intervalIntegrable 0 t
      · intro s hs
        rw [hg_eq s hs.1]
        exact hf_bound s hs.1
    calc
      |∫ s in (0 : ℝ)..t, g s| ≤ ∫ s in (0 : ℝ)..t, |g s| :=
        intervalIntegral.abs_integral_le_integral_abs ht0
      _ ≤ ∫ s in (0 : ℝ)..t, M := h_abs_mono
      _ = M * t := by
        rw [intervalIntegral.integral_const]
        simp [smul_eq_mul, mul_comm]
      _ ≤ M * T0 := mul_le_mul_of_nonneg_left htT (le_of_lt hM)
  have hx_pre : ∀ t, 0 ≤ t → t ≤ T0 → x t ≤ B0 := by
    intro t ht0 htT
    have h_exp_le : Real.exp (-G t) ≤ Real.exp (M * T0) := by
      apply Real.exp_le_exp.mpr
      have hG := hG_abs_le t ht0 htT
      linarith [(abs_le.mp hG).1]
    have h_int_le : ∫ s in (0 : ℝ)..t, Real.exp (G s) ≤ T0 * Real.exp (M * T0) := by
      have h_exp_mono :
          ∫ s in (0 : ℝ)..t, Real.exp (G s) ≤ ∫ s in (0 : ℝ)..t, Real.exp (M * T0) := by
        apply intervalIntegral.integral_mono_on ht0
        · exact hexpG.intervalIntegrable 0 t
        · exact continuous_const.intervalIntegrable 0 t
        · intro s hs
          have hsT : s ≤ T0 := le_trans hs.2 htT
          have hG := hG_abs_le s hs.1 hsT
          apply Real.exp_le_exp.mpr
          exact (abs_le.mp hG).2
      calc
        ∫ s in (0 : ℝ)..t, Real.exp (G s) ≤ ∫ s in (0 : ℝ)..t, Real.exp (M * T0) := h_exp_mono
        _ = t * Real.exp (M * T0) := by
          rw [intervalIntegral.integral_const]
          simp [smul_eq_mul]
        _ ≤ T0 * Real.exp (M * T0) :=
          mul_le_mul_of_nonneg_right htT (le_of_lt (Real.exp_pos _))
    have h_int_nonneg : 0 ≤ ∫ s in (0 : ℝ)..t, Real.exp (G s) :=
      intervalIntegral.integral_nonneg ht0 (fun s hs => le_of_lt (Real.exp_pos _))
    rw [hx_def, hB0_def]
    exact mul_le_mul h_exp_le h_int_le h_int_nonneg (le_of_lt (Real.exp_pos _))
  have hk_le_exp :
      ∀ {T t s : ℝ}, T0 ≤ T → s ∈ Set.Icc T t →
        k t s ≤ Real.exp (-(α / 2) * (t - s)) := by
    intro T t s hT0T hs
    have hmono : ∫ u in s..t, (α / 2 : ℝ) ≤ ∫ u in s..t, g u := by
      apply intervalIntegral.integral_mono_on hs.2
      · exact continuous_const.intervalIntegrable s t
      · exact hg_cont.intervalIntegrable s t
      · intro u hu
        exact hg_lower u (le_trans hT0T (le_trans hs.1 hu.1))
    have hconst : ∫ u in s..t, (α / 2 : ℝ) = (α / 2) * (t - s) := by
      simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
        (intervalIntegral.integral_const (a := s) (b := t) (c := (α / 2 : ℝ)))
    have hneg : -(∫ u in s..t, g u) ≤ -(α / 2) * (t - s) := by
      linarith
    calc
      k t s = Real.exp (-(∫ u in s..t, g u)) := by simp [k]
      _ ≤ Real.exp (-(α / 2) * (t - s)) := Real.exp_le_exp.mpr hneg
  have hx_large : ∀ t, T0 ≤ t → x t ≤ B0 + 2 / α := by
    intro t htT
    have hrestart := hx_restart hT0_pos.le htT
    have hk_int : ∫ s in T0..t, k t s ≤ 2 / α := by
      have hint_expdec :
          IntervalIntegrable (fun s => Real.exp (-(α / 2) * (t - s)))
            MeasureTheory.volume T0 t := by
        apply Continuous.intervalIntegrable
        fun_prop
      calc
        ∫ s in T0..t, k t s ≤ ∫ s in T0..t, Real.exp (-(α / 2) * (t - s)) := by
          apply intervalIntegral.integral_mono_on htT
          · exact (hk_cont t).intervalIntegrable T0 t
          · exact hint_expdec
          · intro s hs
            exact hk_le_exp (le_rfl : T0 ≤ T0) hs
        _ ≤ 1 / (α / 2) := integral_exp_decay_le (by positivity)
        _ = 2 / α := by field_simp [hα_ne]
    have hk_one : k t T0 ≤ 1 := by
      have h_int_nonneg : 0 ≤ ∫ u in T0..t, g u := by
        apply intervalIntegral.integral_nonneg htT
        intro u hu
        have hlow := hg_lower u hu.1
        linarith
      calc
        k t T0 = Real.exp (-(∫ u in T0..t, g u)) := by simp [k]
        _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
        _ = 1 := by simp
    have hxT0 : x T0 ≤ B0 := hx_pre T0 hT0_pos.le le_rfl
    have hxT0_nonneg : 0 ≤ x T0 := hx_nonneg T0 hT0_pos.le
    have hterm1 : k t T0 * x T0 ≤ B0 := by
      calc
        k t T0 * x T0 ≤ 1 * x T0 :=
          mul_le_mul_of_nonneg_right hk_one hxT0_nonneg
        _ ≤ 1 * B0 := by simpa using hxT0
        _ = B0 := by ring
    linarith
  have hB0_nonneg : 0 ≤ B0 := by
    rw [hB0_def]
    positivity
  have hA1_exp : B0 + 3 / α ≤ Real.exp (↑Ninit : ℝ) := by
    have hceil : B0 + 3 / α ≤ Ninit := Nat.le_ceil _
    have hnat : (↑Ninit : ℝ) ≤ Real.exp (↑Ninit : ℝ) := by
      have := Real.add_one_le_exp (↑Ninit : ℝ)
      linarith
    exact le_trans hceil hnat
  have hA2_exp : (2 / α ^ 2 : ℝ) ≤ Real.exp (↑Ntail : ℝ) := by
    have hceil : (2 / α ^ 2 : ℝ) ≤ Ntail := Nat.le_ceil _
    have hnat : (↑Ntail : ℝ) ≤ Real.exp (↑Ntail : ℝ) := by
      have := Real.add_one_le_exp (↑Ntail : ℝ)
      linarith
    exact le_trans hceil hnat
  let Cinv : ℝ :=
    (C + 2 / α) +
      (T0 + (C * (↑Ntail + 2) + 1) + (2 / α) * (↑Ninit + 1))
  -- Build (d+1)-dimensional PIVP
  refine ⟨d + 1, ?_, Cinv, ?_, ?_⟩
  · refine {
    pivp := {
      field := Fin.snoc (fun j => MvPolynomial.rename Fin.castSucc (btc.pivp.field j))
          (1 - MvPolynomial.X (Fin.castSucc btc.pivp.output) * MvPolynomial.X (Fin.last d))
      init := Fin.snoc btc.pivp.init 0
      output := Fin.last d }
    sol := {
      trajectory := fun t => Fin.snoc (btc.sol.trajectory t) (x t)
      init_cond := by
        ext i; refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Fin.snoc_last, PolyPIVP.toPIVP_init, Rat.cast_zero]; exact hx_zero
        · simp only [Fin.snoc_castSucc, PolyPIVP.toPIVP_init]
          have h0 := congr_fun btc.sol.init_cond j
          simp only [PolyPIVP.toPIVP_init] at h0
          exact h0
      is_solution := fun t ht => by
        rw [hasDerivAt_pi]
        refine Fin.lastCases ?_ (fun j => ?_)
        · -- Last component: d/dt x(t) = 1 - f(t)·x(t)
          simp only [PolyPIVP.toPIVP_field_eq, PolyPIVP.evalField, Fin.snoc_last,
            MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one, MvPolynomial.eval₂_mul,
            MvPolynomial.eval₂_X, Fin.snoc_castSucc]
          have := hx_hd t; rw [hg_eq t ht] at this; exact this
        · -- Original PIVP components
          simp only [PolyPIVP.toPIVP_field_eq, PolyPIVP.evalField, Fin.snoc_castSucc,
            MvPolynomial.eval₂_rename, Fin.snoc_comp_castSucc]
          exact (hasDerivAt_pi.mp (btc.sol.is_solution t ht)) j }
    modulus := fun r =>
      max T0 (btc.modulus (r + Ntail + 1) + 1) + (2 / α) * (↑r + ↑Ninit + 1)
    bounded := by
      refine ⟨M + (B0 + 2 / α), by positivity, fun t ht => ?_⟩
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      refine Fin.lastCases ?_ (fun j => ?_)
      · simp only [Fin.snoc_last]
        rw [Real.norm_eq_abs]
        have hx_bound : x t ≤ B0 + 2 / α := by
          by_cases hcase : t ≤ T0
          · have hx_pre' := hx_pre t ht hcase
            have htail_nonneg : 0 ≤ 2 / α := by positivity
            linarith
          · exact hx_large t (le_of_lt (lt_of_not_ge hcase))
        have hx_nn : 0 ≤ x t := hx_nonneg t ht
        rw [abs_of_nonneg hx_nn]
        have htail_nonneg : 0 ≤ M := le_of_lt hM
        linarith
      · simp only [Fin.snoc_castSucc]
        calc
          ‖btc.sol.trajectory t j‖ ≤ ‖btc.sol.trajectory t‖ := norm_le_pi_norm _ _
          _ ≤ M := hbound t ht
          _ ≤ M + (B0 + 2 / α) := by
            have htail_nonneg : 0 ≤ B0 + 2 / α := by
              positivity
            linarith
    trajectory_continuous := by
      have hx_cont : Continuous x :=
        continuous_iff_continuousAt.mpr fun t => (hx_hd t).continuousAt
      refine continuous_pi fun i => ?_
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        exact hx_cont
      · simp only [Fin.snoc_castSucc]
        exact (continuous_apply j).comp btc.trajectory_continuous
    convergence := by
      intro r t ht
      simp only [Fin.snoc_last]
      set T : ℝ := max T0 (btc.modulus (r + Ntail + 1) + 1) with hT_def
      have hT0T : T0 ≤ T := by
        rw [hT_def]
        exact le_max_left _ _
      have hT_ge0 : 0 ≤ T := le_trans hT0_pos.le hT0T
      have hTt : T ≤ t := by
        have hdelay_nonneg : 0 ≤ (2 / α) * (↑r + ↑Ninit + 1) := by positivity
        rw [hT_def] at ht
        linarith
      have hT_mod : btc.modulus (r + Ntail + 1) < T := by
        rw [hT_def]
        have : btc.modulus (r + Ntail + 1) < btc.modulus (r + Ntail + 1) + 1 := by linarith
        exact lt_of_lt_of_le this (le_max_right _ _)
      have hclose : ∀ s, T ≤ s → |g s - α| < Real.exp (-(↑(r + Ntail + 1) : ℝ)) := by
        intro s hs
        have hs0 : 0 ≤ s := le_trans hT_ge0 hs
        rw [hg_eq s hs0]
        exact btc.convergence (r + Ntail + 1) s (lt_of_lt_of_le hT_mod hs)
      have hrestart := hx_restart hT_ge0 hTt
      have hk_id := hk_integral hTt
      have hintk : IntervalIntegrable (fun s => k t s) MeasureTheory.volume T t :=
        (hk_cont t).intervalIntegrable T t
      have hintgk : IntervalIntegrable (fun s => g s * k t s) MeasureTheory.volume T t :=
        (hg_cont.mul (hk_cont t)).intervalIntegrable T t
      have hcomb :
          (∫ s in T..t, k t s) - (1 / α) * ∫ s in T..t, g s * k t s =
            (1 / α) * ∫ s in T..t, (α - g s) * k t s := by
        exact forcing_integral_kernel_identity hα_ne hintk hintgk
      have herr :
          x t - α⁻¹ =
            k t T * (x T - α⁻¹) + (1 / α) * ∫ s in T..t, (α - g s) * k t s := by
        exact reciprocal_error_decomposition hrestart hk_id hcomb
      have herr_abs :
          |x t - α⁻¹| ≤
            k t T * |x T - α⁻¹| + (1 / α) * |∫ s in T..t, (α - g s) * k t s| := by
        have hkT_nonneg : 0 ≤ k t T := by
          have hkT_pos : 0 < k t T := by
            change 0 < Real.exp (-(∫ u in T..t, g u))
            exact Real.exp_pos _
          exact le_of_lt hkT_pos
        have hαinv_nonneg : 0 ≤ (1 / α : ℝ) := by
          positivity
        rw [herr]
        exact abs_two_term_mul_le hkT_nonneg hαinv_nonneg
      have hkT_le : k t T ≤ Real.exp (-(α / 2) * (t - T)) := by
        exact hk_le_exp hT0T ⟨le_rfl, hTt⟩
      have hxT_bound : x T ≤ B0 + 2 / α := hx_large T hT0T
      have heT_bound : |x T - α⁻¹| ≤ B0 + 3 / α := by
        exact abs_sub_inv_le_of_nonneg_le hα_pos (hx_nonneg T hT_ge0) hxT_bound
      have hdelay : (α / 2) * (t - T) > ↑r + ↑Ninit + 1 := by
        have : t - T > (2 / α) * (↑r + ↑Ninit + 1) := by
          rw [hT_def] at ht
          linarith
        have hmul :
            (α / 2) * (t - T) > (α / 2) * ((2 / α) * (↑r + ↑Ninit + 1)) :=
          mul_lt_mul_of_pos_left this (by positivity)
        have hrhs : (α / 2) * ((2 / α) * (↑r + ↑Ninit + 1)) = ↑r + ↑Ninit + 1 := by
          field_simp [hα_ne]
        rw [hrhs] at hmul
        exact hmul
      have hfirst :
          k t T * |x T - α⁻¹| < Real.exp (-(↑(r + 1) : ℝ)) := by
        have hfirst_le :
            k t T * |x T - α⁻¹| ≤ Real.exp (-(α / 2) * (t - T)) * (B0 + 3 / α) :=
          mul_le_mul hkT_le heT_bound (by positivity) (by positivity)
        have htail_exp :
            Real.exp (-(α / 2) * (t - T)) * (B0 + 3 / α) < Real.exp (-(↑(r + 1) : ℝ)) := by
          have htail_exp' :=
            exp_mul_le_exp_tail (A := B0 + 3 / α) (delay := (α / 2) * (t - T)) hA1_exp hdelay
          have hrewrite : -((α / 2) * (t - T)) = (-(α / 2) * (t - T)) := by
            ring
          exact hrewrite ▸ htail_exp'
        exact lt_of_le_of_lt hfirst_le htail_exp
      have hI_le : ∫ s in T..t, Real.exp (-(α / 2) * (t - s)) ≤ 2 / α := by
        calc
          ∫ s in T..t, Real.exp (-(α / 2) * (t - s)) ≤ 1 / (α / 2) :=
            integral_exp_decay_le (by positivity)
          _ = 2 / α := by field_simp [hα_ne]
      have hforcing :
          |∫ s in T..t, (α - g s) * k t s|
            ≤ Real.exp (-(↑(r + Ntail + 1) : ℝ)) *
                ∫ s in T..t, Real.exp (-(α / 2) * (t - s)) := by
        exact forcing_integral_abs_bound hg_cont hk_cont hclose
          (fun {s} hs => hk_le_exp hT0T hs)
          (fun {s} hs => by
            have hk_pos : 0 < k t s := by
              change 0 < Real.exp (-(∫ u in s..t, g u))
              exact Real.exp_pos _
            exact le_of_lt hk_pos)
          hTt
      have hsecond :
          (1 / α) * |∫ s in T..t, (α - g s) * k t s|
            ≤ Real.exp (-(↑(r + 1) : ℝ)) := by
        exact scaled_forcing_tail_le hα_pos hforcing hI_le hA2_exp
      calc
        |x t - α⁻¹|
            ≤ k t T * |x T - α⁻¹| + (1 / α) * |∫ s in T..t, (α - g s) * k t s| := herr_abs
        _ < Real.exp (-(↑r : ℝ)) := add_tail_bounds_lt_exp hfirst hsecond
    }
  · dsimp [Cinv]
    positivity
  · intro r
    have htail_mod : btc.modulus (r + Ntail + 1) + 1 ≤ C * (↑r + ↑Ntail + 2) + 1 := by
      have hlin := hmod (r + Ntail + 1)
      calc
        btc.modulus (r + Ntail + 1) + 1 ≤ C * ((↑(r + Ntail + 1) : ℝ) + 1) + 1 := by
          linarith
        _ = C * (↑r + ↑Ntail + 2) + 1 := by
          push_cast
          ring
    calc
      max T0 (btc.modulus (r + Ntail + 1) + 1) + (2 / α) * (↑r + ↑Ninit + 1)
          ≤ (T0 + (C * (↑r + ↑Ntail + 2) + 1)) + (2 / α) * (↑r + ↑Ninit + 1) := by
              have htail_nonneg : 0 ≤ C * (↑r + ↑Ntail + 2) + 1 := by
                have hr_nonneg : 0 ≤ (↑r : ℝ) := Nat.cast_nonneg r
                have hNtail_nonneg : 0 ≤ (↑Ntail : ℝ) := Nat.cast_nonneg Ntail
                nlinarith [hC, hr_nonneg, hNtail_nonneg]
              have hmax :
                  max T0 (btc.modulus (r + Ntail + 1) + 1) ≤ T0 + (C * (↑r + ↑Ntail + 2) + 1) := by
                apply max_le
                · exact le_add_of_nonneg_right htail_nonneg
                · exact le_trans htail_mod (le_add_of_nonneg_left hT0_pos.le)
              linarith
      _ = (C + 2 / α) * ↑r +
            (T0 + (C * (↑Ntail + 2) + 1) + (2 / α) * (↑Ninit + 1)) := by
            ring
      _ ≤ Cinv * (↑r + 1) := by
            have hr_nonneg : 0 ≤ (↑r : ℝ) := Nat.cast_nonneg r
            have hK_nonneg : 0 ≤ T0 + (C * (↑Ntail + 2) + 1) + (2 / α) * (↑Ninit + 1) := by
              have hterm1 : 0 ≤ T0 := hT0_pos.le
              have hterm2 : 0 ≤ C * (↑Ntail + 2) + 1 := by
                have hmul_nonneg : 0 ≤ C * (↑Ntail + 2 : ℝ) := by
                  positivity
                linarith
              have hterm3 : 0 ≤ (2 / α) * (↑Ninit + 1) := by
                positivity
              linarith
            have hrest_nonneg :
                0 ≤ (C + 2 / α) + (T0 + (C * (↑Ntail + 2) + 1) + (2 / α) * (↑Ninit + 1)) * ↑r := by
              have hA_nonneg : 0 ≤ C + 2 / α := by
                positivity
              nlinarith
            calc
              (C + 2 / α) * ↑r + (T0 + (C * (↑Ntail + 2) + 1) + (2 / α) * (↑Ninit + 1))
                  ≤ (C + 2 / α) * ↑r +
                      (T0 + (C * (↑Ntail + 2) + 1) + (2 / α) * (↑Ninit + 1)) +
                      ((C + 2 / α) +
                        (T0 + (C * (↑Ntail + 2) + 1) + (2 / α) * (↑Ninit + 1)) * ↑r) := by
                    linarith
              _ = Cinv * (↑r + 1) := by
                    dsimp [Cinv]
                    ring

/-- Reciprocal closure for real-time computable numbers.
  When α ≠ 0 and α ∈ ℝ_RTCRN, then α⁻¹ ∈ ℝ_RTCRN.
  For α > 0: extend PIVP with x' = 1 - f(t)·x (integrating factor).
  For α < 0: reduce via 1/α = -(1/(-α)). -/
theorem realtime_field_inv {α : ℝ} (hα : α ≠ 0)
    (ha : IsRealTimeComputable α) : IsRealTimeComputable α⁻¹ := by
  by_cases hpos : 0 < α
  · exact realtime_field_inv_pos hpos ha
  · push Not at hpos
    have hneg : α < 0 := lt_of_le_of_ne hpos hα
    have h1 := realtime_field_inv_pos (neg_pos.mpr hneg) (realtime_field_neg ha)
    convert realtime_field_neg h1 using 1
    rw [inv_neg, neg_neg]

/-- Division closure: α / β = α · β⁻¹. -/
theorem realtime_field_div {α β : ℝ} (hβ : β ≠ 0)
    (ha : IsRealTimeComputable α) (hb : IsRealTimeComputable β) :
    IsRealTimeComputable (α / β) := by
  rw [div_eq_mul_inv]
  exact realtime_field_mul ha (realtime_field_inv hβ hb)

/-- Subtraction closure: derived from add and neg. -/
theorem realtime_field_sub {α β : ℝ} (ha : IsRealTimeComputable α)
    (hb : IsRealTimeComputable β) : IsRealTimeComputable (α - β) := by
  have : α - β = α + (-β) := sub_eq_add_neg α β
  rw [this]
  exact realtime_field_add ha (realtime_field_neg hb)

end Ripple
