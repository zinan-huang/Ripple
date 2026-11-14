import Ripple.Stochastic.ContinuousItoLinear
import Ripple.Kurtz.StrongApprox.KurtzClockAdapter

/-!
# The SDE of the Kurtz diffusion with the continuous Itô integral

When the channel integrals in `sdeRhs` are the continuous Itô integrals
`continuousItoOfFun` against Brownian motions `B l` of one filtration, the fixed-point equation
gives `KurtzSDEPathsNN` with `M l` the continuous Itô integral of `sqrt (N f_l (Z))`, the
integrand `kurtzClockIntegrand`. The scaling identity `M l = sqrt N * ∫ sqrt (f_l (Z)) dB_l`
is proved from the scalar linearity of the continuous integral, almost surely for all times.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Ripple.Kurtz.StrongApprox.KMTTransfer

open Ripple.Stochastic.StrongSDE Ripple.Stochastic.ContinuousItoLinear
open Ripple.Stochastic.FilteredItoIntegralCLM

/-- The SDE in the form `KurtzSDEPathsNN`, with `M l` the continuous Itô integral of
`sqrt (N f_l (Z))`, from the fixed-point equation `sdeRhs` whose channel integrals are the
continuous Itô integrals of `sqrt (f_l (Z))`. -/
theorem kurtzSDEPathsNN_of_continuousIto
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] {d : ℕ}
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {B : ι → ℝ≥0 → Ω → ℝ} [∀ l, IsFilteredPreBrownian (B l) F P]
    (hB : ∀ l ω, Continuous (fun t => B l t ω)) (hBmeas : ∀ l t, Measurable (B l t))
    {N : ℕ} (hN : 0 < N) {f : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ} {T : ℝ≥0}
    {Z : ℝ≥0 → Ω → Fin d → ℝ} {x₀ : Fin d → ℝ}
    (hmem : ∀ l, MemLp (Function.uncurry fun s ω => Real.sqrt (f l (Z s ω))) 2
      (trimMeasure_T (𝓖 := F) (μ := P) T (hBmeas l)))
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => Z t ω)
    (heq : ∀ᵐ ω ∂P, ∀ t ≤ T, Z t ω =
      sdeRhs (fun l => continuousItoOfFun P F T (hB l) (hBmeas l)) v
        (fun l x => Real.sqrt (f l x)) (tcDrift f v) x₀ N Z t ω) :
    ∀ᵐ ω ∂P, KurtzSDEPathsNN N f v T Z
      (fun l => continuousItoOfFun P F T (hB l) (hBmeas l)
        (fun s ω => Real.sqrt ((N : ℝ) * f l (Z s ω))))
      (fun _ => x₀) ω := by
  have hscale : ∀ l, ∀ᵐ ω ∂P, ∀ t,
      continuousItoOfFun P F T (hB l) (hBmeas l)
          (fun s ω => Real.sqrt ((N : ℝ) * f l (Z s ω))) t ω =
        Real.sqrt N * continuousItoOfFun P F T (hB l) (hBmeas l)
          (fun s ω => Real.sqrt (f l (Z s ω))) t ω := by
    intro l
    have hfun : (fun s ω => Real.sqrt ((N : ℝ) * f l (Z s ω))) =
        fun s ω => Real.sqrt N * Real.sqrt (f l (Z s ω)) := by
      funext s ω
      exact Real.sqrt_mul (Nat.cast_nonneg N) _
    rw [hfun]
    exact continuousItoOfFun_const_mul T (hB l) (hBmeas l) (hmem l) _
  filter_upwards [hcont, heq, ae_all_iff.2 hscale] with ω h1 h2 h3
  exact kurtzSDEPathsNN_of_sdeRhs hN h1 h2 (fun l t _ => h3 l t)

end Ripple.Kurtz.StrongApprox.KMTTransfer
