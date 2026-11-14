-- Ripple/Kurtz/StrongApprox/SIPDensityStrongApprox.lean
import Ripple.Kurtz.StrongApprox.PoissonCellTimeChangeFactor
import Ripple.Kurtz.StrongApprox.ChainFluidLIL

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
open Ripple.CTMC

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {N : ℕ → Ω → ℕ}
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Total named version of the time-change path.  Scale zero uses the constant initial
path; every eventually-at-top theorem immediately enters the positive branch. -/
noncomputable def namedPoissonTimeChange
    (β : ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (b : ι → ℝ)
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (n : ℕ)
    (ω : ι → PathSpace Ω) : ℝ → Fin d → ℝ :=
  if hn : 0 < n then
    globalPoissonPath (N := N) (v := v)
      hn hβ0 hβb hβm x₀ ω
  else fun _ => x₀

@[simp]
theorem namedPoissonTimeChange_eq_global
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) {n : ℕ} (hn : 0 < n)
    (ω : ι → PathSpace Ω) :
    namedPoissonTimeChange (N := N)
      β v b hβ0 hβb hβm x₀ n ω =
      globalPoissonPath (N := N) (v := v)
        hn hβ0 hβb hβm x₀ ω := by
  simp [namedPoissonTimeChange, hn]

/-- Measurability in physical time for every scale. -/
theorem namedPoissonTimeChange_measurable_time
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (n : ℕ)
    (ω : ι → PathSpace Ω) :
    Measurable (namedPoissonTimeChange (N := N)
      β v b hβ0 hβb hβm x₀ n ω) := by
  by_cases hn : 0 < n
  · rw [namedPoissonTimeChange_eq_global
      (N := N) hβ0 hβb hβm x₀ hn]
    exact globalPoissonPath_measurable
      (N := N) (v := v) hn hβ0 hβb hβm x₀ ω
  · simp [namedPoissonTimeChange, hn]

@[simp]
theorem namedPoissonTimeChange_initial
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (n : ℕ)
    (ω : ι → PathSpace Ω) :
    namedPoissonTimeChange (N := N)
      β v b hβ0 hβb hβm x₀ n ω 0 = x₀ := by
  by_cases hn : 0 < n
  · rw [namedPoissonTimeChange_eq_global
      (N := N) hβ0 hβb hβm x₀ hn]
    exact globalPoissonPath_initial
      (N := N) (v := v) hn hβ0 hβb hβm x₀ ω
  · simp [namedPoissonTimeChange, hn]

/-- The named positive-scale path satisfies the random time-change equation. -/
theorem namedPoissonTimeChange_equation
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) {n : ℕ} (hn : 0 < n)
    (ω : ι → PathSpace Ω) {t : ℝ} (ht : 0 ≤ t) :
    let X := namedPoissonTimeChange (N := N)
      β v b hβ0 hβb hβm x₀ n ω
    X t = X 0 +
      ∑ l, ((poisFamily ι N l
        ((n : ℝ) * clock β X l t) ω : ℝ) /
          (n : ℝ)) • v l := by
  rw [namedPoissonTimeChange_eq_global
    (N := N) hβ0 hβb hβm x₀ hn]
  exact globalPoissonPath_equation
    (N := N) (v := v) hn hβ0 hβb hβm x₀ ω ht

/-- **The actual named time-change solution satisfies the LIL-scale rate.** -/
theorem ae_namedPoissonTimeChange_rate
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1))
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ y z,
      ‖tcDrift β v y - tcDrift β v z‖ ≤ L * ‖y - z‖)
    {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ → Fin d → ℝ} {x₀ : Fin d → ℝ}
    (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Icc (0 : ℝ) T,
      x t = x₀ + ∫ s in (0 : ℝ)..t, tcDrift β v (x s)) :
    ∀ᵐ ω ∂familyMeasure ι P,
      ∀ᶠ n : ℕ in atTop,
        ∀ t ∈ Icc (0 : ℝ) T,
          ‖namedPoissonTimeChange (N := N)
              β v b hβ0 hβb hβm x₀ n ω t - x t‖ ≤
            ((n : ℝ)⁻¹ *
              ∑ l, ‖v l‖ * envelope ((n : ℝ) * (b l * T))) *
                Real.exp (L * t) := by
  have hrate := ae_chain_fluid_rate hNm hN hNl
    hβ0 hβb hβm hL hF hT hxc hx
  filter_upwards [hrate] with ω hω
  filter_upwards [hω, Filter.eventually_gt_atTop 0] with n hnAll hn
  let X := namedPoissonTimeChange (N := N)
    β v b hβ0 hβb hβm x₀ n ω
  have hXm : Measurable X :=
    namedPoissonTimeChange_measurable_time
      (N := N) hβ0 hβb hβm x₀ n ω
  have hEq : ∀ t ∈ Icc (0 : ℝ) T,
      X t = X 0 +
        ∑ l, ((poisFamily ι N l
          ((n : ℝ) * clock β X l t) ω : ℝ) /
            (n : ℝ)) • v l := by
    intro t ht
    exact namedPoissonTimeChange_equation
      (N := N) hβ0 hβb hβm x₀ hn ω ht.1
  have hb := hnAll X hXm hEq
  intro t ht
  have h := hb t ht
  simpa [X, namedPoissonTimeChange_initial
    (N := N) hβ0 hβb hβm x₀ n ω] using h

/-- Density-dependent family data needed by the final one-space theorem.  The
only nonstandard field is the aligned coupling, isolated explicitly. -/
structure DensitySIPFamily
    (Γ : Ripple.Kurtz.RateSpec d)
    (β : ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (b : ι → ℝ)
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (xDensity : Fin d → ℝ) : Type _ where
  latticeStart : ∀ n : ℕ, 0 < n → Fin d → Fin (n + 1)
  coupling : ∀ n : ℕ, ∀ hn : 0 < n,
    AlignedCellCoupling (v := v)
      (DensityDepCTMC.mk n hn Γ)
      (latticeStart n hn)
      hβ0 hβb hβm xDensity

namespace DensitySIPFamily

/-- Every positive scale in the one-space family has the canonical
DensityDepCTMC path law. -/
theorem path_law
    {Γ : Ripple.Kurtz.RateSpec d}
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    {hβ0 : ∀ l y, 0 ≤ β l y}
    {hβb : ∀ l y, β l y ≤ b l}
    {hβm : ∀ l, Measurable (β l)}
    {xDensity : Fin d → ℝ}
    (D : DensitySIPFamily Γ β v b hβ0 hβb hβm xDensity)
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1))
    (n : ℕ) (hn : 0 < n) :
    (familyMeasure ι P).map
        (fun (ω : ι → PathSpace Ω) (t : ℝ≥0) =>
          namedPoissonTimeChange (N := N)
            β v b hβ0 hβb hβm xDensity n ω t) =
      ((DensityDepCTMC.mk n hn Γ).canonicalRecordMeasure
        (D.latticeStart n hn)).map
          (AlignedCellCoupling.canonicalDensityNonnegative
            (DensityDepCTMC.mk n hn Γ)) := by
  have hfun : (fun (ω : ι → PathSpace Ω) (t : ℝ≥0) =>
      namedPoissonTimeChange (N := N)
        β v b hβ0 hβb hβm xDensity n ω t) =
      globalNonnegativePath (N := N) (β := β) (v := v) (b := b)
        hn hβ0 hβb hβm xDensity := by
    funext ω t
    rw [namedPoissonTimeChange_eq_global
      (N := N) (v := v) hβ0 hβb hβm xDensity hn]
    rfl
  rw [hfun]
  exact sipGlobalPoissonPath_canonical_law
    (N := N) (P := P) (β := β) (v := v) (b := b)
    (M := DensityDepCTMC.mk n hn Γ) (xLattice := D.latticeStart n hn)
    hNm hN hNl hβ0 hβb hβm xDensity (D.coupling n hn)

end DensitySIPFamily

/-- **Final one-probability-space composition, conditional only on the aligned
cell coupling at each scale.**  The same SIP driver family carries every
`X_n`; each `X_n` has the canonical density-dependent CTMC law, and almost
surely all sufficiently large `n` satisfy the explicit LIL-scale bound. -/
theorem sip_density_strong_approximation
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1))
    {Γ : Ripple.Kurtz.RateSpec d}
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    {hβ0 : ∀ l y, 0 ≤ β l y}
    {hβb : ∀ l y, β l y ≤ b l}
    {hβm : ∀ l, Measurable (β l)}
    {xDensity : Fin d → ℝ}
    (D : DensitySIPFamily Γ β v b hβ0 hβb hβm xDensity)
    {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ y z,
      ‖tcDrift β v y - tcDrift β v z‖ ≤ L * ‖y - z‖)
    {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ → Fin d → ℝ}
    (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Icc (0 : ℝ) T,
      x t = xDensity +
        ∫ s in (0 : ℝ)..t, tcDrift β v (x s)) :
    (∀ n : ℕ, ∀ hn : 0 < n,
      (familyMeasure ι P).map
          (fun (ω : ι → PathSpace Ω) (t : ℝ≥0) =>
            namedPoissonTimeChange (N := N)
              β v b hβ0 hβb hβm xDensity n ω t) =
        ((DensityDepCTMC.mk n hn Γ).canonicalRecordMeasure
          (D.latticeStart n hn)).map
            (AlignedCellCoupling.canonicalDensityNonnegative
              (DensityDepCTMC.mk n hn Γ))) ∧
      (∀ᵐ ω ∂familyMeasure ι P,
        ∀ᶠ n : ℕ in atTop,
          ∀ t ∈ Icc (0 : ℝ) T,
            ‖namedPoissonTimeChange (N := N)
                β v b hβ0 hβb hβm xDensity n ω t - x t‖ ≤
              ((n : ℝ)⁻¹ *
                ∑ l, ‖v l‖ * envelope ((n : ℝ) * (b l * T))) *
                  Real.exp (L * t)) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    exact D.path_law hNm hN hNl n hn
  · exact ae_namedPoissonTimeChange_rate
      (N := N) hNm hN hNl
        hβ0 hβb hβm hL hF hT hxc hx

end Ripple.Kurtz.StrongApprox

end
