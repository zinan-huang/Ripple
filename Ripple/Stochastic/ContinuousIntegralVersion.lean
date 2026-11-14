import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Uniqueness and stopping of continuous versions

Equality at each fixed time cannot be substituted directly at a random time.
A countable dense set and continuous paths give one exceptional null set for
all times. The resulting equality is preserved by random evaluation and stopping.
This module proves these transfer lemmas; it does not construct a version.
-/

open MeasureTheory Filter
open scoped NNReal

namespace Ripple.Stochastic.ContinuousIntegralVersion

variable {Ω ι : Type*} [MeasurableSpace Ω] [TopologicalSpace ι]
  {P : Measure Ω} {X Y : ι → Ω → ℝ}

/-- Continuous modifications of the same process agree at all times outside one null set. -/
theorem indistinguishable_of_dense_eq (d : ℕ → ι) (hd : DenseRange d)
    (hX : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (hXY : ∀ n, X (d n) =ᵐ[P] Y (d n)) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  have hall : ∀ᵐ ω ∂P, ∀ n, X (d n) ω = Y (d n) ω := ae_all_iff.mpr hXY
  filter_upwards [hX, hY, hall] with ω hXω hYω hω
  have heq : (fun t => X t ω) = (fun t => Y t ω) :=
    hd.equalizer hXω hYω (funext hω)
  exact congrFun heq

/-- Random-time evaluation is legitimate after obtaining one exceptional set. -/
theorem randomTime_eq_of_indistinguishable
    (hXY : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω) (τ : Ω → ι) :
    (fun ω => X (τ ω) ω) =ᵐ[P] (fun ω => Y (τ ω) ω) :=
  hXY.mono fun ω hω => hω (τ ω)

/-- Stopping preserves indistinguishability; no measurability is needed for this identity. -/
theorem stopped_eq_of_indistinguishable [LinearOrder ι]
    (hXY : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω) (τ : Ω → ι) :
    ∀ᵐ ω ∂P, ∀ t, X (min t (τ ω)) ω = Y (min t (τ ω)) ω :=
  hXY.mono fun ω hω t => hω (min t (τ ω))

/-- Once both versions are continuous, fixed-time stopping identities on a dense grid
upgrade to the indistinguishable identity needed by bracket and exponential arguments. -/
theorem stopped_identity_of_dense_eq
    {X J : ℝ≥0 → Ω → ℝ} (τ : Ω → ℝ≥0)
    (d : ℕ → ℝ≥0) (hd : DenseRange d)
    (hX : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hJ : ∀ᵐ ω ∂P, Continuous (fun t => J t ω))
    (hgrid : ∀ n, J (d n) =ᵐ[P] (fun ω => X (min (d n) (τ ω)) ω)) :
    ∀ᵐ ω ∂P, ∀ t, J t ω = X (min t (τ ω)) ω := by
  apply indistinguishable_of_dense_eq d hd hJ _ hgrid
  exact hX.mono fun ω hω => hω.comp (continuous_id.min continuous_const)

end Ripple.Stochastic.ContinuousIntegralVersion
