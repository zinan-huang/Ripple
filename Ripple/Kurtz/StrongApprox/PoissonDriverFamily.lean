-- Ripple/Kurtz/StrongApprox/PoissonDriverFamily.lean
import Ripple.Kurtz.StrongApprox.PoissonCellTimeChangeFactor
import Mathlib.Probability.Independence.InfinitePi

/-!
# A concrete iid Poisson(1) driver family

The canonical base `CanonicalCountSpace = ℕ → ℕ` carries the infinite product of
the Poisson(1) law.  The coordinate counts `canonicalCount i` are the driver
family `N` required by the Kurtz strong-approximation theorems:
measurable, independent, and Poisson(1) distributed.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.PoissonDriverFamily

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Ripple.Kurtz.StrongApprox

local instance : Fact (0 ≤ (1 : ℝ)) := ⟨zero_le_one⟩

/-- The product of countably many Poisson(1) laws on the canonical base. -/
noncomputable def driverMeasure : Measure CanonicalCountSpace :=
  Measure.infinitePi fun _ : ℕ => poisMeasure 1

instance driverMeasure_isProbabilityMeasure :
    IsProbabilityMeasure driverMeasure := by
  unfold driverMeasure
  infer_instance

/-- Every coordinate count is measurable. -/
theorem driver_measurable : ∀ i, Measurable (canonicalCount i) :=
  measurable_canonicalCount

/-- The coordinate counts are independent. -/
theorem driver_indep : iIndepFun canonicalCount driverMeasure :=
  iIndepFun_infinitePi (P := fun _ : ℕ => poisMeasure 1)
    (X := fun _ (k : ℕ) => k) (fun _ => measurable_id)

/-- Each coordinate count is Poisson(1). -/
theorem driver_law : ∀ i k,
    driverMeasure {omega | canonicalCount i omega = k} =
      ENNReal.ofReal (poisTerm k 1) := by
  intro i k
  have hmap : driverMeasure.map (fun z : CanonicalCountSpace => z i) =
      poisMeasure 1 := by
    simpa only [driverMeasure] using
      Measure.infinitePi_map_eval (fun _ : ℕ => poisMeasure 1) i
  have hset : {omega : CanonicalCountSpace | canonicalCount i omega = k} =
      (fun z : CanonicalCountSpace => z i) ⁻¹' {k} := rfl
  rw [hset, ← Measure.map_apply (measurable_pi_apply i)
    (measurableSet_singleton k), hmap, poisMeasure_singleton]

/-!
THEOREM LIST
* `driverMeasure`
* `driver_measurable`, `driver_indep`, `driver_law`
END
-/

end Ripple.Kurtz.StrongApprox.PoissonDriverFamily

end
