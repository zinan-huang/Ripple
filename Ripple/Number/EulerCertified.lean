import Ripple.Number.Euler

/-!
# Euler's certified bounded-time computation

Expose the polynomial certificate used in `euler_is_realtime` as a named
object, retaining its two-dimensional polynomial PIVP, closed-form trajectory,
and exact modulus.
-/

namespace Ripple.Number

/-- The certified two-dimensional computation of `Real.exp 1`, with the
existing polynomial PIVP and exact modulus `r + 2`. -/
noncomputable def eulerCBTC : CertifiedBoundedTimeComputable 2 (Real.exp 1) :=
  eulerBTC.certify eulerPolyPIVP eulerPolyPIVP_evalField
    (fun i => by
      fin_cases i <;> simp [eulerPolyPIVP, eulerBTC, eulerPIVP])
    rfl eulerSolution_continuous

@[simp] theorem eulerCBTC_pivp :
    eulerCBTC.pivp = eulerPolyPIVP := rfl

@[simp] theorem eulerCBTC_modulus (r : ℕ) :
    eulerCBTC.modulus r = (r : ℝ) + 2 := rfl

@[simp] theorem eulerCBTC_trajectory :
    eulerCBTC.sol.trajectory = eulerSolution := rfl

/-- Euler's certified export: the same certificate retains the exact
dimension, polynomial PIVP, and modulus. -/
theorem euler_certifiedBoundedTimeComputable :
    ∃ btc : CertifiedBoundedTimeComputable 2 (Real.exp 1),
      btc.pivp = eulerPolyPIVP ∧
        ∀ r : ℕ, btc.modulus r = (r : ℝ) + 2 := by
  exact ⟨eulerCBTC, eulerCBTC_pivp, eulerCBTC_modulus⟩

end Ripple.Number
