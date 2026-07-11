/-
Numeric constants for the exact-majority protocol's probability analysis.
Extracted to break the transitive PhaseChain dependency on the headline path.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.BranchAndBudget

namespace ExactMajority
namespace Constants

def C0_numeral : ℕ := 17
def Cbad_numeral : ℕ := 3

theorem C0_numeral_above_recut : (3 : ℝ) / ((14 : ℝ) / 75) < (C0_numeral : ℝ) := by
  have h := BranchAndBudget.recut_window_coeff_bounds
  simpa [C0_numeral] using h.2

theorem Cbad_numeral_eq : Cbad_numeral = 3 := rfl

end Constants
end ExactMajority
