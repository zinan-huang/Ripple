import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GapMassLower

namespace ExactMajority
namespace DominantLevelChoice

/-- The current repository surface for the paper's dominant-level selection.

The log-floor construction of `ell` is not present in the codebase yet, so the
dominant window is represented by its two advertised inequalities. -/
structure Window (M g : ℝ) (ell : ℕ) : Prop where
  gap_lower : (0.4 : ℝ) * |M| ≤ g * (2 : ℝ) ^ ell
  gap_upper : g * (2 : ℝ) ^ ell < (0.8 : ℝ) * |M|

/-- Lower edge of the dominant-level window:
`0.4 * |M| <= g * 2^ell`. -/
theorem dominantLevel_gap_lower {M g : ℝ} {ell : ℕ}
    (hchoice : Window M g ell) :
    (0.4 : ℝ) * |M| ≤ g * (2 : ℝ) ^ ell := by
  exact hchoice.gap_lower

/-- Repository consumers use the nonnegative main-count variable `M` rather
than `|M|`; this is the same lower edge under `0 <= M`. -/
theorem dominantLevel_gap_lower_of_nonneg {M g : ℝ} {ell : ℕ}
    (hM : 0 ≤ M) (hchoice : Window M g ell) :
    (0.4 : ℝ) * M ≤ g * (2 : ℝ) ^ ell := by
  simpa [abs_of_nonneg hM] using dominantLevel_gap_lower (M := M) (g := g)
    (ell := ell) hchoice

/-- Feed the carried dominant-level choice into `GapMassLower.gapMassLower`. -/
theorem gapMassLower_of_dominantLevelChoice {g betaPos betaNeg M : ℝ} (ell : ℕ)
    (hM : 0 ≤ M)
    (hchoice : Window M g ell)
    (hgap : g = betaPos - betaNeg)
    (hneg : 0 ≤ betaNeg) :
    (0.4 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ)) ≤ betaPos := by
  exact GapMassLower.gapMassLower ell hgap hneg
    (dominantLevel_gap_lower_of_nonneg (M := M) (g := g) (ell := ell) hM hchoice)

#print axioms dominantLevel_gap_lower
#print axioms dominantLevel_gap_lower_of_nonneg
#print axioms gapMassLower_of_dominantLevelChoice

end DominantLevelChoice
end ExactMajority
