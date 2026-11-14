-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingClassReceiptArithmetic.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingSeedReceipt

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingClassReceiptArithmetic

open TimeTheorem StageEventSpec
open LateStrengthening
open LateSamplingSeedReceipt

variable {n : ℕ}

/-- (33): 3 A + B >= .592 M and A <= .0111 M imply
    A + B >= .5698 M. This is integer-exact, with no rounding
    of random class sizes and no division by M. -/
theorem first_branch_two_class_arithmetic
    (M A B : ℕ)
    (hmass : 592 * M ≤ 3000 * A + 1000 * B)
    (hshallow : 10000 * A ≤ 111 * M) :
    5698 * M ≤ 10000 * (A + B) := by
  omega

/-- The .4 M majority mass inequality, with a .002 M lower-index
    allowance and all remaining mass conservatively placed at
    ell+2, yields the 3A+B inequality. The inequality is written
    without divisions, to expose the exact integer bookkeeping. -/
theorem first_branch_mass_to_shape
    (M A B : ℕ)
    (hmass : 1600 * M ≤ 8 * M + 3000 * A + 1000 * B) :
    592 * M ≤ 3000 * A + 1000 * B := by
  omega

/-- Exact-level retrospective budget: at most .002 M new ell
    arrivals gives the weaker .0021 M sampling allowance. -/
theorem retrospective_exact_level_arithmetic
    (M earlier terminal : ℕ)
    (harrival : 1000 * terminal ≤ 1000 * earlier + 2 * M) :
    10000 * terminal ≤ 10000 * earlier + 21 * M := by
  omega

/-- Direct width-three class floor at every actual observed prefix.
    This uses the retained .9616 credit, not raw seed band counts. -/
theorem protected_three_class_at
    {init : InputCfg n} {ω : InputLog n}
    {a s t v M ell : ℕ} {σ : Sign}
    (hpath : LateF6OriginalLaw.Prefix init ω a s t)
    (hseed : LateSamplingSeedReceipt init M ell σ (trace init ω s))
    (hsv : s ≤ v) (hvt : v ≤ t)
    (hcount : timeMainCount (trace init ω v) = M) :
    9232 * M ≤ 10000 * bandCount σ ell 2 (trace init ω v) :=
  hseed.protectedBand_at hpath hsv hvt hcount

/-- Direct width-two credit branch. Unlike the disjunction in
    nearAlternative_at, this hypothesis selects the retained credit
    branch, so the conclusion is a floor at the actual time v. -/
theorem credit_two_class_at
    {init : InputCfg n} {ω : InputLog n}
    {a s t v M ell : ℕ} {σ : Sign}
    (hpath : LateF6OriginalLaw.Prefix init ω a s t)
    (hcredit :
      (1939 / 2000 : ℚ) * (M : ℚ) ≤
        AveragingCreditTransitions.totalCredit σ ell (ell + 1)
          (trace init ω s))
    (hsv : s ≤ v) (hvt : v ≤ t)
    (hcount : timeMainCount (trace init ω v) = M) :
    939 * M ≤ 1000 * bandCount σ ell 1 (trace init ω v) := by
  have hpersist := hcredit.trans
    (totalCredit_prefix_mono hpath le_rfl hsv hvt σ)
  exact two_level_band_of_credit σ ell M (trace init ω v)
    hcount hpersist

/-- The first branch of near_credit, after supplying the two
    explicitly missing mixed-prefix inputs:
      (1) seed shallow mass bounds current shallow mass;
      (2) the .4M mass ledger yields the level-shape inequality.
    The class partition is the elementary identification of the
    width-two band with the two exact level counts. -/
theorem shallow_two_class_at
    {init : InputCfg n} {ω : InputLog n}
    {a s t v M ell : ℕ} {σ : Sign}
    (hpath : LateF6OriginalLaw.Prefix init ω a s t)
    (hseed : LateSamplingSeedReceipt init M ell σ (trace init ω s))
    (hsv : s ≤ v) (hvt : v ≤ t)
    (hbranch :
      10000 * scaledShallowPositive σ ell (trace init ω s) ≤
        111 * (M : ℚ))
    (hshallowTransport :
      scaledShallowPositive σ ell (trace init ω v) ≤
        scaledShallowPositive σ ell (trace init ω s))
    (hlevelWeight :
      (bandCount σ ell 0 (trace init ω v) : ℚ) ≤
        scaledShallowPositive σ ell (trace init ω v))
    (hmass :
      592 * M ≤
        3000 * bandCount σ ell 0 (trace init ω v) +
        1000 * bandCount σ (ell + 1) 0 (trace init ω v))
    (hpartition :
      bandCount σ ell 1 (trace init ω v) =
        bandCount σ ell 0 (trace init ω v) +
        bandCount σ (ell + 1) 0 (trace init ω v)) :
    5698 * M ≤ 10000 * bandCount σ ell 1 (trace init ω v) := by
  have hlevel :
      10000 * bandCount σ ell 0 (trace init ω v) ≤ 111 * M := by
    exact_mod_cast
      (show (10000 : ℚ) *
          (bandCount σ ell 0 (trace init ω v) : ℚ) ≤
          111 * (M : ℚ) by
        linarith)
  have h := first_branch_two_class_arithmetic
    M (bandCount σ ell 0 (trace init ω v))
      (bandCount σ (ell + 1) 0 (trace init ω v)) hmass hlevel
  simpa only [hpartition] using h

/-- Consequence of the two near-credit branches; the result is a
    genuine disjunction of current-snapshot floors. Inputs marked
    Transport/Shape are NOT provided by the existing receipt. -/
theorem two_class_at
    {init : InputCfg n} {ω : InputLog n}
    {a s t v M ell : ℕ} {σ : Sign}
    (hpath : LateF6OriginalLaw.Prefix init ω a s t)
    (hseed : LateSamplingSeedReceipt init M ell σ (trace init ω s))
    (hsv : s ≤ v) (hvt : v ≤ t)
    (hcount : timeMainCount (trace init ω v) = M)
    (hshallowTransport :
      scaledShallowPositive σ ell (trace init ω v) ≤
        scaledShallowPositive σ ell (trace init ω s))
    (hlevelWeight :
      (bandCount σ ell 0 (trace init ω v) : ℚ) ≤
        scaledShallowPositive σ ell (trace init ω v))
    (hmass :
      592 * M ≤
        3000 * bandCount σ ell 0 (trace init ω v) +
        1000 * bandCount σ (ell + 1) 0 (trace init ω v))
    (hpartition :
      bandCount σ ell 1 (trace init ω v) =
        bandCount σ ell 0 (trace init ω v) +
        bandCount σ (ell + 1) 0 (trace init ω v)) :
    5698 * M ≤ 10000 * bandCount σ ell 1 (trace init ω v) ∨
      939 * M ≤ 1000 * bandCount σ ell 1 (trace init ω v) := by
  rcases hseed.near_credit with hsmall | hcredit
  · exact Or.inl
      (shallow_two_class_at hpath hseed hsv hvt hsmall
        hshallowTransport hlevelWeight hmass hpartition)
  · exact Or.inr
      (credit_two_class_at hpath hcredit hsv hvt hcount)

end Ripple.PopulationProtocol.ExactMajority.LateSamplingClassReceiptArithmetic

end
