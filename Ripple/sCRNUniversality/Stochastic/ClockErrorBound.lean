/-
  ClockBoundedLaw instantiation: geometric sum bound → per-microstep error.

  Key bound: for ρ = #A ≥ 1 and clock chain length l ≥ 1:
    1 / Σ_{k=0}^{l} ρ^k ≤ 1 / ρ^l

  This gives per-microstep error ≤ 1/#A^(l-1), which combined with
  error_le_target gives: #A ≥ (4n/δ)^{1/(l-1)} suffices for δ-accuracy.
-/
import Ripple.sCRNUniversality.Stochastic.Propensity

open scoped NNRat

namespace Ripple.sCRNUniversality.Stochastic

noncomputable def geometricSum (ρ : NNRat) : Nat → NNRat
  | 0 => 0
  | n + 1 => geometricSum ρ n + ρ ^ n

@[simp] theorem geometricSum_zero (ρ : NNRat) : geometricSum ρ 0 = 0 := rfl
@[simp] theorem geometricSum_one (ρ : NNRat) : geometricSum ρ 1 = 1 := by
  show 0 + ρ ^ 0 = 1; simp

theorem geometricSum_succ (ρ : NNRat) (n : Nat) :
    geometricSum ρ (n + 1) = geometricSum ρ n + ρ ^ n := rfl

theorem pow_le_geometricSum (ρ : NNRat) (n : Nat) :
    ρ ^ n ≤ geometricSum ρ (n + 1) :=
  le_add_left le_rfl

structure ClockErrorBound where
  accuracy : Nat
  chainLength : Nat
  hAccuracy : 1 ≤ accuracy
  hChain : 1 ≤ chainLength
  perMicrostepError : NNRat
  errorBound : perMicrostepError ≤ 1 / geometricSum (accuracy : NNRat) (chainLength + 1)

theorem ClockErrorBound.error_le_inv_pow (B : ClockErrorBound) :
    B.perMicrostepError ≤ 1 / (B.accuracy : NNRat) ^ B.chainLength := by
  calc B.perMicrostepError
      ≤ 1 / geometricSum (B.accuracy : NNRat) (B.chainLength + 1) := B.errorBound
    _ ≤ 1 / (B.accuracy : NNRat) ^ B.chainLength := by
        apply div_le_div_of_nonneg_left _ _ (pow_le_geometricSum _ _)
        · exact (show (0 : NNRat) ≤ 1 by norm_num)
        · exact pow_pos (Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.one_pos B.hAccuracy)) _

end Ripple.sCRNUniversality.Stochastic
