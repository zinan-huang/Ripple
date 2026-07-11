/-
  Mass-action PMF on Option N.I.

  At a non-terminal state: weight(some i) = jumpProbAt(z, i), weight(none) = 0.
  At a terminal state: weight(none) = 1, weight(some i) = 0.
-/
import Ripple.sCRNUniversality.Stochastic.CRNtoQMatrix
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace Ripple.sCRNUniversality.Stochastic.MassAction

open scoped BigOperators ENNReal

universe u v

variable {S : Type u} [Fintype S] [DecidableEq S]
variable (N : Network.{u, v} S) [DecidableEq N.I]

noncomputable def massActionWeight
    (hPos : N.hasPositiveRates) (z : State S) : Option N.I -> ENNReal := by
  classical
  intro o
  exact if hT : N.Terminal z then
    match o with
    | none => 1
    | some _ => 0
  else
    match o with
    | none => 0
    | some i => (jumpProbAt N z i : ENNReal)

theorem massActionWeight_sum_eq_one
    (hPos : N.hasPositiveRates) (z : State S) :
    Finset.univ.sum (massActionWeight N hPos z) = 1 := by
  classical
  unfold massActionWeight
  by_cases hT : N.Terminal z <;> simp only [hT, dite_true, dite_false]
  · rw [Fintype.sum_option]; simp
  · rw [Fintype.sum_option]; simp only [zero_add]
    have h := jumpProbAt_sum_eq_one N hPos hT
    simp_rw [← ENNReal.coe_nnratCast]
    rw [← ENNReal.coe_finsetSum]
    have h' : Finset.univ.sum (fun i => (jumpProbAt N z i : NNReal)) = 1 := by
      have := congr_arg (NNRat.castHom NNReal) h
      simp [map_sum] at this
      exact this
    rw [h']; simp

noncomputable def massActionPMF
    (hPos : N.hasPositiveRates) (z : State S) : PMF (Option N.I) :=
  ⟨massActionWeight N hPos z, by
    rw [ENNReal.summable.hasSum_iff]
    rw [tsum_fintype]
    exact massActionWeight_sum_eq_one N hPos z⟩

end Ripple.sCRNUniversality.Stochastic.MassAction
