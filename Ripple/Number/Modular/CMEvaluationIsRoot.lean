import Ripple.Number.Modular.CMEvaluationTargets
import Ripple.Number.Modular.JacobiQuarticDefect

/-!
# CM evaluation endpoint bridge

The analytic CM step will produce polynomial endpoint facts for the relevant
singular moduli.  This file records the exact algebraic conversion from those
endpoint facts to the named Ramanujan and Chudnovsky CM statements.
-/

noncomputable section

namespace Ripple
namespace Number
namespace Modular

open Polynomial

lemma RamanujanLambda58Statement.isRoot
    (h : RamanujanLambda58Statement) :
    ramanujanLambda58TargetPolynomial.IsRoot (thetaLambda (ramanujanTau58 : ℂ)) := by
  rw [h]
  exact (by
    simpa [Polynomial.IsRoot] using ramanujanLambda58TargetPolynomial_eval)

lemma RamanujanLambda58Statement.of_isRoot
    (h : ramanujanLambda58TargetPolynomial.IsRoot
      (thetaLambda (ramanujanTau58 : ℂ))) :
    RamanujanLambda58Statement := by
  exact (ramanujanLambda58TargetPolynomial_isRoot_iff.mp h)

lemma RamanujanLambda58Statement.pullback_isRoot
    (h : RamanujanLambda58Statement) :
    ramanujanPullback58TargetPolynomial.IsRoot
      (thetaLambda (ramanujanTau58 : ℂ) ^ 2) := by
  rw [h]
  simpa [Polynomial.IsRoot] using ramanujanPullback58TargetPolynomial_eval

lemma KleinJCM163Statement.isRoot
    (h : KleinJCM163Statement) :
    heegnerJ163ClassPolynomial.IsRoot (kleinJ heegnerTau163) := by
  rw [h]
  exact heegnerJ163Target_isRoot_classPolynomial

lemma KleinJCM163Statement.of_isRoot
    (h : heegnerJ163ClassPolynomial.IsRoot (kleinJ heegnerTau163)) :
    KleinJCM163Statement := by
  exact (heegnerJ163ClassPolynomial_isRoot_iff.mp h)

lemma LambdaCM163Statement.isRoot
    (h : LambdaCM163Statement) :
    heegnerJ163ClassPolynomial.IsRoot (kleinJFromLambda lambdaEta163) := by
  rw [h]
  exact heegnerJ163Target_isRoot_classPolynomial

lemma LambdaCM163Statement.of_isRoot
    (h : heegnerJ163ClassPolynomial.IsRoot (kleinJFromLambda lambdaEta163)) :
    LambdaCM163Statement := by
  exact (heegnerJ163ClassPolynomial_isRoot_iff.mp h)

end Modular
end Number
end Ripple
