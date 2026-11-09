import Ripple.Number.Modular.CMEvaluationTargets
import Ripple.Number.Modular.JacobiQuarticDefect

/-!
# CM evaluation endpoint bridge

The analytic CM step will produce polynomial endpoint facts for the relevant
singular moduli.  This file records the exact algebraic conversion from those
endpoint facts to the named Chudnovsky CM statements. (The Ramanujan level-58 statement
`thetaLambda (i√58/2) = 1/99²` was false and was removed with its consumers.)
-/

noncomputable section

namespace Ripple
namespace Number
namespace Modular

open Polynomial

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
