import Ripple.Probability.CountingBridge.Endpoint
import Ripple.Probability.CountingBridge.Expectation
import Ripple.Probability.CountingBridge.Geometric
import Ripple.Probability.CountingBridge.Stopping

/-! # Word counts and the infinite product of uniform letter laws

For a finite nonempty alphabet `α`, counts of words of length `T` divided by
`card α ^ T` are probabilities under the law of an infinite sequence of independent
uniform letters. This entry point exports cylinder probabilities, integrals of word and
endpoint functions, first-hit events, truncated expectations, almost-sure hitting,
expected-time bounds, first-prefix stopping transfers, and the geometric waiting-time
example.
-/
