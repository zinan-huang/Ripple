/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Population Size Invariant

The total population `x + b + y = n` is preserved by every transition.
This is trivially true because `Config n` enforces it by construction:
the `sum_eq` field is a proof term that must be supplied whenever a new
configuration is built.
-/

import Ripple.PopulationProtocol.Majority.PopProto.Step

namespace PopProto

namespace Config

variable {n : ℕ}

/-- Population size is preserved by `step`: the result (when it exists)
    still satisfies `x_count + b_count + y_count = n`. -/
theorem step_preserves_sum (c : Config n) (i r : State) (c' : Config n)
    (_h : c.step i r = some c') : c'.x_count + c'.b_count + c'.y_count = n :=
  c'.sum_eq

/-- Population size is preserved by `stepOrSelf`. -/
theorem stepOrSelf_preserves_sum (c : Config n) (i r : State) :
    (c.stepOrSelf i r).x_count + (c.stepOrSelf i r).b_count +
      (c.stepOrSelf i r).y_count = n :=
  (c.stepOrSelf i r).sum_eq

end Config
end PopProto
