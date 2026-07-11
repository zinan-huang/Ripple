/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# One-Way Property

The initiator's state never changes during a transition.  This is the
fundamental asymmetry of the protocol: only the responder can be converted.

We re-export `delta_fst` and prove that it implies the initiator's count
in the population does not decrease (though for specific interactions, we
prove the exact relationship).
-/

import Ripple.PopulationProtocol.Majority.PopProto.Step

namespace PopProto

/-- The initiator state is preserved by δ. Alias of `delta_fst`. -/
theorem initiator_unchanged (i r : State) : (delta (i, r)).1 = i :=
  delta_fst (i, r)

/-- The responder's new state depends only on the pair (i, r). -/
theorem responder_determined (i r : State) :
    (delta (i, r)).2 = Config.responderResult i r := rfl

end PopProto
