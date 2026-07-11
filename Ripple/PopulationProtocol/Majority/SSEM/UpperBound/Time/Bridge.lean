/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bridge — re-export of Time.lean for sub-modules

The Time/ sub-modules (CRSOdd, CRSEven, etc.) need definitions from Time.lean
(PEMProtocolCoupled, IsConsensusConfig, etc.) but cannot import Time.lean
directly (that would create a circular dependency). This bridge re-exports
the needed definitions.
-/

import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time

