/-
Ripple.BoundedUniversality.GPAC.Combined
--------------------
Route 3 main theorem: Q(π)-bounded GPAC is Turing universal.
-/

import Ripple.BoundedUniversality.GPAC.BoundedSurrogate
import Ripple.BoundedUniversality.GPAC.BGP

namespace Ripple.BoundedUniversality.GPAC

open Ripple.BoundedUniversality.Core

/-- Route 3 composition. Caveat: it inherits the
vacuity of `bounded_surrogate_strong`: the bounded witness has the zero field, so this conclusion
carries no information about the input system. The faithful bounded
compilation is `Ripple.bounded_compilation` / `Ripple.bounded_compilation_certified` ([BAC]
Thm 3.3, `Ripple/Core/SurrogateCompilation.lean`), for number computation by `PolyPIVP`s; a
faithful compilation of `BoundedTMSimulates` is not formalized. -/
theorem route3_Qpi_bounded_universal :
    ∃ P : PIVP (↥QpiSubfield), Nonempty (BoundedTMSimulates P) := by
  obtain ⟨P, ⟨hP⟩⟩ := BGP_Qpi_universal_exists
  exact bounded_surrogate_strong P ⟨hP⟩

end Ripple.BoundedUniversality.GPAC
