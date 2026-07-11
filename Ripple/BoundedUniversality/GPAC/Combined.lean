/-
Ripple.BoundedUniversality.GPAC.Combined
--------------------
Route 3 main theorem: Q(π)-bounded GPAC is Turing universal.
-/

import Ripple.BoundedUniversality.GPAC.BoundedSurrogate
import Ripple.BoundedUniversality.GPAC.BGP

namespace Ripple.BoundedUniversality.GPAC

open Ripple.BoundedUniversality.Core

theorem route3_Qpi_bounded_universal :
    ∃ P : PIVP (↥QpiSubfield), Nonempty (BoundedTMSimulates P) := by
  obtain ⟨P, ⟨hP⟩⟩ := BGP_Qpi_universal_exists
  exact bounded_surrogate_strong P ⟨hP⟩

end Ripple.BoundedUniversality.GPAC
