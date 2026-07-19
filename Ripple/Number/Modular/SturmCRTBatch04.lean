import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch04 :
    [1000000427, 1000000433, 1000000439, 1000000447, 1000000453, 1000000459, 1000000483, 1000000513].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
