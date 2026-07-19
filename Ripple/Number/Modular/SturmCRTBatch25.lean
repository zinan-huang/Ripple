import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch25 :
    [1000003987, 1000003999, 1000004023, 1000004059, 1000004099, 1000004119, 1000004123, 1000004207].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
