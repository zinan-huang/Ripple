import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch13 :
    [1000001917, 1000001927, 1000001957, 1000001963, 1000001969, 1000002043, 1000002089, 1000002103].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
