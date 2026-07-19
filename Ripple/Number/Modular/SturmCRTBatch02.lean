import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch02 :
    [1000000097, 1000000103, 1000000123, 1000000181, 1000000207, 1000000223, 1000000241, 1000000271].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
