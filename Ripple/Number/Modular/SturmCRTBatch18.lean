import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch18 :
    [1000003009, 1000003013, 1000003051, 1000003057, 1000003097, 1000003111, 1000003133, 1000003153].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
