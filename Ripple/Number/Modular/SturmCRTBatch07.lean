import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch07 :
    [1000000931, 1000000933, 1000000993, 1000001011, 1000001021, 1000001053, 1000001087, 1000001099].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
