import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch01 :
    [999999929, 999999937, 1000000007, 1000000009, 1000000021, 1000000033, 1000000087, 1000000093].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
