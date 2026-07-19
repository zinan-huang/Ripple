import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch27 :
    [1000004437, 1000004449, 1000004459, 1000004497, 1000004507, 1000004519, 1000004539, 1000004567].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
