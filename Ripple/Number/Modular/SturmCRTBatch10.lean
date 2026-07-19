import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch10 :
    [1000001447, 1000001449, 1000001491, 1000001501, 1000001531, 1000001537, 1000001539, 1000001581].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
