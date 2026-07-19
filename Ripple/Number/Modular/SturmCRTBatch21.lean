import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch21 :
    [1000003397, 1000003469, 1000003471, 1000003513, 1000003519, 1000003559, 1000003577, 1000003579].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
