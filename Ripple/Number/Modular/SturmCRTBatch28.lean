import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch28 :
    [1000004569, 1000004581, 1000004609, 1000004611, 1000004627, 1000004633, 1000004647].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
