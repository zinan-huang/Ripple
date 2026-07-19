import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch17 :
    [1000002791, 1000002803, 1000002821, 1000002823, 1000002827, 1000002907, 1000002937, 1000002989].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
