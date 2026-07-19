import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch26 :
    [1000004233, 1000004249, 1000004251, 1000004263, 1000004321, 1000004329, 1000004381, 1000004389].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
