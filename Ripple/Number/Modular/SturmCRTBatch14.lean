import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch14 :
    [1000002139, 1000002149, 1000002161, 1000002173, 1000002187, 1000002193, 1000002233, 1000002239].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
