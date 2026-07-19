import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch23 :
    [1000003751, 1000003769, 1000003777, 1000003787, 1000003793, 1000003843, 1000003853, 1000003871].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
