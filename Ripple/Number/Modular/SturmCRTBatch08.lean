import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch08 :
    [1000001137, 1000001161, 1000001203, 1000001213, 1000001237, 1000001263, 1000001269, 1000001273].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
