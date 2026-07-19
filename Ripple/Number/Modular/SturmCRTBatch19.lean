import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch19 :
    [1000003157, 1000003163, 1000003211, 1000003241, 1000003247, 1000003253, 1000003267, 1000003271].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
