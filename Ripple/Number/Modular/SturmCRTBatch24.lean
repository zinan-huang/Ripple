import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch24 :
    [1000003889, 1000003891, 1000003909, 1000003919, 1000003931, 1000003951, 1000003957, 1000003967].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
