import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch11 :
    [1000001617, 1000001621, 1000001633, 1000001647, 1000001663, 1000001677, 1000001699, 1000001759].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
