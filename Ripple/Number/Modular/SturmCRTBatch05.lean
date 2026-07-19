import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch05 :
    [1000000531, 1000000579, 1000000607, 1000000613, 1000000637, 1000000663, 1000000711, 1000000753].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
