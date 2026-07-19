import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch15 :
    [1000002277, 1000002307, 1000002359, 1000002361, 1000002431, 1000002449, 1000002457, 1000002499].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
