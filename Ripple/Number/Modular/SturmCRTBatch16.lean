import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch16 :
    [1000002571, 1000002581, 1000002607, 1000002631, 1000002637, 1000002649, 1000002667, 1000002727].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
