import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch06 :
    [1000000787, 1000000801, 1000000829, 1000000861, 1000000871, 1000000891, 1000000901, 1000000919].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
