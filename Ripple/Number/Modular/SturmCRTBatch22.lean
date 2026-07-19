import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch22 :
    [1000003601, 1000003621, 1000003643, 1000003651, 1000003663, 1000003679, 1000003709, 1000003747].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
