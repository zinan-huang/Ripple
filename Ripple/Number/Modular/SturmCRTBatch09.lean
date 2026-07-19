import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch09 :
    [1000001279, 1000001311, 1000001329, 1000001333, 1000001351, 1000001371, 1000001393, 1000001413].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
