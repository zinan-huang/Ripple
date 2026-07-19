import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch03 :
    [1000000289, 1000000297, 1000000321, 1000000349, 1000000363, 1000000403, 1000000409, 1000000411].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
