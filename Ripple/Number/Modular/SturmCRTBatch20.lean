import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch20 :
    [1000003273, 1000003283, 1000003309, 1000003337, 1000003351, 1000003357, 1000003373, 1000003379].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
