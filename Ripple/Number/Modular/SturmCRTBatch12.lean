import Ripple.Number.Modular.SturmCRTModNat

namespace Ripple.Number.Modular

set_option maxHeartbeats 0 in
theorem sturmCRTCheck_batch12 :
    [1000001773, 1000001789, 1000001791, 1000001801, 1000001803, 1000001819, 1000001857, 1000001887].all
      (fun p => sturmCRTCheckAllFast p) = true := by native_decide

end Ripple.Number.Modular
