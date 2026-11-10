/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kanaya et al. Theorem 4, time part, for the paper instance of P_EM

The stage bounds of P3 compose to the uniform window (P3 Theorem W): for `n ≥ 1608`, from every
flat configuration whose agents satisfy `GoodPEM` (timer `≤ 308`, errorcount `≤ 208 n`,
resetcount `≤ ⌈60 ln n⌉`, delaytimer `≤ 32 n`, children `≤ 2`), the silent consensus is reached
within `1043 n²` interactions with probability at least `1/5` (`P_EM_paper_window`).

Through the state simulation onto the finite paper instance (`trank = 40`, `Emax = 208 n`,
`Dmax = 32 n`) and the restart lemmas this gives, for `n ≥ 1608` and every finite configuration:
expected parallel time to silence at most `5215 n`, and silence within `4172 n² ⌈log₂ n⌉`
interactions except with probability at most `1/n` (`P_EM_paper_thm4_time`). `kanayaThm4Time`
is the existential form.
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.StagesA
import Ripple.PopulationProtocol.SSEM.UpperBound.TreeRankingStage
import Ripple.PopulationProtocol.SSEM.UpperBound.StagesSRankSort
import Ripple.PopulationProtocol.SSEM.UpperBound.StagesB1Z

namespace Ripple.PopulationProtocol.SSEM

/-- **P3 Theorem W** for the flat paper instance. -/
theorem P_EM_paper_window : PEMPaperWindow 40 208 32 1608 1043 5⁻¹ :=
  pemPaperWindow_of_stages stageA stageA'
    (epoch1_of_stages stageB1 stageB2 stageB34 stageB56) stageC
    (epoch2_of_stages stageB1Z stageB2M stageB34M stageB56M) stageE

/-- **Kanaya et al. Theorem 4, time part, with explicit constants**: for the finite paper
instance with `trank = 40`, `Emax = 208 n`, `Dmax = 32 n` and every `n ≥ 1608`, the expected
parallel time to silence is at most `5215 n` from every configuration, and silence is reached
within `4172 n² ⌈log₂ n⌉` interactions except with probability at most `1/n`. -/
theorem P_EM_paper_thm4_time :
    KanayaThm4TimeExpected 40 208 32 1608 5215 ∧ KanayaThm4TimeWhp 40 208 32 1608 4172 :=
  kanayaThm4Time_explicit_of_window P_EM_paper_window

/-- **Kanaya et al. Theorem 4, time part** (existential form of `P_EM_paper_thm4_time`). -/
theorem kanayaThm4Time : KanayaThm4Time :=
  kanayaThm4Time_of_window P_EM_paper_window

end Ripple.PopulationProtocol.SSEM
