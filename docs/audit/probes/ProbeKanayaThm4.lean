import Ripple.PopulationProtocol.SSEM.UpperBound.Thm4Final

/-! Non-vacuity probe for `P_EM_paper_thm4_time`: an explicit configuration of the finite paper
instance at `n = 1608` (every agent Resetting-free in the second summand: rank-less, follower,
answer `φ`, timer `0`, opinion `A`), to which both conclusions apply. -/

namespace Ripple.PopulationProtocol.SSEM.ProbeKanayaThm4

open Ripple.PopulationProtocol.SSEM Ripple.PopulationProtocol.SSEM.Probability

/-- An explicit configuration of the paper instance at `n = 1608`. -/
def C₀ : Config (PEMFinState 1608 (7 * (40 + 4)) (208 * 1608) (rmaxPaper 1608) (32 * 1608))
    Opinion 1608 :=
  fun _ => (Sum.inr (Sum.inl (0, Leader.F, Answer.phi, 0)), Opinion.A)

theorem probe_expected :
    expectedParallelTimeToSilent (protocolPEMPaperFin 1608 40 208 32 (by norm_num))
      (by norm_num) C₀ ≤ 5215 * (1608 : ENNReal) :=
  P_EM_paper_thm4_time.1 1608 le_rfl (by norm_num) (by norm_num) C₀

theorem probe_whp :
    probNotHitBy (protocolPEMPaperFin 1608 40 208 32 (by norm_num)) (by norm_num) C₀
        (fun C => C.isSilent (protocolPEMPaperFin 1608 40 208 32 (by norm_num)))
        (4172 * 1608 ^ 2 * Nat.clog 2 1608) ≤ (1608 : ENNReal)⁻¹ :=
  P_EM_paper_thm4_time.2 1608 le_rfl (by norm_num) (by norm_num) C₀

end Ripple.PopulationProtocol.SSEM.ProbeKanayaThm4

#print axioms Ripple.PopulationProtocol.SSEM.ProbeKanayaThm4.probe_expected
#print axioms Ripple.PopulationProtocol.SSEM.ProbeKanayaThm4.probe_whp
