/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBLevelPhaseStructural
import Tri.SingleBProductiveTail

/-!
# Parameterized Single-B late rung

This file connects the structural level phase to the late productive clock.
The wrapper keeps all constants symbolic: concrete dyadic stages only need to
inhabit the additive side conditions.  In particular, the creation boundary is
handled by `singleBand_boundary_deadline_of_start_co`, not by a lazy `T < H`
budget.
-/

namespace Tri

open scoped ENNReal

/-- The resolved-clock error inserted into a structural Single-B late rung. -/
noncomputable def singleLateResolvedClockError
    (n d c D H _M K T : Nat) : ENNReal :=
  ((1 - singleBandProductivity n d c)
      + singleBandProductivity n d c * ((1 : ENNReal) / 2)) ^ T /
    ((1 : ENNReal) / 2) ^ K
  + ENNReal.ofReal (Real.exp (-((D : Real) ^ 2 / (2 * (H : Real)))))

/-- The structural phase error with the resolved Single-B late clock installed. -/
noncomputable def singleLateRungError
    (n d c D D₂ H M K T : Nat)
    (w η : ENNReal) (Bw Lentry targetΛ Lhi Mhi Bret sret : Nat)
    (epsRet : ENNReal) : ENNReal :=
  singleLevelPhaseStructuralError w η Bw Lentry targetΛ M
    (singleLateResolvedClockError n d c D H M K T)
    D D₂ H Bret sret T n epsRet Lhi Mhi

/-- Parameterized late rung: the structural boundary stream and the
resolution-masked productive clock are discharged from additive side
conditions. -/
theorem singleLate_rung_resolved
    {n : Nat} (hn : 2 <= n)
    (aLoΛ hiΛ D D₂ H p qRat Bw M K T Lentry Lexit sret Bret Lhi Mhi
      startCoCap d c : Nat)
    (hH : 0 < H) (hq : qRat ≠ 0)
    (w v η u epsRet : ENNReal) (hε1 : epsRet <= 1)
    (hu : u = (p : ENNReal) / (qRat : ENNReal))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w <= η)
    (hwv : w * v = 1) (hw1 : w <= 1) (hw0 : w ≠ 0)
    (hη1 : 1 <= η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤)
    (hlive : forall q : SingleLedger n,
      ¬ SingleBandFrozen n aLoΛ hiΛ D H q ->
        exists a : Nat, q.CorrectedLevel (a + 1) ∧
          qRat * q.cfg.1.y <= p * q.cfg.1.x)
    (hBw : aLoΛ + Bw = Lentry)
    (hvac : aLoΛ + D₂ <= Lexit)
    (hLn : n + 1 <= Lexit)
    (hBret : Lexit + Bret = 2 * n + 1)
    (hslack : Lexit + sret + D <= hiΛ)
    (hLhiReturn : Lexit + sret + D <= Lhi)
    (htargetHi : Lexit + D + 1 <= hiΛ)
    (hK : H + M <= K)
    (hgap : n + D + d = aLoΛ + 1)
    (hcoClock : hiΛ + 2 * M + 2 * c <= 2 * n + 1)
    (hpp1 : singleBandProductivity n d c <= 1)
    (hstartCo : forall s : SingleState n,
      Lentry <= s.1.doubleLevel -> s.1.doubleCoLevel <= startCoCap)
    (hboundaryH : startCoCap + 2 * Mhi + D + 1 <= H) :
    Reaches (singleStateStep n hn) T
      (fun s : SingleState n => Lentry <= s.1.doubleLevel)
      (fun s : SingleState n => Lexit <= s.1.doubleLevel)
      (singleLateRungError n d c D D₂ H M K T w η Bw Lentry
        (Lexit + D) Lhi Mhi Bret sret epsRet) := by
  refine singleBand_reaches_level_structural hn
    aLoΛ hiΛ D D₂ H p qRat Bw M T Lentry Lexit sret Bret Lhi Mhi
    hH hq w v η u
    (singleLateResolvedClockError n d c D H M K T)
    epsRet hε1 hu hrel hwη hwv hw1 hw0 hη1 hwt hηt hlive
    hBw hvac hLn hBret hslack hLhiReturn ?_ ?_
  · intro s hs q hz hnotBad hboundary _hbelow
    exact singleBand_boundary_deadline_of_start_co hn aLoΛ hiΛ D H
      startCoCap Mhi s q (hstartCo s hs) hboundaryH hz hnotBad hboundary
  · intro s _hs
    exact singleBand_hclock_resolved_with_creation_entry hn
      aLoΛ hiΛ (Lexit + D) D H M K T d c htargetHi hH hK hgap
      hcoClock hpp1 s

section Inhabitation

example :
    singleLateResolvedClockError 16 3 2 1 5 2 8 10 =
      ((1 - singleBandProductivity 16 3 2)
      + singleBandProductivity 16 3 2 * ((1 : ENNReal) / 2)) ^ 10 /
        ((1 : ENNReal) / 2) ^ 8
      + ENNReal.ofReal (Real.exp (-((1 : Real) ^ 2 / (2 * (5 : Real))))) := by
  simp [singleLateResolvedClockError]

end Inhabitation

end Tri

#print axioms Tri.singleLateResolvedClockError
#print axioms Tri.singleLateRungError
#print axioms Tri.singleLate_rung_resolved
