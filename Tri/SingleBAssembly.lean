/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBFinalConsensus

/-!
# Unconditional Single-B consensus assembly

This composes the already-proved early, middle, high-cap, constant-base late
ladder, and the direct physical co-level final block.
-/

namespace Tri

open scoped ENNReal

/-- Single-B consensus horizon. -/
def singleConsensusHorizon (n gamma : Nat) : Nat :=
  singleEarlyLadderHorizon n gamma +
    singleMiddleHighCapConstLateHorizon n gamma +
    singleFinalHorizon n gamma

/-- Single-B consensus error after installing the final power-law block. -/
noncomputable def singleConsensusError (n gamma : Nat) : ENNReal :=
  singleEarlyLadderError n gamma +
    singleMiddleHighCapConstLateError n gamma +
    2 * (n : ENNReal)⁻¹ ^ ((1 / 64 : Real) * (gamma : Real))

/-- Assembly from the paper Single-B initial predicate to all-`X` consensus. -/
theorem singleConsensus_reaches
    (n gamma : Nat) (hn : 2 <= n)
    (hlog : 1024 <= Nat.log 2 n) (hgamma : 1 <= gamma)
    (hsize : 6 * gamma * Nat.log 2 n <= n) :
    Reaches (singleStateStep n hn) (singleConsensusHorizon n gamma)
      (SingleBEarlyInitial n gamma)
      (fun s : SingleState n => BiXConsensus n s.1)
      (singleConsensusError n gamma) := by
  have he := singleEarly_reaches n hn gamma
    (hlog.trans' (by norm_num)) hgamma
  have hm :=
    singleMiddle_highCap_constLate_reaches_target n gamma hn hlog hgamma
      hsize
  have hfinal :=
    singleFinalConsensus_reaches_power n hn gamma hlog hgamma hsize
  have h := (he.comp hm).comp hfinal
  simpa [singleConsensusHorizon, singleConsensusError, add_assoc] using h

end Tri

#print axioms Tri.singleConsensusHorizon
#print axioms Tri.singleConsensusError
#print axioms Tri.singleConsensus_reaches
