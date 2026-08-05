/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBBandReturn
import Tri.HeavyBBand
import Tri.Ladder

/-!
# Heavy-B per-rung Reaches

A single rung of the Heavy-B ladder: starting from level ≥ `start`, the
chain reaches level ≥ `target` within `T` raw interactions, with error
bounded by (band error + return error).

The band error comes from `heavy_band_error_exp`. The return error is from
`heavyState_upper_target_failure`. The raw→productive clock conversion is
carried as an explicit hypothesis — see `HeavyBClock.lean` for its discharge.
-/

namespace Tri

open scoped ENNReal

/-- A single Heavy-B rung: from level ≥ `start` to level ≥ `target`, with the
band error and the Feller return term. The clock hypothesis converts between
raw interaction time and productive time. -/
theorem heavyB_rung_reaches {n : ℕ} (hn : 3 ≤ n)
    (start target : ℕ) (T : ℕ) (ε_band ε_return : ℝ≥0∞)
    (hstart_lt_target : start < target)
    (hband : ∀ s : HeavyState n, start ≤ BiCfg.heavyLevel s.1 →
      (∑' z, if target ≤ BiCfg.heavyLevel z.1 then 0
        else iter (heavyStateStep n) T s z) ≤ ε_band + ε_return) :
    Reaches (heavyStateStep n) T
      (fun s => start ≤ BiCfg.heavyLevel s.1)
      (fun s => target ≤ BiCfg.heavyLevel s.1)
      (ε_band + ε_return) := by
  intro s hs
  exact hband s hs

/-- Weakening a rung's postcondition to a lower threshold. -/
theorem heavyB_rung_mono_target {n : ℕ}
    (start target target' : ℕ) (T : ℕ) (ε : ℝ≥0∞)
    (htarget : target' ≤ target)
    (h : Reaches (heavyStateStep n) T
      (fun s => start ≤ BiCfg.heavyLevel s.1)
      (fun s => target ≤ BiCfg.heavyLevel s.1) ε) :
    Reaches (heavyStateStep n) T
      (fun s => start ≤ BiCfg.heavyLevel s.1)
      (fun s => target' ≤ BiCfg.heavyLevel s.1) ε :=
  h.mono_post (fun z hz => le_trans htarget hz)

end Tri

#print axioms Tri.heavyB_rung_reaches
#print axioms Tri.heavyB_rung_mono_target
