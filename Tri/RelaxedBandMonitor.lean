/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedBand
import Tri.DoubleBAssembly

/-!
# Physical continuation monitor for relaxed finite bands

The finite-band estimates live on `relaxedBandStop`, which freezes both the
productive counter and the `X` coordinate at the first lower or upper boundary.
The physical relaxed chain must not be frozen. This file couples the two
without changing either proved kernel:

* `physical` always evolves by `relaxedTriChain`;
* before the first boundary hit, `shadow` evolves by `relaxedCount`;
* after the first boundary hit, `shadow` is held fixed while `physical`
  continues to evolve.

Thus the physical projection is exactly the raw chain and the shadow projection
is exactly `relaxedBandStop`. A final set-cover lemma exposes the only extra
term needed to conclude a physical endpoint statement: the upper checkpoint
was hit, but the physical chain subsequently backslid below it.
-/

namespace Tri

open scoped ENNReal

/-- Whether the counted shadow is still live or has remembered its first band
exit. -/
inductive RelaxedBandMonitorMark
  | live
  | hit
  deriving DecidableEq, Repr

/-- Raw data of the continuation monitor. -/
structure RelaxedBandMonitorRaw where
  physical : ℕ
  shadow : ℕ × ℕ
  mark : RelaxedBandMonitorMark
  deriving DecidableEq, Repr

/-- Coherence between the physical coordinate, counted shadow, and remembered
first-hit status. -/
def RelaxedBandMonitorCoherent
    (lower target : ℕ) (q : RelaxedBandMonitorRaw) : Prop :=
  match q.mark with
  | .live =>
      q.shadow.1 = q.physical ∧
        ¬ RelaxedBandBoundary lower target q.shadow
  | .hit => RelaxedBandBoundary lower target q.shadow

instance relaxedBandMonitorCoherentDecidable
    (lower target : ℕ) (q : RelaxedBandMonitorRaw) :
    Decidable (RelaxedBandMonitorCoherent lower target q) := by
  unfold RelaxedBandMonitorCoherent
  cases q.mark <;> infer_instance

/-- Invariant state space of the continuation monitor. -/
def RelaxedBandMonitor (lower target : ℕ) :=
  {q : RelaxedBandMonitorRaw //
    RelaxedBandMonitorCoherent lower target q}

namespace RelaxedBandMonitor

variable {lower target : ℕ}

/-- Physical `X` coordinate. -/
def physical (q : RelaxedBandMonitor lower target) : ℕ := q.1.physical

/-- Counted first-hit shadow. -/
def shadow (q : RelaxedBandMonitor lower target) : ℕ × ℕ := q.1.shadow

/-- The remembered upper checkpoint has been hit. -/
def UpperHit (q : RelaxedBandMonitor lower target) : Prop :=
  target ≤ q.shadow.1

instance upperHitDecidable : DecidablePred (@UpperHit lower target) := by
  intro q
  unfold UpperHit
  infer_instance

end RelaxedBandMonitor

/-- Deterministic monitor update after the raw chain draws its next physical
`X` count. -/
def relaxedBandMonitorNext
    (lower target : ℕ) (q : RelaxedBandMonitorRaw) (x' : ℕ) :
    RelaxedBandMonitorRaw :=
  match q.mark with
  | .hit =>
      { physical := x'
        shadow := q.shadow
        mark := .hit }
  | .live =>
      let z : ℕ × ℕ :=
        (x', if x' = q.physical then q.shadow.2 else q.shadow.2 + 1)
      if RelaxedBandBoundary lower target z then
        { physical := x'
          shadow := z
          mark := .hit }
      else
        { physical := x'
          shadow := z
          mark := .live }

@[simp] theorem relaxedBandMonitorNext_physical
    (lower target : ℕ) (q : RelaxedBandMonitorRaw) (x' : ℕ) :
    (relaxedBandMonitorNext lower target q x').physical = x' := by
  cases hmark : q.mark with
  | live =>
      unfold relaxedBandMonitorNext
      rw [hmark]
      dsimp only
      by_cases hx : x' = q.physical
      · rw [if_pos hx]
        by_cases hb :
            RelaxedBandBoundary lower target (x', q.shadow.2)
        · rw [if_pos hb]
        · rw [if_neg hb]
      · rw [if_neg hx]
        by_cases hb :
            RelaxedBandBoundary lower target (x', q.shadow.2 + 1)
        · rw [if_pos hb]
        · rw [if_neg hb]
  | hit =>
      simp [relaxedBandMonitorNext, hmark]

@[simp] theorem relaxedBandMonitorNext_shadow
    (lower target : ℕ) (q : RelaxedBandMonitorRaw) (x' : ℕ) :
    (relaxedBandMonitorNext lower target q x').shadow =
      match q.mark with
      | .hit => q.shadow
      | .live =>
          (x', if x' = q.physical then q.shadow.2 else q.shadow.2 + 1) := by
  cases hmark : q.mark with
  | live =>
      unfold relaxedBandMonitorNext
      rw [hmark]
      dsimp only
      by_cases hx : x' = q.physical
      · rw [if_pos hx]
        by_cases hb :
            RelaxedBandBoundary lower target (x', q.shadow.2)
        · rw [if_pos hb]
        · rw [if_neg hb]
      · rw [if_neg hx]
        by_cases hb :
            RelaxedBandBoundary lower target (x', q.shadow.2 + 1)
        · rw [if_pos hb]
        · rw [if_neg hb]
  | hit =>
      simp [relaxedBandMonitorNext, hmark]

/-- The deterministic update preserves monitor coherence. -/
theorem relaxedBandMonitorNext_coherent
    (lower target : ℕ) (q : RelaxedBandMonitorRaw)
    (hq : RelaxedBandMonitorCoherent lower target q) (x' : ℕ) :
    RelaxedBandMonitorCoherent lower target
      (relaxedBandMonitorNext lower target q x') := by
  cases hmark : q.mark with
  | live =>
      unfold relaxedBandMonitorNext
      rw [hmark]
      dsimp only
      by_cases hx : x' = q.physical
      · rw [if_pos hx]
        by_cases hb :
            RelaxedBandBoundary lower target (x', q.shadow.2)
        · rw [if_pos hb]
          exact hb
        · rw [if_neg hb]
          exact ⟨rfl, hb⟩
      · rw [if_neg hx]
        by_cases hb :
            RelaxedBandBoundary lower target (x', q.shadow.2 + 1)
        · rw [if_pos hb]
          exact hb
        · rw [if_neg hb]
          exact ⟨rfl, hb⟩
  | hit =>
      unfold relaxedBandMonitorNext
      rw [hmark]
      simpa [RelaxedBandMonitorCoherent, hmark] using hq

/-- The physical continuation monitor. The random draw is always the raw
relaxed `X` step; only the deterministic bookkeeping depends on first-hit
status. -/
noncomputable def relaxedBandMonitorStep
    (r : RelaxedRate) (n lower target : ℕ) :
    RelaxedBandMonitor lower target → PMF (RelaxedBandMonitor lower target) :=
  fun q =>
    (relaxedTriChain r n q.1.physical).map
      (fun x' =>
        ⟨relaxedBandMonitorNext lower target q.1 x',
          relaxedBandMonitorNext_coherent lower target q.1 q.2 x'⟩)

/-- The physical one-step projection is exactly the raw relaxed chain. -/
theorem relaxedBandMonitorStep_map_physical
    (r : RelaxedRate) (n lower target : ℕ)
    (q : RelaxedBandMonitor lower target) :
    (relaxedBandMonitorStep r n lower target q).map
        RelaxedBandMonitor.physical =
      relaxedTriChain r n q.physical := by
  unfold relaxedBandMonitorStep RelaxedBandMonitor.physical
  rw [PMF.map_comp]
  convert PMF.map_id (relaxedTriChain r n q.1.physical) using 1
  congr 1
  funext x'
  exact relaxedBandMonitorNext_physical lower target q.1 x'

/-- The counted shadow one-step projection is exactly the proved two-boundary
frozen counted chain. -/
theorem relaxedBandMonitorStep_map_shadow
    (r : RelaxedRate) (n lower target : ℕ)
    (q : RelaxedBandMonitor lower target) :
    (relaxedBandMonitorStep r n lower target q).map
        RelaxedBandMonitor.shadow =
      relaxedBandStop r n lower target q.shadow := by
  rcases q with ⟨q, hq⟩
  cases hmark : q.mark with
  | live =>
      have hqLive :
          q.shadow.1 = q.physical ∧
            ¬ RelaxedBandBoundary lower target q.shadow := by
        simpa [RelaxedBandMonitorCoherent, hmark] using hq
      unfold relaxedBandMonitorStep RelaxedBandMonitor.shadow
      rw [PMF.map_comp]
      unfold relaxedBandStop
      rw [freeze_of_not_mem q.shadow hqLive.2]
      unfold relaxedCount
      rw [hqLive.1]
      congr 1
      funext x'
      simp only [Function.comp_apply,
        relaxedBandMonitorNext_shadow, hmark]
  | hit =>
      have hqHit : RelaxedBandBoundary lower target q.shadow := by
        simpa [RelaxedBandMonitorCoherent, hmark] using hq
      unfold relaxedBandMonitorStep RelaxedBandMonitor.shadow
      rw [PMF.map_comp]
      unfold relaxedBandStop
      rw [freeze_of_mem q.shadow hqHit]
      convert
        PMF.map_const
          (relaxedTriChain r n q.physical) q.shadow using 1
      congr 1
      funext x'
      simp [Function.comp_apply,
        relaxedBandMonitorNext_shadow, hmark]

/-- Exact physical projection at every finite raw horizon. -/
theorem iter_relaxedBandMonitor_map_physical
    (r : RelaxedRate) (n lower target T : ℕ)
    (q : RelaxedBandMonitor lower target) :
    iter (relaxedTriChain r n) T q.physical =
      (iter (relaxedBandMonitorStep r n lower target) T q).map
        RelaxedBandMonitor.physical :=
  iter_map_equivariant
    (relaxedBandMonitorStep r n lower target)
    (relaxedTriChain r n)
    RelaxedBandMonitor.physical
    (relaxedBandMonitorStep_map_physical r n lower target)
    T q

/-- Exact frozen counted-shadow projection at every finite horizon. -/
theorem iter_relaxedBandMonitor_map_shadow
    (r : RelaxedRate) (n lower target T : ℕ)
    (q : RelaxedBandMonitor lower target) :
    iter (relaxedBandStop r n lower target) T q.shadow =
      (iter (relaxedBandMonitorStep r n lower target) T q).map
        RelaxedBandMonitor.shadow :=
  iter_map_equivariant
    (relaxedBandMonitorStep r n lower target)
    (relaxedBandStop r n lower target)
    RelaxedBandMonitor.shadow
    (relaxedBandMonitorStep_map_shadow r n lower target)
    T q

/-- Initial coherent live monitor with a zero productive counter. -/
def relaxedBandMonitorInit
    (lower target start : ℕ)
    (hstart : lower < start ∧ start < target) :
    RelaxedBandMonitor lower target :=
  ⟨{ physical := start
     shadow := (start, 0)
     mark := .live }, by
    change start = start ∧ ¬ (start ≤ lower ∨ target ≤ start)
    exact ⟨rfl, by omega⟩⟩

/-- Failure of remembered upper entry has exactly the same mass as failure in
the proved frozen counted band. -/
theorem relaxedBandMonitor_notUpper_mass_eq
    (r : RelaxedRate) (n lower target T : ℕ)
    (q : RelaxedBandMonitor lower target) :
    (∑' s, if RelaxedBandMonitor.UpperHit s then 0 else
        iter (relaxedBandMonitorStep r n lower target) T q s) =
      ∑' z, if target ≤ z.1 then 0 else
        iter (relaxedBandStop r n lower target) T q.shadow z := by
  rw [masked_eq_expect, masked_eq_expect,
    iter_relaxedBandMonitor_map_shadow r n lower target T q,
    expect_map]
  rfl

/-- Physical endpoint failure is covered by failure to have ever reached the
upper checkpoint plus the explicit post-hit backsliding event. -/
theorem relaxedBandMonitor_physical_failure_split
    (r : RelaxedRate) (n lower target T : ℕ)
    (q : RelaxedBandMonitor lower target) :
    (∑' s, if target ≤ s.physical then 0 else
        iter (relaxedBandMonitorStep r n lower target) T q s) ≤
      (∑' s, if RelaxedBandMonitor.UpperHit s then 0 else
          iter (relaxedBandMonitorStep r n lower target) T q s) +
      ∑' s, if RelaxedBandMonitor.UpperHit s ∧ s.physical < target then
          iter (relaxedBandMonitorStep r n lower target) T q s else 0 := by
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun s => ?_
  by_cases hp : target ≤ s.physical
  · simp [hp]
  · have hplt : s.physical < target := by omega
    by_cases hu : RelaxedBandMonitor.UpperHit s
    · simp [hp, hplt, hu]
    · simp [hp, hu]

/-- Raw-chain endpoint failure is exactly physical monitor endpoint failure. -/
theorem relaxedBandMonitor_physical_failure_eq_raw
    (r : RelaxedRate) (n lower target T : ℕ)
    (q : RelaxedBandMonitor lower target) :
    (∑' x, if target ≤ x then 0 else
        iter (relaxedTriChain r n) T q.physical x) =
      ∑' s, if target ≤ s.physical then 0 else
        iter (relaxedBandMonitorStep r n lower target) T q s := by
  rw [masked_eq_expect, masked_eq_expect,
    iter_relaxedBandMonitor_map_physical r n lower target T q,
    expect_map]

/-- The complete finite-band estimate transferred to remembered first-hit
monitoring of the physical raw chain. -/
theorem relaxedBandMonitor_phase_fail
    (r : RelaxedRate)
    (n lower target bHi gap M T yLo : ℕ)
    (beta slack tau : NNReal)
    (wp p p' : ℝ≥0∞)
    (h3 : 3 ≤ n) (htarget : target ≤ n)
    (hband : lower + bHi + 2 = n)
    (hyLo : target + yLo = n + 1)
    (hbeta1 : 1 ≤ beta)
    (hslack : r.fire + slack ≤ beta)
    (htau : tau * (bHi : NNReal) ≤ slack)
    (hB : 1 < beta + tau)
    (hcorner :
      beta * (bHi + 1 : NNReal) ≤
        r.fire * (lower + 1 : NNReal))
    (hwp1 : wp ≤ 1) (hwp0 : wp ≠ 0) (hp : p + p' = 1)
    (hpFloor :
      p ≤ relaxedBandProductiveFloor r n (lower + 1) yLo)
    (q0 : RelaxedBandMonitor lower target)
    (hstart : q0.shadow.1 = lower + gap)
    (hstartLive : lower < q0.shadow.1 ∧ q0.shadow.1 < target)
    (hc0 : q0.shadow.2 = 0) :
    (∑' s, if RelaxedBandMonitor.UpperHit s then 0 else
        iter (relaxedBandMonitorStep r n lower target) T q0 s) ≤
      (beta : ℝ≥0∞)⁻¹ ^ gap +
      (relaxedDirW (beta + tau) : ℝ≥0∞) ^ q0.shadow.1 /
        ((relaxedDirW (beta + tau) : ℝ≥0∞) ^ (target - 1) *
          (relaxedDirEta (beta + tau) : ℝ≥0∞) ^ M) +
      (p' + p * wp) ^ T * 1 / wp ^ M := by
  rw [relaxedBandMonitor_notUpper_mass_eq]
  calc
    (∑' z, if target ≤ z.1 then 0 else
        iter (relaxedBandStop r n lower target) T q0.shadow z) =
      ∑' z, if z.1 + 1 ≤ target then
        iter (relaxedBandStop r n lower target) T q0.shadow z else 0 := by
          apply tsum_congr
          intro z
          by_cases hz : target ≤ z.1
          · have hn : ¬ z.1 + 1 ≤ target := by omega
            simp [hz, hn]
          · have hy : z.1 + 1 ≤ target := by omega
            simp [hz, hy]
    _ ≤ (beta : ℝ≥0∞)⁻¹ ^ gap +
        (relaxedDirW (beta + tau) : ℝ≥0∞) ^ q0.shadow.1 /
          ((relaxedDirW (beta + tau) : ℝ≥0∞) ^ (target - 1) *
            (relaxedDirEta (beta + tau) : ℝ≥0∞) ^ M) +
        (p' + p * wp) ^ T * 1 / wp ^ M :=
      relaxedBand_phase_fail
        r n lower target bHi gap M T yLo beta slack tau wp p p'
        h3 htarget hband hyLo hbeta1 hslack htau hB hcorner
        hwp1 hwp0 hp hpFloor q0.shadow hstart hstartLive hc0

/-- Strongest direct transfer back to a physical raw-chain endpoint. The
caller supplies an honest bound on post-hit upper-checkpoint backsliding. -/
theorem relaxedTriChain_phase_fail_of_backslide
    (r : RelaxedRate)
    (n lower target bHi gap M T yLo : ℕ)
    (beta slack tau : NNReal)
    (wp p p' delta : ℝ≥0∞)
    (h3 : 3 ≤ n) (htarget : target ≤ n)
    (hband : lower + bHi + 2 = n)
    (hyLo : target + yLo = n + 1)
    (hbeta1 : 1 ≤ beta)
    (hslack : r.fire + slack ≤ beta)
    (htau : tau * (bHi : NNReal) ≤ slack)
    (hB : 1 < beta + tau)
    (hcorner :
      beta * (bHi + 1 : NNReal) ≤
        r.fire * (lower + 1 : NNReal))
    (hwp1 : wp ≤ 1) (hwp0 : wp ≠ 0) (hp : p + p' = 1)
    (hpFloor :
      p ≤ relaxedBandProductiveFloor r n (lower + 1) yLo)
    (q0 : RelaxedBandMonitor lower target)
    (hstart : q0.shadow.1 = lower + gap)
    (hstartLive : lower < q0.shadow.1 ∧ q0.shadow.1 < target)
    (hc0 : q0.shadow.2 = 0)
    (hbackslide :
      (∑' s, if RelaxedBandMonitor.UpperHit s ∧ s.physical < target then
          iter (relaxedBandMonitorStep r n lower target) T q0 s else 0) ≤
        delta) :
    (∑' x, if target ≤ x then 0 else
        iter (relaxedTriChain r n) T q0.physical x) ≤
      ((beta : ℝ≥0∞)⁻¹ ^ gap +
        (relaxedDirW (beta + tau) : ℝ≥0∞) ^ q0.shadow.1 /
          ((relaxedDirW (beta + tau) : ℝ≥0∞) ^ (target - 1) *
            (relaxedDirEta (beta + tau) : ℝ≥0∞) ^ M) +
        (p' + p * wp) ^ T * 1 / wp ^ M) + delta := by
  rw [relaxedBandMonitor_physical_failure_eq_raw]
  refine (relaxedBandMonitor_physical_failure_split
    r n lower target T q0).trans ?_
  exact add_le_add
    (relaxedBandMonitor_phase_fail
      r n lower target bHi gap M T yLo beta slack tau wp p p'
      h3 htarget hband hyLo hbeta1 hslack htau hB hcorner
      hwp1 hwp0 hp hpFloor q0 hstart hstartLive hc0)
    hbackslide

end Tri

#print axioms Tri.relaxedBandMonitorStep_map_physical
#print axioms Tri.relaxedBandMonitorStep_map_shadow
#print axioms Tri.iter_relaxedBandMonitor_map_physical
#print axioms Tri.iter_relaxedBandMonitor_map_shadow
#print axioms Tri.relaxedBandMonitor_phase_fail
#print axioms Tri.relaxedTriChain_phase_fail_of_backslide
