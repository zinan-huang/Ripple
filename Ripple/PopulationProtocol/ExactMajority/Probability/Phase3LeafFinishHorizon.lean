import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3LeafStaticGoodClock
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Post3

/-!
# Leaf cut horizon from `Snapshot617Horizon` (the deterministic finish bound, per trace)

The leaf cut-time horizon `T` for `LeafCutsBoundedBy` is **not** derivable from `GoodClockUpTo`
alone (`start_h`/`end_h` are uncapped first-passage `Nat.find`; the quantile
gives only relative bounds).  The absolute bound is the repo's existing `Snapshot617Horizon`
(`T_end_l2 = GoodClock.finish good (ell+2) ≤ 17·n·(L+1)`).  This file supplies the missing
first-passage proof-irrelevance + finish-monotonicity machinery and the per-trace
bridge `leafCutsBoundedBy_of_horizon`.  Per trace, because a single `Snapshot617Horizon` is tied
to its stored trace; the closure applies it inside the trace branch where that horizon exists.
-/

namespace Ripple.PopulationProtocol.ExactMajority

open scoped ENNReal NNReal BigOperators

variable {L K : ℕ}

namespace Phase3GoodClock

/-- First-passage time depends only on the predicate, not the existence proof. -/
theorem firstPassage_proof_irrel {P : ℕ → Prop} [DecidablePred P]
    (hex₁ hex₂ : ∃ t, P t) :
    firstPassage P hex₁ = firstPassage P hex₂ := by
  have h : hex₁ = hex₂ := Subsingleton.elim _ _
  cases h; rfl

theorem end_h_proof_irrel (θ : ClockTimingParams) (tr : Trace L K) (h : ℕ)
    (hex₁ hex₂ : ∃ τ, EndHit (L := L) (K := K) θ h (tr τ)) :
    end_h (L := L) (K := K) θ tr h hex₁ = end_h (L := L) (K := K) θ tr h hex₂ := by
  simpa [end_h] using
    firstPassage_proof_irrel (P := fun τ => EndHit (L := L) (K := K) θ h (tr τ)) hex₁ hex₂

namespace GoodClock

/-- One-step finish monotonicity: `finish h ≤ finish (h+1)` from `previous_hour_finished`. -/
theorem finish_step_mono {M : ℕ} {θ : ClockTimingParams} {tr : Trace L K}
    (G : GoodClock (L := L) (K := K) M θ tr) (h : ℕ) :
    G.finish h ≤ G.finish (h + 1) := by
  have hprev : G.finish h < G.start (h + 1) := by
    simpa using G.previous_hour_finished (h + 1) (Nat.succ_pos h)
  have hstart_le : G.start (h + 1) ≤ G.finish (h + 1) := by
    have hx := G.twoOverC_le_end (h + 1)
    dsimp [start, finish] at hx ⊢; omega
  exact le_trans (Nat.le_of_lt hprev) hstart_le

theorem finish_mono {M : ℕ} {θ : ClockTimingParams} {tr : Trace L K}
    (G : GoodClock (L := L) (K := K) M θ tr) {h h' : ℕ} (hle : h ≤ h') :
    G.finish h ≤ G.finish h' := by
  induction hle with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (G.finish_step_mono _)

end GoodClock
end Phase3GoodClock

namespace Phase3GoodClockRegime
namespace GoodClockUpTo

/-- `finish` depends only on `h`, not the carried `h ≤ lastHour` proof. -/
theorem finish_irrel {M : ℕ} {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {lastHour h : ℕ}
    (G : GoodClockUpTo (L := L) (K := K) M θ tr lastHour) (hh₁ hh₂ : h ≤ lastHour) :
    G.finish hh₁ = G.finish hh₂ := by
  unfold finish
  exact Phase3GoodClock.end_h_proof_irrel (L := L) (K := K) θ tr h
    (G.quantile.end_exists h hh₁) (G.quantile.end_exists h hh₂)

/-- A `GoodClockUpTo` finish equals any full `GoodClock` finish on the same `(θ, tr, h)`
(proof-irrelevance).  `M`-agnostic: `end_h` does not depend on `M`, so `U` and `G` may carry
different clock-domain parameters. -/
theorem finish_eq_good_finish {M M' : ℕ} {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {lastHour h : ℕ}
    (U : GoodClockUpTo (L := L) (K := K) M θ tr lastHour)
    (G : Phase3GoodClock.GoodClock (L := L) (K := K) M' θ tr) (hh : h ≤ lastHour) :
    U.finish hh = Phase3GoodClock.GoodClock.finish (L := L) (K := K) G h := by
  unfold finish Phase3GoodClock.GoodClock.finish
  exact Phase3GoodClock.end_h_proof_irrel (L := L) (K := K) θ tr h
    (U.quantile.end_exists h hh) (G.end_exists h)

end GoodClockUpTo
end Phase3GoodClockRegime

namespace Phase3Assembly

/-- **Per-trace finish horizon bound.**  Given a `Snapshot617Horizon H` for `tr` (matching the
domain `D`'s clock parameters), every `GoodClockUpTo` finish below `D.lastCoreHour` is `≤ T_end_l2`
(`≤ 17·n·(L+1)`).  Via `finish_eq_good_finish` (proof-irrel) + `GoodClock.finish_mono`. -/
theorem goodClockUpTo_finish_le_horizon
    {D : Phase3Core.Phase3ModeDomain L} {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {n ell : ℕ}
    (H : Phase3Post3.Snapshot617Horizon (L := L) (K := K) n ell)
    (hθ : H.θ = θ) (htr : H.tr = tr)
    (hLast : D.lastCoreHour ≤ ell + 2)
    (U : Phase3GoodClockRegime.GoodClockUpTo (L := L) (K := K) D.M θ tr D.lastCoreHour)
    (h : ℕ) (hh : h ≤ D.lastCoreHour) :
    Phase3GoodClockRegime.GoodClockUpTo.finish (L := L) (K := K) U hh ≤ H.T_end_l2 := by
  subst hθ; subst htr
  have hbridge :
      Phase3GoodClockRegime.GoodClockUpTo.finish (L := L) (K := K) U hh
        = Phase3GoodClock.GoodClock.finish (L := L) (K := K) H.good h :=
    Phase3GoodClockRegime.GoodClockUpTo.finish_eq_good_finish (L := L) (K := K) U H.good hh
  have hmono :
      Phase3GoodClock.GoodClock.finish (L := L) (K := K) H.good h
        ≤ Phase3GoodClock.GoodClock.finish (L := L) (K := K) H.good (ell + 2) :=
    Phase3GoodClock.GoodClock.finish_mono (L := L) (K := K) H.good (le_trans hh hLast)
  calc
    Phase3GoodClockRegime.GoodClockUpTo.finish (L := L) (K := K) U hh
        = Phase3GoodClock.GoodClock.finish (L := L) (K := K) H.good h := hbridge
    _ ≤ H.T_end_l2 := by simpa [H.T_end_l2_eq_end_h] using hmono

end Phase3Assembly

namespace Phase3LeafStaticGoodClock

/-- **Per-trace cut bound from the horizon.**  Combines the per-trace finish bound with the
deterministic cut bridge `leafCutsBoundedBy_of_finishBounded`'s per-trace core. -/
theorem leafCutsBoundedBy_of_horizon
    {D : Phase3Core.Phase3ModeDomain L} {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {n ell : ℕ}
    (H : Phase3Post3.Snapshot617Horizon (L := L) (K := K) n ell)
    (hθ : H.θ = θ) (htr : H.tr = tr)
    (hLast : D.lastCoreHour ≤ ell + 2)
    (hGood : Phase3GoodClockRegime.GoodClockUpTo (L := L) (K := K) D.M θ tr D.lastCoreHour) :
    LeafCutsBoundedBy (L := L) (K := K) H.T_end_l2 D θ tr := by
  intro G h hh
  have hstart := Phase3Assembly.StrictCutTiming.goodClock_start_eq_goodClockUpTo_start
    (L := L) (K := K) (D := D) (θ := θ) (tr := tr) G hGood hh
  have hfin := Phase3Assembly.goodClockUpTo_finish_le_horizon
    (L := L) (K := K) (D := D) (θ := θ) (tr := tr) H hθ htr hLast hGood h hh
  have hslack : Phase3GoodClockRegime.GoodClockUpTo.start (L := L) (K := K) hGood hh
        + θ.twoOverC + θ.fortySevenOverM + 1
      ≤ Phase3GoodClockRegime.GoodClockUpTo.finish (L := L) (K := K) hGood hh := by
    simpa [Phase3GoodClockRegime.GoodClockUpTo.start,
      Phase3GoodClockRegime.GoodClockUpTo.finish] using hGood.quantile.fortySeven_slack h hh
  rw [hstart]; omega

end Phase3LeafStaticGoodClock
end Ripple.PopulationProtocol.ExactMajority
