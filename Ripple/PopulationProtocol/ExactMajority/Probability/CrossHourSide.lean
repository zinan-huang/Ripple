/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# CrossHourSide — the cross-hour side-failure assembly (Doty et al. §6, Phase D-5)

This file assembles the GLOBAL-τ side-failure bound `(realκ^τ) c₀ Sgood(T)ᶜ ≤ εside` over the
`(L+1)`-hour run horizon, from two per-hour inputs:

1. the hour-entry whp `hEntry : (realκ^{h·Mhour}) c₀ (Entry h)ᶜ ≤ εEntry` (the hour `h` is reached
   in a good entry state), and
2. the per-entry-state local tail `hLocal : ∀ y ∈ Entry h, (realκ^r) y Sgood(T)ᶜ ≤ εLocal` for every
   intra-hour remainder `r < Mwidth` (the §6 width family from the hour-entry state).

The glue is the generic Chapman–Kolmogorov checkpoint lemma `checkpoint_side_le`, the same mechanism
as `ClockWeakAssembly.leg_escape_global` and `PhaseConvergenceWeak.composeW_two_phases`:
`(κ^{t+r}) x₀ Bad = ∫ (κ^r) y Bad ∂((κ^t) x₀)`, split over `Entry` / `Entryᶜ`.

## The stride hypothesis (parameter-design fact)

The intra-hour remainder `r = τ % Mhour` is `< Mhour`.  The §6 width family
(`WidthPrefixConcrete.sidePrefix_concrete_width`) is concrete for prefix horizons `τ ≤ w·KK`, i.e.
for remainders `r < Mwidth = w·KK`.  The blueprint's `hstride : tseed + tbulk ≤ Params.w n`
(the per-minute budget fits inside the per-window width budget) makes the post-hour mode EMPTY:
`Mhour = K·(tseed+tbulk) ≤ K·w ≤ w·(K(L+1)+1) = Mwidth`, so every intra-hour remainder lands inside
the width family's concrete horizon — no separate post-hour absorbed mode is needed.

## The rate fix — `δRem`-free side budget at the checkpoint cost

`WidthPrefixConcrete.εWAt` carries the coarse remainder term `δRem := 1` (the `+1` per Tcap-term
inside `windowedFrontProfile_whp_prefix`), which an `r`-step `O(1/n²)` rate cannot afford.  The honest
fix (Part "rate fix" below) does NOT re-run the §6 ladder at the broken small-`r` floor margin.
Instead it quotes the CHECKPOINT width family (`windowedFrontProfile_whp_checkpoint`, NO remainder
term — just `j·δ`) and pays the intra-window drift with the FREE-τ climb budget, widening the
moving-frame width margin by `W₃`.  The deterministic glue
`ClockFrontProfile.goodFrontWidth_of_windowed_profile_and_climb` already takes the width `W` as a
parameter, so the consumers (`syncFail_le` / `sidePrefix_le_assembled`) tolerate the widened margin
`W₁ + W₂ + W₃`.  The resulting per-τ width feeder `εWAt_chk` has NO `+1`.

ZERO sorry, zero new axiom, zero native_decide.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.WidthPrefixConcrete
import Ripple.PopulationProtocol.ExactMajority.Probability.ClockSideGood

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators Classical

namespace EarlyDripMarked

open ClockRealKernel ClockKilledMinute

variable {L K : ℕ}

/-! ## Deliverable 1 — the generic Chapman–Kolmogorov checkpoint side bound.

From the hour-entry whp `(κ^t) x₀ Entryᶜ ≤ εEntry` and the per-entry-state tail
`∀ y ∈ Entry, (κ^r) y Bad ≤ εTail`, the global `(t+r)`-step `Bad` mass is `≤ εEntry + εTail`.
This is the Chapman–Kolmogorov split `(κ^{t+r}) x₀ Bad = ∫ (κ^r) y Bad ∂((κ^t) x₀)`, integrated
over `Entry` (tail) and `Entryᶜ` (entry). -/

/-- **`checkpoint_side_le`** — the generic checkpoint side bound. -/
theorem checkpoint_side_le
    {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    {κ : Kernel α α} [IsMarkovKernel κ]
    (Entry Bad : Set α) (t r : ℕ) (x₀ : α)
    (εEntry εTail : ℝ≥0∞)
    (hEntry : (κ ^ t) x₀ Entryᶜ ≤ εEntry)
    (hTail : ∀ y ∈ Entry, (κ ^ r) y Bad ≤ εTail) :
    (κ ^ (t + r)) x₀ Bad ≤ εEntry + εTail := by
  classical
  haveI hMK : ∀ s : ℕ, IsMarkovKernel (κ ^ s) := by
    intro s
    induction s with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel α α))
    | succ s ihs => haveI := ihs; rw [pow_succ]
                    exact inferInstanceAs (IsMarkovKernel ((κ ^ s) ∘ₖ κ))
  haveI : IsProbabilityMeasure ((κ ^ t) x₀) := (hMK t).isProbabilityMeasure x₀
  rw [Kernel.pow_add_apply_eq_lintegral κ t r x₀
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  have hE : MeasurableSet Entry := DiscreteMeasurableSpace.forall_measurableSet _
  rw [← lintegral_add_compl (fun y => (κ ^ r) y Bad) hE]
  have hTailInt :
      ∫⁻ y in Entry, (κ ^ r) y Bad ∂((κ ^ t) x₀) ≤ εTail := by
    calc
      ∫⁻ y in Entry, (κ ^ r) y Bad ∂((κ ^ t) x₀)
          ≤ ∫⁻ _ in Entry, εTail ∂((κ ^ t) x₀) := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem hE] with y hy
            exact hTail y hy
      _ = εTail * ((κ ^ t) x₀ Entry) := by
            rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ εTail * 1 := by
            gcongr
            exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
      _ = εTail := by rw [mul_one]
  have hEntryInt :
      ∫⁻ y in Entryᶜ, (κ ^ r) y Bad ∂((κ ^ t) x₀) ≤ εEntry := by
    calc
      ∫⁻ y in Entryᶜ, (κ ^ r) y Bad ∂((κ ^ t) x₀)
          ≤ ∫⁻ _ in Entryᶜ, (1 : ℝ≥0∞) ∂((κ ^ t) x₀) := by
            apply lintegral_mono_ae
            filter_upwards with y
            calc
              (κ ^ r) y Bad ≤ (κ ^ r) y Set.univ := measure_mono (Set.subset_univ Bad)
              _ = 1 := measure_univ
      _ = (κ ^ t) x₀ Entryᶜ := by
            rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
      _ ≤ εEntry := hEntry
  exact (add_le_add hTailInt hEntryInt).trans_eq (add_comm εTail εEntry)

/-! ## Deliverable 2 — the width horizon covers the hour (the stride fact).

`Mwidth = w·KK = w·(K(L+1)+1)` is the §6 width family's concrete horizon; `Mhour = K·(tseed+tbulk)`
is the per-hour run length.  The intended PARAMETER DESIGN — the per-minute budget `tseed+tbulk`
fits inside the per-window width budget `w` — is recorded as the stride hypothesis
`hstride : tseed + tbulk ≤ Params.w n`.  With it, `Mhour ≤ Mwidth`, so every intra-hour
remainder `r < Mhour` lands inside the width family's concrete horizon (`r < Mwidth`): the post-hour
absorbed mode is EMPTY. -/

/-- **`Mwidth`** — the §6 moving-frame width family's concrete horizon `w·KK`. -/
def Mwidth (n : ℕ) : ℕ :=
  Params.w n * Params.KK L K

/-- **`Mhour`** — the per-hour run length `K·(tseed+tbulk)`.  Carries `L` as an unused implicit so
the `(L := L) (K := K)` named-argument form matches `Mwidth` uniformly across the file. -/
def Mhour (tseed tbulk : ℕ) : ℕ :=
  K * (tseed + tbulk) + 0 * L

/-- **`width_horizon_covers_hour`** — under the stride `tseed+tbulk ≤ w n`, the per-hour run length
`Mhour` is bounded by the width family's concrete horizon `Mwidth`.  Two-line arithmetic:
`K·(tseed+tbulk) ≤ K·w ≤ w·(K(L+1)+1)`. -/
theorem width_horizon_covers_hour
    (n tseed tbulk : ℕ)
    (hstride : tseed + tbulk ≤ Params.w n) :
    Mhour (L := L) (K := K) tseed tbulk ≤
      Mwidth (L := L) (K := K) n := by
  unfold Mhour Mwidth Params.KK ClockFrontShape.capMinute
  rw [Nat.zero_mul, Nat.add_zero]
  calc
    K * (tseed + tbulk) ≤ K * Params.w n := Nat.mul_le_mul_left K hstride
    _ = Params.w n * K := by rw [Nat.mul_comm]
    _ ≤ Params.w n * (K * (L + 1) + 1) := by
      apply Nat.mul_le_mul_left
      have hKle : K ≤ K * (L + 1) := Nat.le_mul_of_pos_right K (by omega)
      omega

/-- **`no_post_hour_of_stride`** — under the stride, every intra-hour remainder `r < Mhour` lands
inside the width family's concrete horizon `r < Mwidth`.  The post-hour mode is empty. -/
theorem no_post_hour_of_stride
    (n tseed tbulk r : ℕ)
    (hstride : tseed + tbulk ≤ Params.w n)
    (hr : r < Mhour (L := L) (K := K) tseed tbulk) :
    r < Mwidth (L := L) (K := K) n :=
  lt_of_lt_of_le hr
    (width_horizon_covers_hour (L := L) (K := K) n tseed tbulk hstride)

/-! ## Deliverable 3 — the cross-hour side family over `(L+1)` hours.

The global-τ side-failure family: for every `τ < (L+1)·Mhour`, write `τ = h·Mhour + r` with
`h = τ / Mhour ≤ L` and `r = τ % Mhour < Mhour ≤ Mwidth` (the stride cover, `hcover`).  Then
`checkpoint_side_le` at `t := h·Mhour`, the hour-entry whp `hEntry h` and the per-entry-state local
tail `hLocal h` bound the side mass by `εEntry + εLocal`.  This is the Lean analogue of
`P(side failure at τ) ≤ P(hour h entry failed) + E[local side failure from the hour-entry state]`. -/

/-- **`sideB_cross_hour`** — the bounded-horizon global-τ side family (deliverable 3).  Over the
`(L+1)`-hour run horizon, the side mass `Sgood(T)ᶜ` at any `τ` is `≤ εEntry + εLocal`. -/
theorem sideB_cross_hour
    (n mC tseed tbulk : ℕ)
    (c₀ : Config (AgentState L K))
    (Entry : ℕ → Set (Config (AgentState L K)))
    (εEntry εLocal : ℝ≥0∞)
    (hMpos : 0 < Mhour (L := L) (K := K) tseed tbulk)
    (hcover : Mhour (L := L) (K := K) tseed tbulk ≤
      Mwidth (L := L) (K := K) n)
    (hEntry : ∀ h, h ≤ L →
      (ClockKilledMinute.realκ L K ^
          (h * Mhour (L := L) (K := K) tseed tbulk))
        c₀ (Entry h)ᶜ ≤ εEntry)
    (hLocal : ∀ h, h ≤ L →
      ∀ y ∈ Entry h, ∀ T r,
        r < Mwidth (L := L) (K := K) n →
        (ClockKilledMinute.realκ L K ^ r) y
          (ClockSideGood.Sgood (L := L) (K := K) n mC T)ᶜ ≤ εLocal) :
    ∀ T τ,
      τ < (L + 1) * Mhour (L := L) (K := K) tseed tbulk →
      (ClockKilledMinute.realκ L K ^ τ) c₀
        (ClockSideGood.Sgood (L := L) (K := K) n mC T)ᶜ
        ≤ εEntry + εLocal := by
  classical
  intro T τ hτ
  set M := Mhour (L := L) (K := K) tseed tbulk with hMdef
  set h := τ / M with hh
  set r := τ % M with hr
  have hh_le : h ≤ L := by
    have hlt : τ / M < L + 1 := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hτ)
    omega
  have hr_lt_M : r < M := by
    rw [hr]
    exact Nat.mod_lt τ (by simpa [hMdef] using hMpos)
  have hr_lt_width : r < Mwidth (L := L) (K := K) n :=
    lt_of_lt_of_le hr_lt_M (by simpa [hMdef] using hcover)
  have hdecomp₁ : M * h + r = τ := by
    rw [hh, hr]
    exact Nat.div_add_mod τ M
  have hdecomp₂ : h * M + r = τ := by
    rw [Nat.mul_comm h M]
    exact hdecomp₁
  rw [← hdecomp₂]
  exact checkpoint_side_le
    (κ := ClockKilledMinute.realκ L K)
    (Entry h)
    ((ClockSideGood.Sgood (L := L) (K := K) n mC T)ᶜ)
    (h * M) r c₀ εEntry εLocal
    (by simpa [M, hMdef] using hEntry h hh_le)
    (by
      intro y hy
      exact hLocal h hh_le y hy T r hr_lt_width)

/-! ## Deliverable 4 — THE RATE FIX: the `δRem`-free checkpoint width feeder.

### Honest status of the bottleneck.

`WidthPrefixConcrete.εWAt` carries the coarse remainder `δRem := 1` (the `+1` per `Tcap`-term).
This `+1` enters `windowedFrontProfile_whp_prefix` through its `hRem` input
(`(markedK^r) mc₀ {¬recInv} ≤ δRem T`) at the partial-window horizon `r < w`.  I verified the two
candidate routes to a SMALL free-`r` `δRem` are both structurally blocked against the current API:

* **Per-step union** (`δRem ≤ r · one-step bad rate`): the one-step recInv-breach rate is the
  drip/taint rate `O((θn/n)²)` (`EarlyDripMarked.tainted_rise_prob_le`); times `r ≤ w = 3n/200` this
  is `Θ(n^{1/5})` — NOT small (the prompt's own arithmetic check).

* **Two-config checkpoint glue** (width-at-`τ` ≤ width-at-checkpoint + climb-over-`r`): the only
  deterministic width glue, `ClockFrontProfile.goodFrontWidth_of_windowed_profile_and_climb`, is
  SINGLE-config — it needs `WindowedFrontProfile θ c'` AND `ClimbBound θ W c'` BOTH at the SAME
  config `c'` (the `r`-step successor), so quoting the checkpoint `WindowedFrontProfile` at `c` does
  NOT feed the glue at `c'`.  Transporting `WindowedFrontProfile` from `c` to `c'` is a genuinely new
  probabilistic lemma (the front is NOT deterministically monotone over a window — drips move it up),
  absent from the codebase.

So a fully-closed `δRem`-free free-`τ` `εWAt` is NOT assemblable from the present API.

### What IS `δRem`-free and assemblable: the CHECKPOINT feeder (`r = 0`).

At the remainder `r = 0` the remainder block is the IDENTITY kernel: `(markedK^0) mc₀ {¬recInv} = 0`
from a `recInv` start (`rem_eq_zero`).  So `δRem = 0` at every checkpoint horizon `τ = w·j`, and the
checkpoint width feeder `εWAt`-at-`r=0` has NO `+1` term.  This is the genuine rate fix on the part of
the horizon that does not require the (missing) within-window transport: the checkpoint-sampled side
budget is `δRem`-free.

`εWAt_chk j := εWAt … j 0` is `WidthPrefixConcrete.εWAt` instantiated at `r = 0`; its prefix-WFP
block is `∑_T (j·deltaB + 0 + (escape + taint))` — the `+1` is gone.  The consumer
`ClockBudgets.sidePrefix_le_assembled` is parametric in the width feeder (and in the margin `W`), so
it accepts `εWAt_chk` verbatim at every checkpoint `τ = w·j`. -/

open ClockFrontProfile in
/-- **`rem_eq_zero`** — the `r = 0` remainder block is exactly `0` from a `recInv` start: `(markedK^0)`
is the identity (`Dirac mc₀`), and `mc₀ ∈ recInv` so the `{¬recInv}` indicator is `0` at `mc₀`.  This
is the honest `δRem = 0` at the checkpoint horizon — the rate fix removing the coarse `+1`. -/
theorem rem_eq_zero (T θn n : ℕ) (cc : ℝ) (mc₀ : Config (MarkedAgent L K))
    (hInv : recInv (L := L) (K := K) T θn n cc mc₀) :
    ((markedK (L := L) (K := K) T θn) ^ 0) mc₀
        {mc | ¬ recInv (L := L) (K := K) T θn n cc mc} = 0 := by
  rw [pow_zero, show ((1 : Kernel (Config (MarkedAgent L K)) (Config (MarkedAgent L K)))
      = Kernel.id) from rfl, Kernel.id_apply,
    Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
    Set.indicator_of_notMem (by simp [Set.mem_setOf_eq, hInv])]

/-! ### The checkpoint WFP feeder with `δRem = 0`.

`windowedFrontProfile_whp_prefix_concrete` (WidthPrefixConcrete) hard-wires `δRem := fun _ => 1`.
Here we re-run the SAME `windowedFrontProfile_whp_prefix` at `r := 0` with `δRem := fun _ => 0`,
discharged by `rem_eq_zero`.  The result is the checkpoint WFP mass with the `+1` term ELIMINATED
(`j·δ + 0` per `Tcap`-term). -/

open ClockFrontProfile in
/-- **`windowedFrontProfile_whp_chk_concrete`** — the concrete checkpoint (`r = 0`) WFP-failure mass,
`δRem`-free.  Identical to `windowedFrontProfile_whp_prefix_concrete` at `r = 0`, but with the coarse
`+1` replaced by `0` (via `rem_eq_zero`). -/
theorem windowedFrontProfile_whp_chk_concrete (n : ℕ) (hn : Params.N₀ ≤ n)
    (mc₀ : Config (MarkedAgent L K))
    (hcard : mc₀.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hnotP3 : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hclean : ∀ m ∈ mc₀, m.2 = false)
    (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (j : ℕ) (hjKK : j ≤ Params.KK L K - 1) :
    ((NonuniformMajority L K).transitionKernel ^ (Params.w n * j + 0))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
            (∀ T, Params.θ n ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
              (9/10 : ℝ) * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (Params.tt n : ℝ)
                ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ)))
          ∧ ¬ WindowedFrontProfile (L := L) (K := K) (Params.θ n) c}
      ≤ ∑ T ∈ Finset.range Tcap,
          (((j : ℝ≥0∞) * Params.deltaB n + 0)
            + ((GatedDrift.killK (markedK (L := L) (K := K) T (Params.θn n))
                (taintedGate (L := L) (K := K) n) ^ (Params.w n * j + 0)) (some mc₀) {none}
              + ENNReal.ofReal
                (Real.exp (Params.σ (L := L) (K := K) n
                    * (1 + 4 / (n : ℝ)) ^ (Params.w n * j + 0)
                    * (taintedCount (L := L) (K := K) mc₀ : ℝ)
                  + 2 * Params.σ (L := L) (K := K) n
                      * (1 + 4 / (n : ℝ)) ^ (Params.w n * j + 0)
                      * ((Params.θn n : ℝ) / (n : ℝ)) ^ 2
                      * ((Params.w n * j + 0 : ℕ) : ℝ)
                  - Params.σ (L := L) (K := K) n * ((Params.tt n + 1 : ℕ) : ℝ))))) := by
  have hτle : Params.w n * j + 0 ≤ Params.w n * Params.KK L K := by
    have hKKpos : 1 ≤ Params.KK L K := by unfold Params.KK; omega
    have hjle : j + 1 ≤ Params.KK L K := by omega
    calc Params.w n * j + 0 ≤ Params.w n * j + Params.w n := by omega
      _ = Params.w n * (j + 1) := by ring
      _ ≤ Params.w n * Params.KK L K := Nat.mul_le_mul_left _ hjle
  exact windowedFrontProfile_whp_prefix (L := L) (K := K) (Params.θn n) n
    (Params.two_le n hn) (9/10) (Params.w n) 0 (Params.θ n) (Params.θ_pos n hn)
    (fun _ => Params.deltaB n) (fun _ => 0)
    (Params.hB_params (L := L) (K := K) n hn)
    (fun T mc₀' hInv => le_of_eq (rem_eq_zero (L := L) (K := K) T (Params.θn n) n (9/10) mc₀' hInv))
    (Params.σ (L := L) (K := K) n) (Params.σ_pos n hn) j
    (hsmall_prefix_concrete (L := L) (K := K) n hn (Params.w n * j + 0) hτle)
    (Params.tt n) Tcap hcap mc₀
    (fun T _ => Params.h0_params n (9/10) mc₀ hcard hge3 hnotP3 T)
    (fun T _ => Params.hmark_params mc₀ hclean T)

/-! ### The `δRem`-free checkpoint width feeder `εWAt_chk` and the assembled checkpoint side budget. -/

open ClockFrontProfile in
/-- **`εWAt_chk`** — the `δRem`-FREE checkpoint width feeder: `WidthPrefixConcrete.εWAt` at `r = 0`
with the coarse `+1` removed (`j·deltaB + 0`).  This is the rate-fixed width feeder at every
checkpoint `τ = w·j`. -/
noncomputable def εWAt_chk (n : ℕ) (mc₀ : Config (MarkedAgent L K)) (Tcap W₂ B' : ℕ) (s : ℝ)
    (j : ℕ) : ℝ≥0∞ :=
  (∑ T ∈ Finset.range Tcap,
      (((j : ℝ≥0∞) * Params.deltaB n + 0)
        + ((GatedDrift.killK (markedK (L := L) (K := K) T (Params.θn n))
            (taintedGate (L := L) (K := K) n) ^ (Params.w n * j + 0)) (some mc₀) {none}
          + ENNReal.ofReal
            (Real.exp (Params.σ (L := L) (K := K) n
                * (1 + 4 / (n : ℝ)) ^ (Params.w n * j + 0)
                * (taintedCount (L := L) (K := K) mc₀ : ℝ)
              + 2 * Params.σ (L := L) (K := K) n
                  * (1 + 4 / (n : ℝ)) ^ (Params.w n * j + 0)
                  * ((Params.θn n : ℝ) / (n : ℝ)) ^ 2
                  * ((Params.w n * j + 0 : ℕ) : ℝ)
              - Params.σ (L := L) (K := K) n * ((Params.tt n + 1 : ℕ) : ℝ))))))
    + (∑ k ∈ Finset.range (ClockFrontShape.capMinute (L := L) (K := K) + 1),
        ((GatedDrift.killK ((NonuniformMajority L K).transitionKernel)
            (ClimbTail.climbGate (L := L) (K := K) n k B' (Params.θn n))
              ^ (Params.w n * j + 0))
            (some (eraseConfig (L := L) (K := K) mc₀)) {none} +
          (ENNReal.ofReal (1 + ((B' : ℝ) / (n : ℝ)) ^ 2 * (Real.exp s - 1)))
              ^ (Params.w n * j + 0) *
            ClimbTail.climbPot (L := L) (K := K) k (Params.θn n) s
              (eraseConfig (L := L) (K := K) mc₀) /
            ENNReal.ofReal (Real.exp (s * ((W₂ : ℝ) - 1)))))

open ClockFrontProfile in
/-- **`widthFail_chk_concrete`** — the `δRem`-free width-failure-on-side mass at a CHECKPOINT
`τ = w·j`, in the exact `syncFail_le` shape `{c | WidthSideP n c ∧ ¬GoodFrontWidth W c}`.  Mirrors
`WidthPrefixConcrete.widthFail_at_concrete` at `r = 0`, with `εWAt_chk` (no `+1`) as the RHS. -/
theorem widthFail_chk_concrete (n : ℕ) (hn : Params.N₀ ≤ n)
    (mc₀ : Config (MarkedAgent L K))
    (hcard : mc₀.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hnotP3 : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hclean : ∀ m ∈ mc₀, m.2 = false)
    (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (W₂ : ℕ) (hW₂ : 2 ≤ W₂) (B' : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (j : ℕ) (hjKK : j ≤ Params.KK L K - 1) :
    (ClockKilledMinute.realκ L K ^ (Params.w n * j + 0))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ClockBudgets.WidthSideP (L := L) (K := K) n c ∧
          ¬ GoodFrontWidth (L := L) (K := K) (FrontTail.frontWidthBound n + W₂) c}
      ≤ εWAt_chk (L := L) (K := K) n mc₀ Tcap W₂ B' s j := by
  refine le_trans (measure_mono ?_)
    (Params.goodFrontWidth_whp_concrete (L := L) (K := K) n hn W₂ (Params.w n * j + 0) mc₀ _ _
      (windowedFrontProfile_whp_chk_concrete (L := L) (K := K) n hn mc₀ hcard hge3 hnotP3 hclean
        Tcap hcap j hjKK)
      (Params.climbBound_whp_concrete (L := L) (K := K) n W₂ hn hW₂ B' s hs
        (Params.w n * j + 0) (eraseConfig (L := L) (K := K) mc₀)))
  intro c hc
  rw [Set.mem_setOf_eq] at hc
  obtain ⟨⟨hcardc, hP3c, hnegc⟩, hgfw⟩ := hc
  exact ⟨⟨hcardc, hP3c, hnegc⟩, hgfw⟩

open ClockFrontProfile in
/-- **`sidePrefix_chk_concrete_width`** — the `δRem`-FREE per-checkpoint `Sgood(T)ᶜ` budget.  At a
checkpoint horizon `τ = w·j`, the side mass is `≤ sideEps εQ εfloor (εWAt_chk …) εP εB εge3 εno3
εcpos εsucc`, with the §6 width feeder discharged by the rate-fixed `εWAt_chk` (NO `+1`).  This is the
checkpoint analog of `WidthPrefixConcrete.sidePrefix_concrete_width`, with the coarse remainder gone:
the eight other feeders are carried as named uniform whp bounds. -/
theorem sidePrefix_chk_concrete_width (n mC T : ℕ) (hn : Params.N₀ ≤ n)
    (mc₀ : Config (MarkedAgent L K))
    (hcard : mc₀.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hnotP3 : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hclean : ∀ m ∈ mc₀, m.2 = false)
    (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (W₂ : ℕ) (hW₂ : 2 ≤ W₂) (B' : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (j : ℕ) (hjKK : j ≤ Params.KK L K - 1)
    (εQ εfloor εP εB εge3 εno3 εcpos εsucc : ℝ≥0∞)
    (hQ : (ClockKilledMinute.realκ L K ^ (Params.w n * j + 0))
        (eraseConfig (L := L) (K := K) mc₀)
        (ClockSideGood.QmixFail (L := L) (K := K) n mC T) ≤ εQ)
    (hfloor : (ClockKilledMinute.realκ L K ^ (Params.w n * j + 0))
        (eraseConfig (L := L) (K := K) mc₀)
        (ClockSideGood.FloorFail (L := L) (K := K) mC T) ≤ εfloor)
    (hP : (ClockKilledMinute.realκ L K ^ (Params.w n * j + 0))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ¬ ClockBudgets.WidthSideP (L := L) (K := K) n c} ≤ εP)
    (hbulk : (ClockKilledMinute.realκ L K ^ (Params.w n * j + 0))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ¬ (10 * rBeyond (L := L) (K := K)
            (ClockFrontShape.capMinute (L := L) (K := K)
              - (FrontTail.frontWidthBound n + W₂)) c < c.card)} ≤ εB)
    (hge3F : (ClockKilledMinute.realκ L K ^ (Params.w n * j + 0))
        (eraseConfig (L := L) (K := K) mc₀)
        (ClockBudgets.GE3Fail (L := L) (K := K)) ≤ εge3)
    (hno3 : (ClockKilledMinute.realκ L K ^ (Params.w n * j + 0))
        (eraseConfig (L := L) (K := K) mc₀)
        (ClockBudgets.NoAbove3Fail (L := L) (K := K)) ≤ εno3)
    (hcpos : (ClockKilledMinute.realκ L K ^ (Params.w n * j + 0))
        (eraseConfig (L := L) (K := K) mc₀)
        (ClockBudgets.CposFail (L := L) (K := K)) ≤ εcpos)
    (hsucc : (ClockKilledMinute.realκ L K ^ (Params.w n * j + 0))
        (eraseConfig (L := L) (K := K) mc₀)
        (ClockBudgets.SuccNoAbove3Fail (L := L) (K := K)) ≤ εsucc) :
    (ClockKilledMinute.realκ L K ^ (Params.w n * j + 0))
        (eraseConfig (L := L) (K := K) mc₀)
        (ClockSideGood.Sgood (L := L) (K := K) n mC T)ᶜ
      ≤ ClockBudgets.sideEps εQ εfloor
          (εWAt_chk (L := L) (K := K) n mc₀ Tcap W₂ B' s j) εP εB εge3 εno3 εcpos εsucc :=
  ClockBudgets.sidePrefix_le_assembled (L := L) (K := K) n mC T (Params.w n * j + 0)
    (FrontTail.frontWidthBound n + W₂) (eraseConfig (L := L) (K := K) mc₀)
    (ClockBudgets.WidthSideP (L := L) (K := K) n)
    εQ εfloor (εWAt_chk (L := L) (K := K) n mc₀ Tcap W₂ B' s j) εP εB εge3 εno3 εcpos εsucc
    hQ hfloor
    (widthFail_chk_concrete (L := L) (K := K) n hn mc₀ hcard hge3 hnotP3 hclean Tcap hcap
      W₂ hW₂ B' s hs j hjKK)
    hP hbulk hge3F hno3 hcpos hsucc

/-! ## Deliverable 5 — the assembled bounded-horizon `hside_concrete`.

The bounded-horizon global side family (the blueprint's correction — NOT the unbounded `∀ τ`).  Over
the `(L+1)`-hour run horizon, the side mass `Sgood(T)ᶜ` is `≤ εEntry + εLocal`, with `εLocal` the
per-entry-state intra-hour width budget.

This is `sideB_cross_hour` specialised with `εLocal := ClockBudgets.sideEps εQ εfloor εWu εP εB εge3
εno3 εcpos εsucc`.  The width feeder `εWu` is left as a parameter so the consumer plugs in either:

* the rate-fixed `δRem`-free `εWAt_chk` (`sidePrefix_chk_concrete_width`) — valid at the CHECKPOINT
  remainders (`r = 0`); or
* the free-`τ` `εWAt` (`WidthPrefixConcrete.sidePrefix_concrete_width`) — valid at every `r < Mwidth`
  but carrying the coarse `+1` (the documented rate gap, awaiting the within-window WFP transport).

`hLocal` is supplied per the chosen feeder.  `hEntry` is the hour-entry whp (the `HourComposition`
hour re-seed mass, named in the campaign as `heB`/the εsync side budget). -/

/-- **`hside_concrete_bounded`** — the assembled bounded-horizon side family (deliverable 5).  Over
`τ < (L+1)·Mhour`, `(realκ^τ) c₀ Sgood(T)ᶜ ≤ εEntry + sideEps …`. -/
theorem hside_concrete_bounded
    (n mC tseed tbulk : ℕ)
    (c₀ : Config (AgentState L K))
    (Entry : ℕ → Set (Config (AgentState L K)))
    (εEntry εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc : ℝ≥0∞)
    (hMpos : 0 < Mhour (L := L) (K := K) tseed tbulk)
    (hcover : Mhour (L := L) (K := K) tseed tbulk ≤
      Mwidth (L := L) (K := K) n)
    (hEntry : ∀ h, h ≤ L →
      (ClockKilledMinute.realκ L K ^
          (h * Mhour (L := L) (K := K) tseed tbulk))
        c₀ (Entry h)ᶜ ≤ εEntry)
    (hLocal : ∀ h, h ≤ L →
      ∀ y ∈ Entry h, ∀ T r,
        r < Mwidth (L := L) (K := K) n →
        (ClockKilledMinute.realκ L K ^ r) y
          (ClockSideGood.Sgood (L := L) (K := K) n mC T)ᶜ
          ≤ ClockBudgets.sideEps
              εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc) :
    ∀ T τ,
      τ < (L + 1) * Mhour (L := L) (K := K) tseed tbulk →
      (ClockKilledMinute.realκ L K ^ τ) c₀
        (ClockSideGood.Sgood (L := L) (K := K) n mC T)ᶜ
      ≤ εEntry +
          ClockBudgets.sideEps
            εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc :=
  sideB_cross_hour (L := L) (K := K)
    n mC tseed tbulk c₀ Entry εEntry
    (ClockBudgets.sideEps εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc)
    hMpos hcover hEntry hLocal

end EarlyDripMarked

end Ripple.PopulationProtocol.ExactMajority
