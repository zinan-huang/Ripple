import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockKilledMinute
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealHours

/-!
# ClockWeakAssembly — the weak faithful-clock assembly (Doty §6 Phase B step 4)

This is the assembly layer over the killed-minute brick (`ClockKilledMinute`).  It replaces
the OLD `ClockRealFaithfulHours` assembly (which required the FALSE `habs_mix` deterministic
window closure as a carried ∀-minute hypothesis) by a WEAK assembly: the per-minute legs are
killed-kernel `PhaseConvergenceW` tails whose `Post` is NUMERICAL-only, and the gate-escape
budget is telescoped GLOBALLY off the run measure.

## Design of record (campaign §"ASSEMBLY DESIGN")

Two observations resolve the start-dependence mismatch (`clock_real_step_gated`'s escape
budget is start-dependent, but the killed-phase convergence is start-uniform):

1. **The killed-phase part is start-uniform** — `clock_killed_seed_stepW`/`_bulk_stepW` hold
   from any (lifted) `Pre`-config; no mismatch there.
2. **Escape telescopes globally.**  Per-leg escape from leg-start configs, INTEGRATED over the
   time-`t` run distribution `(K^t) x₀`, re-expands via Chapman–Kolmogorov into GLOBAL-time
   per-step terms.  `leg_escape_global` (deliverable 1) is exactly this: integrating
   `kill_now_escape_le_prefix_union`'s per-start statement and collapsing
   `∫ (K^σ) y Sᶜ ∂((K^t) x₀) = (K^{t+σ}) x₀ Sᶜ`.

## The side-set `S` (settled shape — documented per the campaign report request)

`leg_escape_global` is stated GENERICALLY in `K`, `G`, `S`, `q`.  At instantiation
(deliverable 3) we choose `S := G` (the gate itself), i.e. the side event under which the
one-step gate-escape probability is `≤ q` is membership in `G`.  With `S = G`:
* `hstep` becomes `∀ x ∈ G, K x Gᶜ ≤ q` — the one-step escape bound from gated configs, the
  honest §6 "drip-only excess counter" rate;
* the prefix budget `∑_{τ∈[t,t+M)} (K^τ) x₀ Gᶜ` charges exactly the times the GLOBAL run sits
  off the gate `G` — which, for `G = Qset = {Q_mix n mC T}` (seed) resp.
  `G = QbulkSet = {QbulkWin n mC T}` (bulk), is the per-`τ` window-failure mass that the
  WidthPrefix family (`goodFrontWidth_whp_at`) + endpoint bridges discharge later.

With `S = G`, `Gᶜ = Sᶜ`, so the "ungated start" worry (escape mass `1` from `x ∉ G`) is folded
automatically: the term `(K^t) x₀ Gᶜ` sits inside the prefix sum at `τ = t`.

## What this file delivers

* `leg_escape_global` (B-10a): the integrated/telescoped global escape bound.
* `clock_real_leg_global` (B-10b): the real seed leg, escape charged globally.
* `faithfulMinutePhasesW` + `clock_real_faithful_all_minutes_W` (B-10c/d): the `Fin L₀` real
  minute family with leg-indexed budgets, composed.
* `clock_real_faithful_O_log_n_W` (B-10e): the O(log n) endpoint wrapper.

ZERO sorry, zero new axiom, zero native_decide.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators Classical

namespace ClockWeakAssembly

open ClockRealKernel ClockRealMixed ClockRealSeed ClockRealBulk ClockMonoDischarge
open GatedDrift ClockKilledMinute ClockRealHours

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Inhabited α]

/-- The cemetery extension carries the discrete (`⊤`) measurable space (matching
`GatedKillNow`'s / `ClockKilledMinute`'s local instances). -/
local instance instOptionMScwa : MeasurableSpace (Option α) := ⊤
local instance instOptionDMScwa : DiscreteMeasurableSpace (Option α) := ⟨fun _ => trivial⟩

/-! ## Deliverable 1 (B-10a) — `leg_escape_global`.

The global-start telescoped escape bound.  From the per-start
`GatedDrift.kill_now_escape_le_prefix_union` (escape after `M` steps `≤ M·q + ∑_{σ<M} (K^σ) y Sᶜ`
from a gated start `y ∈ G`), we integrate over the GLOBAL time-`t` run distribution `(K^t) x₀`
and Chapman–Kolmogorov-collapse each prefix term:
  `∫ (K^σ) y Sᶜ ∂((K^t) x₀) = (K^{t+σ}) x₀ Sᶜ`.
Charging the OFF-gate start mass to the `τ = t` term of the side prefix requires `S ⊆ G`
(then `Gᶜ ⊆ Sᶜ`): the design takes `S = G`, so this is automatic; we state the generic lemma
with the explicit `hSG : Gᶜ ⊆ Sᶜ` side condition so the instantiation discharges it by `rfl`.
-/

/-- **Per-start escape, extended to ALL starts.**  `kill_now_escape_le_prefix_union` requires a
gated start `y ∈ G`.  For ungated `y ∉ G` (with `Gᶜ ⊆ Sᶜ`), the `σ = 0` prefix term
`(K^0) y Sᶜ = 1` already dominates the escape mass `≤ 1` — UNLESS `M = 0`, in which case the
escape mass is `0`.  So the per-start prefix bound holds for EVERY start. -/
theorem kill_now_escape_prefix_all {K : Kernel α α} {G S : Set α} [IsMarkovKernel K]
    (q : ℝ≥0∞) (hstep : ∀ x ∈ G, x ∈ S → K x Gᶜ ≤ q) (hSG : Gᶜ ⊆ Sᶜ)
    (M : ℕ) (y : α) :
    (GatedDrift.killK_now K G ^ M) (some y) {(none : Option α)}
      ≤ (M : ℝ≥0∞) * q + ∑ σ ∈ Finset.range M, (K ^ σ) y Sᶜ := by
  classical
  have hMKkill : ∀ s : ℕ, IsMarkovKernel (GatedDrift.killK_now K G ^ s) := by
    intro s; induction s with
    | zero => rw [pow_zero]
              exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel (Option α) (Option α)))
    | succ s ih => haveI := ih; rw [pow_succ]
                   exact inferInstanceAs (IsMarkovKernel ((GatedDrift.killK_now K G ^ s) ∘ₖ _))
  by_cases hy : y ∈ G
  · exact GatedDrift.kill_now_escape_le_prefix_union (K := K) (G := G) S q hstep M y hy
  · -- ungated start: dominate by 1; for M ≥ 1 the σ=0 prefix term is 1, for M = 0 escape is 0.
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · subst hM0
      have : (GatedDrift.killK_now K G ^ 0) (some y) {(none : Option α)} = 0 := by
        rw [pow_zero, show ((1 : Kernel (Option α) (Option α))) = Kernel.id from rfl,
          Kernel.id_apply,
          Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
        simp
      rw [this]; exact zero_le'
    · have hesc1 : (GatedDrift.killK_now K G ^ M) (some y) {(none : Option α)} ≤ 1 := by
        haveI := hMKkill M
        calc (GatedDrift.killK_now K G ^ M) (some y) {(none : Option α)}
            ≤ (GatedDrift.killK_now K G ^ M) (some y) Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      have hterm : (K ^ 0) y Sᶜ = 1 := by
        rw [pow_zero, show ((1 : Kernel α α)) = Kernel.id from rfl, Kernel.id_apply,
          Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
          Set.indicator_of_mem (hSG hy), Pi.one_apply]
      have hsum1 : (1 : ℝ≥0∞) ≤ ∑ σ ∈ Finset.range M, (K ^ σ) y Sᶜ := by
        have hmem : (0 : ℕ) ∈ Finset.range M := Finset.mem_range.2 hMpos
        calc (1 : ℝ≥0∞) = (K ^ 0) y Sᶜ := hterm.symm
          _ ≤ ∑ σ ∈ Finset.range M, (K ^ σ) y Sᶜ :=
              Finset.single_le_sum (f := fun σ => (K ^ σ) y Sᶜ) (fun _ _ => zero_le') hmem
      exact le_trans hesc1 (le_trans hsum1 (le_add_self))

theorem leg_escape_global {K : Kernel α α} {G S : Set α} [IsMarkovKernel K]
    (q : ℝ≥0∞) (hstep : ∀ x ∈ G, x ∈ S → K x Gᶜ ≤ q) (hSG : Gᶜ ⊆ Sᶜ)
    (t M : ℕ) (x₀ : α) :
    (∫⁻ y, (GatedDrift.killK_now K G ^ M) (some y) {(none : Option α)} ∂((K ^ t) x₀))
      ≤ (M : ℝ≥0∞) * q + ∑ τ ∈ Finset.Ico t (t + M), (K ^ τ) x₀ Sᶜ := by
  classical
  calc ∫⁻ y, (GatedDrift.killK_now K G ^ M) (some y) {(none : Option α)} ∂((K ^ t) x₀)
      ≤ ∫⁻ y, ((M : ℝ≥0∞) * q + ∑ σ ∈ Finset.range M, (K ^ σ) y Sᶜ) ∂((K ^ t) x₀) := by
        apply lintegral_mono
        intro y
        exact kill_now_escape_prefix_all (K := K) (G := G) (S := S) q hstep hSG M y
    _ = ∫⁻ _, (M : ℝ≥0∞) * q ∂((K ^ t) x₀)
        + ∫⁻ y, (∑ σ ∈ Finset.range M, (K ^ σ) y Sᶜ) ∂((K ^ t) x₀) := by
        rw [MeasureTheory.lintegral_add_left (by fun_prop)]
    _ ≤ (M : ℝ≥0∞) * q + ∑ τ ∈ Finset.Ico t (t + M), (K ^ τ) x₀ Sᶜ := by
        have hMK : ∀ s : ℕ, IsMarkovKernel (K ^ s) := by
          intro s; induction s with
          | zero => rw [pow_zero]; exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel α α))
          | succ s ih => haveI := ih; rw [pow_succ]; exact inferInstanceAs (IsMarkovKernel ((K ^ s) ∘ₖ K))
        haveI : IsMarkovKernel (K ^ t) := hMK t
        gcongr
        · rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
        · rw [MeasureTheory.lintegral_finsetSum _ (fun σ _ => by fun_prop),
            Finset.sum_Ico_eq_sum_range, show t + M - t = M from by omega]
          refine Finset.sum_le_sum (fun σ _ => ?_)
          -- ∫ (K^σ) y Sᶜ ∂((K^t) x₀) = (K^{t+σ}) x₀ Sᶜ via Chapman–Kolmogorov.
          rw [Kernel.pow_add_apply_eq_lintegral K t σ x₀
            (DiscreteMeasurableSpace.forall_measurableSet _)]

/-! ## Deliverable 3 (B-10b) — the real SEED leg, averaged with global escape.

The averaged real seed-leg bound: integrating over the GLOBAL leg-start distribution
`(realκ^Tstart) c₀`, the real `M`-step mass missing the (numerical) `SeedPost` is bounded by
`εseed` (the killed convergence) PLUS the global escape budget `M·q + ∑_{τ∈[Tstart,Tstart+M)}
(realκ^τ) c₀ Qsetᶜ`.  The side set is `S = G = Qset` (so `Qsetᶜ = Sᶜ`, `hSG := rfl`).

The proof routes the real mass through `real_le_killed_now`, splits the killed target
`{none ∨ some-bad} = {none} ∪ {¬optLift SeedPost}` (note `none ∉ {¬optLift SeedPost}`), and:
* the `{none}` integral is the GLOBAL escape → `leg_escape_global`;
* the `{¬optLift SeedPost}` integral splits over `Qset`/`Qsetᶜ`: on `Qset` the killed seed
  convergence gives `εseed`; on `Qsetᶜ` the ungated killed walk dies in step 1 and the target
  excludes `none`, so the mass is `0` (requires `0 < M` — always true for a real leg).
-/

/-- The killed-seed walk from an UNGATED start `y ∉ Qset`, after `M ≥ 1` steps, places no mass
on `{¬ optLift SeedPost}` (it dies into the cemetery `none`, which lies OUTSIDE that set). -/
theorem killed_seed_ungated_post_zero (n mC T : ℕ) (M : ℕ) (hM : 0 < M) (y : Cfg L K)
    (hy : y ∉ Qset (L := L) (K := K) n mC T) :
    ((κQ_now (L := L) (K := K) n mC T) ^ M) (some y)
      {o | ¬ optLift (SeedPost (L := L) (K := K) n mC T) o} = 0 := by
  classical
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  -- κQ_now (some y) = δ none; after M'+1 steps mass concentrates on none ∉ target.
  have hstep : (κQ_now (L := L) (K := K) n mC T) (some y) = Measure.dirac (none : Option (Cfg L K)) :=
    GatedDrift.killK_now_ungated (K := realκ L K) (G := Qset (L := L) (K := K) n mC T) y hy
  rw [show M' + 1 = 1 + M' from by ring,
    Kernel.pow_add_apply_eq_lintegral (κQ_now (L := L) (K := K) n mC T) 1 M' (some y)
      (DiscreteMeasurableSpace.forall_measurableSet _), pow_one, hstep,
    MeasureTheory.lintegral_dirac' _ (by fun_prop : Measurable fun o =>
      ((κQ_now (L := L) (K := K) n mC T) ^ M') o
        {o | ¬ optLift (SeedPost (L := L) (K := K) n mC T) o})]
  rw [GatedDrift.none_absorbing_now M',
    Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
    Set.indicator_of_notMem (show (none : Option (Cfg L K)) ∉
      {o | ¬ optLift (SeedPost (L := L) (K := K) n mC T) o} from by
        simp only [Set.mem_setOf_eq, not_not]; exact trivial)]

/-- **The killed `{¬optLift SeedPost}` integral, averaged over the global leg-start.**  On
`Qset` the killed seed convergence gives `εseed`; on `Qsetᶜ` (for `0 < M`) the mass is `0`.
So the whole integral is `≤ εseed`. -/
theorem killed_seed_avg_le (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hT : T < K * (L + 1))
    (M : ℕ) (hM : 0 < M) (εseed : ℝ≥0)
    (hεs : minuteRate n mC ^ M *
        ENNReal.ofReal (Real.exp (Real.log 2 * (seedLo mC : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (Tstart : ℕ) (c₀ : Cfg L K) :
    (∫⁻ y, ((κQ_now (L := L) (K := K) n mC T) ^ M) (some y)
        {o | ¬ optLift (SeedPost (L := L) (K := K) n mC T) o} ∂((realκ L K ^ Tstart) c₀))
      ≤ (εseed : ℝ≥0∞) := by
  classical
  have hmeasG : MeasurableSet (Qset (L := L) (K := K) n mC T) :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hMK : ∀ s : ℕ, IsMarkovKernel (realκ L K ^ s) := by
    intro s; induction s with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel (Cfg L K) (Cfg L K)))
    | succ s ih => haveI := ih; rw [pow_succ]; exact inferInstanceAs (IsMarkovKernel ((realκ L K ^ s) ∘ₖ realκ L K))
  haveI : IsMarkovKernel (realκ L K ^ Tstart) := hMK Tstart
  rw [← lintegral_add_compl (fun y => ((κQ_now (L := L) (K := K) n mC T) ^ M) (some y)
      {o | ¬ optLift (SeedPost (L := L) (K := K) n mC T) o}) hmeasG]
  have hG : ∫⁻ y in Qset (L := L) (K := K) n mC T,
        ((κQ_now (L := L) (K := K) n mC T) ^ M) (some y)
          {o | ¬ optLift (SeedPost (L := L) (K := K) n mC T) o} ∂((realκ L K ^ Tstart) c₀)
      ≤ (εseed : ℝ≥0∞) := by
    calc ∫⁻ y in Qset (L := L) (K := K) n mC T,
            ((κQ_now (L := L) (K := K) n mC T) ^ M) (some y)
              {o | ¬ optLift (SeedPost (L := L) (K := K) n mC T) o} ∂((realκ L K ^ Tstart) c₀)
        ≤ ∫⁻ _ in Qset (L := L) (K := K) n mC T, (εseed : ℝ≥0∞) ∂((realκ L K ^ Tstart) c₀) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hmeasG] with y hy
          exact clock_killed_seed_stepW (L := L) (K := K) n mC T hn hmC hT M εseed hεs (some y)
            (show optLift (SeedPre (L := L) (K := K) n mC T) (some y) from hy)
      _ ≤ (εseed : ℝ≥0∞) := by
          rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ]
          calc (εseed : ℝ≥0∞) * ((realκ L K ^ Tstart) c₀ (Qset (L := L) (K := K) n mC T))
              ≤ (εseed : ℝ≥0∞) * 1 := by
                gcongr
                exact (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)
            _ = _ := mul_one _
  have hGc : ∫⁻ y in (Qset (L := L) (K := K) n mC T)ᶜ,
        ((κQ_now (L := L) (K := K) n mC T) ^ M) (some y)
          {o | ¬ optLift (SeedPost (L := L) (K := K) n mC T) o} ∂((realκ L K ^ Tstart) c₀) = 0 := by
    rw [MeasureTheory.lintegral_eq_zero_iff (by fun_prop)]
    filter_upwards [ae_restrict_mem hmeasG.compl] with y hy
    exact killed_seed_ungated_post_zero (L := L) (K := K) n mC T M hM y hy
  rw [hGc, add_zero]; exact hG

/-- **`clock_real_seed_leg_avg` (B-10b) — the real SEED leg, averaged with global escape.**

Integrating over the GLOBAL leg-start distribution `(realκ^Tstart) c₀`, the real `M`-step mass
missing `SeedPost n mC T` is bounded by `εseed + (M·q + ∑_{τ∈[Tstart,Tstart+M)} (realκ^τ) c₀
Qsetᶜ)`.  `q` is the per-step gate-escape rate (`∀ x∈Qset, realκ x Qsetᶜ ≤ q`).  `S = G = Qset`,
so `hSG := rfl`. -/
theorem clock_real_seed_leg_avg (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hT : T < K * (L + 1))
    (M : ℕ) (hM : 0 < M) (εseed : ℝ≥0)
    (hεs : minuteRate n mC ^ M *
        ENNReal.ofReal (Real.exp (Real.log 2 * (seedLo mC : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (q : ℝ≥0∞)
    (hstep : ∀ x ∈ Qset (L := L) (K := K) n mC T,
        realκ L K x (Qset (L := L) (K := K) n mC T)ᶜ ≤ q)
    (Tstart : ℕ) (c₀ : Cfg L K) :
    (∫⁻ y, ((realκ L K) ^ M) y {c | ¬ SeedPost (L := L) (K := K) n mC T c}
        ∂((realκ L K ^ Tstart) c₀))
      ≤ (εseed : ℝ≥0∞)
        + ((M : ℝ≥0∞) * q
          + ∑ τ ∈ Finset.Ico Tstart (Tstart + M),
              (realκ L K ^ τ) c₀ (Qset (L := L) (K := K) n mC T)ᶜ) := by
  classical
  set bad : Cfg L K → Prop := fun c => ¬ SeedPost (L := L) (K := K) n mC T c with hbad
  set G : Set (Cfg L K) := Qset (L := L) (K := K) n mC T with hG
  -- Step 1: route the real mass through real_le_killed_now (pointwise in the start y).
  calc ∫⁻ y, ((realκ L K) ^ M) y {c | bad c} ∂((realκ L K ^ Tstart) c₀)
      ≤ ∫⁻ y, ((κQ_now (L := L) (K := K) n mC T) ^ M) (some y)
          {o | o = none ∨ (∃ c, o = some c ∧ bad c)} ∂((realκ L K ^ Tstart) c₀) := by
        apply lintegral_mono
        intro y
        exact GatedDrift.real_le_killed_now (K := realκ L K) (G := G) bad M y
    -- Step 2: split the killed target into {none} ∪ {¬optLift SeedPost}; union bound pointwise.
    _ ≤ ∫⁻ y, (((κQ_now (L := L) (K := K) n mC T) ^ M) (some y) {(none : Option (Cfg L K))}
          + ((κQ_now (L := L) (K := K) n mC T) ^ M) (some y)
              {o | ¬ optLift (SeedPost (L := L) (K := K) n mC T) o})
          ∂((realκ L K ^ Tstart) c₀) := by
        apply lintegral_mono
        intro y
        refine le_trans (measure_mono ?_) (measure_union_le _ _)
        intro o ho
        rcases ho with hnone | ⟨c, rfl, hbadc⟩
        · exact Or.inl (by rw [Set.mem_singleton_iff]; exact hnone)
        · exact Or.inr (show ¬ optLift (SeedPost (L := L) (K := K) n mC T) (some c) from hbadc)
    _ = (∫⁻ y, ((κQ_now (L := L) (K := K) n mC T) ^ M) (some y) {(none : Option (Cfg L K))}
            ∂((realκ L K ^ Tstart) c₀))
        + (∫⁻ y, ((κQ_now (L := L) (K := K) n mC T) ^ M) (some y)
              {o | ¬ optLift (SeedPost (L := L) (K := K) n mC T) o} ∂((realκ L K ^ Tstart) c₀)) := by
        rw [MeasureTheory.lintegral_add_left (by fun_prop)]
    -- Step 3+4: escape integral ≤ leg_escape_global; the post integral ≤ εseed.
    _ ≤ ((M : ℝ≥0∞) * q + ∑ τ ∈ Finset.Ico Tstart (Tstart + M),
            (realκ L K ^ τ) c₀ Gᶜ) + (εseed : ℝ≥0∞) := by
        refine add_le_add ?_ ?_
        · exact leg_escape_global (K := realκ L K) (G := G) (S := G) q
            (fun x hx _ => hstep x hx) (le_refl _) Tstart M c₀
        · exact killed_seed_avg_le (L := L) (K := K) n mC T hn hmC hT M hM εseed hεs Tstart c₀
    _ = (εseed : ℝ≥0∞) + ((M : ℝ≥0∞) * q
          + ∑ τ ∈ Finset.Ico Tstart (Tstart + M), (realκ L K ^ τ) c₀ Gᶜ) := by
        rw [add_comm]

/-! ## Deliverable 3 (B-10b, bulk half) — the real BULK leg, averaged with global escape.

Mirror of the seed half, with kernel `κQ_now_bulk`, gate `QbulkSet = {QbulkWin}`, `BulkPost`,
convergence `clock_killed_bulk_stepW`. -/

/-- Bulk analogue of `killed_seed_ungated_post_zero`. -/
theorem killed_bulk_ungated_post_zero (n mC T : ℕ) (M : ℕ) (hM : 0 < M) (y : Cfg L K)
    (hy : y ∉ QbulkSet (L := L) (K := K) n mC T) :
    ((κQ_now_bulk (L := L) (K := K) n mC T) ^ M) (some y)
      {o | ¬ optLift (BulkPost (L := L) (K := K) n mC T) o} = 0 := by
  classical
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hstep : (κQ_now_bulk (L := L) (K := K) n mC T) (some y)
      = Measure.dirac (none : Option (Cfg L K)) :=
    GatedDrift.killK_now_ungated (K := realκ L K)
      (G := QbulkSet (L := L) (K := K) n mC T) y hy
  rw [show M' + 1 = 1 + M' from by ring,
    Kernel.pow_add_apply_eq_lintegral (κQ_now_bulk (L := L) (K := K) n mC T) 1 M' (some y)
      (DiscreteMeasurableSpace.forall_measurableSet _), pow_one, hstep,
    MeasureTheory.lintegral_dirac' _ (by fun_prop : Measurable fun o =>
      ((κQ_now_bulk (L := L) (K := K) n mC T) ^ M') o
        {o | ¬ optLift (BulkPost (L := L) (K := K) n mC T) o})]
  rw [GatedDrift.none_absorbing_now M',
    Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
    Set.indicator_of_notMem (show (none : Option (Cfg L K)) ∉
      {o | ¬ optLift (BulkPost (L := L) (K := K) n mC T) o} from by
        simp only [Set.mem_setOf_eq, not_not]; exact trivial)]

/-- Bulk analogue of `killed_seed_avg_le`. -/
theorem killed_bulk_avg_le (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hT : T < K * (L + 1))
    (M : ℕ) (hM : 0 < M) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ M *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (Tstart : ℕ) (c₀ : Cfg L K) :
    (∫⁻ y, ((κQ_now_bulk (L := L) (K := K) n mC T) ^ M) (some y)
        {o | ¬ optLift (BulkPost (L := L) (K := K) n mC T) o} ∂((realκ L K ^ Tstart) c₀))
      ≤ (εbulk : ℝ≥0∞) := by
  classical
  have hmeasG : MeasurableSet (QbulkSet (L := L) (K := K) n mC T) :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hMK : ∀ s : ℕ, IsMarkovKernel (realκ L K ^ s) := by
    intro s; induction s with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel (Cfg L K) (Cfg L K)))
    | succ s ih => haveI := ih; rw [pow_succ]; exact inferInstanceAs (IsMarkovKernel ((realκ L K ^ s) ∘ₖ realκ L K))
  haveI : IsMarkovKernel (realκ L K ^ Tstart) := hMK Tstart
  rw [← lintegral_add_compl (fun y => ((κQ_now_bulk (L := L) (K := K) n mC T) ^ M) (some y)
      {o | ¬ optLift (BulkPost (L := L) (K := K) n mC T) o}) hmeasG]
  have hG : ∫⁻ y in QbulkSet (L := L) (K := K) n mC T,
        ((κQ_now_bulk (L := L) (K := K) n mC T) ^ M) (some y)
          {o | ¬ optLift (BulkPost (L := L) (K := K) n mC T) o} ∂((realκ L K ^ Tstart) c₀)
      ≤ (εbulk : ℝ≥0∞) := by
    calc ∫⁻ y in QbulkSet (L := L) (K := K) n mC T,
            ((κQ_now_bulk (L := L) (K := K) n mC T) ^ M) (some y)
              {o | ¬ optLift (BulkPost (L := L) (K := K) n mC T) o} ∂((realκ L K ^ Tstart) c₀)
        ≤ ∫⁻ _ in QbulkSet (L := L) (K := K) n mC T, (εbulk : ℝ≥0∞) ∂((realκ L K ^ Tstart) c₀) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hmeasG] with y hy
          exact clock_killed_bulk_stepW (L := L) (K := K) n mC T hn hmC hT M εbulk hεb (some y)
            (show optLift (BulkPre (L := L) (K := K) n mC T) (some y) from hy)
      _ ≤ (εbulk : ℝ≥0∞) := by
          rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ]
          calc (εbulk : ℝ≥0∞) * ((realκ L K ^ Tstart) c₀ (QbulkSet (L := L) (K := K) n mC T))
              ≤ (εbulk : ℝ≥0∞) * 1 := by
                gcongr
                exact (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)
            _ = _ := mul_one _
  have hGc : ∫⁻ y in (QbulkSet (L := L) (K := K) n mC T)ᶜ,
        ((κQ_now_bulk (L := L) (K := K) n mC T) ^ M) (some y)
          {o | ¬ optLift (BulkPost (L := L) (K := K) n mC T) o} ∂((realκ L K ^ Tstart) c₀) = 0 := by
    rw [MeasureTheory.lintegral_eq_zero_iff (by fun_prop)]
    filter_upwards [ae_restrict_mem hmeasG.compl] with y hy
    exact killed_bulk_ungated_post_zero (L := L) (K := K) n mC T M hM y hy
  rw [hGc, add_zero]; exact hG

/-- **`clock_real_bulk_leg_avg` (B-10b, bulk) — the real BULK leg, averaged with global
escape.**  Mirror of `clock_real_seed_leg_avg`; gate `QbulkSet`, `S = G = QbulkSet`. -/
theorem clock_real_bulk_leg_avg (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hT : T < K * (L + 1))
    (M : ℕ) (hM : 0 < M) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ M *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (q : ℝ≥0∞)
    (hstep : ∀ x ∈ QbulkSet (L := L) (K := K) n mC T,
        realκ L K x (QbulkSet (L := L) (K := K) n mC T)ᶜ ≤ q)
    (Tstart : ℕ) (c₀ : Cfg L K) :
    (∫⁻ y, ((realκ L K) ^ M) y {c | ¬ BulkPost (L := L) (K := K) n mC T c}
        ∂((realκ L K ^ Tstart) c₀))
      ≤ (εbulk : ℝ≥0∞)
        + ((M : ℝ≥0∞) * q
          + ∑ τ ∈ Finset.Ico Tstart (Tstart + M),
              (realκ L K ^ τ) c₀ (QbulkSet (L := L) (K := K) n mC T)ᶜ) := by
  classical
  set bad : Cfg L K → Prop := fun c => ¬ BulkPost (L := L) (K := K) n mC T c with hbad
  set G : Set (Cfg L K) := QbulkSet (L := L) (K := K) n mC T with hG
  calc ∫⁻ y, ((realκ L K) ^ M) y {c | bad c} ∂((realκ L K ^ Tstart) c₀)
      ≤ ∫⁻ y, ((κQ_now_bulk (L := L) (K := K) n mC T) ^ M) (some y)
          {o | o = none ∨ (∃ c, o = some c ∧ bad c)} ∂((realκ L K ^ Tstart) c₀) := by
        apply lintegral_mono
        intro y
        exact GatedDrift.real_le_killed_now (K := realκ L K) (G := G) bad M y
    _ ≤ ∫⁻ y, (((κQ_now_bulk (L := L) (K := K) n mC T) ^ M) (some y) {(none : Option (Cfg L K))}
          + ((κQ_now_bulk (L := L) (K := K) n mC T) ^ M) (some y)
              {o | ¬ optLift (BulkPost (L := L) (K := K) n mC T) o})
          ∂((realκ L K ^ Tstart) c₀) := by
        apply lintegral_mono
        intro y
        refine le_trans (measure_mono ?_) (measure_union_le _ _)
        intro o ho
        rcases ho with hnone | ⟨c, rfl, hbadc⟩
        · exact Or.inl (by rw [Set.mem_singleton_iff]; exact hnone)
        · exact Or.inr (show ¬ optLift (BulkPost (L := L) (K := K) n mC T) (some c) from hbadc)
    _ = (∫⁻ y, ((κQ_now_bulk (L := L) (K := K) n mC T) ^ M) (some y) {(none : Option (Cfg L K))}
            ∂((realκ L K ^ Tstart) c₀))
        + (∫⁻ y, ((κQ_now_bulk (L := L) (K := K) n mC T) ^ M) (some y)
              {o | ¬ optLift (BulkPost (L := L) (K := K) n mC T) o} ∂((realκ L K ^ Tstart) c₀)) := by
        rw [MeasureTheory.lintegral_add_left (by fun_prop)]
    _ ≤ ((M : ℝ≥0∞) * q + ∑ τ ∈ Finset.Ico Tstart (Tstart + M),
            (realκ L K ^ τ) c₀ Gᶜ) + (εbulk : ℝ≥0∞) := by
        refine add_le_add ?_ ?_
        · exact leg_escape_global (K := realκ L K) (G := G) (S := G) q
            (fun x hx _ => hstep x hx) (le_refl _) Tstart M c₀
        · exact killed_bulk_avg_le (L := L) (K := K) n mC T hn hmC hT M hM εbulk hεb Tstart c₀
    _ = (εbulk : ℝ≥0∞) + ((M : ℝ≥0∞) * q
          + ∑ τ ∈ Finset.Ico Tstart (Tstart + M), (realκ L K ^ τ) c₀ Gᶜ) := by
        rw [add_comm]

/-! ## Deliverable 3 (B-10c) — the assembled real MINUTE, global escape.

### The minute is the BULK leg, started AFTER the seed phase (window offset = `tseed`).

CK-gluing `(realκ^(Tstart+tseed+tbulk)) c₀ {¬BulkPost}
= ∫ (realκ^tbulk) y {¬BulkPost} ∂((realκ^(Tstart+tseed)) c₀)` and applying
`clock_real_bulk_leg_avg` at leg-start `Tstart+tseed` gives the per-minute mass bound
  `(realκ^(Tstart+tseed+tbulk)) c₀ {¬BulkPost}
     ≤ εbulk + tbulk·q + ∑_{τ∈[Tstart+tseed, Tstart+tseed+tbulk)} (realκ^τ) c₀ QbulkSetᶜ`.

### DOCUMENTED DEVIATION from the campaign §3 budget (`εseed + εbulk + both escapes`).

The averaged/global design makes the SEED leg's separate `εseed` and the seed escape budget
UNNECESSARY as additive budget terms.  The seed leg's role manifests instead as the WINDOW
OFFSET: the bulk leg's prefix sum runs over `τ ≥ Tstart + tseed`, i.e. only over post-seed
times.  All boundary re-establishment — including the within-minute `Q_mix` re-establishment AND
the `mC/10` infected-floor re-establishment — is charged to the SINGLE side-set
`S = QbulkSet = {QbulkWin} = {Q_mix n mC T ∧ mC/10 ≤ rBeyond (T+1)}`, whose per-`τ` failure mass
`(realκ^τ) c₀ QbulkSetᶜ` is exactly what `WidthPrefix.goodFrontWidth_whp_at` + the endpoint
bridges discharge later (the seed drip establishes the `mC/10` floor whp by time `Tstart+tseed`,
so the post-seed prefix terms are whp-small).  This is STRICTLY CLEANER than the nominal budget
(fewer terms, one side-set) and HONEST: nothing is dropped, the seed obligation is relocated
into the (later-discharged) prefix sum rather than carried as `εseed`.

### THE SIDE-SET `S` (report answer).
`S = QbulkSet = {QbulkWin n mC T} = {Q_mix n mC T ∧ mC/10 ≤ rBeyond (T+1)}`.  The boundary
`Q_mix` re-establishment charges to `(realκ^τ) c₀ QbulkSetᶜ` at `τ = Tstart+tseed` (inside the
prefix sum).  `S = G` (the gate), so `leg_escape_global`'s `hSG := rfl`. -/

/-- **`clock_real_minute_avg` (B-10c) — the assembled real minute, global escape.** -/
theorem clock_real_minute_avg (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hT : T < K * (L + 1))
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (q : ℝ≥0∞)
    (hstep : ∀ x ∈ QbulkSet (L := L) (K := K) n mC T,
        realκ L K x (QbulkSet (L := L) (K := K) n mC T)ᶜ ≤ q)
    (Tstart : ℕ) (c₀ : Cfg L K) :
    ((realκ L K) ^ (Tstart + tseed + tbulk)) c₀
        {c | ¬ BulkPost (L := L) (K := K) n mC T c}
      ≤ (εbulk : ℝ≥0∞)
        + ((tbulk : ℝ≥0∞) * q
          + ∑ τ ∈ Finset.Ico (Tstart + tseed) (Tstart + tseed + tbulk),
              (realκ L K ^ τ) c₀ (QbulkSet (L := L) (K := K) n mC T)ᶜ) := by
  classical
  -- CK: split the global window at Tstart+tseed.
  rw [Kernel.pow_add_apply_eq_lintegral (realκ L K) (Tstart + tseed) tbulk c₀
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  exact clock_real_bulk_leg_avg (L := L) (K := K) n mC T hn hmC hT tbulk htbulk εbulk hεb q hstep
    (Tstart + tseed) c₀

/-! ## Deliverable 4 (B-10d) — the `Fin L₀` minute family + the all-minutes endpoint.

### DOCUMENTED DEVIATION: no deterministic cross-minute `composeW_n_phases` chain.

The campaign §4 design wires the minutes with `Q_mix_succ_of_post`-analogues and `composeW`.
`Q_mix_succ_of_post` needs `Q_mix n mC T c` (the FULL window at level `T`) at the boundary, but
the NUMERICAL-only Posts (`BulkPost = bulkHi mC ≤ rBeyond (T+1)`) do NOT carry `Q_mix`.  This is
the SAME residual obstruction the killed brick flagged (§B-9: the `Q_mix` endpoint conjunct is
recovered from the side gates, NOT from the killed Post) and that forced the two-kernel split.
A deterministic `Post i → Pre (i+1)` chain at the real level is therefore NOT available without
the unproven front-shape synchronization (`HabsDischarge.ClockPhase3_remaining_synchronization`).

The averaged/global design resolves this WITHOUT a deterministic chain: each minute `T`'s bound
is a STANDALONE averaged-global bulk-leg bound (`clock_real_minute_avg` at its own offset),
charging ALL boundary re-establishment (including `Q_mix(T)` recovery) to its per-minute side
prefix `∑_{τ∈window_T} (realκ^τ) c₀ QbulkSet(T)ᶜ`.  The "all minutes" content is then the family
of per-minute standalone bounds, summed (union bound) at the endpoint — NOT a composed chain.

### The per-minute side-set varies (design item C): `S_T = QbulkSet n mC T` (gate at level `T`).
The endpoint budget is the HONEST double sum `∑_{i<L₀} (εbulk + tbulk·q + ∑_{τ∈window_i}
(realκ^τ) c₀ QbulkSet(i.val)ᶜ)`; the per-minute side prefixes are discharged later by the
WidthPrefix `∀ τ` family at each level.  No single fixed-`S` global prefix exists because the
floor gate `rBeyond (T+1)` tracks the minute level `T`. -/

/-- **`minuteFailW` — the per-minute standalone failure budget (the `Fin L₀` family).**

For minute `i : Fin L₀`, started at the cumulative offset `i.val * (tseed + tbulk)`, the real
mass missing minute-`i`'s `BulkPost` is bounded by `εbulk + tbulk·q + (the minute's per-`τ`
gate-failure prefix)`.  This is `clock_real_minute_avg` packaged as a family. -/
theorem minuteFailW (n mC L₀ : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hL₀cap : L₀ ≤ K * (L + 1))
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (q : ℝ≥0∞)
    (hstep : ∀ T : ℕ, ∀ x ∈ QbulkSet (L := L) (K := K) n mC T,
        realκ L K x (QbulkSet (L := L) (K := K) n mC T)ᶜ ≤ q)
    (c₀ : Cfg L K) (i : Fin L₀) :
    ((realκ L K) ^ (i.val * (tseed + tbulk) + tseed + tbulk)) c₀
        {c | ¬ BulkPost (L := L) (K := K) n mC i.val c}
      ≤ (εbulk : ℝ≥0∞)
        + ((tbulk : ℝ≥0∞) * q
          + ∑ τ ∈ Finset.Ico (i.val * (tseed + tbulk) + tseed)
              (i.val * (tseed + tbulk) + tseed + tbulk),
              (realκ L K ^ τ) c₀ (QbulkSet (L := L) (K := K) n mC i.val)ᶜ) :=
  clock_real_minute_avg (L := L) (K := K) n mC i.val hn hmC
    (by have := i.isLt; omega) tseed tbulk htbulk εbulk hεb q (hstep i.val)
    (i.val * (tseed + tbulk)) c₀

/-- **`clock_real_faithful_all_minutes_W` (B-10d) — the all-minutes endpoint, union-bounded.**

The total failure that SOME minute `i < L₀` misses its `BulkPost` is at most the sum over
minutes of the per-minute standalone budgets (union bound over the `Fin L₀` family).  Budget:
`L₀·εbulk + L₀·tbulk·q + ∑_i (minute-i gate-failure prefix)`. -/
theorem clock_real_faithful_all_minutes_W (n mC L₀ : ℕ) (hL₀ : 0 < L₀)
    (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hL₀cap : L₀ ≤ K * (L + 1))
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (q : ℝ≥0∞)
    (hstep : ∀ T : ℕ, ∀ x ∈ QbulkSet (L := L) (K := K) n mC T,
        realκ L K x (QbulkSet (L := L) (K := K) n mC T)ᶜ ≤ q)
    (c₀ : Cfg L K) :
    ∑ i : Fin L₀, ((realκ L K) ^ (i.val * (tseed + tbulk) + tseed + tbulk)) c₀
        {c | ¬ BulkPost (L := L) (K := K) n mC i.val c}
      ≤ ∑ i : Fin L₀, ((εbulk : ℝ≥0∞)
          + ((tbulk : ℝ≥0∞) * q
            + ∑ τ ∈ Finset.Ico (i.val * (tseed + tbulk) + tseed)
                (i.val * (tseed + tbulk) + tseed + tbulk),
                (realκ L K ^ τ) c₀ (QbulkSet (L := L) (K := K) n mC i.val)ᶜ)) :=
  Finset.sum_le_sum (fun i _ =>
    minuteFailW (L := L) (K := K) n mC L₀ hn hmC hL₀cap tseed tbulk htbulk εbulk hεb q hstep c₀ i)

/-! ## Deliverable 5 (B-10e) — `clock_real_faithful_O_log_n_W`: the O(log n) endpoint wrapper.

Instantiates `clock_real_faithful_all_minutes_W` at `L₀ = K·(L+1)` (the protocol's full minute
count `= k·⌈log₂ n⌉`), giving total interactions `K·(L+1)·(tseed+tbulk) = O(n·log n)` (parallel
`/n = O(log n)`), failure `≤ K·(L+1)·εbulk + K·(L+1)·tbulk·q + ∑_i (per-minute prefixes)`.

### HONEST VERDICT (the WEAK assembly, replacing `ClockRealFaithfulHours`).

This is the WEAK faithful clock: the per-minute legs are killed-kernel `PhaseConvergenceW`
tails (numerical-only Posts), and ALL boundary re-establishment is charged to the per-minute
side prefixes `∑_{τ∈window_i} (realκ^τ) c₀ QbulkSet(i.val)ᶜ`.

* It DISCHARGES the FALSE `habs_mix` (the deterministic `Q_mix` window closure the OLD
  `ClockRealFaithfulHours` assembly carried as a ∀-minute hypothesis) — that hypothesis is GONE.
* In its place it carries (as NAMED hypotheses, NOT discharged here):
  - `hstep` — the per-step gate-escape rate `∀ T, ∀ x∈QbulkSet, realκ x QbulkSetᶜ ≤ q` (the §6
    "drip-only excess counter" one-step bound from a gated config);
  - the per-minute side prefixes are LEFT in the conclusion's RHS (NOT bounded here) — they are
    discharged LATER by `WidthPrefix.goodFrontWidth_whp_at` + the endpoint bridges +
    `Params` (the seed drip establishes the `mC/10` floor whp, so the post-seed prefix terms
    are whp-small).  This file leaves all parameters raw; it does NOT discharge them.
* DEVIATION (documented at `clock_real_minute_avg` / `clock_real_faithful_all_minutes_W`): no
  separate `εseed` term (the seed leg is the window offset), no deterministic cross-minute
  chain (numerical Posts don't carry `Q_mix`; the union-bound endpoint replaces `composeW`).

The OLD `ClockRealFaithfulHours.clock_real_faithful_O_log_n` is NOT deleted (retirement is a
later cleanup); this is its `habs_mix`-free replacement. -/
theorem clock_real_faithful_O_log_n_W (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1))
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (q : ℝ≥0∞)
    (hstep : ∀ T : ℕ, ∀ x ∈ QbulkSet (L := L) (K := K) n mC T,
        realκ L K x (QbulkSet (L := L) (K := K) n mC T)ᶜ ≤ q)
    (c₀ : Cfg L K) :
    ∑ i : Fin (K * (L + 1)),
        ((realκ L K) ^ (i.val * (tseed + tbulk) + tseed + tbulk)) c₀
          {c | ¬ BulkPost (L := L) (K := K) n mC i.val c}
      ≤ ∑ i : Fin (K * (L + 1)), ((εbulk : ℝ≥0∞)
          + ((tbulk : ℝ≥0∞) * q
            + ∑ τ ∈ Finset.Ico (i.val * (tseed + tbulk) + tseed)
                (i.val * (tseed + tbulk) + tseed + tbulk),
                (realκ L K ^ τ) c₀ (QbulkSet (L := L) (K := K) n mC i.val)ᶜ)) :=
  clock_real_faithful_all_minutes_W (L := L) (K := K) n mC (K * (L + 1)) hLK hn hmC
    (le_refl (K * (L + 1))) tseed tbulk htbulk εbulk hεb q hstep c₀

/-! ## Status. -/
theorem clock_weak_assembly_status : True := trivial

end ClockWeakAssembly

end ExactMajority
