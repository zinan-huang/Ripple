import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealSeed
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedKillNow
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.KernelWindowDrift

/-!
# ClockKilledMinute — the killed clock-minute (Doty §6 Phase B step 3 deep brick)

A faithful clock minute is two killed phases composed on `Option (Config (AgentState L K))`:
a SEED leg (`rBeyond (T+1)` rises from the `0.9·mC` prior floor up past `seedLo mC = mC/10`)
and a BULK leg (`rBeyond (T+1)` rises from `mC/10` past `bulkHi mC = 9·mC/10`).  We run them
on the IMMEDIATE-kill kernel `killK_now (realκ) Qset` (`GatedKillNow`), gating on the mixed
window `Qset = {Q_mix n mC T}`.

## Post-shape choice (documented): NUMERICAL-ONLY killed Post.

The full one-step closure of `Q_mix` (`habs_mix`) is NOT proven — it rests on the unproven
front-shape synchronization (`HabsDischarge.ClockPhase3_remaining_synchronization`).  We
therefore do NOT carry the `Q_mix` conjunct in the killed `Post`.  Two facts make this clean:

* the killed kernel `killK_now` FILTERS successors through the gate (`alive_support_gate`):
  any ALIVE successor already lies in `Qset = {Q_mix}` by construction, so we never need to
  prove the real dynamics preserve `Q_mix`;
* the unguarded potential `rSeedPot` links to the NUMERICAL threshold only
  (`not_finished_imp_rSeedPot_ge_one`), so `SeedPost`/`BulkPost` are numerical crossings.

`SeedPost some c := mC/10 ≤ rBeyond (T+1) c`,  `BulkPost some c := bulkHi mC ≤ rBeyond (T+1) c`
(and `none` is accepted in both `Pre`/`Post` so the weak composer chains cemetery endpoints).
The `Q_mix` endpoint conjunct (when a downstream consumer needs it) is recovered separately
from the side gates, NOT from the killed Post.

## Drift hypothesis: UNCONDITIONAL (per `KernelWindowDrift`).

The killed drift `∀ o, ∫ killΦ Φ ∂(killK_now o) ≤ minuteRate · killΦ Φ o` holds at EVERY `o`:
at the cemetery and off-gate it is `0 ≤ 0`; on-gate alive it reduces (via the gate-filtered
pushforward, dropping the dead mass since `killΦ Φ none = 0`) to the REAL unguarded drift
`rSeedPot_contracts_seed` / `_bulk`.  No `r ≥ 1` and no `Q`-absorption is needed.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators Classical

namespace ClockKilledMinute

open ClockRealKernel ClockRealMixed ClockRealSeed ClockRealBulk ClockMonoDischarge
open GatedDrift KernelWindowDrift

variable {L K : ℕ}

abbrev Cfg (L K : ℕ) := Config (AgentState L K)

/-- A default `AgentState` (every field has a default inhabitant), giving the `Inhabited`
instance that `killK_now`'s `Option`-machinery (`Option.getD default`) requires. -/
instance : Inhabited (AgentState L K) :=
  ⟨{ input := .A, output := .A, phase := default, role := default, assigned := false,
     bias := .zero, smallBias := default, hour := default, minute := default,
     full := false, opinions := default, counter := default }⟩

/-- The cemetery extension carries the discrete (`⊤`) measurable space (matching
`GatedKillNow`'s local instances). -/
local instance instOptionMSckm : MeasurableSpace (Option (Cfg L K)) := ⊤
local instance instOptionDMSckm : DiscreteMeasurableSpace (Option (Cfg L K)) :=
  ⟨fun _ => trivial⟩

noncomputable abbrev realκ (L K : ℕ) : Kernel (Cfg L K) (Cfg L K) :=
  (NonuniformMajority L K).transitionKernel

/-- The mixed-window gate `Qset = {Q_mix n mC T}`. -/
def Qset (n mC T : ℕ) : Set (Cfg L K) := {c | Q_mix (L := L) (K := K) n mC T c}

/-- The bulk SYNC gate `QbulkSet = {QbulkWin n mC T}` = `Q_mix` AND the `mC/10` infected
floor.  The bulk leg gates on THIS (stronger) window: the `mC/10` floor is the invariant the
bulk drift `rSeedPot_contracts_bulk` consumes, and it is preserved along alive killed
successors via `hmono_mix_discharged`. -/
def QbulkSet (n mC T : ℕ) : Set (Cfg L K) := {c | QbulkWin (L := L) (K := K) n mC T c}

/-- The killed SEED kernel: immediate-kill on the mixed window `Q_mix`. -/
noncomputable abbrev κQ_now (n mC T : ℕ) : Kernel (Option (Cfg L K)) (Option (Cfg L K)) :=
  GatedDrift.killK_now (realκ L K) (Qset (L := L) (K := K) n mC T)

/-- The killed BULK kernel: immediate-kill on the bulk SYNC window `QbulkWin` (carries the
`mC/10` infected floor that the bulk drift consumes). -/
noncomputable abbrev κQ_now_bulk (n mC T : ℕ) :
    Kernel (Option (Cfg L K)) (Option (Cfg L K)) :=
  GatedDrift.killK_now (realκ L K) (QbulkSet (L := L) (K := K) n mC T)

/-- SEED `Pre`: the mixed window AND the `0.9·mC` prior floor at level `T`. -/
def SeedPre (n mC T : ℕ) (c : Cfg L K) : Prop :=
  Q_mix (L := L) (K := K) n mC T c

/-- SEED `Post` (NUMERICAL-ONLY): crossed the seed band `mC/10`. -/
def SeedPost (n mC T : ℕ) (c : Cfg L K) : Prop :=
  seedLo mC ≤ rBeyond (L := L) (K := K) (T + 1) c

/-- BULK `Pre`: the mixed window AND the `mC/10` infected floor. -/
def BulkPre (n mC T : ℕ) (c : Cfg L K) : Prop :=
  QbulkWin (L := L) (K := K) n mC T c

/-- BULK `Post` (NUMERICAL-ONLY): crossed the bulk band `bulkHi mC`. -/
def BulkPost (n mC T : ℕ) (c : Cfg L K) : Prop :=
  bulkHi mC ≤ rBeyond (L := L) (K := K) (T + 1) c

/-- Lift a config predicate to `Option`, accepting the cemetery `none`. -/
def optLift (P : Cfg L K → Prop) : Option (Cfg L K) → Prop
  | none => True
  | some c => P c

/-- The killed seed potential: the unguarded level-`seedLo mC` potential, `0` at cemetery. -/
noncomputable def seedΦ (mC T : ℕ) : Option (Cfg L K) → ℝ≥0∞ :=
  GatedDrift.killΦ (fun c => rSeedPot (L := L) (K := K) (seedLo mC) T (Real.log 2) c)

/-- The killed bulk potential: the unguarded level-`bulkHi mC` potential, `0` at cemetery. -/
noncomputable def bulkΦ (mC T : ℕ) : Option (Cfg L K) → ℝ≥0∞ :=
  GatedDrift.killΦ (fun c => rSeedPot (L := L) (K := K) (bulkHi mC) T (Real.log 2) c)

/-- The genuine clock-fraction-squared minute contraction rate. -/
noncomputable def minuteRate (n mC : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ) /
      ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-Real.log 2)))

/-- **Killed-integral reduction.**  For a gated alive state `some c` (`c ∈ Qset`), the killed
integral of `killΦ Φ` reduces to the REAL integral of the gate-FILTERED potential
`fun y => if y ∈ Qset then Φ y else 0`, which is ≤ the real integral of `Φ` itself (the dead
mass contributes `0`).  This is the bridge from the killed drift to the unguarded real drift. -/
theorem killed_int_le_real (n mC T : ℕ) (Φ : Cfg L K → ℝ≥0∞) (c : Cfg L K)
    (hQ : Q_mix (L := L) (K := K) n mC T c) :
    ∫⁻ o, GatedDrift.killΦ Φ o ∂(κQ_now (L := L) (K := K) n mC T (some c))
      ≤ ∫⁻ y, Φ y ∂(realκ L K c) := by
  have hc : c ∈ Qset (L := L) (K := K) n mC T := hQ
  rw [show κQ_now (L := L) (K := K) n mC T (some c)
        = (realκ L K c).map (GatedDrift.gateMap (Qset (L := L) (K := K) n mC T)) from
      GatedDrift.killK_now_some_gated (K := realκ L K) (G := Qset (L := L) (K := K) n mC T) c hc,
    MeasureTheory.lintegral_map (GatedDrift.killΦ_measurable Φ)
      (GatedDrift.gateMap_measurable _)]
  refine lintegral_mono (fun y => ?_)
  unfold GatedDrift.gateMap
  by_cases hyG : y ∈ Qset (L := L) (K := K) n mC T
  · rw [if_pos hyG, GatedDrift.killΦ_some]
  · rw [if_neg hyG, GatedDrift.killΦ_none]; exact zero_le'

/-- The bulk-gate analogue of `killed_int_le_real`: for `c ∈ QbulkSet`, the killed-bulk
integral of `killΦ Φ` is bounded by the real integral of `Φ` (dead mass contributes `0`). -/
theorem killed_int_le_real_bulk (n mC T : ℕ) (Φ : Cfg L K → ℝ≥0∞) (c : Cfg L K)
    (hQ : QbulkWin (L := L) (K := K) n mC T c) :
    ∫⁻ o, GatedDrift.killΦ Φ o ∂(κQ_now_bulk (L := L) (K := K) n mC T (some c))
      ≤ ∫⁻ y, Φ y ∂(realκ L K c) := by
  have hc : c ∈ QbulkSet (L := L) (K := K) n mC T := hQ
  rw [show κQ_now_bulk (L := L) (K := K) n mC T (some c)
        = (realκ L K c).map (GatedDrift.gateMap (QbulkSet (L := L) (K := K) n mC T)) from
      GatedDrift.killK_now_some_gated (K := realκ L K)
        (G := QbulkSet (L := L) (K := K) n mC T) c hc,
    MeasureTheory.lintegral_map (GatedDrift.killΦ_measurable Φ)
      (GatedDrift.gateMap_measurable _)]
  refine lintegral_mono (fun y => ?_)
  unfold GatedDrift.gateMap
  by_cases hyG : y ∈ QbulkSet (L := L) (K := K) n mC T
  · rw [if_pos hyG, GatedDrift.killΦ_some]
  · rw [if_neg hyG, GatedDrift.killΦ_none]; exact zero_le'

/-- On the mixed window, if the level-`H` band is already finished at `c`, then the real
integral of the level-`H` potential vanishes: every successor preserves the crossing (via
`hmono_mix_discharged`), so the integrand is `0` a.e. -/
theorem real_int_zero_of_finished (n mC T H : ℕ) (c : Cfg L K)
    (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hfin : H ≤ rBeyond (L := L) (K := K) (T + 1) c) :
    ∫⁻ y, rSeedPot (L := L) (K := K) H T (Real.log 2) y ∂(realκ L K c) = 0 := by
  rw [MeasureTheory.lintegral_eq_zero_iff (rSeedPot_measurable (L := L) (K := K) H T (Real.log 2))]
  have hae : ∀ᵐ y ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure,
      H ≤ rBeyond (L := L) (K := K) (T + 1) y := by
    rw [MeasureTheory.ae_iff]
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {y | ¬ H ≤ rBeyond (L := L) (K := K) (T + 1) y} = 0
    rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _),
      Set.disjoint_left]
    intro y hsupp hbad
    have hmono := hmono_mix_discharged n mC T c y hQ hsupp
    exact hbad (le_trans hfin hmono)
  filter_upwards [hae] with y hy
  show rSeedPot (L := L) (K := K) H T (Real.log 2) y = 0
  unfold rSeedPot
  rw [if_pos hy]

/-- **The killed SEED drift (UNCONDITIONAL).**  At EVERY `o`, the killed integral of `seedΦ`
contracts at `minuteRate`. -/
theorem killed_seed_drift (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hT : T < K * (L + 1)) :
    ∀ o : Option (Cfg L K),
      ∫⁻ o', seedΦ (L := L) (K := K) mC T o' ∂(κQ_now (L := L) (K := K) n mC T o)
        ≤ minuteRate n mC * seedΦ (L := L) (K := K) mC T o := by
  have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmeas : Measurable (seedΦ (L := L) (K := K) mC T) := GatedDrift.killΦ_measurable _
  intro o
  rcases o with _ | c
  · -- cemetery: κQ_now none = δ none, both sides 0.
    rw [GatedDrift.killK_now_none, MeasureTheory.lintegral_dirac' _ hmeas]
    simp only [seedΦ, GatedDrift.killΦ_none, mul_zero, le_refl]
  · by_cases hQ : c ∈ Qset (L := L) (K := K) n mC T
    · -- gated alive: reduce to real integral, then split finished / seed-regime.
      have hQ' : Q_mix (L := L) (K := K) n mC T c := hQ
      refine le_trans (killed_int_le_real n mC T _ c hQ') ?_
      have hΦc : seedΦ (L := L) (K := K) mC T (some c)
          = rSeedPot (L := L) (K := K) (seedLo mC) T (Real.log 2) c := rfl
      by_cases hfin : seedLo mC ≤ rBeyond (L := L) (K := K) (T + 1) c
      · -- finished: real integral = 0 ≤ RHS.
        rw [real_int_zero_of_finished n mC T (seedLo mC) c hQ' hfin]
        exact zero_le'
      · -- seed regime: apply the unguarded real seed drift.
        have hnc : rBeyond (L := L) (K := K) (T + 1) c < seedLo mC := by omega
        have hreal := rSeedPot_contracts_seed (L := L) (K := K) n mC T hn hmC hT
          (Real.log 2) hs c hQ' hnc
        rw [hΦc]; exact hreal
    · -- ungated alive: κQ_now (some c) = δ none, LHS = seedΦ none = 0 ≤ RHS.
      rw [GatedDrift.killK_now_ungated c hQ, MeasureTheory.lintegral_dirac' _ hmeas]
      simp only [seedΦ, GatedDrift.killΦ_none]
      exact zero_le'

/-- **The killed BULK drift (UNCONDITIONAL).**  At EVERY `o`, the killed-bulk integral of
`bulkΦ` contracts at `minuteRate`.  The bulk gate `QbulkWin` carries the `mC/10` infected
floor `hlo` that `rSeedPot_contracts_bulk` consumes. -/
theorem killed_bulk_drift (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hT : T < K * (L + 1)) :
    ∀ o : Option (Cfg L K),
      ∫⁻ o', bulkΦ (L := L) (K := K) mC T o' ∂(κQ_now_bulk (L := L) (K := K) n mC T o)
        ≤ minuteRate n mC * bulkΦ (L := L) (K := K) mC T o := by
  have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmeas : Measurable (bulkΦ (L := L) (K := K) mC T) := GatedDrift.killΦ_measurable _
  intro o
  rcases o with _ | c
  · -- cemetery: both sides 0.
    rw [GatedDrift.killK_now_none, MeasureTheory.lintegral_dirac' _ hmeas]
    simp only [bulkΦ, GatedDrift.killΦ_none, mul_zero, le_refl]
  · by_cases hQ : c ∈ QbulkSet (L := L) (K := K) n mC T
    · have hQbw : QbulkWin (L := L) (K := K) n mC T c := hQ
      have hQ' : Q_mix (L := L) (K := K) n mC T c := hQbw.1
      have hlo : mC / 10 ≤ rBeyond (L := L) (K := K) (T + 1) c := hQbw.2
      refine le_trans (killed_int_le_real_bulk n mC T _ c hQbw) ?_
      have hΦc : bulkΦ (L := L) (K := K) mC T (some c)
          = rSeedPot (L := L) (K := K) (bulkHi mC) T (Real.log 2) c := rfl
      by_cases hfin : bulkHi mC ≤ rBeyond (L := L) (K := K) (T + 1) c
      · rw [real_int_zero_of_finished n mC T (bulkHi mC) c hQ' hfin]
        exact zero_le'
      · have hnc : rBeyond (L := L) (K := K) (T + 1) c < bulkHi mC := by omega
        have hreal := rSeedPot_contracts_bulk (L := L) (K := K) n mC T hn hmC hT
          (Real.log 2) hs c hQ' hlo hnc
        rw [hΦc]; exact hreal
    · -- ungated alive: κQ_now_bulk (some c) = δ none.
      rw [GatedDrift.killK_now_ungated c hQ, MeasureTheory.lintegral_dirac' _ hmeas]
      simp only [bulkΦ, GatedDrift.killΦ_none]
      exact zero_le'

/-- **The killed SEED phase** (weak phase convergence on `κQ_now`).  Threshold `θ = 1`; the
`¬SeedPost → 1 ≤ seedΦ` link is `not_finished_imp_rSeedPot_ge_one`; `none` is accepted in both
`Pre`/`Post`. -/
noncomputable def killedSeedPhase (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hT : T < K * (L + 1)) (tseed : ℕ) (εseed : ℝ≥0)
    (hεs : minuteRate n mC ^ tseed *
        ENNReal.ofReal (Real.exp (Real.log 2 * (seedLo mC : ℝ))) / 1 ≤ (εseed : ℝ≥0∞)) :
    PhaseConvergenceW (κQ_now (L := L) (K := K) n mC T) :=
  KernelWindowDrift.kernelWindowDrift_PhaseConvergenceW
    (seedΦ (L := L) (K := K) mC T) (GatedDrift.killΦ_measurable _)
    (minuteRate n mC) (killed_seed_drift (L := L) (K := K) n mC T hn hmC hT)
    (optLift (SeedPre (L := L) (K := K) n mC T))
    (optLift (SeedPost (L := L) (K := K) n mC T))
    1 one_ne_zero ENNReal.one_ne_top
    (by
      have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      intro o hnot
      rcases o with _ | c
      · exact absurd trivial hnot
      · -- ¬ SeedPost c = ¬ rFinished (seedLo mC) T c → 1 ≤ rSeedPot.
        have hnf : ¬ rFinished (L := L) (K := K) (seedLo mC) T c := hnot
        exact not_finished_imp_rSeedPot_ge_one (L := L) (K := K) (seedLo mC) T
          (Real.log 2) hs c hnf)
    (ENNReal.ofReal (Real.exp (Real.log 2 * (seedLo mC : ℝ))))
    (by
      have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      intro o _
      rcases o with _ | c
      · simp only [seedΦ, GatedDrift.killΦ_none]; exact zero_le'
      · exact rSeedPot_le_max (L := L) (K := K) (seedLo mC) T (Real.log 2) hs c)
    tseed εseed hεs

/-- **The killed BULK phase** (weak phase convergence on `κQ_now_bulk`).  Threshold `θ = 1`;
the `¬BulkPost → 1 ≤ bulkΦ` link is `not_finished_imp_rSeedPot_ge_one` at level `bulkHi mC`. -/
noncomputable def killedBulkPhase (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hT : T < K * (L + 1)) (tbulk : ℕ) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞)) :
    PhaseConvergenceW (κQ_now_bulk (L := L) (K := K) n mC T) :=
  KernelWindowDrift.kernelWindowDrift_PhaseConvergenceW
    (bulkΦ (L := L) (K := K) mC T) (GatedDrift.killΦ_measurable _)
    (minuteRate n mC) (killed_bulk_drift (L := L) (K := K) n mC T hn hmC hT)
    (optLift (BulkPre (L := L) (K := K) n mC T))
    (optLift (BulkPost (L := L) (K := K) n mC T))
    1 one_ne_zero ENNReal.one_ne_top
    (by
      have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      intro o hnot
      rcases o with _ | c
      · exact absurd trivial hnot
      · have hnf : ¬ rFinished (L := L) (K := K) (bulkHi mC) T c := hnot
        exact not_finished_imp_rSeedPot_ge_one (L := L) (K := K) (bulkHi mC) T
          (Real.log 2) hs c hnf)
    (ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))))
    (by
      have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      intro o _
      rcases o with _ | c
      · simp only [bulkΦ, GatedDrift.killΦ_none]; exact zero_le'
      · exact rSeedPot_le_max (L := L) (K := K) (bulkHi mC) T (Real.log 2) hs c)
    tbulk εbulk hεb

/-! ## The killed-leg tails and the real-leg transfer.

Two notes on the composition shape (DOCUMENTED DEVIATION from the blueprint §4
`clock_killed_stepW`):

* The SEED leg gates on `Q_mix` (kernel `κQ_now`); the BULK leg gates on the STRONGER
  `QbulkWin` (kernel `κQ_now_bulk`), because `rSeedPot_contracts_bulk` consumes the `mC/10`
  infected floor.  These are DIFFERENT kernels, so a single-kernel `composeW_two_phases` is
  NOT available here without unifying the gate to a single window that tracks the `mC/10`
  floor for ALL alive successors — which is exactly the front-shape floor invariant the
  blueprint flags (the unproven `HabsDischarge.ClockPhase3_remaining_synchronization` family).
  We therefore deliver the two legs SEPARATELY (each a `PhaseConvergenceW` tail) plus the
  REAL-leg transfer for the seed leg, rather than a single composed minute.  Consumers chain
  the two legs at the level of the real kernel via the per-leg real transfers.
-/

/-- The killed SEED leg tail on `κQ_now`: from a `SeedPre` (lifted) start, the `tseed`-step
mass missing `SeedPost` is `≤ εseed`. -/
theorem clock_killed_seed_stepW (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hT : T < K * (L + 1)) (tseed : ℕ) (εseed : ℝ≥0)
    (hεs : minuteRate n mC ^ tseed *
        ENNReal.ofReal (Real.exp (Real.log 2 * (seedLo mC : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (o₀ : Option (Cfg L K)) (ho₀ : optLift (SeedPre (L := L) (K := K) n mC T) o₀) :
    ((κQ_now (L := L) (K := K) n mC T) ^ tseed) o₀
      {o | ¬ optLift (SeedPost (L := L) (K := K) n mC T) o} ≤ (εseed : ℝ≥0∞) :=
  (killedSeedPhase (L := L) (K := K) n mC T hn hmC hT tseed εseed hεs).convergence o₀ ho₀

/-- The killed BULK leg tail on `κQ_now_bulk`: from a `BulkPre` (lifted) start, the
`tbulk`-step mass missing `BulkPost` is `≤ εbulk`. -/
theorem clock_killed_bulk_stepW (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hT : T < K * (L + 1)) (tbulk : ℕ) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (o₀ : Option (Cfg L K)) (ho₀ : optLift (BulkPre (L := L) (K := K) n mC T) o₀) :
    ((κQ_now_bulk (L := L) (K := K) n mC T) ^ tbulk) o₀
      {o | ¬ optLift (BulkPost (L := L) (K := K) n mC T) o} ≤ (εbulk : ℝ≥0∞) :=
  (killedBulkPhase (L := L) (K := K) n mC T hn hmC hT tbulk εbulk hεb).convergence o₀ ho₀

/-- **The real seed-leg transfer** (blueprint §5).  The REAL `tseed`-step mass of the bad set
`{¬ SeedPost}` is bounded by the ESCAPE mass `(κQ_now^tseed)(some c₀){none}` plus the killed
seed-leg failure mass.  Proven via `real_le_killed_now` + the `{none} ∪ {some bad}` split. -/
theorem clock_real_seed_step_gated (n mC T : ℕ)
    (tseed : ℕ) (εseed εesc : ℝ≥0∞) (c₀ : Cfg L K)
    (hesc : ((κQ_now (L := L) (K := K) n mC T) ^ tseed) (some c₀)
        {(none : Option (Cfg L K))} ≤ εesc)
    (hkilled : ((κQ_now (L := L) (K := K) n mC T) ^ tseed) (some c₀)
        {o | ¬ optLift (SeedPost (L := L) (K := K) n mC T) o} ≤ εseed) :
    ((realκ L K) ^ tseed) c₀
      {c | ¬ SeedPost (L := L) (K := K) n mC T c} ≤ εesc + εseed := by
  classical
  set bad : Cfg L K → Prop := fun c => ¬ SeedPost (L := L) (K := K) n mC T c with hbad
  refine le_trans (GatedDrift.real_le_killed_now (K := realκ L K)
    (G := Qset (L := L) (K := K) n mC T) bad tseed c₀) ?_
  -- {o = none ∨ ∃ c, o = some c ∧ bad c} ⊆ {none} ∪ {some c | bad c}; union bound.
  set A : Set (Option (Cfg L K)) := {(none : Option (Cfg L K))} with hA
  set B : Set (Option (Cfg L K)) := {o | ∃ c, o = some c ∧ bad c} with hB
  have hsub : {o : Option (Cfg L K) | o = none ∨ (∃ c, o = some c ∧ bad c)} ⊆ A ∪ B := by
    intro o ho
    rcases ho with hnone | hsome
    · exact Or.inl (by rw [hA, Set.mem_singleton_iff]; exact hnone)
    · exact Or.inr hsome
  calc ((κQ_now (L := L) (K := K) n mC T) ^ tseed) (some c₀)
        {o | o = none ∨ (∃ c, o = some c ∧ bad c)}
      ≤ ((κQ_now (L := L) (K := K) n mC T) ^ tseed) (some c₀) (A ∪ B) := measure_mono hsub
    _ ≤ ((κQ_now (L := L) (K := K) n mC T) ^ tseed) (some c₀) A
          + ((κQ_now (L := L) (K := K) n mC T) ^ tseed) (some c₀) B := measure_union_le _ _
    _ ≤ εesc + εseed := by
        refine add_le_add (le_trans ?_ hesc) (le_trans (measure_mono ?_) hkilled)
        · exact le_of_eq rfl
        · -- {some c | bad c} ⊆ {o | ¬ optLift SeedPost o}
          intro o ho
          rcases ho with ⟨c, rfl, hbadc⟩
          exact hbadc

end ClockKilledMinute
end ExactMajority
