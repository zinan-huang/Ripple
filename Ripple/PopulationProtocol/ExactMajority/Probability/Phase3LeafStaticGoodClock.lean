import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3StaticInvCountClosed
import Ripple.PopulationProtocol.ExactMajority.Probability.ProtocolTraceLaw
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3StrictCutTiming

/-!
# Slot-3 leaf static fact from GoodClock (the deterministic core)

`LeafStaticInvGood` needs `StaticInv` at the 3 cut configs `tr(cut)`.  Since `StaticInv` is only
`FrontSync`-guarded-step-closed (Slot3StaticInvCountClosed), the discharge is a fixed-horizon stopped
prefix argument: pick a deterministic horizon `T` above all cuts (`LeafCutsBoundedBy`), assume the run
is a support path up to `T` and `FrontSync` on `[0,T)`, then the prefix induction gives `StaticInv` at
each cut.  The probabilistic side (a.e. support path, `FrontSyncPrefixBad` tail from the proven
front-width whp) is handled separately and feeds these deterministic pieces.  (Proofs reuse the committed
`staticInv_step_of_frontSync`.)
-/

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase3LeafStaticGoodClock

open Phase3Assembly.LeafTail Phase3StaticInvCountClosed

variable {L K : ℕ}

/-- Run is a kernel-support path on the finite prefix `[0, T)`. -/
def TraceSupportPathUpTo (T : ℕ) (tr : Phase3GoodClock.Trace L K) : Prop :=
  ∀ τ, τ < T → tr (τ + 1) ∈ ((NonuniformMajority L K).stepDistOrSelf (tr τ)).support

/-- `FrontSync` holds on the whole prefix `[0, T)`. -/
def FrontSyncPrefix (T : ℕ) (tr : Phase3GoodClock.Trace L K) : Prop :=
  ∀ τ, τ < T → ClockFrontShape.FrontSync (L := L) (K := K) (tr τ)

/-- The three GoodClock cuts all land below a deterministic horizon `T`. -/
def LeafCutsBoundedBy (T : ℕ) (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams) (tr : Phase3GoodClock.Trace L K) : Prop :=
  ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr) (h : ℕ), h ≤ D.lastCoreHour →
    (coreInput (L := L) (K := K) D θ tr G h).start + θ.twoOverC + θ.fortySevenOverM < T

/-- **Finite stopped-prefix induction** (the `≤ T` version of `staticInv_at_time_of_frontSync_prefix`).
Avoids needing the support path / FrontSync for all infinite time. -/
theorem staticInv_at_time_upTo {D : Phase3Core.Phase3ModeDomain L} {C : ℝ} {T : ℕ}
    {entry : Config (AgentState L K)} {tr : Phase3GoodClock.Trace L K}
    (hstart : tr 0 = entry)
    (hpath : TraceSupportPathUpTo (L := L) (K := K) T tr)
    (hentry : StaticInv (L := L) (K := K) D C entry)
    (t : ℕ) (htT : t ≤ T)
    (hfront : ∀ τ, τ < t → ClockFrontShape.FrontSync (L := L) (K := K) (tr τ)) :
    StaticInv (L := L) (K := K) D C (tr t) := by
  induction t with
  | zero => simpa [hstart] using hentry
  | succ t ih =>
      have htT' : t < T := by omega
      have hs_t : StaticInv (L := L) (K := K) D C (tr t) :=
        ih (by omega) (fun τ hτ => hfront τ (by omega))
      exact staticInv_step_of_frontSync (L := L) (K := K) hs_t
        (hfront t (by omega)) (hpath t htT')

/-- **The deterministic implication**: on the good prefix event, `LeafStaticInvGood` holds. -/
theorem leafStaticInvGood_of_prefix {D : Phase3Core.Phase3ModeDomain L} {C : ℝ} {T : ℕ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)} {tr : Phase3GoodClock.Trace L K}
    (hentry : StaticInv (L := L) (K := K) D C entry)
    (hstart : tr 0 = entry)
    (hpath : TraceSupportPathUpTo (L := L) (K := K) T tr)
    (hfront : FrontSyncPrefix (L := L) (K := K) T tr)
    (hcuts : LeafCutsBoundedBy (L := L) (K := K) T D θ tr) :
    LeafStaticInvGood (L := L) (K := K) D C θ tr := by
  refine ⟨fun G h hh => ?_, fun G h hh => ?_, fun G h hh => ?_⟩
  · -- afterO cut = start + twoOverC
    have h47 := hcuts G h hh
    have hlt : (coreInput (L := L) (K := K) D θ tr G h).start + θ.twoOverC < T := by omega
    exact staticInv_at_time_upTo (L := L) (K := K) hstart hpath hentry _ (le_of_lt hlt)
      (fun τ hτ => hfront τ (by omega))
  · -- afterPhi cut = start + twoOverC + fortyOneOverM
    have h47 := hcuts G h hh
    have h41 := θ.fortyOne_le_fortySeven
    have hlt : (coreInput (L := L) (K := K) D θ tr G h).start + θ.twoOverC + θ.fortyOneOverM < T := by
      omega
    exact staticInv_at_time_upTo (L := L) (K := K) hstart hpath hentry _ (le_of_lt hlt)
      (fun τ hτ => hfront τ (by omega))
  · -- afterMass cut = start + twoOverC + fortySevenOverM
    have h47 := hcuts G h hh
    exact staticInv_at_time_upTo (L := L) (K := K) hstart hpath hentry _ (le_of_lt h47)
      (fun τ hτ => hfront τ (by omega))

/-! ## Measure side — the fixed-horizon FrontSync-prefix tail (the probabilistic input) -/

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- `FrontSync` fails at some prefix time `< T`. -/
def FrontSyncPrefixBad (T : ℕ) (tr : Phase3GoodClock.Trace L K) : Prop :=
  ∃ τ, τ < T ∧ ¬ ClockFrontShape.FrontSync (L := L) (K := K) (tr τ)

/-- Endpoint kernel `¬FrontSync` bound transfers to the trace-time marginal (via `endpoint_law`). -/
theorem trace_frontSync_time_bound (entry : Config (AgentState L K)) (τ : ℕ) (ε : ℝ≥0∞)
    (hτ : ((NonuniformMajority L K).transitionKernel ^ τ) entry
        {c : Config (AgentState L K) | ¬ ClockFrontShape.FrontSync (L := L) (K := K) c} ≤ ε) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr : Phase3GoodClock.Trace L K | ¬ ClockFrontShape.FrontSync (L := L) (K := K) (tr τ)} ≤ ε := by
  classical
  have hS : MeasurableSet
      {c : Config (AgentState L K) | ¬ ClockFrontShape.FrontSync (L := L) (K := K) c} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  rw [show {tr : Phase3GoodClock.Trace L K | ¬ ClockFrontShape.FrontSync (L := L) (K := K) (tr τ)}
      = (fun tr : Phase3GoodClock.Trace L K => tr τ) ⁻¹'
        {c : Config (AgentState L K) | ¬ ClockFrontShape.FrontSync (L := L) (K := K) c} from rfl]
  rw [← Measure.map_apply (measurable_pi_apply τ) hS,
    (ProtocolTraceLaw.traceLawAt (L := L) (K := K) entry τ).endpoint_law]
  exact hτ

/-- Fixed-horizon union bound: the prefix-`FrontSync`-bad event is `≤ Σ_{τ<T}` the per-time bounds. -/
theorem frontSyncPrefixBad_le_sum (entry : Config (AgentState L K)) (T : ℕ) (ε : ℕ → ℝ≥0∞)
    (hε : ∀ τ, τ < T → ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr : Phase3GoodClock.Trace L K | ¬ ClockFrontShape.FrontSync (L := L) (K := K) (tr τ)} ≤ ε τ) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr : Phase3GoodClock.Trace L K | FrontSyncPrefixBad (L := L) (K := K) T tr}
      ≤ ∑ τ ∈ Finset.range T, ε τ := by
  classical
  induction T with
  | zero =>
      have hempty : {tr : Phase3GoodClock.Trace L K | FrontSyncPrefixBad (L := L) (K := K) 0 tr} = ∅ := by
        ext tr; constructor
        · rintro ⟨τ, hτ, _⟩; omega
        · intro h; exact False.elim h
      rw [hempty]; simp
  | succ T ih =>
      have hsubset :
          {tr : Phase3GoodClock.Trace L K | FrontSyncPrefixBad (L := L) (K := K) (T + 1) tr}
            ⊆ {tr | FrontSyncPrefixBad (L := L) (K := K) T tr} ∪
              {tr | ¬ ClockFrontShape.FrontSync (L := L) (K := K) (tr T)} := by
        intro tr htr
        rcases htr with ⟨τ, hτ, hbad⟩
        by_cases hτT : τ < T
        · exact Or.inl ⟨τ, hτT, hbad⟩
        · have hτeq : τ = T := by omega
          exact Or.inr (by simpa [hτeq] using hbad)
      calc
        ProtocolTraceLaw.μ (L := L) (K := K) entry
            {tr : Phase3GoodClock.Trace L K | FrontSyncPrefixBad (L := L) (K := K) (T + 1) tr}
            ≤ ProtocolTraceLaw.μ (L := L) (K := K) entry
              ({tr | FrontSyncPrefixBad (L := L) (K := K) T tr} ∪
                {tr | ¬ ClockFrontShape.FrontSync (L := L) (K := K) (tr T)}) := measure_mono hsubset
        _ ≤ ProtocolTraceLaw.μ (L := L) (K := K) entry
              {tr | FrontSyncPrefixBad (L := L) (K := K) T tr} +
            ProtocolTraceLaw.μ (L := L) (K := K) entry
              {tr | ¬ ClockFrontShape.FrontSync (L := L) (K := K) (tr T)} := measure_union_le _ _
        _ ≤ (∑ τ ∈ Finset.range T, ε τ) + ε T :=
              add_le_add (ih (fun τ hτ => hε τ (by omega))) (hε T (by omega))
        _ = ∑ τ ∈ Finset.range (T + 1), ε τ := by rw [Finset.sum_range_succ]

end Phase3LeafStaticGoodClock

namespace ProtocolTraceLaw

open ProbabilityTheory MeasureTheory Finset Preorder
open scoped ENNReal

variable {L K : ℕ}

private lemma singleStepSupport_bad_measurable (τ : ℕ) :
    MeasurableSet
      {tr : Phase3GoodClock.Trace L K |
        ¬ tr (τ + 1) ∈ ((NonuniformMajority L K).stepDistOrSelf (tr τ)).support} := by
  classical
  have hR : MeasurableSet
      {p : Config (AgentState L K) × Config (AgentState L K) |
        ¬ p.2 ∈ ((NonuniformMajority L K).stepDistOrSelf p.1).support} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hmap : Measurable (fun tr : Phase3GoodClock.Trace L K => (tr τ, tr (τ + 1))) :=
    (measurable_pi_apply τ).prod (measurable_pi_apply (τ + 1))
  exact hR.preimage hmap

private lemma traj_prefix_coord_ae (τ : ℕ) (x : Π i : Finset.Iic τ, St L K i) :
    ∀ᵐ tr ∂(Kernel.traj (kfamily (L := L) (K := K)) τ x),
      tr τ = x ⟨τ, Finset.mem_Iic.2 le_rfl⟩ := by
  classical
  set m : Measure (Phase3GoodClock.Trace L K) :=
    Kernel.traj (kfamily (L := L) (K := K)) τ x with hm
  have hmap : Measure.map (frestrictLe (π := St L K) τ) m = Measure.dirac x := by
    rw [hm, Kernel.traj_map_frestrictLe_apply (κ := kfamily (L := L) (K := K)) τ τ x,
      Kernel.partialTraj_self, Kernel.id_apply]
  have hS : MeasurableSet {y : Π i : Finset.Iic τ, St L K i | y ≠ x} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hzero : m {tr : Phase3GoodClock.Trace L K | frestrictLe (π := St L K) τ tr ≠ x} = 0 := by
    calc
      m ((frestrictLe (π := St L K) τ) ⁻¹' {y : Π i : Finset.Iic τ, St L K i | y ≠ x})
          = Measure.map (frestrictLe (π := St L K) τ) m
              {y : Π i : Finset.Iic τ, St L K i | y ≠ x} := by
            rw [Measure.map_apply (measurable_frestrictLe τ) hS]
      _ = Measure.dirac x {y : Π i : Finset.Iic τ, St L K i | y ≠ x} := by rw [hmap]
      _ = 0 := by simp
  have hprefix : ∀ᵐ tr ∂m, frestrictLe (π := St L K) τ tr = x := by
    rw [ae_iff]; simpa using hzero
  exact hprefix.mono (by
    intro tr htr
    have hcoord := congrFun htr ⟨τ, Finset.mem_Iic.2 le_rfl⟩
    simpa [frestrictLe] using hcoord)

private lemma traj_succ_coord_support_ae (τ : ℕ) (x : Π i : Finset.Iic τ, St L K i) :
    ∀ᵐ tr ∂(Kernel.traj (kfamily (L := L) (K := K)) τ x),
      tr (τ + 1) ∈
        ((NonuniformMajority L K).stepDistOrSelf (x ⟨τ, Finset.mem_Iic.2 le_rfl⟩)).support := by
  classical
  set m : Measure (Phase3GoodClock.Trace L K) :=
    Kernel.traj (kfamily (L := L) (K := K)) τ x with hm
  set succCoord : (Π i : Finset.Iic (τ + 1), St L K i) → Config (AgentState L K) :=
    fun y => y ⟨τ + 1, Finset.mem_Iic.2 le_rfl⟩ with hsucc
  have hmap_restrict :
      Measure.map (frestrictLe (π := St L K) (τ + 1)) m
        = Kernel.partialTraj (kfamily (L := L) (K := K)) τ (τ + 1) x := by
    rw [hm]; exact Kernel.traj_map_frestrictLe_apply (κ := kfamily (L := L) (K := K)) τ (τ + 1) x
  have hmap_partial :
      Measure.map succCoord (Kernel.partialTraj (kfamily (L := L) (K := K)) τ (τ + 1) x)
        = kfamily (L := L) (K := K) τ x := by
    rw [hsucc, ← Kernel.map_apply _ (measurable_pi_apply _) x,
      Kernel.map_partialTraj_succ_self]
  have hcomp_succ :
      (succCoord ∘ frestrictLe (π := St L K) (τ + 1))
        = (fun tr : Phase3GoodClock.Trace L K => tr (τ + 1)) := by
    rw [hsucc]; funext tr; simp [frestrictLe]
  have hmap_succ :
      Measure.map (fun tr : Phase3GoodClock.Trace L K => tr (τ + 1)) m
        = kfamily (L := L) (K := K) τ x := by
    calc
      Measure.map (fun tr : Phase3GoodClock.Trace L K => tr (τ + 1)) m
          = Measure.map succCoord (Measure.map (frestrictLe (π := St L K) (τ + 1)) m) := by
            rw [← hcomp_succ,
              Measure.map_map (measurable_pi_apply _) (measurable_frestrictLe (τ + 1))]
      _ = Measure.map succCoord (Kernel.partialTraj (kfamily (L := L) (K := K)) τ (τ + 1) x) := by
          rw [hmap_restrict]
      _ = kfamily (L := L) (K := K) τ x := hmap_partial
  have hS : MeasurableSet
      {y : Config (AgentState L K) |
        y ∉ ((NonuniformMajority L K).stepDistOrSelf (x ⟨τ, Finset.mem_Iic.2 le_rfl⟩)).support} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hk_zero :
      kfamily (L := L) (K := K) τ x
        {y : Config (AgentState L K) |
          y ∉ ((NonuniformMajority L K).stepDistOrSelf (x ⟨τ, Finset.mem_Iic.2 le_rfl⟩)).support} = 0 := by
    unfold kfamily Protocol.transitionKernel
    rw [Kernel.comap_apply]
    change ((NonuniformMajority L K).stepDistOrSelf (x ⟨τ, Finset.mem_Iic.2 le_rfl⟩)).toMeasure
      {y : Config (AgentState L K) |
        y ∉ ((NonuniformMajority L K).stepDistOrSelf (x ⟨τ, Finset.mem_Iic.2 le_rfl⟩)).support} = 0
    rw [PMF.toMeasure_apply_eq_zero_iff _ hS, Set.disjoint_left]
    intro y hy hbad; exact hbad hy
  have hzero :
      m ((fun tr : Phase3GoodClock.Trace L K => tr (τ + 1)) ⁻¹'
          {y : Config (AgentState L K) |
            y ∉ ((NonuniformMajority L K).stepDistOrSelf (x ⟨τ, Finset.mem_Iic.2 le_rfl⟩)).support}) = 0 := by
    rw [← Measure.map_apply (measurable_pi_apply (τ + 1)) hS, hmap_succ]
    exact hk_zero
  rw [ae_iff]; exact hzero

private lemma traj_single_step_support_ae (τ : ℕ) (x : Π i : Finset.Iic τ, St L K i) :
    ∀ᵐ tr ∂(Kernel.traj (kfamily (L := L) (K := K)) τ x),
      tr (τ + 1) ∈ ((NonuniformMajority L K).stepDistOrSelf (tr τ)).support := by
  filter_upwards [traj_prefix_coord_ae (L := L) (K := K) τ x,
    traj_succ_coord_support_ae (L := L) (K := K) τ x] with tr hτ hsupp
  rw [hτ]; exact hsupp

private theorem one_step_support_ae (entry : Config (AgentState L K)) (τ : ℕ) :
    ∀ᵐ tr ∂(μ (L := L) (K := K) entry),
      tr (τ + 1) ∈ ((NonuniformMajority L K).stepDistOrSelf (tr τ)).support := by
  classical
  have hbad_meas : MeasurableSet {tr : Phase3GoodClock.Trace L K |
      ¬ tr (τ + 1) ∈ ((NonuniformMajority L K).stepDistOrSelf (tr τ)).support} :=
    singleStepSupport_bad_measurable (L := L) (K := K) τ
  have hcomp :
      (Kernel.traj (kfamily (L := L) (K := K)) τ) ∘ₖ
          (Kernel.partialTraj (kfamily (L := L) (K := K)) 0 τ)
        = Kernel.traj (kfamily (L := L) (K := K)) 0 :=
    Kernel.traj_comp_partialTraj (κ := kfamily (L := L) (K := K)) (Nat.zero_le τ)
  have hμ : μ (L := L) (K := K) entry
      = ((Kernel.traj (kfamily (L := L) (K := K)) τ) ∘ₖ
          (Kernel.partialTraj (kfamily (L := L) (K := K)) 0 τ)) (fun _ => entry) := by
    unfold μ traj0; rw [← hcomp]
  rw [ae_iff, hμ, Kernel.comp_apply' _ _ _ hbad_meas,
    lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad_meas)]
  refine ae_of_all _ (fun x => ?_)
  exact ae_iff.mp (traj_single_step_support_ae (L := L) (K := K) τ x)

theorem supportPathUpTo_ae (entry : Config (AgentState L K)) (T : ℕ) :
    ∀ᵐ tr ∂(μ (L := L) (K := K) entry),
      ∀ τ, τ < T → tr (τ + 1) ∈ ((NonuniformMajority L K).stepDistOrSelf (tr τ)).support := by
  rw [ae_all_iff]; intro τ
  by_cases hτ : τ < T
  · exact (one_step_support_ae (L := L) (K := K) entry τ).mono (fun tr hsupp _ => hsupp)
  · exact ae_of_all _ (fun _ hlt => False.elim (hτ hlt))

end ProtocolTraceLaw

/-! ## Static-branch leaf assembly — `¬LeafStaticInvGood` charged to the FrontSync-prefix tail

The corrected discharge of the leaf static event.  Since `StaticInvStepClosed` is FALSE
unconditionally (clock at cap advances past phase 3), the static fact is NOT charged zero;
instead, on the support-path event (a.e., `supportPathUpTo_ae`) the only way `LeafStaticInvGood`
fails (with `GoodClockUpTo`, so the cuts are bounded) is a `FrontSync` failure at some prefix
minute — i.e. `FrontSyncPrefixBad`.  That event carries the proven front-width whp tail. -/

namespace Phase3LeafStaticGoodClock

open MeasureTheory Phase3Assembly.LeafTail Phase3StaticInvCountClosed
open scoped ENNReal NNReal BigOperators

variable {L K : ℕ}

/-- `tr 0 = entry` holds a.e. under the entry-started trace law (`starts_at` is measure 1). -/
theorem starts_at_ae (entry : Config (AgentState L K)) :
    ∀ᵐ tr ∂(ProtocolTraceLaw.μ (L := L) (K := K) entry), tr 0 = entry := by
  classical
  have hmeas : MeasurableSet {tr : Phase3GoodClock.Trace L K | tr 0 = entry} := by
    have hpre : {tr : Phase3GoodClock.Trace L K | tr 0 = entry}
        = (fun tr : Phase3GoodClock.Trace L K => tr 0) ⁻¹' {entry} := rfl
    rw [hpre]; exact (measurable_pi_apply 0) (measurableSet_singleton entry)
  have h1 : ProtocolTraceLaw.μ (L := L) (K := K) entry {tr | tr 0 = entry} = 1 :=
    (ProtocolTraceLaw.traceLawAt (L := L) (K := K) entry 0).starts_at
  rw [ae_iff]
  have hco : {tr : Phase3GoodClock.Trace L K | ¬ tr 0 = entry}
      = {tr | tr 0 = entry}ᶜ := rfl
  rw [hco, measure_compl hmeas (measure_ne_top _ _), h1, measure_univ]
  simp

/-- `¬FrontSyncPrefixBad` (no prefix-minute `FrontSync` failure) gives `FrontSyncPrefix`. -/
theorem frontSyncPrefix_of_not_bad {T : ℕ} {tr : Phase3GoodClock.Trace L K}
    (h : ¬ FrontSyncPrefixBad (L := L) (K := K) T tr) :
    FrontSyncPrefix (L := L) (K := K) T tr := by
  intro τ hτ; by_contra hc; exact h ⟨τ, hτ, hc⟩

/-- **The deterministic finish-horizon hypothesis** for the leaf cuts.  Since `GoodClockUpTo`'s
quantile only gives RELATIVE timing bounds (`start_h`/`end_h` are uncapped
first-passage `Nat.find`; `capMinute` is a state-field cap, not a time-index cap), the absolute
cut horizon is a separate certificate, discharged at the regime level from the existing
`Snapshot617Horizon` (`T_end_l2 ≤ 17·n·(L+1)`). -/
def GoodClockUpToFinishBoundedBy (T : ℕ) (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams) : Prop :=
  ∀ (tr : Phase3GoodClock.Trace L K)
    (U : Phase3GoodClockRegime.GoodClockUpTo (L := L) (K := K) D.M θ tr D.lastCoreHour)
    (h : ℕ) (hh : h ≤ D.lastCoreHour),
    Phase3GoodClockRegime.GoodClockUpTo.finish (L := L) (K := K) U hh ≤ T

/-- The finish-horizon certificate yields `LeafCutsBoundedBy`.  Uses the proven first-passage
proof-irrelevance bridge `goodClock_start_eq_goodClockUpTo_start` and the `47/M` slack. -/
theorem leafCutsBoundedBy_of_finishBounded
    {T : ℕ} {D : Phase3Core.Phase3ModeDomain L} {θ : Phase3GoodClock.ClockTimingParams}
    (hfinish : GoodClockUpToFinishBoundedBy (L := L) (K := K) T D θ) :
    ∀ tr, Phase3GoodClockRegime.GoodClockUpTo (L := L) (K := K) D.M θ tr D.lastCoreHour →
      LeafCutsBoundedBy (L := L) (K := K) T D θ tr := by
  intro tr U G h hh
  have hstart := Phase3Assembly.StrictCutTiming.goodClock_start_eq_goodClockUpTo_start
    (L := L) (K := K) (D := D) (θ := θ) (tr := tr) G U hh
  have hslack : Phase3GoodClockRegime.GoodClockUpTo.start (L := L) (K := K) U hh
        + θ.twoOverC + θ.fortySevenOverM + 1
      ≤ Phase3GoodClockRegime.GoodClockUpTo.finish (L := L) (K := K) U hh := by
    simpa [Phase3GoodClockRegime.GoodClockUpTo.start,
      Phase3GoodClockRegime.GoodClockUpTo.finish] using U.quantile.fortySeven_slack h hh
  have hfin := hfinish tr U h hh
  rw [hstart]; omega

/-- **Static branch ≤ FrontSync-prefix tail.**  On `GoodClockUpTo` (cuts bounded by `T` via
`hcuts`), the a.e. support path forces: `¬LeafStaticInvGood ⟹ FrontSyncPrefixBad`. -/
theorem leafStaticBad_le_frontSyncPrefixBad
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)} {T : ℕ}
    (hentry : StaticInv (L := L) (K := K) D C entry)
    (hcuts : ∀ tr, Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour →
      LeafCutsBoundedBy (L := L) (K := K) T D θ tr) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
          ¬ LeafStaticInvGood (L := L) (K := K) D C θ tr}
      ≤ ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | FrontSyncPrefixBad (L := L) (K := K) T tr} := by
  refine measure_mono_ae ?_
  filter_upwards [ProtocolTraceLaw.supportPathUpTo_ae (L := L) (K := K) entry T,
    starts_at_ae (L := L) (K := K) entry] with tr hsupp hstart0
  rintro ⟨hgood, hbadLeaf⟩
  by_contra hnotBad
  exact hbadLeaf
    (leafStaticInvGood_of_prefix (L := L) (K := K) hentry hstart0 hsupp
      (frontSyncPrefix_of_not_bad (L := L) (K := K) hnotBad) (hcuts tr hgood))

/-- **Static branch ≤ Σ per-minute `FrontSync` tails.**  Composes the prefix-tail bound with
the proven fixed-horizon union bound `frontSyncPrefixBad_le_sum`. -/
theorem leafStaticBad_le_sum
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)} {T : ℕ} (ε : ℕ → ℝ≥0∞)
    (hentry : StaticInv (L := L) (K := K) D C entry)
    (hcuts : ∀ tr, Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour →
      LeafCutsBoundedBy (L := L) (K := K) T D θ tr)
    (hε : ∀ τ, τ < T → ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | ¬ ClockFrontShape.FrontSync (L := L) (K := K) (tr τ)} ≤ ε τ) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
          ¬ LeafStaticInvGood (L := L) (K := K) D C θ tr}
      ≤ ∑ τ ∈ Finset.range T, ε τ :=
  le_trans (leafStaticBad_le_frontSyncPrefixBad (L := L) (K := K) hentry hcuts)
    (frontSyncPrefixBad_le_sum (L := L) (K := K) entry T ε hε)

end Phase3LeafStaticGoodClock
end Ripple.PopulationProtocol.ExactMajority
