-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingObservedHourTails.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingActiveCarrierTails
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingLogPotentialTail
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingTerminalDebtDeadlines
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCanonicalBlocks
noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators
namespace Ripple.PopulationProtocol.ExactMajority.AveragingObservedHourTails
open TimeTheorem PairLog StageEventSpec
open AveragingCancellationAlgebra AveragingCancellationTargets
open AveragingActiveCarrierTails AveragingLogPotentialTail
open AveragingTerminalDebtDeadlines AveragingChangingZeroTail
open AveragingMixedLedgers AveragingDebtService AveragingNumerics
open PhaseOneDrain AveragingRandomOldBlocks AveragingOldBlocks
variable {L n:ℕ}
def hourError (n:ℕ):ℝ≥0∞ :=
 ENNReal.ofReal (1 / (n:ℝ)^20)
theorem old_prefix_tail (n M:ℕ)
  (hn:timePopulationThreshold≤n) (hMpos:0 < M) (hMle:M≤n)
  (init:Cfg L 256) (s h:ℕ) (hh:1≤h)
  (E:Set (Ω L 256)) (hE:MeasurableSet[pairLogFiltration L 256 s] E)
  (Ψ:ℕ) (hΨ:(Ψ:ℝ)≤(1 / 1000:ℝ)*n)
  (σ:Fin (oldCutoff n - 6)→Ω L 256→WithTop ℕ)
  (hσ:∀ j,PairLogPastTime (σ j))
  (τ:Ω L 256→WithTop ℕ) (hτ:PairLogPastTime τ) :
  law init (E∩endpointBlocksFailure init s h
    (ENNReal.ofReal (oldWorkRate n M)) Set.univ Ψ
    (oldWorkTrials n M) σ τ)≤hourError n*law init E:=by
 rw [pairLogFiltration_eq_comap] at hE
 obtain ⟨A,_,hA⟩:=hE
 have hp:{ω | frestrictLe (π:=fun _:ℕ=>Draw L 256) s ω∈A}=E:=hA
 have hsub:E∩endpointBlocksFailure init s h
    (ENNReal.ofReal (oldWorkRate n M)) Set.univ Ψ (oldWorkTrials n M) σ τ ⊆
   endpointBlocksFailure init s h
    (ENNReal.ofReal (oldWorkRate n M)) A Ψ (oldWorkTrials n M) σ τ:=by
  rintro ω ⟨hω,u,ht,hlive,hcomplete,hpositive⟩
  refine ⟨u,ht,?_,hcomplete,hpositive⟩
  refine ⟨?_,hlive.2⟩
  change ω∈{ω | frestrictLe (π:=fun _:ℕ=>Draw L 256) s ω∈A}
  rw [hp]
  exact hω
 have ht:=old_blocks_tail_at_random_endpoint n M hn hMpos hMle
  init s h hh A Ψ hΨ σ hσ τ hτ
 exact (measure_mono hsub).trans (by simpa only [hp,hourError] using ht)
def fuelHourFailure (init:Cfg L 256) (s:ℕ)
  (level:Fin (L+1)) (A:ℚ) (C M:ℕ):Set (Ω L 256) :=
 thresholdFailure init s (changingZeroFuel level.val) A
  (FuelGate level.val A init.card (warmClockCount C))
  M (1 / 500) (clockWarmup init.card C)
def potentialHourFailure (init:Cfg L 256) (s:ℕ)
  (level:Fin (L+1)) (M:ℕ):Set (Ω L 256) :=
 LogSurvival init s init.card M level.val
  (fun _=>LogGate init.card M level.val)
theorem fuel_prefix_tail (init:Cfg L 256) (s:ℕ)
  (E:Set (Ω L 256)) (hE:MeasurableSet[pairLogFiltration L 256 s] E)
  (level:Fin (L+1)) (A:ℚ) (C M:ℕ)
  (hn:timePopulationThreshold≤ init.card) (hC:0 < C)
  (hroles:C+M≤ init.card) (hmain:12*init.card≤25*M) :
  law init (E∩fuelHourFailure init s level A C M) ≤
   hourError init.card*law init E:=by
 rw [pairLogFiltration_eq_comap] at hE
 obtain ⟨B,_,hB⟩:=hE
 have hp:{ω | frestrictLe (π:=fun _:ℕ=>Draw L 256) s ω∈B}=E:=hB
 have hc:2≤ init.card:=by
  have h:=(time_population_bounds hn).2
  omega
 have hk:level.val≤L:=by omega
 have ht:=changingZeroFuel_warmup_tail_from init s B level.val hk A
  init.card C M hc hC hroles
 have hscalar :
   ENNReal.ofReal (Real.exp (-(M:ℝ) / 500))≤hourError init.card:=by
  exact ENNReal.ofReal_le_ofReal
   (faster_mass_tail_le_inverse_power hn hmain
    (by norm_num:(0:ℝ) < 500) (by norm_num:(500:ℝ)≤1000))
 have hw:=ht.trans (mul_le_mul_right' hscalar
  (law init {ω | frestrictLe (π:=fun _:ℕ=>Draw L 256) s ω∈B}))
 change law init
   ({ω | frestrictLe (π:=fun _:ℕ=>Draw L 256) s ω∈B} ∩
    fuelHourFailure init s level A C M) ≤
   hourError init.card *
    law init {ω | frestrictLe (π:=fun _:ℕ=>Draw L 256) s ω∈B} at hw
 simpa only [hp] using hw
theorem potential_prefix_tail (init:Cfg L 256) (s:ℕ)
  (E:Set (Ω L 256)) (hE:MeasurableSet[pairLogFiltration L 256 s] E)
  (level:Fin (L+1)) (hh:1≤level.val) (M:ℕ)
  (hn:timePopulationThreshold≤ init.card)
  (hmain:12*init.card≤25*M) (hMn:M≤ init.card) :
  law init (E∩potentialHourFailure init s level M) ≤
   hourError init.card*law init E:=by
 rw [pairLogFiltration_eq_comap] at hE
 obtain ⟨B,_,hB⟩:=hE
 have hp:{ω | frestrictLe (π:=fun _:ℕ=>Draw L 256) s ω∈B}=E:=hB
 have ht:=actual_logarithmic_survival_from_prefix hn hmain hMn hh init s B
  (fun _=>LogGate init.card M level.val) (fun _ _ hc=>hc)
 change law init
   ({ω | frestrictLe (π:=fun _:ℕ=>Draw L 256) s ω∈B} ∩
    potentialHourFailure init s level M) ≤
   hourError init.card *
    law init {ω | frestrictLe (π:=fun _:ℕ=>Draw L 256) s ω∈B} at ht
 simpa only [hp] using ht
theorem cancellation_prefix_tail (init:Cfg L 256)
  (hinit:validInitial init) (s:ℕ)
  (E:Set (Ω L 256)) (hE:MeasurableSet[pairLogFiltration L 256 s] E)
  (r:CancellationRegime) (σ:Sign)
  (level:Fin (L+1)) (hh:1≤level.val) (M:ℕ)
  (hn:timePopulationThreshold≤ init.card)
  (hmain:12*init.card≤25*M) (hMn:M≤ init.card) :
  law init (E∩activeTargetFailure init s r σ level M) ≤
   hourError init.card*law init E:=by
 rw [pairLogFiltration_eq_comap] at hE
 obtain ⟨B,_,hB⟩:=hE
 have hp:{ω | frestrictLe (π:=fun _:ℕ=>Draw L 256) s ω∈B}=E:=hB
 have hnlarge:=(time_population_bounds hn).2
 have hc:2≤ init.card:=by omega
 have hM:0 < M:=by omega
 have ht:=active_cancellation_target_tail_from
  init hinit hc s B r σ level hh M hM hMn
 have hscalar :
   ENNReal.ofReal (Real.exp (-(M:ℝ) / 1000))≤hourError init.card :=
  ENNReal.ofReal_le_ofReal (mass_tail_le_inverse_power hn hmain)
 have hw:=ht.trans (mul_le_mul_right' hscalar
  (law init {ω | frestrictLe (π:=fun _:ℕ=>Draw L 256) s ω∈B}))
 change law init
   ({ω | frestrictLe (π:=fun _:ℕ=>Draw L 256) s ω∈B} ∩
    activeTargetFailure init s r σ level M) ≤
   hourError init.card *
    law init {ω | frestrictLe (π:=fun _:ℕ=>Draw L 256) s ω∈B} at hw
 simpa only [hp] using hw
def localTotalFailure (init:Cfg L 256) (sF sPhi sCancel C M:ℕ)
  (level:Fin (L+1)) (A:ℚ) (σ:Sign) (r:CancellationRegime) :
  Set (Ω L 256) :=
 fuelHourFailure init sF level A C M ∪
  (potentialHourFailure init sPhi level M ∪
   activeTargetFailure init sCancel r σ level M)
def localSimultaneousFailure (init:Cfg L 256) (sF sPhi sCancel C M:ℕ)
  (level:Fin (L+1)) (A:ℚ) (σ:Sign)
  (rTotal rMinority:CancellationRegime):Set (Ω L 256) :=
 localTotalFailure init sF sPhi sCancel C M level A σ rTotal ∪
  activeTargetFailure init sCancel rMinority σ level M
theorem local_total_prefix_tail (init:Cfg L 256) (hinit:validInitial init)
  (sF sPhi sCancel C M:ℕ) (hFphi:sF≤sPhi) (hFcancel:sF≤sCancel)
  (level:Fin (L+1)) (hh:1≤level.val)
  (A:ℚ) (σ:Sign) (r:CancellationRegime)
  (E:Set (Ω L 256)) (hE:MeasurableSet[pairLogFiltration L 256 sF] E)
  (hn:timePopulationThreshold≤ init.card) (hC:0 < C)
  (hroles:C+M≤ init.card) (hmain:12*init.card≤25*M) :
  law init (E∩localTotalFailure init sF sPhi sCancel C M level A σ r) ≤
   3*hourError init.card*law init E:=by
 have hMn:M≤ init.card:=by omega
 have hPhi:=potential_prefix_tail init sPhi E
  (((pairLogFiltration L 256).mono hFphi) _ hE) level hh M hn hmain hMn
 have hCancel:=cancellation_prefix_tail init hinit sCancel E
  (((pairLogFiltration L 256).mono hFcancel) _ hE) r σ level hh M hn hmain hMn
 have hFuel:=fuel_prefix_tail init sF E hE level A C M hn hC hroles hmain
 have heq:E∩localTotalFailure init sF sPhi sCancel C M level A σ r =
   (E∩fuelHourFailure init sF level A C M) ∪
    ((E∩potentialHourFailure init sPhi level M) ∪
     (E∩activeTargetFailure init sCancel r σ level M)):=by
  ext ω
  simp only [localTotalFailure,Set.mem_inter_iff,Set.mem_union]
  clear * -
  tauto
 rw [heq]
 calc
  _≤hourError init.card*law init E +
     (hourError init.card*law init E+hourError init.card*law init E) :=
   (measure_union_le _ _).trans
    (add_le_add hFuel
     ((measure_union_le _ _).trans (add_le_add hPhi hCancel)))
  _=3*hourError init.card*law init E:=by ring
theorem local_simultaneous_prefix_tail (init:Cfg L 256)
  (hinit:validInitial init) (sF sPhi sCancel C M:ℕ)
  (hFphi:sF≤sPhi) (hFcancel:sF≤sCancel)
  (level:Fin (L+1)) (hh:1≤level.val) (A:ℚ) (σ:Sign)
  (rTotal rMinority:CancellationRegime)
  (E:Set (Ω L 256)) (hE:MeasurableSet[pairLogFiltration L 256 sF] E)
  (hn:timePopulationThreshold≤ init.card) (hC:0 < C)
  (hroles:C+M≤ init.card) (hmain:12*init.card≤25*M) :
  law init (E ∩
    localSimultaneousFailure init sF sPhi sCancel C M level A σ rTotal rMinority) ≤
   4*hourError init.card*law init E:=by
 have ht:=local_total_prefix_tail init hinit sF sPhi sCancel C M
  hFphi hFcancel level hh A σ rTotal E hE hn hC hroles hmain
 have hm:=cancellation_prefix_tail init hinit sCancel E
  (((pairLogFiltration L 256).mono hFcancel) _ hE)
  rMinority σ level hh M hn hmain (by omega)
 have heq:E ∩
    localSimultaneousFailure init sF sPhi sCancel C M level A σ rTotal rMinority =
   (E∩localTotalFailure init sF sPhi sCancel C M level A σ rTotal) ∪
    (E∩activeTargetFailure init sCancel rMinority σ level M):=by
  ext ω
  simp only [localSimultaneousFailure,Set.mem_inter_iff,Set.mem_union]
  clear * -
  tauto
 rw [heq]
 calc
  _≤3*hourError init.card*law init E+hourError init.card*law init E :=
   (measure_union_le _ _).trans (add_le_add ht hm)
  _=4*hourError init.card*law init E:=by ring
theorem observable_partition_bound
  {Ω ι:Type*} [MeasurableSpace Ω] [Countable ι]
  (μ:Measure Ω) (E:Set Ω) (hE:MeasurableSet E)
  (f:Ω→ι) (hf:∀ i,MeasurableSet {ω | f ω=i})
  (B:ι→Set Ω) (ε:ℝ≥0∞)
  (hlocal:∀ i,
   μ ((E∩{ω | f ω=i})∩B i)≤ε*μ (E∩{ω | f ω=i})) :
  μ (E∩{ω | ω∈B (f ω)})≤ε*μ E:=by
 let P:ι→Set Ω:=fun i=>E∩{ω | f ω=i}
 have hP:∀ i,MeasurableSet (P i):=fun i=>hE.inter (hf i)
 have hdisj:Pairwise (fun i j=>Disjoint (P i) (P j)):=by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro ω ⟨_,hi⟩ ⟨_,hj⟩
  exact hij (hi.symm.trans hj)
 have hpartition:(⋃ i,P i)=E:=by
  ext ω
  constructor
  ·
   intro hω
   obtain ⟨i,hi⟩:=Set.mem_iUnion.mp hω
   exact hi.1
  ·
   intro hω
   exact Set.mem_iUnion.mpr ⟨f ω,hω,rfl⟩
 have hcover:E∩{ω | ω∈B (f ω)}⊆⋃ i,P i∩B i:=by
  rintro ω ⟨hω,hb⟩
  exact Set.mem_iUnion.mpr ⟨f ω,⟨hω,rfl⟩,hb⟩
 calc
  μ (E∩{ω | ω∈B (f ω)})≤μ (⋃ i,P i∩B i) :=
   measure_mono hcover
  _≤∑' i,μ (P i∩B i):=measure_iUnion_le _
  _≤∑' i,ε*μ (P i):=ENNReal.tsum_le_tsum hlocal
  _=ε * ∑' i,μ (P i):=by rw [ENNReal.tsum_mul_left]
  _=ε*μ E:=by rw [← measure_iUnion hdisj hP,hpartition]
def seedCounts (init:InputCfg n) (S:ℕ) (ω:InputLog n):ℕ×ℕ :=
 (StageEventSpec.clockCount (trace init ω S),timeMainCount (trace init ω S))
theorem seedCounts_fibre_measurable (init:InputCfg n) (S s:ℕ)
  (hSs:S≤s) (p:ℕ×ℕ) :
  MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 s]
   {ω | seedCounts init S ω=p}:=by
 have hm:MeasurableSet {c:InputCfg n |
   (StageEventSpec.clockCount c,timeMainCount c)=p} :=
  (Set.to_countable _).measurableSet
 exact hm.preimage ((measurable_trace_at init S).mono
  ((pairLogFiltration _ _).mono hSs) le_rfl)
theorem seed_clock_main_le_card (c:InputCfg n) :
  StageEventSpec.clockCount c+timeMainCount c≤c.card:=by
 classical
 induction c using Multiset.induction_on with
 | empty=>simp [StageEventSpec.clockCount,timeMainCount]
 | cons a c ih =>
   dsimp only [StageEventSpec.clockCount,timeMainCount] at ih ⊢
   simp only [Multiset.countP_cons,Multiset.card_cons]
   by_cases hc:a.role=.clock
   ·
    have hm:a.role≠.main:=by simp [hc]
    simp only [if_pos hc,if_neg hm]
    omega
   ·
    by_cases hm:a.role=.main
    ·
     simp only [if_neg hc,if_pos hm]
     omega
    ·
     simp only [if_neg hc,if_neg hm]
     omega
theorem seedCounts_bounds (init:InputCfg n) (S:ℕ) (ω:InputLog n)
  (hn:0 < n) (hp:SeedProfile n init (trace init ω S)) :
  0 < (seedCounts init S ω).1 ∧
   12*n≤25*(seedCounts init S ω).2 ∧
   (seedCounts init S ω).1+(seedCounts init S ω).2≤n:=by
 let c:=trace init ω S
 have hmEq:RoleSplitConcentration.mainCount c=timeMainCount c:=by
  simp only [RoleSplitConcentration.mainCount,timeMainCount,
   AveragingEventInterface.countP_classical]
 have hcEq:RoleSplitConcentration.clockCount c=StageEventSpec.clockCount c:=by
  simp only [RoleSplitConcentration.clockCount,StageEventSpec.clockCount,
   AveragingEventInterface.countP_classical]
 have hm:=hp.role_good.2.1
 have hc:=hp.role_good.2.2.2.1
 change (1 - (1 / 25:ℝ))*(n:ℝ) / 2 ≤
  (RoleSplitConcentration.mainCount c:ℝ) at hm
 change (1 - (1 / 25:ℝ))*(n:ℝ) / 4 ≤
  (RoleSplitConcentration.clockCount c:ℝ) at hc
 rw [hmEq] at hm
 rw [hcEq] at hc
 have hmR:(12:ℝ)*n≤25*(timeMainCount c:ℝ):=by linarith
 have hcR:(6:ℝ)*n≤25*(StageEventSpec.clockCount c:ℝ):=by linarith
 have hmN:12*n≤25*timeMainCount c:=by exact_mod_cast hmR
 have hcN:6*n≤25*StageEventSpec.clockCount c:=by exact_mod_cast hcR
 have hroles:=seed_clock_main_le_card c
 have hcard:c.card=n:=hp.card_eq
 rw [hcard] at hroles
 exact ⟨by change 0 < StageEventSpec.clockCount c; omega,hmN,hroles⟩
theorem seedCounts_prefix_bound (init:InputCfg n) (S s:ℕ) (hSs:S≤s)
  (E:Set (InputLog n))
  (hE:MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 s] E)
  (hn:0 < n) (hseed:∀ ω∈E,SeedProfile n init (trace init ω S))
  (B:(ℕ×ℕ)→Set (InputLog n)) (ε:ℝ≥0∞)
  (hlocal:∀ p:ℕ×ℕ,0 < p.1→12*n≤25*p.2→p.1+p.2≤n →
   law init ((E∩{ω | seedCounts init S ω=p})∩B p) ≤
    ε*law init (E∩{ω | seedCounts init S ω=p})) :
  law init (E∩{ω | ω∈B (seedCounts init S ω)})≤ε*law init E:=by
 apply observable_partition_bound (law init) E
  ((pairLogFiltration _ _).le s _ hE) (seedCounts init S)
  (fun p=>(pairLogFiltration _ _).le s _
   (seedCounts_fibre_measurable init S s hSs p)) B ε
 intro p
 by_cases hex:(E∩{ω | seedCounts init S ω=p}).Nonempty
 ·
  obtain ⟨ω,hωE,hωp⟩:=hex
  have hp:=seedCounts_bounds init S ω hn (hseed ω hωE)
  change seedCounts init S ω=p at hωp
  rw [hωp] at hp
  exact hlocal p hp.1 hp.2.1 hp.2.2
 ·
  have he:E∩{ω | seedCounts init S ω=p}=∅ :=
   Set.not_nonempty_iff_eq_empty.mp hex
  simp only [he,Set.empty_inter,measure_empty,mul_zero]
  exact le_rfl
def observedSimultaneousFailure (init:InputCfg n) (S s:ℕ)
  (level:Fin (PhaseThreeModel.Numeric.hourIndex n+1)) (A:ℕ→ℚ)
  (σ:Sign) (rTotal rMinority:CancellationRegime):Set (InputLog n) :=
 {ω | let p:=seedCounts init S ω
  ω∈localSimultaneousFailure init s
   (s+clockWarmup init.card p.1)
   (s+clockWarmup init.card p.1+potentialTrials init.card p.2)
   p.1 p.2 level (A p.2) σ rTotal rMinority}
theorem observed_simultaneous_prefix_tail (init:InputCfg n)
  (hinit:validInitial init) (hcard:init.card=n)
  (hn:timePopulationThreshold≤n) (S s:ℕ) (hSs:S≤s)
  (level:Fin (PhaseThreeModel.Numeric.hourIndex n+1))
  (hh:1≤level.val) (A:ℕ→ℚ)
  (σ:Sign) (rTotal rMinority:CancellationRegime)
  (E:Set (InputLog n))
  (hE:MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 s] E)
  (hseed:∀ ω∈E,SeedProfile n init (trace init ω S)) :
  law init (E∩observedSimultaneousFailure init S s level A σ rTotal rMinority) ≤
   4*hourError n*law init E:=by
 have hnlarge:=(time_population_bounds hn).2
 apply seedCounts_prefix_bound init S s hSs E hE (by omega) hseed
  (fun p=>localSimultaneousFailure init s
   (s+clockWarmup init.card p.1)
   (s+clockWarmup init.card p.1+potentialTrials init.card p.2)
   p.1 p.2 level (A p.2) σ rTotal rMinority) (4*hourError n)
 intro p hC hmain hroles
 have hEf :
   MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 s]
    (E∩{ω | seedCounts init S ω=p}) :=
  hE.inter (seedCounts_fibre_measurable init S s hSs p)
 have ht:=local_simultaneous_prefix_tail init hinit s
  (s+clockWarmup init.card p.1)
  (s+clockWarmup init.card p.1+potentialTrials init.card p.2)
  p.1 p.2 (by omega) (by omega) level hh (A p.2) σ rTotal rMinority
  (E∩{ω | seedCounts init S ω=p}) hEf
  (by simpa only [hcard] using hn) hC
  (by simpa only [hcard] using hroles)
  (by simpa only [hcard] using hmain)
 simpa only [hcard] using ht
def observedOldFailure (init:InputCfg n) (S s r:ℕ)
  (σ:Fin (oldCutoff n - 6)→InputLog n→WithTop ℕ)
  (finish:InputLog n→WithTop ℕ):Set (InputLog n) :=
 {ω | let M:=(seedCounts init S ω).2
  ω∈endpointBlocksFailure init s r (ENNReal.ofReal (oldWorkRate n M))
   Set.univ (M / 1000) (oldWorkTrials n M) σ finish}
theorem observed_old_prefix_tail (init:InputCfg n)
  (hn:timePopulationThreshold≤n) (S s:ℕ) (hSs:S≤s)
  (r:ℕ) (hr:1≤r)
  (σ:Fin (oldCutoff n - 6)→InputLog n→WithTop ℕ)
  (hσ:∀ j,PairLogPastTime (σ j))
  (finish:InputLog n→WithTop ℕ) (hfinish:PairLogPastTime finish)
  (E:Set (InputLog n))
  (hE:MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 s] E)
  (hseed:∀ ω∈E,SeedProfile n init (trace init ω S)) :
  law init (E∩observedOldFailure init S s r σ finish) ≤
   hourError n*law init E:=by
 have hnlarge:=(time_population_bounds hn).2
 apply seedCounts_prefix_bound init S s hSs E hE (by omega) hseed
  (fun p=>endpointBlocksFailure init s r (ENNReal.ofReal (oldWorkRate n p.2))
   Set.univ (p.2 / 1000) (oldWorkTrials n p.2) σ finish) (hourError n)
 intro p _ hmain hroles
 have hM:0 < p.2:=by omega
 have hMn:p.2≤n:=by omega
 have hcapN:1000*(p.2 / 1000)≤n:=by omega
 have hcapR:(1000:ℝ)*((p.2 / 1000:ℕ):ℝ)≤(n:ℝ):=by
  exact_mod_cast hcapN
 exact old_prefix_tail n p.2 hn hM hMn init s r hr
  (E∩{ω | seedCounts init S ω=p})
  (hE.inter (seedCounts_fibre_measurable init S s hSs p))
  (p.2 / 1000) (by linarith) σ hσ finish hfinish
end Ripple.PopulationProtocol.ExactMajority.AveragingObservedHourTails
end
