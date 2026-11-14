-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingActiveCarrierTails.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingActiveCarrierProduct
noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators
namespace Ripple.PopulationProtocol.ExactMajority.AveragingActiveCarrierTails
open TimeTheorem PairLog PhaseOneDrain P3DeterministicAlgebra StageEventSpec
open AveragingMixedAlgebra AveragingMixedLedgers AveragingLiveProduct
open AveragingCancellationAlgebra AveragingCancellationProbability
open AveragingCancellationLedger AveragingCancellationRecorded
open AveragingCancellationTargets AveragingActiveCarrierProduct
open AveragingRecordedExpectation AveragingRecordedSplice AveragingNumerics
variable {L:ℕ}
def activeTargetGate (r:CancellationRegime) (σ:Sign)
  (level:Fin (L+1)) (M:ℕ) (c:Cfg L 256):Prop :=
 ActiveCancellationGate level M c∧targetGap r σ level M c
def activeTargetLive (r:CancellationRegime) (σ:Sign)
  (level:Fin (L+1)) (M:ℕ) (c:Cfg L 256):Prop :=
 activeTargetGate r σ level M c ∧
  currentTarget r*M < targetQuantity r σ level c
def activeTargetFailure (init:Cfg L 256) (s:ℕ)
  (r:CancellationRegime) (σ:Sign) (level:Fin (L+1)) (M:ℕ) :
  Set (Ω L 256) :=
 {ω | targetStart r σ level M (trace init ω s) ∧
  (∀ u,u≤cancellationTrials init.card M →
   activeTargetGate r σ level M (trace init ω (s+u))) ∧
  currentTarget r*M <
   targetQuantity r σ level (trace init ω (s+cancellationTrials init.card M))}
theorem measurableSet_activeTargetFailure (init:Cfg L 256) (s:ℕ)
  (r:CancellationRegime) (σ:Sign) (level:Fin (L+1)) (M:ℕ) :
  MeasurableSet (activeTargetFailure init s r σ level M):=by
 have hs:=measurableSet_trace_predicate init s (targetStart r σ level M)
 have hg:MeasurableSet {ω:Ω L 256 |
   ∀ u,u≤cancellationTrials init.card M →
    activeTargetGate r σ level M (trace init ω (s+u))}:=by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun u=>MeasurableSet.iInter fun _ =>
   measurableSet_trace_predicate init (s+u) (activeTargetGate r σ level M)
 have hf:=measurableSet_trace_predicate init (s+cancellationTrials init.card M)
  (fun c=>currentTarget r*M < targetQuantity r σ level c)
 exact hs.inter (hg.inter hf)
theorem activeTargetFailure_subset_stop_survival
  (init:Cfg L 256) (hinit:validInitial init) (s:ℕ)
  (r:CancellationRegime) (σ:Sign) (level:Fin (L+1)) (M:ℕ) :
  activeTargetFailure init s r σ level M ⊆
   {ω | (cancellationTrials init.card M:WithTop ℕ) <
    windowStop init s (targetStart r σ level M) (activeTargetLive r σ level M) ω}:=by
 intro ω hω
 apply (windowStop_gt_iff init s _ _ _ ω).2
 refine ⟨hω.1,?_⟩
 intro u hu
 refine ⟨hω.2.1 u hu,?_⟩
 have hgate:∀ v,s≤v→v≤s+cancellationTrials init.card M →
   ActiveCancellationGate level M (trace init ω v):=by
  intro v hsv hv
  exact (gate_at_absolute init ω s (cancellationTrials init.card M) _
   hω.2.1 v hsv hv).1
 have hmono:=targetQuantity_trace_le r σ level init hinit ω
  (s+u) (s+cancellationTrials init.card M) (by omega)
  (fun v huv hv=>(hgate v (by omega) hv).range)
  (fun v huv hv=>(hgate v (by omega) hv).safe)
  (fun v huv hv=>(hgate v (by omega) hv).small_carrier)
 exact lt_of_lt_of_le hω.2.2 hmono
theorem active_target_stop_failure_count
  (init:Cfg L 256) (hinit:validInitial init) (s N:ℕ)
  (r:CancellationRegime) (σ:Sign) (level:Fin (L+1)) (M:ℕ)
  (ω:Ω L 256)
  (hsurvive:(N:WithTop ℕ) <
   windowStop init s (targetStart r σ level M) (activeTargetLive r σ level M) ω) :
  cancellationCountFrom init level s N ω <
   (cancellationParameters r).2.2*(M:ℝ):=by
 obtain ⟨hstart,hlive⟩:=(windowStop_gt_iff init s _ _ N ω).1 hsurvive
 have hgate:∀ v,s≤v→v≤s+N →
   ActiveCancellationGate level M (trace init ω v):=by
  intro v hsv hv
  exact (gate_at_absolute init ω s N _ hlive v hsv hv).1.1
 have hfinal:=(hlive N le_rfl).2
 obtain ⟨_,hrow⟩:=target_row_parameters r
 cases hm:targetKind r
 ·
  simp only [hm] at hrow
  have hs:(2:ℝ)^level.val*(mixedAbsoluteMass (trace init ω s):ℝ) ≤
    2*previousTarget r*(M:ℝ):=by
   simpa only [targetStart,targetQuantity,hm] using hstart
  have hf:currentTarget r*(M:ℝ) <
    (2:ℝ)^level.val*(mixedAbsoluteMass (trace init ω (s+N)):ℝ):=by
   simpa only [targetQuantity,hm] using hfinal
  have hcount:=total_target_failure_count init hinit level ω s N
   (fun v hsv hv=>(hgate v hsv hv).range)
   (fun v hsv hv=>(hgate v hsv hv).safe)
   (fun v hsv hv=>(hgate v hsv hv).small_carrier) hs hf
  simpa only [hrow.2.2.2] using hcount
 ·
  simp only [hm] at hrow
  have hs:(2:ℝ)^level.val*(sideMass (oppositeSign σ) (trace init ω s):ℝ) ≤
    2*previousTarget r*(M:ℝ):=by
   simpa only [targetStart,targetQuantity,hm] using hstart
  have hf:currentTarget r*(M:ℝ) < (2:ℝ)^level.val *
    (sideMass (oppositeSign σ) (trace init ω (s+N)):ℝ):=by
   simpa only [targetQuantity,hm] using hfinal
  have hcount:=minority_target_failure_count σ init hinit level ω s N
   (fun v hsv hv=>(hgate v hsv hv).range)
   (fun v hsv hv=>(hgate v hsv hv).safe)
   (fun v hsv hv=>(hgate v hsv hv).small_carrier) hs hf
  simpa only [hrow.2.2.2] using hcount
theorem recorded_active_target_tail
  (init:Cfg L 256) (hinit:validInitial init) (hc:2≤ init.card)
  (s:ℕ) (p:(i:Finset.Iic s)→Draw L 256)
  (r:CancellationRegime) (σ:Sign) (level:Fin (L+1))
  (hh:1≤level.val) (M:ℕ) (hM:0 < M) (hMn:M≤ init.card) :
  recordedFuture init s p (activeTargetFailure init s r σ level M) ≤
   ENNReal.ofReal (Real.exp (-(M:ℝ) / 1000)):=by
 refine (measure_mono (activeTargetFailure_subset_stop_survival init hinit s r σ level M)).trans ?_
 apply recorded_cancellation_regime_tail init hc level r M hM hMn s p
  (windowStop init s (targetStart r σ level M) (activeTargetLive r σ level M))
  (windowStop_isStoppingTime init s _ _)
 ·
  intro t ω hbefore
  have hlive:=((windowStop_gt_iff init s _ _ t ω).1 hbefore).2 t le_rfl
  have hcfg:labelCfg (labelsAt init ω (s+t))=trace init ω (s+t) :=
   labelsAt_config init ω (s+t)
  apply active_target_live_product r σ level hh M (labelsAt init ω (s+t))
  rw [hcfg]
  exact ⟨hlive.1.1,hlive.1.2,hlive.2⟩
 ·
  intro ω hbefore
  exact active_target_stop_failure_count init hinit s (cancellationTrials init.card M)
   r σ level M ω hbefore
theorem active_cancellation_target_tail_from
  (init:Cfg L 256) (hinit:validInitial init) (hc:2≤ init.card)
  (s:ℕ) (A:Set ((i:Finset.Iic s)→Draw L 256))
  (r:CancellationRegime) (σ:Sign) (level:Fin (L+1))
  (hh:1≤level.val) (M:ℕ) (hM:0 < M) (hMn:M≤ init.card) :
  law init {ω | frestrictLe (π:=fun _:ℕ=>Draw L 256) s ω∈A ∧
    ω∈activeTargetFailure init s r σ level M} ≤
   ENNReal.ofReal (Real.exp (-(M:ℝ) / 1000)) *
    law init {ω | frestrictLe (π:=fun _:ℕ=>Draw L 256) s ω∈A} :=
 law_prefix_joint_bound init s A _ (measurableSet_activeTargetFailure init s r σ level M) _
  (fun p _=>recorded_active_target_tail init hinit hc s p r σ level hh M hM hMn)
end Ripple.PopulationProtocol.ExactMajority.AveragingActiveCarrierTails
end
