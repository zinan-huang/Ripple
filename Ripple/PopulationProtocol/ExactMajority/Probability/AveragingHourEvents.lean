-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingHourEvents.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingHourPrefix
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingHourGateAssembly
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Ripple.PopulationProtocol.ExactMajority.AveragingHourEvents
open TimeTheorem PairLog PhaseOneDrain StageEventSpec AveragingSparseEntry
open AveragingMixedAlgebra AveragingMixedLedgers AveragingIntegerPotential AveragingLiveProduct
open P3DeterministicAlgebra
open AveragingHourStops AveragingSeededDelay AveragingHourPrefix
open AveragingHourSchedule AveragingHourGateAssembly AveragingClockBlocks
open AveragingCancellationAlgebra AveragingTerminalDebtDeadlines AveragingNumerics
variable {n:ℕ}
def hourWorkEnd (init:InputCfg n) (seed:InputLog n→WithTop ℕ)
  (h:ℕ):InputLog n→WithTop ℕ :=
 seededDelay init seed (hourStart init seed h)
  (fun c=>rawWork n (timeMainCount c) (clockCount c))
theorem hourWorkEnd_past (init:InputCfg n) (seed:InputLog n→WithTop ℕ)
  (hs:PairLogPastTime seed) (h:ℕ):PairLogPastTime (hourWorkEnd init seed h) :=
 seededDelay_pastTime init seed (hourStart init seed h) hs
  (hourStart_pastTime init seed hs h) _
theorem hourWorkEnd_clock {init:InputCfg n} {ω:InputLog n}
  {S T ρ:ℕ} {w:ClockTimes init} (H:ClockHistory init ω S T ρ w)
  (seed:InputLog n→WithTop ℕ) (hs:seed ω=(S:WithTop ℕ))
  (h:ℕ) (hh:h≤PhaseThreeModel.Numeric.hourIndex n) :
  hourWorkEnd init seed h ω =
   (workCheckpoint w (clockCount (trace init ω S))
    (timeMainCount (trace init ω S)) h:WithTop ℕ):=by
 have ht:=hourStart_clockHistory H seed h hs hh
 have hSh:=((hourStart_eq_iff_of_seed init seed h ω S (w.start h) hs).mp ht).1
 exact seededDelay_eq_of_eq init seed (hourStart init seed h) _ ω S
  (w.start h) hs ht hSh
def checkTime (init:InputCfg n) (seed:InputLog n→WithTop ℕ)
  (h:ℕ) (i:Fin 5):InputLog n→WithTop ℕ :=
 if i.val < 2 then hourWarmStart init seed h
 else if i.val=2 then hourPotentialEnd init seed h
 else hourWorkEnd init seed h
def checkTest (ell:ℕ) (σ:Sign) (h:ℕ) (i:Fin 5)
  (seedCfg c:InputCfg n):Prop :=
 if i.val=0 then
  changingZeroFuel h c≤(2*totalPrevious ell h+1 / 500)*timeMainCount seedCfg
 else if i.val=1 then h≤oldCutoff n∨augmentedPhiNat (h - oldCutoff n) c=0
 else if i.val=2 then (1000:ℚ)*augmentedPhi h c≤timeMainCount seedCfg
 else if i.val=3 then
  (2:ℚ)^h*mixedAbsoluteMass c≤totalTarget ell h*timeMainCount seedCfg
 else ell≤h+4→h≤ell →
  (2:ℚ)^h*sideMass (oppositeSign σ) c≤minorityTarget ell h*timeMainCount seedCfg
def hourSuccess (init:InputCfg n) (seed:InputLog n→WithTop ℕ)
  (ell:ℕ) (σ:Sign):ℕ→InputLog n→Prop :=
 checkpointHourSuccess init seed (checkTime init seed) (checkTest ell σ)
def earlierSuccessBy (init:InputCfg n) (seed:InputLog n→WithTop ℕ)
  (ell:ℕ) (σ:Sign) (k t:ℕ):Set (InputLog n) :=
 previousHoursBy init seed (checkTime init seed) (checkTest ell σ) k t
theorem checkTime_past (init:InputCfg n) (seed:InputLog n→WithTop ℕ)
  (hs:PairLogPastTime seed) (h:ℕ) (i:Fin 5) :
  PairLogPastTime (checkTime init seed h i):=by
 unfold checkTime
 split_ifs
 · exact hourWarmStart_pastTime init seed hs h
 · exact hourPotentialEnd_pastTime init seed hs h
 · exact hourWorkEnd_past init seed hs h
theorem earlierSuccessBy_past (init:InputCfg n)
  (seed:InputLog n→WithTop ℕ) (hs:PairLogPastTime seed)
  (ell:ℕ) (σ:Sign) (k t:ℕ) :
  MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
   (earlierSuccessBy init seed ell σ k t) :=
 previousHoursBy_measurable init seed hs _ (checkTime_past init seed hs) _ k t
theorem observed_value {L K:ℕ} (init:Cfg L K)
  (seed checkpoint:Ω L K→WithTop ℕ) (P:Cfg L K→Cfg L K→Prop)
  (ω:Ω L K) (S u:ℕ) (hs:seed ω=(S:WithTop ℕ))
  (hu:checkpoint ω=(u:WithTop ℕ))
  (h:ω∈observedCheckpoint init seed checkpoint P) :
  P (trace init ω S) (trace init ω u):=by
 obtain ⟨A,b,_,ha,hb,hp⟩:=h
 have hA:A=S:=WithTop.coe_injective (ha.symm.trans hs)
 have hB:b=u:=WithTop.coe_injective (hb.symm.trans hu)
 simpa only [hA,hB] using hp
theorem preceding_of_success {init:InputCfg n} {ω:InputLog n}
  {S T ρ ell h:ℕ} {w:ClockTimes init} (H:ClockHistory init ω S T ρ w)
  (seed:InputLog n→WithTop ℕ) (hs:seed ω=(S:WithTop ℕ))
  (hL:h≤PhaseThreeModel.Numeric.hourIndex n) (hle:h≤ell) (σ:Sign)
  (past:∀ j,1≤j→j < h→hourSuccess init seed ell σ j ω) :
  PrecedingHours init ω S w ell h∧PrecedingMinority σ init ω S w ell h:=by
 have eval (j:ℕ) (hj:1≤j) (hjh:j < h) (i:Fin 5) (u:ℕ)
   (hu:checkTime init seed j i ω=(u:WithTop ℕ)) :
   checkTest ell σ j i (trace init ω S) (trace init ω u) :=
  observed_value init seed _ _ ω S u hs hu (past j hj hjh i)
 refine ⟨⟨?_,?_,?_⟩,?_⟩
 ·
  intro j hj hjh
  have hv:=hourWarmStart_clockHistory H seed j hs (by omega)
  simpa [checkTest] using eval j hj hjh ⟨0,by decide⟩ _ (by simpa [checkTime] using hv)
 ·
  intro j hj hjh
  have hv:=hourPotentialEnd_clockHistory H seed j hs (by omega)
  simpa [checkTest,potentialCheckpoint,warmCheckpoint] using
   eval j hj hjh ⟨2,by decide⟩ _ (by simpa [checkTime] using hv)
 ·
  intro j hj hjh
  have hv:=hourWorkEnd_clock H seed hs j (by omega)
  simpa [checkTest] using eval j hj hjh ⟨3,by decide⟩ _ (by simpa [checkTime] using hv)
 ·
  intro j hj hjh hjlast
  have hv:=hourWorkEnd_clock H seed hs j (by omega)
  have hm:=eval j hj hjh ⟨4,by decide⟩ _ (by simpa [checkTime] using hv)
  simp only [checkTest] at hm
  norm_num at hm
  exact hm hjlast (by omega)
theorem checkpoints_before_next {init:InputCfg n} {ω:InputLog n}
  {S T ρ:ℕ} {w:ClockTimes init} (H:ClockHistory init ω S T ρ w)
  (hn:0 < n) (seed:InputLog n→WithTop ℕ)
  (hs:seed ω=(S:WithTop ℕ)) (k:ℕ)
  (hL:k+1≤PhaseThreeModel.Numeric.hourIndex n) :
  ∀ j,j < k→∀ i,∃ u:ℕ,
   checkTime init seed (j+1) i ω=(u:WithTop ℕ)∧u≤w.start (k+1):=by
 intro j hj i
 have hjL:j+1≤PhaseThreeModel.Numeric.hourIndex n:=by omega
 have hf:=clockHistory_raw_work_fits H hn (j+1) hjL
 have hnxt:=H.previous_end (j+2) (by omega) (by omega)
 have hm:=clockHistory_start_mono H hn (j+2) (k+1) (by omega) hL
 have hwork:workCheckpoint w (clockCount (trace init ω S))
   (timeMainCount (trace init ω S)) (j+1)≤w.start (k+1):=by
  dsimp only [workCheckpoint]
  have he:j+2 - 1=j+1:=by omega
  rw [he] at hnxt
  omega
 have hwarm:warmCheckpoint w (clockCount (trace init ω S)) (j+1) ≤
   workCheckpoint w (clockCount (trace init ω S))
    (timeMainCount (trace init ω S)) (j+1):=by
  unfold warmCheckpoint workCheckpoint rawWork clockWarmup
  omega
 have hphi:potentialCheckpoint w (clockCount (trace init ω S))
   (timeMainCount (trace init ω S)) (j+1) ≤
   workCheckpoint w (clockCount (trace init ω S))
    (timeMainCount (trace init ω S)) (j+1):=by
  unfold potentialCheckpoint warmCheckpoint workCheckpoint rawWork clockWarmup potentialTrials
  omega
 unfold checkTime
 split_ifs
 · exact ⟨_,hourWarmStart_clockHistory H seed (j+1) hs hjL,hwarm.trans hwork⟩
 · exact ⟨_,hourPotentialEnd_clockHistory H seed (j+1) hs hjL,hphi.trans hwork⟩
 · exact ⟨_,hourWorkEnd_clock H seed hs (j+1) hjL,hwork⟩
theorem earlierSuccessBy_iff {init:InputCfg n} {ω:InputLog n}
  {S T ρ ell:ℕ} {w:ClockTimes init} (H:ClockHistory init ω S T ρ w)
  (hn:0 < n) (seed:InputLog n→WithTop ℕ)
  (hs:seed ω=(S:WithTop ℕ)) (σ:Sign) (k:ℕ)
  (hL:k+1≤PhaseThreeModel.Numeric.hourIndex n) :
  ω∈earlierSuccessBy init seed ell σ k (w.start (k+1)) ↔
   ∀ j,j < k→hourSuccess init seed ell σ (j+1) ω :=
 previousHoursBy_iff_of_completed init seed _ _ ω k _
  (checkpoints_before_next H hn seed hs k hL)
end Ripple.PopulationProtocol.ExactMajority.AveragingHourEvents
end
