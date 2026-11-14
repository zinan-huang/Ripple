-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingHourFailureCover.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingHourGateAssembly
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingObservedHourTails
noncomputable section
namespace Ripple.PopulationProtocol.ExactMajority.AveragingHourFailureCover

open PhaseThreeClockProducer
open TimeTheorem PairLog StageEventSpec P3DeterministicAlgebra
open AveragingSparseEntry AveragingMixedAlgebra AveragingMixedLedgers AveragingLiveProduct
open AveragingIntegerPotential AveragingPotentialService AveragingChangingZeroTail
open AveragingHourInvariant AveragingHourSchedule AveragingOldHourGate AveragingHourGateAssembly
open AveragingCancellationAlgebra AveragingCancellationProbability
open AveragingCancellationTargets AveragingActiveCarrierProduct
open AveragingActiveCarrierTails AveragingNumerics AveragingTerminalDebtDeadlines
open AveragingSeededDelay AveragingOldBlocks AveragingCanonicalBlocks AveragingRandomOldBlocks
open AveragingLogPotentialTail AveragingCompensatedLog AveragingStoppedDebt AveragingObservedHourTails
variable {n:ℕ}
def CurrentHourChecks (σ:Sign) (init:InputCfg n) (ω:InputLog n)
  (S:ℕ) (w:ClockTimes init) (ell h:ℕ):Prop :=
 let C:=clockCount (trace init ω S)
 let M:=timeMainCount (trace init ω S)
 let W:=warmCheckpoint w C h
 let P:=potentialCheckpoint w C M h
 let E:=workCheckpoint w C M h
 changingZeroFuel h (trace init ω W)≤(2*totalPrevious ell h+1 / 500)*M ∧
  (h≤oldCutoff n∨augmentedPhiNat (h - oldCutoff n) (trace init ω W)=0) ∧
  (1000:ℚ)*augmentedPhi h (trace init ω P)≤M ∧
  (2:ℚ)^h*mixedAbsoluteMass (trace init ω E)≤totalTarget ell h*M ∧
  (ell≤h+4→(2:ℚ)^h*sideMass (oppositeSign σ) (trace init ω E) ≤
   minorityTarget ell h*M)
theorem current_failure_cover (σ:Sign) {init:InputCfg n}
  (hvalid:validInitial init) {ω:InputLog n} {S T ρ ell h:ℕ}
  {w:ClockTimes init} (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w) (hn:timePopulationThreshold≤n)
  (hell:5≤ell) (hh:1≤h) (hle:h≤ell)
  (hL:h≤PhaseThreeModel.Numeric.hourIndex n)
  (seed:InputLog n→WithTop ℕ) (hseedTime:seed ω=(S:WithTop ℕ))
  (hupper:5*2^ell*gapMagnitude init < 4*timeMainCount (trace init ω S))
  (hwinning:ell≤h+4→winningSign init σ)
  (hlower:ell≤h+4→2*timeMainCount (trace init ω S) ≤
   5*2^ell*gapMagnitude init)
  (past:PrecedingHours init ω S w ell h)
  (pastMinority:PrecedingMinority σ init ω S w ell h)
  (hbad:¬ CurrentHourChecks σ init ω S w ell h) :
  let C:=clockCount (trace init ω S)
  let M:=timeMainCount (trace init ω S);
  (oldCutoff n < h ∧
   ω∈randomBlocksFailure init (hourPotentialEnd init seed (h - oldCutoff n))
    (hourWarmStart init seed h) (h - oldCutoff n)
    (ENNReal.ofReal (oldWorkRate n M)) (M / 1000)
    (oldWorkTrials n M) (oldBlockStarts init seed (h - oldCutoff n) (oldCutoff n))) ∨
   ω∈localSimultaneousFailure init (w.start h) (warmCheckpoint w C h)
    (potentialCheckpoint w C M h) C M ⟨h,by omega⟩
    (2*totalPrevious ell h*M) σ (totalRegime ell h) (minorityRegime ell h):=by
 classical
 let C:=clockCount (trace init ω S)
 let M:=timeMainCount (trace init ω S)
 let a:=w.start h
 let W:=warmCheckpoint w C h
 let P:=potentialCheckpoint w C M h
 let E:=workCheckpoint w C M h
 let c:=fun v=>trace init ω v
 let level:Fin (PhaseThreeModel.Numeric.hourIndex n+1):=⟨h,by omega⟩
 let r:=totalPrevious ell h
 let A:=2*r*(M:ℚ)
 have hnpos:0 < n:=by exact_mod_cast (population_log_lower hn).1
 have hcard:init.card=n:=by
  simpa only [TimeTheorem.trace_zero] using population_of_clockHistory H 0
 have horder:=checkpoint_order H hnpos h hh hL
 have hfit:=clockHistory_raw_work_fits H hnpos h hL
 have hWP:W+potentialTrials n M=P:=rfl
 have hPE:P+cancellationTrials n M=E:=by
  simp [P,E,W,potentialCheckpoint,warmCheckpoint,workCheckpoint,
   rawWork,clockWarmup,potentialTrials,cancellationTrials,Nat.add_assoc]
 have haW:a≤W:=by dsimp only [a,W,warmCheckpoint]; omega
 have hWPle:W≤P:=by omega
 have hPEle:P≤E:=by omega
 have htime (v:ℕ) (hav:a≤v) (hvE:v≤E) :
   S≤v∧v≤w.finish h∧v < ρ:=by
  dsimp only [a,E,workCheckpoint,M,C] at hav hvE
  omega
 have hWtime:=htime W haW (hWPle.trans hPEle)
 have hPtime:=htime P (haW.trans hWPle) hPEle
 have hEtime:=htime E (haW.trans (hWPle.trans hPEle)) le_rfl
 have hfg (v:ℕ) (hav:a≤v) (hvE:v≤E) :
   FuelGate h A n (warmClockCount C) (c v) :=
  fuelGate_of_precedingHours hvalid hseed H hnpos hell hh hL hav
   (htime v hav hvE).2.1 (htime v hav hvE).2.2 past
 change ¬ (changingZeroFuel h (c W)≤(2*r+1 / 500)*M ∧
  (h≤oldCutoff n∨augmentedPhiNat (h - oldCutoff n) (c W)=0) ∧
  (1000:ℚ)*augmentedPhi h (c P)≤M ∧
  (2:ℚ)^h*mixedAbsoluteMass (c E)≤totalTarget ell h*M ∧
  (ell≤h+4→(2:ℚ)^h*sideMass (oppositeSign σ) (c E) ≤
   minorityTarget ell h*M)) at hbad
 by_cases hf:changingZeroFuel h (c W)≤(2*r+1 / 500)*M
 ·
  by_cases ho:h≤oldCutoff n∨augmentedPhiNat (h - oldCutoff n) (c W)=0
  ·
   by_cases hp:(1000:ℚ)*augmentedPhi h (c P)≤M
   ·
    have hgate (v:ℕ) (hPv:P≤v) (hvE:v≤E) :
      ActiveCancellationGate level M (c v) :=
     activeCancellationGate_of_checkpoint hvalid hseed H level hh hPtime.1 hPv
      (htime v (haW.trans (hWPle.trans hPv)) hvE).2.2
      (htime v (haW.trans (hWPle.trans hPv)) hvE).2.1 hp
    by_cases ht:(2:ℚ)^h*mixedAbsoluteMass (c E)≤totalTarget ell h*M
    ·
     by_cases hlast:ell≤h+4
     ·
      have hm:minorityTarget ell h*(M:ℚ) <
        (2:ℚ)^h*sideMass (oppositeSign σ) (c E):=by
       apply lt_of_not_ge
       intro hm
       exact hbad ⟨hf,ho,hp,ht,fun _=>hm⟩
      have hmem:ω∈activeTargetFailure init P (minorityRegime ell h) σ level M:=by
       simp only [activeTargetFailure,Set.mem_setOf_eq,hcard]
       refine ⟨?_,?_,?_⟩
       · exact minority_start_of_precedingHours σ hvalid hseed H hnpos hell hh hle
           hlast hL (haW.trans hWPle) hPtime.2.2 (hwinning hlast)
           (hlower hlast) past pastMinority
       ·
        intro u hu
        have huE:P+u≤E:=by omega
        have ht:=htime (P+u) (by omega) huE
        exact ⟨hgate _ (by omega) huE,
         minority_targetGap_of_clockHistory σ hvalid H ht.1 ht.2.2
          (hwinning hlast) hle hlast hL (hlower hlast)⟩
       ·
        rw [hPE]
        have hmR:(minorityTarget ell h:ℝ)*M <
          (2:ℝ)^h*(sideMass (oppositeSign σ) (c E):ℝ):=by
         exact_mod_cast hm
        simpa only [targetQuantity,minorityRegime_kind,
 ←minorityTarget_cast ell h hle hlast] using hmR
      exact Or.inr (Or.inr hmem)
     · exact False.elim (hbad ⟨hf,ho,hp,ht,fun hl=>(hlast hl).elim⟩)
    ·
     have hmem:ω∈activeTargetFailure init P (totalRegime ell h) σ level M:=by
      simp only [activeTargetFailure,Set.mem_setOf_eq,hcard]
      refine ⟨?_,?_,?_⟩
      ·
       have hs:=total_start_of_precedingHours hvalid hseed H hnpos hell hh hle
        hL (haW.trans hWPle) hPtime.2.2 past
       simpa only [targetStart,targetQuantity,totalRegime_kind] using hs
      ·
       intro u hu
       have huE:P+u≤E:=by omega
       have ht:=htime (P+u) (by omega) huE
       exact ⟨hgate _ (by omega) huE,
        total_targetGap_of_clockHistory σ hvalid H ht.1 ht.2.2 hle hL hupper⟩
      ·
       rw [hPE]
       have htR:(totalTarget ell h:ℝ)*M <
         (2:ℝ)^h*(mixedAbsoluteMass (c E):ℝ):=by
        exact_mod_cast (lt_of_not_ge ht)
       simpa only [targetQuantity,totalRegime_kind,←totalTarget_cast ell h] using htR
     exact Or.inr (Or.inl (Or.inr (Or.inr hmem)))
   ·
    have hfinal:potentialTarget M < (augmentedPhiNat h (c P):ℝ):=by
     have hq:(M:ℚ) < 1000*(augmentedPhiNat h (c P):ℚ):=by
      rw [augmentedPhiNat_cast]
      exact lt_of_not_ge hp
     have hr:(M:ℝ) < 1000*(augmentedPhiNat h (c P):ℝ):=by exact_mod_cast hq
     unfold potentialTarget
     linarith only [hr]
    have hmem:ω∈potentialHourFailure init W level M:=by
     simp only [potentialHourFailure,LogSurvival,Set.mem_setOf_eq,hcard]
     refine ⟨?_,?_⟩
     ·
      intro u hu
      have hvP:W+u≤P:=by omega
      have hvE:W+u≤E:=hvP.trans hPEle
      have ht:=htime (W+u) (by omega) hvE
      refine ⟨logGate_after_warm hvalid hseed H hn h hh hL hWtime.1
       (by omega) ht.2.2 ht.2.1 r (totalPrevious_le hh hle) hf ho,?_⟩
      have hmono:=potential_trace_le_of_domain h hh init ω (W+u) P hvP
       (fun v huv hvP=>potentialDomain_of_safeSparseSeed_clockHistory
        hvalid hseed H (by omega) (lt_of_le_of_lt hvP hPtime.2.2))
      exact hfinal.trans_le (by exact_mod_cast hmono)
     · exact potential_start_of_precedingHours hvalid hseed H hnpos hell hh hle hL
         haW hWtime.2.2 past
    exact Or.inr (Or.inl (Or.inr (Or.inl hmem)))
  ·
   have hlate:oldCutoff n < h:=by
    by_contra h
    exact ho (Or.inl (by omega))
   have hpositive:1≤augmentedPhiNat (h - oldCutoff n) (c W):=by
    by_contra hz
    exact ho (Or.inr (by omega))
   exact Or.inl ⟨hlate,old_failure_of_precedingHours hvalid hseed H hn hle hL
    seed hseedTime hlate past hpositive⟩
 ·
  have hmem:ω∈fuelHourFailure init a level A C M:=by
   simp only [fuelHourFailure,thresholdFailure,Set.mem_setOf_eq,hcard]
   refine ⟨⟨?_,?_⟩,?_⟩
   ·
    have ha:=htime a le_rfl (by omega)
    have hceil:=fuel_initial_ceiling_le_mainCount h A n (warmClockCount C) (c a)
     (hfg a le_rfl (by omega))
    exact hceil.trans_eq (mainCount_eq_seed H ha.1 ha.2.2)
   ·
    intro u hu
    apply hfg
    · omega
    ·
     have huW:a+u≤W:=by
      dsimp only [a,W,warmCheckpoint]
      omega
     exact huW.trans (hWPle.trans hPEle)
   ·
    have hlarge:=lt_of_not_ge hf
    change A+(1 / 500:ℚ)*M < changingZeroFuel h (c W)
    dsimp only [A]
    linarith only [hlarge]
  exact Or.inr (Or.inl (Or.inl hmem))
end Ripple.PopulationProtocol.ExactMajority.AveragingHourFailureCover
end
