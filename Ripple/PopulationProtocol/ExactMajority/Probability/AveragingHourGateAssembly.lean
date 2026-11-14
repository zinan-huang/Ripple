-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingHourGateAssembly.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingOldHourGate
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingHourSchedule
noncomputable section
namespace Ripple.PopulationProtocol.ExactMajority.AveragingHourGateAssembly

open PhaseThreeClockProducer
open TimeTheorem PairLog StageEventSpec P3DeterministicAlgebra
open AveragingSparseEntry AveragingMixedAlgebra AveragingMixedLedgers AveragingLiveProduct
open AveragingIntegerPotential AveragingPotentialService AveragingDebtService
open AveragingChangingZeroTail
open AveragingHourInvariant AveragingHourSchedule AveragingOldHourGate
open AveragingCancellationAlgebra AveragingCancellationTargets
open AveragingNumerics AveragingTerminalDebtDeadlines AveragingSeededDelay
open AveragingOldBlocks AveragingCanonicalBlocks AveragingRandomOldBlocks
variable {n:ℕ}
def warmCheckpoint {init:InputCfg n} (w:ClockTimes init) (C h:ℕ):ℕ :=
 w.start h+clockWarmup n C
def potentialCheckpoint {init:InputCfg n} (w:ClockTimes init)
  (C M h:ℕ):ℕ :=
 warmCheckpoint w C h+potentialTrials n M
def workCheckpoint {init:InputCfg n} (w:ClockTimes init) (C M h:ℕ):ℕ :=
 w.start h+rawWork n M C
structure PrecedingHours (init:InputCfg n) (ω:InputLog n) (S:ℕ)
  (w:ClockTimes init) (ell h:ℕ):Prop where
 warm:∀ j,1≤j→j < h →
  changingZeroFuel j (trace init ω
   (warmCheckpoint w (clockCount (trace init ω S)) j)) ≤
    (2*totalPrevious ell j+1 / 500)*timeMainCount (trace init ω S)
 potential:∀ j,1≤j→j < h →
  (1000:ℚ)*augmentedPhi j (trace init ω
   (potentialCheckpoint w (clockCount (trace init ω S))
    (timeMainCount (trace init ω S)) j))≤timeMainCount (trace init ω S)
 total:∀ j,1≤j→j < h →
  (2:ℚ)^j*mixedAbsoluteMass (trace init ω
   (workCheckpoint w (clockCount (trace init ω S))
    (timeMainCount (trace init ω S)) j)) ≤
     totalTarget ell j*timeMainCount (trace init ω S)
theorem work_before_next {init:InputCfg n} {ω:InputLog n}
  {S T ρ h:ℕ} {w:ClockTimes init} (H:ClockHistory init ω S T ρ w)
  (hn:0 < n) (hh:1≤h) (hL:h≤PhaseThreeModel.Numeric.hourIndex n) :
  workCheckpoint w (clockCount (trace init ω S))
   (timeMainCount (trace init ω S)) (h - 1) < w.start h:=by
 have hfit:=clockHistory_raw_work_fits H hn (h - 1) (by omega)
 have hnext:=H.previous_end h hh hL
 exact hfit.trans hnext
theorem preceding_total_at_current {init:InputCfg n}
  (hvalid:validInitial init) {ω:InputLog n} {S T ρ v ell h:ℕ}
  {w:ClockTimes init} (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w) (hn:0 < n)
  (hell:5≤ell) (hh:1≤h) (hL:h≤PhaseThreeModel.Numeric.hourIndex n)
  (hstart:w.start h≤v) (hvρ:v < ρ)
  (past:PrecedingHours init ω S w ell h) :
  (2:ℚ)^(h - 1)*mixedAbsoluteMass (trace init ω v) ≤
   totalPrevious ell h*timeMainCount (trace init ω S):=by
 have hSv:=((H.start_positive h hh hL).1).trans hstart
 by_cases hone:h=1
 ·
  subst h
  have hm:=sparse_mass_of_safeSparseSeed_clockHistory hvalid hseed H hSv hvρ
  rw [totalPrevious_early (ell:=ell) (h:=1) (by omega) (by omega)]
  norm_num
  have hM:(0:ℚ)≤timeMainCount (trace init ω S):=by positivity
  linarith only [hm,hM]
 ·
  let u:=workCheckpoint w (clockCount (trace init ω S))
   (timeMainCount (trace init ω S)) (h - 1)
  have hSu:S≤u:=by
   have hs:=(H.start_positive (h - 1) (by omega) (by omega)).1
   dsimp only [u,workCheckpoint]
   omega
  have huv:u≤v:=(work_before_next H hn hh hL).le.trans hstart
  have hmono:=mixedAbsoluteMass_le_of_clockHistory hvalid hseed H hSu huv hvρ
  exact (mul_le_mul_of_nonneg_left hmono
   (show (0:ℚ)≤2^(h - 1) by positivity)).trans
    (past.total (h - 1) (by omega) (by omega))
theorem fuelGate_of_precedingHours {init:InputCfg n}
  (hvalid:validInitial init) {ω:InputLog n} {S T ρ v ell h:ℕ}
  {w:ClockTimes init} (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w) (hn:0 < n)
  (hell:5≤ell) (hh:1≤h) (hL:h≤PhaseThreeModel.Numeric.hourIndex n)
  (hstart:w.start h≤v) (hfinish:v≤w.finish h) (hvρ:v < ρ)
  (past:PrecedingHours init ω S w ell h) :
  FuelGate h (2*totalPrevious ell h*timeMainCount (trace init ω S))
   n (warmClockCount (clockCount (trace init ω S))) (trace init ω v):=by
 have hprev:=preceding_total_at_current hvalid hseed H hn hell hh hL hstart hvρ past
 have he:h=(h - 1)+1:=by omega
 have hmass:(2:ℚ)^h*mixedAbsoluteMass (trace init ω v) ≤
   2*totalPrevious ell h*timeMainCount (trace init ω S):=by
  conv_lhs=>rw [he,pow_succ]
  nlinarith only [hprev]
 exact fuelGate_of_previous_mass hvalid hseed H
  (((H.start_positive h hh hL).1).trans hstart) le_rfl hvρ hL hstart hfinish _ hmass
theorem potential_start_of_precedingHours {init:InputCfg n}
  (hvalid:validInitial init) {ω:InputLog n} {S T ρ v ell h:ℕ}
  {w:ClockTimes init} (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w) (hn:0 < n)
  (hell:5≤ell) (hh:1≤h) (hle:h≤ell)
  (hL:h≤PhaseThreeModel.Numeric.hourIndex n)
  (hstart:w.start h≤v) (hvρ:v < ρ)
  (past:PrecedingHours init ω S w ell h) :
  (augmentedPhiNat h (trace init ω v):ℝ) ≤
   (103 / 250:ℝ)*timeMainCount (trace init ω S):=by
 apply integer_potential_cap_of_rational
 have hSv:=((H.start_positive h hh hL).1).trans hstart
 by_cases hone:h=1
 ·
  subst h
  exact first_potential_cap_of_clockHistory hvalid hseed H hSv hvρ
 ·
  let p:=potentialCheckpoint w (clockCount (trace init ω S))
   (timeMainCount (trace init ω S)) (h - 1)
  have hs:=(H.start_positive (h - 1) (by omega) (by omega)).1
  have hSp:S≤p:=by dsimp only [p,potentialCheckpoint,warmCheckpoint]; omega
  have hpv:p≤v:=by
   have hnext:=work_before_next H hn hh hL
   have hlework:p≤workCheckpoint w (clockCount (trace init ω S))
     (timeMainCount (trace init ω S)) (h - 1):=by
    dsimp only [p,potentialCheckpoint,warmCheckpoint,workCheckpoint]
    unfold rawWork clockWarmup potentialTrials
    omega
   exact hlework.trans (hnext.le.trans hstart)
  have hmass:=preceding_total_at_current hvalid hseed H hn hell hh hL hstart hvρ past
  have hp:=successor_potential_cap_of_clockHistory (h - 1) (by omega)
   hvalid hseed H hSp hpv hSv le_rfl hvρ (totalPrevious ell h)
   (totalPrevious_le hh hle) (past.potential (h - 1) (by omega) (by omega)) hmass
  have he:h - 1+1=h:=by omega
  rwa [he] at hp
theorem total_start_of_precedingHours {init:InputCfg n}
  (hvalid:validInitial init) {ω:InputLog n} {S T ρ v ell h:ℕ}
  {w:ClockTimes init} (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w) (hn:0 < n)
  (hell:5≤ell) (hh:1≤h) (hle:h≤ell)
  (hL:h≤PhaseThreeModel.Numeric.hourIndex n)
  (hstart:w.start h≤v) (hvρ:v < ρ)
  (past:PrecedingHours init ω S w ell h) :
  targetStart (totalRegime ell h) .pos ⟨h,by omega⟩
   (timeMainCount (trace init ω S)) (trace init ω v):=by
 have hm:=preceding_total_at_current hvalid hseed H hn hell hh hL hstart hvρ past
 have he:h=(h - 1)+1:=by omega
 have hb:(2:ℚ)^h*mixedAbsoluteMass (trace init ω v) ≤
   2*totalPrevious ell h*timeMainCount (trace init ω S):=by
  conv_lhs=>rw [he,pow_succ]
  nlinarith only [hm]
 have hr:(2:ℝ)^h*(mixedAbsoluteMass (trace init ω v):ℝ) ≤
   2*(totalPrevious ell h:ℝ)*timeMainCount (trace init ω S):=by
  exact_mod_cast hb
 simpa only [targetStart,targetQuantity,totalRegime_kind,
  totalPrevious_cast ell h hell hh hle] using hr
theorem old_failure_of_precedingHours {init:InputCfg n}
  (hvalid:validInitial init) {ω:InputLog n} {S T ρ ell h:ℕ}
  {w:ClockTimes init} (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w) (hn:timePopulationThreshold≤n)
  (hle:h≤ell) (hL:h≤PhaseThreeModel.Numeric.hourIndex n)
  (seed:InputLog n→WithTop ℕ) (hseedTime:seed ω=(S:WithTop ℕ))
  (hold:oldCutoff n < h) (past:PrecedingHours init ω S w ell h)
  (hpositive:1≤augmentedPhiNat (h - oldCutoff n)
   (trace init ω (warmCheckpoint w (clockCount (trace init ω S)) h))) :
  ω∈randomBlocksFailure init (hourPotentialEnd init seed (h - oldCutoff n))
   (hourWarmStart init seed h) (h - oldCutoff n)
   (ENNReal.ofReal (oldWorkRate n (timeMainCount (trace init ω S))))
   (timeMainCount (trace init ω S) / 1000)
   (oldWorkTrials n (timeMainCount (trace init ω S)))
   (oldBlockStarts init seed (h - oldCutoff n) (oldCutoff n)):=by
 let r:=h - oldCutoff n
 let q:=oldCutoff n
 let M:=timeMainCount (trace init ω S)
 let C:=clockCount (trace init ω S)
 have hq:7≤q:=oldCutoff_ge_seven hn
 have hr:1≤r:=by dsimp only [r]; omega
 have he:r+q=h:=by dsimp only [r,q]; omega
 have hbefore:r < h:=by omega
 have hcapQ:=past.potential r hr hbefore
 have hcapN:1000*augmentedPhiNat r
   (trace init ω (potentialCheckpoint w C M r))≤M:=by
  have hcast:(1000:ℚ)*(augmentedPhiNat r
    (trace init ω (potentialCheckpoint w C M r)):ℚ)≤M:=by
   rw [augmentedPhiNat_cast]
   exact hcapQ
  exact_mod_cast hcast
 have hcap:augmentedPhiNat r
   (trace init ω (potentialCheckpoint w C M r))≤M / 1000:=by omega
 have hwarm:∀ j:Fin (q - 6),
   changingZeroFuel (r+1+j.val)
    (trace init ω (warmCheckpoint w C (r+1+j.val))) ≤
     (101 / 500:ℚ)*M:=by
  intro j
  have hj:=j.isLt
  have hp:=past.warm (r+1+j.val) (by omega) (by omega)
  rw [old_block_previous_early (by omega) (by omega) hle] at hp
  norm_num at hp
  exact hp
 let P:=potentialCheckpoint w C M r
 let W:=warmCheckpoint w C h
 have hnpos:0 < n:=by exact_mod_cast (population_log_lower hn).1
 have hPW:P≤W:=by
  simpa only [he] using
   potential_checkpoint_le_later_warm H hnpos r (r+q) hr (by omega) (by omega)
 have hsum:P+(W - P)=W:=by omega
 refine ⟨P,W - P,?_,?_,?_,?_,?_⟩
 · exact hourPotentialEnd_clockHistory H seed r hseedTime (by omega)
 ·
  rw [hsum]
  exact hourWarmStart_clockHistory H seed h hseedTime hL
 · simpa only [he] using canonical_old_workLive hvalid hseed H hn seed hseedTime
     r q (M / 1000) hr hq (by omega) hcap hwarm
 · simpa only [he] using canonical_old_blocks_complete H hnpos seed hseedTime
     r q hq (by omega)
 · simpa only [hsum] using hpositive
def PrecedingMinority (σ:Sign) (init:InputCfg n) (ω:InputLog n) (S:ℕ)
  (w:ClockTimes init) (ell h:ℕ):Prop :=
 ∀ j,1≤j→j < h→ell≤j+4 →
  (2:ℚ)^j*sideMass (oppositeSign σ) (trace init ω
   (workCheckpoint w (clockCount (trace init ω S))
    (timeMainCount (trace init ω S)) j)) ≤
     minorityTarget ell j*timeMainCount (trace init ω S)
theorem minority_start_of_precedingHours (σ:Sign) {init:InputCfg n}
  (hvalid:validInitial init) {ω:InputLog n} {S T ρ v ell h:ℕ}
  {w:ClockTimes init} (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w) (hn:0 < n)
  (hell:5≤ell) (hh:1≤h) (hle:h≤ell) (hlast:ell≤h+4)
  (hL:h≤PhaseThreeModel.Numeric.hourIndex n)
  (hstart:w.start h≤v) (hvρ:v < ρ) (hwinning:winningSign init σ)
  (hscale:2*timeMainCount (trace init ω S)≤5*2^ell*gapMagnitude init)
  (past:PrecedingHours init ω S w ell h)
  (pastMinority:PrecedingMinority σ init ω S w ell h) :
  targetStart (minorityRegime ell h) σ ⟨h,by omega⟩
   (timeMainCount (trace init ω S)) (trace init ω v):=by
 have hSv:=((H.start_positive h hh hL).1).trans hstart
 have hm:(2:ℚ)^(h - 1)*sideMass (oppositeSign σ) (trace init ω v) ≤
   minorityPrevious ell h*timeMainCount (trace init ω S):=by
  by_cases hfirst:h+4=ell
  ·
   have hk:h - 1=ell - 5:=by omega
   have ht:=preceding_total_at_current hvalid hseed H hn hell hh hL hstart hvρ past
   rw [totalPrevious_early hh (by omega)] at ht
   have hb:=minority_base_of_total_checkpoint σ hvalid H hSv hvρ
    hwinning hell hscale (by simpa only [hk] using ht)
   simpa only [minorityPrevious,hk] using hb
  ·
   let u:=workCheckpoint w (clockCount (trace init ω S))
    (timeMainCount (trace init ω S)) (h - 1)
   have hSu:S≤u:=by
    have hs:=(H.start_positive (h - 1) (by omega) (by omega)).1
    dsimp only [u,workCheckpoint]
    omega
   have huv:u≤v:=(work_before_next H hn hh hL).le.trans hstart
   have hmono:=sideMass_le_of_clockHistory (oppositeSign σ) hvalid hseed H hSu huv hvρ
   exact (mul_le_mul_of_nonneg_left hmono
    (show (0:ℚ)≤2^(h - 1) by positivity)).trans
     (pastMinority (h - 1) (by omega) (by omega) (by omega))
 have he:h=(h - 1)+1:=by omega
 have hb:(2:ℚ)^h*sideMass (oppositeSign σ) (trace init ω v) ≤
   2*minorityPrevious ell h*timeMainCount (trace init ω S):=by
  conv_lhs=>rw [he,pow_succ]
  nlinarith only [hm]
 have hr:(2:ℝ)^h*(sideMass (oppositeSign σ) (trace init ω v):ℝ) ≤
   2*(minorityPrevious ell h:ℝ)*timeMainCount (trace init ω S):=by
  exact_mod_cast hb
 simpa only [targetStart,targetQuantity,minorityRegime_kind,
  minorityPrevious_cast ell h hell hh hle hlast] using hr
end Ripple.PopulationProtocol.ExactMajority.AveragingHourGateAssembly
end
