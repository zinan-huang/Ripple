-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingOldHourGate.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingHourInvariant
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCanonicalBlocks
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingChangingZeroTail
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingFuelFloor
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingAtomBound
noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal
namespace Ripple.PopulationProtocol.ExactMajority.AveragingOldHourGate

open PhaseThreeClockProducer
open TimeTheorem PairLog StageEventSpec AveragingSparseEntry
open AveragingMixedLedgers AveragingIntegerPotential AveragingPotentialService
open AveragingPotentialDrift AveragingChangingZeroTail AveragingTerminalDebt
open AveragingCreditClockBridge AveragingFuelFloor AveragingHourInvariant
open AveragingNumerics AveragingOldBlocks AveragingWorkCounter
open AveragingObservedBlocks AveragingClockBlocks AveragingWorkBudget
open AveragingCanonicalBlocks AveragingSeededDelay AveragingRandomOldBlocks
open AveragingTerminalDebtDeadlines AveragingCancellationAlgebra
open AveragingAtomBound AveragingLogPotentialTail
variable {L n:ℕ}
theorem exactZeroCount_le_readyZeroCount (r j:ℕ) (hrj:r≤j)
  (c:Cfg L 256) (hc:PotentialDomain c) :
  exactZeroCount j c≤readyZeroCount r c:=by
 classical
 revert hc
 induction c using Multiset.induction_on with
 | empty =>
   intro hc
   simp [exactZeroCount,readyZeroCount]
 | cons a c ih =>
   intro hc
   have ha:=hc a (by simp)
   have hrest:PotentialDomain c:=fun b hb=>hc b (by simp [hb])
   have hpoint:exactZeroWeight j a≤ if ReadyZero r a then 1 else 0:=by
    by_cases he:a.role=.main∧¬ a.phase.val < 3 ∧
      a.bias=.zero∧a.hour.val=j
    ·
     have hp:a.phase.val=3:=by have hp:=ha.range; omega
     have hr:r≤a.hour.val:=by omega
     have hready:ReadyZero r a:=⟨hp,he.1,he.2.2.1,hr⟩
     simp [exactZeroWeight,he,hready]
    ·
     have h0:exactZeroWeight j a=0:=by
      unfold exactZeroWeight
      rw [if_neg he]
     rw [h0]
     exact Nat.zero_le _
   simpa only [exactZeroCount,Multiset.map_cons,Multiset.sum_cons,
    readyZeroCount,Multiset.countP_cons,add_comm] using add_le_add hpoint (ih hrest)
theorem fuel_trace_le_of_domain (h:ℕ) (init:Cfg L 256)
  (ω:Ω L 256) (a b:ℕ) (hab:a≤b)
  (hdom:∀ v,a≤v→v≤b→PotentialDomain (trace init ω v)) :
  changingZeroFuel h (trace init ω b)≤changingZeroFuel h (trace init ω a):=by
 revert hdom
 induction b,hab using Nat.le_induction with
 | base =>
   intro hdom
   exact le_rfl
 | succ b hab ih =>
   intro hdom
   have hprev:=ih (fun v hav hvb=>hdom v hav (by omega))
   have hstep:changingZeroFuel h (trace init ω (b+1)) ≤
     changingZeroFuel h (trace init ω b):=by
    rw [TimeTheorem.trace_succ]
    apply changingZeroFuel_draw_le h _ (hdom b hab (by omega)) _
    simpa only [TimeTheorem.trace_succ] using
     hdom (b+1) (by omega) le_rfl
   exact hstep.trans hprev
theorem potential_trace_le_of_domain (h:ℕ) (hh:1≤h)
  (init:Cfg L 256) (ω:Ω L 256) (a b:ℕ) (hab:a≤b)
  (hdom:∀ v,a≤v→v≤b→PotentialDomain (trace init ω v)) :
  augmentedPhiNat h (trace init ω b)≤augmentedPhiNat h (trace init ω a) :=
 trace_augmentedPhiNat_le h hh init ω a b hab
  (fun v hav hvb s hs=>(hdom v hav hvb s hs).range)
  (fun v hav hvb s hs=>(hdom v hav hvb s hs).safe)
  (fun v hav hvb s hs=>(hdom v hav hvb s hs).small_carrier)
theorem oldWorkRate_le_readyRate {n M r:ℕ} (hn:2≤n)
  (c:Cfg L 256) (hpop:c.card=n)
  (hready:(77 / 100:ℚ)*M≤(readyZeroCount r c:ℚ)) :
  ENNReal.ofReal (oldWorkRate n M)≤readyRate r c:=by
 have hcard:2≤c.card:=by simpa only [hpop] using hn
 have hnpos:(0:ℝ) < n:=by exact_mod_cast (show 0 < n by omega)
 have hnreal:(2:ℝ)≤n:=by exact_mod_cast hn
 have hfloor:(77 / 100:ℝ)*M≤(readyZeroCount r c:ℝ):=by
  have h2:=(Rat.cast_le (K:=ℝ)).mpr hready
  push_cast at h2
  exact h2
 have hden:(c.totalPairs:ℝ)=(n:ℝ)*((n:ℝ) - 1):=by
  simp only [Config.totalPairs,hpop,Nat.cast_mul,
   Nat.cast_sub (show 1≤n by omega),Nat.cast_one]
 have hdpos:(0:ℝ) < c.totalPairs:=by
  rw [hden]
  exact mul_pos hnpos (by linarith only [hnreal])
 have hdle:(c.totalPairs:ℝ)≤(n:ℝ)^2:=by
  rw [hden]
  nlinarith only [hnpos]
 have hreal:oldWorkRate n M≤(readyRate r c).toReal:=by
  calc
   oldWorkRate n M=((77 / 100:ℝ)*M) / (n:ℝ)^2:=rfl
   _≤(readyZeroCount r c:ℝ) / (n:ℝ)^2 :=
    div_le_div_of_nonneg_right hfloor (sq_nonneg _)
   _≤(readyZeroCount r c:ℝ) / (c.totalPairs:ℝ) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hdpos hdle
   _=(readyRate r c).toReal:=by
    simp only [readyRate,ENNReal.toReal_div,ENNReal.toReal_natCast]
 calc
  ENNReal.ofReal (oldWorkRate n M) ≤
    ENNReal.ofReal ((readyRate r c).toReal):=ENNReal.ofReal_le_ofReal hreal
  _=readyRate r c:=ENNReal.ofReal_toReal (readyRate_ne_top r c hcard)
theorem checkpoint_order {init:InputCfg n} {ω:InputLog n}
  {S T ρ:ℕ} {w:ClockTimes init} (H:ClockHistory init ω S T ρ w)
  (hn:0 < n) (k:ℕ) (hkpos:1≤k)
  (hk:k≤PhaseThreeModel.Numeric.hourIndex n) :
  let C:=clockCount (trace init ω S)
  let M:=timeMainCount (trace init ω S)
  S≤w.start k ∧
   w.start k+clockWarmup n C+potentialTrials n M < w.finish k ∧
   w.finish k < ρ:=by
 dsimp only
 have hs:=(H.start_positive k hkpos hk).1
 have hfit:=clockHistory_raw_work_fits H hn k hk
 have hbudget :
   clockWarmup n (clockCount (trace init ω S)) +
     potentialTrials n (timeMainCount (trace init ω S)) ≤
    rawWork n (timeMainCount (trace init ω S)) (clockCount (trace init ω S)):=by
  unfold clockWarmup potentialTrials rawWork
  omega
 have hcap:=(H.hour_before_cap k hk).2
 have hexit:=H.protected_settling
 refine ⟨hs,?_,by omega⟩
 have hle:=add_le_add (le_refl (w.start k)) hbudget
 omega
theorem potential_checkpoint_le_later_warm {init:InputCfg n}
  {ω:InputLog n} {S T ρ:ℕ} {w:ClockTimes init}
  (H:ClockHistory init ω S T ρ w) (hn:0 < n)
  (a b:ℕ) (ha:1≤a) (hab:a < b)
  (hb:b≤PhaseThreeModel.Numeric.hourIndex n) :
  w.start a+clockWarmup n (clockCount (trace init ω S)) +
    potentialTrials n (timeMainCount (trace init ω S)) ≤
   w.start b+clockWarmup n (clockCount (trace init ω S)):=by
 have horder:=checkpoint_order H hn a ha (by omega)
 have hnext:=H.previous_end (a+1) (by omega) (by omega)
 have hmono:=clockHistory_start_mono H hn (a+1) b (by omega) hb
 simp only [Nat.add_sub_cancel] at hnext
 omega
theorem old_ready_floor_after_warm {init:InputCfg n}
  (hvalid:validInitial init) {ω:InputLog n} {S T ρ a v:ℕ}
  {w:ClockTimes init} (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w) (r j:ℕ) (hrj:r≤j)
  (hj:j≤PhaseThreeModel.Numeric.hourIndex n)
  (hSa:S≤a) (hav:a≤v) (hvρ:v < ρ) (hv:v≤w.finish j)
  (hfuel:changingZeroFuel j (trace init ω a) ≤
   (101 / 500:ℚ)*timeMainCount (trace init ω S)) :
  (77 / 100:ℚ)*timeMainCount (trace init ω S) ≤
   (readyZeroCount r (trace init ω v):ℚ):=by
 have hSv:S≤v:=hSa.trans hav
 have hdom:∀ u,a≤u→u≤v→PotentialDomain (trace init ω u):=by
  intro u hau huv
  exact potentialDomain_of_safeSparseSeed_clockHistory hvalid hseed H
   (hSa.trans hau) (lt_of_le_of_lt huv hvρ)
 have hpersist:=fuel_trace_le_of_domain j init ω a v hav hdom
 have hM:RoleSplitConcentration.mainCount (trace init ω v) =
   timeMainCount (trace init ω S):=by
  convert H.main_count v hSv hvρ using 1 <;>
   simp only [RoleSplitConcentration.mainCount,timeMainCount] <;> congr!
 have hz:=exact_zero_floor_early j (timeMainCount (trace init ω S))
  (trace init ω v) hM (hpersist.trans hfuel)
  (exceptionCount_bound_clockHistory H hSv hvρ j hj hv)
 exact hz.trans (by
  exact_mod_cast exactZeroCount_le_readyZeroCount r j hrj
   (trace init ω v) (hdom v hav le_rfl))
theorem canonical_old_workLive {init:InputCfg n}
  (hvalid:validInitial init) {ω:InputLog n} {S T ρ:ℕ}
  {w:ClockTimes init} (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w) (hn:timePopulationThreshold≤n)
  (seed:InputLog n→WithTop ℕ) (hseedTime:seed ω=(S:WithTop ℕ))
  (r q Ψ:ℕ) (hr:1≤r) (hq:7≤q)
  (hrq:r+q≤PhaseThreeModel.Numeric.hourIndex n)
  (hcap:augmentedPhiNat r
   (trace init ω (w.start r+clockWarmup n (clockCount (trace init ω S)) +
    potentialTrials n (timeMainCount (trace init ω S))))≤Ψ)
  (hwarm:∀ j:Fin (q - 6),
   changingZeroFuel (r+1+j.val)
    (trace init ω (w.start (r+1+j.val) +
     clockWarmup n (clockCount (trace init ω S)))) ≤
      (101 / 500:ℚ)*timeMainCount (trace init ω S)) :
  let C:=clockCount (trace init ω S)
  let M:=timeMainCount (trace init ω S)
  let P:=w.start r+clockWarmup n C+potentialTrials n M
  let W:=w.start (r+q)+clockWarmup n C
  WorkLive init P r (ENNReal.ofReal (oldWorkRate n M)) Set.univ Ψ
   (blockWork P (oldWorkTrials n M) (oldBlockStarts init seed r q)) (W - P) ω:=by
 let C:=clockCount (trace init ω S)
 let M:=timeMainCount (trace init ω S)
 let P:=w.start r+clockWarmup n C+potentialTrials n M
 let W:=w.start (r+q)+clockWarmup n C
 change WorkLive init P r (ENNReal.ofReal (oldWorkRate n M)) Set.univ Ψ
  (blockWork P (oldWorkTrials n M) (oldBlockStarts init seed r q)) (W - P) ω
 have hnlarge:40≤n:=(time_population_bounds hn).2
 have hnpos:0 < n:=by omega
 have hrorder:=checkpoint_order H hnpos r hr (by omega)
 have hhorder:=checkpoint_order H hnpos (r+q) (by omega) hrq
 have hSP:S≤P:=by dsimp only [P,C,M]; omega
 have hPW:P≤W :=
  potential_checkpoint_le_later_warm H hnpos r (r+q) hr (by omega) hrq
 have hWρ:W < ρ:=by dsimp only [W,C]; omega
 refine ⟨Set.mem_univ _,hcap,?_⟩
 intro u hu
 have hSu:S≤P+u:=by omega
 have huW:P+u≤W:=by omega
 have huρ:P+u < ρ:=lt_of_le_of_lt huW hWρ
 have hdomain:=potentialDomain_of_safeSparseSeed_clockHistory hvalid hseed H hSu huρ
 have hpop:(trace init ω (P+u)).card=n :=
  population_of_clockHistory H (P+u)
 refine ⟨by rw [hpop]; omega,hdomain,?_⟩
 intro hmarked
 obtain ⟨j,a,ha,_,hau,hua⟩ :=
  (blockWork_eq_true P (oldWorkTrials n M) (oldBlockStarts init seed r q) u ω).mp hmarked
 have hvalue:=oldBlockStarts_clockHistory H seed hseedTime r q hrq j
 have haeq:a=w.start (r+1+j.val)+clockWarmup n C:=by
  exact_mod_cast ha.symm.trans hvalue
 have hj:=j.isLt
 have hjL:r+1+j.val≤PhaseThreeModel.Numeric.hourIndex n:=by omega
 have hjstart:=(H.start_positive (r+1+j.val) (by omega) hjL).1
 have hjfinish:=clockHistory_oldWork_before_finish H hnpos (r+1+j.val) hjL
 have hbound:P+u≤w.finish (r+1+j.val):=by
  dsimp only [M,C] at haeq hua
  omega
 apply oldWorkRate_le_readyRate (by omega) _ hpop
 apply old_ready_floor_after_warm hvalid hseed H r (r+1+j.val)
  (by omega) hjL (a:=w.start (r+1+j.val)+clockWarmup n C)
  (by omega) (by omega) huρ hbound
 exact hwarm j
theorem logGate_after_warm {init:InputCfg n}
  (hvalid:validInitial init) {ω:InputLog n} {S T ρ a v:ℕ}
  {w:ClockTimes init} (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w) (hn:timePopulationThreshold≤n)
  (h:ℕ) (hh:1≤h) (hhL:h≤PhaseThreeModel.Numeric.hourIndex n)
  (hSa:S≤a) (hav:a≤v) (hvρ:v < ρ) (hv:v≤w.finish h)
  (z:ℚ) (hz:z≤(51 / 125:ℚ))
  (hfuel:changingZeroFuel h (trace init ω a) ≤
   (2*z+1 / 500)*timeMainCount (trace init ω S))
  (hold:h≤oldCutoff n ∨
   augmentedPhiNat (h - oldCutoff n) (trace init ω a)=0) :
  LogGate n (timeMainCount (trace init ω S)) h (trace init ω v):=by
 have hSv:S≤v:=hSa.trans hav
 have hdom:∀ u,a≤u→u≤v→PotentialDomain (trace init ω u):=by
  intro u hau huv
  exact potentialDomain_of_safeSparseSeed_clockHistory hvalid hseed H
   (hSa.trans hau) (lt_of_le_of_lt huv hvρ)
 have hpersist:=fuel_trace_le_of_domain h init ω a v hav hdom
 have hM:RoleSplitConcentration.mainCount (trace init ω v) =
   timeMainCount (trace init ω S):=by
  convert H.main_count v hSv hvρ using 1 <;>
   simp only [RoleSplitConcentration.mainCount,timeMainCount] <;> congr!
 have hzcount:=exact_zero_floor_general h (timeMainCount (trace init ω S))
  (trace init ω v) z hM (hpersist.trans hfuel)
  (exceptionCount_bound_clockHistory H hSv hvρ h hhL hv) hz
 have hreadyQ :
   (17 / 100:ℚ)*timeMainCount (trace init ω S) ≤
    (readyZeroCount h (trace init ω v):ℚ) :=
  hzcount.trans (by exact_mod_cast
   exactZeroCount_le_readyZeroCount h h le_rfl (trace init ω v) (hdom v hav le_rfl))
 have hready :
   (17 / 100:ℝ)*timeMainCount (trace init ω S) ≤
    (readyZeroCount h (trace init ω v):ℝ):=by
  have h2:=(Rat.cast_le (K:=ℝ)).mpr hreadyQ
  push_cast at h2
  exact h2
 have holdv:h≤oldCutoff n ∨
   augmentedPhiNat (h - oldCutoff n) (trace init ω v)=0:=by
  by_cases hearly:h≤oldCutoff n
  · exact Or.inl hearly
  ·
   have hzero:=hold.resolve_left hearly
   have hmono:=potential_trace_le_of_domain (h - oldCutoff n) (by omega)
    init ω a v hav hdom
   exact Or.inr (by omega)
 exact logGate_of_old_extinction hn h hh _ (hdom v hav le_rfl)
  (population_of_clockHistory H v) hready holdv
end Ripple.PopulationProtocol.ExactMajority.AveragingOldHourGate
end
