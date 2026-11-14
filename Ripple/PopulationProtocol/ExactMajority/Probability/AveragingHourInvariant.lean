-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingHourInvariant.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingSparseEntry
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingChangingZeroTail
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingTerminalDebtDeadlines
import Ripple.PopulationProtocol.ExactMajority.Probability.NonMainBiasZero
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingActiveCarrierProduct
noncomputable section
namespace Ripple.PopulationProtocol.ExactMajority.AveragingHourInvariant
open TimeTheorem PairLog StageEventSpec P3DeterministicAlgebra
open AveragingSparseEntry AveragingMixedAlgebra AveragingMixedLedgers
open AveragingMixedPotentialTransitions AveragingIntegerPotential
open AveragingPotentialService AveragingChangingZeroTail
open AveragingTerminalDebtDeadlines
open AveragingLiveProduct AveragingCancellationLedger
variable {L K n:ℕ}
theorem population_of_clockHistory {init:InputCfg n} {ω:InputLog n}
  {S T ρ:ℕ} {w:ClockTimes init}
  (H:ClockHistory init ω S T ρ w) (v:ℕ) :
  (trace init ω v).card=n:=by
 have hs:(trace init ω S).card=init.card :=
  Protocol.reachable_card_eq
   (PhaseZeroEntry.phase_zero_trace_reachable init ω S)
 have hv:(trace init ω v).card=init.card :=
  Protocol.reachable_card_eq
   (PhaseZeroEntry.phase_zero_trace_reachable init ω v)
 exact hv.trans (hs.symm.trans H.entry.seed_profile.card_eq)
theorem mainCount_eq_seed {init:InputCfg n} {ω:InputLog n}
  {S T ρ v:ℕ} {w:ClockTimes init}
  (H:ClockHistory init ω S T ρ w) (hSv:S≤v) (hvρ:v < ρ) :
  RoleSplitConcentration.mainCount (trace init ω v) =
   timeMainCount (trace init ω S):=by
 convert H.main_count v hSv hvρ using 1 <;>
  simp only [RoleSplitConcentration.mainCount,timeMainCount] <;> congr!
theorem potentialDomain_of_safeSparseSeed_clockHistory
  {init:InputCfg n} (hvalid:validInitial init) {ω:InputLog n}
  {S T ρ v:ℕ} {w:ClockTimes init}
  (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w) (hSv:S≤v) (hvρ:v < ρ) :
  PotentialDomain (trace init ω v):=by
 have hreach:=PhaseZeroEntry.phase_zero_trace_reachable init ω v
 have hsafe:=safeSparseSeed_small_safe_future init ω S v hseed hSv
 have hrange:=H.phase_range v hSv hvρ
 have hroles:=PhaseTwoActivation.trace_final_roles_of_range init hvalid ω v hrange
 have hs:=reachable_nonMain_smallBias_zero init (trace init ω v) hvalid hreach
 have hb:=NonMainBiasZero.reachable_nonMainBiasZero init (trace init ω v) hvalid hreach
 have hwf:=PhaseTwoDrainedSafety.reachable_small_safe_wf init (trace init ω v)
  hvalid hreach (fun a ha=>(hrange a ha).1)
  (fun a ha=>by have:=(hrange a ha).2; omega) hsafe
 intro a ha
 refine ⟨hrange a ha,hwf a ha,?_,?_⟩
 ·
  intro hm
  rcases hroles a ha with hmain | hc | hr
  · exact (hm hmain).elim
  · exact hs a ha (Or.inr hc)
  · exact hs a ha (Or.inl hr)
 ·
  intro hp hm
  exact hb a ha hm (by omega) (by omega)
theorem mixedAbsoluteMass_le_of_clockHistory
  {init:InputCfg n} (hvalid:validInitial init) {ω:InputLog n}
  {S T ρ u v:ℕ} {w:ClockTimes init}
  (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w)
  (hSu:S≤u) (huv:u≤v) (hvρ:v < ρ) :
  mixedAbsoluteMass (trace init ω v)≤mixedAbsoluteMass (trace init ω u):=by
 have hdom (t:ℕ) (hut:u≤t) (htv:t≤v) :
   PotentialDomain (trace init ω t) :=
  potentialDomain_of_safeSparseSeed_clockHistory hvalid hseed H
   (hSu.trans hut) (lt_of_le_of_lt htv hvρ)
 have hsides:=trace_mixedSides_le init hvalid ω u v huv
  (fun t hut htv a ha=>(hdom t hut htv a ha).range)
  (fun t hut htv a ha=>(hdom t hut htv a ha).safe)
  (fun t hut htv a ha=>(hdom t hut htv a ha).small_carrier)
 rw [← (mixedMassIdentities (trace init ω v)).2,
←(mixedMassIdentities (trace init ω u)).2]
 exact add_le_add hsides.1 hsides.2
theorem sideMass_le_of_clockHistory (σ:Sign)
  {init:InputCfg n} (hvalid:validInitial init) {ω:InputLog n}
  {S T ρ u v:ℕ} {w:ClockTimes init}
  (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w)
  (hSu:S≤u) (huv:u≤v) (hvρ:v < ρ) :
  sideMass σ (trace init ω v)≤sideMass σ (trace init ω u):=by
 have hdom (t:ℕ) (hut:u≤t) (htv:t≤v) :
   PotentialDomain (trace init ω t) :=
  potentialDomain_of_safeSparseSeed_clockHistory hvalid hseed H
   (hSu.trans hut) (lt_of_le_of_lt htv hvρ)
 exact sideMass_trace_le σ init hvalid ω u v huv
  (fun t hut htv a ha=>(hdom t hut htv a ha).range)
  (fun t hut htv a ha=>(hdom t hut htv a ha).safe)
  (fun t hut htv a ha=>(hdom t hut htv a ha).small_carrier)
theorem augmentedPhi_le_of_clockHistory (h:ℕ) (hh:1≤h)
  {init:InputCfg n} (hvalid:validInitial init) {ω:InputLog n}
  {S T ρ u v:ℕ} {w:ClockTimes init}
  (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w)
  (hSu:S≤u) (huv:u≤v) (hvρ:v < ρ) :
  augmentedPhi h (trace init ω v)≤augmentedPhi h (trace init ω u):=by
 have hdom (t:ℕ) (hut:u≤t) (htv:t≤v) :
   PotentialDomain (trace init ω t) :=
  potentialDomain_of_safeSparseSeed_clockHistory hvalid hseed H
   (hSu.trans hut) (lt_of_le_of_lt htv hvρ)
 exact trace_augmentedPhi_le h hh init ω u v huv
  (fun t hut htv a ha=>(hdom t hut htv a ha).range)
  (fun t hut htv a ha=>(hdom t hut htv a ha).safe)
  (fun t hut htv a ha=>(hdom t hut htv a ha).small_carrier)
theorem sparse_mass_of_safeSparseSeed_clockHistory
  {init:InputCfg n} (hvalid:validInitial init) {ω:InputLog n}
  {S T ρ v:ℕ} {w:ClockTimes init}
  (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w) (hSv:S≤v) (hvρ:v < ρ) :
  mixedAbsoluteMass (trace init ω v) ≤
   (3 / 100:ℚ)*timeMainCount (trace init ω S):=by
 have hmono:=mixedAbsoluteMass_le_of_clockHistory hvalid hseed H
  le_rfl hSv hvρ
 have hsparse:(100:ℚ)*mixedAbsoluteMass (trace init ω S) ≤
   3*(timeMainCount (trace init ω S):ℚ):=hseed.2.2.1
 linarith only [hmono,hsparse]
theorem firstAgentPhi_le_twice_mass (a:AgentState L K) :
  augmentedAgentPhi 1 a≤2 * |prePhase4Mass a|:=by
 by_cases hp:a.phase.val < 3
 · simp [augmentedAgentPhi,pendingPotentialWeight,prePhase4Mass,hp]
 ·
  cases hb:a.bias with
  | zero =>
    simp [augmentedAgentPhi,prePhase4Mass,hp,hb,
     agentPhiAboveQ,phiBiasWeightQ,Bias.toRat]
  | dyadic σ i =>
    by_cases hi:i.val < 1
    ·
     have hiZero:i.val=0:=by omega
     cases σ <;>
      norm_num [augmentedAgentPhi,prePhase4Mass,hp,hb,
       agentPhiAboveQ,phiBiasWeightQ,Bias.toRat,hiZero]
    ·
     simp only [augmentedAgentPhi,if_neg hp,agentPhiAboveQ,
      phiBiasWeightQ,hb,if_neg hi]
     exact mul_nonneg (by norm_num) (abs_nonneg _)
theorem firstPhi_le_twice_mass (c:Cfg L K) :
  augmentedPhi 1 c≤2*mixedAbsoluteMass c:=by
 induction c using Multiset.induction_on with
 | empty=>simp [augmentedPhi,mixedAbsoluteMass]
 | cons a c ih =>
   have ha:=firstAgentPhi_le_twice_mass a
   simp only [augmentedPhi,mixedAbsoluteMass,
    Multiset.map_cons,Multiset.sum_cons] at ih ⊢
   linarith only [ha,ih]
theorem activeLevelWeight_le_scaled_mass (h:ℕ) (a:AgentState L K) :
  activeLevelWeight h a≤(2:ℚ)^h * |prePhase4Mass a|:=by
 by_cases hp:a.phase.val < 3
 ·
  simp only [activeLevelWeight,if_pos hp]
  exact mul_nonneg (by positivity) (abs_nonneg _)
 ·
  cases hb:a.bias with
  | zero=>simp [activeLevelWeight,prePhase4Mass,hp,hb,Bias.toRat]
  | dyadic σ i =>
    by_cases hi:i.val=h
    ·
     have he:(2:ℚ)^h * |prePhase4Mass a|=1:=by
      cases σ <;>
       simp [prePhase4Mass,hp,hb,Bias.toRat,hi,abs_div]
     simp only [activeLevelWeight,if_neg hp,hb,if_pos hi,he,le_refl]
    ·
     simp only [activeLevelWeight,if_neg hp,hb,if_neg hi]
     exact mul_nonneg (by positivity) (abs_nonneg _)
theorem activeLevelCount_le_scaled_mass (h:ℕ) (c:Cfg L K) :
  activeLevelCount h c≤(2:ℚ)^h*mixedAbsoluteMass c:=by
 induction c using Multiset.induction_on with
 | empty=>simp [activeLevelCount,mixedAbsoluteMass]
 | cons a c ih =>
   have ha:=activeLevelWeight_le_scaled_mass h a
   simp only [activeLevelCount,mixedAbsoluteMass,
    Multiset.map_cons,Multiset.sum_cons] at ih ⊢
   nlinarith only [ha,ih]
theorem first_potential_cap_of_clockHistory
  {init:InputCfg n} (hvalid:validInitial init) {ω:InputLog n}
  {S T ρ v:ℕ} {w:ClockTimes init}
  (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w) (hSv:S≤v) (hvρ:v < ρ) :
  augmentedPhi 1 (trace init ω v) ≤
   (103 / 250:ℚ)*timeMainCount (trace init ω S):=by
 have hphi:=firstPhi_le_twice_mass (trace init ω v)
 have hmass:=sparse_mass_of_safeSparseSeed_clockHistory hvalid hseed H hSv hvρ
 have hM:(0:ℚ)≤timeMainCount (trace init ω S):=by positivity
 nlinarith only [hphi,hmass,hM]
theorem successor_potential_cap_of_clockHistory (k:ℕ) (hk:1≤k)
  {init:InputCfg n} (hvalid:validInitial init) {ω:InputLog n}
  {S T ρ p u v:ℕ} {w:ClockTimes init}
  (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w)
  (hSp:S≤p) (hpv:p≤v) (hSu:S≤u) (huv:u≤v)
  (hvρ:v < ρ) (r:ℚ) (hr:r≤51 / 125)
  (hpotential:(1000:ℚ)*augmentedPhi k (trace init ω p) ≤
   timeMainCount (trace init ω S))
  (hmass:(2:ℚ)^k*mixedAbsoluteMass (trace init ω u) ≤
   r*timeMainCount (trace init ω S)) :
  augmentedPhi (k+1) (trace init ω v) ≤
   (103 / 250:ℚ)*timeMainCount (trace init ω S):=by
 have hphi:=augmentedPhi_le_of_clockHistory k hk hvalid hseed H hSp hpv hvρ
 have hmassMono:=mixedAbsoluteMass_le_of_clockHistory hvalid hseed H hSu huv hvρ
 have hscaled:=mul_le_mul_of_nonneg_left hmassMono
  (show (0:ℚ)≤2^k by positivity)
 have hlevel:=activeLevelCount_le_scaled_mass k (trace init ω v)
 have hrow:=mul_le_mul_of_nonneg_right hr
  (show (0:ℚ)≤timeMainCount (trace init ω S) by positivity)
 rw [augmentedPhi_successor k hk]
 nlinarith only [hphi,hpotential,hscaled,hmass,hlevel,hrow]
theorem integer_potential_cap_of_rational (h M:ℕ) (c:Cfg L K)
  (hc:augmentedPhi h c≤(103 / 250:ℚ)*M) :
  (augmentedPhiNat h c:ℝ)≤(103 / 250:ℝ)*M:=by
 have hq:(augmentedPhiNat h c:ℚ)≤(103 / 250:ℚ)*M:=by
  rwa [augmentedPhiNat_cast]
 have h2:(((augmentedPhiNat h c:ℚ)):ℝ)≤(((103 / 250:ℚ)*M:ℚ):ℝ):=Rat.cast_le.mpr hq
 push_cast at h2
 exact h2
open Classical in
theorem fuelGate_of_previous_mass
  {init:InputCfg n} (hvalid:validInitial init) {ω:InputLog n}
  {S T ρ u v h:ℕ} {w:ClockTimes init}
  (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w)
  (hSu:S≤u) (huv:u≤v) (hvρ:v < ρ)
  (hh:h≤PhaseThreeModel.Numeric.hourIndex n)
  (hstart:w.start h≤v) (hfinish:v≤w.finish h)
  (A:ℚ) (hmass:(2:ℚ)^h*mixedAbsoluteMass (trace init ω u)≤A) :
  FuelGate h A n (warmClockCount (clockCount (trace init ω S)))
   (trace init ω v):=by
 have hSv:=hSu.trans huv
 refine ⟨population_of_clockHistory H v,
  potentialDomain_of_safeSparseSeed_clockHistory hvalid hseed H hSv hvρ,
  ?_,clockFloor_of_clockHistory H hSv hvρ h hh hstart hfinish⟩
 exact (mul_le_mul_of_nonneg_left
  (mixedAbsoluteMass_le_of_clockHistory hvalid hseed H hSu huv hvρ)
  (show (0:ℚ)≤2^h by positivity)).trans hmass
theorem activeCancellationGate_of_checkpoint
  {init:InputCfg n} (hvalid:validInitial init) {ω:InputLog n}
  {S T ρ p v:ℕ} {w:ClockTimes init}
  (hseed:SafeSparseSeed init ω S)
  (H:ClockHistory init ω S T ρ w)
  (level:Fin (PhaseThreeModel.Numeric.hourIndex n+1))
  (hh:1≤level.val) (hSp:S≤p) (hpv:p≤v) (hvρ:v < ρ)
  (hfinish:v≤w.finish level.val)
  (hpotential:(1000:ℚ)*augmentedPhi level.val (trace init ω p) ≤
   timeMainCount (trace init ω S)) :
  AveragingActiveCarrierProduct.ActiveCancellationGate level
   (timeMainCount (trace init ω S)) (trace init ω v):=by
 have hSv:=hSp.trans hpv
 have hdom:=potentialDomain_of_safeSparseSeed_clockHistory hvalid hseed H hSv hvρ
 refine ⟨(fun a ha=>(hdom a ha).range),
  (fun a ha=>(hdom a ha).safe),
  (fun a ha=>(hdom a ha).small_carrier),?_,?_,?_⟩
 ·
  intro a ha hm hp
  exact (hdom a ha).active_carrier (by have:=(hdom a ha).range.2; omega) hm
 ·
  have hmono:=augmentedPhi_le_of_clockHistory level.val hh hvalid hseed H hSp hpv hvρ
  linarith only [hmono,hpotential]
 ·
  have hcap:level.val≤PhaseThreeModel.Numeric.hourIndex n:=by
   have:=level.isLt
   omega
  have hdeep:=H.main_deep_tail level.val hcap v hSv hfinish
  rw [AveragingLiveProduct.deepCount_clockHistory H hSv hvρ level.val]
  omega
def pendingClockWitness : AgentState 0 256 :=
  { input := .A, output := .T, phase := ⟨1, by decide⟩, role := .clock,
    assigned := false, bias := .dyadic .pos ⟨0, by decide⟩,
    smallBias := ⟨3, by decide⟩, hour := ⟨0, by decide⟩,
    minute := ⟨0, by decide⟩, full := false,
    opinions := ⟨0, by decide⟩, counter := ⟨50, by decide⟩ }
theorem pendingClockWitness_fields :
  pendingClockWitness.phase.val=1 ∧
   pendingClockWitness.role≠.main ∧
   pendingClockWitness.smallBias.val=3 ∧
   pendingClockWitness.bias≠.zero:=by decide
theorem pendingClockWitness_potentialAgent:PotentialAgent pendingClockWitness:=by
 constructor
 · decide
 · decide
 · intro _; rfl
 ·
  intro hp
  have:pendingClockWitness.phase.val=1:=rfl
  omega
def initialRawBiasWitness : AgentState 0 256 :=
  { pendingClockWitness with
    phase := ⟨0, by decide⟩, role := .mcr, smallBias := ⟨4, by decide⟩ }
theorem initialRawBiasWitness_valid :
  validInitial ({initialRawBiasWitness}:Cfg 0 256):=by
 intro a ha
 have he:a=initialRawBiasWitness:=by simpa only [Multiset.mem_singleton] using ha
 subst a
 decide
theorem initialRawBiasWitness_nonzero:initialRawBiasWitness.bias≠.zero:=by decide
end Ripple.PopulationProtocol.ExactMajority.AveragingHourInvariant
end
