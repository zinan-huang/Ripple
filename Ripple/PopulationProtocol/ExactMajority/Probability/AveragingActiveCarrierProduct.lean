-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingActiveCarrierProduct.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCancellationTargets
noncomputable section
namespace Ripple.PopulationProtocol.ExactMajority.AveragingActiveCarrierProduct
open TimeTheorem PairLog P3DeterministicAlgebra StageEventSpec
open AveragingMixedAlgebra AveragingMixedLedgers AveragingLiveProduct
open AveragingCancellationAlgebra AveragingCancellationProbability
open AveragingCancellationTargets
variable {L K m:ℕ}
structure ActiveCancellationGate (level:Fin (L+1)) (M:ℕ)
  (c:Cfg L 256):Prop where
 range:∀ a∈c,1≤a.phase.val∧a.phase.val≤3
 safe:∀ a∈c,a.smallBias.val∈({2,3,4}:Finset ℕ)
 small_carrier:∀ a∈c,a.role≠.main→a.smallBias.val=3
 bias_carrier:∀ a∈c,a.role≠.main→3≤a.phase.val→a.bias=.zero
 potential:(1000:ℚ)*augmentedPhi level.val c≤M
 deep:1250*deepCount level.val c≤3*M
theorem active_scaled_agent_mass_le_level_phi_deep
  (j:Fin (L+1)) (hj:1≤j.val) (a:AgentState L K)
  (hphase:a.phase.val≤3)
  (hcarrier:a.role≠.main→3≤a.phase.val→a.bias=.zero) :
  (2:ℚ)^j.val * |prePhase4Mass a| ≤
   levelWeight .pos j a+levelWeight .neg j a +
    2*augmentedAgentPhi j.val a+(deepAtom j.val a:ℚ) / 2:=by
 by_cases hp:a.phase.val < 3
 ·
  have h:=scaled_mixedShallowWeight_le_phi j.val hj a
  have heq:mixedShallowWeight j.val a=|prePhase4Mass a|:=by
   simp [mixedShallowWeight,prePhase4Mass,hp]
  rw [heq] at h
  have hl:=levelWeight_nonneg .pos j a
  have hr:=levelWeight_nonneg .neg j a
  have hd:(0:ℚ)≤(deepAtom j.val a:ℚ) / 2:=by positivity
  linarith
 · exact scaled_agent_mass_le_level_phi_deep j hj a hphase
    (fun hm=>hcarrier hm (by omega))
theorem active_outsideMass_add_le
  (j:Fin (L+1)) (hj:1≤j.val) (c:Cfg L K)
  (hphase:∀ a∈c,a.phase.val≤3)
  (hcarrier:∀ a∈c,a.role≠.main→3≤a.phase.val→a.bias=.zero) :
  outsideMass .pos j c+outsideMass .neg j c ≤
   2*augmentedPhi j.val c+(deepCount j.val c:ℚ) / 2:=by
 have hsum :
   (2:ℚ)^j.val*mixedAbsoluteMass c ≤
    (levelCount .pos j c:ℚ)+(levelCount .neg j c:ℚ) +
     2*augmentedPhi j.val c+(deepCount j.val c:ℚ) / 2:=by
  rw [← sum_levelWeight,←sum_levelWeight]
  revert hphase hcarrier
  induction c using Multiset.induction_on with
  | empty =>
    intro _ _
    simp [mixedAbsoluteMass,augmentedPhi,deepCount]
  | cons a c ih =>
    intro hphase hcarrier
    have ha:=active_scaled_agent_mass_le_level_phi_deep j hj a
     (hphase a (Multiset.mem_cons_self _ _))
     (hcarrier a (Multiset.mem_cons_self _ _))
    have ht:=ih
     (fun b hb=>hphase b (Multiset.mem_cons_of_mem hb))
     (fun b hb=>hcarrier b (Multiset.mem_cons_of_mem hb))
    simp only [mixedAbsoluteMass,augmentedPhi,deepCount,
     Multiset.map_cons,Multiset.sum_cons,Nat.cast_add] at ht ⊢
    nlinarith only [ha,ht]
 unfold outsideMass
 rw [← sideMass_add c] at hsum
 nlinarith only [hsum]
theorem active_outsideMass_allowance
  (j:Fin (L+1)) (hj:1≤j.val) (c:Cfg L K) (M:ℕ)
  (hphase:∀ a∈c,a.phase.val≤3)
  (hcarrier:∀ a∈c,a.role≠.main→3≤a.phase.val→a.bias=.zero)
  (hphi:(1000:ℚ)*augmentedPhi j.val c≤M)
  (hdeep:1250*deepCount j.val c≤3*M) :
  outsideMass .pos j c+outsideMass .neg j c ≤
   (4 / 1250:ℚ)*M:=by
 have hs:=active_outsideMass_add_le j hj c hphase hcarrier
 have hd:(1250:ℚ)*(deepCount j.val c:ℚ)≤3*(M:ℚ):=by
  exact_mod_cast hdeep
 linarith
theorem active_level_product_of_total_mass
  (j:Fin (L+1)) (hj:1≤j.val) (c:Cfg L K) (M:ℕ)
  (hphase:∀ a∈c,a.phase.val≤3)
  (hcarrier:∀ a∈c,a.role≠.main→3≤a.phase.val→a.bias=.zero)
  (hphi:(1000:ℚ)*augmentedPhi j.val c≤M)
  (hdeep:1250*deepCount j.val c≤3*M)
  {r g:ℝ} (hg:0≤g) (hmin:(4 / 1250:ℝ)≤(r - g) / 2)
  (hw:r*M≤(2:ℝ)^j.val*(mixedAbsoluteMass c:ℝ))
  (hgap:|(2:ℝ)^j.val*(prePhase4MassSum c:ℝ)|≤g*M) :
  ((r+g) / 2)*((r - g) / 2 - 4 / 1250)*(M:ℝ)^2 ≤
   (levelCount .pos j c:ℝ)*(levelCount .neg j c:ℝ):=by
 have hpq:=outsideMass_nonneg .pos j c
 have hnq:=outsideMass_nonneg .neg j c
 have hoq:=active_outsideMass_allowance j hj c M hphase hcarrier hphi hdeep
 unfold outsideMass at hpq hnq hoq
 have hp:0≤(2:ℝ)^j.val*(sideMass .pos c:ℝ) -
   (levelCount .pos j c:ℝ):=by
  exact_mod_cast hpq
 have hn:0≤(2:ℝ)^j.val*(sideMass .neg c:ℝ) -
   (levelCount .neg j c:ℝ):=by
  exact_mod_cast hnq
 have ho :
   ((2:ℝ)^j.val*(sideMass .pos c:ℝ) - levelCount .pos j c) +
    ((2:ℝ)^j.val*(sideMass .neg c:ℝ) - levelCount .neg j c) ≤
   (4 / 1250:ℝ)*M:=by
  have h:=(Rat.cast_le (K:=ℝ)).2 hoq
  push_cast at h
  linarith only [h]
 have hadd:=congrArg (fun x:ℚ=>(x:ℝ)) (sideMass_add c)
 have hsub:=congrArg (fun x:ℚ=>(x:ℝ)) (sideMass_sub c)
 push_cast at hadd hsub
 apply product_floor_of_total_mass (by positivity) hg (by norm_num) hmin hp hn ho
 ·
  rw [← hadd,mul_add] at hw
  exact hw
 ·
  have heq :
    (2:ℝ)^j.val*(sideMass .pos c:ℝ) -
      (2:ℝ)^j.val*(sideMass .neg c:ℝ) =
     (2:ℝ)^j.val*(prePhase4MassSum c:ℝ):=by
    rw [← hsub]
    ring
  rwa [heq]
theorem active_level_product_of_minority
  (σ:Sign) (j:Fin (L+1)) (hj:1≤j.val)
  (c:Cfg L K) (M:ℕ)
  (hphase:∀ a∈c,a.phase.val≤3)
  (hcarrier:∀ a∈c,a.role≠.main→3≤a.phase.val→a.bias=.zero)
  (hphi:(1000:ℚ)*augmentedPhi j.val c≤M)
  (hdeep:1250*deepCount j.val c≤3*M)
  {ξ g:ℝ} (hg:0≤g) (hξ:(4 / 1250:ℝ)≤ξ)
  (hminority:ξ*M ≤
   (2:ℝ)^j.val*(sideMass (oppositeSign σ) c:ℝ))
  (hgap:g*M≤(2:ℝ)^j.val *
   ((sideMass σ c:ℝ) - (sideMass (oppositeSign σ) c:ℝ))) :
  (ξ+g)*(ξ - 4 / 1250)*(M:ℝ)^2 ≤
   (levelCount .pos j c:ℝ)*(levelCount .neg j c:ℝ):=by
 have hmajorq:=outsideMass_nonneg σ j c
 have hminorq:=outsideMass_nonneg (oppositeSign σ) j c
 have houtq:outsideMass σ j c+outsideMass (oppositeSign σ) j c ≤
   (4 / 1250:ℚ)*M:=by
  have h:=active_outsideMass_allowance j hj c M hphase hcarrier hphi hdeep
  cases σ
  · exact h
  · simpa only [oppositeSign,add_comm] using h
 unfold outsideMass at hmajorq hminorq houtq
 have hmajor:0≤(2:ℝ)^j.val*(sideMass σ c:ℝ) -
   (levelCount σ j c:ℝ):=by exact_mod_cast hmajorq
 have hminor:0≤(2:ℝ)^j.val*(sideMass (oppositeSign σ) c:ℝ) -
   (levelCount (oppositeSign σ) j c:ℝ):=by exact_mod_cast hminorq
 have hout :
   ((2:ℝ)^j.val*(sideMass σ c:ℝ) - levelCount σ j c) +
    ((2:ℝ)^j.val*(sideMass (oppositeSign σ) c:ℝ) -
     levelCount (oppositeSign σ) j c)≤(4 / 1250:ℝ)*M:=by
  have h:=(Rat.cast_le (K:=ℝ)).2 houtq
  push_cast at h
  linarith only [h]
 have hgap':g*M≤(2:ℝ)^j.val*(sideMass σ c:ℝ) -
   (2:ℝ)^j.val*(sideMass (oppositeSign σ) c:ℝ):=by
  simpa only [mul_sub] using hgap
 have hp:=product_floor_of_minority (by positivity:(0:ℝ)≤M)
  hg (by norm_num:(0:ℝ)≤4 / 1250) hξ hmajor hminor hout
  hminority hgap'
 cases σ
 · exact hp
 · simpa only [oppositeSign,mul_comm] using hp
theorem active_target_live_product (r:CancellationRegime) (σ:Sign)
  (level:Fin (L+1)) (hh:1≤level.val) (M:ℕ)
  {m:ℕ} (f:Fin m→AgentState L 256)
  (hlive:ActiveCancellationGate level M (labelCfg f) ∧
   targetGap r σ level M (labelCfg f) ∧
   currentTarget r*M < targetQuantity r σ level (labelCfg f)) :
  (cancellationParameters r).1*(cancellationParameters r).2.1*(M:ℝ)^2 ≤
   ((levelSet f .pos level).card:ℝ)*(levelSet f .neg level).card:=by
 obtain ⟨hg,hrow⟩:=target_row_parameters r
 have hc:=hlive.1
 cases hm:targetKind r
 ·
  simp only [hm] at hrow
  obtain ⟨hmin,hA,hB,_⟩:=hrow
  have hgap:|(2:ℝ)^level.val*(prePhase4MassSum (labelCfg f):ℝ)| ≤
    gapTarget r*M:=by
   simpa only [targetGap,hm] using hlive.2.1
  have hmass:currentTarget r*M ≤
    (2:ℝ)^level.val*(mixedAbsoluteMass (labelCfg f):ℝ):=by
   simpa only [targetQuantity,hm] using hlive.2.2.le
  have hp:=active_level_product_of_total_mass level hh (labelCfg f) M
   (fun a ha=>(hc.range a ha).2) hc.bias_carrier hc.potential hc.deep
   hg hmin hmass hgap
  simpa only [hA,hB,levelCount_labelCfg] using hp
 ·
  simp only [hm] at hrow
  obtain ⟨hmin,hA,hB,_⟩:=hrow
  have hgap:gapTarget r*M≤(2:ℝ)^level.val *
    ((sideMass σ (labelCfg f):ℝ) -
     (sideMass (oppositeSign σ) (labelCfg f):ℝ)):=by
   simpa only [targetGap,hm] using hlive.2.1
  have hmass:currentTarget r*M≤(2:ℝ)^level.val *
    (sideMass (oppositeSign σ) (labelCfg f):ℝ):=by
   simpa only [targetQuantity,hm] using hlive.2.2.le
  have hp:=active_level_product_of_minority σ level hh (labelCfg f) M
   (fun a ha=>(hc.range a ha).2) hc.bias_carrier hc.potential hc.deep
   hg hmin hmass hgap
  simpa only [hA,hB,levelCount_labelCfg] using hp
end Ripple.PopulationProtocol.ExactMajority.AveragingActiveCarrierProduct
end
