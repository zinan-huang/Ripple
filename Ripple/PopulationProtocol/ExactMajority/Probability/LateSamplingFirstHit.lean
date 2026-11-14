-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingFirstHit.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingSplice
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6RoleArrivals

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingFirstHit

def UnitSteps (C B : ℕ → ℕ) (s T : ℕ) : Prop :=
  ∀ u, s ≤ u → u < T →
    ∃ a b : ℕ, C (u+1) = C u+a ∧ B (u+1) = B u+b ∧ a ≤ 1 ∧ b ≤ a

variable {C B : ℕ → ℕ} {s T : ℕ}

theorem UnitSteps.count_le (h : UnitSteps C B s T)
    {u v : ℕ} (hsu : s ≤ u) (huv : u ≤ v) (hvT : v ≤ T) : C u ≤ C v := by
  revert hvT
  induction v, huv using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ v huv ih =>
      intro hvT
      have hp := ih (by omega)
      obtain ⟨a,b,hC,hB,ha,hba⟩ := h v (hsu.trans huv) (by omega)
      omega

theorem UnitSteps.bad_le (h : UnitSteps C B s T)
    {u v : ℕ} (hsu : s ≤ u) (huv : u ≤ v) (hvT : v ≤ T) : B u ≤ B v := by
  revert hvT
  induction v, huv using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ v huv ih =>
      intro hvT
      have hp := ih (by omega)
      obtain ⟨a,b,hC,hB,ha,hba⟩ := h v (hsu.trans huv) (by omega)
      omega

theorem UnitSteps.bad_increment_le (h : UnitSteps C B s T)
    {u v : ℕ} (hsu : s ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    B v + C u ≤ C v + B u := by
  revert hvT
  induction v, huv using Nat.le_induction with
  | base => intro _; omega
  | succ v huv ih =>
      intro hvT
      have hp := ih (by omega)
      obtain ⟨a,b,hC,hB,ha,hba⟩ := h v (hsu.trans huv) (by omega)
      omega

theorem UnitSteps.gap_le (h : UnitSteps C B s T)
    {u v : ℕ} (hsu : s ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    C u - B u ≤ C v - B v := by
  have hd := h.bad_increment_le hsu huv hvT
  omega

theorem UnitSteps.bad_eq_on_count_plateau (h : UnitSteps C B s T)
    {u v : ℕ} (hsu : s ≤ u) (huv : u ≤ v) (hvT : v ≤ T)
    (hC : C u = C v) : B u = B v := by
  have hmono := h.bad_le hsu huv hvT
  have hinc := h.bad_increment_le hsu huv hvT
  omega

theorem first_unit_hit {X : ℕ → ℕ} {s T k : ℕ}
    (hstep : ∀ u, s ≤ u → u < T → X (u+1) ≤ X u+1)
    (hzero : X s = 0) (hsT : s ≤ T) (hk : k ≤ X T) :
    ∃ t, s ≤ t ∧ t ≤ T ∧ X t = k ∧
      ∀ u, s ≤ u → u < t → X u < k := by
  classical
  have hex : ∃ t, s ≤ t ∧ t ≤ T ∧ k ≤ X t := ⟨T,hsT,le_rfl,hk⟩
  let t := Nat.find hex
  have ht : s ≤ t ∧ t ≤ T ∧ k ≤ X t := Nat.find_spec hex
  have hbefore : ∀ u, s ≤ u → u < t → X u < k := by
    intro u hsu hut
    have hn := Nat.find_min hex hut
    have huT : u ≤ T := (Nat.le_of_lt hut).trans ht.2.1
    by_contra h
    exact hn ⟨hsu,huT,by omega⟩
  have heq : X t = k := by
    by_cases hts : t = s
    · have hz : X t = 0 := by rw [hts,hzero]
      omega
    · have hsPred : s ≤ t-1 := by omega
      have hPred : t-1 < t := by omega
      have hp := hbefore (t-1) hsPred hPred
      have hn := hstep (t-1) hsPred (lt_of_lt_of_le hPred ht.2.1)
      have he : t-1+1 = t := by omega
      rw [he] at hn
      omega
  exact ⟨t,ht.1,ht.2.1,heq,hbefore⟩

theorem first_count_hit (h : UnitSteps C B s T) {k : ℕ}
    (hzero : C s = 0) (hsT : s ≤ T) (hk : k ≤ C T) :
    ∃ t, s ≤ t ∧ t ≤ T ∧ C t = k ∧
      ∀ u, s ≤ u → u < t → C u < k := by
  apply first_unit_hit ?_ hzero hsT hk
  intro u hsu huT
  obtain ⟨a,b,hC,hB,ha,hba⟩ := h u hsu huT
  omega

theorem first_count_hit_with_bad (h : UnitSteps C B s T) {k : ℕ}
    (hzero : C s = 0) (hsT : s ≤ T) (hfinal : C T = k) :
    ∃ t, s ≤ t ∧ t ≤ T ∧ C t = k ∧ B t = B T ∧
      ∀ u, s ≤ u → u < t → C u < k := by
  obtain ⟨t,hst,htT,hCt,hbefore⟩ := first_count_hit (k := k) h hzero hsT (by omega)
  exact ⟨t,hst,htT,hCt,
    h.bad_eq_on_count_plateau hst htT le_rfl (hCt.trans hfinal.symm),hbefore⟩

theorem first_bad_hit_cap (h : UnitSteps C B s T) {k : ℕ}
    (hzeroC : C s = 0) (hzeroB : B s = 0) (hsT : s ≤ T)
    (hk : 0 < k) (hbad : k ≤ B T) (hgood : C T-B T < k) :
    ∃ v, s ≤ v ∧ v ≤ T ∧ B v = k ∧ k ≤ C v ∧ C v < 2*k ∧
      ∀ u, s ≤ u → u < v → C u < C v := by
  have hstepB : ∀ u, s ≤ u → u < T → B (u+1) ≤ B u+1 := by
    intro u hsu huT
    obtain ⟨a,b,hC,hB,ha,hba⟩ := h u hsu huT
    omega
  obtain ⟨v,hsv,hvT,hBv,hbefore⟩ := first_unit_hit hstepB hzeroB hsT hbad
  have hdom := h.bad_increment_le le_rfl hsv hvT
  have hgap := h.gap_le hsv hvT le_rfl
  have hlow : k ≤ C v := by omega
  have hhigh : C v < 2*k := by omega
  refine ⟨v,hsv,hvT,hBv,hlow,hhigh,?_⟩
  intro u hsu huv
  have hc := h.count_le hsu (Nat.le_of_lt huv) hvT
  have hb := hbefore u hsu huv
  have hne : C u ≠ C v := by
    intro he
    have hbeq := h.bad_eq_on_count_plateau hsu (Nat.le_of_lt huv) hvT he
    omega
  omega

open TimeTheorem PairLog PairLogAuxiliary LateF6Hazards
open LateF6OriginalLaw PhaseOneDrainStopping

variable {n : ℕ}

theorem label_mem_trace {L K : ℕ} (init : Cfg L K) (ω : Ω L K)
    (t : ℕ) (i : Fin init.card) :
    labelsAt init ω t i ∈ trace init ω t := by
  rw [← labelsAt_config]
  exact Multiset.mem_map.mpr ⟨i,by simp,rfl⟩

theorem prefix_start_strict {init : InputCfg n} {ω : InputLog n}
    {a s T : ℕ} (h : Prefix init ω a s T) : a < s := by
  have hfirst := (exitTime_eq_iff_firstHit init (StageEventSpec.someGE (n := n) 4) ω s).mp
    h.four_start
  have hne : a ≠ s := by
    intro he
    obtain ⟨b,hb,hp⟩ := hfirst.1
    rw [← he] at hb
    have hthree := h.all_three b hb
    omega
  have has := h.start_order
  omega

theorem prefix_before_start_all_three {init : InputCfg n} {ω : InputLog n}
    {a s T : ℕ} (h : Prefix init ω a s T) :
    ∀ i : Fin init.card, (labelsAt init ω (s-1) i).phase.val = 3 := by
  have hstrict := prefix_start_strict h
  have hfirst := (exitTime_eq_iff_firstHit init (StageEventSpec.someGE (n := n) 4) ω s).mp
    h.four_start
  have hwindow := h.window (s-1) (by omega) (by have hsT := h.observed; omega)
  intro i
  have hm := label_mem_trace init ω (s-1) i
  have hlo := (hwindow _ hm).1
  have hnot : ¬ 4 ≤ (labelsAt init ω (s-1) i).phase.val := by
    intro hge
    exact hfirst.2 (s-1) (by omega) ⟨_,hm,hge⟩
  omega

theorem prefix_start_counts_zero {init : InputCfg n} {ω : InputLog n}
    {a s T : ℕ} (h : Prefix init ω a s T) :
    frozenCount (labelsAt init ω s) = 0 ∧
      acceptedCount (labelsAt init ω s) = 0 ∧
      nonclockFrozenCount (labelsAt init ω s) = 0 ∧
      reserveFrozenCount (labelsAt init ω s) = 0 := by
  have hs := prefix_start_strict h
  have he : s-1+1 = s := by omega
  have hthree := prefix_before_start_all_three h
  have hmain := allThree_step_counts_zero (labelsAt init ω (s-1)) hthree (ω ((s-1)+1))
  have hroles := allThree_step_role_counts_zero (labelsAt init ω (s-1)) hthree (ω ((s-1)+1))
  have hstate : labelsAt init ω s =
      stepLabels (labelsAt init ω (s-1)) (ω ((s-1)+1)) := by
    simpa only [he] using labelsAt_succ init ω (s-1)
  rw [hstate]
  exact ⟨hmain.1,hmain.2,hroles.1,hroles.2⟩

theorem prefix_start_bad_counts_zero {init : InputCfg n} {ω : InputLog n}
    {a s T : ℕ} (h : Prefix init ω a s T)
    (C : Bias (PhaseThreeModel.Numeric.hourIndex n) → Prop)
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n+1))) :
    frozenBadCount C (labelsAt init ω s) = 0 ∧
      badSampleCount J (labelsAt init ω s) = 0 := by
  have hzero := prefix_start_counts_zero h
  have hfreeze : frozenBadCount C (labelsAt init ω s) ≤ frozenCount (labelsAt init ω s) :=
    pool_mono _ (FrozenBad C) FrozenMain (fun _ ha => ha.1)
  have hsample : badSampleCount J (labelsAt init ω s) ≤ acceptedCount (labelsAt init ω s) :=
    pool_mono _ (BadSample J) AcceptedReserve (fun _ ha => ha.1)
  omega

end Ripple.PopulationProtocol.ExactMajority.LateSamplingFirstHit
end
