-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockRareDripCharging.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRareDrips
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockShapeFreeze
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockNormalBarrierStarts

/-!
# Charging a sparse chain to actual high-drip interactions

The first appearance of a positive level cannot be a copy from an existing
member of that level. It is an equal-minute drip from the preceding level.
The first appearances of distinct positive levels occur at distinct raw
interactions. Thus the rises k+1 -> k+2 through k+d-1 -> k+d charge d-1
different indicators in RareDrips. The first k -> k+1 rise is uncharged.

All arguments are pathwise on an explicit current phase cap. The guards
in the probabilistic count remain predicates of the preinteraction state.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRareDripCharging

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeScalar
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockEarlyMarkInitialization PhaseThreeClockSeedTails
  PhaseThreeClockShapeFreeze PhaseThreeClockStoppedPassage
  PhaseThreeClockRareDrips PhaseThreeClockNormalBarrierStarts

variable {L K m n : ℕ}

theorem frontCount_antitone_level (f : Fin m → AgentState L K)
    (a b : ℕ) (hab : a ≤ b) : frontCount f b ≤ frontCount f a := by
  apply Finset.card_le_card
  intro i hi
  have hp := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.1, hab.trans hp.2⟩

theorem firstAfter_le_of_hit {P : ℕ → Prop} {s u v : ℕ}
    (hu : StageEventSpec.firstAfter P s u) (hsv : s ≤ v) (hv : P v) :
    u ≤ v := by
  by_contra hnot
  exact hu.2.2 v hsv (lt_of_not_ge hnot) hv

theorem frontCount_zero_at_seed (init : InputCfg n) (ω : InputLog n)
    (s ell : ℕ) (hseed : ω ∈ seedPrefix init s) (hell : 1 ≤ ell) :
    frontCount (virtualLabels init ω s) ell = 0 := by
  unfold frontCount
  rw [aboveSet_at_seedPrefix_eq_empty init ω s ell hseed hell, Finset.card_empty]

theorem frontCount_mono_safe (init : InputCfg n) (C : Finset (Fin init.card))
    (s a b ell : ℕ) (hsa : s ≤ a) (hab : a ≤ b) (hell : 1 ≤ ell)
    (hcap : ell ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (ω : InputLog n) (hsafe : shapeSafeAt init C s b ω) :
    frontCount (virtualLabels init ω a) ell ≤
      frontCount (virtualLabels init ω b) ell := by
  have hmono := frozenFront_mono init C ell 0 s s le_rfl hell hcap ω
    (show a - s ≤ b - s by omega)
  have hsaEq : s + (a - s) = a := Nat.add_sub_of_le hsa
  have hsbEq : s + (b - s) = b := Nat.add_sub_of_le (hsa.trans hab)
  have hsafea : shapeSafeAt init C s (s + (a - s)) ω := by
    rw [hsaEq]
    exact shapeSafeAt_anti init C s a b hab ω hsafe
  have hsafeb : shapeSafeAt init C s (s + (b - s)) ω := by
    simpa only [hsbEq] using hsafe
  have hr :
      (frontCount (virtualLabels init ω a) ell : ℝ) ≤
        (frontCount (virtualLabels init ω b) ell : ℝ) := by
    simpa only [frozenFront,
      frozenShapeCounts_eq_raw init C ell 0 s s (a - s) ω hsafea,
      frozenShapeCounts_eq_raw init C ell 0 s s (b - s) ω hsafeb,
      rawShapeCounts, hsaEq, hsbEq] using hmono
  exact_mod_cast hr

/-- A first positive level is born strictly after the seed, from two
labels whose previous effective minutes are exactly ell-1. -/
theorem first_positive_birth_pair (init : InputCfg n)
    (C : Finset (Fin init.card)) (s ell v : ℕ) (hell : 1 ≤ ell)
    (hcap : ell ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (ω : InputLog n) (hsafe : shapeSafeAt init C s v ω)
    (hfirst : StageEventSpec.firstAfter
      (fun t => 1 ≤ frontCount (virtualLabels init ω t) ell) s v) :
    s < v ∧ ∃ i j,
      drawLabels init ω v = some (i, j) ∧
      i ∈ exactSet (virtualLabels init ω (v - 1)) (ell - 1) ∧
      j ∈ exactSet (virtualLabels init ω (v - 1)) (ell - 1) := by
  classical
  have hsv : s < v := by
    have hz := frontCount_zero_at_seed init ω s ell hsafe.1.1 hell
    have hsle : s ≤ v := hfirst.1
    by_contra hnot
    have he : v = s := by omega
    have hp : 1 ≤ frontCount (virtualLabels init ω v) ell := hfirst.2.1
    rw [he, hz] at hp
    omega
  have hpred : s ≤ v - 1 := by omega
  have hsucc : v - 1 + 1 = v := by omega
  have hzero : frontCount (virtualLabels init ω (v - 1)) ell = 0 := by
    have hn := hfirst.2.2 (v - 1) hpred (by omega)
    omega
  have hstep := front_step_safe init C ell 0 s (v - 1) hpred hell hcap ω
    (by simpa only [hsucc] using hsafe)
  have hone : gatedIndicator init ell (v - 1) ω = 1 := by
    rcases gatedIndicator_zero_one init ell (v - 1) ω with hz | ho
    · rw [hz, hzero, Nat.cast_zero, zero_add, hsucc] at hstep
      have hp : (1 : ℝ) ≤ frontCount (virtualLabels init ω v) ell := by
        exact_mod_cast hfirst.2.1
      linarith
    · exact ho
  have hex : ∃ i j, drawLabels init ω (v - 1 + 1) = some (i, j) ∧
      GatedTick ell (virtualLabels init ω (v - 1)) i j := by
    by_contra hn
    have hz : gatedIndicator init ell (v - 1) ω = 0 := by
      simp only [gatedIndicator, show ¬ ∃ i j,
        drawLabels init ω (v - 1 + 1) = some (i, j) ∧
          GatedTick ell (auxLabels init virtualRule ω (v - 1)) i j from hn,
        if_false]
    rw [hz] at hone
    norm_num at hone
  obtain ⟨i, j, hd, hg⟩ := hex
  refine ⟨hsv, ?_⟩
  rcases hg.1 with hcopy | hcopy | hdrip
  · have hp : 0 < frontCount (virtualLabels init ω (v - 1)) ell :=
      Finset.card_pos.mpr ⟨j, hcopy.2⟩
    omega
  · have hp : 0 < frontCount (virtualLabels init ω (v - 1)) ell :=
      Finset.card_pos.mpr ⟨i, hcopy.1⟩
    omega
  · exact ⟨i, j, by simpa only [hsucc] using hd, hdrip⟩

theorem first_positive_times_strict (init : InputCfg n)
    (C : Finset (Fin init.card)) (s a b u v : ℕ)
    (ha : 1 ≤ a) (hab : a < b)
    (hcap : b ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (ω : InputLog n) (hsafe : shapeSafeAt init C s v ω)
    (hu : StageEventSpec.firstAfter
      (fun t => 1 ≤ frontCount (virtualLabels init ω t) a) s u)
    (hv : StageEventSpec.firstAfter
      (fun t => 1 ≤ frontCount (virtualLabels init ω t) b) s v) :
    u < v := by
  obtain ⟨hsv, i, j, hd, hi, hj⟩ :=
    first_positive_birth_pair init C s b v (by omega) hcap ω hsafe hv
  have hp : i ∈ aboveSet (virtualLabels init ω (v - 1)) a := by
    have hsrc := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    have hm := hsrc.2
    exact ⟨Finset.mem_univ _, hsrc.1, by omega⟩
  have hpos : 1 ≤ frontCount (virtualLabels init ω (v - 1)) a := by
    exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨i, hp⟩)
  have hle := firstAfter_le_of_hit hu (by omega : s ≤ v - 1) hpos
  omega

theorem first_positive_times_mono (init : InputCfg n)
    (s a b u v : ℕ) (hab : a ≤ b) (ω : InputLog n)
    (hu : StageEventSpec.firstAfter
      (fun t => 1 ≤ frontCount (virtualLabels init ω t) a) s u)
    (hv : StageEventSpec.firstAfter
      (fun t => 1 ≤ frontCount (virtualLabels init ω t) b) s v) :
    u ≤ v :=
  firstAfter_le_of_hit hu hv.1
    (hv.2.1.trans (frontCount_antitone_level _ a b hab))

theorem first_positive_birth_charged (init : InputCfg n)
    (C : Finset (Fin init.card)) (s k cutoff B ell v : ℕ)
    (hkell : k + 2 ≤ ell)
    (hcap : ell ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (ω : InputLog n) (hsafe : shapeSafeAt init C s v ω)
    (hfirst : StageEventSpec.firstAfter
      (fun t => 1 ≤ frontCount (virtualLabels init ω t) ell) s v)
    (hlower : frontCount (virtualLabels init ω (v - 1)) k < cutoff)
    (hupper : frontCount (virtualLabels init ω (v - 1)) (k + 1) ≤ B) :
    rareDripIndicator init k cutoff B (v - 1) ω = 1 := by
  classical
  obtain ⟨hsv, i, j, hd, hi, hj⟩ :=
    first_positive_birth_pair init C s ell v (by omega) hcap ω hsafe hfirst
  have hisrc := (Finset.mem_filter.mp hi).2
  have hjsrc := (Finset.mem_filter.mp hj).2
  have him := hisrc.2
  have hjm := hjsrc.2
  have hp : SparseHighDrip (virtualLabels init ω (v - 1)) k cutoff B i j := by
    refine ⟨hlower, hupper, ?_, ?_, hisrc.2.trans hjsrc.2.symm, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hisrc.1, by omega⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjsrc.1, by omega⟩
    · change effMinute (virtualLabels init ω (v - 1) i) <
        256 * (PhaseThreeModel.Numeric.hourIndex n + 1)
      omega
  unfold rareDripIndicator
  apply if_pos
  exact ⟨i, j, by simpa only [show v - 1 + 1 = v by omega] using hd, hp⟩

/-- The d-1 charged maximum increases occur at different selected
interactions, all inside the actual raw count interval. -/
theorem rareDripCount_ge_of_first_hits (init : InputCfg n)
    (C : Finset (Fin init.card)) (s k d cutoff B N : ℕ)
    (hk : 1 ≤ k) (hd : 2 ≤ d)
    (hcap : k + d ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (f : ℕ → ℕ) (ω : InputLog n)
    (hfirst : ∀ ell, k ≤ ell → ell ≤ k + d →
      StageEventSpec.firstAfter
        (fun t => 1 ≤ frontCount (virtualLabels init ω t) ell) s (f ell))
    (hsafe : shapeSafeAt init C s (f (k + d)) ω)
    (horizon : f (k + d) ≤ f k + N)
    (hguard : ∀ t, f k ≤ t → t < f (k + d) →
      frontCount (virtualLabels init ω t) k < cutoff ∧
        frontCount (virtualLabels init ω t) (k + 1) ≤ B) :
    ((d - 1 : ℕ) : ℝ) ≤ rareDripCount init k cutoff B (f k) N ω := by
  classical
  let level : ℕ → ℕ := fun q => k + q + 2
  let index : ℕ → ℕ := fun q => f (level q) - f k - 1
  let J : Finset ℕ := (Finset.range (d - 1)).image index
  have hlevels (q : ℕ) (hq : q ∈ Finset.range (d - 1)) :
      k + 2 ≤ level q ∧ level q ≤ k + d := by
    have hq' := Finset.mem_range.mp hq
    dsimp only [level]
    omega
  have htimes (q : ℕ) (hq : q ∈ Finset.range (d - 1)) :
      f k < f (level q) ∧ f (level q) ≤ f (k + d) := by
    have hlev := hlevels q hq
    have hright := first_positive_times_mono init s (level q) (k + d)
      (f (level q)) (f (k + d)) hlev.2 ω
      (hfirst _ (by omega) hlev.2) (hfirst _ (by omega) le_rfl)
    have hsafeq := shapeSafeAt_anti init C s _ _ hright ω hsafe
    exact ⟨first_positive_times_strict init C s k (level q) (f k) (f (level q))
      hk (by omega) (hlev.2.trans hcap) ω hsafeq
      (hfirst k le_rfl (by omega)) (hfirst _ (by omega) hlev.2), hright⟩
  have hindex (q : ℕ) (hq : q ∈ Finset.range (d - 1)) :
      index q < N ∧ f k + index q = f (level q) - 1 := by
    have ht := htimes q hq
    dsimp only [index]
    omega
  have hinj : Set.InjOn index (↑(Finset.range (d - 1)) : Set ℕ) := by
    intro a ha b hb he
    have hat := htimes a ha
    have hbt := htimes b hb
    have hai := hindex a ha
    have hbi := hindex b hb
    have hfeq : f (level a) = f (level b) := by omega
    rcases lt_trichotomy a b with hab | hab | hab
    · have hlab : level a < level b := by dsimp only [level]; omega
      have hsafeb := shapeSafeAt_anti init C s _ _ hbt.2 ω hsafe
      have hlt := first_positive_times_strict init C s (level a) (level b)
        (f (level a)) (f (level b)) (by have := hlevels a ha; omega) hlab
        ((hlevels b hb).2.trans hcap) ω hsafeb
        (hfirst _ (by have := hlevels a ha; omega) (hlevels a ha).2)
        (hfirst _ (by have := hlevels b hb; omega) (hlevels b hb).2)
      omega
    · exact hab
    · have hlba : level b < level a := by dsimp only [level]; omega
      have hsafea := shapeSafeAt_anti init C s _ _ hat.2 ω hsafe
      have hlt := first_positive_times_strict init C s (level b) (level a)
        (f (level b)) (f (level a)) (by have := hlevels b hb; omega) hlba
        ((hlevels a ha).2.trans hcap) ω hsafea
        (hfirst _ (by have := hlevels b hb; omega) (hlevels b hb).2)
        (hfirst _ (by have := hlevels a ha; omega) (hlevels a ha).2)
      omega
  have hcard : J.card = d - 1 := by
    dsimp only [J]
    rw [Finset.card_image_iff.mpr hinj, Finset.card_range]
  have hsub : J ⊆ Finset.range N := by
    intro t ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_range.mpr (hindex q hq).1
  have hone (t : ℕ) (ht : t ∈ J) :
      rareDripIndicator init k cutoff B (f k + t) ω = 1 := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
    rw [(hindex q hq).2]
    have ht := htimes q hq
    have hg := hguard (f (level q) - 1) (by omega) (by omega)
    exact first_positive_birth_charged init C s k cutoff B (level q) (f (level q))
      (hlevels q hq).1 ((hlevels q hq).2.trans hcap) ω
      (shapeSafeAt_anti init C s _ _ ht.2 ω hsafe)
      (hfirst _ (by have := hlevels q hq; omega) (hlevels q hq).2) hg.1 hg.2
  have hnonneg (t : ℕ) : 0 ≤ rareDripIndicator init k cutoff B (f k + t) ω := by
    rcases rareDripIndicator_zero_one init k cutoff B (f k + t) ω with h | h <;>
      simp only [h] <;> norm_num
  calc
    ((d - 1 : ℕ) : ℝ) = (J.card : ℝ) := by rw [hcard]
    _ = ∑ t ∈ J, rareDripIndicator init k cutoff B (f k + t) ω := by
      simp only [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ t ∈ Finset.range N, rareDripIndicator init k cutoff B (f k + t) ω :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hnonneg t)
    _ = _ := rfl

theorem first_threshold_count_eq (init : InputCfg n)
    (C : Finset (Fin init.card)) (s ell b v : ℕ)
    (hell : 1 ≤ ell) (hb : 1 ≤ b)
    (hcap : ell ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (ω : InputLog n) (hsafe : shapeSafeAt init C s v ω)
    (hfirst : StageEventSpec.firstAfter
      (fun t => b ≤ frontCount (virtualLabels init ω t) ell) s v) :
    frontCount (virtualLabels init ω v) ell = b := by
  have hsv : s < v := by
    have hz := frontCount_zero_at_seed init ω s ell hsafe.1.1 hell
    have hsle : s ≤ v := hfirst.1
    by_contra hnot
    have he : v = s := by omega
    have hp : b ≤ frontCount (virtualLabels init ω v) ell := hfirst.2.1
    rw [he, hz] at hp
    omega
  have hpred : s ≤ v - 1 := by omega
  have hsucc : v - 1 + 1 = v := by omega
  have hsmall : frontCount (virtualLabels init ω (v - 1)) ell < b := by
    have hn := hfirst.2.2 (v - 1) hpred (by omega)
    omega
  have hstep := front_step_safe init C ell 0 s (v - 1) hpred hell hcap ω
    (by simpa only [hsucc] using hsafe)
  have hIle : gatedIndicator init ell (v - 1) ω ≤ 1 := by
    rcases gatedIndicator_zero_one init ell (v - 1) ω with h | h <;>
      simp only [h] <;> norm_num
  have hsmallR : (frontCount (virtualLabels init ω (v - 1)) ell : ℝ) + 1 ≤ b := by
    exact_mod_cast (Nat.succ_le_iff.mpr hsmall)
  have hupper : (frontCount (virtualLabels init ω v) ell : ℝ) ≤ b := by
    rw [hsucc] at hstep
    linarith
  exact Nat.le_antisymm (by exact_mod_cast hupper) hfirst.2.1

/-- An earlier shape assertion at the first w-hit gives the predictable
sparse upper-front guard at every preceding time. The target w-hit is
obtained from the genuine finite bulk hit, not postulated. -/
theorem sparse_upper_guard_of_earlier_shape (init : InputCfg n)
    (C : Finset (Fin init.card)) (s k w b v tau : ℕ)
    (hC : 0 < C.card) (hk : 1 ≤ k) (hw : 1 ≤ w) (hwb : w ≤ b)
    (hcap : k + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (ω : InputLog n) (hsv : s ≤ v)
    (hsafe : shapeSafeAt init C s (max v tau) ω)
    (hbulk : StageEventSpec.firstAfter
      (fun t => b ≤ frontCount (virtualLabels init ω t) k) s tau)
    (hshape : ∀ t, s ≤ t → t ≤ tau →
      w ≤ frontCount (virtualLabels init ω t) k →
      frontCount (virtualLabels init ω t) k ≤ b →
      C.card * frontCount (virtualLabels init ω t) (k + 1) ≤
        frontCount (virtualLabels init ω t) k ^ 2)
    (hsmall : frontCount (virtualLabels init ω v) k < w) :
    v < tau ∧ ∀ t, s ≤ t → t ≤ v →
      frontCount (virtualLabels init ω t) (k + 1) ≤ w ^ 2 / C.card := by
  have hsafev := shapeSafeAt_anti init C s v (max v tau) (le_max_left _ _) ω hsafe
  have hsafetau := shapeSafeAt_anti init C s tau (max v tau) (le_max_right _ _) ω hsafe
  have hvtau : v < tau := by
    by_contra hnot
    have hm := frontCount_mono_safe init C s tau v k hbulk.1
      (by omega) hk (by omega) ω hsafev
    have hb2 : b ≤ frontCount (virtualLabels init ω tau) k := hbulk.2.1
    omega
  obtain ⟨u, hutau, hu⟩ :=
    exists_earlyCutoffFibre init s k w tau ω hbulk.1 (hwb.trans hbulk.2.1)
  have hfirst : StageEventSpec.firstAfter
      (fun t => w ≤ frontCount (virtualLabels init ω t) k) s u :=
    ⟨hu.1, hu.2.1, fun t hst htu => not_le_of_gt (hu.2.2 t hst htu)⟩
  have hsafeu := shapeSafeAt_anti init C s u tau hutau ω hsafetau
  have hwu := first_threshold_count_eq init C s k w u hk hw (by omega) ω hsafeu hfirst
  have hvu : v < u := by
    by_contra hnot
    have hm := frontCount_mono_safe init C s u v k hu.1 (by omega) hk
      (by omega) ω hsafev
    rw [hwu] at hm
    omega
  have hshapeu := hshape u hu.1 hutau (by omega) (by omega)
  rw [hwu] at hshapeu
  have hubound :
      frontCount (virtualLabels init ω u) (k + 1) ≤ w ^ 2 / C.card := by
    apply (Nat.le_div_iff_mul_le hC).mpr
    simpa only [Nat.mul_comm] using hshapeu
  refine ⟨hvtau, ?_⟩
  intro t hst htv
  exact (frontCount_mono_safe init C s t u (k + 1) hst
    (by omega) (by omega) hcap ω hsafeu).trans hubound

/-- On the earlier k-shape and k-raw-horizon events, a sparse first
appearance of level k+d is included in the actual rare-drip count tail.
No future-success event is used in the count's conditional law. -/
theorem sparse_chain_implies_rare_count (init : InputCfg n)
    (C : Finset (Fin init.card)) (s k d w b N : ℕ)
    (hC : 0 < C.card) (hk : 1 ≤ k) (hd : 2 ≤ d)
    (hw : 1 ≤ w) (hwb : w ≤ b)
    (hcap : k + d ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (f : ℕ → ℕ) (tau : ℕ) (ω : InputLog n)
    (hfirst : ∀ ell, k ≤ ell → ell ≤ k + d →
      StageEventSpec.firstAfter
        (fun t => 1 ≤ frontCount (virtualLabels init ω t) ell) s (f ell))
    (hsafe : shapeSafeAt init C s (max (f (k + d)) tau) ω)
    (hbulk : StageEventSpec.firstAfter
      (fun t => b ≤ frontCount (virtualLabels init ω t) k) s tau)
    (hshape : ∀ t, s ≤ t → t ≤ tau →
      w ≤ frontCount (virtualLabels init ω t) k →
      frontCount (virtualLabels init ω t) k ≤ b →
      C.card * frontCount (virtualLabels init ω t) (k + 1) ≤
        frontCount (virtualLabels init ω t) k ^ 2)
    (horizon : tau ≤ f k + N)
    (hsmall : frontCount (virtualLabels init ω (f (k + d))) k < w) :
    ((d - 1 : ℕ) : ℝ) ≤
      rareDripCount init k w (w ^ 2 / C.card) (f k) N ω := by
  have hend := hfirst (k + d) (by omega) le_rfl
  have hguards := sparse_upper_guard_of_earlier_shape
    init C s k w b (f (k + d)) tau hC hk hw hwb (by omega) ω hend.1
      hsafe hbulk hshape hsmall
  have hsafeEnd := shapeSafeAt_anti init C s (f (k + d)) _
    (le_max_left _ _) ω hsafe
  apply rareDripCount_ge_of_first_hits init C s k d w (w ^ 2 / C.card) N
    hk hd hcap f ω hfirst hsafeEnd (by omega)
  intro t hstart ht
  have hst := (hfirst k le_rfl (by omega)).1.trans hstart
  refine ⟨?_, hguards.2 t hst ht.le⟩
  exact (frontCount_mono_safe init C s t (f (k + d)) k hst ht.le hk
    (by omega) ω hsafeEnd).trans_lt hsmall

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRareDripCharging

end
