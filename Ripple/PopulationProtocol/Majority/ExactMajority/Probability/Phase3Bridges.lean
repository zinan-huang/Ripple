import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase3Core
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourCoupling
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Lemma613OFloor
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockStoppedTransfer
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Lemma617Minority
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealMixed
import Mathlib.Tactic

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Real

namespace Phase3Bridges

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

local instance instOptionMSPhase3Bridges :
    MeasurableSpace (Option (Phase3Core.Omega L K)) := ⊤

local instance instOptionDMSPhase3Bridges :
    DiscreteMeasurableSpace (Option (Phase3Core.Omega L K)) :=
  ⟨fun _ => trivial⟩

/-!
Slot-3 piece 6 bridge layer.

This file keeps the probabilistic bridge obligations stopped.  The generic
`CatalyticPull` section is the killed-chain milestone interface needed for
Lemma 6.13's catalytic pull.  The `H13Bridge` and `H14Bridge` sections then turn
lower stopped tails into the exact `Phase3Core` producer fields.
-/

/-! ## Generic stopped-tail bookkeeping -/

theorem stoppedTail_mono {G : Set (Phase3Core.Omega L K)} {t : ℕ}
    {x : Phase3Core.Omega L K} {Bad Bad' : Phase3Core.Omega L K → Prop}
    {ε : ℝ≥0∞}
    (hsub : ∀ c, Bad c → Bad' c)
    (h : Phase3Core.stoppedTail (L := L) (K := K) G t x Bad' ε) :
    Phase3Core.stoppedTail (L := L) (K := K) G t x Bad ε := by
  unfold Phase3Core.stoppedTail at h ⊢
  exact (measure_mono (by
    intro o ho
    rcases ho with hnone | ⟨c, rfl, hbad⟩
    · exact Or.inl hnone
    · exact Or.inr ⟨c, rfl, hsub c hbad⟩)).trans h

theorem stoppedTail_union {G : Set (Phase3Core.Omega L K)} {t : ℕ}
    {x : Phase3Core.Omega L K} {Bad₁ Bad₂ Bad : Phase3Core.Omega L K → Prop}
    {ε₁ ε₂ ε : ℝ≥0∞}
    (h₁ : Phase3Core.stoppedTail (L := L) (K := K) G t x Bad₁ ε₁)
    (h₂ : Phase3Core.stoppedTail (L := L) (K := K) G t x Bad₂ ε₂)
    (hbad : ∀ c, Bad c → Bad₁ c ∨ Bad₂ c)
    (hbudget : ε₁ + ε₂ ≤ ε) :
    Phase3Core.stoppedTail (L := L) (K := K) G t x Bad ε := by
  unfold Phase3Core.stoppedTail at h₁ h₂ ⊢
  have hsub :
      Phase3Core.killedBad Bad ⊆
        Phase3Core.killedBad Bad₁ ∪ Phase3Core.killedBad Bad₂ := by
    intro o ho
    rcases ho with hnone | ⟨c, rfl, hc⟩
    · exact Or.inl (Or.inl hnone)
    · rcases hbad c hc with hbad₁ | hbad₂
      · exact Or.inl (Or.inr ⟨c, rfl, hbad₁⟩)
      · exact Or.inr (Or.inr ⟨c, rfl, hbad₂⟩)
  calc
    (GatedDrift.killK_now (Phase3Core.phase3Kernel L K) G ^ t) (some x)
        (Phase3Core.killedBad Bad)
        ≤ (GatedDrift.killK_now (Phase3Core.phase3Kernel L K) G ^ t) (some x)
            (Phase3Core.killedBad Bad₁ ∪ Phase3Core.killedBad Bad₂) :=
          measure_mono hsub
    _ ≤ (GatedDrift.killK_now (Phase3Core.phase3Kernel L K) G ^ t) (some x)
            (Phase3Core.killedBad Bad₁) +
          (GatedDrift.killK_now (Phase3Core.phase3Kernel L K) G ^ t) (some x)
            (Phase3Core.killedBad Bad₂) :=
          measure_union_le _ _
    _ ≤ ε₁ + ε₂ := add_le_add h₁ h₂
    _ ≤ ε := hbudget

/-- Convert a real-kernel bad-tail and a cemetery/exit bound into the Core
immediate-kill stopped-tail shape.  The killed target is split into `none` plus
alive bad states; the alive part is dominated by the real kernel. -/
theorem stoppedTail_of_real_tail_add_exit {G : Set (Phase3Core.Omega L K)} {t : ℕ}
    {x : Phase3Core.Omega L K} {Bad : Phase3Core.Omega L K → Prop}
    {εExit εBad ε : ℝ≥0∞}
    (hexit :
      (GatedDrift.killK_now (Phase3Core.phase3Kernel L K) G ^ t)
        (some x) {(none : Option (Phase3Core.Omega L K))} ≤ εExit)
    (hreal :
      (Phase3Core.phase3Kernel L K ^ t) x {y | Bad y} ≤ εBad)
    (hbudget : εExit + εBad ≤ ε) :
    Phase3Core.stoppedTail (L := L) (K := K) G t x Bad ε := by
  classical
  let μ : Measure (Option (Phase3Core.Omega L K)) :=
    (GatedDrift.killK_now (Phase3Core.phase3Kernel L K) G ^ t) (some x)
  let AliveBad : Set (Option (Phase3Core.Omega L K)) :=
    {o | ∃ y ∈ ({y | Bad y} : Set (Phase3Core.Omega L K)), o = some y}
  have hsplit :
      Phase3Core.killedBad Bad ⊆
        {(none : Option (Phase3Core.Omega L K))} ∪ AliveBad := by
    intro o ho
    rcases ho with hnone | ⟨y, hy, hbad⟩
    · exact Or.inl hnone
    · exact Or.inr ⟨y, hbad, hy⟩
  have halive :
      μ AliveBad ≤ (Phase3Core.phase3Kernel L K ^ t) x {y | Bad y} := by
    simpa [μ, AliveBad] using
      GatedDrift.killed_now_alive_le_real
        (K := Phase3Core.phase3Kernel L K) (G := G)
        ({y | Bad y} : Set (Phase3Core.Omega L K)) t x
  unfold Phase3Core.stoppedTail
  calc
    μ (Phase3Core.killedBad Bad)
        ≤ μ ({(none : Option (Phase3Core.Omega L K))} ∪ AliveBad) :=
          measure_mono hsplit
    _ ≤ μ {(none : Option (Phase3Core.Omega L K))} + μ AliveBad :=
          measure_union_le _ _
    _ ≤ εExit + εBad := add_le_add (by simpa [μ] using hexit) (halive.trans hreal)
    _ ≤ ε := hbudget

/-! ## Immediate-kill to self-loop stopped transfer -/

section KillNowSupport

open GatedDrift

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Inhabited α]

local instance instOptionMSKillNowSupport : MeasurableSpace (Option α) := ⊤
local instance instOptionDMSKillNowSupport : DiscreteMeasurableSpace (Option α) :=
  ⟨fun _ => trivial⟩

/-- If an immediate-killed walk starts inside `G`, its alive mass never lands
outside `G`.  The cemetery carries all off-gate successors. -/
theorem kill_now_alive_outside_gate_zero
    (K : Kernel α α) [IsMarkovKernel K] (G : Set α)
    (t : ℕ) {x : α} (hx : x ∈ G) :
    (GatedDrift.killK_now K G ^ t) (some x)
      {o | ∃ y, y ∉ G ∧ o = some y} = 0 := by
  classical
  induction t generalizing x with
  | zero =>
      rw [pow_zero]
      change (Kernel.id (some x))
          {o | ∃ y, y ∉ G ∧ o = some y} = 0
      rw [Kernel.id_apply,
        Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
      have hnot : (some x : Option α) ∉ {o | ∃ y, y ∉ G ∧ o = some y} := by
        rintro ⟨y, hyG, hxy⟩
        exact hyG ((Option.some.inj hxy).symm ▸ hx)
      rw [Set.indicator_of_notMem hnot]
  | succ t ih =>
      let A : Set (Option α) := {o | ∃ y, y ∉ G ∧ o = some y}
      have hA : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
      rw [show t + 1 = 1 + t by omega,
        Kernel.pow_add_apply_eq_lintegral (GatedDrift.killK_now K G) 1 t (some x) hA,
        pow_one, GatedDrift.killK_now_some_gated (K := K) (G := G) x hx,
        MeasureTheory.lintegral_map (Measurable.of_discrete) (GatedDrift.gateMap_measurable G)]
      have hzero :
          (fun y => (GatedDrift.killK_now K G ^ t) (GatedDrift.gateMap G y) A)
            = fun _ => 0 := by
        funext y
        unfold GatedDrift.gateMap
        by_cases hy : y ∈ G
        · rw [if_pos hy]
          exact ih hy
        · rw [if_neg hy, GatedDrift.none_absorbing_now (K := K) (G := G) t,
            Measure.dirac_apply' _ hA]
          have hnone : (none : Option α) ∉ A := by
            rintro ⟨z, _, hz⟩
            cases hz
          rw [Set.indicator_of_notMem hnone]
      rw [hzero]
      simp

/-- The alive bad part of `killK_now` is bounded by the corresponding ordinary
self-loop stopped kernel, after restricting the alive support to `G`. -/
theorem kill_now_alive_bad_le_stopped_on_gate
    (K : Kernel α α) [IsMarkovKernel K] (G : Set α)
    {bad az : α → Prop}
    (hsub : ∀ y, y ∈ G → bad y → az y)
    (t : ℕ) {x : α} (hx : x ∈ G) :
    (GatedDrift.killK_now K G ^ t) (some x)
        {o | ∃ y, o = some y ∧ bad y}
      ≤ (ClockStoppedTransfer.stoppedK K G ^ t) x {y | az y} := by
  classical
  let AliveBad : Set (Option α) := {o | ∃ y, o = some y ∧ bad y}
  let AliveGateBad : Set (Option α) := {o | ∃ y, y ∈ G ∧ bad y ∧ o = some y}
  let AliveOutside : Set (Option α) := {o | ∃ y, y ∉ G ∧ o = some y}
  let AliveAz : Set (Option α) := {o | ∃ y ∈ ({y | az y} : Set α), o = some y}
  have hcover : AliveBad ⊆ AliveGateBad ∪ AliveOutside := by
    intro o ho
    rcases ho with ⟨y, hoy, hybad⟩
    by_cases hyG : y ∈ G
    · exact Or.inl ⟨y, hyG, hybad, hoy⟩
    · exact Or.inr ⟨y, hyG, hoy⟩
  have hgate_sub : AliveGateBad ⊆ AliveAz := by
    intro o ho
    rcases ho with ⟨y, hyG, hybad, hoy⟩
    exact ⟨y, hsub y hyG hybad, hoy⟩
  have hout :
      (GatedDrift.killK_now K G ^ t) (some x) AliveOutside = 0 := by
    simpa [AliveOutside] using
      kill_now_alive_outside_gate_zero (K := K) (G := G) t hx
  calc
    (GatedDrift.killK_now K G ^ t) (some x) AliveBad
        ≤ (GatedDrift.killK_now K G ^ t) (some x)
            (AliveGateBad ∪ AliveOutside) :=
          measure_mono hcover
    _ ≤ (GatedDrift.killK_now K G ^ t) (some x) AliveGateBad +
          (GatedDrift.killK_now K G ^ t) (some x) AliveOutside :=
          measure_union_le _ _
    _ = (GatedDrift.killK_now K G ^ t) (some x) AliveGateBad := by
          rw [hout, add_zero]
    _ ≤ (GatedDrift.killK_now K G ^ t) (some x) AliveAz :=
          measure_mono hgate_sub
    _ ≤ (ClockStoppedTransfer.stoppedK K G ^ t) x {y | az y} := by
          simpa [AliveAz] using
            ClockStoppedTransfer.killed_now_alive_le_stopped
              (K := K) (G := G) ({y | az y} : Set α) t x

end KillNowSupport

/-! ## Lemma 6.13 deterministic target split -/

def ReachedMainFloor (D : Phase3Core.Phase3ModeDomain L) (h : ℕ)
    (c : Phase3Core.Omega L K) : Prop :=
  (97 / 100 : ℝ) * (D.M : ℝ) ≤
    (Lemma613OFloor.phase3ReachedMainCount (L := L) (K := K) h c : ℝ)

def BiasedMainBound (D : Phase3Core.Phase3ModeDomain L) (rho : ℝ)
    (c : Phase3Core.Omega L K) : Prop :=
  (Lemma613OFloor.phase3BiasedMainCount (L := L) (K := K) c : ℝ) ≤
    2 * rho * (D.M : ℝ)

theorem ofuelFloor_of_reached_biased
    (D : Phase3Core.Phase3ModeDomain L) (h : ℕ) (rho : ℝ)
    (c : Phase3Core.Omega L K)
    (hcoef : D.tau h ≤ 97 / 100 - 2 * rho)
    (hReach : ReachedMainFloor (L := L) (K := K) D h c)
    (hBiased : BiasedMainBound (L := L) (K := K) D rho c) :
    Phase3Core.OFuelFloor (L := L) (K := K) D h c := by
  have hfloor :=
    Lemma613OFloor.ofuel_floor (L := L) (K := K) h rho (D.M : ℝ) c
      hReach hBiased
  have hcoefM :
      D.tau h * (D.M : ℝ) ≤ (97 / 100 - 2 * rho) * (D.M : ℝ) :=
    mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg D.M)
  exact hcoefM.trans hfloor

theorem stoppedTail_ofuelFloor_of_reached_biased
    {D : Phase3Core.Phase3ModeDomain L} {G : Set (Phase3Core.Omega L K)}
    {t : ℕ} {x : Phase3Core.Omega L K} {h : ℕ} {rho : ℝ}
    {εReach εBiased ε : ℝ≥0∞}
    (hcoef : D.tau h ≤ 97 / 100 - 2 * rho)
    (hReach :
      Phase3Core.stoppedTail (L := L) (K := K) G t x
        (fun c => ¬ ReachedMainFloor (L := L) (K := K) D h c) εReach)
    (hBiased :
      Phase3Core.stoppedTail (L := L) (K := K) G t x
        (fun c => ¬ BiasedMainBound (L := L) (K := K) D rho c) εBiased)
    (hbudget : εReach + εBiased ≤ ε) :
    Phase3Core.stoppedTail (L := L) (K := K) G t x
      (fun c => ¬ Phase3Core.OFuelFloor (L := L) (K := K) D h c) ε := by
  refine stoppedTail_union (L := L) (K := K) hReach hBiased ?_ hbudget
  intro c hnot
  by_cases hR : ReachedMainFloor (L := L) (K := K) D h c
  · by_cases hB : BiasedMainBound (L := L) (K := K) D rho c
    · exact False.elim (hnot (ofuelFloor_of_reached_biased
        (L := L) (K := K) D h rho c hcoef hR hB))
    · exact Or.inr hB
  · exact Or.inl hR

namespace CatalyticPull

noncomputable def catalyticPullRate (n a₀ i : ℕ) : ℝ :=
  (2 : ℝ) * (a₀ : ℝ) * (i : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))

end CatalyticPull

/-! ## Lemma 6.13 catalytic-pull scheduler rectangle -/

def LaggingO (h : ℕ) (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ a.bias = Bias.zero ∧ a.hour.val < h

instance (h : ℕ) (a : AgentState L K) :
    Decidable (LaggingO (L := L) (K := K) h a) := by
  unfold LaggingO
  infer_instance

def laggingOCount (h : ℕ) (c : Phase3Core.Omega L K) : ℕ :=
  Multiset.countP (fun a => LaggingO (L := L) (K := K) h a) c

noncomputable def clockFrontAt (h : ℕ) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a =>
    Phase3GoodClock.clockAtOrBeyondHourP (L := L) (K := K) h a)

noncomputable def laggingOAt (h : ℕ) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => LaggingO (L := L) (K := K) h a)

noncomputable def h13PullRect (h : ℕ) :
    Finset (AgentState L K × AgentState L K) :=
  (clockFrontAt (L := L) (K := K) h ×ˢ laggingOAt (L := L) (K := K) h) ∪
    (laggingOAt (L := L) (K := K) h ×ˢ clockFrontAt (L := L) (K := K) h)

def h13PullPairs (c : Phase3Core.Omega L K) (h : ℕ) :
    Set (AgentState L K × AgentState L K) :=
  {p | p ∈ h13PullRect (L := L) (K := K) h ∧
    Protocol.Applicable c p.1 p.2}

private lemma applicable_of_pos_iCount_h13 (c : Phase3Core.Omega L K)
    (s₁ s₂ : AgentState L K) (h : 0 < c.interactionCount s₁ s₂) :
    Protocol.Applicable c s₁ s₂ := by
  change {s₁, s₂} ≤ c
  rw [Multiset.le_iff_count]
  intro a
  simp only [Config.interactionCount, Config.count] at h
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  by_cases heq : s₁ = s₂
  · subst heq
    simp only [ite_true] at h
    have htwo : 2 ≤ Multiset.count s₁ c := by
      by_contra hlt
      have hle : Multiset.count s₁ c ≤ 1 := by omega
      have hzero : Multiset.count s₁ c * (Multiset.count s₁ c - 1) = 0 := by
        rcases Nat.eq_zero_or_pos (Multiset.count s₁ c) with h0 | hpos
        · simp [h0]
        · have hone : Multiset.count s₁ c = 1 := by omega
          simp [hone]
      omega
    by_cases ha : a = s₁ <;> simp_all
  · simp only [heq, ite_false] at h
    have hc1 : 0 < Multiset.count s₁ c := pos_of_mul_pos_left h (Nat.zero_le _)
    have hc2 : 0 < Multiset.count s₂ c := pos_of_mul_pos_right h (Nat.zero_le _)
    by_cases ha1 : a = s₁ <;> by_cases ha2 : a = s₂ <;> simp_all <;> omega

private theorem clockFrontAt_laggingOAt_disjoint
    (h : ℕ) (a : AgentState L K)
    (haC : a ∈ clockFrontAt (L := L) (K := K) h)
    (haO : a ∈ laggingOAt (L := L) (K := K) h) :
    False := by
  rw [clockFrontAt, Finset.mem_filter] at haC
  rw [laggingOAt, Finset.mem_filter] at haO
  have hrole : Role.main = Role.clock := haO.2.1.symm.trans haC.2.1
  cases hrole

private theorem h13PullRect_orientations_disjoint (h : ℕ) :
    Disjoint
      (clockFrontAt (L := L) (K := K) h ×ˢ laggingOAt (L := L) (K := K) h)
      (laggingOAt (L := L) (K := K) h ×ˢ clockFrontAt (L := L) (K := K) h) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpA hpB
  rw [Finset.mem_product] at hpA hpB
  exact clockFrontAt_laggingOAt_disjoint (L := L) (K := K) h p.1 hpA.1 hpB.1

private theorem clockFrontAt_sum_count
    (h : ℕ) (c : Phase3Core.Omega L K) :
    (clockFrontAt (L := L) (K := K) h).sum c.count =
      Phase3GoodClock.hourFront (L := L) (K := K) h c := by
  unfold clockFrontAt Phase3GoodClock.hourFront
  rw [HourCouplingAzuma.countP_eq_sum_count
    (L := L) (K := K)
    (fun a => Phase3GoodClock.clockAtOrBeyondHourP (L := L) (K := K) h a) c]

private theorem laggingOAt_sum_count
    (h : ℕ) (c : Phase3Core.Omega L K) :
    (laggingOAt (L := L) (K := K) h).sum c.count =
      laggingOCount (L := L) (K := K) h c := by
  unfold laggingOAt laggingOCount
  rw [HourCouplingAzuma.countP_eq_sum_count
    (L := L) (K := K)
    (fun a => LaggingO (L := L) (K := K) h a) c]

private theorem h13Pull_orientation_interactionCount
    (h : ℕ) (c : Phase3Core.Omega L K) :
    (∑ p ∈ clockFrontAt (L := L) (K := K) h ×ˢ
          laggingOAt (L := L) (K := K) h,
        c.interactionCount p.1 p.2)
      = Phase3GoodClock.hourFront (L := L) (K := K) h c *
          laggingOCount (L := L) (K := K) h c := by
  classical
  rw [← clockFrontAt_sum_count (L := L) (K := K) h c,
    ← laggingOAt_sum_count (L := L) (K := K) h c]
  exact ClockRealMixed.sum_interactionCount_cross_disjoint
    (L := L) (K := K) c
    (clockFrontAt (L := L) (K := K) h)
    (laggingOAt (L := L) (K := K) h)
    (fun a ha b hb hEq =>
      clockFrontAt_laggingOAt_disjoint (L := L) (K := K) h b
        (by simpa [hEq] using ha) hb)

private theorem h13Pull_orientation_interactionCount_symm
    (h : ℕ) (c : Phase3Core.Omega L K) :
    (∑ p ∈ laggingOAt (L := L) (K := K) h ×ˢ
          clockFrontAt (L := L) (K := K) h,
        c.interactionCount p.1 p.2)
      = laggingOCount (L := L) (K := K) h c *
          Phase3GoodClock.hourFront (L := L) (K := K) h c := by
  classical
  rw [← laggingOAt_sum_count (L := L) (K := K) h c,
    ← clockFrontAt_sum_count (L := L) (K := K) h c]
  exact ClockRealMixed.sum_interactionCount_cross_disjoint
    (L := L) (K := K) c
    (laggingOAt (L := L) (K := K) h)
    (clockFrontAt (L := L) (K := K) h)
    (fun a ha b hb hEq =>
      clockFrontAt_laggingOAt_disjoint (L := L) (K := K) h b hb
        (by simpa [hEq] using ha))

private theorem h13PullRect_interactionCount
    (h : ℕ) (c : Phase3Core.Omega L K) :
    (∑ p ∈ h13PullRect (L := L) (K := K) h, c.interactionCount p.1 p.2)
      = 2 * Phase3GoodClock.hourFront (L := L) (K := K) h c *
          laggingOCount (L := L) (K := K) h c := by
  classical
  unfold h13PullRect
  rw [Finset.sum_union (h13PullRect_orientations_disjoint (L := L) (K := K) h)]
  rw [h13Pull_orientation_interactionCount (L := L) (K := K) h c,
    h13Pull_orientation_interactionCount_symm (L := L) (K := K) h c]
  ring

private theorem phase3_h13_interactionProb_ge
    (h n : ℕ) (c : Phase3Core.Omega L K)
    (hcard : c.card = n) (hn : 2 ≤ n) :
    ENNReal.ofReal
        (((2 * Phase3GoodClock.hourFront (L := L) (K := K) h c *
            laggingOCount (L := L) (K := K) h c : ℕ) : ℝ) /
          ((n : ℝ) * (n - 1 : ℕ)))
      ≤ (c.interactionPMF (by rw [hcard]; exact hn)).toMeasure
          (h13PullPairs (L := L) (K := K) c h) := by
  classical
  let R := h13PullRect (L := L) (K := K) h
  have hc2 : 2 ≤ c.card := by rw [hcard]; exact hn
  have hsupport_subset :
      (↑R : Set (AgentState L K × AgentState L K)) ∩
          (c.interactionPMF hc2).support
        ⊆ h13PullPairs (L := L) (K := K) c h := by
    intro p hp
    obtain ⟨hpR, hpsupp⟩ := hp
    rw [PMF.mem_support_iff] at hpsupp
    have happ : Protocol.Applicable c p.1 p.2 := by
      apply applicable_of_pos_iCount_h13 (L := L) (K := K)
      by_contra hzero
      exact hpsupp (by
        change c.interactionProb p.1 p.2 = 0
        unfold Config.interactionProb
        rw [show c.interactionCount p.1 p.2 = 0 by omega]
        simp)
    exact ⟨by simpa [R] using hpR, happ⟩
  have hle_support := (c.interactionPMF hc2).toMeasure_mono
    (DiscreteMeasurableSpace.forall_measurableSet _) hsupport_subset
  have hRmeasure :
      (c.interactionPMF hc2).toMeasure (↑R : Set (AgentState L K × AgentState L K))
        = ENNReal.ofReal
          (((2 * Phase3GoodClock.hourFront (L := L) (K := K) h c *
              laggingOCount (L := L) (K := K) h c : ℕ) : ℝ) /
            ((n : ℝ) * (n - 1 : ℕ))) := by
    rw [PMF.toMeasure_apply_finset]
    simp_rw [show ∀ p : AgentState L K × AgentState L K,
        (c.interactionPMF hc2) p =
          (c.interactionCount p.1 p.2 : ENNReal) / c.totalPairs
      from fun _ => rfl, div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum]
    rw [show (∑ p ∈ R, c.interactionCount p.1 p.2)
        = 2 * Phase3GoodClock.hourFront (L := L) (K := K) h c *
          laggingOCount (L := L) (K := K) h c by
        simpa [R] using h13PullRect_interactionCount (L := L) (K := K) h c]
    rw [← div_eq_mul_inv]
    have hden_pos : (0 : ℝ) < ((n : ℝ) * (n - 1 : ℕ)) := by
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
      have hn1 : (0 : ℝ) < (n - 1 : ℕ) := by
        exact_mod_cast (Nat.sub_pos_of_lt hn)
      positivity
    have hden_cast :
        (((n * (n - 1) : ℕ) : ℝ)) = (n : ℝ) * (n - 1 : ℕ) := by
      rw [Nat.cast_mul]
    rw [show c.totalPairs = n * (n - 1) by rw [Config.totalPairs, hcard]]
    rw [← ENNReal.ofReal_natCast
      (2 * Phase3GoodClock.hourFront (L := L) (K := K) h c *
        laggingOCount (L := L) (K := K) h c)]
    rw [← ENNReal.ofReal_natCast (n * (n - 1))]
    rw [← ENNReal.ofReal_div_of_pos
      (by rwa [hden_cast] : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ))]
    rw [hden_cast]
    rw [div_eq_mul_inv]
  calc
    ENNReal.ofReal
        (((2 * Phase3GoodClock.hourFront (L := L) (K := K) h c *
            laggingOCount (L := L) (K := K) h c : ℕ) : ℝ) /
          ((n : ℝ) * (n - 1 : ℕ)))
        = (c.interactionPMF hc2).toMeasure (↑R : Set (AgentState L K × AgentState L K)) :=
          hRmeasure.symm
    _ ≤ (c.interactionPMF hc2).toMeasure
          (h13PullPairs (L := L) (K := K) c h) := hle_support

private lemma stepDistOrSelf_toMeasure_ge_phase3Bridges
    (c : Phase3Core.Omega L K) (hc : 2 ≤ c.card)
    (target : Set (Phase3Core.Omega L K))
    (good : Set (AgentState L K × AgentState L K))
    (hgood : ∀ pair ∈ good,
      (NonuniformMajority L K).scheduledStep c pair ∈ target) :
    ((NonuniformMajority L K).stepDistOrSelf c).toMeasure target ≥
      (c.interactionPMF hc).toMeasure good := by
  have h_meas : MeasurableSet target := DiscreteMeasurableSpace.forall_measurableSet _
  unfold Protocol.stepDistOrSelf
  rw [dif_pos hc]
  unfold Protocol.stepDist
  have h_map := PMF.toMeasure_map ((NonuniformMajority L K).scheduledStep c)
    (c.interactionPMF hc) Measurable.of_discrete
  calc
    (PMF.map ((NonuniformMajority L K).scheduledStep c)
        (c.interactionPMF hc)).toMeasure target
        = ((c.interactionPMF hc).toMeasure.map
            ((NonuniformMajority L K).scheduledStep c)) target := by
          rw [← h_map]
    _ = (c.interactionPMF hc).toMeasure
          ((NonuniformMajority L K).scheduledStep c ⁻¹' target) :=
        MeasureTheory.Measure.map_apply Measurable.of_discrete h_meas
    _ ≥ (c.interactionPMF hc).toMeasure good :=
        MeasureTheory.measure_mono (fun pair hp => hgood pair hp)

private lemma hour_le_min_div_of_clockAtOrBeyond
    {h : ℕ} {clk : AgentState L K}
    (hK : 0 < K) (hhL : h ≤ L)
    (hclk : Phase3GoodClock.clockAtOrBeyondHourP (L := L) (K := K) h clk) :
    h ≤ min L (clk.minute.val / K) := by
  have hdiv : h ≤ clk.minute.val / K := by
    exact (Nat.le_div_iff_mul_le hK).2 hclk.2
  exact le_min hhL hdiv

private theorem transition_main_clock_left_not_lagging
    {h : ℕ} {s t : AgentState L K}
    (hK : 0 < K) (hhL : h ≤ L)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsO : LaggingO (L := L) (K := K) h s)
    (htC : Phase3GoodClock.clockAtOrBeyondHourP (L := L) (K := K) h t) :
    ¬ LaggingO (L := L) (K := K) h (Transition L K s t).1 ∧
      ¬ LaggingO (L := L) (K := K) h (Transition L K s t).2 := by
  have hs_phase : s.phase = ⟨3, by decide⟩ := Fin.ext hs3
  have hepi :=
    ClockRealKernel.phaseEpidemicUpdate_eq_self_p3
      (L := L) (K := K) s t hs3 ht3
  have hdrag : h ≤ min L (t.minute.val / K) :=
    hour_le_min_div_of_clockAtOrBeyond (L := L) (K := K) hK hhL htC
  constructor
  · intro hbad
    have hhour : (Transition L K s t).1.hour.val =
        max s.hour.val (min L (t.minute.val / K)) := by
      unfold Transition
      rw [hepi]
      simp [hs_phase, Phase3Transition, hsO.1, hsO.2.1, htC.1]
    have hle : h ≤ (Transition L K s t).1.hour.val := by
      rw [hhour]
      exact le_trans hdrag (Nat.le_max_right _ _)
    have hlt : (Transition L K s t).1.hour.val < h := hbad.2.2
    omega
  · intro hbad
    have hrole : (Transition L K s t).2.role = Role.clock := by
      unfold Transition
      rw [hepi]
      simp [hs_phase, Phase3Transition, hsO.1, hsO.2.1, htC.1]
    have hcontra : Role.main = Role.clock := hbad.1.symm.trans hrole
    cases hcontra

private theorem transition_clock_main_right_not_lagging
    {h : ℕ} {s t : AgentState L K}
    (hK : 0 < K) (hhL : h ≤ L)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsC : Phase3GoodClock.clockAtOrBeyondHourP (L := L) (K := K) h s)
    (htO : LaggingO (L := L) (K := K) h t) :
    ¬ LaggingO (L := L) (K := K) h (Transition L K s t).1 ∧
      ¬ LaggingO (L := L) (K := K) h (Transition L K s t).2 := by
  have hs_phase : s.phase = ⟨3, by decide⟩ := Fin.ext hs3
  have hepi :=
    ClockRealKernel.phaseEpidemicUpdate_eq_self_p3
      (L := L) (K := K) s t hs3 ht3
  have hdrag : h ≤ min L (s.minute.val / K) :=
    hour_le_min_div_of_clockAtOrBeyond (L := L) (K := K) hK hhL hsC
  constructor
  · intro hbad
    have hrole : (Transition L K s t).1.role = Role.clock := by
      unfold Transition
      rw [hepi]
      simp [hs_phase, Phase3Transition, hsC.1, htO.1, htO.2.1]
    have hcontra : Role.main = Role.clock := hbad.1.symm.trans hrole
    cases hcontra
  · intro hbad
    have hhour : (Transition L K s t).2.hour.val =
        max t.hour.val (min L (s.minute.val / K)) := by
      unfold Transition
      rw [hepi]
      simp [hs_phase, Phase3Transition, hsC.1, htO.1, htO.2.1]
    have hle : h ≤ (Transition L K s t).2.hour.val := by
      rw [hhour]
      exact le_trans hdrag (Nat.le_max_right _ _)
    have hlt : (Transition L K s t).2.hour.val < h := hbad.2.2
    omega

private theorem laggingOCount_scheduledStep_lt_left
    {h : ℕ} (c : Phase3Core.Omega L K) {s t : AgentState L K}
    (hK : 0 < K) (hhL : h ≤ L)
    (hphase : ∀ a ∈ c, a.phase.val = 3)
    (happ : Protocol.Applicable c s t)
    (hsO : LaggingO (L := L) (K := K) h s)
    (htC : Phase3GoodClock.clockAtOrBeyondHourP (L := L) (K := K) h t) :
    laggingOCount (L := L) (K := K) h
        ((NonuniformMajority L K).scheduledStep c (s, t)) <
      laggingOCount (L := L) (K := K) h c := by
  have hs_mem : s ∈ c := ClockRealKernel.mem_of_applicable_left happ
  have ht_mem : t ∈ c := ClockRealKernel.mem_of_applicable_right happ
  have hnot :=
    transition_main_clock_left_not_lagging
      (L := L) (K := K) (h := h) hK hhL
      (hphase s hs_mem) (hphase t ht_mem) hsO htC
  have hpair_before :
      Multiset.countP (fun a => LaggingO (L := L) (K := K) h a)
        ({s, t} : Multiset (AgentState L K)) = 1 := by
    change Multiset.countP (fun a => LaggingO (L := L) (K := K) h a)
      (s ::ₘ ({t} : Multiset (AgentState L K))) = 1
    rw [Multiset.countP_cons_of_pos
      (p := fun a => LaggingO (L := L) (K := K) h a)
      ({t} : Multiset (AgentState L K)) hsO]
    have ht_zero :
        Multiset.countP (fun a => LaggingO (L := L) (K := K) h a)
          ({t} : Multiset (AgentState L K)) = 0 := by
      change Multiset.countP (fun a => LaggingO (L := L) (K := K) h a)
        (t ::ₘ (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro htO
        have hcontra : Role.main = Role.clock := htO.1.symm.trans htC.1
        cases hcontra
    rw [ht_zero]
  have hpair_after :
      Multiset.countP (fun a => LaggingO (L := L) (K := K) h a)
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) = 0 := by
    change Multiset.countP (fun a => LaggingO (L := L) (K := K) h a)
      ((Transition L K s t).1 ::ₘ
        ({(Transition L K s t).2} : Multiset (AgentState L K))) = 0
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP (fun a => LaggingO (L := L) (K := K) h a)
        ((Transition L K s t).2 ::ₘ (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · exact hnot.2
    · exact hnot.1
  have hsub :
      Multiset.countP (fun a => LaggingO (L := L) (K := K) h a)
        (c - ({s, t} : Multiset (AgentState L K))) =
      laggingOCount (L := L) (K := K) h c - 1 := by
    have hsub' := Multiset.countP_sub
      (s := c) (t := ({s, t} : Multiset (AgentState L K))) happ
      (fun a => LaggingO (L := L) (K := K) h a)
    unfold laggingOCount
    rw [hsub', hpair_before]
  have hstep :
      (NonuniformMajority L K).scheduledStep c (s, t) =
        c - ({s, t} : Multiset (AgentState L K)) +
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) := by
    unfold Protocol.scheduledStep Protocol.stepOrSelf NonuniformMajority
    rw [if_pos happ]
  have hnew :
      laggingOCount (L := L) (K := K) h
        ((NonuniformMajority L K).scheduledStep c (s, t)) =
      laggingOCount (L := L) (K := K) h
        (c - ({s, t} : Multiset (AgentState L K))) := by
    unfold laggingOCount
    rw [hstep, Multiset.countP_add, hpair_after, add_zero]
  have hpos_old :
      0 < laggingOCount (L := L) (K := K) h c := by
    unfold laggingOCount
    exact Multiset.countP_pos_of_mem hs_mem hsO
  have hsub_count :
      laggingOCount (L := L) (K := K) h
        (c - ({s, t} : Multiset (AgentState L K))) =
      laggingOCount (L := L) (K := K) h c - 1 := by
    simpa [laggingOCount] using hsub
  rw [hnew, hsub_count]
  omega

private theorem laggingOCount_scheduledStep_lt_right
    {h : ℕ} (c : Phase3Core.Omega L K) {s t : AgentState L K}
    (hK : 0 < K) (hhL : h ≤ L)
    (hphase : ∀ a ∈ c, a.phase.val = 3)
    (happ : Protocol.Applicable c s t)
    (hsC : Phase3GoodClock.clockAtOrBeyondHourP (L := L) (K := K) h s)
    (htO : LaggingO (L := L) (K := K) h t) :
    laggingOCount (L := L) (K := K) h
        ((NonuniformMajority L K).scheduledStep c (s, t)) <
      laggingOCount (L := L) (K := K) h c := by
  have hs_mem : s ∈ c := ClockRealKernel.mem_of_applicable_left happ
  have ht_mem : t ∈ c := ClockRealKernel.mem_of_applicable_right happ
  have hnot :=
    transition_clock_main_right_not_lagging
      (L := L) (K := K) (h := h) hK hhL
      (hphase s hs_mem) (hphase t ht_mem) hsC htO
  have hpair_before :
      Multiset.countP (fun a => LaggingO (L := L) (K := K) h a)
        ({s, t} : Multiset (AgentState L K)) = 1 := by
    change Multiset.countP (fun a => LaggingO (L := L) (K := K) h a)
      (s ::ₘ ({t} : Multiset (AgentState L K))) = 1
    rw [Multiset.countP_cons_of_neg]
    · have ht_one :
          Multiset.countP (fun a => LaggingO (L := L) (K := K) h a)
            ({t} : Multiset (AgentState L K)) = 1 := by
        change Multiset.countP (fun a => LaggingO (L := L) (K := K) h a)
          (t ::ₘ (0 : Multiset (AgentState L K))) = 1
        rw [Multiset.countP_cons_of_pos
          (p := fun a => LaggingO (L := L) (K := K) h a)
          (0 : Multiset (AgentState L K)) htO]
        simp
      rw [ht_one]
    · intro hsO
      have hcontra : Role.main = Role.clock := hsO.1.symm.trans hsC.1
      cases hcontra
  have hpair_after :
      Multiset.countP (fun a => LaggingO (L := L) (K := K) h a)
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) = 0 := by
    change Multiset.countP (fun a => LaggingO (L := L) (K := K) h a)
      ((Transition L K s t).1 ::ₘ
        ({(Transition L K s t).2} : Multiset (AgentState L K))) = 0
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP (fun a => LaggingO (L := L) (K := K) h a)
        ((Transition L K s t).2 ::ₘ (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · exact hnot.2
    · exact hnot.1
  have hsub :
      Multiset.countP (fun a => LaggingO (L := L) (K := K) h a)
        (c - ({s, t} : Multiset (AgentState L K))) =
      laggingOCount (L := L) (K := K) h c - 1 := by
    have hsub' := Multiset.countP_sub
      (s := c) (t := ({s, t} : Multiset (AgentState L K))) happ
      (fun a => LaggingO (L := L) (K := K) h a)
    unfold laggingOCount
    rw [hsub', hpair_before]
  have hstep :
      (NonuniformMajority L K).scheduledStep c (s, t) =
        c - ({s, t} : Multiset (AgentState L K)) +
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) := by
    unfold Protocol.scheduledStep Protocol.stepOrSelf NonuniformMajority
    rw [if_pos happ]
  have hnew :
      laggingOCount (L := L) (K := K) h
        ((NonuniformMajority L K).scheduledStep c (s, t)) =
      laggingOCount (L := L) (K := K) h
        (c - ({s, t} : Multiset (AgentState L K))) := by
    unfold laggingOCount
    rw [hstep, Multiset.countP_add, hpair_after, add_zero]
  have hpos_old :
      0 < laggingOCount (L := L) (K := K) h c := by
    unfold laggingOCount
    exact Multiset.countP_pos_of_mem ht_mem htO
  have hsub_count :
      laggingOCount (L := L) (K := K) h
        (c - ({s, t} : Multiset (AgentState L K))) =
      laggingOCount (L := L) (K := K) h c - 1 := by
    simpa [laggingOCount] using hsub
  rw [hnew, hsub_count]
  omega

/-- Lemma 6.13's deterministic scheduler rectangle.  Inside a phase-3 stopped
window, an ordered pair from the hour-front clock catalysts and the lagging
zero-bias Main population performs the Rule-2 hour pull and strictly decreases
`laggingOCount`. -/
theorem phase3_h13_pull_rect
    (h n a₀ i : ℕ) (c : Phase3Core.Omega L K)
    (hK : 0 < K) (hhL : h ≤ L)
    (hphase : ∀ a ∈ c, a.phase.val = 3)
    (hcard : c.card = n) (hn : 2 ≤ n)
    (hcat : a₀ ≤ Phase3GoodClock.hourFront (L := L) (K := K) h c)
    (hcnt : laggingOCount (L := L) (K := K) h c = i) :
    CatalyticPull.catalyticPullRate n a₀ i ≤
      ((NonuniformMajority L K).transitionKernel c).real
        {y | laggingOCount (L := L) (K := K) h y <
          laggingOCount (L := L) (K := K) h c} := by
  classical
  have hc2 : 2 ≤ c.card := by rw [hcard]; exact hn
  let target : Set (Phase3Core.Omega L K) :=
    {y | laggingOCount (L := L) (K := K) h y <
      laggingOCount (L := L) (K := K) h c}
  have hgood : ∀ p ∈ h13PullPairs (L := L) (K := K) c h,
      (NonuniformMajority L K).scheduledStep c p ∈ target := by
    intro p hp
    rcases hp with ⟨hpR, happ⟩
    unfold h13PullRect at hpR
    rw [Finset.mem_union] at hpR
    rcases hpR with hpCL | hpLC
    · rw [Finset.mem_product] at hpCL
      have hpC := (Finset.mem_filter.mp hpCL.1).2
      have hpO := (Finset.mem_filter.mp hpCL.2).2
      exact laggingOCount_scheduledStep_lt_right
        (L := L) (K := K) (h := h) c hK hhL hphase happ hpC hpO
    · rw [Finset.mem_product] at hpLC
      have hpO := (Finset.mem_filter.mp hpLC.1).2
      have hpC := (Finset.mem_filter.mp hpLC.2).2
      exact laggingOCount_scheduledStep_lt_left
        (L := L) (K := K) (h := h) c hK hhL hphase happ hpO hpC
  have hstep :
      (c.interactionPMF hc2).toMeasure (h13PullPairs (L := L) (K := K) c h)
        ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure target := by
    exact stepDistOrSelf_toMeasure_ge_phase3Bridges
      (L := L) (K := K) c hc2 target
      (h13PullPairs (L := L) (K := K) c h) hgood
  have hrect :
      ENNReal.ofReal
          (((2 * Phase3GoodClock.hourFront (L := L) (K := K) h c *
              laggingOCount (L := L) (K := K) h c : ℕ) : ℝ) /
            ((n : ℝ) * (n - 1 : ℕ)))
        ≤ (c.interactionPMF hc2).toMeasure
            (h13PullPairs (L := L) (K := K) c h) := by
    simpa using phase3_h13_interactionProb_ge
      (L := L) (K := K) h n c hcard hn
  have hfloor_nat :
      2 * a₀ * i ≤
        2 * Phase3GoodClock.hourFront (L := L) (K := K) h c *
          laggingOCount (L := L) (K := K) h c := by
    rw [hcnt]
    calc
      2 * a₀ * i = 2 * (a₀ * i) := by ring
      _ ≤ 2 * (Phase3GoodClock.hourFront (L := L) (K := K) h c * i) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right i hcat)
      _ = 2 * Phase3GoodClock.hourFront (L := L) (K := K) h c * i := by ring
  have hfloor_real :
      (2 : ℝ) * (a₀ : ℝ) * (i : ℝ) ≤
        ((2 * Phase3GoodClock.hourFront (L := L) (K := K) h c *
          laggingOCount (L := L) (K := K) h c : ℕ) : ℝ) := by
    exact_mod_cast hfloor_nat
  have hden_pos : (0 : ℝ) < ((n : ℝ) * (n - 1 : ℕ)) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
    have hn1 : (0 : ℝ) < (n - 1 : ℕ) := by
      exact_mod_cast (Nat.sub_pos_of_lt hn)
    positivity
  have hrate_le_rect :
      ENNReal.ofReal (CatalyticPull.catalyticPullRate n a₀ i) ≤
        ENNReal.ofReal
          (((2 * Phase3GoodClock.hourFront (L := L) (K := K) h c *
              laggingOCount (L := L) (K := K) h c : ℕ) : ℝ) /
            ((n : ℝ) * (n - 1 : ℕ))) := by
    apply ENNReal.ofReal_le_ofReal
    have hden_eq :
        (n : ℝ) * ((n : ℝ) - 1) = (n : ℝ) * (n - 1 : ℕ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    unfold CatalyticPull.catalyticPullRate
    rw [hden_eq]
    exact div_le_div_of_nonneg_right hfloor_real (le_of_lt hden_pos)
  have hENN :
      ENNReal.ofReal (CatalyticPull.catalyticPullRate n a₀ i) ≤
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure target :=
    hrate_le_rect.trans (hrect.trans hstep)
  have hrate_nonneg : 0 ≤ CatalyticPull.catalyticPullRate n a₀ i := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hn1_nonneg : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      linarith
    have hden_nonneg : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) :=
      mul_nonneg hn0 hn1_nonneg
    unfold CatalyticPull.catalyticPullRate
    exact div_nonneg (by positivity) hden_nonneg
  have htarget_ne_top :
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure target ≠ ⊤ := by
    have hle_one :
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure target ≤ (1 : ℝ≥0∞) := by
      calc
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure target
            ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Set.univ :=
              measure_mono (Set.subset_univ _)
        _ = 1 := by simp
    exact ne_of_lt (lt_of_le_of_lt hle_one ENNReal.one_lt_top)
  have hreal := ENNReal.toReal_mono htarget_ne_top hENN
  rw [ENNReal.toReal_ofReal hrate_nonneg] at hreal
  simpa [Measure.real, Phase3Core.phase3Kernel, target] using hreal

theorem phase3_h13_pull_rect_ennreal
    (h n a₀ i : ℕ) (c : Phase3Core.Omega L K)
    (hK : 0 < K) (hhL : h ≤ L)
    (hphase : ∀ a ∈ c, a.phase.val = 3)
    (hcard : c.card = n) (hn : 2 ≤ n)
    (hcat : a₀ ≤ Phase3GoodClock.hourFront (L := L) (K := K) h c)
    (hcnt : laggingOCount (L := L) (K := K) h c = i) :
    ENNReal.ofReal (CatalyticPull.catalyticPullRate n a₀ i) ≤
      (Phase3Core.phase3Kernel L K c)
        {y | laggingOCount (L := L) (K := K) h y <
          laggingOCount (L := L) (K := K) h c} := by
  have hreal :=
    phase3_h13_pull_rect (L := L) (K := K)
      h n a₀ i c hK hhL hphase hcard hn hcat hcnt
  exact ENNReal.ofReal_le_of_le_toReal (by
    simpa [Measure.real, Phase3Core.phase3Kernel] using hreal)

namespace CatalyticPull

theorem h13_pull_progress_of_stopped_clock_floor
    {G S : Set (Phase3Core.Omega L K)} {h n a₀ : ℕ}
    (B : Phase3Core.Omega L K → ℕ)
    (hCatalyst : ∀ c ∈ G, c ∈ S →
      a₀ ≤ Phase3GoodClock.hourFront (L := L) (K := K) h c)
    (hLaggingRect : ∀ c, c ∈ G → c ∈ S →
      Phase3Core.phase3Kernel L K c {c' | B c' < B c}
        ≥ ENNReal.ofReal
          ((2 : ℝ) *
            (Phase3GoodClock.hourFront (L := L) (K := K) h c : ℝ) *
            (B c : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))))
    (hn : 2 ≤ n)
    (c : Phase3Core.Omega L K) (hcG : c ∈ G) (hcS : c ∈ S) :
    Phase3Core.phase3Kernel L K c {c' | B c' < B c}
      ≥ ENNReal.ofReal (catalyticPullRate n a₀ (B c)) := by
  have hcat := hCatalyst c hcG hcS
  have hfront_real :
      (a₀ : ℝ) ≤
        (Phase3GoodClock.hourFront (L := L) (K := K) h c : ℝ) := by
    exact_mod_cast hcat
  have hB_nonneg : (0 : ℝ) ≤ (B c : ℝ) := Nat.cast_nonneg _
  have hnum :
      (2 : ℝ) * (a₀ : ℝ) * (B c : ℝ) ≤
        (2 : ℝ) *
          (Phase3GoodClock.hourFront (L := L) (K := K) h c : ℝ) *
          (B c : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hfront_real (by norm_num : (0 : ℝ) ≤ 2),
      hB_nonneg]
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
      have hn1' : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      linarith
    positivity
  have hrate_le :
      catalyticPullRate n a₀ (B c) ≤
        ((2 : ℝ) *
          (Phase3GoodClock.hourFront (L := L) (K := K) h c : ℝ) *
          (B c : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
    unfold catalyticPullRate
    exact div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
  exact (ENNReal.ofReal_le_ofReal hrate_le).trans (hLaggingRect c hcG hcS)

end CatalyticPull

/-! ## Generic catalytic-pull milestone over a stopped counter -/

namespace CatalyticPull

variable {β : Type*} [MeasurableSpace β] [DiscreteMeasurableSpace β]

def counterMilestone (B : β → ℕ) (bHi bLo : ℕ)
    (i : Fin (bHi - bLo)) (x : β) : Prop :=
  B x ≤ bHi - (i.val + 1)

omit [MeasurableSpace β] [DiscreteMeasurableSpace β] in
theorem counterMilestone_frontier {B : β → ℕ} {bHi bLo : ℕ}
    (hlo : bLo < bHi) {i : Fin (bHi - bLo)} {x : β}
    (hB_hi : B x ≤ bHi)
    (hprev : ∀ j : Fin (bHi - bLo), j < i →
      counterMilestone B bHi bLo j x)
    (hnot : ¬ counterMilestone B bHi bLo i x) :
    B x = bHi - i.val := by
  have hi_lt : i.val < bHi - bLo := i.isLt
  have hi_le_bHi : i.val ≤ bHi := by omega
  have hupper : B x ≤ bHi - i.val := by
    by_cases hiz : i.val = 0
    · simpa [hiz] using hB_hi
    · have hpos : 0 < i.val := Nat.pos_of_ne_zero hiz
      let j : Fin (bHi - bLo) := ⟨i.val - 1, by omega⟩
      have hjlt : j < i := by
        rw [Fin.lt_def]
        dsimp [j]
        omega
      have hj := hprev j hjlt
      unfold counterMilestone at hj
      dsimp [j] at hj
      omega
  have hlower : bHi - i.val ≤ B x := by
    unfold counterMilestone at hnot
    have hlt : bHi - (i.val + 1) < B x := Nat.lt_of_not_ge hnot
    omega
  omega

omit [MeasurableSpace β] [DiscreteMeasurableSpace β] in
theorem counterMilestone_post_le {B : β → ℕ} {bHi bLo : ℕ}
    (hlo : bLo < bHi) {x : β}
    (hPost : ∀ i : Fin (bHi - bLo), counterMilestone B bHi bLo i x) :
    B x ≤ bLo := by
  let i : Fin (bHi - bLo) := ⟨bHi - bLo - 1, by omega⟩
  have hi := hPost i
  unfold counterMilestone at hi
  dsimp [i] at hi
  omega

noncomputable def counterKernelMilestone
    (Q : Kernel β β) (B : β → ℕ) (bHi bLo : ℕ) (hlo : bLo < bHi)
    (rate : Fin (bHi - bLo) → ℝ)
    (hrate_pos : ∀ i, 0 < rate i)
    (hrate_le_one : ∀ i, rate i ≤ 1)
    (hB_hi : ∀ x, B x ≤ bHi)
    (hB_mono : ∀ x y, 0 < Q x {y} → B y ≤ B x)
    (hprogress : ∀ i x, B x = bHi - i.val →
      Q x {y | B y < B x} ≥ ENNReal.ofReal (rate i)) :
    RoleSplitConcentration.KernelMilestone Q where
  k := bHi - bLo
  milestone := counterMilestone B bHi bLo
  p := rate
  hp_pos := hrate_pos
  hp_le_one := hrate_le_one
  milestone_monotone := by
    intro i x y hx hsupp
    unfold counterMilestone at hx ⊢
    exact (hB_mono x y hsupp).trans hx
  progress := by
    intro i x hprev hnot
    have hfront := counterMilestone_frontier (B := B) (bHi := bHi) (bLo := bLo)
      hlo (hB_hi x) hprev hnot
    have hsub : {y : β | B y < B x} ⊆ {y : β | counterMilestone B bHi bLo i y} := by
      intro y hy
      unfold counterMilestone
      rw [hfront] at hy
      have hi_lt : i.val < bHi - bLo := i.isLt
      have hi_lt_bHi : i.val < bHi := by omega
      have hsucc : bHi - i.val = bHi - (i.val + 1) + 1 := by omega
      rw [hsucc] at hy
      exact Nat.lt_succ_iff.mp (by
        simpa [Nat.succ_eq_add_one] using hy)
    exact (hprogress i x hfront).trans (measure_mono hsub)

theorem catalyticPullRate_pos {n a₀ i : ℕ}
    (hn : 2 ≤ n) (ha₀ : 1 ≤ a₀) (hi : 0 < i) :
    0 < catalyticPullRate n a₀ i := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have hn1' : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have ha0R : (0 : ℝ) < (a₀ : ℝ) := by exact_mod_cast (by omega : 0 < a₀)
  have hiR : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  unfold catalyticPullRate
  exact div_pos (mul_pos (mul_pos (by norm_num) ha0R) hiR) (mul_pos hn0 hn1)

theorem catalyticPullRate_le_one {n a₀ i : ℕ}
    (hn : 2 ≤ n) (h2a₀ : 2 * a₀ ≤ n - 1) (hi : i ≤ n) :
    catalyticPullRate n a₀ i ≤ 1 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have hn1' : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := mul_pos hn0 hn1
  have h2aR : (2 : ℝ) * (a₀ : ℝ) ≤ (n : ℝ) - 1 := by
    have hcast : ((2 * a₀ : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast h2a₀
    simpa [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ n)] using hcast
  have hiR : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi
  have hi_nonneg : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hn1_nonneg : (0 : ℝ) ≤ (n : ℝ) - 1 := le_of_lt hn1
  have hmul := mul_le_mul h2aR hiR hi_nonneg hn1_nonneg
  unfold catalyticPullRate
  rw [div_le_one hden]
  nlinarith

noncomputable def catalyticPullKernelMilestone
    (Q : Kernel β β) (B : β → ℕ) (bHi bLo n a₀ : ℕ)
    (hlo : bLo < bHi) (hn : 2 ≤ n) (ha₀ : 1 ≤ a₀)
    (hbHi_le_n : bHi ≤ n) (h2a₀ : 2 * a₀ ≤ n - 1)
    (hB_hi : ∀ x, B x ≤ bHi)
    (hB_mono : ∀ x y, 0 < Q x {y} → B y ≤ B x)
    (hprogress : ∀ (i : Fin (bHi - bLo)) (x : β), B x = bHi - i.val →
      Q x {y | B y < B x} ≥
        ENNReal.ofReal (catalyticPullRate n a₀ (bHi - i.val))) :
    RoleSplitConcentration.KernelMilestone Q :=
  counterKernelMilestone Q B bHi bLo hlo
    (fun i => catalyticPullRate n a₀ (bHi - i.val))
    (by
      intro i
      apply catalyticPullRate_pos hn ha₀
      omega)
    (by
      intro i
      apply catalyticPullRate_le_one hn h2a₀
      omega)
    hB_hi hB_mono hprogress

end CatalyticPull

/-! ## Killed-chain catalytic tail, in the stopped shape Core uses -/

section KilledTail

open GatedDrift

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
  [Inhabited α] [Countable α]

local instance instOptionMSphase3Bridges : MeasurableSpace (Option α) := ⊤
local instance instOptionDMSphase3Bridges : DiscreteMeasurableSpace (Option α) :=
  ⟨fun _ => trivial⟩

theorem killedBad_notGood_le_janson_add_escape_noPre
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (K : Kernel α α) [IsMarkovKernel K] (G S : Set α) (good : α → Prop)
    (q : ℝ≥0∞)
    (mp : RoleSplitConcentration.KernelMilestone (killK_now K G))
    (P : Protocol Λ)
    (post_sound : ∀ y, mp.Post (some y) → good y)
    (hstep : ∀ x ∈ G, x ∈ S → K x Gᶜ ≤ q)
    (c₀ : α) (hc₀ : c₀ ∈ G)
    (lam : ℝ) (hlam : 1 ≤ lam) (t : ℕ)
    (ht : lam * mp.meanTime ≤ (t : ℝ)) :
    (killK_now K G ^ t) (some c₀)
        {o | o = none ∨ ∃ y, o = some y ∧ ¬ good y} ≤
      ENNReal.ofReal
        (Real.exp (-mp.pMin * mp.meanTime * (lam - 1 - Real.log lam))) +
        ((t : ℝ≥0∞) * q + ∑ τ ∈ Finset.range t, (K ^ τ) c₀ Sᶜ) := by
  have hcem :
      (killK_now K G ^ t) (some c₀) {(none : Option α)} ≤
        (t : ℝ≥0∞) * q + ∑ τ ∈ Finset.range t, (K ^ τ) c₀ Sᶜ :=
    RoleSplitConcentration.killedEscape_le_prefix K G S q hstep t c₀ hc₀
  have halive :
      (killK_now K G ^ t) (some c₀)
          {o | ∃ y, o = some y ∧ ¬ good y} ≤
        ENNReal.ofReal
          (Real.exp (-mp.pMin * mp.meanTime * (lam - 1 - Real.log lam))) :=
    RoleSplitConcentration.killedAliveNotGood_le_janson_noPre
      K G good mp P post_sound c₀ lam hlam t ht
  have hsub :
      {o : Option α | o = none ∨ ∃ y, o = some y ∧ ¬ good y} ⊆
        {(none : Option α)} ∪ {o | ∃ y, o = some y ∧ ¬ good y} := by
    intro o ho
    rcases ho with hnone | halive'
    · exact Or.inl hnone
    · exact Or.inr halive'
  calc
    (killK_now K G ^ t) (some c₀)
        {o | o = none ∨ ∃ y, o = some y ∧ ¬ good y}
        ≤ (killK_now K G ^ t) (some c₀)
            ({(none : Option α)} ∪ {o | ∃ y, o = some y ∧ ¬ good y}) :=
          measure_mono hsub
    _ ≤ (killK_now K G ^ t) (some c₀) {(none : Option α)} +
          (killK_now K G ^ t) (some c₀) {o | ∃ y, o = some y ∧ ¬ good y} :=
          measure_union_le _ _
    _ ≤ ((t : ℝ≥0∞) * q + ∑ τ ∈ Finset.range t, (K ^ τ) c₀ Sᶜ) +
          ENNReal.ofReal
            (Real.exp (-mp.pMin * mp.meanTime * (lam - 1 - Real.log lam))) :=
          add_le_add hcem halive
    _ = ENNReal.ofReal
          (Real.exp (-mp.pMin * mp.meanTime * (lam - 1 - Real.log lam))) +
        ((t : ℝ≥0∞) * q + ∑ τ ∈ Finset.range t, (K ^ τ) c₀ Sᶜ) := by
          rw [add_comm]

theorem phase3_stoppedTail_of_kernelMilestone_noPre
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G S : Set (Phase3Core.Omega L K)) (good : Phase3Core.Omega L K → Prop)
    (q ε : ℝ≥0∞)
    (mp : RoleSplitConcentration.KernelMilestone
      (killK_now (Phase3Core.phase3Kernel L K) G))
    (P : Protocol Λ)
    (post_sound : ∀ y, mp.Post (some y) → good y)
    (hstep :
      ∀ x ∈ G, x ∈ S → Phase3Core.phase3Kernel L K x Gᶜ ≤ q)
    (c₀ : Phase3Core.Omega L K) (hc₀ : c₀ ∈ G)
    (lam : ℝ) (hlam : 1 ≤ lam) (t : ℕ)
    (ht : lam * mp.meanTime ≤ (t : ℝ))
    (hbudget :
      ENNReal.ofReal
          (Real.exp (-mp.pMin * mp.meanTime * (lam - 1 - Real.log lam))) +
        ((t : ℝ≥0∞) * q +
          ∑ τ ∈ Finset.range t, (Phase3Core.phase3Kernel L K ^ τ) c₀ Sᶜ)
        ≤ ε) :
    Phase3Core.stoppedTail (L := L) (K := K) G t c₀ (fun c => ¬ good c) ε := by
  unfold Phase3Core.stoppedTail Phase3Core.killedBad
  exact (killedBad_notGood_le_janson_add_escape_noPre
    (K := Phase3Core.phase3Kernel L K) G S good q mp P post_sound hstep
    c₀ hc₀ lam hlam t ht).trans hbudget

end KilledTail

/-! ## Lemma 6.11 stopped leakage bridge surface -/

def ClockBeyondTiny (θ : Phase3GoodClock.ClockTimingParams) (h : ℕ)
    (c : Phase3Core.Omega L K) : Prop :=
  Phase3GoodClock.TinyBeforeEnd (L := L) (K := K) θ h c

def MainAboveTiny (M : ℕ) (h : ℕ)
    (c : Phase3Core.Omega L K) : Prop :=
  HourCoupling.mAbove (L := L) (K := K) h c ≤
    Phase3Core.mainAboveTinyThreshold M

def OFuelAboveCount (h : ℕ) (c : Phase3Core.Omega L K) : ℕ :=
  Multiset.countP
    (fun a : AgentState L K => a.role = Role.main ∧ a.bias = Bias.zero ∧ h < a.hour.val)
    c

def OFuelAboveTiny (M : ℕ) (h : ℕ)
    (c : Phase3Core.Omega L K) : Prop :=
  OFuelAboveCount (L := L) (K := K) h c ≤
    Phase3Core.mainAboveTinyThreshold M

theorem ofuelAboveCount_le_mAbove (h : ℕ) (c : Phase3Core.Omega L K) :
    OFuelAboveCount (L := L) (K := K) h c ≤
      HourCoupling.mAbove (L := L) (K := K) h c := by
  unfold OFuelAboveCount HourCoupling.mAbove HourCoupling.mainAboveP
  rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter]
  apply Multiset.card_le_card
  apply Multiset.monotone_filter_right
  intro a ha
  exact ⟨ha.1, ha.2.2⟩

theorem ofuelAboveTiny_of_mainAboveTiny
    {M h : ℕ} {c : Phase3Core.Omega L K}
    (hm : MainAboveTiny (L := L) (K := K) M h c) :
    OFuelAboveTiny (L := L) (K := K) M h c :=
  (ofuelAboveCount_le_mAbove (L := L) (K := K) h c).trans hm

theorem mainAbove_eq_zero_of_L_le {h : ℕ} (hL : L ≤ h)
    (c : Phase3Core.Omega L K) :
    HourCoupling.mAbove (L := L) (K := K) h c = 0 := by
  unfold HourCoupling.mAbove
  induction c using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.countP_cons, ih]
      have hnot : ¬ HourCoupling.mainAboveP h a := by
        intro ha
        have hv := a.hour.2
        have hh : h < a.hour.val := ha.2
        omega
      simp [hnot]

theorem mainAboveTiny_of_L_le {M h : ℕ} (hL : L ≤ h)
    (c : Phase3Core.Omega L K) :
    MainAboveTiny (L := L) (K := K) M h c := by
  unfold MainAboveTiny
  rw [mainAbove_eq_zero_of_L_le (L := L) (K := K) hL c]
  exact Nat.zero_le (Phase3Core.mainAboveTinyThreshold M)

theorem ofuelAboveCount_eq_zero_of_L_le {h : ℕ} (hL : L ≤ h)
    (c : Phase3Core.Omega L K) :
    OFuelAboveCount (L := L) (K := K) h c = 0 := by
  unfold OFuelAboveCount
  induction c using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.countP_cons, ih]
      have hnot :
          ¬ (a.role = Role.main ∧ a.bias = Bias.zero ∧ h < a.hour.val) := by
        intro ha
        have hv := a.hour.2
        omega
      simp [hnot]

theorem ofuelAboveTiny_of_L_le {M h : ℕ} (hL : L ≤ h)
    (c : Phase3Core.Omega L K) :
    OFuelAboveTiny (L := L) (K := K) M h c := by
  unfold OFuelAboveTiny
  rw [ofuelAboveCount_eq_zero_of_L_le (L := L) (K := K) hL c]
  exact Nat.zero_le (Phase3Core.mainAboveTinyThreshold M)

theorem lemma610_honest_on_gate
    (G : Set (Phase3Core.Omega L K)) (M C : ℝ)
    (hM : 0 < M) (hC : 0 < C) (h : ℕ) (hK : 0 < K) (hhL : h < L)
    (hG :
      G ⊆ Lemma610StoppedAzuma.regimeSet (L := L) (K := K) M C h)
    (t : ℕ) (ht : 1 ≤ t) (c₀ : Phase3Core.Omega L K)
    (hphi0 : HourCouplingAzuma.Phi (L := L) (K := K) M C h c₀ = 0) :
    ((ClockStoppedTransfer.stoppedK (Phase3Core.phase3Kernel L K) G) ^ t) c₀
        {c' | (12 / 10000 : ℝ) ≤
              (HourCoupling.mAbove (L := L) (K := K) h c' : ℝ) / M
            ∧ (HourCoupling.cAbove (L := L) (K := K) h c' : ℝ) / C ≤
              (1 / 1000 : ℝ)}
      ≤ ENNReal.ofReal (Real.exp
          (-((1 / 10000 : ℝ) ^ 2) /
            (2 * (t : ℝ) * (2 / M + 2 * (11 / 10 : ℝ) / C) ^ 2))) := by
  classical
  have hc0pos : (0 : ℝ) < 2 / M + 2 * (11 / 10 : ℝ) / C := by
    positivity
  have hdrift :
      ∀ x, ∫ y, HourCouplingAzuma.Phi (L := L) (K := K) M C h y
          ∂((ClockStoppedTransfer.stoppedK (Phase3Core.phase3Kernel L K) G) x)
        ≤ HourCouplingAzuma.Phi (L := L) (K := K) M C h x := by
    intro x
    unfold ClockStoppedTransfer.stoppedK Phase3Core.phase3Kernel
    rw [Kernel.piecewise_apply]
    by_cases hx : x ∈ G
    · rw [if_pos hx]
      obtain ⟨hw, hwin, hMc, hCc, hM1, hC1⟩ := hG hx
      exact HourCouplingAzuma.hour_drift M C h hK hhL x hw hwin hMc hCc hM1 hC1
    · rw [if_neg hx, Kernel.id_apply, integral_dirac]
  have hdiff :
      ∀ x, ∀ᵐ y ∂((ClockStoppedTransfer.stoppedK (Phase3Core.phase3Kernel L K) G) x),
        |HourCouplingAzuma.Phi (L := L) (K := K) M C h y -
          HourCouplingAzuma.Phi (L := L) (K := K) M C h x|
          ≤ 2 / M + 2 * (11 / 10 : ℝ) / C := by
    intro x
    unfold ClockStoppedTransfer.stoppedK Phase3Core.phase3Kernel
    rw [Kernel.piecewise_apply]
    by_cases hx : x ∈ G
    · rw [if_pos hx]
      exact HourCouplingAzuma.hour_bdd M C hM hC h x
    · rw [if_neg hx, Kernel.id_apply]
      have hbnd :
          |HourCouplingAzuma.Phi (L := L) (K := K) M C h x -
            HourCouplingAzuma.Phi (L := L) (K := K) M C h x|
            ≤ 2 / M + 2 * (11 / 10 : ℝ) / C := by
        simp only [sub_self, abs_zero]
        positivity
      exact (MeasureTheory.ae_dirac_iff
        (DiscreteMeasurableSpace.forall_measurableSet _)).mpr hbnd
  refine le_trans (measure_mono ?_)
    (ExactMajority.azuma_tail
      (ClockStoppedTransfer.stoppedK (Phase3Core.phase3Kernel L K) G)
      (HourCouplingAzuma.Phi (L := L) (K := K) M C h)
      (HourCouplingAzuma.Phi_measurable M C h)
      (2 / M + 2 * (11 / 10 : ℝ) / C) hc0pos hdiff hdrift t ht c₀
      (by norm_num : (0 : ℝ) < 1 / 10000))
  intro c' hc'
  obtain ⟨hma, hcl⟩ := hc'
  simp only [Set.mem_setOf_eq, hphi0, zero_add]
  by_contra hcon
  push Not at hcon
  exact absurd
    (Lemma610StoppedAzuma.mAbove_frac_lt_0012 M C hC h c' hcon hcl)
    (by linarith)

/-- Stopped Lemma-6.11 input.  This is the exact place where the Azuma stopped
leakage proof must enter; it is intentionally not a global invariant. -/
structure LeakageBridge {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr) where
  epsLeak : ℕ → ℝ≥0∞
  tail : ∀ h, h ≤ D.lastCoreHour →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ c₀, c₀ ∈ T.surface.checkpoint .hourStart h →
    ∀ dt, dt ≤
        Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.start (L := L) (K := K) (T.clockInput h) →
      Phase3Core.stoppedTail (L := L) (K := K) (T.surface.hourGate h) dt c₀
        (fun c =>
          ¬ (ClockBeyondTiny (L := L) (K := K) θ h c ∧
             MainAboveTiny (L := L) (K := K) D.M h c ∧
             OFuelAboveTiny (L := L) (K := K) D.M h c))
        (epsLeak h)

/-- The quantitative and exit-budget side of Lemma 6.11.  The structural
GoodClock/Regime constraints live on `CoreRunSurface`; this bundle supplies the
two numerical facts needed after the `killK_now`/self-loop stopped-kernel split. -/
structure LeakageBridgeBounds {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr) where
  epsExit : ℕ → ℝ≥0∞
  epsAzuma : ℕ → ℝ≥0∞
  exit_tail : ∀ h, h ≤ D.lastCoreHour →
    ∀ c₀, c₀ ∈ T.surface.checkpoint .hourStart h →
    ∀ dt, dt ≤
        Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.start (L := L) (K := K) (T.clockInput h) →
      (GatedDrift.killK_now (Phase3Core.phase3Kernel L K) (T.surface.hourGate h) ^ dt)
        (some c₀) {(none : Option (Phase3Core.Omega L K))} ≤ epsExit h
  azuma_tail_bound : ∀ h, h ≤ D.lastCoreHour →
    ∀ dt, dt ≤
        Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.start (L := L) (K := K) (T.clockInput h) →
      1 ≤ dt → h < L →
        ENNReal.ofReal (Real.exp
          (-((1 / 10000 : ℝ) ^ 2) /
            (2 * (dt : ℝ) *
              (2 / (D.M : ℝ) + 2 * (11 / 10 : ℝ) / T.surface.leakageC) ^ 2)))
          ≤ epsAzuma h
  eps_budget : ∀ h, h ≤ D.lastCoreHour →
    epsExit h + epsAzuma h ≤
      ENNReal.ofReal Lemma617Minority.Constants.eta617Max

namespace LeakageBridgeBounds

noncomputable def mkLeakageBridge {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (B : LeakageBridgeBounds (L := L) (K := K) D T) :
    LeakageBridge (L := L) (K := K) D T where
  epsLeak := fun _ => ENNReal.ofReal Lemma617Minority.Constants.eta617Max
  tail := by
    intro h hle I c₀ hc₀ dt hdt
    let Bad : Phase3Core.Omega L K → Prop := fun c =>
      ¬ (ClockBeyondTiny (L := L) (K := K) θ h c ∧
         MainAboveTiny (L := L) (K := K) D.M h c ∧
         OFuelAboveTiny (L := L) (K := K) D.M h c)
    by_cases hzero : dt = 0
    · subst dt
      have hc₀G : c₀ ∈ T.surface.hourGate h :=
        (T.surface.hourStart_mem_gate h hle) hc₀
      have hclock :
          ClockBeyondTiny (L := L) (K := K) θ h c₀ :=
        T.surface.hourGate_clock_tiny h hle c₀ hc₀G
      have hmain :
          MainAboveTiny (L := L) (K := K) D.M h c₀ :=
        T.surface.hourStart_main_tiny h hle c₀ hc₀
      have hofuel :
          OFuelAboveTiny (L := L) (K := K) D.M h c₀ :=
        ofuelAboveTiny_of_mainAboveTiny (L := L) (K := K) hmain
      have hgood :
          ClockBeyondTiny (L := L) (K := K) θ h c₀ ∧
          MainAboveTiny (L := L) (K := K) D.M h c₀ ∧
          OFuelAboveTiny (L := L) (K := K) D.M h c₀ :=
        ⟨hclock, hmain, hofuel⟩
      have hnot :
          (some c₀ : Option (Phase3Core.Omega L K)) ∉
            Phase3Core.killedBad Bad := by
        intro ho
        rcases ho with hnone | ⟨c, hsome, hbad⟩
        · cases hnone
        · have hc : c₀ = c := Option.some.inj hsome
          subst c
          exact hbad hgood
      unfold Phase3Core.stoppedTail
      rw [pow_zero]
      change (Kernel.id (some c₀)) (Phase3Core.killedBad Bad) ≤
        ENNReal.ofReal Lemma617Minority.Constants.eta617Max
      rw [Kernel.id_apply,
        Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
      rw [Set.indicator_of_notMem hnot]
      exact zero_le'
    · have hdtpos : 1 ≤ dt := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hzero)
      have hc₀G : c₀ ∈ T.surface.hourGate h :=
        (T.surface.hourStart_mem_gate h hle) hc₀
      let AliveBad : Set (Option (Phase3Core.Omega L K)) :=
        {o | ∃ y, o = some y ∧ Bad y}
      let μ : Measure (Option (Phase3Core.Omega L K)) :=
        (GatedDrift.killK_now (Phase3Core.phase3Kernel L K) (T.surface.hourGate h) ^ dt)
          (some c₀)
      have hsplit :
          Phase3Core.killedBad Bad ⊆
            {(none : Option (Phase3Core.Omega L K))} ∪ AliveBad := by
        intro o ho
        rcases ho with hnone | ⟨c, hc, hbad⟩
        · exact Or.inl hnone
        · exact Or.inr ⟨c, hc, hbad⟩
      have hExit :
          μ {(none : Option (Phase3Core.Omega L K))} ≤ B.epsExit h := by
        simpa [μ] using B.exit_tail h hle c₀ hc₀ dt hdt
      by_cases hLt : h < L
      · let Az : Phase3Core.Omega L K → Prop := fun c =>
          (12 / 10000 : ℝ) ≤
              (HourCoupling.mAbove (L := L) (K := K) h c : ℝ) / (D.M : ℝ) ∧
            (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) /
                T.surface.leakageC ≤ (1 / 1000 : ℝ)
        have hAlive :
            μ AliveBad ≤
              ((ClockStoppedTransfer.stoppedK
                  (Phase3Core.phase3Kernel L K) (T.surface.hourGate h)) ^ dt)
                c₀ {y | Az y} := by
          simpa [μ, AliveBad, Bad, Az] using
            kill_now_alive_bad_le_stopped_on_gate
              (K := Phase3Core.phase3Kernel L K)
              (G := T.surface.hourGate h)
              (bad := Bad) (az := Az)
              (t := dt) (x := c₀)
              (by
                intro y hyG hyBad
                have hclock :
                    ClockBeyondTiny (L := L) (K := K) θ h y :=
                  T.surface.hourGate_clock_tiny h hle y hyG
                have hmain_not :
                    ¬ MainAboveTiny (L := L) (K := K) D.M h y := by
                  intro hmain
                  have hofuel :
                      OFuelAboveTiny (L := L) (K := K) D.M h y :=
                    ofuelAboveTiny_of_mainAboveTiny (L := L) (K := K) hmain
                  exact hyBad ⟨hclock, hmain, hofuel⟩
                exact ⟨
                  Phase3Core.main_not_tiny_frac (L := L) (K := K)
                    (D := D) (h := h) (c := y) hmain_not,
                  T.surface.clockTiny_frac h y hclock⟩)
              hc₀G
        have hM : (0 : ℝ) < (D.M : ℝ) := by
          exact_mod_cast D.M_pos
        have hStopAz :
            ((ClockStoppedTransfer.stoppedK
                (Phase3Core.phase3Kernel L K) (T.surface.hourGate h)) ^ dt)
              c₀ {y | Az y} ≤ B.epsAzuma h := by
          calc
            ((ClockStoppedTransfer.stoppedK
                (Phase3Core.phase3Kernel L K) (T.surface.hourGate h)) ^ dt)
              c₀ {y | Az y}
                ≤ ENNReal.ofReal (Real.exp
                    (-((1 / 10000 : ℝ) ^ 2) /
                      (2 * (dt : ℝ) *
                        (2 / (D.M : ℝ) +
                          2 * (11 / 10 : ℝ) / T.surface.leakageC) ^ 2))) := by
                    simpa [Az] using
                      lemma610_honest_on_gate (L := L) (K := K)
                        (G := T.surface.hourGate h)
                        (M := (D.M : ℝ)) (C := T.surface.leakageC)
                        hM T.surface.leakageC_pos h T.surface.leakageK_pos hLt
                        (T.surface.hourGate_le_regime h hle)
                        dt hdtpos c₀
                        (T.surface.hourStart_phi_zero h hle c₀ hc₀)
            _ ≤ B.epsAzuma h :=
                B.azuma_tail_bound h hle dt hdt hdtpos hLt
        unfold Phase3Core.stoppedTail
        calc
          μ (Phase3Core.killedBad Bad)
              ≤ μ ({(none : Option (Phase3Core.Omega L K))} ∪ AliveBad) :=
                measure_mono hsplit
          _ ≤ μ {(none : Option (Phase3Core.Omega L K))} + μ AliveBad :=
                measure_union_le _ _
          _ ≤ B.epsExit h + B.epsAzuma h :=
                add_le_add hExit (hAlive.trans hStopAz)
          _ ≤ ENNReal.ofReal Lemma617Minority.Constants.eta617Max :=
                B.eps_budget h hle
      · have hLle : L ≤ h := by
          omega
        let FalseAz : Phase3Core.Omega L K → Prop := fun _ => False
        have hAliveFalse :
            μ AliveBad ≤
              ((ClockStoppedTransfer.stoppedK
                  (Phase3Core.phase3Kernel L K) (T.surface.hourGate h)) ^ dt)
                c₀ {y | FalseAz y} := by
          simpa [μ, AliveBad, Bad, FalseAz] using
            kill_now_alive_bad_le_stopped_on_gate
              (K := Phase3Core.phase3Kernel L K)
              (G := T.surface.hourGate h)
              (bad := Bad) (az := FalseAz)
              (t := dt) (x := c₀)
              (by
                intro y hyG hyBad
                have hclock :
                    ClockBeyondTiny (L := L) (K := K) θ h y :=
                  T.surface.hourGate_clock_tiny h hle y hyG
                have hmain :
                    MainAboveTiny (L := L) (K := K) D.M h y :=
                  mainAboveTiny_of_L_le (L := L) (K := K) (M := D.M) hLle y
                have hofuel :
                    OFuelAboveTiny (L := L) (K := K) D.M h y :=
                  ofuelAboveTiny_of_L_le (L := L) (K := K) (M := D.M) hLle y
                exact False.elim (hyBad ⟨hclock, hmain, hofuel⟩))
              hc₀G
        have hAliveZero : μ AliveBad ≤ 0 := by
          calc
            μ AliveBad
                ≤ ((ClockStoppedTransfer.stoppedK
                    (Phase3Core.phase3Kernel L K) (T.surface.hourGate h)) ^ dt)
                  c₀ {y | FalseAz y} := hAliveFalse
            _ = 0 := by
                  simp [FalseAz]
        unfold Phase3Core.stoppedTail
        calc
          μ (Phase3Core.killedBad Bad)
              ≤ μ ({(none : Option (Phase3Core.Omega L K))} ∪ AliveBad) :=
                measure_mono hsplit
          _ ≤ μ {(none : Option (Phase3Core.Omega L K))} + μ AliveBad :=
                measure_union_le _ _
          _ ≤ B.epsExit h + 0 :=
                add_le_add hExit hAliveZero
          _ = B.epsExit h := by simp
          _ ≤ B.epsExit h + B.epsAzuma h :=
                le_add_right (le_refl (B.epsExit h))
          _ ≤ ENNReal.ofReal Lemma617Minority.Constants.eta617Max :=
                B.eps_budget h hle

end LeakageBridgeBounds

/-! ## H13 and H14 Core producer bridges -/

structure H13Bridge {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr) where
  epsReach : ℕ → ℝ≥0∞
  eps_budget : ∀ h, h ≤ D.lastCoreHour → 5 ≤ h →
    epsReach h ≤ T.surface.eps13 h
  /-- Faithful Lemma-6.13 output: the marked-pull engine plus correction budgets
  produces the current `O_h` fuel floor directly.  The old reached-Main floor is
  retained above only as an internal arithmetic helper. -/
  reached_tail : ∀ h, h ≤ D.lastCoreHour → 5 ≤ h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cO, cO ∈ T.surface.checkpoint .afterO h →
    ∀ dt, dt ≤
        Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput h) →
      Phase3Core.stoppedTail (L := L) (K := K) (T.surface.hourGate h) dt cO
        (fun c => ¬ Phase3Core.OFuelFloor (L := L) (K := K) D h c)
        (epsReach h)

namespace H13Bridge

noncomputable def mkH13 {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (B : H13Bridge (L := L) (K := K) D T) :
    ∀ h, h ≤ D.lastCoreHour → 5 ≤ h →
      Phase3Core.PrevCore (L := L) (K := K) D T h →
      Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
      Phase3Core.H13 (L := L) (K := K) D T h := by
  intro h hle h5 prev I
  refine ⟨hle, ?_⟩
  intro cO hcO dt hdt
  exact (B.reached_tail h hle h5 prev I cO hcO dt hdt).trans
    (B.eps_budget h hle h5)

end H13Bridge

structure H14Bridge {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr) where
  epsPhi : ℕ → ℝ≥0∞
  eps_budget : ∀ h, h ≤ D.lastCoreHour → D.q ≤ h →
    epsPhi h ≤ T.surface.eps14 h
  phi_tail : ∀ h, h ≤ D.lastCoreHour → D.q ≤ h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cStart, cStart ∈ T.surface.checkpoint .afterPhi (h - D.q) →
      Phase3Core.stoppedTail (L := L) (K := K)
        (T.surface.spanGate (h - D.q) h)
        (Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput (h - D.q)))
        cStart
        (fun c => ¬ Phase3Core.PhiZero (L := L) (K := K) (h - D.q) c)
        (epsPhi h)

namespace H14Bridge

noncomputable def mkH14 {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (B : H14Bridge (L := L) (K := K) D T) :
    ∀ h, h ≤ D.lastCoreHour → D.q ≤ h →
      Phase3Core.PrevCore (L := L) (K := K) D T h →
      Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
      Phase3Core.H14 (L := L) (K := K) D T h := by
  intro h hle hq prev I
  refine Phase3Core.H14.hit (D := D) (T := T) (h := h) hle hq ?_ ?_
  · omega
  · intro cStart hcStart
    exact stoppedTail_mono (L := L) (K := K)
      (Bad := fun c => ¬ Phase3Core.PhiZero (L := L) (K := K) (h - D.q) c)
      (Bad' := fun c => ¬ Phase3Core.PhiZero (L := L) (K := K) (h - D.q) c)
      (fun c hc => hc)
      (B.phi_tail h hle hq prev I cStart hcStart)
      |> fun htail =>
        (show Phase3Core.stoppedTail (L := L) (K := K)
          (T.surface.spanGate (h - D.q) h)
          (Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput h) -
            Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput (h - D.q)))
          cStart
          (fun c => ¬ Phase3Core.PhiZero (L := L) (K := K) (h - D.q) c)
          (T.surface.eps14 h) from htail.trans (B.eps_budget h hle hq))

end H14Bridge

/-- Core producers with `mkH13` and `mkH14` supplied by bridge lemmas, while
the later H15/H16 producers remain the piece-7 obligations. -/
structure CoreBridgeProducers {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr) where
  pre3 : Phase3Core.Pre3Seed (L := L) (K := K) D T
  h13 : H13Bridge (L := L) (K := K) D T
  h14 : H14Bridge (L := L) (K := K) D T
  mkH15 : ∀ h, h ≤ D.lastCoreHour → 5 ≤ h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H13 (L := L) (K := K) D T h →
    Phase3Core.H14 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    Phase3Core.H15 (L := L) (K := K) D T h
  mkH16 : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H15 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    Phase3Core.H16 (L := L) (K := K) D T h

namespace CoreBridgeProducers

noncomputable def toCoreProducers {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (P : CoreBridgeProducers (L := L) (K := K) D T) :
    Phase3Core.CoreProducers (L := L) (K := K) D T where
  pre3 := P.pre3
  mkH13 := P.h13.mkH13
  mkH14 := P.h14.mkH14
  mkH15 := P.mkH15
  mkH16 := P.mkH16

end CoreBridgeProducers

#print axioms stoppedTail_ofuelFloor_of_reached_biased
#print axioms stoppedTail_of_real_tail_add_exit
#print axioms kill_now_alive_outside_gate_zero
#print axioms kill_now_alive_bad_le_stopped_on_gate
#print axioms phase3_h13_pull_rect
#print axioms phase3_h13_pull_rect_ennreal
#print axioms CatalyticPull.h13_pull_progress_of_stopped_clock_floor
#print axioms lemma610_honest_on_gate
#print axioms LeakageBridgeBounds.mkLeakageBridge
#print axioms CatalyticPull.catalyticPullKernelMilestone
#print axioms phase3_stoppedTail_of_kernelMilestone_noPre
#print axioms H13Bridge.mkH13
#print axioms H14Bridge.mkH14
#print axioms CoreBridgeProducers.toCoreProducers

end Phase3Bridges

end ExactMajority
