import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase3GoodClock
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealBulk
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockHourBounds
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealFaithfulHonest
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFullJoint
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Lemma610StoppedAzuma
import Mathlib.Tactic

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Phase3GoodClockRegime

open Phase3GoodClock ClockRealKernel

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-!
Slot-3 avenue e: Regime discharge surface for the carried GoodClock fields.

The real clock-front concentration and stopped Lemma 6.10 tails remain
probabilistic inputs at this layer.  This file supplies the deterministic
projection into the `GoodClock`/`CoreClockInputs` interface and records the
events whose probabilities are union-bounded.
-/

/-! ## Real-clock count bridges -/

theorem hourFront_eq_rBeyond (h : ℕ) (c : Config (AgentState L K)) :
    Phase3GoodClock.hourFront (L := L) (K := K) h c =
      ClockRealKernel.rBeyond (L := L) (K := K) (h * K) c := by
  rfl

theorem beyondHour_eq_rBeyond (h : ℕ) (c : Config (AgentState L K)) :
    Phase3GoodClock.beyondHour (L := L) (K := K) h c =
      ClockRealKernel.rBeyond (L := L) (K := K) ((h + 1) * K) c := by
  rfl

/-! ## Standard Doty thresholds -/

def stdTheta (mC twoOverC fortyOneOverM fortySevenOverM : ℕ)
    (h41 : fortyOneOverM ≤ fortySevenOverM) :
    Phase3GoodClock.ClockTimingParams where
  small := mC / 1000
  bulk := ClockRealBulk.bulkHi mC
  twoOverC := twoOverC
  fortyOneOverM := fortyOneOverM
  fortySevenOverM := fortySevenOverM
  small_le_bulk := by
    unfold ClockRealBulk.bulkHi
    omega
  fortyOne_le_fortySeven := h41

/-! ## One-step and first-passage deterministic facts -/

theorem firstHit_small_lt_bulk_of_mono_unit
    {X : ℕ → ℕ} {small bulk : ℕ}
    (hsmall : small < bulk)
    (_hmono : ∀ t, X t ≤ X (t + 1))
    (hunit : ∀ t, X (t + 1) ≤ X t + 1)
    (hstartSmall : X 0 < small)
    (hexSmall : ∃ t, small ≤ X t)
    (hexBulk : ∃ t, bulk ≤ X t) :
    Phase3GoodClock.firstPassage (fun t => small ≤ X t) hexSmall <
      Phase3GoodClock.firstPassage (fun t => bulk ≤ X t) hexBulk := by
  classical
  let tb := Phase3GoodClock.firstPassage (fun t => bulk ≤ X t) hexBulk
  have hbulkHit : bulk ≤ X tb := by
    exact (Phase3GoodClock.firstPassage_firstHit
      (P := fun t => bulk ≤ X t) hexBulk).hit
  have hbulkFirst : ∀ τ, τ < tb → ¬ bulk ≤ X τ := by
    exact (Phase3GoodClock.firstPassage_firstHit
      (P := fun t => bulk ≤ X t) hexBulk).first
  have htb_pos : 0 < tb := by
    by_contra hnot
    have htb0 : tb = 0 := by omega
    have : bulk ≤ X 0 := by simpa [htb0] using hbulkHit
    omega
  have hprev_lt_bulk : X (tb - 1) < bulk := by
    exact Nat.lt_of_not_ge (hbulkFirst (tb - 1) (by omega))
  have hunitPrev : X tb ≤ X (tb - 1) + 1 := by
    have h := hunit (tb - 1)
    have htb : tb - 1 + 1 = tb := by omega
    simpa [htb] using h
  have hsmallPrev : small ≤ X (tb - 1) := by omega
  have hfpSmallLe :
      Phase3GoodClock.firstPassage (fun t => small ≤ X t) hexSmall ≤ tb - 1 :=
    Phase3GoodClock.firstPassage_le_of_hit
      (P := fun t => small ≤ X t) hexSmall hsmallPrev
  omega

private theorem clockBeyondP_of_role_minute_ge
    {T : ℕ} {a : AgentState L K}
    (hrole : a.role = .clock) (hmin : T ≤ a.minute.val) :
    ClockRealKernel.clockBeyondP (L := L) (K := K) T a := by
  exact ⟨hrole, hmin⟩

theorem rBeyond_pair_le_add_one (T : ℕ) (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock) :
    Multiset.countP (fun a => ClockRealKernel.clockBeyondP (L := L) (K := K) T a)
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K))
      ≤
    Multiset.countP (fun a => ClockRealKernel.clockBeyondP (L := L) (K := K) T a)
        ({s, t} : Multiset (AgentState L K)) + 1 := by
  classical
  set s' := (Transition L K s t).1 with hs'
  set t' := (Transition L K s t).2 with ht'
  rw [ClockRealKernel.countP_pair, ClockRealKernel.countP_pair]
  by_cases hmin : s.minute = t.minute
  · by_cases hcap : s.minute.val < K * (L + 1)
    · have hd := Transition_phase3_clock_minute_drip_decreases
        (L := L) (K := K) s t hs_phase ht_phase hs_clock ht_clock hmin hcap
      have hs'role : s'.role = .clock := hd.2.2.1
      have ht'role : t'.role = .clock := hd.2.2.2.1
      have ht'min : t'.minute = t.minute := hd.2.2.2.2.2.1
      have h2 :
          (if ClockRealKernel.clockBeyondP (L := L) (K := K) T t' then (1 : ℕ) else 0) =
            if ClockRealKernel.clockBeyondP (L := L) (K := K) T t then 1 else 0 := by
        unfold ClockRealKernel.clockBeyondP
        simp only [ht'role, ht_clock, ht'min]
      have h1 :
          (if ClockRealKernel.clockBeyondP (L := L) (K := K) T s' then (1 : ℕ) else 0)
            ≤ (if ClockRealKernel.clockBeyondP (L := L) (K := K) T s then 1 else 0) + 1 := by
        split <;> omega
      omega
    · have hc := ClockRealKernel.Transition_phase3_clock_cap
        (L := L) (K := K) s t hs_phase ht_phase hs_clock ht_clock hmin hcap
      have hs'role : s'.role = .clock := hc.1
      have ht'role : t'.role = .clock := hc.2.1
      have hs'min : s'.minute = s.minute := hc.2.2.1
      have ht'min : t'.minute = t.minute := hc.2.2.2
      have e1 :
          (if ClockRealKernel.clockBeyondP (L := L) (K := K) T s' then (1 : ℕ) else 0) =
            if ClockRealKernel.clockBeyondP (L := L) (K := K) T s then 1 else 0 := by
        unfold ClockRealKernel.clockBeyondP
        simp only [hs'role, hs_clock, hs'min]
      have e2 :
          (if ClockRealKernel.clockBeyondP (L := L) (K := K) T t' then (1 : ℕ) else 0) =
            if ClockRealKernel.clockBeyondP (L := L) (K := K) T t then 1 else 0 := by
        unfold ClockRealKernel.clockBeyondP
        simp only [ht'role, ht_clock, ht'min]
      omega
  · have hsy := Transition_phase3_clock_minute_sync_decreases
      (L := L) (K := K) s t hs_phase ht_phase hs_clock ht_clock hmin
    have hs'role : s'.role = .clock := hsy.2.2.1
    have ht'role : t'.role = .clock := hsy.2.2.2.1
    have hs'min : s'.minute = max s.minute t.minute := hsy.2.2.2.2.1
    have ht'min : t'.minute = max s.minute t.minute := hsy.2.2.2.2.2.1
    by_cases hmax : T ≤ (max s.minute t.minute).val
    · have hs'P : ClockRealKernel.clockBeyondP (L := L) (K := K) T s' := by
        exact clockBeyondP_of_role_minute_ge hs'role (by simpa [hs'min] using hmax)
      have ht'P : ClockRealKernel.clockBeyondP (L := L) (K := K) T t' := by
        exact clockBeyondP_of_role_minute_ge ht'role (by simpa [ht'min] using hmax)
      have hin_ge_one :
          1 ≤ (if ClockRealKernel.clockBeyondP (L := L) (K := K) T s then (1 : ℕ) else 0) +
              (if ClockRealKernel.clockBeyondP (L := L) (K := K) T t then 1 else 0) := by
        rcases le_total s.minute t.minute with hst | hts
        · have htP : ClockRealKernel.clockBeyondP (L := L) (K := K) T t := by
            have hmaxeq : max s.minute t.minute = t.minute := max_eq_right hst
            exact clockBeyondP_of_role_minute_ge ht_clock (by simpa [hmaxeq] using hmax)
          simp [htP]
        · have hsP : ClockRealKernel.clockBeyondP (L := L) (K := K) T s := by
            have hmaxeq : max s.minute t.minute = s.minute := max_eq_left hts
            exact clockBeyondP_of_role_minute_ge hs_clock (by simpa [hmaxeq] using hmax)
          simp [hsP]
      simp [hs'P, ht'P]
      omega
    · have hs'not : ¬ ClockRealKernel.clockBeyondP (L := L) (K := K) T s' := by
        intro hp
        exact hmax (by simpa [ClockRealKernel.clockBeyondP, hs'role, hs'min] using hp.2)
      have ht'not : ¬ ClockRealKernel.clockBeyondP (L := L) (K := K) T t' := by
        intro hp
        exact hmax (by simpa [ClockRealKernel.clockBeyondP, ht'role, ht'min] using hp.2)
      simp [hs'not, ht'not]

theorem rBeyond_stepOrSelf_le_add_one (T : ℕ) (c : Config (AgentState L K))
    (hw : ClockRealKernel.AllClockP3 (L := L) (K := K) c)
    (r₁ r₂ : AgentState L K) :
    ClockRealKernel.rBeyond (L := L) (K := K) T
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ ClockRealKernel.rBeyond (L := L) (K := K) T c + 1 := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmem1 := ClockRealKernel.mem_of_applicable_left (L := L) (K := K) happ
    have hmem2 := ClockRealKernel.mem_of_applicable_right (L := L) (K := K) happ
    obtain ⟨h1c, h1p⟩ := hw r₁ hmem1
    obtain ⟨h2c, h2p⟩ := hw r₂ hmem2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(NonuniformMajority L K).δ r₁ r₂ |>.1,
            (NonuniformMajority L K).δ r₁ r₂ |>.2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
    have hδ : (NonuniformMajority L K).δ r₁ r₂ = Transition L K r₁ r₂ := rfl
    unfold ClockRealKernel.rBeyond
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub, hδ]
    have hpair_le := rBeyond_pair_le_add_one (L := L) (K := K) T r₁ r₂ h1p h2p h1c h2c
    have hpair_in_le :
        Multiset.countP (fun a => ClockRealKernel.clockBeyondP (L := L) (K := K) T a)
            ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => ClockRealKernel.clockBeyondP (L := L) (K := K) T a) c :=
      Multiset.countP_le_of_le _ hsub
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact Nat.le_succ _

theorem rBeyond_step_unit_increment (T : ℕ) (c c' : Config (AgentState L K))
    (hw : ClockRealKernel.AllClockP3 (L := L) (K := K) c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    ClockRealKernel.rBeyond (L := L) (K := K) T c'
      ≤ ClockRealKernel.rBeyond (L := L) (K := K) T c + 1 := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c =
        (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf
        rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ :=
      Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact rBeyond_stepOrSelf_le_add_one (L := L) (K := K) T c hw r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf
        rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'
    omega

/-! ## Range-indexed GoodClock projection -/

structure ClockFrontQuantileRegime
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) (lastHour : ℕ) : Prop where
  start_exists : ∀ h, h ≤ lastHour →
    ∃ τ, Phase3GoodClock.StartHit (L := L) (K := K) θ h (tr τ)
  end_exists : ∀ h, h ≤ lastHour →
    ∃ τ, Phase3GoodClock.EndHit (L := L) (K := K) θ h (tr τ)
  twoOverC_le_end : ∀ h (hh : h ≤ lastHour),
    Phase3GoodClock.start_h (L := L) (K := K) θ tr h (start_exists h hh) +
        θ.twoOverC ≤
      Phase3GoodClock.end_h (L := L) (K := K) θ tr h (end_exists h hh)
  fortyOne_le_end : ∀ h (hh : h ≤ lastHour),
    Phase3GoodClock.start_h (L := L) (K := K) θ tr h (start_exists h hh) +
        θ.twoOverC + θ.fortyOneOverM ≤
      Phase3GoodClock.end_h (L := L) (K := K) θ tr h (end_exists h hh)
  fortySeven_le_end : ∀ h (hh : h ≤ lastHour),
    Phase3GoodClock.start_h (L := L) (K := K) θ tr h (start_exists h hh) +
        θ.twoOverC + θ.fortySevenOverM ≤
      Phase3GoodClock.end_h (L := L) (K := K) θ tr h (end_exists h hh)
  fortySeven_slack : ∀ h (hh : h ≤ lastHour),
    Phase3GoodClock.start_h (L := L) (K := K) θ tr h (start_exists h hh) +
        θ.twoOverC + θ.fortySevenOverM + 1 ≤
      Phase3GoodClock.end_h (L := L) (K := K) θ tr h (end_exists h hh)
  prev_end_lt_start : ∀ h (hh : h ≤ lastHour), 0 < h →
    Phase3GoodClock.end_h (L := L) (K := K) θ tr (h - 1)
        (end_exists (h - 1) (by omega)) <
      Phase3GoodClock.start_h (L := L) (K := K) θ tr h (start_exists h hh)

def HDomStoppedUpTo (M : ℕ) (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) (lastHour : ℕ)
    (Q : ClockFrontQuantileRegime (L := L) (K := K) θ tr lastHour) : Prop :=
  ∀ h (hh : h ≤ lastHour),
    ∀ τ,
      Phase3GoodClock.start_h (L := L) (K := K) θ tr h (Q.start_exists h hh) +
          θ.twoOverC ≤ τ →
      τ <
        Phase3GoodClock.end_h (L := L) (K := K) θ tr h (Q.end_exists h hh) →
      Phase3GoodClock.hdom (L := L) (K := K) (h + 1) M (tr τ)

structure GoodClockUpTo (M : ℕ) (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) (lastHour : ℕ) : Prop where
  quantile : ClockFrontQuantileRegime (L := L) (K := K) θ tr lastHour
  hdom_stopped : HDomStoppedUpTo (L := L) (K := K) M θ tr lastHour quantile

namespace GoodClockUpTo

noncomputable def start {M : ℕ} {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {lastHour h : ℕ}
    (G : GoodClockUpTo (L := L) (K := K) M θ tr lastHour)
    (hh : h ≤ lastHour) : ℕ :=
  Phase3GoodClock.start_h (L := L) (K := K) θ tr h (G.quantile.start_exists h hh)

noncomputable def finish {M : ℕ} {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {lastHour h : ℕ}
    (G : GoodClockUpTo (L := L) (K := K) M θ tr lastHour)
    (hh : h ≤ lastHour) : ℕ :=
  Phase3GoodClock.end_h (L := L) (K := K) θ tr h (G.quantile.end_exists h hh)

theorem hdom_at_47 {M : ℕ} {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {lastHour h : ℕ}
    (G : GoodClockUpTo (L := L) (K := K) M θ tr lastHour)
    (hh : h ≤ lastHour) :
    Phase3GoodClock.hdom (L := L) (K := K) (h + 1) M
      (tr (G.start hh + θ.twoOverC + θ.fortySevenOverM)) := by
  exact G.hdom_stopped h hh
    (G.start hh + θ.twoOverC + θ.fortySevenOverM)
    (by simp [start])
    (by
      have hslack := G.quantile.fortySeven_slack h hh
      simp [start] at hslack ⊢
      omega)

end GoodClockUpTo

structure GoodClockRegime
    (M : ℕ) (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) (lastHour : ℕ) : Prop where
  quantile : ClockFrontQuantileRegime (L := L) (K := K) θ tr lastHour
  hdom : HDomStoppedUpTo (L := L) (K := K) M θ tr lastHour quantile

theorem goodClockUpTo_of_regime {M : ℕ} {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {lastHour : ℕ}
    (R : GoodClockRegime (L := L) (K := K) M θ tr lastHour) :
    GoodClockUpTo (L := L) (K := K) M θ tr lastHour where
  quantile := R.quantile
  hdom_stopped := R.hdom

/-- Global form matching the current `Phase3Core` interface.  The preferred
producer is `GoodClockUpTo`; this all-hours wrapper is only the projection needed
by `CoreClockInputs.ofGoodClock`. -/
structure GoodClockAllRegime
    (M : ℕ) (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) : Prop where
  start_exists : ∀ h,
    ∃ τ, Phase3GoodClock.StartHit (L := L) (K := K) θ h (tr τ)
  end_exists : ∀ h,
    ∃ τ, Phase3GoodClock.EndHit (L := L) (K := K) θ h (tr τ)
  twoOverC_le_end : ∀ h,
    Phase3GoodClock.start_h (L := L) (K := K) θ tr h (start_exists h) +
        θ.twoOverC ≤
      Phase3GoodClock.end_h (L := L) (K := K) θ tr h (end_exists h)
  fortyOne_le_end : ∀ h,
    Phase3GoodClock.start_h (L := L) (K := K) θ tr h (start_exists h) +
        θ.twoOverC + θ.fortyOneOverM ≤
      Phase3GoodClock.end_h (L := L) (K := K) θ tr h (end_exists h)
  fortySeven_le_end : ∀ h,
    Phase3GoodClock.start_h (L := L) (K := K) θ tr h (start_exists h) +
        θ.twoOverC + θ.fortySevenOverM ≤
      Phase3GoodClock.end_h (L := L) (K := K) θ tr h (end_exists h)
  prev_end_lt_start : ∀ h, 0 < h →
    Phase3GoodClock.end_h (L := L) (K := K) θ tr (h - 1) (end_exists (h - 1)) <
      Phase3GoodClock.start_h (L := L) (K := K) θ tr h (start_exists h)
  hdom_stopped : ∀ h,
    Phase3GoodClock.HDomStopped (L := L) (K := K) (h + 1) M
      (Phase3GoodClock.start_h (L := L) (K := K) θ tr h (start_exists h) +
        θ.twoOverC)
      (Phase3GoodClock.end_h (L := L) (K := K) θ tr h (end_exists h)) tr

noncomputable def goodClock_of_allRegime
    {M : ℕ} {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (R : GoodClockAllRegime (L := L) (K := K) M θ tr) :
    Phase3GoodClock.GoodClock (L := L) (K := K) M θ tr where
  start_exists := R.start_exists
  end_exists := R.end_exists
  twoOverC_le_end := R.twoOverC_le_end
  fortyOne_le_end := R.fortyOne_le_end
  fortySeven_le_end := R.fortySeven_le_end
  prev_end_lt_start := R.prev_end_lt_start
  hdom_stopped := R.hdom_stopped

noncomputable def coreClockInputs_of_allRegime
    {M : ℕ} {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (R : GoodClockAllRegime (L := L) (K := K) M θ tr) (h : ℕ) :
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h :=
  Phase3GoodClock.CoreClockInputs.ofGoodClock (L := L) (K := K) M h
    (goodClock_of_allRegime (L := L) (K := K) R)

namespace Phase3GoodClock
namespace CoreClockInputs

/-- Range-local projection from `GoodClockUpTo` into the facts consumed by one
Core row.  This is the honest replacement for projecting through an all-hours
`GoodClock` when the row satisfies `h ≤ lastHour`. -/
noncomputable def ofGoodClockUpTo
    {M : ℕ} {θ : ClockTimingParams} {tr : Trace L K}
    {lastHour h : ℕ} (hh : h ≤ lastHour)
    (G : Phase3GoodClockRegime.GoodClockUpTo
      (L := L) (K := K) M θ tr lastHour) :
    CoreClockInputs (L := L) (K := K) θ tr h where
  M := M
  start := G.start hh
  finish := G.finish hh
  prevFinish :=
    if hp : 0 < h then
      G.finish (by omega : h - 1 ≤ lastHour)
    else
      0
  h13_start_bulk := by
    simpa [Phase3GoodClockRegime.GoodClockUpTo.start] using
      (start_h_firstHit (L := L) (K := K) θ tr h
        (G.quantile.start_exists h hh)).hit
  tiny_until_finish := by
    intro τ hτ
    have hnot : ¬ EndHit (L := L) (K := K) θ h (tr τ) :=
      (end_h_firstHit (L := L) (K := K) θ tr h
        (G.quantile.end_exists h hh)).first τ (by
          simpa [Phase3GoodClockRegime.GoodClockUpTo.finish] using hτ)
    exact Nat.lt_of_not_ge hnot
  h13_hdom_start := by
    exact G.hdom_stopped h hh (G.start hh + θ.twoOverC)
      (by simp [Phase3GoodClockRegime.GoodClockUpTo.start])
      (by
        have hslack := G.quantile.fortySeven_slack h hh
        simp [Phase3GoodClockRegime.GoodClockUpTo.start] at hslack ⊢
        omega)
  h15_hdom_41 := by
    exact G.hdom_stopped h hh
      (G.start hh + θ.twoOverC + θ.fortyOneOverM)
      (by simp [Phase3GoodClockRegime.GoodClockUpTo.start])
      (by
        have h41 := θ.fortyOne_le_fortySeven
        have hslack := G.quantile.fortySeven_slack h hh
        simp [Phase3GoodClockRegime.GoodClockUpTo.start] at hslack ⊢
        omega)
  h16_hdom_47 := by
    exact G.hdom_stopped h hh
      (G.start hh + θ.twoOverC + θ.fortySevenOverM)
      (by simp [Phase3GoodClockRegime.GoodClockUpTo.start])
      (by
        have hslack := G.quantile.fortySeven_slack h hh
        simp [Phase3GoodClockRegime.GoodClockUpTo.start] at hslack ⊢
        omega)
  fortyOne_inside := G.quantile.fortyOne_le_end h hh
  fortySeven_inside := G.quantile.fortySeven_le_end h hh
  previous_hour_finished := by
    intro hp
    simpa [hp] using G.quantile.prev_end_lt_start h hh hp

end CoreClockInputs
end Phase3GoodClock

/-! ## Honest probabilistic wrapper -/

abbrev ClockFrontQuantileTail
    (μ : Measure (Phase3GoodClock.Trace L K))
    (θ : Phase3GoodClock.ClockTimingParams) (lastHour : ℕ) (ε : ℝ≥0∞) : Prop :=
  μ {tr | ¬ ClockFrontQuantileRegime (L := L) (K := K) θ tr lastHour} ≤ ε

theorem clock_front_quantile_regime_whp
    {μ : Measure (Phase3GoodClock.Trace L K)}
    {θ : Phase3GoodClock.ClockTimingParams} {lastHour : ℕ} {ε : ℝ≥0∞}
    (h :
      ClockFrontQuantileTail (L := L) (K := K) μ θ lastHour ε) :
    μ {tr | ¬ ClockFrontQuantileRegime (L := L) (K := K) θ tr lastHour} ≤ ε :=
  h

def HDomFailureUpTo (M : ℕ) (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) (lastHour : ℕ) : Prop :=
  ∀ Q : ClockFrontQuantileRegime (L := L) (K := K) θ tr lastHour,
    ¬ HDomStoppedUpTo (L := L) (K := K) M θ tr lastHour Q

theorem goodClock_regime_whp
    {μ : Measure (Phase3GoodClock.Trace L K)}
    {M : ℕ} {θ : Phase3GoodClock.ClockTimingParams}
    {lastHour : ℕ} {εq εh ε : ℝ≥0∞}
    (hquant :
      μ {tr | ¬ ClockFrontQuantileRegime (L := L) (K := K) θ tr lastHour} ≤ εq)
    (hhdom :
      μ {tr | HDomFailureUpTo (L := L) (K := K) M θ tr lastHour} ≤ εh)
    (hbudget : εq + εh ≤ ε) :
    μ {tr | ¬ GoodClockUpTo (L := L) (K := K) M θ tr lastHour} ≤ ε := by
  classical
  have hsub :
      {tr | ¬ GoodClockUpTo (L := L) (K := K) M θ tr lastHour} ⊆
        {tr | ¬ ClockFrontQuantileRegime (L := L) (K := K) θ tr lastHour} ∪
          {tr | HDomFailureUpTo (L := L) (K := K) M θ tr lastHour} := by
    intro tr hbad
    by_cases hq : ClockFrontQuantileRegime (L := L) (K := K) θ tr lastHour
    · right
      intro Q hQ
      exact hbad ⟨Q, hQ⟩
    · left
      exact hq
  calc
    μ {tr | ¬ GoodClockUpTo (L := L) (K := K) M θ tr lastHour}
        ≤ μ ({tr | ¬ ClockFrontQuantileRegime (L := L) (K := K) θ tr lastHour} ∪
            {tr | HDomFailureUpTo (L := L) (K := K) M θ tr lastHour}) :=
      measure_mono hsub
    _ ≤ μ {tr | ¬ ClockFrontQuantileRegime (L := L) (K := K) θ tr lastHour} +
          μ {tr | HDomFailureUpTo (L := L) (K := K) M θ tr lastHour} :=
      measure_union_le _ _
    _ ≤ εq + εh :=
      add_le_add hquant hhdom
    _ ≤ ε := hbudget

#print axioms hourFront_eq_rBeyond
#print axioms beyondHour_eq_rBeyond
#print axioms stdTheta
#print axioms firstHit_small_lt_bulk_of_mono_unit
#print axioms rBeyond_step_unit_increment
#print axioms goodClockUpTo_of_regime
#print axioms goodClock_of_allRegime
#print axioms coreClockInputs_of_allRegime
#print axioms clock_front_quantile_regime_whp
#print axioms goodClock_regime_whp

end Phase3GoodClockRegime

end ExactMajority
