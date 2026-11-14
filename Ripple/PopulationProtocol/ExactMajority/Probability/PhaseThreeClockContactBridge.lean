import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockContactMGF

/-!
# From the guard rows to the P14 bad events (N12, step 4, deterministic bridge)

On the virtual path from an asynchronous entry, the step-3 rows (activation, passage,
shape) and the cap row determine the top-level times `first_Q ≤ bulk_Q ≤ high_Q ≤ cap`
and the lengths of the P14 windows. This file shows that when the contact row fails
while the two passage events of `PhaseThreeClockCapPassages` hold, some seed Clock `i₀`
lies in the MGF bad event `tagBad` with the P14 budgets:

* `eligible_le_windowCount`: the eligible contacts of `i₀` from its initialization to
  `cap + T_set` are tagged participations on the local or the settling window (an
  eligible contact has a capped partner, so the top level is positive, and it occurs
  before `cap + T_set`);
* `local_pairs_le`: the Clock pairs on the local window are those of
  `[first_Q, bulk_Q)` (at most `localTickBudget`, by `tick_local` once the activation is
  known to precede the first cap, from `bulk_width` and `activation_before_twenty`)
  plus those of `[bulk_Q, high_Q)` (fewer than `13 C` outside `bulkHighBad`);
* `settle_length_le`: the settling window has length `cap + T_set - high_Q`, at most
  `finWindow + T_set` outside every `highAllBad j` (all Clocks capped by
  `high_Q + finWindow` force the cap).

The numerical input is `2 · frontWidth C + 20 ≤ clockTop n` at the population
threshold (`PhaseThreeModel.Numeric.frontWidth_bounds`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockContactBridge

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne PhaseThreeClockEmbedding
  PhaseThreeClockEmbeddingBridge PhaseThreeClockCore PhaseThreeClockRows
  PhaseThreeClockProductTails PhaseThreeScalar PhaseThreeClockPrefixTails
  PhaseThreeClockProbabilityFloors PhaseThreeClockRegime PhaseThreeClockCapSpread
  PhaseThreeClockCapPassages PhaseThreeClockContactMGF
open StageEventSpec hiding frontCount clockCount
open Classical

variable {n : ℕ} (init : InputCfg n)

/-- The raw-step allowance of the final cap spread, `⌈4 n² ln n / C⌉` (P14, from the
`⌈4 C ln n⌉` ticks at the Clock-pair rate `C² / n²`). -/
def finWindow (n C : ℕ) : ℕ :=
  Nat.ceil (4 * (n : ℝ) ^ 2 * Real.log (n : ℝ) / (C : ℝ))

/-! ## First-hit bookkeeping -/

theorem firstAfter_congr_of_ge {P P' : ℕ → Prop} {S u : ℕ} (h : ∀ v, S ≤ v → (P v ↔ P' v))
    (hP : firstAfter P S u) : firstAfter P' S u :=
  ⟨hP.1, (h u hP.1).mp hP.2.1, fun v hSv hvu hP'v => hP.2.2 v hSv hvu ((h v hSv).mpr hP'v)⟩

theorem exists_firstAfter {P : ℕ → Prop} {S t : ℕ} (hSt : S ≤ t) (ht : P t) :
    ∃ u, firstAfter P S u := by
  classical
  have hex : ∃ u, S ≤ u ∧ P u := ⟨t, hSt, ht⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro u hSu hlt hPu
  exact Nat.find_min hex hlt ⟨hSu, hPu⟩

theorem firstAfter_le_of {P : ℕ → Prop} {S u t : ℕ} (hP : firstAfter P S u) (hSt : S ≤ t)
    (ht : P t) : u ≤ t := by
  by_contra hlt
  exact hP.2.2 t hSt (by omega) ht

/-! ## Sums over `Ioc` and `Ico` -/

theorem sum_Ioc_eq_sum_Ico_succ (f : ℕ → ℕ) (a b : ℕ) :
    ∑ k ∈ Finset.Ioc a b, f k = ∑ t ∈ Finset.Ico a b, f (t + 1) := by
  induction b with
  | zero => simp
  | succ b ih =>
      by_cases hab : a ≤ b
      · rw [Finset.sum_Ioc_succ_top hab, Finset.sum_Ico_succ_top hab, ih]
      · have h1 : Finset.Ioc a (b + 1) = ∅ := Finset.Ioc_eq_empty (by omega)
        have h2 : Finset.Ico a (b + 1) = ∅ := Finset.Ico_eq_empty (by omega)
        rw [h1, h2]
        simp

theorem windowCount_congr {P R : ℕ → InputLog n → Prop} (s N : ℕ) (ω : InputLog n)
    (h : ∀ t, s ≤ t → (P t ω ↔ R t ω)) :
    windowCount P s N ω = windowCount R s N ω := by
  unfold windowCount
  apply Finset.sum_congr rfl
  intro u _
  simp only [h (s + u) (Nat.le_add_right s u)]

/-! ## The virtual path from a guarded entry -/

variable (ω : InputLog n)

section Guard

variable {s T : ℕ}

/-- The row front count at level `ℓ` is antitone in `ℓ`. -/
theorem frontCountL_anti (fS fv : Lab init) {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ') :
    frontCountL init fS fv ℓ' ≤ frontCountL init fS fv ℓ := by
  unfold frontCountL labelCount
  rw [Finset.card_filter, Finset.card_filter]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, le_trans h h1.2⟩ h2
  · exact Nat.zero_le _
  · exact le_rfl

theorem effectiveMinuteL_le_clockTop (fv : Lab init) (i : Fin init.card) :
    effectiveMinuteL init fv i ≤ clockTop n := by
  unfold effectiveMinuteL
  split_ifs
  · exact minute_le_clockTop _
  · exact Nat.zero_le _

/-- `Finset.mem_filter` with the decidability instance taken from the term. -/
theorem mem_filter_any {α : Type*} {p : α → Prop} (inst : DecidablePred p) {s : Finset α}
    {a : α} : a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p inst s a

/-- When some Clock is at the cap, the row front height is the cap. -/
theorem frontHeightL_eq_clockTop (fS fv : Lab init)
    (h : 1 ≤ frontCountL init fS fv (clockTop n)) :
    frontHeightL init fS fv = clockTop n := by
  classical
  apply le_antisymm
  · unfold frontHeightL
    apply Finset.sup_le
    intro i _
    exact effectiveMinuteL_le_clockTop init fv i
  · unfold frontCountL labelCount at h
    obtain ⟨i, hi⟩ := Finset.card_pos.mp h
    have hi' := (mem_filter_any _).mp hi
    unfold frontHeightL
    refine le_trans hi'.2.2 (Finset.le_sup (f := effectiveMinuteL init fv) ?_)
    exact (mem_filter_any _).mpr ⟨Finset.mem_univ _, hi'.2.1⟩

/-- A positive row quantile is attained at some level. -/
theorem frontQuantileL_attained (fS fv : Lab init) (b : ℕ)
    (hpos : 0 < frontQuantileL init fS fv b) :
    ∃ ℓ, frontQuantileL init fS fv b ≤ ℓ ∧ ℓ ≤ clockTop n ∧ b ≤ frontCountL init fS fv ℓ := by
  classical
  unfold frontQuantileL at hpos ⊢
  set F := (Finset.range (clockTop n + 1)).filter (fun ell => b ≤ frontCountL init fS fv ell)
    with hF
  have hne : F.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hpos
    simp at hpos
  obtain ⟨ℓ, hℓ, hsup⟩ := Finset.exists_mem_eq_sup F hne id
  rw [hF] at hℓ
  have hℓ' := (mem_filter_any _).mp hℓ
  rw [Finset.mem_range] at hℓ'
  exact ⟨ℓ, le_of_eq hsup, by omega, hℓ'.2⟩

/-- Density of the seed Clock set. -/
theorem seed_clock_density (hentry : AsyncEntry init ω s T) :
    6 * n ≤ 25 * clockCount (virtualLabels init ω s) := by
  have h := (seed_density init ω hentry).2.2.1
  rw [← virtualCfg_clockCount_eq_seed init ω hentry s le_rfl, clockCount_virtualCfg_eq] at h
  exact h

theorem seed_clock_le : clockCount (virtualLabels init ω s) ≤ init.card :=
  clockCount_le_card _

theorem pos_of_threshold (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) : 0 < n := by
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h := (PhaseThreeModel.Numeric.logarithmic_inputs hn
    (show (6 / 25 : ℝ) * n ≤ n by linarith) le_rfl).1
  exact_mod_cast h

theorem one_le_seed_clock (hentry : AsyncEntry init ω s T)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) :
    1 ≤ clockCount (virtualLabels init ω s) := by
  have h := seed_clock_density init ω hentry
  have h0 := pos_of_threshold hn
  omega

theorem one_le_highThreshold {C : ℕ} (hC : 1 ≤ C) : 1 ≤ highThreshold C := by
  unfold highThreshold
  have : (0 : ℝ) < 9 * (C : ℝ) / 10 := by
    have : (1 : ℝ) ≤ C := by exact_mod_cast hC
    linarith
  exact Nat.one_le_iff_ne_zero.mpr (by
    intro h
    rw [Nat.ceil_eq_zero] at h
    linarith)

/-- The numerical input: `2 · frontWidth C + 20 ≤ clockTop n` at the population threshold. -/
theorem width_lt_clockTop (hentry : AsyncEntry init ω s T)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (hcard : init.card = n) :
    2 * frontWidth (clockCount (virtualLabels init ω s)) + 20 ≤ clockTop n := by
  set C := clockCount (virtualLabels init ω s) with hC
  have hdens := seed_clock_density init ω hentry
  have hle : C ≤ n := by
    have h := seed_clock_le init ω (s := s)
    omega
  have hlo : (6 / 25 : ℝ) * n ≤ C := by
    have : (6 : ℝ) * n ≤ 25 * C := by exact_mod_cast hdens
    linarith
  obtain ⟨-, hx, hCn, -, -⟩ := PhaseThreeModel.Numeric.logarithmic_inputs hn hlo
    (by exact_mod_cast hle)
  obtain ⟨-, hw1, hw2⟩ := PhaseThreeModel.Numeric.frontWidth_bounds hx
  have hlogn : 0 ≤ Real.log (n : ℝ) := by linarith
  have hH : Real.log (n : ℝ) ≤ (PhaseThreeModel.Numeric.hourIndex n : ℝ) := by
    rw [PhaseThreeModel.Numeric.hourIndex_eq_real_ceiling]
    have hl2 := PhaseThreeModel.Numeric.log_two_bounds
    have hpos : 0 < Real.log 2 := by linarith
    have h1 : Real.log (n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
      rw [le_div_iff₀ hpos]
      nlinarith
    exact h1.trans (Nat.le_ceil _)
  have hw : (frontWidth C : ℝ) ≤ Real.log (C : ℝ) / 1048576 := hw1.trans hw2
  have hH0 : (0 : ℝ) ≤ PhaseThreeModel.Numeric.hourIndex n := Nat.cast_nonneg _
  have hreal : 2 * (frontWidth C : ℝ) + 20 ≤
      256 * ((PhaseThreeModel.Numeric.hourIndex n : ℝ) + 1) := by
    have h2 : 2 * (frontWidth C : ℝ) + 20 ≤ Real.log (C : ℝ) := by linarith
    linarith
  have hnat : 2 * frontWidth C + 20 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1) := by
    exact_mod_cast hreal
  exact hnat

/-- The activation precedes the first cap: at the first cap the bulk quantile is within
`2 w` of the cap, so the bulk threshold is reached at level `20`, which the activation
precedes. -/
theorem activation_le_first (hentry : AsyncEntry init ω s T)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (hcard : init.card = n) (hact : activationRow init ω s T) (hpass : passageRow init ω s T)
    (hshape : shapeRow init ω s T) :
    (virtualTimes init ω s).activation ≤ (virtualTimes init ω s).first (clockTop n) := by
  set w := virtualTimes init ω s with hw
  have hfirst := hpass.level_first (clockTop n) one_le_clockTop le_rfl
  have hf1cap := (hpass.level_before_cap (clockTop n) le_rfl).1
  have hsf := hfirst.1
  have hC : StageEventSpec.clockCount (virtualCfg init ω s) =
      clockCount (virtualLabels init ω s) := clockCount_virtualCfg_eq init ω s
  have hwidth := hshape.bulk_width (w.first (clockTop n)) hsf hf1cap
  rw [hC] at hwidth
  have hheight := frontHeightL_eq_clockTop init _ _ hfirst.2.1
  rw [hheight] at hwidth
  have hnum := width_lt_clockTop init ω hentry hn hcard
  have hqpos : 0 < frontQuantileL init (virtualLabels init ω s)
      (virtualLabels init ω (w.first (clockTop n)))
      (bulkThreshold (clockCount (virtualLabels init ω s))) := by omega
  obtain ⟨ℓ, hℓq, -, hℓb⟩ := frontQuantileL_attained init _ _ _ hqpos
  have h20 : 20 ≤ ℓ := by omega
  have hb20 : bulkThreshold (clockCount (virtualLabels init ω s)) ≤
      frontCountL init (virtualLabels init ω s) (virtualLabels init ω (w.first (clockTop n))) 20 :=
    hℓb.trans (frontCountL_anti init _ _ h20)
  have hbulk := hpass.level_bulk 20 (by norm_num) (by unfold clockTop; omega)
  rw [hC] at hbulk
  have hb : w.bulk 20 ≤ w.first (clockTop n) := firstAfter_le_of hbulk hsf hb20
  exact hact.activation_before_twenty.trans hb

/-- Every seed Clock is in Phase 3 from the first cap on. -/
theorem clock_phase_three_of_first (hentry : AsyncEntry init ω s T)
    (hact : activationRow init ω s T) (i : Fin init.card)
    (hi : (virtualLabels init ω s i).role = .clock) {u : ℕ}
    (hu : (virtualTimes init ω s).first (clockTop n) ≤ u) :
    (virtualLabels init ω u i).phase.val = 3 := by
  have hfirst := hact.initialized_first i hi
  have h3 : 3 ≤ (virtualLabels init ω ((virtualTimes init ω s).initialized i) i).phase.val :=
    hfirst.1
  have hinit : s ≤ (virtualTimes init ω s).initialized i := by
    by_contra hlt
    have hlt' : (virtualTimes init ω s).initialized i < s := Nat.lt_of_not_le hlt
    have hagree := virtualLabels_eq_labelsAt_through_asyncEntry init ω s T hentry
    have hsT := hentry.order
    rw [hagree _ (by omega)] at h3
    have hlow := hentry.first_phase_seed.2 _ hlt' _
      (labelsAt_mem_trace init ω ((virtualTimes init ω s).initialized i) i)
    omega
  have hbefore := hact.initialized_before_first_cap i hi
  exact clock_phase_three_after init ω hentry i hi hinit h3 (by omega)

/-! ## The top-level times -/

/-- The first positive top count, the bulk top count and the cap are first hits of
`ReachedTop`/`AllCapAt`. -/
theorem first_top_firstAfter (hentry : AsyncEntry init ω s T) (hpass : passageRow init ω s T) :
    firstAfter (fun v => ReachedTop init 1 v ω) s ((virtualTimes init ω s).first (clockTop n)) := by
  refine firstAfter_congr_of_ge (fun v hsv => ?_)
    (hpass.level_first (clockTop n) one_le_clockTop le_rfl)
  unfold ReachedTop
  rw [frontCountL_top_eq init ω hentry v hsv]

theorem bulk_top_firstAfter (hentry : AsyncEntry init ω s T) (hpass : passageRow init ω s T) :
    firstAfter (fun v => ReachedTop init (bulkThreshold (clockCount (virtualLabels init ω s))) v ω)
      s ((virtualTimes init ω s).bulk (clockTop n)) := by
  refine firstAfter_congr_of_ge (fun v hsv => ?_)
    (hpass.level_bulk (clockTop n) one_le_clockTop le_rfl)
  unfold ReachedTop
  rw [frontCountL_top_eq init ω hentry v hsv, clockCount_virtualCfg_eq]

theorem cap_firstAfter (hentry : AsyncEntry init ω s T) (hpass : passageRow init ω s T) :
    firstAfter (fun v => AllCapAt init s v ω) s (virtualTimes init ω s).cap := by
  refine firstAfter_congr_of_ge (fun v hsv => ?_) hpass.cap_first
  unfold AllCapAt
  rw [frontCountL_top_eq init ω hentry v hsv, clockCount_virtualCfg_eq]

theorem highThreshold_le_card (C : ℕ) : highThreshold C ≤ C := by
  unfold highThreshold
  rw [Nat.ceil_le]
  have : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  linarith

theorem bulkThreshold_le_highThreshold (C : ℕ) : bulkThreshold C ≤ highThreshold C := by
  unfold bulkThreshold highThreshold
  apply Nat.ceil_le_ceil
  have : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  linarith

theorem one_le_bulkThreshold {C : ℕ} (hC : 1 ≤ C) : 1 ≤ bulkThreshold C := by
  unfold bulkThreshold
  have : (0 : ℝ) < (C : ℝ) / 10 := by
    have : (1 : ℝ) ≤ C := by exact_mod_cast hC
    linarith
  exact Nat.one_le_iff_ne_zero.mpr (by
    intro h
    rw [Nat.ceil_eq_zero] at h
    linarith)

/-- All seed Clocks capped at `t` gives the all-cap state. -/
theorem allCapAt_of_all_capped (hentry : AsyncEntry init ω s T) (t : ℕ) (hst : s ≤ t)
    (hall : ∀ j, (virtualLabels init ω s j).role = .clock →
      Capped init (virtualLabels init ω t) j) :
    AllCapAt init s t ω := by
  classical
  unfold AllCapAt
  rw [topCount_eq_card_capped]
  unfold clockCount clockSet
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hcap
    have hr := ((capped_iff init _ j).mp hcap).1
    have hroles := virtualLabels_roles_fixed_of_asyncEntry init ω s T hentry
    rw [hroles t hst j, ← hroles s le_rfl j] at hr
    exact hr
  · intro hj
    exact hall j hj

/-! ## The three count bounds -/

section Counts

theorem card_eq_clockCount (C : Finset (Fin init.card))
    (hC : C = clockSet (virtualLabels init ω s)) : C.card = clockCount (virtualLabels init ω s) := by
  rw [hC]
  rfl

theorem clockCount_eq_at (hentry : AsyncEntry init ω s T) (C : Finset (Fin init.card))
    (hC : C = clockSet (virtualLabels init ω s)) (t : ℕ) (hst : s ≤ t) :
    clockCount (virtualLabels init ω t) = C.card := by
  rw [card_eq_clockCount init ω C hC, clockCount_virtual_eq_seed init ω hentry t hst]

theorem role_clock_at (hentry : AsyncEntry init ω s T) (i : Fin init.card)
    (hi : (virtualLabels init ω s i).role = .clock)
    (t : ℕ) (hst : s ≤ t) : (virtualLabels init ω t i).role = .clock := by
  have hroles := virtualLabels_roles_fixed_of_asyncEntry init ω s T hentry
  rw [hroles t hst i, ← hroles s le_rfl i]
  exact hi

/-- An eligible contact at `k` is a tagged participation on the local or the settling
window at `k - 1`. -/
theorem eligible_le_windowCount (hentry : AsyncEntry init ω s T) (C : Finset (Fin init.card))
    (hC : C = clockSet (virtualLabels init ω s)) (N : ℕ) (i₀ : Fin init.card)
    (hi₀ : (virtualLabels init ω s i₀).role = .clock) (k : ℕ) {cp : ℕ}
    (hcapfirst : firstAfter (fun v => AllCapAt init s v ω) s cp) {a b : ℕ} (hsa : s ≤ a)
    (hbN : b ≤ s + N) (hbcap : b ≤ cp + k) :
    eligibleContactsL init (virtualLabels init ω) (drawLabels init ω) s i₀ a b ≤
      windowCount (fun t ω =>
        (ω ∈ localWindow init C i₀ t ∨ ω ∈ settleWindow init C s i₀ k t) ∧
          StepEvent init (TagPair init i₀) t ω) s N ω := by
  classical
  by_cases hab : a ≤ b
  · set Wtag : ℕ → InputLog n → Prop := fun t ω =>
      (ω ∈ localWindow init C i₀ t ∨ ω ∈ settleWindow init C s i₀ k t) ∧
        StepEvent init (TagPair init i₀) t ω with hWtag
    have hterm : ∀ k', a < k' → k' ≤ b →
        eligibleContactL init (virtualLabels init ω) (drawLabels init ω) s i₀ k' →
        Wtag (k' - 1) ω := by
      intro k' hak' hk'b helig
      obtain ⟨hk'pos, j, l, hd, hmem, hjr, hlr, hj3, hl3, hjm, hlm⟩ := helig
      set t := k' - 1 with ht
      have hst : s ≤ t := by omega
      have hk't : k' = t + 1 := by omega
      rw [hk't] at hd
      have hroles := virtualLabels_roles_fixed_of_asyncEntry init ω s T hentry
      have hjr' : (virtualLabels init ω t j).role = .clock := by
        rw [hroles t hst j, ← hroles s le_rfl j]; exact hjr
      have hlr' : (virtualLabels init ω t l).role = .clock := by
        rw [hroles t hst l, ← hroles s le_rfl l]; exact hlr
      have htag : StepEvent init (TagPair init i₀) t ω := by
        refine ⟨j, l, hd, ⟨hjr', hlr'⟩, ?_⟩
        rcases hmem with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      have hcapj : Capped init (virtualLabels init ω t) j := by
        rw [capped_iff]
        refine ⟨hjr', ?_⟩
        rw [effMinute_eq_minute_of_three _ hj3, hjm]
      have hone : ReachedTop init 1 t ω := by
        unfold ReachedTop
        rw [topCount_eq_card_capped]
        exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcapj⟩⟩
      have hCt := clockCount_eq_at init ω hentry C hC t hst
      have hi₀t := role_clock_at init ω hentry i₀ hi₀ t hst
      refine ⟨?_, htag⟩
      by_cases hhigh : ReachedTop init (highThreshold C.card) t ω
      · right
        refine ⟨hCt, hi₀t, hhigh, ?_⟩
        intro v hsv hvk hall
        have hcpv : cp ≤ v := firstAfter_le_of hcapfirst hsv hall
        omega
      · left
        exact ⟨hCt, hi₀t, hone, hhigh⟩
    calc eligibleContactsL init (virtualLabels init ω) (drawLabels init ω) s i₀ a b
        = ∑ k' ∈ Finset.Ioc a b,
            if eligibleContactL init (virtualLabels init ω) (drawLabels init ω) s i₀ k'
            then 1 else 0 := by
          unfold eligibleContactsL
          rw [Finset.card_filter]
      _ ≤ ∑ k' ∈ Finset.Ioc a b, if Wtag (k' - 1) ω then 1 else 0 := by
          apply Finset.sum_le_sum
          intro k' hk'
          rw [Finset.mem_Ioc] at hk'
          split_ifs with h1 h2 h2
          · exact le_rfl
          · exact absurd (hterm k' hk'.1 hk'.2 h1) h2
          · exact Nat.zero_le _
          · exact le_rfl
      _ = ∑ t ∈ Finset.Ico a b, if Wtag (t + 1 - 1) ω then 1 else 0 :=
          sum_Ioc_eq_sum_Ico_succ (fun k' => if Wtag (k' - 1) ω then 1 else 0) a b
      _ = ∑ t ∈ Finset.Ico a b, if Wtag t ω then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Nat.add_sub_cancel]
      _ = windowCount (fun t ω => a ≤ t ∧ t < b ∧ Wtag t ω) s N ω := by
          rw [windowCount_interval Wtag s N ω hsa hab hbN]
          exact Finset.sum_congr rfl (fun t _ => by congr 1)
      _ ≤ windowCount Wtag s N ω := windowCount_mono (fun t ω h => h.2.2) s N ω
  · have hempty : Finset.Ioc a b = ∅ := Finset.Ioc_eq_empty (by omega)
    unfold eligibleContactsL
    rw [hempty, Finset.filter_empty, Finset.card_empty]
    exact Nat.zero_le _

/-- The Clock pairs on `[a, b)` in the row language are the Clock-pair step events. -/
theorem clockContactsL_eq_sum (hentry : AsyncEntry init ω s T) {a b : ℕ} (hsa : s ≤ a) :
    clockContactsL init (virtualLabels init ω s) (drawLabels init ω) a b =
      ∑ t ∈ Finset.Ico a b, if StepEvent init (CCPair init) t ω then 1 else 0 := by
  classical
  unfold clockContactsL
  rw [Finset.card_filter, sum_Ioc_eq_sum_Ico_succ]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_Ico] at ht
  have hroles := virtualLabels_roles_fixed_of_asyncEntry init ω s T hentry
  have hiff : clockContactL init (virtualLabels init ω s) (drawLabels init ω) (t + 1) ↔
      StepEvent init (CCPair init) t ω := by
    unfold clockContactL StepEvent CCPair fixedRoleL
    constructor
    · rintro ⟨i, j, hd, hi, hj⟩
      refine ⟨i, j, hd, ?_, ?_⟩
      · rw [hroles t (by omega) i, ← hroles s le_rfl i]; exact hi
      · rw [hroles t (by omega) j, ← hroles s le_rfl j]; exact hj
    · rintro ⟨i, j, hd, hi, hj⟩
      refine ⟨i, j, hd, ?_, ?_⟩
      · rw [hroles t (by omega) i, ← hroles s le_rfl i] at hi; exact hi
      · rw [hroles t (by omega) j, ← hroles s le_rfl j] at hj; exact hj
  simp only [hiff]

/-- The local window is `[first_Q, high_Q)` after the seed. -/
theorem localWindow_iff (hentry : AsyncEntry init ω s T) (C : Finset (Fin init.card))
    (hC : C = clockSet (virtualLabels init ω s)) (i₀ : Fin init.card)
    (hi₀ : (virtualLabels init ω s i₀).role = .clock)
    {f1 hq : ℕ} (hf1 : firstAfter (fun v => ReachedTop init 1 v ω) s f1)
    (hhq : firstAfter (fun v => ReachedTop init (highThreshold C.card) v ω) s hq)
    (t : ℕ) (hst : s ≤ t) :
    ω ∈ localWindow init C i₀ t ↔ f1 ≤ t ∧ t < hq := by
  unfold localWindow
  simp only [Set.mem_setOf_eq]
  rw [firstAfter_reachedTop_iff init ω hentry 1 hf1 hst,
    firstAfter_reachedTop_iff init ω hentry _ hhq hst]
  constructor
  · rintro ⟨-, -, h1, h2⟩
    exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨clockCount_eq_at init ω hentry C hC t hst, role_clock_at init ω hentry i₀ hi₀ t hst,
      h1, by omega⟩

/-- The bulk-high window is `[bulk_Q, high_Q)` after the seed. -/
theorem bulkHighWindow_iff (hentry : AsyncEntry init ω s T) (C : Finset (Fin init.card))
    (hC : C = clockSet (virtualLabels init ω s)) {b1 hq : ℕ}
    (hb1 : firstAfter (fun v => ReachedTop init (bulkThreshold C.card) v ω) s b1)
    (hhq : firstAfter (fun v => ReachedTop init (highThreshold C.card) v ω) s hq)
    (t : ℕ) (hst : s ≤ t) :
    ω ∈ bulkHighWindow init C t ↔ b1 ≤ t ∧ t < hq := by
  unfold bulkHighWindow
  simp only [Set.mem_setOf_eq]
  rw [firstAfter_reachedTop_iff init ω hentry _ hb1 hst,
    firstAfter_reachedTop_iff init ω hentry _ hhq hst]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨clockCount_eq_at init ω hentry C hC t hst, h1, by omega⟩

/-- The settling window is `[high_Q, cap + k)` after the seed. -/
theorem settleWindow_iff (hentry : AsyncEntry init ω s T) (C : Finset (Fin init.card))
    (hC : C = clockSet (virtualLabels init ω s)) (i₀ : Fin init.card)
    (hi₀ : (virtualLabels init ω s i₀).role = .clock)
    {hq cp : ℕ}
    (hhq : firstAfter (fun v => ReachedTop init (highThreshold C.card) v ω) s hq)
    (hcapfirst : firstAfter (fun v => AllCapAt init s v ω) s cp) (k t : ℕ) (hst : s ≤ t) :
    ω ∈ settleWindow init C s i₀ k t ↔ hq ≤ t ∧ t < cp + k := by
  unfold settleWindow
  simp only [Set.mem_setOf_eq]
  rw [firstAfter_reachedTop_iff init ω hentry _ hhq hst]
  constructor
  · rintro ⟨-, -, h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra hge
    exact h2 cp hcapfirst.1 (by omega) hcapfirst.2.1
  · rintro ⟨h1, h2⟩
    refine ⟨clockCount_eq_at init ω hentry C hC t hst, role_clock_at init ω hentry i₀ hi₀ t hst,
      h1, ?_⟩
    intro v hsv hvk hall
    have := firstAfter_le_of hcapfirst hsv hall
    omega

/-- The Clock pairs on the local window: `tick_local` on `[first_Q, bulk_Q)` and the P1
count on `[bulk_Q, high_Q)`. -/
theorem local_pairs_le (hentry : AsyncEntry init ω s T) (C : Finset (Fin init.card))
    (hC : C = clockSet (virtualLabels init ω s)) (N : ℕ)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (hcard : init.card = n) (hact : activationRow init ω s T) (hpass : passageRow init ω s T)
    (hshape : shapeRow init ω s T) (i₀ : Fin init.card)
    (hi₀ : (virtualLabels init ω s i₀).role = .clock) {hq : ℕ}
    (hhq : firstAfter (fun v => ReachedTop init (highThreshold C.card) v ω) s hq)
    (hhqN : hq ≤ s + N) (hP1 : ω ∉ bulkHighBad init C s N) :
    windowCount
      (fun t ω => ω ∈ localWindow init C i₀ t ∧ StepEvent init (CCPair init) t ω) s N ω ≤
      localTickBudget C.card + 13 * C.card := by
  classical
  set w := virtualTimes init ω s with hw
  have hcardC := card_eq_clockCount init ω C hC
  have hf1 := first_top_firstAfter init ω hentry hpass
  have hb1 := bulk_top_firstAfter init ω hentry hpass
  rw [← hcardC] at hb1
  have hsf1 : s ≤ w.first (clockTop n) := hf1.1
  have hf1b1 : w.first (clockTop n) ≤ w.bulk (clockTop n) := by
    apply firstAfter_le_of hf1 hb1.1
    exact le_trans (one_le_bulkThreshold (by
      rw [hcardC]; exact one_le_seed_clock init ω hentry hn)) hb1.2.1
  have hb1hq : w.bulk (clockTop n) ≤ hq := by
    apply firstAfter_le_of hb1 hhq.1
    exact le_trans (bulkThreshold_le_highThreshold _) hhq.2.1
  -- the window count as a sum over `[first_Q, high_Q)`
  have hcongr := windowCount_congr
    (P := fun t ω => ω ∈ localWindow init C i₀ t ∧ StepEvent init (CCPair init) t ω)
    (R := fun t ω => w.first (clockTop n) ≤ t ∧ t < hq ∧ StepEvent init (CCPair init) t ω)
    s N ω (fun t hst => by
    dsimp only
    rw [localWindow_iff init ω hentry C hC i₀ hi₀ hf1 hhq t hst]
    tauto)
  rw [hcongr, windowCount_interval _ s N ω hsf1 (hf1b1.trans hb1hq) hhqN,
    ← Finset.sum_Ico_consecutive _ hf1b1 hb1hq]
  -- first part: `tick_local`
  have hpart1 : (∑ t ∈ Finset.Ico (w.first (clockTop n)) (w.bulk (clockTop n)),
      if StepEvent init (CCPair init) t ω then 1 else 0) ≤ localTickBudget C.card := by
    rw [← clockContactsL_eq_sum init ω hentry hsf1]
    have htick := hshape.tick_local (clockTop n) one_le_clockTop le_rfl
    rw [max_eq_left (activation_le_first init ω hentry hn hcard hact hpass hshape),
      clockCount_virtualCfg_eq, ← hcardC] at htick
    exact htick
  -- second part: the P1 count
  have hpart2 : (∑ t ∈ Finset.Ico (w.bulk (clockTop n)) hq,
      if StepEvent init (CCPair init) t ω then 1 else 0) ≤ 13 * C.card := by
    have hcongr2 := windowCount_congr
      (P := fun t ω => ω ∈ bulkHighWindow init C t ∧ StepEvent init (CCPair init) t ω)
      (R := fun t ω => w.bulk (clockTop n) ≤ t ∧ t < hq ∧ StepEvent init (CCPair init) t ω)
      s N ω (fun t hst => by
      dsimp only
      rw [bulkHighWindow_iff init ω hentry C hC hb1 hhq t hst]
      tauto)
    rw [← windowCount_interval _ s N ω hb1.1 hb1hq hhqN, ← hcongr2]
    by_contra hge
    apply hP1
    exact ⟨⟨T, hentry⟩, hcardC.symm, by omega⟩
  omega

/-- The settling window has length `cap + k - high_Q`, at most `finWindow + k` when no
`highAllBad` occurs. -/
theorem settle_length_le (hentry : AsyncEntry init ω s T) (C : Finset (Fin init.card))
    (hC : C = clockSet (virtualLabels init ω s)) (N : ℕ)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (hact : activationRow init ω s T) (hpass : passageRow init ω s T)
    (i₀ : Fin init.card) (hi₀ : (virtualLabels init ω s i₀).role = .clock) (k : ℕ) {hq : ℕ}
    (hhq : firstAfter (fun v => ReachedTop init (highThreshold C.card) v ω) s hq)
    (hhqN : hq + finWindow n C.card ≤ s + N) (hcapN : (virtualTimes init ω s).cap + k ≤ s + N)
    (hP2 : ∀ j ∈ C, ω ∉ highAllBad init (highThreshold C.card) s s (finWindow n C.card) j N) :
    windowCount (fun t ω => ω ∈ settleWindow init C s i₀ k t) s N ω ≤
      finWindow n C.card + k := by
  classical
  set w := virtualTimes init ω s with hw
  have hcardC := card_eq_clockCount init ω C hC
  have hcapfirst := cap_firstAfter init ω hentry hpass
  have hf1 := first_top_firstAfter init ω hentry hpass
  have hf1hq : w.first (clockTop n) ≤ hq :=
    firstAfter_le_of hf1 hhq.1 (le_trans (one_le_highThreshold (by
      rw [hcardC]; exact one_le_seed_clock init ω hentry hn)) hhq.2.1)
  have hshq : s ≤ hq := hhq.1
  -- the cap is at most `high_Q + finWindow`
  have hcap_le : w.cap ≤ hq + finWindow n C.card := by
    apply firstAfter_le_of hcapfirst (by omega)
    apply allCapAt_of_all_capped init ω hentry _ (by omega)
    intro j hj
    have hjC : j ∈ C := by
      rw [hC]
      simp only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj
    by_contra hnot
    apply hP2 j hjC
    refine ⟨⟨T, hentry⟩, le_rfl, hj, hq, hhq, hhqN, ?_, hnot⟩
    intro u hu
    exact clock_phase_three_of_first init ω hentry hact j hj (le_trans hf1hq hu)
  have hcongr := windowCount_congr
    (P := fun t ω => ω ∈ settleWindow init C s i₀ k t)
    (R := fun t ω => hq ≤ t ∧ t < w.cap + k ∧ True)
    s N ω (fun t hst => by
    dsimp only
    rw [settleWindow_iff init ω hentry C hC i₀ hi₀ hhq hcapfirst k t hst]
    tauto)
  have hhqcap : hq ≤ w.cap := by
    apply firstAfter_le_of hhq hcapfirst.1
    unfold ReachedTop
    have := hcapfirst.2.1
    unfold AllCapAt at this
    rw [this, ← hcardC]
    exact highThreshold_le_card _
  rw [hcongr, windowCount_interval (fun _ _ => True) s N ω hhq.1 (by omega) hcapN]
  simp only [if_true, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico]
  omega

/-- The bridge: a guarded failure of the contact row outside the two passage events puts
some seed Clock in the MGF bad event with the P14 budgets. -/
theorem tagBad_of_guard (hentry : AsyncEntry init ω s T) (C : Finset (Fin init.card))
    (hC : C = clockSet (virtualLabels init ω s)) (N : ℕ)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (hcard : init.card = n) (hact : activationRow init ω s T) (hpass : passageRow init ω s T)
    (hshape : shapeRow init ω s T) (hcap : capRow init ω s T)
    (hnot : ¬ contactRow init ω s T)
    (hN : logWindow n 20000 + finWindow n C.card + logWindow n 16 ≤ N)
    (hP1 : ω ∉ bulkHighBad init C s N)
    (hP2 : ∀ j ∈ C, ω ∉ highAllBad init (highThreshold C.card) s s (finWindow n C.card) j N) :
    ∃ i₀ ∈ C, ω ∈ tagBad init C s i₀ (logWindow n 16) N
      (40 * (PhaseThreeModel.Numeric.hourIndex n + 1))
      (localTickBudget C.card + 13 * C.card) (finWindow n C.card + logWindow n 16) := by
  classical
  have hcardC := card_eq_clockCount init ω C hC
  -- the failing Clock
  have hnot' : ∃ i₀, fixedRoleL init (virtualLabels init ω s) .clock i₀ ∧
      40 * (PhaseThreeModel.Numeric.hourIndex n + 1) ≤
        eligibleContactsL init (virtualLabels init ω) (drawLabels init ω) s i₀
          ((virtualTimes init ω s).initialized i₀) ((virtualTimes init ω s).cap + logWindow n 16) := by
    by_contra hcon
    push_neg at hcon
    exact hnot ⟨fun i hi => hcon i hi⟩
  obtain ⟨i₀, hi₀, helig⟩ := hnot'
  have hi₀r : (virtualLabels init ω s i₀).role = .clock := hi₀
  have hi₀C : i₀ ∈ C := by
    rw [hC]
    simp only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi₀r
  -- the times
  have hcapfirst := cap_firstAfter init ω hentry hpass
  have hcapdl : (virtualTimes init ω s).cap ≤ s + logWindow n 20000 := hcap.cap_deadline
  have hhigh_cap : ReachedTop init (highThreshold C.card) (virtualTimes init ω s).cap ω := by
    unfold ReachedTop
    have := hcapfirst.2.1
    unfold AllCapAt at this
    rw [this, ← hcardC]
    exact highThreshold_le_card _
  obtain ⟨hq, hhq⟩ := exists_firstAfter
    (P := fun v => ReachedTop init (highThreshold C.card) v ω) hcapfirst.1 hhigh_cap
  have hhqcap : hq ≤ (virtualTimes init ω s).cap := firstAfter_le_of hhq hcapfirst.1 hhigh_cap
  refine ⟨i₀, hi₀C, ?_, ?_, ?_⟩
  · -- the tagged participations
    have hinit : s ≤ (virtualTimes init ω s).initialized i₀ := by
      have hfirst := hact.initialized_first i₀ hi₀
      have h3 : 3 ≤ (virtualLabels init ω ((virtualTimes init ω s).initialized i₀) i₀).phase.val := hfirst.1
      by_contra hlt
      have hlt' : (virtualTimes init ω s).initialized i₀ < s := Nat.lt_of_not_le hlt
      have hagree := virtualLabels_eq_labelsAt_through_asyncEntry init ω s T hentry
      have hsT := hentry.order
      rw [hagree _ (by omega)] at h3
      have hlow := hentry.first_phase_seed.2 _ hlt' _
        (labelsAt_mem_trace init ω ((virtualTimes init ω s).initialized i₀) i₀)
      omega
    exact helig.trans (eligible_le_windowCount init ω hentry C hC N i₀ hi₀r (logWindow n 16)
      hcapfirst hinit (by omega) le_rfl)
  · exact local_pairs_le init ω hentry C hC N hn hcard hact hpass hshape i₀ hi₀r hhq (by omega) hP1
  · exact settle_length_le init ω hentry C hC N hn hact hpass i₀ hi₀r (logWindow n 16) hhq
      (by omega) (by omega) hP2

end Counts

end Guard

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockContactBridge

end
