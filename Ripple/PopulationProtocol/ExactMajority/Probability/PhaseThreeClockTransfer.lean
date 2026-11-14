import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCore
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEmbedding

/-!
# The first-exit contradiction and the transfer to the actual protocol (N12, step 5)

PHASE3 P14 (transfer part). On the virtual continuation the counter-reserve clause keeps
every Clock counter at least `10 H + 1` through the protected settling horizon
`w.cap + logWindow n 16`. Before the genuine first Phase-4 seed `ρ` the actual labelled
process coincides with the virtual one; a counter exit at `ρ` needs a dispatched Clock
with counter zero at `ρ - 1`, so `ρ` is beyond the protected horizon
(`protected_settling_of_virtual`). All remaining clauses of `ClockHistory` refer to
times before `ρ`, so `VirtualClockCore` transfers to the actual path
(`clockHistory_of_virtual`), given the actual exit clauses of P15.

The initializer facts of `PhaseThreeClockEmbedding` are reused; the two further facts
needed for the exit pair (`runInitsBetween_role_clock_of_output`,
`runInitsBetween_three_clock_counter`) are proved here.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockTransfer

open TimeTheorem PairLog PairLogAuxiliary StageEventSpec PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne PhaseThreeClockEmbedding
  PhaseThreeClockCore

variable {L K : ℕ}

/-! ## Generic first-hit congruences -/

theorem firstAfter_congr {P Q : ℕ → Prop} {S t : ℕ}
    (h : ∀ u, S ≤ u → u ≤ t → (P u ↔ Q u)) (hP : firstAfter P S t) : firstAfter Q S t :=
  ⟨hP.1, (h t hP.1 le_rfl).mp hP.2.1,
    fun u hu hut hQ => hP.2.2 u hu hut ((h u hu hut.le).mpr hQ)⟩

theorem firstHit_congr {α : Type*} {P : α → Prop} {tr tr' : ℕ → α} {t : ℕ}
    (h : ∀ u ≤ t, tr u = tr' u) (hP : firstHit P tr t) : firstHit P tr' t :=
  ⟨by rw [← h t le_rfl]; exact hP.1, fun u hu => by rw [← h u hu.le]; exact hP.2 u hu⟩

/-! ## Initializer facts for the exit pair -/

theorem runInitsBetween_role_clock_of_output (oldP newP : ℕ) (a : AgentState L K)
    (h : (runInitsBetween L K oldP newP a).role = .clock) : a.role = .clock := by
  unfold runInitsBetween at h
  generalize (List.range 11).filter (fun k => oldP < k ∧ k ≤ newP) = l at h
  induction l generalizing a with
  | nil => exact h
  | cons k l ih =>
      rw [List.foldl_cons] at h
      have h' := ih _ h
      split_ifs at h' with hk
      · rw [phaseInit_role] at h'
        by_cases hcr : (⟨k, hk⟩ : Fin 11).val = 1 ∧ a.role = .cr
        · rw [if_pos hcr] at h'
          exact absurd h' (by decide)
        · rw [if_neg hcr] at h'
          exact h'
      · exact h'

/-- Reaching Phase 3 from below runs `phaseInit 3`, which resets a Clock counter. -/
theorem runInitsBetween_three_clock_counter (oldP : ℕ) (h : oldP < 3) (a : AgentState L K)
    (hr : a.role = .clock) :
    (runInitsBetween L K oldP 3 a).counter.val = 50 * (L + 1) := by
  interval_cases oldP
  · have hl : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 3) = [1, 2, 3] := by decide
    unfold runInitsBetween
    rw [hl]
    simp only [List.foldl]
    rw [dif_pos (by norm_num : (1 : ℕ) < 11), dif_pos (by norm_num : (2 : ℕ) < 11),
      dif_pos (by norm_num : (3 : ℕ) < 11)]
    have r2 : (phaseInit L K ⟨2, by norm_num⟩ (phaseInit L K ⟨1, by norm_num⟩ a)).role = .clock := by
      rw [phaseInit_role, phaseInit_role]
      simp [hr]
    rw [phaseInit_three_clock _ r2]
  · have hl : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 3) = [2, 3] := by decide
    unfold runInitsBetween
    rw [hl]
    simp only [List.foldl]
    rw [dif_pos (by norm_num : (2 : ℕ) < 11), dif_pos (by norm_num : (3 : ℕ) < 11)]
    have r2 : (phaseInit L K ⟨2, by norm_num⟩ a).role = .clock := by
      rw [phaseInit_role]
      simp [hr]
    rw [phaseInit_three_clock _ r2]
  · have hl : (List.range 11).filter (fun k => 2 < k ∧ k ≤ 3) = [3] := by decide
    unfold runInitsBetween
    rw [hl]
    simp only [List.foldl]
    rw [dif_pos (by norm_num : (3 : ℕ) < 11), phaseInit_three_clock a hr]

/-- The origin of a counter exit: a Clock in Phase 3 with counter zero before the step. -/
theorem counterExitPair_origin (s t : AgentState L K) (hs3 : s.phase.val ≤ 3)
    (ht3 : t.phase.val ≤ 3) (h : CounterExitPair s t) :
    (s.role = .clock ∧ s.phase.val = 3 ∧ s.counter.val = 0) ∨
    (t.role = .clock ∧ t.phase.val = 3 ∧ t.counter.val = 0) := by
  obtain ⟨⟨h3, h3', hsr, htr, -, -⟩, hz⟩ := h
  have hepi := phaseEpidemicUpdate_eq_of_no_backup s t (by omega) (by omega) ⟨by omega, by omega⟩
  rw [hepi] at h3 h3' hsr htr hz
  simp only [] at h3 h3' hsr htr hz
  have hpv : (max s.phase t.phase).val = max s.phase.val t.phase.val := fin_val_max _ _
  have hp3 : (max s.phase t.phase).val = 3 := by
    rcases runInitsBetween_phase_eq_or_ten s.phase.val (max s.phase t.phase).val
        { s with phase := max s.phase t.phase } with h | h
    · rw [h] at h3; exact h3
    · omega
  rcases hz with hz | hz
  · left
    have hr' := runInitsBetween_role_clock_of_output _ _ _ hsr
    have hr : s.role = .clock := hr'
    have hs3' : s.phase.val = 3 := by
      rcases Nat.lt_or_ge s.phase.val (max s.phase t.phase).val with hlt | hge
      · exfalso
        rw [hp3] at hz hlt
        have := runInitsBetween_three_clock_counter s.phase.val hlt
          { s with phase := max s.phase t.phase } hr
        rw [this] at hz
        omega
      · omega
    have hsp : s.phase = max s.phase t.phase := Fin.ext (by omega)
    refine ⟨hr, hs3', ?_⟩
    rw [← hsp, runInitsBetween_self] at hz
    exact hz
  · right
    have hr' := runInitsBetween_role_clock_of_output _ _ _ htr
    have hr : t.role = .clock := hr'
    have ht3' : t.phase.val = 3 := by
      rcases Nat.lt_or_ge t.phase.val (max s.phase t.phase).val with hlt | hge
      · exfalso
        rw [hp3] at hz hlt
        have := runInitsBetween_three_clock_counter t.phase.val hlt
          { t with phase := max s.phase t.phase } hr
        rw [this] at hz
        omega
      · omega
    have htp : t.phase = max s.phase t.phase := Fin.ext (by omega)
    refine ⟨hr, ht3', ?_⟩
    rw [← htp, runInitsBetween_self] at hz
    exact hz

/-! ## The first-exit contradiction -/

variable {n : ℕ} (init : InputCfg n)

theorem seed_lt_exit (ω : InputLog n) {S T ρ : ℕ}
    (hentry : AsyncEntry init ω S T) (hexit : firstPhaseSeed init 4 ρ ω) : S < ρ := by
  rcases Nat.lt_or_ge S ρ with h | h
  · exact h
  exfalso
  obtain ⟨a, ha, ha4⟩ := hexit.1
  rcases Nat.lt_or_eq_of_le h with h' | h'
  · exact hentry.seed_first.2 ρ h' ⟨a, ha, by omega⟩
  · subst h'
    have := hentry.seed_profile.phase_range a ha
    omega

theorem seed_le_cap (ω : InputLog n) {S T : ℕ} {w : ClockTimes init}
    (hcore : VirtualClockCore init ω S T w) : S ≤ w.cap := by
  have := (hcore.level_before_cap 0 (Nat.zero_le _)).1
  rw [hcore.first_zero] at this
  exact this

/-- PHASE3 P14: no counter exit through the protected settling horizon. -/
theorem protected_settling_of_virtual (ω : InputLog n) {S T ρ : ℕ} {w : ClockTimes init}
    (hn : 1 ≤ n) (hentry : AsyncEntry init ω S T) (hcore : VirtualClockCore init ω S T w)
    (hexit : firstPhaseSeed init 4 ρ ω) :
    w.cap + logWindow n 16 < ρ := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlw : logWindow n 16 ≤ logWindow n 400 := logWindow_mono hlog (by norm_num)
  have hScap : S ≤ w.cap := seed_le_cap init ω hcore
  have hSρ : S < ρ := seed_lt_exit init ω hentry hexit
  by_contra hcon
  have hρZ : ρ ≤ w.cap + logWindow n 16 := by omega
  have hagree := virtualLabels_eq_labelsAt_before_seed init ω hexit
  obtain ⟨r, hr⟩ : ∃ r, ρ = r + 1 := ⟨ρ - 1, by omega⟩
  subst hr
  have hr_lt : r < r + 1 := Nat.lt_succ_self r
  have hlt4 : ∀ i, (labelsAt init ω r i).phase.val < 4 :=
    fun i => hexit.2 r hr_lt _ (labelsAt_mem_trace init ω r i)
  obtain ⟨a, ha, ha4⟩ := hexit.1
  rw [← labelsAt_config] at ha
  obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp ha
  -- a Clock with counter zero at `r` contradicts the virtual counter reserve
  have key : ∀ k : Fin init.card, (labelsAt init ω r k).role = .clock →
      (labelsAt init ω r k).phase.val = 3 → (labelsAt init ω r k).counter.val = 0 → False := by
    intro k hkr hk3 hkc
    rw [← hagree r hr_lt] at hkr hk3 hkc
    have hrole : fixedRoleL init (virtualLabels init ω S) .clock k := by
      unfold fixedRoleL
      rw [← hcore.roles_fixed r (by omega) (by omega) k]
      exact hkr
    have hinit : w.initialized k ≤ r := by
      by_contra hlt
      exact (hcore.initialized_first k hrole).2 r (by omega)
        (show 3 ≤ (virtualLabels init ω r k).phase.val by omega)
    have := hcore.counter_reserve k hrole r hinit (by omega)
    omega
  cases hd : drawLabels init ω (r + 1) with
  | none =>
      have hstep := labelsAt_succ_eq_auxStep init ω r
      rw [hd] at hstep
      rw [hstep] at hk
      simp only [auxStep] at hk
      have := hlt4 k
      rw [hk] at this
      omega
  | some ij =>
      obtain ⟨i, j⟩ := ij
      obtain ⟨hij, hi, hj, hother⟩ := labelsAt_selected_transition init ω r i j hd
      have hf3 : ∀ i, (labelsAt init ω r i).phase.val ≤ 3 := fun i => by have := hlt4 i; omega
      by_cases hce : CounterExitPair (labelsAt init ω r i) (labelsAt init ω r j)
      · rcases counterExitPair_origin _ _ (hf3 i) (hf3 j) hce with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · exact key i h1 h2 h3
        · exact key j h1 h2 h3
      · have hrule : virtualRule (labelsAt init ω r i) (labelsAt init ω r j) =
            (NonuniformMajority _ _).δ (labelsAt init ω r i) (labelsAt init ω r j) :=
          virtualRule_eq_transition _ _ hce
        have hv : labelsAt init ω (r + 1) = virtualLabels init ω (r + 1) := by
          rw [virtualLabels_succ, hd, labelsAt_succ_eq_auxStep, hd, hagree r hr_lt]
          simp only [auxStep, ruleUpdate, hrule]
        have hmem : virtualLabels init ω (r + 1) k ∈ virtualCfg init ω (r + 1) :=
          Multiset.mem_map.mpr ⟨k, Finset.mem_univ_val k, rfl⟩
        have := (hcore.phase_range (r + 1) (by omega) (by omega) _ hmem).2
        rw [← hv, hk] at this
        omega

/-! ## Transfer of the virtual core to the actual history -/

/-- PHASE3 P14 (transfer): a virtual core together with the actual exit clauses of P15
is the reviewed clock history. -/
theorem clockHistory_of_virtual (ω : InputLog n) {S T ρ : ℕ} {w : ClockTimes init}
    (hn : 1 ≤ n) (hentry : AsyncEntry init ω S T) (hcore : VirtualClockCore init ω S T w)
    (hexit : firstPhaseSeed init 4 ρ ω)
    (hρdead : ρ ≤ S + logWindow n 20000)
    (hafter : ρ ≤ w.cap + logWindow n 400)
    (hspread : allGE 4 (trace init ω (S + logWindow n 20000))) :
    ClockHistory init ω S T ρ w := by
  have hprot : w.cap + logWindow n 16 < ρ := protected_settling_of_virtual init ω hn hentry hcore hexit
  have hScap : S ≤ w.cap := seed_le_cap init ω hcore
  have hSρ : S < ρ := seed_lt_exit init ω hentry hexit
  have hcapρ : w.cap < ρ := by omega
  have hagree : ∀ t < ρ, virtualLabels init ω t = labelsAt init ω t :=
    virtualLabels_eq_labelsAt_before_seed init ω hexit
  have hcfg : ∀ t < ρ, virtualCfg init ω t = trace init ω t :=
    virtualCfg_eq_trace_before_seed init ω hexit
  have hTcap : T ≤ w.cap := hcore.all_before_cap
  have hαcap : w.activation ≤ w.cap := hcore.activation_before_cap
  have hlevel := hcore.level_before_cap
  have hhour := hcore.hour_before_cap
  have hVS : virtualLabels init ω S = labelsAt init ω S := hagree S hSρ
  have hCS : virtualCfg init ω S = trace init ω S := hcfg S hSρ
  -- a fixed Clock role at `S` on both paths
  have hrole : ∀ i, fixedRole init ω S .clock i → fixedRoleL init (virtualLabels init ω S) .clock i := by
    intro i hi
    unfold fixedRoleL
    rw [hVS]
    exact hi
  refine
    { entry := hentry
      roles_fixed := ?_, main_count := ?_, clock_count := ?_, reserve_count := ?_
      phase_range := ?_, all_three := ?_, density := ?_, activation_first := ?_
      first_zero := hcore.first_zero, bulk_zero := hcore.bulk_zero
      level_first := ?_, level_bulk := ?_, start_zero := hcore.start_zero
      start_positive := ?_, finish_first := ?_, cap_first := ?_
      activation_before_cap := hαcap, all_before_cap := hTcap
      level_before_cap := hlevel, hour_before_cap := hhour
      first_exit := hexit, cap_deadline := hcore.cap_deadline, exit_deadline := hρdead
      bulk_width := ?_, high_width := ?_, front_shape := ?_
      raw_local := hcore.raw_local, tick_local := ?_, fine_raw_local := ?_
      activation_before_twenty := hcore.activation_before_twenty
      previous_end := hcore.previous_end, raw_width := ?_, exact_hour := ?_
      active_main_floor := ?_, active_clock_floor := ?_
      first_work_allowance := ?_, second_work_allowance := ?_
      main_hour_tail := ?_, main_deep_tail := ?_
      cap_from_activation := hcore.cap_from_activation, protected_settling := hprot
      initialized_first := ?_, initialized_by_all := ?_, counter_reset := ?_
      initialized_before_first_cap := ?_, eligible_budget := ?_, counter_reserve := ?_
      exit_after_cap := hafter, final_spread := hspread }
  · intro v hS hv i
    have h := hcore.roles_fixed v hS (by omega) i
    rw [hagree v hv, hVS] at h
    exact h
  · intro v hS hv
    have h := hcore.main_count v hS (by omega)
    rw [hcfg v hv, hCS] at h
    exact h
  · intro v hS hv
    have h := hcore.clock_count v hS (by omega)
    rw [hcfg v hv, hCS] at h
    exact h
  · intro v hS hv
    have h := hcore.reserve_count v hS (by omega)
    rw [hcfg v hv, hCS] at h
    exact h
  · intro v hS hv
    have h := hcore.phase_range v hS (by omega)
    rw [hcfg v hv] at h
    exact h
  · intro v hT hv
    have h := hcore.all_three v hT (by omega)
    rw [hcfg v hv] at h
    exact h
  · intro v hS hv
    have h := hcore.density v hS (by omega)
    rw [hcfg v hv] at h
    exact h
  · refine firstAfter_congr (fun u hu hut => ?_) hcore.activation_first
    rw [activeCount_eq_L, hagree u (by omega)]
  · intro ell h1 h2
    refine firstAfter_congr (fun u hu hut => ?_) (hcore.level_first ell h1 h2)
    have := (hlevel ell h2).1
    rw [frontCount_eq_L, hVS, hagree u (by omega)]
  · intro ell h1 h2
    refine firstAfter_congr (fun u hu hut => ?_) (hcore.level_bulk ell h1 h2)
    have := (hlevel ell h2).2
    rw [frontCount_eq_L, hVS, hagree u (by omega), hCS]
  · intro h h1 h2
    refine firstAfter_congr (fun u hu hut => ?_) (hcore.start_positive h h1 h2)
    have := (hhour h h2).1
    rw [frontCount_eq_L, hVS, hagree u (by omega), hCS]
  · intro h h2
    refine firstAfter_congr (fun u hu hut => ?_) (hcore.finish_first h h2)
    have := (hhour h h2).2
    rw [frontCount_eq_L, hVS, hagree u (by omega), hCS]
  · refine firstAfter_congr (fun u hu hut => ?_) hcore.cap_first
    rw [frontCount_eq_L, hVS, hagree u (by omega), hCS]
  · have hb := hcore.bulk_width
    dsimp only at hb ⊢
    intro v hS hv
    have h := hb v hS hv
    rw [hVS, hagree v (by omega), hCS] at h
    rw [frontHeight_eq_L, frontQuantile_eq_L]
    exact h
  · have hb := hcore.high_width
    dsimp only at hb ⊢
    intro v hS hv
    have h := hb v hS hv
    rw [hVS, hagree v (by omega), hCS] at h
    rw [frontHeight_eq_L, frontQuantile_eq_L]
    exact h
  · have hb := hcore.front_shape
    dsimp only at hb ⊢
    intro ell v h1 h2 hS hv
    have hbl := (hlevel ell h2.le).2
    have h := hb ell v h1 h2 hS hv
    rw [hVS, hagree v (by omega), hCS] at h
    rw [frontCount_eq_L, frontCount_eq_L]
    exact h
  · intro ell h1 h2
    have h := hcore.tick_local ell h1 h2
    rw [hVS, hCS] at h
    rw [clockContacts_eq_L]
    exact h
  · intro ell h1 h2
    have h := hcore.fine_raw_local ell h1 h2
    rw [hCS] at h
    exact h
  · intro h hh
    have h' := hcore.raw_width h hh
    rw [hCS] at h'
    exact h'
  · intro h hh v h1 h2
    have hfin := (hhour h hh).2
    have h' := hcore.exact_hour h hh v h1 h2
    rw [hVS, hagree v (by omega), hCS] at h'
    rw [exactHourClocks_eq_L]
    exact h'
  · intro v h1 h2
    have h := hcore.active_main_floor v h1 (by omega)
    rw [hVS, hagree v h2, hCS] at h
    rw [activeRoleCount_eq_L]
    exact h
  · intro v h1 h2
    have h := hcore.active_clock_floor v h1 (by omega)
    rw [hVS, hagree v h2, hCS] at h
    rw [activeRoleCount_eq_L]
    exact h
  · intro h hh
    have h' := hcore.first_work_allowance h hh
    rw [hCS] at h'
    exact h'
  · intro h hh
    have h' := hcore.second_work_allowance h hh
    rw [hCS] at h'
    exact h'
  · intro h hh v h1 h2
    have hfin := (hhour h hh).2
    have h' := hcore.main_hour_tail h hh v h1 h2
    rw [hVS, hagree v (by omega), hCS] at h'
    rw [highHourMains_eq_L]
    exact h'
  · intro h hh v h1 h2
    have hfin := (hhour h hh).2
    have h' := hcore.main_deep_tail h hh v h1 h2
    rw [hVS, hagree v (by omega), hCS] at h'
    rw [highHourZeroMains_eq_L, deepBiasedMains_eq_L]
    exact h'
  · intro i hi
    have hiT := hcore.initialized_by_all i (hrole i hi)
    refine firstHit_congr (fun u hu => ?_) (hcore.initialized_first i (hrole i hi))
    rw [hagree u (by omega)]
  · intro i hi
    exact hcore.initialized_by_all i (hrole i hi)
  · intro i hi
    have hiT := hcore.initialized_by_all i (hrole i hi)
    have h := hcore.counter_reset i (hrole i hi)
    rw [hagree _ (by omega)] at h
    exact h
  · intro i hi
    exact hcore.initialized_before_first_cap i (hrole i hi)
  · intro i hi
    have h := hcore.eligible_budget i (hrole i hi)
    rw [eligibleContacts_eq_L]
    have hcongr : eligibleContactsL init (virtualLabels init ω) (drawLabels init ω) S i
        (w.initialized i) (w.cap + logWindow n 16) =
        eligibleContactsL init (labelsAt init ω) (drawLabels init ω) S i
        (w.initialized i) (w.cap + logWindow n 16) := by
      unfold eligibleContactsL
      congr 1
      ext k
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hk, hp⟩
        refine ⟨hk, ?_⟩
        have hk' := Finset.mem_Ioc.mp hk
        unfold eligibleContactL at hp ⊢
        rw [hVS, hagree (k - 1) (by omega)] at hp
        exact hp
      · rintro ⟨hk, hp⟩
        refine ⟨hk, ?_⟩
        have hk' := Finset.mem_Ioc.mp hk
        unfold eligibleContactL at hp ⊢
        rw [hVS, hagree (k - 1) (by omega)]
        exact hp
    rw [← hcongr]
    exact h
  · intro i hi v h1 h2
    have h := hcore.counter_reserve i (hrole i hi) v h1 h2
    rw [hagree v (by omega)] at h
    exact h

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockTransfer

end
