import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockReserve

/-!
# The regime row is deterministic from the entry (N12, §2/P2 regime clauses)

`PhaseThreeClockRows.RowRegime` collects the clauses of the clock core that hold on
the whole window from the seed `S`: roles fixed, the three role counts constant, every
phase in `[1, 3]`, every phase exactly `3` from the all-three time `T`, and the role
densities. On the virtual continuation all of these follow from the asynchronous
entry `AsyncEntry init ω S T` alone:

* roles and phases: `PhaseThreeClockEmbeddingBridge.virtualLabels_roles_fixed_of_asyncEntry`,
  `virtualLabels_clockEnvironment_of_asyncEntry` and `virtualLabels_phase_three_of_time`;
* counts: the virtual configuration is the multiset of the virtual labels, so a role
  count is a count over labels with fixed roles (`virtualCfg_roleCount_eq_seed`);
* density: `SeedProfile.role_good` (`RoleSplitGood` with `η = 1/25`) gives the four lower
  and upper bounds at `S`, and `finalRoles` with `card = n` gives `M + C + R = n`, hence
  `25 C ≤ 7 n` (`role_counts_add_eq_card`).

The headline `regimeRow_of_asyncEntry` is the hypothesis `hreg` of
`PhaseThreeClockReserve.virtual_core_tail_of_row_tails`; `virtual_core_tail_of_tails`
discharges it.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRegime

open TimeTheorem PairLog StageEventSpec PhaseThreeClockVirtual PhaseThreeClockCore
  PhaseThreeClockEmbeddingBridge PhaseThreeClockRows PhaseThreeClockProducer
  PhaseThreeClockAssembly

variable {n : ℕ} (init : InputCfg n)

/-! ## Role counts of a labelled configuration -/

/-- A role count of `labelCfg f` is the number of labels with that role. -/
theorem countP_role_labelCfg (f : Lab init) (r : Role) :
    Multiset.countP (fun a => a.role = r) (labelCfg f) =
      (Finset.univ.filter (fun i => (f i).role = r)).card := by
  unfold labelCfg
  rw [Multiset.countP_map]
  rfl

/-- Labellings with pointwise equal roles have equal role counts. -/
theorem countP_role_labelCfg_eq {f g : Lab init} (hr : ∀ i, (f i).role = (g i).role)
    (r : Role) :
    Multiset.countP (fun a => a.role = r) (labelCfg f) =
      Multiset.countP (fun a => a.role = r) (labelCfg g) := by
  rw [countP_role_labelCfg, countP_role_labelCfg]
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [hr i]

/-- With every role among Main, Clock and Reserve, the three counts sum to the size. -/
theorem role_counts_add_eq_card (c : InputCfg n) (hfin : finalRoles c) :
    timeMainCount c + clockCount c + reserveCount c = c.card := by
  unfold timeMainCount clockCount reserveCount
  induction c using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha := hfin a (Multiset.mem_cons_self a s)
      have hs : finalRoles s := fun b hb => hfin b (Multiset.mem_cons_of_mem hb)
      have ih' := ih hs
      rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_cons, Multiset.card_cons]
      rcases ha with h | h | h <;> simp [h] <;> omega

/-! ## The virtual counts and phases from the entry -/

variable (ω : InputLog n)

theorem virtualCfg_eq_labelCfg (v : ℕ) :
    virtualCfg init ω v = labelCfg (virtualLabels init ω v) := rfl

theorem mem_virtualCfg {v : ℕ} {a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256}
    (ha : a ∈ virtualCfg init ω v) : ∃ i, virtualLabels init ω v i = a := by
  rw [virtualCfg_eq_labelCfg] at ha
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp ha
  exact ⟨i, hi⟩

/-- Every role count of the virtual configuration after the seed is the seed count. -/
theorem virtualCfg_roleCount_eq_seed {S T : ℕ} (hentry : AsyncEntry init ω S T)
    (v : ℕ) (hSv : S ≤ v) (r : Role) :
    Multiset.countP (fun a => a.role = r) (virtualCfg init ω v) =
      Multiset.countP (fun a => a.role = r) (trace init ω S) := by
  rw [virtualCfg_eq_labelCfg, ← labelsAt_config init ω S]
  exact countP_role_labelCfg_eq init
    (virtualLabels_roles_fixed_of_asyncEntry init ω S T hentry v hSv) r

theorem virtualCfg_timeMainCount_eq_seed {S T : ℕ} (hentry : AsyncEntry init ω S T)
    (v : ℕ) (hSv : S ≤ v) :
    timeMainCount (virtualCfg init ω v) = timeMainCount (trace init ω S) :=
  virtualCfg_roleCount_eq_seed init ω hentry v hSv .main

theorem virtualCfg_clockCount_eq_seed {S T : ℕ} (hentry : AsyncEntry init ω S T)
    (v : ℕ) (hSv : S ≤ v) :
    clockCount (virtualCfg init ω v) = clockCount (trace init ω S) :=
  virtualCfg_roleCount_eq_seed init ω hentry v hSv .clock

theorem virtualCfg_reserveCount_eq_seed {S T : ℕ} (hentry : AsyncEntry init ω S T)
    (v : ℕ) (hSv : S ≤ v) :
    reserveCount (virtualCfg init ω v) = reserveCount (trace init ω S) :=
  virtualCfg_roleCount_eq_seed init ω hentry v hSv .reserve

/-- The density clauses at the seed: `RoleSplitGood (1/25)` and `M + C + R = n`. -/
theorem seed_density {S T : ℕ} (hentry : AsyncEntry init ω S T) :
    12 * n ≤ 25 * timeMainCount (trace init ω S) ∧
    25 * timeMainCount (trace init ω S) ≤ 13 * n ∧
    6 * n ≤ 25 * clockCount (trace init ω S) ∧
    25 * clockCount (trace init ω S) ≤ 7 * n ∧
    6 * n ≤ 25 * reserveCount (trace init ω S) := by
  have hgood := hentry.seed_profile.role_good
  obtain ⟨-, hM1, hM2, hC, hR⟩ := hgood
  have hcard := hentry.seed_profile.card_eq
  have hsum := role_counts_add_eq_card (trace init ω S) hentry.seed_profile.final_roles
  rw [hcard] at hsum
  have eM : RoleSplitConcentration.mainCount (trace init ω S) =
      timeMainCount (trace init ω S) := rfl
  have eC : RoleSplitConcentration.clockCount (trace init ω S) =
      clockCount (trace init ω S) := rfl
  have eR : RoleSplitConcentration.reserveCount (trace init ω S) =
      reserveCount (trace init ω S) := rfl
  rw [eM] at hM1 hM2
  rw [eC] at hC
  rw [eR] at hR
  have hM1' : 12 * n ≤ 25 * timeMainCount (trace init ω S) := by
    have : (12 : ℝ) * n ≤ 25 * (timeMainCount (trace init ω S) : ℝ) := by linarith
    exact_mod_cast this
  have hM2' : 25 * timeMainCount (trace init ω S) ≤ 13 * n := by
    have : 25 * (timeMainCount (trace init ω S) : ℝ) ≤ 13 * n := by linarith
    exact_mod_cast this
  have hC' : 6 * n ≤ 25 * clockCount (trace init ω S) := by
    have : (6 : ℝ) * n ≤ 25 * (clockCount (trace init ω S) : ℝ) := by linarith
    exact_mod_cast this
  have hR' : 6 * n ≤ 25 * reserveCount (trace init ω S) := by
    have : (6 : ℝ) * n ≤ 25 * (reserveCount (trace init ω S) : ℝ) := by linarith
    exact_mod_cast this
  exact ⟨hM1', hM2', hC', by omega, hR'⟩

/-- Every phase of the virtual configuration after the seed lies in `[1, 3]`. -/
theorem virtualCfg_phase_range {S T : ℕ} (hentry : AsyncEntry init ω S T)
    (v : ℕ) (hSv : S ≤ v) :
    ∀ a ∈ virtualCfg init ω v, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3 := by
  intro a ha
  obtain ⟨i, rfl⟩ := mem_virtualCfg init ω ha
  exact (virtualLabels_clockEnvironment_of_asyncEntry init ω S T hentry v hSv).phase_range i

/-- Every phase of the virtual configuration from the all-three time is exactly `3`. -/
theorem virtualCfg_all_three {S T : ℕ} (hentry : AsyncEntry init ω S T)
    (v : ℕ) (hTv : T ≤ v) :
    ∀ a ∈ virtualCfg init ω v, a.phase.val = 3 := by
  intro a ha
  obtain ⟨i, rfl⟩ := mem_virtualCfg init ω ha
  have heq := virtualLabels_eq_labelsAt_through_asyncEntry init ω S T hentry
  have hT : ∀ i, (virtualLabels init ω T i).phase.val = 3 := by
    intro i
    rw [heq T le_rfl]
    exact hentry.advanced_profile.all_three _ (labelsAt_mem_trace init ω T i)
  exact virtualLabels_phase_three_of_time init ω T hT v hTv i

/-! ## The regime row -/

/-- The regime row holds on the virtual continuation from every asynchronous entry;
this is the hypothesis `hreg` of `PhaseThreeClockReserve.virtual_core_tail_of_row_tails`. -/
theorem regimeRow_of_asyncEntry {S T : ℕ} (hentry : AsyncEntry init ω S T) :
    regimeRow init ω S T := by
  have hroles := virtualLabels_roles_fixed_of_asyncEntry init ω S T hentry
  have hdens := seed_density init ω hentry
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hSv _ i
    exact (hroles v hSv i).trans (hroles S le_rfl i).symm
  · intro v hSv _
    rw [virtualCfg_timeMainCount_eq_seed init ω hentry v hSv,
      virtualCfg_timeMainCount_eq_seed init ω hentry S le_rfl]
  · intro v hSv _
    rw [virtualCfg_clockCount_eq_seed init ω hentry v hSv,
      virtualCfg_clockCount_eq_seed init ω hentry S le_rfl]
  · intro v hSv _
    rw [virtualCfg_reserveCount_eq_seed init ω hentry v hSv,
      virtualCfg_reserveCount_eq_seed init ω hentry S le_rfl]
  · intro v hSv _
    exact virtualCfg_phase_range init ω hentry v hSv
  · intro v hTv _
    exact virtualCfg_all_three init ω hentry v hTv
  · intro v hSv _
    rw [virtualCfg_timeMainCount_eq_seed init ω hentry v hSv,
      virtualCfg_clockCount_eq_seed init ω hentry v hSv,
      virtualCfg_reserveCount_eq_seed init ω hentry v hSv]
    exact hdens

/-- `hcore` of `PhaseThreeClockBudget.asynchronous_clock_estimate_of_tails` from the six
probabilistic row tails alone. -/
theorem virtual_core_tail_of_tails (hn : 2 ≤ n) (h : RowTails init) :
    law init {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      (∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T) ∧
      ¬ VirtualGoodAt init s ω} ≤
      ENNReal.ofReal (6 / (n : ℝ) ^ 5) :=
  PhaseThreeClockReserve.virtual_core_tail_of_row_tails init hn
    (fun ω S T hentry => regimeRow_of_asyncEntry init ω hentry) h

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRegime

end
