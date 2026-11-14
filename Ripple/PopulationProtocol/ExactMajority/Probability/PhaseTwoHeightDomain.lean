import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoHeightPair
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoHeightNumerics
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoActivation

/-!
# The deterministic domain for activation-height growth

Only the active Clock height is used. Backup configurations are admitted into
the invariant and have potential zero. Outside backup, the phase range and
the Clock density are transported by the actual mixed-phase transition.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoHeight

open TimeTheorem PhaseTwoActivation PhaseTwoActivationLocal

variable {L : ℕ}

def Backup (c : Cfg L 256) : Prop :=
  ∃ a ∈ c, a.phase.val = 10

def Height (c : Cfg L 256) : Prop :=
  ∃ a ∈ c, 3 ≤ a.phase.val ∧ a.role = .clock ∧
    16 * (L + 1) ≤ a.minute.val

def HeightBeforeBackup (c : Cfg L 256) : Prop := Height c ∧ ¬ Backup c

def clockPopulation (c : Cfg L 256) : ℕ :=
  c.countP (fun a => a.role = .clock)

def clockPotential (c : Cfg L 256) : ℝ≥0∞ :=
  Config.sumOf (fun a => (clockWeight a : ℝ≥0∞)) c

def killedPotential (c : Cfg L 256) : ℝ≥0∞ := by
  classical
  exact if Backup c then 0 else clockPotential c

structure HeightDomain (n : ℕ) (c : Cfg L 256) : Prop where
  card_eq : c.card = n
  active : Backup c ∨
    ((∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3) ∧
      25 * clockPopulation c ≤ 7 * n)

theorem no_height_active_clock_below (c : Cfg L 256) (h : ¬ Height c) :
    ActiveClockBelow c := by
  intro a ha hp hc
  by_contra hlow
  exact h ⟨a, ha, by omega, hc, by omega⟩

theorem no_backup_iff (c : Cfg L 256) :
    ¬ Backup c ↔ ∀ a ∈ c, a.phase.val ≠ 10 := by
  simp only [Backup, not_exists, not_and]

theorem backup_step (c : Cfg L 256) (s t : AgentState L 256)
    (hc : Backup c) :
    Backup (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hstep : Protocol.stepOrSelf (NonuniformMajority L 256) c s t =
        c - {s, t} + {(Transition L 256 s t).1, (Transition L 256 s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ] <;> rfl
    obtain ⟨a, ha, hphase⟩ := hc
    have hsplit : c = c - {s, t} + ({s, t} : Multiset (AgentState L 256)) := by
      rw [Multiset.sub_add_cancel happ]
    rw [hsplit] at ha
    rcases Multiset.mem_add.mp ha with hrest | hpair
    · exact ⟨a, by rw [hstep]; exact Multiset.mem_add.mpr (Or.inl hrest), hphase⟩
    · have hp : a = s ∨ a = t := by
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
          Multiset.mem_singleton] at hpair
        exact hpair
      have hmono1 : s.phase.val ≤ (Transition L 256 s t).1.phase.val :=
        (Transition_phase_monotone (L := L) (K := 256) s t).1
      have hmono2 : t.phase.val ≤ (Transition L 256 s t).2.phase.val :=
        (Transition_phase_monotone (L := L) (K := 256) s t).2
      rcases hp with h | h
      · rw [h] at hphase
        refine ⟨(Transition L 256 s t).1, by rw [hstep]; simp, ?_⟩
        have hcap := (Transition L 256 s t).1.phase.isLt
        omega
      · rw [h] at hphase
        refine ⟨(Transition L 256 s t).2, by rw [hstep]; simp, ?_⟩
        have hcap := (Transition L 256 s t).2.phase.isLt
        omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact hc

theorem height_domain_step (n : ℕ) (c : Cfg L 256)
    (hc : HeightDomain n c) (hwindow : ¬ HeightBeforeBackup c)
    (s t : AgentState L 256) :
    HeightDomain n (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) := by
  classical
  refine ⟨(Protocol.stepOrSelf_card_eq c s t).trans hc.card_eq, ?_⟩
  by_cases hnext : Backup (Protocol.stepOrSelf (NonuniformMajority L 256) c s t)
  · exact Or.inl hnext
  · right
    have hback : ¬ Backup c := fun h => hnext (backup_step c s t h)
    obtain ⟨hrange, hdensity⟩ := hc.active.resolve_left hback
    have hheight : ¬ Height c := fun h => hwindow ⟨h, hback⟩
    have hlow := no_height_active_clock_below c hheight
    have hno := (no_backup_iff _).mp hnext
    refine ⟨activation_range_step c s t hrange hlow hno, ?_⟩
    have hcount := activation_role_count_step .clock c s t hrange hlow hno
    simpa only [clockPopulation, hcount] using hdensity

theorem role_counts_le_card (c : Cfg L 256) :
    c.countP (fun a => a.role = .main) +
      c.countP (fun a => a.role = .clock) +
      c.countP (fun a => a.role = .reserve) ≤ c.card := by
  classical
  induction c using Multiset.induction_on with
  | empty => simp
  | @cons a c ih =>
      cases hrole : a.role <;> simp_all <;> omega

theorem seed_clock_density {n : ℕ} (init c : InputCfg n)
    (hseed : StageEventSpec.SeedProfile n init c) :
    25 * clockPopulation c ≤ 7 * n := by
  have hsum := role_counts_le_card c
  rw [hseed.card_eq] at hsum
  have hsumR :
      (c.countP (fun a => a.role = .main) : ℝ) +
        (c.countP (fun a => a.role = .clock) : ℝ) +
        (c.countP (fun a => a.role = .reserve) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hsum
  obtain ⟨_, hmain, _, _, hreserve⟩ := hseed.role_good
  change (1 - (1 / 25 : ℝ)) * (n : ℝ) / 2 ≤
    (c.countP (fun a => a.role = .main) : ℝ) at hmain
  change (1 - (1 / 25 : ℝ)) * (n : ℝ) / 4 ≤
    (c.countP (fun a => a.role = .reserve) : ℝ) at hreserve
  have hclockR : (25 : ℝ) * (clockPopulation c : ℝ) ≤ 7 * (n : ℝ) := by
    change (25 : ℝ) * (c.countP (fun a => a.role = .clock) : ℝ) ≤ 7 * (n : ℝ)
    nlinarith only [hmain, hreserve, hsumR]
  exact_mod_cast hclockR

theorem seed_height_domain {n : ℕ} (init c : InputCfg n)
    (hseed : StageEventSpec.SeedProfile n init c) : HeightDomain n c :=
  ⟨hseed.card_eq, Or.inr ⟨hseed.phase_range, seed_clock_density init c hseed⟩⟩

theorem clockPotential_le_card (c : Cfg L 256)
    (hweight : ∀ a ∈ c, clockWeight a ≤ 1) :
    clockPotential c ≤ (c.card : ℝ≥0∞) := by
  revert hweight
  induction c using Multiset.induction_on with
  | empty => intro _; simp [clockPotential, Config.sumOf]
  | @cons a c ih =>
      intro hweight
      have ha : (clockWeight a : ℝ≥0∞) ≤ 1 := by
        exact_mod_cast hweight a (by simp)
      have hc := ih (fun b hb => hweight b (by simp [hb]))
      simpa only [clockPotential, Config.sumOf, Multiset.map_cons,
        Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one,
        add_comm] using add_le_add ha hc

theorem seed_clockPotential_le {n : ℕ} (init c : InputCfg n)
    (hseed : StageEventSpec.SeedProfile n init c) :
    killedPotential c ≤ (n : ℝ≥0∞) := by
  classical
  by_cases hback : Backup c
  · simp only [killedPotential, if_pos hback, zero_le]
  · rw [killedPotential, if_neg hback]
    have hle : clockPotential c ≤ (c.card : ℝ≥0∞) := by
     apply clockPotential_le_card
     intro a ha
     by_cases hc : a.role = .clock
     · by_cases hp : 3 ≤ a.phase.val
       · have hpEq : a.phase.val = 3 := Nat.le_antisymm (hseed.phase_range a ha).2 hp
         have hminute := Phase3Pre3.clock_minute_zero_of_Phase3EntryAgent
           (hseed.fresh a ha hpEq) hc
         simp [clockWeight, hc, effectiveMinute, hp, hminute]
       · simp [clockWeight, hc, effectiveMinute, hp]
     · simp [clockWeight, hc]
    rwa [hseed.card_eq] at hle

theorem weight_le_potential (c : Cfg L 256) (a : AgentState L 256) (ha : a ∈ c) :
    (clockWeight a : ℝ≥0∞) ≤ clockPotential c := by
  revert ha
  induction c using Multiset.induction_on with
  | empty => intro ha; simpa using ha
  | @cons b c ih =>
      intro ha
      simp only [Multiset.mem_cons] at ha
      have hcp : clockPotential (b ::ₘ c) = (clockWeight b : ℝ≥0∞) + clockPotential c := by
        simp only [clockPotential, Config.sumOf, Multiset.map_cons, Multiset.sum_cons]
      rw [hcp]
      rcases ha with rfl | ha
      · exact le_add_of_nonneg_right zero_le
      · exact (ih ha).trans (le_add_of_nonneg_left zero_le)

theorem height_threshold_le (c : Cfg L 256) (h : HeightBeforeBackup c) :
    heightThreshold L ≤ killedPotential c := by
  classical
  obtain ⟨a, ha, hp, hc, hminute⟩ := h.1
  have hweight : 2 ^ (16 * (L + 1)) ≤ clockWeight a := by
    simp only [clockWeight, if_pos hc, effectiveMinute, if_pos hp]
    exact Nat.pow_le_pow_right (by decide) hminute
  have hcast : heightThreshold L ≤ (clockWeight a : ℝ≥0∞) := by
    unfold heightThreshold
    exact_mod_cast hweight
  rw [killedPotential, if_neg h.2]
  exact hcast.trans (weight_le_potential c a ha)

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoHeight

end
