/-
Interval mass ledger for the Doty et al. exact-majority protocol (phases 0-9).

The exact conservation law `prePhase4MassSum c = initialGap init` holds while every agent is
in a phase `≤ 7`: the small biases (phases 0-2) and then the dyadic biases (phases 3-7) are
redistributed but never created or destroyed.  The Phase-8 absorb reaction breaks exact
conservation: a non-full agent with bias `±2^{-i}` absorbs an opposite agent with bias
`∓2^{-j}` (`i < j`), keeps its own bias field and marks itself `full`; the true remaining mass
`2^{-i} - 2^{-j}` lies in `[2^{-(i+1)}, 2^{-i})`.  The ledger therefore assigns to every agent an
interval `[ledgerLo a, ledgerHi a]` (exact label below phase 8 or when not full; the half/whole
window for a full phase-8/9 agent) and proves that the initial gap always stays between the
two sums while no agent has reached the Phase-10 backup.

Consumers (`Analysis/DeterministicChain.lean`): a phase-9 consensus on one sign must be the
majority sign, and a zero gap forces every bias to zero.
-/

import Ripple.PopulationProtocol.ExactMajority.Analysis.Invariants
import Ripple.PopulationProtocol.ExactMajority.Probability.NonMainBiasZero

open Multiset

namespace Ripple.PopulationProtocol.ExactMajority

variable {L K : ℕ}

/-! ## The ledger -/

/-- Lower end of an agent's mass interval. -/
def ledgerLo (a : AgentState L K) : ℚ :=
  if 8 ≤ a.phase.val ∧ a.full = true then
    match a.bias with
    | .zero => 0
    | .dyadic .pos i => (1 : ℚ) / 2 ^ (i.val + 1)
    | .dyadic .neg i => -(1 : ℚ) / 2 ^ i.val
  else prePhase4Mass a

/-- Upper end of an agent's mass interval. -/
def ledgerHi (a : AgentState L K) : ℚ :=
  if 8 ≤ a.phase.val ∧ a.full = true then
    match a.bias with
    | .zero => 0
    | .dyadic .pos i => (1 : ℚ) / 2 ^ i.val
    | .dyadic .neg i => -(1 : ℚ) / 2 ^ (i.val + 1)
  else prePhase4Mass a

/-- Sum of the lower ends over a configuration. -/
def loSum (c : Config (AgentState L K)) : ℚ := (c.map ledgerLo).sum

/-- Sum of the upper ends over a configuration. -/
def hiSum (c : Config (AgentState L K)) : ℚ := (c.map ledgerHi).sum

/-! ## Arithmetic helpers -/

private lemma div_two_pow_succ (x : ℚ) (j : ℕ) : x / 2 ^ (j + 1) = x / 2 ^ j / 2 := by
  rw [pow_succ, div_div]

private lemma one_div_two_pow_pos (j : ℕ) : (0 : ℚ) < 1 / 2 ^ j := by positivity

private lemma one_div_two_pow_le_of_le {i j : ℕ} (h : i ≤ j) :
    (1 : ℚ) / 2 ^ j ≤ 1 / 2 ^ i := by
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) h

private lemma half_add_half (j : ℕ) :
    (1 : ℚ) / 2 ^ (j + 1) + 1 / 2 ^ (j + 1) = 1 / 2 ^ j := by
  rw [div_two_pow_succ]
  ring

/-! ## Basic facts about the ledger -/

lemma prePhase4Mass_of_phase_lt_three (a : AgentState L K) (h : a.phase.val < 3) :
    prePhase4Mass a = (AgentState.smallBiasInt a : ℚ) := by
  simp [prePhase4Mass, h]

lemma prePhase4Mass_of_phase_ge_three (a : AgentState L K) (h : 3 ≤ a.phase.val) :
    prePhase4Mass a = Bias.toRat a.bias := by
  simp [prePhase4Mass, show ¬ a.phase.val < 3 by omega]

/-- "Plain" agents: below phase 8 or with the `full` flag off. -/
lemma plain_of_phase_lt_eight (a : AgentState L K) (h : a.phase.val < 8) :
    ¬ (8 ≤ a.phase.val ∧ a.full = true) :=
  fun h8 => absurd h8.1 (by omega)

lemma plain_of_full_false (a : AgentState L K) (h : a.full = false) :
    ¬ (8 ≤ a.phase.val ∧ a.full = true) := by
  rintro ⟨_, hf⟩
  rw [h] at hf
  exact Bool.false_ne_true hf

/-- Below phase 8, or when the `full` flag is off, both ends are the exact label. -/
lemma ledgerLo_of_plain (a : AgentState L K) (h : ¬ (8 ≤ a.phase.val ∧ a.full = true)) :
    ledgerLo a = prePhase4Mass a := by
  simp [ledgerLo, h]

lemma ledgerHi_of_plain (a : AgentState L K) (h : ¬ (8 ≤ a.phase.val ∧ a.full = true)) :
    ledgerHi a = prePhase4Mass a := by
  simp [ledgerHi, h]

lemma ledgerLo_of_phase_lt_eight (a : AgentState L K) (h : a.phase.val < 8) :
    ledgerLo a = prePhase4Mass a :=
  ledgerLo_of_plain a (plain_of_phase_lt_eight a h)

lemma ledgerHi_of_phase_lt_eight (a : AgentState L K) (h : a.phase.val < 8) :
    ledgerHi a = prePhase4Mass a :=
  ledgerHi_of_plain a (plain_of_phase_lt_eight a h)

/-! ### Explicit values -/

private lemma ledgerLo_eq_of_full_pos (a : AgentState L K) (h8 : 8 ≤ a.phase.val)
    (hf : a.full = true) (i : Fin (L + 1)) (hb : a.bias = .dyadic .pos i) :
    ledgerLo a = (1 : ℚ) / 2 ^ (i.val + 1) := by
  simp only [ledgerLo, if_pos (And.intro h8 hf), hb]

private lemma ledgerHi_eq_of_full_pos (a : AgentState L K) (h8 : 8 ≤ a.phase.val)
    (hf : a.full = true) (i : Fin (L + 1)) (hb : a.bias = .dyadic .pos i) :
    ledgerHi a = (1 : ℚ) / 2 ^ i.val := by
  simp only [ledgerHi, if_pos (And.intro h8 hf), hb]

private lemma ledgerLo_eq_of_full_neg (a : AgentState L K) (h8 : 8 ≤ a.phase.val)
    (hf : a.full = true) (i : Fin (L + 1)) (hb : a.bias = .dyadic .neg i) :
    ledgerLo a = -(1 : ℚ) / 2 ^ i.val := by
  simp only [ledgerLo, if_pos (And.intro h8 hf), hb]

private lemma ledgerHi_eq_of_full_neg (a : AgentState L K) (h8 : 8 ≤ a.phase.val)
    (hf : a.full = true) (i : Fin (L + 1)) (hb : a.bias = .dyadic .neg i) :
    ledgerHi a = -(1 : ℚ) / 2 ^ (i.val + 1) := by
  simp only [ledgerHi, if_pos (And.intro h8 hf), hb]

private lemma ledgerLo_eq_of_not_full (a : AgentState L K) (hf : a.full = false)
    (h3 : 3 ≤ a.phase.val) : ledgerLo a = Bias.toRat a.bias := by
  rw [ledgerLo_of_plain a (plain_of_full_false a hf), prePhase4Mass_of_phase_ge_three a h3]

private lemma ledgerHi_eq_of_not_full (a : AgentState L K) (hf : a.full = false)
    (h3 : 3 ≤ a.phase.val) : ledgerHi a = Bias.toRat a.bias := by
  rw [ledgerHi_of_plain a (plain_of_full_false a hf), prePhase4Mass_of_phase_ge_three a h3]

private lemma ledgerLo_eq_zero_of_bias_zero (a : AgentState L K) (h3 : 3 ≤ a.phase.val)
    (hb : a.bias = .zero) : ledgerLo a = 0 := by
  unfold ledgerLo
  split_ifs
  · simp only [hb]
  · rw [prePhase4Mass_of_phase_ge_three a h3, hb]
    simp only [Bias.toRat]

private lemma ledgerHi_eq_zero_of_bias_zero (a : AgentState L K) (h3 : 3 ≤ a.phase.val)
    (hb : a.bias = .zero) : ledgerHi a = 0 := by
  unfold ledgerHi
  split_ifs
  · simp only [hb]
  · rw [prePhase4Mass_of_phase_ge_three a h3, hb]
    simp only [Bias.toRat]

private lemma ledgerLo_eq_of_neg (a : AgentState L K) (h3 : 3 ≤ a.phase.val)
    (i : Fin (L + 1)) (hb : a.bias = .dyadic .neg i) :
    ledgerLo a = -(1 : ℚ) / 2 ^ i.val := by
  unfold ledgerLo
  split_ifs
  · simp only [hb]
  · rw [prePhase4Mass_of_phase_ge_three a h3, hb]
    simp only [Bias.toRat]

private lemma ledgerHi_eq_of_pos (a : AgentState L K) (h3 : 3 ≤ a.phase.val)
    (i : Fin (L + 1)) (hb : a.bias = .dyadic .pos i) :
    ledgerHi a = (1 : ℚ) / 2 ^ i.val := by
  unfold ledgerHi
  split_ifs
  · simp only [hb]
  · rw [prePhase4Mass_of_phase_ge_three a h3, hb]
    simp only [Bias.toRat]

lemma ledgerLo_le_ledgerHi (a : AgentState L K) : ledgerLo a ≤ ledgerHi a := by
  unfold ledgerLo ledgerHi
  split_ifs
  · rcases a.bias with _ | ⟨s, i⟩
    · exact le_refl _
    · cases s
      · exact one_div_two_pow_le_of_le (Nat.le_succ _)
      · show -(1 : ℚ) / 2 ^ i.val ≤ -(1 : ℚ) / 2 ^ (i.val + 1)
        rw [neg_div, neg_div]
        exact neg_le_neg (one_div_two_pow_le_of_le (Nat.le_succ _))
  · exact le_refl _

/-- Both ends depend only on `phase ≥ 8`, `full` and `bias` once the phase is `≥ 3`. -/
lemma ledger_congr_of_ge_three {a b : AgentState L K}
    (h3a : 3 ≤ a.phase.val) (h3b : 3 ≤ b.phase.val)
    (h8 : 8 ≤ b.phase.val ↔ 8 ≤ a.phase.val)
    (hfull : b.full = a.full) (hbias : b.bias = a.bias) :
    ledgerLo b = ledgerLo a ∧ ledgerHi b = ledgerHi a := by
  unfold ledgerLo ledgerHi
  rw [prePhase4Mass_of_phase_ge_three a h3a, prePhase4Mass_of_phase_ge_three b h3b,
    hfull, hbias]
  by_cases h : 8 ≤ a.phase.val
  · have hb' : 8 ≤ b.phase.val := h8.mpr h
    cases hf : a.full
    · have hnb : ¬ (8 ≤ b.phase.val ∧ false = true) := fun hc => Bool.false_ne_true hc.2
      have hna : ¬ (8 ≤ a.phase.val ∧ false = true) := fun hc => Bool.false_ne_true hc.2
      rw [if_neg hnb, if_neg hnb, if_neg hna, if_neg hna]
      exact ⟨rfl, rfl⟩
    · have hpb : 8 ≤ b.phase.val ∧ true = true := ⟨hb', rfl⟩
      have hpa : 8 ≤ a.phase.val ∧ true = true := ⟨h, rfl⟩
      rw [if_pos hpb, if_pos hpb, if_pos hpa, if_pos hpa]
      exact ⟨rfl, rfl⟩
  · have hnb : ¬ (8 ≤ b.phase.val ∧ a.full = true) := fun hc => h (h8.mp hc.1)
    have hna : ¬ (8 ≤ a.phase.val ∧ a.full = true) := fun hc => h hc.1
    rw [if_neg hnb, if_neg hnb, if_neg hna, if_neg hna]
    exact ⟨rfl, rfl⟩

/-- Rewriting `opinions` and `output` does not change the ledger entries (phase `≥ 3`). -/
lemma ledger_update_opinions_output (a : AgentState L K) (h3 : 3 ≤ a.phase.val)
    (o : Fin 8) (out : Output) :
    ledgerLo ({ a with opinions := o, output := out }) = ledgerLo a ∧
      ledgerHi ({ a with opinions := o, output := out }) = ledgerHi a :=
  ledger_congr_of_ge_three h3 h3 Iff.rfl rfl rfl

lemma ledger_update_opinions (a : AgentState L K) (h3 : 3 ≤ a.phase.val) (o : Fin 8) :
    ledgerLo ({ a with opinions := o }) = ledgerLo a ∧
      ledgerHi ({ a with opinions := o }) = ledgerHi a :=
  ledger_congr_of_ge_three h3 h3 Iff.rfl rfl rfl

/-- Below phase 8 both ends are the exact label; two such agents with the same label have the
same ledger entries. -/
lemma ledger_eq_of_plain_of_mass_eq {a b : AgentState L K}
    (ha : ¬ (8 ≤ a.phase.val ∧ a.full = true)) (hb : ¬ (8 ≤ b.phase.val ∧ b.full = true))
    (hmass : prePhase4Mass b = prePhase4Mass a) :
    ledgerLo b = ledgerLo a ∧ ledgerHi b = ledgerHi a := by
  rw [ledgerLo_of_plain a ha, ledgerLo_of_plain b hb, ledgerHi_of_plain a ha,
    ledgerHi_of_plain b hb]
  exact ⟨hmass, hmass⟩

lemma ledgerHi_nonpos_of_not_pos (a : AgentState L K) (h3 : 3 ≤ a.phase.val)
    (hnp : ∀ i, a.bias ≠ .dyadic .pos i) : ledgerHi a ≤ 0 := by
  rcases hb : a.bias with _ | ⟨s, i⟩
  · exact le_of_eq (ledgerHi_eq_zero_of_bias_zero a h3 hb)
  · cases s
    · exact absurd hb (hnp i)
    · have hpos_i := one_div_two_pow_pos i.val
      have hpos_i1 := one_div_two_pow_pos (i.val + 1)
      unfold ledgerHi
      split_ifs
      · rw [hb]
        show -(1 : ℚ) / 2 ^ (i.val + 1) ≤ 0
        rw [neg_div]
        linarith
      · rw [prePhase4Mass_of_phase_ge_three a h3, hb]
        show -(1 : ℚ) / 2 ^ i.val ≤ 0
        rw [neg_div]
        linarith

lemma ledgerLo_nonneg_of_not_neg (a : AgentState L K) (h3 : 3 ≤ a.phase.val)
    (hnn : ∀ i, a.bias ≠ .dyadic .neg i) : 0 ≤ ledgerLo a := by
  rcases hb : a.bias with _ | ⟨s, i⟩
  · exact ge_of_eq (ledgerLo_eq_zero_of_bias_zero a h3 hb)
  · cases s
    · have hpos_i := one_div_two_pow_pos i.val
      have hpos_i1 := one_div_two_pow_pos (i.val + 1)
      unfold ledgerLo
      split_ifs
      · rw [hb]
        show (0 : ℚ) ≤ 1 / 2 ^ (i.val + 1)
        linarith
      · rw [prePhase4Mass_of_phase_ge_three a h3, hb]
        show (0 : ℚ) ≤ 1 / 2 ^ i.val
        linarith
    · exact absurd hb (hnn i)

lemma ledgerLo_pos_of_pos (a : AgentState L K) (h3 : 3 ≤ a.phase.val) (i : Fin (L + 1))
    (hb : a.bias = .dyadic .pos i) : 0 < ledgerLo a := by
  have hpos_i := one_div_two_pow_pos i.val
  have hpos_i1 := one_div_two_pow_pos (i.val + 1)
  unfold ledgerLo
  split_ifs
  · rw [hb]
    show (0 : ℚ) < 1 / 2 ^ (i.val + 1)
    exact hpos_i1
  · rw [prePhase4Mass_of_phase_ge_three a h3, hb]
    show (0 : ℚ) < 1 / 2 ^ i.val
    exact hpos_i

lemma ledgerHi_neg_of_neg (a : AgentState L K) (h3 : 3 ≤ a.phase.val) (i : Fin (L + 1))
    (hb : a.bias = .dyadic .neg i) : ledgerHi a < 0 := by
  have hpos_i := one_div_two_pow_pos i.val
  have hpos_i1 := one_div_two_pow_pos (i.val + 1)
  unfold ledgerHi
  split_ifs
  · rw [hb]
    show -(1 : ℚ) / 2 ^ (i.val + 1) < 0
    rw [neg_div]
    linarith
  · rw [prePhase4Mass_of_phase_ge_three a h3, hb]
    show -(1 : ℚ) / 2 ^ i.val < 0
    rw [neg_div]
    linarith

/-! ## Multiset sums -/

private lemma sum_map_nonneg_of_forall {f : AgentState L K → ℚ} (c : Config (AgentState L K))
    (h : ∀ a ∈ c, 0 ≤ f a) : 0 ≤ (c.map f).sum := by
  induction c using Multiset.induction_on with
  | empty => simp
  | cons a c ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      have ha := h a (Multiset.mem_cons_self a c)
      have hc := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
      linarith

private lemma sum_map_nonpos_of_forall {f : AgentState L K → ℚ} (c : Config (AgentState L K))
    (h : ∀ a ∈ c, f a ≤ 0) : (c.map f).sum ≤ 0 := by
  induction c using Multiset.induction_on with
  | empty => simp
  | cons a c ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      have ha := h a (Multiset.mem_cons_self a c)
      have hc := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
      linarith

private lemma sum_map_pos_of_mem {f : AgentState L K → ℚ} (c : Config (AgentState L K))
    (hnn : ∀ a ∈ c, 0 ≤ f a) {a : AgentState L K} (ha : a ∈ c) (hpos : 0 < f a) :
    0 < (c.map f).sum := by
  induction c using Multiset.induction_on with
  | empty => simp at ha
  | cons b c ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      have hb := hnn b (Multiset.mem_cons_self b c)
      have hc := sum_map_nonneg_of_forall c (fun x hx => hnn x (Multiset.mem_cons_of_mem hx))
      rcases Multiset.mem_cons.mp ha with hab | hac
      · subst hab
        linarith
      · have := ih (fun x hx => hnn x (Multiset.mem_cons_of_mem hx)) hac
        linarith

private lemma sum_map_neg_of_mem {f : AgentState L K → ℚ} (c : Config (AgentState L K))
    (hnp : ∀ a ∈ c, f a ≤ 0) {a : AgentState L K} (ha : a ∈ c) (hneg : f a < 0) :
    (c.map f).sum < 0 := by
  induction c using Multiset.induction_on with
  | empty => simp at ha
  | cons b c ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      have hb := hnp b (Multiset.mem_cons_self b c)
      have hc := sum_map_nonpos_of_forall c (fun x hx => hnp x (Multiset.mem_cons_of_mem hx))
      rcases Multiset.mem_cons.mp ha with hab | hac
      · subst hab
        linarith
      · have := ih (fun x hx => hnp x (Multiset.mem_cons_of_mem hx)) hac
        linarith

lemma loSum_eq_prePhase4MassSum_of_phase_lt_eight (c : Config (AgentState L K))
    (h : ∀ a ∈ c, a.phase.val < 8) : loSum c = prePhase4MassSum c := by
  unfold loSum prePhase4MassSum
  congr 1
  exact Multiset.map_congr rfl (fun a ha => ledgerLo_of_phase_lt_eight a (h a ha))

lemma hiSum_eq_prePhase4MassSum_of_phase_lt_eight (c : Config (AgentState L K))
    (h : ∀ a ∈ c, a.phase.val < 8) : hiSum c = prePhase4MassSum c := by
  unfold hiSum prePhase4MassSum
  congr 1
  exact Multiset.map_congr rfl (fun a ha => ledgerHi_of_phase_lt_eight a (h a ha))

/-! ## `phaseInit` and `runInitsBetween` above phase 2 -/

/-- Inits 3-9 keep the phase and the role. -/
private lemma phaseInit_phase_role_of_three_le (p : Fin 11) (a : AgentState L K)
    (hp3 : 3 ≤ p.val) (hp9 : p.val ≤ 9) :
    (phaseInit L K p a).phase = a.phase ∧ (phaseInit L K p a).role = a.role := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  rcases p with ⟨n, hn⟩
  change 3 ≤ n at hp3
  change n ≤ 9 at hp9
  interval_cases n <;> cases role <;> simp [phaseInit]

/-- Inits 4-9 keep the dyadic bias. -/
private lemma phaseInit_bias_of_four_le (p : Fin 11) (a : AgentState L K)
    (hp4 : 4 ≤ p.val) (hp9 : p.val ≤ 9) :
    (phaseInit L K p a).bias = a.bias := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  rcases p with ⟨n, hn⟩
  change 4 ≤ n at hp4
  change n ≤ 9 at hp9
  interval_cases n <;> cases role <;> simp [phaseInit]

/-- Inits 3-9 other than Init 8 keep the `full` flag. -/
private lemma phaseInit_full_of_ne_eight (p : Fin 11) (a : AgentState L K)
    (hp3 : 3 ≤ p.val) (hp9 : p.val ≤ 9) (hne : p.val ≠ 8) :
    (phaseInit L K p a).full = a.full := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  rcases p with ⟨n, hn⟩
  change 3 ≤ n at hp3
  change n ≤ 9 at hp9
  change n ≠ 8 at hne
  interval_cases n <;> first | omega | (cases role <;> simp [phaseInit])

/-- Init 8 clears the `full` flag. -/
private lemma phaseInit_eight_full (p : Fin 11) (a : AgentState L K) (hp : p.val = 8) :
    (phaseInit L K p a).full = false := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  rcases p with ⟨n, hn⟩
  change n = 8 at hp
  subst hp
  cases role <;> simp [phaseInit]

/-- Init 3 converts a well-formed small bias (`2`, `3`, `4`, i.e. `-1, 0, +1`) into the dyadic
bias of the same rational value (non-Main agents carry small bias `3` and get bias zero). -/
private lemma toRat_phaseInit_three_bias_of_carrier (b : AgentState L K)
    (hmcr : b.role ≠ .mcr) (hcarrier : b.role ≠ .main → b.smallBias.val = 3)
    (hsmall : b.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    Bias.toRat (phaseInit L K ⟨3, by decide⟩ b).bias = (AgentState.smallBiasInt b : ℚ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsmall
  rcases hsmall with h | h | h <;> cases hrole : b.role <;>
    simp [phaseInit, AgentState.smallBiasInt, Bias.toRat, hrole, h] at hmcr hcarrier ⊢

/-- `phaseInit` keeps the phase or moves the agent to Phase 10. -/
private lemma ledger_phaseInit_phase_eq_or_ten (p : Fin 11) (a : AgentState L K) :
    (phaseInit L K p a).phase.val = a.phase.val ∨ (phaseInit L K p a).phase.val = 10 := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  cases role <;> fin_cases p <;>
    simp [phaseInit, enterPhase10, phase10] <;>
    (repeat' split_ifs) <;> simp_all

/-- The interval filter behind `runInitsBetween` gains exactly the element `n + 1`
when its upper end moves from `n` to `n + 1`. -/
private lemma ledger_range_filter_interval_succ (o n N : ℕ) (hon : o ≤ n) :
    (List.range N).filter (fun k => o < k ∧ k ≤ n + 1) =
      (List.range N).filter (fun k => o < k ∧ k ≤ n) ++
        (if n + 1 < N then [n + 1] else []) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.filter_append, ih]
    rcases lt_trichotomy N (n + 1) with h | h | h
    · simp [List.filter_cons, show ¬ n + 1 < N by omega, show ¬ n + 1 < N + 1 by omega,
        show N ≤ n by omega, show N ≤ n + 1 by omega]
    · subst h
      simp [List.filter_cons, show o < n + 1 by omega]
    · simp [List.filter_cons, show n + 1 < N by omega, show ¬ N ≤ n by omega,
        show ¬ N ≤ n + 1 by omega]

/-- Peel off the last Init of `runInitsBetween`. -/
private lemma ledger_runInitsBetween_succ (o n : ℕ) (a : AgentState L K) (hon : o ≤ n)
    (hn : n + 1 < 11) :
    runInitsBetween L K o (n + 1) a =
      phaseInit L K ⟨n + 1, hn⟩ (runInitsBetween L K o n a) := by
  unfold runInitsBetween
  rw [ledger_range_filter_interval_succ o n 11 hon, if_pos hn, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, dif_pos hn]

/-- `runInitsBetween o n` keeps the phase or moves the agent to Phase 10 (`o ≤ n ≤ 10`). -/
private lemma ledger_runInitsBetween_phase_eq_or_ten (o n : ℕ) (a : AgentState L K)
    (hon : o ≤ n) (hn : n ≤ 10) :
    (runInitsBetween L K o n a).phase.val = a.phase.val ∨
      (runInitsBetween L K o n a).phase.val = 10 := by
  induction n, hon using Nat.le_induction with
  | base => rw [runInitsBetween_self]; exact Or.inl rfl
  | succ n hon ih =>
      rw [ledger_runInitsBetween_succ o n a hon (by omega)]
      rcases ledger_phaseInit_phase_eq_or_ten ⟨n + 1, by omega⟩ (runInitsBetween L K o n a)
        with h | h
      · rw [h]; exact ih (by omega)
      · exact Or.inr h

/-- The carrier discipline (no MCR; non-Main agents carry small bias `3`) is transported along
`runInitsBetween`: `phaseInit` changes a role only from CR to Reserve and keeps `smallBias`. -/
private lemma ledger_runInitsBetween_role_wf (o n : ℕ) (a : AgentState L K) (hon : o ≤ n)
    (hn : n ≤ 10)
    (hmcr : a.role ≠ .mcr) (hcarrier : a.role ≠ .main → a.smallBias.val = 3) :
    (runInitsBetween L K o n a).role ≠ .mcr ∧
      ((runInitsBetween L K o n a).role ≠ .main →
        (runInitsBetween L K o n a).smallBias.val = 3) := by
  induction n, hon using Nat.le_induction with
  | base => rw [runInitsBetween_self]; exact ⟨hmcr, hcarrier⟩
  | succ n hon ih =>
      rw [ledger_runInitsBetween_succ o n a hon (by omega)]
      rw [phaseInit_smallBias_eq, phaseInit_role]
      have ih' := ih (by omega)
      split_ifs with h
      · exact ⟨by decide, fun _ => ih'.2 (by rw [h.2]; decide)⟩
      · exact ih'

/-- An MCR agent raised from phase 0 to a target in `[1, 10]` is sent to Phase 10 by Init 1. -/
private lemma ledger_runInitsBetween_mcr_zero_target_phase_ten
    (a : AgentState L K) (target : ℕ) (ha_role : a.role = .mcr)
    (htarget_ge : 1 ≤ target) (htarget_le : target ≤ 10) :
    (runInitsBetween L K 0 target
      ({ a with phase := ⟨target, by omega⟩ } : AgentState L K)).phase.val = 10 := by
  have key : ∀ n, 1 ≤ n → n ≤ 10 → ∀ b : AgentState L K, b.role = .mcr →
      (runInitsBetween L K 0 n b).phase.val = 10 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        intro _ b hb
        rw [ledger_runInitsBetween_succ 0 0 b (le_refl 0) (by decide), runInitsBetween_self]
        simp [phaseInit, hb, enterPhase10, phase10]
    | succ n hn ih =>
        intro hn1 b hb
        rw [ledger_runInitsBetween_succ 0 n b (by omega) (by omega)]
        rcases ledger_phaseInit_phase_eq_or_ten ⟨n + 1, by omega⟩ (runInitsBetween L K 0 n b)
          with h | h
        · rw [h]; exact ih (by omega) b hb
        · exact h
  exact key target htarget_ge htarget_le _ (by simpa using ha_role)

/-- Raised to the common target `p` and re-initialized, an agent keeps its ledger entries
(exactly: the Init 3 conversion keeps the label, Inits 4-9 keep the bias, Init 8 clears `full`,
and no Init below Phase 10 moves the phase), provided the run does not end in Phase 10. -/
private lemma ledger_runInitsBetween_eq
    (a : AgentState L K) (p : Fin 11)
    (hle : a.phase.val ≤ p.val) (hp9 : p.val ≤ 9)
    (hres : (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val ≠ 10)
    (hmcr : a.role ≠ .mcr) (hcarrier : a.role ≠ .main → a.smallBias.val = 3)
    (hgood : a.phase.val < 3 → 3 ≤ p.val → a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    ledgerLo (runInitsBetween L K a.phase.val p.val ({ a with phase := p })) = ledgerLo a ∧
      ledgerHi (runInitsBetween L K a.phase.val p.val ({ a with phase := p })) = ledgerHi a := by
  have hp11 : p.val < 11 := p.2
  set a' : AgentState L K := { a with phase := p } with ha'
  set o := a.phase.val with ho
  have ha'_phase : a'.phase.val = p.val := by simp [ha']
  have ha'_bias : a'.bias = a.bias := by simp [ha']
  have ha'_full : a'.full = a.full := by simp [ha']
  have ha'_small : a'.smallBias = a.smallBias := by simp [ha']
  have ha'_role : a'.role = a.role := by simp [ha']
  -- the result sits at the target phase
  have hphase : (runInitsBetween L K o p.val a').phase.val = p.val := by
    rcases ledger_runInitsBetween_phase_eq_or_ten o p.val a' hle (by omega) with h | h
    · rw [h, ha'_phase]
    · exact absurd h hres
  have hsmall : (runInitsBetween L K o p.val a').smallBias = a.smallBias := by
    rw [runInitsBetween_preserves_smallBias, ha'_small]
  have ha_plain_lt : ∀ h : o < 8, ¬ (8 ≤ a.phase.val ∧ a.full = true) :=
    fun h => plain_of_phase_lt_eight a h
  by_cases hp3 : p.val < 3
  · -- below phase 3 the label is the small bias, which every Init keeps
    have ho3 : o < 3 := by omega
    refine ledger_eq_of_plain_of_mass_eq (ha_plain_lt (by omega))
      (plain_of_phase_lt_eight (runInitsBetween L K o p.val a') (by rw [hphase]; omega)) ?_
    rw [prePhase4Mass_of_phase_lt_three a ho3,
      prePhase4Mass_of_phase_lt_three (runInitsBetween L K o p.val a')
        (by rw [hphase]; exact hp3)]
    simp [AgentState.smallBiasInt, hsmall]
  push_neg at hp3
  -- the `full` flag when Init 8 ran
  have hfull_eight : o < 8 → 8 ≤ p.val →
      (runInitsBetween L K o p.val a').full = false := by
    intro ho8 hp8
    have h8 : runInitsBetween L K o 8 a' = phaseInit L K ⟨8, by decide⟩
        (runInitsBetween L K o 7 a') :=
      ledger_runInitsBetween_succ o 7 a' (by omega) (by decide)
    have hfull8 : (runInitsBetween L K o 8 a').full = false := by
      rw [h8]; exact phaseInit_eight_full _ _ rfl
    rcases (show p.val = 8 ∨ p.val = 9 by omega) with h | h
    · rw [h]; exact hfull8
    · have h9 : runInitsBetween L K o 9 a' = phaseInit L K ⟨9, by decide⟩
          (runInitsBetween L K o 8 a') :=
        ledger_runInitsBetween_succ o 8 a' (by omega) (by decide)
      have hfull9 : (phaseInit L K ⟨9, by decide⟩ (runInitsBetween L K o 8 a')).full =
          (runInitsBetween L K o 8 a').full :=
        phaseInit_full_of_ne_eight ⟨9, by decide⟩ _ (by decide) (by decide) (by decide)
      rw [h, h9, hfull9]
      exact hfull8
  by_cases ho3 : 3 ≤ o
  · -- already in the dyadic window: Inits 4-9 keep the bias
    have hbias : ∀ n, o ≤ n → n ≤ p.val → (runInitsBetween L K o n a').bias = a.bias := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => intro _; simp only [runInitsBetween_self, ha']
      | succ n hon ih =>
          intro hn1
          have hlt : n + 1 < 11 := by omega
          have hstep : (phaseInit L K ⟨n + 1, hlt⟩ (runInitsBetween L K o n a')).bias =
              (runInitsBetween L K o n a').bias :=
            phaseInit_bias_of_four_le ⟨n + 1, hlt⟩ _ (by show 4 ≤ n + 1; omega)
              (by show n + 1 ≤ 9; omega)
          rw [ledger_runInitsBetween_succ o n a' hon hlt, hstep]
          exact ih (by omega)
    have hbias' := hbias p.val hle (le_refl _)
    have hmass : prePhase4Mass (runInitsBetween L K o p.val a') = prePhase4Mass a := by
      rw [prePhase4Mass_of_phase_ge_three a ho3,
        prePhase4Mass_of_phase_ge_three (runInitsBetween L K o p.val a')
          (by rw [hphase]; omega), hbias']
    by_cases ho8 : 8 ≤ o
    · -- Inits 9 only: `full` is kept
      have hfull : ∀ n, o ≤ n → n ≤ p.val →
          (runInitsBetween L K o n a').full = a.full := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base => intro _; simp only [runInitsBetween_self, ha']
        | succ n hon ih =>
            intro hn1
            have hlt : n + 1 < 11 := by omega
            have hstep : (phaseInit L K ⟨n + 1, hlt⟩ (runInitsBetween L K o n a')).full =
                (runInitsBetween L K o n a').full :=
              phaseInit_full_of_ne_eight ⟨n + 1, hlt⟩ _ (by show 3 ≤ n + 1; omega)
                (by show n + 1 ≤ 9; omega) (by show n + 1 ≠ 8; omega)
            rw [ledger_runInitsBetween_succ o n a' hon hlt, hstep]
            exact ih (by omega)
      exact ledger_congr_of_ge_three ho3 (by rw [hphase]; omega)
        (by rw [hphase]; exact ⟨fun _ => ho8, fun _ => by omega⟩)
        (hfull p.val hle (le_refl _)) hbias'
    · push_neg at ho8
      by_cases hp8 : p.val < 8
      · exact ledger_eq_of_plain_of_mass_eq (ha_plain_lt ho8)
          (plain_of_phase_lt_eight (runInitsBetween L K o p.val a') (by rw [hphase]; omega))
          hmass
      · push_neg at hp8
        exact ledger_eq_of_plain_of_mass_eq (ha_plain_lt ho8)
          (plain_of_full_false _ (hfull_eight ho8 hp8)) hmass
  · push_neg at ho3
    -- crossing Init 3: the small bias becomes the dyadic bias of the same value
    have hY := ledger_runInitsBetween_role_wf o 2 a' (by omega) (by omega)
      (by rw [ha'_role]; exact hmcr) (by rw [ha'_role, ha'_small]; exact hcarrier)
    have hYsmall : (runInitsBetween L K o 2 a').smallBias = a.smallBias := by
      rw [runInitsBetween_preserves_smallBias, ha'_small]
    have h3 : runInitsBetween L K o 3 a' = phaseInit L K ⟨3, by decide⟩
        (runInitsBetween L K o 2 a') :=
      ledger_runInitsBetween_succ o 2 a' (by omega) (by decide)
    have hX : Bias.toRat (runInitsBetween L K o 3 a').bias =
        (AgentState.smallBiasInt a : ℚ) := by
      rw [h3, toRat_phaseInit_three_bias_of_carrier _ hY.1 hY.2
        (by rw [hYsmall]; exact hgood ho3 hp3)]
      simp only [AgentState.smallBiasInt, hYsmall]
    have hbias : ∀ n, 3 ≤ n → n ≤ p.val →
        Bias.toRat (runInitsBetween L K o n a').bias = (AgentState.smallBiasInt a : ℚ) := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => intro _; exact hX
      | succ n hon ih =>
          intro hn1
          have hlt : n + 1 < 11 := by omega
          have hstep : (phaseInit L K ⟨n + 1, hlt⟩ (runInitsBetween L K o n a')).bias =
              (runInitsBetween L K o n a').bias :=
            phaseInit_bias_of_four_le ⟨n + 1, hlt⟩ _ (by show 4 ≤ n + 1; omega)
              (by show n + 1 ≤ 9; omega)
          rw [ledger_runInitsBetween_succ o n a' (by omega) hlt, hstep]
          exact ih (by omega)
    have hmass : prePhase4Mass (runInitsBetween L K o p.val a') = prePhase4Mass a := by
      rw [prePhase4Mass_of_phase_lt_three a ho3,
        prePhase4Mass_of_phase_ge_three (runInitsBetween L K o p.val a')
          (by rw [hphase]; omega)]
      exact hbias p.val hp3 (le_refl _)
    by_cases hp8 : p.val < 8
    · exact ledger_eq_of_plain_of_mass_eq (ha_plain_lt (by omega))
        (plain_of_phase_lt_eight (runInitsBetween L K o p.val a') (by rw [hphase]; omega))
        hmass
    · push_neg at hp8
      exact ledger_eq_of_plain_of_mass_eq (ha_plain_lt (by omega))
        (plain_of_full_false _ (hfull_eight (by omega) hp8)) hmass

/-! ## The epidemic stage -/

lemma ledger_max_phase_val (s t : AgentState L K) :
    (max s.phase t.phase).val = max s.phase.val t.phase.val := by
  simp only [max_def, Fin.le_def]
  split_ifs <;> rfl

/-- Below Phase 10 the left epidemic output is the plain re-initialization of the left agent. -/
lemma ledger_epidemic_fst_eq (s t : AgentState L K)
    (h : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10) :
    (phaseEpidemicUpdate L K s t).1 =
      runInitsBetween L K s.phase.val (max s.phase t.phase).val
        ({ s with phase := max s.phase t.phase }) := by
  unfold phaseEpidemicUpdate at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hc
  · dsimp only at h ⊢
    unfold phase10EpidemicEntry at h ⊢
    split_ifs at h ⊢ with hs
    · simp [enterPhase10, phase10] at h
    · rfl
  · rfl

lemma ledger_epidemic_snd_eq (s t : AgentState L K)
    (h : (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10) :
    (phaseEpidemicUpdate L K s t).2 =
      runInitsBetween L K t.phase.val (max s.phase t.phase).val
        ({ t with phase := max s.phase t.phase }) := by
  unfold phaseEpidemicUpdate at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hc
  · dsimp only at h ⊢
    unfold phase10EpidemicEntry at h ⊢
    split_ifs at h ⊢ with ht
    · simp [enterPhase10, phase10] at h
    · rfl
  · rfl

/-- The epidemic outputs sit at the common target when not in Phase 10. -/
lemma ledger_epidemic_phase_eq_max (s t : AgentState L K)
    (h : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10) :
    (phaseEpidemicUpdate L K s t).1.phase.val = max s.phase.val t.phase.val := by
  have heq := ledger_epidemic_fst_eq s t h
  have h' : (runInitsBetween L K s.phase.val (max s.phase t.phase).val
      ({ s with phase := max s.phase t.phase })).phase.val ≠ 10 := by
    rw [← heq]; exact h
  rw [heq]
  rcases ledger_runInitsBetween_phase_eq_or_ten s.phase.val (max s.phase t.phase).val
      ({ s with phase := max s.phase t.phase })
      (by rw [ledger_max_phase_val]; exact le_max_left _ _)
      (by have := (max s.phase t.phase).2; omega) with h'' | h''
  · rw [h''] <;> simp [ledger_max_phase_val]
  · exact absurd h'' h'

lemma ledger_epidemic_phase_eq_max_snd (s t : AgentState L K)
    (h : (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10) :
    (phaseEpidemicUpdate L K s t).2.phase.val = max s.phase.val t.phase.val := by
  have heq := ledger_epidemic_snd_eq s t h
  have h' : (runInitsBetween L K t.phase.val (max s.phase t.phase).val
      ({ t with phase := max s.phase t.phase })).phase.val ≠ 10 := by
    rw [← heq]; exact h
  rw [heq]
  rcases ledger_runInitsBetween_phase_eq_or_ten t.phase.val (max s.phase t.phase).val
      ({ t with phase := max s.phase t.phase })
      (by rw [ledger_max_phase_val]; exact le_max_right _ _)
      (by have := (max s.phase t.phase).2; omega) with h'' | h''
  · rw [h''] <;> simp [ledger_max_phase_val]
  · exact absurd h'' h'

/-- Ledger entries of the left epidemic output. -/
private lemma ledger_epidemic_left (s t : AgentState L K)
    (hs_mcr : s.role ≠ .mcr) (hs_carrier : s.role ≠ .main → s.smallBias.val = 3)
    (hs_noerr : 2 ≤ s.phase.val → s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hne : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10) :
    ledgerLo (phaseEpidemicUpdate L K s t).1 = ledgerLo s ∧
      ledgerHi (phaseEpidemicUpdate L K s t).1 = ledgerHi s := by
  have hp := ledger_epidemic_phase_eq_max s t hne
  have hb11 := (phaseEpidemicUpdate L K s t).1.phase.2
  have hmax9 : (max s.phase t.phase).val ≤ 9 := by
    rw [ledger_max_phase_val]; omega
  have hgood : s.phase.val < 3 → 3 ≤ (max s.phase t.phase).val →
      s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
    intro h3 hmax
    rw [ledger_max_phase_val] at hmax
    by_cases h2 : 2 ≤ s.phase.val
    · exact hs_noerr h2
    · push_neg at h2
      have hsm := phaseEpidemicUpdate_left_smallBias_noerror_of_entered_not_ten
        (L := L) (K := K) s t h2 (by omega) hne
      rwa [(phaseEpidemicUpdate_preserves_smallBias L K s t).1] at hsm
  have heq := ledger_epidemic_fst_eq s t hne
  have hne' : (runInitsBetween L K s.phase.val (max s.phase t.phase).val
      ({ s with phase := max s.phase t.phase })).phase.val ≠ 10 := by
    rw [← heq]; exact hne
  rw [heq]
  exact ledger_runInitsBetween_eq s (max s.phase t.phase)
    (by rw [ledger_max_phase_val]; exact le_max_left _ _) hmax9 hne' hs_mcr hs_carrier hgood

private lemma ledger_epidemic_right (s t : AgentState L K)
    (ht_mcr : t.role ≠ .mcr) (ht_carrier : t.role ≠ .main → t.smallBias.val = 3)
    (ht_noerr : 2 ≤ t.phase.val → t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hne : (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10) :
    ledgerLo (phaseEpidemicUpdate L K s t).2 = ledgerLo t ∧
      ledgerHi (phaseEpidemicUpdate L K s t).2 = ledgerHi t := by
  have hp := ledger_epidemic_phase_eq_max_snd s t hne
  have hb11 := (phaseEpidemicUpdate L K s t).2.phase.2
  have hmax9 : (max s.phase t.phase).val ≤ 9 := by
    rw [ledger_max_phase_val]; omega
  have hgood : t.phase.val < 3 → 3 ≤ (max s.phase t.phase).val →
      t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
    intro h3 hmax
    rw [ledger_max_phase_val] at hmax
    by_cases h2 : 2 ≤ t.phase.val
    · exact ht_noerr h2
    · push_neg at h2
      have htm := phaseEpidemicUpdate_right_smallBias_noerror_of_entered_not_ten
        (L := L) (K := K) s t h2 (by omega) hne
      rwa [(phaseEpidemicUpdate_preserves_smallBias L K s t).2] at htm
  have heq := ledger_epidemic_snd_eq s t hne
  have hne' : (runInitsBetween L K t.phase.val (max s.phase t.phase).val
      ({ t with phase := max s.phase t.phase })).phase.val ≠ 10 := by
    rw [← heq]; exact hne
  rw [heq]
  exact ledger_runInitsBetween_eq t (max s.phase t.phase)
    (by rw [ledger_max_phase_val]; exact le_max_right _ _) hmax9 hne' ht_mcr ht_carrier hgood

/-- The carrier discipline and the small-bias range of the left epidemic output. -/
private lemma ledger_epidemic_wf_left (s t : AgentState L K)
    (hs_mcr : s.role ≠ .mcr) (hs_carrier : s.role ≠ .main → s.smallBias.val = 3)
    (hs_noerr : 2 ≤ s.phase.val → s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hne : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10) :
    (phaseEpidemicUpdate L K s t).1.role ≠ .mcr ∧
      ((phaseEpidemicUpdate L K s t).1.role ≠ .main →
        (phaseEpidemicUpdate L K s t).1.smallBias.val = 3) ∧
      (2 ≤ (phaseEpidemicUpdate L K s t).1.phase.val →
        (phaseEpidemicUpdate L K s t).1.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) := by
  have hsmall := (phaseEpidemicUpdate_preserves_smallBias L K s t).1
  have hmax10 : (max s.phase t.phase).val ≤ 10 := by
    have := (max s.phase t.phase).2; omega
  have hwf := ledger_runInitsBetween_role_wf s.phase.val (max s.phase t.phase).val
    ({ s with phase := max s.phase t.phase })
    (by rw [ledger_max_phase_val]; exact le_max_left _ _) hmax10
    (by simpa using hs_mcr) (by simpa using hs_carrier)
  rw [← ledger_epidemic_fst_eq s t hne] at hwf
  refine ⟨hwf.1, hwf.2, ?_⟩
  intro h2
  by_cases hs2 : 2 ≤ s.phase.val
  · rw [hsmall]; exact hs_noerr hs2
  · push_neg at hs2
    exact phaseEpidemicUpdate_left_smallBias_noerror_of_entered_not_ten
      (L := L) (K := K) s t hs2 h2 hne

private lemma ledger_epidemic_wf_right (s t : AgentState L K)
    (ht_mcr : t.role ≠ .mcr) (ht_carrier : t.role ≠ .main → t.smallBias.val = 3)
    (ht_noerr : 2 ≤ t.phase.val → t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hne : (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10) :
    (phaseEpidemicUpdate L K s t).2.role ≠ .mcr ∧
      ((phaseEpidemicUpdate L K s t).2.role ≠ .main →
        (phaseEpidemicUpdate L K s t).2.smallBias.val = 3) ∧
      (2 ≤ (phaseEpidemicUpdate L K s t).2.phase.val →
        (phaseEpidemicUpdate L K s t).2.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) := by
  have hsmall := (phaseEpidemicUpdate_preserves_smallBias L K s t).2
  have hmax10 : (max s.phase t.phase).val ≤ 10 := by
    have := (max s.phase t.phase).2; omega
  have hwf := ledger_runInitsBetween_role_wf t.phase.val (max s.phase t.phase).val
    ({ t with phase := max s.phase t.phase })
    (by rw [ledger_max_phase_val]; exact le_max_right _ _) hmax10
    (by simpa using ht_mcr) (by simpa using ht_carrier)
  rw [← ledger_epidemic_snd_eq s t hne] at hwf
  refine ⟨hwf.1, hwf.2, ?_⟩
  intro h2
  by_cases ht2 : 2 ≤ t.phase.val
  · rw [hsmall]; exact ht_noerr ht2
  · push_neg at ht2
    exact phaseEpidemicUpdate_right_smallBias_noerror_of_entered_not_ten
      (L := L) (K := K) s t ht2 h2 hne

/-! ## The counter subroutine between phases 2 and 8 -/

private lemma advancePhase_eq_of_lt (a : AgentState L K) (h : a.phase.val < 10) :
    advancePhase L K a = { a with phase := ⟨a.phase.val + 1, by omega⟩ } := by
  unfold advancePhase
  exact dif_pos h

private lemma advancePhaseWithInit_eq_of_lt (a : AgentState L K) (h : a.phase.val < 10) :
    advancePhaseWithInit L K a =
      phaseInit L K ⟨a.phase.val + 1, by omega⟩ ({ a with phase := ⟨a.phase.val + 1, by omega⟩ }) := by
  simp only [advancePhaseWithInit, advancePhase_eq_of_lt a h]

/-- From a phase in `[2, 8]` the timed advance lands exactly one phase higher: the destination
Init (3-9) never errors. -/
private lemma advancePhaseWithInit_phase_of_mid (a : AgentState L K)
    (h2 : 2 ≤ a.phase.val) (h8 : a.phase.val ≤ 8) :
    (advancePhaseWithInit L K a).phase.val = a.phase.val + 1 := by
  rw [advancePhaseWithInit_eq_of_lt a (by omega),
    (phaseInit_phase_role_of_three_le ⟨a.phase.val + 1, by omega⟩
      ({ a with phase := ⟨a.phase.val + 1, by omega⟩ })
      (by dsimp only; omega) (by dsimp only; omega)).1]

private lemma advancePhaseWithInit_role_of_mid (a : AgentState L K)
    (h2 : 2 ≤ a.phase.val) (h8 : a.phase.val ≤ 8) :
    (advancePhaseWithInit L K a).role = a.role := by
  rw [advancePhaseWithInit_eq_of_lt a (by omega),
    (phaseInit_phase_role_of_three_le ⟨a.phase.val + 1, by omega⟩
      ({ a with phase := ⟨a.phase.val + 1, by omega⟩ })
      (by dsimp only; omega) (by dsimp only; omega)).2]

private lemma advancePhaseWithInit_bias_of_mid (a : AgentState L K)
    (h3 : 3 ≤ a.phase.val) (h8 : a.phase.val ≤ 8) :
    (advancePhaseWithInit L K a).bias = a.bias := by
  rw [advancePhaseWithInit_eq_of_lt a (by omega),
    phaseInit_bias_of_four_le ⟨a.phase.val + 1, by omega⟩
      ({ a with phase := ⟨a.phase.val + 1, by omega⟩ })
      (by dsimp only; omega) (by dsimp only; omega)]

private lemma advancePhaseWithInit_full_of_mid (a : AgentState L K)
    (h2 : 2 ≤ a.phase.val) (h8 : a.phase.val ≤ 8) (hne : a.phase.val ≠ 7) :
    (advancePhaseWithInit L K a).full = a.full := by
  rw [advancePhaseWithInit_eq_of_lt a (by omega),
    phaseInit_full_of_ne_eight ⟨a.phase.val + 1, by omega⟩
      ({ a with phase := ⟨a.phase.val + 1, by omega⟩ })
      (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]

private lemma advancePhaseWithInit_full_of_seven (a : AgentState L K)
    (h7 : a.phase.val = 7) :
    (advancePhaseWithInit L K a).full = false := by
  rw [advancePhaseWithInit_eq_of_lt a (by omega)]
  exact phaseInit_eight_full _ _ (by dsimp only; omega)

/-- From Phase 9 the timed advance enters Phase 10. -/
private lemma advancePhaseWithInit_phase_of_nine (a : AgentState L K) (h9 : a.phase.val = 9) :
    (advancePhaseWithInit L K a).phase.val = 10 := by
  rw [advancePhaseWithInit_eq_of_lt a (by omega)]
  simp [phaseInit, h9, enterPhase10, phase10]

/-- `stdCounterSubroutine` from a phase in `[3, 8]`: the bias and the role are kept, the phase
moves by at most one, and `full` is kept except through Init 8. -/
private lemma stdCounterSubroutine_mid (a : AgentState L K)
    (h3 : 3 ≤ a.phase.val) (h8 : a.phase.val ≤ 8) :
    (stdCounterSubroutine L K a).bias = a.bias ∧
      (stdCounterSubroutine L K a).role = a.role ∧
      a.phase.val ≤ (stdCounterSubroutine L K a).phase.val ∧
      (stdCounterSubroutine L K a).phase.val ≤ a.phase.val + 1 ∧
      ((stdCounterSubroutine L K a).phase.val = a.phase.val →
        (stdCounterSubroutine L K a).full = a.full) ∧
      ((stdCounterSubroutine L K a).phase.val = a.phase.val + 1 → a.phase.val ≠ 7 →
        (stdCounterSubroutine L K a).full = a.full) ∧
      ((stdCounterSubroutine L K a).phase.val = a.phase.val + 1 → a.phase.val = 7 →
        (stdCounterSubroutine L K a).full = false) := by
  unfold stdCounterSubroutine
  split_ifs with hc
  · have hp := advancePhaseWithInit_phase_of_mid a (by omega) h8
    refine ⟨advancePhaseWithInit_bias_of_mid a h3 h8,
      advancePhaseWithInit_role_of_mid a (by omega) h8, by omega, by omega,
      fun h => by omega,
      fun _ hne => advancePhaseWithInit_full_of_mid a (by omega) h8 hne,
      fun _ h7 => advancePhaseWithInit_full_of_seven a h7⟩
  · refine ⟨rfl, rfl, le_refl _, Nat.le_succ _, fun _ => rfl, ?_, ?_⟩
    · intro h _
      exfalso
      change a.phase.val = a.phase.val + 1 at h
      omega
    · intro h _
      exfalso
      change a.phase.val = a.phase.val + 1 at h
      omega

/-- A clock step from a plain agent in `[3, 7]` yields a plain agent with the same bias and the
same ledger entries. -/
private lemma stdCounterSubroutine_ledger_of_plain (a : AgentState L K)
    (h3 : 3 ≤ a.phase.val) (h7 : a.phase.val ≤ 7) :
    ledgerLo (stdCounterSubroutine L K a) = ledgerLo a ∧
      ledgerHi (stdCounterSubroutine L K a) = ledgerHi a := by
  obtain ⟨hbias, _, hge, hle, _, _, hfull_seven⟩ :=
    stdCounterSubroutine_mid a h3 (by omega)
  have hplain : ¬ (8 ≤ (stdCounterSubroutine L K a).phase.val ∧
      (stdCounterSubroutine L K a).full = true) := by
    rintro ⟨h8, hf⟩
    have hp : (stdCounterSubroutine L K a).phase.val = a.phase.val + 1 := by omega
    have h7' : a.phase.val = 7 := by omega
    rw [hfull_seven hp h7'] at hf
    exact Bool.false_ne_true hf
  refine ledger_eq_of_plain_of_mass_eq (plain_of_phase_lt_eight a (by omega)) hplain ?_
  rw [prePhase4Mass_of_phase_ge_three a h3,
    prePhase4Mass_of_phase_ge_three (stdCounterSubroutine L K a) (by omega), hbias]

/-- A clock step from an agent at phase 8 keeps `bias`, `full` and stays at phase `≥ 8`. -/
private lemma stdCounterSubroutine_ledger_of_eight (a : AgentState L K)
    (h8 : a.phase.val = 8) :
    ledgerLo (stdCounterSubroutine L K a) = ledgerLo a ∧
      ledgerHi (stdCounterSubroutine L K a) = ledgerHi a := by
  obtain ⟨hbias, _, hge, hle, hfull_eq, hfull_ne, _⟩ :=
    stdCounterSubroutine_mid a (by omega) (by omega)
  have hfull : (stdCounterSubroutine L K a).full = a.full := by
    rcases (show (stdCounterSubroutine L K a).phase.val = a.phase.val ∨
        (stdCounterSubroutine L K a).phase.val = a.phase.val + 1 by omega) with h | h
    · exact hfull_eq h
    · exact hfull_ne h (by omega)
  exact ledger_congr_of_ge_three (by omega) (by omega) (by constructor <;> intro _ <;> omega)
    hfull hbias

/-- The clock wrapper of phases 5-8 on a plain agent in `[3, 7]`. -/
private lemma clock_wrap_ledger_of_plain (a : AgentState L K)
    (h3 : 3 ≤ a.phase.val) (h7 : a.phase.val ≤ 7) :
    ledgerLo (if a.role = .clock then stdCounterSubroutine L K a else a) = ledgerLo a ∧
      ledgerHi (if a.role = .clock then stdCounterSubroutine L K a else a) = ledgerHi a := by
  split_ifs
  · exact stdCounterSubroutine_ledger_of_plain a h3 h7
  · exact ⟨rfl, rfl⟩

private lemma clock_wrap_ledger_of_eight (a : AgentState L K) (h8 : a.phase.val = 8) :
    ledgerLo (if a.role = .clock then stdCounterSubroutine L K a else a) = ledgerLo a ∧
      ledgerHi (if a.role = .clock then stdCounterSubroutine L K a else a) = ledgerHi a := by
  split_ifs
  · exact stdCounterSubroutine_ledger_of_eight a h8
  · exact ⟨rfl, rfl⟩

/-! ## The per-phase dispatch (phases 2-9) -/

/-- Phase 2: the opinion epidemic; the advance to Phase 3 converts the small bias. -/
private lemma phase2_dispatch_ledger (s t : AgentState L K)
    (hs : s.phase.val = 2) (ht : t.phase.val = 2)
    (hs_mcr : s.role ≠ .mcr) (ht_mcr : t.role ≠ .mcr)
    (hs_carrier : s.role ≠ .main → s.smallBias.val = 3)
    (ht_carrier : t.role ≠ .main → t.smallBias.val = 3)
    (hs_small : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (ht_small : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    ledgerLo (Phase2Transition L K s t).1 + ledgerLo (Phase2Transition L K s t).2 =
        ledgerLo s + ledgerLo t ∧
      ledgerHi (Phase2Transition L K s t).1 + ledgerHi (Phase2Transition L K s t).2 =
        ledgerHi s + ledgerHi t := by
  have hmass := Phase2Transition_preserves_prePhase4Mass_pair_of_phase_two_wf
    (L := L) (K := K) s t hs ht hs_mcr ht_mcr hs_carrier ht_carrier
    (by simpa using hs_small) (by simpa using ht_small)
  -- every output is at phase 2 or 3
  have hout : (Phase2Transition L K s t).1.phase.val < 8 ∧
      (Phase2Transition L K s t).2.phase.val < 8 := by
    unfold Phase2Transition
    dsimp only
    split_ifs
    · have h1 := advancePhaseWithInit_phase_of_mid
        ({ s with opinions := opinionsUnion s.opinions t.opinions })
        (by dsimp only; omega) (by dsimp only; omega)
      have h2 := advancePhaseWithInit_phase_of_mid
        ({ t with opinions := opinionsUnion s.opinions t.opinions })
        (by dsimp only; omega) (by dsimp only; omega)
      dsimp only at h1 h2 ⊢
      constructor <;> omega
    all_goals (constructor <;> dsimp only <;> omega)
  rw [ledgerLo_of_phase_lt_eight _ hout.1, ledgerLo_of_phase_lt_eight _ hout.2,
    ledgerHi_of_phase_lt_eight _ hout.1, ledgerHi_of_phase_lt_eight _ hout.2,
    ledgerLo_of_phase_lt_eight s (by omega), ledgerLo_of_phase_lt_eight t (by omega),
    ledgerHi_of_phase_lt_eight s (by omega), ledgerHi_of_phase_lt_eight t (by omega)]
  exact ⟨hmass, hmass⟩

/-- Output phases of the Phase-3 dispatch from two phase-3 agents. -/
private lemma Phase3Transition_phase_le_four (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    (Phase3Transition L K s t).1.phase.val ≤ 4 ∧ (Phase3Transition L K s t).2.phase.val ≤ 4 := by
  have hstd_s := (stdCounterSubroutine_mid s (by omega) (by omega)).2.2.2.1
  have hstd_t := (stdCounterSubroutine_mid t (by omega) (by omega)).2.2.2.1
  unfold Phase3Transition
  let s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else stdCounterSubroutine L K s
  else s
  let t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then t
    else stdCounterSubroutine L K t
  else t
  let s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1 : s1.phase.val ≤ 4 := by
    dsimp [s1]; split_ifs <;> first | omega | (show s.phase.val ≤ 4; omega)
  have ht1 : t1.phase.val ≤ 4 := by
    dsimp [t1]; split_ifs <;> first | omega | (show t.phase.val ≤ 4; omega)
  have hs2 : s1.phase.val = s2.phase.val := by dsimp [s2]; split_ifs <;> rfl
  have ht2 : t1.phase.val = t2.phase.val := by dsimp [t2]; split_ifs <;> rfl
  rcases phase3CancelSplit_phase_preserved L K s2 t2 with ⟨h_cs_s, h_cs_t⟩
  refine ⟨?_, ?_⟩
  · change (if s2.role = .main ∧ t2.role = .main then
            phase3CancelSplit L K s2 t2 else (s2, t2)).1.phase.val ≤ 4
    split_ifs
    · rw [h_cs_s]; omega
    · change s2.phase.val ≤ 4; omega
  · change (if s2.role = .main ∧ t2.role = .main then
            phase3CancelSplit L K s2 t2 else (s2, t2)).2.phase.val ≤ 4
    split_ifs
    · rw [h_cs_t]; omega
    · change t2.phase.val ≤ 4; omega

/-- Phase 3: the dyadic cancel/split keeps the mass; clocks may advance to Phase 4. -/
private lemma phase3_dispatch_ledger (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    ledgerLo (Phase3Transition L K s t).1 + ledgerLo (Phase3Transition L K s t).2 =
        ledgerLo s + ledgerLo t ∧
      ledgerHi (Phase3Transition L K s t).1 + ledgerHi (Phase3Transition L K s t).2 =
        ledgerHi s + ledgerHi t := by
  have hmass := Phase3Transition_preserves_prePhase4Mass_pair_of_phase_three
    (L := L) (K := K) s t hs ht
  have hout := Phase3Transition_phase_le_four s t hs ht
  rw [ledgerLo_of_phase_lt_eight (Phase3Transition L K s t).1 (by omega),
    ledgerLo_of_phase_lt_eight (Phase3Transition L K s t).2 (by omega),
    ledgerHi_of_phase_lt_eight (Phase3Transition L K s t).1 (by omega),
    ledgerHi_of_phase_lt_eight (Phase3Transition L K s t).2 (by omega),
    ledgerLo_of_phase_lt_eight s (by omega), ledgerLo_of_phase_lt_eight t (by omega),
    ledgerHi_of_phase_lt_eight s (by omega), ledgerHi_of_phase_lt_eight t (by omega)]
  exact ⟨hmass, hmass⟩

/-- Phase 4: a big bias advances the pair to Phase 5 (Init 5 keeps the bias). -/
private lemma phase4_dispatch_ledger (s t : AgentState L K)
    (hs : s.phase.val = 4) (ht : t.phase.val = 4) :
    ledgerLo (Phase4Transition L K s t).1 + ledgerLo (Phase4Transition L K s t).2 =
        ledgerLo s + ledgerLo t ∧
      ledgerHi (Phase4Transition L K s t).1 + ledgerHi (Phase4Transition L K s t).2 =
        ledgerHi s + ledgerHi t := by
  have hmass := Phase4Transition_preserves_prePhase4Mass_pair_of_phase_four
    (L := L) (K := K) s t hs ht
  have hout : (Phase4Transition L K s t).1.phase.val < 8 ∧
      (Phase4Transition L K s t).2.phase.val < 8 := by
    unfold Phase4Transition
    dsimp only
    split_ifs
    · rw [advancePhaseWithInit_phase_of_mid s (by omega) (by omega),
        advancePhaseWithInit_phase_of_mid t (by omega) (by omega)]
      omega
    · dsimp only
      omega
  rw [ledgerLo_of_phase_lt_eight _ hout.1, ledgerLo_of_phase_lt_eight _ hout.2,
    ledgerHi_of_phase_lt_eight _ hout.1, ledgerHi_of_phase_lt_eight _ hout.2,
    ledgerLo_of_phase_lt_eight s (by omega), ledgerLo_of_phase_lt_eight t (by omega),
    ledgerHi_of_phase_lt_eight s (by omega), ledgerHi_of_phase_lt_eight t (by omega)]
  exact ⟨hmass, hmass⟩

/-- The common shape of the Phase-5/6/7 dispatch: two intermediate agents at the same phase
with a conserved dyadic mass, followed by the clock step. -/
private lemma clock_wrap_pair_ledger (s t s1 t1 : AgentState L K) (p : ℕ)
    (hp3 : 3 ≤ p) (hp7 : p ≤ 7)
    (hs : s.phase.val = p) (ht : t.phase.val = p)
    (hs1 : s1.phase.val = p) (ht1 : t1.phase.val = p)
    (hmass : Bias.toRat s1.bias + Bias.toRat t1.bias = Bias.toRat s.bias + Bias.toRat t.bias) :
    ledgerLo (if s1.role = .clock then stdCounterSubroutine L K s1 else s1) +
        ledgerLo (if t1.role = .clock then stdCounterSubroutine L K t1 else t1) =
      ledgerLo s + ledgerLo t ∧
    ledgerHi (if s1.role = .clock then stdCounterSubroutine L K s1 else s1) +
        ledgerHi (if t1.role = .clock then stdCounterSubroutine L K t1 else t1) =
      ledgerHi s + ledgerHi t := by
  obtain ⟨hs1lo, hs1hi⟩ := clock_wrap_ledger_of_plain s1 (by omega) (by omega)
  obtain ⟨ht1lo, ht1hi⟩ := clock_wrap_ledger_of_plain t1 (by omega) (by omega)
  rw [hs1lo, hs1hi, ht1lo, ht1hi,
    ledgerLo_of_phase_lt_eight s1 (by omega), ledgerLo_of_phase_lt_eight t1 (by omega),
    ledgerHi_of_phase_lt_eight s1 (by omega), ledgerHi_of_phase_lt_eight t1 (by omega),
    ledgerLo_of_phase_lt_eight s (by omega), ledgerLo_of_phase_lt_eight t (by omega),
    ledgerHi_of_phase_lt_eight s (by omega), ledgerHi_of_phase_lt_eight t (by omega),
    prePhase4Mass_of_phase_ge_three s1 (by omega), prePhase4Mass_of_phase_ge_three t1 (by omega),
    prePhase4Mass_of_phase_ge_three s (by omega), prePhase4Mass_of_phase_ge_three t (by omega)]
  exact ⟨hmass, hmass⟩

/-- Phase 5: sampling only writes `hour`. -/
private lemma phase5_dispatch_ledger (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 5) :
    ledgerLo (Phase5Transition L K s t).1 + ledgerLo (Phase5Transition L K s t).2 =
        ledgerLo s + ledgerLo t ∧
      ledgerHi (Phase5Transition L K s t).1 + ledgerHi (Phase5Transition L K s t).2 =
        ledgerHi s + ledgerHi t := by
  unfold Phase5Transition
  dsimp only
  refine clock_wrap_pair_ledger s t _ _ 5 (by omega) (by omega) hs ht ?_ ?_ ?_
  · split_ifs <;> first | exact hs | (show s.phase.val = 5; exact hs)
  · split_ifs <;> first | exact ht | (show t.phase.val = 5; exact ht)
  · split_ifs <;> rfl

/-- The Phase-6 split halves the Main's mass onto the (bias-free) Reserve. -/
private lemma doSplit_toRat_sum (r m : AgentState L K) (hr : r.bias = .zero) :
    Bias.toRat (doSplit L K r m).1.bias + Bias.toRat (doSplit L K r m).2.bias =
      Bias.toRat r.bias + Bias.toRat m.bias := by
  unfold doSplit
  rcases hm : m.bias with _ | ⟨sgn, j⟩
  · simp [hm]
  · dsimp only
    split_ifs
    · cases sgn
      · simp only [Bias.toRat, hr, Fin.val_mk]
        rw [half_add_half]
        ring
      · simp only [Bias.toRat, hr, Fin.val_mk, neg_div]
        have := half_add_half j.val
        linarith
    · simp [hm]
    · simp [hm]

private lemma doSplit_phase (r m : AgentState L K) :
    (doSplit L K r m).1.phase = r.phase ∧ (doSplit L K r m).2.phase = m.phase := by
  unfold doSplit
  rcases hm : m.bias with _ | ⟨sgn, j⟩
  · simp
  · dsimp only
    split_ifs <;> simp

/-- Phase 6: the Reserve-fuelled split. -/
private lemma phase6_dispatch_ledger (s t : AgentState L K)
    (hs : s.phase.val = 6) (ht : t.phase.val = 6)
    (hs_ok : NonMainBiasZero.agentOk s) (ht_ok : NonMainBiasZero.agentOk t) :
    ledgerLo (Phase6Transition L K s t).1 + ledgerLo (Phase6Transition L K s t).2 =
        ledgerLo s + ledgerLo t ∧
      ledgerHi (Phase6Transition L K s t).1 + ledgerHi (Phase6Transition L K s t).2 =
        ledgerHi s + ledgerHi t := by
  have hst := doSplit_phase s t
  have hts := doSplit_phase t s
  unfold Phase6Transition
  dsimp only
  refine clock_wrap_pair_ledger s t _ _ 6 (by omega) (by omega) hs ht ?_ ?_ ?_
  · split_ifs
    · rw [hst.1]; exact hs
    · rw [hts.2]; exact hs
    · exact hs
  · split_ifs
    · rw [hst.2]; exact ht
    · rw [hts.1]; exact ht
    · exact ht
  · split_ifs with h1 h2
    · have hr : s.bias = .zero := hs_ok (by rw [h1.1]; decide) (by omega) (by omega)
      exact doSplit_toRat_sum s t hr
    · have hr : t.bias = .zero := ht_ok (by rw [h2.1]; decide) (by omega) (by omega)
      have h := doSplit_toRat_sum t s hr
      linarith
    · rfl

/-- The Phase-7 cancel/split conserves the dyadic mass. -/
private lemma cancelSplit_toRat_sum (s t : AgentState L K) :
    Bias.toRat (cancelSplit L K s t).1.bias + Bias.toRat (cancelSplit L K s t).2.bias =
      Bias.toRat s.bias + Bias.toRat t.bias := by
  unfold cancelSplit
  rcases hs : s.bias with _ | ⟨sgs, i⟩ <;> rcases ht : t.bias with _ | ⟨sgt, j⟩
  · simp [hs, ht]
  · simp [hs, ht]
  · simp [hs, ht]
  · dsimp only
    by_cases hne : sgs ≠ sgt
    · rw [if_pos hne]
      split_ifs with h1 h2 h3 h4 h5
      · cases sgs <;> cases sgt <;> (first | exact absurd rfl hne | skip) <;>
          simp only [Bias.toRat, Fin.val_mk, neg_div] <;> rw [h1] <;> ring
      · cases sgs <;> cases sgt <;> (first | exact absurd rfl hne | skip) <;>
          simp only [Bias.toRat, Fin.val_mk, neg_div] <;> rw [← h2] <;> ring
      · cases sgs <;> cases sgt <;> (first | exact absurd rfl hne | skip) <;>
          simp only [Bias.toRat, Fin.val_mk, neg_div] <;> rw [← h3] <;> ring
      · cases sgs <;> cases sgt <;> (first | exact absurd rfl hne | skip) <;>
          simp only [Bias.toRat, Fin.val_mk, neg_div] <;> rw [← h4] <;> ring
      · cases sgs <;> cases sgt <;> (first | exact absurd rfl hne | skip) <;>
          simp only [Bias.toRat, Fin.val_mk, neg_div] <;> rw [← h5] <;> ring
      · simp [hs, ht]
    · rw [if_neg hne]
      simp [hs, ht]

private lemma cancelSplit_phase (s t : AgentState L K) :
    (cancelSplit L K s t).1.phase = s.phase ∧ (cancelSplit L K s t).2.phase = t.phase := by
  unfold cancelSplit
  rcases hs : s.bias with _ | ⟨sgs, i⟩ <;> rcases ht : t.bias with _ | ⟨sgt, j⟩
  · simp
  · simp
  · simp
  · dsimp only
    split_ifs <;> simp

/-- Phase 7: the extended cancel/split. -/
private lemma phase7_dispatch_ledger (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 7) :
    ledgerLo (Phase7Transition L K s t).1 + ledgerLo (Phase7Transition L K s t).2 =
        ledgerLo s + ledgerLo t ∧
      ledgerHi (Phase7Transition L K s t).1 + ledgerHi (Phase7Transition L K s t).2 =
        ledgerHi s + ledgerHi t := by
  have hcs := cancelSplit_phase s t
  unfold Phase7Transition
  dsimp only
  refine clock_wrap_pair_ledger s t _ _ 7 (by omega) (by omega) hs ht ?_ ?_ ?_
  · split_ifs
    · rw [hcs.1]; exact hs
    · exact hs
  · split_ifs
    · rw [hcs.2]; exact ht
    · exact ht
  · split_ifs
    · exact cancelSplit_toRat_sum s t
    · rfl

/-- The Phase-8 absorb reaction on two phase-8 agents: the lower ends can only drop and the upper
ends can only rise (the true mass `2^{-i} - 2^{-j}` of the absorber lies in its new window). -/
private lemma absorbConsume_ledger (s t : AgentState L K)
    (hs : s.phase.val = 8) (ht : t.phase.val = 8) :
    ledgerLo (absorbConsume L K s t).1 + ledgerLo (absorbConsume L K s t).2 ≤
        ledgerLo s + ledgerLo t ∧
      ledgerHi s + ledgerHi t ≤
        ledgerHi (absorbConsume L K s t).1 + ledgerHi (absorbConsume L K s t).2 := by
  have hs3 : 3 ≤ s.phase.val := by omega
  have ht3 : 3 ≤ t.phase.val := by omega
  unfold absorbConsume
  rcases hsb : s.bias with _ | ⟨ss, i⟩ <;> rcases htb : t.bias with _ | ⟨st, j⟩
  · dsimp only; exact ⟨le_refl _, le_refl _⟩
  · cases st <;> (dsimp only; exact ⟨le_refl _, le_refl _⟩)
  · cases ss <;> (dsimp only; exact ⟨le_refl _, le_refl _⟩)
  · cases ss <;> cases st
    · dsimp only; exact ⟨le_refl _, le_refl _⟩
    · -- s positive, t negative
      dsimp only
      split_ifs with h1 h2
      · -- s absorbs t
        dsimp only
        have hij : i.val + 1 ≤ j.val := h1.1
        have hsf : s.full = false := by
          cases h : s.full
          · rfl
          · exact absurd h h1.2
        have lo1 : ledgerLo ({ s with bias := .dyadic .pos i, full := true } : AgentState L K) =
            1 / 2 ^ (i.val + 1) :=
          ledgerLo_eq_of_full_pos _ (by show 8 ≤ s.phase.val; omega) rfl i rfl
        have hi1 : ledgerHi ({ s with bias := .dyadic .pos i, full := true } : AgentState L K) =
            1 / 2 ^ i.val :=
          ledgerHi_eq_of_full_pos _ (by show 8 ≤ s.phase.val; omega) rfl i rfl
        have lo2 : ledgerLo ({ t with bias := .zero } : AgentState L K) = 0 :=
          ledgerLo_eq_zero_of_bias_zero _ (by show 3 ≤ t.phase.val; omega) rfl
        have hi2 : ledgerHi ({ t with bias := .zero } : AgentState L K) = 0 :=
          ledgerHi_eq_zero_of_bias_zero _ (by show 3 ≤ t.phase.val; omega) rfl
        have los : ledgerLo s = 1 / 2 ^ i.val := by
          rw [ledgerLo_eq_of_not_full s hsf hs3, hsb]; rfl
        have his : ledgerHi s = 1 / 2 ^ i.val := ledgerHi_eq_of_pos s hs3 i hsb
        have lot : ledgerLo t = -(1 : ℚ) / 2 ^ j.val := ledgerLo_eq_of_neg t ht3 j htb
        have hit : ledgerHi t ≤ 0 :=
          ledgerHi_nonpos_of_not_pos t ht3 (by intro k hk; rw [htb] at hk; cases hk)
        have hle := one_div_two_pow_le_of_le hij
        have hsum := half_add_half i.val
        rw [lo1, hi1, lo2, hi2, los, his, lot]
        simp only [neg_div] at *
        constructor <;> linarith
      · -- t absorbs s
        dsimp only
        have hji : j.val + 1 ≤ i.val := h2.1
        have htf : t.full = false := by
          cases h : t.full
          · rfl
          · exact absurd h h2.2
        have lo1 : ledgerLo ({ s with bias := .zero } : AgentState L K) = 0 :=
          ledgerLo_eq_zero_of_bias_zero _ (by show 3 ≤ s.phase.val; omega) rfl
        have hi1 : ledgerHi ({ s with bias := .zero } : AgentState L K) = 0 :=
          ledgerHi_eq_zero_of_bias_zero _ (by show 3 ≤ s.phase.val; omega) rfl
        have lo2 : ledgerLo ({ t with bias := .dyadic .neg j, full := true } : AgentState L K) =
            -(1 : ℚ) / 2 ^ j.val :=
          ledgerLo_eq_of_full_neg _ (by show 8 ≤ t.phase.val; omega) rfl j rfl
        have hi2 : ledgerHi ({ t with bias := .dyadic .neg j, full := true } : AgentState L K) =
            -(1 : ℚ) / 2 ^ (j.val + 1) :=
          ledgerHi_eq_of_full_neg _ (by show 8 ≤ t.phase.val; omega) rfl j rfl
        have los : 0 ≤ ledgerLo s :=
          ledgerLo_nonneg_of_not_neg s hs3 (by intro k hk; rw [hsb] at hk; cases hk)
        have his : ledgerHi s = 1 / 2 ^ i.val := ledgerHi_eq_of_pos s hs3 i hsb
        have lot : ledgerLo t = -(1 : ℚ) / 2 ^ j.val := ledgerLo_eq_of_neg t ht3 j htb
        have hit : ledgerHi t = -(1 : ℚ) / 2 ^ j.val := by
          rw [ledgerHi_eq_of_not_full t htf ht3, htb]; rfl
        have hle := one_div_two_pow_le_of_le hji
        have hsum := half_add_half j.val
        rw [lo1, hi1, lo2, hi2, his, lot, hit]
        simp only [neg_div] at *
        constructor <;> linarith
      · dsimp only; exact ⟨le_refl _, le_refl _⟩
    · -- s negative, t positive
      dsimp only
      split_ifs with h1 h2
      · -- s absorbs t
        dsimp only
        have hij : i.val + 1 ≤ j.val := h1.1
        have hsf : s.full = false := by
          cases h : s.full
          · rfl
          · exact absurd h h1.2
        have lo1 : ledgerLo ({ s with bias := .dyadic .neg i, full := true } : AgentState L K) =
            -(1 : ℚ) / 2 ^ i.val :=
          ledgerLo_eq_of_full_neg _ (by show 8 ≤ s.phase.val; omega) rfl i rfl
        have hi1 : ledgerHi ({ s with bias := .dyadic .neg i, full := true } : AgentState L K) =
            -(1 : ℚ) / 2 ^ (i.val + 1) :=
          ledgerHi_eq_of_full_neg _ (by show 8 ≤ s.phase.val; omega) rfl i rfl
        have lo2 : ledgerLo ({ t with bias := .zero } : AgentState L K) = 0 :=
          ledgerLo_eq_zero_of_bias_zero _ (by show 3 ≤ t.phase.val; omega) rfl
        have hi2 : ledgerHi ({ t with bias := .zero } : AgentState L K) = 0 :=
          ledgerHi_eq_zero_of_bias_zero _ (by show 3 ≤ t.phase.val; omega) rfl
        have los : ledgerLo s = -(1 : ℚ) / 2 ^ i.val := ledgerLo_eq_of_neg s hs3 i hsb
        have his : ledgerHi s = -(1 : ℚ) / 2 ^ i.val := by
          rw [ledgerHi_eq_of_not_full s hsf hs3, hsb]; rfl
        have lot : 0 ≤ ledgerLo t :=
          ledgerLo_nonneg_of_not_neg t ht3 (by intro k hk; rw [htb] at hk; cases hk)
        have hit : ledgerHi t = 1 / 2 ^ j.val := ledgerHi_eq_of_pos t ht3 j htb
        have hle := one_div_two_pow_le_of_le hij
        have hsum := half_add_half i.val
        rw [lo1, hi1, lo2, hi2, los, his, hit]
        simp only [neg_div] at *
        constructor <;> linarith
      · -- t absorbs s
        dsimp only
        have hji : j.val + 1 ≤ i.val := h2.1
        have htf : t.full = false := by
          cases h : t.full
          · rfl
          · exact absurd h h2.2
        have lo1 : ledgerLo ({ s with bias := .zero } : AgentState L K) = 0 :=
          ledgerLo_eq_zero_of_bias_zero _ (by show 3 ≤ s.phase.val; omega) rfl
        have hi1 : ledgerHi ({ s with bias := .zero } : AgentState L K) = 0 :=
          ledgerHi_eq_zero_of_bias_zero _ (by show 3 ≤ s.phase.val; omega) rfl
        have lo2 : ledgerLo ({ t with bias := .dyadic .pos j, full := true } : AgentState L K) =
            1 / 2 ^ (j.val + 1) :=
          ledgerLo_eq_of_full_pos _ (by show 8 ≤ t.phase.val; omega) rfl j rfl
        have hi2 : ledgerHi ({ t with bias := .dyadic .pos j, full := true } : AgentState L K) =
            1 / 2 ^ j.val :=
          ledgerHi_eq_of_full_pos _ (by show 8 ≤ t.phase.val; omega) rfl j rfl
        have los : ledgerLo s = -(1 : ℚ) / 2 ^ i.val := ledgerLo_eq_of_neg s hs3 i hsb
        have his : ledgerHi s ≤ 0 :=
          ledgerHi_nonpos_of_not_pos s hs3 (by intro k hk; rw [hsb] at hk; cases hk)
        have lot : ledgerLo t = 1 / 2 ^ j.val := by
          rw [ledgerLo_eq_of_not_full t htf ht3, htb]; rfl
        have hit : ledgerHi t = 1 / 2 ^ j.val := ledgerHi_eq_of_pos t ht3 j htb
        have hle := one_div_two_pow_le_of_le hji
        have hsum := half_add_half j.val
        rw [lo1, hi1, lo2, hi2, los, lot, hit]
        simp only [neg_div] at *
        constructor <;> linarith
      · dsimp only; exact ⟨le_refl _, le_refl _⟩
    · dsimp only; exact ⟨le_refl _, le_refl _⟩

private lemma absorbConsume_phase (s t : AgentState L K) :
    (absorbConsume L K s t).1.phase = s.phase ∧ (absorbConsume L K s t).2.phase = t.phase := by
  unfold absorbConsume
  rcases hsb : s.bias with _ | ⟨ss, i⟩ <;> rcases htb : t.bias with _ | ⟨st, j⟩
  · simp
  · cases st <;> simp
  · cases ss <;> simp
  · cases ss <;> cases st <;> dsimp only <;> (try split_ifs) <;> simp

/-- Phase 8: the absorb reaction and the clock step. -/
private lemma phase8_dispatch_ledger (s t : AgentState L K)
    (hs : s.phase.val = 8) (ht : t.phase.val = 8) :
    ledgerLo (Phase8Transition L K s t).1 + ledgerLo (Phase8Transition L K s t).2 ≤
        ledgerLo s + ledgerLo t ∧
      ledgerHi s + ledgerHi t ≤
        ledgerHi (Phase8Transition L K s t).1 + ledgerHi (Phase8Transition L K s t).2 := by
  unfold Phase8Transition
  dsimp only
  by_cases h1 : s.role = .main ∧ t.role = .main
  · rw [if_pos h1, if_pos h1]
    have hp := absorbConsume_phase s t
    obtain ⟨hs1lo, hs1hi⟩ := clock_wrap_ledger_of_eight (absorbConsume L K s t).1
      (by rw [hp.1]; exact hs)
    obtain ⟨ht1lo, ht1hi⟩ := clock_wrap_ledger_of_eight (absorbConsume L K s t).2
      (by rw [hp.2]; exact ht)
    rw [hs1lo, hs1hi, ht1lo, ht1hi]
    exact absorbConsume_ledger s t hs ht
  · rw [if_neg h1, if_neg h1]
    obtain ⟨hs1lo, hs1hi⟩ := clock_wrap_ledger_of_eight s hs
    obtain ⟨ht1lo, ht1hi⟩ := clock_wrap_ledger_of_eight t ht
    rw [hs1lo, hs1hi, ht1lo, ht1hi]
    exact ⟨le_refl _, le_refl _⟩

/-- Phase 9: the opinion epidemic never touches `bias`, `full` or (below Phase 10) `phase`. -/
private lemma phase9_dispatch_ledger (s t : AgentState L K)
    (hs : s.phase.val = 9) (ht : t.phase.val = 9)
    (hout : (Phase9Transition L K s t).1.phase.val ≠ 10) :
    ledgerLo (Phase9Transition L K s t).1 + ledgerLo (Phase9Transition L K s t).2 =
        ledgerLo s + ledgerLo t ∧
      ledgerHi (Phase9Transition L K s t).1 + ledgerHi (Phase9Transition L K s t).2 =
        ledgerHi s + ledgerHi t := by
  unfold Phase9Transition Phase2Transition at hout ⊢
  dsimp only at hout ⊢
  split_ifs at hout ⊢ with h1
  · exfalso
    apply hout
    exact advancePhaseWithInit_phase_of_nine _ (by show s.phase.val = 9; exact hs)
  all_goals
    first
    | (rw [(ledger_update_opinions_output s (by omega) _ _).1,
          (ledger_update_opinions_output t (by omega) _ _).1,
          (ledger_update_opinions_output s (by omega) _ _).2,
          (ledger_update_opinions_output t (by omega) _ _).2]
       exact ⟨rfl, rfl⟩)
    | (rw [(ledger_update_opinions s (by omega) _).1, (ledger_update_opinions t (by omega) _).1,
          (ledger_update_opinions s (by omega) _).2, (ledger_update_opinions t (by omega) _).2]
       exact ⟨rfl, rfl⟩)

/-! ## The pair lemma -/

/-- **Ledger pair lemma.** For an interaction whose epidemic phase is `≥ 2` and whose outputs stay
below Phase 10, the lower ends of the pair can only drop and the upper ends can only rise. -/
theorem Transition_ledger_pair_of_epidemic_ge_two (s t : AgentState L K)
    (hs_mcr : s.role ≠ .mcr) (ht_mcr : t.role ≠ .mcr)
    (hs_carrier : s.role ≠ .main → s.smallBias.val = 3)
    (ht_carrier : t.role ≠ .main → t.smallBias.val = 3)
    (hs_noerr : 2 ≤ s.phase.val → s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (ht_noerr : 2 ≤ t.phase.val → t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hs_ok : NonMainBiasZero.agentOk s) (ht_ok : NonMainBiasZero.agentOk t)
    (hep : 2 ≤ (phaseEpidemicUpdate L K s t).1.phase.val)
    (hout1 : (Transition L K s t).1.phase.val ≠ 10)
    (hout2 : (Transition L K s t).2.phase.val ≠ 10) :
    ledgerLo (Transition L K s t).1 + ledgerLo (Transition L K s t).2 ≤
        ledgerLo s + ledgerLo t ∧
      ledgerHi s + ledgerHi t ≤
        ledgerHi (Transition L K s t).1 + ledgerHi (Transition L K s t).2 := by
  have hmono := phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s t
  have hep1_ne : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10 := by
    intro h
    have h10 := (Transition L K s t).1.phase.2
    omega
  have hep2_ne : (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10 := by
    intro h
    have h10 := (Transition L K s t).2.phase.2
    omega
  have hep_eq : (phaseEpidemicUpdate L K s t).1.phase.val =
      (phaseEpidemicUpdate L K s t).2.phase.val := by
    rw [ledger_epidemic_phase_eq_max s t hep1_ne, ledger_epidemic_phase_eq_max_snd s t hep2_ne]
  have hled_s := ledger_epidemic_left s t hs_mcr hs_carrier hs_noerr hep1_ne
  have hled_t := ledger_epidemic_right s t ht_mcr ht_carrier ht_noerr hep2_ne
  have hwf_s := ledger_epidemic_wf_left s t hs_mcr hs_carrier hs_noerr hep1_ne
  have hwf_t := ledger_epidemic_wf_right s t ht_mcr ht_carrier ht_noerr hep2_ne
  have hok := NonMainBiasZero.phaseEpidemicUpdate_agentOk (L := L) (K := K) s t hs_ok ht_ok
  unfold Transition at hout1 hout2 ⊢
  generalize he : phaseEpidemicUpdate L K s t = ep
  rcases ep with ⟨s', t'⟩
  rw [he] at hout1 hout2 hep hep1_ne hep2_ne hep_eq hled_s hled_t hwf_s hwf_t hok hmono
  simp only at hout1 hout2 hep hep1_ne hep2_ne hep_eq hled_s hled_t hwf_s hwf_t hok hmono ⊢
  let out :=
    match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')
  change (finishPhase10Entry L K s' out.1).phase.val ≠ 10 at hout1
  change (finishPhase10Entry L K t' out.2).phase.val ≠ 10 at hout2
  change ledgerLo (finishPhase10Entry L K s' out.1) + ledgerLo (finishPhase10Entry L K t' out.2) ≤
      ledgerLo s + ledgerLo t ∧
    ledgerHi s + ledgerHi t ≤
      ledgerHi (finishPhase10Entry L K s' out.1) + ledgerHi (finishPhase10Entry L K t' out.2)
  have hout1_out : out.1.phase.val ≠ 10 := by simpa using hout1
  have hout2_out : out.2.phase.val ≠ 10 := by simpa using hout2
  rw [finishPhase10Entry_eq_self_of_after_ne_10 L K s' out.1 hout1_out,
    finishPhase10Entry_eq_self_of_after_ne_10 L K t' out.2 hout2_out]
  rw [← hled_s.1, ← hled_s.2, ← hled_t.1, ← hled_t.2]
  have hdispatch :
      ledgerLo out.1 + ledgerLo out.2 ≤ ledgerLo s' + ledgerLo t' ∧
        ledgerHi s' + ledgerHi t' ≤ ledgerHi out.1 + ledgerHi out.2 := by
    dsimp only [out]
    rcases hsp : s'.phase with ⟨n, hn⟩
    have hs_phase : s'.phase.val = n := by rw [hsp]
    have ht_phase : t'.phase.val = n := by rw [← hep_eq, hsp]
    match n, hn with
    | 0, _ => omega
    | 1, _ => omega
    | 2, _ =>
        have h := phase2_dispatch_ledger s' t' hs_phase ht_phase hwf_s.1 hwf_t.1 hwf_s.2.1
          hwf_t.2.1 (hwf_s.2.2 (by omega)) (hwf_t.2.2 (by omega))
        exact ⟨le_of_eq h.1, le_of_eq h.2.symm⟩
    | 3, _ =>
        have h := phase3_dispatch_ledger s' t' hs_phase ht_phase
        exact ⟨le_of_eq h.1, le_of_eq h.2.symm⟩
    | 4, _ =>
        have h := phase4_dispatch_ledger s' t' hs_phase ht_phase
        exact ⟨le_of_eq h.1, le_of_eq h.2.symm⟩
    | 5, _ =>
        have h := phase5_dispatch_ledger s' t' hs_phase ht_phase
        exact ⟨le_of_eq h.1, le_of_eq h.2.symm⟩
    | 6, _ =>
        have h := phase6_dispatch_ledger s' t' hs_phase ht_phase hok.1 hok.2
        exact ⟨le_of_eq h.1, le_of_eq h.2.symm⟩
    | 7, _ =>
        have h := phase7_dispatch_ledger s' t' hs_phase ht_phase
        exact ⟨le_of_eq h.1, le_of_eq h.2.symm⟩
    | 8, _ =>
        exact phase8_dispatch_ledger s' t' hs_phase ht_phase
    | 9, _ =>
        have hout9 : (Phase9Transition L K s' t').1.phase.val ≠ 10 := by
          simpa [hsp, out] using hout1_out
        have h := phase9_dispatch_ledger s' t' hs_phase ht_phase hout9
        exact ⟨le_of_eq h.1, le_of_eq h.2.symm⟩
    | 10, _ => omega
    | n + 11, hn => omega
  exact hdispatch

/-! ## The reachable ledger bounds -/

/-- Phases never decrease, so a configuration below Phase 10 comes from one below Phase 10. -/
lemma StepRel_phase_lt_ten_of_next
    (c c' : Config (AgentState L K))
    (hstep : (NonuniformMajority L K).StepRel c c')
    (hphase' : ∀ a ∈ c', a.phase.val < 10) :
    ∀ a ∈ c, a.phase.val < 10 := by
  rcases hstep with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hmono := Transition_phase_monotone (L := L) (K := K) r₁ r₂
  simp only at hmono
  have hp₁_mem : (Transition L K r₁ r₂).1 ∈ c' := by
    rw [hc']
    exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_self _ _))
  have hp₂_mem : (Transition L K r₁ r₂).2 ∈ c' := by
    rw [hc']
    exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_of_mem (by simp)))
  have hr₁_phase : r₁.phase.val < 10 := lt_of_le_of_lt hmono.1 (hphase' _ hp₁_mem)
  have hr₂_phase : r₂.phase.val < 10 := lt_of_le_of_lt hmono.2 (hphase' _ hp₂_mem)
  intro a ha
  by_cases ha₁ : a = r₁
  · simpa [ha₁] using hr₁_phase
  by_cases ha₂ : a = r₂
  · simpa [ha₂] using hr₂_phase
  have ha_residual : a ∈ c - r₁ ::ₘ {r₂} := by
    have h₁ : a ∈ c.erase r₁ := (Multiset.mem_erase_of_ne ha₁).2 ha
    have h₂ : a ∈ (c.erase r₁).erase r₂ := (Multiset.mem_erase_of_ne ha₂).2 h₁
    simpa using h₂
  have ha_c' : a ∈ c' := by
    rw [hc']
    simp only [Multiset.mem_add]
    exact Or.inl ha_residual
  exact hphase' a ha_c'

/-- An MCR agent at phase 0 whose partner is at a higher phase is sent to Phase 10 by the
epidemic, so its interaction output is in Phase 10. -/
private lemma Transition_left_phase_ten_of_mcr_zero (r other : AgentState L K)
    (hr_phase : r.phase.val = 0) (hother : 1 ≤ other.phase.val) (hr_mcr : r.role = .mcr) :
    (Transition L K r other).1.phase.val = 10 := by
  have hot_le : other.phase.val ≤ 10 := by have := other.phase.2; omega
  have hep : (phaseEpidemicUpdate L K r other).1.phase.val = 10 := by
    unfold phaseEpidemicUpdate
    set p := max r.phase other.phase with hp_def
    have hp_val : p.val = other.phase.val := by
      simp [p, Fin.le_iff_val_le_val, hr_phase]
    have hp_eq : p = ⟨other.phase.val, by have := other.phase.2; omega⟩ := by
      apply Fin.ext; exact hp_val
    have hs'_phase :
        (runInitsBetween L K r.phase.val p.val
          ({ r with phase := p } : AgentState L K)).phase.val = 10 := by
      rw [hr_phase, hp_eq]
      exact ledger_runInitsBetween_mcr_zero_target_phase_ten r other.phase.val hr_mcr hother hot_le
    have hguard :
        (r.phase.val < 10 ∨ other.phase.val < 10) ∧
        ((runInitsBetween L K r.phase.val p.val
            ({ r with phase := p } : AgentState L K)).phase.val = 10 ∨
         (runInitsBetween L K other.phase.val p.val
            ({ other with phase := p } : AgentState L K)).phase.val = 10) :=
      ⟨Or.inl (by omega), Or.inl hs'_phase⟩
    rw [if_pos hguard]
    simp [phase10EpidemicEntry, hr_phase, enterPhase10, phase10]
  have hmono := (phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) r other).1
  have h10 := (Transition L K r other).1.phase.2
  omega

private lemma Transition_right_phase_ten_of_mcr_zero (other r : AgentState L K)
    (hr_phase : r.phase.val = 0) (hother : 1 ≤ other.phase.val) (hr_mcr : r.role = .mcr) :
    (Transition L K other r).2.phase.val = 10 := by
  have hot_le : other.phase.val ≤ 10 := by have := other.phase.2; omega
  have hep : (phaseEpidemicUpdate L K other r).2.phase.val = 10 := by
    unfold phaseEpidemicUpdate
    set p := max other.phase r.phase with hp_def
    have hp_val : p.val = other.phase.val := by
      simp [p, Fin.le_iff_val_le_val, hr_phase]
    have hp_eq : p = ⟨other.phase.val, by have := other.phase.2; omega⟩ := by
      apply Fin.ext; exact hp_val
    have ht'_phase :
        (runInitsBetween L K r.phase.val p.val
          ({ r with phase := p } : AgentState L K)).phase.val = 10 := by
      rw [hr_phase, hp_eq]
      exact ledger_runInitsBetween_mcr_zero_target_phase_ten r other.phase.val hr_mcr hother hot_le
    have hguard :
        (other.phase.val < 10 ∨ r.phase.val < 10) ∧
        ((runInitsBetween L K other.phase.val p.val
            ({ other with phase := p } : AgentState L K)).phase.val = 10 ∨
         (runInitsBetween L K r.phase.val p.val
            ({ r with phase := p } : AgentState L K)).phase.val = 10) :=
      ⟨Or.inr (by omega), Or.inr ht'_phase⟩
    rw [if_pos hguard]
    simp [phase10EpidemicEntry, hr_phase, enterPhase10, phase10]
  have hmono := (phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) other r).2
  have h10 := (Transition L K other r).2.phase.2
  omega

/-- Small-bias range below Phase 10: every agent at a phase in `[2, 9]` of a reachable
configuration carries a small bias in `{2, 3, 4}` (the Phase-2 Init filters the others out to
Phase 10, and the field is frozen from phase 2 on). -/
theorem reachable_smallBias_noerror_of_phase_lt_ten
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase : ∀ a ∈ c, a.phase.val < 10) :
    ∀ a ∈ c, 2 ≤ a.phase.val → a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  induction hreach with
  | refl =>
      intro a ha hge2
      have hphase0 := (hinit a ha).1
      have hval0 : a.phase.val = 0 := congrArg Fin.val hphase0
      omega
  | tail hprev hstep ih =>
      rename_i b c_next
      have hphase_prev := StepRel_phase_lt_ten_of_next (L := L) (K := K) _ _ hstep hphase
      have ih_prev := ih hphase_prev
      rcases hstep with ⟨r₁, r₂, happ, hc'⟩
      dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
      have hr₁_mem : r₁ ∈ b := Multiset.mem_of_le happ (by simp)
      have hr₂_mem : r₂ ∈ b := Multiset.mem_of_le happ (by simp)
      have hout1 : (Transition L K r₁ r₂).1.phase.val ≠ 10 := by
        have := hphase (Transition L K r₁ r₂).1 (by
          rw [hc']; exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_self _ _)))
        omega
      have hout2 : (Transition L K r₁ r₂).2.phase.val ≠ 10 := by
        have := hphase (Transition L K r₁ r₂).2 (by
          rw [hc']; exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_of_mem (by simp))))
        omega
      have hmono := phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) r₁ r₂
      have hep1_ne : (phaseEpidemicUpdate L K r₁ r₂).1.phase.val ≠ 10 := by
        intro h
        have h10 := (Transition L K r₁ r₂).1.phase.2
        omega
      have hep2_ne : (phaseEpidemicUpdate L K r₁ r₂).2.phase.val ≠ 10 := by
        intro h
        have h10 := (Transition L K r₁ r₂).2.phase.2
        omega
      have hep_eq : (phaseEpidemicUpdate L K r₁ r₂).1.phase.val =
          (phaseEpidemicUpdate L K r₁ r₂).2.phase.val := by
        rw [ledger_epidemic_phase_eq_max r₁ r₂ hep1_ne,
          ledger_epidemic_phase_eq_max_snd r₁ r₂ hep2_ne]
      rw [hc']
      intro a ha hge2
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
      rcases ha with h_old | h_new
      · exact ih_prev a (Multiset.mem_of_le (Multiset.sub_le_self _ {r₁, r₂}) h_old) hge2
      · rcases h_new with h_eq | h_eq
        · subst a
          by_cases hr₁_ge2 : 2 ≤ r₁.phase.val
          · rw [Transition_left_preserves_smallBias_of_phase_ge_two (L := L) (K := K) r₁ r₂ hr₁_ge2]
            exact ih_prev r₁ hr₁_mem hr₁_ge2
          · push_neg at hr₁_ge2
            by_cases hep_ge2 : 2 ≤ (phaseEpidemicUpdate L K r₁ r₂).1.phase.val
            · have hnoerr := phaseEpidemicUpdate_left_smallBias_noerror_of_entered_not_ten
                (L := L) (K := K) r₁ r₂ hr₁_ge2 hep_ge2 hep1_ne
              have hpres := Transition_preserves_epidemic_smallBias_left_of_phase_ge_two
                (L := L) (K := K) r₁ r₂
              simp only at hpres
              rw [hpres hep_ge2]
              exact hnoerr
            · push_neg at hep_ge2
              have hout1_le2 := Transition_left_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
                (L := L) (K := K) r₁ r₂ hep_ge2 hout1
              exact Transition_left_phase2_smallBias_noerror_of_input_lt_two
                (L := L) (K := K) r₁ r₂ hr₁_ge2 (by omega)
        · subst a
          by_cases hr₂_ge2 : 2 ≤ r₂.phase.val
          · rw [Transition_right_preserves_smallBias_of_phase_ge_two (L := L) (K := K) r₁ r₂ hr₂_ge2]
            exact ih_prev r₂ hr₂_mem hr₂_ge2
          · push_neg at hr₂_ge2
            by_cases hep_ge2 : 2 ≤ (phaseEpidemicUpdate L K r₁ r₂).1.phase.val
            · have hnoerr := phaseEpidemicUpdate_right_smallBias_noerror_of_entered_not_ten
                (L := L) (K := K) r₁ r₂ hr₂_ge2 (by omega) hep2_ne
              have hpres := Transition_preserves_epidemic_smallBias_right_of_dispatch_phase_ge_two
                (L := L) (K := K) r₁ r₂
              simp only at hpres
              rw [hpres hep_ge2]
              exact hnoerr
            · push_neg at hep_ge2
              have hout2_le2 := Transition_right_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
                (L := L) (K := K) r₁ r₂ hep_ge2 hout2
              exact Transition_right_phase2_smallBias_noerror_of_input_lt_two
                (L := L) (K := K) r₁ r₂ hr₂_ge2 (by omega)

/-- **Reachable ledger bounds.** From a valid initial configuration, as long as no agent has
reached the Phase-10 backup, the initial gap lies between the two ledger sums. -/
theorem reachable_ledger_bounds
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase : ∀ a ∈ c, a.phase.val < 10) :
    loSum c ≤ (initialGap init : ℚ) ∧ (initialGap init : ℚ) ≤ hiSum c := by
  induction hreach with
  | refl =>
      have h0 : ∀ a ∈ init, a.phase.val < 8 := by
        intro a ha
        have := (hinit a ha).1
        have hv : a.phase.val = 0 := congrArg Fin.val this
        omega
      rw [loSum_eq_prePhase4MassSum_of_phase_lt_eight init h0,
        hiSum_eq_prePhase4MassSum_of_phase_lt_eight init h0,
        prePhase4MassSum_validInitial_eq_initialGap (L := L) (K := K) init hinit]
      exact ⟨le_refl _, le_refl _⟩
  | tail hprev hstep ih =>
      rename_i b c_next
      have hphase_prev := StepRel_phase_lt_ten_of_next (L := L) (K := K) _ _ hstep hphase
      have hprev_sum := ih hphase_prev
      rcases hstep with ⟨r₁, r₂, happ, hc'⟩
      dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
      have hr₁_mem : r₁ ∈ b := Multiset.mem_of_le happ (by simp)
      have hr₂_mem : r₂ ∈ b := Multiset.mem_of_le happ (by simp)
      have hout1 : (Transition L K r₁ r₂).1.phase.val ≠ 10 := by
        have := hphase (Transition L K r₁ r₂).1 (by
          rw [hc']; exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_self _ _)))
        omega
      have hout2 : (Transition L K r₁ r₂).2.phase.val ≠ 10 := by
        have := hphase (Transition L K r₁ r₂).2 (by
          rw [hc']; exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_of_mem (by simp))))
        omega
      -- reachability invariants for the pair
      have hwf := reachable_preserves_well_formed_agents (L := L) (K := K) init _ hinit hprev
      have hcarrier_inv := reachable_nonMainCarrierSmallBiasZeroAgent
        (L := L) (K := K) init _ hinit hprev
      have hok_inv := NonMainBiasZero.reachable_nonMainBiasZero (L := L) (K := K) init _ hinit hprev
      have hquota := reachable_preserves_well_formed_agent_quota (L := L) (K := K) init _ hinit hprev
      have hnoerr_inv : ∀ a ∈ b, 2 ≤ a.phase.val → a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) :=
        reachable_smallBias_noerror_of_phase_lt_ten (L := L) (K := K) init b hinit hprev hphase_prev
      have hpair :
          ledgerLo (Transition L K r₁ r₂).1 + ledgerLo (Transition L K r₁ r₂).2 ≤
              ledgerLo r₁ + ledgerLo r₂ ∧
            ledgerHi r₁ + ledgerHi r₂ ≤
              ledgerHi (Transition L K r₁ r₂).1 + ledgerHi (Transition L K r₁ r₂).2 := by
        by_cases hep_lt2 : (phaseEpidemicUpdate L K r₁ r₂).1.phase.val < 2
        · -- all four phases are below 3: the ledger is the small bias, conserved by the quota law
          have hout1_le2 := Transition_left_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
            (L := L) (K := K) r₁ r₂ hep_lt2 hout1
          have hout2_le2 := Transition_right_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
            (L := L) (K := K) r₁ r₂ hep_lt2 hout2
          have hmax_le : max r₁.phase.val r₂.phase.val ≤ 1 := by
            have hge := phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := K) r₁ r₂
            omega
          have hr1_lt3 : r₁.phase.val < 3 := by
            have := le_max_left r₁.phase.val r₂.phase.val; omega
          have hr2_lt3 : r₂.phase.val < 3 := by
            have := le_max_right r₁.phase.val r₂.phase.val; omega
          have hpair_int := smallBiasSum_step_invariant_of_quota
            (L := L) (K := K) r₁ r₂ (hquota r₁ hr₁_mem) (hquota r₂ hr₂_mem)
          have hcast : (AgentState.smallBiasInt r₁ : ℚ) + (AgentState.smallBiasInt r₂ : ℚ) =
              (AgentState.smallBiasInt (Transition L K r₁ r₂).1 : ℚ) +
                (AgentState.smallBiasInt (Transition L K r₁ r₂).2 : ℚ) := by
            exact_mod_cast hpair_int
          rw [ledgerLo_of_phase_lt_eight (Transition L K r₁ r₂).1 (by omega),
            ledgerLo_of_phase_lt_eight (Transition L K r₁ r₂).2 (by omega),
            ledgerLo_of_phase_lt_eight r₁ (by omega), ledgerLo_of_phase_lt_eight r₂ (by omega),
            ledgerHi_of_phase_lt_eight (Transition L K r₁ r₂).1 (by omega),
            ledgerHi_of_phase_lt_eight (Transition L K r₁ r₂).2 (by omega),
            ledgerHi_of_phase_lt_eight r₁ (by omega), ledgerHi_of_phase_lt_eight r₂ (by omega),
            prePhase4Mass_of_phase_lt_three (Transition L K r₁ r₂).1 (by omega),
            prePhase4Mass_of_phase_lt_three (Transition L K r₁ r₂).2 (by omega),
            prePhase4Mass_of_phase_lt_three r₁ hr1_lt3, prePhase4Mass_of_phase_lt_three r₂ hr2_lt3]
          exact ⟨le_of_eq hcast.symm, le_of_eq hcast⟩
        · push_neg at hep_lt2
          -- the epidemic phase is the larger input phase
          have hep1_ne : (phaseEpidemicUpdate L K r₁ r₂).1.phase.val ≠ 10 := by
            intro h
            have hmono := (phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) r₁ r₂).1
            have h10 := (Transition L K r₁ r₂).1.phase.2
            omega
          have hep_max := ledger_epidemic_phase_eq_max r₁ r₂ hep1_ne
          -- no MCR agent takes part: an MCR sits at phase 0 and would be sent to Phase 10
          have hr1_mcr : r₁.role ≠ .mcr := by
            intro h_mcr
            have hr1_phase0 : r₁.phase.val = 0 := by
              rcases (hwf r₁ hr₁_mem).1 (Or.inl h_mcr) with h0 | h10
              · exact h0
              · have := hphase_prev r₁ hr₁_mem; omega
            have hr2_ge1 : 1 ≤ r₂.phase.val := by
              rw [hep_max] at hep_lt2
              rcases le_total r₁.phase.val r₂.phase.val with h | h
              · rw [max_eq_right h] at hep_lt2; omega
              · rw [max_eq_left h] at hep_lt2; omega
            exact absurd (Transition_left_phase_ten_of_mcr_zero r₁ r₂ hr1_phase0 hr2_ge1 h_mcr) hout1
          have hr2_mcr : r₂.role ≠ .mcr := by
            intro h_mcr
            have hr2_phase0 : r₂.phase.val = 0 := by
              rcases (hwf r₂ hr₂_mem).1 (Or.inl h_mcr) with h0 | h10
              · exact h0
              · have := hphase_prev r₂ hr₂_mem; omega
            have hr1_ge1 : 1 ≤ r₁.phase.val := by
              rw [hep_max] at hep_lt2
              rcases le_total r₁.phase.val r₂.phase.val with h | h
              · rw [max_eq_right h] at hep_lt2; omega
              · rw [max_eq_left h] at hep_lt2; omega
            exact absurd (Transition_right_phase_ten_of_mcr_zero r₁ r₂ hr2_phase0 hr1_ge1 h_mcr) hout2
          have hr1_carrier : r₁.role ≠ .main → r₁.smallBias.val = 3 := by
            intro hnot_main
            have hcr_set : r₁.role = .cr ∨ r₁.role = .reserve ∨ r₁.role = .clock := by
              cases hrole : r₁.role with
              | main => exact absurd hrole hnot_main
              | reserve => right; left; rfl
              | clock => right; right; rfl
              | mcr => exact absurd hrole hr1_mcr
              | cr => left; rfl
            exact hcarrier_inv r₁ hr₁_mem hcr_set
          have hr2_carrier : r₂.role ≠ .main → r₂.smallBias.val = 3 := by
            intro hnot_main
            have hcr_set : r₂.role = .cr ∨ r₂.role = .reserve ∨ r₂.role = .clock := by
              cases hrole : r₂.role with
              | main => exact absurd hrole hnot_main
              | reserve => right; left; rfl
              | clock => right; right; rfl
              | mcr => exact absurd hrole hr2_mcr
              | cr => left; rfl
            exact hcarrier_inv r₂ hr₂_mem hcr_set
          exact Transition_ledger_pair_of_epidemic_ge_two r₁ r₂ hr1_mcr hr2_mcr
            hr1_carrier hr2_carrier (hnoerr_inv r₁ hr₁_mem) (hnoerr_inv r₂ hr₂_mem)
            (hok_inv r₁ hr₁_mem) (hok_inv r₂ hr₂_mem) hep_lt2 hout1 hout2
      -- multiset decomposition of the two sums
      rw [hc']
      have hrestore : b - r₁ ::ₘ {r₂} + r₁ ::ₘ {r₂} = b := Multiset.sub_add_cancel happ
      have hlo_prev : loSum b = loSum (b - r₁ ::ₘ {r₂}) + (ledgerLo r₁ + ledgerLo r₂) := by
        rw [← hrestore]
        simp [loSum, add_left_comm]
      have hhi_prev : hiSum b = hiSum (b - r₁ ::ₘ {r₂}) + (ledgerHi r₁ + ledgerHi r₂) := by
        rw [← hrestore]
        simp [hiSum, add_left_comm]
      have hlo_curr :
          loSum (b - r₁ ::ₘ {r₂} + (Transition L K r₁ r₂).1 ::ₘ {(Transition L K r₁ r₂).2}) =
            loSum (b - r₁ ::ₘ {r₂}) +
              (ledgerLo (Transition L K r₁ r₂).1 + ledgerLo (Transition L K r₁ r₂).2) := by
        simp [loSum, add_left_comm]
      have hhi_curr :
          hiSum (b - r₁ ::ₘ {r₂} + (Transition L K r₁ r₂).1 ::ₘ {(Transition L K r₁ r₂).2}) =
            hiSum (b - r₁ ::ₘ {r₂}) +
              (ledgerHi (Transition L K r₁ r₂).1 + ledgerHi (Transition L K r₁ r₂).2) := by
        simp [hiSum, add_left_comm]
      rw [hlo_curr, hhi_curr]
      rw [hlo_prev, hhi_prev] at hprev_sum
      constructor
      · linarith [hprev_sum.1, hpair.1]
      · linarith [hprev_sum.2, hpair.2]

/-! ## Consequences at an all-phase-9 configuration -/

/-- A positive initial gap forces a positive dyadic bias somewhere in a phase-9 configuration. -/
theorem exists_pos_bias_of_initialGap_pos
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase : ∀ a ∈ c, a.phase.val = 9)
    (hgap : 0 < initialGap init) :
    ∃ a ∈ c, ∃ i, a.bias = .dyadic .pos i := by
  have hb := (reachable_ledger_bounds init c hinit hreach
    (fun a ha => by have := hphase a ha; omega)).2
  have hpos : 0 < hiSum c := lt_of_lt_of_le (by exact_mod_cast hgap) hb
  by_contra hnone
  push_neg at hnone
  have hle : hiSum c ≤ 0 :=
    sum_map_nonpos_of_forall c (fun a ha =>
      ledgerHi_nonpos_of_not_pos a (by have := hphase a ha; omega) (hnone a ha))
  linarith

/-- A negative initial gap forces a negative dyadic bias somewhere in a phase-9 configuration. -/
theorem exists_neg_bias_of_initialGap_neg
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase : ∀ a ∈ c, a.phase.val = 9)
    (hgap : initialGap init < 0) :
    ∃ a ∈ c, ∃ i, a.bias = .dyadic .neg i := by
  have hb := (reachable_ledger_bounds init c hinit hreach
    (fun a ha => by have := hphase a ha; omega)).1
  have hneg : loSum c < 0 := lt_of_le_of_lt hb (by exact_mod_cast hgap)
  by_contra hnone
  push_neg at hnone
  have hge : 0 ≤ loSum c :=
    sum_map_nonneg_of_forall c (fun a ha =>
      ledgerLo_nonneg_of_not_neg a (by have := hphase a ha; omega) (hnone a ha))
  linarith

/-- A zero initial gap and no negative bias force every bias of a phase-9 configuration to zero. -/
theorem bias_zero_of_initialGap_zero_of_no_neg
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase : ∀ a ∈ c, a.phase.val = 9)
    (hgap : initialGap init = 0)
    (hnoneg : ∀ a ∈ c, ∀ i, a.bias ≠ .dyadic .neg i) :
    ∀ a ∈ c, a.bias = .zero := by
  have hb := (reachable_ledger_bounds init c hinit hreach
    (fun a ha => by have := hphase a ha; omega)).1
  have h0 : (initialGap init : ℚ) = 0 := by rw [hgap]; simp
  rw [h0] at hb
  unfold loSum at hb
  have hnn : ∀ a ∈ c, 0 ≤ ledgerLo a := fun a ha =>
    ledgerLo_nonneg_of_not_neg a (by have := hphase a ha; omega) (hnoneg a ha)
  intro a ha
  rcases hab : a.bias with _ | ⟨s, i⟩
  · rfl
  · cases s
    · exfalso
      have hpos := ledgerLo_pos_of_pos a (by have := hphase a ha; omega) i hab
      have := sum_map_pos_of_mem c hnn ha hpos
      linarith
    · exact absurd hab (hnoneg a ha i)

/-- A zero initial gap and no positive bias force every bias of a phase-9 configuration to zero. -/
theorem bias_zero_of_initialGap_zero_of_no_pos
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase : ∀ a ∈ c, a.phase.val = 9)
    (hgap : initialGap init = 0)
    (hnopos : ∀ a ∈ c, ∀ i, a.bias ≠ .dyadic .pos i) :
    ∀ a ∈ c, a.bias = .zero := by
  have hb := (reachable_ledger_bounds init c hinit hreach
    (fun a ha => by have := hphase a ha; omega)).2
  have h0 : (initialGap init : ℚ) = 0 := by rw [hgap]; simp
  rw [h0] at hb
  unfold hiSum at hb
  have hnp : ∀ a ∈ c, ledgerHi a ≤ 0 := fun a ha =>
    ledgerHi_nonpos_of_not_pos a (by have := hphase a ha; omega) (hnopos a ha)
  intro a ha
  rcases hab : a.bias with _ | ⟨s, i⟩
  · rfl
  · cases s
    · exact absurd hab (hnopos a ha i)
    · exfalso
      have hneg := ledgerHi_neg_of_neg a (by have := hphase a ha; omega) i hab
      have := sum_map_neg_of_mem c hnp ha hneg
      linarith

end Ripple.PopulationProtocol.ExactMajority
