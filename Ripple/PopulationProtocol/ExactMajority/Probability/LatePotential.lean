import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Model
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6FuelLedger
import Ripple.PopulationProtocol.ExactMajority.Probability.HourCoupling
import Mathlib.Tactic.FieldSimp

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Ripple.PopulationProtocol.ExactMajority.LatePotential

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

abbrev InputCfg (n : ℕ) :=
  Config (AgentState (PhaseThreeModel.Numeric.hourIndex n) 256)

noncomputable def shallowLargePotential {n : ℕ}
    (ell : ℕ) (c : InputCfg n) : ℕ :=
  (c.map (fun a =>
    if a.role = .main then
      match a.bias with
      | .zero => 0
      | .dyadic _ j =>
          if j.val < ell then 128 ^ (ell - j.val - 1) else 0
    else 0)).sum

noncomputable def fuelFloor (n : ℕ) : ℕ :=
  Nat.ceil ((687 / 10000 : ℝ) * n)

private def agentWeight (ell : ℕ) (a : AgentState L K) : ℕ :=
  if a.role = .main then
    match a.bias with
    | .zero => 0
    | .dyadic _ j =>
        if j.val < ell then 128 ^ (ell - j.val - 1) else 0
  else 0

private def mass (ell : ℕ) (c : Config (AgentState L K)) : ℕ :=
  (c.map (agentWeight ell)).sum

private noncomputable def credit
    (ell : Fin (L + 1)) (r m : AgentState L K) : ℕ :=
  if Phase6FuelLedger.IsTwoFuel ell r then agentWeight ell.val m else 0

private theorem weight_reserve (ell : ℕ) (r : AgentState L K)
    (hr : r.role = .reserve) : agentWeight ell r = 0 := by
  simp [agentWeight, hr]

private theorem weight_witness (ell : ℕ) (a : AgentState L K)
    (ha : agentWeight ell a ≠ 0) :
    a.role = .main ∧
      ∃ σ j, a.bias = .dyadic σ j ∧ j.val < ell := by
  have hm : a.role = .main := by
    by_contra hm
    exact ha (by simp [agentWeight, hm])
  refine ⟨hm, ?_⟩
  cases hb : a.bias with
  | zero => exact False.elim (ha (by simp [agentWeight, hm, hb]))
  | dyadic σ j =>
      refine ⟨σ, j, rfl, ?_⟩
      by_contra hj
      exact ha (by simp [agentWeight, hm, hb, hj])

private theorem shallowLargePotential_eq_mass {n : ℕ} (ell : ℕ) (c : InputCfg n) :
    shallowLargePotential ell c = mass ell c := by
  unfold shallowLargePotential mass
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  unfold agentWeight
  by_cases h : a.role = .main
  · rw [if_pos h, if_pos h]
    cases a.bias <;> rfl
  · rw [if_neg h, if_neg h]

private theorem mass_add (ell : ℕ) (c d : Config (AgentState L K)) :
    mass ell (c + d) = mass ell c + mass ell d := by
  simp only [mass, Multiset.map_add, Multiset.sum_add]

private theorem mass_pair (ell : ℕ) (s t : AgentState L K) :
    mass ell {s, t} = agentWeight ell s + agentWeight ell t := by
  change ((s ::ₘ t ::ₘ 0).map (agentWeight ell)).sum = _
  simp

private theorem mass_eq_sum_count (ell : ℕ) (c : Config (AgentState L K)) :
    mass ell c = ∑ a : AgentState L K, c.count a * agentWeight ell a := by
  classical
  unfold mass
  calc
    (c.map (agentWeight ell)).sum =
        ∑ a ∈ c.toFinset, c.count a * agentWeight ell a := by
          rw [Finset.sum_multiset_map_count]
          simp [Config.count]
    _ = ∑ a : AgentState L K, c.count a * agentWeight ell a := by
          refine Finset.sum_subset (Finset.subset_univ c.toFinset) ?_
          intro a _ ha
          have hcount : c.count a = 0 := by
            rw [Config.count, Multiset.count_eq_zero]
            simpa using ha
          simp [hcount]

/-- One successful shallow split leaves at most one sixty-fourth
of the input pair weight, including the boundary where both outputs vanish. -/
private theorem split_pair_contract
    (ell : ℕ) (r m : AgentState L K) {σ : Sign} {j : Fin (L + 1)}
    (hr : r.role = .reserve) (hm : m.role = .main)
    (hb : m.bias = .dyadic σ j) (hj : j.val < ell)
    (hne : r.hour.val ≠ L) (hgt : j.val < r.hour.val) (hlt : j.val < L) :
    64 * (agentWeight ell (doSplit L K r m).1 +
      agentWeight ell (doSplit L K r m).2) ≤
      agentWeight ell r + agentWeight ell m := by
  rw [Phase6Convergence.doSplit_apply r m hb hne hgt hlt]
  simp only [agentWeight, hr, hm, hb, hj, reduceCtorEq, ↓reduceIte, zero_add]
  change 64 * ((if j.val + 1 < ell then
      128 ^ (ell - (j.val + 1) - 1) else 0) +
    (if j.val + 1 < ell then
      128 ^ (ell - (j.val + 1) - 1) else 0)) ≤ 128 ^ (ell - j.val - 1)
  by_cases hnext : j.val + 1 < ell
  · rw [if_pos hnext]
    have hexp : ell - j.val - 1 = (ell - (j.val + 1) - 1) + 1 := by omega
    rw [hexp, pow_succ]
    omega
  · rw [if_neg hnext]
    simp

private theorem split_pair_le (ell : ℕ) (r m : AgentState L K)
    (hr : r.role = .reserve) (hm : m.role = .main) :
    agentWeight ell (doSplit L K r m).1 +
      agentWeight ell (doSplit L K r m).2 ≤
        agentWeight ell r + agentWeight ell m := by
  by_cases happ : Phase6Convergence.DoSplitApplicable r m
  · obtain ⟨σ, j, hb, hne, hgt, hlt⟩ := happ
    by_cases hj : j.val < ell
    · have h := split_pair_contract ell r m hr hm hb hj hne hgt hlt
      omega
    · rw [Phase6Convergence.doSplit_apply r m hb hne hgt hlt]
      have hnext : ¬ j.val + 1 < ell := by omega
      simp [agentWeight, hr, hm, hb, hj, hnext]
  · rw [Phase6Convergence.doSplit_eq_self_of_not_applicable r m happ]

private theorem clock_weight (ell : ℕ) (a : AgentState L K)
    (ha : 5 ≤ a.phase.val) :
    agentWeight ell
        (if a.role = .clock then stdCounterSubroutine L K a else a) =
      agentWeight ell a := by
  by_cases hc : a.role = .clock
  · rw [if_pos hc]
    unfold agentWeight
    rw [Phase6Convergence.stdCounterSubroutine_role_ge_five6 a ha,
      Phase6Convergence.stdCounterSubroutine_bias_ge_five a ha]
  · rw [if_neg hc]

private theorem credit_zero_of_main (ell : Fin (L + 1))
    (m r : AgentState L K) (hm : m.role = .main) :
    credit ell m r = 0 := by
  simp [credit, Phase6FuelLedger.IsTwoFuel, hm]

private theorem credit_zero_of_not_guard (ell : Fin (L + 1))
    (r m : AgentState L K)
    (hguard : ¬ (r.role = .reserve ∧ m.role = .main ∧ m.bias ≠ .zero)) :
    credit ell r m = 0 := by
  by_cases hf : Phase6FuelLedger.IsTwoFuel ell r
  · by_cases hw : agentWeight ell.val m = 0
    · simp [credit, hf, hw]
    · obtain ⟨hm, σ, j, hb, _⟩ := weight_witness ell.val m hw
      exfalso
      exact hguard ⟨hf.1, hm, by simp [hb]⟩
  · simp [credit, hf]

private theorem split_pair_credit
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (r m : AgentState L K)
    (hr : r.role = .reserve) (hm : m.role = .main) :
    64 * (agentWeight ell.val (doSplit L K r m).1 +
        agentWeight ell.val (doSplit L K r m).2) +
      63 * credit ell r m ≤
        64 * (agentWeight ell.val r + agentWeight ell.val m) := by
  have hmono := split_pair_le ell.val r m hr hm
  by_cases hf : Phase6FuelLedger.IsTwoFuel ell r
  · rw [credit, if_pos hf]
    by_cases hw : agentWeight ell.val m = 0
    · rw [hw]
      omega
    · obtain ⟨_, σ, j, hb, hj⟩ := weight_witness ell.val m hw
      have hne : r.hour.val ≠ L := by
        rcases hf.2 with h | h <;> omega
      have hgt : j.val < r.hour.val := by
        rcases hf.2 with h | h <;> omega
      have hlt : j.val < L := by omega
      have h := split_pair_contract ell.val r m hr hm hb hj hne hgt hlt
      have hz := weight_reserve ell.val r hr
      omega
  · rw [credit, if_neg hf]
    omega

/-- The two credits are exactly the two orientations of the complete
compatible reserve union; neither union component is discarded. -/
private theorem phase_pair_credit
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K) (hs : 6 ≤ s.phase.val) (ht : 6 ≤ t.phase.val) :
    64 * (agentWeight ell.val (Phase6Transition L K s t).1 +
        agentWeight ell.val (Phase6Transition L K s t).2) +
      63 * (credit ell s t + credit ell t s) ≤
        64 * (agentWeight ell.val s + agentWeight ell.val t) := by
  unfold Phase6Transition
  simp only
  set sFirst :=
    (if s.role = .reserve ∧ t.role = .main ∧ t.bias ≠ .zero then
      (doSplit L K s t).1
    else if t.role = .reserve ∧ s.role = .main ∧ s.bias ≠ .zero then
      (doSplit L K t s).2
    else s) with hsFirst
  set tFirst :=
    (if s.role = .reserve ∧ t.role = .main ∧ t.bias ≠ .zero then
      (doSplit L K s t).2
    else if t.role = .reserve ∧ s.role = .main ∧ s.bias ≠ .zero then
      (doSplit L K t s).1
    else t) with htFirst
  have hpre :
      64 * (agentWeight ell.val sFirst + agentWeight ell.val tFirst) +
        63 * (credit ell s t + credit ell t s) ≤
          64 * (agentWeight ell.val s + agentWeight ell.val t) := by
    rw [hsFirst, htFirst]
    split_ifs with hfirst hsecond
    · rw [credit_zero_of_main ell t s hfirst.2.1, add_zero]
      exact split_pair_credit ell hell s t hfirst.1 hfirst.2.1
    · have h := split_pair_credit ell hell t s hsecond.1 hsecond.2.1
      rw [credit_zero_of_main ell s t hsecond.2.1, zero_add]
      omega
    · simp [credit_zero_of_not_guard ell s t hfirst,
        credit_zero_of_not_guard ell t s hsecond]
  have hsp : 5 ≤ sFirst.phase.val := by
    rw [hsFirst]
    split_ifs with hfirst hsecond
    · rw [Phase6Convergence.doSplit_phase_fst_eq s t]
      omega
    · rw [Phase6Convergence.doSplit_phase_snd_eq t s]
      omega
    · omega
  have htp : 5 ≤ tFirst.phase.val := by
    rw [htFirst]
    split_ifs with hfirst hsecond
    · rw [Phase6Convergence.doSplit_phase_snd_eq s t]
      omega
    · rw [Phase6Convergence.doSplit_phase_fst_eq t s]
      omega
    · omega
  rw [clock_weight ell.val sFirst hsp, clock_weight ell.val tFirst htp]
  exact hpre

private theorem mass_step_credit
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (c : Config (AgentState L K)) (hphase : ∀ a ∈ c, a.phase.val = 6)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t) :
    64 * mass ell.val (Protocol.stepOrSelf (NonuniformMajority L K) c s t) +
      63 * (credit ell s t + credit ell t s) ≤ 64 * mass ell.val c := by
  have hsmem : s ∈ c :=
    Multiset.mem_of_le (show ({s, t} : Multiset (AgentState L K)) ≤ c from happ)
      (by simp)
  have htmem : t ∈ c :=
    Multiset.mem_of_le (show ({s, t} : Multiset (AgentState L K)) ≤ c from happ)
      (by simp)
  have hs := hphase s hsmem
  have ht := hphase t htmem
  have hp := phase_pair_credit ell hell s t (by omega) (by omega)
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
      c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have htr := Phase6Convergence.Transition_eq_Phase6Transition_of_phase6 s t hs ht
  have hsplit : c = (c - {s, t}) + {s, t} :=
    (tsub_add_cancel_of_le happ).symm
  have hcval : mass ell.val c =
      mass ell.val (c - {s, t}) +
        (agentWeight ell.val s + agentWeight ell.val t) := by
    conv_lhs => rw [hsplit]
    rw [mass_add, mass_pair]
  rw [hstep, mass_add, mass_pair, htr, hcval]
  omega

private theorem applicable_of_pos_count
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (h : 0 < c.interactionCount s t) : Protocol.Applicable c s t := by
  change {s, t} ≤ c
  rw [Multiset.le_iff_count]
  intro a
  simp only [Config.interactionCount, Config.count] at h
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  by_cases heq : s = t
  · subst heq
    simp only [ite_true] at h
    have htwo : 2 ≤ Multiset.count s c := by
      by_contra hlt
      have hle : Multiset.count s c ≤ 1 := by omega
      have hz : Multiset.count s c * (Multiset.count s c - 1) = 0 := by
        rcases Nat.eq_zero_or_pos (Multiset.count s c) with hzero | hpos
        · simp [hzero]
        · have hone : Multiset.count s c = 1 := by omega
          simp [hone]
      omega
    by_cases ha : a = s <;> simp_all
  · simp only [if_neg heq] at h
    have hspos : 0 < Multiset.count s c :=
      pos_of_mul_pos_left h (Nat.zero_le _)
    have htpos : 0 < Multiset.count t c :=
      pos_of_mul_pos_right h (Nat.zero_le _)
    by_cases has : a = s <;> by_cases hat : a = t <;> simp_all <;> omega

private theorem interactionCount_comm
    (c : Config (AgentState L K)) (s t : AgentState L K) :
    c.interactionCount s t = c.interactionCount t s := by
  by_cases h : s = t
  · subst t
    rfl
  · simp [Config.interactionCount, h, Ne.symm h, mul_comm]

private theorem credit_count_sum
    (ell : Fin (L + 1)) (c : Config (AgentState L K)) :
    (∑ s : AgentState L K, ∑ t : AgentState L K,
      c.interactionCount s t * credit ell s t) =
      Phase6FuelLedger.twoReserveFuel ell c * mass ell.val c := by
  have hpoint : ∀ s t : AgentState L K,
      c.interactionCount s t * credit ell s t =
        (if Phase6FuelLedger.IsTwoFuel ell s then c.count s else 0) *
          (c.count t * agentWeight ell.val t) := by
    intro s t
    by_cases hf : Phase6FuelLedger.IsTwoFuel ell s
    · by_cases heq : s = t
      · subst t
        have hw := weight_reserve ell.val s hf.1
        simp [credit, hf, hw]
      · simp only [credit, if_pos hf, Config.interactionCount, if_neg heq]
        ring
    · simp [credit, hf]
  have hsumfuel :
      (∑ s : AgentState L K,
        if Phase6FuelLedger.IsTwoFuel ell s then c.count s else 0) =
      Phase6FuelLedger.twoReserveFuel ell c := by
    rw [Phase6FuelLedger.twoReserveFuel, Phase6Convergence.countP_eq_sum_count6,
      Finset.sum_filter]
  simp_rw [hpoint, ← Finset.mul_sum]
  rw [← Finset.sum_mul, hsumfuel, ← mass_eq_sum_count]

private theorem credit_count_sum_reverse
    (ell : Fin (L + 1)) (c : Config (AgentState L K)) :
    (∑ s : AgentState L K, ∑ t : AgentState L K,
      c.interactionCount s t * credit ell t s) =
      Phase6FuelLedger.twoReserveFuel ell c * mass ell.val c := by
  rw [Finset.sum_comm]
  calc
    (∑ t : AgentState L K, ∑ s : AgentState L K,
      c.interactionCount s t * credit ell t s) =
        ∑ t : AgentState L K, ∑ s : AgentState L K,
          c.interactionCount t s * credit ell t s := by
            refine Finset.sum_congr rfl ?_
            intro t _
            refine Finset.sum_congr rfl ?_
            intro s _
            rw [interactionCount_comm c s t]
    _ = Phase6FuelLedger.twoReserveFuel ell c * mass ell.val c :=
      credit_count_sum ell c

private theorem both_credits_count_sum
    (ell : Fin (L + 1)) (c : Config (AgentState L K)) :
    (∑ s : AgentState L K, ∑ t : AgentState L K,
      c.interactionCount s t * (credit ell s t + credit ell t s)) =
      2 * Phase6FuelLedger.twoReserveFuel ell c * mass ell.val c := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [credit_count_sum, credit_count_sum_reverse]
  ring

private noncomputable def numerator
    (ell : ℕ) (c : Config (AgentState L K)) : ℕ :=
  ∑ s : AgentState L K, ∑ t : AgentState L K,
    c.interactionCount s t *
      mass ell (Protocol.stepOrSelf (NonuniformMajority L K) c s t)

private theorem numerator_bound
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (c : Config (AgentState L K)) (hphase : ∀ a ∈ c, a.phase.val = 6) :
    64 * numerator ell.val c +
      126 * Phase6FuelLedger.twoReserveFuel ell c * mass ell.val c ≤
        64 * c.totalPairs * mass ell.val c := by
  have hpoint : ∀ s t : AgentState L K,
      c.interactionCount s t *
        (64 * mass ell.val (Protocol.stepOrSelf (NonuniformMajority L K) c s t) +
          63 * (credit ell s t + credit ell t s)) ≤
        c.interactionCount s t * (64 * mass ell.val c) := by
    intro s t
    by_cases hz : c.interactionCount s t = 0
    · simp [hz]
    · exact Nat.mul_le_mul_left _ (mass_step_credit ell hell c hphase s t
        (applicable_of_pos_count c s t (Nat.pos_of_ne_zero hz)))
  have hs := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hpoint s t))
  have hexpand : ∀ s t : AgentState L K,
      c.interactionCount s t *
        (64 * mass ell.val (Protocol.stepOrSelf (NonuniformMajority L K) c s t) +
          63 * (credit ell s t + credit ell t s)) =
        64 * (c.interactionCount s t *
          mass ell.val (Protocol.stepOrSelf (NonuniformMajority L K) c s t)) +
        63 * (c.interactionCount s t * (credit ell s t + credit ell t s)) := by
    intro s t
    ring
  simp_rw [hexpand, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  rw [both_credits_count_sum] at hs
  simp_rw [← Finset.sum_mul] at hs
  rw [Config.sum_interactionCount] at hs
  change 64 * numerator ell.val c +
      63 * (2 * Phase6FuelLedger.twoReserveFuel ell c * mass ell.val c) ≤
        c.totalPairs * (64 * mass ell.val c) at hs
  nlinarith only [hs]

private theorem expectation_eq_numerator
    (ell : ℕ) (c : Config (AgentState L K)) (hc : 2 ≤ c.card) :
    (∫ c', (mass ell c' : ℝ) ∂(NonuniformMajority L K).transitionKernel c) =
      (numerator ell c : ℝ) / (c.totalPairs : ℝ) := by
  rw [HourCouplingAzuma.integral_transitionKernel_eq_sum _ c hc]
  rw [show (Finset.univ : Finset (AgentState L K × AgentState L K)) =
      Finset.univ ×ˢ Finset.univ from Finset.univ_product_univ.symm,
    Finset.sum_product]
  simp only [Config.interactionProb, ENNReal.toReal_div, ENNReal.toReal_natCast]
  have hpoint : ∀ s t : AgentState L K,
      (c.interactionCount s t : ℝ) / (c.totalPairs : ℝ) *
        (mass ell (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ) =
      ((c.interactionCount s t : ℝ) *
        (mass ell (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ)) *
          (c.totalPairs : ℝ)⁻¹ := by
    intro s t
    simp only [div_eq_mul_inv]
    ring
  simp_rw [hpoint, ← Finset.sum_mul]
  simp only [numerator, Nat.cast_sum, Nat.cast_mul, div_eq_mul_inv]

/-- N17: the base-128 shallow potential contracts using both ordered
orientations and every reserve in the two-level compatible union. -/
theorem shallow_large_potential_kernel_drift
    (n : ℕ) (hn : 2 ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (c : InputCfg n) (hcard : c.card = n)
    (hphase : ∀ a ∈ c, a.phase.val = 6)
    (hfuel : Phase6FuelLedger.TwoLevelFuelLedger
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (fuelFloor n) c) :
    (∫ c', (shallowLargePotential ell.val c' : ℝ) ∂
      (NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c) ≤
      (1 - (43281 : ℝ) / (320000 * ((n : ℝ) - 1))) *
        shallowLargePotential ell.val c := by
  have hc : 2 ≤ c.card := by omega
  have hfloor : fuelFloor n ≤ Phase6FuelLedger.twoReserveFuel ell c :=
    Phase6FuelLedger.twoLevelFuelLedger_union_floor ell hell (fuelFloor n) c hfuel
  have hfloorReal : (687 / 10000 : ℝ) * n ≤
      (Phase6FuelLedger.twoReserveFuel ell c : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hfloor)
  have hnum := numerator_bound ell hell c hphase
  have hnumReal :
      64 * (numerator ell.val c : ℝ) +
        126 * (Phase6FuelLedger.twoReserveFuel ell c : ℝ) * (mass ell.val c : ℝ) ≤
      64 * (c.totalPairs : ℝ) * (mass ell.val c : ℝ) := by
    exact_mod_cast hnum
  have hden : (c.totalPairs : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Config.totalPairs, hcard, Nat.cast_mul, Nat.cast_sub (by omega)]
    norm_num
  have hnReal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnSub : 0 < (n : ℝ) - 1 := by linarith
  have hdenPos : 0 < (n : ℝ) * ((n : ℝ) - 1) :=
    mul_pos (by linarith) hnSub
  have hmul := mul_le_mul_of_nonneg_right hfloorReal
    (show (0 : ℝ) ≤ (mass ell.val c : ℝ) by positivity)
  rw [hden] at hnumReal
  have hbound : (numerator ell.val c : ℝ) ≤
      (n : ℝ) * ((n : ℝ) - 1) * (mass ell.val c : ℝ) -
        (43281 / 320000 : ℝ) * n * (mass ell.val c : ℝ) := by
    nlinarith only [hnumReal, hmul]
  simp only [shallowLargePotential_eq_mass]
  rw [expectation_eq_numerator ell.val c hc, hden]
  apply (div_le_iff₀ hdenPos).2
  calc
    (numerator ell.val c : ℝ) ≤
        (n : ℝ) * ((n : ℝ) - 1) * (mass ell.val c : ℝ) -
          (43281 / 320000 : ℝ) * n * (mass ell.val c : ℝ) := hbound
    _ = ((1 - (43281 : ℝ) / (320000 * ((n : ℝ) - 1))) *
        (mass ell.val c : ℝ)) * ((n : ℝ) * ((n : ℝ) - 1)) := by
          field_simp [ne_of_gt hnSub]
          <;> ring

end Ripple.PopulationProtocol.ExactMajority.LatePotential
