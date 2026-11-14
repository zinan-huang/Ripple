import Ripple.PopulationProtocol.ExactMajority.Probability.StageEventSpec
import Ripple.PopulationProtocol.ExactMajority.Analysis.DeterministicChain

/-!
# Mixed-mass and initialization algebra for Phase-3 averaging

These are deterministic prerequisites for DOTY-AVERAGING Lemmas 1, 3 and 4.
The initialization lemmas use the actual Init-3 function, with the phase field
updated before initialization, as in the protocol wrapper. They do not assert
a probability estimate, a full-wrapper fuel invariant, or a mixed-potential
kernel drift.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingMixedAlgebra

open TimeTheorem P3DeterministicAlgebra

variable {L K : ℕ}

/-- Positive-side mass of the actual mixed signed observable. -/
def mixedPositiveMass (c : Config (AgentState L K)) : ℚ :=
  (c.map (fun a => max (prePhase4Mass a) 0)).sum

/-- Negative-side mass of the actual mixed signed observable. -/
def mixedNegativeMass (c : Config (AgentState L K)) : ℚ :=
  (c.map (fun a => max (-prePhase4Mass a) 0)).sum

/-- Absolute mass, with pending labels read through their small bias. -/
def mixedAbsoluteMass (c : Config (AgentState L K)) : ℚ :=
  (c.map (fun a => |prePhase4Mass a|)).sum

private theorem signedSideIdentities (x : ℚ) :
    max x 0 - max (-x) 0 = x ∧ max x 0 + max (-x) 0 = |x| := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx]
    constructor <;> ring
  · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'), abs_of_nonpos hx']
    constructor <;> ring

/-- Both identities are exact even before all labels have initialized. -/
theorem mixedMassIdentities (c : Config (AgentState L K)) :
    mixedPositiveMass c - mixedNegativeMass c = prePhase4MassSum c ∧
      mixedPositiveMass c + mixedNegativeMass c = mixedAbsoluteMass c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [mixedPositiveMass, mixedNegativeMass, mixedAbsoluteMass,
        prePhase4MassSum]
  | cons a c ih =>
      simp only [mixedPositiveMass, mixedNegativeMass, mixedAbsoluteMass,
        prePhase4MassSum, Multiset.map_cons, Multiset.sum_cons] at ih ⊢
      have ha := signedSideIdentities (prePhase4Mass a)
      constructor <;> linarith [ih.1, ih.2, ha.1, ha.2]

theorem mixedAbsoluteMass_eq_reviewed {n : ℕ} (c : InputCfg n) :
    mixedAbsoluteMass c = StageEventSpec.mixedAbsMass c := rfl

/-- Once signed conservation and absolute-mass monotonicity are established,
neither signed-side mass can increase. This avoids a second transition audit. -/
theorem mixedSides_le_of_absolute_le
    (c c' : Config (AgentState L K))
    (hsigned : prePhase4MassSum c' = prePhase4MassSum c)
    (habsolute : mixedAbsoluteMass c' ≤ mixedAbsoluteMass c) :
    mixedPositiveMass c' ≤ mixedPositiveMass c ∧
      mixedNegativeMass c' ≤ mixedNegativeMass c := by
  have hc := mixedMassIdentities c
  have hc' := mixedMassIdentities c'
  constructor <;> linarith [hc.1, hc.2, hc'.1, hc'.2]

/-- Signed mixed mass on the actual pair-log trace. The existing reachable
invariant covers the asynchronous initializations and the selected dispatch. -/
theorem trace_mixedSigned_eq_initialGap
    (init : Cfg L K) (hinit : validInitial init)
    (ω : Ω L K) (t : ℕ)
    (hphase : ∀ a ∈ trace init ω t, a.phase.val ≤ 4) :
    prePhase4MassSum (trace init ω t) = (initialGap init : ℚ) := by
  apply reachable_prePhase4MassSum_eq_initialGap_of_phase_le_four
    init (trace init ω t) hinit
  · simpa only [TimeTheorem.trace_zero] using
      (TimeTheorem.trace_reachable init ω (s := 0) (t := t) (Nat.zero_le t))
  · exact hphase

theorem trace_mixedSides_difference
    (init : Cfg L K) (hinit : validInitial init)
    (ω : Ω L K) (t : ℕ)
    (hphase : ∀ a ∈ trace init ω t, a.phase.val ≤ 4) :
    mixedPositiveMass (trace init ω t) - mixedNegativeMass (trace init ω t) =
      (initialGap init : ℚ) :=
  (mixedMassIdentities (trace init ω t)).1.trans
    (trace_mixedSigned_eq_initialGap init hinit ω t hphase)

/-- The actual Init-3 block applied after updating the phase field. -/
def initializeAtPhaseThree (a : AgentState L K) : AgentState L K :=
  phaseInit L K ⟨3, by decide⟩ { a with phase := ⟨3, by decide⟩ }

theorem initializeAtPhaseThree_phase (a : AgentState L K) :
    (initializeAtPhaseThree a).phase.val = 3 := by
  cases hr : a.role <;> simp [initializeAtPhaseThree, phaseInit, hr]

theorem initializeAtPhaseThree_role (a : AgentState L K) :
    (initializeAtPhaseThree a).role = a.role := by
  simp [initializeAtPhaseThree, phaseInit_role]

theorem safe_small_mass_le_one (a : AgentState L K)
    (hsafe : 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4) :
    |(AgentState.smallBiasInt a : ℚ)| ≤ 1 := by
  have hc : a.smallBias.val = 2 ∨ a.smallBias.val = 3 ∨ a.smallBias.val = 4 := by
    omega
  rcases hc with h | h | h <;> norm_num [AgentState.smallBiasInt, h]

/-- Safe pending values transfer exactly; non-Mains must carry zero pending mass. -/
theorem initializeAtPhaseThree_signed_mass (a : AgentState L K)
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3)
    (hsafe : 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4) :
    Bias.toRat (initializeAtPhaseThree a).bias = (AgentState.smallBiasInt a : ℚ) := by
  have hc : a.smallBias.val = 2 ∨ a.smallBias.val = 3 ∨ a.smallBias.val = 4 := by
    omega
  rcases hc with h | h | h <;> cases hr : a.role <;>
    simp [initializeAtPhaseThree, phaseInit, AgentState.smallBiasInt,
      Bias.toRat, hr, h] at hcarrier ⊢

theorem initializeAtPhaseThree_mixed_mass (a : AgentState L K)
    (hpending : a.phase.val < 3)
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3)
    (hsafe : 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4) :
    prePhase4Mass (initializeAtPhaseThree a) = prePhase4Mass a := by
  have ha : ¬ (initializeAtPhaseThree a).phase.val < 3 := by
    rw [initializeAtPhaseThree_phase]
    omega
  simpa only [prePhase4Mass, if_neg ha, if_pos hpending] using
    initializeAtPhaseThree_signed_mass a hcarrier hsafe

theorem initializeAtPhaseThree_absolute_mass (a : AgentState L K)
    (hpending : a.phase.val < 3)
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3)
    (hsafe : 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4) :
    |prePhase4Mass (initializeAtPhaseThree a)| = |prePhase4Mass a| :=
  congrArg abs (initializeAtPhaseThree_mixed_mass a hpending hcarrier hsafe)

/-- The charge assigned to one pending Main in the double-pending potential. -/
def pendingPotentialWeight (h : ℕ) (a : AgentState L K) : ℚ :=
  2 * (4 : ℚ) ^ (h - 1) * |(AgentState.smallBiasInt a : ℚ)|

/-- Init 3 alone removes exactly half the pending potential. Further Phase-3
work must be handled by the separate pair-transition inequalities. -/
theorem initializeAtPhaseThree_phi_eq_half_pending
    (h : ℕ) (hh : 1 ≤ h) (a : AgentState L K)
    (hmain : a.role = .main)
    (hsafe : 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4) :
    agentPhiAboveQ h (initializeAtPhaseThree a) =
      (1 / 2 : ℚ) * pendingPotentialWeight h a := by
  have hpos : 0 < h := by omega
  have hc : a.smallBias.val = 2 ∨ a.smallBias.val = 3 ∨ a.smallBias.val = 4 := by
    omega
  rcases hc with hb | hb | hb <;>
    simp [initializeAtPhaseThree, phaseInit, hmain, hb, agentPhiAboveQ,
      phiBiasWeightQ, pendingPotentialWeight, AgentState.smallBiasInt, hpos] <;> ring

/-- The per-Main contribution to the changing-zero fuel, with one unit reserved
for each inactive Main. -/
def mainFuel (h : ℕ) (a : AgentState L K) : ℚ :=
  if a.role = .main then
    (2 : ℚ) ^ h * |prePhase4Mass a| +
      if a.phase.val < 3 then 1
      else if a.bias = .zero ∧ a.hour.val < h then 1 else 0
  else 0

/-- A zero activation exchanges its inactive charge for its low-hour-zero charge;
a nonzero activation removes its inactive charge. -/
theorem initializeAtPhaseThree_fuel_identity
    (h : ℕ) (hh : 1 ≤ h) (a : AgentState L K)
    (hmain : a.role = .main) (hpending : a.phase.val < 3)
    (hsafe : 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4) :
    mainFuel h (initializeAtPhaseThree a) +
        (if a.smallBias.val = 3 then (0 : ℚ) else 1) =
      mainFuel h a := by
  have hpos : 0 < h := by omega
  have hc : a.smallBias.val = 2 ∨ a.smallBias.val = 3 ∨ a.smallBias.val = 4 := by
    omega
  rcases hc with hb | hb | hb <;>
    simp [mainFuel, initializeAtPhaseThree, phaseInit, hmain, hpending,
      hb, prePhase4Mass, AgentState.smallBiasInt, Bias.toRat, hpos] <;> ring

theorem initializeAtPhaseThree_fuel_le
    (h : ℕ) (hh : 1 ≤ h) (a : AgentState L K)
    (hmain : a.role = .main) (hpending : a.phase.val < 3)
    (hsafe : 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4) :
    mainFuel h (initializeAtPhaseThree a) ≤ mainFuel h a := by
  have hid := initializeAtPhaseThree_fuel_identity h hh a hmain hpending hsafe
  split_ifs at hid <;> linarith

/-- An initialized zero is dragged in the same Phase-3 dispatch. This verifies the
unit-service case for an inactive zero, at the initializer-plus-dispatch level. -/
theorem initializeThenClock_zero_fuel_drop
    (h : ℕ) (a clock : AgentState L K)
    (hmain : a.role = .main) (hpending : a.phase.val < 3)
    (hzero : a.smallBias.val = 3) (hclock : clock.role = .clock)
    (hcap : h ≤ L) (hminute : h ≤ clock.minute.val / K) :
    mainFuel h (Phase3Transition L K (initializeAtPhaseThree a) clock).1 + 1 =
      mainFuel h a := by
  have hf :
      (Phase3Transition L K (initializeAtPhaseThree a) clock).1.role = .main ∧
      (Phase3Transition L K (initializeAtPhaseThree a) clock).1.phase.val = 3 ∧
      (Phase3Transition L K (initializeAtPhaseThree a) clock).1.bias = .zero ∧
      (Phase3Transition L K (initializeAtPhaseThree a) clock).1.hour.val =
        min L (clock.minute.val / K) := by
    simp [Phase3Transition, initializeAtPhaseThree, phaseInit, hmain, hzero, hclock]
  rcases hf with ⟨hr, hp, hb, hh⟩
  have hnot :
      ¬ (Phase3Transition L K (initializeAtPhaseThree a) clock).1.hour.val < h := by
    rw [hh]
    exact not_lt.mpr (le_min hcap hminute)
  simp [mainFuel, hr, hp, hb, hnot, hmain, hpending, hzero,
    prePhase4Mass, AgentState.smallBiasInt, Bias.toRat]

theorem biasMass_eq_abs_toRat (b : Bias L) :
    biasMassQ b = |Bias.toRat b| := by
  cases b with
  | zero => simp [biasMassQ, biasPosMassQ, biasNegMassQ, Bias.toRat]
  | dyadic s i =>
      cases s <;>
        simp [biasMassQ, biasPosMassQ, biasNegMassQ, Bias.toRat, weightQ, abs_div]

/-- The active part of the changing-zero ledger for a pair of initialized Mains. -/
def activeFuel (h : ℕ) (a : AgentState L K) : ℚ :=
  (2 : ℚ) ^ h * agentMassQ a +
    if a.bias = .zero ∧ a.hour.val < h then 1 else 0

theorem mainFuel_eq_activeFuel (h : ℕ) (a : AgentState L K)
    (hmain : a.role = .main) (hphase : a.phase.val = 3) :
    mainFuel h a = activeFuel h a := by
  simp [mainFuel, activeFuel, hmain, hphase, prePhase4Mass,
    agentMassQ, biasMass_eq_abs_toRat]

theorem scaled_weight_ge_one (h : ℕ) (i : Fin (L + 1)) (hi : i.val ≤ h) :
    (1 : ℚ) ≤ (2 : ℚ) ^ h * weightQ i := by
  have hpow : (2 : ℚ) ^ i.val ≤ (2 : ℚ) ^ h :=
    pow_le_pow_right₀ (by norm_num) hi
  have hw : (2 : ℚ) ^ i.val * weightQ i = 1 := by
    have hp : (2 : ℚ) ^ i.val ≠ 0 := by positivity
    unfold weightQ
    field_simp [hp]
  nlinarith [mul_le_mul_of_nonneg_right hpow (weightQ_nonneg i)]

/-- Cancellation resets both zero hours to the canceled index. The resulting
low-hour charges are paid by the deleted scaled mass. -/
theorem activeFuel_cancel_pos_neg_le
    (h : ℕ) (s t : AgentState L K) (i : Fin (L + 1)) :
    activeFuel h
        (phase3CancelSplit L K { s with bias := .dyadic .pos i }
          { t with bias := .dyadic .neg i }).1 +
      activeFuel h
        (phase3CancelSplit L K { s with bias := .dyadic .pos i }
          { t with bias := .dyadic .neg i }).2 ≤
    activeFuel h { s with bias := .dyadic .pos i } +
      activeFuel h { t with bias := .dyadic .neg i } := by
  by_cases hi : i.val < h
  · have hw := scaled_weight_ge_one h i (Nat.le_of_lt hi)
    have hle : (2 : ℚ) ≤
        (2 : ℚ) ^ h * weightQ i + (2 : ℚ) ^ h * weightQ i := by linarith
    convert hle using 1 <;>
      norm_num [activeFuel, phase3CancelSplit, agentMassQ, biasMassQ,
        biasPosMassQ, biasNegMassQ, hi] <;> (try simp)
  · have hw : (0 : ℚ) ≤ (2 : ℚ) ^ h * weightQ i :=
      mul_nonneg (by positivity) (weightQ_nonneg i)
    simpa [activeFuel, phase3CancelSplit, agentMassQ, biasMassQ,
      biasPosMassQ, biasNegMassQ, hi] using add_nonneg hw hw

/-- A split preserves weighted mass and consumes exactly the zero's low-hour
charge. The strict implemented guard is retained. -/
theorem activeFuel_split_left_identity
    (h : ℕ) (z b : AgentState L K) (sgn : Sign) (i : Fin (L + 1))
    (hz : z.bias = .zero) (hb : b.bias = .dyadic sgn i)
    (hgt : z.hour.val > i.val) :
    activeFuel h (phase3CancelSplit L K z b).1 +
        activeFuel h (phase3CancelSplit L K z b).2 +
        (if z.hour.val < h then (1 : ℚ) else 0) =
      activeFuel h z + activeFuel h b := by
  have hl : (phase3CancelSplit L K z b).1.bias ≠ .zero := by
    simp [phase3CancelSplit, hz, hb, hgt]
  have hr : (phase3CancelSplit L K z b).2.bias ≠ .zero := by
    simp [phase3CancelSplit, hz, hb, hgt]
  have hm := p3_totalMass_split_delta_left z b sgn i hz hb hgt
  have hscaled := congrArg (fun x : ℚ => (2 : ℚ) ^ h * x) hm
  dsimp only [pairMassQ] at hscaled
  simp [activeFuel, hl, hr, hz, hb] <;> nlinarith [hscaled]

/-! This finite witness concerns the safety premise. The reviewed theorem
requires successful entry provenance, which excludes this state. -/

def unsafePendingWitness : AgentState 0 1 :=
  { input := .A, output := .T, phase := ⟨1, by decide⟩, role := .main, assigned := false, bias := .zero, smallBias := ⟨5, by decide⟩, hour := ⟨0, by decide⟩, minute := ⟨0, by decide⟩, full := false, opinions := ⟨0, by decide⟩, counter := ⟨0, by decide⟩ }

theorem unsafePendingWitness_initialized_clause :
    2 ≤ unsafePendingWitness.phase.val →
      2 ≤ unsafePendingWitness.smallBias.val ∧
        unsafePendingWitness.smallBias.val ≤ 4 := by
  decide

theorem unsafePendingWitness_mass :
    prePhase4Mass unsafePendingWitness = 2 := by
  decide

theorem unsafePendingWitness_init_mass :
    prePhase4Mass (initializeAtPhaseThree unsafePendingWitness) = 1 := by
  norm_num [unsafePendingWitness, initializeAtPhaseThree, phaseInit,
    prePhase4Mass, Bias.toRat]

end Ripple.PopulationProtocol.ExactMajority.AveragingMixedAlgebra

end
