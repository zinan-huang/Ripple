-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingLiveProduct.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCancellationProbability
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingMixedLedgers
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingTerminalReadout

/-!
# Live current-level cancellation products

The outside-level allowance is derived from the actual augmented potential and
the actual deep-label count. Pending agents are included through their small
biases. The statements use the full physical-label populations, so their
products can be passed to the compiled cancellation probability theorem.

This file supplies deterministic live floors. It does not assert the hour
induction or a new stopping-time tail.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingLiveProduct

open TimeTheorem PairLog P3DeterministicAlgebra
open AveragingMixedAlgebra AveragingMixedLedgers AveragingCancellationAlgebra
open AveragingCancellationProbability
open StageEventSpec

variable {L K m : ℕ}

def sideAtom (σ : Sign) (a : AgentState L K) : ℚ :=
  match σ with
  | .pos => max (prePhase4Mass a) 0
  | .neg => max (-prePhase4Mass a) 0

def sideMass (σ : Sign) (c : Cfg L K) : ℚ :=
  (c.map (sideAtom σ)).sum

def AtLevel (σ : Sign) (j : Fin (L + 1)) (a : AgentState L K) : Prop :=
  a.phase.val = 3 ∧ a.role = .main ∧ a.bias = .dyadic σ j

open Classical in
def levelWeight (σ : Sign) (j : Fin (L + 1)) (a : AgentState L K) : ℚ :=
  if AtLevel σ j a then 1 else 0

open Classical in
def levelCount (σ : Sign) (j : Fin (L + 1)) (c : Cfg L K) : ℕ :=
  c.countP (AtLevel σ j)

open Classical in
def deepAtom (h : ℕ) (a : AgentState L K) : ℕ :=
  if a.phase.val = 3 ∧ a.role = .main then
    match a.bias with
    | .zero => 0
    | .dyadic _ j => if h < j.val then 1 else 0
  else 0

def deepCount (h : ℕ) (c : Cfg L K) : ℕ :=
  (c.map (deepAtom h)).sum

def outsideMass (σ : Sign) (j : Fin (L + 1)) (c : Cfg L K) : ℚ :=
  (2 : ℚ) ^ j.val * sideMass σ c - levelCount σ j c

theorem sideAtom_nonneg (σ : Sign) (a : AgentState L K) :
    0 ≤ sideAtom σ a := by
  cases σ <;> exact le_max_right _ _

theorem levelWeight_nonneg (σ : Sign) (j : Fin (L + 1))
    (a : AgentState L K) : 0 ≤ levelWeight σ j a := by
  unfold levelWeight
  split_ifs <;> norm_num

theorem sideMass_pos (c : Cfg L K) :
    sideMass .pos c = mixedPositiveMass c := rfl

theorem sideMass_neg (c : Cfg L K) :
    sideMass .neg c = mixedNegativeMass c := rfl

theorem sideMass_add (c : Cfg L K) :
    sideMass .pos c + sideMass .neg c = mixedAbsoluteMass c :=
  (mixedMassIdentities c).2

theorem sideMass_sub (c : Cfg L K) :
    sideMass .pos c - sideMass .neg c = prePhase4MassSum c :=
  (mixedMassIdentities c).1

theorem sideMass_nonneg (σ : Sign) (c : Cfg L K) :
    0 ≤ sideMass σ c := by
  induction c using Multiset.induction_on with
  | empty => simp [sideMass]
  | cons a c ih =>
      simpa only [sideMass, Multiset.map_cons, Multiset.sum_cons] using
        add_nonneg (sideAtom_nonneg σ a) ih

theorem scaled_weight_at_level (j : Fin (L + 1)) :
    (2 : ℚ) ^ j.val * weightQ j = 1 := by
  have hp : (2 : ℚ) ^ j.val ≠ 0 := by positivity
  unfold weightQ
  field_simp [hp]

theorem sideAtom_of_atLevel (σ : Sign) (j : Fin (L + 1))
    (a : AgentState L K) (ha : AtLevel σ j a) :
    sideAtom σ a = weightQ j := by
  have hp : (0 : ℚ) ≤ 1 / (2 : ℚ) ^ j.val := by positivity
  cases σ <;>
    simp [sideAtom, prePhase4Mass, ha.1, ha.2.2,
      Bias.toRat, weightQ, neg_div, max_eq_left hp]

theorem levelWeight_le_scaled_side (σ : Sign) (j : Fin (L + 1))
    (a : AgentState L K) :
    levelWeight σ j a ≤ (2 : ℚ) ^ j.val * sideAtom σ a := by
  by_cases ha : AtLevel σ j a
  · rw [levelWeight, if_pos ha, sideAtom_of_atLevel σ j a ha,
      scaled_weight_at_level]
  · rw [levelWeight, if_neg ha]
    exact mul_nonneg (by positivity) (sideAtom_nonneg σ a)

theorem sum_levelWeight (σ : Sign) (j : Fin (L + 1)) (c : Cfg L K) :
    (c.map (levelWeight σ j)).sum = (levelCount σ j c : ℚ) := by
  induction c using Multiset.induction_on with
  | empty => simp [levelCount]
  | cons a c ih =>
      by_cases ha : AtLevel σ j a <;>
        simp [levelWeight, levelCount, Multiset.countP_cons, ha] at ih ⊢ <;>
        linarith

theorem levelCount_le_scaled_side (σ : Sign) (j : Fin (L + 1))
    (c : Cfg L K) :
    (levelCount σ j c : ℚ) ≤ (2 : ℚ) ^ j.val * sideMass σ c := by
  rw [← sum_levelWeight]
  induction c using Multiset.induction_on with
  | empty => simp [sideMass]
  | cons a c ih =>
      have ha := levelWeight_le_scaled_side σ j a
      simp only [Multiset.map_cons, Multiset.sum_cons, sideMass] at ih ⊢
      nlinarith only [ha, ih]

theorem outsideMass_nonneg (σ : Sign) (j : Fin (L + 1)) (c : Cfg L K) :
    0 ≤ outsideMass σ j c :=
  sub_nonneg.mpr (levelCount_le_scaled_side σ j c)

theorem scaled_deep_mass_le_half (h : ℕ) (j : Fin (L + 1))
    (hh : h < j.val) :
    (2 : ℚ) ^ h * weightQ j ≤ 1 / 2 := by
  have hp : (2 : ℚ) ^ (h + 1) ≤ (2 : ℚ) ^ j.val :=
    pow_le_pow_right₀ (by norm_num) hh
  rw [pow_succ] at hp
  have heq : (2 : ℚ) ^ h * weightQ j = (2 : ℚ) ^ h / (2 : ℚ) ^ j.val := by
    unfold weightQ
    ring
  rw [heq]
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < (2 : ℚ) ^ j.val)).2
  nlinarith only [hp]

/-- The pointwise outside-level inequality. No freshness assumption is made
about the pending dyadic fields. -/
theorem scaled_agent_mass_le_level_phi_deep
    (j : Fin (L + 1)) (hj : 1 ≤ j.val) (a : AgentState L K)
    (hphase : a.phase.val ≤ 3)
    (hcarrier : a.role ≠ .main → a.bias = .zero) :
    (2 : ℚ) ^ j.val * |prePhase4Mass a| ≤
      levelWeight .pos j a + levelWeight .neg j a +
        2 * augmentedAgentPhi j.val a + (deepAtom j.val a : ℚ) / 2 := by
  by_cases hp : a.phase.val < 3
  · have h := scaled_mixedShallowWeight_le_phi j.val hj a
    have heq : mixedShallowWeight j.val a = |prePhase4Mass a| := by
      simp [mixedShallowWeight, prePhase4Mass, hp]
    rw [heq] at h
    have hl := levelWeight_nonneg .pos j a
    have hr := levelWeight_nonneg .neg j a
    have hd : (0 : ℚ) ≤ (deepAtom j.val a : ℚ) / 2 := by positivity
    linarith
  · have hthree : a.phase.val = 3 := by omega
    cases hb : a.bias with
    | zero =>
        have hl := levelWeight_nonneg .pos j a
        have hr := levelWeight_nonneg .neg j a
        have hφ := augmentedAgentPhi_nonneg j.val a
        have hd : (0 : ℚ) ≤ (deepAtom j.val a : ℚ) / 2 := by positivity
        simp only [prePhase4Mass, if_neg hp, hb, Bias.toRat, abs_zero, mul_zero]
        linarith
    | dyadic σ i =>
        have hm : a.role = .main := by
          by_contra hm
          have hz := hcarrier hm
          rw [hb] at hz
          cases hz
        have habs : |prePhase4Mass a| = weightQ i := by
          cases σ <;>
            simp [prePhase4Mass, hp, hb, Bias.toRat, weightQ, abs_div]
        by_cases hlt : i.val < j.val
        · have h := scaled_mixedShallowWeight_le_phi j.val hj a
          have heq : mixedShallowWeight j.val a = |prePhase4Mass a| := by
            cases σ <;>
              simp [mixedShallowWeight, hp, agentMassAboveQ,
                biasMassAboveQ, hb, hlt, habs]
          rw [heq] at h
          have hl := levelWeight_nonneg .pos j a
          have hr := levelWeight_nonneg .neg j a
          have hd : (0 : ℚ) ≤ (deepAtom j.val a : ℚ) / 2 := by positivity
          linarith
        · by_cases heq : i = j
          · subst i
            rw [habs, scaled_weight_at_level]
            cases σ <;>
              norm_num [levelWeight, AtLevel, hthree, hm, hb,
                augmentedAgentPhi, agentPhiAboveQ, phiBiasWeightQ, deepAtom] <;>
              simp
          · have hne : i.val ≠ j.val := fun h => heq (Fin.ext h)
            have hgt : j.val < i.val := by omega
            have hmass := scaled_deep_mass_le_half j.val i hgt
            rw [habs]
            have hinj : ¬ Bias.dyadic σ i = Bias.dyadic .pos j :=
              fun h => heq (by cases h; rfl)
            have hinj' : ¬ Bias.dyadic σ i = Bias.dyadic .neg j :=
              fun h => heq (by cases h; rfl)
            simpa [levelWeight, AtLevel, hthree, hm, hb, hinj, hinj',
              augmentedAgentPhi, agentPhiAboveQ, phiBiasWeightQ,
              hlt, deepAtom, hgt] using hmass

theorem outsideMass_add_le
    (j : Fin (L + 1)) (hj : 1 ≤ j.val) (c : Cfg L K)
    (hphase : ∀ a ∈ c, a.phase.val ≤ 3)
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.bias = .zero) :
    outsideMass .pos j c + outsideMass .neg j c ≤
      2 * augmentedPhi j.val c + (deepCount j.val c : ℚ) / 2 := by
  have hsum :
      (2 : ℚ) ^ j.val * mixedAbsoluteMass c ≤
        (levelCount .pos j c : ℚ) + (levelCount .neg j c : ℚ) +
          2 * augmentedPhi j.val c + (deepCount j.val c : ℚ) / 2 := by
    rw [← sum_levelWeight, ← sum_levelWeight]
    revert hphase hcarrier
    induction c using Multiset.induction_on with
    | empty =>
        intro _ _
        simp [mixedAbsoluteMass, augmentedPhi, deepCount]
    | cons a c ih =>
        intro hphase hcarrier
        have ha := scaled_agent_mass_le_level_phi_deep j hj a
          (hphase a (Multiset.mem_cons_self _ _))
          (hcarrier a (Multiset.mem_cons_self _ _))
        have ht := ih
          (fun b hb => hphase b (Multiset.mem_cons_of_mem hb))
          (fun b hb => hcarrier b (Multiset.mem_cons_of_mem hb))
        simp only [mixedAbsoluteMass, augmentedPhi, deepCount,
          Multiset.map_cons, Multiset.sum_cons, Nat.cast_add] at ht ⊢
        nlinarith only [ha, ht]
  unfold outsideMass
  rw [← sideMass_add c] at hsum
  nlinarith only [hsum]

theorem outsideMass_allowance
    (j : Fin (L + 1)) (hj : 1 ≤ j.val) (c : Cfg L K) (M : ℕ)
    (hphase : ∀ a ∈ c, a.phase.val ≤ 3)
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.bias = .zero)
    (hphi : (1000 : ℚ) * augmentedPhi j.val c ≤ M)
    (hdeep : 1250 * deepCount j.val c ≤ 3 * M) :
    outsideMass .pos j c + outsideMass .neg j c ≤
      (4 / 1250 : ℚ) * M := by
  have hs := outsideMass_add_le j hj c hphase hcarrier
  have hd : (1250 : ℚ) * (deepCount j.val c : ℚ) ≤ 3 * (M : ℚ) := by
    exact_mod_cast hdeep
  linarith

/-- Scalar monotonicity of the worst product in current total mass and gap. -/
theorem total_mass_worst_product
    {a b M r g δ : ℝ} (hM : 0 ≤ M) (hab : b ≤ a)
    (hg : 0 ≤ g) (hδ : 0 ≤ δ) (hmin : δ ≤ (r - g) / 2)
    (hw : r * M ≤ a + b) (hgap : a - b ≤ g * M) :
    ((r + g) / 2) * ((r - g) / 2 - δ) * M ^ 2 ≤
      a * (b - δ * M) := by
  have hminM := mul_le_mul_of_nonneg_right hmin hM
  have hgM := mul_nonneg hg hM
  have hδM := mul_nonneg hδ hM
  have hfirst : 0 ≤
      (a + b - r * M) * (a + b + r * M - 2 * δ * M) :=
    mul_nonneg (by linarith) (by linarith)
  have hsecond : 0 ≤
      (g * M - (a - b)) * (g * M + (a - b) + 2 * δ * M) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith only [hfirst, hsecond]

/-- Current product from total mass, signed gap and actual off-level loss.
The sign of the gap is handled by symmetry. -/
theorem product_floor_of_total_mass
    {a b A B M r g δ : ℝ} (hM : 0 ≤ M)
    (hg : 0 ≤ g) (hδ : 0 ≤ δ) (hmin : δ ≤ (r - g) / 2)
    (hA : 0 ≤ a - A) (hB : 0 ≤ b - B)
    (hoff : (a - A) + (b - B) ≤ δ * M)
    (hw : r * M ≤ a + b) (hgap : |a - b| ≤ g * M) :
    ((r + g) / 2) * ((r - g) / 2 - δ) * M ^ 2 ≤ A * B := by
  have hminM := mul_le_mul_of_nonneg_right hmin hM
  rcases le_total b a with hab | hab
  · have hgap' : a - b ≤ g * M := (le_abs_self _).trans hgap
    have hδb : δ * M ≤ b := by linarith
    have hfloor := cancellation_product_lower_of_outside_bound hab hδb
      hA hB hoff (by linarith : a - (a - A) ≤ A)
      (by linarith : b - (b - B) ≤ B)
    exact (total_mass_worst_product hM hab hg hδ hmin hw hgap').trans hfloor
  · have hgap' : b - a ≤ g * M := by
      have := neg_le_abs (a - b)
      linarith
    have hδa : δ * M ≤ a := by linarith
    have hfloor := cancellation_product_lower_of_outside_bound hab hδa
      hB hA (by linarith : (b - B) + (a - A) ≤ δ * M)
      (by linarith : b - (b - B) ≤ B)
      (by linarith : a - (a - A) ≤ A)
    have htarget := total_mass_worst_product hM hab hg hδ hmin
      (by linarith : r * M ≤ b + a) hgap'
    simpa only [mul_comm A B] using htarget.trans hfloor

theorem level_product_of_total_mass
    (j : Fin (L + 1)) (hj : 1 ≤ j.val) (c : Cfg L K) (M : ℕ)
    (hphase : ∀ a ∈ c, a.phase.val ≤ 3)
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.bias = .zero)
    (hphi : (1000 : ℚ) * augmentedPhi j.val c ≤ M)
    (hdeep : 1250 * deepCount j.val c ≤ 3 * M)
    {r g : ℝ} (hg : 0 ≤ g) (hmin : (4 / 1250 : ℝ) ≤ (r - g) / 2)
    (hw : r * M ≤ (2 : ℝ) ^ j.val * (mixedAbsoluteMass c : ℝ))
    (hgap : |(2 : ℝ) ^ j.val * (prePhase4MassSum c : ℝ)| ≤ g * M) :
    ((r + g) / 2) * ((r - g) / 2 - 4 / 1250) * (M : ℝ) ^ 2 ≤
      (levelCount .pos j c : ℝ) * (levelCount .neg j c : ℝ) := by
  have hpq := outsideMass_nonneg .pos j c
  have hnq := outsideMass_nonneg .neg j c
  have hoq := outsideMass_allowance j hj c M hphase hcarrier hphi hdeep
  unfold outsideMass at hpq hnq hoq
  have hp : 0 ≤ (2 : ℝ) ^ j.val * (sideMass .pos c : ℝ) -
      (levelCount .pos j c : ℝ) := by
    exact_mod_cast hpq
  have hn : 0 ≤ (2 : ℝ) ^ j.val * (sideMass .neg c : ℝ) -
      (levelCount .neg j c : ℝ) := by
    exact_mod_cast hnq
  have ho :
      ((2 : ℝ) ^ j.val * (sideMass .pos c : ℝ) - levelCount .pos j c) +
        ((2 : ℝ) ^ j.val * (sideMass .neg c : ℝ) - levelCount .neg j c) ≤
      (4 / 1250 : ℝ) * M := by
    have h := (Rat.cast_le (K := ℝ)).2 hoq
    push_cast at h
    linarith only [h]
  have hadd := congrArg (fun x : ℚ => (x : ℝ)) (sideMass_add c)
  have hsub := congrArg (fun x : ℚ => (x : ℝ)) (sideMass_sub c)
  push_cast at hadd hsub
  apply product_floor_of_total_mass (by positivity) hg (by norm_num) hmin hp hn ho
  · rw [← hadd, mul_add] at hw
    exact hw
  · have heq :
        (2 : ℝ) ^ j.val * (sideMass .pos c : ℝ) -
            (2 : ℝ) ^ j.val * (sideMass .neg c : ℝ) =
          (2 : ℝ) ^ j.val * (prePhase4MassSum c : ℝ) := by
        rw [← hsub]
        ring
    rwa [heq]

/-- The minority target gives a current product floor even while the total
mass is changing. The signed-gap lower bound is used in the majority direction. -/
theorem product_floor_of_minority
    {a b A B M ξ g δ : ℝ} (hM : 0 ≤ M)
    (hg : 0 ≤ g) (hδ : 0 ≤ δ) (hξ : δ ≤ ξ)
    (hA : 0 ≤ a - A) (hB : 0 ≤ b - B)
    (hoff : (a - A) + (b - B) ≤ δ * M)
    (hminority : ξ * M ≤ b) (hgap : g * M ≤ a - b) :
    (ξ + g) * (ξ - δ) * M ^ 2 ≤ A * B := by
  have hgM := mul_nonneg hg hM
  have hδM := mul_nonneg hδ hM
  have hξM := mul_le_mul_of_nonneg_right hξ hM
  have hab : b ≤ a := by linarith only [hgM, hgap]
  have hδb : δ * M ≤ b := hξM.trans hminority
  have hmajor : (ξ + g) * M ≤ a := by
    nlinarith only [hminority, hgap]
  have hminor : (ξ - δ) * M ≤ b - δ * M := by
    nlinarith only [hminority]
  have hprod :
      ((ξ + g) * M) * ((ξ - δ) * M) ≤ a * (b - δ * M) :=
    mul_le_mul hmajor hminor
      (mul_nonneg (sub_nonneg.mpr hξ) hM)
      (by nlinarith only [hmajor, hgM, hξM, hδM])
  have hcurrent := cancellation_product_lower_of_outside_bound hab hδb
    hA hB hoff (by linarith : a - (a - A) ≤ A)
    (by linarith : b - (b - B) ≤ B)
  calc
    (ξ + g) * (ξ - δ) * M ^ 2 =
        ((ξ + g) * M) * ((ξ - δ) * M) := by ring
    _ ≤ a * (b - δ * M) := hprod
    _ ≤ A * B := hcurrent

theorem level_product_of_minority
    (σ : Sign) (j : Fin (L + 1)) (hj : 1 ≤ j.val)
    (c : Cfg L K) (M : ℕ)
    (hphase : ∀ a ∈ c, a.phase.val ≤ 3)
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.bias = .zero)
    (hphi : (1000 : ℚ) * augmentedPhi j.val c ≤ M)
    (hdeep : 1250 * deepCount j.val c ≤ 3 * M)
    {ξ g : ℝ} (hg : 0 ≤ g) (hξ : (4 / 1250 : ℝ) ≤ ξ)
    (hminority : ξ * M ≤
      (2 : ℝ) ^ j.val * (sideMass (oppositeSign σ) c : ℝ))
    (hgap : g * M ≤ (2 : ℝ) ^ j.val *
      ((sideMass σ c : ℝ) - (sideMass (oppositeSign σ) c : ℝ))) :
    (ξ + g) * (ξ - 4 / 1250) * (M : ℝ) ^ 2 ≤
      (levelCount .pos j c : ℝ) * (levelCount .neg j c : ℝ) := by
  have hmajorq := outsideMass_nonneg σ j c
  have hminorq := outsideMass_nonneg (oppositeSign σ) j c
  have houtq : outsideMass σ j c + outsideMass (oppositeSign σ) j c ≤
      (4 / 1250 : ℚ) * M := by
    have h := outsideMass_allowance j hj c M hphase hcarrier hphi hdeep
    cases σ
    · exact h
    · simpa only [oppositeSign, add_comm] using h
  unfold outsideMass at hmajorq hminorq houtq
  have hmajor : 0 ≤ (2 : ℝ) ^ j.val * (sideMass σ c : ℝ) -
      (levelCount σ j c : ℝ) := by exact_mod_cast hmajorq
  have hminor : 0 ≤ (2 : ℝ) ^ j.val * (sideMass (oppositeSign σ) c : ℝ) -
      (levelCount (oppositeSign σ) j c : ℝ) := by exact_mod_cast hminorq
  have hout :
      ((2 : ℝ) ^ j.val * (sideMass σ c : ℝ) - levelCount σ j c) +
        ((2 : ℝ) ^ j.val * (sideMass (oppositeSign σ) c : ℝ) -
          levelCount (oppositeSign σ) j c) ≤ (4 / 1250 : ℝ) * M := by
    have h := (Rat.cast_le (K := ℝ)).2 houtq
    push_cast at h
    linarith only [h]
  have hgap' : g * M ≤ (2 : ℝ) ^ j.val * (sideMass σ c : ℝ) -
      (2 : ℝ) ^ j.val * (sideMass (oppositeSign σ) c : ℝ) := by
    simpa only [mul_sub] using hgap
  have hp := product_floor_of_minority (by positivity : (0 : ℝ) ≤ M)
    hg (by norm_num : (0 : ℝ) ≤ 4 / 1250) hξ hmajor hminor hout
    hminority hgap'
  cases σ
  · exact hp
  · simpa only [oppositeSign, mul_comm] using hp

theorem countP_labelCfg (f : Fin m → AgentState L K)
    (P : AgentState L K → Prop) [DecidablePred P] :
    (labelCfg f).countP P = (Finset.univ.filter (fun i => P (f i))).card := by
  unfold labelCfg
  rw [Multiset.countP_map]
  rfl

/-- The physical labels and the multiset describe exactly the same count.
This also bridges the classical predicate instance used by labelCount. -/
theorem countP_trace_eq_labelCount {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (t : ℕ)
    (P : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 → Prop)
    [DecidablePred P] :
    (trace init ω t).countP P =
      labelCount init (fun i => P (labelsAt init ω t i)) := by
  classical
  rw [← labelsAt_config init ω t]
  change (labelCfg (labelsAt init ω t)).countP P = _
  rw [countP_labelCfg]
  unfold labelCount
  congr!

def DeepAt (h : ℕ) (a : AgentState L K) : Prop :=
  a.phase.val = 3 ∧ a.role = .main ∧
    ∃ σ j, a.bias = Bias.dyadic σ j ∧ h < j.val

open Classical in
theorem deepAtom_eq_indicator (h : ℕ) (a : AgentState L K) :
    deepAtom h a = if DeepAt h a then 1 else 0 := by
  classical
  by_cases hp : a.phase.val = 3 ∧ a.role = .main
  · cases hb : a.bias with
    | zero => simp [deepAtom, DeepAt, hp.1, hp.2, hb]
    | dyadic σ j =>
        by_cases hj : h < j.val <;>
          simp [deepAtom, DeepAt, hp.1, hp.2, hb, hj]
  · have hn : ¬ DeepAt h a := fun hs => hp ⟨hs.1, hs.2.1⟩
    simp only [deepAtom, if_neg hp, if_neg hn]

open Classical in
theorem deepCount_eq_countP (h : ℕ) (c : Cfg L K) :
    deepCount h c = c.countP (DeepAt h) := by
  classical
  induction c using Multiset.induction_on with
  | empty => simp [deepCount]
  | cons a c ih =>
      by_cases ha : DeepAt h a <;>
        simp [deepCount, deepAtom_eq_indicator, Multiset.countP_cons, ha] at ih ⊢ <;>
        omega

theorem deepCount_clockHistory {n : ℕ}
    {init : InputCfg n} {ω : InputLog n} {S T ρ v : ℕ}
    {w : ClockTimes init} (h : ClockHistory init ω S T ρ w)
    (hSv : S ≤ v) (hvρ : v < ρ) (k : ℕ) :
    deepCount k (trace init ω v) = deepBiasedMains init ω S v k := by
  classical
  rw [deepCount_eq_countP, countP_trace_eq_labelCount]
  unfold deepBiasedMains
  apply congrArg (labelCount init)
  funext i
  apply propext
  have hi : labelsAt init ω v i ∈ trace init ω v := by
    rw [← labelsAt_config init ω v]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  have hphase := (h.phase_range v hSv hvρ _ hi).2
  have hrole := h.roles_fixed v hSv hvρ i
  simp only [DeepAt, fixedRole, active, hrole]
  constructor
  · rintro ⟨hp, hr, hb⟩
    exact ⟨hr, by omega, hb⟩
  · rintro ⟨hr, hp, hb⟩
    exact ⟨by omega, hr, hb⟩

theorem levelCount_labelCfg (f : Fin m → AgentState L K)
    (σ : Sign) (j : Fin (L + 1)) :
    levelCount σ j (labelCfg f) = (levelSet f σ j).card := by
  classical
  unfold levelCount labelCfg levelSet
  rw [Multiset.countP_map]
  simp only [AtLevel, Finset.card_def, Finset.filter_val]

/-- The preceding floor is now expressed using exactly the two populations
in cancellation_conditional_law. -/
theorem labels_product_of_total_mass
    (f : Fin m → AgentState L K) (j : Fin (L + 1)) (hj : 1 ≤ j.val)
    (M : ℕ)
    (hphase : ∀ a ∈ labelCfg f, a.phase.val ≤ 3)
    (hcarrier : ∀ a ∈ labelCfg f, a.role ≠ .main → a.bias = .zero)
    (hphi : (1000 : ℚ) * augmentedPhi j.val (labelCfg f) ≤ M)
    (hdeep : 1250 * deepCount j.val (labelCfg f) ≤ 3 * M)
    {r g : ℝ} (hg : 0 ≤ g) (hmin : (4 / 1250 : ℝ) ≤ (r - g) / 2)
    (hw : r * M ≤ (2 : ℝ) ^ j.val * (mixedAbsoluteMass (labelCfg f) : ℝ))
    (hgap : |(2 : ℝ) ^ j.val * (prePhase4MassSum (labelCfg f) : ℝ)| ≤ g * M) :
    ((r + g) / 2) * ((r - g) / 2 - 4 / 1250) * (M : ℝ) ^ 2 ≤
      ((levelSet f .pos j).card : ℝ) * (levelSet f .neg j).card := by
  simpa only [levelCount_labelCfg] using
    level_product_of_total_mass j hj (labelCfg f) M
      hphase hcarrier hphi hdeep hg hmin hw hgap

theorem labels_product_of_minority
    (σ : Sign) (f : Fin m → AgentState L K)
    (j : Fin (L + 1)) (hj : 1 ≤ j.val) (M : ℕ)
    (hphase : ∀ a ∈ labelCfg f, a.phase.val ≤ 3)
    (hcarrier : ∀ a ∈ labelCfg f, a.role ≠ .main → a.bias = .zero)
    (hphi : (1000 : ℚ) * augmentedPhi j.val (labelCfg f) ≤ M)
    (hdeep : 1250 * deepCount j.val (labelCfg f) ≤ 3 * M)
    {ξ g : ℝ} (hg : 0 ≤ g) (hξ : (4 / 1250 : ℝ) ≤ ξ)
    (hminority : ξ * M ≤
      (2 : ℝ) ^ j.val * (sideMass (oppositeSign σ) (labelCfg f) : ℝ))
    (hgap : g * M ≤ (2 : ℝ) ^ j.val *
      ((sideMass σ (labelCfg f) : ℝ) -
        (sideMass (oppositeSign σ) (labelCfg f) : ℝ))) :
    (ξ + g) * (ξ - 4 / 1250) * (M : ℝ) ^ 2 ≤
      ((levelSet f .pos j).card : ℝ) * (levelSet f .neg j).card := by
  simpa only [levelCount_labelCfg] using
    level_product_of_minority σ j hj (labelCfg f) M
      hphase hcarrier hphi hdeep hg hξ hminority hgap


end Ripple.PopulationProtocol.ExactMajority.AveragingLiveProduct

end
