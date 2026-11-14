-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingPotentialDrift.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingPotentialService
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoHeightMoments
import Ripple.PopulationProtocol.ExactMajority.Probability.WeightedDriftDropSum

/-!
# Actual averaging drift from a weighted ready-zero rectangle

Both orientations are counted. Pending nonzero Mains use the same active
ready-zero partners as active shallow Mains: their activation already pays
half their double pending weight. No future gate-success event is conditioned on.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.AveragingPotentialDrift

open TimeTheorem AveragingPotentialService AveragingIntegerPotential

section Rectangle

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

open Classical in
theorem sumOf_indicator_eq_count (c : Config Λ) (P : Λ → Prop) :
    Config.sumOf (fun a => if P a then (1 : ℝ≥0∞) else 0) c = c.countP P := by
  induction c using Multiset.induction_on with
  | empty => simp [Config.sumOf]
  | cons a c ih =>
      simp only [Config.sumOf] at ih
      by_cases ha : P a <;>
        simp [Config.sumOf, Multiset.countP_cons, ha, ih, add_comm]

open Classical in
theorem weighted_partner_count (c : Config Λ) (P : Λ → Prop)
    (g : Λ → ℝ≥0∞) (hg : ∀ a, P a → g a = 0) :
    (∑ p : Λ × Λ,
      (if P p.2 then g p.1 else 0) *
        (c.interactionCount p.1 p.2 : ℝ≥0∞)) =
      (c.countP P : ℝ≥0∞) * Config.sumOf g c := by
  have hterm (a b : Λ) :
      (if P b then g a else 0) * (c.interactionCount a b : ℝ≥0∞) =
        (g a * (c.count a : ℝ≥0∞)) *
          (if P b then (c.count b : ℝ≥0∞) else 0) := by
    by_cases hb : P b
    · by_cases hab : a = b
      · subst b
        simp [hb, hg a hb]
      · simp only [if_pos hb, Config.interactionCount, if_neg hab, Nat.cast_mul]
        ring
    · simp [hb]
  have hcount :
      (∑ b : Λ, if P b then (c.count b : ℝ≥0∞) else 0) = c.countP P := by
    have hsum := PhaseTwoHeight.sumOf_eq_sum_count c
      (fun b => if P b then (1 : ℝ≥0∞) else 0)
    rw [sumOf_indicator_eq_count] at hsum
    symm
    refine hsum.trans ?_
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : P b <;> simp [hb]
  rw [show (Finset.univ : Finset (Λ × Λ)) = Finset.univ ×ˢ Finset.univ
    from Finset.univ_product_univ.symm, Finset.sum_product]
  calc
    (∑ a : Λ, ∑ b : Λ,
        (if P b then g a else 0) * (c.interactionCount a b : ℝ≥0∞)) =
        ∑ a : Λ, (g a * (c.count a : ℝ≥0∞)) * (c.countP P : ℝ≥0∞) := by
          apply Finset.sum_congr rfl
          intro a _
          simp_rw [hterm a]
          rw [← Finset.mul_sum, hcount]
    _ = (c.countP P : ℝ≥0∞) * Config.sumOf g c := by
      rw [← Finset.sum_mul, ← PhaseTwoHeight.sumOf_eq_sum_count]
      ring

open Classical in
theorem weighted_partner_probability (c : Config Λ) (P : Λ → Prop)
    (g : Λ → ℝ≥0∞) (hg : ∀ a, P a → g a = 0) :
    (∑ p : Λ × Λ,
      (if P p.2 then g p.1 else 0) * c.interactionProb p.1 p.2) =
      ((c.countP P : ℝ≥0∞) / c.totalPairs) * Config.sumOf g c := by
  simp only [Config.interactionProb, div_eq_mul_inv]
  calc
    (∑ p : Λ × Λ,
        (if P p.2 then g p.1 else 0) *
          ((c.interactionCount p.1 p.2 : ℝ≥0∞) *
            (c.totalPairs : ℝ≥0∞)⁻¹)) =
        (∑ p : Λ × Λ, (if P p.2 then g p.1 else 0) *
          (c.interactionCount p.1 p.2 : ℝ≥0∞)) *
            (c.totalPairs : ℝ≥0∞)⁻¹ := by
              simp only [mul_assoc, Finset.sum_mul]
    _ = ((c.countP P : ℝ≥0∞) * (c.totalPairs : ℝ≥0∞)⁻¹) *
        Config.sumOf g c := by
      rw [weighted_partner_count c P g hg]
      ring

open Classical in
theorem weighted_partner_probability_reverse (c : Config Λ) (P : Λ → Prop)
    (g : Λ → ℝ≥0∞) (hg : ∀ a, P a → g a = 0) :
    (∑ p : Λ × Λ,
      (if P p.1 then g p.2 else 0) * c.interactionProb p.1 p.2) =
      ((c.countP P : ℝ≥0∞) / c.totalPairs) * Config.sumOf g c := by
  rw [← Equiv.sum_comp (Equiv.prodComm Λ Λ)
    (fun p : Λ × Λ =>
      (if P p.1 then g p.2 else 0) * c.interactionProb p.1 p.2)]
  have hswap (a b : Λ) : c.interactionProb a b = c.interactionProb b a := by
    unfold Config.interactionProb
    rw [PhaseTwoHeight.interactionCount_swap]
  simpa only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, hswap] using
    weighted_partner_probability c P g hg

open Classical in
theorem weighted_half_service_probability (c : Config Λ) (P : Λ → Prop)
    (g : Λ → ℝ≥0∞) (hg : ∀ a, P a → g a = 0) :
    (∑ p : Λ × Λ,
      (((if P p.2 then g p.1 else 0) +
        (if P p.1 then g p.2 else 0)) / 2) *
          c.interactionProb p.1 p.2) =
      ((c.countP P : ℝ≥0∞) / c.totalPairs) * Config.sumOf g c := by
  calc
    (∑ p : Λ × Λ,
        (((if P p.2 then g p.1 else 0) +
          (if P p.1 then g p.2 else 0)) / 2) *
            c.interactionProb p.1 p.2) =
        ((∑ p : Λ × Λ,
          (if P p.2 then g p.1 else 0) * c.interactionProb p.1 p.2) +
        (∑ p : Λ × Λ,
          (if P p.1 then g p.2 else 0) * c.interactionProb p.1 p.2)) / 2 := by
            simp only [div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro p _
            ring
    _ = ((c.countP P : ℝ≥0∞) / c.totalPairs) * Config.sumOf g c := by
      rw [weighted_partner_probability c P g hg,
        weighted_partner_probability_reverse c P g hg,
        ENNReal.add_div, ENNReal.add_halves]

end Rectangle

/-- Positive ordered-pair multiplicity supplies the physical applicability
certificate, including the diagonal requirement of two occurrences. -/
theorem applicable_of_pos_interactionCount {L K : ℕ}
    (c : Cfg L K) (s t : AgentState L K)
    (h : 0 < c.interactionCount s t) : Protocol.Applicable c s t := by
  classical
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
      have hzero : Multiset.count s c * (Multiset.count s c - 1) = 0 := by
        rcases Nat.eq_zero_or_pos (Multiset.count s c) with hz | hp
        · simp [hz]
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

theorem interactionProb_zero_of_not_applicable {L K : ℕ}
    (c : Cfg L K) (s t : AgentState L K) (h : ¬ Protocol.Applicable c s t) :
    c.interactionProb s t = 0 := by
  have hz : c.interactionCount s t = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hp
    exact h (applicable_of_pos_interactionCount c s t hp)
  simp [Config.interactionProb, hz]

variable {L : ℕ}

open Classical in
def readyZeroCount (h : ℕ) (c : Cfg L 256) : ℕ :=
  c.countP (ReadyZero h)

def readyRate (h : ℕ) (c : Cfg L 256) : ℝ≥0∞ :=
  (readyZeroCount h c : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞)

theorem phiNat_cast_sum (h : ℕ) (c : Cfg L 256) :
    Config.sumOf (fun a => (augmentedAgentPhiNat h a : ℝ≥0∞)) c =
      (augmentedPhiNat h c : ℝ≥0∞) := by
  induction c using Multiset.induction_on with
  | empty => simp [Config.sumOf, augmentedPhiNat]
  | cons a c ih =>
      simp only [Config.sumOf, augmentedPhiNat, Multiset.map_cons,
        Multiset.sum_cons, Nat.cast_add] at ih ⊢
      rw [ih]

theorem weighted_phiNat_service (h : ℕ) (hh : 1 ≤ h) (c : Cfg L 256)
    (hc : PotentialDomain c) (s t : AgentState L 256) :
    ((pairService h s t : ℝ≥0∞) / 2) * c.interactionProb s t ≤
      ((augmentedPhiNat h c : ℝ≥0∞) -
        (augmentedPhiNat h
          (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) : ℝ≥0∞)) *
        c.interactionProb s t := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hservice := phiNat_step_service h hh c hc s t happ
    have hmono := phiNat_step_le h hh c hc s t
    have hn : pairService h s t ≤
        2 * (augmentedPhiNat h c -
          augmentedPhiNat h (Protocol.stepOrSelf (NonuniformMajority L 256) c s t)) := by
      omega
    have he : (pairService h s t : ℝ≥0∞) / 2 ≤
        (augmentedPhiNat h c : ℝ≥0∞) -
          (augmentedPhiNat h
            (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) : ℝ≥0∞) := by
      apply (ENNReal.div_le_iff' (by norm_num) (by norm_num)).2
      have hcast :
          (pairService h s t : ℝ≥0∞) ≤
            ((2 * (augmentedPhiNat h c -
              augmentedPhiNat h
                (Protocol.stepOrSelf (NonuniformMajority L 256) c s t)) : ℕ) : ℝ≥0∞) :=
        by exact_mod_cast hn
      simpa only [Nat.cast_mul, Nat.cast_ofNat, ENNReal.natCast_sub] using hcast
    exact mul_le_mul_right' he _
  · simp only [interactionProb_zero_of_not_applicable c s t happ,
      mul_zero, le_refl]

theorem phiNat_weighted_drop (h : ℕ) (hh : 1 ≤ h)
    (c : Cfg L 256) (hc : PotentialDomain c) :
    readyRate h c * augmentedPhiNat h c ≤
      WeightedDriftDropSum.weightedDropSum (NonuniformMajority L 256)
        (augmentedPhiNat h) c := by
  classical
  have hsum := weighted_half_service_probability c (ReadyZero h)
    (fun a => (augmentedAgentPhiNat h a : ℝ≥0∞))
    (fun a ha => by simp only [ready_phiNat_zero h a ha, Nat.cast_zero])
  have hservice (s t : AgentState L 256) :
      (pairService h s t : ℝ≥0∞) =
        (if ReadyZero h t then (augmentedAgentPhiNat h s : ℝ≥0∞) else 0) +
          (if ReadyZero h s then (augmentedAgentPhiNat h t : ℝ≥0∞) else 0) := by
    by_cases hs : ReadyZero h s <;> by_cases ht : ReadyZero h t <;>
      simp [pairService, hs, ht]
  have heq :
      (∑ p : AgentState L 256 × AgentState L 256,
        ((pairService h p.1 p.2 : ℝ≥0∞) / 2) *
          c.interactionProb p.1 p.2) = readyRate h c * augmentedPhiNat h c := by
    simp only [hservice]
    simpa only [readyRate, readyZeroCount, phiNat_cast_sum] using hsum
  rw [← heq]
  unfold WeightedDriftDropSum.weightedDropSum
  exact Finset.sum_le_sum fun p _ => weighted_phiNat_service h hh c hc p.1 p.2

theorem readyRate_ne_top (h : ℕ) (c : Cfg L 256) (hc : 2 ≤ c.card) :
    readyRate h c ≠ ⊤ := by
  have hpos : 0 < c.totalPairs := by
    unfold Config.totalPairs
    exact Nat.mul_pos (by omega) (by omega)
  exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (by exact_mod_cast (Nat.ne_of_gt hpos))

theorem readyRate_le_one (h : ℕ) (c : Cfg L 256) (hc : 2 ≤ c.card) :
    readyRate h c ≤ 1 := by
  classical
  have hp : 0 < c.totalPairs := by
    unfold Config.totalPairs
    exact Nat.mul_pos (by omega) (by omega)
  have hcount : readyZeroCount h c ≤ c.totalPairs := by
    calc
      readyZeroCount h c ≤ c.card := Multiset.countP_le_card _ _
      _ = c.card * 1 := by simp
      _ ≤ c.card * (c.card - 1) := Nat.mul_le_mul_left _ (by omega)
      _ = c.totalPairs := rfl
  unfold readyRate
  apply (ENNReal.div_le_iff (by exact_mod_cast (Nat.ne_of_gt hp))
    (ENNReal.natCast_ne_top _)).2
  simpa only [one_mul] using (show (readyZeroCount h c : ℝ≥0∞) ≤
    (c.totalPairs : ℝ≥0∞) by exact_mod_cast hcount)

/-- Concrete full one-step drift. The next configuration is not killed or
restricted by any future gate. -/
theorem augmentedPhiNat_kernel_drift (h : ℕ) (hh : 1 ≤ h)
    (c : Cfg L 256) (hn : 2 ≤ c.card) (hc : PotentialDomain c) :
    (∫⁻ c', (augmentedPhiNat h c' : ℝ≥0∞)
      ∂(NonuniformMajority L 256).transitionKernel c) ≤
        (1 - readyRate h c) * augmentedPhiNat h c :=
  WeightedDriftDropSum.weighted_dyadic_mass_drift_of_dropSum
    (NonuniformMajority L 256) (augmentedPhiNat h) c hn (readyRate h c)
    (readyRate_ne_top h c hn) (fun p => phiNat_step_le h hh c hc p.1 p.2)
    (phiNat_weighted_drop h hh c hc)

end Ripple.PopulationProtocol.ExactMajority.AveragingPotentialDrift

end
