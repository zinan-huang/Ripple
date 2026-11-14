-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingMassCountTransport.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingFirstBranchShape
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingShallowTransport
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase5To6FuelProducer

/-!
# Lemma 7.2 mass/count transport to the completed sampling snapshot

The upper-tail debt is the natural-valued `massAboveScaled`.  It is
nonincreasing in every actual Phase-3/4/5 interaction: the Phase-3 theorem
handles a 3/3 pair, while `transition_freeze_fields` makes the observable
literally invariant once the maximum phase is at least four.

The minority exact-level class is bounded through the already compiled
`scaledShallowPositive_seed_mono` theorem.  No future-success conditioning and
no next-level implication occur here.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingMassCountTransport

open TimeTheorem PairLog
open StageEventSpec
open LateStrengthening
open LateF6Acceptance LateF6OriginalLaw
open LateSamplingFirstBranchShape
open LateSamplingShallowTransport
open AveragingCreditTransitions LateSamplingSeedReceipt

variable {L K n : ℕ}

/-! ## Natural upper-tail transport through the actual mixed window -/

/-- Every actual Phase-3/4/5 pair is nonincreasing for the natural scaled
upper-tail mass. -/
theorem transition_agentMassAboveScaledW_pair_le_of_window
    (ell : ℕ) (s t : AgentState L K)
    (hs : Window s) (ht : Window t) :
    Lemma615MassAbove.agentMassAboveScaledW
          (L := L) (K := K) ell (Transition L K s t).1 +
        Lemma615MassAbove.agentMassAboveScaledW
          (L := L) (K := K) ell (Transition L K s t).2 ≤
      Lemma615MassAbove.agentMassAboveScaledW
          (L := L) (K := K) ell s +
        Lemma615MassAbove.agentMassAboveScaledW
          (L := L) (K := K) ell t := by
  by_cases hfreeze : 4 ≤ max s.phase.val t.phase.val
  · have hfields := transition_freeze_fields s t hs ht hfreeze
    unfold Lemma615MassAbove.agentMassAboveScaledW
    rw [hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2]
  · have hsphase : s.phase.val = 3 := by
      have := hs.1
      have := ht.1
      have hsmax := le_max_left s.phase.val t.phase.val
      omega
    have htphase : t.phase.val = 3 := by
      have := hs.1
      have := ht.1
      have htmax := le_max_right s.phase.val t.phase.val
      omega
    exact
      Phase5To6FuelProducer.Transition_agentMassAboveScaledW_pair_le_of_three_three
          (L := L) (K := K) ell s t hsphase htphase

/-- Additive form for replacing one selected pair. -/
theorem massAboveScaled_add_pair
    (ell : ℕ) (c : Cfg L K) (s t : AgentState L K) :
    Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) ell (c + {s, t}) =
      Lemma615MassAbove.massAboveScaled
          (L := L) (K := K) ell c +
        (Lemma615MassAbove.agentMassAboveScaledW
            (L := L) (K := K) ell s +
          Lemma615MassAbove.agentMassAboveScaledW
            (L := L) (K := K) ell t) := by
  simp [Lemma615MassAbove.massAboveScaled,
    Multiset.map_add, Multiset.sum_add,
    add_assoc, add_left_comm, add_comm]

/-- Configuration-level one-step transport. -/
theorem massAboveScaled_stepOrSelf_le_of_window
    (ell : ℕ) (c : Cfg L K) (s t : AgentState L K)
    (hwindow : ∀ x ∈ c, Window x) :
    Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) ell
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ≤
      Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) ell c := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hstep :
        Protocol.stepOrSelf (NonuniformMajority L K) c s t =
          c - {s, t} +
            {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hpair :=
      transition_agentMassAboveScaledW_pair_le_of_window
        (L := L) (K := K) ell s t (hwindow s hs) (hwindow t ht)
    have hsplit :
        c = c - {s, t} + ({s, t} : Multiset (AgentState L K)) := by
      rw [Multiset.sub_add_cancel
        (show ({s, t} : Multiset (AgentState L K)) ≤ c from happ)]
    rw [hstep, massAboveScaled_add_pair]
    conv_rhs => rw [hsplit]
    rw [massAboveScaled_add_pair]
    exact add_le_add le_rfl hpair
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- Draw-level form, including the no-draw identity branch. -/
theorem massAboveScaled_draw_le_of_window
    (ell : ℕ) (c : Cfg L K) (d : Draw L K)
    (hwindow : ∀ x ∈ c, Window x) :
    Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) ell (applyDraw c d) ≤
      Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) ell c := by
  cases d with
  | none => exact le_rfl
  | some pair =>
      exact massAboveScaled_stepOrSelf_le_of_window
        ell c pair.1.1 pair.2.1 hwindow

/-- Trace transport through any interval whose source configurations lie in
`Window`. -/
theorem massAboveScaled_trace_le_of_window
    (ell : ℕ) (init : Cfg L K) (ω : Ω L K)
    (s t : ℕ) (hst : s ≤ t)
    (hwindow : ∀ u, s ≤ u → u < t →
      ∀ x ∈ trace init ω u, Window x) :
    Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) ell (trace init ω t) ≤
      Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) ell (trace init ω s) := by
  revert hwindow
  induction t, hst using Nat.le_induction with
  | base =>
      intro _
      exact le_rfl
  | succ t hst ih =>
      intro hwindow
      have hprevious :=
        ih (fun u hsu hut => hwindow u hsu (by omega))
      have hnext :
          Lemma615MassAbove.massAboveScaled
              (L := L) (K := K) ell (trace init ω (t + 1)) ≤
            Lemma615MassAbove.massAboveScaled
              (L := L) (K := K) ell (trace init ω t) := by
        rw [TimeTheorem.trace_succ]
        exact massAboveScaled_draw_le_of_window
          ell (trace init ω t) (ω (t + 1))
          (hwindow t hst (by omega))
      exact hnext.trans hprevious

/-! ## Identification with the N16 strict-shallow budget -/

private theorem scaledWeight_eq_scaledZpow_for_mass
    (ell j : ℕ) :
    scaledWeight ell j =
      (2 : ℚ) ^ ell * (2 : ℚ) ^ (-(j : ℤ)) := by
  simp [scaledWeight, zpow_neg, zpow_natCast, div_eq_mul_inv]

private theorem cast_pow_sub_eq_scaledZpow_for_mass
    (ell j : ℕ) (hj : j < ell) :
    ((2 ^ (ell - j) : ℕ) : ℚ) =
      (2 : ℚ) ^ ell * (2 : ℚ) ^ (-(j : ℤ)) := by
  have hnat := shallowWeight_eq_nat ell j
  have hscaled :
      scaledWeight ell j = ((2 ^ (ell - j) : ℕ) : ℚ) := by
    simpa [shallowWeight, shallowWeightNat, hj.le] using hnat
  exact hscaled.symm.trans (scaledWeight_eq_scaledZpow_for_mass ell j)

private theorem agentMassAboveScaledW_cast_eq_shallowAtom
    (ell : ℕ) (x : AgentState L K) :
    ((Lemma615MassAbove.agentMassAboveScaledW
        (L := L) (K := K) ell x : ℕ) : ℚ) =
      (2 : ℚ) ^ ell *
        (if x.role = .main then
          match x.bias with
          | .zero => 0
          | .dyadic _ j =>
              if j.val < ell then
                (2 : ℚ) ^ (-(j.val : ℤ))
              else 0
        else 0) := by
  classical
  by_cases hm : x.role = .main
  · cases hb : x.bias with
    | zero =>
        simp [Lemma615MassAbove.agentMassAboveScaledW,
          Lemma615MassAbove.biasMassAboveScaledW, hm, hb]
    | dyadic tau j =>
        by_cases hj : j.val < ell
        · simpa [Lemma615MassAbove.agentMassAboveScaledW,
            Lemma615MassAbove.biasMassAboveScaledW, hm, hb, hj] using
            cast_pow_sub_eq_scaledZpow_for_mass ell j.val hj
        · simp [Lemma615MassAbove.agentMassAboveScaledW,
            Lemma615MassAbove.biasMassAboveScaledW, hm, hb, hj]
  · simp [Lemma615MassAbove.agentMassAboveScaledW, hm]

/-- The natural upper-tail observable is exactly the N16 rational
strict-shallow mass scaled by `2^ell`. -/
theorem massAboveScaled_cast_eq_scaledShallowMass
    (ell : ℕ) (c : InputCfg n) :
    (Lemma615MassAbove.massAboveScaled
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell c : ℚ) =
      (2 : ℚ) ^ ell * shallowMass ell c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [Lemma615MassAbove.massAboveScaled, shallowMass]
  | cons x c ih =>
      simp only [Lemma615MassAbove.massAboveScaled, shallowMass,
        Multiset.map_cons, Multiset.sum_cons, Nat.cast_add] at ih ⊢
      rw [ih, mul_add]
      congr 1
      by_cases hm : x.role = .main
      · cases hb : x.bias with
        | zero =>
            simp [Lemma615MassAbove.agentMassAboveScaledW,
              Lemma615MassAbove.biasMassAboveScaledW, hm, hb]
        | dyadic tau j =>
            by_cases hj : j.val < ell
            · simpa [Lemma615MassAbove.agentMassAboveScaledW,
                Lemma615MassAbove.biasMassAboveScaledW, hm, hb, hj] using
                cast_pow_sub_eq_scaledZpow_for_mass ell j.val hj
            · simp [Lemma615MassAbove.agentMassAboveScaledW,
                Lemma615MassAbove.biasMassAboveScaledW, hm, hb, hj]
      · simp [Lemma615MassAbove.agentMassAboveScaledW, hm]

/-- Real cap on the completed upper-tail debt, before integer rounding. -/
theorem massAboveScaled_cast_le_at_observed
    {init : InputCfg n} {ω : InputLog n}
    {a four u m ell : ℕ} {sigma : Sign}
    (hpath : Prefix init ω a four u)
    (hseed : LateSamplingSeedReceipt init m ell sigma
      (trace init ω four)) :
    (Lemma615MassAbove.massAboveScaled
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        ell (trace init ω u) : ℝ) ≤
      (1 / 500 : ℝ) * m := by
  have hmono :=
    massAboveScaled_trace_le_of_window
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell init ω four u hpath.observed
      (fun r hfourr hru x hx =>
        hpath.window r
          (hpath.start_order.trans hfourr)
          (Nat.le_of_lt hru) x hx)
  have hseedQ :
      (Lemma615MassAbove.massAboveScaled
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          ell (trace init ω four) : ℚ) ≤
        (1 / 500 : ℚ) * m := by
    rw [massAboveScaled_cast_eq_scaledShallowMass]
    nlinarith only [hseed.shallow]
  have hmonoQ :
      (Lemma615MassAbove.massAboveScaled
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          ell (trace init ω u) : ℚ) ≤
        Lemma615MassAbove.massAboveScaled
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          ell (trace init ω four) := by
    exact_mod_cast hmono
  have hcapQ := hmonoQ.trans hseedQ
  have hcapR := (Rat.cast_le (K := ℝ)).mpr hcapQ
  push_cast at hcapR
  exact hcapR

/-- Natural cap on the completed upper-tail debt. -/
theorem massAboveScaled_le_natCap_at_observed
    {init : InputCfg n} {ω : InputLog n}
    {a four u m ell Btail : ℕ} {sigma : Sign} {M : ℝ}
    (hpath : Prefix init ω a four u)
    (hseed : LateSamplingSeedReceipt init m ell sigma
      (trace init ω four))
    (hM : (m : ℝ) = M)
    (hround : (1 / 500 : ℝ) * M < (Btail + 1 : ℕ)) :
    Lemma615MassAbove.massAboveScaled
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        ell (trace init ω u) ≤ Btail := by
  have hcast := massAboveScaled_cast_le_at_observed hpath hseed
  rw [hM] at hcast
  have hlt := hcast.trans_lt hround
  have hnat :
      Lemma615MassAbove.massAboveScaled
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          ell (trace init ω u) < Btail + 1 := by
    exact_mod_cast hlt
  omega

/-! ## Minority exact-level cap -/

private theorem winningScaledAtom_sum_for_mass
    (sigma : Sign) (ell : ℕ) (c : InputCfg n) :
    Config.sumOf (winningScaledAtom sigma ell) c =
      (2 : ℚ) ^ ell * signMass sigma c := by
  classical
  induction c using Multiset.induction_on with
  | empty =>
      simp [Config.sumOf, signMass]
  | cons x c ih =>
      simp only [Config.sumOf, signMass, Multiset.map_cons,
        Multiset.sum_cons] at ih ⊢
      rw [ih, mul_add]
      congr 1
      by_cases hm : x.role = .main
      · cases hb : x.bias with
        | zero => simp [winningScaledAtom, hm, hb]
        | dyadic tau j =>
            by_cases htau : tau = sigma
            · simp [winningScaledAtom, hm, hb, htau,
                scaledWeight_eq_scaledZpow_for_mass]
            · simp [winningScaledAtom, hm, hb, htau]
      · simp [winningScaledAtom, hm]

private theorem boundedWinningScaledAtom_sum_for_mass
    (sigma : Sign) (ell : ℕ) (c : InputCfg n) :
    Config.sumOf (boundedWinningScaledAtom sigma ell) c =
      scaledShallowPositive sigma ell c := by
  classical
  induction c using Multiset.induction_on with
  | empty =>
      simp [Config.sumOf, scaledShallowPositive]
  | cons x c ih =>
      simp only [Config.sumOf, scaledShallowPositive,
        Multiset.map_cons, Multiset.sum_cons] at ih ⊢
      rw [ih, mul_add]
      congr 1
      by_cases hm : x.role = .main
      · cases hb : x.bias with
        | zero => simp [boundedWinningScaledAtom, hm, hb]
        | dyadic tau j =>
            by_cases htau : tau = sigma
            · by_cases hj : j.val ≤ ell
              · simp [boundedWinningScaledAtom, hm, hb, htau, hj,
                  scaledWeight_eq_scaledZpow_for_mass]
              · simp [boundedWinningScaledAtom, hm, hb, htau, hj]
            · simp [boundedWinningScaledAtom, hm, hb, htau]
      · simp [boundedWinningScaledAtom, hm]

private theorem sumOf_le_sumOf_for_mass
    {alpha : Type*} (f g : alpha → ℚ) (c : Multiset alpha)
    (h : ∀ x ∈ c, f x ≤ g x) :
    Config.sumOf f c ≤ Config.sumOf g c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [Config.sumOf]
  | cons x c ih =>
      have hx := h x (Multiset.mem_cons_self x c)
      have hc := ih (fun y hy => h y (Multiset.mem_cons_of_mem hy))
      simp only [Config.sumOf, Multiset.map_cons,
        Multiset.sum_cons] at hx hc ⊢
      linarith

private theorem boundedWinningScaledAtom_le_winningScaledAtom_for_mass
    (sigma : Sign) (ell : ℕ) (x : AgentState L K) :
    boundedWinningScaledAtom sigma ell x ≤
      winningScaledAtom sigma ell x := by
  classical
  by_cases hm : x.role = .main
  · cases hb : x.bias with
    | zero =>
        simp [boundedWinningScaledAtom, winningScaledAtom, hm, hb]
    | dyadic tau j =>
        by_cases htau : tau = sigma
        · by_cases hj : j.val ≤ ell
          · simp [boundedWinningScaledAtom, winningScaledAtom,
              hm, hb, htau, hj]
          · have hw := scaledWeight_nonneg ell j.val
            simp [boundedWinningScaledAtom, winningScaledAtom,
              hm, hb, htau, hj, hw]
        · simp [boundedWinningScaledAtom, winningScaledAtom,
            hm, hb, htau]
  · simp [boundedWinningScaledAtom, winningScaledAtom, hm]

/-- Truncating a same-sign mass at `ell` can only decrease the complete
same-sign mass. -/
theorem scaledShallowPositive_le_scaledSignMass
    (sigma : Sign) (ell : ℕ) (c : InputCfg n) :
    scaledShallowPositive sigma ell c ≤
      (2 : ℚ) ^ ell * signMass sigma c := by
  rw [← boundedWinningScaledAtom_sum_for_mass,
    ← winningScaledAtom_sum_for_mass]
  exact sumOf_le_sumOf_for_mass
    (boundedWinningScaledAtom sigma ell)
    (winningScaledAtom sigma ell) c
    (fun x _ =>
      boundedWinningScaledAtom_le_winningScaledAtom_for_mass
        sigma ell x)

/-- The width-zero band count is exactly the public Phase-5 biased-Main class
count. -/
theorem exactBandCount_eq_biasedMainClassU
    (sigma : Sign)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (c : InputCfg n) :
    bandCount sigma ell.val 0 c =
      Phase5Convergence.biasedMainClassU
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        sigma ell c := by
  classical
  unfold bandCount Phase5Convergence.biasedMainClassU
  apply Multiset.countP_congr rfl
  intro x _
  apply propext
  constructor
  · rintro ⟨hm, j, hb, hlo, hhi⟩
    have hjval : j.val = ell.val := by omega
    have hj : j = ell := Fin.ext hjval
    subst j
    exact ⟨hm, hb⟩
  · rintro ⟨hm, hb⟩
    exact ⟨hm, ell, hb, le_rfl, by omega⟩

@[simp]
theorem oppositeSign_eq_minoritySignOfMajority (sigma : Sign) :
    oppositeSign sigma = Phase3Post3.minoritySignOfMajority sigma := by
  cases sigma <;> rfl

/-- Real cap on the minority-sign exact-level class at the completed
snapshot. -/
theorem minorityClassU_cast_le_at_observed
    {init : InputCfg n} {ω : InputLog n}
    {a four u m : ℕ}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (sigma : Sign)
    (hpath : Prefix init ω a four u)
    (hseed : LateSamplingSeedReceipt init m ell.val sigma
      (trace init ω four)) :
    (Phase5Convergence.biasedMainClassU
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        (Phase3Post3.minoritySignOfMajority sigma) ell
        (trace init ω u) : ℝ) ≤
      (1 / 250 : ℝ) * m := by
  have hband :
      (Phase5Convergence.biasedMainClassU
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          (Phase3Post3.minoritySignOfMajority sigma) ell
          (trace init ω u) : ℚ) ≤
        scaledShallowPositive (oppositeSign sigma) ell.val
          (trace init ω u) := by
    have h := bandCount_exact_le_scaledShallowPositive
      (oppositeSign sigma) ell.val (trace init ω u)
    rw [exactBandCount_eq_biasedMainClassU
      (sigma := oppositeSign sigma) (ell := ell)] at h
    simpa using h
  have htransport :=
    scaledShallowPositive_seed_mono
      (σ := oppositeSign sigma) (ell := ell.val)
      hpath hpath.observed le_rfl
  have hseedMass :=
    scaledShallowPositive_le_scaledSignMass
      (oppositeSign sigma) ell.val (trace init ω four)
  have hcombined := hband.trans (htransport.trans hseedMass)
  have hcapQ :
      (Phase5Convergence.biasedMainClassU
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          (Phase3Post3.minoritySignOfMajority sigma) ell
          (trace init ω u) : ℚ) ≤
        (1 / 250 : ℚ) * m := by
    nlinarith only [hcombined, hseed.minority]
  have hcapR := (Rat.cast_le (K := ℝ)).mpr hcapQ
  push_cast at hcapR
  exact hcapR

/-- Natural cap on the minority exact-level class. -/
theorem minorityClassU_le_natCap_at_observed
    {init : InputCfg n} {ω : InputLog n}
    {a four u m Bminority : ℕ}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (sigma : Sign) {M : ℝ}
    (hpath : Prefix init ω a four u)
    (hseed : LateSamplingSeedReceipt init m ell.val sigma
      (trace init ω four))
    (hM : (m : ℝ) = M)
    (hround : (1 / 250 : ℝ) * M < (Bminority + 1 : ℕ)) :
    Phase5Convergence.biasedMainClassU
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        (Phase3Post3.minoritySignOfMajority sigma) ell
        (trace init ω u) ≤ Bminority := by
  have hcast :=
    minorityClassU_cast_le_at_observed ell sigma hpath hseed
  rw [hM] at hcast
  have hlt := hcast.trans_lt hround
  have hnat :
      Phase5Convergence.biasedMainClassU
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          (Phase3Post3.minoritySignOfMajority sigma) ell
          (trace init ω u) < Bminority + 1 := by
    exact_mod_cast hlt
  omega

/-!
THEOREM LIST
* `transition_agentMassAboveScaledW_pair_le_of_window`
* `massAboveScaled_add_pair`
* `massAboveScaled_stepOrSelf_le_of_window`
* `massAboveScaled_draw_le_of_window`
* `massAboveScaled_trace_le_of_window`
* `massAboveScaled_cast_eq_scaledShallowMass`
* `massAboveScaled_cast_le_at_observed`
* `massAboveScaled_le_natCap_at_observed`
* `scaledShallowPositive_le_scaledSignMass`
* `exactBandCount_eq_biasedMainClassU`
* `oppositeSign_eq_minoritySignOfMajority`
* `minorityClassU_cast_le_at_observed`
* `minorityClassU_le_natCap_at_observed`

CLOSES
* Natural upper-tail transport from the genuine Phase-4 seed to completion.
* Conversion of the N16 `.002 M` strict-shallow receipt into the natural
  `massAboveScaled` cap.
* Transport and rounding of the N16 minority exact-level cap.
* The deterministic inputs consumed by `Lemma72MassCountBounds.of_paper_caps`.

UNFINISHED
* The numerical choice of `Btail`, `Bmajority`, and `Bminority`, and their
  final `Rlo`/`Rhi` budget arithmetic, are intentionally inputs to the next
  file because the current consumer leaves `Rlo` and `Rhi` abstract.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateSamplingMassCountTransport

end
