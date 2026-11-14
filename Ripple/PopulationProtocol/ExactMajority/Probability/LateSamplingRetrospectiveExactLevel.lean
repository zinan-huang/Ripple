-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingRetrospectiveExactLevel.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingCompletion
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingShallowTransport
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingClassReceiptArithmetic

/-!
# Retrospective exact-level arrivals

For the winning sign, the exact combined potential is

  exactEll + 2 * scaledShallowPositive (ell - 1)
    = scaledShallowPositive ell.

Consequently the shallow monotonicity theorem of `LateSamplingShallowTransport` already transports the combined
potential between arbitrary observed snapshots.  The seed's `.002 M`
all-sign shallow budget bounds the second summand by `.002 M`, giving the
integer-exact retrospective allowance consumed by
`retrospective_exact_level_arithmetic`.

The old-index cutoff is deliberately absent from the hypotheses: it is
strictly unnecessary for this bound.  It remains part of the N16 receipt for
later ancestry statements.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingRetrospectiveExactLevel

open TimeTheorem StageEventSpec
open AveragingCreditTransitions AveragingTerminalReadout
open LateStrengthening LateF6OriginalLaw
open LateSamplingSeedReceipt
open LateSamplingShallowTransport
open LateSamplingCompletion

variable {L K n : ℕ}

/-! ## Atom forms of the two deterministic readouts -/

/-- Winning-sign mass through `ell`, scaled by `2^ell`, for one agent. -/
noncomputable def winningAtOrBelowAtom
    (σ : Sign) (ell : ℕ) (a : AgentState L K) : ℚ := by
  classical
  exact
    if a.role = .main then
      match a.bias with
      | .zero => 0
      | .dyadic τ j =>
          if τ = σ ∧ j.val ≤ ell then scaledWeight ell j.val else 0
    else 0

/-- Absolute Main mass strictly below `ell`, scaled by `2^ell`, for one
agent. -/
noncomputable def strictAbsoluteAtom
    (ell : ℕ) (a : AgentState L K) : ℚ := by
  classical
  exact
    if a.role = .main then
      match a.bias with
      | .zero => 0
      | .dyadic _ j =>
          if j.val < ell then scaledWeight ell j.val else 0
    else 0

private theorem scaledWeight_eq_scaledZpow (ell j : ℕ) :
    scaledWeight ell j =
      (2 : ℚ) ^ ell * (2 : ℚ) ^ (-(j : ℤ)) := by
  simp [scaledWeight, zpow_neg, zpow_natCast, div_eq_mul_inv]

private theorem scaledWeight_self_eq_one (ell : ℕ) :
    scaledWeight ell ell = (1 : ℚ) := by
  unfold scaledWeight
  field_simp

private theorem scaledWeight_twice_previous
    (ell j : ℕ) (hell : 1 ≤ ell) :
    2 * scaledWeight (ell - 1) j = scaledWeight ell j := by
  have hs : ell - 1 + 1 = ell := by
    omega
  unfold scaledWeight
  conv_rhs => rw [← hs, pow_succ]
  ring

private theorem winningAtOrBelowAtom_eq_term
    (σ : Sign) (ell : ℕ) (a : AgentState L K) :
    winningAtOrBelowAtom σ ell a =
      (2 : ℚ) ^ ell *
        (if a.role = .main then
          match a.bias with
          | .zero => 0
          | .dyadic τ j =>
              if τ = σ ∧ j.val ≤ ell then
                (2 : ℚ) ^ (-(j.val : ℤ))
              else 0
        else 0) := by
  classical
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [winningAtOrBelowAtom, hm, hb]
    | dyadic τ j =>
        by_cases hτ : τ = σ
        · by_cases hj : j.val ≤ ell <;>
            simp [winningAtOrBelowAtom, hm, hb, hτ, hj,
              scaledWeight_eq_scaledZpow]
        · simp [winningAtOrBelowAtom, hm, hb, hτ]
  · simp [winningAtOrBelowAtom, hm]

private theorem strictAbsoluteAtom_eq_term
    (ell : ℕ) (a : AgentState L K) :
    strictAbsoluteAtom ell a =
      (2 : ℚ) ^ ell *
        (if a.role = .main then
          match a.bias with
          | .zero => 0
          | .dyadic _ j =>
              if j.val < ell then
                (2 : ℚ) ^ (-(j.val : ℤ))
              else 0
        else 0) := by
  classical
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [strictAbsoluteAtom, hm, hb]
    | dyadic τ j =>
        by_cases hj : j.val < ell <;>
          simp [strictAbsoluteAtom, hm, hb, hj,
            scaledWeight_eq_scaledZpow]
  · simp [strictAbsoluteAtom, hm]

private theorem winningAtOrBelowAtom_sum
    (σ : Sign) (ell : ℕ) (c : InputCfg n) :
    Config.sumOf (winningAtOrBelowAtom σ ell) c =
      scaledShallowPositive σ ell c := by
  classical
  induction c using Multiset.induction_on with
  | empty =>
      simp [Config.sumOf, scaledShallowPositive]
  | cons a c ih =>
      simp only [Config.sumOf, scaledShallowPositive,
        Multiset.map_cons, Multiset.sum_cons] at ih ⊢
      rw [ih, mul_add]
      congr 1
      by_cases hm : a.role = .main
      · cases hb : a.bias with
        | zero => simp [winningAtOrBelowAtom, hm, hb]
        | dyadic τ j =>
            by_cases hτ : τ = σ
            · by_cases hj : j.val ≤ ell <;>
                simp [winningAtOrBelowAtom, hm, hb, hτ, hj,
                  scaledWeight_eq_scaledZpow]
            · simp [winningAtOrBelowAtom, hm, hb, hτ]
      · simp [winningAtOrBelowAtom, hm]

private theorem strictAbsoluteAtom_sum
    (ell : ℕ) (c : InputCfg n) :
    Config.sumOf (strictAbsoluteAtom ell) c =
      (2 : ℚ) ^ ell * shallowMass ell c := by
  classical
  induction c using Multiset.induction_on with
  | empty =>
      simp [Config.sumOf, shallowMass]
  | cons a c ih =>
      simp only [Config.sumOf, shallowMass, Multiset.map_cons,
        Multiset.sum_cons] at ih ⊢
      rw [ih, mul_add]
      congr 1
      by_cases hm : a.role = .main
      · cases hb : a.bias with
        | zero => simp [strictAbsoluteAtom, hm, hb]
        | dyadic τ j =>
            by_cases hj : j.val < ell <;>
              simp [strictAbsoluteAtom, hm, hb, hj,
                scaledWeight_eq_scaledZpow]
      · simp [strictAbsoluteAtom, hm]

private theorem winningAtOrBelowAtom_nonneg
    (σ : Sign) (ell : ℕ) (a : AgentState L K) :
    0 ≤ winningAtOrBelowAtom σ ell a := by
  classical
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [winningAtOrBelowAtom, hm, hb]
    | dyadic τ j =>
        by_cases hτ : τ = σ
        · by_cases hj : j.val ≤ ell <;>
            simp [winningAtOrBelowAtom, hm, hb, hτ, hj,
              scaledWeight_nonneg]
        · simp [winningAtOrBelowAtom, hm, hb, hτ]
  · simp [winningAtOrBelowAtom, hm]

private theorem strictAbsoluteAtom_nonneg
    (ell : ℕ) (a : AgentState L K) :
    0 ≤ strictAbsoluteAtom ell a := by
  classical
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [strictAbsoluteAtom, hm, hb]
    | dyadic τ j =>
        by_cases hj : j.val < ell <;>
          simp [strictAbsoluteAtom, hm, hb, hj,
            scaledWeight_nonneg]
  · simp [strictAbsoluteAtom, hm]

private theorem sumOf_nonneg
    {α : Type*} (f : α → ℚ) (c : Multiset α)
    (h : ∀ a ∈ c, 0 ≤ f a) :
    0 ≤ Config.sumOf f c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [Config.sumOf]
  | cons a c ih =>
      have ha := h a (Multiset.mem_cons_self a c)
      have hc := ih
        (fun b hb => h b (Multiset.mem_cons_of_mem hb))
      simp only [Config.sumOf, Multiset.map_cons,
        Multiset.sum_cons] at ha hc ⊢
      exact add_nonneg ha hc

private theorem sumOf_const_mul
    {α : Type*} (r : ℚ) (f : α → ℚ) (c : Multiset α) :
    Config.sumOf (fun a => r * f a) c =
      r * Config.sumOf f c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [Config.sumOf]
  | cons a c ih =>
      simp only [Config.sumOf, Multiset.map_cons,
        Multiset.sum_cons] at ih ⊢
      rw [ih]
      ring

private theorem sumOf_le_sumOf
    {α : Type*} (f g : α → ℚ) (c : Multiset α)
    (h : ∀ a ∈ c, f a ≤ g a) :
    Config.sumOf f c ≤ Config.sumOf g c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [Config.sumOf]
  | cons a c ih =>
      have ha := h a (Multiset.mem_cons_self a c)
      have hc := ih
        (fun b hb => h b (Multiset.mem_cons_of_mem hb))
      simp only [Config.sumOf, Multiset.map_cons,
        Multiset.sum_cons] at ha hc ⊢
      linarith

/-! ## Exact decomposition at one level -/

private theorem dyadicIndex_eq_of_eq
    {τ υ : Sign} {j k : Fin (L + 1)}
    (h : Bias.dyadic τ j = Bias.dyadic υ k) :
    j.val = k.val := by
  have hv := congrArg
    (fun b : Bias L =>
      match b with
      | .zero => 0
      | .dyadic _ r => r.val) h
  simpa using hv

private theorem dyadicSign_eq_of_eq
    {τ υ : Sign} {j k : Fin (L + 1)}
    (h : Bias.dyadic τ j = Bias.dyadic υ k) :
    τ = υ := by
  have hv := congrArg
    (fun b : Bias L =>
      match b with
      | .zero => (none : Option Sign)
      | .dyadic ρ _ => some ρ) h
  simpa using hv

private theorem exactBand_iff_index
    (a : AgentState L K) (σ : Sign) (ell : ℕ)
    (j : Fin (L + 1))
    (hm : a.role = .main)
    (hb : a.bias = Bias.dyadic σ j) :
    InBand σ ell 0 a ↔ j.val = ell := by
  constructor
  · rintro ⟨_, k, hk, hlo, hhi⟩
    have hindex := dyadicIndex_eq_of_eq (hb.symm.trans hk)
    omega
  · intro hj
    exact ⟨hm, j, hb, by omega, by omega⟩

private theorem not_inBand_of_wrong_sign
    (a : AgentState L K) (σ τ : Sign)
    (ell width : ℕ) (j : Fin (L + 1))
    (hb : a.bias = Bias.dyadic τ j)
    (hne : τ ≠ σ) :
    ¬ InBand σ ell width a := by
  rintro ⟨_, k, hk, _, _⟩
  have hsign : τ = σ :=
    dyadicSign_eq_of_eq (hb.symm.trans hk)
  exact hne hsign

private theorem winningAtOrBelowAtom_split
    (σ : Sign) (ell : ℕ) (hell : 1 ≤ ell)
    (a : AgentState L K) :
    winningAtOrBelowAtom σ ell a =
      bandIndicator σ ell 0 a +
        2 * winningAtOrBelowAtom σ (ell - 1) a := by
  classical
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [winningAtOrBelowAtom, bandIndicator, InBand, hm, hb]
    | dyadic τ j =>
        by_cases hτ : τ = σ
        · subst τ
          have hbandIff := exactBand_iff_index a σ ell j hm hb
          by_cases hlt : j.val < ell
          · have hcur : j.val ≤ ell := by
              omega
            have hprev : j.val ≤ ell - 1 := by
              omega
            have hnotBand : ¬ InBand σ ell 0 a := by
              rw [hbandIff]
              omega
            have hw := scaledWeight_twice_previous ell j.val hell
            simpa [winningAtOrBelowAtom, hm, hb, hcur, hprev,
              bandIndicator, hnotBand] using hw.symm
          · by_cases heq : j.val = ell
            · have hcur : j.val ≤ ell := by
                omega
              have hnotPrev : ¬ j.val ≤ ell - 1 := by
                omega
              have hband : InBand σ ell 0 a := hbandIff.2 heq
              have hnotPrev' : ¬ ell ≤ ell - 1 := by
                omega
              simpa [winningAtOrBelowAtom, hm, hb, hcur, hnotPrev,
                bandIndicator, hband, heq, hnotPrev'] using
                (scaledWeight_self_eq_one ell)
            · have hcur : ¬ j.val ≤ ell := by
                omega
              have hprev : ¬ j.val ≤ ell - 1 := by
                omega
              have hnotBand : ¬ InBand σ ell 0 a := by
                rw [hbandIff]
                exact heq
              simp [winningAtOrBelowAtom, hm, hb, hcur, hprev,
                bandIndicator, hnotBand]
        · have hnotBand :=
            not_inBand_of_wrong_sign a σ τ ell 0 j hb hτ
          simp [winningAtOrBelowAtom, hm, hb, hτ,
            bandIndicator, hnotBand]
  · have hnotBand : ¬ InBand σ ell 0 a := by
      intro h
      exact hm h.1
    simp [winningAtOrBelowAtom, hm, bandIndicator, hnotBand]

private theorem sum_winningAtOrBelowAtom_split
    (σ : Sign) (ell : ℕ) (hell : 1 ≤ ell)
    (c : InputCfg n) :
    Config.sumOf (winningAtOrBelowAtom σ ell) c =
      Config.sumOf (bandIndicator σ ell 0) c +
        2 * Config.sumOf
          (winningAtOrBelowAtom σ (ell - 1)) c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [Config.sumOf]
  | cons a c ih =>
      simp only [Config.sumOf, Multiset.map_cons,
        Multiset.sum_cons] at ih ⊢
      rw [winningAtOrBelowAtom_split σ ell hell a, ih]
      ring

/-- Exact deterministic identity behind the retrospective-arrival budget. -/
theorem scaledShallowPositive_exactLevel_split
    (σ : Sign) (ell : ℕ) (c : InputCfg n)
    (hell : 1 ≤ ell) :
    scaledShallowPositive σ ell c =
      (bandCount σ ell 0 c : ℚ) +
        2 * scaledShallowPositive σ (ell - 1) c := by
  calc
    scaledShallowPositive σ ell c =
        Config.sumOf (winningAtOrBelowAtom σ ell) c :=
      (winningAtOrBelowAtom_sum σ ell c).symm
    _ = Config.sumOf (bandIndicator σ ell 0) c +
          2 * Config.sumOf
            (winningAtOrBelowAtom σ (ell - 1)) c :=
      sum_winningAtOrBelowAtom_split σ ell hell c
    _ = (bandCount σ ell 0 c : ℚ) +
          2 * scaledShallowPositive σ (ell - 1) c := by
      rw [sum_bandIndicator, winningAtOrBelowAtom_sum]

/-- The exact-level count is one nonnegative summand of the combined
potential. -/
theorem retro_bandCount_exact_le_scaledShallowPositive
    (σ : Sign) (ell : ℕ) (c : InputCfg n)
    (hell : 1 ≤ ell) :
    (bandCount σ ell 0 c : ℚ) ≤
      scaledShallowPositive σ ell c := by
  have hnonneg :
      0 ≤ scaledShallowPositive σ (ell - 1) c := by
    rw [← winningAtOrBelowAtom_sum]
    exact sumOf_nonneg
      (winningAtOrBelowAtom σ (ell - 1)) c
      (fun a _ => winningAtOrBelowAtom_nonneg σ (ell - 1) a)
  rw [scaledShallowPositive_exactLevel_split σ ell c hell]
  linarith

/-! ## The original `.002 M` shallow allowance -/

private theorem twice_winningPrevious_le_strictAbsolute
    (σ : Sign) (ell : ℕ) (hell : 1 ≤ ell)
    (a : AgentState L K) :
    2 * winningAtOrBelowAtom σ (ell - 1) a ≤
      strictAbsoluteAtom ell a := by
  classical
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [winningAtOrBelowAtom, strictAbsoluteAtom, hm, hb]
    | dyadic τ j =>
        by_cases hbound : τ = σ ∧ j.val ≤ ell - 1
        · obtain ⟨hτ, hj⟩ := hbound
          have hlt : j.val < ell := by
            omega
          have hw := scaledWeight_twice_previous ell j.val hell
          simp [winningAtOrBelowAtom, strictAbsoluteAtom,
            hm, hb, hτ, hj, hlt]
          exact le_of_eq hw
        · have hnonneg := strictAbsoluteAtom_nonneg ell a
          simp [winningAtOrBelowAtom, hm, hb, hbound]
          exact hnonneg
  · simp [winningAtOrBelowAtom, strictAbsoluteAtom, hm]

/-- Same-sign mass through `ell - 1`, scaled at `ell - 1`, is at most
half the all-sign strict-shallow mass scaled at `ell`. -/
theorem retro_twice_scaledShallowPrevious_le_shallowMass
    (σ : Sign) (ell : ℕ) (c : InputCfg n)
    (hell : 1 ≤ ell) :
    2 * scaledShallowPositive σ (ell - 1) c ≤
      (2 : ℚ) ^ ell * shallowMass ell c := by
  calc
    2 * scaledShallowPositive σ (ell - 1) c =
        2 * Config.sumOf
          (winningAtOrBelowAtom σ (ell - 1)) c := by
      rw [winningAtOrBelowAtom_sum]
    _ = Config.sumOf
        (fun a => 2 * winningAtOrBelowAtom σ (ell - 1) a) c := by
      exact
        (sumOf_const_mul 2
          (winningAtOrBelowAtom σ (ell - 1)) c).symm
    _ ≤ Config.sumOf (strictAbsoluteAtom ell) c :=
      sumOf_le_sumOf
        (fun a => 2 * winningAtOrBelowAtom σ (ell - 1) a)
        (strictAbsoluteAtom ell) c
        (fun a _ =>
          twice_winningPrevious_le_strictAbsolute
            σ ell hell a)
    _ = (2 : ℚ) ^ ell * shallowMass ell c :=
      strictAbsoluteAtom_sum ell c

/-- The transported winning-sign mass below `ell` costs at most `.001 M`;
after the factor two in the exact decomposition this is the requested
`.002 M` count allowance. -/
theorem scaledShallowPrevious_seed_budget
    {init : InputCfg n} {ω : InputLog n}
    {a s t v M ell : ℕ} {σ : Sign}
    (hpath : Prefix init ω a s t)
    (hseed : LateSamplingSeedReceipt init M ell σ
      (trace init ω s))
    (hsv : s ≤ v) (hvt : v ≤ t) :
    (1000 : ℚ) *
        scaledShallowPositive σ (ell - 1)
          (trace init ω v) ≤
      (M : ℚ) := by
  have hell : 1 ≤ ell := by
    have := hseed.levelLower
    omega
  have htransport :=
    scaledShallowPositive_seed_mono
      (ell := ell - 1) (σ := σ) hpath hsv hvt
  have hstrict :=
    retro_twice_scaledShallowPrevious_le_shallowMass
      σ ell (trace init ω s) hell
  have hseedBudget := hseed.shallow
  nlinarith only [htransport, hstrict, hseedBudget]

/-! ## Pathwise retrospective transport -/

/-- The combined potential itself is nonincreasing between any two actual
snapshots in the observed prefix. -/
theorem exactLevelArrivalPotential_mono
    {init : InputCfg n} {ω : InputLog n}
    {a s t v u ell : ℕ} {σ : Sign}
    (hpath : Prefix init ω a s t)
    (hsv : s ≤ v) (hvu : v ≤ u) (hut : u ≤ t)
    (hell : 1 ≤ ell) :
    (bandCount σ ell 0 (trace init ω u) : ℚ) +
        2 * scaledShallowPositive σ (ell - 1)
          (trace init ω u) ≤
      (bandCount σ ell 0 (trace init ω v) : ℚ) +
        2 * scaledShallowPositive σ (ell - 1)
          (trace init ω v) := by
  rw [← scaledShallowPositive_exactLevel_split
      σ ell (trace init ω u) hell,
    ← scaledShallowPositive_exactLevel_split
      σ ell (trace init ω v) hell]
  exact scaledShallowPositive_observed_mono
    hpath hsv hvu hut

/-- The exact integer form required by the arithmetic consumer
`LateSamplingClassReceiptArithmetic`. -/
theorem retrospective_exact_level_at_snapshot
    {init : InputCfg n} {ω : InputLog n}
    {a s t v u M ell : ℕ} {σ : Sign}
    (hpath : Prefix init ω a s t)
    (hseed : LateSamplingSeedReceipt init M ell σ
      (trace init ω s))
    (hsv : s ≤ v) (hvu : v ≤ u) (hut : u ≤ t) :
    1000 * bandCount σ ell 0 (trace init ω u) ≤
      1000 * bandCount σ ell 0 (trace init ω v) +
        2 * M := by
  have hell : 1 ≤ ell := by
    have := hseed.levelLower
    omega
  have hterminal :=
    retro_bandCount_exact_le_scaledShallowPositive
      σ ell (trace init ω u) hell
  have hmono :=
    scaledShallowPositive_observed_mono
      (ell := ell) (σ := σ) hpath hsv hvu hut
  have hsplit :=
    scaledShallowPositive_exactLevel_split
      σ ell (trace init ω v) hell
  have hbudget :=
    scaledShallowPrevious_seed_budget
      hpath hseed hsv (hvu.trans hut)
  have hq :
      (1000 : ℚ) *
          (bandCount σ ell 0 (trace init ω u) : ℚ) ≤
        1000 *
          (bandCount σ ell 0 (trace init ω v) : ℚ) +
        2 * (M : ℚ) := by
    nlinarith only [hterminal, hmono, hsplit, hbudget]
  exact_mod_cast hq

/-- Completion-receipt wrapper.  The receipt supplies the whole observed
prefix `four .. u`; the N16 seed receipt and the position of `v` inside that
prefix are the two explicit cross-row inputs. -/
theorem retrospective_exact_level_at_completion
    {init : InputCfg n} {ω : InputLog n}
    {a four five u v M ell : ℕ} {σ : Sign}
    {Snapshot : InputCfg n → Prop}
    (hcompletion :
      CompletionReceipt init ω a four five u Snapshot)
    (hseed : LateSamplingSeedReceipt init M ell σ
      (trace init ω four))
    (hfourv : four ≤ v) (hvu : v ≤ u) :
    1000 * bandCount σ ell 0 (trace init ω u) ≤
      1000 * bandCount σ ell 0 (trace init ω v) +
        2 * M := by
  exact retrospective_exact_level_at_snapshot
    hcompletion.observed_path hseed hfourv hvu le_rfl

/-- The exact `.002 M` result converted immediately to the weaker `.0021 M`
allowance exported by `LateSamplingClassReceiptArithmetic`. -/
theorem retrospective_sampling_allowance_at_completion
    {init : InputCfg n} {ω : InputLog n}
    {a four five u v M ell : ℕ} {σ : Sign}
    {Snapshot : InputCfg n → Prop}
    (hcompletion :
      CompletionReceipt init ω a four five u Snapshot)
    (hseed : LateSamplingSeedReceipt init M ell σ
      (trace init ω four))
    (hfourv : four ≤ v) (hvu : v ≤ u) :
    10000 * bandCount σ ell 0 (trace init ω u) ≤
      10000 * bandCount σ ell 0 (trace init ω v) +
        21 * M := by
  exact
    LateSamplingClassReceiptArithmetic.retrospective_exact_level_arithmetic
      M
      (bandCount σ ell 0 (trace init ω v))
      (bandCount σ ell 0 (trace init ω u))
      (retrospective_exact_level_at_completion
        hcompletion hseed hfourv hvu)

end Ripple.PopulationProtocol.ExactMajority.LateSamplingRetrospectiveExactLevel

end
