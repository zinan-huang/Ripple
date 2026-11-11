/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.RegisterMachine.Clocked.Levels
import Ripple.sCRNUniversality.Stochastic.MassAction.Completion

/-!
# SCWB Theorem 3.1: a register machine simulated by a fixed CRN with error `δ`

Soloveichik, Cook, Winfree, Bruck, "Computation with finite stochastic chemical reaction
networks", Theorem 3.1 (FIX3-SCWB §3).  For a register machine `M`, the network `net M L`
(Fig. 3.1) is fixed before the error bound, the input and the step bound; only the initial count
`a` of the accuracy species `A` depends on them.

The law `law M L a σ₀ = rawLaw (net M L) _ (enc a σ₀)` is the law of the *embedded jump chain*
of the mass-action CTMC (the sequence of reaction labels); the sample space carries no holding
times.  Expected time is the expected holding-time functional of that chain
(`Stochastic/MassAction/Completion.lean`).

* `SimOK a σ₀ x₀ t ω` (safety): along the jump chain `ω`, whenever at most `t` machine
  reactions have fired, the CRN state encodes the corresponding configuration of `M` from `x₀`;
* `Completes a σ₀ t ω` (liveness): after some jump, `t` machine reactions have fired or the
  machine is halted; `Simulates := SimOK ∧ Completes`;
* `expTime a σ₀ t`: expected time spent in live states before `t` machine steps, for unit rate
  constants and unit volume (with rate constant `k` and volume `v` all holding times scale by
  `v / k`);
* `law_simOK_not_completes`: a correct run completes with probability one (on the paths that
  never complete, every jump costs at least `1 / propBound` of expected time, while `expTime`
  is finite);
* `theorem_3_1_general` (Theorem 3.1′): for clock length `L + 1 ≥ 2` and `a ≥ 2`, the
  probability that the simulation is not correct and complete is at most `t / G` and the
  expected time at most `2 t G`, `G = 1 + a + ⋯ + a^L`;
* `scwb_theorem_3_1`: with `L = 1` and `a = max 2 ⌈t / δ⌉`, error `≤ δ` and expected time
  `≤ 6 v t² / (k δ)`.
-/

namespace Ripple.sCRNUniversality.RegisterMachine.Clocked

open MeasureTheory ProbabilityTheory Preorder Stochastic Stochastic.MassAction
open Stochastic.ClockOccupation
open scoped ENNReal

variable {Reg Label : Type} [Fintype Reg] [DecidableEq Reg] [Fintype Label] [DecidableEq Label]
variable {L : ℕ} {M : RM Reg Label}

/-! ### Machine semantics on outer states -/

/-- One step of `M` on an outer state (`none` at `halt`). -/
def stepO (M : RM Reg Label) (x : Outer Reg Label) : Option (Outer Reg Label) :=
  (M.step? ⟨x.1, x.2⟩).map fun c => (c.pc, c.reg)

/-- The configuration of `M` after `k` steps from `x₀` (`none` once `M` has halted). -/
def cfgAt (M : RM Reg Label) (x₀ : Outer Reg Label) : ℕ → Option (Outer Reg Label)
  | 0 => some x₀
  | k + 1 => (cfgAt M x₀ k).bind (stepO M)

omit [Fintype Reg] [Fintype Label] [DecidableEq Label] in
theorem cfgAt_succ (x₀ : Outer Reg Label) (k : ℕ) :
    cfgAt M x₀ (k + 1) = (cfgAt M x₀ k).bind (stepO M) := rfl

/-- **Correct simulation of the first `t` steps** along `ω` (safety): after every jump at which
at most `t` machine reactions have fired, the state encodes the configuration of `M` reached by
that many steps.  It does not assert that the machine reactions occur; see `Simulates`. -/
def SimOK (a : ℕ) (σ₀ : RState Reg Label L) (x₀ : Outer Reg Label) (t : ℕ) (ω : Ω M L) : Prop :=
  ∀ n, K n ω ≤ t → ∃ x c, cfgAt M x₀ (K n ω) = some x ∧ Z a σ₀ n ω = enc a (x, c)

/-- Error event: a jump-on-zero reaction fires on a nonzero register before step `t`. -/
def Err (a : ℕ) (σ₀ : RState Reg Label L) (t : ℕ) : Set (Ω M L) :=
  {ω | ∃ n, K n ω < t ∧ ∃ d : DecIdx M,
    ω (n + 1) = some (Sum.inr (Sum.inr (Sum.inl d))) ∧ 1 ≤ Z a σ₀ n ω (Sp.reg d.1.2.1)}

/-- Null event: a label of probability zero is drawn. -/
def Null (a : ℕ) (σ₀ : RState Reg Label L) : Set (Ω M L) :=
  {ω | ∃ n, massActionPMF (net M L) (net_hasPositiveRates M L) (Z a σ₀ n ω) (ω (n + 1)) = 0}

variable (a : ℕ)

theorem law_Null (ha : 1 ≤ a) (hL : 1 ≤ L) (σ₀ : RState Reg Label L) :
    law M L a σ₀ (Null a σ₀) = 0 := by
  classical
  let H : ℕ × (ℕ × RState Reg Label L) × Option (net M L).I → Set (Ω M L) := fun p =>
    if massActionPMF (net M L) (net_hasPositiveRates M L) (enc a p.2.1.2) p.2.2 = 0 then
      E a σ₀ p.1 p.2.1.1 p.2.1.2 ∩ {ω | ω (p.1 + 1) = p.2.2} else ∅
  have hsub : Null (M := M) a σ₀ ⊆ ⋃ p, H p := by
    rintro ω ⟨n, hn⟩
    obtain ⟨σ, hσ⟩ := Z_enc ha hL σ₀ n ω
    refine Set.mem_iUnion.mpr ⟨(n, (K n ω, σ), ω (n + 1)), ?_⟩
    rw [hσ] at hn
    simp only [H, if_pos hn]
    exact ⟨⟨rfl, hσ⟩, rfl⟩
  refine measure_mono_null hsub (measure_iUnion_null fun p => ?_)
  simp only [H]
  split_ifs with h
  · rw [law_E_label, h, mul_zero]
  · exact measure_empty

/-- Off the error and null events the CRN simulates `M` step by step. -/
theorem simOK_of_not_mem (ha : 1 ≤ a) (hL : 1 ≤ L) (x₀ : Outer Reg Label) (t : ℕ) (ω : Ω M L)
    (hE : ω ∉ Err a (x₀, Fin.last L) t) (hN : ω ∉ Null a (x₀, Fin.last L)) :
    SimOK a (x₀, Fin.last L) x₀ t ω := by
  intro n
  induction n with
  | zero => intro _; exact ⟨x₀, Fin.last L, rfl, rfl⟩
  | succ n ih =>
    intro hKt
    obtain ⟨x, c, hcfg, hZ⟩ := ih (le_trans (K_mono ω (Nat.le_succ n)) hKt)
    have hpmf : massActionPMF (net M L) (net_hasPositiveRates M L) (enc a (x, c))
        (ω (n + 1)) ≠ 0 := by
      intro h0; exact hN ⟨n, by rw [hZ]; exact h0⟩
    cases ho : ω (n + 1) with
    | none => rw [ho, pmf_enc_none ha hL] at hpmf; exact absurd rfl hpmf
    | some i =>
      rw [ho, pmf_enc_some ha hL] at hpmf
      have hβ : beta M a i (x, c) ≠ 0 := by intro h; apply hpmf; simp [h]
      have hZ' : Z a (x₀, Fin.last L) (n + 1) ω = enc a (tgt M i (x, c)) := by
        rw [Z_succ, hZ, ho, stateStep_enc_of_beta ha hL hβ]
      have hK' : K (n + 1) ω = K n ω + rmOpt (M := M) (some i) := by rw [K_succ, ho]
      refine ⟨(tgt M i (x, c)).1, (tgt M i (x, c)).2, ?_, hZ'⟩
      rcases i with p | d | d | j | j
      · have hq : p.1.1 = x.1 := by by_contra h; apply hβ; simp [beta, h]
        have hcode : M.code x.1 = .inc p.1.2.1 p.1.2.2 := hq ▸ p.2
        rw [hK', show rmOpt (M := M) (some (Sum.inl p)) = 1 from rfl, cfgAt_succ, hcfg,
          Option.bind_some]
        simp only [stepO, RM.step?, hcode, Option.map_some, tgt]
        congr 2
        funext r'
        simp only [Function.update_apply]
        split_ifs with h <;> simp [h]
      · have hq : d.1.1 = x.1 := by by_contra h; apply hβ; simp [beta, h]
        have hy : x.2 d.1.2.1 ≠ 0 := by intro h; apply hβ; simp [beta, h]
        have hcode : M.code x.1 = .decJz d.1.2.1 d.1.2.2.1 d.1.2.2.2 := hq ▸ d.2
        rw [hK', show rmOpt (M := M) (some (Sum.inr (Sum.inl d))) = 1 from rfl, cfgAt_succ, hcfg,
          Option.bind_some]
        simp only [stepO, RM.step?, hcode, hy, if_false, Option.map_some, tgt]
        congr 2
        funext r'
        simp only [Function.update_apply]
      · have h2 : (0 : Fin (L + 1)) = c ∧ d.1.1 = x.1 := by
          by_contra h; apply hβ; simp only [beta]; rw [if_neg h]
        have hcode : M.code x.1 = .decJz d.1.2.1 d.1.2.2.1 d.1.2.2.2 := h2.2 ▸ d.2
        have hK1 : K (n + 1) ω = K n ω + 1 := hK'
        have hy : x.2 d.1.2.1 = 0 := by
          by_contra hy
          refine hE ⟨n, by omega, d, ho, ?_⟩
          rw [hZ]
          show 1 ≤ x.2 d.1.2.1
          omega
        rw [hK1, cfgAt_succ, hcfg, Option.bind_some]
        simp only [stepO, RM.step?, hcode, hy, if_true, Option.map_some, tgt]
      · rw [hK', show rmOpt (M := M) (some (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))) = 0 from rfl,
          add_zero, hcfg]
        rfl
      · rw [hK', show rmOpt (M := M) (some (Sum.inr (Sum.inr (Sum.inr (Sum.inr j))))) = 0 from rfl,
          add_zero, hcfg]
        rfl

/-! ### The error bound -/

theorem law_Err_le (ha : 1 ≤ a) (hL : 1 ≤ L) (σ₀ : RState Reg Label L) (t : ℕ) :
    law M L a σ₀ (Err a σ₀ t) ≤ ∑' ξ : ℕ × RState Reg Label L, ∑ d : DecIdx M,
      if ξ.1 < t ∧ 1 ≤ ξ.2.1.2 d.1.2.1 then
        Wt (M := M) a σ₀ ξ * (beta M a (Sum.inr (Sum.inr (Sum.inl d))) ξ.2 : ℝ≥0∞) else 0 := by
  classical
  let G : ℕ × (ℕ × RState Reg Label L) × DecIdx M → Set (Ω M L) := fun p =>
    if p.2.1.1 < t ∧ 1 ≤ p.2.1.2.1.2 p.2.2.1.2.1 then
      E a σ₀ p.1 p.2.1.1 p.2.1.2 ∩ {ω | ω (p.1 + 1) = some (Sum.inr (Sum.inr (Sum.inl p.2.2)))}
    else ∅
  have hsub : Err (M := M) a σ₀ t ⊆ ⋃ p, G p := by
    rintro ω ⟨n, hn, d, hd, hreg⟩
    obtain ⟨σ, hσ⟩ := Z_enc ha hL σ₀ n ω
    refine Set.mem_iUnion.mpr ⟨(n, (K n ω, σ), d), ?_⟩
    have hc : K n ω < t ∧ 1 ≤ σ.1.2 d.1.2.1 := ⟨hn, by rw [hσ] at hreg; exact hreg⟩
    simp only [G, if_pos hc]
    exact ⟨⟨rfl, hσ⟩, hd⟩
  have hval : ∀ p, law M L a σ₀ (G p) =
      if p.2.1.1 < t ∧ 1 ≤ p.2.1.2.1.2 p.2.2.1.2.1 then
        law M L a σ₀ (E a σ₀ p.1 p.2.1.1 p.2.1.2) *
          ((beta M a (Sum.inr (Sum.inr (Sum.inl p.2.2))) p.2.1.2 : ℝ≥0∞) /
            (Btot M a p.2.1.2 : ℝ≥0∞)) else 0 := by
    intro p
    simp only [G]
    split_ifs
    · rw [law_E_label]
      congr 1
      exact pmf_enc_some ha hL _ _
    · exact measure_empty
  calc law M L a σ₀ (Err a σ₀ t) ≤ law M L a σ₀ (⋃ p, G p) := measure_mono hsub
    _ ≤ ∑' p, law M L a σ₀ (G p) := measure_iUnion_le _
    _ = ∑' n : ℕ, ∑' ξ : ℕ × RState Reg Label L, ∑' d : DecIdx M, law M L a σ₀ (G (n, ξ, d)) := by
        rw [ENNReal.tsum_prod']
        exact tsum_congr fun n => ENNReal.tsum_prod'
    _ = ∑' ξ : ℕ × RState Reg Label L, ∑' d : DecIdx M, ∑' n : ℕ, law M L a σ₀ (G (n, ξ, d)) := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun ξ => ENNReal.tsum_comm
    _ = _ := by
        refine tsum_congr fun ξ => ?_
        rw [tsum_fintype]
        refine Finset.sum_congr rfl fun d _ => ?_
        simp only [hval]
        split_ifs
        · rw [ENNReal.tsum_mul_right, ← occ_mul_div]
          rfl
        · simp

theorem errSum_mul_le (ha2 : 2 ≤ a) (hL : 1 ≤ L) (σ₀ : RState Reg Label L)
    (hσ₀ : σ₀.2 = Fin.last L) (t : ℕ) :
    (∑' ξ : ℕ × RState Reg Label L, ∑ d : DecIdx M,
      if ξ.1 < t ∧ 1 ≤ ξ.2.1.2 d.1.2.1 then
        Wt (M := M) a σ₀ ξ * (beta M a (Sum.inr (Sum.inr (Sum.inl d))) ξ.2 : ℝ≥0∞) else 0) *
      ENNReal.ofReal (geomWeight a (L + 1)) ≤ t := by
  have ha : 1 ≤ a := by omega
  rw [ENNReal.tsum_prod', tsum_eq_sum (s := Finset.range t)]
  · rw [Finset.sum_mul]
    calc _ ≤ ∑ k ∈ Finset.range t, (1 : ℝ≥0∞) := Finset.sum_le_sum fun k hk => ?_
      _ = t := by simp
    rw [Finset.mem_range] at hk
    calc _ ≤ ∑' σ, eE (M := M) a σ₀ k σ := ?_
      _ ≤ 1 := eE_total_le_one (M := M) a σ₀ ha hL k
    rw [ENNReal.tsum_prod' (α := Outer Reg Label) (β := Fin (L + 1)),
      ENNReal.tsum_prod' (α := Outer Reg Label) (β := Fin (L + 1)), ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun x => ?_
    rw [tsum_fintype, tsum_fintype]
    dsimp only
    by_cases hex : ∃ d : DecIdx M, d.1.1 = x.1 ∧ 1 ≤ x.2 d.1.2.1
    · obtain ⟨d₀, hq, hy⟩ := hex
      have hlive : Live M x := live_of_dec d₀ x hq
      have hρ : 1 ≤ rho M x := le_trans hy (le_rho_of_dec x d₀ hq)
      have hterm : ∀ (c : Fin (L + 1)) (d : DecIdx M),
          (if k < t ∧ 1 ≤ x.2 d.1.2.1 then Wt (M := M) a σ₀ (k, (x, c)) *
            (beta M a (Sum.inr (Sum.inr (Sum.inl d))) (x, c) : ℝ≥0∞) else 0) ≤
          if c = 0 ∧ d = d₀ then Wt (M := M) a σ₀ (k, (x, 0)) else 0 := by
        intro c d
        by_cases h : (0 : Fin (L + 1)) = c ∧ d.1.1 = x.1
        · obtain ⟨hc, hd⟩ := h
          subst hc
          have hdd : d = d₀ := DecIdx.ext_q (hd.trans hq.symm)
          subst hdd
          have hb : beta M a (Sum.inr (Sum.inr (Sum.inl d))) (x, (0 : Fin (L + 1))) = 1 := by
            simp [beta, hd]
          rw [hb, Nat.cast_one, mul_one,
            if_pos (show (0 : Fin (L + 1)) = 0 ∧ d = d from ⟨rfl, rfl⟩)]
          split_ifs <;> simp
        · have hb : beta M a (Sum.inr (Sum.inr (Sum.inl d))) (x, c) = 0 := by
            simp only [beta]; rw [if_neg h]
          rw [hb, Nat.cast_zero, mul_zero, ite_self]
          exact zero_le
      calc _ ≤ (∑ c : Fin (L + 1), ∑ d : DecIdx M,
            if c = 0 ∧ d = d₀ then Wt (M := M) a σ₀ (k, (x, 0)) else 0) *
              ENNReal.ofReal (geomWeight a (L + 1)) := by
            gcongr with c _ d _
            exact hterm c d
        _ = Wt (M := M) a σ₀ (k, (x, 0)) * ENNReal.ofReal (geomWeight a (L + 1)) := by
            simp [ite_and]
        _ ≤ _ := (level_bounds (M := M) a σ₀ ha2 hL hσ₀ k hlive).2 hρ
    · have hzero : ∀ (c : Fin (L + 1)) (d : DecIdx M),
          (if k < t ∧ 1 ≤ x.2 d.1.2.1 then Wt (M := M) a σ₀ (k, (x, c)) *
            (beta M a (Sum.inr (Sum.inr (Sum.inl d))) (x, c) : ℝ≥0∞) else 0) = 0 := by
        intro c d
        by_cases h : (0 : Fin (L + 1)) = c ∧ d.1.1 = x.1
        · rw [if_neg]
          intro h'
          exact hex ⟨d, h.2, h'.2⟩
        · have hb : beta M a (Sum.inr (Sum.inr (Sum.inl d))) (x, c) = 0 := by
            simp only [beta]; rw [if_neg h]
          rw [hb, Nat.cast_zero, mul_zero, ite_self]
      simp only [hzero, Finset.sum_const_zero, zero_mul]
      exact zero_le
  · intro k hk
    rw [Finset.mem_range, not_lt] at hk
    refine ENNReal.tsum_eq_zero.mpr fun σ => Finset.sum_eq_zero fun d _ => if_neg ?_
    intro h
    exact absurd (lt_of_lt_of_le h.1 hk) (lt_irrefl k)

/-! ### The time bound -/

instance (x : Outer Reg Label) : Decidable (Live M x) := by
  unfold Live; infer_instance

/-- `z` carries a machine label that has not halted. -/
def LiveState (M : RM Reg Label) (z : State (Sp Reg Label L)) : Prop :=
  ∃ q, 1 ≤ z (Sp.st q) ∧ M.code q ≠ .halt

omit [Fintype Reg] [DecidableEq Reg] [Fintype Label] in
theorem liveState_enc (x : Outer Reg Label) (c : Fin (L + 1)) :
    LiveState M (enc a (x, c)) ↔ Live M x := by
  constructor
  · rintro ⟨q, hq, hcode⟩
    have hqx : q = x.1 := by
      by_contra h
      simp [enc, h] at hq
    subst hqx
    exact hcode
  · intro h
    exact ⟨x.1, by simp [enc], h⟩

open Classical in
/-- **Expected simulation time** of the first `t` steps: the expected total holding time in live
states before `t` machine reactions, for unit rate constants and unit volume.  `law` is the
embedded jump chain, so this is the occupation functional `E[Σ_n 1/totalPropensity(Z_n)]` over
the jumps before the target: the mean holding time at `Z_n` is `1/totalPropensity(Z_n)`. -/
noncomputable def expTime (a : ℕ) (σ₀ : RState Reg Label L) (t : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' n, (if K n ω < t ∧ LiveState M (Z a σ₀ n ω) then
    (((net M L).totalPropensity (Z a σ₀ n ω) : ℝ≥0∞))⁻¹ else 0) ∂(law M L a σ₀)

theorem expTime_eq (ha : 1 ≤ a) (hL : 1 ≤ L) (σ₀ : RState Reg Label L) (t : ℕ) :
    expTime (M := M) a σ₀ t = ∑' ξ : ℕ × RState Reg Label L,
      if ξ.1 < t ∧ Live M ξ.2.1 then Wt (M := M) a σ₀ ξ else 0 := by
  classical
  let g : ℕ × RState Reg Label L → ℝ≥0∞ := fun ξ =>
    if ξ.1 < t ∧ Live M ξ.2.1 then ((Btot M a ξ.2 : ℝ≥0∞))⁻¹ else 0
  have hcast : ∀ m : ℕ, (((m : ℚ≥0)) : ℝ≥0∞) = (m : ℝ≥0∞) := fun m => by
    rw [← ENNReal.coe_nnratCast, NNRat.cast_natCast, ENNReal.coe_natCast]
  have hpt : ∀ n (ω : Ω M L), (if K n ω < t ∧ LiveState M (Z a σ₀ n ω) then
      (((net M L).totalPropensity (Z a σ₀ n ω) : ℝ≥0∞))⁻¹ else 0) =
        ∑' ξ : ℕ × RState Reg Label L, (E (M := M) a σ₀ n ξ.1 ξ.2).indicator (fun _ => g ξ) ω := by
    intro n ω
    obtain ⟨σ, hσ⟩ := Z_enc ha hL σ₀ n ω
    rw [tsum_eq_single (K n ω, σ)]
    · rw [Set.indicator_of_mem (show ω ∈ E (M := M) a σ₀ n (K n ω, σ).1 (K n ω, σ).2 from
        ⟨rfl, hσ⟩)]
      obtain ⟨x, c⟩ := σ
      simp only [g, hσ, totalPropensity_enc, liveState_enc, hcast]
    · intro ξ hξ
      rw [Set.indicator_of_notMem]
      rintro ⟨hK, hZ⟩
      exact hξ (Prod.ext hK.symm (enc_injective a (hZ.symm.trans hσ)))
  have h1 : ∀ n, ∫⁻ ω, ∑' ξ : ℕ × RState Reg Label L,
      (E (M := M) a σ₀ n ξ.1 ξ.2).indicator (fun _ => g ξ) ω ∂(law M L a σ₀) =
        ∑' ξ : ℕ × RState Reg Label L, g ξ * law M L a σ₀ (E a σ₀ n ξ.1 ξ.2) := by
    intro n
    rw [lintegral_tsum (fun ξ : ℕ × RState Reg Label L =>
      (measurable_const.indicator (measurableSet_E a σ₀ n ξ.1 ξ.2)).aemeasurable)]
    exact tsum_congr fun ξ => lintegral_indicator_const (measurableSet_E a σ₀ n ξ.1 ξ.2) (g ξ)
  calc expTime (M := M) a σ₀ t = ∫⁻ ω, ∑' n, ∑' ξ : ℕ × RState Reg Label L,
        (E (M := M) a σ₀ n ξ.1 ξ.2).indicator (fun _ => g ξ) ω ∂(law M L a σ₀) := by
        unfold expTime
        congr 1
        funext ω
        exact tsum_congr fun n => hpt n ω
    _ = ∑' n, ∫⁻ ω, ∑' ξ : ℕ × RState Reg Label L,
        (E (M := M) a σ₀ n ξ.1 ξ.2).indicator (fun _ => g ξ) ω ∂(law M L a σ₀) :=
        lintegral_tsum (fun n => (Measurable.ennreal_tsum fun ξ : ℕ × RState Reg Label L =>
          measurable_const.indicator (measurableSet_E a σ₀ n ξ.1 ξ.2)).aemeasurable)
    _ = ∑' n, ∑' ξ : ℕ × RState Reg Label L, g ξ * law M L a σ₀ (E a σ₀ n ξ.1 ξ.2) :=
        tsum_congr h1
    _ = ∑' ξ : ℕ × RState Reg Label L, g ξ * occ (M := M) a σ₀ ξ := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun ξ => ENNReal.tsum_mul_left
    _ = _ := by
        refine tsum_congr fun ξ => ?_
        simp only [g]
        split_ifs
        · unfold Wt; rw [div_eq_mul_inv, mul_comm]
        · simp

theorem expTime_le (ha2 : 2 ≤ a) (hL : 1 ≤ L) (σ₀ : RState Reg Label L)
    (hσ₀ : σ₀.2 = Fin.last L) (t : ℕ) :
    expTime (M := M) a σ₀ t ≤ t * ENNReal.ofReal (2 * geomWeight a (L + 1)) := by
  have ha : 1 ≤ a := by omega
  rw [expTime_eq a ha hL, ENNReal.tsum_prod', tsum_eq_sum (s := Finset.range t)]
  · calc _ ≤ ∑ k ∈ Finset.range t, ENNReal.ofReal (2 * geomWeight a (L + 1)) :=
          Finset.sum_le_sum fun k hk => ?_
      _ = t * ENNReal.ofReal (2 * geomWeight a (L + 1)) := by simp
    rw [Finset.mem_range] at hk
    calc _ = ∑' x : Outer Reg Label, ∑' c : Fin (L + 1),
          (if k < t ∧ Live M x then Wt (M := M) a σ₀ (k, (x, c)) else 0) :=
          ENNReal.tsum_prod' (α := Outer Reg Label) (β := Fin (L + 1))
      _ ≤ ∑' x : Outer Reg Label, ENNReal.ofReal (2 * geomWeight a (L + 1)) *
          ∑' c : Fin (L + 1), eE (M := M) a σ₀ k (x, c) := ENNReal.tsum_le_tsum fun x => ?_
      _ = ENNReal.ofReal (2 * geomWeight a (L + 1)) * ∑' σ, eE (M := M) a σ₀ k σ := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_prod' (α := Outer Reg Label) (β := Fin (L + 1))]
      _ ≤ ENNReal.ofReal (2 * geomWeight a (L + 1)) * 1 := by
          gcongr
          exact eE_total_le_one (M := M) a σ₀ ha hL k
      _ = _ := mul_one _
    rw [tsum_fintype, tsum_fintype]
    by_cases hx : Live M x
    · simp only [hk, hx, and_self, if_true]
      exact (level_bounds (M := M) a σ₀ ha2 hL hσ₀ k hx).1
    · simp only [hx, and_false, if_false, Finset.sum_const_zero]
      exact zero_le
  · intro k hk
    rw [Finset.mem_range, not_lt] at hk
    refine ENNReal.tsum_eq_zero.mpr fun σ => if_neg ?_
    intro h
    exact absurd (lt_of_lt_of_le h.1 hk) (lt_irrefl k)

/-! ### Completion -/

/-- **Completion of the first `t` steps** along `ω` (liveness): after some jump, `t` machine
reactions have fired, or the encoded machine is halted (no state molecule `S_q` with
`code q ≠ halt`). -/
def Completes (a : ℕ) (σ₀ : RState Reg Label L) (t : ℕ) (ω : Ω M L) : Prop :=
  ∃ n, t ≤ K n ω ∨ ¬ LiveState M (Z a σ₀ n ω)

/-- **Correct and complete simulation of the first `t` steps**: after every jump the state
encodes the configuration of `M` after the machine reactions fired so far (`SimOK`), and the run
fires `t` machine reactions or halts (`Completes`).  At the first jump `n` with `K n ω = t` the
state is `enc a (x, c)` with `cfgAt M x₀ t = some x`; at a jump with the machine halted it is
`enc a (x, c)` with `cfgAt M x₀ (K n ω) = some x` and `code x.1 = halt`. -/
def Simulates (a : ℕ) (σ₀ : RState Reg Label L) (x₀ : Outer Reg Label) (t : ℕ)
    (ω : Ω M L) : Prop :=
  SimOK a σ₀ x₀ t ω ∧ Completes a σ₀ t ω

/-- The largest total propensity of an encoded configuration among the first `t` steps of `M`
from `x₀`, over all clock positions. -/
noncomputable def propBound (M : RM Reg Label) (L : ℕ) (a : ℕ) (x₀ : Outer Reg Label)
    (t : ℕ) : ℕ :=
  (Finset.range (t + 1) ×ˢ (Finset.univ : Finset (Fin (L + 1)))).sup
    fun p => Btot M a ((cfgAt M x₀ p.1).getD x₀, p.2)

theorem Btot_le_propBound (x₀ : Outer Reg Label) (t : ℕ) {k : ℕ} (hk : k ≤ t)
    {x : Outer Reg Label} (hx : cfgAt M x₀ k = some x) (c : Fin (L + 1)) :
    Btot M a (x, c) ≤ propBound M L a x₀ t := by
  have hmem : (k, c) ∈ Finset.range (t + 1) ×ˢ (Finset.univ : Finset (Fin (L + 1))) := by
    rw [Finset.mem_product, Finset.mem_range]
    exact ⟨by omega, Finset.mem_univ _⟩
  have := Finset.le_sup (f := fun p : ℕ × Fin (L + 1) =>
    Btot M a ((cfgAt M x₀ p.1).getD x₀, p.2)) hmem
  simpa [hx] using this

/-- **A correct run completes with probability one.** The event "every state so far is a
correct encoding, but the run never fires `t` machine reactions and never halts" is null: on it
every jump costs at least `1 / propBound` of expected holding time, while `expTime` is finite. -/
theorem law_simOK_not_completes (ha2 : 2 ≤ a) (hL : 1 ≤ L) (x₀ : Outer Reg Label) (t : ℕ) :
    law M L a (x₀, Fin.last L)
      {ω | SimOK a (x₀, Fin.last L) x₀ t ω ∧ ¬ Completes a (x₀, Fin.last L) t ω} = 0 := by
  classical
  let g : ℕ → Ω M L → ℝ≥0∞ := fun n ω =>
    if K n ω < t ∧ LiveState M (Z a (x₀, Fin.last L) n ω) then
      (((net M L).totalPropensity (Z a (x₀, Fin.last L) n ω) : ℝ≥0∞))⁻¹ else 0
  have hg : ∀ n, Measurable (g n) := fun n =>
    measurable_of_frestrictLe (net M L) n (g n) fun ω ω' h => by
      simp only [g, K_det n h, Z_det a (x₀, Fin.last L) n h]
  have hfin : ∫⁻ ω, ∑' n, g n ω ∂(law M L a (x₀, Fin.last L)) ≠ ⊤ := by
    have h := expTime_le (M := M) a ha2 hL (x₀, Fin.last L) rfl t
    unfold expTime at h
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top t)
      ENNReal.ofReal_ne_top) h
  have hcast : ∀ m : ℕ, (((m : ℚ≥0)) : ℝ≥0∞) = (m : ℝ≥0∞) := fun m => by
    rw [← ENNReal.coe_nnratCast, NNRat.cast_natCast, ENNReal.coe_natCast]
  refine measure_mono_null ?_ (measure_tsum_eq_top g hg hfin)
  rintro ω ⟨hok, hnc⟩
  simp only [Completes, not_exists, not_or, not_le, not_not] at hnc
  change ∑' n, g n ω = ⊤
  refine tsum_eq_top_of_le (ε := ((propBound M L a x₀ t : ℝ≥0∞))⁻¹)
    (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)) fun n => ?_
  obtain ⟨hKt, hlive⟩ := hnc n
  obtain ⟨x, c, hcfg, hZ⟩ := hok n hKt.le
  simp only [g, if_pos (And.intro hKt hlive), hZ, totalPropensity_enc, hcast]
  exact ENNReal.inv_le_inv.mpr (by exact_mod_cast Btot_le_propBound a x₀ t hKt.le hcfg c)

/-! ### The theorems -/

/-- The safety half of Theorem 3.1′: the probability that some state before `t` machine
reactions is not a correct encoding is at most `t / G`. -/
theorem law_not_simOK_le (M : RM Reg Label) (L : ℕ) (hL : 1 ≤ L) (a : ℕ) (ha2 : 2 ≤ a)
    (x₀ : Outer Reg Label) (t : ℕ) :
    law M L a (x₀, Fin.last L) {ω | ¬ SimOK a (x₀, Fin.last L) x₀ t ω} ≤
      ENNReal.ofReal (t / geomWeight a (L + 1)) := by
  have ha : 1 ≤ a := by omega
  have hG1 := one_le_geomWeight (L := L) (a : ℝ) (Nat.cast_nonneg _)
  have hGpos : 0 < geomWeight (a : ℝ) (L + 1) := by linarith
  have hsub : {ω : Ω M L | ¬ SimOK a (x₀, Fin.last L) x₀ t ω} ⊆
      Err a (x₀, Fin.last L) t ∪ Null a (x₀, Fin.last L) := by
    intro ω hω
    by_contra h
    simp only [Set.mem_union, not_or] at h
    exact hω (simOK_of_not_mem a ha hL x₀ t ω h.1 h.2)
  calc _ ≤ law M L a (x₀, Fin.last L) (Err a (x₀, Fin.last L) t ∪ Null a (x₀, Fin.last L)) :=
        measure_mono hsub
    _ ≤ law M L a (x₀, Fin.last L) (Err a (x₀, Fin.last L) t) +
        law M L a (x₀, Fin.last L) (Null a (x₀, Fin.last L)) := measure_union_le _ _
    _ = law M L a (x₀, Fin.last L) (Err a (x₀, Fin.last L) t) := by
        rw [law_Null a ha hL, add_zero]
    _ ≤ _ := law_Err_le a ha hL _ t
    _ ≤ _ := by
        rw [ENNReal.ofReal_div_of_pos hGpos, ENNReal.ofReal_natCast,
          ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hGpos).ne')
            (Or.inl ENNReal.ofReal_ne_top)]
        exact errSum_mul_le a ha2 hL _ rfl t

/-- **SCWB Theorem 3.1′** (FIX3-SCWB §3): for the fixed network `net M L` with clock length
`L + 1 ≥ 2`, initial clock at the top and `a ≥ 2` molecules of `A`, the probability that the first
`t` steps are not simulated correctly and completely (`Simulates`: every state encodes the right
configuration, and the run fires `t` machine reactions or halts) is at most `t / G`, and the
expected simulation time is at most `2 t G`, where `G = 1 + a + ⋯ + a^L`. -/
theorem theorem_3_1_general (M : RM Reg Label) (L : ℕ) (hL : 1 ≤ L) (a : ℕ) (ha2 : 2 ≤ a)
    (x₀ : Outer Reg Label) (t : ℕ) :
    law M L a (x₀, Fin.last L) {ω | ¬ Simulates a (x₀, Fin.last L) x₀ t ω} ≤
        ENNReal.ofReal (t / geomWeight a (L + 1)) ∧
      expTime (M := M) a (x₀, Fin.last L) t ≤ ENNReal.ofReal (2 * t * geomWeight a (L + 1)) := by
  constructor
  · have hsub : {ω : Ω M L | ¬ Simulates a (x₀, Fin.last L) x₀ t ω} ⊆
        {ω | ¬ SimOK a (x₀, Fin.last L) x₀ t ω} ∪
          {ω | SimOK a (x₀, Fin.last L) x₀ t ω ∧ ¬ Completes a (x₀, Fin.last L) t ω} := by
      intro ω hω
      by_cases h : SimOK a (x₀, Fin.last L) x₀ t ω
      · exact Or.inr ⟨h, fun hc => hω ⟨h, hc⟩⟩
      · exact Or.inl h
    calc _ ≤ _ := measure_mono hsub
      _ ≤ law M L a (x₀, Fin.last L) {ω | ¬ SimOK a (x₀, Fin.last L) x₀ t ω} +
          law M L a (x₀, Fin.last L)
            {ω | SimOK a (x₀, Fin.last L) x₀ t ω ∧ ¬ Completes a (x₀, Fin.last L) t ω} :=
          measure_union_le _ _
      _ = law M L a (x₀, Fin.last L) {ω | ¬ SimOK a (x₀, Fin.last L) x₀ t ω} := by
          rw [law_simOK_not_completes a ha2 hL x₀ t, add_zero]
      _ ≤ _ := law_not_simOK_le M L hL a ha2 x₀ t
  · calc _ ≤ t * ENNReal.ofReal (2 * geomWeight a (L + 1)) := expTime_le a ha2 hL _ rfl t
      _ = _ := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          ring

/-- **SCWB Theorem 3.1.** For every register machine `M` the network `net M 1` (Fig. 3.1, clock
length `2`) is fixed; then for every error bound `δ ∈ (0, 1]`, every input `y₀` and every step
bound `t ≥ 1` there is an initial count `a` of `A` such that, with probability at least `1 - δ`,
the first `t` steps are simulated correctly and completely (`Simulates`: every state along the
run encodes the configuration of `M` after the machine reactions fired so far, and the run fires
`t` machine reactions or `M` halts earlier), in expected time at most `6 v t² / (k δ)` for rate
constant `k` and volume `v` (`expTime`: the expected holding-time functional of the embedded jump
chain `law`). -/
theorem scwb_theorem_3_1 (M : RM Reg Label) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ (y₀ : Reg → ℕ) (t : ℕ), 1 ≤ t → ∃ a : ℕ,
      law M 1 a ((M.start, y₀), Fin.last 1)
          {ω | ¬ Simulates a ((M.start, y₀), Fin.last 1) (M.start, y₀) t ω} ≤
        ENNReal.ofReal δ ∧
        ∀ v k : ℝ, 0 < v → 0 < k →
          ENNReal.ofReal (v / k) * expTime (M := M) a ((M.start, y₀), Fin.last 1) t ≤
            ENNReal.ofReal (6 * v * t ^ 2 / (k * δ)) := by
  intro δ hδ hδ1 y₀ t ht
  refine ⟨max 2 ⌈(t : ℝ) / δ⌉₊, ?_⟩
  obtain ⟨herr, htime⟩ := theorem_3_1_general M 1 le_rfl (max 2 ⌈(t : ℝ) / δ⌉₊)
    (le_max_left _ _) (M.start, y₀) t
  set a := max 2 ⌈(t : ℝ) / δ⌉₊ with ha_def
  have hG : geomWeight (a : ℝ) (1 + 1) = 1 + a := by
    simp [geomWeight, Finset.sum_range_succ]
  rw [hG] at herr htime
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htd : (t : ℝ) / δ ≤ a := by
    rw [ha_def]
    push_cast
    exact le_trans (Nat.le_ceil _) (le_max_right _ _)
  have htd1 : 1 ≤ (t : ℝ) / δ := by rw [le_div_iff₀ hδ]; linarith
  have ha_le : (a : ℝ) ≤ max 2 ((t : ℝ) / δ + 1) := by
    rw [ha_def]
    push_cast
    exact max_le_max le_rfl (Nat.ceil_lt_add_one (by positivity)).le
  have h1a : 1 + (a : ℝ) ≤ 3 * ((t : ℝ) / δ) := by
    rcases le_total 2 ((t : ℝ) / δ + 1) with h | h
    · rw [max_eq_right h] at ha_le; linarith
    · rw [max_eq_left h] at ha_le; linarith
  refine ⟨herr.trans (ENNReal.ofReal_le_ofReal ?_), fun v k hv hk => ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have := (div_le_iff₀ hδ).mp htd
    nlinarith
  · have hkey : 2 * (t : ℝ) * (1 + a) ≤ 6 * t ^ 2 / δ := by
      calc 2 * (t : ℝ) * (1 + a) ≤ 2 * t * (3 * ((t : ℝ) / δ)) := by gcongr
        _ = 6 * t ^ 2 / δ := by ring
    calc ENNReal.ofReal (v / k) * expTime (M := M) a ((M.start, y₀), Fin.last 1) t
        ≤ ENNReal.ofReal (v / k) * ENNReal.ofReal (2 * t * (1 + a)) := by gcongr
      _ = ENNReal.ofReal (v / k * (2 * t * (1 + a))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (v / k * (6 * t ^ 2 / δ)) := by
          apply ENNReal.ofReal_le_ofReal
          gcongr
      _ = ENNReal.ofReal (6 * v * t ^ 2 / (k * δ)) := by
          congr 1
          field_simp

end Ripple.sCRNUniversality.RegisterMachine.Clocked
