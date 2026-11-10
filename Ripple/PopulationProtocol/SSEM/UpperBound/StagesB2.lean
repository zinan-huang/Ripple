/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage B2: leader election among dormant agents (P3 Lemma 10 (B2), P2 Lemma 7.2)

From `FD_L^{½}` (all agents dormant with delay timers `≥ 16 n + 1`, some leader), within
`t₂ = 4 n (n - 1)` interactions the configuration is fully dormant with exactly one leader, with
probability `≥ 3/4 - 1/n²` (`stageB2`); answers are kept when they are all non-`φ`
(`stageB2M`, from `FD_L^{½} ∩ AllMaj` to `FD_1 ∩ AllMaj`).

* `pem_step_dormant`: one step between two dormant agents with delay timers `≥ 2` only
  decrements both delay timers, deduplicates leaders, and runs the answer epidemic.
* `dormant_run`: while every agent has had fewer than `16 n` interactions, all agents stay
  dormant with `delaytimer + count ≥ 16 n + 1` (P2 Lemma 2.4(d)).
* Leader chain: with `ℓ` leaders, `ℓ (ℓ - 1)` ordered pairs remove one; the potential
  `Φ = Σ_{k=2}^{ℓ} n(n-1)/(k(k-1)) ≤ n(n-1)` drops by exactly one per step in expectation, so the
  guarded additive drift (`probNotHitBy_window_le_drift_guarded`) gives
  `P[no single leader by 4 n (n-1)] ≤ 1/4 + P[some agent has ≥ 16 n interactions]`.
* The interaction-count tail uses base 2: `2^D · P[cnt ≥ D] ≤ (1 + 2/n)^K`.
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.StagesB1
import Ripple.PopulationProtocol.SSEM.Probability.PrefixGuarded

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped BigOperators ENNReal

variable {n : ℕ}

/-! ### One step between two dormant agents -/

theorem preAgent_of_resetting (trank : ℕ) {s r : AgentState n} (hs : s.role = .Resetting)
    (hr : r.role = .Resetting) : preAgent n trank s r = r := by
  unfold preAgent
  simp [hs, hr]

theorem preEpi_eq_of_ne_phi {a₀ a₁ : AgentState n} (h₀ : a₀.answer ≠ .phi)
    (h₁ : a₁.answer ≠ .phi) : preEpi a₀ a₁ = (a₀, a₁) := by
  unfold preEpi
  simp [h₀, h₁]

theorem preEpi_dt_leader (a₀ a₁ : AgentState n) :
    (preEpi a₀ a₁).1.delaytimer = a₀.delaytimer ∧ (preEpi a₀ a₁).2.delaytimer = a₁.delaytimer ∧
      (preEpi a₀ a₁).1.leader = a₀.leader ∧ (preEpi a₀ a₁).2.leader = a₁.leader := by
  unfold preEpi
  split_ifs <;> simp

/-- **One P_EM step between two dormant agents** with delay timers at least `2`. -/
theorem pem_step_dormant {trank R Emax Dmax : ℕ} {hn : 0 < n} (a b : AgentState n)
    (x₀ x₁ : Opinion) (ha : a.role = .Resetting) (hb : b.role = .Resetting)
    (hra : a.resetcount = 0) (hrb : b.resetcount = 0) (hda : 2 ≤ a.delaytimer)
    (hdb : 2 ≤ b.delaytimer) :
    transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁)) =
      preEpi { a with resetcount := 0, delaytimer := a.delaytimer - 1 }
        (if a.leader = .L ∧ b.leader = .L then
          { b with resetcount := 0, delaytimer := b.delaytimer - 1, leader := .F }
        else { b with resetcount := 0, delaytimer := b.delaytimer - 1 }) := by
  have hrec : prRecruit Dmax a b = (a, b) := by simp [prRecruit, ha, hb]
  have hsync : prSync a b = ({ a with resetcount := 0 }, { b with resetcount := 0 }) := by
    simp [prSync, ha, hb, hra, hrb]
  have hpa : processAgent Emax Dmax hn { a with resetcount := 0 } a.resetcount true =
      { a with resetcount := 0, delaytimer := a.delaytimer - 1 } := by
    have : a.delaytimer - 1 ≠ 0 := by omega
    simp [processAgent, ha, hra, this]
  have hpb : processAgent Emax Dmax hn { b with resetcount := 0 } b.resetcount true =
      { b with resetcount := 0, delaytimer := b.delaytimer - 1 } := by
    have : b.delaytimer - 1 ≠ 0 := by omega
    simp [processAgent, hb, hrb, this]
  have hrd' : rankDeltaOSSR R Emax Dmax hn (a, b) =
      prDedup (processAgent Emax Dmax hn { a with resetcount := 0 } a.resetcount true,
        processAgent Emax Dmax hn { b with resetcount := 0 } b.resetcount true) := by
    rw [rankDeltaOSSR_eq_of_resetting (Or.inl ha), propagateReset_eq, hrec, hsync]
    simp [hb, ha]
  have hrd : rankDeltaOSSR R Emax Dmax hn (a, b) =
      ({ a with resetcount := 0, delaytimer := a.delaytimer - 1 },
        if a.leader = .L ∧ b.leader = .L then
          { b with resetcount := 0, delaytimer := b.delaytimer - 1, leader := .F }
        else { b with resetcount := 0, delaytimer := b.delaytimer - 1 }) := by
    rw [hrd', hpa, hpb]
    unfold prDedup
    by_cases hL : a.leader = .L ∧ b.leader = .L
    · simp [hL, ha, hb]
    · simp only [ha, hb, and_true]
      try rw [if_neg hL, if_neg hL]
  rw [transitionPEM_eq]
  have hnot : ¬ ((transitionPEM_prePhase4 n trank (rankDeltaOSSR R Emax Dmax hn) a b x₀ x₁).1.role =
      .Settled ∧ (transitionPEM_prePhase4 n trank (rankDeltaOSSR R Emax Dmax hn) a b x₀ x₁).2.role =
      .Settled) := by
    rw [prePhase4_eq, hrd]
    rintro ⟨h, -⟩
    rw [(preEpi_role_rc _ _).1, (preAgent_role_rc _ _ _).1] at h
    simp [ha] at h
  rw [transitionPEM_phase4_of_not_both_settled hnot, prePhase4_eq, hrd]
  dsimp only
  rw [preAgent_of_resetting trank ha (by simp [ha]), preAgent_of_resetting trank hb (by
    split_ifs <;> simp [hb])]

/-- Field-level form of `pem_step_dormant`. -/
theorem pem_step_dormant_fields {trank R Emax Dmax : ℕ} {hn : 0 < n} (a b : AgentState n)
    (x₀ x₁ : Opinion) (ha : a.role = .Resetting) (hb : b.role = .Resetting)
    (hra : a.resetcount = 0) (hrb : b.resetcount = 0) (hda : 2 ≤ a.delaytimer)
    (hdb : 2 ≤ b.delaytimer) :
    (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.role =
        .Resetting ∧
      (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.resetcount =
        0 ∧
      (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.delaytimer =
        a.delaytimer - 1 ∧
      (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.leader =
        a.leader ∧
      (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.role =
        .Resetting ∧
      (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.resetcount =
        0 ∧
      (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.delaytimer =
        b.delaytimer - 1 ∧
      (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.leader =
        (if a.leader = .L ∧ b.leader = .L then .F else b.leader) ∧
      (a.answer ≠ .phi → b.answer ≠ .phi →
        (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.answer =
          a.answer ∧
        (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.answer =
          b.answer) := by
  rw [pem_step_dormant a b x₀ x₁ ha hb hra hrb hda hdb]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h0 h1 => ?_⟩
  all_goals first
    | (rw [preEpi_eq_of_ne_phi (by simpa using h0) (by split_ifs <;> simpa using h1)]
       split_ifs <;> simp)
    | (unfold preEpi; split_ifs <;> simp_all)

/-! ### Runs among dormant agents -/

/-- The guard: every agent has had at most `16 n - 1` interactions. -/
def CntGuard (n : ℕ) (K : ℕ) (σ : SchedulerPrefix n K) : Prop := ∀ v, cntIter K σ v + 1 ≤ 16 * n

theorem cntGuard_init (K : ℕ) (σ : SchedulerPrefix n K) (p : Fin n × Fin n)
    (h : CntGuard n (K + 1) (Fin.snoc σ p)) : CntGuard n K σ := by
  intro v
  have h1 := cntIter_succ_ge K (Fin.snoc σ p) v
  rw [Fin.init_snoc] at h1
  have := h v
  omega

/-- **Dormant runs**: from `FD` with delay timers `≥ 16 n + 1`, while the guard holds every agent
stays dormant with `delaytimer + count ≥ 16 n + 1`, and non-`φ` answers do not change. -/
theorem dormant_run {hn : 0 < n} (X : Config (AgentState n) Opinion n)
    (hX : ∀ v, (X v).1.role = .Resetting ∧ (X v).1.resetcount = 0 ∧
      16 * n + 1 ≤ (X v).1.delaytimer) :
    ∀ K (σ : SchedulerPrefix n K), CntGuard n K σ → ∀ v,
      (runPrefix (PEM40 n hn) X K σ v).1.role = .Resetting ∧
      (runPrefix (PEM40 n hn) X K σ v).1.resetcount = 0 ∧
      16 * n + 1 ≤ (runPrefix (PEM40 n hn) X K σ v).1.delaytimer + cntIter K σ v ∧
      ((∀ w, (X w).1.answer ≠ .phi) → (runPrefix (PEM40 n hn) X K σ v).1.answer = (X v).1.answer)
  | 0, σ, _, v => ⟨(hX v).1, (hX v).2.1,
      by have := (hX v).2.2; simp [cntIter, prefixIter]; omega, fun _ => rfl⟩
  | K + 1, σ, hc, v => by
      have hc' : CntGuard n K (Fin.init σ) := by
        have := cntGuard_init K (Fin.init σ) (σ (Fin.last K))
        rw [Fin.snoc_init_self] at this
        exact this hc
      have ih := dormant_run (hn := hn) X hX K (Fin.init σ) hc'
      have hcK := hc
      simp only [CntGuard, cntIter, prefixIter_succ, cntStep] at hcK
      simp only [runPrefix_succ, cntIter, prefixIter_succ, cntStep]
      simp only [cntIter] at ih
      generalize σ (Fin.last K) = p at hcK ⊢
      obtain ⟨a, b⟩ := p
      generalize runPrefix (PEM40 n hn) X K (Fin.init σ) = C at ih ⊢
      generalize prefixIter (fun _ => 0) cntStep K (Fin.init σ) = c at ih hcK ⊢
      simp only
      by_cases hab : a = b
      · subst hab
        have hC : C.step (PEM40 n hn) a a = C := by simp [Config.step]
        have hnot : ∀ w, (a, a) ∉ PairsInvolving n w := by
          intro w h; exact ((mem_PairsInvolving n w (a, a)).mp h).1 rfl
        rw [hC]
        simp only [hnot, if_false]
        exact ih v
      · have hmemA : (a, b) ∈ PairsInvolving n a :=
          (mem_PairsInvolving n a (a, b)).mpr ⟨hab, Or.inl rfl⟩
        have hmemB : (a, b) ∈ PairsInvolving n b :=
          (mem_PairsInvolving n b (a, b)).mpr ⟨hab, Or.inr rfl⟩
        have hca : c a + 2 ≤ 16 * n := by have := hcK a; rw [if_pos hmemA] at this; omega
        have hcb : c b + 2 ≤ 16 * n := by have := hcK b; rw [if_pos hmemB] at this; omega
        have hda : 2 ≤ (C a).1.delaytimer := by have := (ih a).2.2.1; omega
        have hdb : 2 ≤ (C b).1.delaytimer := by have := (ih b).2.2.1; omega
        obtain ⟨A1, A2, A3, -, B1, B2, B3, -, AB⟩ := pem_step_dormant_fields (trank := 40)
          (R := rmaxPaper n) (Emax := 208 * n) (Dmax := 32 * n) (hn := hn) (C a).1 (C b).1
          (C a).2 (C b).2 (ih a).1 (ih b).1 (ih a).2.1 (ih b).2.1 hda hdb
        have hstep : ∀ w, (C.step (PEM40 n hn) a b) w =
            if w = a then ((transitionPEM n 40 (rmaxPaper n)
                (rankDeltaOSSR (rmaxPaper n) (208 * n) (32 * n) hn) ((C a), (C b))).1, (C a).2)
            else if w = b then ((transitionPEM n 40 (rmaxPaper n)
                (rankDeltaOSSR (rmaxPaper n) (208 * n) (32 * n) hn) ((C a), (C b))).2, (C b).2)
            else C w := by
          intro w
          simp only [Config.step, hab, if_false]
          rfl
        rw [hstep]
        by_cases hwa : v = a
        · subst hwa
          rw [if_pos rfl, if_pos hmemA]
          refine ⟨A1, A2, by rw [A3]; have := (ih v).2.2.1; omega, fun hphi => ?_⟩
          have hav : (C v).1.answer = (X v).1.answer := (ih v).2.2.2 hphi
          have hbv : (C b).1.answer = (X b).1.answer := (ih b).2.2.2 hphi
          rw [(AB (by rw [hav]; exact hphi v) (by rw [hbv]; exact hphi b)).1]
          exact hav
        · by_cases hwb : v = b
          · subst hwb
            rw [if_neg hwa, if_pos rfl, if_pos hmemB]
            refine ⟨B1, B2, by rw [B3]; have := (ih v).2.2.1; omega, fun hphi => ?_⟩
            have hav : (C a).1.answer = (X a).1.answer := (ih a).2.2.2 hphi
            have hbv : (C v).1.answer = (X v).1.answer := (ih v).2.2.2 hphi
            rw [(AB (by rw [hav]; exact hphi a) (by rw [hbv]; exact hphi v)).2]
            exact hbv
          · have hnv : (a, b) ∉ PairsInvolving n v := by
              intro h
              rcases ((mem_PairsInvolving n v (a, b)).mp h).2 with h' | h'
              · exact hwa h'.symm
              · exact hwb h'.symm
            rw [if_neg hwa, if_neg hwb, if_neg hnv]
            exact ih v

/-! ### Leader sets -/

/-- All agents dormant with delay timers `≥ 2`. -/
def NiceDormant (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ v, (C v).1.role = .Resetting ∧ (C v).1.resetcount = 0 ∧ 2 ≤ (C v).1.delaytimer

theorem leaderSet_step {hn : 0 < n} (C : Config (AgentState n) Opinion n) (hC : NiceDormant C)
    (i j : Fin n) (hij : i ≠ j) :
    leaderSet (C.step (PEM40 n hn) i j) =
      if i ∈ leaderSet C ∧ j ∈ leaderSet C then (leaderSet C).erase j else leaderSet C := by
  obtain ⟨-, -, -, F1, -, -, -, F2, -⟩ := pem_step_dormant_fields (trank := 40)
    (R := rmaxPaper n) (Emax := 208 * n) (Dmax := 32 * n) (hn := hn) (C i).1 (C j).1 (C i).2
    (C j).2 (hC i).1 (hC j).1 (hC i).2.1 (hC j).2.1 (hC i).2.2 (hC j).2.2
  have hstep : ∀ w, (C.step (PEM40 n hn) i j) w =
      if w = i then ((transitionPEM n 40 (rmaxPaper n)
          (rankDeltaOSSR (rmaxPaper n) (208 * n) (32 * n) hn) ((C i), (C j))).1, (C i).2)
      else if w = j then ((transitionPEM n 40 (rmaxPaper n)
          (rankDeltaOSSR (rmaxPaper n) (208 * n) (32 * n) hn) ((C i), (C j))).2, (C j).2)
      else C w := by
    intro w
    simp only [Config.step, hij, if_false]
    rfl
  ext w
  simp only [leaderSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hstep w]
  by_cases hwi : w = i
  · subst hwi
    rw [if_pos rfl]
    simp only
    rw [F1]
    split_ifs with h
    · simp [Finset.mem_erase, hij, h.1]
    · simp
  · by_cases hwj : w = j
    · subst hwj
      rw [if_neg hwi, if_pos rfl]
      simp only
      rw [F2]
      by_cases h : (C i).1.leader = .L ∧ (C w).1.leader = .L
      · rw [if_pos h, if_pos (by simp [h.1, h.2])]
        simp
      · rw [if_neg h, if_neg (by simpa using h)]
        simp
    · rw [if_neg hwi, if_neg hwj]
      split_ifs <;> simp [Finset.mem_erase, hwj]

/-! ### The leader potential -/

/-- `g k = n(n-1) / (k(k-1))`. -/
noncomputable def leaderGap (n k : ℕ) : ℝ≥0∞ := ((n * (n - 1) : ℕ) : ℝ≥0∞) / ((k * (k - 1) : ℕ) : ℝ≥0∞)

/-- `Φ(ℓ) = Σ_{k=2}^{ℓ} n(n-1)/(k(k-1))`. -/
noncomputable def leaderPot (n ℓ : ℕ) : ℝ≥0∞ := ∑ k ∈ Finset.Icc 2 ℓ, leaderGap n k

theorem leaderPot_succ (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    leaderPot n (ℓ + 1) = leaderPot n ℓ + leaderGap n (ℓ + 1) := by
  unfold leaderPot
  rw [Finset.sum_Icc_succ_top (by omega)]

theorem sum_inv_telescope : ∀ m : ℕ, 1 ≤ m →
    ∑ k ∈ Finset.Icc 2 m, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) = 1 - 1 / m
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simp
  | m + 2, _ => by
      rw [Finset.sum_Icc_succ_top (by omega), sum_inv_telescope (m + 1) (by omega)]
      push_cast
      field_simp
      ring

theorem leaderPot_le (ℓ : ℕ) : leaderPot n ℓ ≤ ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
  rcases Nat.eq_zero_or_pos ℓ with h | h
  · subst h; simp [leaderPot]
  have hreal : leaderPot n ℓ = ENNReal.ofReal (((n * (n - 1) : ℕ) : ℝ) *
      ∑ k ∈ Finset.Icc 2 ℓ, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1))) := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
    · unfold leaderPot
      apply Finset.sum_congr rfl
      intro k hk
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have hpos : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := by
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
        nlinarith
      unfold leaderGap
      rw [mul_one_div, ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast]
      congr 1
      rw [show (k : ℝ) * ((k : ℝ) - 1) = ((k * (k - 1) : ℕ) : ℝ) by
        rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring, ENNReal.ofReal_natCast]
    · intro k hk
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      have : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
      positivity
  rw [hreal, sum_inv_telescope ℓ h, ← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  have : (0 : ℝ) ≤ 1 / (ℓ : ℝ) := by positivity
  have : (0 : ℝ) ≤ ((n * (n - 1) : ℕ) : ℝ) := by positivity
  nlinarith

/-- **Drift of the leader potential**: one expected unit per step while `ℓ ≥ 2`. -/
theorem leaderPot_drift {hn : 0 < n} (hn2 : 2 ≤ n) (C : Config (AgentState n) Opinion n)
    (hC : NiceDormant C) (h2 : 2 ≤ (leaderSet C).card) :
    ∑ p : Fin n × Fin n, uniformPair n hn2 p *
        leaderPot n (leaderSet (C.step (PEM40 n hn) p.1 p.2)).card + 1 ≤
      leaderPot n (leaderSet C).card := by
  classical
  set S := leaderSet C
  set ℓ := S.card
  set LL := S.offDiag
  have hpt : ∀ p : Fin n × Fin n, leaderPot n (leaderSet (C.step (PEM40 n hn) p.1 p.2)).card =
      leaderPot n (ℓ - 1) + if p ∈ LL then 0 else leaderGap n ℓ := by
    intro p
    have hsucc : leaderPot n ℓ = leaderPot n (ℓ - 1) + leaderGap n ℓ := by
      have := leaderPot_succ (n := n) (ℓ - 1) (by omega)
      rwa [Nat.sub_add_cancel (by omega)] at this
    by_cases hp : p.1 = p.2
    · have hC' : C.step (PEM40 n hn) p.1 p.2 = C := by simp [Config.step, hp]
      have hpLL : p ∉ LL := by simp [LL, Finset.mem_offDiag, hp]
      rw [hC', if_neg hpLL]
      exact hsucc
    · rw [leaderSet_step C hC p.1 p.2 hp]
      by_cases hin : p.1 ∈ S ∧ p.2 ∈ S
      · have hpLL : p ∈ LL := by
          simp only [LL, Finset.mem_offDiag]; exact ⟨hin.1, hin.2, hp⟩
        rw [if_pos hin, if_pos hpLL, Finset.card_erase_of_mem hin.2, add_zero]
      · have hpLL : p ∉ LL := by
          simp only [LL, Finset.mem_offDiag, not_and]; exact fun h1 h2 _ => hin ⟨h1, h2⟩
        rw [if_neg hin, if_neg hpLL]
        exact hsucc
  have hsum1 := uniformPair_sum_one hn2
  have hLLsub : LL ⊆ OffDiagonalPairs n := by
    intro p hp
    rw [mem_offDiagonalPairs]
    exact (Finset.mem_offDiag.mp hp).2.2
  have hmassLL : ∑ p ∈ LL, uniformPair n hn2 p =
      ((ℓ * (ℓ - 1) : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ := by
    have := pairSetMass_eq_card_mul_inv_of_subset n hn2 LL hLLsub
    unfold pairSetMass at this
    rw [this, Finset.offDiag_card]
    congr 2
    rw [Nat.mul_sub_one]
  have hN0 : ((n * (n - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this.ne'
  have hM0 : ((ℓ * (ℓ - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    have : 0 < ℓ * (ℓ - 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this.ne'
  have hone : leaderGap n ℓ * ∑ p ∈ LL, uniformPair n hn2 p = 1 := by
    rw [hmassLL, leaderGap, div_eq_mul_inv]
    calc ((n * (n - 1) : ℕ) : ℝ≥0∞) * ((ℓ * (ℓ - 1) : ℕ) : ℝ≥0∞)⁻¹ *
          (((ℓ * (ℓ - 1) : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹)
        = (((n * (n - 1) : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹) *
          (((ℓ * (ℓ - 1) : ℕ) : ℝ≥0∞) * ((ℓ * (ℓ - 1) : ℕ) : ℝ≥0∞)⁻¹) := by ring
      _ = 1 := by
          rw [ENNReal.mul_inv_cancel hN0 (ENNReal.natCast_ne_top _),
            ENNReal.mul_inv_cancel hM0 (ENNReal.natCast_ne_top _), one_mul]
  rw [Finset.sum_congr rfl (fun p _ => by rw [hpt p]), ← hone]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum1, one_mul]
  have hsplit : ∑ p : Fin n × Fin n, uniformPair n hn2 p * (if p ∈ LL then 0 else leaderGap n ℓ) =
      leaderGap n ℓ * ∑ p ∈ Finset.univ \ LL, uniformPair n hn2 p := by
    rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ LL)]
    rw [Finset.sum_eq_zero (fun p hp => by
      rw [if_pos (Finset.mem_filter.mp hp).2, mul_zero]), zero_add]
    rw [show Finset.univ \ LL = Finset.univ.filter (fun p => p ∉ LL) by ext; simp]
    apply Finset.sum_congr rfl
    intro p hp
    rw [if_neg (Finset.mem_filter.mp hp).2, mul_comm]
  rw [hsplit, add_assoc, ← mul_add, Finset.sum_sdiff (Finset.subset_univ LL), hsum1, mul_one]
  have hsucc : leaderPot n ℓ = leaderPot n (ℓ - 1) + leaderGap n ℓ := by
    have := leaderPot_succ (n := n) (ℓ - 1) (by omega)
    rwa [Nat.sub_add_cancel (by omega)] at this
  rw [hsucc]

/-! ### Interaction counts with base 2 -/

theorem uniformPair_sum_two_pow (hn : 2 ≤ n) (v : Fin n) :
    ∑ p : Fin n × Fin n, uniformPair n hn p * (if p ∈ PairsInvolving n v then 2 else 1) =
      1 + 2 * (n : ℝ≥0∞)⁻¹ := by
  classical
  have h1 : ∀ p : Fin n × Fin n, uniformPair n hn p * (if p ∈ PairsInvolving n v then 2 else 1) =
      uniformPair n hn p + (if p ∈ PairsInvolving n v then uniformPair n hn p else 0) := by
    intro p
    split_ifs
    · rw [show (2 : ℝ≥0∞) = 1 + 1 by norm_num, mul_add, mul_one]
    · rw [mul_one, add_zero]
  rw [Finset.sum_congr rfl (fun p _ => h1 p), Finset.sum_add_distrib, uniformPair_sum_one hn,
    ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have := pairSetMass_pairsInvolving n hn v
  unfold pairSetMass at this
  rw [this]

theorem count_tail_two_le (hn : 2 ≤ n) (v : Fin n) (K D : ℕ) :
    2 ^ D * (schedulerPrefixPMF n hn K).toOuterMeasure {σ | D ≤ cntIter K σ v} ≤
      (1 + 2 * (n : ℝ≥0∞)⁻¹) ^ K := by
  classical
  have hE := schedulerPrefix_expect_le_pow hn (fun K σ => (2 : ℝ≥0∞) ^ cntIter K σ v)
    (1 + 2 * (n : ℝ≥0∞)⁻¹) (by
      intro K σ
      simp only [cntIter, prefixIter_snoc, cntStep]
      have h2 : ∀ p : Fin n × Fin n, uniformPair n hn p *
          (2 : ℝ≥0∞) ^ (if p ∈ PairsInvolving n v then
            prefixIter (fun _ => 0) cntStep K σ v + 1
            else prefixIter (fun _ => 0) cntStep K σ v) =
          (2 : ℝ≥0∞) ^ prefixIter (fun _ => 0) cntStep K σ v *
            (uniformPair n hn p * (if p ∈ PairsInvolving n v then 2 else 1)) := by
        intro p
        split_ifs
        · rw [pow_succ]; ring
        · ring
      rw [Finset.sum_congr rfl (fun p _ => h2 p), ← Finset.mul_sum,
        uniformPair_sum_two_pow hn v, mul_comm]) K
  simp only [cntIter, prefixIter, pow_zero, mul_one] at hE
  refine le_trans ?_ hE
  have hM := schedulerPrefix_markov hn K (fun σ => (2 : ℝ≥0∞) ^ cntIter K σ v) (2 ^ D)
  refine le_trans (mul_le_mul_left' (MeasureTheory.measure_mono ?_) _) hM
  intro σ hσ
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) hσ

/-- The guard fails within `4 n (n - 1)` steps with probability at most `1/n²`. -/
theorem cntGuard_fail_le (hN : 1608 ≤ n) :
    (schedulerPrefixPMF n (by omega) (4 * n * (n - 1))).toOuterMeasure
        {σ | ¬ CntGuard n (4 * n * (n - 1)) σ} ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  have hn2 : 2 ≤ n := by omega
  set K := 4 * n * (n - 1)
  have hn' : (1608 : ℝ) ≤ n := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by linarith
  have hsub : {σ : SchedulerPrefix n K | ¬ CntGuard n K σ} ⊆
      ⋃ v, {σ | 16 * n ≤ cntIter K σ v} := by
    intro σ hσ
    simp only [CntGuard, not_forall, not_le, Set.mem_setOf_eq] at hσ
    obtain ⟨v, hv⟩ := hσ
    exact Set.mem_iUnion.mpr ⟨v, by show 16 * n ≤ cntIter K σ v; omega⟩
  have h2 : (2 : ℝ≥0∞) ^ (16 * n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2' : (2 : ℝ≥0∞) ^ (16 * n) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  refine (MeasureTheory.measure_mono hsub).trans ?_
  rw [← ENNReal.mul_le_mul_iff_right h2 h2']
  calc (2 : ℝ≥0∞) ^ (16 * n) * (schedulerPrefixPMF n hn2 K).toOuterMeasure
        (⋃ v, {σ | 16 * n ≤ cntIter K σ v})
      ≤ (2 : ℝ≥0∞) ^ (16 * n) * ∑ v : Fin n, (schedulerPrefixPMF n hn2 K).toOuterMeasure
          {σ | 16 * n ≤ cntIter K σ v} :=
        mul_le_mul_left' (MeasureTheory.measure_iUnion_fintype_le _ _) _
    _ = ∑ v : Fin n, (2 : ℝ≥0∞) ^ (16 * n) * (schedulerPrefixPMF n hn2 K).toOuterMeasure
          {σ | 16 * n ≤ cntIter K σ v} := Finset.mul_sum _ _ _
    _ ≤ ∑ _v : Fin n, (1 + 2 * (n : ℝ≥0∞)⁻¹) ^ K :=
        Finset.sum_le_sum fun v _ => count_tail_two_le hn2 v K (16 * n)
    _ = n * (1 + 2 * (n : ℝ≥0∞)⁻¹) ^ K := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (16 * n) * ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
        have hbase : (1 + 2 * (n : ℝ≥0∞)⁻¹) = ENNReal.ofReal (1 + 2 / n) := by
          rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, div_eq_mul_inv,
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos hn0,
            ENNReal.ofReal_natCast]
          norm_num
        have h2r : (2 : ℝ≥0∞) ^ (16 * n) = ENNReal.ofReal (2 ^ (16 * n)) := by
          rw [ENNReal.ofReal_pow (by norm_num)]; norm_num
        rw [hbase, ← ENNReal.ofReal_pow (by positivity), h2r, ← ENNReal.ofReal_natCast n,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hK : (K : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by
          have : K ≤ 4 * n ^ 2 := by
            have : n - 1 ≤ n := Nat.sub_le n 1
            simp only [K]; nlinarith
          exact_mod_cast this
        have h1 : (1 + 2 / (n : ℝ)) ^ K ≤ Real.exp (2 * K / n) := by
          calc (1 + 2 / (n : ℝ)) ^ K ≤ (Real.exp (2 / n)) ^ K := by
                apply pow_le_pow_left₀ (by positivity)
                have := Real.add_one_le_exp (2 / (n : ℝ)); linarith
            _ = Real.exp (2 * K / n) := by rw [← Real.exp_nat_mul]; congr 1; ring
        have h2K : 2 * (K : ℝ) / n ≤ 8 * n := by
          rw [div_le_iff₀ hn0]; nlinarith
        have hl2 := Real.log_two_gt_d9
        have hlog : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
        have h2e : (2 : ℝ) ^ (16 * n) = Real.exp (((16 * n : ℕ) : ℝ) * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
        rw [h2e]
        push_cast
        have hnexp : (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn0).symm
        have hn2exp : ((n : ℝ) ^ 2) = Real.exp (2 * Real.log n) := by
          rw [show 2 * Real.log n = Real.log ((n : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
            Real.exp_log (by positivity)]
        calc (n : ℝ) * (1 + 2 / (n : ℝ)) ^ K
            ≤ Real.exp (Real.log n) * Real.exp (8 * n) := by
              rw [← hnexp]
              exact mul_le_mul_of_nonneg_left (h1.trans (Real.exp_le_exp.mpr h2K)) hn0.le
          _ = Real.exp (16 * (n : ℝ) * Real.log 2 - 2 * Real.log n) *
                Real.exp (3 * Real.log n + 8 * n - 16 * (n : ℝ) * Real.log 2) := by
              rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          _ ≤ Real.exp (16 * (n : ℝ) * Real.log 2 - 2 * Real.log n) * 1 := by
              apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
              rw [Real.exp_le_one_iff]
              nlinarith
          _ = Real.exp (16 * (n : ℝ) * Real.log 2) * (1 / (n : ℝ) ^ 2) := by
              rw [mul_one, Real.exp_sub, hn2exp, div_eq_mul_one_div]

/-! ### The stages -/

theorem fdOne_of_card {C : Config (AgentState n) Opinion n} (hFD : FD C)
    (h1 : (leaderSet C).card = 1) : FDOne C := by
  refine ⟨hFD, ?_⟩
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
  refine ⟨a, ?_, fun w hw => ?_⟩
  · have : a ∈ leaderSet C := by rw [ha]; exact Finset.mem_singleton_self a
    simpa [leaderSet] using this
  · have : w ∈ leaderSet C := by simpa [leaderSet] using hw
    rw [ha] at this
    exact Finset.mem_singleton.mp this

/-- Stage B2, generic in an extra property `M` that holds along guarded dormant runs. -/
theorem stageB2_gen (M : ∀ {n : ℕ}, Config (AgentState n) Opinion n → Prop)
    (hM : ∀ {n : ℕ} (hn : 0 < n) (X : Config (AgentState n) Opinion n), FDLHalf X → M X →
      ∀ K (σ : SchedulerPrefix n K), CntGuard n K σ → M (runPrefix (PEM40 n hn) X K σ)) :
    StageBound (fun C => FDLHalf C ∧ M C) (fun C => FDOne C ∧ M C)
      (fun n => 4 * n * (n - 1)) 0.7499 := by
  classical
  intro n hN hn hn2 X _ hA
  obtain ⟨⟨hFD, hL, hdt⟩, hMX⟩ := hA
  set W := 4 * n * (n - 1)
  have hX : ∀ v, (X v).1.role = .Resetting ∧ (X v).1.resetcount = 0 ∧
      16 * n + 1 ≤ (X v).1.delaytimer := fun v => ⟨(hFD v).1, (hFD v).2, hdt v⟩
  have hrun := dormant_run (hn := hn) X hX
  have hnice : ∀ K (σ : SchedulerPrefix n K), CntGuard n K σ →
      NiceDormant (runPrefix (PEM40 n hn) X K σ) := by
    intro K σ hg v
    have h := hrun K σ hg v
    have hc := hg v
    exact ⟨h.1, h.2.1, by omega⟩
  have hleader : ∀ K (σ : SchedulerPrefix n K), 1 ≤ (leaderSet (runPrefix (PEM40 n hn) X K σ)).card := by
    intro K σ
    obtain ⟨v, hv⟩ := runPrefix_inv (PEM40 n hn) X (fun C => ∃ v, (C v).1.leader = .L) hL
      (fun C hC i j => exists_leader_step_PEM40 C hC i j) K σ
    exact Finset.card_pos.mpr ⟨v, by simp [leaderSet, hv]⟩
  have hdrift := probNotHitBy_window_le_drift_guarded (PEM40 n hn) hn2 X (fun C => FDOne C ∧ M C)
    (fun C => leaderPot n (leaderSet C).card) (fun K σ => CntGuard n K σ)
    (fun K σ p h => cntGuard_init K σ p h) (by
      intro K σ hg hav
      have hnot := pathAvoids_final (PEM40 n hn) X _ K σ hav
      have hFDr : FD (runPrefix (PEM40 n hn) X K σ) := fun v => ⟨(hnice K σ hg v).1, (hnice K σ hg v).2.1⟩
      have h2 : 2 ≤ (leaderSet (runPrefix (PEM40 n hn) X K σ)).card := by
        by_contra hlt
        have h1 : (leaderSet (runPrefix (PEM40 n hn) X K σ)).card = 1 := by
          have := hleader K σ; omega
        exact hnot ⟨fdOne_of_card hFDr h1, hM hn X ⟨hFD, hL, hdt⟩ hMX K σ hg⟩
      exact leaderPot_drift hn2 _ (hnice K σ hg) h2) W
  -- turn the drift bound into a probability bound
  have hW0 : (W : ℝ≥0∞) ≠ 0 := by
    have : 0 < W := Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
    exact_mod_cast this.ne'
  have hWt : (W : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hfail := cntGuard_fail_le hN
  have hpot : leaderPot n (leaderSet X).card ≤ (W : ℝ≥0∞) * ENNReal.ofReal (1 / 4) := by
    refine (leaderPot_le _).trans (le_of_eq ?_)
    have hWeq : (W : ℝ≥0∞) = 4 * ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
      simp only [W]; push_cast; ring
    have h4 : ENNReal.ofReal (1 / 4) = (4 : ℝ≥0∞)⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num
    rw [h4, hWeq, mul_comm (4 : ℝ≥0∞), mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
  have hnot : probNotHitBy (PEM40 n hn) hn2 X (fun C => FDOne C ∧ M C) W ≤
      ENNReal.ofReal (1 / 4 + 1 / (n : ℝ) ^ 2) := by
    rw [← ENNReal.mul_le_mul_iff_right hW0 hWt]
    refine hdrift.trans ?_
    rw [ENNReal.ofReal_add (by norm_num) (by positivity), mul_add]
    exact add_le_add hpot (mul_le_mul_left' hfail _)
  apply ofReal_le_probHitBy_of_probNotHitBy_le (PEM40 n hn) hn2 X _ W 0.7499 _ (by norm_num)
    (by positivity) _ hnot
  have hn' : (1608 : ℝ) ≤ n := by exact_mod_cast hN
  have : (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 1608 ^ 2 := by gcongr
  norm_num at *
  linarith

/-- **Stage B2** (P3 Lemma 10 (B2), P2 Lemma 7.2). -/
theorem stageB2 : StageB2 := by
  intro n hN hn hn2 X hX hA
  have h := stageB2_gen (fun _ => True) (fun _ _ _ _ _ _ _ => trivial) n hN hn hn2 X hX
    ⟨hA, trivial⟩
  exact h.trans (probHitBy_mono_goal _ hn2 X _ _ (fun C hC => hC.1) _)

/-- **Stage B2 with answers** (P3 Lemma 10 (B2): no answer changes on the event). -/
theorem stageB2M : StageB2M :=
  stageB2_gen AllMaj (fun {n} hn X hX hMX K σ hg => by
    obtain ⟨hFD, -, hdt⟩ := hX
    have hrun := dormant_run (hn := hn) X (fun v => ⟨(hFD v).1, (hFD v).2, hdt v⟩) K σ hg
    have hmaj : majorityAnswer (runPrefix (PEM40 n hn) X K σ) = majorityAnswer X :=
      runPrefix_inv (PEM40 n hn) X (fun C => majorityAnswer C = majorityAnswer X) rfl
        (fun C hC i j => (majorityAnswer_step_eq C i j).trans hC) K σ
    have hphi : ∀ w, (X w).1.answer ≠ .phi := fun w => by
      rw [hMX w]; exact majorityAnswer_ne_phi X
    intro v
    rw [(hrun v).2.2.2 hphi, hmaj]
    exact hMX v)

/-- Non-vacuity at `n = 1608`: a good configuration in `FD_L^{½}` (all dormant with delay timer
`16 n + 1`, one leader). -/
example : ∃ X : Config (AgentState 1608) Opinion 1608, GoodPaper X ∧ FDLHalf X :=
  ⟨fun v => (AgentState.mk .Resetting 0 (if v = 0 then .L else .F) 0 .outA 0 0 0
      (16 * 1608 + 1), Opinion.A),
    fun v => by simp [GoodPEM], ⟨fun _ => ⟨rfl, rfl⟩, ⟨0, by simp⟩, fun _ => le_rfl⟩⟩

end Ripple.PopulationProtocol.SSEM
