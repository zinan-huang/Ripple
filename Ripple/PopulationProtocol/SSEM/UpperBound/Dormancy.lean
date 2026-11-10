/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Burman et al. Lemma 3.3 (dormancy) for P_EM

Paper phase `docs/audit/FIX2-BURMAN.md`, node B33; proof `docs/audit/FIX2-P2.md`
§3 (Lemmas 2.4, 2.6, 3.1, 3.2). From a fully propagating configuration, while every agent has
fewer than `Dmax` interactions, every agent stays Resetting, no agent wakes, and the resetcounts
follow the max-minus-one process exactly (`dormancy_run`). The potential
`Φ = Σ φ(x_v)`, `φ(0) = 0`, `φ(k) = 3^k`, contracts by `1 - 2/(3n)` per step in expectation
(`PhiN_expect_le`). Result (`P_EM_paper_dormancy`): the probability of not being fully dormant
after `K` interactions is at most `P[some agent has ≥ Dmax interactions] + P[Φ_K ≥ 3]`.
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.InteractionCount
import Ripple.PopulationProtocol.SSEM.UpperBound.PaperInstance

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped BigOperators ENNReal

variable {n : ℕ}

/-! ### The potential -/

/-- `φ(0) = 0`, `φ(k) = 3^k`. -/
def phiN (k : ℕ) : ℕ := if k = 0 then 0 else 3 ^ k

/-- `Φ(y) = Σ_v φ(y v)`. -/
def PhiN (y : Fin n → ℕ) : ℕ := ∑ w, phiN (y w)

/-- The max-minus-one process from an arbitrary initial vector. -/
def maxFrom (y₀ : Fin n → ℕ) : (K : ℕ) → SchedulerPrefix n K → Fin n → ℕ :=
  prefixIter y₀ maxStep

theorem three_le_phiN {k : ℕ} (hk : k ≠ 0) : 3 ≤ phiN k := by
  simp only [phiN, hk, if_false]
  calc 3 = 3 ^ 1 := by norm_num
    _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hk)

theorem phiN_step (ya yb : ℕ) : 3 * phiN (max (ya - 1) (yb - 1)) ≤ phiN ya + phiN yb := by
  rcases le_total yb ya with h | h
  · rw [max_eq_left (by omega)]
    by_cases h1 : ya - 1 = 0
    · simp [phiN, h1]
    · have h0 : ya ≠ 0 := by omega
      simp only [phiN, h1, h0, if_false]
      have : 3 * 3 ^ (ya - 1) = 3 ^ ya := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      rw [this]
      exact Nat.le_add_right _ _
  · rw [max_eq_right (by omega)]
    by_cases h1 : yb - 1 = 0
    · simp [phiN, h1]
    · have h0 : yb ≠ 0 := by omega
      simp only [phiN, h1, h0, if_false]
      have : 3 * 3 ^ (yb - 1) = 3 ^ yb := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      rw [this]
      exact Nat.le_add_left _ _

theorem sum_pairUpd_eq {a b : Fin n} (hab : a ≠ b) (f : Fin n → ℕ) (v : ℕ) :
    ∑ w, pairUpd f a b v w + f a + f b = ∑ w, f w + v + v := by
  classical
  have ha : a ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ a
  have hb : b ∈ (Finset.univ : Finset (Fin n)).erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
  rw [← Finset.add_sum_erase Finset.univ (pairUpd f a b v) ha,
    ← Finset.add_sum_erase _ (pairUpd f a b v) hb,
    ← Finset.add_sum_erase Finset.univ f ha, ← Finset.add_sum_erase _ f hb]
  have hrest : ∑ w ∈ (Finset.univ.erase a).erase b, pairUpd f a b v w =
      ∑ w ∈ (Finset.univ.erase a).erase b, f w := by
    apply Finset.sum_congr rfl
    intro w hw
    simp only [Finset.mem_erase] at hw
    simp [pairUpd, hw.1, hw.2.1]
  rw [hrest]
  have h1 : pairUpd f a b v a = v := by simp [pairUpd, hab]
  have h2 : pairUpd f a b v b = v := by simp [pairUpd, hab]
  rw [h1, h2]
  omega

theorem PhiN_maxStep {a b : Fin n} (hab : a ≠ b) (y : Fin n → ℕ) :
    3 * PhiN (maxStep y (a, b)) + (phiN (y a) + phiN (y b)) ≤ 3 * PhiN y := by
  have hpt : ∀ w, phiN (maxStep y (a, b) w) =
      pairUpd (fun w => phiN (y w)) a b (phiN (max (y a - 1) (y b - 1))) w := by
    intro w
    simp only [maxStep, pairUpd]
    split_ifs <;> rfl
  have hsum := sum_pairUpd_eq hab (fun w => phiN (y w)) (phiN (max (y a - 1) (y b - 1)))
  have hstep := phiN_step (y a) (y b)
  unfold PhiN
  simp only [hpt]
  simp only at hsum
  omega

theorem PhiN_maxStep_ennreal (hn : 2 ≤ n) (y : Fin n → ℕ) :
    3 * ∑ p : Fin n × Fin n, uniformPair n hn p * (PhiN (maxStep y p) : ℝ≥0∞) +
        2 * (n : ℝ≥0∞)⁻¹ * (PhiN y : ℝ≥0∞) ≤ 3 * (PhiN y : ℝ≥0∞) := by
  classical
  have hpt : ∀ p : Fin n × Fin n,
      uniformPair n hn p * (3 * (PhiN (maxStep y p) : ℝ≥0∞) +
        ((phiN (y p.1) : ℝ≥0∞) + (phiN (y p.2) : ℝ≥0∞))) ≤
      uniformPair n hn p * (3 * (PhiN y : ℝ≥0∞)) := by
    intro p
    obtain ⟨a, b⟩ := p
    by_cases hab : a = b
    · subst hab
      rw [uniformPair_apply_self, zero_mul, zero_mul]
    · apply mul_le_mul_left'
      have := PhiN_maxStep hab y
      exact_mod_cast this
  have hsum := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => hpt p
  rw [← Finset.sum_mul, show ∑ p : Fin n × Fin n, uniformPair n hn p = 1 by
    simpa [tsum_fintype] using (uniformPair n hn).tsum_coe, one_mul] at hsum
  rw [Finset.sum_congr rfl (fun p _ => mul_add (uniformPair n hn p)
    (3 * (PhiN (maxStep y p) : ℝ≥0∞)) ((phiN (y p.1) : ℝ≥0∞) + (phiN (y p.2) : ℝ≥0∞))),
    Finset.sum_add_distrib] at hsum
  rw [uniformPair_sum_endpoints hn (fun w => (phiN (y w) : ℝ≥0∞))] at hsum
  have hcast : (PhiN y : ℝ≥0∞) = ∑ w, (phiN (y w) : ℝ≥0∞) := by
    unfold PhiN; push_cast; rfl
  rw [hcast] at ⊢
  rw [← hcast] at hsum ⊢
  calc 3 * ∑ p : Fin n × Fin n, uniformPair n hn p * (PhiN (maxStep y p) : ℝ≥0∞) +
          2 * (n : ℝ≥0∞)⁻¹ * (PhiN y : ℝ≥0∞)
        = ∑ p : Fin n × Fin n, uniformPair n hn p * (3 * (PhiN (maxStep y p) : ℝ≥0∞)) +
          2 * (n : ℝ≥0∞)⁻¹ * (PhiN y : ℝ≥0∞) := by
          rw [Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro p _
          ring
      _ ≤ 3 * (PhiN y : ℝ≥0∞) := hsum

/-- The contraction factor `1 - 2/(3n)`. -/
noncomputable def dormRho (n : ℕ) : ℝ≥0∞ := 1 - 3⁻¹ * 2 * (n : ℝ≥0∞)⁻¹

theorem PhiN_step_expect (hn : 2 ≤ n) (y : Fin n → ℕ) :
    ∑ p : Fin n × Fin n, uniformPair n hn p * (PhiN (maxStep y p) : ℝ≥0∞) ≤
      dormRho n * (PhiN y : ℝ≥0∞) := by
  set E := ∑ p : Fin n × Fin n, uniformPair n hn p * (PhiN (maxStep y p) : ℝ≥0∞)
  have H := PhiN_maxStep_ennreal hn y
  have h3 : (3 : ℝ≥0∞)⁻¹ * 3 = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have h : E + 3⁻¹ * 2 * (n : ℝ≥0∞)⁻¹ * (PhiN y : ℝ≥0∞) ≤ (PhiN y : ℝ≥0∞) :=
    calc E + 3⁻¹ * 2 * (n : ℝ≥0∞)⁻¹ * (PhiN y : ℝ≥0∞)
        = 3⁻¹ * (3 * E + 2 * (n : ℝ≥0∞)⁻¹ * (PhiN y : ℝ≥0∞)) := by
          rw [mul_add, ← mul_assoc, h3, one_mul]
          ring
      _ ≤ 3⁻¹ * (3 * (PhiN y : ℝ≥0∞)) := mul_le_mul_left' H _
      _ = (PhiN y : ℝ≥0∞) := by rw [← mul_assoc, h3, one_mul]
  unfold dormRho
  rw [ENNReal.sub_mul (fun _ _ => ENNReal.natCast_ne_top _), one_mul]
  have hb : 3⁻¹ * 2 * (n : ℝ≥0∞)⁻¹ * (PhiN y : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (le_add_self.trans h)
  exact ENNReal.le_sub_of_add_le_right hb h

/-- **Expected potential** after `K` interactions. -/
theorem PhiN_expect_le (hn : 2 ≤ n) (y₀ : Fin n → ℕ) (K : ℕ) :
    ∑ σ : SchedulerPrefix n K, schedulerPrefixPMF n hn K σ * (PhiN (maxFrom y₀ K σ) : ℝ≥0∞) ≤
      dormRho n ^ K * (PhiN y₀ : ℝ≥0∞) := by
  have h := schedulerPrefix_expect_le_pow hn (fun K σ => (PhiN (maxFrom y₀ K σ) : ℝ≥0∞))
    (dormRho n) (by
      intro K σ
      simp only [maxFrom, prefixIter_snoc]
      exact PhiN_step_expect hn _) K
  simpa [maxFrom, prefixIter] using h

/-! ### No wake while interaction counts stay below `Dmax` -/

theorem preAgent_dt (trank : ℕ) (s r : AgentState n) :
    (preAgent n trank s r).delaytimer = r.delaytimer := by
  unfold preAgent
  dsimp only
  split_ifs <;> simp

theorem preEpi_dt (a₀ a₁ : AgentState n) :
    (preEpi a₀ a₁).1.delaytimer = a₀.delaytimer ∧ (preEpi a₀ a₁).2.delaytimer = a₁.delaytimer := by
  unfold preEpi
  split_ifs <;> simp

theorem prDedup_fields (p : AgentState n × AgentState n) :
    (prDedup p).1 = p.1 ∧ (prDedup p).2.role = p.2.role ∧
      (prDedup p).2.resetcount = p.2.resetcount ∧ (prDedup p).2.delaytimer = p.2.delaytimer := by
  unfold prDedup
  refine ⟨rfl, ?_⟩
  split_ifs <;> simp

/-- A Resetting agent after synchronisation with a Resetting partner, when the decremented
delay timer cannot reach `0`, stays Resetting. -/
theorem processAgent_resetting_partner {Emax Dmax : ℕ} {hn : 0 < n} (s : AgentState n) (m c : ℕ)
    (hs : s.role = .Resetting) (hi : s.resetcount = 0 → Dmax ≤ s.delaytimer + c)
    (hc : c + 2 ≤ Dmax) :
    (processAgent Emax Dmax hn { s with resetcount := m } s.resetcount true).role = .Resetting ∧
      (processAgent Emax Dmax hn { s with resetcount := m } s.resetcount true).resetcount = m ∧
      ((processAgent Emax Dmax hn { s with resetcount := m } s.resetcount true).resetcount = 0 →
        Dmax ≤ (processAgent Emax Dmax hn { s with resetcount := m } s.resetcount true).delaytimer +
          (c + 1)) := by
  by_cases hm : m = 0
  · subst hm
    by_cases ho : 0 < s.resetcount
    · have hD : Dmax ≠ 0 := by omega
      have : processAgent Emax Dmax hn { s with resetcount := 0 } s.resetcount true =
          { s with resetcount := 0, delaytimer := Dmax } := by
        simp [processAgent, hs, ho, hD]
      rw [this]
      simp [hs]
    · have h0 : s.resetcount = 0 := by omega
      have hdt := hi h0
      have hne : s.delaytimer - 1 ≠ 0 := by omega
      have : processAgent Emax Dmax hn { s with resetcount := 0 } s.resetcount true =
          { s with resetcount := 0, delaytimer := s.delaytimer - 1 } := by
        simp [processAgent, hs, h0, hne]
      rw [this]
      simp only [hs, true_and]
      intro _
      omega
  · rw [processAgent_rc_ne_zero (by simpa using hm)]
    simp [hs, hm]

/-- **One P_EM step between two Resetting agents** (no wake, synchronised resetcount, delay
timer bookkeeping). -/
theorem pem_step_resetting {trank R Emax Dmax : ℕ} {hn : 0 < n} (a b : AgentState n)
    (x₀ x₁ : Opinion) (ha : a.role = .Resetting) (hb : b.role = .Resetting) (ca cb : ℕ)
    (hia : a.resetcount = 0 → Dmax ≤ a.delaytimer + ca)
    (hib : b.resetcount = 0 → Dmax ≤ b.delaytimer + cb)
    (hca : ca + 2 ≤ Dmax) (hcb : cb + 2 ≤ Dmax) :
    ((transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.role =
        .Resetting ∧
      (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.resetcount =
        max (a.resetcount - 1) (b.resetcount - 1) ∧
      ((transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.resetcount =
          0 → Dmax ≤ (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn)
            ((a, x₀), (b, x₁))).1.delaytimer + (ca + 1))) ∧
    ((transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.role =
        .Resetting ∧
      (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.resetcount =
        max (a.resetcount - 1) (b.resetcount - 1) ∧
      ((transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.resetcount =
          0 → Dmax ≤ (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn)
            ((a, x₀), (b, x₁))).2.delaytimer + (cb + 1))) := by
  set m := max (a.resetcount - 1) (b.resetcount - 1)
  have hrec : prRecruit Dmax a b = (a, b) := by simp [prRecruit, ha, hb]
  have hsync : prSync a b = ({ a with resetcount := m }, { b with resetcount := m }) := by
    simp [prSync, ha, hb, m]
  have hrd : rankDeltaOSSR R Emax Dmax hn (a, b) =
      prDedup (processAgent Emax Dmax hn { a with resetcount := m } a.resetcount true,
        processAgent Emax Dmax hn { b with resetcount := m } b.resetcount true) := by
    rw [rankDeltaOSSR_eq_of_resetting (Or.inl ha), propagateReset_eq, hrec, hsync]
    simp [hb, ha]
  obtain ⟨A1, A2, A3⟩ := processAgent_resetting_partner (Emax := Emax) (hn := hn) a m ca ha hia hca
  obtain ⟨B1, B2, B3⟩ := processAgent_resetting_partner (Emax := Emax) (hn := hn) b m cb hb hib hcb
  obtain ⟨D1, D2, D3, D4⟩ := prDedup_fields
    (processAgent Emax Dmax hn { a with resetcount := m } a.resetcount true,
      processAgent Emax Dmax hn { b with resetcount := m } b.resetcount true)
  rw [transitionPEM_eq]
  have hnot : ¬ ((transitionPEM_prePhase4 n trank (rankDeltaOSSR R Emax Dmax hn) a b x₀ x₁).1.role =
      .Settled ∧ (transitionPEM_prePhase4 n trank (rankDeltaOSSR R Emax Dmax hn) a b x₀ x₁).2.role =
      .Settled) := by
    rw [prePhase4_eq, hrd]
    rintro ⟨h, -⟩
    rw [(preEpi_role_rc _ _).1, (preAgent_role_rc _ _ _).1, D1, A1] at h
    exact Role.noConfusion h
  rw [transitionPEM_phase4_of_not_both_settled hnot, prePhase4_eq, hrd]
  obtain ⟨E1, E2, E3, E4⟩ := preEpi_role_rc
    (preAgent n trank a (prDedup (processAgent Emax Dmax hn { a with resetcount := m } a.resetcount true,
      processAgent Emax Dmax hn { b with resetcount := m } b.resetcount true)).1)
    (preAgent n trank b (prDedup (processAgent Emax Dmax hn { a with resetcount := m } a.resetcount true,
      processAgent Emax Dmax hn { b with resetcount := m } b.resetcount true)).2)
  obtain ⟨F1, F2⟩ := preEpi_dt
    (preAgent n trank a (prDedup (processAgent Emax Dmax hn { a with resetcount := m } a.resetcount true,
      processAgent Emax Dmax hn { b with resetcount := m } b.resetcount true)).1)
    (preAgent n trank b (prDedup (processAgent Emax Dmax hn { a with resetcount := m } a.resetcount true,
      processAgent Emax Dmax hn { b with resetcount := m } b.resetcount true)).2)
  rw [E1, E2, E3, E4, F1, F2]
  simp only [(preAgent_role_rc _ _ _).1, (preAgent_role_rc _ _ _).2, preAgent_dt, D1, D2, D3, D4]
  exact ⟨⟨A1, A2, A3⟩, ⟨B1, B2, B3⟩⟩

/-- Fully dormant: every agent Resetting with resetcount `0`. -/
def FullyDormant {X : Type*} (C : Config (AgentState n) X n) : Prop :=
  ∀ v, (C v).1.role = .Resetting ∧ (C v).1.resetcount = 0

/-- **Deterministic core of B33.** -/
theorem dormancy_run {trank e d : ℕ} {hn : 0 < n} (X : Config (AgentState n) Opinion n)
    (hX : ∀ v, (X v).1.role = .Resetting ∧ 1 ≤ (X v).1.resetcount) :
    ∀ K (σ : SchedulerPrefix n K), (∀ v, cntIter K σ v + 1 < d * n) → ∀ v,
      (runPrefix (protocolPEMPaper n trank e d hn) X K σ v).1.role = .Resetting ∧
      (runPrefix (protocolPEMPaper n trank e d hn) X K σ v).1.resetcount =
        maxFrom (fun w => (X w).1.resetcount) K σ v ∧
      ((runPrefix (protocolPEMPaper n trank e d hn) X K σ v).1.resetcount = 0 →
        d * n ≤ (runPrefix (protocolPEMPaper n trank e d hn) X K σ v).1.delaytimer +
          cntIter K σ v)
  | 0, σ, _, v => by
      refine ⟨(hX v).1, rfl, fun h => ?_⟩
      have h1 := (hX v).2
      have h2 : (X v).1.resetcount = 0 := h
      omega
  | K + 1, σ, hc, v => by
      have hc' : ∀ w, cntIter K (Fin.init σ) w + 1 < d * n :=
        fun w => lt_of_le_of_lt (Nat.add_le_add_right (cntIter_succ_ge K σ w) 1) (hc w)
      have ih := dormancy_run (trank := trank) (e := e) (d := d) (hn := hn) X hX K (Fin.init σ) hc'
      have hcK := hc
      simp only [cntIter, prefixIter_succ, cntStep] at hcK
      simp only [runPrefix_succ, maxFrom, prefixIter_succ, maxStep, pairUpd, cntIter, cntStep]
      simp only [maxFrom, cntIter] at ih
      generalize σ (Fin.last K) = p at hcK ⊢
      obtain ⟨a, b⟩ := p
      generalize runPrefix (protocolPEMPaper n trank e d hn) X K (Fin.init σ) = C at ih ⊢
      generalize prefixIter (fun w => (X w).1.resetcount) maxStep K (Fin.init σ) = x at ih ⊢
      generalize prefixIter (fun _ => 0) cntStep K (Fin.init σ) = c at ih hcK ⊢
      simp only
      by_cases hab : a = b
      · subst hab
        have hC : C.step (protocolPEMPaper n trank e d hn) a a = C := by simp [Config.step]
        have hnot : ∀ w, (a, a) ∉ PairsInvolving n w := by
          intro w h; exact ((mem_PairsInvolving n w (a, a)).mp h).1 rfl
        rw [hC, if_neg (fun h => h.1 rfl)]
        simp only [hnot, if_false]
        exact ih v
      · have hmemA : (a, b) ∈ PairsInvolving n a :=
          (mem_PairsInvolving n a (a, b)).mpr ⟨hab, Or.inl rfl⟩
        have hmemB : (a, b) ∈ PairsInvolving n b :=
          (mem_PairsInvolving n b (a, b)).mpr ⟨hab, Or.inr rfl⟩
        have hca : c a + 2 ≤ d * n := by have := hcK a; rw [if_pos hmemA] at this; omega
        have hcb : c b + 2 ≤ d * n := by have := hcK b; rw [if_pos hmemB] at this; omega
        obtain ⟨⟨A1, A2, A3⟩, ⟨B1, B2, B3⟩⟩ := pem_step_resetting (trank := trank)
          (R := rmaxPaper n) (Emax := e * n) (Dmax := d * n) (hn := hn) (C a).1 (C b).1
          (C a).2 (C b).2 (ih a).1 (ih b).1 (c a) (c b) (ih a).2.2 (ih b).2.2 hca hcb
        have hstep : ∀ w, (C.step (protocolPEMPaper n trank e d hn) a b) w =
            if w = a then ((transitionPEM n trank (rmaxPaper n)
                (rankDeltaOSSR (rmaxPaper n) (e * n) (d * n) hn) ((C a), (C b))).1, (C a).2)
            else if w = b then ((transitionPEM n trank (rmaxPaper n)
                (rankDeltaOSSR (rmaxPaper n) (e * n) (d * n) hn) ((C a), (C b))).2, (C b).2)
            else C w := by
          intro w
          simp only [Config.step, hab, if_false]
          rfl
        rw [hstep]
        have hxa := (ih a).2.1
        have hxb := (ih b).2.1
        by_cases hwa : v = a
        · subst hwa
          rw [if_pos rfl, if_pos ⟨hab, Or.inl rfl⟩, if_pos hmemA]
          refine ⟨A1, ?_, A3⟩
          rw [A2, hxa, hxb]
        · by_cases hwb : v = b
          · subst hwb
            rw [if_neg hwa, if_pos rfl, if_pos ⟨hab, Or.inr rfl⟩, if_pos hmemB]
            refine ⟨B1, ?_, B3⟩
            rw [B2, hxa, hxb]
          · have hnv : (a, b) ∉ PairsInvolving n v := by
              intro h
              rcases ((mem_PairsInvolving n v (a, b)).mp h).2 with h' | h'
              · exact hwa h'.symm
              · exact hwb h'.symm
            rw [if_neg hwa, if_neg hwb, if_neg (fun h => h.2.elim hwa hwb), if_neg hnv]
            exact ih v

/-- **Burman et al. Lemma 3.3 for the paper instance (reduction).** -/
theorem P_EM_paper_dormancy {trank e d : ℕ} {hn : 0 < n} (hn2 : 2 ≤ n)
    (X : Config (AgentState n) Opinion n) (hX : FullyPropagating X) (K : ℕ) :
    probNotHitBy (protocolPEMPaper n trank e d hn) hn2 X FullyDormant K ≤
      (schedulerPrefixPMF n hn2 K).toOuterMeasure {σ | ∃ v, d * n ≤ cntIter K σ v + 1} +
        (schedulerPrefixPMF n hn2 K).toOuterMeasure
          {σ | 3 ≤ PhiN (maxFrom (fun w => (X w).1.resetcount) K σ)} := by
  classical
  have hX' : ∀ v, (X v).1.role = .Resetting ∧ 1 ≤ (X v).1.resetcount := by
    intro v
    have h := hX v
    by_cases hr : (X v).1.role = .Resetting
    · exact ⟨hr, by rw [effRc_of_resetting hr] at h; exact h⟩
    · rw [effRc_of_not_resetting hr] at h; omega
  refine (probNotHitBy_le_prefixMass _ hn2 X FullyDormant K).trans ?_
  refine (MeasureTheory.measure_mono ?_).trans (MeasureTheory.measure_union_le _ _)
  intro σ hσ
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_le] at hcon
  apply hσ
  intro v
  have hrun := dormancy_run (trank := trank) (e := e) (d := d) (hn := hn) X hX' K σ hcon.1 v
  refine ⟨hrun.1, ?_⟩
  rw [hrun.2.1]
  by_contra hne
  have h3 := three_le_phiN hne
  have hle : phiN (maxFrom (fun w => (X w).1.resetcount) K σ v) ≤
      PhiN (maxFrom (fun w => (X w).1.resetcount) K σ) :=
    Finset.single_le_sum (f := fun w => phiN (maxFrom (fun w => (X w).1.resetcount) K σ w))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  omega

end Ripple.PopulationProtocol.SSEM
