/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage B1 from `Z`: propagation of the correct answer (P3 Lemmas 18 and 19)

From `Z` (two triggered leaders with the majority answer, every other agent Settled with distinct
non-median ranks):

* `stageB1Za`: within `K₃₂ = ⌈4 n ln n⌉` interactions the configuration becomes fully
  propagating with every answer the majority answer, with probability `≥ 0.9981`
  (`≥ 1 - 3/n`). On the event that the walk weights from both sources stay below `3^Rmax` and
  the epidemic from the first source is complete, no agent is ever dormant: every Resetting agent
  is reached and has resetcount `≥ 1` and the majority answer, and every computing agent is
  Settled with a distinct non-median rank (`z_run`, P3 Lemma 18).
* `stageB1Zb`: from there `FD_L^{½} ∩ AllMaj` within `t₃₃` (B33 with answers kept).

`stageB1Z : StageB1Z` composes them.
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.StagesB2

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped BigOperators ENNReal

variable {n : ℕ}

/-! ### One-step lemmas -/

theorem preEpi_answers_of_ne_phi {a₀ a₁ : AgentState n} (h₀ : a₀.answer ≠ .phi)
    (h₁ : a₁.answer ≠ .phi) :
    (preEpi a₀ a₁).1.answer = a₀.answer ∧ (preEpi a₀ a₁).2.answer = a₁.answer := by
  rw [preEpi_eq_of_ne_phi h₀ h₁]
  exact ⟨rfl, rfl⟩

/-- Two propagating agents whose synchronised resetcount stays positive. -/
theorem pem_step_prop_prop {trank R Emax Dmax : ℕ} {hn : 0 < n} (a b : AgentState n)
    (x₀ x₁ : Opinion) (ha : a.role = .Resetting) (hb : b.role = .Resetting)
    (hm : 1 ≤ max (a.resetcount - 1) (b.resetcount - 1)) :
    (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.role =
        .Resetting ∧
      (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.resetcount =
        max (a.resetcount - 1) (b.resetcount - 1) ∧
      (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.role =
        .Resetting ∧
      (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.resetcount =
        max (a.resetcount - 1) (b.resetcount - 1) ∧
      (a.answer ≠ .phi → b.answer ≠ .phi →
        (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.answer =
          a.answer ∧
        (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.answer =
          b.answer) := by
  set m := max (a.resetcount - 1) (b.resetcount - 1)
  have hm0 : m ≠ 0 := by omega
  have hrec : prRecruit Dmax a b = (a, b) := by simp [prRecruit, ha, hb]
  have hsync : prSync a b = ({ a with resetcount := m }, { b with resetcount := m }) := by
    simp [prSync, ha, hb, m]
  have hrd : rankDeltaOSSR R Emax Dmax hn (a, b) =
      prDedup ({ a with resetcount := m }, { b with resetcount := m }) := by
    rw [rankDeltaOSSR_eq_of_resetting (Or.inl ha), propagateReset_eq, hrec, hsync]
    simp only
    rw [processAgent_rc_ne_zero (by simpa using hm0), processAgent_rc_ne_zero (by simpa using hm0)]
  have hD := prDedup_fields ({ a with resetcount := m }, { b with resetcount := m })
  have hDa : ∀ p : AgentState n × AgentState n, (prDedup p).2.answer = p.2.answer := by
    intro p; unfold prDedup; split_ifs <;> simp
  rw [transitionPEM_eq]
  have hnot : ¬ ((transitionPEM_prePhase4 n trank (rankDeltaOSSR R Emax Dmax hn) a b x₀ x₁).1.role =
      .Settled ∧ (transitionPEM_prePhase4 n trank (rankDeltaOSSR R Emax Dmax hn) a b x₀ x₁).2.role =
      .Settled) := by
    rw [prePhase4_eq, hrd]
    rintro ⟨h, -⟩
    rw [(preEpi_role_rc _ _).1, (preAgent_role_rc _ _ _).1, hD.1] at h
    simp [ha] at h
  rw [transitionPEM_phase4_of_not_both_settled hnot, prePhase4_eq, hrd]
  have hr1 : (prDedup ({ a with resetcount := m }, { b with resetcount := m })).1.role =
      .Resetting := by rw [hD.1]; simp [ha]
  have hr2 : (prDedup ({ a with resetcount := m }, { b with resetcount := m })).2.role =
      .Resetting := by rw [hD.2.1]; simp [hb]
  rw [preAgent_of_resetting trank ha hr1, preAgent_of_resetting trank hb hr2]
  obtain ⟨E1, E2, E3, E4⟩ := preEpi_role_rc
    (prDedup ({ a with resetcount := m }, { b with resetcount := m })).1
    (prDedup ({ a with resetcount := m }, { b with resetcount := m })).2
  refine ⟨E1.trans hr1, E2.trans (by rw [hD.1]), E3.trans hr2, E4.trans (by rw [hD.2.2.1]),
    fun h0 h1 => ?_⟩
  have h0' : (prDedup ({ a with resetcount := m }, { b with resetcount := m })).1.answer =
      a.answer := by rw [hD.1]
  have h1' : (prDedup ({ a with resetcount := m }, { b with resetcount := m })).2.answer =
      b.answer := by rw [hDa]
  rw [(preEpi_answers_of_ne_phi (by rw [h0']; exact h0) (by rw [h1']; exact h1)).1,
    (preEpi_answers_of_ne_phi (by rw [h0']; exact h0) (by rw [h1']; exact h1)).2, h0', h1']
  exact ⟨rfl, rfl⟩

/-- A propagating agent with resetcount `≥ 2` recruits a computing partner (either order). -/
theorem pem_step_prop_comp {trank R Emax Dmax : ℕ} {hn : 0 < n} (a b : AgentState n)
    (x₀ x₁ : Opinion) (hD : 1 ≤ Dmax) :
    ((a.role = .Resetting ∧ 2 ≤ a.resetcount ∧ b.role ≠ .Resetting ∧ a.answer ≠ .phi) →
      (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.role =
          .Resetting ∧
        (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.resetcount
          = a.resetcount - 1 ∧
        (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.role =
          .Resetting ∧
        (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.resetcount
          = a.resetcount - 1 ∧
        (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.answer =
          a.answer ∧
        (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.answer =
          a.answer) ∧
    ((b.role = .Resetting ∧ 2 ≤ b.resetcount ∧ a.role ≠ .Resetting ∧ b.answer ≠ .phi) →
      (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.role =
          .Resetting ∧
        (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.resetcount
          = b.resetcount - 1 ∧
        (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.role =
          .Resetting ∧
        (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.resetcount
          = b.resetcount - 1 ∧
        (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.answer =
          b.answer ∧
        (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.answer =
          b.answer) := by
  constructor
  · rintro ⟨ha, hra, hb, hphi⟩
    set m := a.resetcount - 1
    have hm0 : m ≠ 0 := by omega
    have hrec : prRecruit Dmax a b =
        (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax }) := by
      simp [prRecruit, ha, hb, show 0 < a.resetcount by omega]
    have hsync : prSync a { b with role := .Resetting, resetcount := 0, delaytimer := Dmax } =
        ({ a with resetcount := m },
          { b with role := .Resetting, resetcount := m, delaytimer := Dmax }) := by
      simp [prSync, ha, m]
    have hrd : rankDeltaOSSR R Emax Dmax hn (a, b) =
        prDedup ({ a with resetcount := m },
          { b with role := .Resetting, resetcount := m, delaytimer := Dmax }) := by
      rw [rankDeltaOSSR_eq_of_resetting (Or.inl ha), propagateReset_eq, hrec, hsync]
      simp only
      rw [processAgent_rc_ne_zero (by simpa using hm0),
        processAgent_rc_ne_zero (by simpa using hm0)]
    set q := prDedup ({ a with resetcount := m },
      { b with role := .Resetting, resetcount := m, delaytimer := Dmax })
    have hD' := prDedup_fields ({ a with resetcount := m },
      { b with role := .Resetting, resetcount := m, delaytimer := Dmax })
    have hq1 : q.1 = { a with resetcount := m } := hD'.1
    have hq2r : q.2.role = .Resetting := by rw [hD'.2.1]
    have hq2c : q.2.resetcount = m := by rw [hD'.2.2.1]
    rw [transitionPEM_eq]
    have hnot : ¬ ((transitionPEM_prePhase4 n trank (rankDeltaOSSR R Emax Dmax hn) a b x₀ x₁).1.role =
        .Settled ∧
        (transitionPEM_prePhase4 n trank (rankDeltaOSSR R Emax Dmax hn) a b x₀ x₁).2.role =
        .Settled) := by
      rw [prePhase4_eq, hrd]
      rintro ⟨h, -⟩
      rw [(preEpi_role_rc _ _).1, (preAgent_role_rc _ _ _).1, hq1] at h
      simp [ha] at h
    rw [transitionPEM_phase4_of_not_both_settled hnot, prePhase4_eq, hrd]
    have hA : preAgent n trank a q.1 = { a with resetcount := m } := by
      rw [hq1]; exact preAgent_of_resetting trank ha (by simp [ha])
    have hB : preAgent n trank b q.2 = { q.2 with answer := .phi } := by
      unfold preAgent
      simp [hq2r, hb]
    rw [hA, hB]
    have hE : preEpi { a with resetcount := m } { q.2 with answer := .phi } =
        ({ a with resetcount := m }, { q.2 with answer := a.answer }) := by
      unfold preEpi
      simp [ha, hq2r, hphi]
    rw [hE]
    simp [ha, hq2r, hq2c, m]
  · rintro ⟨hb, hrb, ha, hphi⟩
    set m := b.resetcount - 1
    have hm0 : m ≠ 0 := by omega
    have hrec : prRecruit Dmax a b =
        ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b) := by
      simp [prRecruit, ha, hb, show 0 < b.resetcount by omega]
    have hsync : prSync { a with role := .Resetting, resetcount := 0, delaytimer := Dmax } b =
        ({ a with role := .Resetting, resetcount := m, delaytimer := Dmax },
          { b with resetcount := m }) := by
      simp [prSync, hb, m]
    have hrd : rankDeltaOSSR R Emax Dmax hn (a, b) =
        prDedup ({ a with role := .Resetting, resetcount := m, delaytimer := Dmax },
          { b with resetcount := m }) := by
      rw [rankDeltaOSSR_eq_of_resetting (Or.inr hb), propagateReset_eq, hrec, hsync]
      simp only
      rw [processAgent_rc_ne_zero (by simpa using hm0),
        processAgent_rc_ne_zero (by simpa using hm0)]
    set q := prDedup ({ a with role := .Resetting, resetcount := m, delaytimer := Dmax },
      { b with resetcount := m })
    have hD' := prDedup_fields ({ a with role := .Resetting, resetcount := m, delaytimer := Dmax },
      { b with resetcount := m })
    have hq1 : q.1 = { a with role := .Resetting, resetcount := m, delaytimer := Dmax } := hD'.1
    have hq2r : q.2.role = .Resetting := by rw [hD'.2.1]; simp [hb]
    have hq2c : q.2.resetcount = m := by rw [hD'.2.2.1]
    have hq2a : q.2.answer = b.answer := by
      simp only [q]; unfold prDedup; split_ifs <;> simp
    rw [transitionPEM_eq]
    have hnot : ¬ ((transitionPEM_prePhase4 n trank (rankDeltaOSSR R Emax Dmax hn) a b x₀ x₁).1.role =
        .Settled ∧
        (transitionPEM_prePhase4 n trank (rankDeltaOSSR R Emax Dmax hn) a b x₀ x₁).2.role =
        .Settled) := by
      rw [prePhase4_eq, hrd]
      rintro ⟨-, h⟩
      rw [(preEpi_role_rc _ _).2.2.1, (preAgent_role_rc _ _ _).1, hq2r] at h
      exact absurd h (by decide)
    rw [transitionPEM_phase4_of_not_both_settled hnot, prePhase4_eq, hrd]
    set a' : AgentState n := { a with role := .Resetting, resetcount := m, delaytimer := Dmax }
      with ha'
    have hA : preAgent n trank a q.1 = { a' with answer := .phi } := by
      rw [hq1]
      unfold preAgent
      simp [ha, ha']
    have hB : preAgent n trank b q.2 = q.2 := preAgent_of_resetting trank hb hq2r
    rw [hA, hB]
    have hE : preEpi { a' with answer := .phi } q.2 = ({ a' with answer := b.answer }, q.2) := by
      unfold preEpi
      simp [hq2r, hq2a, hphi, ha']
    rw [hE]
    simp [hq2r, hq2c, hq2a, m, ha']

/-- Two Settled agents with distinct non-median ranks: the step at most swaps their states. -/
theorem pem_step_settled_nonmed {trank R Emax Dmax : ℕ} {hn : 0 < n} (a b : AgentState n)
    (x₀ x₁ : Opinion) (ha : a.role = .Settled) (hb : b.role = .Settled) (hne : a.rank ≠ b.rank)
    (hma : a.rank.val + 1 ≠ ceilHalf n) (hmb : b.rank.val + 1 ≠ ceilHalf n) :
    transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁)) = (a, b) ∨
      transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁)) = (b, a) := by
  rw [transitionPEM_eq_phase4_of_settled_fix (rankDeltaOSSR_settled_distinct_ranks ha hb hne)
    ha hb]
  have hc : ceilHalf n = (n + 1) / 2 := rfl
  have hdec : ∀ c₀ c₁ : AgentState n, c₀.rank.val + 1 ≠ ceilHalf n →
      c₁.rank.val + 1 ≠ ceilHalf n → phase4_decide n c₀ c₁ x₀ x₁ = (c₀, c₁) := by
    intro c₀ c₁ h0 h1
    unfold phase4_decide
    dsimp only
    split_ifs <;> first | rfl | (exfalso; omega)
  have hprop : ∀ c₀ c₁ : AgentState n, c₀.rank.val + 1 ≠ ceilHalf n →
      c₁.rank.val + 1 ≠ ceilHalf n → phase4_propagate n R c₀ c₁ = (c₀, c₁) := by
    intro c₀ c₁ h0 h1
    unfold phase4_propagate
    simp [h0, h1]
  unfold transitionPEM_phase4 phase4_swap
  simp only [ha, hb, and_self, if_true]
  split_ifs
  · right
    simp only [hdec b a hmb hma, hprop b a hmb hma]
  · left
    simp only [hdec a b hma hmb, hprop a b hma hmb]

/-! ### The run from `Z` (P3 Lemma 18) -/

theorem wtIter_le_succ (L : ℝ≥0∞) (hL : 1 ≤ L) (s : Fin n) (K : ℕ)
    (σ : SchedulerPrefix n (K + 1)) (w : Fin n) :
    wtIter L s K (Fin.init σ) w ≤ wtIter L s (K + 1) σ w := by
  simp only [wtIter, prefixIter_succ, wtStep, pairUpd]
  split_ifs with hc
  · rcases hc.2 with h | h
    · rw [h]; exact le_self_add.trans (le_mul_of_one_le_left' hL)
    · rw [h]; exact le_add_self.trans (le_mul_of_one_le_left' hL)
  · exact le_rfl

/-- The walk weights from both sources stay below `3 ^ R`. -/
def WalkOK (R : ℕ) (s s' : Fin n) (K : ℕ) (σ : SchedulerPrefix n K) : Prop :=
  ∑ w, wtIter 3 s K σ w < 3 ^ R ∧ ∑ w, wtIter 3 s' K σ w < 3 ^ R

theorem walkOK_init (R : ℕ) (s s' : Fin n) (K : ℕ) (σ : SchedulerPrefix n (K + 1))
    (h : WalkOK R s s' (K + 1) σ) : WalkOK R s s' K (Fin.init σ) :=
  ⟨lt_of_le_of_lt (Finset.sum_le_sum fun w _ => wtIter_le_succ 3 (by norm_num) s K σ w) h.1,
    lt_of_le_of_lt (Finset.sum_le_sum fun w _ => wtIter_le_succ 3 (by norm_num) s' K σ w) h.2⟩

theorem maxIter_pos_of_reach (R : ℕ) (s : Fin n) (K : ℕ) (σ : SchedulerPrefix n K) (w : Fin n)
    (hsum : ∑ w, wtIter 3 s K σ w < 3 ^ R) (hr : reachIter s K σ w = true) :
    1 ≤ maxIter R s K σ w := by
  by_contra h0
  have hx : maxIter R s K σ w = 0 := by omega
  have h := (wt_invariant R s 3 (by norm_num) K σ w).2 hr
  rw [hx, Nat.sub_zero] at h
  exact absurd (h.trans (Finset.single_le_sum (fun i _ => zero_le) (Finset.mem_univ w)))
    (not_le.mpr hsum)

/-- The invariant of P3 Lemma 18: Resetting agents are reached, propagating, with answer `maj`;
computing agents are Settled with pairwise distinct non-median ranks. -/
def ZInv (maj : Answer) (C : Config (AgentState n) Opinion n) (r r' : Fin n → Bool) : Prop :=
  (∀ w, (C w).1.role = .Resetting →
    (r w = true ∨ r' w = true) ∧ 1 ≤ (C w).1.resetcount ∧ (C w).1.answer = maj) ∧
  (∀ w, (C w).1.role ≠ .Resetting →
    (C w).1.role = .Settled ∧ (C w).1.rank.val + 1 ≠ ceilHalf n) ∧
  (∀ w w', w ≠ w' → (C w).1.role ≠ .Resetting → (C w').1.role ≠ .Resetting →
    (C w).1.rank ≠ (C w').1.rank)

theorem zInv_step {hn : 0 < n} (maj : Answer) (hmaj : maj ≠ .phi)
    (C : Config (AgentState n) Opinion n) (r r' : Fin n → Bool) (x x' : Fin n → ℕ)
    (hI : ZInv maj C r r') (hx : ∀ w, x w ≤ effRc (C w).1) (hx' : ∀ w, x' w ≤ effRc (C w).1)
    (a b : Fin n) (hab : a ≠ b)
    (hpos : (r a || r b) = true → 1 ≤ max (x a - 1) (x b - 1))
    (hpos' : (r' a || r' b) = true → 1 ≤ max (x' a - 1) (x' b - 1)) :
    ZInv maj (C.step (PEM40 n hn) a b) (pairUpd r a b (r a || r b))
      (pairUpd r' a b (r' a || r' b)) := by
  obtain ⟨hres, hcomp, hinj⟩ := hI
  set out := transitionPEM n 40 (rmaxPaper n) (rankDeltaOSSR (rmaxPaper n) (208 * n) (32 * n) hn)
    ((C a), (C b)) with hout
  have hstep : ∀ w, (C.step (PEM40 n hn) a b) w =
      if w = a then (out.1, (C a).2) else if w = b then (out.2, (C b).2) else C w := by
    intro w
    simp only [Config.step, hab, if_false, hout]
    rfl
  have hD : 1 ≤ 32 * n := by omega
  -- if one participant is Resetting, both end Resetting, propagating, with answer `maj`
  have hRR : ((C a).1.role = .Resetting ∨ (C b).1.role = .Resetting) →
      (out.1.role = .Resetting ∧ 1 ≤ out.1.resetcount ∧ out.1.answer = maj) ∧
      (out.2.role = .Resetting ∧ 1 ≤ out.2.resetcount ∧ out.2.answer = maj) := by
    intro hone
    -- the reached source gives a positive synchronised value
    have hreach : (C a).1.role = .Resetting → 1 ≤ max (effRc (C a).1 - 1) (effRc (C b).1 - 1) := by
      intro ha
      rcases (hres a ha).1 with h | h
      · have := hpos (by simp [h])
        have := hx a; have := hx b; omega
      · have := hpos' (by simp [h])
        have := hx' a; have := hx' b; omega
    have hreachb : (C b).1.role = .Resetting →
        1 ≤ max (effRc (C a).1 - 1) (effRc (C b).1 - 1) := by
      intro hb
      rcases (hres b hb).1 with h | h
      · have := hpos (by simp [h])
        have := hx a; have := hx b; omega
      · have := hpos' (by simp [h])
        have := hx' a; have := hx' b; omega
    by_cases ha : (C a).1.role = .Resetting
    · by_cases hb : (C b).1.role = .Resetting
      · have hm := hreach ha
        rw [effRc_of_resetting ha, effRc_of_resetting hb] at hm
        obtain ⟨A1, A2, B1, B2, AB⟩ := pem_step_prop_prop (trank := 40) (R := rmaxPaper n)
          (Emax := 208 * n) (Dmax := 32 * n) (hn := hn) (C a).1 (C b).1 (C a).2 (C b).2 ha hb hm
        have hans := AB (by rw [(hres a ha).2.2]; exact hmaj) (by rw [(hres b hb).2.2]; exact hmaj)
        exact ⟨⟨A1, by rw [A2]; exact hm, by rw [hans.1, (hres a ha).2.2]⟩,
          ⟨B1, by rw [B2]; exact hm, by rw [hans.2, (hres b hb).2.2]⟩⟩
      · have hm := hreach ha
        rw [effRc_of_resetting ha, effRc_of_not_resetting hb] at hm
        obtain ⟨A1, A2, B1, B2, AA, BA⟩ := (pem_step_prop_comp (trank := 40) (R := rmaxPaper n)
          (Emax := 208 * n) (hn := hn) (C a).1 (C b).1 (C a).2 (C b).2 hD).1
          ⟨ha, by omega, hb, by rw [(hres a ha).2.2]; exact hmaj⟩
        exact ⟨⟨A1, by rw [A2]; omega, by rw [AA, (hres a ha).2.2]⟩,
          ⟨B1, by rw [B2]; omega, by rw [BA, (hres a ha).2.2]⟩⟩
    · have hb : (C b).1.role = .Resetting := hone.resolve_left ha
      have hm := hreachb hb
      rw [effRc_of_not_resetting ha, effRc_of_resetting hb] at hm
      obtain ⟨A1, A2, B1, B2, AA, BA⟩ := (pem_step_prop_comp (trank := 40) (R := rmaxPaper n)
        (Emax := 208 * n) (hn := hn) (C a).1 (C b).1 (C a).2 (C b).2 hD).2
        ⟨hb, by omega, ha, by rw [(hres b hb).2.2]; exact hmaj⟩
      exact ⟨⟨A1, by rw [A2]; omega, by rw [AA, (hres b hb).2.2]⟩,
        ⟨B1, by rw [B2]; omega, by rw [BA, (hres b hb).2.2]⟩⟩
  -- both computing: the step at most swaps the two states
  have hCC : (C a).1.role ≠ .Resetting → (C b).1.role ≠ .Resetting →
      out = ((C a).1, (C b).1) ∨ out = ((C b).1, (C a).1) := by
    intro ha hb
    exact pem_step_settled_nonmed (C a).1 (C b).1 (C a).2 (C b).2 (hcomp a ha).1 (hcomp b hb).1
      (hinj a b hab ha hb) (hcomp a ha).2 (hcomp b hb).2
  have hupd : ∀ (q : Fin n → Bool) w, w ≠ a → w ≠ b → pairUpd q a b (q a || q b) w = q w := by
    intro q w hwa hwb
    simp only [pairUpd]
    rw [if_neg (fun h => h.2.elim hwa hwb)]
  have hupdab : ∀ (q : Fin n → Bool) w, (w = a ∨ w = b) →
      pairUpd q a b (q a || q b) w = (q a || q b) := by
    intro q w hw
    simp only [pairUpd]
    rw [if_pos ⟨hab, hw⟩]
  by_cases hone : (C a).1.role = .Resetting ∨ (C b).1.role = .Resetting
  · obtain ⟨⟨A1, A2, A3⟩, ⟨B1, B2, B3⟩⟩ := hRR hone
    -- the reached source of the Resetting participant reaches both
    have hreachab : ((r a || r b) = true) ∨ ((r' a || r' b) = true) := by
      rcases hone with ha | hb
      · rcases (hres a ha).1 with h | h
        · left; simp [h]
        · right; simp [h]
      · rcases (hres b hb).1 with h | h
        · left; simp [h]
        · right; simp [h]
    refine ⟨fun w hw => ?_, fun w hw => ?_, fun w w' hww' hw hw' => ?_⟩
    · rw [hstep w] at hw ⊢
      by_cases hwa : w = a
      · subst hwa
        simp only [if_pos rfl] at hw ⊢
        refine ⟨?_, A2, A3⟩
        rcases hreachab with h | h
        · left; rw [hupdab r w (Or.inl rfl)]; exact h
        · right; rw [hupdab r' w (Or.inl rfl)]; exact h
      · by_cases hwb : w = b
        · subst hwb
          simp only [if_neg hwa, if_pos rfl] at hw ⊢
          refine ⟨?_, B2, B3⟩
          rcases hreachab with h | h
          · left; rw [hupdab r w (Or.inr rfl)]; exact h
          · right; rw [hupdab r' w (Or.inr rfl)]; exact h
        · simp only [if_neg hwa, if_neg hwb] at hw ⊢
          rw [hupd r w hwa hwb, hupd r' w hwa hwb]
          exact hres w hw
    · rw [hstep w] at hw ⊢
      by_cases hwa : w = a
      · subst hwa; simp only [if_pos rfl] at hw; exact absurd A1 hw
      · by_cases hwb : w = b
        · subst hwb; simp only [if_neg hwa, if_pos rfl] at hw; exact absurd B1 hw
        · simp only [if_neg hwa, if_neg hwb] at hw ⊢
          exact hcomp w hw
    · rw [hstep w] at hw ⊢
      rw [hstep w'] at hw' ⊢
      by_cases hwa : w = a
      · subst hwa; simp only [if_pos rfl] at hw; exact absurd A1 hw
      by_cases hwb : w = b
      · subst hwb; simp only [if_neg hwa, if_pos rfl] at hw; exact absurd B1 hw
      by_cases hwa' : w' = a
      · subst hwa'; simp only [if_pos rfl] at hw'; exact absurd A1 hw'
      by_cases hwb' : w' = b
      · subst hwb'; simp only [if_neg hwa', if_pos rfl] at hw'; exact absurd B1 hw'
      simp only [if_neg hwa, if_neg hwb, if_neg hwa', if_neg hwb'] at hw hw' ⊢
      exact hinj w w' hww' hw hw'
  · push Not at hone
    obtain ⟨ha, hb⟩ := hone
    have hsw := hCC ha hb
    -- new states: the multiset {C a, C b} at {a, b}
    have hnewa : (C.step (PEM40 n hn) a b a).1 = (C a).1 ∨ (C.step (PEM40 n hn) a b a).1 = (C b).1 := by
      rw [hstep a]; simp only [if_pos rfl]
      rcases hsw with h | h <;> rw [h] <;> simp
    have hnewb : (C.step (PEM40 n hn) a b b).1 = (C a).1 ∨ (C.step (PEM40 n hn) a b b).1 = (C b).1 := by
      rw [hstep b]; simp only [if_neg (Ne.symm hab), if_pos rfl]
      rcases hsw with h | h <;> rw [h] <;> simp
    have hnewab : (C.step (PEM40 n hn) a b a).1 ≠ (C.step (PEM40 n hn) a b b).1 ∨
        (C a).1 = (C b).1 := by
      rw [hstep a, hstep b]; simp only [if_pos rfl, if_neg (Ne.symm hab)]
      rcases hsw with h | h <;> rw [h] <;> simp only
      · by_cases he : (C a).1 = (C b).1
        · right; exact he
        · left; exact he
      · by_cases he : (C b).1 = (C a).1
        · right; exact he.symm
        · left; exact he
    have hother : ∀ w, w ≠ a → w ≠ b → C.step (PEM40 n hn) a b w = C w := by
      intro w hwa hwb
      rw [hstep w, if_neg hwa, if_neg hwb]
    have hrank : (C a).1.rank ≠ (C b).1.rank := hinj a b hab ha hb
    have hcases : ∀ w, (C.step (PEM40 n hn) a b w).1 = (C w).1 ∨
        ((w = a ∨ w = b) ∧ ((C.step (PEM40 n hn) a b w).1 = (C a).1 ∨
          (C.step (PEM40 n hn) a b w).1 = (C b).1)) := by
      intro w
      by_cases hwa : w = a
      · subst hwa; right; exact ⟨Or.inl rfl, hnewa⟩
      · by_cases hwb : w = b
        · subst hwb; right; exact ⟨Or.inr rfl, hnewb⟩
        · left; rw [hother w hwa hwb]
    refine ⟨fun w hw => ?_, fun w hw => ?_, fun w w' hww' hw hw' => ?_⟩
    · -- a Resetting agent is not a participant
      have hwa : w ≠ a := by
        rintro rfl
        rcases hnewa with h | h <;> rw [h] at hw
        · exact ha hw
        · exact hb hw
      have hwb : w ≠ b := by
        rintro rfl
        rcases hnewb with h | h <;> rw [h] at hw
        · exact ha hw
        · exact hb hw
      rw [hother w hwa hwb] at hw ⊢
      rw [hupd r w hwa hwb, hupd r' w hwa hwb]
      exact hres w hw
    · rcases hcases w with h | ⟨-, h | h⟩ <;> rw [h] at hw ⊢
      · exact hcomp w hw
      · exact hcomp a ha
      · exact hcomp b hb
    · -- distinct ranks among computing agents
      by_cases hwab : w = a ∨ w = b
      · by_cases hwab' : w' = a ∨ w' = b
        · -- both participants
          have hpair : (w = a ∧ w' = b) ∨ (w = b ∧ w' = a) := by
            rcases hwab with rfl | rfl <;> rcases hwab' with rfl | rfl
            · exact absurd rfl hww'
            · left; exact ⟨rfl, rfl⟩
            · right; exact ⟨rfl, rfl⟩
            · exact absurd rfl hww'
          have hstates : (C.step (PEM40 n hn) a b a).1.rank ≠ (C.step (PEM40 n hn) a b b).1.rank := by
            rw [hstep a, hstep b]; simp only [if_pos rfl, if_neg (Ne.symm hab)]
            rcases hsw with h | h <;> rw [h]
            · exact hrank
            · exact Ne.symm hrank
          rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hstates
          · exact Ne.symm hstates
        · push Not at hwab'
          rw [hother w' hwab'.1 hwab'.2] at hw' ⊢
          have hw'a : w' ≠ a := hwab'.1
          have hw'b : w' ≠ b := hwab'.2
          rcases hwab with rfl | rfl
          · rcases hnewa with h | h <;> rw [h]
            · exact hinj w w' hww' ha hw'
            · exact hinj b w' (Ne.symm hw'b) hb hw'
          · rcases hnewb with h | h <;> rw [h]
            · exact hinj a w' (Ne.symm hw'a) ha hw'
            · exact hinj w w' hww' hb hw'
      · push Not at hwab
        rw [hother w hwab.1 hwab.2] at hw ⊢
        by_cases hwab' : w' = a ∨ w' = b
        · rcases hwab' with rfl | rfl
          · rcases hnewa with h | h <;> rw [h]
            · exact hinj w w' hww' hw ha
            · exact hinj w b hwab.2 hw hb
          · rcases hnewb with h | h <;> rw [h]
            · exact hinj w a hwab.1 hw ha
            · exact hinj w w' hww' hw hb
        · push Not at hwab'
          rw [hother w' hwab'.1 hwab'.2] at hw' ⊢
          exact hinj w w' hww' hw hw'


/-- **P3 Lemma 18, deterministic part**: on the walk-weight event the invariant `ZInv` holds
along the whole run. -/
theorem z_run {hn : 0 < n} (X : Config (AgentState n) Opinion n) (s s' : Fin n)
    (hI : ZInv (majorityAnswer X) X (fun w => decide (w = s)) (fun w => decide (w = s')))
    (hs : rmaxPaper n ≤ effRc (X s).1) (hs' : rmaxPaper n ≤ effRc (X s').1) :
    ∀ K (σ : SchedulerPrefix n K), WalkOK (rmaxPaper n) s s' K σ →
      ZInv (majorityAnswer X) (runPrefix (PEM40 n hn) X K σ) (reachIter s K σ)
        (reachIter s' K σ)
  | 0, _, _ => hI
  | K + 1, σ, hW => by
      have ih := z_run (hn := hn) X s s' hI hs hs' K (Fin.init σ) (walkOK_init _ s s' K σ hW)
      have hδ := fun (s₀ s₁ : AgentState n) (x₀ x₁ : Opinion) =>
        transitionPEM_effRc (trank := 40) (Rmax := rmaxPaper n) (Emax := 208 * n)
          (Dmax := 32 * n) (hn := hn) s₀ s₁ x₀ x₁
      have hdom := effRc_runPrefix_ge (PEM40 n hn) (rmaxPaper n) hδ X s hs K (Fin.init σ)
      have hdom' := effRc_runPrefix_ge (PEM40 n hn) (rmaxPaper n) hδ X s' hs' K (Fin.init σ)
      have hpos1 := fun w (hr : reachIter s (K + 1) σ w = true) =>
        maxIter_pos_of_reach (rmaxPaper n) s (K + 1) σ w hW.1 hr
      have hpos2 := fun w (hr : reachIter s' (K + 1) σ w = true) =>
        maxIter_pos_of_reach (rmaxPaper n) s' (K + 1) σ w hW.2 hr
      simp only [reachIter, maxIter, prefixIter_succ, reachStep, maxStep] at hpos1 hpos2 ⊢
      simp only [reachIter, maxIter] at ih hdom hdom'
      rw [runPrefix_succ]
      generalize σ (Fin.last K) = p at hpos1 hpos2 ⊢
      obtain ⟨a, b⟩ := p
      generalize runPrefix (PEM40 n hn) X K (Fin.init σ) = C at ih hdom hdom' ⊢
      generalize prefixIter (fun w => decide (w = s)) reachStep K (Fin.init σ) = r
        at ih hpos1 ⊢
      generalize prefixIter (fun w => decide (w = s')) reachStep K (Fin.init σ) = r'
        at ih hpos2 ⊢
      generalize prefixIter (fun w => if w = s then rmaxPaper n else 0) maxStep K
        (Fin.init σ) = x at hdom hpos1
      generalize prefixIter (fun w => if w = s' then rmaxPaper n else 0) maxStep K
        (Fin.init σ) = x' at hdom' hpos2
      simp only at hpos1 hpos2 ⊢
      by_cases hab : a = b
      · subst hab
        have hC : C.step (PEM40 n hn) a a = C := by simp [Config.step]
        have hp : ∀ q : Fin n → Bool, pairUpd q a a (q a || q a) = q := by
          intro q; funext w; simp [pairUpd]
        rw [hC, hp, hp]
        exact ih
      · refine zInv_step (majorityAnswer X) (majorityAnswer_ne_phi X) C r r' x x' ?_ hdom hdom'
          a b hab (fun h => ?_) (fun h => ?_)
        · -- `majorityAnswer` of the run equals that of `X`; the invariant is stated with `X`
          exact ih
        · have := hpos1 a (by simp [pairUpd, hab, h])
          simpa [pairUpd, hab] using this
        · have := hpos2 a (by simp [pairUpd, hab, h])
          simpa [pairUpd, hab] using this

theorem zInv_of_zTwo (X : Config (AgentState n) Opinion n) (s s' : Fin n) (hss : s ≠ s')
    (h1 : ∀ w, (w = s ∨ w = s') → (X w).1.role = .Resetting ∧
      (X w).1.resetcount = rmaxPaper n ∧ (X w).1.leader = .L ∧
      (X w).1.answer = majorityAnswer X)
    (h2 : ∀ w, w ≠ s → w ≠ s' → (X w).1.role = .Settled ∧ (X w).1.rank.val + 1 ≠ ceilHalf n)
    (h3 : ∀ w w', w ≠ s → w ≠ s' → w' ≠ s → w' ≠ s' → (X w).1.rank = (X w').1.rank → w = w')
    (hR : 1 ≤ rmaxPaper n) :
    ZInv (majorityAnswer X) X (fun w => decide (w = s)) (fun w => decide (w = s')) := by
  have hcomp : ∀ w, (X w).1.role ≠ .Resetting → w ≠ s ∧ w ≠ s' := by
    intro w hw
    refine ⟨fun h => hw (h1 w (Or.inl h)).1, fun h => hw (h1 w (Or.inr h)).1⟩
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w w' hww' hw hw' => ?_⟩
  · by_cases hws : w = s
    · subst hws
      exact ⟨Or.inl (by simp), by rw [(h1 w (Or.inl rfl)).2.1]; exact hR,
        (h1 w (Or.inl rfl)).2.2.2⟩
    · by_cases hws' : w = s'
      · subst hws'
        exact ⟨Or.inr (by simp), by rw [(h1 w (Or.inr rfl)).2.1]; exact hR,
          (h1 w (Or.inr rfl)).2.2.2⟩
      · exact absurd hw (by rw [(h2 w hws hws').1]; decide)
  · exact h2 w (hcomp w hw).1 (hcomp w hw).2
  · intro he
    exact hww' (h3 w w' (hcomp w hw).1 (hcomp w hw).2 (hcomp w' hw').1 (hcomp w' hw').2 he)

/-! ### Answers along dormancy runs -/

theorem preAgent_answer_of_resetting (trank : ℕ) {s : AgentState n} (r : AgentState n)
    (hs : s.role = .Resetting) : (preAgent n trank s r).answer = r.answer := by
  unfold preAgent
  simp only [hs, ne_eq, not_true_eq_false, and_false, if_false]
  split_ifs <;> simp

/-- Answers in a step between two Resetting agents that stay Resetting (B33 regime). -/
theorem pem_step_resetting_answer {trank R Emax Dmax : ℕ} {hn : 0 < n} (a b : AgentState n)
    (x₀ x₁ : Opinion) (ha : a.role = .Resetting) (hb : b.role = .Resetting) (ca cb : ℕ)
    (hia : a.resetcount = 0 → Dmax ≤ a.delaytimer + ca)
    (hib : b.resetcount = 0 → Dmax ≤ b.delaytimer + cb)
    (hca : ca + 2 ≤ Dmax) (hcb : cb + 2 ≤ Dmax) (hpa : a.answer ≠ .phi)
    (hpb : b.answer ≠ .phi) :
    (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).1.answer =
        a.answer ∧
      (transitionPEM n trank R (rankDeltaOSSR R Emax Dmax hn) ((a, x₀), (b, x₁))).2.answer =
        b.answer := by
  set m := max (a.resetcount - 1) (b.resetcount - 1)
  have hrec : prRecruit Dmax a b = (a, b) := by simp [prRecruit, ha, hb]
  have hsync : prSync a b = ({ a with resetcount := m }, { b with resetcount := m }) := by
    simp [prSync, ha, hb, m]
  have hrd : rankDeltaOSSR R Emax Dmax hn (a, b) =
      prDedup (processAgent Emax Dmax hn { a with resetcount := m } a.resetcount true,
        processAgent Emax Dmax hn { b with resetcount := m } b.resetcount true) := by
    rw [rankDeltaOSSR_eq_of_resetting (Or.inl ha), propagateReset_eq, hrec, hsync]
    simp [hb, ha]
  obtain ⟨A1, -, -⟩ := processAgent_resetting_partner (Emax := Emax) (hn := hn) a m ca ha hia hca
  obtain ⟨D1, -, -, -⟩ := prDedup_fields
    (processAgent Emax Dmax hn { a with resetcount := m } a.resetcount true,
      processAgent Emax Dmax hn { b with resetcount := m } b.resetcount true)
  have hDa : ∀ p : AgentState n × AgentState n, (prDedup p).2.answer = p.2.answer := by
    intro p; unfold prDedup; split_ifs <;> simp
  rw [transitionPEM_eq]
  have hnot : ¬ ((transitionPEM_prePhase4 n trank (rankDeltaOSSR R Emax Dmax hn) a b x₀ x₁).1.role =
      .Settled ∧ (transitionPEM_prePhase4 n trank (rankDeltaOSSR R Emax Dmax hn) a b x₀ x₁).2.role =
      .Settled) := by
    rw [prePhase4_eq, hrd]
    rintro ⟨h, -⟩
    rw [(preEpi_role_rc _ _).1, (preAgent_role_rc _ _ _).1, D1, A1] at h
    exact Role.noConfusion h
  rw [transitionPEM_phase4_of_not_both_settled hnot, prePhase4_eq, hrd]
  have h0 : (preAgent n trank a (prDedup (processAgent Emax Dmax hn { a with resetcount := m }
      a.resetcount true, processAgent Emax Dmax hn { b with resetcount := m } b.resetcount
      true)).1).answer = a.answer := by
    rw [preAgent_answer_of_resetting trank _ ha, D1, processAgent_answer_preserved]
  have h1 : (preAgent n trank b (prDedup (processAgent Emax Dmax hn { a with resetcount := m }
      a.resetcount true, processAgent Emax Dmax hn { b with resetcount := m } b.resetcount
      true)).2).answer = b.answer := by
    rw [preAgent_answer_of_resetting trank _ hb, hDa, processAgent_answer_preserved]
  rw [(preEpi_answers_of_ne_phi (by rw [h0]; exact hpa) (by rw [h1]; exact hpb)).1,
    (preEpi_answers_of_ne_phi (by rw [h0]; exact hpa) (by rw [h1]; exact hpb)).2, h0, h1]
  exact ⟨rfl, rfl⟩

/-- Answers are kept along the B33 run while interaction counts stay below `Dmax - 1`. -/
theorem dormancy_answers {hn : 0 < n} (X : Config (AgentState n) Opinion n)
    (hX : ∀ v, (X v).1.role = .Resetting ∧ 1 ≤ (X v).1.resetcount)
    (hphi : ∀ v, (X v).1.answer ≠ .phi) :
    ∀ K (σ : SchedulerPrefix n K), (∀ v, cntIter K σ v + 1 < 32 * n) → ∀ v,
      (runPrefix (PEM40 n hn) X K σ v).1.answer = (X v).1.answer
  | 0, _, _, _ => rfl
  | K + 1, σ, hc, v => by
      have hc' : ∀ w, cntIter K (Fin.init σ) w + 1 < 32 * n :=
        fun w => lt_of_le_of_lt (Nat.add_le_add_right (cntIter_succ_ge K σ w) 1) (hc w)
      have ih := dormancy_answers (hn := hn) X hX hphi K (Fin.init σ) hc'
      have hrun := dormancy_run (trank := 40) (e := 208) (d := 32) (hn := hn) X hX K
        (Fin.init σ) hc'
      have hcK := hc
      simp only [cntIter, prefixIter_succ, cntStep] at hcK
      simp only [runPrefix_succ]
      simp only [cntIter] at hrun
      generalize σ (Fin.last K) = p at hcK ⊢
      obtain ⟨a, b⟩ := p
      generalize runPrefix (PEM40 n hn) X K (Fin.init σ) = C at ih hrun ⊢
      generalize prefixIter (fun _ => 0) cntStep K (Fin.init σ) = c at hrun hcK
      by_cases hab : a = b
      · subst hab
        have hC : C.step (PEM40 n hn) a a = C := by simp [Config.step]
        rw [hC]; exact ih v
      · have hmemA : (a, b) ∈ PairsInvolving n a :=
          (mem_PairsInvolving n a (a, b)).mpr ⟨hab, Or.inl rfl⟩
        have hmemB : (a, b) ∈ PairsInvolving n b :=
          (mem_PairsInvolving n b (a, b)).mpr ⟨hab, Or.inr rfl⟩
        have hca : c a + 2 ≤ 32 * n := by have := hcK a; rw [if_pos hmemA] at this; omega
        have hcb : c b + 2 ≤ 32 * n := by have := hcK b; rw [if_pos hmemB] at this; omega
        obtain ⟨E1, E2⟩ := pem_step_resetting_answer (trank := 40) (R := rmaxPaper n)
          (Emax := 208 * n) (Dmax := 32 * n) (hn := hn) (C a).1 (C b).1 (C a).2 (C b).2
          (hrun a).1 (hrun b).1 (c a) (c b) (hrun a).2.2 (hrun b).2.2 hca hcb
          (by rw [ih a]; exact hphi a) (by rw [ih b]; exact hphi b)
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
        · subst hwa; rw [if_pos rfl]; simp only; rw [E1]; exact ih v
        · by_cases hwb : v = b
          · subst hwb; rw [if_neg hwa, if_pos rfl]; simp only; rw [E2]; exact ih v
          · rw [if_neg hwa, if_neg hwb]; exact ih v

/-! ### The stages -/

/-- Mass of the walk-weight failure from one source. -/
theorem walk_fail_le (hn2 : 2 ≤ n) (s : Fin n) :
    (schedulerPrefixPMF n hn2 (propWindow n)).toOuterMeasure
        {σ | 3 ^ rmaxPaper n ≤ ∑ w, wtIter 3 s (propWindow n) σ w} ≤ ENNReal.ofReal (1 / n) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hK2 : (propWindow n : ℝ) ≤ 4 * (n : ℝ) * Real.log n + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hR : 60 * Real.log n ≤ rmaxPaper n := Nat.le_ceil _
  have hM := (schedulerPrefix_markov hn2 (propWindow n)
    (fun σ => ∑ w, wtIter 3 s (propWindow n) σ w) (3 ^ rmaxPaper n)).trans
    (expect_wtSum_le hn2 3 s (propWindow n))
  have hL0 : (3 : ℝ≥0∞) ^ rmaxPaper n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hLT : (3 : ℝ≥0∞) ^ rmaxPaper n ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  refine le_trans ?_ (walk_term_le hn2 (propWindow n) (rmaxPaper n) hK2 hR)
  rw [ENNReal.le_div_iff_mul_le (Or.inl hL0) (Or.inl hLT), mul_comm]
  exact hM

/-- Mass of an incomplete epidemic from one source. -/
theorem epi_fail_le (hn2 : 2 ≤ n) (s : Fin n) :
    (schedulerPrefixPMF n hn2 (propWindow n)).toOuterMeasure
        {σ | ∃ w, reachIter s (propWindow n) σ w = false} ≤ ENNReal.ofReal (1 / n) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hK1 : 4 * (n : ℝ) * Real.log n ≤ propWindow n := Nat.le_ceil _
  have hepi := (epidemic_incomplete_le hn2 s (propWindow n)).trans
    (epidemic_term_le hn2 (propWindow n) hK1)
  have hinv : ENNReal.ofReal (1 / n) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  exact (ENNReal.mul_le_mul_iff_right hinv ENNReal.ofReal_ne_top).mp hepi

/-- Fully propagating, a leader, and every answer the majority answer. -/
def FPLM (C : Config (AgentState n) Opinion n) : Prop := FPL C ∧ AllMaj C

/-- **Stage B1Z-a** (P3 Lemma 18). -/
theorem stageB1Za : StageBound ZTwo FPLM propWindow 0.9981 := by
  classical
  intro n hN hn hn2 X _ hZ
  obtain ⟨s, s', hss, h1, h2, h3⟩ := hZ
  have hn' : (1608 : ℝ) ≤ n := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by linarith
  have hR1 : 1 ≤ rmaxPaper n := one_le_rmaxPaper hn2
  have hI := zInv_of_zTwo X s s' hss h1 h2 h3 hR1
  have hs : rmaxPaper n ≤ effRc (X s).1 := by
    rw [effRc_of_resetting (h1 s (Or.inl rfl)).1, (h1 s (Or.inl rfl)).2.1]
  have hs' : rmaxPaper n ≤ effRc (X s').1 := by
    rw [effRc_of_resetting (h1 s' (Or.inr rfl)).1, (h1 s' (Or.inr rfl)).2.1]
  set K := propWindow n
  have hδ := fun (s₀ s₁ : AgentState n) (x₀ x₁ : Opinion) =>
    transitionPEM_effRc (trank := 40) (Rmax := rmaxPaper n) (Emax := 208 * n)
      (Dmax := 32 * n) (hn := hn) s₀ s₁ x₀ x₁
  -- deterministic part
  have hdet : ∀ σ : SchedulerPrefix n K, WalkOK (rmaxPaper n) s s' K σ →
      (∀ w, reachIter s K σ w = true) → FPLM (runPrefix (PEM40 n hn) X K σ) := by
    intro σ hW hreach
    have hinv := z_run (hn := hn) X s s' hI hs hs' K σ hW
    have hpos : ∀ w, 1 ≤ effRc (runPrefix (PEM40 n hn) X K σ w).1 := fun w =>
      (maxIter_pos_of_reach (rmaxPaper n) s K σ w hW.1 (hreach w)).trans
        (effRc_runPrefix_ge (PEM40 n hn) (rmaxPaper n) hδ X s hs K σ w)
    have hres : ∀ w, (runPrefix (PEM40 n hn) X K σ w).1.role = .Resetting := by
      intro w
      by_contra h
      have := hpos w
      rw [effRc_of_not_resetting h] at this
      omega
    have hmaj : majorityAnswer (runPrefix (PEM40 n hn) X K σ) = majorityAnswer X :=
      runPrefix_inv (PEM40 n hn) X (fun C => majorityAnswer C = majorityAnswer X) rfl
        (fun C hC i j => (majorityAnswer_step_eq C i j).trans hC) K σ
    refine ⟨⟨hpos, ?_⟩, fun w => ?_⟩
    · exact runPrefix_inv (PEM40 n hn) X (fun C => ∃ v, (C v).1.leader = .L)
        ⟨s, (h1 s (Or.inl rfl)).2.2.1⟩ (fun C hC i j => exists_leader_step_PEM40 C hC i j) K σ
    · rw [hmaj]
      exact (hinv.1 w (hres w)).2.2
  have hnot : probNotHitBy (PEM40 n hn) hn2 X FPLM K ≤
      ENNReal.ofReal (1 / n) + ENNReal.ofReal (1 / n) + ENNReal.ofReal (1 / n) := by
    refine (probNotHitBy_le_prefixMass (PEM40 n hn) hn2 X FPLM K).trans ?_
    refine (MeasureTheory.measure_mono (t :=
      {σ | 3 ^ rmaxPaper n ≤ ∑ w, wtIter 3 s K σ w} ∪
        {σ | 3 ^ rmaxPaper n ≤ ∑ w, wtIter 3 s' K σ w} ∪
        {σ | ∃ w, reachIter s K σ w = false}) ?_).trans
      ((MeasureTheory.measure_union_le _ _).trans (add_le_add
        ((MeasureTheory.measure_union_le _ _).trans (add_le_add (walk_fail_le hn2 s)
          (walk_fail_le hn2 s'))) (epi_fail_le hn2 s)))
    intro σ hσ
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le, not_exists,
      Bool.not_eq_false] at hcon
    exact hσ (hdet σ ⟨hcon.1.1, hcon.1.2⟩ hcon.2)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at hnot
  apply ofReal_le_probHitBy_of_probNotHitBy_le (PEM40 n hn) hn2 X FPLM K 0.9981 _
    (by norm_num) (by positivity) _ hnot
  have : (1 : ℝ) / n ≤ 1 / 1608 := by gcongr
  linarith

/-- **Stage B1Z-b** (B33 with the answers kept). -/
theorem stageB1Zb : StageBound FPLM (fun C => FDLHalf C ∧ AllMaj C) dormWindow 0.9997 := by
  classical
  intro n hN hn hn2 Y hY hA
  obtain ⟨⟨hFP, hL⟩, hM⟩ := hA
  have hn' : (1608 : ℝ) ≤ n := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by linarith
  set K := dormWindow n
  set y₀ : Fin n → ℕ := fun w => (Y w).1.resetcount
  have hY' : ∀ v, (Y v).1.role = .Resetting ∧ 1 ≤ (Y v).1.resetcount := by
    intro v
    have h := hFP v
    by_cases hr : (Y v).1.role = .Resetting
    · exact ⟨hr, by rw [effRc_of_resetting hr] at h; exact h⟩
    · rw [effRc_of_not_resetting hr] at h; omega
  have hphi : ∀ v, (Y v).1.answer ≠ .phi := fun v => by
    rw [hM v]; exact majorityAnswer_ne_phi Y
  -- deterministic part
  have hdet : ∀ σ : SchedulerPrefix n K, ¬ (∃ v, 16 * n ≤ cntIter K σ v) →
      ¬ (3 ≤ PhiN (maxFrom y₀ K σ)) →
        FDLHalf (runPrefix (PEM40 n hn) Y K σ) ∧ AllMaj (runPrefix (PEM40 n hn) Y K σ) := by
    intro σ hc hphiN
    push Not at hc hphiN
    have hc' : ∀ v, cntIter K σ v + 1 < 32 * n := fun v => by have := hc v; omega
    have hrun := dormancy_run (trank := 40) (e := 208) (d := 32) (hn := hn) Y hY' K σ hc'
    have hans := dormancy_answers (hn := hn) Y hY' hphi K σ hc'
    have hmaj : majorityAnswer (runPrefix (PEM40 n hn) Y K σ) = majorityAnswer Y :=
      runPrefix_inv (PEM40 n hn) Y (fun C => majorityAnswer C = majorityAnswer Y) rfl
        (fun C hC i j => (majorityAnswer_step_eq C i j).trans hC) K σ
    have hzero : ∀ v, maxFrom y₀ K σ v = 0 := by
      intro v
      by_contra hne
      have h3 := three_le_phiN hne
      have hle : phiN (maxFrom y₀ K σ v) ≤ PhiN (maxFrom y₀ K σ) :=
        Finset.single_le_sum (f := fun w => phiN (maxFrom y₀ K σ w))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
      omega
    have hrc : ∀ v, (runPrefix (PEM40 n hn) Y K σ v).1.resetcount = 0 := fun v => by
      rw [(hrun v).2.1]; exact hzero v
    refine ⟨⟨fun v => ⟨(hrun v).1, hrc v⟩, ?_, fun v => ?_⟩, fun v => ?_⟩
    · exact runPrefix_inv (PEM40 n hn) Y (fun C => ∃ v, (C v).1.leader = .L) hL
        (fun C hC i j => exists_leader_step_PEM40 C hC i j) K σ
    · have h1 : 32 * n ≤ (runPrefix (PEM40 n hn) Y K σ v).1.delaytimer + cntIter K σ v :=
        (hrun v).2.2 (hrc v)
      have h2 := hc v
      omega
    · rw [hans v, hmaj]; exact hM v
  -- probability part
  have hnot : probNotHitBy (PEM40 n hn) hn2 Y (fun C => FDLHalf C ∧ AllMaj C) K ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 2) + ENNReal.ofReal (1 / (3 * n)) := by
    refine (probNotHitBy_le_prefixMass (PEM40 n hn) hn2 Y _ K).trans ?_
    refine (MeasureTheory.measure_mono (t := {σ | ∃ v, 16 * n ≤ cntIter K σ v} ∪
      {σ | 3 ≤ PhiN (maxFrom y₀ K σ)}) ?_).trans
      ((MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ ?_))
    · intro σ hσ
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hcon
      exact hσ (hdet σ hcon.1 hcon.2)
    · exact count_term16_le hN K (Nat.ceil_lt_add_one (by
        have : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
        have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
        positivity)).le
    · have hp := phi_term_le hn2 y₀ (rmaxPaper n) (fun v => (hY v).2.1) K (Nat.le_ceil _)
      have h3 : (3 : ℝ≥0∞) ≠ 0 := by norm_num
      have h3' : (3 : ℝ≥0∞) ≠ ⊤ := by norm_num
      rw [← ENNReal.mul_le_mul_iff_right h3 h3']
      refine hp.trans (le_of_eq ?_)
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      field_simp
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hnot
  apply ofReal_le_probHitBy_of_probNotHitBy_le (PEM40 n hn) hn2 Y _ K 0.9997 _ (by norm_num)
    (by positivity) _ hnot
  have : (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 1608 ^ 2 := by gcongr
  have : (1 : ℝ) / (3 * n) ≤ 1 / (3 * 1608) := by gcongr
  norm_num at *
  linarith

/-- **Stage B1Z** (P3 Lemmas 18-19). -/
theorem stageB1Z : StageB1Z :=
  (stageB1Za.comp stageB1Zb (by norm_num)).mono (fun _ _ => le_rfl) (by norm_num)


/-- Non-vacuity of `ZTwo` under `GoodPaper` at `n = 1608`: two triggered leaders, all other agents
Settled at pairwise distinct non-median ranks, all opinions `A`. -/
example : ∃ X : Config (AgentState 1608) Opinion 1608, GoodPaper X ∧ ZTwo X := by
  classical
  let rk : Fin 1608 → Fin 1608 := fun w => if w = 803 then 0 else w
  let X : Config (AgentState 1608) Opinion 1608 := fun w =>
    if w = 0 ∨ w = 1 then
      (AgentState.mk .Resetting 0 .L (rmaxPaper 1608) .outA 0 0 0 0, Opinion.A)
    else (AgentState.mk .Settled (rk w) .F 0 .outA 0 0 0 0, Opinion.A)
  have hin : ∀ v, (X v).2 = Opinion.A := fun v => by
    simp only [X]; split_ifs <;> rfl
  have hA : nAOf X = 1608 := by
    have hf : Finset.univ.filter (fun v => X.inputOf v = Opinion.A) = Finset.univ :=
      Finset.filter_true_of_mem (fun v _ => hin v)
    unfold nAOf Config.agentsWithInput
    rw [hf]
    simp
  have hB : nBOf X = 0 := by
    unfold nBOf Config.agentsWithInput
    rw [Finset.filter_false_of_mem (fun v _ => by
      show ¬ X.inputOf v = Opinion.B
      rw [show X.inputOf v = Opinion.A from hin v]; decide)]
    simp
  have hmaj : majorityAnswer X = .outA := by
    unfold majorityAnswer; rw [hA, hB]; simp
  refine ⟨X, fun v => ?_, 0, 1, by decide, fun w hw => ?_, fun w h0 h1 => ?_,
    fun w w' h0 h1 h0' h1' he => ?_⟩
  · simp only [X]; split_ifs <;> simp [GoodPEM]
  · rw [hmaj]; simp [X, if_pos hw]
  · simp only [X, h0, h1, false_or, if_false, rk]
    refine ⟨by trivial, ?_⟩
    split_ifs with h
    · decide
    · intro hc
      apply h
      ext
      simp only [ceilHalf] at hc
      show (w : ℕ) = 803
      omega
  · simp only [X, h0, h1, h0', h1', false_or, if_false, rk] at he
    split_ifs at he with ha hb hb'
    · rw [ha, hb]
    · exact absurd he.symm h0'
    · exact absurd he h0
    · exact he

end Ripple.PopulationProtocol.SSEM
