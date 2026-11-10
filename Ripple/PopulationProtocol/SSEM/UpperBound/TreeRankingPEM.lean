/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# One P_EM interaction in the tree phase (P3 Lemma 1, Lemma 11)

P_EM runs `rankDeltaOSSR`, then `transitionPEM_prePhase4` (answers and the median timer only),
then Phase 4 (swap, decide, propagate) when both outputs are Settled. In the tree phase of P3
Lemma 11 no Phase-4 reset happens as long as the median timer is at least `2`, and then:

* `pem_tree_step`: the ranking projections of the new configuration are those of the
  `rankDeltaOSSR` step (`kstep`), up to the Phase-4 swap of the two participants (a permutation
  `π`; non-Settled states never move);
* `pem_tree_medTimer`: the timer of a Settled median state of the new configuration is at least
  the old median timer (or `T₀` if there was none), minus one for a tick by the rank-`(n-1)`
  state (a *tick pair*), minus one when the rank-`(n-1)` state is created in this step by the
  median (R3 review F1).

There is no swap coupling here: everything below only uses quantities that are invariant under
the swap (the multiset of ranking projections, the median timer).
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.TreeRankingCore
import Ripple.PopulationProtocol.SSEM.UpperBound.EpochCompose

namespace Ripple.PopulationProtocol.SSEM

variable {n : ℕ}

/-- The timer after Phase-4 propagation: the median state ticks against rank `n - 1`. -/
def tickT (n : ℕ) (c c' : AgentState n) : ℕ :=
  if c.rank.val + 1 = ceilHalf n ∧ c'.rank.val + 1 = n then c.timer - 1 else c.timer

theorem tickT_ge (c c' : AgentState n) : c.timer ≤ tickT n c c' + 1 := by
  unfold tickT; split_ifs <;> omega

theorem tickT_cases (c c' : AgentState n) :
    (c.rank.val + 1 = ceilHalf n ∧ c'.rank.val + 1 = n ∧ tickT n c c' = c.timer - 1) ∨
      (¬ (c.rank.val + 1 = ceilHalf n ∧ c'.rank.val + 1 = n) ∧ tickT n c c' = c.timer) := by
  unfold tickT
  split_ifs with h
  · exact Or.inl ⟨h.1, h.2, rfl⟩
  · exact Or.inr ⟨h, rfl⟩

/-! ### Phase 4 without reset -/

theorem phase4_propagate_noreset {Rmax : ℕ} (b₀ b₁ : AgentState n) (hne : b₀.rank ≠ b₁.rank)
    (h₀ : b₀.rank.val + 1 = ceilHalf n → 2 ≤ b₀.timer)
    (h₁ : b₁.rank.val + 1 = ceilHalf n → 2 ≤ b₁.timer) :
    let p := phase4_propagate n Rmax b₀ b₁
    rhoS p.1 = rhoS b₀ ∧ rhoS p.2 = rhoS b₁ ∧ p.1.timer = tickT n b₀ b₁ ∧
      p.2.timer = tickT n b₁ b₀ ∧ p.1.answer = b₀.answer ∧ p.2.answer = b₁.answer := by
  have hne' : b₀.rank.val ≠ b₁.rank.val := fun e => hne (Fin.ext e)
  unfold phase4_propagate tickT
  by_cases m₀ : b₀.rank.val + 1 = ceilHalf n
  · have m₁ : ¬ (b₁.rank.val + 1 = ceilHalf n) := by omega
    have t₀ := h₀ m₀
    by_cases l : b₁.rank.val + 1 = n
    · have : ¬ (b₀.timer - 1 = 0) := by omega
      have hc1 : ¬ n = ceilHalf n := by omega
      have hc2 : ¬ ceilHalf n = n := by omega
      simp [m₀, m₁, l, this, hc1, hc2]
    · have : ¬ (b₀.timer = 0) := by omega
      simp [m₀, m₁, l, this]
  · by_cases m₁ : b₁.rank.val + 1 = ceilHalf n
    · have t₁ := h₁ m₁
      by_cases l : b₀.rank.val + 1 = n
      · have : ¬ (b₁.timer - 1 = 0) := by omega
        have hc1 : ¬ n = ceilHalf n := by omega
        have hc2 : ¬ ceilHalf n = n := by omega
        simp [m₀, m₁, l, this, hc1, hc2]
      · have : ¬ (b₁.timer = 0) := by omega
        simp [m₀, m₁, l, this]
    · simp [m₀, m₁]

theorem phase4_decide_fields (b₀ b₁ : AgentState n) (x₀ x₁ : Opinion) :
    let d := phase4_decide n b₀ b₁ x₀ x₁
    rhoS d.1 = rhoS b₀ ∧ rhoS d.2 = rhoS b₁ ∧ d.1.timer = b₀.timer ∧ d.2.timer = b₁.timer ∧
      (d.1.answer = b₀.answer ∨ IsMedType n b₀.rank.val) ∧
      (d.2.answer = b₁.answer ∨ IsMedType n b₁.rank.val) := by
  unfold phase4_decide IsMedType ceilHalf
  split_ifs <;> simp_all <;> omega

/-- **Phase 4 without reset**: the two Settled states are possibly exchanged, the answers change
only at median-type ranks, and only the median timer changes (a tick). -/
theorem phase4_noreset {Rmax : ℕ} (a₀ a₁ : AgentState n) (x₀ x₁ : Opinion)
    (ha₀ : a₀.role = .Settled) (ha₁ : a₁.role = .Settled) (hne : a₀.rank ≠ a₁.rank)
    (h₀ : a₀.rank.val + 1 = ceilHalf n → 2 ≤ a₀.timer)
    (h₁ : a₁.rank.val + 1 = ceilHalf n → 2 ≤ a₁.timer) :
    ∃ c₀ c₁ : AgentState n, ((c₀ = a₀ ∧ c₁ = a₁) ∨ (c₀ = a₁ ∧ c₁ = a₀)) ∧
      rhoS (transitionPEM_phase4 n Rmax (a₀, a₁) x₀ x₁).1 = rhoS c₀ ∧
      rhoS (transitionPEM_phase4 n Rmax (a₀, a₁) x₀ x₁).2 = rhoS c₁ ∧
      (transitionPEM_phase4 n Rmax (a₀, a₁) x₀ x₁).1.timer = tickT n c₀ c₁ ∧
      (transitionPEM_phase4 n Rmax (a₀, a₁) x₀ x₁).2.timer = tickT n c₁ c₀ ∧
      ((transitionPEM_phase4 n Rmax (a₀, a₁) x₀ x₁).1.answer = c₀.answer ∨
        IsMedType n c₀.rank.val) ∧
      ((transitionPEM_phase4 n Rmax (a₀, a₁) x₀ x₁).2.answer = c₁.answer ∨
        IsMedType n c₁.rank.val) := by
  have hsw : phase4_swap a₀ a₁ x₀ x₁ = (a₀, a₁) ∨ phase4_swap a₀ a₁ x₀ x₁ = (a₁, a₀) := by
    unfold phase4_swap; split_ifs <;> simp
  have key : ∀ c₀ c₁ : AgentState n, c₀.rank ≠ c₁.rank →
      (c₀.rank.val + 1 = ceilHalf n → 2 ≤ c₀.timer) →
      (c₁.rank.val + 1 = ceilHalf n → 2 ≤ c₁.timer) →
      let d := phase4_decide n c₀ c₁ x₀ x₁
      let p := phase4_propagate n Rmax d.1 d.2
      rhoS p.1 = rhoS c₀ ∧ rhoS p.2 = rhoS c₁ ∧ p.1.timer = tickT n c₀ c₁ ∧
        p.2.timer = tickT n c₁ c₀ ∧ (p.1.answer = c₀.answer ∨ IsMedType n c₀.rank.val) ∧
        (p.2.answer = c₁.answer ∨ IsMedType n c₁.rank.val) := by
    intro c₀ c₁ hc hc₀ hc₁
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := phase4_decide_fields c₀ c₁ x₀ x₁
    have r1 := congrArg AgentState.rank d1
    have r2 := congrArg AgentState.rank d2
    simp only [rhoS_rank] at r1 r2
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := phase4_propagate_noreset (Rmax := Rmax)
      (phase4_decide n c₀ c₁ x₀ x₁).1 (phase4_decide n c₀ c₁ x₀ x₁).2
      (by rw [r1, r2]; exact hc) (by rw [r1, d3]; exact hc₀) (by rw [r2, d4]; exact hc₁)
    refine ⟨by rw [p1, d1], by rw [p2, d2], ?_, ?_, ?_, ?_⟩
    · rw [p3]; unfold tickT; rw [r1, r2, d3]
    · rw [p4]; unfold tickT; rw [r1, r2, d4]
    · rw [p5]; exact d5
    · rw [p6]; exact d6
  unfold transitionPEM_phase4
  simp only [ha₀, ha₁, and_self, if_true]
  rcases hsw with e | e
  · rw [e]
    exact ⟨a₀, a₁, Or.inl ⟨rfl, rfl⟩, key a₀ a₁ hne h₀ h₁⟩
  · rw [e]
    exact ⟨a₁, a₀, Or.inr ⟨rfl, rfl⟩, key a₁ a₀ (Ne.symm hne) h₁ h₀⟩

/-! ### Before Phase 4 -/

theorem prePhase4_fields {trank : ℕ}
    (rd : AgentState n × AgentState n → AgentState n × AgentState n)
    (s₀ s₁ : AgentState n) (x₀ x₁ : Opinion) :
    let p := transitionPEM_prePhase4 n trank rd s₀ s₁ x₀ x₁
    let r := rd (s₀, s₁)
    rhoS p.1 = rhoS r.1 ∧ rhoS p.2 = rhoS r.2 ∧
      p.1.timer = (if r.1.role = .Settled ∧ s₀.role ≠ .Settled ∧ r.1.rank.val + 1 = ceilHalf n
        then 7 * (trank + 4) else r.1.timer) ∧
      p.2.timer = (if r.2.role = .Settled ∧ s₁.role ≠ .Settled ∧ r.2.rank.val + 1 = ceilHalf n
        then 7 * (trank + 4) else r.2.timer) ∧
      (p.1.answer = r.1.answer ∨
        (r.1.role = .Resetting ∧ (r.1.answer = .phi ∨ s₀.role ≠ .Resetting))) ∧
      (p.2.answer = r.2.answer ∨
        (r.2.role = .Resetting ∧ (r.2.answer = .phi ∨ s₁.role ≠ .Resetting))) := by
  unfold transitionPEM_prePhase4
  rcases hr : rd (s₀, s₁) with ⟨r₀, r₁⟩
  simp only
  split_ifs <;> simp_all [rhoS_eq_iff]

/-! ### Configuration level -/

/-- The states of a configuration. -/
def kC (C : Config (AgentState n) Opinion n) : Fin n → AgentState n := fun w => (C w).1

/-- A Settled state of median rank `m* = ⌈n/2⌉ - 1`. -/
def MedAt (s : AgentState n) : Prop := s.role = .Settled ∧ s.rank.val + 1 = ceilHalf n

instance (s : AgentState n) : Decidable (MedAt s) := by unfold MedAt; infer_instance

instance (k : Fin n → AgentState n) (j : ℕ) : Decidable (Asg k j) := by
  unfold Asg; infer_instance

/-- The median timer (`T₀` when there is no Settled median state). -/
noncomputable def medTimer (T₀ : ℕ) (C : Config (AgentState n) Opinion n) : ℕ :=
  if h : ∃ w, MedAt (C w).1 then (C h.choose).1.timer else T₀

theorem medTimer_eq {T₀ : ℕ} {C : Config (AgentState n) Opinion n} (hT : TreeCore (kC C))
    {w : Fin n} (hw : MedAt (C w).1) : medTimer T₀ C = (C w).1.timer := by
  have h : ∃ w, MedAt (C w).1 := ⟨w, hw⟩
  unfold medTimer
  rw [dif_pos h]
  have hc := h.choose_spec
  have : h.choose = w := hT.inj _ _ hc.1 hw.1 (Fin.ext (by
    have := hc.2; have := hw.2; simp only [kC] at *; omega))
  rw [this]

theorem medTimer_none {T₀ : ℕ} {C : Config (AgentState n) Opinion n}
    (h : ∀ w, ¬ MedAt (C w).1) : medTimer T₀ C = T₀ := by
  unfold medTimer
  rw [dif_neg (fun ⟨w, hw⟩ => h w hw)]

/-- The tick pair: the two participants hold the median state and the rank-`(n-1)` state. -/
def TickPair (C : Config (AgentState n) Opinion n) (u v : Fin n) : Prop :=
  (MedAt (C u).1 ∧ (C v).1.role = .Settled ∧ (C v).1.rank.val + 1 = n) ∨
    (MedAt (C v).1 ∧ (C u).1.role = .Settled ∧ (C u).1.rank.val + 1 = n)

instance (C : Config (AgentState n) Opinion n) (u v : Fin n) : Decidable (TickPair C u v) := by
  unfold TickPair; infer_instance

section Step

variable {trank Rmax Emax Dmax : ℕ} {hn : 0 < n}

theorem pem_delta_eq (rd : AgentState n × AgentState n → AgentState n × AgentState n)
    (C : Config (AgentState n) Opinion n) (u v : Fin n) :
    (protocolPEM n trank Rmax rd).δ (C u, C v) =
      transitionPEM_phase4 n Rmax
        (transitionPEM_prePhase4 n trank rd (C u).1 (C v).1 (C u).2 (C v).2) (C u).2 (C v).2 :=
  rfl

theorem step_other {P : Protocol (AgentState n) Opinion Output}
    (C : Config (AgentState n) Opinion n) {u v w : Fin n} (hu : w ≠ u) (hv : w ≠ v) :
    C.step P u v w = C w := by
  unfold Config.step
  split_ifs <;> simp [hu, hv]

theorem trStep_fst {P : Protocol (AgentState n) Opinion Output}
    (C : Config (AgentState n) Opinion n) {u v : Fin n} (huv : u ≠ v) :
    (C.step P u v u).1 = (P.δ (C u, C v)).1 := by
  unfold Config.step
  simp [huv]

theorem trStep_snd {P : Protocol (AgentState n) Opinion Output}
    (C : Config (AgentState n) Opinion n) {u v : Fin n} (huv : u ≠ v) :
    (C.step P u v v).1 = (P.δ (C u, C v)).2 := by
  unfold Config.step
  simp [huv, Ne.symm huv]

/-- One median-timer bound for a participant `x` with partner `y` (both orders of the pair). -/
theorem medTimer_part {T₀ : ℕ} (C : Config (AgentState n) Opinion n) (K' : Fin n → AgentState n)
    {x y : Fin n} (hxy : x ≠ y) (hT : TreeCore (kC C)) (hT' : TreeCore K')
    (hother : ∀ w, w ≠ x → w ≠ y → K' w = (C w).1)
    (hsx : StepRel Emax (C x).1 (K' x)) (hsy : StepRel Emax (C y).1 (K' y))
    (hnew : (K' x).role = .Settled → (C x).1.role ≠ .Settled →
      (K' x).rank.val = 0 ∨ ((C y).1.role = .Settled ∧
        (K' x).rank.val = 2 * (C y).1.rank.val + (C y).1.children + 1 ∧
        (K' y).rank = (C y).1.rank))
    (p p' : AgentState n) (hp : rhoS p = rhoS (K' x)) (hp' : rhoS p' = rhoS (K' y))
    (hpt : p.timer = if (K' x).role = .Settled ∧ (C x).1.role ≠ .Settled ∧
      (K' x).rank.val + 1 = ceilHalf n then T₀ else (C x).1.timer)
    (hmed : MedAt p) (hn3 : 3 ≤ n) :
    medTimer T₀ C ≤ p.timer ∧
      (p'.role = .Settled → p'.rank.val + 1 = n →
        medTimer T₀ C + 1 ≤ p.timer + (if TickPair C x y then 1 else 0) +
          (if ¬ Asg (kC C) (n - 1) ∧ Asg K' (n - 1) then 1 else 0)) := by
  obtain ⟨hpS, hpm⟩ := hmed
  have ep := rhoS_eq_iff.mp hp
  have ep' := rhoS_eq_iff.mp hp'
  have hxS : (K' x).role = .Settled := ep.1 ▸ hpS
  have hxm : (K' x).rank.val + 1 = ceilHalf n := by rw [← ep.2.1]; exact hpm
  have hceil : ceilHalf n < n := by unfold ceilHalf; omega
  -- Settled states of `C` persist in `K'`
  have hpers : ∀ w, (C w).1.role = .Settled → (K' w).role = .Settled ∧ (K' w).rank = (C w).1.rank := by
    intro w hw
    by_cases hwx : w = x
    · subst hwx; exact hsx.settled hw
    · by_cases hwy : w = y
      · subst hwy; exact hsy.settled hw
      · rw [hother w hwx hwy]; exact ⟨hw, rfl⟩
  by_cases hold : (C x).1.role = .Settled
  · -- the median state existed before
    have hpt' : p.timer = (C x).1.timer := by
      rw [hpt, if_neg (fun h => h.2.1 hold)]
    have hrk : (C x).1.rank = (K' x).rank := ((hsx.settled hold).2).symm
    have hCm : MedAt (C x).1 := ⟨hold, by rw [hrk]; exact hxm⟩
    have hτ : medTimer T₀ C = (C x).1.timer := medTimer_eq hT hCm
    refine ⟨by rw [hτ, hpt'], fun hp'S hp'l => ?_⟩
    have hyS : (K' y).role = .Settled := ep'.1 ▸ hp'S
    have hyl : (K' y).rank.val + 1 = n := by rw [← ep'.2.1]; exact hp'l
    by_cases holdy : (C y).1.role = .Settled
    · have hrky : (C y).1.rank = (K' y).rank := ((hsy.settled holdy).2).symm
      have htp : TickPair C x y := Or.inl ⟨hCm, holdy, by rw [hrky]; exact hyl⟩
      rw [if_pos htp, hτ, hpt']; omega
    · -- the rank-(n-1) state is new
      have hnl : ¬ Asg (kC C) (n - 1) ∧ Asg K' (n - 1) := by
        refine ⟨?_, ⟨y, hyS, by omega⟩⟩
        rintro ⟨w, hw, hwr⟩
        have hwy : w ≠ y := by intro e; subst e; exact holdy hw
        obtain ⟨h1, h2⟩ := hpers w hw
        exact hwy (hT'.inj w y h1 hyS (Fin.ext (by
          have : ((C w).1.rank).val = n - 1 := hwr
          rw [h2]; omega)))
      rw [if_pos hnl, hτ, hpt']; omega
  · -- the median state is new: no median before, partner is its recruiter
    have hpt' : p.timer = T₀ := by rw [hpt, if_pos ⟨hxS, hold, hxm⟩]
    have hnone : ∀ w, ¬ MedAt (C w).1 := by
      rintro w ⟨hw, hwm⟩
      have hwx : w ≠ x := by intro e; subst e; exact hold hw
      obtain ⟨h1, h2⟩ := hpers w hw
      exact hwx (hT'.inj w x h1 hxS (Fin.ext (by
        have : ((C w).1.rank).val + 1 = ceilHalf n := hwm
        rw [h2]; omega)))
    have hτ : medTimer T₀ C = T₀ := medTimer_none hnone
    refine ⟨by rw [hτ, hpt'], fun hp'S hp'l => ?_⟩
    have hyl : (K' y).rank.val + 1 = n := by rw [← ep'.2.1]; exact hp'l
    exfalso
    rcases hnew hxS hold with h0 | ⟨_, hr, hry⟩
    · unfold ceilHalf at hxm; omega
    · have := (K' x).rank.isLt
      rw [hry] at hyl; omega

end Step

section Main

variable {trank Rmax Emax Dmax : ℕ} {hn : 0 < n}

/-- Hypotheses of a tree-phase step: valid tree, no errorcount about to expire, median timer
at least `2` (so no Phase-4 reset). -/
structure TreeStepHyp (C : Config (AgentState n) Opinion n) : Prop where
  core : TreeCore (kC C)
  ec : ∀ w, (C w).1.role = .Unsettled → 2 ≤ (C w).1.errorcount
  med : ∀ w, MedAt (C w).1 → 2 ≤ (C w).1.timer

theorem tickPair_comm (C : Config (AgentState n) Opinion n) (u v : Fin n) :
    TickPair C v u ↔ TickPair C u v := Or.comm

/-- **One P_EM interaction in the tree phase.** -/
theorem pem_tree_step (C : Config (AgentState n) Opinion n) (h : TreeStepHyp C) {u v : Fin n}
    (huv : u ≠ v) (hT0 : 2 ≤ 7 * (trank + 4)) (hn3 : 3 ≤ n) :
    TreeCore (kstep (rankDeltaOSSR Rmax Emax Dmax hn) (kC C) u v) ∧
      StepRel Emax (C u).1 (kstep (rankDeltaOSSR Rmax Emax Dmax hn) (kC C) u v u) ∧
      StepRel Emax (C v).1 (kstep (rankDeltaOSSR Rmax Emax Dmax hn) (kC C) u v v) ∧
      ∃ π : Equiv.Perm (Fin n),
        (∀ w, rhoS (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v w).1 =
          rhoS (kstep (rankDeltaOSSR Rmax Emax Dmax hn) (kC C) u v (π w))) ∧
        (∀ w, (kstep (rankDeltaOSSR Rmax Emax Dmax hn) (kC C) u v (π w)).role ≠ .Settled →
          π w = w) ∧
        (∀ w, MedAt (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            u v w).1 →
          medTimer (7 * (trank + 4)) C ≤
            (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v w).1.timer +
              (if TickPair C u v then 1 else 0) +
              (if ¬ Asg (kC C) (n - 1) ∧
                  Asg (kstep (rankDeltaOSSR Rmax Emax Dmax hn) (kC C) u v) (n - 1)
                then 1 else 0)) ∧
        (∀ w, (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v w).1.answer =
            (C (π w)).1.answer ∨
          ((C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v w).1.role =
              .Settled ∧
            IsMedType n
              (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v w).1.rank.val) ∨
          ((C (π w)).1.role = .Resetting ∧ (C (π w)).1.answer = .phi)) := by
  set K' := kstep (rankDeltaOSSR Rmax Emax Dmax hn) (kC C) u v with hK'
  set P := protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  set T₀ := 7 * (trank + 4) with hT₀
  have hvu : v ≠ u := Ne.symm huv
  obtain ⟨hT', hsu, hsv⟩ := treeCore_kstep (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) h.core huv (h.ec u) (h.ec v)
  obtain ⟨hnu, hnv⟩ := kstep_newSettled (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) h.core huv (h.ec u) (h.ec v)
  refine ⟨hT', hsu, hsv, ?_⟩
  set s₀ := (C u).1 with hs₀
  set s₁ := (C v).1 with hs₁
  have hK'u : K' u = (rankDeltaOSSR Rmax Emax Dmax hn (s₀, s₁)).1 := kstep_fst _ _ _ _
  have hK'v : K' v = (rankDeltaOSSR Rmax Emax Dmax hn (s₀, s₁)).2 := kstep_snd _ _ huv
  have hK'o : ∀ w, w ≠ u → w ≠ v → K' w = (C w).1 := fun w hwu hwv => kstep_other _ _ hwu hwv
  obtain ⟨rt1, rt2⟩ := tr_rankDeltaOSSR_timer (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) s₀ s₁
  obtain ⟨pr1, pr2, pt1, pt2, pa1, pa2⟩ :=
    prePhase4_fields (trank := trank) (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁ (C u).2 (C v).2
  obtain ⟨ra1, ra2⟩ := rankDeltaOSSR_answer_preserved (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) s₀ s₁
  -- the answers before Phase 4 are the old ones, except for a dormant agent with answer `φ`
  have hpa1 : (transitionPEM_prePhase4 n trank (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁
      (C u).2 (C v).2).1.answer = s₀.answer ∨
      (s₀.role = .Resetting ∧ s₀.answer = .phi) := by
    rcases pa1 with e | ⟨hR, hor⟩
    · left; rw [e, ra1]
    · have hs0R : s₀.role = .Resetting :=
        (hsu.resetting (by show (K' u).role = .Resetting; rw [hK'u]; exact hR)).1
      rcases hor with hp | hne
      · right; exact ⟨hs0R, by rw [← ra1]; exact hp⟩
      · exact absurd hs0R hne
  have hpa2 : (transitionPEM_prePhase4 n trank (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁
      (C u).2 (C v).2).2.answer = s₁.answer ∨
      (s₁.role = .Resetting ∧ s₁.answer = .phi) := by
    rcases pa2 with e | ⟨hR, hor⟩
    · left; rw [e, ra2]
    · have hs1R : s₁.role = .Resetting :=
        (hsv.resetting (by show (K' v).role = .Resetting; rw [hK'v]; exact hR)).1
      rcases hor with hp | hne
      · right; exact ⟨hs1R, by rw [← ra2]; exact hp⟩
      · exact absurd hs1R hne
  set pre := transitionPEM_prePhase4 n trank (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁
    (C u).2 (C v).2 with hpre
  rw [rt1, ← hK'u] at pt1
  rw [rt2, ← hK'v] at pt2
  rw [← hK'u] at pr1
  rw [← hK'v] at pr2
  have hCu : (C.step P u v u).1 = (transitionPEM_phase4 n Rmax pre (C u).2 (C v).2).1 := by
    rw [trStep_fst C huv, hP, pem_delta_eq]
  have hCv : (C.step P u v v).1 = (transitionPEM_phase4 n Rmax pre (C u).2 (C v).2).2 := by
    rw [trStep_snd C huv, hP, pem_delta_eq]
  have hCo : ∀ w, w ≠ u → w ≠ v → C.step P u v w = C w := fun w hwu hwv => step_other C hwu hwv
  have mtu := fun hm => medTimer_part (T₀ := T₀) C K' huv h.core hT' hK'o hsu hsv hnu
    pre.1 pre.2 pr1 pr2 pt1 hm hn3
  have mtv := fun hm => medTimer_part (T₀ := T₀) C K' hvu h.core hT'
    (fun w h1 h2 => hK'o w h2 h1) hsv hsu hnv pre.2 pre.1 pr2 pr1 pt2 hm hn3
  simp only [tickPair_comm] at mtv
  -- median timers of the prePhase4 states are at least 2
  have hm2 : ∀ (x : Fin n) (p : AgentState n), rhoS p = rhoS (K' x) →
      StepRel Emax (C x).1 (K' x) →
      p.timer = (if (K' x).role = .Settled ∧ (C x).1.role ≠ .Settled ∧
        (K' x).rank.val + 1 = ceilHalf n then T₀ else (C x).1.timer) →
      p.role = .Settled → p.rank.val + 1 = ceilHalf n → 2 ≤ p.timer := by
    intro x p hp hsx hpt hpS hpm
    have ep := rhoS_eq_iff.mp hp
    rw [hpt]
    split_ifs with hc
    · exact hT0
    · have hxS : (K' x).role = .Settled := ep.1 ▸ hpS
      have hxm : (K' x).rank.val + 1 = ceilHalf n := ep.2.1 ▸ hpm
      have hold : (C x).1.role = .Settled := by
        by_contra hne; exact hc ⟨hxS, hne, hxm⟩
      exact h.med x ⟨hold, by rw [← (hsx.settled hold).2]; exact hxm⟩
  -- the medTimer bound for an untouched agent
  have hotherT : ∀ w, w ≠ u → w ≠ v → MedAt (C.step P u v w).1 →
      T₀ ≥ 0 → medTimer T₀ C ≤ (C.step P u v w).1.timer := by
    intro w hwu hwv hm _
    rw [hCo w hwu hwv] at hm ⊢
    rw [medTimer_eq h.core hm]
  have medrho : ∀ p q : AgentState n, rhoS p = rhoS q → (MedAt p ↔ MedAt q) := by
    intro p q e
    have := rhoS_eq_iff.mp e
    unfold MedAt; rw [this.1, this.2.1]
  by_cases hS : pre.1.role = .Settled ∧ pre.2.role = .Settled
  · have e1 := rhoS_eq_iff.mp pr1
    have e2 := rhoS_eq_iff.mp pr2
    have hne : pre.1.rank ≠ pre.2.rank := by
      intro e
      apply huv
      exact hT'.inj u v (e1.1 ▸ hS.1) (e2.1 ▸ hS.2) (by rw [← e1.2.1, ← e2.2.1, e])
    obtain ⟨c₀, c₁, hc, b1, b2, t1, t2, a1, a2⟩ := phase4_noreset (Rmax := Rmax) pre.1 pre.2
      (C u).2 (C v).2 hS.1 hS.2 hne (hm2 u pre.1 pr1 hsu pt1 hS.1)
      (hm2 v pre.2 pr2 hsv pt2 hS.2)
    rw [← hCu] at b1 t1 a1
    rw [← hCv] at b2 t2 a2
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨Equiv.refl _, ?_, fun w _ => rfl, ?_, ?_⟩
      · intro w
        simp only [Equiv.refl_apply]
        by_cases hwu : w = u
        · subst hwu; rw [b1, pr1]
        · by_cases hwv : w = v
          · subst hwv; rw [b2, pr2]
          · rw [hCo w hwu hwv, hK'o w hwu hwv]
      · intro w hm
        by_cases hwu : w = u
        · subst hwu
          have hmp : MedAt pre.1 := (medrho _ _ b1).mp hm
          rw [t1]
          rcases tickT_cases pre.1 pre.2 with ⟨-, htk2, e⟩ | ⟨-, e⟩ <;> rw [e]
          · have h2 := hm2 w pre.1 pr1 hsu pt1 hS.1 hmp.2
            have := (mtu hmp).2 hS.2 htk2
            omega
          · have := (mtu hmp).1; omega
        · by_cases hwv : w = v
          · subst hwv
            have hmp : MedAt pre.2 := (medrho _ _ b2).mp hm
            rw [t2]
            rcases tickT_cases pre.2 pre.1 with ⟨-, htk2, e⟩ | ⟨-, e⟩ <;> rw [e]
            · have h2 := hm2 w pre.2 pr2 hsv pt2 hS.2 hmp.2
              have := (mtv hmp).2 hS.1 htk2
              omega
            · have := (mtv hmp).1; omega
          · have := hotherT w hwu hwv hm (Nat.zero_le _); omega
      · intro w
        simp only [Equiv.refl_apply]
        by_cases hwu : w = u
        · subst hwu
          rcases a1 with e | hmed
          · rw [e]; rcases hpa1 with e' | e'
            · exact Or.inl e'
            · exact Or.inr (Or.inr e')
          · have eb := rhoS_eq_iff.mp b1
            exact Or.inr (Or.inl ⟨eb.1.trans hS.1, by rw [eb.2.1]; exact hmed⟩)
        · by_cases hwv : w = v
          · subst hwv
            rcases a2 with e | hmed
            · rw [e]; rcases hpa2 with e' | e'
              · exact Or.inl e'
              · exact Or.inr (Or.inr e')
            · have eb := rhoS_eq_iff.mp b2
              exact Or.inr (Or.inl ⟨eb.1.trans hS.2, by rw [eb.2.1]; exact hmed⟩)
          · exact Or.inl (by rw [hCo w hwu hwv])
    · refine ⟨Equiv.swap u v, ?_, ?_, ?_, ?_⟩
      · intro w
        by_cases hwu : w = u
        · subst hwu; rw [Equiv.swap_apply_left, b1, pr2]
        · by_cases hwv : w = v
          · subst hwv; rw [Equiv.swap_apply_right, b2, pr1]
          · rw [Equiv.swap_apply_of_ne_of_ne hwu hwv, hCo w hwu hwv, hK'o w hwu hwv]
      · intro w hw
        by_cases hwu : w = u
        · subst hwu; rw [Equiv.swap_apply_left] at hw; exact absurd (e2.1 ▸ hS.2) hw
        · by_cases hwv : w = v
          · subst hwv; rw [Equiv.swap_apply_right] at hw; exact absurd (e1.1 ▸ hS.1) hw
          · exact Equiv.swap_apply_of_ne_of_ne hwu hwv
      · intro w hm
        by_cases hwu : w = u
        · subst hwu
          have hmp : MedAt pre.2 := (medrho _ _ b1).mp hm
          rw [t1]
          rcases tickT_cases pre.2 pre.1 with ⟨-, htk2, e⟩ | ⟨-, e⟩ <;> rw [e]
          · have h2 := hm2 v pre.2 pr2 hsv pt2 hS.2 hmp.2
            have := (mtv hmp).2 hS.1 htk2
            omega
          · have := (mtv hmp).1; omega
        · by_cases hwv : w = v
          · subst hwv
            have hmp : MedAt pre.1 := (medrho _ _ b2).mp hm
            rw [t2]
            rcases tickT_cases pre.1 pre.2 with ⟨-, htk2, e⟩ | ⟨-, e⟩ <;> rw [e]
            · have h2 := hm2 u pre.1 pr1 hsu pt1 hS.1 hmp.2
              have := (mtu hmp).2 hS.2 htk2
              omega
            · have := (mtu hmp).1; omega
          · have := hotherT w hwu hwv hm (Nat.zero_le _); omega
      · intro w
        by_cases hwu : w = u
        · subst hwu
          rw [Equiv.swap_apply_left]
          rcases a1 with e | hmed
          · rw [e]; rcases hpa2 with e' | e'
            · exact Or.inl e'
            · exact Or.inr (Or.inr e')
          · have eb := rhoS_eq_iff.mp b1
            exact Or.inr (Or.inl ⟨eb.1.trans hS.2, by rw [eb.2.1]; exact hmed⟩)
        · by_cases hwv : w = v
          · subst hwv
            rw [Equiv.swap_apply_right]
            rcases a2 with e | hmed
            · rw [e]; rcases hpa1 with e' | e'
              · exact Or.inl e'
              · exact Or.inr (Or.inr e')
            · have eb := rhoS_eq_iff.mp b2
              exact Or.inr (Or.inl ⟨eb.1.trans hS.1, by rw [eb.2.1]; exact hmed⟩)
          · rw [Equiv.swap_apply_of_ne_of_ne hwu hwv]
            exact Or.inl (by rw [hCo w hwu hwv])
  · have hid : transitionPEM_phase4 n Rmax pre (C u).2 (C v).2 = pre :=
      transitionPEM_phase4_of_not_both_settled hS
    rw [hid] at hCu hCv
    refine ⟨Equiv.refl _, ?_, fun w _ => rfl, ?_, ?_⟩
    · intro w
      simp only [Equiv.refl_apply]
      by_cases hwu : w = u
      · subst hwu; rw [hCu, pr1]
      · by_cases hwv : w = v
        · subst hwv; rw [hCv, pr2]
        · rw [hCo w hwu hwv, hK'o w hwu hwv]
    · intro w hm
      by_cases hwu : w = u
      · subst hwu; rw [hCu] at hm ⊢; have := (mtu hm).1; omega
      · by_cases hwv : w = v
        · subst hwv; rw [hCv] at hm ⊢; have := (mtv hm).1; omega
        · have := hotherT w hwu hwv hm (Nat.zero_le _); omega
    · intro w
      simp only [Equiv.refl_apply]
      by_cases hwu : w = u
      · subst hwu; rw [hCu]; exact hpa1.imp id Or.inr
      · by_cases hwv : w = v
        · subst hwv; rw [hCv]; exact hpa2.imp id Or.inr
        · exact Or.inl (by rw [hCo w hwu hwv])

end Main

end Ripple.PopulationProtocol.SSEM
