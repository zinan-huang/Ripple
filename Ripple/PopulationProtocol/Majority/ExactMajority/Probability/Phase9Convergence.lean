
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase9Convergence

Phase-9 clone of the real-kernel Phase-2 opinion-union epidemic.

`Phase2Convergence.phase2Convergence` pins the consensus window at `phase.val = 2`,
so it cannot directly discharge work slot 9.  This file clones the proof with the
window pin changed to `phase.val = 9`.

The only protocol-side fact needed for the clone is landed definitionally:

  `Phase9Transition L K s t = Phase2Transition L K s t`.

No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase2Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace Phase9Convergence

open Phase2Convergence

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part A — phase-9 informed/susceptible counts and window. -/

/-- A phase-9 agent is `U`-informed when it has opinion set exactly `U`. -/
def informedP9 (U : Fin 8) (a : AgentState L K) : Prop :=
  a.phase.val = 9 ∧ a.opinions = U

instance (U : Fin 8) (a : AgentState L K) : Decidable (informedP9 U a) := by
  unfold informedP9
  infer_instance

/-- The number of phase-9 `U`-informed agents. -/
def informedU9 (U : Fin 8) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => informedP9 U a) c

/-- A phase-9 susceptible agent with opinion set exactly `v`. -/
def susceptibleP9 (v : Fin 8) (a : AgentState L K) : Prop :=
  a.phase.val = 9 ∧ a.opinions = v

instance (v : Fin 8) (a : AgentState L K) : Decidable (susceptibleP9 v a) := by
  unfold susceptibleP9
  infer_instance

/-- Phase-9 opinion consensus window: fixed size `n`, all agents phase 9, and every
opinion set is either `U` or `v`. -/
def Q9 (U v : Fin 8) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, a.phase.val = 9 ∧ (a.opinions = U ∨ a.opinions = v)

instance (U v : Fin 8) (n : ℕ) (c : Config (AgentState L K)) : Decidable (Q9 U v n c) := by
  unfold Q9
  infer_instance

/-! ## Part B — deterministic phase-9 pair behaviour. -/

/-- On two phase-9 agents in the single-sign consensus regime, the full transition
keeps both agents in phase 9 and sets both opinions to the union value. -/
theorem Transition_consensus_pair9 (U v : Fin 8)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (s t : AgentState L K)
    (hs9 : s.phase.val = 9) (ht9 : t.phase.val = 9)
    (hsop : s.opinions = U ∨ s.opinions = v)
    (htop : t.opinions = U ∨ t.opinions = v) :
    let s' := (Transition L K s t).1
    let t' := (Transition L K s t).2
    s'.phase.val = 9 ∧ t'.phase.val = 9 ∧
      (s'.opinions = U ∨ s'.opinions = v) ∧
      (t'.opinions = U ∨ t'.opinions = v) ∧
      s'.opinions = opinionsUnion s.opinions t.opinions ∧
      t'.opinions = opinionsUnion s.opinions t.opinions := by
  intro s' t'
  have hs_phase_eq : s.phase = ⟨9, by decide⟩ := Fin.ext hs9
  have ht_phase_eq : t.phase = ⟨9, by decide⟩ := Fin.ext ht9
  have hepidemic : phaseEpidemicUpdate L K s t = (s, t) := by
    unfold phaseEpidemicUpdate
    rw [hs_phase_eq, ht_phase_eq, max_self]
    simp only [runInitsBetween_self_api]
    have hs_self : ({s with phase := (⟨9, by decide⟩ : Fin 11)} : AgentState L K) = s := by
      rw [← hs_phase_eq]
    have ht_self : ({t with phase := (⟨9, by decide⟩ : Fin 11)} : AgentState L K) = t := by
      rw [← ht_phase_eq]
    rw [hs_self, ht_self]
    rw [if_neg (by push Not; intro _; simp)]
  set univ := opinionsUnion s.opinions t.opinions with huniv
  have hunion_val : univ = U ∨ univ = v := by
    rcases hsop with hsU | hsv <;> rcases htop with htU | htv
    · left; rw [huniv, hsU, htU, hUU]
    · left; rw [huniv, hsU, htv, hUv]
    · left; rw [huniv, hsv, htU, hvU]
    · right; rw [huniv, hsv, htv, hvv]
  have hunion_single : singleSign univ := by
    rcases hunion_val with h | h <;> rw [h]
    · exact hUsign
    · exact hvsign
  have hnotboth : (hasMinusOne univ && hasPlusOne univ) = false :=
    not_both_signs_of_singleSign hunion_single
  have hTrans : Transition L K s t =
      (finishPhase10Entry L K s (Phase2Transition L K s t).1,
       finishPhase10Entry L K t (Phase2Transition L K s t).2) := by
    unfold Transition
    rw [hepidemic]
    simp only [hs_phase_eq, Phase9Transition]
  have hP2_phase_op :
      (Phase2Transition L K s t).1.phase = s.phase ∧
      (Phase2Transition L K s t).1.opinions = univ ∧
      (Phase2Transition L K s t).2.phase = t.phase ∧
      (Phase2Transition L K s t).2.opinions = univ := by
    unfold Phase2Transition
    rw [← huniv]
    rw [if_neg (by simp [hnotboth])]
    split_ifs <;> simp_all
  have hsafter : ((Phase2Transition L K s t).1).phase.val ≠ 10 := by
    rw [hP2_phase_op.1, hs9]
    omega
  have htafter : ((Phase2Transition L K s t).2).phase.val ≠ 10 := by
    rw [hP2_phase_op.2.2.1, ht9]
    omega
  have hsfin :
      finishPhase10Entry L K s (Phase2Transition L K s t).1 =
        (Phase2Transition L K s t).1 :=
    finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _ hsafter
  have htfin :
      finishPhase10Entry L K t (Phase2Transition L K s t).2 =
        (Phase2Transition L K s t).2 :=
    finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _ htafter
  have hs'_phase : s'.phase.val = 9 := by
    show (Transition L K s t).1.phase.val = 9
    rw [hTrans]
    show (finishPhase10Entry L K s (Phase2Transition L K s t).1).phase.val = 9
    rw [hsfin, hP2_phase_op.1, hs9]
  have ht'_phase : t'.phase.val = 9 := by
    show (Transition L K s t).2.phase.val = 9
    rw [hTrans]
    show (finishPhase10Entry L K t (Phase2Transition L K s t).2).phase.val = 9
    rw [htfin, hP2_phase_op.2.2.1, ht9]
  have hs'_op : s'.opinions = univ := by
    show (Transition L K s t).1.opinions = univ
    rw [hTrans]
    show (finishPhase10Entry L K s (Phase2Transition L K s t).1).opinions = univ
    rw [hsfin]
    exact hP2_phase_op.2.1
  have ht'_op : t'.opinions = univ := by
    show (Transition L K s t).2.opinions = univ
    rw [hTrans]
    show (finishPhase10Entry L K t (Phase2Transition L K s t).2).opinions = univ
    rw [htfin]
    exact hP2_phase_op.2.2.2
  refine ⟨hs'_phase, ht'_phase, ?_, ?_, hs'_op, ht'_op⟩
  · rw [hs'_op]; exact hunion_val
  · rw [ht'_op]; exact hunion_val

/-! ## Part C — informed-count monotonicity. -/

private theorem mem_of_applicable_left9 {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c := by
  have hle : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
  exact Multiset.mem_of_le hle (by simp)

private theorem mem_of_applicable_right9 {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c := by
  have hle : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
  exact Multiset.mem_of_le hle (by simp)

/-- `countP informedP9` over a two-element pair. -/
theorem countP_informedP9_pair (U : Fin 8) (x y : AgentState L K) :
    Multiset.countP (fun a => informedP9 U a) ({x, y} : Multiset (AgentState L K))
      = (if informedP9 U x then 1 else 0) + (if informedP9 U y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  ring

/-- Phase-9 per-pair informed-count monotonicity in the consensus window. -/
theorem informedP9_pair_mono (U v : Fin 8)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (s t : AgentState L K)
    (hs9 : s.phase.val = 9) (ht9 : t.phase.val = 9)
    (hsop : s.opinions = U ∨ s.opinions = v)
    (htop : t.opinions = U ∨ t.opinions = v) :
    Multiset.countP (fun a => informedP9 U a) ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => informedP9 U a)
          ({(Transition L K s t).1, (Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  obtain ⟨hs'9, ht'9, _, _, hs'opU, ht'opU⟩ :=
    Transition_consensus_pair9 U v hUsign hvsign hvU hUv hvv hUU s t hs9 ht9 hsop htop
  set s' := (Transition L K s t).1
  set t' := (Transition L K s t).2
  rw [countP_informedP9_pair, countP_informedP9_pair]
  set univ := opinionsUnion s.opinions t.opinions with huniv
  have hs'op : s'.opinions = univ := hs'opU
  have ht'op : t'.opinions = univ := ht'opU
  have hs'inf : informedP9 U s' ↔ univ = U := by
    unfold informedP9
    rw [hs'op]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨hs'9, h⟩
  have ht'inf : informedP9 U t' ↔ univ = U := by
    unfold informedP9
    rw [ht'op]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨ht'9, h⟩
  have hsinf : informedP9 U s ↔ s.opinions = U := by
    unfold informedP9
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨hs9, h⟩
  have htinf : informedP9 U t ↔ t.opinions = U := by
    unfold informedP9
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨ht9, h⟩
  by_cases hsU : s.opinions = U
  · have huU : univ = U := by
      rw [huniv, hsU]
      rcases htop with h | h <;> rw [h]
      · exact hUU
      · exact hUv
    rw [if_pos (hs'inf.mpr huU), if_pos (ht'inf.mpr huU)]
    have : (if informedP9 U s then 1 else 0) + (if informedP9 U t then 1 else 0) ≤ 2 := by
      split_ifs <;> omega
    omega
  · by_cases htU : t.opinions = U
    · have huU : univ = U := by
        rw [huniv]
        rcases hsop with h | h
        · exact absurd h hsU
        · rw [h, htU, hvU]
      rw [if_pos (hs'inf.mpr huU), if_pos (ht'inf.mpr huU)]
      have : (if informedP9 U s then 1 else 0) + (if informedP9 U t then 1 else 0) ≤ 2 := by
        split_ifs <;> omega
      omega
    · rw [if_neg (by rw [hsinf]; exact hsU), if_neg (by rw [htinf]; exact htU)]
      omega

/-- `informedU9 U` is non-decreasing under any chosen-pair update inside `Q9`. -/
theorem informedU9_stepOrSelf_ge (U v : Fin 8) (n : ℕ)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (c : Config (AgentState L K)) (hw : Q9 U v n c) (r₁ r₂ : AgentState L K) :
    informedU9 U c ≤ informedU9 U (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmem1 := mem_of_applicable_left9 happ
    have hmem2 := mem_of_applicable_right9 happ
    obtain ⟨h1p, h1op⟩ := hw.2 r₁ hmem1
    obtain ⟨h2p, h2op⟩ := hw.2 r₂ hmem2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    unfold informedU9
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair_le :
        Multiset.countP (fun a => informedP9 U a) ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => informedP9 U a) c :=
      Multiset.countP_le_of_le _ hsub
    have hpair :=
      informedP9_pair_mono U v hUsign hvsign hvU hUv hvv hUU r₁ r₂ h1p h2p h1op h2op
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- Support-form monotonicity of `informedU9`. -/
theorem informedU9_ge_monotone (U v : Fin 8) (n m : ℕ)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (c c' : Config (AgentState L K)) (hw : Q9 U v n c)
    (h : m ≤ informedU9 U c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    m ≤ informedU9 U c' := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c =
        (NonuniformMajority L K).stepDist c hc by
          unfold Protocol.stepDistOrSelf
          rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact le_trans h (informedU9_stepOrSelf_ge U v n hUsign hvsign hvU hUv hvv hUU c hw r₁ r₂)
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf
        rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst c'
    exact h

/-! ## Part D — advance rectangle. -/

/-- A phase-9 informed/susceptible ordered pair advances the informed count. -/
theorem informedP9_pair_advances (U v : Fin 8)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v)
    (s t : AgentState L K)
    (hs9 : s.phase.val = 9) (ht9 : t.phase.val = 9)
    (hsU : s.opinions = U) (htv : t.opinions = v) :
    Multiset.countP (fun a => informedP9 U a) ({s, t} : Multiset (AgentState L K)) + 1
      ≤ Multiset.countP (fun a => informedP9 U a)
          ({(Transition L K s t).1, (Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  obtain ⟨hs'9, ht'9, _, _, hs'opU, ht'opU⟩ :=
    Transition_consensus_pair9 U v hUsign hvsign hvU hUv hvv hUU s t hs9 ht9
      (Or.inl hsU) (Or.inr htv)
  set s' := (Transition L K s t).1
  set t' := (Transition L K s t).2
  rw [countP_informedP9_pair, countP_informedP9_pair]
  have huU : opinionsUnion s.opinions t.opinions = U := by
    rw [hsU, htv, hUv]
  have hs'op : s'.opinions = U := by rw [hs'opU, huU]
  have ht'op : t'.opinions = U := by rw [ht'opU, huU]
  have hs'inf : informedP9 U s' := ⟨hs'9, hs'op⟩
  have ht'inf : informedP9 U t' := ⟨ht'9, ht'op⟩
  have hsinf : informedP9 U s := ⟨hs9, hsU⟩
  have htninf : ¬ informedP9 U t := by
    rintro ⟨_, h⟩
    rw [htv] at h
    exact hUv_ne h.symm
  rw [if_pos hs'inf, if_pos ht'inf, if_pos hsinf, if_neg htninf]

/-- Sum of counts over the phase-9 informed state set. -/
theorem sum_count_informed9 (U : Fin 8) (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => informedP9 U a), c.count a)
      = informedU9 U c := by
  classical
  have hcard : (Multiset.filter (fun a : AgentState L K => informedP9 U a) c).card
      = informedU9 U c := by
    unfold informedU9
    rw [Multiset.countP_eq_card_filter]
  rw [← hcard]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => informedP9 U a),
      c.count a = Multiset.count a (Multiset.filter (fun a : AgentState L K => informedP9 U a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-- Sum of counts over the phase-9 susceptible state set. -/
theorem sum_count_susceptible9 (v : Fin 8) (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => susceptibleP9 v a), c.count a)
      = Multiset.countP (fun a => susceptibleP9 v a) c := by
  classical
  have hcard : (Multiset.filter (fun a : AgentState L K => susceptibleP9 v a) c).card
      = Multiset.countP (fun a => susceptibleP9 v a) c := by
    rw [Multiset.countP_eq_card_filter]
  rw [← hcard]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => susceptibleP9 v a),
      c.count a = Multiset.count a (Multiset.filter (fun a : AgentState L K => susceptibleP9 v a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-- In a phase-9 `Q9` window, susceptible count is `n - informedU9`. -/
theorem susceptible_count_eq9 (U v : Fin 8) (n : ℕ) (hUv : U ≠ v)
    (c : Config (AgentState L K)) (hw : Q9 U v n c) :
    Multiset.countP (fun a => susceptibleP9 v a) c = n - informedU9 U c := by
  classical
  unfold informedU9
  have hsplit : Multiset.countP (fun a => informedP9 U a) c
      + Multiset.countP (fun a => susceptibleP9 v a) c = c.card := by
    rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter, ← Multiset.card_add]
    congr 1
    refine Multiset.ext.mpr ?_
    intro a
    rw [Multiset.count_add, Multiset.count_filter, Multiset.count_filter]
    by_cases hmem : a ∈ c
    · obtain ⟨hp, hop⟩ := hw.2 a hmem
      by_cases hinf : informedP9 U a
      · have hnsus : ¬ susceptibleP9 v a := by
          rintro ⟨_, hv⟩
          rw [hinf.2] at hv
          exact hUv hv
        rw [if_pos hinf, if_neg hnsus]
        omega
      · have hsus : susceptibleP9 v a := by
          refine ⟨hp, ?_⟩
          rcases hop with hU | hv
          · exact absurd ⟨hp, hU⟩ hinf
          · exact hv
        rw [if_neg hinf, if_pos hsus]
        omega
    · have h0 : Multiset.count a c = 0 := Multiset.count_eq_zero.mpr hmem
      rw [h0]
      simp
  rw [hw.1] at hsplit
  omega

private theorem applicable_of_mem_distinct9 {c : Config (AgentState L K)}
    {x y : AgentState L K} (hx : x ∈ c) (hy : y ∈ c) (hxy : x ≠ y) :
    Protocol.Applicable c x y := by
  classical
  refine Multiset.le_iff_count.mpr ?_
  intro a
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl,
      Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
  have hxc : 1 ≤ Multiset.count x c := Multiset.one_le_count_iff_mem.mpr hx
  have hyc : 1 ≤ Multiset.count y c := Multiset.one_le_count_iff_mem.mpr hy
  by_cases hax : a = x
  · subst hax
    have hay : ¬ a = y := fun h => hxy (h ▸ rfl)
    rw [if_pos rfl, if_neg hay]
    omega
  · by_cases hay : a = y
    · subst hay
      rw [if_neg hax, if_pos rfl]
      omega
    · rw [if_neg hax, if_neg hay]
      omega

/-- A scheduled phase-9 informed/susceptible pair advances the global informed count. -/
theorem informedU9_stepOrSelf_advance (U v : Fin 8)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v)
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hs9 : s.phase.val = 9) (ht9 : t.phase.val = 9)
    (hsU : s.opinions = U) (htv : t.opinions = v) :
    informedU9 U c + 1 ≤ informedU9 U (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  unfold informedU9
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hpair_le :
      Multiset.countP (fun a => informedP9 U a) ({s, t} : Multiset (AgentState L K))
        ≤ Multiset.countP (fun a => informedP9 U a) c :=
    Multiset.countP_le_of_le _ hsub
  have hadv := informedP9_pair_advances U v hUsign hvsign hvU hUv hvv hUU hUv_ne s t hs9 ht9 hsU htv
  omega

/-- Generic rectangle-to-advance-probability bound for `informedU9`. -/
theorem informed9_advance_prob_of_rect (U : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hcardn : c.card = n)
    (R : Finset (AgentState L K × AgentState L K)) (N : ℕ)
    (hadv : ∀ p ∈ R, 1 ≤ c.count p.1 → 1 ≤ c.count p.2 → (p.1 = p.2 → 2 ≤ c.count p.1) →
      informedU9 U c + 1 ≤ informedU9 U (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2))
    (hcount : (N : ℕ) ≤ ∑ p ∈ R, c.interactionCount p.1 p.2) :
    ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | informedU9 U c + 1 ≤ informedU9 U c'} := by
  classical
  set j := informedU9 U c with hjdef
  have hcard2 : 2 ≤ c.card := by rw [hcardn]; omega
  have hmeas : MeasurableSet {c' : Config (AgentState L K) | j + 1 ≤ informedU9 U c'} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  set S : Finset (AgentState L K × AgentState L K) :=
    R.filter (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2 ∧ (p.1 = p.2 → 2 ≤ c.count p.1)) with hS
  have hsub : (↑S : Set (AgentState L K × AgentState L K)) ⊆
      (Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
        {c' | j + 1 ≤ informedU9 U c'} := by
    intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hS] at hp
    obtain ⟨hpc, hp1, hp2, hp3⟩ := hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Protocol.scheduledStep]
    exact hadv p hpc hp1 hp2 hp3
  have hstepDist : (NonuniformMajority L K).stepDistOrSelf c
      = (NonuniformMajority L K).stepDist c hcard2 := by
    unfold Protocol.stepDistOrSelf
    rw [dif_pos hcard2]
  have hbase : ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | j + 1 ≤ informedU9 U c'}
      = (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ informedU9 U c'}) := by
    rw [hstepDist]
    unfold Protocol.stepDist
    rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hmeas]
  rw [hbase]
  have hmono : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      ≤ (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ informedU9 U c'}) :=
    measure_mono hsub
  refine le_trans ?_ hmono
  have hSmeasure : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      = ∑ p ∈ S, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]
    rfl
  have hSsum : ∑ p ∈ S, c.interactionProb p.1 p.2
      = ∑ p ∈ R, c.interactionProb p.1 p.2 := by
    rw [hS]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hpc hpnot
    rw [Finset.mem_filter] at hpnot
    push Not at hpnot
    have hexcl := hpnot hpc
    have hzero : c.interactionCount p.1 p.2 = 0 := by
      unfold Config.interactionCount
      by_cases h1 : 1 ≤ c.count p.1
      · by_cases h2 : 1 ≤ c.count p.2
        · obtain ⟨hpe, hlt⟩ := hexcl h1 h2
          rw [if_pos hpe]
          have hc1 : c.count p.1 = 1 := by omega
          rw [hc1]
        · have hz2 : c.count p.2 = 0 := by omega
          by_cases hpe : p.1 = p.2
          · rw [if_pos hpe]
            rw [hpe, hz2, Nat.zero_mul]
          · rw [if_neg hpe, hz2, Nat.mul_zero]
      · have hz1 : c.count p.1 = 0 := by omega
        by_cases hpe : p.1 = p.2
        · rw [if_pos hpe, hz1, Nat.zero_mul]
        · rw [if_neg hpe, hz1, Nat.zero_mul]
    unfold Config.interactionProb
    rw [hzero]
    simp
  rw [hSmeasure, hSsum]
  have heqterm : ∀ p : AgentState L K × AgentState L K,
      c.interactionProb p.1 p.2
        = (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro p
    unfold Config.interactionProb
    rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun p _ => heqterm p), ← Finset.sum_mul, ← Nat.cast_sum]
  set M := ∑ p ∈ R, c.interactionCount p.1 p.2 with hM
  have htp : c.totalPairs = n * (n - 1) := by
    rw [Config.totalPairs, hcardn]
  rw [htp, ← div_eq_mul_inv]
  have hden_pos : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hdenR : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hstep1 : ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ ENNReal.ofReal (((M : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    rw [hdenR]
    have hNM : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcount
    have hposden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
      rw [← hdenR]
      exact hden_pos
    gcongr
  refine le_trans hstep1 ?_
  rw [← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_natCast (n * (n - 1)),
      ← ENNReal.ofReal_div_of_pos hden_pos]

/-- Interaction-count mass of a cross rectangle. -/
theorem sum_interactionCount_cross_disjoint9
    (c : Config (AgentState L K)) (A B : Finset (AgentState L K))
    (hdisj : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) :
    (∑ p ∈ A ×ˢ B, c.interactionCount p.1 p.2)
      = (∑ a ∈ A, c.count a) * (∑ b ∈ B, c.count b) := by
  classical
  rw [Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  unfold Config.interactionCount
  rw [if_neg (hdisj a ha b hb)]

/-- The phase-9 informed×susceptible rectangle has mass `m * (n - m)`. -/
theorem sum_interactionCount_syncRect9 (U v : Fin 8) (n : ℕ) (hUv : U ≠ v)
    (c : Config (AgentState L K)) (hw : Q9 U v n c) :
    (∑ p ∈ (Finset.univ.filter (fun a : AgentState L K => informedP9 U a)) ×ˢ
        (Finset.univ.filter (fun a : AgentState L K => susceptibleP9 v a)),
        c.interactionCount p.1 p.2)
      = informedU9 U c * (n - informedU9 U c) := by
  classical
  rw [sum_interactionCount_cross_disjoint9 c _ _ ?_, sum_count_informed9,
      sum_count_susceptible9, susceptible_count_eq9 U v n hUv c hw]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  intro hab
  have : a.opinions = U := ha.2.2
  have hbv : b.opinions = v := hb.2.2
  rw [hab, hbv] at this
  exact hUv this.symm

/-- The derived phase-9 informed-advance probability. -/
theorem opinion_advance_prob9 (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v)
    (c : Config (AgentState L K)) (hw : Q9 U v n c) :
    ENNReal.ofReal
        (((informedU9 U c * (n - informedU9 U c) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | informedU9 U c + 1 ≤ informedU9 U c'} := by
  classical
  set R := (Finset.univ.filter (fun a : AgentState L K => informedP9 U a)) ×ˢ
    (Finset.univ.filter (fun a : AgentState L K => susceptibleP9 v a)) with hR
  set m := informedU9 U c with hmdef
  have hcount : m * (n - m) ≤ ∑ p ∈ R, c.interactionCount p.1 p.2 := by
    rw [hR, sum_interactionCount_syncRect9 U v n hUv_ne c hw]
  refine informed9_advance_prob_of_rect U n hn c hw.1 R (m * (n - m)) ?_ hcount
  rintro ⟨a, b⟩ hp h1 h2 _hsame
  rw [hR, Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
  obtain ⟨⟨_, hainf⟩, ⟨_, hbsus⟩⟩ := hp
  have ha9 : a.phase.val = 9 := hainf.1
  have haU : a.opinions = U := hainf.2
  have hb9 : b.phase.val = 9 := hbsus.1
  have hbv : b.opinions = v := hbsus.2
  have hamem : a ∈ c := Multiset.one_le_count_iff_mem.mp h1
  have hbmem : b ∈ c := Multiset.one_le_count_iff_mem.mp h2
  have hab : a ≠ b := by
    intro h
    rw [h, hbv] at haU
    exact hUv_ne haU.symm
  have happ : Protocol.Applicable c a b := applicable_of_mem_distinct9 hamem hbmem hab
  exact informedU9_stepOrSelf_advance U v hUsign hvsign hvU hUv hvv hUU hUv_ne c a b happ
    ha9 hb9 haU hbv

/-! ## Part E — potential and drift. -/

/-- The clamped phase-9 informed count. -/
def oClamp9 (U : Fin 8) (n : ℕ) (c : Config (AgentState L K)) : ℕ :=
  min (informedU9 U c) n

/-- Phase-9 opinion epidemic has finished when all `n` agents are `U`-informed. -/
def oFinished9 (U : Fin 8) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  n ≤ informedU9 U c

instance (U : Fin 8) (n : ℕ) (c : Config (AgentState L K)) : Decidable (oFinished9 U n c) := by
  unfold oFinished9
  infer_instance

/-- Phase-9 opinion-deficit potential. -/
noncomputable def oDeficitPot9 (U : Fin 8) (n : ℕ) (s : ℝ)
    (c : Config (AgentState L K)) : ℝ≥0∞ :=
  if oFinished9 U n c then 0
  else ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (oClamp9 U n c : ℝ))))

theorem oDeficitPot9_measurable (U : Fin 8) (n : ℕ) (s : ℝ) :
    Measurable (oDeficitPot9 U n s (L := L) (K := K)) :=
  Measurable.of_discrete

theorem oDeficitPot9_eq_of_lt (U : Fin 8) (n : ℕ) (s : ℝ)
    (c : Config (AgentState L K)) (hlt : informedU9 U c < n) :
    oDeficitPot9 U n s c =
      ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (informedU9 U c : ℝ)))) := by
  unfold oDeficitPot9 oFinished9 oClamp9
  rw [if_neg (by omega)]
  congr 2
  rw [min_eq_left (le_of_lt hlt)]

theorem not_finished_imp_oDeficitPot9_ge_one (U : Fin 8) (n : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hc : ¬ oFinished9 U n c) :
    (1 : ℝ≥0∞) ≤ oDeficitPot9 U n s c := by
  have hlt : informedU9 U c < n := by
    unfold oFinished9 at hc
    omega
  rw [oDeficitPot9_eq_of_lt U n s c hlt]
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
  apply ENNReal.ofReal_le_ofReal
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  apply Real.exp_le_exp.mpr
  have hdef : (1 : ℝ) ≤ (n : ℝ) - (informedU9 U c : ℝ) := by
    have : (informedU9 U c : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlt
    linarith
  nlinarith [hs, hdef]

theorem oFinished9_absorbing (U v : Fin 8) (n : ℕ)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (c c' : Config (AgentState L K)) (hw : Q9 U v n c)
    (hfin : oFinished9 U n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    oFinished9 U n c' := by
  unfold oFinished9 at hfin ⊢
  exact informedU9_ge_monotone U v n n hUsign hvsign hvU hUv hvv hUU c c' hw hfin hc'

theorem oDeficitPot9_pointwise_bound (U : Fin 8) (n : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (m : ℕ)
    (_hm : informedU9 U c = m) (_hm_hi : m < n)
    (c' : Config (AgentState L K)) (hmono : m ≤ informedU9 U c') :
    oDeficitPot9 U n s c' ≤
      (if m + 1 ≤ informedU9 U c' then
        ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (m : ℝ) - 1)))
      else
        ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (m : ℝ))))) := by
  unfold oDeficitPot9 oFinished9 oClamp9
  by_cases hfin : n ≤ informedU9 U c'
  · rw [if_pos hfin]
    split_ifs <;> exact bot_le
  · rw [if_neg hfin]
    rw [not_le] at hfin
    by_cases hadv : m + 1 ≤ informedU9 U c'
    · rw [if_pos hadv]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      rw [min_eq_left (le_of_lt hfin)]
      have : (m : ℝ) + 1 ≤ (informedU9 U c' : ℝ) := by exact_mod_cast hadv
      nlinarith [hs, this]
    · rw [if_neg hadv]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      rw [min_eq_left (le_of_lt hfin)]
      have hle : (m : ℝ) ≤ (informedU9 U c' : ℝ) := by exact_mod_cast hmono
      nlinarith [hs, hle]

theorem oDeficitPot9_le_pre (U : Fin 8) (n : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hlo : 1 ≤ informedU9 U c) :
    oDeficitPot9 U n s c ≤ ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) := by
  unfold oDeficitPot9 oClamp9
  by_cases hfin : oFinished9 U n c
  · rw [if_pos hfin]
    exact bot_le
  · rw [if_neg hfin]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hmin : (min (informedU9 U c) n : ℕ) = informedU9 U c := by
      unfold oFinished9 at hfin
      omega
    rw [hmin]
    have h1 : (1 : ℝ) ≤ (informedU9 U c : ℝ) := by exact_mod_cast hlo
    nlinarith [hs, h1]

/-- Full phase-9 drift window: `Q9` plus at least one `U`-informed agent. -/
def Qwin9 (U v : Fin 8) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Q9 U v n c ∧ 1 ≤ informedU9 U c

instance (U v : Fin 8) (n : ℕ) (c : Config (AgentState L K)) : Decidable (Qwin9 U v n c) := by
  unfold Qwin9
  infer_instance

/-- `Q9` is preserved by a chosen-pair update. -/
theorem Q9_stepOrSelf (U v : Fin 8) (n : ℕ)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (c : Config (AgentState L K)) (hw : Q9 U v n c) (r₁ r₂ : AgentState L K) :
    Q9 U v n (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmem1 := mem_of_applicable_left9 happ
    have hmem2 := mem_of_applicable_right9 happ
    obtain ⟨h1p, h1op⟩ := hw.2 r₁ hmem1
    obtain ⟨h2p, h2op⟩ := hw.2 r₂ hmem2
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    obtain ⟨hp1', hp2', hop1', hop2', _, _⟩ :=
      Transition_consensus_pair9 U v hUsign hvsign hvU hUv hvv hUU r₁ r₂ h1p h2p h1op h2op
    refine ⟨?_, ?_⟩
    · have hcard := Protocol.reachable_card_eq
        (Protocol.reachable_stepOrSelf (P := NonuniformMajority L K) c r₁ r₂)
      rw [hcard]
      exact hw.1
    · intro a ha
      rw [hc'] at ha
      rcases Multiset.mem_add.mp ha with hold | hnew
      · exact hw.2 a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold)
      · rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
              : Multiset (AgentState L K))
            = (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0 from rfl] at hnew
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hnew
        rcases hnew with h | h
        · subst h
          exact ⟨hp1', hop1'⟩
        · subst h
          exact ⟨hp2', hop2'⟩
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact hw

/-- `Q9` is one-step-support closed. -/
theorem Q9_absorbing (U v : Fin 8) (n : ℕ)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (c c' : Config (AgentState L K)) (hw : Q9 U v n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Q9 U v n c' := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c =
        (NonuniformMajority L K).stepDist c hc by
          unfold Protocol.stepDistOrSelf
          rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact Q9_stepOrSelf U v n hUsign hvsign hvU hUv hvv hUU c hw r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf
        rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst c'
    exact hw

/-- `Qwin9` is one-step-support closed. -/
theorem Qwin9_absorbing (U v : Fin 8) (n : ℕ)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (c c' : Config (AgentState L K)) (hw : Qwin9 U v n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Qwin9 U v n c' :=
  ⟨Q9_absorbing U v n hUsign hvsign hvU hUv hvv hUU c c' hw.1 hc',
   informedU9_ge_monotone U v n 1 hUsign hvsign hvU hUv hvv hUU c c' hw.1 hw.2 hc'⟩

/-- Phase-9 guarded deficit potential. -/
noncomputable def oPotW9 (U v : Fin 8) (n : ℕ) (s : ℝ)
    (c : Config (AgentState L K)) : ℝ≥0∞ :=
  if Qwin9 U v n c then oDeficitPot9 U n s c else ⊤

theorem oPotW9_measurable (U v : Fin 8) (n : ℕ) (s : ℝ) :
    Measurable (oPotW9 U v n s (L := L) (K := K)) :=
  Measurable.of_discrete

theorem oPotW9_eq_on_window (U v : Fin 8) (n : ℕ) (s : ℝ)
    (c : Config (AgentState L K)) (hw : Qwin9 U v n c) :
    oPotW9 U v n s c = oDeficitPot9 U n s c := by
  unfold oPotW9
  rw [if_pos hw]

/-- Phase-9 opinion drift, identical to the Phase-2 drift after replacing the
phase-indexed informed count. -/
theorem phase9OpinionDrift (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hQ : Q9 U v n c)
    (hlo : 1 ≤ informedU9 U c) (hnc : informedU9 U c < n) :
    ∫⁻ c', oDeficitPot9 U n s c' ∂((NonuniformMajority L K).transitionKernel c) ≤
      ENNReal.ofReal
        (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s)))
        * oDeficitPot9 U n s c := by
  classical
  set m := informedU9 U c with hm
  have hΦc : oDeficitPot9 U n s c
      = ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (m : ℝ)))) :=
    oDeficitPot9_eq_of_lt U n s c hnc
  set A := {c' : Config (AgentState L K) | m + 1 ≤ informedU9 U c'} with hA_def
  have hA_meas : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  set pR : ℝ := (((n - 1 : ℕ)) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) with hpR
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hfloorN : n - 1 ≤ m * (n - m) := advance_floor n m hlo hnc
  have hmRle : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hnc
  have hnmR : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hnc)]
  have hrec_le : ((m * (n - m) : ℕ) : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, hnmR]
    nlinarith [sq_nonneg ((n : ℝ) - 2 * (m : ℝ)), hmRle, hnR,
      mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ))
        (by linarith : (0 : ℝ) ≤ (n : ℝ) - (m : ℝ))]
  have hfloorR : (((n - 1 : ℕ)) : ℝ) ≤ ((m * (n - m) : ℕ) : ℝ) := by exact_mod_cast hfloorN
  have hnum_le : (((n - 1 : ℕ)) : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := le_trans hfloorR hrec_le
  have hpR_nonneg : 0 ≤ pR := by
    rw [hpR]
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hden_pos)
  have hpR_le_one : pR ≤ 1 := by
    rw [hpR, div_le_one hden_pos]
    exact hnum_le
  set E0 : ℝ := Real.exp (s * ((n : ℝ) - (m : ℝ))) with hE0
  set E1 : ℝ := Real.exp (s * ((n : ℝ) - (m : ℝ) - 1)) with hE1
  have hE0_pos : 0 < E0 := Real.exp_pos _
  have hE1_pos : 0 < E1 := Real.exp_pos _
  have hE1_eq : E1 = E0 * Real.exp (-s) := by
    rw [hE0, hE1, ← Real.exp_add]
    congr 1
    ring
  have hstep : ENNReal.ofReal pR ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A := by
    have hadv := opinion_advance_prob9 U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne c hQ
    rw [← hm] at hadv
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hadv
    rw [hpR]
    apply (div_le_div_iff_of_pos_right hden_pos).mpr
    exact hfloorR
  change ∫⁻ c', oDeficitPot9 U n s c'
    ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure ≤ _
  calc
    ∫⁻ c', oDeficitPot9 U n s c'
        ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        ≤ ∫⁻ c', (if m + 1 ≤ informedU9 U c' then ENNReal.ofReal E1
            else ENNReal.ofReal E0) ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure := by
          apply lintegral_mono_ae
          rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
            (DiscreteMeasurableSpace.forall_measurableSet _)]
          rw [Set.disjoint_left]
          intro x hsupp hbad
          apply hbad
          have hmono_x : m ≤ informedU9 U x :=
            informedU9_ge_monotone U v n m hUsign hvsign hvU hUv hvv hUU
              c x hQ (le_of_eq hm.symm) hsupp
          exact oDeficitPot9_pointwise_bound U n s hs c m hm.symm hnc x hmono_x
      _ = (∫⁻ c' in A, ENNReal.ofReal E1 ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure) +
          (∫⁻ c' in Aᶜ, ENNReal.ofReal E0 ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure) := by
          rw [← lintegral_add_compl _ hA_meas]
          congr 1
          · apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem hA_meas] with c' hc'
            simp only [Set.mem_setOf_eq, hA_def] at hc'
            simp [hc']
          · apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem hA_meas.compl] with c' hc'
            simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hA_def] at hc'
            simp [hc']
      _ = ENNReal.ofReal E1 * ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A +
          ENNReal.ofReal E0 * ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Aᶜ := by
          rw [lintegral_const, Measure.restrict_apply_univ,
              lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ENNReal.ofReal (1 - pR * (1 - Real.exp (-s))) * oDeficitPot9 U n s c := by
          rw [hΦc]
          set q := ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A with hq_def
          set qc := ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Aᶜ with hqc_def
          haveI : IsProbabilityMeasure ((NonuniformMajority L K).stepDistOrSelf c).toMeasure :=
            PMF.toMeasure.isProbabilityMeasure _
          have hq_ge : ENNReal.ofReal pR ≤ q := hstep
          have hq_le_one : q ≤ 1 := by
            calc q ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Set.univ :=
                  measure_mono (Set.subset_univ _)
              _ = 1 := measure_univ
          have hq_ne_top : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq_le_one
          have hqc_eq : qc = 1 - q := by
            have h_compl := measure_compl hA_meas hq_ne_top
            rw [show ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Set.univ = 1
              from measure_univ] at h_compl
            exact h_compl
          set qr := q.toReal with hqr_def
          have hqr_nonneg : 0 ≤ qr := ENNReal.toReal_nonneg
          have hqr_le_one : qr ≤ 1 := by
            have := ENNReal.toReal_mono ENNReal.one_ne_top hq_le_one
            rwa [ENNReal.toReal_one] at this
          have hq_ofReal : q = ENNReal.ofReal qr := (ENNReal.ofReal_toReal hq_ne_top).symm
          have hp_le_qr : pR ≤ qr := by
            have h1 : ENNReal.ofReal pR ≤ ENNReal.ofReal qr := by
              rw [← hq_ofReal]
              exact hq_ge
            exact (ENNReal.ofReal_le_ofReal_iff hqr_nonneg).mp h1
          have h1mqr_nonneg : 0 ≤ 1 - qr := by linarith
          have hqc_ofReal : qc = ENNReal.ofReal (1 - qr) := by
            rw [hqc_eq, hq_ofReal,
                show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
                ← ENNReal.ofReal_sub 1 hqr_nonneg]
          have lhs_eq : ENNReal.ofReal E1 * q + ENNReal.ofReal E0 * qc =
              ENNReal.ofReal (E1 * qr + E0 * (1 - qr)) := by
            rw [hq_ofReal, hqc_ofReal,
                ← ENNReal.ofReal_mul hE1_pos.le, ← ENNReal.ofReal_mul hE0_pos.le,
                ← ENNReal.ofReal_add (mul_nonneg hE1_pos.le hqr_nonneg)
                  (mul_nonneg hE0_pos.le h1mqr_nonneg)]
          have hexp_le_one : Real.exp (-s) ≤ 1 := by
            rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
            exact Real.exp_le_exp.mpr (by linarith)
          have rhs_eq :
              ENNReal.ofReal (1 - pR * (1 - Real.exp (-s))) * ENNReal.ofReal E0 =
                ENNReal.ofReal ((1 - pR * (1 - Real.exp (-s))) * E0) := by
            rw [← ENNReal.ofReal_mul]
            have : (1 : ℝ) - pR * (1 - Real.exp (-s)) ≥ 0 := by
              have h0 : (0 : ℝ) ≤ 1 - Real.exp (-s) := by linarith
              nlinarith [hpR_nonneg, hpR_le_one, h0]
            linarith
          rw [lhs_eq, rhs_eq]
          apply ENNReal.ofReal_le_ofReal
          have hfactor : E1 * qr + E0 * (1 - qr) =
              E0 * (1 - qr * (1 - Real.exp (-s))) := by
            rw [hE1_eq]
            ring
          rw [hfactor]
          have hrhs : (1 - pR * (1 - Real.exp (-s))) * E0 =
              E0 * (1 - pR * (1 - Real.exp (-s))) := by ring
          rw [hrhs]
          apply mul_le_mul_of_nonneg_left _ hE0_pos.le
          have h1me : (0 : ℝ) ≤ 1 - Real.exp (-s) := by linarith
          nlinarith [mul_le_mul_of_nonneg_right hp_le_qr h1me]

/-! ## Part F — final PhaseConvergence and W wrapper. -/

/-- Phase-9 opinion-union epidemic convergence on the real kernel. -/
noncomputable def phase9Convergence (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) (s : ℝ) (hs : 0 < s)
    (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal
            (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
            ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1
          ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence (NonuniformMajority L K).transitionKernel := by
  refine WindowConcentration.windowDrift_PhaseConvergence (NonuniformMajority L K)
    (oPotW9 U v n s) (oPotW9_measurable U v n s)
    (fun c => Qwin9 U v n c)
    (Qwin9_absorbing U v n hUsign hvsign hvU hUv hvv hUU)
    (ENNReal.ofReal
      (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))))
    ?_
    (fun c => Qwin9 U v n c)
    (fun c => Qwin9 U v n c ∧ oFinished9 U n c)
    ?_
    1 one_ne_zero ENNReal.one_ne_top
    ?_
    (fun c h => h)
    (ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))))
    ?_
    t ε hε
  · intro c hQw
    obtain ⟨hQ, hlo⟩ := hQw
    rw [oPotW9_eq_on_window U v n s c ⟨hQ, hlo⟩]
    have hint_eq : ∫⁻ c', oPotW9 U v n s c'
          ∂((NonuniformMajority L K).transitionKernel c)
        = ∫⁻ c', oDeficitPot9 U n s c'
          ∂((NonuniformMajority L K).transitionKernel c) := by
      apply lintegral_congr_ae
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure,
        oPotW9 U v n s c' = oDeficitPot9 U n s c'
      rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      rw [Set.disjoint_left]
      intro x hsupp hbad
      apply hbad
      exact oPotW9_eq_on_window U v n s x
        (Qwin9_absorbing U v n hUsign hvsign hvU hUv hvv hUU c x ⟨hQ, hlo⟩ hsupp)
    rw [hint_eq]
    by_cases hfin : oFinished9 U n c
    · have hΦc0 : oDeficitPot9 U n s c = 0 := by
        unfold oDeficitPot9
        rw [if_pos hfin]
      rw [hΦc0, mul_zero, nonpos_iff_eq_zero]
      change ∫⁻ c', oDeficitPot9 U n s c'
          ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure = 0
      rw [lintegral_eq_zero_iff (oDeficitPot9_measurable U n s)]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨((NonuniformMajority L K).stepDistOrSelf c).support, ?_, ?_⟩
      · rw [mem_ae_iff, PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]
        intro x hsupp hx
        exact hx (PMF.mem_support_iff _ _ |>.mp hsupp)
      · intro c' hc'
        have hfin' : oFinished9 U n c' :=
          oFinished9_absorbing U v n hUsign hvsign hvU hUv hvv hUU c c' hQ hfin hc'
        change oDeficitPot9 U n s c' = 0
        unfold oDeficitPot9
        rw [if_pos hfin']
    · have hnc : informedU9 U c < n := by
        unfold oFinished9 at hfin
        omega
      exact phase9OpinionDrift U v n hn hUsign hvsign hvU hUv hvv hUU
        hUv_ne s hs c hQ hlo hnc
  · rintro c c' ⟨hQw, hfin⟩ hc'
    exact ⟨Qwin9_absorbing U v n hUsign hvsign hvU hUv hvv hUU c c' hQw hc',
      oFinished9_absorbing U v n hUsign hvsign hvU hUv hvv hUU c c' hQw.1 hfin hc'⟩
  · intro c hnp
    unfold oPotW9
    by_cases hQw : Qwin9 U v n c
    · rw [if_pos hQw]
      have hnf : ¬ oFinished9 U n c := fun hfin => hnp ⟨hQw, hfin⟩
      exact not_finished_imp_oDeficitPot9_ge_one U n s hs c hnf
    · rw [if_neg hQw]
      exact le_top
  · intro c hPre
    rw [oPotW9_eq_on_window U v n s c hPre]
    exact oDeficitPot9_le_pre U n s hs c hPre.2

/-- Weak-wrapper for the Full work family. -/
noncomputable def phase9ConvergenceW (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) (s : ℝ) (hs : 0 < s)
    (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal
            (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
            ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1
          ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  PhaseConvergence.toW
    (phase9Convergence (L := L) (K := K)
      U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne s hs t ε hε)

#print axioms Transition_consensus_pair9
#print axioms informedU9_ge_monotone
#print axioms opinion_advance_prob9
#print axioms phase9OpinionDrift
#print axioms phase9Convergence
#print axioms phase9ConvergenceW

end Phase9Convergence

end ExactMajority
