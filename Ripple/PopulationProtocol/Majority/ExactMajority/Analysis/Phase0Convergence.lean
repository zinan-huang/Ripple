import Ripple.PopulationProtocol.Majority.ExactMajority.Protocol.Transition
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.JansonHitting
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.TransitionMonotonicity
import Mathlib.Probability.Kernel.Basic

namespace ExactMajority

variable {L K : ℕ}

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

def mcrCount (c : Config (AgentState L K)) : ℕ :=
  (c.filter (fun a => a.role = .mcr)).card

def mcrThreshold (n : ℕ) (i : Fin n) : ℕ :=
  n - 1 - i.val

def phase0Milestone (n : ℕ) (i : Fin n) (c : Config (AgentState L K)) : Prop :=
  mcrCount c ≤ mcrThreshold n i ∨ c.card ≠ n ∨
    (∃ a ∈ c, a.role = .mcr ∧ a.phase.val ≠ 0)

/-- MCR+MCR milestone probability for Phase 0.
When MCR count is M = n - i (and all MCR agents at phase 0),
any pair of two distinct MCR agents decreases the count. Total:
  M*(M-1)/(n*(n-1))
At M=n (init): = 1. At M=2: = 2/(n*(n-1)).
We use k = n - 1 milestones, stopping at mcrCount ≤ 1 (M ≥ 2 always).
meanTime = Σ n*(n-1)/(M*(M-1)) = O(n²). -/
noncomputable def phase0MilestoneProb (n : ℕ) : Fin (n - 1) → ℝ := fun i =>
  let M := n - 1 - i.val + 1
  (M * (M - 1) : ℝ) / (n * (n - 1) : ℝ)

lemma mcrCount_add (c₁ c₂ : Config (AgentState L K)) :
    mcrCount (c₁ + c₂) = mcrCount c₁ + mcrCount c₂ := by
  simp [mcrCount]

private lemma phaseInit_no_mcr (p : Fin 11) (a : AgentState L K) (ha : a.role ≠ .mcr) :
    (phaseInit L K p a).role ≠ .mcr := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  fin_cases p <;> cases role <;>
    simp [phaseInit, enterPhase10] at ha ⊢ <;>
    repeat' split_ifs <;> simp_all

private lemma foldl_phaseInit_no_mcr (ks : List ℕ) (a : AgentState L K) (ha : a.role ≠ .mcr) :
    (ks.foldl
      (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
      a).role ≠ .mcr := by
  induction ks generalizing a with
  | nil => simpa using ha
  | cons k ks ih =>
      simp only [List.foldl]
      apply ih
      by_cases hk : k < 11
      · simpa [hk] using phaseInit_no_mcr (L := L) (K := K) ⟨k, hk⟩ a ha
      · simpa [hk] using ha

private lemma runInitsBetween_no_mcr
    (oldP newP : ℕ) (a : AgentState L K) (ha : a.role ≠ .mcr) :
    (runInitsBetween L K oldP newP a).role ≠ .mcr := by
  unfold runInitsBetween
  exact foldl_phaseInit_no_mcr
    (L := L) (K := K) ((List.range 11).filter fun k => oldP < k ∧ k ≤ newP) a ha

private lemma phase10EpidemicEntry_no_mcr
    (before after : AgentState L K) (ha : after.role ≠ .mcr) :
    (phase10EpidemicEntry L K before after).role ≠ .mcr := by
  unfold phase10EpidemicEntry
  split_ifs <;> simpa [enterPhase10] using ha

private lemma phaseEpidemicUpdate_first_no_mcr (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (phaseEpidemicUpdate L K s t).1.role ≠ .mcr := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase
  set s' := runInitsBetween L K s.phase.val p.val ({ s with phase := p } : AgentState L K)
  set t' := runInitsBetween L K t.phase.val p.val ({ t with phase := p } : AgentState L K)
  have hs' : s'.role ≠ .mcr := by
    exact runInitsBetween_no_mcr (L := L) (K := K) s.phase.val p.val
      ({ s with phase := p } : AgentState L K) (by simpa)
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s'.phase.val = 10 ∨ t'.phase.val = 10) then
      (phase10EpidemicEntry L K s s', phase10EpidemicEntry L K t t')
    else (s', t')).1.role ≠ .mcr
  by_cases h10 : (s.phase.val < 10 ∨ t.phase.val < 10) ∧
      (s'.phase.val = 10 ∨ t'.phase.val = 10)
  · simpa [h10] using phase10EpidemicEntry_no_mcr (L := L) (K := K) s s' hs'
  · simpa [h10] using hs'

private lemma phaseEpidemicUpdate_second_no_mcr (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (phaseEpidemicUpdate L K s t).2.role ≠ .mcr := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase
  set s' := runInitsBetween L K s.phase.val p.val ({ s with phase := p } : AgentState L K)
  set t' := runInitsBetween L K t.phase.val p.val ({ t with phase := p } : AgentState L K)
  have ht' : t'.role ≠ .mcr := by
    exact runInitsBetween_no_mcr (L := L) (K := K) t.phase.val p.val
      ({ t with phase := p } : AgentState L K) (by simpa)
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s'.phase.val = 10 ∨ t'.phase.val = 10) then
      (phase10EpidemicEntry L K s s', phase10EpidemicEntry L K t t')
    else (s', t')).2.role ≠ .mcr
  by_cases h10 : (s.phase.val < 10 ∨ t.phase.val < 10) ∧
      (s'.phase.val = 10 ∨ t'.phase.val = 10)
  · simpa [h10] using phase10EpidemicEntry_no_mcr (L := L) (K := K) t t' ht'
  · simpa [h10] using ht'

private lemma advancePhase_no_mcr (a : AgentState L K) (ha : a.role ≠ .mcr) :
    (advancePhase L K a).role ≠ .mcr := by
  unfold advancePhase
  split_ifs <;> simpa using ha

private lemma advancePhaseWithInit_no_mcr (a : AgentState L K) (ha : a.role ≠ .mcr) :
    (advancePhaseWithInit L K a).role ≠ .mcr := by
  unfold advancePhaseWithInit
  exact phaseInit_no_mcr (L := L) (K := K) (advancePhase L K a).phase
    (advancePhase L K a) (advancePhase_no_mcr (L := L) (K := K) a ha)

private lemma stdCounterSubroutine_no_mcr (a : AgentState L K) (ha : a.role ≠ .mcr) :
    (stdCounterSubroutine L K a).role ≠ .mcr := by
  unfold stdCounterSubroutine
  split_ifs
  · exact advancePhaseWithInit_no_mcr (L := L) (K := K) a ha
  · simpa using ha

private lemma clockCounterStep_no_mcr (a : AgentState L K) (ha : a.role ≠ .mcr) :
    (clockCounterStep L K a).role ≠ .mcr := by
  unfold clockCounterStep
  split_ifs
  · exact stdCounterSubroutine_no_mcr (L := L) (K := K) a ha
  · simpa using ha

private lemma clockCounterFinish_no_mcr (a : AgentState L K) (ha : a.role ≠ .mcr) :
    (if a.role = .clock then stdCounterSubroutine L K a else a).role ≠ .mcr := by
  split_ifs
  · exact stdCounterSubroutine_no_mcr (L := L) (K := K) a ha
  · simpa using ha

private lemma phase3CancelSplit_first_no_mcr
    (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (phase3CancelSplit L K s t).1.role ≠ .mcr := by
  unfold phase3CancelSplit
  match s.bias, t.bias with
  | .zero, .zero => simpa using hs
  | .zero, .dyadic _ _ => simp; split_ifs <;> simpa using hs
  | .dyadic _ _, .zero => simp; split_ifs <;> simpa using hs
  | .dyadic .pos _, .dyadic .pos _ => simpa using hs
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simpa using hs
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simpa using hs
  | .dyadic .neg _, .dyadic .neg _ => simpa using hs

private lemma phase3CancelSplit_second_no_mcr
    (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (phase3CancelSplit L K s t).2.role ≠ .mcr := by
  unfold phase3CancelSplit
  match s.bias, t.bias with
  | .zero, .zero => simpa using ht
  | .zero, .dyadic _ _ => simp; split_ifs <;> simpa using ht
  | .dyadic _ _, .zero => simp; split_ifs <;> simpa using ht
  | .dyadic .pos _, .dyadic .pos _ => simpa using ht
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simpa using ht
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simpa using ht
  | .dyadic .neg _, .dyadic .neg _ => simpa using ht

private lemma doSplit_first_no_mcr (r m : AgentState L K) (hr : r.role ≠ .mcr) :
    (doSplit L K r m).1.role ≠ .mcr := by
  unfold doSplit
  match m.bias with
  | .zero => simpa using hr
  | .dyadic _ _ => simp; split_ifs <;> simp_all

private lemma doSplit_second_no_mcr (r m : AgentState L K) (hm : m.role ≠ .mcr) :
    (doSplit L K r m).2.role ≠ .mcr := by
  unfold doSplit
  match m.bias with
  | .zero => simpa using hm
  | .dyadic _ _ => simp; split_ifs <;> simpa using hm

private lemma cancelSplit_first_no_mcr (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (cancelSplit L K s t).1.role ≠ .mcr := by
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, _ => simpa using hs
  | .dyadic _ _, .zero => simpa using hs
  | .dyadic _ _, .dyadic _ _ => simp; split_ifs <;> simpa using hs

private lemma cancelSplit_second_no_mcr (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (cancelSplit L K s t).2.role ≠ .mcr := by
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, _ => simpa using ht
  | .dyadic _ _, .zero => simpa using ht
  | .dyadic _ _, .dyadic _ _ => simp; split_ifs <;> simpa using ht

private lemma absorbConsume_first_no_mcr (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (absorbConsume L K s t).1.role ≠ .mcr := by
  unfold absorbConsume
  match s.bias, t.bias with
  | .zero, _ => simpa using hs
  | .dyadic .pos _, .zero => simpa using hs
  | .dyadic .neg _, .zero => simpa using hs
  | .dyadic .pos _, .dyadic .pos _ => simpa using hs
  | .dyadic .neg _, .dyadic .neg _ => simpa using hs
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simpa using hs
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simpa using hs

private lemma absorbConsume_second_no_mcr (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (absorbConsume L K s t).2.role ≠ .mcr := by
  unfold absorbConsume
  match s.bias, t.bias with
  | .zero, _ => simpa using ht
  | .dyadic .pos _, .zero => simpa using ht
  | .dyadic .neg _, .zero => simpa using ht
  | .dyadic .pos _, .dyadic .pos _ => simpa using ht
  | .dyadic .neg _, .dyadic .neg _ => simpa using ht
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simpa using ht
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simpa using ht

-- Factor Phase0Transition into named rules to avoid term explosion during proof
private def p0r1s (s t : AgentState L K) : AgentState L K :=
  if s.role = .mcr ∧ t.role = .mcr then
    { s with role := .main, smallBias := addSmallBias s.smallBias t.smallBias }
  else s

private def p0r1t (s t : AgentState L K) : AgentState L K :=
  if s.role = .mcr ∧ t.role = .mcr then
    { t with role := .cr, smallBias := ⟨3, by decide⟩ }
  else t

private def p0r2s (s1 t1 : AgentState L K) : AgentState L K :=
  if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
  else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
  else s1

private def p0r3s (s2 t2 : AgentState L K) : AgentState L K :=
  if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { s2 with role := .main }
  else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { s2 with assigned := true }
  else s2

private def p0r3ps (s3 _t3 : AgentState L K) : AgentState L K := s3

private def p0r4s (s3' t3' : AgentState L K) : AgentState L K :=
  if s3'.role = .cr ∧ t3'.role = .cr then
    { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ }
  else s3'

private def p0r5s (s4 t4 : AgentState L K) : AgentState L K :=
  if s4.role = .clock ∧ t4.role = .clock then
    stdCounterSubroutine L K s4
  else s4

private lemma phase0_first_decompose (s t : AgentState L K) :
    (Phase0Transition L K s t).1 =
      let s1 := p0r1s s t; let t1 := p0r1t s t
      let s2 := p0r2s s1 t1
      let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
                  { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
                else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
                  { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
                else t1
      let s3 := p0r3s s2 t2
      let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
                  { t2 with assigned := true }
                else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
                  { t2 with role := .main }
                else t2
      let s3' := p0r3ps s3 t3
      let t3' := t3
      let s4 := p0r4s (L := L) s3' t3'
      let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
                  { t3' with role := .reserve }
                else t3'
      p0r5s (L := L) (K := K) s4 t4 := by
  unfold Phase0Transition p0r1s p0r1t p0r2s p0r3s p0r3ps p0r4s p0r5s; rfl

private lemma p0r1s_no_mcr (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (p0r1s s t).role ≠ .mcr := by unfold p0r1s; simp [hs]

private lemma p0r2s_no_mcr (s1 t1 : AgentState L K) (hs1 : s1.role ≠ .mcr) :
    (p0r2s s1 t1).role ≠ .mcr := by unfold p0r2s; split_ifs <;> simpa using hs1

private lemma p0r3s_no_mcr (s2 t2 : AgentState L K) (hs2 : s2.role ≠ .mcr) :
    (p0r3s s2 t2).role ≠ .mcr := by unfold p0r3s; split_ifs <;> simpa using hs2

private lemma p0r3ps_no_mcr (s3 t3 : AgentState L K) (hs3 : s3.role ≠ .mcr) :
    (p0r3ps s3 t3).role ≠ .mcr := by unfold p0r3ps; simp [hs3]

private lemma p0r4s_no_mcr (s3' t3' : AgentState L K) (hs3' : s3'.role ≠ .mcr) :
    (p0r4s (L := L) s3' t3').role ≠ .mcr := by
  unfold p0r4s; split_ifs
  · show Role.clock ≠ .mcr; decide
  · exact hs3'

private lemma p0r5s_no_mcr (s4 t4 : AgentState L K) (hs4 : s4.role ≠ .mcr) :
    (p0r5s (L := L) (K := K) s4 t4).role ≠ .mcr := by
  unfold p0r5s; split_ifs
  · exact stdCounterSubroutine_no_mcr (L := L) (K := K) s4 hs4
  · exact hs4

set_option maxHeartbeats 800000 in
lemma Phase0Transition_first_no_mcr (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (Phase0Transition L K s t).1.role ≠ .mcr := by
  rw [phase0_first_decompose]
  exact p0r5s_no_mcr _ _
    (p0r4s_no_mcr _ _
      (p0r3ps_no_mcr _ _
        (p0r3s_no_mcr _ _
          (p0r2s_no_mcr _ _
            (p0r1s_no_mcr s t hs)))))

-- t-side factored helpers
private def p0r2t (s1 t1 : AgentState L K) : AgentState L K :=
  if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
  else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
  else t1

private def p0r3t (s2 t2 : AgentState L K) : AgentState L K :=
  if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { t2 with assigned := true }
  else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { t2 with role := .main }
  else t2

private def p0r3pt (_s3 t3 : AgentState L K) : AgentState L K := t3

private def p0r4t (s3' t3' : AgentState L K) : AgentState L K :=
  if s3'.role = .cr ∧ t3'.role = .cr then
    { t3' with role := .reserve }
  else t3'

private def p0r5t (s4 t4 : AgentState L K) : AgentState L K :=
  if s4.role = .clock ∧ t4.role = .clock then
    stdCounterSubroutine L K t4
  else t4

private lemma phase0_second_decompose (s t : AgentState L K) :
    (Phase0Transition L K s t).2 =
      let s1 := p0r1s s t; let t1 := p0r1t s t
      let s2 := p0r2s s1 t1; let t2 := p0r2t s1 t1
      let s3 := p0r3s s2 t2; let t3 := p0r3t s2 t2
      let s3' := p0r3ps s3 t3; let t3' := p0r3pt s3 t3
      let s4 := p0r4s (L := L) s3' t3'; let t4 := p0r4t s3' t3'
      p0r5t (L := L) (K := K) s4 t4 := by
  unfold Phase0Transition p0r1s p0r1t p0r2s p0r2t p0r3s p0r3t
         p0r3ps p0r3pt p0r4s p0r4t p0r5t; rfl

private lemma p0r1t_no_mcr (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (p0r1t s t).role ≠ .mcr := by
  unfold p0r1t; split_ifs
  · show Role.cr ≠ .mcr; decide
  · exact ht

private lemma p0r2t_no_mcr (s1 t1 : AgentState L K) (ht1 : t1.role ≠ .mcr) :
    (p0r2t s1 t1).role ≠ .mcr := by
  unfold p0r2t; simp [ht1]; split_ifs <;> simpa using ht1

private lemma p0r3t_no_mcr (s2 t2 : AgentState L K) (ht2 : t2.role ≠ .mcr) :
    (p0r3t s2 t2).role ≠ .mcr := by unfold p0r3t; split_ifs <;> simpa using ht2

private lemma p0r3pt_no_mcr (s3 t3 : AgentState L K) (ht3 : t3.role ≠ .mcr) :
    (p0r3pt s3 t3).role ≠ .mcr := by
  unfold p0r3pt; simp [ht3]

private lemma p0r4t_no_mcr (s3' t3' : AgentState L K) (ht3' : t3'.role ≠ .mcr) :
    (p0r4t s3' t3').role ≠ .mcr := by
  unfold p0r4t; split_ifs
  · show Role.reserve ≠ .mcr; decide
  · exact ht3'

private lemma p0r5t_no_mcr (s4 t4 : AgentState L K) (ht4 : t4.role ≠ .mcr) :
    (p0r5t (L := L) (K := K) s4 t4).role ≠ .mcr := by
  unfold p0r5t; split_ifs
  · exact stdCounterSubroutine_no_mcr (L := L) (K := K) t4 ht4
  · exact ht4

set_option maxHeartbeats 800000 in
lemma Phase0Transition_second_no_mcr (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (Phase0Transition L K s t).2.role ≠ .mcr := by
  rw [phase0_second_decompose]
  exact p0r5t_no_mcr _ _
    (p0r4t_no_mcr _ _
      (p0r3pt_no_mcr _ _
        (p0r3t_no_mcr _ _
          (p0r2t_no_mcr _ _
            (p0r1t_no_mcr s t ht)))))

lemma Phase1Transition_first_no_mcr (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (Phase1Transition L K s t).1.role ≠ .mcr := by
  unfold Phase1Transition
  split_ifs
  · exact clockCounterStep_no_mcr (L := L) (K := K)
      ({ s with smallBias := (avgFin7 s.smallBias t.smallBias).1 } : AgentState L K)
      (by simpa using hs)
  · exact clockCounterStep_no_mcr (L := L) (K := K) s hs

lemma Phase1Transition_second_no_mcr (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (Phase1Transition L K s t).2.role ≠ .mcr := by
  unfold Phase1Transition
  split_ifs
  · exact clockCounterStep_no_mcr (L := L) (K := K)
      ({ t with smallBias := (avgFin7 s.smallBias t.smallBias).2 } : AgentState L K)
      (by simpa using ht)
  · exact clockCounterStep_no_mcr (L := L) (K := K) t ht

lemma Phase2Transition_first_no_mcr (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (Phase2Transition L K s t).1.role ≠ .mcr := by
  unfold Phase2Transition
  set univ := opinionsUnion s.opinions t.opinions
  set s' := ({ s with opinions := univ } : AgentState L K)
  set t' := ({ t with opinions := univ } : AgentState L K)
  have hs' : s'.role ≠ .mcr := by
    dsimp [s']
    simpa using hs
  change (if hasMinusOne univ && hasPlusOne univ then
      (advancePhaseWithInit L K s', advancePhaseWithInit L K t')
    else if hasPlusOne univ then
      ({ s' with output := .A }, { t' with output := .A })
    else if hasMinusOne univ then
      ({ s' with output := .B }, { t' with output := .B })
    else if univ.val = 2 then
      ({ s' with output := .T }, { t' with output := .T })
    else (s', t')).1.role ≠ .mcr
  split_ifs
  · exact advancePhaseWithInit_no_mcr (L := L) (K := K) s' hs'
  · simpa using hs'
  · simpa using hs'
  · simpa using hs'
  · simpa using hs'

lemma Phase2Transition_second_no_mcr (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (Phase2Transition L K s t).2.role ≠ .mcr := by
  unfold Phase2Transition
  set univ := opinionsUnion s.opinions t.opinions
  set s' := ({ s with opinions := univ } : AgentState L K)
  set t' := ({ t with opinions := univ } : AgentState L K)
  have ht' : t'.role ≠ .mcr := by
    dsimp [t']
    simpa using ht
  change (if hasMinusOne univ && hasPlusOne univ then
      (advancePhaseWithInit L K s', advancePhaseWithInit L K t')
    else if hasPlusOne univ then
      ({ s' with output := .A }, { t' with output := .A })
    else if hasMinusOne univ then
      ({ s' with output := .B }, { t' with output := .B })
    else if univ.val = 2 then
      ({ s' with output := .T }, { t' with output := .T })
    else (s', t')).2.role ≠ .mcr
  split_ifs
  · exact advancePhaseWithInit_no_mcr (L := L) (K := K) t' ht'
  · simpa using ht'
  · simpa using ht'
  · simpa using ht'
  · simpa using ht'

lemma Phase3Transition_first_no_mcr (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (Phase3Transition L K s t).1.role ≠ .mcr := by
  unfold Phase3Transition
  set s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then
      let pmax := max s.minute t.minute
      { s with minute := pmax }
    else if h_max : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else
      stdCounterSubroutine L K s
  else s
  set t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then
      let pmax := max s.minute t.minute
      { t with minute := pmax }
    else if h_max : s.minute.val < K * (L + 1) then
      t
    else
      stdCounterSubroutine L K t
  else t
  have hs1 : s1.role ≠ .mcr := by
    dsimp [s1]
    split_ifs <;>
      first | exact stdCounterSubroutine_no_mcr (L := L) (K := K) s hs
            | simpa using hs
  set s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    s1
  else s1
  set t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs2 : s2.role ≠ .mcr := by
    dsimp [s2]
    split_ifs <;> simpa using hs1
  change (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
    else (s2, t2)).1.role ≠ .mcr
  split_ifs
  · exact phase3CancelSplit_first_no_mcr (L := L) (K := K) s2 t2 hs2
  · simpa using hs2

lemma Phase3Transition_second_no_mcr (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (Phase3Transition L K s t).2.role ≠ .mcr := by
  unfold Phase3Transition
  set s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then
      let pmax := max s.minute t.minute
      { s with minute := pmax }
    else if h_max : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else
      stdCounterSubroutine L K s
  else s
  set t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then
      let pmax := max s.minute t.minute
      { t with minute := pmax }
    else if h_max : s.minute.val < K * (L + 1) then
      t
    else
      stdCounterSubroutine L K t
  else t
  have ht1 : t1.role ≠ .mcr := by
    dsimp [t1]
    split_ifs <;>
      first | exact stdCounterSubroutine_no_mcr (L := L) (K := K) t ht
            | simpa using ht
  set s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    s1
  else s1
  set t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have ht2 : t2.role ≠ .mcr := by
    dsimp [t2]
    split_ifs <;> simpa using ht1
  change (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
    else (s2, t2)).2.role ≠ .mcr
  split_ifs
  · exact phase3CancelSplit_second_no_mcr (L := L) (K := K) s2 t2 ht2
  · simpa using ht2

lemma Phase4Transition_first_no_mcr (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (Phase4Transition L K s t).1.role ≠ .mcr := by
  unfold Phase4Transition
  dsimp
  split
  · exact advancePhase_no_mcr (L := L) (K := K) s hs
  · simpa using hs

lemma Phase4Transition_second_no_mcr (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (Phase4Transition L K s t).2.role ≠ .mcr := by
  unfold Phase4Transition
  dsimp
  split
  · exact advancePhase_no_mcr (L := L) (K := K) t ht
  · simpa using ht

lemma Phase5Transition_first_no_mcr (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (Phase5Transition L K s t).1.role ≠ .mcr := by
  unfold Phase5Transition
  set s1 := if s.role = .reserve ∧ t.role = .main ∧ t.bias ≠ .zero then
    (if s.hour.val = L then ({ s with hour := exponentOf L t.bias }, t) else (s, t)).1
  else if t.role = .reserve ∧ s.role = .main ∧ s.bias ≠ .zero then
    (if t.hour.val = L then ({ t with hour := exponentOf L s.bias }, s) else (t, s)).2
  else s
  have hs1 : s1.role ≠ .mcr := by
    dsimp [s1]
    split_ifs <;> simpa using hs
  change (if s1.role = .clock then stdCounterSubroutine L K s1 else s1).role ≠ .mcr
  exact clockCounterFinish_no_mcr (L := L) (K := K) s1 hs1

lemma Phase5Transition_second_no_mcr (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (Phase5Transition L K s t).2.role ≠ .mcr := by
  unfold Phase5Transition
  set t1 := if s.role = .reserve ∧ t.role = .main ∧ t.bias ≠ .zero then
    (if s.hour.val = L then ({ s with hour := exponentOf L t.bias }, t) else (s, t)).2
  else if t.role = .reserve ∧ s.role = .main ∧ s.bias ≠ .zero then
    (if t.hour.val = L then ({ t with hour := exponentOf L s.bias }, s) else (t, s)).1
  else t
  have ht1 : t1.role ≠ .mcr := by
    dsimp [t1]
    split_ifs <;> simpa using ht
  change (if t1.role = .clock then stdCounterSubroutine L K t1 else t1).role ≠ .mcr
  exact clockCounterFinish_no_mcr (L := L) (K := K) t1 ht1

lemma Phase6Transition_first_no_mcr (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (Phase6Transition L K s t).1.role ≠ .mcr := by
  unfold Phase6Transition
  set s1 := if s.role = .reserve ∧ t.role = .main ∧ t.bias ≠ .zero then
    (doSplit L K s t).1
  else if t.role = .reserve ∧ s.role = .main ∧ s.bias ≠ .zero then
    (doSplit L K t s).2
  else s
  have hs1 : s1.role ≠ .mcr := by
    dsimp [s1]
    split_ifs
    · exact doSplit_first_no_mcr (L := L) (K := K) s t hs
    · exact doSplit_second_no_mcr (L := L) (K := K) t s hs
    · simpa using hs
  change (if s1.role = .clock then stdCounterSubroutine L K s1 else s1).role ≠ .mcr
  exact clockCounterFinish_no_mcr (L := L) (K := K) s1 hs1

lemma Phase6Transition_second_no_mcr (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (Phase6Transition L K s t).2.role ≠ .mcr := by
  unfold Phase6Transition
  set t1 := if s.role = .reserve ∧ t.role = .main ∧ t.bias ≠ .zero then
    (doSplit L K s t).2
  else if t.role = .reserve ∧ s.role = .main ∧ s.bias ≠ .zero then
    (doSplit L K t s).1
  else t
  have ht1 : t1.role ≠ .mcr := by
    dsimp [t1]
    split_ifs
    · exact doSplit_second_no_mcr (L := L) (K := K) s t ht
    · exact doSplit_first_no_mcr (L := L) (K := K) t s ht
    · simpa using ht
  change (if t1.role = .clock then stdCounterSubroutine L K t1 else t1).role ≠ .mcr
  exact clockCounterFinish_no_mcr (L := L) (K := K) t1 ht1

lemma Phase7Transition_first_no_mcr (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (Phase7Transition L K s t).1.role ≠ .mcr := by
  unfold Phase7Transition
  set s1 := if s.role = .main ∧ t.role = .main then (cancelSplit L K s t).1 else s
  have hs1 : s1.role ≠ .mcr := by
    dsimp [s1]
    split_ifs
    · exact cancelSplit_first_no_mcr (L := L) (K := K) s t hs
    · simpa using hs
  change (if s1.role = .clock then stdCounterSubroutine L K s1 else s1).role ≠ .mcr
  exact clockCounterFinish_no_mcr (L := L) (K := K) s1 hs1

lemma Phase7Transition_second_no_mcr (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (Phase7Transition L K s t).2.role ≠ .mcr := by
  unfold Phase7Transition
  set t1 := if s.role = .main ∧ t.role = .main then (cancelSplit L K s t).2 else t
  have ht1 : t1.role ≠ .mcr := by
    dsimp [t1]
    split_ifs
    · exact cancelSplit_second_no_mcr (L := L) (K := K) s t ht
    · simpa using ht
  change (if t1.role = .clock then stdCounterSubroutine L K t1 else t1).role ≠ .mcr
  exact clockCounterFinish_no_mcr (L := L) (K := K) t1 ht1

lemma Phase8Transition_first_no_mcr (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (Phase8Transition L K s t).1.role ≠ .mcr := by
  unfold Phase8Transition
  set s1 := if s.role = .main ∧ t.role = .main then (absorbConsume L K s t).1 else s
  have hs1 : s1.role ≠ .mcr := by
    dsimp [s1]
    split_ifs
    · exact absorbConsume_first_no_mcr (L := L) (K := K) s t hs
    · simpa using hs
  change (if s1.role = .clock then stdCounterSubroutine L K s1 else s1).role ≠ .mcr
  exact clockCounterFinish_no_mcr (L := L) (K := K) s1 hs1

lemma Phase8Transition_second_no_mcr (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (Phase8Transition L K s t).2.role ≠ .mcr := by
  unfold Phase8Transition
  set t1 := if s.role = .main ∧ t.role = .main then (absorbConsume L K s t).2 else t
  have ht1 : t1.role ≠ .mcr := by
    dsimp [t1]
    split_ifs
    · exact absorbConsume_second_no_mcr (L := L) (K := K) s t ht
    · simpa using ht
  change (if t1.role = .clock then stdCounterSubroutine L K t1 else t1).role ≠ .mcr
  exact clockCounterFinish_no_mcr (L := L) (K := K) t1 ht1

lemma Phase9Transition_first_no_mcr (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (Phase9Transition L K s t).1.role ≠ .mcr := by
  unfold Phase9Transition
  exact Phase2Transition_first_no_mcr (L := L) (K := K) s t hs

lemma Phase9Transition_second_no_mcr (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (Phase9Transition L K s t).2.role ≠ .mcr := by
  unfold Phase9Transition
  exact Phase2Transition_second_no_mcr (L := L) (K := K) s t ht

lemma Phase10Transition_first_no_mcr (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (Phase10Transition L K s t).1.role ≠ .mcr := by
  unfold Phase10Transition
  set s1 :=
    if s.full ∧ t.full then
      if (s.output = .A ∧ t.output = .B) ∨ (s.output = .B ∧ t.output = .A) then
        { s with output := .T }
      else if s.output = .T ∧ (t.output = .A ∨ t.output = .B) then
        { s with output := t.output, full := false }
      else s
    else s
  set t1 :=
    if s.full ∧ t.full then
      if (s.output = .A ∧ t.output = .B) ∨ (s.output = .B ∧ t.output = .A) then
        { t with output := .T }
      else if t.output = .T ∧ (s.output = .A ∨ s.output = .B) then
        { t with output := s.output, full := false }
      else t
    else t
  have hs1 : s1.role ≠ .mcr := by
    dsimp [s1]
    split_ifs <;> simpa using hs
  change (if s1.full ∧ ¬ t1.full then
      ({ s1 with output := s1.output }, { t1 with output := s1.output })
    else if ¬ s1.full ∧ t1.full then
      ({ s1 with output := t1.output }, { t1 with output := t1.output })
    else (s1, t1)).1.role ≠ .mcr
  split_ifs <;> simpa using hs1

lemma Phase10Transition_second_no_mcr (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (Phase10Transition L K s t).2.role ≠ .mcr := by
  unfold Phase10Transition
  set s1 :=
    if s.full ∧ t.full then
      if (s.output = .A ∧ t.output = .B) ∨ (s.output = .B ∧ t.output = .A) then
        { s with output := .T }
      else if s.output = .T ∧ (t.output = .A ∨ t.output = .B) then
        { s with output := t.output, full := false }
      else s
    else s
  set t1 :=
    if s.full ∧ t.full then
      if (s.output = .A ∧ t.output = .B) ∨ (s.output = .B ∧ t.output = .A) then
        { t with output := .T }
      else if t.output = .T ∧ (s.output = .A ∨ s.output = .B) then
        { t with output := s.output, full := false }
      else t
    else t
  have ht1 : t1.role ≠ .mcr := by
    dsimp [t1]
    split_ifs <;> simpa using ht
  change (if s1.full ∧ ¬ t1.full then
      ({ s1 with output := s1.output }, { t1 with output := s1.output })
    else if ¬ s1.full ∧ t1.full then
      ({ s1 with output := t1.output }, { t1 with output := t1.output })
    else (s1, t1)).2.role ≠ .mcr
  split_ifs <;> simpa using ht1

private lemma enterPhase10_no_mcr (a : AgentState L K) (ha : a.role ≠ .mcr) :
    (enterPhase10 L K a).role ≠ .mcr := by
  simp [enterPhase10, ha]

private lemma canonicalPhase10Entry_no_mcr
    (before after : AgentState L K) (ha : after.role ≠ .mcr) :
    (canonicalPhase10Entry L K before after).role ≠ .mcr := by
  unfold canonicalPhase10Entry
  split_ifs
  · exact enterPhase10_no_mcr after ha
  · exact ha

private lemma finishPhase10Entry_no_mcr
    (before after : AgentState L K) (ha : after.role ≠ .mcr) :
    (finishPhase10Entry L K before after).role ≠ .mcr := by
  unfold finishPhase10Entry
  exact canonicalPhase10Entry_no_mcr before after ha

set_option maxHeartbeats 1600000 in
private lemma phaseDispatch_first_no_mcr (s' t' : AgentState L K) (hs : s'.role ≠ .mcr) :
    (match s'.phase with
     | ⟨0, _⟩ => Phase0Transition L K s' t'
     | ⟨1, _⟩ => Phase1Transition L K s' t'
     | ⟨2, _⟩ => Phase2Transition L K s' t'
     | ⟨3, _⟩ => Phase3Transition L K s' t'
     | ⟨4, _⟩ => Phase4Transition L K s' t'
     | ⟨5, _⟩ => Phase5Transition L K s' t'
     | ⟨6, _⟩ => Phase6Transition L K s' t'
     | ⟨7, _⟩ => Phase7Transition L K s' t'
     | ⟨8, _⟩ => Phase8Transition L K s' t'
     | ⟨9, _⟩ => Phase9Transition L K s' t'
     | ⟨10, _⟩ => Phase10Transition L K s' t'
     | _ => (s', t')).1.role ≠ .mcr := by
  split <;> first
    | exact Phase0Transition_first_no_mcr s' t' hs
    | exact Phase1Transition_first_no_mcr s' t' hs
    | exact Phase2Transition_first_no_mcr s' t' hs
    | exact Phase3Transition_first_no_mcr s' t' hs
    | exact Phase4Transition_first_no_mcr s' t' hs
    | exact Phase5Transition_first_no_mcr s' t' hs
    | exact Phase6Transition_first_no_mcr s' t' hs
    | exact Phase7Transition_first_no_mcr s' t' hs
    | exact Phase8Transition_first_no_mcr s' t' hs
    | exact Phase9Transition_first_no_mcr s' t' hs
    | exact Phase10Transition_first_no_mcr s' t' hs
    | exact hs

set_option maxHeartbeats 1600000 in
private lemma phaseDispatch_second_no_mcr (s' t' : AgentState L K) (ht : t'.role ≠ .mcr) :
    (match s'.phase with
     | ⟨0, _⟩ => Phase0Transition L K s' t'
     | ⟨1, _⟩ => Phase1Transition L K s' t'
     | ⟨2, _⟩ => Phase2Transition L K s' t'
     | ⟨3, _⟩ => Phase3Transition L K s' t'
     | ⟨4, _⟩ => Phase4Transition L K s' t'
     | ⟨5, _⟩ => Phase5Transition L K s' t'
     | ⟨6, _⟩ => Phase6Transition L K s' t'
     | ⟨7, _⟩ => Phase7Transition L K s' t'
     | ⟨8, _⟩ => Phase8Transition L K s' t'
     | ⟨9, _⟩ => Phase9Transition L K s' t'
     | ⟨10, _⟩ => Phase10Transition L K s' t'
     | _ => (s', t')).2.role ≠ .mcr := by
  split <;> first
    | exact Phase0Transition_second_no_mcr s' t' ht
    | exact Phase1Transition_second_no_mcr s' t' ht
    | exact Phase2Transition_second_no_mcr s' t' ht
    | exact Phase3Transition_second_no_mcr s' t' ht
    | exact Phase4Transition_second_no_mcr s' t' ht
    | exact Phase5Transition_second_no_mcr s' t' ht
    | exact Phase6Transition_second_no_mcr s' t' ht
    | exact Phase7Transition_second_no_mcr s' t' ht
    | exact Phase8Transition_second_no_mcr s' t' ht
    | exact Phase9Transition_second_no_mcr s' t' ht
    | exact Phase10Transition_second_no_mcr s' t' ht
    | exact ht

set_option maxHeartbeats 800000 in
lemma Transition_first_no_mcr (s t : AgentState L K) (hs : s.role ≠ .mcr) :
    (Transition L K s t).1.role ≠ .mcr := by
  unfold Transition
  apply finishPhase10Entry_no_mcr
  apply phaseDispatch_first_no_mcr
  exact phaseEpidemicUpdate_first_no_mcr s t hs

set_option maxHeartbeats 800000 in
lemma Transition_second_no_mcr (s t : AgentState L K) (ht : t.role ≠ .mcr) :
    (Transition L K s t).2.role ≠ .mcr := by
  unfold Transition
  apply finishPhase10Entry_no_mcr
  apply phaseDispatch_second_no_mcr
  exact phaseEpidemicUpdate_second_no_mcr s t ht

private lemma mcrCount_singleton (a : AgentState L K) :
    mcrCount ({a} : Config (AgentState L K)) = if a.role = .mcr then 1 else 0 := by
  unfold mcrCount
  simp [Multiset.filter_singleton]
  split_ifs <;> simp_all

private lemma mcrCount_pair (a b : AgentState L K) :
    mcrCount ({a, b} : Config (AgentState L K)) =
    (if a.role = .mcr then 1 else 0) + (if b.role = .mcr then 1 else 0) := by
  show mcrCount ({a} + {b}) = _
  rw [mcrCount_add, mcrCount_singleton, mcrCount_singleton]

lemma Transition_mcrCount_le (s t : AgentState L K) :
    mcrCount {(Transition L K s t).1, (Transition L K s t).2} ≤ mcrCount {s, t} := by
  rw [mcrCount_pair, mcrCount_pair]
  have h1 : ¬s.role = .mcr → ¬(Transition L K s t).1.role = .mcr :=
    fun h => Transition_first_no_mcr s t h
  have h2 : ¬t.role = .mcr → ¬(Transition L K s t).2.role = .mcr :=
    fun h => Transition_second_no_mcr s t h
  by_cases hs : s.role = .mcr <;> by_cases ht : t.role = .mcr <;>
    simp_all <;> split_ifs <;> omega

def phaseBelowCount (k : ℕ) (c : Config (AgentState L K)) : ℕ :=
  (c.filter (fun a => decide (a.phase.val < k))).card

lemma phaseBelowCount_add (k : ℕ) (c₁ c₂ : Config (AgentState L K)) :
    phaseBelowCount k (c₁ + c₂) = phaseBelowCount k c₁ + phaseBelowCount k c₂ := by
  simp [phaseBelowCount]

lemma Transition_phaseBelowCount_le (k : ℕ) (s t : AgentState L K) :
    phaseBelowCount k {(Transition L K s t).1, (Transition L K s t).2} ≤
    phaseBelowCount k {s, t} := by
  show phaseBelowCount k ({(Transition L K s t).1} + {(Transition L K s t).2}) ≤
    phaseBelowCount k ({s} + {t})
  rw [phaseBelowCount_add, phaseBelowCount_add]
  simp only [phaseBelowCount, Multiset.filter_singleton, Multiset.card_cons,
    Multiset.card_zero]
  have hm := Transition_phase_monotone (L := L) (K := K) s t
  have hm1 : s.phase.val ≤ (Transition L K s t).1.phase.val := hm.1
  have hm2 : t.phase.val ≤ (Transition L K s t).2.phase.val := hm.2
  by_cases h1 : (Transition L K s t).1.phase.val < k <;>
    by_cases h2 : (Transition L K s t).2.phase.val < k <;>
    simp [h1, h2] <;> (try omega) <;>
    (by_cases h3 : s.phase.val < k <;> by_cases h4 : t.phase.val < k <;>
      simp [h3, h4] <;> omega)

lemma phaseBelowCount_step_le (k : ℕ) (c c' : Config (AgentState L K))
    (h : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    phaseBelowCount k c' ≤ phaseBelowCount k c := by
  unfold Protocol.stepDistOrSelf at h
  split_ifs at h with h_size
  · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ h
    subst heq
    unfold Protocol.scheduledStep Protocol.stepOrSelf at *
    split_ifs at * with h_app
    · have h_sub : {r₁, r₂} ≤ c := by
        unfold Protocol.Applicable at h_app; exact h_app
      have h_restore : c - {r₁, r₂} + {r₁, r₂} = c := Multiset.sub_add_cancel h_sub
      calc phaseBelowCount k (c - {r₁, r₂} + {(Transition L K r₁ r₂).1,
              (Transition L K r₁ r₂).2})
          = phaseBelowCount k (c - {r₁, r₂}) + phaseBelowCount k {(Transition L K r₁ r₂).1,
              (Transition L K r₁ r₂).2} := phaseBelowCount_add _ _ _
        _ ≤ phaseBelowCount k (c - {r₁, r₂}) + phaseBelowCount k {r₁, r₂} :=
            Nat.add_le_add_left (Transition_phaseBelowCount_le k r₁ r₂) _
        _ = phaseBelowCount k (c - {r₁, r₂} + {r₁, r₂}) := (phaseBelowCount_add _ _ _).symm
        _ = phaseBelowCount k c := by rw [h_restore]
    · rfl
  · simp [PMF.support_pure] at h; rw [h]

lemma mcrCount_step_le (c c' : Config (AgentState L K))
    (h : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    mcrCount c' ≤ mcrCount c := by
  unfold Protocol.stepDistOrSelf at h
  split_ifs at h with h_size
  · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ h
    subst heq
    unfold Protocol.scheduledStep Protocol.stepOrSelf at *
    split_ifs at * with h_app
    · have h_sub : {r₁, r₂} ≤ c := by
        unfold Protocol.Applicable at h_app; exact h_app
      have h_restore : c - {r₁, r₂} + {r₁, r₂} = c := Multiset.sub_add_cancel h_sub
      calc mcrCount (c - {r₁, r₂} + {(Transition L K r₁ r₂).1,
              (Transition L K r₁ r₂).2})
          = mcrCount (c - {r₁, r₂}) + mcrCount {(Transition L K r₁ r₂).1,
              (Transition L K r₁ r₂).2} := mcrCount_add _ _
        _ ≤ mcrCount (c - {r₁, r₂}) + mcrCount {r₁, r₂} :=
            Nat.add_le_add_left (Transition_mcrCount_le (L := L) (K := K) r₁ r₂) _
        _ = mcrCount (c - {r₁, r₂} + {r₁, r₂}) := (mcrCount_add _ _).symm
        _ = mcrCount c := by rw [h_restore]
    · rfl
  · simp [PMF.support_pure] at h; rw [h]

lemma mcrCount_ae_noninc (c : Config (AgentState L K)) :
    ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c), mcrCount c' ≤ mcrCount c := by
  change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
  rw [MeasureTheory.ae_iff]
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {c' | ¬mcrCount c' ≤ mcrCount c} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  exact Set.disjoint_left.mpr fun c' hc' hbad =>
    absurd (mcrCount_step_le c c' hc') (Set.mem_setOf.mp hbad)

lemma phaseBelowCount_ae_noninc (k : ℕ) (c : Config (AgentState L K)) :
    ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
      phaseBelowCount k c' ≤ phaseBelowCount k c := by
  change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
  rw [MeasureTheory.ae_iff]
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {c' | ¬phaseBelowCount k c' ≤ phaseBelowCount k c} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  exact Set.disjoint_left.mpr fun c' hc' hbad =>
    absurd (phaseBelowCount_step_le k c c' hc') (Set.mem_setOf.mp hbad)

/-! ### Scheduler probability lower bounds -/

noncomputable instance : MeasurableSpace (AgentState L K × AgentState L K) := ⊤
instance : DiscreteMeasurableSpace (AgentState L K × AgentState L K) := ⟨fun _ => trivial⟩

/-- Lower bound on stepDist measure via preimage monotonicity.
If all "good" pairs map into the target set, the target gets at least
the probability mass of the good pairs. -/
lemma stepDistOrSelf_toMeasure_ge
    (c : Config (AgentState L K)) (hc : 2 ≤ c.card)
    (target : Set (Config (AgentState L K)))
    (good : Set (AgentState L K × AgentState L K))
    (hgood : ∀ pair ∈ good,
      (NonuniformMajority L K).scheduledStep c pair ∈ target) :
    ((NonuniformMajority L K).stepDistOrSelf c).toMeasure target ≥
      (c.interactionPMF hc).toMeasure good := by
  have h_meas : MeasurableSet target := DiscreteMeasurableSpace.forall_measurableSet _
  unfold Protocol.stepDistOrSelf
  rw [dif_pos hc]
  unfold Protocol.stepDist
  have h_map := PMF.toMeasure_map ((NonuniformMajority L K).scheduledStep c)
    (c.interactionPMF hc) Measurable.of_discrete
  calc (PMF.map ((NonuniformMajority L K).scheduledStep c)
        (c.interactionPMF hc)).toMeasure target
      = ((c.interactionPMF hc).toMeasure.map
          ((NonuniformMajority L K).scheduledStep c)) target := by
          rw [← h_map]
    _ = (c.interactionPMF hc).toMeasure
          ((NonuniformMajority L K).scheduledStep c ⁻¹' target) :=
        MeasureTheory.Measure.map_apply Measurable.of_discrete h_meas
    _ ≥ (c.interactionPMF hc).toMeasure good :=
        MeasureTheory.measure_mono (fun pair hp => hgood pair hp)

/-- When both agents are MCR, Phase0Transition Rule 1 converts them to main+cr.
All subsequent rules preserve non-MCR, so both outputs are non-MCR. -/
lemma Phase0Transition_no_mcr_of_mcr_mcr (s t : AgentState L K)
    (hs : s.role = .mcr) (ht : t.role = .mcr) :
    (Phase0Transition L K s t).1.role ≠ .mcr ∧
    (Phase0Transition L K s t).2.role ≠ .mcr := by
  rw [phase0_first_decompose, phase0_second_decompose]
  have hs1 : (p0r1s s t).role = .main := by unfold p0r1s; simp [hs, ht]
  have ht1 : (p0r1t s t).role = .cr := by unfold p0r1t; simp [hs, ht]
  have hs1_ne : (p0r1s s t).role ≠ .mcr := by rw [hs1]; decide
  have ht1_ne : (p0r1t s t).role ≠ .mcr := by rw [ht1]; decide
  exact ⟨p0r5s_no_mcr _ _ (p0r4s_no_mcr _ _ (p0r3ps_no_mcr _ _
      (p0r3s_no_mcr _ _ (p0r2s_no_mcr _ _ hs1_ne)))),
    p0r5t_no_mcr _ _ (p0r4t_no_mcr _ _ (p0r3pt_no_mcr _ _
      (p0r3t_no_mcr _ _ (p0r2t_no_mcr _ _ ht1_ne))))⟩

-- Note: Phase0Transition_first_no_mcr_of_mcr is NOT universally true.
-- MCR+assigned_main, MCR+clock, MCR+reserve leave MCR unchanged.
-- MCR count decreases only for MCR+MCR, MCR+unassigned_main, MCR+cr.

/-! ### MCR+MCR interaction decreases mcrCount (phase 0 agents) -/

-- Note: MCR+MCR does NOT always decrease mcrCount at the Transition level!
-- If either MCR agent is at phase > 0, the epidemic update sends it to phase 10
-- via enterPhase10, which preserves role = .mcr. Phase10Transition doesn't change
-- MCR role. So MCR agents at phase > 0 stay MCR after transition.
-- The decrease only happens when BOTH MCR agents are at phase 0.

/-- `phaseInit` preserves the MCR role. -/
private lemma phaseInit_mcr (p : Fin 11) (a : AgentState L K) (ha : a.role = .mcr) :
    (phaseInit L K p a).role = .mcr := by
  rcases a with ⟨input, output, phase, role, assigned, bias, smallBias,
    hour, minute, full, opinions, counter⟩
  simp only at ha; subst ha
  fin_cases p <;> simp [phaseInit, enterPhase10] <;> repeat' split_ifs <;> simp_all

private lemma foldl_phaseInit_mcr (ks : List ℕ) (a : AgentState L K) (ha : a.role = .mcr) :
    (ks.foldl
      (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
      a).role = .mcr := by
  induction ks generalizing a with
  | nil => simpa using ha
  | cons k ks ih =>
      simp only [List.foldl]
      apply ih
      by_cases hk : k < 11
      · simpa [hk] using phaseInit_mcr (L := L) (K := K) ⟨k, hk⟩ a ha
      · simpa [hk] using ha

private lemma runInitsBetween_mcr
    (oldP newP : ℕ) (a : AgentState L K) (ha : a.role = .mcr) :
    (runInitsBetween L K oldP newP a).role = .mcr := by
  unfold runInitsBetween
  exact foldl_phaseInit_mcr
    (L := L) (K := K) ((List.range 11).filter fun k => oldP < k ∧ k ≤ newP) a ha

private lemma phase10EpidemicEntry_mcr
    (before after : AgentState L K) (ha : after.role = .mcr) :
    (phase10EpidemicEntry L K before after).role = .mcr := by
  unfold phase10EpidemicEntry
  split_ifs <;> simpa [enterPhase10] using ha

private lemma phaseEpidemicUpdate_first_mcr (s t : AgentState L K) (hs : s.role = .mcr) :
    (phaseEpidemicUpdate L K s t).1.role = .mcr := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase
  set s' := runInitsBetween L K s.phase.val p.val ({ s with phase := p } : AgentState L K)
  set t' := runInitsBetween L K t.phase.val p.val ({ t with phase := p } : AgentState L K)
  have hs' : s'.role = .mcr :=
    runInitsBetween_mcr (L := L) (K := K) s.phase.val p.val _ (by simpa)
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s'.phase.val = 10 ∨ t'.phase.val = 10) then
      (phase10EpidemicEntry L K s s', phase10EpidemicEntry L K t t')
    else (s', t')).1.role = .mcr
  by_cases h10 : (s.phase.val < 10 ∨ t.phase.val < 10) ∧
      (s'.phase.val = 10 ∨ t'.phase.val = 10)
  · simpa [h10] using phase10EpidemicEntry_mcr (L := L) (K := K) s s' hs'
  · simpa [h10] using hs'

private lemma phaseEpidemicUpdate_second_mcr (s t : AgentState L K) (ht : t.role = .mcr) :
    (phaseEpidemicUpdate L K s t).2.role = .mcr := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase
  set s' := runInitsBetween L K s.phase.val p.val ({ s with phase := p } : AgentState L K)
  set t' := runInitsBetween L K t.phase.val p.val ({ t with phase := p } : AgentState L K)
  have ht' : t'.role = .mcr :=
    runInitsBetween_mcr (L := L) (K := K) t.phase.val p.val _ (by simpa)
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s'.phase.val = 10 ∨ t'.phase.val = 10) then
      (phase10EpidemicEntry L K s s', phase10EpidemicEntry L K t t')
    else (s', t')).2.role = .mcr
  by_cases h10 : (s.phase.val < 10 ∨ t.phase.val < 10) ∧
      (s'.phase.val = 10 ∨ t'.phase.val = 10)
  · simpa [h10] using phase10EpidemicEntry_mcr (L := L) (K := K) t t' ht'
  · simpa [h10] using ht'

/-- When both agents have the same phase, phaseEpidemicUpdate preserves the phase. -/
private lemma phaseEpidemicUpdate_first_phase_of_same (s t : AgentState L K)
    (h : s.phase = t.phase) :
    (phaseEpidemicUpdate L K s t).1.phase = s.phase := by
  unfold phaseEpidemicUpdate
  have hmax : max s.phase t.phase = s.phase := by rw [h, max_self]
  rw [hmax]
  have hs' : runInitsBetween L K s.phase.val s.phase.val
      ({ s with phase := s.phase } : AgentState L K) =
      { s with phase := s.phase } :=
    runInitsBetween_self_api (L := L) (K := K) s.phase.val _
  have ht' : runInitsBetween L K t.phase.val s.phase.val
      ({ t with phase := s.phase } : AgentState L K) =
      { t with phase := s.phase } := by
    rw [show t.phase.val = s.phase.val from by rw [h]]
    exact runInitsBetween_self_api (L := L) (K := K) s.phase.val _
  simp only [hs', ht']
  have h_s_phase_eq : ({ s with phase := s.phase } : AgentState L K).phase.val = s.phase.val := rfl
  have h_t_phase_eq : ({ t with phase := s.phase } : AgentState L K).phase.val = s.phase.val := rfl
  have hcond : ¬ ((s.phase.val < 10 ∨ t.phase.val < 10) ∧
      (({ s with phase := s.phase } : AgentState L K).phase.val = 10 ∨
       ({ t with phase := s.phase } : AgentState L K).phase.val = 10)) := by
    rw [h_s_phase_eq, h_t_phase_eq, h]
    omega
  rw [if_neg hcond]

set_option maxHeartbeats 1600000 in
lemma Transition_no_mcr_of_both_phase0_mcr (s t : AgentState L K)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0)
    (hs : s.role = .mcr) (ht : t.role = .mcr) :
    (Transition L K s t).1.role ≠ .mcr ∧
    (Transition L K s t).2.role ≠ .mcr := by
  have h_phase_eq : s.phase = t.phase := Fin.ext (by omega)
  have hs'_mcr := phaseEpidemicUpdate_first_mcr (L := L) (K := K) s t hs
  have ht'_mcr := phaseEpidemicUpdate_second_mcr (L := L) (K := K) s t ht
  have hs'_phase := phaseEpidemicUpdate_first_phase_of_same (L := L) (K := K) s t h_phase_eq
  set s' := (phaseEpidemicUpdate L K s t).1
  set t' := (phaseEpidemicUpdate L K s t).2
  have hs'_phase_val : s'.phase.val = 0 := by
    have := congrArg Fin.val hs'_phase; simp at this; rw [this, hs_phase]
  have h_p0 := Phase0Transition_no_mcr_of_mcr_mcr (L := L) (K := K) s' t' hs'_mcr ht'_mcr
  have hs'0 : s'.phase = ⟨0, by omega⟩ := Fin.ext hs'_phase_val
  have hT1 : (Transition L K s t).1 =
      finishPhase10Entry L K s' (Phase0Transition L K s' t').1 := by
    unfold Transition
    show finishPhase10Entry L K s'
      (match s'.phase with
       | ⟨0, _⟩ => Phase0Transition L K s' t'
       | ⟨1, _⟩ => Phase1Transition L K s' t'
       | ⟨2, _⟩ => Phase2Transition L K s' t'
       | ⟨3, _⟩ => Phase3Transition L K s' t'
       | ⟨4, _⟩ => Phase4Transition L K s' t'
       | ⟨5, _⟩ => Phase5Transition L K s' t'
       | ⟨6, _⟩ => Phase6Transition L K s' t'
       | ⟨7, _⟩ => Phase7Transition L K s' t'
       | ⟨8, _⟩ => Phase8Transition L K s' t'
       | ⟨9, _⟩ => Phase9Transition L K s' t'
       | ⟨10, _⟩ => Phase10Transition L K s' t'
       | _ => (s', t')).1 = _
    rw [hs'0]
  have hT2 : (Transition L K s t).2 =
      finishPhase10Entry L K t' (Phase0Transition L K s' t').2 := by
    unfold Transition
    show finishPhase10Entry L K t'
      (match s'.phase with
       | ⟨0, _⟩ => Phase0Transition L K s' t'
       | ⟨1, _⟩ => Phase1Transition L K s' t'
       | ⟨2, _⟩ => Phase2Transition L K s' t'
       | ⟨3, _⟩ => Phase3Transition L K s' t'
       | ⟨4, _⟩ => Phase4Transition L K s' t'
       | ⟨5, _⟩ => Phase5Transition L K s' t'
       | ⟨6, _⟩ => Phase6Transition L K s' t'
       | ⟨7, _⟩ => Phase7Transition L K s' t'
       | ⟨8, _⟩ => Phase8Transition L K s' t'
       | ⟨9, _⟩ => Phase9Transition L K s' t'
       | ⟨10, _⟩ => Phase10Transition L K s' t'
       | _ => (s', t')).2 = _
    rw [hs'0]
  constructor
  · rw [hT1]; exact finishPhase10Entry_no_mcr (L := L) (K := K) s' _ h_p0.1
  · rw [hT2]; exact finishPhase10Entry_no_mcr (L := L) (K := K) t' _ h_p0.2

/-- When both agents are phase 0 MCR, the pair mcrCount strictly decreases. -/
lemma Transition_mcrCount_pair_lt_of_both_phase0_mcr (s t : AgentState L K)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0)
    (hs : s.role = .mcr) (ht : t.role = .mcr) :
    mcrCount ({(Transition L K s t).1, (Transition L K s t).2} : Config (AgentState L K)) <
    mcrCount ({s, t} : Config (AgentState L K)) := by
  have h := Transition_no_mcr_of_both_phase0_mcr (L := L) (K := K) s t hs_phase ht_phase hs ht
  rw [mcrCount_pair, mcrCount_pair]
  simp [hs, ht, h.1, h.2]

/-- Configuration mcrCount strictly decreases when a pair of phase-0 MCR agents interact. -/
lemma mcrCount_config_decrease_of_phase0_mcr_pair
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (h_sub : {r₁, r₂} ≤ c)
    (hr₁_phase : r₁.phase.val = 0) (hr₂_phase : r₂.phase.val = 0)
    (hr₁ : r₁.role = .mcr) (hr₂ : r₂.role = .mcr) :
    mcrCount (c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}) <
    mcrCount c := by
  have h_restore : c - {r₁, r₂} + {r₁, r₂} = c := Multiset.sub_add_cancel h_sub
  have h_pair_lt := Transition_mcrCount_pair_lt_of_both_phase0_mcr (L := L) (K := K)
    r₁ r₂ hr₁_phase hr₂_phase hr₁ hr₂
  calc mcrCount (c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2})
      = mcrCount (c - {r₁, r₂}) + mcrCount {(Transition L K r₁ r₂).1,
          (Transition L K r₁ r₂).2} := mcrCount_add _ _
    _ < mcrCount (c - {r₁, r₂}) + mcrCount {r₁, r₂} :=
        Nat.add_lt_add_left h_pair_lt _
    _ = mcrCount (c - {r₁, r₂} + {r₁, r₂}) := (mcrCount_add _ _).symm
    _ = mcrCount c := by rw [h_restore]

/-! ### MCR role preservation for MCR agents at phase > 0

When an MCR agent has phase > 0, the Transition function preserves its MCR role.
Phases 1-10 do not have MCR-specific rules (MCR ≠ main/clock/cr/reserve),
so MCR agents pass through unchanged. -/

private lemma advancePhaseWithInit_mcr (a : AgentState L K) (ha : a.role = .mcr) :
    (advancePhaseWithInit L K a).role = .mcr := by
  unfold advancePhaseWithInit
  exact phaseInit_mcr (L := L) (K := K) (advancePhase L K a).phase
    (advancePhase L K a) (by rw [advancePhase_role]; exact ha)

private lemma stdCounterSubroutine_mcr (a : AgentState L K) (ha : a.role = .mcr) :
    (stdCounterSubroutine L K a).role = .mcr := by
  unfold stdCounterSubroutine
  split
  · exact advancePhaseWithInit_mcr (L := L) (K := K) a ha
  · simpa using ha

private lemma clockCounterStep_mcr (a : AgentState L K) (ha : a.role = .mcr) :
    (clockCounterStep L K a).role = .mcr := by
  rw [clockCounterStep_role_eq]; exact ha

private lemma Phase1Transition_first_mcr (s t : AgentState L K) (hs : s.role = .mcr) :
    (Phase1Transition L K s t).1.role = .mcr := by
  unfold Phase1Transition
  have : ¬(s.role = .main ∧ t.role = .main) := by simp [hs]
  simp [this, clockCounterStep_role_eq, hs]

private lemma Phase1Transition_second_mcr (s t : AgentState L K) (ht : t.role = .mcr) :
    (Phase1Transition L K s t).2.role = .mcr := by
  unfold Phase1Transition
  split_ifs <;> simp [clockCounterStep_role_eq, ht]

private lemma Phase2Transition_first_mcr (s t : AgentState L K) (hs : s.role = .mcr) :
    (Phase2Transition L K s t).1.role = .mcr := by
  unfold Phase2Transition
  set univ := opinionsUnion s.opinions t.opinions
  set s' : AgentState L K := { s with opinions := univ }
  have hs' : s'.role = .mcr := by simp [s', hs]
  by_cases h1 : (hasMinusOne univ && hasPlusOne univ) = true
  · simp [h1]; exact advancePhaseWithInit_mcr (L := L) (K := K) s' hs'
  · simp [h1]; split_ifs <;> simpa using hs

private lemma Phase2Transition_second_mcr (s t : AgentState L K) (ht : t.role = .mcr) :
    (Phase2Transition L K s t).2.role = .mcr := by
  unfold Phase2Transition
  set univ := opinionsUnion s.opinions t.opinions
  set t' : AgentState L K := { t with opinions := univ }
  have ht' : t'.role = .mcr := by simp [t', ht]
  by_cases h1 : (hasMinusOne univ && hasPlusOne univ) = true
  · simp [h1]; exact advancePhaseWithInit_mcr (L := L) (K := K) t' ht'
  · simp [h1]; split_ifs <;> simpa using ht

private lemma Phase3Transition_first_mcr (s t : AgentState L K) (hs : s.role = .mcr) :
    (Phase3Transition L K s t).1.role = .mcr := by
  have h_ne_clock : s.role ≠ .clock := by simp [hs]
  have h_ne_main : s.role ≠ .main := by simp [hs]
  simp only [Phase3Transition, h_ne_clock, h_ne_main, false_and, ↓reduceIte, and_false]
  exact hs

private lemma Phase3Transition_second_mcr (s t : AgentState L K) (ht : t.role = .mcr) :
    (Phase3Transition L K s t).2.role = .mcr := by
  have h_ne_clock : t.role ≠ .clock := by simp [ht]
  have h_ne_main : t.role ≠ .main := by simp [ht]
  simp only [Phase3Transition, h_ne_clock, h_ne_main, false_and, ↓reduceIte, and_false]
  exact ht

private lemma Phase4Transition_first_mcr (s t : AgentState L K) (hs : s.role = .mcr) :
    (Phase4Transition L K s t).1.role = .mcr := by
  unfold Phase4Transition
  simp only
  split <;> simp [advancePhase_role, hs]

private lemma Phase4Transition_second_mcr (s t : AgentState L K) (ht : t.role = .mcr) :
    (Phase4Transition L K s t).2.role = .mcr := by
  unfold Phase4Transition
  simp only
  split <;> simp [advancePhase_role, ht]

private lemma Phase5Transition_first_mcr (s t : AgentState L K) (hs : s.role = .mcr) :
    (Phase5Transition L K s t).1.role = .mcr := by
  unfold Phase5Transition
  have h1 : ¬(s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero)) := by simp [hs]
  have h2 : ¬(t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero)) := by simp [hs]
  simp [h1, h2, hs]

private lemma Phase5Transition_second_mcr (s t : AgentState L K) (ht : t.role = .mcr) :
    (Phase5Transition L K s t).2.role = .mcr := by
  unfold Phase5Transition
  have h1 : ¬(s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero)) := by simp [ht]
  have h2 : ¬(t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero)) := by simp [ht]
  simp [h1, h2, ht]

private lemma Phase6Transition_first_mcr (s t : AgentState L K) (hs : s.role = .mcr) :
    (Phase6Transition L K s t).1.role = .mcr := by
  unfold Phase6Transition
  have h1 : ¬(s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero)) := by simp [hs]
  have h2 : ¬(t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero)) := by simp [hs]
  simp [h1, h2, hs]

private lemma Phase6Transition_second_mcr (s t : AgentState L K) (ht : t.role = .mcr) :
    (Phase6Transition L K s t).2.role = .mcr := by
  unfold Phase6Transition
  have h1 : ¬(s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero)) := by simp [ht]
  have h2 : ¬(t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero)) := by simp [ht]
  simp [h1, h2, ht]

private lemma Phase7Transition_first_mcr (s t : AgentState L K) (hs : s.role = .mcr) :
    (Phase7Transition L K s t).1.role = .mcr := by
  unfold Phase7Transition
  have : ¬(s.role = .main ∧ t.role = .main) := by simp [hs]
  simp [this, hs]

private lemma Phase7Transition_second_mcr (s t : AgentState L K) (ht : t.role = .mcr) :
    (Phase7Transition L K s t).2.role = .mcr := by
  unfold Phase7Transition
  have : ¬(s.role = .main ∧ t.role = .main) := by simp [ht]
  simp [this, ht]

private lemma Phase8Transition_first_mcr (s t : AgentState L K) (hs : s.role = .mcr) :
    (Phase8Transition L K s t).1.role = .mcr := by
  unfold Phase8Transition
  have : ¬(s.role = .main ∧ t.role = .main) := by simp [hs]
  simp [this, hs]

private lemma Phase8Transition_second_mcr (s t : AgentState L K) (ht : t.role = .mcr) :
    (Phase8Transition L K s t).2.role = .mcr := by
  unfold Phase8Transition
  have : ¬(s.role = .main ∧ t.role = .main) := by simp [ht]
  simp [this, ht]

private lemma Phase9Transition_first_mcr (s t : AgentState L K) (hs : s.role = .mcr) :
    (Phase9Transition L K s t).1.role = .mcr := by
  unfold Phase9Transition
  exact Phase2Transition_first_mcr (L := L) (K := K) s t hs

private lemma Phase9Transition_second_mcr (s t : AgentState L K) (ht : t.role = .mcr) :
    (Phase9Transition L K s t).2.role = .mcr := by
  unfold Phase9Transition
  exact Phase2Transition_second_mcr (L := L) (K := K) s t ht

private lemma Phase10Transition_first_mcr (s t : AgentState L K) (hs : s.role = .mcr) :
    (Phase10Transition L K s t).1.role = .mcr := by
  simp only [Phase10Transition]; split_ifs <;> simp_all

private lemma Phase10Transition_second_mcr (s t : AgentState L K) (ht : t.role = .mcr) :
    (Phase10Transition L K s t).2.role = .mcr := by
  simp only [Phase10Transition]; split_ifs <;> simp_all

/-- The phase dispatch (phases 1-10 + default) preserves MCR on the first component. -/
private lemma phaseDispatch_first_mcr (s' t' : AgentState L K)
    (hs' : s'.role = .mcr) (hs'_phase : s'.phase.val ≠ 0) :
    (match s'.phase with
     | ⟨0, _⟩ => Phase0Transition L K s' t'
     | ⟨1, _⟩ => Phase1Transition L K s' t'
     | ⟨2, _⟩ => Phase2Transition L K s' t'
     | ⟨3, _⟩ => Phase3Transition L K s' t'
     | ⟨4, _⟩ => Phase4Transition L K s' t'
     | ⟨5, _⟩ => Phase5Transition L K s' t'
     | ⟨6, _⟩ => Phase6Transition L K s' t'
     | ⟨7, _⟩ => Phase7Transition L K s' t'
     | ⟨8, _⟩ => Phase8Transition L K s' t'
     | ⟨9, _⟩ => Phase9Transition L K s' t'
     | ⟨10, _⟩ => Phase10Transition L K s' t'
     | _ => (s', t')).1.role = .mcr := by
  -- The match dispatches on s'.phase : Fin 11. Split it.
  split
  case h_1 h => exact absurd (show s'.phase.val = 0 from by rw [h]) hs'_phase
  case h_2 => exact Phase1Transition_first_mcr (L := L) (K := K) s' t' hs'
  case h_3 => exact Phase2Transition_first_mcr (L := L) (K := K) s' t' hs'
  case h_4 => exact Phase3Transition_first_mcr (L := L) (K := K) s' t' hs'
  case h_5 => exact Phase4Transition_first_mcr (L := L) (K := K) s' t' hs'
  case h_6 => exact Phase5Transition_first_mcr (L := L) (K := K) s' t' hs'
  case h_7 => exact Phase6Transition_first_mcr (L := L) (K := K) s' t' hs'
  case h_8 => exact Phase7Transition_first_mcr (L := L) (K := K) s' t' hs'
  case h_9 => exact Phase8Transition_first_mcr (L := L) (K := K) s' t' hs'
  case h_10 => exact Phase9Transition_first_mcr (L := L) (K := K) s' t' hs'
  case h_11 => exact Phase10Transition_first_mcr (L := L) (K := K) s' t' hs'
  case h_12 => exact hs'  -- default case: (s', t').1.role = s'.role

/-- The phase dispatch (phases 1-10 + default) preserves MCR on the second component.
Note: dispatch is on `s'.phase`, but since `t.phase.val ≥ 1`, epidemic ensures
`s'.phase.val ≥ max(s, t) ≥ t ≥ 1`, so phase 0 is excluded. -/
private lemma phaseDispatch_second_mcr (s' t' : AgentState L K)
    (ht' : t'.role = .mcr) (hs'_phase : s'.phase.val ≠ 0) :
    (match s'.phase with
     | ⟨0, _⟩ => Phase0Transition L K s' t'
     | ⟨1, _⟩ => Phase1Transition L K s' t'
     | ⟨2, _⟩ => Phase2Transition L K s' t'
     | ⟨3, _⟩ => Phase3Transition L K s' t'
     | ⟨4, _⟩ => Phase4Transition L K s' t'
     | ⟨5, _⟩ => Phase5Transition L K s' t'
     | ⟨6, _⟩ => Phase6Transition L K s' t'
     | ⟨7, _⟩ => Phase7Transition L K s' t'
     | ⟨8, _⟩ => Phase8Transition L K s' t'
     | ⟨9, _⟩ => Phase9Transition L K s' t'
     | ⟨10, _⟩ => Phase10Transition L K s' t'
     | _ => (s', t')).2.role = .mcr := by
  split
  case h_1 h => exact absurd (show s'.phase.val = 0 from by rw [h]) hs'_phase
  case h_2 => exact Phase1Transition_second_mcr (L := L) (K := K) s' t' ht'
  case h_3 => exact Phase2Transition_second_mcr (L := L) (K := K) s' t' ht'
  case h_4 => exact Phase3Transition_second_mcr (L := L) (K := K) s' t' ht'
  case h_5 => exact Phase4Transition_second_mcr (L := L) (K := K) s' t' ht'
  case h_6 => exact Phase5Transition_second_mcr (L := L) (K := K) s' t' ht'
  case h_7 => exact Phase6Transition_second_mcr (L := L) (K := K) s' t' ht'
  case h_8 => exact Phase7Transition_second_mcr (L := L) (K := K) s' t' ht'
  case h_9 => exact Phase8Transition_second_mcr (L := L) (K := K) s' t' ht'
  case h_10 => exact Phase9Transition_second_mcr (L := L) (K := K) s' t' ht'
  case h_11 => exact Phase10Transition_second_mcr (L := L) (K := K) s' t' ht'
  case h_12 => exact ht'  -- default case: (s', t').2.role = t'.role

/-- If `s.role = .mcr` and `s.phase ≠ 0`, the first output of `Transition` is MCR. -/
lemma Transition_first_mcr_of_high_phase (s t : AgentState L K)
    (hs : s.role = .mcr) (hs_phase : s.phase.val ≠ 0) :
    (Transition L K s t).1.role = .mcr := by
  -- After epidemic update, s' still has MCR role and phase ≥ s.phase ≥ 1
  have hs'_mcr := phaseEpidemicUpdate_first_mcr (L := L) (K := K) s t hs
  have hs'_phase_ge := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
  have hs'_phase : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 0 := by
    have : s.phase.val ≤ max s.phase.val t.phase.val := le_max_left _ _
    omega
  -- Unfold and simplify
  simp only [Transition, finishPhase10Entry_role_eq]
  exact phaseDispatch_first_mcr (L := L) (K := K) _ _ hs'_mcr hs'_phase

/-- If `t.role = .mcr` and `t.phase ≠ 0`, the second output of `Transition` is MCR. -/
lemma Transition_second_mcr_of_high_phase (s t : AgentState L K)
    (ht : t.role = .mcr) (ht_phase : t.phase.val ≠ 0) :
    (Transition L K s t).2.role = .mcr := by
  -- After epidemic update, t' still has MCR role
  have ht'_mcr := phaseEpidemicUpdate_second_mcr (L := L) (K := K) s t ht
  -- s'.phase ≥ max(s,t) ≥ t ≥ 1, so dispatch skips phase 0
  have hs'_phase_ge := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
  have hs'_phase : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 0 := by
    have : t.phase.val ≤ max s.phase.val t.phase.val := le_max_right _ _
    omega
  simp only [Transition, finishPhase10Entry_role_eq]
  exact phaseDispatch_second_mcr (L := L) (K := K) _ _ ht'_mcr hs'_phase

/-! ### Milestone progress: extracting mcrCount from hypotheses -/

/-- From the milestone hypotheses, extract that mcrCount c = n - i, c.card = n,
and all MCR agents are at phase 0. -/
private lemma phase0_milestone_mcrCount_eq (n : ℕ) (hn : 2 ≤ n) (i : Fin (n - 1))
    (c : Config (AgentState L K))
    (h_prev : ∀ j < i, phase0Milestone n ⟨j.val, by omega⟩ c)
    (h_not_reached : ¬ phase0Milestone n ⟨i.val, by omega⟩ c) :
    c.card = n ∧ mcrCount c = n - i.val ∧
    (∀ a ∈ c, a.role = .mcr → a.phase.val = 0) := by
  -- From h_not_reached: ¬(mcrCount c ≤ threshold ∨ c.card ≠ n ∨ ∃ a ∈ c, ...)
  have h1 : ¬ mcrCount c ≤ mcrThreshold n ⟨i.val, by omega⟩ := by
    intro h; exact h_not_reached (Or.inl h)
  have h_card : c.card = n := by
    by_contra h; exact h_not_reached (Or.inr (Or.inl h))
  have h_no_high : ¬ ∃ a ∈ c, a.role = .mcr ∧ a.phase.val ≠ 0 := by
    intro h; exact h_not_reached (Or.inr (Or.inr h))
  have h_mcr_gt := not_le.mp h1
  have h_all_phase0' : ∀ a ∈ c, a.role = .mcr → a.phase.val = 0 := by
    intro a ha hrole
    by_contra h_phase
    exact h_no_high ⟨a, ha, hrole, h_phase⟩
  -- mcrThreshold n i = n - 1 - i, so mcrCount c ≥ n - i
  have h_mcr_ge : n - i.val ≤ mcrCount c := by
    unfold mcrThreshold at h_mcr_gt
    have : (⟨i.val, by omega⟩ : Fin n).val = i.val := rfl
    rw [this] at h_mcr_gt
    omega
  -- mcrCount c ≤ n (since mcrCount ≤ card = n)
  have h_mcr_le_n : mcrCount c ≤ n := by
    have : mcrCount c ≤ c.card := by
      unfold mcrCount; exact Multiset.card_le_card (Multiset.filter_le _ _)
    omega
  -- For i = 0: mcrCount c ≥ n and mcrCount c ≤ n, so mcrCount c = n
  -- For i > 0: from h_prev at j = i-1, get mcrCount c ≤ mcrThreshold n (i-1) = n - i
  by_cases hi : i.val = 0
  · exact ⟨h_card, by omega, h_all_phase0'⟩
  · have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi
    have hj : (⟨i.val - 1, by omega⟩ : Fin (n - 1)) < i := by
      simp [Fin.lt_def]; omega
    have h_prev_j := h_prev ⟨i.val - 1, by omega⟩ hj
    simp only [phase0Milestone] at h_prev_j
    rcases h_prev_j with h_mcr_prev | h_card_prev | h_phase_prev
    · -- h_mcr_prev : mcrCount c ≤ mcrThreshold n ⟨i.val - 1, _⟩
      have h_threshold : mcrThreshold n ⟨i.val - 1, by omega⟩ = n - 1 - (i.val - 1) := by
        unfold mcrThreshold
        have : (⟨i.val - 1, by omega⟩ : Fin n).val = i.val - 1 := rfl
        rw [this]
      rw [h_threshold] at h_mcr_prev
      exact ⟨h_card, by omega, h_all_phase0'⟩
    · exact absurd h_card h_card_prev
    · -- Previous milestone reached because some MCR agent is not at phase 0
      -- But h_not_reached says ¬(∃ a ∈ c, a.role = .mcr ∧ a.phase.val ≠ 0)
      -- These are contradictory
      exact absurd h_phase_prev h_no_high

/-- The set of configs where mcrCount decreases is contained in the milestone target set. -/
private lemma mcrCount_decrease_subset_milestone (n : ℕ) (i : Fin (n - 1))
    (c : Config (AgentState L K))
    (h_mcr_eq : mcrCount c = n - i.val) :
    {c' : Config (AgentState L K) | mcrCount c' < mcrCount c} ⊆
    {c' | phase0Milestone n ⟨i.val, by omega⟩ c'} := by
  intro c' hc'
  simp only [Set.mem_setOf_eq] at hc' ⊢
  left
  unfold mcrThreshold
  simp
  rw [h_mcr_eq] at hc'
  omega


-- Helper: sum of state counts over MCR filter = mcrCount
private lemma sum_count_mcr_filter (c : Config (AgentState L K)) :
    ∑ s ∈ Finset.univ.filter (fun s : AgentState L K => s.role = .mcr),
      c.count s = mcrCount c := by
  set F := Finset.univ.filter (fun s : AgentState L K => s.role = .mcr)
  set cm := Multiset.filter (fun a : AgentState L K => a.role = .mcr) c
  have hcount : ∀ s ∈ F, c.count s = Multiset.count s cm := fun s hs => by
    show Multiset.count s c = Multiset.count s cm
    have hs_mcr : (fun a : AgentState L K => a.role = .mcr) s :=
      (Finset.mem_filter.mp hs).2
    simp only [cm, Multiset.count_filter, hs_mcr, ite_true]
  calc ∑ s ∈ F, c.count s
      = ∑ s ∈ F, Multiset.count s cm := Finset.sum_congr rfl hcount
    _ = Multiset.card cm :=
        Multiset.sum_count_eq_card (s := F) (m := cm)
          (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a, (Multiset.mem_filter.mp ha).2⟩)
    _ = mcrCount c := rfl

-- Helper: for MCR s₁, sum of interactionCount over MCR = count(s₁) * (M-1)
private lemma sum_interactionCount_mcr_right (c : Config (AgentState L K))
    (s₁ : AgentState L K) (hs₁ : s₁.role = .mcr) :
    ∑ s₂ ∈ Finset.univ.filter (fun s : AgentState L K => s.role = .mcr),
      c.interactionCount s₁ s₂ = c.count s₁ * (mcrCount c - 1) := by
  set F := Finset.univ.filter (fun s : AgentState L K => s.role = .mcr)
  by_cases hzero : c.count s₁ = 0
  · have : ∀ s₂ ∈ F, c.interactionCount s₁ s₂ = 0 := fun s₂ _ => by
      unfold Config.interactionCount Config.count
      unfold Config.count at hzero
      split_ifs with h
      · subst h; simp [hzero]
      · simp [hzero]
    rw [Finset.sum_eq_zero this]; simp [hzero]
  · have hfactor : ∀ s₂ ∈ F, c.interactionCount s₁ s₂ =
        c.count s₁ * if s₁ = s₂ then c.count s₁ - 1 else c.count s₂ := by
      intro s₂ _; unfold Config.interactionCount
      by_cases h : s₁ = s₂ <;> simp [h]
    rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]; congr 1
    have hs₁F : s₁ ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ s₁, hs₁⟩
    set f : AgentState L K → ℕ :=
      fun s₂ => if s₁ = s₂ then c.count s₁ - 1 else c.count s₂
    have hf_s₁ : f s₁ = c.count s₁ - 1 := if_pos rfl
    have hf_ne : ∀ s₂ ∈ F.erase s₁, f s₂ = c.count s₂ :=
      fun s₂ hs₂ => if_neg (Finset.ne_of_mem_erase hs₂).symm
    calc ∑ s₂ ∈ F, f s₂
        = f s₁ + ∑ s₂ ∈ F.erase s₁, f s₂ := (Finset.add_sum_erase F f hs₁F).symm
      _ = (c.count s₁ - 1) + ∑ s₂ ∈ F.erase s₁, c.count s₂ := by
          rw [hf_s₁, Finset.sum_congr rfl hf_ne]
      _ = mcrCount c - 1 := by
          have hse : c.count s₁ + ∑ s₂ ∈ F.erase s₁, c.count s₂ = mcrCount c := by
            rw [Finset.add_sum_erase F (fun s => c.count s) hs₁F]
            exact sum_count_mcr_filter c
          have hcount_pos : 0 < c.count s₁ := Nat.pos_of_ne_zero hzero
          omega

-- Helper: double sum of interactionCount over MCR*MCR = M*(M-1)
private lemma sum_interactionCount_mcr (c : Config (AgentState L K)) :
    ∑ s₁ ∈ Finset.univ.filter (fun s : AgentState L K => s.role = .mcr),
      ∑ s₂ ∈ Finset.univ.filter (fun s : AgentState L K => s.role = .mcr),
        c.interactionCount s₁ s₂ = mcrCount c * (mcrCount c - 1) := by
  rw [Finset.sum_congr rfl fun s₁ hs₁ =>
    sum_interactionCount_mcr_right c s₁ (Finset.mem_filter.mp hs₁).2,
    ← Finset.sum_mul, sum_count_mcr_filter]

-- Helper: positive interactionCount implies Applicable
private lemma applicable_of_pos_iCount (c : Config (AgentState L K))
    (s₁ s₂ : AgentState L K) (h : 0 < c.interactionCount s₁ s₂) :
    Protocol.Applicable c s₁ s₂ := by
  show {s₁, s₂} ≤ c; rw [Multiset.le_iff_count]; intro a
  simp only [Config.interactionCount, Config.count] at h
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  by_cases heq : s₁ = s₂
  · subst heq; simp only [ite_true] at h
    have : 2 ≤ Multiset.count s₁ c := by
      by_contra h_lt; push_neg at h_lt
      have : Multiset.count s₁ c ≤ 1 := by omega
      have : Multiset.count s₁ c * (Multiset.count s₁ c - 1) = 0 := by
        rcases Nat.eq_zero_or_pos (Multiset.count s₁ c) with h0 | h0
        · simp [h0]
        · have : Multiset.count s₁ c = 1 := by omega
          simp [this]
      omega
    by_cases ha : a = s₁ <;> simp_all <;> omega
  · simp only [heq, ite_false] at h
    have hc1 : 0 < Multiset.count s₁ c := pos_of_mul_pos_left h (Nat.zero_le _)
    have hc2 : 0 < Multiset.count s₂ c := pos_of_mul_pos_right h (Nat.zero_le _)
    by_cases ha1 : a = s₁ <;> by_cases ha2 : a = s₂ <;> simp_all <;> omega


set_option maxHeartbeats 800000 in
private lemma interactionPMF_toMeasure_mcr_phase0_ge
    (c : Config (AgentState L K)) (hc : 2 ≤ c.card) (M : ℕ)
    (h_M : mcrCount c = M) (h_phase0 : ∀ a ∈ c, a.role = .mcr → a.phase.val = 0) :
    (c.interactionPMF hc).toMeasure
      {p : AgentState L K × AgentState L K |
        p.1.role = .mcr ∧ p.1.phase.val = 0 ∧ p.2.role = .mcr ∧ p.2.phase.val = 0 ∧
        Protocol.Applicable c p.1 p.2} ≥
    ENNReal.ofReal ((M * (M - 1) : ℝ) / (c.card * (c.card - 1) : ℝ)) := by
  -- M=0 or M=1: RHS ≤ 0, so ofReal gives 0
  by_cases hM : M ≤ 1
  · have hM0 : (M * (M - 1) : ℝ) = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hM with rfl | rfl <;> simp
    simp [hM0]
  -- M >= 2: counting argument
  push_neg at hM
  set target := {p : AgentState L K × AgentState L K |
    p.1.role = .mcr ∧ p.1.phase.val = 0 ∧ p.2.role = .mcr ∧ p.2.phase.val = 0 ∧
    Protocol.Applicable c p.1 p.2}
  set F := Finset.univ.filter (fun s : AgentState L K => s.role = .mcr)
  -- (F ×ˢ F) ∩ PMF.support ⊆ target
  have h_sub : (↑(F ×ˢ F) : Set _) ∩ (c.interactionPMF hc).support ⊆ target := by
    intro ⟨s₁, s₂⟩ ⟨h_mem, h_supp⟩
    have hs₁_mcr : s₁.role = .mcr := (Finset.mem_filter.mp (Finset.mem_product.mp h_mem).1).2
    have hs₂_mcr : s₂.role = .mcr := (Finset.mem_filter.mp (Finset.mem_product.mp h_mem).2).2
    rw [PMF.mem_support_iff] at h_supp
    have h_app : Protocol.Applicable c s₁ s₂ := by
      apply applicable_of_pos_iCount
      by_contra h0; exact h_supp (show c.interactionProb s₁ s₂ = 0 by
        simp [Config.interactionProb, show c.interactionCount s₁ s₂ = 0 by omega])
    exact ⟨hs₁_mcr, h_phase0 s₁ (Multiset.mem_of_le h_app (Multiset.mem_cons_self _ _)) hs₁_mcr,
      hs₂_mcr, h_phase0 s₂ (Multiset.mem_of_le h_app
        (Multiset.mem_cons.mpr (Or.inr (Multiset.mem_singleton_self _)))) hs₂_mcr, h_app⟩
  have h_le := (c.interactionPMF hc).toMeasure_mono
    (DiscreteMeasurableSpace.forall_measurableSet _) h_sub
  suffices h_val : (c.interactionPMF hc).toMeasure (↑(F ×ˢ F)) ≥
      ENNReal.ofReal ((↑M * (↑M - 1)) / (↑c.card * (↑c.card - 1))) from
    le_trans h_val h_le
  rw [PMF.toMeasure_apply_finset]
  simp_rw [show ∀ p : AgentState L K × AgentState L K,
    (c.interactionPMF hc) p = (c.interactionCount p.1 p.2 : ENNReal) / c.totalPairs
    from fun _ => rfl, div_eq_mul_inv, ← Finset.sum_mul]
  conv_lhs => arg 1; rw [Finset.sum_product' F F
    (fun s₁ s₂ => (c.interactionCount s₁ s₂ : ENNReal))]
  have h_comb := sum_interactionCount_mcr (L := L) (K := K) c
  rw [h_M] at h_comb
  rw [show ∑ s₁ ∈ F, ∑ s₂ ∈ F, (c.interactionCount s₁ s₂ : ENNReal) =
    ((M * (M - 1) : ℕ) : ENNReal) from by exact_mod_cast h_comb,
    ← div_eq_mul_inv]
  have h1 : 1 ≤ c.card := by omega
  have h2 : 1 ≤ M := by omega
  have hprod_pos : (0 : ℝ) < ↑c.card * (↑c.card - 1) := by
    apply mul_pos
    · exact Nat.cast_pos.mpr (by omega)
    · exact sub_pos.mpr (by exact_mod_cast (show 1 < c.card by omega))
  show ↑(M * (M - 1)) / ↑c.totalPairs ≥
    ENNReal.ofReal ((↑M * (↑M - 1) : ℝ) / (↑c.card * (↑c.card - 1)))
  have hM_cast : (↑M * (↑M - 1) : ℝ) = ((M * (M - 1) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub h2]; ring
  have hcard_cast : ↑c.card * (↑c.card - 1 : ℝ) = ((c.card * (c.card - 1) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub h1]; ring
  rw [ENNReal.ofReal_div_of_pos hprod_pos, hM_cast, hcard_cast,
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    show (c.card * (c.card - 1) : ℕ) = c.totalPairs from rfl]



lemma phase0_mcrCount_decrease_prob (c : Config (AgentState L K)) (n M : ℕ)
    (h_card : c.card = n) (h_M : mcrCount c = M) (hM2 : 2 ≤ M)
    (h_phase0 : ∀ a ∈ c, a.role = .mcr → a.phase.val = 0) :
    ((NonuniformMajority L K).stepDistOrSelf c).toMeasure {c' | mcrCount c' < mcrCount c} ≥
      ENNReal.ofReal ((M * (M - 1) : ℝ) / (n * (n - 1) : ℝ)) := by
  have hM_le_card : M ≤ c.card := by
    have : mcrCount c ≤ c.card := by
      unfold mcrCount; exact Multiset.card_le_card (Multiset.filter_le _ _)
    omega
  have hn2 : 2 ≤ n := by omega
  have hc2 : 2 ≤ c.card := by omega
  -- Define good pairs: both agents are MCR at phase 0 AND applicable
  set good : Set (AgentState L K × AgentState L K) :=
    {p | p.1.role = .mcr ∧ p.1.phase.val = 0 ∧ p.2.role = .mcr ∧ p.2.phase.val = 0 ∧
         Protocol.Applicable c p.1 p.2}
  -- Step 1: every good pair's scheduledStep decreases mcrCount
  have hgood : ∀ pair ∈ good, (NonuniformMajority L K).scheduledStep c pair ∈
      {c' | mcrCount c' < mcrCount c} := by
    intro ⟨s, t⟩ ⟨hs_mcr, hs_phase, ht_mcr, ht_phase, happ⟩
    simp only [Set.mem_setOf_eq]
    unfold Protocol.scheduledStep Protocol.stepOrSelf
    rw [if_pos happ]
    exact mcrCount_config_decrease_of_phase0_mcr_pair c s t happ hs_phase ht_phase hs_mcr ht_mcr
  -- Step 2: chain stepDistOrSelf_toMeasure_ge with interactionPMF bound
  calc ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | mcrCount c' < mcrCount c}
      ≥ (c.interactionPMF hc2).toMeasure good :=
        stepDistOrSelf_toMeasure_ge c hc2 _ good hgood
    _ ≥ ENNReal.ofReal ((M * (M - 1) : ℝ) / (c.card * (c.card - 1) : ℝ)) :=
        interactionPMF_toMeasure_mcr_phase0_ge c hc2 M h_M h_phase0
    _ = ENNReal.ofReal ((M * (M - 1) : ℝ) / (n * (n - 1) : ℝ)) := by
        congr 1; congr 1; rw [h_card]

noncomputable def phase0MilestonePhase (n : ℕ) (hn : 2 ≤ n) :
    MilestonePhase (NonuniformMajority L K) where
  k := n - 1
  milestone i := phase0Milestone n ⟨i.val, by omega⟩
  p := phase0MilestoneProb n
  hp_pos i := by
    -- M = n - i.val ≥ 2 since i.val ≤ n-2
    have hM_ge2 : 2 ≤ mcrThreshold n ⟨i.val, by omega⟩ + 1 := by
      unfold mcrThreshold
      have : (⟨i.val, by omega⟩ : Fin n).val = i.val := rfl
      rw [this]; omega
    have hM_le : mcrThreshold n ⟨i.val, by omega⟩ + 1 ≤ n := by
      unfold mcrThreshold
      have : (⟨i.val, by omega⟩ : Fin n).val = i.val := rfl
      rw [this]; omega
    set M := mcrThreshold n ⟨i.val, by omega⟩ + 1
    show 0 < (M : ℝ) * ((M : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1))
    have hM2_real : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge2
    have hn2_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact div_pos (mul_pos (by linarith) (by linarith)) (mul_pos (by linarith) (by linarith))
  hp_le_one i := by
    have hM_le : mcrThreshold n ⟨i.val, by omega⟩ + 1 ≤ n := by
      unfold mcrThreshold
      have : (⟨i.val, by omega⟩ : Fin n).val = i.val := rfl
      rw [this]; omega
    have hM_ge1 : 1 ≤ mcrThreshold n ⟨i.val, by omega⟩ + 1 := by omega
    set M := mcrThreshold n ⟨i.val, by omega⟩ + 1
    show (M : ℝ) * ((M : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1
    have hM_le_real : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hM_le
    have hM_sub_le : (M : ℝ) - 1 ≤ (n : ℝ) - 1 := by linarith
    have hM_sub_nonneg : (0 : ℝ) ≤ (M : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge1
      linarith
    have hn_sub_nonneg : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      linarith
    exact div_le_one_of_le₀
      (mul_le_mul hM_le_real hM_sub_le hM_sub_nonneg (by linarith))
      (mul_nonneg (Nat.cast_nonneg _) hn_sub_nonneg)
  milestone_monotone i c c' h_mono h_supp := by
    show phase0Milestone n ⟨i.val, by omega⟩ c'
    have h_mono' : phase0Milestone n ⟨i.val, by omega⟩ c := h_mono
    unfold phase0Milestone at h_mono' ⊢
    rcases h_mono' with h_mcr | h_card | h_phase
    · left
      unfold Protocol.stepDistOrSelf at h_supp
      split_ifs at h_supp with h_size
      · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ h_supp
        subst heq
        unfold Protocol.scheduledStep Protocol.stepOrSelf at *
        split_ifs at * with h_app
        · have h_sub : {r₁, r₂} ≤ c := by
            unfold Protocol.Applicable at h_app; exact h_app
          have h_restore : c - {r₁, r₂} + {r₁, r₂} = c := Multiset.sub_add_cancel h_sub
          calc mcrCount (c - {r₁, r₂} + {(Transition L K r₁ r₂).1,
                  (Transition L K r₁ r₂).2})
              = mcrCount (c - {r₁, r₂}) + mcrCount {(Transition L K r₁ r₂).1,
                  (Transition L K r₁ r₂).2} := mcrCount_add _ _
            _ ≤ mcrCount (c - {r₁, r₂}) + mcrCount {r₁, r₂} :=
                Nat.add_le_add_left (Transition_mcrCount_le (L := L) (K := K) r₁ r₂) _
            _ = mcrCount (c - {r₁, r₂} + {r₁, r₂}) := (mcrCount_add _ _).symm
            _ = mcrCount c := by rw [h_restore]
            _ ≤ mcrThreshold n ⟨i.val, by omega⟩ := h_mcr
        · exact h_mcr
      · simp at h_supp; subst h_supp; exact h_mcr
    · right; left
      exact (Protocol.stepDistOrSelf_support_card_eq _ _ _ h_supp).symm ▸ h_card
    · -- An MCR agent at phase ≠ 0 existed in c. It persists in c'.
      right; right
      obtain ⟨a, ha_mem, ha_mcr, ha_phase⟩ := h_phase
      unfold Protocol.stepDistOrSelf at h_supp
      split_ifs at h_supp with h_size
      · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ h_supp
        subst heq
        unfold Protocol.scheduledStep Protocol.stepOrSelf at *
        split_ifs at * with h_app
        · have h_sub : ({r₁, r₂} : Config (AgentState L K)) ≤ c := by
            unfold Protocol.Applicable at h_app; exact h_app
          -- Check if a is in the interacting pair
          by_cases ha_r1 : a = r₁
          · -- a = r₁: output.1 is MCR at phase > 0
            subst ha_r1
            refine ⟨(Transition L K a r₂).1, ?_, ?_, ?_⟩
            · exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_cons_self _ _))
            · exact Transition_first_mcr_of_high_phase a r₂ ha_mcr ha_phase
            · -- phase ≥ a.phase > 0
              have h_mono := Transition_phase_monotone (L := L) (K := K) a r₂
              have h_ge : a.phase.val ≤ (Transition L K a r₂).1.phase.val := h_mono.1
              omega
          · by_cases ha_r2 : a = r₂
            · -- a = r₂: output.2 is MCR at phase > 0
              subst ha_r2
              refine ⟨(Transition L K r₁ a).2, ?_, ?_, ?_⟩
              · exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_cons.mpr
                  (Or.inr (Multiset.mem_singleton.mpr rfl))))
              · exact Transition_second_mcr_of_high_phase r₁ a ha_mcr ha_phase
              · have h_mono := Transition_phase_monotone (L := L) (K := K) r₁ a
                have h_ge : a.phase.val ≤ (Transition L K r₁ a).2.phase.val := h_mono.2
                omega
            · -- a ∉ {r₁, r₂}: a persists unchanged in c'
              have ha_not_in : a ∉ ({r₁, r₂} : Multiset (AgentState L K)) := by
                simp [Multiset.mem_cons, Multiset.mem_singleton]
                exact ⟨ha_r1, ha_r2⟩
              refine ⟨a, ?_, ha_mcr, ha_phase⟩
              apply Multiset.mem_add.mpr; left
              -- a ∈ c and a ∉ {r₁, r₂} implies a ∈ c - {r₁, r₂}
              -- a ∈ c, a ≠ r₁, a ≠ r₂ ⟹ a ∈ c - {r₁, r₂}
              -- Since c = (c - {r₁, r₂}) + {r₁, r₂}, and a ∈ c, a ∉ {r₁, r₂},
              -- a must be in c - {r₁, r₂}.
              have h_restore : c - {r₁, r₂} + {r₁, r₂} = c := Multiset.sub_add_cancel h_sub
              have ha_in_sum : a ∈ c - {r₁, r₂} + ({r₁, r₂} : Multiset _) := by
                rw [h_restore]; exact ha_mem
              rcases Multiset.mem_add.mp ha_in_sum with h | h
              · exact h
              · exact absurd h ha_not_in
        · exact ⟨a, ha_mem, ha_mcr, ha_phase⟩
      · simp [PMF.support_pure] at h_supp; rw [h_supp]
        exact ⟨a, ha_mem, ha_mcr, ha_phase⟩
  progress i c h_prev h_not_reached := by
    -- Extract: c.card = n, mcrCount c = n - i, and all MCR at phase 0
    have ⟨h_card, h_mcr_eq, h_all_phase0⟩ :=
      phase0_milestone_mcrCount_eq n hn i c h_prev h_not_reached
    -- The milestone target contains all configs with mcrCount < mcrCount c
    have h_subset := mcrCount_decrease_subset_milestone n i c h_mcr_eq
    -- M = mcrThreshold n ⟨i.val, _⟩ + 1 = n - i.val = mcrCount c
    have h_fin_val : (⟨i.val, by omega⟩ : Fin n).val = i.val := rfl
    have h_M : mcrCount c = mcrThreshold n ⟨i.val, by omega⟩ + 1 := by
      rw [h_mcr_eq]; unfold mcrThreshold; rw [h_fin_val]; omega
    -- M ≥ 2 since i : Fin (n-1), so i.val ≤ n-2, M = n - i ≥ 2
    have hM2 : 2 ≤ mcrThreshold n ⟨i.val, by omega⟩ + 1 := by
      unfold mcrThreshold; rw [h_fin_val]
      have : i.val < n - 1 := i.isLt
      omega
    calc ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' | phase0Milestone n ⟨i.val, by omega⟩ c'}
        ≥ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' | mcrCount c' < mcrCount c} :=
          MeasureTheory.measure_mono h_subset
      _ ≥ ENNReal.ofReal (phase0MilestoneProb n i) := by
          have hbound := phase0_mcrCount_decrease_prob (L := L) (K := K)
            c n (mcrThreshold n ⟨i.val, by omega⟩ + 1) h_card h_M hM2 h_all_phase0
          exact hbound

@[simp] lemma phase0MilestonePhase_k (n : ℕ) (hn : 2 ≤ n) :
    (phase0MilestonePhase (L := L) (K := K) n hn).k = n - 1 := rfl

@[simp] lemma phase0MilestonePhase_p (n : ℕ) (hn : 2 ≤ n) (i : Fin (n - 1)) :
    (phase0MilestonePhase (L := L) (K := K) n hn).p i =
      phase0MilestoneProb n i := rfl

end ExactMajority
