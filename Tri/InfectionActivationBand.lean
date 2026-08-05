/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionActivation
import Tri.BandReturn

/-!
# Uniform activation bands for infection-initiated Tri

The global activation counter cannot use a positive active-count floor at
unreachable states. This guarded kernel advances the counter artificially below
the stage lower boundary, making the rectangular floor genuinely uniform.
-/

namespace Tri

open scoped ENNReal

/-- The lower guard and activation target of one finite activation stage. -/
def InfectionActivationBoundary
    {n : ℕ} (aLo target : ℕ) (s : InfectionState n) : Prop :=
  s.1.active < aLo ∨ target ≤ s.1.active

instance infectionActivationBoundaryDecidable
    {n : ℕ} (aLo target : ℕ) :
    DecidablePred (InfectionActivationBoundary (n := n) aLo target) := by
  intro s
  unfold InfectionActivationBoundary
  infer_instance

/-- Physical infection chain frozen at the stage guard or target. -/
noncomputable def infectionActivationBandStop
    (n : ℕ) (h3 : 3 ≤ n) (aLo target : ℕ) :
    InfectionState n → PMF (InfectionState n) :=
  freeze (InfectionActivationBoundary aLo target)
    (infectionStateStep n h3)

/-- Activation counter guarded below a stage's active-count floor. -/
noncomputable def infectionActivationBandCount
    (n : ℕ) (h3 : 3 ≤ n) (aLo target : ℕ) :
    InfectionState n × ℕ → PMF (InfectionState n × ℕ) := fun q =>
  if q.1.1.active < aLo then
    PMF.pure (q.1, q.2 + 1)
  else
    infectionActivationCount n h3 target q

/-- Forgetting the activation counter gives the physical two-boundary stage
chain. -/
theorem infectionActivationBandCount_map_fst
    (n : ℕ) (h3 : 3 ≤ n) (aLo target : ℕ)
    (q : InfectionState n × ℕ) :
    (infectionActivationBandCount n h3 aLo target q).map Prod.fst =
      infectionActivationBandStop n h3 aLo target q.1 := by
  by_cases hlo : q.1.1.active < aLo
  · rw [infectionActivationBandCount, if_pos hlo,
      infectionActivationBandStop,
      freeze_of_mem q.1 (Or.inl hlo)]
    exact PMF.pure_map Prod.fst (q.1, q.2 + 1)
  · rw [infectionActivationBandCount, if_neg hlo,
      infectionActivationCount_map_fst,
      infectionActivationStop, infectionActivationBandStop]
    by_cases htarget : target ≤ q.1.1.active
    · rw [freeze_of_mem q.1 htarget,
        freeze_of_mem q.1 (Or.inr htarget)]
    · rw [freeze_of_not_mem q.1 htarget,
        freeze_of_not_mem q.1 (by
          simpa [InfectionActivationBoundary] using And.intro hlo htarget)]

/-- The physical stopped iterate is the counter-forgetting pushforward of the
guarded counted iterate. -/
theorem iter_infectionActivationBandStop_eq_map
    (n : ℕ) (h3 : 3 ≤ n) (aLo target T : ℕ)
    (q : InfectionState n × ℕ) :
    iter (infectionActivationBandStop n h3 aLo target) T q.1 =
      (iter (infectionActivationBandCount n h3 aLo target) T q).map
        Prod.fst :=
  (iter_map_of_step_map
    (infectionActivationBandCount n h3 aLo target)
    (infectionActivationBandStop n h3 aLo target)
    Prod.fst
    (infectionActivationBandCount_map_fst n h3 aLo target)
    T q).symm

/-- Target-failure mass is unchanged by forgetting the activation counter. -/
theorem infectionActivationBandStop_failure_eq_count
    (n : ℕ) (h3 : 3 ≤ n) (aLo target T c0 : ℕ)
    (s0 : InfectionState n) :
    (∑' s, if target ≤ s.1.active then 0 else
        iter (infectionActivationBandStop n h3 aLo target)
          T s0 s) =
      ∑' q, if target ≤ q.1.1.active then 0 else
        iter (infectionActivationBandCount n h3 aLo target)
          T (s0, c0) q := by
  rw [iter_infectionActivationBandStop_eq_map
    n h3 aLo target T (s0, c0)]
  let V : InfectionState n → ℝ≥0∞ :=
    fun s => if target ≤ s.1.active then 0 else 1
  calc
    (∑' s, if target ≤ s.1.active then 0 else
        ((iter (infectionActivationBandCount n h3 aLo target)
          T (s0, c0)).map Prod.fst) s) =
        expect
          ((iter (infectionActivationBandCount n h3 aLo target)
            T (s0, c0)).map Prod.fst) V := by
          unfold expect V
          apply tsum_congr
          intro s
          by_cases hs : target ≤ s.1.active <;> simp [hs]
    _ = expect
          (iter (infectionActivationBandCount n h3 aLo target)
            T (s0, c0)) (fun q => V q.1) := by
          rw [expect_map]
    _ = ∑' q, if target ≤ q.1.1.active then 0 else
        iter (infectionActivationBandCount n h3 aLo target)
          T (s0, c0) q := by
          unfold expect V
          apply tsum_congr
          intro q
          by_cases hq : target ≤ q.1.1.active <;> simp [hq]

/-- A supported physical infection step cannot decrease active count. -/
theorem infectionStateStep_active_le_of_apply_ne_zero
    {n : ℕ} (h3 : 3 ≤ n)
    (s z : InfectionState n)
    (hsz : infectionStateStep n h3 s z ≠ 0) :
    s.1.active ≤ z.1.active := by
  unfold infectionStateStep at hsz
  rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hsz
  push Not at hsz
  obtain ⟨e, he⟩ := hsz
  split_ifs at he with hze
  · rw [hze]
    exact InfectionEvent.active_le_nextState_active s e
  · exact absurd rfl he

/-- Once an activation target is reached, every supported finite physical path
remains above it. -/
theorem infectionStateStep_iter_target
    {n target T : ℕ} (h3 : 3 ≤ n)
    (s z : InfectionState n)
    (hs : target ≤ s.1.active)
    (hz : iter (infectionStateStep n h3) T s z ≠ 0) :
    target ≤ z.1.active := by
  induction T generalizing s with
  | zero =>
      simp only [iter, PMF.pure_apply] at hz
      by_cases h : z = s
      · rwa [h]
      · simp [h] at hz
  | succ T ih =>
      rw [iter_succ, PMF.bind_apply] at hz
      by_contra hztarget
      apply hz
      rw [ENNReal.tsum_eq_zero]
      intro a
      by_cases hsa : infectionStateStep n h3 s a = 0
      · simp [hsa]
      · have hatarget : target ≤ a.1.active :=
          hs.trans
            (infectionStateStep_active_le_of_apply_ne_zero h3 s a hsa)
        have hiaz : iter (infectionStateStep n h3) T a z = 0 := by
          by_contra hne
          exact hztarget (ih a hatarget hne)
        simp [hiaz]

/-- Stopping at the lower guard and activation target can only increase
terminal target-failure mass. Target freezing has zero return error because
active count is monotone. -/
theorem infectionActivation_failure_le_bandStop
    (n : ℕ) (h3 : 3 ≤ n) (aLo target T : ℕ)
    (s0 : InfectionState n) :
    (∑' s, if target ≤ s.1.active then 0 else
        iter (infectionStateStep n h3) T s0 s) ≤
      ∑' s, if target ≤ s.1.active then 0 else
        iter (infectionActivationBandStop n h3 aLo target)
          T s0 s := by
  have hreturn :
      ∀ s : InfectionState n,
        InfectionActivationBoundary aLo target s →
        target ≤ s.1.active →
        ∀ U,
          (∑' z, if target ≤ z.1.active then 0 else
            iter (infectionStateStep n h3) U s z) ≤ 0 := by
    intro s _ hs U
    have hzero :
        (∑' z, if target ≤ z.1.active then 0 else
          iter (infectionStateStep n h3) U s z) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro z
      by_cases hz :
          iter (infectionStateStep n h3) U s z = 0
      · simp [hz]
      · have htarget :=
          infectionStateStep_iter_target h3 s z hs hz
        simp [htarget]
    rw [hzero]
  simpa [infectionActivationBandStop] using
    (failure_le_failure_freeze_add
      (B := InfectionActivationBoundary aLo target)
      (A := fun s : InfectionState n => target ≤ s.1.active)
      (K := infectionStateStep n h3) (δ := 0)
      hreturn T s0)

/-- The original physical chain's target failure is bounded by the guarded
counted stage failure. -/
theorem infectionActivation_failure_le_bandCount
    (n : ℕ) (h3 : 3 ≤ n) (aLo target T c0 : ℕ)
    (s0 : InfectionState n) :
    (∑' s, if target ≤ s.1.active then 0 else
        iter (infectionStateStep n h3) T s0 s) ≤
      ∑' q, if target ≤ q.1.1.active then 0 else
        iter (infectionActivationBandCount n h3 aLo target)
          T (s0, c0) q := by
  exact (infectionActivation_failure_le_bandStop
    n h3 aLo target T s0).trans_eq
      (infectionActivationBandStop_failure_eq_count
        n h3 aLo target T c0 s0)

/-- The rectangle floor gives a uniform contraction for the guarded stage
counter. -/
theorem infectionActivationBandCount_step
    (n : ℕ) (h3 : 3 ≤ n) (aLo target iLo : ℕ)
    (w p p' : ℝ≥0∞)
    (hw : w ≤ 1) (hp : p + p' = 1)
    (hiLo : iLo + target ≤ n + 1)
    (hpFloor : p ≤ infectionActivationFloor n aLo iLo) :
    ∀ q, expect (infectionActivationBandCount n h3 aLo target q)
        (fun z => w ^ z.2) ≤
      (p' + p * w) * w ^ q.2 := by
  rintro ⟨s, c⟩
  by_cases hlo : s.1.active < aLo
  · apply count_step_of_masses
      (K := infectionActivationBandCount n h3 aLo target)
      (count := Prod.snd) (s := (s, c))
      (w := w) (q := 1) (q' := 0) (p := p) (p' := p')
    · simp
    · exact hp
    · exact hw
    · rw [← hp]
      exact le_add_right le_rfl
    · rw [infectionActivationBandCount, if_pos hlo, expect_pure]
      simp
  · rw [infectionActivationBandCount, if_neg hlo]
    apply infectionActivationCount_step_at
      n h3 target w p p' hw hp (s, c)
    intro hlive
    change ¬ target ≤ s.1.active at hlive
    apply hpFloor.trans
    apply infectionActivationFloor_le n h3 s aLo iLo
    · omega
    · have hinv := s.2
      simp only [InfectionCfg.Inv, InfectionCfg.total] at hinv
      omega

/-- Adapted Chernoff lower tail with a genuinely uniform stage floor. -/
theorem infectionActivationBandCount_tail
    (n : ℕ) (h3 : 3 ≤ n) (aLo target iLo : ℕ)
    (w p p' : ℝ≥0∞)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hp : p + p' = 1)
    (hiLo : iLo + target ≤ n + 1)
    (hpFloor : p ≤ infectionActivationFloor n aLo iLo)
    (T M c0 : ℕ) (s0 : InfectionState n) :
    ∑' q, (if q.2 ≤ M then
        iter (infectionActivationBandCount n h3 aLo target)
          T (s0, c0) q else 0) ≤
      (p' + p * w) ^ T * w ^ c0 / w ^ M := by
  exact count_tail_bernoulli
    (infectionActivationBandCount n h3 aLo target) Prod.snd
    w p p' hw1 hw0
    (infectionActivationBandCount_step
      n h3 aLo target iLo w p p' hw1 hp hiLo hpFloor)
    T M (s0, c0)

/-- A supported ordinary activation-count step cannot decrease active count. -/
theorem infectionActivationCount_active_le_of_apply_ne_zero
    {n target : ℕ} (h3 : 3 ≤ n)
    (q z : InfectionState n × ℕ)
    (hqz : infectionActivationCount n h3 target q z ≠ 0) :
    q.1.1.active ≤ z.1.1.active := by
  by_cases hdone : target ≤ q.1.1.active
  · rw [infectionActivationCount, dif_pos hdone, PMF.pure_apply] at hqz
    by_cases hz : z = (q.1, q.2 + 1)
    · rw [hz]
    · simp [hz] at hqz
  · unfold infectionActivationCount at hqz
    rw [dif_neg hdone, PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
    push Not at hqz
    obtain ⟨e, he⟩ := hqz
    split_ifs at he with hze
    · rw [hze]
      exact InfectionEvent.active_le_nextState_active q.1 e
    · exact absurd rfl he

/-- Lower-stage reachability together with the exact activation account. -/
def InfectionActivationStageInv
    {n : ℕ} (aLo target initialActive initialCount : ℕ)
    (q : InfectionState n × ℕ) : Prop :=
  aLo ≤ q.1.1.active ∧
    InfectionActivationAccount target initialActive initialCount q

/-- The guarded stage invariant holds initially. -/
theorem infectionActivationStageInv_initial
    {n aLo target initialCount : ℕ} (s : InfectionState n)
    (haLo : aLo ≤ s.1.active) :
    InfectionActivationStageInv
      aLo target s.1.active initialCount (s, initialCount) :=
  ⟨haLo, infectionActivationAccount_initial s⟩

/-- One supported guarded step preserves the lower bound and activation
account. -/
theorem infectionActivationBandCount_stageInv_of_apply_ne_zero
    {n aLo target initialActive initialCount : ℕ} (h3 : 3 ≤ n)
    (q z : InfectionState n × ℕ)
    (hq : InfectionActivationStageInv
      aLo target initialActive initialCount q)
    (hqz : infectionActivationBandCount n h3 aLo target q z ≠ 0) :
    InfectionActivationStageInv
      aLo target initialActive initialCount z := by
  rcases hq with ⟨hqlo, hqAccount⟩
  have hnlo : ¬ q.1.1.active < aLo := by omega
  unfold infectionActivationBandCount at hqz
  rw [if_neg hnlo] at hqz
  exact ⟨hqlo.trans
      (infectionActivationCount_active_le_of_apply_ne_zero h3 q z hqz),
    infectionActivationCount_account_of_apply_ne_zero
      h3 q z hqAccount hqz⟩

/-- The guarded activation-stage invariant holds along every finite path. -/
theorem infectionActivationBandCount_iter_stageInv
    {n aLo target initialActive initialCount T : ℕ} (h3 : 3 ≤ n)
    (q z : InfectionState n × ℕ)
    (hq : InfectionActivationStageInv
      aLo target initialActive initialCount q)
    (hz : iter (infectionActivationBandCount n h3 aLo target) T q z ≠ 0) :
    InfectionActivationStageInv
      aLo target initialActive initialCount z := by
  induction T generalizing q with
  | zero =>
      simp only [iter, PMF.pure_apply] at hz
      by_cases h : z = q
      · rwa [h]
      · simp [h] at hz
  | succ T ih =>
      rw [iter_succ, PMF.bind_apply] at hz
      by_contra hzInv
      apply hz
      rw [ENNReal.tsum_eq_zero]
      intro a
      by_cases hqa :
          infectionActivationBandCount n h3 aLo target q a = 0
      · simp [hqa]
      · have haInv :=
          infectionActivationBandCount_stageInv_of_apply_ne_zero
            h3 q a hq hqa
        have hiaz :
            iter (infectionActivationBandCount n h3 aLo target) T a z = 0 := by
          by_contra hne
          exact hzInv (ih a haInv hne)
        simp [hiaz]

/-- Failure to reach the target is contained in a low-counter event. -/
theorem infectionActivationBandCount_failure_le_count
    (n : ℕ) (h3 : 3 ≤ n) (aLo target T M c0 : ℕ)
    (s0 : InfectionState n)
    (haLo : aLo ≤ s0.1.active)
    (hthreshold : target + c0 ≤ s0.1.active + (M + 1)) :
    ∑' q, (if target ≤ q.1.1.active then 0 else
        iter (infectionActivationBandCount n h3 aLo target)
          T (s0, c0) q) ≤
      ∑' q, (if q.2 ≤ M then
        iter (infectionActivationBandCount n h3 aLo target)
          T (s0, c0) q else 0) := by
  refine ENNReal.tsum_le_tsum fun q => ?_
  by_cases htarget : target ≤ q.1.1.active
  · simp [htarget]
  · rw [if_neg htarget]
    by_cases hmass :
        iter (infectionActivationBandCount n h3 aLo target)
          T (s0, c0) q = 0
    · rw [hmass]
      simp
    · have hInv :=
        infectionActivationBandCount_iter_stageInv h3
          (s0, c0) q
          (infectionActivationStageInv_initial s0 haLo) hmass
      have hcount : q.2 ≤ M := by
        by_contra hnot
        have henough : target + c0 ≤ s0.1.active + q.2 := by
          omega
        exact htarget
          (infectionActivation_target_of_account q hInv.2 henough)
      rw [if_pos hcount]

/-- Explicit guarded-stage failure tail for reaching an active-count target. -/
theorem infectionActivationBandCount_failure_tail
    (n : ℕ) (h3 : 3 ≤ n) (aLo target iLo : ℕ)
    (w p p' : ℝ≥0∞)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hp : p + p' = 1)
    (hiLo : iLo + target ≤ n + 1)
    (hpFloor : p ≤ infectionActivationFloor n aLo iLo)
    (T M c0 : ℕ) (s0 : InfectionState n)
    (haLo : aLo ≤ s0.1.active)
    (hthreshold : target + c0 ≤ s0.1.active + (M + 1)) :
    ∑' q, (if target ≤ q.1.1.active then 0 else
        iter (infectionActivationBandCount n h3 aLo target)
          T (s0, c0) q) ≤
      (p' + p * w) ^ T * w ^ c0 / w ^ M := by
  exact (infectionActivationBandCount_failure_le_count
    n h3 aLo target T M c0 s0 haLo hthreshold).trans
      (infectionActivationBandCount_tail
        n h3 aLo target iLo w p p'
        hw1 hw0 hp hiLo hpFloor T M c0 s0)

/-- Explicit finite-stage activation tail for the original physical infection
chain. -/
theorem infectionActivation_failure_tail
    (n : ℕ) (h3 : 3 ≤ n) (aLo target iLo : ℕ)
    (w p p' : ℝ≥0∞)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hp : p + p' = 1)
    (hiLo : iLo + target ≤ n + 1)
    (hpFloor : p ≤ infectionActivationFloor n aLo iLo)
    (T M c0 : ℕ) (s0 : InfectionState n)
    (haLo : aLo ≤ s0.1.active)
    (hthreshold : target + c0 ≤ s0.1.active + (M + 1)) :
    (∑' s, if target ≤ s.1.active then 0 else
        iter (infectionStateStep n h3) T s0 s) ≤
      (p' + p * w) ^ T * w ^ c0 / w ^ M := by
  exact (infectionActivation_failure_le_bandCount
    n h3 aLo target T c0 s0).trans
      (infectionActivationBandCount_failure_tail
        n h3 aLo target iLo w p p'
        hw1 hw0 hp hiLo hpFloor T M c0 s0 haLo hthreshold)

end Tri

#print axioms Tri.infectionActivationBandCount_map_fst
#print axioms Tri.infectionStateStep_iter_target
#print axioms Tri.infectionActivation_failure_le_bandCount
#print axioms Tri.infectionActivationBandCount_step
#print axioms Tri.infectionActivationBandCount_tail
#print axioms Tri.infectionActivationBandCount_iter_stageInv
#print axioms Tri.infectionActivationBandCount_failure_le_count
#print axioms Tri.infectionActivationBandCount_failure_tail
#print axioms Tri.infectionActivation_failure_tail
