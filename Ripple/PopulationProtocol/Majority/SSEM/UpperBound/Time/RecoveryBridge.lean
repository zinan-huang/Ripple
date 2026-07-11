import Ripple.PopulationProtocol.Majority.SSEM.Convergence.BurmanConvergenceFinal
import Ripple.PopulationProtocol.Majority.SSEM.Probability.ExpectedTime

namespace SSEM

open scoped ENNReal

variable {n : ℕ}

/-- Self-pair steps are no-ops. -/
theorem step_self_eq (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n) (i : Fin n) :
    C.step P i i = C := by
  simp [Config.step]

/-- Prepending a pair to a schedule and running one more step. -/
private theorem execution_prepend_eq
    (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n)
    (p : Fin n × Fin n) (γ : DetScheduler n) (t : ℕ) :
    execution P C (fun k => if k = 0 then p else γ (k - 1)) (t + 1) =
    execution P (C.step P p.1 p.2) γ t := by
  suffices key : ∀ s, execution P (C.step P p.1 p.2) γ s =
      execution P C (fun k => if k = 0 then p else γ (k - 1)) (s + 1) from
    (key t).symm
  intro s
  induction s with
  | zero => simp [execution]
  | succ s ih =>
    simp only [execution] at ih ⊢
    have h1 : (s + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero s
    simp [h1, Nat.succ_sub_one] at ih ⊢
    rw [← ih]

/-- Shifting a schedule by 1 when the first step is identity. -/
private theorem execution_shift_self
    (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n)
    (γ : DetScheduler n) (t : ℕ)
    (hself : (γ 0).1 = (γ 0).2) :
    execution P C γ (t + 1) = execution P C (fun k => γ (k + 1)) t := by
  suffices key : ∀ s, execution P C (fun k => γ (k + 1)) s =
      execution P C γ (s + 1) from (key t).symm
  intro s
  induction s with
  | zero =>
    simp only [execution]
    rw [hself, step_self_eq]
  | succ s ih =>
    simp only [execution] at ih ⊢
    rw [← ih]

/-- Strip self-pairs from an execution. -/
theorem execution_filter_distinct
    (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n)
    (γ : DetScheduler n) (t : ℕ)
    {Goal : Config (AgentState n) Opinion n → Prop}
    (hGoal : Goal (execution P C γ t)) :
    ∃ (γ2 : DetScheduler n) (t2 : ℕ),
      t2 ≤ t ∧
      (∀ k, k < t2 → (γ2 k).1 ≠ (γ2 k).2) ∧
      Goal (execution P C γ2 t2) := by
  induction t generalizing C γ with
  | zero =>
    exact ⟨γ, 0, le_refl 0, fun k hk => absurd hk (Nat.not_lt_zero k), hGoal⟩
  | succ t ih =>
    by_cases hself : (γ 0).1 = (γ 0).2
    · rw [execution_shift_self P C γ t hself] at hGoal
      obtain ⟨γ2, t2, ht2, hdist, hGoal2⟩ := ih C (fun k => γ (k + 1)) hGoal
      exact ⟨γ2, t2, Nat.le_succ_of_le ht2, hdist, hGoal2⟩
    · have htail : execution P C γ (t + 1) =
          execution P (C.step P (γ 0).1 (γ 0).2) (fun k => γ (k + 1)) t := by
        rw [← execution_prepend_eq P C (γ 0) (fun k => γ (k + 1)) t]
        congr 1; funext k
        by_cases hk : k = 0
        · simp [hk]
        · simp [hk, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)]
      rw [htail] at hGoal
      obtain ⟨γ2, t2, ht2, hdist, hGoal2⟩ :=
        ih (C.step P (γ 0).1 (γ 0).2) (fun k => γ (k + 1)) hGoal
      refine ⟨fun k => if k = 0 then γ 0 else γ2 (k - 1), t2 + 1,
        Nat.succ_le_succ ht2, ?_, ?_⟩
      · intro k hk
        by_cases hk0 : k = 0
        · simp [hk0]; exact hself
        · simp [hk0]; exact hdist (k - 1) (by omega)
      · rw [execution_prepend_eq]; exact hGoal2

end SSEM
