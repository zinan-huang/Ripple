import Ripple.PopulationProtocol.Majority.ExactMajority.Protocol.Transition
import Mathlib.Tactic

namespace ExactMajority

open scoped BigOperators

namespace P3DeterministicAlgebra

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Concrete Phase-3 step classifier -/

/-- The deterministic branch of the concrete Phase-3 ordered-pair transition. -/
inductive P3Kind where
  | ClockEpidemic
  | ClockDrip
  | HourDrag
  | Cancel
  | Split
  | PhaseCounter
  | Noop
  deriving DecidableEq, Repr

namespace P3Step

/-- Classifier for the concrete `Phase3Transition` branch that fires on `(s,t)`.

The order mirrors `Phase3Transition`: clock-clock Rule 1, Main-clock hour drag,
Main-Main cancel/split, then no-op. -/
def kind (s t : AgentState L K) : P3Kind :=
  if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then
      .ClockEpidemic
    else if s.minute.val < K * (L + 1) then
      .ClockDrip
    else
      .PhaseCounter
  else if s.role = .main ∧ s.bias = .zero ∧ t.role = .clock then
    .HourDrag
  else if t.role = .main ∧ t.bias = .zero ∧ s.role = .clock then
    .HourDrag
  else if s.role = .main ∧ t.role = .main then
    match s.bias, t.bias with
    | .dyadic .pos i, .dyadic .neg j => if i.val = j.val then .Cancel else .Noop
    | .dyadic .neg i, .dyadic .pos j => if i.val = j.val then .Cancel else .Noop
    | .zero, .dyadic _ i => if s.hour.val > i.val then .Split else .Noop
    | .dyadic _ i, .zero => if t.hour.val > i.val then .Split else .Noop
    | _, _ => .Noop
  else
    .Noop

@[simp] theorem kind_clock_epidemic (s t : AgentState L K)
    (hcc : s.role = .clock ∧ t.role = .clock) (hne : s.minute ≠ t.minute) :
    kind (L := L) (K := K) s t = .ClockEpidemic := by
  simp [kind, hcc, hne]

@[simp] theorem kind_clock_drip (s t : AgentState L K)
    (hcc : s.role = .clock ∧ t.role = .clock) (heq : ¬ s.minute ≠ t.minute)
    (hnotmax : s.minute.val < K * (L + 1)) :
    kind (L := L) (K := K) s t = .ClockDrip := by
  simp [kind, hcc, heq, hnotmax]

@[simp] theorem kind_phase_counter (s t : AgentState L K)
    (hcc : s.role = .clock ∧ t.role = .clock) (heq : ¬ s.minute ≠ t.minute)
    (hmax : ¬ s.minute.val < K * (L + 1)) :
    kind (L := L) (K := K) s t = .PhaseCounter := by
  simp [kind, hcc, heq, hmax]

@[simp] theorem kind_hour_drag_left (s t : AgentState L K)
    (_hncc : ¬ (s.role = .clock ∧ t.role = .clock))
    (hdrag : s.role = .main ∧ s.bias = .zero ∧ t.role = .clock) :
    kind (L := L) (K := K) s t = .HourDrag := by
  simp [kind, hdrag]

@[simp] theorem kind_hour_drag_right (s t : AgentState L K)
    (_hncc : ¬ (s.role = .clock ∧ t.role = .clock))
    (_hdragL : ¬ (s.role = .main ∧ s.bias = .zero ∧ t.role = .clock))
    (hdragR : t.role = .main ∧ t.bias = .zero ∧ s.role = .clock) :
    kind (L := L) (K := K) s t = .HourDrag := by
  simp [kind, hdragR]

@[simp] theorem kind_cancel_pos_neg (s t : AgentState L K) (i j : Fin (L + 1))
    (_hncc : ¬ (s.role = .clock ∧ t.role = .clock))
    (_hdragL : ¬ (s.role = .main ∧ s.bias = .zero ∧ t.role = .clock))
    (_hdragR : ¬ (t.role = .main ∧ t.bias = .zero ∧ s.role = .clock))
    (hsr : s.role = .main) (htr : t.role = .main)
    (hsb : s.bias = Bias.dyadic .pos i) (htb : t.bias = Bias.dyadic .neg j)
    (hij : i.val = j.val) :
    kind (L := L) (K := K) s t = .Cancel := by
  simp [kind, hsr, htr, hsb, htb, hij]

@[simp] theorem kind_cancel_neg_pos (s t : AgentState L K) (i j : Fin (L + 1))
    (_hncc : ¬ (s.role = .clock ∧ t.role = .clock))
    (_hdragL : ¬ (s.role = .main ∧ s.bias = .zero ∧ t.role = .clock))
    (_hdragR : ¬ (t.role = .main ∧ t.bias = .zero ∧ s.role = .clock))
    (hsr : s.role = .main) (htr : t.role = .main)
    (hsb : s.bias = Bias.dyadic .neg i) (htb : t.bias = Bias.dyadic .pos j)
    (hij : i.val = j.val) :
    kind (L := L) (K := K) s t = .Cancel := by
  simp [kind, hsr, htr, hsb, htb, hij]

@[simp] theorem kind_split_left (s t : AgentState L K) (sgn : Sign) (i : Fin (L + 1))
    (_hncc : ¬ (s.role = .clock ∧ t.role = .clock))
    (_hdragL : ¬ (s.role = .main ∧ s.bias = .zero ∧ t.role = .clock))
    (_hdragR : ¬ (t.role = .main ∧ t.bias = .zero ∧ s.role = .clock))
    (hsr : s.role = .main) (htr : t.role = .main)
    (hsb : s.bias = Bias.zero) (htb : t.bias = Bias.dyadic sgn i)
    (hgt : s.hour.val > i.val) :
    kind (L := L) (K := K) s t = .Split := by
  simp [kind, hsr, htr, hsb, htb, hgt]

@[simp] theorem kind_split_right (s t : AgentState L K) (sgn : Sign) (i : Fin (L + 1))
    (_hncc : ¬ (s.role = .clock ∧ t.role = .clock))
    (_hdragL : ¬ (s.role = .main ∧ s.bias = .zero ∧ t.role = .clock))
    (_hdragR : ¬ (t.role = .main ∧ t.bias = .zero ∧ s.role = .clock))
    (hsr : s.role = .main) (htr : t.role = .main)
    (hsb : s.bias = Bias.dyadic sgn i) (htb : t.bias = Bias.zero)
    (hgt : t.hour.val > i.val) :
    kind (L := L) (K := K) s t = .Split := by
  simp [kind, hsr, htr, hsb, htb, hgt]

end P3Step

/-! ## Weighted dyadic observables -/

/-- `w i = 2^{-i}` as a rational. -/
noncomputable def weightQ (i : Fin (L + 1)) : ℚ :=
  (1 : ℚ) / (2 ^ (i.val : ℕ))

lemma weightQ_nonneg (i : Fin (L + 1)) :
    0 ≤ weightQ (L := L) i := by
  unfold weightQ
  positivity

private lemma weightQ_succ_add_self (i : Fin (L + 1)) (hi : i.val < L) :
    let ip1 : Fin (L + 1) := ⟨i.val + 1, by omega⟩
    weightQ (L := L) ip1 + weightQ (L := L) ip1 = weightQ (L := L) i := by
  dsimp [weightQ]
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have hpow_i : (2 : ℚ) ^ i.val ≠ 0 := pow_ne_zero _ h2
  have hpow_s : (2 : ℚ) ^ (i.val + 1) ≠ 0 := pow_ne_zero _ h2
  field_simp [hpow_i, hpow_s, pow_succ]
  ring

noncomputable def biasPosMassQ : Bias L → ℚ
  | .dyadic .pos i => weightQ (L := L) i
  | _ => 0

noncomputable def biasNegMassQ : Bias L → ℚ
  | .dyadic .neg i => weightQ (L := L) i
  | _ => 0

noncomputable def biasMassQ (b : Bias L) : ℚ :=
  biasPosMassQ (L := L) b + biasNegMassQ (L := L) b

noncomputable def agentPosMassQ (a : AgentState L K) : ℚ :=
  biasPosMassQ (L := L) a.bias

noncomputable def agentNegMassQ (a : AgentState L K) : ℚ :=
  biasNegMassQ (L := L) a.bias

noncomputable def agentMassQ (a : AgentState L K) : ℚ :=
  biasMassQ (L := L) a.bias

noncomputable def betaPlusQ (c : Config (AgentState L K)) : ℚ :=
  Config.sumOf (agentPosMassQ (L := L) (K := K)) c

noncomputable def betaMinusQ (c : Config (AgentState L K)) : ℚ :=
  Config.sumOf (agentNegMassQ (L := L) (K := K)) c

/-- Signed weighted bias `g = β₊ - β₋`. -/
noncomputable def biasSumQ (c : Config (AgentState L K)) : ℚ :=
  Config.sumOf (fun a : AgentState L K => Bias.toRat a.bias) c

/-- Total weighted dyadic mass `μ = β₊ + β₋`. -/
noncomputable def totalMassQ (c : Config (AgentState L K)) : ℚ :=
  Config.sumOf (agentMassQ (L := L) (K := K)) c

lemma Bias.toRat_eq_pos_sub_neg (b : Bias L) :
    Bias.toRat b = biasPosMassQ (L := L) b - biasNegMassQ (L := L) b := by
  cases b with
  | zero => simp [Bias.toRat, biasPosMassQ, biasNegMassQ]
  | dyadic s i =>
      cases s <;> simp [Bias.toRat, biasPosMassQ, biasNegMassQ, weightQ, div_eq_mul_inv]

lemma biasSumQ_eq_betaPlus_sub_betaMinus (c : Config (AgentState L K)) :
    biasSumQ (L := L) (K := K) c =
      betaPlusQ (L := L) (K := K) c - betaMinusQ (L := L) (K := K) c := by
  classical
  unfold biasSumQ betaPlusQ betaMinusQ Config.sumOf
  induction c using Multiset.induction_on with
  | empty => simp
  | cons a c ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons] at ih ⊢
      rw [Bias.toRat_eq_pos_sub_neg, ih]
      simp [agentPosMassQ, agentNegMassQ]
      ring

/-! ## Generic deterministic pair-to-config lifts -/

private theorem stepRel_sumOf_eq_of_pair
    {Λ M : Type*} [Fintype Λ] [DecidableEq Λ] [AddCommMonoid M]
    {P : Protocol Λ} {f : Λ → M} {c c' : Config Λ}
    (hδ : ∀ r₁ r₂, Protocol.Applicable c r₁ r₂ →
      let p := P.δ r₁ r₂
      f p.1 + f p.2 = f r₁ + f r₂)
    (hstep : P.StepRel c c') :
    c'.sumOf f = c.sumOf f := by
  rcases hstep with ⟨r₁, r₂, happ, hc'⟩
  dsimp at hc'
  rcases hpair : P.δ r₁ r₂ with ⟨p₁, p₂⟩
  subst c'
  have hδ' : f p₁ + f p₂ = f r₁ + f r₂ := by
    simpa [hpair] using hδ r₁ r₂ happ
  dsimp [Config.sumOf]
  change ((c - ({r₁, r₂} : Multiset Λ) +
          ({(P.δ r₁ r₂).1, (P.δ r₁ r₂).2} : Multiset Λ)).map f).sum =
    (c.map f).sum
  rw [hpair]
  calc
    ((c - ({r₁, r₂} : Multiset Λ) + ({p₁, p₂} : Multiset Λ)).map f).sum
        = ((c - ({r₁, r₂} : Multiset Λ)).map f).sum +
            (({p₁, p₂} : Multiset Λ).map f).sum := by
          rw [Multiset.map_add, Multiset.sum_add]
    _ = ((c - ({r₁, r₂} : Multiset Λ)).map f).sum + (f p₁ + f p₂) := by simp
    _ = ((c - ({r₁, r₂} : Multiset Λ)).map f).sum + (f r₁ + f r₂) := by rw [hδ']
    _ = ((c - ({r₁, r₂} : Multiset Λ)).map f).sum +
          (({r₁, r₂} : Multiset Λ).map f).sum := by simp
    _ = (((c - ({r₁, r₂} : Multiset Λ)) + ({r₁, r₂} : Multiset Λ)).map f).sum := by
          rw [Multiset.map_add, Multiset.sum_add]
    _ = (c.map f).sum := by rw [Multiset.sub_add_cancel happ]

private theorem stepRel_sumOf_le_of_pair
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {P : Protocol Λ} {f : Λ → ℚ} {c c' : Config Λ}
    (hδ : ∀ r₁ r₂, Protocol.Applicable c r₁ r₂ →
      let p := P.δ r₁ r₂
      f p.1 + f p.2 ≤ f r₁ + f r₂)
    (hstep : P.StepRel c c') :
    c'.sumOf f ≤ c.sumOf f := by
  rcases hstep with ⟨r₁, r₂, happ, hc'⟩
  dsimp at hc'
  rcases hpair : P.δ r₁ r₂ with ⟨p₁, p₂⟩
  subst c'
  have hδ' : f p₁ + f p₂ ≤ f r₁ + f r₂ := by
    simpa [hpair] using hδ r₁ r₂ happ
  dsimp [Config.sumOf]
  change ((c - ({r₁, r₂} : Multiset Λ) +
          ({(P.δ r₁ r₂).1, (P.δ r₁ r₂).2} : Multiset Λ)).map f).sum ≤
    (c.map f).sum
  rw [hpair]
  calc
    ((c - ({r₁, r₂} : Multiset Λ) + ({p₁, p₂} : Multiset Λ)).map f).sum
        = ((c - ({r₁, r₂} : Multiset Λ)).map f).sum +
            (({p₁, p₂} : Multiset Λ).map f).sum := by
          rw [Multiset.map_add, Multiset.sum_add]
    _ = ((c - ({r₁, r₂} : Multiset Λ)).map f).sum + (f p₁ + f p₂) := by simp
    _ ≤ ((c - ({r₁, r₂} : Multiset Λ)).map f).sum + (f r₁ + f r₂) := by
          linarith
    _ = ((c - ({r₁, r₂} : Multiset Λ)).map f).sum +
          (({r₁, r₂} : Multiset Λ).map f).sum := by simp
    _ = (((c - ({r₁, r₂} : Multiset Λ)) + ({r₁, r₂} : Multiset Λ)).map f).sum := by
          rw [Multiset.map_add, Multiset.sum_add]
    _ = (c.map f).sum := by rw [Multiset.sub_add_cancel happ]

/-- The deterministic protocol consisting only of the concrete Phase-3 branch. -/
noncomputable def P3Protocol (L K : ℕ) : Protocol (AgentState L K) where
  δ := Phase3Transition L K

private lemma mem_left_of_applicable {c : Config (AgentState L K)} {r₁ r₂ : AgentState L K}
    (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le happ (by simp)

private lemma mem_right_of_applicable {c : Config (AgentState L K)} {r₁ r₂ : AgentState L K}
    (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le happ (by simp)

/-! ## Signed weighted bias is preserved -/

/-- Pair form: concrete Phase-3 transitions preserve weighted signed bias. -/
theorem p3_biasSum_pair_eq (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    Bias.toRat (Phase3Transition L K s t).1.bias +
      Bias.toRat (Phase3Transition L K s t).2.bias =
    Bias.toRat s.bias + Bias.toRat t.bias :=
  Phase3Transition_preserves_dyadicBiasSum_pair_of_phase_three
    (L := L) (K := K) s t hs ht

/-- Config step form: `g = β₊ - β₋` is preserved by every deterministic Phase-3 step. -/
theorem p3_biasSum_step_eq {c c' : Config (AgentState L K)}
    (hc3 : ∀ a ∈ c, a.phase.val = 3)
    (hstep : (P3Protocol L K).StepRel c c') :
    biasSumQ (L := L) (K := K) c' = biasSumQ (L := L) (K := K) c := by
  unfold biasSumQ
  refine stepRel_sumOf_eq_of_pair (P := P3Protocol L K) ?_ hstep
  intro r₁ r₂ happ
  have hr₁ : r₁.phase.val = 3 := hc3 r₁ (mem_left_of_applicable happ)
  have hr₂ : r₂.phase.val = 3 := hc3 r₂ (mem_right_of_applicable happ)
  simpa [P3Protocol] using
    p3_biasSum_pair_eq (L := L) (K := K) r₁ r₂ hr₁ hr₂

/-! ## Total weighted mass is nonincreasing -/

noncomputable def pairMassQ (s t : AgentState L K) : ℚ :=
  agentMassQ (L := L) (K := K) s + agentMassQ (L := L) (K := K) t

/-- Helper-level mass ledger. Cancels strictly decrease; splits preserve weighted mass. -/
theorem phase3CancelSplit_totalMass_pair_le (s t : AgentState L K) :
    pairMassQ (L := L) (K := K) (phase3CancelSplit L K s t).1 (phase3CancelSplit L K s t).2
      ≤ pairMassQ (L := L) (K := K) s t := by
  classical
  unfold pairMassQ agentMassQ biasMassQ biasPosMassQ biasNegMassQ
  cases hs : s.bias with
  | zero =>
      cases ht : t.bias with
      | zero => simp [phase3CancelSplit, hs, ht]
      | dyadic sgn i =>
          cases sgn
          · by_cases hgt : s.hour.val > i.val
            · have hiL : i.val < L := by
                have hle : s.hour.val ≤ L := by omega
                omega
              simp [phase3CancelSplit, hs, ht, hgt, hiL, weightQ_succ_add_self]
            · simp [phase3CancelSplit, hs, ht, hgt]
          · by_cases hgt : s.hour.val > i.val
            · have hiL : i.val < L := by
                have hle : s.hour.val ≤ L := by omega
                omega
              simp [phase3CancelSplit, hs, ht, hgt, hiL, weightQ_succ_add_self]
            · simp [phase3CancelSplit, hs, ht, hgt]
  | dyadic sgn i =>
      cases ht : t.bias with
      | zero =>
          cases sgn
          · by_cases hgt : t.hour.val > i.val
            · have hiL : i.val < L := by
                have hle : t.hour.val ≤ L := by omega
                omega
              simp [phase3CancelSplit, hs, ht, hgt, hiL, weightQ_succ_add_self]
            · simp [phase3CancelSplit, hs, ht, hgt]
          · by_cases hgt : t.hour.val > i.val
            · have hiL : i.val < L := by
                have hle : t.hour.val ≤ L := by omega
                omega
              simp [phase3CancelSplit, hs, ht, hgt, hiL, weightQ_succ_add_self]
            · simp [phase3CancelSplit, hs, ht, hgt]
      | dyadic tsgn j =>
          cases sgn <;> cases tsgn
          · simp [phase3CancelSplit, hs, ht]
          · by_cases hij : i.val = j.val
            · simp [phase3CancelSplit, hs, ht, hij]
              nlinarith [weightQ_nonneg (L := L) i, weightQ_nonneg (L := L) j]
            · simp [phase3CancelSplit, hs, ht, hij]
          · by_cases hij : i.val = j.val
            · simp [phase3CancelSplit, hs, ht, hij]
              nlinarith [weightQ_nonneg (L := L) i, weightQ_nonneg (L := L) j]
            · simp [phase3CancelSplit, hs, ht, hij]
          · simp [phase3CancelSplit, hs, ht]

/-- Exact total-mass cancellation delta: `(+,j),(-,j) ↦ O,O` removes `2*w j`. -/
theorem p3_totalMass_cancel_delta_pos_neg (s t : AgentState L K) (i : Fin (L + 1)) :
    pairMassQ (L := L) (K := K)
        (phase3CancelSplit L K {s with bias := Bias.dyadic .pos i}
          {t with bias := Bias.dyadic .neg i}).1
        (phase3CancelSplit L K {s with bias := Bias.dyadic .pos i}
          {t with bias := Bias.dyadic .neg i}).2
      = pairMassQ (L := L) (K := K)
          {s with bias := Bias.dyadic .pos i} {t with bias := Bias.dyadic .neg i}
        - 2 * weightQ (L := L) i := by
  simp [phase3CancelSplit, pairMassQ, agentMassQ, biasMassQ, biasPosMassQ, biasNegMassQ]
  ring

/-- Exact total-mass split delta: `(O),(s,j) ↦ (s,j+1),(s,j+1)` preserves mass. -/
theorem p3_totalMass_split_delta_left (z b : AgentState L K) (sgn : Sign) (i : Fin (L + 1))
    (hz : z.bias = Bias.zero) (hb : b.bias = Bias.dyadic sgn i)
    (hgt : z.hour.val > i.val) :
    pairMassQ (L := L) (K := K)
        (phase3CancelSplit L K z b).1 (phase3CancelSplit L K z b).2
      = pairMassQ (L := L) (K := K) z b := by
  have hiL : i.val < L := by
    have hle : z.hour.val ≤ L := by omega
    omega
  cases sgn <;>
    simp [phase3CancelSplit, hz, hb, hgt, hiL, pairMassQ,
      agentMassQ, biasMassQ, biasPosMassQ, biasNegMassQ, weightQ_succ_add_self]

/-- Pair form for the full concrete `Phase3Transition`: total weighted mass is nonincreasing. -/
theorem p3_totalMass_pair_le (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    pairMassQ (L := L) (K := K) (Phase3Transition L K s t).1 (Phase3Transition L K s t).2
      ≤ pairMassQ (L := L) (K := K) s t := by
  classical
  let s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
    else if h_max : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else stdCounterSubroutine L K s
  else s
  let t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
    else if h_max : s.minute.val < K * (L + 1) then t
    else stdCounterSubroutine L K t
  else t
  let s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1 : agentMassQ (L := L) (K := K) s1 = agentMassQ (L := L) (K := K) s := by
    dsimp [s1, agentMassQ, biasMassQ, biasPosMassQ, biasNegMassQ]
    split_ifs <;> simp [stdCounterSubroutine_preserves_bias_of_phase_three, hs]
  have ht1 : agentMassQ (L := L) (K := K) t1 = agentMassQ (L := L) (K := K) t := by
    dsimp [t1, agentMassQ, biasMassQ, biasPosMassQ, biasNegMassQ]
    split_ifs <;> simp [stdCounterSubroutine_preserves_bias_of_phase_three, ht]
  have hs2 : agentMassQ (L := L) (K := K) s2 = agentMassQ (L := L) (K := K) s1 := by
    dsimp [s2, agentMassQ, biasMassQ, biasPosMassQ, biasNegMassQ]
    split_ifs <;> simp
  have ht2 : agentMassQ (L := L) (K := K) t2 = agentMassQ (L := L) (K := K) t1 := by
    dsimp [t2, agentMassQ, biasMassQ, biasPosMassQ, biasNegMassQ]
    split_ifs <;> simp
  have hfinal :
      pairMassQ (L := L) (K := K) (Phase3Transition L K s t).1 (Phase3Transition L K s t).2
        ≤ pairMassQ (L := L) (K := K) s2 t2 := by
    unfold Phase3Transition
    change pairMassQ (L := L) (K := K)
        (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2 else (s2, t2)).1
        (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2 else (s2, t2)).2
      ≤ pairMassQ (L := L) (K := K) s2 t2
    by_cases hmain : s2.role = .main ∧ t2.role = .main
    · simpa [hmain] using phase3CancelSplit_totalMass_pair_le (L := L) (K := K) s2 t2
    · simp [hmain]
  calc
    pairMassQ (L := L) (K := K) (Phase3Transition L K s t).1 (Phase3Transition L K s t).2
        ≤ pairMassQ (L := L) (K := K) s2 t2 := hfinal
    _ = pairMassQ (L := L) (K := K) s1 t1 := by simp [pairMassQ, hs2, ht2]
    _ = pairMassQ (L := L) (K := K) s t := by simp [pairMassQ, hs1, ht1]

/-- Config step form: total weighted mass `μ = β₊ + β₋` is nonincreasing. -/
theorem p3_totalMass_step_le {c c' : Config (AgentState L K)}
    (hc3 : ∀ a ∈ c, a.phase.val = 3)
    (hstep : (P3Protocol L K).StepRel c c') :
    totalMassQ (L := L) (K := K) c' ≤ totalMassQ (L := L) (K := K) c := by
  unfold totalMassQ
  refine stepRel_sumOf_le_of_pair (P := P3Protocol L K) ?_ hstep
  intro r₁ r₂ happ
  have hr₁ : r₁.phase.val = 3 := hc3 r₁ (mem_left_of_applicable happ)
  have hr₂ : r₂.phase.val = 3 := hc3 r₂ (mem_right_of_applicable happ)
  simpa [P3Protocol, pairMassQ] using
    p3_totalMass_pair_le (L := L) (K := K) r₁ r₂ hr₁ hr₂

/-! ## Weighted mass above level `h` is nonincreasing -/

/-- Weighted mass in levels `j < h`, i.e. exponent `-j > -h`. -/
noncomputable def biasMassAboveQ (h : ℕ) : Bias L → ℚ
  | .zero => 0
  | .dyadic _ i => if i.val < h then weightQ (L := L) i else 0

noncomputable def agentMassAboveQ (h : ℕ) (a : AgentState L K) : ℚ :=
  biasMassAboveQ (L := L) h a.bias

noncomputable def massAboveQ (h : ℕ) (c : Config (AgentState L K)) : ℚ :=
  Config.sumOf (agentMassAboveQ (L := L) (K := K) h) c

noncomputable def pairMassAboveQ (h : ℕ) (s t : AgentState L K) : ℚ :=
  agentMassAboveQ (L := L) (K := K) h s + agentMassAboveQ (L := L) (K := K) h t

/-- Helper-level above-mass ledger. Interior splits preserve `μAbove_h`; boundary splits drop it. -/
theorem phase3CancelSplit_massAbove_pair_le (h : ℕ) (s t : AgentState L K) :
    pairMassAboveQ (L := L) (K := K) h
        (phase3CancelSplit L K s t).1 (phase3CancelSplit L K s t).2
      ≤ pairMassAboveQ (L := L) (K := K) h s t := by
  classical
  unfold pairMassAboveQ agentMassAboveQ biasMassAboveQ
  cases hs : s.bias with
  | zero =>
      cases ht : t.bias with
      | zero => simp [phase3CancelSplit, hs, ht]
      | dyadic sgn i =>
          cases sgn
          · by_cases hgt : s.hour.val > i.val
            · have hiL : i.val < L := by
                have hle : s.hour.val ≤ L := by omega
                omega
              by_cases hi : i.val < h
              · by_cases his : i.val + 1 < h
                · simp [phase3CancelSplit, hs, ht, hgt, hiL, hi, his, weightQ_succ_add_self]
                · have hb : ¬ (i.val + 1 < h) := his
                  simp [phase3CancelSplit, hs, ht, hgt, hi, hb, weightQ_nonneg]
              · have hnotSucc : ¬ i.val + 1 < h := by omega
                simp [phase3CancelSplit, hs, ht, hgt, hi, hnotSucc]
            · simp [phase3CancelSplit, hs, ht, hgt]
          · by_cases hgt : s.hour.val > i.val
            · have hiL : i.val < L := by
                have hle : s.hour.val ≤ L := by omega
                omega
              by_cases hi : i.val < h
              · by_cases his : i.val + 1 < h
                · simp [phase3CancelSplit, hs, ht, hgt, hiL, hi, his, weightQ_succ_add_self]
                · have hb : ¬ (i.val + 1 < h) := his
                  simp [phase3CancelSplit, hs, ht, hgt, hi, hb, weightQ_nonneg]
              · have hnotSucc : ¬ i.val + 1 < h := by omega
                simp [phase3CancelSplit, hs, ht, hgt, hi, hnotSucc]
            · simp [phase3CancelSplit, hs, ht, hgt]
  | dyadic sgn i =>
      cases ht : t.bias with
      | zero =>
          cases sgn
          · by_cases hgt : t.hour.val > i.val
            · have hiL : i.val < L := by
                have hle : t.hour.val ≤ L := by omega
                omega
              by_cases hi : i.val < h
              · by_cases his : i.val + 1 < h
                · simp [phase3CancelSplit, hs, ht, hgt, hiL, hi, his, weightQ_succ_add_self]
                · have hb : ¬ (i.val + 1 < h) := his
                  simp [phase3CancelSplit, hs, ht, hgt, hi, hb, weightQ_nonneg]
              · have hnotSucc : ¬ i.val + 1 < h := by omega
                simp [phase3CancelSplit, hs, ht, hgt, hi, hnotSucc]
            · simp [phase3CancelSplit, hs, ht, hgt]
          · by_cases hgt : t.hour.val > i.val
            · have hiL : i.val < L := by
                have hle : t.hour.val ≤ L := by omega
                omega
              by_cases hi : i.val < h
              · by_cases his : i.val + 1 < h
                · simp [phase3CancelSplit, hs, ht, hgt, hiL, hi, his, weightQ_succ_add_self]
                · have hb : ¬ (i.val + 1 < h) := his
                  simp [phase3CancelSplit, hs, ht, hgt, hi, hb, weightQ_nonneg]
              · have hnotSucc : ¬ i.val + 1 < h := by omega
                simp [phase3CancelSplit, hs, ht, hgt, hi, hnotSucc]
            · simp [phase3CancelSplit, hs, ht, hgt]
      | dyadic tsgn j =>
          cases sgn <;> cases tsgn
          · simp [phase3CancelSplit, hs, ht]
          · by_cases hij : i.val = j.val
            · by_cases hi : i.val < h
              · have hj : j.val < h := by omega
                simp [phase3CancelSplit, hs, ht, hij, hj]
                nlinarith [weightQ_nonneg (L := L) i, weightQ_nonneg (L := L) j]
              · have hj : ¬ j.val < h := by omega
                simp [phase3CancelSplit, hs, ht, hij, hj]
            · simp [phase3CancelSplit, hs, ht, hij]
          · by_cases hij : i.val = j.val
            · by_cases hi : i.val < h
              · have hj : j.val < h := by omega
                simp [phase3CancelSplit, hs, ht, hij, hj]
                nlinarith [weightQ_nonneg (L := L) i, weightQ_nonneg (L := L) j]
              · have hj : ¬ j.val < h := by omega
                simp [phase3CancelSplit, hs, ht, hij, hj]
            · simp [phase3CancelSplit, hs, ht, hij]
          · simp [phase3CancelSplit, hs, ht]

/-- Exact above-mass cancellation delta when the canceled level is above the boundary. -/
theorem p3_massAbove_cancel_delta_pos_neg (h : ℕ) (s t : AgentState L K) (i : Fin (L + 1))
    (hi : i.val < h) :
    pairMassAboveQ (L := L) (K := K) h
        (phase3CancelSplit L K {s with bias := Bias.dyadic .pos i}
          {t with bias := Bias.dyadic .neg i}).1
        (phase3CancelSplit L K {s with bias := Bias.dyadic .pos i}
          {t with bias := Bias.dyadic .neg i}).2
      = pairMassAboveQ (L := L) (K := K) h
          {s with bias := Bias.dyadic .pos i} {t with bias := Bias.dyadic .neg i}
        - 2 * weightQ (L := L) i := by
  simp [phase3CancelSplit, pairMassAboveQ, agentMassAboveQ, biasMassAboveQ, hi]
  ring

/-- Exact boundary split delta: splitting level `h-1` moves the mass to level `h`,
which is outside strict `μAbove_h`, so the drop is `w j`. -/
theorem p3_massAbove_split_boundary_delta_left (h : ℕ)
    (z b : AgentState L K) (sgn : Sign) (i : Fin (L + 1))
    (hz : z.bias = Bias.zero) (hb : b.bias = Bias.dyadic sgn i)
    (hgt : z.hour.val > i.val) (hboundary : i.val + 1 = h) :
    pairMassAboveQ (L := L) (K := K) h
        (phase3CancelSplit L K z b).1 (phase3CancelSplit L K z b).2
      = pairMassAboveQ (L := L) (K := K) h z b - weightQ (L := L) i := by
  have hiL : i.val < L := by
    have hle : z.hour.val ≤ L := by omega
    omega
  have hi : i.val < h := by omega
  have hnot : ¬ i.val + 1 < h := by omega
  cases sgn <;>
    simp [phase3CancelSplit, hz, hb, hgt, pairMassAboveQ,
      agentMassAboveQ, biasMassAboveQ, hi, hnot]

/-- Pair form: `μAbove_h` is nonincreasing for the concrete Phase-3 pair transition. -/
theorem p3_massAbove_pair_le (h : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    pairMassAboveQ (L := L) (K := K) h
        (Phase3Transition L K s t).1 (Phase3Transition L K s t).2
      ≤ pairMassAboveQ (L := L) (K := K) h s t := by
  classical
  let s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
    else if h_max : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else stdCounterSubroutine L K s
  else s
  let t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
    else if h_max : s.minute.val < K * (L + 1) then t
    else stdCounterSubroutine L K t
  else t
  let s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1 : agentMassAboveQ (L := L) (K := K) h s1 = agentMassAboveQ (L := L) (K := K) h s := by
    dsimp [s1, agentMassAboveQ, biasMassAboveQ]
    split_ifs <;> simp [stdCounterSubroutine_preserves_bias_of_phase_three, hs]
  have ht1 : agentMassAboveQ (L := L) (K := K) h t1 = agentMassAboveQ (L := L) (K := K) h t := by
    dsimp [t1, agentMassAboveQ, biasMassAboveQ]
    split_ifs <;> simp [stdCounterSubroutine_preserves_bias_of_phase_three, ht]
  have hs2 : agentMassAboveQ (L := L) (K := K) h s2 = agentMassAboveQ (L := L) (K := K) h s1 := by
    dsimp [s2, agentMassAboveQ, biasMassAboveQ]
    split_ifs <;> simp
  have ht2 : agentMassAboveQ (L := L) (K := K) h t2 = agentMassAboveQ (L := L) (K := K) h t1 := by
    dsimp [t2, agentMassAboveQ, biasMassAboveQ]
    split_ifs <;> simp
  have hfinal :
      pairMassAboveQ (L := L) (K := K) h
          (Phase3Transition L K s t).1 (Phase3Transition L K s t).2
        ≤ pairMassAboveQ (L := L) (K := K) h s2 t2 := by
    unfold Phase3Transition
    change pairMassAboveQ (L := L) (K := K) h
        (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2 else (s2, t2)).1
        (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2 else (s2, t2)).2
      ≤ pairMassAboveQ (L := L) (K := K) h s2 t2
    by_cases hmain : s2.role = .main ∧ t2.role = .main
    · simpa [hmain] using phase3CancelSplit_massAbove_pair_le (L := L) (K := K) h s2 t2
    · simp [hmain]
  calc
    pairMassAboveQ (L := L) (K := K) h
        (Phase3Transition L K s t).1 (Phase3Transition L K s t).2
        ≤ pairMassAboveQ (L := L) (K := K) h s2 t2 := hfinal
    _ = pairMassAboveQ (L := L) (K := K) h s1 t1 := by simp [pairMassAboveQ, hs2, ht2]
    _ = pairMassAboveQ (L := L) (K := K) h s t := by simp [pairMassAboveQ, hs1, ht1]

/-- Config step form: weighted `μAbove_h` is nonincreasing. -/
theorem p3_massAbove_step_le {c c' : Config (AgentState L K)} (h : ℕ)
    (hc3 : ∀ a ∈ c, a.phase.val = 3)
    (hstep : (P3Protocol L K).StepRel c c') :
    massAboveQ (L := L) (K := K) h c' ≤ massAboveQ (L := L) (K := K) h c := by
  unfold massAboveQ
  refine stepRel_sumOf_le_of_pair (P := P3Protocol L K) ?_ hstep
  intro r₁ r₂ happ
  have hr₁ : r₁.phase.val = 3 := hc3 r₁ (mem_left_of_applicable happ)
  have hr₂ : r₂.phase.val = 3 := hc3 r₂ (mem_right_of_applicable happ)
  simpa [P3Protocol, pairMassAboveQ] using
    p3_massAbove_pair_le (L := L) (K := K) h r₁ r₂ hr₁ hr₂

/-! ## `φ(> -h)` split delta -/

/-- Per-agent `φ` weight for level `j < h`: `4^(h-1-j)`. -/
noncomputable def phiBiasWeightQ (h : ℕ) : Bias L → ℚ
  | .zero => 0
  | .dyadic _ i => if i.val < h then (4 : ℚ) ^ (h - 1 - i.val) else 0

noncomputable def agentPhiAboveQ (h : ℕ) (a : AgentState L K) : ℚ :=
  phiBiasWeightQ (L := L) h a.bias

noncomputable def phiAboveQ (h : ℕ) (c : Config (AgentState L K)) : ℚ :=
  Config.sumOf (agentPhiAboveQ (L := L) (K := K) h) c

noncomputable def pairPhiAboveQ (h : ℕ) (s t : AgentState L K) : ℚ :=
  agentPhiAboveQ (L := L) (K := K) h s + agentPhiAboveQ (L := L) (K := K) h t

private lemma phi_succ_pair_le_half (h i : ℕ) (hi : i < h) :
    (if i + 1 < h then (4 : ℚ) ^ (h - 1 - (i + 1)) else 0) +
      (if i + 1 < h then (4 : ℚ) ^ (h - 1 - (i + 1)) else 0)
      ≤ (4 : ℚ) ^ (h - 1 - i) - (1 / 2 : ℚ) * (4 : ℚ) ^ (h - 1 - i) := by
  by_cases hsucc : i + 1 < h
  · have hsub : h - 1 - i = (h - 1 - (i + 1)) + 1 := by omega
    simp only [hsucc, if_true]
    rw [hsub, pow_succ]
    ring_nf
    exact le_rfl
  · have hpow0 : h - 1 - i = 0 := by omega
    simp [hsucc, hpow0]
    norm_num

/-- Split-potential delta. If a split fires from level `j < h`, then
`φ(> -h)` drops by at least `1/2 * 4^(h-1-j)`. -/
theorem p3_phiAbove_split_delta_left (h : ℕ)
    (z b : AgentState L K) (sgn : Sign) (i : Fin (L + 1))
    (hz : z.bias = Bias.zero) (hb : b.bias = Bias.dyadic sgn i)
    (hgt : z.hour.val > i.val) (hi : i.val < h) :
    pairPhiAboveQ (L := L) (K := K) h
        (phase3CancelSplit L K z b).1 (phase3CancelSplit L K z b).2
      ≤ pairPhiAboveQ (L := L) (K := K) h z b
          - (1 / 2 : ℚ) * (4 : ℚ) ^ (h - 1 - i.val) := by
  have hiL : i.val < L := by
    have hle : z.hour.val ≤ L := by omega
    omega
  cases sgn <;>
    simp [phase3CancelSplit, hz, hb, hgt, pairPhiAboveQ,
      agentPhiAboveQ, phiBiasWeightQ, hi] <;>
    simpa [one_div] using phi_succ_pair_le_half h i.val hi

/-- Symmetric split-potential delta. -/
theorem p3_phiAbove_split_delta_right (h : ℕ)
    (b z : AgentState L K) (sgn : Sign) (i : Fin (L + 1))
    (hb : b.bias = Bias.dyadic sgn i) (hz : z.bias = Bias.zero)
    (hgt : z.hour.val > i.val) (hi : i.val < h) :
    pairPhiAboveQ (L := L) (K := K) h
        (phase3CancelSplit L K b z).1 (phase3CancelSplit L K b z).2
      ≤ pairPhiAboveQ (L := L) (K := K) h b z
          - (1 / 2 : ℚ) * (4 : ℚ) ^ (h - 1 - i.val) := by
  have hiL : i.val < L := by
    have hle : z.hour.val ≤ L := by omega
    omega
  cases sgn <;>
    simp [phase3CancelSplit, hb, hz, hgt, pairPhiAboveQ,
      agentPhiAboveQ, phiBiasWeightQ, hi] <;>
    simpa [one_div] using phi_succ_pair_le_half h i.val hi

#print axioms p3_biasSum_step_eq
#print axioms p3_totalMass_step_le
#print axioms p3_massAbove_step_le
#print axioms p3_phiAbove_split_delta_left
#print axioms p3_phiAbove_split_delta_right

end P3DeterministicAlgebra
end ExactMajority
