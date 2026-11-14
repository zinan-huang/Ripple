-- Ripple/PopulationProtocol/ExactMajority/Probability/LateF6PairHazards.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6Acceptance
import Ripple.PopulationProtocol.ExactMajority.Probability.PairLogAuxiliary

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateF6Hazards

open TimeTheorem PairLog PairLogAuxiliary LateF6Acceptance

variable {L K n : ℕ}

def pool (f : Fin n → AgentState L K) (P : AgentState L K → Prop) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => P (f i)

@[simp] theorem mem_pool (f : Fin n → AgentState L K)
    (P : AgentState L K → Prop) (i : Fin n) : i ∈ pool f P ↔ P (f i) := by
  classical
  simp [pool]

def contact (P Q : AgentState L K → Prop)
    (f : Fin n → AgentState L K) (i j : Fin n) : Prop :=
  (P (f i) ∧ Q (f j)) ∨ (Q (f i) ∧ P (f j))

def oriented (S T : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  S.product T ∪ T.product S

theorem pool_disjoint (f : Fin n → AgentState L K)
    (P Q : AgentState L K → Prop) (h : ∀ a, P a → Q a → False) :
    Disjoint (pool f P) (pool f Q) := by
  classical
  exact Finset.disjoint_left.mpr fun i hi hj =>
    h (f i) ((mem_pool f P i).mp hi) ((mem_pool f Q i).mp hj)

theorem oriented_card (S T : Finset (Fin n)) (hST : Disjoint S T) :
    (oriented S T).card = 2 * S.card * T.card := by
  classical
  have hd : Disjoint (S.product T) (T.product S) := by
    apply Finset.disjoint_left.mpr
    intro ij h h'
    exact Finset.disjoint_left.mp hST
      (Finset.mem_product.mp h).1 (Finset.mem_product.mp h').1
  rw [oriented, Finset.card_union_of_disjoint hd]
  simp only [Finset.product_eq_sprod, Finset.card_product]
  ring

theorem goodPairs_contact (f : Fin n → AgentState L K)
    (P Q : AgentState L K → Prop) (hPQ : ∀ a, P a → Q a → False) :
    goodPairs (contact P Q) f = oriented (pool f P) (pool f Q) := by
  classical
  ext ij
  rcases ij with ⟨i, j⟩
  simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    contact, oriented, Finset.mem_union, Finset.product_eq_sprod, Finset.mem_product, mem_pool]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    intro hij
    subst j
    rcases h with h | h
    · exact hPQ _ h.1 h.2
    · exact hPQ _ h.2 h.1

theorem contact_card (f : Fin n → AgentState L K)
    (P Q : AgentState L K → Prop) (hPQ : ∀ a, P a → Q a → False) :
    (goodPairs (contact P Q) f).card = 2 * (pool f P).card * (pool f Q).card := by
  rw [goodPairs_contact f P Q hPQ]
  exact oriented_card _ _ (pool_disjoint f P Q hPQ)

def bit (P : Prop) : ℝ := by classical exact if P then 1 else 0

def mask (P : Prop) (x : ℝ) : ℝ := by classical exact if P then x else 0

def pairIndicator (init : Cfg L K) (t : ℕ)
    (G : ((i : Finset.Iic t) → Draw L K) → Prop)
    (A : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop)
    (ω : Ω L K) : ℝ :=
  bit (G (frestrictLe t ω) ∧ ∃ i j,
    drawLabels init ω (t + 1) = some (i, j) ∧ A (labelsAt init ω t) i j)

def pairHazard (init : Cfg L K) (t : ℕ)
    (G : ((i : Finset.Iic t) → Draw L K) → Prop)
    (A : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop)
    (ω : Ω L K) : ℝ :=
  mask (G (frestrictLe t ω))
    (((goodPairs A (labelsAt init ω t)).card : ℝ) /
      ((init.card : ℝ) * ((init.card : ℝ) - 1)))

theorem pairIndicator_zero_one (init : Cfg L K) (t : ℕ)
    (G : ((i : Finset.Iic t) → Draw L K) → Prop)
    (A : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop)
    (ω : Ω L K) :
    pairIndicator init t G A ω = 0 ∨ pairIndicator init t G A ω = 1 := by
  classical
  unfold pairIndicator bit
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem prefix_gate_measurable (t : ℕ)
    (G : ((i : Finset.Iic t) → Draw L K) → Prop) :
    MeasurableSet[pairLogFiltration L K t] {ω : Ω L K | G (frestrictLe t ω)} :=
  (Set.to_countable {p | G p}).measurableSet.preimage (measurable_pairLog_prefix L K t)

theorem label_gate_measurable (init : Cfg L K) (t : ℕ)
    (G : (Fin init.card → AgentState L K) → Prop) :
    MeasurableSet[pairLogFiltration L K t] {ω | G (labelsAt init ω t)} := by
  exact prefix_gate_measurable t (fun p => G (prefixLabels init t p))

theorem pairIndicator_stronglyMeasurable (init : Cfg L K) (t : ℕ)
    (G : ((i : Finset.Iic t) → Draw L K) → Prop)
    (A : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop) :
    StronglyMeasurable[pairLogFiltration L K (t + 1)] (pairIndicator init t G A) := by
  classical
  let H : (((i : Finset.Iic t) → Draw L K) × Draw L K) → ℝ := fun z =>
    bit (G z.1 ∧ ∃ i j, selectLabels (prefixLabels init t z.1) z.2 = some (i, j) ∧
      A (prefixLabels init t z.1) i j)
  have hH : Measurable H := by
    intro S _
    exact (Set.to_countable _).measurableSet
  have hprefix : Measurable[pairLogFiltration L K (t + 1)]
      (frestrictLe (π := fun _ : ℕ => Draw L K) t) :=
    (measurable_pairLog_prefix L K t).mono
      ((pairLogFiltration L K).mono (Nat.le_succ t)) le_rfl
  have hnext : Measurable[pairLogFiltration L K (t + 1)]
      (fun ω : Ω L K => ω (t + 1)) := by
    exact (measurable_pi_apply (⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (t + 1))).comp
      (measurable_pairLog_prefix L K (t + 1))
  simpa only [H, pairIndicator, labelsAt, drawLabels_succ] using
    (hH.comp (hprefix.prodMk hnext)).stronglyMeasurable

theorem pool_partition (f : Fin n → AgentState L K)
    (P Q : AgentState L K → Prop) :
    (pool f (fun a => P a ∧ Q a)).card +
      (pool f (fun a => P a ∧ ¬ Q a)).card = (pool f P).card := by
  classical
  have hu : pool f (fun a => P a ∧ Q a) ∪
      pool f (fun a => P a ∧ ¬ Q a) = pool f P := by
    ext i
    simp only [Finset.mem_union, mem_pool]
    tauto
  have hd : Disjoint (pool f (fun a => P a ∧ Q a))
      (pool f (fun a => P a ∧ ¬ Q a)) := by
    exact pool_disjoint f _ _ (fun _ h h' => h'.2 h.2)
  rw [← Finset.card_union_of_disjoint hd, hu]

def bitNat (P : Prop) : ℕ := by classical exact if P then 1 else 0

theorem pool_updateLabels_balance (f : Fin n → AgentState L K)
    (P : AgentState L K → Prop) (i j : Fin n) (hij : i ≠ j) :
    (pool (PairLog.updateLabels f i j) P).card +
        bitNat (P (f i)) + bitNat (P (f j)) =
      (pool f P).card +
        bitNat (P (((NonuniformMajority L K).δ (f i) (f j)).1)) +
        bitNat (P (((NonuniformMajority L K).δ (f i) (f j)).2)) := by
  classical
  unfold bitNat
  let rest : Finset (Fin n) := (Finset.univ.erase i).erase j
  have hj : j ∉ rest := by simp [rest]
  have hi : i ∉ Finset.cons j rest hj := by simp [rest, hij]
  have hfin : Finset.cons i (Finset.cons j rest hj) hi = Finset.univ := by
    ext k
    by_cases hki : k = i
    · subst k; simp
    · by_cases hkj : k = j
      · subst k; simp
      · simp [rest, hki, hkj]
  have hsplit : (Finset.univ : Finset (Fin n)).val =
      i ::ₘ j ::ₘ rest.val := (congrArg Finset.val hfin).symm
  have hcount (g : Fin n → AgentState L K) :
      (pool g P).card = (rest.filter (fun k => P (g k))).card +
        (if P (g i) then 1 else 0) + (if P (g j) then 1 else 0) := by
    change ((Finset.univ : Finset (Fin n)).val.filter (fun k => P (g k))).card =
      (rest.val.filter (fun k => P (g k))).card +
        (if P (g i) then 1 else 0) + (if P (g j) then 1 else 0)
    rw [hsplit]
    by_cases hpi : P (g i) <;> by_cases hpj : P (g j) <;>
      simp [hpi, hpj, add_comm, add_left_comm, add_assoc]
  have hrest : rest.filter (fun k => P (PairLog.updateLabels f i j k)) =
      rest.filter (fun k => P (f k)) := by
    apply Finset.filter_congr
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    simp [PairLog.updateLabels, hki, hkj]
  rw [hcount (PairLog.updateLabels f i j), hcount f, hrest]
  simp [PairLog.updateLabels, hij, Ne.symm hij, add_comm, add_left_comm, add_assoc]

end Ripple.PopulationProtocol.ExactMajority.LateF6Hazards
end
