/-
# State simulation between population protocols on the multiset model

A protocol `P'` on states `Λ'` simulates `P` on `Λ` when there are maps `enc : Λ → Λ'`,
`emb : Λ' → Λ` and an invariant `Good` on `Λ` such that `enc ∘ emb = id`, `emb` lands in `Good`,
`Good` is closed under `P.δ`, and on good states `enc` commutes with the transition. Then every
execution of `P'` lifts to an execution of `P` and conversely (on good configurations), and
`StablyComputes` transfers from `P` to `P'` for every validity predicate on `P'` whose
decoding is valid for `P`.

This is the multiset-model analogue of `SSEM.StateSimulation`
(`Ripple/PopulationProtocol/SSEM/Convergence/FiniteStatePEM.lean`), used to move the Doty et al.
protocol from the flat `AgentState L K` to the compact `O(L)` state type
(`ExactMajority/Compact/`).
-/

import Ripple.PopulationProtocol.ExactMajority.Basic.PopulationProtocol

namespace Ripple.PopulationProtocol.ExactMajority

variable {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']

/-- `P'` simulates `P` on the good states: `Good` is closed under the transition, `emb` lands in
`Good`, `enc ∘ emb = id`, and on good states `enc` commutes with the transition. -/
structure StateSimulation (P : Protocol Λ) (P' : Protocol Λ') where
  Good : Λ → Prop
  enc : Λ → Λ'
  emb : Λ' → Λ
  good_emb : ∀ q, Good (emb q)
  enc_emb : ∀ q, enc (emb q) = q
  good_δ : ∀ a b, Good a → Good b → Good (P.δ a b).1 ∧ Good (P.δ a b).2
  enc_δ : ∀ a b, Good a → Good b →
    P'.δ (enc a) (enc b) = (enc (P.δ a b).1, enc (P.δ a b).2)

namespace StateSimulation

variable {P : Protocol Λ} {P' : Protocol Λ'} (S : StateSimulation P P')

/-- Encode a configuration agentwise. -/
def encC (c : Config Λ) : Config Λ' := c.map S.enc

/-- Decode a configuration agentwise. -/
def embC (D : Config Λ') : Config Λ := D.map S.emb

/-- Every agent of `c` is good. -/
def GoodC (c : Config Λ) : Prop := ∀ a ∈ c, S.Good a

@[simp] lemma encC_embC (D : Config Λ') : S.encC (S.embC D) = D := by
  simp [encC, embC, Multiset.map_map, S.enc_emb]

lemma goodC_embC (D : Config Λ') : S.GoodC (S.embC D) := by
  intro a ha
  rcases Multiset.mem_map.mp ha with ⟨q, _, rfl⟩
  exact S.good_emb q

@[simp] lemma card_encC (c : Config Λ) : (S.encC c).card = c.card := Multiset.card_map _ _

@[simp] lemma card_embC (D : Config Λ') : (S.embC D).card = D.card := Multiset.card_map _ _

lemma encC_sub (c s : Config Λ) (hs : s ≤ c) : S.encC (c - s) = S.encC c - S.encC s := by
  have h : c = (c - s) + s := (tsub_add_cancel_of_le hs).symm
  calc S.encC (c - s) = S.encC (c - s) + S.encC s - S.encC s := by
        rw [add_tsub_cancel_right]
    _ = S.encC ((c - s) + s) - S.encC s := by rw [encC, encC, encC, Multiset.map_add]
    _ = S.encC c - S.encC s := by rw [← h]

lemma encC_add (c s : Config Λ) : S.encC (c + s) = S.encC c + S.encC s :=
  Multiset.map_add _ _ _

@[simp] lemma encC_pair (a b : Λ) : S.encC ({a, b} : Config Λ) = {S.enc a, S.enc b} := by
  simp [encC]

/-- A good step of `P` encodes to a step of `P'`. -/
theorem stepRel_encC {c c' : Config Λ} (hc : S.GoodC c) (h : P.StepRel c c') :
    P'.StepRel (S.encC c) (S.encC c') := by
  rcases h with ⟨r₁, r₂, happ, hc'⟩
  refine ⟨S.enc r₁, S.enc r₂, ?_, ?_⟩
  · have := Multiset.map_le_map (f := S.enc) happ
    simpa [encC] using this
  · have h1 : S.Good r₁ := hc r₁ (Multiset.subset_of_le happ (by simp))
    have h2 : S.Good r₂ := hc r₂ (Multiset.subset_of_le happ (by simp))
    change S.encC c' = S.encC c - {S.enc r₁, S.enc r₂} +
      {(P'.δ (S.enc r₁) (S.enc r₂)).1, (P'.δ (S.enc r₁) (S.enc r₂)).2}
    rw [S.enc_δ r₁ r₂ h1 h2]
    simp only at hc'
    rw [hc', encC_add, encC_sub S c _ happ, encC_pair, encC_pair]

/-- Goodness is preserved by a step. -/
theorem goodC_step {c c' : Config Λ} (hc : S.GoodC c) (h : P.StepRel c c') : S.GoodC c' := by
  rcases h with ⟨r₁, r₂, happ, hc'⟩
  simp only at hc'
  subst hc'
  have h1 : S.Good r₁ := hc r₁ (Multiset.subset_of_le happ (by simp))
  have h2 : S.Good r₂ := hc r₂ (Multiset.subset_of_le happ (by simp))
  intro a ha
  rcases Multiset.mem_add.mp ha with ha | ha
  · exact hc a (Multiset.subset_of_le (Multiset.sub_le_self _ _) ha)
  · have ha' : a = (P.δ r₁ r₂).1 ∨ a = (P.δ r₁ r₂).2 := by simpa using ha
    rcases ha' with rfl | rfl
    · exact (S.good_δ r₁ r₂ h1 h2).1
    · exact (S.good_δ r₁ r₂ h1 h2).2

/-- A good execution of `P` encodes to an execution of `P'`, and stays good. -/
theorem reachable_encC {c c' : Config Λ} (hc : S.GoodC c) (h : P.Reachable c c') :
    P'.Reachable (S.encC c) (S.encC c') ∧ S.GoodC c' := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hc⟩
  | tail _ hstep ih =>
    exact ⟨Relation.ReflTransGen.tail ih.1 (S.stepRel_encC ih.2 hstep), S.goodC_step ih.2 hstep⟩

/-- Two states of an encoded configuration come from two states of the configuration. -/
lemma exists_pair_of_le_encC {c : Config Λ} {x y : Λ'} (h : ({x, y} : Config Λ') ≤ S.encC c) :
    ∃ a b, ({a, b} : Config Λ) ≤ c ∧ S.enc a = x ∧ S.enc b = y := by
  have hx : x ∈ S.encC c := Multiset.subset_of_le h (by simp)
  rcases Multiset.mem_map.mp hx with ⟨a, ha, rfl⟩
  have ha' : ({a} : Config Λ) ≤ c := Multiset.singleton_le.mpr ha
  have hy : y ∈ S.encC c - {S.enc a} := by
    have : ({S.enc a} : Config Λ') + {y} ≤ S.encC c := by
      simpa [Multiset.insert_eq_cons, Multiset.singleton_add] using h
    exact Multiset.singleton_le.mp (le_tsub_of_add_le_left this)
  have hsub : S.encC c - {S.enc a} = S.encC (c - {a}) := by
    rw [encC_sub S c _ ha']
    simp [encC]
  rw [hsub] at hy
  rcases Multiset.mem_map.mp hy with ⟨b, hb, rfl⟩
  refine ⟨a, b, ?_, rfl, rfl⟩
  have hb' : ({b} : Config Λ) ≤ c - {a} := Multiset.singleton_le.mpr hb
  have : ({a} : Config Λ) + {b} ≤ {a} + (c - {a}) := add_le_add (le_refl _) hb'
  rw [add_tsub_cancel_of_le ha'] at this
  simpa [Multiset.insert_eq_cons, Multiset.singleton_add] using this

/-- A step of `P'` from an encoded good configuration lifts to a step of `P`. -/
theorem lift_step {c : Config Λ} {C' : Config Λ'} (hc : S.GoodC c)
    (h : P'.StepRel (S.encC c) C') :
    ∃ c', P.StepRel c c' ∧ S.encC c' = C' := by
  rcases h with ⟨x, y, happ, hC'⟩
  rcases S.exists_pair_of_le_encC happ with ⟨a, b, hab, rfl, rfl⟩
  have h1 : S.Good a := hc a (Multiset.subset_of_le hab (by simp))
  have h2 : S.Good b := hc b (Multiset.subset_of_le hab (by simp))
  refine ⟨c - {a, b} + {(P.δ a b).1, (P.δ a b).2}, ⟨a, b, hab, rfl⟩, ?_⟩
  simp only at hC'
  rw [hC']
  change S.encC (c - {a, b} + {(P.δ a b).1, (P.δ a b).2}) = S.encC c - {S.enc a, S.enc b} +
    {(P'.δ (S.enc a) (S.enc b)).1, (P'.δ (S.enc a) (S.enc b)).2}
  rw [S.enc_δ a b h1 h2, encC_add, encC_sub S c _ hab, encC_pair, encC_pair]

/-- An execution of `P'` from an encoded good configuration lifts to a good execution of `P`. -/
theorem lift_reachable {c : Config Λ} {C' : Config Λ'} (hc : S.GoodC c)
    (h : P'.Reachable (S.encC c) C') :
    ∃ c', P.Reachable c c' ∧ S.encC c' = C' ∧ S.GoodC c' := by
  induction h with
  | refl => exact ⟨c, Relation.ReflTransGen.refl, rfl, hc⟩
  | tail _ hstep ih =>
    rcases ih with ⟨c₁, hreach, rfl, hgood⟩
    rcases S.lift_step hgood hstep with ⟨c₂, hstep₂, rfl⟩
    exact ⟨c₂, Relation.ReflTransGen.tail hreach hstep₂, rfl, S.goodC_step hgood hstep₂⟩

/-- Output agreement of two partitions along the encoding (on good states). -/
def OutputCompat (part : OutputPartition Λ) (part' : OutputPartition Λ') : Prop :=
  ∀ a, S.Good a →
    (part'.isA (S.enc a), part'.isB (S.enc a), part'.isT (S.enc a)) =
      (part.isA a, part.isB a, part.isT a)

lemma output_encC {part : OutputPartition Λ} {part' : OutputPartition Λ'}
    (hcompat : S.OutputCompat part part') {c : Config Λ} (hc : S.GoodC c) (u : Bool × Bool × Bool)
    (h : part.output u c) : part'.output u (S.encC c) := by
  intro s hs
  rcases Multiset.mem_map.mp hs with ⟨a, ha, rfl⟩
  rw [hcompat a (hc a ha)]
  exact h a ha

/-- **Transfer of stable computation.** If `P` stably computes `target` on `valid`, and every
`P'`-valid configuration decodes to a `P`-valid one with the same target, then `P'` stably
computes `target'` on `valid'`. -/
theorem stablyComputes {part : OutputPartition Λ} {part' : OutputPartition Λ'}
    (hcompat : S.OutputCompat part part')
    {valid : Config Λ → Prop} {valid' : Config Λ' → Prop}
    {target : Config Λ → Bool × Bool × Bool} {target' : Config Λ' → Bool × Bool × Bool}
    (hvalid : ∀ D, valid' D → valid (S.embC D))
    (htarget : ∀ D, valid' D → target' D = target (S.embC D))
    (h : P.StablyComputes part valid target) :
    P'.StablyComputes part' valid' target' := by
  intro D hD C hDC
  have hgood : S.GoodC (S.embC D) := S.goodC_embC D
  rw [← S.encC_embC D] at hDC
  rcases S.lift_reachable hgood hDC with ⟨c, hreach, rfl, hgoodc⟩
  rcases h (S.embC D) (hvalid D hD) c hreach with ⟨o, hco, hout, hstable⟩
  rcases S.reachable_encC hgoodc hco with ⟨hco', hgoodo⟩
  refine ⟨S.encC o, hco', ?_, ?_⟩
  · rw [htarget D hD]
    exact S.output_encC hcompat hgoodo _ hout
  · rcases hstable with ⟨u, hu, hstab⟩
    refine ⟨u, S.output_encC hcompat hgoodo u hu, ?_⟩
    intro C' hC'
    rcases S.lift_reachable hgoodo hC' with ⟨o', hoo', rfl, hgoodo'⟩
    exact S.output_encC hcompat hgoodo' u (hstab o' hoo')

end StateSimulation

end Ripple.PopulationProtocol.ExactMajority
