import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Basic
import Ripple.sCRNUniversality.Core.Embedding
import Ripple.sCRNUniversality.Core.Run

open scoped BigOperators

namespace Ripple.sCRNUniversality

namespace Complex

variable {S : Type u} [Fintype S]

def size (c : Complex S) : Nat :=
  Finset.univ.sum c

@[simp]
theorem size_add (x y : Complex S) :
    Complex.size (State.add x y) = Complex.size x + Complex.size y := by
  classical
  simp [Complex.size, State.add, Finset.sum_add_distrib]

@[simp]
theorem size_single [DecidableEq S] (s : S) (n : Nat) :
    Complex.size (State.single s n : Complex S) = n := by
  classical
  unfold Complex.size State.single
  calc
    (Finset.univ : Finset S).sum (fun t => if t = s then n else 0)
        = (if s = s then n else 0) := by
          refine Finset.sum_eq_single s ?_ ?_
          · intro b _hb hbs
            simp [hbs]
          · intro hs
            exact False.elim (hs (Finset.mem_univ s))
    _ = n := by simp

@[simp]
theorem size_embed {T : Type v} [Fintype T] [DecidableEq T]
    (e : S -> T) (c : Complex S) :
    Complex.size (State.embed e c) = Complex.size c := by
  classical
  unfold Complex.size State.embed
  calc
    (Finset.univ : Finset T).sum
        (fun t => ((Finset.univ : Finset S).filter (fun s : S => e s = t)).sum
          (fun s => c s))
        = ∑ t : T, ∑ s : S, if e s = t then c s else 0 := by
            apply Finset.sum_congr rfl
            intro t _ht
            rw [Finset.sum_filter]
    _ = ∑ s : S, ∑ t : T, if e s = t then c s else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ s : S, c s := by
            apply Finset.sum_congr rfl
            intro s _hs
            have hsingle :
                (∑ t : T, if e s = t then c s else 0) =
                  (if e s = e s then c s else 0) := by
              refine Finset.sum_eq_single (e s) ?_ ?_
              · intro t _ht htne
                have hne : e s ≠ t := by
                  intro h
                  exact htne h.symm
                simp [hne]
              · intro hnot
                exact False.elim (hnot (Finset.mem_univ (e s)))
            have hsingle' :
                (∑ t : T, if e s = t then c s else 0) = c s := by
              exact hsingle.trans (by simp)
            exact hsingle'

end Complex

namespace Reaction

variable {S : Type u} [Fintype S]

def inputArity (rho : Reaction S) : Nat :=
  Complex.size rho.l

def outputArity (rho : Reaction S) : Nat :=
  Complex.size rho.r

def isUnaryInput (rho : Reaction S) : Prop :=
  rho.inputArity = 1

def isBimolecularInput (rho : Reaction S) : Prop :=
  rho.inputArity = 2

def isAtMostBimolecularInput (rho : Reaction S) : Prop :=
  rho.inputArity <= 2

def isAtMostBimolecularOutput (rho : Reaction S) : Prop :=
  rho.outputArity <= 2

def isAtMostBimolecularFull (rho : Reaction S) : Prop :=
  rho.isAtMostBimolecularInput /\ rho.isAtMostBimolecularOutput

theorem isAtMostBimolecularInput_of_isBimolecularInput
    {rho : Reaction S}
    (h : rho.isBimolecularInput) :
    rho.isAtMostBimolecularInput :=
  le_of_eq h

@[simp]
theorem embed_k {T : Type v} [DecidableEq T]
    (e : S -> T) (rho : Reaction S) :
    (Reaction.embed e rho).k = rho.k := by
  rfl

@[simp]
theorem embed_unitRate_iff {T : Type v} [DecidableEq T]
    (e : S -> T) (rho : Reaction S) :
    (Reaction.embed e rho).unitRate <-> rho.unitRate := by
  rfl

@[simp]
theorem embed_hasPositiveRate_iff {T : Type v} [DecidableEq T]
    (e : S -> T) (rho : Reaction S) :
    (Reaction.embed e rho).hasPositiveRate <-> rho.hasPositiveRate := by
  rfl

@[simp]
theorem inputArity_embed {T : Type v} [Fintype T] [DecidableEq T]
    (e : S -> T) (rho : Reaction S) :
    (Reaction.embed e rho).inputArity = rho.inputArity := by
  simp [Reaction.inputArity, Reaction.embed]

@[simp]
theorem outputArity_embed {T : Type v} [Fintype T] [DecidableEq T]
    (e : S -> T) (rho : Reaction S) :
    (Reaction.embed e rho).outputArity = rho.outputArity := by
  simp [Reaction.outputArity, Reaction.embed]

@[simp]
theorem isUnaryInput_embed_iff {T : Type v} [Fintype T] [DecidableEq T]
    (e : S -> T) (rho : Reaction S) :
    (Reaction.embed e rho).isUnaryInput <-> rho.isUnaryInput := by
  simp [Reaction.isUnaryInput]

@[simp]
theorem isBimolecularInput_embed_iff {T : Type v} [Fintype T] [DecidableEq T]
    (e : S -> T) (rho : Reaction S) :
    (Reaction.embed e rho).isBimolecularInput <-> rho.isBimolecularInput := by
  simp [Reaction.isBimolecularInput]

@[simp]
theorem isAtMostBimolecularInput_embed_iff {T : Type v} [Fintype T] [DecidableEq T]
    (e : S -> T) (rho : Reaction S) :
    (Reaction.embed e rho).isAtMostBimolecularInput <->
      rho.isAtMostBimolecularInput := by
  simp [Reaction.isAtMostBimolecularInput]

@[simp]
theorem isAtMostBimolecularOutput_embed_iff
    {T : Type v} [Fintype T] [DecidableEq T]
    (e : S -> T) (rho : Reaction S) :
    (Reaction.embed e rho).isAtMostBimolecularOutput <->
      rho.isAtMostBimolecularOutput := by
  simp [Reaction.isAtMostBimolecularOutput]

@[simp]
theorem isAtMostBimolecularFull_embed_iff
    {T : Type v} [Fintype T] [DecidableEq T]
    (e : S -> T) (rho : Reaction S) :
    (Reaction.embed e rho).isAtMostBimolecularFull <->
      rho.isAtMostBimolecularFull := by
  simp [Reaction.isAtMostBimolecularFull]

end Reaction

namespace Network

variable {S : Type u} [Fintype S]

def allAtMostBimolecularInput (N : Network S) : Prop :=
  forall i : N.I, (N.rxn i).isAtMostBimolecularInput

def allAtMostBimolecularOutput (N : Network S) : Prop :=
  forall i : N.I, (N.rxn i).isAtMostBimolecularOutput

def allAtMostBimolecularFull (N : Network S) : Prop :=
  forall i : N.I, (N.rxn i).isAtMostBimolecularFull

def allBimolecularInput (N : Network S) : Prop :=
  forall i : N.I, (N.rxn i).isBimolecularInput

theorem allAtMostBimolecularInput_of_allBimolecularInput
    {N : Network S}
    (h : N.allBimolecularInput) :
    N.allAtMostBimolecularInput := by
  intro i
  exact Reaction.isAtMostBimolecularInput_of_isBimolecularInput (h i)

theorem allAtMostBimolecularInput_of_full {N : Network S}
    (h : N.allAtMostBimolecularFull) :
    N.allAtMostBimolecularInput := by
  intro i
  exact (h i).1

theorem allAtMostBimolecularOutput_of_full {N : Network S}
    (h : N.allAtMostBimolecularFull) :
    N.allAtMostBimolecularOutput := by
  intro i
  exact (h i).2

theorem allAtMostBimolecularFull_iff (N : Network S) :
    N.allAtMostBimolecularFull <->
      N.allAtMostBimolecularInput /\ N.allAtMostBimolecularOutput := by
  constructor
  · intro h
    exact ⟨allAtMostBimolecularInput_of_full h,
      allAtMostBimolecularOutput_of_full h⟩
  · rintro ⟨hin, hout⟩ i
    exact ⟨hin i, hout i⟩

@[simp]
theorem embed_allUnitRate_iff {T : Type v} [DecidableEq T]
    (e : S -> T) (N : Network S) :
    (Network.embed e N).allUnitRate <-> N.allUnitRate := by
  constructor
  · intro h i
    simpa [Network.embed] using h i
  · intro h i
    simpa [Network.embed] using h i

@[simp]
theorem embed_hasPositiveRates_iff {T : Type v} [DecidableEq T]
    (e : S -> T) (N : Network S) :
    (Network.embed e N).hasPositiveRates <-> N.hasPositiveRates := by
  constructor
  · intro h i
    simpa [Network.embed] using h i
  · intro h i
    simpa [Network.embed] using h i

@[simp]
theorem embed_equalRates_iff {T : Type v} [DecidableEq T]
    (e : S -> T) (N : Network S) :
    (Network.embed e N).equalRates <-> N.equalRates := by
  constructor
  · intro h i j
    simpa [Network.embed, Reaction.embed] using h i j
  · intro h i j
    simpa [Network.embed, Reaction.embed] using h i j

@[simp]
theorem embed_allAtMostBimolecularInput_iff {T : Type v}
    [Fintype T] [DecidableEq T]
    (e : S -> T) (N : Network S) :
    (Network.embed e N).allAtMostBimolecularInput <->
      N.allAtMostBimolecularInput := by
  constructor
  · intro h i
    simpa [Network.embed] using h i
  · intro h i
    simpa [Network.embed] using h i

@[simp]
theorem embed_allAtMostBimolecularOutput_iff {T : Type v}
    [Fintype T] [DecidableEq T]
    (e : S -> T) (N : Network S) :
    (Network.embed e N).allAtMostBimolecularOutput <->
      N.allAtMostBimolecularOutput := by
  constructor
  · intro h i
    simpa [Network.embed] using h i
  · intro h i
    simpa [Network.embed] using h i

@[simp]
theorem embed_allAtMostBimolecularFull_iff {T : Type v}
    [Fintype T] [DecidableEq T]
    (e : S -> T) (N : Network S) :
    (Network.embed e N).allAtMostBimolecularFull <->
      N.allAtMostBimolecularFull := by
  constructor
  · intro h i
    simpa [Network.embed] using h i
  · intro h i
    simpa [Network.embed] using h i

@[simp]
theorem embed_allBimolecularInput_iff {T : Type v}
    [Fintype T] [DecidableEq T]
    (e : S -> T) (N : Network S) :
    (Network.embed e N).allBimolecularInput <-> N.allBimolecularInput := by
  constructor
  · intro h i
    simpa [Network.embed] using h i
  · intro h i
    simpa [Network.embed] using h i

omit [Fintype S] in
theorem parallel_hasPositiveRates_iff (N M : Network S) :
    (N.parallel M).hasPositiveRates <->
      N.hasPositiveRates /\ M.hasPositiveRates := by
  constructor
  · intro h
    constructor
    · intro i
      exact h (Sum.inl i)
    · intro i
      exact h (Sum.inr i)
  · rintro ⟨hN, hM⟩ i
    cases i with
    | inl i =>
        exact hN i
    | inr i =>
        exact hM i

omit [Fintype S] in
theorem parallel_allUnitRate_iff (N M : Network S) :
    (N.parallel M).allUnitRate <->
      N.allUnitRate /\ M.allUnitRate := by
  constructor
  · intro h
    constructor
    · intro i
      exact h (Sum.inl i)
    · intro i
      exact h (Sum.inr i)
  · rintro ⟨hN, hM⟩ i
    cases i with
    | inl i =>
        exact hN i
    | inr i =>
        exact hM i

omit [Fintype S] in
theorem parallel_equalRates_iff (N M : Network S) :
    (N.parallel M).equalRates <->
      N.equalRates /\ M.equalRates /\
        (forall i : N.I, forall j : M.I,
          (N.rxn i).k = (M.rxn j).k) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      exact h (Sum.inl i) (Sum.inl j)
    · intro i j
      exact h (Sum.inr i) (Sum.inr j)
    · intro i j
      exact h (Sum.inl i) (Sum.inr j)
  · rintro ⟨hN, hM, hCross⟩ i j
    cases i with
    | inl i =>
        cases j with
        | inl j => exact hN i j
        | inr j => exact hCross i j
    | inr i =>
        cases j with
        | inl j => exact (hCross j i).symm
        | inr j => exact hM i j

theorem parallel_allAtMostBimolecularInput_iff (N M : Network S) :
    (N.parallel M).allAtMostBimolecularInput <->
      N.allAtMostBimolecularInput /\ M.allAtMostBimolecularInput := by
  constructor
  · intro h
    constructor
    · intro i
      exact h (Sum.inl i)
    · intro i
      exact h (Sum.inr i)
  · rintro ⟨hN, hM⟩ i
    cases i with
    | inl i =>
        exact hN i
    | inr i =>
        exact hM i

theorem parallel_allAtMostBimolecularOutput_iff (N M : Network S) :
    (N.parallel M).allAtMostBimolecularOutput <->
      N.allAtMostBimolecularOutput /\ M.allAtMostBimolecularOutput := by
  constructor
  · intro h
    constructor
    · intro i
      exact h (Sum.inl i)
    · intro i
      exact h (Sum.inr i)
  · rintro ⟨hN, hM⟩ i
    cases i with
    | inl i =>
        exact hN i
    | inr i =>
        exact hM i

theorem parallel_allAtMostBimolecularFull_iff (N M : Network S) :
    (N.parallel M).allAtMostBimolecularFull <->
      N.allAtMostBimolecularFull /\ M.allAtMostBimolecularFull := by
  constructor
  · intro h
    constructor
    · intro i
      exact h (Sum.inl i)
    · intro i
      exact h (Sum.inr i)
  · rintro ⟨hN, hM⟩ i
    cases i with
    | inl i =>
        exact hN i
    | inr i =>
        exact hM i

theorem parallel_allBimolecularInput_iff (N M : Network S) :
    (N.parallel M).allBimolecularInput <->
      N.allBimolecularInput /\ M.allBimolecularInput := by
  constructor
  · intro h
    constructor
    · intro i
      exact h (Sum.inl i)
    · intro i
      exact h (Sum.inr i)
  · rintro ⟨hN, hM⟩ i
    cases i with
    | inl i =>
        exact hN i
    | inr i =>
        exact hM i

omit [Fintype S] in
theorem sigma_hasPositiveRates_iff
    {A : Type v} [Fintype A] (Ns : A -> Network S) :
    (Network.sigma Ns).hasPositiveRates <->
      forall a, (Ns a).hasPositiveRates := by
  constructor
  · intro h a i
    exact h ⟨a, i⟩
  · intro h idx
    cases idx with
    | mk a i => exact h a i

omit [Fintype S] in
theorem sigma_allUnitRate_iff
    {A : Type v} [Fintype A] (Ns : A -> Network S) :
    (Network.sigma Ns).allUnitRate <->
      forall a, (Ns a).allUnitRate := by
  constructor
  · intro h a i
    exact h ⟨a, i⟩
  · intro h idx
    cases idx with
    | mk a i => exact h a i

omit [Fintype S] in
theorem sigma_equalRates_iff
    {A : Type v} [Fintype A] (Ns : A -> Network S) :
    (Network.sigma Ns).equalRates <->
      forall (a b : A) (i : (Ns a).I) (j : (Ns b).I),
        ((Ns a).rxn i).k = ((Ns b).rxn j).k := by
  constructor
  · intro h a b i j
    exact h ⟨a, i⟩ ⟨b, j⟩
  · intro h idx jdx
    rcases idx with ⟨a, i⟩
    rcases jdx with ⟨b, j⟩
    exact h a b i j

theorem sigma_allAtMostBimolecularInput_iff
    {A : Type v} [Fintype A] (Ns : A -> Network S) :
    (Network.sigma Ns).allAtMostBimolecularInput <->
      forall a, (Ns a).allAtMostBimolecularInput := by
  constructor
  · intro h a i
    exact h ⟨a, i⟩
  · intro h idx
    cases idx with
    | mk a i => exact h a i

theorem sigma_allAtMostBimolecularOutput_iff
    {A : Type v} [Fintype A] (Ns : A -> Network S) :
    (Network.sigma Ns).allAtMostBimolecularOutput <->
      forall a, (Ns a).allAtMostBimolecularOutput := by
  constructor
  · intro h a i
    exact h ⟨a, i⟩
  · intro h idx
    cases idx with
    | mk a i => exact h a i

theorem sigma_allAtMostBimolecularFull_iff
    {A : Type v} [Fintype A] (Ns : A -> Network S) :
    (Network.sigma Ns).allAtMostBimolecularFull <->
      forall a, (Ns a).allAtMostBimolecularFull := by
  constructor
  · intro h a i
    exact h ⟨a, i⟩
  · intro h idx
    cases idx with
    | mk a i => exact h a i

theorem sigma_allBimolecularInput_iff
    {A : Type v} [Fintype A] (Ns : A -> Network S) :
    (Network.sigma Ns).allBimolecularInput <->
      forall a, (Ns a).allBimolecularInput := by
  constructor
  · intro h a i
    exact h ⟨a, i⟩
  · intro h idx
    cases idx with
    | mk a i => exact h a i

end Network

end Ripple.sCRNUniversality
