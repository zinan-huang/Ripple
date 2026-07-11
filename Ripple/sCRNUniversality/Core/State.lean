import Mathlib.Data.Nat.Basic

namespace Ripple.sCRNUniversality

abbrev State (S : Type u) := S -> Nat

abbrev Complex (S : Type u) := S -> Nat

namespace State

variable {S : Type u}

def zero : State S :=
  fun _ => 0

def add (x y : State S) : State S :=
  fun s => x s + y s

def sub (x y : State S) : State S :=
  fun s => x s - y s

@[simp]
theorem zero_apply (s : S) :
    (zero : State S) s = 0 := rfl

@[simp]
theorem add_apply (x y : State S) (s : S) :
    add x y s = x s + y s := rfl

@[simp]
theorem sub_apply (x y : State S) (s : S) :
    sub x y s = x s - y s := rfl

theorem add_assoc (x y z : State S) :
    add (add x y) z = add x (add y z) := by
  funext s
  simp [Nat.add_assoc]

theorem add_comm (x y : State S) :
    add x y = add y x := by
  funext s
  simp [Nat.add_comm]

theorem add_zero (x : State S) :
    add x zero = x := by
  funext s
  simp

theorem zero_add (x : State S) :
    add zero x = x := by
  funext s
  simp

def single [DecidableEq S] (s : S) (n : Nat := 1) : State S :=
  fun t => if t = s then n else 0

@[simp]
theorem single_zero [DecidableEq S] (s : S) :
    single s 0 = (zero : State S) := by
  funext t
  by_cases h : t = s <;> simp [single, zero, h]

@[simp]
theorem single_self [DecidableEq S] (s : S) (n : Nat) :
    single s n s = n := by
  simp [single]

@[simp]
theorem single_of_ne [DecidableEq S] {s t : S} (h : t ≠ s) (n : Nat) :
    single s n t = 0 := by
  simp [single, h]

end State

def Covers {S : Type u} (z target : State S) : Prop :=
  forall s, target s <= z s

theorem Covers.coord {S : Type u} {z target : State S}
    (h : Covers z target) (s : S) : target s <= z s :=
  h s

theorem Covers.refl {S : Type u} (z : State S) : Covers z z := by
  intro s
  exact le_rfl

theorem Covers.trans {S : Type u} {x y z : State S}
    (hxy : Covers x y) (hyz : Covers y z) : Covers x z := by
  intro s
  exact le_trans (hyz s) (hxy s)

theorem Covers.antisymm {S : Type u} {x y : State S}
    (hxy : Covers x y) (hyx : Covers y x) : x = y := by
  funext s
  exact Nat.le_antisymm (hyx s) (hxy s)

theorem Covers.single_iff {S : Type u} [DecidableEq S]
    {z : State S} {s : S} {n : Nat} :
    Covers z (State.single s n) <-> n <= z s := by
  constructor
  · intro h
    simpa using h s
  · intro hn t
    by_cases hts : t = s
    · subst hts
      simpa using hn
    · simp [State.single, hts]

theorem Covers.zero_right {S : Type u} (z : State S) :
    Covers z State.zero := by
  intro s
  simp [State.zero]

theorem Covers.add {S : Type u} {x y target target' : State S}
    (hx : Covers x target) (hy : Covers y target') :
    Covers (State.add x y) (State.add target target') := by
  intro s
  exact Nat.add_le_add (hx s) (hy s)

theorem Covers.add_left {S : Type u} {x y target : State S}
    (h : Covers x target) :
    Covers (State.add x y) target := by
  intro s
  exact le_trans (h s) (Nat.le_add_right (x s) (y s))

theorem Covers.add_right {S : Type u} {x y target : State S}
    (h : Covers y target) :
    Covers (State.add x y) target := by
  intro s
  exact le_trans (h s) (Nat.le_add_left (y s) (x s))

theorem Covers.single_mono {S : Type u} [DecidableEq S]
    {s : S} {m n : Nat} (h : m <= n) :
    Covers (State.single s n) (State.single s m) := by
  exact Covers.single_iff.mpr (by simpa using h)

theorem Covers.single_add_single {S : Type u} [DecidableEq S]
    {z : State S} {a b : S} {m n : Nat}
    (hab : a ≠ b)
    (ha : m <= z a) (hb : n <= z b) :
    Covers z (State.add (State.single a m) (State.single b n)) := by
  intro s
  by_cases hsa : s = a
  · subst hsa
    simp [State.add, State.single, hab, ha]
  · by_cases hsb : s = b
    · have hba : b ≠ a := by
        intro h
        exact hab h.symm
      simp [State.add, State.single, hsb, hba, hb]
    · simp [State.add, State.single, hsa, hsb]

theorem Covers.single_add_single_left {S : Type u} [DecidableEq S]
    {z : State S} {a b : S} {m n : Nat}
    (hab : a ≠ b)
    (h : Covers z (State.add (State.single a m) (State.single b n))) :
    m <= z a := by
  have hcoord := h a
  simpa [State.add, State.single, hab] using hcoord

theorem Covers.single_add_single_right {S : Type u} [DecidableEq S]
    {z : State S} {a b : S} {m n : Nat}
    (hab : a ≠ b)
    (h : Covers z (State.add (State.single a m) (State.single b n))) :
    n <= z b := by
  have hcoord := h b
  have hba : b ≠ a := by
    intro hEq
    exact hab hEq.symm
  simpa [State.add, State.single, hba] using hcoord

end Ripple.sCRNUniversality
