import Mathlib.Data.NNRat.Defs
import Ripple.sCRNUniversality.Core.State

namespace Ripple.sCRNUniversality

abbrev Rate := NNRat

structure Reaction (S : Type u) where
  l : Complex S
  r : Complex S
  k : Rate := 1

namespace Reaction

variable {S : Type u}

def enabled (rho : Reaction S) (z : State S) : Prop :=
  forall s, rho.l s <= z s

theorem enabled_iff_covers_l (rho : Reaction S) (z : State S) :
    rho.enabled z <-> Covers z rho.l := by
  rfl

theorem enabled_iff_covers_input (rho : Reaction S) (z : State S) :
    rho.enabled z <-> Covers z rho.l := by
  rfl

def fire (rho : Reaction S) (z : State S) : State S :=
  fun s => z s - rho.l s + rho.r s

def FiresTo (rho : Reaction S) (z z' : State S) : Prop :=
  rho.enabled z /\ z' = rho.fire z

def unitRate (rho : Reaction S) : Prop :=
  rho.k = 1

def hasPositiveRate (rho : Reaction S) : Prop :=
  0 < rho.k

def delta (rho : Reaction S) : S -> Int :=
  fun s => Int.ofNat (rho.r s) - Int.ofNat (rho.l s)

def Touches (rho : Reaction S) (s : S) : Prop :=
  rho.l s ≠ 0 ∨ rho.r s ≠ 0

@[simp]
theorem fire_apply (rho : Reaction S) (z : State S) (s : S) :
    rho.fire z s = z s - rho.l s + rho.r s := rfl

theorem fire_apply_of_enabled (rho : Reaction S) (z : State S)
    (_h : rho.enabled z) (s : S) :
    rho.fire z s = z s - rho.l s + rho.r s := rfl

theorem fire_apply_of_l_eq_r_of_le
    (rho : Reaction S) (z : State S) (s : S)
    (hEq : rho.l s = rho.r s)
    (hLe : rho.l s <= z s) :
    rho.fire z s = z s := by
  rw [Reaction.fire, hEq]
  exact Nat.sub_add_cancel (by simpa [hEq] using hLe)

theorem FiresTo.enabled {rho : Reaction S} {z z' : State S}
    (h : rho.FiresTo z z') : rho.enabled z :=
  h.1

theorem FiresTo.eq_fire {rho : Reaction S} {z z' : State S}
    (h : rho.FiresTo z z') : z' = rho.fire z :=
  h.2

theorem FiresTo.of_enabled_fire {rho : Reaction S} {z : State S}
    (h : rho.enabled z) :
    rho.FiresTo z (rho.fire z) :=
  ⟨h, rfl⟩

theorem FiresTo.of_covers_fire {rho : Reaction S} {z : State S}
    (h : Covers z rho.l) :
    rho.FiresTo z (rho.fire z) :=
  FiresTo.of_enabled_fire ((rho.enabled_iff_covers_input z).mpr h)

theorem FiresTo.apply {rho : Reaction S} {z z' : State S}
    (h : rho.FiresTo z z') (s : S) :
    z' s = z s - rho.l s + rho.r s := by
  rw [h.eq_fire]
  rfl

theorem FiresTo.covers_output {rho : Reaction S} {z z' : State S}
    (h : rho.FiresTo z z') :
    Covers z' rho.r := by
  intro s
  rw [h.eq_fire]
  exact Nat.le_add_left (rho.r s) (z s - rho.l s)

theorem FiresTo.unique {rho : Reaction S} {z z₁ z₂ : State S}
    (h₁ : rho.FiresTo z z₁) (h₂ : rho.FiresTo z z₂) :
    z₁ = z₂ := by
  rw [h₁.eq_fire, h₂.eq_fire]

theorem exists_firesTo_iff_enabled (rho : Reaction S) (z : State S) :
    (exists z' : State S, rho.FiresTo z z') ↔ rho.enabled z := by
  constructor
  · rintro ⟨_z', h⟩
    exact h.enabled
  · intro h
    exact ⟨rho.fire z, h, rfl⟩

theorem fire_eq_of_not_touches (rho : Reaction S) (z : State S) {s : S}
    (h : ¬ rho.Touches s) : rho.fire z s = z s := by
  have hl : rho.l s = 0 := by
    by_contra hl
    exact h (Or.inl hl)
  have hr : rho.r s = 0 := by
    by_contra hr
    exact h (Or.inr hr)
  simp [fire_apply, hl, hr]

theorem FiresTo.eq_on_not_touches {rho : Reaction S} {z z' : State S}
    (hfire : rho.FiresTo z z') {s : S} (h : ¬ rho.Touches s) :
    z' s = z s := by
  rw [hfire.eq_fire]
  exact rho.fire_eq_of_not_touches z h

theorem enabled_of_covers {rho : Reaction S} {z w : State S}
    (hEnabled : rho.enabled z) (hCovers : Covers w z) :
    rho.enabled w := by
  intro s
  exact le_trans (hEnabled s) (hCovers s)

theorem fire_covers_fire_of_covers {rho : Reaction S} {z w : State S}
    (hCovers : Covers w z) :
    Covers (rho.fire w) (rho.fire z) := by
  intro s
  have hsub : z s - rho.l s <= w s - rho.l s :=
    Nat.sub_le_sub_right (hCovers s) (rho.l s)
  exact Nat.add_le_add_right hsub (rho.r s)

theorem enabled_add_right
    {rho : Reaction S} {z extra : State S}
    (hEnabled : rho.enabled z) :
    rho.enabled (State.add z extra) := by
  intro s
  exact le_trans (hEnabled s) (Nat.le_add_right (z s) (extra s))

theorem enabled_add_left
    {rho : Reaction S} {z extra : State S}
    (hEnabled : rho.enabled z) :
    rho.enabled (State.add extra z) := by
  simpa [State.add_comm] using
    (enabled_add_right (extra := extra) hEnabled)

theorem fire_add_right_of_enabled
    {rho : Reaction S} {z extra : State S}
    (hEnabled : rho.enabled z) :
    rho.fire (State.add z extra) = State.add (rho.fire z) extra := by
  funext s
  dsimp [Reaction.fire, State.add]
  have hpre : rho.l s <= z s := hEnabled s
  rw [Nat.sub_add_comm hpre]
  simp [Nat.add_assoc, Nat.add_comm]

theorem fire_add_left_of_enabled
    {rho : Reaction S} {z extra : State S}
    (hEnabled : rho.enabled z) :
    rho.fire (State.add extra z) = State.add extra (rho.fire z) := by
  simpa [State.add_comm] using
    (fire_add_right_of_enabled (extra := extra) hEnabled)

theorem FiresTo.add_right
    {rho : Reaction S} {z z' extra : State S}
    (hfire : rho.FiresTo z z') :
    rho.FiresTo (State.add z extra) (State.add z' extra) := by
  refine ⟨enabled_add_right hfire.enabled, ?_⟩
  rw [hfire.eq_fire, fire_add_right_of_enabled hfire.enabled]

theorem FiresTo.add_left
    {rho : Reaction S} {z z' extra : State S}
    (hfire : rho.FiresTo z z') :
    rho.FiresTo (State.add extra z) (State.add extra z') := by
  refine ⟨enabled_add_left hfire.enabled, ?_⟩
  rw [hfire.eq_fire, fire_add_left_of_enabled hfire.enabled]

theorem FiresTo.lift_covers {rho : Reaction S} {z z' w : State S}
    (hfire : rho.FiresTo z z') (hCovers : Covers w z) :
    exists w', rho.FiresTo w w' /\ Covers w' z' := by
  refine ⟨rho.fire w, ?_, ?_⟩
  · exact ⟨enabled_of_covers hfire.enabled hCovers, rfl⟩
  · rw [hfire.eq_fire]
    exact fire_covers_fire_of_covers hCovers

end Reaction

end Ripple.sCRNUniversality
