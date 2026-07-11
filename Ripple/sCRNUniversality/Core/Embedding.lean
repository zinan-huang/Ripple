import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Ripple.sCRNUniversality.Core.Run

open scoped BigOperators

namespace Ripple.sCRNUniversality

namespace State

def embed {S : Type u} {T : Type v} [Fintype S] [DecidableEq T]
    (e : S -> T) (z : State S) : State T :=
  fun t => (Finset.univ.filter (fun s : S => e s = t)).sum (fun s => z s)

theorem embed_apply_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e) (z : State S) (s : S) :
    embed e z (e s) = z s := by
  classical
  unfold embed
  refine Finset.sum_eq_single s ?_ ?_
  · intro s' hs' hs'ne
    have hes' : e s' = e s := (Finset.mem_filter.mp hs').2
    exact False.elim (hs'ne (he hes'))
  · intro hs
    exact False.elim
      (hs (Finset.mem_filter.mpr ⟨Finset.mem_univ s, rfl⟩))

theorem embed_injective_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e) :
    Function.Injective (embed e : State S -> State T) := by
  intro z z' h
  funext s
  have hs := congrFun h (e s)
  simpa [
    embed_apply_of_injective (e := e) he z s,
    embed_apply_of_injective (e := e) he z' s
  ] using hs

theorem embed_pos_image_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e) (z : State S) (s : S) :
    0 < embed e z (e s) <-> 0 < z s := by
  rw [embed_apply_of_injective (e := e) he z s]

theorem embed_ne_zero_image_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e) (z : State S) (s : S) :
    embed e z (e s) ≠ 0 <-> z s ≠ 0 := by
  rw [embed_apply_of_injective (e := e) he z s]

theorem embed_eq_zero_of_not_exists {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} {z : State S} {t : T}
    (h : ¬ exists s : S, e s = t) :
    embed e z t = 0 := by
  unfold embed
  exact Finset.sum_eq_zero (by
    intro s hs
    have hes : e s = t := (Finset.mem_filter.mp hs).2
    exact False.elim (h ⟨s, hes⟩))

theorem embed_ne_zero_iff_exists {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    (e : S -> T) (z : State S) (t : T) :
    embed e z t ≠ 0 <-> exists s : S, e s = t /\ z s ≠ 0 := by
  classical
  constructor
  · intro hne
    by_contra hnone
    have hzero : embed e z t = 0 := by
      unfold embed
      exact Finset.sum_eq_zero (by
        intro s hs
        have hes : e s = t := (Finset.mem_filter.mp hs).2
        by_contra hz
        exact hnone ⟨s, hes, hz⟩)
    exact hne hzero
  · rintro ⟨s, hes, hz⟩
    unfold embed
    have hs : s ∈ Finset.univ.filter (fun s' : S => e s' = t) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ s, hes⟩
    have hle :
        z s <= (Finset.univ.filter (fun s' : S => e s' = t)).sum
          (fun s => z s) :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hs
    intro hsum
    exact hz (Nat.eq_zero_of_le_zero (by simpa [hsum] using hle))

theorem embed_pullback_eq_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e) {zT : State T}
    (hSupport : forall t, Not (exists s : S, e s = t) -> zT t = 0) :
    embed e (fun s => zT (e s)) = zT := by
  funext t
  by_cases ht : exists s : S, e s = t
  · rcases ht with ⟨s, rfl⟩
    simp [embed_apply_of_injective (e := e) he]
  · simp [
      embed_eq_zero_of_not_exists
        (e := e) (z := fun s => zT (e s)) (t := t) ht,
      hSupport t ht
    ]

theorem embed_pullback_eq_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e) {zT : State T} :
    embed e (fun s => zT (e s)) = zT <->
      forall t, Not (exists s : S, e s = t) -> zT t = 0 := by
  constructor
  · intro h t ht
    have hzero :
        embed e (fun s => zT (e s)) t = 0 :=
      embed_eq_zero_of_not_exists
        (e := e) (z := fun s => zT (e s)) (t := t) ht
    simpa [hzero] using (congrFun h t).symm
  · exact embed_pullback_eq_of_injective (e := e) he

theorem exists_embed_eq_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e) {zT : State T} :
    (exists z : State S, embed e z = zT) <->
      forall t, Not (exists s : S, e s = t) -> zT t = 0 := by
  constructor
  · rintro ⟨z, rfl⟩ t ht
    exact embed_eq_zero_of_not_exists (e := e) (z := z) (t := t) ht
  · intro hSupport
    exact ⟨fun s => zT (e s),
      embed_pullback_eq_of_injective (e := e) he hSupport⟩

theorem exists_eq_embed_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e) {zT : State T} :
    (exists z : State S, zT = embed e z) <->
      forall t, Not (exists s : S, e s = t) -> zT t = 0 := by
  constructor
  · rintro ⟨z, rfl⟩ t ht
    exact embed_eq_zero_of_not_exists (e := e) (z := z) (t := t) ht
  · intro hSupport
    exact ⟨fun s => zT (e s),
      (embed_pullback_eq_of_injective (e := e) he hSupport).symm⟩

@[simp]
theorem embed_zero {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T] (e : S -> T) :
    embed e (State.zero : State S) = State.zero := by
  funext t
  unfold embed
  simp [State.zero]

theorem embed_add {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T] (e : S -> T) (x y : State S) :
    embed e (State.add x y) =
      State.add (embed e x) (embed e y) := by
  funext t
  unfold embed
  simp [State.add, Finset.sum_add_distrib]

theorem embed_single_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e) (s : S) (n : Nat) :
    embed e (single s n) = single (e s) n := by
  funext t
  by_cases ht : exists s' : S, e s' = t
  · rcases ht with ⟨s', rfl⟩
    by_cases hss : s' = s
    · subst hss
      simp [embed_apply_of_injective (e := e) he (single s' n) s']
    · have hes : e s' ≠ e s := fun h => hss (he h)
      simp [embed_apply_of_injective (e := e) he (single s n) s',
        single, hss, hes]
  · have hEmbed : embed e (single s n) t = 0 :=
      embed_eq_zero_of_not_exists
        (e := e) (z := single s n) (t := t) ht
    have hne : t ≠ e s := by
      intro h
      exact ht ⟨s, h.symm⟩
    simp [hEmbed, single, hne]

theorem embed_comp_of_injective {S : Type u} {T : Type v} {U : Type w}
    [Fintype S] [Fintype T] [DecidableEq T] [DecidableEq U]
    {e : S -> T} {f : T -> U}
    (he : Function.Injective e) (hf : Function.Injective f)
    (z : State S) :
    embed f (embed e z) = embed (fun s => f (e s)) z := by
  classical
  have hfe : Function.Injective (fun s => f (e s)) :=
    fun _a _b h => he (hf h)
  funext u
  by_cases hu : exists s : S, f (e s) = u
  · rcases hu with ⟨s, hs⟩
    rw [← hs,
      embed_apply_of_injective (e := f) hf (embed e z) (e s),
      embed_apply_of_injective (e := e) he z s,
      embed_apply_of_injective (e := fun s => f (e s)) hfe z s]
  · have hleft : embed f (embed e z) u = 0 := by
      unfold embed
      exact Finset.sum_eq_zero (by
        intro t ht
        have hft : f t = u := (Finset.mem_filter.mp ht).2
        exact embed_eq_zero_of_not_exists (e := e) (z := z) (t := t) (by
          intro hs
          rcases hs with ⟨s, hes⟩
          exact hu ⟨s, by rw [hes, hft]⟩))
    have hright : embed (fun s => f (e s)) z u = 0 :=
      embed_eq_zero_of_not_exists
        (e := fun s => f (e s)) (z := z) (t := u) hu
    rw [hleft, hright]

end State

namespace Complex

theorem embed_eq_zero_of_not_exists {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} {c : Complex S} {t : T}
    (h : ¬ exists s : S, e s = t) :
    State.embed e c t = 0 :=
  State.embed_eq_zero_of_not_exists (e := e) (z := c) (t := t) h

end Complex

namespace Covers

theorem embed {S : Type u} {T : Type v} [Fintype S] [DecidableEq T]
    {e : S -> T} {z target : State S}
    (h : Covers z target) :
    Covers (State.embed e z) (State.embed e target) := by
  intro t
  dsimp [State.embed]
  exact Finset.sum_le_sum (fun s _hs => h s)

theorem of_embed_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e) {z target : State S}
    (h : Covers (State.embed e z) (State.embed e target)) :
    Covers z target := by
  intro s
  have hs := h (e s)
  simpa [
    State.embed_apply_of_injective (e := e) he z s,
    State.embed_apply_of_injective (e := e) he target s
  ] using hs

theorem embed_supported_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {z : State S} {targetT : State T} :
    Covers (State.embed e z) targetT <->
      (forall t, Not (exists s : S, e s = t) -> targetT t = 0) /\
        Covers z (fun s => targetT (e s)) := by
  constructor
  · intro h
    constructor
    · intro t ht
      have hz : State.embed e z t = 0 :=
        State.embed_eq_zero_of_not_exists (e := e) (z := z) (t := t) ht
      exact Nat.eq_zero_of_le_zero (by simpa [hz] using h t)
    · intro s
      simpa [State.embed_apply_of_injective (e := e) he z s]
        using h (e s)
  · rintro ⟨hSupport, hCovers⟩ t
    by_cases ht : exists s : S, e s = t
    · rcases ht with ⟨s, rfl⟩
      simpa [State.embed_apply_of_injective (e := e) he z s]
        using hCovers s
    · rw [hSupport t ht]
      exact Nat.zero_le _

theorem embed_image_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {z : State S} {targetT : State T} :
    Covers (State.embed e z) targetT <->
      exists target : State S,
        targetT = State.embed e target /\ Covers z target := by
  constructor
  · intro h
    rcases (embed_supported_iff_of_injective (e := e) he
        (z := z) (targetT := targetT)).1 h with
      ⟨hSupport, hBaseCovers⟩
    refine ⟨fun s => targetT (e s), ?_, hBaseCovers⟩
    exact (State.embed_pullback_eq_of_injective
      (e := e) he hSupport).symm
  · rintro ⟨target, rfl, hCovers⟩
    exact embed (e := e) hCovers

theorem embed_target_pullback_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {zT : State T} {target : State S} :
    Covers zT (State.embed e target) <->
      Covers (fun s => zT (e s)) target := by
  constructor
  · intro h s
    have hs := h (e s)
    simpa [State.embed_apply_of_injective (e := e) he target s] using hs
  · intro h t
    by_cases ht : exists s : S, e s = t
    · rcases ht with ⟨s, rfl⟩
      simpa [State.embed_apply_of_injective (e := e) he target s]
        using h s
    · have htarget :
          State.embed e target t = 0 :=
        State.embed_eq_zero_of_not_exists
          (e := e) (z := target) (t := t) ht
      rw [htarget]
      exact Nat.zero_le _

end Covers

namespace Reaction

def embed {S : Type u} {T : Type v} [Fintype S] [DecidableEq T]
    (e : S -> T) (rho : Reaction S) : Reaction T :=
  { l := State.embed e rho.l
    r := State.embed e rho.r
    k := rho.k }

theorem embed_enabled {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} {rho : Reaction S} {z : State S}
    (h : rho.enabled z) :
    (embed e rho).enabled (State.embed e z) := by
  intro t
  dsimp [Reaction.enabled, embed, State.embed]
  exact Finset.sum_le_sum (fun s _hs => h s)

theorem embed_enabled_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {rho : Reaction S} {z : State S} :
    (embed e rho).enabled (State.embed e z) <-> rho.enabled z := by
  constructor
  · intro h s
    have hs := h (e s)
    simpa [embed,
      State.embed_apply_of_injective (e := e) he rho.l s,
      State.embed_apply_of_injective (e := e) he z s] using hs
  · exact embed_enabled (e := e)

theorem embed_enabled_pullback_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {rho : Reaction S} {zT : State T} :
    (embed e rho).enabled zT <->
      rho.enabled (fun s => zT (e s)) := by
  constructor
  · intro h s
    have hs := h (e s)
    simpa [embed, State.embed_apply_of_injective (e := e) he rho.l s]
      using hs
  · intro h t
    by_cases ht : exists s : S, e s = t
    · rcases ht with ⟨s, rfl⟩
      simpa [embed, State.embed_apply_of_injective (e := e) he rho.l s]
        using h s
    · have hl :
          State.embed e rho.l t = 0 :=
        State.embed_eq_zero_of_not_exists
          (e := e) (z := rho.l) (t := t) ht
      simp [embed, hl]

theorem embed_fire_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    (rho : Reaction S) (z : State S) :
    State.embed e (rho.fire z) =
      (embed e rho).fire (State.embed e z) := by
  classical
  funext t
  by_cases ht : exists s : S, e s = t
  · rcases ht with ⟨s, rfl⟩
    have hfire :
        State.embed e (rho.fire z) (e s) = rho.fire z s :=
      State.embed_apply_of_injective (e := e) he (rho.fire z) s
    have hz :
        State.embed e z (e s) = z s :=
      State.embed_apply_of_injective (e := e) he z s
    have hl :
        State.embed e rho.l (e s) = rho.l s :=
      State.embed_apply_of_injective (e := e) he rho.l s
    have hr :
        State.embed e rho.r (e s) = rho.r s :=
      State.embed_apply_of_injective (e := e) he rho.r s
    simp [Reaction.fire, embed, hfire, hz, hl, hr]
  · have hfire :
        State.embed e (rho.fire z) t = 0 :=
      State.embed_eq_zero_of_not_exists
        (e := e) (z := rho.fire z) (t := t) ht
    have hz :
        State.embed e z t = 0 :=
      State.embed_eq_zero_of_not_exists
        (e := e) (z := z) (t := t) ht
    have hl :
        State.embed e rho.l t = 0 :=
      State.embed_eq_zero_of_not_exists
        (e := e) (z := rho.l) (t := t) ht
    have hr :
        State.embed e rho.r t = 0 :=
      State.embed_eq_zero_of_not_exists
        (e := e) (z := rho.r) (t := t) ht
    simp [Reaction.fire, embed, hfire, hz, hl, hr]

theorem embed_fire_pullback_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    (rho : Reaction S) (zT : State T) :
    (fun s => (embed e rho).fire zT (e s)) =
      rho.fire (fun s => zT (e s)) := by
  funext s
  simp [Reaction.fire, embed,
    State.embed_apply_of_injective (e := e) he rho.l s,
    State.embed_apply_of_injective (e := e) he rho.r s]

theorem embed_FiresTo_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {rho : Reaction S} {z z' : State S}
    (h : rho.FiresTo z z') :
    (embed e rho).FiresTo (State.embed e z) (State.embed e z') := by
  refine ⟨embed_enabled (e := e) h.1, ?_⟩
  rw [h.2]
  exact embed_fire_of_injective (e := e) he rho z

theorem embed_touches_apply_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    (rho : Reaction S) (s : S) :
    (embed e rho).Touches (e s) <-> rho.Touches s := by
  constructor
  · rintro (hl | hr)
    · exact Or.inl (by
        simpa [embed, State.embed_apply_of_injective (e := e) he rho.l s] using hl)
    · exact Or.inr (by
        simpa [embed, State.embed_apply_of_injective (e := e) he rho.r s] using hr)
  · rintro (hl | hr)
    · exact Or.inl (by
        simpa [embed, State.embed_apply_of_injective (e := e) he rho.l s] using hl)
    · exact Or.inr (by
        simpa [embed, State.embed_apply_of_injective (e := e) he rho.r s] using hr)

theorem embed_Touches_image_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    (rho : Reaction S) (s : S) :
    (embed e rho).Touches (e s) <-> rho.Touches s :=
  embed_touches_apply_iff_of_injective (e := e) he rho s

theorem embed_not_touches_of_not_exists {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} {rho : Reaction S} {t : T}
    (h : ¬ exists s : S, e s = t) :
    ¬ (embed e rho).Touches t := by
  intro ht
  have hl : State.embed e rho.l t = 0 :=
    State.embed_eq_zero_of_not_exists (e := e) (z := rho.l) (t := t) h
  have hr : State.embed e rho.r t = 0 :=
    State.embed_eq_zero_of_not_exists (e := e) (z := rho.r) (t := t) h
  rcases ht with hlt | hrt
  · exact hlt (by simpa [embed] using hl)
  · exact hrt (by simpa [embed] using hr)

theorem embed_not_Touches_of_not_exists {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (rho : Reaction S) {t : T}
    (h : ¬ exists s : S, e s = t) :
    ¬ (embed e rho).Touches t :=
  embed_not_touches_of_not_exists (e := e) (rho := rho) (t := t) h

theorem embed_comp_of_injective {S : Type u} {T : Type v} {U : Type w}
    [Fintype S] [Fintype T] [DecidableEq T] [DecidableEq U]
    {e : S -> T} {f : T -> U}
    (he : Function.Injective e) (hf : Function.Injective f)
    (rho : Reaction S) :
    embed f (embed e rho) = embed (fun s => f (e s)) rho := by
  cases rho
  simp [embed, State.embed_comp_of_injective (e := e) (f := f) he hf]

end Reaction

namespace Network

def embed {S : Type u} {T : Type v} [Fintype S] [DecidableEq T]
    (e : S -> T) (N : Network S) : Network T where
  I := N.I
  fintypeI := N.fintypeI
  rxn := fun i => Reaction.embed e (N.rxn i)

theorem embed_enabledAt_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {i : N.I} {z : State S} :
    (embed e N).EnabledAt (State.embed e z) i <->
      N.EnabledAt z i := by
  simpa [Network.EnabledAt, embed] using
    Reaction.embed_enabled_iff_of_injective
      (e := e) he (rho := N.rxn i) (z := z)

theorem embed_enabledAt_pullback_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {i : N.I} {zT : State T} :
    (embed e N).EnabledAt zT i <->
      N.EnabledAt (fun s => zT (e s)) i := by
  simpa [Network.EnabledAt, embed] using
    Reaction.embed_enabled_pullback_iff_of_injective
      (e := e) he (rho := N.rxn i) (zT := zT)

theorem embed_terminal_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z : State S} :
    (embed e N).Terminal (State.embed e z) <->
      N.Terminal z := by
  constructor
  · intro hTerminal i hEnabled
    exact hTerminal i
      ((embed_enabledAt_iff_of_injective (e := e) he
        (N := N) (i := i) (z := z)).2 hEnabled)
  · intro hTerminal i hEnabled
    exact hTerminal i
      ((embed_enabledAt_iff_of_injective (e := e) he
        (N := N) (i := i) (z := z)).1 hEnabled)

theorem embed_terminal_pullback_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT : State T} :
    (embed e N).Terminal zT <->
      N.Terminal (fun s => zT (e s)) := by
  constructor
  · intro hTerminal i hEnabled
    exact hTerminal i
      ((embed_enabledAt_pullback_iff_of_injective
        (e := e) he (N := N) (i := i) (zT := zT)).2 hEnabled)
  · intro hTerminal i hEnabled
    exact hTerminal i
      ((embed_enabledAt_pullback_iff_of_injective
        (e := e) he (N := N) (i := i) (zT := zT)).1 hEnabled)

theorem embed_rxn_Touches_image_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} (i : N.I) (s : S) :
    ((embed e N).rxn i).Touches (e s) <-> (N.rxn i).Touches s := by
  simpa [embed] using
    Reaction.embed_Touches_image_iff_of_injective
      (e := e) he (N.rxn i) s

theorem embed_rxn_not_Touches_of_not_exists {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T}
    {N : Network S} (i : N.I) {t : T}
    (h : ¬ exists s : S, e s = t) :
    ¬ ((embed e N).rxn i).Touches t := by
  simpa [embed] using
    Reaction.embed_not_Touches_of_not_exists
      (e := e) (rho := N.rxn i) h

theorem embed_stepAt_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {i : N.I} {z z' : State S}
    (h : N.StepAt i z z') :
    (embed e N).StepAt i (State.embed e z) (State.embed e z') := by
  simpa [StepAt, embed] using
    (Reaction.embed_FiresTo_of_injective
      (e := e) (rho := N.rxn i) he h)

theorem embed_stepAt_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {i : N.I} {z z' : State S} :
    (embed e N).StepAt i (State.embed e z) (State.embed e z') <->
      N.StepAt i z z' := by
  constructor
  · intro h
    have hEnabled : (N.rxn i).enabled z :=
      (Reaction.embed_enabled_iff_of_injective
        (e := e) he (rho := N.rxn i) (z := z)).1 h.enabled
    have hEq :
        State.embed e z' = State.embed e ((N.rxn i).fire z) := by
      rw [h.eq_fire]
      simpa [embed] using
        (Reaction.embed_fire_of_injective
          (e := e) he (N.rxn i) z).symm
    exact ⟨hEnabled, State.embed_injective_of_injective (e := e) he hEq⟩
  · exact embed_stepAt_of_injective (e := e) (N := N) he

theorem embed_stepAt_pullback_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {i : N.I} {zT zT' : State T}
    (hStep : (embed e N).StepAt i zT zT') :
    N.StepAt i
      (fun s => zT (e s))
      (fun s => zT' (e s)) := by
  refine ⟨?_, ?_⟩
  · exact (Reaction.embed_enabled_pullback_iff_of_injective
      (e := e) he (rho := N.rxn i) (zT := zT)).1 hStep.enabled
  · funext s
    rw [hStep.eq_fire]
    exact congrFun
      (Reaction.embed_fire_pullback_of_injective
        (e := e) he (N.rxn i) zT) s

theorem embed_stepAt_lift_pullback_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {i : N.I} {zT : State T} {z' : State S}
    (hStep : N.StepAt i (fun s => zT (e s)) z') :
    exists zT' : State T,
      (embed e N).StepAt i zT zT' /\ (fun s => zT' (e s)) = z' := by
  let zT' : State T := ((embed e N).rxn i).fire zT
  have hEnabledT : (embed e N).EnabledAt zT i :=
    (embed_enabledAt_pullback_iff_of_injective
      (e := e) (N := N) he).2 hStep.enabled
  refine ⟨zT', ⟨hEnabledT, rfl⟩, ?_⟩
  funext s
  rw [hStep.eq_fire]
  exact congrFun
    (Reaction.embed_fire_pullback_of_injective
      (e := e) he (N.rxn i) zT) s

theorem embed_stepAt_lift_pullback_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {i : N.I} {zT : State T} {z' : State S} :
    (exists zT' : State T,
      (embed e N).StepAt i zT zT' /\ (fun s => zT' (e s)) = z') <->
      N.StepAt i (fun s => zT (e s)) z' := by
  constructor
  · rintro ⟨zT', hStepT, hPullback⟩
    have hBase :
        N.StepAt i (fun s => zT (e s)) (fun s => zT' (e s)) :=
      embed_stepAt_pullback_of_injective
        (e := e) (N := N) he hStepT
    simpa [hPullback] using hBase
  · exact embed_stepAt_lift_pullback_of_injective
      (e := e) (N := N) he

theorem embed_stepInvariant_image_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {P : State S -> Prop}
    (hInv : N.StepInvariant P) :
    (embed e N).StepInvariant
      (fun zT => exists z : State S, zT = State.embed e z /\ P z) := by
  intro i zT zT' hStep hImage
  rcases hImage with ⟨z, rfl, hP⟩
  have hEnabled : (N.rxn i).enabled z := by
    exact
      (Reaction.embed_enabled_iff_of_injective
        (e := e) he (rho := N.rxn i) (z := z)).1 hStep.enabled
  let zNext : State S := (N.rxn i).fire z
  have hBaseStep : N.StepAt i z zNext := by
    exact ⟨hEnabled, rfl⟩
  refine ⟨zNext, ?_, hInv hBaseStep hP⟩
  exact
    Reaction.FiresTo.unique hStep
      (embed_stepAt_of_injective (e := e) (N := N) he hBaseStep)

theorem stepInvariant_of_embed_stepInvariant_image_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {P : State S -> Prop}
    (hInv :
      (embed e N).StepInvariant
        (fun zT => exists z : State S, zT = State.embed e z /\ P z)) :
    N.StepInvariant P := by
  intro i z z' hStep hP
  have hEmbStep :
      (embed e N).StepAt i (State.embed e z) (State.embed e z') :=
    embed_stepAt_of_injective (e := e) (N := N) he hStep
  have hImage' := hInv hEmbStep ⟨z, rfl, hP⟩
  rcases hImage' with ⟨w, hw, hPw⟩
  have hz'w : z' = w :=
    State.embed_injective_of_injective (e := e) he hw
  simpa [hz'w] using hPw

theorem embed_stepInvariant_image_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {P : State S -> Prop} :
    (embed e N).StepInvariant
        (fun zT => exists z : State S, zT = State.embed e z /\ P z) <->
      N.StepInvariant P := by
  constructor
  · exact stepInvariant_of_embed_stepInvariant_image_of_injective
      (e := e) he (N := N) (P := P)
  · exact embed_stepInvariant_image_of_injective
      (e := e) he (N := N) (P := P)

theorem embed_exec_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z z' : State S} {is : List N.I}
    (h : N.Exec z z' is) :
    (embed e N).Exec (State.embed e z) (State.embed e z') is := by
  induction h with
  | nil z =>
      exact ExecOf.nil (State.embed e z)
  | cons hStep _tail ih =>
      exact ExecOf.cons
        (embed_stepAt_of_injective (e := e) (N := N) he hStep)
        ih

theorem embed_exec_pullback_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT zT' : State T} {is : List N.I}
    (h : (embed e N).Exec zT zT' is) :
    N.Exec (fun s => zT (e s)) (fun s => zT' (e s)) is := by
  induction h with
  | nil z =>
      exact ExecOf.nil (fun s => z (e s))
  | cons hStep _tail ih =>
      exact ExecOf.cons
        (embed_stepAt_pullback_of_injective
          (e := e) (N := N) he hStep)
        ih

theorem embed_exec_lift_pullback_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT : State T} {z' : State S} {is : List N.I}
    (hExec : N.Exec (fun s => zT (e s)) z' is) :
    exists zT' : State T,
      (embed e N).Exec zT zT' is /\ (fun s => zT' (e s)) = z' := by
  induction is generalizing zT z' with
  | nil =>
      have hEq : (fun s => zT (e s)) = z' := ExecOf.nil_iff.mp hExec
      exact ⟨zT, ExecOf.nil zT, hEq⟩
  | cons i is ih =>
      rcases ExecOf.cons_iff.mp hExec with ⟨mid, hStep, hTail⟩
      rcases embed_stepAt_lift_pullback_of_injective
          (e := e) (N := N) he hStep with
        ⟨midT, hStepT, hMid⟩
      have hTail' : N.Exec (fun s => midT (e s)) z' is := by
        simpa [hMid] using hTail
      rcases ih hTail' with ⟨zT', hTailT, hFinal⟩
      exact ⟨zT', ExecOf.cons hStepT hTailT, hFinal⟩

theorem embed_exec_lift_pullback_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT : State T} {z' : State S} {is : List N.I} :
    (exists zT' : State T,
      (embed e N).Exec zT zT' is /\ (fun s => zT' (e s)) = z') <->
      N.Exec (fun s => zT (e s)) z' is := by
  constructor
  · rintro ⟨zT', hExecT, hPullback⟩
    have hBase :
        N.Exec (fun s => zT (e s)) (fun s => zT' (e s)) is :=
      embed_exec_pullback_of_injective
        (e := e) (N := N) he hExecT
    simpa [hPullback] using hBase
  · exact embed_exec_lift_pullback_of_injective
      (e := e) (N := N) he

theorem embed_exec_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z z' : State S} {is : List N.I} :
    (embed e N).Exec (State.embed e z) (State.embed e z') is <->
      N.Exec z z' is := by
  constructor
  · intro h
    induction is generalizing z with
    | nil =>
        have hEq : State.embed e z = State.embed e z' :=
          ExecOf.nil_iff.mp h
        have hBaseEq : z = z' :=
          State.embed_injective_of_injective (e := e) he hEq
        simp [hBaseEq]
    | cons i is ih =>
        rcases ExecOf.cons_iff.mp h with ⟨midT, hStepT, hTailT⟩
        let mid : State S := (N.rxn i).fire z
        have hEnabled : (N.rxn i).enabled z :=
          (Reaction.embed_enabled_iff_of_injective
            (e := e) he (rho := N.rxn i) (z := z)).1 hStepT.enabled
        have hBaseStep : N.StepAt i z mid := by
          exact ⟨hEnabled, rfl⟩
        have hMid : midT = State.embed e mid :=
          Reaction.FiresTo.unique hStepT
            (embed_stepAt_of_injective
              (e := e) (N := N) he hBaseStep)
        subst hMid
        exact ExecOf.cons hBaseStep (ih hTailT)
  · exact embed_exec_of_injective (e := e) (N := N) he

theorem embed_exec_image_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 : State S} {zT : State T} {is : List N.I}
    (hExec : (embed e N).Exec (State.embed e z0) zT is) :
    exists z : State S, zT = State.embed e z /\ N.Exec z0 z is := by
  induction is generalizing z0 with
  | nil =>
      have hEq : State.embed e z0 = zT := ExecOf.nil_iff.mp hExec
      exact ⟨z0, hEq.symm, ExecOf.nil z0⟩
  | cons i is ih =>
      rcases ExecOf.cons_iff.mp hExec with ⟨midT, hStepT, hTailT⟩
      let mid : State S := (N.rxn i).fire z0
      have hEnabled : (N.rxn i).enabled z0 :=
        (Reaction.embed_enabled_iff_of_injective
          (e := e) he (rho := N.rxn i) (z := z0)).1 hStepT.enabled
      have hBaseStep : N.StepAt i z0 mid := by
        exact ⟨hEnabled, rfl⟩
      have hMid : midT = State.embed e mid :=
        Reaction.FiresTo.unique hStepT
          (embed_stepAt_of_injective
            (e := e) (N := N) he hBaseStep)
      subst hMid
      rcases ih hTailT with ⟨z, hzT, hBaseTail⟩
      exact ⟨z, hzT, ExecOf.cons hBaseStep hBaseTail⟩

theorem embed_exec_image_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 : State S} {zT : State T} {is : List N.I} :
    (exists z : State S, zT = State.embed e z /\ N.Exec z0 z is) <->
      (embed e N).Exec (State.embed e z0) zT is := by
  constructor
  · rintro ⟨z, rfl, hExec⟩
    exact embed_exec_of_injective (e := e) (N := N) he hExec
  · exact embed_exec_image_of_injective (e := e) (N := N) he

theorem embed_exec_supported_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 : State S} {zT : State T} {is : List N.I} :
    (embed e N).Exec (State.embed e z0) zT is <->
      (forall t, Not (exists s : S, e s = t) -> zT t = 0) /\
        N.Exec z0 (fun s => zT (e s)) is := by
  constructor
  · intro hExec
    rcases embed_exec_image_of_injective
        (e := e) (N := N) he hExec with
      ⟨z, hzT, hBaseExec⟩
    constructor
    · intro t ht
      rw [hzT]
      exact State.embed_eq_zero_of_not_exists
        (e := e) (z := z) (t := t) ht
    · have hpull : (fun s => zT (e s)) = z := by
        funext s
        rw [hzT]
        exact State.embed_apply_of_injective (e := e) he z s
      simpa [hpull] using hBaseExec
  · rintro ⟨hSupport, hBaseExec⟩
    have hzT :
        State.embed e (fun s => zT (e s)) = zT :=
      State.embed_pullback_eq_of_injective (e := e) he hSupport
    rw [← hzT]
    exact embed_exec_of_injective (e := e) (N := N) he hBaseExec

theorem embed_reaches_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z z' : State S}
    (h : N.Reaches z z') :
    (embed e N).Reaches (State.embed e z) (State.embed e z') := by
  rcases h with ⟨is, hExec⟩
  exact ⟨is, embed_exec_of_injective (e := e) (N := N) he hExec⟩

theorem embed_reaches_pullback_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT zT' : State T}
    (h : (embed e N).Reaches zT zT') :
    N.Reaches
      (fun s => zT (e s))
      (fun s => zT' (e s)) := by
  rcases h with ⟨is, hExec⟩
  exact ⟨is,
    embed_exec_pullback_of_injective
      (e := e) (N := N) he hExec⟩

theorem embed_reaches_lift_pullback_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT : State T} {z' : State S}
    (h : N.Reaches (fun s => zT (e s)) z') :
    exists zT' : State T,
      (embed e N).Reaches zT zT' /\ (fun s => zT' (e s)) = z' := by
  rcases h with ⟨is, hExec⟩
  rcases embed_exec_lift_pullback_of_injective
      (e := e) (N := N) he hExec with
    ⟨zT', hExecT, hFinal⟩
  exact ⟨zT', ⟨is, hExecT⟩, hFinal⟩

theorem embed_reaches_lift_pullback_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT : State T} {z' : State S} :
    (exists zT' : State T,
      (embed e N).Reaches zT zT' /\ (fun s => zT' (e s)) = z') <->
      N.Reaches (fun s => zT (e s)) z' := by
  constructor
  · rintro ⟨zT', hReachT, hPullback⟩
    have hBase :
        N.Reaches (fun s => zT (e s)) (fun s => zT' (e s)) :=
      embed_reaches_pullback_of_injective
        (e := e) (N := N) he hReachT
    simpa [hPullback] using hBase
  · exact embed_reaches_lift_pullback_of_injective
      (e := e) (N := N) he

theorem embed_reaches_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z z' : State S} :
    (embed e N).Reaches (State.embed e z) (State.embed e z') <->
      N.Reaches z z' := by
  constructor
  · rintro ⟨is, hExec⟩
    exact ⟨is, (embed_exec_iff_of_injective
      (e := e) (N := N) he).mp hExec⟩
  · exact embed_reaches_of_injective (e := e) (N := N) he

theorem embed_reaches_image_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 : State S} {zT : State T}
    (hReach : (embed e N).Reaches (State.embed e z0) zT) :
    exists z : State S, zT = State.embed e z /\ N.Reaches z0 z := by
  rcases hReach with ⟨is, hExec⟩
  rcases embed_exec_image_of_injective
      (e := e) (N := N) he hExec with
    ⟨z, hzT, hBaseExec⟩
  exact ⟨z, hzT, ⟨is, hBaseExec⟩⟩

theorem embed_reaches_image_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 : State S} {zT : State T} :
    (exists z : State S, zT = State.embed e z /\ N.Reaches z0 z) <->
      (embed e N).Reaches (State.embed e z0) zT := by
  constructor
  · rintro ⟨z, rfl, hReach⟩
    exact embed_reaches_of_injective (e := e) (N := N) he hReach
  · exact embed_reaches_image_of_injective (e := e) (N := N) he

theorem embed_reaches_supported_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 : State S} {zT : State T} :
    (embed e N).Reaches (State.embed e z0) zT <->
      (forall t, Not (exists s : S, e s = t) -> zT t = 0) /\
        N.Reaches z0 (fun s => zT (e s)) := by
  constructor
  · intro hReach
    rcases embed_reaches_image_of_injective
        (e := e) (N := N) he hReach with
      ⟨z, hzT, hBaseReach⟩
    constructor
    · intro t ht
      rw [hzT]
      exact State.embed_eq_zero_of_not_exists
        (e := e) (z := z) (t := t) ht
    · have hpull : (fun s => zT (e s)) = z := by
        funext s
        rw [hzT]
        exact State.embed_apply_of_injective (e := e) he z s
      simpa [hpull] using hBaseReach
  · rintro ⟨hSupport, hBaseReach⟩
    have hzT :
        State.embed e (fun s => zT (e s)) = zT :=
      State.embed_pullback_eq_of_injective (e := e) he hSupport
    rw [← hzT]
    exact embed_reaches_of_injective
      (e := e) (N := N) he hBaseReach

theorem embed_coverable_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 target : State S}
    (h : N.CoverableFrom z0 target) :
    (embed e N).CoverableFrom (State.embed e z0) (State.embed e target) := by
  rcases h with ⟨z, hReach, hCovers⟩
  exact ⟨State.embed e z,
    embed_reaches_of_injective (e := e) (N := N) he hReach,
    Covers.embed hCovers⟩

theorem embed_coverable_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 target : State S} :
    (embed e N).CoverableFrom
        (State.embed e z0) (State.embed e target) <->
      N.CoverableFrom z0 target := by
  constructor
  · rintro ⟨zT, hReach, hCovers⟩
    have hImageInv :
        (embed e N).StepInvariant
          (fun zT => exists z : State S,
            zT = State.embed e z /\ True) :=
      embed_stepInvariant_image_of_injective
        (e := e) he (N := N) (P := fun _ => True)
        (by
          intro _i _z _z' _hStep _hTrue
          trivial)
    rcases hImageInv.reaches hReach ⟨z0, rfl, trivial⟩ with
      ⟨z, rfl, _hTrue⟩
    exact ⟨z,
      (embed_reaches_iff_of_injective (e := e) (N := N) he).mp hReach,
      Covers.of_embed_of_injective (e := e) he hCovers⟩
  · exact embed_coverable_of_injective (e := e) (N := N) he

theorem embed_coverable_supported_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 : State S} {targetT : State T} :
    (embed e N).CoverableFrom (State.embed e z0) targetT <->
      (forall t, Not (exists s : S, e s = t) -> targetT t = 0) /\
        N.CoverableFrom z0 (fun s => targetT (e s)) := by
  constructor
  · rintro ⟨zT, hReach, hCovers⟩
    rcases embed_reaches_image_of_injective
        (e := e) (N := N) he hReach with
      ⟨z, rfl, hBaseReach⟩
    rcases (Covers.embed_supported_iff_of_injective
        (e := e) he (z := z) (targetT := targetT)).1 hCovers with
      ⟨hSupport, hBaseCovers⟩
    exact ⟨hSupport, z, hBaseReach, hBaseCovers⟩
  · rintro ⟨hSupport, z, hReach, hCovers⟩
    refine ⟨State.embed e z,
      embed_reaches_of_injective (e := e) (N := N) he hReach, ?_⟩
    exact (Covers.embed_supported_iff_of_injective
      (e := e) he (z := z) (targetT := targetT)).2
      ⟨hSupport, hCovers⟩

theorem embed_coverable_image_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 : State S} {targetT : State T} :
    (embed e N).CoverableFrom (State.embed e z0) targetT <->
      exists target : State S,
        targetT = State.embed e target /\ N.CoverableFrom z0 target := by
  constructor
  · intro h
    rcases (embed_coverable_supported_iff_of_injective
        (e := e) (N := N) he).1 h with
      ⟨hSupport, hBaseCover⟩
    refine ⟨fun s => targetT (e s), ?_, hBaseCover⟩
    exact (State.embed_pullback_eq_of_injective
      (e := e) he hSupport).symm
  · rintro ⟨target, rfl, hBaseCover⟩
    exact embed_coverable_of_injective
      (e := e) (N := N) he hBaseCover

theorem embed_coverable_pullback_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT targetT : State T}
    (h : (embed e N).CoverableFrom zT targetT) :
    N.CoverableFrom (fun s => zT (e s)) (fun s => targetT (e s)) := by
  rcases h with ⟨zT', hReach, hCovers⟩
  exact ⟨fun s => zT' (e s),
    embed_reaches_pullback_of_injective
      (e := e) (N := N) he hReach,
    fun s => hCovers (e s)⟩

theorem embed_coverable_image_pullback_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT targetT : State T}
    (hSupport : forall t, Not (exists s : S, e s = t) -> targetT t = 0)
    (h : (embed e N).CoverableFrom zT targetT) :
    exists target : State S,
      targetT = State.embed e target /\
        N.CoverableFrom (fun s => zT (e s)) target := by
  refine ⟨fun s => targetT (e s), ?_, ?_⟩
  · exact (State.embed_pullback_eq_of_injective
      (e := e) he hSupport).symm
  · exact embed_coverable_pullback_of_injective
      (e := e) (N := N) he h

theorem embed_coverable_target_pullback_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT : State T} {target : State S}
    (h : (embed e N).CoverableFrom zT (State.embed e target)) :
    N.CoverableFrom (fun s => zT (e s)) target := by
  rcases h with ⟨zT', hReach, hCovers⟩
  exact ⟨fun s => zT' (e s),
    embed_reaches_pullback_of_injective
      (e := e) (N := N) he hReach,
    (Covers.embed_target_pullback_iff_of_injective
      (e := e) he).1 hCovers⟩

theorem embed_coverable_target_lift_pullback_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT : State T} {target : State S}
    (h : N.CoverableFrom (fun s => zT (e s)) target) :
    (embed e N).CoverableFrom zT (State.embed e target) := by
  rcases h with ⟨z, hReach, hCovers⟩
  rcases embed_reaches_lift_pullback_of_injective
      (e := e) (N := N) he hReach with
    ⟨zT', hReachT, hPullback⟩
  refine ⟨zT', hReachT, ?_⟩
  exact (Covers.embed_target_pullback_iff_of_injective
    (e := e) he).2 (by
      simpa [hPullback] using hCovers)

theorem embed_coverable_target_pullback_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT : State T} {target : State S} :
    (embed e N).CoverableFrom zT (State.embed e target) <->
      N.CoverableFrom (fun s => zT (e s)) target := by
  constructor
  · exact embed_coverable_target_pullback_of_injective
      (e := e) (N := N) he
  · exact embed_coverable_target_lift_pullback_of_injective
      (e := e) (N := N) he

theorem embed_coverable_single_pullback_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT : State T} {s : S} {n : Nat}
    (h : (embed e N).CoverableFrom zT (State.single (e s) n)) :
    N.CoverableFrom (fun s' => zT (e s')) (State.single s n) :=
  embed_coverable_target_pullback_of_injective
    (e := e) (N := N) he
    (by
      simpa [State.embed_single_of_injective (e := e) he s n] using h)

theorem embed_coverable_single_lift_pullback_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT : State T} {s : S} {n : Nat}
    (h : N.CoverableFrom (fun s' => zT (e s')) (State.single s n)) :
    (embed e N).CoverableFrom zT (State.single (e s) n) := by
  simpa [State.embed_single_of_injective (e := e) he s n] using
    embed_coverable_target_lift_pullback_of_injective
      (e := e) (N := N) he h

theorem embed_coverable_single_pullback_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT : State T} {s : S} {n : Nat} :
    (embed e N).CoverableFrom zT (State.single (e s) n) <->
      N.CoverableFrom (fun s' => zT (e s')) (State.single s n) := by
  constructor
  · exact embed_coverable_single_pullback_of_injective
      (e := e) (N := N) he
  · exact embed_coverable_single_lift_pullback_of_injective
      (e := e) (N := N) he

theorem embed_coverable_coord_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 target : State S} {s : S}
    (h : N.CoverableFrom z0 target) :
    exists zT : State T,
      (embed e N).Reaches (State.embed e z0) zT /\
        target s <= zT (e s) := by
  rcases h with ⟨z, hReach, hCovers⟩
  refine ⟨State.embed e z, ?_, ?_⟩
  · exact embed_reaches_of_injective (e := e) (N := N) he hReach
  · simpa [State.embed_apply_of_injective (e := e) he z s] using hCovers s

theorem embed_reaches_coord_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 : State S} {s : S} {n : Nat} :
    (exists zT : State T,
      (embed e N).Reaches (State.embed e z0) zT /\
        n <= zT (e s)) <->
      exists z : State S, N.Reaches z0 z /\ n <= z s := by
  constructor
  · rintro ⟨zT, hReach, hn⟩
    rcases embed_reaches_image_of_injective
        (e := e) (N := N) he hReach with
      ⟨z, rfl, hBaseReach⟩
    exact ⟨z, hBaseReach, by
      simpa [State.embed_apply_of_injective (e := e) he z s] using hn⟩
  · rintro ⟨z, hReach, hn⟩
    refine ⟨State.embed e z,
      embed_reaches_of_injective (e := e) (N := N) he hReach, ?_⟩
    simpa [State.embed_apply_of_injective (e := e) he z s] using hn

theorem embed_speciesCoverableFrom_of_reaches_coord_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 z : State S} {s : S} {n : Nat}
    (hReach : N.Reaches z0 z) (hn : n <= z s) :
    (embed e N).SpeciesCoverableFrom (State.embed e z0) (e s) n := by
  have hReach' :
      (embed e N).Reaches (State.embed e z0) (State.embed e z) :=
    embed_reaches_of_injective (e := e) (N := N) he hReach
  have hn' : n <= State.embed e z (e s) := by
    simpa [State.embed_apply_of_injective (e := e) he z s] using hn
  exact speciesCoverableFrom_of_reaches_coord hReach' hn'

theorem embed_coverable_single_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 : State S} {s : S} {n : Nat}
    (h : N.CoverableFrom z0 (State.single s n)) :
    (embed e N).CoverableFrom (State.embed e z0) (State.single (e s) n) := by
  simpa [State.embed_single_of_injective (e := e) he s n] using
    (embed_coverable_of_injective (e := e) (N := N) he h)

theorem embed_speciesCoverableFrom_of_injective {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 : State S} {s : S} {n : Nat}
    (h : N.SpeciesCoverableFrom z0 s n) :
    (embed e N).SpeciesCoverableFrom (State.embed e z0) (e s) n := by
  rcases speciesCoverableFrom_iff.mp h with ⟨z, hReach, hn⟩
  exact embed_speciesCoverableFrom_of_reaches_coord_of_injective
    (e := e) (N := N) he hReach hn

theorem embed_speciesCoverableFrom_pullback_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT : State T} {s : S} {n : Nat}
    (h : (embed e N).SpeciesCoverableFrom zT (e s) n) :
    N.SpeciesCoverableFrom (fun s' => zT (e s')) s n :=
  embed_coverable_single_pullback_of_injective
    (e := e) (N := N) he h

theorem embed_speciesCoverableFrom_lift_pullback_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT : State T} {s : S} {n : Nat}
    (h : N.SpeciesCoverableFrom (fun s' => zT (e s')) s n) :
    (embed e N).SpeciesCoverableFrom zT (e s) n :=
  embed_coverable_single_lift_pullback_of_injective
    (e := e) (N := N) he h

theorem embed_speciesCoverableFrom_pullback_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT : State T} {s : S} {n : Nat} :
    (embed e N).SpeciesCoverableFrom zT (e s) n <->
      N.SpeciesCoverableFrom (fun s' => zT (e s')) s n :=
  embed_coverable_single_pullback_iff_of_injective
    (e := e) (N := N) he

theorem embed_speciesCoverableFrom_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 : State S} {s : S} {n : Nat} :
    (embed e N).SpeciesCoverableFrom (State.embed e z0) (e s) n <->
      N.SpeciesCoverableFrom z0 s n := by
  simpa [State.embed_single_of_injective (e := e) he s n] using
    (embed_coverable_iff_of_injective
      (e := e) (N := N) he (z0 := z0) (target := State.single s n))

theorem embed_speciesCoverableFrom_not_exists_iff
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 : State S} {t : T} {n : Nat}
    (ht : Not (exists s : S, e s = t)) :
    (embed e N).SpeciesCoverableFrom (State.embed e z0) t n <->
      n = 0 := by
  rw [speciesCoverableFrom_iff]
  constructor
  · rintro ⟨zT, hReach, hn⟩
    have hSupport :
        forall t, Not (exists s : S, e s = t) -> zT t = 0 :=
      ((embed_reaches_supported_iff_of_injective
        (e := e) (N := N) he).1 hReach).1
    exact Nat.eq_zero_of_le_zero (by
      simpa [hSupport t ht] using hn)
  · intro hn
    subst hn
    exact ⟨State.embed e z0,
      Network.reaches_refl (embed e N) (State.embed e z0),
      Nat.zero_le _⟩

theorem embed_speciesCoverableFrom_image_or_not_exists_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {z0 : State S} {t : T} {n : Nat} :
    (embed e N).SpeciesCoverableFrom (State.embed e z0) t n <->
      (exists s : S, e s = t /\ N.SpeciesCoverableFrom z0 s n) \/
        (Not (exists s : S, e s = t) /\ n = 0) := by
  constructor
  · intro h
    by_cases ht : exists s : S, e s = t
    · rcases ht with ⟨s, hes⟩
      left
      refine ⟨s, hes, ?_⟩
      rw [← hes] at h
      exact (embed_speciesCoverableFrom_iff_of_injective
        (e := e) (N := N) he).1 h
    · right
      exact ⟨ht,
        (embed_speciesCoverableFrom_not_exists_iff
          (e := e) (N := N) he ht).1 h⟩
  · rintro (⟨s, hes, hBase⟩ | ⟨ht, hn⟩)
    · simpa [hes] using
        (embed_speciesCoverableFrom_of_injective
          (e := e) (N := N) he hBase)
    · exact (embed_speciesCoverableFrom_not_exists_iff
        (e := e) (N := N) he ht).2 hn

theorem embed_parallel_stepAt_iff {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    (e : S -> T) (N M : Network S)
    (i : (N.parallel M).I) (z z' : State T) :
    (embed e (N.parallel M)).StepAt i z z' <->
      ((embed e N).parallel (embed e M)).StepAt i z z' := by
  cases i <;> rfl

theorem embed_parallel_exec_iff {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    (e : S -> T) (N M : Network S)
    {z z' : State T} {is : List (N.parallel M).I} :
    (embed e (N.parallel M)).Exec z z' is <->
      ((embed e N).parallel (embed e M)).Exec z z' is :=
  ExecOf.congr_step
    (fun i z z' => embed_parallel_stepAt_iff e N M i z z')

theorem embed_parallel_reaches_iff {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    (e : S -> T) (N M : Network S) (z z' : State T) :
    (embed e (N.parallel M)).Reaches z z' <->
      ((embed e N).parallel (embed e M)).Reaches z z' := by
  constructor
  · rintro ⟨is, hExec⟩
    exact ⟨is, (embed_parallel_exec_iff e N M).mp hExec⟩
  · rintro ⟨is, hExec⟩
    exact ⟨is, (embed_parallel_exec_iff e N M).mpr hExec⟩

theorem embed_parallel_coverable_iff {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    (e : S -> T) (N M : Network S) (z target : State T) :
    (embed e (N.parallel M)).CoverableFrom z target <->
      ((embed e N).parallel (embed e M)).CoverableFrom z target := by
  constructor
  · rintro ⟨z', hReach, hCovers⟩
    exact ⟨z', (embed_parallel_reaches_iff e N M z z').mp hReach,
      hCovers⟩
  · rintro ⟨z', hReach, hCovers⟩
    exact ⟨z', (embed_parallel_reaches_iff e N M z z').mpr hReach,
      hCovers⟩

theorem embed_parallel_speciesCoverableFrom_iff
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    (e : S -> T) (N M : Network S)
    (z : State T) (species : T) (amount : Nat) :
    (embed e (N.parallel M)).SpeciesCoverableFrom z species amount <->
      ((embed e N).parallel (embed e M)).SpeciesCoverableFrom
        z species amount :=
  embed_parallel_coverable_iff e N M z (State.single species amount)

theorem embed_sigma_stepAt_iff {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {A : Type w} [Fintype A]
    (e : S -> T) (Ns : A -> Network S)
    (i : (Network.sigma Ns).I) (z z' : State T) :
    (embed e (Network.sigma Ns)).StepAt i z z' <->
      (Network.sigma (fun a => embed e (Ns a))).StepAt i z z' := by
  rcases i with ⟨a, i⟩
  rfl

theorem embed_sigma_exec_iff {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {A : Type w} [Fintype A]
    (e : S -> T) (Ns : A -> Network S)
    {z z' : State T} {is : List (Network.sigma Ns).I} :
    (embed e (Network.sigma Ns)).Exec z z' is <->
      (Network.sigma (fun a => embed e (Ns a))).Exec z z' is :=
  ExecOf.congr_step
    (fun i z z' => embed_sigma_stepAt_iff e Ns i z z')

theorem embed_sigma_reaches_iff {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {A : Type w} [Fintype A]
    (e : S -> T) (Ns : A -> Network S) (z z' : State T) :
    (embed e (Network.sigma Ns)).Reaches z z' <->
      (Network.sigma (fun a => embed e (Ns a))).Reaches z z' := by
  constructor
  · rintro ⟨is, hExec⟩
    exact ⟨is, (embed_sigma_exec_iff e Ns).mp hExec⟩
  · rintro ⟨is, hExec⟩
    exact ⟨is, (embed_sigma_exec_iff e Ns).mpr hExec⟩

theorem embed_sigma_coverable_iff {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {A : Type w} [Fintype A]
    (e : S -> T) (Ns : A -> Network S) (z target : State T) :
    (embed e (Network.sigma Ns)).CoverableFrom z target <->
      (Network.sigma (fun a => embed e (Ns a))).CoverableFrom z target := by
  constructor
  · rintro ⟨z', hReach, hCovers⟩
    exact ⟨z', (embed_sigma_reaches_iff e Ns z z').mp hReach,
      hCovers⟩
  · rintro ⟨z', hReach, hCovers⟩
    exact ⟨z', (embed_sigma_reaches_iff e Ns z z').mpr hReach,
      hCovers⟩

theorem embed_sigma_speciesCoverableFrom_iff
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {A : Type w} [Fintype A]
    (e : S -> T) (Ns : A -> Network S)
    (z : State T) (species : T) (amount : Nat) :
    (embed e (Network.sigma Ns)).SpeciesCoverableFrom z species amount <->
      (Network.sigma (fun a => embed e (Ns a))).SpeciesCoverableFrom
        z species amount :=
  embed_sigma_coverable_iff e Ns z (State.single species amount)

theorem embed_comp_stepAt_iff_of_injective
    {S : Type u} {T : Type v} {U : Type w}
    [Fintype S] [Fintype T] [Fintype U]
    [DecidableEq T] [DecidableEq U]
    {e : S -> T} {f : T -> U}
    (he : Function.Injective e) (hf : Function.Injective f)
    {N : Network S} {i : N.I} {z z' : State U} :
    (embed f (embed e N)).StepAt i z z' <->
      (embed (fun s => f (e s)) N).StepAt i z z' := by
  simp [Network.StepAt, embed, Reaction.embed_comp_of_injective (e := e) (f := f) he hf]

theorem embed_forall_not_touches_apply_iff_of_injective {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    (N : Network S) (s : S) :
    (forall i : (embed e N).I, ¬ ((embed e N).rxn i).Touches (e s)) <->
      forall i : N.I, ¬ (N.rxn i).Touches s := by
  constructor
  · intro h i hi
    exact h i ((Reaction.embed_touches_apply_iff_of_injective
      (e := e) he (N.rxn i) s).mpr hi)
  · intro h i hi
    exact h i ((Reaction.embed_touches_apply_iff_of_injective
      (e := e) he (N.rxn i) s).mp hi)

theorem embed_forall_not_touches_of_not_exists {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} {N : Network S} {t : T}
    (h : ¬ exists s : S, e s = t) :
    forall i : (embed e N).I, ¬ ((embed e N).rxn i).Touches t := by
  intro i
  simpa [embed] using
    (Reaction.embed_not_touches_of_not_exists
      (e := e) (rho := N.rxn i) (t := t) h)

theorem embed_stepAt_coord_eq_of_not_exists {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} {N : Network S} {t : T}
    (h : ¬ exists s : S, e s = t)
    {i : (embed e N).I} {zT zT' : State T}
    (hStep : (embed e N).StepAt i zT zT') :
    zT' t = zT t :=
  hStep.eq_on_not_touches
    (embed_rxn_not_Touches_of_not_exists
      (e := e) (N := N) i h)

theorem embed_exec_coord_eq_of_not_exists {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} {N : Network S} {t : T}
    (h : ¬ exists s : S, e s = t)
    {zT zT' : State T} {is : List (embed e N).I}
    (hExec : (embed e N).Exec zT zT' is) :
    zT' t = zT t :=
  Exec.coord_eq_of_not_touches hExec
    (fun i => embed_rxn_not_Touches_of_not_exists
      (e := e) (N := N) i h)

theorem embed_reaches_coord_eq_of_not_exists {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} {N : Network S} {t : T}
    (h : ¬ exists s : S, e s = t)
    {zT zT' : State T}
    (hReach : (embed e N).Reaches zT zT') :
    zT' t = zT t :=
  Reaches.coord_eq_of_not_touches hReach
    (fun i => embed_rxn_not_Touches_of_not_exists
      (e := e) (N := N) i h)

theorem embed_exec_pullback_frame_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT zT' : State T} {is : List N.I} :
    (embed e N).Exec zT zT' is <->
      (forall t, Not (exists s : S, e s = t) -> zT' t = zT t) /\
        N.Exec (fun s => zT (e s)) (fun s => zT' (e s)) is := by
  constructor
  · intro hExec
    exact ⟨
      fun t ht => embed_exec_coord_eq_of_not_exists
        (e := e) (N := N) ht hExec,
      embed_exec_pullback_of_injective
        (e := e) (N := N) he hExec⟩
  · rintro ⟨hFrame, hBaseExec⟩
    rcases embed_exec_lift_pullback_of_injective
        (e := e) (N := N) he hBaseExec with
      ⟨wT, hExecT, hPullback⟩
    have hwT : wT = zT' := by
      funext t
      by_cases ht : exists s : S, e s = t
      · rcases ht with ⟨s, rfl⟩
        exact congrFun hPullback s
      · calc
          wT t = zT t :=
            embed_exec_coord_eq_of_not_exists
              (e := e) (N := N) ht hExecT
          _ = zT' t := (hFrame t ht).symm
    simpa [hwT] using hExecT

theorem embed_reaches_pullback_frame_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT zT' : State T} :
    (embed e N).Reaches zT zT' <->
      (forall t, Not (exists s : S, e s = t) -> zT' t = zT t) /\
        N.Reaches (fun s => zT (e s)) (fun s => zT' (e s)) := by
  constructor
  · intro hReach
    exact ⟨
      fun t ht => embed_reaches_coord_eq_of_not_exists
        (e := e) (N := N) ht hReach,
      embed_reaches_pullback_of_injective
        (e := e) (N := N) he hReach⟩
  · rintro ⟨hFrame, hBaseReach⟩
    rcases embed_reaches_lift_pullback_of_injective
        (e := e) (N := N) he hBaseReach with
      ⟨wT, hReachT, hPullback⟩
    have hwT : wT = zT' := by
      funext t
      by_cases ht : exists s : S, e s = t
      · rcases ht with ⟨s, rfl⟩
        exact congrFun hPullback s
      · calc
          wT t = zT t :=
            embed_reaches_coord_eq_of_not_exists
              (e := e) (N := N) ht hReachT
          _ = zT' t := (hFrame t ht).symm
    simpa [hwT] using hReachT

theorem embed_coverable_pullback_frame_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT targetT : State T} :
    (embed e N).CoverableFrom zT targetT <->
      (forall t, Not (exists s : S, e s = t) -> targetT t <= zT t) /\
        N.CoverableFrom (fun s => zT (e s)) (fun s => targetT (e s)) := by
  constructor
  · intro hCover
    constructor
    · intro t ht
      rcases hCover with ⟨zT', hReach, hCovers⟩
      have hEq : zT' t = zT t :=
        embed_reaches_coord_eq_of_not_exists
          (e := e) (N := N) ht hReach
      simpa [hEq] using hCovers t
    · exact embed_coverable_pullback_of_injective
        (e := e) (N := N) he hCover
  · rintro ⟨hOffImage, hBaseCover⟩
    rcases hBaseCover with ⟨z, hBaseReach, hBaseCovers⟩
    rcases embed_reaches_lift_pullback_of_injective
        (e := e) (N := N) he hBaseReach with
      ⟨zT', hReachT, hPullback⟩
    refine ⟨zT', hReachT, ?_⟩
    intro t
    by_cases ht : exists s : S, e s = t
    · rcases ht with ⟨s, rfl⟩
      have hCoord := congrFun hPullback s
      simpa [hCoord] using hBaseCovers s
    · have hEq : zT' t = zT t :=
        embed_reaches_coord_eq_of_not_exists
          (e := e) (N := N) ht hReachT
      simpa [hEq] using hOffImage t ht

theorem embed_speciesCoverableFrom_offImage_iff
    {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq T]
    {e : S -> T} {N : Network S} {zT : State T} {t : T} {n : Nat}
    (ht : Not (exists s : S, e s = t)) :
    (embed e N).SpeciesCoverableFrom zT t n <-> n <= zT t := by
  rw [speciesCoverableFrom_iff]
  constructor
  · rintro ⟨zT', hReach, hn⟩
    have hEq : zT' t = zT t :=
      embed_reaches_coord_eq_of_not_exists
        (e := e) (N := N) ht hReach
    simpa [hEq] using hn
  · intro hn
    exact ⟨zT, Network.reaches_refl (embed e N) zT, hn⟩

theorem embed_speciesCoverableFrom_image_or_offImage_iff_of_injective
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    {e : S -> T} (he : Function.Injective e)
    {N : Network S} {zT : State T} {t : T} {n : Nat} :
    (embed e N).SpeciesCoverableFrom zT t n <->
      (exists s : S, e s = t /\
        N.SpeciesCoverableFrom (fun s' => zT (e s')) s n) \/
      (Not (exists s : S, e s = t) /\ n <= zT t) := by
  constructor
  · intro h
    by_cases ht : exists s : S, e s = t
    · rcases ht with ⟨s, hes⟩
      left
      refine ⟨s, hes, ?_⟩
      rw [← hes] at h
      exact (embed_speciesCoverableFrom_pullback_iff_of_injective
        (e := e) (N := N) he).1 h
    · right
      exact ⟨ht, (embed_speciesCoverableFrom_offImage_iff
        (e := e) (N := N) (zT := zT) (t := t) (n := n) ht).1 h⟩
  · rintro (⟨s, hes, hBase⟩ | ⟨ht, hn⟩)
    · simpa [hes] using
        (embed_speciesCoverableFrom_lift_pullback_of_injective
          (e := e) (N := N) he hBase)
    · exact (embed_speciesCoverableFrom_offImage_iff
        (e := e) (N := N) (zT := zT) (t := t) (n := n) ht).2 hn

theorem embed_inl_rxn_not_Touches_inr
    {S : Type u} {T : Type v}
    [Fintype S] [DecidableEq S] [DecidableEq T]
    {N : Network S} (i : N.I) (t : T) :
    ¬ ((embed (Sum.inl : S -> Sum S T) N).rxn i).Touches (Sum.inr t) := by
  apply embed_rxn_not_Touches_of_not_exists
  intro h
  rcases h with ⟨s, hs⟩
  cases hs

theorem embed_inr_rxn_not_Touches_inl
    {S : Type u} {T : Type v}
    [Fintype T] [DecidableEq S] [DecidableEq T]
    {M : Network T} (i : M.I) (s : S) :
    ¬ ((embed (Sum.inr : T -> Sum S T) M).rxn i).Touches (Sum.inl s) := by
  apply embed_rxn_not_Touches_of_not_exists
  intro h
  rcases h with ⟨t, ht⟩
  cases ht

end Network

end Ripple.sCRNUniversality
