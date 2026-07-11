import Ripple.sCRNUniversality.Core.Schedule

namespace Ripple.sCRNUniversality

namespace Network

namespace Path

variable {S : Type u}

def AlwaysEnabledFrom {N : Network S} (path : N.Path)
    (i : N.I) (t0 : Nat) : Prop :=
  forall t, t0 <= t -> N.EnabledAt (path.state t) i

def EnabledInfinitelyOftenFrom {N : Network S} (path : N.Path)
    (i : N.I) (t0 : Nat) : Prop :=
  forall t, t0 <= t ->
    exists u, t <= u /\ N.EnabledAt (path.state u) i

def FiresInfinitelyOftenFrom {N : Network S} (path : N.Path)
    (i : N.I) (t0 : Nat) : Prop :=
  forall t, t0 <= t ->
    exists u, t <= u /\ path.fired u = some i

def WeaklyFairAt {N : Network S} (path : N.Path)
    (i : N.I) (t0 : Nat) : Prop :=
  path.AlwaysEnabledFrom i t0 -> path.EventuallyFires i t0

def WeaklyFair {N : Network S} (path : N.Path) : Prop :=
  forall i t0, path.WeaklyFairAt i t0

def StronglyFairAt {N : Network S} (path : N.Path)
    (i : N.I) (t0 : Nat) : Prop :=
  path.EnabledInfinitelyOftenFrom i t0 -> path.FiresInfinitelyOftenFrom i t0

def StronglyFair {N : Network S} (path : N.Path) : Prop :=
  forall i t0, path.StronglyFairAt i t0

theorem alwaysEnabledFrom_mono_start
    {N : Network S} {path : N.Path} {i : N.I}
    {t0 t1 : Nat}
    (ht : t0 <= t1)
    (h : path.AlwaysEnabledFrom i t0) :
    path.AlwaysEnabledFrom i t1 := by
  intro t ht1
  exact h t (le_trans ht ht1)

theorem enabledInfinitelyOftenFrom_mono_start
    {N : Network S} {path : N.Path} {i : N.I}
    {t0 t1 : Nat}
    (ht : t0 <= t1)
    (h : path.EnabledInfinitelyOftenFrom i t0) :
    path.EnabledInfinitelyOftenFrom i t1 := by
  intro t ht1
  exact h t (le_trans ht ht1)

theorem firesInfinitelyOftenFrom_mono_start
    {N : Network S} {path : N.Path} {i : N.I}
    {t0 t1 : Nat}
    (ht : t0 <= t1)
    (h : path.FiresInfinitelyOftenFrom i t0) :
    path.FiresInfinitelyOftenFrom i t1 := by
  intro t ht1
  exact h t (le_trans ht ht1)

theorem enabledInfinitelyOftenFrom_of_alwaysEnabledFrom
    {N : Network S} {path : N.Path} {i : N.I}
    {t0 : Nat}
    (h : path.AlwaysEnabledFrom i t0) :
    path.EnabledInfinitelyOftenFrom i t0 := by
  intro t ht
  exact ⟨t, le_rfl, h t ht⟩

theorem eventuallyFires_of_firesInfinitelyOftenFrom
    {N : Network S} {path : N.Path} {i : N.I}
    {t0 : Nat}
    (h : path.FiresInfinitelyOftenFrom i t0) :
    path.EventuallyFires i t0 := by
  exact h t0 le_rfl

theorem eventuallyFires_of_weaklyFairAt
    {N : Network S} {path : N.Path} {i : N.I}
    {t0 : Nat}
    (hfair : path.WeaklyFairAt i t0)
    (henabled : path.AlwaysEnabledFrom i t0) :
    path.EventuallyFires i t0 :=
  hfair henabled

theorem eventuallyFires_of_weaklyFair
    {N : Network S} {path : N.Path} {i : N.I}
    {t0 : Nat}
    (hfair : path.WeaklyFair)
    (henabled : path.AlwaysEnabledFrom i t0) :
    path.EventuallyFires i t0 :=
  eventuallyFires_of_weaklyFairAt (hfair i t0) henabled

theorem eventuallyFiresList_of_weaklyFair
    {N : Network S} {path : N.Path}
    {t0 : Nat} {is : List N.I}
    (hfair : path.WeaklyFair)
    (henabled : forall i, i ∈ is -> path.AlwaysEnabledFrom i t0) :
    path.EventuallyFiresList t0 is := by
  induction is generalizing t0 with
  | nil =>
      trivial
  | cons i is ih =>
      rcases eventuallyFires_of_weaklyFair hfair
          (henabled i List.mem_cons_self) with
        ⟨u, htu, hfired⟩
      refine ⟨u, htu, hfired, ih ?_⟩
      intro j hj
      exact alwaysEnabledFrom_mono_start
        (Nat.le_trans htu (Nat.le_succ u))
        (henabled j (List.mem_cons_of_mem i hj))

theorem eventuallyFiresIntendedSchedule_of_weaklyFair
    {N : Network S} {path : N.Path}
    {t0 : Nat} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1)
    (hfair : path.WeaklyFair)
    (henabled :
      forall i, i ∈ I.schedule -> path.AlwaysEnabledFrom i t0) :
    path.EventuallyFiresList t0 I.schedule :=
  eventuallyFiresList_of_weaklyFair hfair henabled

theorem firesInfinitelyOftenFrom_of_stronglyFairAt
    {N : Network S} {path : N.Path} {i : N.I}
    {t0 : Nat}
    (hfair : path.StronglyFairAt i t0)
    (henabled : path.EnabledInfinitelyOftenFrom i t0) :
    path.FiresInfinitelyOftenFrom i t0 :=
  hfair henabled

theorem firesInfinitelyOftenFrom_of_stronglyFair
    {N : Network S} {path : N.Path} {i : N.I}
    {t0 : Nat}
    (hfair : path.StronglyFair)
    (henabled : path.EnabledInfinitelyOftenFrom i t0) :
    path.FiresInfinitelyOftenFrom i t0 :=
  firesInfinitelyOftenFrom_of_stronglyFairAt (hfair i t0) henabled

theorem eventuallyFiresList_of_stronglyFair
    {N : Network S} {path : N.Path}
    {t0 : Nat} {is : List N.I}
    (hfair : path.StronglyFair)
    (henabled :
      forall i, i ∈ is -> path.EnabledInfinitelyOftenFrom i t0) :
    path.EventuallyFiresList t0 is := by
  induction is generalizing t0 with
  | nil =>
      trivial
  | cons i is ih =>
      rcases firesInfinitelyOftenFrom_of_stronglyFair hfair
          (henabled i List.mem_cons_self) t0 le_rfl with
        ⟨u, htu, hfired⟩
      refine ⟨u, htu, hfired, ih ?_⟩
      intro j hj
      exact enabledInfinitelyOftenFrom_mono_start
        (Nat.le_trans htu (Nat.le_succ u))
        (henabled j (List.mem_cons_of_mem i hj))

theorem eventuallyFiresIntendedSchedule_of_stronglyFair
    {N : Network S} {path : N.Path}
    {t0 : Nat} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1)
    (hfair : path.StronglyFair)
    (henabled :
      forall i, i ∈ I.schedule -> path.EnabledInfinitelyOftenFrom i t0) :
    path.EventuallyFiresList t0 I.schedule :=
  eventuallyFiresList_of_stronglyFair hfair henabled

theorem weaklyFairAt_of_stronglyFairAt
    {N : Network S} {path : N.Path} {i : N.I}
    {t0 : Nat}
    (hfair : path.StronglyFairAt i t0) :
    path.WeaklyFairAt i t0 := by
  intro henabled
  exact eventuallyFires_of_firesInfinitelyOftenFrom
    (hfair (enabledInfinitelyOftenFrom_of_alwaysEnabledFrom henabled))

theorem weaklyFair_of_stronglyFair
    {N : Network S} {path : N.Path}
    (hfair : path.StronglyFair) :
    path.WeaklyFair := by
  intro i t0
  exact weaklyFairAt_of_stronglyFairAt (hfair i t0)

end Path

end Network

end Ripple.sCRNUniversality
