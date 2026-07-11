import Mathlib.Data.Fintype.Basic
import Ripple.sCRNUniversality.Core.OneReaction

namespace Ripple.sCRNUniversality

namespace State

variable {S : Type u}

def EqOn (P : S -> Prop) (z z' : State S) : Prop :=
  forall s, P s -> z s = z' s

def ZeroOn (P : S -> Prop) (z : State S) : Prop :=
  forall s, P s -> z s = 0

theorem EqOn.refl (P : S -> Prop) (z : State S) :
    EqOn P z z := by
  intro s _hs
  rfl

theorem EqOn.symm {P : S -> Prop} {z z' : State S}
    (h : EqOn P z z') :
    EqOn P z' z := by
  intro s hs
  exact (h s hs).symm

theorem EqOn.trans {P : S -> Prop} {x y z : State S}
    (hxy : EqOn P x y) (hyz : EqOn P y z) :
    EqOn P x z := by
  intro s hs
  exact (hxy s hs).trans (hyz s hs)

theorem EqOn.mono {P R : S -> Prop} {z z' : State S}
    (h : EqOn R z z')
    (hPR : forall s, P s -> R s) :
    EqOn P z z' := by
  intro s hs
  exact h s (hPR s hs)

theorem EqOn.add_right {P : S -> Prop} {z z' extra : State S}
    (h : EqOn P z z') :
    EqOn P (State.add z extra) (State.add z' extra) := by
  intro s hs
  simp [State.add, h s hs]

theorem EqOn.add_left {P : S -> Prop} {z z' extra : State S}
    (h : EqOn P z z') :
    EqOn P (State.add extra z) (State.add extra z') := by
  intro s hs
  simp [State.add, h s hs]

theorem ZeroOn.mono {P R : S -> Prop} {z : State S}
    (h : ZeroOn R z)
    (hPR : forall s, P s -> R s) :
    ZeroOn P z := by
  intro s hs
  exact h s (hPR s hs)

theorem ZeroOn.zero (P : S -> Prop) :
    ZeroOn P (State.zero : State S) := by
  intro s _hs
  rfl

theorem ZeroOn.add {P : S -> Prop} {x y : State S}
    (hx : ZeroOn P x) (hy : ZeroOn P y) :
    ZeroOn P (State.add x y) := by
  intro s hs
  simp [State.add, hx s hs, hy s hs]

theorem zeroOn_of_eqOn {P : S -> Prop} {z z' : State S}
    (hEq : EqOn P z' z) (hZero : ZeroOn P z) :
    ZeroOn P z' := by
  intro s hs
  exact (hEq s hs).trans (hZero s hs)

end State

namespace Reaction

variable {S : Type u}

def TouchesOnly (rho : Reaction S) (Footprint : S -> Prop) : Prop :=
  forall s, rho.Touches s -> Footprint s

def Requires (rho : Reaction S) (s : S) (n : Nat := 1) : Prop :=
  n <= rho.l s

def GuardedBy (rho : Reaction S) (guard : S) : Prop :=
  rho.Requires guard 1

theorem Untouches.of_touchesOnly_disjoint
    {rho : Reaction S} {Footprint Protected : S -> Prop}
    (hTouch : rho.TouchesOnly Footprint)
    (hDisjoint : forall s, Footprint s -> Protected s -> False) :
    rho.Untouches Protected := by
  intro s hs hTouches
  exact hDisjoint s (hTouch s hTouches) hs

theorem not_enabled_of_requires_of_lt
    {rho : Reaction S} {z : State S} {s : S} {n : Nat}
    (hReq : rho.Requires s n) (hz : z s < n) :
    Not (rho.enabled z) := by
  intro hEnabled
  have hnz : n <= z s := le_trans hReq (hEnabled s)
  exact (not_lt_of_ge hnz) hz

theorem not_enabled_of_guardedBy_zero
    {rho : Reaction S} {z : State S} {guard : S}
    (hGuard : rho.GuardedBy guard) (hz : z guard = 0) :
    Not (rho.enabled z) := by
  apply not_enabled_of_requires_of_lt hGuard
  simp [hz]

theorem not_firesTo_of_guardedBy_zero
    {rho : Reaction S} {z z' : State S} {guard : S}
    (hGuard : rho.GuardedBy guard) (hz : z guard = 0) :
    Not (rho.FiresTo z z') := by
  intro hFire
  exact not_enabled_of_guardedBy_zero hGuard hz hFire.enabled

end Reaction

namespace Network

variable {S : Type u}

def SchedulePreserves (N : Network S) (is : List N.I)
    (P : State S -> Prop) : Prop :=
  forall i, i ∈ is -> forall {z z'}, N.StepAt i z z' -> P z -> P z'

def ScheduleUntouches (N : Network S) (is : List N.I)
    (P : S -> Prop) : Prop :=
  forall i, i ∈ is -> (N.rxn i).Untouches P

def ScheduleTouchesOnly (N : Network S) (is : List N.I)
    (Footprint : S -> Prop) : Prop :=
  forall i, i ∈ is -> (N.rxn i).TouchesOnly Footprint

def ScheduleGuardedBy (N : Network S) (is : List N.I)
    (guard : S) : Prop :=
  forall i, i ∈ is -> (N.rxn i).GuardedBy guard

def GuardedByFamily (N : Network S) (guard : N.I -> S) : Prop :=
  forall i, (N.rxn i).GuardedBy (guard i)

def HoareExec (N : Network S) (is : List N.I)
    (Pre : State S -> Prop)
    (Post : State S -> State S -> Prop) : Prop :=
  forall {z z'}, N.Exec z z' is -> Pre z -> Post z z'

def ScheduleClears (N : Network S) (is : List N.I)
    (Garbage : S -> Prop) : Prop :=
  N.HoareExec is (State.ZeroOn Garbage)
    (fun _ z' => State.ZeroOn Garbage z')

def ExecutableSchedule (N : Network S) (z : State S)
    (is : List N.I) : Prop :=
  exists z', N.Exec z z' is

def ExecutableAfterPrefix (N : Network S) (z : State S)
    (pref suffix : List N.I) : Prop :=
  exists zMid, N.Exec z zMid pref /\ N.ExecutableSchedule zMid suffix

structure IntendedSchedule (N : Network S) (z0 z1 : State S) where
  schedule : List N.I
  exec : N.Exec z0 z1 schedule

structure BoundedIntendedSchedule
    (N : Network S) (bound : Nat) (z0 z1 : State S) where
  schedule : List N.I
  exec : N.Exec z0 z1 schedule
  length_bound : schedule.length <= bound

def BadIndexSet (N : Network S) : Type _ :=
  N.I -> Prop

theorem scheduleUntouches_of_scheduleTouchesOnly_disjoint
    {N : Network S} {is : List N.I}
    {Footprint Protected : S -> Prop}
    (hTouch : N.ScheduleTouchesOnly is Footprint)
    (hDisjoint : forall s, Footprint s -> Protected s -> False) :
    N.ScheduleUntouches is Protected := by
  intro i hi
  exact Reaction.Untouches.of_touchesOnly_disjoint
    (hTouch i hi) hDisjoint

theorem schedulePreserves_nil
    {N : Network S} {P : State S -> Prop} :
    N.SchedulePreserves [] P := by
  intro i hi
  simp at hi

theorem schedulePreserves_singleton
    {N : Network S} {i : N.I} {P : State S -> Prop}
    (hPres :
      forall {z z'}, N.StepAt i z z' -> P z -> P z') :
    N.SchedulePreserves [i] P := by
  intro j hj z z' hStep hP
  have hji : j = i := by
    simpa using hj
  cases hji
  exact hPres hStep hP

theorem schedulePreserves_append
    {N : Network S} {is js : List N.I} {P : State S -> Prop}
    (hLeft : N.SchedulePreserves is P)
    (hRight : N.SchedulePreserves js P) :
    N.SchedulePreserves (is ++ js) P := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hLeft i hi
  · exact hRight i hi

theorem schedulePreserves_of_stepInvariant
    {N : Network S} {is : List N.I} {P : State S -> Prop}
    (hInv : N.StepInvariant P) :
    N.SchedulePreserves is P := by
  intro _i _hi _z _z' hStep hP
  exact hInv hStep hP

theorem schedulePreserves_of_subset
    {N : Network S} {is js : List N.I} {P : State S -> Prop}
    (h : N.SchedulePreserves is P)
    (hsubset : forall i, i ∈ js -> i ∈ is) :
    N.SchedulePreserves js P := by
  intro i hi z z' hStep hP
  exact h i (hsubset i hi) hStep hP

theorem scheduleUntouches_nil
    {N : Network S} {P : S -> Prop} :
    N.ScheduleUntouches [] P := by
  intro i hi
  simp at hi

theorem scheduleUntouches_singleton
    {N : Network S} {i : N.I} {P : S -> Prop}
    (hUntouches : (N.rxn i).Untouches P) :
    N.ScheduleUntouches [i] P := by
  intro j hj
  have hji : j = i := by
    simpa using hj
  cases hji
  exact hUntouches

theorem scheduleUntouches_append
    {N : Network S} {is js : List N.I} {P : S -> Prop}
    (hLeft : N.ScheduleUntouches is P)
    (hRight : N.ScheduleUntouches js P) :
    N.ScheduleUntouches (is ++ js) P := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hLeft i hi
  · exact hRight i hi

theorem scheduleUntouches_of_subset
    {N : Network S} {is js : List N.I} {P : S -> Prop}
    (h : N.ScheduleUntouches is P)
    (hsubset : forall i, i ∈ js -> i ∈ is) :
    N.ScheduleUntouches js P := by
  intro i hi
  exact h i (hsubset i hi)

theorem scheduleTouchesOnly_nil
    {N : Network S} {Footprint : S -> Prop} :
    N.ScheduleTouchesOnly [] Footprint := by
  intro i hi
  simp at hi

theorem scheduleTouchesOnly_singleton
    {N : Network S} {i : N.I} {Footprint : S -> Prop}
    (hTouches : (N.rxn i).TouchesOnly Footprint) :
    N.ScheduleTouchesOnly [i] Footprint := by
  intro j hj
  have hji : j = i := by
    simpa using hj
  cases hji
  exact hTouches

theorem scheduleTouchesOnly_append
    {N : Network S} {is js : List N.I} {Footprint : S -> Prop}
    (hLeft : N.ScheduleTouchesOnly is Footprint)
    (hRight : N.ScheduleTouchesOnly js Footprint) :
    N.ScheduleTouchesOnly (is ++ js) Footprint := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hLeft i hi
  · exact hRight i hi

theorem scheduleTouchesOnly_of_subset
    {N : Network S} {is js : List N.I} {Footprint : S -> Prop}
    (h : N.ScheduleTouchesOnly is Footprint)
    (hsubset : forall i, i ∈ js -> i ∈ is) :
    N.ScheduleTouchesOnly js Footprint := by
  intro i hi
  exact h i (hsubset i hi)

theorem scheduleGuardedBy_nil
    {N : Network S} {guard : S} :
    N.ScheduleGuardedBy [] guard := by
  intro i hi
  simp at hi

theorem scheduleGuardedBy_singleton
    {N : Network S} {i : N.I} {guard : S}
    (hGuard : (N.rxn i).GuardedBy guard) :
    N.ScheduleGuardedBy [i] guard := by
  intro j hj
  have hji : j = i := by
    simpa using hj
  cases hji
  exact hGuard

theorem scheduleGuardedBy_append
    {N : Network S} {is js : List N.I} {guard : S}
    (hLeft : N.ScheduleGuardedBy is guard)
    (hRight : N.ScheduleGuardedBy js guard) :
    N.ScheduleGuardedBy (is ++ js) guard := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hLeft i hi
  · exact hRight i hi

theorem scheduleGuardedBy_of_subset
    {N : Network S} {is js : List N.I} {guard : S}
    (h : N.ScheduleGuardedBy is guard)
    (hsubset : forall i, i ∈ js -> i ∈ is) :
    N.ScheduleGuardedBy js guard := by
  intro i hi
  exact h i (hsubset i hi)

theorem scheduleGuardedBy_of_guardedByFamily_eq_on
    {N : Network S} {is : List N.I} {guardFamily : N.I -> S}
    {guard : S}
    (hGuard : N.GuardedByFamily guardFamily)
    (hEq : forall i, i ∈ is -> guardFamily i = guard) :
    N.ScheduleGuardedBy is guard := by
  intro i hi
  simpa [hEq i hi] using hGuard i

theorem scheduleGuardedBy_replicate
    {N : Network S} {i : N.I} {guard : S} {k : Nat}
    (hGuard : (N.rxn i).GuardedBy guard) :
    N.ScheduleGuardedBy (List.replicate k i) guard := by
  intro j hj
  have hji : j = i := List.eq_of_mem_replicate hj
  cases hji
  exact hGuard

theorem scheduleGuardedBy_of_guardedByFamily_const
    {N : Network S} {is : List N.I} {guard : S}
    (hGuard : N.GuardedByFamily (fun _ => guard)) :
    N.ScheduleGuardedBy is guard := by
  exact scheduleGuardedBy_of_guardedByFamily_eq_on
    hGuard (by intro _i _hi; rfl)

theorem parallel_schedulePreserves_inl
    {N M : Network S} {is : List N.I} {P : State S -> Prop}
    (hPres : N.SchedulePreserves is P) :
    (N.parallel M).SchedulePreserves (is.map Sum.inl) P := by
  intro i hi z z' hStep hP
  rcases List.mem_map.mp hi with ⟨j, hj, hji⟩
  cases hji
  exact hPres j hj ((Network.parallel_stepAt_inl N M).1 hStep) hP

theorem parallel_schedulePreserves_inr
    {N M : Network S} {is : List M.I} {P : State S -> Prop}
    (hPres : M.SchedulePreserves is P) :
    (N.parallel M).SchedulePreserves (is.map Sum.inr) P := by
  intro i hi z z' hStep hP
  rcases List.mem_map.mp hi with ⟨j, hj, hji⟩
  cases hji
  exact hPres j hj ((Network.parallel_stepAt_inr N M).1 hStep) hP

theorem sigma_schedulePreserves
    {A : Type v} [Fintype A] (Ns : A -> Network S) (a : A)
    {is : List (Ns a).I} {P : State S -> Prop}
    (hPres : (Ns a).SchedulePreserves is P) :
    (Network.sigma Ns).SchedulePreserves
      (is.map (fun i => Sigma.mk a i)) P := by
  intro idx hidx z z' hStep hP
  rcases List.mem_map.mp hidx with ⟨j, hj, hji⟩
  cases hji
  exact hPres j hj ((Network.sigma_stepAt Ns).1 hStep) hP

theorem sigma_schedulePreserves_iff
    {A : Type v} [Fintype A] {Ns : A -> Network S} {a : A}
    {is : List (Ns a).I} {P : State S -> Prop} :
    (Network.sigma Ns).SchedulePreserves
      (is.map (fun i => Sigma.mk a i)) P <->
      (Ns a).SchedulePreserves is P := by
  constructor
  · intro hPres i hi z z' hStep hP
    exact hPres (Sigma.mk a i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
      ((Network.sigma_stepAt Ns).2 hStep) hP
  · exact sigma_schedulePreserves Ns a

theorem parallel_schedulePreserves_inl_iff
    {N M : Network S} {is : List N.I} {P : State S -> Prop} :
    (N.parallel M).SchedulePreserves (is.map Sum.inl) P <->
      N.SchedulePreserves is P := by
  constructor
  · intro hPres i hi z z' hStep hP
    exact hPres (Sum.inl i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
      ((Network.parallel_stepAt_inl N M).2 hStep) hP
  · exact parallel_schedulePreserves_inl

theorem parallel_schedulePreserves_inr_iff
    {N M : Network S} {is : List M.I} {P : State S -> Prop} :
    (N.parallel M).SchedulePreserves (is.map Sum.inr) P <->
      M.SchedulePreserves is P := by
  constructor
  · intro hPres i hi z z' hStep hP
    exact hPres (Sum.inr i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
      ((Network.parallel_stepAt_inr N M).2 hStep) hP
  · exact parallel_schedulePreserves_inr

theorem parallel_scheduleUntouches_inl
    {N M : Network S} {is : List N.I} {P : S -> Prop}
    (hUntouches : N.ScheduleUntouches is P) :
    (N.parallel M).ScheduleUntouches (is.map Sum.inl) P := by
  intro i hi
  rcases List.mem_map.mp hi with ⟨j, hj, hji⟩
  cases hji
  exact hUntouches j hj

theorem parallel_scheduleUntouches_inr
    {N M : Network S} {is : List M.I} {P : S -> Prop}
    (hUntouches : M.ScheduleUntouches is P) :
    (N.parallel M).ScheduleUntouches (is.map Sum.inr) P := by
  intro i hi
  rcases List.mem_map.mp hi with ⟨j, hj, hji⟩
  cases hji
  exact hUntouches j hj

theorem sigma_scheduleUntouches
    {A : Type v} [Fintype A] (Ns : A -> Network S) (a : A)
    {is : List (Ns a).I} {P : S -> Prop}
    (hUntouches : (Ns a).ScheduleUntouches is P) :
    (Network.sigma Ns).ScheduleUntouches
      (is.map (fun i => Sigma.mk a i)) P := by
  intro idx hidx
  rcases List.mem_map.mp hidx with ⟨j, hj, hji⟩
  cases hji
  exact hUntouches j hj

theorem sigma_scheduleUntouches_iff
    {A : Type v} [Fintype A] {Ns : A -> Network S} {a : A}
    {is : List (Ns a).I} {P : S -> Prop} :
    (Network.sigma Ns).ScheduleUntouches
      (is.map (fun i => Sigma.mk a i)) P <->
      (Ns a).ScheduleUntouches is P := by
  constructor
  · intro hUntouches i hi
    simpa using
      hUntouches (Sigma.mk a i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · exact sigma_scheduleUntouches Ns a

theorem parallel_scheduleUntouches_inl_iff
    {N M : Network S} {is : List N.I} {P : S -> Prop} :
    (N.parallel M).ScheduleUntouches (is.map Sum.inl) P <->
      N.ScheduleUntouches is P := by
  constructor
  · intro hUntouches i hi
    exact hUntouches (Sum.inl i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · exact parallel_scheduleUntouches_inl

theorem parallel_scheduleUntouches_inr_iff
    {N M : Network S} {is : List M.I} {P : S -> Prop} :
    (N.parallel M).ScheduleUntouches (is.map Sum.inr) P <->
      M.ScheduleUntouches is P := by
  constructor
  · intro hUntouches i hi
    exact hUntouches (Sum.inr i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · exact parallel_scheduleUntouches_inr

theorem parallel_scheduleTouchesOnly_inl
    {N M : Network S} {is : List N.I} {Footprint : S -> Prop}
    (hTouches : N.ScheduleTouchesOnly is Footprint) :
    (N.parallel M).ScheduleTouchesOnly (is.map Sum.inl) Footprint := by
  intro i hi
  rcases List.mem_map.mp hi with ⟨j, hj, hji⟩
  cases hji
  exact hTouches j hj

theorem parallel_scheduleTouchesOnly_inr
    {N M : Network S} {is : List M.I} {Footprint : S -> Prop}
    (hTouches : M.ScheduleTouchesOnly is Footprint) :
    (N.parallel M).ScheduleTouchesOnly (is.map Sum.inr) Footprint := by
  intro i hi
  rcases List.mem_map.mp hi with ⟨j, hj, hji⟩
  cases hji
  exact hTouches j hj

theorem sigma_scheduleTouchesOnly
    {A : Type v} [Fintype A] (Ns : A -> Network S) (a : A)
    {is : List (Ns a).I} {Footprint : S -> Prop}
    (hTouches : (Ns a).ScheduleTouchesOnly is Footprint) :
    (Network.sigma Ns).ScheduleTouchesOnly
      (is.map (fun i => Sigma.mk a i)) Footprint := by
  intro idx hidx
  rcases List.mem_map.mp hidx with ⟨j, hj, hji⟩
  cases hji
  exact hTouches j hj

theorem sigma_scheduleTouchesOnly_iff
    {A : Type v} [Fintype A] {Ns : A -> Network S} {a : A}
    {is : List (Ns a).I} {Footprint : S -> Prop} :
    (Network.sigma Ns).ScheduleTouchesOnly
      (is.map (fun i => Sigma.mk a i)) Footprint <->
      (Ns a).ScheduleTouchesOnly is Footprint := by
  constructor
  · intro hTouches i hi
    simpa using
      hTouches (Sigma.mk a i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · exact sigma_scheduleTouchesOnly Ns a

theorem parallel_scheduleTouchesOnly_inl_iff
    {N M : Network S} {is : List N.I} {Footprint : S -> Prop} :
    (N.parallel M).ScheduleTouchesOnly (is.map Sum.inl) Footprint <->
      N.ScheduleTouchesOnly is Footprint := by
  constructor
  · intro hTouches i hi
    exact hTouches (Sum.inl i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · exact parallel_scheduleTouchesOnly_inl

theorem parallel_scheduleTouchesOnly_inr_iff
    {N M : Network S} {is : List M.I} {Footprint : S -> Prop} :
    (N.parallel M).ScheduleTouchesOnly (is.map Sum.inr) Footprint <->
      M.ScheduleTouchesOnly is Footprint := by
  constructor
  · intro hTouches i hi
    exact hTouches (Sum.inr i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · exact parallel_scheduleTouchesOnly_inr

theorem parallel_scheduleGuardedBy_inl
    {N M : Network S} {is : List N.I} {guard : S}
    (hGuard : N.ScheduleGuardedBy is guard) :
    (N.parallel M).ScheduleGuardedBy (is.map Sum.inl) guard := by
  intro i hi
  rcases List.mem_map.mp hi with ⟨j, hj, hji⟩
  cases hji
  exact hGuard j hj

theorem parallel_scheduleGuardedBy_inr
    {N M : Network S} {is : List M.I} {guard : S}
    (hGuard : M.ScheduleGuardedBy is guard) :
    (N.parallel M).ScheduleGuardedBy (is.map Sum.inr) guard := by
  intro i hi
  rcases List.mem_map.mp hi with ⟨j, hj, hji⟩
  cases hji
  exact hGuard j hj

theorem sigma_scheduleGuardedBy
    {A : Type v} [Fintype A] (Ns : A -> Network S) (a : A)
    {is : List (Ns a).I} {guard : S}
    (hGuard : (Ns a).ScheduleGuardedBy is guard) :
    (Network.sigma Ns).ScheduleGuardedBy
      (is.map (fun i => Sigma.mk a i)) guard := by
  intro idx hidx
  rcases List.mem_map.mp hidx with ⟨j, hj, hji⟩
  cases hji
  exact hGuard j hj

theorem sigma_scheduleGuardedBy_iff
    {A : Type v} [Fintype A] {Ns : A -> Network S} {a : A}
    {is : List (Ns a).I} {guard : S} :
    (Network.sigma Ns).ScheduleGuardedBy
      (is.map (fun i => Sigma.mk a i)) guard <->
      (Ns a).ScheduleGuardedBy is guard := by
  constructor
  · intro hGuard i hi
    simpa using
      hGuard (Sigma.mk a i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · exact sigma_scheduleGuardedBy Ns a

theorem parallel_scheduleGuardedBy_inl_iff
    {N M : Network S} {is : List N.I} {guard : S} :
    (N.parallel M).ScheduleGuardedBy (is.map Sum.inl) guard <->
      N.ScheduleGuardedBy is guard := by
  constructor
  · intro hGuard i hi
    exact hGuard (Sum.inl i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · exact parallel_scheduleGuardedBy_inl

theorem parallel_scheduleGuardedBy_inr_iff
    {N M : Network S} {is : List M.I} {guard : S} :
    (N.parallel M).ScheduleGuardedBy (is.map Sum.inr) guard <->
      M.ScheduleGuardedBy is guard := by
  constructor
  · intro hGuard i hi
    exact hGuard (Sum.inr i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · exact parallel_scheduleGuardedBy_inr

theorem parallel_guardedByFamily_iff
    {N M : Network S} {guardN : N.I -> S} {guardM : M.I -> S} :
    (N.parallel M).GuardedByFamily (Sum.elim guardN guardM) <->
      N.GuardedByFamily guardN /\ M.GuardedByFamily guardM := by
  constructor
  · intro hGuard
    constructor
    · intro i
      simpa [Network.parallel] using hGuard (Sum.inl i)
    · intro i
      simpa [Network.parallel] using hGuard (Sum.inr i)
  · rintro ⟨hN, hM⟩ i
    cases i with
    | inl i =>
        simpa [Network.parallel] using hN i
    | inr i =>
        simpa [Network.parallel] using hM i

theorem parallel_guardedByFamily_const_iff
    {N M : Network S} {guard : S} :
    (N.parallel M).GuardedByFamily (fun _ => guard) <->
      N.GuardedByFamily (fun _ => guard) /\
        M.GuardedByFamily (fun _ => guard) := by
  simpa using
    (parallel_guardedByFamily_iff
      (N := N) (M := M)
      (guardN := fun _ => guard)
      (guardM := fun _ => guard))

theorem parallel_guardedByFamily_const
    {N M : Network S} {guard : S}
    (hN : N.GuardedByFamily (fun _ => guard))
    (hM : M.GuardedByFamily (fun _ => guard)) :
    (N.parallel M).GuardedByFamily (fun _ => guard) := by
  exact parallel_guardedByFamily_const_iff.mpr ⟨hN, hM⟩

theorem not_enabledAt_of_guardedBy_zero
    {N : Network S} {i : N.I} {z : State S} {guard : S}
    (hGuard : (N.rxn i).GuardedBy guard) (hz : z guard = 0) :
    Not (N.EnabledAt z i) :=
  Reaction.not_enabled_of_guardedBy_zero hGuard hz

theorem not_stepAt_of_guardedBy_zero
    {N : Network S} {i : N.I} {z z' : State S} {guard : S}
    (hGuard : (N.rxn i).GuardedBy guard) (hz : z guard = 0) :
    Not (N.StepAt i z z') :=
  Reaction.not_firesTo_of_guardedBy_zero hGuard hz

theorem terminal_of_guardedByFamily_zero
    {N : Network S} {guard : N.I -> S} {z : State S}
    (hGuard : N.GuardedByFamily guard)
    (hZero : forall i, z (guard i) = 0) :
    N.Terminal z := by
  intro i hEnabled
  exact not_enabledAt_of_guardedBy_zero (hGuard i) (hZero i) hEnabled

namespace IntendedSchedule

def of_exec {N : Network S} {z0 z1 : State S} {is : List N.I}
    (hExec : N.Exec z0 z1 is) :
    N.IntendedSchedule z0 z1 where
  schedule := is
  exec := hExec

theorem reaches {N : Network S} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) :
    N.Reaches z0 z1 :=
  ⟨I.schedule, I.exec⟩

/-- Number of reaction firings in the intended deterministic schedule. -/
def firingCount {N : Network S} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) : Nat :=
  I.schedule.length

@[simp]
theorem firingCount_eq_length {N : Network S} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) :
    I.firingCount = I.schedule.length := by
  rfl

def toBoundedIntendedSchedule {N : Network S}
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) :
    N.BoundedIntendedSchedule I.firingCount z0 z1 where
  schedule := I.schedule
  exec := I.exec
  length_bound := le_rfl

@[simp]
theorem toBoundedIntendedSchedule_schedule {N : Network S}
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) :
    I.toBoundedIntendedSchedule.schedule = I.schedule := by
  rfl

/-- Forward reachability wrapper for an intended deterministic schedule. -/
theorem forward_reaches {N : Network S} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) :
    N.Reaches z0 z1 :=
  I.reaches

theorem executableSchedule {N : Network S} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) :
    N.ExecutableSchedule z0 I.schedule :=
  ⟨z1, I.exec⟩

theorem applyHoareExec {N : Network S} {z0 z1 : State S}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop}
    (I : N.IntendedSchedule z0 z1)
    (hHoare : N.HoareExec I.schedule Pre Post)
    (hPre : Pre z0) :
    Post z0 z1 :=
  hHoare I.exec hPre

theorem hoareExec_exact {N : Network S} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) :
    N.HoareExec I.schedule
      (fun z => z = z0)
      (fun _ z' => z' = z1) := by
  intro z z' hExec hz
  subst hz
  exact Network.exec_unique hExec I.exec

theorem coverableFrom_of_covers {N : Network S}
    {z0 z1 target : State S}
    (I : N.IntendedSchedule z0 z1)
    (hCovers : Covers z1 target) :
    N.CoverableFrom z0 target :=
  Network.coverable_of_reaches_of_covers I.reaches hCovers

theorem coverableFrom_of_le {N : Network S}
    {z0 z1 target : State S}
    (I : N.IntendedSchedule z0 z1)
    (hTarget : forall s, target s <= z1 s) :
    N.CoverableFrom z0 target :=
  I.coverableFrom_of_covers hTarget

theorem speciesCoverableFrom_of_coord [DecidableEq S]
    {N : Network S} {z0 z1 : State S}
    {species : S} {amount : Nat}
    (I : N.IntendedSchedule z0 z1)
    (hamount : amount <= z1 species) :
    N.SpeciesCoverableFrom z0 species amount :=
  Network.speciesCoverableFrom_of_reaches_coord I.reaches hamount

theorem speciesCoverableFrom_one_of_pos [DecidableEq S]
    {N : Network S} {z0 z1 : State S}
    {species : S}
    (I : N.IntendedSchedule z0 z1)
    (hpos : 0 < z1 species) :
    N.SpeciesCoverableFrom z0 species :=
  Network.speciesCoverableFrom_one_of_reaches_pos I.reaches hpos

def append {N : Network S} {z0 z1 z2 : State S}
    (I : N.IntendedSchedule z0 z1)
    (J : N.IntendedSchedule z1 z2) :
    N.IntendedSchedule z0 z2 where
  schedule := I.schedule ++ J.schedule
  exec := ExecOf.append I.exec J.exec

def parallel_inl {N M : Network S} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) :
    (N.parallel M).IntendedSchedule z0 z1 where
  schedule := I.schedule.map Sum.inl
  exec := Network.parallel_exec_inl N M I.exec

def parallel_inr {N M : Network S} {z0 z1 : State S}
    (I : M.IntendedSchedule z0 z1) :
    (N.parallel M).IntendedSchedule z0 z1 where
  schedule := I.schedule.map Sum.inr
  exec := Network.parallel_exec_inr N M I.exec

def sigma {A : Type v} [Fintype A] {Ns : A -> Network S} {a : A}
    {z0 z1 : State S}
    (I : (Ns a).IntendedSchedule z0 z1) :
    (Network.sigma Ns).IntendedSchedule z0 z1 where
  schedule := I.schedule.map (fun i => Sigma.mk a i)
  exec := Network.sigma_exec Ns a I.exec

def add_right {N : Network S} {z0 z1 extra : State S}
    (I : N.IntendedSchedule z0 z1) :
    N.IntendedSchedule
      (State.add z0 extra) (State.add z1 extra) where
  schedule := I.schedule
  exec := Network.Exec.add_right I.exec

def add_left {N : Network S} {z0 z1 extra : State S}
    (I : N.IntendedSchedule z0 z1) :
    N.IntendedSchedule
      (State.add extra z0) (State.add extra z1) where
  schedule := I.schedule
  exec := Network.Exec.add_left I.exec

@[simp]
theorem append_schedule {N : Network S} {z0 z1 z2 : State S}
    (I : N.IntendedSchedule z0 z1)
    (J : N.IntendedSchedule z1 z2) :
    (I.append J).schedule = I.schedule ++ J.schedule := by
  rfl

@[simp]
theorem parallel_inl_schedule {N M : Network S} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) :
    (I.parallel_inl (M := M)).schedule = I.schedule.map Sum.inl := by
  rfl

@[simp]
theorem parallel_inr_schedule {N M : Network S} {z0 z1 : State S}
    (I : M.IntendedSchedule z0 z1) :
    (I.parallel_inr (N := N)).schedule = I.schedule.map Sum.inr := by
  rfl

@[simp]
theorem sigma_schedule {A : Type v} [Fintype A]
    {Ns : A -> Network S} {a : A} {z0 z1 : State S}
    (I : (Ns a).IntendedSchedule z0 z1) :
    I.sigma.schedule = I.schedule.map (fun i => Sigma.mk a i) := by
  rfl

@[simp]
theorem add_right_schedule {N : Network S} {z0 z1 extra : State S}
    (I : N.IntendedSchedule z0 z1) :
    (I.add_right (extra := extra)).schedule = I.schedule := by
  rfl

@[simp]
theorem add_left_schedule {N : Network S} {z0 z1 extra : State S}
    (I : N.IntendedSchedule z0 z1) :
    (I.add_left (extra := extra)).schedule = I.schedule := by
  rfl

@[simp]
theorem append_firingCount {N : Network S} {z0 z1 z2 : State S}
    (I : N.IntendedSchedule z0 z1)
    (J : N.IntendedSchedule z1 z2) :
    (I.append J).firingCount = I.firingCount + J.firingCount := by
  simp [append, firingCount, List.length_append]

@[simp]
theorem parallel_inl_firingCount {N M : Network S} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) :
    (I.parallel_inl (M := M)).firingCount = I.firingCount := by
  exact List.length_map (f := Sum.inl) (as := I.schedule)

@[simp]
theorem parallel_inr_firingCount {N M : Network S} {z0 z1 : State S}
    (I : M.IntendedSchedule z0 z1) :
    (I.parallel_inr (N := N)).firingCount = I.firingCount := by
  exact List.length_map (f := Sum.inr) (as := I.schedule)

@[simp]
theorem sigma_firingCount {A : Type v} [Fintype A]
    {Ns : A -> Network S} {a : A} {z0 z1 : State S}
    (I : (Ns a).IntendedSchedule z0 z1) :
    I.sigma.firingCount = I.firingCount := by
  exact List.length_map
    (f := fun i => (Sigma.mk a i : Sigma (fun a => (Ns a).I)))
    (as := I.schedule)

@[simp]
theorem add_right_firingCount {N : Network S} {z0 z1 extra : State S}
    (I : N.IntendedSchedule z0 z1) :
    (I.add_right (extra := extra)).firingCount = I.firingCount := by
  rfl

@[simp]
theorem add_left_firingCount {N : Network S} {z0 z1 extra : State S}
    (I : N.IntendedSchedule z0 z1) :
    (I.add_left (extra := extra)).firingCount = I.firingCount := by
  rfl

end IntendedSchedule

namespace BoundedIntendedSchedule

def of_exec {N : Network S} {bound : Nat}
    {z0 z1 : State S} {is : List N.I}
    (hExec : N.Exec z0 z1 is)
    (hbound : is.length <= bound) :
    N.BoundedIntendedSchedule bound z0 z1 where
  schedule := is
  exec := hExec
  length_bound := hbound

def toIntendedSchedule {N : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    N.IntendedSchedule z0 z1 where
  schedule := I.schedule
  exec := I.exec

@[simp]
theorem toIntendedSchedule_schedule {N : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    I.toIntendedSchedule.schedule = I.schedule := by
  rfl

theorem reaches {N : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    N.Reaches z0 z1 :=
  I.toIntendedSchedule.reaches

theorem executableSchedule {N : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    N.ExecutableSchedule z0 I.schedule :=
  ⟨z1, I.exec⟩

theorem applyHoareExec {N : Network S} {bound : Nat}
    {z0 z1 : State S}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hHoare : N.HoareExec I.schedule Pre Post)
    (hPre : Pre z0) :
    Post z0 z1 :=
  hHoare I.exec hPre

theorem hoareExec_exact {N : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    N.HoareExec I.schedule
      (fun z => z = z0)
      (fun _ z' => z' = z1) :=
  I.toIntendedSchedule.hoareExec_exact

theorem coverableFrom_of_covers {N : Network S} {bound : Nat}
    {z0 z1 target : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hCovers : Covers z1 target) :
    N.CoverableFrom z0 target :=
  I.toIntendedSchedule.coverableFrom_of_covers hCovers

theorem coverableFrom_of_le {N : Network S} {bound : Nat}
    {z0 z1 target : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hTarget : forall s, target s <= z1 s) :
    N.CoverableFrom z0 target :=
  I.coverableFrom_of_covers hTarget

theorem speciesCoverableFrom_of_coord [DecidableEq S]
    {N : Network S} {bound : Nat} {z0 z1 : State S}
    {species : S} {amount : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hamount : amount <= z1 species) :
    N.SpeciesCoverableFrom z0 species amount :=
  I.toIntendedSchedule.speciesCoverableFrom_of_coord hamount

theorem speciesCoverableFrom_one_of_pos [DecidableEq S]
    {N : Network S} {bound : Nat} {z0 z1 : State S}
    {species : S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hpos : 0 < z1 species) :
    N.SpeciesCoverableFrom z0 species :=
  I.toIntendedSchedule.speciesCoverableFrom_one_of_pos hpos

/-- Number of reaction firings in the bounded intended schedule. -/
def firingCount {N : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) : Nat :=
  I.schedule.length

@[simp]
theorem firingCount_eq_length {N : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    I.firingCount = I.schedule.length := by
  rfl

@[simp]
theorem toIntendedSchedule_firingCount {N : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    I.toIntendedSchedule.firingCount = I.firingCount := by
  rfl

theorem firingCount_le_bound {N : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    I.firingCount <= bound :=
  I.length_bound

def weakenBound {N : Network S} {bound bound' : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hbound : bound <= bound') :
    N.BoundedIntendedSchedule bound' z0 z1 where
  schedule := I.schedule
  exec := I.exec
  length_bound := le_trans I.length_bound hbound

@[simp]
theorem weakenBound_schedule {N : Network S} {bound bound' : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hbound : bound <= bound') :
    (I.weakenBound hbound).schedule = I.schedule := by
  rfl

@[simp]
theorem weakenBound_firingCount {N : Network S} {bound bound' : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hbound : bound <= bound') :
    (I.weakenBound hbound).firingCount = I.firingCount := by
  rfl

@[simp]
theorem weakenBound_toIntendedSchedule {N : Network S} {bound bound' : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hbound : bound <= bound') :
    (I.weakenBound hbound).toIntendedSchedule = I.toIntendedSchedule := by
  rfl

def append {N : Network S} {bound1 bound2 : Nat}
    {z0 z1 z2 : State S}
    (I : N.BoundedIntendedSchedule bound1 z0 z1)
    (J : N.BoundedIntendedSchedule bound2 z1 z2) :
    N.BoundedIntendedSchedule (bound1 + bound2) z0 z2 where
  schedule := I.schedule ++ J.schedule
  exec := ExecOf.append I.exec J.exec
  length_bound := by
    simpa [List.length_append] using
      Nat.add_le_add I.length_bound J.length_bound

def parallel_inl {N M : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    (N.parallel M).BoundedIntendedSchedule bound z0 z1 where
  schedule := I.schedule.map Sum.inl
  exec := Network.parallel_exec_inl N M I.exec
  length_bound := by
    simpa using I.length_bound

def parallel_inr {N M : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : M.BoundedIntendedSchedule bound z0 z1) :
    (N.parallel M).BoundedIntendedSchedule bound z0 z1 where
  schedule := I.schedule.map Sum.inr
  exec := Network.parallel_exec_inr N M I.exec
  length_bound := by
    simpa using I.length_bound

def sigma {A : Type v} [Fintype A] {Ns : A -> Network S} {a : A}
    {bound : Nat} {z0 z1 : State S}
    (I : (Ns a).BoundedIntendedSchedule bound z0 z1) :
    (Network.sigma Ns).BoundedIntendedSchedule bound z0 z1 where
  schedule := I.schedule.map (fun i => Sigma.mk a i)
  exec := Network.sigma_exec Ns a I.exec
  length_bound := by
    simpa using I.length_bound

def add_right {N : Network S} {bound : Nat}
    {z0 z1 extra : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    N.BoundedIntendedSchedule bound
      (State.add z0 extra) (State.add z1 extra) where
  schedule := I.schedule
  exec := Network.Exec.add_right I.exec
  length_bound := I.length_bound

def add_left {N : Network S} {bound : Nat}
    {z0 z1 extra : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    N.BoundedIntendedSchedule bound
      (State.add extra z0) (State.add extra z1) where
  schedule := I.schedule
  exec := Network.Exec.add_left I.exec
  length_bound := I.length_bound

@[simp]
theorem append_schedule {N : Network S} {bound1 bound2 : Nat}
    {z0 z1 z2 : State S}
    (I : N.BoundedIntendedSchedule bound1 z0 z1)
    (J : N.BoundedIntendedSchedule bound2 z1 z2) :
    (I.append J).schedule = I.schedule ++ J.schedule := by
  rfl

@[simp]
theorem parallel_inl_schedule {N M : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    (I.parallel_inl (M := M)).schedule = I.schedule.map Sum.inl := by
  rfl

@[simp]
theorem parallel_inr_schedule {N M : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : M.BoundedIntendedSchedule bound z0 z1) :
    (I.parallel_inr (N := N)).schedule = I.schedule.map Sum.inr := by
  rfl

@[simp]
theorem sigma_schedule {A : Type v} [Fintype A]
    {Ns : A -> Network S} {a : A}
    {bound : Nat} {z0 z1 : State S}
    (I : (Ns a).BoundedIntendedSchedule bound z0 z1) :
    I.sigma.schedule = I.schedule.map (fun i => Sigma.mk a i) := by
  rfl

@[simp]
theorem add_right_schedule {N : Network S} {bound : Nat}
    {z0 z1 extra : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    (I.add_right (extra := extra)).schedule = I.schedule := by
  rfl

@[simp]
theorem add_left_schedule {N : Network S} {bound : Nat}
    {z0 z1 extra : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    (I.add_left (extra := extra)).schedule = I.schedule := by
  rfl

@[simp]
theorem append_firingCount {N : Network S} {bound1 bound2 : Nat}
    {z0 z1 z2 : State S}
    (I : N.BoundedIntendedSchedule bound1 z0 z1)
    (J : N.BoundedIntendedSchedule bound2 z1 z2) :
    (I.append J).firingCount = I.firingCount + J.firingCount := by
  simp [append, firingCount, List.length_append]

@[simp]
theorem parallel_inl_firingCount {N M : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    (I.parallel_inl (M := M)).firingCount = I.firingCount := by
  exact List.length_map (f := Sum.inl) (as := I.schedule)

@[simp]
theorem parallel_inr_firingCount {N M : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : M.BoundedIntendedSchedule bound z0 z1) :
    (I.parallel_inr (N := N)).firingCount = I.firingCount := by
  exact List.length_map (f := Sum.inr) (as := I.schedule)

@[simp]
theorem sigma_firingCount {A : Type v} [Fintype A]
    {Ns : A -> Network S} {a : A}
    {bound : Nat} {z0 z1 : State S}
    (I : (Ns a).BoundedIntendedSchedule bound z0 z1) :
    I.sigma.firingCount = I.firingCount := by
  exact List.length_map
    (f := fun i => (Sigma.mk a i : Sigma (fun a => (Ns a).I)))
    (as := I.schedule)

@[simp]
theorem add_right_firingCount {N : Network S} {bound : Nat}
    {z0 z1 extra : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    (I.add_right (extra := extra)).firingCount = I.firingCount := by
  rfl

@[simp]
theorem add_left_firingCount {N : Network S} {bound : Nat}
    {z0 z1 extra : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    (I.add_left (extra := extra)).firingCount = I.firingCount := by
  rfl

@[simp]
theorem toIntendedSchedule_append {N : Network S} {bound1 bound2 : Nat}
    {z0 z1 z2 : State S}
    (I : N.BoundedIntendedSchedule bound1 z0 z1)
    (J : N.BoundedIntendedSchedule bound2 z1 z2) :
    (I.append J).toIntendedSchedule =
      I.toIntendedSchedule.append J.toIntendedSchedule := by
  rfl

@[simp]
theorem toIntendedSchedule_parallel_inl {N M : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    (I.parallel_inl (M := M)).toIntendedSchedule =
      I.toIntendedSchedule.parallel_inl := by
  rfl

@[simp]
theorem toIntendedSchedule_parallel_inr {N M : Network S} {bound : Nat}
    {z0 z1 : State S}
    (I : M.BoundedIntendedSchedule bound z0 z1) :
    (I.parallel_inr (N := N)).toIntendedSchedule =
      I.toIntendedSchedule.parallel_inr := by
  rfl

@[simp]
theorem toIntendedSchedule_sigma {A : Type v} [Fintype A]
    {Ns : A -> Network S} {a : A}
    {bound : Nat} {z0 z1 : State S}
    (I : (Ns a).BoundedIntendedSchedule bound z0 z1) :
    I.sigma.toIntendedSchedule = I.toIntendedSchedule.sigma := by
  rfl

@[simp]
theorem toIntendedSchedule_add_right {N : Network S} {bound : Nat}
    {z0 z1 extra : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    (I.add_right (extra := extra)).toIntendedSchedule =
      I.toIntendedSchedule.add_right := by
  rfl

@[simp]
theorem toIntendedSchedule_add_left {N : Network S} {bound : Nat}
    {z0 z1 extra : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) :
    (I.add_left (extra := extra)).toIntendedSchedule =
      I.toIntendedSchedule.add_left := by
  rfl

end BoundedIntendedSchedule

namespace IntendedSchedule

@[simp]
theorem toBoundedIntendedSchedule_toIntendedSchedule {N : Network S}
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) :
    I.toBoundedIntendedSchedule.toIntendedSchedule = I := by
  rfl

@[simp]
theorem toBoundedIntendedSchedule_firingCount {N : Network S}
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) :
    I.toBoundedIntendedSchedule.firingCount = I.firingCount := by
  rfl

end IntendedSchedule

def oneRxnNetwork_intendedSchedule
    {rho : Reaction S} {z z' : State S}
    (hfire : rho.FiresTo z z') :
    (oneRxnNetwork rho).IntendedSchedule z z' :=
  IntendedSchedule.of_exec (oneRxn_exec hfire)

@[simp]
theorem oneRxnNetwork_intendedSchedule_schedule
    {rho : Reaction S} {z z' : State S}
    (hfire : rho.FiresTo z z') :
    (oneRxnNetwork_intendedSchedule hfire).schedule =
      [OneRxnIdx.step] := by
  rfl

@[simp]
theorem oneRxnNetwork_intendedSchedule_firingCount
    {rho : Reaction S} {z z' : State S}
    (hfire : rho.FiresTo z z') :
    (oneRxnNetwork_intendedSchedule hfire).firingCount = 1 := by
  rfl

def oneRxnNetwork_boundedIntendedSchedule
    {rho : Reaction S} {z z' : State S}
    (hfire : rho.FiresTo z z') :
    (oneRxnNetwork rho).BoundedIntendedSchedule 1 z z' where
  schedule := [OneRxnIdx.step]
  exec := oneRxn_exec hfire
  length_bound := by simp

@[simp]
theorem oneRxnNetwork_boundedIntendedSchedule_schedule
    {rho : Reaction S} {z z' : State S}
    (hfire : rho.FiresTo z z') :
    (oneRxnNetwork_boundedIntendedSchedule hfire).schedule =
      [OneRxnIdx.step] := by
  rfl

@[simp]
theorem oneRxnNetwork_boundedIntendedSchedule_firingCount
    {rho : Reaction S} {z z' : State S}
    (hfire : rho.FiresTo z z') :
    (oneRxnNetwork_boundedIntendedSchedule hfire).firingCount = 1 := by
  rfl

@[simp]
theorem oneRxnNetwork_boundedIntendedSchedule_toIntendedSchedule
    {rho : Reaction S} {z z' : State S}
    (hfire : rho.FiresTo z z') :
    (oneRxnNetwork_boundedIntendedSchedule hfire).toIntendedSchedule =
      oneRxnNetwork_intendedSchedule hfire := by
  rfl

theorem oneRxnNetwork_scheduleGuardedBy
    {rho : Reaction S} {guard : S}
    (hGuard : rho.GuardedBy guard) :
    (oneRxnNetwork rho).ScheduleGuardedBy
      [OneRxnIdx.step] guard :=
  scheduleGuardedBy_singleton (by
    simpa [oneRxnNetwork] using hGuard)

theorem oneRxnNetwork_scheduleGuardedBy_replicate
    {rho : Reaction S} {guard : S} {k : Nat}
    (hGuard : rho.GuardedBy guard) :
    (oneRxnNetwork rho).ScheduleGuardedBy
      (List.replicate k OneRxnIdx.step) guard :=
  scheduleGuardedBy_replicate (by
    simpa [oneRxnNetwork] using hGuard)

theorem oneRxnNetwork_guardedByFamily_const
    {rho : Reaction S} {guard : S}
    (hGuard : rho.GuardedBy guard) :
    (oneRxnNetwork rho).GuardedByFamily
      (fun _ => guard) := by
  intro i
  cases i
  simpa [oneRxnNetwork] using hGuard

theorem oneRxnNetwork_not_enabledAt_step_of_guard_zero
    {rho : Reaction S} {guard : S} {z : State S}
    (hGuard : rho.GuardedBy guard)
    (hz : z guard = 0) :
    Not ((oneRxnNetwork rho).EnabledAt z OneRxnIdx.step) :=
  not_enabledAt_of_guardedBy_zero
    (N := oneRxnNetwork rho) (i := OneRxnIdx.step)
    (guard := guard)
    (by simpa [oneRxnNetwork] using hGuard)
    hz

theorem oneRxnNetwork_not_stepAt_step_of_guard_zero
    {rho : Reaction S} {guard : S} {z z' : State S}
    (hGuard : rho.GuardedBy guard)
    (hz : z guard = 0) :
    Not ((oneRxnNetwork rho).StepAt OneRxnIdx.step z z') :=
  not_stepAt_of_guardedBy_zero
    (N := oneRxnNetwork rho) (i := OneRxnIdx.step)
    (guard := guard)
    (by simpa [oneRxnNetwork] using hGuard)
    hz

theorem oneRxnNetwork_terminal_of_guard_zero
    {rho : Reaction S} {guard : S} {z : State S}
    (hGuard : rho.GuardedBy guard)
    (hz : z guard = 0) :
    (oneRxnNetwork rho).Terminal z :=
  terminal_of_guardedByFamily_zero
    (oneRxnNetwork_guardedByFamily_const hGuard)
    (by
      intro i
      cases i
      simpa using hz)

namespace ExecutableSchedule

theorem nil (N : Network S) (z : State S) :
    N.ExecutableSchedule z [] :=
  ⟨z, ExecOf.nil z⟩

theorem of_exec {N : Network S} {z z' : State S} {is : List N.I}
    (hExec : N.Exec z z' is) :
    N.ExecutableSchedule z is :=
  ⟨z', hExec⟩

theorem add_right {N : Network S} {z extra : State S}
    {is : List N.I}
    (hExecutable : N.ExecutableSchedule z is) :
    N.ExecutableSchedule (State.add z extra) is := by
  rcases hExecutable with ⟨z', hExec⟩
  exact ⟨State.add z' extra, Network.Exec.add_right hExec⟩

theorem add_left {N : Network S} {z extra : State S}
    {is : List N.I}
    (hExecutable : N.ExecutableSchedule z is) :
    N.ExecutableSchedule (State.add extra z) is := by
  rcases hExecutable with ⟨z', hExec⟩
  exact ⟨State.add extra z', Network.Exec.add_left hExec⟩

theorem exists_post_of_hoareExec
    {N : Network S} {z : State S} {is : List N.I}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop}
    (hExecutable : N.ExecutableSchedule z is)
    (hHoare : N.HoareExec is Pre Post)
    (hPre : Pre z) :
    exists z', N.Exec z z' is /\ Post z z' := by
  rcases hExecutable with ⟨z', hExec⟩
  exact ⟨z', hExec, hHoare hExec hPre⟩

theorem parallel_inl_iff {N M : Network S}
    {z : State S} {is : List N.I} :
    (N.parallel M).ExecutableSchedule z (is.map Sum.inl) <->
      N.ExecutableSchedule z is := by
  constructor
  · rintro ⟨z', hExec⟩
    exact ⟨z', (Network.parallel_exec_inl_iff N M).mp hExec⟩
  · rintro ⟨z', hExec⟩
    exact ⟨z', Network.parallel_exec_inl N M hExec⟩

theorem parallel_inl {N M : Network S}
    {z : State S} {is : List N.I}
    (h : N.ExecutableSchedule z is) :
    (N.parallel M).ExecutableSchedule z (is.map Sum.inl) :=
  parallel_inl_iff.mpr h

theorem parallel_inr_iff {N M : Network S}
    {z : State S} {is : List M.I} :
    (N.parallel M).ExecutableSchedule z (is.map Sum.inr) <->
      M.ExecutableSchedule z is := by
  constructor
  · rintro ⟨z', hExec⟩
    exact ⟨z', (Network.parallel_exec_inr_iff N M).mp hExec⟩
  · rintro ⟨z', hExec⟩
    exact ⟨z', Network.parallel_exec_inr N M hExec⟩

theorem parallel_inr {N M : Network S}
    {z : State S} {is : List M.I}
    (h : M.ExecutableSchedule z is) :
    (N.parallel M).ExecutableSchedule z (is.map Sum.inr) :=
  parallel_inr_iff.mpr h

theorem sigma_iff {A : Type v} [Fintype A]
    {Ns : A -> Network S} {a : A}
    {z : State S} {is : List (Ns a).I} :
    (Network.sigma Ns).ExecutableSchedule z
      (is.map (fun i => Sigma.mk a i)) <->
      (Ns a).ExecutableSchedule z is := by
  constructor
  · rintro ⟨z', hExec⟩
    exact ⟨z', (Network.sigma_exec_iff Ns a).mp hExec⟩
  · rintro ⟨z', hExec⟩
    exact ⟨z', Network.sigma_exec Ns a hExec⟩

theorem sigma {A : Type v} [Fintype A]
    {Ns : A -> Network S} {a : A}
    {z : State S} {is : List (Ns a).I}
    (h : (Ns a).ExecutableSchedule z is) :
    (Network.sigma Ns).ExecutableSchedule z
      (is.map (fun i => Sigma.mk a i)) :=
  sigma_iff.mpr h

theorem afterPrefix_add_right {N : Network S}
    {z extra : State S} {pref suffix : List N.I}
    (h : N.ExecutableAfterPrefix z pref suffix) :
    N.ExecutableAfterPrefix (State.add z extra) pref suffix := by
  rcases h with ⟨zMid, hPref, hSuffix⟩
  exact
    ⟨State.add zMid extra,
      Network.Exec.add_right hPref,
      add_right hSuffix⟩

theorem afterPrefix_add_left {N : Network S}
    {z extra : State S} {pref suffix : List N.I}
    (h : N.ExecutableAfterPrefix z pref suffix) :
    N.ExecutableAfterPrefix (State.add extra z) pref suffix := by
  rcases h with ⟨zMid, hPref, hSuffix⟩
  exact
    ⟨State.add extra zMid,
      Network.Exec.add_left hPref,
      add_left hSuffix⟩

theorem parallel_afterPrefix_inl_iff {N M : Network S}
    {z : State S} {pref suffix : List N.I} :
    (N.parallel M).ExecutableAfterPrefix z
      (pref.map Sum.inl) (suffix.map Sum.inl) <->
      N.ExecutableAfterPrefix z pref suffix := by
  constructor
  · rintro ⟨zMid, hPref, hSuffix⟩
    exact ⟨zMid,
      (Network.parallel_exec_inl_iff N M).mp hPref,
      parallel_inl_iff.mp hSuffix⟩
  · rintro ⟨zMid, hPref, hSuffix⟩
    exact ⟨zMid,
      Network.parallel_exec_inl N M hPref,
      parallel_inl hSuffix⟩

theorem parallel_afterPrefix_inl {N M : Network S}
    {z : State S} {pref suffix : List N.I}
    (h : N.ExecutableAfterPrefix z pref suffix) :
    (N.parallel M).ExecutableAfterPrefix z
      (pref.map Sum.inl) (suffix.map Sum.inl) :=
  parallel_afterPrefix_inl_iff.mpr h

theorem parallel_afterPrefix_inr_iff {N M : Network S}
    {z : State S} {pref suffix : List M.I} :
    (N.parallel M).ExecutableAfterPrefix z
      (pref.map Sum.inr) (suffix.map Sum.inr) <->
      M.ExecutableAfterPrefix z pref suffix := by
  constructor
  · rintro ⟨zMid, hPref, hSuffix⟩
    exact ⟨zMid,
      (Network.parallel_exec_inr_iff N M).mp hPref,
      parallel_inr_iff.mp hSuffix⟩
  · rintro ⟨zMid, hPref, hSuffix⟩
    exact ⟨zMid,
      Network.parallel_exec_inr N M hPref,
      parallel_inr hSuffix⟩

theorem parallel_afterPrefix_inr {N M : Network S}
    {z : State S} {pref suffix : List M.I}
    (h : M.ExecutableAfterPrefix z pref suffix) :
    (N.parallel M).ExecutableAfterPrefix z
      (pref.map Sum.inr) (suffix.map Sum.inr) :=
  parallel_afterPrefix_inr_iff.mpr h

theorem sigma_afterPrefix_iff {A : Type v} [Fintype A]
    {Ns : A -> Network S} {a : A}
    {z : State S} {pref suffix : List (Ns a).I} :
    (Network.sigma Ns).ExecutableAfterPrefix z
      (pref.map (fun i => Sigma.mk a i))
      (suffix.map (fun i => Sigma.mk a i)) <->
      (Ns a).ExecutableAfterPrefix z pref suffix := by
  constructor
  · rintro ⟨zMid, hPref, hSuffix⟩
    exact
      ⟨zMid,
        (Network.sigma_exec_iff Ns a).mp hPref,
        sigma_iff.mp hSuffix⟩
  · rintro ⟨zMid, hPref, hSuffix⟩
    exact
      ⟨zMid,
        Network.sigma_exec Ns a hPref,
        sigma hSuffix⟩

theorem sigma_afterPrefix {A : Type v} [Fintype A]
    {Ns : A -> Network S} {a : A}
    {z : State S} {pref suffix : List (Ns a).I}
    (h : (Ns a).ExecutableAfterPrefix z pref suffix) :
    (Network.sigma Ns).ExecutableAfterPrefix z
      (pref.map (fun i => Sigma.mk a i))
      (suffix.map (fun i => Sigma.mk a i)) :=
  sigma_afterPrefix_iff.mpr h

theorem append_iff {N : Network S} {z : State S}
    {is js : List N.I} :
    N.ExecutableSchedule z (is ++ js) <->
      N.ExecutableAfterPrefix z is js := by
  constructor
  · rintro ⟨zEnd, hExec⟩
    rcases ExecOf.split_append.mp hExec with ⟨zMid, hLeft, hRight⟩
    exact ⟨zMid, hLeft, ⟨zEnd, hRight⟩⟩
  · rintro ⟨zMid, hLeft, zEnd, hRight⟩
    exact ⟨zEnd, ExecOf.append hLeft hRight⟩

theorem append {N : Network S} {z zMid : State S}
    {is js : List N.I}
    (hLeft : N.Exec z zMid is)
    (hRight : N.ExecutableSchedule zMid js) :
    N.ExecutableSchedule z (is ++ js) :=
  append_iff.mpr ⟨zMid, hLeft, hRight⟩

theorem of_afterPrefix {N : Network S} {z : State S}
    {pref suffix : List N.I}
    (h : N.ExecutableAfterPrefix z pref suffix) :
    N.ExecutableSchedule z (pref ++ suffix) :=
  append_iff.mpr h

theorem exists_post_of_afterPrefix_hoareExec
    {N : Network S} {z : State S} {pref suffix : List N.I}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop}
    (hExecutable : N.ExecutableAfterPrefix z pref suffix)
    (hHoare : N.HoareExec (pref ++ suffix) Pre Post)
    (hPre : Pre z) :
    exists z', N.Exec z z' (pref ++ suffix) /\ Post z z' :=
  (of_afterPrefix hExecutable).exists_post_of_hoareExec hHoare hPre

theorem suffix_exec_of_append_exec {N : Network S}
    {z0 zMid zEnd : State S} {pref suffix : List N.I}
    (hExec : N.Exec z0 zEnd (pref ++ suffix))
    (hPref : N.Exec z0 zMid pref) :
    N.Exec zMid zEnd suffix := by
  rcases ExecOf.split_append.mp hExec with ⟨zMid', hPref', hSuffix⟩
  have hMid : zMid' = zMid := Network.exec_unique hPref' hPref
  subst hMid
  exact hSuffix

theorem head_enabled {N : Network S} {z : State S}
    {i : N.I} {is : List N.I}
    (h : N.ExecutableSchedule z (i :: is)) :
    N.EnabledAt z i := by
  rcases h with ⟨zEnd, hExec⟩
  rcases ExecOf.cons_iff.mp hExec with ⟨zMid, hStep, _hTail⟩
  exact hStep.enabled

theorem not_cons_of_scheduleGuardedBy_zero
    {N : Network S} {z : State S}
    {guard : S} {i : N.I} {is : List N.I}
    (hGuard : N.ScheduleGuardedBy (i :: is) guard)
    (hz : z guard = 0) :
    Not (N.ExecutableSchedule z (i :: is)) := by
  intro hExec
  exact not_enabledAt_of_guardedBy_zero
    (hGuard i List.mem_cons_self)
    hz
    (head_enabled hExec)

theorem not_cons_of_guardedByFamily_zero
    {N : Network S} {z : State S}
    {guard : N.I -> S} {i : N.I} {is : List N.I}
    (hGuard : N.GuardedByFamily guard)
    (hz : z (guard i) = 0) :
    Not (N.ExecutableSchedule z (i :: is)) := by
  intro hExec
  exact not_enabledAt_of_guardedBy_zero
    (hGuard i)
    hz
    (head_enabled hExec)

theorem not_terminal_of_cons {N : Network S} {z : State S}
    {i : N.I} {is : List N.I}
    (h : N.ExecutableSchedule z (i :: is)) :
    Not (N.Terminal z) := by
  exact fun hTerminal => hTerminal i (head_enabled h)

theorem not_cons_of_terminal {N : Network S} {z : State S}
    (hTerminal : N.Terminal z) (i : N.I) (is : List N.I) :
    Not (N.ExecutableSchedule z (i :: is)) := by
  intro hExec
  exact not_terminal_of_cons hExec hTerminal

end ExecutableSchedule

theorem not_exec_cons_of_scheduleGuardedBy_zero
    {N : Network S} {z z' : State S}
    {guard : S} {i : N.I} {is : List N.I}
    (hGuard : N.ScheduleGuardedBy (i :: is) guard)
    (hz : z guard = 0) :
    Not (N.Exec z z' (i :: is)) := by
  intro hExec
  exact ExecutableSchedule.not_cons_of_scheduleGuardedBy_zero
    hGuard hz (ExecutableSchedule.of_exec hExec)

theorem not_exec_cons_of_guardedByFamily_zero
    {N : Network S} {z z' : State S}
    {guard : N.I -> S} {i : N.I} {is : List N.I}
    (hGuard : N.GuardedByFamily guard)
    (hz : z (guard i) = 0) :
    Not (N.Exec z z' (i :: is)) := by
  intro hExec
  exact ExecutableSchedule.not_cons_of_guardedByFamily_zero
    hGuard hz (ExecutableSchedule.of_exec hExec)

theorem indices_eq_nil_of_exec_scheduleGuardedBy_zero
    {N : Network S} {is : List N.I}
    {z z' : State S} {guard : S}
    (hGuard : N.ScheduleGuardedBy is guard)
    (hz : z guard = 0)
    (hExec : N.Exec z z' is) :
    is = [] := by
  cases is with
  | nil =>
      rfl
  | cons i is =>
      exact False.elim
        (not_exec_cons_of_scheduleGuardedBy_zero
          (N := N) (i := i) (is := is) hGuard hz hExec)

theorem eq_of_exec_scheduleGuardedBy_zero
    {N : Network S} {is : List N.I}
    {z z' : State S} {guard : S}
    (hGuard : N.ScheduleGuardedBy is guard)
    (hz : z guard = 0)
    (hExec : N.Exec z z' is) :
    z' = z := by
  have hNil :
      is = [] :=
    indices_eq_nil_of_exec_scheduleGuardedBy_zero hGuard hz hExec
  cases hNil
  exact (ExecOf.nil_iff.mp hExec).symm

structure Path (N : Network S) where
  state : Nat -> State S
  fired : Nat -> Option N.I
  valid :
    forall t,
      match fired t with
      | some i => N.StepAt i (state t) (state (t + 1))
      | none => state (t + 1) = state t /\ N.Terminal (state t)

/--
Alias emphasizing that `Path` is a forward deterministic trace interface.
It is not a stochastic sample path or CTMC trajectory.
-/
abbrev ForwardPath (N : Network S) :=
  N.Path

namespace Path

theorem stepAt_of_fired {N : Network S}
    {path : N.Path} {t : Nat} {i : N.I}
    (hfired : path.fired t = some i) :
    N.StepAt i (path.state t) (path.state (t + 1)) := by
  have hvalid := path.valid t
  simpa [hfired] using hvalid

theorem enabledAt_of_fired {N : Network S}
    {path : N.Path} {t : Nat} {i : N.I}
    (hfired : path.fired t = some i) :
    N.EnabledAt (path.state t) i :=
  (stepAt_of_fired (path := path) hfired).enabled

theorem state_succ_eq_of_fired_none {N : Network S}
    {path : N.Path} {t : Nat}
    (hfired : path.fired t = none) :
    path.state (t + 1) = path.state t := by
  have hvalid := path.valid t
  rw [hfired] at hvalid
  exact hvalid.1

theorem terminal_of_fired_none {N : Network S}
    {path : N.Path} {t : Nat}
    (hfired : path.fired t = none) :
    N.Terminal (path.state t) := by
  have hvalid := path.valid t
  rw [hfired] at hvalid
  exact hvalid.2

def FiresListAt {N : Network S} (path : N.Path) :
    Nat -> List N.I -> Prop
  | _t, [] => True
  | t, i :: is =>
      path.fired t = some i /\ FiresListAt path (t + 1) is

theorem not_firesListAt_cons_of_scheduleGuardedBy_zero
    {N : Network S} {path : N.Path}
    {guard : S} {i : N.I} {is : List N.I} {t : Nat}
    (hGuard : N.ScheduleGuardedBy (i :: is) guard)
    (hz : path.state t guard = 0) :
    Not (path.FiresListAt t (i :: is)) := by
  intro hFires
  exact not_enabledAt_of_guardedBy_zero
    (hGuard i List.mem_cons_self)
    hz
    (enabledAt_of_fired (path := path) hFires.1)

theorem not_firesListAt_cons_of_guardedByFamily_zero
    {N : Network S} {path : N.Path}
    {guard : N.I -> S} {i : N.I} {is : List N.I} {t : Nat}
    (hGuard : N.GuardedByFamily guard)
    (hz : path.state t (guard i) = 0) :
    Not (path.FiresListAt t (i :: is)) := by
  intro hFires
  exact not_enabledAt_of_guardedBy_zero
    (hGuard i)
    hz
    (enabledAt_of_fired (path := path) hFires.1)

theorem indices_eq_nil_of_firesListAt_scheduleGuardedBy_zero
    {N : Network S} {path : N.Path} {is : List N.I}
    {guard : S} {t : Nat}
    (hGuard : N.ScheduleGuardedBy is guard)
    (hz : path.state t guard = 0)
    (hFires : path.FiresListAt t is) :
    is = [] := by
  cases is with
  | nil =>
      rfl
  | cons i is =>
      exact False.elim
        (not_firesListAt_cons_of_scheduleGuardedBy_zero
          (N := N) (path := path) (i := i) (is := is)
          hGuard hz hFires)

theorem indices_eq_nil_of_firesListAt_guardedByFamily_zero
    {N : Network S} {path : N.Path} {is : List N.I}
    {guard : N.I -> S} {t : Nat}
    (hGuard : N.GuardedByFamily guard)
    (hzero :
      forall i, i ∈ is -> path.state t (guard i) = 0)
    (hFires : path.FiresListAt t is) :
    is = [] := by
  cases is with
  | nil =>
      rfl
  | cons i is =>
      exact False.elim
        (not_firesListAt_cons_of_guardedByFamily_zero
          (N := N) (path := path) (i := i) (is := is)
          hGuard (hzero i List.mem_cons_self) hFires)

def EventuallyFires {N : Network S}
    (path : N.Path) (i : N.I) (t0 : Nat) : Prop :=
  exists t, t0 <= t /\ path.fired t = some i

def EventuallyFiresList {N : Network S} (path : N.Path) :
    Nat -> List N.I -> Prop
  | _t, [] => True
  | t, i :: is =>
      exists tFire,
        t <= tFire /\
          path.fired tFire = some i /\
          EventuallyFiresList path (tFire + 1) is

def BadFiresBefore {N : Network S}
    (path : N.Path) (Bad : N.BadIndexSet)
    (t0 t1 : Nat) : Prop :=
  exists t, exists i : N.I,
    t0 <= t /\ t < t1 /\ path.fired t = some i /\ Bad i

def BadFiresAt {N : Network S}
    (path : N.Path) (Bad : N.BadIndexSet)
    (t : Nat) : Prop :=
  exists i : N.I, path.fired t = some i /\ Bad i

def NoBadFiresBefore {N : Network S}
    (path : N.Path) (Bad : N.BadIndexSet)
    (t0 t1 : Nat) : Prop :=
  Not (path.BadFiresBefore Bad t0 t1)

def FiresIntendedContiguouslyAt {N : Network S}
    (path : N.Path) (t : Nat)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) : Prop :=
  path.state t = z0 /\ path.FiresListAt t I.schedule

/--
The path fires exactly the intended schedule starting at time `t`.

This is a deterministic prefix assertion about `path.fired`, not a probability
or fairness statement.
-/
def FiresIntendedAt {N : Network S} (path : N.Path)
    {z0 z1 : State S} (I : N.IntendedSchedule z0 z1)
    (t : Nat) : Prop :=
  path.FiresListAt t I.schedule

def IntendedWinsRaceAt {N : Network S}
    (path : N.Path) (Bad : N.BadIndexSet) (t : Nat)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) : Prop :=
  path.FiresIntendedContiguouslyAt t I /\
    Not (path.BadFiresBefore Bad t (t + I.schedule.length))

theorem not_firesIntendedAt_of_scheduleGuardedBy_zero
    {N : Network S} {path : N.Path} {guard : S} {t : Nat}
    {z0 z1 : State S} {I : N.IntendedSchedule z0 z1}
    (hGuard : N.ScheduleGuardedBy I.schedule guard)
    (hz : path.state t guard = 0)
    (hNonempty : I.schedule ≠ []) :
    Not (path.FiresIntendedAt I t) := by
  intro hFires
  exact hNonempty
    (indices_eq_nil_of_firesListAt_scheduleGuardedBy_zero
      hGuard hz (by
        simpa [FiresIntendedAt] using hFires))

theorem not_firesIntendedAt_of_guardedByFamily_zero
    {N : Network S} {path : N.Path} {guard : N.I -> S} {t : Nat}
    {z0 z1 : State S} {I : N.IntendedSchedule z0 z1}
    (hGuard : N.GuardedByFamily guard)
    (hzero :
      forall i, i ∈ I.schedule -> path.state t (guard i) = 0)
    (hNonempty : I.schedule ≠ []) :
    Not (path.FiresIntendedAt I t) := by
  intro hFires
  exact hNonempty
    (indices_eq_nil_of_firesListAt_guardedByFamily_zero
      hGuard hzero (by
        simpa [FiresIntendedAt] using hFires))

theorem not_firesIntendedContiguouslyAt_of_scheduleGuardedBy_zero
    {N : Network S} {path : N.Path} {guard : S} {t : Nat}
    {z0 z1 : State S} {I : N.IntendedSchedule z0 z1}
    (hGuard : N.ScheduleGuardedBy I.schedule guard)
    (hz : path.state t guard = 0)
    (hNonempty : I.schedule ≠ []) :
    Not (path.FiresIntendedContiguouslyAt t I) := by
  intro hFires
  exact not_firesIntendedAt_of_scheduleGuardedBy_zero
    hGuard hz hNonempty hFires.2

theorem not_firesIntendedContiguouslyAt_of_guardedByFamily_zero
    {N : Network S} {path : N.Path} {guard : N.I -> S} {t : Nat}
    {z0 z1 : State S} {I : N.IntendedSchedule z0 z1}
    (hGuard : N.GuardedByFamily guard)
    (hzero :
      forall i, i ∈ I.schedule -> path.state t (guard i) = 0)
    (hNonempty : I.schedule ≠ []) :
    Not (path.FiresIntendedContiguouslyAt t I) := by
  intro hFires
  exact not_firesIntendedAt_of_guardedByFamily_zero
    hGuard hzero hNonempty hFires.2

theorem not_intendedWinsRaceAt_of_scheduleGuardedBy_zero
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {guard : S} {t : Nat}
    {z0 z1 : State S} {I : N.IntendedSchedule z0 z1}
    (hGuard : N.ScheduleGuardedBy I.schedule guard)
    (hz : path.state t guard = 0)
    (hNonempty : I.schedule ≠ []) :
    Not (path.IntendedWinsRaceAt Bad t I) := by
  intro hwin
  exact not_firesIntendedContiguouslyAt_of_scheduleGuardedBy_zero
    hGuard hz hNonempty hwin.1

theorem not_intendedWinsRaceAt_of_guardedByFamily_zero
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {guard : N.I -> S} {t : Nat}
    {z0 z1 : State S} {I : N.IntendedSchedule z0 z1}
    (hGuard : N.GuardedByFamily guard)
    (hzero :
      forall i, i ∈ I.schedule -> path.state t (guard i) = 0)
    (hNonempty : I.schedule ≠ []) :
    Not (path.IntendedWinsRaceAt Bad t I) := by
  intro hwin
  exact not_firesIntendedContiguouslyAt_of_guardedByFamily_zero
    hGuard hzero hNonempty hwin.1

theorem firesListAt_append {N : Network S}
    {path : N.Path} {t : Nat} {is js : List N.I}
    (hleft : path.FiresListAt t is)
    (hright : path.FiresListAt (t + is.length) js) :
    path.FiresListAt t (is ++ js) := by
  induction is generalizing t with
  | nil =>
      simpa using hright
  | cons i is ih =>
      rcases hleft with ⟨hfired, htail⟩
      constructor
      · exact hfired
      · apply ih htail
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright

theorem badFiresAt_of_fired_bad
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat} {i : N.I}
    (hfired : path.fired t = some i) (hBad : Bad i) :
    path.BadFiresAt Bad t :=
  ⟨i, hfired, hBad⟩

theorem badFiresBefore_of_badFiresAt
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t0 t1 t : Nat}
    (ht0 : t0 <= t) (ht1 : t < t1)
    (hbad : path.BadFiresAt Bad t) :
    path.BadFiresBefore Bad t0 t1 := by
  rcases hbad with ⟨i, hfired, hBad⟩
  exact ⟨t, i, ht0, ht1, hfired, hBad⟩

theorem badFiresBefore_mono
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t0 t1 a b : Nat}
    (ht0 : t0 <= a) (ht1 : b <= t1)
    (hbad : path.BadFiresBefore Bad a b) :
    path.BadFiresBefore Bad t0 t1 := by
  rcases hbad with ⟨t, i, ha, hb, hfired, hBad⟩
  exact ⟨t, i, le_trans ht0 ha, lt_of_lt_of_le hb ht1, hfired, hBad⟩

theorem not_badFiresAt_of_noBadFiresBefore
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t0 t1 t : Nat}
    (hNoBad : path.NoBadFiresBefore Bad t0 t1)
    (ht0 : t0 <= t) (ht1 : t < t1) :
    Not (path.BadFiresAt Bad t) := by
  intro hbad
  exact hNoBad (badFiresBefore_of_badFiresAt ht0 ht1 hbad)

theorem noBadFiresBefore_mono
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t0 t1 a b : Nat}
    (hNoBad : path.NoBadFiresBefore Bad t0 t1)
    (ht0 : t0 <= a) (ht1 : b <= t1) :
    path.NoBadFiresBefore Bad a b := by
  intro hbad
  exact hNoBad (badFiresBefore_mono ht0 ht1 hbad)

theorem noBadFiresBefore_of_forall_not_bad
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t0 t1 : Nat}
    (h :
      forall t i,
        t0 <= t -> t < t1 -> path.fired t = some i -> Not (Bad i)) :
    path.NoBadFiresBefore Bad t0 t1 := by
  rintro ⟨t, i, ht0, ht1, hfired, hBad⟩
  exact h t i ht0 ht1 hfired hBad

theorem noBadFiresBefore_of_intendedWinsRaceAt
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat} {z0 z1 : State S}
    {I : N.IntendedSchedule z0 z1}
    (hwin : path.IntendedWinsRaceAt Bad t I) :
    path.NoBadFiresBefore Bad t (t + I.schedule.length) :=
  hwin.2

theorem state_eq_of_intendedWinsRaceAt
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat} {z0 z1 : State S}
    {I : N.IntendedSchedule z0 z1}
    (hwin : path.IntendedWinsRaceAt Bad t I) :
    path.state t = z0 :=
  hwin.1.1

theorem firesListAt_of_intendedWinsRaceAt
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat} {z0 z1 : State S}
    {I : N.IntendedSchedule z0 z1}
    (hwin : path.IntendedWinsRaceAt Bad t I) :
    path.FiresListAt t I.schedule :=
  hwin.1.2

theorem exec_of_firesListAt {N : Network S}
    (path : N.Path) :
    forall {t : Nat} {is : List N.I},
      path.FiresListAt t is ->
        exists z',
          N.Exec (path.state t) z' is /\
            z' = path.state (t + is.length)
  | t, [], _hfires =>
      ⟨path.state t, ExecOf.nil (path.state t), by simp⟩
  | t, i :: is, hfires => by
      rcases hfires with ⟨hfired, htail⟩
      have hvalid := path.valid t
      rw [hfired] at hvalid
      rcases exec_of_firesListAt (path := path) htail with
        ⟨zEnd, hExecTail, hEnd⟩
      exact ⟨zEnd, ExecOf.cons hvalid hExecTail, by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hEnd⟩

theorem executableSchedule_of_firesListAt {N : Network S}
    {path : N.Path} {t : Nat} {is : List N.I}
    (hfires : path.FiresListAt t is) :
    N.ExecutableSchedule (path.state t) is := by
  rcases path.exec_of_firesListAt hfires with ⟨z', hExec, _hEnd⟩
  exact ⟨z', hExec⟩

/-- Forward wrapper for `exec_of_firesListAt`. -/
theorem forward_exec_of_firesListAt {N : Network S}
    (path : N.Path) :
    forall {t : Nat} {is : List N.I},
      path.FiresListAt t is ->
        exists z',
          N.Exec (path.state t) z' is /\
            z' = path.state (t + is.length) :=
  path.exec_of_firesListAt

theorem exec_of_firesIntendedAt {N : Network S}
    (path : N.Path)
    {t : Nat} {z0 z1 : State S}
    {I : N.IntendedSchedule z0 z1}
    (hfires : path.FiresIntendedAt I t) :
    exists z',
      N.Exec (path.state t) z' I.schedule /\
        z' = path.state (t + I.firingCount) := by
  simpa [FiresIntendedAt, IntendedSchedule.firingCount] using
    (path.exec_of_firesListAt (t := t) (is := I.schedule) hfires)

theorem exec_of_firesIntendedContiguouslyAt {N : Network S}
    (path : N.Path)
    {t : Nat} {z0 z1 : State S}
    {I : N.IntendedSchedule z0 z1}
    (hfire : path.FiresIntendedContiguouslyAt t I) :
    N.Exec z0 (path.state (t + I.firingCount)) I.schedule := by
  rcases path.exec_of_firesListAt hfire.2 with
    ⟨zAfter, hExec, hAfter⟩
  have hExec0 : N.Exec z0 zAfter I.schedule := by
    simpa [hfire.1] using hExec
  simpa [IntendedSchedule.firingCount, hAfter] using hExec0

theorem executableSchedule_of_firesIntendedAt {N : Network S}
    {path : N.Path} {t : Nat} {z0 z1 : State S}
    {I : N.IntendedSchedule z0 z1}
    (hfires : path.FiresIntendedAt I t) :
    N.ExecutableSchedule (path.state t) I.schedule := by
  rcases path.exec_of_firesIntendedAt hfires with
    ⟨z', hExec, _hEnd⟩
  exact ⟨z', hExec⟩

theorem executableSchedule_of_firesIntendedContiguouslyAt {N : Network S}
    {path : N.Path} {t : Nat} {z0 z1 : State S}
    {I : N.IntendedSchedule z0 z1}
    (hfire : path.FiresIntendedContiguouslyAt t I) :
    N.ExecutableSchedule z0 I.schedule :=
  ⟨path.state (t + I.firingCount),
    path.exec_of_firesIntendedContiguouslyAt hfire⟩

theorem executableSchedule_of_intendedWinsRaceAt {N : Network S}
    {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat} {z0 z1 : State S}
    {I : N.IntendedSchedule z0 z1}
    (hwin : path.IntendedWinsRaceAt Bad t I) :
    N.ExecutableSchedule (path.state t) I.schedule :=
  executableSchedule_of_firesListAt
    (firesListAt_of_intendedWinsRaceAt hwin)

theorem state_after_intended_of_firesListAt {N : Network S}
    (path : N.Path)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1)
    {t : Nat}
    (hstate : path.state t = z0)
    (hfires : path.FiresListAt t I.schedule) :
    path.state (t + I.schedule.length) = z1 := by
  rcases path.exec_of_firesListAt hfires with
    ⟨zAfter, hExec, hAfter⟩
  have hExec0 : N.Exec z0 zAfter I.schedule := by
    simpa [hstate] using hExec
  have hUnique : z1 = zAfter :=
    Network.exec_unique I.exec hExec0
  exact hAfter.symm.trans hUnique.symm

theorem state_after_intendedWinsRaceAt {N : Network S}
    (path : N.Path) (Bad : N.BadIndexSet)
    {t : Nat} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1)
    (hwin : path.IntendedWinsRaceAt Bad t I) :
    path.state (t + I.schedule.length) = z1 :=
  path.state_after_intended_of_firesListAt I hwin.1.1 hwin.1.2

theorem state_after_intended_of_firesIntendedContiguouslyAt
    {N : Network S} (path : N.Path)
    {t : Nat} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1)
    (hfire : path.FiresIntendedContiguouslyAt t I) :
    path.state (t + I.firingCount) = z1 := by
  simpa [IntendedSchedule.firingCount] using
    path.state_after_intended_of_firesListAt I hfire.1 hfire.2

/--
If a forward path fires the intended schedule from a state equal to `z0`, then
after exactly `I.firingCount` firings its state is `z1`.
-/
theorem forward_state_after_intended_of_firesIntendedAt
    {N : Network S} (path : N.Path)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1)
    {t : Nat}
    (hstate : path.state t = z0)
    (hfires : path.FiresIntendedAt I t) :
    path.state (t + I.firingCount) = z1 := by
  simpa [FiresIntendedAt, IntendedSchedule.firingCount] using
    path.state_after_intended_of_firesListAt I hstate hfires

theorem badFiresBefore_iff_exists_badFiresAt
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t0 t1 : Nat} :
    path.BadFiresBefore Bad t0 t1 <->
      exists t, t0 <= t /\ t < t1 /\ path.BadFiresAt Bad t := by
  constructor
  · rintro ⟨t, i, ht0, ht1, hfired, hBad⟩
    exact ⟨t, ht0, ht1, ⟨i, hfired, hBad⟩⟩
  · rintro ⟨t, ht0, ht1, i, hfired, hBad⟩
    exact ⟨t, i, ht0, ht1, hfired, hBad⟩

theorem badFiresAt_iff_of_fired
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat} {i : N.I}
    (hfired : path.fired t = some i) :
    path.BadFiresAt Bad t <-> Bad i := by
  constructor
  · rintro ⟨j, hj, hBad⟩
    rw [hfired] at hj
    cases hj
    exact hBad
  · intro hBad
    exact ⟨i, hfired, hBad⟩

theorem not_badFiresAt_of_fired_none
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat}
    (hfired : path.fired t = none) :
    Not (path.BadFiresAt Bad t) := by
  rintro ⟨i, hi, _hBad⟩
  rw [hfired] at hi
  cases hi

theorem badFiresBefore_of_fired_bad
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t0 t1 t : Nat} {i : N.I}
    (ht0 : t0 <= t) (ht1 : t < t1)
    (hfired : path.fired t = some i) (hBad : Bad i) :
    path.BadFiresBefore Bad t0 t1 :=
  badFiresBefore_of_badFiresAt ht0 ht1
    (badFiresAt_of_fired_bad hfired hBad)

theorem not_bad_of_fired_of_noBadFiresBefore
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t0 t1 t : Nat} {i : N.I}
    (hNoBad : path.NoBadFiresBefore Bad t0 t1)
    (ht0 : t0 <= t) (ht1 : t < t1)
    (hfired : path.fired t = some i) :
    Not (Bad i) := by
  intro hBad
  exact hNoBad
    (badFiresBefore_of_fired_bad ht0 ht1 hfired hBad)

theorem enabledAt_of_badFiresAt
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat}
    (hbad : path.BadFiresAt Bad t) :
    exists i : N.I, N.EnabledAt (path.state t) i /\ Bad i := by
  rcases hbad with ⟨i, hfired, hBad⟩
  exact ⟨i, enabledAt_of_fired (path := path) hfired, hBad⟩

theorem not_terminal_of_badFiresAt
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat}
    (hbad : path.BadFiresAt Bad t) :
    Not (N.Terminal (path.state t)) := by
  rcases enabledAt_of_badFiresAt hbad with ⟨i, hEnabled, _hBad⟩
  intro hTerminal
  exact hTerminal i hEnabled

theorem noBadFiresBefore_of_le
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t0 t1 : Nat}
    (h : t1 <= t0) :
    path.NoBadFiresBefore Bad t0 t1 := by
  rintro ⟨t, _i, ht0, ht1, _hfired, _hBad⟩
  exact (Nat.not_lt_of_ge (le_trans h ht0)) ht1

theorem noBadFiresBefore_self
    {N : Network S} (path : N.Path) (Bad : N.BadIndexSet)
    (t : Nat) :
    path.NoBadFiresBefore Bad t t :=
  noBadFiresBefore_of_le (path := path) (Bad := Bad) le_rfl

theorem noBadFiresBefore_mono_interval
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t0 t1 u0 u1 : Nat}
    (hNoBad : path.NoBadFiresBefore Bad t0 t1)
    (hleft : t0 <= u0) (hright : u1 <= t1) :
    path.NoBadFiresBefore Bad u0 u1 :=
  noBadFiresBefore_mono hNoBad hleft hright

theorem badFiresBefore_mono_interval
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t0 t1 u0 u1 : Nat}
    (hleft : u0 <= t0) (hright : t1 <= u1)
    (hbad : path.BadFiresBefore Bad t0 t1) :
    path.BadFiresBefore Bad u0 u1 :=
  badFiresBefore_mono hleft hright hbad

theorem badFiresBefore_mono_bad
    {N : Network S} {path : N.Path} {Bad Bad' : N.BadIndexSet}
    {t0 t1 : Nat}
    (hSub : forall i, Bad i -> Bad' i)
    (hbad : path.BadFiresBefore Bad t0 t1) :
    path.BadFiresBefore Bad' t0 t1 := by
  rcases hbad with ⟨t, i, ht0, ht1, hfired, hBad⟩
  exact ⟨t, i, ht0, ht1, hfired, hSub i hBad⟩

theorem noBadFiresBefore_mono_bad
    {N : Network S} {path : N.Path} {Bad Bad' : N.BadIndexSet}
    {t0 t1 : Nat}
    (hSub : forall i, Bad i -> Bad' i)
    (hNoBad' : path.NoBadFiresBefore Bad' t0 t1) :
    path.NoBadFiresBefore Bad t0 t1 := by
  intro hbad
  exact hNoBad' (badFiresBefore_mono_bad hSub hbad)

theorem noBadFiresBefore_iff_forall_not_badFiresAt
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t0 t1 : Nat} :
    path.NoBadFiresBefore Bad t0 t1 <->
      forall t, t0 <= t -> t < t1 -> Not (path.BadFiresAt Bad t) := by
  constructor
  · intro hNoBad t ht0 ht1
    exact not_badFiresAt_of_noBadFiresBefore hNoBad ht0 ht1
  · intro hNoBad hbad
    rcases hbad with ⟨t, i, ht0, ht1, hfired, hBad⟩
    exact hNoBad t ht0 ht1 ⟨i, hfired, hBad⟩

theorem noBadFiresBefore_singleton_iff
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat} :
    path.NoBadFiresBefore Bad t (t + 1) <->
      Not (path.BadFiresAt Bad t) := by
  constructor
  · intro hNoBad
    exact not_badFiresAt_of_noBadFiresBefore hNoBad
      le_rfl (Nat.lt_succ_self t)
  · intro hNoBad hbad
    rcases hbad with ⟨u, i, htu, hut, hfired, hBad⟩
    have hu_le : u <= t := Nat.lt_succ_iff.mp hut
    have hu_eq : u = t := le_antisymm hu_le htu
    subst u
    exact hNoBad ⟨i, hfired, hBad⟩

theorem badFiresBefore_singleton_iff
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat} :
    path.BadFiresBefore Bad t (t + 1) <->
      path.BadFiresAt Bad t := by
  constructor
  · intro hbad
    rcases hbad with ⟨u, i, htu, hut, hfired, hBad⟩
    have hu_le : u <= t := Nat.lt_succ_iff.mp hut
    have hu_eq : u = t := le_antisymm hu_le htu
    subst u
    exact ⟨i, hfired, hBad⟩
  · intro hbad
    exact badFiresBefore_of_badFiresAt
      le_rfl (Nat.lt_succ_self t) hbad

theorem badFiresBefore_split
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t0 t1 t2 : Nat}
    (hbad : path.BadFiresBefore Bad t0 t2) :
    path.BadFiresBefore Bad t0 t1 \/
      path.BadFiresBefore Bad t1 t2 := by
  rcases hbad with ⟨t, i, ht0, ht2, hfired, hBad⟩
  by_cases ht : t < t1
  · exact Or.inl ⟨t, i, ht0, ht, hfired, hBad⟩
  · exact Or.inr
      ⟨t, i, Nat.le_of_not_lt ht, ht2, hfired, hBad⟩

theorem noBadFiresBefore_append
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t0 t1 t2 : Nat}
    (h01 : path.NoBadFiresBefore Bad t0 t1)
    (h12 : path.NoBadFiresBefore Bad t1 t2) :
    path.NoBadFiresBefore Bad t0 t2 := by
  intro hbad
  cases badFiresBefore_split (t1 := t1) hbad with
  | inl hleft => exact h01 hleft
  | inr hright => exact h12 hright

theorem noBadFiresBefore_trans
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t0 t1 t2 : Nat}
    (h01 : path.NoBadFiresBefore Bad t0 t1)
    (h12 : path.NoBadFiresBefore Bad t1 t2) :
    path.NoBadFiresBefore Bad t0 t2 :=
  noBadFiresBefore_append h01 h12

theorem noBadFiresBefore_split_iff
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t0 t1 t2 : Nat}
    (h01 : t0 <= t1) (h12 : t1 <= t2) :
    path.NoBadFiresBefore Bad t0 t2 <->
      path.NoBadFiresBefore Bad t0 t1 /\
        path.NoBadFiresBefore Bad t1 t2 := by
  constructor
  · intro hNoBad
    exact ⟨
      noBadFiresBefore_mono_interval hNoBad le_rfl h12,
      noBadFiresBefore_mono_interval hNoBad h01 le_rfl⟩
  · rintro ⟨hLeft, hRight⟩
    exact noBadFiresBefore_append hLeft hRight

theorem firesListAt_append_iff
    {N : Network S} {path : N.Path} {t : Nat}
    {is js : List N.I} :
    path.FiresListAt t (is ++ js) <->
      path.FiresListAt t is /\
        path.FiresListAt (t + is.length) js := by
  induction is generalizing t with
  | nil =>
      simp [FiresListAt]
  | cons i is ih =>
      constructor
      · intro h
        rcases h with ⟨hi, htail⟩
        rcases (ih (t := t + 1)).mp htail with ⟨hleft, hright⟩
        exact ⟨⟨hi, hleft⟩, by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright⟩
      · rintro ⟨hleft, hright⟩
        exact firesListAt_append hleft hright

theorem firesListAt_append_left
    {N : Network S} {path : N.Path} {t : Nat}
    {is js : List N.I}
    (h : path.FiresListAt t (is ++ js)) :
    path.FiresListAt t is :=
  (firesListAt_append_iff
    (path := path) (t := t) (is := is) (js := js)).mp h |>.1

theorem firesListAt_append_right
    {N : Network S} {path : N.Path} {t : Nat}
    {is js : List N.I}
    (h : path.FiresListAt t (is ++ js)) :
    path.FiresListAt (t + is.length) js :=
  (firesListAt_append_iff
    (path := path) (t := t) (is := is) (js := js)).mp h |>.2

theorem noBadFiresBefore_of_firesListAt_forall_not_bad
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat} {is : List N.I}
    (hfires : path.FiresListAt t is)
    (hnotBad : forall i, i ∈ is -> Not (Bad i)) :
    path.NoBadFiresBefore Bad t (t + is.length) := by
  induction is generalizing t with
  | nil =>
      simpa using
        (noBadFiresBefore_self path Bad t)
  | cons i is ih =>
      rcases hfires with ⟨hfired, htail⟩
      have hNoHead :
          path.NoBadFiresBefore Bad t (t + 1) := by
        rw [noBadFiresBefore_singleton_iff]
        intro hbadAt
        rcases hbadAt with ⟨j, hj, hBad⟩
        rw [hfired] at hj
        cases hj
        exact hnotBad i List.mem_cons_self hBad
      have hNoTail :
          path.NoBadFiresBefore Bad (t + 1) ((t + 1) + is.length) := by
        exact ih htail (by
          intro j hj hBad
          exact hnotBad j (List.mem_cons_of_mem i hj) hBad)
      have hNoAll :
          path.NoBadFiresBefore Bad t ((t + 1) + is.length) :=
        noBadFiresBefore_append hNoHead hNoTail
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hNoAll

theorem noBadFiresBefore_of_bounded_firesListAt_forall_not_bad
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {bound t : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hfires : path.FiresListAt t I.schedule)
    (hnotBad : forall i, i ∈ I.schedule -> Not (Bad i)) :
    path.NoBadFiresBefore Bad t (t + I.firingCount) := by
  simpa [BoundedIntendedSchedule.firingCount] using
    noBadFiresBefore_of_firesListAt_forall_not_bad
      (path := path) (Bad := Bad) (t := t)
      (is := I.schedule) hfires hnotBad

theorem intendedWinsRaceAt_of_firesIntendedContiguouslyAt_forall_not_bad
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat} {z0 z1 : State S}
    {I : N.IntendedSchedule z0 z1}
    (hfire : path.FiresIntendedContiguouslyAt t I)
    (hnotBad : forall i, i ∈ I.schedule -> Not (Bad i)) :
    path.IntendedWinsRaceAt Bad t I := by
  refine ⟨hfire, ?_⟩
  exact noBadFiresBefore_of_firesListAt_forall_not_bad
    hfire.2 hnotBad

theorem not_badFiresAt_of_intendedWinsRaceAt
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t u : Nat} {z0 z1 : State S}
    {I : N.IntendedSchedule z0 z1}
    (hwin : path.IntendedWinsRaceAt Bad t I)
    (htu : t <= u) (huEnd : u < t + I.schedule.length) :
    Not (path.BadFiresAt Bad u) :=
  not_badFiresAt_of_noBadFiresBefore
    (noBadFiresBefore_of_intendedWinsRaceAt hwin)
    htu huEnd

theorem not_bad_head_of_intendedWinsRaceAt
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat} {z0 z1 : State S}
    {I : N.IntendedSchedule z0 z1}
    {i : N.I} {is : List N.I}
    (hschedule : I.schedule = i :: is)
    (hwin : path.IntendedWinsRaceAt Bad t I) :
    Not (Bad i) := by
  have hfires : path.FiresListAt t I.schedule :=
    firesListAt_of_intendedWinsRaceAt hwin
  have hfired : path.fired t = some i := by
    rw [hschedule] at hfires
    exact hfires.1
  have htEnd : t < t + I.schedule.length := by
    rw [hschedule]
    simp
  exact not_bad_of_fired_of_noBadFiresBefore
    (noBadFiresBefore_of_intendedWinsRaceAt hwin)
    le_rfl htEnd hfired

theorem forall_not_bad_of_firesListAt_noBadFiresBefore
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat} {is : List N.I}
    (hfires : path.FiresListAt t is)
    (hNoBad : path.NoBadFiresBefore Bad t (t + is.length)) :
    forall i, i ∈ is -> Not (Bad i) := by
  induction is generalizing t with
  | nil =>
      simp
  | cons i is ih =>
      rcases hfires with ⟨hfired, htail⟩
      intro j hj
      rcases List.mem_cons.mp hj with hji | hjtail
      · subst j
        have htEnd : t < t + (i :: is).length := by
          simp
        exact not_bad_of_fired_of_noBadFiresBefore
          hNoBad le_rfl htEnd hfired
      · have hNoTail :
            path.NoBadFiresBefore Bad (t + 1) ((t + 1) + is.length) := by
          exact noBadFiresBefore_mono_interval hNoBad
            (Nat.le_succ t)
            (by simp [Nat.add_comm, Nat.add_left_comm])
        exact ih htail hNoTail j hjtail

theorem forall_not_bad_of_intendedWinsRaceAt
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat} {z0 z1 : State S}
    {I : N.IntendedSchedule z0 z1}
    (hwin : path.IntendedWinsRaceAt Bad t I) :
    forall i, i ∈ I.schedule -> Not (Bad i) :=
  forall_not_bad_of_firesListAt_noBadFiresBefore
    (firesListAt_of_intendedWinsRaceAt hwin)
    (noBadFiresBefore_of_intendedWinsRaceAt hwin)

theorem state_eq_of_firesIntendedContiguouslyAt
    {N : Network S} {path : N.Path} {t : Nat}
    {z0 z1 : State S}
    {I : N.IntendedSchedule z0 z1}
    (h : path.FiresIntendedContiguouslyAt t I) :
    path.state t = z0 :=
  h.1

theorem firesListAt_of_firesIntendedContiguouslyAt
    {N : Network S} {path : N.Path} {t : Nat}
    {z0 z1 : State S}
    {I : N.IntendedSchedule z0 z1}
    (h : path.FiresIntendedContiguouslyAt t I) :
    path.FiresListAt t I.schedule :=
  h.2

theorem intendedWinsRaceAt_of_parts
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {t : Nat} {z0 z1 : State S}
    {I : N.IntendedSchedule z0 z1}
    (hstate : path.state t = z0)
    (hfires : path.FiresListAt t I.schedule)
    (hNoBad :
      path.NoBadFiresBefore Bad t (t + I.schedule.length)) :
    path.IntendedWinsRaceAt Bad t I :=
  ⟨⟨hstate, hfires⟩, hNoBad⟩

theorem intendedWinsRaceAt_of_bounded_noBadFiresBefore
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {bound t : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hfire : path.FiresIntendedContiguouslyAt t I.toIntendedSchedule)
    (hNoBad : path.NoBadFiresBefore Bad t (t + bound)) :
    path.IntendedWinsRaceAt Bad t I.toIntendedSchedule := by
  refine ⟨hfire, ?_⟩
  exact noBadFiresBefore_mono_interval hNoBad le_rfl (by
    simpa [BoundedIntendedSchedule.toIntendedSchedule] using
      Nat.add_le_add_left I.length_bound t)

theorem intendedWinsRaceAt_of_bounded_parts
    {N : Network S} {path : N.Path} {Bad : N.BadIndexSet}
    {bound t : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hstate : path.state t = z0)
    (hfires : path.FiresListAt t I.schedule)
    (hNoBad : path.NoBadFiresBefore Bad t (t + bound)) :
    path.IntendedWinsRaceAt Bad t I.toIntendedSchedule := by
  refine intendedWinsRaceAt_of_bounded_noBadFiresBefore I ?_ hNoBad
  exact ⟨hstate, by
    simpa [BoundedIntendedSchedule.toIntendedSchedule] using hfires⟩

theorem exec_of_boundedIntendedWinsRaceAt
    {N : Network S} (path : N.Path) (Bad : N.BadIndexSet)
    {bound t : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hwin : path.IntendedWinsRaceAt Bad t I.toIntendedSchedule) :
    N.Exec z0 (path.state (t + I.firingCount)) I.schedule := by
  simpa [BoundedIntendedSchedule.firingCount,
    BoundedIntendedSchedule.toIntendedSchedule] using
    path.exec_of_firesIntendedContiguouslyAt
      (I := I.toIntendedSchedule) hwin.1

theorem exec_of_boundedIntended_of_firesIntendedContiguouslyAt
    {N : Network S} (path : N.Path)
    {bound t : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hfire : path.FiresIntendedContiguouslyAt t I.toIntendedSchedule) :
    N.Exec z0 (path.state (t + I.firingCount)) I.schedule := by
  simpa [BoundedIntendedSchedule.firingCount,
    BoundedIntendedSchedule.toIntendedSchedule] using
    path.exec_of_firesIntendedContiguouslyAt
      (I := I.toIntendedSchedule) hfire

theorem exec_of_boundedIntended_of_firesListAt
    {N : Network S} (path : N.Path)
    {bound t : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hstate : path.state t = z0)
    (hfires : path.FiresListAt t I.schedule) :
    N.Exec z0 (path.state (t + I.firingCount)) I.schedule :=
  path.exec_of_boundedIntended_of_firesIntendedContiguouslyAt I
    ⟨hstate, by
      simpa [BoundedIntendedSchedule.toIntendedSchedule] using hfires⟩

theorem state_after_boundedIntended_of_firesListAt
    {N : Network S} (path : N.Path)
    {bound t : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hstate : path.state t = z0)
    (hfires : path.FiresListAt t I.schedule) :
    path.state (t + I.firingCount) = z1 := by
  simpa [BoundedIntendedSchedule.firingCount,
    BoundedIntendedSchedule.toIntendedSchedule] using
    path.state_after_intended_of_firesListAt
      I.toIntendedSchedule hstate
      (by
        simpa [BoundedIntendedSchedule.toIntendedSchedule] using
          hfires)

theorem state_after_boundedIntended_of_firesIntendedContiguouslyAt
    {N : Network S} (path : N.Path)
    {bound t : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hfire : path.FiresIntendedContiguouslyAt t I.toIntendedSchedule) :
    path.state (t + I.firingCount) = z1 := by
  simpa [BoundedIntendedSchedule.firingCount,
    BoundedIntendedSchedule.toIntendedSchedule] using
    path.state_after_intended_of_firesListAt
      I.toIntendedSchedule hfire.1 hfire.2

theorem state_after_boundedIntendedWinsRaceAt
    {N : Network S} (path : N.Path) (Bad : N.BadIndexSet)
    {bound t : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hwin : path.IntendedWinsRaceAt Bad t I.toIntendedSchedule) :
    path.state (t + I.firingCount) = z1 := by
  simpa [BoundedIntendedSchedule.firingCount,
    BoundedIntendedSchedule.toIntendedSchedule] using
    path.state_after_intendedWinsRaceAt Bad I.toIntendedSchedule hwin

theorem state_after_boundedIntended_of_bounded_parts
    {N : Network S} (path : N.Path) (Bad : N.BadIndexSet)
    {bound t : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (hstate : path.state t = z0)
    (hfires : path.FiresListAt t I.schedule)
    (hNoBad : path.NoBadFiresBefore Bad t (t + bound)) :
    path.state (t + I.firingCount) = z1 :=
  path.state_after_boundedIntendedWinsRaceAt Bad I
    (intendedWinsRaceAt_of_bounded_parts I hstate hfires hNoBad)

theorem eventuallyFires_of_fired
    {N : Network S} {path : N.Path} {t : Nat} {i : N.I}
    (hfired : path.fired t = some i) :
    path.EventuallyFires i t :=
  ⟨t, le_rfl, hfired⟩

theorem eventuallyFires_mono_start
    {N : Network S} {path : N.Path} {i : N.I}
    {t0 t1 : Nat}
    (ht : t0 <= t1)
    (h : path.EventuallyFires i t1) :
    path.EventuallyFires i t0 := by
  rcases h with ⟨u, htu, hfired⟩
  exact ⟨u, le_trans ht htu, hfired⟩

theorem eventuallyFiresList_mono_start
    {N : Network S} {path : N.Path} {is : List N.I}
    {t0 t1 : Nat}
    (ht : t0 <= t1)
    (h : path.EventuallyFiresList t1 is) :
    path.EventuallyFiresList t0 is := by
  cases is with
  | nil =>
      trivial
  | cons i is =>
      rcases h with ⟨u, htu, hfired, htail⟩
      exact ⟨u, le_trans ht htu, hfired, htail⟩

theorem eventuallyFiresList_of_firesListAt
    {N : Network S} {path : N.Path} {t : Nat}
    {is : List N.I}
    (hfires : path.FiresListAt t is) :
    path.EventuallyFiresList t is := by
  induction is generalizing t with
  | nil =>
      trivial
  | cons i is ih =>
      rcases hfires with ⟨hfired, htail⟩
      exact ⟨t, le_rfl, hfired, ih htail⟩

theorem eventuallyFires_of_eventuallyFiresList_cons
    {N : Network S} {path : N.Path} {t : Nat}
    {i : N.I} {is : List N.I}
    (h : path.EventuallyFiresList t (i :: is)) :
    path.EventuallyFires i t := by
  rcases h with ⟨u, htu, hfired, _htail⟩
  exact ⟨u, htu, hfired⟩

theorem eventuallyFiresList_tail_of_cons
    {N : Network S} {path : N.Path} {t : Nat}
    {i : N.I} {is : List N.I}
    (h : path.EventuallyFiresList t (i :: is)) :
    path.EventuallyFiresList t is := by
  rcases h with ⟨u, htu, _hfired, htail⟩
  exact eventuallyFiresList_mono_start
    (path := path) (is := is)
    (Nat.le_trans htu (Nat.le_succ u))
    htail

end Path

namespace Exec

theorem preserves_of_forall_mem
    {N : Network S} {P : State S -> Prop}
    {z z' : State S} {is : List N.I}
    (hExec : N.Exec z z' is)
    (hStep :
      forall i, i ∈ is -> forall {a b}, N.StepAt i a b -> P a -> P b) :
    P z -> P z' := by
  induction is generalizing z with
  | nil =>
      have hEq : z = z' := ExecOf.nil_iff.mp hExec
      intro hP
      simpa [hEq] using hP
  | cons i is ih =>
      rcases ExecOf.cons_iff.mp hExec with ⟨zMid, hFirst, hTail⟩
      intro hP
      have hMid : P zMid :=
        hStep i List.mem_cons_self hFirst hP
      exact ih hTail
        (fun j hj => hStep j (List.mem_cons_of_mem i hj))
        hMid

theorem eqOn_of_scheduleUntouches
    {N : Network S} {P : S -> Prop}
    {z z' : State S} {is : List N.I}
    (hExec : N.Exec z z' is)
    (hUntouches : N.ScheduleUntouches is P) :
    State.EqOn P z' z := by
  intro s hs
  exact coord_eq_of_forall_mem_not_touches hExec
    (fun i hi => hUntouches i hi s hs)

theorem zeroOn_of_scheduleUntouches
    {N : Network S} {P : S -> Prop}
    {z z' : State S} {is : List N.I}
    (hExec : N.Exec z z' is)
    (hUntouches : N.ScheduleUntouches is P)
    (hZero : State.ZeroOn P z) :
    State.ZeroOn P z' :=
  State.zeroOn_of_eqOn
    (eqOn_of_scheduleUntouches hExec hUntouches)
    hZero

theorem eqOn_of_scheduleTouchesOnly_disjoint
    {N : Network S} {Footprint Protected : S -> Prop}
    {z z' : State S} {is : List N.I}
    (hExec : N.Exec z z' is)
    (hTouch : N.ScheduleTouchesOnly is Footprint)
    (hDisjoint : forall s, Footprint s -> Protected s -> False) :
    State.EqOn Protected z' z := by
  exact eqOn_of_scheduleUntouches hExec
    (scheduleUntouches_of_scheduleTouchesOnly_disjoint hTouch hDisjoint)

end Exec

theorem scheduleClears_of_scheduleUntouches
    {N : Network S} {is : List N.I} {Garbage : S -> Prop}
    (hUntouches : N.ScheduleUntouches is Garbage) :
    N.ScheduleClears is Garbage := by
  intro _z _z' hExec hZero
  exact Exec.zeroOn_of_scheduleUntouches hExec hUntouches hZero

theorem scheduleClears_nil
    {N : Network S} {Garbage : S -> Prop} :
    N.ScheduleClears [] Garbage :=
  scheduleClears_of_scheduleUntouches scheduleUntouches_nil

theorem scheduleClears_append
    {N : Network S} {is js : List N.I} {Garbage : S -> Prop}
    (hLeft : N.ScheduleClears is Garbage)
    (hRight : N.ScheduleClears js Garbage) :
    N.ScheduleClears (is ++ js) Garbage := by
  intro _z _z' hExec hZero
  rcases ExecOf.split_append.mp hExec with ⟨zMid, hExecLeft, hExecRight⟩
  exact hRight hExecRight (hLeft hExecLeft hZero)

theorem scheduleClears_parallel_inl_iff
    {N M : Network S} {is : List N.I} {Garbage : S -> Prop} :
    (N.parallel M).ScheduleClears (is.map Sum.inl) Garbage <->
      N.ScheduleClears is Garbage := by
  constructor
  · intro hClear _z _z' hExec hZero
    exact hClear (Network.parallel_exec_inl N M hExec) hZero
  · intro hClear _z _z' hExec hZero
    exact hClear ((Network.parallel_exec_inl_iff N M).mp hExec) hZero

theorem scheduleClears_parallel_inl
    {N M : Network S} {is : List N.I} {Garbage : S -> Prop}
    (hClear : N.ScheduleClears is Garbage) :
    (N.parallel M).ScheduleClears (is.map Sum.inl) Garbage :=
  scheduleClears_parallel_inl_iff.mpr hClear

theorem scheduleClears_parallel_inr_iff
    {N M : Network S} {is : List M.I} {Garbage : S -> Prop} :
    (N.parallel M).ScheduleClears (is.map Sum.inr) Garbage <->
      M.ScheduleClears is Garbage := by
  constructor
  · intro hClear _z _z' hExec hZero
    exact hClear (Network.parallel_exec_inr N M hExec) hZero
  · intro hClear _z _z' hExec hZero
    exact hClear ((Network.parallel_exec_inr_iff N M).mp hExec) hZero

theorem scheduleClears_parallel_inr
    {N M : Network S} {is : List M.I} {Garbage : S -> Prop}
    (hClear : M.ScheduleClears is Garbage) :
    (N.parallel M).ScheduleClears (is.map Sum.inr) Garbage :=
  scheduleClears_parallel_inr_iff.mpr hClear

theorem scheduleClears_sigma_iff
    {A : Type v} [Fintype A] {Ns : A -> Network S} {a : A}
    {is : List (Ns a).I} {Garbage : S -> Prop} :
    (Network.sigma Ns).ScheduleClears
      (is.map (fun i => Sigma.mk a i)) Garbage <->
      (Ns a).ScheduleClears is Garbage := by
  constructor
  · intro hClear _z _z' hExec hZero
    exact hClear (Network.sigma_exec Ns a hExec) hZero
  · intro hClear _z _z' hExec hZero
    exact hClear ((Network.sigma_exec_iff Ns a).mp hExec) hZero

theorem scheduleClears_sigma
    {A : Type v} [Fintype A] {Ns : A -> Network S} {a : A}
    {is : List (Ns a).I} {Garbage : S -> Prop}
    (hClear : (Ns a).ScheduleClears is Garbage) :
    (Network.sigma Ns).ScheduleClears
      (is.map (fun i => Sigma.mk a i)) Garbage :=
  scheduleClears_sigma_iff.mpr hClear

theorem scheduleClears_of_scheduleTouchesOnly_disjoint
    {N : Network S} {is : List N.I}
    {Footprint Garbage : S -> Prop}
    (hTouch : N.ScheduleTouchesOnly is Footprint)
    (hDisjoint : forall s, Footprint s -> Garbage s -> False) :
    N.ScheduleClears is Garbage :=
  scheduleClears_of_scheduleUntouches
    (scheduleUntouches_of_scheduleTouchesOnly_disjoint hTouch hDisjoint)

theorem hoareExec_of_schedulePreserves
    {N : Network S} {is : List N.I} {P : State S -> Prop}
    (hPres : N.SchedulePreserves is P) :
    N.HoareExec is P (fun _ z' => P z') := by
  intro _z _z' hExec hP
  exact Exec.preserves_of_forall_mem hExec hPres hP

namespace HoareExec

theorem nil
    {N : Network S}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop}
    (hPost : forall z, Pre z -> Post z z) :
    N.HoareExec [] Pre Post := by
  intro z z' hExec hPre
  have hEq : z = z' := ExecOf.nil_iff.mp hExec
  subst hEq
  exact hPost z hPre

theorem singleton
    {N : Network S} {i : N.I}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop}
    (hPost :
      forall {z z'}, N.StepAt i z z' -> Pre z -> Post z z') :
    N.HoareExec [i] Pre Post := by
  intro z z' hExec hPre
  exact hPost (ExecOf.singleton_iff.mp hExec) hPre

theorem parallel_inl_iff
    {N M : Network S} {is : List N.I}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop} :
    (N.parallel M).HoareExec (is.map Sum.inl) Pre Post <->
      N.HoareExec is Pre Post := by
  constructor
  · intro hSpec z z' hExec hPre
    exact hSpec (Network.parallel_exec_inl N M hExec) hPre
  · intro hSpec z z' hExec hPre
    exact hSpec ((Network.parallel_exec_inl_iff N M).mp hExec) hPre

theorem parallel_inl
    {N M : Network S} {is : List N.I}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop}
    (hSpec : N.HoareExec is Pre Post) :
    (N.parallel M).HoareExec (is.map Sum.inl) Pre Post :=
  parallel_inl_iff.mpr hSpec

theorem parallel_inr_iff
    {N M : Network S} {is : List M.I}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop} :
    (N.parallel M).HoareExec (is.map Sum.inr) Pre Post <->
      M.HoareExec is Pre Post := by
  constructor
  · intro hSpec z z' hExec hPre
    exact hSpec (Network.parallel_exec_inr N M hExec) hPre
  · intro hSpec z z' hExec hPre
    exact hSpec ((Network.parallel_exec_inr_iff N M).mp hExec) hPre

theorem parallel_inr
    {N M : Network S} {is : List M.I}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop}
    (hSpec : M.HoareExec is Pre Post) :
    (N.parallel M).HoareExec (is.map Sum.inr) Pre Post :=
  parallel_inr_iff.mpr hSpec

theorem sigma_iff
    {A : Type v} [Fintype A] {Ns : A -> Network S} {a : A}
    {is : List (Ns a).I}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop} :
    (Network.sigma Ns).HoareExec
      (is.map (fun i => Sigma.mk a i)) Pre Post <->
      (Ns a).HoareExec is Pre Post := by
  constructor
  · intro hSpec z z' hExec hPre
    exact hSpec (Network.sigma_exec Ns a hExec) hPre
  · intro hSpec z z' hExec hPre
    exact hSpec ((Network.sigma_exec_iff Ns a).mp hExec) hPre

theorem sigma
    {A : Type v} [Fintype A] {Ns : A -> Network S} {a : A}
    {is : List (Ns a).I}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop}
    (hSpec : (Ns a).HoareExec is Pre Post) :
    (Network.sigma Ns).HoareExec
      (is.map (fun i => Sigma.mk a i)) Pre Post :=
  sigma_iff.mpr hSpec

theorem append
    {N : Network S} {is js : List N.I}
    {Pre : State S -> Prop}
    {Mid Post : State S -> State S -> Prop}
    (hLeft : N.HoareExec is Pre Mid)
    (hRight :
      forall {z0 zMid},
        Pre z0 -> Mid z0 zMid ->
          N.HoareExec js (fun z => z = zMid)
            (fun _ z' => Post z0 z')) :
    N.HoareExec (is ++ js) Pre Post := by
  intro z z' hExec hPre
  rcases ExecOf.split_append.mp hExec with ⟨zMid, hExecLeft, hExecRight⟩
  have hMid : Mid z zMid := hLeft hExecLeft hPre
  exact
    (hRight (z0 := z) (zMid := zMid) hPre hMid)
      hExecRight rfl

theorem cons
    {N : Network S} {i : N.I} {is : List N.I}
    {Pre : State S -> Prop}
    {Mid Post : State S -> State S -> Prop}
    (hHead : N.HoareExec [i] Pre Mid)
    (hTail :
      forall {z0 zMid},
        Pre z0 -> Mid z0 zMid ->
          N.HoareExec is (fun z => z = zMid)
            (fun _ z' => Post z0 z')) :
    N.HoareExec (i :: is) Pre Post := by
  intro z z' hExec hPre
  rcases ExecOf.cons_iff.mp hExec with ⟨zMid, hStep, hTailExec⟩
  have hMid : Mid z zMid :=
    hHead (ExecOf.singleton_iff.mpr hStep) hPre
  exact
    (hTail (z0 := z) (zMid := zMid) hPre hMid)
      hTailExec rfl

theorem append_final
    {N : Network S} {is js : List N.I}
    {Pre Mid Post : State S -> Prop}
    (hLeft : N.HoareExec is Pre (fun _ zMid => Mid zMid))
    (hRight : N.HoareExec js Mid (fun _ z' => Post z')) :
    N.HoareExec (is ++ js) Pre (fun _ z' => Post z') := by
  intro z z' hExec hPre
  rcases ExecOf.split_append.mp hExec with ⟨zMid, hExecLeft, hExecRight⟩
  have hMid : Mid zMid :=
    hLeft (z := z) (z' := zMid) hExecLeft hPre
  exact hRight (z := zMid) (z' := z') hExecRight hMid

theorem consequence
    {N : Network S} {is : List N.I}
    {Pre Pre' : State S -> Prop}
    {Post Post' : State S -> State S -> Prop}
    (hSpec : N.HoareExec is Pre Post)
    (hPre : forall z, Pre' z -> Pre z)
    (hPost : forall {z z'}, Pre' z -> Post z z' -> Post' z z') :
    N.HoareExec is Pre' Post' := by
  intro z z' hExec hPre'
  exact hPost hPre' (hSpec hExec (hPre z hPre'))

theorem frame_eqOn_of_scheduleUntouches
    {N : Network S} {is : List N.I}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop}
    {Frame : S -> Prop}
    (hSpec : N.HoareExec is Pre Post)
    (hUntouches : N.ScheduleUntouches is Frame) :
    N.HoareExec is Pre
      (fun z z' => Post z z' /\ State.EqOn Frame z' z) := by
  intro z z' hExec hPre
  exact ⟨hSpec hExec hPre,
    Network.Exec.eqOn_of_scheduleUntouches hExec hUntouches⟩

theorem frame_zeroOn_of_scheduleUntouches
    {N : Network S} {is : List N.I}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop}
    {Protected : S -> Prop}
    (hSpec : N.HoareExec is Pre Post)
    (hUntouches : N.ScheduleUntouches is Protected) :
    N.HoareExec is
      (fun z => Pre z /\ State.ZeroOn Protected z)
      (fun z z' => Post z z' /\ State.ZeroOn Protected z') := by
  intro z z' hExec hPre
  have hEq : State.EqOn Protected z' z :=
    Network.Exec.eqOn_of_scheduleUntouches hExec hUntouches
  exact ⟨hSpec hExec hPre.1,
    State.zeroOn_of_eqOn hEq hPre.2⟩

theorem with_clears
    {N : Network S} {is : List N.I}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop}
    {Garbage : S -> Prop}
    (hSpec : N.HoareExec is Pre Post)
    (hClear : N.ScheduleClears is Garbage) :
    N.HoareExec is
      (fun z => Pre z /\ State.ZeroOn Garbage z)
      (fun z z' => Post z z' /\ State.ZeroOn Garbage z') := by
  intro _z _z' hExec hPre
  exact ⟨hSpec hExec hPre.1, hClear hExec hPre.2⟩

theorem frame_eqOn_of_scheduleTouchesOnly_disjoint
    {N : Network S} {is : List N.I}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop}
    {Footprint Frame : S -> Prop}
    (hSpec : N.HoareExec is Pre Post)
    (hTouch : N.ScheduleTouchesOnly is Footprint)
    (hDisjoint :
      forall s, Footprint s -> Frame s -> False) :
    N.HoareExec is Pre
      (fun z z' => Post z z' /\ State.EqOn Frame z' z) :=
  frame_eqOn_of_scheduleUntouches hSpec
    (scheduleUntouches_of_scheduleTouchesOnly_disjoint
      hTouch hDisjoint)

theorem frame_zeroOn_of_scheduleTouchesOnly_disjoint
    {N : Network S} {is : List N.I}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop}
    {Footprint Protected : S -> Prop}
    (hSpec : N.HoareExec is Pre Post)
    (hTouch : N.ScheduleTouchesOnly is Footprint)
    (hDisjoint :
      forall s, Footprint s -> Protected s -> False) :
    N.HoareExec is
      (fun z => Pre z /\ State.ZeroOn Protected z)
      (fun z z' => Post z z' /\ State.ZeroOn Protected z') :=
  frame_zeroOn_of_scheduleUntouches hSpec
    (scheduleUntouches_of_scheduleTouchesOnly_disjoint
      hTouch hDisjoint)

theorem with_clears_of_scheduleTouchesOnly_disjoint
    {N : Network S} {is : List N.I}
    {Pre : State S -> Prop}
    {Post : State S -> State S -> Prop}
    {Footprint Garbage : S -> Prop}
    (hSpec : N.HoareExec is Pre Post)
    (hTouch : N.ScheduleTouchesOnly is Footprint)
    (hDisjoint :
      forall s, Footprint s -> Garbage s -> False) :
    N.HoareExec is
      (fun z => Pre z /\ State.ZeroOn Garbage z)
      (fun z z' => Post z z' /\ State.ZeroOn Garbage z') :=
  with_clears hSpec
    (scheduleClears_of_scheduleTouchesOnly_disjoint
      hTouch hDisjoint)

end HoareExec

namespace IntendedSchedule

theorem hoareExec_exact_frame_eqOn_of_scheduleUntouches
    {N : Network S} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1)
    {Frame : S -> Prop}
    (hUntouches : N.ScheduleUntouches I.schedule Frame) :
    N.HoareExec I.schedule
      (fun z => z = z0)
      (fun z z' => z' = z1 /\ State.EqOn Frame z' z) :=
  HoareExec.frame_eqOn_of_scheduleUntouches
    I.hoareExec_exact hUntouches

theorem hoareExec_exact_frame_zeroOn_of_scheduleUntouches
    {N : Network S} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1)
    {Protected : S -> Prop}
    (hUntouches : N.ScheduleUntouches I.schedule Protected) :
    N.HoareExec I.schedule
      (fun z => z = z0 /\ State.ZeroOn Protected z)
      (fun _ z' => z' = z1 /\ State.ZeroOn Protected z') :=
  HoareExec.frame_zeroOn_of_scheduleUntouches
    I.hoareExec_exact hUntouches

theorem hoareExec_exact_with_clears
    {N : Network S} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1)
    {Garbage : S -> Prop}
    (hClear : N.ScheduleClears I.schedule Garbage) :
    N.HoareExec I.schedule
      (fun z => z = z0 /\ State.ZeroOn Garbage z)
      (fun _ z' => z' = z1 /\ State.ZeroOn Garbage z') :=
  HoareExec.with_clears I.hoareExec_exact hClear

theorem hoareExec_exact_frame_eqOn_of_scheduleTouchesOnly_disjoint
    {N : Network S} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1)
    {Footprint Frame : S -> Prop}
    (hTouch : N.ScheduleTouchesOnly I.schedule Footprint)
    (hDisjoint :
      forall s, Footprint s -> Frame s -> False) :
    N.HoareExec I.schedule
      (fun z => z = z0)
      (fun z z' => z' = z1 /\ State.EqOn Frame z' z) :=
  HoareExec.frame_eqOn_of_scheduleTouchesOnly_disjoint
    I.hoareExec_exact hTouch hDisjoint

theorem hoareExec_exact_frame_zeroOn_of_scheduleTouchesOnly_disjoint
    {N : Network S} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1)
    {Footprint Protected : S -> Prop}
    (hTouch : N.ScheduleTouchesOnly I.schedule Footprint)
    (hDisjoint :
      forall s, Footprint s -> Protected s -> False) :
    N.HoareExec I.schedule
      (fun z => z = z0 /\ State.ZeroOn Protected z)
      (fun _ z' => z' = z1 /\ State.ZeroOn Protected z') :=
  HoareExec.frame_zeroOn_of_scheduleTouchesOnly_disjoint
    I.hoareExec_exact hTouch hDisjoint

theorem hoareExec_exact_with_clears_of_scheduleTouchesOnly_disjoint
    {N : Network S} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1)
    {Footprint Garbage : S -> Prop}
    (hTouch : N.ScheduleTouchesOnly I.schedule Footprint)
    (hDisjoint :
      forall s, Footprint s -> Garbage s -> False) :
    N.HoareExec I.schedule
      (fun z => z = z0 /\ State.ZeroOn Garbage z)
      (fun _ z' => z' = z1 /\ State.ZeroOn Garbage z') :=
  HoareExec.with_clears_of_scheduleTouchesOnly_disjoint
    I.hoareExec_exact hTouch hDisjoint

theorem preserves_of_schedulePreserves
    {N : Network S} {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1)
    {P : State S -> Prop}
    (hPres : N.SchedulePreserves I.schedule P)
    (hP : P z0) :
    P z1 :=
  Exec.preserves_of_forall_mem I.exec hPres hP

end IntendedSchedule

namespace BoundedIntendedSchedule

theorem hoareExec_exact_frame_eqOn_of_scheduleUntouches
    {N : Network S} {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    {Frame : S -> Prop}
    (hUntouches : N.ScheduleUntouches I.schedule Frame) :
    N.HoareExec I.schedule
      (fun z => z = z0)
      (fun z z' => z' = z1 /\ State.EqOn Frame z' z) :=
  HoareExec.frame_eqOn_of_scheduleUntouches
    I.hoareExec_exact hUntouches

theorem hoareExec_exact_frame_zeroOn_of_scheduleUntouches
    {N : Network S} {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    {Protected : S -> Prop}
    (hUntouches : N.ScheduleUntouches I.schedule Protected) :
    N.HoareExec I.schedule
      (fun z => z = z0 /\ State.ZeroOn Protected z)
      (fun _ z' => z' = z1 /\ State.ZeroOn Protected z') :=
  HoareExec.frame_zeroOn_of_scheduleUntouches
    I.hoareExec_exact hUntouches

theorem hoareExec_exact_with_clears
    {N : Network S} {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    {Garbage : S -> Prop}
    (hClear : N.ScheduleClears I.schedule Garbage) :
    N.HoareExec I.schedule
      (fun z => z = z0 /\ State.ZeroOn Garbage z)
      (fun _ z' => z' = z1 /\ State.ZeroOn Garbage z') :=
  HoareExec.with_clears I.hoareExec_exact hClear

theorem hoareExec_exact_frame_eqOn_of_scheduleTouchesOnly_disjoint
    {N : Network S} {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    {Footprint Frame : S -> Prop}
    (hTouch : N.ScheduleTouchesOnly I.schedule Footprint)
    (hDisjoint :
      forall s, Footprint s -> Frame s -> False) :
    N.HoareExec I.schedule
      (fun z => z = z0)
      (fun z z' => z' = z1 /\ State.EqOn Frame z' z) :=
  HoareExec.frame_eqOn_of_scheduleTouchesOnly_disjoint
    I.hoareExec_exact hTouch hDisjoint

theorem hoareExec_exact_frame_zeroOn_of_scheduleTouchesOnly_disjoint
    {N : Network S} {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    {Footprint Protected : S -> Prop}
    (hTouch : N.ScheduleTouchesOnly I.schedule Footprint)
    (hDisjoint :
      forall s, Footprint s -> Protected s -> False) :
    N.HoareExec I.schedule
      (fun z => z = z0 /\ State.ZeroOn Protected z)
      (fun _ z' => z' = z1 /\ State.ZeroOn Protected z') :=
  HoareExec.frame_zeroOn_of_scheduleTouchesOnly_disjoint
    I.hoareExec_exact hTouch hDisjoint

theorem hoareExec_exact_with_clears_of_scheduleTouchesOnly_disjoint
    {N : Network S} {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    {Footprint Garbage : S -> Prop}
    (hTouch : N.ScheduleTouchesOnly I.schedule Footprint)
    (hDisjoint :
      forall s, Footprint s -> Garbage s -> False) :
    N.HoareExec I.schedule
      (fun z => z = z0 /\ State.ZeroOn Garbage z)
      (fun _ z' => z' = z1 /\ State.ZeroOn Garbage z') :=
  HoareExec.with_clears_of_scheduleTouchesOnly_disjoint
    I.hoareExec_exact hTouch hDisjoint

theorem preserves_of_schedulePreserves
    {N : Network S} {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    {P : State S -> Prop}
    (hPres : N.SchedulePreserves I.schedule P)
    (hP : P z0) :
    P z1 :=
  Exec.preserves_of_forall_mem I.exec hPres hP

end BoundedIntendedSchedule

end Network

end Ripple.sCRNUniversality
