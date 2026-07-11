import Ripple.sCRNUniversality.Core.Schedule

namespace Ripple.sCRNUniversality

namespace State

variable {S : Type u}

def AgreesOutside (P : S -> Prop) (z z' : State S) : Prop :=
  forall s, Not (P s) -> z' s = z s

namespace AgreesOutside

theorem refl {P : S -> Prop} (z : State S) :
    AgreesOutside P z z := by
  intro s _hs
  rfl

theorem symm {P : S -> Prop} {z z' : State S}
    (h : AgreesOutside P z z') :
    AgreesOutside P z' z := by
  intro s hs
  exact (h s hs).symm

theorem trans {P : S -> Prop} {z0 z1 z2 : State S}
    (h01 : AgreesOutside P z0 z1)
    (h12 : AgreesOutside P z1 z2) :
    AgreesOutside P z0 z2 := by
  intro s hs
  exact (h12 s hs).trans (h01 s hs)

theorem trans_union {P R : S -> Prop} {z0 z1 z2 : State S}
    (h01 : AgreesOutside P z0 z1)
    (h12 : AgreesOutside R z1 z2) :
    AgreesOutside (fun s => P s \/ R s) z0 z2 := by
  intro s hs
  have hsP : Not (P s) := fun hP => hs (Or.inl hP)
  have hsR : Not (R s) := fun hR => hs (Or.inr hR)
  exact (h12 s hsR).trans (h01 s hsP)

theorem coord {P : S -> Prop} {z z' : State S}
    (h : AgreesOutside P z z') {s : S} (hs : Not (P s)) :
    z' s = z s :=
  h s hs

theorem mono {P R : S -> Prop} {z z' : State S}
    (h : AgreesOutside P z z')
    (hPR : forall s, P s -> R s) :
    AgreesOutside R z z' := by
  intro s hsR
  exact h s (fun hsP => hsR (hPR s hsP))

theorem add_right {P : S -> Prop} {z z' extra : State S}
    (h : AgreesOutside P z z') :
    AgreesOutside P (State.add z extra) (State.add z' extra) := by
  intro s hs
  simp [State.add, h s hs]

theorem add_left {P : S -> Prop} {z z' extra : State S}
    (h : AgreesOutside P z z') :
    AgreesOutside P (State.add extra z) (State.add extra z') := by
  intro s hs
  simp [State.add, h s hs]

end AgreesOutside

end State

namespace Reaction

variable {S : Type u}

abbrev FootprintWithin (rho : Reaction S) (P : S -> Prop) : Prop :=
  rho.TouchesOnly P

theorem not_touches_of_footprintWithin
    {rho : Reaction S} {P : S -> Prop} {s : S}
    (hFoot : rho.FootprintWithin P)
    (hs : Not (P s)) :
    Not (rho.Touches s) := by
  intro hTouches
  exact hs (hFoot s hTouches)

theorem footprintWithin_mono
    {rho : Reaction S} {P R : S -> Prop}
    (hFoot : rho.FootprintWithin P)
    (hPR : forall s, P s -> R s) :
    rho.FootprintWithin R := by
  intro s hTouches
  exact hPR s (hFoot s hTouches)

def TransfersAmount (rho : Reaction S) (source target : S)
    (amount : Nat) : Prop :=
  rho.l source = amount /\
    rho.r source = 0 /\
    rho.l target = 0 /\
    rho.r target = amount

/--
`TransfersAmountOnly source target amount` strengthens `TransfersAmount` by
requiring the reaction footprint to be contained in `{source, target}`.

Use this when a proof needs “only this transfer happens.” Plain
`TransfersAmount` is only a coordinate-level statement.
-/
def TransfersAmountOnly (rho : Reaction S) (source target : S)
    (amount : Nat) : Prop :=
  rho.TransfersAmount source target amount /\
    rho.FootprintWithin (fun s => s = source \/ s = target)

theorem transfersAmount_of_transfersAmountOnly
    {rho : Reaction S} {source target : S} {amount : Nat}
    (h : rho.TransfersAmountOnly source target amount) :
    rho.TransfersAmount source target amount :=
  h.1

theorem footprintWithin_pair_of_transfersAmountOnly
    {rho : Reaction S} {source target : S} {amount : Nat}
    (h : rho.TransfersAmountOnly source target amount) :
    rho.FootprintWithin (fun s => s = source \/ s = target) :=
  h.2

theorem enabled_amount_le_of_transfersAmount
    {rho : Reaction S} {source target : S} {amount : Nat}
    {z : State S}
    (hTransfer : rho.TransfersAmount source target amount)
    (hEnabled : rho.enabled z) :
    amount <= z source := by
  rcases hTransfer with ⟨hSourceIn, _hSourceOut, _hTargetIn, _hTargetOut⟩
  simpa [hSourceIn] using hEnabled source

theorem fire_source_of_transfersAmount
    {rho : Reaction S} {source target : S} {amount : Nat}
    (z : State S)
    (hTransfer : rho.TransfersAmount source target amount) :
    rho.fire z source = z source - amount := by
  rcases hTransfer with ⟨hSourceIn, hSourceOut, _hTargetIn, _hTargetOut⟩
  simp [Reaction.fire, hSourceIn, hSourceOut]

theorem fire_target_of_transfersAmount
    {rho : Reaction S} {source target : S} {amount : Nat}
    (z : State S)
    (hTransfer : rho.TransfersAmount source target amount) :
    rho.fire z target = z target + amount := by
  rcases hTransfer with ⟨_hSourceIn, _hSourceOut, hTargetIn, hTargetOut⟩
  simp [Reaction.fire, hTargetIn, hTargetOut]

theorem FiresTo.source_eq_of_transfersAmount
    {rho : Reaction S} {source target : S} {amount : Nat}
    {z z' : State S}
    (hFire : rho.FiresTo z z')
    (hTransfer : rho.TransfersAmount source target amount) :
    z' source = z source - amount := by
  rw [hFire.eq_fire]
  exact rho.fire_source_of_transfersAmount z hTransfer

theorem FiresTo.target_eq_of_transfersAmount
    {rho : Reaction S} {source target : S} {amount : Nat}
    {z z' : State S}
    (hFire : rho.FiresTo z z')
    (hTransfer : rho.TransfersAmount source target amount) :
    z' target = z target + amount := by
  rw [hFire.eq_fire]
  exact rho.fire_target_of_transfersAmount z hTransfer

theorem FiresTo.agreesOutside_of_footprintWithin
    {rho : Reaction S} {P : S -> Prop} {z z' : State S}
    (hFire : rho.FiresTo z z')
    (hFoot : rho.FootprintWithin P) :
    State.AgreesOutside P z z' := by
  intro s hs
  exact hFire.eq_on_not_touches
    (Reaction.not_touches_of_footprintWithin hFoot hs)

theorem FiresTo.coord_eq_of_transfersAmountOnly
    {rho : Reaction S} {source target : S} {amount : Nat}
    {z z' : State S}
    (hFire : rho.FiresTo z z')
    (hTransfer : rho.TransfersAmountOnly source target amount)
    {s : S}
    (hsource : s ≠ source)
    (htarget : s ≠ target) :
    z' s = z s := by
  exact hFire.eq_on_not_touches
    (Reaction.not_touches_of_footprintWithin hTransfer.2 (by
      intro hPair
      cases hPair with
      | inl hs => exact hsource hs
      | inr ht => exact htarget ht))

end Reaction

namespace Network

variable {S : Type u}

def FootprintWithin (N : Network S) (P : S -> Prop) : Prop :=
  forall i : N.I, (N.rxn i).FootprintWithin P

abbrev ScheduleFootprintWithin
    (N : Network S) (is : List N.I) (P : S -> Prop) : Prop :=
  N.ScheduleTouchesOnly is P

theorem scheduleFootprintWithin_of_footprintWithin
    {N : Network S} {P : S -> Prop} {is : List N.I}
    (hFoot : N.FootprintWithin P) :
    N.ScheduleFootprintWithin is P := by
  intro i _hi
  exact hFoot i

theorem footprintWithin_mono
    {N : Network S} {P R : S -> Prop}
    (hFoot : N.FootprintWithin P)
    (hPR : forall s, P s -> R s) :
    N.FootprintWithin R := by
  intro i
  exact Reaction.footprintWithin_mono (hFoot i) hPR

theorem scheduleFootprintWithin_mono
    {N : Network S} {is : List N.I} {P R : S -> Prop}
    (hFoot : N.ScheduleFootprintWithin is P)
    (hPR : forall s, P s -> R s) :
    N.ScheduleFootprintWithin is R := by
  intro i hi
  exact Reaction.footprintWithin_mono (hFoot i hi) hPR

theorem scheduleFootprintWithin_singleton
    {N : Network S} {P : S -> Prop} {i : N.I}
    (hFoot : (N.rxn i).FootprintWithin P) :
    N.ScheduleFootprintWithin [i] P := by
  intro j hj
  have hji : j = i := by
    simpa using hj
  cases hji
  exact hFoot

theorem oneRxnNetwork_footprintWithin
    {rho : Reaction S} {P : S -> Prop}
    (hFoot : rho.FootprintWithin P) :
    (oneRxnNetwork rho).FootprintWithin P := by
  intro i
  cases i
  simpa [oneRxnNetwork] using hFoot

theorem oneRxnNetwork_scheduleFootprintWithin
    {rho : Reaction S} {P : S -> Prop}
    (hFoot : rho.FootprintWithin P) :
    (oneRxnNetwork rho).ScheduleFootprintWithin
      [OneRxnIdx.step] P :=
  scheduleFootprintWithin_singleton (by
    simpa using hFoot)

theorem scheduleFootprintWithin_append
    {N : Network S} {is js : List N.I} {P : S -> Prop}
    (hLeft : N.ScheduleFootprintWithin is P)
    (hRight : N.ScheduleFootprintWithin js P) :
    N.ScheduleFootprintWithin (is ++ js) P := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hLeft i hi
  · exact hRight i hi

theorem scheduleFootprintWithin_append_union
    {N : Network S} {is js : List N.I} {P R : S -> Prop}
    (hLeft : N.ScheduleFootprintWithin is P)
    (hRight : N.ScheduleFootprintWithin js R) :
    N.ScheduleFootprintWithin (is ++ js) (fun s => P s \/ R s) :=
  scheduleFootprintWithin_append
    (scheduleFootprintWithin_mono hLeft (fun _ hs => Or.inl hs))
    (scheduleFootprintWithin_mono hRight (fun _ hs => Or.inr hs))

theorem parallel_scheduleFootprintWithin_inl
    {N M : Network S} {is : List N.I} {P : S -> Prop}
    (hFoot : N.ScheduleFootprintWithin is P) :
    (N.parallel M).ScheduleFootprintWithin (is.map Sum.inl) P :=
  parallel_scheduleTouchesOnly_inl hFoot

theorem parallel_scheduleFootprintWithin_inr
    {N M : Network S} {is : List M.I} {P : S -> Prop}
    (hFoot : M.ScheduleFootprintWithin is P) :
    (N.parallel M).ScheduleFootprintWithin (is.map Sum.inr) P :=
  parallel_scheduleTouchesOnly_inr hFoot

theorem sigma_scheduleFootprintWithin
    {A : Type v} [Fintype A] (Ns : A -> Network S) (a : A)
    {is : List (Ns a).I} {P : S -> Prop}
    (hFoot : (Ns a).ScheduleFootprintWithin is P) :
    (Network.sigma Ns).ScheduleFootprintWithin
      (is.map (fun i => Sigma.mk a i)) P :=
  Network.sigma_scheduleTouchesOnly Ns a hFoot

theorem sigma_scheduleFootprintWithin_iff
    {A : Type v} [Fintype A] {Ns : A -> Network S} {a : A}
    {is : List (Ns a).I} {P : S -> Prop} :
    (Network.sigma Ns).ScheduleFootprintWithin
      (is.map (fun i => Sigma.mk a i)) P <->
      (Ns a).ScheduleFootprintWithin is P :=
  Network.sigma_scheduleTouchesOnly_iff

theorem parallel_scheduleFootprintWithin_inl_iff
    {N M : Network S} {is : List N.I} {P : S -> Prop} :
    (N.parallel M).ScheduleFootprintWithin (is.map Sum.inl) P <->
      N.ScheduleFootprintWithin is P :=
  parallel_scheduleTouchesOnly_inl_iff

theorem parallel_scheduleFootprintWithin_inr_iff
    {N M : Network S} {is : List M.I} {P : S -> Prop} :
    (N.parallel M).ScheduleFootprintWithin (is.map Sum.inr) P <->
      M.ScheduleFootprintWithin is P :=
  parallel_scheduleTouchesOnly_inr_iff

def ExecFootprintWithin
    (N : Network S) (P : S -> Prop)
    (z z' : State S) : Prop :=
  exists is : List N.I, N.Exec z z' is /\ N.ScheduleFootprintWithin is P

theorem parallel_footprintWithin
    {N M : Network S} {P : S -> Prop}
    (hN : N.FootprintWithin P)
    (hM : M.FootprintWithin P) :
    (N.parallel M).FootprintWithin P := by
  intro i
  cases i with
  | inl i => exact hN i
  | inr i => exact hM i

theorem parallel_footprintWithin_iff
    (N M : Network S) (P : S -> Prop) :
    (N.parallel M).FootprintWithin P <->
      N.FootprintWithin P /\ M.FootprintWithin P := by
  constructor
  · intro h
    exact ⟨fun i => h (Sum.inl i), fun i => h (Sum.inr i)⟩
  · rintro ⟨hN, hM⟩
    exact parallel_footprintWithin hN hM

theorem sigma_footprintWithin
    {A : Type v} [Fintype A] {Ns : A -> Network S} {P : S -> Prop}
    (hFoot : forall a, (Ns a).FootprintWithin P) :
    (Network.sigma Ns).FootprintWithin P := by
  intro idx
  rcases idx with ⟨a, i⟩
  exact hFoot a i

theorem sigma_footprintWithin_iff
    {A : Type v} [Fintype A] (Ns : A -> Network S) (P : S -> Prop) :
    (Network.sigma Ns).FootprintWithin P <->
      forall a, (Ns a).FootprintWithin P := by
  constructor
  · intro h a i
    exact h ⟨a, i⟩
  · exact sigma_footprintWithin

namespace StepAt

theorem source_eq_of_transfersAmount
    {N : Network S} {i : N.I} {source target : S} {amount : Nat}
    {z z' : State S}
    (hStep : N.StepAt i z z')
    (hTransfer : (N.rxn i).TransfersAmount source target amount) :
    z' source = z source - amount :=
  Reaction.FiresTo.source_eq_of_transfersAmount hStep hTransfer

theorem target_eq_of_transfersAmount
    {N : Network S} {i : N.I} {source target : S} {amount : Nat}
    {z z' : State S}
    (hStep : N.StepAt i z z')
    (hTransfer : (N.rxn i).TransfersAmount source target amount) :
    z' target = z target + amount :=
  Reaction.FiresTo.target_eq_of_transfersAmount hStep hTransfer

theorem agreesOutside_of_footprintWithin
    {N : Network S} {i : N.I} {P : S -> Prop}
    {z z' : State S}
    (hStep : N.StepAt i z z')
    (hFoot : (N.rxn i).FootprintWithin P) :
    State.AgreesOutside P z z' :=
  Reaction.FiresTo.agreesOutside_of_footprintWithin hStep hFoot

end StepAt

namespace Exec

theorem agreesOutside_of_scheduleFootprintWithin
    {N : Network S} {P : S -> Prop}
    {z z' : State S} {is : List N.I}
    (hExec : N.Exec z z' is)
    (hFoot : N.ScheduleFootprintWithin is P) :
    State.AgreesOutside P z z' := by
  intro s hs
  exact coord_eq_of_forall_mem_not_touches hExec
    (fun i hi => Reaction.not_touches_of_footprintWithin (hFoot i hi) hs)

theorem agreesOutside_of_footprintWithin
    {N : Network S} {P : S -> Prop}
    {z z' : State S} {is : List N.I}
    (hExec : N.Exec z z' is)
    (hFoot : N.FootprintWithin P) :
    State.AgreesOutside P z z' :=
  agreesOutside_of_scheduleFootprintWithin hExec
    (scheduleFootprintWithin_of_footprintWithin hFoot)

theorem coord_eq_of_scheduleFootprintWithin
    {N : Network S} {P : S -> Prop}
    {z z' : State S} {is : List N.I} {s : S}
    (hExec : N.Exec z z' is)
    (hFoot : N.ScheduleFootprintWithin is P)
    (hs : Not (P s)) :
    z' s = z s :=
  (agreesOutside_of_scheduleFootprintWithin hExec hFoot).coord hs

theorem coord_eq_of_footprintWithin
    {N : Network S} {P : S -> Prop}
    {z z' : State S} {is : List N.I} {s : S}
    (hExec : N.Exec z z' is)
    (hFoot : N.FootprintWithin P)
    (hs : Not (P s)) :
    z' s = z s :=
  (agreesOutside_of_footprintWithin hExec hFoot).coord hs

theorem eqOn_of_scheduleFootprintWithin_disjoint
    {N : Network S} {Footprint Protected : S -> Prop}
    {z z' : State S} {is : List N.I}
    (hExec : N.Exec z z' is)
    (hFoot : N.ScheduleFootprintWithin is Footprint)
    (hDisjoint :
      forall s, Footprint s -> Protected s -> False) :
    State.EqOn Protected z' z :=
  Network.Exec.eqOn_of_scheduleTouchesOnly_disjoint
    hExec hFoot hDisjoint

theorem eqOn_of_footprintWithin_disjoint
    {N : Network S} {Footprint Protected : S -> Prop}
    {z z' : State S} {is : List N.I}
    (hExec : N.Exec z z' is)
    (hFoot : N.FootprintWithin Footprint)
    (hDisjoint :
      forall s, Footprint s -> Protected s -> False) :
    State.EqOn Protected z' z :=
  eqOn_of_scheduleFootprintWithin_disjoint hExec
    (scheduleFootprintWithin_of_footprintWithin hFoot)
    hDisjoint

end Exec

namespace ExecFootprintWithin

theorem of_exec_scheduleFootprintWithin
    {N : Network S} {P : S -> Prop} {z z' : State S}
    {is : List N.I}
    (hExec : N.Exec z z' is)
    (hFoot : N.ScheduleFootprintWithin is P) :
    N.ExecFootprintWithin P z z' :=
  ⟨is, hExec, hFoot⟩

theorem of_intendedSchedule
    {N : Network S} {P : S -> Prop} {z z' : State S}
    (I : N.IntendedSchedule z z')
    (hFoot : N.ScheduleFootprintWithin I.schedule P) :
    N.ExecFootprintWithin P z z' :=
  of_exec_scheduleFootprintWithin I.exec hFoot

theorem of_intendedSchedule_footprintWithin
    {N : Network S} {P : S -> Prop} {z z' : State S}
    (I : N.IntendedSchedule z z')
    (hFoot : N.FootprintWithin P) :
    N.ExecFootprintWithin P z z' :=
  of_intendedSchedule I
    (scheduleFootprintWithin_of_footprintWithin hFoot)

theorem of_boundedIntendedSchedule
    {N : Network S} {P : S -> Prop} {bound : Nat}
    {z z' : State S}
    (I : N.BoundedIntendedSchedule bound z z')
    (hFoot : N.ScheduleFootprintWithin I.schedule P) :
    N.ExecFootprintWithin P z z' :=
  of_exec_scheduleFootprintWithin I.exec hFoot

theorem of_boundedIntendedSchedule_footprintWithin
    {N : Network S} {P : S -> Prop} {bound : Nat}
    {z z' : State S}
    (I : N.BoundedIntendedSchedule bound z z')
    (hFoot : N.FootprintWithin P) :
    N.ExecFootprintWithin P z z' :=
  of_boundedIntendedSchedule I
    (scheduleFootprintWithin_of_footprintWithin hFoot)

theorem of_exec_footprintWithin
    {N : Network S} {P : S -> Prop} {z z' : State S}
    {is : List N.I}
    (hExec : N.Exec z z' is)
    (hFoot : N.FootprintWithin P) :
    N.ExecFootprintWithin P z z' :=
  of_exec_scheduleFootprintWithin hExec
    (scheduleFootprintWithin_of_footprintWithin hFoot)

theorem of_reaches_footprintWithin
    {N : Network S} {P : S -> Prop} {z z' : State S}
    (hReach : N.Reaches z z')
    (hFoot : N.FootprintWithin P) :
    N.ExecFootprintWithin P z z' := by
  rcases hReach with ⟨is, hExec⟩
  exact of_exec_footprintWithin hExec hFoot

theorem refl
    (N : Network S) (P : S -> Prop) (z : State S) :
    N.ExecFootprintWithin P z z :=
  ⟨[], ExecOf.nil z, by
    intro i hi
    simp at hi⟩

theorem mono
    {N : Network S} {P R : S -> Prop} {z z' : State S}
    (h : N.ExecFootprintWithin P z z')
    (hPR : forall s, P s -> R s) :
    N.ExecFootprintWithin R z z' := by
  rcases h with ⟨is, hExec, hFoot⟩
  exact of_exec_scheduleFootprintWithin hExec
    (scheduleFootprintWithin_mono hFoot hPR)

theorem add_right
    {N : Network S} {P : S -> Prop} {z z' extra : State S}
    (h : N.ExecFootprintWithin P z z') :
    N.ExecFootprintWithin P
      (State.add z extra) (State.add z' extra) := by
  rcases h with ⟨is, hExec, hFoot⟩
  exact of_exec_scheduleFootprintWithin
    (Network.Exec.add_right hExec) hFoot

theorem add_left
    {N : Network S} {P : S -> Prop} {z z' extra : State S}
    (h : N.ExecFootprintWithin P z z') :
    N.ExecFootprintWithin P
      (State.add extra z) (State.add extra z') := by
  rcases h with ⟨is, hExec, hFoot⟩
  exact of_exec_scheduleFootprintWithin
    (Network.Exec.add_left hExec) hFoot

theorem sigma
    {A : Type v} [Fintype A] {Ns : A -> Network S} {a : A}
    {P : S -> Prop} {z z' : State S}
    (h : (Ns a).ExecFootprintWithin P z z') :
    (Network.sigma Ns).ExecFootprintWithin P z z' := by
  rcases h with ⟨is, hExec, hFoot⟩
  exact of_exec_scheduleFootprintWithin
    (Network.sigma_exec Ns a hExec)
    (Network.sigma_scheduleFootprintWithin Ns a hFoot)

theorem trans
    {N : Network S} {P : S -> Prop} {z0 z1 z2 : State S}
    (h01 : N.ExecFootprintWithin P z0 z1)
    (h12 : N.ExecFootprintWithin P z1 z2) :
    N.ExecFootprintWithin P z0 z2 := by
  rcases h01 with ⟨is, hExec01, hFoot01⟩
  rcases h12 with ⟨js, hExec12, hFoot12⟩
  refine of_exec_scheduleFootprintWithin
    (ExecOf.append hExec01 hExec12) ?_
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hFoot01 i hi
  · exact hFoot12 i hi

theorem trans_union
    {N : Network S} {P R : S -> Prop} {z0 z1 z2 : State S}
    (h01 : N.ExecFootprintWithin P z0 z1)
    (h12 : N.ExecFootprintWithin R z1 z2) :
    N.ExecFootprintWithin (fun s => P s \/ R s) z0 z2 := by
  rcases h01 with ⟨is, hExec01, hFoot01⟩
  rcases h12 with ⟨js, hExec12, hFoot12⟩
  exact of_exec_scheduleFootprintWithin
    (ExecOf.append hExec01 hExec12)
    (scheduleFootprintWithin_append_union hFoot01 hFoot12)

theorem reaches
    {N : Network S} {P : S -> Prop} {z z' : State S}
    (h : N.ExecFootprintWithin P z z') :
    N.Reaches z z' := by
  rcases h with ⟨is, hExec, _hFoot⟩
  exact ⟨is, hExec⟩

theorem coverableFrom_of_covers
    {N : Network S} {P : S -> Prop} {z z' target : State S}
    (h : N.ExecFootprintWithin P z z')
    (hCovers : Covers z' target) :
    N.CoverableFrom z target :=
  Network.coverable_of_reaches_of_covers h.reaches hCovers

theorem coverableFrom_of_le
    {N : Network S} {P : S -> Prop} {z z' target : State S}
    (h : N.ExecFootprintWithin P z z')
    (hTarget : forall s, target s <= z' s) :
    N.CoverableFrom z target :=
  h.coverableFrom_of_covers hTarget

theorem speciesCoverableFrom_of_coord [DecidableEq S]
    {N : Network S} {P : S -> Prop} {z z' : State S}
    (h : N.ExecFootprintWithin P z z')
    {species : S} {amount : Nat}
    (hamount : amount <= z' species) :
    N.SpeciesCoverableFrom z species amount :=
  Network.speciesCoverableFrom_of_reaches_coord h.reaches hamount

theorem speciesCoverableFrom_one_of_pos [DecidableEq S]
    {N : Network S} {P : S -> Prop} {z z' : State S}
    (h : N.ExecFootprintWithin P z z')
    {species : S}
    (hpos : 0 < z' species) :
    N.SpeciesCoverableFrom z species :=
  Network.speciesCoverableFrom_one_of_reaches_pos h.reaches hpos

theorem agreesOutside
    {N : Network S} {P : S -> Prop} {z z' : State S}
    (h : N.ExecFootprintWithin P z z') :
    State.AgreesOutside P z z' := by
  rcases h with ⟨is, hExec, hFoot⟩
  exact Exec.agreesOutside_of_scheduleFootprintWithin hExec hFoot

theorem eqOn_of_disjoint
    {N : Network S} {Footprint Protected : S -> Prop}
    {z z' : State S}
    (h : N.ExecFootprintWithin Footprint z z')
    (hDisjoint :
      forall s, Footprint s -> Protected s -> False) :
    State.EqOn Protected z' z := by
  rcases h with ⟨is, hExec, hFoot⟩
  exact Network.Exec.eqOn_of_scheduleTouchesOnly_disjoint
    hExec hFoot hDisjoint

theorem coord_eq
    {N : Network S} {P : S -> Prop} {z z' : State S} {s : S}
    (h : N.ExecFootprintWithin P z z')
    (hs : Not (P s)) :
    z' s = z s :=
  h.agreesOutside.coord hs

end ExecFootprintWithin

theorem execFootprintWithin_of_exec_scheduleFootprintWithin
    {N : Network S} {P : S -> Prop} {z z' : State S}
    {is : List N.I}
    (hExec : N.Exec z z' is)
    (hFoot : N.ScheduleFootprintWithin is P) :
    N.ExecFootprintWithin P z z' :=
  Network.ExecFootprintWithin.of_exec_scheduleFootprintWithin hExec hFoot

theorem oneRxnNetwork_execFootprintWithin
    {rho : Reaction S} {P : S -> Prop} {z z' : State S}
    (hFire : rho.FiresTo z z')
    (hFoot : rho.FootprintWithin P) :
    (oneRxnNetwork rho).ExecFootprintWithin P z z' :=
  Network.ExecFootprintWithin.of_exec_scheduleFootprintWithin
    (oneRxn_exec hFire)
    (oneRxnNetwork_scheduleFootprintWithin hFoot)

theorem execFootprintWithin_of_exec_footprintWithin
    {N : Network S} {P : S -> Prop} {z z' : State S}
    {is : List N.I}
    (hExec : N.Exec z z' is)
    (hFoot : N.FootprintWithin P) :
    N.ExecFootprintWithin P z z' :=
  Network.ExecFootprintWithin.of_exec_footprintWithin hExec hFoot

theorem execFootprintWithin_mono
    {N : Network S} {P R : S -> Prop} {z z' : State S}
    (h : N.ExecFootprintWithin P z z')
    (hPR : forall s, P s -> R s) :
    N.ExecFootprintWithin R z z' :=
  Network.ExecFootprintWithin.mono h hPR

theorem execFootprintWithin_add_right
    {N : Network S} {P : S -> Prop} {z z' extra : State S}
    (h : N.ExecFootprintWithin P z z') :
    N.ExecFootprintWithin P
      (State.add z extra) (State.add z' extra) :=
  Network.ExecFootprintWithin.add_right h

theorem execFootprintWithin_add_left
    {N : Network S} {P : S -> Prop} {z z' extra : State S}
    (h : N.ExecFootprintWithin P z z') :
    N.ExecFootprintWithin P
      (State.add extra z) (State.add extra z') :=
  Network.ExecFootprintWithin.add_left h

theorem execFootprintWithin_sigma
    {A : Type v} [Fintype A] {Ns : A -> Network S} {a : A}
    {P : S -> Prop} {z z' : State S}
    (h : (Ns a).ExecFootprintWithin P z z') :
    (Network.sigma Ns).ExecFootprintWithin P z z' :=
  Network.ExecFootprintWithin.sigma h

namespace Reaches

theorem agreesOutside_of_footprintWithin
    {N : Network S} {P : S -> Prop}
    {z z' : State S}
    (hReach : N.Reaches z z')
    (hFoot : N.FootprintWithin P) :
    State.AgreesOutside P z z' := by
  rcases hReach with ⟨is, hExec⟩
  exact Exec.agreesOutside_of_footprintWithin hExec hFoot

theorem coord_eq_of_footprintWithin
    {N : Network S} {P : S -> Prop}
    {z z' : State S} {s : S}
    (hReach : N.Reaches z z')
    (hFoot : N.FootprintWithin P)
    (hs : Not (P s)) :
    z' s = z s :=
  (agreesOutside_of_footprintWithin hReach hFoot).coord hs

theorem eqOn_of_footprintWithin_disjoint
    {N : Network S} {Footprint Protected : S -> Prop}
    {z z' : State S}
    (hReach : N.Reaches z z')
    (hFoot : N.FootprintWithin Footprint)
    (hDisjoint :
      forall s, Footprint s -> Protected s -> False) :
    State.EqOn Protected z' z := by
  rcases hReach with ⟨is, hExec⟩
  exact Exec.eqOn_of_footprintWithin_disjoint
    hExec hFoot hDisjoint

end Reaches

end Network

end Ripple.sCRNUniversality
