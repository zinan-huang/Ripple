import Ripple.sCRNUniversality.Core.Footprint
import Ripple.sCRNUniversality.Computation.CTM.ReadGadget
import Ripple.sCRNUniversality.Computation.CTM.EraseGadget
import Ripple.sCRNUniversality.Computation.CTM.ShiftGadget
import Ripple.sCRNUniversality.Computation.CTM.WriteGadget

namespace Ripple.sCRNUniversality

namespace CTM

namespace FourPhaseSpecies

universe u

def IsTapePair {Q : Type u} : FourPhaseSpecies Q -> Prop
  | FourPhaseSpecies.tape => True
  | FourPhaseSpecies.tapeBar => True
  | _ => False

def IsLocalMacroFootprint {Q : Type u}
    (oldCtrl newCtrl : FourPhaseSpecies Q) :
    FourPhaseSpecies Q -> Prop :=
  fun species => species = oldCtrl \/ species = newCtrl \/ IsTapePair species

@[simp]
theorem isTapePair_tape {Q : Type u} :
    IsTapePair (Q := Q) FourPhaseSpecies.tape := by
  trivial

@[simp]
theorem isTapePair_tapeBar {Q : Type u} :
    IsTapePair (Q := Q) FourPhaseSpecies.tapeBar := by
  trivial

@[simp]
theorem not_isTapePair_ctrl {Q : Type u}
    (q : Q) (phase : Phase4)
    (readSymbol pendingWrite : Option Bool) (pendingState : Option Q) :
    Not
      (IsTapePair
        (FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState)) := by
  intro h
  cases h

theorem readProbe_isTapePair {Q : Type u} (r : Bool) :
    IsTapePair (FourPhaseEncoding.readProbe (Q := Q) r) := by
  cases r <;> simp [FourPhaseEncoding.readProbe]

theorem isTapePair_iff {Q : Type u} (species : FourPhaseSpecies Q) :
    IsTapePair species <->
      species = FourPhaseSpecies.tape \/
        species = FourPhaseSpecies.tapeBar := by
  cases species <;> simp [IsTapePair]

theorem isTapePair_elim {Q : Type u}
    {P : FourPhaseSpecies Q -> Prop}
    {species : FourPhaseSpecies Q}
    (h : IsTapePair species)
    (htape : P FourPhaseSpecies.tape)
    (htapeBar : P FourPhaseSpecies.tapeBar) :
    P species := by
  cases species with
  | ctrl q phase readSymbol pendingWrite pendingState =>
      cases h
  | tape =>
      exact htape
  | tapeBar =>
      exact htapeBar

theorem localMacroFootprint_of_isTapePair {Q : Type u}
    {oldCtrl newCtrl species : FourPhaseSpecies Q}
    (h : IsTapePair species) :
    IsLocalMacroFootprint oldCtrl newCtrl species :=
  Or.inr (Or.inr h)

@[simp]
theorem localMacroFootprint_oldCtrl {Q : Type u}
    (oldCtrl newCtrl : FourPhaseSpecies Q) :
    IsLocalMacroFootprint oldCtrl newCtrl oldCtrl :=
  Or.inl rfl

@[simp]
theorem localMacroFootprint_newCtrl {Q : Type u}
    (oldCtrl newCtrl : FourPhaseSpecies Q) :
    IsLocalMacroFootprint oldCtrl newCtrl newCtrl :=
  Or.inr (Or.inl rfl)

@[simp]
theorem localMacroFootprint_tape {Q : Type u}
    (oldCtrl newCtrl : FourPhaseSpecies Q) :
    IsLocalMacroFootprint oldCtrl newCtrl FourPhaseSpecies.tape :=
  Or.inr (Or.inr isTapePair_tape)

@[simp]
theorem localMacroFootprint_tapeBar {Q : Type u}
    (oldCtrl newCtrl : FourPhaseSpecies Q) :
    IsLocalMacroFootprint oldCtrl newCtrl FourPhaseSpecies.tapeBar :=
  Or.inr (Or.inr isTapePair_tapeBar)

@[simp]
theorem localMacroFootprint_readProbe {Q : Type u}
    (oldCtrl newCtrl : FourPhaseSpecies Q) (r : Bool) :
    IsLocalMacroFootprint oldCtrl newCtrl
      (FourPhaseEncoding.readProbe (Q := Q) r) :=
  localMacroFootprint_of_isTapePair
    (readProbe_isTapePair (Q := Q) r)

theorem localMacroFootprint_swap {Q : Type u}
    {oldCtrl newCtrl species : FourPhaseSpecies Q}
    (h : IsLocalMacroFootprint oldCtrl newCtrl species) :
    IsLocalMacroFootprint newCtrl oldCtrl species := by
  rcases h with hOld | hRest
  · exact Or.inr (Or.inl hOld)
  · rcases hRest with hNew | hTape
    · exact Or.inl hNew
    · exact Or.inr (Or.inr hTape)

theorem localMacroFootprint_mono {Q : Type u}
    {oldCtrl newCtrl : FourPhaseSpecies Q}
    {P : FourPhaseSpecies Q -> Prop}
    (hold : P oldCtrl)
    (hnew : P newCtrl)
    (htape : P FourPhaseSpecies.tape)
    (htapeBar : P FourPhaseSpecies.tapeBar) :
    forall {species : FourPhaseSpecies Q},
      IsLocalMacroFootprint oldCtrl newCtrl species -> P species := by
  intro species h
  rcases h with hOld | hRest
  · simpa [hOld] using hold
  · rcases hRest with hNew | hTape
    · simpa [hNew] using hnew
    · exact isTapePair_elim hTape htape htapeBar

theorem not_localMacroFootprint_of_not_members {Q : Type u}
    {oldCtrl newCtrl species : FourPhaseSpecies Q}
    (hold : species ≠ oldCtrl)
    (hnew : species ≠ newCtrl)
    (htape : Not (IsTapePair species)) :
    Not (IsLocalMacroFootprint oldCtrl newCtrl species) := by
  intro h
  rcases h with hOld | hRest
  · exact hold hOld
  · rcases hRest with hNew | hTape
    · exact hnew hNew
    · exact htape hTape

theorem not_localMacroFootprint_ctrl {Q : Type u}
    {oldCtrl newCtrl : FourPhaseSpecies Q}
    {q : Q} {phase : Phase4}
    {readSymbol pendingWrite : Option Bool} {pendingState : Option Q}
    (hold :
      FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState ≠
        oldCtrl)
    (hnew :
      FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState ≠
        newCtrl) :
    Not
      (IsLocalMacroFootprint oldCtrl newCtrl
        (FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState)) :=
  not_localMacroFootprint_of_not_members hold hnew
    (not_isTapePair_ctrl q phase readSymbol pendingWrite pendingState)

theorem localMacroFootprint_disjoint {Q : Type u}
    {oldCtrl newCtrl : FourPhaseSpecies Q}
    {Protected : FourPhaseSpecies Q -> Prop}
    (hold : Not (Protected oldCtrl))
    (hnew : Not (Protected newCtrl))
    (htape : Not (Protected FourPhaseSpecies.tape))
    (htapeBar : Not (Protected FourPhaseSpecies.tapeBar)) :
    forall species,
      IsLocalMacroFootprint oldCtrl newCtrl species ->
        Protected species -> False := by
  intro species hLocal hProtected
  rcases hLocal with hOld | hRest
  · exact hold (by simpa [hOld] using hProtected)
  · rcases hRest with hNew | hTapePair
    · exact hnew (by simpa [hNew] using hProtected)
    · exact
        (isTapePair_elim
          (P := fun species => Protected species -> False)
          hTapePair htape htapeBar) hProtected

end FourPhaseSpecies

namespace ReadGadget

universe u

variable {Q : Type u} [DecidableEq Q]

set_option linter.flexible false in
theorem reaction_footprintWithin {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) :
    (reaction (s := s) q r w qNext).FootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf (MicroState.readPhase q))
        (FourPhaseSpecies.ctrlOf
          (MicroState.afterRead (MicroState.readPhase q) r w qNext))) := by
  intro species hTouches
  cases species with
  | ctrl q0 phase0 read0 write0 state0 =>
      rcases hTouches with hInput | hOutput
      · exact Or.inl (by
          by_contra hne
          exact hInput (by
            simp [reaction, input, State.add, State.single,
              FourPhaseEncoding.readProbe]
            constructor
            · intro hq hphase hread hwrite hstate
              exact hne (by
                cases hq
                cases hphase
                cases hread
                cases hwrite
                cases hstate
                rfl)
            · intro hEq
              cases r <;> cases hEq))
      · exact Or.inr (Or.inl (by
          by_contra hne
          exact hOutput (by
            simp [reaction, output, State.add, State.single,
              FourPhaseEncoding.readProbe]
            constructor
            · intro hq hphase hread hwrite hstate
              exact hne (by
                cases hq
                cases hphase
                cases hread
                cases hwrite
                cases hstate
                rfl)
            · intro hEq
              cases r <;> cases hEq)))
  | tape =>
      exact Or.inr (Or.inr FourPhaseSpecies.isTapePair_tape)
  | tapeBar =>
      exact Or.inr (Or.inr FourPhaseSpecies.isTapePair_tapeBar)

end ReadGadget

namespace EraseGadget

universe u

variable {Q : Type u} [DecidableEq Q]

theorem reaction_footprintWithin {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) :
    (reaction (s := s) q r w qNext).FootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf (sourceState q r w qNext))
        (FourPhaseSpecies.ctrlOf (targetState q r w qNext))) := by
  intro species hTouches
  cases species with
  | ctrl q0 phase0 read0 write0 state0 =>
      rcases hTouches with hInput | hOutput
      · exact Or.inl (by
          by_contra hne
          exact hInput (by
            simp [reaction, input, State.add, State.single, hne]))
      · exact Or.inr (Or.inl (by
          by_contra hne
          exact hOutput (by
            simp [reaction, output, State.add, State.single, hne])))
  | tape =>
      exact Or.inr (Or.inr FourPhaseSpecies.isTapePair_tape)
  | tapeBar =>
      exact Or.inr (Or.inr FourPhaseSpecies.isTapePair_tapeBar)

end EraseGadget

namespace ShiftGadget

universe u

variable {Q : Type u} [DecidableEq Q]

theorem reaction_footprintWithin {s : Nat} (i : Idx Q s) :
    (reaction i).FootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf (sourceState i.q i.r i.w i.qNext))
        (FourPhaseSpecies.ctrlOf (targetState i.q i.r i.w i.qNext))) := by
  intro species hTouches
  cases species with
  | ctrl q0 phase0 read0 write0 state0 =>
      rcases hTouches with hInput | hOutput
      · exact Or.inl (by
          by_contra hne
          exact hInput (by
            simp [reaction, input, State.add, State.single, hne]))
      · exact Or.inr (Or.inl (by
          by_contra hne
          exact hOutput (by
            simp [reaction, output, State.add, State.single, hne])))
  | tape =>
      exact Or.inr (Or.inr FourPhaseSpecies.isTapePair_tape)
  | tapeBar =>
      exact Or.inr (Or.inr FourPhaseSpecies.isTapePair_tapeBar)

end ShiftGadget

namespace WriteGadget

universe u

variable {Q : Type u} [DecidableEq Q]

theorem reaction_footprintWithin
    (q : Q) (r w : Bool) (qNext : Q) :
    (reaction q r w qNext).FootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf (sourceState q r w qNext))
        (FourPhaseSpecies.ctrlOf (targetState q r w qNext))) := by
  intro species hTouches
  cases species with
  | ctrl q0 phase0 read0 write0 state0 =>
      rcases hTouches with hInput | hOutput
      · exact Or.inl (by
          by_contra hne
          exact hInput (by
            simp [reaction, input, State.add, State.single, hne]))
      · exact Or.inr (Or.inl (by
          by_contra hne
          exact hOutput (by
            simp [reaction, output, State.add, State.single, hne])))
  | tape =>
      exact Or.inr (Or.inr FourPhaseSpecies.isTapePair_tape)
  | tapeBar =>
      exact Or.inr (Or.inr FourPhaseSpecies.isTapePair_tapeBar)

end WriteGadget

end CTM

end Ripple.sCRNUniversality
