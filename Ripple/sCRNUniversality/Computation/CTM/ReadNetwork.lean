import Ripple.sCRNUniversality.Computation.CTM.ReadGadget

namespace Ripple.sCRNUniversality

namespace CTM

namespace ReadNetwork

universe u

structure ReadTransitionData (Q : Type u) where
  q : Q
  r : Bool
  w : Bool
  qNext : Q
deriving DecidableEq, Repr, Fintype

abbrev ReadIdx {Q : Type u} (M : Binary Q) :=
  { τ : ReadTransitionData Q //
      M.delta τ.q τ.r = some (τ.w, τ.qNext) }

namespace ReadIdx

variable {Q : Type u} {M : Binary Q}

def q (i : ReadIdx M) : Q := i.1.q
def r (i : ReadIdx M) : Bool := i.1.r
def w (i : ReadIdx M) : Bool := i.1.w
def qNext (i : ReadIdx M) : Q := i.1.qNext

@[simp]
theorem delta (i : ReadIdx M) :
    M.delta (q i) (r i) = some (w i, qNext i) :=
  i.2

end ReadIdx

def readIdxOfDelta {Q : Type u} {M : Binary Q}
    {q : Q} {r w : Bool} {qNext : Q}
    (hδ : M.delta q r = some (w, qNext)) :
    ReadIdx M :=
  ⟨{ q := q, r := r, w := w, qNext := qNext }, hδ⟩

def network {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    Network (FourPhaseSpecies Q) where
  I := ReadIdx M
  fintypeI := inferInstance
  rxn := fun i =>
    ReadGadget.reaction (s := s)
      (ReadIdx.q i) (ReadIdx.r i) (ReadIdx.w i) (ReadIdx.qNext i)

theorem network_allUnitRate {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    (network (s := s) M).allUnitRate := by
  intro i
  rfl

theorem network_hasPositiveRates {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    (network (s := s) M).hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    (network_allUnitRate (s := s) M)

theorem network_equalRates {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    (network (s := s) M).equalRates :=
  Network.equalRates_of_allUnitRate
    (network_allUnitRate (s := s) M)

theorem exec_idx {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (i : ReadIdx M) (tape : Nat)
    (hread : ReadIdx.r i = Encoding.readMSB? s tape) :
    (network (s := s) M).Exec
      (FourPhaseEncoding.enc
        (ReadGadget.sourceCfg (s := s) (ReadIdx.q i) tape))
      (FourPhaseEncoding.enc
        (ReadGadget.targetCfg (s := s)
          (ReadIdx.q i) (ReadIdx.r i) (ReadIdx.w i)
          (ReadIdx.qNext i) tape))
      [i] := by
  exact ExecOf.cons
    (by
      simpa [network, Network.StepAt] using
        ReadGadget.reaction_firesTo (s := s)
          (ReadIdx.q i) (ReadIdx.r i) (ReadIdx.w i)
          (ReadIdx.qNext i) tape hread)
    (ExecOf.nil _)

theorem phaseStep?_read_of_idx {Q : Type u} [Fintype Q]
    {s : Nat} (M : Binary Q)
    (i : ReadIdx M) (tape : Nat)
    (hread : ReadIdx.r i = Encoding.readMSB? s tape) :
    phaseStep? (s := s) M
      (ReadGadget.sourceCfg (s := s) (ReadIdx.q i) tape) =
    some
      (ReadGadget.targetCfg (s := s)
        (ReadIdx.q i) (ReadIdx.r i) (ReadIdx.w i)
        (ReadIdx.qNext i) tape) := by
  have hδ :
      M.delta (ReadIdx.q i) (Encoding.readMSB? s tape) =
        some (ReadIdx.w i, ReadIdx.qNext i) := by
    rw [← hread]
    exact ReadIdx.delta i
  simp [ReadGadget.sourceCfg, ReadGadget.targetCfg,
    phaseStep?, hδ, MicroState.readPhase, MicroState.afterRead, hread]

theorem exec_of_phaseStep?_source {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {q : Q} {tape : Nat} {c' : MicroCfg Q s}
    (hstep :
      phaseStep? (s := s) M
        (ReadGadget.sourceCfg (s := s) q tape) = some c') :
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc
          (ReadGadget.sourceCfg (s := s) q tape))
        (FourPhaseEncoding.enc c') is /\
      is.length = 1 := by
  cases hδ : M.delta q (Encoding.readMSB? s tape) with
  | none =>
      simp [ReadGadget.sourceCfg, phaseStep?, hδ, MicroState.readPhase] at hstep
  | some out =>
      rcases out with ⟨w, qNext⟩
      let i : ReadIdx M :=
        readIdxOfDelta (M := M) (q := q)
          (r := Encoding.readMSB? s tape) (w := w) (qNext := qNext) hδ
      have hEq :
          some
            (ReadGadget.targetCfg (s := s)
              q (Encoding.readMSB? s tape) w qNext tape) = some c' := by
        simpa [ReadGadget.sourceCfg, ReadGadget.targetCfg,
          phaseStep?, hδ, MicroState.readPhase, MicroState.afterRead]
          using hstep
      cases hEq
      refine ⟨[i], ?_, by simp⟩
      simpa [i, readIdxOfDelta, ReadIdx.q, ReadIdx.r, ReadIdx.w,
        ReadIdx.qNext] using exec_idx (s := s) M i tape rfl

theorem canonical_read_eq_sourceCfg {Q : Type u}
    {s : Nat} {c : MicroCfg Q s}
    (hc : CanonicalMicroCfg c)
    (hphase : c.state.phase = Phase4.read) :
    c = ReadGadget.sourceCfg (s := s) c.state.q c.tape := by
  cases c with
  | mk st tape =>
      cases st with
      | mk q phase readSymbol pendingWrite pendingState =>
          cases phase <;> try cases hphase
          have hcanon :
              readSymbol = none /\
                pendingWrite = none /\
                pendingState = none := by
            simpa [CanonicalMicroCfg, MicroState.Canonical] using hc
          rcases hcanon with ⟨hread, hwrite, hstate⟩
          cases hread
          cases hwrite
          cases hstate
          rfl

theorem exec_of_phaseStep?_read {Q : Type u}
    [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hc : CanonicalMicroCfg c)
    (hphase : c.state.phase = Phase4.read)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') is /\
      is.length = 1 := by
  have hcEq :
      c = ReadGadget.sourceCfg (s := s) c.state.q c.tape :=
    canonical_read_eq_sourceCfg (s := s) hc hphase
  rw [hcEq] at hstep ⊢
  exact exec_of_phaseStep?_source (s := s) M hstep

end ReadNetwork

end CTM

end Ripple.sCRNUniversality
