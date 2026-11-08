import Mathlib.Data.Fintype.Basic

namespace Ripple.sCRNUniversality

namespace CTM

inductive Phase4 where
  | read
  | erase
  | shift
  | write
deriving DecidableEq, Repr

namespace Phase4

instance instFintype : Fintype Phase4 where
  elems := [Phase4.read, Phase4.erase, Phase4.shift, Phase4.write].toFinset
  complete := by
    intro p
    cases p <;> simp

def next : Phase4 -> Phase4
  | read => erase
  | erase => shift
  | shift => write
  | write => read

theorem next_four (p : Phase4) :
    next (next (next (next p))) = p := by
  cases p <;> rfl

end Phase4

structure PhaseState (Q : Type u) where
  q : Q
  phase : Phase4
deriving Repr

namespace PhaseState

def advance {Q : Type u} (st : PhaseState Q) : PhaseState Q :=
  { q := st.q, phase := st.phase.next }

theorem advance_phase {Q : Type u} (st : PhaseState Q) :
    st.advance.phase = st.phase.next := by
  rfl

theorem advance_q {Q : Type u} (st : PhaseState Q) :
    st.advance.q = st.q := by
  rfl

theorem advance_four {Q : Type u} (st : PhaseState Q) :
    st.advance.advance.advance.advance = st := by
  cases st
  simp [advance, Phase4.next_four]

end PhaseState

structure PhaseStepContract (Cfg : Type u) where
  phase : Cfg -> Phase4
  step : Cfg -> Cfg -> Prop
  phase_progress :
    forall {c c'}, step c c' -> phase c' = (phase c).next

end CTM

end Ripple.sCRNUniversality
