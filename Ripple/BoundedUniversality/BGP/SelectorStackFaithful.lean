import Ripple.BoundedUniversality.BGP.SelectorExposureTube
import Ripple.BoundedUniversality.BGP.StackTopRead

/-!
Ripple.BoundedUniversality.BGP.SelectorStackFaithful
---------------------------------

Per-fixed-input exposure-weighted stack tube for the concrete universal
selector.  The deep cycle facts are carried as named finite-window hypotheses;
the induction wiring is closed here.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Finset

/-- The concrete universal-machine orbit on input `w`. -/
def selectorCfgU (w : Nat) : Nat -> MachineInstance.UConf :=
  fun j => MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)

/-- The concrete encoded coordinate for a universal-machine stack index. -/
def selectorStackCoordU (s : Fin 4) : Fin MachineInstance.d_U :=
  MachineInstance.stackMachineEncodingU.stackCoord s

/-- The structural depth of stack coordinate `s` at cycle `j`. -/
def selectorStackDepthU (w : Nat) (s : Fin 4) (j : Nat) : Int :=
  MachineInstance.depthU (selectorCfgU w) j (selectorStackCoordU s)

/-- The exact rational stack code, viewed in `Real`, for stack `s` at cycle `j`. -/
def selectorStackCodeU (w : Nat) (s : Fin 4) (j : Nat) : Real :=
  ((MachineInstance.stackCodeU MachineInstance.B_U MachineInstance.gammaDigit
    (MachineInstance.indexedStackU (selectorCfgU w j) s) : Rat) : Real)

/-- The absolute stack-code error of the analog value `x j`. -/
def selectorStackErrorU (w : Nat) (s : Fin 4) (x : Nat -> Real) (j : Nat) : Real :=
  |x j - selectorStackCodeU w s j|

/-- Stack depths are nonnegative because the coordinate depth is a list length. -/
theorem selectorStackDepthU_nonneg (w : Nat) (s : Fin 4) (j : Nat) :
    0 <= selectorStackDepthU w s j := by
  unfold selectorStackDepthU selectorStackCoordU
  rw [MachineInstance.depthU_stack]
  exact Int.natCast_nonneg _

/--
Per-cycle symbolic stack operation classification for the fixed input orbit.

This is the carried finite-window fact saying that the selected symbolic
push/pop/hold operation is the one implemented by the concrete `M_U` step, with
the matching depth change and the branch-slope error transform.  It is
satisfiable by the concrete local-view classification, `depthU`/`coordDelta`
bookkeeping, and the push/pop algebra in `StackTopRead`.
-/
structure SelectorStackOpClassification
    (w : Nat) (s : Fin 4) (x opTarget : Nat -> Real) (j : Nat) : Prop where
  next_cfg :
    selectorCfgU w (j + 1) = MachineInstance.M_U.step (selectorCfgU w j)
  depth_step :
    selectorStackDepthU w s (j + 1) =
      selectorStackDepthU w s j -
        MachineInstance.stackMachineEncodingU.coordDelta
          (selectorCfgU w j) (selectorStackCoordU s)
  op_error :
    |opTarget j - selectorStackCodeU w s (j + 1)| <=
      (MachineInstance.B_U : Real) ^
          (selectorStackDepthU w s j - selectorStackDepthU w s (j + 1)) *
        selectorStackErrorU w s x j

/--
Faithful exposure-weighted stack tube for one fixed input and one concrete
universal-machine stack coordinate.

The proof is non-circular: the induction hypothesis gives `E_j <= rho`, this
feeds the gate-mix hypothesis at cycle `j`, and only then produces the
recurrence used to prove `E_{j+1} <= rho`.
-/
theorem selector_stack_faithful_tube
    (w : Nat) (s : Fin 4)
    (x mixTarget opTarget epsMix epsWrite : Nat -> Real)
    {C r rho : Real}
    (hinit_exact : x 0 = selectorStackCodeU w s 0)
    (hop_classification :
      forall j, SelectorStackOpClassification w s x opTarget j)
    (hgate_mix :
      forall j,
        expWeight (MachineInstance.B_U : Real) (selectorStackDepthU w s)
            (selectorStackErrorU w s x) j <= rho ->
          |mixTarget j - opTarget j| <= epsMix j)
    (hwrite_reach :
      forall j, |x (j + 1) - mixTarget j| <= epsWrite j)
    (hreserve_geometric :
      forall ell,
        (MachineInstance.B_U : Real) ^
            (selectorStackDepthU w s (ell + 1) + 2) *
          (epsMix ell + epsWrite ell) <= C * r ^ ell)
    (hC : 0 <= C) (hr0 : 0 <= r) (hr1 : r < 1)
    (hreserve_capacity : C / (1 - r) <= rho) :
    forall j,
      expWeight (MachineInstance.B_U : Real) (selectorStackDepthU w s)
        (selectorStackErrorU w s x) j <= rho := by
  let H : Nat -> Int := selectorStackDepthU w s
  let e : Nat -> Real := selectorStackErrorU w s x
  let xi : Nat -> Real := fun j => epsMix j + epsWrite j
  let E : Nat -> Real := fun j => expWeight (MachineInstance.B_U : Real) H e j
  let Omega : Nat -> Real :=
    fun j => (MachineInstance.B_U : Real) ^ (H (j + 1) + 2) * xi j
  have hBpos : 0 < (MachineInstance.B_U : Real) := by
    norm_num [MachineInstance.B_U]
  have hE0 : E 0 = 0 := by
    simp [E, e, H, expWeight, selectorStackErrorU, hinit_exact]
  have hcap : E 0 + C / (1 - r) <= rho := by
    rw [hE0]
    simpa using hreserve_capacity
  have hgeo : forall ell, Omega ell <= C * r ^ ell := by
    intro ell
    simpa [Omega, xi, H] using hreserve_geometric ell
  have hresGeom :
      forall j, E 0 + (Finset.sum (range j) fun ell => Omega ell) <=
        E 0 + C / (1 - r) :=
    expTube_reserve_geometric hgeo hC hr0 hr1
  have htel :
      forall j, E j <= E 0 + (Finset.sum (range j) fun ell => Omega ell) := by
    intro j
    induction j with
    | zero =>
        simp
    | succ j ih =>
        have hEjrho : E j <= rho :=
          le_trans ih (le_trans (hresGeom j) hcap)
        have hrec :
            e (j + 1) <=
              (MachineInstance.B_U : Real) ^ (H j - H (j + 1)) * e j + xi j := by
          have hmixCode :
              |mixTarget j - selectorStackCodeU w s (j + 1)| <=
                epsMix j +
                  (MachineInstance.B_U : Real) ^ (H j - H (j + 1)) * e j := by
            calc
              |mixTarget j - selectorStackCodeU w s (j + 1)|
                  <= |mixTarget j - opTarget j| +
                      |opTarget j - selectorStackCodeU w s (j + 1)| := by
                    exact abs_sub_le (mixTarget j) (opTarget j)
                      (selectorStackCodeU w s (j + 1))
              _ <= epsMix j +
                    (MachineInstance.B_U : Real) ^ (H j - H (j + 1)) * e j := by
                    exact add_le_add (hgate_mix j hEjrho)
                      (hop_classification j).op_error
          calc
            e (j + 1)
                = |x (j + 1) - selectorStackCodeU w s (j + 1)| := by
                  rfl
            _ <= |x (j + 1) - mixTarget j| +
                  |mixTarget j - selectorStackCodeU w s (j + 1)| := by
                  exact abs_sub_le (x (j + 1)) (mixTarget j)
                    (selectorStackCodeU w s (j + 1))
            _ <= epsWrite j +
                  (epsMix j +
                    (MachineInstance.B_U : Real) ^ (H j - H (j + 1)) * e j) := by
                  exact add_le_add (hwrite_reach j) hmixCode
            _ =
                  (MachineInstance.B_U : Real) ^ (H j - H (j + 1)) * e j +
                    xi j := by
                  simp [xi]
                  ring
        have hstep : E (j + 1) <= E j + Omega j := by
          simpa [E, Omega, xi] using
            expWeight_nonexpansive (MachineInstance.B_U : Real) hBpos H e xi j hrec
        calc
          E (j + 1) <= E j + Omega j := hstep
          _ <= (E 0 + (Finset.sum (range j) fun ell => Omega ell)) + Omega j := by
            linarith [ih]
          _ = E 0 + (Finset.sum (range (j + 1)) fun ell => Omega ell) := by
            rw [sum_range_succ]
            ring
  intro j
  exact le_trans (htel j) (le_trans (hresGeom j) hcap)

/-- The exposure-weighted tube gives the local top/second read accuracy. -/
theorem selector_stack_faithful_read_of_tube
    (w : Nat) (s : Fin 4) (x : Nat -> Real) {rho : Real}
    (htube :
      forall j,
        expWeight (MachineInstance.B_U : Real) (selectorStackDepthU w s)
          (selectorStackErrorU w s x) j <= rho) :
    forall j,
      (MachineInstance.B_U : Real) ^ (2 : Int) *
          selectorStackErrorU w s x j <= rho := by
  intro j
  have hB : 1 <= (MachineInstance.B_U : Real) := by
    norm_num [MachineInstance.B_U]
  have he : 0 <= selectorStackErrorU w s x j := by
    exact abs_nonneg _
  exact localview_read_of_expTube (MachineInstance.B_U : Real) hB
    (selectorStackDepthU w s) (selectorStackErrorU w s x) j
    (selectorStackDepthU_nonneg w s j) he (htube j)

#print axioms selector_stack_faithful_tube

end Ripple.BoundedUniversality.BGP
