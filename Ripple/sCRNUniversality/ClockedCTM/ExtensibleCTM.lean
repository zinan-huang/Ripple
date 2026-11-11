import Ripple.sCRNUniversality.ClockedCTM.TMtoCTM
import Ripple.sCRNUniversality.CTM.Basic

/-!
# Extensible clockwise simulation of a binary TM

This is the deterministic layer of FIX3-SCWB-T41 Sections 1 and 12.
The model extends the existing ClockedCTM.CTM read transition.

The controller depends on M alone. The canonical tape stores the head,
the cells to its right, a seam, and the reversed left part. Its length is
2 * tlen T + 2. Each newly visited cell outside the initially allocated
interval causes exactly two one-bit extension operations.

The four continuing macro costs are 2L+4, 4L+10, 4L+4, and 6L+12.
xTime freezes when the TM halts; the xCTM then takes two additional
microsteps to read the head slot and enter its absorbing halt state.

The repository convention delta = none can depend on the scanned symbol.
Accordingly, every source state has both an hd and a halt controller state.
No separate state-only halting-set hypothesis is used.

Absolute interval geometry is tracked with an external initial head
coordinate. The canonical decoder returns the existing relative TM.Tape.
-/

namespace Ripple.sCRNUniversality.ClockedCTM

/-- The three disjoint operations of an extensible clockwise machine. -/
inductive XCTMMode (Q : Type)
  | read
  | extend (next : Q)
  | halt
  deriving DecidableEq, Fintype, Repr

/-- A clockwise machine with state-controlled tape extension and halting.
The read transition is the existing ClockedCTM.CTM transition. -/
structure XCTM (Q : Type) extends CTM Q where
  start : Q
  mode : Q → XCTMMode Q

namespace XCTM

variable {Q : Type}

/-- A read rotates and writes, an extension appends a blank without moving
the head, and a halting state has no successor. Empty read tapes are stuck. -/
def step? (C : XCTM Q) (c : Q × List Bool) : Option (Q × List Bool) :=
  match C.mode c.1 with
  | .read =>
      match c.2 with
      | [] => none
      | _ :: _ => some (C.toCTM.stepT c)
  | .extend q => some (q, c.2 ++ [false])
  | .halt => none

/-- Total run convention: a configuration with no successor remains fixed. -/
def stepT (C : XCTM Q) (c : Q × List Bool) : Q × List Bool :=
  (C.step? c).getD c

def runT (C : XCTM Q) (c : Q × List Bool) : ℕ → Q × List Bool
  | 0 => c
  | k + 1 => C.stepT (C.runT c k)

end XCTM

/-- Content carried by the leftward simulation sweep. -/
inductive XCarry
  | symbol (bit : Bool)
  | seam
  deriving DecidableEq, Fintype, Repr

def xmarker : XCarry → Bool
  | .symbol _ => false
  | .seam => true

def xsymbol : XCarry → Bool
  | .symbol b => b
  | .seam => false

/-- The finite controller of FIX3-SCWB-T41 Section 12.3. Halting is detected
at the symbol read, using the existing TM convention delta = none. -/
inductive XCS (QM : Type)
  | gClear (q : QM)
  | gClearSym (q : QM)
  | gPending (q : QM)
  | gPendingSym (q : QM)
  | gPendingMarked (q : QM)
  | hd (q : QM)
  | halt (q : QM)
  | mk (q : QM)
  | ms (q : QM)
  | cPending (q : QM)
  | cPendingSym (q : QM)
  | cPendingMarked (q : QM)
  | cClear (q : QM)
  | cClearSym (q : QM)
  | cz (q : QM)
  | rx (q : QM)
  | erFirst (q : QM)
  | erSecond (q : QM)
  | pa (q : QM)
  | paSym (q : QM)
  | paMarked (q : QM)
  | pb (q : QM)
  | pbSym (q : QM)
  | pc (q : QM)
  | pcSym (q : QM)
  | sh (q : QM) (carry : XCarry) (passed : Bool)
  | shSym (q : QM) (carry : XCarry) (passed marker : Bool)
  | se (q : QM) (carry : XCarry)
  | elFirst (q : QM)
  | elSecond (q : QM)
  | qa (q : QM)
  | qaSym (q : QM)
  | qaMarked (q : QM)
  | qb (q : QM)
  | qbSym (q : QM)
  deriving DecidableEq, Fintype, Repr

variable {QM : Type}

/-- The extensible controller depends on the TM alone. -/
def xctmOf (M : TM.Machine QM Bool) : XCTM (XCS QM) where
  start := .gClear M.start
  mode s := match s with
    | .erFirst q => .extend (.erSecond q)
    | .erSecond q => .extend (.pa q)
    | .elFirst q => .extend (.elSecond q)
    | .elSecond q => .extend (.qa q)
    | .halt _ => .halt
    | _ => .read
  next s a := match s, a with
    | .gClear q, false => (.gClearSym q, false)
    | .gClear q, true => (.hd q, true)
    | .gClearSym q, b => (.gClear q, b)
    | .gPending q, false => (.gPendingSym q, false)
    | .gPending q, true => (.gPendingMarked q, true)
    | .gPendingSym q, b => (.gPending q, b)
    | .gPendingMarked q, b => (.gClear q, b)
    | .hd q, b =>
        match M.delta q b with
        | none => (.halt q, b)
        | some (z, .R, q') => (.mk q', z)
        | some (z, .L, q') => (.sh q' (.symbol z) false, z)
    | .mk q, false => (.ms q, true)
    | .mk q, true => (.rx q, true)
    | .ms q, b => (.cPending q, b)
    | .cPending q, false => (.cPendingSym q, false)
    | .cPending q, true => (.cPendingMarked q, true)
    | .cPendingSym q, b => (.cPending q, b)
    | .cPendingMarked q, b => (.cClear q, b)
    | .cClear q, false => (.cClearSym q, false)
    | .cClear q, true => (.cz q, false)
    | .cClearSym q, b => (.cClear q, b)
    | .cz q, b => (.gClear q, b)
    | .rx q, _ => (.erFirst q, false)
    | .pa q, false => (.paSym q, false)
    | .pa q, true => (.paMarked q, false)
    | .paSym q, b => (.pa q, b)
    | .paMarked q, b => (.pb q, b)
    | .pb q, _ => (.pbSym q, true)
    | .pbSym q, b => (.pc q, b)
    | .pc q, _ => (.pcSym q, true)
    | .pcSym q, _ => (.gClear q, false)
    | .sh q c p, false => (.shSym q c p false, xmarker c)
    | .sh q c false, true => (.shSym q c false true, xmarker c)
    | .sh q c true, true => (.se q c, true)
    | .shSym q c p m, b =>
        (.sh q (if m then .seam else .symbol b) (p || m), xsymbol c)
    | .se q (.symbol c), _ => (.gPending q, c)
    | .se q .seam, _ => (.elFirst q, false)
    | .qa q, false => (.qaSym q, false)
    | .qa q, true => (.qaMarked q, true)
    | .qaSym q, b => (.qa q, b)
    | .qaMarked q, b => (.qb q, b)
    | .qb q, _ => (.qbSym q, true)
    | .qbSym q, _ => (.gPending q, false)
    | q, b => (q, b)

/-- Canonical pair encoding, including the unique seam pair. -/
def xencT (T : TM.Tape Bool) : List Bool :=
  true :: T.head :: (pairs0 T.right ++ [true, false] ++ pairs0 T.left.reverse)

/-- Canonical extensible-machine configuration. -/
def xencC (q : QM) (T : TM.Tape Bool) : XCS QM × List Bool :=
  (.gClear q, xencT T)

namespace XCTM

variable {Q : Type}

def ofCTM (C : CTM Q) (q₀ : Q) : XCTM Q where
  toCTM := C
  start := q₀
  mode _ := .read

theorem stepT_of_read (C : XCTM Q) (c : Q × List Bool)
    (hm : C.mode c.1 = .read) (hn : c.2 ≠ []) :
    C.stepT c = C.toCTM.stepT c := by
  rcases c with ⟨q, w⟩
  cases w with
  | nil => exact False.elim (hn rfl)
  | cons b u => simp [stepT, step?, hm]

/-- Embedding an ordinary clockwise machine preserves its read step. -/
theorem ofCTM_stepT (C : CTM Q) (q₀ : Q) (c : Q × List Bool)
    (hn : c.2 ≠ []) :
    (ofCTM C q₀).stepT c = C.stepT c := by
  exact stepT_of_read (ofCTM C q₀) c rfl hn

theorem stepT_of_extend (C : XCTM Q) (c : Q × List Bool) (q' : Q)
    (hm : C.mode c.1 = .extend q') :
    C.stepT c = (q', c.2 ++ [false]) := by
  simp [stepT, step?, hm]

theorem step?_of_halt (C : XCTM Q) (c : Q × List Bool)
    (hm : C.mode c.1 = .halt) : C.step? c = none := by
  simp [step?, hm]

/-- On valid tapes, the absence of a successor means a halting state. -/
theorem step?_eq_none_iff (C : XCTM Q) (c : Q × List Bool) (hn : c.2 ≠ []) :
    C.step? c = none ↔ C.mode c.1 = .halt := by
  rcases c with ⟨q, w⟩
  cases w with
  | nil => exact False.elim (hn rfl)
  | cons b u =>
      cases hm : C.mode q <;> simp [step?, hm]

theorem stepT_of_halt (C : XCTM Q) (c : Q × List Bool)
    (hm : C.mode c.1 = .halt) : C.stepT c = c := by
  simp [stepT, step?_of_halt C c hm]

theorem runT_of_halt (C : XCTM Q) (c : Q × List Bool)
    (hm : C.mode c.1 = .halt) (k : ℕ) : C.runT c k = c := by
  induction k with
  | zero => rfl
  | succ k ih => rw [runT, ih, stepT_of_halt C c hm]

/-- The existing fixed-length vector rotate/write operation is the tape
component of the same read step. -/
theorem stepT_read_rotateWrite (C : XCTM Q) (q : Q) {s : ℕ}
    (w : List.Vector Bool (s + 1)) (hm : C.mode q = .read) :
    (C.stepT (q, w.toList)).2 =
      (Ripple.sCRNUniversality.CTM.Machine.rotateWrite w
        (C.toCTM.next q (w.toList.headD false)).2).toList := by
  have hn : w.toList ≠ [] := by
    intro h
    have hl : w.toList.length = s + 1 := w.2
    rw [h] at hl
    simp at hl
  rw [stepT_of_read C (q, w.toList) hm hn]
  rfl

/-- Each extension operation inserts exactly one physical tape cell. -/
def extensionMark (C : XCTM Q) (q : Q) : ℕ :=
  match C.mode q with
  | .extend _ => 1
  | _ => 0

theorem extensionMark_le_one (C : XCTM Q) (q : Q) :
    C.extensionMark q ≤ 1 := by
  cases hm : C.mode q <;> simp [extensionMark, hm]

theorem stepT_length (C : XCTM Q) (c : Q × List Bool) :
    (C.stepT c).2.length = c.2.length + C.extensionMark c.1 := by
  rcases c with ⟨q, w⟩
  cases hm : C.mode q with
  | read =>
      cases w with
      | nil => simp [stepT, step?, extensionMark, hm]
      | cons b u => simp [stepT, step?, CTM.stepT, extensionMark, hm]
  | extend q' => simp [stepT, step?, extensionMark, hm]
  | halt => simp [stepT, step?, extensionMark, hm]

theorem stepT_length_mono (C : XCTM Q) (c : Q × List Bool) :
    c.2.length ≤ (C.stepT c).2.length := by
  rw [stepT_length]
  omega

theorem stepT_length_le (C : XCTM Q) (c : Q × List Bool) :
    (C.stepT c).2.length ≤ c.2.length + 1 := by
  rw [stepT_length]
  have h := extensionMark_le_one C c.1
  omega

/-- Number of physical extension operations in a finite xCTM run. -/
def extensionCount (C : XCTM Q) (c : Q × List Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      C.extensionCount c k + C.extensionMark (C.runT c k).1

theorem runT_length (C : XCTM Q) (c : Q × List Bool) (k : ℕ) :
    (C.runT c k).2.length = c.2.length + C.extensionCount c k := by
  induction k with
  | zero => simp [runT, extensionCount]
  | succ k ih =>
      simp only [runT, stepT_length, ih, extensionCount, Nat.add_assoc]

theorem extensionCount_le (C : XCTM Q) (c : Q × List Bool) (k : ℕ) :
    C.extensionCount c k ≤ k := by
  induction k with
  | zero => simp [extensionCount]
  | succ k ih =>
      simp only [extensionCount]
      have h := extensionMark_le_one C (C.runT c k).1
      omega

theorem runT_length_le (C : XCTM Q) (c : Q × List Bool) (k : ℕ) :
    (C.runT c k).2.length ≤ c.2.length + k := by
  rw [runT_length]
  have h := extensionCount_le C c k
  omega

theorem runT_length_mono (C : XCTM Q) (c : Q × List Bool) :
    Monotone (fun k => (C.runT c k).2.length) := by
  apply monotone_nat_of_le_succ
  intro k
  simpa only [runT] using stepT_length_mono C (C.runT c k)

/-- Nonempty cyclic tapes remain nonempty throughout every run. -/
theorem runT_ne_nil (C : XCTM Q) (c : Q × List Bool) (hn : c.2 ≠ []) (k : ℕ) :
    (C.runT c k).2 ≠ [] := by
  have hpos : 0 < c.2.length := by
    cases h : c.2 <;> simp_all
  intro hk
  have hl := runT_length C c k
  rw [hk] at hl
  simp only [List.length_nil] at hl
  omega

end XCTM

theorem xencT_length (T : TM.Tape Bool) :
    (xencT T).length = 2 * tlen T + 2 := by
  simp only [xencT, List.length_cons, List.length_append, pairs0_length,
    List.length_reverse, List.length_nil, tlen]
  omega

theorem xencT_ne_nil (T : TM.Tape Bool) : xencT T ≠ [] := by
  simp [xencT]

theorem xencT_length_ge (T : TM.Tape Bool) : 4 ≤ (xencT T).length := by
  rw [xencT_length]
  simp only [tlen]
  omega

/-- Parse an ordinary sequence of marker-zero slots. -/
def xdecodeOrdinaryPairs : List Bool → Option (List Bool)
  | [] => some []
  | false :: b :: u => (xdecodeOrdinaryPairs u).map (List.cons b)
  | _ => none

/-- Parse the right interval, the seam, and the reversed left interval. -/
def xdecodeSeam : List Bool → Option (List Bool × List Bool)
  | true :: false :: u =>
      (xdecodeOrdinaryPairs u).map (fun l => ([], l.reverse))
  | false :: b :: u =>
      (xdecodeSeam u).map (fun p => (b :: p.1, p.2))
  | _ => none

/-- Decode a canonical tape into the existing relative TM tape representation. -/
def xdecodeT : List Bool → Option (TM.Tape Bool)
  | true :: b :: u =>
      (xdecodeSeam u).map (fun p => ⟨p.2, b, p.1⟩)
  | _ => none

theorem xdecodeOrdinaryPairs_pairs (u : List Bool) :
    xdecodeOrdinaryPairs (pairs0 u) = some u := by
  induction u with
  | nil => rfl
  | cons b u ih =>
      simp only [pairs0_cons, xdecodeOrdinaryPairs, ih, Option.map_some]

theorem xdecodeSeam_pairs (r l : List Bool) :
    xdecodeSeam (pairs0 r ++ [true, false] ++ pairs0 l.reverse) =
      some (r, l) := by
  induction r with
  | nil =>
      simp [pairs0_nil, xdecodeSeam, xdecodeOrdinaryPairs_pairs]
  | cons b r ih =>
      simp only [pairs0_cons, List.cons_append, xdecodeSeam, ih, Option.map_some]

theorem xdecodeT_xencT (T : TM.Tape Bool) :
    xdecodeT (xencT T) = some T := by
  cases T with
  | mk l b r =>
      simp only [xencT, xdecodeT, xdecodeSeam_pairs, Option.map_some]

theorem xencT_injective : Function.Injective xencT := by
  intro T U h
  apply Option.some.inj
  simpa only [xdecodeT_xencT] using congrArg xdecodeT h

theorem xencC_injective :
    Function.Injective (fun c : TM.Cfg QM Bool => xencC c.state c.tape) := by
  intro c d h
  have hq : c.state = d.state := by
    have hs : XCS.gClear c.state = XCS.gClear d.state := congrArg Prod.fst h
    exact XCS.gClear.inj hs
  have ht : c.tape = d.tape := by
    apply xencT_injective
    exact congrArg Prod.snd h
  cases c
  cases d
  simp only at hq ht
  cases hq
  cases ht
  rfl

/-- Input padded to the prescribed initial visited interval. -/
def xInputWord (s : ℕ) (input : List Bool) : List Bool :=
  input ++ List.replicate (s - input.length) false

def xInputTape (s : ℕ) (input : List Bool) : TM.Tape Bool where
  left := []
  head := (xInputWord s input).headD false
  right := (xInputWord s input).tail

theorem xInputWord_length (s : ℕ) (input : List Bool)
    (hi : input.length ≤ s) : (xInputWord s input).length = s := by
  simp only [xInputWord, List.length_append, List.length_replicate]
  omega

theorem xInputTape_tlen (s : ℕ) (input : List Bool)
    (hs : 1 ≤ s) (hi : input.length ≤ s) :
    tlen (xInputTape s input) = s := by
  have hw := xInputWord_length s input hi
  simp only [xInputTape, tlen, List.length_nil, List.length_tail]
  omega

theorem xInputTape_encoding_length (s : ℕ) (input : List Bool)
    (hs : 1 ≤ s) (hi : input.length ≤ s) :
    (xencT (xInputTape s input)).length = 2 * s + 2 := by
  rw [xencT_length, xInputTape_tlen s input hs hi]

theorem xctmOf_finite [Finite QM] : Finite (XCS QM) := by
  letI := Fintype.ofFinite QM
  infer_instance

theorem xctmOf_halt_after_two (M : TM.Machine QM Bool) (q : QM) (T : TM.Tape Bool)
    (hδ : M.delta q T.head = none) :
    (xctmOf M).runT (xencC q T) 2 =
      (.halt q,
        (pairs0 T.right ++ [true, false] ++ pairs0 T.left.reverse) ++
          [true, T.head]) := by
  simp [XCTM.runT, XCTM.stepT, XCTM.step?, CTM.stepT, xctmOf,
    xencC, xencT, hδ, List.append_assoc]

theorem xctmOf_halt_iff_after_two
    (M : TM.Machine QM Bool) (q : QM) (T : TM.Tape Bool) :
    M.delta q T.head = none ↔
      (xctmOf M).mode ((xctmOf M).runT (xencC q T) 2).1 = .halt := by
  cases hδ : M.delta q T.head with
  | none =>
      simp [XCTM.runT, XCTM.stepT, XCTM.step?, CTM.stepT, xctmOf,
        xencC, xencT, hδ, List.append_assoc]
  | some step =>
      rcases step with ⟨z, d, q'⟩
      cases d <;>
        simp [XCTM.runT, XCTM.stepT, XCTM.step?, CTM.stepT, xctmOf,
          xencC, xencT, hδ, List.append_assoc]


namespace XCTM

variable {Q : Type}

/-- Tapes in the length range used by the chemical simulation. -/
def Valid (c : Q × List Bool) : Prop := 3 ≤ c.2.length

theorem stepT_valid (C : XCTM Q) (c : Q × List Bool) (hc : Valid c) :
    Valid (C.stepT c) := by
  exact le_trans hc (stepT_length_mono C c)

theorem runT_valid (C : XCTM Q) (c : Q × List Bool) (hc : Valid c) (k : ℕ) :
    Valid (C.runT c k) := by
  change 3 ≤ (C.runT c k).2.length
  rw [runT_length]
  change 3 ≤ c.2.length at hc
  omega

end XCTM

theorem xencC_valid (q : QM) (T : TM.Tape Bool) :
    XCTM.Valid (xencC q T) := by
  change 3 ≤ (xencT T).length
  have h := xencT_length_ge T
  omega



namespace XCTM

variable {Q : Type}

theorem runT_add (C : XCTM Q) (c : Q × List Bool) (m n : ℕ) :
    C.runT c (m + n) = C.runT (C.runT c m) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← Nat.add_assoc, runT, ih, runT]

theorem runT_two (C : XCTM Q) (c : Q × List Bool) :
    C.runT c 2 = C.stepT (C.stepT c) := rfl

theorem runT_four (C : XCTM Q) (c : Q × List Bool) :
    C.runT c 4 = C.stepT (C.stepT (C.stepT (C.stepT c))) := rfl

theorem runT_six (C : XCTM Q) (c : Q × List Bool) :
    C.runT c 6 = C.stepT (C.stepT (C.stepT (C.stepT (C.stepT (C.stepT c))))) := rfl

end XCTM

/-- The ordinary-slot copy loops of the controller. -/
inductive XScan
  | seekClear
  | seekPending
  | copyClear
  | copyPending
  | repairRight
  | repairLeft
  deriving DecidableEq, Fintype

def XScan.state {QM : Type} (kind : XScan) (q : QM) : XCS QM :=
  match kind with
  | .seekClear => .gClear q
  | .seekPending => .gPending q
  | .copyClear => .cClear q
  | .copyPending => .cPending q
  | .repairRight => .pa q
  | .repairLeft => .qa q

variable (M : TM.Machine QM Bool)

/-- Each listed loop copies an arbitrary sequence of unmarked slots. -/
theorem xrun_scan (kind : XScan) (q : QM) (v rest : List Bool) :
    (xctmOf M).runT (kind.state q, pairs0 v ++ rest) (2 * v.length) =
      (kind.state q, rest ++ pairs0 v) := by
  induction v generalizing rest with
  | nil => simp [pairs0_nil, XCTM.runT]
  | cons a v ih =>
    have hpair :
        (xctmOf M).runT (kind.state q, pairs0 (a :: v) ++ rest) 2 =
          (kind.state q, pairs0 v ++ (rest ++ [false, a])) := by
      rw [XCTM.runT_two]
      cases kind <;>
        simp [XScan.state, XCTM.stepT, XCTM.step?, CTM.stepT,
          xctmOf, pairs0_cons]
    rw [show 2 * (a :: v).length = 2 + 2 * v.length by
        simp only [List.length_cons]; ring,
      XCTM.runT_add, hpair, ih]
    simp [pairs0_cons]

/-- Seeking the head while one seam remains to be passed. -/
theorem xrun_seek_seam (q : QM) (v w rest : List Bool) :
    (xctmOf M).runT
        (.gPending q, pairs0 v ++ [true, false] ++ pairs0 w ++ rest)
        (2 * v.length + 2 + 2 * w.length) =
      (.gClear q, rest ++ pairs0 v ++ [true, false] ++ pairs0 w) := by
  have hscan :
      (xctmOf M).runT
          (.gPending q, pairs0 v ++ [true, false] ++ pairs0 w ++ rest)
          (2 * v.length) =
        (.gPending q, ([true, false] ++ pairs0 w ++ rest) ++ pairs0 v) := by
    simpa [XScan.state, List.append_assoc] using
      xrun_scan M .seekPending q v ([true, false] ++ pairs0 w ++ rest)
  have hmark :
      (xctmOf M).runT
          (.gPending q, pairs0 v ++ [true, false] ++ pairs0 w ++ rest)
          (2 * v.length + 2) =
        (.gClear q, pairs0 w ++ (rest ++ pairs0 v ++ [true, false])) := by
    rw [XCTM.runT_add, hscan, XCTM.runT_two]
    simp [XCTM.stepT, XCTM.step?, CTM.stepT, xctmOf, List.append_assoc]
  rw [XCTM.runT_add _ _ (2 * v.length + 2) (2 * w.length), hmark]
  simpa [XScan.state, List.append_assoc] using
    xrun_scan M .seekClear q w (rest ++ pairs0 v ++ [true, false])

/-- The right-move cleanup passes the seam and clears the old head marker. -/
theorem xrun_clear_head (q : QM) (v w : List Bool) (z : Bool) (rest : List Bool) :
    (xctmOf M).runT
        (.cPending q, pairs0 v ++ [true, false] ++ pairs0 w ++ [true, z] ++ rest)
        (2 * v.length + 2 + 2 * w.length + 2) =
      (.gClear q, rest ++ pairs0 v ++ [true, false] ++ pairs0 w ++ [false, z]) := by
  have hscan :
      (xctmOf M).runT
          (.cPending q, pairs0 v ++ [true, false] ++ pairs0 w ++ [true, z] ++ rest)
          (2 * v.length) =
        (.cPending q,
          ([true, false] ++ pairs0 w ++ [true, z] ++ rest) ++ pairs0 v) := by
    simpa [XScan.state, List.append_assoc] using
      xrun_scan M .copyPending q v
        ([true, false] ++ pairs0 w ++ [true, z] ++ rest)
  have hseam :
      (xctmOf M).runT
          (.cPending q, pairs0 v ++ [true, false] ++ pairs0 w ++ [true, z] ++ rest)
          (2 * v.length + 2) =
        (.cClear q, pairs0 w ++ ([true, z] ++ rest ++ pairs0 v ++ [true, false])) := by
    rw [XCTM.runT_add, hscan, XCTM.runT_two]
    simp [XCTM.stepT, XCTM.step?, CTM.stepT, xctmOf, List.append_assoc]
  have htail :
      (xctmOf M).runT
          (.cPending q, pairs0 v ++ [true, false] ++ pairs0 w ++ [true, z] ++ rest)
          (2 * v.length + 2 + 2 * w.length) =
        (.cClear q,
          ([true, z] ++ rest ++ pairs0 v ++ [true, false]) ++ pairs0 w) := by
    rw [XCTM.runT_add, hseam]
    simpa [XScan.state] using
      xrun_scan M .copyClear q w
        ([true, z] ++ rest ++ pairs0 v ++ [true, false])
  rw [XCTM.runT_add _ _ (2 * v.length + 2 + 2 * w.length) 2,
    htail, XCTM.runT_two]
  simp [XCTM.stepT, XCTM.step?, CTM.stepT, xctmOf, List.append_assoc]

/-- The two-cell code of a carried symbol or seam. -/
def xslot (c : XCarry) : List Bool := [xmarker c, xsymbol c]

/-- A shift through ordinary slots ending in a known last symbol. -/
theorem xrun_shift_to_last
    (q : QM) (c : XCarry) (passed : Bool) (v : List Bool) (a : Bool) (rest : List Bool) :
    (xctmOf M).runT
        (.sh q c passed, pairs0 (v ++ [a]) ++ rest)
        (2 * (v.length + 1)) =
      (.sh q (.symbol a) passed, rest ++ xslot c ++ pairs0 v) := by
  induction v generalizing c rest with
  | nil =>
      cases passed <;>
        simp [pairs0_cons, pairs0_nil, XCTM.runT, XCTM.stepT, XCTM.step?,
          CTM.stepT, xctmOf, xslot, List.append_assoc]
  | cons b v ih =>
      have hpair :
          (xctmOf M).runT
              (.sh q c passed, pairs0 ((b :: v) ++ [a]) ++ rest) 2 =
            (.sh q (.symbol b) passed,
              pairs0 (v ++ [a]) ++ (rest ++ xslot c)) := by
        rw [XCTM.runT_two]
        cases passed <;>
          simp [List.cons_append, pairs0_cons, XCTM.stepT, XCTM.step?,
            CTM.stepT, xctmOf, xslot, List.append_assoc]
      rw [show 2 * ((b :: v).length + 1) = 2 + 2 * (v.length + 1) by
          simp only [List.length_cons]; ring,
        XCTM.runT_add, hpair, ih]
      simp [xslot, xmarker, xsymbol, pairs0_cons, List.append_assoc]

/-- A shift through ordinary slots and the unique not-yet-passed seam. -/
theorem xrun_shift_to_seam
    (q : QM) (c : Bool) (v rest : List Bool) :
    (xctmOf M).runT
        (.sh q (.symbol c) false, pairs0 v ++ [true, false] ++ rest)
        (2 * v.length + 2) =
      (.sh q .seam true, rest ++ pairs0 (c :: v)) := by
  induction v generalizing c rest with
  | nil =>
      simp [pairs0_cons, pairs0_nil, XCTM.runT, XCTM.stepT, XCTM.step?,
        CTM.stepT, xctmOf, xmarker, xsymbol, List.append_assoc]
  | cons a v ih =>
      have hpair :
          (xctmOf M).runT
              (.sh q (.symbol c) false, pairs0 (a :: v) ++ [true, false] ++ rest) 2 =
            (.sh q (.symbol a) false,
              pairs0 v ++ [true, false] ++ (rest ++ [false, c])) := by
        rw [XCTM.runT_two]
        simp [pairs0_cons, XCTM.stepT, XCTM.step?, CTM.stepT,
          xctmOf, xmarker, xsymbol, List.append_assoc]
      rw [show 2 * (a :: v).length + 2 = 2 + (2 * v.length + 2) by
          simp only [List.length_cons]; ring,
        XCTM.runT_add, hpair, ih]
      simp [pairs0_cons, List.append_assoc]

/-! ### Lemma X: the four continuing macro steps -/

/-- Lemma X, right move inside the visited interval: exactly `2L + 4` steps. -/
theorem xctm_step_right {q q' : QM} {l r : List Bool} {u a z : Bool}
    (hδ : M.delta q u = some (z, .R, q')) :
    (xctmOf M).runT (xencC q ⟨l, u, a :: r⟩)
        (2 * tlen ⟨l, u, a :: r⟩ + 4) =
      xencC q' ⟨z :: l, a, r⟩ := by
  have hfirst :
      (xctmOf M).runT (xencC q ⟨l, u, a :: r⟩) 4 =
        (.cPending q',
          pairs0 r ++ [true, false] ++ pairs0 l.reverse ++ [true, z, true, a]) := by
    rw [XCTM.runT_four]
    simp [xencC, xencT, pairs0_cons, XCTM.stepT, XCTM.step?,
      CTM.stepT, xctmOf, hδ, List.append_assoc]
  rw [show 2 * tlen ⟨l, u, a :: r⟩ + 4 =
      4 + (2 * r.length + 2 + 2 * l.reverse.length + 2) by
        simp only [tlen, List.length_cons, List.length_reverse]; ring,
    XCTM.runT_add, hfirst]
  simpa [xencC, xencT, List.reverse_cons, pairs0_append, pairs0_cons,
    pairs0_nil, List.append_assoc] using
    xrun_clear_head M q' r l.reverse z [true, a]

/-- Lemma X, right move beyond the visited interval: exactly `4L + 10` steps. -/
theorem xctm_step_right_extend {q q' : QM} {l : List Bool} {u z : Bool}
    (hδ : M.delta q u = some (z, .R, q')) :
    (xctmOf M).runT (xencC q ⟨l, u, []⟩)
        (4 * tlen ⟨l, u, []⟩ + 10) =
      xencC q' ⟨z :: l, false, []⟩ := by
  have hfirst :
      (xctmOf M).runT (xencC q ⟨l, u, []⟩) 6 =
        (.pa q', pairs0 l.reverse ++ [true, z, true, false, false, false]) := by
    rw [XCTM.runT_six]
    simp [xencC, xencT, pairs0_nil, XCTM.stepT, XCTM.step?,
      CTM.stepT, xctmOf, hδ, List.append_assoc]
  have hscan :
      (xctmOf M).runT (xencC q ⟨l, u, []⟩)
          (6 + 2 * l.reverse.length) =
        (.pa q', [true, z, true, false, false, false] ++ pairs0 l.reverse) := by
    rw [XCTM.runT_add, hfirst]
    simpa [XScan.state] using
      xrun_scan M .repairRight q' l.reverse [true, z, true, false, false, false]
  have hrepair :
      (xctmOf M).runT (xencC q ⟨l, u, []⟩)
          (6 + 2 * l.reverse.length + 6) =
        (.gClear q', pairs0 (l.reverse ++ [z]) ++ [true, false, true, false]) := by
    rw [XCTM.runT_add, hscan, XCTM.runT_six]
    simp [XCTM.stepT, XCTM.step?, CTM.stepT, xctmOf,
      pairs0_append, pairs0_cons, pairs0_nil, List.append_assoc]
  rw [show 4 * tlen ⟨l, u, []⟩ + 10 =
      6 + 2 * l.reverse.length + 6 + 2 * (l.reverse ++ [z]).length by
        simp only [tlen, List.length_nil, List.length_reverse, List.length_append,
          List.length_cons]; ring,
    XCTM.runT_add, hrepair]
  simpa [XScan.state, xencC, xencT, pairs0_nil, List.reverse_cons,
    List.append_assoc] using
    xrun_scan M .seekClear q' (l.reverse ++ [z]) [true, false, true, false]

/-- Lemma X, left move inside the visited interval: exactly `4L + 4` steps. -/
theorem xctm_step_left {q q' : QM} {l r : List Bool} {u a z : Bool}
    (hδ : M.delta q u = some (z, .L, q')) :
    (xctmOf M).runT (xencC q ⟨a :: l, u, r⟩)
        (4 * tlen ⟨a :: l, u, r⟩ + 4) =
      xencC q' ⟨l, a, z :: r⟩ := by
  have hfirst :
      (xctmOf M).runT (xencC q ⟨a :: l, u, r⟩) 2 =
        (.sh q' (.symbol z) false,
          pairs0 r ++ [true, false] ++ pairs0 (l.reverse ++ [a]) ++ [true, z]) := by
    rw [XCTM.runT_two]
    simp [xencC, xencT, List.reverse_cons, XCTM.stepT, XCTM.step?,
      CTM.stepT, xctmOf, hδ, List.append_assoc]
  have hseam :
      (xctmOf M).runT (xencC q ⟨a :: l, u, r⟩)
          (2 + (2 * r.length + 2)) =
        (.sh q' .seam true,
          pairs0 (l.reverse ++ [a]) ++ [true, z] ++ pairs0 (z :: r)) := by
    rw [XCTM.runT_add, hfirst]
    simpa [List.append_assoc] using
      xrun_shift_to_seam M q' z r (pairs0 (l.reverse ++ [a]) ++ [true, z])
  have hlast :
      (xctmOf M).runT (xencC q ⟨a :: l, u, r⟩)
          (2 + (2 * r.length + 2) + 2 * (l.reverse.length + 1)) =
        (.sh q' (.symbol a) true,
          [true, z] ++ pairs0 (z :: r) ++ [true, false] ++ pairs0 l.reverse) := by
    rw [XCTM.runT_add, hseam]
    simpa [xslot, xmarker, xsymbol, List.append_assoc] using
      xrun_shift_to_last M q' .seam true l.reverse a ([true, z] ++ pairs0 (z :: r))
  have hend :
      (xctmOf M).runT (xencC q ⟨a :: l, u, r⟩)
          (2 + (2 * r.length + 2) + 2 * (l.reverse.length + 1) + 2) =
        (.gPending q',
          pairs0 (z :: r) ++ [true, false] ++ pairs0 l.reverse ++ [true, a]) := by
    rw [XCTM.runT_add, hlast, XCTM.runT_two]
    simp [XCTM.stepT, XCTM.step?, CTM.stepT, xctmOf, List.append_assoc]
  rw [show 4 * tlen ⟨a :: l, u, r⟩ + 4 =
      (2 + (2 * r.length + 2) + 2 * (l.reverse.length + 1) + 2) +
        (2 * (z :: r).length + 2 + 2 * l.reverse.length) by
          simp only [tlen, List.length_cons, List.length_reverse]; ring,
    XCTM.runT_add, hend]
  simpa [xencC, xencT, List.append_assoc] using
    xrun_seek_seam M q' (z :: r) l.reverse [true, a]

/-- Lemma X, left move beyond the visited interval: exactly `6L + 12` steps. -/
theorem xctm_step_left_extend {q q' : QM} {r : List Bool} {u z : Bool}
    (hδ : M.delta q u = some (z, .L, q')) :
    (xctmOf M).runT (xencC q ⟨[], u, r⟩)
        (6 * tlen ⟨[], u, r⟩ + 12) =
      xencC q' ⟨[], false, z :: r⟩ := by
  have hfirst :
      (xctmOf M).runT (xencC q ⟨[], u, r⟩) 2 =
        (.sh q' (.symbol z) false, pairs0 r ++ [true, false, true, z]) := by
    rw [XCTM.runT_two]
    simp [xencC, xencT, XCTM.stepT, XCTM.step?, CTM.stepT,
      xctmOf, hδ, pairs0_nil, List.append_assoc]
  have hseam :
      (xctmOf M).runT (xencC q ⟨[], u, r⟩)
          (2 + (2 * r.length + 2)) =
        (.sh q' .seam true, [true, z] ++ pairs0 (z :: r)) := by
    rw [XCTM.runT_add, hfirst]
    simpa [List.append_assoc] using xrun_shift_to_seam M q' z r [true, z]
  have hextend :
      (xctmOf M).runT (xencC q ⟨[], u, r⟩)
          (2 + (2 * r.length + 2) + 4) =
        (.qa q', pairs0 (z :: r) ++ [true, false, false, false]) := by
    rw [XCTM.runT_add, hseam, XCTM.runT_four]
    simp [XCTM.stepT, XCTM.step?, CTM.stepT, xctmOf, List.append_assoc]
  have hscan :
      (xctmOf M).runT (xencC q ⟨[], u, r⟩)
          (2 + (2 * r.length + 2) + 4 + 2 * (z :: r).length) =
        (.qa q', [true, false, false, false] ++ pairs0 (z :: r)) := by
    rw [XCTM.runT_add, hextend]
    simpa [XScan.state] using
      xrun_scan M .repairLeft q' (z :: r) [true, false, false, false]
  have hrepair :
      (xctmOf M).runT (xencC q ⟨[], u, r⟩)
          (2 + (2 * r.length + 2) + 4 + 2 * (z :: r).length + 4) =
        (.gPending q', pairs0 (z :: r) ++ [true, false, true, false]) := by
    rw [XCTM.runT_add, hscan, XCTM.runT_four]
    simp [XCTM.stepT, XCTM.step?, CTM.stepT, xctmOf, List.append_assoc]
  rw [show 6 * tlen ⟨[], u, r⟩ + 12 =
      (2 + (2 * r.length + 2) + 4 + 2 * (z :: r).length + 4) +
        (2 * (z :: r).length + 2 + 2 * ([] : List Bool).length) by
          simp only [tlen, List.length_cons, List.length_nil]; ring,
    XCTM.runT_add, hrepair]
  simpa [xencC, xencT, pairs0_nil, List.append_assoc] using
    xrun_seek_seam M q' (z :: r) [] [true, false]



/-! ## Visited intervals and exact macro costs -/

/-- A new represented TM cell is allocated exactly at an interval endpoint.
Cells already in the initially padded tape do not count as new cells. -/
def tmNewCells (c : TM.Cfg QM Bool) : ℕ :=
  match M.delta c.state c.tape.head with
  | none => 0
  | some (_, .L, _) =>
      match c.tape.left with
      | [] => 1
      | _ :: _ => 0
  | some (_, .R, _) =>
      match c.tape.right with
      | [] => 1
      | _ :: _ => 0

theorem tmNewCells_le_one (c : TM.Cfg QM Bool) :
    tmNewCells M c ≤ 1 := by
  rcases c with ⟨q, ⟨l, u, r⟩⟩
  cases hδ : M.delta q u with
  | none => simp [tmNewCells, hδ]
  | some step =>
      rcases step with ⟨z, d, q'⟩
      cases d <;> cases l <;> cases r <;> simp [tmNewCells, hδ]

theorem tmStep_tlen (c : TM.Cfg QM Bool) :
    tlen ((M.step? c).getD c).tape = tlen c.tape + tmNewCells M c := by
  rcases c with ⟨q, ⟨l, u, r⟩⟩
  cases hδ : M.delta q u with
  | none =>
      simp [TM.Machine.step?, TM.Tape.read, tmNewCells, hδ]
  | some step =>
      rcases step with ⟨z, d, q'⟩
      cases d <;> cases l <;> cases r <;>
        simp [TM.Machine.step?, TM.Tape.read, TM.Tape.write,
          TM.Tape.move, tmNewCells, hδ, tlen] <;> omega

/-- Number of newly allocated TM cells up to a canonical boundary. -/
def tmExtensionCount (c : TM.Cfg QM Bool) : ℕ → ℕ
  | 0 => 0
  | t + 1 => tmExtensionCount c t + tmNewCells M (tmRun M c t)

theorem tlen_tmRun (c : TM.Cfg QM Bool) (t : ℕ) :
    tlen (tmRun M c t).tape = tlen c.tape + tmExtensionCount M c t := by
  induction t with
  | zero => simp [tmRun, tmExtensionCount]
  | succ t ih =>
      change tlen ((M.step? (tmRun M c t)).getD (tmRun M c t)).tape =
        tlen c.tape + tmExtensionCount M c (t + 1)
      rw [tmStep_tlen, ih, tmExtensionCount]
      omega

theorem tmExtensionCount_le (c : TM.Cfg QM Bool) (t : ℕ) :
    tmExtensionCount M c t ≤ t := by
  induction t with
  | zero => simp [tmExtensionCount]
  | succ t ih =>
      have h := tmNewCells_le_one M (tmRun M c t)
      simp only [tmExtensionCount]
      omega

theorem tlen_tmRun_mono (c : TM.Cfg QM Bool) :
    Monotone (fun t => tlen (tmRun M c t).tape) := by
  apply monotone_nat_of_le_succ
  intro t
  change tlen (tmRun M c t).tape ≤
    tlen ((M.step? (tmRun M c t)).getD (tmRun M c t)).tape
  rw [tmStep_tlen]
  omega

/-- Exact costs from Section 12.4. A halted TM contributes no further macro:
its canonical boundary stays fixed, and the xCTM halts two microsteps later. -/
def xStepCost (c : TM.Cfg QM Bool) : ℕ :=
  match M.delta c.state c.tape.head with
  | none => 0
  | some (_, .R, _) =>
      match c.tape.right with
      | [] => 4 * tlen c.tape + 10
      | _ :: _ => 2 * tlen c.tape + 4
  | some (_, .L, _) =>
      match c.tape.left with
      | [] => 6 * tlen c.tape + 12
      | _ :: _ => 4 * tlen c.tape + 4

/-- The number N_t of xCTM microsteps to the t-th canonical TM boundary. -/
def xTime (c : TM.Cfg QM Bool) : ℕ → ℕ
  | 0 => 0
  | t + 1 => xTime c t + xStepCost M (tmRun M c t)

theorem xStepCost_pos (c : TM.Cfg QM Bool)
    (ha : M.delta c.state c.tape.head ≠ none) :
    1 ≤ xStepCost M c := by
  rcases c with ⟨q, ⟨l, u, r⟩⟩
  cases hδ : M.delta q u with
  | none => simp [hδ] at ha
  | some step =>
      rcases step with ⟨z, d, q'⟩
      cases d <;> cases l <;> cases r <;>
        simp [xStepCost, hδ, tlen] <;> omega

/-- The extension surcharge is charged at the space after the step. -/
theorem xStepCost_le (c : TM.Cfg QM Bool) {s : ℕ}
    (hs : tlen ((M.step? c).getD c).tape ≤ s) :
    xStepCost M c ≤ (4 * s + 4) + (2 * s + 2) * tmNewCells M c := by
  rcases c with ⟨q, ⟨l, u, r⟩⟩
  cases hδ : M.delta q u with
  | none => simp [xStepCost, tmNewCells, hδ]
  | some step =>
      rcases step with ⟨z, d, q'⟩
      cases d <;> cases l <;> cases r <;>
        simp [TM.Machine.step?, TM.Tape.read, TM.Tape.write,
          TM.Tape.move, xStepCost, tmNewCells, hδ, tlen] at hs ⊢ <;> omega

private theorem xTime_le_of_space (c : TM.Cfg QM Bool) (t s : ℕ)
    (hsp : ∀ k ≤ t, tlen (tmRun M c k).tape ≤ s) :
    xTime M c t ≤
      (4 * s + 4) * t + (2 * s + 2) * tmExtensionCount M c t := by
  revert hsp
  induction t with
  | zero =>
      intro hsp
      simp [xTime, tmExtensionCount]
  | succ t ih =>
      intro hsp
      have hprev := ih (fun k hk => hsp k (by omega))
      have hstep := xStepCost_le M (tmRun M c t) (s := s)
        (by simpa only [tmRun] using hsp (t + 1) le_rfl)
      simp only [xTime, tmExtensionCount]
      calc
        xTime M c t + xStepCost M (tmRun M c t) ≤
            ((4 * s + 4) * t + (2 * s + 2) * tmExtensionCount M c t) +
              ((4 * s + 4) + (2 * s + 2) * tmNewCells M (tmRun M c t)) :=
          Nat.add_le_add hprev hstep
        _ = (4 * s + 4) * (t + 1) +
            (2 * s + 2) *
              (tmExtensionCount M c t + tmNewCells M (tmRun M c t)) := by ring

/-- Section 12.4(d), including the exact extension surcharge. -/
theorem xTime_le (c : TM.Cfg QM Bool) (t : ℕ) :
    xTime M c t ≤
      (4 * tlen (tmRun M c t).tape + 4) * t +
        (2 * tlen (tmRun M c t).tape + 2) * tmExtensionCount M c t := by
  exact xTime_le_of_space M c t _ (fun k hk => tlen_tmRun_mono M c hk)

/-- Section 12.4(d), with the final visited interval as the space parameter. -/
theorem xTime_le_linear (c : TM.Cfg QM Bool) (t : ℕ) :
    xTime M c t ≤ (6 * tlen (tmRun M c t).tape + 6) * t := by
  have h := xTime_le M c t
  have he := Nat.mul_le_mul_left (2 * tlen (tmRun M c t).tape + 2)
    (tmExtensionCount_le M c t)
  calc
    xTime M c t ≤
        (4 * tlen (tmRun M c t).tape + 4) * t +
          (2 * tlen (tmRun M c t).tape + 2) * t := by omega
    _ = (6 * tlen (tmRun M c t).tape + 6) * t := by ring

theorem le_xTime_of_active (c : TM.Cfg QM Bool) (t : ℕ)
    (ha : ∀ k < t,
      M.delta (tmRun M c k).state (tmRun M c k).tape.head ≠ none) :
    t ≤ xTime M c t := by
  revert ha
  induction t with
  | zero =>
      intro ha
      simp [xTime]
  | succ t ih =>
      intro ha
      have hp := ih (fun k hk => ha k (by omega))
      have hs := xStepCost_pos M (tmRun M c t) (ha t (by omega))
      simp only [xTime]
      omega


/-! ## Absolute visited intervals (Section 12.1) -/

/-- The absolute head update of one TM step; a halted TM stays put. -/
def tmHeadStep (c : TM.Cfg QM Bool) (h : ℤ) : ℤ :=
  match M.delta c.state c.tape.head with
  | none => h
  | some (_, .L, _) => h - 1
  | some (_, .R, _) => h + 1

/-- Absolute head position, with arbitrary initial coordinate `h`. -/
def tmHeadPosition (c : TM.Cfg QM Bool) (h : ℤ) : ℕ → ℤ
  | 0 => h
  | t + 1 => tmHeadStep M (tmRun M c t) (tmHeadPosition c h t)

/-- The left endpoint represented by a relative tape zipper. -/
def tmIntervalLow (h : ℤ) (T : TM.Tape Bool) : ℤ :=
  h - (T.left.length : ℤ)

/-- The right endpoint represented by a relative tape zipper. -/
def tmIntervalHigh (h : ℤ) (T : TM.Tape Bool) : ℤ :=
  h + (T.right.length : ℤ)

theorem tmIntervalLow_le_head (h : ℤ) (T : TM.Tape Bool) :
    tmIntervalLow h T ≤ h := by
  simp only [tmIntervalLow]
  omega

theorem head_le_tmIntervalHigh (h : ℤ) (T : TM.Tape Bool) :
    h ≤ tmIntervalHigh h T := by
  simp only [tmIntervalHigh]
  omega

theorem tmIntervalLow_le_high (h : ℤ) (T : TM.Tape Bool) :
    tmIntervalLow h T ≤ tmIntervalHigh h T :=
  (tmIntervalLow_le_head h T).trans (head_le_tmIntervalHigh h T)

/-- The represented interval has exactly the number of cells in the zipper. -/
theorem tmInterval_length (h : ℤ) (T : TM.Tape Bool) :
    tmIntervalHigh h T - tmIntervalLow h T + 1 = (tlen T : ℤ) := by
  simp only [tmIntervalLow, tmIntervalHigh, tlen, Nat.cast_add, Nat.cast_one]
  omega

/-- One TM step adjoins its new head position to the represented interval. -/
theorem tmIntervalLow_step (c : TM.Cfg QM Bool) (h : ℤ) :
    tmIntervalLow (tmHeadStep M c h) ((M.step? c).getD c).tape =
      min (tmIntervalLow h c.tape) (tmHeadStep M c h) := by
  rcases c with ⟨q, ⟨l, u, r⟩⟩
  cases hδ : M.delta q u with
  | none =>
      simp [TM.Machine.step?, TM.Tape.read, tmHeadStep, tmIntervalLow,
        hδ, min_def] <;> (try split_ifs) <;> omega
  | some transition =>
      rcases transition with ⟨z, d, q'⟩
      cases d <;> cases l <;> cases r <;>
        simp [TM.Machine.step?, TM.Tape.read, TM.Tape.write, TM.Tape.move,
          tmHeadStep, tmIntervalLow, hδ, min_def] <;> (try split_ifs) <;> omega

theorem tmIntervalHigh_step (c : TM.Cfg QM Bool) (h : ℤ) :
    tmIntervalHigh (tmHeadStep M c h) ((M.step? c).getD c).tape =
      max (tmIntervalHigh h c.tape) (tmHeadStep M c h) := by
  rcases c with ⟨q, ⟨l, u, r⟩⟩
  cases hδ : M.delta q u with
  | none =>
      simp [TM.Machine.step?, TM.Tape.read, tmHeadStep, tmIntervalHigh,
        hδ, max_def] <;> (try split_ifs) <;> omega
  | some transition =>
      rcases transition with ⟨z, d, q'⟩
      cases d <;> cases l <;> cases r <;>
        simp [TM.Machine.step?, TM.Tape.read, TM.Tape.write, TM.Tape.move,
          tmHeadStep, tmIntervalHigh, hδ, max_def] <;> (try split_ifs) <;> omega

/-- Allocation is equivalent to visiting a position outside the current interval. -/
theorem tmNewCells_eq_one_iff_head_outside (c : TM.Cfg QM Bool) (h : ℤ) :
    tmNewCells M c = 1 ↔
      tmHeadStep M c h ∉ Set.Icc (tmIntervalLow h c.tape) (tmIntervalHigh h c.tape) := by
  rcases c with ⟨q, ⟨l, u, r⟩⟩
  cases hδ : M.delta q u with
  | none =>
      simp [tmNewCells, tmHeadStep, tmIntervalLow, tmIntervalHigh,
        Set.mem_Icc, hδ] <;> omega
  | some transition =>
      rcases transition with ⟨z, d, q'⟩
      cases d <;> cases l <;> cases r <;>
        simp [tmNewCells, tmHeadStep, tmIntervalLow, tmIntervalHigh,
          Set.mem_Icc, hδ] <;> omega

def tmVisitedLow (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) : ℤ :=
  tmIntervalLow (tmHeadPosition M c h t) (tmRun M c t).tape

def tmVisitedHigh (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) : ℤ :=
  tmIntervalHigh (tmHeadPosition M c h t) (tmRun M c t).tape

/-- The absolute interval represented after `t` TM steps. -/
def tmVisitedInterval (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) : Set ℤ :=
  Set.Icc (tmVisitedLow M c h t) (tmVisitedHigh M c h t)

theorem tmHeadPosition_succ_of_halt
    (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ)
    (hδ : M.delta (tmRun M c t).state (tmRun M c t).tape.head = none) :
    tmHeadPosition M c h (t + 1) = tmHeadPosition M c h t := by
  simp [tmHeadPosition, tmHeadStep, hδ]

theorem tmHeadPosition_succ_of_left
    (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) {z : Bool} {q : QM}
    (hδ : M.delta (tmRun M c t).state (tmRun M c t).tape.head = some (z, .L, q)) :
    tmHeadPosition M c h (t + 1) = tmHeadPosition M c h t - 1 := by
  simp [tmHeadPosition, tmHeadStep, hδ]

theorem tmHeadPosition_succ_of_right
    (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) {z : Bool} {q : QM}
    (hδ : M.delta (tmRun M c t).state (tmRun M c t).tape.head = some (z, .R, q)) :
    tmHeadPosition M c h (t + 1) = tmHeadPosition M c h t + 1 := by
  simp [tmHeadPosition, tmHeadStep, hδ]

theorem tmVisitedLow_zero (c : TM.Cfg QM Bool) (h : ℤ) :
    tmVisitedLow M c h 0 = tmIntervalLow h c.tape := rfl

theorem tmVisitedHigh_zero (c : TM.Cfg QM Bool) (h : ℤ) :
    tmVisitedHigh M c h 0 = tmIntervalHigh h c.tape := rfl

theorem tmVisitedLow_succ (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) :
    tmVisitedLow M c h (t + 1) =
      min (tmVisitedLow M c h t) (tmHeadPosition M c h (t + 1)) := by
  simpa only [tmVisitedLow, tmHeadPosition, tmRun] using
    tmIntervalLow_step M (tmRun M c t) (tmHeadPosition M c h t)

theorem tmVisitedHigh_succ (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) :
    tmVisitedHigh M c h (t + 1) =
      max (tmVisitedHigh M c h t) (tmHeadPosition M c h (t + 1)) := by
  simpa only [tmVisitedHigh, tmHeadPosition, tmRun] using
    tmIntervalHigh_step M (tmRun M c t) (tmHeadPosition M c h t)

theorem tmVisitedLow_le_initial (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) :
    tmVisitedLow M c h t ≤ tmIntervalLow h c.tape := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
      rw [tmVisitedLow_succ]
      exact (min_le_left _ _).trans ih

theorem initial_le_tmVisitedHigh (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) :
    tmIntervalHigh h c.tape ≤ tmVisitedHigh M c h t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
      rw [tmVisitedHigh_succ]
      exact ih.trans (le_max_left _ _)

theorem tmVisitedLow_le_head (c : TM.Cfg QM Bool) (h : ℤ) {k t : ℕ} (hkt : k ≤ t) :
    tmVisitedLow M c h t ≤ tmHeadPosition M c h k := by
  induction t generalizing k with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      exact tmIntervalLow_le_head h c.tape
  | succ t ih =>
      by_cases hk : k = t + 1
      · subst k
        exact tmIntervalLow_le_head (tmHeadPosition M c h (t + 1))
          (tmRun M c (t + 1)).tape
      · rw [tmVisitedLow_succ]
        exact (min_le_left _ _).trans (ih (k := k) (by omega))

theorem head_le_tmVisitedHigh (c : TM.Cfg QM Bool) (h : ℤ) {k t : ℕ} (hkt : k ≤ t) :
    tmHeadPosition M c h k ≤ tmVisitedHigh M c h t := by
  induction t generalizing k with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      exact head_le_tmIntervalHigh h c.tape
  | succ t ih =>
      by_cases hk : k = t + 1
      · subst k
        exact head_le_tmIntervalHigh (tmHeadPosition M c h (t + 1))
          (tmRun M c (t + 1)).tape
      · rw [tmVisitedHigh_succ]
        exact (ih (k := k) (by omega)).trans (le_max_left _ _)

theorem tmVisitedInterval_contains_initial (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) :
    Set.Icc (tmIntervalLow h c.tape) (tmIntervalHigh h c.tape) ⊆
      tmVisitedInterval M c h t := by
  intro x hx
  exact ⟨(tmVisitedLow_le_initial M c h t).trans hx.1,
    hx.2.trans (initial_le_tmVisitedHigh M c h t)⟩

theorem tmVisitedInterval_contains_head
    (c : TM.Cfg QM Bool) (h : ℤ) {k t : ℕ} (hkt : k ≤ t) :
    tmHeadPosition M c h k ∈ tmVisitedInterval M c h t :=
  ⟨tmVisitedLow_le_head M c h hkt, head_le_tmVisitedHigh M c h hkt⟩

/-- Any interval containing the initial interval and every head position also
contains both represented endpoints. -/
theorem tmVisited_endpoints_minimal
    (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) (a b : ℤ)
    (hinitial : a ≤ tmIntervalLow h c.tape ∧ tmIntervalHigh h c.tape ≤ b)
    (hheads : ∀ k ≤ t,
      a ≤ tmHeadPosition M c h k ∧ tmHeadPosition M c h k ≤ b) :
    a ≤ tmVisitedLow M c h t ∧ tmVisitedHigh M c h t ≤ b := by
  revert hheads
  induction t with
  | zero =>
      intro hheads
      exact hinitial
  | succ t ih =>
      intro hheads
      have hp := ih (fun k hk => hheads k (by omega))
      have hn := hheads (t + 1) le_rfl
      rw [tmVisitedLow_succ, tmVisitedHigh_succ]
      exact ⟨le_min hp.1 hn.1, max_le hp.2 hn.2⟩

/-- The represented interval is the smallest integer interval containing
the initially allocated cells and every head position through time `t`. -/
theorem tmVisitedInterval_minimal
    (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) (a b : ℤ)
    (hinitial : Set.Icc (tmIntervalLow h c.tape) (tmIntervalHigh h c.tape) ⊆
      Set.Icc a b)
    (hheads : ∀ k ≤ t, tmHeadPosition M c h k ∈ Set.Icc a b) :
    tmVisitedInterval M c h t ⊆ Set.Icc a b := by
  have hlo := hinitial ⟨le_rfl, tmIntervalLow_le_high h c.tape⟩
  have hhi := hinitial ⟨tmIntervalLow_le_high h c.tape, le_rfl⟩
  have hb := tmVisited_endpoints_minimal M c h t a b ⟨hlo.1, hhi.2⟩ hheads
  intro x hx
  exact ⟨hb.1.trans hx.1, hx.2.trans hb.2⟩

theorem tmVisited_interval_length (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) :
    tmVisitedHigh M c h t - tmVisitedLow M c h t + 1 =
      (tlen (tmRun M c t).tape : ℤ) :=
  tmInterval_length (tmHeadPosition M c h t) (tmRun M c t).tape

theorem tmVisited_interval_length_nat (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) :
    (tmVisitedHigh M c h t - tmVisitedLow M c h t + 1).toNat =
      tlen (tmRun M c t).tape := by
  rw [tmVisited_interval_length]
  simp

theorem tmNewCells_at_run_iff_head_outside
    (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) :
    tmNewCells M (tmRun M c t) = 1 ↔
      tmHeadPosition M c h (t + 1) ∉ tmVisitedInterval M c h t := by
  simpa only [tmHeadPosition, tmVisitedInterval, tmVisitedLow, tmVisitedHigh] using
    tmNewCells_eq_one_iff_head_outside M (tmRun M c t) (tmHeadPosition M c h t)

/-- The count of new visits is the growth of the literal integer interval. -/
theorem tmExtensionCount_eq_interval_growth
    (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) :
    tmExtensionCount M c t =
      (tmVisitedHigh M c h t - tmVisitedLow M c h t + 1).toNat - tlen c.tape := by
  rw [tmVisited_interval_length_nat, tlen_tmRun]
  omega

theorem xInputTape_interval_low (s : ℕ) (input : List Bool) :
    tmIntervalLow 1 (xInputTape s input) = 1 := by
  simp [tmIntervalLow, xInputTape]

theorem xInputTape_interval_high (s : ℕ) (input : List Bool)
    (hs : 1 ≤ s) (hi : input.length ≤ s) :
    tmIntervalHigh 1 (xInputTape s input) = (s : ℤ) := by
  have ht := xInputTape_tlen s input hs hi
  simp only [tlen, xInputTape, List.length_nil] at ht
  simp only [tmIntervalHigh, xInputTape]
  omega

/-- The prescribed initial tape represents exactly `[1,s]`. -/
theorem xInputTape_interval (s : ℕ) (input : List Bool)
    (hs : 1 ≤ s) (hi : input.length ≤ s) :
    Set.Icc (tmIntervalLow 1 (xInputTape s input))
        (tmIntervalHigh 1 (xInputTape s input)) =
      Set.Icc (1 : ℤ) (s : ℤ) := by
  rw [xInputTape_interval_low, xInputTape_interval_high s input hs hi]


/-! ## Canonical boundaries, physical extensions, space, and halting -/

/-- The four concrete macro theorems assembled into one TM-step simulation. -/
theorem xctm_step (hb : M.blank = false) (c : TM.Cfg QM Bool) :
    (xctmOf M).runT (xencC c.state c.tape) (xStepCost M c) =
      xencC ((M.step? c).getD c).state ((M.step? c).getD c).tape := by
  rcases c with ⟨q, ⟨l, u, r⟩⟩
  cases hδ : M.delta q u with
  | none =>
      simp [xStepCost, TM.Machine.step?, TM.Tape.read, hδ, XCTM.runT]
  | some step =>
      rcases step with ⟨z, d, q'⟩
      cases d with
      | L =>
          cases l with
          | nil =>
              simpa [xStepCost, TM.Machine.step?, TM.Tape.read, TM.Tape.write,
                TM.Tape.move, hb, hδ] using
                (xctm_step_left_extend M (r := r) hδ)
          | cons a l =>
              simpa [xStepCost, TM.Machine.step?, TM.Tape.read, TM.Tape.write,
                TM.Tape.move, hb, hδ] using
                (xctm_step_left M (l := l) (r := r) (a := a) hδ)
      | R =>
          cases r with
          | nil =>
              simpa [xStepCost, TM.Machine.step?, TM.Tape.read, TM.Tape.write,
                TM.Tape.move, hb, hδ] using
                (xctm_step_right_extend M (l := l) hδ)
          | cons a r =>
              simpa [xStepCost, TM.Machine.step?, TM.Tape.read, TM.Tape.write,
                TM.Tape.move, hb, hδ] using
                (xctm_step_right M (l := l) (r := r) (a := a) hδ)

/-- Lemma X(a): exact run-level tracking at all canonical boundaries. -/
theorem xctm_tracks (hb : M.blank = false) (c : TM.Cfg QM Bool) (t : ℕ) :
    (xctmOf M).runT (xencC c.state c.tape) (xTime M c t) =
      xencC (tmRun M c t).state (tmRun M c t).tape := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [xTime, XCTM.runT_add, ih]
      exact xctm_step M hb (tmRun M c t)

/-- Precisely two physical extension operations for each new TM cell,
and none for a step that stays in the represented interval. -/
theorem xctm_step_extension_count (hb : M.blank = false) (c : TM.Cfg QM Bool) :
    (xctmOf M).extensionCount (xencC c.state c.tape) (xStepCost M c) =
      2 * tmNewCells M c := by
  have hl := XCTM.runT_length (xctmOf M) (xencC c.state c.tape) (xStepCost M c)
  rw [xctm_step M hb c] at hl
  change (xencT ((M.step? c).getD c).tape).length =
    (xencT c.tape).length +
      (xctmOf M).extensionCount (xencC c.state c.tape) (xStepCost M c) at hl
  rw [xencT_length, xencT_length, tmStep_tlen] at hl
  omega

theorem xctm_extension_count (hb : M.blank = false) (c : TM.Cfg QM Bool) (t : ℕ) :
    (xctmOf M).extensionCount (xencC c.state c.tape) (xTime M c t) =
      2 * tmExtensionCount M c t := by
  have hl := XCTM.runT_length (xctmOf M) (xencC c.state c.tape) (xTime M c t)
  rw [xctm_tracks M hb c t] at hl
  change (xencT (tmRun M c t).tape).length =
    (xencT c.tape).length +
      (xctmOf M).extensionCount (xencC c.state c.tape) (xTime M c t) at hl
  rw [xencT_length, xencT_length, tlen_tmRun] at hl
  omega

/-- Lemma X(b): exact tape length at a canonical boundary. -/
theorem xctm_canonical_length (hb : M.blank = false) (c : TM.Cfg QM Bool) (t : ℕ) :
    ((xctmOf M).runT (xencC c.state c.tape) (xTime M c t)).2.length =
      2 * tlen (tmRun M c t).tape + 2 := by
  rw [xctm_tracks M hb c t]
  exact xencT_length _

/-- Lemma X(b): the same final-space bound holds between boundaries. -/
theorem xctm_space_bound (hb : M.blank = false) (c : TM.Cfg QM Bool)
    (t : ℕ) {k : ℕ} (hk : k ≤ xTime M c t) :
    ((xctmOf M).runT (xencC c.state c.tape) k).2.length ≤
      2 * tlen (tmRun M c t).tape + 2 := by
  calc
    ((xctmOf M).runT (xencC c.state c.tape) k).2.length ≤
        ((xctmOf M).runT (xencC c.state c.tape) (xTime M c t)).2.length :=
      XCTM.runT_length_mono (xctmOf M) (xencC c.state c.tape) hk
    _ = 2 * tlen (tmRun M c t).tape + 2 :=
      xctm_canonical_length M hb c t

/-- No halting state can occur at or before a canonical boundary. -/
theorem xctm_no_halt_before_boundary (hb : M.blank = false) (c : TM.Cfg QM Bool)
    (t : ℕ) {k : ℕ} (hk : k ≤ xTime M c t) :
    (xctmOf M).mode ((xctmOf M).runT (xencC c.state c.tape) k).1 ≠ .halt := by
  intro hh
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
  have hr :
      (xctmOf M).runT (xencC c.state c.tape) (xTime M c t) =
        (xctmOf M).runT (xencC c.state c.tape) k := by
    rw [hd, XCTM.runT_add]
    exact XCTM.runT_of_halt (xctmOf M) _ hh d
  have hh' :
      (xctmOf M).mode
        ((xctmOf M).runT (xencC c.state c.tape) (xTime M c t)).1 = .halt := by
    rw [hr]
    exact hh
  rw [xctm_tracks M hb c t] at hh'
  change (XCTMMode.read : XCTMMode (XCS QM)) = .halt at hh'
  cases hh'

/-- The first header-reading microstep is also nonhalting. -/
theorem xctm_no_halt_before_two (hb : M.blank = false) (c : TM.Cfg QM Bool)
    (t : ℕ) {k : ℕ} (hk : k < xTime M c t + 2) :
    (xctmOf M).mode ((xctmOf M).runT (xencC c.state c.tape) k).1 ≠ .halt := by
  by_cases hle : k ≤ xTime M c t
  · exact xctm_no_halt_before_boundary M hb c t hle
  · have he : k = xTime M c t + 1 := by omega
    rw [he, XCTM.runT_add, xctm_tracks M hb c t]
    simp [XCTM.runT, XCTM.stepT, XCTM.step?, CTM.stepT, xctmOf, xencC, xencT]

/-- Lemma X(c): a halted TM is recognized two microsteps after its boundary.
The tape is its canonical tape rotated by one marker/symbol slot. -/
theorem xctm_halt_at (hb : M.blank = false) (c : TM.Cfg QM Bool) (t : ℕ)
    (hδ : M.delta (tmRun M c t).state (tmRun M c t).tape.head = none) :
    (xctmOf M).runT (xencC c.state c.tape) (xTime M c t + 2) =
      (.halt (tmRun M c t).state,
        pairs0 (tmRun M c t).tape.right ++ [true, false] ++
          pairs0 (tmRun M c t).tape.left.reverse ++
            [true, (tmRun M c t).tape.head]) := by
  rw [XCTM.runT_add, xctm_tracks M hb c t]
  simpa only [List.append_assoc] using (xctmOf_halt_after_two M _ _ hδ)

/-- Lemma X(c), stated using the actual partial transition functions. -/
theorem xctm_halts_iff (hb : M.blank = false) (c : TM.Cfg QM Bool) :
    (∃ k, (xctmOf M).step? ((xctmOf M).runT (xencC c.state c.tape) k) = none) ↔
      ∃ t, M.step? (tmRun M c t) = none := by
  classical
  constructor
  · rintro ⟨k, hk⟩
    by_contra hn
    have ha : ∀ i,
        M.delta (tmRun M c i).state (tmRun M c i).tape.head ≠ none := by
      intro i hδ
      apply hn
      exact ⟨i, by simp [TM.Machine.step?, TM.Tape.read, hδ]⟩
    have ht := le_xTime_of_active M c k (fun i _ => ha i)
    have hnh := xctm_no_halt_before_boundary M hb c k ht
    have hw :
        ((xctmOf M).runT (xencC c.state c.tape) k).2 ≠ [] :=
      XCTM.runT_ne_nil (xctmOf M) (xencC c.state c.tape) (xencT_ne_nil c.tape) k
    exact hnh ((XCTM.step?_eq_none_iff (xctmOf M) _ hw).mp hk)
  · rintro ⟨t, ht⟩
    have hδ : M.delta (tmRun M c t).state (tmRun M c t).tape.head = none := by
      cases hd : M.delta (tmRun M c t).state (tmRun M c t).tape.head with
      | none => rfl
      | some step =>
          rcases step with ⟨z, d, q'⟩
          simp [TM.Machine.step?, TM.Tape.read, hd] at ht
    refine ⟨xTime M c t + 2, ?_⟩
    rw [xctm_halt_at M hb c t hδ]
    rfl

/-- The specified input, padded over the initial interval [1,s]. -/
def xInputCfg (s : ℕ) (input : List Bool) : TM.Cfg QM Bool :=
  ⟨M.start, xInputTape s input⟩

/-- Lemma X with the input convention of Section 12.1. Together with
xctm_no_halt_before_two and xctm_halts_iff, this gives the run-level corollary. -/
theorem xctm_input_run (hb : M.blank = false) (s : ℕ) (input : List Bool)
    (hs : 1 ≤ s) (hi : input.length ≤ s) (t : ℕ) :
    let c := xInputCfg M s input
    (xctmOf M).runT (xencC c.state c.tape) (xTime M c t) =
        xencC (tmRun M c t).state (tmRun M c t).tape ∧
      tlen (tmRun M c t).tape = s + tmExtensionCount M c t ∧
      tmExtensionCount M c t ≤ t ∧
      (xctmOf M).extensionCount (xencC c.state c.tape) (xTime M c t) =
        2 * tmExtensionCount M c t ∧
      (∀ k ≤ xTime M c t,
        ((xctmOf M).runT (xencC c.state c.tape) k).2.length ≤
          2 * tlen (tmRun M c t).tape + 2) ∧
      xTime M c t ≤
        (4 * tlen (tmRun M c t).tape + 4) * t +
          (2 * tlen (tmRun M c t).tape + 2) * tmExtensionCount M c t ∧
      xTime M c t ≤ (6 * tlen (tmRun M c t).tape + 6) * t := by
  dsimp only
  refine ⟨xctm_tracks M hb _ t, ?_, tmExtensionCount_le M _ t,
    xctm_extension_count M hb _ t,
    fun k hk => xctm_space_bound M hb _ t hk, xTime_le M _ t,
    xTime_le_linear M _ t⟩
  rw [tlen_tmRun]
  change tlen (xInputTape s input) + _ = s + _
  rw [xInputTape_tlen s input hs hi]


open Classical in
/-- Physical extensions in the next actual macro occur precisely when its
new head position leaves the previously visited integer interval. -/
theorem xctm_next_macro_extensions (hb : M.blank = false)
    (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) :
    (xctmOf M).extensionCount
        ((xctmOf M).runT (xencC c.state c.tape) (xTime M c t))
        (xStepCost M (tmRun M c t)) =
      if tmHeadPosition M c h (t + 1) ∉ tmVisitedInterval M c h t
      then 2 else 0 := by
  classical
  rw [xctm_tracks M hb c t, xctm_step_extension_count M hb]
  have hnew := tmNewCells_at_run_iff_head_outside M c h t
  have hle := tmNewCells_le_one M (tmRun M c t)
  by_cases ho : tmHeadPosition M c h (t + 1) ∉ tmVisitedInterval M c h t
  · simp [ho, hnew.mpr ho]
  · have hn : tmNewCells M (tmRun M c t) ≠ 1 := fun hn => ho (hnew.mp hn)
    have hz : tmNewCells M (tmRun M c t) = 0 := by omega
    simp [ho, hz]

/-- The space bound expressed using the literal visited-interval length. -/
theorem xctm_space_bound_interval (hb : M.blank = false)
    (c : TM.Cfg QM Bool) (h : ℤ) (t : ℕ) {k : ℕ} (hk : k ≤ xTime M c t) :
    ((xctmOf M).runT (xencC c.state c.tape) k).2.length ≤
      2 * (tmVisitedHigh M c h t - tmVisitedLow M c h t + 1).toNat + 2 := by
  rw [tmVisited_interval_length_nat]
  exact xctm_space_bound M hb c t hk

/-!
The code below witnesses only the loss of absolute integer origin in the
literal reading of §12.4(e). The repository TM configurations are relative
tapes; the simulated relative configurations in this example are equal.
-/

namespace AbsoluteOriginWitness

inductive Control
  | start
  | returnRight
  | halt
  deriving DecidableEq, Fintype

def machine : TM.Machine Control Bool where
  start := .start
  blank := false
  delta
    | .start, false => some (false, .R, .halt)
    | .start, true => some (false, .L, .returnRight)
    | .returnRight, _ => some (false, .R, .halt)
    | .halt, _ => none

def input (a : Bool) : TM.Cfg Control Bool :=
  ⟨.start, ⟨[], a, []⟩⟩

/-- Absolute TM head coordinate, initially at integer cell 1. -/
def position (a : Bool) : ℕ → ℤ
  | 0 => 1
  | t + 1 =>
      position a t +
        match machine.delta (tmRun machine (input a) t).state
            (tmRun machine (input a) t).tape.head with
        | none => 0
        | some (_, .L, _) => -1
        | some (_, .R, _) => 1

/-- Two inputs of length at most one to the same machine have equal final
canonical xCTM codes, but different absolute head coordinates. Their visited
intervals, including the initial cell, are [1,2] and [0,1]. -/
theorem same_code_different_origin :
    (tmRun machine (input false) 1).state = Control.halt ∧
    (tmRun machine (input true) 2).state = Control.halt ∧
    xencT (tmRun machine (input false) 1).tape =
      xencT (tmRun machine (input true) 2).tape ∧
    [position false 0, position false 1] = ([1, 2] : List ℤ) ∧
    [position true 0, position true 1, position true 2] = ([1, 0, 1] : List ℤ) ∧
    position false 1 ≠ position true 2 := by
  decide +kernel

end AbsoluteOriginWitness

end Ripple.sCRNUniversality.ClockedCTM
