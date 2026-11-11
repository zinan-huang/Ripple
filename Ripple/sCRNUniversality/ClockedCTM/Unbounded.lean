import Mathlib
import Ripple.sCRNUniversality.ClockedCTM.ExtensibleCTM
import Ripple.sCRNUniversality.CTMCBridge

/-!
Layer two of FIX3-SCWB-T41. The stochastic headlines below are propositions,
not proved probability or running-time results.
-/
namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded

open Stochastic Stochastic.MassAction
open MeasureTheory
open scoped ENNReal BigOperators

variable {Q : Type} [Fintype Q] [DecidableEq Q]

abbrev ReadState (C : XCTM Q) := {q : Q // C.mode q = .read}
abbrev ExtendState (C : XCTM Q) := {q : Q // ∃ q', C.mode q = .extend q'}
abbrev ActiveState (C : XCTM Q) := ReadState C ⊕ ExtendState C

private instance readStateDecidablePred (C : XCTM Q) :
    DecidablePred (fun q : Q => C.mode q = .read) :=
  fun q =>
    match hm : C.mode q with
    | .read => isTrue hm
    | .extend _ => isFalse (fun h => by cases hm.symm.trans h)
    | .halt => isFalse (fun h => by cases hm.symm.trans h)

private instance extendStateDecidablePred (C : XCTM Q) :
    DecidablePred (fun q : Q => ∃ q', C.mode q = .extend q') :=
  fun q =>
    match hm : C.mode q with
    | .read => isFalse (fun h => by
        obtain ⟨q', hq'⟩ := h
        cases hm.symm.trans hq')
    | .extend q' => isTrue ⟨q', hm⟩
    | .halt => isFalse (fun h => by
        obtain ⟨q', hq'⟩ := h
        cases hm.symm.trans hq')

def activeControl (C : XCTM Q) : ActiveState C → Q
  | .inl q => q.val
  | .inr e => e.val

def extensionNext (C : XCTM Q) (e : ExtendState C) : Q :=
  match C.mode e.val with
  | .extend q' => q'
  | _ => e.val

theorem mode_extensionNext (C : XCTM Q) (e : ExtendState C) :
    C.mode e.val = .extend (extensionNext C e) := by
  obtain ⟨q', hq'⟩ := e.property
  simp [extensionNext, hq']

theorem activeControl_injective (C : XCTM Q) :
    Function.Injective (activeControl C) := by
  intro a b h
  cases a with
  | inl q =>
    cases b with
    | inl r =>
      have he : q = r := Subtype.ext h
      cases he
      rfl
    | inr e =>
      change q.val = e.val at h
      have hr := q.property
      rw [h] at hr
      have he := mode_extensionNext C e
      rw [hr] at he
      cases he
  | inr e =>
    cases b with
    | inl q =>
      change e.val = q.val at h
      have he := mode_extensionNext C e
      rw [h, q.property] at he
      cases he
    | inr f =>
      have he : e = f := Subtype.ext h
      cases he
      rfl

@[simp] theorem activeControl_eq_iff (C : XCTM Q) (a b : ActiveState C) :
    activeControl C a = activeControl C b ↔ a = b :=
  (activeControl_injective C).eq_iff

/-- Exactly the species of §3.1. -/
inductive Sp (C : XCTM Q) where
  | first (q : Q)
  | second (a : ActiveState C)
  | third (a : ActiveState C)
  | reader (q : ReadState C)
  | write (q : ReadState C) (b : Bool)
  | extend (e : ExtendState C)
  | signal
  | clock (c : Fin 5)
  | forward
  | forwardLatent
  | backward
  | backwardLatent
  | mem (m : Mem)
  deriving DecidableEq, Fintype

set_option synthInstance.maxSize 512 in
/-- Clock Boolean: false is the ordinary catalyst, true the latent catalyst. -/
inductive Rx (C : XCTM Q) where
  | tick (latent : Bool)
  | up (c : Fin 4) (latent : Bool)
  | down (c : Fin 4) (latent : Bool)
  | startSecond (a : ActiveState C)
  | growSecond (a : ActiveState C)
  | startThird (a : ActiveState C)
  | growThird (a : ActiveState C)
  | startRead (q : ReadState C)
  | chooseRead (q : ReadState C) (b : Bool)
  | growWrite (q : ReadState C) (b : Bool)
  | finishWrite (q : ReadState C) (b : Bool)
  | growFirstFromWrite (q : ReadState C) (b : Bool)
  | startExtension (e : ExtendState C)
  | growExtension (e : ExtendState C)
  | finishExtension (e : ExtendState C)
  | growFirstFromExtension (e : ExtendState C)
  | restoreM (a : ActiveState C)
  | restoreT (a : ActiveState C)
  | restoreD (a : ActiveState C)
  | restoreB (a : ActiveState C)
  | restoreForward (a : ActiveState C)
  | restoreBackward (a : ActiveState C)
  | pair
  | consumeDouble
  | consumeSingle
  | readRestoreM (q : ReadState C) (b : Bool)
  | readRestoreTs (q : ReadState C) (b : Bool)
  | readRestoreT (q : ReadState C) (b : Bool)
  | readShift (q : ReadState C) (b : Bool)
  | readZero (q : ReadState C) (b : Bool)
  | readWrite (q : ReadState C) (b : Bool)
  | extendRestoreM (e : ExtendState C)
  | extendShift (e : ExtendState C)
  | extendWrite (e : ExtendState C)
  | extendRestoreTs (e : ExtendState C)
  | extendRestoreT (e : ExtendState C)
  | extendD (e : ExtendState C)
  | extendForward (e : ExtendState C)
  | extendBackward (e : ExtendState C)
  deriving DecidableEq, Fintype

def isTick {C : XCTM Q} : Rx C → Bool
  | .tick _ => true
  | _ => false

def IsTick {C : XCTM Q} (r : Rx C) : Prop := isTick r = true

def isClock {C : XCTM Q} : Rx C → Bool
  | .tick _ | .up _ _ | .down _ _ => true
  | _ => false

/-- The existing one-molecule gadget on the enlarged species type. -/
def unit {C : XCTM Q} (s : Sp C) : Complex (Sp C) :=
  fun s' => if s' = s then 1 else 0

@[simp] theorem unit_apply {C : XCTM Q} (s s' : Sp C) :
    unit s s' = if s' = s then 1 else 0 := rfl

def bimolecular {C : XCTM Q} (s t : Sp C) (out : Complex (Sp C)) :
    Reaction (Sp C) :=
  { l := unit s + unit t, r := out, k := 1 }

def sourceLeft (C : XCTM Q) : Rx C → Sp C
  | .tick _ => .clock 0
  | .up c _ => .clock c.castSucc
  | .down c _ => .clock c.succ
  | .startSecond _ => .signal
  | .growSecond a => .first (activeControl C a)
  | .startThird _ => .signal
  | .growThird a => .second a
  | .startRead _ => .signal
  | .chooseRead q _ => .reader q
  | .growWrite q _ => .third (.inl q)
  | .finishWrite _ _ => .signal
  | .growFirstFromWrite q b => .write q b
  | .startExtension _ => .signal
  | .growExtension e => .third (.inr e)
  | .finishExtension _ => .signal
  | .growFirstFromExtension e => .extend e
  | .restoreM a => .second a
  | .restoreT a => .second a
  | .restoreD a => .second a
  | .restoreB a => .second a
  | .restoreForward a => .second a
  | .restoreBackward a => .second a
  | .pair => .mem .t
  | .consumeDouble => .mem .k2
  | .consumeSingle => .mem .k1
  | .readRestoreM q b => .write q b
  | .readRestoreTs q b => .write q b
  | .readRestoreT q b => .write q b
  | .readShift q b => .write q b
  | .readZero q b => .write q b
  | .readWrite q b => .write q b
  | .extendRestoreM e => .extend e
  | .extendShift e => .extend e
  | .extendWrite e => .extend e
  | .extendRestoreTs e => .extend e
  | .extendRestoreT e => .extend e
  | .extendD e => .extend e
  | .extendForward e => .extend e
  | .extendBackward e => .extend e

def sourceRight (C : XCTM Q) : Rx C → Sp C
  | .tick latent => if latent then .backwardLatent else .backward
  | .up _ latent => if latent then .forwardLatent else .forward
  | .down _ latent => if latent then .backwardLatent else .backward
  | .startSecond a => .first (activeControl C a)
  | .growSecond a => .second a
  | .startThird a => .second a
  | .growThird a => .third a
  | .startRead q => .third (.inl q)
  | .chooseRead _ b => .mem (if b then .m else .t)
  | .growWrite q b => .write q b
  | .finishWrite q b => .write q b
  | .growFirstFromWrite q b => .first (C.next q.val b).1
  | .startExtension e => .third (.inr e)
  | .growExtension e => .extend e
  | .finishExtension e => .extend e
  | .growFirstFromExtension e => .first (extensionNext C e)
  | .restoreM _ => .mem .md
  | .restoreT _ => .mem .td
  | .restoreD _ => .mem .ds
  | .restoreB _ => .mem .bs
  | .restoreForward _ => .forwardLatent
  | .restoreBackward _ => .backwardLatent
  | .pair => .mem .m
  | .consumeDouble => .mem .md
  | .consumeSingle => .mem .md
  | .readRestoreM _ _ => .mem .ms
  | .readRestoreTs _ _ => .mem .ts
  | .readRestoreT _ _ => .mem .t
  | .readShift _ _ => .mem .m
  | .readZero _ _ => .mem .d
  | .readWrite _ _ => .mem .b
  | .extendRestoreM _ => .mem .ms
  | .extendShift _ => .mem .m
  | .extendWrite _ => .mem .b
  | .extendRestoreTs _ => .mem .ts
  | .extendRestoreT _ => .mem .t
  | .extendD _ => .mem .d
  | .extendForward _ => .forward
  | .extendBackward _ => .backward

def products (C : XCTM Q) : Rx C → Complex (Sp C)
  | .tick latent =>
      unit (.clock (Fin.last 4)) + unit .signal +
        unit (if latent then .backwardLatent else .backward)
  | .up c latent =>
      unit (.clock c.succ) + unit (if latent then .forwardLatent else .forward)
  | .down c latent =>
      unit (.clock c.castSucc) + unit (if latent then .backwardLatent else .backward)
  | .startSecond a => unit (.second a)
  | .growSecond a => 2 • unit (.second a)
  | .startThird a => unit (.third a)
  | .growThird a => 2 • unit (.third a)
  | .startRead q => unit (.reader q)
  | .chooseRead q b => unit (.write q b) + unit (.mem (if b then .m else .t))
  | .growWrite q b => 2 • unit (.write q b)
  | .finishWrite q b => unit (.first (C.next q.val b).1)
  | .growFirstFromWrite q b => 2 • unit (.first (C.next q.val b).1)
  | .startExtension e => 3 • unit (.extend e)
  | .growExtension e => 4 • unit (.extend e)
  | .finishExtension e => unit (.first (extensionNext C e))
  | .growFirstFromExtension e => 2 • unit (.first (extensionNext C e))
  | .restoreM a => unit (.second a) + unit (.mem .m)
  | .restoreT a => unit (.second a) + unit (.mem .t)
  | .restoreD a => unit (.second a) + unit (.mem .d) + unit .forward
  | .restoreB a => unit (.second a) + unit (.mem .b)
  | .restoreForward a => unit (.second a) + 3 • unit .forward
  | .restoreBackward a => unit (.second a) + 3 • unit .backward
  | .pair => unit (.mem .ts) + unit (.mem .ms)
  | .consumeDouble => unit (.mem .k1)
  | .consumeSingle => 0
  | .readRestoreM q b => unit (.write q b) + unit (.mem .m)
  | .readRestoreTs q b => unit (.write q b) + unit (.mem .td)
  | .readRestoreT q b => unit (.write q b) + unit (.mem .td)
  | .readShift q b => unit (.write q b) + 3 • unit (.mem .md)
  | .readZero q b =>
      unit (.write q b) + 3 • unit (.mem (if b then .k2 else .k1)) + unit (.mem .ds)
  | .readWrite q b =>
      unit (.write q b) + ((C.next q.val b).2.toNat + 1) • unit (.mem .md) +
        unit (.mem .bs)
  | .extendRestoreM e => unit (.extend e) + unit (.mem .m)
  | .extendShift e => unit (.extend e) + 3 • unit (.mem .md)
  | .extendWrite e => unit (.extend e) + unit (.mem .md) + unit (.mem .bs)
  | .extendRestoreTs e => unit (.extend e) + 3 • unit (.mem .td)
  | .extendRestoreT e => unit (.extend e) + 3 • unit (.mem .td)
  | .extendD e => unit (.extend e) + 3 • unit (.mem .ds)
  | .extendForward e => unit (.extend e) + unit .forwardLatent
  | .extendBackward e => unit (.extend e) + unit .backwardLatent

def rxn (C : XCTM Q) (r : Rx C) : Reaction (Sp C) :=
  bimolecular (sourceLeft C r) (sourceRight C r) (products C r)

/-- The finite network depends on C alone. -/
def net (C : XCTM Q) : Network (Sp C) where
  I := Rx C
  rxn := rxn C

theorem net_hasPositiveRates (C : XCTM Q) : (net C).hasPositiveRates := by
  intro r
  show (0 : Rate) < 1
  exact zero_lt_one

instance (C : XCTM Q) : DecidableEq (net C).I := by
  change DecidableEq (Rx C)
  infer_instance

@[simp] theorem rxn_l (C : XCTM Q) (r : Rx C) :
    (rxn C r).l = unit (sourceLeft C r) + unit (sourceRight C r) := rfl

@[simp] theorem rxn_r (C : XCTM Q) (r : Rx C) :
    (rxn C r).r = products C r := rfl

theorem source_distinct (C : XCTM Q) (r : Rx C) :
    sourceLeft C r ≠ sourceRight C r := by
  cases r with
  | tick latent => cases latent <;> simp [sourceLeft, sourceRight]
  | up c latent => cases latent <;> simp [sourceLeft, sourceRight]
  | down c latent => cases latent <;> simp [sourceLeft, sourceRight]
  | _ => simp [sourceLeft, sourceRight]

def rate (C : XCTM Q) (r : Rx C) (z : State (Sp C)) : ℕ :=
  z (sourceLeft C r) * z (sourceRight C r)

theorem propensity_rxn (C : XCTM Q) (r : Rx C) (z : State (Sp C)) :
    (rxn C r).propensity z =
      ((z (sourceLeft C r) * z (sourceRight C r) : ℕ) : Rate) := by
  have h := source_distinct C r
  unfold Reaction.propensity rxn bimolecular
  simp only [one_mul]
  rw [Finset.prod_eq_mul_of_mem
    (sourceLeft C r) (sourceRight C r)
    (Finset.mem_univ _) (Finset.mem_univ _) h]
  · simp [h, h.symm, Nat.cast_mul]
  · intro s _ hs
    simp [hs.1, hs.2]

theorem enabled_iff (C : XCTM Q) (r : Rx C) (z : State (Sp C)) :
    (rxn C r).enabled z ↔ rate C r z ≠ 0 := by
  have h := source_distinct C r
  constructor
  · intro hen
    have hl := hen (sourceLeft C r)
    have hr := hen (sourceRight C r)
    simp only [rxn, bimolecular, Pi.add_apply, unit_apply,
      if_true, h, h.symm, if_false] at hl hr
    simp only [rate, ne_eq, mul_eq_zero, not_or]
    omega
  · intro hr s
    simp only [rate, ne_eq, mul_eq_zero, not_or] at hr
    simp only [rxn, bimolecular, Pi.add_apply, unit_apply]
    by_cases hl : s = sourceLeft C r
    · subst hl
      simp [h]
      omega
    · by_cases hs : s = sourceRight C r
      · subst hs
        simp [hl]
        omega
      · simp [hl, hs]

theorem fire_apply (C : XCTM Q) (r : Rx C) (z : State (Sp C)) (s : Sp C) :
    (rxn C r).fire z s =
      z s -
        ((if s = sourceLeft C r then 1 else 0) +
         (if s = sourceRight C r then 1 else 0)) +
      products C r s := rfl

def stateCount (s : ℕ) : ℕ := 3 ^ (s - 1)
def threshold (s : ℕ) : ℕ := 2 * 3 ^ (s - 1) + 2 * 3 ^ (s - 3)

/-- §4: only the initial configuration carries the input and accuracy. -/
def initial (C : XCTM Q) (i₀ : ℕ) (w : List Bool) : State (Sp C)
  | .first q => if q = C.start then stateCount w.length else 0
  | .mem .md => tval w
  | .mem .td => threshold w.length
  | .mem .ds => stateCount w.length
  | .mem .bs => 1
  | .forward => i₀ * stateCount w.length
  | .backward => stateCount w.length
  | .clock c => if c = Fin.last 4 then 1 else 0
  | _ => 0

@[simp] theorem initial_first (C : XCTM Q) (i₀ : ℕ) (w : List Bool) :
    initial C i₀ w (.first C.start) = stateCount w.length := by simp [initial]

@[simp] theorem initial_memory (C : XCTM Q) (i₀ : ℕ) (w : List Bool) :
    initial C i₀ w (.mem .md) = tval w := rfl

@[simp] theorem initial_forward (C : XCTM Q) (i₀ : ℕ) (w : List Bool) :
    initial C i₀ w .forward = i₀ * stateCount w.length := rfl

@[simp] theorem initial_backward (C : XCTM Q) (i₀ : ℕ) (w : List Bool) :
    initial C i₀ w .backward = stateCount w.length := rfl

theorem initial_accuracy_only_forward (C : XCTM Q) (i j : ℕ)
    (w : List Bool) (s : Sp C) (hs : s ≠ .forward) :
    initial C i w s = initial C j w s := by
  cases s with
  | mem m => cases m <;> simp_all [initial]
  | _ => simp_all [initial]

theorem initial_input_only_memory (C : XCTM Q) (i₀ : ℕ)
    (w v : List Bool) (hlen : w.length = v.length)
    (s : Sp C) (hs : s ≠ .mem .md) :
    initial C i₀ w s = initial C i₀ v s := by
  cases s with
  | mem m => cases m <;> simp_all [initial]
  | _ => simp_all [initial]

def tmNetwork {QM : Type} [Fintype QM] [DecidableEq QM]
    (M : TM.Machine QM Bool) : Network (Sp (xctmOf M)) := net (xctmOf M)

def tmInitial {QM : Type} [Fintype QM] [DecidableEq QM]
    (M : TM.Machine QM Bool) (s i₀ : ℕ) (input : List Bool) :
    State (Sp (xctmOf M)) :=
  initial (xctmOf M) i₀ (xencT (xInputTape s input))


/-! ## Work dynamics and support -/

def Sp.IsControl {C : XCTM Q} : Sp C → Prop
  | .first _ | .second _ | .third _ | .reader _ | .write _ _ | .extend _ | .signal => True
  | _ => False

def OnlyControl (C : XCTM Q) (l : List (Sp C)) (z : State (Sp C)) : Prop :=
  ∀ s, s.IsControl → s ∉ l → z s = 0

theorem OnlyControl.fire {C : XCTM Q} {l : List (Sp C)} {z : State (Sp C)}
    (h : OnlyControl C l z) (r : Rx C)
    (hout : ∀ s, s.IsControl → s ∉ l → products C r s = 0) :
    OnlyControl C l ((rxn C r).fire z) := by
  intro s hs hn
  rw [fire_apply, h s hs hn, hout s hs hn]
  simp

theorem enabled_control_support (C : XCTM Q) {l : List (Sp C)}
    {z : State (Sp C)} {r : Rx C} (h : OnlyControl C l z)
    (hen : (rxn C r).enabled z) :
    ((sourceLeft C r).IsControl → sourceLeft C r ∈ l) ∧
    ((sourceRight C r).IsControl → sourceRight C r ∈ l) := by
  have hr := (enabled_iff C r z).mp hen
  have hp : z (sourceLeft C r) ≠ 0 ∧ z (sourceRight C r) ≠ 0 := by
    simpa only [rate, ne_eq, mul_eq_zero, not_or] using hr
  constructor
  · intro hs
    by_contra hn
    exact hp.1 (h _ hs hn)
  · intro hs
    by_contra hn
    exact hp.2 (h _ hs hn)

def WorkTerminal (C : XCTM Q) (z : State (Sp C)) : Prop :=
  ∀ r : Rx C, isClock r = false → ¬ (rxn C r).enabled z

theorem workTerminal_iff (C : XCTM Q) (z : State (Sp C)) :
    WorkTerminal C z ↔ ∀ r : Rx C, isClock r = false → rate C r z = 0 := by
  classical
  simp only [WorkTerminal, enabled_iff, not_not]

def WorkStep (C : XCTM Q) (x y : State (Sp C)) : Prop :=
  ∃ r : Rx C, isClock r = false ∧ (rxn C r).enabled x ∧ y = (rxn C r).fire x

def ReachBy (C : XCTM Q) (allowed : Rx C → Prop) :
    State (Sp C) → State (Sp C) → Prop :=
  Relation.ReflTransGen
    (fun x y => ∃ r : Rx C, allowed r ∧ (rxn C r).enabled x ∧ y = (rxn C r).fire x)

abbrev WorkReach (C : XCTM Q) := ReachBy C (fun r => isClock r = false)

theorem workReach_invariant (C : XCTM Q) (Inv : State (Sp C) → Prop)
    (hclosed : ∀ x y, Inv x → WorkStep C x y → Inv y)
    {x y : State (Sp C)} (h : WorkReach C x y) (hx : Inv x) : Inv y := by
  induction h with
  | refl => exact hx
  | tail hxy hyz ih => exact hclosed _ _ ih hyz

/-- A decreasing natural rank gives an actual finite terminal work trace. -/
theorem work_reaches_terminal (C : XCTM Q) (Inv : State (Sp C) → Prop)
    (rank : State (Sp C) → ℕ)
    (hclosed : ∀ x y, Inv x → WorkStep C x y → Inv y)
    (hdrop : ∀ x y, Inv x → WorkStep C x y → rank y < rank x)
    {x : State (Sp C)} (hx : Inv x) :
    ∃ y, WorkReach C x y ∧ Inv y ∧ WorkTerminal C y := by
  classical
  have aux : ∀ m : ℕ, ∀ x : State (Sp C), rank x = m → Inv x →
      ∃ y, WorkReach C x y ∧ Inv y ∧ WorkTerminal C y := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hm hx
      by_cases ht : WorkTerminal C x
      · exact ⟨x, .refl, hx, ht⟩
      · have he : ∃ r : Rx C, isClock r = false ∧ (rxn C r).enabled x := by
          by_contra hnone
          apply ht
          intro r hr hen
          exact hnone ⟨r, hr, hen⟩
        obtain ⟨r, hr, hen⟩ := he
        let y := (rxn C r).fire x
        have hxy : WorkStep C x y := ⟨r, hr, hen, rfl⟩
        have hy := hclosed x y hx hxy
        have hlt : rank y < m := by simpa only [hm] using hdrop x y hx hxy
        obtain ⟨z, hyz, hz, ht⟩ := ih (rank y) hlt y rfl hy
        have hreach : WorkReach C x y := .tail .refl hxy
        exact ⟨z, hreach.trans hyz, hz, ht⟩
  exact aux (rank x) x rfl hx

/-- Every run of actual work firings is finite: no fairness assumption. -/
theorem no_infinite_work_run (C : XCTM Q) (Inv : State (Sp C) → Prop)
    (rank : State (Sp C) → ℕ)
    (hclosed : ∀ x y, Inv x → WorkStep C x y → Inv y)
    (hdrop : ∀ x y, Inv x → WorkStep C x y → rank y < rank x)
    (z : ℕ → State (Sp C)) (hz : Inv (z 0)) :
    ¬ ∀ n, WorkStep C (z n) (z (n + 1)) := by
  intro hs
  have hi : ∀ n, Inv (z n) := by
    intro n
    induction n with
    | zero => exact hz
    | succ n ih => exact hclosed _ _ ih (hs n)
  have hb : ∀ n, rank (z n) + n ≤ rank (z 0) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have hd := hdrop _ _ (hi n) (hs n)
      omega
  have hf := hb (rank (z 0) + 1)
  omega

def workView (C : XCTM Q) (z : State (Sp C)) : State (Sp C)
  | .clock _ => 0
  | s => z s

theorem initial_terminal (C : XCTM Q) (i₀ : ℕ) (w : List Bool) :
    WorkTerminal C (initial C i₀ w) := by
  rw [workTerminal_iff]
  intro r hr
  cases r <;> simp_all [isClock, rate, sourceLeft, sourceRight, initial]


/-! ## Tape and parameter arithmetic -/

theorem stateCount_eq (s : ℕ) (hs : 3 ≤ s) :
    stateCount s = 9 * 3 ^ (s - 3) := by
  have he : s - 1 = (s - 3) + 2 := by omega
  simp only [stateCount, he, pow_add]
  norm_num <;> ring

theorem threshold_eq (s : ℕ) (hs : 3 ≤ s) :
    threshold s = 20 * 3 ^ (s - 3) := by
  change 2 * stateCount s + 2 * 3 ^ (s - 3) = _
  rw [stateCount_eq s hs]
  ring

theorem stateCount_succ (s : ℕ) (hs : 1 ≤ s) :
    stateCount (s + 1) = 3 * stateCount s := by
  have he : s = (s - 1) + 1 := by omega
  simp only [stateCount, Nat.add_sub_cancel]
  conv_lhs => rw [he, pow_succ]
  ring

theorem threshold_succ (s : ℕ) (hs : 3 ≤ s) :
    threshold (s + 1) = 3 * threshold s := by
  rw [threshold_eq (s + 1) (by omega), threshold_eq s hs]
  rw [show s + 1 - 3 = (s - 3) + 1 by omega, pow_succ]
  ring

theorem stateCount_div_exact (s : ℕ) (hs : 3 ≤ s) :
    3 * (stateCount s / 3) = stateCount s := by
  rw [stateCount_eq s hs]
  omega

theorem extension_value (w : List Bool) :
    tval (w ++ [false]) = 3 * tval w + 1 := by
  simpa only [bw] using tval_append w false

theorem read_value (w : List Bool) (hs : 3 ≤ w.length) (z : Bool) :
    tval (w.tail ++ [z]) + 3 * bw (w.headD false) * stateCount w.length =
      3 * tval w + bw z := by
  have h := (tape_facts (n := w.length - 3) (w := w) (by omega) z).1
  rw [stateCount_eq w.length hs]
  exact h

theorem read_length (w : List Bool) (hs : 1 ≤ w.length) (z : Bool) :
    (w.tail ++ [z]).length = w.length := by
  simp only [List.length_append, List.length_tail, List.length_singleton]
  omega

theorem run_space_bound (C : XCTM Q) (c : Q × List Bool) (n : ℕ) :
    (C.runT c n).2.length ≤ c.2.length + n :=
  XCTM.runT_length_le C c n

theorem run_space_le_accuracy (C : XCTM Q) (c : Q × List Bool)
    (i₀ : ℕ) (h : c.2.length ≤ i₀) (n : ℕ) :
    (C.runT c n).2.length ≤ i₀ + n := by
  have hspace := run_space_bound C c n
  omega

theorem restore_counts_bound {a ad f fd ds alpha d : ℕ}
    (ha : a + 3 * ad + ds = (alpha + 1) * d)
    (hf : f + 3 * fd = d) (hd : ds ≤ d) :
    f + fd ≤ d ∧ alpha * (f + fd) ≤ 3 * (a + ad) := by
  have hb : f + fd ≤ d := by omega
  have ha' : alpha * d ≤ 3 * (a + ad) := by nlinarith
  constructor
  · exact hb
  · exact (Nat.mul_le_mul_left alpha hb).trans ha'

theorem ratio_bound {alpha a f : ℕ} (hf : 0 < f)
    (ha : alpha * f ≤ 3 * a) :
    (alpha : ℝ) / 3 ≤ (a : ℝ) / f := by
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have ha' : (alpha : ℝ) * f ≤ 3 * a := by exact_mod_cast ha
  exact (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hf').2 (by nlinarith)

def forwardCount (C : XCTM Q) (z : State (Sp C)) : ℕ :=
  z .forward + z .forwardLatent

def backwardCount (C : XCTM Q) (z : State (Sp C)) : ℕ :=
  z .backward + z .backwardLatent

def forwardWeight (C : XCTM Q) (z : State (Sp C)) : ℕ :=
  z .forward + 3 * z .forwardLatent

def backwardWeight (C : XCTM Q) (z : State (Sp C)) : ℕ :=
  z .backward + 3 * z .backwardLatent


/-! ## The explicit clean schedule -/

/-- First and fourth phases store starred memory. -/
def storedMemory (w : List Bool) : Mem → ℕ
  | .md => tval w
  | .td => threshold w.length
  | .ds => stateCount w.length
  | .bs => 1
  | _ => 0

/-- Fully restored and compared memory, at the ends of phases two and three. -/
def comparedMemory (w : List Bool) : Mem → ℕ
  | .m => tval w - min (tval w) (threshold w.length)
  | .ms => min (tval w) (threshold w.length)
  | .t => threshold w.length - min (tval w) (threshold w.length)
  | .ts => min (tval w) (threshold w.length)
  | .d => stateCount w.length
  | .b => 1
  | _ => 0

/-- A denotes the effective accuracy after the current restoration.
The fourth-phase tape is already the resulting tape. -/
inductive Plan (C : XCTM Q) where
  | first (q : Q) (w : List Bool) (a : ℕ) (latent : Bool)
  | second (q : ActiveState C) (w : List Bool) (a : ℕ)
  | third (q : ActiveState C) (w : List Bool) (a : ℕ)
  | write (q : ReadState C) (b : Bool) (w : List Bool) (a : ℕ)
  | extend (e : ExtendState C) (w : List Bool) (a : ℕ)

def Plan.tape {C : XCTM Q} : Plan C → List Bool
  | .first _ w _ _ | .second _ w _ | .third _ w _ | .write _ _ w _ | .extend _ w _ => w

/-- Decode U and X through their transitions; do not identify them with S-one. -/
def Plan.configuration (C : XCTM Q) : Plan C → Q × List Bool
  | .first q w _ _ => (q, w)
  | .second q w _ | .third q w _ => (activeControl C q, w)
  | .write q b w _ => ((C.next q.val b).1, w)
  | .extend e w _ => (extensionNext C e, w)

def Plan.halted (C : XCTM Q) : Plan C → Bool
  | .first q _ _ _ => match C.mode q with | .halt => true | _ => false
  | _ => false

def Plan.advance (C : XCTM Q) : Plan C → Plan C
  | .first q w a latent =>
    match h : C.mode q with
    | .read => .second (.inl ⟨q, h⟩) w (a + 1)
    | .extend q' => .second (.inr ⟨q, ⟨q', h⟩⟩) w (a + 1)
    | .halt => .first q w a latent
  | .second q w a => .third q w a
  | .third (.inl q) w a =>
      .write q (w.headD false) (w.tail ++ [(C.next q.val (w.headD false)).2]) a
  | .third (.inr e) w a => .extend e (w ++ [false]) a
  | .write q b w a => .first (C.next q.val b).1 w a false
  | .extend e w a => .first (extensionNext C e) w a true

private theorem Plan.advance_first_read (C : XCTM Q) (q : Q)
    (w : List Bool) (a : ℕ) (latent : Bool) (h : C.mode q = .read) :
    Plan.advance C (.first q w a latent) =
      .second (.inl ⟨q, h⟩) w (a + 1) := by
  dsimp only [Plan.advance]
  split <;> first
    | rfl
    | (exfalso; rename_i hh; rw [h] at hh; cases hh)
    | simp_all

private theorem Plan.advance_first_extend (C : XCTM Q) (q q' : Q)
    (w : List Bool) (a : ℕ) (latent : Bool) (h : C.mode q = .extend q') :
    Plan.advance C (.first q w a latent) =
      .second (.inr ⟨q, ⟨q', h⟩⟩) w (a + 1) := by
  dsimp only [Plan.advance]
  split <;> first
    | rfl
    | (exfalso; rename_i hh; rw [h] at hh; cases hh)
    | simp_all

def Plan.iterate (C : XCTM Q) (p : Plan C) : ℕ → Plan C
  | 0 => p
  | k + 1 => Plan.advance C (Plan.iterate C p k)

def plan (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (k : ℕ) : Plan C :=
  Plan.iterate C (.first C.start w i₀ false) k

/-- Exact state/clock-catalyst/memory counts; the five clock positions are erased.
The division by three occurs only in the post-extension representation. -/
def payload (C : XCTM Q) (controller : Sp C) (d a : ℕ)
    (latent : Bool) (memory : Mem → ℕ) : State (Sp C)
  | .mem m => memory m
  | .forward => if latent then 0 else a * d
  | .forwardLatent => if latent then a * (d / 3) else 0
  | .backward => if latent then 0 else d
  | .backwardLatent => if latent then d / 3 else 0
  | .clock _ => 0
  | s => if s = controller then d else 0

def Plan.workState (C : XCTM Q) : Plan C → State (Sp C)
  | .first q w a latent =>
      payload C (.first q) (stateCount w.length) a latent (storedMemory w)
  | .second q w a =>
      payload C (.second q) (stateCount w.length) a false (comparedMemory w)
  | .third q w a =>
      payload C (.third q) (stateCount w.length) a false (comparedMemory w)
  | .write q b w a =>
      payload C (.write q b) (stateCount w.length) a false (storedMemory w)
  | .extend e w a =>
      payload C (.extend e) (stateCount w.length) a true (storedMemory w)

def gamma (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (k : ℕ) : State (Sp C) :=
  Plan.workState C (plan C i₀ w k)

/-- Ignore I only in the genuinely halted first phase. -/
def cleanView (C : XCTM Q) (halted : Bool) (z : State (Sp C)) : State (Sp C)
  | .clock _ => 0
  | .signal => if halted then 0 else z .signal
  | s => z s

def Clean (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (k : ℕ)
    (z : State (Sp C)) : Prop :=
  cleanView C (Plan.halted C (plan C i₀ w k)) z = gamma C i₀ w k

theorem plan_succ (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (k : ℕ) :
    plan C i₀ w (k + 1) = Plan.advance C (plan C i₀ w k) := rfl

theorem Plan.iterate_add (C : XCTM Q) (p : Plan C) (k j : ℕ) :
    Plan.iterate C p (k + j) = Plan.iterate C (Plan.iterate C p k) j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg (Plan.advance C) ih

theorem Plan.advance_halt (C : XCTM Q) (q : Q) (w : List Bool)
    (a : ℕ) (latent : Bool) (h : C.mode q = .halt) :
    Plan.advance C (.first q w a latent) = .first q w a latent := by
  dsimp only [Plan.advance]
  split <;> simp_all

theorem Plan.iterate_halt (C : XCTM Q) (q : Q) (w : List Bool)
    (a : ℕ) (latent : Bool) (h : C.mode q = .halt) (k : ℕ) :
    Plan.iterate C (.first q w a latent) k = .first q w a latent := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Plan.iterate, ih, Plan.advance_halt C q w a latent h]

theorem Plan.advance_valid (C : XCTM Q) (p : Plan C)
    (h : 3 ≤ p.tape.length) :
    3 ≤ (Plan.advance C p).tape.length := by
  cases p with
  | first q w a latent =>
      cases hm : C.mode q with
      | read =>
          rw [Plan.advance_first_read C q w a latent hm]
          exact h
      | extend q' =>
          rw [Plan.advance_first_extend C q q' w a latent hm]
          exact h
      | halt =>
          rw [Plan.advance_halt C q w a latent hm]
          exact h
  | second q w a => exact h
  | third q w a =>
      cases q with
      | inl q =>
          simp only [Plan.advance, Plan.tape, List.length_append,
            List.length_tail, List.length_singleton]
          change 3 ≤ w.length at h
          omega
      | inr e =>
          simp only [Plan.advance, Plan.tape, List.length_append,
            List.length_singleton]
          change 3 ≤ w.length at h
          omega
  | write q b w a => exact h
  | extend e w a => exact h

theorem plan_valid (C : XCTM Q) (i₀ : ℕ) (w : List Bool)
    (h : 3 ≤ w.length) (k : ℕ) :
    3 ≤ (plan C i₀ w k).tape.length := by
  induction k with
  | zero => exact h
  | succ k ih => exact Plan.advance_valid C _ ih

theorem initial_clean (C : XCTM Q) (i₀ : ℕ) (w : List Bool) :
    Clean C i₀ w 0 (initial C i₀ w) := by
  unfold Clean gamma plan Plan.iterate
  funext s
  cases s with
  | mem m => cases m <;> rfl
  | _ => simp [cleanView, Plan.workState, payload, storedMemory, initial]

theorem comparison_zero_product (v t : ℕ) :
    (t - min v t) * (v - min v t) = 0 := by
  rcases le_total v t with h | h
  · simp [min_eq_left h]
  · simp [min_eq_right h]

/-- Every listed clean work configuration is terminal. -/
theorem Plan.workState_terminal (C : XCTM Q) (p : Plan C) :
    WorkTerminal C (Plan.workState C p) := by
  rw [workTerminal_iff]
  intro r hr
  cases p <;> cases r <;>
    simp_all [isClock, rate, sourceLeft, sourceRight, Plan.workState,
      payload, storedMemory, comparedMemory, comparison_zero_product]

/-- Halting freezes all specified work data; later ticks may add idle I. -/
theorem gamma_freezes (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (k : ℕ)
    (q : Q) (v : List Bool) (a : ℕ) (latent : Bool)
    (hp : plan C i₀ w k = .first q v a latent) (hh : C.mode q = .halt) (j : ℕ) :
    gamma C i₀ w (k + j) = gamma C i₀ w k := by
  unfold gamma plan at *
  rw [Plan.iterate_add, hp, Plan.iterate_halt C q v a latent hh j]


/-! ## Second window: restoration, comparison, delayed tripling -/

def RestoreLabel {C : XCTM Q} : Rx C → Prop
  | .startSecond _ | .growSecond _ | .restoreM _ | .restoreT _
    | .restoreD _ | .restoreB _ | .restoreForward _ | .restoreBackward _ | .pair => True
  | _ => False

def RestoreBudget (C : XCTM Q) (alpha d : ℕ) (z : State (Sp C)) : Prop :=
  forwardWeight C z + z (.mem .ds) = (alpha + 1) * d ∧
    backwardWeight C z = d ∧ z (.mem .ds) ≤ d

theorem restoreBudget_fire (C : XCTM Q) {alpha d : ℕ}
    {z : State (Sp C)} {r : Rx C}
    (hr : RestoreLabel r) (hen : (rxn C r).enabled z)
    (h : RestoreBudget C alpha d z) :
    RestoreBudget C alpha d ((rxn C r).fire z) := by
  have hp := (enabled_iff C r z).mp hen
  simp only [rate, ne_eq, mul_eq_zero, not_or] at hp
  cases r <;>
    simp_all [RestoreLabel, RestoreBudget, forwardWeight, backwardWeight,
      fire_apply, sourceLeft, sourceRight, products, unit] <;> omega

theorem restoreBudget_parameters (C : XCTM Q) {alpha d : ℕ}
    {z : State (Sp C)} (hd : 0 < d) (h : RestoreBudget C alpha d z) :
    0 < backwardCount C z ∧ backwardCount C z ≤ d ∧
      alpha * backwardCount C z ≤ 3 * forwardCount C z := by
  rcases h with ⟨ha, hf, hds⟩
  have hp : 0 < backwardCount C z := by
    dsimp [backwardWeight] at hf
    dsimp [backwardCount]
    omega
  have hh := restore_counts_bound ha hf hds
  exact ⟨hp, hh.1, hh.2⟩

def RestoreAt {C : XCTM Q} (a : ActiveState C) : Rx C → Prop
  | .startSecond b | .growSecond b | .restoreM b | .restoreT b
    | .restoreD b | .restoreB b | .restoreForward b | .restoreBackward b => b = a
  | .pair => True
  | _ => False

theorem restoreAt_label {C : XCTM Q} {a : ActiveState C} {r : Rx C}
    (h : RestoreAt a r) : RestoreLabel r := by
  cases r <;> simp_all [RestoreAt, RestoreLabel]

def RestoreWindow (C : XCTM Q) (a : ActiveState C)
    (d threshold value alpha : ℕ) (z : State (Sp C)) : Prop :=
  OnlyControl C [.first (activeControl C a), .second a, .signal] z ∧
    z (.first (activeControl C a)) + z (.second a) = d ∧
    z .signal ≤ 1 ∧ (z .signal = 1 ∨ 0 < z (.second a)) ∧
    (z .signal = 0 ∨ z (.second a) = 0) ∧
    MemA d threshold value (fun m => z (.mem m)) ∧
    RestoreBudget C alpha d z

theorem restore_enabled_at (C : XCTM Q) {a : ActiveState C}
    {d threshold value alpha : ℕ} {z : State (Sp C)} {r : Rx C}
    (h : RestoreWindow C a d threshold value alpha z)
    (hc : isClock r = false) (hen : (rxn C r).enabled z) : RestoreAt a r := by
  rcases h with ⟨ho, hst, hi, hseed, hex, hm, hb⟩
  rcases hm with ⟨hm, ht, hms, hd, hB, hk, hkk⟩
  have hp := (enabled_iff C r z).mp hen
  simp only [rate, ne_eq, mul_eq_zero, not_or] at hp
  have hsupport (s : Sp C) (hs : s.IsControl) (hn : z s ≠ 0) :
      s ∈ [.first (activeControl C a), .second a, .signal] := by
    by_contra hnot
    exact hn (ho s hs hnot)
  have hleft : (sourceLeft C r).IsControl →
      sourceLeft C r ∈ [.first (activeControl C a), .second a, .signal] :=
    fun hs => hsupport _ hs hp.1
  have hright : (sourceRight C r).IsControl →
      sourceRight C r ∈ [.first (activeControl C a), .second a, .signal] :=
    fun hs => hsupport _ hs hp.2
  cases r <;>
    simp_all [RestoreAt, isClock, sourceLeft, sourceRight, Sp.IsControl,
      activeControl_eq_iff]

/- Diagnosis of the old startSecond macro.

   Its first arithmetic goal after simplification was:
   ⊢ (z (.first (activeControl C a)) - 1) +
       (z (.second a) + 1) = d
   with hst : z (.first (activeControl C a)) + z (.second a) = d.
   Enabledness gives 1 ≤ z (.first (activeControl C a)), so this is valid.

   The first reported failure (old line 970) was the MemA goal:
   ⊢ z (.mem .m) + z (.mem .ms) + z (.mem .md) = value ∧
     z (.mem .t) + z (.mem .ts) + z (.mem .td) = threshold ∧
     z (.mem .ms) = z (.mem .ts) ∧
     z (.mem .d) + z (.mem .ds) = d ∧
     z (.mem .b) + z (.mem .bs) = 1 ∧
     z (.mem .k1) = 0 ∧ z (.mem .k2) = 0.

   For its first conjunct the corresponding hypothesis was:
   hm : (fun m => z (.mem m)) .m +
        (fun m => z (.mem m)) .ms +
        (fun m => z (.mem m)) .md = value.
   No memory coordinate changes in startSecond. The goal is therefore
   definitionally the original memory assertion. The supplied diagnostic
   nevertheless assigns separate omega atoms to the beta applications and
   to the literal state applications. The explicit changes below normalize
   all seven hypotheses before arithmetic reasoning.

   Later cases also need ordinary constructor simplification and pointwise
   reduction of products. RestoreWindow itself is unchanged. -/
private theorem restore_window_onlyControl_fire
    (C : XCTM Q) {a : ActiveState C}
    {z : State (Sp C)} {r : Rx C}
    (ho :
      OnlyControl C
        [.first (activeControl C a), .second a, .signal] z)
    (hr : RestoreAt a r) :
    OnlyControl C
      [.first (activeControl C a), .second a, .signal]
      ((rxn C r).fire z) := by
  apply OnlyControl.fire ho r
  intro s hs hn
  have hns : s ≠ .second a := by
    intro he
    apply hn
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inl he)
  have hnm (m : Mem) : s ≠ .mem m := by
    intro he
    subst s
    exact hs
  have hnf : s ≠ .forward := by
    intro he
    subst s
    exact hs
  have hnb : s ≠ .backward := by
    intro he
    subst s
    exact hs
  cases r <;>
    simp_all [RestoreAt, products, unit, nsmul_eq_mul,
      hns, hnm, hnf, hnb]

private theorem restore_window_memory_fire
    (C : XCTM Q) {d threshold value : ℕ}
    {z : State (Sp C)} {r : Rx C}
    (hr : RestoreLabel r)
    (hen : (rxn C r).enabled z)
    (hmem : MemA d threshold value (fun m => z (.mem m))) :
    MemA d threshold value
      (fun m => (rxn C r).fire z (.mem m)) := by
  rcases hmem with ⟨hm, ht, hms, hd, hB, hk1, hk2⟩
  change
    z (.mem .m) + z (.mem .ms) + z (.mem .md) = value
    at hm
  change
    z (.mem .t) + z (.mem .ts) + z (.mem .td) = threshold
    at ht
  change z (.mem .ms) = z (.mem .ts) at hms
  change z (.mem .d) + z (.mem .ds) = d at hd
  change z (.mem .b) + z (.mem .bs) = 1 at hB
  change z (.mem .k1) = 0 at hk1
  change z (.mem .k2) = 0 at hk2
  have hp := (enabled_iff C r z).mp hen
  simp only [rate, ne_eq, mul_eq_zero, not_or] at hp
  have hleft : 1 ≤ z (sourceLeft C r) := by
    omega
  have hright : 1 ≤ z (sourceRight C r) := by
    omega
  cases r <;>
    simp_all [RestoreLabel, MemA, fire_apply, sourceLeft,
      sourceRight, products, unit, nsmul_eq_mul] <;>
    omega

private theorem restore_window_fire_same_control
    (C : XCTM Q) {a : ActiveState C}
    {d threshold value alpha : ℕ}
    {z : State (Sp C)} {r : Rx C}
    (h : RestoreWindow C a d threshold value alpha z)
    (hr : RestoreAt a r)
    (hen : (rxn C r).enabled z)
    (hF :
      (rxn C r).fire z (.first (activeControl C a)) =
        z (.first (activeControl C a)))
    (hS :
      (rxn C r).fire z (.second a) = z (.second a))
    (hI :
      (rxn C r).fire z .signal = z .signal) :
    RestoreWindow C a d threshold value alpha
      ((rxn C r).fire z) := by
  rcases h with ⟨ho, hst, hi, hseed, hex, hm, hb⟩
  refine ⟨restore_window_onlyControl_fire C ho hr,
    ?_, ?_, ?_, ?_,
    restore_window_memory_fire C (restoreAt_label hr) hen hm,
    restoreBudget_fire C (restoreAt_label hr) hen hb⟩
  · simpa only [hF, hS] using hst
  · simpa only [hI] using hi
  · simpa only [hI, hS] using hseed
  · simpa only [hI, hS] using hex

section RestoreWindowFireCases

variable (C : XCTM Q) {a : ActiveState C}
    {d threshold value alpha : ℕ} {z : State (Sp C)}
    (h : RestoreWindow C a d threshold value alpha z)

include h

private theorem restore_window_fire_startSecond
    (hen : (rxn C (.startSecond a)).enabled z) :
    RestoreWindow C a d threshold value alpha
      ((rxn C (.startSecond a)).fire z) := by
  rcases h with ⟨ho, hst, hi, hseed, hex, hm, hb⟩
  have hp :
      z .signal ≠ 0 ∧
        z (.first (activeControl C a)) ≠ 0 := by
    simpa only [rate, sourceLeft, sourceRight, ne_eq,
      mul_eq_zero, not_or] using
      (enabled_iff C (.startSecond a) z).mp hen
  have hfirst : 1 ≤ z (.first (activeControl C a)) := by
    omega
  have hsignal : z .signal = 1 := by
    omega
  have hsecond : z (.second a) = 0 := by
    omega
  have hF :
      (rxn C (.startSecond a)).fire z
          (.first (activeControl C a)) =
        z (.first (activeControl C a)) - 1 := by
    simp [fire_apply, sourceLeft, sourceRight, products, unit]
  have hS :
      (rxn C (.startSecond a)).fire z (.second a) = 1 := by
    simp [fire_apply, sourceLeft, sourceRight, products,
      unit, hsecond]
  have hI :
      (rxn C (.startSecond a)).fire z .signal = 0 := by
    simp [fire_apply, sourceLeft, sourceRight, products,
      unit, hsignal]
  refine ⟨
    restore_window_onlyControl_fire C ho
      (show RestoreAt a (.startSecond a) by rfl),
    ?_, ?_, ?_, ?_,
    restore_window_memory_fire C
      (show RestoreLabel (.startSecond a) by trivial) hen hm,
    restoreBudget_fire C
      (show RestoreLabel (.startSecond a) by trivial) hen hb⟩
  · rw [hF, hS]
    omega
  · rw [hI]
    decide
  · right
    rw [hS]
    decide
  · exact Or.inl hI

private theorem restore_window_fire_growSecond
    (hen : (rxn C (.growSecond a)).enabled z) :
    RestoreWindow C a d threshold value alpha
      ((rxn C (.growSecond a)).fire z) := by
  rcases h with ⟨ho, hst, hi, hseed, hex, hm, hb⟩
  have hp :
      z (.first (activeControl C a)) ≠ 0 ∧
        z (.second a) ≠ 0 := by
    simpa only [rate, sourceLeft, sourceRight, ne_eq,
      mul_eq_zero, not_or] using
      (enabled_iff C (.growSecond a) z).mp hen
  have hfirst : 1 ≤ z (.first (activeControl C a)) := by
    omega
  have hsecond : 1 ≤ z (.second a) := by
    omega
  have hsignal : z .signal = 0 := by
    omega
  have hF :
      (rxn C (.growSecond a)).fire z
          (.first (activeControl C a)) =
        z (.first (activeControl C a)) - 1 := by
    simp [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul]
  have hS :
      (rxn C (.growSecond a)).fire z (.second a) =
        z (.second a) + 1 := by
    simp [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul] <;>
      omega
  have hI :
      (rxn C (.growSecond a)).fire z .signal = 0 := by
    simp [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul, hsignal]
  refine ⟨
    restore_window_onlyControl_fire C ho
      (show RestoreAt a (.growSecond a) by rfl),
    ?_, ?_, ?_, ?_,
    restore_window_memory_fire C
      (show RestoreLabel (.growSecond a) by trivial) hen hm,
    restoreBudget_fire C
      (show RestoreLabel (.growSecond a) by trivial) hen hb⟩
  · rw [hF, hS]
    omega
  · rw [hI]
    decide
  · right
    rw [hS]
    omega
  · exact Or.inl hI

private theorem restore_window_fire_restoreM
    (hen : (rxn C (.restoreM a)).enabled z) :
    RestoreWindow C a d threshold value alpha
      ((rxn C (.restoreM a)).fire z) := by
  have hsecond : 1 ≤ z (.second a) := by
    have hp := (enabled_iff C (.restoreM a) z).mp hen
    simp only [rate, sourceLeft, sourceRight, ne_eq,
      mul_eq_zero, not_or] at hp
    omega
  refine restore_window_fire_same_control C h
    (r := .restoreM a) (by rfl) hen ?_ ?_ ?_
  · simp [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul]
  · simpa [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul] using Nat.sub_add_cancel hsecond
  · simp [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul]

private theorem restore_window_fire_restoreT
    (hen : (rxn C (.restoreT a)).enabled z) :
    RestoreWindow C a d threshold value alpha
      ((rxn C (.restoreT a)).fire z) := by
  have hsecond : 1 ≤ z (.second a) := by
    have hp := (enabled_iff C (.restoreT a) z).mp hen
    simp only [rate, sourceLeft, sourceRight, ne_eq,
      mul_eq_zero, not_or] at hp
    omega
  refine restore_window_fire_same_control C h
    (r := .restoreT a) (by rfl) hen ?_ ?_ ?_
  · simp [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul]
  · simpa [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul] using Nat.sub_add_cancel hsecond
  · simp [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul]

private theorem restore_window_fire_restoreD
    (hen : (rxn C (.restoreD a)).enabled z) :
    RestoreWindow C a d threshold value alpha
      ((rxn C (.restoreD a)).fire z) := by
  have hsecond : 1 ≤ z (.second a) := by
    have hp := (enabled_iff C (.restoreD a) z).mp hen
    simp only [rate, sourceLeft, sourceRight, ne_eq,
      mul_eq_zero, not_or] at hp
    omega
  refine restore_window_fire_same_control C h
    (r := .restoreD a) (by rfl) hen ?_ ?_ ?_
  · simp [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul]
  · simpa [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul] using Nat.sub_add_cancel hsecond
  · simp [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul]

private theorem restore_window_fire_restoreB
    (hen : (rxn C (.restoreB a)).enabled z) :
    RestoreWindow C a d threshold value alpha
      ((rxn C (.restoreB a)).fire z) := by
  have hsecond : 1 ≤ z (.second a) := by
    have hp := (enabled_iff C (.restoreB a) z).mp hen
    simp only [rate, sourceLeft, sourceRight, ne_eq,
      mul_eq_zero, not_or] at hp
    omega
  refine restore_window_fire_same_control C h
    (r := .restoreB a) (by rfl) hen ?_ ?_ ?_
  · simp [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul]
  · simpa [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul] using Nat.sub_add_cancel hsecond
  · simp [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul]

private theorem restore_window_fire_restoreForward
    (hen : (rxn C (.restoreForward a)).enabled z) :
    RestoreWindow C a d threshold value alpha
      ((rxn C (.restoreForward a)).fire z) := by
  have hsecond : 1 ≤ z (.second a) := by
    have hp := (enabled_iff C (.restoreForward a) z).mp hen
    simp only [rate, sourceLeft, sourceRight, ne_eq,
      mul_eq_zero, not_or] at hp
    omega
  refine restore_window_fire_same_control C h
    (r := .restoreForward a) (by rfl) hen ?_ ?_ ?_
  · simp [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul]
  · simpa [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul] using Nat.sub_add_cancel hsecond
  · simp [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul]

private theorem restore_window_fire_restoreBackward
    (hen : (rxn C (.restoreBackward a)).enabled z) :
    RestoreWindow C a d threshold value alpha
      ((rxn C (.restoreBackward a)).fire z) := by
  have hsecond : 1 ≤ z (.second a) := by
    have hp := (enabled_iff C (.restoreBackward a) z).mp hen
    simp only [rate, sourceLeft, sourceRight, ne_eq,
      mul_eq_zero, not_or] at hp
    omega
  refine restore_window_fire_same_control C h
    (r := .restoreBackward a) (by rfl) hen ?_ ?_ ?_
  · simp [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul]
  · simpa [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul] using Nat.sub_add_cancel hsecond
  · simp [fire_apply, sourceLeft, sourceRight, products,
      unit, nsmul_eq_mul]

private theorem restore_window_fire_pair
    (hen : (rxn C (.pair)).enabled z) :
    RestoreWindow C a d threshold value alpha
      ((rxn C (.pair)).fire z) := by
  refine restore_window_fire_same_control C h
    (r := .pair) (by trivial) hen ?_ ?_ ?_
  all_goals
    simp [fire_apply, sourceLeft, sourceRight, products, unit]

end RestoreWindowFireCases

theorem restore_window_fire (C : XCTM Q) {a : ActiveState C}
    {d threshold value alpha : ℕ} {z : State (Sp C)} {r : Rx C}
    (h : RestoreWindow C a d threshold value alpha z)
    (hc : isClock r = false) (hen : (rxn C r).enabled z) :
    RestoreWindow C a d threshold value alpha ((rxn C r).fire z) := by
  have hr := restore_enabled_at C h hc hen
  cases r with
  | startSecond a' =>
      change a' = a at hr
      subst a'
      exact restore_window_fire_startSecond C h hen
  | growSecond a' =>
      change a' = a at hr
      subst a'
      exact restore_window_fire_growSecond C h hen
  | restoreM a' =>
      change a' = a at hr
      subst a'
      exact restore_window_fire_restoreM C h hen
  | restoreT a' =>
      change a' = a at hr
      subst a'
      exact restore_window_fire_restoreT C h hen
  | restoreD a' =>
      change a' = a at hr
      subst a'
      exact restore_window_fire_restoreD C h hen
  | restoreB a' =>
      change a' = a at hr
      subst a'
      exact restore_window_fire_restoreB C h hen
  | restoreForward a' =>
      change a' = a at hr
      subst a'
      exact restore_window_fire_restoreForward C h hen
  | restoreBackward a' =>
      change a' = a at hr
      subst a'
      exact restore_window_fire_restoreBackward C h hen
  | pair => exact restore_window_fire_pair C h hen
  | _ => exact False.elim hr

def restoreRank (C : XCTM Q) (a : ActiveState C) (z : State (Sp C)) : ℕ :=
  z (.first (activeControl C a)) + z .signal +
    2 * z (.mem .md) + z (.mem .m) + 2 * z (.mem .td) + z (.mem .t) +
    z (.mem .ds) + z (.mem .bs) + z .forwardLatent + z .backwardLatent

theorem restore_rank_drop (C : XCTM Q) {a : ActiveState C}
    {z : State (Sp C)} {r : Rx C}
    (hr : RestoreAt a r) (hen : (rxn C r).enabled z) :
    restoreRank C a ((rxn C r).fire z) < restoreRank C a z := by
  have hp := (enabled_iff C r z).mp hen
  simp only [rate, ne_eq, mul_eq_zero, not_or] at hp
  cases r <;>
    simp_all [RestoreAt, restoreRank, fire_apply, sourceLeft, sourceRight,
      products, unit] <;> omega

theorem restore_workReach_parameters (C : XCTM Q) {a : ActiveState C}
    {d threshold value alpha : ℕ} {x y : State (Sp C)}
    (hd : 0 < d) (hx : RestoreWindow C a d threshold value alpha x)
    (hxy : WorkReach C x y) :
    backwardCount C y ≤ d ∧
      (alpha : ℝ) / 3 ≤ (forwardCount C y : ℝ) / backwardCount C y := by
  have hy : RestoreWindow C a d threshold value alpha y := by
    induction hxy with
    | refl => exact hx
    | tail hxy hyz ih =>
        rcases hyz with ⟨r, hc, hen, rfl⟩
        exact restore_window_fire C ih hc hen
  obtain ⟨hp, hb, ha⟩ := restoreBudget_parameters C hd hy.2.2.2.2.2.2
  exact ⟨hb, ratio_bound hp ha⟩

def restoredMemory (d threshold value : ℕ) : Mem → ℕ
  | .m => value - min value threshold
  | .ms => min value threshold
  | .t => threshold - min value threshold
  | .ts => min value threshold
  | .d => d
  | .b => 1
  | _ => 0

theorem restored_memory_unique {d threshold value : ℕ} {v : Mem → ℕ}
    (ha : MemA d threshold value v) (hr : MemReset v)
    (hp : v .t = 0 ∨ v .m = 0) :
    v = restoredMemory d threshold value := by
  rcases ha with ⟨hm, ht, hms, hd, hb, hk, hkk⟩
  rcases hr with ⟨hmd, htd, hds, hbs⟩
  rcases hp with htzero | hmzero
  · have hle : threshold ≤ value := by omega
    funext s
    cases s <;> simp [restoredMemory, Nat.min_eq_right hle] <;> omega
  · have hle : value ≤ threshold := by omega
    funext s
    cases s <;> simp [restoredMemory, Nat.min_eq_left hle] <;> omega

def RestoreNormal (C : XCTM Q) (a : ActiveState C)
    (d threshold value alpha : ℕ) (z : State (Sp C)) : Prop :=
  OnlyControl C [.second a] z ∧ z (.second a) = d ∧
    (fun m => z (.mem m)) = restoredMemory d threshold value ∧
    z .forward = (alpha + 1) * d ∧ z .forwardLatent = 0 ∧
    z .backward = d ∧ z .backwardLatent = 0

theorem restore_terminal_normal (C : XCTM Q) {a : ActiveState C}
    {d threshold value alpha : ℕ} {z : State (Sp C)}
    (hd : 0 < d) (h : RestoreWindow C a d threshold value alpha z)
    (hterm : WorkTerminal C z) : RestoreNormal C a d threshold value alpha z := by
  rcases h with ⟨ho, hst, hi, hseed, hex, hmem, hbudget⟩
  have hz (r : Rx C) (hc : isClock r = false) : rate C r z = 0 := by
    by_contra hn
    exact hterm r hc ((enabled_iff C r z).mpr hn)
  have hstart := hz (.startSecond a) rfl
  have hgrow := hz (.growSecond a) rfl
  simp only [rate, sourceLeft, sourceRight] at hstart hgrow
  have hsplits := mul_eq_zero.mp hstart
  have hgsplits := mul_eq_zero.mp hgrow
  have hnewpos : 0 < z (.second a) := by omega
  have hold : z (.first (activeControl C a)) = 0 :=
    hgsplits.resolve_right (Nat.ne_of_gt hnewpos)
  have hsignal : z .signal = 0 := hex.resolve_right (Nat.ne_of_gt hnewpos)
  have hnew : z (.second a) = d := by omega
  have zero_of_product (s : Sp C)
      (hs : z (.second a) * z s = 0) : z s = 0 :=
    (mul_eq_zero.mp hs).resolve_left (Nat.ne_of_gt hnewpos)
  have hmd : z (.mem .md) = 0 := zero_of_product _ (by
    simpa only [rate, sourceLeft, sourceRight] using hz (.restoreM a) rfl)
  have htd : z (.mem .td) = 0 := zero_of_product _ (by
    simpa only [rate, sourceLeft, sourceRight] using hz (.restoreT a) rfl)
  have hds : z (.mem .ds) = 0 := zero_of_product _ (by
    simpa only [rate, sourceLeft, sourceRight] using hz (.restoreD a) rfl)
  have hbs : z (.mem .bs) = 0 := zero_of_product _ (by
    simpa only [rate, sourceLeft, sourceRight] using hz (.restoreB a) rfl)
  have had : z .forwardLatent = 0 := zero_of_product _ (by
    simpa only [rate, sourceLeft, sourceRight] using hz (.restoreForward a) rfl)
  have hfd : z .backwardLatent = 0 := zero_of_product _ (by
    simpa only [rate, sourceLeft, sourceRight] using hz (.restoreBackward a) rfl)
  have hpair : z (.mem .t) = 0 ∨ z (.mem .m) = 0 := by
    simpa only [rate, sourceLeft, sourceRight, mul_eq_zero] using hz .pair rfl
  have hmemory := restored_memory_unique hmem ⟨hmd, htd, hds, hbs⟩ hpair
  have hforward : z .forward = (alpha + 1) * d := by
    simpa only [forwardWeight, had, hds, Nat.mul_zero, Nat.add_zero] using hbudget.1
  have hbackward : z .backward = d := by
    simpa only [backwardWeight, hfd, Nat.mul_zero, Nat.add_zero] using hbudget.2.1
  have honly : OnlyControl C [.second a] z := by
    intro s hs hn
    by_cases hf : s = .first (activeControl C a)
    · simpa only [hf] using hold
    by_cases hs' : s = .signal
    · simpa only [hs'] using hsignal
    have hn' : s ≠ .second a := by simpa using hn
    exact ho s hs (by simp [hf, hs', hn'])
  exact ⟨honly, hnew, hmemory, hforward, had, hbackward, hfd⟩

theorem restore_start (C : XCTM Q) (a : ActiveState C)
    (w : List Bool) (alpha : ℕ) (latent : Bool)
    (hthree : latent = true →
      3 * (stateCount w.length / 3) = stateCount w.length) :
    RestoreWindow C a (stateCount w.length) (threshold w.length) (tval w) alpha
      (payload C (.first (activeControl C a)) (stateCount w.length)
        alpha latent (storedMemory w) + unit .signal) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs hn
    cases s <;> simp_all [Sp.IsControl, payload, unit]
  · simp [payload, unit]
  · simp [payload, unit]
  · simp [payload, unit]
  · simp [payload, unit]
  · simp [MemA, payload, storedMemory, unit]
  · cases latent with
    | false =>
        simp [RestoreBudget, forwardWeight, backwardWeight,
          payload, storedMemory, unit] <;> ring
    | true =>
        have hd := hthree rfl
        have ha :
            3 * (alpha * (stateCount w.length / 3)) + stateCount w.length =
              (alpha + 1) * stateCount w.length := by
          calc
            _ = alpha * (3 * (stateCount w.length / 3)) + stateCount w.length := by ring
            _ = (alpha + 1) * stateCount w.length := by rw [hd]; ring
        simp [RestoreBudget, forwardWeight, backwardWeight,
          payload, storedMemory, unit, hd, ha]

theorem restore_normal_payload (C : XCTM Q) {a : ActiveState C}
    {d threshold value alpha : ℕ} {z : State (Sp C)}
    (h : RestoreNormal C a d threshold value alpha z) :
    workView C z = payload C (.second a) d (alpha + 1) false
      (restoredMemory d threshold value) := by
  rcases h with ⟨ho, hnew, hm, ha, had, hf, hfd⟩
  have hc (s : Sp C) (hs : s.IsControl) :
      z s = if s = .second a then d else 0 := by
    by_cases he : s = .second a
    · subst s
      simpa using hnew
    · simpa [he] using ho s hs (by simpa using he)
  funext s
  cases s with
  | first q => simpa only [workView, payload] using hc (.first q) trivial
  | second q => simpa only [workView, payload] using hc (.second q) trivial
  | third q => simpa only [workView, payload] using hc (.third q) trivial
  | reader q => simpa only [workView, payload] using hc (.reader q) trivial
  | write q b => simpa only [workView, payload] using hc (.write q b) trivial
  | extend q => simpa only [workView, payload] using hc (.extend q) trivial
  | signal => simpa only [workView, payload] using hc .signal trivial
  | clock q => rfl
  | mem m => simpa only [workView, payload] using congrFun hm m
  | forward => simpa [workView, payload] using ha
  | forwardLatent => simpa [workView, payload] using had
  | backward => simpa [workView, payload] using hf
  | backwardLatent => simpa [workView, payload] using hfd

theorem restore_terminal_payload (C : XCTM Q) {a : ActiveState C}
    (w : List Bool) {alpha : ℕ} {z : State (Sp C)}
    (h : RestoreWindow C a (stateCount w.length) (threshold w.length) (tval w) alpha z)
    (hterm : WorkTerminal C z) :
    workView C z = payload C (.second a) (stateCount w.length)
      (alpha + 1) false (comparedMemory w) := by
  have hd : 0 < stateCount w.length := by unfold stateCount; positivity
  have hn := restore_terminal_normal C hd h hterm
  simpa only [restoredMemory, comparedMemory] using restore_normal_payload C hn

theorem restore_closed (C : XCTM Q) (a : ActiveState C)
    (d th v alpha : ℕ) :
    ∀ x y, RestoreWindow C a d th v alpha x → WorkStep C x y →
      RestoreWindow C a d th v alpha y := by
  rintro x y hx ⟨r, hr, he, rfl⟩
  exact restore_window_fire C hx hr he

theorem restore_decreases (C : XCTM Q) (a : ActiveState C)
    (d th v alpha : ℕ) :
    ∀ x y, RestoreWindow C a d th v alpha x → WorkStep C x y →
      restoreRank C a y < restoreRank C a x := by
  rintro x y hx ⟨r, hr, he, rfl⟩
  exact restore_rank_drop C (restore_enabled_at C hx hr he) he


/-! ## Fourth read window: repaired shift, zeroing, and writing -/

def readMem (C : XCTM Q) (z : State (Sp C)) : Mem → ℕ := fun a => z (.mem a)

def ReadWindow (C : XCTM Q) (m T g : ℕ) (q : ReadState C) (b : Bool)
    (x x' : ℕ) (z : State (Sp C)) : Prop :=
  (OnlyControl C [.third (.inl q), .signal] z ∧ z .signal = 1 ∧
    z (.third (.inl q)) = m ∧ K3mem m T g b x (readMem C z)) ∨
  (OnlyControl C [.third (.inl q), .reader q] z ∧ z (.reader q) = 1 ∧
    z (.third (.inl q)) + 1 = m ∧ K3mem m T g b x (readMem C z)) ∨
  (OnlyControl C [.third (.inl q), .write q b] z ∧
    z (.third (.inl q)) + z (.write q b) = m ∧ 1 ≤ z (.write q b) ∧
    MemC m T b (C.next q.val b).2 x' (readMem C z))

def ReadNormal (C : XCTM Q) (m T : ℕ) (q : ReadState C) (b : Bool)
    (x' : ℕ) (z : State (Sp C)) : Prop :=
  OnlyControl C [.write q b] z ∧ z (.write q b) = m ∧ Mem4 m T x' (readMem C z)

def readRank (C : XCTM Q) (q : ReadState C) (z : State (Sp C)) : ℕ :=
  z (.third (.inl q)) + 2 * z .signal + z (.reader q) +
    7 * z (.mem .d) + z (.mem .b) + z (.mem .m) + 2 * z (.mem .ms) +
    3 * z (.mem .t) + z (.mem .ts) + z (.mem .k1) + 2 * z (.mem .k2)

private theorem read_enabled_sources (C : XCTM Q) (r : Rx C) (z : State (Sp C))
    (h : (rxn C r).enabled z) :
    z (sourceLeft C r) ≠ 0 ∧ z (sourceRight C r) ≠ 0 := by
  have h' := (enabled_iff C r z).mp h
  change z (sourceLeft C r) * z (sourceRight C r) ≠ 0 at h'
  exact mul_ne_zero_iff.mp h'

theorem read_start_enabled (C : XCTM Q) {m T g x : ℕ} {q : ReadState C}
    {b : Bool} {z : State (Sp C)}
    (hO : OnlyControl C [.third (.inl q), .signal] z)
    (hM : K3mem m T g b x (readMem C z))
    (r : Rx C) (hclock : isClock r = false) (hE : (rxn C r).enabled z) :
    r = .startRead q := by
  obtain ⟨hL, hR⟩ := enabled_control_support C hO hE
  obtain ⟨hleft, hright⟩ := read_enabled_sources C r z hE
  obtain ⟨⟨_, _, _, _, _, hk, hkk⟩, _, hb, hb'⟩ := hM
  have hTM : z (.mem .t) = 0 ∨ z (.mem .m) = 0 := by
    cases b
    · exact Or.inr (hb rfl).1
    · exact Or.inl (hb' rfl).1
  simp only [readMem] at hk hkk
  cases r <;> simp_all [sourceLeft, sourceRight, Sp.IsControl, isClock]

theorem read_choose_enabled (C : XCTM Q) {m T g x : ℕ} {q : ReadState C}
    {b : Bool} {z : State (Sp C)}
    (hO : OnlyControl C [.third (.inl q), .reader q] z)
    (hM : K3mem m T g b x (readMem C z))
    (r : Rx C) (hclock : isClock r = false) (hE : (rxn C r).enabled z) :
    r = .chooseRead q b := by
  obtain ⟨hL, hR⟩ := enabled_control_support C hO hE
  obtain ⟨hleft, hright⟩ := read_enabled_sources C r z hE
  obtain ⟨⟨_, _, _, _, _, hk, hkk⟩, _, hb, hb'⟩ := hM
  simp only [readMem] at hk hkk hb hb'
  cases r with
  | chooseRead q' b' =>
      have hq : q' = q := by
        simpa [sourceLeft, Sp.IsControl] using hL trivial
      subst q'
      cases b <;> cases b' <;>
        simp_all [sourceLeft, sourceRight, Sp.IsControl, isClock]
  | _ =>
      cases b <;>
        simp_all [sourceLeft, sourceRight, Sp.IsControl, isClock]

def readWorkLabels (C : XCTM Q) (q : ReadState C) (b : Bool) : List (Rx C) :=
  [.growWrite q b, .readRestoreM q b, .readRestoreTs q b, .readRestoreT q b,
    .readShift q b, .readZero q b, .readWrite q b, .pair, .consumeSingle, .consumeDouble]

theorem read_work_enabled (C : XCTM Q) {q : ReadState C} {b : Bool}
    {z : State (Sp C)} (hO : OnlyControl C [.third (.inl q), .write q b] z)
    (r : Rx C) (hclock : isClock r = false) (hE : (rxn C r).enabled z) :
    r ∈ readWorkLabels C q b := by
  obtain ⟨hL, hR⟩ := enabled_control_support C hO hE
  cases r <;>
    simp_all [readWorkLabels, sourceLeft, sourceRight, Sp.IsControl, isClock]

theorem read_terminal_normal (C : XCTM Q) {m T g x x' : ℕ}
    (hm : 0 < m) (hg : 0 < g) (hx' : 0 < x') {q : ReadState C}
    {b : Bool} {z : State (Sp C)} (hW : ReadWindow C m T g q b x x' z)
    (hT : WorkTerminal C z) : ReadNormal C m T q b x' z := by
  rcases hW with ⟨hO, hI, hthird, hM⟩ | ⟨hO, hR, hthird, hM⟩ |
    ⟨hO, hcount, hu, hM⟩
  · exfalso
    apply hT (.startRead q) rfl
    rw [enabled_iff]
    simpa [rate, sourceLeft, sourceRight, hI, hthird] using hm.ne'
  · exfalso
    have hc : z (.mem (if b then .m else .t)) ≠ 0 := by
      obtain ⟨_, _, hb, hb'⟩ := hM
      cases b with
      | false =>
          have h := (hb rfl).2
          change g ≤ z (.mem .t) at h
          change z (.mem .t) ≠ 0
          omega
      | true =>
          have h := (hb' rfl).2
          change g ≤ z (.mem .m) at h
          change z (.mem .m) ≠ 0
          omega
    apply hT (.chooseRead q b) rfl
    rw [enabled_iff]
    simpa [rate, sourceLeft, sourceRight, hR] using hc
  · have hthird : z (.third (.inl q)) = 0 := by
      by_contra hz
      apply hT (.growWrite q b) rfl
      rw [enabled_iff]
      change z (.third (.inl q)) * z (.write q b) ≠ 0
      exact mul_ne_zero hz (by omega)
    have vanish (a : Mem) (r : Rx C) (hL : sourceLeft C r = .write q b)
        (hR : sourceRight C r = .mem a) (hc : isClock r = false) :
        z (.mem a) = 0 := by
      by_contra hz
      apply hT r hc
      rw [enabled_iff]
      change z (sourceLeft C r) * z (sourceRight C r) ≠ 0
      rw [hL, hR]
      exact mul_ne_zero (by omega) hz
    have hms := vanish .ms (.readRestoreM q b) rfl rfl rfl
    have hts := vanish .ts (.readRestoreTs q b) rfl rfl rfl
    have ht := vanish .t (.readRestoreT q b) rfl rfl rfl
    have hmm := vanish .m (.readShift q b) rfl rfl rfl
    have hd := vanish .d (.readZero q b) rfl rfl rfl
    have hb := vanish .b (.readWrite q b) rfl rfl rfl
    obtain ⟨hv, hthreshold, hdtotal, hbtotal⟩ := hM
    simp only [readMem] at hv hthreshold hdtotal hbtotal
    simp only [hmm, hms, hb, hd, mul_zero, add_zero, zero_add] at hv
    have hmd : 0 < z (.mem .md) := by omega
    have hk : z (.mem .k1) = 0 := by
      by_contra hz
      apply hT .consumeSingle rfl
      rw [enabled_iff]
      change z (.mem .k1) * z (.mem .md) ≠ 0
      exact mul_ne_zero hz hmd.ne'
    have hkk : z (.mem .k2) = 0 := by
      by_contra hz
      apply hT .consumeDouble rfl
      rw [enabled_iff]
      change z (.mem .k2) * z (.mem .md) ≠ 0
      exact mul_ne_zero hz hmd.ne'
    refine ⟨?_, by omega, ?_⟩
    · intro s hs hn
      by_cases he : s = .third (.inl q)
      · simpa only [he] using hthird
      · exact hO s hs (by simpa [he] using hn)
    · change Mem4 m T x' (readMem C z)
      simp only [Mem4, readMem]
      exact ⟨by omega, by omega, by omega, by omega,
        hmm, hms, ht, hts, hd, hb, hk, hkk⟩

theorem read_normal_terminal (C : XCTM Q) {m T x' : ℕ} {q : ReadState C}
    {b : Bool} {z : State (Sp C)} (h : ReadNormal C m T q b x' z) :
    WorkTerminal C z := by
  obtain ⟨hO, hu, hM⟩ := h
  have hO' : OnlyControl C [.third (.inl q), .write q b] z := by
    intro s hs hn
    apply hO s hs
    intro hmem
    apply hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
    exact Or.inr hmem
  have hthird : z (.third (.inl q)) = 0 := hO _ trivial (by simp)
  obtain ⟨_, _, _, _, hmm, hms, ht, hts, hd, hb, hk, hkk⟩ := hM
  simp only [readMem] at hmm hms ht hts hd hb hk hkk
  intro r hc hE
  have hr := read_work_enabled C hO' r hc hE
  simp only [readWorkLabels, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [enabled_iff] at hE <;>
    simp [rate, sourceLeft, sourceRight, hthird, hmm, hms, ht, hts, hd, hb, hk, hkk] at hE


private theorem read_work_finish (C : XCTM Q)
    {m T g x x' : ℕ} {q : ReadState C} {b : Bool}
    {z : State (Sp C)}
    (hO : OnlyControl C [.third (.inl q), .write q b] z)
    (hcount : z (.third (.inl q)) + z (.write q b) = m)
    (hu : 1 ≤ z (.write q b))
    (r : Rx C) (hr : r ∈ readWorkLabels C q b)
    (hE : (rxn C r).enabled z)
    (hmem :
      MemC m T b (C.next q.val b).2 x'
        (readMem C ((rxn C r).fire z)))
    (hdrop :
      readRank C q ((rxn C r).fire z) < readRank C q z) :
    ReadWindow C m T g q b x x' ((rxn C r).fire z) ∧
      readRank C q ((rxn C r).fire z) < readRank C q z := by
  have hsrc := read_enabled_sources C r z hE
  simp only [readWorkLabels, List.mem_cons, List.not_mem_nil, or_false] at hr
  refine
    ⟨Or.inr (Or.inr
      ⟨OnlyControl.fire hO r ?_, ?_, ?_, hmem⟩), hdrop⟩
  · intro s hs hn
    have hnU : s ≠ .write q b := by
      intro he
      apply hn
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr he
    have hnM (a : Mem) : s ≠ .mem a := by
      intro he
      subst s
      exact hs
    rcases hr with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [products, unit, Pi.add_apply, Pi.smul_apply,
        nsmul_eq_mul, hnU, hnM]
  · rcases hr with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sourceLeft, sourceRight] at hsrc <;>
      simp [fire_apply, sourceLeft, sourceRight, products, unit,
        Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] <;>
      omega
  · rcases hr with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sourceLeft, sourceRight] at hsrc <;>
      simp [fire_apply, sourceLeft, sourceRight, products, unit,
        Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] <;>
      omega

section ReadWorkFireCases

variable (C : XCTM Q) {m T g x x' : ℕ} {q : ReadState C}
    {b : Bool} {z : State (Sp C)}
    (hO : OnlyControl C [.third (.inl q), .write q b] z)
    (hcount : z (.third (.inl q)) + z (.write q b) = m)
    (hu : 1 ≤ z (.write q b))
    (hM : MemC m T b (C.next q.val b).2 x' (readMem C z))

include hO hcount hu hM

private theorem read_work_fire_growWrite
    (hE : (rxn C (.growWrite q b)).enabled z) :
    ReadWindow C m T g q b x x' ((rxn C (.growWrite q b)).fire z) ∧
      readRank C q ((rxn C (.growWrite q b)).fire z) <
        readRank C q z := by
  have hsrc := read_enabled_sources C (.growWrite q b) z hE
  simp only [sourceLeft, sourceRight] at hsrc
  apply read_work_finish C hO hcount hu (.growWrite q b)
    (by simp [readWorkLabels]) hE
  · simpa [MemC, readMem, fire_apply, sourceLeft, sourceRight,
      products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] using hM
  · simp [readRank, fire_apply, sourceLeft, sourceRight,
      products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] <;>
      omega

private theorem read_work_fire_readRestoreM
    (hE : (rxn C (.readRestoreM q b)).enabled z) :
    ReadWindow C m T g q b x x' ((rxn C (.readRestoreM q b)).fire z) ∧
      readRank C q ((rxn C (.readRestoreM q b)).fire z) <
        readRank C q z := by
  have hsrc := read_enabled_sources C (.readRestoreM q b) z hE
  simp only [sourceLeft, sourceRight] at hsrc
  apply read_work_finish C hO hcount hu (.readRestoreM q b)
    (by simp [readWorkLabels]) hE
  · cases hz : (C.next q.val b).2 <;> cases b <;>
      simp [MemC, readMem, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul,
        bw, Bool.toNat, hz] at hM ⊢ <;>
      omega
  · cases b <;>
      simp [readRank, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] <;>
      omega

private theorem read_work_fire_readRestoreTs
    (hE : (rxn C (.readRestoreTs q b)).enabled z) :
    ReadWindow C m T g q b x x' ((rxn C (.readRestoreTs q b)).fire z) ∧
      readRank C q ((rxn C (.readRestoreTs q b)).fire z) <
        readRank C q z := by
  have hsrc := read_enabled_sources C (.readRestoreTs q b) z hE
  simp only [sourceLeft, sourceRight] at hsrc
  apply read_work_finish C hO hcount hu (.readRestoreTs q b)
    (by simp [readWorkLabels]) hE
  · cases hz : (C.next q.val b).2 <;> cases b <;>
      simp [MemC, readMem, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul,
        bw, Bool.toNat, hz] at hM ⊢ <;>
      omega
  · cases b <;>
      simp [readRank, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] <;>
      omega

private theorem read_work_fire_readRestoreT
    (hE : (rxn C (.readRestoreT q b)).enabled z) :
    ReadWindow C m T g q b x x' ((rxn C (.readRestoreT q b)).fire z) ∧
      readRank C q ((rxn C (.readRestoreT q b)).fire z) <
        readRank C q z := by
  have hsrc := read_enabled_sources C (.readRestoreT q b) z hE
  simp only [sourceLeft, sourceRight] at hsrc
  apply read_work_finish C hO hcount hu (.readRestoreT q b)
    (by simp [readWorkLabels]) hE
  · cases hz : (C.next q.val b).2 <;> cases b <;>
      simp [MemC, readMem, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul,
        bw, Bool.toNat, hz] at hM ⊢ <;>
      omega
  · cases b <;>
      simp [readRank, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] <;>
      omega

private theorem read_work_fire_readShift
    (hE : (rxn C (.readShift q b)).enabled z) :
    ReadWindow C m T g q b x x' ((rxn C (.readShift q b)).fire z) ∧
      readRank C q ((rxn C (.readShift q b)).fire z) <
        readRank C q z := by
  have hsrc := read_enabled_sources C (.readShift q b) z hE
  simp only [sourceLeft, sourceRight] at hsrc
  apply read_work_finish C hO hcount hu (.readShift q b)
    (by simp [readWorkLabels]) hE
  · cases hz : (C.next q.val b).2 <;> cases b <;>
      simp [MemC, readMem, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul,
        bw, Bool.toNat, hz] at hM ⊢ <;>
      omega
  · cases b <;>
      simp [readRank, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] <;>
      omega

private theorem read_work_fire_readZero
    (hE : (rxn C (.readZero q b)).enabled z) :
    ReadWindow C m T g q b x x' ((rxn C (.readZero q b)).fire z) ∧
      readRank C q ((rxn C (.readZero q b)).fire z) <
        readRank C q z := by
  have hsrc := read_enabled_sources C (.readZero q b) z hE
  simp only [sourceLeft, sourceRight] at hsrc
  apply read_work_finish C hO hcount hu (.readZero q b)
    (by simp [readWorkLabels]) hE
  · cases hz : (C.next q.val b).2 <;> cases b <;>
      simp [MemC, readMem, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul,
        bw, Bool.toNat, hz] at hM ⊢ <;>
      omega
  · cases b <;>
      simp [readRank, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] <;>
      omega

private theorem read_work_fire_readWrite
    (hE : (rxn C (.readWrite q b)).enabled z) :
    ReadWindow C m T g q b x x' ((rxn C (.readWrite q b)).fire z) ∧
      readRank C q ((rxn C (.readWrite q b)).fire z) <
        readRank C q z := by
  have hsrc := read_enabled_sources C (.readWrite q b) z hE
  simp only [sourceLeft, sourceRight] at hsrc
  apply read_work_finish C hO hcount hu (.readWrite q b)
    (by simp [readWorkLabels]) hE
  · cases hz : (C.next q.val b).2 <;> cases b <;>
      simp [MemC, readMem, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul,
        bw, Bool.toNat, hz] at hM ⊢ <;>
      omega
  · cases b <;>
      simp [readRank, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] <;>
      omega

private theorem read_work_fire_pair
    (hE : (rxn C .pair).enabled z) :
    ReadWindow C m T g q b x x' ((rxn C .pair).fire z) ∧
      readRank C q ((rxn C .pair).fire z) <
        readRank C q z := by
  have hsrc := read_enabled_sources C .pair z hE
  simp only [sourceLeft, sourceRight] at hsrc
  apply read_work_finish C hO hcount hu .pair
    (by simp [readWorkLabels]) hE
  · cases hz : (C.next q.val b).2 <;> cases b <;>
      simp [MemC, readMem, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul,
        bw, Bool.toNat, hz] at hM ⊢ <;>
      omega
  · cases b <;>
      simp [readRank, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] <;>
      omega

private theorem read_work_fire_consumeSingle
    (hE : (rxn C .consumeSingle).enabled z) :
    ReadWindow C m T g q b x x' ((rxn C .consumeSingle).fire z) ∧
      readRank C q ((rxn C .consumeSingle).fire z) <
        readRank C q z := by
  have hsrc := read_enabled_sources C .consumeSingle z hE
  simp only [sourceLeft, sourceRight] at hsrc
  apply read_work_finish C hO hcount hu .consumeSingle
    (by simp [readWorkLabels]) hE
  · cases hz : (C.next q.val b).2 <;> cases b <;>
      simp [MemC, readMem, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul,
        bw, Bool.toNat, hz] at hM ⊢ <;>
      omega
  · cases b <;>
      simp [readRank, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] <;>
      omega

private theorem read_work_fire_consumeDouble
    (hE : (rxn C .consumeDouble).enabled z) :
    ReadWindow C m T g q b x x' ((rxn C .consumeDouble).fire z) ∧
      readRank C q ((rxn C .consumeDouble).fire z) <
        readRank C q z := by
  have hsrc := read_enabled_sources C .consumeDouble z hE
  simp only [sourceLeft, sourceRight] at hsrc
  apply read_work_finish C hO hcount hu .consumeDouble
    (by simp [readWorkLabels]) hE
  · cases hz : (C.next q.val b).2 <;> cases b <;>
      simp [MemC, readMem, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul,
        bw, Bool.toNat, hz] at hM ⊢ <;>
      omega
  · cases b <;>
      simp [readRank, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] <;>
      omega

end ReadWorkFireCases

theorem read_work_fire (C : XCTM Q) {m T g x x' : ℕ} {q : ReadState C}
    {b : Bool} {z : State (Sp C)}
    (hO : OnlyControl C [.third (.inl q), .write q b] z)
    (hcount : z (.third (.inl q)) + z (.write q b) = m)
    (hu : 1 ≤ z (.write q b))
    (hM : MemC m T b (C.next q.val b).2 x' (readMem C z))
    (r : Rx C) (hc : isClock r = false) (hE : (rxn C r).enabled z) :
    ReadWindow C m T g q b x x' ((rxn C r).fire z) ∧
      readRank C q ((rxn C r).fire z) < readRank C q z := by
  have hr := read_work_enabled C hO r hc hE
  simp only [readWorkLabels, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact read_work_fire_growWrite C hO hcount hu hM hE
  · exact read_work_fire_readRestoreM C hO hcount hu hM hE
  · exact read_work_fire_readRestoreTs C hO hcount hu hM hE
  · exact read_work_fire_readRestoreT C hO hcount hu hM hE
  · exact read_work_fire_readShift C hO hcount hu hM hE
  · exact read_work_fire_readZero C hO hcount hu hM hE
  · exact read_work_fire_readWrite C hO hcount hu hM hE
  · exact read_work_fire_pair C hO hcount hu hM hE
  · exact read_work_fire_consumeSingle C hO hcount hu hM hE
  · exact read_work_fire_consumeDouble C hO hcount hu hM hE

theorem read_memory_enter (C : XCTM Q) {m T g x x' : ℕ} {q : ReadState C}
    {b : Bool} {z : State (Sp C)}
    (hM : K3mem m T g b x (readMem C z))
    (hnext : x' + 3 * bw b * m = 3 * x + bw (C.next q.val b).2) :
    MemC m T b (C.next q.val b).2 x' (readMem C z) := by
  obtain ⟨⟨hvalue, hthreshold, hpair, hdtotal, hbtotal, hk, hkk⟩,
    ⟨hmd, htd, hds, hbs⟩, _, _⟩ := hM
  simp only [readMem] at hvalue hthreshold hpair hdtotal hbtotal hk hkk hmd htd hds hbs
  have hd : z (.mem .d) = m := by omega
  have hb : z (.mem .b) = 1 := by omega
  have hv : z (.mem .m) + z (.mem .ms) = x := by omega
  refine ⟨?_, hthreshold, hdtotal, hbtotal⟩
  simp only [readMem, hmd, hk, hkk, hd, hb, hv, mul_one, mul_zero, add_zero, zero_add]
  exact hnext.symm

theorem read_window_fire (C : XCTM Q) {m T g x x' : ℕ}
    {q : ReadState C} {b : Bool} {z : State (Sp C)}
    (hnext : x' + 3 * bw b * m = 3 * x + bw (C.next q.val b).2)
    (hW : ReadWindow C m T g q b x x' z)
    (r : Rx C) (hc : isClock r = false) (hE : (rxn C r).enabled z) :
    ReadWindow C m T g q b x x' ((rxn C r).fire z) ∧
      readRank C q ((rxn C r).fire z) < readRank C q z := by
  rcases hW with ⟨hO, hI, hthird, hM⟩ | ⟨hO, hR, hthird, hM⟩ |
    ⟨hO, hcount, hu, hM⟩
  · obtain rfl := read_start_enabled C hO hM r hc hE
    have hsrc := read_enabled_sources C (.startRead q) z hE
    simp only [sourceLeft, sourceRight] at hsrc
    have hR : z (.reader q) = 0 := hO _ trivial (by simp)
    have hmem : readMem C ((rxn C (.startRead q)).fire z) = readMem C z := by
      funext a
      simp [readMem, fire_apply, sourceLeft, sourceRight, products, unit]
    refine ⟨Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩), ?_⟩
    · intro s hs hn
      by_cases he : s = .signal
      · subst s
        simp [fire_apply, sourceLeft, sourceRight, products, unit, hI]
      · have hz := hO s hs (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn ⊢
          exact ⟨hn.1, he⟩)
        have hnR : s ≠ .reader q := fun h => hn (by simp [h])
        simp [fire_apply, sourceLeft, sourceRight, products, unit, hz, hnR, he]
    · simp [fire_apply, sourceLeft, sourceRight, products, unit, hR]
    · simp [fire_apply, sourceLeft, sourceRight, products, unit] <;> omega
    · rw [hmem]
      exact hM
    · simp [readRank, fire_apply, sourceLeft, sourceRight, products, unit, hI, hR] <;> omega
  · obtain rfl := read_choose_enabled C hO hM r hc hE
    have hsrc := read_enabled_sources C (.chooseRead q b) z hE
    simp only [sourceLeft, sourceRight] at hsrc
    have hu : z (.write q b) = 0 := hO _ trivial (by simp)
    have hmem : readMem C ((rxn C (.chooseRead q b)).fire z) = readMem C z := by
      funext a
      cases b <;> cases a <;>
        simp [readMem, fire_apply, sourceLeft, sourceRight, products, unit] at hsrc ⊢ <;> omega
    refine ⟨Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩), ?_⟩
    · intro s hs hn
      by_cases he : s = .reader q
      · subst s
        simp [fire_apply, sourceLeft, sourceRight, products, unit, hR]
      · have hz := hO s hs (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn ⊢
          exact ⟨hn.1, he⟩)
        have hnU : s ≠ .write q b := fun h => hn (by simp [h])
        have hnM : ∀ a : Mem, s ≠ .mem a := by
          rintro a rfl
          exact hs
        simp [fire_apply, sourceLeft, sourceRight, products, unit, hz, hnU, he, hnM]
    · simp [fire_apply, sourceLeft, sourceRight, products, unit, hu] <;> omega
    · simp [fire_apply, sourceLeft, sourceRight, products, unit, hu]
    · rw [hmem]
      exact read_memory_enter C hM hnext
    · simp only [readRank]
      cases b <;>
        simp [fire_apply, sourceLeft, sourceRight, products, unit, hR] at hsrc ⊢ <;> omega
  · exact read_work_fire C hO hcount hu hM r hc hE

def readFuel (C : XCTM Q) (z : State (Sp C)) : ℕ × ℕ × ℕ × ℕ :=
  (z .forward, z .forwardLatent, z .backward, z .backwardLatent)

theorem read_fuel_fire (C : XCTM Q) {m T g x x' : ℕ} {q : ReadState C}
    {b : Bool} {z : State (Sp C)} (hW : ReadWindow C m T g q b x x' z)
    (r : Rx C) (hc : isClock r = false) (hE : (rxn C r).enabled z) :
    readFuel C ((rxn C r).fire z) = readFuel C z := by
  rcases hW with ⟨hO, _, _, hM⟩ | ⟨hO, _, _, hM⟩ | ⟨hO, _, _, _⟩
  · obtain rfl := read_start_enabled C hO hM r hc hE
    simp [readFuel, fire_apply, sourceLeft, sourceRight, products, unit]
  · obtain rfl := read_choose_enabled C hO hM r hc hE
    simp [readFuel, fire_apply, sourceLeft, sourceRight, products, unit]
  · have hr := read_work_enabled C hO r hc hE
    simp only [readWorkLabels, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [readFuel, fire_apply, sourceLeft, sourceRight, products, unit]

theorem read_workReach_invariant (C : XCTM Q) {m T g x x' : ℕ}
    {q : ReadState C} {b : Bool} {z₀ z : State (Sp C)}
    (hnext : x' + 3 * bw b * m = 3 * x + bw (C.next q.val b).2)
    (hstart : ReadWindow C m T g q b x x' z₀) (hreach : WorkReach C z₀ z) :
    ReadWindow C m T g q b x x' z ∧ readFuel C z = readFuel C z₀ := by
  induction hreach with
  | refl => exact ⟨hstart, rfl⟩
  | tail hxy hyz ih =>
      obtain ⟨r, hc, hE, rfl⟩ := hyz
      exact ⟨(read_window_fire C hnext ih.1 r hc hE).1,
        (read_fuel_fire C ih.1 r hc hE).trans ih.2⟩

theorem comparedMemory_read (w : List Bool) (hs : 3 ≤ w.length) :
    K3mem (stateCount w.length) (threshold w.length) (2 * 3 ^ (w.length - 3))
      (w.headD false) (tval w) (comparedMemory w) := by
  obtain ⟨_, hfalse, htrue, _, _, _⟩ :=
    tape_facts (n := w.length - 3) (w := w) (by omega) false
  have hc := Nat.min_le_left (tval w) (threshold w.length)
  have hc' := Nat.min_le_right (tval w) (threshold w.length)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · change
        tval w - min (tval w) (threshold w.length) +
            min (tval w) (threshold w.length) + 0 =
          tval w
      omega
    · change
        threshold w.length - min (tval w) (threshold w.length) +
            min (tval w) (threshold w.length) + 0 =
          threshold w.length
      omega
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · intro hb
    have hgap : tval w + 2 * 3 ^ (w.length - 3) ≤ threshold w.length := by
      rw [threshold_eq w.length hs]
      exact hfalse hb
    have hmin : min (tval w) (threshold w.length) = tval w :=
      Nat.min_eq_left (by omega)
    simp only [comparedMemory, hmin]
    constructor <;> omega
  · intro hb
    have hgap : threshold w.length + 2 * 3 ^ (w.length - 3) ≤ tval w := by
      rw [threshold_eq w.length hs]
      exact htrue hb
    have hmin : min (tval w) (threshold w.length) = threshold w.length :=
      Nat.min_eq_right (by omega)
    simp only [comparedMemory, hmin]
    constructor <;> omega

theorem read_start_from_payload (C : XCTM Q) (q : ReadState C)
    (w : List Bool) (a : ℕ) (hs : 3 ≤ w.length) :
    ReadWindow C (stateCount w.length) (threshold w.length)
      (2 * 3 ^ (w.length - 3)) q (w.headD false) (tval w)
      (tval (w.tail ++ [(C.next q.val (w.headD false)).2]))
      (payload C (.third (.inl q)) (stateCount w.length) a false (comparedMemory w) +
        unit .signal) := by
  refine Or.inl ⟨?_, ?_, ?_, ?_⟩
  · intro s hcontrol hn
    cases s <;> simp_all [payload, unit, Sp.IsControl]
  · simp [payload, unit]
  · simp [payload, unit]
  · have hmem :
        readMem C
          (payload C (.third (.inl q)) (stateCount w.length) a false (comparedMemory w) +
            unit .signal) = comparedMemory w := by
      funext m
      simp [readMem, payload, unit]
    rw [hmem]
    exact comparedMemory_read w hs

theorem read_normal_payload (C : XCTM Q) (q : ReadState C) (b : Bool)
    (w : List Bool) (a : ℕ) (z : State (Sp C))
    (hN : ReadNormal C (stateCount w.length) (threshold w.length) q b (tval w) z)
    (hF : readFuel C z = (a * stateCount w.length, 0, stateCount w.length, 0)) :
    workView C z =
      payload C (.write q b) (stateCount w.length) a false (storedMemory w) := by
  obtain ⟨hO, hu, hM⟩ := hN
  simp only [readFuel, Prod.mk.injEq] at hF
  obtain ⟨hA, hAd, hB, hBd⟩ := hF
  simp only [Mem4, readMem] at hM
  obtain ⟨hmd, htd, hds, hbs, hmm, hms, ht, hts, hd, hb, hk, hkk⟩ := hM
  have hcontrol (s : Sp C) (hs : s.IsControl) :
      workView C z s =
        payload C (.write q b) (stateCount w.length) a false (storedMemory w) s := by
    by_cases he : s = .write q b
    · subst s
      simpa [workView, payload] using hu
    · have hz : z s = 0 := hO s hs (by simp [he])
      cases s <;> simp_all [workView, payload, Sp.IsControl]
  funext s
  by_cases hs : s.IsControl
  · exact hcontrol s hs
  · cases s with
    | mem m => cases m <;> simp_all [workView, payload, storedMemory]
    | _ => simp_all [workView, payload, Sp.IsControl]


/-! ## Fourth extension window -/

def ExtensionSpecies (C : XCTM Q) (e : ExtendState C) : Sp C → Prop
  | .third a => a = .inr e
  | .extend e' => e' = e
  | .signal | .clock _ | .forward | .forwardLatent | .backward | .backwardLatent => True
  | .mem m => m ≠ .k1 ∧ m ≠ .k2
  | _ => False

def ExtensionLabel (C : XCTM Q) (e : ExtendState C) (r : Rx C) : Prop :=
  r = .startExtension e ∨ r = .growExtension e ∨
  r = .extendRestoreM e ∨ r = .extendShift e ∨ r = .extendWrite e ∨
  r = .extendRestoreTs e ∨ r = .extendRestoreT e ∨ r = .extendD e ∨
  r = .extendForward e ∨ r = .extendBackward e ∨ r = .pair

structure ExtensionInvariant
    (C : XCTM Q) (e : ExtendState C) (d v th a f : ℕ) (z : State (Sp C)) : Prop where
  support : ∀ s, ¬ ExtensionSpecies C e s → z s = 0
  control : 3 * z (.third (.inr e)) + z (.extend e) = 3 * d
  signal : z .signal ≤ 1
  exclusive : z .signal = 0 ∨ z (.extend e) = 0
  progress : 0 < z .signal ∨ 0 < z (.extend e)
  memory : 3 * (z (.mem .m) + z (.mem .ms)) +
    z (.mem .md) + z (.mem .b) = 3 * v + 1
  threshold : 3 * (z (.mem .t) + z (.mem .ts)) + z (.mem .td) = 3 * th
  size : 3 * z (.mem .d) + z (.mem .ds) = 3 * d
  button : z (.mem .b) + z (.mem .bs) = 1
  forward : z .forward + z .forwardLatent = a
  backward : z .backward + z .backwardLatent = f

def extensionRank (C : XCTM Q) (e : ExtendState C) (z : State (Sp C)) : ℕ :=
  z (.third (.inr e)) + z .signal + z (.mem .b) + z (.mem .d) +
    z (.mem .m) + 2 * z (.mem .ms) + 3 * z (.mem .t) +
    z (.mem .ts) + z .forward + z .backward

private theorem enabled_sources_positive (C : XCTM Q) (r : Rx C) (z : State (Sp C))
    (he : (rxn C r).enabled z) :
    0 < z (sourceLeft C r) ∧ 0 < z (sourceRight C r) := by
  have h := (enabled_iff C r z).mp he
  simp only [rate, ne_eq, mul_eq_zero, not_or] at h
  omega

theorem extension_products_support (C : XCTM Q) (e : ExtendState C) (r : Rx C)
    (hr : ExtensionLabel C e r) (s : Sp C)
    (hs : ¬ ExtensionSpecies C e s) : products C r s = 0 := by
  unfold ExtensionLabel at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    cases s with
    | mem m =>
        cases m <;> simp_all [ExtensionSpecies, products, unit, Pi.add_apply, Pi.smul_apply]
    | _ => simp_all [ExtensionSpecies, products, unit, Pi.add_apply, Pi.smul_apply]

theorem extension_invariant_fire
    (C : XCTM Q) (e : ExtendState C) (d v th a f : ℕ)
    (z : State (Sp C)) (hz : ExtensionInvariant C e d v th a f z)
    (r : Rx C) (hr : ExtensionLabel C e r) (he : (rxn C r).enabled z) :
    ExtensionInvariant C e d v th a f ((rxn C r).fire z) := by
  have hp := enabled_sources_positive C r z he
  have hsupport : ∀ s, ¬ ExtensionSpecies C e s → (rxn C r).fire z s = 0 := by
    intro s hs
    rw [fire_apply, hz.support s hs, extension_products_support C e r hr s hs]
    simp
  rcases hz with ⟨hs, hc, hi, hx, hpresent, hm, ht, hd, hb, ha, hf⟩
  refine ⟨hsupport, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    unfold ExtensionLabel at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [fire_apply, sourceLeft, sourceRight, products, unit,
        Pi.add_apply, Pi.smul_apply] at hp ⊢ <;> omega

theorem extension_rank_drop (C : XCTM Q) (e : ExtendState C) (r : Rx C)
    (hr : ExtensionLabel C e r) (z : State (Sp C)) (he : (rxn C r).enabled z) :
    extensionRank C e ((rxn C r).fire z) < extensionRank C e z := by
  have hp := enabled_sources_positive C r z he
  unfold ExtensionLabel at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [extensionRank, fire_apply, sourceLeft, sourceRight,
      products, unit, Pi.add_apply, Pi.smul_apply] at hp ⊢ <;> omega

theorem extension_enabled_label
    (C : XCTM Q) (e : ExtendState C) (d v th a f : ℕ)
    (z : State (Sp C)) (hz : ExtensionInvariant C e d v th a f z)
    (r : Rx C) (hw : isClock r = false) (he : (rxn C r).enabled z) :
    ExtensionLabel C e r := by
  have hp := enabled_sources_positive C r z he
  have hfirst (q : Q) : z (.first q) = 0 :=
    hz.support _ (by simp [ExtensionSpecies])
  have hsecond (u : ActiveState C) : z (.second u) = 0 :=
    hz.support _ (by simp [ExtensionSpecies])
  have hreader (q : ReadState C) : z (.reader q) = 0 :=
    hz.support _ (by simp [ExtensionSpecies])
  have hwrite (q : ReadState C) (b : Bool) : z (.write q b) = 0 :=
    hz.support _ (by simp [ExtensionSpecies])
  have hreadThird (q : ReadState C) : z (.third (.inl q)) = 0 :=
    hz.support _ (by simp [ExtensionSpecies])
  have hdouble : z (.mem .k2) = 0 := hz.support _ (by simp [ExtensionSpecies])
  have hsingle : z (.mem .k1) = 0 := hz.support _ (by simp [ExtensionSpecies])
  have onlyExtend (e' : ExtendState C) (hh : 0 < z (.extend e')) : e' = e := by
    by_contra hn
    have hzero := hz.support (.extend e') (by simpa [ExtensionSpecies] using hn)
    omega
  have onlyThird (u : ActiveState C) (hh : 0 < z (.third u)) : u = .inr e := by
    by_contra hn
    have hzero := hz.support (.third u) (by simpa [ExtensionSpecies] using hn)
    omega
  cases r with
  | tick latent => simp [isClock] at hw
  | up c latent => simp [isClock] at hw
  | down c latent => simp [isClock] at hw
  | startExtension e' =>
      have hu := onlyThird (.inr e') (by simpa [sourceRight] using hp.2)
      have heq : e' = e := Sum.inr.inj hu
      subst e'
      simp [ExtensionLabel]
  | growExtension e' =>
      have heq := onlyExtend e' (by simpa [sourceRight] using hp.2)
      subst e'
      simp [ExtensionLabel]
  | extendRestoreM e' | extendShift e' | extendWrite e' | extendRestoreTs e' | extendRestoreT e' | extendD e' | extendForward e' | extendBackward e' =>
      have heq := onlyExtend e' (by simpa [sourceLeft] using hp.1)
      subst e'
      simp [ExtensionLabel]
  | finishExtension e' =>
      have heq := onlyExtend e' (by simpa [sourceRight] using hp.2)
      subst e'
      have hx := hz.exclusive
      simp [sourceLeft, sourceRight] at hp
      omega
  | pair => simp [ExtensionLabel]
  | _ =>
      simp [sourceLeft, sourceRight, hfirst, hsecond, hreader,
        hwrite, hreadThird, hdouble, hsingle] at hp

theorem extension_terminal_rank_zero
    (C : XCTM Q) (e : ExtendState C) (d v th a f : ℕ)
    (hd : 0 < d) (z : State (Sp C)) (hz : ExtensionInvariant C e d v th a f z)
    (ht : WorkTerminal C z) : extensionRank C e z = 0 := by
  have noRate (r : Rx C) (hr : isClock r = false) : rate C r z = 0 := by
    by_contra hn
    exact ht r hr ((enabled_iff C r z).mpr hn)
  have hxp : 0 < z (.extend e) := by
    rcases hz.progress with hi | hx
    · have hzero : z (.extend e) = 0 := by
        rcases hz.exclusive with hi' | hx'
        · omega
        · exact hx'
      have hc := hz.control
      have hold : 0 < z (.third (.inr e)) := by omega
      have hn := noRate (.startExtension e) rfl
      simp only [rate, sourceLeft, sourceRight, mul_eq_zero] at hn
      omega
    · exact hx
  have hi : z .signal = 0 := by
    rcases hz.exclusive with hi | hx
    · exact hi
    · omega
  have hold : z (.third (.inr e)) = 0 := by
    have hn := noRate (.growExtension e) rfl
    simp only [rate, sourceLeft, sourceRight, mul_eq_zero] at hn
    omega
  have substrateZero (r : Rx C) (hl : sourceLeft C r = .extend e)
      (hr : isClock r = false) : z (sourceRight C r) = 0 := by
    have hn := noRate r hr
    rw [rate, hl] at hn
    exact (mul_eq_zero.mp hn).resolve_left (ne_of_gt hxp)
  have hms : z (.mem .ms) = 0 := substrateZero (.extendRestoreM e) rfl rfl
  have hm : z (.mem .m) = 0 := substrateZero (.extendShift e) rfl rfl
  have hb : z (.mem .b) = 0 := substrateZero (.extendWrite e) rfl rfl
  have hts : z (.mem .ts) = 0 := substrateZero (.extendRestoreTs e) rfl rfl
  have hthreshold : z (.mem .t) = 0 := substrateZero (.extendRestoreT e) rfl rfl
  have hsize : z (.mem .d) = 0 := substrateZero (.extendD e) rfl rfl
  have ha : z .forward = 0 := substrateZero (.extendForward e) rfl rfl
  have hf : z .backward = 0 := substrateZero (.extendBackward e) rfl rfl
  simp [extensionRank, hi, hold, hms, hm, hb, hts, hthreshold, hsize, ha, hf]

def extensionStart (C : XCTM Q) (e : ExtendState C) (d v th a f : ℕ)
    (clocks : Fin 5 → ℕ) : State (Sp C)
  | .third u => if u = .inr e then d else 0
  | .signal => 1
  | .mem .m => v - min v th
  | .mem .ms => min v th
  | .mem .t => th - min v th
  | .mem .ts => min v th
  | .mem .d => d
  | .mem .b => 1
  | .forward => a
  | .backward => f
  | .clock c => clocks c
  | _ => 0

theorem extension_start_invariant (C : XCTM Q) (e : ExtendState C) (d v th a f : ℕ)
    (clocks : Fin 5 → ℕ) :
    ExtensionInvariant C e d v th a f (extensionStart C e d v th a f clocks) := by
  have hv := min_le_left v th
  have ht := min_le_right v th
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    cases s with
    | mem m => cases m <;> simp_all [ExtensionSpecies, extensionStart]
    | _ => simp_all [ExtensionSpecies, extensionStart]
  all_goals simp [extensionStart] <;> omega

def extensionFinal (C : XCTM Q) (e : ExtendState C) (d v th a f : ℕ)
    (clocks : Fin 5 → ℕ) : State (Sp C)
  | .extend e' => if e' = e then 3 * d else 0
  | .mem .md => 3 * v + 1
  | .mem .td => 3 * th
  | .mem .ds => 3 * d
  | .mem .bs => 1
  | .forwardLatent => a
  | .backwardLatent => f
  | .clock c => clocks c
  | _ => 0

theorem extension_terminal_normal
    (C : XCTM Q) (e : ExtendState C) (d v th a f : ℕ)
    (hd : 0 < d) (z : State (Sp C)) (hz : ExtensionInvariant C e d v th a f z)
    (ht : WorkTerminal C z) :
    z = extensionFinal C e d v th a f (fun c => z (.clock c)) := by
  have hrank := extension_terminal_rank_zero C e d v th a f hd z hz ht
  have hzero :
      z (.third (.inr e)) = 0 ∧ z .signal = 0 ∧
      z (.mem .b) = 0 ∧ z (.mem .d) = 0 ∧ z (.mem .m) = 0 ∧ z (.mem .ms) = 0 ∧
      z (.mem .t) = 0 ∧ z (.mem .ts) = 0 ∧ z .forward = 0 ∧ z .backward = 0 := by
    unfold extensionRank at hrank
    omega
  rcases hzero with ⟨hold, hi, hb, hdry, hm, hms, htzero, hts, ha, hf⟩
  have hx : z (.extend e) = 3 * d := by have h := hz.control; omega
  have hmd : z (.mem .md) = 3 * v + 1 := by have h := hz.memory; omega
  have htd : z (.mem .td) = 3 * th := by have h := hz.threshold; omega
  have hds : z (.mem .ds) = 3 * d := by have h := hz.size; omega
  have hbs : z (.mem .bs) = 1 := by have h := hz.button; omega
  have had : z .forwardLatent = a := by have h := hz.forward; omega
  have hfd : z .backwardLatent = f := by have h := hz.backward; omega
  funext s
  cases s with
  | first q => simpa [extensionFinal] using hz.support (.first q) (by simp [ExtensionSpecies])
  | second u => simpa [extensionFinal] using hz.support (.second u) (by simp [ExtensionSpecies])
  | third u =>
      by_cases hu : u = .inr e
      · subst u
        simpa [extensionFinal] using hold
      · simpa [extensionFinal] using hz.support (.third u) (by simpa [ExtensionSpecies] using hu)
  | reader q => simpa [extensionFinal] using hz.support (.reader q) (by simp [ExtensionSpecies])
  | write q b => simpa [extensionFinal] using hz.support (.write q b) (by simp [ExtensionSpecies])
  | extend e' =>
      by_cases he : e' = e
      · subst e'
        simpa [extensionFinal] using hx
      · simpa [extensionFinal, he] using
          hz.support (.extend e') (by simpa [ExtensionSpecies] using he)
  | signal => simpa [extensionFinal] using hi
  | clock c => rfl
  | forward => simpa [extensionFinal] using ha
  | forwardLatent => simpa [extensionFinal] using had
  | backward => simpa [extensionFinal] using hf
  | backwardLatent => simpa [extensionFinal] using hfd
  | mem m =>
      cases m with
      | m => simpa [extensionFinal] using hm
      | md => simpa [extensionFinal] using hmd
      | ms => simpa [extensionFinal] using hms
      | t => simpa [extensionFinal] using htzero
      | td => simpa [extensionFinal] using htd
      | ts => simpa [extensionFinal] using hts
      | d => simpa [extensionFinal] using hdry
      | ds => simpa [extensionFinal] using hds
      | b => simpa [extensionFinal] using hb
      | bs => simpa [extensionFinal] using hbs
      | k1 => simpa [extensionFinal] using hz.support (.mem .k1) (by simp [ExtensionSpecies])
      | k2 => simpa [extensionFinal] using hz.support (.mem .k2) (by simp [ExtensionSpecies])

theorem extension_work_closed (C : XCTM Q) (e : ExtendState C) (d v th a f : ℕ) :
    ∀ x y, ExtensionInvariant C e d v th a f x → WorkStep C x y →
      ExtensionInvariant C e d v th a f y := by
  rintro x y hx ⟨r, hr, he, rfl⟩
  exact extension_invariant_fire C e d v th a f x hx r
    (extension_enabled_label C e d v th a f x hx r hr he) he

theorem extension_work_decreases (C : XCTM Q) (e : ExtendState C) (d v th a f : ℕ) :
    ∀ x y, ExtensionInvariant C e d v th a f x → WorkStep C x y →
      extensionRank C e y < extensionRank C e x := by
  rintro x y hx ⟨r, hr, he, rfl⟩
  exact extension_rank_drop C e r
    (extension_enabled_label C e d v th a f x hx r hr he) x he

theorem extension_window_parameters (C : XCTM Q) (e : ExtendState C)
    (alpha d v th : ℕ) (hd : 0 < d) (z : State (Sp C))
    (hz : ExtensionInvariant C e d v th ((alpha + 1) * d) d z) :
    backwardCount C z ≤ d ∧
      (alpha : ℝ) / 3 ≤ (forwardCount C z : ℝ) / backwardCount C z := by
  have ha : forwardCount C z = (alpha + 1) * d := hz.forward
  have hf : backwardCount C z = d := hz.backward
  constructor
  · exact hf.le
  · apply ratio_bound
    · rw [hf]
      exact hd
    · rw [ha, hf]
      nlinarith

theorem extension_reachable_parameters (C : XCTM Q) (e : ExtendState C)
    (alpha d v th : ℕ) (hd : 0 < d) (clocks : Fin 5 → ℕ)
    {z : State (Sp C)}
    (hreach : WorkReach C
      (extensionStart C e d v th ((alpha + 1) * d) d clocks) z) :
    backwardCount C z ≤ d ∧
      (alpha : ℝ) / 3 ≤ (forwardCount C z : ℝ) / backwardCount C z := by
  have hz := workReach_invariant C
    (ExtensionInvariant C e d v th ((alpha + 1) * d) d)
    (extension_work_closed C e d v th ((alpha + 1) * d) d)
    hreach (extension_start_invariant C e d v th ((alpha + 1) * d) d clocks)
  exact extension_window_parameters C e alpha d v th hd z hz


/-! ## Buffer windows: the two inactive adjacent phases -/

inductive Buffer (C : XCTM Q) where
  | fromRead (q : ReadState C) (b : Bool) (w : List Bool) (a : ℕ)
  | fromExtension (e : ExtendState C) (w : List Bool) (a : ℕ)
  | toThird (q : ActiveState C) (w : List Bool) (a : ℕ)

def Buffer.before (C : XCTM Q) : Buffer C → Plan C
  | .fromRead q b w a => .write q b w a
  | .fromExtension e w a => .extend e w a
  | .toThird q w a => .second q w a

def Buffer.after (C : XCTM Q) (b : Buffer C) : Plan C :=
  Plan.advance C (Buffer.before C b)

def Buffer.old (C : XCTM Q) : Buffer C → Sp C
  | .fromRead q b _ _ => .write q b
  | .fromExtension e _ _ => .extend e
  | .toThird q _ _ => .second q

def Buffer.new (C : XCTM Q) : Buffer C → Sp C
  | .fromRead q b _ _ => .first (C.next q.val b).1
  | .fromExtension e _ _ => .first (extensionNext C e)
  | .toThird q _ _ => .third q

def Buffer.count (C : XCTM Q) (b : Buffer C) : ℕ :=
  stateCount (Buffer.before C b).tape.length

def Buffer.seed (C : XCTM Q) : Buffer C → Rx C
  | .fromRead q b _ _ => .finishWrite q b
  | .fromExtension e _ _ => .finishExtension e
  | .toThird q _ _ => .startThird q

def Buffer.grow (C : XCTM Q) : Buffer C → Rx C
  | .fromRead q b _ _ => .growFirstFromWrite q b
  | .fromExtension e _ _ => .growFirstFromExtension e
  | .toThird q _ _ => .growThird q

def BufferWindow (C : XCTM Q) (b : Buffer C) (z : State (Sp C)) : Prop :=
  OnlyControl C [Buffer.old C b, Buffer.new C b, .signal] z ∧
    z (Buffer.old C b) + z (Buffer.new C b) = Buffer.count C b ∧
    z .signal ≤ 1 ∧
    (z .signal = 1 ∨ 0 < z (Buffer.new C b)) ∧
    (z .signal = 0 ∨ z (Buffer.new C b) = 0) ∧
    ∀ s, ¬ s.IsControl → z s = Plan.workState C (Buffer.before C b) s

def bufferRank (C : XCTM Q) (b : Buffer C) (z : State (Sp C)) : ℕ :=
  z (Buffer.old C b) + z .signal

theorem buffer_start (C : XCTM Q) (b : Buffer C) :
    BufferWindow C b (Plan.workState C (Buffer.before C b) + unit .signal) := by
  cases b <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | (intro s hs hn; cases s <;>
        simp_all [Buffer.old, Buffer.new, Buffer.before, Plan.workState,
          payload, unit, Sp.IsControl])
    | (intro s hs; cases s <;>
        simp_all [Buffer.before, Plan.workState, payload, unit, Sp.IsControl])
    | simp [Buffer.old, Buffer.new, Buffer.count, Buffer.before, Plan.tape,
        Plan.workState, payload, unit]

private theorem buffer_old_control (C : XCTM Q) (b : Buffer C) :
    (Buffer.old C b).IsControl := by
  cases b <;> trivial

private theorem buffer_new_control (C : XCTM Q) (b : Buffer C) :
    (Buffer.new C b).IsControl := by
  cases b <;> trivial

private theorem buffer_old_ne_new (C : XCTM Q) (b : Buffer C) :
    Buffer.old C b ≠ Buffer.new C b := by
  cases b <;> simp [Buffer.old, Buffer.new]

private theorem buffer_old_ne_signal (C : XCTM Q) (b : Buffer C) :
    Buffer.old C b ≠ .signal := by
  cases b <;> simp [Buffer.old]

private theorem buffer_new_ne_signal (C : XCTM Q) (b : Buffer C) :
    Buffer.new C b ≠ .signal := by
  cases b <;> simp [Buffer.new]

private theorem buffer_seed_left (C : XCTM Q) (b : Buffer C) :
    sourceLeft C (Buffer.seed C b) = .signal := by
  cases b <;> rfl

private theorem buffer_seed_right (C : XCTM Q) (b : Buffer C) :
    sourceRight C (Buffer.seed C b) = Buffer.old C b := by
  cases b <;> rfl

private theorem buffer_seed_products (C : XCTM Q) (b : Buffer C) :
    products C (Buffer.seed C b) = unit (Buffer.new C b) := by
  cases b <;> rfl

private theorem buffer_grow_left (C : XCTM Q) (b : Buffer C) :
    sourceLeft C (Buffer.grow C b) = Buffer.old C b := by
  cases b <;> rfl

private theorem buffer_grow_right (C : XCTM Q) (b : Buffer C) :
    sourceRight C (Buffer.grow C b) = Buffer.new C b := by
  cases b <;> rfl

private theorem buffer_grow_products (C : XCTM Q) (b : Buffer C) :
    products C (Buffer.grow C b) = 2 • unit (Buffer.new C b) := by
  cases b <;> rfl

private theorem buffer_seed_old (C : XCTM Q) (b : Buffer C) (z : State (Sp C)) :
    (rxn C (Buffer.seed C b)).fire z (Buffer.old C b) =
      z (Buffer.old C b) - 1 := by
  rw [fire_apply, buffer_seed_left, buffer_seed_right, buffer_seed_products]
  simp [unit, buffer_old_ne_signal, buffer_old_ne_new]

private theorem buffer_seed_new (C : XCTM Q) (b : Buffer C) (z : State (Sp C)) :
    (rxn C (Buffer.seed C b)).fire z (Buffer.new C b) =
      z (Buffer.new C b) + 1 := by
  rw [fire_apply, buffer_seed_left, buffer_seed_right, buffer_seed_products]
  simp [unit, buffer_new_ne_signal, (buffer_old_ne_new C b).symm]

private theorem buffer_seed_signal (C : XCTM Q) (b : Buffer C) (z : State (Sp C)) :
    (rxn C (Buffer.seed C b)).fire z .signal = z .signal - 1 := by
  rw [fire_apply, buffer_seed_left, buffer_seed_right, buffer_seed_products]
  simp [unit, (buffer_old_ne_signal C b).symm, (buffer_new_ne_signal C b).symm]

private theorem buffer_grow_old (C : XCTM Q) (b : Buffer C) (z : State (Sp C)) :
    (rxn C (Buffer.grow C b)).fire z (Buffer.old C b) =
      z (Buffer.old C b) - 1 := by
  rw [fire_apply, buffer_grow_left, buffer_grow_right, buffer_grow_products]
  simp [unit, buffer_old_ne_new, Pi.smul_apply]

private theorem buffer_grow_new (C : XCTM Q) (b : Buffer C) (z : State (Sp C)) :
    (rxn C (Buffer.grow C b)).fire z (Buffer.new C b) =
      z (Buffer.new C b) - 1 + 2 := by
  rw [fire_apply, buffer_grow_left, buffer_grow_right, buffer_grow_products]
  simp [unit, (buffer_old_ne_new C b).symm, Pi.smul_apply]

private theorem buffer_grow_signal (C : XCTM Q) (b : Buffer C) (z : State (Sp C)) :
    (rxn C (Buffer.grow C b)).fire z .signal = z .signal := by
  rw [fire_apply, buffer_grow_left, buffer_grow_right, buffer_grow_products]
  simp [unit, (buffer_old_ne_signal C b).symm,
    (buffer_new_ne_signal C b).symm, Pi.smul_apply]

private theorem buffer_seed_passive (C : XCTM Q) (b : Buffer C) (z : State (Sp C))
    (s : Sp C) (hs : ¬ s.IsControl) :
    (rxn C (Buffer.seed C b)).fire z s = z s := by
  have ho : s ≠ Buffer.old C b := by
    intro he
    subst s
    exact hs (buffer_old_control C b)
  have hn : s ≠ Buffer.new C b := by
    intro he
    subst s
    exact hs (buffer_new_control C b)
  have hi : s ≠ .signal := by
    intro he
    subst s
    exact hs (by trivial)
  rw [fire_apply, buffer_seed_left, buffer_seed_right, buffer_seed_products]
  simp only [unit_apply, if_neg ho, if_neg hn, if_neg hi,
    zero_add, Nat.sub_zero, add_zero]

private theorem buffer_grow_passive (C : XCTM Q) (b : Buffer C) (z : State (Sp C))
    (s : Sp C) (hs : ¬ s.IsControl) :
    (rxn C (Buffer.grow C b)).fire z s = z s := by
  have ho : s ≠ Buffer.old C b := by
    intro he
    subst s
    exact hs (buffer_old_control C b)
  have hn : s ≠ Buffer.new C b := by
    intro he
    subst s
    exact hs (buffer_new_control C b)
  rw [fire_apply, buffer_grow_left, buffer_grow_right, buffer_grow_products]
  simp [unit, ho, hn, Pi.smul_apply]

private theorem buffer_payload_control (C : XCTM Q) (c : Sp C) (d a : ℕ)
    (latent : Bool) (m : Mem → ℕ) (s : Sp C) (hs : s.IsControl) :
    payload C c d a latent m s = if s = c then d else 0 := by
  cases s <;> simp_all only [Sp.IsControl, payload]

private theorem buffer_payload_passive (C : XCTM Q) (c c' : Sp C) (d a : ℕ)
    (latent : Bool) (m : Mem → ℕ) (s : Sp C) (hs : ¬ s.IsControl) :
    payload C c d a latent m s = payload C c' d a latent m s := by
  cases s <;> simp_all only [Sp.IsControl, payload, not_true_eq_false]

private theorem buffer_after_control (C : XCTM Q) (b : Buffer C)
    (s : Sp C) (hs : s.IsControl) :
    Plan.workState C (Buffer.after C b) s =
      if s = Buffer.new C b then Buffer.count C b else 0 := by
  cases b <;>
    exact buffer_payload_control C _ _ _ _ _ s hs

private theorem buffer_after_passive (C : XCTM Q) (b : Buffer C)
    (s : Sp C) (hs : ¬ s.IsControl) :
    Plan.workState C (Buffer.before C b) s =
      Plan.workState C (Buffer.after C b) s := by
  cases b <;>
    exact buffer_payload_passive C _ _ _ _ _ _ s hs

private theorem buffer_enabled_fromRead (C : XCTM Q)
    (q : ReadState C) (bit : Bool) (w : List Bool) (a : ℕ) {z : State (Sp C)} {r : Rx C}
    (h : BufferWindow C (.fromRead q bit w a) z)
    (hc : isClock r = false) (he : (rxn C r).enabled z) :
    r = Buffer.seed C (.fromRead q bit w a) ∨ r = Buffer.grow C (.fromRead q bit w a) := by
  rcases h with ⟨ho, hcount, hi, hprogress, hexclusive, hpassive⟩
  obtain ⟨hl, hr⟩ := enabled_control_support C ho he
  have hp := (enabled_iff C r z).mp he
  simp only [rate, ne_eq, mul_eq_zero, not_or] at hp
  have hm (m : Mem) :
      z (.mem m) = Plan.workState C (Buffer.before C (.fromRead q bit w a)) (.mem m) :=
    hpassive _ (by simp only [Sp.IsControl, not_false_eq_true])
  have ha : z .forward =
      Plan.workState C (Buffer.before C (.fromRead q bit w a)) .forward :=
    hpassive _ (by simp only [Sp.IsControl, not_false_eq_true])
  have had : z .forwardLatent =
      Plan.workState C (Buffer.before C (.fromRead q bit w a)) .forwardLatent :=
    hpassive _ (by simp only [Sp.IsControl, not_false_eq_true])
  have hf : z .backward =
      Plan.workState C (Buffer.before C (.fromRead q bit w a)) .backward :=
    hpassive _ (by simp only [Sp.IsControl, not_false_eq_true])
  have hfd : z .backwardLatent =
      Plan.workState C (Buffer.before C (.fromRead q bit w a)) .backwardLatent :=
    hpassive _ (by simp only [Sp.IsControl, not_false_eq_true])
  have hpair : z (.mem .t) * z (.mem .m) = 0 := by
    rw [hm, hm]
    simp [Buffer.before, Plan.workState, payload, storedMemory,
      comparedMemory, comparison_zero_product]
  have hpairs := mul_eq_zero.mp hpair
  clear ho hcount hi hprogress hpassive he hpair
  simp only [Buffer.before, Plan.workState, payload] at hm ha had hf hfd
  cases r <;>
    simp_all [Buffer.old, Buffer.new, Buffer.seed, Buffer.grow,
      sourceLeft, sourceRight, isClock, Sp.IsControl,
      storedMemory, comparedMemory] <;> omega

private theorem buffer_enabled_fromExtension (C : XCTM Q)
    (e : ExtendState C) (w : List Bool) (a : ℕ) {z : State (Sp C)} {r : Rx C}
    (h : BufferWindow C (.fromExtension e w a) z)
    (hc : isClock r = false) (he : (rxn C r).enabled z) :
    r = Buffer.seed C (.fromExtension e w a) ∨ r = Buffer.grow C (.fromExtension e w a) := by
  rcases h with ⟨ho, hcount, hi, hprogress, hexclusive, hpassive⟩
  obtain ⟨hl, hr⟩ := enabled_control_support C ho he
  have hp := (enabled_iff C r z).mp he
  simp only [rate, ne_eq, mul_eq_zero, not_or] at hp
  have hm (m : Mem) :
      z (.mem m) = Plan.workState C (Buffer.before C (.fromExtension e w a)) (.mem m) :=
    hpassive _ (by simp only [Sp.IsControl, not_false_eq_true])
  have ha : z .forward =
      Plan.workState C (Buffer.before C (.fromExtension e w a)) .forward :=
    hpassive _ (by simp only [Sp.IsControl, not_false_eq_true])
  have had : z .forwardLatent =
      Plan.workState C (Buffer.before C (.fromExtension e w a)) .forwardLatent :=
    hpassive _ (by simp only [Sp.IsControl, not_false_eq_true])
  have hf : z .backward =
      Plan.workState C (Buffer.before C (.fromExtension e w a)) .backward :=
    hpassive _ (by simp only [Sp.IsControl, not_false_eq_true])
  have hfd : z .backwardLatent =
      Plan.workState C (Buffer.before C (.fromExtension e w a)) .backwardLatent :=
    hpassive _ (by simp only [Sp.IsControl, not_false_eq_true])
  have hpair : z (.mem .t) * z (.mem .m) = 0 := by
    rw [hm, hm]
    simp [Buffer.before, Plan.workState, payload, storedMemory,
      comparedMemory, comparison_zero_product]
  have hpairs := mul_eq_zero.mp hpair
  clear ho hcount hi hprogress hpassive he hpair
  simp only [Buffer.before, Plan.workState, payload] at hm ha had hf hfd
  cases r <;>
    simp_all [Buffer.old, Buffer.new, Buffer.seed, Buffer.grow,
      sourceLeft, sourceRight, isClock, Sp.IsControl,
      storedMemory, comparedMemory] <;> omega

private theorem buffer_enabled_toThird (C : XCTM Q)
    (q : ActiveState C) (w : List Bool) (a : ℕ) {z : State (Sp C)} {r : Rx C}
    (h : BufferWindow C (.toThird q w a) z)
    (hc : isClock r = false) (he : (rxn C r).enabled z) :
    r = Buffer.seed C (.toThird q w a) ∨ r = Buffer.grow C (.toThird q w a) := by
  rcases h with ⟨ho, hcount, hi, hprogress, hexclusive, hpassive⟩
  obtain ⟨hl, hr⟩ := enabled_control_support C ho he
  have hp := (enabled_iff C r z).mp he
  simp only [rate, ne_eq, mul_eq_zero, not_or] at hp
  have hm (m : Mem) :
      z (.mem m) = Plan.workState C (Buffer.before C (.toThird q w a)) (.mem m) :=
    hpassive _ (by simp only [Sp.IsControl, not_false_eq_true])
  have ha : z .forward =
      Plan.workState C (Buffer.before C (.toThird q w a)) .forward :=
    hpassive _ (by simp only [Sp.IsControl, not_false_eq_true])
  have had : z .forwardLatent =
      Plan.workState C (Buffer.before C (.toThird q w a)) .forwardLatent :=
    hpassive _ (by simp only [Sp.IsControl, not_false_eq_true])
  have hf : z .backward =
      Plan.workState C (Buffer.before C (.toThird q w a)) .backward :=
    hpassive _ (by simp only [Sp.IsControl, not_false_eq_true])
  have hfd : z .backwardLatent =
      Plan.workState C (Buffer.before C (.toThird q w a)) .backwardLatent :=
    hpassive _ (by simp only [Sp.IsControl, not_false_eq_true])
  have hpair : z (.mem .t) * z (.mem .m) = 0 := by
    rw [hm, hm]
    simp [Buffer.before, Plan.workState, payload, storedMemory,
      comparedMemory, comparison_zero_product]
  have hpairs := mul_eq_zero.mp hpair
  clear ho hcount hi hprogress hpassive he hpair
  simp only [Buffer.before, Plan.workState, payload] at hm ha had hf hfd
  cases r <;>
    simp_all [Buffer.old, Buffer.new, Buffer.seed, Buffer.grow,
      sourceLeft, sourceRight, isClock, Sp.IsControl,
      storedMemory, comparedMemory] <;> omega

theorem buffer_enabled (C : XCTM Q) {b : Buffer C} {z : State (Sp C)}
    {r : Rx C} (h : BufferWindow C b z)
    (hc : isClock r = false) (he : (rxn C r).enabled z) :
    r = Buffer.seed C b ∨ r = Buffer.grow C b := by
  cases b with
  | fromRead q bit w a => exact buffer_enabled_fromRead C q bit w a h hc he
  | fromExtension e w a => exact buffer_enabled_fromExtension C e w a h hc he
  | toThird q w a => exact buffer_enabled_toThird C q w a h hc he

private theorem buffer_seed_window (C : XCTM Q) {b : Buffer C} {z : State (Sp C)}
    (h : BufferWindow C b z) (he : (rxn C (Buffer.seed C b)).enabled z) :
    BufferWindow C b ((rxn C (Buffer.seed C b)).fire z) ∧
      bufferRank C b ((rxn C (Buffer.seed C b)).fire z) < bufferRank C b z := by
  rcases h with ⟨ho, hcount, hi, hprogress, hexclusive, hpassive⟩
  have hp := (enabled_iff C (Buffer.seed C b) z).mp he
  rw [rate, buffer_seed_left, buffer_seed_right] at hp
  have hp' : z .signal ≠ 0 ∧ z (Buffer.old C b) ≠ 0 := by
    simpa only [ne_eq, mul_eq_zero, not_or] using hp
  have ho' := OnlyControl.fire ho (Buffer.seed C b) (by
    intro s _ hn
    have hsn : s ≠ Buffer.new C b := by
      intro heq
      subst s
      exact hn (by simp)
    rw [buffer_seed_products]
    exact if_neg hsn)
  constructor
  · refine ⟨ho', ?_, ?_, ?_, ?_, ?_⟩
    · rw [buffer_seed_old, buffer_seed_new]
      omega
    · rw [buffer_seed_signal]
      omega
    · rw [buffer_seed_signal, buffer_seed_new]
      omega
    · rw [buffer_seed_signal, buffer_seed_new]
      omega
    · intro s hs
      rw [buffer_seed_passive C b z s hs]
      exact hpassive s hs
  · simp only [bufferRank, buffer_seed_old, buffer_seed_signal]
    omega

private theorem buffer_grow_window (C : XCTM Q) {b : Buffer C} {z : State (Sp C)}
    (h : BufferWindow C b z) (he : (rxn C (Buffer.grow C b)).enabled z) :
    BufferWindow C b ((rxn C (Buffer.grow C b)).fire z) ∧
      bufferRank C b ((rxn C (Buffer.grow C b)).fire z) < bufferRank C b z := by
  rcases h with ⟨ho, hcount, hi, hprogress, hexclusive, hpassive⟩
  have hp := (enabled_iff C (Buffer.grow C b) z).mp he
  rw [rate, buffer_grow_left, buffer_grow_right] at hp
  have hp' : z (Buffer.old C b) ≠ 0 ∧ z (Buffer.new C b) ≠ 0 := by
    simpa only [ne_eq, mul_eq_zero, not_or] using hp
  have ho' := OnlyControl.fire ho (Buffer.grow C b) (by
    intro s _ hn
    have hsn : s ≠ Buffer.new C b := by
      intro heq
      subst s
      exact hn (by simp)
    rw [buffer_grow_products]
    simp [unit, hsn, Pi.smul_apply])
  constructor
  · refine ⟨ho', ?_, ?_, ?_, ?_, ?_⟩
    · rw [buffer_grow_old, buffer_grow_new]
      omega
    · rw [buffer_grow_signal]
      exact hi
    · rw [buffer_grow_signal, buffer_grow_new]
      omega
    · rw [buffer_grow_signal, buffer_grow_new]
      omega
    · intro s hs
      rw [buffer_grow_passive C b z s hs]
      exact hpassive s hs
  · simp only [bufferRank, buffer_grow_old, buffer_grow_signal]
    omega

theorem buffer_fire (C : XCTM Q) {b : Buffer C} {z : State (Sp C)}
    {r : Rx C} (h : BufferWindow C b z)
    (hc : isClock r = false) (he : (rxn C r).enabled z) :
    BufferWindow C b ((rxn C r).fire z) ∧
      bufferRank C b ((rxn C r).fire z) < bufferRank C b z := by
  rcases buffer_enabled C h hc he with hr | hr
  · subst r
    exact buffer_seed_window C h he
  · subst r
    exact buffer_grow_window C h he

theorem buffer_terminal_normal (C : XCTM Q) {b : Buffer C}
    {z : State (Sp C)} (h : BufferWindow C b z) (ht : WorkTerminal C z) :
    z = Plan.workState C (Buffer.after C b) := by
  rcases h with ⟨ho, hcount, hi, hprogress, hexclusive, hpassive⟩
  have hpositive : 0 < Buffer.count C b := by
    unfold Buffer.count stateCount
    positivity
  have hz := (workTerminal_iff C z).mp ht
  have hs : isClock (Buffer.seed C b) = false := by cases b <;> rfl
  have hg : isClock (Buffer.grow C b) = false := by cases b <;> rfl
  have hseed := hz (Buffer.seed C b) hs
  have hgrow := hz (Buffer.grow C b) hg
  have hseed' : z .signal * z (Buffer.old C b) = 0 := by
    simpa only [rate, buffer_seed_left, buffer_seed_right] using hseed
  have hgrow' : z (Buffer.old C b) * z (Buffer.new C b) = 0 := by
    simpa only [rate, buffer_grow_left, buffer_grow_right] using hgrow
  have hseedcases := mul_eq_zero.mp hseed'
  have hgrowcases := mul_eq_zero.mp hgrow'
  have hnpositive : 0 < z (Buffer.new C b) := by omega
  have hold : z (Buffer.old C b) = 0 := by omega
  have hsignal : z .signal = 0 := by omega
  have hnew : z (Buffer.new C b) = Buffer.count C b := by omega
  have honly : OnlyControl C [Buffer.new C b] z := by
    intro s hs hn
    by_cases he : s = Buffer.old C b
    · simpa only [he] using hold
    by_cases hi : s = .signal
    · simpa only [hi] using hsignal
    exact ho s hs (by simpa [he, hi] using hn)
  funext s
  by_cases hs : s.IsControl
  · rw [buffer_after_control C b s hs]
    by_cases he : s = Buffer.new C b
    · subst s
      simpa only [if_pos rfl] using hnew
    · rw [if_neg he]
      exact honly s hs (by simpa only [List.mem_singleton] using he)
  · exact (hpassive s hs).trans (buffer_after_passive C b s hs)

theorem buffer_normalization (C : XCTM Q) (b : Buffer C) :
    WorkReach C (Plan.workState C (Buffer.before C b) + unit .signal)
      (Plan.workState C (Buffer.after C b)) ∧
    ∀ z, WorkReach C
        (Plan.workState C (Buffer.before C b) + unit .signal) z →
      WorkTerminal C z → z = Plan.workState C (Buffer.after C b) := by
  have hc : ∀ x y, BufferWindow C b x → WorkStep C x y → BufferWindow C b y := by
    intro x y hx hxy
    rcases hxy with ⟨r, hr, he, rfl⟩
    exact (buffer_fire C hx hr he).1
  have hd : ∀ x y, BufferWindow C b x → WorkStep C x y →
      bufferRank C b y < bufferRank C b x := by
    intro x y hx hxy
    rcases hxy with ⟨r, hr, he, rfl⟩
    exact (buffer_fire C hx hr he).2
  obtain ⟨z, hz, hi, ht⟩ :=
    work_reaches_terminal C (BufferWindow C b) (bufferRank C b) hc hd (buffer_start C b)
  have heq := buffer_terminal_normal C hi ht
  constructor
  · simpa only [heq] using hz
  · intro z hz ht
    exact buffer_terminal_normal C
      (workReach_invariant C (BufferWindow C b) hc hz (buffer_start C b)) ht


/-! ## Assembly of the deterministic windows -/

@[simp] theorem workView_payload (C : XCTM Q) (c : Sp C) (d a : ℕ)
    (latent : Bool) (m : Mem → ℕ) :
    workView C (payload C c d a latent m) = payload C c d a latent m := by
  funext s
  cases s <;> rfl

@[simp] theorem workView_planState (C : XCTM Q) (p : Plan C) :
    workView C (Plan.workState C p) = Plan.workState C p := by
  cases p <;> exact workView_payload C _ _ _ _ _

/-- This is constructed below from reaction-by-reaction proofs, not assumed
as a hypothesis of a stochastic headline. -/
structure WorkCertificate (C : XCTM Q) (start target : State (Sp C)) where
  inv : State (Sp C) → Prop
  rank : State (Sp C) → ℕ
  initial : inv start
  closed : ∀ x y, inv x → WorkStep C x y → inv y
  decreases : ∀ x y, inv x → WorkStep C x y → rank y < rank x
  terminal : ∀ z, inv z → WorkTerminal C z → workView C z = target

theorem WorkCertificate.normalization (C : XCTM Q) {start target : State (Sp C)}
    (P : WorkCertificate C start target) :
    (∃ y, WorkReach C start y ∧ WorkTerminal C y ∧ workView C y = target) ∧
    (∀ y, WorkReach C start y → WorkTerminal C y → workView C y = target) ∧
    (∀ z : ℕ → State (Sp C), z 0 = start →
      ¬ ∀ j, WorkStep C (z j) (z (j + 1))) := by
  obtain ⟨y, hy, hi, ht⟩ :=
    work_reaches_terminal C P.inv P.rank P.closed P.decreases P.initial
  refine ⟨⟨y, hy, ht, P.terminal y hi ht⟩, ?_, ?_⟩
  · intro y hy ht
    exact P.terminal y (workReach_invariant C P.inv P.closed hy P.initial) ht
  · intro z hz
    apply no_infinite_work_run C P.inv P.rank P.closed P.decreases z
    simpa only [hz] using P.initial

def bufferCertificate (C : XCTM Q) (b : Buffer C) :
    WorkCertificate C
      (Plan.workState C (Buffer.before C b) + unit .signal)
      (Plan.workState C (Buffer.after C b)) where
  inv := BufferWindow C b
  rank := bufferRank C b
  initial := buffer_start C b
  closed := by
    rintro x y hx ⟨r, hr, he, rfl⟩
    exact (buffer_fire C hx hr he).1
  decreases := by
    rintro x y hx ⟨r, hr, he, rfl⟩
    exact (buffer_fire C hx hr he).2
  terminal := by
    intro z hz ht
    rw [buffer_terminal_normal C hz ht, workView_planState]

def restoreCertificate (C : XCTM Q) (q : ActiveState C)
    (w : List Bool) (a : ℕ) (latent : Bool) (hs : 3 ≤ w.length) :
    WorkCertificate C
      (payload C (.first (activeControl C q)) (stateCount w.length)
        a latent (storedMemory w) + unit .signal)
      (payload C (.second q) (stateCount w.length) (a + 1) false (comparedMemory w)) where
  inv := RestoreWindow C q (stateCount w.length) (threshold w.length) (tval w) a
  rank := restoreRank C q
  initial := restore_start C q w a latent (fun _ => stateCount_div_exact w.length hs)
  closed := restore_closed C q (stateCount w.length) (threshold w.length) (tval w) a
  decreases := restore_decreases C q (stateCount w.length) (threshold w.length) (tval w) a
  terminal := fun _ hz ht => restore_terminal_payload C w hz ht

def readCertificate (C : XCTM Q) (q : ReadState C)
    (w : List Bool) (a : ℕ) (hs : 3 ≤ w.length) :
    WorkCertificate C
      (Plan.workState C (.third (.inl q) w a) + unit .signal)
      (Plan.workState C (Plan.advance C (.third (.inl q) w a))) := by
  let b := w.headD false
  let w' := w.tail ++ [(C.next q.val b).2]
  have hlen : w'.length = w.length := read_length w (by omega) _
  have hnext :
      tval w' + 3 * bw b * stateCount w.length =
        3 * tval w + bw (C.next q.val b).2 :=
    read_value w hs _
  have hm : 0 < stateCount w.length := by unfold stateCount; positivity
  have hg : 0 < 2 * 3 ^ (w.length - 3) := by positivity
  have hx : 0 < tval w' := by
    have hh := (tape_facts (n := w.length - 3) (w := w) (by omega)
      (C.next q.val b).2).2.2.2.1
    have hpow : 0 < 9 * 3 ^ (w.length - 3) := by positivity
    change 9 * 3 ^ (w.length - 3) ≤ tval w' at hh
    omega
  refine
    { inv := fun z =>
        ReadWindow C (stateCount w.length) (threshold w.length)
          (2 * 3 ^ (w.length - 3)) q b (tval w) (tval w') z ∧
        readFuel C z = (a * stateCount w.length, 0, stateCount w.length, 0)
      rank := readRank C q
      initial := ?_
      closed := ?_
      decreases := ?_
      terminal := ?_ }
  · exact ⟨read_start_from_payload C q w a hs,
      by simp [Plan.workState, readFuel, payload, unit]⟩
  · rintro x y ⟨hW, hF⟩ ⟨r, hr, he, rfl⟩
    exact ⟨(read_window_fire C hnext hW r hr he).1,
      (read_fuel_fire C hW r hr he).trans hF⟩
  · rintro x y ⟨hW, hF⟩ ⟨r, hr, he, rfl⟩
    exact (read_window_fire C hnext hW r hr he).2
  · rintro z ⟨hW, hF⟩ ht
    have hN := read_terminal_normal C hm hg hx hW ht
    have hN' : ReadNormal C (stateCount w'.length) (threshold w'.length)
        q b (tval w') z := by simpa only [hlen] using hN
    have hF' : readFuel C z =
        (a * stateCount w'.length, 0, stateCount w'.length, 0) := by
      simpa only [hlen] using hF
    exact read_normal_payload C q b w' a z hN' hF'

theorem extension_start_payload (C : XCTM Q) (e : ExtendState C)
    (w : List Bool) (a : ℕ) :
    extensionStart C e (stateCount w.length) (tval w) (threshold w.length)
      (a * stateCount w.length) (stateCount w.length) (fun _ => 0) =
    Plan.workState C (.third (.inr e) w a) + unit .signal := by
  funext s
  cases s with
  | mem m => cases m <;>
      simp [extensionStart, Plan.workState, payload, comparedMemory, unit]
  | _ => simp [extensionStart, Plan.workState, payload, comparedMemory, unit]

theorem extension_final_payload (C : XCTM Q) (e : ExtendState C)
    (w : List Bool) (a : ℕ) (hs : 3 ≤ w.length) (clocks : Fin 5 → ℕ) :
    workView C (extensionFinal C e (stateCount w.length) (tval w) (threshold w.length)
      (a * stateCount w.length) (stateCount w.length) clocks) =
      Plan.workState C (.extend e (w ++ [false]) a) := by
  have hd := stateCount_succ w.length (by omega)
  have ht := threshold_succ w.length hs
  funext s
  cases s with
  | mem m => cases m <;>
      simp [workView, extensionFinal, Plan.workState, payload, storedMemory,
        List.length_append, extension_value, hd, ht]
  | _ =>
      simp [workView, extensionFinal, Plan.workState, payload, storedMemory,
        List.length_append, extension_value, hd, ht]

def extensionCertificate (C : XCTM Q) (e : ExtendState C)
    (w : List Bool) (a : ℕ) (hs : 3 ≤ w.length) :
    WorkCertificate C
      (Plan.workState C (.third (.inr e) w a) + unit .signal)
      (Plan.workState C (Plan.advance C (.third (.inr e) w a))) where
  inv := ExtensionInvariant C e (stateCount w.length) (tval w) (threshold w.length)
    (a * stateCount w.length) (stateCount w.length)
  rank := extensionRank C e
  initial := by
    rw [← extension_start_payload]
    exact extension_start_invariant C e _ _ _ _ _ (fun _ => 0)
  closed := extension_work_closed C e _ _ _ _ _
  decreases := extension_work_decreases C e _ _ _ _ _
  terminal := by
    intro z hz ht
    have hd : 0 < stateCount w.length := by unfold stateCount; positivity
    rw [extension_terminal_normal C e _ _ _ _ _ hd z hz ht]
    exact extension_final_payload C e w a hs _

/-- All nonhalting window certificates are constructed from the actual network. -/
def planCertificate (C : XCTM Q) (p : Plan C) (hs : 3 ≤ p.tape.length)
    (hh : Plan.halted C p = false) :
    WorkCertificate C (Plan.workState C p + unit .signal)
      (Plan.workState C (Plan.advance C p)) := by
  cases p with
  | first q w a latent =>
      cases hm : C.mode q with
      | read =>
          rw [Plan.advance_first_read C q w a latent hm]
          exact restoreCertificate C (.inl ⟨q, hm⟩) w a latent hs
      | extend q' =>
          rw [Plan.advance_first_extend C q q' w a latent hm]
          exact restoreCertificate C (.inr ⟨q, ⟨q', hm⟩⟩) w a latent hs
      | halt =>
          simp [Plan.halted, hm] at hh
  | second q w a =>
      exact bufferCertificate C (.toThird q w a)
  | third q w a =>
      cases q with
      | inl q => exact readCertificate C q w a hs
      | inr e => exact extensionCertificate C e w a hs
  | write q b w a => exact bufferCertificate C (.fromRead q b w a)
  | extend e w a => exact bufferCertificate C (.fromExtension e w a)

/-- Lemma 8.1, with the halting exception made explicit. Existence and uniqueness
refer to actual enabled work firings; the last clause excludes every infinite
work-only computation. It does not assert that a stochastic clock must tick. -/
theorem next_window_normalization (C : XCTM Q) (p : Plan C)
    (hs : 3 ≤ p.tape.length) (hh : Plan.halted C p = false) :
    (∃ y, WorkReach C (Plan.workState C p + unit .signal) y ∧
      WorkTerminal C y ∧ workView C y = Plan.workState C (Plan.advance C p)) ∧
    (∀ y, WorkReach C (Plan.workState C p + unit .signal) y →
      WorkTerminal C y → workView C y = Plan.workState C (Plan.advance C p)) ∧
    (∀ z : ℕ → State (Sp C), z 0 = Plan.workState C p + unit .signal →
      ¬ ∀ j, WorkStep C (z j) (z (j + 1))) :=
  WorkCertificate.normalization C (planCertificate C p hs hh)


/-! ## Clock erasure and halted configurations -/

theorem work_enabled_view (C : XCTM Q) (r : Rx C) (z : State (Sp C))
    (hr : isClock r = false) :
    (rxn C r).enabled (workView C z) ↔ (rxn C r).enabled z := by
  cases r <;>
    simp_all [isClock, enabled_iff, rate, sourceLeft, sourceRight, workView]

theorem work_fire_view (C : XCTM Q) (r : Rx C) (z : State (Sp C))
    (hr : isClock r = false) :
    workView C ((rxn C r).fire z) = (rxn C r).fire (workView C z) := by
  cases r <;> simp [isClock] at hr
  all_goals
    funext s
    cases s <;>
      simp [workView, fire_apply, sourceLeft, sourceRight, products, unit,
        Pi.add_apply, Pi.smul_apply]

theorem clock_move_workView (C : XCTM Q) (r : Rx C) (z : State (Sp C))
    (hc : isClock r = true) (hnt : isTick r = false) (he : (rxn C r).enabled z) :
    workView C ((rxn C r).fire z) = workView C z := by
  have hp := enabled_sources_positive C r z he
  cases r with
  | up c latent =>
      cases latent <;> funext s
      all_goals cases s <;>
        simp [workView, fire_apply, sourceLeft, sourceRight, products, unit,
          Pi.add_apply, Pi.smul_apply] at hp ⊢ <;> omega
  | down c latent =>
      cases latent <;> funext s
      all_goals cases s <;>
        simp [workView, fire_apply, sourceLeft, sourceRight, products, unit,
          Pi.add_apply, Pi.smul_apply] at hp ⊢ <;> omega
  | tick latent => simp [isTick] at hnt
  | _ => simp [isClock] at hc

theorem tick_workView (C : XCTM Q) (latent : Bool) (z : State (Sp C))
    (he : (rxn C (.tick latent)).enabled z) :
    workView C ((rxn C (.tick latent)).fire z) = workView C z + unit (.signal : Sp C) := by
  have hp := enabled_sources_positive C (.tick latent) z he
  cases latent <;> funext s
  all_goals cases s <;>
    simp [workView, fire_apply, sourceLeft, sourceRight, products, unit,
      Pi.add_apply, Pi.smul_apply] at hp ⊢ <;> omega

theorem workTerminal_view (C : XCTM Q) (z : State (Sp C)) :
    WorkTerminal C (workView C z) ↔ WorkTerminal C z := by
  constructor
  · intro h r hr he
    exact h r hr ((work_enabled_view C r z hr).mpr he)
  · intro h r hr he
    exact h r hr ((work_enabled_view C r z hr).mp he)

@[simp] theorem cleanView_workView (C : XCTM Q) (halted : Bool) (z : State (Sp C)) :
    cleanView C halted (workView C z) = cleanView C halted z := by
  funext s
  cases s <;> rfl

theorem cleanView_false (C : XCTM Q) (z : State (Sp C)) :
    cleanView C false z = workView C z := by
  funext s
  cases s <;> rfl

@[simp] theorem cleanView_planState (C : XCTM Q) (halted : Bool) (p : Plan C) :
    cleanView C halted (Plan.workState C p) = Plan.workState C p := by
  cases p <;> funext s
  all_goals cases s <;> simp [cleanView, Plan.workState, payload]

theorem cleanView_eq_from_workView (C : XCTM Q) (p : Plan C) (z : State (Sp C))
    (h : workView C z = Plan.workState C p) :
    cleanView C (Plan.halted C p) z = Plan.workState C p := by
  have he := congrArg (cleanView C (Plan.halted C p)) h
  simpa only [cleanView_workView, cleanView_planState] using he

theorem cleanView_true_add_signal (C : XCTM Q) (z : State (Sp C)) :
    cleanView C true (z + unit .signal) = cleanView C true z := by
  funext s
  cases s <;> simp [cleanView, unit]

theorem initial_workView (C : XCTM Q) (i₀ : ℕ) (w : List Bool) :
    workView C (initial C i₀ w) = gamma C i₀ w 0 := by
  funext s
  cases s with
  | mem m => cases m <;> rfl
  | _ => simp [workView, gamma, plan, Plan.iterate, Plan.workState,
      payload, storedMemory, initial]

theorem Plan.advance_fixed_of_halted (C : XCTM Q) (p : Plan C)
    (hh : Plan.halted C p = true) : Plan.advance C p = p := by
  cases p with
  | first q w a latent =>
      cases hm : C.mode q with
      | read => simp [Plan.halted, hm] at hh
      | extend q' => simp [Plan.halted, hm] at hh
      | halt => exact Plan.advance_halt C q w a latent hm
  | _ => simp [Plan.halted] at hh

theorem activeControl_mode_ne_halt (C : XCTM Q) (q : ActiveState C) :
    C.mode (activeControl C q) ≠ .halt := by
  cases q with
  | inl q =>
      change C.mode q.val ≠ .halt
      rw [q.property]
      intro h
      cases h
  | inr e =>
      change C.mode e.val ≠ .halt
      rw [mode_extensionNext]
      intro h
      cases h

private theorem workTerminal_of_zero_work_sources
    (C : XCTM Q) (z : State (Sp C))
    (hfirst : ∀ r : ActiveState C, z (.first (activeControl C r)) = 0)
    (hsecond : ∀ r : ActiveState C, z (.second r) = 0)
    (hthird : ∀ r : ActiveState C, z (.third r) = 0)
    (hreader : ∀ r : ReadState C, z (.reader r) = 0)
    (hwrite : ∀ (r : ReadState C) (b : Bool), z (.write r b) = 0)
    (hextend : ∀ e : ExtendState C, z (.extend e) = 0)
    (ht : z (.mem .t) = 0)
    (hk1 : z (.mem .k1) = 0)
    (hk2 : z (.mem .k2) = 0) : WorkTerminal C z := by
  rw [workTerminal_iff]
  intro r hr
  cases r <;>
    simp [isClock, rate, sourceLeft, sourceRight, hfirst, hsecond,
      hthird, hreader, hwrite, hextend, ht, hk1, hk2] at hr ⊢

theorem halted_payload_terminal (C : XCTM Q) (q : Q) (w : List Bool)
    (a : ℕ) (latent : Bool) (signal : ℕ) (hh : C.mode q = .halt) :
    WorkTerminal C
      (Plan.workState C (.first q w a latent) + signal • unit .signal) := by
  have hactive (r : ActiveState C) : activeControl C r ≠ q := by
    intro h
    have hn := activeControl_mode_ne_halt C r
    rw [h, hh] at hn
    exact hn rfl
  refine workTerminal_of_zero_work_sources C _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r
    simp [Plan.workState, payload, unit, hactive r]
  · intro r
    simp [Plan.workState, payload, unit]
  · intro r
    simp [Plan.workState, payload, unit]
  · intro r
    simp [Plan.workState, payload, unit]
  · intro r b
    simp [Plan.workState, payload, unit]
  · intro e
    simp [Plan.workState, payload, unit]
  · simp [Plan.workState, payload, storedMemory, unit]
  · simp [Plan.workState, payload, storedMemory, unit]
  · simp [Plan.workState, payload, storedMemory, unit]

theorem halted_clean_terminal (C : XCTM Q) (p : Plan C) (z : State (Sp C))
    (hh : Plan.halted C p = true)
    (h : cleanView C true z = Plan.workState C p) : WorkTerminal C z := by
  cases p with
  | first q w a latent =>
      have hm : C.mode q = .halt := by
        cases he : C.mode q <;> simp_all [Plan.halted]
      have hw :
          workView C z = Plan.workState C (.first q w a latent) +
            z .signal • unit .signal := by
        funext s
        have he := congrFun h s
        cases s <;>
          simpa [cleanView, workView, Plan.workState, payload, unit] using he
      apply (workTerminal_view C z).mp
      rw [hw]
      exact halted_payload_terminal C q w a latent (z .signal) hm
  | _ => simp [Plan.halted] at hh


/-! ## The schedule follows the extensible machine -/

def extensionFlag (C : XCTM Q) (q : Q) : Bool :=
  match C.mode q with
  | .extend _ => true
  | _ => false

def previousExtension (C : XCTM Q) (w : List Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => extensionFlag C (C.runT (C.start, w) n).1

theorem Plan.four_windows (C : XCTM Q) (q : Q) (w : List Bool)
    (a : ℕ) (latent : Bool) (hw : w ≠ []) (hh : C.mode q ≠ .halt) :
    Plan.iterate C (.first q w a latent) 4 =
      .first (C.stepT (q, w)).1 (C.stepT (q, w)).2 (a + 1) (extensionFlag C q) := by
  change Plan.advance C
    (Plan.advance C
      (Plan.advance C
        (Plan.advance C (.first q w a latent)))) = _
  cases hm : C.mode q with
  | read =>
      rw [Plan.advance_first_read C q w a latent hm]
      cases w with
      | nil => exact False.elim (hw rfl)
      | cons b u =>
          simp [Plan.advance, XCTM.stepT, XCTM.step?,
            CTM.stepT, extensionFlag, hm]
  | extend q' =>
      rw [Plan.advance_first_extend C q q' w a latent hm]
      simp [Plan.advance, XCTM.stepT, XCTM.step?,
        extensionNext, extensionFlag, hm]
  | halt => exact False.elim (hh hm)

theorem Plan.three_windows_configuration (C : XCTM Q) (q : Q) (w : List Bool)
    (a : ℕ) (latent : Bool) (hw : w ≠ []) (hh : C.mode q ≠ .halt) :
    Plan.configuration C (Plan.iterate C (.first q w a latent) 3) = C.stepT (q, w) := by
  change Plan.configuration C
    (Plan.advance C
      (Plan.advance C
        (Plan.advance C (.first q w a latent)))) = _
  cases hm : C.mode q with
  | read =>
      rw [Plan.advance_first_read C q w a latent hm]
      cases w with
      | nil => exact False.elim (hw rfl)
      | cons b u =>
          simp [Plan.advance, Plan.configuration, XCTM.stepT,
            XCTM.step?, CTM.stepT, hm]
  | extend q' =>
      rw [Plan.advance_first_extend C q q' w a latent hm]
      simp [Plan.advance, Plan.configuration, XCTM.stepT,
        XCTM.step?, extensionNext, hm]
  | halt => exact False.elim (hh hm)

theorem plan_at_step (C : XCTM Q) (i₀ : ℕ) (w : List Bool)
    (hs : 3 ≤ w.length) (n : ℕ)
    (hbefore : ∀ j < n, C.mode (C.runT (C.start, w) j).1 ≠ .halt) :
    plan C i₀ w (4 * n) =
      .first (C.runT (C.start, w) n).1 (C.runT (C.start, w) n).2
        (i₀ + n) (previousExtension C w n) := by
  have hw : w ≠ [] := by
    intro h
    rw [h] at hs
    simp at hs
  revert hbefore
  induction n with
  | zero =>
      intro hbefore
      simp [plan, Plan.iterate, XCTM.runT, previousExtension]
  | succ n ih =>
      intro hbefore
      have hi := ih (fun j hj => hbefore j (by omega))
      have hn := XCTM.runT_ne_nil C (C.start, w) hw n
      change Plan.iterate C (.first C.start w i₀ false) (4 * (n + 1)) = _
      rw [Nat.mul_succ, Plan.iterate_add]
      change Plan.iterate C (plan C i₀ w (4 * n)) 4 = _
      rw [hi, Plan.four_windows C _ _ _ _ hn (hbefore n (by omega))]
      simp only [XCTM.runT, previousExtension, Nat.add_assoc]

/-- The fourth phase already encodes the next xCTM configuration through U/X.
This is the configuration present before tick 4(n+1). -/
theorem plan_at_tick_completion (C : XCTM Q) (i₀ : ℕ) (w : List Bool)
    (hs : 3 ≤ w.length) (n : ℕ)
    (hbefore : ∀ j ≤ n, C.mode (C.runT (C.start, w) j).1 ≠ .halt) :
    Plan.configuration C (plan C i₀ w (4 * n + 3)) =
      C.runT (C.start, w) (n + 1) := by
  have hw : w ≠ [] := by
    intro h
    rw [h] at hs
    simp at hs
  have hp := plan_at_step C i₀ w hs n (fun j hj => hbefore j (by omega))
  have hn := XCTM.runT_ne_nil C (C.start, w) hw n
  change Plan.configuration C
    (Plan.iterate C (.first C.start w i₀ false) (4 * n + 3)) = _
  rw [Plan.iterate_add]
  change Plan.configuration C (Plan.iterate C (plan C i₀ w (4 * n)) 3) = _
  rw [hp, Plan.three_windows_configuration C _ _ _ _ hn (hbefore n le_rfl)]
  rfl


/-! ## Raw-law paths, windows, error, and the unproved stochastic headlines -/

/-- Coordinate zero is the unused initial reaction mark. -/
abbrev LabelPath (C : XCTM Q) := ℕ → Option (Rx C)

noncomputable instance labelMeasurableSpace (C : XCTM Q) :
    MeasurableSpace (Option (Rx C)) :=
  Stochastic.MassAction.instMS (net C)

noncomputable def firedTick (C : XCTM Q) (z₀ : State (Sp C))
    (ω : LabelPath C) (j : ℕ) : Bool :=
  match pathFired (net C) z₀ ω j with
  | none => false
  | some r => isTick r

def TickAt (C : XCTM Q) (z₀ : State (Sp C))
    (ω : LabelPath C) (j : ℕ) : Prop := firedTick C z₀ ω j = true

open Classical in
noncomputable def tickCount (C : XCTM Q) (z₀ : State (Sp C))
    (ω : LabelPath C) : ℕ → ℕ
  | 0 => 0
  | j + 1 => tickCount C z₀ ω j + if TickAt C z₀ ω j then 1 else 0

theorem tickCount_mono (C : XCTM Q) (z₀ : State (Sp C)) (ω : LabelPath C) :
    Monotone (tickCount C z₀ ω) := by
  apply monotone_nat_of_le_succ
  intro j
  classical
  simp only [tickCount]
  split_ifs <;> omega

theorem tickCount_succ_le (C : XCTM Q) (z₀ : State (Sp C))
    (ω : LabelPath C) (j : ℕ) :
    tickCount C z₀ ω (j + 1) ≤ tickCount C z₀ ω j + 1 := by
  classical
  simp only [tickCount]
  split_ifs <;> omega

theorem tickCount_succ_of_tick (C : XCTM Q) (z₀ : State (Sp C))
    (ω : LabelPath C) (j : ℕ) (h : TickAt C z₀ ω j) :
    tickCount C z₀ ω (j + 1) = tickCount C z₀ ω j + 1 := by
  simp only [tickCount, if_pos h]

/-- Jump index j belongs to the work window with k preceding actual ticks. -/
def InWindow (C : XCTM Q) (z₀ : State (Sp C))
    (ω : LabelPath C) (k j : ℕ) : Prop := tickCount C z₀ ω j = k

def TickBoundary (C : XCTM Q) (z₀ : State (Sp C))
    (ω : LabelPath C) (k j : ℕ) : Prop :=
  InWindow C z₀ ω k j ∧ TickAt C z₀ ω j

/-- Exactly the event in §7.1: an actual tick at a nonterminal work state. -/
def Error (C : XCTM Q) (z₀ : State (Sp C)) (ω : LabelPath C) : Prop :=
  ∃ j, TickAt C z₀ ω j ∧ ¬ WorkTerminal C (pathState (net C) z₀ ω j)

theorem not_error_iff (C : XCTM Q) (z₀ : State (Sp C)) (ω : LabelPath C) :
    ¬ Error C z₀ ω ↔
      ∀ j, TickAt C z₀ ω j → WorkTerminal C (pathState (net C) z₀ ω j) := by
  classical
  simp only [Error, not_exists, not_and, not_not]

/-- The probability layer must prove this almost surely. -/
def TickProgress (C : XCTM Q) (z₀ : State (Sp C)) (ω : LabelPath C) : Prop :=
  ∀ k : ℕ, ∃ j : ℕ, k ≤ tickCount C z₀ ω j

/-- Correct simulation for all steps includes progress, not only conditional safety. -/
def SimulatesAll (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (ω : LabelPath C) : Prop :=
  TickProgress C (initial C i₀ w) ω ∧
    ∀ j, TickAt C (initial C i₀ w) ω j →
      Clean C i₀ w (tickCount C (initial C i₀ w) ω j)
        (pathState (net C) (initial C i₀ w) ω j)

def ExtensionStep (C : XCTM Q) (w : List Bool) (n : ℕ) : Prop :=
  ∃ q', C.mode (C.runT (C.start, w) n).1 = .extend q'

def InExtensionEpoch (C : XCTM Q) (w : List Bool) (n k : ℕ) : Prop :=
  ExtensionStep C w n ∧
    (k = 4 * n + 3 ∨ k = 4 * (n + 1) ∨ k = 4 * (n + 1) + 1)

def BeforeHalt (C : XCTM Q) (w : List Bool) (n : ℕ) : Prop :=
  ∀ j < n, C.mode (C.runT (C.start, w) j).1 ≠ .halt

noncomputable def jumpLaw (C : XCTM Q) (i₀ : ℕ) (w : List Bool) : Measure (LabelPath C) :=
  rawLaw (net C) (net_hasPositiveRates C) (initial C i₀ w)

noncomputable def errorBound (i₀ : ℕ) : ℝ := 1344 / ((i₀ : ℝ) - 1) ^ 2

def AdmissibleAccuracy (w : List Bool) (i₀ : ℕ) (δ : ℝ) : Prop :=
  3 ≤ w.length ∧ 0 < δ ∧ δ ≤ 1 ∧
    max (w.length : ℝ) (1 + 37 / Real.sqrt δ) ≤ (i₀ : ℝ)

/-- Theorem 7.1, as a proposition for the next layer. The a.e. qualifier
is necessary for its progress assertion on the raw path space. -/
def ErrorClaim (C : XCTM Q) : Prop :=
  ∀ (w : List Bool) (i₀ : ℕ) (δ : ℝ), AdmissibleAccuracy w i₀ δ →
    jumpLaw C i₀ w {ω | Error C (initial C i₀ w) ω} ≤ ENNReal.ofReal (errorBound i₀) ∧
    errorBound i₀ ≤ δ ∧
    (∀ᵐ ω ∂jumpLaw C i₀ w,
      ¬ Error C (initial C i₀ w) ω → SimulatesAll C i₀ w ω)

abbrev TimedPath (C : XCTM Q) := CTMCBridge.TimedΩ (net C)

noncomputable def markedLaw (C : XCTM Q) (i₀ : ℕ) (w : List Bool) :
    Measure (TimedPath C) :=
  CTMCBridge.timedLaw (net C) (net_hasPositiveRates C) (initial C i₀ w)

def moleculeCount (C : XCTM Q) (z : State (Sp C)) : ℕ := ∑ s, z s

noncomputable def densityVolume (C : XCTM Q) (ρ : ℝ) (z : State (Sp C)) : ℝ :=
  (moleculeCount C z : ℝ) / ρ

/-- Unit-rate exponential marks, rescaled by the actual physical v(z)/κ. -/
noncomputable def physicalHolding (C : XCTM Q) (z₀ : State (Sp C))
    (volume : State (Sp C) → ℝ) (κ : ℝ) (j : ℕ) (η : TimedPath C) : ℝ≥0∞ :=
  CTMCBridge.holdingTime (net C) z₀ j η *
    ENNReal.ofReal (volume (pathState (net C) z₀ η.1 j) / κ)

noncomputable def physicalJumpTime (C : XCTM Q) (z₀ : State (Sp C))
    (volume : State (Sp C) → ℝ) (κ : ℝ) (J : ℕ) (η : TimedPath C) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range J, physicalHolding C z₀ volume κ j η

open Classical in
/-- A genuine hitting time: a missing target tick has time infinity. -/
noncomputable def physicalTickTime (C : XCTM Q) (z₀ : State (Sp C))
    (volume : State (Sp C) → ℝ) (κ : ℝ) (K : ℕ) (η : TimedPath C) : ℝ≥0∞ :=
  if h : ∃ j, K ≤ tickCount C z₀ η.1 j then
    physicalJumpTime C z₀ volume κ (Nat.find h) η
  else ⊤

def noErrorTimed (C : XCTM Q) (i₀ : ℕ) (w : List Bool) : Set (TimedPath C) :=
  {η | ¬ Error C (initial C i₀ w) η.1}

noncomputable def conditionalTickMean (C : XCTM Q) (i₀ : ℕ) (w : List Bool)
    (ρ κ : ℝ) (K : ℕ) : ℝ≥0∞ :=
  (∫⁻ η in noErrorTimed C i₀ w,
      physicalTickTime C (initial C i₀ w) (densityVolume C ρ) κ K η
        ∂markedLaw C i₀ w) / markedLaw C i₀ w (noErrorTimed C i₀ w)

/-- Theorem 7.2 / §14, as a proposition. -/
def TimeClaim (C : XCTM Q) : Prop :=
  ∀ (w : List Bool) (i₀ : ℕ) (δ ρ κ : ℝ),
    AdmissibleAccuracy w i₀ δ → δ < 1 → 0 < ρ → 0 < κ →
    ∀ n : ℕ, BeforeHalt C w n →
      conditionalTickMean C i₀ w ρ κ (4 * n) ≤
        ENNReal.ofReal (92 * (n : ℝ) * ((i₀ : ℝ) + n) ^ 5 / ((1 - δ) * ρ * κ))

noncomputable def accuracyIndex (s : ℕ) (δ : ℝ) : ℕ :=
  max s (1 + ⌈37 / Real.sqrt δ⌉₊)

/-- The explicit TM-time corollary, with layer one's exact macro-step count. -/
def TMTimeClaim {QM : Type} [Fintype QM] [DecidableEq QM]
    (M : TM.Machine QM Bool) : Prop :=
  M.blank = false →
  ∀ (s : ℕ) (input : List Bool) (δ ρ κ : ℝ),
    1 ≤ s → input.length ≤ s → 0 < δ → δ < 1 → 0 < ρ → 0 < κ →
    ∀ t : ℕ,
      (∀ j < t, M.delta (tmRun M (xInputCfg M s input) j).state
        (tmRun M (xInputCfg M s input) j).tape.head ≠ none) →
      let c := xInputCfg M s input
      let st := tlen (tmRun M c t).tape
      conditionalTickMean (xctmOf M) (accuracyIndex (2 * s + 2) δ)
        (xencT (xInputTape s input)) ρ κ (4 * xTime M c t) ≤
      ENNReal.ofReal
        (552 * ((st : ℝ) + 1) * (t : ℝ) *
          (37 / Real.sqrt δ + 2 * (s : ℝ) + 4 + 6 * ((st : ℝ) + 1) * t) ^ 5 /
            ((1 - δ) * ρ * κ))

theorem markedLaw_error (C : XCTM Q) (i₀ : ℕ) (w : List Bool) :
    markedLaw C i₀ w {η | Error C (initial C i₀ w) η.1} =
      jumpLaw C i₀ w {ω | Error C (initial C i₀ w) ω} := by
  exact CTMCBridge.timedLaw_labels (net C) (net_hasPositiveRates C)
    (initial C i₀ w) {ω | Error C (initial C i₀ w) ω}


/-! ## Deterministic safety on the actual raw-law paths -/

/-- The work invariant after k ticks, including idle signals after halting. -/
def Window (C : XCTM Q) (i₀ : ℕ) (w : List Bool) : ℕ → State (Sp C) → Prop
  | 0, z => workView C z = gamma C i₀ w 0
  | k + 1, z =>
      if Plan.halted C (plan C i₀ w k) then
        cleanView C true z = gamma C i₀ w k
      else WorkReach C (gamma C i₀ w k + unit .signal) (workView C z)

private theorem path_workView_idem (C : XCTM Q) (z : State (Sp C)) :
    workView C (workView C z) = workView C z := by
  funext s
  cases s <;> rfl

private theorem path_cleanView_congr (C : XCTM Q) (h : Bool)
    {x y : State (Sp C)} (heq : workView C x = workView C y) :
    cleanView C h x = cleanView C h y := by
  rw [← cleanView_workView C h x, ← cleanView_workView C h y, heq]

theorem window_of_workView_eq (C : XCTM Q) (i₀ : ℕ) (w : List Bool)
    (k : ℕ) {x y : State (Sp C)} (heq : workView C y = workView C x)
    (hW : Window C i₀ w k x) : Window C i₀ w k y := by
  cases k with
  | zero => exact heq.trans hW
  | succ k =>
      cases hh : Plan.halted C (plan C i₀ w k) with
      | false =>
          simp only [Window, hh] at hW ⊢
          rw [heq]
          exact hW
      | true =>
          simp only [Window, hh] at hW ⊢
          exact (path_cleanView_congr C true heq).trans hW

/-- Actual work firings preserve the concrete window invariant. -/
theorem window_work_fire (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (k : ℕ)
    (z : State (Sp C)) (hW : Window C i₀ w k z)
    (r : Rx C) (hr : isClock r = false) (he : (rxn C r).enabled z) :
    Window C i₀ w k ((rxn C r).fire z) := by
  cases k with
  | zero =>
      have ht : WorkTerminal C z := (workTerminal_view C z).mp (by
        rw [hW]
        exact Plan.workState_terminal C (plan C i₀ w 0))
      exact False.elim (ht r hr he)
  | succ k =>
      cases hh : Plan.halted C (plan C i₀ w k) with
      | true =>
          simp only [Window, hh] at hW
          have ht := halted_clean_terminal C (plan C i₀ w k) z hh hW
          exact False.elim (ht r hr he)
      | false =>
          simp only [Window, hh] at hW ⊢
          rw [work_fire_view C r z hr]
          exact Relation.ReflTransGen.tail hW
            ⟨r, hr, (work_enabled_view C r z hr).mpr he, rfl⟩

/-- Terminality identifies the unique clean target, including a halted predecessor. -/
theorem window_terminal_clean (C : XCTM Q) (i₀ : ℕ) (w : List Bool)
    (hs : 3 ≤ w.length) (k : ℕ) (z : State (Sp C))
    (hW : Window C i₀ w k z) (ht : WorkTerminal C z) :
    Clean C i₀ w k z := by
  cases k with
  | zero =>
      exact cleanView_eq_from_workView C (plan C i₀ w 0) z hW
  | succ k =>
      cases hh : Plan.halted C (plan C i₀ w k) with
      | true =>
          simp only [Window, hh] at hW
          have hp : plan C i₀ w (k + 1) = plan C i₀ w k := by
            change Plan.advance C (plan C i₀ w k) = plan C i₀ w k
            exact Plan.advance_fixed_of_halted C (plan C i₀ w k) hh
          simpa only [Clean, gamma, hp, hh] using hW
      | false =>
          simp only [Window, hh] at hW
          have hc :=
            planCertificate C (plan C i₀ w k) (plan_valid C i₀ w hs k) hh
          have hn := (WorkCertificate.normalization C hc).2.1
            (workView C z) hW ((workTerminal_view C z).mpr ht)
          apply cleanView_eq_from_workView C (plan C i₀ w (k + 1)) z
          change workView C z =
            Plan.workState C (Plan.advance C (plan C i₀ w k))
          simpa only [path_workView_idem] using hn

/-- A correct tick starts the next concrete window; halted signals remain idle. -/
theorem window_after_tick (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (k : ℕ)
    (z : State (Sp C)) (hC : Clean C i₀ w k z) (latent : Bool)
    (he : (rxn C (.tick latent)).enabled z) :
    Window C i₀ w (k + 1) ((rxn C (.tick latent)).fire z) := by
  cases hh : Plan.halted C (plan C i₀ w k) with
  | false =>
      simp only [Window, hh]
      have hz : workView C z = gamma C i₀ w k := by
        simpa only [Clean, hh, cleanView_false] using hC
      rw [tick_workView C latent z he, hz]
      exact Relation.ReflTransGen.refl
  | true =>
      simp only [Window, hh]
      calc
        cleanView C true ((rxn C (.tick latent)).fire z) =
            cleanView C true (workView C ((rxn C (.tick latent)).fire z)) :=
          (cleanView_workView C true _).symm
        _ = cleanView C true (workView C z + unit .signal) := by
          rw [tick_workView C latent z he]
        _ = cleanView C true (workView C z) := cleanView_true_add_signal C _
        _ = cleanView C true z := cleanView_workView C true z
        _ = gamma C i₀ w k := by
          simpa only [Clean, hh] using hC

private theorem path_tick_cases (C : XCTM Q) (r : Rx C)
    (ht : isTick r = true) :
    ∃ latent : Bool, r = .tick latent := by
  cases r <;> simp_all [isTick]

/-- Every state on an error-free sanitized path lies in its concrete window. -/
theorem noError_window (C : XCTM Q) (i₀ : ℕ) (w : List Bool)
    (hs : 3 ≤ w.length) (ω : LabelPath C)
    (hNo : ¬ Error C (initial C i₀ w) ω) :
    ∀ j : ℕ,
      Window C i₀ w (tickCount C (initial C i₀ w) ω j)
        (pathState (net C) (initial C i₀ w) ω j) := by
  intro j
  induction j with
  | zero =>
      change workView C (initial C i₀ w) = gamma C i₀ w 0
      exact initial_workView C i₀ w
  | succ j ih =>
      have hv := pathFired_valid (net C) (initial C i₀ w) ω j
      cases hF : pathFired (net C) (initial C i₀ w) ω j with
      | none =>
          simp only [hF] at hv
          have hcount :
              tickCount C (initial C i₀ w) ω (j + 1) =
                tickCount C (initial C i₀ w) ω j := by
            simp [tickCount, TickAt, firedTick, hF]
          rw [hcount, hv.1]
          exact ih
      | some r =>
          simp only [hF] at hv
          have he : (rxn C r).enabled
              (pathState (net C) (initial C i₀ w) ω j) := hv.1
          have hstate :
              pathState (net C) (initial C i₀ w) ω (j + 1) =
                (rxn C r).fire
                  (pathState (net C) (initial C i₀ w) ω j) := hv.2
          cases ht : isTick r with
          | false =>
              have hcount :
                  tickCount C (initial C i₀ w) ω (j + 1) =
                    tickCount C (initial C i₀ w) ω j := by
                simp [tickCount, TickAt, firedTick, hF, ht]
              rw [hcount, hstate]
              cases hc : isClock r with
              | false =>
                  exact window_work_fire C i₀ w _ _ ih r hc he
              | true =>
                  exact window_of_workView_eq C i₀ w _
                    (clock_move_workView C r _ hc ht he) ih
          | true =>
              have hTick : TickAt C (initial C i₀ w) ω j := by
                simpa only [TickAt, firedTick, hF] using ht
              have hterminal : WorkTerminal C
                  (pathState (net C) (initial C i₀ w) ω j) := by
                by_contra h
                exact hNo ⟨j, hTick, h⟩
              have hclean :=
                window_terminal_clean C i₀ w hs _ _ ih hterminal
              have hcount :=
                tickCount_succ_of_tick C (initial C i₀ w) ω j hTick
              obtain ⟨latent, rfl⟩ := path_tick_cases C r ht
              rw [hcount, hstate]
              exact window_after_tick C i₀ w _ _ hclean latent he

/-- Section 8.1: every occurring error-free tick sees the prescribed clean state. -/
theorem noError_clean_at_ticks (C : XCTM Q) (i₀ : ℕ) (w : List Bool)
    (hs : 3 ≤ w.length) (ω : LabelPath C)
    (hNo : ¬ Error C (initial C i₀ w) ω) :
    ∀ j : ℕ, TickAt C (initial C i₀ w) ω j →
      Clean C i₀ w (tickCount C (initial C i₀ w) ω j)
        (pathState (net C) (initial C i₀ w) ω j) := by
  intro j hTick
  apply window_terminal_clean C i₀ w hs _ _
    (noError_window C i₀ w hs ω hNo j)
  exact (not_error_iff C (initial C i₀ w) ω).mp hNo j hTick

/-- The probability layer only needs to supply tick progress in addition to no error. -/
theorem simulatesAll_of_noError_progress (C : XCTM Q) (i₀ : ℕ)
    (w : List Bool) (hs : 3 ≤ w.length) (ω : LabelPath C)
    (hNo : ¬ Error C (initial C i₀ w) ω)
    (hProgress : TickProgress C (initial C i₀ w) ω) :
    SimulatesAll C i₀ w ω :=
  ⟨hProgress, noError_clean_at_ticks C i₀ w hs ω hNo⟩


/-! ## The TM simulation event and deterministic composition with layer one -/

/-- Unbounded tick progress supplies an actual boundary for every window index. -/
theorem exists_tickBoundary (C : XCTM Q) (z₀ : State (Sp C))
    (ω : LabelPath C) (hProgress : TickProgress C z₀ ω) (k : ℕ) :
    ∃ j : ℕ, TickBoundary C z₀ ω k j := by
  classical
  let hex : ∃ j : ℕ, k + 1 ≤ tickCount C z₀ ω j := hProgress (k + 1)
  have hpos : 0 < Nat.find hex := by
    by_contra h
    have hz : Nat.find hex = 0 := by omega
    have hfound := Nat.find_spec hex
    rw [hz] at hfound
    change k + 1 ≤ 0 at hfound
    omega
  let j := Nat.find hex - 1
  have hj : j + 1 = Nat.find hex := by
    dsimp only [j]
    omega
  have hbefore : ¬ k + 1 ≤ tickCount C z₀ ω j :=
    Nat.find_min hex (by
      dsimp only [j]
      omega)
  have hafter : k + 1 ≤ tickCount C z₀ ω (j + 1) := by
    rw [hj]
    exact Nat.find_spec hex
  have hstep := tickCount_succ_le C z₀ ω j
  have hcount : tickCount C z₀ ω j = k := by omega
  have hTick : TickAt C z₀ ω j := by
    by_contra h
    have hflat : tickCount C z₀ ω (j + 1) = tickCount C z₀ ω j := by
      simp only [tickCount, if_neg h, Nat.add_zero]
    omega
  exact ⟨j, hcount, hTick⟩

/-- Every TM macro boundary decodes to the layer-one canonical encoding. -/
theorem plan_at_tm_boundary {QM : Type} [Fintype QM] [DecidableEq QM]
    (M : TM.Machine QM Bool) (hb : M.blank = false)
    (s i₀ : ℕ) (input : List Bool)
    (hs : 1 ≤ s) (hi : input.length ≤ s) (t : ℕ) :
    Plan.configuration (xctmOf M)
      (plan (xctmOf M) i₀ (xencT (xInputTape s input))
        (4 * xTime M (xInputCfg M s input) t)) =
      xencC (tmRun M (xInputCfg M s input) t).state
        (tmRun M (xInputCfg M s input) t).tape := by
  let c := xInputCfg M s input
  let n := xTime M c t
  have hlen : 3 ≤ (xencT (xInputTape s input)).length := by
    rw [xInputTape_encoding_length s input hs hi]
    omega
  have hactive :
      ∀ j < n,
        (xctmOf M).mode
          ((xctmOf M).runT
            ((xctmOf M).start, xencT (xInputTape s input)) j).1 ≠ .halt := by
    intro j hj
    change (xctmOf M).mode
      ((xctmOf M).runT (xencC c.state c.tape) j).1 ≠ .halt
    exact xctm_no_halt_before_boundary M hb c t (Nat.le_of_lt hj)
  have hplan :=
    plan_at_step (xctmOf M) i₀ (xencT (xInputTape s input)) hlen n hactive
  change Plan.configuration (xctmOf M)
      (plan (xctmOf M) i₀ (xencT (xInputTape s input)) (4 * n)) =
    xencC (tmRun M c t).state (tmRun M c t).tape
  rw [hplan]
  change (xctmOf M).runT (xencC c.state c.tape) (xTime M c t) =
    xencC (tmRun M c t).state (tmRun M c t).tape
  exact xctm_tracks M hb c t

/-- The actual reaction path visits a clean encoding of every TM configuration.
The boundary and Clean conjuncts refer to the sanitized reaction path; the last
equality decodes its clean state through the explicit plan. -/
def TMSimulatesAll {QM : Type} [Fintype QM] [DecidableEq QM]
    (M : TM.Machine QM Bool) (s i₀ : ℕ) (input : List Bool)
    (ω : LabelPath (xctmOf M)) : Prop :=
  TickProgress (xctmOf M) (tmInitial M s i₀ input) ω ∧
    ∀ t : ℕ, ∃ j : ℕ,
      TickBoundary (xctmOf M) (tmInitial M s i₀ input) ω
        (4 * xTime M (xInputCfg M s input) t) j ∧
      Clean (xctmOf M) i₀ (xencT (xInputTape s input))
        (4 * xTime M (xInputCfg M s input) t)
        (pathState (net (xctmOf M)) (tmInitial M s i₀ input) ω j) ∧
      Plan.configuration (xctmOf M)
        (plan (xctmOf M) i₀ (xencT (xInputTape s input))
          (4 * xTime M (xInputCfg M s input) t)) =
        xencC (tmRun M (xInputCfg M s input) t).state
          (tmRun M (xInputCfg M s input) t).tape

/-- Deterministic composition with the layer-one TM simulation. -/
theorem tmSimulatesAll_of_simulatesAll
    {QM : Type} [Fintype QM] [DecidableEq QM]
    (M : TM.Machine QM Bool) (hb : M.blank = false)
    (s i₀ : ℕ) (input : List Bool)
    (hs : 1 ≤ s) (hi : input.length ≤ s)
    (ω : LabelPath (xctmOf M))
    (hSim : SimulatesAll (xctmOf M) i₀ (xencT (xInputTape s input)) ω) :
    TMSimulatesAll M s i₀ input ω := by
  refine ⟨hSim.1, ?_⟩
  intro t
  obtain ⟨j, hj⟩ :=
    exists_tickBoundary (xctmOf M) (tmInitial M s i₀ input) ω hSim.1
      (4 * xTime M (xInputCfg M s input) t)
  refine ⟨j, hj, ?_, plan_at_tm_boundary M hb s i₀ input hs hi t⟩
  have hclean := hSim.2 j hj.2
  have hcount :
      tickCount (xctmOf M) (tmInitial M s i₀ input) ω j =
        4 * xTime M (xInputCfg M s input) t := hj.1
  change Clean (xctmOf M) i₀ (xencT (xInputTape s input))
      (tickCount (xctmOf M) (tmInitial M s i₀ input) ω j)
      (pathState (net (xctmOf M)) (tmInitial M s i₀ input) ω j) at hclean
  rw [hcount] at hclean
  exact hclean

theorem tmSimulatesAll_of_noError_progress
    {QM : Type} [Fintype QM] [DecidableEq QM]
    (M : TM.Machine QM Bool) (hb : M.blank = false)
    (s i₀ : ℕ) (input : List Bool)
    (hs : 1 ≤ s) (hi : input.length ≤ s)
    (ω : LabelPath (xctmOf M))
    (hNo : ¬ Error (xctmOf M) (tmInitial M s i₀ input) ω)
    (hProgress : TickProgress (xctmOf M) (tmInitial M s i₀ input) ω) :
    TMSimulatesAll M s i₀ input ω := by
  have hlen : 3 ≤ (xencT (xInputTape s input)).length := by
    rw [xInputTape_encoding_length s input hs hi]
    omega
  apply tmSimulatesAll_of_simulatesAll M hb s i₀ input hs hi ω
  exact simulatesAll_of_noError_progress (xctmOf M) i₀
    (xencT (xInputTape s input)) hlen ω hNo hProgress


/-! ## State-population bounds for Section 8.3 -/

noncomputable def controlMolecules (C : XCTM Q) (z : State (Sp C)) : ℕ := by
  classical
  exact ∑ s : Sp C, if s.IsControl ∧ s ≠ .signal then z s else 0

theorem controlMolecules_single_le (C : XCTM Q) (z : State (Sp C))
    (s : Sp C) (hs : s.IsControl) (hn : s ≠ .signal) :
    z s ≤ controlMolecules C z := by
  classical
  unfold controlMolecules
  have h := Finset.single_le_sum
    (f := fun t : Sp C => if t.IsControl ∧ t ≠ .signal then z t else 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
  simpa only [
    if_pos (show s.IsControl ∧ s ≠ Sp.signal from ⟨hs, hn⟩)] using h

theorem controlMolecules_pair_le (C : XCTM Q) (z : State (Sp C))
    (s t : Sp C) (hs : s.IsControl) (ht : t.IsControl)
    (hns : s ≠ .signal) (hnt : t ≠ .signal) (hne : s ≠ t) :
    z s + z t ≤ controlMolecules C z := by
  classical
  let f : Sp C → ℕ :=
    fun u => if u.IsControl ∧ u ≠ .signal then z u else 0
  calc
    z s + z t = ∑ u ∈ ({s, t} : Finset (Sp C)), f u := by
      simp [f, hne, hs, ht, hns, hnt]
    _ ≤ ∑ u : Sp C, f u :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Nat.zero_le _)
    _ = controlMolecules C z := rfl

theorem controlMolecules_add_signal
    (C : XCTM Q) (z : State (Sp C)) (j : ℕ) :
    controlMolecules C (z + j • unit (.signal : Sp C)) =
      controlMolecules C z := by
  classical
  unfold controlMolecules
  apply Finset.sum_congr rfl
  intro s hs
  by_cases he : s = .signal
  · simp [he]
  · simp [he, unit, Pi.add_apply, Pi.smul_apply]

theorem restore_controlMolecules (C : XCTM Q) {a : ActiveState C}
    {d threshold value alpha : ℕ} {z : State (Sp C)}
    (h : RestoreWindow C a d threshold value alpha z) :
    d ≤ controlMolecules C z := by
  rw [← h.2.1]
  exact controlMolecules_pair_le C z
    (.first (activeControl C a)) (.second a)
    trivial trivial (by simp) (by simp) (by simp)

theorem read_controlMolecules (C : XCTM Q)
    {m T g x x' : ℕ} {q : ReadState C} {b : Bool} {z : State (Sp C)}
    (h : ReadWindow C m T g q b x x' z) :
    m ≤ controlMolecules C z := by
  rcases h with h | h | h
  · rw [← h.2.2.1]
    exact controlMolecules_single_le C z
      (.third (.inl q)) trivial (by simp)
  · have hsum := controlMolecules_pair_le C z
      (.third (.inl q)) (.reader q)
      trivial trivial (by simp) (by simp) (by simp)
    have hreader := h.2.1
    have htotal := h.2.2.1
    omega
  · rw [← h.2.1]
    exact controlMolecules_pair_le C z
      (.third (.inl q)) (.write q b)
      trivial trivial (by simp) (by simp) (by simp)

theorem extension_controlMolecules_of_population
    (C : XCTM Q) (e : ExtendState C) {d : ℕ} {z : State (Sp C)}
    (hpop : 3 * z (.third (.inr e)) + z (.extend e) = 3 * d) :
    d ≤ controlMolecules C z := by
  have hsum := controlMolecules_pair_le C z
    (.third (.inr e)) (.extend e)
    trivial trivial (by simp) (by simp) (by simp)
  omega

theorem extension_controlMolecules (C : XCTM Q) {e : ExtendState C}
    {d v th a f : ℕ} {z : State (Sp C)}
    (h : ExtensionInvariant C e d v th a f z) :
    d ≤ controlMolecules C z :=
  extension_controlMolecules_of_population C e h.control

theorem buffer_controlMolecules (C : XCTM Q) (b : Buffer C)
    {z : State (Sp C)} (h : BufferWindow C b z) :
    Buffer.count C b ≤ controlMolecules C z := by
  rw [← h.2.1]
  apply controlMolecules_pair_le C z (Buffer.old C b) (Buffer.new C b)
  all_goals
    cases b <;> simp [Buffer.old, Buffer.new, Sp.IsControl]

/-! ## Read-window clock parameters on actual work reachability -/

theorem read_reachable_clock_counts
    (C : XCTM Q) (q : ReadState C) (w : List Bool) (accuracy : ℕ)
    (hs : 3 ≤ w.length) {z : State (Sp C)}
    (hreach : WorkReach C
      (payload C (.third (.inl q)) (stateCount w.length)
        accuracy false (comparedMemory w) + unit .signal) z) :
    forwardCount C z = accuracy * stateCount w.length ∧
      backwardCount C z = stateCount w.length := by
  have hstart := read_start_from_payload C q w accuracy hs
  have hnext := read_value w hs
    (C.next q.val (w.headD false)).2
  have hconstant :=
    (read_workReach_invariant C hnext hstart hreach).2
  have ha := congrArg
    (fun f : ℕ × ℕ × ℕ × ℕ => f.1 + f.2.1) hconstant
  have hf := congrArg
    (fun f : ℕ × ℕ × ℕ × ℕ => f.2.2.1 + f.2.2.2) hconstant
  constructor
  · simpa [readFuel, forwardCount, payload, unit] using ha
  · simpa [readFuel, backwardCount, payload, unit] using hf

theorem read_reachable_parameters
    (C : XCTM Q) (q : ReadState C) (w : List Bool) (accuracy : ℕ)
    (hs : 3 ≤ w.length) {z : State (Sp C)}
    (hreach : WorkReach C
      (payload C (.third (.inl q)) (stateCount w.length)
        accuracy false (comparedMemory w) + unit .signal) z) :
    0 < backwardCount C z ∧
      backwardCount C z ≤ stateCount w.length ∧
      (accuracy : ℝ) / 3 ≤
        (forwardCount C z : ℝ) / backwardCount C z := by
  obtain ⟨ha, hf⟩ :=
    read_reachable_clock_counts C q w accuracy hs hreach
  have hd : 0 < stateCount w.length := by
    unfold stateCount
    positivity
  have hpositive : 0 < backwardCount C z := by omega
  refine ⟨hpositive, by omega, ratio_bound hpositive ?_⟩
  rw [ha, hf]
  omega

/-! ## Buffer-window clock parameters -/

/-- The accuracy parameter stored in the preceding clean payload. -/
def bufferAccuracy {C : XCTM Q} : Buffer C → ℕ
  | .fromRead _ _ _ a => a
  | .fromExtension _ _ a => a
  | .toThird _ _ a => a

/-- Buffers preserve every non-control coordinate. The backward count is
either d or d/3, and the forward count is the stored accuracy times it. -/
theorem buffer_clock_counts (C : XCTM Q) (b : Buffer C)
    {z : State (Sp C)} (h : BufferWindow C b z) :
    forwardCount C z = bufferAccuracy b * backwardCount C z ∧
      (backwardCount C z = Buffer.count C b ∨
        backwardCount C z = Buffer.count C b / 3) := by
  have hwork := h.2.2.2.2.2
  have ha := hwork .forward (by simp [Sp.IsControl])
  have had := hwork .forwardLatent (by simp [Sp.IsControl])
  have hf := hwork .backward (by simp [Sp.IsControl])
  have hfd := hwork .backwardLatent (by simp [Sp.IsControl])
  cases b <;>
    simp_all [bufferAccuracy, forwardCount, backwardCount,
      Buffer.before, Buffer.count, Plan.workState, Plan.tape, payload]

theorem buffer_parameters (C : XCTM Q) (b : Buffer C)
    {z : State (Sp C)}
    (hs : 3 ≤ (Buffer.before C b).tape.length)
    (h : BufferWindow C b z) :
    0 < backwardCount C z ∧
      backwardCount C z ≤ Buffer.count C b ∧
      (bufferAccuracy b : ℝ) / 3 ≤
        (forwardCount C z : ℝ) / backwardCount C z := by
  obtain ⟨ha, hf⟩ := buffer_clock_counts C b h
  have hd : 0 < Buffer.count C b := by
    dsimp [Buffer.count]
    unfold stateCount
    positivity
  have hdiv : 3 * (Buffer.count C b / 3) = Buffer.count C b := by
    simpa only [Buffer.count] using
      stateCount_div_exact (Buffer.before C b).tape.length hs
  have hb : 0 < backwardCount C z ∧
      backwardCount C z ≤ Buffer.count C b := by
    rcases hf with hf | hf
    · constructor <;> omega
    · constructor <;> omega
  refine ⟨hb.1, hb.2, ratio_bound hb.1 ?_⟩
  rw [ha]
  omega


/-! ## Uniform deterministic parameters for the next window -/

def Plan.accuracy {C : XCTM Q} : Plan C → ℕ
  | .first _ _ a _ | .second _ _ a | .third _ _ a
    | .write _ _ _ a | .extend _ _ a => a

def Parameters (C : XCTM Q) (d alpha : ℕ) (z : State (Sp C)) : Prop :=
  0 < backwardCount C z ∧ backwardCount C z ≤ d ∧
    (alpha : ℝ) / 3 ≤ (forwardCount C z : ℝ) / backwardCount C z ∧
    d ≤ controlMolecules C z

theorem parameters_mono (C : XCTM Q) {d alpha beta : ℕ} {z : State (Sp C)}
    (hab : alpha ≤ beta) (h : Parameters C d beta z) :
    Parameters C d alpha z := by
  have hab' : (alpha : ℝ) ≤ beta := by exact_mod_cast hab
  exact ⟨h.1, h.2.1, (by linarith [h.2.2.1]), h.2.2.2⟩

theorem initial_parameters (C : XCTM Q) (i₀ : ℕ) (w : List Bool) :
    Parameters C (stateCount w.length) i₀ (initial C i₀ w) := by
  have hd : 0 < stateCount w.length := by unfold stateCount; positivity
  have hp : 0 < backwardCount C (initial C i₀ w) := by
    simpa [backwardCount, initial] using hd
  refine ⟨hp, by simp [backwardCount, initial], ratio_bound hp ?_, ?_⟩
  · simp [forwardCount, backwardCount, initial] <;> omega
  · simpa [initial] using
      controlMolecules_single_le C (initial C i₀ w) (.first C.start)
        trivial (by simp)

theorem restore_reachable_parameters_full (C : XCTM Q) (q : ActiveState C)
    (w : List Bool) (a : ℕ) (latent : Bool) (hs : 3 ≤ w.length)
    {z : State (Sp C)}
    (hreach : WorkReach C
      (payload C (.first (activeControl C q)) (stateCount w.length)
        a latent (storedMemory w) + unit .signal) z) :
    Parameters C (stateCount w.length) a z := by
  have hstart := restore_start C q w a latent
    (fun _ => stateCount_div_exact w.length hs)
  have hz := workReach_invariant C
    (RestoreWindow C q (stateCount w.length) (threshold w.length) (tval w) a)
    (restore_closed C q (stateCount w.length) (threshold w.length) (tval w) a)
    hreach hstart
  have hd : 0 < stateCount w.length := by unfold stateCount; positivity
  obtain ⟨hp, hb, ha⟩ := restoreBudget_parameters C hd hz.2.2.2.2.2.2
  exact ⟨hp, hb, ratio_bound hp ha, restore_controlMolecules C hz⟩

theorem buffer_reachable_parameters_full (C : XCTM Q) (b : Buffer C)
    (hs : 3 ≤ (Buffer.before C b).tape.length) {z : State (Sp C)}
    (hreach : WorkReach C
      (Plan.workState C (Buffer.before C b) + unit .signal) z) :
    Parameters C (Buffer.count C b) (bufferAccuracy b) z := by
  have hclosed : ∀ x y, BufferWindow C b x → WorkStep C x y →
      BufferWindow C b y := by
    rintro x y hx ⟨r, hr, he, rfl⟩
    exact (buffer_fire C hx hr he).1
  have hz := workReach_invariant C (BufferWindow C b) hclosed hreach (buffer_start C b)
  obtain ⟨hp, hf, hr⟩ := buffer_parameters C b hs hz
  exact ⟨hp, hf, hr, buffer_controlMolecules C b hz⟩

theorem read_reachable_parameters_full (C : XCTM Q) (q : ReadState C)
    (w : List Bool) (a : ℕ) (hs : 3 ≤ w.length) {z : State (Sp C)}
    (hreach : WorkReach C
      (Plan.workState C (.third (.inl q) w a) + unit .signal) z) :
    Parameters C (stateCount w.length) a z := by
  have hz := (read_workReach_invariant C
    (read_value w hs (C.next q.val (w.headD false)).2)
    (read_start_from_payload C q w a hs) hreach).1
  obtain ⟨hp, hf, hr⟩ := read_reachable_parameters C q w a hs hreach
  exact ⟨hp, hf, hr, read_controlMolecules C hz⟩

theorem extension_reachable_parameters_full (C : XCTM Q) (e : ExtendState C)
    (w : List Bool) (a : ℕ) {z : State (Sp C)}
    (hreach : WorkReach C
      (Plan.workState C (.third (.inr e) w a) + unit .signal) z) :
    Parameters C (stateCount w.length) a z := by
  have hstart :
      ExtensionInvariant C e (stateCount w.length) (tval w) (threshold w.length)
        (a * stateCount w.length) (stateCount w.length)
        (Plan.workState C (.third (.inr e) w a) + unit .signal) := by
    rw [← extension_start_payload]
    exact extension_start_invariant C e _ _ _ _ _ (fun _ => 0)
  have hz := workReach_invariant C
    (ExtensionInvariant C e (stateCount w.length) (tval w) (threshold w.length)
      (a * stateCount w.length) (stateCount w.length))
    (extension_work_closed C e _ _ _ _ _) hreach hstart
  have hd : 0 < stateCount w.length := by unfold stateCount; positivity
  have hf : backwardCount C z = stateCount w.length := hz.backward
  have ha : forwardCount C z = a * stateCount w.length := hz.forward
  have hp : 0 < backwardCount C z := by omega
  refine ⟨hp, hf.le, ratio_bound hp ?_, extension_controlMolecules C hz⟩
  rw [ha, hf]
  omega

/-- All four next-window types satisfy the required clock and population bounds.
For a second/third-phase predecessor, p.accuracy is alpha_n+1, so this
is stronger than the alpha_n/3 bound needed by Section 8.3. -/
theorem next_window_parameters (C : XCTM Q) (p : Plan C)
    (hs : 3 ≤ p.tape.length) (hh : Plan.halted C p = false)
    {z : State (Sp C)}
    (hreach : WorkReach C (Plan.workState C p + unit .signal) z) :
    Parameters C (stateCount p.tape.length) p.accuracy z := by
  cases p with
  | first q w a latent =>
      cases hm : C.mode q with
      | read =>
          exact restore_reachable_parameters_full C (.inl ⟨q, hm⟩) w a latent hs hreach
      | extend q' =>
          exact restore_reachable_parameters_full C
            (.inr ⟨q, ⟨q', hm⟩⟩) w a latent hs hreach
      | halt => simp [Plan.halted, hm] at hh
  | second q w a =>
      exact buffer_reachable_parameters_full C (.toThird q w a) hs hreach
  | third q w a =>
      cases q with
      | inl q => exact read_reachable_parameters_full C q w a hs hreach
      | inr e => exact extension_reachable_parameters_full C e w a hreach
  | write q b w a =>
      exact buffer_reachable_parameters_full C (.fromRead q b w a) hs hreach
  | extend e w a =>
      exact buffer_reachable_parameters_full C (.fromExtension e w a) hs hreach


/-! ## Finite counterexamples to overstrong readings of the note -/

namespace RatioWitness

def machine : XCTM Unit where
  next _ b := ((), b)
  start := ()
  mode _ := .read

def active : ActiveState machine := .inl ⟨(), rfl⟩

def tape : List Bool := [false, false, false]

def start : State (Sp machine) := initial machine 38 tape + unit .signal

def seeded : State (Sp machine) :=
  (rxn machine (.startSecond active)).fire start

def restored : State (Sp machine) :=
  (rxn machine (.restoreD active)).fire seeded

/-- Ordinary restoration already gives a nonintegral intermediate clock ratio.
The two displayed positive propensities certify actual enabled firings. -/
theorem ordinary_restore_ratio_counterexample :
    rate machine (.startSecond active) start = 9 ∧
    rate machine (.restoreD active) seeded = 9 ∧
    forwardCount machine restored = 343 ∧
    backwardCount machine restored = 9 ∧
    (forwardCount machine restored : ℚ) / backwardCount machine restored ≠ 38 ∧
    (forwardCount machine restored : ℚ) / backwardCount machine restored ≠ 39 := by
  decide +kernel

theorem ordinary_restore_reachable : WorkReach machine start restored := by
  have heSeed : (rxn machine (.startSecond active)).enabled start := by
    rw [enabled_iff, ordinary_restore_ratio_counterexample.1]
    decide +kernel
  have heRestore : (rxn machine (.restoreD active)).enabled seeded := by
    rw [enabled_iff, ordinary_restore_ratio_counterexample.2.1]
    decide +kernel
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
      ⟨.startSecond active, rfl, heSeed, rfl⟩)
    ⟨.restoreD active, rfl, heRestore, rfl⟩

theorem witness_accuracy_admissible : AdmissibleAccuracy tape 38 1 := by
  norm_num [AdmissibleAccuracy, tape]

/-- Two actual clock moves can return to the initial state without a tick.
Repeating this finite cycle is a legitimate path with no tick progress. -/
theorem clock_bounce_counterexample :
    let upper := initial machine 38 tape
    let lower := (rxn machine (.down (3 : Fin 4) false)).fire upper
    rate machine (.down (3 : Fin 4) false) upper = 9 ∧
    rate machine (.up (3 : Fin 4) false) lower = 342 ∧
    (rxn machine (.up (3 : Fin 4) false)).fire lower = upper ∧
    isTick (.down (3 : Fin 4) false : Rx machine) = false ∧
    isTick (.up (3 : Fin 4) false : Rx machine) = false := by
  dsimp only
  refine ⟨rfl, rfl, ?_, rfl, rfl⟩
  funext s
  cases s with
  | clock c => fin_cases c <;> rfl
  | _ => rfl

end RatioWitness

end Ripple.sCRNUniversality.ClockedCTM.Unbounded
