/-
  Register Machine CRN simulation (SCWB Theorem 3.1, Fig 3.1A).

  Reactions:
  - dec₁: S_i + M_r → S_j (decrement, register nonzero)
  - dec₂: C₁ + S_i → S_k + C₁ (zero test, register zero)

  Error: dec₂ fires when register nonzero (race). Controlled by clock.
  Per-step error ≤ 1/#A^(l-1) via clock module.
-/
import Ripple.sCRNUniversality.Core.Run

namespace Ripple.sCRNUniversality.RegisterMachine

universe u v

variable {Q : Type u} [Fintype Q] [DecidableEq Q]
         {R : Type v} [Fintype R] [DecidableEq R]

inductive RMSpecies (Q : Type u) (R : Type v) where
  | state : Q → RMSpecies Q R
  | reg : R → RMSpecies Q R
  | catalyst : RMSpecies Q R
deriving DecidableEq, Repr

instance [Fintype Q] [Fintype R] : Fintype (RMSpecies Q R) :=
  Fintype.ofEquiv (Q ⊕ R ⊕ Unit)
    { toFun := fun | .inl q => .state q | .inr (.inl r) => .reg r | .inr (.inr ()) => .catalyst
      invFun := fun | .state q => .inl q | .reg r => .inr (.inl r) | .catalyst => .inr (.inr ())
      left_inv := by intro x; rcases x with q | r | ⟨⟩ <;> simp
      right_inv := by intro x; cases x <;> simp }

open RMSpecies

structure DecInstruction (Q : Type u) (R : Type v) where
  source : Q
  register : R
  target_nonzero : Q
  target_zero : Q
deriving DecidableEq, Repr

def rxnDec1 (instr : DecInstruction Q R) : Reaction (RMSpecies Q R) where
  l := fun | state q => if q = instr.source then 1 else 0
           | reg r => if r = instr.register then 1 else 0
           | catalyst => 0
  r := fun | state q => if q = instr.target_nonzero then 1 else 0
           | _ => 0
  k := 1

def rxnDec2 (instr : DecInstruction Q R) : Reaction (RMSpecies Q R) where
  l := fun | state q => if q = instr.source then 1 else 0
           | catalyst => 1
           | _ => 0
  r := fun | state q => if q = instr.target_zero then 1 else 0
           | catalyst => 1
           | _ => 0
  k := 1

def encodeRM (q : Q) (regs : R → Nat) : State (RMSpecies Q R) := fun
  | state q' => if q' = q then 1 else 0
  | reg r => regs r
  | catalyst => 1

theorem dec1_enabled_of_state_and_reg
    (instr : DecInstruction Q R) (regs : R → Nat)
    (hr : 0 < regs instr.register) :
    (rxnDec1 instr).enabled (encodeRM instr.source regs) := by
  intro sp; cases sp with
  | state q => simp [rxnDec1, encodeRM]
  | reg r =>
    simp only [rxnDec1, encodeRM]
    split <;> simp_all <;> omega
  | catalyst => simp [rxnDec1]

theorem dec2_enabled_of_state
    (instr : DecInstruction Q R) (regs : R → Nat) :
    (rxnDec2 instr).enabled (encodeRM instr.source regs) := by
  intro sp; cases sp with
  | state q => simp [rxnDec2, encodeRM]
  | reg r => simp [rxnDec2]
  | catalyst => simp [rxnDec2, encodeRM]

theorem both_enabled_when_register_nonzero
    (instr : DecInstruction Q R) (regs : R → Nat)
    (hr : 0 < regs instr.register) :
    (rxnDec1 instr).enabled (encodeRM instr.source regs) ∧
    (rxnDec2 instr).enabled (encodeRM instr.source regs) :=
  ⟨dec1_enabled_of_state_and_reg instr regs hr,
   dec2_enabled_of_state instr regs⟩

theorem dec1_not_enabled_when_register_zero
    (instr : DecInstruction Q R) (regs : R → Nat)
    (hr : regs instr.register = 0) :
    ¬(rxnDec1 instr).enabled (encodeRM instr.source regs) := by
  intro h
  have := h (reg instr.register)
  simp [rxnDec1, encodeRM, hr] at this

theorem only_dec2_when_zero
    (instr : DecInstruction Q R) (regs : R → Nat)
    (hr : regs instr.register = 0) :
    (rxnDec2 instr).enabled (encodeRM instr.source regs) ∧
    ¬(rxnDec1 instr).enabled (encodeRM instr.source regs) :=
  ⟨dec2_enabled_of_state instr regs,
   dec1_not_enabled_when_register_zero instr regs hr⟩

-- ── Increment instruction ─────────────────────────────────────────────

structure IncInstruction (Q : Type u) (R : Type v) where
  source : Q
  register : R
  target : Q
deriving DecidableEq, Repr

/-- inc(i,r,j): S_i + C → S_j + M_r + C  (catalyst on both sides) -/
def rxnInc (instr : IncInstruction Q R) : Reaction (RMSpecies Q R) where
  l := fun | state q => if q = instr.source then 1 else 0
           | catalyst => 1
           | _ => 0
  r := fun | state q => if q = instr.target then 1 else 0
           | reg r => if r = instr.register then 1 else 0
           | catalyst => 1
  k := 1

theorem inc_enabled_of_state
    (instr : IncInstruction Q R) (regs : R → Nat) :
    (rxnInc instr).enabled (encodeRM instr.source regs) := by
  intro sp; cases sp with
  | state q => simp [rxnInc, encodeRM]
  | reg r => simp [rxnInc]
  | catalyst => simp [rxnInc, encodeRM]

theorem inc_fire_eq
    (instr : IncInstruction Q R) (regs : R → Nat)
    (hSrcNeTgt : instr.source ≠ instr.target) :
    (rxnInc instr).fire (encodeRM instr.source regs) =
      encodeRM instr.target (Function.update regs instr.register (regs instr.register + 1)) := by
  funext sp; cases sp with
  | state q =>
    simp only [Reaction.fire_apply, rxnInc, encodeRM]
    by_cases hqs : q = instr.source
    · subst hqs
      simp [hSrcNeTgt]
    · by_cases hqt : q = instr.target
      · subst hqt; simp [hqs]
      · simp [hqs, hqt]
  | reg r =>
    simp only [Reaction.fire_apply, rxnInc, encodeRM, Function.update]
    by_cases hr : r = instr.register
    · subst hr; simp
    · simp [hr]
  | catalyst =>
    simp [Reaction.fire_apply, rxnInc, encodeRM]

theorem inc_firesTo
    (instr : IncInstruction Q R) (regs : R → Nat)
    (hSrcNeTgt : instr.source ≠ instr.target) :
    (rxnInc instr).FiresTo
      (encodeRM instr.source regs)
      (encodeRM instr.target (Function.update regs instr.register (regs instr.register + 1))) :=
  ⟨inc_enabled_of_state instr regs, (inc_fire_eq instr regs hSrcNeTgt).symm⟩

-- ── dec fire results ──────────────────────────────────────────────────

theorem dec1_fire_eq
    (instr : DecInstruction Q R) (regs : R → Nat)
    (hSrcNeNz : instr.source ≠ instr.target_nonzero) :
    (rxnDec1 instr).fire (encodeRM instr.source regs) =
      encodeRM instr.target_nonzero (Function.update regs instr.register (regs instr.register - 1)) := by
  funext sp; cases sp with
  | state q =>
    simp only [Reaction.fire_apply, rxnDec1, encodeRM]
    by_cases hqs : q = instr.source
    · subst hqs; simp [hSrcNeNz]
    · by_cases hqt : q = instr.target_nonzero
      · subst hqt; simp [hqs]
      · simp [hqs, hqt]
  | reg r =>
    simp only [Reaction.fire_apply, rxnDec1, encodeRM, Function.update]
    by_cases hreg : r = instr.register
    · subst hreg; simp
    · simp [hreg]
  | catalyst =>
    simp [Reaction.fire_apply, rxnDec1, encodeRM]

theorem dec1_firesTo
    (instr : DecInstruction Q R) (regs : R → Nat)
    (hr : 0 < regs instr.register)
    (hSrcNeNz : instr.source ≠ instr.target_nonzero) :
    (rxnDec1 instr).FiresTo
      (encodeRM instr.source regs)
      (encodeRM instr.target_nonzero (Function.update regs instr.register (regs instr.register - 1))) :=
  ⟨dec1_enabled_of_state_and_reg instr regs hr, (dec1_fire_eq instr regs hSrcNeNz).symm⟩

theorem dec2_fire_eq
    (instr : DecInstruction Q R) (regs : R → Nat)
    (hSrcNeZ : instr.source ≠ instr.target_zero) :
    (rxnDec2 instr).fire (encodeRM instr.source regs) =
      encodeRM instr.target_zero regs := by
  funext sp; cases sp with
  | state q =>
    simp only [Reaction.fire_apply, rxnDec2, encodeRM]
    by_cases hqs : q = instr.source
    · subst hqs; simp [hSrcNeZ]
    · by_cases hqt : q = instr.target_zero
      · subst hqt; simp [hqs]
      · simp [hqs, hqt]
  | reg r =>
    simp [Reaction.fire_apply, rxnDec2, encodeRM]
  | catalyst =>
    simp [Reaction.fire_apply, rxnDec2, encodeRM]

theorem dec2_firesTo
    (instr : DecInstruction Q R) (regs : R → Nat)
    (_hr : regs instr.register = 0)
    (hSrcNeZ : instr.source ≠ instr.target_zero) :
    (rxnDec2 instr).FiresTo
      (encodeRM instr.source regs)
      (encodeRM instr.target_zero regs) :=
  ⟨dec2_enabled_of_state instr regs, (dec2_fire_eq instr regs hSrcNeZ).symm⟩

-- ── RM program and network ───────────────────────────────────────────

inductive RMInstruction (Q : Type u) (R : Type v) where
  | inc : IncInstruction Q R → RMInstruction Q R
  | dec : DecInstruction Q R → RMInstruction Q R
deriving DecidableEq, Repr

abbrev RMProgram (Q : Type u) (R : Type v) := List (RMInstruction Q R)

/-- For a single inc instruction, a one-reaction network. -/
def incNetwork (instr : IncInstruction Q R) : Network (RMSpecies Q R) where
  I := Unit
  rxn := fun () => rxnInc instr

/-- For a single dec instruction, a two-reaction network. -/
def decNetwork (instr : DecInstruction Q R) : Network (RMSpecies Q R) where
  I := Bool
  rxn := fun | false => rxnDec1 instr | true => rxnDec2 instr

/-- Network for a single RM instruction (inc or dec). -/
def instrNetwork (instr : RMInstruction Q R) : Network (RMSpecies Q R) :=
  match instr with
  | .inc i => incNetwork i
  | .dec d => decNetwork d

/-- Full RM network: union over all instructions in the program. -/
def rmNetwork (prog : RMProgram Q R) : Network (RMSpecies Q R) :=
  Network.sigma (fun (idx : Fin prog.length) => instrNetwork (prog.get idx))

-- ── Simulation: inc step ─────────────────────────────────────────────

theorem inc_simulation
    (instr : IncInstruction Q R) (regs : R → Nat)
    (hSrcNeTgt : instr.source ≠ instr.target) :
    (incNetwork instr).Reaches
      (encodeRM instr.source regs)
      (encodeRM instr.target (Function.update regs instr.register (regs instr.register + 1))) := by
  refine ⟨[()], ?_⟩
  exact ExecOf.cons (inc_firesTo instr regs hSrcNeTgt) (ExecOf.nil _)

-- ── Simulation: dec step (nonzero case) ──────────────────────────────

theorem dec_nonzero_simulation
    (instr : DecInstruction Q R) (regs : R → Nat)
    (hr : 0 < regs instr.register)
    (hSrcNeNz : instr.source ≠ instr.target_nonzero) :
    (decNetwork instr).Reaches
      (encodeRM instr.source regs)
      (encodeRM instr.target_nonzero (Function.update regs instr.register (regs instr.register - 1))) := by
  refine ⟨[false], ?_⟩
  exact ExecOf.cons (dec1_firesTo instr regs hr hSrcNeNz) (ExecOf.nil _)

-- ── Simulation: dec step (zero case) ─────────────────────────────────

theorem dec_zero_simulation
    (instr : DecInstruction Q R) (regs : R → Nat)
    (hr : regs instr.register = 0)
    (hSrcNeZ : instr.source ≠ instr.target_zero) :
    (decNetwork instr).Reaches
      (encodeRM instr.source regs)
      (encodeRM instr.target_zero regs) := by
  refine ⟨[true], ?_⟩
  exact ExecOf.cons (dec2_firesTo instr regs hr hSrcNeZ) (ExecOf.nil _)

-- ── Full network simulation ──────────────────────────────────────────

/-- Helper: lift a sub-network reach to the sigma network.
    (Inlined because `Network.sigma_reaches` may not be in the built olean.) -/
private theorem sigma_reaches'
    {S : Type*} {A : Type*} [Fintype A]
    (Ns : A → Network S) (a : A)
    {z z' : State S}
    (h : (Ns a).Reaches z z') :
    (Network.sigma Ns).Reaches z z' := by
  rcases h with ⟨is, hExec⟩
  exact Network.sigma_reaches_of_exec Ns a hExec

/-- An RM inc step on a program lifts to a CRN reach in the full rmNetwork. -/
theorem rmNetwork_inc_simulation
    (prog : RMProgram Q R)
    (idx : Fin prog.length)
    (instr : IncInstruction Q R)
    (hInstr : prog.get idx = .inc instr)
    (regs : R → Nat)
    (hSrcNeTgt : instr.source ≠ instr.target) :
    (rmNetwork prog).Reaches
      (encodeRM instr.source regs)
      (encodeRM instr.target (Function.update regs instr.register (regs instr.register + 1))) := by
  apply sigma_reaches' (fun i => instrNetwork (prog.get i)) idx
  simp only [instrNetwork, hInstr]
  exact inc_simulation instr regs hSrcNeTgt

theorem rmNetwork_dec_nonzero_simulation
    (prog : RMProgram Q R) (idx : Fin prog.length)
    (instr : DecInstruction Q R) (hInstr : prog.get idx = .dec instr)
    (regs : R → Nat) (hr : 0 < regs instr.register)
    (hSrcNeNz : instr.source ≠ instr.target_nonzero) :
    (rmNetwork prog).Reaches
      (encodeRM instr.source regs)
      (encodeRM instr.target_nonzero
        (Function.update regs instr.register (regs instr.register - 1))) := by
  apply sigma_reaches' (fun i => instrNetwork (prog.get i)) idx
  simp only [instrNetwork, hInstr]
  exact dec_nonzero_simulation instr regs hr hSrcNeNz

theorem rmNetwork_dec_zero_simulation
    (prog : RMProgram Q R) (idx : Fin prog.length)
    (instr : DecInstruction Q R) (hInstr : prog.get idx = .dec instr)
    (regs : R → Nat) (hr : regs instr.register = 0)
    (hSrcNeZ : instr.source ≠ instr.target_zero) :
    (rmNetwork prog).Reaches
      (encodeRM instr.source regs)
      (encodeRM instr.target_zero regs) := by
  apply sigma_reaches' (fun i => instrNetwork (prog.get i)) idx
  simp only [instrNetwork, hInstr]
  exact dec_zero_simulation instr regs hr hSrcNeZ

end Ripple.sCRNUniversality.RegisterMachine
