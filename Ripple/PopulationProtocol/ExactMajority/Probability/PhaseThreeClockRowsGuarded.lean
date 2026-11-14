import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRegime

/-!
# The guarded §11 row split (N12, steps 3–4 interface, nested form)

PHASE3 §11 charges each row of the virtual-core failure on the prefix on which the
earlier rows hold ("all cap estimates are applied on the `F_T`-measurable
activation-good prefix and are subsequently intersected with front success"; the Main
credit estimate P12 is stopped at the `U_*` horizon of P3a). The unguarded row tails of
`PhaseThreeClockRows.RowTails` are therefore not the statements the paper proves: for
example the contact budget of P14 (`n^{-6} + n^{-21}`) uses the local cap allowance
`tick_local` of the shape row and the cap deadline of the cap row.

This file restates the row split in the nested form: the failure of a row is charged
only when every earlier row holds (`guardedFailure`), in the order activation, passage,
shape, cap, Main, contact. `virtual_core_bad_subset_guarded` is the inclusion of the
virtual-core failure into the union of the guarded failures (the first failing row is
charged), and `virtual_core_tail_of_guarded_rows` is `hcore` of
`PhaseThreeClockBudget.asynchronous_clock_estimate_of_tails` from the guarded tails
`GuardedRowTails`, with the same budgets and the same sum `6 / n ^ 5`. The regime row is
deterministic (`PhaseThreeClockRegime.regimeRow_of_asyncEntry`) and the counter reserve
follows from the activation and contact rows (`PhaseThreeClockReserve.rowReserve_of_rows`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRowsGuarded

open TimeTheorem PairLog StageEventSpec PhaseThreeClockVirtual PhaseThreeClockCore
  PhaseThreeClockProducer PhaseThreeClockAssembly PhaseThreeClockExit PhaseThreeClockRows
  PhaseThreeClockRegime PhaseThreeClockReserve

variable {n : ℕ} (init : InputCfg n)

/-- The failure of the row `R` on the guard `G`: a finite genuine first seed `S`, an entry
`T` within the early horizon, the guard, and the failure of the row. -/
def guardedFailure (G R : InputLog n → ℕ → ℕ → Prop) : Set (InputLog n) :=
  {ω | ∃ S T : ℕ, seedTime init 3 ω = (S : WithTop ℕ) ∧ T ≤ earlyHorizon n ∧
    AsyncEntry init ω S T ∧ G ω S T ∧ ¬ R ω S T}

theorem guardedFailure_mono {G G' R : InputLog n → ℕ → ℕ → Prop}
    (h : ∀ ω S T, G ω S T → G' ω S T) :
    guardedFailure init G R ⊆ guardedFailure init G' R := by
  rintro ω ⟨S, T, hs, hT, hentry, hG, hR⟩
  exact ⟨S, T, hs, hT, hentry, h ω S T hG, hR⟩

/-- The guards, in the order activation, passage, shape, cap, Main. -/
def guardPassage (ω : InputLog n) (S T : ℕ) : Prop := activationRow init ω S T

def guardShape (ω : InputLog n) (S T : ℕ) : Prop :=
  activationRow init ω S T ∧ passageRow init ω S T

def guardCap (ω : InputLog n) (S T : ℕ) : Prop :=
  activationRow init ω S T ∧ passageRow init ω S T ∧ shapeRow init ω S T

def guardMain (ω : InputLog n) (S T : ℕ) : Prop :=
  activationRow init ω S T ∧ passageRow init ω S T ∧ shapeRow init ω S T ∧ capRow init ω S T

def guardContact (ω : InputLog n) (S T : ℕ) : Prop :=
  activationRow init ω S T ∧ passageRow init ω S T ∧ shapeRow init ω S T ∧
    capRow init ω S T ∧ mainRow init ω S T

/-- The §11 row tails in the guarded form; the budgets are those of
`PhaseThreeClockRows.RowTails`. The contact row is guarded by the activation, passage,
shape and cap rows only (the Main row is not needed by P14). -/
structure GuardedRowTails : Prop where
  activation : law init (rowFailure init (activationRow init)) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 8)
  passage : law init (guardedFailure init (guardPassage init) (passageRow init)) ≤
    ENNReal.ofReal (1 / (n : ℝ) ^ 8)
  shape : law init (guardedFailure init (guardShape init) (shapeRow init)) ≤
    ENNReal.ofReal (2 / (n : ℝ) ^ 10)
  cap : law init (guardedFailure init (guardCap init) (capRow init)) ≤
    ENNReal.ofReal (3 / (n : ℝ) ^ 5)
  main : law init (guardedFailure init (guardMain init) (mainRow init)) ≤
    ENNReal.ofReal (1 / (n : ℝ) ^ 29)
  contact : law init (guardedFailure init (guardMain init) (contactRow init)) ≤
    ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21)

/-- The virtual-core failure is covered by the guarded row failures: the first failing
row is charged. -/
theorem virtual_core_bad_subset_guarded
    (hreg : ∀ ω S T, AsyncEntry init ω S T → regimeRow init ω S T)
    (hres : ∀ ω S T, AsyncEntry init ω S T → activationRow init ω S T →
      contactRow init ω S T → reserveRow init ω S T) :
    {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      (∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T) ∧ ¬ VirtualGoodAt init s ω} ⊆
    rowFailure init (activationRow init) ∪
      (guardedFailure init (guardPassage init) (passageRow init) ∪
      (guardedFailure init (guardShape init) (shapeRow init) ∪
      (guardedFailure init (guardCap init) (capRow init) ∪
      (guardedFailure init (guardMain init) (mainRow init) ∪
      guardedFailure init (guardContact init) (contactRow init))))) := by
  rintro ω ⟨s, hs, -, ⟨T, hT, hentry⟩, hbad⟩
  by_cases h2 : activationRow init ω s T
  · by_cases h3 : passageRow init ω s T
    · by_cases h4 : shapeRow init ω s T
      · by_cases h6 : capRow init ω s T
        · by_cases h5 : mainRow init ω s T
          · by_cases h7 : contactRow init ω s T
            · exact absurd (virtualGoodAt_of_rows init hT hentry (hreg ω s T hentry) h2 h3 h4
                h5 h6 h7 (hres ω s T hentry h2 h7)) hbad
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                ⟨s, T, hs, hT, hentry, ⟨h2, h3, h4, h6, h5⟩, h7⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨s, T, hs, hT, hentry, ⟨h2, h3, h4, h6⟩, h5⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, T, hs, hT, hentry, ⟨h2, h3, h4⟩, h6⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨s, T, hs, hT, hentry, ⟨h2, h3⟩, h4⟩))
    · exact Or.inr (Or.inl ⟨s, T, hs, hT, hentry, h2, h3⟩)
  · exact Or.inl ⟨s, T, hs, hT, hentry, h2⟩

/-- `hcore` from the guarded row tails. -/
theorem virtual_core_tail_of_guarded_rows (hn : 2 ≤ n) (h : GuardedRowTails init) :
    law init {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      (∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T) ∧ ¬ VirtualGoodAt init s ω} ≤
      ENNReal.ofReal (6 / (n : ℝ) ^ 5) := by
  have hcontact : law init (guardedFailure init (guardContact init) (contactRow init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21) :=
    (measure_mono (guardedFailure_mono init
      (fun ω S T hG => ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1⟩))).trans h.contact
  calc law init {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
        SeedProfile n init (trace init ω s) ∧
        (∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T) ∧ ¬ VirtualGoodAt init s ω}
      ≤ law init _ := measure_mono (virtual_core_bad_subset_guarded init
          (fun ω S T hentry => regimeRow_of_asyncEntry init ω hentry)
          (fun ω S T hentry hact hcontact => rowReserve_of_rows init ω hentry hact hcontact))
    _ ≤ law init _ + (law init _ + (law init _ + (law init _ + (law init _ + law init _)))) := by
        refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
        refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
        refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
        refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 8) + (ENNReal.ofReal (1 / (n : ℝ) ^ 8) +
          (ENNReal.ofReal (2 / (n : ℝ) ^ 10) + (ENNReal.ofReal (3 / (n : ℝ) ^ 5) +
          (ENNReal.ofReal (1 / (n : ℝ) ^ 29) +
          ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21))))) :=
        add_le_add h.activation (add_le_add h.passage (add_le_add h.shape
          (add_le_add h.cap (add_le_add h.main hcontact))))
    _ = ENNReal.ofReal (1 / (n : ℝ) ^ 8) + (ENNReal.ofReal (1 / (n : ℝ) ^ 8) +
          (ENNReal.ofReal (2 / (n : ℝ) ^ 10) + (ENNReal.ofReal (1 / (n : ℝ) ^ 29) +
          (ENNReal.ofReal (3 / (n : ℝ) ^ 5) +
          ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21))))) := by ring
    _ ≤ ENNReal.ofReal (6 / (n : ℝ) ^ 5) := row_budget hn

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRowsGuarded

end
