/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBKernel
import Tri.DoubleBTrace

/-!
# The counted Heavy-B trace and its three exact ledgers

`Tri/HeavyBEmulation.lean` established that the Heavy-B clause cannot be
obtained by transport — neither onto Double-B (a time change) nor onto the tri
chain (the odds agree only when `b = 1` or `x = y`). So the two-parameter
potential engine has to be re-instantiated here, exactly as Double-B's was.

This file is the trace layer that engine runs on: the configuration augmented
with the three event counters that matter, plus the identities relating them to
the physical counts.

## Which counters, and why three rather than two

Double-B's trace carries `fuel` and `resolve`. Heavy-B wants the two
resolutions kept APART, because its `Y`-resolution moves `y` by `+2` while its
creation moves it by `−1`, so the `Y` ledger has a coefficient that a merged
`resolve` counter would hide. Keeping `up` and `down` separate makes all three
identities exact rather than inequalities.

## The three ledgers, all subtraction-free and all exact

```text
level:   heavyLevel + down  =  L₀ + up        (motion only at resolutions)
Y side:  y + fuel           =  y₀ + 2·down
X side:  x + fuel           =  x₀ + 2·up
```

The first is the Double-B property made quantitative: the level's displacement
is exactly the resolution imbalance, with creations and inert events
contributing nothing. The other two say each species' count is its start plus
twice its own resolutions, less one per creation — the `2` being the blank's
mass, which is where Heavy-B differs from Double-B arithmetically.

Adding the last two recovers the population invariant, which is a useful
consistency check: `x + y + 2·fuel = x₀ + y₀ + 2·(up + down)`, and
`fuel = up + down` is NOT assumed — the identities are independent.
-/

namespace Tri

open scoped ENNReal

/-- Heavy-B configuration augmented with the three event counters. -/
structure HeavyTrace (n : ℕ) where
  cfg : HeavyState n
  /-- number of `X + B → 3X` resolutions -/
  up : ℕ
  /-- number of `Y + B → 3Y` resolutions -/
  down : ℕ
  /-- number of `X + Y → B` creations -/
  fuel : ℕ

namespace PairComp

def heavyUpInc : PairComp → ℕ
  | .xb => 1
  | _ => 0

def heavyDownInc : PairComp → ℕ
  | .yb => 1
  | _ => 0

def heavyFuelInc : PairComp → ℕ
  | .xy => 1
  | _ => 0

/-- Guarded counted update; zero-weight compositions leave the whole trace
fixed, counters included. -/
noncomputable def nextHeavyTrace {n : ℕ} (q : HeavyTrace n) (k : PairComp) :
    HeavyTrace n :=
  if hk : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k = 0 then q
  else
    { cfg := ⟨PairComp.heavyNext q.cfg.1 k,
        PairComp.heavyNext_heavyInv n q.cfg.1 k q.cfg.2 hk⟩
      up := q.up + k.heavyUpInc
      down := q.down + k.heavyDownInc
      fuel := q.fuel + k.heavyFuelInc }

end PairComp

/-- One counted Heavy-B interaction, totalized like `heavyStateStep`. -/
noncomputable def heavyTraceStep (n : ℕ) (q : HeavyTrace n) :
    PMF (HeavyTrace n) :=
  if h : 2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b then
    (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b h).map (PairComp.nextHeavyTrace q)
  else PMF.pure q

/-! ### The three ledgers -/

/-- **The level ledger.**  The level's displacement is exactly the resolution
imbalance; creations and inert events contribute nothing.  This is the Double-B
property made quantitative. -/
def HeavyTrace.LevelLedger {n : ℕ} (L₀ : ℕ) (q : HeavyTrace n) : Prop :=
  BiCfg.heavyLevel q.cfg.1 + q.down = L₀ + q.up

/-- **The `Y` ledger.**  Each `Y`-resolution adds two `Y`s; each creation
removes one. -/
def HeavyTrace.YLedger {n : ℕ} (y₀ : ℕ) (q : HeavyTrace n) : Prop :=
  q.cfg.1.y + q.fuel = y₀ + 2 * q.down

/-- **The `X` ledger**, symmetrically. -/
def HeavyTrace.XLedger {n : ℕ} (x₀ : ℕ) (q : HeavyTrace n) : Prop :=
  q.cfg.1.x + q.fuel = x₀ + 2 * q.up

theorem HeavyTrace.initial_levelLedger {n : ℕ} (s : HeavyState n) :
    HeavyTrace.LevelLedger (BiCfg.heavyLevel s.1) ⟨s, 0, 0, 0⟩ := by
  simp [HeavyTrace.LevelLedger]

theorem HeavyTrace.initial_yLedger {n : ℕ} (s : HeavyState n) :
    HeavyTrace.YLedger s.1.y ⟨s, 0, 0, 0⟩ := by
  simp [HeavyTrace.YLedger]

theorem HeavyTrace.initial_xLedger {n : ℕ} (s : HeavyState n) :
    HeavyTrace.XLedger s.1.x ⟨s, 0, 0, 0⟩ := by
  simp [HeavyTrace.XLedger]

/-- Each positive-weight event preserves the level ledger. -/
theorem PairComp.nextHeavyTrace_levelLedger {n L₀ : ℕ} (q : HeavyTrace n)
    (k : PairComp) (hq : q.LevelLedger L₀)
    (hk : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0) :
    (PairComp.nextHeavyTrace q k).LevelLedger L₀ := by
  obtain ⟨⟨⟨x, y, b⟩, hinv⟩, up, down, fuel⟩ := q
  unfold PairComp.nextHeavyTrace
  rw [dif_neg hk]
  simp only [HeavyTrace.LevelLedger, BiCfg.heavyLevel] at hq ⊢
  cases k <;>
    simp only [PairComp.heavyUpInc, PairComp.heavyDownInc,
      PairComp.heavyFuelInc, PairComp.heavyNext, PairComp.weight] at hk ⊢ <;>
    first
    | omega
    | (rw [Nat.mul_ne_zero_iff] at hk; omega)

theorem PairComp.nextHeavyTrace_yLedger {n y₀ : ℕ} (q : HeavyTrace n)
    (k : PairComp) (hq : q.YLedger y₀)
    (hk : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0) :
    (PairComp.nextHeavyTrace q k).YLedger y₀ := by
  obtain ⟨⟨⟨x, y, b⟩, hinv⟩, up, down, fuel⟩ := q
  unfold PairComp.nextHeavyTrace
  rw [dif_neg hk]
  simp only [HeavyTrace.YLedger] at hq ⊢
  cases k <;>
    simp only [PairComp.heavyUpInc, PairComp.heavyDownInc,
      PairComp.heavyFuelInc, PairComp.heavyNext, PairComp.weight] at hk ⊢ <;>
    first
    | omega
    | (rw [Nat.mul_ne_zero_iff] at hk; omega)

theorem PairComp.nextHeavyTrace_xLedger {n x₀ : ℕ} (q : HeavyTrace n)
    (k : PairComp) (hq : q.XLedger x₀)
    (hk : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0) :
    (PairComp.nextHeavyTrace q k).XLedger x₀ := by
  obtain ⟨⟨⟨x, y, b⟩, hinv⟩, up, down, fuel⟩ := q
  unfold PairComp.nextHeavyTrace
  rw [dif_neg hk]
  simp only [HeavyTrace.XLedger] at hq ⊢
  cases k <;>
    simp only [PairComp.heavyUpInc, PairComp.heavyDownInc,
      PairComp.heavyFuelInc, PairComp.heavyNext, PairComp.weight] at hk ⊢ <;>
    first
    | omega
    | (rw [Nat.mul_ne_zero_iff] at hk; omega)

/-- A ledger preserved by every positive-weight event is preserved by the
totalized step: the self-loop branch changes nothing. -/
theorem heavyTraceStep_ledger_of_apply_ne_zero {n : ℕ}
    (P : HeavyTrace n → Prop)
    (hstep : ∀ (q : HeavyTrace n) (k : PairComp), P q →
      PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0 →
      P (PairComp.nextHeavyTrace q k))
    (q : HeavyTrace n) (hq : P q) (z : HeavyTrace n)
    (hqz : heavyTraceStep n q z ≠ 0) : P z := by
  unfold heavyTraceStep at hqz
  split_ifs at hqz with h
  · rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
    push Not at hqz
    obtain ⟨k, hk⟩ := hqz
    split_ifs at hk with hzk
    · have hw : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0 := by
        intro hw
        exact hk (by
          simp [dbPairPMF_apply, hw])
      rw [hzk]
      exact hstep q k hq hw
    · exact absurd rfl hk
  · rw [PMF.pure_apply] at hqz
    by_cases hzq : z = q
    · rwa [hzq]
    · simp [hzq] at hqz

theorem heavyTrace_iter_levelLedger {n L₀ T : ℕ} (q z : HeavyTrace n)
    (hq : q.LevelLedger L₀)
    (hz : iter (heavyTraceStep n) T q z ≠ 0) :
    z.LevelLedger L₀ :=
  iter_support_closed (heavyTraceStep n) (HeavyTrace.LevelLedger L₀)
    (fun a ha z haz =>
      heavyTraceStep_ledger_of_apply_ne_zero _
        (fun q k hq hk => PairComp.nextHeavyTrace_levelLedger q k hq hk)
        a ha z haz)
    T q z hq hz

theorem heavyTrace_iter_yLedger {n y₀ T : ℕ} (q z : HeavyTrace n)
    (hq : q.YLedger y₀)
    (hz : iter (heavyTraceStep n) T q z ≠ 0) :
    z.YLedger y₀ :=
  iter_support_closed (heavyTraceStep n) (HeavyTrace.YLedger y₀)
    (fun a ha z haz =>
      heavyTraceStep_ledger_of_apply_ne_zero _
        (fun q k hq hk => PairComp.nextHeavyTrace_yLedger q k hq hk)
        a ha z haz)
    T q z hq hz

theorem heavyTrace_iter_xLedger {n x₀ T : ℕ} (q z : HeavyTrace n)
    (hq : q.XLedger x₀)
    (hz : iter (heavyTraceStep n) T q z ≠ 0) :
    z.XLedger x₀ :=
  iter_support_closed (heavyTraceStep n) (HeavyTrace.XLedger x₀)
    (fun a ha z haz =>
      heavyTraceStep_ledger_of_apply_ne_zero _
        (fun q k hq hk => PairComp.nextHeavyTrace_xLedger q k hq hk)
        a ha z haz)
    T q z hq hz

/-- **The fuel bound the direction engine consumes.**  Merging the two
resolution counters costs an inequality, which is why they are kept apart
above; but the merged form is what the potential's `η^resolve` factor sees. -/
theorem heavyTrace_fuel_le {n y₀ : ℕ} (q : HeavyTrace n) (hq : q.YLedger y₀) :
    q.fuel + q.cfg.1.y ≤ y₀ + 2 * (q.up + q.down) := by
  simp only [HeavyTrace.YLedger] at hq
  omega

/-- The two species ledgers together recover the population invariant, an
independent consistency check on the counters. -/
theorem heavyTrace_ledgers_consistent {n x₀ y₀ : ℕ} (q : HeavyTrace n)
    (hx : q.XLedger x₀) (hy : q.YLedger y₀) :
    q.cfg.1.x + q.cfg.1.y + 2 * q.fuel
      = x₀ + y₀ + 2 * (q.up + q.down) := by
  simp only [HeavyTrace.XLedger, HeavyTrace.YLedger] at hx hy
  omega

/-! ### The resolution floor: both ledgers together beat either one

A productive-reaction quota `K` forces a floor on the resolution count, and the
paper's Heavy-B phase-1 quota is `K = 7n`.

The one-ledger argument (drop `y ≥ 0` from the `Y` ledger, so `F ≤ y₀ + 2D`,
hence `K ≤ y₀ + 3R`) gives `2n ≤ R`. Using BOTH exact ledgers gives strictly
more: adding `F ≤ y₀ + 2D` and `F ≤ x₀ + 2U` yields `2F ≤ x₀ + y₀ + 2R`, and
with the population invariant `x₀ + y₀ + 2b₀ = n` this is

```text
2K + 2b₀ ≤ n + 4R
```

so at `K = 7n` the floor is `13n ≤ 4R`, i.e. `R ≥ 3.25n` rather than `2n`.

That the sharper floor exists is what makes keeping `up` and `down` separate pay
off twice: once for the exact ledgers, once here. -/

/-- **The resolution floor from both ledgers**, subtraction-free.  A productive
quota `K` forces `2K + 2b₀ ≤ n + 4(up + down)`. -/
theorem heavyTrace_resolution_floor {n x₀ y₀ b₀ K : ℕ} (q : HeavyTrace n)
    (hx : q.XLedger x₀) (hy : q.YLedger y₀)
    (hinv : x₀ + y₀ + 2 * b₀ = n)
    (hK : q.fuel + q.up + q.down = K) :
    2 * K + 2 * b₀ ≤ n + 4 * (q.up + q.down) := by
  simp only [HeavyTrace.XLedger, HeavyTrace.YLedger] at hx hy
  omega

/-- **Phase 1.**  At the paper's Heavy-B quota `K = 7n` the floor is
`13n ≤ 4(up + down)` — strictly stronger than the `2n ≤ up + down` the `Y`
ledger alone gives. -/
theorem heavyTrace_resolution_floor_phase1 {n x₀ y₀ b₀ : ℕ} (q : HeavyTrace n)
    (hx : q.XLedger x₀) (hy : q.YLedger y₀)
    (hinv : x₀ + y₀ + 2 * b₀ = n)
    (hK : q.fuel + q.up + q.down = 7 * n) :
    13 * n ≤ 4 * (q.up + q.down) := by
  have h := heavyTrace_resolution_floor q hx hy hinv hK
  omega

/-- The convenient `ℕ`-arithmetic corollary: `3n ≤ up + down`. -/
theorem heavyTrace_resolution_floor_three {n x₀ y₀ b₀ : ℕ} (q : HeavyTrace n)
    (hx : q.XLedger x₀) (hy : q.YLedger y₀)
    (hinv : x₀ + y₀ + 2 * b₀ = n)
    (hK : q.fuel + q.up + q.down = 7 * n) :
    3 * n ≤ q.up + q.down := by
  have h := heavyTrace_resolution_floor_phase1 q hx hy hinv hK
  omega

/-! ### Projection: forgetting the counters recovers `heavyStateStep` -/

private theorem heavyTraceStep_unfold {n : ℕ} (hn : 3 ≤ n) (q : HeavyTrace n) :
    heavyTraceStep n q
      = (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg)).map (PairComp.nextHeavyTrace q) := by
  unfold heavyTraceStep
  exact dif_pos (heavy_two_entities hn q.cfg)

private theorem heavyStateStep_unfold' {n : ℕ} (hn : 3 ≤ n) (s : HeavyState n) :
    heavyStateStep n s
      = (dbPairPMF s.1.x s.1.y s.1.b
            (heavy_two_entities hn s)).map (PairComp.nextHeavyState s) := by
  unfold heavyStateStep
  exact dif_pos (heavy_two_entities hn s)

/-- Forgetting the counters projects the counted Heavy-B step onto
`heavyStateStep`. -/
theorem heavyTraceStep_map_cfg {n : ℕ} (hn : 3 ≤ n) (q : HeavyTrace n) :
    (heavyTraceStep n q).map HeavyTrace.cfg = heavyStateStep n q.cfg := by
  let p := dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (heavy_two_entities hn q.cfg)
  calc (heavyTraceStep n q).map HeavyTrace.cfg
      = (p.map (PairComp.nextHeavyTrace q)).map HeavyTrace.cfg :=
        congrArg (PMF.map HeavyTrace.cfg) (heavyTraceStep_unfold hn q)
    _ = p.map (HeavyTrace.cfg ∘ PairComp.nextHeavyTrace q) :=
        PMF.map_comp _ _ _
    _ = p.map (PairComp.nextHeavyState q.cfg) := by
        apply PMF.map_change_on_zero_mass
        intro k hk
        simp only [Function.comp, PairComp.nextHeavyTrace, PairComp.nextHeavyState] at hk
        split_ifs at hk <;> simp_all
    _ = heavyStateStep n q.cfg :=
        (heavyStateStep_unfold' hn q.cfg).symm

/-- The subtype iterate is the pushforward of the trace iterate. -/
theorem iter_heavyStateStep_eq_map {n : ℕ} (hn : 3 ≤ n) :
    ∀ (T : ℕ) (q : HeavyTrace n),
    iter (heavyStateStep n) T q.cfg
      = (iter (heavyTraceStep n) T q).map HeavyTrace.cfg := by
  intro T
  induction T with
  | zero => intro q; rw [iter_zero, iter_zero, PMF.pure_map]
  | succ T ih =>
    intro q
    rw [iter_succ, iter_succ, ← heavyTraceStep_map_cfg hn q, PMF.map_bind]
    rw [show (PMF.map HeavyTrace.cfg (heavyTraceStep n q)).bind
          (iter (heavyStateStep n) T)
        = (heavyTraceStep n q).bind
          (fun a => iter (heavyStateStep n) T (HeavyTrace.cfg a)) by
      simp only [PMF.map, PMF.bind_bind, Function.comp, PMF.pure_bind]]
    congr 1
    funext a
    exact ih a

end Tri

#print axioms Tri.heavyTraceStep_map_cfg
#print axioms Tri.iter_heavyStateStep_eq_map
#print axioms Tri.PairComp.nextHeavyTrace_levelLedger
#print axioms Tri.PairComp.nextHeavyTrace_yLedger
#print axioms Tri.PairComp.nextHeavyTrace_xLedger
#print axioms Tri.heavyTrace_iter_levelLedger
#print axioms Tri.heavyTrace_iter_yLedger
#print axioms Tri.heavyTrace_iter_xLedger
#print axioms Tri.heavyTrace_fuel_le
#print axioms Tri.heavyTrace_ledgers_consistent
#print axioms Tri.heavyTrace_resolution_floor
#print axioms Tri.heavyTrace_resolution_floor_phase1
#print axioms Tri.heavyTrace_resolution_floor_three
