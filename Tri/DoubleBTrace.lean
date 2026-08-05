/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBInvariant
import Tri.Decay

/-!
# The counted Double-B trace and the fuel invariant (Theorem 2)

To convert the physical interaction clock into a *resolution-event* clock we run
the Double-B chain augmented with two counters: `fuel` (incremented by the
blank-creating/consuming reactions `xy`, `yb`) and `resolve` (incremented by the
level-changing reactions `xb`, `yb`).  The pathwise **fuel invariant**

`fuel + y ≤ y₀ + 2 · resolve`

is the Lean form of the paper's statement that at least `(k − y₀)/2` of `k`
productive reactions are resolutions.  Following `data/theorem2_design_Q319.md`.
-/

namespace Tri

open scoped ENNReal

/-- The Double-B configuration together with fuel and resolution counters. -/
structure DoubleTrace (n : ℕ) where
  cfg : DoubleState n
  fuel : ℕ
  resolve : ℕ

/-- The fuel counter increments on the two blank-touching neutral/down reactions. -/
def PairComp.fuelInc : PairComp → ℕ
  | .xy | .yb => 1
  | _ => 0

/-- The resolution counter increments on the two level-changing reactions. -/
def PairComp.resolveInc : PairComp → ℕ
  | .xb | .yb => 1
  | _ => 0

/-- The counted next-trace: supported reactions advance the config and counters;
zero-weight compositions leave the trace fixed (and carry no mass). -/
noncomputable def PairComp.nextDoubleTrace {n : ℕ} (q : DoubleTrace n) (k : PairComp) :
    DoubleTrace n :=
  if hk : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k = 0 then q
  else
    { cfg := ⟨PairComp.next q.cfg.1 k, PairComp.next_doubleInv n q.cfg.1 k q.cfg.2 hk⟩
      fuel := q.fuel + k.fuelInc
      resolve := q.resolve + k.resolveInc }

/-- The counted Double-B step. -/
noncomputable def doubleTraceStep (n : ℕ) (hn : 2 ≤ n) (q : DoubleTrace n) :
    PMF (DoubleTrace n) :=
  (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
    (by have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega)).map
      (PairComp.nextDoubleTrace q)

/-- Forgetting the counters projects the counted step onto `doubleStateStep`. -/
theorem doubleTraceStep_map_cfg (n : ℕ) (hn : 2 ≤ n) (q : DoubleTrace n) :
    (doubleTraceStep n hn q).map DoubleTrace.cfg = doubleStateStep n hn q.cfg := by
  unfold doubleTraceStep doubleStateStep
  rw [PMF.map_comp]
  apply PMF.map_change_on_zero_mass
  intro k hk
  unfold Function.comp PairComp.nextDoubleTrace PairComp.nextDoubleState at hk
  split_ifs at hk <;> simp_all

/-- The fuel invariant: `fuel + y ≤ y₀ + 2·resolve`. -/
def DoubleTrace.FuelInv {n : ℕ} (y₀ : ℕ) (q : DoubleTrace n) : Prop :=
  q.fuel + q.cfg.1.y ≤ y₀ + 2 * q.resolve

/-- The invariant holds at the start when `y₀` bounds the initial free-`Y` count. -/
theorem DoubleTrace.initial_fuelInv {n y₀ : ℕ} (s : DoubleState n) (hy : s.1.y ≤ y₀) :
    DoubleTrace.FuelInv y₀ ⟨s, 0, 0⟩ := by
  simp [DoubleTrace.FuelInv, hy]

/-- Every supported reaction preserves the fuel invariant.  Neutral `xy` spends a
`Y` and a fuel unit in step; each resolution spends at most two of the `2·resolve`
budget. -/
theorem PairComp.nextDoubleTrace_fuelInv {n y₀ : ℕ} (q : DoubleTrace n) (k : PairComp)
    (hq : q.FuelInv y₀) (hk : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0) :
    (PairComp.nextDoubleTrace q k).FuelInv y₀ := by
  rcases q with ⟨⟨⟨x, y, b⟩, hinv⟩, f, r⟩
  simp only [DoubleTrace.FuelInv] at hq
  simp only [PairComp.nextDoubleTrace]
  rw [dif_neg hk]
  simp only [DoubleTrace.FuelInv]
  cases k <;>
    simp only [PairComp.fuelInc, PairComp.resolveInc, PairComp.next, PairComp.weight] at hk ⊢ <;>
    first | omega | (rw [Nat.mul_ne_zero_iff] at hk; omega)

/-! ## From fuel to resolution count -/

/-- Support closure: a predicate closed under single steps is closed under any
deterministic iterate (on the support). -/
theorem iter_support_closed {α : Type*} (K : α → PMF α) (P : α → Prop)
    (hstep : ∀ s, P s → ∀ z, K s z ≠ 0 → P z) :
    ∀ T s z, P s → iter K T s z ≠ 0 → P z := by
  intro T
  induction T with
  | zero =>
      intro s z hs hz
      simp only [iter, PMF.pure_apply] at hz
      by_cases h : z = s
      · rwa [h]
      · simp [h] at hz
  | succ T ih =>
      intro s z hs hz
      rw [iter_succ, PMF.bind_apply] at hz
      by_contra hzP
      apply hz
      rw [ENNReal.tsum_eq_zero]
      intro a
      by_cases hKa : K s a = 0
      · simp [hKa]
      · have haP := hstep s hs a hKa
        have hiaz : iter K T a z = 0 := by
          by_contra hne; exact hzP (ih a z haP hne)
        simp [hiaz]

/-- One counted step preserves the fuel invariant on its support. -/
theorem doubleTraceStep_fuelInv_of_apply_ne_zero {n y₀ : ℕ} (hn : 2 ≤ n) (a : DoubleTrace n)
    (ha : a.FuelInv y₀) (z : DoubleTrace n) (haz : doubleTraceStep n hn a z ≠ 0) :
    z.FuelInv y₀ := by
  unfold doubleTraceStep at haz
  rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at haz
  push_neg at haz
  obtain ⟨k, hk⟩ := haz
  split_ifs at hk with hzk
  · have hwk : PairComp.weight a.cfg.1.x a.cfg.1.y a.cfg.1.b k ≠ 0 :=
      fun hw => hk (dbPairPMF_zero_of_weight_zero hw)
    rw [hzk]
    exact PairComp.nextDoubleTrace_fuelInv a k ha hwk
  · exact absurd rfl hk

/-- The fuel invariant holds along the whole counted chain. -/
theorem doubleTrace_iter_fuelInv {n y₀ T : ℕ} (hn : 2 ≤ n) (q z : DoubleTrace n)
    (hq : q.FuelInv y₀) (hz : iter (doubleTraceStep n hn) T q z ≠ 0) :
    z.FuelInv y₀ :=
  iter_support_closed (doubleTraceStep n hn) (DoubleTrace.FuelInv y₀)
    (fun a ha z haz => doubleTraceStep_fuelInv_of_apply_ne_zero hn a ha z haz) T q z hq hz

/-- **Fuel forces resolutions.**  If enough fuel has accrued, at least `M`
resolution events have occurred — the Double-B form of the paper's `(k−y₀)/2`. -/
theorem resolve_of_fuel {n y₀ M : ℕ} (q : DoubleTrace n)
    (hq : q.FuelInv y₀) (hf : y₀ + 2 * M ≤ q.fuel) : M ≤ q.resolve := by
  unfold DoubleTrace.FuelInv at hq; omega

/-! ## Per-label counter/config after one trace step (event-indexed-direction substrate) -/

/-- The resolve counter advances by `resolveInc` on a supported label. -/
theorem nextTrace_resolve (n : ℕ) (q : DoubleTrace n) (k : PairComp)
    (hw : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0) :
    (PairComp.nextDoubleTrace q k).resolve = q.resolve + k.resolveInc := by
  rw [PairComp.nextDoubleTrace, dif_neg hw]

/-- The configuration advances by `PairComp.next` on a supported label. -/
theorem nextTrace_cfg (n : ℕ) (q : DoubleTrace n) (k : PairComp)
    (hw : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0) :
    (PairComp.nextDoubleTrace q k).cfg = ⟨PairComp.next q.cfg.1 k,
      PairComp.next_doubleInv n q.cfg.1 k q.cfg.2 hw⟩ := by
  rw [PairComp.nextDoubleTrace, dif_neg hw]

end Tri
