/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBDirection
import Tri.Theorem2
import Tri.Freeze
import Tri.Compose
import Tri.DoubleBFeller

/-!
# Theorem 2 assembly, part 1: chain projections

The raw `doubleBChain` (on `BiCfg`), the subtype chain `doubleStateStep` (on
`DoubleState`), and the counted chain `doubleTraceStep` (on `DoubleTrace`) are all
projections of one another.  `iter_map_equivariant` iterates any kernel-intertwining
projection, and the two corollaries specialise it, so the non-consensus mass of the
physical chain equals a mass on the counted trace — where the direction/ruin
estimates live.
-/

namespace Tri
open scoped ENNReal

/-- **Iterating a projection.**  If `π` intertwines the kernels (`(K s).map π =
L (π s)`), then the whole iterate intertwines: `iter L T (π s₀) = (iter K T s₀).map π`. -/
theorem iter_map_equivariant {α β : Type*} (K : α → PMF α) (L : β → PMF β) (π : α → β)
    (h : ∀ s, (K s).map π = L (π s)) :
    ∀ (T : ℕ) (s₀ : α), iter L T (π s₀) = (iter K T s₀).map π := by
  intro T
  induction T with
  | zero => intro s₀; rw [iter_zero, iter_zero, PMF.pure_map]
  | succ T ih =>
    intro s₀
    rw [iter_succ, iter_succ, ← h s₀, PMF.map_bind]
    rw [show (PMF.map π (K s₀)).bind (iter L T)
        = (K s₀).bind (fun a => iter L T (π a)) by
      simp only [PMF.map, PMF.bind_bind, Function.comp, PMF.pure_bind]]
    congr 1
    funext a
    exact ih a

/-- The raw `doubleBChain` iterate is the pushforward of the subtype iterate. -/
theorem iter_doubleBChain_eq_map (n : ℕ) (hn : 2 ≤ n) (T : ℕ) (s : DoubleState n) :
    iter doubleBChain T s.1 = (iter (doubleStateStep n hn) T s).map Subtype.val :=
  iter_map_equivariant (doubleStateStep n hn) doubleBChain Subtype.val
    (doubleStateStep_map_val n hn) T s

/-- The subtype iterate is the pushforward (forget counters) of the trace iterate. -/
theorem iter_doubleStateStep_eq_map (n : ℕ) (hn : 2 ≤ n) (T : ℕ) (q : DoubleTrace n) :
    iter (doubleStateStep n hn) T q.cfg = (iter (doubleTraceStep n hn) T q).map DoubleTrace.cfg :=
  iter_map_equivariant (doubleTraceStep n hn) (doubleStateStep n hn) DoubleTrace.cfg
    (doubleTraceStep_map_cfg n hn) T q

/-- **Non-consensus mass, lifted to the trace.**  The raw non-consensus mass after
`T` steps equals the trace mass of non-consensus configurations. -/
theorem nonconsensus_mass_eq_trace (n : ℕ) (hn : 2 ≤ n) (T : ℕ) (q₀ : DoubleTrace n) :
    ∑' z : BiCfg, (if BiXConsensus n z then 0 else iter doubleBChain T q₀.cfg.1 z)
      = ∑' q : DoubleTrace n,
          (if BiXConsensus n q.cfg.1 then 0 else iter (doubleTraceStep n hn) T q₀ q) := by
  -- push through both projections
  rw [iter_doubleBChain_eq_map n hn T q₀.cfg, iter_doubleStateStep_eq_map n hn T q₀, PMF.map_comp]
  set p := iter (doubleTraceStep n hn) T q₀ with hp
  set g : DoubleTrace n → BiCfg := Subtype.val ∘ DoubleTrace.cfg with hg
  have hL : ∀ z : BiCfg, (if BiXConsensus n z then (0 : ℝ≥0∞) else (p.map g) z)
      = (p.map g) z * (if BiXConsensus n z then 0 else 1) := by
    intro z; split_ifs <;> simp
  rw [tsum_congr hL, ← expect, expect_map, expect]
  apply tsum_congr; intro a
  simp only [Function.comp_apply, hg]
  split_ifs <;> simp

variable {α : Type*}

/-- Absorption: once inside the frozen set `B`, the frozen chain stays put. -/
theorem iter_freeze_absorb (B : α → Prop) [DecidablePred B] (K : α → PMF α)
    (T : ℕ) (s : α) (hs : B s) : iter (freeze B K) T s = PMF.pure s := by
  induction T with
  | zero => rfl
  | succ T ih => rw [iter_succ, freeze_of_mem s hs, PMF.pure_bind, ih]

/-- Masked mass as an expectation of the `¬Q` indicator. -/
theorem masked_eq_expect (Q : α → Prop) [DecidablePred Q] (p : PMF α) :
    (∑' z, if Q z then (0 : ℝ≥0∞) else p z)
      = expect p (fun z => if Q z then 0 else 1) := by
  unfold expect
  refine tsum_congr fun z => ?_
  by_cases hQ : Q z <;> simp [hQ]

/-- The `¬Q` indicator expectation never exceeds `1`. -/
theorem expect_indicator_le_one (Q : α → Prop) [DecidablePred Q] (p : PMF α) :
    expect p (fun z => if Q z then (0 : ℝ≥0∞) else 1) ≤ 1 := by
  calc expect p (fun z => if Q z then (0 : ℝ≥0∞) else 1)
      = ∑' z, p z * (if Q z then (0:ℝ≥0∞) else 1) := rfl
    _ ≤ ∑' z, p z * 1 := ENNReal.tsum_le_tsum fun z => by gcongr; split_ifs <;> simp
    _ = 1 := by simp [PMF.tsum_coe]

/-- **Freezing into a `¬Q`-absorbing set can only increase the `¬Q` mass.** -/
theorem mass_le_freeze (K : α → PMF α) (B Q : α → Prop) [DecidablePred B] [DecidablePred Q]
    (hBQ : ∀ s, B s → ¬ Q s) :
    ∀ (T : ℕ) (s : α), ∑' z, (if Q z then (0 : ℝ≥0∞) else iter K T s z)
      ≤ ∑' z, (if Q z then (0 : ℝ≥0∞) else iter (freeze B K) T s z) := by
  set ν : α → ℝ≥0∞ := fun z => if Q z then 0 else 1 with hν
  suffices h : ∀ (T : ℕ) (s : α), expect (iter K T s) ν ≤ expect (iter (freeze B K) T s) ν by
    intro T s; rw [masked_eq_expect Q, masked_eq_expect Q]; exact h T s
  intro T
  induction T with
  | zero => intro s; simp [expect_pure]
  | succ T ih =>
    intro s
    rw [iter_succ, iter_succ, expect_bind, expect_bind]
    by_cases hB : B s
    · rw [freeze_of_mem s hB]
      have hRHS : ∑' b, (PMF.pure s) b * expect (iter (freeze B K) T b) ν = 1 := by
        rw [tsum_eq_single s (by intro b hb; simp [PMF.pure_apply, hb])]
        rw [PMF.pure_apply, if_pos rfl, one_mul, iter_freeze_absorb B K T s hB, expect_pure]
        simp [hν, hBQ s hB]
      rw [hRHS]
      calc ∑' b, K s b * expect (iter K T b) ν
          ≤ ∑' b, K s b * 1 :=
            ENNReal.tsum_le_tsum fun b => by gcongr; exact expect_indicator_le_one Q (iter K T b)
        _ = 1 := by simp [PMF.tsum_coe]
    · rw [freeze_of_not_mem s hB]
      exact ENNReal.tsum_le_tsum fun b => by gcongr; exact ih b

/-- `doubleDirStop` is exactly the generic `freeze` at the ruin set `level ≤ aLo`. -/
theorem doubleDirStop_eq_freeze (n : ℕ) (hn : 2 ≤ n) (aLo : ℕ) :
    doubleDirStop n hn aLo
      = freeze (fun q : DoubleTrace n => q.cfg.1.doubleLevel ≤ aLo) (doubleTraceStep n hn) := by
  funext q
  unfold doubleDirStop freeze
  by_cases h : q.cfg.1.doubleLevel ≤ aLo
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg h]

/-- Non-consensus is exactly a sub-maximal level. -/
theorem noncons_iff_level {n : ℕ} (s : DoubleState n) :
    ¬ BiXConsensus n s.1 ↔ s.1.doubleLevel < 2 * n := by
  rcases s with ⟨⟨x, y, b⟩, h⟩
  simp only [BiCfg.doubleLevel, BiCfg.DoubleInv, BiXConsensus] at h ⊢
  omega

/-- **Set-cover split of the trace non-consensus mass.**  Bounds it by the ruin
mass (`level ≤ aLo`), the many-resolutions mass (`level < 2n ∧ M ≤ resolve`), and
the few-resolutions band mass (`aLo < level < 2n ∧ resolve < M`). -/
theorem trace_noncons_split (n : ℕ) (hn : 2 ≤ n) (aLo M T : ℕ) (haLo : aLo < 2 * n)
    (q₀ : DoubleTrace n) :
    ∑' q, (if BiXConsensus n q.cfg.1 then 0 else iter (doubleTraceStep n hn) T q₀ q)
      ≤ (∑' q, (if q.cfg.1.doubleLevel ≤ aLo then
            iter (doubleDirStop n hn aLo) T q₀ q else 0))
        + (∑' q, (if q.cfg.1.doubleLevel < 2 * n ∧ M ≤ q.resolve then
            iter (doubleDirStop n hn aLo) T q₀ q else 0))
        + (∑' q, (if aLo + 1 ≤ q.cfg.1.doubleLevel ∧ q.cfg.1.doubleLevel < 2 * n
            ∧ q.resolve < M then iter (doubleDirStop n hn aLo) T q₀ q else 0)) := by
  have hBQ : ∀ q : DoubleTrace n, q.cfg.1.doubleLevel ≤ aLo → ¬ BiXConsensus n q.cfg.1 := by
    intro q hq; rw [noncons_iff_level]; omega
  have hdom := mass_le_freeze (doubleTraceStep n hn)
    (fun q : DoubleTrace n => q.cfg.1.doubleLevel ≤ aLo) (fun q => BiXConsensus n q.cfg.1) hBQ T q₀
  rw [← doubleDirStop_eq_freeze n hn aLo] at hdom
  refine le_trans hdom ?_
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun q => ?_
  set p := iter (doubleDirStop n hn aLo) T q₀ q with hp
  by_cases hcons : BiXConsensus n q.cfg.1
  · simp [hcons]
  · rw [if_neg hcons]
    have hlv : q.cfg.1.doubleLevel < 2 * n := (noncons_iff_level q.cfg).1 hcons
    by_cases h1 : q.cfg.1.doubleLevel ≤ aLo
    · rw [if_pos h1]
      exact le_trans (self_le_add_right _ _) (self_le_add_right _ _)
    · rw [if_neg h1]
      by_cases h2 : M ≤ q.resolve
      · rw [if_pos ⟨hlv, h2⟩, zero_add]
        exact self_le_add_right _ _
      · rw [if_neg (by tauto), if_pos ⟨by omega, hlv, by omega⟩, zero_add, zero_add]

/-- The frozen trace chain (at the ruin set) projects onto the frozen state chain. -/
theorem freezeTrace_map_cfg (n : ℕ) (hn : 2 ≤ n) (aLo : ℕ) (q : DoubleTrace n) :
    (freeze (fun q' : DoubleTrace n => q'.cfg.1.doubleLevel ≤ aLo) (doubleTraceStep n hn) q).map
        DoubleTrace.cfg
      = freeze (fun s : DoubleState n => s.1.doubleLevel ≤ aLo) (doubleStateStep n hn) q.cfg := by
  unfold freeze
  by_cases h : q.cfg.1.doubleLevel ≤ aLo
  · rw [if_pos h, if_pos h, PMF.pure_map]
  · rw [if_neg h, if_neg h, doubleTraceStep_map_cfg]

/-- **Ruin term transfer.**  The frozen-trace ruin mass equals the frozen-state
ruin mass (`hitProb`), hence is bounded by `doubleB_ruin`. -/
theorem ruin_term_le (n : ℕ) (hn : 2 ≤ n) (aLo bHi k T : ℕ)
    (hpop2n : aLo + bHi + 2 = 2 * n) (haLo : 0 < aLo) (hbHi : 0 < bHi) (hmaj : bHi ≤ aLo)
    (q₀ : DoubleTrace n) (hstart : q₀.cfg.1.doubleLevel = aLo + k) :
    ∑' q, (if q.cfg.1.doubleLevel ≤ aLo then iter (doubleDirStop n hn aLo) T q₀ q else 0)
      ≤ ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k := by
  classical
  have hproj : iter (freeze (fun s : DoubleState n => s.1.doubleLevel ≤ aLo)
        (doubleStateStep n hn)) T q₀.cfg
      = (iter (freeze (fun q' : DoubleTrace n => q'.cfg.1.doubleLevel ≤ aLo)
        (doubleTraceStep n hn)) T q₀).map DoubleTrace.cfg :=
    iter_map_equivariant _ _ DoubleTrace.cfg (freezeTrace_map_cfg n hn aLo) T q₀
  have hEq : ∑' q, (if q.cfg.1.doubleLevel ≤ aLo then
        iter (doubleDirStop n hn aLo) T q₀ q else 0)
      = hitProb (fun s : DoubleState n => s.1.doubleLevel ≤ aLo)
          (doubleStateStep n hn) T q₀.cfg := by
    rw [doubleDirStop_eq_freeze n hn aLo, hitProb, hproj, expect_map]
    unfold expect ind
    refine tsum_congr fun q => ?_
    by_cases h : q.cfg.1.doubleLevel ≤ aLo <;>
      simp only [h, if_true, if_false, mul_one, mul_zero]
  rw [hEq]
  refine le_trans (le_iSup (fun T => hitProb (fun s : DoubleState n => s.1.doubleLevel ≤ aLo)
    (doubleStateStep n hn) T q₀.cfg) T) ?_
  exact doubleB_ruin n aLo bHi k hn hpop2n haLo hbHi hmaj q₀.cfg hstart

/-- **Direction term bound.**  The many-resolutions band mass is bounded by the
event-indexed direction tail, at threshold `2n−1`. -/
theorem direction_term_le (n : ℕ) (hn : 2 ≤ n) (aLo bHi M T : ℕ)
    (haLo : 0 < aLo) (hmaj : bHi ≤ aLo) (heq : aLo + bHi = 2 * n)
    (w η u : ℝ≥0∞) (hu : u = (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (q₀ : DoubleTrace n) (hr0 : q₀.resolve = 0) :
    ∑' q, (if q.cfg.1.doubleLevel < 2 * n ∧ M ≤ q.resolve then
        iter (doubleDirStop n hn aLo) T q₀ q else 0)
      ≤ w ^ q₀.cfg.1.doubleLevel / (w ^ (2 * n - 1) * η ^ M) := by
  have hrw : ∑' q, (if q.cfg.1.doubleLevel < 2 * n ∧ M ≤ q.resolve then
        iter (doubleDirStop n hn aLo) T q₀ q else 0)
      = ∑' q, (if q.cfg.1.doubleLevel ≤ 2 * n - 1 ∧ M ≤ q.resolve then
        iter (doubleDirStop n hn aLo) T q₀ q else 0) := by
    refine tsum_congr fun q => ?_
    have hiff : (q.cfg.1.doubleLevel < 2 * n ∧ M ≤ q.resolve)
        ↔ (q.cfg.1.doubleLevel ≤ 2 * n - 1 ∧ M ≤ q.resolve) := by
      constructor <;> (rintro ⟨a, b⟩; exact ⟨by omega, b⟩)
    by_cases hc : q.cfg.1.doubleLevel < 2 * n ∧ M ≤ q.resolve
    · rw [if_pos hc, if_pos (hiff.1 hc)]
    · rw [if_neg hc, if_neg (fun h => hc (hiff.2 h))]
  rw [hrw]
  exact doubleDirStop_tail n hn aLo bHi (2 * n - 1) M T haLo hmaj heq w η u hu hrel hwη
    hw1 hw0 hη1 hηt q₀ hr0

/-- **Band productivity, arithmetic core.**  While not at `X`-consensus and with
`x ≥ 1` (the majority band), the productive pair count `xy+xb+yb` is at least
`n−1`, so the productive mass is at least `(n−1)/C(n,2) = 2/n`.  This is the
per-step drift the productivity lower tail consumes; it is *uniform*, hence only
gives `Θ(lg n)` productive draws over an `O(n lg n)` horizon — the phase ladder is
needed to turn it into the `Θ(n)` draws the endgame requires. -/
theorem band_productive_lower (n x y b : ℕ) (hsum : x + y + b = n) (hx1 : 1 ≤ x)
    (hxn : x ≤ n - 1) : n - 1 ≤ x * y + x * b + y * b := by
  have h1n : 1 ≤ n := by omega
  have hyb1 : 1 ≤ y + b := by omega
  zify [h1n]
  have hs : (x:ℤ) + y + b = n := by exact_mod_cast hsum
  have hx1' : (1:ℤ) ≤ x := by exact_mod_cast hx1
  have hyb1' : (1:ℤ) ≤ (y:ℤ) + b := by exact_mod_cast hyb1
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ (x:ℤ) - 1) (by linarith : (0:ℤ) ≤ (y:ℤ) + b - 1),
    mul_nonneg (Int.natCast_nonneg y) (Int.natCast_nonneg b)]

/-- **Inert draws are trace no-ops.**  A pair draw of type `xx`, `yy`, or `bb`
leaves the counted trace entirely unchanged — configuration and both counters.
So the trace only advances on *productive* draws (`xy`, `xb`, `yb`); this is the
basis for treating productivity as a subordinated (draw-counted) process, and
`fuel + resolve` increments by 1 or 2 on each productive draw, by 0 on each inert
draw. -/
theorem nextDoubleTrace_inert {n : ℕ} (q : DoubleTrace n) (k : PairComp)
    (hk : k = .xx ∨ k = .yy ∨ k = .bb) :
    PairComp.nextDoubleTrace q k = q := by
  unfold PairComp.nextDoubleTrace
  by_cases hw : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k = 0
  · rw [dif_pos hw]
  · rw [dif_neg hw]
    have hnext : PairComp.next q.cfg.1 k = q.cfg.1 := by
      rcases hk with h | h | h <;> subst h <;> rfl
    have hf : k.fuelInc = 0 := by rcases hk with h | h | h <;> subst h <;> rfl
    have hr : k.resolveInc = 0 := by rcases hk with h | h | h <;> subst h <;> rfl
    rw [hf, hr, Nat.add_zero, Nat.add_zero]
    congr 1
    exact Subtype.ext hnext

/-- The fuel counter advances by `fuelInc` on a supported label. -/
theorem nextTrace_fuel (n : ℕ) (q : DoubleTrace n) (k : PairComp)
    (hw : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0) :
    (PairComp.nextDoubleTrace q k).fuel = q.fuel + k.fuelInc := by
  rw [PairComp.nextDoubleTrace, dif_neg hw]

/-- **Productive-count one-step expansion** against `w^(fuel+resolve)`.  Inert
draws (`xx`,`yy`,`bb`) keep the counter; `xy`,`xb` add one; `yb` adds two. -/
theorem doubleTraceStep_prod_expect (n : ℕ) (hn : 2 ≤ n) (q : DoubleTrace n) (w : ℝ≥0∞) :
    expect (doubleTraceStep n hn q) (fun q' => w ^ (q'.fuel + q'.resolve))
      = (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
            have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xx
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
            have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .yy
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
            have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .bb)
          * w ^ (q.fuel + q.resolve)
        + (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
            have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xy
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
            have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xb)
          * w ^ (q.fuel + q.resolve + 1)
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
            have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .yb
          * w ^ (q.fuel + q.resolve + 2) := by
  have hh : 2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b := by
    have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega
  have key : ∀ k : PairComp,
      dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh k
        * w ^ ((PairComp.nextDoubleTrace q k).fuel + (PairComp.nextDoubleTrace q k).resolve)
      = dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh k
        * w ^ (q.fuel + q.resolve + (k.fuelInc + k.resolveInc)) := by
    intro k
    by_cases hw : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k = 0
    · rw [dbPairPMF_zero_of_weight_zero hw]; simp
    · rw [nextTrace_fuel n q k hw, nextTrace_resolve n q k hw]; ring_nf
  unfold doubleTraceStep
  rw [expect_map]; unfold expect; rw [tsum_fintype]; simp only []
  rw [show (Finset.univ : Finset PairComp)
      = {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb, PairComp.yb, PairComp.bb} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [key .xx, key .xy, key .yy, key .xb, key .yb, key .bb]
  simp only [PairComp.fuelInc, PairComp.resolveInc]
  ring

/-- Scalar productivity step: `inert + prod·w ≤ p' + p·w` when `inert+prod=1`,
`p+p'=1`, `p ≤ prod`, `w ≤ 1`.  Identity `(p'+pw)−(inert+prod·w)=(prod−p)(1−w)≥0`. -/
theorem prod_scalar (inert prod w p p' : ℝ≥0∞)
    (hmass : inert + prod = 1) (hpp : p + p' = 1) (hp : p ≤ prod) (hw1 : w ≤ 1)
    (hit : inert ≠ ⊤) (hpt : prod ≠ ⊤) (hwt : w ≠ ⊤) (hpT : p ≠ ⊤) (hp't : p' ≠ ⊤) :
    inert + prod * w ≤ p' + p * w := by
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_add hit (by finiteness), ENNReal.toReal_add hp't (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  have hmassR : inert.toReal + prod.toReal = 1 := by
    have := congrArg ENNReal.toReal hmass
    rwa [ENNReal.toReal_add hit hpt, ENNReal.toReal_one] at this
  have hppR : p.toReal + p'.toReal = 1 := by
    have := congrArg ENNReal.toReal hpp
    rwa [ENNReal.toReal_add hpT hp't, ENNReal.toReal_one] at this
  have hpR : p.toReal ≤ prod.toReal := (ENNReal.toReal_le_toReal hpT hpt).mpr hp
  have hwR : w.toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact (ENNReal.toReal_le_toReal hwt (by simp)).mpr hw1
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ prod.toReal - p.toReal)
    (by linarith : (0:ℝ) ≤ 1 - w.toReal)]

/-- The six pair masses sum to `1` (`dbPairPMF` is a PMF over the six compositions). -/
theorem dbPairPMF_sum_six (x y b : ℕ) (h : 2 ≤ x + y + b) :
    dbPairPMF x y b h .xx + dbPairPMF x y b h .yy + dbPairPMF x y b h .bb
      + dbPairPMF x y b h .xy + dbPairPMF x y b h .xb + dbPairPMF x y b h .yb = 1 := by
  have := (dbPairPMF x y b h).tsum_coe
  rw [tsum_fintype, show (Finset.univ : Finset PairComp)
      = {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb, PairComp.yb, PairComp.bb}
        from rfl] at this
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at this
  rw [← this]; ring

/-- **Productivity supermartingale.**  If the productive mass is at least `p`
(`p+p'=1`), then `w^(fuel+resolve)` decays by the factor `p'+p·w ≤ 1` in one step
(`w²≤w` folds the `yb` double-increment down). -/
theorem doubleTrace_prod_super (n : ℕ) (hn : 2 ≤ n) (q : DoubleTrace n) (w p p' : ℝ≥0∞)
    (hw1 : w ≤ 1) (hpp : p + p' = 1) (hwt : w ≠ ⊤) (hpT : p ≠ ⊤) (hp't : p' ≠ ⊤)
    (hprod : p ≤ (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
        have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xy
      + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
        have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xb
      + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
        have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .yb)) :
    expect (doubleTraceStep n hn q) (fun q' => w ^ (q'.fuel + q'.resolve))
      ≤ (p' + p * w) * w ^ (q.fuel + q.resolve) := by
  have hh : 2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b := by
    have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega
  set c := q.fuel + q.resolve
  set xx := dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh .xx
  set yy := dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh .yy
  set bb := dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh .bb
  set xy := dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh .xy
  set xb := dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh .xb
  set yb := dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh .yb
  have hfin : ∀ k, dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh k ≠ ⊤ :=
    fun k => PMF.apply_ne_top _ _
  have hit : xx + yy + bb ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩, hfin _⟩
  have hpt : xy + xb + yb ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩, hfin _⟩
  rw [doubleTraceStep_prod_expect n hn q w]
  have hmass : (xx + yy + bb) + (xy + xb + yb) = 1 := by
    have := dbPairPMF_sum_six q.cfg.1.x q.cfg.1.y q.cfg.1.b hh; rw [← this]; ring
  have hyb : yb * w ^ (c + 2) ≤ yb * w ^ (c + 1) :=
    mul_le_mul_left' (pow_le_pow_right_of_le_one' hw1 (by omega : c + 1 ≤ c + 2)) yb
  calc (xx + yy + bb) * w ^ c + (xy + xb) * w ^ (c + 1) + yb * w ^ (c + 2)
      ≤ (xx + yy + bb) * w ^ c + (xy + xb) * w ^ (c + 1) + yb * w ^ (c + 1) :=
        add_le_add (le_refl _) hyb
    _ = ((xx + yy + bb) + (xy + xb + yb) * w) * w ^ c := by rw [pow_succ]; ring
    _ ≤ (p' + p * w) * w ^ c :=
        mul_le_mul_right' (prod_scalar (xx + yy + bb) (xy + xb + yb) w p p' hmass hpp hprod hw1
          hit hpt hwt hpT hp't) (w ^ c)

/-- **Count lower tail with a frozen success set.**  With the vanishing-on-`B`
potential `V = if B then 0 else w^count` a uniform `φ`-supermartingale (it is `0`
at frozen success states, so contraction holds there trivially), the mass that
after `T` steps has a low count AND has not yet succeeded is at most
`φ^T · V(s₀) / w^m`. -/
theorem count_tail_frozen (K : α → PMF α) (B : α → Prop) [DecidablePred B] (count : α → ℕ)
    (w φ : ℝ≥0∞) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hstep : ∀ s, expect (freeze B K s) (fun z => if B z then 0 else w ^ count z)
        ≤ φ * (if B s then 0 else w ^ count s))
    (T m : ℕ) (s₀ : α) :
    ∑' z, (if count z ≤ m ∧ ¬ B z then iter (freeze B K) T s₀ z else 0)
      ≤ φ ^ T * (if B s₀ then 0 else w ^ count s₀) / w ^ m := by
  have hwtop : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  set V : α → ℝ≥0∞ := fun z => if B z then 0 else w ^ count z with hV
  set θ : ℝ≥0∞ := w ^ m with hθ
  have hθ0 : θ ≠ 0 := pow_ne_zero _ hw0
  have hθt : θ ≠ ⊤ := ENNReal.pow_ne_top hwtop
  have hsub : ∀ z, (if count z ≤ m ∧ ¬ B z then iter (freeze B K) T s₀ z else 0)
      ≤ (if θ ≤ V z then iter (freeze B K) T s₀ z else 0) := by
    intro z
    by_cases hz : count z ≤ m ∧ ¬ B z
    · have hle : θ ≤ V z := by
        rw [hV]; simp only [hz.2, if_false, hθ]
        exact pow_le_pow_right_of_le_one' hw1 hz.1
      simp [hz, hle]
    · simp [hz]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans (markov_div (iter (freeze B K) T s₀) V θ hθ0 hθt) ?_
  exact ENNReal.div_le_div_right (expect_iter_le (freeze B K) V φ hstep T s₀) θ

/-- **Productivity V-supermartingale.**  Freeze at any set `B` containing all
low-productivity states; then `V = if B then 0 else w^(fuel+resolve)` is a uniform
`(p'+p·w)`-supermartingale (off `B` productivity `≥ p`; on `B` the potential is `0`). -/
theorem prod_V_super (n : ℕ) (hn : 2 ≤ n) (B : DoubleTrace n → Prop) [DecidablePred B]
    (w p p' : ℝ≥0∞) (hw1 : w ≤ 1) (hpp : p + p' = 1) (hwt : w ≠ ⊤) (hpT : p ≠ ⊤) (hp't : p' ≠ ⊤)
    (hBprod : ∀ q : DoubleTrace n, ¬ B q →
      p ≤ (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xy
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xb
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .yb)) :
    ∀ q : DoubleTrace n,
      expect (freeze B (doubleTraceStep n hn) q)
          (fun z => if B z then 0 else w ^ (z.fuel + z.resolve))
        ≤ (p' + p * w) * (if B q then 0 else w ^ (q.fuel + q.resolve)) := by
  intro q
  by_cases hB : B q
  · rw [freeze_of_mem q hB, expect_pure]
    simp [hB]
  · rw [freeze_of_not_mem q hB, if_neg hB]
    calc expect (doubleTraceStep n hn q) (fun z => if B z then 0 else w ^ (z.fuel + z.resolve))
        ≤ expect (doubleTraceStep n hn q) (fun z => w ^ (z.fuel + z.resolve)) := by
          unfold expect
          refine ENNReal.tsum_le_tsum fun z => mul_le_mul_left' ?_ _
          by_cases hBz : B z <;> simp [hBz]
      _ ≤ (p' + p * w) * w ^ (q.fuel + q.resolve) :=
          doubleTrace_prod_super n hn q w p p' hw1 hpp hwt hpT hp't (hBprod q hB)

/-- **Productivity lower tail (one region).**  On the chain frozen at `B` (which
contains the success/low-productivity states), the mass that after `T` steps has a
low productive count (`fuel+resolve ≤ m`) and has not yet been frozen is at most
`(p'+p·w)^T · V(q₀) / w^m` — exponentially small when the productivity floor `p>0`
lets `w` be chosen with `p'+p·w < 1`. -/
theorem productivity_tail (n : ℕ) (hn : 2 ≤ n) (B : DoubleTrace n → Prop) [DecidablePred B]
    (w p p' : ℝ≥0∞) (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hpp : p + p' = 1)
    (hwt : w ≠ ⊤) (hpT : p ≠ ⊤) (hp't : p' ≠ ⊤)
    (hBprod : ∀ q : DoubleTrace n, ¬ B q →
      p ≤ (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xy
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xb
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .yb))
    (T m : ℕ) (q₀ : DoubleTrace n) :
    ∑' q, (if q.fuel + q.resolve ≤ m ∧ ¬ B q then
        iter (freeze B (doubleTraceStep n hn)) T q₀ q else 0)
      ≤ (p' + p * w) ^ T * (if B q₀ then 0 else w ^ (q₀.fuel + q₀.resolve)) / w ^ m :=
  count_tail_frozen (doubleTraceStep n hn) B (fun q => q.fuel + q.resolve) w (p' + p * w)
    hw1 hw0 (prod_V_super n hn B w p p' hw1 hpp hwt hpT hp't hBprod) T m q₀

/-- **Level-dependent productivity floor (count form).**  The productive pair count
is at least `x·(n−x)` — quadratic in the majority `x`, hence `Ω(n²)` far from
consensus and shrinking to `Θ(n)` near it.  This is the per-phase productivity that
turns `Θ(n)` resolutions in `O(n·lg n)` time into a summable (harmonic) ladder. -/
theorem productive_count_lower (n x y b : ℕ) (hsum : x + y + b = n) :
    x * (n - x) ≤ x * y + x * b + y * b := by
  have hyb : y + b = n - x := by omega
  calc x * (n - x) = x * (y + b) := by rw [hyb]
    _ = x * y + x * b := by ring
    _ ≤ x * y + x * b + y * b := Nat.le_add_right _ _

/-- The productive mass is at least `x·(n−x) / C(n,2)`. -/
theorem productive_mass_lower (n : ℕ) (hn : 2 ≤ n) (s : DoubleState n) :
    ((s.1.x * (n - s.1.x) : ℕ) : ℝ≥0∞) / (Nat.choose n 2 : ℝ≥0∞)
      ≤ dbPairPMF s.1.x s.1.y s.1.b (by
          have := s.2; simp only [BiCfg.DoubleInv] at this; omega) .xy
        + dbPairPMF s.1.x s.1.y s.1.b (by
          have := s.2; simp only [BiCfg.DoubleInv] at this; omega) .xb
        + dbPairPMF s.1.x s.1.y s.1.b (by
          have := s.2; simp only [BiCfg.DoubleInv] at this; omega) .yb := by
  have hpop : s.1.x + s.1.y + s.1.b = n := s.2
  have hh : 2 ≤ s.1.x + s.1.y + s.1.b := by omega
  have hxy : dbPairPMF s.1.x s.1.y s.1.b hh .xy
      = ((s.1.x * s.1.y : ℕ) : ℝ≥0∞) / (Nat.choose n 2 : ℝ≥0∞) := by
    rw [show dbPairPMF s.1.x s.1.y s.1.b hh PairComp.xy
        = ((PairComp.weight s.1.x s.1.y s.1.b PairComp.xy : ℕ):ℝ≥0∞)
          /(Nat.choose (s.1.x+s.1.y+s.1.b) 2:ℝ≥0∞) from rfl, hpop]; simp [PairComp.weight]
  have hxb : dbPairPMF s.1.x s.1.y s.1.b hh .xb
      = ((s.1.x * s.1.b : ℕ) : ℝ≥0∞) / (Nat.choose n 2 : ℝ≥0∞) := by
    rw [show dbPairPMF s.1.x s.1.y s.1.b hh PairComp.xb
        = ((PairComp.weight s.1.x s.1.y s.1.b PairComp.xb : ℕ):ℝ≥0∞)
          /(Nat.choose (s.1.x+s.1.y+s.1.b) 2:ℝ≥0∞) from rfl, hpop]; simp [PairComp.weight]
  have hyb : dbPairPMF s.1.x s.1.y s.1.b hh .yb
      = ((s.1.y * s.1.b : ℕ) : ℝ≥0∞) / (Nat.choose n 2 : ℝ≥0∞) := by
    rw [show dbPairPMF s.1.x s.1.y s.1.b hh PairComp.yb
        = ((PairComp.weight s.1.x s.1.y s.1.b PairComp.yb : ℕ):ℝ≥0∞)
          /(Nat.choose (s.1.x+s.1.y+s.1.b) 2:ℝ≥0∞) from rfl, hpop]; simp [PairComp.weight]
  rw [hxy, hxb, hyb, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  apply ENNReal.div_le_div_right
  rw [← Nat.cast_add, ← Nat.cast_add]
  exact_mod_cast productive_count_lower n s.1.x s.1.y s.1.b hpop

/-- **Consensus is absorbing.**  At `X`-consensus every draw fixes the trace
(inert `xx`, or zero-weight `xy`/`xb`/`yb`), so the counted step is the identity.
Hence `doubleDirStop` (frozen only at `level ≤ aLo`) also freezes at consensus for
free — the trace and productivity estimates on it inherit consensus absorption. -/
theorem doubleTraceStep_consensus (n : ℕ) (hn : 2 ≤ n) (q : DoubleTrace n)
    (hc : q.cfg.1.x = n ∧ q.cfg.1.y = 0 ∧ q.cfg.1.b = 0) :
    doubleTraceStep n hn q = PMF.pure q := by
  obtain ⟨hx, hy, hb⟩ := hc
  have hconst : ∀ k, PairComp.nextDoubleTrace q k = q := by
    intro k
    cases k
    · exact nextDoubleTrace_inert q .xx (Or.inl rfl)
    · rw [PairComp.nextDoubleTrace, dif_pos (by simp [PairComp.weight, hy])]
    · exact nextDoubleTrace_inert q .yy (Or.inr (Or.inl rfl))
    · rw [PairComp.nextDoubleTrace, dif_pos (by simp [PairComp.weight, hb])]
    · rw [PairComp.nextDoubleTrace, dif_pos (by simp [PairComp.weight, hb])]
    · exact nextDoubleTrace_inert q .bb (Or.inr (Or.inr rfl))
  unfold doubleTraceStep
  rw [show (PairComp.nextDoubleTrace q) = (fun _ => q) from funext hconst]
  ext z
  rw [PMF.map_apply, PMF.pure_apply]
  by_cases hz : z = q
  · subst hz; simp only [eq_self_iff_true, if_true]; exact PMF.tsum_coe _
  · simp only [if_neg hz, tsum_zero, if_neg (Ne.symm hz)]

/-- One step of `doubleDirStop` preserves the fuel invariant on its support. -/
theorem doubleDirStop_step_fuelInv {n y₀ : ℕ} (hn : 2 ≤ n) (aLo : ℕ) (a : DoubleTrace n)
    (ha : a.FuelInv y₀) (z : DoubleTrace n) (haz : doubleDirStop n hn aLo a z ≠ 0) :
    z.FuelInv y₀ := by
  unfold doubleDirStop at haz
  split_ifs at haz with hlive
  · exact doubleTraceStep_fuelInv_of_apply_ne_zero hn a ha z haz
  · rw [PMF.pure_apply] at haz
    by_cases hz : z = a
    · rw [hz]; exact ha
    · simp [hz] at haz

/-- The fuel invariant holds along the whole frozen direction chain. -/
theorem doubleDirStop_iter_fuelInv {n y₀ T : ℕ} (hn : 2 ≤ n) (aLo : ℕ) (q z : DoubleTrace n)
    (hq : q.FuelInv y₀) (hz : iter (doubleDirStop n hn aLo) T q z ≠ 0) :
    z.FuelInv y₀ :=
  iter_support_closed (doubleDirStop n hn aLo) (DoubleTrace.FuelInv y₀)
    (fun a ha z haz => doubleDirStop_step_fuelInv hn aLo a ha z haz) T q z hq hz

/-- Since consensus is auto-absorbing, `doubleDirStop` (frozen at `level ≤ aLo`)
equals the chain frozen at `level ≤ aLo ∨ consensus` — the set on whose complement
(`aLo < level < 2n`) the productivity floor holds, so `productivity_tail` applies to
the direction chain with no rework. -/
theorem doubleDirStop_eq_freeze_unified (n : ℕ) (hn : 2 ≤ n) (aLo : ℕ) (haLo : aLo < 2 * n) :
    doubleDirStop n hn aLo
      = freeze (fun q : DoubleTrace n => q.cfg.1.doubleLevel ≤ aLo ∨ BiXConsensus n q.cfg.1)
          (doubleTraceStep n hn) := by
  funext q
  have hlv2n : BiXConsensus n q.cfg.1 → q.cfg.1.doubleLevel = 2 * n := by
    intro hc; exact (doubleLevel_eq_top_iff q.cfg).2 ⟨hc.1, hc.2.1, hc.2.2⟩
  unfold doubleDirStop freeze
  by_cases h1 : q.cfg.1.doubleLevel ≤ aLo
  · rw [if_neg (by omega), if_pos (Or.inl h1)]
  · by_cases hc : BiXConsensus n q.cfg.1
    · rw [if_pos (by have := hlv2n hc; omega), if_pos (Or.inr hc)]
      exact doubleTraceStep_consensus n hn q ⟨hc.1, hc.2.1, hc.2.2⟩
    · rw [if_pos (by omega), if_neg (not_or.mpr ⟨h1, hc⟩)]

/-- **Productivity term bound.**  Combines the frozen `fuelInv` (few resolutions ⟹
low productive count on the support) with `productivity_tail`.  From a fresh trace
`⟨s₀,0,0⟩`, the band mass with `< M` resolutions is bounded by the productivity
Chernoff tail at count threshold `s₀.y + 3M`.  The floor `p` is supplied per phase. -/
theorem productivity_term_le (n : ℕ) (hn : 2 ≤ n) (aLo : ℕ) (haLo : aLo < 2 * n)
    (w p p' : ℝ≥0∞) (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hpp : p + p' = 1)
    (hwt : w ≠ ⊤) (hpT : p ≠ ⊤) (hp't : p' ≠ ⊤)
    (hBprod : ∀ q : DoubleTrace n,
      ¬ (q.cfg.1.doubleLevel ≤ aLo ∨ BiXConsensus n q.cfg.1) →
      p ≤ (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xy
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xb
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .yb))
    (M T : ℕ) (s₀ : DoubleState n) :
    ∑' q, (if aLo + 1 ≤ q.cfg.1.doubleLevel ∧ q.cfg.1.doubleLevel < 2 * n ∧ q.resolve < M then
        iter (doubleDirStop n hn aLo) T (⟨s₀, 0, 0⟩ : DoubleTrace n) q else 0)
      ≤ (p' + p * w) ^ T * 1 / w ^ (s₀.1.y + 3 * M) := by
  set B : DoubleTrace n → Prop :=
    fun q => q.cfg.1.doubleLevel ≤ aLo ∨ BiXConsensus n q.cfg.1 with hBdef
  set q₀ : DoubleTrace n := ⟨s₀, 0, 0⟩ with hq0
  have hfuel0 : q₀.FuelInv s₀.1.y := DoubleTrace.initial_fuelInv s₀ (le_refl _)
  have hsub : ∀ q,
      (if aLo + 1 ≤ q.cfg.1.doubleLevel ∧ q.cfg.1.doubleLevel < 2 * n ∧ q.resolve < M then
        iter (doubleDirStop n hn aLo) T q₀ q else 0)
      ≤ (if q.fuel + q.resolve ≤ s₀.1.y + 3 * M ∧ ¬ B q then
        iter (doubleDirStop n hn aLo) T q₀ q else 0) := by
    intro q
    by_cases hq : aLo + 1 ≤ q.cfg.1.doubleLevel ∧ q.cfg.1.doubleLevel < 2 * n ∧ q.resolve < M
    · rw [if_pos hq]
      by_cases hz : iter (doubleDirStop n hn aLo) T q₀ q = 0
      · rw [hz]; simp
      · have hfi : q.FuelInv s₀.1.y := doubleDirStop_iter_fuelInv hn aLo q₀ q hfuel0 hz
        have hnB : ¬ B q := by
          rw [hBdef, not_or]
          exact ⟨by omega, (noncons_iff_level q.cfg).2 hq.2.1⟩
        rw [if_pos]
        refine ⟨?_, hnB⟩
        simp only [DoubleTrace.FuelInv] at hfi
        omega
    · rw [if_neg hq]; positivity
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  rw [doubleDirStop_eq_freeze_unified n hn aLo haLo]
  refine le_trans
    (productivity_tail n hn B w p p' hw1 hw0 hpp hwt hpT hp't hBprod T (s₀.1.y + 3 * M) q₀) ?_
  gcongr
  rw [hq0]
  split_ifs <;> simp

/-- **The complete non-consensus failure bound.**  Assembling `nonconsensus_mass_eq_trace`,
`trace_noncons_split`, and the three term bounds: the physical Double-B non-consensus
mass after `T` steps is at most a ruin term `(bHiᵣ/aLo)^k`, a direction (Chernoff-in-
resolutions) term `w^{L₀}/(w^{2n-1}·η^M)`, and a productivity (Chernoff-in-draws) term
`(pp'+pp·wp)^T/wp^{y₀+3M}`.  This reduces `theorem2` to instantiating the constants,
discharging the productivity floor `pp` (per phase, via `productive_mass_lower`), and
the scalar arithmetic bounding the three terms by `(n⁻¹)^{c·γ}`. -/
theorem noncons_mass_bound (n : ℕ) (hn : 2 ≤ n) (aLo bHiR bHiD k M T : ℕ)
    (haLoLt : aLo < 2 * n)
    (hpop2n : aLo + bHiR + 2 = 2 * n) (haLo0 : 0 < aLo) (hbHiR0 : 0 < bHiR) (hmajR : bHiR ≤ aLo)
    (heqD : aLo + bHiD = 2 * n) (hmajD : bHiD ≤ aLo)
    (w η u : ℝ≥0∞) (hu : u = (bHiD : ℝ≥0∞) / (aLo : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (wp pp pp' : ℝ≥0∞) (hwp1 : wp ≤ 1) (hwp0 : wp ≠ 0) (hppp : pp + pp' = 1)
    (hwpt : wp ≠ ⊤) (hppT : pp ≠ ⊤) (hpp't : pp' ≠ ⊤)
    (hBprod : ∀ q : DoubleTrace n,
      ¬ (q.cfg.1.doubleLevel ≤ aLo ∨ BiXConsensus n q.cfg.1) →
      pp ≤ (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xy
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xb
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .yb))
    (s₀ : DoubleState n) (hstart : s₀.1.doubleLevel = aLo + k) :
    ∑' z : BiCfg, (if BiXConsensus n z then 0 else iter doubleBChain T s₀.1 z)
      ≤ ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k
        + w ^ s₀.1.doubleLevel / (w ^ (2 * n - 1) * η ^ M)
        + (pp' + pp * wp) ^ T * 1 / wp ^ (s₀.1.y + 3 * M) := by
  set q₀ : DoubleTrace n := ⟨s₀, 0, 0⟩ with hq0
  have heq1 : (∑' z : BiCfg, if BiXConsensus n z then 0 else iter doubleBChain T s₀.1 z)
      = ∑' q : DoubleTrace n, if BiXConsensus n q.cfg.1 then 0
          else iter (doubleTraceStep n hn) T q₀ q := by
    have := nonconsensus_mass_eq_trace n hn T q₀
    simpa [hq0] using this
  rw [heq1]
  refine le_trans (trace_noncons_split n hn aLo M T haLoLt q₀) ?_
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact ruin_term_le n hn aLo bHiR k T hpop2n haLo0 hbHiR0 hmajR q₀ (by simpa [hq0] using hstart)
  · have := direction_term_le n hn aLo bHiD M T haLo0 hmajD heqD w η u hu hrel hwη
      hw1 hw0 hη1 hηt q₀ (by simp [hq0])
    simpa [hq0] using this
  · have := productivity_term_le n hn aLo haLoLt wp pp pp' hwp1 hwp0 hppp hwpt hppT hpp't
      hBprod M T s₀
    simpa [hq0] using this

/-- The band-frozen direction chain: run the trace while `aLo < level < hi`, freeze
outside.  For a single phase `[aLo, hi]` (`hi ≤ 2n`) both boundaries are absorbing —
the chain the per-phase direction and productivity floors act on. -/
noncomputable def doubleBandStop (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ) (q : DoubleTrace n) :
    PMF (DoubleTrace n) :=
  if aLo + 1 ≤ q.cfg.1.doubleLevel ∧ q.cfg.1.doubleLevel + 1 ≤ hi then
    doubleTraceStep n hn q else PMF.pure q

theorem doubleBandStop_eq_freeze (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ) :
    doubleBandStop n hn aLo hi
      = freeze (fun q : DoubleTrace n => q.cfg.1.doubleLevel ≤ aLo ∨ hi ≤ q.cfg.1.doubleLevel)
          (doubleTraceStep n hn) := by
  funext q
  unfold doubleBandStop freeze
  by_cases h : q.cfg.1.doubleLevel ≤ aLo ∨ hi ≤ q.cfg.1.doubleLevel
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg h]

/-- **Uniform direction supermartingale on the band chain.**  `Θ` does not increase
at any state — drift where `aLo < level < hi` (majority holds since `level > aLo`),
equality when frozen at either boundary. -/
theorem doubleBandStop_super (n : ℕ) (hn : 2 ≤ n) (aLo bHi hi : ℕ)
    (haLo : 0 < aLo) (hmaj : bHi ≤ aLo) (heq : aLo + bHi = 2 * n) (hhi : hi ≤ 2 * n)
    (w η u : ℝ≥0∞) (hu : u = (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hwt : w ≠ ⊤) (hηt : η ≠ ⊤) :
    ∀ q, expect (doubleBandStop n hn aLo hi q) (doubleTheta w η) ≤ 1 * doubleTheta w η q := by
  intro q
  rw [one_mul]
  unfold doubleBandStop
  split_ifs with hlive
  · obtain ⟨a, ha⟩ : ∃ a, q.cfg.1.doubleLevel = a + 1 :=
      ⟨q.cfg.1.doubleLevel - 1, by omega⟩
    have hcolev : q.cfg.1.doubleCoLevel - 1 ≤ bHi := by
      have hadd := doubleLevel_add_doubleCoLevel q.cfg; omega
    have hlo : aLo ≤ q.cfg.1.doubleLevel - 1 := by omega
    have hdle : doubleResolveDown q.cfg ≤ doubleResolveUp q.cfg * u := by
      rw [hu]; exact doubleResolve_down_le n aLo bHi hn q.cfg haLo hlo hcolev hmaj
    have hsum := double_mass_sum n hn q.cfg
    have hCpos : 0 < Nat.choose n 2 := Nat.choose_pos hn
    have hdt : doubleResolveDown q.cfg ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hCpos.ne')
    have hut : doubleResolveUp q.cfg ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hCpos.ne')
    have hnt : doubleNeutralMass hn q.cfg ≠ ⊤ := by
      intro h; rw [h] at hsum; simp at hsum
    have huT : u ≠ ⊤ := by
      rw [hu]; exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
        (by simp only [ne_eq, Nat.cast_eq_zero]; omega)
    exact traceStep_theta_super n hn q a ha w η u hdle hsum hrel hwη hdt hnt hut hwt hηt huT
  · rw [expect_pure]

/-- **Band direction tail.**  On the band chain, the mass that after `T` steps has
level `≤ thr` and `≥ M` resolutions is `≤ w^{L₀}/(w^{thr}·η^M)`. -/
theorem doubleBandStop_tail (n : ℕ) (hn : 2 ≤ n) (aLo bHi hi thr M T : ℕ)
    (haLo : 0 < aLo) (hmaj : bHi ≤ aLo) (heq : aLo + bHi = 2 * n) (hhi : hi ≤ 2 * n)
    (w η u : ℝ≥0∞) (hu : u = (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (q₀ : DoubleTrace n) (hr0 : q₀.resolve = 0) :
    ∑' q, (if q.cfg.1.doubleLevel ≤ thr ∧ M ≤ q.resolve then
        iter (doubleBandStop n hn aLo hi) T q₀ q else 0)
      ≤ w ^ q₀.cfg.1.doubleLevel / (w ^ thr * η ^ M) := by
  have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  set θ : ℝ≥0∞ := w ^ thr * η ^ M with hθdef
  have hθ0 : θ ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ hw0)
    exact pow_ne_zero _ (by rintro rfl; simp at hη1)
  have hθtop : θ ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top hwt) (ENNReal.pow_ne_top hηt)
  have hsub : ∀ q,
      (if q.cfg.1.doubleLevel ≤ thr ∧ M ≤ q.resolve then
        iter (doubleBandStop n hn aLo hi) T q₀ q else 0)
      ≤ (if θ ≤ doubleTheta w η q then iter (doubleBandStop n hn aLo hi) T q₀ q else 0) := by
    intro q
    by_cases hq : q.cfg.1.doubleLevel ≤ thr ∧ M ≤ q.resolve
    · have hle : θ ≤ doubleTheta w η q := by
        rw [hθdef, doubleTheta]
        exact mul_le_mul' (pow_le_pow_right_of_le_one' hw1 hq.1) (pow_le_pow_right₀ hη1 hq.2)
      simp [hq, hle]
    · simp [hq]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans (markov_div (iter (doubleBandStop n hn aLo hi) T q₀)
    (doubleTheta w η) θ hθ0 hθtop) ?_
  have hiter := expect_iter_le (doubleBandStop n hn aLo hi) (doubleTheta w η) 1
    (doubleBandStop_super n hn aLo bHi hi haLo hmaj heq hhi w η u hu hrel hwη hwt hηt) T q₀
  have hΘ0 : doubleTheta w η q₀ = w ^ q₀.cfg.1.doubleLevel := by
    simp [doubleTheta, hr0]
  rw [one_pow, one_mul, hΘ0] at hiter
  exact ENNReal.div_le_div_right hiter θ

/-- **Level-based productive floor (count form).**  Since `x−y = level−n` and
`2x ≤ level`, the productive pair count satisfies
`(level−n)·(2n−level) ≤ 2·(xy+xb+yb)`.  This is `Ω((level−n)(2n−level))` — the phase
floor: `Ω(n·coLevel)` near consensus, giving the harmonic `O(n·lg n)` endgame. -/
theorem productive_count_level_floor (n x y b : ℕ) (hsum : x + y + b = n) :
    (2 * x + b - n) * (2 * n - (2 * x + b)) ≤ 2 * (x * y + x * b + y * b) := by
  have hstep : (2 * x + b - n) * (2 * n - (2 * x + b)) ≤ 2 * x * (n - x) := by
    have h1 : 2 * x + b - n ≤ x := by omega
    have h2 : 2 * n - (2 * x + b) ≤ 2 * (n - x) := by omega
    calc (2 * x + b - n) * (2 * n - (2 * x + b)) ≤ x * (2 * (n - x)) := Nat.mul_le_mul h1 h2
      _ = 2 * x * (n - x) := by ring
  have hprod := productive_count_lower n x y b hsum
  nlinarith [hstep, hprod]

/-- Productive mass equals `(xy+xb+yb)/C(n,2)`. -/
theorem dbProductive_mass_eq (n : ℕ) (hn : 2 ≤ n) (s : DoubleState n) :
    dbPairPMF s.1.x s.1.y s.1.b (by
        have := s.2; simp only [BiCfg.DoubleInv] at this; omega) .xy
      + dbPairPMF s.1.x s.1.y s.1.b (by
        have := s.2; simp only [BiCfg.DoubleInv] at this; omega) .xb
      + dbPairPMF s.1.x s.1.y s.1.b (by
        have := s.2; simp only [BiCfg.DoubleInv] at this; omega) .yb
      = ((s.1.x * s.1.y + s.1.x * s.1.b + s.1.y * s.1.b : ℕ) : ℝ≥0∞) / (Nat.choose n 2 : ℝ≥0∞) := by
  have hpop : s.1.x + s.1.y + s.1.b = n := s.2
  have hh : 2 ≤ s.1.x + s.1.y + s.1.b := by omega
  have hval : ∀ k, dbPairPMF s.1.x s.1.y s.1.b hh k
      = ((PairComp.weight s.1.x s.1.y s.1.b k : ℕ) : ℝ≥0∞) / (Nat.choose n 2 : ℝ≥0∞) := by
    intro k
    rw [show dbPairPMF s.1.x s.1.y s.1.b hh k
        = ((PairComp.weight s.1.x s.1.y s.1.b k : ℕ):ℝ≥0∞)
          /(Nat.choose (s.1.x+s.1.y+s.1.b) 2:ℝ≥0∞) from rfl, hpop]
  rw [hval, hval, hval, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  congr 1
  rw [← Nat.cast_add, ← Nat.cast_add]
  simp [PairComp.weight]

/-- **Level-based productive mass floor.**  `(level−n)(2n−level)/(2·C(n,2)) ≤` the
productive mass — the per-phase floor `pp` in `ℝ≥0∞` (`Ω(coLevel/n)` near consensus). -/
theorem productive_mass_level_floor (n : ℕ) (hn : 2 ≤ n) (s : DoubleState n) :
    ((s.1.doubleLevel - n) * (2 * n - s.1.doubleLevel) : ℕ) / (2 * Nat.choose n 2 : ℝ≥0∞)
      ≤ dbPairPMF s.1.x s.1.y s.1.b (by
          have := s.2; simp only [BiCfg.DoubleInv] at this; omega) .xy
        + dbPairPMF s.1.x s.1.y s.1.b (by
          have := s.2; simp only [BiCfg.DoubleInv] at this; omega) .xb
        + dbPairPMF s.1.x s.1.y s.1.b (by
          have := s.2; simp only [BiCfg.DoubleInv] at this; omega) .yb := by
  have hpop : s.1.x + s.1.y + s.1.b = n := s.2
  have hlv : s.1.doubleLevel = 2 * s.1.x + s.1.b := rfl
  rw [dbProductive_mass_eq n hn s, hlv]
  have hfloor := productive_count_level_floor n s.1.x s.1.y s.1.b hpop
  calc ((2 * s.1.x + s.1.b - n) * (2 * n - (2 * s.1.x + s.1.b)) : ℕ)
        / (2 * Nat.choose n 2 : ℝ≥0∞)
      ≤ ((2 * (s.1.x * s.1.y + s.1.x * s.1.b + s.1.y * s.1.b) : ℕ) : ℝ≥0∞)
        / (2 * Nat.choose n 2 : ℝ≥0∞) :=
        ENNReal.div_le_div_right (by exact_mod_cast hfloor) _
    _ = ((s.1.x * s.1.y + s.1.x * s.1.b + s.1.y * s.1.b : ℕ) : ℝ≥0∞) / (Nat.choose n 2 : ℝ≥0∞) := by
        push_cast
        rw [ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

/-- Any chain `freeze B doubleTraceStep` preserves the fuel invariant on its support. -/
theorem freezeTrace_iter_fuelInv {n y₀ T : ℕ} (hn : 2 ≤ n)
    (B : DoubleTrace n → Prop) [DecidablePred B] (q z : DoubleTrace n)
    (hq : q.FuelInv y₀) (hz : iter (freeze B (doubleTraceStep n hn)) T q z ≠ 0) :
    z.FuelInv y₀ := by
  refine iter_support_closed (freeze B (doubleTraceStep n hn)) (DoubleTrace.FuelInv y₀)
    (fun a ha z haz => ?_) T q z hq hz
  unfold freeze at haz
  split_ifs at haz with hB
  · rw [PMF.pure_apply] at haz
    by_cases hz2 : z = a
    · rw [hz2]; exact ha
    · simp [hz2] at haz
  · exact doubleTraceStep_fuelInv_of_apply_ne_zero hn a ha z haz

/-- **Band productivity term bound.**  On the band chain, the mass with `aLo < level
< hi` and `< M` resolutions is bounded by the productivity Chernoff tail at count
threshold `s₀.y + 3M`, with per-phase floor `pp`. -/
theorem band_productivity_term_le (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ)
    (wp pp pp' : ℝ≥0∞) (hwp1 : wp ≤ 1) (hwp0 : wp ≠ 0) (hppp : pp + pp' = 1)
    (hwpt : wp ≠ ⊤) (hppT : pp ≠ ⊤) (hpp't : pp' ≠ ⊤)
    (hBprod : ∀ q : DoubleTrace n,
      ¬ (q.cfg.1.doubleLevel ≤ aLo ∨ hi ≤ q.cfg.1.doubleLevel) →
      pp ≤ (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xy
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xb
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .yb))
    (M T : ℕ) (s₀ : DoubleState n) :
    ∑' q, (if aLo + 1 ≤ q.cfg.1.doubleLevel ∧ q.cfg.1.doubleLevel + 1 ≤ hi ∧ q.resolve < M then
        iter (doubleBandStop n hn aLo hi) T (⟨s₀, 0, 0⟩ : DoubleTrace n) q else 0)
      ≤ (pp' + pp * wp) ^ T * 1 / wp ^ (s₀.1.y + 3 * M) := by
  set B : DoubleTrace n → Prop :=
    fun q => q.cfg.1.doubleLevel ≤ aLo ∨ hi ≤ q.cfg.1.doubleLevel with hBdef
  set q₀ : DoubleTrace n := ⟨s₀, 0, 0⟩ with hq0
  have hfuel0 : q₀.FuelInv s₀.1.y := DoubleTrace.initial_fuelInv s₀ (le_refl _)
  have hsub : ∀ q,
      (if aLo + 1 ≤ q.cfg.1.doubleLevel ∧ q.cfg.1.doubleLevel + 1 ≤ hi ∧ q.resolve < M then
        iter (doubleBandStop n hn aLo hi) T q₀ q else 0)
      ≤ (if q.fuel + q.resolve ≤ s₀.1.y + 3 * M ∧ ¬ B q then
        iter (doubleBandStop n hn aLo hi) T q₀ q else 0) := by
    intro q
    by_cases hq : aLo + 1 ≤ q.cfg.1.doubleLevel ∧ q.cfg.1.doubleLevel + 1 ≤ hi ∧ q.resolve < M
    · rw [if_pos hq]
      by_cases hz : iter (doubleBandStop n hn aLo hi) T q₀ q = 0
      · rw [hz]; simp
      · have hfi : q.FuelInv s₀.1.y := by
          have hzf : iter (freeze B (doubleTraceStep n hn)) T q₀ q ≠ 0 := by
            rwa [← doubleBandStop_eq_freeze n hn aLo hi]
          exact freezeTrace_iter_fuelInv hn B q₀ q hfuel0 hzf
        have hnB : ¬ B q := by rw [hBdef, not_or]; exact ⟨by omega, by omega⟩
        rw [if_pos]
        refine ⟨?_, hnB⟩
        simp only [DoubleTrace.FuelInv] at hfi
        omega
    · rw [if_neg hq]; positivity
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  rw [doubleBandStop_eq_freeze n hn aLo hi]
  refine le_trans
    (productivity_tail n hn B wp pp pp' hwp1 hwp0 hppp hwpt hppT hpp't hBprod T
      (s₀.1.y + 3 * M) q₀) ?_
  gcongr
  rw [hq0]
  split_ifs <;> simp

/-- **Per-phase set-cover split.**  On the band chain, the "not yet reached `hi`" mass
is covered by the ruin mass (`level ≤ aLo`), the many-resolutions band mass
(`level ≤ hi-1 ∧ M≤resolve`), and the few-resolutions band mass
(`aLo<level<hi ∧ resolve<M`). -/
theorem band_split (n : ℕ) (hn : 2 ≤ n) (aLo hi M T : ℕ) (q₀ : DoubleTrace n) :
    ∑' q, (if q.cfg.1.doubleLevel + 1 ≤ hi then
        iter (doubleBandStop n hn aLo hi) T q₀ q else 0)
      ≤ (∑' q, (if q.cfg.1.doubleLevel ≤ aLo then
            iter (doubleBandStop n hn aLo hi) T q₀ q else 0))
        + (∑' q, (if q.cfg.1.doubleLevel ≤ hi - 1 ∧ M ≤ q.resolve then
            iter (doubleBandStop n hn aLo hi) T q₀ q else 0))
        + (∑' q, (if aLo + 1 ≤ q.cfg.1.doubleLevel ∧ q.cfg.1.doubleLevel + 1 ≤ hi
            ∧ q.resolve < M then iter (doubleBandStop n hn aLo hi) T q₀ q else 0)) := by
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun q => ?_
  set p := iter (doubleBandStop n hn aLo hi) T q₀ q with hp
  by_cases hlt : q.cfg.1.doubleLevel + 1 ≤ hi
  · rw [if_pos hlt]
    by_cases h1 : q.cfg.1.doubleLevel ≤ aLo
    · rw [if_pos h1]
      exact le_trans (self_le_add_right _ _) (self_le_add_right _ _)
    · rw [if_neg h1]
      by_cases h2 : M ≤ q.resolve
      · rw [if_pos ⟨by omega, h2⟩, zero_add]
        exact self_le_add_right _ _
      · rw [if_neg (by tauto), if_pos ⟨by omega, hlt, by omega⟩, zero_add, zero_add]
  · rw [if_neg hlt]; positivity

/-- **Per-phase failure bound.**  On the band chain from a fresh trace, the mass that
has NOT reached `hi` after `T` steps is at most the ruin mass plus the band direction
term `w^{L₀}/(w^{hi-1}·η^M)` plus the band productivity term `(pp'+pp·wp)^T/wp^{y₀+3M}`.
The per-phase analog of `noncons_mass_bound`; composed over `~lg n` phases it gives
`theorem2`. -/
theorem band_phase_fail (n : ℕ) (hn : 2 ≤ n) (aLo bHi hi M T : ℕ)
    (haLo : 0 < aLo) (hmaj : bHi ≤ aLo) (heq : aLo + bHi = 2 * n) (hhi : hi ≤ 2 * n)
    (w η u : ℝ≥0∞) (hu : u = (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (wp pp pp' : ℝ≥0∞) (hwp1 : wp ≤ 1) (hwp0 : wp ≠ 0) (hppp : pp + pp' = 1)
    (hwpt : wp ≠ ⊤) (hppT : pp ≠ ⊤) (hpp't : pp' ≠ ⊤)
    (hBprod : ∀ q : DoubleTrace n,
      ¬ (q.cfg.1.doubleLevel ≤ aLo ∨ hi ≤ q.cfg.1.doubleLevel) →
      pp ≤ (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xy
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xb
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .yb))
    (s₀ : DoubleState n) :
    ∑' q, (if q.cfg.1.doubleLevel + 1 ≤ hi then
        iter (doubleBandStop n hn aLo hi) T (⟨s₀, 0, 0⟩ : DoubleTrace n) q else 0)
      ≤ (∑' q, (if q.cfg.1.doubleLevel ≤ aLo then
            iter (doubleBandStop n hn aLo hi) T (⟨s₀, 0, 0⟩ : DoubleTrace n) q else 0))
        + w ^ s₀.1.doubleLevel / (w ^ (hi - 1) * η ^ M)
        + (pp' + pp * wp) ^ T * 1 / wp ^ (s₀.1.y + 3 * M) := by
  set q₀ : DoubleTrace n := ⟨s₀, 0, 0⟩ with hq0
  refine le_trans (band_split n hn aLo hi M T q₀) ?_
  refine add_le_add (add_le_add le_rfl ?_) ?_
  · have := doubleBandStop_tail n hn aLo bHi hi (hi - 1) M T haLo hmaj heq hhi w η u hu hrel hwη
      hw1 hw0 hη1 hηt q₀ (by simp [hq0])
    simpa [hq0] using this
  · have := band_productivity_term_le n hn aLo hi wp pp pp' hwp1 hwp0 hppp hwpt hppT hpp't
      hBprod M T s₀
    simpa [hq0] using this

/-- The band chain is `doubleDirStop` with an extra freeze at `level ≥ hi`. -/
theorem doubleBandStop_eq_freeze_dir (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ) :
    doubleBandStop n hn aLo hi
      = freeze (fun q : DoubleTrace n => hi ≤ q.cfg.1.doubleLevel) (doubleDirStop n hn aLo) := by
  funext q
  unfold doubleBandStop doubleDirStop freeze
  by_cases hhi : hi ≤ q.cfg.1.doubleLevel
  · rw [if_pos hhi, if_neg (by rintro ⟨_, h⟩; omega)]
  · rw [if_neg hhi]
    dsimp only
    by_cases haLo : aLo + 1 ≤ q.cfg.1.doubleLevel
    · rw [if_pos ⟨haLo, by omega⟩, if_pos haLo]
    · rw [if_neg (fun h => haLo h.1), if_neg haLo]

/-- **Band ruin term.**  The band-chain ruin mass is at most the direction-chain ruin
mass (freezing at `hi` only prevents reaching `aLo`), hence `≤ (bHi/aLo)^k`.  Uses the
complement identity `ruin = 1 − ¬ruin` and `mass_le_freeze` on the complement. -/
theorem band_ruin_term_le (n : ℕ) (hn : 2 ≤ n) (aLo bHi hi k T : ℕ) (haLohi : aLo < hi)
    (hpop2n : aLo + bHi + 2 = 2 * n) (haLo : 0 < aLo) (hbHi : 0 < bHi) (hmaj : bHi ≤ aLo)
    (q₀ : DoubleTrace n) (hstart : q₀.cfg.1.doubleLevel = aLo + k) :
    ∑' q, (if q.cfg.1.doubleLevel ≤ aLo then iter (doubleBandStop n hn aLo hi) T q₀ q else 0)
      ≤ ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k := by
  have hcompl : ∀ (K : DoubleTrace n → PMF (DoubleTrace n)),
      (∑' q, if q.cfg.1.doubleLevel ≤ aLo then iter K T q₀ q else 0)
        = 1 - (∑' q, if q.cfg.1.doubleLevel ≤ aLo then (0 : ℝ≥0∞) else iter K T q₀ q) := by
    intro K
    have hle1 : (∑' q, if q.cfg.1.doubleLevel ≤ aLo then (0 : ℝ≥0∞) else iter K T q₀ q) ≤ 1 := by
      calc _ ≤ ∑' q, iter K T q₀ q := ENNReal.tsum_le_tsum fun q => by split_ifs <;> simp
        _ = 1 := PMF.tsum_coe _
    have hne : (∑' q, if q.cfg.1.doubleLevel ≤ aLo then (0 : ℝ≥0∞) else iter K T q₀ q) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top hle1
    have hpt : ∀ q, (if q.cfg.1.doubleLevel ≤ aLo then iter K T q₀ q else 0)
        + (if q.cfg.1.doubleLevel ≤ aLo then (0 : ℝ≥0∞) else iter K T q₀ q) = iter K T q₀ q := by
      intro q; split_ifs <;> simp
    have hp : (∑' q, if q.cfg.1.doubleLevel ≤ aLo then iter K T q₀ q else 0)
        + (∑' q, if q.cfg.1.doubleLevel ≤ aLo then (0 : ℝ≥0∞) else iter K T q₀ q) = 1 := by
      rw [← ENNReal.tsum_add, tsum_congr hpt, PMF.tsum_coe]
    rw [← hp, ENNReal.add_sub_cancel_right hne]
  have hnoruin_le : (∑' q, if q.cfg.1.doubleLevel ≤ aLo then (0 : ℝ≥0∞)
        else iter (doubleDirStop n hn aLo) T q₀ q)
      ≤ (∑' q, if q.cfg.1.doubleLevel ≤ aLo then (0 : ℝ≥0∞)
        else iter (doubleBandStop n hn aLo hi) T q₀ q) := by
    rw [doubleBandStop_eq_freeze_dir n hn aLo hi]
    exact mass_le_freeze (doubleDirStop n hn aLo)
      (fun q : DoubleTrace n => hi ≤ q.cfg.1.doubleLevel)
      (fun q => q.cfg.1.doubleLevel ≤ aLo) (fun q hq => by omega) T q₀
  calc ∑' q, (if q.cfg.1.doubleLevel ≤ aLo then iter (doubleBandStop n hn aLo hi) T q₀ q else 0)
      = 1 - (∑' q, if q.cfg.1.doubleLevel ≤ aLo then (0 : ℝ≥0∞)
          else iter (doubleBandStop n hn aLo hi) T q₀ q) := hcompl _
    _ ≤ 1 - (∑' q, if q.cfg.1.doubleLevel ≤ aLo then (0 : ℝ≥0∞)
          else iter (doubleDirStop n hn aLo) T q₀ q) := tsub_le_tsub_left hnoruin_le 1
    _ = ∑' q, (if q.cfg.1.doubleLevel ≤ aLo then iter (doubleDirStop n hn aLo) T q₀ q else 0) :=
        (hcompl _).symm
    _ ≤ ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k :=
        ruin_term_le n hn aLo bHi k T hpop2n haLo hbHi hmaj q₀ hstart

/-- **Complete per-phase failure bound** (all terms explicit).  Combining
`band_phase_fail` with `band_ruin_term_le`: from a fresh trace at level `aLo + k`,
the mass not reaching `hi` after `T` steps is at most
`(bHiR/aLo)^k + w^{aLo+k}/(w^{hi-1}·η^M) + (pp'+pp·wp)^T/wp^{y₀+3M}`.
The ruin and direction complementary bounds differ by two, so they are kept as
separate parameters `bHiR` and `bHiD`.  This is the phase brick; the ladder
composes `~lg n` of these (geometric `hi`, harmonic `T`). -/
theorem band_phase_fail_full (n : ℕ) (hn : 2 ≤ n) (aLo bHiR bHiD hi k M T : ℕ)
    (haLohi : aLo < hi) (hpop2n : aLo + bHiR + 2 = 2 * n)
    (haLo : 0 < aLo) (hbHiR : 0 < bHiR) (hmajR : bHiR ≤ aLo)
    (heq : aLo + bHiD = 2 * n) (hmajD : bHiD ≤ aLo) (hhi : hi ≤ 2 * n)
    (w η u : ℝ≥0∞) (hu : u = (bHiD : ℝ≥0∞) / (aLo : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (wp pp pp' : ℝ≥0∞) (hwp1 : wp ≤ 1) (hwp0 : wp ≠ 0) (hppp : pp + pp' = 1)
    (hwpt : wp ≠ ⊤) (hppT : pp ≠ ⊤) (hpp't : pp' ≠ ⊤)
    (hBprod : ∀ q : DoubleTrace n,
      ¬ (q.cfg.1.doubleLevel ≤ aLo ∨ hi ≤ q.cfg.1.doubleLevel) →
      pp ≤ (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xy
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .xb
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2; simp only [BiCfg.DoubleInv] at this; omega) .yb))
    (s₀ : DoubleState n) (hstart : s₀.1.doubleLevel = aLo + k) :
    ∑' q, (if q.cfg.1.doubleLevel + 1 ≤ hi then
        iter (doubleBandStop n hn aLo hi) T (⟨s₀, 0, 0⟩ : DoubleTrace n) q else 0)
      ≤ ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k
        + w ^ s₀.1.doubleLevel / (w ^ (hi - 1) * η ^ M)
        + (pp' + pp * wp) ^ T * 1 / wp ^ (s₀.1.y + 3 * M) := by
  refine le_trans (band_phase_fail n hn aLo bHiD hi M T haLo hmajD heq hhi w η u hu hrel hwη
    hw1 hw0 hη1 hηt wp pp pp' hwp1 hwp0 hppp hwpt hppT hpp't hBprod s₀) ?_
  refine add_le_add (add_le_add ?_ le_rfl) le_rfl
  exact band_ruin_term_le n hn aLo bHiR hi k T haLohi hpop2n haLo hbHiR hmajR
    (⟨s₀, 0, 0⟩ : DoubleTrace n) (by simpa using hstart)

end Tri
