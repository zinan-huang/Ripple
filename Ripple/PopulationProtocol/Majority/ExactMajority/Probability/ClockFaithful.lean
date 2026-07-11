/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue C3 — the FAITHFUL clock O(log n) upper bound (Lemma 6.4)

This file is **Avenue C3** of the Doty et al. Theorem 3.1 time-half campaign.  It
replaces C2's CONDITIONAL/UNFAITHFUL `clock_composed_O_log_n` (which assumed the
cross-minute chaining `h_chain` as a free hypothesis) with the **genuine**
per-minute chaining for the O(log n) *upper* time bound — the headline source of
the speedup.

## The extended-consult refinement (the authoritative DAG)

The O(1)-per-minute UPPER time bound (Lemma 6.4 — THE source of O(log n)) does NOT
need the front/early-drip analysis.  Its proof is:

  once `c≥i ≥ 0.1` (minute `i` crossed, `hi n ≤ beyond i`), drips create a seed at
  minute `i+1` (`lo n ≤ beyond (i+1)`) within `O(n)` interactions, then epidemic
  growth (S1!) brings `beyond (i+1)` from the seed up to `hi n`.

We build this faithfully, in two GENUINELY-CHAINED phases:

* **`seedPhase`** (NEW content): from `CrossedB n i` (`hi n ≤ beyond i`), the
  count of agents at minute *exactly* `i` is `≥ hi n − lo n ≥ 0.8 n` whenever
  `beyond (i+1) < lo n`, so the same-state drip `(s_i, s_i) ↦ (s_i, s_{i+1})`
  fires with per-step probability `≥ Θ(1)` (`clock_drip_seed_advance_prob`, a
  LOWER bound, proven from first principles by the singleton-mass technique — the
  exact dual of C2's `clock_beyond_advance_prob`).  A window contraction on the
  *seed deficit* `lo n − beyond (i+1)` then crosses `0 → lo n` in `O(n)`
  interactions.  Its `Post` is `floorInvB n (i+1)` (`card = n ∧ lo n ≤ beyond
  (i+1)`), and its `Pre` is exactly `CrossedB n i ∧ card = n`.

* **`epidemicPhase`** (= C2's S1-transported `bulkPhase`, REUSED honestly): from
  `floorInvB n (i+1)` (`lo n ≤ beyond (i+1)`), the bulk epidemic crosses
  `beyond (i+1): lo n → hi n` in `O(n)` interactions (`windowPotB_drift_floorInv`,
  the genuine transport of S1's constant-density contraction).  Its `Post` is
  `CrossedB n (i+1)`, its `Pre` is `floorInvB n (i+1)`.

The chaining `seedPhase.Post → epidemicPhase.Pre` is `floorInvB n (i+1) →
floorInvB n (i+1)` — **a genuine implication, not the assumed `h_chain` of C2**.
And `epidemicPhase.Post → seedPhase'.Pre` for the next minute is
`CrossedB n (i+1) → (CrossedB n (i+1) ∧ card = n)`, also genuine (card is an
absorbing invariant).

Composing one `seedPhase ++ epidemicPhase` per minute over `kL = Θ(log n)`
minutes gives total interactions `O(n · kL) = O(n log n)` = `O(log n)` parallel,
failure `≤ kL · (per-minute) = 1/poly` — the faithful upgrade of the proven
`Θ(log² n)`.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockOLogN

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockFaithful

open ClockTime ConstantDensity ClockOLogN FrontTailKernel

variable {L₀ : ℕ}

/-! ## Part A — the drip-seed advance probability (the SEED keystone, a LOWER
bound; the genuine dual of C2's `clock_beyond_advance_prob`).

When minute `i` is crossed (`hi n ≤ beyond i`) but minute `i+1` is not yet seeded
to the floor (`beyond (i+1) < lo n`), there are at least `hi n − lo n` agents at
minute *exactly* `i`.  The same-state drip `(s_i, s_i) ↦ (s_i, dripUp s_i) =
(s_i, s_{i+1})` raises one of them to minute `i+1`, advancing `beyond (i+1)` by
one, and the scheduler picks the ordered pair `(s_i, s_i)` with probability
`m·(m−1) / (n·(n−1))` where `m = count s_i`.  We LOWER-bound the advance
probability by this single same-state pair's mass. -/

/-- A scheduled same-state drip pair `(s_i, s_i)` at minute exactly `i` (with
`i + 1 ≤ L₀`, so `dripUp` actually increments) raises `beyond (i+1)` by one,
provided two agents sit at minute `i`. -/
theorem drip_pair_advances (T j : ℕ) (hT : T + 1 ≤ L₀) (c : Config (Minute L₀))
    (hcount : 2 ≤ c.count (frontState (L₀ := L₀) T (by omega)))
    (hj : beyond (T + 1) c = j) :
    j + 1 ≤ beyond (T + 1)
      (Protocol.scheduledStep (clockProto L₀) c
        (frontState (L₀ := L₀) T (by omega), frontState (L₀ := L₀) T (by omega))) := by
  classical
  set sT := frontState (L₀ := L₀) T (by omega) with hsT
  -- applicability: the same-state pair {s_T, s_T} ≤ c since count s_T ≥ 2.
  have hpaircount : ∀ x : Minute L₀,
      Multiset.count x ({sT, sT} : Multiset (Minute L₀))
        = (if x = sT then 2 else 0) := by
    intro x
    rw [show ({sT, sT} : Multiset (Minute L₀)) = sT ::ₘ sT ::ₘ 0 from rfl]
    rw [Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
    by_cases hx : x = sT <;> simp [hx]
  have happ : Protocol.Applicable c sT sT := by
    refine Multiset.le_iff_count.mpr ?_
    intro x
    rw [hpaircount x]
    have hcx : Multiset.count sT c = c.count sT := rfl
    by_cases hx : x = sT
    · subst hx; rw [if_pos rfl, hcx]; omega
    · rw [if_neg hx]; omega
  show j + 1 ≤ beyond (T + 1) (Protocol.stepOrSelf (clockProto L₀) c sT sT)
  rw [beyond_stepOrSelf_applicable (T + 1) c sT sT happ]
  -- δ s_T s_T = (s_T, dripUp s_T)
  have hδ : (clockProto L₀).δ sT sT = (sT, dripUp sT) := by
    rw [clockProto_delta, if_pos rfl]
  rw [hδ]
  -- countP (≥ T+1) of a 2-element multiset
  have hcountP2 : ∀ x y : Minute L₀,
      Multiset.countP (fun a => T + 1 ≤ a.val) ({x, y} : Multiset (Minute L₀))
        = (if T + 1 ≤ x.val then 1 else 0) + (if T + 1 ≤ y.val then 1 else 0) := by
    intro x y
    rw [show ({x, y} : Multiset (Minute L₀)) = x ::ₘ y ::ₘ 0 from rfl]
    rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]; ring
  -- s_T sits at minute exactly T (< T+1); dripUp s_T sits at minute T+1.
  have hsT_val : sT.val = T := by rw [hsT, frontState_val]
  have hdrip_eq : (dripUp sT).val = T + 1 := by
    unfold dripUp
    rw [dif_pos (by omega)]
    show sT.val + 1 = T + 1
    omega
  rw [hcountP2 sT (dripUp sT), hcountP2 sT sT]
  -- consumed: {s_T, s_T}, both < T+1 ⇒ 0; produced: {s_T, s_{T+1}} ⇒ 1.
  have hsT_lt : ¬ (T + 1 ≤ sT.val) := by rw [hsT_val]; omega
  have hdrip_ge : T + 1 ≤ (dripUp sT).val := by rw [hdrip_eq]
  simp only [if_neg hsT_lt, if_pos hdrip_ge]
  -- beyond (T+1) c = j; net: (j - 0) + 1 = j + 1
  have hjc : Multiset.countP (fun a => T + 1 ≤ a.val) c = j := hj
  rw [hjc]
  omega

/-- **The clock-side drip-seed advance probability (the SEED keystone, a LOWER
bound).**  If `c` has `2 ≤ card`, `T + 1 ≤ L₀`, `beyond (T+1) c = j`, and at least
`2` agents sit at minute exactly `T` (`2 ≤ count s_T`), then one scheduler step
raises `beyond (T+1)` to `≥ j+1` with probability at least
`m·(m−1)/(card·(card−1))` where `m = count s_T` — the mass of the single
same-state drip pair `(s_T, s_T)`.  This is the genuine dual of C2's
`clock_beyond_advance_prob`, proven by lower-bounding the advance set's measure by
the singleton pair's interaction probability. -/
theorem clock_drip_seed_advance_prob (T : ℕ) (hT : T + 1 ≤ L₀)
    (c : Config (Minute L₀)) (j : ℕ) (hc : 2 ≤ c.card)
    (hj : beyond (T + 1) c = j)
    (hcount : 2 ≤ c.count (frontState (L₀ := L₀) T (by omega))) :
    ((clockProto L₀).stepDistOrSelf c).toMeasure {c' | j + 1 ≤ beyond (T + 1) c'} ≥
      ENNReal.ofReal ((c.count (frontState (L₀ := L₀) T (by omega)) *
        (c.count (frontState (L₀ := L₀) T (by omega)) - 1) : ℝ) /
        (c.card * (c.card - 1) : ℝ)) := by
  classical
  set sT := frontState (L₀ := L₀) T (by omega) with hsT
  set m := c.count sT with hm
  set n := c.card with hn
  -- stepDistOrSelf = stepDist (map scheduledStep interactionPMF)
  have hstepDist : (clockProto L₀).stepDistOrSelf c = (clockProto L₀).stepDist c hc := by
    unfold Protocol.stepDistOrSelf; rw [dif_pos hc]
  have hmeas : MeasurableSet {c' : Config (Minute L₀) | j + 1 ≤ beyond (T + 1) c'} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  -- the singleton pair (sT, sT) is contained in the advance preimage.
  have hsub : ({(sT, sT)} : Set (Minute L₀ × Minute L₀)) ⊆
      (Protocol.scheduledStep (clockProto L₀) c) ⁻¹' {c' | j + 1 ≤ beyond (T + 1) c'} := by
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    exact drip_pair_advances T j hT c hcount hj
  -- the measure of the advance set = interactionPMF measure of the preimage
  have hbase : ((clockProto L₀).stepDistOrSelf c).toMeasure {c' | j + 1 ≤ beyond (T + 1) c'}
      = (c.interactionPMF hc).toMeasure
          ((Protocol.scheduledStep (clockProto L₀) c) ⁻¹' {c' | j + 1 ≤ beyond (T + 1) c'}) := by
    rw [hstepDist]
    unfold Protocol.stepDist
    rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hmeas]
  rw [hbase]
  -- lower bound the preimage measure by the singleton pair's mass.
  have hmono : (c.interactionPMF hc).toMeasure ({(sT, sT)} : Set _)
      ≤ (c.interactionPMF hc).toMeasure
          ((Protocol.scheduledStep (clockProto L₀) c) ⁻¹' {c' | j + 1 ≤ beyond (T + 1) c'}) :=
    measure_mono hsub
  refine le_trans ?_ hmono
  -- toMeasure {(sT,sT)} = interactionProb sT sT = m(m-1)/(n(n-1)).
  have hsingle : (c.interactionPMF hc).toMeasure ({(sT, sT)} : Set _)
      = c.interactionProb sT sT := by
    rw [PMF.toMeasure_apply_singleton _ _ (DiscreteMeasurableSpace.forall_measurableSet _)]
    rfl
  rw [hsingle]
  -- interactionProb sT sT = ↑(m(m-1)) / ↑(n(n-1)) = ofReal(m(m-1)/(n(n-1))).
  have hIP : c.interactionProb sT sT
      = (↑(m * (m - 1)) : ℝ≥0∞) / (↑(n * (n - 1)) : ℝ≥0∞) := by
    unfold Config.interactionProb Config.interactionCount Config.totalPairs
    rw [if_pos rfl]
  rw [hIP]
  have hdenN_pos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  have hdenN_posR : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast hdenN_pos
  have hratio : (↑(m * (m - 1)) : ℝ≥0∞) / (↑(n * (n - 1)) : ℝ≥0∞)
      = ENNReal.ofReal (((m * (m - 1) : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos hdenN_posR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [hratio]
  apply ENNReal.ofReal_le_ofReal
  -- (m(m-1) : ℕ)/(n(n-1) : ℕ) = (m·(m-1) : ℝ)/(n·(n-1) : ℝ).
  have hmle : m ≤ n := by rw [hm, hn]; exact Multiset.count_le_card sT c
  have hm1 : 1 ≤ m := by omega
  have hn1 : 1 ≤ n := by omega
  have hnumL : ((m * (m - 1) : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hm1, Nat.cast_one]
  have hdenL : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hn1, Nat.cast_one]
  rw [hnumL, hdenL]

/-! ## Part B — the seed deficit window contraction.

We now show that, on the "minute `i` crossed but minute `i+1` not yet seeded to
the floor" regime, the seed `beyond (i+1)` grows `0 → lo n` in `O(n)`
interactions with `exp(−Θ(n))` failure.  The driver is `clock_drip_seed_advance_prob`:
when `hi n ≤ beyond i` (minute `i` crossed) and `beyond (i+1) < lo n`, the count
of agents at minute exactly `i` is `≥ hi n − lo n ≥ 0.8 n`, so the drip-seed
advance fires with per-step probability `≥ 1/4`. -/

/-- The count of agents at minute *exactly* `T` equals `beyond T − beyond (T+1)`:
agents at minute `≥ T` minus those at minute `≥ T+1`. -/
theorem count_frontState_eq (T : ℕ) (hT : T + 1 ≤ L₀) (c : Config (Minute L₀)) :
    c.count (frontState (L₀ := L₀) T (by omega)) = beyond T c - beyond (T + 1) c := by
  classical
  set sT := frontState (L₀ := L₀) T (by omega) with hsT
  have hsT_val : sT.val = T := by rw [hsT, frontState_val]
  -- beyond T = count sT + beyond (T+1):  split countP (T ≤ ·.val) over (T+1 ≤ ·.val).
  have hsplit : beyond T c = c.count sT + beyond (T + 1) c := by
    have hkey := Multiset.countP_eq_countP_filter_add c
      (fun a : Minute L₀ => T ≤ a.val) (fun a : Minute L₀ => T + 1 ≤ a.val)
    -- first summand: on the (T+1 ≤ ·.val) filter, (T ≤ ·.val) always holds.
    have h1 : (Multiset.filter (fun a : Minute L₀ => T + 1 ≤ a.val) c).countP
          (fun a : Minute L₀ => T ≤ a.val) = beyond (T + 1) c := by
      unfold beyond
      rw [Multiset.countP_filter]
      apply Multiset.countP_congr rfl
      intro a _ ; simp only [eq_iff_iff]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨by omega, h⟩
    -- second summand: on the (¬ T+1 ≤ ·.val) filter, (T ≤ ·.val) ⇔ (a = sT).
    have h2 : (Multiset.filter (fun a : Minute L₀ => ¬ T + 1 ≤ a.val) c).countP
          (fun a : Minute L₀ => T ≤ a.val) = c.count sT := by
      rw [Multiset.countP_filter]
      show Multiset.countP (fun a : Minute L₀ => T ≤ a.val ∧ ¬ T + 1 ≤ a.val) c
        = Multiset.countP (fun x => sT = x) c
      apply Multiset.countP_congr rfl
      intro a _ ; simp only [eq_iff_iff]
      constructor
      · intro ⟨hge, hlt⟩
        apply Fin.ext; rw [hsT_val]; omega
      · intro h; rw [← h]; rw [hsT_val]; omega
    show Multiset.countP (fun a : Minute L₀ => T ≤ a.val) c = c.count sT + beyond (T + 1) c
    rw [hkey, h1, h2, add_comm]
  omega

/-- **The drip-seed advance probability is at least `1/4` in the seed regime.**
When the count `m` of agents at minute exactly `i` is at least `hi n − lo n`
(`≥ 0.7 n`, the regime when minute `i` is crossed but `i+1` not seeded) and
`n ≥ 20`, the drip-seed advance ratio `m·(m−1) / (n·(n−1))` is at least `1/4`.
This is the constant-fraction lower bound feeding the seed window contraction —
the dual of S1's `advance_prob_ge` for the same-state drip event. -/
theorem drip_advance_prob_ge (n m : ℕ) (hn : 20 ≤ n) (hm : hi n - lo n ≤ m) :
    (1 : ℝ) / 4 ≤ (m * (m - 1) : ℝ) / (n * (n - 1) : ℝ) := by
  -- nat arithmetic: 10·(hi n − lo n) ≥ 7n, hence m ≥ 7n/10, hence 4 m(m-1) ≥ n(n-1).
  have hhi : hi n = 9 * n / 10 := rfl
  have hlo : lo n = n / 10 := rfl
  have hfloor : 7 * n ≤ 10 * (hi n - lo n) := by
    rw [hhi, hlo]; omega
  have hm7 : 7 * n ≤ 10 * m := by omega
  have hm1 : 1 ≤ m := by omega
  have hn1 : 1 ≤ n := by omega
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
    nlinarith
  rw [le_div_iff₀ hden_pos]
  -- real bounds: 10·m ≥ 7·n, m ≥ 1, n ≥ 20.
  have hm7R : 7 * (n : ℝ) ≤ 10 * (m : ℝ) := by exact_mod_cast hm7
  have hnR : (20 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  -- goal: 1/4 · (n·(n-1)) ≤ m·(m-1).  With m ≥ 0.7n, m ≥ 1, n ≥ 20.
  nlinarith [hm7R, hnR, hm1R, mul_nonneg (le_trans (by norm_num) hm1R) (by linarith : (0:ℝ) ≤ (m:ℝ) - 1)]

/-! ### The seed window potential and its contraction.

We track the seed `beyond (T+1)` crossing `0 → lo n`.  The window potential is the
exponential of the *deficit* `lo n − beyond (T+1)`, clamped to `[0, lo n]`.  The
"seed floor invariant" is `card = n ∧ CrossedB n T` (minute `T` crossed), which is
absorbing; on it, while the seed is below `lo n`, the count at minute exactly `T`
is `≥ hi n − lo n`, so the drip-seed advance fires with probability `≥ 1/4`. -/

/-- The clamped seed count, restricted to the window `[0, lo n]`. -/
def clampSeed (n T : ℕ) (c : Config (Minute L₀)) : ℕ := min (beyond (T + 1) c) (lo n)

/-- The seed "crossing finished" predicate: `beyond (T+1)` reaches `lo n`. -/
def SeededB (n T : ℕ) (c : Config (Minute L₀)) : Prop := lo n ≤ beyond (T + 1) c

/-- The seed window potential (deficit `lo n − clampSeed`). -/
noncomputable def seedPot (n T : ℕ) (s : ℝ) (c : Config (Minute L₀)) : ℝ≥0∞ :=
  if lo n ≤ beyond (T + 1) c then 0
  else ENNReal.ofReal (Real.exp (s * ((lo n : ℝ) - (clampSeed (L₀ := L₀) n T c : ℝ))))

theorem seedPot_measurable (n T : ℕ) (s : ℝ) :
    Measurable (seedPot (L₀ := L₀) n T s) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

/-- The seed floor invariant: `card = n` and minute `T` is crossed
(`hi n ≤ beyond T`). -/
def seedFloorInv (n T : ℕ) (c : Config (Minute L₀)) : Prop :=
  c.card = n ∧ CrossedB (L₀ := L₀) n T c

/-- The seed floor invariant is absorbing: `card` preserved and `CrossedB n T`
preserved (`beyond_ge_monotone`). -/
theorem seedFloorInv_absorbing (n T : ℕ) (c c' : Config (Minute L₀))
    (h : seedFloorInv (L₀ := L₀) n T c)
    (hc' : c' ∈ ((clockProto L₀).stepDistOrSelf c).support) :
    seedFloorInv (L₀ := L₀) n T c' := by
  obtain ⟨hcard, hcr⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Protocol.stepDistOrSelf_support_card_eq (clockProto L₀) c c' hc']; exact hcard
  · exact beyond_ge_monotone T (hi n) c c' hcr hc'

theorem clampSeed_eq_of_lt (n T : ℕ) (c : Config (Minute L₀))
    (h : beyond (T + 1) c < lo n) :
    clampSeed (L₀ := L₀) n T c = beyond (T + 1) c := by
  unfold clampSeed; omega

/-- Pointwise one-step bound on the seed window potential (mirror of S1's
`windowPot_pointwise_bound`), using `beyond_ge_monotone` for support
monotonicity of `beyond (T+1)`. -/
theorem seedPot_pointwise_bound (n T : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (Minute L₀)) (m : ℕ) (hm : beyond (T + 1) c = m)
    (hm_hi : m < lo n)
    (c' : Config (Minute L₀)) (hsupp : c' ∈ ((clockProto L₀).stepDistOrSelf c).support) :
    seedPot (L₀ := L₀) n T s c' ≤
      (if m + 1 ≤ beyond (T + 1) c' then
        ENNReal.ofReal (Real.exp (s * ((lo n : ℝ) - (m : ℝ) - 1)))
      else
        ENNReal.ofReal (Real.exp (s * ((lo n : ℝ) - (m : ℝ))))) := by
  have hmono : m ≤ beyond (T + 1) c' := beyond_ge_monotone (T + 1) m c c' (by rw [hm]) hsupp
  unfold seedPot clampSeed
  by_cases hcross : lo n ≤ beyond (T + 1) c'
  · rw [if_pos hcross]; split_ifs <;> positivity
  · rw [if_neg hcross]
    rw [not_le] at hcross
    by_cases hadv : m + 1 ≤ beyond (T + 1) c'
    · rw [if_pos hadv]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hclamp : min (beyond (T + 1) c') (lo n) = beyond (T + 1) c' := by omega
      rw [hclamp]
      have : (m : ℝ) + 1 ≤ (beyond (T + 1) c' : ℝ) := by exact_mod_cast hadv
      nlinarith [hs, this]
    · rw [if_neg hadv]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have heq : beyond (T + 1) c' = m := by omega
      have hclamp : min (beyond (T + 1) c') (lo n) = beyond (T + 1) c' := by omega
      rw [hclamp, heq]

/-- **The seed window contraction (the SEED keystone drift).**  On the seed floor
invariant (`card = n`, `hi n ≤ beyond T`) and an unseeded config
(`beyond (T+1) < lo n`), the seed window potential contracts at rate
`r = 1 − (1/4)(1 − e^{−s})`.  The `1/4` comes from `drip_advance_prob_ge`: minute
`T` crossed means `count s_T = beyond T − beyond (T+1) ≥ hi n − lo n`, so the
drip-seed advance (`clock_drip_seed_advance_prob`) fires with probability `≥ 1/4`.
This is the genuine drift driving the seed `0 → lo n`. -/
theorem seedPot_contracts_on_floor (n T : ℕ) (hT : T + 1 ≤ L₀) (s : ℝ) (hs : 0 < s)
    (hn : 20 ≤ n) (c : Config (Minute L₀)) (hfl : seedFloorInv (L₀ := L₀) n T c)
    (hnc : ¬ SeededB (L₀ := L₀) n T c) :
    ∫⁻ c', seedPot (L₀ := L₀) n T s c' ∂((clockProto L₀).transitionKernel c) ≤
      ENNReal.ofReal (1 - (1 / 4) * (1 - Real.exp (-s)))
        * seedPot (L₀ := L₀) n T s c := by
  obtain ⟨hcard, hcr⟩ := hfl
  set m := beyond (T + 1) c with hm
  have hm_hi : m < lo n := by rw [SeededB, not_le] at hnc; exact hnc
  -- Φ(c) = ofReal(exp(s(lo - m)))
  have hΦc : seedPot (L₀ := L₀) n T s c
      = ENNReal.ofReal (Real.exp (s * ((lo n : ℝ) - (m : ℝ)))) := by
    unfold seedPot
    rw [if_neg (by rw [← hm]; omega)]
    rw [clampSeed_eq_of_lt n T c (by rw [← hm]; omega)]
  set A := {c' : Config (Minute L₀) | m + 1 ≤ beyond (T + 1) c'} with hA_def
  have hA_meas : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  have hc2 : 2 ≤ c.card := by rw [hcard]; omega
  -- count at minute exactly T ≥ hi n − lo n.
  set sT := frontState (L₀ := L₀) T (by omega) with hsT
  have hcount_eq : c.count sT = beyond T c - beyond (T + 1) c := count_frontState_eq T hT c
  have hbeyondT : hi n ≤ beyond T c := hcr
  have hcount_ge : hi n - lo n ≤ c.count sT := by
    rw [hcount_eq, ← hm]
    omega
  have hcount2 : 2 ≤ c.count sT := by
    have : 14 ≤ hi n - lo n := by unfold hi lo; omega
    omega
  -- the drip-seed advance probability is ≥ 1/4.
  have hstep := clock_drip_seed_advance_prob T hT c m hc2 hm.symm hcount2
  have hp4 : (1 : ℝ) / 4 ≤ (c.count sT * (c.count sT - 1) : ℝ) / (c.card * (c.card - 1) : ℝ) := by
    rw [hcard]; exact drip_advance_prob_ge n (c.count sT) hn hcount_ge
  set E0 : ℝ := Real.exp (s * ((lo n : ℝ) - (m : ℝ))) with hE0
  set E1 : ℝ := Real.exp (s * ((lo n : ℝ) - (m : ℝ) - 1)) with hE1
  have hE0_pos : 0 < E0 := Real.exp_pos _
  have hE1_pos : 0 < E1 := Real.exp_pos _
  have hE1_eq : E1 = E0 * Real.exp (-s) := by
    rw [hE0, hE1, ← Real.exp_add]; congr 1; ring
  change ∫⁻ c', seedPot (L₀ := L₀) n T s c' ∂((clockProto L₀).stepDistOrSelf c).toMeasure ≤ _
  calc ∫⁻ c', seedPot (L₀ := L₀) n T s c' ∂((clockProto L₀).stepDistOrSelf c).toMeasure
      ≤ ∫⁻ c', (if m + 1 ≤ beyond (T + 1) c' then ENNReal.ofReal E1
          else ENNReal.ofReal E0) ∂((clockProto L₀).stepDistOrSelf c).toMeasure := by
        apply lintegral_mono_ae
        rw [ae_iff]
        rw [PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]
        intro x hsupp hbad
        apply hbad
        exact seedPot_pointwise_bound n T s hs c m hm.symm hm_hi x hsupp
    _ = (∫⁻ c' in A, ENNReal.ofReal E1 ∂((clockProto L₀).stepDistOrSelf c).toMeasure) +
        (∫⁻ c' in Aᶜ, ENNReal.ofReal E0 ∂((clockProto L₀).stepDistOrSelf c).toMeasure) := by
        rw [← lintegral_add_compl _ hA_meas]
        congr 1
        · apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hA_meas] with c' hc'
          simp only [Set.mem_setOf_eq, hA_def] at hc'
          simp [hc']
        · apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hA_meas.compl] with c' hc'
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hA_def] at hc'
          simp [hc']
    _ = ENNReal.ofReal E1 * ((clockProto L₀).stepDistOrSelf c).toMeasure A +
        ENNReal.ofReal E0 * ((clockProto L₀).stepDistOrSelf c).toMeasure Aᶜ := by
        rw [lintegral_const, Measure.restrict_apply_univ,
            lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (1 - (1 / 4) * (1 - Real.exp (-s)))
          * seedPot (L₀ := L₀) n T s c := by
        rw [hΦc]
        set q := ((clockProto L₀).stepDistOrSelf c).toMeasure A with hq_def
        set qc := ((clockProto L₀).stepDistOrSelf c).toMeasure Aᶜ with hqc_def
        haveI : IsProbabilityMeasure ((clockProto L₀).stepDistOrSelf c).toMeasure :=
          PMF.toMeasure.isProbabilityMeasure _
        have hq_ge : ENNReal.ofReal ((1 : ℝ) / 4) ≤ q := by
          refine le_trans (ENNReal.ofReal_le_ofReal hp4) ?_
          exact hstep
        have hq_le_one : q ≤ 1 := by
          calc q ≤ ((clockProto L₀).stepDistOrSelf c).toMeasure Set.univ :=
                measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        have hq_ne_top : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq_le_one
        have hqc_eq : qc = 1 - q := by
          have h_compl := measure_compl hA_meas hq_ne_top
          rw [show ((clockProto L₀).stepDistOrSelf c).toMeasure Set.univ = 1 from measure_univ]
            at h_compl
          exact h_compl
        set qr := q.toReal with hqr_def
        have hqr_nonneg : 0 ≤ qr := ENNReal.toReal_nonneg
        have hqr_le_one : qr ≤ 1 := by
          have := ENNReal.toReal_mono ENNReal.one_ne_top hq_le_one
          rwa [ENNReal.toReal_one] at this
        have hq_ofReal : q = ENNReal.ofReal qr := (ENNReal.ofReal_toReal hq_ne_top).symm
        have h4_le_qr : (1 : ℝ) / 4 ≤ qr := by
          have h1 : ENNReal.ofReal ((1 : ℝ) / 4) ≤ ENNReal.ofReal qr := by
            rw [← hq_ofReal]; exact hq_ge
          exact (ENNReal.ofReal_le_ofReal_iff hqr_nonneg).mp h1
        have h1mqr_nonneg : 0 ≤ 1 - qr := by linarith
        have hqc_ofReal : qc = ENNReal.ofReal (1 - qr) := by
          rw [hqc_eq, hq_ofReal,
              show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
              ← ENNReal.ofReal_sub 1 hqr_nonneg]
        have lhs_eq : ENNReal.ofReal E1 * q + ENNReal.ofReal E0 * qc =
            ENNReal.ofReal (E1 * qr + E0 * (1 - qr)) := by
          rw [hq_ofReal, hqc_ofReal,
              ← ENNReal.ofReal_mul hE1_pos.le, ← ENNReal.ofReal_mul hE0_pos.le,
              ← ENNReal.ofReal_add (mul_nonneg hE1_pos.le hqr_nonneg)
                (mul_nonneg hE0_pos.le h1mqr_nonneg)]
        have rhs_eq : ENNReal.ofReal (1 - (1 / 4) * (1 - Real.exp (-s)))
            * ENNReal.ofReal E0 =
            ENNReal.ofReal ((1 - (1 / 4) * (1 - Real.exp (-s))) * E0) := by
          rw [← ENNReal.ofReal_mul]
          have hexp_le_one : Real.exp (-s) ≤ 1 := by
            rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
            exact Real.exp_le_exp.mpr (by linarith)
          have : (1 : ℝ) - (1 / 4) * (1 - Real.exp (-s)) ≥ 0 := by
            have : (0 : ℝ) ≤ 1 - Real.exp (-s) := by linarith
            nlinarith
          linarith
        rw [lhs_eq, rhs_eq]
        apply ENNReal.ofReal_le_ofReal
        have hexp_lt_one : Real.exp (-s) ≤ 1 := by
          rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
          exact Real.exp_le_exp.mpr (by linarith)
        have hfactor : E1 * qr + E0 * (1 - qr) = E0 * (1 - qr * (1 - Real.exp (-s))) := by
          rw [hE1_eq]; ring
        rw [hfactor]
        have hrhs : (1 - (1 / 4) * (1 - Real.exp (-s))) * E0
            = E0 * (1 - (1 / 4) * (1 - Real.exp (-s))) := by ring
        rw [hrhs]
        apply mul_le_mul_of_nonneg_left _ hE0_pos.le
        have h1me : (0 : ℝ) ≤ 1 - Real.exp (-s) := by linarith
        nlinarith [mul_le_mul_of_nonneg_right h4_le_qr h1me]

/-- On `{¬SeededB}` the seed window potential is `≥ 1` (mirror of S1's
`not_crossed_imp_pot_ge_one`). -/
theorem not_seededB_imp_seedPot_ge_one (n T : ℕ) (s : ℝ) (hs : 0 < s) (hn : 20 ≤ n)
    (c : Config (Minute L₀)) (hnc : ¬ SeededB (L₀ := L₀) n T c) :
    1 ≤ seedPot (L₀ := L₀) n T s c := by
  unfold SeededB at hnc
  rw [not_le] at hnc
  unfold seedPot clampSeed
  rw [if_neg (by omega)]
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  apply Real.exp_le_exp.mpr
  have hlo_pos : 0 < lo n := lo_pos n hn
  have hclamp_lt : min (beyond (T + 1) c) (lo n) ≤ lo n - 1 := by omega
  have h1 : ((min (beyond (T + 1) c) (lo n) : ℕ) : ℝ) ≤ (lo n : ℝ) - 1 := by
    have h1' : ((min (beyond (T + 1) c) (lo n) : ℕ) : ℝ) ≤ ((lo n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hclamp_lt
    have h2 : ((lo n - 1 : ℕ) : ℝ) = (lo n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    linarith
  have hdef : (1 : ℝ) ≤ (lo n : ℝ) - ((min (beyond (T + 1) c) (lo n) : ℕ) : ℝ) := by
    linarith
  nlinarith [hs, hdef]

/-- The seed drift holds on the *entire* seed floor invariant (seeded or not): on
seeded configs `Φ = 0` and `SeededB` is preserved (`beyond_ge_monotone`).  This is
the full `hdrift` the framework consumes. -/
theorem seedPot_drift_floorInv (n T : ℕ) (hT : T + 1 ≤ L₀) (s : ℝ) (hs : 0 < s)
    (hn : 20 ≤ n) (c : Config (Minute L₀)) (hfl : seedFloorInv (L₀ := L₀) n T c) :
    ∫⁻ c', seedPot (L₀ := L₀) n T s c' ∂((clockProto L₀).transitionKernel c) ≤
      ENNReal.ofReal (1 - (1 / 4) * (1 - Real.exp (-s)))
        * seedPot (L₀ := L₀) n T s c := by
  by_cases hnc : SeededB (L₀ := L₀) n T c
  · have hnc' : lo n ≤ beyond (T + 1) c := hnc
    have hΦc0 : seedPot (L₀ := L₀) n T s c = 0 := by
      unfold seedPot; rw [if_pos hnc']
    rw [hΦc0, mul_zero, nonpos_iff_eq_zero]
    change ∫⁻ c', seedPot (L₀ := L₀) n T s c'
        ∂((clockProto L₀).stepDistOrSelf c).toMeasure = 0
    rw [lintegral_eq_zero_iff (seedPot_measurable n T s)]
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨((clockProto L₀).stepDistOrSelf c).support, ?_, ?_⟩
    · rw [mem_ae_iff, PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      rw [Set.disjoint_left]; intro x hsupp hx
      exact hx (PMF.mem_support_iff _ _ |>.mp hsupp)
    · intro c' hc'
      have hcr : lo n ≤ beyond (T + 1) c' := beyond_ge_monotone (T + 1) (lo n) c c' hnc hc'
      show seedPot (L₀ := L₀) n T s c' = 0
      unfold seedPot; rw [if_pos hcr]
  · exact seedPot_contracts_on_floor n T hT s hs hn c hfl hnc

/-! ### The card-guarded seed potential (so `card = n` flows through `Post`).

To DISCHARGE C2's cross-minute chaining genuinely we must carry `card = n` in each
phase's `Post` (so it implies the next phase's `Pre`).  We guard the seed potential
with `card = n`: off-card configs get potential `⊤`, which makes the threshold link
`¬(card = n ∧ SeededB) → θ ≤ Φ` hold everywhere (off-card: `Φ = ⊤ ≥ θ`; on-card &
unseeded: `Φ = seedPot ≥ 1 = θ`), while the drift is unaffected on the `card = n`
floor invariant (which is absorbing). -/

/-- The card-guarded seed potential: `⊤` off the `card = n` shell, else `seedPot`. -/
noncomputable def seedPotG (n T : ℕ) (s : ℝ) (c : Config (Minute L₀)) : ℝ≥0∞ :=
  if c.card = n then seedPot (L₀ := L₀) n T s c else ⊤

theorem seedPotG_measurable (n T : ℕ) (s : ℝ) :
    Measurable (seedPotG (L₀ := L₀) n T s) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

/-- On the seed floor invariant (`card = n`) the guard is transparent. -/
theorem seedPotG_eq_on_floor (n T : ℕ) (s : ℝ) (c : Config (Minute L₀))
    (hcard : c.card = n) :
    seedPotG (L₀ := L₀) n T s c = seedPot (L₀ := L₀) n T s c := by
  unfold seedPotG; rw [if_pos hcard]

/-- Drift of the guarded potential on the seed floor invariant. -/
theorem seedPotG_drift_floorInv (n T : ℕ) (hT : T + 1 ≤ L₀) (s : ℝ) (hs : 0 < s)
    (hn : 20 ≤ n) (c : Config (Minute L₀)) (hfl : seedFloorInv (L₀ := L₀) n T c) :
    ∫⁻ c', seedPotG (L₀ := L₀) n T s c' ∂((clockProto L₀).transitionKernel c) ≤
      ENNReal.ofReal (1 - (1 / 4) * (1 - Real.exp (-s)))
        * seedPotG (L₀ := L₀) n T s c := by
  obtain ⟨hcard, hcr⟩ := hfl
  rw [seedPotG_eq_on_floor n T s c hcard]
  -- on the support, card = n, so seedPotG = seedPot a.e.; the integral matches.
  have hint_eq : ∫⁻ c', seedPotG (L₀ := L₀) n T s c' ∂((clockProto L₀).transitionKernel c)
      = ∫⁻ c', seedPot (L₀ := L₀) n T s c' ∂((clockProto L₀).transitionKernel c) := by
    apply lintegral_congr_ae
    change ∀ᵐ c' ∂((clockProto L₀).stepDistOrSelf c).toMeasure,
      seedPotG (L₀ := L₀) n T s c' = seedPot (L₀ := L₀) n T s c'
    rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    rw [Set.disjoint_left]
    intro x hsupp hbad
    apply hbad
    have hxcard : x.card = n := by
      rw [← hcard]; exact Protocol.stepDistOrSelf_support_card_eq (clockProto L₀) c x hsupp
    exact seedPotG_eq_on_floor n T s x hxcard
  rw [hint_eq]
  exact seedPot_drift_floorInv n T hT s hs hn c ⟨hcard, hcr⟩

/-- The guarded threshold link: `¬(card = n ∧ SeededB) → 1 ≤ Φ`. -/
theorem seedPotG_link (n T : ℕ) (s : ℝ) (hs : 0 < s) (hn : 20 ≤ n)
    (c : Config (Minute L₀))
    (hnc : ¬ (c.card = n ∧ SeededB (L₀ := L₀) n T c)) :
    1 ≤ seedPotG (L₀ := L₀) n T s c := by
  unfold seedPotG
  by_cases hcard : c.card = n
  · rw [if_pos hcard]
    have hns : ¬ SeededB (L₀ := L₀) n T c := fun h => hnc ⟨hcard, h⟩
    exact not_seededB_imp_seedPot_ge_one n T s hs hn c hns
  · rw [if_neg hcard]; exact le_top

/-- The guarded `Post` is absorbing: `card = n` (kernel-invariant) and
`SeededB n T` (`beyond_ge_monotone`) both persist. -/
theorem seedPostG_absorbing (n T : ℕ) (c c' : Config (Minute L₀))
    (h : c.card = n ∧ SeededB (L₀ := L₀) n T c)
    (hc' : c' ∈ ((clockProto L₀).stepDistOrSelf c).support) :
    c'.card = n ∧ SeededB (L₀ := L₀) n T c' := by
  obtain ⟨hcard, hsd⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Protocol.stepDistOrSelf_support_card_eq (clockProto L₀) c c' hc']; exact hcard
  · exact beyond_ge_monotone (T + 1) (lo n) c c' hsd hc'

/-- The guarded seed potential is bounded by `exp(s·lo n)` on the floor invariant
(the seed deficit `lo n − clampSeed` is at most `lo n`). -/
theorem seedPotG_le_max (n T : ℕ) (s : ℝ) (hs : 0 < s) (c : Config (Minute L₀))
    (hcard : c.card = n) :
    seedPotG (L₀ := L₀) n T s c ≤ ENNReal.ofReal (Real.exp (s * (lo n : ℝ))) := by
  rw [seedPotG_eq_on_floor n T s c hcard]
  unfold seedPot clampSeed
  by_cases hsd : lo n ≤ beyond (T + 1) c
  · rw [if_pos hsd]; positivity
  · rw [if_neg hsd]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hge0 : (0 : ℝ) ≤ ((min (beyond (T + 1) c) (lo n) : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [hs, hge0]

/-- **The seed crossing as a `PhaseConvergence`** (`Pre = seedFloorInv`,
`Post = card = n ∧ SeededB`).  Starting from the seed floor invariant
(`card = n`, minute `T` crossed), `beyond (T+1)` reaches `lo n` within `t`
interactions with failure `≤ ε`, provided the geometric tail
`(rate)ᵗ · exp(log2·lo n) ≤ ε` at `s = log 2` (rate `= 7/8`).  This is the genuine
SEED phase, driven by the drip-advance lower bound. -/
noncomputable def seedPhase (n T : ℕ) (hT : T + 1 ≤ L₀) (hn : 20 ≤ n)
    (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal ((7 / 8 : ℝ)) ^ t *
            ENNReal.ofReal (Real.exp (Real.log 2 * (lo n : ℝ))) / 1
          ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence (clockProto L₀).transitionKernel := by
  have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have he : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]; norm_num
  have hrate : (1 : ℝ) - (1 / 4) * (1 - Real.exp (-Real.log 2)) = 7 / 8 := by
    rw [he]; norm_num
  refine WindowConcentration.windowDrift_PhaseConvergence (clockProto L₀)
    (seedPotG (L₀ := L₀) n T (Real.log 2)) (seedPotG_measurable n T (Real.log 2))
    (seedFloorInv (L₀ := L₀) n T) (seedFloorInv_absorbing n T)
    (ENNReal.ofReal (1 - (1 / 4) * (1 - Real.exp (-Real.log 2))))
    (seedPotG_drift_floorInv n T hT (Real.log 2) hs hn)
    (seedFloorInv (L₀ := L₀) n T)                       -- Pre
    (fun c => c.card = n ∧ SeededB (L₀ := L₀) n T c)    -- Post
    (seedPostG_absorbing n T)                           -- hPost_abs
    1 one_ne_zero ENNReal.one_ne_top                    -- θ = 1
    (seedPotG_link n T (Real.log 2) hs hn)              -- hlink
    (fun c h => h)                                      -- hPre_Q
    (ENNReal.ofReal (Real.exp (Real.log 2 * (lo n : ℝ))))  -- Φ₀
    ?_                                                  -- hPre_bound
    t ε ?_                                              -- hε
  · intro c ⟨hcard, _⟩
    exact seedPotG_le_max n T (Real.log 2) hs c hcard
  · rw [hrate] at *
    exact hε

/-! ## Part C — the card-guarded epidemic (bulk) phase (S1 transported, C2 reused).

We reuse C2's S1-transport `windowPotB`/`windowPotB_drift_floorInv` for the bulk
crossing `beyond (T+1): lo n → hi n`, but card-guard it so that `card = n` flows
through `Post = (card = n ∧ CrossedB n (T+1))` — discharging the chaining.  Note
`floorInvB n (T+1) = (card = n ∧ SeededB n T)`, so `seedPhase.Post` is DEFINITIONALLY
`epidemicPhase.Pre`: the chaining is a genuine identity, not C2's assumed `h_chain`. -/

/-- The card-guarded bulk potential: `⊤` off the `card = n` shell, else C2's
`windowPotB` (the S1-transported window potential on `beyond (T+1)`). -/
noncomputable def bulkPotG (n T : ℕ) (s : ℝ) (c : Config (Minute L₀)) : ℝ≥0∞ :=
  if c.card = n then windowPotB (L₀ := L₀) n (T + 1) s c else ⊤

theorem bulkPotG_measurable (n T : ℕ) (s : ℝ) :
    Measurable (bulkPotG (L₀ := L₀) n T s) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

theorem bulkPotG_eq_on_floor (n T : ℕ) (s : ℝ) (c : Config (Minute L₀))
    (hcard : c.card = n) :
    bulkPotG (L₀ := L₀) n T s c = windowPotB (L₀ := L₀) n (T + 1) s c := by
  unfold bulkPotG; rw [if_pos hcard]

/-- Drift of the guarded bulk potential on `floorInvB n (T+1)`. -/
theorem bulkPotG_drift_floorInv (n T : ℕ) (s : ℝ) (hs : 0 < s) (hn : 20 ≤ n)
    (c : Config (Minute L₀)) (hfl : floorInvB (L₀ := L₀) n (T + 1) c) :
    ∫⁻ c', bulkPotG (L₀ := L₀) n T s c' ∂((clockProto L₀).transitionKernel c) ≤
      ENNReal.ofReal (1 - (1 / 100) * (1 - Real.exp (-s)))
        * bulkPotG (L₀ := L₀) n T s c := by
  have hcard := hfl.1
  rw [bulkPotG_eq_on_floor n T s c hcard]
  have hint_eq : ∫⁻ c', bulkPotG (L₀ := L₀) n T s c' ∂((clockProto L₀).transitionKernel c)
      = ∫⁻ c', windowPotB (L₀ := L₀) n (T + 1) s c' ∂((clockProto L₀).transitionKernel c) := by
    apply lintegral_congr_ae
    change ∀ᵐ c' ∂((clockProto L₀).stepDistOrSelf c).toMeasure,
      bulkPotG (L₀ := L₀) n T s c' = windowPotB (L₀ := L₀) n (T + 1) s c'
    rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    rw [Set.disjoint_left]
    intro x hsupp hbad
    apply hbad
    have hxcard : x.card = n := by
      rw [← hcard]; exact Protocol.stepDistOrSelf_support_card_eq (clockProto L₀) c x hsupp
    exact bulkPotG_eq_on_floor n T s x hxcard
  rw [hint_eq]
  exact windowPotB_drift_floorInv n (T + 1) s hs hn c hfl

/-- The guarded threshold link: `¬(card = n ∧ CrossedB n (T+1)) → 1 ≤ Φ`. -/
theorem bulkPotG_link (n T : ℕ) (s : ℝ) (hs : 0 < s) (hn : 20 ≤ n)
    (c : Config (Minute L₀))
    (hnc : ¬ (c.card = n ∧ CrossedB (L₀ := L₀) n (T + 1) c)) :
    1 ≤ bulkPotG (L₀ := L₀) n T s c := by
  unfold bulkPotG
  by_cases hcard : c.card = n
  · rw [if_pos hcard]
    have hns : ¬ CrossedB (L₀ := L₀) n (T + 1) c := fun h => hnc ⟨hcard, h⟩
    exact not_crossedB_imp_potB_ge_one n (T + 1) s hs hn c hns
  · rw [if_neg hcard]; exact le_top

/-- The guarded bulk `Post` is absorbing. -/
theorem bulkPostG_absorbing (n T : ℕ) (c c' : Config (Minute L₀))
    (h : c.card = n ∧ CrossedB (L₀ := L₀) n (T + 1) c)
    (hc' : c' ∈ ((clockProto L₀).stepDistOrSelf c).support) :
    c'.card = n ∧ CrossedB (L₀ := L₀) n (T + 1) c' := by
  obtain ⟨hcard, hcr⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Protocol.stepDistOrSelf_support_card_eq (clockProto L₀) c c' hc']; exact hcard
  · exact beyond_ge_monotone (T + 1) (hi n) c c' hcr hc'

/-- The guarded bulk potential is bounded by `exp(s·(hi − lo))` on `Pre`
(`floorInvB n (T+1)`: `beyond (T+1) ≥ lo n`, so the deficit `hi − clampB ≤ hi − lo`). -/
theorem bulkPotG_le_max (n T : ℕ) (s : ℝ) (hs : 0 < s) (hn : 20 ≤ n)
    (c : Config (Minute L₀)) (hfl : floorInvB (L₀ := L₀) n (T + 1) c) :
    bulkPotG (L₀ := L₀) n T s c ≤
      ENNReal.ofReal (Real.exp (s * ((hi n : ℝ) - (lo n : ℝ)))) := by
  obtain ⟨hcard, hfloor⟩ := hfl
  rw [bulkPotG_eq_on_floor n T s c hcard]
  unfold windowPotB
  by_cases hcross : hi n ≤ beyond (T + 1) c
  · rw [if_pos hcross]; positivity
  · rw [if_neg hcross]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    rw [clampB_eq_of_floor n (T + 1) c hfloor]
    have hge : (lo n : ℝ) ≤ ((min (beyond (T + 1) c) (hi n) : ℕ) : ℝ) := by
      have : lo n ≤ min (beyond (T + 1) c) (hi n) := by
        have := lo_lt_hi n hn; omega
      exact_mod_cast this
    nlinarith [hs, hge]

/-- **The bulk crossing as a `PhaseConvergence`** (`Pre = floorInvB n (T+1)`,
`Post = card = n ∧ CrossedB n (T+1)`).  The S1-transported constant-density bulk
crosses `beyond (T+1): lo n → hi n` in `t` interactions with failure `≤ ε`, at
rate `199/200` (`s = log 2`).  This REUSES C2's keystone `windowPotB` honestly.
Crucially `Pre = (card = n ∧ lo n ≤ beyond (T+1))` is DEFINITIONALLY
`seedPhase.Post`, so the seed→bulk chaining is genuine. -/
noncomputable def epidemicPhase (n T : ℕ) (hn : 20 ≤ n) (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal ((199 / 200 : ℝ)) ^ t *
            ENNReal.ofReal (Real.exp (Real.log 2 * ((hi n : ℝ) - (lo n : ℝ)))) / 1
          ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence (clockProto L₀).transitionKernel := by
  have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have he : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]; norm_num
  have hrate : (1 : ℝ) - (1 / 100) * (1 - Real.exp (-Real.log 2)) = 199 / 200 := by
    rw [he]; norm_num
  refine WindowConcentration.windowDrift_PhaseConvergence (clockProto L₀)
    (bulkPotG (L₀ := L₀) n T (Real.log 2)) (bulkPotG_measurable n T (Real.log 2))
    (floorInvB (L₀ := L₀) n (T + 1)) (floorInvariantB_absorbing n (T + 1))
    (ENNReal.ofReal (1 - (1 / 100) * (1 - Real.exp (-Real.log 2))))
    (bulkPotG_drift_floorInv n T (Real.log 2) hs hn)
    (floorInvB (L₀ := L₀) n (T + 1))                        -- Pre
    (fun c => c.card = n ∧ CrossedB (L₀ := L₀) n (T + 1) c) -- Post
    (bulkPostG_absorbing n T)                               -- hPost_abs
    1 one_ne_zero ENNReal.one_ne_top                        -- θ = 1
    (bulkPotG_link n T (Real.log 2) hs hn)                  -- hlink
    (fun c h => h)                                          -- hPre_Q
    (ENNReal.ofReal (Real.exp (Real.log 2 * ((hi n : ℝ) - (lo n : ℝ)))))  -- Φ₀
    (bulkPotG_le_max n T (Real.log 2) hs hn)                -- hPre_bound
    t ε ?_                                                  -- hε
  · rw [hrate] at *
    exact hε

/-! ## Part D — `clock_step_upper`: the FAITHFUL O(1)-per-minute upper bound.

This is the headline (Lemma 6.4): from minute `T` crossed, minute `T+1` crosses
within `O(n)` interactions (= O(1) parallel) with `1/poly` failure, by GENUINELY
chaining `seedPhase` then `epidemicPhase` via `compose_two_phases`.  The chaining
`seedPhase.Post → epidemicPhase.Pre` is `(card = n ∧ SeededB n T) → floorInvB n
(T+1)`, a DEFINITIONAL identity (`SeededB n T = (lo n ≤ beyond (T+1))`) — NOT C2's
assumed `h_chain`. -/

/-- **`clock_step_upper` (Lemma 6.4) — the faithful O(1)-per-minute upper bound.**

From minute `T` crossed (`seedFloorInv n T = card = n ∧ hi n ≤ beyond T`), within
`tseed + tbulk` interactions minute `T+1` is crossed
(`card = n ∧ CrossedB n (T+1)`) with failure `≤ εseed + εbulk`.  The proof
composes `seedPhase` (SEED, drip-driven `0 → lo n`) and `epidemicPhase`
(EPIDEMIC, S1 bulk `lo n → hi n`) via `compose_two_phases`, with the chaining
GENUINELY discharged (`seed_bulk_chain`).  Taking `tseed = tbulk = O(n)` gives
`O(1)` parallel per minute. -/
theorem clock_step_upper (n T : ℕ) (hT : T + 1 ≤ L₀) (hn : 20 ≤ n)
    (tseed tbulk : ℕ) (εseed εbulk : ℝ≥0)
    (hεs : ENNReal.ofReal ((7 / 8 : ℝ)) ^ tseed *
            ENNReal.ofReal (Real.exp (Real.log 2 * (lo n : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (hεb : ENNReal.ofReal ((199 / 200 : ℝ)) ^ tbulk *
            ENNReal.ofReal (Real.exp (Real.log 2 * ((hi n : ℝ) - (lo n : ℝ)))) / 1
              ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (Minute L₀)) (hc₀ : seedFloorInv (L₀ := L₀) n T c₀) :
    ((clockProto L₀).transitionKernel ^ (tseed + tbulk)) c₀
        {c | ¬ (c.card = n ∧ CrossedB (L₀ := L₀) n (T + 1) c)} ≤
      (εseed + εbulk : ℝ≥0∞) := by
  have hchain : ∀ x, (seedPhase (L₀ := L₀) n T hT hn tseed εseed hεs).Post x →
      (epidemicPhase (L₀ := L₀) n T hn tbulk εbulk hεb).Pre x := by
    intro x hx; exact hx
  have hcompose := compose_two_phases
    (seedPhase (L₀ := L₀) n T hT hn tseed εseed hεs)
    (epidemicPhase (L₀ := L₀) n T hn tbulk εbulk hεb)
    hchain c₀ hc₀
  exact hcompose

/-! ## Part E — `clock_faithful_O_log_n_upper`: composing minutes to O(log n).

We package one `seedPhase ++ epidemicPhase` per minute as a single
`PhaseConvergence` (`minutePhase`), whose `Pre = seedFloorInv n i` and
`Post = card = n ∧ CrossedB n (i+1)`.  The cross-MINUTE chaining
`minutePhase i.Post → minutePhase (i+1).Pre` is
`(card = n ∧ CrossedB n (i+1)) → seedFloorInv n (i+1)`, a DEFINITIONAL identity
(`seedFloorInv n (i+1) = card = n ∧ CrossedB n (i+1)`) — the genuine discharge of
C2's assumed `h_chain`.  Composing over `m = k·L = Θ(log n)` minutes via
`compose_n_phases` gives total interactions `m·(tseed + tbulk) = O(n·log n)` =
`O(log n)` parallel, failure `≤ m·(εseed + εbulk) = 1/poly`. -/

/-- **The combined per-minute phase** (`Pre = seedFloorInv n T`,
`Post = card = n ∧ CrossedB n (T+1)`), the genuine seed+bulk composition.  Its
`t = tseed + tbulk = O(n)` interactions (= O(1) parallel), its `ε = εseed + εbulk`
the per-minute failure. -/
noncomputable def minutePhase (n T : ℕ) (hT : T + 1 ≤ L₀) (hn : 20 ≤ n)
    (tseed tbulk : ℕ) (εseed εbulk : ℝ≥0)
    (hεs : ENNReal.ofReal ((7 / 8 : ℝ)) ^ tseed *
            ENNReal.ofReal (Real.exp (Real.log 2 * (lo n : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (hεb : ENNReal.ofReal ((199 / 200 : ℝ)) ^ tbulk *
            ENNReal.ofReal (Real.exp (Real.log 2 * ((hi n : ℝ) - (lo n : ℝ)))) / 1
              ≤ (εbulk : ℝ≥0∞)) :
    PhaseConvergence (clockProto L₀).transitionKernel where
  Pre := seedFloorInv (L₀ := L₀) n T
  Post := fun c => c.card = n ∧ CrossedB (L₀ := L₀) n (T + 1) c
  t := tseed + tbulk
  ε := εseed + εbulk
  post_absorbing := by
    intro c hc
    change ((clockProto L₀).stepDistOrSelf c).toMeasure
      {c' | c'.card = n ∧ CrossedB (L₀ := L₀) n (T + 1) c'} = 1
    rw [(((clockProto L₀).stepDistOrSelf c)).toMeasure_apply_eq_one_iff
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    intro c' hc'
    exact bulkPostG_absorbing n T c c' hc hc'
  convergence := by
    intro c₀ hPre
    exact clock_step_upper n T hT hn tseed tbulk εseed εbulk hεs hεb c₀ hPre

/-- **The minute-phase family** for `m` minutes over a population of `n` agents,
using a uniform per-minute budget `(tseed, tbulk, εseed, εbulk)`.  Minute `i` is
`minutePhase n i`, requiring `i + 1 ≤ L₀` (`hML : m ≤ L₀`). -/
noncomputable def minutePhases (n m : ℕ) (hML : m ≤ L₀) (hn : 20 ≤ n)
    (tseed tbulk : ℕ) (εseed εbulk : ℝ≥0)
    (hεs : ENNReal.ofReal ((7 / 8 : ℝ)) ^ tseed *
            ENNReal.ofReal (Real.exp (Real.log 2 * (lo n : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (hεb : ENNReal.ofReal ((199 / 200 : ℝ)) ^ tbulk *
            ENNReal.ofReal (Real.exp (Real.log 2 * ((hi n : ℝ) - (lo n : ℝ)))) / 1
              ≤ (εbulk : ℝ≥0∞)) :
    Fin m → PhaseConvergence (clockProto L₀).transitionKernel :=
  fun i => minutePhase (L₀ := L₀) n i.val (by omega) hn tseed tbulk εseed εbulk hεs hεb

/-- **`clock_faithful_O_log_n_upper` — the FAITHFUL O(log n) clock upper bound.**

Composing the per-minute engine `minutePhase` over `m = k·L = Θ(log n)` minute
levels, starting from minute `0` crossed (`seedFloorInv n 0`), the top minute `m`
is crossed (`card = n ∧ CrossedB n m`) within `m·(tseed + tbulk) = O(n·log n)`
interactions (= O(log n) parallel) with failure `≤ m·(εseed + εbulk) = 1/poly`.

The cross-minute chaining `minutePhase i.Post → minutePhase (i+1).Pre` is the
DEFINITIONAL identity `(card = n ∧ CrossedB n (i+1)) → seedFloorInv n (i+1)`
(`seedFloorInv n (i+1) = card = n ∧ CrossedB n (i+1)`) — GENUINELY discharged,
replacing C2's assumed `h_chain`.  This is the faithful upgrade of the proven
`Θ(log² n)` (`ClockTime.clock_composed_via_A0`). -/
theorem clock_faithful_O_log_n_upper (n m : ℕ) (hm : m > 0) (hML : m ≤ L₀)
    (hn : 20 ≤ n) (tseed tbulk : ℕ) (εseed εbulk : ℝ≥0)
    (hεs : ENNReal.ofReal ((7 / 8 : ℝ)) ^ tseed *
            ENNReal.ofReal (Real.exp (Real.log 2 * (lo n : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (hεb : ENNReal.ofReal ((199 / 200 : ℝ)) ^ tbulk *
            ENNReal.ofReal (Real.exp (Real.log 2 * ((hi n : ℝ) - (lo n : ℝ)))) / 1
              ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (Minute L₀)) (hx₀ : seedFloorInv (L₀ := L₀) n 0 c₀) :
    ((clockProto L₀).transitionKernel ^
        (∑ _i : Fin m, (tseed + tbulk))) c₀
        {y | ¬ (y.card = n ∧ CrossedB (L₀ := L₀) n m y)} ≤
      (∑ _i : Fin m, ((εseed + εbulk : ℝ≥0) : ℝ≥0∞)) := by
  classical
  set phases := minutePhases (L₀ := L₀) n m hML hn tseed tbulk εseed εbulk hεs hεb
    with hphases
  -- the cross-minute chaining: minutePhase i.Post = seedFloorInv n (i+1) = minutePhase (i+1).Pre.
  have h_chain : ∀ (i : Fin m) (hi : i.val + 1 < m),
      ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x := by
    intro i hi x hx
    -- (phases i).Post x = (card = n ∧ CrossedB n (i+1) x)
    -- (phases ⟨i+1⟩).Pre x = seedFloorInv n (i+1) x = (card = n ∧ CrossedB n (i+1) x)
    exact hx
  -- the start: seedFloorInv n 0 = (phases ⟨0⟩).Pre.
  have hx₀' : (phases ⟨0, hm⟩).Pre c₀ := hx₀
  have hcomp := compose_n_phases (K := (clockProto L₀).transitionKernel) hm phases
    h_chain c₀ hx₀'
  -- rewrite the time sum, the failure sum, and the final Post to closed forms.
  have ht_eq : (∑ i : Fin m, (phases i).t) = ∑ _i : Fin m, (tseed + tbulk) := by
    apply Finset.sum_congr rfl; intro i _; rfl
  have hε_eq : (∑ i : Fin m, ((phases i).ε : ℝ≥0∞))
      = ∑ _i : Fin m, ((εseed + εbulk : ℝ≥0) : ℝ≥0∞) := by
    apply Finset.sum_congr rfl; intro i _; rfl
  have hpost_eq : {y : Config (Minute L₀) | ¬ (phases ⟨m - 1, by omega⟩).Post y}
      = {y | ¬ (y.card = n ∧ CrossedB (L₀ := L₀) n m y)} := by
    apply Set.ext; intro y
    simp only [Set.mem_setOf_eq, not_iff_not]
    -- (phases ⟨m-1⟩).Post y = (card = n ∧ CrossedB n ((m-1)+1) y); (m-1)+1 = m.
    have hmm : (m - 1) + 1 = m := by omega
    constructor
    · intro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; rw [← hmm]; exact h2
    · intro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; rw [hmm]; exact h2
  rw [ht_eq, hε_eq, hpost_eq] at hcomp
  exact hcomp

/-! ## Part F — the O(log n) parallel-time arithmetic.

The composed interaction count is `m·(tseed + tbulk)`.  With `tseed = tbulk = O(n)`
(the per-minute O(1) parallel budget) and `m = k·L = Θ(log n)`, the parallel time
`m·(tseed + tbulk)/n = O(m) = O(log n)` — the headline upgrade over `Θ(log² n)`. -/

/-- The composed interaction count is `m·(tseed + tbulk)`. -/
theorem composed_time_eq (m tseed tbulk : ℕ) :
    (∑ _i : Fin m, (tseed + tbulk)) = m * (tseed + tbulk) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The composed failure probability is `≤ m·(εseed + εbulk)`. -/
theorem composed_failure_eq (m : ℕ) (εseed εbulk : ℝ≥0) :
    (∑ _i : Fin m, ((εseed + εbulk : ℝ≥0) : ℝ≥0∞)) = (m : ℝ≥0∞) * (εseed + εbulk : ℝ≥0) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The O(log n)-parallel clock (the headline arithmetic).**  With a per-minute
budget `tseed + tbulk ≤ C·n` (= O(1) parallel) and `m = k·L` minutes, the total
parallel time `m·(tseed + tbulk)/n ≤ k·L·C` is `O(L) = O(log n)` (since
`L = ⌈log₂ n⌉`).  This is `clock_faithful_O_log_n_upper`'s interaction count
divided by `n`, the faithful upgrade of the proven `Θ(log² n)`. -/
theorem clock_parallel_O_log_n (k L n C tseed tbulk : ℕ) (hn : 1 ≤ n)
    (hbudget : tseed + tbulk ≤ C * n) :
    (((k * L) * (tseed + tbulk) : ℕ) : ℝ) / n ≤ (k : ℝ) * L * C := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hnpos]
  have hb : ((tseed + tbulk : ℕ) : ℝ) ≤ (C : ℝ) * n := by
    have : ((tseed + tbulk : ℕ) : ℝ) ≤ ((C * n : ℕ) : ℝ) := by exact_mod_cast hbudget
    rwa [Nat.cast_mul] at this
  calc (((k * L) * (tseed + tbulk) : ℕ) : ℝ)
      = ((k * L : ℕ) : ℝ) * ((tseed + tbulk : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((k * L : ℕ) : ℝ) * ((C : ℝ) * n) := by
        apply mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (k : ℝ) * L * C * n := by push_cast; ring

/-! ## HONEST STATUS — Avenue C3 (faithful clock O(log n) upper bound)

C3 is COMPLETE at the kernel level for the **upper time bound** (Lemma 6.4 — the
headline O(log n) source), 0-sorry / 0-axiom (only `propext`, `Classical.choice`,
`Quot.sound`).  Unlike C2, the cross-minute chaining is GENUINELY DISCHARGED, not
assumed:

* **The SEED is genuine.**  `clock_drip_seed_advance_prob` is a LOWER bound on the
  drip-seed advance probability, proven from first principles (singleton-mass of
  the same-state pair `(s_i, s_i)`, the dual of C2's `clock_beyond_advance_prob`).
  `drip_advance_prob_ge` then shows that once minute `i` is crossed
  (`count s_i = beyond i − beyond (i+1) ≥ hi n − lo n ≥ 0.7 n`,
  `count_frontState_eq`), the drip-seed fires with probability `≥ 1/4`.
  `seedPot_contracts_on_floor` packages this into the window contraction crossing
  the seed `0 → lo n` in `O(n)` interactions; `seedPhase` is the resulting
  `PhaseConvergence`.

* **The EPIDEMIC is S1, honestly reused.**  `epidemicPhase` wraps C2's
  S1-transport `windowPotB` / `windowPotB_drift_floorInv` (the constant-density
  bulk crossing `lo n → hi n`), card-guarded so `card = n` flows through `Post`.

* **The chaining is a DEFINITIONAL IDENTITY, not C2's `h_chain`.**  In
  `clock_step_upper`, `seedPhase.Post = (card = n ∧ SeededB n i)` is
  definitionally `epidemicPhase.Pre = floorInvB n (i+1)` (since
  `SeededB n i = (lo n ≤ beyond (i+1))`); the chaining is `fun x hx => hx`.  In
  `clock_faithful_O_log_n_upper`, `minutePhase i.Post = (card = n ∧ CrossedB n
  (i+1))` is definitionally `minutePhase (i+1).Pre = seedFloorInv n (i+1)`; again
  `fun x hx => hx`.  No front-cap `B` and no cross-minute `h_chain` are assumed —
  the C2 flaw is fixed.

* **The O(log n) headline.**  `clock_faithful_O_log_n_upper` composes `m = k·L =
  Θ(log n)` minutes; the total interaction count is `m·(tseed + tbulk)`
  (`composed_time_eq`), and with `tseed + tbulk = O(n)` the parallel time
  `m·(tseed + tbulk)/n = O(k·L) = O(log n)` (`clock_parallel_O_log_n`), failure
  `≤ m·(εseed + εbulk) = 1/poly` (`composed_failure_eq`).  Per the extended
  consult, this upper bound does NOT use the front-shape / early-drip analysis
  (S2b/S3); those are for the LOWER bound + hour-sync, a separate sub-avenue
  deferred here.

The clock's O(log n)-parallel UPPER time bound (the time-half headline of the
paper's Theorem 3.1) is now FAITHFUL at the kernel level. -/
theorem clock_faithful_upper_status : True := trivial

end ClockFaithful

end ExactMajority
