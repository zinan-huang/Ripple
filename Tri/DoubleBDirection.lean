/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBTrace
import Tri.DoubleBResolution

/-!
# The event-indexed direction supermartingale (Theorem 2)

The Double-B level `2x+b` only moves at *resolution* events (`xb`, `yb`); between
them the raw chain is flat, so no raw-time contraction exists (at `b=0` nothing
resolves).  We therefore track level *and* the resolution counter jointly through
the two-parameter potential `Θ(q) = w^{doubleLevel} · η^{resolve}`.

With the direction optimum `η(u+w²)=w(u+1)` and `w ≤ η` (so `η ≥ 1` exactly when
`u < w < 1`, the strong-majority regime), `Θ` is a genuine one-step
supermartingale — the resolution bias `down ≤ up·u` is spent as decay per
resolution.  Markov on `Θ` (next file) then yields `w^{L₀−thr}·η^{−M}`, an
exponential tail in the number of resolutions, with no time-change coupling.
-/

namespace Tri
open scoped ENNReal

/-- **Trace expectation expansion tracking level AND resolve.** -/
theorem doubleTraceStep_expect (n : ℕ) (hn : 2 ≤ n) (q : DoubleTrace n) (a : ℕ)
    (ha : q.cfg.1.doubleLevel = a + 1) (G : ℕ → ℕ → ℝ≥0∞) :
    expect (doubleTraceStep n hn q) (fun q' => G q'.cfg.1.doubleLevel q'.resolve)
      = doubleResolveDown q.cfg * G a (q.resolve + 1)
        + doubleNeutralMass hn q.cfg * G (a + 1) q.resolve
        + doubleResolveUp q.cfg * G (a + 2) (q.resolve + 1) := by
  set s := q.cfg with hs
  set r := q.resolve with hr
  have hh : 2 ≤ s.1.x + s.1.y + s.1.b := by
    have := s.2; simp only [BiCfg.DoubleInv] at this; omega
  have hpop : s.1.x + s.1.y + s.1.b = n := s.2
  have hup : dbPairPMF s.1.x s.1.y s.1.b hh .xb = doubleResolveUp s := by
    unfold doubleResolveUp
    rw [show dbPairPMF s.1.x s.1.y s.1.b hh PairComp.xb
        = ((PairComp.weight s.1.x s.1.y s.1.b PairComp.xb : ℕ):ℝ≥0∞)
          /(Nat.choose (s.1.x+s.1.y+s.1.b) 2:ℝ≥0∞) from rfl, hpop]
    simp [PairComp.weight]
  have hdown : dbPairPMF s.1.x s.1.y s.1.b hh .yb = doubleResolveDown s := by
    unfold doubleResolveDown
    rw [show dbPairPMF s.1.x s.1.y s.1.b hh PairComp.yb
        = ((PairComp.weight s.1.x s.1.y s.1.b PairComp.yb : ℕ):ℝ≥0∞)
          /(Nat.choose (s.1.x+s.1.y+s.1.b) 2:ℝ≥0∞) from rfl, hpop]
    simp [PairComp.weight]
  have key : ∀ k : PairComp,
      dbPairPMF s.1.x s.1.y s.1.b hh k
        * G ((PairComp.nextDoubleTrace q k).cfg.1.doubleLevel)
            (PairComp.nextDoubleTrace q k).resolve
      = dbPairPMF s.1.x s.1.y s.1.b hh k
        * G ((PairComp.next s.1 k).doubleLevel) (r + k.resolveInc) := by
    intro k
    by_cases hw : PairComp.weight s.1.x s.1.y s.1.b k = 0
    · rw [dbPairPMF_zero_of_weight_zero hw]; simp
    · rw [nextTrace_resolve n q k (by rw [← hs]; exact hw),
        nextTrace_cfg n q k (by rw [← hs]; exact hw)]
  -- fold up/down/xy masses (with weight-zero guard for the raw level)
  have hxbT : dbPairPMF s.1.x s.1.y s.1.b hh .xb
        * G ((PairComp.next s.1 .xb).doubleLevel) (r + PairComp.resolveInc .xb)
      = doubleResolveUp s * G (a + 2) (r + 1) := by
    by_cases hw : s.1.x * s.1.b = 0
    · rw [dbPairPMF_zero_of_weight_zero (by simpa [PairComp.weight] using hw)]
      have h0 : doubleResolveUp s = 0 := by unfold doubleResolveUp; rw [hw]; simp
      rw [h0]; simp
    · have hlev : (PairComp.next s.1 .xb).doubleLevel = a + 2 := by
        have h := nextDS_level_xb n s a ha hw
        rwa [PairComp.nextDoubleState,
          dif_neg (show PairComp.weight s.1.x s.1.y s.1.b PairComp.xb ≠ 0 by
            simpa [PairComp.weight] using hw)] at h
      rw [hlev, hup]; rfl
  have hybT : dbPairPMF s.1.x s.1.y s.1.b hh .yb
        * G ((PairComp.next s.1 .yb).doubleLevel) (r + PairComp.resolveInc .yb)
      = doubleResolveDown s * G a (r + 1) := by
    by_cases hw : s.1.y * s.1.b = 0
    · rw [dbPairPMF_zero_of_weight_zero (by simpa [PairComp.weight] using hw)]
      have h0 : doubleResolveDown s = 0 := by unfold doubleResolveDown; rw [hw]; simp
      rw [h0]; simp
    · have hlev : (PairComp.next s.1 .yb).doubleLevel = a := by
        have h := nextDS_level_yb n s a ha hw
        rw [PairComp.nextDoubleState,
          dif_neg (show PairComp.weight s.1.x s.1.y s.1.b PairComp.yb ≠ 0 by
            simpa [PairComp.weight] using hw)] at h
        replace h : (PairComp.next s.1 .yb).doubleLevel + 1 = a + 1 := h
        omega
      rw [hlev, hdown]; rfl
  have hxyT : dbPairPMF s.1.x s.1.y s.1.b hh .xy
        * G ((PairComp.next s.1 .xy).doubleLevel) (r + PairComp.resolveInc .xy)
      = dbPairPMF s.1.x s.1.y s.1.b hh .xy * G (a + 1) r := by
    by_cases hw : s.1.x * s.1.y = 0
    · rw [dbPairPMF_zero_of_weight_zero (by simpa [PairComp.weight] using hw)]; simp
    · have hlev : (PairComp.next s.1 .xy).doubleLevel = a + 1 := by
        have h := nextDS_level_xy n s a ha
        rwa [PairComp.nextDoubleState,
          dif_neg (show PairComp.weight s.1.x s.1.y s.1.b PairComp.xy ≠ 0 by
            simpa [PairComp.weight] using hw)] at h
      rw [hlev]; simp [PairComp.resolveInc]
  unfold doubleTraceStep
  rw [expect_map]; unfold expect; rw [tsum_fintype]; simp only []
  rw [show (Finset.univ : Finset PairComp)
      = {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb, PairComp.yb, PairComp.bb} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [key .xx, key .xy, key .yy, key .xb, key .yb, key .bb]
  -- inert labels: next = s, level = a+1 (defeq via ha); resolveInc = 0
  have hix : (PairComp.next s.1 .xx).doubleLevel = a + 1 := ha
  have hiy : (PairComp.next s.1 .yy).doubleLevel = a + 1 := ha
  have hib : (PairComp.next s.1 .bb).doubleLevel = a + 1 := ha
  rw [hix, hiy, hib, hxbT, hybT, hxyT]
  simp only [PairComp.resolveInc, Nat.add_zero]
  unfold doubleNeutralMass
  ring



/-- Scalar supermartingale core (over ℝ≥0∞ via `toReal`): with the direction
optimum `η(u+w²)=w(u+1)` and `w ≤ η`, the one-resolution factor does not exceed
`w`.  Identity: `w − (neu·w+η(dn+up·w²)) = (u·up−dn)(η−w) ≥ 0`. -/
theorem doubleDir_scalar (dn neu up u w η : ℝ≥0∞)
    (hsum : dn + neu + up = 1) (hdle : dn ≤ up * u) (hrel : η * (u + w ^ 2) = w * (u + 1))
    (hwη : w ≤ η)
    (hdt : dn ≠ ⊤) (hnt : neu ≠ ⊤) (hut : up ≠ ⊤) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤)
    (huT : u ≠ ⊤) :
    neu * w + η * (dn + up * w ^ 2) ≤ w := by
  rw [← ENNReal.toReal_le_toReal (by finiteness) hwt]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_add hdt (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_pow]
  have hsumR : dn.toReal + neu.toReal + up.toReal = 1 := by
    have := congrArg ENNReal.toReal hsum
    rwa [ENNReal.toReal_add (by finiteness) hut, ENNReal.toReal_add hdt hnt,
      ENNReal.toReal_one] at this
  have hdleR : dn.toReal ≤ up.toReal * u.toReal := by
    rw [← ENNReal.toReal_mul]; exact (ENNReal.toReal_le_toReal hdt (by finiteness)).mpr hdle
  have hrelR : η.toReal * (u.toReal + w.toReal ^ 2) = w.toReal * (u.toReal + 1) := by
    have := congrArg ENNReal.toReal hrel
    rwa [ENNReal.toReal_mul, ENNReal.toReal_add huT (by finiteness), ENNReal.toReal_pow,
      ENNReal.toReal_mul, ENNReal.toReal_add huT ENNReal.one_ne_top, ENNReal.toReal_one] at this
  have hwηR : w.toReal ≤ η.toReal := (ENNReal.toReal_le_toReal hwt hηt).mpr hwη
  have hprod : 0 ≤ (u.toReal * up.toReal - dn.toReal) * (η.toReal - w.toReal) :=
    mul_nonneg (by nlinarith [hdleR]) (by linarith)
  have hkey : up.toReal * (η.toReal * (u.toReal + w.toReal ^ 2))
      = up.toReal * (w.toReal * (u.toReal + 1)) := by rw [hrelR]
  have hneu : neu.toReal = 1 - dn.toReal - up.toReal := by linarith
  rw [hneu]
  nlinarith [hprod, hkey]


/-- The event-indexed direction potential on the counted trace:
`w^doubleLevel · η^resolve`. -/
noncomputable def doubleTheta (w η : ℝ≥0∞) {n : ℕ} (q : DoubleTrace n) : ℝ≥0∞ :=
  w ^ q.cfg.1.doubleLevel * η ^ q.resolve

/-- **Event-indexed direction supermartingale (one step).** With the direction
optimum `η(u+w²)=w(u+1)` and `w ≤ η`, the potential `w^level·η^resolve` does not
increase in expectation across one counted step in the live band. -/
theorem traceStep_theta_super (n : ℕ) (hn : 2 ≤ n) (q : DoubleTrace n) (a : ℕ)
    (ha : q.cfg.1.doubleLevel = a + 1) (w η u : ℝ≥0∞)
    (hdle : doubleResolveDown q.cfg ≤ doubleResolveUp q.cfg * u)
    (hsum : doubleResolveDown q.cfg + doubleNeutralMass hn q.cfg + doubleResolveUp q.cfg = 1)
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hdt : doubleResolveDown q.cfg ≠ ⊤) (hnt : doubleNeutralMass hn q.cfg ≠ ⊤)
    (hut : doubleResolveUp q.cfg ≠ ⊤) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤) (huT : u ≠ ⊤) :
    expect (doubleTraceStep n hn q) (doubleTheta w η) ≤ doubleTheta w η q := by
  set dn := doubleResolveDown q.cfg
  set neu := doubleNeutralMass hn q.cfg
  set up := doubleResolveUp q.cfg
  have hexp : expect (doubleTraceStep n hn q) (doubleTheta w η)
      = dn * (w ^ a * η ^ (q.resolve + 1)) + neu * (w ^ (a + 1) * η ^ q.resolve)
        + up * (w ^ (a + 2) * η ^ (q.resolve + 1)) := by
    have := doubleTraceStep_expect n hn q a ha (fun L ρ => w ^ L * η ^ ρ)
    simpa [doubleTheta] using this
  rw [hexp]
  have hscalar : neu * w + η * (dn + up * w ^ 2) ≤ w :=
    doubleDir_scalar dn neu up u w η hsum hdle hrel hwη hdt hnt hut hwt hηt huT
  have hL : dn * (w ^ a * η ^ (q.resolve + 1)) + neu * (w ^ (a + 1) * η ^ q.resolve)
        + up * (w ^ (a + 2) * η ^ (q.resolve + 1))
      = (w ^ a * η ^ q.resolve) * (neu * w + η * (dn + up * w ^ 2)) := by ring
  have hR : doubleTheta w η q = (w ^ a * η ^ q.resolve) * w := by
    simp only [doubleTheta, ha]; ring
  rw [hL, hR]
  gcongr



/-- The frozen event-indexed direction chain: run the counted trace while the
level stays above `aLo`, freeze once it drops to `aLo` (ruin, handled
separately). -/
noncomputable def doubleDirStop (n : ℕ) (hn : 2 ≤ n) (aLo : ℕ) (q : DoubleTrace n) :
    PMF (DoubleTrace n) :=
  if aLo + 1 ≤ q.cfg.1.doubleLevel then doubleTraceStep n hn q else PMF.pure q

/-- **Uniform** event-indexed supermartingale for the frozen chain: `Θ` does not
increase in expectation at any state (drift in the live band, equality when
frozen). -/
theorem doubleDirStop_super (n : ℕ) (hn : 2 ≤ n) (aLo bHi : ℕ)
    (haLo : 0 < aLo) (hmaj : bHi ≤ aLo) (heq : aLo + bHi = 2 * n)
    (w η u : ℝ≥0∞) (hu : u = (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hwt : w ≠ ⊤) (hηt : η ≠ ⊤) :
    ∀ q, expect (doubleDirStop n hn aLo q) (doubleTheta w η) ≤ 1 * doubleTheta w η q := by
  intro q
  rw [one_mul]
  unfold doubleDirStop
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

/-- **The event-indexed direction tail bound.**  Starting from a fresh trace
(`resolve = 0`) at level `L₀`, the mass that after `T` frozen steps has both a low
level (`≤ thr`) and many resolutions (`≥ M`) is at most `w^{L₀} / (w^{thr}·η^M)` —
exponentially small in `M` when `η > 1` (the strong-majority regime). -/
theorem doubleDirStop_tail (n : ℕ) (hn : 2 ≤ n) (aLo bHi thr M T : ℕ)
    (haLo : 0 < aLo) (hmaj : bHi ≤ aLo) (heq : aLo + bHi = 2 * n)
    (w η u : ℝ≥0∞) (hu : u = (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (q₀ : DoubleTrace n) (hr0 : q₀.resolve = 0) :
    ∑' q, (if q.cfg.1.doubleLevel ≤ thr ∧ M ≤ q.resolve then
        iter (doubleDirStop n hn aLo) T q₀ q else 0)
      ≤ w ^ q₀.cfg.1.doubleLevel / (w ^ thr * η ^ M) := by
  have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  set θ : ℝ≥0∞ := w ^ thr * η ^ M with hθdef
  have hθ0 : θ ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ hw0)
    exact pow_ne_zero _ (by rintro rfl; simp at hη1)
  have hθtop : θ ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top hwt) (ENNReal.pow_ne_top hηt)
  have hsub : ∀ q,
      (if q.cfg.1.doubleLevel ≤ thr ∧ M ≤ q.resolve then
        iter (doubleDirStop n hn aLo) T q₀ q else 0)
      ≤ (if θ ≤ doubleTheta w η q then iter (doubleDirStop n hn aLo) T q₀ q else 0) := by
    intro q
    by_cases hq : q.cfg.1.doubleLevel ≤ thr ∧ M ≤ q.resolve
    · have hle : θ ≤ doubleTheta w η q := by
        rw [hθdef, doubleTheta]
        exact mul_le_mul' (pow_le_pow_right_of_le_one' hw1 hq.1)
          (pow_le_pow_right₀ hη1 hq.2)
      simp [hq, hle]
    · simp [hq]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans (markov_div (iter (doubleDirStop n hn aLo) T q₀)
    (doubleTheta w η) θ hθ0 hθtop) ?_
  have hiter := expect_iter_le (doubleDirStop n hn aLo) (doubleTheta w η) 1
    (doubleDirStop_super n hn aLo bHi haLo hmaj heq w η u hu hrel hwη hwt hηt) T q₀
  have hΘ0 : doubleTheta w η q₀ = w ^ q₀.cfg.1.doubleLevel := by
    simp [doubleTheta, hr0]
  rw [one_pow, one_mul, hΘ0] at hiter
  exact ENNReal.div_le_div_right hiter θ

end Tri
