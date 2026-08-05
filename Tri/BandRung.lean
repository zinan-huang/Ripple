/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ProdBound

/-!
# A productive-count rung stopped at both phase boundaries

The one-sided kernel in `Tri.Rung` cannot use the phase-1 productive-mass
constant all the way to consensus.  This module stops the `X`-coordinate at
both ends of the open band `aLo < x` and `x < aHi`.  The scalar `bandChain`
has genuinely absorbing boundary states.  Its counted lift `bandCount` keeps
the stopped `X`-coordinate fixed but advances the auxiliary counter; as in
`rungCount`, those artificial increments make the global deadline
supermartingale valid and cannot erase a lower-boundary failure.

The main theorem `band_rung_bound` discharges its productive-mass premise with
`hprod_phase1`, at the concrete constant `21 / 64`.  The transfer theorem is
deliberately limited to targets strictly inside the open band: freezing can
only increase failure mass for such a target.  An upper-boundary hitting event
is not such a target and therefore cannot be transferred to an exact-time
claim about the original chain without an additional return-probability bound.

The final direction theorem records the remaining probabilistic obligation
honestly.  A large total productive count does not determine how many of those
reactions pointed upward.
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

/-- The base Tri chain frozen outside the open band `aLo < x < aHi`.
Both boundary regions are absorbing. -/
noncomputable def bandChain (n aLo aHi : ℕ) : ℕ → PMF ℕ :=
  freeze (fun x : ℕ => x ≤ aLo ∨ aHi ≤ x) (triChain n)

/-- The productive-count lift stopped in its first coordinate outside the open
band.  At a stopped state the artificial counter increment supplies the
deadline contraction while the `X`-coordinate remains absorbed. -/
noncomputable def bandCount (n aLo aHi : ℕ) : ℕ × ℕ → PMF (ℕ × ℕ) := fun s =>
  if s.1 ≤ aLo then PMF.pure (s.1, s.2 + 1)
  else if aHi ≤ s.1 then PMF.pure (s.1, s.2 + 1)
  else triCount n s

/-- Projecting the stopped counting chain gives the base band chain. -/
theorem bandCount_map_fst (n aLo aHi : ℕ) (s : ℕ × ℕ) :
    (bandCount n aLo aHi s).map Prod.fst = bandChain n aLo aHi s.1 := by
  by_cases hlo : s.1 ≤ aLo
  · rw [bandChain, freeze_of_mem s.1 (Or.inl hlo)]
    simp only [bandCount, if_pos hlo]
    exact PMF.pure_map Prod.fst (s.1, s.2 + 1)
  · by_cases hhi : aHi ≤ s.1
    · rw [bandChain, freeze_of_mem s.1 (Or.inr hhi)]
      simp only [bandCount, if_neg hlo, if_pos hhi]
      exact PMF.pure_map Prod.fst (s.1, s.2 + 1)
    · rw [bandChain, freeze_of_not_mem s.1 (by simp [hlo, hhi])]
      simp only [bandCount, if_neg hlo, if_neg hhi]
      exact triCount_map_fst n s

/-- Productive mass bounded below on the live band contracts the counter
potential at every counted step. -/
theorem bandCount_step (n aLo aHi : ℕ) (h3 : 3 ≤ n) (haHi : aHi ≤ n)
    (w p p' : ℝ≥0∞) (hp : p + p' = 1) (hw : w ≤ 1)
    (hprod : ∀ (a b : ℕ) (hb : a + b + 2 = n), aLo ≤ a → a + 1 < aHi →
      p ≤ triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 2)) :
    ∀ s, expect (bandCount n aLo aHi s) (fun z => w ^ z.2) ≤
      (p' + p * w) * w ^ s.2 := by
  rintro ⟨x, c⟩
  by_cases hlo : x ≤ aLo
  · apply count_step_of_masses
        (K := bandCount n aLo aHi) (count := Prod.snd) (s := (x, c))
        (w := w) (q := 1) (q' := 0) (p := p) (p' := p')
    · simp
    · exact hp
    · exact hw
    · rw [← hp]
      exact le_add_right le_rfl
    · rw [bandCount, if_pos hlo, expect_pure]
      simp
  · by_cases hhi : aHi ≤ x
    · apply count_step_of_masses
          (K := bandCount n aLo aHi) (count := Prod.snd) (s := (x, c))
          (w := w) (q := 1) (q' := 0) (p := p) (p' := p')
      · simp
      · exact hp
      · exact hw
      · rw [← hp]
        exact le_add_right le_rfl
      · rw [bandCount, if_neg hlo, if_pos hhi, expect_pure]
        simp
    · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
      obtain ⟨b, hb⟩ : ∃ b, a + b + 2 = n := ⟨n - a - 2, by omega⟩
      rw [bandCount, if_neg (by omega), if_neg (by omega)]
      exact triCount_step_of_productive_lower hb h3 hp hw
        (hprod a b hb (by omega) (by omega))

/-- The lower-boundary mass of the band counting chain obeys the Feller
estimate used by the one-sided rung. -/
theorem bandCount_safety (n aLo aHi bHi k T c₀ : ℕ) (h3 : 3 ≤ n)
    (hpop : aLo + bHi + 2 = n) (haLo : 0 < aLo) (hbHi : 0 < bHi)
    (hmaj : bHi ≤ aLo) (haHi : aHi ≤ n) :
    ∑' z : ℕ × ℕ, (if aLo < z.1 then 0
      else iter (bandCount n aLo aHi) T (aLo + k, c₀) z) ≤
      ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k := by
  set u : ℝ≥0∞ := (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞) with hu
  have hane : (aLo : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hatop : (aLo : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top aLo
  have hu1 : u ≤ 1 := by
    rw [hu]
    calc
      (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞) ≤
          (aLo : ℝ≥0∞) / (aLo : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hmaj) _
      _ = 1 := ENNReal.div_self hane hatop
  have hu0 : u ≠ 0 := by
    rw [hu]
    simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨by simp only [Nat.cast_eq_zero]; omega, hatop⟩
  have hstep : ∀ s : ℕ × ℕ,
      expect (bandCount n aLo aHi s) (fun z => u ^ z.1) ≤ u ^ s.1 := by
    rintro ⟨x, c⟩
    by_cases hlo : x ≤ aLo
    · rw [bandCount, if_pos hlo, expect_pure]
    · by_cases hhi : aHi ≤ x
      · rw [bandCount, if_neg hlo, if_pos hhi, expect_pure]
      · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
        obtain ⟨b, hb⟩ : ∃ b, a + b + 2 = n := ⟨n - a - 2, by omega⟩
        have hbb : b ≤ bHi := by omega
        rw [bandCount, if_neg (by omega), if_neg (by omega)]
        unfold triCount
        rw [expect_map, triChain_apply hb h3]
        change expect (triStep (a + 1) (b + 1) (by omega))
          (fun x => u ^ x) ≤ u ^ (a + 1)
        rw [hu]
        exact triStep_conserve_on_region a b aLo bHi (by omega) (by omega)
          hbb haLo hmaj
  have hruin := ruin_le_u (bandCount n aLo aHi) Prod.fst u hu1 hu0
    (fun z => u ^ z.1) (fun _ => rfl) hstep T aLo k (aLo + k, c₀) rfl
  calc
    ∑' z : ℕ × ℕ, (if aLo < z.1 then 0
        else iter (bandCount n aLo aHi) T (aLo + k, c₀) z) =
      ∑' z : ℕ × ℕ, (if z.1 ≤ aLo then
        iter (bandCount n aLo aHi) T (aLo + k, c₀) z else 0) := by
          apply tsum_congr
          intro z
          by_cases hz : z.1 ≤ aLo <;> simp [hz]
    _ ≤ u ^ k := hruin
    _ = ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k := by rw [hu]

/-- The productive-counter deadline for a chain stopped outside the open band. -/
theorem bandCount_deadline (n aLo aHi T m c₀ : ℕ) (h3 : 3 ≤ n)
    (haHi : aHi ≤ n) (w p p' : ℝ≥0∞) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hp : p + p' = 1)
    (hprod : ∀ (a b : ℕ) (hb : a + b + 2 = n), aLo ≤ a → a + 1 < aHi →
      p ≤ triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 2))
    (x₀ : ℕ) :
    ∑' z, (if z.2 ≤ m then iter (bandCount n aLo aHi) T (x₀, c₀) z else 0) ≤
      (p' + p * w) ^ T * w ^ c₀ / w ^ m := by
  exact count_tail_bernoulli (bandCount n aLo aHi) Prod.snd w p p' hw1 hw0
    (bandCount_step n aLo aHi h3 haHi w p p' hp hw1 hprod) T m (x₀, c₀)

/-- A band rung under an explicit productive-mass lower bound on precisely the
live part of the band. -/
theorem band_rung_bound_of_productive
    (n aLo aHi bHi k T m c₀ : ℕ) (h3 : 3 ≤ n)
    (hpop : aLo + bHi + 2 = n) (haLo : 0 < aLo) (hbHi : 0 < bHi)
    (hmaj : bHi ≤ aLo) (haHi : aHi ≤ n)
    (w p p' : ℝ≥0∞) (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hp : p + p' = 1)
    (hprod : ∀ (a b : ℕ) (hb : a + b + 2 = n), aLo ≤ a → a + 1 < aHi →
      p ≤ triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 2)) :
    Reaches (bandCount n aLo aHi) T
      (fun s => s = (aLo + k, c₀))
      (fun z => aLo < z.1 ∧ (aHi ≤ z.1 ∨ m < z.2))
      (((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k +
        (p' + p * w) ^ T * w ^ c₀ / w ^ m) := by
  have hstrong : Reaches (bandCount n aLo aHi) T
      (fun s => s = (aLo + k, c₀))
      (fun z => aLo < z.1 ∧ m < z.2)
      (((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k +
        (p' + p * w) ^ T * w ^ c₀ / w ^ m) := by
    apply Reaches.inter
    · intro s hs
      subst s
      exact bandCount_safety n aLo aHi bHi k T c₀ h3 hpop haLo hbHi hmaj haHi
    · intro s hs
      subst s
      calc
        ∑' z, (if m < z.2 then 0
            else iter (bandCount n aLo aHi) T (aLo + k, c₀) z) =
            ∑' z, (if z.2 ≤ m then
              iter (bandCount n aLo aHi) T (aLo + k, c₀) z else 0) := by
                apply tsum_congr
                intro z
                by_cases hz : z.2 ≤ m
                · simp [hz, Nat.not_lt.mpr hz]
                · simp [hz, Nat.lt_of_not_ge hz]
        _ ≤ (p' + p * w) ^ T * w ^ c₀ / w ^ m :=
          bandCount_deadline n aLo aHi T m c₀ h3 haHi w p p' hw1 hw0 hp
            hprod (aLo + k)
  intro s hs
  calc
    ∑' z, (if aLo < z.1 ∧ (aHi ≤ z.1 ∨ m < z.2) then 0
        else iter (bandCount n aLo aHi) T s z) ≤
      ∑' z, (if aLo < z.1 ∧ m < z.2 then 0
        else iter (bandCount n aLo aHi) T s z) := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hlo : aLo < z.1 <;> by_cases hc : m < z.2 <;>
            by_cases hhi : aHi ≤ z.1 <;> simp [hlo, hc, hhi]
    _ ≤ ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k +
        (p' + p * w) ^ T * w ^ c₀ / w ^ m := hstrong s hs

/-- One phase-1 band rung with the productive lower bound discharged at
`p = 21 / 64`.  The upper arithmetic guard is the subtraction-free rounded
form ensuring `8 * x < 7 * n` at every live state `x < aHi`. -/
theorem band_rung_bound (n aLo aHi bHi k T m c₀ : ℕ)
    (hpop : aLo + bHi + 2 = n) (hbHi : 0 < bHi) (hbias : bHi < aLo)
    (hphaseHi : 8 * aHi ≤ 7 * n + 7)
    (w : ℝ≥0∞) (hw1 : w ≤ 1) (hw0 : w ≠ 0) :
    Reaches (bandCount n aLo aHi) T
      (fun s => s = (aLo + k, c₀))
      (fun z => aLo < z.1 ∧ (aHi ≤ z.1 ∨ m < z.2))
      (((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k +
        ((43 : ℝ≥0∞) / 64 + (21 : ℝ≥0∞) / 64 * w) ^ T *
          w ^ c₀ / w ^ m) := by
  have h3 : 3 ≤ n := by omega
  have haLo : 0 < aLo := by omega
  have hmaj : bHi ≤ aLo := hbias.le
  have haHi : aHi ≤ n := by omega
  have hp : (21 : ℝ≥0∞) / 64 + (43 : ℝ≥0∞) / 64 = 1 := by
    rw [← ENNReal.add_div]
    norm_num only [Nat.cast_ofNat]
    exact ENNReal.div_self (by norm_num) (by norm_num)
  have hprod : ∀ (a b : ℕ) (hb : a + b + 2 = n), aLo ≤ a → a + 1 < aHi →
      (21 : ℝ≥0∞) / 64 ≤ triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 2) := by
    intro a b hb ha ha'
    exact hprod_phase1 a b n h3 hb (by omega) (by omega)
  exact band_rung_bound_of_productive n aLo aHi bHi k T m c₀ h3 hpop
    haLo hbHi hmaj haHi w ((21 : ℝ≥0∞) / 64) ((43 : ℝ≥0∞) / 64)
    hw1 hw0 hp hprod

/-- A frozen state remains fixed under every deterministic iterate. -/
theorem iter_freeze_of_mem {B : α → Prop} [DecidablePred B]
    {K : α → PMF α} (s : α) (hs : B s) :
    ∀ T, iter (freeze B K) T s = PMF.pure s := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [iter_succ, freeze_of_mem s hs, PMF.pure_bind, ih]

/-- Freezing away from a target can only increase its terminal failure mass. -/
theorem failure_le_failure_freeze {B A : α → Prop}
    [DecidablePred B] [DecidablePred A] {K : α → PMF α}
    (hdisj : ∀ s, A s → ¬ B s) :
    ∀ T s,
      (∑' z, if A z then 0 else iter K T s z) ≤
        ∑' z, if A z then 0 else iter (freeze B K) T s z := by
  let V : α → ℝ≥0∞ := fun z => if A z then 0 else 1
  have hmass (q : PMF α) :
      (∑' z, if A z then 0 else q z) = expect q V := by
    unfold expect V
    apply tsum_congr
    intro z
    by_cases hz : A z <;> simp [hz]
  intro T
  induction T with
  | zero =>
      intro s
      rfl
  | succ T ih =>
      intro s
      rw [hmass, hmass]
      by_cases hs : B s
      · have hAs : ¬ A s := fun hA => hdisj s hA hs
        rw [iter_freeze_of_mem s hs (T + 1), expect_pure]
        calc
          expect (iter K (T + 1) s) V ≤ ∑' z, iter K (T + 1) s z := by
            unfold expect
            exact ENNReal.tsum_le_tsum fun z => by
              unfold V
              by_cases hz : A z <;> simp [hz]
          _ = 1 := PMF.tsum_coe _
          _ = V s := by simp [V, hAs]
      · rw [iter_succ, iter_succ, freeze_of_not_mem s hs,
          expect_bind, expect_bind]
        exact ENNReal.tsum_le_tsum fun a => mul_le_mul_right (by
          rw [← hmass, ← hmass]
          exact ih a) _

/-- A reachability estimate for a frozen chain transfers to the original chain
when the target is disjoint from the freeze set. -/
theorem Reaches.of_freeze {B P A : α → Prop}
    [DecidablePred B] [DecidablePred A] {K : α → PMF α}
    {T : ℕ} {ε : ℝ≥0∞} (hdisj : ∀ s, A s → ¬ B s)
    (h : Reaches (freeze B K) T P A ε) :
    Reaches K T P A ε := by
  intro s hs
  exact (failure_le_failure_freeze hdisj T s).trans (h s hs)

/-- The original chain's terminal failure mass is bounded by that of the band
counting chain for a first-coordinate target lying strictly inside the band. -/
theorem band_rung_transfer (n aLo aHi T x₀ c₀ : ℕ)
    (A : ℕ → Prop) [DecidablePred A]
    (hA : ∀ x, A x → aLo < x ∧ x < aHi) :
    (∑' x, if A x then 0 else iter (triChain n) T x₀ x) ≤
      ∑' s, if A s.1 then 0 else
        iter (bandCount n aLo aHi) T (x₀, c₀) s := by
  let B : ℕ → Prop := fun x => x ≤ aLo ∨ aHi ≤ x
  let V : ℕ → ℝ≥0∞ := fun x => if A x then 0 else 1
  have hdisj : ∀ x, A x → ¬ B x := by
    intro x hx hB
    obtain ⟨hxLo, hxHi⟩ := hA x hx
    rcases hB with hxlo | hxhi <;> omega
  have hmap :
      (iter (bandCount n aLo aHi) T (x₀, c₀)).map Prod.fst =
        iter (bandChain n aLo aHi) T x₀ :=
    iter_map_of_step_map _ _ _ (bandCount_map_fst n aLo aHi) T _
  have hmass_nat (q : PMF ℕ) :
      (∑' z, if A z then 0 else q z) = expect q V := by
    unfold expect V
    apply tsum_congr
    intro z
    by_cases hz : A z <;> simp [hz]
  have hmass_pair (q : PMF (ℕ × ℕ)) :
      (∑' z, if A z.1 then 0 else q z) = expect q (fun z => V z.1) := by
    unfold expect V
    apply tsum_congr
    intro z
    by_cases hz : A z.1 <;> simp [hz]
  calc
    (∑' x, if A x then 0 else iter (triChain n) T x₀ x) ≤
        ∑' x, if A x then 0 else iter (bandChain n aLo aHi) T x₀ x := by
      unfold bandChain
      exact failure_le_failure_freeze hdisj T x₀
    _ = expect (iter (bandChain n aLo aHi) T x₀) V := hmass_nat _
    _ = expect ((iter (bandCount n aLo aHi) T (x₀, c₀)).map Prod.fst) V := by
      rw [hmap]
    _ = expect (iter (bandCount n aLo aHi) T (x₀, c₀)) (fun z => V z.1) :=
      expect_map _ _ _
    _ = ∑' s, if A s.1 then 0 else
        iter (bandCount n aLo aHi) T (x₀, c₀) s := (hmass_pair _).symm

/-- A band-chain reachability estimate transfers to the original chain for an
interior first-coordinate target. -/
theorem Reaches.of_bandCount (n aLo aHi T x₀ c₀ : ℕ)
    (A : ℕ → Prop) [DecidablePred A] (ε : ℝ≥0∞)
    (hA : ∀ x, A x → aLo < x ∧ x < aHi)
    (hband : Reaches (bandCount n aLo aHi) T
      (fun s => s = (x₀, c₀)) (fun s => A s.1) ε) :
    Reaches (triChain n) T (fun x => x = x₀) A ε := by
  intro x hx
  subst x
  exact (band_rung_transfer n aLo aHi T x₀ c₀ A hA).trans
    (hband (x₀, c₀) rfl)

/-- A direction-sensitive arithmetic criterion for doubling an initial gap.
The total productive count must be split into up and down reactions, and the
up count must satisfy the displayed directional excess. -/
theorem phase1_direction_progress {n g x₀ x up down count : ℕ}
    (hgap : n + g ≤ 2 * x₀) (hcount : up + down = count)
    (hnet : x + down = x₀ + up) (hdir : 2 * count + g ≤ 4 * up) :
    n + 2 * g ≤ 2 * x := by
  omega

/-- A rung-good terminal state reaches doubled gap once the missing
directional tail estimate is supplied.  The second hypothesis is precisely the
unproved mass of runs with enough productive reactions but insufficient net
upward direction. -/
theorem phase1_direction_progress_of_tail
    (n aLo aHi x₀ T m c₀ : ℕ) (εrung εdir : ℝ≥0∞)
    (hrung : Reaches (bandCount n aLo aHi) T
      (fun s => s = (x₀, c₀))
      (fun z => aLo < z.1 ∧ (aHi ≤ z.1 ∨ m < z.2)) εrung)
    (hdirection : ∑' z, (if 4 * x₀ ≤ n + 2 * z.1 then 0
      else if aLo < z.1 ∧ (aHi ≤ z.1 ∨ m < z.2) then
        iter (bandCount n aLo aHi) T (x₀, c₀) z else 0) ≤ εdir) :
    Reaches (bandCount n aLo aHi) T
      (fun s => s = (x₀, c₀))
      (fun z => 4 * x₀ ≤ n + 2 * z.1) (εrung + εdir) := by
  intro s hs
  subst s
  calc
    ∑' z, (if 4 * x₀ ≤ n + 2 * z.1 then 0
        else iter (bandCount n aLo aHi) T (x₀, c₀) z) ≤
      ∑' z, ((if aLo < z.1 ∧ (aHi ≤ z.1 ∨ m < z.2) then 0
        else iter (bandCount n aLo aHi) T (x₀, c₀) z) +
        (if 4 * x₀ ≤ n + 2 * z.1 then 0
        else if aLo < z.1 ∧ (aHi ≤ z.1 ∨ m < z.2) then
          iter (bandCount n aLo aHi) T (x₀, c₀) z else 0)) := by
      refine ENNReal.tsum_le_tsum fun z => ?_
      by_cases hq : aLo < z.1 ∧ (aHi ≤ z.1 ∨ m < z.2) <;>
        by_cases hr : 4 * x₀ ≤ n + 2 * z.1 <;> simp [hq, hr]
    _ = (∑' z, (if aLo < z.1 ∧ (aHi ≤ z.1 ∨ m < z.2) then 0
          else iter (bandCount n aLo aHi) T (x₀, c₀) z)) +
        ∑' z, (if 4 * x₀ ≤ n + 2 * z.1 then 0
          else if aLo < z.1 ∧ (aHi ≤ z.1 ∨ m < z.2) then
            iter (bandCount n aLo aHi) T (x₀, c₀) z else 0) := ENNReal.tsum_add
    _ ≤ εrung + εdir := add_le_add (hrung (x₀, c₀) rfl) hdirection

end Tri
