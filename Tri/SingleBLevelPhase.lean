/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBCoReturn
import Tri.SingleBStaged

/-!
# Level-form Single-B band phase

`singleBand_phase_reaches` pins the exit predicate to a physical `x` floor,
which cannot re-establish the next gap-form checkpoint.  This file rebuilds
the phase around a physical LEVEL exit `Lexit ≤ 2x+b`, which is exactly what
a gap-form ladder chains on.

The transfer works through `failure_le_failure_freeze_add_exc` with the
exception event

```
E q := (D + cx ≤ cy) ∨ (D₂ + cy ≤ cx) ∨ (H ≤ cx + cy),
```

whose three components are charged to the `Y`-side creation tail, the mirror
`X`-side creation tail, and the (zero-mass, for a lazy budget) boundary
stream.  Outside `E`, a frozen state's physical level is pinned within `D₂`
of the corrected band: frozen-low states contradict the exit, and frozen-high
states sit `sret` co-units above it, where the co-level return engine gives a
horizon-bounded Hoeffding return bound.
-/

namespace Tri

open scoped ENNReal

variable {n : ℕ}

/-! ## The mirror creation tail on the stopped band -/

/-- The `X`-heavy creation-imbalance tail survives the band stopping. -/
theorem singleCreationX_stopped_tail (hn : 2 ≤ n)
    (aLoΛ hiΛ D H D₂ T : ℕ) (hH : 0 < H) (s₀ : SingleState n) :
    ∑' q, (if CreationBad D₂ H q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      ≤ ENNReal.ofReal (Real.exp (-((D₂ : ℝ) ^ 2 / (2 * (H : ℝ))))) := by
  classical
  set K : SingleLedger n → PMF (SingleLedger n) :=
    singleBandStop n hn aLoΛ hiΛ D H with hK
  set lam : ℝ := (D₂ : ℝ) / (H : ℝ) with hlam
  have hlam0 : (0 : ℝ) ≤ lam := by
    rw [hlam]
    positivity
  -- dominate by the chain frozen additionally at the bad set
  have hfreeze :=
    failure_le_failure_freeze
      (B := CreationBad D₂ H (n := n))
      (A := fun q : SingleLedger n => ¬ CreationBad D₂ H q)
      (K := K)
      (fun s hs => not_not.mp (not_not_intro hs)) T
      (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n)
  have hconv : ∀ (p : SingleLedger n → ℝ≥0∞),
      (∑' q, if CreationBad D₂ H q then p q else 0) =
        ∑' q, if ¬ CreationBad D₂ H q then 0 else p q := by
    intro p
    apply tsum_congr
    intro q
    by_cases hq : CreationBad D₂ H q <;> simp [hq]
  have hhit :
      (∑' q, if ¬ CreationBad D₂ H q then 0 else
          iter (freeze (CreationBad D₂ H) K) T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q) =
        hitProb (CreationBad D₂ H) K T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) := by
    unfold hitProb expect ind
    apply tsum_congr
    intro q
    by_cases hq : CreationBad D₂ H q <;> simp [hq]
  have hstep : ∀ q : SingleLedger n,
      expect (K q) (creationG lam) ≤ creationG lam q := by
    intro q
    rw [hK]
    unfold singleBandStop
    exact creationG_freeze_step hn lam
      (SingleBandFrozen n aLoΛ hiΛ D H) q
  have hville := ville_frozen K (CreationBad D₂ H)
    (creationG lam) (creationTheta lam D₂ H)
    (creationTheta_ne_zero lam D₂ H)
    (creationTheta_ne_top lam D₂ H)
    (creation_contain lam hlam0 D₂ H)
    hstep
    (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n)
  rw [creationG_fresh lam s₀, one_div_creationTheta] at hville
  rw [hlam] at hville
  rw [creation_exponent_optimised D₂ H hH] at hville
  calc
    (∑' q, (if CreationBad D₂ H q then
        iter K T (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
        = ∑' q, if ¬ CreationBad D₂ H q then 0 else
            iter K T (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q := hconv _
    _ ≤ ∑' q, if ¬ CreationBad D₂ H q then 0 else
          iter (freeze (CreationBad D₂ H) K) T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q := hfreeze
    _ = hitProb (CreationBad D₂ H) K T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) := hhit
    _ ≤ ⨆ U : ℕ, hitProb (CreationBad D₂ H) K U
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) :=
      le_iSup (fun U : ℕ => hitProb (CreationBad D₂ H) K U
        (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n)) T
    _ ≤ ENNReal.ofReal (Real.exp (-((D₂ : ℝ) ^ 2 / (2 * (H : ℝ))))) :=
      hville

/-! ## The exception event -/

/-- Ledger exception event: either creation imbalance has reached `D` on the
`Y` side or `D₂` on the `X` side, or the creation budget is exhausted. -/
def SingleLevelExc (D D₂ H : ℕ) (q : SingleLedger n) : Prop :=
  (D + q.cx ≤ q.cy) ∨ (D₂ + q.cy ≤ q.cx) ∨ singleCreationBoundary H q

instance (D D₂ H : ℕ) : DecidablePred (SingleLevelExc D D₂ H (n := n)) :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- Failure of the level exit together with no exception forces the corrected
level below the target `Lexit + D`. -/
theorem singleLevelExc_failure_split
    (D D₂ H Lexit : ℕ) (q : SingleLedger n)
    (h : ¬ ((Lexit ≤ q.cfg.1.doubleLevel) ∧ ¬ SingleLevelExc D D₂ H q)) :
    (singleCorrectedBelow (Lexit + D) q ∨ CreationBadY D H q ∨
        singleCreationBoundary H q) ∨ (D₂ + q.cy ≤ q.cx) := by
  by_cases hE2 : D₂ + q.cy ≤ q.cx
  · exact Or.inr hE2
  by_cases hE3 : singleCreationBoundary H q
  · exact Or.inl (Or.inr (Or.inr hE3))
  by_cases hE1 : D + q.cx ≤ q.cy
  · left
    right
    left
    refine ⟨?_, hE1⟩
    unfold singleCreationBoundary at hE3
    omega
  · have hnE : ¬ SingleLevelExc D D₂ H q := by
      unfold SingleLevelExc
      tauto
    have hnA : ¬ Lexit ≤ q.cfg.1.doubleLevel := by
      intro hA
      exact h ⟨hA, hnE⟩
    left
    left
    unfold singleCorrectedBelow
    omega

/-! ## The level-form phase theorem -/

/-- Explicit error of one level-form Single-B band phase. -/
noncomputable def singleLevelPhaseError
    (w η : ℝ≥0∞) (Bw Lentry targetΛ M : ℕ) (ε_clock : ℝ≥0∞)
    (D D₂ H : ℕ) (Bret sret T n : ℕ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  ((w ^ Bw + w ^ Lentry / (w ^ targetΛ * η ^ M)) + ε_clock)
    + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ)))))
    + ENNReal.ofReal (Real.exp (-((D₂ : ℝ) ^ 2 / (2 * (H : ℝ)))))
    + (1 + ε ^ 2 * ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
        (1 + ε) ^ (sret + 1)

/-- **Level-form Single-B phase reachability.**  From every state at physical
level at least `Lentry`, after exactly `T` steps the physical level is at
least `Lexit`, except for the six explicit error streams: backslide,
direction deadline, clock starvation, the two creation tails, and the
co-level return. -/
theorem singleBand_reaches_level
    (hn : 2 ≤ n)
    (aLoΛ hiΛ D D₂ H p qRat Bw M T Lentry Lexit sret Bret : ℕ)
    (hH : 0 < H) (hTH : T < H) (hq : qRat ≠ 0)
    (w v η u ε_clock : ℝ≥0∞) (ε : ℝ≥0∞) (hε1 : ε ≤ 1)
    (hu : u = (p : ℝ≥0∞) / (qRat : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hwv : w * v = 1) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤)
    (hlive : ∀ q, ¬ SingleBandFrozen n aLoΛ hiΛ D H q →
      ∃ a : ℕ, q.CorrectedLevel (a + 1) ∧
        qRat * q.cfg.1.y ≤ p * q.cfg.1.x)
    (hBw : aLoΛ + Bw = Lentry)
    (hvac : aLoΛ + D₂ ≤ Lexit)
    (hLn : n + 1 ≤ Lexit)
    (hBret : Lexit + Bret = 2 * n + 1)
    (hslack : Lexit + sret + D ≤ hiΛ)
    (hclock : ∀ s : SingleState n, Lentry ≤ s.1.doubleLevel →
      ∑' q, (if singleBandStarvation aLoΛ (Lexit + D) H M q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
        ≤ ε_clock) :
    Reaches (singleStateStep n hn) T
      (fun s => Lentry ≤ s.1.doubleLevel)
      (fun s => Lexit ≤ s.1.doubleLevel)
      (singleLevelPhaseError w η Bw Lentry (Lexit + D) M ε_clock
        D D₂ H Bret sret T n ε) := by
  intro s hs
  obtain ⟨d, hd⟩ : ∃ d, s.1.doubleLevel = Lentry + d :=
    ⟨s.1.doubleLevel - Lentry, by omega⟩
  set q₀ : SingleLedger n := ⟨s, 0, 0, 0, 0⟩ with hq₀
  -- the exception transfer on the ledger chain
  have hreturn : ∀ q : SingleLedger n,
      SingleBandFrozen n aLoΛ hiΛ D H q →
      (fun r : SingleLedger n => Lexit ≤ r.cfg.1.doubleLevel) q →
      ¬ SingleLevelExc D D₂ H q → ∀ U, U ≤ T →
      (∑' z, if Lexit ≤ z.cfg.1.doubleLevel then 0
          else iter (singleLedgerStep n hn) U q z) ≤
        (1 + ε ^ 2 * ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
          (1 + ε) ^ (sret + 1) := by
    intro q hfr hA hE U hUT
    have hlevel : Lexit + sret ≤ q.cfg.1.doubleLevel := by
      rcases hfr with hLow | hHigh | hBad | hBound
      · -- frozen low: contradicts the exit outside the exception
        exfalso
        have hnE2 : ¬ (D₂ + q.cy ≤ q.cx) := fun h =>
          hE (Or.inr (Or.inl h))
        change Lexit ≤ q.cfg.1.doubleLevel at hA
        omega
      · -- frozen high: outside the Y-imbalance the level is pinned
        have hnE1 : ¬ (D + q.cx ≤ q.cy) := fun h => hE (Or.inl h)
        omega
      · exact absurd (Or.inl hBad.2) hE
      · exact absurd (Or.inr (Or.inr hBound)) hE
    have hconv :
        (∑' z, if Lexit ≤ z.cfg.1.doubleLevel then 0
            else iter (singleLedgerStep n hn) U q z) =
          ∑' z : SingleState n, if Lexit ≤ z.1.doubleLevel then 0
            else iter (singleStateStep n hn) U q.cfg z :=
      (singleState_failure_eq_ledger n hn U q
        (fun z : SingleState n => Lexit ≤ z.1.doubleLevel)).symm
    rw [hconv]
    exact singleCo_return_raw n hn Lexit sret T U Bret hUT hLn hBret
      ε hε1 q.cfg hlevel
  have htransfer :=
    failure_le_failure_freeze_add_exc
      (B := SingleBandFrozen n aLoΛ hiΛ D H)
      (A := fun q : SingleLedger n => Lexit ≤ q.cfg.1.doubleLevel)
      (E := SingleLevelExc D D₂ H)
      (K := singleLedgerStep n hn)
      (δ := (1 + ε ^ 2 * ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
        (1 + ε) ^ (sret + 1))
      (T := T) hreturn T le_rfl q₀
  -- the stopped side: split failures into the five band streams plus the
  -- mirror creation stream
  have hstopped :
      (∑' q, if (Lexit ≤ q.cfg.1.doubleLevel) ∧
          ¬ SingleLevelExc D D₂ H q then 0
          else iter (freeze (SingleBandFrozen n aLoΛ hiΛ D H)
            (singleLedgerStep n hn)) T q₀ q) ≤
        (∑' q, (if singleCorrectedBelow (Lexit + D) q ∨ CreationBadY D H q ∨
              singleCreationBoundary H q then
            iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q else 0))
          + (∑' q, (if CreationBad D₂ H q then
              iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q else 0)) := by
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun q => ?_
    by_cases hA' : (Lexit ≤ q.cfg.1.doubleLevel) ∧
        ¬ SingleLevelExc D D₂ H q
    · simp [hA']
    · have hsplit := singleLevelExc_failure_split D D₂ H Lexit q hA'
      have hKeq : iter (freeze (SingleBandFrozen n aLoΛ hiΛ D H)
          (singleLedgerStep n hn)) T q₀ q =
          iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q := rfl
      rw [if_neg hA', hKeq]
      rcases hsplit with hfive | hE2
      · calc
          iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q
              = (if singleCorrectedBelow (Lexit + D) q ∨
                  CreationBadY D H q ∨ singleCreationBoundary H q then
                iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q else 0) := by
            rw [if_pos hfive]
          _ ≤ _ := le_add_right le_rfl
      · by_cases hmass :
            iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q = 0
        · rw [hmass]
          exact bot_le
        · have hbudget :=
            singleBandStop_creation_budget_fresh hn aLoΛ hiΛ D H s q
              (by simpa [hq₀] using hmass)
          have hbad2 : CreationBad D₂ H q := ⟨by omega, hE2⟩
          calc
            iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q
                = (if CreationBad D₂ H q then
                  iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q else 0) := by
              rw [if_pos hbad2]
            _ ≤ _ := le_add_left le_rfl
  -- the five band streams at the shifted start
  have hphase := singleBand_phase_fail hn aLoΛ hiΛ (Lexit + D) D H p qRat
    (Bw + d) M T hH hTH hq w v η u ε_clock hu hrel hwη hwv hw1 hw0 hη1
    hwt hηt hlive s (by omega) (hclock s hs)
  -- the mirror creation stream
  have hmirror := singleCreationX_stopped_tail hn aLoΛ hiΛ D H D₂ T hH s
  -- monotonicity in the start shift
  have hmono :
      (w ^ (Bw + d) + w ^ (aLoΛ + (Bw + d)) / (w ^ (Lexit + D) * η ^ M)) ≤
        w ^ Bw + w ^ Lentry / (w ^ (Lexit + D) * η ^ M) := by
    apply add_le_add
    · exact pow_le_pow_right_of_le_one' hw1 (by omega)
    · exact ENNReal.div_le_div_right
        (pow_le_pow_right_of_le_one' hw1 (by omega)) _
  -- assemble
  have hfail :
      (∑' z, if Lexit ≤ z.1.doubleLevel then 0
          else iter (singleStateStep n hn) T s z) =
        ∑' q, if Lexit ≤ q.cfg.1.doubleLevel then 0
          else iter (singleLedgerStep n hn) T q₀ q :=
    singleState_failure_eq_ledger n hn T q₀
      (fun z : SingleState n => Lexit ≤ z.1.doubleLevel)
  unfold singleLevelPhaseError
  calc
    (∑' z, if Lexit ≤ z.1.doubleLevel then 0
        else iter (singleStateStep n hn) T s z)
        = ∑' q, if Lexit ≤ q.cfg.1.doubleLevel then 0
            else iter (singleLedgerStep n hn) T q₀ q := hfail
    _ ≤ (∑' q, if (Lexit ≤ q.cfg.1.doubleLevel) ∧
            ¬ SingleLevelExc D D₂ H q then 0
            else iter (freeze (SingleBandFrozen n aLoΛ hiΛ D H)
              (singleLedgerStep n hn)) T q₀ q)
          + (1 + ε ^ 2 * ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
              (1 + ε) ^ (sret + 1) := htransfer
    _ ≤ ((∑' q, (if singleCorrectedBelow (Lexit + D) q ∨
              CreationBadY D H q ∨ singleCreationBoundary H q then
            iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q else 0))
          + (∑' q, (if CreationBad D₂ H q then
              iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q else 0)))
          + (1 + ε ^ 2 * ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
              (1 + ε) ^ (sret + 1) :=
      add_le_add hstopped le_rfl
    _ ≤ ((((w ^ (Bw + d) + w ^ (aLoΛ + (Bw + d)) /
              (w ^ (Lexit + D) * η ^ M)) + ε_clock)
          + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ))))))
          + ENNReal.ofReal (Real.exp (-((D₂ : ℝ) ^ 2 / (2 * (H : ℝ))))))
          + (1 + ε ^ 2 * ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
              (1 + ε) ^ (sret + 1) :=
      add_le_add (add_le_add hphase hmirror) le_rfl
    _ ≤ (((w ^ Bw + w ^ Lentry / (w ^ (Lexit + D) * η ^ M)) + ε_clock)
          + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ)))))
          + ENNReal.ofReal (Real.exp (-((D₂ : ℝ) ^ 2 / (2 * (H : ℝ)))))
          + (1 + ε ^ 2 * ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
              (1 + ε) ^ (sret + 1)) := by
      exact add_le_add (add_le_add (add_le_add
        (add_le_add hmono le_rfl) le_rfl) le_rfl) le_rfl

end Tri

#print axioms Tri.singleCreationX_stopped_tail
#print axioms Tri.singleLevelExc_failure_split
#print axioms Tri.singleBand_reaches_level
