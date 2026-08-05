/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBGapRung
import Tri.Phase1Refactored

/-!
# Single-B early gap ladder

Gap-form checkpoints `n + G ≤ 2x+b` on the physical doubled level.  A stage
at unit `u` runs 132 concrete rungs (`singleGapRung`), doubling the
checkpoint gap from `132u` to `264u`; the dyadic ladder runs the stages from
the seed unit `max 1 (seedR/132)` until the unit reaches `n/2^18`, landing at
the fixed early target gap `132·(n/2^18) ≈ n/1986`.  Every rung horizon is
the γ-free `Θ(n)` wide-clock horizon.
-/

namespace Tri

open scoped BigOperators ENNReal

/-- Gap-form Single-B checkpoint on the physical doubled level. -/
def SingleGapCheckpoint (n G : ℕ) (s : SingleState n) : Prop :=
  n + G ≤ s.1.doubleLevel

instance (n G : ℕ) : DecidablePred (SingleGapCheckpoint n G) := fun _ =>
  inferInstanceAs (Decidable (_ ≤ _))

/-- A fixed-scale chain of `R` concrete rungs, climbing `R·u` gap units. -/
theorem singleGapChain
    (n u G₀ R : ℕ) (hn : 2 ≤ n) (hu : 0 < u)
    (hlar : 131072 * u ≤ n) (hG₀ : 130 * u ≤ G₀)
    (hsmall : 4 * (G₀ + R * u) + 1032 * u + 8 ≤ n) :
    Reaches (singleStateStep n hn) (R * singleWideHorizon n (n / 8))
      (SingleGapCheckpoint n G₀)
      (SingleGapCheckpoint n (G₀ + R * u))
      (R * (8 * singleGapEnvelope n u)) := by
  have hrungs : ∀ t < R,
      Reaches (singleStateStep n hn) (singleWideHorizon n (n / 8))
        (fun s => SingleGapCheckpoint n (G₀ + t * u) s)
        (fun s => SingleGapCheckpoint n (G₀ + (t + 1) * u) s)
        (8 * singleGapEnvelope n u) := by
    intro t ht
    have htu : t * u + u ≤ R * u := by
      have h1 : t + 1 ≤ R := ht
      calc
        t * u + u = (t + 1) * u := (Nat.succ_mul t u).symm
        _ ≤ R * u := Nat.mul_le_mul_right u h1
    refine (singleGapRung n u (G₀ + t * u) hn hu hlar
      (by omega) (by omega)).mono_post ?_
    intro z hz
    show n + (G₀ + (t + 1) * u) ≤ z.1.doubleLevel
    have hmul : (t + 1) * u = t * u + u := Nat.succ_mul t u
    omega
  have hchain :=
    Reaches.chain_uniform
      (K := singleStateStep n hn)
      (P := fun t => SingleGapCheckpoint n (G₀ + t * u))
      (T := fun _ => singleWideHorizon n (n / 8))
      (ε := fun _ => 8 * singleGapEnvelope n u)
      hrungs (fun _ _ => rfl) (fun _ _ => le_rfl)
  intro s hs
  refine le_trans ?_ (hchain s (by
    show n + (G₀ + 0 * u) ≤ s.1.doubleLevel
    have h0 : 0 * u = 0 := Nat.zero_mul u
    exact by
      change n + G₀ ≤ s.1.doubleLevel at hs
      omega))
  exact le_of_eq rfl

/-- A fixed-scale chain of concrete structural rungs with a caller-supplied
creation quota `M`.  This is the middle-extension form: the sharp `CX` cap in
`singleGapRung_structural` lets the gap climb to a fixed fraction of `n`. -/
theorem singleGapChain_structural
    (n u M G₀ R : ℕ) (hn : 2 ≤ n) (hu : 0 < u)
    (hlar : 131072 * u ≤ n) (hG₀ : 130 * u ≤ G₀)
    (hMdir : 16 * n ≤ 255 * M) (hM8 : 8 * M ≤ n)
    (hsmall : 2 * (G₀ + R * u) + 512 * u + 4 * M ≤ n) :
    Reaches (singleStateStep n hn) (R * singleWideHorizon n M)
      (SingleGapCheckpoint n G₀)
      (SingleGapCheckpoint n (G₀ + R * u))
      (R * (8 * singleGapEnvelope n u)) := by
  have hrungs : ∀ t < R,
      Reaches (singleStateStep n hn) (singleWideHorizon n M)
        (fun s => SingleGapCheckpoint n (G₀ + t * u) s)
        (fun s => SingleGapCheckpoint n (G₀ + (t + 1) * u) s)
        (8 * singleGapEnvelope n u) := by
    intro t ht
    have htu : t * u + u ≤ R * u := by
      have h1 : t + 1 ≤ R := ht
      calc
        t * u + u = (t + 1) * u := (Nat.succ_mul t u).symm
        _ ≤ R * u := Nat.mul_le_mul_right u h1
    refine (singleGapRung_structural n u (G₀ + t * u) M hn hu hlar
      (by omega) hMdir hM8 (by omega)).mono_post ?_
    intro z hz
    show n + (G₀ + (t + 1) * u) ≤ z.1.doubleLevel
    have hmul : (t + 1) * u = t * u + u := Nat.succ_mul t u
    omega
  have hchain :=
    Reaches.chain_uniform
      (K := singleStateStep n hn)
      (P := fun t => SingleGapCheckpoint n (G₀ + t * u))
      (T := fun _ => singleWideHorizon n M)
      (ε := fun _ => 8 * singleGapEnvelope n u)
      hrungs (fun _ _ => rfl) (fun _ _ => le_rfl)
  intro s hs
  refine le_trans ?_ (hchain s (by
    show n + (G₀ + 0 * u) ≤ s.1.doubleLevel
    have h0 : 0 * u = 0 := Nat.zero_mul u
    exact by
      change n + G₀ ≤ s.1.doubleLevel at hs
      omega))
  exact le_of_eq rfl

/-- A fixed-scale chain of wider concrete structural rungs, using
`g = 256u`.  This is the main middle-extension form after the short bootstrap
from `132u` to `258u`. -/
theorem singleGapChain_structural256
    (n u M G₀ R : ℕ) (hn : 2 ≤ n) (hu : 0 < u)
    (hlar : 131072 * u ≤ n) (hG₀ : 258 * u ≤ G₀)
    (hMdir : 32 * n ≤ 1000 * M) (hM8 : 8 * M ≤ n)
    (hsmall : 2 * (G₀ + R * u) + 1024 * u + 4 * M ≤ n) :
    Reaches (singleStateStep n hn) (R * singleWideHorizon n M)
      (SingleGapCheckpoint n G₀)
      (SingleGapCheckpoint n (G₀ + R * u))
      (R * (8 * singleGapEnvelope n u)) := by
  have hrungs : ∀ t < R,
      Reaches (singleStateStep n hn) (singleWideHorizon n M)
        (fun s => SingleGapCheckpoint n (G₀ + t * u) s)
        (fun s => SingleGapCheckpoint n (G₀ + (t + 1) * u) s)
        (8 * singleGapEnvelope n u) := by
    intro t ht
    have htu : t * u + u ≤ R * u := by
      have h1 : t + 1 ≤ R := ht
      calc
        t * u + u = (t + 1) * u := (Nat.succ_mul t u).symm
        _ ≤ R * u := Nat.mul_le_mul_right u h1
    refine (singleGapRung_structural256 n u (G₀ + t * u) M hn hu hlar
      (by omega) hMdir hM8 (by omega)).mono_post ?_
    intro z hz
    show n + (G₀ + (t + 1) * u) ≤ z.1.doubleLevel
    have hmul : (t + 1) * u = t * u + u := Nat.succ_mul t u
    omega
  have hchain :=
    Reaches.chain_uniform
      (K := singleStateStep n hn)
      (P := fun t => SingleGapCheckpoint n (G₀ + t * u))
      (T := fun _ => singleWideHorizon n M)
      (ε := fun _ => 8 * singleGapEnvelope n u)
      hrungs (fun _ _ => rfl) (fun _ _ => le_rfl)
  intro s hs
  refine le_trans ?_ (hchain s (by
    show n + (G₀ + 0 * u) ≤ s.1.doubleLevel
    have h0 : 0 * u = 0 := Nat.zero_mul u
    exact by
      change n + G₀ ≤ s.1.doubleLevel at hs
      omega))
  exact le_of_eq rfl

/-! ## Dyadic stages -/

/-- Seed unit of the Single-B early ladder. -/
def singleEarlySeedUnit (n γ : ℕ) : ℕ :=
  max 1 (phase1SeedR n γ / 132)

/-- Dyadic unit scale of stage `j`. -/
def singleEarlyScale (n γ j : ℕ) : ℕ :=
  2 ^ j * singleEarlySeedUnit n γ

theorem singleEarlyScale_pos (n γ j : ℕ) : 0 < singleEarlyScale n γ j := by
  unfold singleEarlyScale singleEarlySeedUnit
  positivity

theorem singleEarlyScale_succ (n γ j : ℕ) :
    singleEarlyScale n γ (j + 1) = 2 * singleEarlyScale n γ j := by
  unfold singleEarlyScale
  rw [pow_succ]
  ring

/-- One dyadic Single-B stage: 132 rungs at unit `u_j`, doubling the gap. -/
theorem singleEarly_stage
    (n γ j : ℕ) (hn : 2 ≤ n)
    (hguard : 131072 * singleEarlyScale n γ j ≤ n) :
    Reaches (singleStateStep n hn) (132 * singleWideHorizon n (n / 8))
      (SingleGapCheckpoint n (132 * singleEarlyScale n γ j))
      (SingleGapCheckpoint n (132 * singleEarlyScale n γ (j + 1)))
      (132 * (8 * singleGapEnvelope n (singleEarlyScale n γ j))) := by
  set u : ℕ := singleEarlyScale n γ j with hudef
  have hu : 0 < u := singleEarlyScale_pos n γ j
  have hchain := singleGapChain n u (132 * u) 132 hn hu hguard
    (by omega) (by omega)
  refine hchain.mono_post ?_
  intro z hz
  show n + 132 * singleEarlyScale n γ (j + 1) ≤ z.1.doubleLevel
  rw [singleEarlyScale_succ]
  change n + (132 * u + 132 * u) ≤ z.1.doubleLevel at hz
  omega

/-! ## The dyadic ladder -/

theorem singleEarlyScale_hits (n γ : ℕ) :
    ∃ j, n / 262144 ≤ singleEarlyScale n γ j := by
  refine ⟨Nat.log 2 n, ?_⟩
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hpow : n < 2 ^ (Nat.log 2 n + 1) := by
      simpa using Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
    have hhalf : n / 262144 ≤ 2 ^ Nat.log 2 n := by
      rw [pow_succ] at hpow
      have hd : n / 262144 ≤ n := Nat.div_le_self n 262144
      omega
    calc
      n / 262144 ≤ 2 ^ Nat.log 2 n := hhalf
      _ = 2 ^ Nat.log 2 n * 1 := by ring
      _ ≤ 2 ^ Nat.log 2 n * singleEarlySeedUnit n γ := by
        exact Nat.mul_le_mul_left _ (le_max_left 1 _)

/-- Number of dyadic Single-B stages. -/
def singleEarlyStages (n γ : ℕ) : ℕ :=
  Nat.find (singleEarlyScale_hits n γ)

theorem singleEarlyScale_final (n γ : ℕ) :
    n / 262144 ≤ singleEarlyScale n γ (singleEarlyStages n γ) :=
  Nat.find_spec (singleEarlyScale_hits n γ)

theorem singleEarlyScale_lt_final
    (n γ i : ℕ) (hi : i < singleEarlyStages n γ) :
    singleEarlyScale n γ i < n / 262144 :=
  Nat.lt_of_not_ge (Nat.find_min (singleEarlyScale_hits n γ) hi)

theorem singleEarlyStages_le_log (n γ : ℕ) :
    singleEarlyStages n γ ≤ Nat.log 2 n := by
  exact Nat.find_min' (singleEarlyScale_hits n γ)
    (by
      rcases singleEarlyScale_hits n γ with ⟨j, hj⟩
      by_cases hn0 : n = 0
      · subst n
        simp
      · have hpow : n < 2 ^ (Nat.log 2 n + 1) := by
          simpa using Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
        have hhalf : n / 262144 ≤ 2 ^ Nat.log 2 n := by
          rw [pow_succ] at hpow
          have hd : n / 262144 ≤ n := Nat.div_le_self n 262144
          omega
        calc
          n / 262144 ≤ 2 ^ Nat.log 2 n := hhalf
          _ = 2 ^ Nat.log 2 n * 1 := by ring
          _ ≤ 2 ^ Nat.log 2 n * singleEarlySeedUnit n γ :=
            Nat.mul_le_mul_left _ (le_max_left 1 _))

theorem singleEarlyScale_guard
    (n γ i : ℕ) (hi : i < singleEarlyStages n γ) :
    131072 * singleEarlyScale n γ i ≤ n := by
  have hlt := singleEarlyScale_lt_final n γ i hi
  have hle : singleEarlyScale n γ i + 1 ≤ n / 262144 := hlt
  calc
    131072 * singleEarlyScale n γ i ≤ 262144 * singleEarlyScale n γ i := by
      exact Nat.mul_le_mul_right _ (by norm_num)
    _ ≤ 262144 * (n / 262144) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ n := Nat.mul_div_le n 262144

/-- Fixed early Single-B target gap: `132·(n/2^18)`. -/
def SingleEarlyTarget (n : ℕ) (s : SingleState n) : Prop :=
  SingleGapCheckpoint n (132 * (n / 262144)) s

instance (n : ℕ) : DecidablePred (SingleEarlyTarget n) := fun _ =>
  inferInstanceAs (Decidable (_ ≤ _))

/-- Raw horizon of the early Single-B ladder. -/
def singleEarlyLadderHorizon (n γ : ℕ) : ℕ :=
  singleEarlyStages n γ * (132 * singleWideHorizon n (n / 8))

/-- Error of the early Single-B ladder. -/
noncomputable def singleEarlyLadderError (n γ : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (singleEarlyStages n γ),
    132 * (8 * singleGapEnvelope n (singleEarlyScale n γ j))

/-- **The Single-B early dyadic ladder.** -/
theorem singleEarly_ladder
    (n : ℕ) (hn : 2 ≤ n) (γ : ℕ) :
    Reaches (singleStateStep n hn) (singleEarlyLadderHorizon n γ)
      (SingleGapCheckpoint n (132 * singleEarlySeedUnit n γ))
      (SingleEarlyTarget n)
      (singleEarlyLadderError n γ) := by
  have hrungs : ∀ j < singleEarlyStages n γ,
      Reaches (singleStateStep n hn) (132 * singleWideHorizon n (n / 8))
        (fun s => SingleGapCheckpoint n
          (132 * singleEarlyScale n γ j) s)
        (fun s => SingleGapCheckpoint n
          (132 * singleEarlyScale n γ (j + 1)) s)
        (132 * (8 * singleGapEnvelope n (singleEarlyScale n γ j))) := by
    intro j hj
    exact singleEarly_stage n γ j hn (singleEarlyScale_guard n γ j hj)
  have hchain :=
    Reaches.chain
      (K := singleStateStep n hn)
      (P := fun j => SingleGapCheckpoint n (132 * singleEarlyScale n γ j))
      (T := fun _ => 132 * singleWideHorizon n (n / 8))
      (ε := fun j => 132 * (8 * singleGapEnvelope n (singleEarlyScale n γ j)))
      hrungs
  have hpost := hchain.mono_post (by
    intro z hz
    show SingleEarlyTarget n z
    unfold SingleGapCheckpoint at hz
    unfold SingleEarlyTarget SingleGapCheckpoint
    have hfinal := singleEarlyScale_final n γ
    have hmul : 132 * (n / 262144) ≤
        132 * singleEarlyScale n γ (singleEarlyStages n γ) :=
      Nat.mul_le_mul_left 132 hfinal
    omega)
  intro s hs
  have hentry : SingleGapCheckpoint n (132 * singleEarlyScale n γ 0) s := by
    unfold SingleGapCheckpoint at hs ⊢
    unfold singleEarlyScale
    simpa using hs
  have hres := hpost s hentry
  have hHsum :
      (∑ _j ∈ Finset.range (singleEarlyStages n γ),
        132 * singleWideHorizon n (n / 8)) =
        singleEarlyLadderHorizon n γ := by
    rw [Finset.sum_const, Finset.card_range]
    unfold singleEarlyLadderHorizon
    ring
  rw [hHsum] at hres
  exact hres

/-! ## Seed entry from the paper premise -/

/-- The seed unit clears `132` under a moderate log bound. -/
theorem singleEarlySeedUnit_entry
    {n γ : ℕ} (hlog : 30 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (s : SingleState n) (gap : ℕ)
    (hxy : s.1.y + gap ≤ s.1.x)
    (hgapSq : γ * n * Nat.log 2 n ≤ gap ^ 2) :
    SingleGapCheckpoint n (132 * singleEarlySeedUnit n γ) s := by
  have hseedGap : phase1SeedR n γ ≤ gap :=
    phase1SeedR_le_of_sq
      (by simpa [phase1SeedRadicand] using hgapSq)
  have hn30 : 2 ^ 30 ≤ n := by
    calc
      (2 : ℕ) ^ 30 ≤ 2 ^ Nat.log 2 n :=
        Nat.pow_le_pow_right (by norm_num) hlog
      _ ≤ n := Nat.pow_log_le_self 2 (by
        intro h0
        rw [h0, Nat.log_zero_right] at hlog
        omega)
  have hseed132 : 132 ≤ phase1SeedR n γ := by
    have hrad : 132 ^ 2 ≤ phase1SeedRadicand n γ := by
      unfold phase1SeedRadicand
      calc
        132 ^ 2 = 17424 := by norm_num
        _ ≤ 1 * 2 ^ 30 * 30 := by norm_num
        _ ≤ γ * n * Nat.log 2 n :=
          Nat.mul_le_mul (Nat.mul_le_mul hγ hn30) hlog
    have hsqrt : 132 ≤ Nat.sqrt (phase1SeedRadicand n γ) :=
      (Nat.le_sqrt').mpr hrad
    unfold phase1SeedR
    dsimp only
    split_ifs <;> omega
  have hunit : singleEarlySeedUnit n γ = phase1SeedR n γ / 132 := by
    unfold singleEarlySeedUnit
    rw [max_eq_right]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 132)]
    omega
  have h132 : 132 * singleEarlySeedUnit n γ ≤ phase1SeedR n γ := by
    rw [hunit]
    exact Nat.mul_div_le _ _
  unfold SingleGapCheckpoint
  have hinv := s.2
  simp only [BiCfg.DoubleInv] at hinv
  simp only [BiCfg.doubleLevel]
  omega

/-- Paper-style Single-B initial gap in physical coordinates. -/
def SingleBEarlyInitial (n γ : ℕ) (s : SingleState n) : Prop :=
  ∃ gap : ℕ,
    s.1.y + gap ≤ s.1.x ∧
      γ * n * Nat.log 2 n ≤ gap ^ 2

/-- The early ladder started from the paper premise. -/
theorem singleEarly_reaches
    (n : ℕ) (hn : 2 ≤ n) (γ : ℕ)
    (hlog : 30 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    Reaches (singleStateStep n hn) (singleEarlyLadderHorizon n γ)
      (SingleBEarlyInitial n γ)
      (SingleEarlyTarget n)
      (singleEarlyLadderError n γ) := by
  have hl := singleEarly_ladder n hn γ
  intro s hs
  obtain ⟨gap, hxy, hgapSq⟩ := hs
  exact hl s (singleEarlySeedUnit_entry hlog hγ s gap hxy hgapSq)

/-! ## Ladder error and horizon envelopes -/

/-- Every stage envelope is dominated by the seed envelope. -/
theorem singleEarlyLadderError_le_first
    (n γ : ℕ) (hn : 0 < n) :
    singleEarlyLadderError n γ ≤
      ENNReal.ofReal
        ((1056 : ℝ) * (Nat.log 2 n : ℝ) *
          Real.exp
            (-((singleEarlySeedUnit n γ : ℝ) ^ 2 / (1024 * (n : ℝ))))) := by
  unfold singleEarlyLadderError
  have hterm : ∀ j ∈ Finset.range (singleEarlyStages n γ),
      132 * (8 * singleGapEnvelope n (singleEarlyScale n γ j)) ≤
        ENNReal.ofReal
          ((1056 : ℝ) *
            Real.exp
              (-((singleEarlySeedUnit n γ : ℝ) ^ 2 /
                (1024 * (n : ℝ))))) := by
    intro j _hj
    have hscale : singleEarlySeedUnit n γ ≤ singleEarlyScale n γ j := by
      unfold singleEarlyScale
      calc
        singleEarlySeedUnit n γ = 1 * singleEarlySeedUnit n γ := by ring
        _ ≤ 2 ^ j * singleEarlySeedUnit n γ :=
          Nat.mul_le_mul_right _ (Nat.one_le_two_pow)
    have henv : singleGapEnvelope n (singleEarlyScale n γ j) ≤
        ENNReal.ofReal
          (Real.exp
            (-((singleEarlySeedUnit n γ : ℝ) ^ 2 / (1024 * (n : ℝ))))) := by
      unfold singleGapEnvelope
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff]
      have hscaleR : (singleEarlySeedUnit n γ : ℝ) ≤
          (singleEarlyScale n γ j : ℝ) := by exact_mod_cast hscale
      have h0 : (0 : ℝ) ≤ (singleEarlySeedUnit n γ : ℝ) := by positivity
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ h0 hscaleR 2
    calc
      132 * (8 * singleGapEnvelope n (singleEarlyScale n γ j))
          ≤ 132 * (8 * ENNReal.ofReal
              (Real.exp
                (-((singleEarlySeedUnit n γ : ℝ) ^ 2 /
                  (1024 * (n : ℝ)))))) := by
        exact mul_le_mul_left' (mul_le_mul_left' henv 8) 132
      _ = ENNReal.ofReal
            ((1056 : ℝ) *
              Real.exp
                (-((singleEarlySeedUnit n γ : ℝ) ^ 2 /
                  (1024 * (n : ℝ))))) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1056),
          ENNReal.ofReal_ofNat]
        ring
  calc
    (∑ j ∈ Finset.range (singleEarlyStages n γ),
        132 * (8 * singleGapEnvelope n (singleEarlyScale n γ j)))
        ≤ ∑ _j ∈ Finset.range (singleEarlyStages n γ),
            ENNReal.ofReal
              ((1056 : ℝ) *
                Real.exp
                  (-((singleEarlySeedUnit n γ : ℝ) ^ 2 /
                    (1024 * (n : ℝ))))) :=
      Finset.sum_le_sum hterm
    _ = (singleEarlyStages n γ : ℝ≥0∞) *
          ENNReal.ofReal
            ((1056 : ℝ) *
              Real.exp
                (-((singleEarlySeedUnit n γ : ℝ) ^ 2 /
                  (1024 * (n : ℝ))))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal
          ((1056 : ℝ) * (Nat.log 2 n : ℝ) *
            Real.exp
              (-((singleEarlySeedUnit n γ : ℝ) ^ 2 /
                (1024 * (n : ℝ))))) := by
      have hstages := singleEarlyStages_le_log n γ
      calc
        (singleEarlyStages n γ : ℝ≥0∞) *
            ENNReal.ofReal
              ((1056 : ℝ) *
                Real.exp
                  (-((singleEarlySeedUnit n γ : ℝ) ^ 2 /
                    (1024 * (n : ℝ)))))
            ≤ (Nat.log 2 n : ℝ≥0∞) *
              ENNReal.ofReal
                ((1056 : ℝ) *
                  Real.exp
                    (-((singleEarlySeedUnit n γ : ℝ) ^ 2 /
                      (1024 * (n : ℝ))))) := by
          exact mul_le_mul_right' (by exact_mod_cast hstages) _
        _ = ENNReal.ofReal
              ((1056 : ℝ) * (Nat.log 2 n : ℝ) *
                Real.exp
                  (-((singleEarlySeedUnit n γ : ℝ) ^ 2 /
                    (1024 * (n : ℝ))))) := by
          rw [show (Nat.log 2 n : ℝ≥0∞) =
              ENNReal.ofReal ((Nat.log 2 n : ℕ) : ℝ) from
                (ENNReal.ofReal_natCast _).symm]
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring

/-- Horizon envelope: the early ladder is `O(n·lg n)`, γ-free per rung. -/
theorem singleEarlyLadderHorizon_le (n γ : ℕ) :
    singleEarlyLadderHorizon n γ ≤ 42240 * n * Nat.log 2 n := by
  unfold singleEarlyLadderHorizon
  have hT : singleWideHorizon n (n / 8) ≤ 320 * n := by
    rw [singleWideHorizon_linear]
    have := Nat.mul_div_le n 8
    omega
  have hstages := singleEarlyStages_le_log n γ
  calc
    singleEarlyStages n γ * (132 * singleWideHorizon n (n / 8))
        ≤ Nat.log 2 n * (132 * (320 * n)) := by
      exact Nat.mul_le_mul hstages (Nat.mul_le_mul_left _ hT)
    _ = 42240 * n * Nat.log 2 n := by ring

section Inhabitation

example : singleEarlySeedUnit (2 ^ 30) 1 = max 1 (phase1SeedR (2 ^ 30) 1 / 132) :=
  rfl

end Inhabitation

end Tri

#print axioms Tri.singleGapChain
#print axioms Tri.singleGapChain_structural
#print axioms Tri.singleGapChain_structural256
#print axioms Tri.singleEarly_stage
#print axioms Tri.singleEarly_ladder
#print axioms Tri.singleEarlySeedUnit_entry
#print axioms Tri.singleEarly_reaches
#print axioms Tri.singleEarlyLadderError_le_first
#print axioms Tri.singleEarlyLadderHorizon_le
