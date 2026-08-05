/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedBinaryMonotone
import Tri.RelaxedBandScalarConstructor
import Tri.StoppedHitMonotone
import Tri.ByzantineJointLaw
import Tri.ByzantinePhase2Bridge
import Tri.ByzantinePhase2ClockFloor

/-!
# Unconditional buffered Phase-II rungs

The paper's short productive-quota interface cannot close a Phase-II dyadic
rung: at the first checkpoint an adverse first productive move can cross the
global `3n/4` boundary, and `n/K` productive moves are shorter than the
Lemma-7 drift deadline.  This module instead uses the rung-local Feller buffer
and the raw-time relaxed-band theorem.

On every live fixed-`z` state, the paper-worst `X` marginal stochastically
dominates the relaxed chain with firing rate `1/2`.  Starting-point
monotonicity extends the exact relaxed rung from its standard anchor to the
whole current Byzantine checkpoint.  The resulting rungs and finite ladder
have no caller-supplied liveness, clock-floor, or productive-success premise.
-/

namespace Tri.Byzantine

open scoped BigOperators ENNReal NNReal

noncomputable section

variable {n B z : ℕ}

instance controlledJointStrongXEntryDecidable :
    DecidablePred
      (fun r : ControlledJointState n B => StrongXEntry r.2) := by
  intro r
  unfold StrongXEntry
  infer_instance

instance controlledJointRelaxedXConsensusDecidable :
    DecidablePred
      (fun r : ControlledJointState n B =>
        RelaxedXConsensus r.2) := by
  intro r
  unfold RelaxedXConsensus
  infer_instance

/-- Fixed half-rate comparison chain used throughout Byzantine Phase II. -/
noncomputable def phase2HalfRate : RelaxedRate where
  fire := 1 / 2
  idle := 1 / 2
  add_eq_one := by norm_num

@[simp] theorem phase2HalfRate_fire :
    phase2HalfRate.fire = (1 / 2 : NNReal) :=
  rfl

/-- The aggregate-minority scale associated with dyadic denominator `K_j`. -/
def phase2DyadicMinorityScale (n j : ℕ) : ℕ :=
  n / phase2DyadicK j

/-- Buffered lower boundary for one Phase-II rung. -/
def Phase2DyadicBufferedBad
    (d j : ℕ) (q : Phase2Level n B z) : Prop :=
  State.x q.1 ≤
    relaxedDyadicLower n (phase2DyadicMinorityScale n j) d

instance phase2DyadicBufferedBadDecidable (d j : ℕ) :
    DecidablePred
      (Phase2DyadicBufferedBad (n := n) (B := B) (z := z) d j) := by
  intro q
  unfold Phase2DyadicBufferedBad
  infer_instance

/-- Count form of the same buffered lower boundary. -/
def Phase2CountBufferedBad (n P d x : ℕ) : Prop :=
  x ≤ relaxedDyadicLower n P d

instance phase2CountBufferedBadDecidable (n P d : ℕ) :
    DecidablePred (Phase2CountBufferedBad n P d) := by
  intro x
  unfold Phase2CountBufferedBad
  infer_instance

theorem terminalFailureMass_congr_predicate
    {α : Type*} (p : PMF α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x ↔ Q x) :
    terminalFailureMass p P = terminalFailureMass p Q := by
  unfold terminalFailureMass
  apply tsum_congr
  intro x
  by_cases hx : P x
  · rw [if_pos hx, if_pos ((h x).1 hx)]
  · rw [if_neg hx, if_neg (fun hq => hx ((h x).2 hq))]

theorem phase2DyadicK_pos (j : ℕ) :
    0 < phase2DyadicK j := by
  simp [phase2DyadicK]

theorem phase2DyadicK_ge_four (j : ℕ) :
    4 ≤ phase2DyadicK j := by
  unfold phase2DyadicK
  have hpow : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  nlinarith

theorem phase2DyadicMinorityScale_pos
    (j : ℕ) (hKle : phase2DyadicK j ≤ n) :
    1 ≤ phase2DyadicMinorityScale n j := by
  unfold phase2DyadicMinorityScale
  apply (Nat.le_div_iff_mul_le (phase2DyadicK_pos j)).2
  simpa using hKle

/-- Failure of strong entry forces the canonical effective firing rate above
one half. -/
theorem phase2HalfRate_fire_le_effective
    (q : Phase2Level n B z)
    (hstrong : ¬ Phase2StrongTarget q) :
    phase2HalfRate.fire ≤ (phase2PaperEffectiveRate q).fire := by
  have hyz : State.z q.1 < State.y q.1 := by
    apply Nat.lt_of_not_ge
    intro h
    exact hstrong ((phase2StrongTarget_iff_y_le_z q).2 h)
  have hm : State.y q.1 + State.z q.1 ≠ 0 := by omega
  simp only [phase2HalfRate_fire, phase2PaperEffectiveRate, hm,
    ↓reduceDIte]
  rw [div_le_div_iff₀ (by norm_num : (0 : NNReal) < 2)
    (by positivity :
      (0 : NNReal) <
        (State.y q.1 + State.z q.1 : ℕ))]
  have hpair :
      ((State.y q.1 + State.z q.1 : ℕ) : NNReal) ≤
        2 * (State.y q.1 : NNReal) := by
    exact_mod_cast (by omega :
      State.y q.1 + State.z q.1 ≤ 2 * State.y q.1)
  simpa [mul_comm] using hpair

/-- On a physical fixed-fibre count, the canonical paper-worst `X` marginal
is exactly the raw relaxed chain at its state-dependent effective rate. -/
theorem phase1XStep_eq_relaxed_effective
    (h3 : 3 ≤ n) (base q : Phase2Level n B z) :
    phase1XStep h3 base (State.x q.1) =
      relaxedTriChain (phase2PaperEffectiveRate q) n
        (State.x q.1) := by
  rw [phase1XStep_of_level h3 base q]
  rw [paperWorst_step_map_x_eq_relaxedTriStep
    (phase2PaperEffectiveRate q) q.1 h3
    (phase2PaperEffectiveRate_spec q)]
  unfold relaxedTriChain
  rw [dif_pos ⟨h3, State.x_le q.1⟩]
  congr 1
  have ht := State.total q.1
  omega

/-- Before either buffered failure or the next rung target, the half-rate raw
relaxed chain is stochastically dominated by the paper-worst fixed-fibre
`X` marginal. -/
theorem phase2HalfRate_expect_le_phase1XStep
    (h3 : 3 ≤ n) (base : Phase2Level n B z)
    (P d Knext x : ℕ)
    (_hbad : ¬ Phase2CountBufferedBad n P d x)
    (hgood : ¬ Phase2CountRungTarget n z Knext x)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (relaxedTriChain phase2HalfRate n x) F ≤
      expect (phase1XStep h3 base x) F := by
  have hxz : x + z ≤ n := by
    unfold Phase2CountRungTarget at hgood
    push Not at hgood
    omega
  let q : Phase2Level n B z :=
    phase1LevelWithX base x hxz
  have hxq : State.x q.1 = x := rfl
  have hstrong : ¬ Phase2StrongTarget q := by
    intro h
    have hyz := (phase2StrongTarget_iff_y_le_z q).1 h
    unfold Phase2CountRungTarget at hgood
    push Not at hgood
    have ht := State.total q.1
    have hzq : State.z q.1 = z := q.2
    omega
  have hfire :=
    phase2HalfRate_fire_le_effective q hstrong
  calc
    expect (relaxedTriChain phase2HalfRate n x) F =
        expect (relaxedTriChain phase2HalfRate n (State.x q.1)) F := by
          rw [hxq]
    _ ≤ expect
          (relaxedTriChain (phase2PaperEffectiveRate q) n
            (State.x q.1)) F :=
      expect_relaxedTriChain_mono_fire
        phase2HalfRate (phase2PaperEffectiveRate q)
        n (State.x q.1) hfire F hF
    _ = expect (phase1XStep h3 base x) F := by
      rw [← phase1XStep_eq_relaxed_effective h3 base q, hxq]

/-- The Phase-II dyadic rung multiplier chosen from the fixed scalar
certificate and the paper buffer `d`. -/
def phase2BufferedRungMultiplier
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d n j : ℕ) : ℕ :=
  relaxedDyadicAdaptiveMultiplier S.R₀ d
    (phase2DyadicMinorityScale n j)

/-- Raw horizon of one buffered Byzantine Phase-II rung. -/
def phase2BufferedRungHorizon
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d n j : ℕ) : ℕ :=
  relaxedDyadicHorizon
    (S.C * phase2BufferedRungMultiplier S d n j) n

/-- Exact three-branch error of one buffered Byzantine Phase-II rung. -/
noncomputable def phase2BufferedRungError
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d n j : ℕ) : ℝ≥0∞ :=
  let P := phase2DyadicMinorityScale n j
  let R := phase2BufferedRungMultiplier S d n j
  relaxedDyadicBandError phase2HalfRate n P d R (S.C * R)
    (6 / 5 : NNReal) 0

/-- The arithmetic corner estimate used by every buffered Phase-II rung.
Exact divisibility is unnecessary; `K P ≤ n` is the right floor-division
interface. -/
theorem phase2_floor_scalar_of_le
    (K n P d xLo : ℕ)
    (hK : 4 ≤ K)
    (hshare : K * P ≤ n)
    (hden : P + d + xLo = n)
    (hlarge : 68 * d ≤ 3 * n) :
    12 * (P + d) ≤ 5 * xLo := by
  have hquarter : 4 * P ≤ n := by
    exact (Nat.mul_le_mul_right P hK).trans hshare
  omega

theorem phase2Buffered_room
    (K n P d : ℕ)
    (hK : 4 ≤ K)
    (hshare : K * P ≤ n)
    (hlarge : 68 * d ≤ 3 * n) :
    2 * (P + d) ≤ n := by
  have hquarter : 4 * P ≤ n := by
    exact (Nat.mul_le_mul_right P hK).trans hshare
  omega

theorem phase2HalfRate_corner
    (K n P d : ℕ)
    (hP : 1 ≤ P) (hd : 1 ≤ d)
    (hK : 4 ≤ K)
    (hshare : K * P ≤ n)
    (hlarge : 68 * d ≤ 3 * n) :
    (6 / 5 : NNReal) *
        (relaxedDyadicBHi P d + 1 : NNReal) ≤
      phase2HalfRate.fire *
        (relaxedDyadicLower n P d + 1 : NNReal) := by
  have hroom := phase2Buffered_room K n P d hK hshare hlarge
  have hsum :
      P + d + relaxedDyadicLower n P d = n := by
    unfold relaxedDyadicLower
    omega
  have hscalar :
      12 * (P + d) ≤
        5 * relaxedDyadicLower n P d :=
    phase2_floor_scalar_of_le K n P d
      (relaxedDyadicLower n P d) hK hshare hsum hlarge
  have hnat :
      12 * (relaxedDyadicBHi P d + 1) ≤
        5 * (relaxedDyadicLower n P d + 1) := by
    unfold relaxedDyadicBHi
    omega
  rw [phase2HalfRate_fire, div_mul_eq_mul_div,
    div_mul_eq_mul_div]
  rw [div_le_div_iff₀ (by norm_num : (0 : NNReal) < 5)
    (by norm_num : (0 : NNReal) < 2)]
  have hnat' :
      2 * (6 * (relaxedDyadicBHi P d + 1)) ≤
        5 * (relaxedDyadicLower n P d + 1) := by
    omega
  have hcast :
      (2 : NNReal) *
          (6 * (relaxedDyadicBHi P d + 1 : NNReal)) ≤
        5 * (relaxedDyadicLower n P d + 1 : NNReal) := by
    exact_mod_cast hnat'
  simpa [mul_assoc, mul_comm, mul_left_comm] using hcast

/-- The scalar margin remains valid after increasing the adaptive rung
multiplier above its schedule-wide base value. -/
theorem phase2BufferedRung_margin
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d P : ℕ) :
    (1 : NNReal) +
        1 / (relaxedDyadicAdaptiveMultiplier S.R₀ d P : NNReal) ≤
      (6 / 5 : NNReal) := by
  have hbase :
      S.R₀ ≤ relaxedDyadicAdaptiveMultiplier S.R₀ d P :=
    relaxedDyadicAdaptiveMultiplier_ge_base S.R₀ d P
  have hbasePos : (0 : NNReal) < (S.R₀ : NNReal) := by
    exact_mod_cast
      (show 0 < S.R₀ from
        lt_of_lt_of_le Nat.zero_lt_one S.hR₀)
  have hcast :
      (S.R₀ : NNReal) ≤
        (relaxedDyadicAdaptiveMultiplier S.R₀ d P : NNReal) := by
    exact_mod_cast hbase
  have hrecip :
      (1 : NNReal) /
          (relaxedDyadicAdaptiveMultiplier S.R₀ d P : NNReal) ≤
        1 / (S.R₀ : NNReal) :=
    one_div_le_one_div_of_le hbasePos hcast
  have hadd :
      (1 : NNReal) +
          1 /
            (relaxedDyadicAdaptiveMultiplier S.R₀ d P : NNReal) ≤
        1 + 1 / (S.R₀ : NNReal) := by
    simpa [add_comm] using add_le_add_left hrecip 1
  exact hadd.trans S.hmargin

/-- Reaching the usual relaxed upper boundary is enough for the next
fixed-fibre Byzantine aggregate cap. -/
theorem phase2CountRungTarget_of_relaxedDyadicTarget
    (K n P z x : ℕ)
    (hshare : K * P ≤ n)
    (hx : relaxedDyadicTarget n P ≤ x) :
    Phase2CountRungTarget n z (2 * K) x := by
  right
  by_cases hxn : n ≤ x
  · exact (Nat.mul_le_mul_left (2 * K) hxn).trans
      (Nat.le_add_right _ _)
  · have hxn' : x ≤ n := by omega
    have hminor : n - x ≤ P / 2 := by
      unfold relaxedDyadicTarget at hx
      omega
    have hrem :
        (2 * K) * (n - x) ≤ n := by
      calc
        (2 * K) * (n - x) ≤
            (2 * K) * (P / 2) :=
          Nat.mul_le_mul_left (2 * K) hminor
        _ = K * (2 * (P / 2)) := by ring
        _ ≤ K * P := by
          exact Nat.mul_le_mul_left K (Nat.mul_div_le P 2)
        _ ≤ n := hshare
    have hdecomp : x + (n - x) = n := by omega
    calc
      (2 * K) * n =
          (2 * K) * x + (2 * K) * (n - x) := by
        rw [← Nat.mul_add, hdecomp]
      _ ≤ (2 * K) * x + n :=
        Nat.add_le_add_left hrem _

/-- A current dyadic aggregate cap places the count at or above the standard
relaxed starting point for the floor scale `n / K`. -/
theorem relaxedDyadicStart_le_of_phase2CountCap
    (K n x : ℕ)
    (hK : 0 < K)
    (hcap : K * n ≤ K * x + n) :
    relaxedDyadicStart n (n / K) ≤ x := by
  by_cases hxn : n ≤ x
  · exact (Nat.sub_le n (n / K)).trans hxn
  · have hxn' : x ≤ n := by omega
    have hdecomp : x + (n - x) = n := by omega
    have hrem : K * (n - x) ≤ n := by
      have hcap' :
          K * x + K * (n - x) ≤ K * x + n := by
        simpa [← Nat.mul_add, hdecomp] using hcap
      exact Nat.le_of_add_le_add_left hcap'
    have hminor : n - x ≤ n / K :=
      (Nat.le_div_iff_mul_le hK).2 (by
        simpa [Nat.mul_comm] using hrem)
    unfold relaxedDyadicStart
    omega

/-- One buffered raw-time Phase-II rung on the fixed-`z` count chain.  All
probabilistic premises are discharged internally by comparison with the
half-rate relaxed chain. -/
theorem phase2_count_buffered_dyadic_rung
    (h3 : 3 ≤ n)
    (base : Phase2Level n B z)
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d j : ℕ)
    (hd : 1 ≤ d)
    (hKle : phase2DyadicK j ≤ n)
    (hlarge : 68 * d ≤ 3 * n) :
    Reaches
      (freeze
        (Phase2CountRungTarget n z (2 * phase2DyadicK j))
        (phase1XStep h3 base))
      (phase2BufferedRungHorizon S d n j)
      (Phase2CountRungTarget n z (phase2DyadicK j))
      (Phase2CountRungTarget n z (2 * phase2DyadicK j))
      (phase2BufferedRungError S d n j) := by
  let K := phase2DyadicK j
  let P := phase2DyadicMinorityScale n j
  let R := phase2BufferedRungMultiplier S d n j
  let T := phase2BufferedRungHorizon S d n j
  let Bad := Phase2CountBufferedBad n P d
  let GoodCap := fun x : ℕ => relaxedDyadicTarget n P ≤ x
  let Good := Phase2CountRungTarget n z (2 * K)
  let Pre := Phase2CountRungTarget n z K
  let Kref := relaxedTriChain phase2HalfRate n
  let Kdom := phase1XStep h3 base
  have hKpos : 0 < K := by
    exact phase2DyadicK_pos j
  have hK4 : 4 ≤ K := by
    exact phase2DyadicK_ge_four j
  have hP : 1 ≤ P := by
    exact phase2DyadicMinorityScale_pos j hKle
  have hshare : K * P ≤ n := by
    simpa [K, P, phase2DyadicMinorityScale] using
      (Nat.mul_div_le n (phase2DyadicK j))
  have hroom : 2 * (P + d) ≤ n :=
    phase2Buffered_room K n P d hK4 hshare hlarge
  have hRbase : S.R₀ ≤ R := by
    exact relaxedDyadicAdaptiveMultiplier_ge_base S.R₀ d P
  have hR : 1 ≤ R := S.hR₀.trans hRbase
  have hmargin :
      (1 : NNReal) + 1 / (R : NNReal) ≤
        (6 / 5 : NNReal) := by
    exact phase2BufferedRung_margin S d P
  have hcorner :
      (6 / 5 : NNReal) *
          (relaxedDyadicBHi P d + 1 : NNReal) ≤
        phase2HalfRate.fire *
          (relaxedDyadicLower n P d + 1 : NNReal) :=
    phase2HalfRate_corner K n P d hP hd hK4 hshare hlarge
  have hrel :
      Reaches
        (freeze
          (fun x : ℕ => Bad x ∨ GoodCap x)
          Kref)
        T
        (fun x => x = relaxedDyadicStart n P)
        GoodCap
        (phase2BufferedRungError S d n j) := by
    simpa [Bad, GoodCap, Kref, T, R,
      phase2BufferedRungHorizon, phase2BufferedRungError,
      phase2BufferedRungMultiplier, P] using
      (relaxedDyadicBand_physical_reaches
        phase2HalfRate n P d R (S.C * R)
        (6 / 5 : NNReal) 0 0
        hP hd hR hroom
        (by
          rw [← NNReal.coe_le_coe]
          push_cast
          norm_num)
        (by
          have :
              phase2HalfRate.fire ≤ (6 / 5 : NNReal) := by
            rw [phase2HalfRate_fire, ← NNReal.coe_le_coe]
            push_cast
            norm_num
          simpa using this)
        (by simp)
        (by simpa using hmargin)
        hcorner)
  have hBadLower :
      ∀ ⦃i k : ℕ⦄, i ≤ k → Bad k → Bad i := by
    intro i k hik hk
    exact hik.trans hk
  have hGoodUpper :
      ∀ ⦃i k : ℕ⦄, i ≤ k → GoodCap i → GoodCap k := by
    intro i k hik hi
    exact hi.trans hik
  have hcapGood : ∀ x, GoodCap x → Good x := by
    intro x hx
    exact phase2CountRungTarget_of_relaxedDyadicTarget
      K n P z x hshare hx
  have href :
      ∀ s, Pre s →
        terminalFailureMass
            (iter (freeze (fun x => Bad x ∨ Good x) Kref) T s)
            Good ≤
          phase2BufferedRungError S d n j := by
    intro s hs
    by_cases hgood : Good s
    · rw [iter_targetFreeze_of_mem
        (fun x => Bad x ∨ Good x) Kref s (Or.inr hgood) T]
      simp [terminalFailureMass_pure, hgood]
    · have hcap : K * n ≤ K * s + n := by
        unfold Pre Phase2CountRungTarget at hs
        rcases hs with hstrong | hcap
        · exact False.elim (hgood (Or.inl hstrong))
        · exact hcap
      have hstart :
          relaxedDyadicStart n P ≤ s := by
        simpa [P, K, phase2DyadicMinorityScale] using
          (relaxedDyadicStart_le_of_phase2CountCap
            K n s hKpos hcap)
      calc
        terminalFailureMass
              (iter (freeze (fun x => Bad x ∨ Good x) Kref) T s)
              Good ≤
            terminalFailureMass
              (iter
                (freeze (fun x => Bad x ∨ GoodCap x) Kref)
                T s)
              GoodCap :=
          stoppedBand_failure_mono_good
            Bad GoodCap Good Kref hcapGood T s
        _ ≤ terminalFailureMass
              (iter
                (freeze (fun x => Bad x ∨ GoodCap x) Kref)
                T (relaxedDyadicStart n P))
              GoodCap :=
          stoppedBand_failure_antitone_start
            Bad GoodCap Kref hBadLower hGoodUpper
            (fun F hF =>
              relaxedTriChain_expect_monotone
                phase2HalfRate n F hF)
            T hstart
        _ ≤ phase2BufferedRungError S d n j :=
          hrel (relaxedDyadicStart n P) rfl
  have hreach :
      Reaches
        (freeze Good Kdom)
        T Pre Good
        (phase2BufferedRungError S d n j) := by
    exact reaches_targetFreeze_of_live_stochDom
      Bad Good Pre Kref Kdom
      hBadLower
      (by
        intro i k hik hi
        unfold Good Phase2CountRungTarget at hi ⊢
        rcases hi with hi | hi
        · left
          omega
        · right
          exact hi.trans (Nat.add_le_add_right
            (Nat.mul_le_mul_left (2 * K) hik) n))
      (fun F hF =>
        relaxedTriChain_expect_monotone phase2HalfRate n F hF)
      (fun i hbad hgood F hF =>
        phase2HalfRate_expect_le_phase1XStep
          h3 base P d (2 * K) i hbad hgood F hF)
      T (phase2BufferedRungError S d n j) href
  simpa [Good, Pre, Kdom, T, K] using hreach

theorem phase2DyadicK_succ (j : ℕ) :
    phase2DyadicK (j + 1) = 2 * phase2DyadicK j := by
  simp [phase2DyadicK, pow_succ]
  ring

/-- The fixed-`z` count target and the fibre-level ladder target are the same
predicate under the `X` projection. -/
theorem phase2CountRungTarget_iff_ladder
    (j : ℕ) (q : Phase2Level n B z) :
    Phase2CountRungTarget n z (phase2DyadicK j) (State.x q.1) ↔
      Phase2LadderTarget (n := n) (B := B) (z := z) j q := by
  have hcount :=
    phase2CountRungTarget_iff_state
      (n := n) (B := B) (phase2DyadicK j) q.1
  rw [q.2] at hcount
  simpa [Phase2LadderTarget, Phase2DyadicCheckpoint,
    Phase2PhysRungTarget, phase2StrongTarget_iff_y_le_z] using hcount

/-- Fibre-level unconditional buffered Phase-II rung.  Unlike the older raw
rung interface, this theorem has no caller-supplied liveness, clock-floor, or
productive-success premise. -/
theorem phase2_reference_buffered_dyadic_rung
    (h3 : 3 ≤ n)
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d j : ℕ)
    (hd : 1 ≤ d)
    (hKle : phase2DyadicK j ≤ n)
    (hlarge : 68 * d ≤ 3 * n) :
    Reaches
      (freeze
        (Phase2LadderTarget (n := n) (B := B) (z := z) (j + 1))
        (phase2ReferenceStep (n := n) (B := B) (z := z) h3))
      (phase2BufferedRungHorizon S d n j)
      (Phase2LadderTarget (n := n) (B := B) (z := z) j)
      (Phase2LadderTarget (n := n) (B := B) (z := z) (j + 1))
      (phase2BufferedRungError S d n j) := by
  let GoodState :=
    Phase2LadderTarget (n := n) (B := B) (z := z) (j + 1)
  let GoodCount :=
    Phase2CountRungTarget n z (2 * phase2DyadicK j)
  let Kstate :=
    freeze GoodState
      (phase2ReferenceStep (n := n) (B := B) (z := z) h3)
  intro q hq
  let base : Phase2Level n B z := q
  have hcount :=
    phase2_count_buffered_dyadic_rung
      (n := n) (B := B) (z := z)
      h3 base S d j hd hKle hlarge
  have hpre :
      Phase2CountRungTarget n z
        (phase2DyadicK j) (State.x q.1) :=
    (phase2CountRungTarget_iff_ladder j q).2 hq
  have hgood :
      ∀ r : Phase2Level n B z,
        GoodState r ↔ GoodCount (State.x r.1) := by
    intro r
    change
      Phase2LadderTarget (n := n) (B := B) (z := z) (j + 1) r ↔
        Phase2CountRungTarget n z
          (2 * phase2DyadicK j) (State.x r.1)
    rw [← phase2DyadicK_succ j]
    exact (phase2CountRungTarget_iff_ladder (j + 1) r).symm
  let Kcount' :=
    freeze GoodCount (phase1XStep h3 base)
  have hstep :
      ∀ r : Phase2Level n B z,
        (Kstate r).map (fun s => State.x s.1) =
          Kcount' (State.x r.1) := by
    intro r
    dsimp only [Kstate, Kcount']
    by_cases hr : GoodState r
    · have hrc : GoodCount (State.x r.1) := (hgood r).1 hr
      rw [freeze_of_mem r hr,
        freeze_of_mem (State.x r.1) hrc, PMF.pure_map]
    · have hrc : ¬ GoodCount (State.x r.1) := by
        exact fun h => hr ((hgood r).2 h)
      rw [freeze_of_not_mem r hr,
        freeze_of_not_mem (State.x r.1) hrc]
      change
        (phase1ReferenceStep h3 r).map
            (fun s => State.x s.1) =
          phase1XStep h3 base (State.x r.1)
      rw [phase1ReferenceStep_map_x,
        ← phase1XStep_of_level h3 base r]
  have hmap :
      (iter Kstate
          (phase2BufferedRungHorizon S d n j) q).map
          (fun s => State.x s.1) =
        iter Kcount'
          (phase2BufferedRungHorizon S d n j)
          (State.x q.1) :=
    iter_map_of_step_map
      Kstate Kcount' (fun s => State.x s.1)
      hstep (phase2BufferedRungHorizon S d n j) q
  have hc := hcount (State.x q.1) hpre
  change
    terminalFailureMass
        (iter Kstate (phase2BufferedRungHorizon S d n j) q)
        GoodState ≤
      phase2BufferedRungError S d n j
  change
    terminalFailureMass
        (iter Kcount'
          (phase2BufferedRungHorizon S d n j)
          (State.x q.1))
        GoodCount ≤
      phase2BufferedRungError S d n j at hc
  rw [← hmap, terminalFailureMass_map] at hc
  exact
    (terminalFailureMass_congr_predicate
      (iter Kstate (phase2BufferedRungHorizon S d n j) q)
      GoodState
      (fun r => GoodCount (State.x r.1))
      hgood).le.trans hc

/-- Exact total raw horizon of the buffered Phase-II ladder. -/
def phase2BufferedLadderHorizon
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d n J : ℕ) : ℕ :=
  ∑ j ∈ Finset.range J, phase2BufferedRungHorizon S d n j

/-- Exact finite error sum of the buffered Phase-II ladder. -/
noncomputable def phase2BufferedLadderError
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d n J : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range J, phase2BufferedRungError S d n j

/-- Common exponential envelope for every buffered Phase-II rung. -/
noncomputable def phase2BufferedRungEnvelope (d : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
      (Real.exp
        (-((d : ℝ) * Real.log ((6 / 5 : NNReal) : ℝ)))) +
    ENNReal.ofReal (Real.exp (-(d : ℝ))) +
    ENNReal.ofReal (Real.exp (-(d : ℝ)))

theorem phase2BufferedRungError_le_envelope
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d n j : ℕ)
    (hd : 1 ≤ d)
    (hKle : phase2DyadicK j ≤ n)
    (hlarge : 68 * d ≤ 3 * n) :
    phase2BufferedRungError S d n j ≤
      phase2BufferedRungEnvelope d := by
  let K := phase2DyadicK j
  let P := phase2DyadicMinorityScale n j
  have hK4 : 4 ≤ K := phase2DyadicK_ge_four j
  have hP : 1 ≤ P :=
    phase2DyadicMinorityScale_pos j hKle
  have hshare : K * P ≤ n := by
    simpa [K, P, phase2DyadicMinorityScale] using
      (Nat.mul_div_le n (phase2DyadicK j))
  have hroom : 2 * (P + d) ≤ n :=
    phase2Buffered_room K n P d hK4 hshare hlarge
  have hcorner :
      (6 / 5 : NNReal) *
          (relaxedDyadicBHi P d + 1 : NNReal) ≤
        phase2HalfRate.fire *
          (relaxedDyadicLower n P d + 1 : NNReal) :=
    phase2HalfRate_corner K n P d hP hd hK4 hshare hlarge
  have hbeta : (1 : NNReal) < 6 / 5 := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    norm_num
  let E :=
    relaxedDyadicAdaptiveErrorDataOfScalars
      phase2HalfRate n P d (6 / 5 : NNReal)
      S hP hd hroom hbeta hcorner
  have herr :=
    relaxedDyadicAdaptiveRungError_le
      phase2HalfRate n P 0 E
  simpa [phase2BufferedRungError,
    phase2BufferedRungEnvelope,
    phase2BufferedRungMultiplier,
    relaxedDyadicLadderError,
    relaxedDyadicAdaptiveRungEnvelope,
    relaxedDyadicAdaptiveRungData,
    relaxedDyadicAdaptiveErrorDataOfScalars,
    relaxedDyadicActiveScale, relaxedDyadicScale,
    Nat.max_eq_right hP, P, E] using herr

theorem phase2BufferedLadderError_le
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d n J : ℕ)
    (hd : 1 ≤ d)
    (hlarge : 68 * d ≤ 3 * n)
    (hKle : ∀ j < J, phase2DyadicK j ≤ n) :
    phase2BufferedLadderError S d n J ≤
      (J : ℝ≥0∞) * phase2BufferedRungEnvelope d := by
  unfold phase2BufferedLadderError
  calc
    (∑ j ∈ Finset.range J,
        phase2BufferedRungError S d n j) ≤
      ∑ _ ∈ Finset.range J,
        phase2BufferedRungEnvelope d := by
      gcongr with j hj
      exact phase2BufferedRungError_le_envelope
        S d n j hd (hKle j (Finset.mem_range.mp hj)) hlarge
    _ = (J : ℝ≥0∞) * phase2BufferedRungEnvelope d := by
      simp [nsmul_eq_mul]

/-- Unconditional finite buffered Phase-II ladder on the paper-worst
fixed-Byzantine fibre. -/
theorem phase2_reference_buffered_ladder_to_entry_or_endpoint
    (h3 : 3 ≤ n)
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d J : ℕ)
    (hd : 1 ≤ d)
    (hlarge : 68 * d ≤ 3 * n)
    (hKle : ∀ j < J, phase2DyadicK j ≤ n) :
    Reaches
      (freeze
        (Phase2LadderTarget
          (n := n) (B := B) (z := z) J)
        (phase2ReferenceStep
          (n := n) (B := B) (z := z) h3))
      (phase2BufferedLadderHorizon S d n J)
      (Phase2DyadicCheckpoint
        (n := n) (B := B) (z := z) 0)
      (Phase2LadderTarget
        (n := n) (B := B) (z := z) J)
      (phase2BufferedLadderError S d n J) := by
  let P : ℕ → Phase2Level n B z → Prop :=
    fun j =>
      Phase2LadderTarget (n := n) (B := B) (z := z) j
  let T : ℕ → ℕ :=
    fun j => phase2BufferedRungHorizon S d n j
  let Stop :
      ℕ → Phase2Level n B z → Phase2Level n B z → Prop :=
    fun j _ q => P (j + 1) q
  letI : ∀ j, DecidablePred (P j) := by
    intro j q
    dsimp only [P]
    infer_instance
  letI : ∀ j a, DecidablePred (Stop j a) := by
    intro j a q
    exact inferInstanceAs (Decidable (P (j + 1) q))
  have hT : ∀ j < J, 0 < T j := by
    intro j hj
    have hCpos : 0 < S.C :=
      lt_of_lt_of_le Nat.zero_lt_one S.hC
    have hnpos : 0 < n := by omega
    have hRpos :
        0 < phase2BufferedRungMultiplier S d n j := by
      unfold phase2BufferedRungMultiplier
        relaxedDyadicAdaptiveMultiplier
      exact Nat.mul_pos
        (lt_of_lt_of_le Nat.zero_lt_one S.hR₀)
        (by
          rw [Nat.add_comm]
          exact Nat.succ_pos _)
    dsimp only [T, phase2BufferedRungHorizon,
      relaxedDyadicHorizon]
    exact Nat.mul_pos
      (Nat.mul_pos (by norm_num) (Nat.mul_pos hCpos hRpos))
      hnpos
  have hstage :
      ∀ j < J, ∀ q, P j q →
        terminalFailureMass
          (StagedFreezeControl.block
            (phase2ReferenceStep
              (n := n) (B := B) (z := z) h3)
            Stop T j q)
          (P (j + 1)) ≤
        phase2BufferedRungError S d n j := by
    intro j hj q hq
    change
      terminalFailureMass
        (iter
          (freeze
            (P (j + 1))
            (phase2ReferenceStep
              (n := n) (B := B) (z := z) h3))
          (phase2BufferedRungHorizon S d n j) q)
        (P (j + 1)) ≤
      phase2BufferedRungError S d n j
    exact
      phase2_reference_buffered_dyadic_rung
        (n := n) (B := B) (z := z)
        h3 S d j hd (hKle j hj) hlarge q hq
  intro q₀ hq₀
  have hP₀ : P 0 q₀ := Or.inr hq₀
  have hstaged :=
    terminalFailureMass_stagedIter
      (K := StagedFreezeControl.block
        (phase2ReferenceStep
          (n := n) (B := B) (z := z) h3)
        Stop T)
      (P := P)
      (ε := fun j => phase2BufferedRungError S d n j)
      (m := J) hstage q₀ hP₀
  have hcompare :=
    StagedFreezeControl.targetFreeze_failure_le_stagedFreeze
      (Phase2LadderTarget
        (n := n) (B := B) (z := z) J)
      (phase2ReferenceStep
        (n := n) (B := B) (z := z) h3)
      Stop T J hT q₀
  have hsumT :
      (∑ j ∈ Finset.range J, T j) =
        phase2BufferedLadderHorizon S d n J := by
    simp [T, phase2BufferedLadderHorizon]
  rw [hsumT] at hcompare
  exact hcompare.trans (by
    simpa [P, phase2BufferedLadderError] using hstaged)

/-- Number of buffered dyadic rungs required to make the terminal aggregate
cap strictly smaller than one molecule. -/
def phase2BufferedStageCount (n : ℕ) : ℕ :=
  Nat.log 2 n - 1

theorem phase2BufferedStageCount_log_lower
    (d n : ℕ) (hd : 1 ≤ d)
    (hlarge : 68 * d ≤ 3 * n) :
    4 ≤ Nat.log 2 n := by
  have hn16 : 2 ^ 4 ≤ n := by
    norm_num
    omega
  exact Nat.le_log_of_pow_le (by norm_num) hn16

theorem phase2BufferedStageCount_rung_le
    (d n j : ℕ) (hd : 1 ≤ d)
    (hlarge : 68 * d ≤ 3 * n)
    (hj : j < phase2BufferedStageCount n) :
    phase2DyadicK j ≤ n := by
  have hlog :=
    phase2BufferedStageCount_log_lower d n hd hlarge
  have hjlog : j + 2 ≤ Nat.log 2 n := by
    unfold phase2BufferedStageCount at hj
    omega
  calc
    phase2DyadicK j = 2 ^ (j + 2) := by
      simp [phase2DyadicK, pow_add]
    _ ≤ 2 ^ Nat.log 2 n :=
      Nat.pow_le_pow_right (by norm_num) hjlog
    _ ≤ n :=
      Nat.pow_log_le_self 2 (by omega)

theorem phase2DyadicK_stageCount_gt
    (d n : ℕ) (hd : 1 ≤ d)
    (hlarge : 68 * d ≤ 3 * n) :
    n < phase2DyadicK (phase2BufferedStageCount n) := by
  have hlog :=
    phase2BufferedStageCount_log_lower d n hd hlarge
  have hlt :
      n < 2 ^ (Nat.log 2 n + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) n
  calc
    n < 2 ^ (Nat.log 2 n + 1) := hlt
    _ = phase2DyadicK (phase2BufferedStageCount n) := by
      unfold phase2BufferedStageCount phase2DyadicK
      have hsub :
          Nat.log 2 n - 1 + 2 = Nat.log 2 n + 1 := by
        omega
      rw [← hsub, pow_add]
      norm_num

theorem phase2LadderTarget_stageCount_iff_strong
    (d n : ℕ) (hd : 1 ≤ d)
    (hlarge : 68 * d ≤ 3 * n)
    (q : Phase2Level n B z) :
    Phase2LadderTarget
        (n := n) (B := B) (z := z)
        (phase2BufferedStageCount n) q ↔
      Phase2StrongTarget q := by
  constructor
  · rintro (hstrong | hcap)
    · exact hstrong
    · have hKgt :=
        phase2DyadicK_stageCount_gt d n hd hlarge
      have hminor :
          State.y q.1 + State.z q.1 = 0 := by
        by_contra hne
        have hmpos :
            0 < State.y q.1 + State.z q.1 :=
          Nat.pos_of_ne_zero hne
        have hKle :
            phase2DyadicK (phase2BufferedStageCount n) ≤
              phase2DyadicK (phase2BufferedStageCount n) *
                (State.y q.1 + State.z q.1) :=
          Nat.le_mul_of_pos_right _ hmpos
        unfold Phase2DyadicCheckpoint
          Phase2AggregateCap at hcap
        omega
      exact (phase2StrongTarget_iff_y_le_z q).2 (by omega)
  · exact fun hstrong => Or.inl hstrong

/-- Complete unconditional buffered Phase-II reference ladder from the
Phase-I handoff checkpoint to the strong entry `y ≤ z`. -/
theorem phase2_reference_buffered_to_strong
    (h3 : 3 ≤ n)
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d : ℕ)
    (hd : 1 ≤ d)
    (hlarge : 68 * d ≤ 3 * n) :
    Reaches
      (freeze
        (Phase2StrongTarget (n := n) (B := B) (z := z))
        (phase2ReferenceStep
          (n := n) (B := B) (z := z) h3))
      (phase2BufferedLadderHorizon S d n
        (phase2BufferedStageCount n))
      (Phase2DyadicCheckpoint
        (n := n) (B := B) (z := z) 0)
      (Phase2StrongTarget (n := n) (B := B) (z := z))
      (phase2BufferedLadderError S d n
        (phase2BufferedStageCount n)) := by
  have hreach :=
    phase2_reference_buffered_ladder_to_entry_or_endpoint
      (n := n) (B := B) (z := z)
      h3 S d (phase2BufferedStageCount n)
      hd hlarge
      (fun j hj =>
        phase2BufferedStageCount_rung_le
          d n j hd hlarge hj)
  have htargetIff :
      ∀ q : Phase2Level n B z,
        Phase2LadderTarget
            (n := n) (B := B) (z := z)
            (phase2BufferedStageCount n) q ↔
          Phase2StrongTarget q :=
    fun q =>
      phase2LadderTarget_stageCount_iff_strong
        d n hd hlarge q
  have hfreeze :
      freeze
          (Phase2LadderTarget
            (n := n) (B := B) (z := z)
            (phase2BufferedStageCount n))
          (phase2ReferenceStep
            (n := n) (B := B) (z := z) h3) =
        freeze
          (Phase2StrongTarget
            (n := n) (B := B) (z := z))
          (phase2ReferenceStep
            (n := n) (B := B) (z := z) h3) := by
    funext q
    unfold freeze
    by_cases hq :
        Phase2LadderTarget
          (n := n) (B := B) (z := z)
          (phase2BufferedStageCount n) q
    · rw [if_pos hq, if_pos ((htargetIff q).1 hq)]
    · rw [if_neg hq,
        if_neg (fun hs => hq ((htargetIff q).2 hs))]
  intro q hq
  have hc := hreach q hq
  rw [hfreeze] at hc
  exact
    (terminalFailureMass_congr_predicate
      (iter
        (freeze
          (Phase2StrongTarget
            (n := n) (B := B) (z := z))
          (phase2ReferenceStep
            (n := n) (B := B) (z := z) h3))
        (phase2BufferedLadderHorizon S d n
          (phase2BufferedStageCount n))
        q)
      (Phase2StrongTarget
        (n := n) (B := B) (z := z))
      (Phase2LadderTarget
        (n := n) (B := B) (z := z)
        (phase2BufferedStageCount n))
      (fun r => (htargetIff r).symm)).le.trans hc

/-- The unconditional buffered Phase-II ladder transfers uniformly to every
history-dependent Byzantine strategy on the fixed `z` fibre. -/
theorem phase2_controlled_buffered_to_strong
    (σ : Strategy n B)
    (h3 : 3 ≤ n)
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d : ℕ)
    (hd : 1 ≤ d)
    (hlarge : 68 * d ≤ 3 * n) :
    Reaches
      (freeze
        (fun r : History n B × Phase2Level n B z =>
          Phase2StrongTarget r.2)
        (fun r =>
          phase2ControlledStep
            (n := n) (B := B) (z := z)
            σ h3 r.1 r.2))
      (phase2BufferedLadderHorizon S d n
        (phase2BufferedStageCount n))
      (fun r =>
        Phase2DyadicCheckpoint
          (n := n) (B := B) (z := z) 0 r.2)
      (fun r => Phase2StrongTarget r.2)
      (phase2BufferedLadderError S d n
        (phase2BufferedStageCount n)) := by
  rintro ⟨hist, q⟩ hq
  have hcompare :=
    stoppedControlledBand_failure_le_reference
      (fun _ : Phase2Level n B z => False)
      (Phase2StrongTarget
        (n := n) (B := B) (z := z))
      (phase2ReferenceStep
        (n := n) (B := B) (z := z) h3)
      (phase2ControlledStep
        (n := n) (B := B) (z := z) σ h3)
      (by
        intro i j hij hj
        exact False.elim hj)
      (@phase2StrongTarget_upper
        (n := n) (B := B) (z := z))
      (phase2ReferenceStep_mono
        (n := n) (B := B) (z := z) h3)
      (phase2_reference_le_controlled
        (n := n) (B := B) (z := z) σ h3)
      (phase2BufferedLadderHorizon S d n
        (phase2BufferedStageCount n))
      hist q
  have href :=
    phase2_reference_buffered_to_strong
      (n := n) (B := B) (z := z)
      h3 S d hd hlarge q hq
  have hfreezeControlled :
      freeze
          (fun r : History n B × Phase2Level n B z =>
            False ∨ Phase2StrongTarget r.2)
          (fun r =>
            phase2ControlledStep
              (n := n) (B := B) (z := z)
              σ h3 r.1 r.2) =
        freeze
          (fun r : History n B × Phase2Level n B z =>
            Phase2StrongTarget r.2)
          (fun r =>
            phase2ControlledStep
              (n := n) (B := B) (z := z)
              σ h3 r.1 r.2) := by
    funext r
    unfold freeze
    by_cases hr : Phase2StrongTarget r.2
    · rw [if_pos (Or.inr hr), if_pos hr]
    · rw [if_neg (by simpa using hr), if_neg hr]
  have hfreezeReference :
      freeze
          (fun r : Phase2Level n B z =>
            False ∨ Phase2StrongTarget r)
          (phase2ReferenceStep
            (n := n) (B := B) (z := z) h3) =
        freeze
          (Phase2StrongTarget
            (n := n) (B := B) (z := z))
          (phase2ReferenceStep
            (n := n) (B := B) (z := z) h3) := by
    funext r
    unfold freeze
    by_cases hr : Phase2StrongTarget r
    · rw [if_pos (Or.inr hr), if_pos hr]
    · rw [if_neg (by simpa using hr), if_neg hr]
  rw [hfreezeControlled, hfreezeReference] at hcompare
  have hcompare' :
      terminalFailureMass
          (iter
            (freeze
              (fun r : History n B × Phase2Level n B z =>
                Phase2StrongTarget r.2)
              (fun r =>
                phase2ControlledStep
                  (n := n) (B := B) (z := z)
                  σ h3 r.1 r.2))
            (phase2BufferedLadderHorizon S d n
              (phase2BufferedStageCount n))
            (hist, q))
          (fun r => Phase2StrongTarget r.2) ≤
        terminalFailureMass
          (iter
            (freeze
              (Phase2StrongTarget
                (n := n) (B := B) (z := z))
              (phase2ReferenceStep
                (n := n) (B := B) (z := z) h3))
            (phase2BufferedLadderHorizon S d n
              (phase2BufferedStageCount n))
            q)
          (Phase2StrongTarget
            (n := n) (B := B) (z := z)) := by
    exact hcompare
  exact hcompare'.trans href

/-- Forget the fixed-fibre proof while retaining the adaptive transcript. -/
def phase2JointForget
    (q : History n B × Phase2Level n B z) :
    ControlledJointState n B :=
  (q.1, q.2.1)

/-- The fibre-level controlled step projects exactly to the physical joint
history/state step. -/
theorem phase2ControlledStep_map_jointForget
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (hist : History n B) (q : Phase2Level n B z) :
    (phase2ControlledStep
        (n := n) (B := B) (z := z)
        σ h3 hist q).map phase2JointForget =
      controlledJointStep σ h3 (hist, q.1) := by
  unfold phase2JointForget controlledJointStep
    phase2ControlledStep phase1ControlledStep
    adaptiveEventStep fixedEventStep
  rw [PMF.map_comp, PMF.map_comp]
  rfl

/-- Physical joint-law form of the complete Phase-II ladder.  The initial
Byzantine count chooses the fixed fibre internally. -/
theorem phase2_controlledJoint_buffered_to_strong
    (σ : Strategy n B)
    (h3 : 3 ≤ n)
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d : ℕ)
    (hd : 1 ≤ d)
    (hlarge : 68 * d ≤ 3 * n) :
    Reaches
      (freeze
        (fun r : ControlledJointState n B =>
          StrongXEntry r.2)
        (controlledJointStep σ h3))
      (phase2BufferedLadderHorizon S d n
        (phase2BufferedStageCount n))
      (fun r =>
        4 * (State.y r.2 + State.z r.2) ≤ n)
      (fun r => StrongXEntry r.2)
      (phase2BufferedLadderError S d n
        (phase2BufferedStageCount n)) := by
  rintro ⟨hist, s⟩ hs
  let q : Phase2Level n B (State.z s) := ⟨s, rfl⟩
  let GoodFibre :=
    fun r : History n B × Phase2Level n B (State.z s) =>
      Phase2StrongTarget r.2
  let GoodPhysical :=
    fun r : ControlledJointState n B =>
      StrongXEntry r.2
  let Kfibre :=
    freeze GoodFibre
      (fun r =>
        phase2ControlledStep
          (n := n) (B := B) (z := State.z s)
          σ h3 r.1 r.2)
  let Kphysical :=
    freeze GoodPhysical (controlledJointStep σ h3)
  have hq :
      Phase2DyadicCheckpoint
        (n := n) (B := B) (z := State.z s) 0 q := by
    unfold Phase2DyadicCheckpoint phase2DyadicK
      Phase2AggregateCap
    simpa [q] using hs
  have hfibre :=
    phase2_controlled_buffered_to_strong
      (n := n) (B := B) (z := State.z s)
      σ h3 S d hd hlarge (hist, q) hq
  have hstep :
      ∀ r : History n B × Phase2Level n B (State.z s),
        (Kfibre r).map phase2JointForget =
          Kphysical (phase2JointForget r) := by
    intro r
    dsimp only [Kfibre, Kphysical]
    by_cases hr : GoodFibre r
    · have hr' : GoodPhysical (phase2JointForget r) := by
        exact hr
      rw [freeze_of_mem r hr,
        freeze_of_mem (phase2JointForget r) hr',
        PMF.pure_map]
    · have hr' : ¬ GoodPhysical (phase2JointForget r) := by
        exact hr
      rw [freeze_of_not_mem r hr,
        freeze_of_not_mem (phase2JointForget r) hr']
      exact phase2ControlledStep_map_jointForget
        σ h3 r.1 r.2
  have hmap :
      (iter Kfibre
          (phase2BufferedLadderHorizon S d n
            (phase2BufferedStageCount n))
          (hist, q)).map phase2JointForget =
        iter Kphysical
          (phase2BufferedLadderHorizon S d n
            (phase2BufferedStageCount n))
          (hist, s) := by
    exact iter_map_of_step_map
      Kfibre Kphysical phase2JointForget hstep
      (phase2BufferedLadderHorizon S d n
        (phase2BufferedStageCount n))
      (hist, q)
  change
    terminalFailureMass
        (iter Kphysical
          (phase2BufferedLadderHorizon S d n
            (phase2BufferedStageCount n))
          (hist, s))
        GoodPhysical ≤
      phase2BufferedLadderError S d n
        (phase2BufferedStageCount n)
  rw [← hmap, terminalFailureMass_map]
  simpa [GoodFibre, GoodPhysical, Phase2StrongTarget,
    StrongXEntry, q] using hfibre

/-- The physical adaptive process reaches the paper's relaxed entry target no
later than it reaches the stronger `y ≤ z` target. -/
theorem phase2_controlledJoint_buffered_to_relaxed
    (σ : Strategy n B)
    (h3 : 3 ≤ n)
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d : ℕ)
    (hd : 1 ≤ d)
    (hlarge : 68 * d ≤ 3 * n) :
    Reaches
      (freeze
        (fun r : ControlledJointState n B =>
          RelaxedXConsensus r.2)
        (controlledJointStep σ h3))
      (phase2BufferedLadderHorizon S d n
        (phase2BufferedStageCount n))
      (fun r =>
        4 * (State.y r.2 + State.z r.2) ≤ n)
      (fun r => RelaxedXConsensus r.2)
      (phase2BufferedLadderError S d n
        (phase2BufferedStageCount n)) := by
  intro q hq
  have hstrong :=
    phase2_controlledJoint_buffered_to_strong
      (n := n) (B := B)
      σ h3 S d hd hlarge q hq
  exact
    (targetFreeze_failure_mono_good
      (fun r : ControlledJointState n B =>
        StrongXEntry r.2)
      (fun r : ControlledJointState n B =>
        RelaxedXConsensus r.2)
      (controlledJointStep σ h3)
      (fun r hr => strongXEntry_relaxed r.2 hr)
      (phase2BufferedLadderHorizon S d n
        (phase2BufferedStageCount n))
      q).trans hstrong

end

end Tri.Byzantine

#print axioms Tri.Byzantine.phase2HalfRate_fire_le_effective
#print axioms Tri.Byzantine.phase1XStep_eq_relaxed_effective
#print axioms Tri.Byzantine.phase2HalfRate_expect_le_phase1XStep
#print axioms Tri.Byzantine.phase2_count_buffered_dyadic_rung
#print axioms Tri.Byzantine.phase2_reference_buffered_dyadic_rung
#print axioms Tri.Byzantine.phase2BufferedRungError_le_envelope
#print axioms Tri.Byzantine.phase2BufferedLadderError_le
#print axioms Tri.Byzantine.phase2_reference_buffered_ladder_to_entry_or_endpoint
#print axioms Tri.Byzantine.phase2BufferedStageCount_rung_le
#print axioms Tri.Byzantine.phase2DyadicK_stageCount_gt
#print axioms Tri.Byzantine.phase2_reference_buffered_to_strong
#print axioms Tri.Byzantine.phase2_controlled_buffered_to_strong
#print axioms Tri.Byzantine.phase2ControlledStep_map_jointForget
#print axioms Tri.Byzantine.phase2_controlledJoint_buffered_to_strong
#print axioms Tri.Byzantine.phase2_controlledJoint_buffered_to_relaxed
