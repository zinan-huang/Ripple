# Time bound of P_EM (Kanaya et al. Theorem 4) and its inputs from Burman et al.

Paper notes for the Lean development under `Ripple/PopulationProtocol/SSEM/UpperBound/`.
Section A is the diagnosis (target statements, premise graph, the instance with the papers'
parameters, model differences); section B.1 is the proof of node B32 (Burman et al. Lemma 3.2,
potential form) in the form formalized as `P_EM_paper_propagation`. Node labels: N (not yet
proved on paper), R(k) (checked by k readers); verdicts HOLDS / GAP / REPAIR / INSTANCE.

Sources:
- [K] Kanaya, Eguchi, Sasada, Ooshita, Inoue, arXiv:2503.17652v1, §5.2.1, Lemmas 6–14
- [B] Burman, Chen, Chen, Doty, Nowak, Severson, Xu, *Time-optimal self-stabilizing leader
  election in population protocols*, PODC 2021, arXiv:1907.06068v5: §2.1 Lemma 2.7 / Cor. 2.8 (epidemic, from
  Mocquard et al. [50]), §3 Propagate-Reset (Obs. 3.1, Lemma 3.2 citing Sudo et al. [59]
  Cor. 8, Lemma 3.3, Thm 3.4, Cor. 3.5), §4 Optimal-Silent-SSR (Lemma 4.1, Lemma 4.2,
  Thm 4.3, Cor. 4.4).

## A. Diagnosis

### A.1 Target statements (Kanaya Thm 4, time part)

For the P_EM instance with the paper's parameters (A.3), run on its finite role-indexed state
set (`protocolPEMPaperFin`), for all `n ≥ N₀` and every initial configuration `C₀` of that
finite protocol, with `T` the first time a silent
configuration is reached under the uniform scheduler on ordered pairs of distinct agents:

- (T-exp) `expectedParallelTimeToSilent P hn C₀ ≤ c₁ · n`;
- (T-whp) `probNotHitBy P hn C₀ isSilent (c₂ · n² · ⌈log n⌉) ≤ 1/n`
  (i.e. silence within `c₂ n log n` parallel time with probability ≥ 1 − 1/n).

Lean API already present (`SSEM/Probability/ExpectedTime.lean`): `expectedParallelTimeToSilent`
(:4530), `probNotHitBy` (:853), `ProbHitWithin`, restart lemmas
`expectedHittingTime_le_window_mul_inv` (:3276: a uniform window bound `p ≤ P[hit within K]`
from every non-goal configuration gives `E[T] ≤ K/p`) and
`probNotHitBy_mul_window_le_initial_mul_pow` (:2242: `P[T > rK] ≤ (1-p)^r`). So [K] Lemma 14
(restart) is **(c) packaging**: both (T-exp) and (T-whp) follow from

- (W) **uniform window**: there are constants `c, p > 0` with
  `p ≤ ProbHitWithin P hn C S_em (c · n²)` for every configuration `C` of the finite protocol
  (equivalently: every flat configuration with counters in range, `GoodPEM`, using
  `expectedHittingTime_le_window_mul_inv_of_invariant` :3952; its w.h.p. counterpart
  `probNotHitBy_mul_window_le_initial_mul_pow_of_invariant` :3885 is `private` now),

with (T-whp) by `r = ⌈log n / log(1/(1-p))⌉` windows; the change of goal from `S_em` to
"silent" uses `expectedHittingTime_mono_goal` (:2845) and `probNotHitBy_mono_goal` (:1217).
Over the flat `AgentState n` (unbounded counters) the targets are false: all agents Settled
and sorted with correct answers and median timer `M` needs `M(n−1)/2` expected parallel time
(review R1) — hence the finite protocol. `S_em ⊆ silent` is Lemma 6 (proved in
FIX1, `SilentPEM.lean`, for any `trank`; it uses only the transition). Everything below is the
proof of (W).

### A.2 Premise DAG of (W)

```
W ── K7 ── B43*  ── B35 ── B34 ── B32 ── E (epidemic / propagating variable)
 │    │              │      └──── B33 ── Chernoff (agent interaction counts)
 │    │              └──── (dormant ⇒ wake) pigeonhole
 │    ├── K-timer (timer survives the ranking: binomial tail)       [K L7, L9 second half]
 ├── K9 ── K8 (swap, coupon sum)  ── K-timer
 ├── K10 ── K8, decision wait, K-timer
 ├── K12 ── K11 (countdown), B34/B35 (reset completes), answer epidemic (B32-type), K10
 └── K13 ── K11
B43* = B43 run inside P_EM (see A.4): B41 (tree ranking), B42 (unique leader w.c.p.),
       Emax-countdown (Chernoff), collision detection (geometric).
```

Status of every node (no node has an accepted paper proof inside Ripple yet):

| id | statement (locator) | class | Ripple pieces | status |
|---|---|---|---|---|
| E | two-way epidemic: E[T_n] = (n−1)H_{n−1}; constant-probability O(n log n) interactions ([B] L2.7, C2.8) | (b) in SSEM model | SSEM `EpidemicBound.epidemic_phiCount_to_zero_expected_le` (expected coupon form), `OptimalWindows` :159/:224 (Σ ≤ n²); ExactMajority `TightEpidemicWork.epidemic_janson_exp_le_half_inv_sq` (multiset model, w.h.p.) | N |
| B32 | Rmax = 60 ln n: partially triggered ⇒ fully propagating within 4 ln n time, prob ≥ 1 − O(1/n) ([B] L3.2 via [59] Cor. 8) | (b): proof is by citation only | none | N |
| B33 | fully propagating ⇒ fully dormant within O(log n + Rmax) time w.h.p. (potential Φ = Σ 3^{rc}) ([B] L3.3) | (b) | `RecoveryBound.lean:843` (all-Resetting to Phase1Goal ≤ Rmax·n², expected), `DrainNoWake*` (no wake-up tail) | N |
| B34 | partially triggered ⇒ awakening config within O(Dmax) time, prob ≥ 1 − O(1/n) ([B] T3.4) | (b) | — | N |
| B35 | any config ⇒ awakening or fully computing within O(log n + Dmax) time ([B] C3.5) | (b) | `PolynomialBound.lean:573` (seed to all-Resetting ≤ n²(n−1)) | N |
| B41 | single leader + n−1 Unsettled ⇒ tree ranking done in expected O(n) time ([B] L4.1) | (b) | `UpperBound.lean:6128` (FreshRankingStart ⇒ InSrank ≤ Rmax·n², weaker) | N |
| B42 | awakening configuration has a unique leader with constant probability ([B] L4.2) | (b), see A.4 (ii) | — | N |
| B43 | Optimal-Silent-SSR silent in expected O(n) time from any config ([B] T4.3) | (b) | conditional only (`h12ranking` in `GenericKeystone`) | N |
| K-timer | median timer ≥ 28 when ranking completes, prob ≥ 1/5 (binomial, [K] L7, L9) | (b), elementary | — | N |
| K8 | from Srank without reset, E[time to Sswap] ≤ n ([K] L8) | (b), elementary | `UpperBound.lean:5422` (swap ≤ Σ n(n−1)/(k+1)²) | N, close to R |
| K11 | from Srank, median timer reaches 0 within 7(trank+4)(n−1) time, prob ≥ 1/2 ([K] L11) | (b), elementary | `PolynomialBound.lean:143` (drain ≤ T·n(n−1)) | N, close to R |
| K7, K9, K10, K12, K13 | [K] Table 2 window lemmas | (b) | four of them are the carried hypotheses of `PEM_expected_parallel_time_from_phase_bounds` (UpperBound.lean:6328) | N |
| K14 | restart ([K] L14) | (c) | restart lemmas above | packaging |

Minimal roots: E, B32, B33, B41, B42 (probabilistic content), K-timer (binomial), and the
coupling A.4 (i). Everything else composes them.

Edges added after review R1 (2026-11-08): K9 → B43* (its second half re-ranks after a
reset), decision wait, mismatch-detection wait; K12 → K-timer, B43*, B32 (every agent must be
recruited so its answer is cleared; the answer epidemic then races the first wake-up,
Θ(Dmax) = Θ(n), not the decay of `resetcount`); B34 → pigeonhole (some agent makes Dmax
interactions); B35 → B33, E (superepidemic of computing agents); B43 → epoch restart.

Errata ledger (source steps that do not hold as printed; labels per the paper-phase rules):
- [K] L7 assumes `C₀ ∈ Srank`; the use in L14 needs every configuration.
  REPRODUCED-BY-2 (two readers, including reviewer R1).
- [K] L9 assumes `C₀ ∈ Srank ∩ Tswap`; Table 2 reads `Srank → Tswap ∪ Stim`. CLAIMED (R1).
- [K] L7/L9 Chernoff step counts `n² trank` interactions while the Markov window is
  `2 s_rank ≤ 2 trank n` parallel time `= 2 trank n²` interactions; the constant `20/3`
  matches `2n²`. CLAIMED (R1); constants to be redone in B.
- [K] L11 prints `2/(n(n−2))`; the pair probability is `2/(n(n−1))`. REPRODUCED-BY-2.
- [B] Protocol 3 line 9 guard `2·rank + children < n` never assigns rank n (with 1-indexed
  ranks, child `2i` needs `2i ≤ n`); the Lean guard `2r + c + 1 < n` (0-indexed) is the
  corrected `≤ n`. REPRODUCED-BY-2.
- [B] Thm 4.3 / L4.2: an adversarial configuration with all agents Resetting with leader F and
  no trigger reaches an awakening configuration with no leader; this is a failed epoch costing
  O(Emax) (all wake Unsettled, errorcount expires, trigger). B42/B43 must account for it.
  CLAIMED (R1), consistent with the Lean code.

### A.3 The second P_EM instance (paper parameters)

`protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)` with
- `Rmax = ⌈60 ln n⌉` ([B] §3: "we choose the concrete value Rmax = 60 ln n");
- `Emax = e·n`, `Dmax = d·n` with constants `e, d` fixed in B42/B43 ([B] §4: Θ(n));
- `trank` a constant with `s_rank ≤ trank · n`, where `s_rank` is the expected silence time of
  Optimal-Silent-SSR from B43 ([K] §5.2); the timer starts at `7(trank + 4)`.

The current Lean instance `protocolPEM n n n` (trank = Rmax = n) cannot carry the time bound:
the countdown alone takes `7(n+4)(n−1)/2` expected parallel time ([K] L11). The state count of
the new instance follows from `pemSimulation` (FiniteStatePEM.lean) with `T = 7(trank+4)`,
`R = ⌈60 ln n⌉`, `E = e n`, `D = d n`: `≤ 24n + 24(T+1) + 8(en+1) + 8R + 8(dn+1) = O(n)`.
Correctness for this instance is proved (FIX2, `UpperBound/PaperInstance.lean`):
`P_EM_paper_solves_silent_SSEM` and `P_EM_paper_fin_solves_silent_SSEM` compose the existing
log-`Rmax` convergence proof `burmanConvergence_concrete_log` /
`P_EM_solves_SSEM_log` (`Convergence/BurmanConvergenceLog.lean`, any `trank`,
`Rmax ≥ 2⌈log₂ n⌉ + 2`, `1 < Dmax`) with `two_clog_add_two_le_rmaxPaper`
(`2⌈log₂ n⌉ + 2 ≤ ⌈60 ln n⌉`). Pointed out by review R1.

Option recorded by R1 (A.5): Theorem 4 does not fix `Rmax`; `Rmax = Θ(n)` keeps O(n) states
and O(n)-time windows (B33 is O(log n + Rmax) with Dmax = Ω(Rmax)) and gives B32 slack. If
B32 at `Rmax = Θ(log n)` stalls, a third instance with `Rmax = n` is the fallback; it would
still be the paper's protocol, with Burman's specific constant replaced.

### A.4 Model differences between [B]/[K] pseudocode and the Lean protocol

(i) **Ranking inside P_EM.** [K] Lemmas 7, 9, 12 apply [B] Thm 4.3 to the ranking subprotocol
as it runs inside P_EM. Two interferences: (a) `phase4_swap` exchanges whole states of two
Settled agents of distinct ranks; the ranking data move with the state, so the ranking process
seen as a configuration modulo agent names is unchanged in law (the uniform scheduler is
invariant under agent permutation) — to be written as a lemma; (b) the median agent triggers
Propagate-Reset on an answer mismatch after its timer hits 0 ([K] handles this by the K-timer
event: with probability ≥ 1/5 the timer outlives the ranking).

(ii) **Leader bit on recruitment.** [B] §4 text: "all agents set themselves to L upon entering
the Resetting role"; Protocol 2 line 2 recruits without writing `leader`. The Lean
`propagateReset` keeps the stale leader bit of a recruited agent. Effect on B42: the number of
leaders at the start of the dormant phase is at most n and at least 1 (every trigger writes
L); the L,L → L,F election only gets shorter. Effect on the "awakening" analysis: an L agent
whose stale bit was F … none (F agents wake Unsettled). To check in B42: the bound must hold for
every initial leader count in [1, n], not only for n.

(iii) **Deduplication guard.** Lean deduplicates only when both agents are still Resetting after
Propagate-Reset ([B] Protocol 3 line 3 has no guard; in [B]'s encoding `leader` exists only in
role Resetting, so the guard is the faithful reading).

(iv) **0-indexed ranks.** Lean: leader rank 0, children `2r + c + 1`; [B]: rank 1, children
`2r + c`. Same heap.

### A.5 Simplification for an O(n) target (not checked)

[K] needs only constant-probability events inside O(n)-time windows. So the w.h.p. O(log n)
statements of [B] (Cor. 2.8, L3.2, L3.3) may be replaced by constant-probability versions
with O(n log n) or O(n²) interaction bounds, provided each window stays O(n²) interactions.
Exception: B32 (propagation must outrun the decay of `resetcount` with `Rmax = Θ(log n)`) has no
slack: it needs the epidemic-tree depth argument of [59] (depth O(log n) w.h.p.) or an
equivalent. This is the single hardest node.

## B. Paper proofs

### B.1 B32 in the form used for Lean

"P1", "P2" and "P3" below name working proofs that are not part of this repository (P1: the
walk-enumeration proof of B32, Theorem A, with Lemmas 1–11; P2, P3: the later Burman nodes). The
argument of this section does not depend on them except through P1 Lemma 1, the one-interaction
fact proved in Lean as the effective-resetcount lemma of `UpperBound/Propagation.lean`.

Same statement as P1 Theorem A with different constants; the proof replaces the walk enumeration
(P1 Lemmas 3–7) and the geometric-sum tail (P1 Lemma 10) by two potentials, each with a one-step
conditional bound, so that Lean needs one generic lemma (expectation over the scheduler prefix of a
function with a one-step bound `E[F(σp) | σ] ≤ ρ F(σ)` is at most `ρ^K F(∅)`) plus Markov.

Setting: prefix `σ = (p_1, …, p_K)` of pairs; at step `t` with `p_t = (a, b)`, `a ≠ b` (diagonal pairs
have probability 0 and change nothing in the protocol; all recursions below leave them unchanged).
Fix the source `s` (Resetting, `rc ≥ R`) and `L ≥ 1`.
- reach: `reach_0 = {s}`; `reach_t = reach_{t−1} ∪ {a, b}` if `{a, b}` meets `reach_{t−1}`.
- max-process: `x_0 = R·1[w = s]`; `x_t(a) = x_t(b) = max(x(a) ∸ 1, x(b) ∸ 1)`; others unchanged.
- walk weight: `N_0 = 1[w = s]`; `N_t(a) = N_t(b) = L (N(a) + N(b))`; others unchanged. (`N_t(w)` is
  the sum over time-respecting walks from `s` held by `w` at time `t` of `L^{cost}`; not needed.)
- `S_t = Σ_w N_t(w)`.

(D1) `effRc(C_t(w)) ≥ x_t(w)` (P1 Lemma 2, from Lemma 1 and `x ≤ R`).
(D2) Invariant: `x_t ≤ R`; `x_t(w) ≥ 1 ⇒ w ∈ reach_t`; `w ∈ reach_t ⇒ L^{R − x_t(w)} ≤ N_t(w)`.
  Step: for `w ∈ {a, b}` with some reached endpoint, let `r` be an endpoint with
  `x(r) = max(x(a), x(b))`. If `x(r) ≥ 1`, `r` is reached and `L^{R − (x(r) − 1)} = L·L^{R − x(r)} ≤
  L N(r) ≤ N_t(w)`. If `x(r) = 0`, pick a reached endpoint `r'`: `L^R ≤ L N(r') ≤ N_t(w)`.
  New `x ≥ 1` forces `x(r) ≥ 2`, so `r` and hence both endpoints are reached.
(D3) `S_t` is nondecreasing in `t` (`L(N(a) + N(b)) ≥ N(a), N(b)`).
(P1') One step: `S_t ≤ S_{t−1} + 2L(N(a) + N(b))`; averaging over the `n(n−1)` ordered distinct pairs,
  `Σ_{a≠b}(N(a) + N(b)) = 2(n−1) S`, so `E[S_t | σ_{<t}] ≤ (1 + 4L/n) S_{t−1}` and
  `E[S_K] ≤ (1 + 4L/n)^K ≤ exp(4LK/n)`.
(P2') Epidemic: with `k = |reach|`, `Ψ = (n − k)/k`. A step leaves `k` or (with probability
  `p_k = 2k(n−k)/(n(n−1))`) raises it by one, and `Ψ − Ψ' = n/(k(k+1))`, so
  `E[Ψ_t | σ_{<t}] = Ψ − p_k n/(k(k+1)) = Ψ (1 − 2k/((n−1)(k+1))) ≤ Ψ (1 − 1/(n−1))` (`k ≥ 1`).
  `Ψ_0 = n − 1` and `Ψ ≥ 1/(n−1)` while `k < n`, so
  `P[reach_K ≠ V] ≤ (n−1)² (1 − 1/(n−1))^K ≤ (n−1)² e^{−K/(n−1)}`.
(A') If `reach_K = V` and `S_K < L^R`, then for every `t ≤ K` and every `w ∈ reach_t`: `x_t(w) ≥ 1`
  (else `L^R ≤ N_t(w) ≤ S_t ≤ S_K` by D2, D3), so by D1 every agent is Resetting with `rc ≥ 1` at
  every `t ∈ [T_n, K]`. Hence
  `P[not fully propagating at some t ∈ [T_n, K], or T_n > K] ≤ (n−1)² e^{−K/(n−1)} + L^{−R} e^{4LK/n}`.
  With `K = ⌈4 n ln n⌉`, `L = 3`, `R ≥ 60 ln n`: the first term is `≤ n^{−2}`, the second
  `≤ e^{12/n} n^{48 − 60 ln 3} ≤ e^{12/n} n^{−17.9}`; total `≤ 1/n` for `n ≥ 3`.

## C. Status

Formalized: B32 as `P_EM_paper_propagation` (`UpperBound/PropagationPaper.lean`), with the generic
prefix lemma in `Probability/PrefixRun.lean`. The other nodes of the time bound (the Burman reset
and ranking stages and the Kanaya phase lemmas) are not formalized; the time part of Kanaya
Theorem 4 is stated as `KanayaThm4Time` and is open (`OPEN_PROBLEMS.md` §6.1).
