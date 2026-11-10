# P3: uniform window bound for P_EM (Kanaya Thm 4, time part; [K] Lemmas 7–14)

Paper proofs only (2026-11-09). Status at writing: CLAIMED; later reviewed (R3) and reproduced by a
second reader after the fix F1 (see `FIX2-BURMAN.md`).

Labels used below: P1, P2 and P3 are three working proofs written for the time bound of P_EM
(P1: Burman et al. Lemma 3.2 by walk enumeration, superseded by `FIX2-BURMAN.md` §B.1 and not
published; P2: this repository's `FIX2-P2.md`; P3: `FIX2-P3.md`). R1–R3 are independent reviews
of them (not published); their findings are cited by item (for example "R2 I5"). "The packet"
is the question a working proof answers. The status of each node is in `FIX2-BURMAN.md`, and
the formalized statements are in `Ripple/PopulationProtocol/SSEM/UpperBound/`.


Sources read: packet P3 (question); P1, P2, R2 (independent review of P1/P2,
found while working; its verdicts are used only to fix N₀ = 1608); Lean
`Protocol/Transition.lean` (`transitionPEM_prePhase4`, `phase4_swap`, `phase4_decide`,
`phase4_propagate`, `transitionPEM_phase4`, `transitionPEM`, `protocolPEM`),
`Protocol/RankDelta.lean`, `Protocol/State.lean`, `Defs/Config.lean` (`step`, `isSilent`),
`Convergence/Silent.lean` (`majorityAnswer`, `IsConsensusConfig`), `Convergence/SilentPEM.lean`
(`IsSilentConsensus`, `consensus_step_apply`, `IsSilentConsensus.isSilent`),
`Convergence/FiniteStatePEM.lean` (`PEMFinState`, `encPEM`, `embPEM`, `GoodPEM`, `pemSimulation`),
`UpperBound/PaperInstance.lean`; [K] = arXiv:2503.17652v1 §5.2 (Algorithm 1, Table 2, Lemmas 6–14).

## 0. Result

**Theorem W (uniform window; §7).** Let `trank ≥ 40` (default `trank = 40`), `T₀ := 7(trank + 4)`
(`= 308` for `trank = 40`), `Rmax = ⌈60 ln n⌉`, `Emax = 208 n`, `Dmax = 32 n`, `N₀ := 1608`.
For every `n ≥ N₀` and every configuration `C₀` of the finite paper instance
`protocolPEMPaperFin n trank 208 32`,

`P_{C₀}[ S_em is hit within K interactions ] ≥ p₀`,  `K := (426.5 + 2T₀) n²`,  `p₀ := 0.2`,

so with `trank = 40`: `C = 1043`, `K ≤ 1043 n²`, `p₀ = 0.2` (the proof gives `0.2097`). `S_em`
(`IsSilentConsensus`) is silent (Lean Lemma 6), so the silence time `T_sil` satisfies the same bound.

**Corollary (§7).** `E[T_sil] ≤ K/p₀ ≤ 5212.5 n²` interactions `= 5212.5 n` parallel time;
`P[T_sil > j K] ≤ 0.8^j`; with `j = ⌈ln n / ln(5/4)⌉ ≤ 4 ⌈log₂ n⌉`:
`P[T_sil > 4172 n² ⌈log₂ n⌉] ≤ 1/n`, i.e. `O(n log n)` parallel time w.h.p.

Route (all windows deterministic; composition only by the Markov property at deterministic times and the
first-hit decomposition P2 Lemma 1.3):

```
any C ──(L9: Stage A, 0.861)──► S_rank ∪ PT_L
S_rank ──(L13: sort+decide, 0.915)──► D ∪ PT_L
PT_L ──(Prop 15: epoch 1 = B1,B2,B34,B56, 0.516)──► D
D ──(L17: countdown + mismatch, 0.9975)──► S_em ∪ Z
Z ──(Prop 20: epoch 2 with answers, 0.5166)──► Cons
Cons ──(L21: countdown, 1 − e^{−77})──► S_em
```

Main new ingredients: the swap-coupling Lemma 6 (packet item (a)), the tick bound for the median timer
(Lemma 4 + Lemma 11; replaces [K]'s "timer outlives the ranking w.p. ≥ 1/5"), the two-source no-wake
lemma (Lemma 18; fixes the answer issue (c) and R2's I3), and the corrected swap-time lemma (Lemma 12; [K]
L8 is false as printed, counterexample `n = 6`).

---

## 1. Setting

### 1.1 Scheduler and notation
`V = {0,…,n−1}`, `n ≥ N₀`. Steps `t = 1, 2, …` draw `e_t = (u_t, v_t)` i.i.d. uniform on the `n(n−1)`
ordered pairs of distinct agents (`uniformPair`; P1 §0.1, P2 §0.1). `X_t` is the configuration after `t`
steps, a deterministic function of `X₀, e_1, …, e_t`; `F_t = σ(e_1,…,e_t)`. Agent `v` carries a fixed input
`x_v ∈ {A, B}` (`Config.step` writes the transition output to the first coordinate and keeps the input).
`p := 2/(n(n−1))`, `κ := ln 4 − 1 > 0.3862`. All window lengths are in interactions.

We work on the flat state `AgentState n` restricted to `G` := configurations all of whose states satisfy
`GoodPEM T₀ Emax Rmax Dmax` (timer ≤ T₀, rc ≤ R, errorcount ≤ E, dt ≤ D, children ≤ 2). Every configuration of
the finite instance is the image of one in `G` under `encPEM`, `G` is invariant, and on `G` the encoding commutes
with the transition (`pemSimulation`). Hence every hitting probability below transfers (Used fact L4; open point O1).

Ranks are 0-indexed. Median rank `m* := ceilHalf(n) − 1`; last rank `n − 1`; `m* < n − 1` for `n ≥ 2`.
*Median-type ranks* `Mt := {m*}` if `n` is odd, `{m*, m*+1}` if `n` is even (`m* = n/2 − 1`).
`maj := majorityAnswer` (`outA`, `outB` or `outT`; never `phi`). `R, D, E` abbreviate `Rmax, Dmax, Emax`.

### 1.2 One interaction of P_EM (Lean)

Write `δ := rankDeltaOSSR R E D hn`. For a state `s` let `ρ(s)` be `s` with `answer := phi`, `timer := 0`
(the *ranking projection*).

**Lemma 1 (structure of one P_EM step; own, by inspection of `Transition.lean`, `RankDelta.lean`).**
Let the ordered pair be `(u, v)` with states `s₀, s₁`, inputs `x₀, x₁`, and `(r₀, r₁) := δ(s₀, s₁)`.

(a) `δ` reads only role, rank, leader, resetcount, children, errorcount, delaytimer, and copies `answer` and
`timer` unchanged. Hence `ρ(δ(s₀,s₁)) = δ(ρ s₀, ρ s₁)` componentwise.
(b) `transitionPEM_prePhase4` changes only `answer` and `timer` of `(r₀, r₁)`: (i) `answer := phi` for an
agent that is Resetting after `δ` and was not Resetting before; (ii) `timer := T₀` for an agent that is Settled
after `δ`, was not Settled before, and has rank `m*`; (iii) if both are Resetting after (i)–(ii), an agent with
answer `phi` copies a non-`phi` answer of the partner.
(c) `transitionPEM_phase4` is the identity unless both prePhase4 outputs are Settled. Then, in order:
*swap* — the two states are exchanged iff the initiator's state has the smaller rank, `x₀ = B`, `x₁ = A`;
*decide* — writes only `answer`: `n` odd: a state of rank `m*` gets the answer of its (new) holder's input;
`n` even: if the two states have ranks `m*` and `m*+1`, both get `opinionToAnswer(x)` if the inputs agree,
`outT` otherwise; *propagate* — if one state `b` has rank `m*` (the initiator's is tested first), then
`b.timer := b.timer ∸ 1` if the other has rank `n − 1` (a **tick**), and if then `b.timer = 0` and
`b.answer ≠` the other's answer, a **Phase-4 reset**: both get role Resetting, leader L, resetcount R, and the
other's answer `:= b.answer`; otherwise nothing more.
(d) Hence the ranking projection of the output is `(ρr₀, ρr₁)`, or `(ρr₁, ρr₀)` (swap, no reset), or both
states are (Resetting, L, R) (Phase-4 reset).
(e) A state moves to another agent only by a swap, and only Settled states are swapped.
(f) The timer of a Settled state of rank `m*` changes only by a tick or by the initialization (b)(ii) when the
state becomes Settled (a Settled state never changes its rank: `δ` writes `rank` only on recruitment of the
recruited agent and on an L-wake, i.e. when the agent becomes Settled).
(g) A Phase-4 reset in a step requires a Settled state of rank `m*` whose timer, after the possible tick, is 0.
(h) Leader bits change only by dedup (`b` from L to F, both still Resetting) and by triggers (OSSR collision or
expiry, or Phase-4 reset), which write L.

*Proof.* (a) Every branch of `propagateReset`, `processAgent`, `resetOSSR`, dedup and Parts 2–4 of
`rankDeltaOSSR` is a record update not naming `answer` or `timer` (Lean: `rankDeltaOSSR_answer_preserved`;
the timer case is the same inspection), and no guard reads them. (b), (c) are the code. (d) from (b), (c):
decide writes `answer`, a non-reset propagate writes `timer`. (e), (g), (h) are read off (b), (c) and `δ`.
(f): `timer` is written only in (b)(ii) and by the tick. ∎

*Remark (ticks of a newly created median state).* A state of rank `m*` created by recruitment has the recruiter
(rank `⌊(m*−1)/2⌋ ≠ n − 1`) as partner, so no tick and (timer `T₀ ≥ 1`) no reset happens in its creation step.
An L-wake gives rank 0 `≠ m*` for `n ≥ 3`.

### 1.3 Classes
- `PT_L`: some agent Resetting with rc `= R`, and some agent with leader L (P2 §0.3). Every trigger (OSSR or
  Phase-4) produces a configuration in `PT_L` (Lemma 1(c),(h); P2 Lemma 2.1(b)).
- `S_rank`: all agents Settled with pairwise distinct ranks (a bijection onto `{0,…,n−1}`). For `C ∈ S_rank`:
  `med(C)`, `last(C)` the agents holding ranks `m*`, `n−1`; `τ(C)` the timer of `med(C)`.
- `R(θ) := S_rank ∩ {τ ≥ θ}`.
- `S_sw := S_rank ∩ {x_v = A ⟺ rank(v) < n_A}` (sorted; `n_A` = number of A inputs).
- `D := S_sw ∩ {every agent with rank in Mt has answer maj}` (decided).
- `AnsOK := {every Settled agent with rank ∉ Mt has answer maj}`. `AllMaj := {every agent has answer maj}`.
- `Cons := D ∩ AnsOK`; this is exactly `IsConsensusConfig` (allSettled, ranks_inj, input_rank, all answers maj).
- `S_em := Cons ∩ {τ = 0}` = `IsSilentConsensus`; silent (`IsSilentConsensus.isSilent`), hence absorbing.
- `FD, FD_L^{½}, FD_1` as in P2 §7 (conditions on the ranking projection; all agents Resetting, rc = 0; with
  ≥ 1 L and all dt ≥ ⌊D/2⌋+1; resp. exactly one L).
- `Z`: exactly two agents are Resetting, both with rc `= R`, leader L, answer `maj`; every other agent is
  Settled; the Settled ranks are pairwise distinct and none equals `m*`.

**Lemma 2 (dynamics on S_rank; own).** Let `X_{k−1} ∈ S_rank`. In step `k`: `δ` is the identity
(`rankDeltaOSSR_settled_distinct_ranks`), prePhase4 is the identity (nobody changes role), Phase 4 runs.
So `X_k ∈ S_rank` unless step `k` is a Phase-4 reset (then `X_k ∈ PT_L`). A tick happens iff
`e_k ∈ {(med, last), (last, med)}`. If `X_{k−1} ∈ S_sw`, no swap happens (no pair has the B-agent at the
smaller rank), so `X_k ∈ S_sw` or a reset, holders of all ranks are unchanged, and decide writes `maj` to
median-type states. If `X_{k−1} ∈ D`, then `X_k ∈ D` or `X_k ∈ Z` (a reset), and the set
`M(X) := {w : answer(w) ≠ maj}` does not change in non-reset steps.

*Proof.* Lemma 1. Sorted ⇒ correct decisions: `n` odd, the holder of `m* = (n−1)/2` has input A iff
`n_A ≥ (n+1)/2` iff `maj = outA`; `n` even, the holders of `n/2 − 1`, `n/2` have inputs (A,A), (A,B), (B,B) iff
`n_A > n/2`, `= n/2`, `< n/2`, giving `outA, outT, outB = maj`. In `D` a reset needs the median (answer `maj`)
to meet `w` with answer `≠ maj` (for `n` even the rank-`m*+1` agent gets `maj` from decide in the same step,
so it never causes a reset); the result has `med` and `w` Resetting with rc R, L, answer `maj`, and the other
`n − 2` agents Settled with distinct ranks `≠ m*`: that is `Z`. ∎

---

## 2. Probability tools

**Lemma 3 = P2 Lemmas 1.1–1.3 (used as given).** Markov property at deterministic times; chaining at
deterministic times (P2 1.2(i),(ii)); composition at a hitting time (P2 1.3: if `P_Y[τ_{H′} ≤ T_B] ≥ q_B` for
all `Y ∈ H`, then `P_X[τ_{H′} ≤ T_A + T_B] ≥ q_B P_X[τ_H ≤ T_A]`). Since the final target `S_em` is absorbing,
"hit `S_em` within `T`" is monotone in `T`, so continuations of different lengths from different parts of `H`
are combined by taking the largest window and the smallest probability.

**Lemma 4 (Bernoulli selectors; own).** Let `(a_k, b_k)` be `F_{k−1}`-measurable random pairs of distinct agents
and `c_k` an `F_{k−1}`-measurable agent, `k = 1, …, L`. Then
`J_k := 1[e_k ∈ {(a_k,b_k), (b_k,a_k)}]` are i.i.d. Bernoulli(`p`), `J′_k := 1[e_k = (a_k, b_k)]` are i.i.d.
Bernoulli(`1/(n(n−1))`), and `I_k := 1[c_k ∈ e_k]` are i.i.d. Bernoulli(`2/n`).
Consequently: (i) `Σ_{k≤L} J_k ~ Bin(L, p)`; (ii) if `J_k = 1` implies `τ ≤ k` for a random time `τ`, then
`P[τ > L] ≤ (1 − p)^L ≤ exp(−pL)`.

*Proof.* `e_k` is independent of `F_{k−1}` and uniform; for every fixed distinct pair the probability of the
two orders is `p`. So `P[J_k = 1 | F_{k−1}] = p` a.s., and for `j ∈ {0,1}^L`, conditioning on `F_{L−1}` and
inducting, `P[J = j] = Π p^{j_k}(1−p)^{1−j_k}`. Same for `J′`, `I`. (ii): `{τ > L} ⊆ {J_1 = … = J_L = 0}`. ∎

**Chernoff (P2 Lemma 1.5, used as given).** For `X ~ Bin(N, q)`, `μ = Nq ≤ μ⁺`:
(a) `P[X ≥ 2μ⁺] ≤ e^{−κμ⁺}`; (b) `P[X ≥ k] ≤ (e μ/k)^k` for `k ≥ μ`; (c) `P[X ≤ μ/2] ≤ e^{−μ/8}`.

**Lemma 5 (monotone index; = P2 Lemma 1.4, used as given).** If `Z_t` is adapted, nonincreasing, with values
in a finite totally ordered set, and `P[Z_{t+1} ≠ z | F_t] ≥ p_z > 0` on `{Z_t = z}`, then
`E[#{t : Z_t = z}] ≤ 1/p_z`.

---

## 3. The swap coupling (packet item (a))

**Lemma 6 (swap invariance; own).** Fix a P_EM configuration `X₀ ∈ G` and run the P_EM chain `X_t` with the
pairs `e_t`. Let `τ_P` be the first step at which a Phase-4 reset occurs (`∞` if none). Define bijections
`π_t : V → V` by `π₀ = id`; for `t ≥ 1`, `π_t := π_{t−1} ∘ (u_t v_t)` if `t < τ_P` and step `t` swaps
(Lemma 1(c)), else `π_t := π_{t−1}`. Put `e′_t := (π_{t−1}(u_t), π_{t−1}(v_t))` and let `Y_t` be the
`rankDeltaOSSR` chain started at `Y₀ := ρ∘X₀` and driven by `(e′_t)`. Then:

1. `(e′_t)_{t≥1}` is i.i.d. uniform on ordered distinct pairs; hence `(Y_t)` has the law of the OSSR chain
   from `ρ∘X₀`, and every probability bound of P2 for that chain applies to `Y`.
2. For every `t < τ_P` and every agent `w`: `ρ(X_t(w)) = Y_t(π_t(w))`.
3. For every step `t < τ_P`: step `t` of `X` is an OSSR trigger (collision or expiry) iff step `t` of `Y` is,
   and the same holds for "recruitment", "wake", "dedup".

*Proof.* (1) `π_{t−1}` is `F_{t−1}`-measurable, and for every fixed ordered pair `(a, b)`,
`P[e′_t = (a,b) | F_{t−1}] = P[e_t = (π_{t−1}^{−1}a, π_{t−1}^{−1}b) | F_{t−1}] = 1/(n(n−1))`. So `e′_t` is
independent of `F_{t−1} ⊇ σ(e′_1, …, e′_{t−1})` and uniform; induct as in Lemma 4.
(2) Induction on `t`. `t = 0`: definition. Step `t < τ_P` with `e_t = (u, v)`; write `ũ = π_{t−1}(u)`,
`ṽ = π_{t−1}(v)`. By the hypothesis, `(ρX_{t−1}(u), ρX_{t−1}(v)) = (Y_{t−1}(ũ), Y_{t−1}(ṽ))`; by Lemma 1(a),
`(ρr₀, ρr₁) = δ(Y_{t−1}(ũ), Y_{t−1}(ṽ)) = (Y_t(ũ), Y_t(ṽ))`. By Lemma 1(d) (no reset since `t < τ_P`):
without swap `ρX_t(u) = ρr₀ = Y_t(π_t u)`, `ρX_t(v) = Y_t(π_t v)`; with swap `ρX_t(u) = ρr₁ = Y_t(ṽ) =
Y_t(π_t u)` and symmetrically for `v`. Other agents: both sides unchanged.
(3) These are properties of `δ` on the pair of ranking projections, which agree by (2) at `t − 1`. ∎

**Corollary 7 (the ranking modulo agent names; exact statement).** For every `X₀ ∈ G`, the process of
multisets `⟦ρ∘X_t⟧` stopped before `τ_P` coincides pathwise with `⟦Y_t⟧` (`t < τ_P`), whose law is that of the
multiset process of OSSR from `⟦ρ∘X₀⟧`. In particular, for every set `A` of OSSR configurations closed under
permutations of agents and every path event `B` of `Y`:
`P[ρ∘X_t ∈ A, τ_P > t] = P[Y_t ∈ A, τ_P > t] ≥ P^{OSSR}_{ρX₀}[A at t] − P[τ_P ≤ t]`, and
`P[{Y ∈ B} ∩ {τ_P > t}]` is the probability that `B` happens to the ranking of P_EM (modulo `π`) up to `t`.

So the swap does not change the ranking in law; the only interference of P_EM with the ranking is the
Phase-4 reset, which Lemma 11 controls through the tick count.

---

## 4. Ranking inside P_EM

**Lemma 8 (P2's structural lemmas for P_EM; own transfer).** With "trigger" meaning an OSSR trigger or a
Phase-4 reset, P2 Lemmas 2.1, 2.2 (Corollary), 2.3, 2.4, 2.5 (Corollary), 2.6 hold verbatim for the P_EM chain;
P2 Lemma 2.4(c) holds in every non-trigger step; P2 Lemma 2.7's last sentence holds for every Unsettled agent.

*Proof.* 2.1, 2.2: P1 Lemma 1 (stated for `transitionPEM`) is exactly 2.1(a),(b); (c) because only the two
participants change. 2.3: Lemma 1(h). 2.4: a Resetting agent's step is Part 1 of `δ`; Phase 4 does not apply
to a pair one of which is Resetting after prePhase4, and a propagating agent stays Resetting after `δ`
(`processAgent` acts only at rc 0); an agent becomes Resetting only by recruitment or a trigger (Lemma 1(b),(c)).
A woken agent may then be swapped (Lemma 1(e)) but is computing after the step unless the step is a trigger.
2.5, 2.6: their proofs use only 2.1–2.4, per-agent interaction counts of dormant agents (whose states do not
move, Lemma 1(e)), and the absence of computing agents (2.6), under which P_EM acts as `δ` on ranking fields.
2.7: Unsettled states do not move (Lemma 1(e)); an Unsettled agent's interaction is Part 3 (recruited) or
Part 4 (decrement) of `δ`, whatever Phase 4 does afterwards. ∎

**Lemma 9 (Stage A, [K] L7 first half for every configuration; P2 Prop. 7.6 for P_EM).** Let
`H := S_rank ∪ PT_L`, `K_A := t₁ + 241 n²`. For every `X ∈ G`: `P_X[τ_H ≤ K_A] ≥ q_A := 0.861`.

*Proof.* P2's proof of Prop. 7.6, step by step, with Lemma 8 in place of P2 §2. On `{τ_H > t}` there is no
trigger in `[1, t]` (every trigger produces `PT_L`). Case `X ∉ PT`: A1 (P2 Lemma 5.1: `r` is the max-process by
Lemma 8/2.2(b); P2 Lemma 3.1) — failure `≤ 1/(3n)`. A2 from `ND`: Lemma 8/2.5 and P2 Cor. 1.6 row 3 — failure
`≤ n e^{−8n}`; no agent becomes Resetting without a propagating agent or a trigger. A3 from `FC`: Lemma 8/2.7
for Unsettled agents (their states do not move) and Cor. 1.6 row 5 — all Settled at `W_E`, failure
`≤ n e^{−52n}`. A4 from all-Settled `Y`: if the ranks are distinct, `Y ∈ S_rank ⊆ H`. Otherwise fix two states
with equal rank; swaps permute states but keep both (Lemma 1(e)); let `(a_k, b_k)` be their holders at `k − 1`
(`F_{k−1}`-measurable). `J_k = 1` before any trigger is a collision (both Settled, equal ranks, OSSR Part 2), so
by Lemma 4(ii) `P[τ_H > n²] ≤ e^{−2n/(n−1)} ≤ e^{−2}`. Case `X ∈ PT_0`: P2 Lemma 4.1 for P_EM (Lemma 10 below)
gives `FD_0` at `t₁` on `{τ_H > t₁}` up to `(c₂+1/3)/n + n 2^{−16n}` (no L without trigger, Lemma 1(h));
Stage 2 as A2 (all wake Unsettled; Settled states arise only from an L-wake or a recruitment); Stage 3: no
Settled agent, so no swap and no Phase 4, and the pigeonhole on `208 n²` participations forces an expiry.
Numbers as in P2: `q_A ≥ 1 − 0.1387 ≥ 0.861`. ∎

**Lemma 10 (Stages B1, B2 for P_EM; transfer of P2 Lemmas 4.1 = 7.1 and 7.2).** For `n ≥ N₀`:
(B1) from every `X ∈ PT_L ∩ G`: `P[X_{t₁} ∈ FD_L^{½}] ≥ q_{B1} := 1 − (7/3)/n − n 2^{−16n} ≥ 0.99854`;
(B2) from every `X ∈ FD_L^{½}`: `P[X_{t₂} ∈ FD_1] ≥ q_{B2} := 3/4 − n e^{−8κn}`; on this event no agent wakes and
no agent changes its answer except by the epidemic (b)(iii).
(Here `t₁ = K₃₂ + t₃₃ ≤ n²/2`, `K₃₂ = ⌈4n ln n⌉`, `t₂ = 4n(n−1)`; P2 §0.4, R2.)

*Proof.* (B1) P2's proof of Lemma 4.1: G1 is P1 Theorem A (stated for `transitionPEM`, fixed-time form at
`T = K₃₂`, R2 §1); G2 is a scheduler event; on G1 ∩ G2, Lemma 8/2.6 gives no wake and no trigger in
`(K₃₂, t₁]`; G3 is P2 Lemma 3.1 at the deterministic time `K₃₂` (Lemma 3); (ii) dt bound from Lemma 8/2.6;
(iv) Lemma 1(h). (B2) On P2's event (nobody has `≥ 16n` interactions in `t₂` steps) nobody wakes, so all agents
stay Resetting, Phase 4 never runs, P_EM acts as `δ` on ranking fields, and P2's leader chain argument is
unchanged; answers change only through prePhase4 (b)(iii) since nobody becomes Resetting from computing. ∎

**Lemma 11 (Stage B34: tree ranking inside P_EM with the median timer; [K] L7 second half, K-timer).**
Let `W₃₄ := W_D + W_R = 52 n²`. From every `X ∈ G` whose ranking projection is in `FD_1`:

`P[ X_{W₃₄} ∈ R(T₀ − 209), no trigger of any kind in (0, W₃₄] ] ≥ q₃₄ := q_{B3}⁺ q_{B4}⁺ − e^{−105κ} ≥ 0.75325`.

If moreover `X ∈ AllMaj`, then on the same event `X_{W₃₄} ∈ AnsOK`.

*Proof.* Couple with `Y` by Lemma 6. Let `E_Y` := {no OSSR trigger of `Y` in `(0, W₃₄]` and `Y_{W₃₄} ∈ S_rank`}.
By the "+" forms of P2 Lemmas 7.3, 7.4 (Used fact P2-c) and Lemma 3, `P[E_Y] ≥ q_{B3}⁺ q_{B4}⁺ ≥
(1 − 10⁻⁹)(1 − π²/40 − 10⁻⁹)`. On `E_Y`, by P2 Lemma 2.9(a) from `FD_1` (A = ∅, one L, dormant; R2 I5),
every `Y_k`, `k ≤ W₃₄`, is `VT⁻`: Settled ranks pairwise distinct, and every Settled state of `Y_k` was
created at some step in `[1, k]` (`Y₀` has none).

Ticks. For `k ≥ 1` let `(a_k, b_k)` be the holders in `X_{k−1}` of the unique Settled state of rank `m*` and of
rank `n−1` if both exist uniquely, and `(0, 1)` otherwise; `F_{k−1}`-measurable. Let `J_k` be as in Lemma 4, so
`N := Σ_{k ≤ W₃₄} J_k ~ Bin(W₃₄, p)`, `μ = 104 n/(n−1) ≤ 105`, and `P[N ≥ 210] ≤ e^{−105κ} < 3·10⁻¹⁸`.

Claim: on `E_Y ∩ {N ≤ 209}`, `τ_P > W₃₄`. Suppose `τ_P ≤ W₃₄`. For `k < τ_P` Lemma 6(2) transfers `VT⁻` to
`X_k`, so Settled ranks of `X_k` are distinct, every tick at a step `k ≤ τ_P` has `J_k = 1` (Lemma 1(c)), and
no Settled state leaves Settled before `τ_P` (no OSSR trigger by Lemma 6(3)). The reset at `τ_P` is made by a
Settled state `b` of rank `m*` present in `X_{τ_P − 1}` (Remark after Lemma 1: a state created in step `τ_P`
cannot reset in that step). `b` was created at a step `c ∈ [1, τ_P)` with timer `T₀` (Lemma 1(b)(ii); `X₀` has no
Settled state), and its timer is `T₀ ∸ (ticks of b in (c, τ_P])` (Lemma 1(f)). Timer 0 needs `≥ T₀ ≥ 308 > 209`
ticks: contradiction.

So on `E_Y ∩ {N ≤ 209}`: `ρ∘X_{W₃₄} = Y_{W₃₄}∘π_{W₃₄} ∈ S_rank` (permutation-invariant), hence
`X_{W₃₄} ∈ S_rank`; its median state was created in the window with `T₀` and has `≤ 209` ticks:
`τ ≥ T₀ − 209`; and no trigger occurred. Probability `≥ P[E_Y] − P[N ≥ 210] ≥ 0.753259 − 3·10⁻¹⁸`.

Answers. If `X₀ ∈ AllMaj` (all agents Resetting with answer `maj`): in `(0, W₃₄]` there is no trigger and no
propagating agent (`r ≡ 0`, Lemma 8/2.2(b)), so nobody becomes Resetting from computing (no `phi` is
written, Lemma 1(b)(i)), the epidemic (b)(iii) has no `phi` to fill, `δ` and wakes keep answers
(`resetOSSR_answer_preserved`), and decide writes only to states of rank in `Mt` (Lemma 1(c)); a state's rank
never changes once Settled (Lemma 1(f)). So every state whose rank is not in `Mt` keeps `maj`: `AnsOK`. ∎

---

## 5. Sorting and decision

**Lemma 12 (swap time; corrected [K] L8; own).** Let `X₀ ∈ S_rank` and let `σ` be the first time at which the
configuration is in `S_sw` or a Phase-4 reset has occurred. Let `J := |V_B(X₀)|`, `V_B` = agents with input B and
rank `< n_A` (`|V_A| = |V_B|` for `V_A` = A-agents with rank `≥ n_A`). Then
`E[σ] ≤ Σ_{j=1}^{J} n(n−1)/j² < (π²/6) n(n−1)`; in the reset-free swap dynamics (Phase 4c disabled) this holds
with equality.

*Proof.* Before `σ`, `X ∈ S_rank` (Lemma 2), and ranks move only by swaps. A swap exchanges a B-agent at rank
`r₁` with an A-agent at rank `r₂ > r₁`; `|V_B|` drops by 1 iff `r₁ < n_A ≤ r₂` and is unchanged otherwise. So
`Z_t := |V_B(X_t)|` for `t < σ`, `Z_t := 0` for `t ≥ σ` is nonincreasing; `Z = 0` iff sorted (the `n_A` ranks
below `n_A` are then held by the `n_A` A-agents). From `Z_t = j ≥ 1`, each of the `j²` **ordered** pairs
`(b, a)`, `b ∈ V_B`, `a ∈ V_A`, swaps (`rank(b) < n_A ≤ rank(a)`, `x₀ = B`, `x₁ = A`); the reverse order
`(a, b)` does not (Lemma 1(c)). So the exit probability is `≥ j²/(n(n−1))` (exactly, without resets), and
Lemma 5 summed over `j` gives the bound. ∎

**Lemma 13 (Stage A′: S_rank → D ∪ PT_L; corrected [K] L9 first half).** From every `X ∈ S_rank` (any timer, any
answers, any placement of inputs): `P[τ_{D ∪ PT_L} ≤ 23 n²] ≥ q_{A′} := 1 − π²/120 − e^{−6} ≥ 0.9152`.

*Proof.* P2 Lemma 1.2(ii) with `A = S_sw`. First `20 n²` steps: on `{τ_{PT_L} > 20n²}` there is no reset, and
`X_{20n²} ∉ S_sw` means `σ > 20 n²`; by Markov and Lemma 12, `P ≤ (π²/6)n(n−1)/(20n²) < π²/120`. From
`Y ∈ S_sw`: holders are fixed until a reset (Lemma 2); let `J_k` (n even: holders of ranks `m*`, `m*+1`) or
`I_k` (n odd: holder of `m*`, any partner, all are Settled) be Lemma 4's indicators; the first such step decides
(Lemma 1(c)), after which `X ∈ D` (Lemma 2) unless a reset occurs. Failure in `3n²` steps `≤ e^{−6n/(n−1)}`
(n even) or `e^{−6n}` (n odd), `≤ e^{−6}`. ∎

**Lemma 14 (Stage B56: R(θ) → D; corrected [K] L10).** Let `θ ≥ 94`, `W₅₆ := 23 n²`. From every `X ∈ R(θ)`:
`P[X_{W₅₆} ∈ D ∩ R(θ − 93), no reset in (0, W₅₆]] ≥ q₅₆ := 1 − π²/120 − e^{−6} − e^{−47κ} ≥ 0.91527`.
If `X ∈ AnsOK`, then on this event `X_{W₅₆} ∈ Cons`.

*Proof.* Let `J_k` be the tick indicators of `(med, last)` in `X_{k−1}` (defined while `X_{k−1} ∈ S_rank`, dummy
otherwise) and `N₅₆ := Σ_{k ≤ W₅₆} J_k ~ Bin(23n², p)`, `μ = 46n/(n−1) ≤ 47`, `P[N₅₆ ≥ 94] ≤ e^{−47κ} < 1.4·10⁻⁸`.
On `{N₅₆ ≤ 93}`, by induction over steps (Lemma 2: while no reset, `X ∈ S_rank`, ticks are counted by `J`), the
timer after every tick is `≥ θ − 93 ≥ 1`, so no reset occurs (Lemma 1(g)), and `X_{W₅₆} ∈ R(θ − 93)`. On that
event Lemma 12 (with `σ` = sorting time) and Markov give sorting by `20 n²` except `π²/120`, and the decision
argument of Lemma 13 gives `D` by `23 n²` except `e^{−6}`; `D` persists without reset (Lemma 2). `AnsOK`:
without reset and without Resetting agents, only decide writes answers, only to ranks in `Mt`; so
`D ∩ AnsOK = Cons`. ∎

**Proposition 15 (epoch 1: PT_L → D; [K] L7 + L9 second half + L10).** Let
`K_B := t₁ + t₂ + W₃₄ + W₅₆ ≤ 79.5 n²` (`t₁ ≤ n²/2`, `t₂ ≤ 4n²`). From every `X ∈ PT_L ∩ G`:
`P[X_{K_B} ∈ D] ≥ q_B := q_{B1} q_{B2} q₃₄ q₅₆ ≥ 0.5163`.

*Proof.* Lemma 3 (P2 1.2(i)) applied to Lemma 10 (B1, B2), Lemma 11 (`FD_1 → R(T₀ − 209)`), Lemma 14 with
`θ = T₀ − 209 ≥ 99 ≥ 94`. Numbers (`n ≥ 1608`): `0.998549 · 0.75 · 0.753259 · 0.915275 ≥ 0.5163`. ∎

Answers are not tracked in epoch 1: a configuration in `D` may carry arbitrary (stale, `phi`, wrong) answers
outside `Mt`; Lemma 17 turns that into a correct reset.

---

## 6. Countdown, propagation, second epoch

**Lemma 16 (countdown in S_rank; corrected [K] L11).** From `X ∈ S_rank` with `τ(X) = x`, as long as no reset
occurs the timer of the median state decreases by exactly one at each step with `e_k ∈ {(med,last),(last,med)}`,
an event of conditional probability exactly `p = 2/(n(n−1))` (not `2/(n(n−2))`); no reset can occur while the
timer is positive (Lemma 1(g)). Hence the time to timer 0 is a sum of `x` i.i.d. `Geom(p)`, with mean
`x n(n−1)/2` interactions `= x(n−1)/2` parallel time, and `P[timer > 0 after L steps] = P[Bin(L, p) < x]`.
With `L = T₀ n² ≥ x n²`: `μ ≥ 2T₀`, so `P ≤ P[Bin ≤ μ/2] ≤ e^{−T₀/4}`.

*Proof.* Lemma 2 and Lemma 4 (the holders are `F_{k−1}`-measurable; timer `> 0` excludes reset, so `S_rank`
persists and med, last exist uniquely). Chernoff (c). ∎

**Lemma 17 (Stage C: D → S_em ∪ Z; [K] L12 first half).** From every `X ∈ D` (any timer `≤ T₀`):
`P[τ_{S_em ∪ Z} ≤ (T₀ + 3) n²] ≥ q_C := 1 − e^{−T₀/4} − e^{−6} ≥ 0.99752`.

*Proof.* P2 Lemma 1.2(ii) with `A := D ∩ {τ = 0}`. Until `τ_Z`, `X ∈ D` (Lemma 2), so Lemma 16 gives
`P[τ_Z > T₀ n², X_{T₀n²} ∉ A] ≤ e^{−T₀/4}`. From `Y ∈ A`: if `M(Y) = ∅` then `Y ∈ S_em`. Otherwise fix
`w ∈ M(Y)`; holders are fixed until a reset (Lemma 2); with `(a_k, b_k) = (med, w)`, `J_k = 1` gives a Phase-4
reset at step `k` (the timer stays 0 under `∸ 1`; the median's answer is `maj` after decide, `w`'s is not; both
orders of the pair reach the reset branch, Lemma 1(c)); by Lemma 2 the result is in `Z`. Lemma 4(ii):
`P[τ_Z > 3n²] ≤ e^{−6}`. ∎

**Lemma 18 (two sources, no wake; strengthened B32, needed form of P1 Theorem A).** Let `X₀ ∈ Z` with Resetting
agents `s, s′`, and `T := K₃₂ = ⌈4 n ln n⌉`. There is an event `E_{18}` with
`P[E_{18}] ≥ 1 − 1/n − 4 n^{−12.2}` on which:
(i) in `(0, T]` there is no trigger, no wake, and no dormant agent;
(ii) at every `t ≤ T` every Resetting agent is propagating and has answer `maj`;
(iii) `X_T` is fully propagating (all agents Resetting with rc `≥ 1`) and `X_T ∈ AllMaj`.

*Why this form.* P1 Theorem A gives (iii)'s first half only; the answers need that no agent leaves Resetting
and re-enters (re-entry clears to `phi`, OSSR triggers write `phi` to both agents), and that no Phase-4 reset
writes a non-`maj` answer. Everything below uses only P1 Lemma 2, Lemma 4, Corollary 5, Lemma 6 / (3.1) and
Lemma 10, each as stated.

*Proof.* Let `x^s, x^{s′}` be P1's pure processes from `s`, `s′` with `R`, and `Rch^s, Rch^{s′}` the reached sets.
P1 Lemma 2 applies to each (each is Resetting with rc `≥ R`): `r(X_t(w)) ≥ max(x^s_w(t), x^{s′}_w(t))` pathwise.
Let `E_{18} := E₁^s ∩ E₂^s ∩ E₂^{s′}` with P1's events (`E₁^s = {T_n^s ≤ T}`, `E₂^·` = every realized walk from the
source over `(0, T]` has cost `≤ R − 1`, the trivial walk included). P1 Lemma 10 and (3.1) (computed in the proof
of Theorem A) give the probability bound. On `E₂^s`, P1 Corollary 5 (with `t` = the entry time of `w`) gives
`x^s_w(t′) ≥ 1` for all `w ∈ Rch^s(t)` and `t ≤ t′ ≤ T`; likewise for `s′`.

Induction on `t ≤ T` of the statement `P(t)`: up to time `t` no trigger and no wake occurred; every Resetting agent
lies in `Rch^s(t) ∪ Rch^{s′}(t)`, is propagating, and has answer `maj`; the computing agents are Settled with pairwise
distinct ranks, none equal to `m*`. `P(0)`: definition of `Z`. Step `t` with pair `{u, v}`:
- both computing: `δ` is the identity (distinct ranks), Phase 4 can only swap (decide and propagate need a
  Settled state of rank `m*`; for `n` even the decide pair needs rank `m*` too): no trigger, no answer change;
- `u` Resetting (propagating, in a reached set), `v` computing: recruitment; `v` enters the same reached set at `t`,
  so `r(v) ≥ 1` at `t`; `u` stays propagating; prePhase4 clears `v`'s answer and the epidemic copies `u`'s `maj`
  (Lemma 1(b)); no trigger (Part 1 only), no Phase 4 (both Resetting);
- both Resetting: both in reached sets, both `r ≥ 1` after the step, so no `processAgent` action (no wake); answers
  unchanged.
No agent is ever dormant, so no wake; collisions, expiries and Phase-4 resets need two equal Settled ranks, an
Unsettled agent, or a Settled rank `m*`, none of which exists. At `T`, `E₁^s` gives `Rch^s(T) = V`, so all
agents are propagating with answer `maj`. ∎

**Lemma 19 (Stage B1′ from Z; [K] L12, the propagation of the correct answer).** From every `X ∈ Z`:
`P[X_{t₁} ∈ FD_L^{½} ∩ AllMaj, no trigger in (0, t₁]] ≥ q′_{B1} := 1 − (4/3)/n − 4 n^{−12.2} − n 2^{−16n} ≥ 0.99917`.

*Proof.* Lemma 18 on `[0, K₃₂]`; then P2's G2 (nobody has `≥ 16n` interactions in `(0, t₁]`, failure
`n 2^{−16n}`) and G3 (max-process from `K₃₂` is 0 at `t₁`, failure `1/(3n)`, Lemma 3). On these, Lemma 8/2.6 from
the fully propagating `X_{K₃₂}`: no wake and no trigger in `(K₃₂, t₁]`, all agents Resetting; `r` is the
max-process (Lemma 8/2.2(b)), 0 at `t₁`; dt `≥ ⌊D/2⌋ + 1`; answers unchanged (nobody becomes Resetting from
computing; no `phi` to fill); `#L ≥ 1` (Lemma 1(h); `s` is L at time 0). ∎

**Proposition 20 (epoch 2: Z → Cons; [K] L12 second half).** From every `X ∈ Z`:
`P[X_{K_B} ∈ Cons] ≥ q′_B := q′_{B1} q_{B2} q₃₄ q₅₆ ≥ 0.5166`.

*Proof.* Lemma 19; Lemma 10 (B2: no wake, all Resetting, answers all `maj`, so the epidemic changes nothing:
`FD_1 ∩ AllMaj`); Lemma 11 with `AllMaj` (`R(T₀ − 209) ∩ AnsOK`); Lemma 14 with `AnsOK` (`Cons`). Chained by
Lemma 3. ∎

**Lemma 21 (Cons → S_em; [K] L13).** From every `X ∈ Cons`: `P[X_{T₀ n²} ∈ S_em] ≥ q_E := 1 − e^{−T₀/4}`.

*Proof.* On `Cons` a step only applies `medianTick` (Lean `consensus_step_apply`), so `Cons` is closed and the
timer counts down exactly as in Lemma 16; at timer 0 the configuration is in `S_em`. ∎

---

## 7. Composition ([K] L14) and constants

**Theorem 22 (= Theorem W).** For `n ≥ N₀ = 1608`, `trank ≥ 40`, every `X ∈ G`:
`P_X[τ_{S_em} ≤ K] ≥ q_A q_{A′} q_B q_C q′_B q_E`, `K := K_A + 23n² + 2K_B + (T₀ + 3)n² + T₀ n² ≤ (426.5 + 2T₀) n²`.

*Proof.* Backward, by Lemma 3 (P2 1.3; `S_em` absorbing, so windows are padded to the largest):
- from `Cons`: window `V_E := T₀n²`, prob `q_E` (L21);
- from `Z`: `V_Z := K_B + V_E`, `q_Z := q′_B q_E` (Prop 20, then L21 at the deterministic time `K_B`);
- from `D`: `V_D := (T₀+3)n² + V_Z`, `q_D := q_C q_Z` (L17; continuation from `S_em` has prob 1);
- from `PT_L`: `V_PT := K_B + V_D`, `q_PT := q_B q_D` (Prop 15);
- from `S_rank`: `V_SR := 23n² + V_PT`, `q_SR := q_{A′} q_PT` (L13; from `D` the continuation `V_D ≤ V_PT`, `q_D ≥ q_PT`);
- from any `X ∈ G`: `K = K_A + V_SR`, `q := q_A q_SR` (L9; `H = S_rank ∪ PT_L`). ∎

| quantity | value (n ≥ 1608, trank = 40, T₀ = 308) |
|---|---|
| `q_A` (L9) | 0.861 |
| `q_{A′}` (L13) | 1 − π²/120 − e^{−6} ≥ 0.91527 |
| `q_B` (Prop 15) | 0.998549 · 0.75 · 0.753259 · 0.915275 ≥ 0.51632 |
| `q_C` (L17) | 1 − e^{−77} − e^{−6} ≥ 0.99752 |
| `q′_B` (Prop 20) | 0.999170 · 0.75 · 0.753259 · 0.915275 ≥ 0.51665 |
| `q_E` (L21) | 1 − e^{−77} |
| product | ≥ 0.2097 → `p₀ = 0.2` |
| `K` | (241.5 + 23 + 159 + 311 + 308) n² = 1042.5 n² → `C = 1043` |

`trank`: the proof needs `T₀ ≥ 209 + 93 + 1 = 303`, i.e. `trank ≥ 40`; `T₀` enters `K` only through the two
countdowns. [K]'s recipe `s_rank ≤ trank·n` with P2's `E[T] ≤ 621 n²` would give `trank = 621`, also covered
(`C = 427 + 14(trank + 4)`, same `p₀`).

**Corollary 23 (expected and w.h.p. time).** The finite instance is closed, so Theorem 22 holds from every
configuration reached. By Lemma 3 at the deterministic times `jK`:
`P[τ_{S_em} > jK] ≤ (1 − p₀)^j = 0.8^j`, and `E[τ_{S_em}] ≤ Σ_{j≥0} K 0.8^j = K/p₀ ≤ 5212.5 n²` interactions.
`T_sil ≤ τ_{S_em}`. With `j := ⌈ln n/ln 1.25⌉ ≤ 3.107 log₂ n + 1 ≤ 4⌈log₂ n⌉` (n ≥ 1608):
`P[T_sil > 4172 n² ⌈log₂ n⌉] ≤ 1/n`. In the Lean targets (`KanayaThm4Time`, `e = 208`, `d = 32`,
`trank = 40`, `N₀ = 1608`): `c₁ = 5213` (parallel time), `c₂ = 4172`. (Lean: `expectedHittingTime_le_window_mul_inv_of_invariant`,
`probNotHitBy_mul_window_le_initial_mul_pow_of_invariant`, `expectedHittingTime_mono_goal`, `probNotHitBy_mono_goal`.)

---

## 8. The printed statements of [K] (Table 2) for the Lean protocol

| [K] | printed | verdict | replacement here |
|---|---|---|---|
| L7 | `C₀ ∈ S_rank` ⇒ reach `S_rank` in `O(n)` time w.p. ≥ 1/10 | true but vacuous (`C₀` is already in `S_rank`); the intended form from `C_all` is not proved by the printed argument: it applies [B] Lemma 4 to the ranking inside P_EM without the coupling, ignores Phase-4 resets from stale median timers before the reset, and its Chernoff window (`trank n²`) is half the Markov window `2 s_rank` | L9 + Prop 15 (first three stages): from every `C`, `P[τ_{S_rank} ≤ K_A + t₁ + t₂ + 52n² ≤ 298n²] ≥ 0.861 · 0.564 ≥ 0.485` |
| L8 | from `S_rank`, no reset: `E[time to S_swap] ≤ n` | **false** (factor 2: a pair `(a ∈ V_A, b ∈ V_B)` swaps in one order only) | L12: `E = Σ_{j ≤ J} n(n−1)/j²` interactions `< (π²/6)(n−1)` parallel time |
| L9 | `C₀ ∈ S_rank ∩ T_swap` ⇒ reach `T_swap ∪ S_tim` w.p. ≥ 1/20 | true but vacuous (`C₀ ∈ T_swap`); intended form (from `S_rank`) needs the coupling and the tick bound | L13 (`S_rank → D ∪ PT_L`, 0.915) + Prop 15 (`PT_L → D`, 0.516) |
| L10 | `T_swap → S_dec` within `3n − 1` time w.p. ≥ 1/8 | statement true (n ≥ 3): sorting within `2n²` w.p. `≥ 1 − (π²/6)(n−1)/(2n) ≥ 0.1775`, decision within `n(n−1)` w.p. `≥ 1 − e^{−2}`, `≥ 28` ticks in `3n²` steps w.p. `≤ (8e/28)^{28} < 10⁻³`; product `≥ 0.152`. The printed proof uses the false L8 | L14 (`R(θ) → D ∩ R(θ − 93)`, 0.915, `23n²`) |
| L11 | timer 0 within `x(n−1)` time w.p. ≥ 1/2; pair prob `2/(n(n−2))` | true with pair prob `2/(n(n−1))`; holds from every `S_rank` configuration (no reset before timer 0) | L16 |
| L12 | `S_dec → S_tim` in `O(n)` w.p. ≥ 1/1280 | statement true (n ≥ N₀); printed proof has gaps: the answer epidemic does not handle answers cleared by re-entry or by OSSR triggers, nor wake-ups before full propagation (R2 I3), and it cites "latter part of L9" for the timer | L17 + L18–Prop 20: `D → S_em ∪ Z → Cons`, prob ≥ 0.9975 · 0.5166 within `(T₀+3)n² + K_B`. For `n` even [K]'s `S_dec` does not fix the rank-`m*+1` answer; one decision meeting (Lemma 13's argument, `e^{−6}`) or a reset (into `Z`, the median's answer being `maj`) reduces it to `D ∪ Z` |
| L13 | `S_tim → S_em` w.p. ≥ 1/2 | true (`S_tim = Cons`) | L21 (`1 − e^{−T₀/4}`) |
| L14 | composition; 1/4096000 | arithmetic correct; composition invalid as printed (L7, L9 hypotheses do not cover the states reached) | Theorem 22, Corollary 23 |

**Counterexample to [K] L8 (smallest `n`).** `n = 6`, inputs `A, A, A, B, B, B`, all Settled, ranks: the three
B-agents hold ranks 0, 1, 2 and the three A-agents ranks 3, 4, 5 (0-indexed); median timer `T₀`. Without Phase-4
resets (Phase 4c disabled; equivalently on `{τ_P > σ}`, whose probability → 1 as `trank → ∞`), `|V_B|` is a
pure death chain with rates `j²/30`, so `E[σ] = 30(1 + 1/4 + 1/9) = 40.83 > 36 = n²` interactions, i.e.
`6.81 > n = 6` parallel time. (`n = 5`, `J = 2` gives exactly `25 = n²`.) Corrected: L12.

---

## 9. Discrepancies

Lean vs [K] Algorithm 1 (Lean used throughout):
1. None in the transition itself. Lines 3–8 = prePhase4 (clear on entering Resetting, timer init on becoming
   Settled at `⌈n/2⌉`, epidemic); lines 9–24 = Phase 4 run on the post-OSSR states; line 20 `max(0, timer − 1)`
   = `∸ 1`; line 22 (partner copies the median's answer) is in Lean.
2. [K] text "any agent with role = Resetting other than the agent with rank ⌈n/2⌉ sets its answer to ϕ" does not
   describe line 22: the Phase-4 partner gets the median's answer, not `phi`. Harmless from `D` (it is `maj`);
   from stale configurations a Phase-4 reset can seed a wrong answer, which is why epoch 1 does not track answers.
3. The swap is ordered (line 10 and `phase4_swap`): only the initiator-B/responder-A order swaps. This is the
   error in [K] L8.
4. Lean's propagate tests the initiator first when both states have rank `m*`; such a pair never reaches Phase 4
   for `n ≥ 3` (two Settled agents of equal rank collide in `δ`; two simultaneous L-wakes give rank 0 `≠ m*`).
5. [K] mixes interactions and parallel time in L7/L9 (erratum A.2, confirmed): `B(n²·trank, ·)` counts ticks over
   `trank n²` interactions while the Markov window is `2 s_rank ≤ 2 trank n` time `= 2 trank n²` interactions.
   Not used here.

On P1 / P2 (taken as given; no error found in the statements I use):
6. P2 Lemma 6.1 / 7.4 cite Lemma 2.9(a), whose hypothesis is the one-leader start; for a general VT start
   the invariance holds by the same argument (R2 I5). I use 7.3 and 7.4 only along the chain from `FD_1`, where
   2.9(a) applies directly.
7. P2's statements give only the end configuration; Lemma 11 needs the "+" forms (no trigger in the window),
   which are exactly the events in P2's proofs (Used fact P2-c). If the reviewers prefer, they should be added
   to P2's statements.
8. P1 Theorem A's statement is one-source and silent about answers and wakes before `T_n`; Lemma 18 derives the
   two-source no-wake form from P1 Lemma 2 and Corollary 5 (this is also the fix R2 proposes for P2's
   Counterexample 2, I3).

---

## 10. Used facts (exact forms)

From P1 (as stated there):
- P1-a (Lemma 1): for `δ` and for `transitionPEM n trank R δ`, the effective resetcount pair after any
  interaction is `(m, m)`, `m = max(ρa ∸ 1, ρb ∸ 1)`, or `(R, R)`.
- P1-b (Lemma 2): if `C₀` has an agent `s` Resetting with rc `≥ R`, then `ρ(C_t(w)) ≥ x_w(t)` for every realization,
  `t`, `w`, where `x` is the pure process from `s`.
- P1-c (Corollary 5): if `u ∈ Rch(t)`, `t ≤ T`, and every realized walk from `s` to `u` over `(0, T]` has cost
  `≤ R − 1`, then `x_u(t′) ≥ 1` for `t ≤ t′ ≤ T`.
- P1-d (Lemma 6 / (3.1), with the numbers of Theorem A's proof): `n ≥ 10`, `R ≥ 60 ln n`, `T = ⌈4n ln n⌉`:
  `P[∃u ∃ realized walk from s to u over (0, T] with cost ≥ R] ≤ 2 n^{−12.2}`.
- P1-e (Lemma 10): `P[T_n ≥ 4 n ln n] < 1/n` for `n ≥ 8`.
- P1-f (Theorem A): from any configuration with an agent Resetting with rc `≥ R`, `X_T` is fully propagating
  with probability `≥ 1 − 1/n − 2n^{−12.2}` (for `transitionPEM`).

From P2 (as stated there, `n ≥ N₀ = 1608`, `R = ⌈60 ln n⌉`, `D = 32n`, `E = 208n`, `c₁ = 4`, `c₂ = 2`):
- P2-a: Lemmas 1.1–1.5, Corollary 1.6 (rows used: 1, 2, 3, 5, 6), Lemmas 2.1–2.7, 2.9(a), Lemma 3.1
  (`P[x_{t₃₃} ≠ 0] ≤ 1/(3n)` from any `x₀ ≤ R`), Lemma 4.1 (= 7.1), Lemma 5.1, Lemma 6.1, Lemma 7.2,
  Proposition 7.6 (all for `rankDeltaOSSR`; transferred to P_EM by Lemmas 8–10 here).
- P2-b: Lemma 7.2: from `FD_L^{½}`, `P[C_{t₂} ∈ FD_1] ≥ 3/4 − n e^{−8κn}`, on the event "nobody has `≥ 16n`
  interactions in `t₂` steps and the leader chain reaches 1".
- P2-c ("+" forms, read off P2's proofs): Lemma 7.3⁺: from `FD_1`, `P[no trigger in (0, W_D] and
  C_{W_D} ∈ RT(80n+1)] ≥ 1 − n e^{−8n} − n e^{−64κn}` (the event `H1 ∩ H2`); Lemma 7.4⁺: from `RT(80n+1)`,
  `P[no trigger in (0, W_R] and C_{W_R} ∈ S] ≥ 1 − π²/40 − n e^{−40κn}` (the event `{T ≤ W_R} ∩ {T_ex > W_R}`,
  with VT invariance up to the first expiry).

Lean (existing): `rankDeltaOSSR_settled_distinct_ranks`; `rankDeltaOSSR_answer_preserved`,
`resetOSSR_answer_preserved`; `consensus_step_apply`, `IsSilentConsensus.isSilent`; `GoodPEM` invariance
(FiniteStatePEM :903 ff.), `pemSimulation`, `encPEM_embPEM`; the restart lemmas of `ExpectedTime.lean`.

Standard: Markov's inequality; binomial mgf; `(1 − y)^L ≤ e^{−yL}`; `Σ 1/j² = π²/6`; independence of
`e_k` from `F_{k−1}` (i.i.d. scheduler, P2 U8).

## 11. Open points

- O1 (Lean, transport). Hitting probabilities of the finite instance equal those of the flat chain from
  `embC C₀` (pathwise: the encoding commutes with every step on `GoodC`); `encC` of a configuration in `S_em` is
  silent in the finite protocol. Needs a Lean lemma over `nthStepDist`.
- O2 (Lean, tools). First-hit decomposition (P2 Lemma 1.3) is used six times; Lemma 4 (selectors with
  `F_{k−1}`-measurable pairs are i.i.d.) and Lemma 6 (scheduler relabelled by an adapted permutation is again
  i.i.d. uniform) need the i.i.d.-pair representation of `nthStepDist` (P1 O2).
- O3 (dependence on proof-internal events). Lemma 11 uses P2-c, Lemma 18 uses P1's events `E₁, E₂` through
  Corollary 5 and (3.1). Both are stated above exactly; the reviewer should confirm they match P2's/P1's proofs.
- O4 (constants). Not optimised. `N₀ = 1608` is inherited from P2's condition `2a ln n ≤ n` (`t₁ ≤ n²/2`);
  for `n < N₀` only finiteness is available. `p₀` is dominated by the two ranking epochs (`q_{B2} q₃₄ ≈ 0.565`
  each).
- O5 (independent check). Not reproduced by a second party; no simulation run for P_EM. The swap-time formula
  (Lemma 12) and the counterexample are exact computations; the rest is proof.
- O6 (scope). The independent review R2 of P1/P2 found no error in the statements used here; if its I-items change
  P2's constants, `q_B`, `q′_B` change accordingly (they are products of P2's stage probabilities).
