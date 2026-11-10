# P2: Burman et al. §3–§4 for the exact Lean OPTIMAL-SILENT-SSR

Paper proofs only.

Labels used below: P1, P2 and P3 are three working proofs written for the time bound of P_EM
(P1: Burman et al. Lemma 3.2 by walk enumeration, superseded by `FIX2-BURMAN.md` §B.1 and not
published; P2: this repository's `FIX2-P2.md`; P3: `FIX2-P3.md`). R1–R3 are independent reviews
of them (not published); their findings are cited by item (for example "R2 I5"). "The packet"
is the question a working proof answers. The status of each node is in `FIX2-BURMAN.md`, and
the formalized statements are in `Ripple/PopulationProtocol/SSEM/UpperBound/`.

Sources: `Ripple/PopulationProtocol/SSEM/Protocol/RankDelta.lean`
(`resetOSSR`, `processAgent`, `propagateReset`, `rankDeltaOSSR`), `Defs/Config.lean` (`step`),
`Probability/RandomScheduler.lean` (`uniformPair`), `Convergence/FiniteStatePEM.lean` (`GoodPEM`),
[B] = arXiv:1907.06068v5 §3–§4.

## Summary of results (n ≥ N₀, constants below)

| id | statement proved here | constants |
|---|---|---|
| B33 = L3.3 | from a fully propagating config: fully dormant at time t₃₃, no wake before, prob ≥ 1 − 1/(3n) − n·2^{−D} | t₃₃ = ⌈(3n/2)(2 ln n + R ln 3)⌉, needs D ≥ 4·exp(1)·t₃₃/n |
| B34 = T3.4 | from any partially triggered config: fully dormant at t₁ with all dt > D/2, awakening config within t₁ + ⌈nD/2⌉, prob ≥ 1 − (c₂+1/3)/n − n·2^{−D/2} | t₁ = K₃₂ + t₃₃ ≤ a·n ln n, needs D ≥ 8·exp(1)·a ln n |
| B35 = C3.5 | from any config: awakening or fully computing config within t₃₃ + nD + t₁ + ⌈nD/2⌉, prob ≥ 1 − (c₂+2/3)/n − n·2^{−D/2} − n·e^{−D/4} | same |
| B41 = L4.1 | from any valid partial tree (in particular one Settled rank 0 + n−1 Unsettled): E[min(T_rank, T_expiry)] ≤ (π²/2)·n(n−1) interactions | C = π²/2 < 4.94 parallel time per agent |
| B42 = L4.2 | printed form false (§8.1); corrected: from a partially triggered config with ≥ 1 leader, the first awakening config has exactly one L in the population with prob ≥ (1 − (c₂+1/3)/n − n2^{−D/2})(1 − 8/d − n·e^{−κdn/4}) | D = dn |
| B43 = T4.3 | uniform window: for every config C in the range domain G, P_C[silent within K] ≥ p₀ | K = 298 n², p₀ = 0.48; E[T] ≤ 621 n² interactions = 621 n parallel time |

Parameters: R = Rmax = ⌈c ln n⌉ with c the constant of B32 (default c = 60), D = Dmax = 32n (d = 32),
E = Emax = 208n (e = 208). κ := ln 4 − 1 > 0.386. Euler's number is written exp(1), because e is the Emax constant.
a := c₁ + (3/2)c·ln 3 + 6 (= c₁ + 104.88 for c = 60).
N₀ := max(N₃₂, 100(c₂ + 1), n_a), with n_a the least n ≥ 3 such that n/ln n ≥ 2a (n/ln n is increasing for n ≥ 3;
for example c₁ = 20 gives n_a = 1991).

B32 is used in the form B32* (§2.3), which is the paper's Lemma 3.2 form ("reach a fully propagating configuration")
stated for the max-process. The form written in P1 ("every agent has been Resetting at some point, assuming no agent
wakes") is not enough; §2.3 says why.

---

## 0. Model and the exact protocol

### 0.1 Scheduler
Agents V = {1,…,n}, n ≥ 2. Steps t = 1, 2, …; at step t the ordered pair ξ_t = (u_t, v_t) is uniform on the n(n−1)
ordered pairs of distinct agents (`uniformPair` on `OffDiagonalPairs`); the ξ_t are i.i.d. (`Config.step` makes
u = v a no-op, but such pairs are never drawn). C_t is the configuration after t steps; C_t is a deterministic function
of C₀ and ξ_1,…,ξ_t. F_t = σ(ξ_1,…,ξ_t). P_X denotes the law with C₀ = X.

Agent v *interacts at step k* iff v ∈ {u_k, v_k}; this has probability 2(n−1)/(n(n−1)) = 2/n, independently over k.
N_v(s,t] := #{k ∈ (s,t] : v interacts at k} ~ Bin(t − s, 2/n). These counts depend only on the scheduler.

### 0.2 The protocol (Lean source)
I checked the packet's pseudocode against `RankDelta.lean`. They agree. The points that matter below:

1. `rankDeltaOSSR` is an if / else-if chain. If one of the two agents is Resetting, only `propagateReset` and the
   dedup line run (Part 1); collision detection, recruitment and error counting (Parts 2–4) run only when neither
   agent is Resetting. [B] Protocol 3 runs lines 1–18 one after the other, so a just-woken agent can collide, recruit
   or count down in the same interaction. This is a model difference; nothing below depends on the paper's version.
2. Dedup: after `propagateReset`, if a.leader = L, b.leader = L and both are still Resetting, then b.leader := F.
3. The triggers (Part 2 collision; Part 4 expiry, which makes *both* agents Resetting) set role := Resetting,
   rc := R, leader := L. They do not touch dt. That does no harm, because dt is read only when rc = 0, and the
   transition rc > 0 → 0 sets dt := D (Lemma 3.1(e)).
4. `processAgent` uses oldRc = rc after Phase 1 (recruitment) and before Phase 2 (sync). The flag "partner
   Resetting" is the partner's role after Phases 1–2, before Phase 3.
5. errorcount uses truncated subtraction. An Unsettled agent with errorcount 0 expires at its first Part-4
   interaction.
6. `resetOSSR`: if the leader bit is L, the agent becomes Settled with rank 0 and children 0. If it is F, the agent
   becomes Unsettled with errorcount E. The leader bit and rc do not change.
7. Recruitment (Phase 1) does not write the leader bit (A.4 (ii)). Ranks are 0-indexed; the children of rank j are
   2j+1 and 2j+2, and the guard is 2j + c + 1 < n (A.4 (iv)).

### 0.3 Terminology
- *computing*: role ≠ Resetting. *propagating*: Resetting with rc ≥ 1. *dormant*: Resetting with rc = 0.
  *triggered*: Resetting with rc = R.
- r(v) := rc(v) if v is Resetting, else 0.
- A *trigger interaction* is one in which Part 2 or Part-4 expiry fires.
- PT: some agent is triggered. PT_L: PT and some agent (any role) has leader L. PT_0 := PT \ PT_L.
- FD (fully dormant): all agents Resetting with rc = 0. ND: no propagating agent. FC (fully computing): no Resetting
  agent.
- S (target): all agents Settled with pairwise distinct ranks, which is then a permutation of {0,…,n−1}. S is closed,
  because every interaction is the identity there (`rankDeltaOSSR_settled_distinct_ranks`), so "S is hit within K"
  is the same event as "C_K ∈ S".
- Awakening time: a time T ≥ 1 with C_{T−1} ∈ FD and C_T not in FD. C_T is then an *awakening configuration*.
- G (range domain): every agent has rc ≤ R, errorcount ≤ E, dt ≤ D, children ≤ 2. This is `GoodPEM` restricted to the
  ranking fields. It is invariant under `rankDeltaOSSR` (FiniteStatePEM.lean:903). All configurations below are in G.

Without G the target bounds are false. Example: all agents Unsettled with errorcount M ≫ n². No Settled agent exists,
so the first trigger needs some agent to make M interactions, which takes at least M·n/2 steps. Hence the window form
is stated on G, as in A.1.

### 0.4 Parameters and derived windows
- K₃₂ := ⌈c₁ n ln n⌉ (from B32*).
- t₃₃ := ⌈(3n/2)(2 ln n + R ln 3)⌉.
- t₁ := K₃₂ + t₃₃.
- t₂ := 4n(n−1).
- W_D := 32n², W_E := 208n², W_4 := n², W_R := 20n².

**Fact 0.1.** For n ≥ 3, t₁ ≤ a·n ln n.

Proof. K₃₂ ≤ c₁ n ln n + 1. Since R ≤ c ln n + 1, t₃₃ ≤ (3/2)n(2 ln n + (c ln n + 1) ln 3) + 1
= (3 + (3/2)c ln 3) n ln n + (3/2)(ln 3)n + 1. For n ≥ 3 we have ln n ≥ 1.0986, so (3/2)(ln 3)n ≤ 1.65 n ≤ 1.51 n ln n,
and 2 ≤ 0.61 n ln n. The sum is at most (c₁ + (3/2)c ln 3 + 5.12) n ln n. ∎

For n ≥ N₀ we have 2a ln n ≤ n, so t₁ ≤ n²/2 (condition N3), and exp(1)·a ln n ≤ 4n (condition N2, implied by N3).

---

## 1. Probabilistic tools

**Lemma 1.1 (Markov property at deterministic times).** For deterministic s and any event B on paths,
P_X[(C_{s+t})_{t≥0} ∈ B | F_s] = P_{C_s}[(C_t)_{t≥0} ∈ B].

Proof. C_{s+t} = Ψ_t(C_s; ξ_{s+1},…,ξ_{s+t}), and (ξ_{s+k})_{k≥1} is i.i.d., independent of F_s, with the same law as
(ξ_k)_{k≥1}. ∎

**Lemma 1.2 (chaining at deterministic times).**
(i) Suppose P_X[C_{T₁} ∈ A₁] ≥ q₁ and inf_{Y∈A₁} P_Y[C_{T₂} ∈ A₂] ≥ q₂. Then P_X[C_{T₁+T₂} ∈ A₂] ≥ q₁q₂.
(ii) Let τ_H be the hitting time of a set H. Suppose P_X[τ_H > T₁, C_{T₁} ∉ A] ≤ ε₁ and sup_{Y∈A} P_Y[τ_H > T₂] ≤ ε₂.
Then P_X[τ_H > T₁+T₂] ≤ ε₁ + ε₂.

Proof. (i) Use E[1{C_{T₁}∈A₁} P_{C_{T₁}}[C_{T₂}∈A₂]] and Lemma 1.1.
(ii) The event {τ_H > T₁+T₂} is contained in {τ_H > T₁, C_{T₁} ∉ A} ∪ {C_{T₁} ∈ A, C_{T₁+k} ∉ H for all k ≤ T₂}.
The second event has probability ≤ ε₂ by Lemma 1.1. ∎

**Lemma 1.3 (composition at a hitting time).** Let H and H′ be sets of configurations. Suppose that from every
Y ∈ H, P_Y[τ_{H′} ≤ T_B] ≥ q_B. Then for every X, P_X[τ_{H′} ≤ T_A + T_B] ≥ q_B · P_X[τ_H ≤ T_A].

Proof. The events {τ_H = s}, s = 0,…,T_A, are disjoint and {τ_H = s} ∈ F_s. On {τ_H = s} we have C_s ∈ H, and a hit
of H′ in [s, s+T_B] is a hit by T_A + T_B. So
P_X[τ_{H′} ≤ T_A+T_B] ≥ Σ_{s≤T_A} E[1{τ_H=s} P_{C_s}[τ_{H′} ≤ T_B]] ≥ q_B Σ_s P[τ_H = s]
by Lemma 1.1. ∎
This is the strong Markov property in the only form needed: a finite sum over the values of the hitting time.

**Lemma 1.4 (geometric domination for monotone indices).** Let Z_t be adapted, with values in a finite totally
ordered set, and nonincreasing in t. Fix z. Suppose P[Z_{t+1} ≠ z | F_t] ≥ p > 0 on {Z_t = z} for all t. Then
E[#{t ≥ 0 : Z_t = z}] ≤ 1/p.

Proof. Let a_t := P[Z_t = z] and b_{t+1} := P[Z_t > z, Z_{t+1} = z], b₀ := a₀. Since {Z_{t+1} = z} ⊆
{Z_t = z, Z_{t+1} = z} ∪ {Z_t > z, Z_{t+1} = z}, we get a_{t+1} ≤ (1−p)a_t + b_{t+1}. By monotonicity the "entering"
events are pairwise disjoint, so Σ_t b_t ≤ 1. Summing from 0 to T:
Σ_{t≤T} a_t ≤ (1−p)Σ_{t≤T} a_t + 1. Hence p Σ_{t≤T} a_t ≤ 1; let T → ∞. ∎

**Lemma 1.5 (binomial tails).** Let X ~ Bin(N, p) and μ = Np ≤ μ⁺.
(a) P[X ≥ 2μ⁺] ≤ (exp(1)/4)^{μ⁺} = exp(−κμ⁺).
(b) For k ≥ μ: P[X ≥ k] ≤ (exp(1)μ/k)^k. In particular, if k ≥ 2·exp(1)·μ then P[X ≥ k] ≤ 2^{−k}.
(c) P[X ≤ μ/2] ≤ exp(−μ/8).
(d) For λ ≥ 0, E[e^{λX}] ≤ exp(μ⁺(e^λ − 1)).

Proof. (d): E e^{λX} = (1 + p(e^λ−1))^N ≤ exp(μ(e^λ−1)) ≤ exp(μ⁺(e^λ−1)).
(a): Markov's inequality with λ = ln 2 gives P[X ≥ 2μ⁺] ≤ exp(μ⁺ − 2μ⁺ ln 2).
(b): take μ⁺ = μ and λ = ln(k/μ) ≥ 0; this gives exp(k − μ)(μ/k)^k ≤ (exp(1)μ/k)^k.
(c) is the standard lower Chernoff bound exp(−δ²μ/2) with δ = 1/2 (Used facts U2). ∎

**Corollary 1.6 (interaction counts used below).** For n ≥ 100, union over n agents, all within a window of
deterministic length:

| window | event | failure probability ≤ |
|---|---|---|
| t₁ steps | some agent has ≥ ⌈D/2⌉ = 16n interactions | n·2^{−16n} (by (b): μ ≤ 2a ln n and 2·exp(1)·2a ln n ≤ 16n by N2) |
| t₂ = 4n(n−1) steps | some agent has ≥ 16n interactions | n·exp(−8κn) (by (a): μ ≤ 8n = μ⁺) |
| W_D = 32n² steps | some agent has < 32n = D interactions | n·exp(−8n) (by (c): μ = 64n) |
| W_D steps | some agent has ≥ 128n interactions | n·exp(−64κn) (by (a): μ⁺ = 64n) |
| W_E = 208n² steps | some agent has < 208n = E interactions | n·exp(−52n) (by (c): μ = 416n) |
| W_R = 20n² steps | some agent has ≥ 80n interactions | n·exp(−40κn) (by (a): μ⁺ = 40n) |
| t₃₃ steps | some agent has ≥ D interactions | n·2^{−D} if D ≥ 4·exp(1)·t₃₃/n (by (b)) |

For n ≥ 100 the sum of all the n·exp(−Θ(n)) entries is below 10⁻⁹.

---

## 2. Structural lemmas for the Lean protocol

**Lemma 2.1 (the r-process).** Consider one interaction of u and v, and let m := max(r(u)−1, r(v)−1, 0), computed
before the interaction.
(a) If the interaction is not a trigger interaction, then afterwards r(u) = r(v) = m.
(b) A trigger interaction has both agents computing before it. Afterwards r(u) = r(v) = R and both have leader L.
(c) r of every other agent is unchanged. Wakes never change r.

Proof. If neither agent is Resetting, r = 0 for both. A trigger gives (R, R); any other Part 2–4 interaction leaves
both computing, so r = (0, 0) = (m, m).
If at least one is Resetting, Part 1 runs; dedup does not touch role or rc. Four cases:
- (propagating u, computing v): Phase 1 recruits v (rc := 0); Phase 2 sets both to max(r(u)−1, 0−1) = r(u)−1 = m.
  Phase 3 may wake an agent whose rc is now 0, which leaves r = 0.
- (computing u, propagating v): symmetric, by the else-branch of Phase 1.
- (dormant, computing): no recruitment, since the dormant agent has rc = 0. No sync. The dormant agent wakes because
  its partner is not Resetting. r = (0, 0) = (m, m).
- (both Resetting): Phase 2 sets both to max(r(u)−1, r(v)−1) with truncated subtraction, i.e. to m. Wakes keep r = 0.
(c) holds because only the two participants change, and a woken agent had rc = 0 and is computing afterwards. ∎

Let x_t be the *max-process*: x₀ = r(C₀), and x_{t} = F_{ξ_t}(x_{t−1}), where F_{(u,v)} sets coordinates u and v to
max(x_u−1, x_v−1, 0). F is monotone in each coordinate.

**Corollary 2.2 (coupling).** (a) r(C_t) ≥ x_t for all t, coordinatewise. (b) If there is no trigger interaction in
(s, t], then r(C_k) is the max-process started at time s from r(C_s), for k ∈ [s, t].
(c) If X ∉ PT, C_t ∈ PT and t ≥ 1, then some interaction in [1, t] is a trigger. The reason: a non-trigger interaction
gives r ≤ R − 1 to both participants.

Proof. Induction with Lemma 2.1 and monotonicity of F (R ≥ every value). ∎

**Lemma 2.3 (leader bits).** A leader bit changes only (i) by dedup, which turns the responder from L to F while the
initiator stays L, or (ii) by a trigger, which sets both participants to L. Hence: if some agent is L, then some
agent is L at every later time. Without trigger interactions, the set of L agents is nonincreasing.

Proof. Inspection: recruitment, `processAgent`, `resetOSSR` and Part 3 do not write `leader`. Part 2 and Part 4
write L. Dedup writes F only to b, and only when a.leader = L. ∎

**Lemma 2.4 (Resetting dynamics).**
(a) A propagating agent does not change role in an interaction.
(b) A computing agent becomes Resetting only if it is recruited (its partner is propagating) or by a trigger.
(c) A dormant agent whose partner is computing wakes in that interaction.
(d) A dormant agent with a Resetting partner, whose rc is still 0 after Phase 2, gets dt := dt − 1 (truncated), and
it wakes iff the new dt is 0.
(e) "Fresh dormancy": if r(v) goes from ≥ 1 to 0 in an interaction, then afterwards v is Resetting with dt = D.
(f) Waking applies `resetOSSR` (§0.2 item 6).

Proof. (a): `processAgent` acts only when rc = 0 after Phase 2.
(c), (d): `processAgent` with oldRc = 0.
(e): v had rc ≥ 1 after Phase 1 (Phase 1 does not change a propagating agent's rc), so oldRc > 0 and dt := D. The
partner is Resetting after Phase 1: either it was Resetting already, or v recruited it. Since D ≥ 1, v does not
wake. ∎

**Corollary 2.5 (waking without propagation).** Suppose C_s ∈ ND and there is no trigger interaction in (s, t]. Then:
- r ≡ 0 on [s, t];
- no agent becomes Resetting in (s, t];
- every agent dormant at time s with N_v(s, t] ≥ D is computing at time t.

Proof. By Corollary 2.2(b), r stays 0. By Lemma 2.4(b), nobody becomes Resetting. A dormant agent with dt = y ≤ D (G)
loses 1 from dt at each interaction with a Resetting partner (Lemma 2.4(d)) and wakes at once with a computing partner
(Lemma 2.4(c)). So it wakes by its max(y, 1)-th interaction, and max(y, 1) ≤ D. ∎

**Lemma 2.6 (no wake after full propagation).** Suppose C_s is fully propagating. Let T_w be the first wake after s.
Then on [s, T_w) every agent is Resetting, no trigger occurs, every L–L interaction performs dedup, and some agent has
at least D interactions in (s, T_w]. So if N_v(s, t] < D for all v, then T_w > t. More precisely: an agent dormant at
time k ∈ [s, T_w) has dt ≥ D − N_v(s, k].

Proof. Until the first wake nobody is computing, by Lemma 2.4(a) and because a Resetting agent leaves the role only
by waking. Without computing agents there are no triggers (Lemma 2.1(b)), and dedup's guard "both still Resetting"
holds. Every agent was propagating at s, so it became dormant after s with dt = D (Lemma 2.4(e)). After that, dt
loses at most 1 per interaction; it is reset to D on a re-dormancy. No computing partner exists, so by Lemma 2.4(d)
the agent wakes only when dt reaches 0, which needs ≥ D interactions after s. ∎

**Lemma 2.7 (computing configurations).** Consider an interaction of two computing agents that is not a trigger.
Settled agents stay Settled; their rank is unchanged and their children may grow by 1. An Unsettled participant is
either recruited (it becomes Settled) or its errorcount drops by 1 (truncated); if the new value is 0, a trigger
fires. Two Settled agents with distinct ranks give the identity; equal ranks give a trigger.
Consequently: an Unsettled agent with errorcount y ≤ E, all of whose partners are computing, is Settled or has caused
a trigger by its max(y, 1)-th interaction.

Proof. Inspection of Parts 2–4. For a pair (u, s) with u Unsettled and s Settled, the else-branch "b recruits a"
applies, so recruitment happens in either order. If s cannot recruit, Part 4 decrements u. ∎

**Definition 2.8 (valid tree, VT).** Let A be the set of ranks held by Settled agents. C is VT⁻ if:
- the Settled agents have pairwise distinct ranks;
- A = ∅, or A contains 0 and is closed under parent j ↦ ⌊(j−1)/2⌋;
- each Settled agent of rank j has children = #{k ∈ {0,1} : 2j+k+1 ∈ A}, and 2j+2 ∈ A implies 2j+1 ∈ A;
- no agent is propagating, and no agent is Settled outside this structure (every non-Settled agent is Unsettled or
  dormant).
C is VT if it is VT⁻, A ∋ 0, and every agent is computing.

**Lemma 2.9 (tree invariance).**
(a) Starting from a VT⁻ configuration in which exactly one agent λ is L, with A = ∅ and λ dormant, or with A ∋ 0 and λ
Settled of rank 0, every interaction up to the first expiry gives a VT⁻ configuration, and no collision can occur.
(b) In a VT configuration with an Unsettled agent, some Settled agent can recruit, and every recruitment adds a new
rank. A VT configuration with no Unsettled agent is in S.

Proof. (a) Without triggers r stays 0 (Corollary 2.2(b)), so nobody becomes Resetting. Followers wake Unsettled.
λ wakes as Settled with rank 0 and children 0; then A = {0}, consistent, since before that no Settled agent exists:
Settled agents arise only from an L-wake or from a recruitment by a Settled agent.
Recruitment by an agent of rank j with children c < 2 and 2j+c+1 < n assigns rank 2j+c+1. By consistency, if c = 0
neither child is in A, and if c = 1 exactly 2j+1 is. So the new rank is not in A, and the conditions are preserved
(the new agent has children 0 and no children in A, since A was parent-closed).
Distinct ranks exclude collisions; Part 4 without expiry changes no Settled agent.
(b) Let j be the least rank not in A. Then j ≥ 1, its parent p is in A, and p's consistent children count c ≤ (j − 2p
− 1). So c < 2 and 2p + c + 1 ≤ j < n: p can recruit. With no Unsettled agents, all n agents are Settled with
distinct ranks. ∎

---

## 2.3 The form of B32 used (B32*)

**(B32*)** There are constants c, c₁, c₂, N₃₂ such that for n ≥ N₃₂, R = ⌈c ln n⌉, and every x₀ ∈ {0,…,R}^V with
max x₀ = R, the max-process satisfies P[∃ t ≤ K₃₂ : x_t(v) ≥ 1 for all v] ≥ 1 − c₂/n.

By monotonicity of F it suffices to prove this for x₀ = R·1_{u}. The fixed-time form
P[x_{K₃₂}(v) ≥ 1 for all v] ≥ 1 − c₂/n implies it. This is [B] Lemma 3.2 ("fully propagating within 4 ln n time") for
Observation 3.1's propagating variable, i.e. [59] Cor. 8. The P1 proof (infection tree, decay of the value by at
most 1 per interaction of the holder, union bound over paths) proves a statement about the max-process. It should
deliver this form.

Why the form written in P1/P2 does not suffice:
1. The hypothesis "no agent wakes during the window" cannot be secured.
   - Adversarial starts contain dormant agents with dt = 0. Example: a triggered agent, n/2 dormant agents with
     dt = 0 and the rest Settled. Each dormant agent wakes at its first interaction, so the hypothesis fails with
     probability → 1.
   - A freshly dormant agent wakes on meeting a computing agent that has not been recruited yet (Lemma 2.4(c)), and
     that computing agent is not recruited by it. This is exactly the failure of propagation, so assuming it away is
     circular.
2. The conclusion "every agent has been Resetting at some point" is not simultaneous. An agent recruited by a partner
   with rc = 1 is dormant at once (dt = D − 1) and can be woken by a computing agent before the others are recruited.
3. In the max-process formulation neither issue arises. By Lemma 2.1 wakes do not change r. Later triggers only raise
   r (Corollary 2.2(a)), so the "no later trigger" hypothesis is not needed either.
B32* gives: on its event, the real configuration is fully propagating at some time T_fp ≤ K₃₂ (Corollary 2.2(a)),
regardless of wakes and triggers.

---

## 3. B33: Lemma 3.3

Let Φ(x) := Σ_v φ(x_v), with φ(0) = 0 and φ(y) = 3^y for y ≥ 1.

**Lemma 3.1 (potential drift of the max-process).** For every t:
- Φ(x_{t+1}) ≤ Φ(x_t) pathwise;
- E[Φ(x_{t+1}) | F_t] ≤ (1 − 2/(3n)) Φ(x_t).
Hence from any x₀ ∈ {0,…,R}^V, P[x_{t₃₃} ≠ 0] ≤ 1/(3n).

Proof. Suppose the interacting pair holds values y, z, and let M := max(y, z). If M ≤ 1 both values become 0. If
M ≥ 2 both become M − 1, and 2·3^{M−1} = (2/3)3^M ≤ (2/3)(φ(y) + φ(z)). In all cases
φ(new_u) + φ(new_v) ≤ (2/3)(φ(y) + φ(z)), and other agents are unchanged. Each agent lies in 2(n−1) of the n(n−1)
ordered pairs, so
E[Φ_{t+1} − Φ_t | F_t] ≤ −(1/3)·Σ_{(u,v)} (φ(x_u) + φ(x_v))/(n(n−1)) = −(1/3)·2(n−1)Φ_t/(n(n−1)) = −(2/(3n))Φ_t.
By iteration, E[Φ_t] ≤ (1 − 2/(3n))^t Φ₀ ≤ exp(−2t/(3n))·n·3^R ≤ 1/n at t = t₃₃. Since Φ is 0 or ≥ 3, Markov's
inequality gives P[Φ_{t₃₃} ≥ 3] ≤ 1/(3n). ∎

**Lemma 3.2 (B33, [B] Lemma 3.3 for the Lean protocol).** Let n ≥ 2, R ≥ 1, and D ≥ 4·exp(1)·t₃₃/n; for example
D ≥ 6·exp(1)(2 ln n + R ln 3) + 11 suffices, which is Ω(log n + R). From every fully propagating X ∈ G:
P_X[no wake in [1, t₃₃] and C_{t₃₃} ∈ FD] ≥ 1 − 1/(3n) − n·2^{−D},
with t₃₃ = ⌈(3n/2)(2 ln n + R ln 3)⌉ = O(n(log n + R)) interactions.

Proof. By Corollary 1.6 (last row), with probability ≥ 1 − n2^{−D} every agent has < D interactions in (0, t₃₃]. Then
Lemma 2.6 gives no wake and no trigger in [1, t₃₃], and all agents stay Resetting. By Corollary 2.2(b), r is the
max-process. Lemma 3.1 gives r(C_{t₃₃}) = 0 except with probability 1/(3n), and then C_{t₃₃} ∈ FD. ∎

The printed proof is correct for this protocol, with the pair probability 2/(n(n−1)) in place of 1/C(n,2), which is
the same quantity. Starting "fully Resetting" (dormant agents allowed) instead of fully propagating is not enough for
the "no wake" part, because stale dormant agents can wake. The Φ part (Lemma 3.1) holds from any start.

---

## 4. B34: Theorem 3.4

**Lemma 4.1 (stage B1).** Let n ≥ max(3, N₃₂) and D ≥ 8·exp(1)·a ln n. From every X ∈ PT ∩ G, with probability
≥ 1 − (c₂ + 1/3)/n − n·2^{−D/2} the following hold:
(i) C_{t₁} ∈ FD;
(ii) every agent has dt ≥ ⌊D/2⌋ + 1 at time t₁;
(iii) no wake occurs in (T_fp, t₁] for some T_fp ≤ K₃₂ at which C_{T_fp} is fully propagating;
(iv) #L(C_{t₁}) ≥ 1 if X ∈ PT_L. If X ∈ PT_0 and there is no trigger in [1, t₁], then #L(C_{t₁}) = 0.

Proof. Three events:
- G1: the max-process from r(X) is fully positive at some T_fp ≤ K₃₂ (B32*; probability ≥ 1 − c₂/n).
- G2: every agent has < ⌈D/2⌉ interactions in (0, t₁]. By Lemma 1.5(b), μ = 2t₁/n ≤ 2a ln n (Fact 0.1) and
  2·exp(1)μ ≤ D/2, so this holds with probability ≥ 1 − n·2^{−D/2}.
- G3: the max-process started at time K₃₂ from r(C_{K₃₂}) is 0 at time t₁. By Lemmas 1.1 and 3.1 (r ≤ R by G), it
  fails with probability ≤ 1/(3n).

On G1, C_{T_fp} is fully propagating (Corollary 2.2(a)). On G2, Lemma 2.6 applied from T_fp gives no wake and no
trigger in (T_fp, t₁]. So r on [K₃₂, t₁] equals the max-process started at K₃₂ (Corollary 2.2(b)), and G3 gives
r(C_{t₁}) = 0. All agents are Resetting, so C_{t₁} ∈ FD; this is (i), (iii).
(ii) Lemma 2.6: dt ≥ D − N_v(T_fp, t₁] ≥ D − (⌈D/2⌉ − 1) = ⌊D/2⌋ + 1.
(iv) Lemma 2.3. ∎

**Theorem 4.2 (B34, [B] Theorem 3.4).** Under the hypotheses of Lemma 4.1, from every X ∈ PT ∩ G, with probability
≥ 1 − (c₂ + 1/3)/n − n·2^{−D/2}, there is an awakening time T_w with t₁ < T_w ≤ t₁ + ⌈nD/2⌉. That is
O(n log n + nD) interactions, O(log n + D) parallel time; O(D) since D = Ω(log n).

Proof. On the event of Lemma 4.1, C_{t₁} ∈ FD. From a fully dormant configuration, Corollary 2.5 applies until the
first wake: no propagating agent and no computing agent, hence no trigger. In ⌈nD/2⌉ steps there are ≥ nD agent
participations, so some agent has ≥ D interactions; by Corollary 2.5 it has woken. At the first wake T_w the previous
configuration is fully dormant. ∎

---

## 5. B35: Corollary 3.5

**Lemma 5.1 (stage A1).** From every X ∈ G \ PT: P_X[σ > t₃₃ and C_{t₃₃} ∉ ND] ≤ 1/(3n), where σ := τ_PT.

Proof. On {σ > t₃₃} there is no trigger in [1, t₃₃] (a trigger creates PT). By Corollary 2.2(b), r is the
max-process from r(X). Lemma 3.1 applies. ∎

**Corollary 5.2 (B35, [B] Corollary 3.5).** Under the hypotheses of Lemma 4.1, let T₃₅ := t₃₃ + nD + t₁ + ⌈nD/2⌉.
From every X ∈ G, with probability ≥ 1 − (c₂ + 2/3)/n − n·2^{−D/2} − n·e^{−D/4}, the process has an awakening time
or visits FC within T₃₅ steps.

Proof. Let T₀ := t₃₃ + nD.

Branch σ ≤ T₀: apply Lemma 1.3 with H = PT, H′ = "awakening time has occurred" (formally, lift the chain by a flag
recording C_{t−1} ∈ FD), and Theorem 4.2. The probability of no awakening by T₀ + t₁ + ⌈nD/2⌉ on {σ ≤ T₀} is at most
ε_{4.2} = (c₂ + 1/3)/n + n2^{−D/2}.

Branch σ > T₀: by Lemma 5.1, except with probability 1/(3n), C_{t₃₃} ∈ ND. By Corollary 2.5 on (t₃₃, T₀] (no trigger,
because σ > T₀), every agent with ≥ D interactions there is computing at T₀, and nobody re-entered Resetting. N_v ~
Bin(nD, 2/n) with μ = 2D, so Lemma 1.5(c) gives all agents ≥ D interactions except with probability n·e^{−D/4}. Then
C_{T₀} ∈ FC. ∎

Remark. The printed proof finishes the second branch with a superepidemic of computing agents. The dt-countdown
argument above avoids it and stays O(nD) interactions. A fully dormant C_{t₃₃} with no trigger gives an awakening
time and then FC; both are allowed outcomes.

---

## 6. B41: Lemma 4.1 (tree ranking)

Heap on {0,…,n−1}; level ℓ(j) = ⌊log₂(j+1)⌋; h := ⌊log₂ n⌋. Levels 0,…,h−1 are complete, because 2^h − 2 ≤ n − 1.

**Lemma 6.1 (B41).** Start from a VT configuration; in particular, one Settled agent of rank 0 with children 0 and
n − 1 Unsettled agents. Let T_rk := first time in S, T_ex := first expiry, T := min(T_rk, T_ex). Then
E[T] ≤ (π²/6)·(1 + Σ_{k≥1} 1/(2^k − 1))·n(n−1) ≤ (π²/2)·n(n−1).
In particular, in the process with errorcounts ignored (T_ex = ∞), the expected completion time is ≤ (π²/2)(n−1)
parallel time; C = π²/2 < 4.94. (The sharper constant is (π²/6)(2.607) < 4.29.)

Proof. Up to T, the configuration is VT (Lemma 2.9). Define the index Z_t := (d, i), where d is the least level with an
unassigned node (d ≥ 1, since 0 ∈ A) and i ≥ 1 is the number of unassigned nodes at level d; set Z_t := ⊥ for t ≥ T.
Order (d, i) by d increasing, then i decreasing, with ⊥ last. Since A only grows before T, Z is monotone, and
T = #{t : Z_t ≠ ⊥}.

Exit probability from (d, i):
- *Recruiters.* Each unassigned level-d node j = 2p + k + 1 has an assigned parent p (level d−1 is complete). Its
  consistent count satisfies c ≤ k, so c < 2 and 2p + c + 1 ≤ j < n, and p's recruitment assigns the level-d node
  2p + c + 1. The i nodes have ≥ ⌈i/2⌉ distinct such parents.
- *Unsettled agents.* All agents are computing, and Settled agents are in bijection with A, so #Unsettled =
  #unassigned ranks. A is parent-closed, so the subtree of each unassigned level-d node is unassigned. For d ≤ h−1 that
  subtree contains the 2^{h−d} − 1 nodes on levels d,…,h−1 (all < n). Subtrees are disjoint. So
  U ≥ i(2^{h−d} − 1) for d < h, and U ≥ i for d = h.
- *Pairs.* Any pair {p, u} with p a recruiter and u Unsettled assigns a level-d node, in either order (Lemma 2.7).
  There are 2·⌈i/2⌉·U ≥ iU such ordered pairs.

So P[Z_{t+1} ≠ (d,i) | F_t] ≥ i·U/(n(n−1)). Lemma 1.4 gives
E[T] ≤ Σ_{d=1}^{h−1} Σ_{i≥1} n(n−1)/(i²(2^{h−d} − 1)) + Σ_{i≥1} n(n−1)/i²
≤ (π²/6) n(n−1)(Σ_{k≥1} 1/(2^k − 1) + 1) ≤ (π²/6)·3·n(n−1),
using 1/(2^k − 1) ≤ 2^{1−k}. ∎

Discrepancy with the printed proof (statement holds):
- The printed proof uses "Unsettled ≥ i·n·2^{−d}". That is an approximation, off by up to a factor 2 at the last
  level.
- It also uses a "stochastically dominating process in which no agent is assigned at level > d until level d is
  complete", which is not proved there.
The (d, i) index with Lemma 1.4 needs neither: deeper assignments do not touch the unassigned subtrees counted in U.

---

## 7. Stage lemmas for the epoch (B42, B43*)

Fix d = 32, β = 4, γ = 20, e = 208 (D = 32n, E = 208n) and n ≥ N₀. All classes are intersected with G.

Classes:
- FD_L^{½}: FD, #L ≥ 1, all dt ≥ ⌊D/2⌋ + 1.
- FD_1: FD with exactly one L.
- FD_0: FD with no L.
- RT(m): VT with every Unsettled errorcount ≥ m.

**Lemma 7.1 (stage B1).** From X ∈ PT_L: P[C_{t₁} ∈ FD_L^{½}] ≥ q_{B1} := 1 − (c₂ + 1/3)/n − n·2^{−16n}.

Proof. Lemma 4.1, with D = 32n ≥ 8·exp(1)·a ln n (N2). ∎

**Lemma 7.2 (stage B2: leader election before the first wake).** From X ∈ FD_L^{½}:
P[C_{t₂} ∈ FD_1] ≥ q_{B2} := 1 − 1/β − n·exp(−8κn) = 3/4 − n·exp(−8κn).

Proof. Leader chain: L₀ := L-set of X; L_{k} := L_{k−1} \ {v_k} if u_k, v_k ∈ L_{k−1}, else L_{k−1}. This depends only on
the scheduler. Z_k := |L_k| is nonincreasing, and from i ≥ 2 it decreases with probability i(i−1)/(n(n−1)). By
Lemma 1.4, the time T_LE to reach 1 satisfies
E[T_LE] ≤ Σ_{i=2}^{|L₀|} n(n−1)/(i(i−1)) = n(n−1)(1 − 1/|L₀|) < n(n−1).
So P[T_LE > βn(n−1)] < 1/β (Markov).

X is fully dormant: no propagating and no computing agent, so no trigger until the first wake, and r ≡ 0
(Corollary 2.2(b)). A dormant agent wakes only when dt reaches 0 (Lemma 2.4(d)). That needs ≥ ⌊D/2⌋ + 1 > 16n
interactions. By Corollary 1.6 (row 2), with probability ≥ 1 − n·exp(−8κn) nobody has ≥ 16n interactions in t₂
steps, so nobody wakes in [1, t₂]. On that event, every L–L interaction performs dedup (both stay Resetting), and the
real L-set equals L_k for k ≤ t₂. With T_LE ≤ t₂, C_{t₂} is fully dormant with exactly one L. Any dt ≤ D is allowed
in FD_1. ∎

**Lemma 7.3 (stage B3: everybody wakes, the tree starts).** From X ∈ FD_1: P[C_{W_D} ∈ RT(80n + 1)] ≥ q_{B3} :=
1 − n·exp(−8n) − n·exp(−64κn).

Proof. Events (Corollary 1.6):
- H1: every agent has ≥ 32n = D interactions in (0, W_D];
- H2: every agent has < 128n interactions there.

On H2 no expiry happens. An errorcount is set to E = 208n at wake and decreases only at the agent's own interactions,
and 128n − 1 < E. Lemma 2.9(a) applies from X (A = ∅, λ dormant), so there is no collision, hence no trigger, hence
no Resetting re-entry. On H1, Corollary 2.5 makes every agent computing at W_D. So C_{W_D} is VT, and every Unsettled
errorcount is ≥ 208n − (128n − 1) = 80n + 1. ∎

**Lemma 7.4 (stage B4: ranking finishes before any errorcount expires).** From X ∈ RT(80n + 1):
P[C_{W_R} ∈ S] ≥ q_{B4} := 1 − π²/(2γ) − n·exp(−40κn) = 1 − π²/40 − n·exp(−40κn).

Proof. Lemma 6.1 and Markov's inequality: P[T > 20n²] ≤ (π²/2)n(n−1)/(20n²) < π²/40.
An expiry before W_R requires some agent to have ≥ 80n + 1 interactions in W_R steps; by Corollary 1.6 this has
probability ≤ n·exp(−40κn).
On {T ≤ W_R} ∩ {T_ex > W_R} we have T = T_rk ≤ W_R. S is closed. ∎

**Proposition 7.5 (Phase B).** From every X ∈ PT_L, with K_B := t₁ + t₂ + W_D + W_R ≤ t₁ + 56n²:
P_X[C_{K_B} ∈ S] ≥ q_B := q_{B1}·q_{B2}·q_{B3}·q_{B4} ≥ 0.559 for n ≥ N₀.

Proof. Lemma 1.2(i), three times. Numerics for n ≥ N₀ ≥ 100(c₂+1):
- q_{B1} ≥ 0.99 − 10⁻⁹;
- q_{B2} ≥ 0.75 − 10⁻⁹;
- q_{B3} ≥ 1 − 10⁻⁹;
- q_{B4} ≥ 1 − 0.24675 − 10⁻⁹.
The product is ≥ 0.559. ∎

**Proposition 7.6 (Phase A: reach a trigger with a leader, or the target).** Let H := S ∪ PT_L and
K_A := t₁ + 241n². For every X ∈ G: P_X[τ_H ≤ K_A] ≥ q_A := 0.861 for n ≥ N₀.

Proof. If X ∈ H, then τ_H = 0. Every trigger interaction produces a configuration in PT_L (Lemma 2.1(b)), so "no
trigger in [1, t]" holds on {τ_H > t}. Two cases.

*Case X ∉ PT* (stages A1–A4, chained with Lemma 1.2(ii)).
- A1 (t₃₃ steps): Lemma 5.1 gives P[τ_H > t₃₃, C_{t₃₃} ∉ ND] ≤ 1/(3n).
- A2 (W_D steps), from Y ∈ ND: on {τ_H > W_D} there are no triggers, and by Corollary 2.5 plus "all agents
  ≥ D interactions" the configuration is FC at W_D. Failure ≤ n·e^{−8n}.
- A3 (W_E steps), from Y ∈ FC: on {τ_H > W_E} there are no triggers, so nobody becomes Resetting and no new Unsettled
  agent appears (Unsettled agents arise only from wakes). By Lemma 2.7, every Unsettled agent with ≥ E interactions
  is Settled. So, except with probability n·e^{−52n} (Corollary 1.6), C_{W_E} has all agents Settled.
- A4 (W_4 = n² steps), from Y all Settled: either Y ∈ S, or two agents share a rank. In the latter case Y is frozen
  until an equal-rank pair (≥ 2 ordered pairs) is drawn, which triggers. So
  P[τ_H > n²] ≤ (1 − 2/(n(n−1)))^{n²} ≤ exp(−2n/(n−1)) ≤ e^{−2}.
Total window t₃₃ + 32n² + 208n² + n² ≤ K_A. Failure ≤ 1/(3n) + e^{−2} + 2·10⁻⁹ ≤ 0.1387 for n ≥ 100.

*Case X ∈ PT_0* (zero-leader epoch, errata A.2).
- Stage 1 (t₁ steps): by Lemma 4.1, except with probability (c₂+1/3)/n + n2^{−16n}, on {τ_H > t₁} we have
  C_{t₁} ∈ FD_0. Without triggers no L is created (Lemma 2.3).
- Stage 2 (W_D steps), from Y ∈ FD_0: on {τ_H > W_D} and "all ≥ D interactions" (failure ≤ n·e^{−8n}),
  Corollary 2.5 makes everyone computing. All bits are F, so everyone woke Unsettled, and no Settled agent can arise
  (Lemma 2.9's argument with no L).
- Stage 3 (⌈nE/2⌉ = 104n² steps), from all-Unsettled: there are 208n² = nE participations, so some agent has ≥ E
  interactions. All its partners are Unsettled (as long as τ_H has not occurred), so each interaction decrements its
  errorcount (≤ E), and it expires by its E-th interaction. That is a trigger, so τ_H ≤ 104n² deterministically.
Total window t₁ + 136n² ≤ K_A. Failure ≤ (c₂ + 1/3)/n + 2·10⁻⁹ ≤ 0.0101.

So q_A ≥ 1 − 0.1387 ≥ 0.861. ∎

---

## 8. B42: Lemma 4.2

### 8.1 The printed statement is false
"An awakening configuration has a single leader with constant probability."

Counterexample 1 (any n ≥ 3). X: all agents Resetting, rc = 0, leader L, dt = 1; X ∈ G and X ∈ FD. At step 1 both
participants get dt := 0 and wake (Lemma 2.4(d)) as Settled rank 0. Dedup does not apply, since neither is still
Resetting. C₁ is awakening with n agents L and two Settled rank-0 agents. This happens with probability 1.

Counterexample 2 (zero leaders even after a reset; errata A.2). X: one agent Resetting with rc = R and leader F; the
others Settled with distinct ranks 1,…,n−1 and leader F. Among computing agents there is no trigger (distinct ranks,
no Unsettled), so there is no trigger before the first awakening. By Lemma 4.1 / Theorem 4.2 an awakening
configuration with zero L agents is reached with probability ≥ 1 − (c₂+1/3)/n − n2^{−D/2}. All agents then wake
Unsettled; the epoch fails and costs ≤ (d + e/2)n² + t₁ steps until the expiry trigger (Proposition 7.6, case PT_0).

What is true is the corrected statement below: it requires the reset to start from a partially triggered
configuration with ≥ 1 leader. This always holds right after a trigger interaction, which writes L. For the stale
leader bits of A.4 (ii), any initial number of leaders in [1, n] is handled.

### 8.2 Corrected statement
**Lemma 8.1 (B42, corrected).** Let D = dn with d ≥ 8, n ≥ max(3, N₃₂), and D ≥ 8·exp(1)·a ln n. From every
X ∈ PT_L ∩ G, with any number of L agents in [1, n]:
P[C_{t₁ + ⌈(d/8)n(n−1)⌉} ∈ FD_1] ≥ (1 − (c₂ + 1/3)/n − n·2^{−D/2})·(1 − 8/d − n·exp(−κdn/4)).
On this event, the next awakening configuration, reached within ⌈nD/2⌉ further steps (proof of Theorem 4.2), has
exactly one L agent in the whole population. Every agent that wakes later wakes Unsettled, and no rank-0 collision
with a late leader is possible. For d = 32: q ≥ 0.99 × 0.75 − 10⁻⁹ ≥ 0.742.

Proof. Lemma 4.1, then the proof of Lemma 7.2 with β = d/8:
- μ ≤ 2⌈βn(n−1)⌉/n ≤ dn/4 =: μ⁺;
- waking requires ≥ ⌊D/2⌋ + 1 > 2μ⁺ interactions;
- Lemma 1.5(a) bounds that by exp(−κμ⁺);
- leader election misses the window with probability < 8/d.
Combine with Lemma 1.2(i). After FD_1, Lemma 2.3 keeps one L (no trigger before wakes; dedup cannot remove the last
L). ∎

If ≥ 2 leaders remain at the first wake, the late leaders wake as Settled rank 0. They collide with the first leader
or its subtree, or the stuck Unsettled agents expire. We do not analyse this: it is a failed epoch. In the window
form, failure costs nothing extra, because the next window starts from whatever configuration in G has been reached
(§9).

---

## 9. B43: Theorem 4.3 (uniform window and expected time)

**Theorem 9.1 (B43, uniform window).** Parameters R = ⌈c ln n⌉, D = 32n, E = 208n; n ≥ N₀; K := 298n²; p₀ := 0.48.
For every configuration X ∈ G of `rankDeltaOSSR`:
P_X[S is hit within K interactions] = P_X[C_K ∈ S] ≥ p₀.

Proof. Proposition 7.6 gives P_X[τ_H ≤ K_A] ≥ q_A with H = S ∪ PT_L. From every Y ∈ H:
- if Y ∈ S, P_Y[C_{K_B} ∈ S] = 1;
- if Y ∈ PT_L, it is ≥ q_B (Proposition 7.5).
Lemma 1.3 with H′ = S gives P_X[τ_S ≤ K_A + K_B] ≥ q_A q_B ≥ 0.861 × 0.559 ≥ 0.4813 ≥ 0.48.
For the window: K_A + K_B ≤ 2t₁ + 297n² ≤ 298n², by t₁ ≤ n²/2 (N3). S is closed, and hitting within a smaller
window implies hitting within K. ∎

**Corollary 9.2 (expected time, w.h.p.).** G is invariant, and S is absorbing. For every X ∈ G:
- E_X[τ_S] ≤ K/p₀ ≤ 621n² interactions, i.e. ≤ 621n parallel time (Lean: `expectedHittingTime_le_window_mul_inv_of_invariant`);
- P_X[τ_S > rK] ≤ (1 − p₀)^r = 0.52^r (`probNotHitBy_mul_window_le_initial_mul_pow`);
- hence τ_S ≤ 298n²·⌈ln n / ln(1/0.52)⌉ = O(n² log n) interactions with probability ≥ 1 − 1/n ([B] Cor. 4.4).

Proof. Restart: Lemma 1.1 at the deterministic times K, 2K, …, with Theorem 9.1 applied to C_{jK} ∈ G. Then
P[τ_S > (j+1)K | F_{jK}] ≤ 1 − p₀, and E[τ_S] ≤ Σ_{j≥0} K·(1−p₀)^j = K/p₀. ∎

Adversarial starts:

| start | where it is handled |
|---|---|
| stale dt | dt ≤ D by G; dt = 0 wakes at once; Corollary 2.5, Lemma 2.6 |
| Resetting agents but no triggered agent | stage A1 (Lemma 5.1) |
| zero leaders | PT_0 path in Proposition 7.6; Counterexample 2 |
| many leaders | Lemma 7.2, any |L₀| ≤ n |
| duplicate ranks | stage A4; also collisions during A3 are triggers, so τ_H is hit |
| Settled agents with wrong children counts | A3 uses only Lemma 2.7 (each Unsettled interaction recruits or decrements). A Settled agent with an overcounted children value never recruits; one with an undercounted value creates a duplicate rank. Both end in a trigger or in all-Settled. After a reset, every Settled agent comes from λ's tree with correct counts (Lemma 2.9). |
| Unsettled agents with any errorcount ≤ E (errorcount 0 included) | Lemma 2.7 |
| initially triggered agents with leader F | PT_0 path |

The printed epoch argument ([B] Thm 4.3 proof) relies on Corollary 3.5 followed by "an awakening configuration has a
unique leader with constant probability". That step fails for the awakening configurations of Corollary 3.5's second
branch (no trigger) and for PT_0 (§8.1). The window proof above routes every non-trigger case to a trigger first
(Proposition 7.6).

---

## 10. Discrepancies found

1. **B32 form (blocking for P1).** P1 must deliver B32* (§2.3): the max-process is fully positive at some time
   ≤ K₃₂, starting from any x₀ with max x₀ = R. The form written in P1/P2 assumes "no agent wakes" and concludes
   "every agent has been Resetting at some point". Its hypothesis fails with probability → 1 from adversarial starts,
   and its conclusion is not simultaneous.
2. **[B] Lemma 4.2 false as printed.** Counterexamples 1 and 2 in §8.1. Corrected: Lemma 8.1 (needs PT_L, i.e. a
   reset started by a trigger or with a stale L; probability depends on d).
3. **[B] Theorem 4.3 proof**, step "by Corollary 3.5 we only need fully computing or awakening": awakening
   configurations not preceded by a trigger can have 0 or many leaders. Repaired by Proposition 7.6 (go to a trigger
   first; zero-leader epoch costs O(n²) steps).
4. **[B] Lemma 4.1 proof.** The subtree count and the "dominating process" are not justified as written. The
   statement holds (Lemma 6.1, C = π²/2).
5. **Model: Part 1 is exclusive in Lean** (§0.2 item 1). [B] runs lines 5–18 in the same interaction. No effect on
   the proofs here.
6. **Model: triggers do not write dt in Lean.** Harmless (§0.2 item 3).
7. **[B] Protocol 2 line 10** reads "b.role ≠ Resetting" for both i ∈ {a, b}; Lean uses the partner's role (after
   Phases 1–2). The Lean reading is the intended one.
8. The packet's pseudocode matches the Lean source; no deviation found. One note: errorcount 0 in an initial
   Unsettled agent expires at its first Part-4 interaction.

## 11. Used facts (exact statements)

- U1 (Chernoff, upper, MGF form). If X ~ Bin(N, p), λ ≥ 0, then E e^{λX} ≤ exp(Np(e^λ − 1)). With Markov's inequality
  this gives Lemma 1.5(a), (b), (d) (proved in §1).
- U2 (Chernoff, lower). For X ~ Bin(N, p), μ = Np, 0 < δ < 1: P[X ≤ (1−δ)μ] ≤ exp(−δ²μ/2).
- U3 (Markov's inequality). For Y ≥ 0 and a > 0: P[Y ≥ a] ≤ E[Y]/a.
- U4. (1 − x)^t ≤ e^{−xt} for x ∈ [0, 1], t ≥ 0.
- U5. Σ_{i≥1} 1/i² = π²/6; Σ_{i=2}^{m} 1/(i(i−1)) = 1 − 1/m.
- U6 (B32*), from P1, in the form of §2.3.
- U7 (Lean, existing). `GoodPEM` invariance under `rankDeltaOSSR` (FiniteStatePEM.lean:903);
  `rankDeltaOSSR_settled_distinct_ranks`; restart lemmas `expectedHittingTime_le_window_mul_inv_of_invariant`
  (ExpectedTime.lean:3952) and `probNotHitBy_mul_window_le_initial_mul_pow` (:2242).
- U8 (construction). The scheduler is i.i.d. and independent of the states (`uniformPair`); this gives Lemma 1.1.

## 12. Open points

1. B32* is not proved here; it is P1's task, in the form of §2.3. N₀ depends on c₁ and c₂ through a and
   100(c₂ + 1). If P1 picks a different c, a = c₁ + (3/2)c ln 3 + 6 changes accordingly.
2. Lemma 1.3 (composition at a hitting time) is elementary, but I did not find it in `ExpectedTime.lean`. The present
   exact-time composition is `probHitAndInFrom_add_ge_mul`, at a deterministic time. Lean needs a first-hit
   decomposition: a sum over s of P[τ_H = s] times the window bound from C_s. It is used twice: Theorem 9.1 (Phase A to
   Phase B) and Corollary 5.2.
3. The constants are not optimised; d = 32 and e = 208 were chosen so that every tail is exp(−Θ(n)). Smaller e is
   possible, by using the superepidemic for waking in stage B3 instead of the dt countdown.
4. Not in scope: interference with P_EM (A.4 (i): swap and the median timer). Theorem 9.1 is for
   Optimal-Silent-SSR alone.
5. For 2 ≤ n < N₀ only finiteness is available (positive window probability per n). The theorems are stated for
   n ≥ N₀.
6. Independent check: these proofs were re-derived by a second reader and independently reviewed (R2); see `FIX2-BURMAN.md` for the resulting status.
