# Soloveichik–Cook–Winfree–Bruck, Theorems 3.1, 3.2, 4.1 — paper proofs

Paper: D. Soloveichik, M. Cook, E. Winfree, J. Bruck,
"Computation with finite stochastic chemical reaction networks", Caltech technical report
etr085v2 (Dec 2007); Natural Computing 7
(2008) 615–633. Section and lemma numbers are those of etr085v2. Status of the theorems:
`OPEN_PROBLEMS.md` §6.2.

Status labels: **PROVED** (complete proof below), **SKETCH** (route and estimates given,
not every step checked), **OPEN** (object or proof missing).

| Paper item | Here | Status |
|---|---|---|
| Lemmas A.1–A.3 (clock) | §2, Lemmas 2.1–2.4 (discrete occupation form) | PROVED |
| Lemma A.4, Theorem 3.1 (RM, bounded) | §3, Theorem 3.1′ | PROVED |
| Lemmas A.5–A.9, Theorem 3.2 (TM, bounded) | §4 | SKETCH; improves A.8 and the time bound |
| Section 4, A.5, Theorem 4.1 (TM, unbounded) | §5 | OPEN (network not given in the paper) |

## 1. Model

**Stochastic kinetics.** A state is a vector `z ∈ ℕ^S`. Reaction `i` with reactant vector
`l_i`, rate constant `k` and volume `v` has propensity `α_i(z) = (k / v^{|l_i|-1}) ∏_s C(z_s, l_{i,s})`.
Every reaction used below is bimolecular with two distinct reactant species, so
`α_i(z) = (k/v) z_s z_{s'}`. Write `α_i = (k/v) β_i` with `β_i(z) = z_s z_{s'}` (the
unit-rate propensity, Ripple's `Reaction.propensity` with `k = 1`) and
`B(z) = Σ_i β_i(z)`.

The continuous-time chain is the jump chain `Z_0, Z_1, …` with
`P(Z_{n+1} = z + Δ_i | Z_0..Z_n) = β_i(Z_n) / B(Z_n)` (the factor `k/v` cancels), together with
holding times that are, given the jump chain, independent exponentials with means
`(v/k) / B(Z_n)`. Hence for every nonnegative path functional
`E[time spent in states satisfying P before jump N] = (v/k) E[Σ_{n<N} 1{P(Z_n)} / B(Z_n)]`
(Tonelli plus the conditional mean of the holding times), whenever the stopping index `N` is a
function of the jump chain; non-explosion is not needed. All probability statements below are
about the jump chain (Ripple's `MassAction.rawLaw`); all time statements are of this form,
reported in units of `v/k`.

**Occupation measures.** For a jump chain started at `z_0` and any countable statistic
`X_n = F(Z_0, …, Z_n)` let `p_n(ξ) = P(X_n = ξ)`, `O(ξ) = Σ_n p_n(ξ) ∈ [0, ∞]` and, when
`X_n` determines `Z_n`, `W(ξ) = O(ξ)/B(z(ξ))` (expected time in `ξ`, units `v/k`). If the
`n`-th jump moves `ξ` to `ξ'` with probability `β(ξ → ξ')/B(z(ξ))`, then writing
`O(ξ') = p_0(ξ') + Σ_n p_{n+1}(ξ')` with `p_{n+1}(ξ') = Σ_ξ p_n(ξ) β(ξ→ξ')/B(z(ξ))` (Tonelli in
`[0, ∞]`) gives the **balance law**

  `O(ξ') = 1{ξ' = ξ_0} + Σ_ξ W(ξ) β(ξ → ξ')`.   (1.1)

The expected number of jumps of a given type `τ` taken from states in a set `A` is
`Σ_{ξ∈A} W(ξ) β_τ(ξ)` (sum over `n` of `p_n(ξ) β_τ/B`).

## 2. The clock module (paper Lemmas A.1–A.3)

Clock species `C_1, …, C_l` (`l ≥ 2`), accuracy species `A` (count `a ≥ 1`) and `A*` (count 1).
Reactions (paper Fig. 3.1B): `up_c : C_c + A → C_{c+1} + A` and
`down_c : C_{c+1} + A* → C_c + A*` for `1 ≤ c < l`. Exactly one clock molecule is present;
write `c` for its index. Unit-rate propensities: `up` at `c < l` is `a`, `down` at `c > 1` is 1.

**Epoch.** Fix the rest of the state, an "outer part" `x`, which the clock reactions do not
change. While the outer part is `x`, the clock is a birth–death chain on `{1..l}` with up rate
`a`, down rate 1, and two kinds of exits that change `x`: a clock-independent exit of total
rate `ρ ≥ 0`, and an exit of rate `κ ≥ 0` that is possible only at `c = 1` (the tick: `dec2`
for the RM, the state-transition initiation for the CTM). So the total unit-rate propensity is
`B(x, c) = ρ + κ 1{c=1} + a 1{c<l} + 1{c>1}`.

Let `w(c) = W(x, c)` be the expected time spent with outer part `x` and clock `c` (within one
fixed "epoch counter" value, see §3), and `e(c)` the expected number of entries into
`(x, c)` from other outer parts (plus the initial mass). The balance law (1.1) restricted to
outer part `x` reads, for `1 ≤ c ≤ l`, with `w(0) = w(l+1) = 0`,

  `B(x, c) w(c) = e(c) + a w(c-1) + w(c+1)`.   (2.1)

Write `S(c) = Σ_{c' ≤ c} w(c')`, `E(c) = Σ_{c' ≤ c} e(c')`, and `μ = μ_l(a) = 1/(1 + a + … + a^{l-1})`.

**Lemma 2.1 (flux identity).** If all `w(c) < ∞`, then for `1 ≤ c ≤ l-1`

  `w(c+1) − a w(c) = ρ S(c) + κ w(1) − E(c)`,   (2.2)

and `ρ S(l) + κ w(1) = E(l)`.

*Proof.* Sum (2.1) over `c' ≤ c`. For `c ≤ l-1` the left side is
`ρ S(c) + κ w(1) + a S(c) + (S(c) − w(1))` and the right side is
`E(c) + a S(c-1) + (S(c+1) − w(1))`; subtract. For the total, sum (2.1) over all `c`:
`ρ S(l) + κ w(1) + a S(l-1) + (S(l) − w(1)) = E(l) + a S(l-1) + (S(l) − w(1))`. ∎

**The cone.** `C_a = {v ∈ [0,∞)^l : v(c+1) ≥ a v(c), 1 ≤ c < l}`. It is a convex cone, closed
under nonnegative (also countable, when finite) combinations, and `δ_l ∈ C_a`.

**Lemma 2.2 (cone invariance; replaces Lemma A.1 and the "memoryless" step of A.4).** Let
`a > 0`, `ρ, κ ≥ 0`, `w ∈ [0,∞)^l` satisfy (2.1) with `e ∈ C_a`. Then `w ∈ C_a`.

*Proof.* Put `u(c) = w(c+1) − a w(c)` for `1 ≤ c ≤ l-1`, `u(0) = κ w(1) ≥ 0`, `u(l) = 0`.
By (2.2), `u(c) = ρ S(c) + κ w(1) − E(c)` for `0 ≤ c ≤ l` (with `S(0) = E(0) = 0`; the case
`c = l` is the total identity). For `1 ≤ c ≤ l-1`:

  `(ρ + a + 1) u(c) − a u(c−1) − u(c+1) = e(c+1) − a e(c)`.   (2.3)

Indeed, substituting the expressions for `u`: the `κ w(1)` terms give `ρ κ w(1)`; the `E` terms
give `−(ρ+a+1)E(c) + a E(c−1) + E(c+1) = −ρ E(c) − a e(c) + e(c+1)`; the `S` terms give
`ρ[(ρ+a+1) S(c) − a S(c−1) − S(c+1)] = ρ[ρ S(c) + a w(c) − w(c+1)] = ρ[ρ S(c) − u(c)]`.
The sum is `ρ(κ w(1) − E(c) + ρ S(c)) − ρ u(c) + e(c+1) − a e(c) = e(c+1) − a e(c)`.

The right side of (2.3) is `≥ 0` because `e ∈ C_a`. Suppose some `u(c) < 0` with
`1 ≤ c ≤ l-1`; let `m = min u < 0` over `1..l-1` and `c*` the smallest index attaining it.
Then `u(c*−1) > m` (either `c* = 1` and `u(0) ≥ 0 > m`, or `c*−1 ≥ 1` is not a minimiser) and
`u(c*+1) ≥ m` (`u(l) = 0 > m`). Hence, as `a > 0`,
`a u(c*−1) + u(c*+1) > (a+1) m`, and (2.3) gives `(ρ+a+1) m > (a+1) m`, i.e. `ρ m > 0`,
impossible since `ρ ≥ 0 > m`. So `u ≥ 0`, i.e. `w ∈ C_a`. ∎

**Lemma 2.3 (tick probability; replaces Lemmas A.1–A.2).** Under Lemma 2.2's hypotheses,
`w(1) ≤ μ S(l)`. If moreover `ρ > 0`, then `S(l) ≤ E(l)/ρ`, so the expected number of ticks
taken from outer part `x` is `κ w(1) ≤ κ μ E(l) / ρ`.

*Proof.* `w ∈ C_a` gives `w(c) ≥ a^{c−1} w(1)`, so `S(l) ≥ w(1)(1 + a + … + a^{l−1})`.
The total identity gives `ρ S(l) ≤ E(l)`. The tick count is `Σ W β_tick = κ w(1)` (§1). ∎

**Lemma 2.4 (time to tick; replaces Lemma A.3).** If `ρ = 0`, `κ = 1`, `a ≥ 2`, `e ≥ 0` and all
`w(c)` are finite, then `S(l) ≤ (a/(a−1)) E(l)/μ ≤ 2 E(l)/μ`. (For every `a > 0`:
`S(l) ≤ l E(l)/μ`, since `w(c) ≤ w(1)/μ`.)

*Proof.* The total identity gives `w(1) = E(l)`; (2.2) gives `w(c+1) ≤ a w(c) + w(1)`, so by
induction `w(c) ≤ E(l)(1 + a + … + a^{c−1}) = E(l)(a^c − 1)/(a − 1)`. Summing,
`S(l) ≤ E(l) Σ_{c=1}^{l} a^c/(a−1) = (a/(a−1)) E(l) Σ_{c=1}^{l} a^{c−1} = (a/(a−1)) E(l)/μ`. ∎

Lemma 2.4 needs no cone hypothesis (it holds for every entry law).

**Finiteness.** In §3 the `w(c)` are expected times inside one epoch and are finite: if
`ρ > 0`, the expected number of clock-independent exits is `ρ S(l) ≤ 1` (one per path, §3);
if `ρ = 0, κ = 1`, the expected number of ticks is `w(1) ≤ 1`, and (2.1) at `c` gives
`w(c+1) ≤ B(x,c) w(c)`, so all `w(c)` are finite by induction.

**Comparison with the paper.** Lemma A.1 proves the ratio invariant `p_{i+1}/p_i ≥ r/f` for the
clock started at state `l` and A.4 then appeals to a "memoryless property" for the clock at the
start of a later decrement, whose law depends on the history. Lemma 2.2 proves the invariant
for every entry law in the cone and shows the entry laws stay in the cone (§3, step 2), which is
the missing step. Lemma 2.3 bounds the tick probability by `μ E(l)/ρ` directly (no exponential
comparison).

## 3. Theorem 3.1: bounded register-machine simulation

**Machine.** Finite sets `Reg`, `Label`, `start ∈ Label`, `code : Label → Instr` with
`Instr = inc r j | decJz r j k | halt` (Ripple `RegisterMachine.RM`; `decJz r j k`: if register
`r` is nonzero, decrement and go to `j`, else go to `k`). Configurations `(q, y)`,
`y : Reg → ℕ`; `step` as in `RegisterMachine.RM.step?`; `cfg_0 = (start-or-given q_0, y_0)`
and `cfg_{k+1} = step cfg_k` while defined (it is undefined exactly at `halt`; then
`cfg_{k+1} = cfg_k` by convention).

**Network `N(M, l)`** (paper Fig. 3.1, `l ≥ 2`). Species `S_q (q ∈ Label)`, `M_r (r ∈ Reg)`,
`C`, `C_1..C_l`, `A`, `A*`. Reactions, all rate `k`:
- `code q = inc r j`: `inc_q : C + S_q → C + S_j + M_r`;
- `code q = decJz r j k`: `dec1_q : S_q + M_r → S_j`, `dec2_q : C_1 + S_q → C_l + S_k`;
- clock: `up_c`, `down_c` (`1 ≤ c < l`) as in §2.

The network is fixed by `M` and `l`; δ, the input and `t` enter only through the initial state
`z_0(a, q_0, y_0)`: `S_{q_0} = 1`, `M_r = y_0(r)`, `C = 1`, `C_l = 1`, `A = a`, `A* = 1`, all
other species 0.

**Invariants.** Every reaction preserves `Σ_q S_q`, `C`, `Σ_c C_c`, `A`, `A*`. So every
reachable state is `⟨q, y, c⟩` (one state molecule `S_q`, registers `y`, one clock molecule
`C_c`, `C = 1`, `A = a`, `A* = 1`), and every reaction changes the state (for `l ≥ 2`).
Unit-rate propensities at `⟨q, y, c⟩`: `inc_q`: 1; `dec1_q`: `y(r)`; `dec2_q`: `1{c=1}`;
`up_c`: `a 1{c<l}`; `down`: `1{c>1}`; so `B > 0` (the clock always has an enabled reaction)
and the chain never stops.

**RM events and errors.** `inc`, `dec1`, `dec2` are RM reactions. `K_n` = number of RM reactions
among the first `n` jumps. An **error** is a firing of `dec2_q` at a state with `y(r) ≥ 1`
(`code q = decJz r j k`). Write `Err_{k+1}` for the event that the `(k+1)`-th RM reaction is an
error.

**Lemma 3.1 (determinism off errors).** On the complement of `Err_1 ∪ … ∪ Err_k`, every `n`
with `K_n ≤ k` has `(q, y)(Z_n) = cfg_{K_n}`.

*Proof.* Induction on `n`. Clock reactions change neither `(q, y)` nor `K`. At `⟨q, y, c⟩`
with `(q, y) = cfg_j`: if `code q = inc r j'`, the only RM reaction is `inc_q`, giving
`cfg_{j+1}`; if `code q = decJz r j' k'` and `y(r) = 0`, `dec1_q` has propensity 0 and
`dec2_q` gives `(k', y) = cfg_{j+1}`; if `y(r) ≥ 1`, `dec1_q` gives `cfg_{j+1}` and `dec2_q`
is an error; at `halt` there is no RM reaction. ∎

**Theorem 3.1′.** For every `M`, `l ≥ 2`, `a ≥ 1`, input `(q_0, y_0)` and `t ∈ ℕ`, under the
jump chain of `N(M, l)` from `z_0(a, q_0, y_0)`:

(i) `P(Err_1 ∪ … ∪ Err_t) ≤ t μ_l(a)`; hence with probability `≥ 1 − t μ_l(a)`, for every
`n` with `K_n ≤ t`, `(q, y)(Z_n) = cfg_{K_n}`.

(ii) if `a ≥ 2`, the expected time until `t` RM reactions have occurred or the state species is
`S_halt`-type (code `halt`), `E[T_t] = (v/k) E[Σ_n 1{K_n < t, code q(Z_n) ≠ halt}/B(Z_n)]`,
satisfies `E[T_t] ≤ (v/k) · 2t/μ_l(a)`.

*Proof.* Statistic `X_n = (K_n, Z_n)`; for `k ∈ ℕ`, an outer part `x = (q, y)` and clock `c`,
let `W_k(x, c)` be the occupation time of `(k, ⟨x, c⟩)` and `w_{k,x} = W_k(x, ·)`.

*Step 1 (balance in an epoch).* Within `K = k` the outer part `x` changes only by RM
reactions, which increase `K`. So (1.1) for `(k, ⟨x, c⟩)` is (2.1) with `ρ = ρ(x)` (1 for
`inc`, `y(r)` for `decJz`, 0 for `halt`), `κ = κ(x)` (1 for `decJz`, else 0) and entry vector

  `e_{k,x}(c) = 1{k = 0, x = (q_0,y_0), c = l} + Σ_{x'} ρ(x' → x) w_{k−1,x'}(c) + 1{c = l} Σ_{x'} 1{x' →_{dec2} x} w_{k−1,x'}(1)`,

where `ρ(x' → x)` is the unit-rate propensity of the `inc` or `dec1` reaction taking `x'` to
`x` (it does not depend on `c`). The total entry `E_{k,x}(l)` is the probability that the
`k`-th RM reaction (for `k = 0`: the start) lands in outer part `x`; so `Σ_x E_{k,x}(l) ≤ 1`.

*Step 2 (cone, by induction on `k`).* For every non-halt `x`, `w_{k,x} ∈ C_a`. For `k = 0`
the entry is `δ_l` or 0. For `k ≥ 1`, `e_{k,x}` is a nonnegative combination of the vectors
`w_{k−1,x'} ∈ C_a` (the `inc`/`dec1` entries keep `c`; halt states have no RM exits so do
not contribute) and a multiple of `δ_l`; it is finite since its total is `≤ 1`. The `w_{k,x}`
are finite (§2, finiteness), so Lemma 2.2 applies.

*Step 3 (errors).* `Err_{k+1}` happens exactly when a `dec2` is taken from some `(k, ⟨x, 1⟩)`
with `x` at risk (`code q = decJz r ·`, `y(r) ≥ 1`). Its probability is
`Σ_{x at risk} w_{k,x}(1)` (§1). For such `x`, `ρ = y(r) ≥ 1`, `κ = 1`, and Lemma 2.3 gives
`w_{k,x}(1) ≤ μ E_{k,x}(l)/y(r) ≤ μ E_{k,x}(l)`. Summing over `x`: `P(Err_{k+1}) ≤ μ`; summing
over `k < t` gives (i), and Lemma 3.1 gives the correctness statement.

*Step 4 (time).* By Tonelli, `E[T_t] = (v/k) Σ_{k<t} Σ_{x non-halt} S_{k,x}(l)`. For `inc`
and at-risk `x`, `ρ ≥ 1` and `S ≤ E_{k,x}(l)`; for `decJz` with `y(r) = 0`, Lemma 2.4 gives
`S ≤ 2 E_{k,x}(l)/μ`. As `2/μ ≥ 1` and `Σ_x E_{k,x}(l) ≤ 1`, `E[T_t] ≤ (v/k) t · 2/μ`. ∎

**Corollary (paper Theorem 3.1).** Fix `l = 2` (so `1/μ = 1 + a`). For every RM `M` the
network `N(M, 2)` satisfies: for every `δ ∈ (0, 1]`, every input and every `t ≥ 1`, with
`a = max(2, ⌈t/δ⌉)`, the cumulative error probability over `t` RM steps is `≤ t/(1+a) ≤ δ`
and `E[T_t] ≤ (v/k) · 2t(1 + a) ≤ 6 (v/k) t²/δ` (since `1 + a ≤ max(3, t/δ + 2) ≤ 3t/δ`).
For general `l`, `a = max(2, ⌈(t/δ)^{1/(l−1)}⌉)` gives error `≤ δ` and
`E[T_t] ≤ l 2^l (v/k) t²/δ`. This is the paper's `O(v t²/(kδ))`.

Remarks. (a) The per-step bound `μ/y(r)` improves with the register value, as the paper notes
("otherwise, the error is even smaller"). (b) The quantifier order is the paper's: the network
depends only on `M` (and the fixed `l`); `a` is chosen after `δ`, the input and `t`. (c) The
time bound counts all reactions, clock included; it holds whether or not an error occurred.

## 4. Theorem 3.2: bounded TM simulation (SKETCH; superseded)

Superseded by `docs/audit/FIX3-SCWB-T32.md` (complete proof of Theorem 3.2′ for a repaired
network, independently reviewed). The network of Fig. 3.2 as drawn does not
work (F1: in microstep 4 zeroing, writing and the shift race on `M`, and the result is wrong in
every run; F2: the tick's `I` is captured by `T` or `M` outside microstep 3; F3: `S_{j,4}` does not
determine the digit to zero or the bit to write); Theorem 3.2 holds via the repaired network.
The sketch below is kept as written.

Network: paper Fig. 3.2 (CTM microsteps `(i, z)`, `z = 1..4`, state species with count
`m = 3^{s−1}`, `s = s_ct`; memory `M`, threshold `T`, `D`, `B`, `K_1`, `K_2`, primed copies;
clock as Fig. 3.1B). The paper is inconsistent about the state-transition initiation: the text
(p. 8) says a state species reacts with `C_1`; Fig. 3.2 has `C_1 → C_l + I` catalysed by `A*`,
the produced `I` then starting the transition. We follow the figure.

**Error per microstep (improves Lemma A.8).** A microstep window runs from the tick that opens
it (clock at `C_l`) to the next tick. Until that next tick, the clock and the rest of the
network are independent: only the tick involves `C_c`, `A`, `A*`, and `#A`, `#A*` are constant.
Let `T` be the completion time of the microstep's reactions in the clock-free dynamics. By the
paper's Lemmas A.1–A.2 (clock started at `C_l`), the tick time `τ` has
`P(τ < s) ≤ 1 − e^{−λ s}` with `λ = f μ_l(r/f)`, `f = (k/v)#A*`, `r = (k/v)#A`; by independence
`P(τ < T) = E[P(τ < T | T)] ≤ E[1 − e^{−λT}] ≤ λ E[T]`. So the error per microstep is at most
`λ E[T]` and `λ = ε/E[T]` suffices; the paper (Chebyshev with the variances of A.5–A.7) needs
`λ = Θ(ε^{3/2} k m/(v log m))`. With `E[T] = O((v/(km)) log m)` (Lemmas A.5–A.7, expectations
only): `λ = Θ(ε k m/(v log m))`, i.e. `#A^{l−1} = Θ(1/ε)` with the paper's `#A*`.

**Time per microstep.** The tick time from `C_l` has expectation at most `l/λ`: for the
autonomous clock with a killing tick, (2.2) with `ρ = 0` gives `w(c+1) ≤ a w(c) + w(1)`, so
`w(c) ≤ w(1)/μ` and `S(l) ≤ l E(l)/μ` for every `a > 0` (no `a ≥ 2` needed); in time units
`1/f` this is `≤ l/λ`. Total: `t_ct = O(t_tm(s_tm+∆))` CTM steps, four microsteps each,
`ε = δ/(4 t_ct)`, `log m = Θ(s_ct)`, `s_ct = 2 s_tm + ∆`: expected time
`O(t_ct · v s_ct t_ct/(k 3^{s_ct} δ)) = O(v (s_tm+∆)^3 t_tm²/(k 3^{2 s_tm + ∆} δ))`, against the
paper's `O(v (s_tm+∆)^{7/2} t_tm^{5/2}/(k 3^{2s_tm+∆} δ^{3/2}))`.

Not checked here, needed for PROVED: (1) correctness of the CTM microstep logic of Fig. 3.2
(threshold comparison with `#T = 2·3^{s−1} + 2·3^{s−3}`, the `D/K_1/K_2` zeroing of the high
digit, `B → (z+1)M + B*`, `M → 3M†`, restoration of `D`, `B`, `T`, `M`) when every reaction of a
microstep completes before the tick, including the autocatalytic transitions
`S_{i,z} + S_{i,z+1} → 2 S_{i,z+1}` and the fate of the `I` molecules; (2) Lemmas A.5–A.7 with
explicit constants (A.7's proof splits the run into halves by time reversal and is the least
explicit); (3) Lemma A.9 (TM → CTM, cited from Neary–Woods). Ripple has CTM material
(`Ripple/sCRNUniversality/CTM/`), but its `statePairTransferNetwork` is not the Fig. 3.2
network and does not depend on the machine.

## 5. Theorem 4.1: unbounded TM simulation (OPEN)

The paper gives no network for Theorem 4.1: Section 4 and A.5 describe modifications
("tripling A can be done by reactions akin to `A → A†` and `A† → 3A`", a clock with `l = 5`,
`#A` increased by `Θ(3^{s_ct})` per step, footnote 5: clock reactions additionally catalysed by
intermediate species). The object to formalise is unspecified. The analysis also needs Lemma 2.2 with an entry law in `C_b` for `b < a` (the
accuracy count changes between epochs). This holds for every `l` (found in the review, §7): with
`u_b(c) = w(c+1) − b w(c)`, `(ρ+a+1) u_b(c) − a u_b(c−1) − u_b(c+1) = e(c+1) − b e(c)` for
`1 ≤ c ≤ l−1`, with boundary values `u_b(0) = w(1)(1 − b(1−κ)/a) ≥ 0` and
`u_b(l) = (a−b) w(l) ≥ 0`, and the same minimum principle applies. The RM analogue (Section 4:
`dec1` produces one `A`, `l = 3`, error `Σ_{i ≥ i_0} O(1/i²)`) is not a numbered theorem; the
paper is inconsistent there (Section 4: `dec1` produces `A`; A.4: "after `i` dec2 steps,
`#A = i_0 + i`"). Not formalised here.

## 6. Lean (Theorem 3.1′): done

Done in `Ripple/sCRNUniversality/RegisterMachine/Clocked/` (2026-11-09), along the
plan below: `Network.lean` (`net M L`, reduced states `enc a σ`, `propensity_enc`, `fire_enc`),
`Occupation.lean` (`occ_balance`, the balance law (1.1) under `rawLaw`), `Levels.lean`
(level split, exit and entry bounds, `clockBalance`, `cone_eN`, `level_bounds`), `Theorem.lean`
(`simOK_of_not_mem`, `law_Err_le`, `expTime_eq`, `theorem_3_1_general`, `scwb_theorem_3_1`).
The clock starts at `C_l` (`Fin.last L`).

Plan as written before the formalization:


Module `Ripple/sCRNUniversality/RegisterMachine/ClockedRM.lean` (new) on top of
`Stochastic/MassAction/Traj.lean` (`rawLaw`) and `RegisterMachine/Basic.lean` (`RM`, `step?`):
1. `clockedRMNetwork M l` (§3 network; species `Label ⊕ Reg ⊕ Unit ⊕ Fin l ⊕ Unit ⊕ Unit`),
   `initState a q₀ y₀`, invariants, propensities.
2. Bridge: marginal recursion of a prefix statistic under `rawLaw`
   (`Kernel.partialTraj_succ_eq_comp`, `map_partialTraj_succ_self`), giving (1.1).
3. Lemma 2.2 on `Fin l → ℝ` (minimum principle), Lemmas 2.3, 2.4.
4. Theorem 3.1′ (i) as a bound on `rawLaw` of the error event; (ii) as a bound on the
   `rawLaw`-expectation of `Σ_n 1{…}/B(Z_n)`; the corollary with `l = 2`.

## 7. Review (2026-11-08)

One independent reviewer, against the PDF (figures on pp. 5, 8), with exact rational checks
of the §2 identities (20,000 random cases, `l = 2..7`, `ρ = 0` and `κ ∈ {0, 1}` included) and a
Monte Carlo run of the §3 network on an adversarial machine (observed error and time below
`tμ` and `2t/μ`). Verdicts: §1 OK; §2 OK (identity (2.3) re-derived via ghost points
`w(0) = (1−κ)w(1)/a`, `w(l+1) = a w(l)`; minimum principle OK including `ρ = 0`); §3 OK
(network matches Fig. 3.1, entry vector, cone induction, error and time steps, corollary);
faithfulness OK and stronger (time bound unconditional, `a` independent of the input).
Corrections adopted: §4 rewritten (independence argument instead of the cone, microstep time
via the `a`-free bound `l/λ`, `#A^{l−1} = Θ(1/ε)`, Fig. 3.2 vs p. 8 discrepancy); §5 `C_b`
invariance for `b ≤ a` (general `l`) and the A.4 inconsistency; §1 notation; corollary
constant 6.
