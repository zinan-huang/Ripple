# Soloveichik–Cook–Winfree–Bruck, Theorem 3.2 — complete paper proof

Paper: D. Soloveichik, M. Cook, E. Winfree, J. Bruck,
"Computation with finite stochastic chemical reaction networks", Caltech technical report
etr085v2 (Dec 2007); Natural Computing 7
(2008) 615–633. Numbers of sections, lemmas and figures are those of etr085v2. This note closes
the three gaps listed at the end of `FIX3-SCWB.md` §4 and supersedes that sketch. Fig. 3.2 was
read from the PDF (page 8, rendered at 400 dpi); the text dump loses it.

| Paper item | Here | Status |
|---|---|---|
| Fig. 3.2 network | §3 | **construction fails** (three defects F1–F3, proofs); repaired network `N♯` |
| Correctness of the microsteps | §4, Lemmas 4.2–4.5 | PROVED for `N♯` |
| Lemmas A.1–A.3 (clock) | §2, Lemmas 2.1–2.2 | PROVED (exact `E[σ]`) |
| Lemmas A.5–A.7 (completion times) | §1.3, §5 | PROVED, expectations only, explicit constants |
| Lemma A.8 (error per microstep) | §7, step 1 | PROVED, stronger: `λ = Θ(ε k m/(v log m))` |
| Lemma A.9 (TM → CTM) | §6 | PROVED directly (no citation used) |
| Theorem 3.2 | §7, Theorem 3.2′ | PROVED, via the repaired network `N♯`; better bound than the paper's |

**Summary.** (1) The network of Fig. 3.2 does not simulate a CTM even when every microstep
finishes before the next clock tick: in microstep 4 the memory count always ends too large by
at least 2 (F1, Proposition 3.1); the tick's molecule `I` is captured by `T` or `M` outside
microstep 3 with probability `≥ 2/11` per CTM step (F2); and `S_{j,4}` does not determine the
digit to remove or the bit to write for a non-normalised CTM (F3). The construction fails;
Theorem 3.2 itself holds via the repaired network. (2) With three local repairs (§3.3; the same
repairs as a parallel working note on Theorem 4.1), every microstep is correct (§4). (3) The
four microsteps of one CTM step complete in total expected time
`≤ (v/(km))(21.9 h + 12.6) ≤ 26 (v/k) h/m`, `h = 1 + ln m`, `m = 3^{s−1}` (§5). (4) Error
`≤ δ` and `E[time] ≤ 208 (3/2)^{l−1} (v/k) t_ct² h/(m δ)`, i.e.
`O(v (s_tm+Δ)^3 t_tm^2 / (k 3^{2 s_tm + Δ} δ))`, against the paper's
`O(v (s_tm+Δ)^{7/2} t_tm^{5/2} / (k 3^{2 s_tm + Δ} δ^{3/2}))` (§7).

Conventions. Time is in units of `v/k`: a bimolecular reaction `X + Y → …` (always two
distinct reactant species here) has propensity `#X · #Y` in these units, and every expected
time below is to be multiplied by `v/k`. `H_n = Σ_{q ≤ n} 1/q ≤ 1 + ln n`. "Catalysed by `C`"
means `C` is a reactant and a product. `m = 3^{s−1}` with `s = s_ct ≥ 3`, so `9 | m` and
`m ≥ 9`, and `h := 1 + ln m ≥ 1 + ln 9 > 3.19`.

## 1. Model and probabilistic tools

**1.1 Kinetics.** The stochastic kinetics of a network with reactions `ρ` (state change
`ν_ρ`, propensity `α_ρ`) is the continuous-time Markov chain with jump rates `α_ρ(x)` from `x`
to `x + ν_ρ`, run up to its explosion time `ζ ≤ ∞`.

*Fact 1.1 (random time change; Ethier–Kurtz 1986, Ch. 6 §4; Anderson–Kurtz 2011).* Let
`(Y_ρ)` be independent unit-rate Poisson processes. The equation
`X(t) = X(0) + Σ_ρ ν_ρ Y_ρ(∫_0^t α_ρ(X(u)) du)` has a unique solution up to its explosion
time, and the solution is the chain above. The chain has the strong Markov property at
stopping times `< ζ`.

*Fact 1.2 (labelled molecules).* Give every molecule a label (new molecules get fresh labels)
and let each *reaction instance* (a choice of reactant molecules) be a channel with rate 1.
The unlabelled projection of this labelled chain has, from every labelled state, total rate
`#X·#Y` into each unlabelled target, a function of the unlabelled state only; by Dynkin's
lumpability criterion it is the kinetics chain.

*Tagged projection.* Fix one labelled molecule `i` and forget all other labels: the state is
(unlabelled counts, the species of `i` or "gone"). For each reaction `X + Y → …` and each
role of `i`, the instances in which `i` takes part are lumped into one channel; e.g. if `i`
is an `X`, "`i` reacts with some `Y`" has propensity `#Y·1{i is an X}`, and the remaining
instances form the channel "an untagged `X` reacts with some `Y`" with propensity
`(#X − 1{i is an X})·#Y`. The aggregate rate into each target of the tagged projection
depends only on the tagged state, so the tagged projection of the fully labelled chain is
again a Markov chain (Dynkin), with these channels; Fact 1.1 applies to it.

*How these are used (§5, Lemma 5.4).* The fully labelled chain is the single probability space
on which all molecules live, so extinction times of a family are maxima of per-molecule exit
times, and Lemma 1.4 (union bound) needs only the law of each molecule's exit time. That law
is the same in the fully labelled chain and in its tagged projection for that molecule, and
it is computed in the tagged projection by Fact 1.1, with one Poisson process per lumped
channel of the tagged molecule (e.g. for an `M`-molecule: shift, pairing with some `T`,
return from `M*`; for a `K`-molecule: removal by some `M†`). No independence between
different molecules is used. We apply this only after restarting at a stopping time by the
strong Markov property, with fresh Poisson processes, so no multiparameter stopping-time
argument is needed.

**1.2 Three death chains (replace Lemmas A.5–A.7).** Each of the following is a statement
about one integer coordinate `Y` that, during the period considered, changes only as
stated; then `Y` is itself a Markov chain with the stated rates (its rates depend on `Y`
only), and its absorption time is a sum of independent exponentials.

*Lemma 1.3.*
(a) *Catalytic decay (A.5).* If `Y` decreases by 1 at rate `cY` (each molecule converted by
a catalyst of fixed count `c`) and nothing increases it, the time to `Y = 0` from `Y = n` has
mean `H_n/c`.
(b) *Annihilation with excess (A.6).* If `X + Z → …` is the only reaction changing `#X`,
`#Z`, and `#Z − #X = Δ ≥ 1`, then from `#X = n` the time to `#X = 0` has mean
`Σ_{q=1}^{n} 1/(q(q+Δ)) = (H_n + H_Δ − H_{n+Δ})/Δ ≤ H_Δ/Δ`, and `H_Δ/Δ` is decreasing in `Δ`.
(c) *Autocatalysis (A.7).* If `X + Z → 2Z` is the only reaction changing `#X`, `#Z`, and
`#X + #Z = m`, then from `#Z = 1` the time to `#X = 0` has mean
`Σ_{j=1}^{m−1} 1/(j(m−j)) = 2H_{m−1}/m`.

*Proof.* (a) Rates `cq`, `q = n, …, 1`. (b) With `q = #X`, the rate is `q(q+Δ)`; partial
fractions `1/(q(q+Δ)) = (1/Δ)(1/q − 1/(q+Δ))`; `H_Δ/Δ` is the mean of `1/q` over
`q ≤ Δ`. (c) With `j = #Z` the rate is `j(m−j)`; `1/(j(m−j)) = (1/m)(1/j + 1/(m−j))`. ∎

These are exact; the paper's variance statements are not needed. Lemma 1.3(c) replaces the
time-reversal argument of A.7.

*Lemma 1.4 (maxima).* If `L_1, …, L_n ≥ 0` satisfy `P(L_i > t) ≤ K e^{−ct}` with `K ≥ 1`
(no independence assumed), then `E[max_i L_i] ≤ (1 + ln(nK))/c`. If the `L_i` are i.i.d.
`Exp(c)`, `E[max_i L_i] = H_n/c`.

*Proof.* `E[max] = ∫_0^∞ P(max > t) dt ≤ ∫_0^∞ min(1, nK e^{−ct}) dt = ln(nK)/c + 1/c`.
The i.i.d. case is (a) above. ∎

## 2. The clock (Lemmas A.1–A.3)

Clock species `C_1, …, C_l` (`l ≥ 2`, fixed with the network), `A`, `A*`, counts `#A`,
`#A*` constant. Reactions (Fig. 3.1B and the first row of Fig. 3.2A):
`C_c + A → C_{c+1} + A`, `C_{c+1} + A* → C_c + A*` (`1 ≤ c < l`), and the **tick**
`C_1 + A* → C_l + I + A*`. Put `r = #A`, `f = #A*` (rates in units `k/v`), `a = r/f`,
`μ = μ_l(a) = 1/(1 + a + … + a^{l−1})`, `λ = f μ` (in units `k/v`). None of these reactions
involves a non-clock species as reactant, so the clock coordinate `c` is an autonomous
finite Markov chain. Let `σ` be the time of the first tick from `c = l`, and
`F(t) = P(σ ≤ t)`.

*Lemma 2.1 (A.1–A.2).* `F(t) ≤ 1 − e^{−λt} ≤ λ t` for all `t ≥ 0`.

*Proof.* Let `p_c(t) = P(c(t) = c, σ > t)`. Out-rate at `c` is `r·1{c<l} + f` (up, down or
tick), so `p_c' = r p_{c−1} 1{c ≥ 2} + f p_{c+1} 1{c ≤ l−1} − (r 1{c<l} + f) p_c`. Put
`u_c = p_{c+1} − a p_c` (`1 ≤ c ≤ l−1`), `u_0 := p_1`, `u_l := 0`. A direct computation
(using `r = af` at `c = l−1`, where `p_l' = r p_{l−1} − f p_l`) gives, for `1 ≤ c ≤ l−1`,
`u_c' = f u_{c+1} − (r+f) u_c + r u_{c−1}`. So `u' = G u + r p_1 e_1` with `G` tridiagonal,
off-diagonal entries `f, r ≥ 0`: `G` is Metzler, `e^{tG} = e^{−βt} e^{t(G+βI)} ≥ 0`
entrywise for `β ≥ r+f`, and `u(t) = e^{tG}u(0) + ∫_0^t e^{(t−s)G} r p_1(s) e_1 ds ≥ 0`
because `u(0) = e_{l−1} ≥ 0` (`p(0) = e_l`). Hence `p_c ≥ a^{c−1} p_1`, so
`p_1 ≤ μ Σ_c p_c = μ(1 − F)`. Since `F' = f p_1 ≤ λ(1 − F)`,
`(e^{λt}(1 − F))' ≥ 0` and `F(t) ≤ 1 − e^{−λt}`. ∎

This is the paper's ratio invariant `p_{i+1}/p_i ≥ r/f`, proved by the Metzler property
instead of a boundary-derivative argument.

*Lemma 2.2 (A.3, exact).* `E[σ] = (1/f) Σ_{c=1}^{l} (a^c − 1)/(a − 1)` (`a ≠ 1`). For
`a ≥ 2`, `E[σ] ≤ (a/(a−1))/λ ≤ 2/λ`.

*Proof.* `w(c) = ∫_0^∞ p_c` is finite (finite chain, all states transient). Integrating the
forward equation over `[0, ∞)` gives `(r 1{c<l} + f) w(c) = 1{c=l} + r w(c−1) + f w(c+1)`.
Summing over `c' ≤ c ≤ l−1` gives `f w(c+1) = r w(c) + f w(1)`; summing over all `c` gives
`f w(1) = 1`. So `w(c) = (1/f)(a^c − 1)/(a − 1)` and
`Σ_c w(c) ≤ (1/(f(a−1))) Σ_{c ≤ l} a^c = (a/(a−1))/(fμ)`. ∎

## 3. The network of Fig. 3.2

### 3.1 Fig. 3.2 as drawn

CTM (paper p. 7): finite state set `Q`, instruction `op(i, j, k, z_j, z_k)` for each `i`,
i.e. a total map `δ(i, 0) = (j, z_j)`, `δ(i, 1) = (k, z_k)`. A configuration is `(q, w)`
with `w = w_1…w_s ∈ {0,1}^s`; one step reads `b = w_1` and gives `(q', w_2…w_s z)` with
`(q', z) = δ(q, b)`. Encoding: `val(w) = Σ_{r=1}^{s} (w_r + 1) 3^{s−r}` (digits 1, 2).

Species: `S_{i,z}` (`i ∈ Q`, `z = 1..4`), clock as in §2, `I, I_T, I_M`, memory
`M, M†, M*, T, T†, T*, D, D*, B, B*, K_1, K_2`. Reactions for `op(i, j, k, z_j, z_k)` (Fig.
3.2A, catalysts in brackets, `∅` = none):

| Row | Reactions | Catalyst |
|---|---|---|
| initiation | `C_1 → C_l + I` | `A*` |
| `(i,4)→(i,1)` | `I + S_{i,4} → S_{i,1}`; `S_{i,4} → S_{i,1}` | ∅; `S_{i,1}` |
| `(i,1)→(i,2)` | `I + S_{i,1} → S_{i,2}`; `S_{i,1} → S_{i,2}` | ∅; `S_{i,2}` |
| `(i,2)→(i,3)` | `I + S_{i,2} → S_{i,3}`; `S_{i,2} → S_{i,3}` | ∅; `S_{i,3}` |
| `(i,3)→(j,4)` | `I → I_T`; `I_T + S_{i,3} → S_{j,4}`; `S_{i,3} → S_{j,4}` | `T`; ∅; `S_{j,4}` |
| `(i,3)→(k,4)` | `I → I_M`; `I_M + S_{i,3} → S_{k,4}`; `S_{i,3} → S_{k,4}` | `M`; ∅; `S_{k,4}` |
| restore memory | `M† → M` | `S_{i,2}` |
| compare | `T† → T`; `T + M → T* + M*` | `S_{i,2}`; ∅ |
| restore `D`, `B` | `D* → D`; `B* → B` | `S_{i,2}` |
| restore memory, threshold | `T* → T†`; `M* → M` | `S_{j,4}` or `S_{k,4}` |
| zero out high digit | `D → K_1 + D*`; `D → K_2 + D*`; `K_2 + M → K_1`; `K_1 + M → ∅` | `S_{j,4}`; `S_{k,4}`; ∅; ∅ |
| write low digit | `B → (z_j+1)M + B*`; `B → (z_k+1)M + B*` | `S_{j,4}`; `S_{k,4}` |
| shift | `M → 3M†` | `S_{j,4}` or `S_{k,4}` |

Initial counts (Fig. 3.2B), input `b_1…b_s`: `#M = val(b)`, `#T = 2·3^{s−1} + 2·3^{s−3}`,
`#D = #S_{î,1} = 3^{s−1}`, `#B = 1`, all others 0 (clock: `#C_l = 1`).

**Text versus figure.** p. 8 says "the transition is initiated by a reaction of a state
species with a clock molecule `C_1`"; the figure initiates by `C_1 → C_l + I` (catalyst
`A*`) and lets `I` react with the state species. We follow the figure. This choice matters
for the proof: the tick does not involve any non-clock species, so the clock is autonomous
(§2) and the tick times form a renewal sequence (Lemma 7.1).

Threshold margins (`s ≥ 3`, `T_0 := 2·3^{s−1} + 2·3^{s−3} = 20m/9`). Words with `w_1 = 0`
have `val(w) ≤ 3^{s−1} + 2(3^{s−1} − 1)/2 = 2m − 1`, so `T_0 − val(w) ≥ 2m/9 + 1`. Words with
`w_1 = 1` have `val(w) ≥ 2m + (m−1)/2`, so `val(w) − T_0 ≥ (5m − 9)/18 ≥ 2m/9` (as `m ≥ 9`).
So `|val(w) − T_0| ≥ g := 2m/9` (an integer `≥ 2`), and `val(w) < T_0 ⟺ w_1 = 0`. (3.1)

### 3.2 Three defects

**F3 (the union network is wrong for a non-normalised CTM).** The rows catalysed by
`S_{j,4}` depend on the instruction of the predecessor `i`: which of `K_1`, `K_2` is produced
(the bit read) and which `z` is written. Taking the union of the reaction sets over all
instructions gives a well-defined network, but if `j = δ(i,0)` and `j = δ(i',1)` for some
`i, i'` (including `i = i'`, i.e. `j = k`), or two instructions entering `j` write different
bits, the union contains both `D → K_1 + D*` and `D → K_2 + D*` (or two different writes)
catalysed by `S_{j,4}`, and the amount removed is decided by a race. For a CTM that is first
normalised so that each state records the bit it was entered with and the bit written, the
union is consistent. The repair `U_{q,b}` (microstep-4 species indexed by the transition
`(q, b)`) is this normalisation, restricted to microstep 4.

**F1 (microstep 4 always gives the wrong count).** Assume F3 repaired (so the target `j`
determines `b` and `z`). In microstep 4 the zeroing (`K + M`), the write (`B → (z+1)M`) and
the shift (`M → 3M†`) all act on `M` under the same catalyst.

*Proposition 3.1.* Start microstep 4 of the literal network from the completed microstep-3
state for `(i, w)` (`M + M* = x = val(w)`, `M* = T* = min(x, T_0)`, `D = m`, `B = 1`,
`M† = K_1 = K_2 = 0`) with `b = w_1`, `(j, z) = δ(i, b)` and the intended value
`x' = 3(x − (b+1)m) + (z + 1)` (`= val(w_2…w_s z)`). At every terminal state of the
microstep-4 reactions, `#M† − (#K_1 + 2#K_2) = x' + 2(z+1) + 2(#K_1 + 2#K_2) ≥ x' + 2`.

*Proof.* `V := 3(#M + #M*) + #M† − 3(#K_1 + 2#K_2) − 3(b+1)#D + 3(z+1)#B` is conserved by
every reaction that can fire in microstep 4 (`K_1 + M → ∅`: `−3 + 3`; `K_2 + M → K_1`:
`−3 + 3(2 − 1)`; `D → K_{b+1} + D*`: `+3(b+1) − 3(b+1)`; `B → (z+1)M + B*`: `+3(z+1) −
3(z+1)`; `M → 3M†`, `M* → M`, `T + M → T* + M*`: 0). Initially `V = 3x − 3(b+1)m + 3(z+1)
= x' + 2(z+1)`. At a terminal state `M = M* = D = B = 0`, so `#M† − 3P = x' + 2(z+1)` with
`P = #K_1 + 2#K_2`. ∎

So the memory, even after all pending removals, exceeds the intended value; in particular
`#M† ≡ 0 (mod 3)` while `x' ≡ z + 1 ≢ 0`. Observed: 200 of 200 runs per case wrong
(`s = 3, 4, 5`, simulation script, not in the repository).

**F2 (stray `I`).** `I → I_T` is catalysed by `T` and `I → I_M` by `M`, not by a
microstep-3 species. At the tick that ends microstep 2, `S_{i,2} = m` and (once the
comparison is complete) exactly one of `T`, `M` has count `y = |x − T_0| ≥ 2m/9` by (3.1).
The tick's `I` then reacts first with `T` or `M` with probability exactly
`y/(m + y) ≥ 2/11`. (From the initial state, where `M` and `T` are both present during
microstep 1, the capture probability at tick 1 is `(x + T_0)/(m + x + T_0) > 0.79`.) The
diverted `I_T` (or `I_M`) persists and fires `I_T + S_{i',3} → S_{·,4}` as soon as some
`S_{i',3}` appears. Proposition 3.2 turns this into a proved failure.

*Proposition 3.2 (a capture leads to a wrong state).* Take the network of Fig. 3.2 (or
`N♯` with the paper's reading `I + T → I_T + T`, `I + M → I_M + M`,
`I_T + S_{q,3} → U_{q,0}`, `I_M + S_{q,3} → U_{q,1}` in place of repair 2; read `U_{î,0}` for
`S_{j,4}` below). Start from the initial state with `w_1 = 0`, so `x < T_0`; put
`y = T_0 − x ≥ 2m/9 + 1` and `(j, z) = δ(î, 0)`. The following finite sequence of jumps has
positive probability, and just before each of ticks 1, 2, 3 no non-clock reaction is enabled
(every reaction has completed: the paper's condition for an error-free microstep holds):

1. the comparison `T + M → T* + M*` fires `x` times before tick 1 (from the initial state it
   is the only enabled non-clock reaction; each jump has positive probability against the
   clock), giving `M = 0`, `M* = T* = x`, `T = y`;
2. tick 1, then `I + T → I_T + T` (probability `y/(m + y)`; the other `I`-reaction is
   `I + S_{î,1}`, rate `m`); nothing else is enabled until tick 2 (`I_T` needs `S_{·,3}`);
3. tick 2, then `I + S_{î,1} → S_{î,2}` (probability `m/(m + y)`) and `m − 1` autocatalytic
   steps to `S_{î,2} = m` (the restores have no reactant); this is `𝒦_2` plus one `I_T`;
4. tick 3, then `I + S_{î,2} → S_{î,3}` (probability `m/(m + y)`), and then
   `I_T + S_{î,3} → S_{j,4}` before `S_{î,2} + S_{î,3} → 2S_{î,3}` (rates 1 and `m − 1`,
   no other non-clock reaction enabled: `M = 0` and the restores have no reactant;
   probability `1/m` among them).

The state `Z*` reached has `S_{î,2} = m − 1`, `S_{j,4} = 1`, `S_{î,3} = 0`, no `I`, `I_T`,
`I_M`. *Claim:* until the next tick, `#S_{î,2} = m − 1` and `#S_{j,4} = 1`. Indeed the
reactions that change them are `I + S_{î,2}`, `S_{î,2} + S_{î,3} → 2S_{î,3}`,
`I + S_{j,4}`, `S_{j,4} + S_{j,1} → 2S_{j,1}` (and `S_{î,3} + S_{j,4}`, which needs
`S_{î,3}`); they need `I`, `S_{î,3}` or `S_{j,1}`. These are 0 at `Z*`, `I` is produced only by
a tick, and `S_{î,3}`, `S_{j,1}` only by reactions that themselves need `I`, `S_{î,3}` or
`S_{j,1}`. So before the next tick the state never has a single state species: whatever the tick time, the state just
before tick 4 is in no class `𝒦_·`, i.e. it encodes no CTM configuration. Moreover, from `Z*`
the jumps `M* → M` (catalyst `S_{j,4}`), then repeatedly `M → 3M†` (`S_{j,4}`) and
`M† → M` (`S_{î,2}`), have positive probability, and each `M → 3M†` raises
`#M + #M* + #M†` by 2; so for every `N` the memory exceeds `N` before tick 4 with positive
probability. ∎

So "every microstep completes before the next tick" does not imply a correct step, contrary
to p. 9 ("The only source of error is …"): in the run above all reactions complete before
ticks 1–3, and afterwards no single-state-species configuration is reachable before tick 4.
Observed in simulation: with F1 and F3 repaired and the paper's reading kept, 29 of 30 random runs (3-state CTMs, `s = 3`, ideal schedule: every tick only after all
non-clock reactions have stopped) end in a wrong configuration or in unbounded growth within
15 CTM steps.

### 3.3 The corrected network `N♯(𝒞, l)`

Three repairs; species, schedule and initial counts are otherwise those of Fig. 3.2.

| # | Fig. 3.2 | `N♯` | reason |
|---|---|---|---|
| 1 (F1) | `D → K_{b+1} + D*`, `K + M → ·`, `B → (z+1)M + B*` | `D → 3K_{b+1} + D*`, `K_2 + M† → K_1`, `K_1 + M† → ∅`, `B → (z+1)M† + B*` | zero out and write in post-shift units; no race with the shift |
| 2 (F2) | `I → I_T` (cat. `T`), `I → I_M` (cat. `M`), `I_T`/`I_M + S_{i,3} → S_{·,4}` | `I + S_{q,3} → R_q`, `R_q + T → U_{q,0} + T`, `R_q + M → U_{q,1} + M` | `I` meets only the current state species |
| 3 (F3) | `S_{j,4}` | `U_{q,b}` (transition-indexed microstep-4 species) | determines `b` and the written bit |

and, as in the working note on Theorem 4.1, the leftover threshold is cleared in microstep 4
(`T → T†`, catalyst `U_{q,b}`). This last reaction is not needed for correctness of Theorem
3.2; it makes the terminal state of microstep 4 independent of the branch.

**Definition (`N♯(𝒞, l)`).** For a CTM `𝒞 = (Q, δ)` write `δ(q, b) = (q_b, z_b)`. Species:
`S_{q,1}, S_{q,2}, S_{q,3}, R_q` (`q ∈ Q`), `U_{q,b}` (`q ∈ Q`, `b ∈ {0,1}`), `I`, clock
`C_1..C_l, A, A*`, memory `M, M†, M*, T, T†, T*, D, D*, B, B*, K_1, K_2`. Reactions, all
bimolecular with rate constant `k`:

| Microstep | Reaction(s) (for all `q ∈ Q`, `b ∈ {0,1}`) | Catalyst |
|---|---|---|
| tick | `C_1 + A* → C_l + I + A*`; clock walk of §2 | — |
| 4→1 | `ε_{q,b}: I + U_{q,b} → S_{q_b,1}`; `U_{q,b} + S_{q_b,1} → 2 S_{q_b,1}` | — |
| 1→2 | `I + S_{q,1} → S_{q,2}`; `S_{q,1} + S_{q,2} → 2S_{q,2}` | — |
| 2→3 | `I + S_{q,2} → S_{q,3}`; `S_{q,2} + S_{q,3} → 2S_{q,3}` | — |
| 3→4 | `I + S_{q,3} → R_q`; `R_q + T → U_{q,0} + T`; `R_q + M → U_{q,1} + M`; `S_{q,3} + U_{q,b} → 2U_{q,b}` | (`T`, `M` in the 2nd, 3rd) |
| 2 | `M† → M`, `T† → T`, `D* → D`, `B* → B` | `S_{q,2}` |
| any | `T + M → T* + M*`; `K_2 + M† → K_1`; `K_1 + M† → ∅` | — |
| 4 | `M* → M`, `T* → T†`, `T → T†`, `M → 3M†`, `D → 3K_{b+1} + D*`, `B → (z_b+1)M† + B*` | `U_{q,b}` |

(In the paper's notation `U_{i,0}` is `S_{j,4}` and `U_{i,1}` is `S_{k,4}`.)

Initial state `z_0(w, n_*, a)` for CTM start state `q̂` and tape `w ∈ {0,1}^s`: Fig. 3.2B
(`#M = val(w)`, `#T = T_0`, `#D = #S_{q̂,1} = m`, `#B = 1`), `#C_l = 1`, `#A* = n_*`,
`#A = a·n_*`, all other counts 0. The network depends only on `𝒞` and `l`.

Conservation laws (each reaction checked): `Σ_q (S_{q,1} + S_{q,2} + S_{q,3} + R_q) +
Σ_{q,b} U_{q,b} = m`; `#T + #T* + #T† = T_0`; `#D + #D* = m`; `#B + #B* = 1`; the clock has
one molecule.

## 4. Correctness of the microsteps

Let `x = val(w)`, `b = w_1`, `(q', z) = δ(q, b)`, `w' = w_2…w_s z`, `x' = val(w') =
3(x − (b+1)m) + (z+1)`. "Other state species zero" means all of `S_{·,·}`, `R_·`, `U_{·,·}`
except the one named. Memory class `𝒜(x)`: `#M + #M* + #M† = x`,
`#T + #T* + #T† = T_0`, `#M* = #T*`, `#D + #D* = m`, `#B + #B* = 1`, `#K_1 = #K_2 = 0`.

| Class | State species | Memory | Rest |
|---|---|---|---|
| `𝒦_1(q, w)` | `S_{q,1} = m` | `𝒜(x)` | `I = 0` |
| `𝒦_2(q, w)` | `S_{q,2} = m` | `𝒜(x)`, `M† = T† = D* = B* = 0` | `I = 0` |
| `𝒦_3(q, w)` | `S_{q,3} = m` | as `𝒦_2` and `min(#T, #M) = 0` | `I = 0` |
| `𝒦_4(q, b; w')` | `U_{q,b} = m` | `M† = x'`, `T† = T_0`, `D* = m`, `B* = 1`, all other memory 0 | `I = 0` |

The initial state is in `𝒦_1(q̂, w)` (with `M = x`, `T = T_0`, `D = m`, `B = 1`).
In `𝒦_3`, (3.1) and `𝒜(x)` give `#M* = #T* = min(x, T_0)`, and `#T > 0 ⟺ b = 0`.

The *rest* process is the network without the clock reactions (I is then only consumed).
A *window* starts at a tick, i.e. in `K + {one I}` for a class state `K`.

*Lemma 4.1 (closed targets).* Under the rest dynamics, `𝒦_3` and `𝒦_4` are absorbing (no
non-clock reaction is enabled) and `𝒦_1`, `𝒦_2` are closed (only `T + M → T* + M*` can
fire, and it preserves the class).

*Proof.* With `I = R = 0` and a single state species, no state reaction is enabled
(each needs `I`, `R_q`, or two distinct state species). Catalysed memory reactions need their
catalyst: in `𝒦_1` none (`S_{q,1}` catalyses nothing); in `𝒦_2` the restores have no
reactant; in `𝒦_3` nothing is catalysed by `S_{q,3}` except via `I`; in `𝒦_4` the
reactants `M*, T*, T, M, D, B` are 0. Uncatalysed: `K = 0`; `T + M` is disabled in `𝒦_3`
(`min = 0`) and `𝒦_4` (`M = 0`) and preserves `𝒜` and the extra conditions of `𝒦_2`. ∎

*Lemma 4.2 (window 1→2).* From `𝒦_1(q, w) + I` the rest process stays, until it enters
`𝒦_2(q, w)`, in states where: `I + S_{q,1} → S_{q,2}` fires once (it is the only reaction
using `I`), then only `S_{q,1} + S_{q,2} → 2S_{q,2}` changes state species; the memory
changes only by the four `S_{q,2}`-catalysed restores and `T + M`, which preserve `𝒜(x)`.
It enters `𝒦_2(q, w)` exactly when `S_{q,1} = 0` and `M† = T† = D* = B* = 0`.

*Proof.* `S_{q,3}`, `R`, `U` stay 0: `S_{q,3}` is produced only by `I + S_{q,2}` or
`S_{q,2} + S_{q,3}`; the first needs `I` and `S_{q,2}` together, but `S_{q,2}` first becomes
positive at the reaction that consumes the only `I`. `K` and the producers of `M†, T†, D*, B*`
are catalysed by `U` (0). The restores and `T + M` preserve each equation of `𝒜(x)`. ∎

*Lemma 4.3 (window 2→3).* From `𝒦_2(q, w) + I`: `I + S_{q,2} → S_{q,3}` fires once, then
`S_{q,2} + S_{q,3} → 2S_{q,3}`; `I + S_{q,3} → R_q` never fires (the `I` is gone when
`S_{q,3}` first appears); the restores have no reactant and nothing produces one; `T + M`
runs. The target `𝒦_3(q, w)` is reached exactly when `S_{q,2} = 0` and `min(#T, #M) = 0`. ∎

*Lemma 4.4 (window 3→4).* From `𝒦_3(q, w) + I` the rest process does, in order:
(a) `I + S_{q,3} → R_q` (the only reaction using `I`: the other `I`-reactions need
`S_{·,1}, S_{·,2}, U` = 0); (b) `R_q + T → U_{q,0} + T` if `b = 0`, `R_q + M → U_{q,1} + M`
if `b = 1` (exactly one of `#T, #M` is positive by (3.1), and nothing changes `T` or `M`
before (b): `T + M` is disabled and `U = 0`); (c) `S_{q,3} + U_{q,b} → 2U_{q,b}` until
`S_{q,3} = 0`, together with the `U_{q,b}`-catalysed microstep-4 reactions, `T + M` and the
`K`-reactions; `S_{q,2}`-restores cannot fire (`S_{q,2} = 0`). It is absorbed in
`𝒦_4(q, b; w')`.

*Proof of the last claim.* During (c), `Ψ := 3(#M + #M*) + #M† − (#K_1 + 2#K_2) −
3(b+1)#D + (z+1)#B` is conserved: `M → 3M†`, `M* → M`, `T + M → T* + M*`: 0;
`D → 3K_{b+1} + D*`: `−(−3(b+1)) − 3(b+1) = 0`; `K_2 + M† → K_1`: `−1 − (1 − 2) = 0`;
`K_1 + M† → ∅`: `−1 + 1 = 0`; `B → (z+1)M† + B*`: `(z+1) − (z+1) = 0`. At the start of (c),
`Ψ = 3x − 3(b+1)m + (z+1) = x'`. (This is the `Ψ` of the working note on Theorem 4.1, microstep 4.) The weight
`Φ = 3#T + #T* + #M + 2#M* + 10#D + 3#K_2 + #K_1 + #B` decreases by at least 1 in every
reaction of (c) other than the autocatalysis (`T + M`: `−3 −1 +1 +2`; `M* → M`: `−2 + 1`;
`T → T†`: `−3`; `D → 3K + D*`: `−10 + 3·3` at most; `K_2 + M† → K_1`: `−2`;
`K_1 + M† → ∅`, `B → …`, `M → 3M†`, `T* → T†`: `−1`), so (c) ends after
finitely many reactions in a state where nothing is enabled: `S_{q,3} = 0`, `U_{q,b} = m`,
`M* = T* = T = M = D = B = 0`. If `K_1 + K_2 > 0` there, then `#M† = 0` and
`Ψ = −(#K_1 + 2#K_2) < 0 < x'`, impossible. So `K = 0` and `#M† = Ψ = x'`; the conservation
laws give `T† = T_0`, `D* = m`, `B* = 1`. ∎

*Lemma 4.5 (window 4→1).* From `𝒦_4(q, b; w') + I`: `I + U_{q,b} → S_{q',1}` (`q' = q_b`)
fires once, then `U_{q,b} + S_{q',1} → 2S_{q',1}`; no memory reaction is enabled (all
`U`-catalysed reactions lack reactants, `S_{q',1}` catalyses nothing, `M = K = 0`). It is
absorbed in `𝒦_1(q', w')` (with `M† = x'`, `T† = T_0`, `D* = m`, `B* = 1`). ∎

Hence, writing `c_n = (q_n, w_n)` for the CTM run and `b_n = (w_n)_1`: the window that starts
at tick `j ≥ 1` ends just before tick `j + 1`; on `[0, τ_1)` there is no `I` and the initial
state stays in the closed class `𝒦_1(c_0)`. So **if each window reaches its target before the
next tick, then for `n ≥ 0` the state just before tick `4n + 1` is in `𝒦_1(c_n)`, before
`4n + 2` in `𝒦_2(c_n)`, before `4n + 3` in `𝒦_3(c_n)`, and before `4n + 4` in
`𝒦_4(q_n, b_n; w_{n+1})`**, which encodes `c_{n+1}`: the CTM state is `q_{n+1} = (q_n)_{b_n}`,
read from the index of the present `U_{q_n, b_n}`, and the tape is `w_{n+1}`, read from
`#M† = val(w_{n+1})`. The fate of the tick molecules: each `I` is consumed within its window, by
`ε`, `I + S_{q,1}`, `I + S_{q,2}` or `I + S_{q,3} → R_q`, and `R_q` within window 3→4.

Checked by simulation for random 3-state CTMs (`s = 3`: 40 runs × 15 steps; `s = 4`:
20 runs × 12 steps; ideal schedule, all correct).

## 5. Completion times (Lemmas A.5–A.7 with constants)

`T_j(K)` denotes the hitting time of the target class by the rest process started at
`K + I`, `K` in the source class of window `j` (`j = 2, 3, 4, 1`: window ending microstep
`j`). All bounds are uniform over the class and over `w`.

*Lemma 5.1.* `E[T_1] ≤ (1 + 2H_{m−1})/m ≤ (1 + 2h)/m`.

*Proof.* Lemma 4.5: the first reaction has rate `#U_{q,b} = m` (it is the only enabled
one), then Lemma 1.3(c). ∎

*Lemma 5.2.* `E[T_2] ≤ (1 + 2H_{m−1} + H_{56m/9})/m ≤ (3h + 2.83)/m`.

*Proof.* `I + S_{q,1}` has rate `m` until it fires (Exp(m)); then Lemma 1.3(c) up to the
stopping time `θ` with `S_{q,2} = m`. After `θ` (strong Markov), `Y = #M† + #T† + #D* + #B*`
decreases by 1 at rate `mY` and is never increased (its producers are `U`-catalysed);
Lemma 1.3(a) with `Y(θ) ≤ x + T_0 + m + 1 ≤ (3m−1) + 20m/9 + m + 1 = 56m/9`.
`H_{56m/9} ≤ h + ln(56/9) ≤ h + 1.83`. ∎

*Lemma 5.3.* `E[T_3] ≤ (1 + 2H_{m−1})/m + H_g/g ≤ (6.5h − 5.76)/m`, `g = 2m/9`.

*Proof.* `T_3 ≤ (τ_I + τ_A) + τ_C`, where `τ_I ~ Exp(m)` and `τ_A` (Lemma 1.3(c)) are the
state part, and `τ_C` is the comparison time: in this window only `T + M` changes `T`, `M`,
`#M − #T = x − T_0` is constant with `|x − T_0| ≥ g` by (3.1), so Lemma 1.3(b) gives
`E[τ_C] ≤ H_g/g`. `(9/(2m)) H_{2m/9} ≤ (4.5/m)(h − ln 4.5)`, `4.5 ln 4.5 ≥ 6.76`. ∎

*Lemma 5.4.* `E[T_4] ≤ (10.39 h + 14.45)/m`.

*Proof.* Stages (a), (b) of Lemma 4.4: rates `m` and `≥ g` (the count of `T` or `M`,
unchanged meanwhile), means `1/m` and `1/g = 4.5/m`. Stage (c) up to `θ`, the time
`S_{q,3} = 0`: Lemma 1.3(c), mean `2H_{m−1}/m`. From `θ` on (strong Markov, fresh
random time change) every `U`-catalysed reaction has rate `m` per reactant molecule. The
per-molecule bounds in items 2–5 are computed in the tagged projection of the molecule
(Fact 1.2), restarted at the stated stopping time with fresh Poisson processes, one per lumped
channel of the tagged molecule; maxima over molecules are taken on the fully labelled chain
and bounded by Lemma 1.4, which uses only these per-molecule laws. Let `x_θ` be the state at `θ`; then `#M + #M* ≤ x`, `#T ≤ T̂`, where
`T̂ = 0` if `b = 1` and `T̂ ≤ T_0 − x ≤ 20m/9 − (3m−1)/2 = (13m+9)/18 ≤ m` if `b = 0` (smallest
`x` with `w_1 = 0` is `(3m−1)/2`), and `#T` never increases after `θ`.

1. `D`, `B` (never produced after `θ`): `ζ_{DB}`, extinction of `D + B ≤ m + 1`, Lemma
   1.3(a): mean `≤ H_{m+1}/m ≤ (h + 0.11)/m`.
2. `T` (never produced): in its tagged projection from `θ`, each `T` molecule has the lumped
   channel `T → T†` of rate `m`, so it is gone by `E_i/m` with `E_i ~ Exp(1)` the first point
   of that channel's Poisson process; `ζ_T ≤ max_i E_i/m`, mean `≤ (1 + ln m)/m = h/m` by
   Lemma 1.4 (`#T ≤ m`).
3. The `M`-family (labelled molecules in `M` or `M*`; no new ones after `θ`, since `B`
   now writes `M†`). For molecule `i` let `A_i`, `B_i` be its total time in `M`, in `M*`,
   after `θ`, and `ζ_i = A_i + B_i` its exit time (it exits only by `M → 3M†`). In the tagged
   projection of `i` from `θ`, the lumped channels of `i` are: shift (propensity
   `m·1{i ∈ M}`), pairing with some `T` (`#T·1{i ∈ M} ≤ T̂·1{i ∈ M}`; the `T` partner is not
   tracked), return (`m·1{i ∈ M*}`), driven by independent Poisson processes
   `Y_i^s, Y_i^p, Y_i^r`. The shift fires
   when `m A_i` reaches the first point `E_i` of `Y_i^s`: `A_i = E_i/m`. The number of
   pairings is `≤ P_i := Y_i^p(T̂ E_i/m)`. Molecule `i` exits in state `M`, so all its
   `M*`-sojourns are finished: `m B_i` equals the `N_i`-th point `Γ^r_{N_i}` of `Y_i^r` with
   `N_i ≤ P_i + 1`. So `ζ_i ≤ L̂_i := E_i/m + Γ^r_{P_i+1}/m`. Here `P_i` is geometric:
   `P(P_i = k) = π(1−π)^k`, `π = m/(m + T̂)`, independent of `Y_i^r`, so
   `Γ^r_{P_i+1} ~ Exp(π)`. Hence `P(L̂_i > t) ≤ e^{−mt/2} + e^{−mπt/2} ≤ 2e^{−mπt/2}`, and
   Lemma 1.4 gives `E[ζ_M] ≤ (2/(mπ))(1 + ln(2 n_M))`. For `b = 0`: `π ≥ 1/2`,
   `n_M ≤ x ≤ 2m − 1`: `≤ (4/m)(h + ln 4)`. For `b = 1`: `π = 1`, `n_M < 3m`:
   `≤ (2/m)(h + ln 6)`, smaller. So `E[ζ_M] ≤ (4h + 5.55)/m`.
4. `T*`: molecules present at `θ` or created later by pairings (all created before `ζ_M`);
   at most `#T* + #T ≤ T_0` of them; in its tagged projection restarted at `max(θ,
   creation)` (a stopping time), each leaves `E_j/m` later by its lumped `T* → T†` channel,
   `E_j ~ Exp(1)`. So the `T*` extinction time is `≤ ζ_M + max_j E_j/m`, mean
   `≤ E[ζ_M] + (1 + ln T_0)/m ≤ E[ζ_M] + (h + 0.80)/m` (Lemma 1.4).
5. `K`: at most `3m` molecules ever; each needs at most 2 removals; its removal channel has
   propensity `#M†`. Let `θ' = max(ζ_{DB}, ζ_M)`. After `θ'`, `M = M* = B = 0` stay 0, so
   `#M† = Ψ + (#K_1 + 2#K_2) ≥ x' ≥ (3m−1)/2 =: g'` (all digits of `w'` are `≥ 1`). In the
   tagged projection of a `K`-molecule `i` restarted at `θ'`, its lumped channel "removal by
   some `M†`" (propensity `#M†·1{i is a K}`) has internal time growing at rate `≥ g'`, so `i`
   is gone by `θ' + Γ_{2,i}/g'` (`Γ_{2,i}` = second point of that channel's Poisson
   process; a `K_2` needs two removals, a `K_1` one).
   `P(Γ_2/g' > t) = (1 + g't)e^{−g't} ≤ 2e^{−g't/2}`; Lemma 1.4: mean of the maximum
   `≤ (2/g')(1 + ln 6m) ≤ (4m/(3m−1))(h + ln 6)/m ≤ (1.385 h + 2.49)/m`.

The target is reached at the latest at
`θ + ζ_{DB} + ζ_M + ζ_T + max_j E_j/m + max_i Γ_{2,i}/g'`. Summing (units `1/m`):
`1 + 4.5 + 2h` (before `θ`) `+ (h + 0.11) + (4h + 5.55) + h + (h + 0.80) + (1.385h + 2.49)`
`= 10.385 h + 14.45`. ∎

*Proposition 5.5 (one CTM step).*
`Θ := sup Σ_{j=1}^{4} E[T_j] ≤ (21.9 h + 12.6)/m ≤ 26 h/m` (units `v/k`), using `h > 3.19`
(sum of Lemmas 5.1–5.4: `(2 + 3 + 6.5 + 10.39) h + (1 + 2.83 − 5.76 + 14.45)`).

Monte Carlo (`s = 3..6`, extreme words): observed
`Σ_j E[T_j] ≈ (9.3–11.9) h/m`; every window below its bound; every run ended in the
asserted target state.

## 6. Lemma A.9: TM → CTM

The paper cites Neary–Woods (TR NUIM-CS-2005-TR-12) with a sketch. We do not use the citation;
the lemma is proved here. What the theorem needs, and the paper's use requires implicitly:
**the CTM depends only on the TM** (not on `s_tm`, `Δ`), since the network is fixed before
them; the construction below uses markers, never counters.

**TM.** States `Q_M`, halting set `H ⊆ Q_M`, binary tape (0 = blank), transition
`δ_M(q, a) = (q', z, D)`, `D ∈ {L, R}`, for `q ∉ H` (the paper's `op(i,j,k,z_j,z_k,D)` has
`D` depending on `q` only; this is more general). Input `w_in ∈ {0,1}^n` on cells `1..n`,
head on cell 1, state `q_0`. *Space*: `M` uses space `≤ s_tm` within `t_tm` steps if an
interval `J ⊂ ℤ` of length `≤ s_tm` contains the cells `1..max(n,1)` and all head positions
at times `0..t_tm`. A halted machine stays put (configurations constant after halting).

**Cycle view.** For a cycle length `L ≥ s_tm`, a *cycle configuration* is `(q, u)`,
`u ∈ {0,1}^L`, the tape read clockwise from the head. Step for `q ∉ H`,
`(q', z, D) = δ_M(q, u_1)`: `R`: `u' = u_2…u_L z`; `L`: `u' = u_L z u_2 … u_{L−1}`.

*Lemma 6.1.* Let `M` use space `≤ s_tm ≤ L` within `t_tm` steps, and let `(q_t, a_t, h_t)`
be its configurations. Define `u^{(t)}_j` = the content at time `t` of the unique cell
`r ∈ J` with `r ≡ h_t + j − 1 (mod L)`, or 0 if there is none. Then the cycle run from
`(q_0, u^{(0)})` has configuration `(q_t, u^{(t)})` for all `t ≤ t_tm`.

*Proof.* `r ↦ r mod L` is injective on `J`. Cells outside `J` are blank and never visited
up to `t_tm`. Induction: the head cell `h_t ∈ J` corresponds to `j = 1`; writing `z` at
`h_t` and moving to `h_t ± 1 ∈ J` turns `u^{(t)}` into the cycle step's `u'` (for `R` the
new head is position 2; for `L` it is position `L`, i.e. `h_t − 1 mod L`, which lies in `J`,
so the `0`-or-content convention is consistent). ∎

**The CTM `𝒞(M)`.** Tape `2L` bits: the cycle configuration `(q, u)` is encoded by the
*canonical* CTM configuration `F_m(q)` with tape `1u_1 0u_2 0u_3 … 0u_L` (a marker bit, then
the symbol, per cell). States and `δ_ct(state, read) = (next state, written bit)`:

| State | read 0 | read 1 |
|---|---|---|
| `F_m(q)` | `F_s(q)`, 0 | `q ∈ H`: `F_s(q)`, 1; else `Hd(q)`, 1 |
| `F_s(q)` | `F_m(q)`, 0 | `F_m(q)`, 1 |
| `Hd(q)` (read `a`) | with `(q', z, D) = δ_M(q, a)`: `D = R`: `Mk(q')`, `z`; `D = L`: `Sh_m(q', z)`, `z` | same |
| `Mk(q')` | `Ms(q')`, 1 | `Ms(q')`, 1 |
| `Ms(q')` (read `a`) | `C_m(q')`, `a` | |
| `C_m(q')` | `C_s(q')`, 0 | `Cs(q')`, 0 |
| `C_s(q')`, `Cs(q')` (read `a`) | `C_m(q')`, `a`; resp. `F_m(q')`, `a` | |
| `Sh_m(q', c)` | `Sh_s(q', c)`, 0 | `Se(q', c)`, 1 |
| `Sh_s(q', c)` (read `a`) | `Sh_m(q', a)`, `c` | |
| `Se(q', c)` (read `a`) | `F_m(q')`, `c` | |

At most `14|Q_M|` states; `δ_ct` is total (entries for configurations that never occur are
arbitrary, e.g. `Mk` reading 1).

*Lemma 6.2.* Let `L ≥ 2`. From the canonical configuration of `(q, u)`, `q ∉ H`, the CTM
reaches the canonical configuration of the cycle successor `(q', u')` after exactly
`2L + 2` steps (`D = R`) or `4L` steps (`D = L`), and this is the first later time it is in
a state `F_m(·)` reading 1. For `q ∈ H` it returns to the canonical configuration of `(q, u)`
after `2L` steps.

*Proof.* Pairs `P_1 … P_L` (pair `j` = marker, symbol of cell `j` of `u`), front first.
`F_m(q)` reads marker 1 of `P_1`, keeps it; `Hd(q)` reads `u_1`, writes `z`. Case `R`:
`Mk, Ms` turn `P_2` into `(1, u_2)` (2 steps); `C_m/C_s` copy `P_3 … P_L` (markers 0) and
reach `P_1` (marker 1), where `C_m` writes 0 and `Cs` copies `z` (`2(L−2) + 2` steps); now
`P_2 = (1, u_2)` is at the front and the state is `F_m(q')`. Read from the front:
`1u_2 0u_3 … 0u_L 0z` = canonical of `u_2…u_L z`. Steps `2 + 2 + 2(L−1) = 2L + 2`. Case `L`:
`Sh` copies markers of `P_2 … P_L` (all 0) and shifts symbols by one pair (carry `c`, start
`c = z`): `P_2` gets `z`, `P_j` gets `u_{j−1}`; at `P_1` (marker 1) `Se` replaces `z` by the
carry `u_L` (`2(L−1) + 2` steps); `F_m(q')` copies `P_2 … P_L` (`2(L−1)` steps) and is at
`P_1`. Read from the front: `1u_L 0z 0u_2 … 0u_{L−1}` = canonical of `u_L z u_2 … u_{L−1}`.
Steps `2 + 2(L−1) + 2 + 2(L−1) = 4L` (head pair 2, shift `2(L−1)`, fix at `P_1` 2,
copy `P_2 … P_L` `2(L−1)`; `P_1` is then at the front). In both cases no state `F_m(·)` reads a
1 before the end (the scans run in `C` and `Sh` states). `q ∈ H`: `F_m, F_s` copy every bit. ∎

Checked: 16,112 TM steps of 3,000 random TMs (`|Q_M| ≤ 4`, `L = 2..7`), maximum
`4L` CTM steps per TM step; Lemma 6.1 against an infinite-tape simulator on 3,000 random runs.

*Lemma 6.3 (A.9 as used).* Given `M`, `w_in`, `s_tm`, `t_tm` with space `≤ s_tm` within
`t_tm` steps, and `Δ ≥ 0`, put `L = max(2, s_tm + ⌈Δ/2⌉)`, `s_ct = 2L` and
`t_ct = 4L t_tm = 2 s_ct t_tm`. Then the CTM `𝒞(M)` started from `F_m(q_0)` with tape
`enc(w_in) = 1u_1 0u_2 … 0u_L`, `u = u^{(0)}` of Lemma 6.1 (input bits `w_in` at cycle positions
`1..n`, zeros elsewhere), is after `N(t) ≤ 4L t` steps in the canonical configuration of
`(q_t, u^{(t)})`, for every `t ≤ t_tm`; after halting it stays canonical every `2L` steps.
Moreover `2 s_tm + Δ ≤ s_ct ≤ 2 s_tm + Δ + 2`.

This matches the paper's use: `s_ct = 2s_tm + Δ` (up to the rounding `+1`, `+2`) and
`t_ct = O(t_tm (s_tm + Δ))`, with `m = 3^{s_ct − 1}`; the paper's sketch ("record the current
head position with the marker, then move each tape symbol clockwise by one position") is the
`L`-move above. Decoding: in `𝒦_4(q, b; w')` the CTM state is `q_b` and the base-3 digits of
`#M†` give `w'` (in `𝒦_1(q, w)`: state `q`, digits of `#M + #M* + #M†`); the TM state and
tape are read from the CTM state and the marker.

## 7. Theorem 3.2

*Lemma 7.1 (product structure).* Let `τ_0 = 0 < τ_1 < τ_2 < …` be the tick times.
(a) `(τ_{j+1} − τ_j)_j` are i.i.d. with the law of `σ` (Lemma 2.2). (b) For every `j`,
conditionally on `𝓕_{τ_j}` and on `τ_j < ζ`: the next gap `σ_{j+1}` and the rest process
`R` (non-clock reactions only, started at `X_rest(τ_j)`, which includes the new `I`) are
independent, `σ_{j+1}` has the law of `σ`, and `X_rest(τ_j + t) = R(t)` for `t < σ_{j+1}`.

*Proof.* At `τ_j` the clock is at `C_l`. By the strong Markov property the future is the
chain from `(C_l, X_rest(τ_j))`, which we represent by Fact 1.1 with fresh Poisson
processes. The clock propensities depend only on the clock coordinate (and the constants
`#A, #A*`), so the clock path, hence `σ_{j+1}`, is a function of the clock Poisson processes
alone; this gives (a). Before the next tick the `I`-increment term is zero, so the non-clock
coordinates solve the autonomous rest equation driven by the other Poisson processes, whose
solution is `R`. ∎

**Theorem 3.2′.** Fix a TM `M` and `l ≥ 2`; let `N = N♯(𝒞(M), l)` (§3.3, §6). For every
`δ ∈ (0, 1]`, `Δ ≥ 0`, `s_tm ≥ 1`, `t_tm ≥ 1` and input `w_in` such that `M` uses space
`≤ s_tm` within `t_tm` steps, define `L, s = s_ct, t_ct` as in Lemma 6.3,
`m = 3^{s−1}`, `h = 1 + ln m`,
`λ_0 = δ m/(26 t_ct h)` (units `k/v`),
`n_* = ⌈(2^l − 1) m/(26 h)⌉`, `a = min{a ∈ ℕ, a ≥ 2 : n_* μ_l(a) ≤ λ_0}`,
and start `N` from `z_0(enc(w_in), n_*, a)` with `q̂ = F_m(q_0)`. Then:

(i) with probability `≥ 1 − δ`, for every `N'` with `1 ≤ N' ≤ t_ct` the state just before
tick `4N'` is in `𝒦_4(q_{N'−1}, b_{N'−1}; w_{N'})`, which encodes the CTM configuration
`c_{N'}` after `N'` steps, and for `0 ≤ n < t_ct` the states just before ticks `4n+1`,
`4n+2`, `4n+3` are in `𝒦_1(c_n)`, `𝒦_2(c_n)`, `𝒦_3(c_n)` (the list after Lemma 4.5); in
particular, just before tick `4N(t_tm)` (`1 ≤ N(t_tm) ≤ t_ct`; for a halted machine take a
multiple of `2L`) the network encodes the TM configuration after `t_tm` steps;

(ii) `E[τ_{4 t_ct}] ≤ 208 (3/2)^{l−1} (v/k) t_ct² h/(m δ)
≤ 2746 (3/2)^{l−1} (v/k) s³ t_tm² / (3^s δ)`, with `2s_tm + Δ ≤ s ≤ 2s_tm + Δ + 2`; so
`E[τ_{4t_ct}] = O(v (s_tm + Δ)^3 t_tm^2 / (k 3^{2 s_tm + Δ} δ))`. This bound holds without
conditioning on correctness.

The network depends only on `M` (and `l`); `#A*` depends only on `s`; `#A` on `δ`, `t_tm`,
`s`; the memory counts on the input — the quantifier order of the paper (which also sets
`#A*` from `s_ct` in A.3).

*Proof.* **Step 0 (λ).** Put `λ = n_* μ_l(a)` (units `k/v`). `a` exists since
`μ_l(a) → 0`. Since `δ ≤ 1`, `t_ct ≥ 1`: `λ_0 ≤ m/(26h) ≤ n_* μ_l(2)` (`μ_l(2) = 1/(2^l−1)`).
If `a = 2` then `λ = λ_0`. If `a ≥ 3` then `n_* μ_l(a−1) > λ_0` and, from
`1/μ_l(a) = Σ_{j<l} (a/(a−1))^j (a−1)^j ≤ (a/(a−1))^{l−1}/μ_l(a−1)`,
`λ ≥ ((a−1)/a)^{l−1} λ_0 ≥ (2/3)^{l−1} λ_0`. So `(2/3)^{l−1} λ_0 ≤ λ ≤ λ_0`.

**Step 1 (error per window; replaces A.8).** For `j ≥ 1` let `G_j` be the event that the
states just before ticks `1..j` are in their classes (the list after Lemma 4.5) and
`τ_j < ζ`. `G_1` has probability 1: on `[0, τ_1)` there is no `I`, the initial state is in
the closed class `𝒦_1(c_0)` with bounded counts (Lemma 4.1), so there is no explosion. For
`j ≥ 1`, on `G_j`, `X(τ_j)` is a class state plus one `I`, and by Lemma 7.1 the window succeeds iff `σ_{j+1} > T(R)`, where
`T(R)` is the hitting time of the target class by `R` (Lemma 4.1: the target is closed, so
`R(σ_{j+1}−)` is in it; and before `T(R)` the counts are bounded, so no explosion). By
independence and Lemma 2.1,
`P(G_j \ G_{j+1} | 𝓕_{τ_j}) = E[F(T(R))] ≤ λ E[T(R)]` on `G_j`.

**Step 2 (total error).** The windows needed are those starting at ticks
`j = 1, …, 4t_ct − 1`: for each `n < t_ct` the windows from ticks `4n+1`, `4n+2`, `4n+3`
(ending microsteps 2, 3, 4 of step `n`) and, for `n < t_ct − 1`, the window from tick
`4n+4` (ending microstep 1 of step `n+1`). Grouping them by `n` (at most one window of each
type per group) and using Proposition 5.5: `P(G_{4t_ct}^c) ≤ Σ_{j=1}^{4t_ct−1}
P(G_j \ G_{j+1}) ≤ Σ_{n < t_ct} λ Θ ≤ t_ct λ (26 h/m) ≤ t_ct λ_0 (26 h/m) = δ`. On `G_{4t_ct}` the classes are as stated (§4), and Lemma 6.3 translates to the TM.

**Step 3 (time).** The configuration after `t_ct` steps is present just before tick `4t_ct`
(item (i)), so `τ_{4t_ct}` is the completion time. By Lemma 7.1(a) and Lemma 2.2 (`a ≥ 2`),
`E[τ_{4t_ct}] = 4 t_ct E[σ]
≤ 4 t_ct · 2/λ ≤ 8 (3/2)^{l−1} t_ct/λ_0 = 208 (3/2)^{l−1} t_ct² h/(m δ)`. With `t_ct = 2 s
t_tm`, `m = 3^s/3`, `h = 1 + (s−1) ln 3 ≤ 1.1 s`: `≤ 208·4·3·1.1 (3/2)^{l−1} s³ t_tm²/(3^s
δ) ≤ 2746 (3/2)^{l−1} s³ t_tm²/(3^s δ)`. Finally `3^s ≥ 3^{2 s_tm + Δ}` and
`s ≤ 2s_tm + Δ + 2 ≤ 4(s_tm + Δ)`. ∎

**Comparison with the paper.** Paper: per-microstep error `ε` needs
`λ = Θ(ε^{3/2} k 3^{s}/(v s))` (Chebyshev with variances) and total
`O(v (s_tm+Δ)^{7/2} t_tm^{5/2}/(k 3^{2s_tm+Δ} δ^{3/2}))`. Here the error per window is
`≤ λ E[T]` by independence of the clock (Lemma 7.1; every window starts with the clock at
`C_l`, so the "memoryless" remark after Lemma A.3 is not needed), giving `λ = Θ(ε k m/(v h))`
and a bound smaller by the factor `Θ(((s_tm + Δ) t_tm/δ)^{1/2})`. Parameters: here
`#A* = n_* = Θ(3^s/s)` and `a = #A/#A*` satisfies `a^{l−1} = Θ_l(t_ct/δ)` (from
`n_* μ_l(a) ≈ λ_0` and `μ_l(a) ∈ [a^{1−l}/2, a^{1−l}]`), so
`#A = Θ_l((3^s/s)(t_ct/δ)^{1/(l−1)})`; the paper takes `#A*^l = Θ(3^s/s)`,
`#A^{l−1} = Θ(ε^{−3/2})`. With our choice `#A` can exceed `m` (for `l = 2` by the factor
`Θ(t_ct/(δ s))`), so the paper's remark that `m` dominates the total molecular count (end of
A.3) does not transfer; that remark is not part of Theorem 3.2 and is not checked here.

## 8. What remains, and relation to other notes

- **OPEN: none for Theorem 3.2′.** The construction of Fig. 3.2 is incorrect (Propositions
  3.1, 3.2); Theorem 3.2, an existence statement, holds via the repaired network `N♯`
  (Theorem 3.2′). Not proved here: that the drawn network violates the error bound for every
  `#A`; that would also need lower bounds on the probability of the other failure paths.
- Assumptions used and stated: the kinetics model (§1.1, Facts 1.1–1.2, standard); `s_ct ≥ 3`
  (ensured by `L ≥ 2`); the figure's tick (not the text's).
- Non-explosion of the whole network is not needed: explosion is counted as failure in
  Step 1 and never happens before a window's target is reached; the time bound uses the clock
  only.
- `FIX3-SCWB.md` §4 (sketch) is superseded; its independence argument is Step 1 here, now
  with Lemma 2.1 proved.
- A separate working note on Theorem 4.1 (not published) finds the same defects F1–F3 and
  repairs 1–3, checked independently here (Proposition 3.1; the F2 run; Lemmas 4.2–4.5).

The simulation scripts used for the observations above are not in the repository.

## 9. Review response

Independent review (not published; verdict: proof holds; findings E1, G1–G4), resolved as follows.

| Item | Resolution |
|---|---|
| E1 (tick/class indexing off by one) | §4 (list after Lemma 4.5), Theorem 3.2′(i), Steps 1–3 relabelled: just before tick `4n+1, 4n+2, 4n+3` the state is in `𝒦_1(c_n), 𝒦_2(c_n), 𝒦_3(c_n)`; just before tick `4n+4` it is in `𝒦_4(q_n, b_n; w_{n+1})`, which encodes `c_{n+1}` (state from the index of `U`, tape from `#M†`). Windows start at ticks `j ≥ 1`; `G_1` holds a.s.; the error sum runs over the windows from ticks `1..4t_ct−1` (at most one of each type per CTM step); §6 decoding updated. The completion time is still `τ_{4t_ct}`, so the constant 208 is unchanged. |
| G1 (pairing representation in Lemma 5.4) | Fact 1.2 now defines the tagged projection (one tagged molecule, lumped channels such as "`i` pairs with some `T`", untagged remainder), justified by Dynkin's criterion; Lemma 5.4 states that items 2–5 use the tagged projection of each molecule restarted at a stopping time, and that maxima are taken on the fully labelled chain via Lemma 1.4, which needs only per-molecule laws (no independence). Items 2 and 4 now quote Lemma 1.4 (same constants). |
| G2 (capture ⇒ error only simulated) | New Proposition 3.2: an explicit positive-probability jump sequence from the initial state (`w_1 = 0`) in which all reactions complete before ticks 1–3, the tick-1 `I` is captured as `I_T`, and at tick 3 `I_T + S_{î,3} → S_{j,4}` fires first (probability `1/m`); from there `S_{î,2} = m−1` and `S_{j,4} = 1` are frozen until the next tick (proved), so the state before tick 4 is in no class, and the memory can be driven above any bound by `M → 3M†`/`M† → M` cycles. Simulation kept as supporting evidence. |
| G3 (F3 overstated) | F3 restated: the union network is well defined but wrong for a non-normalised CTM; normalising (each state records the bit read and written; `U_{q,b}` does this for microstep 4) removes it. |
| G4 ("Theorem 3.2 is false") | Replaced in the status table and §8: the construction of Fig. 3.2 fails; Theorem 3.2 holds via `N♯`; what is not proved about the drawn network is stated. |
| Review remark: capture probability from the initial state `> 0.79` | Added to F2. |
