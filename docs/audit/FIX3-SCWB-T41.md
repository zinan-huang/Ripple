# Soloveichik–Cook–Winfree–Bruck, Theorem 4.1 — an explicit network and its proof

Paper: Soloveichik, Cook, Winfree, Bruck, "Computation with
finite stochastic chemical reaction networks", Caltech TR etr085v2,
Section 4, Appendix A.5, footnote 5, Fig. 3.2. Companion of `docs/audit/FIX3-SCWB.md` (cited as
"FIX3 §k"). Mathematics only; no Lean.

The paper gives no network for Theorem 4.1, only modifications of Fig. 3.2. This note writes one
down (§3–§5), records every place where the paper is ambiguous or wrong and the choice made (§2,
§6), states the theorem the network satisfies (§7) and gives the proof outline with the error
budget (§8–§10). §12–§15 (2026-11-09) close the items left open there: the TM-to-xCTM
simulation (Lemma X), the completion-time lemma with `C₀ = 16`, the time part, and the error
budget with explicit constants; §16 lists what is still not claimed, §17 answers the cold
review (`FIX3-SCWB-T41-REVIEW.md`), §18 is the changelog.
Status labels as in FIX3: PROVED, SKETCH, OPEN.

| Item | Here | Status |
|---|---|---|
| Network `N(𝒞)` (species, reactions, catalysts) | §3 | given in full |
| Initial state `z₀(δ, s₀, w₀)` | §4 | given in full |
| Clean configurations, extension epochs | §5 | given in full |
| Logic: every window ends in the next clean configuration | §8.1 | PROVED (plus random-order simulation) |
| One-window error bound | §8.2 | PROVED from FIX3 Lemmas 2.1–2.3 (C_b form) plus Lemma 8.3 |
| Microstep completion time `τ̄ ≤ C₀(s + ln(α+2))/d`, `C₀ = 16` | §8.4, §13 | PROVED |
| Error budget, choice of `i₀` | §9, §15 | PROVED: `P(Err) ≤ 1344/(i₀−1)²` |
| Time bound (Theorem 7.2) | §10, §14 | PROVED, explicit constants |
| TM → extensible CTM (Lemma A.9 with tape extension) | §1, §12 | PROVED (Lemma X) |

## 1. Machine model: extensible clockwise TM (xCTM)

An **xCTM** is `𝒞 = (Q, q̂, Q_R, Q_E, Q_H, δ, wr, nx)` with `Q = Q_R ⊔ Q_E ⊔ Q_H` finite (read,
extension and halting states), start `q̂ ∈ Q`, `δ, wr : Q_R × {0,1} → Q, {0,1}`, `nx : Q_E → Q`.
A configuration is `(q, w)`, `w = w₁…w_s ∈ {0,1}^s`, the circular tape read clockwise from the
head (`w₁` is under the head). One step:

- read `q ∈ Q_R`: `(q, b·u) ↦ (δ(q,b), u·wr(q,b))` (read `b`, write `wr(q,b)` in that cell, move
  clockwise);
- extension `e ∈ Q_E`: `(e, w) ↦ (nx(e), w·0)` (insert a blank cell between `w_s` and `w₁`, i.e.
  just behind the head; the head does not move);
- halt `h ∈ Q_H`: no step.

The paper's `op(i, j, k, z_j, z_k)` is the read step with `δ(i,0) = j`, `wr(i,0) = z_j`,
`δ(i,1) = k`, `wr(i,1) = z_k`. Write `(q_n, w_n)` for the configuration after `n` steps,
`s_n = |w_n|` (so `s_n ≤ s₀ + n`).

**Lemma X (PROVED in §12; replaces Lemma A.9 for unbounded space).** For every binary TM `𝓜`
with a two-way infinite tape there is an xCTM `𝒞(𝓜)`, depending on `𝓜` alone, and an input
encoding such that for inputs of length `≤ s_tm0` the initial xCTM tape has length
`s₀ = 2 s_tm0 + 2`. A run of `𝓜` with `t` steps whose visited interval (with `[1, s_tm0]`)
has length `s_tm` is simulated by `N_t ≤ (6 s_tm + 6) t` steps of `𝒞` with tape length
`≤ 2 s_tm + 2`, and `𝒞` halts iff `𝓜` halts. Exact step counts per TM step are in §12. Two
xCTM cells per TM cell (head marker, symbol) plus one seam pair between the rightmost and
leftmost visited TM cells; a move onto an unvisited cell, on either side, inserts two cells
next to the seam. Lemma A.9 itself is only cited in the paper (from Neary–Woods, without
extension).

## 2. Defects of Fig. 3.2 found here (they also affect Theorem 3.2)

Fig. 3.2 as printed (transcribed from p. 8 of the PDF) has three defects. A randomized check
confirms the first two: firing reactions in propensity-weighted random order and ticking only
when no non-clock reaction is enabled, which is the best case for the paper. The script is not in
the repository.

**F1 (microstep 4 is not deterministic).** In microstep 4 the same species `S_{j,4}`
catalyses the zero-out (`D → K₁ + D*`, `K₂ + M → K₁`, `K₁ + M → ∅`), the write
`B → (z+1)M + B*` and the shift `M → 3M†`. The written `M` is then always shifted (the
microstep is complete only when `#M = 0`), so the new low digit lands at position 1. The
`K + M` removals race with the shift, and the `K`'s that survive remove post-shift units after
`M† → M` in microstep 2. In 40 of 40 random runs (s = 4) the result differed from
`val(w₂…w_s z)`. This defect is fatal even with no clock error.

**F2 (stray `I`).** `I → I_T` (catalyst `T`) and `I → I_M` (catalyst `M`) are enabled in every
microstep. At the tick that ends microstep 2, one of `T`, `M` has an excess of at least
`(2/9)·3^{s−1}` molecules against `3^{s−1}` state molecules. At the ticks that end microsteps 4
and 1, the leftover `T` from a bit-0 read is still present. So with constant probability the
`I` becomes an `I_T`/`I_M` molecule that persists until the next microstep 3 and forces
`(i,3) → (j,4)` or `(k,4)` regardless of the bit read there. With F1 repaired, 26 of 30 random
7-step runs left the CTM run.

**F3 (`S_{j,4}` underdetermined).** `S_{j,4}` chooses the zero-out amount (`K₁` or `K₂`) and
the written digit `z_j`. If state `j` is the bit-0 target of one state and the bit-1 target of
another (or two predecessors write different bits), both are catalysed. Fix: index the
microstep-4 species by the transition `(q, b)`.

Known before (FIX3 §4): the text on p. 8 says a state species reacts with `C₁`; the figure has
`C₁ → C_l + I` catalysed by `A*`. We follow the figure.

## 3. The network `N(𝒞)` (clock length `l = 5`)

All reactions are bimolecular with two distinct reactant species. All rate constants equal `k`.
"`X → Y` cat `Z`" means `X + Z → Y + Z`.

### 3.1 Species

| Group | Species | Number |
|---|---|---|
| state, microsteps 1–3 | `S_{q,1}` (`q ∈ Q`), `S_{q,2}`, `S_{q,3}` (`q ∈ Q_R ∪ Q_E`) | `|Q| + 2|Q_R| + 2|Q_E|` |
| reader (replaces `I_T`, `I_M`) | `R_q` (`q ∈ Q_R`) | `|Q_R|` |
| state, microstep 4, read | `U_{q,b}` (`q ∈ Q_R`, `b ∈ {0,1}`; the paper's `S_{δ(q,b),4}`) | `2|Q_R|` |
| state, microstep 4, extension | `X_e` (`e ∈ Q_E`) | `|Q_E|` |
| transition signal | `I` | 1 |
| memory | `M, M†, M*, T, T†, T*, D, D*, K₁, K₂, B, B*` | 12 |
| clock | `C₁,…,C₅, A, A†, A*, A*†` | 9 |

Total: `6|Q_R| + 4|Q_E| + |Q_H| + 22` species.

### 3.2 Reactions

**Clock** (Fig. 3.1B plus footnote 5; 18 reactions). For `1 ≤ c ≤ 4`:
`C_c + A → C_{c+1} + A`, `C_c + A† → C_{c+1} + A†`,
`C_{c+1} + A* → C_c + A*`, `C_{c+1} + A*† → C_c + A*†`. Tick:
`C₁ + A* → C₅ + I + A*`, `C₁ + A*† → C₅ + I + A*†`.

**Uncatalysed memory reactions** (3): `T + M → T* + M*`, `K₂ + M† → K₁`, `K₁ + M† → ∅`.

**Per read state `q ∈ Q_R`** (31 reactions). Write `q_b = δ(q,b)`, `z_b = wr(q,b)`.

| Microstep | Reaction | Catalyst | Function |
|---|---|---|---|
| 1→2 | `I + S_{q,1} → S_{q,2}`; `S_{q,1} + S_{q,2} → 2S_{q,2}` | — | transition |
| 2→3 | `I + S_{q,2} → S_{q,3}`; `S_{q,2} + S_{q,3} → 2S_{q,3}` | — | transition |
| 3→4 | `I + S_{q,3} → R_q` | — | start read |
| 3→4 | `R_q + T → U_{q,0} + T`; `R_q + M → U_{q,1} + M` | (T, M) | read high bit |
| 3→4 | `S_{q,3} + U_{q,b} → 2U_{q,b}` (b = 0, 1) | — | transition |
| 4→1 | `I + U_{q,b} → S_{q_b,1}`; `U_{q,b} + S_{q_b,1} → 2S_{q_b,1}` (b = 0, 1) | — | transition |
| 2 | `M† → M`, `T† → T`, `B* → B` | `S_{q,2}` | restore |
| 2 | `D* → D + A` | `S_{q,2}` | restore `D`; `#A += 3^{s−1}` |
| 2 | `A† → 3A`, `A*† → 3A*` | `S_{q,2}` | second half of tripling (idle unless the previous step extended) |
| 4 | `M* → M`, `T* → T†`, `T → T†` | `U_{q,b}` | restore after the comparison |
| 4 | `M → 3M†` | `U_{q,b}` | shift |
| 4 | `D → 3K_{b+1} + D*` | `U_{q,b}` | zero out high digit `b+1`, in post-shift units |
| 4 | `B → (z_b + 1) M† + B*` | `U_{q,b}` | write the new low digit, post-shift |

**Per extension state `e ∈ Q_E`** (22 reactions), `e' = nx(e)`:

| Microstep | Reaction | Catalyst | Function |
|---|---|---|---|
| 1→2, 2→3 | as for read states (4 reactions) | — | transition |
| 3→4 | `I + S_{e,3} → 3X_e`; `S_{e,3} + X_e → 4X_e` | — | transition, triples the state count |
| 4→1 | `I + X_e → S_{e',1}`; `X_e + S_{e',1} → 2S_{e',1}` | — | transition |
| 2 | the six microstep-2 reactions of a read state | `S_{e,2}` | as above |
| 4 | `M* → M`, `M → 3M†`, `B → M† + B*` | `X_e` | `M ↦ 3M + 1` (append blank cell) |
| 4 | `T* → 3T†`, `T → 3T†` | `X_e` | triple threshold |
| 4 | `D → 3D*` | `X_e` | triple `D` |
| 4 | `A → A†`, `A* → A*†` | `X_e` | first half of tripling `A`, `A*` |

**Halting states** have no reactions. `S_{h,1}` catalyses nothing, and the `I` produced by
later ticks has no partner.

Total: `31|Q_R| + 22|Q_E| + 21` reactions. Among the state species, only `S_{·,2}`, `U_{·,·}`
and `X_·` catalyse anything (outside the state species, `T` and `M` catalyse the read
`R_q + T → U_{q,0} + T`, `R_q + M → U_{q,1} + M`, and `A, A†, A*, A*†` catalyse the clock).
`S_{·,1}` and `S_{·,3}` catalyse nothing, so microsteps 1 and 3 are buffers. The cyclic
pairs `M → 3M†`/`M† → M`, `T* → T†`/`T† → T`, `D → ·D*`/`D* → D`, `B → B*`/`B* → B` and
`A → A†`/`A† → 3A` are all split between microsteps 4 and 2, which are never adjacent.

## 4. Initial state

Parameters: input tape `w₀ ∈ {0,1}^{s₀}` with `s₀ ≥ 3`, and the accuracy index `i₀ ∈ ℕ`. Put
`d₀ = 3^{s₀−1}`, `val(w) = Σ_{p=1}^{s} (w_p + 1) 3^{s−p}` and `θ(s) = 2·3^{s−1} + 2·3^{s−3}`.

`z₀(i₀, w₀)`: `S_{q̂,1} = d₀`, `M† = val(w₀)`, `T† = θ(s₀)`, `D* = d₀`, `B* = 1`,
`A = i₀ d₀`, `A* = d₀`, `C₅ = 1`; every other species 0.

Theorem 7.1 takes `i₀ = i₀(δ, s₀) = max(s₀, 1 + ⌈37/√δ⌉)`; here `37 ≥ √(84 C₀)` with
`C₀ = 16` the constant of Lemma 8.4 (§13, §15). Only `A` depends on `δ`. Only `M†` depends on the input. Everything else depends on
`s₀` alone, which is fixed by the input-size bound (`s₀ = 2 s_tm0 + 2`, Lemma X).

## 5. Schedule: windows, clean configurations, extension epochs

**Windows.** Tick `k` is the `k`-th firing of a tick reaction. Window `k` is the stretch between
tick `k` and tick `k+1`; window 0 runs from time 0 to tick 1. CTM step `n` occupies windows `4n`
(microstep 1), `4n+1` (μ2), `4n+2` (μ3) and `4n+3` (μ4). The **work state** is the configuration
without the clock species `C₁, …, C₅` (the species `A, A†, A*, A*†`, listed with the clock in
§3.1, belong to the work state: `a(x)`, `f(x)` in §8.2 are functions of it, and the A-data are
part of `Γ_k`). **Work reactions** are all reactions except the 16 clock moves and
the 2 ticks.

**Clean configurations.** Write `d_n = 3^{s_n−1}` and `α_n = i₀ + n`. `Γ_k` is the work state
at the end of window `k`; `I`, `R`, `K₁`, `K₂` are 0 in every `Γ_k`. For a halting `q_n`, `Γ_k =
Γ_{4n}` for all `k ≥ 4n` (up to idle `I`'s). The A-data columns give the counts of
`A, A†, A*, A*†`.

| Window | State species | Memory | A-data |
|---|---|---|---|
| `4n` (end μ1) | `S_{q_n,1} = d_n` | `M† = val(w_n)`, `T† = θ(s_n)`, `D* = d_n`, `B* = 1` | `(α_n d_n, 0, d_n, 0)`; if `q_{n−1} ∈ Q_E`: `(0, α_n d_n/3, 0, d_n/3)` |
| `4n+1` (end μ2) | `S_{q_n,2} = d_n` | with `v = val(w_n)`, `c = min(v, θ(s_n))`: `M = v−c`, `M* = c`, `T = θ(s_n)−c`, `T* = c`, `D = d_n`, `B = 1` | `((α_n+1) d_n, 0, d_n, 0)` |
| `4n+2` (end μ3) | `S_{q_n,3} = d_n` | as `4n+1` | as `4n+1` |
| `4n+3` (end μ4), `q_n ∈ Q_R`, `b = (w_n)₁` | `U_{q_n,b} = d_n` | `M† = val(w_{n+1})`, `T† = θ(s_n)`, `D* = d_n`, `B* = 1` | `((α_n+1) d_n, 0, d_n, 0)` |
| `4n+3`, `q_n ∈ Q_E` | `X_{q_n} = 3d_n` | `M† = 3 val(w_n) + 1 = val(w_{n+1})`, `T† = θ(s_n+1)`, `D* = 3d_n`, `B* = 1` | `(0, (α_n+1) d_n, 0, d_n)` |

`z₀` is `Γ₀` with `C₅ = 1`. The table is consistent across windows: after an extension step,
`d_{n+1} = 3d_n` and `α_{n+1} d_{n+1}/3 = (α_n+1) d_n`.

**Extension epochs.** Space extension happens exactly in the CTM steps with `q_n ∈ Q_E`:

1. Window `4n+3`: the transition `I + S_{e,3} → 3X_e`, `S_{e,3} + X_e → 4X_e` triples the
   state count. `X_e` then performs `M ↦ 3M + 1` (through `M†`), `T ↦ 3T`, `D ↦ 3D` and the
   first half of the tripling, `A → A†`, `A* → A*†`.
2. Window `4(n+1)` (μ1 of the next step): `X_e` hands over to `S_{e',1}` with count `d_{n+1}`.
   There are no memory reactions.
3. Window `4(n+1)+1` (μ2): `A† → 3A`, `A*† → 3A*` (second half) and the per-step
   `D* → D + A` (adds `d_{n+1}`).

Every step, extension or not, adds exactly `d_n` molecules of `A` in its μ2. So at the start of
step `n` the clock ratio is `(#A + #A†)/(#A* + #A*†) = α_n = i₀ + n`, the effective `A*` count
is `d_n` (`d_n/3` right after an extension), and the tape length satisfies `s_n ≤ s₀ + n`. This
realises A.5's `#A = Θ((i₀+i)3^{s_ct})`, `#A* = Θ(3^{s_ct})`, tripling at extension and
`+Θ(3^{s_ct})` per step, with exact constants.

## 6. Choices and paper inconsistencies

| # | Paper | Here | Why |
|---|---|---|---|
| 1 | Fig. 3.2 microstep 4: zero-out, write, shift all on `M` (F1) | zero-out and write act on `M†`: `D → 3K_{b+1} + D*`, `K + M† → ·`, `B → (z+1)M† + B*` | makes the outcome independent of order; it is the smallest change that does |
| 2 | `I → I_T` cat `T`, `I → I_M` cat `M` (F2) | `I + S_{q,3} → R_q`, `R_q + T → U_{q,0} + T`, `R_q + M → U_{q,1} + M` | `I` reacts only with the current state species |
| 3 | `S_{j,4}` indexed by target state (F3) | `U_{q,b}` indexed by transition | determines `K_{b+1}` and `wr(q,b)` |
| 4 | leftover `T` after the comparison stays `T` | `T → T†` (read), `T → 3T†` (extension) cat μ4 species | needed for extension (otherwise the leftover `T` escapes tripling); gives a unique `Γ_k` |
| 5 | Sec. 4: "triples … state species, `M`, `T`, `D`, and `P`" | `P` is not defined anywhere in the paper; we triple state, `T`, `D`, `A`, `A*`; `B` stays 1 | `B` is the one-shot writer |
| 6 | tripling `M` | `M ↦ 3M + 1` | `3M` has low digit 0, outside the `{1,2}` encoding; `+1` is a blank cell |
| 7 | when and where the tape grows: unspecified | `ext` instruction of the xCTM (§1), cell inserted behind the head | `M ↦ 3M+1` inserts exactly there; Lemma X uses it |
| 8 | tripling of state species: no mechanism | in the 3→4 transition: `I + S_{e,3} → 3X_e`, `S_{e,3} + X_e → 4X_e` | exact, and no extra microstep |
| 9 | "`A → A†`, `A† → 3A` cat different state species in two non-consecutive microsteps"; `A*` also tripled, no mechanism | `A → A†`, `A* → A*†` cat `X_e` (μ4); `A† → 3A`, `A*† → 3A*` cat every `S_{q,2}` (μ2) | μ4 and μ2 are not adjacent, so there is no runaway; the μ2 reactions are idle unless an extension just happened |
| 10 | footnote 5: clock reactions also catalysed by intermediates | up by `A, A†`; down and tick by `A*, A*†` | effective counts `#A + #A†` and `#A* + #A*†` never decrease |
| 11 | "increase `#A` by `Θ(3^{s_ct})` every step" | `D* → D + A` cat `S_{q,2}` (exactly `d_n`) | reuses `D`, so no new species |
| 12 | initial `M, T, D, B` unstarred (Fig. 3.2B) | starred (`M†, T†, D*, B*`) | `z₀ = Γ₀`, uniform invariant. Unproved remark, not used: the paper's unstarred version is not analysed here (with `M`, `T` unstarred, window 0 runs the comparison while the clock runs, so `ε₀ ≠ 0`, and the A-data shift by one step) |
| 13 | `#T = 2·3^{s−1} + 2·3^{s−3}` needs `s ≥ 3` | `s₀ ≥ 3` | — |
| 14 | A.5: `λ = Θ(kε^{3/2}3^{s}/(v s))` "achieved" by `l=5`, `#A=Θ((i₀+i)3^s)` | the requirement is `λ ≤`, not `Θ` | with `i₀ ≥ s_ct0` the inequality holds since `s ≤ s_ct0 + i` |
| 15 | per-microstep error by Chebyshev (A.8) | `μ_l(b)·F·E[τ]` (§8.2) | FIX3 §4 already improves A.8 this way; here the clock rates may change inside a window |
| 16 | Sec. 4/A.5: `i₀ = Θ(1/δ + s_ct0)` | `i₀ = max(s₀, 1 + ⌈37/√δ⌉)` | per-step error `≤ 168 C₀/(i₀+n)³` (§15); the paper's `i₀` also works |

Footnote 10 (conditioning on overall correctness costs at most a factor `1/(1−δ)`) checks out: on
a correct window the post-tick state is the deterministic `Γ_k + I` with clock at `C₅`. So by the
strong Markov property the future is independent of the window's duration.

## 7. Statement

**Theorem 7.1 (Theorem 4.1′, error part).** Let `𝒞` be an xCTM and `N(𝒞)` the network of §3.
Let `C₀ = 16` (Lemma 8.4, §13). For every `s₀ ≥ 3`, every `w₀ ∈ {0,1}^{s₀}`, every
`δ ∈ (0,1]` and every integer `i₀ ≥ max(s₀, 1 + 37/√δ)`, take the jump chain of `N(𝒞)` from
`z₀(i₀, w₀)` and let `Err` be the event that some tick fires while the work state is not
terminal (§8.1). Then:

(i) `P(Err) ≤ 84 C₀/(i₀ − 1)² = 1344/(i₀ − 1)² ≤ δ` (§15);

(ii) on `Err^c`, for every `k ≥ 0`, the work state just before tick `k+1` is `Γ_k` (§5). In
particular, for every `n` up to halting, the state species after step `n` is `S_{q_n,1}` and
`#M† = val(w_n)` with `|w_n| = s_n`. If `𝒞` halts at step `N`, then from window `4N` on the
configuration is frozen at `Γ_{4N}` (memory and `S_{h,1}`).

(i) and (ii) hold for every volume function `v : ℕ^S → (0, ∞)`. Every reaction is bimolecular,
so all propensities carry the common factor `k/v(z)`, and the jump chain does not depend on `v`.

**Quantifier order.** `∀𝒞 ∃N(𝒞) ∀s₀ ∀w₀ ∀δ`, with the initial state `z₀` the only thing that
depends on `δ`, and only through `#A = i₀(δ, s₀)·3^{s₀−1}`. The network is independent of `δ`,
the input and the input size, as the paper claims ("for any TM there is an SCRN such that for
any δ … and any bound `s_tm0` … there is an initial amount of A"). The `A` amount depends on
`(δ, s₀)` only, hence on `(δ, s_tm0)` and not on the input itself.

**Theorem 7.2 (time part, PROVED in §14).** Let `v(z) = |z|/ρ_v`, where `|z|` is the total
molecule count, and let `δ < 1` in Theorem 7.1. Let `τ_{4n}` be the time of tick `4n`, and let
`n ≤ N` (`N` the halting step of `𝒞`, or any `n` if `𝒞` does not halt). Then
`E[τ_{4n} | Err^c] ≤ 92 n (i₀ + n)^5/((1−δ) ρ_v k)`. With Lemma X (`n = N_{t_tm} ≤
6(s_tm + 1) t_tm`, `s₀ = 2 s_tm0 + 2`, `i₀ = max(s₀, 1 + ⌈37/√δ⌉)`), `t_tm` TM steps take
expected time, given correctness, at most
`552 (s_tm + 1) t_tm (37 δ^{−1/2} + 2 s_tm0 + 4 + 6 (s_tm + 1) t_tm)^5 / ((1−δ) ρ_v k)`, i.e.
`O(t_tm s_tm (δ^{−1/2} + s_tm0 + t_tm s_tm)^5/(ρ_v k))` for `δ ≤ 1/2`. This is the paper's
bound with `1/δ` improved to `δ^{−1/2}`.

**TM version.** Theorem 7.1 composed with Lemma X gives the paper's Theorem 4.1 (error part)
for TMs.

## 8. Proof outline

### 8.1 Logic (PROVED)

**Lemma 8.1.** Suppose window `k` starts in `Γ_{k−1} + I`. Then the work dynamics alone (all
reactions except clock moves and ticks) terminates on every run in finitely many steps. Its
unique terminal state is `Γ_k`, and `Γ_k` has no enabled work reaction.

*Proof by window type.*

- **Transitions.** `I` meets exactly one state species in `Γ_{k−1}`. In μ4 of a read step,
  `R_q` meets exactly one of `T`, `M`: `val(w) ≤ 2d − 1 < θ(s)` if `w₁ = 0`, and
  `val(w) ≥ 2d + (d−1)/2 > θ(s)` if `w₁ = 1` (`d ≥ 9`). Nothing changes `T` or `M` before `U`
  exists, because `S_{q,3}` catalyses nothing. The autocatalysis preserves the state count
  (tripling it for `X_e`).
- **Coexistence of state species.** During a transition two state species coexist: `(U or X,
  S_{·,1})`, `(S_{·,1}, S_{·,2})`, `(S_{·,2}, S_{·,3})`, `(S_{·,3}, R/U/X)`. In each pair the
  old member (the first) either catalyses nothing (`S_{·,1}`, `S_{·,3}`) or has no reactant
  left (`U`, `X`, `S_{·,2}`: their catalysed reactions are complete in `Γ_{k−1}`); the new
  member is the window's catalyst, whose reactions are the window's work. The new reactions do
  not produce reactants of the old member's catalysed reactions.
- **μ2.** All reactions are one-way conversions. `M + M* + M†`, `T + T* + T†` and
  `T* − M*` (zero at the start) are conserved. Terminal means `M† = T† = D* = B* = A† = A*† = 0`
  and `min(T, M) = 0`, which forces `T* = M* = min(val, θ)`. For `A`:
  `A_end = A + 3A† + D*` at the start.
- **μ4, read** (`b = w₁`, `z = wr(q,b)`). The quantity
  `Ψ = 3(M + M*) + M† − K₁ − 2K₂ − 3(b+1)D + (z+1)B` is conserved by every μ4 reaction, and so
  is `T + T* + T†`. A run is finite: `D` and `B` fire at most `d` times and once; each `M`
  is shifted once; each `K` consumes at most 2 `M†`; `T + M → T* + M*` lowers `T`. At a terminal
  state `M = M* = T = T* = D = B = 0`. If `K₁ + K₂ > 0` there, then `M† = 0` and
  `Ψ = −K₁ − 2K₂ < 0`, contradicting `Ψ = 3val − 3(b+1)d + z + 1 > 0`. Hence
  `M† = Ψ = val(w₂…w_s z)`.
- **μ4, extension.** The conserved quantities are `3(M + M*) + M† + B`, `3(T + T*) + T†`,
  `3D + D*`, `A + A†` and `A* + A*†`. Terminal values are as in the table of §5.
- **Halting.** `Γ_{4N}` stays terminal forever.

Check: a random-order simulation of the whole network, with ticks only at terminal states (40
inputs, `s₀ ∈ {3,4}`, 7 steps, a 4-state xCTM with an extension state, three seeds), matched
`Γ_k` and the xCTM run in every case, including the A-data. ∎

Consequently `Err^c` implies (ii) by induction on `k`, and `P(Err) ≤ Σ_k ε_k` with
`ε_k = sup` over the start of window `k` of `P(the window's tick fires at a non-terminal work
state)`. The window starts from `Γ_{k−1} + I`, clock at `C₅`. This uses the strong Markov
property at the jump index of tick `k`: the tick resets the clock to `C_l = C₅`.

### 8.2 One-window bound (PROVED from FIX3 §2 and Lemma 8.3)

Fix a window starting at work state `x₀` with clock `C_l`. For a work state `x` put
`a(x) = #A + #A†`, `f(x) = #A* + #A*†` and `ρ(x)` = total unit-rate work propensity. Unit-rate
clock propensities at `(x, c)` are: up `a(x)1{c<l}`, down `f(x)1{c>1}`, tick `f(x)1{c=1}`.

**Lemma 8.2.** If `a(x) ≥ b f(x)` and `f(x) ≤ F` for every work state `x` reachable from `x₀`
(with `b > 0`), then
`P(tick at a non-terminal work state) ≤ μ_l(b) · F · τ̄(x₀)`, where
`μ_l(b) = 1/(1 + b + … + b^{l−1}) ≤ b^{−(l−1)}` and `τ̄(x₀) = E[Σ_{j<J} 1/ρ(X_j)]` is the
expected absorption time, at unit rates, of the work chain alone (`X_j` its jump chain, `J` its
absorption index).

*Proof.* Use the statistic `(j, Z_n)`, where `j` is the number of work reactions in the window,
exactly as in FIX3 §3 Step 1. Work reactions change `x` and raise `j`. Clock moves keep `x`. The
tick is the exit at `c = 1`.

For a non-terminal `x` at level `j`, divide the balance law (FIX3 (2.1)) by `f(x)`. This gives
(2.1) with parameters `â = a(x)/f(x) ≥ b`, `ρ̂ = ρ(x)/f(x)`, `κ̂ = 1`, the same `w`, and entry
`e/f(x)`.

1. **Cone, by induction on `j`.** The entry at level 0 is `δ_l`. At level `j+1` it is
   `Σ_{x'} β(x'→x) w_{j,x'}` (work reactions keep `c`), a nonnegative combination of vectors in
   `C_b`. Lemma 2.2 in its `C_b`, `b ≤ â` form (FIX3 §5; boundary values `u_b(0) = w(1) ≥ 0`
   since `κ̂ = 1`, and `u_b(l) = (â − b)w(l) ≥ 0`) gives `w_{j,x} ∈ C_b`. Finiteness, which Lemma 2.1 assumes: a path leaves level
   `(j, x)` by a work jump at most once (a work jump raises `j`, and `j` never decreases), so by
   Tonelli (FIX3 §1, expected number of jumps of a given type) the expected number of such jumps
   satisfies `ρ(x) S_{j,x}(l) ≤ 1`. Hence `S_{j,x}(l) ≤ 1/ρ(x) < ∞` for non-terminal `x`, every
   `w_{j,x}(c)` is finite, and the total identity of Lemma 2.1 applies:
   `S_{j,x}(l) ≤ E_{j,x}(l)/ρ(x)`.
2. **Ticks per state.** By Lemma 2.3, `w(1) ≤ μ_l(b) S(l)`, so the expected number of ticks
   from `(j, x)` is `f(x) w_{j,x}(1) ≤ μ_l(b) F S_{j,x}(l)`.
3. **Sum.** Lemma 8.3 gives `Σ_{j, x non-terminal} S_{j,x}(l) ≤ τ̄(x₀)`. ∎

**Lemma 8.3 (new, PROVED).** For every `j` and `x`, `E_{j,x}(l) ≤ P(X_j = x)`. Hence
`Σ_{j,x non-terminal} S_{j,x}(l) ≤ Σ_{j,x} P(X_j = x)/ρ(x) = τ̄(x₀)`.

*Proof.* Induction on `j`, with `E_{j+1,x}(l) = Σ_{x'} β(x'→x) S_{j,x'}(l)` and
`S_{j,x'}(l) ≤ E_{j,x'}(l)/ρ(x')` (total identity; it applies because `S_{j,x'}(l) ≤ 1/ρ(x')`
is finite, Lemma 8.2 step 1). ∎

### 8.3 Parameters per window (PROVED from §5)

In every window of step `n`, every reachable work state has `f(x) ≤ d_n` and
`a(x)/f(x) ≥ α_n/3`.

- The ratio is exactly `α_n` or `α_n + 1` in every window except μ2 directly after an
  extension.
- In that μ2, `a ≥ α_n d_n/3` (its starting value; `a` never decreases) and `f ≤ d_n` (its final
  value). This factor 3 is the only cost of tripling `A` and `A*` concurrently.

There are always at least `d_n` state molecules.

### 8.4 Microstep completion time (PROVED in §13)

**Lemma 8.4.** For every window `k ≥ 1` of step `n` (`k ∈ {4n, …, 4n+3}`),
`τ̄(Γ_{k−1} + I) ≤ (10.39 h_n + 14.45 + ln(α_n + 2))/d_n ≤ C₀ (s_n + ln(α_n + 2))/d_n` with
`h_n = 1 + ln d_n` and `C₀ = 16` (natural logarithms).

Route (carried out in §13):

1. Split each window into phases: the transition, which is `I + S` (`O(1/d)`) followed by the
   autocatalysis (Lemma A.7 with explicit constants); the catalysed conversions; the comparison;
   and the `K + M†` removals.
2. Bound each phase from the worst state it can start in:
   - a conversion `X → Y` catalysed by `≥ d` molecules finishes, from `≤ N` molecules, in
     expected time `≤ H_N/d`;
   - `T + M → ·` and `K + M† → ∅` have an excess `≥ min(2d/9, (5d−9)/18)`, which gives
     Lemma A.6 in the form `Σ_{q≤x} 1/(q(q+Δ)) ≤ H_x/Δ`;
   - the largest count is `#A + #A† ≤ 3(α_n + 2)d_n`, which is where the `log(α_n + 2)` comes
     from.
3. Sum the phases: `τ̄` is at most the sum of the phase bounds, because each phase's bound holds
   from any state the previous phases can leave.

FIX3 §4 lists A.5–A.7 with explicit constants as not yet checked; this lemma is that item plus
the routine conversion bounds. (T32 §5 has since proved A.5–A.7 with constants; §13 reuses it.)

## 9. Error budget (PROVED; first version, constants refined in §15)

Window 0 starts terminal, so `ε₀ = 0`. For a window of step `n`, Lemmas 8.2 and 8.4 with §8.3
(`l = 5`, `b = α_n/3`, `F = d_n`) give

  `ε ≤ (3/α_n)^4 · d_n · C₀(s_n + log(α_n+2))/d_n = 81 C₀ (s_n + log(α_n + 2))/α_n^4`.

The `d_n` cancels; that is the reason for keeping `#A* = d_n`. Since `i₀ ≥ s₀`, we have
`s_n ≤ s₀ + n ≤ α_n`, and `log(α + 2) ≤ α` for `α ≥ 3`. So `ε ≤ 162 C₀/α_n³`. Four windows per
step give

  `P(Err) ≤ Σ_{n≥0} 648 C₀/(i₀ + n)³ ≤ 648 C₀ ∫_{i₀−1}^∞ x^{−3} dx = 324 C₀/(i₀ − 1)² ≤ δ`

for `i₀ ≥ 1 + 18√(C₀/δ)`.

Per CTM step the error is `O((i₀ + n)^{−3})`, against A.5's target `1/(Θ(1/δ) + i)²`.

Unproved remark, not used: for general `l` the window error is `O((s_n + log α_n)/α_n^{l−1})`,
which is summable for `l ≥ 4` (the converse "only if" would need `s_n` to grow linearly, which
is not shown). With `l = 4` one needs `i₀ = Θ(1/δ + s₀)` (the paper's choice), and the time exponent
drops from 5 to 4. We keep `l = 5` as the paper states.

## 10. Time (sketch of the first version; the proof is §14)

On a correct run, the time of window `k` is at most `(v_max/k)` times the unit-rate time. Here
`v_max = |z|_max/ρ_v ≤ c(α_n + 2)d_n/ρ_v`: `A` dominates, `M†, T† ≤ 3^{s_n+1}`, there is at most
one `I`, and the clock is one molecule. The unit-rate time is `τ_work` plus the wait for the
tick once the work is terminal. In the terminal state `a/f = α_n + 1 ≥ 2` (or `α_n` right after
an extension) and `f ≥ d_n/3`. FIX3 Lemma 2.4, normalized by `f`, bounds the wait from `C₅` by
`2/(f μ_5(a/f)) ≤ 12(α_n+1)^4/d_n`. The wait from any `c ≤ 5` is at most the wait from `C₅`
(birth–death monotonicity; to be written).

So the expected window time is `O((α_n + 2)^5/(ρ_v k))`. Sum over `4n` windows, use the strong
Markov property at ticks on `Err^c`, and divide by `P(Err^c) ≥ 1 − δ`. This gives Theorem 7.2.

Still to write: the monotonicity of the tick wait in the start position, and the phase bound of
Lemma 8.4 in expectation (it covers both §9 and here).

## 11. Lemma ledger

Used from FIX3:

- §1: balance law (1.1), occupation statistics, jump chain and time formula.
- §2: Lemma 2.1 (total identity), Lemma 2.2 in the `C_b`, `b ≤ a` form recorded in §5 (applied
  per work state with `â(x) = a(x)/f(x) ≥ b`), Lemma 2.3, Lemma 2.4 (time part only).
- §3, Step 1–2 pattern: levels indexed by the number of non-clock reactions, cone induction.
- §4: the per-microstep bound "tick rate × expected work time" in place of Chebyshev. Here it is
  re-proved in jump-chain form (Lemma 8.2), because the clock rates change inside a window
  (tripling and the per-step addition of `A`), which §4's independence argument does not cover.

New:

- Lemma 8.1 (logic, PROVED).
- Lemma 8.2 (one window with state-dependent clock rates, PROVED).
- Lemma 8.3 (occupation domination by the work chain, PROVED).
- §8.3 parameter bounds (PROVED).
- Lemma 8.4 (completion time, PROVED in §13, `C₀ = 16`).
- Lemma X (TM → xCTM with extension, PROVED in §12).
- Tick-wait formula and monotonicity (Lemma 14.2), volume bound (Lemma 14.3), Theorem 7.2
  (PROVED in §14).

The three OPEN items of the first version (Lemma 8.4 with explicit `C₀`; Lemma X; tick-wait
monotonicity and the volume constant) are closed in §12–§15. What is still open is listed in
§16.

## 12. Lemma X: TM → xCTM with tape extension (PROVED)

This section reuses the construction of `FIX3-SCWB-T32.md` §6 (pairs of xCTM cells holding a
head marker and a TM symbol; a right move marks the next pair; a left move shifts all symbols one
pair clockwise with a carry) and adds a seam pair, a seam flag in the scanning states, and two
extension routines.

### 12.1 TM, visited interval, extending steps

As in T32 §6: states `Q_M`, halting set `H ⊆ Q_M`, start `q₀`, binary tape (0 = blank),
`δ_M(q, a) = (q', z, D)` with `D ∈ {L, R}` for `q ∉ H`. Fix the input bound `s_tm0 ≥ 1`; the
input `w_in`, `|w_in| ≤ s_tm0`, is written on cells `1..|w_in|`, the head is on cell 1. Write
`(q_t, a_t, h_t)` for the run (`a_t : ℤ → {0,1}` the tape). The **visited interval** is
`J_t = [lo_t, hi_t]`, the smallest interval containing `[1, s_tm0]` and `h_0, …, h_t`; put
`L_t = |J_t|`. The **space** of the first `t` steps is `s_tm := L_t` (nondecreasing in `t`).
Since `|h_{t+1} − h_t| = 1`, `J_{t+1} = J_t ∪ {h_{t+1}}`, and `h_{t+1} ∉ J_t` exactly when
(`D = R` and `h_t = hi_t`) or (`D = L` and `h_t = lo_t`). Call such a step **extending**; then
`L_{t+1} = L_t + 1`, otherwise `L_{t+1} = L_t`. The number of extending steps among the first
`t` is `e_t = L_t − s_tm0 ≤ t`.

### 12.2 Encoding

A **slot** is two consecutive xCTM cells: a marker bit, then a symbol bit. Slot codes: an
ordinary TM cell with symbol `u` is `(0, u)`; the head cell is `(1, u)`; the **seam** is `(1, 0)`.
The canonical tape `κ_t ∈ {0,1}^{2L_t + 2}` is, read clockwise from the xCTM head (`h = h_t`,
`lo = lo_t`, `hi = hi_t`, `a = a_t`):

  `(1, a(h)), (0, a(h+1)), …, (0, a(hi)), (1, 0), (0, a(lo)), …, (0, a(h−1))`.

So the seam sits between the rightmost and the leftmost visited cell, which are adjacent on the
circle. The **canonical configuration** is `K_t = (G⁰(q_t), κ_t)`. In particular
`K_0` has tape `(1, w_1)(0, w_2)…(0, w_{s_tm0})(1, 0)` (input padded with 0 to length
`s_tm0`), of length `s₀ = 2 s_tm0 + 2 ≥ 4`.

**Order rule.** A canonical tape has exactly two slots with marker 1, the head slot and the seam,
and a marker bit cannot tell them apart. Every scan below starts at a known slot and its control
state records which marked slots it has passed; e.g. starting just after the head slot of a
canonical tape, the first marked slot met is the seam and the second is the head slot. This is
the only way the machine distinguishes them, and the case analysis in §12.4 checks it each time.

### 12.3 The xCTM `𝒞(𝓜)`

States are indexed by `q ∈ Q_M` (for the move states the index is the TM state `q'` after the
move) and, for the shift states, by a carry `c ∈ {0, 1, σ}` (`σ` = "seam") and a flag
`π ∈ {0, 1}` ("seam already passed"). "copy → X" means: read `b`, write `b`, go to `X` (for both
`b`). Entries are `next state, written bit`. `μ(c) = 1` if `c = σ` and 0 otherwise;
`β(c) = c` if `c ∈ {0,1}` and 0 if `c = σ`.

| State | read 0 | read 1 |
|---|---|---|
| `G⁰(q)` (seek head, no seam ahead) | `G⁰s(q)`, 0 | `q ∈ H`: `Hh(q)`, 1; `q ∉ H`: `Hd(q)`, 1 |
| `G⁰s(q)` | copy → `G⁰(q)` | |
| `G¹(q)` (seek head, seam ahead) | `G¹s(q)`, 0 | `G¹t(q)`, 1 |
| `G¹s(q)`, `G¹t(q)` | copy → `G¹(q)`; copy → `G⁰(q)` | |
| `Hh(q)`, `q ∈ H` | copy → `Halt(q)` | |
| `Halt(q)` | halting state (`Q_H`) | |
| `Hd(q)`, `q ∉ H`, reads `u` | with `(q', z, D) = δ_M(q, u)`: `D = R`: `Mk(q')`, `z`; `D = L`: `Sh(q', z, 0)`, `z` | same rule |
| **R move** | | |
| `Mk(q')` | `Ms(q')`, 1 | `Rx(q')`, 1 |
| `Ms(q')` | copy → `C¹(q')` | |
| `C¹(q')` | `C¹s(q')`, 0 | `C¹t(q')`, 1 |
| `C¹s(q')`, `C¹t(q')` | copy → `C¹(q')`; copy → `C⁰(q')` | |
| `C⁰(q')` | `C⁰s(q')`, 0 | `Cz(q')`, 0 |
| `C⁰s(q')`, `Cz(q')` | copy → `C⁰(q')`; copy → `G⁰(q')` | |
| **R extension** | | |
| `Rx(q')` | `E¹_R(q')`, 0 | `E¹_R(q')`, 0 |
| `E¹_R(q')`, `E²_R(q')` | extension states: `nx = E²_R(q')`, resp. `Pa(q')` | |
| `Pa(q')` | `Pas(q')`, 0 | `Paz(q')`, 0 |
| `Pas(q')`, `Paz(q')` | copy → `Pa(q')`; copy → `Pb(q')` | |
| `Pb(q')` | `Pbs(q')`, 1 | `Pbs(q')`, 1 |
| `Pbs(q')` | copy → `Pc(q')` | |
| `Pc(q')` | `Pcs(q')`, 1 | `Pcs(q')`, 1 |
| `Pcs(q')` | `G⁰(q')`, 0 | `G⁰(q')`, 0 |
| **L move** | | |
| `Sh(q', c, π)` (marker of the next slot) | `ShS(q', c, π, 0)`, `μ(c)` | `π = 0`: `ShS(q', c, 0, 1)`, `μ(c)`; `π = 1`: `Se(q', c)`, 1 |
| `ShS(q', c, π, m)`, reads `a` | `Sh(q', c⁺, π ∨ m)`, `β(c)`, where `c⁺ = a` if `m = 0`, `c⁺ = σ` if `m = 1` | same rule |
| `Se(q', c)`, `c ∈ {0,1}` | `G¹(q')`, `c` | `G¹(q')`, `c` |
| `Se(q', σ)` | `E¹_L(q')`, 0 | `E¹_L(q')`, 0 |
| `E¹_L(q')`, `E²_L(q')` | extension states: `nx = E²_L(q')`, resp. `Qa(q')` | |
| `Qa(q')` | `Qas(q')`, 0 | `Qat(q')`, 1 |
| `Qas(q')`, `Qat(q')` | copy → `Qa(q')`; copy → `Qb(q')` | |
| `Qb(q')` | `Qbs(q')`, 1 | `Qbs(q')`, 1 |
| `Qbs(q')` | `G¹(q')`, 0 | `G¹(q')`, 0 |

Every read state has both entries, so `δ, wr` are total on `Q_R × {0,1}` (entries that never
occur in a run, such as `Mk` meeting a malformed slot, are still defined). Counting: 5 seek
states, 46 move states and `Hd(q)` per `q ∉ H`, or `Hh(q)`, `Halt(q)` per `q ∈ H`, so
`|Q| = 52 |Q_M| + |H|`, `|Q_E| = 4 |Q_M|`, `|Q_H| = |H|`. The start state is `G⁰(q₀)`.
`𝒞(𝓜)` depends on `𝓜` alone (no counters, no dependence on `s_tm0`, the input or the space).

### 12.4 Statement and proof

**Lemma X.** Let `𝓜`, `s_tm0 ≥ 1` and `w_in` (`|w_in| ≤ s_tm0`) be as in §12.1, and run
`𝒞 = 𝒞(𝓜)` from `K_0`. Let `t ≥ 0` be such that `q_0, …, q_{t−1} ∉ H`. Then:

(a) `𝒞` is in `K_t` after exactly `N_t = Σ_{t' < t} ν_{t'}` steps, where, with `L = L_{t'}` and
`D` the direction of TM step `t'`:
`ν_{t'} = 2L + 4` (`D = R`, not extending), `4L + 10` (`D = R`, extending),
`4L + 4` (`D = L`, not extending), `6L + 12` (`D = L`, extending).
No halting state is entered before step `N_t`.

(b) The xCTM tape length is `2L_{t'} + 2` at step `N_{t'}` and at most `2L_t + 2` at every step
`≤ N_t`. In particular it never exceeds `2 s_tm + 2`, `s_tm = L_t`.

(c) If `q_t ∈ H`, `𝒞` enters `Halt(q_t)` at step `N_t + 2` (its tape is `κ_t` rotated by one
slot). If `𝓜` never halts, `𝒞` never enters a halting state. So `𝒞` halts iff `𝓜` halts.

(d) `N_t ≤ (4 s_tm + 4) t + (2 s_tm + 2) e_t ≤ (6 s_tm + 6) t`, with `s_tm = L_t` and
`e_t ≤ t` the number of extending steps.

(e) `K_t` determines the TM configuration: the TM state is the index of `G⁰(q_t)`, and the tape on
`J_t` with the head position is read off `κ_t` (head slot first, seam between `hi` and `lo`).

*Proof.* (a) by induction on `t`; `N_0 = 0` and the start is `K_0`. Fix `t' < t`, write
`q = q_{t'} ∉ H`, `h, lo, hi, L, a` for the data at `t'`, and `P_1, …, P_{L+1}` for the slots of
`κ_{t'}` clockwise from the xCTM head. `P_1` is the head slot, and the seam is `P_j` with
`j = hi − h + 2 ∈ {2, …, L+1}`; so `P_2` is the seam iff `h = hi`, and `P_{L+1}` is the seam iff
`h = lo`. Two steps: `G⁰(q)` reads the marker 1 of `P_1` (writes 1), `Hd(q)` reads `u = a(h)`
and writes `z`, where `(q', z, D) = δ_M(q, u)`. The xCTM head is now at the first bit of `P_2`.
Let `a'` be `a` with `a'(h) = z`.

*Case R, `h < hi`.* `P_2 = (0, a(h+1))`. `Mk` reads 0 and writes 1, `Ms` copies `a(h+1)`, so
`P_2 = (1, a(h+1))`. `C¹(q')` starts at `P_3`. The slots `P_3, …, P_{L+1}` contain the seam and
no other marked slot (the seam is not `P_1` or `P_2`). `C¹` copies unmarked slots, copies the
seam (`C¹t`) and switches to `C⁰`; `C⁰` copies unmarked slots up to the next marked slot, which is
`P_1` by the order rule. There it writes marker 0 and `Cz` copies `z`. The machine is in
`G⁰(q')` at the first bit of `P_2`, and the tape from `P_2` is
`(1, a(h+1)), (0, a(h+2)), …, (0, a(hi)), (1,0), (0, a(lo)), …, (0, a(h−1)), (0, z)`, which is
`κ_{t'+1}` (`h_{t'+1} = h + 1`, `J` unchanged). Steps: `2 + 2 + 2(L−1) + 2 = 2L + 4`.

*Case R, `h = hi` (extending).* `P_2` is the seam. `Mk` reads 1, writes 1; `Rx` reads 0, writes
0, so `P_2 = (1, 0)`: this will be the head slot of the new blank cell `hi + 1`. The xCTM head is
at the first bit of the slot after `P_2`, which is `P_3` (`P_1` if `L = 1`). `E¹_R`, `E²_R`
append two 0's behind the head, i.e. insert a slot `X = (0, 0)` between `P_2` and `P_3`; `X` is
now the last slot of the clockwise word. Pass 1 (`Pa`, `Pb`, `Pc`) from `P_3`: `P_3, …, P_{L+1}`
are unmarked (the seam was `P_2`) and copied; the first marked slot is `P_1`, whose marker is
cleared (`Pa` writes 0) and whose symbol `z` is copied (`Paz`); the next slot `P_2` is rewritten
as `(1, 0)` (`Pb`, `Pbs`; it was `(1, 0)`); the next slot `X` is written `(1, 0)` (`Pc`, `Pcs`).
Pass 2 in `G⁰(q')` from `P_3`: `P_3, …, P_{L+1}, P_1` are unmarked and copied, the next marked
slot is `P_2`. The machine is in `G⁰(q')` at the first bit of `P_2`, and the tape from `P_2` is
`(1, 0), (1, 0), (0, a(lo)), …, (0, a(hi − 1)), (0, z)`: head slot of the blank cell `hi + 1`,
seam `X`, then cells `lo, …, hi`. This is `κ_{t'+1}` with `h_{t'+1} = hi_{t'+1} = hi + 1`.
Steps: `2 + 2 + 2 + [2(L−1) + 2 + 2 + 2] + [2(L−1) + 2] = 4L + 10`.

*Case L, `h > lo`.* `P_{L+1} = (0, a(h−1))` and the seam is `P_j` with `2 ≤ j ≤ L`. Shift:
`Sh(q', z, 0)` processes `P_2, …, P_{L+1}`. Invariant before slot `P_i` (`2 ≤ i ≤ L+1`): the
carry is the old content of `P_{i−1}` (for `i = 2`, the cell content `z`), and `π = 1` iff the
seam is among `P_2, …, P_{i−1}`. Processing `P_i` writes the carry's code (`(1, 0)` for `σ`,
`(0, c)` for a cell symbol `c`) and loads the old content of `P_i` into the carry; a marker 1 read
with `π = 0` is the seam, as the order rule requires (no other marked slot lies in
`P_2..P_{L+1}`). After `P_{L+1}` the carry is the cell symbol `a(h−1)` and `π = 1`. The next
marker read is that of `P_1` (marker 1 with `π = 1`), so `Se(q', a(h−1))` writes `(1, a(h−1))`.
Now `P_1 = (1, a(h−1))`, `P_2 = (0, z)`, `P_i` = old `P_{i−1}` for `3 ≤ i ≤ L+1`, and the seam is
at `P_{j+1}`, `3 ≤ j + 1 ≤ L + 1`. `G¹(q')` from `P_2` copies unmarked slots, passes the seam
(first marked slot), switches to `G⁰(q')`, copies the rest and reaches `P_1`. Tape from `P_1`:
`(1, a(h−1)), (0, z), (0, a(h+1)), …, (0, a(hi)), (1, 0), (0, a(lo)), …, (0, a(h−2))` =
`κ_{t'+1}`. Steps: `2 + 2L + 2 + 2L = 4L + 4`.

*Case L, `h = lo` (extending).* The seam is `P_{L+1}`. The shift runs as in the previous case;
after `P_{L+1}` the carry is `σ`, `π = 1`, and `P_2, …, P_{L+1}` hold
`(0, z), (0, a(lo+1)), …, (0, a(hi))`. At `P_1`, `Se(q', σ)` writes `(1, 0)`: `P_1` is now the
seam. The xCTM head is at the first bit of `P_2`; `E¹_L`, `E²_L` insert `X = (0, 0)` between `P_1`
and `P_2`. Pass 1 (`Qa`, `Qb`) from `P_2`: `P_2, …, P_{L+1}` unmarked, copied; first marked slot
`P_1`, copied; next slot `X`, written `(1, 0)`. Pass 2 in `G¹(q')` from `P_2`: unmarked slots
copied, the seam `P_1` passed (first marked slot), `G⁰(q')` at the first bit of `X`. Tape from
`X`: `(1, 0), (0, z), (0, a(lo+1)), …, (0, a(hi)), (1, 0)`: head slot of the blank cell `lo − 1`,
then cells `lo, …, hi`, then the seam. This is `κ_{t'+1}` with `h_{t'+1} = lo_{t'+1} = lo − 1`.
Steps: `2 + 2L + 2 + 2 + [2L + 2 + 2] + [2L + 2] = 6L + 12`.

In all four cases the only states of the form `G⁰(·)` visited before `K_{t'+1}` read a marker
0 (they are entered at an unmarked slot or after the seam, and stop at the head slot), so
`Hh(·)` and `Halt(·)` are not entered; the TM data after the step are those of `t' + 1`. This
proves (a).

(b) Only extension states change the length, by one cell each; they occur exactly in extending
steps, two per step. (c) From `K_t` with `q_t ∈ H`: `G⁰(q_t)` reads 1, `Hh(q_t)` copies, then
`Halt(q_t)`. If `𝓜` never halts, (a) holds for every `t`, and `N_t` is strictly increasing with
no halting state before `N_t`. (d) A non-extending step has `ν ≤ 4L_{t'} + 4 ≤ 4 s_tm + 4`. An
extending step has `L_{t'} ≤ s_tm − 1` and `ν ≤ 6L_{t'} + 12 ≤ (4 s_tm + 4) + (2 s_tm + 2)`.
Sum over the `t` steps, `e_t` of them extending. (e) is the definition of `κ_t`. ∎

**Relation to §4 and Theorem 7.1.** The xCTM `𝒞(𝓜)` is the `𝒞` of §3 (its read, extension and
halting states are as listed), `q̂ = G⁰(q₀)`, `w₀ = κ_0`, `s₀ = 2 s_tm0 + 2 ≥ 4`. CTM step `n`
of §5 is xCTM step `n` here. The paper's Lemma A.9 has `s_ct = 2 s_tm` and `t_ct = O(t_tm s_tm)`;
here `s_ct ≤ 2 s_tm + 2` (one seam pair) and `t_ct = N_{t_tm} ≤ 6(s_tm + 1) t_tm`, with
extension. Compared with T32 §6 (which pads instead of extending), the step counts are those of
T32 Lemma 6.2 for `L + 1` slots (`2(L+1) + 2` and `4(L+1)`) plus the extension routines.

**Check.** A script (not in the repository) builds the table above and runs 8000
random TMs (`|Q_M| ≤ 6`, one halting state, `s_tm0 ∈ 1..5`, inputs of length `0..s_tm0`, up
to 60 TM steps) against a two-way-infinite-tape simulator: at every TM step `𝒞` is in `K_{t+1}`
exactly `ν_t` steps after `K_t` (the four formulas), the tape length is `2L_t + 2`, no halting
state is entered early, and `Halt(q)` is entered two steps after a canonical configuration with
`q ∈ H`. State count printed: `52 |Q_M| + |H|`.

## 13. Proof of Lemma 8.4 (`C₀ = 16`)

**Conventions.** Unit rates (every bimolecular reaction `X + Y → …` has propensity `#X·#Y`), as
in the definition of `τ̄`. Fix a window `k ≥ 1` of step `n` with `q_n ∉ Q_H` and write
`d = d_n = 3^{s−1}`, `s = s_n ≥ 3`, `α = α_n`, `h = 1 + ln d`, `v = val(w_n) ≤ 3d − 1`,
`θ = θ(s_n) = 20d/9`, `g = 2d/9` (an integer, as `9 | d`). Tools from `FIX3-SCWB-T32.md`:
Lemma 1.3 (catalytic decay `H_n/c`; annihilation with excess `≤ H_Δ/Δ`, decreasing in `Δ`;
autocatalysis `2H_{m−1}/m`), Lemma 1.4 (expected maximum of `n` variables with
`P(L_i > t) ≤ K e^{−ct}` is `≤ (1 + ln(nK))/c`, no independence needed), Fact 1.2 (tagged
projection of one labelled molecule, its lumped channels driven by their own Poisson processes,
restarted at stopping times). `H_{d−1} ≤ h`. All of these are statements about a continuous-time
chain of bimolecular reactions and apply to the work chain alone. If `𝒞` halts at step `N`, window
`4N` (μ1 of the halting step) starts at `Γ_{4N−1} + I` and runs the transition into `S_{h,1}`;
it is a W1 window below (the 4→1 reactions exist for halting targets, and `U`, `X` have no
reactant), so `τ̄ ≤ (1 + 2h)/d_N`. The windows after it, `k > 4N`, start at `Γ_{4N} + I`,
which is terminal (§8.1), and have `τ̄ = 0`.

**Threshold facts** (T32 (3.1), for every word of length `s ≥ 3`). `|v − θ| ≥ g`; `v < θ` iff
`w_1 = 0`; and if `w_1 = 0`, then `θ − v ≤ θ − (3d−1)/2 = (13d + 9)/18 ≤ d`.

**Phase rule.** If `0 = ϑ_0 ≤ ϑ_1 ≤ … ≤ ϑ_r` are stopping times of the work chain and the chain
is absorbed by `ϑ_r`, then `τ̄ ≤ Σ_i E[ϑ_i − ϑ_{i−1}]`, and by the strong Markov property each
term is at most the supremum of the corresponding expected duration over the states the chain
can occupy at `ϑ_{i−1}`.

**Transition part.** In every window, `I` meets exactly one state species of `Γ_{k−1}` (§8.1),
and the autocatalysis involves only the old and the new state species. So the vector (I, old
state species, new state species) changes only by these reactions, whose propensities depend on
it alone: it is a Markov chain by itself. Its absorption time `ϑ_1` has mean
`1/d + 2H_{d−1}/d` (Exp(`d`) for the `I`-reaction, then T32 Lemma 1.3(c)), except in the
extension window W4e below. After `ϑ_1` the new state species has its final count and the old
one is 0; neither changes again in the window.

**(W1) window `4n`** (μ1), start `Γ_{4n−1} + I`, state species `U_{q,b} = d` or, after an
extension, `X_e = 3 d_{n−1} = d`. The catalysts `U`, `X` have no reactant in `Γ_{4n−1}` (the
reactants of `U`- and `X`-catalysed reactions, `M, M*, T, T*, D, B` and, for `X`, `A, A*`, are
0 there, table §5; after a read step `A, A*` are positive, but `U` catalyses no A-reaction), `S_{·,1}` catalyses nothing, and the uncatalysed
reactions need `T` and `M` or `K`. So only the transition runs, as in T32 Lemma 5.1:
`d·τ̄ = 1 + 2H_{d−1} ≤ 1 + 2h`.

**(W2) window `4n+1`** (μ2), start `Γ_{4n} + I`. Phases: `ϑ_1` (transition); `ϑ_2` = first time
`≥ ϑ_1` with `Y := #M† + #T† + #D* + #B* + #A† + #A*† = 0`; absorption.
- `ϑ_2 − ϑ_1`. After `ϑ_1`, `#S_{q,2} = d`. Each `Y`-molecule is converted by an
  `S_{q,2}`-catalysed reaction (`M† → M`, `T† → T`, `D* → D + A`, `B* → B`, `A† → 3A`,
  `A*† → 3A*`), so `Y` drops by 1 at rate `dY`. Nothing produces `Y`: its producers are
  catalysed by `U` or `X`, which are absent in this window. T32 Lemma 1.3(a):
  `E[ϑ_2 − ϑ_1] ≤ H_{Y₀}/d` with `Y₀ = Y(Γ_{4n})`. The largest `Y₀` occurs after an extension,
  `(A†, A*†) = (αd/3, d/3)`: `Y₀ ≤ (3d − 1) + 20d/9 + d + 1 + (α + 1)d/3 = (59 + 3α)d/9`.
- Absorption after `ϑ_2`. Now the restores are complete: `M + M* = v`, `T + T* = θ`, and
  `M* = T*` (both start at 0 in `Γ_{4n}` and only `T + M → T* + M*` creates them). So
  `#M − #T = v − θ`, with `|v − θ| ≥ g`. Every other reaction with `T` or `M` as reactant is
  catalysed by `U` or `X`. So only `T + M → T* + M*` can fire, and T32 Lemma 1.3(b) bounds the
  mean time to `min(T, M) = 0` by `H_g/g ≤ (4.5/d)(1 + ln(2d/9)) = (4.5/d)(h − ln 4.5)`.
Sum: `d·τ̄ ≤ 1 + 2h + h + ln((59 + 3α)/9) + 4.5h − 4.5 ln 4.5 ≤ 7.5h + ln(α + 2) − 4.58`, using
`(59 + 3α)/(9(α + 2)) ≤ 59/18` and `ln(59/18) ≤ 1.188`, `4.5 ln 4.5 ≥ 6.768`
(`1 + 1.188 − 6.768 = −4.58`).

**(W3) window `4n+2`** (μ3), start `Γ_{4n+1} + I`. `S_{q,2}`-catalysed reactions have no
reactant (`M† = T† = D* = B* = A† = A*† = 0` in `Γ_{4n+1}`), `S_{q,3}` catalyses nothing,
`min(T, M) = 0` and `K = 0`. Only the transition runs: `d·τ̄ = 1 + 2H_{d−1} ≤ 1 + 2h`.

**(W4r) window `4n+3`, `q_n ∈ Q_R`**, start `Γ_{4n+2} + I`. Without its A-data, `Γ_{4n+2}` is a
state of T32's class `𝒦_3(q_n, w_n)` with `m = d` (state `S_{q,3} = d`; `M + M* = v`,
`T + T* = θ`, `M* = T*`, `min(T, M) = 0`, `D = d`, `B = 1`; all daggered and starred-restore
species 0; `K = 0`). The reactions that can fire in this window are exactly those of T32
Lemma 4.4: the 3→4 rows and the μ4 rows of §3.2 coincide with those of T32's `N♯` (§3.3 there),
and the A-species are reactants only of `S_{·,2}`- and `X`-catalysed reactions (absent here) and
of the clock. So T32 Lemma 5.4 applies verbatim: `d·τ̄ ≤ 10.39 h + 14.45`.

**(W4e) window `4n+3`, `q_n = e ∈ Q_E`**, start `Γ_{4n+2} + I`, with the same memory as in W4r
and A-data `((α+1)d, 0, d, 0)`.
- *Transition, `ϑ_1`.* `I + S_{e,3} → 3X_e` (rate `d`), then `S_{e,3} + X_e → 4X_e`. With
  `i = #S_{e,3}`, `#X_e = 3(d − i)` and the rate is `3i(d − i)`; `i` runs from `d − 1` to 1.
  `E[ϑ_1] = 1/d + Σ_{i=1}^{d−1} 1/(3i(d−i)) = 1/d + 2H_{d−1}/(3d)`. After `ϑ_1`,
  `#X_e = 3d` and stays (no `I`).
- *After `ϑ_1`* (strong Markov, fresh Poisson processes). Every `X_e`-catalysed reaction has
  rate `3d` per reactant molecule. Nothing produces `D, B, A, A*, T` (their producers are
  catalysed by `S_{·,2}`, absent) or new `M`-family molecules (`B → M† + B*` writes `M†`, and
  `M† → M` needs `S_{·,2}`). Families, counted at `ϑ_1`:
  - `D` (`≤ d`), `B` (`≤ 1`), `A` (`≤ (α+1)d`), `A*` (`≤ d`), `T` (`≤ T̂`, where
    `T̂ = 0` if `w_1 = 1` and `T̂ ≤ θ − v ≤ d` if `w_1 = 0`). In its tagged projection each such
    molecule has a lumped channel of rate `3d` that removes it (`D → 3D*`, `B → M† + B*`,
    `A → A†`, `A* → A*†`, `T → 3T†`; a `T` may also leave earlier by pairing). So its exit time
    `L_i` satisfies `P(L_i > t) ≤ e^{−3dt}`.
  - The `M`-family (molecules in `M` or `M*`, at most `v ≤ 3d − 1`). Exactly T32 Lemma 5.4
    item 3 with catalyst count `3d` in place of `m`: channels shift (`3d·1{i∈M}`), pairing
    (`#T·1{i∈M} ≤ T̂·1{i∈M}`, `#T` nonincreasing), return (`3d·1{i∈M*}`). The exit time
    satisfies `L_i ≤ E_i/(3d) + Γ_i/(3d)` with `E_i ~ Exp(1)` and `Γ_i ~ Exp(π)`,
    `π = 3d/(3d + T̂) ≥ 3/4`, hence `P(L_i > t) ≤ e^{−3dt/2} + e^{−3dπt/2} ≤ 2e^{−9dt/8}`.
  - `T*`: present at `ϑ_1` or created by a pairing (which needs an `M`, so before the
    `M`-family is extinct); at most `θ` molecules in all. Each leaves by `T* → 3T†` within
    `E_j/(3d)` after `max(ϑ_1, its creation)`, `E_j ~ Exp(1)` (tagged projection restarted at
    that stopping time).
  Let `ζ` be the largest exit time over the first two groups (`n ≤ d + 1 + (α+1)d + d + d +
  (3d − 1) = (α + 7)d` molecules; all satisfy `P(L_i > t) ≤ 2e^{−9dt/8}`). T32 Lemma 1.4:
  `E[ζ − ϑ_1] ≤ (8/(9d))(1 + ln(2(α+7)d))`. The `T*` family is extinct by
  `ζ + max_j E_j/(3d)`, mean `≤ E[ζ] + (1 + ln θ)/(3d) = E[ζ] + (h + ln(20/9))/(3d)`. At that
  time `S_{e,3} = M = M* = T = T* = D = B = A = A* = 0`: the terminal state `Γ_{4n+3}`.
Sum: `d·τ̄ ≤ 1 + (2/3)h + (8/9)(h + ln 2 + ln(α + 7)) + (h + 0.80)/3
≤ 1.89 h + 0.89 ln(α + 7) + 1.89`.

**Assembly.** With `ln(α + 7) ≤ ln(α + 2) + ln 3.5`, every window bound is at most
`(10.39 h + 14.45 + ln(α + 2))/d` (W4r is the largest in `h`; W2 and W4e carry the `ln α`).
Finally `h = 1 + (s − 1) ln 3 ≤ 1.0987 s` and `10.39 h + 14.45 ≤ 11.415 s + 13.43 ≤ 15.9 s` for
`s ≥ 3`, so `τ̄ ≤ 16 (s_n + ln(α_n + 2))/d_n`. This is Lemma 8.4 with `C₀ = 16`. ∎

The `ln α` comes only from the `A`-family: `A† → 3A` in W2 after an extension and `A → A†` in
W4e convert `Θ(α d)` molecules with `Θ(d)` catalysts.

**Check.** A script (not in the repository) runs the work chain of the §3 network by Gillespie
simulation for every window type (W1 after a read and after an extension step, W2 with and
without a preceding extension, W3, W4r, W4e), `s = 3..6`, `α ∈ {3, 30}` (`α = 3` only at
`s = 6`), the extreme words
`01…1`, `1…1`, `10…0`, `0…0`; 200 runs per case for `s ≤ 5`, 40 for `s = 6`. Every run ended in
the `Γ_k` of §5 (Lemma 8.1), and every mean is below its bound (within sampling error for W1
and W3, whose mean `1 + 2H_{d−1}` is the bound up to `2(h − H_{d−1})`). Largest observed
mean/bound per type: W1 0.97, W3 0.97, W2 0.64, W4e 0.40, W4r 0.31; the largest observed mean over all cases is `0.24·C₀(s + ln(α+2))`.
A script (not in the repository) checks the numerical inequalities used here and in §14–§15.

## 14. Time part: proof of Theorem 7.2

In this section `k` is the rate constant and `ω` indexes windows. Real time: a reaction
`X + Y → …` has propensity `(k/v(z))·#X·#Y` with `v(z) = |z|/ρ_v`. Let
`B(z)` be the total unit-rate propensity (work and clock reactions). The jump chain does not depend
on `v` or `k`.

**Lemma 14.1 (real time from unit-rate time).** Given the jump chain `(Z_j)`, the holding times
are independent exponentials with means `v(Z_j)/(k B(Z_j))`. Hence for a stretch of jumps
`j_0 ≤ j < j_1` (stopping indices of the jump chain) in which `|Z_j| ≤ V`,
`E[real duration] ≤ (V/(ρ_v k)) · E[Σ_{j_0 ≤ j < j_1} 1/B(Z_j)]`, and the last expectation is the
expected duration of the same stretch at unit rates.

*Proof.* FIX3 §1 (time formula) with the state-dependent rate factor `k/v(Z_j)`; Tonelli. ∎

**Lemma 14.2 (tick wait; monotone in the start).** Freeze the work state at `x` with `a = a(x)`,
`f = f(x) > 0`, `r = a/f`. The clock is the birth–death chain on `{1, …, 5}` with up rate `a`
(from `c < 5`), down rate `f` (from `c > 1`) and the tick at rate `f` from `c = 1`. Let `m(c)`
be the expected time to the tick from `c`. Then

  `m(c) = (1/f) Σ_{c'=1}^{c} Σ_{j=0}^{5−c'} r^j`,

so `m` is strictly increasing in `c`, and `m(c) ≤ m(5) = (1/f) Σ_{c=1}^{5} (r^c − 1)/(r − 1)
≤ r⁶/((r − 1)² f)` for `r > 1`.

*Proof.* Let `η(c)` be the expected time to go from `c` to `c − 1` (to the tick for `c = 1`).
The chain is skip-free, so from `c` it reaches the tick by passing `c − 1, …, 1` in order, and by
the strong Markov property `m(c) = Σ_{c' ≤ c} η(c')`. First-step analysis: `η(5) = 1/f`; for
`c < 5`, `η(c) = 1/(a + f) + (a/(a + f))(η(c+1) + η(c))`, i.e. `f η(c) = 1 + r f η(c+1)`. So
`f η(c) = Σ_{j=0}^{5−c} r^j`. Summing over `c ≤ 5` gives `Σ_{c=1}^{5}(r^c − 1)/(r − 1)` (this is
T32 Lemma 2.2), and `Σ_c (r^c − 1)/(r − 1) ≤ Σ_{c ≤ 5} r^c/(r − 1) = r(r⁵ − 1)/(r − 1)²`. ∎

**Lemma 14.3 (volume).** In every window of step `n` (`q_n ∉ Q_H`), every state `z` reachable
from `Γ_{ω−1} + I` (with the clock) has `|z| ≤ (α_n + 24) d_n ≤ 6.75 (α_n + 1) d_n`.

*Proof.* Write `d = d_n`, `α = α_n`. Bounds by group, from the conservation laws of each window
(§8.1, §5):
- state species: `≤ d`, except in W4e, where `3#S_{e,3} + #X_e = 3d` gives `≤ 3d`;
  `#I ≤ 1`; one clock molecule;
- `M`-family: `M + M* + M† = v ≤ 3d` outside μ4; in W4r, `Ψ` of §8.1 is conserved and
  `P := K₁ + 2K₂ + 3(b+1)#D` never increases (`D → 3K_{b+1} + D*` keeps it, the `K + M†`
  reactions lower it by 1), so `M† + 3(M + M*) ≤ val(w_{n+1}) + P ≤ 3d + 6d`; in W4e,
  `3(M + M*) + M† + B = 3v + 1`; in both cases `M + M* + M† ≤ 9d`;
- `T`-family: `T + T* + T† = θ = 20d/9`, except in W4e, where `3(T + T*) + T† = 3θ` gives
  `≤ 20d/3`;
- `D + D* = d`, except in W4e, where `3D + D* = 3d`; `B + B* = 1`;
- `K₁ + K₂ ≤ P ≤ 6d`, only in W4r (0 elsewhere); `R_q ≤ 1` (counted with the state species);
- A-data: `A + 3A† + D*` and `A* + 3A*†` are conserved in μ2, with final values `(α + 1)d` and
  `d`; `A + A†`, `A* + A*†` are constant in all other windows of step `n`, at most `(α + 1)d`
  and `d`. So `A + A† + A* + A*† ≤ (α + 2)d`.
W4e gives the largest total: `3d + 9d + 20d/3 + 3d + 1 + (α + 2)d + 2 ≤ (α + 23.7)d + 3`; W4r
gives `≤ (α + 21.3)d + 3`. With `d ≥ 9`, `3 ≤ d/3`, so `|z| ≤ (α + 24)d`; and
`α + 24 ≤ 6.75(α + 1)` for `α ≥ 3`. ∎

**Lemma 14.4 (one window).** Let `ω ≥ 0` be a window of step `n` (`q_n ∉ Q_H`), started at
`Γ_{ω−1} + I` with the clock at `C₅` (for `ω = 0`: at `z₀`). Its real duration `D_ω`
satisfies `E[D_ω] ≤ 22.8 (α_n + 1)^5/(ρ_v k)`.

*Proof.* Unit-rate duration first. Use the statistic `(j, x, c)` of Lemma 8.2 (`j` = number of
work reactions so far, `x` the work state, `c` the clock), with expected occupation times
`w_{j,x}(c)` and `S_{j,x}(5) = Σ_c w_{j,x}(c)`. (1) Non-terminal work states: by the total
identity (FIX3 Lemma 2.1) and Lemma 8.3, `Σ_{j, x non-terminal} S_{j,x}(5) ≤ τ̄(Γ_{ω−1} + I)`.
(2) The terminal work state `x* = Γ_ω` (unique, Lemma 8.1): once it is reached, only clock moves
are enabled until the tick, and they do not change `x*`. By the strong Markov property at the
entrance time, the expected time spent there is `m(c) ≤ m(5)` of Lemma 14.2 for `x*`, where `c`
is the clock position at entrance. If the tick fires before `x*` is reached, part (2) is 0.
So the unit-rate duration has mean `≤ τ̄ + m_{x*}(5)`.

For `x*`: `Γ_{4n+1}, Γ_{4n+2}, Γ_{4n+3}` have `r = α + 1`, `f = d`, so
`m(5) ≤ (α+1)⁶/(α² d) ≤ (16/9)(α+1)⁴/d`. `Γ_{4n}` has `r = α`, and `f = d` or (after an
extension) `f = d/3`, so `m(5) ≤ 3α⁶/((α−1)² d) ≤ 3(α+1)⁴/d`, since
`α³ ≤ (α − 1)(α + 1)²` for `α ≥ 2`. (Here `α = α_n`, `d = d_n`; window 0 has `x* = Γ₀`, `r = i₀`,
`f = d₀`, `τ̄ = 0`.) Lemma 8.4 with `s_n ≤ α_n` and `ln(α+2) ≤ α`:
`d τ̄ ≤ 16(s + ln(α + 2)) ≤ 32α ≤ 0.375(α + 1)⁴` (as `32α/(α+1)⁴ ≤ 96/256` for `α ≥ 3`). So the
unit-rate mean is `≤ 3.375(α + 1)⁴/d`. Lemma 14.1 with Lemma 14.3:
`E[D_ω] ≤ (6.75(α + 1)d/(ρ_v k))·3.375(α + 1)⁴/d ≤ 22.8(α + 1)⁵/(ρ_v k)`. ∎

**Proof of Theorem 7.2.** Let `G_ω` be the event that the ticks `1, …, ω` all fire at terminal
work states, so `Err^c ⊆ G_ω`. Then `τ_{4n} = Σ_{ω < 4n} D_ω` and
`E[τ_{4n} 1_{Err^c}] ≤ Σ_{ω<4n} E[D_ω 1_{G_ω}]`. On `G_ω` the state at tick `ω` is
`Γ_{ω−1} + I` with the clock at `C₅` (§8.1), a deterministic state; by the strong Markov property
at tick `ω` (a.s. finite on `G_ω`: each earlier window has a.s. finitely many jumps),
`E[D_ω 1_{G_ω}] = P(G_ω) E_{Γ_{ω−1}+I}[D_ω] ≤ 22.8(α_m + 1)⁵/(ρ_v k)` for window `ω` of step `m`.
Four windows per step and `α_m + 1 = i₀ + m + 1 ≤ i₀ + n` for `m < n`:
`E[τ_{4n} 1_{Err^c}] ≤ 91.2 n (i₀ + n)⁵/(ρ_v k)`. Divide by `P(Err^c) ≥ 1 − δ > 0`
(Theorem 7.1(i)): `E[τ_{4n} | Err^c] ≤ 92 n (i₀ + n)⁵/((1 − δ) ρ_v k)`.

TM version: by Lemma X(a), after `t_tm` TM steps (none halting before) the TM configuration is
encoded at xCTM step `n = N_{t_tm} ≤ 6(s_tm + 1)t_tm`, i.e. in `Γ_{4n−1}`, present just before
tick `4n` on `Err^c`. With `i₀ = max(s₀, 1 + ⌈37/√δ⌉) ≤ 2 s_tm0 + 4 + 37/√δ` and the bound
increasing in `n`:
`E[τ_{4n} | Err^c] ≤ 552 (s_tm + 1) t_tm (37 δ^{−1/2} + 2 s_tm0 + 4 + 6 (s_tm + 1) t_tm)⁵ /
((1 − δ) ρ_v k)`. ∎

**Remarks.** (1) The paper's footnote 10 is the division by `P(Err^c)` above. (2) After
halting, every tick adds an idle `I`, so the volume grows by one per window; Theorem 7.2 stops at
the halting step and does not need a bound there. (3) Lemma 14.2's monotonicity is what the
first version of §10 left to be written; Lemma 14.4 uses it only through `m(c) ≤ m(5)`, and FIX3
Lemma 2.4 (which holds for every entry law) would give the same bound with the constant
`r/(r−1)` in place of the exact sum.

## 15. Error budget with `C₀ = 16` (Theorem 7.1(i))

Window `k` of step `n`, Lemma 8.2 with `l = 5`, `F = d_n`, and `b` from §8.3: `b = α_n` in
windows `4n` (μ1), `4n+2` (μ3) and `4n+3` (μ4), where the ratio `a/f` is `α_n` or `α_n + 1`
throughout; `b = α_n/3` only in window `4n+1` (μ2), and only after an extension. With
`μ_5(b) ≤ b^{−4}` and Lemma 8.4:

  `Σ_{k = 4n}^{4n+3} ε_k ≤ (3 + 81) α_n^{−4} · d_n · C₀ (s_n + ln(α_n + 2))/d_n
  = 84 C₀ (s_n + ln(α_n + 2))/α_n⁴ ≤ 168 C₀/α_n³`,

using `s_n ≤ s₀ + n ≤ i₀ + n = α_n` (`i₀ ≥ s₀`) and `ln(α + 2) ≤ α` for `α ≥ 2`. Window 0 has
`ε₀ = 0`. If `𝒞` halts at step `N`, window `4N` (μ1 of the halting step) is a W1 window with
`b = α_N`, `F = d_N` and is counted in the step-`N` term above; only the windows `k > 4N` have
`ε = 0`. The sum below runs over all `n ≥ 0` without truncation, so it covers window `4N`.
Summing,

  `P(Err) ≤ 168 C₀ Σ_{n ≥ 0} (i₀ + n)^{−3} ≤ 168 C₀ ∫_{i₀−1}^{∞} x^{−3} dx
  = 84 C₀/(i₀ − 1)² = 1344/(i₀ − 1)²`,

which is `≤ δ` when `i₀ ≥ 1 + √(1344/δ)`, in particular when `i₀ ≥ 1 + 37/√δ` (`37² = 1369`).
This is Theorem 7.1(i) as now stated. The first version (§9) charged every window with
`b = α_n/3`, giving `324 C₀/(i₀ − 1)²`; that bound is also valid, with `C₀ = 16` it reads
`5184/(i₀ − 1)²`.

Per CTM step the error is at most `168 C₀/(i₀ + n)³ = 2688/(i₀ + n)³`; the paper's target in A.5
is `1/(Θ(1/δ) + i)²`.

## 16. Status after this revision

PROVED (on paper; cold review `FIX3-SCWB-T41-REVIEW.md`: holds, corrections applied in §17):
Lemma X (§12), Lemma 8.4 with `C₀ = 16` (§13), Theorem
7.1 with `P(Err) ≤ 1344/(i₀−1)²` and `i₀ = max(s₀, 1 + ⌈37/√δ⌉)` (§15), Theorem 7.2 with
`E[τ_{4n} | Err^c] ≤ 92 n (i₀ + n)⁵/((1−δ) ρ_v k)` (§14), and the TM version of both.

Not claimed:
- The remarks labelled "unproved remark, not used" (§6 row 12, §9 last paragraph).
- Theorem 7.2 is a bound on the expected time given correctness, as in the paper; no
  unconditional time bound is claimed (after an error the tripling reactions can drive `#A`
  up, as the paper notes).
- Behaviour after halting (idle `I`'s, growing volume) is not analysed; it is not part of
  Theorem 4.1.


## 17. Review response

Cold review: `docs/audit/FIX3-SCWB-T41-REVIEW.md` (verdict: holds; one error, one gap,
slips; no constant or statement of Theorems 7.1, 7.2 changes).

| Item | Resolution |
|---|---|
| E1 (halting window: window `4N` is not zero-work, zero-error) | §13 *Conventions*: window `4N` (μ1 of the halting step) starts at `Γ_{4N−1} + I` and is a W1 window, `τ̄ ≤ (1+2h)/d_N`; only windows `k > 4N` have `τ̄ = 0`. §15: window `4N` has `b = α_N`, `F = d_N` and is already in the step-`N` term, since the sum over `n ≥ 0` is not truncated; only `k > 4N` have `ε = 0`. Theorem 7.2 uses windows `ω < 4n ≤ 4N` only and is unaffected. |
| G1 (finiteness of `S_{j,x}(l)` in Lemmas 8.2, 8.3) | §8.2 step 1: a path leaves level `(j, x)` by a work jump at most once (`j` only increases), so by Tonelli the expected number of such jumps is `ρ(x) S_{j,x}(l) ≤ 1`; hence `S_{j,x}(l) < ∞` for non-terminal `x` and the total identity applies. Lemma 8.3's proof cites this. |
| E2 (W1 aside: `A, A*` are not 0 in `Γ_{4n−1}` after a read step) | §13 W1 reworded: the reactants of `U`- and `X`-catalysed reactions are 0; after a read step `A, A*` are positive but `U` catalyses no A-reaction. |
| E3 (`ln(59/18) = 1.18717`) | §13 W2: written `≤ 1.188`; the constant `1 + 1.188 − 6.768 = −4.58` is unchanged. |
| Wording, §5 "clock species" | §5: the clock species excluded from the work state are `C₁, …, C₅`; `A, A†, A*, A*†` belong to the work state. |
| Wording, §3.2 "only `S_{·,2}`, `U`, `X` catalyse anything" | §3.2: "among the state species"; `T`, `M` catalyse the read and the A-species the clock. |
| Wording, §8.1 coexistence | §8.1: in each coexisting pair the old member either catalyses nothing or has no reactant left; the new member is the window's catalyst. |
| Unproved remarks | §6 row 12 ("the paper's unstarred version also works") and §9's last paragraph (`l ≥ 4` summability, `l = 4` choice) are labelled "unproved remark, not used"; the "iff" is reduced to "for `l ≥ 4`". |

## 18. Changelog

- 2026-11-09 (review). Applied the cold review `FIX3-SCWB-T41-REVIEW.md` (§17): E1 halting
  window in §13 and §15, G1 finiteness in §8.2/§8.3, E2, E3, wording in §3.2, §5, §8.1,
  unproved-remark labels in §6 row 12 and §9; §16 status updated. No constant or theorem
  statement changed.

- 2026-11-09. Closed the three OPEN items of the first version. Added §12 (Lemma X: explicit
  xCTM with seam slot and extension routines, exact step counts `2L+4`, `4L+10`, `4L+4`,
  `6L+12`, space `2 s_tm + 2`, proof and simulation check), §13 (Lemma 8.4 per window type,
  reusing T32 Lemmas 1.3, 1.4, 5.1, 5.4; new bounds for μ2 after an extension and for the
  extension μ4; `C₀ = 16`), §14 (Theorem 7.2: real-time conversion, tick-wait formula and its
  monotonicity, volume bound `(α_n + 24) d_n`, constant 92), §15 (error budget refined to
  `1344/(i₀−1)²`; `i₀ = max(s₀, 1 + ⌈37/√δ⌉)`), §16 (status). Updated the status table, §1
  (Lemma X statement), §4 and §6 row 16 (`i₀`), §7 (Theorems 7.1, 7.2 with explicit constants),
  §8.4 (statement with `C₀`), §9/§10 headings, §11 (ledger).
- 2026-11-08. First version (network, statement, logic, one-window bound, error budget given
  Lemma 8.4; OPEN: Lemma 8.4, Lemma X, time part).
- 2026-11-10 (Lean layer 2, `ClockedCTM/Unbounded.lean`): the §8.3 sentence that the clock ratio is exactly α_n or α_n + 1 outside the restoration right after an extension is false already during ordinary restoration (`ordinary_restore_ratio_counterexample`, kernel-checked); the window parameters used later are proved in their corrected form (`next_window_parameters`). Tick progress is not automatic (`clock_bounce_counterexample`); §8's almost-sure progress step must be proved in the probability layer.
