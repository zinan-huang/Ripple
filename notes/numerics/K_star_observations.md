# The Universal Constant K* ≈ 3.158 — Observations

## Setup (scaling limit)

Starting from the scalar cubic dual-rail with `p(y) = 1 − y³`, initial
condition `u(0) = U₀`, `v(0) = 0`, we rescale:

- `u(t) = U₀ · φ(τ)`, `v(t) = U₀ · ψ(τ)`, `τ = U₀² · t`
- `σ̃ = φ + ψ`, `ỹ = φ − ψ`, `K := k / U₀`

As `U₀ → ∞`, the `+1` forcing terms drop (they scale as `U₀⁻³`), and
we get a universal rescaled ODE:

```
σ̃' = σ̃³ − (K/2)(σ̃² − ỹ²)
ỹ' = −ỹ³
(σ̃, ỹ)(0) = (1, 1)
```

**Critical value numerically:** K* ≈ **3.1580** (converged to 4 digits
by binary search on U₀ ∈ {50, 100, 500}).

## Structural observations

### 1. `ỹ` is explicit
Integrating `ỹ' = −ỹ³` with `ỹ(0) = 1`:
```
ỹ(τ) = (1 + 2τ)^{−1/2}
ỹ²(τ) = 1 / (1 + 2τ)
```

So the system reduces to a **non-autonomous scalar ODE** for σ̃:
```
σ̃' = σ̃³ − (K/2) σ̃² + (K/2) · 1/(1 + 2τ)
```
i.e. a Riccati-like cubic with explicit rational forcing.

### 2. Fixed points of the (σ̃, ỹ) system
- `ỹ' = 0 ⇔ ỹ = 0`
- Then `σ̃' = σ̃²(σ̃ − K/2)`, zeros at σ̃ = 0 and σ̃ = K/2.
- So fixed points: `(0, 0)` (degenerate, on ỹ-nullcline) and `(K/2, 0)`.

### 3. Linearization at `(K/2, 0)`
Jacobian:
```
J = [[3σ̃² − Kσ̃,  Kỹ     ],
     [0,           −3ỹ²   ]]
J(K/2, 0) = [[K²/4, 0], [0, 0]]
```
Eigenvalues: **K²/4** (unstable in σ̃ direction) and **0** (center
along ỹ, since `ỹ' = −ỹ³` is super-stable at 0).

So `(K/2, 0)` is **non-hyperbolic** — semi-stable with a 1D center
manifold tangent to the ỹ-axis.

### 4. Dynamics interpretation

- For `K < K*`: trajectory starting at `(1, 1)` escapes past σ̃ = K/2
  to infinity (blow-up in finite τ).
- For `K > K*`: trajectory is "caught" — σ̃ overshoots but turns back,
  converges to `(K/2, 0)` along the center manifold.
- For `K = K*`: trajectory limits **exactly** to `(K/2, 0)` — lies on
  the stable manifold (here: center manifold, since eigenvalue is 0).

**K* is the K value where the initial point `(1, 1)` lies on the 1D
center manifold of the fixed point `(K*/2, 0)`.**

### 5. Where does 3.158 come from?

`K*/2 ≈ 1.579`. This is the asymptotic value σ̃(∞) of the separatrix.

Possible closed forms to check:
- `K* = 2·1.579 ≈ π` ? (π ≈ 3.14159... no, off by 0.016)
- `K* = √10 ≈ 3.16228` ? (close, differs by 0.004 — possibly numerical error?)
- `K*/2 = π²/(2e)` or similar combinations?
- Related to Airy function / Bessel / special function constants?

The non-autonomous cubic ODE
```
σ̃' = σ̃³ − (K/2)σ̃² + (K/2)/(1 + 2τ)
```
might be solvable in closed form via a substitution (e.g.
`σ̃ = w'/w · (−1/something)` Riccati-to-linear reduction, though this
is for quadratic Riccati, not cubic).

### 6. The 2D autonomous form

Using `τ`-substitution `s = ln(1 + 2τ)` or `u = 1/(1+2τ)`, the ODE
becomes autonomous. Let `u := ỹ² = 1/(1 + 2τ)`:
- `du/dτ = −2/(1+2τ)² = −2u²`
- `dτ/du = −1/(2u²)`
- `dσ̃/du = dσ̃/dτ · dτ/du = [σ̃³ − (K/2)(σ̃² − u)] · (−1/(2u²))`
- `= −[2σ̃³ − K(σ̃² − u)] / (4u²)`
- `= [K(σ̃² − u) − 2σ̃³] / (4u²)`

At `τ = 0`, `u = 1`. At `τ → ∞`, `u → 0`.

Initial `(σ̃, u) = (1, 1)`. Target as `u → 0`: σ̃ → K/2.

So **K* = 2·lim_{u→0⁺} σ̃(u)** where σ̃(u) starts at σ̃(1) = 1 and
obeys `dσ̃/du = [K(σ̃² − u) − 2σ̃³] / (4u²)`.

This is a BOUNDARY VALUE problem in `u ∈ (0, 1]`:
- IC: σ̃(1) = 1
- BC: σ̃(0⁺) = K/2 (the fixed point)

K* = value making these compatible.

### 7. Possible exact calculation

The cubic ODE is not elementary. Candidate special-function forms:
- Abel's equation (first/second kind)? The RHS is cubic in σ̃.
- `dσ̃/du = [K σ̃² - 2σ̃³]/(4u²)` when `u` is small. Here ỹ² term is negligible.
  Separable near u → 0: `dσ̃/(Kσ̃² − 2σ̃³) = du/(4u²)`, i.e.
  `dσ̃ / (σ̃²(K − 2σ̃)) = du/(4u²)`.
  LHS integral: partial fractions in `σ̃`.

So near `u → 0`, with σ̃ → K/2: linearize σ̃ = K/2 − ε.
`σ̃²(K − 2σ̃) ≈ (K/2)² · 2ε = K²ε/2`. So `dε/(−K²ε/2) = du/(4u²)`,
i.e. `d(ln ε)/du = −(1/(2u²))(·)... ` — need to work out.

This should yield the asymptotic approach rate of σ̃ to K/2.

### 8. Summary of what's needed

To get the **exact** closed form of K*, the problem reduces to solving
the BVP:
```
dσ̃/du = [K(σ̃² − u) − 2σ̃³] / (4u²)
σ̃(1) = 1
σ̃(0⁺) = K/2
```
on u ∈ (0, 1], and finding the unique K that makes both conditions hold.

The ODE is cubic (not quadratic Riccati), so a linear transformation
trick might not apply. Possibly amenable to:
- Painlevé classification
- Asymptotic matched expansions at u→0 and u→1
- Numerical shooting (what we've done) confirming K ≈ 3.158

If K* turns out to be algebraic (like K* = √10 or a root of a simple
polynomial), that would be a strong signal. If transcendental, it's
likely a nontrivial special function value.
