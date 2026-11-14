# The CF'24 protocol from interior initial conditions: global phase portrait

Status labels used below: **[proved]** = complete proof in this document (or an already
compiled Lean theorem, named); **[classical]** = a textbook theorem cited with its exact
hypotheses; **[numerical]** = checked by simulation only (the simulation scripts are not part
of the repository), not used in any proof; **[open]** = not proved.

Reference objects: `Ripple/LPP/CF24Example.lean` (`field`, `fixedPoint`, `saddlePoint`,
`lyapunov`, `cf24_global_solution`, `Cf24SaddleExcludedBasinEntry`), OPEN_PROBLEMS.md §6.3.

## 0. Claim

**The statement of §6.3 is false.** It is not true that every interior initial condition
off the stable manifold of the interior saddle gives readout limit (3 − √5)/6. The simplex
vertex e_c = (z00, z01, z11) = (0, 0, 1) is a **hyperbolic sink** (eigenvalues −2, −1), so it
owns a nonempty open basin of interior initial conditions, on which the readout
z11 + z01/2 tends to 1. Explicit counterexample: x0 = (1/200, 1/200, 99/100). Consequently
the Lean predicate `Cf24SaddleExcludedBasinEntry` is false (Theorem C). **[proved]**

**The true statement** (Theorem A, trichotomy). For every initial condition in the open
simplex the trajectory converges to exactly one of the three points fixedPoint, e_c,
saddlePoint, with readout limits (3 − √5)/6, 1, (3 + √5)/6 respectively. The first two
alternatives each occur on a nonempty open set; the third occurs exactly on the stable
manifold W^s(saddle), a C¹ curve. **[proved on paper, modulo two classical theorems:
Poincaré–Bendixson and Green's theorem; not in Lean]**

The corrected form of the §6.3 hypothesis is therefore

> for every interior x0: if the trajectory tends neither to saddlePoint nor to e_c, then it
> enters the sharp basin {V < (13 − 4√5)²/784} in finite time,

which is a consequence of Theorem A and is what remains open in Lean (§7).

## 1. Setup

Write a = z00, b = z01, c = z11. The field of `CF24.field` is

    a' = −2a² + 7ab − 2ac,
    b' = 2a² − 8ab + 16ac − bc,
    c' = ab − 14ac + bc.

Let Δ = {a, b, c ≥ 0, a + b + c = 1} (closed simplex) and Δ° its relative interior.

**Lemma 1.1 (global solutions, invariance). [proved: Lean]** For x0 ∈ Δ the solution exists
for all t ≥ 0, stays in Δ (`pivp_solution_nonneg`, `conservative_trajectory_simplex`), and if
x0 ∈ Δ° it stays in Δ° (`cf24_traj_simplex_interior`). The face {a = 0} is invariant since
a' = a·(−2a + 7b − 2c).

**Lemma 1.2 (reduction). [proved]** On the plane a + b + c = 1 (substitute c = 1 − a − b),

    a' = a(9b − 2),
    b' = 16a − b − 14a² − 23ab + b²  =: F₂(a, b).

Proof. −2a + 7b − 2c = −2a + 7b − 2 + 2a + 2b = 9b − 2. For b':
2a² − 8ab + 16a(1 − a − b) − b(1 − a − b) = 2a² − 8ab + 16a − 16a² − 16ab − b + ab + b²
= 16a − b − 14a² − 23ab + b². ∎

So the dynamics is the planar polynomial vector field F = (a(9b − 2), F₂) on the triangle
T = {a ≥ 0, b ≥ 0, a + b ≤ 1}, which is forward invariant (Lemma 1.1). The readout is
z11 + z01/2 = 1 − a − b/2.

## 2. Equilibria and their types

**Lemma 2.1. [proved]** F has exactly four zeros in T:
e_c = (0, 0) [= (0,0,1)], e_b = (0, 1) [= (0,1,0)], p⁺ = ((7+3√5)/18, 2/9) = fixedPoint,
p⁻ = ((7−3√5)/18, 2/9) = saddlePoint.

Proof. a(9b − 2) = 0 gives a = 0 or b = 2/9. If a = 0 then F₂ = −b + b² = b(b − 1), so
b ∈ {0, 1}. If b = 2/9 then F₂ = 16a − 2/9 − 14a² − 46a/9 + 4/81 = −14a² + (98/9)a − 14/81,
and multiplying by −81/14 gives 81a² − 63a + 1 = 0, a = (63 ± √(3969 − 324))/162
= (7 ± 3√5)/18. Both roots satisfy a > 0, a + 2/9 < 1. ∎

**Lemma 2.2 (linearization). [proved]** The Jacobian of F is

    DF(a, b) = [ 9b − 2            9a        ]
               [ 16 − 28a − 23b   −1 − 23a + 2b ].

* DF(e_c) = [[−2, 0], [16, −1]]: eigenvalues −2, −1. **e_c is a hyperbolic sink.**
* DF(e_b) = [[7, 0], [−7, 1]]: eigenvalues 7, 1. e_b is a hyperbolic source.
* p⁺: trace < 0, det > 0 (Lean `jacobianTrace_neg`, `jacobianDet_pos`): hyperbolic sink.
* p⁻: det < 0 (Lean `saddleJacobianDet_neg`), eigenvalues (−57+23√5 ± √disc)/12 ≈ 0.854, −1.783
  (Lean `saddleEigenvaluePositive_pos`, `saddleEigenvalueNegative_neg`): hyperbolic saddle.

Numerical check of all four spectra by simulation. **[numerical, consistent]**

## 3. The corner trapping region at e_c (elementary; Lean target)

Define the linear function **Φ(x) := 16a + b** (Lean: `cornerWeight`).

**Lemma 3.1 (Lie derivative). [proved]** Along the field, for any x with a + b + c = 1,

    Φ̇ := 16·field(x)₀ + field(x)₁ = −30a² + 104ab − 16ac − bc = −16a − b + 121ab − 14a² + b².

Proof. 16(−2a² + 7ab − 2ac) + (2a² − 8ab + 16ac − bc) = −30a² + 104ab − 16ac − bc. Substitute
c = 1 − a − b: −30a² + 104ab − 16a + 16a² + 16ab − b + ab + b² = −16a − b + 121ab − 14a² + b². ∎

**Lemma 3.2 (strict decrease on the corner). [proved]** If a ≥ 0, b ≥ 0, a + b + c = 1 and
Φ(x) = 16a + b ≤ 1/10, then Φ̇ ≤ −(1/8)·Φ(x).

Proof. From 16a + b ≤ 1/10 and a ≥ 0 we get b ≤ 1/10. Hence 121ab ≤ (121/10)a and
b² ≤ b/10, so
Φ̇ + Φ/8 = −14a − (7/8)b + 121ab − 14a² + b² ≤ −14a + 12.1a − (7/8)b + b/10 − 14a²
= −1.9a − 0.775b − 14a² ≤ 0. ∎
(Exact certificate: Φ̇ + Φ/8 = −121a(1/10 − b) − (19/10)a − b(1/10 − b) − (31/40)b − 14a².)

**Lemma 3.3 (invariance and exponential decay). [proved]** Let x0 ∈ Δ with a0 := x0₀ > 0 and
Φ(x0) ≤ 1/10, and let x(t) be the trajectory (Lemma 1.1). Then for all t ≥ 0

    Φ(x(t)) ≤ Φ(x0)·e^{−t/8}.

Proof. Fix T > 0. Step 1 (invariance of {Φ ≤ Φ(x0)} on [0, T]): apply the strict-barrier
lemma (Mathlib `image_le_of_deriv_right_lt_deriv_boundary`) with f(t) = Φ(x(t)),
f'(t) = Φ̇(x(t)), and the constant barrier B ≡ Φ(x0), B' ≡ 0. f is C¹ on [0, ∞) because the
trajectory is. At a touching time t ∈ [0, T) with f(t) = Φ(x0) we have x(t) ∈ Δ (Lemma 1.1)
and Φ(x(t)) = Φ(x0) ≤ 1/10, so Lemma 3.2 gives f'(t) ≤ −Φ(x0)/8 < 0 = B'(t), using
Φ(x0) ≥ 16a0 > 0. Hence Φ(x(t)) ≤ Φ(x0) on [0, T].
Step 2 (decay): on [0, T) we now have Φ(x(t)) ≤ 1/10, so by Lemma 3.2 f' ≤ −f/8 everywhere
on [0, T). The integrating factor φ(t) = f(t)e^{t/8} has φ' = (f' + f/8)e^{t/8} ≤ 0, so φ is
antitone and f(t) ≤ f(0)e^{−t/8} on [0, T] (Ripple `scalar_exponential_decay`). T was
arbitrary. ∎

**Corollary 3.4. [proved]** Under the hypotheses of Lemma 3.3, with Φ₀ := Φ(x0):
1. 0 ≤ a(t) ≤ Φ₀e^{−t/8}/16 and 0 ≤ b(t) ≤ Φ₀e^{−t/8}; hence a(t) → 0, b(t) → 0,
   c(t) = 1 − a − b → 1, i.e. x(t) → e_c, and the readout z11 + z01/2 → 1.
2. For all t ≥ 0, c(t) ≥ 1 − Φ(x(t)) ≥ 9/10, so with c* = (7 − 3√5)/18 < 7/18:
   c(t) − c* > 9/10 − 7/18 = 23/45 > 1/2 > (13 − 4√5)/28, hence
   V(x(t)) = (b − 2/9)² + (c − c*)² ≥ (c − c*)² > (13 − 4√5)²/784 (the sharp threshold).
3. x(t) does not tend to saddlePoint: b(t) → 0 ≠ 2/9 = saddlePoint₁.
4. The set {x ∈ Δ° : Φ(x) < 1/10} is a nonempty, relatively open subset of Δ° contained in
   the basin of e_c; it contains x0 = (1/200, 1/200, 99/100) (Φ = 17/200).

Proof. 1: a ≤ Φ/16, b ≤ Φ, squeeze; readout = c + b/2 → 1. 2: Φ(x(t)) ≤ Φ₀ ≤ 1/10 by Lemma
3.3 and a + b ≤ 16a + b. √5 > 0 gives c* < 7/18; (13 − 4√5)/28 < 13/28 < 1/2. Squaring
nonnegative numbers is monotone. 3: by 1 and uniqueness of limits. 4: Φ is continuous. ∎

**Theorem C (refutation). [proved]** `Cf24SaddleExcludedBasinEntry` is false.

Proof. Take x0 = (1/200, 1/200, 99/100) ∈ Δ°. By Corollary 3.4(3) the trajectory does not
tend to saddlePoint, so the predicate would give t₀ ≥ 0 with V(x(t₀)) < (13 − 4√5)²/784,
contradicting Corollary 3.4(2). ∎

Numerical check: from x0 the trajectory reaches (6.7e−15, −1.1e−13, 1.0) by t = 60, with
max a = 0.005, max b = 0.023 (simulation). **[numerical, consistent]**

## 4. The source e_b is never an ω-limit point of another orbit

Let s := a + c = 1 − b (so s(e_b) = 0 and s > 0 on Δ \ {e_b}).

**Lemma 4.1. [proved]** On Δ, ṡ = s + 7a + 14a² − 23as − s². If moreover s ≤ 1/10 then
ṡ ≥ (9/10)s + (47/10)a ≥ (9/10)s.

Proof. ṡ = −b' = b − 16a + 14a² + 23ab − b² with b = 1 − s:
(1 − s) − 16a + 14a² + 23a(1 − s) − (1 − s)² = s + 7a + 14a² − 23as − s². If s ≤ 1/10 then
a ≤ s ≤ 1/10, so 23as ≤ (23/10)a and s² ≤ s/10. ∎

**Lemma 4.2 (repelling sublevel sets). [proved]** Let η ∈ (0, 1/10] and x0 ∈ Δ with
s(x0) ≥ η. Then s(x(t)) ≥ η for all t ≥ 0.

Proof. Barrier lemma applied to f = −s(x(t)), constant barrier B ≡ −η: at a touching time
s(x(t)) = η > 0 and Lemma 4.1 gives ṡ ≥ (9/10)η > 0, i.e. f' < 0 = B'. ∎

**Corollary 4.3. [proved]** If x0 ∈ Δ \ {e_b} then e_b ∉ ω(x0).

Proof. η := min(s(x0), 1/10) > 0; by Lemma 4.2 the forward orbit lies in the closed set
{s ≥ η}, hence so does ω(x0), and s(e_b) = 0 < η. ∎

## 5. Dulac function: no periodic orbits, no homoclinic loops

**Lemma 5.1 (Dulac identity). [proved]** On {a > 0}, with B(a, b) := a^{−4/3},

    div(B·F) = ∂_a(a^{−4/3}·a(9b − 2)) + ∂_b(a^{−4/3}·F₂(a, b))
             = a^{−4/3}·(−1/3 − b − 23a).

In particular div(B·F) < 0 on {a > 0, b ≥ 0} ⊇ T ∩ {a > 0}.

Proof. ∂_a(a^{−1/3}(9b − 2)) = −(1/3)a^{−4/3}(9b − 2) = a^{−4/3}(−3b + 2/3).
∂_b F₂ = −1 − 23a + 2b. Sum: a^{−4/3}(−3b + 2/3 − 1 − 23a + 2b) = a^{−4/3}(−1/3 − b − 23a). ∎
(Finite-difference check at random points. **[numerical, consistent]**)

Remark (choice of exponent). With B = a^α one gets div(BF) = (11 + 9α)b − (3 + 2α) − 23a
times a^α; this is negative on the whole triangle exactly when −3/2 < α < −8/7. Integer
exponents do not work (α = −1: 2b − 1 − 23a; α = −2: 1 − 7b − 23a), which is why the
fractional power is needed.

**Lemma 5.2. [proved, using Green's theorem (classical)]** (i) F has no periodic orbit in T.
(ii) There is no homoclinic orbit to p⁻ in T (an orbit γ ⊂ T, γ ≠ {p⁻}, with α(γ) = ω(γ) = p⁻).

Proof. (i) Let γ ⊂ T be a periodic orbit. γ is not contained in the invariant face {a = 0}:
there b' = b(b − 1) ≤ 0, so b is monotone along orbits and no orbit is periodic except the
equilibria. Hence some point of γ has a > 0, and since a' = a·(9b − 2) the coordinate a is
positive along the whole orbit (a(t) = a(t₀)exp∫(9b − 2) > 0). γ is a C¹ Jordan curve; let D
be the bounded component of its complement. T is convex, so D ⊂ conv(γ) ⊂ T, and the linear
function a satisfies a ≥ min_γ a > 0 on conv(γ). Thus the closure of D lies in the open set
{a > 0} on which B·F is C¹. Green's theorem gives
∬_D div(B·F) dA = ∮_γ (B·F)·n ds = 0, since F (hence B·F) is tangent to γ. But the integrand
is strictly negative on D by Lemma 5.1, and D has positive area: contradiction.
(ii) Let γ be homoclinic to p⁻. p⁻ has a > 0, so by the same exponential formula a > 0 on
γ. The set γ ∪ {p⁻} is a Jordan curve, C¹ except at the single point p⁻ (where the two
ends enter along the stable and unstable eigendirections), so it is rectifiable and Green's
theorem applies to the bounded component D, whose closure again lies in {a > 0} by
convexity. The flux of B·F through γ is 0 (tangency) and B·F vanishes at p⁻, so the
boundary integral is 0 while ∬_D div(B·F) < 0: contradiction. ∎

## 6. Poincaré–Bendixson and the trichotomy

**Theorem (Poincaré–Bendixson, generalized form). [classical]** Let F be C¹ on an open set
E ⊂ ℝ², and let the forward orbit of x0 lie in a compact K ⊂ E containing finitely many
equilibria. Then ω(x0) is (a) a single equilibrium, or (b) a periodic orbit, or (c) a set
consisting of finitely many equilibria p₁, …, p_m together with orbits γ whose α- and
ω-limit sets are among p₁, …, p_m (and ω(x0) contains at least one such γ in case (c)).
Reference: Perko, *Differential Equations and Dynamical Systems*, 3rd ed., §3.7, Theorem 2.

**Lemma 6.1 (sinks capture). [proved]**
(i) If e_c ∈ ω(x0) for x0 ∈ Δ then x(t) → e_c.
(ii) If p⁺ ∈ ω(x0) for x0 ∈ Δ then x(t) → p⁺.

Proof. (i) U := {x ∈ Δ : Φ(x) < 1/10} is a relative neighbourhood of e_c in Δ. Since
e_c ∈ ω(x0), x(t₁) ∈ U for some t₁ ≥ 0. If a(t₁) = 0 the orbit lies in the invariant face,
where b' = b(b − 1) < 0 for b ∈ (0, 1), so b ↓ 0 and x(t) → e_c (or x0 = e_c). If a(t₁) > 0,
Lemma 3.3 applied from x(t₁) gives x(t) → e_c (Corollary 3.4(1)).
(ii) U := {x ∈ Δ : V(x) < (13 − 4√5)²/784} with V the Lean `lyapunov`. If V(x(t₁)) = 0 then
x(t₁) = p⁺ (V = 0 forces b = 2/9, c = c*, and a = 1 − b − c) and the orbit is constant.
Otherwise the Lean theorems `cf24_lyapunov_forward_invariant_sharp` (sublevel sets of V
below the threshold are forward invariant) and `cf24_lyapunov_tendsto_zero_sharp` (V → 0
there) apply from x(t₁), and V → 0 means b → 2/9, c → c*, a → 1 − 2/9 − c* = a⁺. ∎

**Theorem A (trichotomy). [proved on paper]** For every x0 ∈ Δ° exactly one of the following
holds:
(I)   x(t) → fixedPoint and z11 + z01/2 → (3 − √5)/6;
(II)  x(t) → e_c = (0, 0, 1) and z11 + z01/2 → 1;
(III) x(t) → saddlePoint and z11 + z01/2 → (3 + √5)/6.
Moreover (I) and (II) each hold on a nonempty open subset of Δ°.

Proof. The forward orbit lies in the compact T, F is polynomial on ℝ², and T contains
exactly four equilibria (Lemma 2.1), so Poincaré–Bendixson applies. ω(x0) ≠ ∅.
Case (b) is excluded by Lemma 5.2(i). In cases (a) and (c), ω(x0) contains an equilibrium.
If it contains p⁺ or e_c we are in (I) or (II) by Lemma 6.1 (and ω(x0) is that single
point). It cannot contain e_b by Corollary 4.3 (x0 ≠ e_b). So the only equilibrium in
ω(x0) is p⁻. In case (c) every non-equilibrium orbit γ ⊂ ω(x0) then has α(γ) = ω(γ) = p⁻,
i.e. is homoclinic, which Lemma 5.2(ii) excludes; so we are in case (a) with ω(x0) = {p⁻},
which is (III) because an orbit with compact closure and singleton ω-limit set converges.
Readout limits: continuity of 1 − a − b/2 at the three points (Lean `readout_fixedPoint`,
`readout_saddlePoint`; readout(e_c) = 1). Exclusivity: the three limits differ.
Openness and nonemptiness: (II) contains {Φ < 1/10} ∩ Δ° (Corollary 3.4(4)); (I) contains
the sharp basin {V < (13 − 4√5)²/784} ∩ Δ° (Lemma 6.1(ii)), nonempty since it contains a
neighbourhood of p⁺. ∎

**Corollary A′ (corrected §6.3 hypothesis). [proved on paper]** For x0 ∈ Δ°, if x(t) ↛
saddlePoint and x(t) ↛ e_c, then there is t₀ ≥ 0 with 0 < V(x(t₀)) < (13 − 4√5)²/784 or
V(x(t₀)) = 0 (the trajectory meets the sharp basin). Equivalently, the predicate obtained
from `Cf24SaddleExcludedBasinEntry` by adding the hypothesis
`¬ Tendsto traj atTop (nhds ![0,0,1])` is true; without it the predicate is false (Theorem C).

(The clause 0 < V is only there to match the existing Lean predicate; V(x(t₀)) = 0 happens
exactly when x0 = p⁺, which `cf24_basinEntry_fromSmallInit` already treats.)

**Geometry of the separatrix. [numerical]** W^s(p⁻) ∩ T is a curve from e_b through p⁻ to the
point ≈ (0.0398, 0, 0.9602) of the edge {b = 0}; the basin of e_c is the strip between this
curve and the face {a = 0}. W^u(p⁻): one branch tends to p⁺, the other to e_c
(simulation). By the stable manifold theorem W^s(p⁻) is a C¹ curve of measure zero, so
the basin of e_c is "small" but open; it is not negligible for the protocol: any population
started with at most ≈ 4 % agents in state 00 and most agents in state 11 converges to the
wrong answer 1.

## 7. Adversarial re-check (what could break the argument)

* Did I miss an equilibrium on the boundary? Lemma 2.1 solves the system exactly: a = 0
  forces b ∈ {0, 1}; a ≠ 0 forces b = 2/9 and a quadratic with the two interior roots. No.
* Is e_c really attracting in the full 3-variable system, not only after reduction? The
  simplex is invariant and the reduction is exact on it (Lemma 1.2); the Lean trajectory
  lives on the simplex (`conservative_trajectory_simplex`). Yes.
* Could the barrier argument of Lemma 3.3 fail at Φ(x0) = 1/10 exactly? No: the touching
  condition only needs Φ ≤ 1/10, and the strict inequality comes from Φ(x0) > 0.
* Does Poincaré–Bendixson need the flow to be complete on ℝ²? No: it is a statement about
  one forward orbit with compact closure in the domain of a C¹ field (Perko's formulation).
* Does case (c) allow a "cycle" through e_b or the sinks? Such a cycle would need an orbit
  with ω-limit e_b (impossible, Corollary 4.3) or an orbit leaving a sink (impossible). The
  only remaining graphs are homoclinic loops at p⁻, handled by Lemma 5.2(ii). The face
  orbits (from e_b to e_c along a = 0) cannot be in ω(x0) because e_b would be.
* Green's theorem for the homoclinic loop: the curve is a rectifiable Jordan curve (C¹
  except at one corner), the field B·F is C¹ on a neighbourhood of the closed domain
  (a ≥ min > 0 by convexity). Standard.
* The numerics were not used in any proof step; every inequality above is explicit.

## 8. Lean plan

Target file `Ripple/LPP/CF24Interior.lean`, importing `Ripple.LPP.CF24Example`, reusing
`field`, `cf24PIVP`, `cf24_global_solution`, `lyapunov`, `fixedPoint`, `saddlePoint`,
`Cf24SaddleExcludedBasinEntry`, `pivp_solution_nonneg`, `conservative_trajectory_simplex`,
Mathlib `image_le_of_deriv_right_lt_deriv_boundary`, Ripple `scalar_exponential_decay`.

Formalizable now (sections 3 and Theorem C), in dependency order:
1. `cornerWeight`, `cornerWeightDeriv`; `cornerWeightDeriv_eq` (Lemma 3.1, `ring`).
2. `cornerWeightDeriv_le_neg` (Lemma 3.2, `nlinarith` with the certificate).
3. `cf24_corner_trajectory_le` (Step 1 of Lemma 3.3, barrier lemma with constant B).
4. `cf24_corner_exp_bound` (Lemma 3.3, via `scalar_exponential_decay`, α = 1/8).
5. `cf24_corner_tendsto_vertex`, `cf24_corner_readout_tendsto_one` (Cor. 3.4(1)).
6. `cf24_corner_lyapunov_ge_sharp` (Cor. 3.4(2)), `cf24_corner_not_tendsto_saddle` (3.4(3)).
7. `cf24_saddleExcludedBasinEntry_false` (Theorem C).
Also formalizable: Lemma 5.1 as a `HasDerivAt` identity with `Real.rpow` (Dulac identity
and its sign), and Lemma 4.2 (repelling sublevel set at e_b) by the same barrier pattern.

**Lean status (2026-11-11).** Items 1–7 are compiled in `Ripple/LPP/CF24Interior.lean`;
Lemma 5.1 (`cf24_dulac`) and Lemma 4.2 (`cf24_source_repelling`) in `Ripple/LPP/CF24Dulac.lean`.
`#print axioms` of all nine headline theorems: `[propext, Classical.choice, Quot.sound]`. Theorem C is `cf24_saddleExcludedBasinEntry_false`.

Not formalizable without new infrastructure: Theorem A. It needs (a) ω-limit sets and the
Poincaré–Bendixson theorem for planar flows (absent from Mathlib), (b) Green's theorem on
Jordan domains (absent from Mathlib in the needed generality), (c) the stable manifold
theorem (absent). A Lean-feasible weakening that avoids all three is not visible: any proof
of Corollary A′ must rule out periodic orbits and homoclinic loops, which is planar
topology. The Lean deliverable therefore is Theorem C plus the explicit second basin; the
open item in OPEN_PROBLEMS §6.3 should be restated as Corollary A′ (status: proved on paper
by Poincaré–Bendixson + Dulac, not in Lean).
