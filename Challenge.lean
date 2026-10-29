module

public import Mathlib

@[expose] public section

/-!
# The two-qubit Hardy ladder: the closed form `P_K*(q)` and its unique maximiser for every `K`,
Hardy's optimum `φ⁻⁵` at `K = 1`, and the optimum `(8ρ² + ρ − 11)/25` in the cubic field `ℚ(ρ)`
at `K = 2`

This file is the statement of record. It imports only Mathlib, uses no definition of its own, and
states every compared theorem with its formula written out. Comparator checks that
`Solution.lean` proves exactly the thirty theorems stated here, using only the axioms
`propext`, `Quot.sound` and `Classical.choice`.

## Setting

A two-qubit pure state in Schmidt form `c₀|00⟩ + c₁|11⟩` (`c₀, c₁ > 0`, `c₀² + c₁² = 1`) is
measured by two parties with real projective measurements: party A's `k`-th measurement has
outcome `1` along `(cos aₖ, sin aₖ)` and outcome `0` along `(−sin aₖ, cos aₖ)`, party B's along
`(cos bₖ, sin bₖ)` and `(−sin bₖ, cos bₖ)`. The joint probabilities are the squared real amplitudes

* `P(Aⱼ = 1, Bⱼ = 1) = (c₀ cos aⱼ cos bⱼ + c₁ sin aⱼ sin bⱼ)²`,
* `P(Aₖ₊₁ = 1, Bₖ = 0) = (c₀ cos aₖ₊₁ (−sin bₖ) + c₁ sin aₖ₊₁ cos bₖ)²`,
* `P(Aₖ = 0, Bₖ₊₁ = 1) = (c₀ (−sin aₖ) cos bₖ₊₁ + c₁ cos aₖ sin bₖ₊₁)²`.

In Lean the state, the measurements and the probabilities are not modelled as Hilbert-space
objects: each probability is the squared real amplitude above, written out in the statements, and
reading these expressions as quantum probabilities is the informal account.

The `K`-step Hardy ladder (Hardy 1993 for `K = 1`; Hardy 1997 and Boschi, Branca, De Martini and
Hardy 1997)
imposes `P(A₀ = 1, B₀ = 1) = 0` and, for `k < K`, `P(Aₖ₊₁ = 1, Bₖ = 0) = 0` and
`P(Aₖ = 0, Bₖ₊₁ = 1) = 0`; its figure of merit is `P(A_K = 1, B_K = 1)`, which a local realistic
model must assign `0`. With `q = c₁/c₀`, the closed form

  `P_K*(q) = q² (1 − q^{2K})² / ((1 + q²)(1 + q^{2K+1})²)`

is the value of `P(A_K = 1, B_K = 1)` optimised over the real measurement angles at fixed state
(statements 1–2). Statements 3–4 state that for every `K` the ladder probability is below `1/2`,
and that `1/2` is approached as `K` grows. Statements 5–8 concern the function `P_K*` and
Cereceda's polynomial

  `m_K(x) = x^{4K+3} − (1 + 2K) x^{2K+3} − 2K x^{2K+2} − 2K x^{2K+1} − (1 + 2K) x^{2K} + 1`

(statement 5 on `q > 0`, statements 6–8 on `(0, 1)`), and statements 12, 14–15 and 20–23 concern
`P₁*` and `P₂*` on `(0, 1)` (statements 13 and 19 are about `φ` and `ρ` alone); the maximum of
`P_K*` on `(0, 1)` is the optimum of the `K`-step ladder over Schmidt states with `c₁ < c₀` and
real settings. The passage to every Schmidt ratio uses the symmetry `P_K*(1/q) = P_K*(q)`
(Cereceda 2002, below Table 1; p. 4 of arXiv v4), proved in the library as
`HardyLadder.ladderValue_inv` (uncompared); it enters the proofs of statements 3, 9, 11, 16, 18,
24 and 26, and not those of the attainment statements 10, 17 and 25. Statements 9–11 (every
`K ≥ 1`), 16–18 (`K = 1`) and 24–26 (`K = 2`) state the optima over every two-qubit Schmidt state
and real settings, end to end in the ladder probabilities: the bound, its attainment at one
optimal state (for every `K`, at the Schmidt ratio `r`), and the condition every optimal state
satisfies (for every `K`, Schmidt ratio `r` or `r⁻¹`). That the swapped state (ratio `r⁻¹`) also
attains the optimum follows from the symmetry and is not a compared statement. That complex
settings do no better is not formalised. Below, "optimum" means this real-settings optimum.

## The thirty statements (namespace `HardyLadder.Entry`)

Every `K` — the closed form, below one half, and the maximiser:

1. `ladder_prob_le` — under the `K`-step ladder constraints, `P(A_K = 1, B_K = 1) ≤ P_K*(c₁/c₀)`.
2. `ladder_prob_attained` — for every `K` and every normalised `c₀, c₁ > 0` the bound is attained
   by some measurement angles satisfying the constraints.
3. `ladder_prob_lt_half` — under exactly the hypotheses of statement 1,
   `P(A_K = 1, B_K = 1) < 1/2`.
4. `ladder_prob_approaches_half` — for every `ε > 0` there is `K₀` such that for every `K ≥ K₀`
   some normalised Schmidt state `c₀, c₁ > 0` and some angles satisfying the `K`-step constraints
   give `P(A_K = 1, B_K = 1) > 1/2 − ε`. With statement 3: over all `K`, all Schmidt states and
   all real settings, the supremum of the ladder probability is `1/2`, and it is not attained.
5. `hasDerivAt_ladder_value` — for `q > 0`,
   `d/dq P_K*(q) = 2q (1 − q^{2K}) m_K(q) / ((1 + q²)² (1 + q^{2K+1})³)`.
6. `existsUnique_mK_root` — for `K ≥ 1`, `m_K` has exactly one zero `r` in `(0, 1)`.
7. `ladder_value_isGreatest_of_mK_root` — for `K ≥ 1`, if `r ∈ (0, 1)` and `m_K(r) = 0`, then
   `P_K*(r)` is the greatest value of `P_K*` on `(0, 1)`.
8. `eq_of_ladder_value_eq_of_mK_root` — for such `r`, every `q ∈ (0, 1)` with
   `P_K*(q) = P_K*(r)` is `r`: the maximiser on `(0, 1)` is unique.
9. `ladder_prob_le_of_mK_root` — for such `r`, under the `K`-step constraints and for every
   Schmidt state, `P(A_K = 1, B_K = 1) ≤ P_K*(r)`.
10. `ladder_prob_attained_of_ratio` — for every `K` and `r > 0`, some state with `c₁/c₀ = r` and
    some angles satisfying the `K`-step constraints give `P(A_K = 1, B_K = 1) = P_K*(r)`; at the
    zero `r` of `m_K` this is the optimum of statement 9.
11. `ratio_of_ladder_prob_eq_of_mK_root` — for `r` as in statement 9, every configuration with
    `P(A_K = 1, B_K = 1) = P_K*(r)` has `c₁/c₀ = r` or `c₁/c₀ = r⁻¹`.

`K = 1` (Hardy's value):

12. `hardy_K1_isGreatest` — `φ⁻⁵` is the greatest value of `P₁*` on `(0, 1)` (`φ` is Mathlib's
    `Real.goldenRatio`).
13. `hardy_value_eq` — `φ⁻⁵ = (5√5 − 11)/2`.
14. `hardy_K1_eq_iff_quartic` — for `q ∈ (0, 1)`, `P₁*(q) = φ⁻⁵` iff
    `q⁴ − 3q³ + 3q² − 3q + 1 = 0`.
15. `hardy_K1_existsUnique` — the maximiser of `P₁*` on `(0, 1)` is unique.
16. `ladder_K1_le` — under the one-step constraints, `P(A₁ = 1, B₁ = 1) ≤ φ⁻⁵`.
17. `ladder_K1_attained` — some state with `2c₀c₁ = 3 − √5` (Hardy's condition) and some angles
    satisfying the one-step constraints give `P(A₁ = 1, B₁ = 1) = φ⁻⁵`.
18. `ladder_K1_hardy_condition_of_eq` — every configuration with `P(A₁ = 1, B₁ = 1) = φ⁻⁵` has
    `2c₀c₁ = 3 − √5`.

`K = 2` (the plastic number `ρ`, the real root of `x³ − x − 1`):

19. `existsUnique_cubic` — `x³ = x + 1` has exactly one real solution (so the hypothesis
    `ρ³ = ρ + 1` below pins `ρ`).
20. `hardy_K2_isGreatest` — `(8ρ² + ρ − 11)/25` is the greatest value of `P₂*` on `(0, 1)`.
21. `hardy_K2_eq_iff_inv_sq` — for `q ∈ (0, 1)`, `P₂*(q) = (8ρ² + ρ − 11)/25` iff `q = ρ⁻²`.
22. `hardy_K2_eq_iff_cubic` — for `q ∈ (0, 1)`, `P₂*(q) = (8ρ² + ρ − 11)/25` iff
    `q³ − q² + 2q − 1 = 0` (the stationarity cofactor, a factor of Cereceda's `m₂(x)`, eq. (20)).
23. `hardy_K2_existsUnique` — the maximiser of `P₂*` on `(0, 1)` is unique.
24. `ladder_K2_le` — under the two-step constraints, `P(A₂ = 1, B₂ = 1) ≤ (8ρ² + ρ − 11)/25`.
25. `ladder_K2_attained` — some state with Schmidt weights `c₀² = ρ⁻¹`, `c₁² = ρ⁻⁵` and some angles
    satisfying the two-step constraints give `P(A₂ = 1, B₂ = 1) = (8ρ² + ρ − 11)/25`.
26. `ladder_K2_weights_of_eq` — every configuration with `P(A₂ = 1, B₂ = 1) = (8ρ² + ρ − 11)/25`
    has Schmidt weights `{c₀², c₁²} = {ρ⁻¹, ρ⁻⁵}`.

The arithmetic of the `K = 2` value:

27. `minpoly_value` — the minimal polynomial of `(8ρ² + ρ − 11)/25` over `ℚ` is
    `x³ + (17/25) x² + (2/25) x − 1/25`.
28. `finrank_adjoin_value` — `[ℚ((8ρ² + ρ − 11)/25) : ℚ] = 3`.
29. `irreducible_25` — `25x³ + 17x² + 2x − 1` is irreducible over `ℚ` (the hypothesis
    `ρ³ = ρ + 1` does not enter the conclusion; by statement 19 it is satisfiable).
30. `exists_nonreal_root_minpoly_value` — the minimal polynomial of `(8ρ² + ρ − 11)/25` over `ℚ`
    has a root `z ∈ ℂ` with `z.im ≠ 0`: read with statement 27, the `K = 2` value has a non-real
    conjugate, i.e. it is not totally real.

Given statements 12 and 20, which identify the maximum values, statements 14–15 and 22–23 follow
from the `K = 1` and `K = 2` cases of statements 6–8: Cereceda's polynomials factor as
`m₁(x) = (x + 1)³(x⁴ − 3x³ + 3x² − 3x + 1)` and
`m₂(x) = (x + 1)³(x² + 1)(x³ − 2x² + x − 1)(x³ − x² + 2x − 1)` (library lemmas
`HardyLadder.cerecedaM_one`, `HardyLadder.cerecedaM_two`), the other factors have no zero in
`(0, 1)`, and the factor carrying the zero in `(0, 1)` is the quartic of statement 14 and the cubic
of statement 22. Statement 23 also follows directly from statement 21, since `ρ⁻² ∈ (0, 1)`. They
are kept as separate statements, proved separately in the library through `s = q + 1/q`, because
they give the maximiser's polynomial and its uniqueness at the closed-form values `φ⁻⁵` and
`(8ρ² + ρ − 11)/25`.

## How to read the statements

* Measurement angles are functions `a b : ℕ → ℝ`; only `a 0, …, a K` and `b 0, …, b K` enter.
* The constraints are stated as vanishing probabilities (squared amplitudes), as in the ladder
  papers; the objective is the squared amplitude `P(A_K = 1, B_K = 1)`. Statements 1–4, 9–11,
  16–18 and 24–26 write the constraints and the objective out in this form (at `K = 1` in 16–18
  and `K = 2` in 24–26).
* In statements 5–9 and 11, `m_K(x)` is written out as Cereceda prints it (eq. (20)), with the
  natural number `K` cast to `ℝ` in the coefficients `1 + 2K` and `2K`; statement 5 uses Mathlib's
  `HasDerivAt f f' q` (`f` has derivative `f'` at `q`).
* Statements 7, 12 and 20 use Mathlib's `IsGreatest s m` (`m ∈ s` and `m` bounds `s`) on the image
  of `Set.Ioo 0 1` under `P_K*`; statements 6, 15, 19 and 23 use `∃!`.
* Statement 4 is written with `∃` and `∀` (`∀ K ≥ K₀` on `ℕ`); no limit, filter or supremum
  is written in it.
* `ρ` enters statements 20–30 as a real number with `ρ ^ 3 = ρ + 1`; by statement 19 there
  is exactly one such real number, `ρ = 1.3247…`.
* Statements 27 and 30 use Mathlib's `minpoly ℚ`: the monic minimal polynomial of an algebraic
  number, and `0` for a non-algebraic one. The `K = 2` value is algebraic (of degree 3), and
  statement 27 names its minimal polynomial as the monic cubic; the primitive integer form is
  statement 29. In statement 30, `aeval z p` evaluates the rational polynomial `p` at the complex
  number `z`. Read with statement 27, statement 30 says that a complex root of that cubic, that is,
  a conjugate of the `K = 2` value, lies off the real line, i.e. the value is not totally real
  (for the zero polynomial statement 30 would hold trivially; statement 27 rules this out, and the
  `z` of statement 30 is a root of `25x³ + 17x² + 2x − 1`).

## Attribution
Statement 3, that the ladder probability is below `1/2` for every `K`, is the two-qubit,
real-settings, Schmidt-form case of a stronger bound that follows from known results: Cereceda
(Quantum Inf. Process. 15, 1779, 2016, eqs. (8)–(9)) combines the no-signalling identity
`CHSH_K = 2K + 4P_K` with Wehner's chained-CHSH Tsirelson bound for ±1 observables (PRA 73,
022110, 2006) to get `P_K ≤ L_K = ¼[2(K + 1)cos(π/(2K + 2)) − 2K]`, and `L_K < 1/2` because the
cosine is below 1. Cereceda states his setting as two qubits, but neither step uses the
dimension, so the bound holds for any state and any ±1 observables in every dimension (this
inference, and `L_K < 1/2`, are drawn here; Cereceda prints `P_K ≤ L_K` and that `L_K` tends to
`0.5`). No-signalling alone allows exactly `1/2` for every `K`
(Cereceda, Adv. Stud. Theor. Phys. 9, 433, 2015). That
`1/2` is approached for large `K` (statement 4) is Hardy's (1997) and Boschi, Branca, De Martini
and Hardy's (1997), whose two-qubit ladder uses equal settings (unequal real settings are Cereceda
2002, eq. (18)); in the words of Cereceda (2002, after eq. (19)), "the maximum value of P_K is
(50 − δ)% which is realized for K → ∞ and a state that is not quite maximally entangled", which
also gives the two-qubit, equal-settings case of statement 3.
The `K = 1` value `½(5√5 − 11)`, with the maximiser `2|αβ| = 3 − √5` (i.e. `q + 1/q = φ²`), is
Hardy's (PRL 71, 1665, 1993, p. 1667); the form `τ⁻⁵`, `τ` the golden mean, is in Mermin (Physics
Today 47(6), 9, 1994, p. 11) and Cereceda (Found. Phys. Lett. 14, 401, 2001). The closed form
`P_K*(q)` is Cereceda's eq. (19) (J. Phys. A 35, 9105, 2002), equivalently half his eq. (33) in
`x = α/β`, attributed there to Hardy (1997) and Boschi et
al. (1997); Cereceda shows that equal settings are optimal (eq. (18)), characterises the
maximisers as the non-trivial real roots of a polynomial `m_K(x)` (eq. (20)), and tabulates the
optima to three decimals for `K = 1, …, 10` (Table 1: `0.090` at `K = 1`, `0.174` at `K = 2`;
`0.17455` appears as `0.174`). The `m_K` of statements 5–9 and 11 is Cereceda's eq. (20)
coefficient for coefficient; his variable is `x = α/β`, ours `q = c₁/c₀`, and `m_K` is palindromic
(`x^{4K+3} m_K(1/x) = m_K(x)`), so both readings have the same zeros. The quartic of statement 14
is the `K = 1` factor of `m₁(x) = (x + 1)³(x⁴ − 3x³ + 3x² − 3x + 1)`, and the cubic of statement 22
is a factor of `m₂(x) = (x + 1)³(x² + 1)(x³ − 2x² + x − 1)(x³ − x² + 2x − 1)`, which the paper does
not factor beyond noting the triple root `−1` and that the other `4K − 2` roots are complex
(footnote, p. 4).
The uniqueness of the maximiser on `(0, 1)` (statements 6–8 for every `K ≥ 1`; statements 15 and
23 at `K = 1, 2`) is in print: for every `K` Cereceda states it without proof (2002, p. 4: the
maximisers are the two non-trivial real roots `r₁ < 1 < r₂ = 1/r₁` of `m_K`, "It can be shown"; by
the footnote the other roots are `−1` and complex), and no printed proof of it for `K ≥ 2` was found
in the literature searched (search dated 2026-10-29; the bodies of Hardy 1997 and Boschi et al.
1997 were not opened); for `K = 1` Mermin states it (1994, p. 11,
in his parametrisation: "Maximizing (6) gives uniquely p_l = p_r = (√5 − 1)/2 = 1/τ"); in every
dimension, any state attaining the `K = 1` value is equivalent up to local isometries to the
two-qubit optimal state (self-testing: Rabelo, Zhi and Scarani, PRL 109, 180401, 2012). The
formal proof of statements 5–8 given here is the derivative identity of statement 5 with
`m_K(x) = 1 − x^{2K} g_K(x)`, `g_K(x) = (1 + 2K) + 2Kx + 2Kx² + (1 + 2K)x³ − x^{2K+3}`, where on
`[0, 1]` both `g_K` and `g_K'` are positive, so `m_K` decreases strictly from `1` to `−8K`.
To five digits the optima are
`0.09017` and `0.17455` (Meng et al., PRA 98, 062103, 2018, Table I), and to six `0.090169` and
`0.174550` (Cereceda, Quantum Stud. Math. Found. 4, 205, 2017, Table 1; `0.174550` also in Yang,
Zhang and Chen, PRA 110, 012441, 2024, Table I); Cabello (PRA 58, 1687,
1998) quotes `17.5 %` at `K = 2` from Hardy (1997) and Boschi, Branca, De Martini and Hardy (1997).
In the literature and repositories searched (search dated 2026-10-28) we found no statement of the
identification of the `K = 2` stationarity root as `ρ⁻²` (`ρ` the plastic number; the root itself
is OEIS A357471, with no mention of either the plastic number or Hardy's ladder), of the closed
form `(8ρ² + ρ − 11)/25` with minimal polynomial `25x³ + 17x² + 2x − 1`, or of the Schmidt weights
`ρ⁻¹`, `ρ⁻⁵`; this is a search result, not a proof of absence (the bodies of Hardy 1997 and Boschi
et al. 1997 were not opened).
Statement 30 records that the `K = 2` value is not totally real; with statement 27 it is the
consequence of the negative discriminant `−23³` of `25x³ + 17x² + 2x − 1` (computer algebra, not
formalised), and it records the contrast with the `K = 1` value. Its field is the cubic field
`ℚ(ρ)` (LMFDB 3.1.23.1: `x³ − x² + 1`, signature `(1, 1)`, discriminant `−23`; that
`ℚ((8ρ² + ρ − 11)/25) = ℚ(ρ)` follows from statement 28, since the value lies in `ℚ(ρ)` and both
fields have degree `3`, and is not formalised), whereas the `K = 1` value lies in the totally real
field `ℚ(√5)` (not formalised). Nothing in this file asserts anything about physics beyond these
identities, inequalities and a derivative of real expressions and facts about polynomials and a
cubic field.
-/

namespace HardyLadder.Entry

open Real Polynomial

/-- **The closed-form bound.** For a two-qubit state `c₀|00⟩ + c₁|11⟩` (`c₀, c₁ > 0`,
`c₀² + c₁² = 1`) and real measurement angles satisfying the `K`-step ladder constraints,
`P(A_K = 1, B_K = 1) ≤ P_K*(c₁/c₀) = q² (1 − q^{2K})² / ((1 + q²)(1 + q^{2K+1})²)`. -/
theorem ladder_prob_le (K : ℕ) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) :
    (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 ≤
      (c₁ / c₀) ^ 2 * (1 - (c₁ / c₀) ^ (2 * K)) ^ 2 /
        ((1 + (c₁ / c₀) ^ 2) * (1 + (c₁ / c₀) ^ (2 * K + 1)) ^ 2) := by
  sorry

/-- **The bound is attained.** For every `K` and every normalised `c₀, c₁ > 0` there are
measurement angles satisfying the `K`-step ladder constraints with
`P(A_K = 1, B_K = 1) = P_K*(c₁/c₀)`. -/
theorem ladder_prob_attained (K : ℕ) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) :
    ∃ a b : ℕ → ℝ,
      (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0 ∧
      (∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
        c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0) ∧
      (∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
        c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) ∧
      (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 =
        (c₁ / c₀) ^ 2 * (1 - (c₁ / c₀) ^ (2 * K)) ^ 2 /
          ((1 + (c₁ / c₀) ^ 2) * (1 + (c₁ / c₀) ^ (2 * K + 1)) ^ 2) := by
  sorry

/-- **Below one half, for every `K`.** Under exactly the hypotheses of statement 1,
`P(A_K = 1, B_K = 1) < 1/2`. This is the two-qubit, real-settings, Schmidt-form case of a
stronger bound that follows from Cereceda 2016, eq. (9), with Wehner 2006 (any state, any ±1
observables, any dimension; the inference is drawn here, see the attribution above); for two
qubits and equal settings it is in Hardy 1997 and Boschi, Branca, De Martini and Hardy 1997, as
quoted by Cereceda 2002 after eq. (19), and unequal real settings are Cereceda 2002, eq. (18). -/
theorem ladder_prob_lt_half (K : ℕ) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) :
    (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 < 1 / 2 := by
  sorry

/-- **One half is approached** (Hardy 1997; Boschi, Branca, De Martini and Hardy 1997; as quoted
by Cereceda 2002 after eq. (19)). For every `ε > 0` there is `K₀` such that for every `K ≥ K₀`
some normalised Schmidt state `c₀, c₁ > 0` and some angles satisfying the `K`-step ladder
constraints give `P(A_K = 1, B_K = 1) > 1/2 − ε`. -/
theorem ladder_prob_approaches_half {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ c₀ ^ 2 + c₁ ^ 2 = 1 ∧
      ∃ a b : ℕ → ℝ,
        (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0 ∧
        (∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
          c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0) ∧
        (∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
          c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) ∧
        1 / 2 - ε < (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 := by
  sorry

/-- **The derivative of the closed form, every `K`.** For `q > 0`,
`d/dq P_K*(q) = 2q (1 − q^{2K}) m_K(q) / ((1 + q²)² (1 + q^{2K+1})³)`, where
`m_K(x) = x^{4K+3} − (1 + 2K) x^{2K+3} − 2K x^{2K+2} − 2K x^{2K+1} − (1 + 2K) x^{2K} + 1` is
Cereceda's polynomial (J. Phys. A 35, 9105, 2002, eq. (20)), written out. -/
theorem hasDerivAt_ladder_value (K : ℕ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt
      (fun x : ℝ => x ^ 2 * (1 - x ^ (2 * K)) ^ 2 / ((1 + x ^ 2) * (1 + x ^ (2 * K + 1)) ^ 2))
      (2 * q * (1 - q ^ (2 * K)) *
          (q ^ (4 * K + 3) - (1 + 2 * K) * q ^ (2 * K + 3) - 2 * K * q ^ (2 * K + 2) -
            2 * K * q ^ (2 * K + 1) - (1 + 2 * K) * q ^ (2 * K) + 1) /
        ((1 + q ^ 2) ^ 2 * (1 + q ^ (2 * K + 1)) ^ 3)) q := by
  sorry

/-- **Cereceda's `m_K` has exactly one zero in `(0, 1)`, for every `K ≥ 1`**:
`m_K(r) = r^{4K+3} − (1 + 2K) r^{2K+3} − 2K r^{2K+2} − 2K r^{2K+1} − (1 + 2K) r^{2K} + 1`
(Cereceda 2002, eq. (20)). -/
theorem existsUnique_mK_root (K : ℕ) (hK : 1 ≤ K) :
    ∃! r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 ∧
      r ^ (4 * K + 3) - (1 + 2 * K) * r ^ (2 * K + 3) - 2 * K * r ^ (2 * K + 2) -
        2 * K * r ^ (2 * K + 1) - (1 + 2 * K) * r ^ (2 * K) + 1 = 0 := by
  sorry

/-- **The maximum of `P_K*` on `(0, 1)` is its value at the zero of `m_K`, for every `K ≥ 1`.**
If `r ∈ (0, 1)` and `m_K(r) = 0`, then `P_K*(r)` is the greatest value of
`P_K*(q) = q² (1 − q^{2K})² / ((1 + q²)(1 + q^{2K+1})²)` on `(0, 1)`. -/
theorem ladder_value_isGreatest_of_mK_root (K : ℕ) (hK : 1 ≤ K) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hm : r ^ (4 * K + 3) - (1 + 2 * K) * r ^ (2 * K + 3) - 2 * K * r ^ (2 * K + 2) -
      2 * K * r ^ (2 * K + 1) - (1 + 2 * K) * r ^ (2 * K) + 1 = 0) :
    IsGreatest ((fun q : ℝ => q ^ 2 * (1 - q ^ (2 * K)) ^ 2 /
        ((1 + q ^ 2) * (1 + q ^ (2 * K + 1)) ^ 2)) '' Set.Ioo 0 1)
      (r ^ 2 * (1 - r ^ (2 * K)) ^ 2 / ((1 + r ^ 2) * (1 + r ^ (2 * K + 1)) ^ 2)) := by
  sorry

/-- **The maximiser on `(0, 1)` is unique, for every `K ≥ 1`.** If `r ∈ (0, 1)`, `m_K(r) = 0`, and
`q ∈ (0, 1)` has `P_K*(q) = P_K*(r)`, then `q = r`. -/
theorem eq_of_ladder_value_eq_of_mK_root (K : ℕ) (hK : 1 ≤ K) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hm : r ^ (4 * K + 3) - (1 + 2 * K) * r ^ (2 * K + 3) - 2 * K * r ^ (2 * K + 2) -
      2 * K * r ^ (2 * K + 1) - (1 + 2 * K) * r ^ (2 * K) + 1 = 0)
    {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (heq : q ^ 2 * (1 - q ^ (2 * K)) ^ 2 / ((1 + q ^ 2) * (1 + q ^ (2 * K + 1)) ^ 2) =
      r ^ 2 * (1 - r ^ (2 * K)) ^ 2 / ((1 + r ^ 2) * (1 + r ^ (2 * K + 1)) ^ 2)) :
    q = r := by
  sorry

/-- **The `K`-step bound over every Schmidt state, every `K ≥ 1`.** If `r ∈ (0, 1)` and
`m_K(r) = 0`, then for every `c₀, c₁ > 0` with `c₀² + c₁² = 1` (either order) and real angles
satisfying the `K`-step ladder constraints, `P(A_K = 1, B_K = 1) ≤ P_K*(r)`. -/
theorem ladder_prob_le_of_mK_root (K : ℕ) (hK : 1 ≤ K) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hm : r ^ (4 * K + 3) - (1 + 2 * K) * r ^ (2 * K + 3) - 2 * K * r ^ (2 * K + 2) -
      2 * K * r ^ (2 * K + 1) - (1 + 2 * K) * r ^ (2 * K) + 1 = 0)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) :
    (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 ≤
      r ^ 2 * (1 - r ^ (2 * K)) ^ 2 / ((1 + r ^ 2) * (1 + r ^ (2 * K + 1)) ^ 2) := by
  sorry

/-- **Every value `P_K*(r)`, `r > 0`, is attained at the Schmidt ratio `r`.** Some state with
`c₁/c₀ = r` and some real angles satisfying the `K`-step ladder constraints give
`P(A_K = 1, B_K = 1) = P_K*(r)`; at the zero `r` of `m_K` in `(0, 1)` this attains the bound of
statement 9. -/
theorem ladder_prob_attained_of_ratio (K : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ c₀ ^ 2 + c₁ ^ 2 = 1 ∧ c₁ / c₀ = r ∧
      ∃ a b : ℕ → ℝ,
        (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0 ∧
        (∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
          c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0) ∧
        (∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
          c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) ∧
        (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 =
          r ^ 2 * (1 - r ^ (2 * K)) ^ 2 / ((1 + r ^ 2) * (1 + r ^ (2 * K + 1)) ^ 2) := by
  sorry

/-- **The optimal states, every `K ≥ 1`.** If `r ∈ (0, 1)`, `m_K(r) = 0`, and real angles
satisfying the `K`-step ladder constraints give `P(A_K = 1, B_K = 1) = P_K*(r)`, then the Schmidt
ratio is `c₁/c₀ = r` or `c₁/c₀ = r⁻¹`. -/
theorem ratio_of_ladder_prob_eq_of_mK_root (K : ℕ) (hK : 1 ≤ K) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hm : r ^ (4 * K + 3) - (1 + 2 * K) * r ^ (2 * K + 3) - 2 * K * r ^ (2 * K + 2) -
      2 * K * r ^ (2 * K + 1) - (1 + 2 * K) * r ^ (2 * K) + 1 = 0)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0)
    (hopt : (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 =
      r ^ 2 * (1 - r ^ (2 * K)) ^ 2 / ((1 + r ^ 2) * (1 + r ^ (2 * K + 1)) ^ 2)) :
    c₁ / c₀ = r ∨ c₁ / c₀ = r⁻¹ := by
  sorry

/-- **Hardy's `K = 1` value on `(0, 1)`.** The greatest value of
`P₁*(q) = q² (1 − q²)² / ((1 + q²)(1 + q³)²)` on `(0, 1)` is `φ⁻⁵`, `φ` the golden ratio. -/
theorem hardy_K1_isGreatest :
    IsGreatest ((fun q : ℝ => q ^ 2 * (1 - q ^ 2) ^ 2 / ((1 + q ^ 2) * (1 + q ^ 3) ^ 2)) ''
      Set.Ioo 0 1) (goldenRatio⁻¹ ^ 5) := by
  sorry

/-- **Hardy's value**: `φ⁻⁵ = (5√5 − 11)/2 = 0.09016…`. -/
theorem hardy_value_eq : goldenRatio⁻¹ ^ 5 = (5 * √5 - 11) / 2 := by
  sorry

/-- **The `K = 1` maximiser is the root in `(0, 1)` of the quartic** `q⁴ − 3q³ + 3q² − 3q + 1`
(the product of Hardy's condition `q² − φ²q + 1 = 0`, i.e. `2c₀c₁ = 3 − √5`, with its conjugate
over `ℚ(√5)`; the `K = 1` factor of Cereceda's `m₁(x)`, eq. (20)). -/
theorem hardy_K1_eq_iff_quartic {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    q ^ 2 * (1 - q ^ 2) ^ 2 / ((1 + q ^ 2) * (1 + q ^ 3) ^ 2) = goldenRatio⁻¹ ^ 5 ↔
      q ^ 4 - 3 * q ^ 3 + 3 * q ^ 2 - 3 * q + 1 = 0 := by
  sorry

/-- **The `K = 1` maximiser is unique.** -/
theorem hardy_K1_existsUnique :
    ∃! q : ℝ, q ∈ Set.Ioo (0 : ℝ) 1 ∧
      q ^ 2 * (1 - q ^ 2) ^ 2 / ((1 + q ^ 2) * (1 + q ^ 3) ^ 2) = goldenRatio⁻¹ ^ 5 := by
  sorry

/-- **The `K = 1` bound over every Schmidt state.** For every `c₀, c₁ > 0` with
`c₀² + c₁² = 1` (either order) and real angles satisfying the one-step ladder constraints,
`P(A₁ = 1, B₁ = 1) ≤ φ⁻⁵ = (5√5 − 11)/2`. -/
theorem ladder_K1_le {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < 1, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < 1, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) :
    (c₀ * cos (a 1) * cos (b 1) + c₁ * sin (a 1) * sin (b 1)) ^ 2 ≤ goldenRatio⁻¹ ^ 5 := by
  sorry

/-- **The `K = 1` bound is attained**, by a Schmidt state satisfying Hardy's condition
`2c₀c₁ = 3 − √5` and real angles satisfying the one-step ladder constraints. -/
theorem ladder_K1_attained :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ c₀ ^ 2 + c₁ ^ 2 = 1 ∧ 2 * c₀ * c₁ = 3 - √5 ∧
      ∃ a b : ℕ → ℝ,
        (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0 ∧
        (∀ k < 1, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
          c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0) ∧
        (∀ k < 1, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
          c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) ∧
        (c₀ * cos (a 1) * cos (b 1) + c₁ * sin (a 1) * sin (b 1)) ^ 2 = goldenRatio⁻¹ ^ 5 := by
  sorry

/-- **Every `K = 1` optimum satisfies Hardy's condition.** If real angles satisfying the one-step
ladder constraints give `P(A₁ = 1, B₁ = 1) = φ⁻⁵`, then `2c₀c₁ = 3 − √5`. -/
theorem ladder_K1_hardy_condition_of_eq {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < 1, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < 1, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0)
    (hopt : (c₀ * cos (a 1) * cos (b 1) + c₁ * sin (a 1) * sin (b 1)) ^ 2 =
      goldenRatio⁻¹ ^ 5) :
    2 * c₀ * c₁ = 3 - √5 := by
  sorry

/-- **The real root of `x³ − x − 1` is unique** (the plastic number `ρ = 1.3247…`). -/
theorem existsUnique_cubic : ∃! ρ : ℝ, ρ ^ 3 = ρ + 1 := by
  sorry

/-- **The `K = 2` value on `(0, 1)`.** For `ρ` the real root of `x³ − x − 1`, the greatest value of
`P₂*(q) = q² (1 − q⁴)² / ((1 + q²)(1 + q⁵)²)` on `(0, 1)` is `(8ρ² + ρ − 11)/25 = 0.17454…`. -/
theorem hardy_K2_isGreatest {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    IsGreatest ((fun q : ℝ => q ^ 2 * (1 - q ^ 4) ^ 2 / ((1 + q ^ 2) * (1 + q ^ 5) ^ 2)) ''
      Set.Ioo 0 1) ((8 * ρ ^ 2 + ρ - 11) / 25) := by
  sorry

/-- **The `K = 2` maximiser is `q = ρ⁻²`** (the Schmidt ratio `c₁/c₀`). -/
theorem hardy_K2_eq_iff_inv_sq {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    q ^ 2 * (1 - q ^ 4) ^ 2 / ((1 + q ^ 2) * (1 + q ^ 5) ^ 2) = (8 * ρ ^ 2 + ρ - 11) / 25 ↔
      q = ρ⁻¹ ^ 2 := by
  sorry

/-- **The `K = 2` maximiser is the root in `(0, 1)` of the stationarity cofactor**
`q³ − q² + 2q − 1` (a factor of Cereceda's `m₂(x)`, eq. (20)). -/
theorem hardy_K2_eq_iff_cubic {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    q ^ 2 * (1 - q ^ 4) ^ 2 / ((1 + q ^ 2) * (1 + q ^ 5) ^ 2) = (8 * ρ ^ 2 + ρ - 11) / 25 ↔
      q ^ 3 - q ^ 2 + 2 * q - 1 = 0 := by
  sorry

/-- **The `K = 2` maximiser is unique.** -/
theorem hardy_K2_existsUnique {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    ∃! q : ℝ, q ∈ Set.Ioo (0 : ℝ) 1 ∧
      q ^ 2 * (1 - q ^ 4) ^ 2 / ((1 + q ^ 2) * (1 + q ^ 5) ^ 2) = (8 * ρ ^ 2 + ρ - 11) / 25 := by
  sorry

/-- **The `K = 2` bound over every Schmidt state.** For `ρ` the real root of `x³ − x − 1`, every
`c₀, c₁ > 0` with `c₀² + c₁² = 1` (either order) and real angles satisfying the two-step ladder
constraints, `P(A₂ = 1, B₂ = 1) ≤ (8ρ² + ρ − 11)/25`. -/
theorem ladder_K2_le {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < 2, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < 2, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) :
    (c₀ * cos (a 2) * cos (b 2) + c₁ * sin (a 2) * sin (b 2)) ^ 2 ≤
      (8 * ρ ^ 2 + ρ - 11) / 25 := by
  sorry

/-- **The `K = 2` bound is attained**, by the Schmidt state with weights `c₀² = ρ⁻¹`, `c₁² = ρ⁻⁵`
and real angles satisfying the two-step ladder constraints. -/
theorem ladder_K2_attained {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ c₀ ^ 2 + c₁ ^ 2 = 1 ∧ c₀ ^ 2 = ρ⁻¹ ∧ c₁ ^ 2 = ρ⁻¹ ^ 5 ∧
      ∃ a b : ℕ → ℝ,
        (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0 ∧
        (∀ k < 2, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
          c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0) ∧
        (∀ k < 2, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
          c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) ∧
        (c₀ * cos (a 2) * cos (b 2) + c₁ * sin (a 2) * sin (b 2)) ^ 2 =
          (8 * ρ ^ 2 + ρ - 11) / 25 := by
  sorry

/-- **The optimal states at `K = 2`.** If real angles satisfying the two-step ladder constraints
give `P(A₂ = 1, B₂ = 1) = (8ρ² + ρ − 11)/25`, then the Schmidt weights are `ρ⁻¹` and `ρ⁻⁵`, in
one order or the other. -/
theorem ladder_K2_weights_of_eq {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < 2, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < 2, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0)
    (hopt : (c₀ * cos (a 2) * cos (b 2) + c₁ * sin (a 2) * sin (b 2)) ^ 2 =
      (8 * ρ ^ 2 + ρ - 11) / 25) :
    (c₀ ^ 2 = ρ⁻¹ ∧ c₁ ^ 2 = ρ⁻¹ ^ 5) ∨ (c₀ ^ 2 = ρ⁻¹ ^ 5 ∧ c₁ ^ 2 = ρ⁻¹) := by
  sorry

/-- **The minimal polynomial of the `K = 2` optimum** over `ℚ` is
`x³ + (17/25) x² + (2/25) x − 1/25` (monic form of `25x³ + 17x² + 2x − 1`). -/
theorem minpoly_value {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    minpoly ℚ ((8 * ρ ^ 2 + ρ - 11) / 25) =
      X ^ 3 + C (17 / 25 : ℚ) * X ^ 2 + C (2 / 25 : ℚ) * X - C (1 / 25 : ℚ) := by
  sorry

/-- **The `K = 2` optimum generates a cubic field**: `[ℚ((8ρ² + ρ − 11)/25) : ℚ] = 3`. -/
theorem finrank_adjoin_value {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {(8 * ρ ^ 2 + ρ - 11) / 25}) = 3 := by
  sorry

/-- **`25x³ + 17x² + 2x − 1` is irreducible over `ℚ`.** The hypothesis `ρ³ = ρ + 1` does not
enter the conclusion (the proof goes through the minimal polynomial of the value). -/
theorem irreducible_25 {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    Irreducible (25 * X ^ 3 + 17 * X ^ 2 + 2 * X - 1 : ℚ[X]) := by
  sorry

/-- **The `K = 2` value is not totally real.** For `ρ` the real root of `x³ − x − 1`, the minimal
polynomial of `(8ρ² + ρ − 11)/25` over `ℚ` has a root `z ∈ ℂ` off the real line: the value has a
non-real conjugate. -/
theorem exists_nonreal_root_minpoly_value {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    ∃ z : ℂ, z.im ≠ 0 ∧ aeval z (minpoly ℚ ((8 * ρ ^ 2 + ρ - 11) / 25)) = 0 := by
  sorry

end HardyLadder.Entry
