# hardy-ladder

A standalone Lean 4 / Mathlib package, kernel-checked, on the two-qubit Hardy ladder.

**Theorem.** For a real two-qubit state in Schmidt form `c₀|00⟩ + c₁|11⟩` (`c₀, c₁ > 0`,
`c₀² + c₁² = 1`) and real projective measurements with angles `aₖ, bₖ` satisfying the `K`-step
ladder constraints (`P(A₀=1,B₀=1) = 0`, `P(Aₖ₊₁=1,Bₖ=0) = 0`, `P(Aₖ=0,Bₖ₊₁=1) = 0` for `k < K`),

  `P(A_K=1, B_K=1) ≤ P_K*(q) = q² (1 − q^{2K})² / ((1 + q²)(1 + q^{2K+1})²)`, `q = c₁/c₀`,

with equality attainable (statements 1–2, every `K`). For every `K` the ladder probability is
below `1/2`, and `1/2` is approached as `K` grows: for every `ε > 0` and every large enough `K`,
some Schmidt state and real settings give more than `1/2 − ε` (statements 3–4; the bound is the
two-qubit, real-settings case of a bound that follows in every dimension from published results,
and the approach is the
"(50 − δ)%" of Hardy 1997 and Boschi et al. 1997; see Provenance and Scope). For every `K ≥ 1` the
maximiser of `P_K*` on `(0, 1)` is the unique zero there of Cereceda's polynomial

  `m_K(x) = x^{4K+3} − (1+2K)x^{2K+3} − 2Kx^{2K+2} − 2Kx^{2K+1} − (1+2K)x^{2K} + 1`

(statements 5–8: `d/dq P_K*(q) = 2q(1 − q^{2K}) m_K(q)/((1 + q²)²(1 + q^{2K+1})³)` for `q > 0`;
`m_K` has exactly one zero `r` in `(0, 1)`; `P_K*(r)` is the greatest value of `P_K*` on `(0, 1)`;
and `r` is the only point of `(0, 1)` attaining it), and over every real Schmidt state and real
settings the `K`-step optimum is `P_K*(r)` (statement 9), attained at the Schmidt ratio
`c₁/c₀ = r` (statement 10), and every configuration attaining it has `c₁/c₀ ∈ {r, r⁻¹}` (statement
11); that the ratio `r⁻¹` also attains it follows from the symmetry `P_K*(1/q) = P_K*(q)`, proved in
the library (`HardyLadder.ladderValue_inv`) and not compared. At `K = 1` the optimum is
`φ⁻⁵ = (5√5 − 11)/2` (`φ` the golden ratio), attained on `(0, 1)` at the unique root there of
`q⁴ − 3q³ + 3q² − 3q + 1` and, over every Schmidt state, attained at a state with
`2c₀c₁ = 3 − √5` and only where `2c₀c₁ = 3 − √5` (statements 12–18). At `K = 2` the optimum is

  `(8ρ² + ρ − 11)/25 = 0.17454957…`, `ρ` the real root of `x³ − x − 1` (the plastic number),

attained on `(0, 1)` exactly at `q = ρ⁻²`, the root in `(0, 1)` of `q³ − q² + 2q − 1`, and over
every Schmidt state attained at the weights `c₀² = ρ⁻¹`, `c₁² = ρ⁻⁵` and only where
`{c₀², c₁²} = {ρ⁻¹, ρ⁻⁵}` (statements 19–26); at `K = 1, 2`, as for every `K`, the swapped state
also attains the optimum by the same uncompared symmetry. Given the values of statements 12 and 20,
statements 14–15 and 22–23 follow from the `K = 1` and `K = 2` cases of statements 6–8 and the
factorisations of `m₁` and `m₂` under Provenance (library lemmas `HardyLadder.cerecedaM_one`,
`HardyLadder.cerecedaM_two`; the other factors have no zero in `(0, 1)`), and statement 23 also
follows directly from statement 21, since `ρ⁻² ∈ (0, 1)`. They are proved separately in the
library, through `s = q + 1/q`, and are kept as compared statements because they give the
maximiser's polynomial and its uniqueness at the closed-form values `φ⁻⁵` and
`(8ρ² + ρ − 11)/25`. The `K = 2` value has minimal polynomial `x³ + (17/25)x² + (2/25)x − 1/25`
over `ℚ`, so `25x³ + 17x² + 2x − 1` is irreducible over `ℚ` and the value generates a cubic field
(statements 27–29), and the value is not totally real: read with statement 27, which identifies
that polynomial as the cubic, statement 30 gives it a root in `ℂ` off the real line. Statement 30
is the consequence of the negative discriminant `−23³` of the cubic (computer algebra, not
formalised); it records the contrast with the `K = 1` value, which lies in the totally real
quadratic field `ℚ(√5)` (not formalised).

**What the Lean models.** Statements 1–2 model the ladder for a *real* two-qubit state in Schmidt
form with *real* projective settings. In Lean the state, the measurements and the probabilities are
not modelled as Hilbert-space objects: each `P(·)` is the squared real amplitude written out in
`Challenge.lean` (§Setting), and reading these expressions as quantum probabilities is the informal
account. Statements 5–8, 12, 14–15 and 20–23 concern the function `P_K*(q)` and Cereceda's
`m_K` (statement 5 on `q > 0`, the others on `q ∈ (0, 1)`); statements 13 and 19 are about `φ` and
`ρ` alone. The library proves
the symmetry `P_K*(1/q) = P_K*(q)` (`HardyLadder.ladderValue_inv`, uncompared; Cereceda notes it
below his Table 1) and composes it with statement 1 in the proofs of statements 3, 9, 11, 16, 18,
24 and 26 (the attainment statements 10, 17 and 25 do not use it); statements 9–11 (every
`K ≥ 1`), 16–18 (`K = 1`) and 24–26 (`K = 2`) state the result end to end, in the ladder
probabilities themselves, over every real Schmidt state (`c₀, c₁ > 0`, with `c₁ < c₀`, `c₁ = c₀` or
`c₁ > c₀`; product states are not covered) and all real settings (attainment is stated at one of
the two optimal states: at `K = 1, 2` at one state, and for every `K` at the ratio `r`, statement
10 giving `P_K*(r)` at the ratio `r` for every `r > 0`; that the swapped state, ratio `r⁻¹`, also
attains the optimum follows from the uncompared symmetry and is not stated):
`P_K*(r)` for every `K ≥ 1`, `r` the zero of `m_K` in `(0, 1)` (statement 9,
`ladder_prob_le_of_mK_root`; attained by statement 10, `ladder_prob_attained_of_ratio`, which
holds for every `K` and every `r > 0`), attained only where `c₁/c₀ ∈ {r, r⁻¹}` (statement 11,
`ratio_of_ladder_prob_eq_of_mK_root`);
`φ⁻⁵` at `K = 1` (statements 16–17, `ladder_K1_le`, `ladder_K1_attained`), attained only where
`2c₀c₁ = 3 − √5`, Hardy's condition (statement 18, `ladder_K1_hardy_condition_of_eq`); and
`(8ρ² + ρ − 11)/25` at `K = 2` (statements 24–25, `ladder_K2_le`, `ladder_K2_attained`), attained
only at Schmidt weights `{c₀², c₁²} = {ρ⁻¹, ρ⁻⁵}` (statement 26, `ladder_K2_weights_of_eq`).
Statements 3–4 (every `K`, below `1/2` and approaching it) are over the same states and
settings. Unless qualified as all-dimension, "optimum" in this package means the optimum over
two-qubit Schmidt states and **real** measurement settings, the setting of Cereceda (2002); that
complex settings, or general two-qubit pure states, do no better is not formalised here.

**Provenance.** The ladder is Hardy's (*New Developments on Fundamental Problems in Quantum
Physics*, Kluwer 1997, pp. 163–170) and Boschi, Branca, De Martini and Hardy's (PRL 79, 2755,
1997), and so is the behaviour of statement 4, that the ladder probability approaches `1/2` for
large `K` (with equal settings; unequal real settings are Cereceda 2002, eq. (18)): in Cereceda's
words (J. Phys. A 35, 9105, 2002, after eq. (19); its page numbers here are those of
arXiv:quant-ph/0206015v4), "the maximum value of P_K is (50 − δ)% which is
realized for K → ∞ and a state that is not quite maximally entangled"; Cabello (PRA 58, 1687,
1998) likewise credits to them that the proof "goes through for 50% of pairs at the most"
(abstract) and that "As K tends to infinity PK tends to 50%" (arXiv v2, p. 3), and Cereceda
(2002, p. 6, from eq. (33)) puts the limit at `K → ∞` and `x → 1`. Statement 3, the bound below
`1/2` for every `K`, is the two-qubit, real-settings, Schmidt-form case of a stronger bound that
follows in every dimension from Cereceda 2016 and Wehner 2006 (see Scope). `K = 1` is Hardy's
paradox (PRL 71, 1665, 1993), whose p. 1667 gives the maximum `½(5√5 − 11)` at
`2|αβ| = 3 − √5`, i.e. at `q + 1/q = φ²`; the form `τ⁻⁵`, `τ` the golden mean, is in Mermin
(Physics Today 47(6), 9, 1994) and Cereceda (Found. Phys. Lett. 14, 401, 2001). The closed form
`P_K*` is eq. (19) of Cereceda (J. Phys. A 35, 9105, 2002), equivalently half his
eq. (33) in `x = α/β` (the `q`-form itself is printed in Cereceda 2016, p. 4), attributed there to
Hardy 1997 and Boschi et al. 1997; Cereceda shows that equal settings are optimal (eq. (18)), gives
the maximisers as the non-trivial real roots of
`m_K(x) = x^{4K+3} − (1+2K)x^{2K+3} − 2Kx^{2K+2} − 2Kx^{2K+1} − (1+2K)x^{2K} + 1` (eq. (20)), and
lists the optima to three decimals for `K = 1, …, 10` in Table 1 (`0.090`, `0.174`, …; mostly
truncated: `0.17455` appears as `0.174`, while the `K = 8` value `0.35394` appears as `0.354`).
The `m_K` of statements 5–9 and 11 is this polynomial, coefficient for coefficient;
Cereceda's variable is `x = α/β` (his `r₁ = α/β`, `r₂ = β/α`) and ours is `q = c₁/c₀`, and `m_K` is
palindromic (`x^{4K+3} m_K(1/x) = m_K(x)`), so the two readings have the same zeros. Cereceda
introduces eq. (20) with "It can be shown" (p. 4) and prints neither the derivative nor a proof:
he states the characterisation without proof. Statements 6–8 are the formal statement, on `(0, 1)`
and for every `K ≥ 1`, of his characterisation of the maximiser (his footnote's census of the
other roots of `m_K`, `−1` with multiplicity 3 and `4K − 2` non-real roots, is not formalised; it
was checked by computer algebra for `K ≤ 40`), proved here through the derivative identity of
statement 5 and `m_K(x) = 1 − x^{2K} g_K(x)`,
`g_K(x) = (1 + 2K) + 2Kx + 2Kx² + (1 + 2K)x³ − x^{2K+3}`, with `g_K > 0` and `g_K' > 0` on
`[0, 1]`, so that `m_K` decreases strictly from `1` to `−8K`. The characterisation is Cereceda's;
the argument is elementary calculus, and no printed proof of it for `K ≥ 2` was found in the
literature searched (search dated 2026-10-29: Cereceda 2002, 2015, 2016 and 2017; Meng et al.
2018; Yang et al. 2019; Yang, Zhang and Chen 2024; Chen, Mal, Tabia and Liang 2024; Barbieri, De
Martini, Di Nepi and Mataloni 2004, arXiv:quant-ph/0406156; Cabello 1998; none prints a proof; where
they treat `K ≥ 2` they state the characterisation (Cereceda 2002) or the existence of a maximiser
without proof, or give numerical values), with the bodies of Hardy 1997 and Boschi et al. 1997 not opened; no prior formal
statement found. The quartic of statement 14 is the
`K = 1` factor of
`m₁(x) = (x + 1)³(x⁴ − 3x³ + 3x² − 3x + 1)`; the cubic of statement 22 is a factor of
`m₂(x) = (x + 1)³(x² + 1)(x³ − 2x² + x − 1)(x³ − x² + 2x − 1)`, which the paper does not factor
beyond noting the triple root `−1` and that the other `4K − 2` roots are complex (footnote, p. 4).
The `K = 2` value is in print numerically: `17.5 %` (Cabello, PRA 58, 1687, 1998, quoting Hardy
1997 and Boschi et al. 1997), `0.17455` (Meng et al., PRA 98, 062103, 2018, Table I; Yang et
al., PRA 99, 032103, 2019; Chen, Mal, Tabia and Liang, PRA 109, 042206, 2024) and `0.174550`
(Cereceda, Quantum Stud. Math. Found. 4, 205, 2017, Table 1; Yang, Zhang and Chen, PRA 110, 012441,
2024, Table I). In the literature and repositories
searched (search dated 2026-10-28) we found no statement of the identification of the `K = 2`
stationarity root as `ρ⁻²` (the root itself is OEIS A357471, with no mention of either the plastic
number or Hardy's ladder), of the closed form `(8ρ² + ρ − 11)/25` with minimal polynomial
`25x³ + 17x² + 2x − 1`, or of the Schmidt weights `ρ⁻¹`, `ρ⁻⁵`; this is a search result, not a
proof of absence (the bodies of Hardy 1997 and Boschi et al. 1997, the primary sources of
eq. (19), were not opened). Why `K = 1` and `K = 2`: for `K = 3, …, 8` the irreducible factor of
`m_K` over `ℚ` carrying the maximiser has degree 12, 14, 20, 22, 28, 30 (computer algebra, not
formalised); among `K = 1, …, 8`, `K = 1` (degree 4) and `K = 2` (degree 3) are the only cases of
degree at most 4.

**Scope.** Nothing in the compared statements asserts anything about physics beyond identities,
inequalities and a derivative of real expressions and facts about polynomials and a cubic number
field. The `K = 1`
value is the optimum in every dimension, and any state attaining it is equivalent up to local
isometries to the two-qubit optimal state (self-testing; Rabelo, Zhi and Scarani, PRL 109, 180401,
2012). At `K = 2` the all-dimension optimum is, to our knowledge (search dated 2026-10-28), open:
Liang, Spekkens and Wiseman (Phys. Rep. 506, 1, 2011, Sec. IV.E) report the NPA upper bound
`0.17456` against the two-qubit `0.17455`, and Chen, Mal, Tabia and Liang (2024) give `0.17459` at
level 1a of the Moroder et al. hierarchy; neither proves tightness. Cereceda (Quantum Inf.
Process. 15, 1779, 2016; arXiv:1508.06317) derives the upper bound `P₂ ≤ (3√3 − 4)/4 ≈ 0.299`
from the chained-CHSH Tsirelson bound, which is not tight. For every `K` the strict bound
`P_K < 1/2` already follows in every dimension from Cereceda (2016, eqs. (8)–(9)) and Wehner 2006.
Cereceda combines the no-signalling identity `CHSH_K = 2K + 4P_K` with Wehner's dimension-free
chained-CHSH bound for ±1 observables (PRA 73, 022110, 2006) to get
`P_K ≤ L_K = ¼[2(K + 1)cos(π/(2K + 2)) − 2K]`. Cereceda states his setting as two qubits, but
neither step uses the dimension, and `L_K < 1/2` because the cosine is below 1. Both inferences
are drawn here; Cereceda prints `P_K ≤ L_K` and that `L_K` tends to `0.5`. No-signalling alone
allows exactly `1/2` for every `K` (Cereceda, Adv.
Stud. Theor. Phys. 9, 433, 2015). Statement 3 is the two-qubit, real-settings, Schmidt-form case.
No dimension-independence is formalised here.

**Prior formalisations.** Three public Lean 4 developments formalise Hardy's `K = 1` paradox (found
2026-10-28): zblore/csd-lean4 (the local-realism no-go, and the attainment of `(5√5 − 11)/2` by the
golden-ratio state, `CSD.Empirical.Hardy.HardyQMMax.hardyMax_probability_eq` and `hardyMax_value`;
no upper bound over states or settings is stated there; the same repository has
`CsdLean4/Empirical/CSD/HardyVolume.lean`, the same value as a Kähler volume, an evaluation,
`CsdLean4/Empirical/CSD/Hardy.lean`, a CSD-model no-go (`no_csd_hardy_assignment`),
`CsdLean4/LF4/HardyKahler.lean`, Born-frequency convergence for the `1/12` state, and
`CsdLean4/Mathlib/Probability/ChainedBell.lean`, the Colbeck–Renner chained walk, a no-signalling
marginal bound, not the ladder and not the Braunstein–Caves inequality),
primaryhosting/brockian-mathematics (`QI.hardy_paradox` and its variants, the `1/12` instance)
and inventor1975/ZTL (`Hardy.*`, the `1/12` instance in integer arithmetic). None of them states
the ladder bound, the maximality or the uniqueness at `K = 1`, or anything at `K = 2`. The prover
sweep of 2026-10-28 (Mathlib master and the pin, QuAIR/Lean-QIT,
physical-superintelligence/oqp-batch-2026, openai/math, physlib, Lean-QuantumInfo, CoqQ,
QuantumLib, Isabelle/AFP, and a GitHub-wide code search for Hardy's paradox and the Hardy ladder in
Lean, Coq and Isabelle) found no other formal statement of these results;
a second sweep on 2026-10-29, at that day's heads of the same targets (openai/math and the AFP
through their contents lists, tree listings and code search) and adding the Lean library
the-omega-institute/trureturing, found no formal statement of statements 5–11 or 30. That library
(dev `52ce13dc`, 2026-10-29) has Hardy-type modules on other arguments: the temporal Hardy maximum
`1/4` with spin measurements (`D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.lean`), a
refuted no-signalling conjecture for a relaxed multipartite Hardy test, and a refutation of the
three-qubit `9/64` conjecture of Cereceda 2017
(`D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.lean`); none concerns the two-qubit ladder
or Cereceda 2002.
The nearest formal neighbours are CHSH/Tsirelson developments: Mathlib
`Mathlib/Algebra/Star/CHSH.lean`, Lean-QIT `QIT/Nonlocality/Tsirelson.lean`, AFP
`Projective_Measurements/CHSH_Inequality.thy` and the AFP entry `TsirelsonBound` (`Tsirelson.thy`),
and CoqQ `src/QIT/commutator.v` (`CHSH_inequality`, `CHSH_violation`). None states a Hardy or
ladder bound.

Pin: Lean `leanprover/lean4:v4.35.0-rc2`, Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`
(required in git form in `lakefile.toml`). `lake build` → exit 0; the only `sorry` tokens are the
thirty deliberate placeholders of `Challenge.lean`; each of the 160 theorems of the library
and each of the thirty compared theorems of `Solution.lean` depends on exactly
`[propext, Classical.choice, Quot.sound]` (`AxiomAudit.lean` prints the audit for all 160 library
theorems and the thirty compared theorems; see `BUILD.txt`).

## The comparison surface

`Challenge.lean` (imports Mathlib only; thirty statements, each with a `sorry` placeholder, no
definition of its own — every formula written out) and `Solution.lean` (proves each by the library
theorem), compared through `comparator.json`. The Mathlib definitions the statements import
(`Real.cos`, `Real.sin`, `Real.goldenRatio`, `Real.sqrt`, `IsGreatest`, `Set.Ioo`, `Set.image`,
`ExistsUnique`, `HasDerivAt`, `minpoly`, `IntermediateField.adjoin`, `Module.finrank`,
`Polynomial.C`, `X`, `Polynomial.aeval`, `Irreducible`, `Complex`) are quoted
verbatim from the pinned source with permalinks in
`MATHLIB_DEFINITIONS.md`, and `DefinitionAudit.lean` (a default build target, Mathlib only, not
compared) kernel-checks the facts about them the account relies on.

"No prior formal statement found" below refers to the prover sweep of 2026-10-28 described above
and, for statements 5–11 and 30, also to the second sweep of 2026-10-29.

| # | `HardyLadder.Entry.…` | statement | attribution |
|---|---|---|---|
| 1 | `ladder_prob_le` | every `K`: under the ladder constraints, `P(A_K=1,B_K=1) ≤ P_K*(c₁/c₀)` (real settings) | Cereceda 2002 eq. (19), equivalently half of eq. (33) (Hardy 1997, Boschi et al. 1997); optimality over the settings: Cereceda 2002, eq. (18); no prior formal statement found |
| 2 | `ladder_prob_attained` | every `K`: angles satisfying the constraints with equality exist | same |
| 3 | `ladder_prob_lt_half` | every `K`, under the hypotheses of 1: `P(A_K=1,B_K=1) < 1/2` | the two-qubit, real-settings, Schmidt-form case of a known stronger bound: Cereceda 2016, eqs. (8)–(9), with Wehner 2006, give `P_K ≤ ¼[2(K + 1)cos(π/(2K + 2)) − 2K]`, which is below `1/2`, for any state and any ±1 observables (Cereceda's setting is two qubits; neither step uses the dimension); for two qubits and equal settings, Hardy 1997 and Boschi et al. 1997, the "(50 − δ)%" (as quoted by Cereceda 2002 after eq. (19)); unequal real settings via Cereceda 2002, eq. (18); no-signalling boxes reach exactly `1/2` (Cereceda 2015); no prior formal statement found |
| 4 | `ladder_prob_approaches_half` | `ε > 0 ⇒ ∃ K₀, ∀ K ≥ K₀`, some Schmidt state and angles satisfying the `K`-step constraints give `P(A_K=1,B_K=1) > 1/2 − ε` | Hardy 1997 and Boschi et al. 1997, the "(50 − δ)%" (as quoted by Cereceda 2002 after eq. (19)); the limit `1/2` as `K → ∞`, `x → 1` also in Cereceda 2002, p. 6, Cabello 1998, Sec. 2 (arXiv v2, p. 3), and Cereceda 2016, p. 4; no prior formal statement found |
| 5 | `hasDerivAt_ladder_value` | every `K`, `q > 0`: `HasDerivAt P_K* (2q(1 − q^{2K}) m_K(q)/((1 + q²)²(1 + q^{2K+1})³)) q`, `m_K` written out | `m_K` is Cereceda 2002, eq. (20), coefficient for coefficient; the derivative is not printed there (eq. (20) is introduced with "It can be shown", p. 4); no prior formal statement found |
| 6 | `existsUnique_mK_root` | `K ≥ 1`: `∃! r, r ∈ (0,1) ∧ m_K(r) = 0` | Cereceda 2002, p. 4 and footnote (the maximisers are the two non-trivial real roots `r₁ < 1 < r₂ = 1/r₁` of `m_K`, "It can be shown"; the other roots are `−1` and complex); no prior formal statement found |
| 7 | `ladder_value_isGreatest_of_mK_root` | `K ≥ 1`, `r ∈ (0,1)`, `m_K(r) = 0` ⇒ `IsGreatest (P_K* '' (0,1)) (P_K*(r))` | Cereceda 2002, eq. (20) and p. 4 ("It can be shown"); the optima to three decimals for `K = 1, …, 10` in his Table 1; no prior formal statement found |
| 8 | `eq_of_ladder_value_eq_of_mK_root` | same `r`; `q ∈ (0,1)`, `P_K*(q) = P_K*(r)` ⇒ `q = r` | the uniqueness in Cereceda 2002, p. 4 (as for 6); no prior formal statement found |
| 9 | `ladder_prob_le_of_mK_root` | same `r`; every Schmidt state, under the `K`-step constraints: `P(A_K=1,B_K=1) ≤ P_K*(r)` | Cereceda 2002, eqs. (18)–(20) and p. 4; no prior formal statement found |
| 10 | `ladder_prob_attained_of_ratio` | every `K`, `r > 0`: some state with `c₁/c₀ = r` and angles satisfying the constraints give `P(A_K=1,B_K=1) = P_K*(r)` | statement 2 at the state with ratio `r` (Hardy 1997, Boschi et al. 1997; Cereceda 2002, eqs. (18)–(19)) |
| 11 | `ratio_of_ladder_prob_eq_of_mK_root` | same `r`: `P(A_K=1,B_K=1) = P_K*(r)` ⇒ `c₁/c₀ = r ∨ c₁/c₀ = r⁻¹` | Cereceda 2002, p. 4 (the maximisers `r₁` and `r₂ = 1/r₁`, by the symmetry `P_K(α, β) = P_K(β, α)`); no prior formal statement found |
| 12 | `hardy_K1_isGreatest` | `IsGreatest (P₁* '' (0,1)) φ⁻⁵` | Hardy 1993 (attainment of the value formalised earlier in zblore/csd-lean4, `hardyMax_probability_eq`; the upper bound is not) |
| 13 | `hardy_value_eq` | `φ⁻⁵ = (5√5 − 11)/2` | elementary; the `φ⁻⁵` form is in Mermin 1994 and Cereceda 2001; cf. csd-lean4 `hardyMax_value` (`1/(5φ + 3)`) |
| 14 | `hardy_K1_eq_iff_quartic` | `q ∈ (0,1)`: `P₁*(q) = φ⁻⁵ ⇔ q⁴ − 3q³ + 3q² − 3q + 1 = 0` | Hardy 1993 (as `2c₀c₁ = 3 − √5`); the quartic is the `K = 1` factor of Cereceda's `m₁(x)`, eq. (20) |
| 15 | `hardy_K1_existsUnique` | the `K = 1` maximiser on `(0,1)` is unique | Mermin 1994, p. 11, in his parametrisation ("Maximizing (6) gives uniquely p_l = p_r = (√5 − 1)/2 = 1/τ"); for every `K`, Cereceda 2002, p. 4 (the maximisers are the two non-trivial real roots `r₁ < 1 < r₂ = 1/r₁` of `m_K`, "It can be shown"); in every dimension the optimal state is unique up to local isometries (self-testing: Rabelo, Zhi and Scarani 2012); no prior formal statement found |
| 16 | `ladder_K1_le` | every Schmidt state, under the one-step constraints: `P(A₁=1,B₁=1) ≤ φ⁻⁵` | Hardy 1993; optimality over the settings: Cereceda 2002, eq. (18); a special case of Rabelo, Zhi and Scarani 2012 (every dimension); no prior formal statement found |
| 17 | `ladder_K1_attained` | some state with `2c₀c₁ = 3 − √5` and angles satisfying the constraints give `P(A₁=1,B₁=1) = φ⁻⁵` | Hardy 1993 (attainment of the value formalised earlier in zblore/csd-lean4, `hardyMax_probability_eq`) |
| 18 | `ladder_K1_hardy_condition_of_eq` | `P(A₁=1,B₁=1) = φ⁻⁵ ⇒ 2c₀c₁ = 3 − √5` | Hardy 1993 (the condition `2\|αβ\| = 3 − √5`); uniqueness of the optimal state in every dimension: Rabelo, Zhi and Scarani 2012; no prior formal statement found |
| 19 | `existsUnique_cubic` | `∃! ρ : ℝ, ρ³ = ρ + 1` | elementary |
| 20 | `hardy_K2_isGreatest` | `ρ³ = ρ + 1 ⇒ IsGreatest (P₂* '' (0,1)) ((8ρ² + ρ − 11)/25)` | value numerical in Cereceda 2002 (`0.174`) and Meng et al. 2018 (`0.17455`); closed form not found (search dated 2026-10-28) |
| 21 | `hardy_K2_eq_iff_inv_sq` | `q ∈ (0,1)`: `P₂*(q) = (8ρ² + ρ − 11)/25 ⇔ q = ρ⁻²` | maximiser numerical in Cereceda 2002 (`r₁ = 0.569`); `ρ⁻²` not found (search dated 2026-10-28) |
| 22 | `hardy_K2_eq_iff_cubic` | `q ∈ (0,1)`: `P₂*(q) = (8ρ² + ρ − 11)/25 ⇔ q³ − q² + 2q − 1 = 0` | the stationarity cofactor; a factor of Cereceda's `m₂(x)`, eq. (20), not factored there |
| 23 | `hardy_K2_existsUnique` | the `K = 2` maximiser on `(0,1)` is unique | Cereceda 2002, eq. (20) and p. 4 (the maximisers are the two non-trivial real roots `r₁ < 1 < r₂ = 1/r₁` of `m_K`, "It can be shown"); no prior formal statement found |
| 24 | `ladder_K2_le` | every Schmidt state, under the two-step constraints: `P(A₂=1,B₂=1) ≤ (8ρ² + ρ − 11)/25` | value numerical in Hardy 1997 and Boschi et al. 1997 (`17.5 %`, as quoted by Cabello 1998), Cereceda 2002 (`0.174`) and Meng et al. 2018 (`0.17455`); closed form not found (search dated 2026-10-28) |
| 25 | `ladder_K2_attained` | some state with `c₀² = ρ⁻¹`, `c₁² = ρ⁻⁵` and angles satisfying the constraints attain `(8ρ² + ρ − 11)/25` | the weights not found (search dated 2026-10-28) |
| 26 | `ladder_K2_weights_of_eq` | `P(A₂=1,B₂=1) = (8ρ² + ρ − 11)/25 ⇒ {c₀², c₁²} = {ρ⁻¹, ρ⁻⁵}` | same |
| 27 | `minpoly_value` | `minpoly ℚ ((8ρ² + ρ − 11)/25) = X³ + C(17/25)X² + C(2/25)X − C(1/25)` | no prior formal statement found |
| 28 | `finrank_adjoin_value` | `[ℚ((8ρ² + ρ − 11)/25) : ℚ] = 3` | no prior formal statement found |
| 29 | `irreducible_25` | `Irreducible (25X³ + 17X² + 2X − 1 : ℚ[X])` | the primitive form of 27 (the hypothesis `ρ³ = ρ + 1` does not enter the conclusion) |
| 30 | `exists_nonreal_root_minpoly_value` | `ρ³ = ρ + 1 ⇒ ∃ z : ℂ, z.im ≠ 0 ∧ aeval z (minpoly ℚ ((8ρ² + ρ − 11)/25)) = 0` (the value is not totally real) | elementary; the value lies in `ℚ(ρ)`, LMFDB 3.1.23.1 (`x³ − x² + 1`, signature `(1, 1)`, discriminant `−23`, no intermediate fields); the discriminant of `25x³ + 17x² + 2x − 1` is `−23³` (computer algebra, not formalised); no prior formal statement found |

## The library (`HardyLadder/`, ten modules)

* `Plastic.lean` — the real root of `x³ − x − 1`: positivity, `5/4 < ρ < 4/3`, existence (IVT) and
  uniqueness, `ρ⁻¹ = ρ² − 1`, `ρ⁻² = −ρ² + ρ + 1`, `ρ⁻⁵ = 2 − ρ²`, `ρ⁻¹ + ρ⁻⁵ = 1`.
* `Golden.lean` — `φ⁵ = (11 + 5√5)/2`, `φ⁻⁵ = (5√5 − 11)/2`, `φ⁴ = 3φ + 2`, `φ⁵ = 5φ + 3`, and
  the root `q* = (φ² − √(3φ − 2))/2 ∈ (0, 1)` of `q² − φ² q + 1`.
* `Ladder.lean` — the closed form for every `K`: the constraints make each measurement vector
  parallel to a rotated image of the previous one (`cross u v = 0`, transitive through nonzero
  vectors and preserved by `N = diag(c₁, c₀)`), so `A_K ∥ N^K A₀`, `B_K ∥ N^K J M A₀` (or the other
  way round, by the parity of `K`); the squared amplitude is a ratio whose denominator exceeds the
  AM–GM value by `c₀^{2K} c₁^{2K} (c₀x² − c₁y²)² ≥ 0`. Attainment by the `arctan` chain
  `tan a₀ = q^{−1/2}`, `tan b₀ = −q^{−1/2}`, `tan aₖ₊₁ = tan bₖ/q`, `tan bₖ₊₁ = tan aₖ/q`.
* `HardyK1.lean` — in `s = q + q⁻¹ > 2`, `P₁* = (s − 2)/(s(s − 1)²)` and
  `s(s − 1)² − φ⁵(s − 2) = (s − φ²)²(s + 2φ)`; the quartic factors as
  `(q² − φ²q + 1)(q² − (2 − φ)q + 1)`.
* `HardyK2.lean` — `P₂* = s(s − 2)/(s² − s − 1)²` and
  `v(s² − s − 1)² − s(s − 2) = (s − ρ − 1)²(v s² + B s + C)` with `v, B, C > 0`;
  `q² − (ρ + 1)q + 1 = (q − ρ⁻²)(q − ρ²)`; `q³ − q² + 2q − 1 = (q − ρ⁻²)(q² + (ρ⁻² − 1)q + ρ²)`.
* `Minpoly.lean` — the reversed polynomial `x³ − 2x² − 17x − 25` is monic and reduces to
  `x³ + x + 1` over `𝔽₂`, so it is irreducible over `ℤ` and `ℚ`; `ℚ(v) = ℚ(v⁻¹)` has degree `3`;
  the monic cubic vanishing at `v` is its minimal polynomial.
* `TotallyReal.lean` — `x³ − x − 1` is irreducible over `ℤ` and `ℚ` and is the minimal polynomial
  of any root; its root set in `ℂ` has three elements, at most one real, so some embedding
  `L →+* ℂ` sends `ρ` off the real line and `L` is not totally real; a prime-degree extension has
  only `⊥` and `⊤` as intermediate fields, so every totally real subfield of a cubic field
  containing a root of `x³ − x − 1` is `ℚ` (uncompared). For the `K = 2` value:
  `25x³ + 17x² + 2x − 1` is negative for `x ≤ 0` and has at most one positive root, so of the three
  complex roots of the (irreducible, hence separable) minimal polynomial at most one is real
  (statement 30).
* `Optimum.lean` — the symmetry `P_K*(1/q) = P_K*(q)` and `P_K*(1) = 0`, hence the bounds of
  statements 12 and 20 on all of `q > 0`; the `K = 1` and `K = 2` optima over every real Schmidt
  state and all real settings, their attainment, and the optimal states (Hardy's condition
  `2c₀c₁ = 3 − √5` at `K = 1`; the weights `{ρ⁻¹, ρ⁻⁵}` at `K = 2`): the library proofs of
  statements 16–18 and 24–26.
* `OneHalf.lean` — for `q ∈ (0, 1)`, `P_K*(q) ≤ q²/(1 + q²) < 1/2` (with the symmetry, for every
  `q > 0`), hence statement 3; `P_K*(q) → q²/(1 + q²)` as `K → ∞` (`(q²)^K → 0`), and
  `q²/(1 + q²) → 1/2` as `q → 1`, which with the attainment of statement 2 gives statement 4.
* `Maximiser.lean` — every `K ≥ 1`: Cereceda's `m_K` (`cerecedaM`) and the derivative identity
  `d/dq P_K*(q) = 2q(1 − q^{2K}) m_K(q)/((1 + q²)²(1 + q^{2K+1})³)` (statement 5);
  `m_K = 1 − x^{2K} g_K` with `g_K > 0` and `g_K' > 0` on `[0, 1]`
  (`3(1 + 2K)x² ≥ (2K + 3)x^{2K+2}`), so `m_K` decreases strictly on `[0, 1]` from `1` to `−8K`
  and has exactly one zero `r` in `(0, 1)` (intermediate value theorem; statement 6); `P_K*` is
  strictly increasing on `(0, r]` and strictly decreasing on `[r, 1)` (`strictMonoOn_of_deriv_pos`,
  `strictAntiOn_of_deriv_neg`), so `r` is its unique maximiser on `(0, 1)` (statements 7–8); with
  the symmetry and statement 1, the optimum `P_K*(r)` over every real Schmidt state (statement 9)
  and the restriction of every optimal configuration to the ratios `r` and `r⁻¹` (statement 11);
  with statement 2, attainment of `P_K*(r)` at the ratio `r` (statement 10, which holds at every
  ratio and does not use the symmetry); and the factorisations of `m₁` and `m₂` (`cerecedaM_one`,
  `cerecedaM_two`).

## Building

```
lake build
```

builds the library and the four surface files (`Challenge`, `Solution`, `AxiomAudit`,
`DefinitionAudit`) against the pinned Mathlib (`lake exe cache get` first, on a fresh machine).
`BUILD.txt` records the build and the axiom audit; `SHA256SUMS.txt` the file hashes.

## License

MIT (see `LICENSE`). Mathlib is Apache-2.0.
