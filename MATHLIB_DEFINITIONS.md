# Mathlib definitions used by the compared statements

The compared statements of `Challenge.lean` use no definition of this entry: every formula is
written out. They rest on the following Mathlib declarations, at the pinned revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55` (toolchain `leanprover/lean4:v4.35.0-rc2`). Each excerpt
below is quoted verbatim from the pinned source as checked out by Lake under
`.lake/packages/mathlib` (a build product, not shipped; the same revision the permalinks point
to), with its path, line range and permalink. On 2026-10-29 all 19 excerpts were also compared byte
for byte with the raw files at the pinned revision on GitHub (19/19 identical) and the 17 distinct
permalinks answered HTTP 200. `DefinitionAudit.lean` (a default build target, Mathlib only, not
compared) records, as kernel-checked theorems, the facts about these definitions that the informal
account relies on; the audit theorems named after each excerpt are listed below it (`Set.Ioo` with
`Set.image` share `mem_image_Ioo`, and the three derivative excerpts share
`hasDerivAt_iff_tendsto_slope'`). The Mathlib source is Apache-2.0, copyright the Mathlib authors.
Statements 3–4, 9–11, 16–18 and 24–26 use no Mathlib definition beyond those quoted below
(sections 1–3 and 5): statement 4 is written with `∃`, `∀`, `<`, `≥` and arithmetic on `ℕ` and `ℝ`
only. No limit, filter or supremum is written in any compared statement; statement 5 uses
`HasDerivAt`, which Mathlib defines through a little-o condition along a filter (section 11), and
`Module.finrank` in statement 28 is defined through `Module.rank`, which Mathlib defines as a
supremum.

Notation: `P` abbreviates `https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/`.

## 1. The real sine and cosine (statements 1–4, 9–11, 16–18, 24–26)

The measurement directions are `(cos aₖ, sin aₖ)` and `(−sin aₖ, cos aₖ)`; `Real.cos`, `Real.sin`
are the real parts of the complex functions.

`Mathlib/Analysis/Complex/Trigonometric.lean`, lines 71–79 —
[P`Mathlib/Analysis/Complex/Trigonometric.lean#L71-L79`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Trigonometric.lean#L71-L79):

```lean
/-- The real sine function, defined as the real part of the complex sine -/
@[pp_nodot]
nonrec def sin (x : ℝ) : ℝ :=
  (sin x).re

/-- The real cosine function, defined as the real part of the complex cosine -/
@[pp_nodot]
nonrec def cos (x : ℝ) : ℝ :=
  (cos x).re
```

The bound (statement 1) uses only `cos x ^ 2 + sin x ^ 2 = 1` (`Real.cos_sq_add_sin_sq`, line 667
of the same file; audit theorem `cos_sq_add_sin_sq`), which makes `(cos aₖ, sin aₖ)` a unit vector.
The attaining construction of statement 2 also uses Mathlib's `Real.cos_arctan`, `Real.sin_arctan`
and `Real.cos_sq_arctan` (the `arctan` chain of `HardyLadder/Ladder.lean`); these are not audited
in `DefinitionAudit.lean`, since `Real.arctan` does not occur in any compared statement.
Statements 3–4, 9–11, 16–18 and 24–26 write the same squared amplitudes out at step `K` (`K = 1` in
16–18, `K = 2` in 24–26); their proofs reach the trigonometric functions only through the library
proofs of statements 1 and 2.

## 2. The golden ratio (statements 12–18)

`Mathlib/NumberTheory/Real/GoldenRatio.lean`, lines 36–37 —
[P`Mathlib/NumberTheory/Real/GoldenRatio.lean#L36-L37`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/NumberTheory/Real/GoldenRatio.lean#L36-L37):

```lean
/-- The golden ratio `φ := (1 + √5)/2`. -/
abbrev goldenRatio : ℝ := (1 + √5) / 2
```

Audit theorems `goldenRatio_def` (`rfl`) and `goldenRatio_sq` (`φ² = φ + 1`, Mathlib's
`Real.goldenRatio_sq`). Statement 13 states `φ⁻¹ ^ 5 = (5√5 − 11)/2`; statements 12, 14–18 state
the `K = 1` optimum as `φ⁻¹ ^ 5`.

## 3. The real square root (statements 13, 17, 18)

`Mathlib/Analysis/Real/Sqrt.lean`, lines 109–113 —
[P`Mathlib/Analysis/Real/Sqrt.lean#L109-L113`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Real/Sqrt.lean#L109-L113):

```lean
/-- The square root of a real number. This returns 0 for negative inputs.

This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`. -/
@[irreducible] noncomputable def sqrt (x : ℝ) : ℝ :=
  NNReal.sqrt (Real.toNNReal x)
```

The proof of statement 13 uses `√5 ^ 2 = 5` (`Real.sq_sqrt`; audit theorem `sq_sqrt_five`) and
`0 ≤ √5` (`Real.sqrt_nonneg`). Statements 17 and 18 state Hardy's condition as
`2 * c₀ * c₁ = 3 - √5`. The library also uses the square root in proofs (the maximiser `q*` of
`HardyLadder/Golden.lean`, the `arctan` chain of `HardyLadder/Ladder.lean`, and the states with a
prescribed Schmidt ratio built in `HardyLadder/Optimum.lean` and `HardyLadder/OneHalf.lean`, the
latter also used by `HardyLadder/Maximiser.lean`).

## 4. `IsGreatest`, `upperBounds` (statements 7, 12, 20)

`Mathlib/Order/Bounds/Defs.lean`, lines 33–35 (`upperBounds`) and 42–46 (`IsLeast`, whose
`to_dual` attribute generates `IsGreatest s a := a ∈ s ∧ a ∈ upperBounds s`) —
[P`Mathlib/Order/Bounds/Defs.lean#L33-L46`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Bounds/Defs.lean#L33-L46):

```lean
@[to_dual /-- The set of lower bounds of a set. -/]
def upperBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → a ≤ x }
```

```lean
/-- `a` is a least element of a set `s`; for a partial order, it is unique if exists. -/
@[to_dual
/-- `a` is a greatest element of a set `s`; for a partial order, it is unique if exists. -/]
def IsLeast (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ lowerBounds s
```

Audit theorem `isGreatest_iff`: `IsGreatest s m ↔ m ∈ s ∧ ∀ x ∈ s, x ≤ m` (`Iff.rfl`). Statements
7, 12 and 20 assert that the stated value is attained on `(0, 1)` and bounds every value there.

## 5. `Set.Ioo` and `Set.image` (statements 6–9, 11, 12, 15, 20, 23)

`Mathlib/Order/Interval/Set/Defs.lean`, lines 49–51 —
[P`Mathlib/Order/Interval/Set/Defs.lean#L49-L51`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/Defs.lean#L49-L51):

```lean
/-- `Ioo a b` is the left-open right-open interval $(a, b)$. -/
@[to_dual self (reorder := a b)]
def Ioo (a b : α) := { x | a < x ∧ x < b }
```

`Mathlib/Data/Set/Defs.lean`, lines 264–266 —
[P`Mathlib/Data/Set/Defs.lean#L264-L266`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L264-L266):

```lean
/-- The image of `s : Set α` by `f : α → β`, written `f '' s`, is the set of `b : β` such that
`f a = b` for some `a ∈ s`. -/
def image {β : Type v} (f : α → β) (s : Set α) : Set β := {f a | a ∈ s}
```

Audit theorem `mem_image_Ioo`: `y ∈ f '' Set.Ioo 0 1 ↔ ∃ q, (0 < q ∧ q < 1) ∧ f q = y`
(`Iff.rfl`).

## 6. `ExistsUnique` (statements 6, 15, 19, 23)

`Mathlib/Basic/ExistsUnique.lean`, lines 21–22 —
[P`Mathlib/Basic/ExistsUnique.lean#L21-L22`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/ExistsUnique.lean#L21-L22):

```lean
/-- For `p : α → Prop`, `ExistsUnique p` means that there exists a unique `x : α` with `p x`. -/
def ExistsUnique (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x
```

Audit theorem `existsUnique_iff` (`Iff.rfl`). The notation `∃! x, p x` is `ExistsUnique fun x => p x`.

## 7. `minpoly` (statements 27, 30)

`Mathlib/FieldTheory/Minpoly/Basic.lean`, lines 31–42 —
[P`Mathlib/FieldTheory/Minpoly/Basic.lean#L31-L42`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/FieldTheory/Minpoly/Basic.lean#L31-L42):

```lean
/-- Suppose `x : B`, where `B` is an `A`-algebra.

The minimal polynomial `minpoly A x` of `x`
is a monic polynomial with coefficients in `A` of smallest degree that has `x` as its root,
if such exists (`IsIntegral A x`) or zero otherwise.

For example, if `V` is a `𝕜`-vector space for some field `𝕜` and `f : V →ₗ[𝕜] V` then
the minimal polynomial of `f` is `minpoly 𝕜 f`.
-/
@[stacks 09GM]
noncomputable def minpoly (x : B) : A[X] :=
  if hx : IsIntegral A x then degree_lt_wf.min _ hx else 0
```

Audit theorems `minpoly_monic`, `minpoly_aeval`, `minpoly_irreducible`, `minpoly_dvd` (Mathlib's
`minpoly.monic`, `minpoly.aeval`, `minpoly.irreducible`, `minpoly.dvd`). Statement 27 names
`minpoly ℚ ((8ρ² + ρ − 11)/25)` as the monic cubic `X³ + C (17/25) X² + C (2/25) X − C (1/25)`;
statement 30 evaluates the same polynomial at a complex number (section 12).

## 8. `IntermediateField.adjoin` and `Module.finrank` (statement 28)

`Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean`, lines 32–36 —
[P`Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean#L32-L36`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean#L32-L36):

```lean
/-- `adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`. -/
@[stacks 09FZ "first part"]
def adjoin : IntermediateField F E :=
  { Subfield.closure (Set.range (algebraMap F E) ∪ S) with
    algebraMap_mem' := fun x => Subfield.subset_closure (Or.inl (Set.mem_range_self x)) }
```

`Mathlib/LinearAlgebra/Dimension/Finrank.lean`, lines 62–63 —
[P`Mathlib/LinearAlgebra/Dimension/Finrank.lean#L62-L63`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Dimension/Finrank.lean#L62-L63):

```lean
noncomputable def finrank (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] : ℕ :=
  Cardinal.toNat (Module.rank R M)
```

Audit theorem `finrank_adjoin_eq_natDegree`: `[ℚ(x) : ℚ] = natDegree (minpoly ℚ x)` for integral
`x` (Mathlib's `IntermediateField.adjoin.finrank`). Statement 28 reads `[ℚ(v) : ℚ] = 3` for the
`K = 2` value `v`; `IntermediateField.adjoin ℚ {v}` is the subfield of `ℝ` generated by `v`.

## 9. `Polynomial.C`, `Polynomial.X` (statements 27, 29)

`Mathlib/Algebra/Polynomial/Basic.lean`, lines 429–436 and 478–480 —
[P`Mathlib/Algebra/Polynomial/Basic.lean#L429-L436`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Polynomial/Basic.lean#L429-L436),
[P`Mathlib/Algebra/Polynomial/Basic.lean#L478-L480`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Polynomial/Basic.lean#L478-L480):

```lean
/-- `C a` is the constant polynomial `a`.
`C` is provided as a ring homomorphism.
-/
def C : R →+* R[X] :=
  { monomial 0 with
    map_one' := by simp [monomial_zero_one]
    map_mul' := by simp [monomial_mul_monomial]
    map_zero' := by simp }
```

```lean
/-- `X` is the polynomial variable (aka indeterminate). -/
def X : R[X] :=
  monomial 1 1
```

Audit theorem `aeval_C_X`: evaluating `C a` at a real number gives `(a : ℝ)` and `X` gives the
number (Mathlib's `aeval_C`, `aeval_X`). In statement 29 the numerals `25`, `17`, `2`, `1` of
`ℚ[X]` are the constant polynomials `C 25`, … (Mathlib's `Polynomial.C_ofNat`, `C_1`).

## 10. `Irreducible` (statement 29)

`Mathlib/Algebra/Group/Irreducible/Defs.lean`, lines 43–48 —
[P`Mathlib/Algebra/Group/Irreducible/Defs.lean#L43-L48`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Irreducible/Defs.lean#L43-L48):

```lean
@[to_additive (attr := wikidata Q2989575)]
structure Irreducible (p : M) : Prop where
  /-- An irreducible element is not a unit. -/
  not_isUnit : ¬IsUnit p
  /-- If an irreducible element factors, then one factor is a unit. -/
  isUnit_or_isUnit ⦃a b : M⦄ : p = a * b → IsUnit a ∨ IsUnit b
```

Audit theorem `irreducible_iff` (Mathlib's `irreducible_iff`). In `ℚ[X]` the units are the nonzero
constants, so statement 29 says that `25x³ + 17x² + 2x − 1` has no factorisation into two
polynomials of positive degree over `ℚ`.

## 11. `HasDerivAt` (statement 5)

`Mathlib/Analysis/Calculus/Deriv/Basic.lean`, lines 112–117 (`HasDerivAtFilter`) and 126–131 (`HasDerivAt`) —
[P`Mathlib/Analysis/Calculus/Deriv/Basic.lean#L112-L131`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/Deriv/Basic.lean#L112-L131):

```lean
/-- `f` has the derivative `f'` along the filter `L`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `(x', x)` converges along the filter `L`.
-/
def HasDerivAtFilter (f : 𝕜 → F) (f' : F) (L : Filter (𝕜 × 𝕜)) :=
  HasFDerivAtFilter f (toSpanSingleton 𝕜 f') L
```

```lean
/-- `f` has the derivative `f'` at the point `x`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x`.
-/
def HasDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasDerivAtFilter f f' (𝓝 x ×ˢ pure x)
```

`Mathlib/Analysis/Calculus/FDeriv/Defs.lean`, lines 99–112 (`HasFDerivAtFilter`) —
[P`Mathlib/Analysis/Calculus/FDeriv/Defs.lean#L99-L112`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Defs.lean#L99-L112):

```lean
/-- A function `f` has the continuous linear map `f'` as derivative along the filter `L` if
`f x₁ = f x₂ + f' (x₁ - x₂) + o (x₁ - x₂)` when `x = (x₁, x₂)` converges along the filter `L`.
This definition is designed to be specialized

- for `L = 𝓝 (x, x)` (in `HasStrictFDerivAt`),
  giving rise to the derivative in the sense of strict differentiability;
- for `L = 𝓝 x ×ˢ pure x` (in `HasFDerivAt`), giving rise to the usual notion of Fréchet derivative;
- for `L = 𝓝[s] x ×ˢ pure x` (in `HasFDerivWithinAt`),
  giving rise to the notion of Fréchet derivative along the set `s`.
-/
@[mk_iff hasFDerivAtFilter_iff_isLittleOTVS]
structure HasFDerivAtFilter (f : E → F) (f' : E →L[𝕜] F) (L : Filter (E × E)) : Prop where
  of_isLittleOTVS ::
    isLittleOTVS : (fun p ↦ f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝕜; L] (fun p ↦ p.1 - p.2)
```

Audit theorems `hasDerivAt_iff_tendsto_slope'` (Mathlib's `hasDerivAt_iff_tendsto_slope`:
`HasDerivAt f f' x` iff the difference quotients `slope f x y` tend to `f'` as `y → x`, `y ≠ x`)
and `slope_eq_div` (`slope f x y = (f y − f x)/(y − x)`, Mathlib's `slope_def_field`). Statement 5
says that the written-out closed form `P_K*` has derivative
`2q(1 − q^{2K}) m_K(q)/((1 + q²)²(1 + q^{2K+1})³)` at every `q > 0`; the filter and the little-o
condition enter only through this definition.

## 12. `Polynomial.aeval` and `Complex` (statement 30)

`Mathlib/Algebra/Polynomial/AlgebraMap.lean`, lines 253–258 —
[P`Mathlib/Algebra/Polynomial/AlgebraMap.lean#L253-L258`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Polynomial/AlgebraMap.lean#L253-L258):

```lean
/-- Given a valuation `x` of the variable in an `R`-algebra `A`, `aeval R A x` is
the unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`.

This is a stronger variant of the linear map `Polynomial.leval`. -/
def aeval : R[X] →ₐ[R] A :=
  aevalEquiv R A x
```

`Mathlib/Basic/Complex/Basic.lean`, lines 33–39 —
[P`Mathlib/Basic/Complex/Basic.lean#L33-L39`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Complex/Basic.lean#L33-L39):

```lean
/-- Complex numbers consist of two `Real`s: a real part `re` and an imaginary part `im`. -/
@[wikidata Q11567]
structure Complex : Type where
  /-- The real part of a complex number. -/
  re : ℝ
  /-- The imaginary part of a complex number. -/
  im : ℝ
```

Audit theorems `aeval_C_X_complex` (evaluating `C a` at `z : ℂ` gives `(a : ℂ)` and `X` gives `z`,
Mathlib's `aeval_C`, `aeval_X`, `eq_ratCast`) and `im_eq_zero_iff` (a complex number has imaginary
part `0` iff it is a real number, Mathlib's `Complex.ofReal_im` and `Complex.ext`). Statement 30
says that some `z : ℂ` with `z.im ≠ 0` is a root of `minpoly ℚ ((8ρ² + ρ − 11)/25)` (section 7).
Mathlib's `minpoly` is `0` for an element that is not integral ("or zero otherwise", section 7),
for which statement 30 would hold trivially; the `K = 2` value is algebraic of degree 3, and
statement 27 identifies the polynomial as the monic cubic, so read with statement 27, statement
30 says that the `K = 2` value has a conjugate off the real line, i.e. is not totally real. Reading the complex roots of the minimal
polynomial as the conjugates is the standard meaning of the word, not an audit theorem.
