module

public import Mathlib

@[expose] public section

/-!
# Audit of the imported definitions

The compared statements in `Challenge.lean` rest on definitions imported from Mathlib (pinned
revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`): the real trigonometric functions `Real.cos`,
`Real.sin` (statements 1–4, 9–11, 16–18, 24–26), the golden ratio `Real.goldenRatio`
(statements 12–18), the square root `Real.sqrt` (statements 13, 17, 18), `IsGreatest` and the
image of `Set.Ioo` (statements 7, 12, 20), `ExistsUnique` (statements 6, 15, 19, 23),
`HasDerivAt` (statement 5), `minpoly` (statements 27, 30), `IntermediateField.adjoin` with
`Module.finrank` (statement 28), `Polynomial.C`, `Polynomial.X`, `Irreducible` (statements 27,
29), and `Polynomial.aeval` with the imaginary part `Complex.im` (statement 30). Their pinned
source text is quoted verbatim, with permalinks, in `MATHLIB_DEFINITIONS.md`. This file imports
Mathlib only and is not part of the compared set. It records, as kernel-checked theorems, the
facts about those definitions that the informal account relies on, so that the correspondence
can be audited from this repository alone:

* `cos_sq_add_sin_sq` — `(cos a, sin a)` is a unit vector: `cos a ^ 2 + sin a ^ 2 = 1`
  (Mathlib's `Real.cos_sq_add_sin_sq`). This is what makes `(cos aₖ, sin aₖ)` a measurement
  direction and `(−sin aₖ, cos aₖ)` its orthogonal complement.
* `cos_sin_orthogonal` — `(cos a, sin a)` and `(−sin a, cos a)` are orthogonal (`ring`).
* `goldenRatio_def` — `Real.goldenRatio = (1 + √5)/2` (`rfl`); `goldenRatio_sq` — `φ² = φ + 1`
  (Mathlib's `Real.goldenRatio_sq`).
* `sq_sqrt_five` — `√5 ^ 2 = 5` (Mathlib's `Real.sq_sqrt`); with `0 ≤ √5` (`Real.sqrt_nonneg`),
  the properties of `√5` used in the proof of statement 13.
* `isGreatest_iff` — `IsGreatest s m ↔ m ∈ s ∧ ∀ x ∈ s, x ≤ m` (Mathlib's definition;
  `Iff.rfl` up to `upperBounds`).
* `mem_image_Ioo` — `y ∈ f '' Set.Ioo 0 1 ↔ ∃ q, (0 < q ∧ q < 1) ∧ f q = y` (Mathlib's
  `Set.mem_image` and `Set.mem_Ioo`).
* `existsUnique_iff` — `(∃! x, p x) ↔ ∃ x, p x ∧ ∀ y, p y → y = x` (Mathlib's `ExistsUnique`;
  `Iff.rfl`).
* `minpoly_monic`, `minpoly_aeval`, `minpoly_irreducible` — for `x : ℝ` integral over `ℚ`,
  `minpoly ℚ x` is monic, vanishes at `x`, and is irreducible (Mathlib's `minpoly.monic`,
  `minpoly.aeval`, `minpoly.irreducible`); `minpoly_dvd` — it divides every rational polynomial
  vanishing at `x` (`minpoly.dvd`). Statements 27 and 30 name this polynomial.
* `finrank_adjoin_eq_natDegree` — `[ℚ(x) : ℚ] = natDegree (minpoly ℚ x)` for integral `x`
  (Mathlib's `IntermediateField.adjoin.finrank`). Statement 28 reads `3` off statement 27.
* `aeval_C_X` — `aeval x (C a) = a` and `aeval x X = x` (Mathlib's `aeval_C`, `aeval_X`,
  `eq_ratCast`): how the polynomial of statements 27 and 29 evaluates at a real number;
  `aeval_C_X_complex` — the same at a complex number `z`: how statement 30 evaluates the minimal
  polynomial at `z`.
* `irreducible_iff` — `Irreducible p ↔ ¬IsUnit p ∧ ∀ a b, p = a * b → IsUnit a ∨ IsUnit b`
  (Mathlib's `irreducible_iff`).
* `hasDerivAt_iff_tendsto_slope'` — `HasDerivAt f f' x` iff the difference quotients
  `slope f x y = (f y − f x)/(y − x)` tend to `f'` as `y → x`, `y ≠ x` (Mathlib's
  `hasDerivAt_iff_tendsto_slope`; `slope_eq_div` is Mathlib's `slope_def_field`): the reading of
  statement 5 as "the derivative of `P_K*` at `q` is …".
* `im_eq_zero_iff` — a complex number has imaginary part `0` iff it is (the image of) a real
  number (Mathlib's `Complex.ofReal_im`, `Complex.ext`): in statement 30, `z.im ≠ 0` says that the
  root `z` is not real. Reading "a root in `ℂ` of the minimal polynomial" as "a conjugate" is the
  standard meaning of the word, not one of the theorems below.

Each theorem is a restatement of the named Mathlib declaration or a `rfl`/`Iff.rfl`/`ring`/`simp`
step; none uses anything from this entry.
-/

namespace DefinitionAudit

open Real Polynomial

/-- `(cos a, sin a)` is a unit vector (Mathlib's `Real.cos_sq_add_sin_sq`). -/
theorem cos_sq_add_sin_sq (a : ℝ) : cos a ^ 2 + sin a ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq a

/-- `(cos a, sin a)` is orthogonal to `(−sin a, cos a)`. -/
theorem cos_sin_orthogonal (a : ℝ) : cos a * (-sin a) + sin a * cos a = 0 := by ring

/-- The golden ratio is `(1 + √5)/2` (Mathlib's definition; `rfl`). -/
theorem goldenRatio_def : goldenRatio = (1 + √5) / 2 := rfl

/-- `φ² = φ + 1` (Mathlib's `Real.goldenRatio_sq`). -/
theorem goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 :=
  Real.goldenRatio_sq

/-- `√5 ^ 2 = 5` (Mathlib's `Real.sq_sqrt`). -/
theorem sq_sqrt_five : (√5 : ℝ) ^ 2 = 5 :=
  Real.sq_sqrt (by norm_num)

/-- `IsGreatest s m` unfolds to `m ∈ s` and `m` is an upper bound of `s` (Mathlib's definition). -/
theorem isGreatest_iff (s : Set ℝ) (m : ℝ) : IsGreatest s m ↔ m ∈ s ∧ ∀ x ∈ s, x ≤ m :=
  Iff.rfl

/-- Membership in the image of `Set.Ioo 0 1` (Mathlib's `Set.mem_image`, `Set.mem_Ioo`). -/
theorem mem_image_Ioo (f : ℝ → ℝ) (y : ℝ) :
    y ∈ f '' Set.Ioo (0 : ℝ) 1 ↔ ∃ q : ℝ, (0 < q ∧ q < 1) ∧ f q = y :=
  Iff.rfl

/-- `∃!` unfolds to existence plus uniqueness (Mathlib's `ExistsUnique`; `Iff.rfl`). -/
theorem existsUnique_iff (p : ℝ → Prop) : (∃! x, p x) ↔ ∃ x, p x ∧ ∀ y, p y → y = x :=
  Iff.rfl

/-- The minimal polynomial is monic (Mathlib's `minpoly.monic`). -/
theorem minpoly_monic {x : ℝ} (hx : IsIntegral ℚ x) : (minpoly ℚ x).Monic :=
  minpoly.monic hx

/-- The minimal polynomial vanishes at `x` (Mathlib's `minpoly.aeval`). -/
theorem minpoly_aeval (x : ℝ) : aeval x (minpoly ℚ x) = 0 :=
  minpoly.aeval ℚ x

/-- The minimal polynomial is irreducible (Mathlib's `minpoly.irreducible`). -/
theorem minpoly_irreducible {x : ℝ} (hx : IsIntegral ℚ x) : Irreducible (minpoly ℚ x) :=
  minpoly.irreducible hx

/-- The minimal polynomial divides every rational polynomial vanishing at `x`
(Mathlib's `minpoly.dvd`). -/
theorem minpoly_dvd (x : ℝ) {p : ℚ[X]} (hp : aeval x p = 0) : minpoly ℚ x ∣ p :=
  minpoly.dvd ℚ x hp

/-- `[ℚ(x) : ℚ]` is the degree of the minimal polynomial (Mathlib's
`IntermediateField.adjoin.finrank`). -/
theorem finrank_adjoin_eq_natDegree {x : ℝ} (hx : IsIntegral ℚ x) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = (minpoly ℚ x).natDegree :=
  IntermediateField.adjoin.finrank hx

/-- Evaluation of constants and of `X` at a real number (Mathlib's `aeval_C`, `aeval_X`,
`eq_ratCast`). -/
theorem aeval_C_X (x : ℝ) (a : ℚ) : aeval x (C a) = (a : ℝ) ∧ aeval x (X : ℚ[X]) = x :=
  ⟨by simp, by simp⟩

/-- `Irreducible` unfolds to: not a unit, and every factorisation has a unit factor
(Mathlib's `irreducible_iff`). -/
theorem irreducible_iff (p : ℚ[X]) :
    Irreducible p ↔ ¬IsUnit p ∧ ∀ a b, p = a * b → IsUnit a ∨ IsUnit b :=
  _root_.irreducible_iff

/-- Evaluation of constants and of `X` at a complex number (Mathlib's `aeval_C`, `aeval_X`,
`eq_ratCast`). -/
theorem aeval_C_X_complex (z : ℂ) (a : ℚ) : aeval z (C a) = (a : ℂ) ∧ aeval z (X : ℚ[X]) = z :=
  ⟨by simp, by simp⟩

/-- `HasDerivAt f f' x` iff the difference quotients tend to `f'` (Mathlib's
`hasDerivAt_iff_tendsto_slope`). -/
theorem hasDerivAt_iff_tendsto_slope' (f : ℝ → ℝ) (f' x : ℝ) :
    HasDerivAt f f' x ↔ Filter.Tendsto (slope f x) (nhdsWithin x {x}ᶜ) (nhds f') :=
  hasDerivAt_iff_tendsto_slope

/-- The difference quotient (Mathlib's `slope_def_field`). -/
theorem slope_eq_div (f : ℝ → ℝ) (x y : ℝ) : slope f x y = (f y - f x) / (y - x) :=
  slope_def_field f x y

/-- A complex number has imaginary part `0` iff it is a real number (Mathlib's
`Complex.ofReal_im`, `Complex.ext`). -/
theorem im_eq_zero_iff (z : ℂ) : z.im = 0 ↔ ∃ x : ℝ, (x : ℂ) = z := by
  constructor
  · intro h
    exact ⟨z.re, Complex.ext (by simp) (by simp [h])⟩
  · rintro ⟨x, rfl⟩
    simp

end DefinitionAudit

-- Axiom audit of this file: every declaration must depend on at most
-- {propext, Classical.choice, Quot.sound}.
#print axioms DefinitionAudit.cos_sq_add_sin_sq
#print axioms DefinitionAudit.cos_sin_orthogonal
#print axioms DefinitionAudit.goldenRatio_def
#print axioms DefinitionAudit.goldenRatio_sq
#print axioms DefinitionAudit.sq_sqrt_five
#print axioms DefinitionAudit.isGreatest_iff
#print axioms DefinitionAudit.mem_image_Ioo
#print axioms DefinitionAudit.existsUnique_iff
#print axioms DefinitionAudit.minpoly_monic
#print axioms DefinitionAudit.minpoly_aeval
#print axioms DefinitionAudit.minpoly_irreducible
#print axioms DefinitionAudit.minpoly_dvd
#print axioms DefinitionAudit.finrank_adjoin_eq_natDegree
#print axioms DefinitionAudit.aeval_C_X
#print axioms DefinitionAudit.irreducible_iff
#print axioms DefinitionAudit.aeval_C_X_complex
#print axioms DefinitionAudit.hasDerivAt_iff_tendsto_slope'
#print axioms DefinitionAudit.slope_eq_div
#print axioms DefinitionAudit.im_eq_zero_iff
