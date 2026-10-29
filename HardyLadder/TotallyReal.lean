module

public import Mathlib
public import HardyLadder.Plastic
public import HardyLadder.Minpoly

@[expose] public section

/-!
# The totally-real exclusion for the cubic field `ℚ(ρ)`

Let `L` be a number field of degree `3` containing a root `ρ` of `x³ − x − 1` (so `L = ℚ(ρ)`).
Then `L` is not totally real — the polynomial `x³ − x − 1` has exactly one real root, so some
embedding `L →+* ℂ` sends `ρ` off the real line — and, `L` having prime degree, its only
intermediate fields are `ℚ` and `L`. Hence every totally real subfield of `L` is `ℚ`, and every
`x ∈ L` whose field `ℚ(x)` is totally real (informally, every conjugate of `x` is real) lies in
`ℚ`.

Mathlib's `NumberField.IsTotallyReal K` says that every infinite place of `K` is real; for a
subfield `ℚ(x)` of `L` this is the statement that every embedding `ℚ(x) →+* ℂ` is real; reading
it as "every conjugate of `x` is real" is an informal gloss (through
`NumberField.Embeddings.range_eval_eq_rootSet_minpoly`).

The last section states the property for the `K = 2` value `v = (8ρ² + ρ − 11)/25` directly, in
terms of its conjugates: the minimal polynomial `x³ + (17/25) x² + (2/25) x − 1/25` of `v` over
`ℚ` (`minpoly_value`) is irreducible, so it has three distinct complex roots, and
`25x³ + 17x² + 2x − 1` has only one real root (it is negative for `x ≤ 0` and strictly increasing
for `x > 0`); so some root is off the real line (`exists_nonreal_root_minpoly_value`, which
proves compared statement 30). The other theorems of this file, including
`totallyReal_subfield_eq_bot` and `mem_bot_of_isTotallyReal_adjoin`, are uncompared library
lemmas.
-/

namespace HardyLadder

open Polynomial NumberField

/-! ### `x³ − x − 1` over `ℤ`, `ℚ`, `𝔽₂` -/

/-- `x³ − x − 1` over `ℤ`. -/
noncomputable def plasticZ : ℤ[X] := X ^ 3 - X - 1

theorem plasticZ_monic : plasticZ.Monic := by
  unfold plasticZ
  monicity!

theorem plasticZ_map2 : plasticZ.map (Int.castRingHom (ZMod 2)) = X ^ 3 + X + 1 := by
  unfold plasticZ
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    have e : (2 : ZMod 2) = 0 := by decide
    calc (2 : (ZMod 2)[X]) = C (2 : ZMod 2) := (C_ofNat 2).symm
      _ = C (0 : ZMod 2) := by rw [e]
      _ = 0 := by simp
  linear_combination (-(X : (ZMod 2)[X]) - 1) * h2

/-- `x³ − x − 1` is irreducible over `ℤ`. -/
theorem plasticZ_irred : Irreducible plasticZ := by
  apply plasticZ_monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2))
  rw [plasticZ_map2]
  exact cubic_irred_zmod2

/-- `x³ − x − 1` is irreducible over `ℚ`. -/
theorem plasticQ_irreducible : Irreducible (X ^ 3 - X - 1 : ℚ[X]) := by
  have h := (plasticZ_monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp plasticZ_irred
  have hmap : plasticZ.map (algebraMap ℤ ℚ) = (X ^ 3 - X - 1 : ℚ[X]) := by
    unfold plasticZ
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  rwa [hmap] at h

theorem plasticQ_monic : (X ^ 3 - X - 1 : ℚ[X]).Monic := by monicity!

theorem plasticQ_natDegree : (X ^ 3 - X - 1 : ℚ[X]).natDegree = 3 := by compute_degree!

section Minpoly

variable {L : Type*} [Field L] [Algebra ℚ L]

theorem aeval_plastic {ρ : L} (hρ : ρ ^ 3 = ρ + 1) : aeval ρ (X ^ 3 - X - 1 : ℚ[X]) = 0 := by
  simp only [map_sub, map_pow, aeval_X, map_one]
  rw [hρ]
  ring

/-- The minimal polynomial of a root of `x³ − x − 1` over `ℚ`. -/
theorem minpoly_plastic {ρ : L} (hρ : ρ ^ 3 = ρ + 1) : minpoly ℚ ρ = X ^ 3 - X - 1 :=
  (minpoly.eq_of_irreducible_of_monic plasticQ_irreducible (aeval_plastic hρ) plasticQ_monic).symm

end Minpoly

/-! ### The complex roots of `x³ − x − 1`: at most one is real -/

/-- Two real roots of `z³ = z + 1` in `ℂ` coincide. -/
theorem complex_root_eq_of_im_eq_zero {z w : ℂ} (hz : z ^ 3 = z + 1) (hw : w ^ 3 = w + 1)
    (hzi : z.im = 0) (hwi : w.im = 0) : z = w := by
  have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hzi])
  have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [hwi])
  rw [hz'] at hz
  rw [hw'] at hw
  have hz'' : z.re ^ 3 = z.re + 1 := by exact_mod_cast hz
  have hw'' : w.re ^ 3 = w.re + 1 := by exact_mod_cast hw
  rw [hz', hw', eq_of_cubic hz'' hw'']

/-- A root of `x³ − x − 1` in `ℂ` satisfies `z³ = z + 1`. -/
theorem cubic_of_mem_rootSet {z : ℂ} (hz : z ∈ (X ^ 3 - X - 1 : ℚ[X]).rootSet ℂ) :
    z ^ 3 = z + 1 := by
  rw [mem_rootSet] at hz
  have h := hz.2
  simp only [map_sub, map_pow, aeval_X, map_one] at h
  linear_combination h

/-- The root set of `x³ − x − 1` in `ℂ` has three elements. -/
theorem card_rootSet_plastic : Fintype.card ((X ^ 3 - X - 1 : ℚ[X]).rootSet ℂ) = 3 := by
  rw [card_rootSet_eq_natDegree plasticQ_irreducible.separable
    (IsAlgClosed.splits ((X ^ 3 - X - 1 : ℚ[X]).map (algebraMap ℚ ℂ))), plasticQ_natDegree]

section NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- **A non-real embedding.** Some embedding `L →+* ℂ` sends a root `ρ` of `x³ − x − 1` to a
non-real number: the three complex roots cannot all be real, since the real root is unique. -/
theorem exists_embedding_im_ne_zero (ρ : L) (hρ : ρ ^ 3 = ρ + 1) :
    ∃ φ : L →+* ℂ, (φ ρ).im ≠ 0 := by
  have hroot : Set.range (fun φ : L →+* ℂ => φ ρ) = (minpoly ℚ ρ).rootSet ℂ :=
    NumberField.Embeddings.range_eval_eq_rootSet_minpoly L ℂ ρ
  rw [minpoly_plastic hρ] at hroot
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hcard : 1 < Fintype.card ((X ^ 3 - X - 1 : ℚ[X]).rootSet ℂ) := by
    rw [card_rootSet_plastic]; norm_num
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hcard
  have ha : (a : ℂ) ∈ Set.range (fun φ : L →+* ℂ => φ ρ) := by rw [hroot]; exact a.2
  have hb : (b : ℂ) ∈ Set.range (fun φ : L →+* ℂ => φ ρ) := by rw [hroot]; exact b.2
  obtain ⟨φa, hφa⟩ := ha
  obtain ⟨φb, hφb⟩ := hb
  have hai : (a : ℂ).im = 0 := by rw [← hφa]; exact hcon φa
  have hbi : (b : ℂ).im = 0 := by rw [← hφb]; exact hcon φb
  exact hab (Subtype.ext (complex_root_eq_of_im_eq_zero (cubic_of_mem_rootSet a.2)
    (cubic_of_mem_rootSet b.2) hai hbi))

/-- **`ℚ(ρ)` is not totally real.** -/
theorem not_isTotallyReal_of_cubic (ρ : L) (hρ : ρ ^ 3 = ρ + 1) : ¬ IsTotallyReal L := by
  intro h
  obtain ⟨φ, hφ⟩ := exists_embedding_im_ne_zero ρ hρ
  have hreal : (InfinitePlace.mk φ).IsReal := h.isReal _
  rw [InfinitePlace.isReal_mk_iff] at hreal
  have hconj : ComplexEmbedding.conjugate φ = φ := ComplexEmbedding.isReal_iff.mp hreal
  have := congrArg (fun ψ : L →+* ℂ => ψ ρ) hconj
  simp only [ComplexEmbedding.conjugate_coe_eq] at this
  exact hφ (Complex.conj_eq_iff_im.mp this)

/-- **The totally-real exclusion for the cubic field.** Every totally real subfield of a cubic
number field containing a root of `x³ − x − 1` is `ℚ`. -/
theorem totallyReal_subfield_eq_bot (hL : Module.finrank ℚ L = 3) (ρ : L) (hρ : ρ ^ 3 = ρ + 1)
    (F : IntermediateField ℚ L) [IsTotallyReal F] : F = ⊥ := by
  have hsimple : IsSimpleOrder (IntermediateField ℚ L) :=
    IntermediateField.isSimpleOrder_of_finrank_prime ℚ L (by rw [hL]; norm_num)
  rcases hsimple.eq_bot_or_eq_top F with h | h
  · exact h
  · exfalso
    subst h
    exact not_isTotallyReal_of_cubic ρ hρ
      (IsTotallyReal.ofRingEquiv (IntermediateField.topEquiv (F := ℚ) (E := L)).toRingEquiv)

/-- **No element outside `ℚ` is totally real.** If `ℚ(x)` is totally real for `x ∈ ℚ(ρ)`
(informally, every conjugate of `x` is real), then `x ∈ ℚ`. -/
theorem mem_bot_of_isTotallyReal_adjoin (hL : Module.finrank ℚ L = 3) (ρ : L)
    (hρ : ρ ^ 3 = ρ + 1) (x : L) [IsTotallyReal (IntermediateField.adjoin ℚ {x})] :
    x ∈ (⊥ : IntermediateField ℚ L) := by
  have h := totallyReal_subfield_eq_bot hL ρ hρ (IntermediateField.adjoin ℚ {x})
  rw [← h]
  exact IntermediateField.mem_adjoin_simple_self ℚ x

end NumberField

/-! ### The `K = 2` value has a non-real conjugate -/

/-- A real root of `25x³ + 17x² + 2x − 1` is positive: for `x ≤ 0`,
`25x³ + 17x² + 2x − 1 = 25x (x + 2/5)² − 3 (x + 1/3)² − 2/3 < 0`. -/
theorem pos_of_value_cubic {x : ℝ} (hx : 25 * x ^ 3 + 17 * x ^ 2 + 2 * x - 1 = 0) : 0 < x := by
  by_contra h
  rw [not_lt] at h
  nlinarith [mul_nonneg (neg_nonneg.mpr h) (sq_nonneg (x + 2 / 5)), sq_nonneg (x + 1 / 3)]

/-- `25x³ + 17x² + 2x − 1` has at most one real root (two positive roots `x ≠ y` would make
`25(x² + xy + y²) + 17(x + y) + 2` vanish). -/
theorem eq_of_value_cubic {x y : ℝ} (hx : 25 * x ^ 3 + 17 * x ^ 2 + 2 * x - 1 = 0)
    (hy : 25 * y ^ 3 + 17 * y ^ 2 + 2 * y - 1 = 0) : x = y := by
  have hx0 := pos_of_value_cubic hx
  have hy0 := pos_of_value_cubic hy
  have h : (x - y) * (25 * (x ^ 2 + x * y + y ^ 2) + 17 * (x + y) + 2) = 0 := by
    linear_combination hx - hy
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · have : 0 < 25 * (x ^ 2 + x * y + y ^ 2) + 17 * (x + y) + 2 := by positivity
    linarith

/-- A complex root of `x³ + (17/25) x² + (2/25) x − 1/25` on the real line is a real root of
`25x³ + 17x² + 2x − 1`. -/
theorem value_cubic_re_of_root {z : ℂ} (hz : aeval z mQ = 0) (hzi : z.im = 0) :
    25 * z.re ^ 3 + 17 * z.re ^ 2 + 2 * z.re - 1 = 0 := by
  have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hzi])
  unfold mQ at hz
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, eq_ratCast, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_one] at hz
  rw [hz'] at hz
  have h : ((25 * z.re ^ 3 + 17 * z.re ^ 2 + 2 * z.re - 1 : ℝ) : ℂ) = 0 := by
    push_cast
    linear_combination 25 * hz
  exact_mod_cast h

/-- **The `K = 2` value is not totally real.** For `ρ³ = ρ + 1`, the minimal polynomial of
`(8ρ² + ρ − 11)/25` over `ℚ` has a root in `ℂ` off the real line: of its three complex roots
(it is irreducible, hence separable) at most one is real. -/
theorem exists_nonreal_root_minpoly_value {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    ∃ z : ℂ, z.im ≠ 0 ∧ aeval z (minpoly ℚ ((8 * ρ ^ 2 + ρ - 11) / 25)) = 0 := by
  have hmin : minpoly ℚ ((8 * ρ ^ 2 + ρ - 11) / 25) = mQ := minpoly_value hρ
  rw [hmin]
  have hirr : Irreducible mQ := by
    have h := minpoly.irreducible (isIntegral_value hρ)
    rwa [hmin] at h
  have hcard : Fintype.card (mQ.rootSet ℂ) = 3 := by
    rw [card_rootSet_eq_natDegree hirr.separable (IsAlgClosed.splits (mQ.map (algebraMap ℚ ℂ))),
      mQ_natDegree]
  by_contra hcon
  have hreal : ∀ z : ℂ, aeval z mQ = 0 → z.im = 0 := fun z hz => by
    by_contra h
    exact hcon ⟨z, h, hz⟩
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card
    (show 1 < Fintype.card (mQ.rootSet ℂ) by rw [hcard]; norm_num)
  have ha : aeval (a : ℂ) mQ = 0 := (mem_rootSet.mp a.2).2
  have hb : aeval (b : ℂ) mQ = 0 := (mem_rootSet.mp b.2).2
  have hai := hreal _ ha
  have hbi := hreal _ hb
  exact hab (Subtype.ext (Complex.ext
    (eq_of_value_cubic (value_cubic_re_of_root ha hai) (value_cubic_re_of_root hb hbi))
    (hai.trans hbi.symm)))

end HardyLadder
