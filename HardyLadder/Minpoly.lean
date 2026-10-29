module

public import Mathlib
public import HardyLadder.Plastic
public import HardyLadder.HardyK2

@[expose] public section

/-!
# The minimal polynomial of the K = 2 optimum

`v = (8ρ² + ρ − 11)/25` satisfies `25v³ + 17v² + 2v − 1 = 0`. Its reciprocal `w = v⁻¹` is a root
of the monic integer cubic `x³ − 2x² − 17x − 25`, which is irreducible over `ℤ` (it reduces to
`x³ + x + 1` over `𝔽₂`, which has no root), hence over `ℚ` (Gauss), so `[ℚ(w) : ℚ] = 3`; since
`ℚ(v) = ℚ(w)`, the minimal polynomial of `v` over `ℚ` has degree `3` and is the monic cubic
`x³ + (17/25) x² + (2/25) x − 1/25`, i.e. `25x³ + 17x² + 2x − 1` is irreducible over `ℚ`, and
`v` generates a cubic field.
-/

namespace HardyLadder

open Polynomial

/-- `x³ + x + 1` is irreducible over `𝔽₂` (no root). -/
theorem cubic_irred_zmod2 : Irreducible (X ^ 3 + X + 1 : (ZMod 2)[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hd : (X ^ 3 + X + 1 : (ZMod 2)[X]).natDegree = 3 := by compute_degree!
    rw [Finset.mem_Icc, hd]
    omega
  · intro x
    rw [IsRoot.def]
    simp only [eval_add, eval_pow, eval_X, eval_one]
    fin_cases x <;> decide

/-- The reversed polynomial `x³ − 2x² − 17x − 25` over `ℤ`. -/
noncomputable def revZ : ℤ[X] := X ^ 3 - 2 * X ^ 2 - 17 * X - 25

theorem revZ_monic : revZ.Monic := by
  unfold revZ
  monicity!

theorem revZ_map2 : revZ.map (Int.castRingHom (ZMod 2)) = X ^ 3 + X + 1 := by
  unfold revZ
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat]
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    have e : (2 : ZMod 2) = 0 := by decide
    calc (2 : (ZMod 2)[X]) = C (2 : ZMod 2) := (C_ofNat 2).symm
      _ = C (0 : ZMod 2) := by rw [e]
      _ = 0 := by simp
  linear_combination (-(X : (ZMod 2)[X]) ^ 2 - 9 * X - 13) * h2

/-- `x³ − 2x² − 17x − 25` is irreducible over `ℤ`. -/
theorem revZ_irred : Irreducible revZ := by
  apply revZ_monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2))
  rw [revZ_map2]
  exact cubic_irred_zmod2

/-- `x³ − 2x² − 17x − 25` is irreducible over `ℚ`. -/
theorem revQ_irreducible : Irreducible (X ^ 3 - 2 * X ^ 2 - 17 * X - 25 : ℚ[X]) := by
  have h := (revZ_monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp revZ_irred
  have hmap : revZ.map (algebraMap ℤ ℚ) = (X ^ 3 - 2 * X ^ 2 - 17 * X - 25 : ℚ[X]) := by
    unfold revZ
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat]
  rwa [hmap] at h

theorem revQ_monic : (X ^ 3 - 2 * X ^ 2 - 17 * X - 25 : ℚ[X]).Monic := by monicity!

theorem revQ_natDegree : (X ^ 3 - 2 * X ^ 2 - 17 * X - 25 : ℚ[X]).natDegree = 3 := by
  compute_degree!

theorem aeval_rev {w : ℝ} (hw : w ^ 3 - 2 * w ^ 2 - 17 * w - 25 = 0) :
    aeval w (X ^ 3 - 2 * X ^ 2 - 17 * X - 25 : ℚ[X]) = 0 := by
  simp only [map_sub, map_mul, map_pow, aeval_X, map_ofNat]
  linear_combination hw

theorem isIntegral_rev {w : ℝ} (hw : w ^ 3 - 2 * w ^ 2 - 17 * w - 25 = 0) : IsIntegral ℚ w :=
  ⟨X ^ 3 - 2 * X ^ 2 - 17 * X - 25, revQ_monic, by rw [← aeval_def]; exact aeval_rev hw⟩

/-- The minimal polynomial of a real root of the reversed cubic. -/
theorem minpoly_rev {w : ℝ} (hw : w ^ 3 - 2 * w ^ 2 - 17 * w - 25 = 0) :
    minpoly ℚ w = X ^ 3 - 2 * X ^ 2 - 17 * X - 25 := by
  symm
  exact minpoly.eq_of_irreducible_of_monic revQ_irreducible (aeval_rev hw) revQ_monic

/-! ### The value `v` -/

/-- The monic rational cubic `x³ + (17/25) x² + (2/25) x − 1/25`. -/
noncomputable def mQ : ℚ[X] := X ^ 3 + C (17 / 25 : ℚ) * X ^ 2 + C (2 / 25 : ℚ) * X - C (1 / 25 : ℚ)

theorem mQ_monic : mQ.Monic := by
  unfold mQ
  monicity!

theorem mQ_natDegree : mQ.natDegree = 3 := by
  unfold mQ
  compute_degree!

/-- `25v³ + 17v² + 2v − 1 = 0` for `v = (8ρ² + ρ − 11)/25`. -/
theorem value_cubic {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    25 * ((8 * ρ ^ 2 + ρ - 11) / 25) ^ 3 + 17 * ((8 * ρ ^ 2 + ρ - 11) / 25) ^ 2 +
      2 * ((8 * ρ ^ 2 + ρ - 11) / 25) - 1 = 0 := by
  linear_combination (512 * ρ ^ 3 / 625 + 192 * ρ ^ 2 / 625 - 488 * ρ / 625 + 449 / 625) * hρ

theorem aeval_mQ {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) : aeval ((8 * ρ ^ 2 + ρ - 11) / 25) mQ = 0 := by
  unfold mQ
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, eq_ratCast, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_one]
  linear_combination (1 / 25 : ℝ) * value_cubic hρ

theorem isIntegral_value {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) : IsIntegral ℚ ((8 * ρ ^ 2 + ρ - 11) / 25) :=
  ⟨mQ, mQ_monic, by rw [← aeval_def]; exact aeval_mQ hρ⟩

/-- The reciprocal `w = v⁻¹` is a root of the reversed cubic. -/
theorem inv_value_rev {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    ((8 * ρ ^ 2 + ρ - 11) / 25)⁻¹ ^ 3 - 2 * ((8 * ρ ^ 2 + ρ - 11) / 25)⁻¹ ^ 2 -
      17 * ((8 * ρ ^ 2 + ρ - 11) / 25)⁻¹ - 25 = 0 := by
  have hv : (8 * ρ ^ 2 + ρ - 11) / 25 ≠ 0 := (value_pos hρ).ne'
  have h := value_cubic hρ
  set v := (8 * ρ ^ 2 + ρ - 11) / 25 with hvdef
  have key : v⁻¹ ^ 3 - 2 * v⁻¹ ^ 2 - 17 * v⁻¹ - 25 =
      -(25 * v ^ 3 + 17 * v ^ 2 + 2 * v - 1) / v ^ 3 := by
    field_simp
    ring
  rw [key, h, neg_zero, zero_div]

/-- `ℚ(v) = ℚ(v⁻¹)`. -/
theorem adjoin_eq_adjoin_inv (v : ℝ) :
    IntermediateField.adjoin ℚ {v} = IntermediateField.adjoin ℚ {v⁻¹} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := IntermediateField.mem_adjoin_simple_self ℚ v⁻¹
    simpa using inv_mem this
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self ℚ v)

/-- **`v` generates a cubic field**: `[ℚ(v) : ℚ] = 3`. -/
theorem finrank_adjoin_value {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {(8 * ρ ^ 2 + ρ - 11) / 25}) = 3 := by
  rw [adjoin_eq_adjoin_inv, IntermediateField.adjoin.finrank (isIntegral_rev (inv_value_rev hρ)),
    minpoly_rev (inv_value_rev hρ), revQ_natDegree]

/-- **The minimal polynomial of the K = 2 optimum** is `x³ + (17/25) x² + (2/25) x − 1/25`. -/
theorem minpoly_value {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    minpoly ℚ ((8 * ρ ^ 2 + ρ - 11) / 25) =
      X ^ 3 + C (17 / 25 : ℚ) * X ^ 2 + C (2 / 25 : ℚ) * X - C (1 / 25 : ℚ) := by
  have hint := isIntegral_value hρ
  have hdeg : (minpoly ℚ ((8 * ρ ^ 2 + ρ - 11) / 25)).natDegree = 3 := by
    rw [← IntermediateField.adjoin.finrank hint, finrank_adjoin_value hρ]
  have h := Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) mQ_monic
    (minpoly.dvd ℚ _ (aeval_mQ hρ)) (by rw [hdeg, mQ_natDegree])
  rw [← h]
  rfl

/-- **`25x³ + 17x² + 2x − 1` is irreducible over `ℚ`.** -/
theorem irreducible_25 {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    Irreducible (25 * X ^ 3 + 17 * X ^ 2 + 2 * X - 1 : ℚ[X]) := by
  have hirr : Irreducible (minpoly ℚ ((8 * ρ ^ 2 + ρ - 11) / 25)) :=
    minpoly.irreducible (isIntegral_value hρ)
  rw [minpoly_value hρ] at hirr
  have hunit : IsUnit (C (25 : ℚ)) := Polynomial.isUnit_C.mpr (by norm_num)
  have heq : (25 * X ^ 3 + 17 * X ^ 2 + 2 * X - 1 : ℚ[X]) =
      C (25 : ℚ) * (X ^ 3 + C (17 / 25 : ℚ) * X ^ 2 + C (2 / 25 : ℚ) * X - C (1 / 25 : ℚ)) := by
    rw [mul_sub, mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, ← C_mul]
    rw [show (25 : ℚ) * (17 / 25) = 17 by norm_num, show (25 : ℚ) * (2 / 25) = 2 by norm_num,
      show (25 : ℚ) * (1 / 25) = 1 by norm_num, C_ofNat, C_ofNat, C_ofNat, C_1]
  rw [heq]
  exact (associated_unit_mul_left _ _ hunit).symm.irreducible hirr

end HardyLadder
