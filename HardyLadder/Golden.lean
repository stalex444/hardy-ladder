module

public import Mathlib

@[expose] public section

/-!
# Golden-ratio identities for the K = 1 optimum

Hardy's value `(5√5 − 11)/2` is `φ⁻⁵` for the golden ratio `φ = (1 + √5)/2` (Mathlib's
`Real.goldenRatio`); `φ⁴ = 3φ + 2`, `φ⁵ = 5φ + 3`, and the root `q* = (φ² − √(3φ − 2))/2` of
`q² − φ² q + 1` lies in `(0, 1)`.
-/

namespace HardyLadder

open Real

/-- `φ⁵ = (11 + 5√5)/2`. -/
theorem goldenRatio_pow_five : goldenRatio ^ 5 = (11 + 5 * √5) / 2 := by
  have ht : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [goldenRatio]
  linear_combination ((√5 : ℝ) ^ 3 / 32 + 5 * (√5 : ℝ) ^ 2 / 32 + 15 * √5 / 32 + 35 / 32) * ht

/-- **Hardy's value is `φ⁻⁵`**: `φ⁻¹ ^ 5 = (5√5 − 11)/2`. -/
theorem goldenRatio_inv_pow_five : goldenRatio⁻¹ ^ 5 = (5 * √5 - 11) / 2 := by
  have ht : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5 : goldenRatio ^ 5 = (11 + 5 * √5) / 2 := goldenRatio_pow_five
  have hne : goldenRatio ^ 5 ≠ 0 := pow_ne_zero _ goldenRatio_ne_zero
  rw [inv_pow, inv_eq_iff_eq_inv, inv_div, h5]
  have hne : (5 * √5 - 11 : ℝ) ≠ 0 := by
    intro h
    nlinarith [Real.sqrt_nonneg 5]
  rw [div_eq_div_iff (by norm_num) hne]
  linear_combination (25 : ℝ) * ht

/-- `φ⁴ = 3φ + 2`. -/
theorem goldenRatio_pow_four : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
  have h := goldenRatio_sq
  linear_combination (goldenRatio ^ 2 + goldenRatio + 2) * h

/-- `φ⁵ = 5φ + 3`. -/
theorem goldenRatio_pow_five' : goldenRatio ^ 5 = 5 * goldenRatio + 3 := by
  have h := goldenRatio_sq
  linear_combination (goldenRatio ^ 3 + goldenRatio ^ 2 + 2 * goldenRatio + 3) * h

/-- `3φ − 2 > 0`. -/
theorem three_goldenRatio_sub_two_pos : 0 < 3 * goldenRatio - 2 := by
  have := one_lt_goldenRatio
  linarith

/-- The root `q* = (φ² − √(3φ − 2))/2` of `q² − φ² q + 1`. -/
noncomputable def qstar1 : ℝ := (goldenRatio ^ 2 - √(3 * goldenRatio - 2)) / 2

theorem qstar1_root : qstar1 ^ 2 - goldenRatio ^ 2 * qstar1 + 1 = 0 := by
  unfold qstar1
  have ht : (√(3 * goldenRatio - 2)) ^ 2 = 3 * goldenRatio - 2 :=
    Real.sq_sqrt three_goldenRatio_sub_two_pos.le
  have h := goldenRatio_sq
  linear_combination (-(goldenRatio ^ 2 + goldenRatio + 2) / 4) * h + (1 / 4 : ℝ) * ht

theorem qstar1_pos : 0 < qstar1 := by
  unfold qstar1
  have h := goldenRatio_sq
  have h1 := one_lt_goldenRatio
  have hs : √(3 * goldenRatio - 2) < goldenRatio ^ 2 := by
    rw [Real.sqrt_lt' (by positivity)]
    nlinarith [goldenRatio_pow_four]
  linarith

theorem qstar1_lt_one : qstar1 < 1 := by
  unfold qstar1
  have h := goldenRatio_sq
  have h1 := one_lt_goldenRatio
  have hs : goldenRatio ^ 2 - 2 < √(3 * goldenRatio - 2) := by
    rw [Real.lt_sqrt (by nlinarith)]
    nlinarith [goldenRatio_pow_four]
  linarith

theorem qstar1_mem_Ioo : qstar1 ∈ Set.Ioo (0 : ℝ) 1 := ⟨qstar1_pos, qstar1_lt_one⟩

end HardyLadder
