module

public import Mathlib

@[expose] public section

/-!
# The real root of `x³ − x − 1`

Elementary facts about a real number `ρ` with `ρ³ = ρ + 1` (the plastic number, the real root of
`x³ − x − 1`): positivity, the bounds `5/4 < ρ < 4/3`, the existence and uniqueness of such a real
number, and the inverse-power identities `ρ⁻¹ = ρ² − 1`, `ρ⁻² = −ρ² + ρ + 1`, `ρ⁻⁵ = 2 − ρ²`, hence
`ρ⁻¹ + ρ⁻⁵ = 1` (the Schmidt weights of the K = 2 optimum sum to one).
-/

namespace HardyLadder

section Plastic

variable {ρ : ℝ}

/-- A real solution of `ρ³ = ρ + 1` is positive. -/
theorem pos_of_cubic (hρ : ρ ^ 3 = ρ + 1) : 0 < ρ := by
  by_contra h
  rw [not_lt] at h
  have h3 : ρ ^ 3 ≤ 0 := by
    nlinarith [mul_nonneg (neg_nonneg.mpr h) (sq_nonneg ρ)]
  have h1 : ρ ≤ -1 := by linarith
  nlinarith [mul_nonneg (neg_nonneg.mpr h)
    (mul_nonneg (by linarith : (0:ℝ) ≤ -ρ - 1) (by linarith : (0:ℝ) ≤ -ρ + 1))]

/-- A real solution of `ρ³ = ρ + 1` exceeds `1`. -/
theorem one_lt_of_cubic (hρ : ρ ^ 3 = ρ + 1) : 1 < ρ := by
  have hpos := pos_of_cubic hρ
  by_contra h
  rw [not_lt] at h
  nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr h),
    mul_nonneg (mul_nonneg hpos.le hpos.le) (sub_nonneg.mpr h)]

/-- `5/4 < ρ`: the cubic is negative at `5/4` and increasing beyond `1`. -/
theorem five_quarters_lt_of_cubic (hρ : ρ ^ 3 = ρ + 1) : 5 / 4 < ρ := by
  have h1 := one_lt_of_cubic hρ
  by_contra h
  rw [not_lt] at h
  -- ρ³ − ρ − 1 = (ρ − 5/4)(ρ² + 5ρ/4 + 9/16) − 19/64 < 0 for ρ ≤ 5/4
  have hq : (0:ℝ) ≤ ρ ^ 2 + 5 / 4 * ρ + 9 / 16 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr h) hq]

/-- `ρ < 4/3`: the cubic is positive at `4/3`. -/
theorem lt_four_thirds_of_cubic (hρ : ρ ^ 3 = ρ + 1) : ρ < 4 / 3 := by
  have h1 := one_lt_of_cubic hρ
  by_contra h
  rw [not_lt] at h
  -- ρ³ − ρ − 1 = (ρ − 4/3)(ρ² + 4ρ/3 + 7/9) + 1/27 > 0 for ρ ≥ 4/3
  have hq : (0:ℝ) ≤ ρ ^ 2 + 4 / 3 * ρ + 7 / 9 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr h) hq]

/-- Two real solutions of `x³ = x + 1` coincide. -/
theorem eq_of_cubic {x y : ℝ} (hx : x ^ 3 = x + 1) (hy : y ^ 3 = y + 1) : x = y := by
  have hx1 := one_lt_of_cubic hx
  have hy1 := one_lt_of_cubic hy
  have h : (x - y) * (x ^ 2 + x * y + y ^ 2 - 1) = 0 := by linear_combination hx - hy
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · nlinarith

/-- `x³ − x − 1` has a real root (by the intermediate value theorem on `[1, 2]`). -/
theorem exists_cubic : ∃ ρ : ℝ, ρ ^ 3 = ρ + 1 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - x - 1) (Set.Icc 1 2) := by fun_prop
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 3 - x - 1) 1) ((fun x : ℝ => x ^ 3 - x - 1) 2) := by
    simp only [Set.mem_Icc]
    norm_num
  obtain ⟨ρ, -, hρ⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hcont h0
  exact ⟨ρ, by simp only at hρ; linarith⟩

/-- **The real root of `x³ − x − 1` is unique.** -/
theorem existsUnique_cubic : ∃! ρ : ℝ, ρ ^ 3 = ρ + 1 := by
  obtain ⟨ρ, hρ⟩ := exists_cubic
  exact ⟨ρ, hρ, fun y hy => eq_of_cubic hy hρ⟩

theorem ne_zero_of_cubic (hρ : ρ ^ 3 = ρ + 1) : ρ ≠ 0 := (pos_of_cubic hρ).ne'

/-- `ρ⁻¹ = ρ² − 1`. -/
theorem inv_eq_of_cubic (hρ : ρ ^ 3 = ρ + 1) : ρ⁻¹ = ρ ^ 2 - 1 := by
  have h0 := ne_zero_of_cubic hρ
  have h : (ρ ^ 2 - 1) * ρ = 1 := by linear_combination hρ
  exact (eq_inv_of_mul_eq_one_left h).symm

/-- `ρ⁻² = −ρ² + ρ + 1`. -/
theorem inv_sq_eq_of_cubic (hρ : ρ ^ 3 = ρ + 1) : ρ⁻¹ ^ 2 = -ρ ^ 2 + ρ + 1 := by
  rw [inv_eq_of_cubic hρ]
  linear_combination ρ * hρ

/-- `ρ⁻⁵ = 2 − ρ²`. -/
theorem inv_pow_five_eq_of_cubic (hρ : ρ ^ 3 = ρ + 1) : ρ⁻¹ ^ 5 = 2 - ρ ^ 2 := by
  rw [inv_eq_of_cubic hρ]
  linear_combination (ρ ^ 7 - 4 * ρ ^ 5 + ρ ^ 4 + 6 * ρ ^ 3 - 3 * ρ ^ 2 - 3 * ρ + 3) * hρ

/-- **The Schmidt weights of the K = 2 optimum sum to one**: `ρ⁻¹ + ρ⁻⁵ = 1` (equivalently
`ρ⁵ = ρ⁴ + 1`). -/
theorem inv_add_inv_pow_five (hρ : ρ ^ 3 = ρ + 1) : ρ⁻¹ + ρ⁻¹ ^ 5 = 1 := by
  rw [inv_pow_five_eq_of_cubic hρ, inv_eq_of_cubic hρ]
  ring

/-- `ρ⁵ = ρ⁴ + 1`. -/
theorem pow_five_eq_of_cubic (hρ : ρ ^ 3 = ρ + 1) : ρ ^ 5 = ρ ^ 4 + 1 := by
  linear_combination (ρ ^ 2 - ρ + 1) * hρ

/-- `ρ⁻² ∈ (0, 1)`. -/
theorem inv_sq_mem_Ioo (hρ : ρ ^ 3 = ρ + 1) : ρ⁻¹ ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := by
  have h1 := one_lt_of_cubic hρ
  have hpos : 0 < ρ⁻¹ := inv_pos.mpr (by linarith)
  have hlt : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  exact ⟨by positivity, by nlinarith⟩

end Plastic

end HardyLadder
