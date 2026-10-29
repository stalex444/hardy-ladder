module

public import Mathlib
public import HardyLadder.Golden
public import HardyLadder.Ladder

@[expose] public section

/-!
# K = 1: Hardy's value `φ⁻⁵ = (5√5 − 11)/2`

`P₁*(q) = q² (1 − q²)² / ((1 + q²)(1 + q³)²)`. In `s = q + q⁻¹` (which runs over `(2, ∞)` as `q`
runs over `(0, 1)`), `P₁* = (s − 2) / (s (s − 1)²)`, and
`s (s − 1)² − φ⁵ (s − 2) = (s − φ²)² (s + 2φ) ≥ 0`, so the supremum is `φ⁻⁵`, attained exactly at
`s = φ²`, i.e. at the unique root `q* = (φ² − √(3φ − 2))/2` of `q² − φ² q + 1` in `(0, 1)` — the
root in `(0, 1)` of the quartic `q⁴ − 3q³ + 3q² − 3q + 1 = (q² − φ² q + 1)(q² − φ⁻² q + 1)`.
Hardy (PRL 71, 1665, 1993, p. 1667) gives the maximiser as `2|αβ| = 3 − √5`, which is the
condition `q² − φ² q + 1 = 0`; the quartic is the `K = 1` factor of Cereceda's polynomial
`m₁(x) = (x + 1)³ (x⁴ − 3x³ + 3x² − 3x + 1)` (J. Phys. A 35, 9105, 2002, eq. (20)).
-/

namespace HardyLadder

open Real

/-- For `q > 0`, `s = q + q⁻¹ ≥ 2`. -/
theorem two_le_add_inv {q : ℝ} (hq0 : 0 < q) : 2 ≤ q + q⁻¹ := by
  have hq : q ≠ 0 := hq0.ne'
  have h : q + q⁻¹ - 2 = (q - 1) ^ 2 / q := by field_simp; ring
  have : 0 ≤ (q - 1) ^ 2 / q := by positivity
  linarith

/-- For `q ∈ (0, 1)`, `s = q + q⁻¹ > 2`. -/
theorem two_lt_add_inv {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : 2 < q + q⁻¹ := by
  have hq : q ≠ 0 := hq0.ne'
  have h : q + q⁻¹ - 2 = (q - 1) ^ 2 / q := by field_simp; ring
  have hne : q - 1 ≠ 0 := by linarith
  have hsq : 0 < (q - 1) ^ 2 := by positivity
  have : 0 < (q - 1) ^ 2 / q := div_pos hsq hq0
  linarith

/-- `P₁*(q)` in terms of `s = q + q⁻¹`. -/
theorem ladderValue_one_eq {q : ℝ} (hq : 0 < q) :
    ladderValue 1 q = (q + q⁻¹ - 2) / ((q + q⁻¹) * (q + q⁻¹ - 1) ^ 2) := by
  unfold ladderValue
  have hq0 : q ≠ 0 := hq.ne'
  have hs := two_le_add_inv hq
  have h1 : q + q⁻¹ ≠ 0 := by positivity
  have h2 : q + q⁻¹ - 1 ≠ 0 := by linarith
  have h3 : 1 + q ^ 2 ≠ 0 := by positivity
  have h4 : 1 + q ^ 3 ≠ 0 := by positivity
  simp only [show (2 * 1 : ℕ) = 2 from rfl, show (2 * 1 + 1 : ℕ) = 3 from rfl]
  have hden1 : (1 + q ^ 2) * (1 + q ^ 3) ^ 2 ≠ 0 := mul_ne_zero h3 (pow_ne_zero 2 h4)
  have hden2 : (q + q⁻¹) * (q + q⁻¹ - 1) ^ 2 ≠ 0 := mul_ne_zero h1 (pow_ne_zero 2 h2)
  rw [div_eq_div_iff hden1 hden2]
  field_simp
  ring

/-- The one-variable bound: for `s > 2`, `(s − 2) / (s (s − 1)²) ≤ φ⁻⁵`. -/
theorem F1_le {s : ℝ} (hs : 2 < s) : (s - 2) / (s * (s - 1) ^ 2) ≤ goldenRatio⁻¹ ^ 5 := by
  have hφ := goldenRatio_pos
  have h := goldenRatio_sq
  have hs1 : 0 < s - 1 := by linarith
  have hd : 0 < s * (s - 1) ^ 2 := by positivity
  rw [inv_pow, ← one_div, div_le_div_iff₀ hd (by positivity)]
  have key : s * (s - 1) ^ 2 - goldenRatio ^ 5 * (s - 2) =
      (s - goldenRatio ^ 2) ^ 2 * (s + 2 * goldenRatio) := by
    linear_combination (s * (-goldenRatio ^ 3 - 2 * goldenRatio ^ 2 + goldenRatio + 2 * s - 1)) * h
  have hpos : 0 ≤ (s - goldenRatio ^ 2) ^ 2 * (s + 2 * goldenRatio) := by positivity
  nlinarith

/-- Equality at `s = φ²`. -/
theorem F1_value : (goldenRatio ^ 2 - 2) / (goldenRatio ^ 2 * (goldenRatio ^ 2 - 1) ^ 2) =
    goldenRatio⁻¹ ^ 5 := by
  have hφ := goldenRatio_pos
  have h1 := one_lt_goldenRatio
  have h := goldenRatio_sq
  have h2 : 0 < goldenRatio ^ 2 - 1 := by nlinarith
  have hd : goldenRatio ^ 2 * (goldenRatio ^ 2 - 1) ^ 2 ≠ 0 := by positivity
  rw [inv_pow, ← one_div, div_eq_div_iff hd (by positivity)]
  linear_combination (goldenRatio ^ 2 * (goldenRatio ^ 3 - goldenRatio + 1)) * h

/-- Equality forces `s = φ²`. -/
theorem F1_eq_iff {s : ℝ} (hs : 2 < s) :
    (s - 2) / (s * (s - 1) ^ 2) = goldenRatio⁻¹ ^ 5 ↔ s = goldenRatio ^ 2 := by
  have hφ := goldenRatio_pos
  have h := goldenRatio_sq
  have hs1 : 0 < s - 1 := by linarith
  have hd : s * (s - 1) ^ 2 ≠ 0 := by positivity
  rw [inv_pow, ← one_div, div_eq_div_iff hd (by positivity)]
  have key : s * (s - 1) ^ 2 - goldenRatio ^ 5 * (s - 2) =
      (s - goldenRatio ^ 2) ^ 2 * (s + 2 * goldenRatio) := by
    linear_combination (s * (-goldenRatio ^ 3 - 2 * goldenRatio ^ 2 + goldenRatio + 2 * s - 1)) * h
  constructor
  · intro heq
    have h0 : (s - goldenRatio ^ 2) ^ 2 * (s + 2 * goldenRatio) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h0)
    · linarith
  · rintro rfl
    linear_combination (goldenRatio ^ 2 * (goldenRatio ^ 3 - goldenRatio + 1)) * h

/-- `q* + q*⁻¹ = φ²`. -/
theorem qstar1_add_inv : qstar1 + qstar1⁻¹ = goldenRatio ^ 2 := by
  have h0 := qstar1_pos.ne'
  have h := qstar1_root
  have h' : (goldenRatio ^ 2 - qstar1) * qstar1 = 1 := by linear_combination -h
  rw [(eq_inv_of_mul_eq_one_left h').symm]
  ring

/-- **Hardy's K = 1 optimum.** The supremum of `P₁*(q) = q² (1 − q²)² / ((1 + q²)(1 + q³)²)` over
`q ∈ (0, 1)` is `φ⁻⁵ = (5√5 − 11)/2`, and it is attained. -/
theorem hardy_K1_isGreatest :
    IsGreatest ((fun q : ℝ => ladderValue 1 q) '' Set.Ioo 0 1) (goldenRatio⁻¹ ^ 5) := by
  constructor
  · refine ⟨qstar1, qstar1_mem_Ioo, ?_⟩
    simp only
    rw [ladderValue_one_eq qstar1_pos, qstar1_add_inv]
    exact F1_value
  · rintro _ ⟨q, ⟨hq0, hq1⟩, rfl⟩
    simp only
    rw [ladderValue_one_eq hq0]
    exact F1_le (two_lt_add_inv hq0 hq1)

/-- The maximisers of `P₁*` on `(0, 1)` are the roots of `q² − φ² q + 1`. -/
theorem hardy_K1_eq_iff {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ladderValue 1 q = goldenRatio⁻¹ ^ 5 ↔ q ^ 2 - goldenRatio ^ 2 * q + 1 = 0 := by
  rw [ladderValue_one_eq hq0, F1_eq_iff (two_lt_add_inv hq0 hq1)]
  have h0 := hq0.ne'
  constructor
  · intro h
    have hinv : q⁻¹ = goldenRatio ^ 2 - q := by linarith
    have hmul : q * q⁻¹ = 1 := mul_inv_cancel₀ h0
    rw [hinv] at hmul
    linear_combination -hmul
  · intro h
    have h' : (goldenRatio ^ 2 - q) * q = 1 := by linear_combination -h
    rw [(eq_inv_of_mul_eq_one_left h').symm]
    ring

/-- The `K = 1` quartic factors over `ℚ(φ)`:
`q⁴ − 3q³ + 3q² − 3q + 1 = (q² − φ² q + 1)(q² − φ⁻² q + 1)` with `φ⁻² = 2 − φ`. -/
theorem quartic_factor (q : ℝ) :
    q ^ 4 - 3 * q ^ 3 + 3 * q ^ 2 - 3 * q + 1 =
      (q ^ 2 - goldenRatio ^ 2 * q + 1) * (q ^ 2 - (2 - goldenRatio) * q + 1) := by
  have h := goldenRatio_sq
  linear_combination (q ^ 3 + (goldenRatio - 1) * q ^ 2 + q) * h

/-- The second factor is positive for every real `q`. -/
theorem second_factor_pos (q : ℝ) : 0 < q ^ 2 - (2 - goldenRatio) * q + 1 := by
  have h1 := one_lt_goldenRatio
  have h2 : goldenRatio < 2 := goldenRatio_lt_two
  have h3 : 0 < (2 - goldenRatio) * (goldenRatio - 1) := mul_pos (by linarith) (by linarith)
  nlinarith [sq_nonneg (q - (2 - goldenRatio) / 2)]

/-- **The maximiser of `P₁*` on `(0, 1)` is the root of the quartic** `q⁴ − 3q³ + 3q² − 3q + 1`
there. -/
theorem hardy_K1_eq_iff_quartic {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ladderValue 1 q = goldenRatio⁻¹ ^ 5 ↔ q ^ 4 - 3 * q ^ 3 + 3 * q ^ 2 - 3 * q + 1 = 0 := by
  rw [hardy_K1_eq_iff hq0 hq1, quartic_factor]
  constructor
  · intro h; rw [h, zero_mul]
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h (second_factor_pos q).ne'

/-- **The maximiser is unique.** -/
theorem hardy_K1_existsUnique :
    ∃! q : ℝ, q ∈ Set.Ioo (0 : ℝ) 1 ∧ ladderValue 1 q = goldenRatio⁻¹ ^ 5 := by
  refine ⟨qstar1, ⟨qstar1_mem_Ioo, ?_⟩, ?_⟩
  · exact (hardy_K1_eq_iff qstar1_pos qstar1_lt_one).mpr qstar1_root
  · rintro q ⟨⟨hq0, hq1⟩, hq⟩
    have h := (hardy_K1_eq_iff hq0 hq1).mp hq
    have h' := qstar1_root
    have hq1' := qstar1_lt_one
    have hφ : 2 < goldenRatio ^ 2 := by nlinarith [goldenRatio_sq, one_lt_goldenRatio]
    have : (q - qstar1) * (q + qstar1 - goldenRatio ^ 2) = 0 := by linear_combination h - h'
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · linarith

end HardyLadder
