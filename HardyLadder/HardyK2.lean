module

public import Mathlib
public import HardyLadder.Plastic
public import HardyLadder.Ladder
public import HardyLadder.HardyK1

@[expose] public section

/-!
# K = 2: the optimum `(8ρ² + ρ − 11)/25` in `ℚ(ρ)`

`P₂*(q) = q² (1 − q⁴)² / ((1 + q²)(1 + q⁵)²)`. In `s = q + q⁻¹ ∈ (2, ∞)`,
`P₂* = s (s − 2) / (s² − s − 1)²`, and for `ρ³ = ρ + 1`, `v = (8ρ² + ρ − 11)/25`,

  `v (s² − s − 1)² − s (s − 2) = (s − ρ − 1)² (v s² + B s + C)`,
  `B = (2ρ² − 6ρ + 16)/25`, `C = (−23ρ² + 19ρ + 16)/25`,

with `v, B, C > 0` (from `5/4 < ρ < 4/3`), so the supremum over `(0, 1)` is `v`, attained exactly
at `s = ρ + 1 = ρ³`, i.e. at `q* = ρ⁻²` (the other root `ρ²` of `q² − (ρ + 1) q + 1` is `> 1`).
The stationarity cofactor `q³ − q² + 2q − 1 = (q − ρ⁻²)(q² + (ρ⁻² − 1) q + ρ²)` has `q* = ρ⁻²`
as its only real root, and the Schmidt weights at the maximiser are `c₀² = ρ⁻¹`, `c₁² = ρ⁻⁵`.
The optimum over every real Schmidt state (`c₁ ≷ c₀`), with its attainment and its optimal states,
is in `HardyLadder/Optimum.lean`.
-/

namespace HardyLadder

section K2

variable {ρ : ℝ}

/-- `P₂*(q)` in terms of `s = q + q⁻¹`. -/
theorem ladderValue_two_eq {q : ℝ} (hq : 0 < q) :
    ladderValue 2 q =
      (q + q⁻¹) * (q + q⁻¹ - 2) / ((q + q⁻¹) ^ 2 - (q + q⁻¹) - 1) ^ 2 := by
  unfold ladderValue
  have hq0 : q ≠ 0 := hq.ne'
  have hs : 2 ≤ q + q⁻¹ := by
    have h : q + q⁻¹ - 2 = (q - 1) ^ 2 / q := by field_simp; ring
    have : 0 ≤ (q - 1) ^ 2 / q := by positivity
    linarith
  have h1 : q + q⁻¹ ≠ 0 := by positivity
  have h2 : (q + q⁻¹) ^ 2 - (q + q⁻¹) - 1 ≠ 0 := by nlinarith
  have h3 : 1 + q ^ 2 ≠ 0 := by positivity
  have h4 : 1 + q ^ 5 ≠ 0 := by positivity
  simp only [show (2 * 2 : ℕ) = 4 from rfl, show (2 * 2 + 1 : ℕ) = 5 from rfl]
  have hden1 : (1 + q ^ 2) * (1 + q ^ 5) ^ 2 ≠ 0 := mul_ne_zero h3 (pow_ne_zero 2 h4)
  have hden2 : ((q + q⁻¹) ^ 2 - (q + q⁻¹) - 1) ^ 2 ≠ 0 := pow_ne_zero 2 h2
  rw [div_eq_div_iff hden1 hden2]
  field_simp
  ring

/-- The value `v = (8ρ² + ρ − 11)/25` is positive. -/
theorem value_pos (hρ : ρ ^ 3 = ρ + 1) : 0 < (8 * ρ ^ 2 + ρ - 11) / 25 := by
  have h := five_quarters_lt_of_cubic hρ
  have : 0 < 8 * ρ ^ 2 + ρ - 11 := by nlinarith [mul_pos (sub_pos.mpr h) (by linarith : (0:ℝ) < 8 * ρ + 11)]
  positivity

theorem coeffB_pos (ρ : ℝ) : 0 < (2 * ρ ^ 2 - 6 * ρ + 16) / 25 := by
  have : 0 < 2 * ρ ^ 2 - 6 * ρ + 16 := by nlinarith [sq_nonneg (ρ - 3 / 2)]
  positivity

theorem coeffC_pos (hρ : ρ ^ 3 = ρ + 1) : 0 < (-23 * ρ ^ 2 + 19 * ρ + 16) / 25 := by
  have h := lt_four_thirds_of_cubic hρ
  have h0 := pos_of_cubic hρ
  have : 0 < -23 * ρ ^ 2 + 19 * ρ + 16 := by
    nlinarith [mul_pos (sub_pos.mpr h) (by linarith : (0:ℝ) < 23 * ρ + 35 / 3)]
  positivity

/-- The factorisation
`v (s² − s − 1)² − s (s − 2) = (s − ρ − 1)² (v s² + B s + C)` modulo `ρ³ = ρ + 1`. -/
theorem G_factor (hρ : ρ ^ 3 = ρ + 1) (s : ℝ) :
    (8 * ρ ^ 2 + ρ - 11) / 25 * (s ^ 2 - s - 1) ^ 2 - s * (s - 2) =
      (s - ρ - 1) ^ 2 * ((8 * ρ ^ 2 + ρ - 11) / 25 * s ^ 2 + (2 * ρ ^ 2 - 6 * ρ + 16) / 25 * s +
        (-23 * ρ ^ 2 + 19 * ρ + 16) / 25) := by
  linear_combination (-8 * ρ * s ^ 2 / 25 - 2 * ρ * s / 25 + 23 * ρ / 25 + 16 * s ^ 3 / 25 -
    13 * s ^ 2 / 25 - 44 * s / 25 + 27 / 25) * hρ

/-- The one-variable bound: for `s > 2`, `s (s − 2) / (s² − s − 1)² ≤ v`. -/
theorem F2_le (hρ : ρ ^ 3 = ρ + 1) {s : ℝ} (hs : 2 < s) :
    s * (s - 2) / (s ^ 2 - s - 1) ^ 2 ≤ (8 * ρ ^ 2 + ρ - 11) / 25 := by
  have hd : 0 < (s ^ 2 - s - 1) ^ 2 := by
    have : 0 < s ^ 2 - s - 1 := by nlinarith
    positivity
  rw [div_le_iff₀ hd]
  have hG := G_factor hρ s
  have hv := value_pos hρ
  have hB := coeffB_pos ρ
  have hC := coeffC_pos hρ
  have hs0 : 0 < s := by linarith
  have hQ : 0 < (8 * ρ ^ 2 + ρ - 11) / 25 * s ^ 2 + (2 * ρ ^ 2 - 6 * ρ + 16) / 25 * s +
      (-23 * ρ ^ 2 + 19 * ρ + 16) / 25 := by positivity
  have hpos : 0 ≤ (s - ρ - 1) ^ 2 * ((8 * ρ ^ 2 + ρ - 11) / 25 * s ^ 2 +
      (2 * ρ ^ 2 - 6 * ρ + 16) / 25 * s + (-23 * ρ ^ 2 + 19 * ρ + 16) / 25) := by positivity
  linarith

/-- Equality in the one-variable bound holds exactly at `s = ρ + 1`. -/
theorem F2_eq_iff (hρ : ρ ^ 3 = ρ + 1) {s : ℝ} (hs : 2 < s) :
    s * (s - 2) / (s ^ 2 - s - 1) ^ 2 = (8 * ρ ^ 2 + ρ - 11) / 25 ↔ s = ρ + 1 := by
  have hd : 0 < (s ^ 2 - s - 1) ^ 2 := by
    have : 0 < s ^ 2 - s - 1 := by nlinarith
    positivity
  rw [div_eq_iff hd.ne']
  have hG := G_factor hρ s
  have hv := value_pos hρ
  have hB := coeffB_pos ρ
  have hC := coeffC_pos hρ
  have hs0 : 0 < s := by linarith
  have hQ : 0 < (8 * ρ ^ 2 + ρ - 11) / 25 * s ^ 2 + (2 * ρ ^ 2 - 6 * ρ + 16) / 25 * s +
      (-23 * ρ ^ 2 + 19 * ρ + 16) / 25 := by positivity
  constructor
  · intro h
    have h0 : (s - ρ - 1) ^ 2 * ((8 * ρ ^ 2 + ρ - 11) / 25 * s ^ 2 +
        (2 * ρ ^ 2 - 6 * ρ + 16) / 25 * s + (-23 * ρ ^ 2 + 19 * ρ + 16) / 25) = 0 := by
      linarith
    rcases mul_eq_zero.mp h0 with h0 | h0
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
      linarith
    · exact absurd h0 hQ.ne'
  · rintro rfl
    linear_combination (-8 * ρ ^ 3 / 25 - 17 * ρ ^ 2 / 25 + 9 * ρ / 25 + 14 / 25) * hρ

/-- `ρ⁻² + (ρ⁻²)⁻¹ = ρ + 1`. -/
theorem inv_sq_add_inv (hρ : ρ ^ 3 = ρ + 1) : ρ⁻¹ ^ 2 + (ρ⁻¹ ^ 2)⁻¹ = ρ + 1 := by
  rw [show (ρ⁻¹ ^ 2)⁻¹ = ρ ^ 2 by rw [inv_pow, inv_inv], inv_sq_eq_of_cubic hρ]
  ring

/-- **The K = 2 optimum.** For `ρ` the real root of `x³ − x − 1`, the supremum of
`P₂*(q) = q² (1 − q⁴)² / ((1 + q²)(1 + q⁵)²)` over `q ∈ (0, 1)` is `(8ρ² + ρ − 11)/25`, and it is
attained. -/
theorem hardy_K2_isGreatest (hρ : ρ ^ 3 = ρ + 1) :
    IsGreatest ((fun q : ℝ => ladderValue 2 q) '' Set.Ioo 0 1) ((8 * ρ ^ 2 + ρ - 11) / 25) := by
  constructor
  · refine ⟨ρ⁻¹ ^ 2, inv_sq_mem_Ioo hρ, ?_⟩
    simp only
    rw [ladderValue_two_eq (inv_sq_mem_Ioo hρ).1, inv_sq_add_inv hρ]
    exact (F2_eq_iff hρ (by linarith [one_lt_of_cubic hρ])).mpr rfl
  · rintro _ ⟨q, ⟨hq0, hq1⟩, rfl⟩
    simp only
    rw [ladderValue_two_eq hq0]
    exact F2_le hρ (two_lt_add_inv hq0 hq1)

/-- The maximisers of `P₂*` on `(0, 1)` are the roots of `q² − (ρ + 1) q + 1`. -/
theorem hardy_K2_eq_iff (hρ : ρ ^ 3 = ρ + 1) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ladderValue 2 q = (8 * ρ ^ 2 + ρ - 11) / 25 ↔ q ^ 2 - (ρ + 1) * q + 1 = 0 := by
  rw [ladderValue_two_eq hq0, F2_eq_iff hρ (two_lt_add_inv hq0 hq1)]
  have h0 := hq0.ne'
  constructor
  · intro h
    have hinv : q⁻¹ = ρ + 1 - q := by linarith
    have hmul : q * q⁻¹ = 1 := mul_inv_cancel₀ h0
    rw [hinv] at hmul
    linear_combination -hmul
  · intro h
    have h' : (ρ + 1 - q) * q = 1 := by linear_combination -h
    rw [(eq_inv_of_mul_eq_one_left h').symm]
    ring

/-- `q² − (ρ + 1) q + 1 = (q − ρ⁻²)(q − ρ²)`. -/
theorem quadratic_factor (hρ : ρ ^ 3 = ρ + 1) (q : ℝ) :
    q ^ 2 - (ρ + 1) * q + 1 = (q - ρ⁻¹ ^ 2) * (q - ρ ^ 2) := by
  rw [inv_sq_eq_of_cubic hρ]
  linear_combination (ρ - 1) * hρ

/-- **The maximiser of `P₂*` on `(0, 1)` is `q* = ρ⁻²`** (Schmidt ratio `c₁/c₀ = ρ⁻²`). -/
theorem hardy_K2_eq_iff_inv_sq (hρ : ρ ^ 3 = ρ + 1) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ladderValue 2 q = (8 * ρ ^ 2 + ρ - 11) / 25 ↔ q = ρ⁻¹ ^ 2 := by
  rw [hardy_K2_eq_iff hρ hq0 hq1, quadratic_factor hρ]
  have h1 := one_lt_of_cubic hρ
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact sub_eq_zero.mp h
    · have : 1 < ρ ^ 2 := by nlinarith
      linarith [sub_eq_zero.mp h]
  · rintro rfl
    simp

/-- **The maximiser is unique.** -/
theorem hardy_K2_existsUnique (hρ : ρ ^ 3 = ρ + 1) :
    ∃! q : ℝ, q ∈ Set.Ioo (0 : ℝ) 1 ∧ ladderValue 2 q = (8 * ρ ^ 2 + ρ - 11) / 25 := by
  refine ⟨ρ⁻¹ ^ 2, ⟨inv_sq_mem_Ioo hρ, ?_⟩, ?_⟩
  · exact (hardy_K2_eq_iff_inv_sq hρ (inv_sq_mem_Ioo hρ).1 (inv_sq_mem_Ioo hρ).2).mpr rfl
  · rintro q ⟨⟨hq0, hq1⟩, hq⟩
    exact (hardy_K2_eq_iff_inv_sq hρ hq0 hq1).mp hq

/-- **The stationarity cofactor.** `q³ − q² + 2q − 1 = (q − ρ⁻²)(q² + (ρ⁻² − 1) q + ρ²)`. -/
theorem cubic_cofactor_factor (hρ : ρ ^ 3 = ρ + 1) (q : ℝ) :
    q ^ 3 - q ^ 2 + 2 * q - 1 = (q - ρ⁻¹ ^ 2) * (q ^ 2 + (ρ⁻¹ ^ 2 - 1) * q + ρ ^ 2) := by
  rw [inv_sq_eq_of_cubic hρ]
  linear_combination (q * ρ - 2 * q - ρ + 1) * hρ

/-- The quadratic factor of the cofactor has no real root. -/
theorem cofactor_quadratic_pos (hρ : ρ ^ 3 = ρ + 1) (q : ℝ) :
    0 < q ^ 2 + (ρ⁻¹ ^ 2 - 1) * q + ρ ^ 2 := by
  rw [inv_sq_eq_of_cubic hρ]
  have h1 := one_lt_of_cubic hρ
  have h2 := lt_four_thirds_of_cubic hρ
  have h3 : (ρ - 1) ^ 2 < 1 := by nlinarith
  have h4 : 0 < ρ ^ 2 * (4 - (ρ - 1) ^ 2) := mul_pos (by positivity) (by linarith)
  nlinarith [sq_nonneg (q + (ρ - ρ ^ 2) / 2)]

/-- **The maximiser is the root in `(0, 1)` of the stationarity cofactor** `q³ − q² + 2q − 1`. -/
theorem hardy_K2_eq_iff_cubic (hρ : ρ ^ 3 = ρ + 1) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ladderValue 2 q = (8 * ρ ^ 2 + ρ - 11) / 25 ↔ q ^ 3 - q ^ 2 + 2 * q - 1 = 0 := by
  rw [hardy_K2_eq_iff_inv_sq hρ hq0 hq1, cubic_cofactor_factor hρ]
  constructor
  · rintro rfl; simp
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (cofactor_quadratic_pos hρ q).ne'

/-- **The optimal Schmidt weights**: `c₀² = ρ⁻¹`, `c₁² = ρ⁻⁵` sum to one, and their ratio
`c₁²/c₀² = ρ⁻⁴ = (ρ⁻²)²`. -/
theorem schmidt_weights (hρ : ρ ^ 3 = ρ + 1) :
    ρ⁻¹ + ρ⁻¹ ^ 5 = 1 ∧ ρ⁻¹ ^ 5 / ρ⁻¹ = (ρ⁻¹ ^ 2) ^ 2 := by
  refine ⟨inv_add_inv_pow_five hρ, ?_⟩
  have h0 : ρ⁻¹ ≠ 0 := inv_ne_zero (ne_zero_of_cubic hρ)
  rw [show ρ⁻¹ ^ 5 = (ρ⁻¹ ^ 2) ^ 2 * ρ⁻¹ by ring, mul_div_cancel_right₀ _ h0]

end K2

end HardyLadder
