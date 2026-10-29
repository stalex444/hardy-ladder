module

public import Mathlib
public import HardyLadder.Plastic
public import HardyLadder.Golden
public import HardyLadder.Ladder
public import HardyLadder.HardyK1
public import HardyLadder.HardyK2

@[expose] public section

/-!
# The `K = 1` and `K = 2` optima over every real Schmidt state (library proofs of compared
statements 16–18 and 24–26)

The compared statements 12 and 20 bound `P₁*` and `P₂*` on `q ∈ (0, 1)`, i.e. for Schmidt states
with `c₁ < c₀`. The closed form is symmetric under `q ↦ 1/q` (`ladderValue_inv`; the symmetry
`P_K(α, β) = P_K(β, α)` noted by Cereceda, J. Phys. A 35, 9105, 2002, below Table 1), and
`P_K*(1) = 0` (`ladderValue_at_one`), so the bounds on `(0, 1)` hold for every `q > 0`
(`ladderValue_one_le`, `ladderValue_two_le`). Composed with the closed-form bound
`ladder_prob_le` and its attainment `ladder_prob_attained`, this gives the optimum of the `K`-step
ladder over every two-qubit state in Schmidt form `c₀|00⟩ + c₁|11⟩` (`c₀, c₁ > 0`,
`c₀² + c₁² = 1`) and every choice of real settings:

* `K = 1`: `ladder_K1_le` (the bound `φ⁻⁵`), `ladder_K1_attained` (attained, at a state with
  `2c₀c₁ = 3 − √5`, Hardy's condition `2|αβ| = 3 − √5`), and `ladder_K1_hardy_condition_of_eq`
  (every configuration attaining `φ⁻⁵` has `2c₀c₁ = 3 − √5`);
* `K = 2`: `ladder_K2_le` (the bound `(8ρ² + ρ − 11)/25`), `ladder_K2_attained` (attained, at
  Schmidt weights `c₀² = ρ⁻¹`, `c₁² = ρ⁻⁵`), and `ladder_K2_weights_of_eq` (every configuration
  attaining it has Schmidt weights `{c₀², c₁²} = {ρ⁻¹, ρ⁻⁵}`).

As in the other compared statements, the probabilities are the squared real amplitudes written out
in `Challenge.lean`; the reduction of complex settings and of general two-qubit pure states to this
real Schmidt case is not formalised. The six theorems `ladder_K1_le`, `ladder_K1_attained`,
`ladder_K1_hardy_condition_of_eq`, `ladder_K2_le`, `ladder_K2_attained` and
`ladder_K2_weights_of_eq` prove compared statements 16–18 and 24–26 (`HardyLadder.Entry.*` in
`Solution.lean`), whose statement text in `Challenge.lean` is identical to theirs; the other six
theorems of this file are uncompared library lemmas. The same composition for every `K ≥ 1`, at
the zero of Cereceda's `m_K` in `(0, 1)`, is in `HardyLadder/Maximiser.lean` (compared statements
9–11).
-/

namespace HardyLadder

open Real

/-! ### The symmetry of the closed form -/

/-- **The symmetry `P_K*(1/q) = P_K*(q)`** for every `K` and `q > 0`. -/
theorem ladderValue_inv (K : ℕ) {q : ℝ} (hq : 0 < q) :
    ladderValue K q⁻¹ = ladderValue K q := by
  unfold ladderValue
  have hq0 : q ≠ 0 := hq.ne'
  have h1 : (1 + q ^ 2) ≠ 0 := by positivity
  have h2 : (1 + q ^ (2 * K + 1)) ≠ 0 := by positivity
  have h3 : (q ^ (2 * K + 1) + 1) ≠ 0 := by positivity
  have h4 : (q ^ 2 + 1) ≠ 0 := by positivity
  rw [inv_pow, inv_pow, inv_pow]
  rw [div_eq_div_iff (by
      refine mul_ne_zero ?_ (pow_ne_zero 2 ?_)
      · rw [show (1 : ℝ) + (q ^ 2)⁻¹ = (q ^ 2 + 1) / q ^ 2 by field_simp]
        exact div_ne_zero h4 (pow_ne_zero 2 hq0)
      · rw [show (1 : ℝ) + (q ^ (2 * K + 1))⁻¹ = (q ^ (2 * K + 1) + 1) / q ^ (2 * K + 1) by
          field_simp]
        exact div_ne_zero h3 (pow_ne_zero _ hq0))
    (mul_ne_zero h1 (pow_ne_zero 2 h2))]
  field_simp
  ring

/-- `P_K*(1) = 0`: the maximally entangled state gives nothing. -/
theorem ladderValue_at_one (K : ℕ) : ladderValue K 1 = 0 := by
  unfold ladderValue
  simp

/-- `P₁*(q) ≤ φ⁻⁵` for every `q > 0`, not only on `(0, 1)`. -/
theorem ladderValue_one_le {q : ℝ} (hq : 0 < q) : ladderValue 1 q ≤ goldenRatio⁻¹ ^ 5 := by
  rcases lt_trichotomy q 1 with h1 | h1 | h1
  · exact hardy_K1_isGreatest.2 ⟨q, ⟨hq, h1⟩, rfl⟩
  · rw [h1, ladderValue_at_one]
    exact pow_nonneg (inv_nonneg.mpr goldenRatio_pos.le) 5
  · rw [← ladderValue_inv 1 hq]
    exact hardy_K1_isGreatest.2 ⟨q⁻¹, ⟨inv_pos.mpr hq, inv_lt_one_of_one_lt₀ h1⟩, rfl⟩

/-- `P₂*(q) ≤ (8ρ² + ρ − 11)/25` for every `q > 0`, not only on `(0, 1)`. -/
theorem ladderValue_two_le {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) {q : ℝ} (hq : 0 < q) :
    ladderValue 2 q ≤ (8 * ρ ^ 2 + ρ - 11) / 25 := by
  rcases lt_trichotomy q 1 with h1 | h1 | h1
  · exact (hardy_K2_isGreatest hρ).2 ⟨q, ⟨hq, h1⟩, rfl⟩
  · rw [h1, ladderValue_at_one]
    exact (value_pos hρ).le
  · rw [← ladderValue_inv 2 hq]
    exact (hardy_K2_isGreatest hρ).2 ⟨q⁻¹, ⟨inv_pos.mpr hq, inv_lt_one_of_one_lt₀ h1⟩, rfl⟩

/-! ### Two algebraic steps -/

/-- Hardy's condition: if `x > 0`, `x² + y² = 1` and `q = y/x` is a root of `q² − φ² q + 1`, then
`2xy = 3 − √5`. -/
theorem two_mul_eq_of_ratio {x y : ℝ} (hx : 0 < x) (hn : x ^ 2 + y ^ 2 = 1)
    (h : (y / x) ^ 2 - goldenRatio ^ 2 * (y / x) + 1 = 0) : 2 * x * y = 3 - √5 := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ, y / x = q := ⟨_, rfl⟩
  rw [hq] at h
  have hy : y = q * x := by rw [← hq, div_mul_cancel₀ y hx.ne']
  rw [hy] at hn ⊢
  have hφ2 : goldenRatio ^ 2 = (3 + √5) / 2 := by
    rw [goldenRatio_sq, goldenRatio]
    ring
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h1 : 1 + q ^ 2 = (3 + √5) / 2 * q := by linear_combination h + q * hφ2
  linear_combination (3 - √5) * hn - (3 - √5) * x ^ 2 * h1 + x ^ 2 * q / 2 * h5

/-- The Schmidt weights from the ratio: if `x > 0`, `x² + y² = 1`, `y/x = t²` and `t + t⁵ = 1`,
then `x² = t` and `y² = t⁵`. -/
theorem weights_of_ratio {t x y : ℝ} (ht : t + t ^ 5 = 1) (hx : 0 < x)
    (hn : x ^ 2 + y ^ 2 = 1) (h : y / x = t ^ 2) : x ^ 2 = t ∧ y ^ 2 = t ^ 5 := by
  have hy : y = t ^ 2 * x := (div_eq_iff hx.ne').mp h
  have hpos : (1 + t ^ 4) ≠ 0 := by positivity
  have h1 : x ^ 2 * (1 + t ^ 4) = t * (1 + t ^ 4) := by
    rw [hy] at hn
    linear_combination hn - ht
  have hx2 : x ^ 2 = t := mul_right_cancel₀ hpos h1
  refine ⟨hx2, ?_⟩
  rw [hy, mul_pow, hx2]
  ring

/-! ### `K = 1`: the optimum over every real Schmidt state -/

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
    (c₀ * cos (a 1) * cos (b 1) + c₁ * sin (a 1) * sin (b 1)) ^ 2 ≤ goldenRatio⁻¹ ^ 5 :=
  (ladder_prob_le 1 hc₀ hc₁ hnorm a b h₀ hA hB).trans (ladderValue_one_le (div_pos hc₁ hc₀))

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
  have hq0 := qstar1_pos
  have hs : 0 < √(1 + qstar1 ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : √(1 + qstar1 ^ 2) ^ 2 = 1 + qstar1 ^ 2 := Real.sq_sqrt (by positivity)
  have hc₀ : 0 < (√(1 + qstar1 ^ 2))⁻¹ := inv_pos.mpr hs
  have hc₁ : 0 < qstar1 * (√(1 + qstar1 ^ 2))⁻¹ := mul_pos hq0 hc₀
  have hn : ((√(1 + qstar1 ^ 2))⁻¹) ^ 2 + (qstar1 * (√(1 + qstar1 ^ 2))⁻¹) ^ 2 = 1 := by
    have : ((√(1 + qstar1 ^ 2))⁻¹) ^ 2 + (qstar1 * (√(1 + qstar1 ^ 2))⁻¹) ^ 2 =
        (1 + qstar1 ^ 2) / √(1 + qstar1 ^ 2) ^ 2 := by ring
    rw [this, hs2, div_self (show (1 + qstar1 ^ 2 : ℝ) ≠ 0 by positivity)]
  have hr : qstar1 * (√(1 + qstar1 ^ 2))⁻¹ / (√(1 + qstar1 ^ 2))⁻¹ = qstar1 :=
    mul_div_cancel_right₀ qstar1 hc₀.ne'
  refine ⟨_, _, hc₀, hc₁, hn, two_mul_eq_of_ratio hc₀ hn (by rw [hr]; exact qstar1_root), ?_⟩
  obtain ⟨a, b, h₀, hA, hB, hv⟩ := ladder_prob_attained 1 hc₀ hc₁ hn
  refine ⟨a, b, h₀, hA, hB, ?_⟩
  rw [hv, hr]
  exact (hardy_K1_eq_iff qstar1_pos qstar1_lt_one).mpr qstar1_root

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
  have hq : 0 < c₁ / c₀ := div_pos hc₁ hc₀
  have heq : ladderValue 1 (c₁ / c₀) = goldenRatio⁻¹ ^ 5 :=
    le_antisymm (ladderValue_one_le hq)
      ((le_of_eq hopt.symm).trans (ladder_prob_le 1 hc₀ hc₁ hnorm a b h₀ hA hB))
  rcases lt_trichotomy (c₁ / c₀) 1 with h1 | h1 | h1
  · exact two_mul_eq_of_ratio hc₀ hnorm ((hardy_K1_eq_iff hq h1).mp heq)
  · exfalso
    rw [h1, ladderValue_at_one] at heq
    exact (pow_pos (inv_pos.mpr goldenRatio_pos) 5).ne' heq.symm
  · rw [← ladderValue_inv 1 hq, inv_div] at heq
    have hq' : 0 < c₀ / c₁ := div_pos hc₀ hc₁
    have h1' : c₀ / c₁ < 1 := (div_lt_one hc₁).mpr ((one_lt_div hc₀).mp h1)
    have hn' : c₁ ^ 2 + c₀ ^ 2 = 1 := by linarith
    have := two_mul_eq_of_ratio hc₁ hn' ((hardy_K1_eq_iff hq' h1').mp heq)
    linear_combination this

/-! ### `K = 2`: the optimum over every real Schmidt state -/

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
      (8 * ρ ^ 2 + ρ - 11) / 25 :=
  (ladder_prob_le 2 hc₀ hc₁ hnorm a b h₀ hA hB).trans (ladderValue_two_le hρ (div_pos hc₁ hc₀))

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
  have hρ0 : 0 < ρ := pos_of_cubic hρ
  have hi : 0 < ρ⁻¹ := inv_pos.mpr hρ0
  have hi5 : 0 < ρ⁻¹ ^ 5 := pow_pos hi 5
  have hc₀ : 0 < √(ρ⁻¹) := Real.sqrt_pos.mpr hi
  have hc₁ : 0 < √(ρ⁻¹ ^ 5) := Real.sqrt_pos.mpr hi5
  have hn : √(ρ⁻¹) ^ 2 + √(ρ⁻¹ ^ 5) ^ 2 = 1 := by
    rw [Real.sq_sqrt hi.le, Real.sq_sqrt hi5.le]
    exact inv_add_inv_pow_five hρ
  have hs : √(ρ⁻¹ ^ 5) = ρ⁻¹ ^ 2 * √(ρ⁻¹) := by
    rw [show ρ⁻¹ ^ 5 = (ρ⁻¹ ^ 2) ^ 2 * ρ⁻¹ by ring,
      Real.sqrt_mul (show (0 : ℝ) ≤ (ρ⁻¹ ^ 2) ^ 2 by positivity),
      Real.sqrt_sq (show (0 : ℝ) ≤ ρ⁻¹ ^ 2 by positivity)]
  have hr : √(ρ⁻¹ ^ 5) / √(ρ⁻¹) = ρ⁻¹ ^ 2 := by
    rw [hs, mul_div_cancel_right₀ _ hc₀.ne']
  refine ⟨_, _, hc₀, hc₁, hn, Real.sq_sqrt hi.le, Real.sq_sqrt hi5.le, ?_⟩
  obtain ⟨a, b, h₀, hA, hB, hv⟩ := ladder_prob_attained 2 hc₀ hc₁ hn
  refine ⟨a, b, h₀, hA, hB, ?_⟩
  rw [hv, hr]
  exact (hardy_K2_eq_iff_inv_sq hρ (inv_sq_mem_Ioo hρ).1 (inv_sq_mem_Ioo hρ).2).mpr rfl

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
  have hq : 0 < c₁ / c₀ := div_pos hc₁ hc₀
  have heq : ladderValue 2 (c₁ / c₀) = (8 * ρ ^ 2 + ρ - 11) / 25 :=
    le_antisymm (ladderValue_two_le hρ hq)
      ((le_of_eq hopt.symm).trans (ladder_prob_le 2 hc₀ hc₁ hnorm a b h₀ hA hB))
  have ht : ρ⁻¹ + ρ⁻¹ ^ 5 = 1 := inv_add_inv_pow_five hρ
  rcases lt_trichotomy (c₁ / c₀) 1 with h1 | h1 | h1
  · left
    exact weights_of_ratio ht hc₀ hnorm ((hardy_K2_eq_iff_inv_sq hρ hq h1).mp heq)
  · exfalso
    rw [h1, ladderValue_at_one] at heq
    exact (value_pos hρ).ne' heq.symm
  · right
    rw [← ladderValue_inv 2 hq, inv_div] at heq
    have hq' : 0 < c₀ / c₁ := div_pos hc₀ hc₁
    have h1' : c₀ / c₁ < 1 := (div_lt_one hc₁).mpr ((one_lt_div hc₀).mp h1)
    have hn' : c₁ ^ 2 + c₀ ^ 2 = 1 := by linarith
    obtain ⟨hw₁, hw₂⟩ :=
      weights_of_ratio ht hc₁ hn' ((hardy_K2_eq_iff_inv_sq hρ hq' h1').mp heq)
    exact ⟨hw₂, hw₁⟩

end HardyLadder
