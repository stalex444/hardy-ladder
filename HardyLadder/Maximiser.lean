module

public import Mathlib
public import HardyLadder.Ladder
public import HardyLadder.Optimum
public import HardyLadder.OneHalf

@[expose] public section

/-!
# Every `K ≥ 1`: the maximiser of `P_K*` on `(0, 1)` is the unique zero there of Cereceda's `m_K`

Cereceda (J. Phys. A 35, 9105, 2002, eq. (20) and p. 4) characterises the maximisers of the closed
form `P_K*(q) = q² (1 − q^{2K})² / ((1 + q²)(1 + q^{2K+1})²)` as the two non-trivial real roots
`r₁ < 1 < r₂ = 1/r₁` of

  `m_K(x) = x^{4K+3} − (1 + 2K) x^{2K+3} − 2K x^{2K+2} − 2K x^{2K+1} − (1 + 2K) x^{2K} + 1`

("It can be shown"). This file proves the statement on `(0, 1)` for every `K ≥ 1`:

* `hasDerivAt_ladderValue`: for `q > 0`,
  `d/dq P_K*(q) = 2q (1 − q^{2K}) m_K(q) / ((1 + q²)² (1 + q^{2K+1})³)`;
* `cerecedaM_eq`: `m_K(x) = 1 − x^{2K} g_K(x)` with
  `g_K(x) = (1 + 2K) + 2K x + 2K x² + (1 + 2K) x³ − x^{2K+3}`;
* on `[0, 1]`, `g_K > 0` and `g_K' > 0` (because `3(1 + 2K) x² ≥ (2K + 3) x^{2K+2}`), so
  `x^{2K} g_K(x)` is strictly increasing and `m_K` strictly decreasing, from `m_K(0) = 1` to
  `m_K(1) = −8K`: `m_K` has exactly one zero `r` in `(0, 1)` (`existsUnique_cerecedaM_root`);
* hence `P_K*` is strictly increasing on `(0, r]` and strictly decreasing on `[r, 1)`, and `r` is
  its unique maximiser on `(0, 1)` (`ladderValue_isGreatest_of_root`,
  `eq_of_ladderValue_eq_of_root`);
* with the symmetry `P_K*(1/q) = P_K*(q)` and the closed-form bound, the optimum of the
  `K`-step ladder over every real Schmidt state and real settings is `P_K*(r)`
  (`ladder_prob_le_of_root`); it is attained at the Schmidt ratio `r` (the closed form's
  attainment, `ladder_prob_attained_of_ratio`, which holds at every ratio and does not use the
  symmetry), and every configuration attaining it has `c₁/c₀ ∈ {r, r⁻¹}`
  (`ratio_of_ladder_prob_eq_of_root`); attainment at `r⁻¹` follows from the symmetry and is not
  stated as a separate theorem.

`cerecedaM_one` and `cerecedaM_two` record the factorisations
`m₁(x) = (x + 1)³ (x⁴ − 3x³ + 3x² − 3x + 1)` and
`m₂(x) = (x + 1)³ (x² + 1)(x³ − 2x² + x − 1)(x³ − x² + 2x − 1)`, through which the `K = 1`
quartic and the `K = 2` cubic of `HardyK1.lean` and `HardyK2.lean` are the factors of `m_K`
carrying the root in `(0, 1)`.

The seven theorems `hasDerivAt_ladderValue`, `existsUnique_cerecedaM_root`,
`ladderValue_isGreatest_of_root`, `eq_of_ladderValue_eq_of_root`, `ladder_prob_le_of_root`,
`ladder_prob_attained_of_ratio` and `ratio_of_ladder_prob_eq_of_root` prove compared statements
5–11 (`HardyLadder.Entry.*` in `Solution.lean`, where `ladderValue K q` and, in all but
statement 10, `cerecedaM K x` are written out); the other theorems of this file are uncompared
library lemmas.
-/

namespace HardyLadder

open Real

/-- Cereceda's polynomial (J. Phys. A 35, 9105, 2002, eq. (20)):
`m_K(x) = x^{4K+3} − (1 + 2K) x^{2K+3} − 2K x^{2K+2} − 2K x^{2K+1} − (1 + 2K) x^{2K} + 1`. -/
noncomputable def cerecedaM (K : ℕ) (x : ℝ) : ℝ :=
  x ^ (4 * K + 3) - (1 + 2 * K) * x ^ (2 * K + 3) - 2 * K * x ^ (2 * K + 2) -
    2 * K * x ^ (2 * K + 1) - (1 + 2 * K) * x ^ (2 * K) + 1

/-- The cofactor `g_K(x) = (1 + 2K) + 2K x + 2K x² + (1 + 2K) x³ − x^{2K+3}`. -/
noncomputable def gK (K : ℕ) (x : ℝ) : ℝ :=
  (1 + 2 * K) + 2 * K * x + 2 * K * x ^ 2 + (1 + 2 * K) * x ^ 3 - x ^ (2 * K + 3)

/-- `m_K(x) = 1 − x^{2K} g_K(x)`. -/
theorem cerecedaM_eq (K : ℕ) (x : ℝ) : cerecedaM K x = 1 - x ^ (2 * K) * gK K x := by
  unfold cerecedaM gK
  ring

/-- `m₁(x) = (x + 1)³ (x⁴ − 3x³ + 3x² − 3x + 1)`. -/
theorem cerecedaM_one (x : ℝ) :
    cerecedaM 1 x = (x + 1) ^ 3 * (x ^ 4 - 3 * x ^ 3 + 3 * x ^ 2 - 3 * x + 1) := by
  unfold cerecedaM
  push_cast
  ring

/-- `m₂(x) = (x + 1)³ (x² + 1)(x³ − 2x² + x − 1)(x³ − x² + 2x − 1)`. -/
theorem cerecedaM_two (x : ℝ) :
    cerecedaM 2 x = (x + 1) ^ 3 * (x ^ 2 + 1) * (x ^ 3 - 2 * x ^ 2 + x - 1) *
      (x ^ 3 - x ^ 2 + 2 * x - 1) := by
  unfold cerecedaM
  push_cast
  ring

/-- `m_K(0) = 1` for `K ≥ 1`. -/
theorem cerecedaM_zero (K : ℕ) (hK : 1 ≤ K) : cerecedaM K 0 = 1 := by
  rw [cerecedaM_eq, zero_pow (by omega : 2 * K ≠ 0), zero_mul, sub_zero]

/-- `m_K(1) = −8K`. -/
theorem cerecedaM_at_one (K : ℕ) : cerecedaM K 1 = -(8 * K) := by
  unfold cerecedaM
  simp only [one_pow, mul_one]
  ring

/-! ### The derivative of `P_K*` -/

/-- **The derivative of the closed form.** For `q > 0`,
`d/dq P_K*(q) = 2q (1 − q^{2K}) m_K(q) / ((1 + q²)² (1 + q^{2K+1})³)`. -/
theorem hasDerivAt_ladderValue (K : ℕ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (ladderValue K)
      (2 * q * (1 - q ^ (2 * K)) * cerecedaM K q /
        ((1 + q ^ 2) ^ 2 * (1 + q ^ (2 * K + 1)) ^ 3)) q := by
  have hq0 : q ≠ 0 := hq.ne'
  have hD1 : 1 + q ^ 2 ≠ 0 := by positivity
  have hD2 : 1 + q ^ (2 * K + 1) ≠ 0 := by positivity
  have hN := (hasDerivAt_pow 2 q).fun_mul
    (((hasDerivAt_const (x := q) (c := (1 : ℝ))).fun_sub (hasDerivAt_pow (2 * K) q)).fun_pow 2)
  have hD := ((hasDerivAt_const (x := q) (c := (1 : ℝ))).fun_add (hasDerivAt_pow 2 q)).fun_mul
    (((hasDerivAt_const (x := q) (c := (1 : ℝ))).fun_add (hasDerivAt_pow (2 * K + 1) q)).fun_pow 2)
  have h := hN.fun_div hD (mul_ne_zero hD1 (pow_ne_zero 2 hD2))
  refine h.congr_deriv ?_
  have key1 : ((2 * K : ℕ) : ℝ) * q ^ (2 * K - 1) = 2 * K * q ^ (2 * K) / q := by
    rcases K with _ | k
    · simp
    · rw [eq_div_iff hq0, mul_assoc, pow_sub_one_mul (by omega)]
      push_cast
      ring
  have key2 : ((2 * K + 1 : ℕ) : ℝ) * q ^ (2 * K + 1 - 1) = (2 * K + 1) * q ^ (2 * K) := by
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  rw [key1, key2]
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  have e1 : q ^ (2 * K + 1) = q * q ^ (2 * K) := by ring
  have e2 : q ^ (2 * K + 2) = q ^ 2 * q ^ (2 * K) := by ring
  have e3 : q ^ (2 * K + 3) = q ^ 3 * q ^ (2 * K) := by ring
  have e4 : q ^ (4 * K + 3) = q ^ 3 * (q ^ (2 * K)) ^ 2 := by ring
  have hD2' : 1 + q * q ^ (2 * K) ≠ 0 := by positivity
  unfold cerecedaM
  rw [e4, e3, e2, e1]
  field_simp
  ring

/-! ### `g_K` and the unique zero of `m_K` in `(0, 1)` -/

/-- The derivative of `g_K`. -/
theorem hasDerivAt_gK (K : ℕ) (x : ℝ) :
    HasDerivAt (gK K)
      (2 * K + 2 * K * (2 * x) + (1 + 2 * K) * (3 * x ^ 2) - (2 * K + 3) * x ^ (2 * K + 2)) x := by
  have h1 := (hasDerivAt_id' (x := x)).const_mul (2 * (K : ℝ))
  have h2 := (hasDerivAt_pow 2 x).const_mul (2 * (K : ℝ))
  have h3 := (hasDerivAt_pow 3 x).const_mul (1 + 2 * (K : ℝ))
  have h4 := hasDerivAt_pow (2 * K + 3) x
  have h := ((((hasDerivAt_const (x := x) (c := 1 + 2 * (K : ℝ))).fun_add h1).fun_add h2).fun_add
    h3).fun_sub h4
  refine h.congr_deriv ?_
  rw [show 2 * K + 3 - 1 = 2 * K + 2 by omega]
  push_cast
  ring

/-- `g_K' > 0` on `(0, 1)` for `K ≥ 1`: `3(1 + 2K) x² ≥ (2K + 3) x^{2K+2}`. -/
theorem gK_deriv_pos (K : ℕ) (hK : 1 ≤ K) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < 2 * K + 2 * K * (2 * x) + (1 + 2 * K) * (3 * x ^ 2) - (2 * K + 3) * x ^ (2 * K + 2) := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hp : x ^ (2 * K + 2) ≤ x ^ 2 := pow_le_pow_of_le_one hx0.le hx1.le (by omega)
  have h1 : 0 ≤ (2 * (K : ℝ) + 3) * (x ^ 2 - x ^ (2 * K + 2)) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hp)
  nlinarith [mul_pos (by linarith : (0 : ℝ) < K) hx0,
    mul_pos (by linarith : (0 : ℝ) < K) (pow_pos hx0 2)]

/-- `g_K > 0` on `[0, 1]`. -/
theorem gK_pos (K : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 < gK K x := by
  unfold gK
  have hp : x ^ (2 * K + 3) ≤ x ^ 3 := pow_le_pow_of_le_one hx.1 hx.2 (by omega)
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith [mul_nonneg hK hx.1, mul_nonneg hK (pow_nonneg hx.1 2),
    mul_nonneg hK (pow_nonneg hx.1 3)]

/-- `g_K` is strictly increasing on `[0, 1]` for `K ≥ 1`. -/
theorem strictMonoOn_gK (K : ℕ) (hK : 1 ≤ K) : StrictMonoOn (gK K) (Set.Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
  · exact fun x _ => (hasDerivAt_gK K x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_gK K x).deriv]
    exact gK_deriv_pos K hK hx.1 hx.2

/-- `x^{2K} g_K(x)` is strictly increasing on `[0, 1]` for `K ≥ 1`. -/
theorem strictMonoOn_pow_mul_gK (K : ℕ) (hK : 1 ≤ K) :
    StrictMonoOn (fun x : ℝ => x ^ (2 * K) * gK K x) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have hg : gK K x < gK K y := strictMonoOn_gK K hK hx hy hxy
  have hgx : 0 < gK K x := gK_pos K hx
  have hy0 : 0 < y := lt_of_le_of_lt hx.1 hxy
  have hpow : x ^ (2 * K) ≤ y ^ (2 * K) := pow_le_pow_left₀ hx.1 hxy.le _
  have hypos : 0 < y ^ (2 * K) := pow_pos hy0 _
  show x ^ (2 * K) * gK K x < y ^ (2 * K) * gK K y
  calc x ^ (2 * K) * gK K x ≤ y ^ (2 * K) * gK K x := mul_le_mul_of_nonneg_right hpow hgx.le
    _ < y ^ (2 * K) * gK K y := mul_lt_mul_of_pos_left hg hypos

/-- `m_K` is strictly decreasing on `[0, 1]` for `K ≥ 1`. -/
theorem strictAntiOn_cerecedaM (K : ℕ) (hK : 1 ≤ K) :
    StrictAntiOn (cerecedaM K) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have h := strictMonoOn_pow_mul_gK K hK hx hy hxy
  simp only at h
  rw [cerecedaM_eq, cerecedaM_eq]
  linarith

/-- `m_K` has a zero in `(0, 1)` for `K ≥ 1` (intermediate value theorem: `m_K(0) = 1`,
`m_K(1) = −8K`). -/
theorem exists_cerecedaM_root (K : ℕ) (hK : 1 ≤ K) :
    ∃ r ∈ Set.Ioo (0 : ℝ) 1, cerecedaM K r = 0 := by
  have hc : Continuous (fun x : ℝ => cerecedaM K x) := by
    simp only [cerecedaM]
    fun_prop
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h0 : (0 : ℝ) ∈
      Set.Ioo ((fun x : ℝ => cerecedaM K x) 1) ((fun x : ℝ => cerecedaM K x) 0) := by
    simp only [cerecedaM_zero K hK, cerecedaM_at_one]
    constructor <;> linarith
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo' zero_le_one hc.continuousOn h0
  exact ⟨r, hr, hr0⟩

/-- **`m_K` has exactly one zero in `(0, 1)`**, for every `K ≥ 1`. -/
theorem existsUnique_cerecedaM_root (K : ℕ) (hK : 1 ≤ K) :
    ∃! r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 ∧ cerecedaM K r = 0 := by
  obtain ⟨r, hr, hr0⟩ := exists_cerecedaM_root K hK
  refine ⟨r, ⟨hr, hr0⟩, ?_⟩
  rintro s ⟨hs, hs0⟩
  exact (strictAntiOn_cerecedaM K hK).injOn (Set.Ioo_subset_Icc_self hs)
    (Set.Ioo_subset_Icc_self hr) (hs0.trans hr0.symm)

/-- Left of the zero, `m_K > 0`. -/
theorem cerecedaM_pos_of_lt (K : ℕ) (hK : 1 ≤ K) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hm : cerecedaM K r = 0) {x : ℝ} (hx : 0 ≤ x) (hxr : x < r) : 0 < cerecedaM K x := by
  have := strictAntiOn_cerecedaM K hK ⟨hx, (hxr.trans hr.2).le⟩ (Set.Ioo_subset_Icc_self hr) hxr
  linarith

/-- Right of the zero, `m_K < 0`. -/
theorem cerecedaM_neg_of_gt (K : ℕ) (hK : 1 ≤ K) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hm : cerecedaM K r = 0) {x : ℝ} (hrx : r < x) (hx : x ≤ 1) : cerecedaM K x < 0 := by
  have := strictAntiOn_cerecedaM K hK (Set.Ioo_subset_Icc_self hr) ⟨(hr.1.trans hrx).le, hx⟩ hrx
  linarith

/-! ### The unique maximiser of `P_K*` on `(0, 1)` -/

/-- `P_K*(q) > 0` on `(0, 1)` for `K ≥ 1`. -/
theorem ladderValue_pos (K : ℕ) (hK : 1 ≤ K) {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    0 < ladderValue K q := by
  unfold ladderValue
  have h1 : 0 < 1 - q ^ (2 * K) := sub_pos.mpr (pow_lt_one₀ hq.1.le hq.2 (by omega))
  have h0 := hq.1
  exact div_pos (mul_pos (by positivity) (pow_pos h1 2)) (by positivity)

/-- `P_K*` is strictly increasing on `(0, r]`. -/
theorem strictMonoOn_ladderValue (K : ℕ) (hK : 1 ≤ K) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hm : cerecedaM K r = 0) : StrictMonoOn (ladderValue K) (Set.Ioc 0 r) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 r)
  · exact fun x hx => (hasDerivAt_ladderValue K hx.1).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    rw [(hasDerivAt_ladderValue K hx.1).deriv]
    have hx0 := hx.1
    have hx1 : x < 1 := hx.2.trans hr.2
    have hm' : 0 < cerecedaM K x := cerecedaM_pos_of_lt K hK hr hm hx0.le hx.2
    have h1 : 0 < 1 - x ^ (2 * K) := sub_pos.mpr (pow_lt_one₀ hx0.le hx1 (by omega))
    exact div_pos (mul_pos (mul_pos (by positivity) h1) hm') (by positivity)

/-- `P_K*` is strictly decreasing on `[r, 1)`. -/
theorem strictAntiOn_ladderValue (K : ℕ) (hK : 1 ≤ K) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hm : cerecedaM K r = 0) : StrictAntiOn (ladderValue K) (Set.Ico r 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ico r 1)
  · exact fun x hx =>
      (hasDerivAt_ladderValue K (hr.1.trans_le hx.1)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    have hx0 : 0 < x := hr.1.trans hx.1
    rw [(hasDerivAt_ladderValue K hx0).deriv]
    have hm' : cerecedaM K x < 0 := cerecedaM_neg_of_gt K hK hr hm hx.1 hx.2.le
    have h1 : 0 < 1 - x ^ (2 * K) := sub_pos.mpr (pow_lt_one₀ hx0.le hx.2 (by omega))
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos (by positivity) h1) hm')
      (by positivity)

/-- At the zero `r` of `m_K` in `(0, 1)`, `P_K*(q) ≤ P_K*(r)` for every `q ∈ (0, 1)`. -/
theorem ladderValue_le_of_root (K : ℕ) (hK : 1 ≤ K) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hm : cerecedaM K r = 0) {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    ladderValue K q ≤ ladderValue K r := by
  rcases le_or_gt q r with h | h
  · exact (strictMonoOn_ladderValue K hK hr hm).monotoneOn ⟨hq.1, h⟩ ⟨hr.1, le_rfl⟩ h
  · exact (strictAntiOn_ladderValue K hK hr hm).antitoneOn ⟨le_rfl, hr.2⟩ ⟨h.le, hq.2⟩ h.le

/-- **The maximum of `P_K*` on `(0, 1)` is its value at the zero of `m_K`.** -/
theorem ladderValue_isGreatest_of_root (K : ℕ) (hK : 1 ≤ K) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hm : cerecedaM K r = 0) :
    IsGreatest ((fun q : ℝ => ladderValue K q) '' Set.Ioo 0 1) (ladderValue K r) :=
  ⟨⟨r, hr, rfl⟩, by
    rintro _ ⟨q, hq, rfl⟩
    exact ladderValue_le_of_root K hK hr hm hq⟩

/-- **The maximiser is unique**: a `q ∈ (0, 1)` with `P_K*(q) = P_K*(r)` is `r`. -/
theorem eq_of_ladderValue_eq_of_root (K : ℕ) (hK : 1 ≤ K) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hm : cerecedaM K r = 0) {q : ℝ}
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (h : ladderValue K q = ladderValue K r) : q = r := by
  rcases lt_trichotomy q r with h1 | h1 | h1
  · have := strictMonoOn_ladderValue K hK hr hm ⟨hq.1, h1.le⟩ ⟨hr.1, le_rfl⟩ h1
    linarith
  · exact h1
  · have := strictAntiOn_ladderValue K hK hr hm ⟨le_rfl, hr.2⟩ ⟨h1.le, hq.2⟩ h1
    linarith

/-- The bound on all of `q > 0`, by the symmetry `P_K*(1/q) = P_K*(q)`. -/
theorem ladderValue_le_of_root_of_pos (K : ℕ) (hK : 1 ≤ K) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hm : cerecedaM K r = 0) {q : ℝ} (hq : 0 < q) :
    ladderValue K q ≤ ladderValue K r := by
  rcases lt_trichotomy q 1 with h1 | h1 | h1
  · exact ladderValue_le_of_root K hK hr hm ⟨hq, h1⟩
  · rw [h1, ladderValue_at_one]
    exact (ladderValue_pos K hK hr).le
  · rw [← ladderValue_inv K hq]
    exact ladderValue_le_of_root K hK hr hm ⟨inv_pos.mpr hq, inv_lt_one_of_one_lt₀ h1⟩

/-! ### The optimum over every real Schmidt state, every `K ≥ 1` -/

/-- **The `K`-step bound at the zero of `m_K`.** Under the `K`-step ladder constraints, for every
Schmidt state, `P(A_K = 1, B_K = 1) ≤ P_K*(r)`. -/
theorem ladder_prob_le_of_root (K : ℕ) (hK : 1 ≤ K) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hm : cerecedaM K r = 0) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) :
    (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 ≤ ladderValue K r :=
  (ladder_prob_le K hc₀ hc₁ hnorm a b h₀ hA hB).trans
    (ladderValue_le_of_root_of_pos K hK hr hm (div_pos hc₁ hc₀))

/-- **Every value `P_K*(r)`, `r > 0`, is attained at the Schmidt ratio `r`**: some state with
`c₁/c₀ = r` and some angles satisfying the `K`-step constraints give
`P(A_K = 1, B_K = 1) = P_K*(r)`. -/
theorem ladder_prob_attained_of_ratio (K : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ c₀ ^ 2 + c₁ ^ 2 = 1 ∧ c₁ / c₀ = r ∧
      ∃ a b : ℕ → ℝ,
        (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0 ∧
        (∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
          c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0) ∧
        (∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
          c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) ∧
        (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 = ladderValue K r := by
  obtain ⟨c₀, c₁, hc₀, hc₁, hn, hrat⟩ := exists_state_of_ratio hr
  obtain ⟨a, b, h₀, hA, hB, hv⟩ := ladder_prob_attained K hc₀ hc₁ hn
  refine ⟨c₀, c₁, hc₀, hc₁, hn, hrat, a, b, h₀, hA, hB, ?_⟩
  rw [hv, hrat]

/-- **The optimal states for every `K ≥ 1`.** If angles satisfying the `K`-step constraints give
`P(A_K = 1, B_K = 1) = P_K*(r)`, `r` the zero of `m_K` in `(0, 1)`, then `c₁/c₀ = r` or
`c₁/c₀ = r⁻¹`. -/
theorem ratio_of_ladder_prob_eq_of_root (K : ℕ) (hK : 1 ≤ K) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hm : cerecedaM K r = 0) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0)
    (hopt : (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 = ladderValue K r) :
    c₁ / c₀ = r ∨ c₁ / c₀ = r⁻¹ := by
  have hq : 0 < c₁ / c₀ := div_pos hc₁ hc₀
  have heq : ladderValue K (c₁ / c₀) = ladderValue K r :=
    le_antisymm (ladderValue_le_of_root_of_pos K hK hr hm hq)
      ((le_of_eq hopt.symm).trans (ladder_prob_le K hc₀ hc₁ hnorm a b h₀ hA hB))
  rcases lt_trichotomy (c₁ / c₀) 1 with h1 | h1 | h1
  · exact Or.inl (eq_of_ladderValue_eq_of_root K hK hr hm ⟨hq, h1⟩ heq)
  · exfalso
    rw [h1, ladderValue_at_one] at heq
    exact (ladderValue_pos K hK hr).ne' heq.symm
  · right
    rw [← ladderValue_inv K hq] at heq
    have := eq_of_ladderValue_eq_of_root K hK hr hm
      ⟨inv_pos.mpr hq, inv_lt_one_of_one_lt₀ h1⟩ heq
    rw [← this, inv_inv]

end HardyLadder
