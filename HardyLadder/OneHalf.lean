module

public import Mathlib
public import HardyLadder.Ladder
public import HardyLadder.Optimum

@[expose] public section

/-!
# Every `K`: the ladder probability is below one half, and one half is approached

For a two-qubit state in Schmidt form `c₀|00⟩ + c₁|11⟩` (`c₀, c₁ > 0`, `c₀² + c₁² = 1`) and real
settings satisfying the `K`-step ladder constraints, `P(A_K = 1, B_K = 1) < 1/2` for every `K`
(`ladder_prob_lt_half`); and for every `ε > 0` there is `K₀` such that for every `K ≥ K₀` some
normalised Schmidt state and some real settings satisfying the `K`-step constraints give
`P(A_K = 1, B_K = 1) > 1/2 − ε` (`ladder_prob_approaches_half`). Together: over all `K`, all
two-qubit Schmidt states and all real settings, the supremum of the ladder probability is `1/2`,
and it is not attained.

The bound is the two-qubit, real-settings, Schmidt-form case of a stronger bound that follows from
known results: Cereceda (Quantum Inf. Process. 15, 1779, 2016, eqs. (8)–(9)) combines the
no-signalling identity `CHSH_K = 2K + 4P_K` with Wehner's chained-CHSH Tsirelson bound for ±1
observables (PRA 73, 022110, 2006) to get `P_K ≤ L_K = ¼[2(K + 1)cos(π/(2K + 2)) − 2K]`, and
`L_K < 1/2` because the cosine is below 1. Cereceda states his setting as two qubits, but neither
step uses the dimension, so the bound holds for any state and any ±1 observables in every
dimension (this inference, and `L_K < 1/2`, are drawn here; Cereceda prints `P_K ≤ L_K` and that
`L_K` tends to `0.5`). No-signalling alone allows exactly `1/2` for every `K` (Cereceda, Adv.
Stud. Theor. Phys. 9, 433, 2015). The
approach to `1/2` is the behaviour of the ladder found by Hardy (1997) and Boschi, Branca, De
Martini and Hardy (1997), with equal settings (unequal real settings: Cereceda 2002, eq. (18)):
in the words of Cereceda (J. Phys. A 35, 9105, 2002, after eq. (19)), "the maximum value of PK
is (50 − δ)% which is realized for K → ∞ and a state that is not quite maximally entangled".

## Proof

By the closed-form bound (`ladder_prob_le`), `P(A_K = 1, B_K = 1) ≤ P_K*(q)` with `q = c₁/c₀`. For
`q ∈ (0, 1)`, `P_K*(q) = q²/(1 + q²) · ((1 − q^{2K})/(1 + q^{2K+1}))²`, where `q²/(1 + q²) < 1/2`
and `0 ≤ 1 − q^{2K} ≤ 1 ≤ 1 + q^{2K+1}`; `q > 1` reduces to `q ∈ (0, 1)` by the symmetry
`P_K*(1/q) = P_K*(q)` (`ladderValue_inv`), and `P_K*(1) = 0` (`ladderValue_at_one`). For the
approach, fix `q ∈ (0, 1)` with `q²/(1 + q²) > 1/2 − ε`; since `(q²)^K → 0`,
`P_K*(q) → q²/(1 + q²)` as `K → ∞` (`tendsto_ladderValue`), and the closed form is attained at
every `K` (`ladder_prob_attained`) by the state with `c₁/c₀ = q`.
-/

namespace HardyLadder

open Real Filter Topology

/-- On `(0, 1)`: `P_K*(q) < 1/2`. -/
theorem ladderValue_lt_half_of_lt_one (K : ℕ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ladderValue K q < 1 / 2 := by
  unfold ladderValue
  have ht0 : 0 < q ^ (2 * K) := pow_pos hq0 _
  have ht1 : q ^ (2 * K) ≤ 1 := pow_le_one₀ hq0.le hq1.le
  have hu0 : 0 < q ^ (2 * K + 1) := pow_pos hq0 _
  have hden : 0 < (1 + q ^ 2) * (1 + q ^ (2 * K + 1)) ^ 2 := by positivity
  rw [div_lt_iff₀ hden]
  have h1 : (1 - q ^ (2 * K)) ^ 2 ≤ 1 := by nlinarith
  have h2 : 1 ≤ (1 + q ^ (2 * K + 1)) ^ 2 := by nlinarith
  have hq2 : q ^ 2 < 1 := by nlinarith
  have hA : q ^ 2 * (1 - q ^ (2 * K)) ^ 2 ≤ q ^ 2 * 1 :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg q)
  have hB : 1 / 2 * (1 + q ^ 2) * 1 ≤ 1 / 2 * (1 + q ^ 2) * (1 + q ^ (2 * K + 1)) ^ 2 :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  nlinarith

/-- **For every `K` and every `q > 0`, `P_K*(q) < 1/2`.** -/
theorem ladderValue_lt_half (K : ℕ) {q : ℝ} (hq : 0 < q) : ladderValue K q < 1 / 2 := by
  rcases lt_trichotomy q 1 with h1 | h1 | h1
  · exact ladderValue_lt_half_of_lt_one K hq h1
  · rw [h1, ladderValue_at_one]
    norm_num
  · rw [← ladderValue_inv K hq]
    exact ladderValue_lt_half_of_lt_one K (inv_pos.mpr hq) (inv_lt_one_of_one_lt₀ h1)

/-- **The `K`-step ladder probability is below one half, for every `K`.** For `c₀, c₁ > 0`
with `c₀² + c₁² = 1` and real angles satisfying the `K`-step ladder constraints,
`P(A_K = 1, B_K = 1) < 1/2`. This is the two-qubit, real-settings, Schmidt-form case of a
stronger bound that follows from Cereceda 2016, eq. (9), with Wehner 2006 (any state, any ±1
observables, any dimension; the inference is drawn here, see the module docstring); for two
qubits and equal settings it is in Hardy 1997 and Boschi, Branca, De Martini and Hardy 1997, as
quoted by Cereceda 2002 after eq. (19), and unequal real settings are Cereceda 2002, eq. (18). -/
theorem ladder_prob_lt_half (K : ℕ) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) :
    (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 < 1 / 2 :=
  (ladder_prob_le K hc₀ hc₁ hnorm a b h₀ hA hB).trans_lt
    (ladderValue_lt_half K (div_pos hc₁ hc₀))

/-- For fixed `q ∈ (0, 1)`, `P_K*(q) → q²/(1 + q²)` as `K → ∞`. -/
theorem tendsto_ladderValue {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun K : ℕ => ladderValue K q) atTop (𝓝 (q ^ 2 / (1 + q ^ 2))) := by
  have ht : Tendsto (fun K : ℕ => (q ^ 2) ^ K) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by nlinarith)
  have hform : (fun K : ℕ => ladderValue K q) = fun K : ℕ =>
      q ^ 2 * (1 - (q ^ 2) ^ K) ^ 2 / ((1 + q ^ 2) * (1 + q * (q ^ 2) ^ K) ^ 2) := by
    funext K
    have e1 : q ^ (2 * K) = (q ^ 2) ^ K := pow_mul q 2 K
    have e2 : q ^ (2 * K + 1) = q * (q ^ 2) ^ K := by
      rw [pow_succ, pow_mul]
      ring
    unfold ladderValue
    rw [e2, e1]
  rw [hform]
  have hnum : Tendsto (fun K : ℕ => q ^ 2 * (1 - (q ^ 2) ^ K) ^ 2) atTop
      (𝓝 (q ^ 2 * (1 - 0) ^ 2)) :=
    tendsto_const_nhds.mul ((tendsto_const_nhds.sub ht).pow 2)
  have hden : Tendsto (fun K : ℕ => (1 + q ^ 2) * (1 + q * (q ^ 2) ^ K) ^ 2) atTop
      (𝓝 ((1 + q ^ 2) * (1 + q * 0) ^ 2)) :=
    tendsto_const_nhds.mul ((tendsto_const_nhds.add (tendsto_const_nhds.mul ht)).pow 2)
  have hne : (1 + q ^ 2) * (1 + q * 0) ^ 2 ≠ 0 := by
    rw [mul_zero, add_zero, one_pow, mul_one]
    positivity
  have hlim := hnum.div hden hne
  rw [show q ^ 2 * (1 - 0) ^ 2 / ((1 + q ^ 2) * (1 + q * 0) ^ 2) = q ^ 2 / (1 + q ^ 2) by ring]
    at hlim
  exact hlim

/-- For every `ε > 0` there is `q ∈ (0, 1)` with `q²/(1 + q²) > 1/2 − ε`. -/
theorem exists_ratio_gt {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ 1 / 2 - ε < q ^ 2 / (1 + q ^ 2) := by
  obtain ⟨q, hlo, hhi⟩ :=
    exists_between (show max 0 (1 - ε) < 1 from max_lt one_pos (by linarith))
  have hq0 : 0 < q := lt_of_le_of_lt (le_max_left _ _) hlo
  have hqε : 1 - ε < q := lt_of_le_of_lt (le_max_right _ _) hlo
  refine ⟨q, hq0, hhi, ?_⟩
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [mul_pos (show 0 < ε - (1 - q) by linarith) (show 0 < 1 + q by linarith),
    mul_pos hε (show 0 < 1 - q by linarith), mul_nonneg hε.le (sq_nonneg q)]

/-- A normalised Schmidt state with any prescribed ratio `c₁/c₀ = q > 0`. -/
theorem exists_state_of_ratio {q : ℝ} (hq : 0 < q) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ c₀ ^ 2 + c₁ ^ 2 = 1 ∧ c₁ / c₀ = q := by
  have hs : 0 < √(1 + q ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : √(1 + q ^ 2) ^ 2 = 1 + q ^ 2 := Real.sq_sqrt (by positivity)
  have hc₀ : 0 < (√(1 + q ^ 2))⁻¹ := inv_pos.mpr hs
  refine ⟨_, _, hc₀, mul_pos hq hc₀, ?_, mul_div_cancel_right₀ q hc₀.ne'⟩
  have : ((√(1 + q ^ 2))⁻¹) ^ 2 + (q * (√(1 + q ^ 2))⁻¹) ^ 2 =
      (1 + q ^ 2) / √(1 + q ^ 2) ^ 2 := by ring
  rw [this, hs2, div_self (show (1 + q ^ 2 : ℝ) ≠ 0 by positivity)]

/-- **One half is approached** (Hardy 1997; Boschi, Branca, De Martini and Hardy 1997; as quoted
by Cereceda 2002 after eq. (19)). For every `ε > 0` there is `K₀` such that for every `K ≥ K₀`
some normalised Schmidt state `c₀, c₁ > 0` and some real angles satisfying the `K`-step ladder
constraints give `P(A_K = 1, B_K = 1) > 1/2 − ε`. -/
theorem ladder_prob_approaches_half {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ c₀ ^ 2 + c₁ ^ 2 = 1 ∧
      ∃ a b : ℕ → ℝ,
        (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0 ∧
        (∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
          c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0) ∧
        (∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
          c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) ∧
        1 / 2 - ε < (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 := by
  obtain ⟨q, hq0, hq1, hqε⟩ := exists_ratio_gt hε
  obtain ⟨K₀, hK₀⟩ :=
    eventually_atTop.mp ((tendsto_ladderValue hq0 hq1).eventually (lt_mem_nhds hqε))
  refine ⟨K₀, fun K hK => ?_⟩
  obtain ⟨c₀, c₁, hc₀, hc₁, hn, hr⟩ := exists_state_of_ratio hq0
  obtain ⟨a, b, h₀, hA, hB, hv⟩ := ladder_prob_attained K hc₀ hc₁ hn
  refine ⟨c₀, c₁, hc₀, hc₁, hn, a, b, h₀, hA, hB, ?_⟩
  rw [hv, hr]
  exact hK₀ K hK

end HardyLadder
