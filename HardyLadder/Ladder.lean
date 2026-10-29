module

public import Mathlib

@[expose] public section

/-!
# The two-qubit Hardy ladder: the closed form `P_K*(q)`

Setting (Hardy, in *New Developments on Fundamental Problems in Quantum Physics*, Kluwer 1997, and
Boschi, Branca, De Martini and Hardy, PRL 79, 2755, 1997; Hardy, PRL 71, 1665, 1993 for `K = 1`).
A two-qubit pure state in Schmidt form `c₀|00⟩ + c₁|11⟩` with `c₀, c₁ > 0`,
`c₀² + c₁² = 1`, and real projective measurements: party A's `k`-th measurement has outcome `1`
along the direction `(cos aₖ, sin aₖ)` and outcome `0` along `(−sin aₖ, cos aₖ)`; party B's along
`(cos bₖ, sin bₖ)` and `(−sin bₖ, cos bₖ)`. The joint probabilities are squared amplitudes:

* `P(Aⱼ = 1, Bⱼ = 1) = (c₀ cos aⱼ cos bⱼ + c₁ sin aⱼ sin bⱼ)²`,
* `P(Aₖ₊₁ = 1, Bₖ = 0) = (c₀ cos aₖ₊₁ (−sin bₖ) + c₁ sin aₖ₊₁ cos bₖ)²`,
* `P(Aₖ = 0, Bₖ₊₁ = 1) = (c₀ (−sin aₖ) cos bₖ₊₁ + c₁ cos aₖ sin bₖ₊₁)²`.

The `K`-step ladder constraints are `P(A₀ = 1, B₀ = 1) = 0`, `P(Aₖ₊₁ = 1, Bₖ = 0) = 0` and
`P(Aₖ = 0, Bₖ₊₁ = 1) = 0` for `k < K`; the objective is `P(A_K = 1, B_K = 1)`.

**Theorem** (`ladder_prob_le`): under the constraints,
`P(A_K = 1, B_K = 1) ≤ P_K*(q) := q² (1 − q^{2K})² / ((1 + q²)(1 + q^{2K+1})²)`, `q = c₁/c₀`,
and (`ladder_prob_attained`) the bound is attained.

## Proof

Write `M = diag(c₀, c₁)`, `N = diag(c₁, c₀)`, `J = [[0, −1], [1, 0]]`, and `Aₖ = (cos aₖ, sin aₖ)`,
`Bₖ = (cos bₖ, sin bₖ)` as unit vectors of `ℝ²`. Each constraint says that a unit vector is
orthogonal to a nonzero vector, hence parallel to its rotation: `B₀ ∥ J M A₀`, `Aₖ₊₁ ∥ N Bₖ`,
`Bₖ₊₁ ∥ N Aₖ`. Parallelism (`cross u v = 0`) is transitive through nonzero vectors and preserved
by `N`, so `A_K ∥ V_K`, `B_K ∥ W_K` for the reference chain `V₀ = A₀`, `W₀ = J M A₀`,
`Vₖ₊₁ = N Wₖ`, `Wₖ₊₁ = N Vₖ`; explicitly `{V_K, W_K} = {N^K A₀, N^K J M A₀}` (the order depends
on the parity of `K`). For unit `A ∥ V`, `B ∥ W`, `(Aᵀ M B)² = (Vᵀ M W)² / (|V|² |W|²)`, and with
`A₀ = (x, y)` the ratio is
`c₀² c₁² x² y² (c₀^{2K} − c₁^{2K})² / ((c₁^{2K} x² + c₀^{2K} y²)(c₀^{2K+2} x² + c₁^{2K+2} y²))`,
which is at most `c₀² c₁² (c₀^{2K} − c₁^{2K})² / (c₀^{2K+1} + c₁^{2K+1})²` because
`(c₁^{2K} x² + c₀^{2K} y²)(c₀^{2K+2} x² + c₁^{2K+2} y²) − x² y² (c₀^{2K+1} + c₁^{2K+1})²
 = c₀^{2K} c₁^{2K} (c₀ x² − c₁ y²)² ≥ 0`
(this is the AM–GM step `tan² a₀ + tan² b₀ ≥ 2 |tan a₀ tan b₀|` of the tangent derivation). The
normalisation `c₀² + c₁² = 1` turns the symmetric form into `P_K*(c₁/c₀)`. Equality holds for the
chain with `tan a₀ = q^{−1/2}`, `tan b₀ = −q^{−1/2}`, `tan aₖ₊₁ = tan bₖ / q`,
`tan bₖ₊₁ = tan aₖ / q`, which `ladder_prob_attained` constructs with `Real.arctan`.
-/

namespace HardyLadder

/-- The closed form `P_K*(q) = q² (1 − q^{2K})² / ((1 + q²)(1 + q^{2K+1})²)`. -/
noncomputable def ladderValue (K : ℕ) (q : ℝ) : ℝ :=
  q ^ 2 * (1 - q ^ (2 * K)) ^ 2 / ((1 + q ^ 2) * (1 + q ^ (2 * K + 1)) ^ 2)

/-- The same bound in the Schmidt coefficients:
`c₀² c₁² (c₀^{2K} − c₁^{2K})² / (c₀^{2K+1} + c₁^{2K+1})²`. -/
noncomputable def ladderValue' (K : ℕ) (c₀ c₁ : ℝ) : ℝ :=
  c₀ ^ 2 * c₁ ^ 2 * (c₀ ^ (2 * K) - c₁ ^ (2 * K)) ^ 2 / (c₀ ^ (2 * K + 1) + c₁ ^ (2 * K + 1)) ^ 2

/-- The normalisation step, in abstract variables `a = c₀^K`, `b = c₁^K`. -/
theorem ladderValue_eq_aux {c₀ c₁ a b : ℝ} (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (ha : a ≠ 0)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) :
    c₁ ^ 2 / c₀ ^ 2 * (1 - b ^ 2 / a ^ 2) ^ 2 /
        ((1 + c₁ ^ 2 / c₀ ^ 2) * (1 + b ^ 2 * c₁ / (a ^ 2 * c₀)) ^ 2) =
      c₀ ^ 2 * c₁ ^ 2 * (a ^ 2 - b ^ 2) ^ 2 / (a ^ 2 * c₀ + b ^ 2 * c₁) ^ 2 := by
  have h1 : 1 + c₁ ^ 2 / c₀ ^ 2 = 1 / c₀ ^ 2 := by
    field_simp
    linear_combination hnorm
  rw [h1]
  field_simp

/-- With `c₀² + c₁² = 1` and `q = c₁/c₀`, the two forms agree. -/
theorem ladderValue_eq_ladderValue' (K : ℕ) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) : ladderValue K (c₁ / c₀) = ladderValue' K c₀ c₁ := by
  unfold ladderValue ladderValue'
  have ha : c₀ ^ (2 * K) = (c₀ ^ K) ^ 2 := by rw [pow_mul']
  have hb : c₁ ^ (2 * K) = (c₁ ^ K) ^ 2 := by rw [pow_mul']
  have ha' : c₀ ^ (2 * K + 1) = (c₀ ^ K) ^ 2 * c₀ := by rw [pow_succ, pow_mul']
  have hb' : c₁ ^ (2 * K + 1) = (c₁ ^ K) ^ 2 * c₁ := by rw [pow_succ, pow_mul']
  rw [div_pow, div_pow, div_pow, ha, hb, ha', hb']
  exact ladderValue_eq_aux hc₀.ne' hc₁.ne' (pow_pos hc₀ K).ne' hnorm

/-! ### Vectors of `ℝ²` -/

/-- The 2D cross product; `cross u v = 0` iff `u ∥ v`. -/
def cross (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- The squared Euclidean norm. -/
def nsq (u : ℝ × ℝ) : ℝ := u.1 ^ 2 + u.2 ^ 2

/-- `N = diag(c₁, c₀)`. -/
def nmap (c₀ c₁ : ℝ) (u : ℝ × ℝ) : ℝ × ℝ := (c₁ * u.1, c₀ * u.2)

/-- `N^k = diag(c₁^k, c₀^k)`. -/
def npow (c₀ c₁ : ℝ) (k : ℕ) (u : ℝ × ℝ) : ℝ × ℝ := (c₁ ^ k * u.1, c₀ ^ k * u.2)

/-- `J M = [[0, −c₁], [c₀, 0]]`: rotation by `π/2` after `M = diag(c₀, c₁)`. -/
def jm (c₀ c₁ : ℝ) (u : ℝ × ℝ) : ℝ × ℝ := (-(c₁ * u.2), c₀ * u.1)

/-- The amplitude `uᵀ M v = c₀ u₁ v₁ + c₁ u₂ v₂`. -/
def amp (c₀ c₁ : ℝ) (u v : ℝ × ℝ) : ℝ := c₀ * u.1 * v.1 + c₁ * u.2 * v.2

/-- The reference chain: `ref 0 = (A₀, J M A₀)`, `ref (k+1) = (N (ref k).2, N (ref k).1)`. -/
def ref (c₀ c₁ : ℝ) (u : ℝ × ℝ) : ℕ → (ℝ × ℝ) × (ℝ × ℝ)
  | 0 => (u, jm c₀ c₁ u)
  | k + 1 => (nmap c₀ c₁ (ref c₀ c₁ u k).2, nmap c₀ c₁ (ref c₀ c₁ u k).1)

theorem cross_self (u : ℝ × ℝ) : cross u u = 0 := by simp [cross]; ring

theorem amp_comm (c₀ c₁ : ℝ) (u v : ℝ × ℝ) : amp c₀ c₁ u v = amp c₀ c₁ v u := by
  simp [amp]; ring

/-- Parallelism is transitive through a nonzero vector. -/
theorem cross_trans {u v w : ℝ × ℝ} (huv : cross u v = 0) (hvw : cross v w = 0) (hv : v ≠ 0) :
    cross u w = 0 := by
  simp only [cross] at *
  have h1 : v.1 * (u.1 * w.2 - u.2 * w.1) = 0 := by linear_combination w.1 * huv + u.1 * hvw
  have h2 : v.2 * (u.1 * w.2 - u.2 * w.1) = 0 := by linear_combination w.2 * huv + u.2 * hvw
  rcases mul_eq_zero.mp h1 with h | h
  · rcases mul_eq_zero.mp h2 with h' | h'
    · exact absurd (Prod.ext h h') hv
    · exact h'
  · exact h

theorem cross_nmap (c₀ c₁ : ℝ) (u v : ℝ × ℝ) :
    cross (nmap c₀ c₁ u) (nmap c₀ c₁ v) = c₀ * c₁ * cross u v := by
  simp [cross, nmap]; ring

theorem nmap_ne_zero {c₀ c₁ : ℝ} (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) {u : ℝ × ℝ} (hu : nsq u = 1) :
    nmap c₀ c₁ u ≠ 0 := by
  intro h
  simp only [nmap, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, mul_eq_zero, hc₀, hc₁,
    false_or] at h
  simp [nsq, h.1, h.2] at hu

theorem nmap_npow (c₀ c₁ : ℝ) (k : ℕ) (u : ℝ × ℝ) :
    nmap c₀ c₁ (npow c₀ c₁ k u) = npow c₀ c₁ (k + 1) u := by
  simp [nmap, npow, pow_succ]; constructor <;> ring

theorem npow_zero (c₀ c₁ : ℝ) (u : ℝ × ℝ) : npow c₀ c₁ 0 u = u := by
  simp [npow]

/-- The reference chain in closed form, by parity. -/
theorem ref_closed (c₀ c₁ : ℝ) (u : ℝ × ℝ) (j : ℕ) :
    ref c₀ c₁ u (2 * j) = (npow c₀ c₁ (2 * j) u, npow c₀ c₁ (2 * j) (jm c₀ c₁ u)) ∧
    ref c₀ c₁ u (2 * j + 1) = (npow c₀ c₁ (2 * j + 1) (jm c₀ c₁ u), npow c₀ c₁ (2 * j + 1) u) := by
  induction j with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [ref, npow]
    · simp [ref, npow, nmap, jm]
  | succ j ih =>
    obtain ⟨-, h1⟩ := ih
    have e1 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    have hA : ref c₀ c₁ u (2 * (j + 1)) =
        (npow c₀ c₁ (2 * (j + 1)) u, npow c₀ c₁ (2 * (j + 1)) (jm c₀ c₁ u)) := by
      rw [e1, ref.eq_2, h1]
      simp only [nmap_npow]
    refine ⟨hA, ?_⟩
    rw [ref.eq_2, hA]
    simp only [nmap_npow]

/-- The chain lemma: under the ladder constraints every measurement vector is parallel to its
reference vector. -/
theorem chain {c₀ c₁ : ℝ} (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (A B : ℕ → ℝ × ℝ)
    (hA : ∀ k, nsq (A k) = 1) (hB : ∀ k, nsq (B k) = 1) (K : ℕ)
    (h0 : cross (B 0) (jm c₀ c₁ (A 0)) = 0)
    (hAB : ∀ k < K, cross (A (k + 1)) (nmap c₀ c₁ (B k)) = 0)
    (hBA : ∀ k < K, cross (B (k + 1)) (nmap c₀ c₁ (A k)) = 0) :
    ∀ k ≤ K, cross (A k) (ref c₀ c₁ (A 0) k).1 = 0 ∧ cross (B k) (ref c₀ c₁ (A 0) k).2 = 0 := by
  intro k
  induction k with
  | zero => intro _; exact ⟨cross_self _, h0⟩
  | succ k ih =>
    intro hk
    obtain ⟨ihA, ihB⟩ := ih (by omega)
    refine ⟨?_, ?_⟩
    · show cross (A (k + 1)) (nmap c₀ c₁ (ref c₀ c₁ (A 0) k).2) = 0
      refine cross_trans (hAB k (by omega)) ?_ (nmap_ne_zero hc₀ hc₁ (hB k))
      rw [cross_nmap, ihB, mul_zero]
    · show cross (B (k + 1)) (nmap c₀ c₁ (ref c₀ c₁ (A 0) k).1) = 0
      refine cross_trans (hBA k (by omega)) ?_ (nmap_ne_zero hc₀ hc₁ (hA k))
      rw [cross_nmap, ihA, mul_zero]

/-- For unit `A ∥ V` and unit `B ∥ W`: `(Aᵀ M B)² |V|² |W|² = (Vᵀ M W)²`. -/
theorem amp_sq_mul_eq (c₀ c₁ : ℝ) {A B V W : ℝ × ℝ} (hA : nsq A = 1) (hB : nsq B = 1)
    (hAV : cross A V = 0) (hBW : cross B W = 0) :
    amp c₀ c₁ A B ^ 2 * (nsq V * nsq W) = amp c₀ c₁ V W ^ 2 := by
  simp only [nsq, cross, amp] at *
  have hV1 : V.1 = (V.1 * A.1 + V.2 * A.2) * A.1 := by
    linear_combination (-V.1) * hA - A.2 * hAV
  have hV2 : V.2 = (V.1 * A.1 + V.2 * A.2) * A.2 := by
    linear_combination (-V.2) * hA + A.1 * hAV
  have hW1 : W.1 = (W.1 * B.1 + W.2 * B.2) * B.1 := by
    linear_combination (-W.1) * hB - B.2 * hBW
  have hW2 : W.2 = (W.1 * B.1 + W.2 * B.2) * B.2 := by
    linear_combination (-W.2) * hB + B.1 * hBW
  have hVn : V.1 ^ 2 + V.2 ^ 2 = (V.1 * A.1 + V.2 * A.2) ^ 2 := by
    linear_combination (-(V.1 ^ 2 + V.2 ^ 2)) * hA + (A.1 * V.2 - A.2 * V.1) * hAV
  have hWn : W.1 ^ 2 + W.2 ^ 2 = (W.1 * B.1 + W.2 * B.2) ^ 2 := by
    linear_combination (-(W.1 ^ 2 + W.2 ^ 2)) * hB + (B.1 * W.2 - B.2 * W.1) * hBW
  set l := V.1 * A.1 + V.2 * A.2 with hl
  set m := W.1 * B.1 + W.2 * B.2 with hm
  rw [hVn, hWn, hV1, hV2, hW1, hW2]
  ring

/-- The core inequality (the AM–GM step), in the Schmidt coefficients: with `a = c₀^K`,
`b = c₁^K`, `V = N^K (x, y) = (b x, a y)`, `W = N^K J M (x, y) = (−b c₁ y, a c₀ x)`,
`(Vᵀ M W)² (c₀ a² + c₁ b²)² ≤ c₀² c₁² (a² − b²)² |V|² |W|²`. -/
theorem core_ineq (c₀ c₁ a b x y : ℝ) :
    (c₀ * (b * x) * (-(b * c₁ * y)) + c₁ * (a * y) * (a * c₀ * x)) ^ 2 *
        (c₀ * a ^ 2 + c₁ * b ^ 2) ^ 2 ≤
      c₀ ^ 2 * c₁ ^ 2 * (a ^ 2 - b ^ 2) ^ 2 *
        (((b * x) ^ 2 + (a * y) ^ 2) * ((b * c₁ * y) ^ 2 + (a * c₀ * x) ^ 2)) := by
  have h : c₀ ^ 2 * c₁ ^ 2 * (a ^ 2 - b ^ 2) ^ 2 *
        (((b * x) ^ 2 + (a * y) ^ 2) * ((b * c₁ * y) ^ 2 + (a * c₀ * x) ^ 2)) -
      (c₀ * (b * x) * (-(b * c₁ * y)) + c₁ * (a * y) * (a * c₀ * x)) ^ 2 *
        (c₀ * a ^ 2 + c₁ * b ^ 2) ^ 2 =
      a ^ 2 * b ^ 2 * c₀ ^ 2 * c₁ ^ 2 * (a - b) ^ 2 * (a + b) ^ 2 * (c₀ * x ^ 2 - c₁ * y ^ 2) ^ 2 := by
    ring
  have hnn : 0 ≤ a ^ 2 * b ^ 2 * c₀ ^ 2 * c₁ ^ 2 * (a - b) ^ 2 * (a + b) ^ 2 *
      (c₀ * x ^ 2 - c₁ * y ^ 2) ^ 2 := by positivity
  linarith

theorem nsq_npow_pos {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (k : ℕ) {u : ℝ × ℝ}
    (hu : u ≠ 0) : 0 < nsq (npow c₀ c₁ k u) := by
  simp only [nsq, npow]
  have hk0 : c₀ ^ k ≠ 0 := (pow_pos hc₀ k).ne'
  have hk1 : c₁ ^ k ≠ 0 := (pow_pos hc₁ k).ne'
  rcases ne_or_eq u.1 0 with h | h
  · have h1 : c₁ ^ k * u.1 ≠ 0 := mul_ne_zero hk1 h
    have : 0 < (c₁ ^ k * u.1) ^ 2 := by positivity
    exact add_pos_of_pos_of_nonneg this (sq_nonneg _)
  · have h2 : u.2 ≠ 0 := fun h2 => hu (Prod.ext h h2)
    have h1 : c₀ ^ k * u.2 ≠ 0 := mul_ne_zero hk0 h2
    have : 0 < (c₀ ^ k * u.2) ^ 2 := by positivity
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) this

theorem ne_zero_of_nsq_eq_one {u : ℝ × ℝ} (hu : nsq u = 1) : u ≠ 0 := by
  rintro rfl
  simp [nsq] at hu

theorem jm_ne_zero {c₀ c₁ : ℝ} (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) {u : ℝ × ℝ} (hu : nsq u = 1) :
    jm c₀ c₁ u ≠ 0 := by
  intro h
  simp only [jm, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, neg_eq_zero, mul_eq_zero, hc₀, hc₁,
    false_or] at h
  simp [nsq, h.1, h.2] at hu

/-- The bound in vector form: for unit vectors `A_k, B_k` satisfying the ladder constraints,
`(A_Kᵀ M B_K)² ≤ ladderValue' K c₀ c₁`. -/
theorem amp_sq_le_ladderValue' {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (A B : ℕ → ℝ × ℝ)
    (hA : ∀ k, nsq (A k) = 1) (hB : ∀ k, nsq (B k) = 1) (K : ℕ)
    (h0 : cross (B 0) (jm c₀ c₁ (A 0)) = 0)
    (hAB : ∀ k < K, cross (A (k + 1)) (nmap c₀ c₁ (B k)) = 0)
    (hBA : ∀ k < K, cross (B (k + 1)) (nmap c₀ c₁ (A k)) = 0) :
    amp c₀ c₁ (A K) (B K) ^ 2 ≤ ladderValue' K c₀ c₁ := by
  obtain ⟨hVA, hWB⟩ := chain hc₀.ne' hc₁.ne' A B hA hB K h0 hAB hBA K le_rfl
  -- the reference vectors at step K, by parity
  set V := (ref c₀ c₁ (A 0) K).1 with hV
  set W := (ref c₀ c₁ (A 0) K).2 with hW
  have hmain : amp c₀ c₁ (A K) (B K) ^ 2 * (nsq V * nsq W) = amp c₀ c₁ V W ^ 2 :=
    amp_sq_mul_eq c₀ c₁ (hA K) (hB K) hVA hWB
  have hu0 : A 0 ≠ 0 := ne_zero_of_nsq_eq_one (hA 0)
  have hjm0 : jm c₀ c₁ (A 0) ≠ 0 := jm_ne_zero hc₀.ne' hc₁.ne' (hA 0)
  -- the core inequality in either parity
  have hcore : ∀ (P Q : ℝ × ℝ), P = npow c₀ c₁ K (A 0) → Q = npow c₀ c₁ K (jm c₀ c₁ (A 0)) →
      amp c₀ c₁ P Q ^ 2 * (c₀ ^ (2 * K + 1) + c₁ ^ (2 * K + 1)) ^ 2 ≤
        c₀ ^ 2 * c₁ ^ 2 * (c₀ ^ (2 * K) - c₁ ^ (2 * K)) ^ 2 * (nsq P * nsq Q) := by
    rintro P Q rfl rfl
    have ha : c₀ ^ (2 * K) = (c₀ ^ K) ^ 2 := by rw [pow_mul']
    have hb : c₁ ^ (2 * K) = (c₁ ^ K) ^ 2 := by rw [pow_mul']
    have ha' : c₀ ^ (2 * K + 1) = c₀ * (c₀ ^ K) ^ 2 := by rw [pow_succ, pow_mul']; ring
    have hb' : c₁ ^ (2 * K + 1) = c₁ * (c₁ ^ K) ^ 2 := by rw [pow_succ, pow_mul']; ring
    rw [ha, hb, ha', hb']
    simp only [amp, nsq, npow, jm]
    have := core_ineq c₀ c₁ (c₀ ^ K) (c₁ ^ K) (A 0).1 (A 0).2
    convert this using 2 <;> ring
  have hVWpos : 0 < nsq V * nsq W := by
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' K
    · obtain ⟨h1, -⟩ := ref_closed c₀ c₁ (A 0) j
      rw [hV, hW, hj, h1]
      exact mul_pos (nsq_npow_pos hc₀ hc₁ _ hu0) (nsq_npow_pos hc₀ hc₁ _ hjm0)
    · obtain ⟨-, h1⟩ := ref_closed c₀ c₁ (A 0) j
      rw [hV, hW, hj, h1]
      exact mul_pos (nsq_npow_pos hc₀ hc₁ _ hjm0) (nsq_npow_pos hc₀ hc₁ _ hu0)
  have hden : 0 < (c₀ ^ (2 * K + 1) + c₁ ^ (2 * K + 1)) ^ 2 := by positivity
  have hineq : amp c₀ c₁ V W ^ 2 * (c₀ ^ (2 * K + 1) + c₁ ^ (2 * K + 1)) ^ 2 ≤
      c₀ ^ 2 * c₁ ^ 2 * (c₀ ^ (2 * K) - c₁ ^ (2 * K)) ^ 2 * (nsq V * nsq W) := by
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' K
    · obtain ⟨h1, -⟩ := ref_closed c₀ c₁ (A 0) j
      have hV' : V = npow c₀ c₁ K (A 0) := by rw [hV, hj, h1]
      have hW' : W = npow c₀ c₁ K (jm c₀ c₁ (A 0)) := by rw [hW, hj, h1]
      exact hcore V W hV' hW'
    · obtain ⟨-, h1⟩ := ref_closed c₀ c₁ (A 0) j
      have hV' : V = npow c₀ c₁ K (jm c₀ c₁ (A 0)) := by rw [hV, hj, h1]
      have hW' : W = npow c₀ c₁ K (A 0) := by rw [hW, hj, h1]
      have := hcore W V hW' hV'
      rw [amp_comm, mul_comm (nsq V)]
      exact this
  unfold ladderValue'
  rw [le_div_iff₀ hden]
  rw [← hmain] at hineq
  -- cancel the positive factor nsq V * nsq W
  have := le_of_mul_le_mul_right (a := nsq V * nsq W) (by linarith [hineq] :
    amp c₀ c₁ (A K) (B K) ^ 2 * (c₀ ^ (2 * K + 1) + c₁ ^ (2 * K + 1)) ^ 2 * (nsq V * nsq W) ≤
      c₀ ^ 2 * c₁ ^ 2 * (c₀ ^ (2 * K) - c₁ ^ (2 * K)) ^ 2 * (nsq V * nsq W)) hVWpos
  exact this

/-! ### The angle form -/

/-- **The closed-form bound** (Hardy / Boschi–Branca–De Martini–Hardy ladder, two qubits, real
settings).
For `c₀, c₁ > 0` with `c₀² + c₁² = 1` and measurement angles `a b : ℕ → ℝ` satisfying the `K`-step
ladder constraints, `P(A_K = 1, B_K = 1) ≤ P_K*(c₁/c₀)`. -/
theorem ladder_prob_le (K : ℕ) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * Real.cos (a 0) * Real.cos (b 0) + c₁ * Real.sin (a 0) * Real.sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < K, (c₀ * Real.cos (a (k + 1)) * (-Real.sin (b k)) +
      c₁ * Real.sin (a (k + 1)) * Real.cos (b k)) ^ 2 = 0)
    (hB : ∀ k < K, (c₀ * (-Real.sin (a k)) * Real.cos (b (k + 1)) +
      c₁ * Real.cos (a k) * Real.sin (b (k + 1))) ^ 2 = 0) :
    (c₀ * Real.cos (a K) * Real.cos (b K) + c₁ * Real.sin (a K) * Real.sin (b K)) ^ 2 ≤
      ladderValue K (c₁ / c₀) := by
  rw [ladderValue_eq_ladderValue' K hc₀ hc₁ hnorm]
  let A : ℕ → ℝ × ℝ := fun k => (Real.cos (a k), Real.sin (a k))
  let B : ℕ → ℝ × ℝ := fun k => (Real.cos (b k), Real.sin (b k))
  have hAu : ∀ k, nsq (A k) = 1 := fun k => by simp [nsq, A, Real.cos_sq_add_sin_sq]
  have hBu : ∀ k, nsq (B k) = 1 := fun k => by simp [nsq, B, Real.cos_sq_add_sin_sq]
  have h0' : cross (B 0) (jm c₀ c₁ (A 0)) = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h₀
    simp only [cross, jm, A, B]
    linear_combination this
  have hAB' : ∀ k < K, cross (A (k + 1)) (nmap c₀ c₁ (B k)) = 0 := by
    intro k hk
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (hA k hk)
    simp only [cross, nmap, A, B]
    linear_combination -this
  have hBA' : ∀ k < K, cross (B (k + 1)) (nmap c₀ c₁ (A k)) = 0 := by
    intro k hk
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (hB k hk)
    simp only [cross, nmap, A, B]
    linear_combination -this
  have := amp_sq_le_ladderValue' hc₀ hc₁ A B hAu hBu K h0' hAB' hBA'
  simpa [amp, A, B] using this

/-! ### Attainment -/

/-- The tangent chain: `T 0 = (q^{-1/2}, −q^{-1/2})`, `T (k+1) = ((T k).2 / q, (T k).1 / q)`. -/
noncomputable def tchain (q : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1 / Real.sqrt q, -(1 / Real.sqrt q))
  | k + 1 => ((tchain q k).2 / q, (tchain q k).1 / q)

theorem tchain_invariants {q : ℝ} (hq : 0 < q) (k : ℕ) :
    (tchain q k).1 * (tchain q k).2 = -(1 / q ^ (2 * k + 1)) ∧
    (tchain q k).1 ^ 2 = 1 / q ^ (2 * k + 1) ∧ (tchain q k).2 ^ 2 = 1 / q ^ (2 * k + 1) := by
  induction k with
  | zero =>
    have hs : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.le
    simp only [tchain, Nat.mul_zero, Nat.zero_add, pow_one]
    refine ⟨?_, ?_, ?_⟩
    · rw [show (1 / Real.sqrt q) * (-(1 / Real.sqrt q)) = -(1 / (Real.sqrt q * Real.sqrt q)) by
        ring, hs]
    · rw [show (1 / Real.sqrt q) ^ 2 = 1 / (Real.sqrt q * Real.sqrt q) by ring, hs]
    · rw [show (-(1 / Real.sqrt q)) ^ 2 = 1 / (Real.sqrt q * Real.sqrt q) by ring, hs]
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hq0 : q ≠ 0 := hq.ne'
    have e : q ^ (2 * (k + 1) + 1) = q ^ (2 * k + 1) * q ^ 2 := by ring
    simp only [tchain]
    rw [e]
    refine ⟨?_, ?_, ?_⟩
    · calc (tchain q k).2 / q * ((tchain q k).1 / q)
          = ((tchain q k).1 * (tchain q k).2) / q ^ 2 := by ring
        _ = -(1 / q ^ (2 * k + 1)) / q ^ 2 := by rw [h1]
        _ = -(1 / (q ^ (2 * k + 1) * q ^ 2)) := by ring
    · calc ((tchain q k).2 / q) ^ 2 = (tchain q k).2 ^ 2 / q ^ 2 := by ring
        _ = 1 / q ^ (2 * k + 1) / q ^ 2 := by rw [h3]
        _ = 1 / (q ^ (2 * k + 1) * q ^ 2) := by ring
    · calc ((tchain q k).1 / q) ^ 2 = (tchain q k).1 ^ 2 / q ^ 2 := by ring
        _ = 1 / q ^ (2 * k + 1) / q ^ 2 := by rw [h2]
        _ = 1 / (q ^ (2 * k + 1) * q ^ 2) := by ring

/-- The joint amplitude of two `arctan` directions factors: `c₀ cos cos + c₁ sin sin =
cos cos (c₀ + c₁ s t)`. -/
theorem amp_arctan (c₀ c₁ s t : ℝ) :
    c₀ * Real.cos (Real.arctan s) * Real.cos (Real.arctan t) +
        c₁ * Real.sin (Real.arctan s) * Real.sin (Real.arctan t) =
      Real.cos (Real.arctan s) * Real.cos (Real.arctan t) * (c₀ + c₁ * (s * t)) := by
  rw [Real.sin_arctan, Real.sin_arctan, Real.cos_arctan, Real.cos_arctan]
  ring

theorem amp_arctan_A (c₀ c₁ s t : ℝ) :
    c₀ * Real.cos (Real.arctan s) * (-Real.sin (Real.arctan t)) +
        c₁ * Real.sin (Real.arctan s) * Real.cos (Real.arctan t) =
      Real.cos (Real.arctan s) * Real.cos (Real.arctan t) * (-(c₀ * t) + c₁ * s) := by
  rw [Real.sin_arctan, Real.sin_arctan, Real.cos_arctan, Real.cos_arctan]
  ring

theorem amp_arctan_B (c₀ c₁ s t : ℝ) :
    c₀ * (-Real.sin (Real.arctan s)) * Real.cos (Real.arctan t) +
        c₁ * Real.cos (Real.arctan s) * Real.sin (Real.arctan t) =
      Real.cos (Real.arctan s) * Real.cos (Real.arctan t) * (-(c₀ * s) + c₁ * t) := by
  rw [Real.sin_arctan, Real.sin_arctan, Real.cos_arctan, Real.cos_arctan]
  ring

/-- **The bound is attained.** For every `K` and every normalised `c₀, c₁ > 0` there are
measurement angles satisfying the `K`-step ladder constraints with
`P(A_K = 1, B_K = 1) = P_K*(c₁/c₀)`: the chain `tan a₀ = q^{-1/2}`, `tan b₀ = −q^{-1/2}`,
`tan aₖ₊₁ = tan bₖ / q`, `tan bₖ₊₁ = tan aₖ / q`. -/
theorem ladder_prob_attained (K : ℕ) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) :
    ∃ a b : ℕ → ℝ,
      (c₀ * Real.cos (a 0) * Real.cos (b 0) + c₁ * Real.sin (a 0) * Real.sin (b 0)) ^ 2 = 0 ∧
      (∀ k < K, (c₀ * Real.cos (a (k + 1)) * (-Real.sin (b k)) +
        c₁ * Real.sin (a (k + 1)) * Real.cos (b k)) ^ 2 = 0) ∧
      (∀ k < K, (c₀ * (-Real.sin (a k)) * Real.cos (b (k + 1)) +
        c₁ * Real.cos (a k) * Real.sin (b (k + 1))) ^ 2 = 0) ∧
      (c₀ * Real.cos (a K) * Real.cos (b K) + c₁ * Real.sin (a K) * Real.sin (b K)) ^ 2 =
        ladderValue K (c₁ / c₀) := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = c₁ / c₀ := ⟨_, rfl⟩
  have hqpos : 0 < q := hq ▸ div_pos hc₁ hc₀
  have hq0 : q ≠ 0 := hqpos.ne'
  have hc₁q : c₁ = q * c₀ := by rw [hq]; field_simp
  have hq2 : c₀ ^ 2 * (1 + q ^ 2) = 1 := by rw [hc₁q] at hnorm; linear_combination hnorm
  rw [← hq]
  subst hc₁q
  refine ⟨fun k => Real.arctan (tchain q k).1, fun k => Real.arctan (tchain q k).2,
    ?_, ?_, ?_, ?_⟩
  · -- P(A₀ = 1, B₀ = 1) = 0 : tan a₀ tan b₀ = −1/q
    beta_reduce
    rw [amp_arctan]
    have h := (tchain_invariants hqpos 0).1
    simp only [Nat.mul_zero, Nat.zero_add, pow_one] at h
    rw [h]
    have : c₀ + q * c₀ * -(1 / q) = 0 := by
      calc c₀ + q * c₀ * -(1 / q) = c₀ - c₀ * (q / q) := by ring
        _ = 0 := by rw [div_self hq0]; ring
    rw [this]; ring
  · -- P(Aₖ₊₁ = 1, Bₖ = 0) = 0 : tan aₖ₊₁ = tan bₖ / q
    intro k _
    beta_reduce
    rw [amp_arctan_A]
    have : -(c₀ * (tchain q k).2) + q * c₀ * (tchain q (k + 1)).1 = 0 := by
      simp only [tchain]; field_simp; ring
    rw [this]; ring
  · -- P(Aₖ = 0, Bₖ₊₁ = 1) = 0 : tan bₖ₊₁ = tan aₖ / q
    intro k _
    beta_reduce
    rw [amp_arctan_B]
    have : -(c₀ * (tchain q k).1) + q * c₀ * (tchain q (k + 1)).2 = 0 := by
      simp only [tchain]; field_simp; ring
    rw [this]; ring
  · -- the value
    beta_reduce
    rw [amp_arctan]
    obtain ⟨h1, h2, h3⟩ := tchain_invariants hqpos K
    rw [mul_pow, mul_pow, Real.cos_sq_arctan, Real.cos_sq_arctan, h1, h2, h3]
    have hm : 0 < q ^ (2 * K + 1) := pow_pos hqpos _
    have hm0 : q ^ (2 * K + 1) ≠ 0 := hm.ne'
    have hn : q ^ (2 * K + 1) = q ^ (2 * K) * q := pow_succ q (2 * K)
    have hc₀sq : c₀ ^ 2 = 1 / (1 + q ^ 2) := by
      rw [eq_div_iff (by positivity)]; exact hq2
    unfold ladderValue
    have h1m : 1 + 1 / q ^ (2 * K + 1) ≠ 0 := by positivity
    have step1 : 1 / (1 + 1 / q ^ (2 * K + 1)) * (1 / (1 + 1 / q ^ (2 * K + 1))) *
        (c₀ + q * c₀ * -(1 / q ^ (2 * K + 1))) ^ 2 =
        c₀ ^ 2 * (q ^ (2 * K + 1) - q) ^ 2 / (q ^ (2 * K + 1) + 1) ^ 2 := by
      field_simp
      ring
    rw [step1, hc₀sq, hn]
    have hn0 : q ^ (2 * K) ≠ 0 := pow_ne_zero _ hq0
    field_simp
    ring

end HardyLadder
