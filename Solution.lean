module

public import Mathlib
public import HardyLadder

@[expose] public section

/-!
# Proofs of the statements in `Challenge.lean`

Each theorem below has exactly the statement of its counterpart in `Challenge.lean` and is proved
by the corresponding theorem of the library `HardyLadder`:

* statements 1–2 (the closed form and its attainment, every `K`): `HardyLadder.ladder_prob_le`,
  `HardyLadder.ladder_prob_attained` (`HardyLadder/Ladder.lean`), stated there with the
  abbreviation `HardyLadder.ladderValue K q`, which unfolds to the written-out formula;
* statements 3–4 (every `K`, below one half, and one half approached): `ladder_prob_lt_half`,
  `ladder_prob_approaches_half` (`HardyLadder/OneHalf.lean`);
* statements 5–11 (every `K`, the maximiser and the optimum): `hasDerivAt_ladderValue`,
  `existsUnique_cerecedaM_root`, `ladderValue_isGreatest_of_root`, `eq_of_ladderValue_eq_of_root`,
  `ladder_prob_le_of_root`, `ladder_prob_attained_of_ratio`, `ratio_of_ladder_prob_eq_of_root`
  (`HardyLadder/Maximiser.lean`), stated there with `ladderValue K q` and Cereceda's polynomial
  `HardyLadder.cerecedaM K x`, which unfold to the written-out formulas;
* statements 12–18 (`K = 1`): `hardy_K1_isGreatest`, `goldenRatio_inv_pow_five`,
  `hardy_K1_eq_iff_quartic`, `hardy_K1_existsUnique` (`HardyLadder/HardyK1.lean`,
  `HardyLadder/Golden.lean`), and `ladder_K1_le`, `ladder_K1_attained`,
  `ladder_K1_hardy_condition_of_eq` (`HardyLadder/Optimum.lean`, stated there with the same text
  as here);
* statements 19–26 (`K = 2`): `existsUnique_cubic` (`HardyLadder/Plastic.lean`),
  `hardy_K2_isGreatest`, `hardy_K2_eq_iff_inv_sq`, `hardy_K2_eq_iff_cubic`,
  `hardy_K2_existsUnique` (`HardyLadder/HardyK2.lean`), and `ladder_K2_le`, `ladder_K2_attained`,
  `ladder_K2_weights_of_eq` (`HardyLadder/Optimum.lean`, stated there with the same text as here);
* statements 27–29 (the arithmetic of the value): `minpoly_value`, `finrank_adjoin_value`,
  `irreducible_25` (`HardyLadder/Minpoly.lean`);
* statement 30 (the value is not totally real): `exists_nonreal_root_minpoly_value`
  (`HardyLadder/TotallyReal.lean`).
-/

namespace HardyLadder.Entry

open Real Polynomial

theorem ladder_prob_le (K : ℕ) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) :
    (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 ≤
      (c₁ / c₀) ^ 2 * (1 - (c₁ / c₀) ^ (2 * K)) ^ 2 /
        ((1 + (c₁ / c₀) ^ 2) * (1 + (c₁ / c₀) ^ (2 * K + 1)) ^ 2) :=
  HardyLadder.ladder_prob_le K hc₀ hc₁ hnorm a b h₀ hA hB

theorem ladder_prob_attained (K : ℕ) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) :
    ∃ a b : ℕ → ℝ,
      (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0 ∧
      (∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
        c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0) ∧
      (∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
        c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) ∧
      (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 =
        (c₁ / c₀) ^ 2 * (1 - (c₁ / c₀) ^ (2 * K)) ^ 2 /
          ((1 + (c₁ / c₀) ^ 2) * (1 + (c₁ / c₀) ^ (2 * K + 1)) ^ 2) :=
  HardyLadder.ladder_prob_attained K hc₀ hc₁ hnorm

theorem ladder_prob_lt_half (K : ℕ) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) :
    (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 < 1 / 2 :=
  HardyLadder.ladder_prob_lt_half K hc₀ hc₁ hnorm a b h₀ hA hB

theorem ladder_prob_approaches_half {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ c₀ ^ 2 + c₁ ^ 2 = 1 ∧
      ∃ a b : ℕ → ℝ,
        (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0 ∧
        (∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
          c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0) ∧
        (∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
          c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) ∧
        1 / 2 - ε < (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 :=
  HardyLadder.ladder_prob_approaches_half hε

theorem hasDerivAt_ladder_value (K : ℕ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt
      (fun x : ℝ => x ^ 2 * (1 - x ^ (2 * K)) ^ 2 / ((1 + x ^ 2) * (1 + x ^ (2 * K + 1)) ^ 2))
      (2 * q * (1 - q ^ (2 * K)) *
          (q ^ (4 * K + 3) - (1 + 2 * K) * q ^ (2 * K + 3) - 2 * K * q ^ (2 * K + 2) -
            2 * K * q ^ (2 * K + 1) - (1 + 2 * K) * q ^ (2 * K) + 1) /
        ((1 + q ^ 2) ^ 2 * (1 + q ^ (2 * K + 1)) ^ 3)) q :=
  HardyLadder.hasDerivAt_ladderValue K hq

theorem existsUnique_mK_root (K : ℕ) (hK : 1 ≤ K) :
    ∃! r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 ∧
      r ^ (4 * K + 3) - (1 + 2 * K) * r ^ (2 * K + 3) - 2 * K * r ^ (2 * K + 2) -
        2 * K * r ^ (2 * K + 1) - (1 + 2 * K) * r ^ (2 * K) + 1 = 0 :=
  HardyLadder.existsUnique_cerecedaM_root K hK

theorem ladder_value_isGreatest_of_mK_root (K : ℕ) (hK : 1 ≤ K) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hm : r ^ (4 * K + 3) - (1 + 2 * K) * r ^ (2 * K + 3) - 2 * K * r ^ (2 * K + 2) -
      2 * K * r ^ (2 * K + 1) - (1 + 2 * K) * r ^ (2 * K) + 1 = 0) :
    IsGreatest ((fun q : ℝ => q ^ 2 * (1 - q ^ (2 * K)) ^ 2 /
        ((1 + q ^ 2) * (1 + q ^ (2 * K + 1)) ^ 2)) '' Set.Ioo 0 1)
      (r ^ 2 * (1 - r ^ (2 * K)) ^ 2 / ((1 + r ^ 2) * (1 + r ^ (2 * K + 1)) ^ 2)) :=
  HardyLadder.ladderValue_isGreatest_of_root K hK hr hm

theorem eq_of_ladder_value_eq_of_mK_root (K : ℕ) (hK : 1 ≤ K) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hm : r ^ (4 * K + 3) - (1 + 2 * K) * r ^ (2 * K + 3) - 2 * K * r ^ (2 * K + 2) -
      2 * K * r ^ (2 * K + 1) - (1 + 2 * K) * r ^ (2 * K) + 1 = 0)
    {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (heq : q ^ 2 * (1 - q ^ (2 * K)) ^ 2 / ((1 + q ^ 2) * (1 + q ^ (2 * K + 1)) ^ 2) =
      r ^ 2 * (1 - r ^ (2 * K)) ^ 2 / ((1 + r ^ 2) * (1 + r ^ (2 * K + 1)) ^ 2)) :
    q = r :=
  HardyLadder.eq_of_ladderValue_eq_of_root K hK hr hm hq heq

theorem ladder_prob_le_of_mK_root (K : ℕ) (hK : 1 ≤ K) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hm : r ^ (4 * K + 3) - (1 + 2 * K) * r ^ (2 * K + 3) - 2 * K * r ^ (2 * K + 2) -
      2 * K * r ^ (2 * K + 1) - (1 + 2 * K) * r ^ (2 * K) + 1 = 0)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) :
    (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 ≤
      r ^ 2 * (1 - r ^ (2 * K)) ^ 2 / ((1 + r ^ 2) * (1 + r ^ (2 * K + 1)) ^ 2) :=
  HardyLadder.ladder_prob_le_of_root K hK hr hm hc₀ hc₁ hnorm a b h₀ hA hB

theorem ladder_prob_attained_of_ratio (K : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ c₀ ^ 2 + c₁ ^ 2 = 1 ∧ c₁ / c₀ = r ∧
      ∃ a b : ℕ → ℝ,
        (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0 ∧
        (∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
          c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0) ∧
        (∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
          c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) ∧
        (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 =
          r ^ 2 * (1 - r ^ (2 * K)) ^ 2 / ((1 + r ^ 2) * (1 + r ^ (2 * K + 1)) ^ 2) :=
  HardyLadder.ladder_prob_attained_of_ratio K hr

theorem ratio_of_ladder_prob_eq_of_mK_root (K : ℕ) (hK : 1 ≤ K) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hm : r ^ (4 * K + 3) - (1 + 2 * K) * r ^ (2 * K + 3) - 2 * K * r ^ (2 * K + 2) -
      2 * K * r ^ (2 * K + 1) - (1 + 2 * K) * r ^ (2 * K) + 1 = 0)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < K, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < K, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0)
    (hopt : (c₀ * cos (a K) * cos (b K) + c₁ * sin (a K) * sin (b K)) ^ 2 =
      r ^ 2 * (1 - r ^ (2 * K)) ^ 2 / ((1 + r ^ 2) * (1 + r ^ (2 * K + 1)) ^ 2)) :
    c₁ / c₀ = r ∨ c₁ / c₀ = r⁻¹ :=
  HardyLadder.ratio_of_ladder_prob_eq_of_root K hK hr hm hc₀ hc₁ hnorm a b h₀ hA hB hopt

theorem hardy_K1_isGreatest :
    IsGreatest ((fun q : ℝ => q ^ 2 * (1 - q ^ 2) ^ 2 / ((1 + q ^ 2) * (1 + q ^ 3) ^ 2)) ''
      Set.Ioo 0 1) (goldenRatio⁻¹ ^ 5) :=
  HardyLadder.hardy_K1_isGreatest

theorem hardy_value_eq : goldenRatio⁻¹ ^ 5 = (5 * √5 - 11) / 2 :=
  HardyLadder.goldenRatio_inv_pow_five

theorem hardy_K1_eq_iff_quartic {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    q ^ 2 * (1 - q ^ 2) ^ 2 / ((1 + q ^ 2) * (1 + q ^ 3) ^ 2) = goldenRatio⁻¹ ^ 5 ↔
      q ^ 4 - 3 * q ^ 3 + 3 * q ^ 2 - 3 * q + 1 = 0 :=
  HardyLadder.hardy_K1_eq_iff_quartic hq0 hq1

theorem hardy_K1_existsUnique :
    ∃! q : ℝ, q ∈ Set.Ioo (0 : ℝ) 1 ∧
      q ^ 2 * (1 - q ^ 2) ^ 2 / ((1 + q ^ 2) * (1 + q ^ 3) ^ 2) = goldenRatio⁻¹ ^ 5 :=
  HardyLadder.hardy_K1_existsUnique

theorem ladder_K1_le {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < 1, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < 1, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) :
    (c₀ * cos (a 1) * cos (b 1) + c₁ * sin (a 1) * sin (b 1)) ^ 2 ≤ goldenRatio⁻¹ ^ 5 :=
  HardyLadder.ladder_K1_le hc₀ hc₁ hnorm a b h₀ hA hB

theorem ladder_K1_attained :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ c₀ ^ 2 + c₁ ^ 2 = 1 ∧ 2 * c₀ * c₁ = 3 - √5 ∧
      ∃ a b : ℕ → ℝ,
        (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0 ∧
        (∀ k < 1, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
          c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0) ∧
        (∀ k < 1, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
          c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) ∧
        (c₀ * cos (a 1) * cos (b 1) + c₁ * sin (a 1) * sin (b 1)) ^ 2 = goldenRatio⁻¹ ^ 5 :=
  HardyLadder.ladder_K1_attained

theorem ladder_K1_hardy_condition_of_eq {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < 1, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < 1, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0)
    (hopt : (c₀ * cos (a 1) * cos (b 1) + c₁ * sin (a 1) * sin (b 1)) ^ 2 =
      goldenRatio⁻¹ ^ 5) :
    2 * c₀ * c₁ = 3 - √5 :=
  HardyLadder.ladder_K1_hardy_condition_of_eq hc₀ hc₁ hnorm a b h₀ hA hB hopt

theorem existsUnique_cubic : ∃! ρ : ℝ, ρ ^ 3 = ρ + 1 :=
  HardyLadder.existsUnique_cubic

theorem hardy_K2_isGreatest {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    IsGreatest ((fun q : ℝ => q ^ 2 * (1 - q ^ 4) ^ 2 / ((1 + q ^ 2) * (1 + q ^ 5) ^ 2)) ''
      Set.Ioo 0 1) ((8 * ρ ^ 2 + ρ - 11) / 25) :=
  HardyLadder.hardy_K2_isGreatest hρ

theorem hardy_K2_eq_iff_inv_sq {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    q ^ 2 * (1 - q ^ 4) ^ 2 / ((1 + q ^ 2) * (1 + q ^ 5) ^ 2) = (8 * ρ ^ 2 + ρ - 11) / 25 ↔
      q = ρ⁻¹ ^ 2 :=
  HardyLadder.hardy_K2_eq_iff_inv_sq hρ hq0 hq1

theorem hardy_K2_eq_iff_cubic {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    q ^ 2 * (1 - q ^ 4) ^ 2 / ((1 + q ^ 2) * (1 + q ^ 5) ^ 2) = (8 * ρ ^ 2 + ρ - 11) / 25 ↔
      q ^ 3 - q ^ 2 + 2 * q - 1 = 0 :=
  HardyLadder.hardy_K2_eq_iff_cubic hρ hq0 hq1

theorem hardy_K2_existsUnique {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    ∃! q : ℝ, q ∈ Set.Ioo (0 : ℝ) 1 ∧
      q ^ 2 * (1 - q ^ 4) ^ 2 / ((1 + q ^ 2) * (1 + q ^ 5) ^ 2) = (8 * ρ ^ 2 + ρ - 11) / 25 :=
  HardyLadder.hardy_K2_existsUnique hρ

theorem ladder_K2_le {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < 2, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < 2, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) :
    (c₀ * cos (a 2) * cos (b 2) + c₁ * sin (a 2) * sin (b 2)) ^ 2 ≤
      (8 * ρ ^ 2 + ρ - 11) / 25 :=
  HardyLadder.ladder_K2_le hρ hc₀ hc₁ hnorm a b h₀ hA hB

theorem ladder_K2_attained {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ c₀ ^ 2 + c₁ ^ 2 = 1 ∧ c₀ ^ 2 = ρ⁻¹ ∧ c₁ ^ 2 = ρ⁻¹ ^ 5 ∧
      ∃ a b : ℕ → ℝ,
        (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0 ∧
        (∀ k < 2, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
          c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0) ∧
        (∀ k < 2, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
          c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0) ∧
        (c₀ * cos (a 2) * cos (b 2) + c₁ * sin (a 2) * sin (b 2)) ^ 2 =
          (8 * ρ ^ 2 + ρ - 11) / 25 :=
  HardyLadder.ladder_K2_attained hρ

theorem ladder_K2_weights_of_eq {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hnorm : c₀ ^ 2 + c₁ ^ 2 = 1) (a b : ℕ → ℝ)
    (h₀ : (c₀ * cos (a 0) * cos (b 0) + c₁ * sin (a 0) * sin (b 0)) ^ 2 = 0)
    (hA : ∀ k < 2, (c₀ * cos (a (k + 1)) * (-sin (b k)) +
      c₁ * sin (a (k + 1)) * cos (b k)) ^ 2 = 0)
    (hB : ∀ k < 2, (c₀ * (-sin (a k)) * cos (b (k + 1)) +
      c₁ * cos (a k) * sin (b (k + 1))) ^ 2 = 0)
    (hopt : (c₀ * cos (a 2) * cos (b 2) + c₁ * sin (a 2) * sin (b 2)) ^ 2 =
      (8 * ρ ^ 2 + ρ - 11) / 25) :
    (c₀ ^ 2 = ρ⁻¹ ∧ c₁ ^ 2 = ρ⁻¹ ^ 5) ∨ (c₀ ^ 2 = ρ⁻¹ ^ 5 ∧ c₁ ^ 2 = ρ⁻¹) :=
  HardyLadder.ladder_K2_weights_of_eq hρ hc₀ hc₁ hnorm a b h₀ hA hB hopt

theorem minpoly_value {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    minpoly ℚ ((8 * ρ ^ 2 + ρ - 11) / 25) =
      X ^ 3 + C (17 / 25 : ℚ) * X ^ 2 + C (2 / 25 : ℚ) * X - C (1 / 25 : ℚ) :=
  HardyLadder.minpoly_value hρ

theorem finrank_adjoin_value {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {(8 * ρ ^ 2 + ρ - 11) / 25}) = 3 :=
  HardyLadder.finrank_adjoin_value hρ

theorem irreducible_25 {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    Irreducible (25 * X ^ 3 + 17 * X ^ 2 + 2 * X - 1 : ℚ[X]) :=
  HardyLadder.irreducible_25 hρ

theorem exists_nonreal_root_minpoly_value {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    ∃ z : ℂ, z.im ≠ 0 ∧ aeval z (minpoly ℚ ((8 * ρ ^ 2 + ρ - 11) / 25)) = 0 :=
  HardyLadder.exists_nonreal_root_minpoly_value hρ

end HardyLadder.Entry

/-! ### Axiom audit of the compared theorems (printed on every build) -/

#print axioms HardyLadder.Entry.ladder_prob_le
#print axioms HardyLadder.Entry.ladder_prob_attained
#print axioms HardyLadder.Entry.ladder_prob_lt_half
#print axioms HardyLadder.Entry.ladder_prob_approaches_half
#print axioms HardyLadder.Entry.hasDerivAt_ladder_value
#print axioms HardyLadder.Entry.existsUnique_mK_root
#print axioms HardyLadder.Entry.ladder_value_isGreatest_of_mK_root
#print axioms HardyLadder.Entry.eq_of_ladder_value_eq_of_mK_root
#print axioms HardyLadder.Entry.ladder_prob_le_of_mK_root
#print axioms HardyLadder.Entry.ladder_prob_attained_of_ratio
#print axioms HardyLadder.Entry.ratio_of_ladder_prob_eq_of_mK_root
#print axioms HardyLadder.Entry.hardy_K1_isGreatest
#print axioms HardyLadder.Entry.hardy_value_eq
#print axioms HardyLadder.Entry.hardy_K1_eq_iff_quartic
#print axioms HardyLadder.Entry.hardy_K1_existsUnique
#print axioms HardyLadder.Entry.ladder_K1_le
#print axioms HardyLadder.Entry.ladder_K1_attained
#print axioms HardyLadder.Entry.ladder_K1_hardy_condition_of_eq
#print axioms HardyLadder.Entry.existsUnique_cubic
#print axioms HardyLadder.Entry.hardy_K2_isGreatest
#print axioms HardyLadder.Entry.hardy_K2_eq_iff_inv_sq
#print axioms HardyLadder.Entry.hardy_K2_eq_iff_cubic
#print axioms HardyLadder.Entry.hardy_K2_existsUnique
#print axioms HardyLadder.Entry.ladder_K2_le
#print axioms HardyLadder.Entry.ladder_K2_attained
#print axioms HardyLadder.Entry.ladder_K2_weights_of_eq
#print axioms HardyLadder.Entry.minpoly_value
#print axioms HardyLadder.Entry.finrank_adjoin_value
#print axioms HardyLadder.Entry.irreducible_25
#print axioms HardyLadder.Entry.exists_nonreal_root_minpoly_value
