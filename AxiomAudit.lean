module

public import HardyLadder
public import Solution

/-! Axiom audit: every theorem must depend on at most {propext, Classical.choice, Quot.sound}.
Every theorem of the library comes first (160), module by module; the thirty compared
theorems of `Solution.lean` (namespace `HardyLadder.Entry`) are audited at the end. -/

open HardyLadder

-- Plastic (the real root of x³ − x − 1; existsUnique_cubic proves compared statement 19)
#print axioms HardyLadder.pos_of_cubic
#print axioms HardyLadder.one_lt_of_cubic
#print axioms HardyLadder.five_quarters_lt_of_cubic
#print axioms HardyLadder.lt_four_thirds_of_cubic
#print axioms HardyLadder.eq_of_cubic
#print axioms HardyLadder.exists_cubic
#print axioms HardyLadder.existsUnique_cubic
#print axioms HardyLadder.ne_zero_of_cubic
#print axioms HardyLadder.inv_eq_of_cubic
#print axioms HardyLadder.inv_sq_eq_of_cubic
#print axioms HardyLadder.inv_pow_five_eq_of_cubic
#print axioms HardyLadder.inv_add_inv_pow_five
#print axioms HardyLadder.pow_five_eq_of_cubic
#print axioms HardyLadder.inv_sq_mem_Ioo
-- Golden (φ; goldenRatio_inv_pow_five proves compared statement 13)
#print axioms HardyLadder.goldenRatio_pow_five
#print axioms HardyLadder.goldenRatio_inv_pow_five
#print axioms HardyLadder.goldenRatio_pow_four
#print axioms HardyLadder.goldenRatio_pow_five'
#print axioms HardyLadder.three_goldenRatio_sub_two_pos
#print axioms HardyLadder.qstar1_root
#print axioms HardyLadder.qstar1_pos
#print axioms HardyLadder.qstar1_lt_one
#print axioms HardyLadder.qstar1_mem_Ioo
-- Ladder (the closed form, every K; compared statements 1-2)
#print axioms HardyLadder.ladderValue_eq_aux
#print axioms HardyLadder.ladderValue_eq_ladderValue'
#print axioms HardyLadder.cross_self
#print axioms HardyLadder.amp_comm
#print axioms HardyLadder.cross_trans
#print axioms HardyLadder.cross_nmap
#print axioms HardyLadder.nmap_ne_zero
#print axioms HardyLadder.nmap_npow
#print axioms HardyLadder.npow_zero
#print axioms HardyLadder.ref_closed
#print axioms HardyLadder.chain
#print axioms HardyLadder.amp_sq_mul_eq
#print axioms HardyLadder.core_ineq
#print axioms HardyLadder.nsq_npow_pos
#print axioms HardyLadder.ne_zero_of_nsq_eq_one
#print axioms HardyLadder.jm_ne_zero
#print axioms HardyLadder.amp_sq_le_ladderValue'
#print axioms HardyLadder.ladder_prob_le
#print axioms HardyLadder.tchain_invariants
#print axioms HardyLadder.amp_arctan
#print axioms HardyLadder.amp_arctan_A
#print axioms HardyLadder.amp_arctan_B
#print axioms HardyLadder.ladder_prob_attained
-- HardyK1 (compared statements 12, 14, 15)
#print axioms HardyLadder.two_le_add_inv
#print axioms HardyLadder.two_lt_add_inv
#print axioms HardyLadder.ladderValue_one_eq
#print axioms HardyLadder.F1_le
#print axioms HardyLadder.F1_value
#print axioms HardyLadder.F1_eq_iff
#print axioms HardyLadder.qstar1_add_inv
#print axioms HardyLadder.hardy_K1_isGreatest
#print axioms HardyLadder.hardy_K1_eq_iff
#print axioms HardyLadder.quartic_factor
#print axioms HardyLadder.second_factor_pos
#print axioms HardyLadder.hardy_K1_eq_iff_quartic
#print axioms HardyLadder.hardy_K1_existsUnique
-- HardyK2 (compared statements 20-23; schmidt_weights is uncompared)
#print axioms HardyLadder.ladderValue_two_eq
#print axioms HardyLadder.value_pos
#print axioms HardyLadder.coeffB_pos
#print axioms HardyLadder.coeffC_pos
#print axioms HardyLadder.G_factor
#print axioms HardyLadder.F2_le
#print axioms HardyLadder.F2_eq_iff
#print axioms HardyLadder.inv_sq_add_inv
#print axioms HardyLadder.hardy_K2_isGreatest
#print axioms HardyLadder.hardy_K2_eq_iff
#print axioms HardyLadder.quadratic_factor
#print axioms HardyLadder.hardy_K2_eq_iff_inv_sq
#print axioms HardyLadder.hardy_K2_existsUnique
#print axioms HardyLadder.cubic_cofactor_factor
#print axioms HardyLadder.cofactor_quadratic_pos
#print axioms HardyLadder.hardy_K2_eq_iff_cubic
#print axioms HardyLadder.schmidt_weights
-- Minpoly (compared statements 27-29)
#print axioms HardyLadder.cubic_irred_zmod2
#print axioms HardyLadder.revZ_monic
#print axioms HardyLadder.revZ_map2
#print axioms HardyLadder.revZ_irred
#print axioms HardyLadder.revQ_irreducible
#print axioms HardyLadder.revQ_monic
#print axioms HardyLadder.revQ_natDegree
#print axioms HardyLadder.aeval_rev
#print axioms HardyLadder.isIntegral_rev
#print axioms HardyLadder.minpoly_rev
#print axioms HardyLadder.mQ_monic
#print axioms HardyLadder.mQ_natDegree
#print axioms HardyLadder.value_cubic
#print axioms HardyLadder.aeval_mQ
#print axioms HardyLadder.isIntegral_value
#print axioms HardyLadder.inv_value_rev
#print axioms HardyLadder.adjoin_eq_adjoin_inv
#print axioms HardyLadder.finrank_adjoin_value
#print axioms HardyLadder.minpoly_value
#print axioms HardyLadder.irreducible_25
-- TotallyReal (the cubic field has no totally real element outside ℚ, uncompared; the
-- K = 2 value has a non-real conjugate, compared statement 30)
#print axioms HardyLadder.plasticZ_monic
#print axioms HardyLadder.plasticZ_map2
#print axioms HardyLadder.plasticZ_irred
#print axioms HardyLadder.plasticQ_irreducible
#print axioms HardyLadder.plasticQ_monic
#print axioms HardyLadder.plasticQ_natDegree
#print axioms HardyLadder.aeval_plastic
#print axioms HardyLadder.minpoly_plastic
#print axioms HardyLadder.complex_root_eq_of_im_eq_zero
#print axioms HardyLadder.cubic_of_mem_rootSet
#print axioms HardyLadder.card_rootSet_plastic
#print axioms HardyLadder.exists_embedding_im_ne_zero
#print axioms HardyLadder.not_isTotallyReal_of_cubic
#print axioms HardyLadder.totallyReal_subfield_eq_bot
#print axioms HardyLadder.mem_bot_of_isTotallyReal_adjoin
#print axioms HardyLadder.pos_of_value_cubic
#print axioms HardyLadder.eq_of_value_cubic
#print axioms HardyLadder.value_cubic_re_of_root
#print axioms HardyLadder.exists_nonreal_root_minpoly_value
-- Optimum (the K = 1 and K = 2 optima over every real Schmidt state; the last six are the
-- library proofs of compared statements 16-18 and 24-26)
#print axioms HardyLadder.ladderValue_inv
#print axioms HardyLadder.ladderValue_at_one
#print axioms HardyLadder.ladderValue_one_le
#print axioms HardyLadder.ladderValue_two_le
#print axioms HardyLadder.two_mul_eq_of_ratio
#print axioms HardyLadder.weights_of_ratio
#print axioms HardyLadder.ladder_K1_le
#print axioms HardyLadder.ladder_K1_attained
#print axioms HardyLadder.ladder_K1_hardy_condition_of_eq
#print axioms HardyLadder.ladder_K2_le
#print axioms HardyLadder.ladder_K2_attained
#print axioms HardyLadder.ladder_K2_weights_of_eq
-- OneHalf (every K: below one half, and one half approached; compared statements 3-4)
#print axioms HardyLadder.ladderValue_lt_half_of_lt_one
#print axioms HardyLadder.ladderValue_lt_half
#print axioms HardyLadder.ladder_prob_lt_half
#print axioms HardyLadder.tendsto_ladderValue
#print axioms HardyLadder.exists_ratio_gt
#print axioms HardyLadder.exists_state_of_ratio
#print axioms HardyLadder.ladder_prob_approaches_half
-- Maximiser (every K >= 1: the unique maximiser, the zero of Cereceda's m_K in (0, 1), and
-- the optimum over every real Schmidt state; compared statements 5-11)
#print axioms HardyLadder.cerecedaM_eq
#print axioms HardyLadder.cerecedaM_one
#print axioms HardyLadder.cerecedaM_two
#print axioms HardyLadder.cerecedaM_zero
#print axioms HardyLadder.cerecedaM_at_one
#print axioms HardyLadder.hasDerivAt_ladderValue
#print axioms HardyLadder.hasDerivAt_gK
#print axioms HardyLadder.gK_deriv_pos
#print axioms HardyLadder.gK_pos
#print axioms HardyLadder.strictMonoOn_gK
#print axioms HardyLadder.strictMonoOn_pow_mul_gK
#print axioms HardyLadder.strictAntiOn_cerecedaM
#print axioms HardyLadder.exists_cerecedaM_root
#print axioms HardyLadder.existsUnique_cerecedaM_root
#print axioms HardyLadder.cerecedaM_pos_of_lt
#print axioms HardyLadder.cerecedaM_neg_of_gt
#print axioms HardyLadder.ladderValue_pos
#print axioms HardyLadder.strictMonoOn_ladderValue
#print axioms HardyLadder.strictAntiOn_ladderValue
#print axioms HardyLadder.ladderValue_le_of_root
#print axioms HardyLadder.ladderValue_isGreatest_of_root
#print axioms HardyLadder.eq_of_ladderValue_eq_of_root
#print axioms HardyLadder.ladderValue_le_of_root_of_pos
#print axioms HardyLadder.ladder_prob_le_of_root
#print axioms HardyLadder.ladder_prob_attained_of_ratio
#print axioms HardyLadder.ratio_of_ladder_prob_eq_of_root
-- Compared surface (Solution.lean, namespace HardyLadder.Entry)
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
