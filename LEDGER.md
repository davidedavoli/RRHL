# Xhl artifact ledger

The following tables relate the paper's statements to their Lean formalization.

## The language

| Paper | Lean file | Lean name |
|---|---|---|
| The pwhile language (§4.1) | Xhl/Language/Syntax.lean | `Cmd`, `Expr`, `Vars`, `MemType` |
| Semantics of programs (Fig. 2) | Xhl/Language/Semantics.lean | `osemA`, `esem` |
| Observable semantics: transcripts and `release` (§4.1) | Xhl/Language/Semantics.lean | `osemA`, `St`, `Tr` |
| The semantics is sub-Markov (prose remark, §4.1) | Xhl/Language/SubMarkov.lean | `osemA_univ_le_one` |

## The divergence layer

| Paper | Lean file | Lean name |
|---|---|---|
| Hellinger integral, unweighted (§3.1) | Xhl/Divergence/HellingerIntegral.lean | `hellingerIntegral` |
| Definition 3.1 (Weighted Hellinger integral) | Xhl/Divergence/HellingerIntegral.lean | `weightedHellingerIntegral` |
| Theorem 3.2 (Dual characterization) | Xhl/Divergence/WeightedDual.lean | `weightedHellingerIntegral_eq_testSupW` |
| Theorem 3.3 (Composition) | Xhl/Divergence/ChainUncond.lean | `weightedHellingerIntegral_bind_le` |
| Mixture-of-bind algebra behind the subsampling studies | Xhl/Divergence/MixtureBind.lean | `hellingerIntegral_bind_le_const`, `add_bind'`, `smul_bind'` |
| Proposition 3.5 (Conversion) | Xhl/Divergence/Privacy.lean | `RenyiDP.epsilonDeltaDP` |

## Differential privacy, at the definition level

| Paper | Lean file | Lean name |
|---|---|---|
| Definition 2.1 ((ε,δ)-differential privacy) | Xhl/Divergence/Privacy.lean | `EpsilonDeltaDP` |
| Definition 3.4 (Rényi divergence) | Xhl/Divergence/Privacy.lean | `renyiDiv` |
| Definition 3.4 (Rényi differential privacy) | Xhl/Divergence/Privacy.lean | `RenyiDP` |
| Definition 3.6 (Individual Rényi differential privacy) | Xhl/Divergence/Privacy.lean | `IndivRenyiDP` |
| Lemma 3.7 (From individual to global RDP) | Xhl/Divergence/Privacy.lean | `IndivRenyiDP.renyiDP_iSup`, `IndivRenyiDP.renyiDP_of_le` |

## The logic

| Paper | Lean file | Lean name |
|---|---|---|
| Definition 4.1 (Validity) | Xhl/Logic/Rrhl/Rrhl.lean, Xhl/Divergence/TestVal.lean | `RRhl`, `testValC` |
| Proposition 4.2 (Weak duality) | Xhl/Logic/Rrhl/Duality.lean | `WRhl`, `rrhl_of_wrhl` |
| Theorem D.1 (Strong duality) | Xhl/Logic/Rrhl/Duality.lean | `wrhl_of_rrhl_polish`, `rrhl_iff_wrhl_polish` |
| Figure 3 (derived rules): the sampling rules | Xhl/Logic/Rrhl/Deriv.lean | `TDeriv.rnd`, `TDeriv.rndGap`, `TDeriv.rndFwdK` |
| Figure 3: [Local], derived | Xhl/Logic/Rrhl/Deriv.lean | `TDeriv.loc`, `TDeriv.locs` |
| Proposition 4.4 (Characterization of RDP) | Xhl/Logic/Rrhl/Readout.lean | `rrhl_renyiDP`, `rrhl_indivRenyiDP`, `rrhl_tr_hellingerIntegral_le` |
| Figure 3: the derivability relation | Xhl/Logic/Rrhl/Deriv.lean | `TDeriv` |
| Theorem 4.3 (Soundness) | Xhl/Logic/Rrhl/Deriv.lean | `TDeriv.sound` |
| Figures 8–9: the program equivalence calculus (Appendix C) | Xhl/Logic/Equiv/CEquiv.lean | `CEquiv`, `CEquiv.sound` |

## The case studies

| Paper | Lean file | Lean name |
|---|---|---|
| DP-SGD, transcript model (§5.1.1, eq. (4)) | Xhl/Examples/DPSGD/Transcript/Deriv.lean, Xhl/Examples/DPSGD/Transcript/DP.lean | `dpsgdTranscript_deriv`, `dpsgdTranscript_Hellinger`, `dpsgdTranscript_RDP` |
| DP-SGD, last iterate (§5.1.3, eq. (9)) | Xhl/Examples/DPSGD/LastIterate/Deriv.lean | `dpsgdLastIter_deriv` |
| Non-expansive update for convex, β-smooth, Γ-Lipschitz losses at η ≤ 2q/β (§5.1.3, first condition of eq. (8)) | Xhl/Examples/DPSGD/LastIterate/ATLoss.lean | `ATLoss`, `hstep_of_ATLoss` |
| DP-SGD, last iterate: the bound does not depend on `T` (§5.1.3, closing paragraph; Altschuler–Talwar eqs. (3.4)–(3.6)) | Xhl/Examples/DPSGD/LastIterate/Horizon.lean | `log_subDispBudget_pow`, `dpsgdLastIter_horizonFree_RDP` |
| Corollary E.3 ((ε,δ) guarantee) | Xhl/Examples/DPSGD/Transcript/DP.lean | `dpsgdTranscript_DP` |
| Proposition E.2 (Evaluating the per-round cost) | Xhl/Divergence/SubsamplingMixBudget.lean | `mixBudgetR_eq_phiForm`, `mixBudgetR_eq_erfcForm` |
| DP-FTRL, matrix mechanism (§5.3, eqs. (13)–(14)) | Xhl/Examples/DPFTRLMatrix/Deriv.lean, Xhl/Examples/DPFTRLMatrix/Potential.lean | `dpftrl_gen_deriv`, `dpftrl_IndivRDP` |
| DP-FTRL, multi-epoch participation (App. E.4, comparison with Choquette-Choo et al.) | Xhl/Examples/DPFTRLMatrix/Deriv.lean | `dpftrl_gen_multiEpoch_RDP` |
| DP-FTRL, tree aggregation (App. E.4, comparison with Kairouz et al.) | Xhl/Examples/DPFTRLMatrix/Deriv.lean | `dpftrl_gen_tree_RDP` |
| DP-FTRL, single participation (App. E.4, comparison with Denisov et al.) | Xhl/Examples/DPFTRLMatrix/Deriv.lean | `dpftrl_gen_denisov_RDP` |
| Proposition E.5 (encoder sensitivity), claim (1): single participation | Xhl/Examples/DPFTRLMatrix/Program.lean | `sum_relGap_sq_singleton` |
| Proposition E.5 (encoder sensitivity), claim (2): banded encoder | Xhl/Examples/DPFTRLMatrix/Program.lean | `sum_relGap_sq_banded` |
| Rényi filter (§5.2, eq. (10)) | Xhl/Examples/Filter/Deriv.lean | `filter_IndivRDP`, `filter_gen_IndivRDP` |
| Amplified banded DP-FTRL, one release per round (§E.5) | Xhl/Examples/DPFTRLBanded/DerivT.lean, Xhl/Examples/DPFTRLBanded/Instance.lean | `dpftrlBanded_gen_deriv`, `dpftrlBanded_uniform_IndivRDP` |
| Lemma E.1 (Mironov et al., Corollary 7): Λ_α ≤ Υ_α | Xhl/Divergence/SubsamplingDomination.lean | `mixFlipBudgetE_le_forward` |
| Υ_α, the subsampled-Gaussian budget (eq. (3), §5.1.1) | Xhl/Divergence/SubsamplingMixBudget.lean | `mixBudgetR` |
| App. E.2, eq. (22) (`eq:weak-triangle`): weak triangle inequality for Hellinger integrals | Xhl/Divergence/WeakTriangle.lean | `hellingerIntegral_le_sqrt_mul` |
| Proposition E.4 (Last iterate at replace-one adjacency), with Mironov et al.'s Theorem 11 | Xhl/Examples/DPSGD/LastIterate/Replace.lean, Xhl/Divergence/SubsamplingMironov.lean | `mixBudgetR_le_mironov`, `dpsgdLastIter_AT_replace`, `ReplF` |

