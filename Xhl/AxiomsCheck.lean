import Xhl.Logic.Equiv.CEquiv
import Xhl.Logic.Rrhl.Deriv
import Xhl.Logic.Rrhl.Readout
import Xhl.Logic.Rrhl.Duality
import Xhl.Divergence.WeightedDual
import Xhl.Divergence.Convert
import Xhl.Divergence.Privacy
import Xhl.Divergence.SubsamplingDomination
import Xhl.Divergence.WeakTriangle
import Xhl.Examples.DPSGD.Transcript.DP
import Xhl.Examples.DPSGD.Shared.Equiv.BlockCEquiv
import Xhl.Examples.DPSGD.LastIterate.Deriv
import Xhl.Examples.DPSGD.LastIterate.Horizon
import Xhl.Examples.DPSGD.LastIterate.Replace
import Xhl.Examples.DPSGD.LastIterate.ATLoss
import Xhl.Examples.DPFTRLMatrix.Deriv
import Xhl.Examples.Filter.Deriv
import Xhl.Examples.DPFTRLBanded.Instance

-- §3: the divergence layer and the mechanism-level DP notions
#print axioms Continuous.weightedHellingerIntegral_eq_testSupW
#print axioms Continuous.weightedHellingerIntegral_bind_le
#print axioms Continuous.hellingerIntegral_to_dp_balle
#print axioms Continuous.RenyiDP.epsilonDeltaDP
#print axioms Continuous.IndivRenyiDP.renyiDP_iSup
#print axioms Continuous.hellingerIntegral_map_le_uncond
-- §4: language, judgment, rules, soundness, readouts
#print axioms Continuous.osemA_univ_le_one
#print axioms Continuous.osemA_loc_eq_reset
#print axioms Continuous.rrhl_of_wrhl
#print axioms Continuous.TDeriv.loc
#print axioms Continuous.TDeriv.locs
#print axioms Continuous.TDeriv.rnd
#print axioms Continuous.TDeriv.rndGap
#print axioms Continuous.TDeriv.rndFwdK
#print axioms Continuous.tderiv_while_prod
#print axioms Continuous.TDeriv.sound
#print axioms Continuous.rrhl_tr_hellingerIntegral_le
#print axioms Continuous.rrhl_renyiDP
#print axioms Continuous.rrhl_indivRenyiDP
-- Appendix C: the equivalence calculus; Appendix D: strong duality
#print axioms Continuous.wrhl_of_rrhl_polish
#print axioms Continuous.rrhl_iff_wrhl_polish
#print axioms Continuous.CEquiv.sound
-- §5.1.1 and Appendix sec:details-dpsgd: DP-SGD, transcript model
#print axioms DPSGDPaper.cequiv_blockLoc_fusedLoc
#print axioms DPSGDPaper.dpsgdTranscript_deriv
#print axioms DPSGDPaper.dpsgdTranscript_Hellinger
#print axioms DPSGDPaper.dpsgdTranscript_IndivRDP
#print axioms DPSGDPaper.dpsgdTranscript_RDP
#print axioms DPSGDPaper.dpsgdTranscript_DP
#print axioms Continuous.mixFlipBudgetE_le_forward
#print axioms Continuous.hellingerIntegral_sgMixture_real_closedForm_unconditional
#print axioms Continuous.mixBudgetR_eq_phiForm
#print axioms Continuous.mixBudgetR_eq_erfcForm
-- §5.1.3 and Appendix sec:details-li: DP-SGD, last iterate
#print axioms DPSGDPaper.cequiv_blockLoc_splitLoc
#print axioms DPSGDPaper.dpsgdLastIter_deriv
#print axioms DPSGDPaper.dpsgdLastIter_Hellinger
#print axioms DPSGDPaper.dpsgdLastIter_full_deriv
#print axioms DPSGDPaper.dpsgdLastIter_full_Hellinger
#print axioms DPSGDPaper.log_subDispBudget_pow
#print axioms DPSGDPaper.exists_mul_add_div_le
#print axioms DPSGDPaper.dpsgdLastIter_horizonFree_Hellinger
#print axioms DPSGDPaper.dpsgdLastIter_horizonFree_IndivRDP
#print axioms DPSGDPaper.dpsgdLastIter_horizonFree_RDP
#print axioms Continuous.hellingerIntegral_le_sqrt_mul
#print axioms Continuous.mixBudgetR_le_mironov
#print axioms DPSGDPaper.dpsgdLastIter_AT_replace
#print axioms DPSGDPaper.hstep_of_ATLoss
-- §5.2: Rényi filter
#print axioms RenyiFilter.filter_gen_deriv
#print axioms RenyiFilter.filter_IndivRDP
-- §5.3 and Appendix sec:details-dpftrl: DP-FTRL, matrix mechanism
#print axioms DPFTRL.dpftrl_gen_deriv
#print axioms DPFTRL.dpftrl_gen_Hellinger
#print axioms DPFTRL.dpftrl_gen_IndivRDP
#print axioms DPFTRL.dpftrl_IndivRDP
#print axioms DPFTRL.sensW_eq_gaussB_sensSq
#print axioms DPFTRL.sensSq_le_relGap
#print axioms DPFTRL.sum_relGap_sq_singleton
#print axioms DPFTRL.sum_relGap_sq_banded
#print axioms DPFTRL.colNormSq_tree
#print axioms DPFTRL.dpftrl_gen_tree_RDP
#print axioms DPFTRL.dpftrl_gen_denisov_RDP
#print axioms DPFTRL.sensSq_eq_patNormSq
#print axioms DPFTRL.dpftrl_gen_multiEpoch_IndivRDP
#print axioms DPFTRL.dpftrl_gen_multiEpoch_RDP
-- Appendix sec:details-banded: amplified banded DP-FTRL
#print axioms DPFTRL.Band.cequiv_windowT_windowS_rules
#print axioms DPFTRL.Band.dpftrlBanded_Hellinger
#print axioms DPFTRL.Band.dpftrlBanded_IndivRDP
#print axioms DPFTRL.Band.dpftrlBanded_uniform_IndivRDP
