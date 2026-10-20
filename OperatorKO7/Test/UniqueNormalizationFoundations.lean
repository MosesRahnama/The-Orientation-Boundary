import OperatorKO7.Meta.UniqueNormalization.NormalizationCore
import OperatorKO7.Meta.UniqueNormalization.NormalizationDomains
import OperatorKO7.Meta.UniqueNormalization.NormalFormSaturation
import OperatorKO7.Meta.UniqueNormalization.NormalizerRealization
import OperatorKO7.Meta.UniqueNormalization.NormalizerForests
import OperatorKO7.Meta.UniqueNormalization.ConservativePolicies
import OperatorKO7.Meta.UniqueNormalization.NormalizerTransport
import OperatorKO7.Meta.UniqueNormalization.NormalizerTRS
import OperatorKO7.Meta.UniqueNormalization.NormalizationExamples

/-!
# Complete declaration and axiom check for the normalization foundation

The paired commands expose complete types and the axiom inventory of every
named public declaration in the dedicated foundation modules.
-/

set_option autoImplicit false
set_option pp.universes true
set_option pp.explicit true

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Star
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Star

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Conv
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Conv

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Subrel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Subrel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.NF
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.NF

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Normalizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Normalizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.WN
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.WN

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.UNR
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.UNR

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.UNC
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.UNC

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.CR
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.CR

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.NFP
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.NFP

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.SN
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.SN

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.star_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.star_mono

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.star_map
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.star_map

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conv_of_star
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conv_of_star

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conv_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conv_mono

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conv_map
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conv_map

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conv_of_join
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conv_of_join

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.nf_star_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.nf_star_eq

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.star_from_nf_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.star_from_nf_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normalizes_of_nf
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normalizes_of_nf

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normalizes_backward
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normalizes_backward

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.star_first
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.star_first

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.star_invariant
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.star_invariant

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conv_invariant
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conv_invariant

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.unr_of_unc
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.unr_of_unc

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.cr_of_wn_unr
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.cr_of_wn_unr

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.join_trans
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.join_trans

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.join_of_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.join_of_conv

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.unc_of_cr
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.unc_of_cr

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.nfp_of_cr
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.nfp_of_cr

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.cr_iff_unc_of_wn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.cr_iff_unc_of_wn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.cr_iff_unr_of_wn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.cr_iff_unr_of_wn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.acc_normalizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.acc_normalizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.wn_of_sn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.wn_of_sn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sn_subrel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sn_subrel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sn_irrefl
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sn_irrefl

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.empty_wn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.empty_wn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.empty_cr
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.empty_cr

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.empty_sn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.empty_sn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.cr_of_reachable_invariant
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.cr_of_reachable_invariant

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.idempotent_of_reachable_invariant
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.idempotent_of_reachable_invariant

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sn_no_two_cycle
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sn_no_two_cycle

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.ConvertsToNF
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.ConvertsToNF

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.HereditarilyNormalizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.HereditarilyNormalizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.NormalizingCarrier
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.NormalizingCarrier

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.NormalizingCore
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.NormalizingCore

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.ForwardInvariant
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.ForwardInvariant

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.CRAt
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.CRAt

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.ReflectsNormalizingConversion
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.ReflectsNormalizingConversion

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.core_star_lift
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.core_star_lift

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.core_star_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.core_star_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.core_conv_project
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.core_conv_project

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.core_nf_of_nf
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.core_nf_of_nf

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.core_wn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.core_wn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.core_nf_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.core_nf_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.core_unr_of_unr
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.core_unr_of_unr

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.unr_of_core_unr
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.unr_of_core_unr

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.unr_iff_core_cr
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.unr_iff_core_cr

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.NormalFormCarrier
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.NormalFormCarrier

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.chosenNF
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.chosenNF

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.chosenNF_reaches
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.chosenNF_reaches

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.chosenNF_unique
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.chosenNF_unique

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.chosenNF_step
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.chosenNF_step

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.chosenNF_eq_iff_core_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.chosenNF_eq_iff_core_conv

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.core_reflection_of_unc
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.core_reflection_of_unc

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.unc_iff_core_cr_and_reflection
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.unc_iff_core_cr_and_reflection

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.core_reflection_iff_unc
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.core_reflection_iff_unc

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.core_conv_iff_of_unc
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.core_conv_iff_of_unc

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.convertsToNF_of_normalizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.convertsToNF_of_normalizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.convertsToNF_of_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.convertsToNF_of_conv

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.convertsToNF_conv_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.convertsToNF_conv_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.hereditary_normalizes_self
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.hereditary_normalizes_self

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.hereditary_forward_star
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.hereditary_forward_star

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.hereditary_forward_invariant
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.hereditary_forward_invariant

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.forwardInvariant_star
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.forwardInvariant_star

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.hereditary_greatest
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.hereditary_greatest

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normalizes_conv_iff_of_forward_invariant
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normalizes_conv_iff_of_forward_invariant

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.hereditary_eq_normalizes_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.hereditary_eq_normalizes_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.hereditary_iff_normalizes_and_crAt
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.hereditary_iff_normalizes_and_crAt

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normalizes_eq_convertsToNF_of_nfp
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normalizes_eq_convertsToNF_of_nfp

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.nfp_iff_normalizes_eq_convertsToNF
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.nfp_iff_normalizes_eq_convertsToNF

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.nfp_iff_hereditary_eq_normalizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.nfp_iff_hereditary_eq_normalizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.nf_hereditarily_normalizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.nf_hereditarily_normalizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.ConvertibleCarrier
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.ConvertibleCarrier

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.ConvertibleRestriction
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.ConvertibleRestriction

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.classNF
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.classNF

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.classNF_converts
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.classNF_converts

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.classNF_unique
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.classNF_unique

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.classNF_eq_iff_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.classNF_eq_iff_conv

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.classNF_eq_self_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.classNF_eq_self_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.classLabel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.classLabel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.classLabel_eq_iff_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.classLabel_eq_iff_conv

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.classLabel_fixed_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.classLabel_fixed_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.classLabel_idempotent
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.classLabel_idempotent

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conversionSetoid
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conversionSetoid

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.ambientNormalSetoid
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.ambientNormalSetoid

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.CoreQuotient
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.CoreQuotient

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.AmbientNormalQuotient
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.AmbientNormalQuotient

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normalizingToConvertible
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normalizingToConvertible

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormToCoreQuotient
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormToCoreQuotient

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.coreToAmbientQuotient
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.coreToAmbientQuotient

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormToAmbientQuotient
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormToAmbientQuotient

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.quotient_maps_compose
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.quotient_maps_compose

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormToCoreQuotient_surjective
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormToCoreQuotient_surjective

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.coreToAmbientQuotient_surjective
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.coreToAmbientQuotient_surjective

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormToAmbientQuotient_surjective
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormToAmbientQuotient_surjective

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormToCoreQuotient_injective_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormToCoreQuotient_injective_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.coreToAmbientQuotient_injective_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.coreToAmbientQuotient_injective_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormToAmbientQuotient_injective_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormToAmbientQuotient_injective_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormCoreEquiv
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormCoreEquiv

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.coreAmbientEquiv
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.coreAmbientEquiv

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormAmbientEquiv
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormAmbientEquiv

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Saturate
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Saturate

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_extensive
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_extensive

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_nf_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_nf_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_conv_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_conv_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_mono

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_idempotent
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_idempotent

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_greatest
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_greatest

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_trans
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_trans

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_self_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_self_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_star_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_star_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_pair_comparable
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_pair_comparable

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_join_one_step
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_join_one_step

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_cr_iff_unc
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_cr_iff_unc

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.unc_iff_exists_confluent_extension
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.unc_iff_exists_confluent_extension

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_map
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_map

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_normalizes_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_normalizes_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_convertsToNF_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_convertsToNF_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_hereditary_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_hereditary_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_sn_iff_empty
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_sn_iff_empty

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.SameNormalFormReductions
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.SameNormalFormReductions

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.NonnormalNFP
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.NonnormalNFP

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.same_nf_reductions_sat_iff_nonnormal_nfp
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.same_nf_reductions_sat_iff_nonnormal_nfp

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.nfp_iff_unc_and_nonnormal_nfp
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.nfp_iff_unc_and_nonnormal_nfp

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.nfp_iff_unc_and_same_nf_reductions_sat
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.nfp_iff_unc_and_same_nf_reductions_sat

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.same_nf_reductions_sat_iff_nfp
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.same_nf_reductions_sat_iff_nfp

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.same_nf_reductions_sat_iff_domains_equal
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.same_nf_reductions_sat_iff_domains_equal

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.SourceSupport
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.SourceSupport

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sourceSupport_iff_not_nf
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sourceSupport_iff_not_nf

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.RelationSignature
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.RelationSignature

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.SignatureLE
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.SignatureLE

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.relationSigma
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.relationSigma

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.relationGamma
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.relationGamma

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.signatureLE_refl
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.signatureLE_refl

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.signatureLE_trans
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.signatureLE_trans

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.signatureLE_antisymm
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.signatureLE_antisymm

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.relationSigma_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.relationSigma_mono

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.relationGamma_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.relationGamma_mono

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.relation_adjunction
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.relation_adjunction

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.relationGammaSigma
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.relationGammaSigma

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.relation_adjunction_unit
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.relation_adjunction_unit

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.relation_adjunction_counit
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.relation_adjunction_counit

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sat_le_iff_signature_le
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sat_le_iff_signature_le

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.MaxRel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.MaxRel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.cr
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.cr

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.reaches
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.reaches

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.normal
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.normal

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.wn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.wn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.idem
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.idem

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.step_invariant
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.step_invariant

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.subrel_maxRel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.subrel_maxRel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.nf_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.nf_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.conv_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.conv_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_of_subrel_maxRel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_of_subrel_maxRel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.maxRel_realizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.maxRel_realizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.exists_realizes_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.exists_realizes_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.empty_realizes_id
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.empty_realizes_id

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.empty_realizes_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.empty_realizes_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.exists_normalizer_iff_wn_cr
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.exists_normalizer_iff_wn_cr

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.star_invariant
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.star_invariant

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.conv_invariant
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.conv_invariant

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.nf_star_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.nf_star_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_normalizer_unique
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_normalizer_unique

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_mono

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_of_sn_subrel_maxRel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_of_sn_subrel_maxRel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_union_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_union_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_iUnion
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_iUnion

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_iInter_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_iInter_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_nonempty_iInter_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_nonempty_iInter_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_intersection_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_intersection_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.AllowedRel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.AllowedRel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.subrel_allowed
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Realizes.subrel_allowed

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.allowed_realizes_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.allowed_realizes_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.exists_realizes_subrel_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.exists_realizes_subrel_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.RootFree
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.RootFree

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Exits
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Exits

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.AllCuts
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.AllCuts

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.FiberCuts
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.FiberCuts

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.exits_of_star
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.exits_of_star

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.root_reach_iff_cuts
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.root_reach_iff_cuts

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.root_reach_iff_fiber_cuts
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.root_reach_iff_fiber_cuts

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_iff_cuts
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_iff_cuts

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_iff_fiber_cuts
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_iff_fiber_cuts

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.not_realizes_iff_closed_rootFree
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.not_realizes_iff_closed_rootFree

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.PathLen
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.PathLen

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.PathLen.toStar
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.PathLen.toStar

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.PathLen.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.PathLen.mono

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.PathLen.map
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.PathLen.map

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.PathLen.snoc
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.PathLen.snoc

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.star_iff_exists_pathLen
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.star_iff_exists_pathLen

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.pathLen_zero_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.pathLen_zero_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.PathLen.first
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.PathLen.first

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.RootDistance
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.RootDistance

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rootDistance_spec
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rootDistance_spec

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rootDistance_le
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rootDistance_le

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rootDistance_eq_zero_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rootDistance_eq_zero_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.ShortestRel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.ShortestRel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.shortestRel_subrel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.shortestRel_subrel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rootDistance_step_le
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rootDistance_step_le

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.shortestRel_successor
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.shortestRel_successor

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.shortestRel_sn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.shortestRel_sn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.shortestRel_realizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.shortestRel_realizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.shortest_path_preserved
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.shortest_path_preserved

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rootDistance_shortest_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rootDistance_shortest_eq

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.shortestRel_idempotent
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.shortestRel_idempotent

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.PathLen.distance_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.PathLen.distance_eq

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.shortest_complete_length
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.shortest_complete_length

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.shortest_path_to_normal_length
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.shortest_path_to_normal_length

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.FunctionalRel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.FunctionalRel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.MinimalRealizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.MinimalRealizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.LeastRealizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.LeastRealizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.exists_functional_realization_subrel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.exists_functional_realization_subrel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.minimalRealizes_of_functional
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.minimalRealizes_of_functional

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.minimalRealizes_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.minimalRealizes_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.exists_minimal_realization_subrel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.exists_minimal_realization_subrel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.functional_realizes_subrel_shortest
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.functional_realizes_subrel_shortest

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.functional_realizes_sn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.functional_realizes_sn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.MinimalRealizes.sn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.MinimalRealizes.sn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.minimalRealizes_iff_unique_successor
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.minimalRealizes_iff_unique_successor

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.LeastRealizes.minimal
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.LeastRealizes.minimal

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.leastRealizes_unique
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.leastRealizes_unique

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.RootStar
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.RootStar

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rootStar_realizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rootStar_realizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rootStar_functional
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rootStar_functional

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rootStar_minimal
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rootStar_minimal

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rootStar_sn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rootStar_sn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rootStar_irrefl
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rootStar_irrefl

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.FibersAtMostTwo
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.FibersAtMostTwo

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.fibersAtMostTwo_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.fibersAtMostTwo_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rootStar_subrel_of_fibersAtMostTwo
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rootStar_subrel_of_fibersAtMostTwo

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rootStar_least
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rootStar_least

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Reroute
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Reroute

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.reroute_realizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.reroute_realizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.no_common_realization_rootStar_reroute
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.no_common_realization_rootStar_reroute

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.LeastRealizes.nonroot_unique
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.LeastRealizes.nonroot_unique

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.LeastRealizes.small_fibers
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.LeastRealizes.small_fibers

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.exists_leastRealizes_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.exists_leastRealizes_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.leastRealizes_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.leastRealizes_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.edgeSourceEquiv
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.edgeSourceEquiv

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.functional_realizes_edge_count
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.functional_realizes_edge_count

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.MinimalRealizes.edge_count
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.MinimalRealizes.edge_count

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.saturate_realizes_eq_maxRel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.saturate_realizes_eq_maxRel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.saturate_realizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.saturate_realizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.saturate_shortest_eq_maxRel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.saturate_shortest_eq_maxRel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rootDistance_maxRel_nonfixed
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rootDistance_maxRel_nonfixed

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.shortestRel_maxRel_eq_rootStar
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.shortestRel_maxRel_eq_rootStar

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.shortestRel_saturate_eq_rootStar
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.shortestRel_saturate_eq_rootStar

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.maxRel_eq_rootStar_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.maxRel_eq_rootStar_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.saturate_shortest_commute_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.saturate_shortest_commute_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.convertible_saturate_eq_maxRel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.convertible_saturate_eq_maxRel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.convertible_saturate_realizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.convertible_saturate_realizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.nf_subrel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.nf_subrel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.retained_normalizing_paths_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.retained_normalizing_paths_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conservative_deletion
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conservative_deletion

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conservative_deletion_realizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conservative_deletion_realizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.terminating_deletion_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.terminating_deletion_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.DeletionPolicy
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.DeletionPolicy

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Redex
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Redex

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Successors
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Successors

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.PolicyRows
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.PolicyRows

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.deletion_policy_iff_realizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.deletion_policy_iff_realizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policyToRows
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policyToRows

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policyFromRows
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policyFromRows

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policyRowsEquiv
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policyRowsEquiv

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policy_rows_subrel_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policy_rows_subrel_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.fullPolicy
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.fullPolicy

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policyUnion
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policyUnion

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policy_union_le_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policy_union_le_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policyIntersection
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policyIntersection

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policy_common_lower_bound_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policy_common_lower_bound_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policyInf
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policyInf

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policy_le_inf_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policy_le_inf_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.MinimalPolicy
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.MinimalPolicy

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.LeastPolicy
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.LeastPolicy

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policyKeepAt
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policyKeepAt

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.minimal_policy_iff_functional
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.minimal_policy_iff_functional

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.exists_least_policy_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.exists_least_policy_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.PolicyChoices
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.PolicyChoices

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policyFromChoices
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policyFromChoices

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policyFromChoices_step_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policyFromChoices_step_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policyFromChoices_minimal
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policyFromChoices_minimal

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.choosePolicySuccessor
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.choosePolicySuccessor

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.choosePolicySuccessor_mem
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.choosePolicySuccessor_mem

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.minimalPoliciesEquivChoices
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.minimalPoliciesEquivChoices

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.minimalPolicyEdgeSourceEquiv
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.minimalPolicyEdgeSourceEquiv

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.deletionPolicyOrder
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.deletionPolicyOrder

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policyRowsOrder
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policyRowsOrder

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policyRowsOrderIso
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policyRowsOrderIso

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.exists_minimal_policy_below
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.exists_minimal_policy_below

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.redexFintype
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.redexFintype

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.successorsFintype
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.successorsFintype

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policyRowsFintype
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policyRowsFintype

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.deletionPolicyFintype
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.deletionPolicyFintype

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.policyChoicesFintype
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.policyChoicesFintype

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.card_nonempty_subsets
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.card_nonempty_subsets

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.deletion_policy_count
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.deletion_policy_count

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.minimal_deletion_policy_count
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.minimal_deletion_policy_count

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.minimal_deletion_policy_edge_count
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.minimal_deletion_policy_edge_count

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.SameSCC
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.SameSCC

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.SinkSCC
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.SinkSCC

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.sinkSCC_iff_return
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.sinkSCC_iff_return

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.finite_reaches_sinkSCC
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.finite_reaches_sinkSCC

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.finite_realizes_iff_sinkSCC
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.finite_realizes_iff_sinkSCC

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.RuleUnion
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.RuleUnion

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.SafeRule
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.SafeRule

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.CutRule
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.CutRule

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.HitsRuleCuts
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.HitsRuleCuts

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rule_family_realizes_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rule_family_realizes_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.safe_rule_family_realizes_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.safe_rule_family_realizes_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.safe_rule_family_greatest
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.safe_rule_family_greatest

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rule_family_feasible_iff_safe
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rule_family_feasible_iff_safe

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.MinimalRuleFamily
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.MinimalRuleFamily

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.minimal_rule_family_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.minimal_rule_family_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.exists_minimum_rule_cost
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.exists_minimum_rule_cost

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.minimal_rule_family_iff_transversal
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.minimal_rule_family_iff_transversal

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.exists_minimum_rule_cost_finite
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.exists_minimum_rule_cost_finite

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.exists_minimal_rule_family
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.exists_minimal_rule_family

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.singleton_rule_selection_realizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.singleton_rule_selection_realizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.singleton_rule_family_minimal
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.singleton_rule_family_minimal

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.BundledRuleControl.loopBundle
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.BundledRuleControl.loopBundle

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.BundledRuleControl.minimal_bundle_with_loop
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.BundledRuleControl.minimal_bundle_with_loop

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.BundledRuleControl.duplicateBundle
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.BundledRuleControl.duplicateBundle

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.BundledRuleControl.duplicate_selection_same_relation
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.BundledRuleControl.duplicate_selection_same_relation

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.BundledRuleControl.duplicate_minima_incomparable
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.BundledRuleControl.duplicate_minima_incomparable

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.BundledRuleControl.splitBundle
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.BundledRuleControl.splitBundle

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.BundledRuleControl.minimal_bundle_sizes_differ
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.BundledRuleControl.minimal_bundle_sizes_differ

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conservative_deletion_common_normalizer
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conservative_deletion_common_normalizer

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.terminating_base_policy_normalizer
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.terminating_base_policy_normalizer

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Attained
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Attained

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.attained
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.attained

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.attained_surjective
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.attained_surjective

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.image_decoder_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.image_decoder_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.identity_decoder_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.identity_decoder_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.observation_equiv_fixed
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.observation_equiv_fixed

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.invariant_adequacy_iff_kernel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.invariant_adequacy_iff_kernel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normal_form_decoder_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normal_form_decoder_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.invariant_normal_form_decoder_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.invariant_normal_form_decoder_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normal_form_ambient_replacement_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normal_form_ambient_replacement_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.chosenNF_of_normal
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.chosenNF_of_normal

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormObservationEquiv
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormObservationEquiv

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormObservationEquiv_apply
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normalFormObservationEquiv_apply

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.unc_of_normalized_transport
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.unc_of_normalized_transport

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.cr_of_normalized_transport
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.cr_of_normalized_transport

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Conjugate
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Conjugate

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.ConjugateMap
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.ConjugateMap

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_apply
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_apply

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_star
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_star

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_conv

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_nf
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_nf

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_saturate
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_saturate

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_cr
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_cr

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_acc
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_acc

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_sn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_sn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_subrel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_subrel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.relationConjugacy
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.relationConjugacy

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_realizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_realizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_map_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_map_eq

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugacy_symm
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugacy_symm

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_conjugate_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.realizes_conjugate_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.realizationConjugacy
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.realizationConjugacy

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_max_rel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_max_rel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_pathLen
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_pathLen

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_rootDistance
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_rootDistance

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_shortestRel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_shortestRel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_rootDistance_of_intertwining
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_rootDistance_of_intertwining

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_shortestRel_of_intertwining
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_shortestRel_of_intertwining

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_functional
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_functional

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_minimalRealizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_minimalRealizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_leastRealizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_leastRealizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_exists_leastRealizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.conjugate_exists_leastRealizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.OperationClosed
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.OperationClosed

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.maxRel_operation_closed_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.maxRel_operation_closed_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.maxRel_operation_closed
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.maxRel_operation_closed

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.operation_closed_on_restriction
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.operation_closed_on_restriction

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.TermContext
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.TermContext

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.TermContext.plug
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.TermContext.plug

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.termContext_step
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.termContext_step

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rewriting_step_subst
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rewriting_step_subst

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.maxRel_context
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.maxRel_context

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.maxRel_substitution
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.maxRel_substitution

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.normalized_substitution
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.normalized_substitution

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.NoFreshVars
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.NoFreshVars

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.RuleNoFreshVars
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.RuleNoFreshVars

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.noFreshVars_substitution
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.noFreshVars_substitution

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.noFreshVars_arg
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.noFreshVars_arg

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.noFreshVars_context
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.noFreshVars_context

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.noFreshVars_step
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.noFreshVars_step

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.VarMaxRel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.VarMaxRel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.step_subrel_varMaxRel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.step_subrel_varMaxRel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.varMaxRel_realizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.varMaxRel_realizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.varMaxRel_greatest
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.varMaxRel_greatest

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.varMaxRel_context
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.varMaxRel_context

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.varMaxRel_substitution
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.varMaxRel_substitution

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.RuleInstance
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.RuleInstance

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rewriting_step_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rewriting_step_mono

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rewriting_rule_self
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rewriting_rule_self

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.ruleInstance_self
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.ruleInstance_self

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.rewriting_step_iff_ruleUnion
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.rewriting_step_iff_ruleUnion

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.ruleInstance_subrel_iff_of_closed
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.ruleInstance_subrel_iff_of_closed

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.ruleInstance_safe_iff_of_closed
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.ruleInstance_safe_iff_of_closed

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.ruleInstance_safe_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.ruleInstance_safe_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.trs_rule_side_safety
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.trs_rule_side_safety

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.trs_realizes_iff_rule_cuts
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.trs_realizes_iff_rule_cuts

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.trs_extension_realizes_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.trs_extension_realizes_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.ruleAdmission
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.ruleAdmission

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.ruleAdmission_spec_of_closed
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.ruleAdmission_spec_of_closed

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.ruleAdmission_spec
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.ruleAdmission_spec

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.admittedRules
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.admittedRules

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.mem_admittedRules
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.mem_admittedRules

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.admittedRules_extension_realizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.admittedRules_extension_realizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.erasingRule
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.erasingRule

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.erasingTRS
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.erasingTRS

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.groundSource
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.groundSource

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.openTarget
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.openTarget

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.commonResult
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.commonResult

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.erasingRule_noFreshVars
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.erasingRule_noFreshVars

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.erasingTRS_noFreshVars
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.erasingTRS_noFreshVars

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.groundSource_step
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.groundSource_step

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.openTarget_step
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.openTarget_step

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.saturation_fresh_variable
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.saturation_fresh_variable

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.saturation_not_variable_preserving
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.saturation_not_variable_preserving

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.saturation_no_ordinary_presentation
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.FreshVariableControl.saturation_no_ordinary_presentation

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.decidableNF
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.decidableNF

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.Five
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.Five

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fiveRel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fiveRel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.five_transitive
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.five_transitive

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.five_star_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.five_star_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.five_nf_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.five_nf_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.five_unr
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.five_unr

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.five_not_unc
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.five_not_unc

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.Three
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.Three

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escapeRel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escapeRel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_transitive
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_transitive

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_star_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_star_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_nf_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_nf_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_normalizes_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_normalizes_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_unc
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_unc

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_conv_root
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_conv_root

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_not_wn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_not_wn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_not_nfp
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_not_nfp

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_not_cr
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_not_cr

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.deletionBase
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.deletionBase

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.deletion_same_nf
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.deletion_same_nf

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.deletion_base_wn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.deletion_base_wn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.deletion_base_unc
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.deletion_base_unc

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.deletion_base_cr
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.deletion_base_cr

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.deletion_subrel
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.deletion_subrel

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.deletion_same_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.deletion_same_conv

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.deletion_control
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.deletion_control

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.directRoot
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.directRoot

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chain
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chain

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chain_nf_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chain_nf_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chain_root_predecessor_unique
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chain_root_predecessor_unique

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.direct_root_paths
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.direct_root_paths

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chain_root_paths
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chain_root_paths

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.direct_root_sn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.direct_root_sn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chain_sn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chain_sn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.star_chain_same_normalizer
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.star_chain_same_normalizer

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.reverseChain
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.reverseChain

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.reverse_chain_paths
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.reverse_chain_paths

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.reverse_chain_sn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.reverse_chain_sn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.opposite_chains_same_normalizer
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.opposite_chains_same_normalizer

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.terminating_realizations_union_not_sn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.terminating_realizations_union_not_sn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.star_chain_not_graph_isomorphic
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.star_chain_not_graph_isomorphic

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork_wn
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork_wn

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork_not_nfp
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork_not_nfp

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork_all_descendants_normalize
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork_all_descendants_normalize

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_hereditarily_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_hereditarily_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_normalizes_exact
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_normalizes_exact

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_converts_to_nf
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_converts_to_nf

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_three_domains
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_three_domains

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_step_map_does_not_preserve_normalizing_carrier
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.escape_step_map_does_not_preserve_normalizing_carrier

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork_domains_equal_without_nfp
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork_domains_equal_without_nfp

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork_nonnormal_nfp
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork_nonnormal_nfp

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork_sat_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork_sat_iff

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork_same_nf_reductions_sat
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork_same_nf_reductions_sat

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork_saturation_control
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.fork_saturation_control

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chainRank
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chainRank

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chain_rank_step
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chain_rank_step

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chain_path_rank
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chain_path_rank

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chain_rootDistance
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.chain_rootDistance

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.shortcut
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.shortcut

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.shortcut_rootDistance_a
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.shortcut_rootDistance_a

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.shortcut_rootDistance_b
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.shortcut_rootDistance_b

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.shortcut_realizes
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.shortcut_realizes

#check @OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.shortestRel_nonmonotone_control
#print axioms OperatorKO7.Meta.UniqueNormalization.Normalization.Examples.shortestRel_nonmonotone_control

