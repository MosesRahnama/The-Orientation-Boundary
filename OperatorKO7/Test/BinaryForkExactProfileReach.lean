import OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile

/-! Declaration, axiom, and semantic-instance checks for the binary-fork profile. -/

set_option autoImplicit false

#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportScope
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportScope
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportData
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportData
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.semanticProfile_invariant_under_relationIso
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.semanticProfile_invariant_under_relationIso
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryWitnessAdequacy
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryWitnessAdequacy
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryWitnessAdequacy_rank
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryWitnessAdequacy_rank
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.forkARS
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.forkARS
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.forkARS_fintype
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.forkARS_fintype
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawScope
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawScope
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedScope
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedScope
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawCloses
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawCloses
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.raw_coverable
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.raw_coverable
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedCloses
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedCloses
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensed_coverable
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensed_coverable
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawData
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawData
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedData
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedData
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.raw_repairCandidates_exact
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.raw_repairCandidates_exact
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.raw_repair_cover_exact
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.raw_repair_cover_exact
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.raw_repair_cost_exact
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.raw_repair_cost_exact
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawExactProfile
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawExactProfile
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedExactProfile
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedExactProfile
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.raw_binaryWitness_rank
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.raw_binaryWitness_rank
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensed_binaryWitness_rank
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensed_binaryWitness_rank
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryFork_raw_profile_exact
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryFork_raw_profile_exact
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryFork_licensed_profile_exact
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryFork_licensed_profile_exact
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryFork_profile_drop_exact
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryFork_profile_drop_exact
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.raw_profile_cost_injective
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.raw_profile_cost_injective
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.same_relation_different_repair_cost_profiles
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.same_relation_different_repair_cost_profiles
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.licensedIso
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.licensedIso
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.rawData
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.rawData
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.licensedData
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.licensedData
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryForkPresentation_profile_drop_exact
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryForkPresentation_profile_drop_exact
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.canonicalPresentation
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.canonicalPresentation
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.fintype
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.fintype
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryForkPresentation_profile_exact_unconditional
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryForkPresentation_profile_exact_unconditional
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawDefectAdequacy
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawDefectAdequacy
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedDefectAdequacy
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedDefectAdequacy
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawRepairSemantics
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawRepairSemantics
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedRepairSemantics
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedRepairSemantics
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryWitnessModel
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryWitnessModel
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryWitnessModel_adequate_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryWitnessModel_adequate_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawWitnessLanguageAdequacy
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawWitnessLanguageAdequacy
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedWitnessLanguageAdequacy
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedWitnessLanguageAdequacy
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.optimalBinaryCode
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.optimalBinaryCode
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.optimalPrefixCode
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.optimalPrefixCode
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.optimalPrefixCode_injective
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.optimalPrefixCode_injective
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.optimalPrefixCode_prefixFree
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.optimalPrefixCode_prefixFree
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawAlternativeCarrier
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawAlternativeCarrier
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedAlternativeCarrier
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedAlternativeCarrier
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawMorphism
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawMorphism
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licenseMorphism
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licenseMorphism
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawSemanticAdequacy
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.rawSemanticAdequacy
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedSemanticAdequacy
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.licensedSemanticAdequacy
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.certified_same_relation_different_prices
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.certified_same_relation_different_prices
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.mk
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.mk
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.rawIso
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.rawIso
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.licensed
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.licensed
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.licensed_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.licensed_iff

#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.joinable_transport_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.joinable_transport_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.normalizing_transport
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.normalizing_transport
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.imageRelation
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.imageRelation
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.imageRelationIso
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.imageRelationIso
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportDefectAdequacy
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportDefectAdequacy
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.peakResolved_image_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.peakResolved_image_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportRepairSemantics
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportRepairSemantics
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportWitnessLanguageAdequacy
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportWitnessLanguageAdequacy
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportAlternativeCarrier
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportAlternativeCarrier
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportSemanticAdequacy
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportSemanticAdequacy
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.decodeBinaryCode
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.decodeBinaryCode
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.decodeBinaryCode_encode
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.decodeBinaryCode_encode
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportedBinaryCode
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportedBinaryCode
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportedBinaryDecode
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportedBinaryDecode
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportedBinaryCode_eq_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportedBinaryCode_eq_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportedBinaryDecode_encode
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.transportedBinaryDecode_encode
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.licensed_sub_raw
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.licensed_sub_raw
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.rawMorphism
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.rawMorphism
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.licenseMorphism
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.licenseMorphism
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.rawSemanticAdequacy
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.rawSemanticAdequacy
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.licensedSemanticAdequacy
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.BinaryForkPresentation.licensedSemanticAdequacy
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryForkPresentation_certified_profiles
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.binaryForkPresentation_certified_profiles
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.steps_map
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.steps_map
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.steps_pull
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.steps_pull
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.reach_map
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.reach_map
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.reach_pull
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.reach_pull
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.normalForm_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.normalForm_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.terminalEquiv
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.terminalEquiv
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.terminalFintype
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.terminalFintype
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.terminal_card
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.terminal_card
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.licensedEmbedding
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.licensedEmbedding
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.localARS
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.localARS
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.localFintype
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.localFintype
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.presentation
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.presentation
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ambientBinaryFork_profile_exact
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ambientBinaryFork_profile_exact
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ambientBinaryFork_terminal_counts
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ambientBinaryFork_terminal_counts
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ko7AmbientARS
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ko7AmbientARS
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ko7AmbientBinaryFork
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ko7AmbientBinaryFork
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ko7_binaryFork_profile_recovery
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ko7_binaryFork_profile_recovery
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ko7_binaryFork_ambient_terminals
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ko7_binaryFork_ambient_terminals
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.mk
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.mk
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.map
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.map
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.step_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.step_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.forward_closed
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding.forward_closed
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.mk
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.mk
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.raw
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.raw
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.licensed
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.licensed
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.licensed_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.licensed_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.licensed_sub_raw
#print axioms OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.AmbientBinaryFork.licensed_sub_raw

namespace OperatorKO7.Test.BinaryForkExactProfileReach

open OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile
open OperatorKO7.Meta.LicensedBoundaryCalculus
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork

noncomputable section

example (cost : Nat) : semanticProfile (rawData cost) = rawExactProfile cost :=
  binaryFork_raw_profile_exact cost

example (cost : Nat) : semanticProfile (licensedData cost) = licensedExactProfile :=
  binaryFork_licensed_profile_exact cost

example : (rawData 0).scope = (rawData 1).scope ∧
    semanticProfile (rawData 0) ≠ semanticProfile (rawData 1) :=
  same_relation_different_repair_cost_profiles

example (cost : Nat) : SemanticAdequacyCertificate.{0, 0, 0, 0, 0, 0} rawMorphism (rawData cost) :=
  rawSemanticAdequacy cost

example (cost : Nat) : SemanticAdequacyCertificate.{0, 0, 0, 0, 0, 0} licenseMorphism (licensedData cost) :=
  licensedSemanticAdequacy cost

example : ¬ Nonempty ({x // x ∈ terminalSupport Fork3Step .source} ↪ BitWord 0) := by
  intro h
  have hle := witnessRank_le_of_adequate
    (binaryWitnessAdequacy {x // x ∈ terminalSupport Fork3Step .source}) h
  rw [raw_binaryWitness_rank] at hle
  omega

example : Nonempty ({x // x ∈ terminalSupport Fork3Step .source} ↪ BitWord 1) := by
  have h := witnessRank_adequate
    (binaryWitnessAdequacy {x // x ∈ terminalSupport Fork3Step .source})
  rw [raw_binaryWitness_rank] at h
  exact h

example : witnessRank (binaryWitnessAdequacy Empty) = 0 := by
  rw [binaryWitnessAdequacy_rank]
  norm_num [Nat.clog]

example : witnessRank (binaryWitnessAdequacy (Fin 4)) = 2 := by
  rw [binaryWitnessAdequacy_rank]
  norm_num [Nat.clog]

example : semanticProfile (canonicalPresentation.rawData 7) = rawExactProfile 7 ∧
    semanticProfile (canonicalPresentation.licensedData 7) = licensedExactProfile :=
  binaryForkPresentation_profile_drop_exact canonicalPresentation 7

universe u
example {A : ARS.{u}} (P : BinaryForkPresentation A) (cost : Nat) :
    letI : Fintype A.Carrier := P.fintype
    semanticProfile (P.rawData cost) = rawExactProfile cost ∧
      semanticProfile (P.licensedData cost) = licensedExactProfile :=
  binaryForkPresentation_profile_exact_unconditional P cost

example {A : ARS.{u}} (P : AmbientBinaryFork A) :
    letI := P.raw.terminalFintype .source
    Fintype.card {y // Reach A.step (P.raw.map .source) y ∧
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm A.step y} = 2 :=
  (ambientBinaryFork_terminal_counts P).1

example :
    letI : Fintype {y : OperatorKO7.Trace // Reach OperatorKO7.Step (.eqW .void .void) y ∧
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm OperatorKO7.Step y} :=
      ko7AmbientBinaryFork.raw.terminalFintype .source
    Fintype.card {y : OperatorKO7.Trace // Reach OperatorKO7.Step (.eqW .void .void) y ∧
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm OperatorKO7.Step y} = 2 :=
  ko7_binaryFork_ambient_terminals.1

example {A : ARS.{u}} (P : AmbientBinaryFork A)
    (y : {t // Reach A.step (P.raw.map .source) t ∧
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm A.step t}) :
    transportedBinaryDecode (P.raw.terminalEquiv .source)
      (transportedBinaryCode (P.raw.terminalEquiv .source) y) = some y :=
  transportedBinaryDecode_encode (P.raw.terminalEquiv .source) y

end
end OperatorKO7.Test.BinaryForkExactProfileReach
