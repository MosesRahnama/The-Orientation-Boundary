import OperatorKO7.Meta.DomainTransformerCertificate_Faithfulness

/-!
# LawUSStateCA DTC faithfulness

Legal-statute plug specialization of the domain-transformer
certificate faithfulness theorem. The wrappers retain plug-validity and expert-signoff parameters.
The imported proof bodies use only the two DTC intake predicates for `Faithful cert`, and only the
invariant bundle's citation conservativity plus verdict licensing for `LawNLClaimHolds`.
-/

namespace OperatorKO7.Meta.Plugs.LawUSStateCA.DTCFaithfulness

open OperatorKO7.Meta.DomainTransformerCertificate_Faithfulness
open OperatorKO7.Meta.DomainTransformerCertificate_Faithfulness.LawUSStateCACluster
open OperatorKO7.Meta.Plugs.LawUSStateCA

/-- LawUSStateCA specialization of
`domain_transformer_certificate_faithfulness_unconditional`.

The conclusion is derived from `hFormalDiffCovers` and `hKeysExhaustEntities`. The imported wrapper
accepts `hLawUSStateCAValidity` as an unused parameter. -/
theorem legalStatuteDTCFaithfulness
    (cert : DomainTransformerCertificate)
    (obligation : LawUSStateCAObligation)
    (hFormalDiffCovers : FormalDiffCovers cert)
    (hKeysExhaustEntities : KeysExhaustEntities cert)
    (hLawUSStateCAValidity : LawUSStateCAPlugValidity cert obligation) :
    Faithful cert :=
  legalStatuteDTCFaithfulness_apply
    cert obligation
    hFormalDiffCovers hKeysExhaustEntities hLawUSStateCAValidity

/-- String containing the declaration name of `legalStatuteDTCFaithfulness`. -/
def legal_statute_dtc_faithfulness_anchor : String :=
  "OperatorKO7.Meta.Plugs.LawUSStateCA.DTCFaithfulness." ++
    "legalStatuteDTCFaithfulness"

/-! ## Local wrapper for the Law claim theorem -/

/-- Local wrapper around `LawUSStateCACluster.law_refinement_soundness`. The imported proof uses
`h_invariants.i5_conservativity` and `h_verdict`; its validity and expert-signoff parameters are
unused. -/
theorem legalStatuteRefinementSoundness
    (cert : DomainTransformerCertificate)
    (obligation : LawUSStateCAObligation)
    (claim : LawNLClaim)
    (h_invariants : InvariantsOneToFive cert claim.citations)
    (h_validity : LawUSStateCAPlugValidity cert obligation)
    (h_expert : LegalExpertSignoff cert obligation claim)
    (verdict : EngineVerdict)
    (h_verdict : verdict.licensesNLClaim) :
    LawNLClaimHolds cert claim verdict :=
  law_refinement_soundness
    cert obligation claim
    h_invariants h_validity h_expert verdict h_verdict

/-- String containing the declaration name of `legalStatuteRefinementSoundness`. -/
def legal_statute_refinement_soundness_anchor : String :=
  "OperatorKO7.Meta.Plugs.LawUSStateCA.DTCFaithfulness." ++
    "legalStatuteRefinementSoundness"

end OperatorKO7.Meta.Plugs.LawUSStateCA.DTCFaithfulness
