import OperatorKO7.Meta.NormalizationBoundary.ThreeFaces

/-!
# Reach and axiom gate: `Meta/NormalizationBoundary/ThreeFaces.lean`

Every explicit public declaration of the owned module carries a paired `#check`
and `#print axioms` here.
-/

open OperatorKO7.Meta.NormalizationBoundary.ThreeFaces

#check @distinction_collapse_constant
#print axioms distinction_collapse_constant

#check @orientation_collapse_constant
#print axioms orientation_collapse_constant

#check @normalization_face_is_not_constant_collapse
#print axioms normalization_face_is_not_constant_collapse

#check @licensedRecover_injective
#print axioms licensedRecover_injective

#check @three_faces_share_one_root
#print axioms three_faces_share_one_root

#check @normalization_face_has_unbounded_erasure
#print axioms normalization_face_has_unbounded_erasure
#check @normalization_face_exact_token_is_infinite
#print axioms normalization_face_exact_token_is_infinite
