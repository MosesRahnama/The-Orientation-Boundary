import OperatorKO7.Meta.NormalizationBoundary.ThreeFaces

/-!
# Reach and axiom gate: `Meta/NormalizationBoundary/ThreeFaces.lean`

Every explicit public declaration of the owned module carries a paired `#check`
and `#print axioms` here (LASOT Gate Q24, section 18.2).

Build status note.  This gate's import closure passes through
`Meta/DistinctionBoundary/SharedRoot.lean` and from there, at eight hops, through
`Meta/InformationAccess.lean`, which is an uncommitted in-flight edit of another
sprint and does not currently elaborate.  Until that module is repaired by its
owner, this gate and its target module are validated by direct
`lake env lean` only, and no `.olean` build artifact may be claimed for them
(LASOT Q39).  The blockage is pre-existing and independent of this lane: the
control build of the untouched sibling
`Meta/NormalizationBoundary/NormalizationLicense.lean` fails with the same three
`InformationAccess` errors.
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
