import OperatorKO7.Meta.RDRSTerminationMethodAtlas

namespace OperatorKO7.RDRSTerminationMethodAtlasReach

open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.RDRSTerminationMethodAtlas

#check RDRSAtlasRow
#check RDRSAtlasReason
#check RDRSAtlasSurface
#check rdrsTerminationMethodAtlas
#check rdrsTerminationMethodAtlas_length
#check rdrs_termination_method_atlas_nodup
#check rdrs_termination_method_atlas_has_no_unclassified_rows
#check rdrs_termination_method_atlas_complete

theorem reach_atlas_length :
    rdrsTerminationMethodAtlas.length = 76 :=
  rdrsTerminationMethodAtlas_length

theorem reach_atlas_nodup :
    rdrsTerminationMethodAtlas.Nodup :=
  rdrs_termination_method_atlas_nodup

theorem reach_atlas_no_unclassified :
    ∀ row : RDRSAtlasRow,
      row ∈ rdrsTerminationMethodAtlas → row.Classified :=
  rdrs_termination_method_atlas_has_no_unclassified_rows

theorem reach_atlas_complete_marker :
    rdrsTerminationMethodAtlas.length = 76 ∧
      rdrsTerminationMethodAtlas.Nodup ∧
      (∀ family : RDRSMethodFamily,
        ∃ row : RDRSAtlasRow,
          row ∈ rdrsTerminationMethodAtlas ∧
            row.family = family ∧
            row.status = statusOf family ∧
            row.reason = reasonOfStatus (statusOf family) ∧
            row.surface = surfaceOfStatus (statusOf family)) ∧
      (∀ row : RDRSAtlasRow,
        row ∈ rdrsTerminationMethodAtlas → row.Classified) :=
  rdrs_termination_method_atlas_complete

theorem reach_standard_kbo_status :
    (rowOf .standardKBO).status = .barrier :=
  rfl

theorem reach_subterm_coefficient_kbo_status :
    (rowOf .subtermCoefficientKBO).status = .barrier :=
  rfl

theorem reach_status_projection (family : RDRSMethodFamily) :
    (rowOf family).status = statusOf family :=
  rowOf_status family

theorem reach_member_status_projection
    {row : RDRSAtlasRow}
    (hrow : row ∈ rdrsTerminationMethodAtlas) :
    row.status = statusOf row.family :=
  rdrsTerminationMethodAtlas_member_status_exact hrow

end OperatorKO7.RDRSTerminationMethodAtlasReach
