import OperatorKO7.Meta.RDRSTerminationMethodUniverse

/-!
# RDRS Termination-Method Atlas

Atlas-kernel row ledger for the RDRS termination-method universe.

The universe file owns the stable family enum and terminal status projection.
This layer packages those families as rows, records a named reason/surface
classification for each row, and proves the exact 76-row coverage facts used by
downstream closeout files.
-/

namespace OperatorKO7.RDRSTerminationMethodAtlas

open OperatorKO7.RDRSTerminationMethodUniverse

/-- Coarse named reason attached to a terminal atlas row. -/
inductive RDRSAtlasReason
  | directBarrier
  | conditionalBarrier
  | conditionalEscapeRoute
  | importedSubstrate
  | constructionRoute
  | nonconservativeRoute
  | outsideRDRSLane
  | externalProblem
  deriving DecidableEq, Repr

/-- The theorem/witness surface expected from later row-specific closeout files. -/
inductive RDRSAtlasSurface
  | directBarrierTheorem
  | conditionalBarrierTheorem
  | conditionalEscapeWitness
  | importDependencyWitness
  | constructionWitness
  | nonconservativeWitness
  | notApplicableWitness
  | externalProblemWitness
  deriving DecidableEq, Repr

/-- One exact atlas row. -/
structure RDRSAtlasRow where
  family : RDRSMethodFamily
  status : RDRSMethodStatus
  reason : RDRSAtlasReason
  surface : RDRSAtlasSurface
  deriving DecidableEq, Repr

/-- A row is classified exactly when its row status agrees with the universe projection. -/
def RDRSAtlasRow.Classified (row : RDRSAtlasRow) : Prop :=
  row.status = statusOf row.family

/-- Named reason projection for terminal statuses. -/
def reasonOfStatus (status : RDRSMethodStatus) : RDRSAtlasReason :=
  if status = .barrier then
    .directBarrier
  else if status = .conditional_barrier then
    .conditionalBarrier
  else if status = .conditional_escape then
    .conditionalEscapeRoute
  else if status = .import_dependent then
    .importedSubstrate
  else if status = .nonconservative_escape then
    .nonconservativeRoute
  else if status = .not_applicable then
    .outsideRDRSLane
  else if status = .external_non_lane_problem then
    .externalProblem
  else
    .constructionRoute

/-- The theorem/witness surface projection for terminal statuses. -/
def surfaceOfStatus (status : RDRSMethodStatus) : RDRSAtlasSurface :=
  if status = .barrier then
    .directBarrierTheorem
  else if status = .conditional_barrier then
    .conditionalBarrierTheorem
  else if status = .conditional_escape then
    .conditionalEscapeWitness
  else if status = .import_dependent then
    .importDependencyWitness
  else if status = .nonconservative_escape then
    .nonconservativeWitness
  else if status = .not_applicable then
    .notApplicableWitness
  else if status = .external_non_lane_problem then
    .externalProblemWitness
  else
    .constructionWitness

/-- Canonical atlas row for one universe family. -/
def rowOf (family : RDRSMethodFamily) : RDRSAtlasRow :=
  { family := family
    status := statusOf family
    reason := reasonOfStatus (statusOf family)
    surface := surfaceOfStatus (statusOf family) }

/-- Exact finite atlas catalog. Its row identities are inherited from the universe list. -/
def rdrsTerminationMethodAtlas : List RDRSAtlasRow :=
  allMethodFamilies.map rowOf

theorem rowOf_family (family : RDRSMethodFamily) :
    (rowOf family).family = family := by
  rfl

theorem rowOf_status (family : RDRSMethodFamily) :
    (rowOf family).status = statusOf family := by
  rfl

theorem rowOf_reason (family : RDRSMethodFamily) :
    (rowOf family).reason = reasonOfStatus (statusOf family) := by
  rfl

theorem rowOf_surface (family : RDRSMethodFamily) :
    (rowOf family).surface = surfaceOfStatus (statusOf family) := by
  rfl

theorem rowOf_classified (family : RDRSMethodFamily) :
    (rowOf family).Classified := by
  rfl

/-- The atlas row ledger has exact length 76. -/
theorem rdrsTerminationMethodAtlas_length :
    rdrsTerminationMethodAtlas.length = 76 := by
  simpa [rdrsTerminationMethodAtlas] using allMethodFamilies_length

/-- The atlas row ledger has no duplicate rows. -/
theorem rdrs_termination_method_atlas_nodup :
    rdrsTerminationMethodAtlas.Nodup := by
  decide

/-- The atlas family projection has no duplicate family identities. -/
theorem rdrsTerminationMethodAtlas_families_nodup :
    (rdrsTerminationMethodAtlas.map RDRSAtlasRow.family).Nodup := by
  simpa [rdrsTerminationMethodAtlas, rowOf] using allMethodFamilies_nodup

/-- Every universe family appears as the family projection of a canonical atlas row. -/
theorem rdrsTerminationMethodAtlas_family_mem (family : RDRSMethodFamily) :
    rowOf family ∈ rdrsTerminationMethodAtlas := by
  simpa [rdrsTerminationMethodAtlas] using
    (List.mem_map_of_mem (f := rowOf) (allMethodFamilies_complete family))

/-- Exact family-level completeness for the 76-row atlas. -/
theorem rdrsTerminationMethodAtlas_complete_exact (family : RDRSMethodFamily) :
    ∃ row : RDRSAtlasRow,
      row ∈ rdrsTerminationMethodAtlas ∧
        row.family = family ∧
        row.status = statusOf family ∧
        row.reason = reasonOfStatus (statusOf family) ∧
        row.surface = surfaceOfStatus (statusOf family) := by
  exact ⟨rowOf family,
    rdrsTerminationMethodAtlas_family_mem family,
    rowOf_family family,
    rowOf_status family,
    rowOf_reason family,
    rowOf_surface family⟩

/-- Any listed row projects back to a listed universe family. -/
theorem rdrsTerminationMethodAtlas_member_family_mem
    {row : RDRSAtlasRow}
    (hrow : row ∈ rdrsTerminationMethodAtlas) :
    row.family ∈ allMethodFamilies := by
  rcases List.mem_map.mp hrow with ⟨family, hfamily, hrow_eq⟩
  rw [← hrow_eq]
  exact hfamily

/-- Any listed row has the exact universe status projection. -/
theorem rdrsTerminationMethodAtlas_member_status_exact
    {row : RDRSAtlasRow}
    (hrow : row ∈ rdrsTerminationMethodAtlas) :
    row.status = statusOf row.family := by
  rcases List.mem_map.mp hrow with ⟨family, _hfamily, hrow_eq⟩
  rw [← hrow_eq]
  rfl

/-- Any listed row has the reason projection induced by its terminal status. -/
theorem rdrsTerminationMethodAtlas_member_reason_exact
    {row : RDRSAtlasRow}
    (hrow : row ∈ rdrsTerminationMethodAtlas) :
    row.reason = reasonOfStatus row.status := by
  rcases List.mem_map.mp hrow with ⟨family, _hfamily, hrow_eq⟩
  rw [← hrow_eq]
  rfl

/-- Any listed row has the theorem/witness surface induced by its terminal status. -/
theorem rdrsTerminationMethodAtlas_member_surface_exact
    {row : RDRSAtlasRow}
    (hrow : row ∈ rdrsTerminationMethodAtlas) :
    row.surface = surfaceOfStatus row.status := by
  rcases List.mem_map.mp hrow with ⟨family, _hfamily, hrow_eq⟩
  rw [← hrow_eq]
  rfl

/-- No atlas row is left outside the terminal classification projection. -/
theorem rdrs_termination_method_atlas_has_no_unclassified_rows :
    ∀ row : RDRSAtlasRow,
      row ∈ rdrsTerminationMethodAtlas → row.Classified := by
  intro row hrow
  exact rdrsTerminationMethodAtlas_member_status_exact hrow

/-- Atlas-kernel closeout marker for the RDRS termination-method universe. -/
theorem rdrs_termination_method_atlas_complete :
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
        row ∈ rdrsTerminationMethodAtlas → row.Classified) := by
  exact ⟨rdrsTerminationMethodAtlas_length,
    rdrs_termination_method_atlas_nodup,
    rdrsTerminationMethodAtlas_complete_exact,
    rdrs_termination_method_atlas_has_no_unclassified_rows⟩

end OperatorKO7.RDRSTerminationMethodAtlas
