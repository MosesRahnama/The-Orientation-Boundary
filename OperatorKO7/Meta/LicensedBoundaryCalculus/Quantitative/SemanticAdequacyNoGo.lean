import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.KO7SemanticAdequacy

/-!
# Why semantic adequacy is a separate certificate

`SemanticConstructionData` intentionally remains a model input.  This module
constructs data over the exact licensed KO7 relation whose supplied defect
set contains one element even though the relation has no actual local defect.
The profile computation faithfully counts the supplied element, while a
`DefectAdequacy` or full `SemanticAdequacyCertificate` is impossible.

## Audit slots

Relation: the unchanged licensed KO7 relation.
Closure: root-local non-joinability used to refute the fake defect.
Trust: kernel-only finite counterexample.
Scope: statement adequacy of construction data, not a physical no-go.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace SemanticAdequacyNoGo

open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone
open KO7DistinctionAdapter

abbrev CanonicalDefect := KO7DistinctionAdapter.CanonicalDefect
abbrev RepairAction := KO7DistinctionAdapter.RepairAction

/-- A deliberately overdeclared closure table for the negative fixture. -/
def falseDefectCloses (_ : RepairAction) : Finset CanonicalDefect :=
  Finset.univ

theorem falseDefectCoverable :
    IsRepairCover (Finset.univ : Finset CanonicalDefect)
      falseDefectCloses Finset.univ := by
  intro d hd
  simp only [Finset.mem_biUnion]
  exact
    ⟨.guardDiff, Finset.mem_univ _,
      by exact Finset.mem_univ _⟩

/-- Same licensed relation and source as `licensedData`, but with a supplied
singleton defect field. -/
def falseDefectData :
    SemanticConstructionData KO7DistinctionAdapter.rawARS
      CanonicalDefect RepairAction where
  scope := KO7DistinctionAdapter.licensedScope
  defects := Finset.univ
  closes := falseDefectCloses
  coverable := falseDefectCoverable
  actionCost :=
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.actionCost
  witnessAdequacy := baseAdequacy
  fixedLengthAlternatives := 1
  prefixCodeAlternatives := 1

/-- The computation record counts the supplied false defect. -/
theorem falseDefectData_reports_one_fixture :
    (semanticProfile falseDefectData).criticalPairDefect = 1 := by
  rfl

/-- No sound and complete actual-defect interpretation exists for the false
defect field. -/
theorem falseDefectData_not_adequate :
    ¬ Nonempty (DefectAdequacy falseDefectData) := by
  rintro ⟨certificate⟩
  rcases certificate.sound .diagonal (by simp [falseDefectData]) with
    ⟨actual, _hendpoints⟩
  rcases actual with ⟨left, right, hleft, hright, hnot⟩
  cases hleft
  cases hright
  exact hnot
    ⟨.reflVerdict,
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.reach_refl _,
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.reach_refl _⟩

/-- Required F1 no-go: exact relation metadata plus a computed defect count do
not force that count to describe the relation's actual local defects. -/
theorem uncertified_semanticData_does_not_determine_actualDefectProfile :
    (∀ x y,
      falseDefectData.scope.relation x y ↔
        KO7DistinctionAdapter.licenseMorphism.admitted x y) ∧
      (semanticProfile falseDefectData).criticalPairDefect = 1 ∧
      ¬ Nonempty (DefectAdequacy falseDefectData) := by
  refine ⟨fun _ _ => Iff.rfl, falseDefectData_reports_one_fixture, ?_⟩
  exact falseDefectData_not_adequate

/-- Consequently the overdeclared data cannot receive the full semantic
adequacy certificate. -/
theorem falseDefectData_no_full_certificate :
    ¬ Nonempty (SemanticAdequacyCertificate
      KO7DistinctionAdapter.licenseMorphism falseDefectData) := by
  rintro ⟨certificate⟩
  exact falseDefectData_not_adequate ⟨certificate.defects⟩

#check falseDefectData_reports_one_fixture
#check falseDefectData_not_adequate
#check uncertified_semanticData_does_not_determine_actualDefectProfile
#check falseDefectData_no_full_certificate
#print axioms falseDefectData_reports_one_fixture
#print axioms falseDefectData_not_adequate
#print axioms uncertified_semanticData_does_not_determine_actualDefectProfile
#print axioms falseDefectData_no_full_certificate

end SemanticAdequacyNoGo
end OperatorKO7.Meta.LicensedBoundaryCalculus
