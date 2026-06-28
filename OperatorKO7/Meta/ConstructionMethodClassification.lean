import OperatorKO7.Meta.EscapeTrichotomy
import OperatorKO7.Meta.PolyInterpretation_FullStep
import OperatorKO7.Meta.MPO_FullStep
import OperatorKO7.Meta.BenchmarkedPrimitiveRecursionFamily
import OperatorKO7.Meta.BoundaryFactorization

/-!
# Construction-Method Classification

This module starts the M1 construction-side classification layer. It does not claim a
universal theorem about all first-order methods. It packages explicit W1 successes already
present in the artifact and records which structural import each one uses.

The W1 envelope here is intentionally narrow and theorem-backed:

- precedence import through the KO7 MPO witness;
- nonlinear/global polynomial import through the `W` witness;
- imported-whole witness import through the benchmarked primitive-recursion family;
- transparency-essentiality import through the same nonlinear `W` witness.
-/

namespace OperatorKO7.ConstructionMethodClassification

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- Small route vocabulary for the paper's W0/W1/W2 discussion. -/
inductive ConstructionRoute where
  | W0
  | W1
  | W2
deriving DecidableEq, Repr

/-- Permitted structural imports for the first theorem-backed W1 layer. -/
inductive W1ImportClass where
  | precedence
  | globalPolynomial
  | importedWholeWitness
  | transparencyEssentiality
deriving DecidableEq, Repr

/-- The nonlinear polynomial witness is not base-transparent on `ko7Schema`. -/
theorem poly_not_transparent_at_base :
    ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema PolyInterpretation.W := by
  intro htransparent
  simp [StepDuplicatingSchema.TransparentAtBase, ko7Schema] at htransparent

/-- The benchmarked imported-whole witness separates W1 success from W0 direct witnesses. -/
theorem fullDuplicating_imported_whole_not_w0_direct :
    BenchmarkedPRCFamily.HasImportedWholeWitness BenchmarkedPRCFamily.fullDuplicating ∧
      ¬ BenchmarkedPRCFamily.HasDirectWitness BenchmarkedPRCFamily.fullDuplicating := by
  exact ⟨BenchmarkedPRCFamily.fullDuplicating_has_imported_whole_witness,
    BenchmarkedPRCFamily.fullDuplicating_has_no_direct_witness⟩

/-- The KO7 recursor-step MPO proof uses the strict precedence comparison `app < recΔ`. -/
theorem mpo_recursor_step_uses_precedence :
    MetaMPO.symPrec MetaMPO.Sym.app MetaMPO.Sym.recΔ := by
  simp [MetaMPO.symPrec, MetaMPO.rank]

/-- The theorem-bearing evidence attached to a permitted W1 import class. -/
inductive W1ImportEvidence : W1ImportClass → Type where
  | precedenceImport :
    (recursorStepPrecedence : MetaMPO.symPrec MetaMPO.Sym.app MetaMPO.Sym.recΔ) →
      (orientsStep : ∀ {a b : Trace}, Step a b → MetaMPO.MPO a b) →
      W1ImportEvidence .precedence
  | globalPolynomialImport :
      (orientsStep : ∀ {a b : Trace}, Step a b → PolyInterpretation.W b < PolyInterpretation.W a) →
      (violatesTransparency : ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema PolyInterpretation.W) →
      (notAdditive : ¬ ∃ c : Nat, ∀ b s n : Trace,
        PolyInterpretation.W (recΔ b s n) =
          c + PolyInterpretation.W b + PolyInterpretation.W s + PolyInterpretation.W n) →
      (notAffine : ¬ ∃ α β γ δ_r : Nat, ∀ b s n : Trace,
        PolyInterpretation.W (recΔ b s n) =
          α + β * PolyInterpretation.W b + γ * PolyInterpretation.W s +
            δ_r * PolyInterpretation.W n) →
      W1ImportEvidence .globalPolynomial
  | importedWholeWitnessImport :
      (witness : BenchmarkedPRCFamily.HasImportedWholeWitness BenchmarkedPRCFamily.fullDuplicating) →
      (notW0Direct : ¬ BenchmarkedPRCFamily.HasDirectWitness BenchmarkedPRCFamily.fullDuplicating) →
      W1ImportEvidence .importedWholeWitness
  | transparencyEssentialityImport :
      (orientsStep : ∀ {a b : Trace}, Step a b → PolyInterpretation.W b < PolyInterpretation.W a) →
      (violatesTransparency : ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema PolyInterpretation.W) →
      W1ImportEvidence .transparencyEssentiality

/-- A first-class W1 construction success carries theorem-level evidence of its permitted import. -/
structure W1ConstructionSuccess where
  route : ConstructionRoute
  route_is_w1 : route = .W1
  importClass : W1ImportClass
  evidence : W1ImportEvidence importClass

/-- The permitted W1 imports restated as a proposition carrying the theorem payload. -/
inductive PermittedW1Import : W1ImportClass → Prop where
  | precedence :
    (recursorStepPrecedence : MetaMPO.symPrec MetaMPO.Sym.app MetaMPO.Sym.recΔ) →
      (orientsStep : ∀ {a b : Trace}, Step a b → MetaMPO.MPO a b) →
      PermittedW1Import .precedence
  | globalPolynomial :
      (orientsStep : ∀ {a b : Trace}, Step a b → PolyInterpretation.W b < PolyInterpretation.W a) →
      (violatesTransparency : ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema PolyInterpretation.W) →
      (notAdditive : ¬ ∃ c : Nat, ∀ b s n : Trace,
        PolyInterpretation.W (recΔ b s n) =
          c + PolyInterpretation.W b + PolyInterpretation.W s + PolyInterpretation.W n) →
      (notAffine : ¬ ∃ α β γ δ_r : Nat, ∀ b s n : Trace,
        PolyInterpretation.W (recΔ b s n) =
          α + β * PolyInterpretation.W b + γ * PolyInterpretation.W s +
            δ_r * PolyInterpretation.W n) →
      PermittedW1Import .globalPolynomial
  | importedWholeWitness :
      (witness : BenchmarkedPRCFamily.HasImportedWholeWitness BenchmarkedPRCFamily.fullDuplicating) →
      (notW0Direct : ¬ BenchmarkedPRCFamily.HasDirectWitness BenchmarkedPRCFamily.fullDuplicating) →
      PermittedW1Import .importedWholeWitness
  | transparencyEssentiality :
      (orientsStep : ∀ {a b : Trace}, Step a b → PolyInterpretation.W b < PolyInterpretation.W a) →
      (violatesTransparency : ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema PolyInterpretation.W) →
      PermittedW1Import .transparencyEssentiality

/-- Any theorem-backed W1 success must realize one of the permitted structural imports. -/
theorem w1_success_requires_permitted_import (S : W1ConstructionSuccess) :
    PermittedW1Import S.importClass := by
  rcases S with ⟨_, _, _, evidence⟩
  cases evidence with
  | precedenceImport recursorStepPrecedence orientsStep =>
    exact PermittedW1Import.precedence recursorStepPrecedence orientsStep
  | globalPolynomialImport orientsStep violatesTransparency notAdditive notAffine =>
      exact PermittedW1Import.globalPolynomial orientsStep violatesTransparency notAdditive notAffine
  | importedWholeWitnessImport witness notW0Direct =>
      exact PermittedW1Import.importedWholeWitness witness notW0Direct
  | transparencyEssentialityImport orientsStep violatesTransparency =>
      exact PermittedW1Import.transparencyEssentiality orientsStep violatesTransparency

/-- Canonical W1 success witness using the KO7-specialized MPO surface. -/
def mpo_w1_success : W1ConstructionSuccess where
  route := .W1
  route_is_w1 := rfl
  importClass := .precedence
  evidence := .precedenceImport mpo_recursor_step_uses_precedence MetaMPO.mpo_orients_step

/-- Canonical W1 success witness using the nonlinear/global polynomial witness. -/
def poly_w1_success : W1ConstructionSuccess where
  route := .W1
  route_is_w1 := rfl
  importClass := .globalPolynomial
  evidence := .globalPolynomialImport
    PolyInterpretation.W_orients_step
    poly_not_transparent_at_base
    PolyInterpretation.W_not_additive
    PolyInterpretation.W_not_affine

/-- Canonical W1 success witness using the benchmarked imported-whole witness. -/
def importedWhole_w1_success : W1ConstructionSuccess where
  route := .W1
  route_is_w1 := rfl
  importClass := .importedWholeWitness
  evidence := .importedWholeWitnessImport
    fullDuplicating_imported_whole_not_w0_direct.1
    fullDuplicating_imported_whole_not_w0_direct.2

/-- Canonical W1 success witness using transparency-essentiality evidence. -/
def transparency_w1_success : W1ConstructionSuccess where
  route := .W1
  route_is_w1 := rfl
  importClass := .transparencyEssentiality
  evidence := .transparencyEssentialityImport
    PolyInterpretation.W_orients_step
    poly_not_transparent_at_base

/-- The canonical MPO witness extracts the explicit precedence-side import. -/
theorem mpo_w1_success_requires_precedence_import :
    PermittedW1Import .precedence := by
  simpa [mpo_w1_success] using w1_success_requires_permitted_import mpo_w1_success

/-- The canonical polynomial witness extracts the global-polynomial import. -/
theorem poly_w1_success_requires_global_polynomial_import :
    PermittedW1Import .globalPolynomial := by
  simpa [poly_w1_success] using w1_success_requires_permitted_import poly_w1_success

/-- The canonical imported-whole witness extracts the imported-whole lane. -/
theorem importedWhole_w1_success_requires_imported_whole :
    PermittedW1Import .importedWholeWitness := by
  simpa [importedWhole_w1_success] using
    w1_success_requires_permitted_import importedWhole_w1_success

/-- The canonical transparency witness extracts the transparency-essentiality lane. -/
theorem transparency_w1_success_requires_transparency_import :
    PermittedW1Import .transparencyEssentiality := by
  simpa [transparency_w1_success] using
    w1_success_requires_permitted_import transparency_w1_success

/-- The imported-whole W1 witness stays outside the W0 direct-witness lane. -/
theorem importedWhole_w1_success_separates_from_w0 :
    importedWhole_w1_success.route ≠ .W0 ∧
      BenchmarkedPRCFamily.HasImportedWholeWitness BenchmarkedPRCFamily.fullDuplicating ∧
      ¬ BenchmarkedPRCFamily.HasDirectWitness BenchmarkedPRCFamily.fullDuplicating := by
  refine ⟨?_, BenchmarkedPRCFamily.fullDuplicating_has_imported_whole_witness,
    BenchmarkedPRCFamily.fullDuplicating_has_no_direct_witness⟩
  simp [importedWhole_w1_success]

/-- The nonlinear polynomial W1 witness escapes the direct additive, affine, and transparent surface. -/
theorem poly_w1_success_escapes_direct_additive_affine_surface :
    ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema PolyInterpretation.W ∧
      (¬ ∃ c : Nat, ∀ b s n : Trace,
        PolyInterpretation.W (recΔ b s n) =
          c + PolyInterpretation.W b + PolyInterpretation.W s + PolyInterpretation.W n) ∧
      (¬ ∃ α β γ δ_r : Nat, ∀ b s n : Trace,
        PolyInterpretation.W (recΔ b s n) =
          α + β * PolyInterpretation.W b + γ * PolyInterpretation.W s +
            δ_r * PolyInterpretation.W n) := by
  exact ⟨poly_not_transparent_at_base,
    ⟨PolyInterpretation.W_not_additive, PolyInterpretation.W_not_affine⟩⟩

/-- Combined catalog for the canonical theorem-backed W1 witnesses currently formalized here. -/
theorem canonical_w1_witness_catalog :
    (mpo_w1_success.importClass = .precedence ∧ PermittedW1Import .precedence) ∧
      (poly_w1_success.importClass = .globalPolynomial ∧ PermittedW1Import .globalPolynomial) ∧
      (importedWhole_w1_success.importClass = .importedWholeWitness ∧
        PermittedW1Import .importedWholeWitness) ∧
      (transparency_w1_success.importClass = .transparencyEssentiality ∧
        PermittedW1Import .transparencyEssentiality) := by
  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · exact ⟨rfl, mpo_w1_success_requires_precedence_import⟩
  · exact ⟨rfl, poly_w1_success_requires_global_polynomial_import⟩
  · exact ⟨rfl, importedWhole_w1_success_requires_imported_whole⟩
  · exact ⟨rfl, transparency_w1_success_requires_transparency_import⟩

end OperatorKO7.ConstructionMethodClassification
