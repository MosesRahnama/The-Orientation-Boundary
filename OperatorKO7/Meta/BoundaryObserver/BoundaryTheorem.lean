import OperatorKO7.Meta.BoundaryObserver.MergedPair
import OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates
import OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
import OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy
import OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy
import OperatorKO7.Meta.BoundaryObserver.FiberResolution
import OperatorKO7.Meta.BoundaryObserver.BoundaryPole

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem

universe u

open scoped BigOperators
open OperatorKO7.Meta.BoundaryObserver
open ProtocolResolution MergedPair

noncomputable section

/-- Clause (4) of the Boundary Theorem at a merged pair: every determined Boolean test agrees on
the pair, the separating tests are the two indicator tables of the pair, the transposition of the
pair composed with the indicator of `x₀` is the indicator of `x₁`, so the two tables exchange
under it, a side symbol resolves the pair iff it separates it, and no comparison decoder reads
equality from the records. -/
def KinematicClauseGoal : Prop :=
  ∀ (X Q : Type) [DecidableEq X] (q : X → Q) (x₀ x₁ : X), IsMergedPair q x₀ x₁ →
    (∀ f : X → Bool, Determines q f → f x₀ = f x₁) ∧
    (∀ f : X → Bool, f x₀ ≠ f x₁ →
        (f x₀ = decide (x₀ = x₀) ∧ f x₁ = decide (x₁ = x₀)) ∨
          (f x₀ = decide (x₀ = x₁) ∧ f x₁ = decide (x₁ = x₁))) ∧
    (∀ a : X, decide (Equiv.swap x₀ x₁ a = x₀) = decide (a = x₁)) ∧
    (∀ (S : Type) (s : X → S),
      Set.InjOn (fun x => (q x, s x)) ({x₀, x₁} : Set X) ↔ s x₀ ≠ s x₁) ∧
    ¬ ∃ d : Q → Q → Bool, ∀ a ∈ ({x₀, x₁} : Set X), ∀ b ∈ ({x₀, x₁} : Set X),
        d (q a) (q b) = decide (a = b)

theorem kinematicClause : KinematicClauseGoal := by
  intro X Q _ q x₀ x₁ h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun f hf => MergedPair.mergedPair_tests_through_record h f hf
  · exact (MergedPair.mergedPair_separating_tests h.1).1
  · exact (MergedPair.mergedPair_separating_tests h.1).2.2.1
  · exact fun S s => MergedPair.mergedPair_side_symbol h s
  · exact MergedPair.mergedPair_no_comparison_decoder h

def PlaceOrbitClauseGoal : Prop :=
  ∀ (X Q : Type) (q : X → Q) (n : ℕ) (p p' : X → Fin n),
    p ∈ PlaceCoordinates.PlaceCoord q n → p' ∈ PlaceCoordinates.PlaceCoord q n →
      (∃ σ ∈ OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer.licenseStabilizer q,
          p' = p ∘ σ.symm) ∧
      ∀ τ ∈ OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer.licenseStabilizer q,
        p ∘ τ.symm = p → τ = 1

theorem placeOrbitClause : PlaceOrbitClauseGoal := by
  intro X Q q n p p' hp hp'
  refine ⟨PlaceCoordinates.placeCoord_transitive q hp hp', ?_⟩
  intro τ hτ hfix
  exact PlaceCoordinates.placeCoord_free q hp hτ hfix

/-! ## The core Boundary Theorem

The clauses of the Boundary Theorem that live in logic, recursion, information, statistics,
privacy and secrecy, with the classical form of the apex pair. -/

open BoundarySingularity in
/-- The classical apex pair: the constant observer on the two labels merges them, the binary
reading of bias `ε` has discrimination `8 ε²` at them, and the fair bit has entropy `log 2`. -/
def ApexCoreGoal : Prop :=
  IsMergedPair (fun _ : Bool => ()) true false ∧
    (∀ ε : ℝ, discrimination (binaryKernel ε true) (binaryKernel ε false) = 8 * ε ^ 2) ∧
    Real.binEntropy 2⁻¹ = Real.log 2

open BoundarySingularity in
/-- The classical apex pair holds. -/
theorem apexCoreGoal : ApexCoreGoal :=
  ⟨⟨by decide, rfl⟩, discrimination_binaryKernel, Real.binEntropy_two_inv⟩

open BoundaryPole FiberResolution BoundaryPrivacy BoundarySecrecy in
/-- The core Boundary Theorem: the pole of the record, the kinematic and place clauses, the order
of the pole, the incompleteness and diagonal clauses, the recursion clause, the fibers of size
`n`, the two-point bound, the privacy and secrecy clauses, and the classical apex pair. -/
def BoundaryTheoremCoreGoal : Prop :=
  RecordPoleGoal ∧ BoundaryZeroSetGoal ∧ RecordProtocolPoleGoal ∧ KinematicClauseGoal ∧
    PlaceOrbitClauseGoal ∧ PoleOrderOneGoal ∧ PoleResidueGoal ∧ GodelPoleGoal ∧
    GodelSideSymbolGoal ∧ DiagonalWalkGoal ∧ DiagonalUnionGoal ∧ RecursionClauseGoal.{u} ∧
    FiberOneReadingGoal ∧ FiberCapacityGoal ∧ FiberAttainmentGoal ∧ FiberFanoGoal ∧
    SparseControlGoal ∧ TwoPointGoal ∧ PrivacyDiscriminationGoal ∧ PrivacyCostGoal ∧
    PerfectSecrecyPoleGoal ∧ OneTimePadGoal ∧ ShannonKeyGoal ∧ ApexCoreGoal

/-- The core Boundary Theorem holds, every clause with its accepted proof. -/
theorem boundaryTheoremCoreGoal : BoundaryTheoremCoreGoal.{u} :=
  ⟨BoundaryPole.recordPoleGoal, BoundaryPole.boundaryZeroSetGoal,
    BoundaryPole.recordProtocolPoleGoal, kinematicClause, placeOrbitClause,
    BoundaryPole.poleOrderOneGoal, BoundaryPole.poleResidueGoal, BoundaryPole.godelPoleGoal,
    BoundaryPole.godelSideSymbolGoal, BoundaryPole.diagonalWalkGoal,
    BoundaryPole.diagonalUnionGoal, BoundaryPole.recursionClauseGoal.{u},
    FiberResolution.fiberOneReading, FiberResolution.fiberCapacity,
    FiberResolution.fiberAttainment, FiberResolution.fiberFano, FiberResolution.sparseControl,
    BoundaryPole.twoPointGoal, BoundaryPrivacy.privacyDiscriminationGoal,
    BoundaryPrivacy.privacyCostGoal, BoundarySecrecy.perfectSecrecyPoleGoal,
    BoundarySecrecy.oneTimePadGoal, BoundarySecrecy.shannonKeyGoal, apexCoreGoal⟩

end

end OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem
