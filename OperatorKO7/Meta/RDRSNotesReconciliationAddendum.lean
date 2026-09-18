import OperatorKO7.Meta.RDRSTerminationMethodUniverseCloseout
import OperatorKO7.Meta.DirectBarrierScope
import OperatorKO7.Meta.FBI_FinalCatalog
import OperatorKO7.Meta.MatrixUnrestrictedSplit

/-!
# RDRS Notes Reconciliation Addendum

This module closes the residual method names that still appear in
`Theory-Expansion-Notes.md` but are not explicit rows in the 76-row RDRS
termination-method universe. The addendum does not widen the Paper A theorem.
It records the remaining note-only names as theorem-backed classifications
against existing scope sentinels, final catalogs, or nonconservative substrate
changes.
-/

namespace OperatorKO7.RDRSNotesReconciliationAddendum

open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.RDRSTerminationMethodUniverseCloseout
open OperatorKO7.StepDuplicating

/-- Residual names extracted from `Theory-Expansion-Notes.md` that were not
explicitly named in the 76-row RDRS universe. -/
inductive NotesReconciliationRow
  | coRewritePairCoWPO
  | uncurryingApplicativeTransformation
  | innermostStrategyRestriction
  | weakCallByNameStrategyRestriction
  | constraintTrivialization
  | generalizedWPOBranch
  | fbiAdequacyBridge
  | matrixUnrestrictedSplitBridge
  | probabilisticASTMethods
  | modularHierarchicalCommutativeUnion
  | complexityDependencyTuple
  deriving DecidableEq, Repr

/-- Exact note-reconciliation row list. -/
def notesReconciliationRows : List NotesReconciliationRow :=
  [ .coRewritePairCoWPO
  , .uncurryingApplicativeTransformation
  , .innermostStrategyRestriction
  , .weakCallByNameStrategyRestriction
  , .constraintTrivialization
  , .generalizedWPOBranch
  , .fbiAdequacyBridge
  , .matrixUnrestrictedSplitBridge
  , .probabilisticASTMethods
  , .modularHierarchicalCommutativeUnion
  , .complexityDependencyTuple
  ]

theorem notesReconciliationRows_length :
    notesReconciliationRows.length = 11 := by
  decide

theorem notesReconciliationRows_nodup :
    notesReconciliationRows.Nodup := by
  decide

theorem notesReconciliationRows_complete (row : NotesReconciliationRow) :
    row ∈ notesReconciliationRows := by
  cases row <;> decide

/-- Terminal classification for each note-only row. -/
def notesStatus : NotesReconciliationRow → RDRSMethodStatus
  | .coRewritePairCoWPO => .nonconservative_escape
  | .uncurryingApplicativeTransformation => .nonconservative_escape
  | .innermostStrategyRestriction => .conditional_escape
  | .weakCallByNameStrategyRestriction => .conditional_escape
  | .constraintTrivialization => .conditional_escape
  | .generalizedWPOBranch => .conditional_escape
  | .fbiAdequacyBridge => .import_dependent
  | .matrixUnrestrictedSplitBridge => .conditional_escape
  | .probabilisticASTMethods => .nonconservative_escape
  | .modularHierarchicalCommutativeUnion => .nonconservative_escape
  | .complexityDependencyTuple => .not_applicable

/-- Every note-only row has a terminal status in the same vocabulary as the
RDRS universe. -/
theorem notesStatus_total (row : NotesReconciliationRow) :
    ∃ status : RDRSMethodStatus, notesStatus row = status :=
  ⟨notesStatus row, rfl⟩

/-- A constrained or trivialized rule-firing setting violates the RDRS firing
requirement rather than creating a new direct-orientation theorem. -/
def constraintTrivializationScope : DirectBarrierScope where
  hasPositions := True
  hasOccurrenceCounter := True
  hasFirabilityWitness := False
  treeSemantics := True
  firstOrder := True
  fullRewriting := True
  monotoneObserver := True
  syntacticDirect := True
  noEquationalQuotient := True

theorem constraintTrivializationScope_not_InScope :
    ¬ InScope constraintTrivializationScope :=
  fun h => h.hasFirabilityWitness

/-! ### Typed substrate carriers

The four rows below used to close against `Prop := True` sentinels, which carried no content. Each
is now an indexed typed carrier with a proved carrier-level incompatibility: a statement that the
substrate the row names differs structurally from the deterministic, single-component, fixed-
signature, orientation-bearing substrate the direct RDRS barrier is stated over.

These are carrier-level incompatibilities, not faithful adapters for any named real method. No
claim is made here that a concrete published method instantiates any of these carriers; supplying
such an adapter is WP-10's surface, not this addendum's. -/

/-- Signature-changing transformation carrier: a symbol set with arities together with a
transformation that provably moves at least one symbol. -/
structure SignatureTransformationCarrier where
  /-- The symbol set of the source signature. -/
  Sym : Type
  /-- Arity assignment on the source signature. -/
  arity : Sym → Nat
  /-- The signature transformation induced by the method. -/
  transform : Sym → Sym
  /-- A symbol the transformation moves. -/
  movedSymbol : Sym
  /-- The transformation is not the identity at that symbol. -/
  moves : transform movedSymbol ≠ movedSymbol

/-- Uncurrying-style witness on a two-symbol signature: the binary symbol is exchanged with the
constant, so the transformation is provably non-identity. -/
def uncurryingSignatureTransformation : SignatureTransformationCarrier where
  Sym := Bool
  arity := fun b => if b then 2 else 0
  transform := not
  movedSymbol := true
  moves := by decide

/-- Signature-changing transformations, including uncurrying, close as nonconservative substrate
changes: the carrier is inhabited by a transformation that is not the identity on symbols. -/
abbrev signatureTransformationClosed : Prop := Nonempty SignatureTransformationCarrier

theorem signatureTransformationClosed_intro :
    signatureTransformationClosed :=
  ⟨uncurryingSignatureTransformation⟩

/-- Carrier-level incompatibility: the transformation moves a symbol, so the post-transformation
signature is not the fixed RDRS signature the direct barrier quantifies over. -/
theorem signatureTransformation_is_not_identity (C : SignatureTransformationCarrier) :
    ∃ s : C.Sym, C.transform s ≠ s :=
  ⟨C.movedSymbol, C.moves⟩

/-- The generalized-WPO note splits between the existing RDRS closeout and the
nonmonotone co-order sentinel. -/
abbrev generalizedWPOBranchClosed : Prop :=
  RDRSUniverseClosed ∧ ¬ InScope coOrderScope

theorem generalizedWPOBranchClosed_intro :
    generalizedWPOBranchClosed :=
  ⟨rdrs_termination_method_universe_closed, coOrderScope_not_InScope⟩

/-- Probabilistic substrate carrier: a weighted outcome space with two distinct branches that both
carry positive mass. -/
structure ProbabilisticSubstrateCarrier where
  /-- The outcome space of one rewrite decision. -/
  Outcome : Type
  /-- Unnormalized distribution data on outcomes. -/
  weight : Outcome → Nat
  /-- First branch of a genuinely probabilistic decision. -/
  branchLeft : Outcome
  /-- Second branch of a genuinely probabilistic decision. -/
  branchRight : Outcome
  /-- The two branches are distinct. -/
  branches_distinct : branchLeft ≠ branchRight
  /-- The first branch carries positive mass. -/
  left_pos : 0 < weight branchLeft
  /-- The second branch carries positive mass. -/
  right_pos : 0 < weight branchRight

/-- Fair two-outcome witness. -/
def fairCoinProbabilisticSubstrate : ProbabilisticSubstrateCarrier where
  Outcome := Bool
  weight := fun _ => 1
  branchLeft := true
  branchRight := false
  branches_distinct := by decide
  left_pos := by decide
  right_pos := by decide

/-- Probabilistic AST methods change the substrate away from the deterministic first-order RDRS
direct-barrier lane: the carrier is inhabited by explicit distribution data. -/
abbrev probabilisticASTMethodsClosed : Prop := Nonempty ProbabilisticSubstrateCarrier

theorem probabilisticASTMethodsClosed_intro :
    probabilisticASTMethodsClosed :=
  ⟨fairCoinProbabilisticSubstrate⟩

/-- Carrier-level incompatibility: two distinct outcomes carry positive mass at the same decision,
so no single deterministic successor represents the substrate. -/
theorem probabilisticSubstrate_has_two_positive_branches
    (C : ProbabilisticSubstrateCarrier) :
    ∃ o₁ o₂ : C.Outcome, o₁ ≠ o₂ ∧ 0 < C.weight o₁ ∧ 0 < C.weight o₂ :=
  ⟨C.branchLeft, C.branchRight, C.branches_distinct, C.left_pos, C.right_pos⟩

/-- Union / hierarchy substrate carrier: two distinct components together with a rule index that
the second component carries and the first does not. -/
structure UnionSubstrateCarrier where
  /-- The component index of the union or hierarchy. -/
  Component : Type
  /-- First component. -/
  first : Component
  /-- Second component. -/
  second : Component
  /-- The two components are distinct. -/
  components_distinct : first ≠ second
  /-- Rule membership per component. -/
  carries : Component → Nat → Prop
  /-- A rule index that separates the two components. -/
  splitRule : Nat
  /-- The second component carries the separating rule. -/
  splitRule_in_second : carries second splitRule
  /-- The first component does not. -/
  splitRule_not_in_first : ¬ carries first splitRule

/-- Two-component witness. -/
def twoComponentUnionSubstrate : UnionSubstrateCarrier where
  Component := Bool
  first := true
  second := false
  components_distinct := by decide
  carries := fun c _ => c = false
  splitRule := 0
  splitRule_in_second := rfl
  splitRule_not_in_first := by decide

/-- Modular, hierarchical, and commutative-union methods are recorded as substrate-changing method
families: the carrier is inhabited by a genuine second component. -/
abbrev modularHierarchicalCommutativeUnionClosed : Prop := Nonempty UnionSubstrateCarrier

theorem modularHierarchicalCommutativeUnionClosed_intro :
    modularHierarchicalCommutativeUnionClosed :=
  ⟨twoComponentUnionSubstrate⟩

/-- Carrier-level incompatibility: the second component carries a rule the first does not, so a
single-system reading of the substrate omits a rule. -/
theorem unionSubstrate_has_second_component_rule (C : UnionSubstrateCarrier) :
    ∃ r : Nat, C.carries C.second r ∧ ¬ C.carries C.first r :=
  ⟨C.splitRule, C.splitRule_in_second, C.splitRule_not_in_first⟩

/-- Complexity-only carrier: a derivation-length bound that is non-increasing across the step
relation, together with an explicit step on which the bound ties. The record has no orientation
field, and the tie witness shows none can be extracted. -/
structure ComplexityOnlyCarrier where
  /-- Term carrier. -/
  Term : Type
  /-- Step relation. -/
  step : Term → Term → Prop
  /-- Derivation-length bound. -/
  bound : Term → Nat
  /-- The bound never increases across a step. This is the complexity conclusion. -/
  bound_nonincreasing : ∀ a b, step a b → bound b ≤ bound a
  /-- Source of a step on which the bound ties. -/
  tieSource : Term
  /-- Target of a step on which the bound ties. -/
  tieTarget : Term
  /-- The tie step is a real step. -/
  tie_step : step tieSource tieTarget
  /-- The bound does not move across it. -/
  tie_bound : bound tieTarget = bound tieSource

/-- Constant-bound witness. -/
def constantComplexityOnlyCarrier : ComplexityOnlyCarrier where
  Term := Unit
  step := fun _ _ => True
  bound := fun _ => 0
  bound_nonincreasing := fun _ _ _ => Nat.le_refl 0
  tieSource := ()
  tieTarget := ()
  tie_step := trivial
  tie_bound := rfl

/-- Complexity-only dependency tuples close as a non-orientation row: the carrier is inhabited by a
bound that is non-increasing but carries no strict-decrease datum. -/
abbrev complexityDependencyTupleClosed : Prop := Nonempty ComplexityOnlyCarrier

theorem complexityDependencyTupleClosed_intro :
    complexityDependencyTupleClosed :=
  ⟨constantComplexityOnlyCarrier⟩

/-- Carrier-level incompatibility: the complexity bound admits a step on which it fails to strictly
decrease, so it supplies no orientation datum for the direct RDRS barrier. -/
theorem complexityOnly_has_no_strict_orientation (C : ComplexityOnlyCarrier) :
    ∃ a b : C.Term, C.step a b ∧ ¬ (C.bound b < C.bound a) := by
  refine ⟨C.tieSource, C.tieTarget, C.tie_step, ?_⟩
  rw [C.tie_bound]
  exact Nat.lt_irrefl _

/-- Packed certificate that every residual name from `Theory-Expansion-Notes.md`
has been assigned to an existing theorem-backed surface or a closed substrate
classification. -/
structure NotesReconciliationClosed : Prop where
  rowCount : notesReconciliationRows.length = 11
  nodup : notesReconciliationRows.Nodup
  complete : ∀ row : NotesReconciliationRow, row ∈ notesReconciliationRows
  statusTotal : ∀ row : NotesReconciliationRow,
    ∃ status : RDRSMethodStatus, notesStatus row = status
  coOrderClosed : ¬ InScope coOrderScope
  innermostClosed : ¬ InScope innermostOnlyScope
  constraintClosed : ¬ InScope constraintTrivializationScope
  signatureTransformClosed : signatureTransformationClosed
  generalizedWPOClosed : generalizedWPOBranchClosed
  fbiClosed : OperatorKO7.FBIFinalCatalog.FBIFinalCatalogCertificate
  matrixUnrestrictedClosed :
    OperatorKO7.MatrixUnrestrictedSplit.MatrixUnrestrictedSplitFinalCatalog
  probabilisticClosed : probabilisticASTMethodsClosed
  modularClosed : modularHierarchicalCommutativeUnionClosed
  dependencyTupleClosed : complexityDependencyTupleClosed

/-- Final addendum marker for the notes-reconciliation pass. -/
theorem rdrs_notes_reconciliation_addendum_closed :
    NotesReconciliationClosed where
  rowCount := notesReconciliationRows_length
  nodup := notesReconciliationRows_nodup
  complete := notesReconciliationRows_complete
  statusTotal := notesStatus_total
  coOrderClosed := coOrderScope_not_InScope
  innermostClosed := innermostOnlyScope_not_InScope
  constraintClosed := constraintTrivializationScope_not_InScope
  signatureTransformClosed := signatureTransformationClosed_intro
  generalizedWPOClosed := generalizedWPOBranchClosed_intro
  fbiClosed := OperatorKO7.FBIFinalCatalog.fbi_final_catalog_certificate
  matrixUnrestrictedClosed :=
    OperatorKO7.MatrixUnrestrictedSplit.unrestricted_matrix_classes_split_final_catalog
  probabilisticClosed := probabilisticASTMethodsClosed_intro
  modularClosed := modularHierarchicalCommutativeUnionClosed_intro
  dependencyTupleClosed := complexityDependencyTupleClosed_intro

/-- Stable string anchor for paper and supervisor ledgers. -/
def rdrs_notes_reconciliation_addendum_closed_anchor : String :=
  "OperatorKO7.RDRSNotesReconciliationAddendum.rdrs_notes_reconciliation_addendum_closed"

end OperatorKO7.RDRSNotesReconciliationAddendum
