import OperatorKO7.Meta.Methods.ExactPromotionCarriers

/-!
# Generalization of the six exact promotion carriers

The six singleton KO7 carriers in `ExactPromotionCarriers` are retained as
instances. This module factors their method data into carrier-parametric
interfaces. The generic interfaces store method operations and defining laws,
not a field containing the row conclusion.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.ExistingSixteenGeneralization

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Methods.DependencyPairTypedRows
open OperatorKO7.Methods.SubstrateChangeRows
open OperatorKO7.Methods.ExactPromotionCarriers

/-! ## Argument filtering -/

/-- Schema-level argument-filter data. The selected recursor coordinate and the
constructor equations are part of the method object. -/
structure SchemaArgumentFilter (S : StepDuplicatingSchema) where
  keepRecurCoordinate : Fin 3
  keepsCounter : keepRecurCoordinate = ⟨2, by decide⟩
  profile : ProjectionRank S

/-- Any counter projection maps the duplicating source above its wrapper target. -/
theorem SchemaArgumentFilter.orients_dup
    {S : StepDuplicatingSchema} (F : SchemaArgumentFilter S) (b s n : S.T) :
    F.profile.rank (S.wrap s (S.recur b s n)) <
      F.profile.rank (S.recur b s (S.succ n)) := by
  rw [F.profile.rank_wrap, F.profile.rank_recur, F.profile.rank_succ]
  omega

/-- KO7 counter-only filtering as an instance of the generic method. -/
def ko7SchemaArgumentFilter : SchemaArgumentFilter ko7Schema where
  keepRecurCoordinate := schemaArgumentFilteringWitness.keepRecurCoordinate
  keepsCounter := schemaArgumentFilteringWitness.keepRecurCoordinate_is_counter
  profile := argumentFilteringDerivedRank

/-- The generic instance recovers the exact promoted method rank. -/
theorem ko7SchemaArgumentFilter_recovers_exact_rank :
    ko7SchemaArgumentFilter.profile.rank =
      KO7ArgumentFilteringMethod.rank .counterOnly := by
  rfl

/-! ## Neutral dependency-pair processors -/

/-- A neutral processor on an arbitrary pair relation. Its semantics is the
output relation; neutrality is exact extensional identity with the input pair
problem. -/
structure NeutralProcessorMethod (α : Type) (Pair : α → α → Prop) where
  output : α → α → Prop
  neutral : ∀ a b, output a b ↔ Pair a b

/-- Neutral processing preserves reverse well-foundedness in both directions. -/
theorem NeutralProcessorMethod.wellFounded_iff
    {α : Type} {Pair : α → α → Prop} (P : NeutralProcessorMethod α Pair) :
    WellFounded (fun y x => P.output x y) ↔ WellFounded (fun y x => Pair x y) := by
  have hrel : P.output = Pair := by
    funext a b
    exact propext (P.neutral a b)
  rw [hrel]

/-- KO7 identity DP processor as a generic neutral processor. -/
def ko7NeutralProcessor : NeutralProcessorMethod Trace DPPair where
  output := identityDPProcessor.output
  neutral := identityDPProcessor_neutral

/-- The generic processor recovers the exact promoted processor relation. -/
theorem ko7NeutralProcessor_recovers_exact :
    ko7NeutralProcessor.output =
      (KO7NeutralDPProcessorMethod.processor .identity).output := rfl

/-! ## Size-change termination -/

/-- Generic single-call size-change method. The graph and the projection rank
are independent data tied by an explicitly selected strict coordinate. -/
structure SingleCallSCTMethod (S : StepDuplicatingSchema) where
  graph : SizeChangeGraph 3
  strictCoordinate : Fin 3
  strictDiagonal : graph.arcs strictCoordinate strictCoordinate = SCArc.strictDecrease
  rank : ProjectionRank S

/-- The projection component of a size-change method orients the schema
recursor call. -/
theorem SingleCallSCTMethod.orients_dup
    {S : StepDuplicatingSchema} (M : SingleCallSCTMethod S) (b s n : S.T) :
    M.rank.rank (S.wrap s (S.recur b s n)) <
      M.rank.rank (S.recur b s (S.succ n)) := by
  rw [M.rank.rank_wrap, M.rank.rank_recur, M.rank.rank_succ]
  omega

/-- The KO7 size-change graph and derived projection as a generic method. -/
def ko7SingleCallSCTMethod : SingleCallSCTMethod ko7Schema where
  graph := schemaRecCallGraph
  strictCoordinate := ⟨2, by decide⟩
  strictDiagonal := schemaRecCallGraph_counter_descent
  rank := sctDerivedRank

/-- The generic graph and rank recover the exact promoted SCT carrier. -/
theorem ko7SingleCallSCTMethod_recovers_exact :
    ko7SingleCallSCTMethod.graph = KO7SizeChangeMethod.graph .schemaSingleCall ∧
      ko7SingleCallSCTMethod.rank = KO7SizeChangeMethod.rank .schemaSingleCall := by
  exact ⟨rfl, rfl⟩

/-! ## Controlled Cichon descent -/

/-- Carrier-parametric Cichon method data. The ordinal notation and the
slow-growing numerical bound are the method outputs. -/
structure ControlledCichonMethod (α : Type) where
  note : α → NONote
  bound : α → Nat
  noteBelowOmega : ∀ x, NONote.repr (note x) < Ordinal.omega0

/-- The concrete guarded contextual Cichon method. -/
def ko7ControlledCichonMethod : ControlledCichonMethod Trace where
  note := MetaSN_KO7.ctxExpNote
  bound := MetaSN_KO7.ctxExpCichonBound
  noteBelowOmega := MetaSN_KO7.ctxExpNote_lt_omega

/-- The generic data recover both exact promoted Cichon functions. -/
theorem ko7ControlledCichonMethod_recovers_exact :
    ko7ControlledCichonMethod.note = KO7CichonSlowGrowingMethod.note .guardedContextual ∧
      ko7ControlledCichonMethod.bound = KO7CichonSlowGrowingMethod.bound .guardedContextual := by
  exact ⟨rfl, rfl⟩

/-- The existing derivation-length theorem supplies the certification of the
recovered generic method on its live guarded contextual relation. -/
theorem ko7ControlledCichonMethod_certifies :
    CichonSlowGrowingCertifies .guardedContextual :=
  cichonSlowGrowing_certifies .guardedContextual

/-! ## Equational quotients -/

/-- Generic quotient method on a source relation. The equation is the method
semantics; the witness data identify a pair of distinct source-normal terms it
collapses. -/
structure EquationalQuotientMethod (α : Type) (SourceStep : α → α → Prop) where
  equation : α → α → Prop
  left : α
  right : α
  distinct : left ≠ right
  leftNormal : ∀ u, ¬ SourceStep left u
  rightNormal : ∀ u, ¬ SourceStep right u
  identifies : equation left right

/-- Every such quotient is nonconservative for source normal forms. -/
theorem EquationalQuotientMethod.nonconservative
    {α : Type} {SourceStep : α → α → Prop}
    (Q : EquationalQuotientMethod α SourceStep) :
    Q.left ≠ Q.right ∧
      (∀ u, ¬ SourceStep Q.left u) ∧
      (∀ u, ¬ SourceStep Q.right u) ∧ Q.equation Q.left Q.right :=
  ⟨Q.distinct, Q.leftNormal, Q.rightNormal, Q.identifies⟩

/-- Merge commutativity as an instance of the generic quotient method. -/
def ko7EquationalQuotient : EquationalQuotientMethod Trace Step where
  equation := MergeCommutativityEquation
  left := mergeLeft
  right := mergeRight
  distinct := merge_terms_distinct
  leftNormal := mergeLeft_rootNormal
  rightNormal := mergeRight_rootNormal
  identifies := merge_commutativity_identifies_witness

/-- The generic equation recovers the exact promoted quotient relation. -/
theorem ko7EquationalQuotient_recovers_exact :
    ko7EquationalQuotient.equation =
      KO7EquationalQuotientMethod.equation .mergeCommutativity := rfl

/-! ## Sharing -/

/-- Generic sharing method. Two distinct target representations have the same
source read-back while the method's native size records a strict saving. -/
structure SharingMethod (Source Shared : Type) where
  readBack : Shared → Source
  size : Shared → Nat
  sharedRep : Shared
  explicitRep : Shared
  distinctRep : sharedRep ≠ explicitRep
  sameReadBack : readBack sharedRep = readBack explicitRep
  strictSaving : size sharedRep < size explicitRep

/-- A sharing representation with equal read-back is necessarily
noninjective. -/
theorem SharingMethod.readBack_not_injective
    {Source Shared : Type} (M : SharingMethod Source Shared) :
    ¬ Function.Injective M.readBack := by
  intro h
  exact M.distinctRep (h M.sameReadBack)

/-- The explicit shared-node representation as a generic sharing method. -/
def ko7SharingMethod : SharingMethod Trace SharedTerm where
  readBack := unshare
  size := sharedSize
  sharedRep := .shared .leaf
  explicitRep := .node .leaf .leaf
  distinctRep := by decide
  sameReadBack := rfl
  strictSaving := sharedSize_shared_lt_node .leaf

/-- The generic method recovers the exact promoted read-back and size
functions. -/
theorem ko7SharingMethod_recovers_exact :
    ko7SharingMethod.readBack = KO7SharingMethod.readBack .explicitSharedNode ∧
      ko7SharingMethod.size = KO7SharingMethod.size .explicitSharedNode := by
  exact ⟨rfl, rfl⟩

/-! ## Existing-sixteen capstone -/

/-- The six singleton promotion carriers are recovered as instances of generic
method interfaces. The other ten historical rows retain their existing
carrier-wide or schema-wide theorem statements. -/
structure ExistingSixteenGeneralized : Prop where
  argumentFilter : Nonempty (SchemaArgumentFilter ko7Schema)
  argumentFilterExact :
    ko7SchemaArgumentFilter.profile.rank = KO7ArgumentFilteringMethod.rank .counterOnly
  neutralProcessor : Nonempty (NeutralProcessorMethod Trace DPPair)
  neutralExact :
    ko7NeutralProcessor.output = (KO7NeutralDPProcessorMethod.processor .identity).output
  sizeChange : Nonempty (SingleCallSCTMethod ko7Schema)
  sizeChangeExact :
    ko7SingleCallSCTMethod.graph = KO7SizeChangeMethod.graph .schemaSingleCall ∧
      ko7SingleCallSCTMethod.rank = KO7SizeChangeMethod.rank .schemaSingleCall
  cichon : Nonempty (ControlledCichonMethod Trace)
  cichonExact :
    ko7ControlledCichonMethod.note = KO7CichonSlowGrowingMethod.note .guardedContextual ∧
      ko7ControlledCichonMethod.bound = KO7CichonSlowGrowingMethod.bound .guardedContextual
  quotient : Nonempty (EquationalQuotientMethod Trace Step)
  quotientExact :
    ko7EquationalQuotient.equation = KO7EquationalQuotientMethod.equation .mergeCommutativity
  sharing : Nonempty (SharingMethod Trace SharedTerm)
  sharingExact :
    ko7SharingMethod.readBack = KO7SharingMethod.readBack .explicitSharedNode ∧
      ko7SharingMethod.size = KO7SharingMethod.size .explicitSharedNode

/-- Genericization receipt for the six exact historical promotion carriers. -/
theorem existing_sixteen_generalized : ExistingSixteenGeneralized where
  argumentFilter := ⟨ko7SchemaArgumentFilter⟩
  argumentFilterExact := ko7SchemaArgumentFilter_recovers_exact_rank
  neutralProcessor := ⟨ko7NeutralProcessor⟩
  neutralExact := ko7NeutralProcessor_recovers_exact
  sizeChange := ⟨ko7SingleCallSCTMethod⟩
  sizeChangeExact := ko7SingleCallSCTMethod_recovers_exact
  cichon := ⟨ko7ControlledCichonMethod⟩
  cichonExact := ko7ControlledCichonMethod_recovers_exact
  quotient := ⟨ko7EquationalQuotient⟩
  quotientExact := ko7EquationalQuotient_recovers_exact
  sharing := ⟨ko7SharingMethod⟩
  sharingExact := ko7SharingMethod_recovers_exact

end OperatorKO7.Methods.OrientationClosure.ExistingSixteenGeneralization
