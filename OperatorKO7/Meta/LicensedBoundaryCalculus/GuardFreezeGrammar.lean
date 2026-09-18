import OperatorKO7.Meta.DistinctionBoundary.WriteClosure
import OperatorKO7.Meta.DistinctionBoundary.ConservativeRepair
import OperatorKO7.Meta.SafeStep.GaugeFixingGuard

/-!
# Closed guard and freeze-policy grammars

The guard grammar is deliberately bounded: it generates policies determined
only by equality status and is closed under meet/join.  A compiled
counterexample proves that it is not semantically complete for all
`Trace → Trace → Prop` guards.

The freeze grammar targets the exact live positional carrier `CtorPos → Prop`.
Its atoms cover every constructor position, it is closed under union/intersection,
and it exposes the live write-closure and canonical confluence-repair operators.
Every pointwise-decidable positional selection can be compiled exactly into
finite freeze syntax.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

open OperatorKO7 Trace
open OperatorKO7.EqGuardedConfluence
open OperatorKO7.Meta.DistinctionBoundary.FreezePositions
open OperatorKO7.Meta.DistinctionBoundary.WriteClosure
open OperatorKO7.Meta.DistinctionBoundary.ConservativeRepair

/-! ## Guard grammar -/

/-- Constructor-closed syntax for comparator guards. -/
inductive GuardGrammar where
  | deny
  | allow
  | disequality
  | meet (left right : GuardGrammar)
  | join (left right : GuardGrammar)

/-- Interpret guard syntax into the exact comparator guard carrier. -/
def interpretGuard : GuardGrammar → Trace → Trace → Prop
  | .deny, _, _ => False
  | .allow, _, _ => True
  | .disequality, a, b => a ≠ b
  | .meet left right, a, b => interpretGuard left a b ∧ interpretGuard right a b
  | .join left right, a, b => interpretGuard left a b ∨ interpretGuard right a b

/-- Syntax closure under meet has the intended pointwise semantics. -/
theorem interpretGuard_meet (left right : GuardGrammar) (a b : Trace) :
    interpretGuard (.meet left right) a b ↔
      interpretGuard left a b ∧ interpretGuard right a b :=
  Iff.rfl

/-- Syntax closure under join has the intended pointwise semantics. -/
theorem interpretGuard_join (left right : GuardGrammar) (a b : Trace) :
    interpretGuard (.join left right) a b ↔
      interpretGuard left a b ∨ interpretGuard right a b :=
  Iff.rfl

/-- The grammar's disequality constructor is exactly the live `SafeStepGuard`. -/
theorem disequality_guard_exact_safeStepGuard (a b : Trace) :
    interpretGuard .disequality a b ↔
      OperatorKO7.Meta.SafeStep.GaugeFixingGuard.SafeStepGuard a b := by
  constructor
  · intro h
    exact OperatorKO7.Meta.SafeStep.GaugeFixingGuard.distinctionLicense_to_safeStepGuard h
  · intro h
    exact OperatorKO7.Meta.SafeStep.GaugeFixingGuard.safeStepGuard_to_distinctionLicense h

/-- A semantic invariant of this bounded grammar: interpretation depends only
on whether the compared values are equal. -/
def EqualityStatusInvariant (g : Trace → Trace → Prop) : Prop :=
  ∀ a b c d, (a = b ↔ c = d) → (g a b ↔ g c d)

/-- Every generated guard satisfies the equality-status invariant. -/
theorem interpretGuard_equalityStatusInvariant (code : GuardGrammar) :
    EqualityStatusInvariant (interpretGuard code) := by
  induction code with
  | deny =>
      intro _ _ _ _ _
      exact Iff.rfl
  | allow =>
      intro _ _ _ _ _
      exact Iff.rfl
  | disequality =>
      intro a b c d hEq
      exact not_congr hEq
  | meet left right ihLeft ihRight =>
      intro a b c d hEq
      constructor
      · rintro ⟨hl, hr⟩
        exact ⟨(ihLeft a b c d hEq).mp hl, (ihRight a b c d hEq).mp hr⟩
      · rintro ⟨hl, hr⟩
        exact ⟨(ihLeft a b c d hEq).mpr hl, (ihRight a b c d hEq).mpr hr⟩
  | join left right ihLeft ihRight =>
      intro a b c d hEq
      constructor
      · intro h
        cases h with
        | inl hl => exact Or.inl ((ihLeft a b c d hEq).mp hl)
        | inr hr => exact Or.inr ((ihRight a b c d hEq).mp hr)
      · intro h
        cases h with
        | inl hl => exact Or.inl ((ihLeft a b c d hEq).mpr hl)
        | inr hr => exact Or.inr ((ihRight a b c d hEq).mpr hr)

/-- A legitimate guard outside the bounded equality-status grammar. -/
def leftVoidGuard (a _b : Trace) : Prop :=
  a = void

/-- The counterexample guard distinguishes two equally off-diagonal pairs. -/
theorem leftVoidGuard_not_equalityStatusInvariant :
    ¬ EqualityStatusInvariant leftVoidGuard := by
  intro hInv
  have hEq : (void = delta void) ↔ (delta void = void) := by
    constructor <;> intro h <;> cases h
  have hTransfer := hInv void (delta void) (delta void) void hEq
  have hLeft : leftVoidGuard void (delta void) := rfl
  have hRight : leftVoidGuard (delta void) void := hTransfer.mp hLeft
  change delta void = void at hRight
  cases hRight

/-- Semantic completeness for *all* comparator guards is false; the bounded
claim is closed by a compiled counterexample rather than by an exhaustive-list
assertion. -/
theorem guardGrammar_not_semantically_complete :
    ¬ ∀ g : Trace → Trace → Prop, ∃ code : GuardGrammar, interpretGuard code = g := by
  intro hAll
  obtain ⟨code, hcode⟩ := hAll leftVoidGuard
  apply leftVoidGuard_not_equalityStatusInvariant
  rw [← hcode]
  exact interpretGuard_equalityStatusInvariant code

/-! ## Exact positional freeze grammar -/

/-- Atomic syntax has one constructor for each live positional carrier value. -/
inductive FreezeAtom where
  | void
  | delta
  | integrate
  | merge
  | appL
  | appR
  | recD
  | eqW

/-- Atom interpretation target. -/
def freezeAtomPosition : FreezeAtom → CtorPos
  | .void => .void
  | .delta => .delta
  | .integrate => .integrate
  | .merge => .merge
  | .appL => .appL
  | .appR => .appR
  | .recD => .recD
  | .eqW => .eqW

/-- Interpret one atom as the singleton positional selection. -/
def interpretFreezeAtom (atom : FreezeAtom) (c : CtorPos) : Prop :=
  c = freezeAtomPosition atom

/-- Finite constructor completeness: every live positional carrier value has an atom. -/
theorem freezeAtom_complete (c : CtorPos) :
    ∃ atom : FreezeAtom, interpretFreezeAtom atom c := by
  cases c with
  | void => exact ⟨.void, rfl⟩
  | delta => exact ⟨.delta, rfl⟩
  | integrate => exact ⟨.integrate, rfl⟩
  | merge => exact ⟨.merge, rfl⟩
  | appL => exact ⟨.appL, rfl⟩
  | appR => exact ⟨.appR, rfl⟩
  | recD => exact ⟨.recD, rfl⟩
  | eqW => exact ⟨.eqW, rfl⟩

/-- Closed syntax for positional policies and the two live completion operations. -/
inductive FreezePolicyGrammar where
  | empty
  | atom (value : FreezeAtom)
  | union (left right : FreezePolicyGrammar)
  | inter (left right : FreezePolicyGrammar)
  | writeClose (policy : FreezePolicyGrammar)
  | repair (policy : FreezePolicyGrammar)

/-- Interpret freeze syntax into the exact live carrier `CtorPos → Prop`. -/
def interpretFreezePolicy : FreezePolicyGrammar → CtorPos → Prop
  | .empty, _ => False
  | .atom atom, c => interpretFreezeAtom atom c
  | .union left right, c => interpretFreezePolicy left c ∨ interpretFreezePolicy right c
  | .inter left right, c => interpretFreezePolicy left c ∧ interpretFreezePolicy right c
  | .writeClose policy, c => writeClosure (interpretFreezePolicy policy) c
  | .repair policy, c => confluenceRepair (interpretFreezePolicy policy) c

/-- Union syntax has exact set-union semantics. -/
theorem interpretFreezePolicy_union (left right : FreezePolicyGrammar) (c : CtorPos) :
    interpretFreezePolicy (.union left right) c ↔
      interpretFreezePolicy left c ∨ interpretFreezePolicy right c :=
  Iff.rfl

/-- Intersection syntax has exact set-intersection semantics. -/
theorem interpretFreezePolicy_inter (left right : FreezePolicyGrammar) (c : CtorPos) :
    interpretFreezePolicy (.inter left right) c ↔
      interpretFreezePolicy left c ∧ interpretFreezePolicy right c :=
  Iff.rfl

/-- `writeClose` syntax invokes the exact live write closure. -/
theorem interpretFreezePolicy_writeClose (policy : FreezePolicyGrammar) :
    interpretFreezePolicy (.writeClose policy) =
      writeClosure (interpretFreezePolicy policy) :=
  rfl

/-- `repair` syntax invokes the exact live least confluent repair. -/
theorem interpretFreezePolicy_repair (policy : FreezePolicyGrammar) :
    interpretFreezePolicy (.repair policy) =
      confluenceRepair (interpretFreezePolicy policy) :=
  rfl

/-- Every grammar write-closure node interprets to a write-closed selection. -/
theorem freezePolicy_writeClose_closed (policy : FreezePolicyGrammar) :
    WriteClosed (interpretFreezePolicy (.writeClose policy)) :=
  writeClosure_closed (interpretFreezePolicy policy)

/-- Every grammar repair node interprets to a confluent live positional policy. -/
theorem freezePolicy_repair_confluent (policy : FreezePolicyGrammar) :
    ConfluentOnPos (interpretFreezePolicy (.repair policy)) EqGuardedStep :=
  confluenceRepair_confluent (interpretFreezePolicy policy)

/-- Select one atom exactly when an external decidable positional predicate contains it. -/
def selectedAtom (S : CtorPos → Prop) [DecidablePred S]
    (atom : FreezeAtom) : FreezePolicyGrammar :=
  if S (freezeAtomPosition atom) then .atom atom else .empty

/-- Conditional atom compilation has exact singleton semantics. -/
theorem interpret_selectedAtom (S : CtorPos → Prop) [DecidablePred S]
    (atom : FreezeAtom) (c : CtorPos) :
    interpretFreezePolicy (selectedAtom S atom) c ↔
      S (freezeAtomPosition atom) ∧ c = freezeAtomPosition atom := by
  by_cases h : S (freezeAtomPosition atom)
  · simp [selectedAtom, h, interpretFreezePolicy, interpretFreezeAtom]
  · simp [selectedAtom, h, interpretFreezePolicy]

/-- Compile every pointwise-decidable live positional selection into finite syntax. -/
def compileFreezePolicy (S : CtorPos → Prop) [DecidablePred S] : FreezePolicyGrammar :=
  .union (selectedAtom S .void)
    (.union (selectedAtom S .delta)
      (.union (selectedAtom S .integrate)
        (.union (selectedAtom S .merge)
          (.union (selectedAtom S .appL)
            (.union (selectedAtom S .appR)
              (.union (selectedAtom S .recD) (selectedAtom S .eqW)))))))

/-- Operational completeness boundary: every decidable positional selection is
represented exactly, pointwise, by the closed freeze grammar. -/
theorem freezePolicy_semantic_complete (S : CtorPos → Prop) [DecidablePred S] :
    interpretFreezePolicy (compileFreezePolicy S) = S := by
  funext c
  apply propext
  cases c <;>
    simp [compileFreezePolicy, interpretFreezePolicy, interpret_selectedAtom,
      freezeAtomPosition]

/-- Concrete grammar request for exactly the live `recD` seed. -/
def recDPolicy : FreezePolicyGrammar :=
  .atom .recD

/-- The grammar names exactly the `recD` seed used by the positional counterexample. -/
theorem recDPolicy_exact :
    interpretFreezePolicy recDPolicy = recDSeed := by
  funext c
  apply propext
  cases c <;> simp [recDPolicy, interpretFreezePolicy, interpretFreezeAtom,
    freezeAtomPosition, recDSeed]

/-- Applying the grammar-level repair to the concrete seed yields confluence. -/
theorem repairedRecDPolicy_confluent :
    ConfluentOnPos (interpretFreezePolicy (.repair recDPolicy)) EqGuardedStep :=
  freezePolicy_repair_confluent recDPolicy

end OperatorKO7.Meta.LicensedBoundaryCalculus
