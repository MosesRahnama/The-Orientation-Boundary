import OperatorKO7.Meta.OperationalInexpressibility.ResponseProvenance

/-!
# Declared response universe

This module classifies only the response syntax declared below. The `.other`
constructor keeps the universe open to responses not analyzed by the two named
constructors. Consequently the classification theorem is not a completeness
claim about termination methods in general.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.DeclaredResponseUniverse

open OperatorKO7.Meta.OperationalInexpressibility.ResponseProvenance

/-- The response forms analyzed by this package, plus an explicit remainder. -/
inductive ResponseSyntax
  | construction (rank : AdmissibleConstructionRank)
  | confession (response : ConfessionResponse)
  | other

/-- Classification labels for precisely `ResponseSyntax`. -/
inductive ResponseClass
  | construction
  | confession
  | other
  deriving DecidableEq, Repr

/-- Total classifier on the declared syntax. -/
def classify : ResponseSyntax -> ResponseClass
  | .construction _ => .construction
  | .confession _ => .confession
  | .other => .other

/-- Exhaustiveness is expressly limited to the declared response syntax. -/
theorem declaredResponseUniverse_trichotomy (response : ResponseSyntax) :
    classify response = ResponseClass.construction
      ∨ classify response = ResponseClass.confession
      ∨ classify response = ResponseClass.other := by
  cases response <;> simp [classify]

/-- Constructor-level form of the syntax-bounded classification theorem. -/
theorem declaredResponseUniverse_cases (response : ResponseSyntax) :
    (exists rank : AdmissibleConstructionRank,
        response = ResponseSyntax.construction rank)
      ∨ (exists confession : ConfessionResponse,
          response = ResponseSyntax.confession confession)
      ∨ response = ResponseSyntax.other := by
  cases response with
  | construction rank => exact Or.inl ⟨rank, rfl⟩
  | confession confession => exact Or.inr (Or.inl ⟨confession, rfl⟩)
  | other => exact Or.inr (Or.inr rfl)

/-- The remainder constructor is not silently classified as construction. -/
theorem other_not_construction :
    classify ResponseSyntax.other ≠ ResponseClass.construction := by
  intro h
  cases h

/-- The remainder constructor is not silently classified as confession. -/
theorem other_not_confession :
    classify ResponseSyntax.other ≠ ResponseClass.confession := by
  intro h
  cases h

/-- The two concrete construction witnesses inhabit the declared construction
branch while retaining their proved inequality. -/
theorem declaredConstructionBranch_nonunique :
    ResponseSyntax.construction canonicalConstructionRank ≠
      ResponseSyntax.construction shiftedConstructionRank := by
  intro h
  injection h with hRank
  exact canonicalConstructionRank_ne_shiftedConstructionRank hRank

/-- The proof-bearing KO7 confession inhabits the declared confession branch. -/
def declaredKO7Confession : ResponseSyntax :=
  ResponseSyntax.confession ko7ConfessionResponse

end OperatorKO7.Meta.OperationalInexpressibility.DeclaredResponseUniverse
