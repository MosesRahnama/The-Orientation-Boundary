import Mathlib

/-!
# Minimal role-collapsed equality-witness syntax

The declared grammar has exactly three constructors/roles: the equal verdict,
the different verdict, and a binary equality-witness query. No separate base
symbols are needed because the verdict constants themselves can serve as closed
query inputs.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

/-- Three-symbol recursive term grammar for the minimal equality-witness system. -/
inductive MiniEqWTerm where
  | same
  | different
  | eqW : MiniEqWTerm → MiniEqWTerm → MiniEqWTerm
  deriving DecidableEq, Repr

/-- Count of equality-witness/query nodes. -/
def miniEqWCount : MiniEqWTerm → Nat
  | .same => 0
  | .different => 0
  | .eqW a b => miniEqWCount a + miniEqWCount b + 1

/-- The two verdict constants are distinct. -/
theorem miniEqW_same_ne_different :
    MiniEqWTerm.same ≠ MiniEqWTerm.different := by
  intro h
  cases h

/-- The canonical closed diagonal query. -/
def miniEqWClosedDiagonal : MiniEqWTerm :=
  .eqW .same .same

/-- A canonical closed off-diagonal query. -/
def miniEqWClosedOffDiagonal : MiniEqWTerm :=
  .eqW .same .different

/-- The grammar is genuinely recursive and therefore intentionally has no
`Fintype MiniEqWTerm` instance. This concrete family witnesses arbitrarily many
query nodes. -/
def miniEqWNested : Nat → MiniEqWTerm
  | 0 => .same
  | n + 1 => .eqW (miniEqWNested n) .different

@[simp] theorem miniEqWCount_nested (n : Nat) :
    miniEqWCount (miniEqWNested n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [miniEqWNested, miniEqWCount, ih]

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
