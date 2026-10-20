import OperatorKO7.Kernel
import Mathlib.Logic.Function.Defs

set_option autoImplicit false

/-!
# String and cycle rewriting inapplicability

Cycle rewriting and string rewriting require a unary signature (every
function symbol has arity at most 1). KO7 has binary and ternary constructors.
The universal theorem below rules out every injective, arity-preserving direct
encoding into every unary target signature. It does not rule out an encoding
that changes arity or introduces auxiliary structure.
-/

namespace OperatorKO7.Methods.UnarySignatureInapplicability

/-- A signature is unary when every symbol has arity at most 1. -/
def UnarySignature {σ : Type} (arity : σ → Nat) : Prop :=
  ∀ f : σ, arity f ≤ 1

/-- A direct signature encoding that is injective on symbols and preserves
every arity exactly. -/
structure ArityPreservingEmbedding {σ τ : Type} (sourceArity : σ → Nat)
    (targetArity : τ → Nat) where
  toFun : σ → τ
  injective : Function.Injective toFun
  arity_eq : ∀ f : σ, targetArity (toFun f) = sourceArity f

/-- Direct arity-preserving embeddability into a target signature. -/
def DirectArityPreservingEncoding {σ τ : Type} (sourceArity : σ → Nat)
    (targetArity : τ → Nat) : Prop :=
  Nonempty (ArityPreservingEmbedding sourceArity targetArity)

/-- Existence of any arity-preserving symbol map, without an injectivity
requirement. -/
def ArityPreservingMapExists {σ τ : Type} (sourceArity : σ → Nat)
    (targetArity : τ → Nat) : Prop :=
  ∃ f : σ → τ, ∀ s : σ, targetArity (f s) = sourceArity s

theorem unarySignature_of_arityPreservingMap {σ τ : Type}
    {sourceArity : σ → Nat} {targetArity : τ → Nat}
    (f : σ → τ) (hArity : ∀ s : σ, targetArity (f s) = sourceArity s)
    (hTarget : UnarySignature targetArity) : UnarySignature sourceArity := by
  intro s
  rw [← hArity s]
  exact hTarget (f s)

/-- Unary target signatures reflect across every direct arity-preserving
embedding. -/
theorem unarySignature_of_arityPreservingEmbedding {σ τ : Type}
    {sourceArity : σ → Nat} {targetArity : τ → Nat}
    (E : ArityPreservingEmbedding sourceArity targetArity)
    (hTarget : UnarySignature targetArity) : UnarySignature sourceArity := by
  intro f
  rw [← E.arity_eq f]
  exact hTarget (E.toFun f)

inductive KO7Fun : Type
  | void
  | delta
  | integrate
  | merge
  | app
  | recΔ
  | eqW
  deriving DecidableEq, Repr

def ko7FunArity : KO7Fun → Nat
  | .void => 0
  | .delta => 1
  | .integrate => 1
  | .merge => 2
  | .app => 2
  | .recΔ => 3
  | .eqW => 2

theorem merge_arity_gt_one : 1 < ko7FunArity KO7Fun.merge := by decide

theorem recΔ_arity_gt_one : 1 < ko7FunArity KO7Fun.recΔ := by decide

theorem ko7_not_unary_signature : ¬ UnarySignature ko7FunArity := by
  intro h
  have : ko7FunArity KO7Fun.merge ≤ 1 := h KO7Fun.merge
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt this merge_arity_gt_one)

/-- KO7 has no direct arity-preserving encoding into any unary signature. -/
theorem ko7_no_direct_arity_preserving_encoding_into_unary
    {τ : Type} (targetArity : τ → Nat) (hTarget : UnarySignature targetArity) :
    ¬ DirectArityPreservingEncoding ko7FunArity targetArity := by
  rintro ⟨E⟩
  exact ko7_not_unary_signature
    (unarySignature_of_arityPreservingEmbedding E hTarget)

/-- Stronger form: no arity-preserving symbol map at all exists from KO7 into
any unary target signature. -/
theorem ko7_no_arity_preserving_map_into_unary
    {τ : Type} (targetArity : τ → Nat) (hTarget : UnarySignature targetArity) :
    ¬ ArityPreservingMapExists ko7FunArity targetArity := by
  rintro ⟨f, hArity⟩
  exact ko7_not_unary_signature
    (unarySignature_of_arityPreservingMap f hArity hTarget)

/-- The direct unary-signature precondition for cycle rewriting fails on KO7. -/
theorem cycleRewriting_inapplicable : ¬ UnarySignature ko7FunArity :=
  ko7_not_unary_signature

/-- The direct unary-signature precondition for string rewriting fails on KO7. -/
theorem stringRewriting_inapplicable : ¬ UnarySignature ko7FunArity :=
  ko7_not_unary_signature

theorem cycleRewriting_no_direct_arity_preserving_encoding
    {τ : Type} (targetArity : τ → Nat) (hTarget : UnarySignature targetArity) :
    ¬ DirectArityPreservingEncoding ko7FunArity targetArity :=
  ko7_no_direct_arity_preserving_encoding_into_unary targetArity hTarget

theorem stringRewriting_no_direct_arity_preserving_encoding
    {τ : Type} (targetArity : τ → Nat) (hTarget : UnarySignature targetArity) :
    ¬ DirectArityPreservingEncoding ko7FunArity targetArity :=
  ko7_no_direct_arity_preserving_encoding_into_unary targetArity hTarget

end OperatorKO7.Methods.UnarySignatureInapplicability
