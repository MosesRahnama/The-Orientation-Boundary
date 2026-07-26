/-!
# Shared affine mass profiles

`TraceFamily` supplies an arbitrary depth-indexed carrier and a natural-valued
mass function. If two families are separately assumed to satisfy the same
affine equation, `whole_term_indistinguishable` proves equality of their mass
values by rewriting those assumptions. The theorem does not construct a
recursor family, a circular family, or a semantics of role labels.

`projection_escape` is an independent finite witness: two pairs of natural
numbers can have equal first coordinates and unequal second coordinates. It
does not connect those pairs to `TraceFamily`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.WholeTermIndistinguishability

/-- A depth-indexed carrier equipped with a natural-valued observation function. -/
structure TraceFamily where
  Trace : Nat → Type
  mass : (n : Nat) → Trace n → Nat

/-- Every observation in the family is assumed equal to `c * n + d` at depth `n`. -/
def AffineMass (F : TraceFamily) (c d : Nat) : Prop :=
  ∀ n (t : F.Trace n), F.mass n t = c * n + d

/-- Two families satisfying the same affine observation equation have equal observations at a
chosen depth. -/
theorem whole_term_indistinguishable (R C : TraceFamily) (c d : Nat)
    (hR : AffineMass R c d) (hC : AffineMass C c d)
    (n : Nat) (tr : R.Trace n) (tc : C.Trace n) :
    R.mass n tr = C.mass n tc := by
  rw [hR n tr, hC n tc]

/-- Two pairs of natural numbers can agree in their first coordinate and differ in their second. -/
theorem projection_escape :
    ∃ t₁ t₂ : Nat × Nat, t₁.1 = t₂.1 ∧ t₁.2 ≠ t₂.2 :=
  ⟨(5, 0), (5, 1), rfl, by decide⟩

#print axioms whole_term_indistinguishable
#print axioms projection_escape

end OperatorKO7.Meta.BoundaryGeneral.WholeTermIndistinguishability
