/-!
# Theory III: Whole-term indistinguishability strengthening

Boundary-general cross-paper packet, Theory III. A whole-term mass observer sees a trace's total
mass but not its role labels (which occurrence is step, payload, or control). Two trace families
with the same affine mass profile (same linear coefficient and offset) are therefore identical to
such an observer at every depth: the terminating duplicating recursor and a circular-reference
carrier, both growing one whole-term unit per step, cannot be separated by whole-term mass. A
coordinate projection that names the step argument *can* separate traces the mass observer
identifies.

`whole_term_indistinguishable` is the barrier (mass observer cannot separate); `projection_escape`
is the escape (a step-coordinate projection separates equal-mass traces).

No `sorry`, `axiom`, or `native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.WholeTermIndistinguishability

/-- A trace family with a whole-term mass observer: `mass n t` is the total mass of trace `t` at
depth `n`, invariant under internal role labels. -/
structure TraceFamily where
  Trace : Nat → Type
  mass : (n : Nat) → Trace n → Nat

/-- The family has an affine mass profile `mass = c·n + d`. -/
def AffineMass (F : TraceFamily) (c d : Nat) : Prop :=
  ∀ n (t : F.Trace n), F.mass n t = c * n + d

/-- **Whole-term indistinguishability (Theorem 3.4).** Two families with the same affine mass
coefficient and offset have identical mass at every depth: a whole-term mass observer returns the
same value on both, so it cannot decide whether a repeated occurrence is control or payload. -/
theorem whole_term_indistinguishable (R C : TraceFamily) (c d : Nat)
    (hR : AffineMass R c d) (hC : AffineMass C c d)
    (n : Nat) (tr : R.Trace n) (tc : C.Trace n) :
    R.mass n tr = C.mass n tc := by
  rw [hR n tr, hC n tc]

/-- **Projection escape (Theorem 3.5).** A coordinate projection that names the step argument can
separate traces that a whole-term mass observer identifies: there exist two traces (modeled as
`(whole-term mass, step projection)` pairs) with equal mass but different projected step values. -/
theorem projection_escape :
    ∃ t₁ t₂ : Nat × Nat, t₁.1 = t₂.1 ∧ t₁.2 ≠ t₂.2 :=
  ⟨(5, 0), (5, 1), rfl, by decide⟩

#print axioms whole_term_indistinguishable
#print axioms projection_escape

end OperatorKO7.Meta.BoundaryGeneral.WholeTermIndistinguishability
