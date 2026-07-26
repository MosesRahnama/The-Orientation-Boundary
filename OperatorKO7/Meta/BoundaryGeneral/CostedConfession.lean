/-!
# Costed confession arithmetic

`compositionBurden B₁ B₂ shared` uses truncated natural subtraction to model a
combined burden. `composition_le` gives its unconditional upper bound.
`composition_eq_of_disjoint` covers the zero-sharing case, while
`composition_lt_of_shared` requires positive sharing bounded by `B₁ + B₂`.

`IsLowerBound` is a predicate over an admissible burden class.
`canonical_lower_bound` projects a caller-supplied proof of that predicate.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.CostedConfession

/-- The serial-composition burden of two confessions with total burdens `B₁`, `B₂` sharing `shared`
units of carrier (counted once in the composition). -/
def compositionBurden (B₁ B₂ shared : Nat) : Nat := B₁ + B₂ - shared

/-- **Additive composition bound (Theorem 4.5).** The composition burden is at most the sum of the
parts. -/
theorem composition_le (B₁ B₂ shared : Nat) :
    compositionBurden B₁ B₂ shared ≤ B₁ + B₂ := by
  unfold compositionBurden; omega

/-- **Zero-sharing equality (Theorem 4.5).** At `shared = 0`, the composition
burden equals the sum. -/
theorem composition_eq_of_disjoint (B₁ B₂ : Nat) :
    compositionBurden B₁ B₂ 0 = B₁ + B₂ := by
  unfold compositionBurden; omega

/-- **Strict saving under genuine sharing.** When the shared carrier is positive (and within the
combined budget) the composition strictly saves over the sum: shared redundancy is counted once. -/
theorem composition_lt_of_shared (B₁ B₂ shared : Nat) (hpos : 0 < shared)
    (hle : shared ≤ B₁ + B₂) : compositionBurden B₁ B₂ shared < B₁ + B₂ := by
  unfold compositionBurden; omega

/-- A burden value is a lower bound when every admissible burden is at least that value. -/
def IsLowerBound (Bstar : Nat) (admissible : Nat → Prop) : Prop :=
  ∀ B, admissible B → Bstar ≤ B

/-- **Supplied lower-bound projection (Theorem 4.4).** A proof that every
admissible burden is at least `Bstar` inhabits `IsLowerBound Bstar admissible`. -/
theorem canonical_lower_bound (Bstar : Nat) (admissible : Nat → Prop)
    (h : ∀ B, admissible B → Bstar ≤ B) : IsLowerBound Bstar admissible := h

#print axioms composition_le
#print axioms canonical_lower_bound

end OperatorKO7.Meta.BoundaryGeneral.CostedConfession
