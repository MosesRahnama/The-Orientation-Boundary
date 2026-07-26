import OperatorKO7.Meta.BoundaryOperator.UniversalCertificationChain
import Mathlib.Order.Lattice

/-!
# Four-element obligation-kind lattice

`ObligationKind` is a four-constructor type equipped with a hand-written diamond
order. Its labels are `w0Classify`, `w1Route`, `dtcFaithful`, and `w2Confess`.

The defined order has the following diamond equations:
`w1Route ⊓ dtcFaithful = w0Classify` and `w1Route ⊔ dtcFaithful = w2Confess`, with
`w1Route` and `dtcFaithful` incomparable.

`plugObligationLattice` ignores its `CertificationChain` argument and returns
this fixed type. The declarations supply neither plug-specific obligations nor
discharge evidence linking the lattice labels to a certification chain.
-/

namespace OperatorKO7.Meta.BoundaryOperator.UniversalP4CObligationLattice

open OperatorKO7.Meta.BoundaryOperator.UniversalCertificationChain

/-- Four labels used by the abstract obligation-kind lattice. -/
inductive ObligationKind
  | w0Classify
  | w1Route
  | dtcFaithful
  | w2Confess
  deriving DecidableEq, Repr, Fintype

namespace ObligationKind

/-- Decidable dependency order: `w0Classify` is below everything, `w2Confess` is
above everything, `w1Route` and `dtcFaithful` are incomparable. -/
def leB : ObligationKind → ObligationKind → Bool
  | .w0Classify, _ => true
  | _, .w2Confess => true
  | .w1Route, .w1Route => true
  | .dtcFaithful, .dtcFaithful => true
  | _, _ => false

/-- Join: least upper bound. The two independent obligations join to confession. -/
def joinK : ObligationKind → ObligationKind → ObligationKind
  | .w0Classify, b => b
  | a, .w0Classify => a
  | .w2Confess, _ => .w2Confess
  | _, .w2Confess => .w2Confess
  | .w1Route, .w1Route => .w1Route
  | .dtcFaithful, .dtcFaithful => .dtcFaithful
  | .w1Route, .dtcFaithful => .w2Confess
  | .dtcFaithful, .w1Route => .w2Confess

/-- Meet: greatest lower bound. The two independent obligations meet at classify. -/
def meetK : ObligationKind → ObligationKind → ObligationKind
  | .w2Confess, b => b
  | a, .w2Confess => a
  | .w0Classify, _ => .w0Classify
  | _, .w0Classify => .w0Classify
  | .w1Route, .w1Route => .w1Route
  | .dtcFaithful, .dtcFaithful => .dtcFaithful
  | .w1Route, .dtcFaithful => .w0Classify
  | .dtcFaithful, .w1Route => .w0Classify

-- These finite laws establish the order fields before instance construction.
theorem leB_refl : ∀ a, leB a a = true := by decide
theorem leB_trans : ∀ a b c, leB a b = true → leB b c = true → leB a c = true := by decide
theorem leB_antisymm : ∀ a b, leB a b = true → leB b a = true → a = b := by decide
theorem leB_join_left : ∀ a b, leB a (joinK a b) = true := by decide
theorem leB_join_right : ∀ a b, leB b (joinK a b) = true := by decide
theorem joinK_le : ∀ a b c, leB a c = true → leB b c = true → leB (joinK a b) c = true := by decide
theorem meetK_le_left : ∀ a b, leB (meetK a b) a = true := by decide
theorem meetK_le_right : ∀ a b, leB (meetK a b) b = true := by decide
theorem le_meetK : ∀ a b c, leB a b = true → leB a c = true → leB a (meetK b c) = true := by decide

instance : Lattice ObligationKind where
  le a b := leB a b = true
  le_refl := leB_refl
  le_trans a b c := leB_trans a b c
  le_antisymm a b := leB_antisymm a b
  sup := joinK
  inf := meetK
  le_sup_left := leB_join_left
  le_sup_right := leB_join_right
  sup_le a b c := joinK_le a b c
  inf_le_left := meetK_le_left
  inf_le_right := meetK_le_right
  le_inf a b c := le_meetK a b c

instance : DecidableLE ObligationKind :=
  fun a b => inferInstanceAs (Decidable (leB a b = true))

/-- The two middle constructors are incomparable in the defined order. -/
theorem w1_dtc_incomparable :
    ¬ (w1Route ≤ dtcFaithful) ∧ ¬ (dtcFaithful ≤ w1Route) := by
  decide

/-- Diamond meet: the two independent obligations meet at the W0 classification. -/
theorem w1_inf_dtc : w1Route ⊓ dtcFaithful = w0Classify := by decide

/-- Diamond join: the two independent obligations join at the W2 confession. -/
theorem w1_sup_dtc : w1Route ⊔ dtcFaithful = w2Confess := by decide

/-- `w0Classify` is the bottom obligation (every kind dominates it). -/
theorem w0_is_bottom (k : ObligationKind) : w0Classify ≤ k := by
  cases k <;> decide

/-- `w2Confess` is the top obligation (it dominates every kind). -/
theorem w2_is_top (k : ObligationKind) : k ≤ w2Confess := by
  cases k <;> decide

end ObligationKind

/-- Constant type-valued function that ignores its chain argument and returns
`ObligationKind`. -/
def plugObligationLattice (_ : CertificationChain) : Type := ObligationKind

/-- Reflexive equality induced by the constant definition of
`plugObligationLattice`. -/
theorem obligation_lattice_plug_independent (C₁ C₂ : CertificationChain) :
    plugObligationLattice C₁ = plugObligationLattice C₂ := rfl

/-- The constant type-valued function returns `ObligationKind` on three fixtures. -/
theorem plug_obligation_lattices_agree :
    plugObligationLattice lawChain = plugObligationLattice pharmaChain ∧
    plugObligationLattice pharmaChain = plugObligationLattice qecChain ∧
    plugObligationLattice lawChain = ObligationKind :=
  ⟨rfl, rfl, rfl⟩

/-- String identifier for the diamond-meet theorem. -/
def universal_p4c_obligation_lattice_anchor : String :=
  "OperatorKO7.Meta.BoundaryOperator.UniversalP4CObligationLattice.ObligationKind.w1_inf_dtc"

end OperatorKO7.Meta.BoundaryOperator.UniversalP4CObligationLattice
