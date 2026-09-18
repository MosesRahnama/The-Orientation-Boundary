import OperatorKO7.Meta.DistinctionBoundary.GodelArithmetization
import Mathlib.Computability.Primrec

set_option autoImplicit false

/-!
# Standard primitive-recursion closure, first arithmetic layer

This file connects the polynomial arithmetic pairing used by the live Gödel
coding to Mathlib's standard primitive-recursive function class.  It is the
first load-bearing layer of the larger closure target.  The recursive syntax,
substitution, proof-checking, and proof-relation functions are not asserted
primitive recursive here until their tagged-code recursors are separately
proved to lie in the same class.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- The polynomial pairing used by the live arithmetic coding is a genuine
binary primitive-recursive function. -/
theorem cpair_primrec : Primrec₂ cpair := by
  have hadd : Primrec₂ (fun a b : Nat => a + b) := Primrec.nat_add
  have hsq : Primrec₂ (fun a b : Nat => (a + b) * (a + b)) :=
    Primrec.nat_mul.comp₂ hadd hadd
  have hpair : Primrec₂ (fun a b : Nat => (a + b) * (a + b) + b) :=
    Primrec.nat_add.comp₂ hsq Primrec₂.right
  exact hpair.of_eq (fun _ _ => rfl)

/-- The positive cons constructor used by all live tagged syntax codes is a
genuine binary primitive-recursive function. -/
theorem ccons_primrec : Primrec₂ ccons := by
  exact (Primrec.succ.comp₂ cpair_primrec).of_eq (fun _ _ => rfl)

/-- The numeral coding function of the live arithmetization is primitive
recursive.  This is the layer the substitution and representability arguments
consume: every numeral reaches its code through a primitive recursion over the
same `ccons` algebra. -/
theorem numCode_primrec : Primrec numCode := by
  have hstep : Primrec₂ (fun _ ih : Nat => ccons 1 ih) :=
    ccons_primrec.comp₂ (Primrec.const 1).to₂ Primrec₂.right
  have h := Primrec.nat_rec₁ (ccons 0 0) hstep
  refine h.of_eq (fun n => ?_)
  induction n with
  | zero => rfl
  | succ k ih => exact congrArg (ccons 1) ih

/-- Primitive-recursive closure package for the arithmetic code algebra: the
pairing, the tagged cons, and the numeral coder all lie in Mathlib's standard
primitive-recursive class.  The recursive syntax, substitution, proof-checking,
and proof-relation layers remain outside this package until their tagged-code
recursors are proved to lie in the same class. -/
theorem code_algebra_primrec :
    Primrec₂ cpair ∧ Primrec₂ ccons ∧ Primrec numCode :=
  ⟨cpair_primrec, ccons_primrec, numCode_primrec⟩

#check cpair_primrec
#check ccons_primrec
#check numCode_primrec
#check code_algebra_primrec
#print axioms numCode_primrec
#print axioms code_algebra_primrec

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
