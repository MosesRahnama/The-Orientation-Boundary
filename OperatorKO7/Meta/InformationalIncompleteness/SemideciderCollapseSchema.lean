import OperatorKO7.Meta.InformationalIncompleteness.ComparisonAsymmetry

set_option autoImplicit false

namespace OperatorKO7.Meta.InformationalIncompleteness.SemideciderCollapseSchema

open OperatorKO7.Meta.InformationalIncompleteness.ComparisonAsymmetry

/-- Abstract two-semidecider collapse schema for a proposition family. -/
structure JointSemideciderSchema (A : Type) (P : A -> A -> Prop) where
  posSD : forall a b, Semidecider (P a b)
  negSD : forall a b, Semidecider (Not (P a b))
  cover : forall a b,
    (exists n, (posSD a b).test n = true)
      ∨ (exists n, (negSD a b).test n = true)

/-- A jointly total positive/negative semidecider pair manufactures a decision procedure for `P`. -/
def JointSemideciderSchema.toDecidableRel {A : Type} {P : A -> A -> Prop}
    (S : JointSemideciderSchema A P) :
    forall a b, Decidable (P a b) :=
  fun a b =>
    let eqSD : Semidecider (P a b) := S.posSD a b
    let neqSD : Semidecider (Not (P a b)) := S.negSD a b
    let hex : exists n, ((eqSD.test n || neqSD.test n) = true) := by
      rcases S.cover a b with ⟨n, hn⟩ | ⟨n, hn⟩
      · have heq : eqSD.test n = true := by simpa [eqSD] using hn
        exact ⟨n, by rw [heq]; simp⟩
      · have hneq : neqSD.test n = true := by simpa [neqSD] using hn
        exact ⟨n, by rw [hneq]; cases eqSD.test n <;> rfl⟩
    let N := Nat.find hex
    have hN : (eqSD.test N || neqSD.test N) = true := Nat.find_spec hex
    match hp : eqSD.test N with
    | true => isTrue (eqSD.spec.mp ⟨N, hp⟩)
    | false =>
        isFalse (by
          rw [hp, Bool.false_or] at hN
          exact neqSD.spec.mp ⟨N, hN⟩)

/-- The equality/disequality case is exactly the comparison-asymmetry collapse. -/
theorem equality_semidecider_collapse_is_decidableEq {A : Type}
    (S : JointSemideciderSchema A (fun a b => a = b)) :
    Nonempty (DecidableEq A) :=
  ⟨fun a b => JointSemideciderSchema.toDecidableRel S a b⟩

/-- Halting-style portability: a jointly total semidecider pair for any halting predicate decides it. -/
def halting_semidecider_collapse_decides
    {Machine Input : Type} (H : Machine -> Input -> Prop)
    (S : JointSemideciderSchema (Machine × Input)
      (fun x y : Machine × Input => x = y ∧ H x.1 x.2)) :
    forall x y : Machine × Input, Decidable (x = y ∧ H x.1 x.2) :=
  JointSemideciderSchema.toDecidableRel S

#print axioms JointSemideciderSchema.toDecidableRel
#print axioms equality_semidecider_collapse_is_decidableEq
#print axioms halting_semidecider_collapse_decides

end OperatorKO7.Meta.InformationalIncompleteness.SemideciderCollapseSchema
