import OperatorKO7.Meta.UniqueNormalization.RationalUnification

/-!
# Axiom-free finite-unifier bridge

This module constructs the finite `UnifClosure` certificate for a finite common
instance directly from the recursive term and substitution definitions. It
avoids the convenience equalities whose current proof terms carry `propext` or
`Quot.sound`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.FiniteUnifierOmegaCore

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

universe u v

variable {sigma : Type u} {nu : Type v}

/-- Equality of substituted argument lists gives the pointwise kernel relation,
proved directly from `Subst.applyList`. -/
theorem forall2_applyList_eq (r : Subst sigma nu) :
    ∀ (xs ys : List (Term sigma nu)),
      Subst.applyList r xs = Subst.applyList r ys →
      List.Forall₂ (fun a b => Subst.apply r a = Subst.apply r b) xs ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => exact List.Forall₂.nil
      | cons y ys => cases h
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil => cases h
      | cons y ys =>
          change Subst.apply r x :: Subst.applyList r xs =
            Subst.apply r y :: Subst.applyList r ys at h
          injection h with hxy hrest
          exact List.Forall₂.cons hxy (ih ys hrest)

/-- The kernel of one finite substitution is an omega-unification closure. -/
theorem omegaUnifiableShared_of_subst_axfree {s t : Term sigma nu}
    (r : Subst sigma nu) (h : Subst.apply r s = Subst.apply r t) :
    OmegaUnifiableShared s t := by
  let E : Term sigma nu → Term sigma nu → Prop :=
    fun a b => Subst.apply r a = Subst.apply r b
  refine ⟨E, ?_, h⟩
  refine ⟨fun _ => rfl, fun hab => hab.symm, fun hab hbc => hab.trans hbc, ?_⟩
  intro f g xs ys hab
  change Term.app f (Subst.applyList r xs) =
    Term.app g (Subst.applyList r ys) at hab
  injection hab with hfg hargs
  exact ⟨hfg, forall2_applyList_eq r xs ys hargs⟩

/-- One substitution on the disjoint variable copies, using the left tag for
both finite images. -/
def renameApartSubst (a b : Subst sigma nu) : Subst sigma (nu ⊕ nu)
  | .inl x => Term.mapVar Sum.inl (a x)
  | .inr y => Term.mapVar Sum.inl (b y)

/-- Argument-list part of the left-copy substitution equation. -/
theorem applyList_leftCopy_axfree (a b : Subst sigma nu) :
    ∀ (xs : List (Term sigma nu)),
      (∀ x, x ∈ xs →
        Subst.apply (renameApartSubst a b) (Term.mapVar Sum.inl x) =
          Term.mapVar Sum.inl (Subst.apply a x)) →
      Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inl xs) =
        Term.mapVarList Sum.inl (Subst.applyList a xs) := by
  intro xs
  induction xs with
  | nil =>
      intro _
      rfl
  | cons x xs ih =>
      intro hall
      change Subst.apply (renameApartSubst a b) (Term.mapVar Sum.inl x) ::
          Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inl xs) =
        Term.mapVar Sum.inl (Subst.apply a x) ::
          Term.mapVarList Sum.inl (Subst.applyList a xs)
      have hx := hall x (List.Mem.head _)
      have hxs := ih (fun y hy => hall y (List.Mem.tail _ hy))
      calc
        Subst.apply (renameApartSubst a b) (Term.mapVar Sum.inl x) ::
            Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inl xs) =
          Term.mapVar Sum.inl (Subst.apply a x) ::
            Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inl xs) :=
          congrArg (fun z => z :: Subst.applyList (renameApartSubst a b)
            (Term.mapVarList Sum.inl xs)) hx
        _ = Term.mapVar Sum.inl (Subst.apply a x) ::
            Term.mapVarList Sum.inl (Subst.applyList a xs) :=
          congrArg (List.cons (Term.mapVar Sum.inl (Subst.apply a x))) hxs

/-- Applying the combined substitution to the left renamed copy gives the
renamed finite left instance. The proof uses the primitive mutual recursor. -/
theorem apply_leftCopy_axfree (a b : Subst sigma nu) :
    ∀ t : Term sigma nu,
      Subst.apply (renameApartSubst a b) (leftCopy t) =
        Term.mapVar Sum.inl (Subst.apply a t) := by
  intro t
  exact @Term.rec sigma nu
    (fun z => Subst.apply (renameApartSubst a b) (leftCopy z) =
      Term.mapVar Sum.inl (Subst.apply a z))
    (fun zs => Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inl zs) =
      Term.mapVarList Sum.inl (Subst.applyList a zs))
    (fun _ => rfl)
    (fun f args hargs => by
      change Term.app f
          (Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inl args)) =
        Term.app f (Term.mapVarList Sum.inl (Subst.applyList a args))
      exact congrArg (Term.app f) hargs)
    rfl
    (fun head tail hhead htail => by
      change Subst.apply (renameApartSubst a b) (Term.mapVar Sum.inl head) ::
          Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inl tail) =
        Term.mapVar Sum.inl (Subst.apply a head) ::
          Term.mapVarList Sum.inl (Subst.applyList a tail)
      calc
        Subst.apply (renameApartSubst a b) (Term.mapVar Sum.inl head) ::
            Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inl tail) =
          Term.mapVar Sum.inl (Subst.apply a head) ::
            Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inl tail) :=
          congrArg (fun z => z :: Subst.applyList (renameApartSubst a b)
            (Term.mapVarList Sum.inl tail)) hhead
        _ = Term.mapVar Sum.inl (Subst.apply a head) ::
            Term.mapVarList Sum.inl (Subst.applyList a tail) :=
          congrArg (List.cons (Term.mapVar Sum.inl (Subst.apply a head))) htail)
    t

/-- Argument-list part of the right-copy substitution equation. -/
theorem applyList_rightCopy_axfree (a b : Subst sigma nu) :
    ∀ (xs : List (Term sigma nu)),
      (∀ x, x ∈ xs →
        Subst.apply (renameApartSubst a b) (Term.mapVar Sum.inr x) =
          Term.mapVar Sum.inl (Subst.apply b x)) →
      Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inr xs) =
        Term.mapVarList Sum.inl (Subst.applyList b xs) := by
  intro xs
  induction xs with
  | nil =>
      intro _
      rfl
  | cons x xs ih =>
      intro hall
      change Subst.apply (renameApartSubst a b) (Term.mapVar Sum.inr x) ::
          Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inr xs) =
        Term.mapVar Sum.inl (Subst.apply b x) ::
          Term.mapVarList Sum.inl (Subst.applyList b xs)
      have hx := hall x (List.Mem.head _)
      have hxs := ih (fun y hy => hall y (List.Mem.tail _ hy))
      calc
        Subst.apply (renameApartSubst a b) (Term.mapVar Sum.inr x) ::
            Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inr xs) =
          Term.mapVar Sum.inl (Subst.apply b x) ::
            Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inr xs) :=
          congrArg (fun z => z :: Subst.applyList (renameApartSubst a b)
            (Term.mapVarList Sum.inr xs)) hx
        _ = Term.mapVar Sum.inl (Subst.apply b x) ::
            Term.mapVarList Sum.inl (Subst.applyList b xs) :=
          congrArg (List.cons (Term.mapVar Sum.inl (Subst.apply b x))) hxs

/-- Applying the combined substitution to the right renamed copy gives the
left-tagged finite right instance. The proof uses the primitive mutual recursor. -/
theorem apply_rightCopy_axfree (a b : Subst sigma nu) :
    ∀ t : Term sigma nu,
      Subst.apply (renameApartSubst a b) (rightCopy t) =
        Term.mapVar Sum.inl (Subst.apply b t) := by
  intro t
  exact @Term.rec sigma nu
    (fun z => Subst.apply (renameApartSubst a b) (rightCopy z) =
      Term.mapVar Sum.inl (Subst.apply b z))
    (fun zs => Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inr zs) =
      Term.mapVarList Sum.inl (Subst.applyList b zs))
    (fun _ => rfl)
    (fun f args hargs => by
      change Term.app f
          (Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inr args)) =
        Term.app f (Term.mapVarList Sum.inl (Subst.applyList b args))
      exact congrArg (Term.app f) hargs)
    rfl
    (fun head tail hhead htail => by
      change Subst.apply (renameApartSubst a b) (Term.mapVar Sum.inr head) ::
          Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inr tail) =
        Term.mapVar Sum.inl (Subst.apply b head) ::
          Term.mapVarList Sum.inl (Subst.applyList b tail)
      calc
        Subst.apply (renameApartSubst a b) (Term.mapVar Sum.inr head) ::
            Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inr tail) =
          Term.mapVar Sum.inl (Subst.apply b head) ::
            Subst.applyList (renameApartSubst a b) (Term.mapVarList Sum.inr tail) :=
          congrArg (fun z => z :: Subst.applyList (renameApartSubst a b)
            (Term.mapVarList Sum.inr tail)) hhead
        _ = Term.mapVar Sum.inl (Subst.apply b head) ::
            Term.mapVarList Sum.inl (Subst.applyList b tail) :=
          congrArg (List.cons (Term.mapVar Sum.inl (Subst.apply b head))) htail)
    t

/-- A finite two-substitution common instance gives the exact rename-apart
`OmegaUnifiable` certificate without extensionality or quotient axioms. -/
theorem omegaUnifiable_of_unifier_axfree {s t : Term sigma nu}
    (a b : Subst sigma nu) (h : Subst.apply a s = Subst.apply b t) :
    OmegaUnifiable s t := by
  apply omegaUnifiableShared_of_subst_axfree (renameApartSubst a b)
  calc
    Subst.apply (renameApartSubst a b) (leftCopy s) =
        Term.mapVar Sum.inl (Subst.apply a s) := apply_leftCopy_axfree a b s
    _ = Term.mapVar Sum.inl (Subst.apply b t) := congrArg (Term.mapVar Sum.inl) h
    _ = Subst.apply (renameApartSubst a b) (rightCopy t) :=
      (apply_rightCopy_axfree a b t).symm

end OperatorKO7.Meta.UniqueNormalization.FiniteUnifierOmegaCore
