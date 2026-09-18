import OperatorKO7.Meta.UniqueNormalization.Section7CutElimination

/-!
# Global proof data for the Section 7 invariant

This module gives the six generating clauses of `Down` as explicit proof data on
the full finite-term carrier. There is no transitivity constructor. Unlike the
finite `DownOnDerivation`, the data carry no fixed coalgebra, so a later cut
repair may introduce finitely many auxiliary terms and recover finite support
only after composition.

Relation: `Down R`.
Closure: exactly the six `DownStep` generating forms.
Strategy: full rewriting.
Trust: kernel checked; no external certificate or new axiom.
Scope: arbitrary signatures, variable types, and constructor TRSs.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

mutual

/-- Proof-relevant derivations for the six clauses generating global `Down`.
There is deliberately no transitivity constructor. -/
inductive GlobalDownDerivation
    (R : TRS (sigma ⊕ sigma) nu) :
    Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu → Type (max u v) where
  | refl {a} : GlobalDownDerivation R a a
  | symm {a b} (h : GlobalDownDerivation R a b) : GlobalDownDerivation R b a
  | rootComp {a c b}
      (hroot : rootStep R a c) (tail : GlobalDownDerivation R c b) :
      GlobalDownDerivation R a b
  | barComp {d : sigma} {as cs : List (Term (sigma ⊕ sigma) nu)} {b}
      (args : GlobalDownArgsDerivation R as cs)
      (tail : GlobalDownDerivation R (.app (.inr d) cs) b) :
      GlobalDownDerivation R (.app (.inr d) as) b
  | hatCl {c : sigma} {as bs : List (Term (sigma ⊕ sigma) nu)}
      (args : GlobalDownArgsDerivation R as bs) :
      GlobalDownDerivation R (.app (.inl c) as) (.app (.inl c) bs)
  | barCl {d : sigma} {as bs : List (Term (sigma ⊕ sigma) nu)}
      (args : GlobalDownArgsDerivation R as bs) :
      GlobalDownDerivation R (.app (.inr d) as) (.app (.inr d) bs)

/-- Pointwise global argument derivations. -/
inductive GlobalDownArgsDerivation
    (R : TRS (sigma ⊕ sigma) nu) :
    List (Term (sigma ⊕ sigma) nu) →
    List (Term (sigma ⊕ sigma) nu) → Type (max u v) where
  | nil : GlobalDownArgsDerivation R [] []
  | cons {a b as bs}
      (head : GlobalDownDerivation R a b)
      (tail : GlobalDownArgsDerivation R as bs) :
      GlobalDownArgsDerivation R (a :: as) (b :: bs)

end

mutual

/-- Structural height of a global derivation. -/
def GlobalDownDerivation.height
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu} :
    GlobalDownDerivation R a b → Nat
  | .refl => 1
  | .symm h => h.height + 1
  | .rootComp _ tail => tail.height + 1
  | .barComp args tail => Nat.max args.height tail.height + 1
  | .hatCl args => args.height + 1
  | .barCl args => args.height + 1

/-- Maximum structural height of pointwise global argument derivations. -/
def GlobalDownArgsDerivation.height
    {R : TRS (sigma ⊕ sigma) nu}
    {as bs : List (Term (sigma ⊕ sigma) nu)} :
    GlobalDownArgsDerivation R as bs → Nat
  | .nil => 0
  | .cons head tail => Nat.max head.height tail.height + 1

end

/-- Replay global proof data into the original impredicative fixed point. -/
def GlobalDownDerivation.toDown
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : GlobalDownDerivation R a b) : Down R a b :=
  GlobalDownDerivation.rec
    (motive_1 := fun x y _ => Down R x y)
    (motive_2 := fun xs ys _ => List.Forall₂ (Down R) xs ys)
    (Down.refl _)
    (fun _ ih => Down.symm ih)
    (fun hroot _ ih => Down.rootComp hroot ih)
    (fun _ _ hargs htail => Down.barComp hargs htail)
    (fun _ hargs => Down.hatCl hargs)
    (fun _ hargs => Down.barCl hargs)
    List.Forall₂.nil
    (fun _ _ hhead htail => List.Forall₂.cons hhead htail)
    h

/-- Replay global pointwise proof data into `List.Forall₂ Down`. -/
def GlobalDownArgsDerivation.toForall₂
    {R : TRS (sigma ⊕ sigma) nu}
    {as bs : List (Term (sigma ⊕ sigma) nu)}
    (h : GlobalDownArgsDerivation R as bs) : List.Forall₂ (Down R) as bs :=
  GlobalDownArgsDerivation.rec
    (motive_1 := fun x y _ => Down R x y)
    (motive_2 := fun xs ys _ => List.Forall₂ (Down R) xs ys)
    (Down.refl _)
    (fun _ ih => Down.symm ih)
    (fun hroot _ ih => Down.rootComp hroot ih)
    (fun _ _ hargs htail => Down.barComp hargs htail)
    (fun _ hargs => Down.hatCl hargs)
    (fun _ hargs => Down.barCl hargs)
    List.Forall₂.nil
    (fun _ _ hhead htail => List.Forall₂.cons hhead htail)
    h

/-- Pointwise nonempty proof data assemble into one argument derivation. -/
theorem GlobalDownArgsDerivation.nonempty_of_forall₂
    {R : TRS (sigma ⊕ sigma) nu}
    {as bs : List (Term (sigma ⊕ sigma) nu)}
    (h : List.Forall₂ (fun a b => Nonempty (GlobalDownDerivation R a b)) as bs) :
    Nonempty (GlobalDownArgsDerivation R as bs) := by
  induction h with
  | nil => exact ⟨.nil⟩
  | cons hab _ ih =>
      rcases hab with ⟨head⟩
      rcases ih with ⟨tail⟩
      exact ⟨.cons head tail⟩

/-- Every global `Down` fact has explicit proof data. This is least-fixed-point
elimination into the proof-data relation; it does not assume transitivity. -/
theorem Down.nonempty_globalDerivation
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : Down R a b) : Nonempty (GlobalDownDerivation R a b) := by
  apply Down.least (E := fun x y => Nonempty (GlobalDownDerivation R x y)) ?_ h
  intro p q hpq
  rcases hpq with heq | hinv | ⟨c, hroot, htail⟩ |
      ⟨d, as, cs, hpShape, hargs, htail⟩ | hhat | hbar
  · subst q
    exact ⟨.refl⟩
  · rcases hinv with ⟨d⟩
    exact ⟨.symm d⟩
  · rcases htail with ⟨tail⟩
    exact ⟨.rootComp hroot tail⟩
  · subst p
    rcases GlobalDownArgsDerivation.nonempty_of_forall₂ hargs with ⟨args⟩
    rcases htail with ⟨tail⟩
    exact ⟨.barComp args tail⟩
  · obtain ⟨f, as, bs, _, rfl, rfl, hargs⟩ := hhat
    rcases GlobalDownArgsDerivation.nonempty_of_forall₂ hargs with ⟨args⟩
    cases f with
    | inl c => exact ⟨.hatCl args⟩
    | inr d => exact ⟨.barCl args⟩
  · obtain ⟨f, as, bs, _, rfl, rfl, hargs⟩ := hbar
    rcases GlobalDownArgsDerivation.nonempty_of_forall₂ hargs with ⟨args⟩
    cases f with
    | inl c => exact ⟨.hatCl args⟩
    | inr d => exact ⟨.barCl args⟩

/-- Global proof data are extensionally complete for `Down`. -/
theorem down_iff_nonempty_globalDerivation
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu} :
    Down R a b ↔ Nonempty (GlobalDownDerivation R a b) := by
  constructor
  · exact Down.nonempty_globalDerivation
  · rintro ⟨d⟩
    exact d.toDown

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownDerivation
#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownArgsDerivation
#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownDerivation.height
#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownArgsDerivation.height
#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownDerivation.toDown
#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownArgsDerivation.toForall₂
#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownArgsDerivation.nonempty_of_forall₂
#check @OperatorKO7.Meta.UniqueNormalization.Down.nonempty_globalDerivation
#check @OperatorKO7.Meta.UniqueNormalization.down_iff_nonempty_globalDerivation

#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownDerivation
#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownArgsDerivation
#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownDerivation.height
#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownArgsDerivation.height
#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownDerivation.toDown
#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownArgsDerivation.toForall₂
#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownArgsDerivation.nonempty_of_forall₂
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.nonempty_globalDerivation
#print axioms OperatorKO7.Meta.UniqueNormalization.down_iff_nonempty_globalDerivation
