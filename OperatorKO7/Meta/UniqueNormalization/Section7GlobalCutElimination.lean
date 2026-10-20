import OperatorKO7.Meta.UniqueNormalization.Section7GlobalDownDerivation

/-!
# Global symmetry-normal proof data for Section 7

Global `Down` proof data contain an explicit symmetry constructor. For cut
composition, symmetry is normalized into explicit left and right root and
destructor-prefix constructors. The resulting data carry no fixed coalgebra and
have no transitivity constructor.

Relation: `Down R`.
Closure: the six `DownStep` clauses with symmetry pushed into left/right prefix
forms.
Strategy: full rewriting.
Trust: kernel checked; no external certificate or new axiom.
Scope: arbitrary signatures, variable types, and rewrite systems.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

mutual

/-- Symmetry-normal global proof data. -/
inductive GlobalDownCutDerivation
    (R : TRS (sigma ⊕ sigma) nu) :
    Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu → Type (max u v) where
  | refl {a} : GlobalDownCutDerivation R a a
  | rootLeft {a c b}
      (hroot : rootStep R a c) (tail : GlobalDownCutDerivation R c b) :
      GlobalDownCutDerivation R a b
  | rootRight {a b c}
      (hroot : rootStep R b c) (head : GlobalDownCutDerivation R a c) :
      GlobalDownCutDerivation R a b
  | barLeft {d : sigma} {as cs : List (Term (sigma ⊕ sigma) nu)} {b}
      (args : GlobalDownCutArgsDerivation R as cs)
      (tail : GlobalDownCutDerivation R (.app (.inr d) cs) b) :
      GlobalDownCutDerivation R (.app (.inr d) as) b
  | barRight {d : sigma} {as cs : List (Term (sigma ⊕ sigma) nu)} {a}
      (args : GlobalDownCutArgsDerivation R as cs)
      (head : GlobalDownCutDerivation R a (.app (.inr d) cs)) :
      GlobalDownCutDerivation R a (.app (.inr d) as)
  | hatCl {c : sigma} {as bs : List (Term (sigma ⊕ sigma) nu)}
      (args : GlobalDownCutArgsDerivation R as bs) :
      GlobalDownCutDerivation R (.app (.inl c) as) (.app (.inl c) bs)
  | barCl {d : sigma} {as bs : List (Term (sigma ⊕ sigma) nu)}
      (args : GlobalDownCutArgsDerivation R as bs) :
      GlobalDownCutDerivation R (.app (.inr d) as) (.app (.inr d) bs)

/-- Pointwise symmetry-normal global argument proof data. -/
inductive GlobalDownCutArgsDerivation
    (R : TRS (sigma ⊕ sigma) nu) :
    List (Term (sigma ⊕ sigma) nu) →
    List (Term (sigma ⊕ sigma) nu) → Type (max u v) where
  | nil : GlobalDownCutArgsDerivation R [] []
  | cons {a b as bs}
      (head : GlobalDownCutDerivation R a b)
      (tail : GlobalDownCutArgsDerivation R as bs) :
      GlobalDownCutArgsDerivation R (a :: as) (b :: bs)

end

mutual

/-- Structural reversal swaps left and right prefixes and recursively reverses
argument proofs. -/
def GlobalDownCutDerivation.flip
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu} :
    GlobalDownCutDerivation R a b → GlobalDownCutDerivation R b a
  | .refl => .refl
  | .rootLeft hroot tail => .rootRight hroot tail.flip
  | .rootRight hroot head => .rootLeft hroot head.flip
  | .barLeft args tail => .barRight args tail.flip
  | .barRight args head => .barLeft args head.flip
  | .hatCl args => .hatCl args.flip
  | .barCl args => .barCl args.flip

/-- Structural reversal of global argument proofs. -/
def GlobalDownCutArgsDerivation.flip
    {R : TRS (sigma ⊕ sigma) nu}
    {as bs : List (Term (sigma ⊕ sigma) nu)} :
    GlobalDownCutArgsDerivation R as bs → GlobalDownCutArgsDerivation R bs as
  | .nil => .nil
  | .cons head tail => .cons head.flip tail.flip

end

mutual

/-- Structural height of a symmetry-normal global derivation. -/
def GlobalDownCutDerivation.height
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu} :
    GlobalDownCutDerivation R a b → Nat
  | .refl => 1
  | .rootLeft _ tail => tail.height + 1
  | .rootRight _ head => head.height + 1
  | .barLeft args tail => Nat.max args.height tail.height + 1
  | .barRight args head => Nat.max args.height head.height + 1
  | .hatCl args => args.height + 1
  | .barCl args => args.height + 1

/-- Maximum structural height of symmetry-normal global argument data. -/
def GlobalDownCutArgsDerivation.height
    {R : TRS (sigma ⊕ sigma) nu}
    {as bs : List (Term (sigma ⊕ sigma) nu)} :
    GlobalDownCutArgsDerivation R as bs → Nat
  | .nil => 0
  | .cons head tail => Nat.max head.height tail.height + 1

end

mutual

/-- Replay symmetry-normal global proof data to `Down`. -/
def GlobalDownCutDerivation.toDown
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu} :
    GlobalDownCutDerivation R a b → Down R a b
  | .refl => Down.refl _
  | .rootLeft hroot tail => Down.rootComp hroot tail.toDown
  | .rootRight hroot head =>
      Down.symm (Down.rootComp hroot (Down.symm head.toDown))
  | .barLeft args tail => Down.barComp args.toForall₂ tail.toDown
  | .barRight args head =>
      Down.symm (Down.barComp args.toForall₂ (Down.symm head.toDown))
  | .hatCl args => Down.hatCl args.toForall₂
  | .barCl args => Down.barCl args.toForall₂

/-- Replay pointwise symmetry-normal global data to `List.Forall₂ Down`. -/
def GlobalDownCutArgsDerivation.toForall₂
    {R : TRS (sigma ⊕ sigma) nu}
    {as bs : List (Term (sigma ⊕ sigma) nu)} :
    GlobalDownCutArgsDerivation R as bs → List.Forall₂ (Down R) as bs
  | .nil => List.Forall₂.nil
  | .cons head tail => List.Forall₂.cons head.toDown tail.toForall₂

end

mutual

/-- Normalize every explicit global symmetry node into left/right prefix forms. -/
def GlobalDownDerivation.toCut
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu} :
    GlobalDownDerivation R a b → GlobalDownCutDerivation R a b
  | .refl => .refl
  | .symm h => h.toCut.flip
  | .rootComp hroot tail => .rootLeft hroot tail.toCut
  | .barComp args tail => .barLeft args.toCut tail.toCut
  | .hatCl args => .hatCl args.toCut
  | .barCl args => .barCl args.toCut

/-- Normalize pointwise global argument proof data. -/
def GlobalDownArgsDerivation.toCut
    {R : TRS (sigma ⊕ sigma) nu}
    {as bs : List (Term (sigma ⊕ sigma) nu)} :
    GlobalDownArgsDerivation R as bs → GlobalDownCutArgsDerivation R as bs
  | .nil => .nil
  | .cons head tail => .cons head.toCut tail.toCut

end

/-- Every global `Down` proposition has symmetry-normal proof data. -/
theorem Down.nonempty_globalCutDerivation
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : Down R a b) : Nonempty (GlobalDownCutDerivation R a b) := by
  rcases h.nonempty_globalDerivation with ⟨d⟩
  exact ⟨d.toCut⟩

/-- Symmetry-normal global proof data are extensionally complete for `Down`. -/
theorem down_iff_nonempty_globalCutDerivation
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu} :
    Down R a b ↔ Nonempty (GlobalDownCutDerivation R a b) := by
  constructor
  · exact Down.nonempty_globalCutDerivation
  · rintro ⟨d⟩
    exact d.toDown

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownCutDerivation
#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownCutArgsDerivation
#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownCutDerivation.flip
#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownCutArgsDerivation.flip
#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownCutDerivation.height
#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownCutArgsDerivation.height
#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownCutDerivation.toDown
#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownCutArgsDerivation.toForall₂
#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownDerivation.toCut
#check @OperatorKO7.Meta.UniqueNormalization.GlobalDownArgsDerivation.toCut
#check @OperatorKO7.Meta.UniqueNormalization.Down.nonempty_globalCutDerivation
#check @OperatorKO7.Meta.UniqueNormalization.down_iff_nonempty_globalCutDerivation

#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownCutDerivation
#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownCutArgsDerivation
#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownCutDerivation.flip
#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownCutArgsDerivation.flip
#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownCutDerivation.height
#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownCutArgsDerivation.height
#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownCutDerivation.toDown
#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownCutArgsDerivation.toForall₂
#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownDerivation.toCut
#print axioms OperatorKO7.Meta.UniqueNormalization.GlobalDownArgsDerivation.toCut
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.nonempty_globalCutDerivation
#print axioms OperatorKO7.Meta.UniqueNormalization.down_iff_nonempty_globalCutDerivation
