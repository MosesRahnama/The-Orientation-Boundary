import OperatorKO7.Meta.UniqueNormalization.Section7DownDerivation

/-!
# Section 7 cut-elimination proof data

The proof-relevant `DownOnDerivation` mirrors the six defining clauses of
`DownOn`, including an explicit symmetry constructor. A recursive composition
proof cannot use that syntax directly as a height measure, because commuting a
cut through symmetry can add a symmetry wrapper.

This module first normalizes symmetry into explicit right-facing root and
destructor-prefix constructors. The resulting proof data have no symmetry node;
reversal is a structural operation that preserves the proof shape. This is the
proof representation used by the subsequent cut-elimination argument.

This first group does not assert transitivity.

Relation: `DownOn A R`.
Closure: the six source clauses with symmetry pushed into left/right prefix forms.
Strategy: full rewriting.
Trust: kernel checked; no external certificate or new axiom.
Scope: arbitrary signatures and variable types on one finite list carrier.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

mutual

/-- Symmetry-normal proof data for `DownOn`. Root and destructor-prefix clauses
occur in both directions, so no explicit symmetry constructor is needed. -/
inductive DownCutDerivation
    (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) :
    Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu → Type (max u v) where
  | refl {a} (ha : a ∈ A) : DownCutDerivation A R a a
  | rootLeft {a c b} (ha : a ∈ A) (hc : c ∈ A)
      (hroot : rootStep R a c) (tail : DownCutDerivation A R c b) :
      DownCutDerivation A R a b
  | rootRight {a b c} (hb : b ∈ A) (hc : c ∈ A)
      (hroot : rootStep R b c) (head : DownCutDerivation A R a c) :
      DownCutDerivation A R a b
  | barLeft {d : sigma} {as cs : List (Term (sigma ⊕ sigma) nu)} {b}
      (ha : Term.app (Sum.inr d) as ∈ A)
      (args : DownCutArgsDerivation A R as cs)
      (tail : DownCutDerivation A R (.app (Sum.inr d) cs) b) :
      DownCutDerivation A R (.app (Sum.inr d) as) b
  | barRight {d : sigma} {as cs : List (Term (sigma ⊕ sigma) nu)} {a}
      (hb : Term.app (Sum.inr d) as ∈ A)
      (args : DownCutArgsDerivation A R as cs)
      (head : DownCutDerivation A R a (.app (Sum.inr d) cs)) :
      DownCutDerivation A R a (.app (Sum.inr d) as)
  | hatCl {c : sigma} {as bs : List (Term (sigma ⊕ sigma) nu)}
      (ha : Term.app (Sum.inl c) as ∈ A)
      (hb : Term.app (Sum.inl c) bs ∈ A)
      (args : DownCutArgsDerivation A R as bs) :
      DownCutDerivation A R (.app (Sum.inl c) as) (.app (Sum.inl c) bs)
  | barCl {d : sigma} {as bs : List (Term (sigma ⊕ sigma) nu)}
      (ha : Term.app (Sum.inr d) as ∈ A)
      (hb : Term.app (Sum.inr d) bs ∈ A)
      (args : DownCutArgsDerivation A R as bs) :
      DownCutDerivation A R (.app (Sum.inr d) as) (.app (Sum.inr d) bs)

/-- Pointwise argument proof data for `DownCutDerivation`. -/
inductive DownCutArgsDerivation
    (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) :
    List (Term (sigma ⊕ sigma) nu) →
    List (Term (sigma ⊕ sigma) nu) → Type (max u v) where
  | nil : DownCutArgsDerivation A R [] []
  | cons {a b as bs}
      (head : DownCutDerivation A R a b)
      (tail : DownCutArgsDerivation A R as bs) :
      DownCutArgsDerivation A R (a :: as) (b :: bs)

end

mutual

/-- Structural reversal of a symmetry-normal derivation. It swaps left/right
prefix constructors and recursively reverses congruence arguments. -/
def DownCutDerivation.flip
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} :
    DownCutDerivation A R a b → DownCutDerivation A R b a
  | .refl ha => .refl ha
  | .rootLeft ha hc hroot tail => .rootRight ha hc hroot tail.flip
  | .rootRight hb hc hroot head => .rootLeft hb hc hroot head.flip
  | .barLeft ha args tail => .barRight ha args tail.flip
  | .barRight hb args head => .barLeft hb args head.flip
  | .hatCl ha hb args => .hatCl hb ha args.flip
  | .barCl ha hb args => .barCl hb ha args.flip

/-- Structural reversal of argument derivations. -/
def DownCutArgsDerivation.flip
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {as bs : List (Term (sigma ⊕ sigma) nu)} :
    DownCutArgsDerivation A R as bs → DownCutArgsDerivation A R bs as
  | .nil => .nil
  | .cons head tail => .cons head.flip tail.flip

end

mutual

/-- Structural height of a symmetry-normal derivation. Every recursive proof
field has strictly smaller height. -/
def DownCutDerivation.height
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} : DownCutDerivation A R a b → Nat
  | .refl _ => 1
  | .rootLeft _ _ _ tail => tail.height + 1
  | .rootRight _ _ _ head => head.height + 1
  | .barLeft _ args tail => Nat.max args.height tail.height + 1
  | .barRight _ args head => Nat.max args.height head.height + 1
  | .hatCl _ _ args => args.height + 1
  | .barCl _ _ args => args.height + 1

/-- Maximum structural height of a symmetry-normal argument derivation. -/
def DownCutArgsDerivation.height
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {as bs : List (Term (sigma ⊕ sigma) nu)} :
    DownCutArgsDerivation A R as bs → Nat
  | .nil => 0
  | .cons head tail => Nat.max head.height tail.height + 1

end

mutual

/-- Structural reversal preserves derivation height. The generated mutual
recursor supplies both term and argument induction hypotheses. -/
theorem DownCutDerivation.height_flip
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} (h : DownCutDerivation A R a b) :
    h.flip.height = h.height :=
  DownCutDerivation.rec
    (motive_1 := fun _ _ d => d.flip.height = d.height)
    (motive_2 := fun _ _ d => d.flip.height = d.height)
    (fun _ => rfl)
    (fun _ _ _ _ ih => by simp only [DownCutDerivation.flip, DownCutDerivation.height, ih])
    (fun _ _ _ _ ih => by simp only [DownCutDerivation.flip, DownCutDerivation.height, ih])
    (fun _ _ _ ihArgs ihTail => by
      simp only [DownCutDerivation.flip, DownCutDerivation.height, ihTail])
    (fun _ _ _ ihArgs ihHead => by
      simp only [DownCutDerivation.flip, DownCutDerivation.height, ihHead])
    (fun _ _ _ ihArgs => by
      simp only [DownCutDerivation.flip, DownCutDerivation.height, ihArgs])
    (fun _ _ _ ihArgs => by
      simp only [DownCutDerivation.flip, DownCutDerivation.height, ihArgs])
    rfl
    (fun _ _ ihHead ihTail => by
      simp only [DownCutArgsDerivation.flip, DownCutArgsDerivation.height, ihHead, ihTail])
    h

/-- Structural reversal preserves argument-derivation height. -/
theorem DownCutArgsDerivation.height_flip
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {as bs : List (Term (sigma ⊕ sigma) nu)} (h : DownCutArgsDerivation A R as bs) :
    h.flip.height = h.height :=
  DownCutArgsDerivation.rec
    (motive_1 := fun _ _ d => d.flip.height = d.height)
    (motive_2 := fun _ _ d => d.flip.height = d.height)
    (fun _ => rfl)
    (fun _ _ _ _ ih => by simp only [DownCutDerivation.flip, DownCutDerivation.height, ih])
    (fun _ _ _ _ ih => by simp only [DownCutDerivation.flip, DownCutDerivation.height, ih])
    (fun _ _ _ ihArgs ihTail => by
      simp only [DownCutDerivation.flip, DownCutDerivation.height, ihTail])
    (fun _ _ _ ihArgs ihHead => by
      simp only [DownCutDerivation.flip, DownCutDerivation.height, ihHead])
    (fun _ _ _ ihArgs => by
      simp only [DownCutDerivation.flip, DownCutDerivation.height, ihArgs])
    (fun _ _ _ ihArgs => by
      simp only [DownCutDerivation.flip, DownCutDerivation.height, ihArgs])
    rfl
    (fun _ _ ihHead ihTail => by
      simp only [DownCutArgsDerivation.flip, DownCutArgsDerivation.height, ihHead, ihTail])
    h

end

mutual

/-- Replay symmetry-normal proof data into the original finite invariant. -/
def DownCutDerivation.toDownOn
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} :
    DownCutDerivation A R a b → DownOn A R a b
  | .refl ha => DownOn.refl ha
  | .rootLeft ha hc hroot tail =>
      DownOn.rootComp ha hc hroot tail.toDownOn
  | .rootRight hb hc hroot head =>
      DownOn.symm (DownOn.rootComp hb hc hroot (DownOn.symm head.toDownOn))
  | .barLeft ha args tail =>
      DownOn.barComp ha args.toForall₂ tail.toDownOn
  | .barRight hb args head =>
      DownOn.symm (DownOn.barComp hb args.toForall₂ (DownOn.symm head.toDownOn))
  | .hatCl ha hb args => DownOn.hatCl ha hb args.toForall₂
  | .barCl ha hb args => DownOn.barCl ha hb args.toForall₂

/-- Replay symmetry-normal argument data to `List.Forall₂ DownOn`. -/
def DownCutArgsDerivation.toForall₂
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {as bs : List (Term (sigma ⊕ sigma) nu)} :
    DownCutArgsDerivation A R as bs → List.Forall₂ (DownOn A R) as bs
  | .nil => List.Forall₂.nil
  | .cons head tail => List.Forall₂.cons head.toDownOn tail.toForall₂

end

mutual

/-- Push every explicit symmetry node of `DownOnDerivation` into the
left/right prefix forms of `DownCutDerivation`. -/
def DownOnDerivation.toCut
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} :
    DownOnDerivation A R a b → DownCutDerivation A R a b
  | .refl ha => .refl ha
  | .symm h => h.toCut.flip
  | .rootComp ha hc hroot tail => .rootLeft ha hc hroot tail.toCut
  | .barComp ha args tail => .barLeft ha args.toCut tail.toCut
  | .hatCl ha hb args => .hatCl ha hb args.toCut
  | .barCl ha hb args => .barCl ha hb args.toCut

/-- Pointwise conversion of explicit argument derivations to symmetry-normal
argument derivations. -/
def DownOnArgsDerivation.toCut
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {as bs : List (Term (sigma ⊕ sigma) nu)} :
    DownOnArgsDerivation A R as bs → DownCutArgsDerivation A R as bs
  | .nil => .nil
  | .cons head tail => .cons head.toCut tail.toCut

end

/-- Symmetry normalization is sound for the original finite invariant. -/
theorem DownOnDerivation.toCut_toDownOn
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} (h : DownOnDerivation A R a b) :
    h.toCut.toDownOn = h.toDownOn := by
  apply Subsingleton.elim

/-- Every `DownOn` proposition has a symmetry-normal proof datum. -/
theorem DownOn.nonempty_cutDerivation
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} (h : DownOn A R a b) :
    Nonempty (DownCutDerivation A R a b) := by
  rcases h.nonempty_derivation with ⟨d⟩
  exact ⟨d.toCut⟩

/-- Symmetry-normal proof data are extensionally complete for `DownOn`. -/
theorem downOn_iff_nonempty_cutDerivation
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} :
    DownOn A R a b ↔ Nonempty (DownCutDerivation A R a b) := by
  constructor
  · exact DownOn.nonempty_cutDerivation
  · rintro ⟨d⟩
    exact d.toDownOn

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.DownCutDerivation
#check @OperatorKO7.Meta.UniqueNormalization.DownCutArgsDerivation
#check @OperatorKO7.Meta.UniqueNormalization.DownCutDerivation.flip
#check @OperatorKO7.Meta.UniqueNormalization.DownCutArgsDerivation.flip
#check @OperatorKO7.Meta.UniqueNormalization.DownCutDerivation.height
#check @OperatorKO7.Meta.UniqueNormalization.DownCutArgsDerivation.height
#check @OperatorKO7.Meta.UniqueNormalization.DownCutDerivation.height_flip
#check @OperatorKO7.Meta.UniqueNormalization.DownCutArgsDerivation.height_flip
#check @OperatorKO7.Meta.UniqueNormalization.DownCutDerivation.toDownOn
#check @OperatorKO7.Meta.UniqueNormalization.DownCutArgsDerivation.toForall₂
#check @OperatorKO7.Meta.UniqueNormalization.DownOnDerivation.toCut
#check @OperatorKO7.Meta.UniqueNormalization.DownOnArgsDerivation.toCut
#check @OperatorKO7.Meta.UniqueNormalization.DownOnDerivation.toCut_toDownOn
#check @OperatorKO7.Meta.UniqueNormalization.DownOn.nonempty_cutDerivation
#check @OperatorKO7.Meta.UniqueNormalization.downOn_iff_nonempty_cutDerivation

#print axioms OperatorKO7.Meta.UniqueNormalization.DownCutDerivation
#print axioms OperatorKO7.Meta.UniqueNormalization.DownCutArgsDerivation
#print axioms OperatorKO7.Meta.UniqueNormalization.DownCutDerivation.flip
#print axioms OperatorKO7.Meta.UniqueNormalization.DownCutArgsDerivation.flip
#print axioms OperatorKO7.Meta.UniqueNormalization.DownCutDerivation.height
#print axioms OperatorKO7.Meta.UniqueNormalization.DownCutArgsDerivation.height
#print axioms OperatorKO7.Meta.UniqueNormalization.DownCutDerivation.height_flip
#print axioms OperatorKO7.Meta.UniqueNormalization.DownCutArgsDerivation.height_flip
#print axioms OperatorKO7.Meta.UniqueNormalization.DownCutDerivation.toDownOn
#print axioms OperatorKO7.Meta.UniqueNormalization.DownCutArgsDerivation.toForall₂
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOnDerivation.toCut
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOnArgsDerivation.toCut
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOnDerivation.toCut_toDownOn
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.nonempty_cutDerivation
#print axioms OperatorKO7.Meta.UniqueNormalization.downOn_iff_nonempty_cutDerivation
