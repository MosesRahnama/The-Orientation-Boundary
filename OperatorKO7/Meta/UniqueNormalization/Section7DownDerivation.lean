import OperatorKO7.Meta.UniqueNormalization.Section7SupportSaturation

/-!
# Proof data for the finite Section 7 invariant

`DownOn` is presented as an impredicative least closed relation in `Coalgebra`.
That presentation is ideal for closure proofs but its proof terms live in `Prop`,
so they cannot be inspected to define a numerical proof measure.

This module gives the same six generating forms as explicit proof data. It adds
no transitivity constructor. Every proof datum replays to `DownOn`, and every
`DownOn` proposition has a proof datum under `Nonempty`. The data therefore
provide a legitimate structural height for the later composition argument.

Relation: `DownOn A R`.
Closure: exactly the six `DownStepOn` generating forms; no arbitrary transitivity.
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

/-- Proof-relevant finite derivations for the six clauses defining `DownOn`.
There is deliberately no transitivity constructor. -/
inductive DownOnDerivation
    (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) :
    Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu → Type (max u v) where
  | refl {a} (ha : a ∈ A) : DownOnDerivation A R a a
  | symm {a b} (h : DownOnDerivation A R a b) : DownOnDerivation A R b a
  | rootComp {a c b} (ha : a ∈ A) (hc : c ∈ A)
      (hroot : rootStep R a c) (tail : DownOnDerivation A R c b) :
      DownOnDerivation A R a b
  | barComp {d : sigma} {as cs : List (Term (sigma ⊕ sigma) nu)} {b}
      (ha : Term.app (Sum.inr d) as ∈ A)
      (args : DownOnArgsDerivation A R as cs)
      (tail : DownOnDerivation A R (.app (Sum.inr d) cs) b) :
      DownOnDerivation A R (.app (Sum.inr d) as) b
  | hatCl {c : sigma} {as bs : List (Term (sigma ⊕ sigma) nu)}
      (ha : Term.app (Sum.inl c) as ∈ A)
      (hb : Term.app (Sum.inl c) bs ∈ A)
      (args : DownOnArgsDerivation A R as bs) :
      DownOnDerivation A R (.app (Sum.inl c) as) (.app (Sum.inl c) bs)
  | barCl {d : sigma} {as bs : List (Term (sigma ⊕ sigma) nu)}
      (ha : Term.app (Sum.inr d) as ∈ A)
      (hb : Term.app (Sum.inr d) bs ∈ A)
      (args : DownOnArgsDerivation A R as bs) :
      DownOnDerivation A R (.app (Sum.inr d) as) (.app (Sum.inr d) bs)

/-- Proof-relevant pointwise argument derivations. -/
inductive DownOnArgsDerivation
    (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) :
    List (Term (sigma ⊕ sigma) nu) →
    List (Term (sigma ⊕ sigma) nu) → Type (max u v) where
  | nil : DownOnArgsDerivation A R [] []
  | cons {a b as bs}
      (head : DownOnDerivation A R a b)
      (tail : DownOnArgsDerivation A R as bs) :
      DownOnArgsDerivation A R (a :: as) (b :: bs)

end

mutual

/-- Structural height of an explicit finite derivation. -/
def DownOnDerivation.height
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} : DownOnDerivation A R a b → Nat
  | .refl _ => 1
  | .symm h => h.height + 1
  | .rootComp _ _ _ tail => tail.height + 1
  | .barComp _ args tail => Nat.max args.height tail.height + 1
  | .hatCl _ _ args => args.height + 1
  | .barCl _ _ args => args.height + 1

/-- Maximum structural height among pointwise argument derivations. The extra
successor makes both recursive fields of `cons` strictly smaller. -/
def DownOnArgsDerivation.height
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {as bs : List (Term (sigma ⊕ sigma) nu)} : DownOnArgsDerivation A R as bs → Nat
  | .nil => 0
  | .cons head tail => Nat.max head.height tail.height + 1

end

/-- Replay explicit proof data into the original finite invariant. The generated
mutual recursor supplies the recursive hypotheses for both proof-data sorts. -/
def DownOnDerivation.toDownOn
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu}
    (h : DownOnDerivation A R a b) : DownOn A R a b :=
  DownOnDerivation.rec
    (motive_1 := fun x y _ => DownOn A R x y)
    (motive_2 := fun xs ys _ => List.Forall₂ (DownOn A R) xs ys)
    (fun ha => DownOn.refl ha)
    (fun _ ih => DownOn.symm ih)
    (fun ha hc hroot _ ih => DownOn.rootComp ha hc hroot ih)
    (fun ha _ _ hargs htail => DownOn.barComp ha hargs htail)
    (fun ha hb _ hargs => DownOn.hatCl ha hb hargs)
    (fun ha hb _ hargs => DownOn.barCl ha hb hargs)
    List.Forall₂.nil
    (fun _ _ hhead htail => List.Forall₂.cons hhead htail)
    h

/-- Replay pointwise proof data into `List.Forall₂ DownOn`. -/
def DownOnArgsDerivation.toForall₂
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {as bs : List (Term (sigma ⊕ sigma) nu)}
    (h : DownOnArgsDerivation A R as bs) : List.Forall₂ (DownOn A R) as bs :=
  DownOnArgsDerivation.rec
    (motive_1 := fun x y _ => DownOn A R x y)
    (motive_2 := fun xs ys _ => List.Forall₂ (DownOn A R) xs ys)
    (fun ha => DownOn.refl ha)
    (fun _ ih => DownOn.symm ih)
    (fun ha hc hroot _ ih => DownOn.rootComp ha hc hroot ih)
    (fun ha _ _ hargs htail => DownOn.barComp ha hargs htail)
    (fun ha hb _ hargs => DownOn.hatCl ha hb hargs)
    (fun ha hb _ hargs => DownOn.barCl ha hb hargs)
    List.Forall₂.nil
    (fun _ _ hhead htail => List.Forall₂.cons hhead htail)
    h

/-- Explicit derivation endpoints lie in the carrier. -/
theorem DownOnDerivation.mem
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu}
    (h : DownOnDerivation A R a b) : a ∈ A ∧ b ∈ A :=
  h.toDownOn.mem

/-- Pointwise `DownOn` proofs carrying explicit derivations can be assembled
into one proof-relevant argument derivation. -/
theorem DownOnArgsDerivation.nonempty_of_forall₂
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {as bs : List (Term (sigma ⊕ sigma) nu)}
    (h : List.Forall₂ (fun a b => Nonempty (DownOnDerivation A R a b)) as bs) :
    Nonempty (DownOnArgsDerivation A R as bs) := by
  induction h with
  | nil => exact ⟨.nil⟩
  | cons hab _ ih =>
      rcases hab with ⟨head⟩
      rcases ih with ⟨tail⟩
      exact ⟨.cons head tail⟩

/-- Every proposition-level `DownOn` fact has an explicit proof datum.
The codomain is `Nonempty`, so the construction remains inside `Prop` while
retaining proof data for later structural induction. -/
theorem DownOn.nonempty_derivation
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} (h : DownOn A R a b) :
    Nonempty (DownOnDerivation A R a b) := by
  refine DownOn.induction
    (P := fun x y => Nonempty (DownOnDerivation A R x y)) ?_ h
  intro p q hpq
  obtain ⟨hp, hq, hbody⟩ := hpq
  rcases hbody with heq | hinv | ⟨c, hc, hroot, htail⟩ |
      ⟨d, as, cs, hpShape, hargs, _, htail⟩ | hhat | hbar
  · subst q
    exact ⟨.refl hp⟩
  · rcases hinv.2 with ⟨d⟩
    exact ⟨.symm d⟩
  · rcases htail.2 with ⟨tail⟩
    exact ⟨.rootComp hp hc hroot tail⟩
  · subst p
    have hargs' : List.Forall₂
        (fun x y => Nonempty (DownOnDerivation A R x y)) as cs :=
      forall₂_mono (fun _ _ hxy => hxy.2) hargs
    rcases DownOnArgsDerivation.nonempty_of_forall₂ hargs' with ⟨args⟩
    rcases htail.2 with ⟨tail⟩
    exact ⟨.barComp hp args tail⟩
  · obtain ⟨f, as, bs, hcon, rfl, rfl, hargs⟩ := hhat
    obtain ⟨c, rfl⟩ := hcon
    have hargs' : List.Forall₂
        (fun x y => Nonempty (DownOnDerivation A R x y)) as bs :=
      forall₂_mono (fun _ _ hxy => hxy.2) hargs
    rcases DownOnArgsDerivation.nonempty_of_forall₂ hargs' with ⟨args⟩
    exact ⟨.hatCl hp hq args⟩
  · obtain ⟨f, as, bs, hdes, rfl, rfl, hargs⟩ := hbar
    obtain ⟨d, rfl⟩ := hdes
    have hargs' : List.Forall₂
        (fun x y => Nonempty (DownOnDerivation A R x y)) as bs :=
      forall₂_mono (fun _ _ hxy => hxy.2) hargs
    rcases DownOnArgsDerivation.nonempty_of_forall₂ hargs' with ⟨args⟩
    exact ⟨.barCl hp hq args⟩

/-- Proof-data representation is extensionally complete for `DownOn`. -/
theorem downOn_iff_nonempty_derivation
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} :
    DownOn A R a b ↔ Nonempty (DownOnDerivation A R a b) := by
  constructor
  · exact DownOn.nonempty_derivation
  · rintro ⟨d⟩
    exact d.toDownOn

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.DownOnDerivation
#check @OperatorKO7.Meta.UniqueNormalization.DownOnArgsDerivation
#check @OperatorKO7.Meta.UniqueNormalization.DownOnDerivation.toDownOn
#check @OperatorKO7.Meta.UniqueNormalization.DownOnArgsDerivation.toForall₂
#check @OperatorKO7.Meta.UniqueNormalization.DownOnDerivation.mem
#check @OperatorKO7.Meta.UniqueNormalization.DownOnDerivation.height
#check @OperatorKO7.Meta.UniqueNormalization.DownOnArgsDerivation.height
#check @OperatorKO7.Meta.UniqueNormalization.DownOnArgsDerivation.nonempty_of_forall₂
#check @OperatorKO7.Meta.UniqueNormalization.DownOn.nonempty_derivation
#check @OperatorKO7.Meta.UniqueNormalization.downOn_iff_nonempty_derivation

#print axioms OperatorKO7.Meta.UniqueNormalization.DownOnDerivation
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOnArgsDerivation
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOnDerivation.toDownOn
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOnArgsDerivation.toForall₂
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOnDerivation.mem
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOnDerivation.height
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOnArgsDerivation.height
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOnArgsDerivation.nonempty_of_forall₂
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.nonempty_derivation
#print axioms OperatorKO7.Meta.UniqueNormalization.downOn_iff_nonempty_derivation
