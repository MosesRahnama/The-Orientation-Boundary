import OperatorKO7.Meta.UniqueNormalization.Theorem69

/-!
# Constructor compatibility, and the reduction of RTA #79 to one property

Campaign: `Roadmaps\klop\ROADMAP.md`, WP-K2c reframed.

Two independent routes to RTA open problem #79 were pursued in this campaign and
both stopped at the same place, which this module names and then discharges
everything above.

Route R1 transcribes Kahrs and Smith. Its Corollary 35 was first read as needing
a constructor-compatible invariant to decompose an application at a destructor
root; amendment A3 of `definitions.md` restores the destructor tilde that the PDF
text layer drops from Definition 30, and `cor35` in `ConsistencyCore.lean` proves
the corollary under the corrected reading.

Route R2 is the campaign's own conditional-linearization path. Its peak
classifier needs the conversion classes to decompose applications, so that two
conditional rules firing on one term produce an omega-unifier of the original
left-hand sides.

The two needs are one need. Both ask that **conversion decompose applications**
at the places patterns live. On a raw system that request is false, since a rule
`f(a) -> g(b)` converts terms with different root symbols. The constructor
translation is what makes it askable: after translation every pattern is a
constructor term, rewriting happens at destructor roots, and the property has a
chance of holding. Kahrs and Smith's Sections 5 to 7 exist to prove exactly it.

## Fidelity block (frozen `definitions.md`, D11, Definition 27 and Lemma 28)

> "A relation R between term-coalgebras is called constructor-compatible iff
> [hat id] . R . [hat id] is contained in [hat R]."

> "Every constructor-compatible relation R between any two term-coalgebras A and
> B is consistent."

Their variables are frozen as nullary constructors, so `ConTopped` below counts
a variable as constructor-topped and `ConstructorCompatible` gives the variable
case its own clause. `Consistent_of_constructorCompatible` is Lemma 28.

## Fidelity block (frozen `definitions.md`, D15, Theorem 66)

> "Let (Sigma, R) be a Constructor TRS such that [down] A is a consistency
> invariant for any strongly finite term-coalgebra A. Then =_R coincides with
> [down] on Ter(Sigma, empty) (and is therefore constructor-compatible)."

That parenthesis is the conclusion this module takes as its hypothesis, and
`Consistent_of_translation_constructorCompatible` proves everything from it to
consistency of the original system. Reaching UN= needs one further input, that
each Theorem 69 extension stays inside the class; `SignatureExtension.lean` proves
it on the enlarged signature, and `UNconv_of_section7` there needs no such
hypothesis.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Constructor-topped terms -/

/-- A term of the doubled signature is **constructor-topped** when it is a
variable, frozen as a nullary constructor in the sense of frozen definition D9,
or an application headed by a constructor symbol. -/
def ConTopped (t : Term (sigma ⊕ sigma) nu) : Prop :=
  (∃ x : nu, t = .var x) ∨ (∃ (f : sigma) (args : List (Term (sigma ⊕ sigma) nu)),
    t = .app (.inl f) args)

theorem ConTopped.var (x : nu) : ConTopped (sigma := sigma) (.var x) :=
  Or.inl ⟨x, rfl⟩

theorem ConTopped.app (f : sigma) (args : List (Term (sigma ⊕ sigma) nu)) :
    ConTopped (.app (.inl f) args) :=
  Or.inr ⟨f, args, rfl⟩

/-! ## Constructor compatibility -/

/-- **Constructor compatibility**, frozen definition D11. A relation is
constructor-compatible when its restriction to constructor-topped terms
decomposes: two related frozen variables are the same variable, and two related
constructor-headed applications share their symbol and have argumentwise related
arguments. -/
def ConstructorCompatible
    (E : Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu → Prop) : Prop :=
  ∀ a b, ConTopped a → ConTopped b → E a b →
    (∃ x : nu, a = .var x ∧ b = .var x) ∨
    (∃ (f : sigma) (xs ys : List (Term (sigma ⊕ sigma) nu)),
      a = .app (.inl f) xs ∧ b = .app (.inl f) ys ∧ List.Forall₂ E xs ys)

/-- **Lemma 28.** A constructor-compatible relation is consistent: distinct
variables stay unrelated, because a frozen variable has no subterms to
decompose into. -/
theorem Consistent_of_constructorCompatible {R : TRS (sigma ⊕ sigma) nu}
    (h : ConstructorCompatible (conv R)) : Consistent R := by
  intro x y hxy
  rcases h _ _ (ConTopped.var x) (ConTopped.var y) hxy with ⟨z, hx, hy⟩ | ⟨f, xs, ys, hx, -, -⟩
  · have hxz : x = z := by simpa using hx
    have hyz : y = z := by simpa using hy
    rw [hxz, hyz]
  · exact absurd hx (by simp)

/-! ## The reduction -/

/-- **The consistency half of RTA #79, reduced to one property.** If the
conversion of a system's constructor translation is constructor-compatible, the
system has a consistent equational theory.

Everything on the right of the hypothesis is proved: `Consistent_of_constructor
Compatible` is Lemma 28 of the source, and `cor16` is its Corollary 16, both
machine-checked in this development. -/
theorem Consistent_of_translation_constructorCompatible (R : TRS sigma nu)
    (h : ConstructorCompatible (conv (constructorTranslation R))) : Consistent R :=
  (cor16 R).mpr (Consistent_of_constructorCompatible h)

/-- **RTA #79 from constructor compatibility.** Two inputs, each a statement
about systems other than the conclusion. `hCC` is the conclusion of Kahrs and
Smith's Sections 5 to 7, quoted in the fidelity block above, read over every
system inside the class. `hclass` says each Theorem 69 extension stays inside
that class.

The chain is: constructor compatibility gives consistency of the translated
system (Lemma 28), Corollary 16 brings consistency back to the system itself,
and Theorem 69's reduction turns that into UN=. All three links are
machine-checked here. -/
theorem UNconv_of_translation_constructorCompatible {R : TRS sigma nu} {x y : nu}
    (hxy : x ≠ y)
    (hCC : ∀ S : TRS sigma nu, NonOmegaOverlapping S → TRS.RhsDetermined S →
      ConstructorCompatible (conv (constructorTranslation S)))
    (hclass : ∀ t u : Term sigma nu, NormalForm R t → NormalForm R u →
      conv R t u → t ≠ u →
      ∃ F : sigma, NonOmegaOverlapping (extendedTRS R F t u x y) ∧
        TRS.RhsDetermined (extendedTRS R F t u x y)) :
    UNconv R :=
  UNconv_of_consistency_of_extensions hxy
    (fun S hno hvar => Consistent_of_translation_constructorCompatible S (hCC S hno hvar))
    hclass

/-- The same two inputs give unique normal forms with respect to reduction. -/
theorem UNred_of_translation_constructorCompatible {R : TRS sigma nu} {x y : nu}
    (hxy : x ≠ y)
    (hCC : ∀ S : TRS sigma nu, NonOmegaOverlapping S → TRS.RhsDetermined S →
      ConstructorCompatible (conv (constructorTranslation S)))
    (hclass : ∀ t u : Term sigma nu, NormalForm R t → NormalForm R u →
      conv R t u → t ≠ u →
      ∃ F : sigma, NonOmegaOverlapping (extendedTRS R F t u x y) ∧
        TRS.RhsDetermined (extendedTRS R F t u x y)) :
    UNred R :=
  UNred_of_UNconv (UNconv_of_translation_constructorCompatible hxy hCC hclass)

/-! ## Non-vacuity of the hypothesis

A relation contained in equality is constructor-compatible, and the conversion of
a system with no rules is such a relation. The hypothesis of the reduction is
therefore inhabited, and the reduction is a real implication rather than a
vacuous one. -/

theorem forall₂_conv_refl (R : TRS (sigma ⊕ sigma) nu)
    (xs : List (Term (sigma ⊕ sigma) nu)) : List.Forall₂ (conv R) xs xs := by
  induction xs with
  | nil => exact List.Forall₂.nil
  | cons a as ih => exact List.Forall₂.cons (conv.refl R a) ih

/-- A conversion contained in equality is constructor-compatible. -/
theorem constructorCompatible_of_conv_eq {R : TRS (sigma ⊕ sigma) nu}
    (h : ∀ a b, conv R a b → a = b) : ConstructorCompatible (conv R) := by
  intro a b hca _ hab
  have hEq : a = b := h a b hab
  subst hEq
  rcases hca with ⟨x, rfl⟩ | ⟨f, args, rfl⟩
  · exact Or.inl ⟨x, rfl, rfl⟩
  · exact Or.inr ⟨f, args, args, rfl, rfl, forall₂_conv_refl R args⟩

/-- A system with no rules admits no step. -/
theorem not_step_nil {s t : Term sigma nu} : ¬ Step ([] : TRS sigma nu) s t := by
  intro h
  induction h with
  | root hr => obtain ⟨rule, hmem, -⟩ := hr; simp at hmem
  | arg _ _ _ _ ih => exact ih

/-- Its conversion is equality. -/
theorem conv_nil_eq {s t : Term sigma nu} (h : conv ([] : TRS sigma nu) s t) : s = t := by
  induction h with
  | refl => rfl
  | tail _ hlast ih =>
      rcases hlast with hstep | hstep
      · exact absurd hstep not_step_nil
      · exact absurd hstep not_step_nil

/-- The empty system's translation has constructor-compatible conversion, so the
hypothesis of the reduction is inhabited. -/
theorem constructorCompatible_nil :
    ConstructorCompatible (conv (constructorTranslation ([] : TRS sigma nu))) := by
  refine constructorCompatible_of_conv_eq (fun a b hab => conv_nil_eq ?_)
  have hempty : constructorTranslation ([] : TRS sigma nu) = [] := rfl
  rwa [hempty] at hab

/-- What the reduction still asks for, in one place: the conclusion of Kahrs and
Smith's Sections 5 to 7 over every system in the class, and membership of each
Theorem 69 extension in that class. Stating it as an `example` records the shape
of the two remaining inputs without asserting either. -/
example {R : TRS sigma nu} {x y : nu} (hxy : x ≠ y)
    (hCC : ∀ S : TRS sigma nu, NonOmegaOverlapping S → TRS.RhsDetermined S →
      ConstructorCompatible (conv (constructorTranslation S)))
    (hclass : ∀ t u : Term sigma nu, NormalForm R t → NormalForm R u →
      conv R t u → t ≠ u →
      ∃ F : sigma, NonOmegaOverlapping (extendedTRS R F t u x y) ∧
        TRS.RhsDetermined (extendedTRS R F t u x y)) :
    UNconv R ∧ UNred R :=
  ⟨UNconv_of_translation_constructorCompatible hxy hCC hclass,
    UNred_of_translation_constructorCompatible hxy hCC hclass⟩

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.ConTopped
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorCompatible
#check @OperatorKO7.Meta.UniqueNormalization.Consistent_of_constructorCompatible
#check @OperatorKO7.Meta.UniqueNormalization.Consistent_of_translation_constructorCompatible
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_translation_constructorCompatible
#check @OperatorKO7.Meta.UniqueNormalization.UNred_of_translation_constructorCompatible

#print axioms OperatorKO7.Meta.UniqueNormalization.Consistent_of_constructorCompatible
#print axioms OperatorKO7.Meta.UniqueNormalization.Consistent_of_translation_constructorCompatible
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_translation_constructorCompatible
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_translation_constructorCompatible
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorCompatible_of_conv_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorCompatible_nil
