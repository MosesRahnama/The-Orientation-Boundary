import OperatorKO7.Meta.UniqueNormalization.Theorem37

/-!
# RTA #79 reduced to transitivity of `⇓`

Campaign: `Roadmaps\klop\ROADMAP.md`, wave 6. Source: Kahrs and Smith, FSCD 2016,
Section 7 and Section 8.

## What this module does

With Sections 5 and 6 machine-checked (`ConsistencyCore.lean`,
`DownRelation.lean`, `Lemma36.lean`, `Theorem37.lean`), one gap separates this
development from RTA open problem #79. This module closes every link around that
gap, so the gap itself is a single named property.

`⇓` contains every rewrite step and is reflexive and symmetric, so it sits inside
conversion, and conversion sits inside it as soon as `⇓` is transitive. That is
the whole content of Section 7 of the source, whose proof-graph construction
exists to prove transitivity and nothing else:

> "The kind of proof graph we want to build is one whose equivalence is the full
> relation down_A, because that would show that down_A is transitive."
> (frozen `definitions.md`, D14, Section 7.2)

Given transitivity, conversion of a constructor translation **is** `⇓`, which
Proposition 44 proves constructor-compatible, and the reduction already in
`ConstructorCompatibility.lean` carries that to UN=.

At this pre-signature-extension stage, the statement below isolates Section 7 transitivity
and the same-signature Theorem 69 class-membership input. `SignatureExtension.lean` then
constructs a faithful extended signature and discharges that class-membership input, yielding
`UNconv_of_section7` and `UNred_of_section7` with Section 7 transitivity as the sole remaining
mathematical hypothesis. Thus `hclass` is unavoidable only for the same-signature route used
in this module, not for the completed campaign architecture.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## The constructor translation is a Constructor TRS -/

/-- Every left-hand side of a constructor translation is a destructor symbol
applied to constructor terms. Both rule families have that shape by
construction. -/
theorem constructorRules_constructorTranslation (R : TRS sigma nu) :
    ConstructorRules (constructorTranslation R) := by
  intro rule hmem
  rcases mem_constructorTranslation hmem with ⟨r₀, -, rfl⟩ | ⟨n, -, rfl⟩
  · -- an `R'_d` rule: the left-hand side is the destructor pattern
    cases hr : r₀.lhs with
    | var x =>
        have := r₀.lhs_isApp
        rw [hr] at this
        simp at this
    | app f args =>
        refine ⟨f, args.map constructorLabel, ?_, ?_⟩
        · show destructorPattern r₀.lhs = _
          rw [hr, destructorPattern_app, Term.mapSymList_eq_map]
          rfl
        · intro p hp
          obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
          exact ConOnly.constructorLabel q
  · -- an `R'_c` rule
    refine ⟨n.1, n.2.map constructorLabel, ?_, ?_⟩
    · show Term.app (Sum.inr n.1) (Term.mapSymList Sum.inl n.2) = _
      rw [Term.mapSymList_eq_map]
      rfl
    · intro p hp
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
      exact ConOnly.constructorLabel q

/-! ## `⇓` sits inside conversion -/

/-- Every clause of `⇓` is a conversion: reflexivity, symmetry, a root
contraction followed by a conversion, and the two argumentwise congruences. -/
theorem Down.to_conv {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : Down R a b) : conv R a b := by
  refine Down.induction (P := fun p q => conv R p q) ?_ h
  intro p q hpq
  rcases hpq with rfl | hinv | ⟨c, hroot, hcb⟩ | ⟨d, as, cs, rfl, hall, hcb⟩ | hhat | hbar
  · exact conv.refl R p
  · exact conv.symm hinv.2
  · exact conv.trans (conv.of_step (Step.root hroot)) hcb.2
  · exact conv.trans (conv.args _ (forall₂_mono (fun _ _ hx => hx.2) hall)) hcb.2
  · obtain ⟨f, as, bs, -, rfl, rfl, hall⟩ := hhat
    exact conv.args _ (forall₂_mono (fun _ _ hx => hx.2) hall)
  · obtain ⟨f, as, bs, -, rfl, rfl, hall⟩ := hbar
    exact conv.args _ (forall₂_mono (fun _ _ hx => hx.2) hall)

/-! ## Transitivity closes the other inclusion -/

/-- If `⇓` is transitive then conversion sits inside it. Reflexivity, symmetry
and containment of the rewrite step are already proved, so a conversion sequence
folds into `⇓` one step at a time. -/
theorem Down.of_conv {R : TRS (sigma ⊕ sigma) nu}
    (htrans : ∀ x y z : Term (sigma ⊕ sigma) nu, Down R x y → Down R y z → Down R x z)
    {a b : Term (sigma ⊕ sigma) nu} (h : conv R a b) : Down R a b := by
  induction h with
  | refl => exact Down.refl a
  | tail _ hlast ih =>
      refine htrans _ _ _ ih ?_
      rcases hlast with hstep | hstep
      · exact Down.of_step hstep
      · exact Down.symm (Down.of_step hstep)

/-- **Theorem 66's conclusion, from transitivity alone.** Conversion and `⇓`
coincide. -/
theorem conv_eq_down {R : TRS (sigma ⊕ sigma) nu}
    (htrans : ∀ x y z : Term (sigma ⊕ sigma) nu, Down R x y → Down R y z → Down R x z)
    (a b : Term (sigma ⊕ sigma) nu) : conv R a b ↔ Down R a b :=
  ⟨Down.of_conv htrans, Down.to_conv⟩

/-- Conversion of a constructor translation is constructor-compatible once `⇓` is
transitive. This is Proposition 44 transported along the coincidence. -/
theorem constructorCompatible_conv_of_down_trans {R : TRS sigma nu}
    (htrans : ∀ x y z : Term (sigma ⊕ sigma) nu,
      Down (constructorTranslation R) x y → Down (constructorTranslation R) y z →
      Down (constructorTranslation R) x z) :
    ConstructorCompatible (conv (constructorTranslation R)) := by
  intro a b hca hcb hab
  have hdown : Down (constructorTranslation R) a b := Down.of_conv htrans hab
  rcases Down.constructorCompatible (constructorRules_constructorTranslation R)
    a b hca hcb hdown with hvar | ⟨f, xs, ys, hax, hby, hall⟩
  · exact Or.inl hvar
  · exact Or.inr ⟨f, xs, ys, hax, hby, forall₂_mono (fun _ _ hx => Down.to_conv hx) hall⟩

/-! ## Pre-signature-extension reduction to Section 7 plus same-signature bookkeeping -/

/-- **Pre-extension RTA #79 reduction.**

This theorem exposes the two inputs required by the same-signature Section 8 route.

`htrans` is the whole content of Kahrs and Smith's Section 7: on the constructor
translation of any system inside the class, `⇓` is transitive. Their proof-graph
construction proves exactly this and is used for nothing else.

`hclass` is the Theorem 69 same-signature bookkeeping: each auxiliary extension built from
a pair of convertible normal forms stays inside the class. `GroundUnification.lean` supplies
both mathematical halves of it. The stronger downstream file `SignatureExtension.lean`
removes this input by constructing a faithful genuinely extended signature, so `hclass` is
not a residual hypothesis of the strongest campaign theorem.

Everything between those two inputs and unique normal forms is machine-checked
here: Lemma 28, Lemma 33, Lemma 34, Corollary 35, Lemma 36, Theorem 37,
Propositions 42, 43 and 44, Corollary 45, Lemma 13, Lemma 14, Proposition 15,
Corollary 16, and Theorem 69's reduction. -/
theorem UNconv_of_down_trans {R : TRS sigma nu} {x y : nu} (hxy : x ≠ y)
    (htrans : ∀ S : TRS sigma nu, NonOmegaOverlapping S → TRS.RhsDetermined S →
      ∀ p q r : Term (sigma ⊕ sigma) nu,
        Down (constructorTranslation S) p q → Down (constructorTranslation S) q r →
        Down (constructorTranslation S) p r)
    (hclass : ∀ t u : Term sigma nu, NormalForm R t → NormalForm R u →
      conv R t u → t ≠ u →
      ∃ F : sigma, NonOmegaOverlapping (extendedTRS R F t u x y) ∧
        TRS.RhsDetermined (extendedTRS R F t u x y)) :
    UNconv R :=
  UNconv_of_translation_constructorCompatible hxy
    (fun S hno hvar => constructorCompatible_conv_of_down_trans (htrans S hno hvar))
    hclass

/-- The same two pre-extension inputs give unique normal forms with respect to reduction.
`SignatureExtension.UNred_of_section7` later removes the class-membership input. -/
theorem UNred_of_down_trans {R : TRS sigma nu} {x y : nu} (hxy : x ≠ y)
    (htrans : ∀ S : TRS sigma nu, NonOmegaOverlapping S → TRS.RhsDetermined S →
      ∀ p q r : Term (sigma ⊕ sigma) nu,
        Down (constructorTranslation S) p q → Down (constructorTranslation S) q r →
        Down (constructorTranslation S) p r)
    (hclass : ∀ t u : Term sigma nu, NormalForm R t → NormalForm R u →
      conv R t u → t ≠ u →
      ∃ F : sigma, NonOmegaOverlapping (extendedTRS R F t u x y) ∧
        TRS.RhsDetermined (extendedTRS R F t u x y)) :
    UNred R :=
  UNred_of_UNconv (UNconv_of_down_trans hxy htrans hclass)

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.conv_eq_down
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_down_trans

#print axioms OperatorKO7.Meta.UniqueNormalization.constructorRules_constructorTranslation
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.to_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.of_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.conv_eq_down
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorCompatible_conv_of_down_trans
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_down_trans
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_down_trans
