import OperatorKO7.Meta.UniqueNormalization.Section7SameGraphClosure
import OperatorKO7.Meta.UniqueNormalization.SignatureExtension

/-!
# The Section 7 closeout interface: the missing theorem and the final chain

Campaign: `COMMAND-CENTER/design/RESEARCH-ROADMAP.md`, M1 contract; closeout
dispatch 2026-09-13, Stage 1.

This module states the exact remaining theorem of the Klop / RTA open problem 79
development and compiles the shortest dependency chain from it to the final
uniqueness theorem. It proves the chain, not the missing theorem: the two
definitions below name the target, and nothing in this file may be presented as
a proof of either.

The chain, in the order the closeout dispatch fixes:

1. the finite-carrier graph supply: on every finite subterm-closed carrier over
   a class system there is a complete targeted proof graph that represents every
   root step (`Section7FiniteTargetedModels`);
2. transitivity of `DownOn` on every finite subterm-closed carrier
   (`FiniteCarrierDownTransitive`), which follows from (1) through
   `TermTargetedPGraph.contextAbsorbs_of_complete` and
   `PGraph.downOn_transitive_of_contextAbsorbs`;
3. global `Down` transitivity on the constructor translation, through
   `Down.trans_of_finite_coalgebras`
   (`down_transitive_of_finiteCarrierDownTransitive`);
4. the Summit theorem `conv_eq_down` and its constructor-compatibility corollary
   `constructorCompatible_conv_of_down_trans`;
5. `SignatureExtension.UNconv_of_section7`;
6. the final conclusion (`UNconv_of_section7TranslationDownOnTrans`).

Status of record, 2026-09-13
(`Audit/worktree-lean-publication-audit/klop-status-assessment.md`): steps (1)
and (2) are unproved for non-omega-overlapping, right-variable-safe systems.
Every recorded organization of their proof stops at a named step
(`klop-failed-attempts.md`: F20, F34, F35, F38, F45, F63, F72, F74, F75); no
counterexample to (2) is known (43,049 finite systems tested, zero failures).
The published proof (Kahrs and Smith, Lemma 64) is false as printed and is
refuted in `Section7FiberReduction.lean`.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## The one missing theorem -/

/-- **The missing theorem, per system.** The relativized invariant is transitive
on every finite subterm-closed carrier, for the constructor translation of one
source system. Not proved anywhere in this development. -/
def FiniteCarrierDownTransitive (S : TRS sigma nu) : Prop :=
  ∀ A : List (Term (sigma ⊕ sigma) nu), Coalgebra A →
    ∀ a b c : Term (sigma ⊕ sigma) nu,
      DownOn A (constructorTranslation S) a b →
      DownOn A (constructorTranslation S) b c →
      DownOn A (constructorTranslation S) a c

/-- **The missing theorem at the class level**, over the extended signature of
`SignatureExtension.UNconv_of_section7`. Not proved. -/
def Section7TranslationDownOnTrans (sigma : Type u) (nu : Type v) : Prop :=
  ∀ S : TRS (ExtSym sigma nu) nu, NonOmegaOverlapping S → TRS.RhsDetermined S →
    FiniteCarrierDownTransitive S

/-- **The finite-model supply for the missing theorem.** On every finite
subterm-closed carrier over a class system there is a complete targeted proof
graph that represents every root step. This is the graph-repair target of the M1
contract (M12). Not proved; it is exposed here so that no consumer can present
it as an assumption proved elsewhere. -/
def Section7FiniteTargetedModels (sigma : Type u) (nu : Type v) : Prop :=
  ∀ S : TRS (ExtSym sigma nu) nu, NonOmegaOverlapping S → TRS.RhsDetermined S →
    ∀ A : List (Term (ExtSym sigma nu ⊕ ExtSym sigma nu) nu), Coalgebra A →
      ∃ rho : TermTargetedPGraph A (constructorTranslation S),
        rho.graph.Complete ∧
          RootStepsRepresented A (constructorTranslation S) rho.graph

/-! ## The chain from the missing theorem to the final theorem -/

/-- Finite-carrier transitivity per system gives global transitivity of `Down`
on the constructor translation, through `Down.trans_of_finite_coalgebras`. -/
theorem down_transitive_of_finiteCarrierDownTransitive {S : TRS sigma nu}
    (h : FiniteCarrierDownTransitive S) :
    ∀ p q r : Term (sigma ⊕ sigma) nu,
      Down (constructorTranslation S) p q → Down (constructorTranslation S) q r →
        Down (constructorTranslation S) p r :=
  Down.trans_of_finite_coalgebras (fun A hA => h A hA)

/-- The finite-model supply proves the per-system missing theorem, carrier by
carrier, through `TermTargetedPGraph.contextAbsorbs_of_complete` and
`PGraph.downOn_transitive_of_contextAbsorbs`. -/
theorem finiteCarrierDownTransitive_of_finiteTargetedModels {S : TRS sigma nu}
    (hmodels : ∀ A : List (Term (sigma ⊕ sigma) nu), Coalgebra A →
      ∃ rho : TermTargetedPGraph A (constructorTranslation S),
        rho.graph.Complete ∧
          RootStepsRepresented A (constructorTranslation S) rho.graph) :
    FiniteCarrierDownTransitive S := by
  intro A hA
  obtain ⟨rho, hcomplete, hroot⟩ := hmodels A hA
  exact rho.graph.downOn_transitive_of_contextAbsorbs hA hroot
    (rho.contextAbsorbs_of_complete hA
      (constructorRules_constructorTranslation S) hcomplete)

namespace Section7TranslationDownOnTrans

/-- The class-level graph supply gives the class-level missing theorem. -/
theorem of_finiteTargetedModels (h : Section7FiniteTargetedModels sigma nu) :
    Section7TranslationDownOnTrans sigma nu :=
  fun S hS hv => finiteCarrierDownTransitive_of_finiteTargetedModels (h S hS hv)

end Section7TranslationDownOnTrans

/-- The missing theorem gives the `htrans` input of `UNconv_of_section7`. -/
theorem htrans_of_section7TranslationDownOnTrans
    (h : Section7TranslationDownOnTrans sigma nu) :
    ∀ S : TRS (ExtSym sigma nu) nu, NonOmegaOverlapping S → TRS.RhsDetermined S →
      ∀ p q r : Term (ExtSym sigma nu ⊕ ExtSym sigma nu) nu,
        Down (constructorTranslation S) p q → Down (constructorTranslation S) q r →
          Down (constructorTranslation S) p r :=
  fun S hS hv => down_transitive_of_finiteCarrierDownTransitive (h S hS hv)

/-- **The final Problem 79 conclusion from the missing theorem alone.** For every
non-omega-overlapping, right-variable-safe system over an infinite variable
type, unique normal forms with respect to conversion follow from
`Section7TranslationDownOnTrans`; no further premise is retained. -/
theorem UNconv_of_section7TranslationDownOnTrans [Infinite nu] {R : TRS sigma nu}
    (h : Section7TranslationDownOnTrans sigma nu)
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) : UNconv R :=
  UNconv_of_section7 (htrans_of_section7TranslationDownOnTrans h) hno hvar

/-- The same input gives unique normal forms with respect to reduction. -/
theorem UNred_of_section7TranslationDownOnTrans [Infinite nu] {R : TRS sigma nu}
    (h : Section7TranslationDownOnTrans sigma nu)
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) : UNred R :=
  UNred_of_section7 (htrans_of_section7TranslationDownOnTrans h) hno hvar

/-- The final conclusion from the graph supply, through the class-level missing
theorem. -/
theorem UNconv_of_section7FiniteTargetedModels [Infinite nu] {R : TRS sigma nu}
    (h : Section7FiniteTargetedModels sigma nu)
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) : UNconv R :=
  UNconv_of_section7TranslationDownOnTrans
    (Section7TranslationDownOnTrans.of_finiteTargetedModels h) hno hvar

/-! ## The merge obligation of every graph repair

A repair that resolves a missing root equation joins the represented classes of
the two endpoints. Soundness of that join at a pair related through both classes
is the three-fold composition below. The composition is equivalent to
transitivity of `DownOn` on that carrier, so a proof of the composition from
established premises proves the missing theorem there; the equivalence itself
excludes no proof method. The M12 route took the composition as an input without
a proof (F33), and its measure organizations stop at F38, both recorded in
`Audit/worktree-lean-publication-audit/klop-failed-attempts.md`. -/

/-- The three-fold composition required by every sound class merge on a finite
carrier is equivalent to transitivity of `DownOn` there. -/
theorem downOn_threeFold_iff_transitive
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu} :
    (∀ x a b y, DownOn A R x a → DownOn A R a b → DownOn A R b y → DownOn A R x y) ↔
      (∀ a b c, DownOn A R a b → DownOn A R b c → DownOn A R a c) := by
  constructor
  · intro h3 a b c hab hbc
    exact h3 a b b c hab (DownOn.refl hab.mem.2) hbc
  · intro ht x a b y hxa hab hby
    exact ht x b y (ht x a b hxa hab) hby

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.FiniteCarrierDownTransitive
#check @OperatorKO7.Meta.UniqueNormalization.Section7TranslationDownOnTrans
#check @OperatorKO7.Meta.UniqueNormalization.Section7FiniteTargetedModels
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_section7

#print axioms OperatorKO7.Meta.UniqueNormalization.FiniteCarrierDownTransitive
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7TranslationDownOnTrans
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7FiniteTargetedModels
#print axioms OperatorKO7.Meta.UniqueNormalization.down_transitive_of_finiteCarrierDownTransitive
#print axioms OperatorKO7.Meta.UniqueNormalization.finiteCarrierDownTransitive_of_finiteTargetedModels
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7TranslationDownOnTrans.of_finiteTargetedModels
#print axioms OperatorKO7.Meta.UniqueNormalization.htrans_of_section7TranslationDownOnTrans
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_section7TranslationDownOnTrans
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_section7TranslationDownOnTrans
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_section7FiniteTargetedModels
#print axioms OperatorKO7.Meta.UniqueNormalization.downOn_threeFold_iff_transitive
