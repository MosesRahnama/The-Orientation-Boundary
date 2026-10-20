import OperatorKO7.Meta.EqGuardedConfluence
import OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity

set_option autoImplicit false

/-!
# The discriminator extension: one comparator suffices, and it is executable

Manuscript anchors: the minimal-extension leg of the definability-boundary
section of `Rahnama_The_Distinction_Boundary`.

## What this module proves

* **The structural comparator.** `structEq` is the left-linear structural
  recursion on the kernel carrier in the observational-type-theory style:
  it compares two terms by descending through matching constructors, so
  `structEq (delta s) (delta t)` reduces to `structEq s t`, and mismatched
  head constructors return `false` at once. `structEq_correct` proves it
  sound and complete for syntactic identity.
* **T-F, sufficiency.** The extended signature defines the exact
  discriminator: `discOp` returns the collapse point on the diagonal and a
  non-collapse record off it, so `discOp_isDiscriminator` holds in the sense
  of `ObserverExpressivity.IsDiscriminator`.
* **T-F, executability.** The comparator implements the disequality guard of
  the surgical relation on the nose: `StepStructGuarded`, whose difference
  rule fires when `structEq a b = false`, coincides with `EqGuardedStep`.
  The guard is therefore a decidable side condition rather than an oracle.
* **Preservation (PX3).** An extension whose operations stay natural under a
  merging endomorphism defines no discriminator, so adding operations of that
  kind preserves the no-go. This is the conservative-extension reading of
  `ObserverExpressivity.not_discriminator_of_natural_under_noninjective`.
* **Minimality in a declared grammar.** Over the two-point extension grammar
  `{none, comparator}`, the comparator entry defines the discriminator and the
  empty entry does not. The failure of the empty entry is carried as an
  explicit hypothesis; its KO7 discharge is
  `SafeStep.SyntacticNonDerivability.disequality_not_sigma_expressible_unconditional`,
  which lives outside this module.

## Claim boundaries

* `structEq` is a metalanguage function on the kernel carrier. Its existence
  says the comparator is implementable, and it stands outside the fixed
  seven-constructor term clone, which is where the no-go lives.
* Minimality is relative to the declared grammar. A grammar with other
  primitives is a different statement, and this module proves nothing about it.

Relation: `EqGuardedStep`, `StepStructGuarded` (root). Closure: root.
Strategy: not applicable. Trust: kernel only, Mathlib baseline.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.DiscriminatorExtension

open OperatorKO7 Trace
open OperatorKO7.EqGuardedConfluence
open OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity

/-! ## The structural comparator -/

/-- Left-linear structural comparison on the kernel carrier. Matching head
constructors recurse into the arguments; mismatched heads return `false`. -/
def structEq : Trace → Trace → Bool
  | void, void => true
  | delta s, delta t => structEq s t
  | integrate s, integrate t => structEq s t
  | merge a b, merge c d => structEq a c && structEq b d
  | app a b, app c d => structEq a c && structEq b d
  | recΔ a b c, recΔ d e f => structEq a d && (structEq b e && structEq c f)
  | eqW a b, eqW c d => structEq a c && structEq b d
  | _, _ => false

/-- The comparator is sound and complete for syntactic identity. The reason is
constructor injectivity together with the recursive calls: matching heads
reduce the question to the arguments, and mismatched heads are separated by
`Trace.noConfusion`. -/
theorem structEq_correct : ∀ a b : Trace, structEq a b = true ↔ a = b := by
  intro a
  induction a with
  | void => intro b; cases b <;> simp [structEq]
  | delta s ih => intro b; cases b <;> simp [structEq, ih]
  | integrate s ih => intro b; cases b <;> simp [structEq, ih]
  | merge a b iha ihb => intro c; cases c <;> simp [structEq, iha, ihb]
  | app a b iha ihb => intro c; cases c <;> simp [structEq, iha, ihb]
  | recΔ a b c iha ihb ihc => intro d; cases d <;> simp [structEq, iha, ihb, ihc]
  | eqW a b iha ihb => intro c; cases c <;> simp [structEq, iha, ihb]

/-- Soundness half, in the form the guard consumes. -/
theorem structEq_sound {a b : Trace} (h : structEq a b = true) : a = b :=
  (structEq_correct a b).mp h

/-- Completeness half. -/
theorem structEq_complete {a b : Trace} (h : a = b) : structEq a b = true :=
  (structEq_correct a b).mpr h

/-- The negative reading: the comparator returns `false` exactly on distinct
terms. This is the executable form of the disequality guard. -/
theorem structEq_false_iff_ne (a b : Trace) : structEq a b = false ↔ a ≠ b := by
  constructor
  · intro hfalse hab
    have : structEq a b = true := structEq_complete hab
    rw [this] at hfalse
    exact Bool.noConfusion hfalse
  · intro hne
    by_contra hc
    have : structEq a b = true := by
      cases hb : structEq a b with
      | false => exact absurd hb hc
      | true => rfl
    exact hne (structEq_sound this)

/-! ## T-F, sufficiency: the extension defines the discriminator -/

/-- The discriminator operation of the extended signature: the collapse point
on the diagonal, a non-collapse record off it. -/
def discOp (a b : Trace) : Trace :=
  if structEq a b = true then void else integrate (merge a b)

/-- **T-F, sufficiency.** The extended signature defines the exact
distinction observer. -/
theorem discOp_isDiscriminator : IsDiscriminator void discOp := by
  intro a b
  constructor
  · intro hne hab
    subst hab
    exact hne (by simp [discOp, structEq_complete (rfl : a = a)])
  · intro hne
    have hfalse : structEq a b = false := (structEq_false_iff_ne a b).mpr hne
    simp only [discOp, hfalse]
    intro hc
    exact Trace.noConfusion hc

/-! ## T-F, executability: the comparator implements the surgical guard -/

/-- The kernel relation with the difference branch guarded by the executable
comparator. Every other rule is the full kernel rule. -/
inductive StepStructGuarded : Trace → Trace → Prop
  | R_int_delta (t) : StepStructGuarded (integrate (delta t)) void
  | R_merge_void_left (t) : StepStructGuarded (merge void t) t
  | R_merge_void_right (t) : StepStructGuarded (merge t void) t
  | R_merge_cancel (t) : StepStructGuarded (merge t t) t
  | R_rec_zero (b s) : StepStructGuarded (recΔ b s void) b
  | R_rec_succ (b s n) : StepStructGuarded (recΔ b s (delta n)) (app s (recΔ b s n))
  | R_eq_refl (a) : StepStructGuarded (eqW a a) void
  | R_eq_diff (a b) (hne : structEq a b = false) :
      StepStructGuarded (eqW a b) (integrate (merge a b))

/-- **T-F, executability.** The executable guard and the disequality guard cut
the kernel at the same place, so the surgical relation is decidable at its
side condition. -/
theorem stepStructGuarded_iff_eqGuardedStep (s t : Trace) :
    StepStructGuarded s t ↔ EqGuardedStep s t := by
  constructor
  · intro h
    cases h with
    | R_int_delta _ => exact EqGuardedStep.R_int_delta _
    | R_merge_void_left _ => exact EqGuardedStep.R_merge_void_left _
    | R_merge_void_right _ => exact EqGuardedStep.R_merge_void_right _
    | R_merge_cancel _ => exact EqGuardedStep.R_merge_cancel _
    | R_rec_zero _ _ => exact EqGuardedStep.R_rec_zero _ _
    | R_rec_succ _ _ _ => exact EqGuardedStep.R_rec_succ _ _ _
    | R_eq_refl _ => exact EqGuardedStep.R_eq_refl _
    | R_eq_diff a b hne =>
        exact EqGuardedStep.R_eq_diff a b ((structEq_false_iff_ne a b).mp hne)
  · intro h
    cases h with
    | R_int_delta _ => exact StepStructGuarded.R_int_delta _
    | R_merge_void_left _ => exact StepStructGuarded.R_merge_void_left _
    | R_merge_void_right _ => exact StepStructGuarded.R_merge_void_right _
    | R_merge_cancel _ => exact StepStructGuarded.R_merge_cancel _
    | R_rec_zero _ _ => exact StepStructGuarded.R_rec_zero _ _
    | R_rec_succ _ _ _ => exact StepStructGuarded.R_rec_succ _ _ _
    | R_eq_refl _ => exact StepStructGuarded.R_eq_refl _
    | R_eq_diff a b hne =>
        exact StepStructGuarded.R_eq_diff a b ((structEq_false_iff_ne a b).mpr hne)

/-! ## Preservation (PX3) -/

/-- **PX3.** An operation of an extension that stays natural under a merging
endomorphism reflecting the collapse point defines no discriminator. Adding
operations of that kind therefore preserves the inexpressibility. -/
theorem extension_without_discriminator_preserves_no_go
    {A : Type*} (nil : A) (h : A → A) (t : A → A → A)
    (hrefl : ∀ z, h z = nil → z = nil)
    (x y : A) (hxy : x ≠ y) (hmerge : h x = h y)
    (hnat : NaturalUnder h t) :
    ¬ IsDiscriminator nil t :=
  not_discriminator_of_natural_under_noninjective nil h t hrefl x y hxy hmerge hnat

/-! ## Minimality inside a declared extension grammar -/

/-- The declared extension grammar of this statement: add nothing, or add the
comparator. -/
inductive ExtensionGrammar
  | none
  | comparator
  deriving DecidableEq, Repr

/-- What an entry of the grammar supplies. -/
def Supplies : ExtensionGrammar → Prop
  | .none => ∃ t : Trace → Trace → Trace, IsDiscriminator void t
  | .comparator => IsDiscriminator void discOp

/-- The comparator entry supplies the discriminator. -/
theorem comparator_supplies : Supplies .comparator :=
  discOp_isDiscriminator

/-- **T-F, minimality in the declared grammar.** Given the kernel-side failure
of the empty extension, the comparator entry is the smallest entry of the
grammar that supplies the discriminator. The hypothesis is discharged for KO7
by the signature-inexpressibility theorem of
`Meta/SafeStep/SyntacticNonDerivability.lean`. -/
theorem comparator_is_minimal_in_grammar
    (hnone : ¬ Supplies .none) :
    ¬ Supplies .none ∧ Supplies .comparator :=
  ⟨hnone, comparator_supplies⟩

/-! ## Non-vacuity and non-triviality -/

/-- R5 witness: the comparator separates a concrete pair and identifies a
concrete diagonal. -/
theorem structEq_nonvacuous :
    structEq void void = true ∧ structEq void (delta void) = false := by
  constructor <;> rfl

/-- R5 witness: the guarded relation with the executable side condition fires
off the diagonal and refuses the diagonal difference edge. -/
theorem stepStructGuarded_nonvacuous :
    StepStructGuarded (eqW void (delta void))
        (integrate (merge void (delta void))) ∧
      ¬ StepStructGuarded (eqW void void) (integrate (merge void void)) := by
  constructor
  · exact StepStructGuarded.R_eq_diff void (delta void) rfl
  · intro h
    cases h with
    | R_eq_diff _ _ hne => exact absurd hne (by decide)

/-- Non-triviality: the discriminator operation separates the diagonal from a
concrete off-diagonal pair, so `discOp_isDiscriminator` is inhabited by data
rather than holding vacuously. -/
theorem discOp_separates :
    discOp void void = void ∧
      discOp void (delta void) = integrate (merge void (delta void)) := by
  constructor <;> rfl

end OperatorKO7.Meta.DistinctionBoundary.DiscriminatorExtension
