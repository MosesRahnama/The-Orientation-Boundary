import OperatorKO7.Meta.BoundaryObserver.MergedPair
import OperatorKO7.Meta.UniqueNormalization.NormalizerTransport
import OperatorKO7.Meta.UniqueNormalization.NormalizationExamples

set_option autoImplicit false

/-!
# The normal form as an observer and as a target

For a relation `R` on a type `X`, `NormalizingCarrier R` holds the states that reach a normal
state, `NormalizingCore R` is the restriction of `R` to that carrier, and `chosenNF R` sends a
state of the carrier to a normal state it reaches. Under `UNR R` (each state reaches at most one
normal state) the map `chosenNF R` is the normal-form map. This module states its place in the
vocabulary of the source manuscript, Proposition `prop:normal-form-target`:
merged pairs, determination, collisions, step-invariant observers, and the conversion class of
the ambient relation as an observer.

Relation: an arbitrary relation `R` and `NormalizingCore R`, its restriction to the normalizing
carrier; `Conv` is the equivalence closure and `Star` the reflexive-transitive closure.
Property: normal_form. Strategy: not applicable.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
Non-vacuity: `five_unr` supplies `UNR` on a five-point relation; `five_normalForm_mergedPair`
and `five_ambientClass_not_determines_normalForm` are instances on that relation.
-/

namespace OperatorKO7.Meta.BoundaryObserver.NormalFormTarget

open OperatorKO7.Meta.UniqueNormalization.Normalization
open OperatorKO7.Meta.UniqueNormalization.Normalization.Examples
open OperatorKO7.Meta.BoundaryObserver.MergedPair (Determines IsMergedPair)

universe u v w

variable {X : Type u} {R : X → X → Prop}

/-! ## The normal form as an observer -/

/-- Proves: under `UNR R`, the merged pairs of the normal-form map are the pairs of distinct
states of the normalizing carrier that are convertible in the normalizing core.
Relation: `NormalizingCore R`, equivalence closure. Trust: kernel-only. -/
theorem isMergedPair_normalForm_iff (hu : UNR R) (a b : NormalizingCarrier R) :
    IsMergedPair (chosenNF R) a b ↔ a ≠ b ∧ Conv (NormalizingCore R) a b := by
  constructor
  · intro h
    exact ⟨h.1, (chosenNF_eq_iff_core_conv hu a b).mp h.2⟩
  · intro h
    exact ⟨h.1, (chosenNF_eq_iff_core_conv hu a b).mpr h.2⟩

/-- Proves: a merged pair of the chosen normal-form map never consists of two normal states,
since a normal state of the carrier is its own chosen normal form. No hypothesis on `R`.
Relation: `R`, reflexive-transitive closure. Trust: kernel-only. -/
theorem mergedPair_normalForm_not_both_normal (a b : NormalizingCarrier R)
    (h : IsMergedPair (chosenNF R) a b) : ¬ (NF R a.val ∧ NF R b.val) := by
  intro hn
  have ha : (chosenNF R a).val = a.val := nf_star_eq hn.1 (chosenNF_reaches R a)
  have hb : (chosenNF R b).val = b.val := nf_star_eq hn.2 (chosenNF_reaches R b)
  exact h.1 (Subtype.ext (ha.symm.trans ((congrArg Subtype.val h.2).trans hb)))

/-- Proves: under `UNR R`, a target on the normalizing carrier is determined by the normal form
if and only if it is constant along every step of the normalizing core.
Relation: `NormalizingCore R`, one step. Trust: kernel-only. -/
theorem normalForm_determines_iff_step_invariant (hu : UNR R) {V : Type w}
    (P : NormalizingCarrier R → V) :
    Determines (chosenNF R) P ↔
      ∀ ⦃a b : NormalizingCarrier R⦄, NormalizingCore R a b → P a = P b := by
  constructor
  · intro h a b hab
    exact h a b (chosenNF_step hu hab)
  · intro h a b hab
    exact conv_invariant P h ((chosenNF_eq_iff_core_conv hu a b).mp hab)

/-! ## The normal form as a target -/

/-- Proves: under `UNR R`, an observer of the normalizing carrier determines the normal form if
and only if states with one record are convertible in the normalizing core.
Relation: `NormalizingCore R`, equivalence closure. Trust: kernel-only. -/
theorem determines_normalForm_iff (hu : UNR R) {Q : Type v}
    (q : NormalizingCarrier R → Q) :
    Determines q (chosenNF R) ↔
      ∀ a b : NormalizingCarrier R, q a = q b → Conv (NormalizingCore R) a b := by
  constructor
  · intro h a b hab
    exact (chosenNF_eq_iff_core_conv hu a b).mp (h a b hab)
  · intro h a b hab
    exact (chosenNF_eq_iff_core_conv hu a b).mpr (h a b hab)

/-- Proves: under `UNR R`, the collisions of an observer for the normal form are the pairs with
one record that are not convertible in the normalizing core.
Relation: `NormalizingCore R`, equivalence closure. Trust: kernel-only. -/
theorem collision_normalForm_iff (hu : UNR R) {Q : Type v}
    (q : NormalizingCarrier R → Q) (a b : NormalizingCarrier R) :
    (q a = q b ∧ chosenNF R a ≠ chosenNF R b) ↔
      (q a = q b ∧ ¬ Conv (NormalizingCore R) a b) := by
  constructor
  · intro h
    exact ⟨h.1, fun hc => h.2 ((chosenNF_eq_iff_core_conv hu a b).mpr hc)⟩
  · intro h
    exact ⟨h.1, fun he => h.2 ((chosenNF_eq_iff_core_conv hu a b).mp he)⟩

/-- Proves: under `UNR R`, an observer that is constant along every step of the normalizing core
determines the normal form if and only if it has the kernel of the normal form.
Relation: `NormalizingCore R`, one step in the hypothesis. Trust: kernel-only. -/
theorem invariant_determines_normalForm_iff_kernel (hu : UNR R) {Q : Type v}
    (q : NormalizingCarrier R → Q)
    (hi : ∀ ⦃a b : NormalizingCarrier R⦄, NormalizingCore R a b → q a = q b) :
    Determines q (chosenNF R) ↔
      ∀ a b : NormalizingCarrier R, q a = q b ↔ chosenNF R a = chosenNF R b := by
  constructor
  · intro h a b
    exact ⟨h a b,
      fun he => conv_invariant q hi ((chosenNF_eq_iff_core_conv hu a b).mp he)⟩
  · intro h a b hab
    exact (h a b).mp hab

/-- Proves: under `UNR R`, the conversion class of the ambient relation `R`, as an observer of
the normalizing carrier, determines the normal form if and only if `UNC R` holds, that is, any
two convertible normal states are equal.
Relation: `R`, equivalence closure, against `NormalizingCore R`. Trust: kernel-only. -/
theorem ambientClass_determines_normalForm_iff_unc (hu : UNR R) :
    Determines (fun a : NormalizingCarrier R => Quot.mk R a.val) (chosenNF R) ↔ UNC R := by
  constructor
  · intro h
    apply (core_reflection_iff_unc hu).mp
    intro a b hab
    exact (chosenNF_eq_iff_core_conv hu a b).mp (h a b (Quot.eqvGen_sound hab))
  · intro hc a b hab
    exact (chosenNF_eq_iff_core_conv hu a b).mpr
      ((core_reflection_iff_unc hu).mpr hc a b (Quot.eqvGen_exact hab))

/-! ## The five-point relation -/

/-- Instance: on the five-point relation of the normal-forms development each state reaches at
most one normal state, and the conversion class of the relation does not determine the normal
form on the normalizing carrier.
Relation: `fiveRel`. Trust: kernel-only. -/
theorem five_ambientClass_not_determines_normalForm :
    ¬ Determines (fun a : NormalizingCarrier fiveRel => Quot.mk fiveRel a.val)
      (chosenNF fiveRel) :=
  fun h => five_not_unc ((ambientClass_determines_normalForm_iff_unc five_unr).mp h)

/-- Instance and non-vacuity: on the five-point relation the normal-form map has a merged pair,
the states `a` and `b`.
Relation: `fiveRel`. Trust: kernel-only. -/
theorem five_normalForm_mergedPair :
    ∃ a b : NormalizingCarrier fiveRel, IsMergedPair (chosenNF fiveRel) a b := by
  have hb : NF fiveRel Five.b := by decide
  have hab : fiveRel Five.a Five.b := by decide
  have hne : Five.a ≠ Five.b := by decide
  exact ⟨⟨Five.a, Five.b, hb, .single hab⟩, ⟨Five.b, normalizes_of_nf hb⟩,
    (isMergedPair_normalForm_iff five_unr _ _).mpr
      ⟨fun h => hne (congrArg Subtype.val h), .rel _ _ hab⟩⟩

end OperatorKO7.Meta.BoundaryObserver.NormalFormTarget
