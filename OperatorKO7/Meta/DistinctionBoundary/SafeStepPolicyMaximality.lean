import OperatorKO7.Meta.DistinctionBoundary.AdmissibleDiagonalRepair
import Mathlib
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

set_option autoImplicit false

/-!
# Greatest admissible policy on the determined diagonal fiber

This module turns the two full-kernel outputs at `eqW a a` into a Boolean policy
over a finite edge carrier.  The resulting policy type and admissible-object
type are `Fintype`s.  Soundness and completeness identify their semantics with
all `AdmissibleAtDiagonal` relations supported on that exact two-edge fiber.
No global maximality claim follows from this restricted statement.

Audit scope (LASOT):
* carrier: exactly the reflexive and diagonal-difference full-kernel edges;
* admissibility: subrelation of `Step`, reflexive-edge retention, and local join
  in ambient `StepStar`;
* order: pointwise implication between retained Boolean edges;
* non-vacuity: the canonical reflexive-only policy is constructed.
-/

open OperatorKO7
open OperatorKO7.Trace
open MetaSN_DM
open MetaSN_KO7
open CategoryTheory
open CategoryTheory.Limits

namespace OperatorKO7.Meta.DistinctionBoundary

/-- The two full-kernel edges at a determined `eqW` diagonal source. -/
inductive DiagonalCriticalEdge where
| reflexive
| difference
deriving DecidableEq, Fintype, Repr

/-- Target selected by a critical diagonal edge. -/
def DiagonalCriticalEdge.target
    (a : Trace) : DiagonalCriticalEdge -> Trace
| .reflexive => void
| .difference => integrate (merge a a)

/-- A policy decidably chooses which critical diagonal edges to retain.  Since
both domain and codomain are finite, this function type inherits `Fintype`. -/
abbrev DiagonalCriticalPolicy := DiagonalCriticalEdge -> Bool

/-- The complete finite enumeration of critical policies. -/
def diagonalCriticalPolicyUniverse : Finset DiagonalCriticalPolicy :=
  Finset.univ

/-- Every critical policy occurs in the finite enumeration. -/
theorem diagonalCriticalPolicyUniverse_complete
    (P : DiagonalCriticalPolicy) :
    P ∈ diagonalCriticalPolicyUniverse :=
  Finset.mem_univ P

/-- Binary relation induced by a policy at the fixed source `eqW a a`. -/
def DiagonalCriticalRelation
    (a : Trace) (P : DiagonalCriticalPolicy) : Trace -> Trace -> Prop :=
  fun x y =>
    x = eqW a a ∧
      ∃ e : DiagonalCriticalEdge, P e = true ∧ y = e.target a

/-- Decidable finite-policy admissibility: retain the reflexive edge and refuse
the difference edge.  Its exact equivalence with semantic admissibility is
proved below rather than built into this definition. -/
def AdmissibleDiagonalCriticalPolicy
    (_a : Trace) (P : DiagonalCriticalPolicy) : Prop :=
  P DiagonalCriticalEdge.reflexive = true ∧
    P DiagonalCriticalEdge.difference = false

/-- The canonical policy retains exactly the reflexive verdict. -/
def canonicalDiagonalCriticalPolicy : DiagonalCriticalPolicy
| .reflexive => true
| .difference => false

/-- Boolean retention by the canonical policy is equivalent to selecting the
reflexive edge. -/
theorem canonicalDiagonalCriticalPolicy_retains_iff
    (e : DiagonalCriticalEdge) :
    canonicalDiagonalCriticalPolicy e = true ↔
      e = DiagonalCriticalEdge.reflexive := by
  cases e <;> simp [canonicalDiagonalCriticalPolicy]

/-- A selected edge is present in its induced critical relation. -/
theorem diagonalCriticalRelation_of_policy
    {a : Trace} {P : DiagonalCriticalPolicy}
    {e : DiagonalCriticalEdge} (he : P e = true) :
    DiagonalCriticalRelation a P (eqW a a) (e.target a) :=
  ⟨rfl, e, he, rfl⟩

/-- The relation induced by the canonical reflexive-only policy satisfies the
independent semantic admissibility interface. -/
theorem canonicalDiagonalCriticalRelation_admissible (a : Trace) :
    AdmissibleAtDiagonal
      (DiagonalCriticalRelation a canonicalDiagonalCriticalPolicy) a := by
  constructor
  · intro x y h
    rcases h with ⟨hx, e, he, hy⟩
    subst x
    have heq :=
      (canonicalDiagonalCriticalPolicy_retains_iff e).1 he
    subst e
    simp [DiagonalCriticalEdge.target] at hy
    subst y
    exact Step.R_eq_refl a
  · exact diagonalCriticalRelation_of_policy
      (a := a) (P := canonicalDiagonalCriticalPolicy)
      (e := DiagonalCriticalEdge.reflexive) rfl
  · intro b c hb hc
    rcases hb with ⟨_, eb, heb, hb⟩
    rcases hc with ⟨_, ec, hec, hc⟩
    have hebq :=
      (canonicalDiagonalCriticalPolicy_retains_iff eb).1 heb
    have hecq :=
      (canonicalDiagonalCriticalPolicy_retains_iff ec).1 hec
    subst eb
    subst ec
    simp [DiagonalCriticalEdge.target] at hb hc
    subst b
    subst c
    exact ⟨void, StepStar.refl void, StepStar.refl void⟩

/-- Every semantically admissible policy relation has exactly the two Boolean
bits required by finite-policy admissibility. -/
theorem semantic_admissibility_implies_policy_admissibility
    {a : Trace} {P : DiagonalCriticalPolicy}
    (H : AdmissibleAtDiagonal (DiagonalCriticalRelation a P) a) :
    AdmissibleDiagonalCriticalPolicy a P := by
  constructor
  · rcases H.retains_reflexive with ⟨_, e, he, hy⟩
    cases e with
    | reflexive => exact he
    | difference =>
        exact False.elim
          ((OperatorKO7.Meta.EqW_Guard_Barrier.void_ne_integrate_merge_self a) hy)
  · cases hvalue : P DiagonalCriticalEdge.difference with
    | false => rfl
    | true =>
        exact False.elim
          (admissibleAtDiagonal_excludes_difference H
            (diagonalCriticalRelation_of_policy hvalue))

/-- An admissible finite policy is extensionally the canonical policy. -/
theorem admissibleDiagonalCriticalPolicy_eq_canonical
    {a : Trace} {P : DiagonalCriticalPolicy}
    (H : AdmissibleDiagonalCriticalPolicy a P) :
    P = canonicalDiagonalCriticalPolicy := by
  funext e
  cases e with
  | reflexive =>
      simpa [canonicalDiagonalCriticalPolicy] using H.1
  | difference =>
      simpa [canonicalDiagonalCriticalPolicy] using H.2

/-- Every admissible Boolean policy has semantically admissible relation
semantics on the exact critical fiber. -/
theorem policy_admissibility_implies_semantic_admissibility
    {a : Trace} {P : DiagonalCriticalPolicy}
    (H : AdmissibleDiagonalCriticalPolicy a P) :
    AdmissibleAtDiagonal (DiagonalCriticalRelation a P) a := by
  have hP := admissibleDiagonalCriticalPolicy_eq_canonical H
  subst P
  exact canonicalDiagonalCriticalRelation_admissible a

/-- Soundness and completeness of the finite policy semantics for the exact
two-edge critical-fiber problem. -/
theorem admissibleDiagonalCriticalPolicy_iff_semantic_admissibility
    (a : Trace) (P : DiagonalCriticalPolicy) :
    AdmissibleDiagonalCriticalPolicy a P ↔
      AdmissibleAtDiagonal (DiagonalCriticalRelation a P) a :=
  ⟨policy_admissibility_implies_semantic_admissibility,
    semantic_admissibility_implies_policy_admissibility⟩

/-- Every admissible critical policy refuses the difference edge. -/
theorem admissibleDiagonalCriticalPolicy_refuses_difference
    {a : Trace} {P : DiagonalCriticalPolicy}
    (H : AdmissibleDiagonalCriticalPolicy a P) :
    P DiagonalCriticalEdge.difference = false :=
  H.2

/-- The canonical reflexive-only policy is admissible. -/
theorem canonicalDiagonalCriticalPolicy_admissible (a : Trace) :
    AdmissibleDiagonalCriticalPolicy a canonicalDiagonalCriticalPolicy :=
  ⟨rfl, rfl⟩

/-- Every admissible critical policy is pointwise below the canonical policy. -/
theorem admissibleDiagonalCriticalPolicy_le_canonical
    {a : Trace} {P : DiagonalCriticalPolicy}
    (H : AdmissibleDiagonalCriticalPolicy a P) :
    ∀ e, P e = true -> canonicalDiagonalCriticalPolicy e = true := by
  have hP := admissibleDiagonalCriticalPolicy_eq_canonical H
  subst P
  intro e he
  exact he

/-- Headline finite-fiber result: the canonical reflexive-only policy is the
greatest admissible policy under pointwise implication. -/
theorem canonicalDiagonalCriticalPolicy_is_greatest (a : Trace) :
    AdmissibleDiagonalCriticalPolicy a canonicalDiagonalCriticalPolicy ∧
      ∀ P : DiagonalCriticalPolicy,
        AdmissibleDiagonalCriticalPolicy a P ->
          ∀ e, P e = true -> canonicalDiagonalCriticalPolicy e = true :=
  ⟨canonicalDiagonalCriticalPolicy_admissible a,
    fun _ H => admissibleDiagonalCriticalPolicy_le_canonical H⟩

/-- Paper-facing non-circular greatestness theorem: the premise is the
independent `AdmissibleAtDiagonal` semantics, not the Boolean bit definition.
Every semantically admissible policy on the exact two-edge fiber is below the
canonical reflexive-only policy. -/
theorem canonicalDiagonalCriticalPolicy_is_greatest_semantic (a : Trace) :
    AdmissibleAtDiagonal
        (DiagonalCriticalRelation a canonicalDiagonalCriticalPolicy) a ∧
      ∀ P : DiagonalCriticalPolicy,
        AdmissibleAtDiagonal (DiagonalCriticalRelation a P) a ->
          ∀ e, P e = true -> canonicalDiagonalCriticalPolicy e = true :=
  ⟨canonicalDiagonalCriticalRelation_admissible a,
    fun _ H => admissibleDiagonalCriticalPolicy_le_canonical
      (semantic_admissibility_implies_policy_admissibility H)⟩

/-- The critical-edge carrier is explicitly finite; the global rewrite relation is not
being claimed finite. -/
theorem diagonalCriticalEdge_finite : Finite DiagonalCriticalEdge :=
  inferInstance

/-- The Boolean policy space itself is finite, not merely its edge carrier. -/
theorem diagonalCriticalPolicy_finite : Finite DiagonalCriticalPolicy :=
  inferInstance

/-- Explicit `Fintype` data for the four Boolean critical policies. -/
def diagonalCriticalPolicyFintype : Fintype DiagonalCriticalPolicy :=
  inferInstance

/-! ## Exact semantics for all supported critical-fiber relations -/

/-- A relation is supported on the exact two-edge critical fiber when every
edge it contains starts at `eqW a a` and targets one of the two enumerated
critical outputs. -/
def SupportedOnDiagonalCriticalFiber
    (a : Trace) (R : Trace -> Trace -> Prop) : Prop :=
  ∀ {x y}, R x y ->
    x = eqW a a ∧
      ∃ e : DiagonalCriticalEdge, y = e.target a

/-- Every finite policy's relation semantics is supported on the exact critical
fiber. -/
theorem diagonalCriticalRelation_supported
    (a : Trace) (P : DiagonalCriticalPolicy) :
    SupportedOnDiagonalCriticalFiber a (DiagonalCriticalRelation a P) := by
  intro x y h
  rcases h with ⟨hx, e, _, hy⟩
  exact ⟨hx, e, hy⟩

/-- Encode a supported relation by its two decidable membership bits.  The
definition is noncomputable only because an arbitrary Prop-valued relation need
not supply its own decision procedure. -/
noncomputable def policyOfCriticalRelation
    (a : Trace) (R : Trace -> Trace -> Prop) :
    DiagonalCriticalPolicy := by
  classical
  exact fun e => decide (R (eqW a a) (e.target a))

/-- Completeness of the finite semantics: encoding and decoding any relation
supported on the exact critical fiber recovers that relation extensionally. -/
theorem diagonalCriticalRelation_policyOf_eq
    (a : Trace) (R : Trace -> Trace -> Prop)
    (H : SupportedOnDiagonalCriticalFiber a R) :
    DiagonalCriticalRelation a (policyOfCriticalRelation a R) = R := by
  classical
  funext x y
  apply propext
  constructor
  · rintro ⟨hx, e, he, hy⟩
    subst x
    subst y
    simpa [policyOfCriticalRelation] using he
  · intro hxy
    rcases H hxy with ⟨hx, e, hy⟩
    refine ⟨hx, e, ?_, hy⟩
    subst x
    subst y
    simp [policyOfCriticalRelation, hxy]

/-- Semantic soundness of every admissible finite policy. -/
theorem admissibleFinitePolicy_semantics_sound
    {a : Trace} {P : DiagonalCriticalPolicy}
    (H : AdmissibleDiagonalCriticalPolicy a P) :
    SupportedOnDiagonalCriticalFiber a (DiagonalCriticalRelation a P) ∧
      AdmissibleAtDiagonal (DiagonalCriticalRelation a P) a :=
  ⟨diagonalCriticalRelation_supported a P,
    policy_admissibility_implies_semantic_admissibility H⟩

/-- Semantic completeness for the restricted problem: every supported
admissible relation is exactly the semantics of an admissible finite Boolean
policy. -/
theorem supportedAdmissibleRelation_has_finitePolicy
    {a : Trace} {R : Trace -> Trace -> Prop}
    (Hsupported : SupportedOnDiagonalCriticalFiber a R)
    (Hadmissible : AdmissibleAtDiagonal R a) :
    ∃ P : DiagonalCriticalPolicy,
      AdmissibleDiagonalCriticalPolicy a P ∧
        DiagonalCriticalRelation a P = R := by
  let P := policyOfCriticalRelation a R
  have hsemantics : DiagonalCriticalRelation a P = R :=
    diagonalCriticalRelation_policyOf_eq a R Hsupported
  refine ⟨P, ?_, hsemantics⟩
  apply semantic_admissibility_implies_policy_admissibility
  rw [hsemantics]
  exact Hadmissible

/-! ## Finite repair category and terminality -/

/-- An object is an admissible member of the finite Boolean policy space.  The
subtype inherits `Fintype` from the decidable bit predicate. -/
abbrev CriticalRepairObject (a : Trace) :=
  { P : DiagonalCriticalPolicy // AdmissibleDiagonalCriticalPolicy a P }

/-- Explicit finite enumeration of the admissible subtype.  The ambient
policy space is finite; choosing the induced subtype enumeration uses only the
project's accepted classical baseline. -/
noncomputable instance criticalRepairObjectFintypeInstance (a : Trace) :
    Fintype (CriticalRepairObject a) :=
  Fintype.ofFinite _

namespace CriticalRepairObject

/-- Underlying Boolean policy. -/
def policy {a : Trace} (A : CriticalRepairObject a) :
    DiagonalCriticalPolicy :=
  A.1

/-- Proof that the underlying policy is admissible. -/
theorem admissible {a : Trace} (A : CriticalRepairObject a) :
    AdmissibleDiagonalCriticalPolicy a A.policy :=
  A.2

end CriticalRepairObject

/-- The admissible critical-repair object type is genuinely finite. -/
theorem criticalRepairObject_finite (a : Trace) :
    Finite (CriticalRepairObject a) :=
  inferInstance

/-- Explicit `Fintype` data for the admissible critical-repair objects. -/
noncomputable def criticalRepairObjectFintype (a : Trace) :
    Fintype (CriticalRepairObject a) :=
  inferInstance

/-- The thin hom proposition is pointwise policy inclusion. -/
def CriticalRepairHom {a : Trace}
    (A B : CriticalRepairObject a) : Prop :=
  ∀ e, A.policy e = true -> B.policy e = true

/-- The pointwise-inclusion relation makes critical repairs a preorder. -/
instance criticalRepairObjectPreorder (a : Trace) :
    Preorder (CriticalRepairObject a) where
  le := CriticalRepairHom
  le_refl := fun _ _ h => h
  le_trans := fun _ _ _ hAB hBC e he => hBC e (hAB e he)

/-- The inherited preorder category is thin. -/
instance criticalRepairObjectThin (a : Trace) :
    Quiver.IsThin (CriticalRepairObject a) :=
  fun _ _ => inferInstance

/-- The canonical reflexive-only repair as an object. -/
def canonicalCriticalRepairObject (a : Trace) : CriticalRepairObject a where
  val := canonicalDiagonalCriticalPolicy
  property := canonicalDiagonalCriticalPolicy_admissible a

/-- Every admissible object has a unique thin morphism to the canonical repair;
this is the terminality corollary of the greatest-policy theorem. -/
theorem canonicalCriticalRepair_terminal
    {a : Trace} (A : CriticalRepairObject a) :
    CriticalRepairHom A (canonicalCriticalRepairObject a) :=
  admissibleDiagonalCriticalPolicy_le_canonical A.admissible

/-- Thin morphisms are proof-irrelevant, hence the terminal arrow is unique. -/
theorem canonicalCriticalRepair_terminal_unique
    {a : Trace} (A : CriticalRepairObject a)
    (f g : CriticalRepairHom A (canonicalCriticalRepairObject a)) :
    f = g :=
  Subsingleton.elim f g

/-- Actual Mathlib categorical terminal object for the finite preorder category
of exact critical-fiber repairs. -/
def canonicalCriticalRepair_isTerminal (a : Trace) :
    IsTerminal (canonicalCriticalRepairObject a) :=
  IsTerminal.ofUniqueHom
    (fun A => homOfLE (canonicalCriticalRepair_terminal A))
    (fun _ _ => Subsingleton.elim _ _)

/-! ## Guarding interior operator on the finite policy lattice -/

/-- Guard an arbitrary critical-edge predicate by the proved greatest
admissible policy. -/
def criticalGuard (P : DiagonalCriticalPolicy) : DiagonalCriticalPolicy :=
  fun e => P e && canonicalDiagonalCriticalPolicy e

/-- The critical guard is deflationary. -/
theorem criticalGuard_deflationary
    (P : DiagonalCriticalPolicy) (e : DiagonalCriticalEdge) :
    criticalGuard P e = true -> P e = true := by
  intro h
  have hparts :
      P e = true ∧ canonicalDiagonalCriticalPolicy e = true := by
    exact Bool.and_eq_true_iff.mp h
  exact hparts.1

/-- The critical guard is monotone. -/
theorem criticalGuard_monotone
    {P Q : DiagonalCriticalPolicy}
    (hle : ∀ e, P e = true -> Q e = true) :
    ∀ e, criticalGuard P e = true -> criticalGuard Q e = true := by
  intro e h
  have hparts :
      P e = true ∧ canonicalDiagonalCriticalPolicy e = true := by
    exact Bool.and_eq_true_iff.mp h
  have hout :
      Q e = true ∧ canonicalDiagonalCriticalPolicy e = true :=
    ⟨hle e hparts.1, hparts.2⟩
  exact Bool.and_eq_true_iff.mpr hout

/-- The critical guard is idempotent. -/
theorem criticalGuard_idempotent
    (P : DiagonalCriticalPolicy) :
    criticalGuard (criticalGuard P) = criticalGuard P := by
  funext e
  simp only [criticalGuard, Bool.and_self, Bool.and_assoc]

/-- Guarding the unrestricted critical-edge universe yields exactly the
canonical repair. -/
theorem criticalGuard_top_eq_canonical :
    criticalGuard (fun _ => true) =
      canonicalDiagonalCriticalPolicy := by
  funext e
  cases e <;> rfl

section AuditChecks

#check @DiagonalCriticalEdge
#check @DiagonalCriticalEdge.target
#check @DiagonalCriticalPolicy
#check @diagonalCriticalPolicyUniverse
#check @diagonalCriticalPolicyUniverse_complete
#check @DiagonalCriticalRelation
#check @AdmissibleDiagonalCriticalPolicy
#check @canonicalDiagonalCriticalPolicy
#check @canonicalDiagonalCriticalRelation_admissible
#check @semantic_admissibility_implies_policy_admissibility
#check @policy_admissibility_implies_semantic_admissibility
#check @admissibleDiagonalCriticalPolicy_iff_semantic_admissibility
#check @admissibleDiagonalCriticalPolicy_refuses_difference
#check @canonicalDiagonalCriticalPolicy_admissible
#check @admissibleDiagonalCriticalPolicy_le_canonical
#check @canonicalDiagonalCriticalPolicy_is_greatest
#check @canonicalDiagonalCriticalPolicy_is_greatest_semantic
#check @diagonalCriticalEdge_finite
#check @diagonalCriticalPolicy_finite
#check @diagonalCriticalPolicyFintype
#check @SupportedOnDiagonalCriticalFiber
#check @policyOfCriticalRelation
#check @diagonalCriticalRelation_policyOf_eq
#check @admissibleFinitePolicy_semantics_sound
#check @supportedAdmissibleRelation_has_finitePolicy
#check @CriticalRepairObject
#check @criticalRepairObject_finite
#check @criticalRepairObjectFintype
#check @CriticalRepairHom
#check @criticalRepairObjectThin
#check @canonicalCriticalRepairObject
#check @canonicalCriticalRepair_terminal
#check @canonicalCriticalRepair_terminal_unique
#check @canonicalCriticalRepair_isTerminal
#check @criticalGuard
#check @criticalGuard_deflationary
#check @criticalGuard_monotone
#check @criticalGuard_idempotent
#check @criticalGuard_top_eq_canonical

#synth Fintype DiagonalCriticalPolicy
#synth DecidableEq DiagonalCriticalPolicy
#synth Fintype (CriticalRepairObject void)
#synth Category (CriticalRepairObject void)
#synth Quiver.IsThin (CriticalRepairObject void)

#print axioms admissibleDiagonalCriticalPolicy_iff_semantic_admissibility
#print axioms admissibleDiagonalCriticalPolicy_refuses_difference
#print axioms canonicalDiagonalCriticalPolicy_admissible
#print axioms admissibleDiagonalCriticalPolicy_le_canonical
#print axioms canonicalDiagonalCriticalPolicy_is_greatest
#print axioms canonicalDiagonalCriticalPolicy_is_greatest_semantic
#print axioms diagonalCriticalEdge_finite
#print axioms diagonalCriticalPolicy_finite
#print axioms diagonalCriticalRelation_policyOf_eq
#print axioms admissibleFinitePolicy_semantics_sound
#print axioms supportedAdmissibleRelation_has_finitePolicy
#print axioms canonicalCriticalRepair_terminal
#print axioms canonicalCriticalRepair_terminal_unique
#print axioms canonicalCriticalRepair_isTerminal
#print axioms criticalGuard_deflationary
#print axioms criticalGuard_monotone
#print axioms criticalGuard_idempotent
#print axioms criticalGuard_top_eq_canonical

end AuditChecks

end OperatorKO7.Meta.DistinctionBoundary
