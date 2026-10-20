import OperatorKO7.Meta.EqGuardedConfluence
import Mathlib.Logic.Relation

set_option autoImplicit false

/-!
# Conservative repair: the greatest safe guard and the exact relation difference

Manuscript anchors: the three-relation table and the repair narrative of
`Rahnama_The_Distinction_Boundary` (Section on SafeStep as the licensed
completion), together with the maximality discussion that replaces the
two-edge critical-fiber statement.

## What this module proves

Four layers, in the order the manuscript uses them.

* **T-B (greatest safe admission predicate).** Over any carrier, a branch
  guard that refuses the diagonal lies below disequality, and disequality is
  the unique guard that is both diagonally safe and off-diagonal complete.
  This is stated for an arbitrary carrier, so it carries no KO7 content.
* **T-C (exact relation difference).** On the KO7 kernel, a `Step` edge that
  `EqGuardedStep` refuses is a diagonal difference edge, and conversely. The
  repair is therefore surgical as a statement about relations.
* **Root determinism.** `EqGuardedStep` sends each source to one target. The
  fact is already available in `OperatorKO7.EqGuardedConfluence`; it is named
  here because the confluence of the repaired relation follows from it, and
  the manuscript states that reason out loud instead of leaving it implicit.
* **T-D and T-ConsRepair.** Among subrelations of `Step` that retain every
  non-diagonal branch, retain the reflexive verdict, and stay locally
  confluent, `EqGuardedStep` is the unique greatest one; and any such repair
  admits the difference edge at `(a, b)` if and only if `a ≠ b`.

## Claim boundaries

* The relation-level statements quantify over root `Step` and root
  `EqGuardedStep`. Contextual closures are separate objects and carry their
  own theorems.
* `AdmissibleRepair` states retention obligations on the repaired relation.
  It avoids naming any guard, so the guard is a conclusion here rather than
  a hypothesis. This is the difference from the earlier two-edge
  critical-fiber statement, whose admissibility predicate already carried the
  policy it was used to justify.
* Local confluence is stated through the reflexive-transitive closure of the
  candidate relation itself, so a candidate may join a peak by its own steps.

Relation: `Step`, `EqGuardedStep` (root). Closure: root, with candidate-local
reflexive-transitive closure for joinability. Strategy: not applicable.
Trust: kernel only, Mathlib baseline.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.ConservativeRepair

open OperatorKO7 Trace
open OperatorKO7.EqGuardedConfluence

/-! ## T-B. The greatest diagonally safe admission predicate

Stated over an arbitrary carrier. A guard is an admission predicate for the
difference branch: the branch fires at `(a, b)` when `g a b` holds. -/

section Guards

variable {α : Type*}

/-- A guard is *diagonally safe* when it refuses every reflexive pair. -/
def DiagSafe (g : α → α → Prop) : Prop := ∀ a, ¬ g a a

/-- A guard is *off-diagonal complete* when it admits every distinct pair. -/
def OffDiagonalComplete (g : α → α → Prop) : Prop := ∀ a b, a ≠ b → g a b

/-- **T-B, lower half.** Every diagonally safe guard lies below disequality. -/
theorem diagSafe_le_disequality {g : α → α → Prop} (h : DiagSafe g) :
    ∀ a b, g a b → a ≠ b := by
  intro a b hg hab
  exact h a (hab ▸ hg)

/-- Disequality is diagonally safe. -/
theorem disequality_diagSafe : DiagSafe (fun a b : α => a ≠ b) := by
  intro a hne
  exact hne rfl

/-- Disequality is off-diagonal complete. -/
theorem disequality_offDiagonalComplete :
    OffDiagonalComplete (fun a b : α => a ≠ b) := by
  intro _ _ hab
  exact hab

/-- **T-B.** Disequality is the unique guard that is both diagonally safe and
off-diagonal complete. -/
theorem diagSafe_offDiagonalComplete_iff_disequality (g : α → α → Prop) :
    (DiagSafe g ∧ OffDiagonalComplete g) ↔ ∀ a b, g a b ↔ a ≠ b := by
  constructor
  · rintro ⟨hsafe, hcomp⟩ a b
    exact ⟨fun hg => diagSafe_le_disequality hsafe a b hg, fun hne => hcomp a b hne⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro a hg
      exact ((h a a).mp hg) rfl
    · intro a b hab
      exact (h a b).mpr hab

/-- **T-B, greatestness.** Disequality is the greatest diagonally safe guard
under pointwise implication. -/
theorem disequality_greatest_diagSafe {g : α → α → Prop} (h : DiagSafe g) :
    ∀ a b, g a b → (a ≠ b) :=
  diagSafe_le_disequality h

end Guards

/-- Non-triviality for T-B: the two conditions are independent. The empty
guard is diagonally safe and fails off-diagonal completeness on the kernel
carrier, so diagonal safety alone does not pin disequality. -/
theorem bot_diagSafe_not_offDiagonalComplete :
    DiagSafe (fun _ _ : Trace => False) ∧
      ¬ OffDiagonalComplete (fun _ _ : Trace => False) := by
  refine ⟨fun _ h => h, ?_⟩
  intro hcomp
  exact hcomp void (delta void) (by intro h; cases h)

/-! ## T-C. The exact relation difference -/

/-- The diagonal difference edge family: the branch that `EqGuardedStep`
refuses and `Step` admits. -/
def DiagonalDifferenceEdge (s t : Trace) : Prop :=
  ∃ a, s = eqW a a ∧ t = integrate (merge a a)

/-- **T-C.** A kernel step is refused by the surgical relation exactly when it
is a diagonal difference edge. -/
theorem step_and_not_eqGuarded_iff (s t : Trace) :
    (Step s t ∧ ¬ EqGuardedStep s t) ↔ DiagonalDifferenceEdge s t := by
  constructor
  · rintro ⟨hstep, hng⟩
    cases hstep with
    | R_int_delta _ => exact absurd (EqGuardedStep.R_int_delta _) hng
    | R_merge_void_left _ => exact absurd (EqGuardedStep.R_merge_void_left _) hng
    | R_merge_void_right _ => exact absurd (EqGuardedStep.R_merge_void_right _) hng
    | R_merge_cancel _ => exact absurd (EqGuardedStep.R_merge_cancel _) hng
    | R_rec_zero _ _ => exact absurd (EqGuardedStep.R_rec_zero _ _) hng
    | R_rec_succ _ _ _ => exact absurd (EqGuardedStep.R_rec_succ _ _ _) hng
    | R_eq_refl _ => exact absurd (EqGuardedStep.R_eq_refl _) hng
    | R_eq_diff a0 b0 =>
        by_cases hab : a0 = b0
        · subst hab
          exact ⟨a0, rfl, rfl⟩
        · exact absurd (EqGuardedStep.R_eq_diff a0 b0 hab) hng
  · rintro ⟨a, rfl, rfl⟩
    refine ⟨Step.R_eq_diff a a, ?_⟩
    intro h
    cases h with
    | R_eq_diff x y hne => exact hne rfl

/-- The surgical relation is a subrelation of the kernel. Re-export of
`OperatorKO7.EqGuardedConfluence.eqGuarded_sub_step` under the paper-facing
name. -/
theorem eqGuardedStep_subset_step {s t : Trace} (h : EqGuardedStep s t) :
    Step s t :=
  eqGuarded_sub_step h

/-- **T-C, strictness (the leg the audit found missing).** The kernel admits a
step that the surgical relation refuses. -/
theorem eqGuardedStep_strict_subset_step :
    ∃ s t : Trace, Step s t ∧ ¬ EqGuardedStep s t :=
  ⟨eqW void void, integrate (merge void void),
    (step_and_not_eqGuarded_iff _ _).mpr ⟨void, rfl, rfl⟩⟩

/-- **T-C, the other strictness leg.** `SafeStep` sits strictly inside the
surgical relation, so the three relations are pairwise distinct. Re-export of
`OperatorKO7.EqGuardedConfluence.eqGuarded_not_subset_safe`. -/
theorem safeStep_strict_subset_eqGuardedStep :
    ∃ s t : Trace, EqGuardedStep s t ∧ ¬ MetaSN_KO7.SafeStep s t :=
  ⟨merge void (recΔ void void (delta void)), recΔ void void (delta void),
    eqGuarded_not_subset_safe⟩

/-! ## Root determinism, named

The confluence of the surgical relation follows from a single target per
source. The manuscript states this reason rather than leaving the reader to
recover it from the proof of `confluentEqGuarded`. -/

/-- The surgical relation sends each source to one target. Re-export of
`OperatorKO7.EqGuardedConfluence.eqGuarded_unique_target`. -/
theorem eqGuardedStep_root_deterministic {a b c : Trace}
    (hb : EqGuardedStep a b) (hc : EqGuardedStep a c) : b = c :=
  eqGuarded_unique_target hb hc

/-- Local joinability of the surgical relation at every source, with the
reason exhibited: the two reducts of a peak coincide. -/
theorem eqGuardedStep_localJoin_of_deterministic (a b c : Trace)
    (hb : EqGuardedStep a b) (hc : EqGuardedStep a c) :
    b = c ∧ EqGuardedStepStar b c := by
  have h := eqGuardedStep_root_deterministic hb hc
  exact ⟨h, h ▸ EqGuardedStepStar.refl b⟩

/-! ## T-D and T-ConsRepair. Admissible repairs -/

/-- Joinability inside a candidate relation, through that relation's own
reflexive-transitive closure. -/
def JoinIn (R : Trace → Trace → Prop) (t u : Trace) : Prop :=
  ∃ d, Relation.ReflTransGen R t d ∧ Relation.ReflTransGen R u d

/-- A candidate repair of the kernel diagonal. The predicate states retention
obligations and local confluence; it names no guard. -/
structure AdmissibleRepair (R : Trace → Trace → Prop) : Prop where
  /-- The repair removes steps and adds none. -/
  sub : ∀ s t, R s t → Step s t
  /-- Every kernel branch away from the diagonal difference family survives. -/
  retainsNonDiagonal : ∀ s t, Step s t → ¬ DiagonalDifferenceEdge s t → R s t
  /-- The reflexive verdict survives. -/
  retainsReflexive : ∀ a, R (eqW a a) void
  /-- The repair is locally confluent. -/
  localConfluent : ∀ s t u, R s t → R s u → JoinIn R t u

/-- `void` has no kernel step. -/
theorem no_step_from_void : ∀ u : Trace, ¬ Step void u := by
  intro u h
  cases h

/-- `integrate (merge a a)` has no kernel root step: the integrate rule needs a
`delta`-headed argument and the argument here is `merge`-headed. -/
theorem no_step_from_integrate_merge_self (a : Trace) :
    ∀ u : Trace, ¬ Step (integrate (merge a a)) u := by
  intro u h
  cases h

/-- A source with no outgoing step reaches only itself. -/
theorem star_eq_of_no_step {R : Trace → Trace → Prop} {x : Trace}
    (hx : ∀ u, ¬ R x u) {d : Trace} (h : Relation.ReflTransGen R x d) : d = x := by
  induction h with
  | refl => rfl
  | tail _ hlast ih =>
      rw [ih] at hlast
      exact absurd hlast (hx _)

/-- **T-ConsRepair, the forcing step.** An admissible repair refuses the
diagonal difference edge at every weight. -/
theorem admissible_refuses_diagonal_difference
    {R : Trace → Trace → Prop} (hR : AdmissibleRepair R) (a : Trace) :
    ¬ R (eqW a a) (integrate (merge a a)) := by
  intro hdiff
  have hrefl : R (eqW a a) void := hR.retainsReflexive a
  obtain ⟨d, hd1, hd2⟩ := hR.localConfluent _ _ _ hrefl hdiff
  have hvoid : ∀ u, ¬ R void u := fun u hu => no_step_from_void u (hR.sub _ _ hu)
  have hint : ∀ u, ¬ R (integrate (merge a a)) u := fun u hu =>
    no_step_from_integrate_merge_self a u (hR.sub _ _ hu)
  have h1 : d = void := star_eq_of_no_step hvoid hd1
  have h2 : d = integrate (merge a a) := star_eq_of_no_step hint hd2
  rw [h1] at h2
  cases h2

/-- **T-D, upper bound.** Every admissible repair lies inside the surgical
relation. -/
theorem admissible_subset_eqGuardedStep
    {R : Trace → Trace → Prop} (hR : AdmissibleRepair R) :
    ∀ s t, R s t → EqGuardedStep s t := by
  intro s t hst
  by_contra hng
  have hdiag : DiagonalDifferenceEdge s t :=
    (step_and_not_eqGuarded_iff s t).mp ⟨hR.sub _ _ hst, hng⟩
  obtain ⟨a, rfl, rfl⟩ := hdiag
  exact admissible_refuses_diagonal_difference hR a hst

/-- **T-D, membership.** The surgical relation is itself admissible. -/
theorem eqGuardedStep_admissible : AdmissibleRepair EqGuardedStep := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s t h
    exact eqGuarded_sub_step h
  · intro s t hstep hnd
    by_contra hng
    exact hnd ((step_and_not_eqGuarded_iff s t).mp ⟨hstep, hng⟩)
  · intro a
    exact EqGuardedStep.R_eq_refl a
  · intro s t u hst hsu
    refine ⟨t, Relation.ReflTransGen.refl, ?_⟩
    rw [eqGuardedStep_root_deterministic hsu hst]

/-- **T-D.** The surgical relation is the unique greatest admissible repair:
it is admissible, every admissible repair lies inside it, and any admissible
repair containing it coincides with it. -/
theorem eqGuardedStep_unique_greatest_admissible :
    AdmissibleRepair EqGuardedStep ∧
      (∀ R, AdmissibleRepair R → ∀ s t, R s t → EqGuardedStep s t) ∧
      (∀ R, AdmissibleRepair R → (∀ s t, EqGuardedStep s t → R s t) →
        ∀ s t, R s t ↔ EqGuardedStep s t) := by
  refine ⟨eqGuardedStep_admissible, fun R hR => admissible_subset_eqGuardedStep hR, ?_⟩
  intro R hR hge s t
  exact ⟨fun h => admissible_subset_eqGuardedStep hR s t h, fun h => hge s t h⟩

/-- **T-ConsRepair.** An admissible repair admits the difference branch at a
pair exactly when the pair is distinct. Conservative repair therefore forces
the guard to recognise disequality; the guard is a conclusion, not a
hypothesis. -/
theorem conservative_repair_forces_exact_distinction
    {R : Trace → Trace → Prop} (hR : AdmissibleRepair R) (a b : Trace) :
    R (eqW a b) (integrate (merge a b)) ↔ a ≠ b := by
  constructor
  · intro hedge hab
    subst hab
    exact admissible_refuses_diagonal_difference hR a hedge
  · intro hab
    refine hR.retainsNonDiagonal _ _ (Step.R_eq_diff a b) ?_
    rintro ⟨c, hs, _⟩
    rw [Trace.eqW.injEq] at hs
    exact hab (hs.1.trans hs.2.symm)

/-- The guard read off an admissible repair is diagonally safe and
off-diagonal complete, so T-B applies to it and pins it to disequality. -/
theorem admissible_guard_is_disequality
    {R : Trace → Trace → Prop} (hR : AdmissibleRepair R) :
    DiagSafe (fun a b => R (eqW a b) (integrate (merge a b))) ∧
      OffDiagonalComplete (fun a b => R (eqW a b) (integrate (merge a b))) := by
  refine ⟨?_, ?_⟩
  · intro a h
    exact admissible_refuses_diagonal_difference hR a h
  · intro a b hab
    exact (conservative_repair_forces_exact_distinction hR a b).mpr hab

/-! ## Non-vacuity and non-triviality -/

/-- R5 witness: the admissible class is inhabited. -/
theorem admissibleRepair_nonempty : ∃ R, AdmissibleRepair R :=
  ⟨EqGuardedStep, eqGuardedStep_admissible⟩

/-- Non-triviality: the full kernel relation fails admissibility, so the class
is a proper restriction of the candidates and the greatest element is not the
ambient relation. -/
theorem step_not_admissible : ¬ AdmissibleRepair Step := by
  intro hR
  exact admissible_refuses_diagonal_difference hR void (Step.R_eq_diff void void)

/-- Non-triviality: `SafeStep` is admissible-adjacent but strictly smaller than
the greatest admissible repair, so greatestness has content. -/
theorem eqGuardedStep_strictly_above_safeStep :
    ∃ s t : Trace, EqGuardedStep s t ∧ ¬ MetaSN_KO7.SafeStep s t :=
  safeStep_strict_subset_eqGuardedStep

end OperatorKO7.Meta.DistinctionBoundary.ConservativeRepair
