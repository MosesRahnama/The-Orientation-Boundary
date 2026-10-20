import OperatorKO7.Meta.UniqueNormalization.DecreasingDiagrams
import OperatorKO7.Meta.UniqueNormalization.Transfer

/-!
# RTA #79 route R2: conditional-step adapter for decreasing diagrams

The generic decreasing-diagrams theorem labels each one-step reduction before a
competing step is known. The roadmap's first coordinate, conditional level, has
such an intrinsic meaning. Its proposed second coordinate, "rank of the critical
overlap", is currently specified from a pair of competing left-hand sides and
therefore is not yet an intrinsic step label.

This module formalizes the intrinsic part without weakening the future summit.
Every conditional step has a unique minimal level. We shift that level down by
one so the base conditional stratum receives `conditionLevel = 0`, matching the
roadmap convention, and set the unresolved rank coordinate to zero. The resulting
`minimalLevelStep` forgets exactly to the existing `CStep` relation.

A second interface, `ConditionalLabelRefinement`, is the future-proof boundary:
any ranked labelled relation may drive the same confluence and transfer pipeline
once forgetting labels gives exactly `CStep`. Thus a later unifier-rank design
must provide a genuine stepwise refinement rather than peak-dependent metadata.

Trust: kernel checked. No external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-- A conditional step occurs first at level `n`. -/
def CStepMinimal (C : CTRS sigma nu) (n : Nat)
    (s t : Term sigma nu) : Prop :=
  CStepLevel C n s t ∧ ∀ m < n, ¬ CStepLevel C m s t

/-- Every system step has a least level. -/
theorem CStep.exists_minimal {C : CTRS sigma nu} {s t : Term sigma nu}
    (h : CStep C s t) : ∃ n, CStepMinimal C n s t := by
  classical
  let hex : ∃ n, CStepLevel C n s t := h
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro m hm
  exact Nat.find_min hex hm

/-- Minimal levels are unique. -/
theorem CStepMinimal.unique {C : CTRS sigma nu} {s t : Term sigma nu}
    {m n : Nat} (hm : CStepMinimal C m s t) (hn : CStepMinimal C n s t) :
    m = n := by
  apply Nat.le_antisymm
  · by_contra hnm
    have hnm' : n < m := Nat.lt_of_not_ge hnm
    exact (hm.2 n hnm') hn.1
  · by_contra hmn
    have hmn' : m < n := Nat.lt_of_not_ge hmn
    exact (hn.2 m hmn') hm.1

/-- Level zero contains no conditional step, so a minimal level is positive. -/
theorem CStepMinimal.ne_zero {C : CTRS sigma nu} {s t : Term sigma nu}
    {n : Nat} (h : CStepMinimal C n s t) : n ≠ 0 := by
  intro hn
  subst n
  exact h.1.elim

/-- The canonical route-R2 labelling by intrinsic minimal conditional level.
The shift `conditionLevel + 1` makes the first nonempty conditional stratum carry
label level zero. The unifier-rank coordinate is deliberately zero until a
step-intrinsic rank refinement is proved. -/
def minimalLevelStep (C : CTRS sigma nu) :
    LabelledStep (Term sigma nu) LevelLabel :=
  fun label s t =>
    label.unifierRank = 0 ∧
      CStepMinimal C (label.conditionLevel + 1) s t

/-- Forgetting the canonical minimal-level label gives exactly the existing
conditional step relation. -/
theorem unlabelled_minimalLevelStep_iff (C : CTRS sigma nu)
    (s t : Term sigma nu) :
    Unlabelled (minimalLevelStep C) s t ↔ CStep C s t := by
  constructor
  · rintro ⟨label, -, hmin⟩
    exact CStep.of_level hmin.1
  · intro h
    obtain ⟨n, hmin⟩ := h.exists_minimal
    cases n with
    | zero => exact False.elim (hmin.ne_zero rfl)
    | succ k =>
        refine ⟨{ conditionLevel := k, unifierRank := 0 }, rfl, ?_⟩
        simpa using hmin

/-- The canonical label attached to a fixed conditional step is unique. -/
theorem minimalLevelStep_label_unique (C : CTRS sigma nu)
    {s t : Term sigma nu} {a b : LevelLabel}
    (ha : minimalLevelStep C a s t) (hb : minimalLevelStep C b s t) : a = b := by
  rcases ha with ⟨haRank, haMin⟩
  rcases hb with ⟨hbRank, hbMin⟩
  have hlevel : a.conditionLevel = b.conditionLevel := by
    have hs : a.conditionLevel + 1 = b.conditionLevel + 1 :=
      haMin.unique hbMin
    omega
  cases a with
  | mk aLevel aRank =>
      cases b with
      | mk bLevel bRank =>
          simp only at haRank hbRank hlevel ⊢
          subst bLevel
          subst aRank
          subst bRank
          rfl

/-- A labelled relation is a sound and complete stepwise refinement of the
existing conditional rewrite relation. This is the interface a future intrinsic
unifier rank must satisfy. -/
structure ConditionalLabelRefinement (C : CTRS sigma nu)
    (step : LabelledStep (Term sigma nu) LevelLabel) : Prop where
  /-- Every labelled step is an existing conditional step. -/
  sound : ∀ {label s t}, step label s t → CStep C s t
  /-- Every existing conditional step receives at least one label. -/
  complete : ∀ {s t}, CStep C s t → ∃ label, step label s t

/-- The canonical minimal-level relation is a conditional label refinement. -/
theorem minimalLevelStep_refinement (C : CTRS sigma nu) :
    ConditionalLabelRefinement C (minimalLevelStep C) := by
  constructor
  · intro label s t h
    exact (unlabelled_minimalLevelStep_iff C s t).mp ⟨label, h⟩
  · intro s t h
    exact (unlabelled_minimalLevelStep_iff C s t).mpr h

/-- Forgetting any valid conditional label refinement gives exactly `CStep`. -/
theorem ConditionalLabelRefinement.unlabelled_iff
    {C : CTRS sigma nu}
    {step : LabelledStep (Term sigma nu) LevelLabel}
    (href : ConditionalLabelRefinement C step)
    (s t : Term sigma nu) :
    Unlabelled step s t ↔ CStep C s t := by
  constructor
  · rintro ⟨label, hlabel⟩
    exact href.sound hlabel
  · intro h
    obtain ⟨label, hlabel⟩ := href.complete h
    exact ⟨label, hlabel⟩

/-- Reflexive-transitive closure is monotone under inclusion of its one-step
relation. -/
theorem reflTransGen_mono {alpha : Type*}
    {r q : alpha → alpha → Prop}
    (hrq : ∀ {a b}, r a b → q a b)
    {a b : alpha} (h : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen q a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih => exact Relation.ReflTransGen.tail ih (hrq hlast)

/-- Confluence of a valid labelled refinement is equivalent to conditional
confluence because their unlabelled one-step relations coincide. -/
theorem ConditionalLabelRefinement.confluent_iff
    {C : CTRS sigma nu}
    {step : LabelledStep (Term sigma nu) LevelLabel}
    (href : ConditionalLabelRefinement C step) :
    UnlabelledConfluent step ↔ cconfluent C := by
  constructor
  · intro hconf source left right hleft hright
    have hleft' : Relation.ReflTransGen (Unlabelled step) source left :=
      reflTransGen_mono
        (fun h => (href.unlabelled_iff _ _).mpr h) hleft
    have hright' : Relation.ReflTransGen (Unlabelled step) source right :=
      reflTransGen_mono
        (fun h => (href.unlabelled_iff _ _).mpr h) hright
    obtain ⟨join, hlj, hrj⟩ := hconf hleft' hright'
    exact ⟨join,
      reflTransGen_mono (fun h => (href.unlabelled_iff _ _).mp h) hlj,
      reflTransGen_mono (fun h => (href.unlabelled_iff _ _).mp h) hrj⟩
  · intro hconf source left right hleft hright
    have hleft' : Relation.ReflTransGen (CStep C) source left :=
      reflTransGen_mono
        (fun h => (href.unlabelled_iff _ _).mp h) hleft
    have hright' : Relation.ReflTransGen (CStep C) source right :=
      reflTransGen_mono
        (fun h => (href.unlabelled_iff _ _).mp h) hright
    obtain ⟨join, hlj, hrj⟩ := hconf source left right hleft' hright'
    exact ⟨join,
      reflTransGen_mono (fun h => (href.unlabelled_iff _ _).mpr h) hlj,
      reflTransGen_mono (fun h => (href.unlabelled_iff _ _).mpr h) hrj⟩

/-- Local decreasingness of any valid conditional label refinement implies
confluence of the existing conditional system. -/
theorem cconfluent_of_localDecreasing
    {C : CTRS sigma nu}
    {step : LabelledStep (Term sigma nu) LevelLabel}
    (href : ConditionalLabelRefinement C step)
    (hdec : AllLocalPeaksDecreasing step LevelLabelLt) :
    cconfluent C :=
  href.confluent_iff.mp (allLocalPeaksDecreasing_confluent hdec)

/-- Canonical minimal-level specialization. -/
theorem cconfluent_of_minimalLevel_localDecreasing
    {C : CTRS sigma nu}
    (hdec : AllLocalPeaksDecreasing (minimalLevelStep C) LevelLabelLt) :
    cconfluent C :=
  cconfluent_of_localDecreasing (minimalLevelStep_refinement C) hdec

/-- Full transfer pipeline: a conditional linearization whose valid stepwise
labelling is locally decreasing has UN= in the original TRS. -/
theorem UNconv_of_linearization_localDecreasing
    {R : TRS sigma nu} {C : CTRS sigma nu}
    {step : LabelledStep (Term sigma nu) LevelLabel}
    (hlin : IsLinearization R C)
    (href : ConditionalLabelRefinement C step)
    (hdec : AllLocalPeaksDecreasing step LevelLabelLt) :
    UNconv R :=
  UNconv_of_cconfluent_linearization hlin
    (cconfluent_of_localDecreasing href hdec)

/-- Same pipeline for UN->. -/
theorem UNred_of_linearization_localDecreasing
    {R : TRS sigma nu} {C : CTRS sigma nu}
    {step : LabelledStep (Term sigma nu) LevelLabel}
    (hlin : IsLinearization R C)
    (href : ConditionalLabelRefinement C step)
    (hdec : AllLocalPeaksDecreasing step LevelLabelLt) :
    UNred R :=
  UNred_of_cconfluent_linearization hlin
    (cconfluent_of_localDecreasing href hdec)

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.CStepMinimal
#check @OperatorKO7.Meta.UniqueNormalization.CStep.exists_minimal
#check @OperatorKO7.Meta.UniqueNormalization.CStepMinimal.unique
#check @OperatorKO7.Meta.UniqueNormalization.CStepMinimal.ne_zero
#check @OperatorKO7.Meta.UniqueNormalization.minimalLevelStep
#check @OperatorKO7.Meta.UniqueNormalization.unlabelled_minimalLevelStep_iff
#check @OperatorKO7.Meta.UniqueNormalization.minimalLevelStep_label_unique
#check @OperatorKO7.Meta.UniqueNormalization.ConditionalLabelRefinement
#check @OperatorKO7.Meta.UniqueNormalization.minimalLevelStep_refinement
#check @OperatorKO7.Meta.UniqueNormalization.ConditionalLabelRefinement.unlabelled_iff
#check @OperatorKO7.Meta.UniqueNormalization.reflTransGen_mono
#check @OperatorKO7.Meta.UniqueNormalization.ConditionalLabelRefinement.confluent_iff
#check @OperatorKO7.Meta.UniqueNormalization.cconfluent_of_localDecreasing
#check @OperatorKO7.Meta.UniqueNormalization.cconfluent_of_minimalLevel_localDecreasing
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_linearization_localDecreasing
#check @OperatorKO7.Meta.UniqueNormalization.UNred_of_linearization_localDecreasing

#print axioms OperatorKO7.Meta.UniqueNormalization.CStep.exists_minimal
#print axioms OperatorKO7.Meta.UniqueNormalization.CStepMinimal.unique
#print axioms OperatorKO7.Meta.UniqueNormalization.CStepMinimal.ne_zero
#print axioms OperatorKO7.Meta.UniqueNormalization.unlabelled_minimalLevelStep_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.minimalLevelStep_label_unique
#print axioms OperatorKO7.Meta.UniqueNormalization.minimalLevelStep_refinement
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionalLabelRefinement.unlabelled_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.reflTransGen_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionalLabelRefinement.confluent_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.cconfluent_of_localDecreasing
#print axioms OperatorKO7.Meta.UniqueNormalization.cconfluent_of_minimalLevel_localDecreasing
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_linearization_localDecreasing
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_linearization_localDecreasing
