import OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation

/-!
# Finite rule support for arbitrary rewrite systems

Rules form an arbitrary predicate, with the same substitution and context
semantics as finite TRSs. Every conversion has finite rule support. The
non-omega-overlapping unique-normal-form statement for all finite systems is
equivalent to its statement for all rule families.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting
open scoped Subst

universe u v

/-- An arbitrary collection of first-order rewrite rules. -/
abbrev RuleFamily (sigma : Type u) (nu : Type v) := Rule sigma nu → Prop

namespace RuleFamily

variable {sigma : Type u} {nu : Type v}

def ofList (R : TRS sigma nu) : RuleFamily sigma nu := fun r => r ∈ R

def FinitePart (P : RuleFamily sigma nu) (R : TRS sigma nu) : Prop :=
  ∀ r ∈ R, P r

def rootStep (P : RuleFamily sigma nu) (s t : Term sigma nu) : Prop :=
  ∃ r, P r ∧ ∃ σ : Subst sigma nu, s = σ • r.lhs ∧ t = σ • r.rhs

inductive Step (P : RuleFamily sigma nu) : Term sigma nu → Term sigma nu → Prop where
  | root {s t : Term sigma nu} : rootStep P s t → Step P s t
  | arg (f : sigma) (pre post : List (Term sigma nu)) {a b : Term sigma nu} :
      Step P a b →
      Step P (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post))

def Conv (P : RuleFamily sigma nu) : Term sigma nu → Term sigma nu → Prop :=
  Relation.ReflTransGen (fun s t => Step P s t ∨ Step P t s)

def NormalForm (P : RuleFamily sigma nu) (t : Term sigma nu) : Prop :=
  ∀ s, ¬ Step P t s

def UNconv (P : RuleFamily sigma nu) : Prop :=
  ∀ s t, NormalForm P s → NormalForm P t → Conv P s t → s = t

theorem rootStep_ofList_iff {R : TRS sigma nu} {s t : Term sigma nu} :
    rootStep (ofList R) s t ↔ Rewriting.rootStep R s t := Iff.rfl

theorem step_of_finite {P : RuleFamily sigma nu} {R : TRS sigma nu}
    (hR : FinitePart P R) {s t : Term sigma nu} (h : Rewriting.Step R s t) :
    Step P s t := by
  induction h with
  | root h =>
      obtain ⟨r, hr, σ, hs, ht⟩ := h
      exact Step.root ⟨r, hR r hr, σ, hs, ht⟩
  | arg f pre post _ ih => exact Step.arg f pre post ih

theorem step_ofList_iff {R : TRS sigma nu} {s t : Term sigma nu} :
    Step (ofList R) s t ↔ Rewriting.Step R s t := by
  constructor
  · intro h
    induction h with
    | root h => exact Rewriting.Step.root h
    | arg f pre post _ ih => exact Rewriting.Step.arg f pre post ih
  · exact step_of_finite (fun _ hr => hr)

theorem step_mono {P Q : RuleFamily sigma nu} (hPQ : ∀ r, P r → Q r)
    {s t : Term sigma nu} (h : Step P s t) : Step Q s t := by
  induction h with
  | root h =>
      obtain ⟨r, hr, σ, hs, ht⟩ := h
      exact Step.root ⟨r, hPQ r hr, σ, hs, ht⟩
  | arg f pre post _ ih => exact Step.arg f pre post ih

theorem finite_step_mono {R S : TRS sigma nu} (hRS : ∀ r ∈ R, r ∈ S)
    {s t : Term sigma nu} (h : Rewriting.Step R s t) : Rewriting.Step S s t :=
  step_ofList_iff.mp (step_of_finite hRS h)

/-- One contextual rewrite uses one actual rule. -/
theorem step_singleton {P : RuleFamily sigma nu} {s t : Term sigma nu}
    (h : Step P s t) : ∃ r, P r ∧ Rewriting.Step [r] s t := by
  induction h with
  | root h =>
      obtain ⟨r, hr, σ, hs, ht⟩ := h
      exact ⟨r, hr, Rewriting.Step.root
        ⟨r, List.mem_singleton_self r, σ, hs, ht⟩⟩
  | arg f pre post _ ih =>
      obtain ⟨r, hr, hstep⟩ := ih
      exact ⟨r, hr, Rewriting.Step.arg f pre post hstep⟩

theorem step_iff_singleton {P : RuleFamily sigma nu} {s t : Term sigma nu} :
    Step P s t ↔ ∃ r, P r ∧ Rewriting.Step [r] s t := by
  refine ⟨step_singleton, ?_⟩
  rintro ⟨r, hr, hstep⟩
  exact step_of_finite (by intro q hq; simpa only [List.mem_singleton.mp hq] using hr) hstep

theorem conv_of_finite {P : RuleFamily sigma nu} {R : TRS sigma nu}
    (hR : FinitePart P R) {s t : Term sigma nu}
    (h : UniqueNormalization.conv R s t) : Conv P s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih =>
      apply Relation.ReflTransGen.tail ih
      rcases hlast with hstep | hstep
      · exact Or.inl (step_of_finite hR hstep)
      · exact Or.inr (step_of_finite hR hstep)

theorem conv_ofList_iff {R : TRS sigma nu} {s t : Term sigma nu} :
    Conv (ofList R) s t ↔ UniqueNormalization.conv R s t := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hlast ih =>
        apply Relation.ReflTransGen.tail ih
        rcases hlast with hstep | hstep
        · exact Or.inl (step_ofList_iff.mp hstep)
        · exact Or.inr (step_ofList_iff.mp hstep)
  · exact conv_of_finite (fun _ hr => hr)

theorem conv_mono {P Q : RuleFamily sigma nu} (hPQ : ∀ r, P r → Q r)
    {s t : Term sigma nu} (h : Conv P s t) : Conv Q s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih =>
      apply Relation.ReflTransGen.tail ih
      rcases hlast with hstep | hstep
      · exact Or.inl (step_mono hPQ hstep)
      · exact Or.inr (step_mono hPQ hstep)

theorem finite_conv_mono {R S : TRS sigma nu} (hRS : ∀ r ∈ R, r ∈ S)
    {s t : Term sigma nu} (h : UniqueNormalization.conv R s t) :
    UniqueNormalization.conv S s t :=
  conv_ofList_iff.mp (conv_of_finite hRS h)

/-- The finite support contains rules from the given family and certifies the
same conversion in the existing finite-TRS relation. -/
theorem conv_exists_finite {P : RuleFamily sigma nu} {s t : Term sigma nu}
    (h : Conv P s t) : ∃ R : TRS sigma nu, FinitePart P R ∧
      UniqueNormalization.conv R s t := by
  induction h with
  | refl =>
      refine ⟨[], ?_, UniqueNormalization.conv.refl [] _⟩
      intro r hr
      cases hr
  | @tail a b _ hlast ih =>
      obtain ⟨R, hR, hprefix⟩ := ih
      have hone : ∃ S : TRS sigma nu, FinitePart P S ∧
          UniqueNormalization.convStep S a b := by
        rcases hlast with hstep | hstep
        · obtain ⟨r, hr, hsr⟩ := step_singleton hstep
          refine ⟨[r], ?_, Or.inl hsr⟩
          intro q hq
          have heq : q = r := List.mem_singleton.mp hq
          subst q
          exact hr
        · obtain ⟨r, hr, hsr⟩ := step_singleton hstep
          refine ⟨[r], ?_, Or.inr hsr⟩
          intro q hq
          have heq : q = r := List.mem_singleton.mp hq
          subst q
          exact hr
      obtain ⟨S, hS, hlastS⟩ := hone
      refine ⟨R ++ S, ?_, ?_⟩
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hR r hr
        · exact hS r hr
      · apply Relation.ReflTransGen.tail
          (finite_conv_mono (fun _ hr => List.mem_append.mpr (Or.inl hr)) hprefix)
        rcases hlastS with hstep | hstep
        · exact Or.inl (finite_step_mono
            (fun _ hr => List.mem_append.mpr (Or.inr hr)) hstep)
        · exact Or.inr (finite_step_mono
            (fun _ hr => List.mem_append.mpr (Or.inr hr)) hstep)

theorem conv_iff_finite {P : RuleFamily sigma nu} {s t : Term sigma nu} :
    Conv P s t ↔ ∃ R : TRS sigma nu, FinitePart P R ∧
      UniqueNormalization.conv R s t := by
  refine ⟨conv_exists_finite, ?_⟩
  rintro ⟨R, hR, hst⟩
  exact conv_of_finite hR hst

theorem normal_ofList_iff {R : TRS sigma nu} {s : Term sigma nu} :
    NormalForm (ofList R) s ↔ UniqueNormalization.NormalForm R s := by
  constructor
  · intro h t ht
    exact h t (step_ofList_iff.mpr ht)
  · intro h t ht
    exact h t (step_ofList_iff.mp ht)

theorem normal_finite {P : RuleFamily sigma nu} {R : TRS sigma nu}
    (hR : FinitePart P R) {s : Term sigma nu} (hs : NormalForm P s) :
    UniqueNormalization.NormalForm R s :=
  fun t h => hs t (step_of_finite hR h)

theorem normal_iff_finite {P : RuleFamily sigma nu} {s : Term sigma nu} :
    NormalForm P s ↔ ∀ R : TRS sigma nu, FinitePart P R →
      UniqueNormalization.NormalForm R s := by
  refine ⟨fun hs _ hR => normal_finite hR hs, ?_⟩
  intro h t hstep
  obtain ⟨r, hr, hs⟩ := step_singleton hstep
  apply h [r] ?_ t hs
  intro q hq
  have heq : q = r := List.mem_singleton.mp hq
  subst q
  exact hr

theorem un_ofList_iff {R : TRS sigma nu} :
    UNconv (ofList R) ↔ UniqueNormalization.UNconv R := by
  constructor
  · intro h s t hs ht hc
    exact h s t (normal_ofList_iff.mpr hs) (normal_ofList_iff.mpr ht)
      (conv_ofList_iff.mpr hc)
  · intro h s t hs ht hc
    exact h s t (normal_ofList_iff.mp hs) (normal_ofList_iff.mp ht)
      (conv_ofList_iff.mp hc)

theorem un_of_finite_parts {P : RuleFamily sigma nu}
    (h : ∀ R : TRS sigma nu, FinitePart P R → UniqueNormalization.UNconv R) :
    UNconv P := by
  intro s t hs ht hc
  obtain ⟨R, hR, hst⟩ := conv_exists_finite hc
  exact h R hR s t (normal_finite hR hs) (normal_finite hR ht) hst

/-- A failure has a finite conversion witness with endpoints still normal
for the whole rule family. Finite-subsystem normality alone is insufficient. -/
theorem not_un_iff_finite_witness {P : RuleFamily sigma nu} :
    ¬ UNconv P ↔ ∃ (R : TRS sigma nu) (s t : Term sigma nu),
      FinitePart P R ∧ NormalForm P s ∧ NormalForm P t ∧
      UniqueNormalization.conv R s t ∧ s ≠ t := by
  classical
  constructor
  · intro h
    by_contra hnone
    apply h
    intro s t hs ht hc
    by_contra hne
    obtain ⟨R, hR, hst⟩ := conv_exists_finite hc
    exact hnone ⟨R, s, t, hR, hs, ht, hst, hne⟩
  · rintro ⟨R, s, t, hR, hs, ht, hc, hne⟩ h
    exact hne (h s t hs ht (conv_of_finite hR hc))

def NonOmegaOverlapping (P : RuleFamily sigma nu) : Prop :=
  ∀ r₁, P r₁ → ∀ r₂, P r₂ → ∀ s : Term sigma nu,
    Subterm s r₁.lhs → s.isApp = true → OmegaUnifiable s r₂.lhs →
      r₁ = r₂ ∧ s = r₁.lhs

def RhsDetermined (P : RuleFamily sigma nu) : Prop :=
  ∀ r, P r → Rule.RhsDetermined r

theorem nonOmega_ofList_iff {R : TRS sigma nu} :
    NonOmegaOverlapping (ofList R) ↔ UniqueNormalization.NonOmegaOverlapping R := Iff.rfl

theorem rhsDetermined_ofList_iff {R : TRS sigma nu} :
    RhsDetermined (ofList R) ↔ TRS.RhsDetermined R := Iff.rfl

theorem nonOmega_finite {P : RuleFamily sigma nu} (hP : NonOmegaOverlapping P)
    {R : TRS sigma nu} (hR : FinitePart P R) :
    UniqueNormalization.NonOmegaOverlapping R :=
  fun r hr q hq s => hP r (hR r hr) q (hR q hq) s

theorem rhsDetermined_finite {P : RuleFamily sigma nu} (hP : RhsDetermined P)
    {R : TRS sigma nu} (hR : FinitePart P R) : TRS.RhsDetermined R :=
  fun r hr => hP r (hR r hr)

/-- Finite and unrestricted rule presentations state the same universal
unique-normal-form theorem. Neither side of this equivalence is assumed proved. -/
theorem finite_un_theorem_iff_rule_families :
    (∀ R : TRS sigma nu, UniqueNormalization.NonOmegaOverlapping R →
      TRS.RhsDetermined R → UniqueNormalization.UNconv R) ↔
    (∀ P : RuleFamily sigma nu, NonOmegaOverlapping P → RhsDetermined P → UNconv P) := by
  constructor
  · intro h P hno hvar
    apply un_of_finite_parts
    intro R hR
    exact h R (nonOmega_finite hno hR) (rhsDetermined_finite hvar hR)
  · intro h R hno hvar
    exact un_ofList_iff.mp (h (ofList R)
      (nonOmega_ofList_iff.mpr hno) (rhsDetermined_ofList_iff.mpr hvar))

end RuleFamily

end OperatorKO7.Meta.UniqueNormalization
