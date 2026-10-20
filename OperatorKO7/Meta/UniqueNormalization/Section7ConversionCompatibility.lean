import OperatorKO7.Meta.UniqueNormalization.DownRelation

/-!
# Constructor heads under rewriting and conversion

When every left-hand side of a system over the doubled signature is headed by a
destructor symbol, no root contraction applies to a constructor-topped term. A
forward rewrite of such a term therefore keeps its outer constructor and rewrites
inside one argument, and a rewrite sequence rewrites the arguments
componentwise. Two consequences hold for every such system: joinability is
constructor-compatible, and conversion is constructor-compatible as soon as
convertible constructor-topped terms are joinable, in particular whenever the
system is confluent.

Conversion by itself is not constructor-compatible. The two-rule constructor
system `d → c₁`, `d → c₂` converts the distinct constructor constants `c₁` and
`c₂` through `d` (`ConvCounterexample.not_constructorCompatible_conv`). An
earlier revision of this file asserted constructor compatibility of conversion
for every constructor system; that statement is false, and its elaboration
errors had hidden the falsity. Constructor compatibility of the conversion of
`constructorTranslation S` is the `hCC` premise of
`UNconv_of_translation_constructorCompatible`, so the rule shape alone cannot
supply it.

Relation: `Step R`, `StepStar R`, `joinable R`, `conv R`.
Closure: one step; reflexive-transitive closure; symmetric reflexive-transitive closure.
Strategy: full rewriting.
Trust: kernel checked; no external certificate or new axiom.
Scope: arbitrary signatures, variable types, and destructor-rooted systems,
which include every `ConstructorRules` system.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v w

variable {sigma : Type u} {nu : Type v}

/-! ## Destructor-rooted systems -/

/-- Every left-hand side is a destructor symbol applied to argument terms. This
is the first half of `ConstructorRules`; the argument patterns are unrestricted. -/
def DestructorRooted (R : TRS (sigma ⊕ sigma) nu) : Prop :=
  ∀ rule ∈ R, ∃ (F : sigma) (ps : List (Term (sigma ⊕ sigma) nu)),
    rule.lhs = .app (Sum.inr F) ps

/-- Every constructor system is destructor-rooted. -/
theorem ConstructorRules.destructorRooted {R : TRS (sigma ⊕ sigma) nu}
    (hR : ConstructorRules R) : DestructorRooted R := by
  intro rule hmem
  obtain ⟨F, ps, hlhs, -⟩ := hR rule hmem
  exact ⟨F, ps, hlhs⟩

/-- In a destructor-rooted system the source of a root contraction is
destructor-headed. -/
theorem rootStep_source_destructor_of_destructorRooted {R : TRS (sigma ⊕ sigma) nu}
    (hR : DestructorRooted R) {a c : Term (sigma ⊕ sigma) nu} (h : rootStep R a c) :
    ∃ (d : sigma) (args : List (Term (sigma ⊕ sigma) nu)), a = .app (Sum.inr d) args := by
  obtain ⟨rule, hmem, s, ha, -⟩ := h
  obtain ⟨F, ps, hlhs⟩ := hR rule hmem
  refine ⟨F, ps.map (Subst.apply s), ?_⟩
  rw [ha, hlhs]
  simp [Subst.applyList_eq_map]

/-! ## One forward step -/

/-- A forward step out of a constructor-topped term rewrites inside exactly one
argument of the outer constructor; a variable has no step. -/
theorem step_of_conTopped {R : TRS (sigma ⊕ sigma) nu} (hR : DestructorRooted R)
    {a b : Term (sigma ⊕ sigma) nu} (hca : ConTopped a) (hab : Step R a b) :
    ∃ (c : sigma) (pre post : List (Term (sigma ⊕ sigma) nu))
      (x y : Term (sigma ⊕ sigma) nu),
      a = .app (.inl c) (pre ++ x :: post) ∧ b = .app (.inl c) (pre ++ y :: post) ∧
        Step R x y := by
  rcases hca with ⟨v, rfl⟩ | ⟨c, args, rfl⟩
  · exact absurd hab Step.not_var
  · rcases Step.app_inv hab with hroot | ⟨pre, post, x, y, hargs, hb, hxy⟩
    · obtain ⟨d, args', hd⟩ := rootStep_source_destructor_of_destructorRooted hR hroot
      simp only [Term.app.injEq] at hd
      exact absurd hd.1 (by simp)
    · exact ⟨c, pre, post, x, y, by rw [hargs], hb, hxy⟩

/-- A forward step out of a constructor-topped term keeps the outer constructor
and relates the arguments by conversion. The target is constructor-topped
automatically, so only the source carries the hypothesis. -/
theorem constructor_step_preserves_head
    {R : TRS (sigma ⊕ sigma) nu} (hR : DestructorRooted R)
    {a b : Term (sigma ⊕ sigma) nu} (hca : ConTopped a) (hab : Step R a b) :
    (∃ x : nu, a = .var x ∧ b = .var x) ∨
      ∃ (c : sigma) (xs ys : List (Term (sigma ⊕ sigma) nu)),
        a = .app (.inl c) xs ∧ b = .app (.inl c) ys ∧ List.Forall₂ (conv R) xs ys := by
  obtain ⟨c, pre, post, x, y, ha, hb, hxy⟩ := step_of_conTopped hR hca hab
  exact Or.inr ⟨c, pre ++ x :: post, pre ++ y :: post, ha, hb,
    forall₂_append_middle (conv.refl R) pre post (conv.of_step hxy)⟩

/-- A one-step conversion between constructor-topped terms keeps the outer
constructor and relates the arguments by conversion. -/
theorem constructor_convStep_compatible
    {R : TRS (sigma ⊕ sigma) nu} (hR : DestructorRooted R)
    {a b : Term (sigma ⊕ sigma) nu}
    (hca : ConTopped a) (hcb : ConTopped b) (hab : convStep R a b) :
    (∃ x : nu, a = .var x ∧ b = .var x) ∨
      ∃ (c : sigma) (xs ys : List (Term (sigma ⊕ sigma) nu)),
        a = .app (.inl c) xs ∧ b = .app (.inl c) ys ∧ List.Forall₂ (conv R) xs ys := by
  rcases hab with hab | hba
  · exact constructor_step_preserves_head hR hca hab
  · rcases constructor_step_preserves_head hR hcb hba with
      ⟨x, hb, ha⟩ | ⟨c, ys, xs, hb, ha, hargs⟩
    · exact Or.inl ⟨x, ha, hb⟩
    · exact Or.inr ⟨c, xs, ys, ha, hb, forall₂_swap (fun _ _ h => conv.symm h) hargs⟩

/-! ## Rewrite sequences -/

private theorem forall₂_trans_of {alpha : Type w} {r : alpha → alpha → Prop}
    (htr : ∀ x y z, r x y → r y z → r x z) :
    ∀ {l₁ l₂ l₃ : List alpha}, List.Forall₂ r l₁ l₂ → List.Forall₂ r l₂ l₃ →
      List.Forall₂ r l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => .cons (htr _ _ _ h₁ h₂) (forall₂_trans_of htr t₁ t₂)

/-- A rewrite sequence out of a constructor-topped term keeps a variable fixed,
or keeps the outer constructor and rewrites the arguments componentwise. -/
theorem stepStar_of_conTopped {R : TRS (sigma ⊕ sigma) nu} (hR : DestructorRooted R)
    {a b : Term (sigma ⊕ sigma) nu} (hca : ConTopped a) (hab : StepStar R a b) :
    (∃ x : nu, a = .var x ∧ b = .var x) ∨
      ∃ (c : sigma) (xs ys : List (Term (sigma ⊕ sigma) nu)),
        a = .app (.inl c) xs ∧ b = .app (.inl c) ys ∧ List.Forall₂ (StepStar R) xs ys := by
  induction hab with
  | refl =>
      rcases hca with ⟨x, rfl⟩ | ⟨c, xs, rfl⟩
      · exact Or.inl ⟨x, rfl, rfl⟩
      · exact Or.inr ⟨c, xs, xs, rfl, rfl, forall₂_self (StepStar.refl R) xs⟩
  | tail _ hlast ih =>
      rcases ih with ⟨x, ha, hm⟩ | ⟨c, xs, ms, ha, hm, hargs⟩
      · subst hm
        exact absurd hlast Step.not_var
      · subst hm
        obtain ⟨c', pre, post, p, q, hmid, hb, hpq⟩ :=
          step_of_conTopped hR (ConTopped.app c ms) hlast
        simp only [Term.app.injEq, Sum.inl.injEq] at hmid
        obtain ⟨hc, hms⟩ := hmid
        subst hc
        subst hms
        exact Or.inr ⟨c, xs, pre ++ q :: post, ha, hb,
          forall₂_trans_of (r := StepStar R) (fun _ _ _ h₁ h₂ => StepStar.trans h₁ h₂) hargs
            (forall₂_append_middle (StepStar.refl R) pre post (StepStar.single hpq))⟩

/-! ## Joinability and conversion -/

private theorem forall₂_joinable_of_stepStar {R : TRS (sigma ⊕ sigma) nu} :
    ∀ {xs ys zs : List (Term (sigma ⊕ sigma) nu)},
      List.Forall₂ (StepStar R) xs zs → List.Forall₂ (StepStar R) ys zs →
        List.Forall₂ (joinable R) xs ys
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ =>
      .cons ⟨_, h₁, h₂⟩ (forall₂_joinable_of_stepStar t₁ t₂)

/-- Joinability is constructor-compatible in every destructor-rooted system. -/
theorem constructorCompatible_joinable {R : TRS (sigma ⊕ sigma) nu}
    (hR : DestructorRooted R) : ConstructorCompatible (joinable R) := by
  rintro a b hca hcb ⟨w, haw, hbw⟩
  rcases stepStar_of_conTopped hR hca haw with ⟨x, ha, hw⟩ | ⟨c, xs, zs, ha, hw, hxz⟩
  · rcases stepStar_of_conTopped hR hcb hbw with ⟨y, hb, hw'⟩ | ⟨d, ys, zs', hb, hw', -⟩
    · rw [hw] at hw'
      have hxy : x = y := by simpa using hw'
      subst hxy
      exact Or.inl ⟨x, ha, hb⟩
    · rw [hw] at hw'
      simp at hw'
  · rcases stepStar_of_conTopped hR hcb hbw with ⟨y, hb, hw'⟩ | ⟨d, ys, zs', hb, hw', hyz⟩
    · rw [hw] at hw'
      simp at hw'
    · rw [hw] at hw'
      simp only [Term.app.injEq, Sum.inl.injEq] at hw'
      obtain ⟨hcd, hzs⟩ := hw'
      subst hcd
      subst hzs
      exact Or.inr ⟨c, xs, ys, ha, hb, forall₂_joinable_of_stepStar hxz hyz⟩

/-- Conversion is constructor-compatible in every destructor-rooted system in
which convertible constructor-topped terms are joinable. -/
theorem constructorCompatible_conv_of_conTopped_joinable {R : TRS (sigma ⊕ sigma) nu}
    (hR : DestructorRooted R)
    (hJ : ∀ a b, ConTopped a → ConTopped b → conv R a b → joinable R a b) :
    ConstructorCompatible (conv R) := by
  intro a b hca hcb hab
  rcases constructorCompatible_joinable hR a b hca hcb (hJ a b hca hcb hab) with
    hvar | ⟨c, xs, ys, ha, hb, hxy⟩
  · exact Or.inl hvar
  · exact Or.inr ⟨c, xs, ys, ha, hb, hxy.imp (fun _ _ h => conv.of_joinable h)⟩

/-- Conversion is constructor-compatible in every confluent destructor-rooted
system. -/
theorem constructorCompatible_conv_of_confluent {R : TRS (sigma ⊕ sigma) nu}
    (hR : DestructorRooted R) (hCR : confluent R) : ConstructorCompatible (conv R) :=
  constructorCompatible_conv_of_conTopped_joinable hR
    (fun _ _ _ _ h => joinable_of_conv hCR h)

/-! ## Conversion alone is not constructor-compatible -/

namespace ConvCounterexample

/-- The destructor constant `d`, the doubled signature's `inr false`. -/
def dConst : Term (Bool ⊕ Bool) Empty := .app (.inr false) []

/-- The constructor constant `c₁`, the doubled signature's `inl false`. -/
def cOne : Term (Bool ⊕ Bool) Empty := .app (.inl false) []

/-- The constructor constant `c₂`, the doubled signature's `inl true`. -/
def cTwo : Term (Bool ⊕ Bool) Empty := .app (.inl true) []

/-- The rule `d → c₁`. -/
def ruleOne : Rule (Bool ⊕ Bool) Empty where
  lhs := dConst
  rhs := cOne
  lhs_isApp := rfl

/-- The rule `d → c₂`. -/
def ruleTwo : Rule (Bool ⊕ Bool) Empty where
  lhs := dConst
  rhs := cTwo
  lhs_isApp := rfl

/-- The two-rule system `d → c₁`, `d → c₂`. -/
def system : TRS (Bool ⊕ Bool) Empty := [ruleOne, ruleTwo]

/-- Both left-hand sides are the destructor constant with no argument pattern,
so the system satisfies `ConstructorRules`. -/
theorem system_constructorRules : ConstructorRules system := by
  intro rule hmem
  simp only [system, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact ⟨false, [], rfl, by simp⟩
  · exact ⟨false, [], rfl, by simp⟩

/-- The root step `d → c₁`. -/
theorem step_dConst_cOne : Step system dConst cOne :=
  Step.root ⟨ruleOne, by simp [system], Term.var, rfl, rfl⟩

/-- The root step `d → c₂`. -/
theorem step_dConst_cTwo : Step system dConst cTwo :=
  Step.root ⟨ruleTwo, by simp [system], Term.var, rfl, rfl⟩

/-- The distinct constructor constants are convertible through `d`. -/
theorem cOne_conv_cTwo : conv system cOne cTwo :=
  conv.trans (conv.single (Or.inr step_dConst_cOne)) (conv.single (Or.inl step_dConst_cTwo))

/-- Conversion of this constructor system is not constructor-compatible. -/
theorem not_constructorCompatible_conv : ¬ ConstructorCompatible (conv system) := by
  intro h
  rcases h cOne cTwo (ConTopped.app false []) (ConTopped.app true []) cOne_conv_cTwo with
    ⟨x, -, -⟩ | ⟨f, xs, ys, h₁, h₂, -⟩
  · exact x.elim
  · simp only [cOne, cTwo, Term.app.injEq, Sum.inl.injEq] at h₁ h₂
    exact Bool.false_ne_true (h₁.1.trans h₂.1.symm)

/-- The system is not confluent, so the hypothesis of
`constructorCompatible_conv_of_confluent` cannot be dropped. -/
theorem system_not_confluent : ¬ confluent system := fun hCR =>
  not_constructorCompatible_conv
    (constructorCompatible_conv_of_confluent system_constructorRules.destructorRooted hCR)

/-- Joinability of the same system is constructor-compatible, as the general
theorem states. -/
theorem system_joinable_constructorCompatible : ConstructorCompatible (joinable system) :=
  constructorCompatible_joinable system_constructorRules.destructorRooted

end ConvCounterexample

/-- There is a constructor system whose conversion is not constructor-compatible. -/
theorem exists_constructorRules_not_constructorCompatible_conv :
    ∃ R : TRS (Bool ⊕ Bool) Empty, ConstructorRules R ∧ ¬ ConstructorCompatible (conv R) :=
  ⟨ConvCounterexample.system, ConvCounterexample.system_constructorRules,
    ConvCounterexample.not_constructorCompatible_conv⟩

end OperatorKO7.Meta.UniqueNormalization
