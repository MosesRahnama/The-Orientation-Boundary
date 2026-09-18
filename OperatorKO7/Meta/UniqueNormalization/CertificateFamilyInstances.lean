import OperatorKO7.Meta.UniqueNormalization.CertificateCarrierClassification

/-!
# A certificate family with nonlinear, collapsing, duplicating and nonterminating rules

Campaign: `COMMAND-CENTER/design/RESEARCH-ROADMAP.md`, package DC-2 of the Distinction
certificate closeout.

First, the F45 system of `ModelInfeasibility.lean`,

  `F(x, x, x) → x`,  `F(G(y, A), G(B, A), y) → y`,

is non-omega-overlapping (`f45_nonOmegaOverlapping`); its accepted Boolean certificate and
uniqueness theorem are unchanged.

Second, for every duplication count `r`, the seven-rule system `family_rules r` adjoins to the
capacity system `R_∞` of `CertificateCarrierClassification.lean` the F45 rules and

  `Z → G(Z, A)`,  `D(x) → J(x, …, x, D(x))`  (`r` displayed copies of `x`),

with symbol codes `F = 1`, `G = 2`, `A = 3`, `B = 4`, `S = 5`, `P = 6`, `H = 7`, `C = 8`,
`Z = 9`, `D = 10`, `J = 11`. The system is non-omega-overlapping and right-hand-side determined
for every `r` (`family_nonOmegaOverlapping`, `family_rhsDetermined`); it has a non-left-linear
rule, collapsing rules, an infinite reduction (`family_infinite_reduction`) and, exactly when
`r` is positive, a duplicating rule (`ruleD_duplicates_iff`).

The certificate lives on `Nat` with one extra successor fixed point (`optionRay`, carrier
`Option Nat`, `none` the fixed point): `S` successor, `P` truncated predecessor, `A = C = 0`,
`B = 1`, `Z` the fixed point, `F` its third coordinate, `G` the successor of its first
coordinate, `D` constantly `0`, `J` its last coordinate, `H` the equality test. The `H` overlap
condition forces `0 = 1`; the `F` overlap conditions force `u = S v`, `u = S B = 2` and `u = v`,
hence `2 = 3` (`familyRay_refutes_F_overlap`). Every other overlap fails by a clash of fixed
symbols. For every `r` a carrier admits a certificate exactly when it is infinite
(`family_certificate_iff_infinite`).

Proves: the class membership of both systems, unique normal forms with respect to conversion for
every `r` (`family_UNconv`), the reduction and duplication facts, and the carrier classification.
Does not prove: certificate existence for systems outside this family.
Relation: `Step (family_rules r)`, through `CStep (linHub (family_rules r))`.
Closure: one step for the reduction chain; conversion for uniqueness.
Strategy: full rewriting.
Trust: kernel checked; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`, `unsafe` or
`opaque`. `Classical.choice` enters through the ray construction on an arbitrary infinite
carrier and the equality test of `H`. Axiom footprints are printed by the paired reach file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.CertificateFamily

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization
open OperatorKO7.Meta.UniqueNormalization.CertificateCapacity

universe u v

/-! ## Unions of systems -/

section Unions

variable {sigma : Type u} {nu : Type v}

/-- **Non-omega-overlap of a union** whose cross pairs are refuted in both orders. -/
theorem nonOmegaOverlapping_append {R₁ R₂ : TRS sigma nu} (h₁ : NonOmegaOverlapping R₁)
    (h₂ : NonOmegaOverlapping R₂)
    (h₁₂ : ∀ r₁ ∈ R₁, ∀ r₂ ∈ R₂, ∀ q : Term sigma nu, Subterm q r₁.lhs → q.isApp = true →
      ¬ OmegaUnifiable q r₂.lhs)
    (h₂₁ : ∀ r₂ ∈ R₂, ∀ r₁ ∈ R₁, ∀ q : Term sigma nu, Subterm q r₂.lhs → q.isApp = true →
      ¬ OmegaUnifiable q r₁.lhs) :
    NonOmegaOverlapping (R₁ ++ R₂) := by
  intro r₁ hr₁ r₂ hr₂ q hq happ hu
  rcases List.mem_append.1 hr₁ with h1 | h1 <;> rcases List.mem_append.1 hr₂ with h2 | h2
  · exact h₁ r₁ h1 r₂ h2 q hq happ hu
  · exact absurd hu (h₁₂ r₁ h1 r₂ h2 q hq happ)
  · exact absurd hu (h₂₁ r₁ h1 r₂ h2 q hq happ)
  · exact h₂ r₁ h1 r₂ h2 q hq happ hu

/-- The variable condition of a union. -/
theorem rhsDetermined_append {R₁ R₂ : TRS sigma nu} (h₁ : TRS.RhsDetermined R₁)
    (h₂ : TRS.RhsDetermined R₂) : TRS.RhsDetermined (R₁ ++ R₂) := by
  intro rule hr
  rcases List.mem_append.1 hr with h | h
  · exact h₁ rule h
  · exact h₂ rule h

/-- **Model refutation for a union** of conditional systems whose cross pairs have no common
instance, in both orders. -/
theorem modelRefutesOverlaps_append {M : Type u} {C₁ C₂ : CTRS Nat Nat}
    {I : SymbolInterp Nat M} (h₁ : ModelRefutesOverlaps C₁ I) (h₂ : ModelRefutesOverlaps C₂ I)
    (h₁₂ : ∀ r₁ ∈ C₁, ∀ r₂ ∈ C₂, ∀ q : Term Nat Nat, Subterm q r₁.lhs → q.isApp = true →
      ∀ σ₁ σ₂ : Subst Nat Nat, Subst.apply σ₁ q ≠ Subst.apply σ₂ r₂.lhs)
    (h₂₁ : ∀ r₂ ∈ C₂, ∀ r₁ ∈ C₁, ∀ q : Term Nat Nat, Subterm q r₂.lhs → q.isApp = true →
      ∀ σ₁ σ₂ : Subst Nat Nat, Subst.apply σ₁ q ≠ Subst.apply σ₂ r₁.lhs) :
    ModelRefutesOverlaps (C₁ ++ C₂) I := by
  intro r₁ hr₁ r₂ hr₂ q hq happ σ₁ σ₂ heq hc₁ hc₂
  rcases List.mem_append.1 hr₁ with h1 | h1 <;> rcases List.mem_append.1 hr₂ with h2 | h2
  · exact h₁ r₁ h1 r₂ h2 q hq happ σ₁ σ₂ heq hc₁ hc₂
  · exact absurd heq (h₁₂ r₁ h1 r₂ h2 q hq happ σ₁ σ₂)
  · exact absurd heq (h₂₁ r₁ h1 r₂ h2 q hq happ σ₁ σ₂)
  · exact h₂ r₁ h1 r₂ h2 q hq happ σ₁ σ₂ heq hc₁ hc₂

end Unions

/-! ## Head-symbol separation -/

/-- Every non-variable subterm of `t` has its head symbol in `S`. -/
def AppHeadsIn (S : Nat → Prop) (t : Term Nat Nat) : Prop :=
  ∀ q, Subterm q t → q.isApp = true → ∃ f xs, q = Term.app f xs ∧ S f

/-- The root of `t` is an application headed in `T`. -/
def RootHeadIn (T : Nat → Prop) (t : Term Nat Nat) : Prop :=
  ∃ g ys, t = Term.app g ys ∧ T g

/-- **Separated heads exclude omega-overlaps** across two systems. -/
theorem not_omega_of_heads {R₁ R₂ : TRS Nat Nat} {S T : Nat → Prop}
    (hS : ∀ r ∈ R₁, AppHeadsIn S r.lhs) (hT : ∀ r ∈ R₂, RootHeadIn T r.lhs)
    (hdisj : ∀ f, S f → ¬ T f) :
    ∀ r₁ ∈ R₁, ∀ r₂ ∈ R₂, ∀ q : Term Nat Nat, Subterm q r₁.lhs → q.isApp = true →
      ¬ OmegaUnifiable q r₂.lhs := by
  intro r₁ h₁ r₂ h₂ q hq happ hu
  obtain ⟨f, xs, rfl, hf⟩ := hS r₁ h₁ q hq happ
  obtain ⟨g, ys, hg, hTg⟩ := hT r₂ h₂
  rw [hg] at hu
  have hfg := ClassExamples.omega_head_eq hu
  subst hfg
  exact hdisj f hf hTg

/-- **Separated heads exclude common instances** across two conditional systems. -/
theorem no_instance_of_heads {C₁ C₂ : CTRS Nat Nat} {S T : Nat → Prop}
    (hS : ∀ r ∈ C₁, AppHeadsIn S r.lhs) (hT : ∀ r ∈ C₂, RootHeadIn T r.lhs)
    (hdisj : ∀ f, S f → ¬ T f) :
    ∀ r₁ ∈ C₁, ∀ r₂ ∈ C₂, ∀ q : Term Nat Nat, Subterm q r₁.lhs → q.isApp = true →
      ∀ σ₁ σ₂ : Subst Nat Nat, Subst.apply σ₁ q ≠ Subst.apply σ₂ r₂.lhs := by
  intro r₁ h₁ r₂ h₂ q hq happ σ₁ σ₂ heq
  obtain ⟨f, xs, rfl, hf⟩ := hS r₁ h₁ q hq happ
  obtain ⟨g, ys, hg, hTg⟩ := hT r₂ h₂
  rw [hg] at heq
  simp only [Subst.apply_app, Term.app.injEq] at heq
  obtain ⟨rfl, -⟩ := heq
  exact hdisj f hf hTg

/-- Heads of a subterm whose left-hand-side classification is known. -/
theorem appHeadsIn_of_cases {S : Nat → Prop} {t : Term Nat Nat} {qs : List (Term Nat Nat)}
    (hcases : ∀ q, Subterm q t → q.isApp = true → q ∈ qs)
    (hqs : ∀ q ∈ qs, ∃ f xs, q = Term.app f xs ∧ S f) : AppHeadsIn S t :=
  fun q hq happ => hqs q (hcases q hq happ)

/-! ## The F45 system is non-omega-overlapping -/

/-- `F(x, x, x) → x`. -/
def f45Rule1 : Rule Nat Nat := ⟨.app 1 [.var 0, .var 0, .var 0], .var 0, rfl⟩

/-- `F(G(y, A), G(B, A), y) → y`. -/
def f45Rule2 : Rule Nat Nat :=
  ⟨.app 1 [.app 2 [.var 0, .app 3 []], .app 2 [.app 4 [], .app 3 []], .var 0], .var 0, rfl⟩

/-- The F45 system is exactly the two named rules. -/
theorem f45_trs_eq : F45Certificate.trs = [f45Rule1, f45Rule2] := rfl

/-- The non-variable subterms of `F(G(y, A), G(B, A), y)`. -/
theorem f45Rule2_subterm_cases {q : Term Nat Nat} (hq : Subterm q f45Rule2.lhs)
    (happ : q.isApp = true) :
    q = f45Rule2.lhs ∨ q = .app 2 [.var 0, .app 3 []] ∨ q = .app 3 [] ∨
      q = .app 2 [.app 4 [], .app 3 []] ∨ q = .app 4 [] := by
  change Subterm q (.app 1 [.app 2 [.var 0, .app 3 []], .app 2 [.app 4 [], .app 3 []], .var 0])
    at hq
  cases hq with
  | refl => exact Or.inl rfl
  | arg ha hsa =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · cases hsa with
        | refl => exact Or.inr (Or.inl rfl)
        | arg hb hsb =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
            rcases hb with rfl | rfl
            · rw [hsb.eq_of_var] at happ
              simp at happ
            · cases hsb with
              | refl => exact Or.inr (Or.inr (Or.inl rfl))
              | arg hc _ => simp at hc
      · cases hsa with
        | refl => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        | arg hb hsb =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
            rcases hb with rfl | rfl
            · cases hsb with
              | refl => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
              | arg hc _ => simp at hc
            · cases hsb with
              | refl => exact Or.inr (Or.inr (Or.inl rfl))
              | arg hc _ => simp at hc
      · rw [hsa.eq_of_var] at happ
        simp at happ

/-- **The two F45 left-hand sides are not omega-unifiable.** The shared variable of
`F(x, x, x)` relates `G(y, A)`, `G(B, A)` and `y`; decomposition gives `y ~ B`, hence
`B ~ G(B, A)`, a clash of `B` with `G`. -/
theorem f45_lhs_not_omegaUnifiable : ¬ OmegaUnifiable f45Rule1.lhs f45Rule2.lhs := by
  rintro ⟨E, hE, hst⟩
  simp only [f45Rule1, f45Rule2, leftCopy, rightCopy, Term.mapVar_app, Term.mapVarList_cons,
    Term.mapVarList_nil, Term.mapVar_var] at hst
  obtain ⟨-, hargs⟩ := hE.decomp hst
  simp only [List.forall₂_cons] at hargs
  obtain ⟨h1, h2, h3, -⟩ := hargs
  obtain ⟨-, hG⟩ := hE.decomp (hE.trans' (hE.symm' h1) h2)
  simp only [List.forall₂_cons] at hG
  have hxB := hE.trans' h3 hG.1
  exact absurd (hE.decomp (hE.trans' (hE.symm' hxB) h2)).1 (by decide)

/-- The same pair in the other order. -/
theorem f45_lhs_not_omegaUnifiable_symm : ¬ OmegaUnifiable f45Rule2.lhs f45Rule1.lhs := by
  rintro ⟨E, hE, hst⟩
  simp only [f45Rule1, f45Rule2, leftCopy, rightCopy, Term.mapVar_app, Term.mapVarList_cons,
    Term.mapVarList_nil, Term.mapVar_var] at hst
  obtain ⟨-, hargs⟩ := hE.decomp hst
  simp only [List.forall₂_cons] at hargs
  obtain ⟨h1, h2, h3, -⟩ := hargs
  obtain ⟨-, hG⟩ := hE.decomp (hE.trans' h1 (hE.symm' h2))
  simp only [List.forall₂_cons] at hG
  have hBx := hE.trans' (hE.symm' hG.1) h3
  exact absurd (hE.decomp (hE.trans' hBx (hE.symm' h2))).1 (by decide)

/-- **The F45 system is non-omega-overlapping.** Its only same-head root pair is refuted above;
every proper non-variable subterm is headed by `G`, `A` or `B`. -/
theorem f45_nonOmegaOverlapping : NonOmegaOverlapping F45Certificate.trs := by
  rw [f45_trs_eq]
  intro r₁ h₁ r₂ h₂ q hq happ hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl
  · have hq' := ClassExamples.flat_app_subterm_eq
      (fun a ha => ⟨0, by simpa using ha⟩) hq happ
    subst hq'
    rcases h₂ with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exact absurd hu f45_lhs_not_omegaUnifiable
  · rcases f45Rule2_subterm_cases hq happ with h | h | h | h | h
    · subst h
      rcases h₂ with rfl | rfl
      · exact absurd hu f45_lhs_not_omegaUnifiable_symm
      · exact ⟨rfl, rfl⟩
    all_goals
      subst h
      exfalso
      rcases h₂ with rfl | rfl <;>
        exact absurd (ClassExamples.omega_head_eq hu) (by decide)

/-- `F45Certificate.trs` is right-hand-side determined. -/
theorem f45_rhsDetermined : TRS.RhsDetermined F45Certificate.trs := by
  rw [f45_trs_eq]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · intro a b hab
    simpa [f45Rule1] using hab
  · intro a b hab
    simpa [f45Rule2] using hab

/-- **The F45 system is in the class and has unique normal forms**, from the accepted Boolean
certificate. -/
theorem f45_class_and_UNconv :
    NonOmegaOverlapping F45Certificate.trs ∧ TRS.RhsDetermined F45Certificate.trs ∧
      UNconv F45Certificate.trs :=
  ⟨f45_nonOmegaOverlapping, f45_rhsDetermined, F45Certificate.UNconv_trs⟩

/-! ## The seven-rule family -/

/-- `Z → G(Z, A)`. -/
def ruleZ : Rule Nat Nat := ⟨.app 9 [], .app 2 [.app 9 [], .app 3 []], rfl⟩

/-- `D(x) → J(x, …, x, D(x))` with `r` displayed copies of `x`. -/
def ruleD (r : Nat) : Rule Nat Nat :=
  ⟨.app 10 [.var 0], .app 11 (List.replicate r (.var 0) ++ [.app 10 [.var 0]]), rfl⟩

/-- The `Z` and `D` rules. -/
def zd_rules (r : Nat) : TRS Nat Nat := [ruleZ, ruleD r]

/-- **The seven-rule family.** -/
def family_rules (r : Nat) : TRS Nat Nat := capacity_rules ++ F45Certificate.trs ++ zd_rules r

/-- `P(S(x)) → x` belongs to every member of the family. -/
theorem ruleP_mem_family (r : Nat) : ruleP ∈ family_rules r :=
  List.mem_append_left _ (List.mem_append_left _ (List.Mem.head _))

/-- The capacity rules are contained in every member of the family. -/
theorem capacity_subset_family (r : Nat) : ∀ rule ∈ capacity_rules, rule ∈ family_rules r :=
  fun _ h => List.mem_append_left _ (List.mem_append_left _ h)

/-! ### Class membership -/

/-- Heads of non-variable subterms of the capacity left-hand sides. -/
theorem capacity_appHeads : ∀ r ∈ capacity_rules,
    AppHeadsIn (fun f => f = 5 ∨ f = 6 ∨ f = 7 ∨ f = 8) r.lhs := by
  intro r hr q hq happ
  have hr' := hr
  simp only [capacity_rules, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases capacity_lhs_subterm_cases hr hq happ with h | h | h | h | h
  · subst h
    rcases hr' with rfl | rfl | rfl
    · exact ⟨6, _, rfl, by simp⟩
    · exact ⟨7, _, rfl, by simp⟩
    · exact ⟨7, _, rfl, by simp⟩
  · exact ⟨5, _, h, by simp⟩
  · exact ⟨8, _, h, by simp⟩
  · exact ⟨5, _, h, by simp⟩
  · exact ⟨6, _, h, by simp⟩

/-- Root heads of the capacity left-hand sides. -/
theorem capacity_rootHeads : ∀ r ∈ capacity_rules, RootHeadIn (fun f => f = 6 ∨ f = 7) r.lhs := by
  intro r hr
  simp only [capacity_rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨6, _, rfl, by simp⟩
  · exact ⟨7, _, rfl, by simp⟩
  · exact ⟨7, _, rfl, by simp⟩

/-- Heads of non-variable subterms of the F45 left-hand sides. -/
theorem f45_appHeads : ∀ r ∈ F45Certificate.trs,
    AppHeadsIn (fun f => f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4) r.lhs := by
  rw [f45_trs_eq]
  intro r hr q hq happ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have hq' := ClassExamples.flat_app_subterm_eq
      (fun a ha => ⟨0, by simpa using ha⟩) hq happ
    exact ⟨1, _, hq', by simp⟩
  · rcases f45Rule2_subterm_cases hq happ with h | h | h | h | h
    · exact ⟨1, _, h, by simp⟩
    · exact ⟨2, _, h, by simp⟩
    · exact ⟨3, _, h, by simp⟩
    · exact ⟨2, _, h, by simp⟩
    · exact ⟨4, _, h, by simp⟩

/-- Root heads of the F45 left-hand sides. -/
theorem f45_rootHeads : ∀ r ∈ F45Certificate.trs, RootHeadIn (fun f => f = 1) r.lhs := by
  rw [f45_trs_eq]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨1, _, rfl, rfl⟩
  · exact ⟨1, _, rfl, rfl⟩

/-- Heads of non-variable subterms of the `Z` and `D` left-hand sides. -/
theorem zd_appHeads (r : Nat) : ∀ rule ∈ zd_rules r,
    AppHeadsIn (fun f => f = 9 ∨ f = 10) rule.lhs := by
  intro rule hr q hq happ
  simp only [zd_rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have hq' := ClassExamples.flat_app_subterm_eq (f := 9) (args := []) (by simp) hq happ
    exact ⟨9, _, hq', by simp⟩
  · have hq' := ClassExamples.flat_app_subterm_eq (f := 10) (args := [.var 0])
      (fun a ha => ⟨0, by simpa using ha⟩) hq happ
    exact ⟨10, _, hq', by simp⟩

/-- Root heads of the `Z` and `D` left-hand sides. -/
theorem zd_rootHeads (r : Nat) : ∀ rule ∈ zd_rules r, RootHeadIn (fun f => f = 9 ∨ f = 10) rule.lhs := by
  intro rule hr
  simp only [zd_rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨9, _, rfl, by simp⟩
  · exact ⟨10, _, rfl, by simp⟩

/-- The `Z` and `D` rules are non-omega-overlapping. -/
theorem zd_nonOmegaOverlapping (r : Nat) : NonOmegaOverlapping (zd_rules r) := by
  intro r₁ h₁ r₂ h₂ q hq happ hu
  simp only [zd_rules, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl
  · have hq' := ClassExamples.flat_app_subterm_eq (f := 9) (args := []) (by simp) hq happ
    rcases h₂ with rfl | rfl
    · exact ⟨rfl, hq'⟩
    · rw [hq'] at hu
      exact absurd (ClassExamples.omega_head_eq hu) (by decide)
  · have hq' := ClassExamples.flat_app_subterm_eq (f := 10) (args := [.var 0])
      (fun a ha => ⟨0, by simpa using ha⟩) hq happ
    rcases h₂ with rfl | rfl
    · rw [hq'] at hu
      exact absurd (ClassExamples.omega_head_eq hu) (by decide)
    · exact ⟨rfl, hq'⟩

/-- **Every member of the family is non-omega-overlapping**, including all cross-package pairs. -/
theorem family_nonOmegaOverlapping (r : Nat) : NonOmegaOverlapping (family_rules r) := by
  have hCF : NonOmegaOverlapping (capacity_rules ++ F45Certificate.trs) :=
    nonOmegaOverlapping_append capacity_nonOmegaOverlapping f45_nonOmegaOverlapping
      (not_omega_of_heads capacity_appHeads f45_rootHeads (by
        intro f hf hT
        omega))
      (not_omega_of_heads f45_appHeads capacity_rootHeads (by
        intro f hf hT
        omega))
  have hCFheads : ∀ rule ∈ capacity_rules ++ F45Certificate.trs,
      AppHeadsIn (fun f => f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4 ∨ f = 5 ∨ f = 6 ∨ f = 7 ∨ f = 8)
        rule.lhs := by
    intro rule hr q hq happ
    rcases List.mem_append.1 hr with h | h
    · obtain ⟨f, xs, hfq, hf⟩ := capacity_appHeads rule h q hq happ
      exact ⟨f, xs, hfq, by omega⟩
    · obtain ⟨f, xs, hfq, hf⟩ := f45_appHeads rule h q hq happ
      exact ⟨f, xs, hfq, by omega⟩
  have hCFroots : ∀ rule ∈ capacity_rules ++ F45Certificate.trs,
      RootHeadIn (fun f => f = 1 ∨ f = 6 ∨ f = 7) rule.lhs := by
    intro rule hr
    rcases List.mem_append.1 hr with h | h
    · obtain ⟨g, ys, hg, hT⟩ := capacity_rootHeads rule h
      exact ⟨g, ys, hg, by omega⟩
    · obtain ⟨g, ys, hg, hT⟩ := f45_rootHeads rule h
      exact ⟨g, ys, hg, by omega⟩
  exact nonOmegaOverlapping_append hCF (zd_nonOmegaOverlapping r)
    (not_omega_of_heads hCFheads (zd_rootHeads r) (by
      intro f hf hT
      omega))
    (not_omega_of_heads (zd_appHeads r) hCFroots (by
      intro f hf hT
      omega))

/-- `Z → G(Z, A)` is right-hand-side determined. -/
theorem ruleZ_rhsDetermined : Rule.RhsDetermined ruleZ :=
  fun _ _ _ => rfl

/-- `D(x) → J(x, …, x, D(x))` is right-hand-side determined. -/
theorem ruleD_rhsDetermined (r : Nat) : Rule.RhsDetermined (ruleD r) := by
  intro a b hab
  have h0 : a 0 = b 0 := by simpa [ruleD] using hab
  simp [ruleD, Subst.applyList_eq_map, List.map_replicate, h0]

/-- **Every member of the family is right-hand-side determined.** -/
theorem family_rhsDetermined (r : Nat) : TRS.RhsDetermined (family_rules r) := by
  refine rhsDetermined_append (rhsDetermined_append capacity_rhsDetermined f45_rhsDetermined) ?_
  intro rule hr
  simp only [zd_rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ruleZ_rhsDetermined
  · exact ruleD_rhsDetermined r

/-- The occurrence form of the variable condition for every member of the family. -/
theorem family_varCondition (r : Nat) :
    ∀ rule ∈ family_rules r, ∀ x, VarOccurs x rule.rhs → VarOccurs x rule.lhs := by
  intro rule hr x hx
  rcases List.mem_append.1 hr with h | h
  · rcases List.mem_append.1 h with h | h
    · exact capacity_varCondition rule h x hx
    · exact F45Certificate.trs_varCondition rule h x hx
  · simp only [zd_rules, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · change VarOccurs x (Term.app 2 [.app 9 [], .app 3 []]) at hx
      rcases hx.app_inv with ⟨a, ha, hxa⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;>
        (rcases hxa.app_inv with ⟨b, hb, -⟩; simp at hb)
    · change VarOccurs x (Term.app 11 (List.replicate r (.var 0) ++ [.app 10 [.var 0]])) at hx
      rcases hx.app_inv with ⟨a, ha, hxa⟩
      rcases List.mem_append.1 ha with ha | ha
      · rw [List.eq_of_mem_replicate ha] at hxa
        cases hxa
        exact VarOccurs.arg (List.Mem.head _) VarOccurs.here
      · simp only [List.mem_singleton] at ha
        subst ha
        exact hxa

/-! ### Rewriting features -/

/-- The tower `t 0 = Z`, `t (n + 1) = G(t n, A)`. -/
def zTower : Nat → Term Nat Nat
  | 0 => .app 9 []
  | n + 1 => .app 2 [zTower n, .app 3 []]

/-- **Each tower term rewrites to the next** by contracting the innermost `Z`. -/
theorem family_step_zTower (r n : Nat) : Step (family_rules r) (zTower n) (zTower (n + 1)) := by
  induction n with
  | zero =>
      exact Step.root ⟨ruleZ, List.mem_append_right _ (List.Mem.head _), Subst.id, rfl, rfl⟩
  | succ n ih =>
      exact Step.arg 2 [] [.app 3 []] ih

/-- The tower terms grow: `zTower n` has size `2 n + 1`. -/
theorem zTower_size (n : Nat) : (zTower n).size = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [zTower, Term.size_app, Term.sizeList_cons, Term.sizeList_nil, ih]
      omega

/-- The tower terms are pairwise different. -/
theorem zTower_injective : Function.Injective zTower := by
  intro m n h
  have hs := congrArg Term.size h
  rw [zTower_size, zTower_size] at hs
  omega

/-- **Every member of the family has an infinite reduction.** -/
theorem family_infinite_reduction (r : Nat) :
    ∃ t : Nat → Term Nat Nat, Function.Injective t ∧ ∀ n, Step (family_rules r) (t n) (t (n + 1)) :=
  ⟨zTower, zTower_injective, family_step_zTower r⟩

/-- A rule duplicates when some variable occurs more often on the right than on the left. -/
def RuleDuplicates (rule : Rule Nat Nat) : Prop :=
  ∃ x, (Term.varOccurrences rule.lhs).count x < (Term.varOccurrences rule.rhs).count x

/-- The occurrences of `r` copies of the variable `0`. -/
theorem flatMap_replicate_var (r : Nat) :
    (List.replicate r (Term.var 0 : Term Nat Nat)).flatMap Term.varOccurrences =
      List.replicate r 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [List.replicate_succ, List.flatMap_cons, ih]
      simp [Term.varOccurrences, List.replicate_succ]

/-- The variable occurrences of the `D` right-hand side: `r + 1` copies of `x`. -/
theorem ruleD_rhs_varOccurrences (r : Nat) :
    Term.varOccurrences (ruleD r).rhs = List.replicate (r + 1) 0 := by
  simp only [ruleD]
  rw [Term.varOccurrences, List.flatMap_append, flatMap_replicate_var]
  simp [Term.varOccurrences, List.replicate_succ']

/-- **The `D` rule has `r + 1` right-hand occurrences of `x` against one on the left.** -/
theorem family_rhs_occurrence_count (r : Nat) :
    (Term.varOccurrences (ruleD r).rhs).count 0 = r + 1 ∧
      (Term.varOccurrences (ruleD r).lhs).count 0 = 1 := by
  refine ⟨?_, ?_⟩
  · rw [ruleD_rhs_varOccurrences, List.count_replicate_self]
  · simp [ruleD, Term.varOccurrences]

/-- **The `D` rule duplicates exactly when `r` is positive.** The case `r = 0` is the erasing
frame `D(x) → J(D(x))`, which keeps one occurrence. -/
theorem ruleD_duplicates_iff (r : Nat) : RuleDuplicates (ruleD r) ↔ 0 < r := by
  have hlhs : Term.varOccurrences (ruleD r).lhs = [0] := by
    simp [ruleD, Term.varOccurrences]
  constructor
  · rintro ⟨x, hx⟩
    rw [hlhs, ruleD_rhs_varOccurrences] at hx
    by_cases h0 : x = 0
    · subst h0
      rw [List.count_replicate_self, List.count_singleton_self] at hx
      omega
    · have hnm : x ∉ List.replicate (r + 1) 0 := fun hm => h0 (List.eq_of_mem_replicate hm)
      rw [List.count_eq_zero_of_not_mem hnm] at hx
      omega
  · intro hr
    refine ⟨0, ?_⟩
    rw [hlhs, ruleD_rhs_varOccurrences, List.count_replicate_self, List.count_singleton_self]
    omega

/-- The family contains the non-left-linear rule `F(x, x, x) → x` and the collapsing rule
`P(S(x)) → x`. -/
theorem family_nonlinear_and_collapsing (r : Nat) :
    f45Rule1 ∈ family_rules r ∧ ¬ Term.LeftLinear f45Rule1.lhs ∧
      ruleP ∈ family_rules r ∧ ruleP.rhs = .var 0 := by
  refine ⟨List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _)), ?_, ruleP_mem_family r,
    rfl⟩
  simp [Term.LeftLinear, f45Rule1, Term.varOccurrences]

/-! ## The family interpretation -/

/-- A split ray whose base is its own predecessor, with one extra point fixed by both maps. -/
structure FamilyRay (M : Type u) extends SplitRay M where
  /-- The predecessor fixes the base point. -/
  prev_base : prev base = base
  /-- The extra fixed point, the value of `Z`. -/
  top : M
  /-- The successor fixes the extra point. -/
  next_top : next top = top
  /-- The predecessor fixes the extra point. -/
  prev_top : prev top = top

/-- The last coordinate of a list, `d` on the empty list. -/
def lastOr {M : Type u} (d : M) : List M → M
  | [] => d
  | [x] => x
  | _ :: y :: ys => lastOr d (y :: ys)

/-- The last coordinate of `xs ++ [x]` is `x`. -/
theorem lastOr_append_singleton {M : Type u} (d : M) (x : M) :
    ∀ xs : List M, lastOr d (xs ++ [x]) = x
  | [] => rfl
  | [_] => rfl
  | _ :: y :: ys => by
      change lastOr d (y :: (ys ++ [x])) = x
      exact lastOr_append_singleton d x (y :: ys)

namespace FamilyRay

variable {M : Type u}

/-- The successor of a family ray is injective. -/
theorem next_injective (ray : FamilyRay M) : Function.Injective ray.next :=
  ray.prev_next.injective

open Classical in
/-- **The family interpretation.** `F` third coordinate, `G` successor of the first coordinate,
`A = C = base`, `B = S(P(base))`, `S` successor, `P` predecessor, `H` equality test, `Z` the fixed
point, `D` constantly `base`, `J` last coordinate; every other symbol and arity takes `base`. -/
noncomputable def interp (ray : FamilyRay M) : SymbolInterp Nat M where
  op := fun f args =>
    if f = 11 then lastOr ray.base args else
    match f, args with
    | 1, [_, _, w] => w
    | 2, [u, _] => ray.next u
    | 3, [] => ray.base
    | 4, [] => ray.next (ray.prev ray.base)
    | 5, [u] => ray.next u
    | 6, [u] => ray.prev u
    | 7, [u, w] => if u = w then ray.base else ray.next (ray.prev ray.base)
    | 8, [] => ray.base
    | 9, [] => ray.top
    | 10, [_] => ray.base
    | _, _ => ray.base

theorem interp_F (ray : FamilyRay M) (u w z : M) : ray.interp.op 1 [u, w, z] = z := rfl
theorem interp_G (ray : FamilyRay M) (u w : M) : ray.interp.op 2 [u, w] = ray.next u := rfl
theorem interp_A (ray : FamilyRay M) : ray.interp.op 3 [] = ray.base := rfl
theorem interp_B (ray : FamilyRay M) : ray.interp.op 4 [] = ray.next (ray.prev ray.base) := rfl
theorem interp_S (ray : FamilyRay M) (u : M) : ray.interp.op 5 [u] = ray.next u := rfl
theorem interp_P (ray : FamilyRay M) (u : M) : ray.interp.op 6 [u] = ray.prev u := rfl
theorem interp_C (ray : FamilyRay M) : ray.interp.op 8 [] = ray.base := rfl
theorem interp_Z (ray : FamilyRay M) : ray.interp.op 9 [] = ray.top := rfl
theorem interp_D (ray : FamilyRay M) (u : M) : ray.interp.op 10 [u] = ray.base := rfl
theorem interp_J (ray : FamilyRay M) (xs : List M) : ray.interp.op 11 xs = lastOr ray.base xs :=
  rfl

open Classical in
theorem interp_H_eq (ray : FamilyRay M) (u : M) : ray.interp.op 7 [u, u] = ray.base := by
  change (if u = u then ray.base else ray.next (ray.prev ray.base)) = ray.base
  rw [if_pos rfl]

open Classical in
theorem interp_H_ne (ray : FamilyRay M) {u w : M} (h : u ≠ w) :
    ray.interp.op 7 [u, w] = ray.next (ray.prev ray.base) := by
  change (if u = w then ray.base else ray.next (ray.prev ray.base)) = _
  rw [if_neg h]

/-- `A` and `B` differ. -/
theorem base_ne_B (ray : FamilyRay M) : ray.base ≠ ray.next (ray.prev ray.base) :=
  fun h => ray.base_outside _ h.symm

/-- `B` is not a fixed point of the successor. -/
theorem B_not_fixed (ray : FamilyRay M) :
    ray.next (ray.next (ray.prev ray.base)) ≠ ray.next (ray.prev ray.base) := by
  intro h
  rw [ray.prev_base] at h
  exact ray.base_outside _ (ray.next_injective h)

/-- **Every rule of every family member holds.** -/
theorem interp_rulesHold (ray : FamilyRay M) (r : Nat) : ray.interp.RulesHold (family_rules r) := by
  intro rule hr val
  rcases List.mem_append.1 hr with h | h
  · rcases List.mem_append.1 h with h | h
    · simp only [capacity_rules, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · simp only [ruleP, SymbolInterp.eval_app, SymbolInterp.evalList_cons,
          SymbolInterp.evalList_nil, SymbolInterp.eval_var, interp_S, interp_P]
        exact ray.prev_next _
      · simp only [ruleH, SymbolInterp.eval_app, SymbolInterp.evalList_cons,
          SymbolInterp.evalList_nil, SymbolInterp.eval_var, interp_H_eq, interp_A]
      · simp only [ruleHC, SymbolInterp.eval_app, SymbolInterp.evalList_cons,
          SymbolInterp.evalList_nil, interp_C, interp_S, interp_P, interp_B]
        exact ray.interp_H_ne ray.base_ne_B
    · rw [f45_trs_eq] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · simp only [f45Rule1, SymbolInterp.eval_app, SymbolInterp.evalList_cons,
          SymbolInterp.evalList_nil, SymbolInterp.eval_var, interp_F]
      · simp only [f45Rule2, SymbolInterp.eval_app, SymbolInterp.evalList_cons,
          SymbolInterp.evalList_nil, SymbolInterp.eval_var, interp_F]
  · simp only [zd_rules, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · simp only [ruleZ, SymbolInterp.eval_app, SymbolInterp.evalList_cons,
        SymbolInterp.evalList_nil, interp_Z, interp_G, interp_A]
      exact ray.next_top.symm
    · simp only [ruleD, SymbolInterp.eval_app, SymbolInterp.evalList_eq_map, List.map_append,
        List.map_cons, List.map_nil, SymbolInterp.eval_var, interp_D, interp_J]
      exact (lastOr_append_singleton _ _ _).symm

end FamilyRay

/-! ### The hub linearization of the family -/

/-- The hub image of `F(x, x, x) → x`: fresh variables `2` and `5`, conditions `x ~ 2`, `x ~ 5`. -/
def hubF1 : CRule Nat Nat :=
  ⟨.app 1 [.var 0, .var 2, .var 5], .var 0, [(.var 0, .var 2), (.var 0, .var 5)], rfl⟩

/-- The hub image of `F(G(y, A), G(B, A), y) → y`: fresh variable `2`, condition `y ~ 2`. -/
def hubF2 : CRule Nat Nat :=
  ⟨.app 1 [.app 2 [.var 0, .app 3 []], .app 2 [.app 4 [], .app 3 []], .var 2], .var 0,
    [(.var 0, .var 2)], rfl⟩

/-- The hub image of `Z → G(Z, A)`. -/
def hubZ : CRule Nat Nat := ⟨.app 9 [], .app 2 [.app 9 [], .app 3 []], [], rfl⟩

/-- The hub image of `D(x) → J(x, …, x, D(x))`. -/
def hubD (r : Nat) : CRule Nat Nat :=
  ⟨.app 10 [.var 0], .app 11 (List.replicate r (.var 0) ++ [.app 10 [.var 0]]), [], rfl⟩

/-- The maximum of a list of zeros is zero. -/
theorem maxNatList_replicate_zero (n : Nat) : maxNatList (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, maxNatList, ih]

/-- The fresh base of `F(x, x, x) → x` is `1`. -/
theorem ruleFreshBase_f45Rule1 : ruleFreshBase f45Rule1 = 1 := by
  simp [ruleFreshBase, f45Rule1, maxNatList, Term.varOccurrences]

/-- The fresh base of `F(G(y, A), G(B, A), y) → y` is `1`. -/
theorem ruleFreshBase_f45Rule2 : ruleFreshBase f45Rule2 = 1 := by
  simp [ruleFreshBase, f45Rule2, maxNatList, Term.varOccurrences]

/-- The hub transform of `F(x, x, x) → x` splits the later occurrences to `2` and `5`. -/
theorem hubCRule_f45Rule1 : hubCRule f45Rule1 = hubF1 := by
  apply crule_ext
  · rw [hubCRule_lhs, ruleFreshBase_f45Rule1]
    simp [f45Rule1, hubF1, hubSplitTerm, hubSplitTermAux, hubSplitListAux, hubFresh, Nat.pair]
  · rfl
  · rw [hubCRule_conds, ruleFreshBase_f45Rule1]
    simp [f45Rule1, hubF1, hubSplitConditions, hubSplitTermAux, hubSplitListAux, hubFresh,
      Nat.pair]

/-- The hub transform of `F(G(y, A), G(B, A), y) → y` splits the later occurrence to `2`. -/
theorem hubCRule_f45Rule2 : hubCRule f45Rule2 = hubF2 := by
  apply crule_ext
  · rw [hubCRule_lhs, ruleFreshBase_f45Rule2]
    simp [f45Rule2, hubF2, hubSplitTerm, hubSplitTermAux, hubSplitListAux, hubFresh, Nat.pair]
  · rfl
  · rw [hubCRule_conds, ruleFreshBase_f45Rule2]
    simp [f45Rule2, hubF2, hubSplitConditions, hubSplitTermAux, hubSplitListAux, hubFresh,
      Nat.pair]

/-- The hub linearization of the F45 system. -/
theorem f45_hub_rules_eq : linHub F45Certificate.trs = [hubF1, hubF2] := by
  rw [f45_trs_eq]
  simp [linHub, hubCRule_f45Rule1, hubCRule_f45Rule2]

/-- The fresh base of `D(x) → J(x, …, x, D(x))` is `1`. -/
theorem ruleFreshBase_ruleD (r : Nat) : ruleFreshBase (ruleD r) = 1 := by
  simp only [ruleFreshBase]
  rw [ruleD_rhs_varOccurrences, maxNatList_replicate_zero]
  simp [ruleD, maxNatList, Term.varOccurrences]

/-- The hub transform of the ground rule `Z → G(Z, A)`. -/
theorem hubCRule_ruleZ : hubCRule ruleZ = hubZ := by
  apply crule_ext
  · rw [hubCRule_lhs]
    simp [ruleZ, hubZ, hubSplitTerm, hubSplitTermAux, hubSplitListAux]
  · rfl
  · rw [hubCRule_conds]
    simp [ruleZ, hubZ, hubSplitConditions, hubSplitTermAux, hubSplitListAux]

/-- The hub transform of the left-linear rule `D(x) → J(x, …, x, D(x))`. -/
theorem hubCRule_ruleD (r : Nat) : hubCRule (ruleD r) = hubD r := by
  apply crule_ext
  · rw [hubCRule_lhs, ruleFreshBase_ruleD]
    simp [ruleD, hubD, hubSplitTerm, hubSplitTermAux, hubSplitListAux]
  · rfl
  · rw [hubCRule_conds, ruleFreshBase_ruleD]
    simp [ruleD, hubD, hubSplitConditions, hubSplitTermAux, hubSplitListAux]

/-- The hub linearization of the `Z` and `D` rules. -/
theorem zd_hub_rules_eq (r : Nat) : linHub (zd_rules r) = [hubZ, hubD r] := by
  simp [linHub, zd_rules, hubCRule_ruleZ, hubCRule_ruleD]

/-- **The actual hub linearization of every family member.** -/
theorem family_hub_rules_eq (r : Nat) :
    linHub (family_rules r) = capacity_hub_rules ++ [hubF1, hubF2] ++ [hubZ, hubD r] := by
  have h : linHub (family_rules r) =
      linHub capacity_rules ++ linHub F45Certificate.trs ++ linHub (zd_rules r) := by
    simp [linHub, family_rules]
  rw [h, capacity_hub_rules_eq, f45_hub_rules_eq, zd_hub_rules_eq]

/-! ### The model refutes every overlap -/

/-- Heads of non-variable subterms of the capacity hub left-hand sides. -/
theorem capacity_hub_appHeads : ∀ c ∈ capacity_hub_rules,
    AppHeadsIn (fun f => f = 5 ∨ f = 6 ∨ f = 7 ∨ f = 8) c.lhs := by
  intro c hc q hq happ
  simp only [capacity_hub_rules, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · rcases hubP_subterm_cases hq happ with h | h
    · exact ⟨6, _, h, by simp⟩
    · exact ⟨5, _, h, by simp⟩
  · exact ⟨7, _, hubH_subterm_eq hq happ, by simp⟩
  · rcases hubHC_subterm_cases hq happ with h | h | h | h
    · exact ⟨7, _, h, by simp⟩
    · exact ⟨8, _, h, by simp⟩
    · exact ⟨5, _, h, by simp⟩
    · exact ⟨6, _, h, by simp⟩

/-- Root heads of the capacity hub left-hand sides. -/
theorem capacity_hub_rootHeads : ∀ c ∈ capacity_hub_rules,
    RootHeadIn (fun f => f = 6 ∨ f = 7) c.lhs := by
  intro c hc
  simp only [capacity_hub_rules, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ⟨6, _, rfl, by simp⟩
  · exact ⟨7, _, rfl, by simp⟩
  · exact ⟨7, _, rfl, by simp⟩

/-- The non-variable subterms of the second F45 hub left-hand side. -/
theorem hubF2_subterm_cases {q : Term Nat Nat} (hq : Subterm q hubF2.lhs)
    (happ : q.isApp = true) :
    q = hubF2.lhs ∨ q = .app 2 [.var 0, .app 3 []] ∨ q = .app 3 [] ∨
      q = .app 2 [.app 4 [], .app 3 []] ∨ q = .app 4 [] := by
  change Subterm q (.app 1 [.app 2 [.var 0, .app 3 []], .app 2 [.app 4 [], .app 3 []], .var 2])
    at hq
  cases hq with
  | refl => exact Or.inl rfl
  | arg ha hsa =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · cases hsa with
        | refl => exact Or.inr (Or.inl rfl)
        | arg hb hsb =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
            rcases hb with rfl | rfl
            · rw [hsb.eq_of_var] at happ
              simp at happ
            · cases hsb with
              | refl => exact Or.inr (Or.inr (Or.inl rfl))
              | arg hc _ => simp at hc
      · cases hsa with
        | refl => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        | arg hb hsb =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
            rcases hb with rfl | rfl
            · cases hsb with
              | refl => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
              | arg hc _ => simp at hc
            · cases hsb with
              | refl => exact Or.inr (Or.inr (Or.inl rfl))
              | arg hc _ => simp at hc
      · rw [hsa.eq_of_var] at happ
        simp at happ

/-- Heads of non-variable subterms of the F45 hub left-hand sides. -/
theorem f45_hub_appHeads : ∀ c ∈ [hubF1, hubF2],
    AppHeadsIn (fun f => f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4) c.lhs := by
  intro c hc q hq happ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · have hq' := ClassExamples.flat_app_subterm_eq (f := 1) (args := [.var 0, .var 2, .var 5])
      (fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨5, rfl⟩) hq happ
    exact ⟨1, _, hq', by simp⟩
  · rcases hubF2_subterm_cases hq happ with h | h | h | h | h
    · exact ⟨1, _, h, by simp⟩
    · exact ⟨2, _, h, by simp⟩
    · exact ⟨3, _, h, by simp⟩
    · exact ⟨2, _, h, by simp⟩
    · exact ⟨4, _, h, by simp⟩

/-- Root heads of the F45 hub left-hand sides. -/
theorem f45_hub_rootHeads : ∀ c ∈ [hubF1, hubF2], RootHeadIn (fun f => f = 1) c.lhs := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨1, _, rfl, rfl⟩
  · exact ⟨1, _, rfl, rfl⟩

/-- Heads of non-variable subterms of the `Z` and `D` hub left-hand sides. -/
theorem zd_hub_appHeads (r : Nat) : ∀ c ∈ [hubZ, hubD r],
    AppHeadsIn (fun f => f = 9 ∨ f = 10) c.lhs := by
  intro c hc q hq happ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨9, _, ClassExamples.flat_app_subterm_eq (f := 9) (args := []) (by simp) hq happ,
      by simp⟩
  · exact ⟨10, _, ClassExamples.flat_app_subterm_eq (f := 10) (args := [.var 0])
      (fun a ha => ⟨0, by simpa using ha⟩) hq happ, by simp⟩

/-- Root heads of the `Z` and `D` hub left-hand sides. -/
theorem zd_hub_rootHeads (r : Nat) : ∀ c ∈ [hubZ, hubD r],
    RootHeadIn (fun f => f = 9 ∨ f = 10) c.lhs := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨9, _, rfl, by simp⟩
  · exact ⟨10, _, rfl, by simp⟩

namespace FamilyRay

variable {M : Type u}

/-- **The `F` overlap is refuted.** At the root overlap of `F(x, 2, 5)` (conditions `x ~ 2`,
`x ~ 5`) with `F(G(y, A), G(B, A), 2)` (condition `y ~ 2`), the values satisfy `u = S v`,
`u = S B`, `u = w` and `v = w`; so `v = B` and `S B = B`, which the ray excludes. -/
theorem familyRay_refutes_F_overlap (ray : FamilyRay M) (σ₁ σ₂ : Subst Nat Nat)
    (heq : Subst.apply σ₁ hubF1.lhs = Subst.apply σ₂ hubF2.lhs)
    (hc₁ : ∀ p ∈ hubF1.conds, ∀ ρ : Nat → M,
      ray.interp.eval ρ (Subst.apply σ₁ p.1) = ray.interp.eval ρ (Subst.apply σ₁ p.2))
    (hc₂ : ∀ p ∈ hubF2.conds, ∀ ρ : Nat → M,
      ray.interp.eval ρ (Subst.apply σ₂ p.1) = ray.interp.eval ρ (Subst.apply σ₂ p.2)) :
    False := by
  simp [hubF1, hubF2] at heq
  obtain ⟨h0, h2, h5⟩ := heq
  have c1 := hc₁ (.var 0, .var 2) (List.Mem.head _) (fun _ => ray.base)
  have c2 := hc₁ (.var 0, .var 5) (List.Mem.tail _ (List.Mem.head _)) (fun _ => ray.base)
  have c3 := hc₂ (.var 0, .var 2) (List.Mem.head _) (fun _ => ray.base)
  simp only [Subst.apply_var] at c1 c2 c3
  rw [h0, h2] at c1
  rw [h0, h5] at c2
  simp only [SymbolInterp.eval_app, SymbolInterp.evalList_cons, SymbolInterp.evalList_nil,
    interp_G, interp_A, interp_B] at c1 c2
  have hv := ray.next_injective c1
  rw [← c3] at c2
  rw [hv] at c2
  exact ray.B_not_fixed c2

/-- The F45 hub rules are refuted by every family ray. -/
theorem interp_refutes_f45 (ray : FamilyRay M) : ModelRefutesOverlaps [hubF1, hubF2] ray.interp := by
  intro r₁ h₁ r₂ h₂ q hq happ σ₁ σ₂ heq hc₁ hc₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl
  · have hq' := ClassExamples.flat_app_subterm_eq (f := 1) (args := [.var 0, .var 2, .var 5])
      (fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨5, rfl⟩) hq happ
    subst hq'
    rcases h₂ with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exact (ray.familyRay_refutes_F_overlap σ₁ σ₂ heq hc₁ hc₂).elim
  · rcases hubF2_subterm_cases hq happ with h | h | h | h | h
    · subst h
      rcases h₂ with rfl | rfl
      · exact (ray.familyRay_refutes_F_overlap σ₂ σ₁ heq.symm hc₂ hc₁).elim
      · exact ⟨rfl, rfl⟩
    all_goals
      subst h
      exfalso
      rcases h₂ with rfl | rfl <;> simp [hubF1, hubF2] at heq

/-- The `Z` and `D` hub rules are refuted by every interpretation: their only overlaps are the
exempt root self-overlaps. -/
theorem interp_refutes_zd (ray : FamilyRay M) (r : Nat) :
    ModelRefutesOverlaps [hubZ, hubD r] ray.interp := by
  intro r₁ h₁ r₂ h₂ q hq happ σ₁ σ₂ heq _ _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl
  · have hq' := ClassExamples.flat_app_subterm_eq (f := 9) (args := []) (by simp) hq happ
    subst hq'
    rcases h₂ with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · simp [hubD] at heq
  · have hq' := ClassExamples.flat_app_subterm_eq (f := 10) (args := [.var 0])
      (fun a ha => ⟨0, by simpa using ha⟩) hq happ
    subst hq'
    rcases h₂ with rfl | rfl
    · simp [hubZ] at heq
    · exact ⟨rfl, rfl⟩

/-- **Every family ray refutes every non-trivial overlap of the hub linearization of every family
member**, including every cross-package pair. -/
theorem interp_refutes (ray : FamilyRay M) (r : Nat) :
    ModelRefutesOverlaps (linHub (family_rules r)) ray.interp := by
  rw [family_hub_rules_eq]
  have hcap : ModelRefutesOverlaps capacity_hub_rules ray.interp :=
    capacity_hub_refutes_of_separation ray.interp ray.base_ne_B
  have hCF : ModelRefutesOverlaps (capacity_hub_rules ++ [hubF1, hubF2]) ray.interp :=
    modelRefutesOverlaps_append hcap ray.interp_refutes_f45
      (no_instance_of_heads capacity_hub_appHeads f45_hub_rootHeads (by
        intro f hf hT
        omega))
      (no_instance_of_heads f45_hub_appHeads capacity_hub_rootHeads (by
        intro f hf hT
        omega))
  have hCFheads : ∀ c ∈ capacity_hub_rules ++ [hubF1, hubF2],
      AppHeadsIn (fun f => f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4 ∨ f = 5 ∨ f = 6 ∨ f = 7 ∨ f = 8)
        c.lhs := by
    intro c hc q hq happ
    rcases List.mem_append.1 hc with h | h
    · obtain ⟨f, xs, hfq, hf⟩ := capacity_hub_appHeads c h q hq happ
      exact ⟨f, xs, hfq, by omega⟩
    · obtain ⟨f, xs, hfq, hf⟩ := f45_hub_appHeads c h q hq happ
      exact ⟨f, xs, hfq, by omega⟩
  have hCFroots : ∀ c ∈ capacity_hub_rules ++ [hubF1, hubF2],
      RootHeadIn (fun f => f = 1 ∨ f = 6 ∨ f = 7) c.lhs := by
    intro c hc
    rcases List.mem_append.1 hc with h | h
    · obtain ⟨g, ys, hg, hT⟩ := capacity_hub_rootHeads c h
      exact ⟨g, ys, hg, by omega⟩
    · obtain ⟨g, ys, hg, hT⟩ := f45_hub_rootHeads c h
      exact ⟨g, ys, hg, by omega⟩
  exact modelRefutesOverlaps_append hCF (ray.interp_refutes_zd r)
    (no_instance_of_heads hCFheads (zd_hub_rootHeads r) (by
      intro f hf hT
      omega))
    (no_instance_of_heads (zd_hub_appHeads r) hCFroots (by
      intro f hf hT
      omega))

end FamilyRay

/-! ### The countable certificate -/

/-- **The ray on `Nat` with one extra point**: `none` is the fixed point. -/
def optionRay : FamilyRay (Option Nat) where
  next := Option.map Nat.succ
  prev := Option.map Nat.pred
  base := some 0
  prev_next := by
    intro x
    cases x <;> rfl
  base_outside := by
    intro x
    cases x <;> simp
  prev_base := rfl
  top := none
  next_top := rfl
  prev_top := rfl

/-- **The countable family interpretation.** -/
noncomputable def family_countable_interp : SymbolInterp Nat (Option Nat) := optionRay.interp

/-- On the countable interpretation, `A = C = 0`, `B = 1`, and `Z` is the fixed point. -/
theorem family_countable_values :
    family_countable_interp.op 3 [] = some 0 ∧ family_countable_interp.op 8 [] = some 0 ∧
      family_countable_interp.op 4 [] = some 1 ∧ family_countable_interp.op 9 [] = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Every rule of every family member holds in the countable interpretation. -/
theorem family_rulesHold (r : Nat) : family_countable_interp.RulesHold (family_rules r) :=
  optionRay.interp_rulesHold r

/-- The countable interpretation refutes every overlap of every family member. -/
theorem family_model_refutes (r : Nat) :
    ModelRefutesOverlaps (linHub (family_rules r)) family_countable_interp :=
  optionRay.interp_refutes r

/-- **Every family member has unique normal forms with respect to conversion.**

Relation: `Step (family_rules r)`. Closure: conversion. Strategy: full rewriting. -/
theorem family_UNconv (r : Nat) : UNconv (family_rules r) :=
  UNconv_of_linHub_model (family_varCondition r) family_countable_interp (family_rulesHold r)
    (family_model_refutes r)

/-! ## The carrier classification for every family member -/

section Classification

variable {M : Type u}

/-- The embedding shifted by one index. -/
def shiftEmbedding (e : Nat ↪ M) : Nat ↪ M :=
  ⟨fun n => e (n + 1), fun _ _ h => Nat.succ_injective (e.injective h)⟩

/-- `e 0` lies outside the image of the shifted embedding. -/
theorem not_mem_shift (e : Nat ↪ M) : ¬ ∃ n, shiftEmbedding e n = e 0 := by
  rintro ⟨n, hn⟩
  have h : e (n + 1) = e 0 := hn
  exact Nat.succ_ne_zero n (e.injective h)

/-- **The family ray of an embedding of `Nat`**: the shifted ray, with `e 0` as the fixed point. -/
noncomputable def FamilyRay.ofEmbedding (e : Nat ↪ M) : FamilyRay M where
  toSplitRay := SplitRay.ofEmbedding (shiftEmbedding e)
  prev_base := rayPrev_apply (shiftEmbedding e) 0
  top := e 0
  next_top := rayNext_of_not_mem (shiftEmbedding e) (not_mem_shift e)
  prev_top := rayPrev_of_not_mem (shiftEmbedding e) (not_mem_shift e)

/-- **Construction: every family ray gives a certificate for every family member.** -/
theorem family_certificate_of_familyRay (ray : FamilyRay M) (r : Nat) :
    HasCertificate (family_rules r) M :=
  ⟨ray.interp, ray.interp_rulesHold r, ray.interp_refutes r⟩

/-- **Extraction: a family certificate restricts to the capacity overlap** and yields a split ray. -/
theorem family_splitRay_of_certificate {r : Nat} (h : HasCertificate (family_rules r) M) :
    Nonempty (SplitRay M) := by
  obtain ⟨I, hR, hcert⟩ := h
  have hH : hubH ∈ linHub (family_rules r) := by
    rw [family_hub_rules_eq]
    exact List.mem_append_left _ (List.mem_append_left _ (List.Mem.tail _ (List.Mem.head _)))
  have hHC : hubHC ∈ linHub (family_rules r) := by
    rw [family_hub_rules_eq]
    exact List.mem_append_left _
      (List.mem_append_left _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hinv := leftInverse_of_ruleP_mem (ruleP_mem_family r) hR
  have hsep := separation_of_hub_members hH hHC hcert
  exact ⟨⟨succOp I, predOp I, baseOp I, hinv, base_outside_of_separation hinv hsep⟩⟩

/-- **Every family certificate carrier receives an embedding of `Nat`.** -/
theorem family_embedding {r : Nat} (h : HasCertificate (family_rules r) M) :
    Nonempty (Nat ↪ M) := by
  obtain ⟨ray⟩ := family_splitRay_of_certificate h
  exact ⟨ray.embedding⟩

/-- **For every duplication count, a carrier has a family certificate exactly when it is
infinite.** -/
theorem family_certificate_iff_infinite (r : Nat) (M : Type u) :
    HasCertificate (family_rules r) M ↔ Infinite M := by
  constructor
  · intro h
    obtain ⟨ray⟩ := family_splitRay_of_certificate h
    exact ray.infinite
  · intro _
    exact family_certificate_of_familyRay (FamilyRay.ofEmbedding (Infinite.natEmbedding M)) r

/-- **The countable minimum for every duplication count.** `Option Nat` carries a certificate, and
`Nat` embeds into every certificate carrier. -/
theorem family_minimal_carrier (r : Nat) :
    HasCertificate (family_rules r) (Option Nat) ∧
      ∀ M : Type u, HasCertificate (family_rules r) M → Nonempty (Nat ↪ M) :=
  ⟨family_certificate_of_familyRay optionRay r, fun _ h => family_embedding h⟩

/-- No finite carrier has a family certificate, although finite rule models exist. -/
theorem family_no_finite_certificate (r : Nat) [Finite M] :
    ¬ HasCertificate (family_rules r) M := by
  intro h
  obtain ⟨e⟩ := family_embedding h
  haveI : Infinite M := Infinite.of_injective e e.injective
  exact not_finite M

/-- The one-element model satisfies every family rule. -/
theorem family_unit_rulesHold (r : Nat) : unitInterp.RulesHold (family_rules r) :=
  fun _ _ _ => rfl

end Classification

end OperatorKO7.Meta.UniqueNormalization.CertificateFamily
