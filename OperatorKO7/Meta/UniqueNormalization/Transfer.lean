import OperatorKO7.Meta.UniqueNormalization.Linearization
import OperatorKO7.Meta.UniqueNormalization.RewriteAux
import OperatorKO7.Meta.UniqueNormalization.Examples
import OperatorKO7.Meta.UniqueNormalization.Fence

/-!
# The transfer theorem: confluence of the linearization gives UN=

Campaign: `Roadmaps\klop\ROADMAP.md`, WP-K2, route R2; proof skeleton in
Section 11.4 of that roadmap.

The classical route to unique normal forms for systems with repeated left-hand
side variables, from the Chew lineage (Chew 1981; Klop and de Vrijer; Toyama and
Oyamaguchi; Mano and Ogawa), runs through conditional linearization: replace the
internalized equality test by an explicit convertibility condition, and read UN=
of the original system off confluence of the linearization. Kahrs and Smith
mention semi-equational conditional systems without developing this route
(frozen answer Q4), so this theorem is cited to that lineage and never to FSCD
2016.

Three components, in order:

* `cstep_of_step`, every original step is a conditional step at level 1;
* `conv_of_cstepLevel`, every conditional step at any level is an original
  conversion, so the two systems have the same equational theory;
* `nf_no_cstep`, under confluence of the linearization an original normal form
  admits no conditional step, by induction on term size.

The transfer theorem follows: convertible original normal forms lift to
convertible conditional terms, confluence joins them, and both being conditional
normal forms forces the join to be each of them.

The two negative controls at the end are theorems about classically known
systems: the conditional linearizations of Huet's system and of the KO7 kernel
both fail confluence, because both systems fail UN=.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Shared lemmas -/

/-- Conversion lifts through a suffix of an argument list. -/
theorem conv.args_append {R : TRS sigma nu} (f : sigma) :
    ∀ (pre : List (Term sigma nu)) {xs ys : List (Term sigma nu)},
      List.Forall₂ (conv R) xs ys →
      conv R (.app f (pre ++ xs)) (.app f (pre ++ ys)) := by
  intro pre xs
  induction xs generalizing pre with
  | nil =>
      intro ys h
      cases h
      exact conv.refl R _
  | cons a as ih =>
      intro ys h
      cases h with
      | cons hab habs =>
          rename_i b _
          refine conv.trans (conv.arg_congr R f pre as hab) ?_
          simpa using ih (pre ++ [b]) habs

/-- Conversion lifts through every argument at once. -/
theorem conv.args {R : TRS sigma nu} (f : sigma) {xs ys : List (Term sigma nu)}
    (h : List.Forall₂ (conv R) xs ys) : conv R (.app f xs) (.app f ys) := by
  simpa using conv.args_append f [] h

/-- Substitutions pointwise convertible on the occurring variables give
convertible instances. -/
theorem conv_apply_pointwise {R : TRS sigma nu} {s s' : Subst sigma nu} :
    ∀ (t : Term sigma nu), (∀ x, VarOccurs x t → conv R (s x) (s' x)) →
      conv R (Subst.apply s t) (Subst.apply s' t) := by
  intro t
  induction t using Term.rec' with
  | hvar x => intro h; exact h x VarOccurs.here
  | happ f args ih =>
      intro h
      simp only [Subst.apply_app, Subst.applyList_eq_map]
      exact conv.args f (forall₂_map_map
        (fun a ha => ih a ha (fun x hx => h x (VarOccurs.arg ha hx))))

/-- A subterm of a normal form is a normal form. -/
theorem NormalForm.subterm {R : TRS sigma nu} {t s : Term sigma nu}
    (ht : NormalForm R t) (hsub : Subterm s t) : NormalForm R s := by
  induction hsub with
  | refl => exact ht
  | @arg a f args hmem _ ih =>
      refine ih ?_
      intro w hw
      obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
      exact ht _ (hsplit ▸ Step.arg f pre post hw)

/-- A conversion built from level-`n` steps is a conversion of the system. The
level is given explicitly, because recovering it from a `CStepE` type would ask
unification to invert the definition of `CStepLevel`. -/
theorem cconv_of_relConv_level {C : CTRS sigma nu} (n : Nat) {s t : Term sigma nu}
    (h : relConv (CStepLevel C n) s t) : cconv C s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih =>
      refine Relation.ReflTransGen.tail ih ?_
      rcases hlast with hab | hab
      · exact Or.inl ⟨n, hab⟩
      · exact Or.inr ⟨n, hab⟩

/-! ## Every original step is a conditional step -/

/-- **F1.** An original root contraction is a conditional step at level 1: the
collapse substitution instantiates the conditional rule, and every condition
instance is a pair of equal terms, discharged by reflexivity. -/
theorem cstepLevel_one_of_rootStep {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) {s t : Term sigma nu} (h : rootStep R s t) :
    CStepLevel C 1 s t := by
  obtain ⟨rule, hrule, tau, hs, ht⟩ := h
  obtain ⟨crule, hcrule, hrhs, rho, hcollapse, hconds, -, hrhsfix⟩ := hlin.2 rule hrule
  refine CStepE.root ⟨crule, hcrule, fun v => tau (rho v), ?_, ?_, ?_⟩
  · rw [hs, ← hcollapse, apply_mapVar]
  · rw [ht, hrhs, ← mapVar_id_on rule.rhs (by
      intro x hx
      exact hrhsfix x (by rw [hrhs]; exact hx)), apply_mapVar, mapVar_id_on]
    intro x hx
    exact hrhsfix x (by rw [hrhs]; exact hx)
  · intro p hp
    obtain ⟨x, y, rfl, hx, hy, -, -⟩ := hconds p hp
    simp only [Subst.apply_var, hx, hy]
    exact Relation.ReflTransGen.refl

/-- **F1, context-closed form.** Every original step is already a conditional step at
level `1`, not merely at some unspecified level. -/
theorem cstepLevel_one_of_step {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) :
    ∀ {s t : Term sigma nu}, Step R s t → CStepLevel C 1 s t := by
  intro s t h
  induction h with
  | root hr => exact cstepLevel_one_of_rootStep hlin hr
  | arg f pre post _ ih => exact CStepE.arg f pre post ih

/-- Every original step persists at every positive conditional level. -/
theorem cstepLevel_of_step {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) {n : Nat} (hn : 1 ≤ n)
    {s t : Term sigma nu} (h : Step R s t) : CStepLevel C n s t :=
  CStepLevel.mono_of_le C hn (cstepLevel_one_of_step hlin h)

/-- Every original step is a conditional step. -/
theorem cstep_of_step {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) {s t : Term sigma nu} (h : Step R s t) : CStep C s t :=
  CStep.of_level (cstepLevel_one_of_step hlin h)

/-- Original conversions are conditional conversions. -/
theorem cconv_of_conv {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) {s t : Term sigma nu} (h : conv R s t) :
    cconv C s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih =>
      refine Relation.ReflTransGen.tail ih ?_
      rcases hlast with hstep | hstep
      · exact Or.inl (cstep_of_step hlin hstep)
      · exact Or.inr (cstep_of_step hlin hstep)

/-! ## Every conditional step is an original conversion -/

/-- **F2.** A conditional step at any level is an original conversion. The outer
induction is on the level, the inner one on the step derivation; the root case
chains the pointwise conversion of the collapse, the collapse equation, the
original step, and the verbatim right-hand side. -/
theorem conv_of_cstepLevel {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) :
    ∀ (n : Nat) {s t : Term sigma nu}, CStepLevel C n s t → conv R s t := by
  intro n
  induction n with
  | zero => intro s t h; exact h.elim
  | succ m ihlevel =>
      intro s t h
      induction h with
      | @root s' t' hr =>
          obtain ⟨crule, hcrule, sb, hs, ht, hcond⟩ := hr
          obtain ⟨rule, hrule, hrhs, rho, hcollapse, hconds, hlhs, -⟩ :=
            hlin.1 crule hcrule
          -- A: the collapse acts convertibly on the conditional left-hand side
          have hA : conv R (Subst.apply sb crule.lhs)
              (Subst.apply (fun v => sb (rho v)) crule.lhs) := by
            refine conv_apply_pointwise crule.lhs ?_
            intro x hx
            rcases hlhs x hx with hfix | hpair
            · rw [hfix]
            · have := hcond _ hpair
              simp only [Subst.apply_var] at this
              exact conv.symm (conv_of_relConv (fun _ _ hab => ihlevel hab) this)
          -- B: the collapse equation
          have hB : Subst.apply (fun v => sb (rho v)) crule.lhs
              = Subst.apply sb rule.lhs := by
            rw [← hcollapse, apply_mapVar]
          -- C: the original step
          have hC : conv R (Subst.apply sb rule.lhs) (Subst.apply sb rule.rhs) :=
            conv.of_step (Step.root ⟨rule, hrule, sb, rfl, rfl⟩)
          -- D: the verbatim right-hand side
          rw [hs, ht, hrhs]
          exact conv.trans hA (hB ▸ hC)
      | arg f pre post _ ih => exact conv.arg_congr R f pre post ih

/-- Conditional steps are original conversions. -/
theorem conv_of_cstep {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) {s t : Term sigma nu} (h : CStep C s t) :
    conv R s t :=
  let ⟨n, hn⟩ := h
  conv_of_cstepLevel hlin n hn

/-- **The two systems have the same equational theory.** -/
theorem cconv_iff_conv {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) (s t : Term sigma nu) :
    cconv C s t ↔ conv R s t :=
  ⟨fun h => conv_of_relConv (fun _ _ hab => conv_of_cstep hlin hab) h,
    cconv_of_conv hlin⟩

/-! ## Normal forms of the original system are conditional normal forms -/

/-- **L.** Under confluence of the linearization, an original normal form admits
no conditional step. The induction is on a size bound: an argument step is
refuted by the induction hypothesis on a smaller subterm, and a root step splits
on whether every condition instance is already equal. If they are, the collapse
turns the conditional redex into an original redex; if one pair differs, its two
sides are strictly smaller original normal forms that confluence joins, so the
induction hypothesis forces them equal. -/
theorem nf_no_cstep {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) (hconf : cconfluent C) :
    ∀ (N : Nat) (t : Term sigma nu), t.size ≤ N → NormalForm R t →
      ∀ s, ¬ CStep C t s := by
  intro N
  induction N with
  | zero =>
      intro t hsize _ _ _
      exact absurd hsize (by simpa using Nat.not_succ_le_zero 0 ∘ (Term.one_le_size t).trans)
  | succ N ih =>
      intro t hsize hnf s hstep
      obtain ⟨n, hn⟩ := hstep
      cases n with
      | zero => exact hn.elim
      | succ m =>
          -- the source of a conditional step is an application
          cases t with
          | var x =>
              cases hn with
              | root hr =>
                  obtain ⟨crule, _, sb, hsrc, -, -⟩ := hr
                  have hApp := crule.lhs_isApp
                  cases hlhs : crule.lhs with
                  | var w => rw [hlhs] at hApp; simp at hApp
                  | app g gargs =>
                      rw [hlhs] at hsrc
                      simp only [Subst.apply_app] at hsrc
                      exact absurd hsrc (by simp)
          | app f args =>
              rcases CStepE.app_inv hn with hroot | ⟨pre, post, a, b, hargs, -, hab⟩
              · -- root case
                obtain ⟨crule, hcrule, sb, hsrc, -, hcond⟩ := hroot
                obtain ⟨rule, hrule, -, rho, hcollapse, hconds, hlhs, -⟩ :=
                  hlin.1 crule hcrule
                by_cases hall : ∀ p ∈ crule.conds,
                    Subst.apply sb p.1 = Subst.apply sb p.2
                · -- every condition instance is already equal: an original redex
                  have hagree : ∀ x, VarOccurs x crule.lhs → sb x = sb (rho x) := by
                    intro x hx
                    rcases hlhs x hx with hfix | hpair
                    · rw [hfix]
                    · have := hall _ hpair
                      simpa using this.symm
                  have hredex : Term.app f args = Subst.apply sb rule.lhs := by
                    rw [hsrc, apply_eq_of_occurs_agree crule.lhs hagree,
                      ← apply_mapVar, hcollapse]
                  exact hnf _ (hredex ▸ Step.root ⟨rule, hrule, sb, rfl, rfl⟩)
                · -- some condition instance differs: two smaller normal forms join
                  push_neg at hall
                  obtain ⟨p, hp, hne⟩ := hall
                  obtain ⟨x, y, rfl, -, -, hxocc, hyocc⟩ := hconds p hp
                  simp only [Subst.apply_var] at hne
                  have hxlt : (sb x).size < (Term.app f args).size := by
                    rw [hsrc]; exact hxocc.size_apply_lt_of_isApp crule.lhs_isApp sb
                  have hylt : (sb y).size < (Term.app f args).size := by
                    rw [hsrc]; exact hyocc.size_apply_lt_of_isApp crule.lhs_isApp sb
                  have hxnf : NormalForm R (sb x) := by
                    refine hnf.subterm ?_
                    rw [hsrc]; exact hxocc.subterm_apply sb
                  have hynf : NormalForm R (sb y) := by
                    refine hnf.subterm ?_
                    rw [hsrc]; exact hyocc.subterm_apply sb
                  -- the condition instances are conditionally convertible
                  have hconvxy : cconv C (sb x) (sb y) := by
                    have hc := hcond _ hp
                    simp only [Subst.apply_var] at hc
                    exact cconv_of_relConv_level m hc
                  obtain ⟨w, hxw, hyw⟩ := relJoinable_of_relConv hconf hconvxy
                  have hxstop : ∀ u, ¬ CStep C (sb x) u :=
                    ih (sb x) (by omega) hxnf
                  have hystop : ∀ u, ¬ CStep C (sb y) u :=
                    ih (sb y) (by omega) hynf
                  rcases hxw.cases_head with hxe | ⟨c, hc, -⟩
                  · rcases hyw.cases_head with hye | ⟨d, hd, -⟩
                    · exact hne (hxe.trans hye.symm)
                    · exact hystop d hd
                  · exact hxstop c hc
              · -- argument case: the step is inside a strictly smaller normal form
                have hmem : a ∈ args := by rw [hargs]; exact List.mem_append_right _ (List.Mem.head _)
                have hanf : NormalForm R a := by
                  refine hnf.subterm (Subterm.arg hmem (Subterm.refl _))
                have halt : a.size < (Term.app f args).size := Term.size_lt_of_mem hmem
                exact ih a (by omega) hanf b (CStep.of_level (n := m + 1) hab)

/-! ## The transfer theorem -/

/-- **Transfer.** If a conditional linearization of `R` is confluent, then `R`
has unique normal forms with respect to conversion.

The theorem concerns the substitution and context closure of the first-order
rewrite relation, with the linearization related to `R` by `IsLinearization`;
the nearest overreading it avoids is a converse, since a system can have unique
normal forms while its linearization loses confluence. -/
theorem UNconv_of_cconfluent_linearization {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) (hconf : cconfluent C) : UNconv R := by
  intro t u htnf hunf hconv
  obtain ⟨w, htw, huw⟩ :=
    relJoinable_of_relConv hconf (cconv_of_conv hlin hconv)
  have htstop : ∀ s, ¬ CStep C t s := nf_no_cstep hlin hconf t.size t (Nat.le_refl _) htnf
  have hustop : ∀ s, ¬ CStep C u s := nf_no_cstep hlin hconf u.size u (Nat.le_refl _) hunf
  rcases htw.cases_head with hte | ⟨c, hc, -⟩
  · rcases huw.cases_head with hue | ⟨d, hd, -⟩
    · exact hte.trans hue.symm
    · exact absurd hd (hustop d)
  · exact absurd hc (htstop c)

/-- The same hypotheses give UN->. -/
theorem UNred_of_cconfluent_linearization {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) (hconf : cconfluent C) : UNred R :=
  UNred_of_UNconv (UNconv_of_cconfluent_linearization hlin hconf)

/-! ## The two negative controls

Contraposing the transfer theorem on two systems already proved to fail UN=
shows their conditional linearizations fail confluence. Both are theorems about
systems with a classical pedigree: Huet's is the standard witness that a
non-overlapping system can lose unique normal forms, and the KO7 kernel is this
program's own diagonal fork. -/

namespace Controls

/-- The conditional linearization of Huet's system: the diagonal rule
`F(x, x) -> A` becomes `F(x, y) -> A` under `x ~ y`, the second rule
`F(x, G(x)) -> B` becomes `F(x, G(z)) -> B` under `x ~ z`, and `C -> G(C)` is
already linear. Fresh variables `5` and `9` miss every original rule. -/
def linHuet : CTRS Nat Nat :=
  [ ⟨.app 1 [.var 0, .var 9], .app 3 [], [(.var 0, .var 9)], rfl⟩,
    ⟨.app 1 [.var 0, .app 2 [.var 5]], .app 4 [], [(.var 0, .var 5)], rfl⟩,
    ⟨.app 5 [], .app 2 [.app 5 []], [], rfl⟩ ]

theorem isLin_huet : IsLinearization HuetSystem.trs linHuet := by
  constructor
  · intro crule hc
    simp only [linHuet, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨HuetSystem.ruleAA, List.Mem.head _,
        linearizesRule_binaryDiagonal 1 0 9 (.app 3 []) (fun h => by rcases h.app_inv with ⟨a, ha, -⟩; simp at ha)⟩
    · refine ⟨HuetSystem.ruleAB, List.Mem.tail _ (List.Mem.head _), rfl,
        (fun v => if v = 5 then 0 else v), by decide, ?_, ?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp
        exact ⟨0, 5, rfl, by decide, by decide,
          VarOccurs.arg (List.Mem.head _) VarOccurs.here,
          VarOccurs.arg (List.Mem.tail _ (List.Mem.head _))
            (VarOccurs.arg (List.Mem.head _) VarOccurs.here)⟩
      · intro v hv
        rcases hv.app_inv with ⟨a, ha, hva⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · cases hva; left; decide
        · rcases hva.app_inv with ⟨c, hc2, hvc⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc2
          subst hc2
          cases hvc
          right
          simp
      · intro v hv; rcases hv.app_inv with ⟨a, ha, -⟩; simp at ha
    · exact ⟨HuetSystem.ruleC, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
        linearizesRule_self HuetSystem.ruleC⟩
  · intro rule hr
    simp only [HuetSystem.trs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.Mem.head _,
        linearizesRule_binaryDiagonal 1 0 9 (.app 3 []) (fun h => by rcases h.app_inv with ⟨a, ha, -⟩; simp at ha)⟩
    · refine ⟨_, List.Mem.tail _ (List.Mem.head _), rfl,
        (fun v => if v = 5 then 0 else v), by decide, ?_, ?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp
        exact ⟨0, 5, rfl, by decide, by decide,
          VarOccurs.arg (List.Mem.head _) VarOccurs.here,
          VarOccurs.arg (List.Mem.tail _ (List.Mem.head _))
            (VarOccurs.arg (List.Mem.head _) VarOccurs.here)⟩
      · intro v hv
        rcases hv.app_inv with ⟨a, ha, hva⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · cases hva; left; decide
        · rcases hva.app_inv with ⟨c, hc2, hvc⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc2
          subst hc2
          cases hvc
          right
          simp
      · intro v hv; rcases hv.app_inv with ⟨a, ha, -⟩; simp at ha
    · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
        linearizesRule_self HuetSystem.ruleC⟩

/-- **The conditional linearization of Huet's system fails confluence.** -/
theorem linHuet_not_cconfluent : ¬ cconfluent linHuet :=
  fun h => HuetSystem.not_UNconv
    (UNconv_of_cconfluent_linearization isLin_huet h)

/-- The conditional linearization of the KO7 kernel. Six of the eight rules are
already left-linear and pass through unchanged. The two diagonal rules split:
`merge(x, x) -> x` becomes `merge(x, y) -> x` under `x ~ y`, and
`eqW(x, x) -> void` becomes `eqW(x, y) -> void` under `x ~ y`. The fresh
variable `9` misses every original rule. -/
def linKO7 : CTRS Nat Nat :=
  [ ⟨.app 2 [.app 1 [.var 0]], .app 0 [], [], rfl⟩,
    ⟨.app 3 [.app 0 [], .var 0], .var 0, [], rfl⟩,
    ⟨.app 3 [.var 0, .app 0 []], .var 0, [], rfl⟩,
    ⟨.app 3 [.var 0, .var 9], .var 0, [(.var 0, .var 9)], rfl⟩,
    ⟨.app 5 [.var 0, .var 1, .app 0 []], .var 0, [], rfl⟩,
    ⟨.app 5 [.var 0, .var 1, .app 1 [.var 2]],
      .app 4 [.var 1, .app 5 [.var 0, .var 1, .var 2]], [], rfl⟩,
    ⟨.app 6 [.var 0, .var 9], .app 0 [], [(.var 0, .var 9)], rfl⟩,
    ⟨.app 6 [.var 0, .var 1], .app 2 [.app 3 [.var 0, .var 1]], [], rfl⟩ ]

/-- The fresh variable `9` misses the two diagonal right-hand sides. -/
theorem nine_not_in_var_zero : ¬ VarOccurs (sigma := Nat) 9 (.var 0) := by
  intro h; cases h

theorem nine_not_in_void : ¬ VarOccurs (sigma := Nat) 9 (.app 0 []) := by
  intro h; rcases h.app_inv with ⟨a, ha, -⟩; simp at ha

theorem isLin_ko7 : IsLinearization KO7Fence.ko7TRS linKO7 := by
  have hmerge : LinearizesRule KO7Fence.rMergeCancel
      ⟨.app 3 [.var 0, .var 9], .var 0, [(.var 0, .var 9)], rfl⟩ :=
    linearizesRule_binaryDiagonal 3 0 9 (.var 0) nine_not_in_var_zero
  have heq : LinearizesRule KO7Fence.rEqRefl
      ⟨.app 6 [.var 0, .var 9], .app 0 [], [(.var 0, .var 9)], rfl⟩ :=
    linearizesRule_binaryDiagonal 6 0 9 (.app 0 []) nine_not_in_void
  constructor
  · intro crule hc
    simp only [linKO7, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨KO7Fence.rIntDelta, by simp [KO7Fence.ko7TRS],
        linearizesRule_self KO7Fence.rIntDelta⟩
    · exact ⟨KO7Fence.rMergeVL, by simp [KO7Fence.ko7TRS],
        linearizesRule_self KO7Fence.rMergeVL⟩
    · exact ⟨KO7Fence.rMergeVR, by simp [KO7Fence.ko7TRS],
        linearizesRule_self KO7Fence.rMergeVR⟩
    · exact ⟨KO7Fence.rMergeCancel, by simp [KO7Fence.ko7TRS], hmerge⟩
    · exact ⟨KO7Fence.rRecZero, by simp [KO7Fence.ko7TRS],
        linearizesRule_self KO7Fence.rRecZero⟩
    · exact ⟨KO7Fence.rRecSucc, by simp [KO7Fence.ko7TRS],
        linearizesRule_self KO7Fence.rRecSucc⟩
    · exact ⟨KO7Fence.rEqRefl, by simp [KO7Fence.ko7TRS], heq⟩
    · exact ⟨KO7Fence.rEqDiff, by simp [KO7Fence.ko7TRS],
        linearizesRule_self KO7Fence.rEqDiff⟩
  · intro rule hr
    rcases KO7Fence.mem_ko7TRS hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.Mem.head _, linearizesRule_self KO7Fence.rIntDelta⟩
    · exact ⟨_, List.Mem.tail _ (List.Mem.head _), linearizesRule_self KO7Fence.rMergeVL⟩
    · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), linearizesRule_self KO7Fence.rMergeVR⟩
    · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))), hmerge⟩
    · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))), linearizesRule_self KO7Fence.rRecZero⟩
    · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))), linearizesRule_self KO7Fence.rRecSucc⟩
    · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))), heq⟩
    · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))), linearizesRule_self KO7Fence.rEqDiff⟩

/-- **The conditional linearization of the KO7 kernel fails confluence.** The
diagonal fork of the Distinction Boundary survives linearization: moving the
equality test into a condition relocates the obstruction without removing it. -/
theorem linKO7_not_cconfluent : ¬ cconfluent linKO7 :=
  fun h => KO7Fence.not_UNconv
    (UNconv_of_cconfluent_linearization isLin_ko7 h)

end Controls

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_cconfluent_linearization
#check @OperatorKO7.Meta.UniqueNormalization.UNred_of_cconfluent_linearization
#check @OperatorKO7.Meta.UniqueNormalization.cconv_iff_conv

#print axioms OperatorKO7.Meta.UniqueNormalization.cconv_of_relConv_level
#print axioms OperatorKO7.Meta.UniqueNormalization.conv.args
#print axioms OperatorKO7.Meta.UniqueNormalization.conv_apply_pointwise
#print axioms OperatorKO7.Meta.UniqueNormalization.NormalForm.subterm
#print axioms OperatorKO7.Meta.UniqueNormalization.cstepLevel_one_of_rootStep
#print axioms OperatorKO7.Meta.UniqueNormalization.cstep_of_step
#print axioms OperatorKO7.Meta.UniqueNormalization.conv_of_cstepLevel
#print axioms OperatorKO7.Meta.UniqueNormalization.cconv_iff_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.nf_no_cstep
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_cconfluent_linearization
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_cconfluent_linearization
#print axioms OperatorKO7.Meta.UniqueNormalization.Controls.isLin_huet
#print axioms OperatorKO7.Meta.UniqueNormalization.Controls.linHuet_not_cconfluent
#print axioms OperatorKO7.Meta.UniqueNormalization.Controls.isLin_ko7
#print axioms OperatorKO7.Meta.UniqueNormalization.Controls.linKO7_not_cconfluent
