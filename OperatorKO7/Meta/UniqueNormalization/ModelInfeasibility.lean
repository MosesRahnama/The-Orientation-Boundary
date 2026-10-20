import OperatorKO7.Meta.UniqueNormalization.SemiEquationalConfluence

/-!
# Model certificates for infeasible overlaps

Campaign: RTA open problem 79, route R2, execution step 4 of the 2026-09-12
roadmap in `Audit/worktree-lean-publication-audit/klop-status-assessment.md`.

An interpretation of the signature in a carrier, under which every rule of `R`
holds as an identity, gives convertible terms the same value
(`SymbolInterp.eval_eq_of_conv`). If in such a model the two condition sets of
every non-trivial overlap of a linearization never hold together, the
linearization has no overlap whose conditions are convertible
(`noFeasibleOverlap_of_model`), and the original system has unique normal forms
with respect to conversion (`UNconv_of_model`, `UNconv_of_linHub_model`).

Instance (`F45Certificate`): `F(x, x, x) -> x` beside
`F(G(y, A), G(B, A), y) -> y`, ledger row F45. Its linearization overlaps at the
root, so the strongly non-overlapping criterion does not apply
(`F45Certificate.lin_not_nonOverlapping`). The two-element model
`F(a, b, c) = c`, `G(a, b) = not a`, `A = B = false` satisfies both rules, and
the overlap's conditions force `t = not t` for the value `t` of the shared
argument. The exhaustive search `klop-l2-lab.py` (ledger row F75) finds no
single-use syntactic refutation of this overlap in the design of Toyama and
Oyamaguchi; the model refutes it directly. That the system is
non-omega-overlapping is proved in `CertificateFamilyInstances.lean`
(`CertificateFamily.f45_nonOmegaOverlapping`).

Completeness (`noFeasibleOverlap_iff_quotient_refutes`): the terms up to conversion
form a model of the rules, and that model refutes the overlaps of a linearization
exactly when the linearization has no feasible overlap. A certificate therefore
exists for a system exactly when route R2's hypothesis holds for it. That
hypothesis implies unique normal forms; the converse implication is unproved, and
so is any impossibility of constructing certificates for the non-omega-overlapping
class.
Controls: no model certificate exists for Huet's system or for the KO7 kernel,
whose linearizations have feasible overlaps.

Proves: unique normal forms with respect to conversion for every system with the
variable condition that has such a model, and for the F45 system; completeness of
the certificate format relative to route R2's hypothesis.
Does not prove: that every non-omega-overlapping system has such a model. A
certificate for every system of the class would prove problem 79; the completeness
theorem restates the certificate condition as route R2's hypothesis and leaves that
construction open.
Relation: `Step R`, through `CStep` of a conditional linearization.
Closure: conversion.
Strategy: full rewriting.
Trust: kernel checked; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe` or `opaque`. Axiom footprints are printed at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v w

/-! ## Interpretations and evaluation -/

/-- An interpretation of a signature in a carrier `M`: every symbol acts on the
list of its argument values. -/
structure SymbolInterp (sigma : Type u) (M : Type w) where
  /-- The action of a symbol on the values of its arguments. -/
  op : sigma → List M → M

namespace SymbolInterp

variable {sigma : Type u} {nu : Type v} {M : Type w}

mutual
/-- The value of a term under a valuation of its variables. -/
def eval (I : SymbolInterp sigma M) (ρ : nu → M) : Term sigma nu → M
  | .var x => ρ x
  | .app f args => I.op f (evalList I ρ args)
/-- The values of an argument list. -/
def evalList (I : SymbolInterp sigma M) (ρ : nu → M) : List (Term sigma nu) → List M
  | [] => []
  | a :: as => eval I ρ a :: evalList I ρ as
end

@[simp] theorem eval_var (I : SymbolInterp sigma M) (ρ : nu → M) (x : nu) :
    I.eval ρ (Term.var x : Term sigma nu) = ρ x := rfl

@[simp] theorem eval_app (I : SymbolInterp sigma M) (ρ : nu → M) (f : sigma)
    (args : List (Term sigma nu)) :
    I.eval ρ (Term.app f args) = I.op f (I.evalList ρ args) := rfl

@[simp] theorem evalList_nil (I : SymbolInterp sigma M) (ρ : nu → M) :
    I.evalList ρ ([] : List (Term sigma nu)) = [] := rfl

@[simp] theorem evalList_cons (I : SymbolInterp sigma M) (ρ : nu → M)
    (a : Term sigma nu) (as : List (Term sigma nu)) :
    I.evalList ρ (a :: as) = I.eval ρ a :: I.evalList ρ as := rfl

/-- `evalList` is the `List.map` of `eval`. -/
theorem evalList_eq_map (I : SymbolInterp sigma M) (ρ : nu → M)
    (args : List (Term sigma nu)) : I.evalList ρ args = args.map (I.eval ρ) := by
  induction args with
  | nil => rfl
  | cons a as ih => simp [ih]

/-- **Substitution lemma.** The value of an instance is the value of the pattern
under the valuation that evaluates the substitution. -/
theorem eval_apply (I : SymbolInterp sigma M) (ρ : nu → M) (s : Subst sigma nu)
    (t : Term sigma nu) :
    I.eval ρ (Subst.apply s t) = I.eval (fun x => I.eval ρ (s x)) t := by
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
      simp only [Subst.apply_app, eval_app, evalList_eq_map, Subst.applyList_eq_map,
        List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih a ha

/-- Every rule of `R` holds in the interpretation under every valuation. -/
def RulesHold (I : SymbolInterp sigma M) (R : TRS sigma nu) : Prop :=
  ∀ rule ∈ R, ∀ ρ : nu → M, I.eval ρ rule.lhs = I.eval ρ rule.rhs

/-- **Soundness for one step.** When every rule of `R` holds, a rewrite step keeps
the value of a term under every valuation.

Relation: `Step R`. Property: one step. -/
theorem eval_eq_of_step {I : SymbolInterp sigma M} {R : TRS sigma nu}
    (hR : I.RulesHold R) {s t : Term sigma nu} (h : Step R s t) (ρ : nu → M) :
    I.eval ρ s = I.eval ρ t := by
  induction h generalizing ρ with
  | root hr =>
      obtain ⟨rule, hrule, σ, rfl, rfl⟩ := hr
      rw [eval_apply, eval_apply]
      exact hR rule hrule _
  | arg f pre post _ ih =>
      simp only [eval_app, evalList_eq_map, List.map_append, List.map_cons, ih ρ]

/-- **Soundness for conversion.** When every rule of `R` holds, convertible terms
have the same value under every valuation.

Relation: `conv R`. Closure: conversion. -/
theorem eval_eq_of_conv {I : SymbolInterp sigma M} {R : TRS sigma nu}
    (hR : I.RulesHold R) {s t : Term sigma nu} (h : conv R s t) (ρ : nu → M) :
    I.eval ρ s = I.eval ρ t := by
  induction h with
  | refl => rfl
  | tail _ hlast ih =>
      rcases hlast with hstep | hstep
      · exact ih.trans (eval_eq_of_step hR hstep ρ)
      · exact ih.trans (eval_eq_of_step hR hstep ρ).symm

end SymbolInterp

variable {sigma : Type u} {nu : Type v} {M : Type w}

/-! ## The certificate -/

/-- **The model refutes every non-trivial overlap of `C`.** Whenever a
non-variable subterm of one left-hand side and a second left-hand side have a
common instance, and both condition sets hold in the model under every
valuation, the two rules coincide and the subterm is the whole left-hand side.
This is `NoFeasibleOverlap` with the conversion of `C` replaced by equality of
values in the model. -/
def ModelRefutesOverlaps (C : CTRS sigma nu) (I : SymbolInterp sigma M) : Prop :=
  ∀ r₁ ∈ C, ∀ r₂ ∈ C, ∀ q : Term sigma nu, Subterm q r₁.lhs → q.isApp = true →
    ∀ σ₁ σ₂ : Subst sigma nu, Subst.apply σ₁ q = Subst.apply σ₂ r₂.lhs →
      (∀ p ∈ r₁.conds, ∀ ρ : nu → M,
        I.eval ρ (Subst.apply σ₁ p.1) = I.eval ρ (Subst.apply σ₁ p.2)) →
      (∀ p ∈ r₂.conds, ∀ ρ : nu → M,
        I.eval ρ (Subst.apply σ₂ p.1) = I.eval ρ (Subst.apply σ₂ p.2)) →
      r₁ = r₂ ∧ q = r₁.lhs

/-- **Model certificate for infeasible overlaps.** A model of the rules of `R`
that refutes every non-trivial overlap of a linearization `C` shows that `C` has
no overlap whose conditions are convertible in `C`.

Relation: `CStep C`, with the conversion of `C` as the condition oracle.
Closure: conversion. -/
theorem noFeasibleOverlap_of_model {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) (I : SymbolInterp sigma M) (hR : I.RulesHold R)
    (hcert : ModelRefutesOverlaps C I) : NoFeasibleOverlap C (cconv C) := by
  intro r₁ h₁ r₂ h₂ q hq happ σ₁ σ₂ heq hc₁ hc₂
  exact hcert r₁ h₁ r₂ h₂ q hq happ σ₁ σ₂ heq
    (fun p hp ρ =>
      SymbolInterp.eval_eq_of_conv hR ((cconv_iff_conv hlin _ _).1 (hc₁ p hp)) ρ)
    (fun p hp ρ =>
      SymbolInterp.eval_eq_of_conv hR ((cconv_iff_conv hlin _ _).1 (hc₂ p hp)) ρ)

/-- **UN= from a model certificate.** A system with the variable condition, a
left-linear linearization, and a model of its rules that refutes every
non-trivial overlap of the linearization has unique normal forms with respect to
conversion.

Relation: `Step R`, through `CStep C`. Closure: conversion.
Strategy: full rewriting. -/
theorem UNconv_of_model {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) (hll : CLeftLinear C)
    (hvar : ∀ rule ∈ R, ∀ x, VarOccurs x rule.rhs → VarOccurs x rule.lhs)
    (I : SymbolInterp sigma M) (hR : I.RulesHold R) (hcert : ModelRefutesOverlaps C I) :
    UNconv R :=
  UNconv_of_linearization_noFeasibleOverlap hlin hll
    (cVarCondition_of_isLinearization hlin hvar) (noFeasibleOverlap_of_model hlin I hR hcert)

/-- **UN= from a model certificate for the hub linearization.** The same
statement for the canonical hub linearization `linHub R`.

Relation: `Step R`, through `CStep (linHub R)`. Closure: conversion.
Strategy: full rewriting. -/
theorem UNconv_of_linHub_model {R : TRS sigma Nat}
    (hvar : ∀ rule ∈ R, ∀ x, VarOccurs x rule.rhs → VarOccurs x rule.lhs)
    (I : SymbolInterp sigma M) (hR : I.RulesHold R)
    (hcert : ModelRefutesOverlaps (linHub R) I) : UNconv R :=
  UNconv_of_linHub_noFeasibleOverlap hvar
    (noFeasibleOverlap_of_model (isLinearization_linHub R) I hR hcert)

/-! ## Completeness: the term model -/

/-- Conversion of `R` as a setoid on terms. -/
def convSetoid (R : TRS sigma nu) : Setoid (Term sigma nu) where
  r := conv R
  iseqv := ⟨conv.refl R, conv.symm, conv.trans⟩

/-- The term model of `R`: terms up to conversion, each symbol applied to chosen
representatives of its argument classes. -/
noncomputable def quotientInterp (R : TRS sigma nu) :
    SymbolInterp sigma (Quotient (convSetoid R)) where
  op f vs := Quotient.mk (convSetoid R) (Term.app f (vs.map Quotient.out))

/-- A chosen representative of the class of `t` is convertible to `t`. -/
theorem conv_out_mk (R : TRS sigma nu) (t : Term sigma nu) :
    conv R (Quotient.mk (convSetoid R) t).out t :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (convSetoid R) t))

/-- In the term model, a term evaluates to the class of its instance under chosen
representatives of the valuation. -/
theorem quotientInterp_eval (R : TRS sigma nu) (ρ : nu → Quotient (convSetoid R))
    (t : Term sigma nu) :
    (quotientInterp R).eval ρ t =
      Quotient.mk (convSetoid R) (Subst.apply (fun x => (ρ x).out) t) := by
  induction t using Term.rec' with
  | hvar x => exact (Quotient.out_eq (ρ x)).symm
  | happ f args ih =>
      rw [SymbolInterp.eval_app, SymbolInterp.evalList_eq_map, Subst.apply_app,
        Subst.applyList_eq_map]
      apply Quotient.sound
      rw [List.map_map]
      apply conv.args
      apply forall₂_map_map
      intro a ha
      show conv R ((quotientInterp R).eval ρ a).out (Subst.apply (fun x => (ρ x).out) a)
      rw [ih a ha]
      exact conv_out_mk R _

/-- Every rule of `R` holds in its term model. -/
theorem quotientInterp_rulesHold (R : TRS sigma nu) : (quotientInterp R).RulesHold R := by
  intro rule hr ρ
  rw [quotientInterp_eval, quotientInterp_eval]
  exact Quotient.sound (conv.of_step (Step.root ⟨rule, hr, _, rfl, rfl⟩))

/-- Under the valuation sending each variable to its own class, a term evaluates to
its own class. -/
theorem quotientInterp_eval_canonical (R : TRS sigma nu) (t : Term sigma nu) :
    (quotientInterp R).eval (fun x => Quotient.mk (convSetoid R) (Term.var x)) t =
      Quotient.mk (convSetoid R) t := by
  rw [quotientInterp_eval]
  apply Quotient.sound
  have h := conv_apply_pointwise (R := R)
    (s := fun x => (Quotient.mk (convSetoid R) (Term.var x)).out) (s' := Subst.id) t
    (fun x _ => conv_out_mk R (Term.var x))
  rw [Subst.id_apply] at h
  exact h

/-- **The certificate format is complete.** A linearization has no overlap whose
conditions are convertible exactly when the term model of `R` refutes its overlaps.
So a model certificate exists for a system exactly when route R2's hypothesis holds
for it.

Relation: `CStep C`, with the conversion of `C` as the condition oracle. -/
theorem noFeasibleOverlap_iff_quotient_refutes {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) :
    NoFeasibleOverlap C (cconv C) ↔ ModelRefutesOverlaps C (quotientInterp R) := by
  constructor
  · intro hno r₁ h₁ r₂ h₂ q hq happ σ₁ σ₂ heq hc₁ hc₂
    refine hno r₁ h₁ r₂ h₂ q hq happ σ₁ σ₂ heq (fun p hp => ?_) (fun p hp => ?_)
    · have h := hc₁ p hp (fun x => Quotient.mk (convSetoid R) (Term.var x))
      rw [quotientInterp_eval_canonical, quotientInterp_eval_canonical] at h
      exact (cconv_iff_conv hlin _ _).2 (Quotient.exact h)
    · have h := hc₂ p hp (fun x => Quotient.mk (convSetoid R) (Term.var x))
      rw [quotientInterp_eval_canonical, quotientInterp_eval_canonical] at h
      exact (cconv_iff_conv hlin _ _).2 (Quotient.exact h)
  · intro h
    exact noFeasibleOverlap_of_model hlin (quotientInterp R) (quotientInterp_rulesHold R) h

/-! ## Controls: no certificate where the hypothesis fails -/

namespace Controls

/-- **No model certificate exists for Huet's system.** Every model of its rules
fails to refute the overlaps of its linearization, which has a feasible overlap. -/
theorem huet_no_model_certificate {M : Type w} (I : SymbolInterp Nat M)
    (hR : I.RulesHold HuetSystem.trs) : ¬ ModelRefutesOverlaps linHuet I :=
  fun h => linHuet_feasibleOverlap (noFeasibleOverlap_of_model isLin_huet I hR h)

/-- **No model certificate exists for the KO7 kernel.** Every model of its rules
fails to refute the overlaps of its linearization, which has a feasible overlap. -/
theorem ko7_no_model_certificate {M : Type w} (I : SymbolInterp Nat M)
    (hR : I.RulesHold KO7Fence.ko7TRS) : ¬ ModelRefutesOverlaps linKO7 I :=
  fun h => linKO7_feasibleOverlap (noFeasibleOverlap_of_model isLin_ko7 I hR h)

end Controls

/-! ## Instance: the F45 system -/

namespace F45Certificate

/-- `F(x, x, x) -> x` beside `F(G(y, A), G(B, A), y) -> y`, with `F = 1`, `G = 2`,
`A = 3`, `B = 4`, and the variable of each rule written `0`. -/
def trs : TRS Nat Nat :=
  [ ⟨.app 1 [.var 0, .var 0, .var 0], .var 0, rfl⟩,
    ⟨.app 1 [.app 2 [.var 0, .app 3 []], .app 2 [.app 4 [], .app 3 []], .var 0], .var 0,
      rfl⟩ ]

/-- Its linearization: `F(x, y, z) -> x` under `x ~ y` and `x ~ z`, with `y = 8` and
`z = 9`, and `F(G(x, A), G(B, A), z) -> x` under `x ~ z`. -/
def lin : CTRS Nat Nat :=
  [ ⟨.app 1 [.var 0, .var 8, .var 9], .var 0, [(.var 0, .var 8), (.var 0, .var 9)], rfl⟩,
    ⟨.app 1 [.app 2 [.var 0, .app 3 []], .app 2 [.app 4 [], .app 3 []], .var 9], .var 0,
      [(.var 0, .var 9)], rfl⟩ ]

/-- The collapse of the fresh variables `8` and `9`, and every larger one, onto `0`. -/
def collapse (v : Nat) : Nat := if 8 ≤ v then 0 else v

/-- The first conditional rule linearizes `F(x, x, x) -> x`. -/
theorem linearizes_first : LinearizesRule
    (⟨.app 1 [.var 0, .var 0, .var 0], .var 0, rfl⟩ : Rule Nat Nat)
    ⟨.app 1 [.var 0, .var 8, .var 9], .var 0, [(.var 0, .var 8), (.var 0, .var 9)], rfl⟩ := by
  refine ⟨rfl, collapse, rfl, ?_, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨0, 8, rfl, rfl, rfl, VarOccurs.arg (by simp) VarOccurs.here,
        VarOccurs.arg (by simp) VarOccurs.here⟩
    · exact ⟨0, 9, rfl, rfl, rfl, VarOccurs.arg (by simp) VarOccurs.here,
        VarOccurs.arg (by simp) VarOccurs.here⟩
  · intro v hv
    change VarOccurs v (Term.app 1 [.var 0, .var 8, .var 9]) at hv
    rcases hv.app_inv with ⟨a, ha, hva⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> cases hva
    · exact Or.inl rfl
    · exact Or.inr (by simp [collapse])
    · exact Or.inr (by simp [collapse])
  · intro v hv
    change VarOccurs v (Term.var 0) at hv
    cases hv
    rfl

/-- The second conditional rule linearizes `F(G(y, A), G(B, A), y) -> y`. -/
theorem linearizes_second : LinearizesRule
    (⟨.app 1 [.app 2 [.var 0, .app 3 []], .app 2 [.app 4 [], .app 3 []], .var 0], .var 0,
      rfl⟩ : Rule Nat Nat)
    ⟨.app 1 [.app 2 [.var 0, .app 3 []], .app 2 [.app 4 [], .app 3 []], .var 9], .var 0,
      [(.var 0, .var 9)], rfl⟩ := by
  refine ⟨rfl, collapse, rfl, ?_, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact ⟨0, 9, rfl, rfl, rfl,
      VarOccurs.arg (List.Mem.head _) (VarOccurs.arg (List.Mem.head _) VarOccurs.here),
      VarOccurs.arg (by simp) VarOccurs.here⟩
  · intro v hv
    change VarOccurs v (Term.app 1 [.app 2 [.var 0, .app 3 []], .app 2 [.app 4 [], .app 3 []],
      .var 9]) at hv
    rcases hv.app_inv with ⟨a, ha, hva⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · rcases hva.app_inv with ⟨b, hb, hvb⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · cases hvb
        exact Or.inl rfl
      · rcases hvb.app_inv with ⟨c, hc, -⟩
        simp at hc
    · rcases hva.app_inv with ⟨b, hb, hvb⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;>
        (rcases hvb.app_inv with ⟨c, hc, -⟩; simp at hc)
    · cases hva
      exact Or.inr (by simp [collapse])
  · intro v hv
    change VarOccurs v (Term.var 0) at hv
    cases hv
    rfl

/-- `lin` is a conditional linearization of `trs`. -/
theorem isLin : IsLinearization trs lin := by
  constructor
  · intro crule hc
    simp only [lin, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_, List.Mem.head _, linearizes_first⟩
    · exact ⟨_, List.Mem.tail _ (List.Mem.head _), linearizes_second⟩
  · intro rule hr
    simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.Mem.head _, linearizes_first⟩
    · exact ⟨_, List.Mem.tail _ (List.Mem.head _), linearizes_second⟩

/-- The left-hand sides of `lin` are left-linear. -/
theorem lin_leftLinear : CLeftLinear lin := by
  intro crule hc
  simp only [lin, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;>
    simp [OperatorKO7.Meta.UniqueNormalization.Term.LeftLinear,
      OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences, List.nodup_cons]

/-- `trs` satisfies the variable condition. -/
theorem trs_varCondition :
    ∀ rule ∈ trs, ∀ x, VarOccurs x rule.rhs → VarOccurs x rule.lhs := by
  intro rule hr x hx
  simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · change VarOccurs x (Term.var 0) at hx
    cases hx
    exact VarOccurs.arg (List.Mem.head _) VarOccurs.here
  · change VarOccurs x (Term.var 0) at hx
    cases hx
    exact VarOccurs.arg (List.Mem.head _) (VarOccurs.arg (List.Mem.head _) VarOccurs.here)

/-- **The overlap exists.** `lin` is not syntactically non-overlapping: the two
left-hand sides have a common instance at the root, so the strongly
non-overlapping criterion does not apply to this system. -/
theorem lin_not_nonOverlapping : ¬ CNonOverlapping lin := by
  intro h
  have hbad := h
    ⟨.app 1 [.var 0, .var 8, .var 9], .var 0, [(.var 0, .var 8), (.var 0, .var 9)], rfl⟩
    (List.Mem.head _)
    ⟨.app 1 [.app 2 [.var 0, .app 3 []], .app 2 [.app 4 [], .app 3 []], .var 9], .var 0,
      [(.var 0, .var 9)], rfl⟩
    (List.Mem.tail _ (List.Mem.head _))
    (.app 1 [.var 0, .var 8, .var 9]) (Subterm.refl _) rfl
    (fun v => if v = 0 then .app 2 [.var 0, .app 3 []]
      else if v = 8 then .app 2 [.app 4 [], .app 3 []] else .var 0)
    (fun _ => .var 0) (by simp)
  simp at hbad

/-- The two-element model: `F(a, b, c) = c`, `G(a, b) = not a`, and `false` for
every other symbol and arity, so `A = B = false`. -/
def model : SymbolInterp Nat Bool where
  op := fun f args =>
    match f, args with
    | 1, [_, _, c] => c
    | 2, [a, _] => !a
    | _, _ => false

/-- `F` returns its third argument. -/
theorem model_op_F (a b c : Bool) : model.op 1 [a, b, c] = c := rfl

/-- `G` negates its first argument. -/
theorem model_op_G (a b : Bool) : model.op 2 [a, b] = !a := rfl

/-- Both rules of `trs` hold in the model. -/
theorem model_rulesHold : model.RulesHold trs := by
  intro rule hr ρ
  simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;>
    simp only [SymbolInterp.eval_app, SymbolInterp.evalList_cons, SymbolInterp.evalList_nil,
      SymbolInterp.eval_var, model_op_F]

/-- The application subterms of the second left-hand side of `lin`: the whole
left-hand side, or an application headed by `G`, `A` or `B`. -/
theorem lhs2_subterm_cases {q : Term Nat Nat}
    (hq : Subterm q
      (.app 1 [.app 2 [.var 0, .app 3 []], .app 2 [.app 4 [], .app 3 []], .var 9]))
    (happ : q.isApp = true) :
    q = .app 1 [.app 2 [.var 0, .app 3 []], .app 2 [.app 4 [], .app 3 []], .var 9] ∨
      ∃ (g : Nat) (args : List (Term Nat Nat)), q = Term.app g args ∧ g ≠ 1 := by
  cases hq with
  | refl => exact Or.inl rfl
  | arg ha hsa =>
      right
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · cases hsa with
        | refl => exact ⟨2, _, rfl, by decide⟩
        | arg hb hsb =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
            rcases hb with rfl | rfl
            · rw [hsb.eq_of_var] at happ
              simp at happ
            · cases hsb with
              | refl => exact ⟨3, _, rfl, by decide⟩
              | arg hc _ => simp at hc
      · cases hsa with
        | refl => exact ⟨2, _, rfl, by decide⟩
        | arg hb hsb =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
            rcases hb with rfl | rfl
            · cases hsb with
              | refl => exact ⟨4, _, rfl, by decide⟩
              | arg hc _ => simp at hc
            · cases hsb with
              | refl => exact ⟨3, _, rfl, by decide⟩
              | arg hc _ => simp at hc
      · rw [hsa.eq_of_var] at happ
        simp at happ

/-- **The model refutes the overlap.** At the only non-trivial overlap, the root
overlap of the two rules, the conditions `x ~ z` of both rules give the shared
argument `t` the value equation `not t = t`, which has no solution in `Bool`. -/
theorem model_refutes : ModelRefutesOverlaps lin model := by
  intro r₁ h₁ r₂ h₂ q hq happ σ₁ σ₂ heq hc₁ hc₂
  simp only [lin, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl
  · -- the first rule, whose left-hand side is flat
    have hq' := ClassExamples.flat_app_subterm_eq (by simp) hq happ
    subst hq'
    rcases h₂ with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exfalso
      simp only [Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil, Subst.apply_var,
        Term.app.injEq, List.cons.injEq, true_and, and_true] at heq
      have h1 := hc₁ (.var 0, .var 9) (by simp) (fun _ => false)
      have h2 := hc₂ (.var 0, .var 9) (by simp) (fun _ => false)
      dsimp only [Subst.apply_var] at h1 h2
      rw [heq.1, heq.2.2, ← h2] at h1
      simp only [SymbolInterp.eval_app, SymbolInterp.evalList_cons,
        SymbolInterp.evalList_nil, model_op_G] at h1
      revert h1
      generalize model.eval (fun _ => false) (σ₂ 0) = e
      cases e <;> decide
  · -- the second rule
    rcases lhs2_subterm_cases hq happ with rfl | ⟨g, args, rfl, hg⟩
    · rcases h₂ with rfl | rfl
      · exfalso
        simp only [Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil, Subst.apply_var,
          Term.app.injEq, List.cons.injEq, true_and, and_true] at heq
        have h1 := hc₁ (.var 0, .var 9) (by simp) (fun _ => false)
        have h2 := hc₂ (.var 0, .var 9) (by simp) (fun _ => false)
        dsimp only [Subst.apply_var] at h1 h2
        rw [← heq.1, ← heq.2.2, ← h1] at h2
        simp only [SymbolInterp.eval_app, SymbolInterp.evalList_cons,
          SymbolInterp.evalList_nil, model_op_G] at h2
        revert h2
        generalize model.eval (fun _ => false) (σ₁ 0) = e
        cases e <;> decide
      · exact ⟨rfl, rfl⟩
    · -- a proper application subterm, headed by `G`, `A` or `B`, never an instance
      -- of a left-hand side headed by `F`
      exfalso
      rcases h₂ with rfl | rfl <;>
        simp only [Subst.apply_app, Term.app.injEq] at heq <;> exact hg heq.1

/-- **The F45 system has unique normal forms with respect to conversion.** Its
linearization overlaps, and the two-element model refutes the overlap.

Relation: `Step trs`. Closure: conversion. Strategy: full rewriting. -/
theorem UNconv_trs : UNconv trs :=
  UNconv_of_model isLin lin_leftLinear trs_varCondition model model_rulesHold model_refutes

end F45Certificate

end OperatorKO7.Meta.UniqueNormalization

/-! ## Axiom audit -/

#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp.eval_apply
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp.eval_eq_of_step
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolInterp.eval_eq_of_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.noFeasibleOverlap_of_model
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_model
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_linHub_model
#print axioms OperatorKO7.Meta.UniqueNormalization.quotientInterp_eval
#print axioms OperatorKO7.Meta.UniqueNormalization.quotientInterp_rulesHold
#print axioms OperatorKO7.Meta.UniqueNormalization.noFeasibleOverlap_iff_quotient_refutes
#print axioms OperatorKO7.Meta.UniqueNormalization.Controls.huet_no_model_certificate
#print axioms OperatorKO7.Meta.UniqueNormalization.Controls.ko7_no_model_certificate
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.lin_not_nonOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.model_refutes
#print axioms OperatorKO7.Meta.UniqueNormalization.F45Certificate.UNconv_trs
