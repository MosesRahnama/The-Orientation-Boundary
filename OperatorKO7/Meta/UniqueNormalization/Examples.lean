import OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation

/-!
# The example battery of RTA open problem #79

Campaign: `Roadmaps\klop\ROADMAP.md`, WP-K1.
Definition freeze: `Roadmaps\klop\definitions.md` (D6, D15).

## Huet's system, the paper's Example 1

> "By Huet: { F(x, x) -> A, F(x, G(x)) -> B, C -> G(C) }. The term F(C, C)
> possesses two distinct normal forms, A and B. However, in a certain sense the
> first two rules overlap semantically: the infinite term G(G(...)) provides
> such an overlap, and in the world of infinitary rewriting the term C even
> rewrites to that term in the limit."

This is the system that made RTA open problem #79 a question rather than a
corollary. Everything the paper says about it is proved here:

* `lhs_not_unifiable` (in `RationalUnification.lean`): the first two left-hand
  sides do not unify, so the system is non-overlapping in the finite sense;
* `lhs_omegaUnifiable` (same file): they do omega-unify, so the system is
  omega-overlapping and outside the hypothesis of Theorem 69;
* `not_UNconv` below: UN= genuinely fails, with `A` and `B` the two distinct
  normal forms of `F(C, C)`.

Together these show that ordinary finite non-overlap is insufficient: Huet's
system is non-unifiable at the two critical left-hand sides, but the same pair
has an explicit potentially infinite-term unifier and UN= fails. Thus the
omega-overlap hypothesis excludes a counterexample that finite non-overlap does
not. No converse and no characterization is claimed.

## Klop's system, the paper's Example 3

> "{ A -> C(A), C(x) -> D(x, C(x)), D(x, x) -> E }. In this system we have
> A ->*_R E and A ->*_R C(E), but C(E) and E have no common reduct."

Both reduction sequences are proved below, and so is the non-joinability the
paper asserts. The invariant is that every reduct of `C(E)` is either `C(E)` or
`D(E, v)` for a reduct `v` of `C(E)`: the duplicating rule `D(x, x) -> E` never
fires there, because its two arguments are `E` and a term whose root is `C` or
`D`. `E` is therefore unreachable from `C(E)`, and Klop's system fails
confluence.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

/-! ## Huet's system -/

namespace HuetSystem

/-- `F(x, x)`, `F` the symbol `1`. -/
def ruleAA : Rule Nat Nat where
  lhs := .app 1 [.var 0, .var 0]
  rhs := .app 3 []
  lhs_isApp := rfl

/-- `F(x, G(x)) -> B`, `G` the symbol `2`. -/
def ruleAB : Rule Nat Nat where
  lhs := .app 1 [.var 0, .app 2 [.var 0]]
  rhs := .app 4 []
  lhs_isApp := rfl

/-- `C -> G(C)`, `C` the symbol `5`. -/
def ruleC : Rule Nat Nat where
  lhs := .app 5 []
  rhs := .app 2 [.app 5 []]
  lhs_isApp := rfl

/-- Huet's three-rule system. -/
def trs : TRS Nat Nat := [ruleAA, ruleAB, ruleC]

/-- The constant `A`. -/
def tA : Term Nat Nat := .app 3 []
/-- The constant `B`. -/
def tB : Term Nat Nat := .app 4 []
/-- The constant `C`. -/
def tC : Term Nat Nat := .app 5 []
/-- The term `G(C)`. -/
def tGC : Term Nat Nat := .app 2 [.app 5 []]
/-- The peak term `F(C, C)`. -/
def tFCC : Term Nat Nat := .app 1 [.app 5 [], .app 5 []]
/-- The term `F(C, G(C))`. -/
def tFCGC : Term Nat Nat := .app 1 [.app 5 [], .app 2 [.app 5 []]]

/-- The substitution sending the single rule variable to `C`. -/
def subC : Subst Nat Nat := fun _ => .app 5 []

/-- `F(C, C) -> A`, contracting the first rule at the root. -/
theorem step_FCC_A : Step trs tFCC tA :=
  Step.root ⟨ruleAA, List.Mem.head _, subC, rfl, rfl⟩

/-- `C -> G(C)`, contracting the third rule at the root. -/
theorem step_C_GC : Step trs tC tGC :=
  Step.root ⟨ruleC, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), subC, rfl, rfl⟩

/-- `F(C, C) -> F(C, G(C))`, rewriting the second argument. -/
theorem step_FCC_FCGC : Step trs tFCC tFCGC :=
  Step.arg 1 [.app 5 []] [] step_C_GC

/-- `F(C, G(C)) -> B`, contracting the second rule at the root. -/
theorem step_FCGC_B : Step trs tFCGC tB :=
  Step.root ⟨ruleAB, List.Mem.tail _ (List.Mem.head _), subC, rfl, rfl⟩

/-- No root contraction applies to a constant whose symbol is none of `1` or
`5`, the two root symbols among the left-hand sides. -/
theorem no_rootStep_of_head {k : Nat} (hk1 : k ≠ 1) (hk5 : k ≠ 5)
    (args : List (Term Nat Nat)) (u : Term Nat Nat) :
    ¬ rootStep trs (.app k args) u := by
  rintro ⟨rule, hmem, σ, hsrc, -⟩
  simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hhead : ∀ (g : Nat) (gs : List (Term Nat Nat)),
      Term.app k args = Subst.apply σ (.app g gs) → k = g := by
    intro g gs h
    simpa using congrArg (fun t => match t with
      | Term.app s _ => s
      | Term.var _ => 0) h
  rcases hmem with rfl | rfl | rfl
  · exact hk1 (hhead 1 _ hsrc)
  · exact hk1 (hhead 1 _ hsrc)
  · exact hk5 (hhead 5 _ hsrc)

/-- `A` is a normal form: its symbol heads no left-hand side, and it has no
argument positions. -/
theorem tA_normalForm : NormalForm trs tA := by
  intro u hstep
  rcases Step.app_inv hstep with hroot | ⟨pre, post, a, b, hargs, -, -⟩
  · exact no_rootStep_of_head (by decide) (by decide) [] u hroot
  · exact absurd hargs.symm (by simp)

/-- `B` is a normal form. -/
theorem tB_normalForm : NormalForm trs tB := by
  intro u hstep
  rcases Step.app_inv hstep with hroot | ⟨pre, post, a, b, hargs, -, -⟩
  · exact no_rootStep_of_head (by decide) (by decide) [] u hroot
  · exact absurd hargs.symm (by simp)

/-- `A` and `B` are convertible: both are reached from `F(C, C)`. -/
theorem conv_A_B : conv trs tA tB :=
  conv.trans (conv.symm (conv.of_step step_FCC_A))
    (conv.trans (conv.of_step step_FCC_FCGC) (conv.of_step step_FCGC_B))

/-- **Huet's system fails UN=.** Two distinct normal forms are convertible. -/
theorem not_UNconv : ¬ UNconv trs := by
  intro hun
  have := hun tA tB tA_normalForm tB_normalForm conv_A_B
  simp [tA, tB] at this

/-- The system also fails UN->, from the same peak. -/
theorem not_UNred : ¬ UNred trs := by
  intro hun
  have := hun tFCC tA tB tA_normalForm tB_normalForm
    (StepStar.single step_FCC_A)
    (StepStar.trans (StepStar.single step_FCC_FCGC) (StepStar.single step_FCGC_B))
  simp [tA, tB] at this

/-- The system does satisfy the variable condition: every right-hand side is a
ground term, so no fresh variable can appear. The UN= failure is therefore not
the `FreshRhs` phenomenon of `CommonGeneralisation.lean`; it is the genuine
omega-overlap phenomenon of RTA open problem #79. -/
theorem rhsDetermined : TRS.RhsDetermined trs := by
  intro rule hmem
  simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;> intro a b _ <;> rfl

/-- **Finite non-overlap is insufficient; the omega-overlap hypothesis excludes
this counterexample.** Huet's system satisfies the variable condition and fails
UN=. Its critical left-hand sides do not finitely unify, but they do omega-unify
both in the finite certificate representation and in the explicit potentially
infinite M-type semantics. -/
theorem hypothesis_required :
    TRS.RhsDetermined trs ∧ ¬ UNconv trs ∧ ¬ UNred trs ∧
      OmegaUnifiable ruleAA.lhs ruleAB.lhs ∧
      InfiniteOmegaUnifiable ruleAA.lhs ruleAB.lhs ∧
      ¬ Unifiable ruleAA.lhs ruleAB.lhs :=
  ⟨rhsDetermined, not_UNconv, not_UNred, Huet.lhs_omegaUnifiable,
    Huet.lhs_infiniteOmegaUnifiable,
    fun h => Huet.lhs_not_unifiable ⟨h.choose, h.choose_spec.choose,
      h.choose_spec.choose_spec⟩⟩

end HuetSystem

/-! ## Klop's system, the paper's Example 3 -/

namespace KlopSystem

/-- `A -> C(A)`, with `A` the symbol `0` and `C` the symbol `1`. -/
def ruleA : Rule Nat Nat where
  lhs := .app 0 []
  rhs := .app 1 [.app 0 []]
  lhs_isApp := rfl

/-- `C(x) -> D(x, C(x))`, with `D` the symbol `2`. -/
def ruleC : Rule Nat Nat where
  lhs := .app 1 [.var 0]
  rhs := .app 2 [.var 0, .app 1 [.var 0]]
  lhs_isApp := rfl

/-- `D(x, x) -> E`, with `E` the symbol `3`. -/
def ruleD : Rule Nat Nat where
  lhs := .app 2 [.var 0, .var 0]
  rhs := .app 3 []
  lhs_isApp := rfl

/-- Klop's three-rule system. -/
def trs : TRS Nat Nat := [ruleA, ruleC, ruleD]

/-- The constant `A`. -/
def tA : Term Nat Nat := .app 0 []
/-- The constant `E`. -/
def tE : Term Nat Nat := .app 3 []
/-- The term `C(A)`. -/
def tCA : Term Nat Nat := .app 1 [.app 0 []]
/-- The term `C(E)`. -/
def tCE : Term Nat Nat := .app 1 [.app 3 []]
/-- The term `D(A, C(A))`. -/
def tDACA : Term Nat Nat := .app 2 [.app 0 [], .app 1 [.app 0 []]]
/-- The term `D(C(A), C(A))`. -/
def tDCACA : Term Nat Nat := .app 2 [.app 1 [.app 0 []], .app 1 [.app 0 []]]
/-- The term `C(C(A))`. -/
def tCCA : Term Nat Nat := .app 1 [.app 1 [.app 0 []]]

/-- The substitution sending the rule variable to `A`. -/
def subA : Subst Nat Nat := fun _ => .app 0 []
/-- The substitution sending the rule variable to `C(A)`. -/
def subCA : Subst Nat Nat := fun _ => .app 1 [.app 0 []]

theorem step_A_CA : Step trs tA tCA :=
  Step.root ⟨ruleA, List.Mem.head _, subA, rfl, rfl⟩

theorem step_CA_DACA : Step trs tCA tDACA :=
  Step.root ⟨ruleC, List.Mem.tail _ (List.Mem.head _), subA, rfl, rfl⟩

theorem step_DACA_DCACA : Step trs tDACA tDCACA :=
  Step.arg 2 [] [.app 1 [.app 0 []]] step_A_CA

theorem step_DCACA_E : Step trs tDCACA tE :=
  Step.root ⟨ruleD, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), subCA, rfl, rfl⟩

/-- `A ->* E`: through `C(A)`, `D(A, C(A))`, `D(C(A), C(A))`. -/
theorem stepStar_A_E : StepStar trs tA tE :=
  StepStar.tail (StepStar.tail (StepStar.tail
    (StepStar.single step_A_CA) step_CA_DACA) step_DACA_DCACA) step_DCACA_E

/-- `C(A) ->* E`, the same sequence without its first step. -/
theorem stepStar_CA_E : StepStar trs tCA tE :=
  StepStar.tail (StepStar.tail
    (StepStar.single step_CA_DACA) step_DACA_DCACA) step_DCACA_E

/-- `A ->* C(E)`: first `A -> C(A)`, then reduce the argument `A` to `E`. -/
theorem stepStar_A_CE : StepStar trs tA tCE :=
  StepStar.trans (StepStar.single step_A_CA)
    (StepStar.arg_congr trs 1 [] [] stepStar_A_E)

/-- The paper's Example 3 reductions: `A ->* E` and `A ->* C(E)`. -/
theorem klop_both_reductions : StepStar trs tA tE ∧ StepStar trs tA tCE :=
  ⟨stepStar_A_E, stepStar_A_CE⟩

/-- `E` and `C(E)` are convertible, both being reducts of `A`. -/
theorem conv_E_CE : conv trs tE tCE :=
  conv.trans (conv.symm (conv.of_stepStar stepStar_A_E)) (conv.of_stepStar stepStar_A_CE)

/-! ### `E` is unreachable from `C(E)` -/

/-- `E` is a normal form: the three rules are rooted at `A`, `C` and `D`, and it
has no argument positions. -/
theorem tE_normalForm : NormalForm trs tE := by
  intro u hstep
  rcases Step.app_inv hstep with hroot | ⟨pre, post, a, b, hargs, -, -⟩
  · obtain ⟨rule, hmem, sb, hsrc, -⟩ := hroot
    simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> simp [ruleA, ruleC, ruleD] at hsrc
  · exact absurd hargs.symm (by simp)

/-- The reducts of `C(E)`: the term itself, and `D(E, v)` for every reduct `v`.
Closure under stepping is `FromCE.step`. -/
inductive FromCE : Term Nat Nat → Prop
  | base : FromCE tCE
  | nest {v : Term Nat Nat} : FromCE v → FromCE (.app 2 [tE, v])

/-- Every member of the reachable set is rooted at `C` or `D`, so none is `E`.
This is what stops the duplicating rule from ever firing. -/
theorem FromCE.ne_tE {w : Term Nat Nat} (h : FromCE w) : w ≠ tE := by
  cases h with
  | base => simp [tCE, tE]
  | nest _ => simp [tE]

/-- The reachable set is closed under stepping. -/
theorem FromCE.step : ∀ {w : Term Nat Nat}, FromCE w →
    ∀ {w' : Term Nat Nat}, Step trs w w' → FromCE w' := by
  intro w h
  induction h with
  | base =>
      intro w' hs
      rcases Step.app_inv hs with hroot | ⟨pre, post, a, b, hargs, htgt, hab⟩
      · obtain ⟨rule, hmem, sb, hsrc, htgt⟩ := hroot
        simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · simp [ruleA] at hsrc
        · -- the rule `C(x) -> D(x, C(x))` fires with `x := E`
          simp only [ruleC, Subst.apply_app, Subst.applyList_cons,
            Subst.applyList_nil, Subst.apply_var, Term.app.injEq, List.cons.injEq,
            and_true, true_and] at hsrc htgt
          subst htgt
          rw [← hsrc]
          exact FromCE.nest FromCE.base
        · simp [ruleD] at hsrc
      · -- the only argument of `C(E)` is `E`, a normal form
        cases pre with
        | cons c cs => simp at hargs
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at hargs
            obtain ⟨ha, -⟩ := hargs
            subst ha
            exact absurd hab (tE_normalForm b)
  | @nest v hv ih =>
      intro w' hs
      rcases Step.app_inv hs with hroot | ⟨pre, post, a, b, hargs, htgt, hab⟩
      · obtain ⟨rule, hmem, sb, hsrc, -⟩ := hroot
        simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · simp [ruleA] at hsrc
        · simp [ruleC] at hsrc
        · -- `D(x, x)` would force the two arguments equal, so `v = E`
          exfalso
          simp only [ruleD, Subst.apply_app, Subst.applyList_cons,
            Subst.applyList_nil, Subst.apply_var, Term.app.injEq, List.cons.injEq,
            and_true, true_and] at hsrc
          exact hv.ne_tE (hsrc.2.trans hsrc.1.symm)
      · -- a step inside `E` is impossible; a step inside `v` stays in the set
        cases pre with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at hargs
            obtain ⟨ha, -⟩ := hargs
            subst ha
            exact absurd hab (tE_normalForm b)
        | cons c cs =>
            cases cs with
            | cons d ds => simp at hargs
            | nil =>
                simp only [List.cons_append, List.nil_append,
                  List.cons.injEq] at hargs
                obtain ⟨hc, ha, hp⟩ := hargs
                subst hc
                subst ha
                subst hp
                subst htgt
                exact FromCE.nest (ih hab)

/-- Every reduct of `C(E)` lies in the reachable set. -/
theorem fromCE_of_stepStar {w : Term Nat Nat} (h : StepStar trs tCE w) : FromCE w := by
  induction h with
  | refl => exact FromCE.base
  | tail _ hlast ih => exact ih.step hlast

/-- `E` is unreachable from `C(E)`. -/
theorem not_stepStar_tCE_tE : ¬ StepStar trs tCE tE :=
  fun h => (fromCE_of_stepStar h).ne_tE rfl

/-- **The paper's Example 3 claim: `C(E)` and `E` have no common reduct.** -/
theorem not_joinable_tE_tCE : ¬ joinable trs tE tCE := by
  rintro ⟨w, hEw, hCEw⟩
  have hw : w = tE := (tE_normalForm.eq_of_stepStar hEw).symm
  subst hw
  exact not_stepStar_tCE_tE hCEw

/-- **Klop's system fails confluence**, from the peak `E <-* A ->* C(E)`. -/
theorem not_confluent : ¬ confluent trs := fun hc =>
  not_joinable_tE_tCE (hc tA tE tCE stepStar_A_E stepStar_A_CE)

/-- Example 3 in full: the two reduction sequences, and the failure of
confluence they witness. -/
theorem klop_example_three :
    StepStar trs tA tE ∧ StepStar trs tA tCE ∧
      ¬ joinable trs tE tCE ∧ ¬ confluent trs :=
  ⟨stepStar_A_E, stepStar_A_CE, not_joinable_tE_tCE, not_confluent⟩

end KlopSystem

/-! ## Whole-system class certificates -/

namespace ClassExamples

universe u v
variable {σ : Type u} {ν : Type v}

theorem omega_head_eq {f g : σ} {xs ys : List (Term σ ν)}
    (h : OmegaUnifiable (.app f xs) (.app g ys)) : f = g := by
  rcases h with ⟨E, hE, hst⟩
  simp only [leftCopy, rightCopy, Term.mapVar_app] at hst
  exact (hE.decomp hst).1

theorem finite_head_eq {f g : σ} {xs ys : List (Term σ ν)}
    (h : Unifiable (.app f xs) (.app g ys)) : f = g :=
  omega_head_eq (OmegaUnifiable.of_unifiable h)

/-- A flat application has no non-variable proper subterm. -/
theorem flat_app_subterm_eq {f : σ} {args : List (Term σ ν)}
    (hargs : ∀ a ∈ args, ∃ x, a = .var x) {s : Term σ ν}
    (hs : Subterm s (.app f args)) (happ : s.isApp = true) :
    s = .app f args := by
  cases hs with
  | refl => rfl
  | arg ha hsa =>
      obtain ⟨x, rfl⟩ := hargs _ ha
      rw [hsa.eq_of_var] at happ
      simp at happ

/-- Finite non-overlap already determines each finite root contraction. -/
theorem deterministic_of_nonOverlapping {R : TRS σ ν}
    (hno : NonOverlapping R) (hvar : TRS.RhsDetermined R) : Deterministic R := by
  rintro s t u ⟨r, hr, a, hsa, hta⟩ ⟨r', hr', b, hsb, hub⟩
  have hu : Unifiable r.lhs r'.lhs := ⟨a, b, hsa.symm.trans hsb⟩
  obtain ⟨heq, _⟩ := hno r hr r' hr' r.lhs (Subterm.refl _) r.lhs_isApp hu
  subst r'
  exact rootStep_eq_of_commonGeneralisation
    (CommonGeneralisation.self r (hvar r hr)) a b hsa hsb hta hub

/-- Every substituted occurring variable remains a subterm of the substituted term. -/
theorem substituted_variable_is_subterm [DecidableEq ν] (s : Subst σ ν) :
    ∀ (t : Term σ ν) (x : ν), x ∈ Term.vars t →
      Subterm (s x) (Subst.apply s t) := by
  intro t
  induction t using Term.rec' with
  | hvar y =>
      intro x hx
      have hxy : x = y := by simpa using hx
      subst x
      exact Subterm.refl _
  | happ f args ih =>
      intro x hx
      obtain ⟨a, ha, hxa⟩ := Term.mem_varsList_iff.mp hx
      simp only [Subst.apply_app, Subst.applyList_eq_map]
      exact Subterm.arg (List.mem_map_of_mem ha) (ih a ha x hxa)

/-- Different nullary outputs cannot share a variable-respecting generalisation
when the first output is absent from its own left-hand side. -/
theorem noCommonGeneralisation_of_distinct_nullary_rhs
    {r r' : Rule σ ν} {f g : σ} (hfg : f ≠ g)
    (hr : r.rhs = .app f []) (hr' : r'.rhs = .app g [])
    (habsent : ¬ Subterm r.rhs r.lhs) : ¬ Nonempty (CommonGeneralisation r r') := by
  classical
  rintro ⟨cg⟩
  cases hgr : cg.gr with
  | var x =>
      have hx : x ∈ Term.vars cg.gl := by
        by_contra hnone
        let p : Subst σ ν := fun _ => .app f []
        let q : Subst σ ν := fun y => if y = x then .app g [] else .app f []
        have hl : Subst.apply p cg.gl = Subst.apply q cg.gl := by
          apply apply_eq_of_agree
          intro y hy
          have hyx : y ≠ x := fun heq => hnone (heq ▸ hy)
          simp [p, q, hyx]
        have hval := cg.determined p q hl
        have heq : (Term.app f [] : Term σ ν) = .app g [] := by
          simpa [hgr, p, q] using hval
        exact hfg (Term.app.inj heq).1
      have hs := substituted_variable_is_subterm cg.s₁ cg.gl x hx
      have hxval : cg.s₁ x = r.rhs := by
        simpa only [hgr, Subst.apply_var] using cg.apply_gr₁
      rw [hxval, cg.apply_gl₁] at hs
      exact habsent hs
  | app a args =>
      have h1 := cg.apply_gr₁
      have h2 := cg.apply_gr₂
      rw [hgr, Subst.apply_app, hr] at h1
      rw [hgr, Subst.apply_app, hr'] at h2
      exact hfg ((Term.app.inj h1).1.symm.trans (Term.app.inj h2).1)

end ClassExamples

namespace HuetSystem

theorem subterm_ruleAA_eq {s : Term Nat Nat}
    (hs : Subterm s ruleAA.lhs) (happ : s.isApp = true) : s = ruleAA.lhs :=
  ClassExamples.flat_app_subterm_eq
    (fun a ha => ⟨0, by simpa using ha⟩) hs happ

theorem subterm_ruleC_eq {s : Term Nat Nat}
    (hs : Subterm s ruleC.lhs) (happ : s.isApp = true) : s = ruleC.lhs :=
  ClassExamples.flat_app_subterm_eq (by simp) hs happ

theorem subterm_ruleAB_cases {s : Term Nat Nat}
    (hs : Subterm s ruleAB.lhs) (happ : s.isApp = true) :
    s = ruleAB.lhs ∨ s = .app 2 [.var 0] := by
  change Subterm s (.app 1 [.var 0, .app 2 [.var 0]]) at hs
  cases hs with
  | refl => exact Or.inl rfl
  | arg ha hsa =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · rw [hsa.eq_of_var] at happ
        simp at happ
      · exact Or.inr (ClassExamples.flat_app_subterm_eq
          (fun a ha => ⟨0, by simpa using ha⟩) hsa happ)

theorem nonvariable_subterm_cases {r : Rule Nat Nat} (hr : r ∈ trs)
    {s : Term Nat Nat} (hs : Subterm s r.lhs) (happ : s.isApp = true) :
    s = r.lhs ∨ s = .app 2 [.var 0] := by
  simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Or.inl (subterm_ruleAA_eq hs happ)
  · exact subterm_ruleAB_cases hs happ
  · exact Or.inl (subterm_ruleC_eq hs happ)

theorem proper_pattern_not_omega_unifiable {r : Rule Nat Nat} (hr : r ∈ trs) :
    ¬ OmegaUnifiable (.app 2 [.var 0]) r.lhs := by
  intro h
  simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  all_goals
    have hh := ClassExamples.omega_head_eq h
    simp at hh

theorem critical_lhs_not_unifiable : ¬ Unifiable ruleAA.lhs ruleAB.lhs := by
  rintro ⟨a, b, h⟩
  exact Huet.lhs_not_unifiable ⟨a, b, h⟩

theorem unifiable_lhs_eq {r r' : Rule Nat Nat} (hr : r ∈ trs) (hr' : r' ∈ trs)
    (h : Unifiable r.lhs r'.lhs) : r = r' := by
  simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hr hr'
  rcases hr with rfl | rfl | rfl <;> rcases hr' with rfl | rfl | rfl
  · rfl
  · exact (critical_lhs_not_unifiable h).elim
  · have hh := ClassExamples.finite_head_eq h
    simp at hh
  · obtain ⟨a, b, hab⟩ := h
    exact (critical_lhs_not_unifiable ⟨b, a, hab.symm⟩).elim
  · rfl
  · have hh := ClassExamples.finite_head_eq h
    simp at hh
  · have hh := ClassExamples.finite_head_eq h
    simp at hh
  · have hh := ClassExamples.finite_head_eq h
    simp at hh
  · rfl

theorem nonOverlapping : NonOverlapping trs := by
  intro r hr r' hr' s hs happ hu
  rcases nonvariable_subterm_cases hr hs happ with hroot | hpat
  · subst s
    exact ⟨unifiable_lhs_eq hr hr' hu, rfl⟩
  · subst s
    exact (proper_pattern_not_omega_unifiable hr' (OmegaUnifiable.of_unifiable hu)).elim

theorem proper_omega_overlaps_absent :
    ∀ r ∈ trs, ∀ r' ∈ trs, ∀ s : Term Nat Nat,
      ProperSubterm s r.lhs → s.isApp = true → ¬ OmegaUnifiable s r'.lhs := by
  intro r hr r' hr' s hs happ hu
  rcases nonvariable_subterm_cases hr (Subterm.of_properSubterm hs) happ with hroot | hpat
  · have hlt := hs.size_lt
    rw [hroot] at hlt
    exact (lt_irrefl _ hlt).elim
  · subst s
    exact proper_pattern_not_omega_unifiable hr' hu

theorem root_deterministic : Deterministic trs :=
  ClassExamples.deterministic_of_nonOverlapping nonOverlapping rhsDetermined

/-- This uses the current finite-root definition of AlmostNonOmegaOverlapping. -/
theorem almostNonOmegaOverlapping : AlmostNonOmegaOverlapping trs :=
  ⟨proper_omega_overlaps_absent, root_deterministic⟩

theorem not_nonOmegaOverlapping : ¬ NonOmegaOverlapping trs := by
  intro h
  have heq := (h ruleAA (by simp [trs]) ruleAB (by simp [trs])
    ruleAA.lhs (Subterm.refl _) rfl Huet.lhs_omegaUnifiable).1
  have hrhs := congrArg Rule.rhs heq
  simp [ruleAA, ruleAB] at hrhs

/-- All rules and all non-variable subterms are covered, not only the critical pair. -/
theorem whole_system_class_certificate :
    NonOverlapping trs ∧ AlmostNonOmegaOverlapping trs ∧ TRS.RhsDetermined trs ∧
      ¬ NonOmegaOverlapping trs ∧ ¬ UNconv trs ∧ ¬ UNred trs :=
  ⟨nonOverlapping, almostNonOmegaOverlapping, rhsDetermined,
    not_nonOmegaOverlapping, not_UNconv, not_UNred⟩

theorem no_common_generalisation : ¬ Nonempty (CommonGeneralisation ruleAA ruleAB) := by
  refine ClassExamples.noCommonGeneralisation_of_distinct_nullary_rhs
    (f := 3) (g := 4) (by decide) rfl rfl ?_
  intro hs
  have hbad := subterm_ruleAA_eq hs rfl
  simp [ruleAA] at hbad

/-- Finite root determinism does not supply common generalisations for
infinite-only root overlaps in the current class definition. -/
theorem finite_root_condition_not_common_generalisation :
    AlmostNonOmegaOverlapping trs ∧ TRS.RhsDetermined trs ∧
      OmegaUnifiable ruleAA.lhs ruleAB.lhs ∧
      ¬ Nonempty (CommonGeneralisation ruleAA ruleAB) :=
  ⟨almostNonOmegaOverlapping, rhsDetermined, Huet.lhs_omegaUnifiable,
    no_common_generalisation⟩

end HuetSystem

namespace KlopSystem

theorem nonvariable_subterm_eq {r : Rule Nat Nat} (hr : r ∈ trs)
    {s : Term Nat Nat} (hs : Subterm s r.lhs) (happ : s.isApp = true) : s = r.lhs := by
  simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ClassExamples.flat_app_subterm_eq (by simp) hs happ
  · exact ClassExamples.flat_app_subterm_eq (fun a ha => ⟨0, by simpa using ha⟩) hs happ
  · exact ClassExamples.flat_app_subterm_eq (fun a ha => ⟨0, by simpa using ha⟩) hs happ

theorem omega_unifiable_lhs_eq {r r' : Rule Nat Nat} (hr : r ∈ trs) (hr' : r' ∈ trs)
    (h : OmegaUnifiable r.lhs r'.lhs) : r = r' := by
  simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hr hr'
  rcases hr with rfl | rfl | rfl <;> rcases hr' with rfl | rfl | rfl
  all_goals first
  | rfl
  | have hh := ClassExamples.omega_head_eq h
    simp at hh

theorem nonOmegaOverlapping : NonOmegaOverlapping trs := by
  intro r hr r' hr' s hs happ hu
  have heq := nonvariable_subterm_eq hr hs happ
  subst s
  exact ⟨omega_unifiable_lhs_eq hr hr' hu, rfl⟩

theorem rhsDetermined : TRS.RhsDetermined trs := by
  intro r hr
  simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · intro a b _
    rfl
  · intro a b hab
    have h0 : a 0 = b 0 := by simpa [ruleC] using hab
    change Term.app 2 [a 0, .app 1 [a 0]] = Term.app 2 [b 0, .app 1 [b 0]]
    rw [h0]
  · intro a b _
    rfl

/-- The entire system lies in the non-omega class and is still nonconfluent. -/
theorem whole_system_class_certificate :
    NonOmegaOverlapping trs ∧ TRS.RhsDetermined trs ∧ ¬ confluent trs :=
  ⟨nonOmegaOverlapping, rhsDetermined, not_confluent⟩

end KlopSystem

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.HuetSystem.trs
#check @OperatorKO7.Meta.UniqueNormalization.KlopSystem.trs

#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.step_FCC_A
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.step_FCGC_B
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.tA_normalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.tB_normalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.conv_A_B
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.not_UNconv
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.not_UNred
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.rhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.HuetSystem.hypothesis_required
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.stepStar_A_E
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.stepStar_A_CE
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.klop_both_reductions
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.conv_E_CE
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.tE_normalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.not_stepStar_tCE_tE
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.not_joinable_tE_tCE
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.not_confluent
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.klop_example_three
