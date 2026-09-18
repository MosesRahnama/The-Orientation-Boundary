import OperatorKO7.Meta.Methods.OrientationClosure.DependencyPairSoundness
import Mathlib.Tactic

/-!
# Processor semantics for dependency-pair problems

A dependency-pair problem over a first-order rewrite system `R` is a relation `P` on calls
`(f, args)`. Its minimal chain relation composes argument rewriting with one `P` edge, with strongly
normalizing arguments at both ends; the problem is finite when that relation is well founded
(`FiniteDP`). The dependency pairs of `R` form one such relation (`dpPairs`), and finiteness of
their problem gives termination of `R` (`terminating_of_finiteDP`).

Processors transform problems. The reduction-triple processor removes the strictly decreasing
edges and is sound (`reductionTriple_processor_sound`); reduction pairs are the triples whose two
weak relations coincide (`tripleOfPair`). The identity processor is sound, while deleting a live
edge is not (`deleting_live_pair_unsound`). An argument filtering transports a reduction pair on
filtered calls to one on calls (`filteredPair`), and the empty filtering removes no recursive
self-call (`emptyFilter_no_strict_self_call`). Termination of a quotient relation gives termination
of the relation (`wf_of_quotStep_wf`); the converse fails (`quotient_self_loop_control`). A shared
representation that performs at least one rewrite step per shared step inherits termination and
its step counts (`wf_of_simulates`, `simulates_relPow`); readback identity alone does not give
termination (`sharing_same_readback_self_loop`).
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.ProcessorSemantics

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness

universe u v w

variable {sigma : Type u} {nu : Type v}

/-- A call: a root symbol with its argument list. -/
abbrev Call (sigma : Type u) (nu : Type v) := sigma × List (Term sigma nu)

/-- A minimal chain step for the pair relation `P`: argument rewriting from `c`, then one `P` edge to
`d`; both ends have strongly normalizing arguments. -/
def ChainP (R : TRS sigma nu) (P : Call sigma nu → Call sigma nu → Prop) (c d : Call sigma nu) :
    Prop :=
  (∀ a ∈ c.2, SN R a) ∧ (∀ a ∈ d.2, SN R a) ∧
    ∃ xs, Relation.ReflTransGen (ArgStep R) c.2 xs ∧ P (c.1, xs) d

/-- A dependency-pair problem is finite when its minimal chain relation is well founded. -/
def FiniteDP (R : TRS sigma nu) (P : Call sigma nu → Call sigma nu → Prop) : Prop :=
  WellFounded (fun d c => ChainP R P c d)

/-- The dependency pairs of `R` as a relation on calls. -/
def dpPairs (R : TRS sigma nu) (c d : Call sigma nu) : Prop :=
  ∃ rule ∈ R, ∃ σ : Subst sigma nu, Term.app c.1 c.2 = Subst.apply σ rule.lhs ∧
    ∃ targs, IsSubterm (Term.app d.1 targs) rule.rhs ∧ IsDefined R d.1 ∧
      d.2 = Subst.applyList σ targs

theorem chainP_dpPairs_iff (R : TRS sigma nu) (c d : Call sigma nu) :
    ChainP R (dpPairs R) c d ↔ MinChainStep R c d := by
  constructor
  · rintro ⟨hc, hd, xs, hr, rule, hrule, σ, hl, targs, hs, hdef, hdd⟩
    exact ⟨hc, hd, xs, hr, rule, hrule, σ, hl, targs, hs, hdef, hdd⟩
  · rintro ⟨hc, hd, xs, hr, rule, hrule, σ, hl, targs, hs, hdef, hdd⟩
    exact ⟨hc, hd, xs, hr, rule, hrule, σ, hl, targs, hs, hdef, hdd⟩

/-- Finiteness of the dependency-pair problem of `R` gives termination of `R`. -/
theorem terminating_of_finiteDP [DecidableEq nu] (R : TRS sigma nu)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) (h : FiniteDP R (dpPairs R)) :
    ∀ t : Term sigma nu, SN R t :=
  terminating_of_minChain_wf R hvars
    (Subrelation.wf (fun {_ _} hm => (chainP_dpPairs_iff R _ _).2 hm) h)

/-- A problem with fewer edges has fewer chains. -/
theorem finiteDP_mono {R : TRS sigma nu} {P Q : Call sigma nu → Call sigma nu → Prop}
    (hPQ : ∀ {c d}, P c d → Q c d) (h : FiniteDP R Q) : FiniteDP R P :=
  Subrelation.wf (fun {_ _} hc => ⟨hc.1, hc.2.1, hc.2.2.choose, hc.2.2.choose_spec.1,
    hPQ hc.2.2.choose_spec.2⟩) h

/-- Problems with the same edges are finite together; this is the soundness and completeness of the
identity processor. -/
theorem neutral_processor_iff {R : TRS sigma nu} {P Q : Call sigma nu → Call sigma nu → Prop}
    (hPQ : ∀ c d, P c d ↔ Q c d) : FiniteDP R P ↔ FiniteDP R Q :=
  ⟨finiteDP_mono fun h => (hPQ _ _).2 h, finiteDP_mono fun h => (hPQ _ _).1 h⟩

theorem argSteps_sn {R : TRS sigma nu} {xs ys : List (Term sigma nu)}
    (h : Relation.ReflTransGen (ArgStep R) xs ys) (hxs : ∀ a ∈ xs, SN R a) : ∀ b ∈ ys, SN R b := by
  induction h with
  | refl => exact hxs
  | tail _ hst ih => exact argStep_sn ih hst

/-! ## Strict-or-weak well-foundedness -/

/-- A relation whose every step is strict for a well-founded relation `S`, or weak and inside a
second well-founded relation `Q'`, is well founded when a weak step followed by a strict step is
strict. -/
theorem wf_of_strict_or_weak {α : Type w} {Q S W Q' : α → α → Prop}
    (hS : WellFounded (fun b a => S a b)) (hQ' : WellFounded (fun b a => Q' a b))
    (hWS : ∀ {a b c}, W a b → S b c → S a c)
    (hQ : ∀ {a b}, Q a b → S a b ∨ (W a b ∧ Q' a b)) :
    WellFounded (fun b a => Q a b) := by
  have key : ∀ a, Acc (fun b a => S a b) a → ∀ b, Acc (fun b a => Q' a b) b →
      (∀ c, S b c → S a c) → Acc (fun b a => Q a b) b := by
    intro a ha
    induction ha with
    | intro a _ ihS =>
      intro b hb
      induction hb with
      | intro b _ ihQ =>
        intro hbelow
        refine Acc.intro _ fun e he => ?_
        rcases hQ he with hs | ⟨hw, hq⟩
        · exact ihS e (hbelow e hs) e (hQ'.apply e) (fun _ h => h)
        · exact ihQ e hq (fun c hc => hbelow c (hWS hw hc))
  exact ⟨fun a => key a (hS.apply a) a (hQ'.apply a) (fun _ h => h)⟩

/-! ## Reduction triples -/

/-- A reduction triple on calls: a weak relation for argument rewriting, and weak and strict
relations for pair edges, with the compositions the processor uses. -/
structure CallReductionTriple (R : TRS sigma nu) where
  rulesWeak : Call sigma nu → Call sigma nu → Prop
  pairWeak : Call sigma nu → Call sigma nu → Prop
  pairStrict : Call sigma nu → Call sigma nu → Prop
  rules_refl : ∀ c, rulesWeak c c
  rules_trans : ∀ {a b c}, rulesWeak a b → rulesWeak b c → rulesWeak a c
  rules_strict : ∀ {a b c}, rulesWeak a b → pairStrict b c → pairStrict a c
  rules_weak : ∀ {a b c}, rulesWeak a b → pairWeak b c → pairWeak a c
  weak_strict : ∀ {a b c}, pairWeak a b → pairStrict b c → pairStrict a c
  strict_wf : WellFounded (fun d c => pairStrict c d)
  arg_weak : ∀ (f : sigma) {xs ys : List (Term sigma nu)}, (∀ a ∈ xs, SN R a) →
    ArgStep R xs ys → rulesWeak (f, xs) (f, ys)

theorem triple_reach {R : TRS sigma nu} (T : CallReductionTriple R) (f : sigma)
    {xs ys : List (Term sigma nu)} (h : Relation.ReflTransGen (ArgStep R) xs ys)
    (hxs : ∀ a ∈ xs, SN R a) : T.rulesWeak (f, xs) (f, ys) := by
  induction h with
  | refl => exact T.rules_refl _
  | tail hr hst ih => exact T.rules_trans ih (T.arg_weak f (argSteps_sn hr hxs) hst)

/-- The reduction-triple processor: if every edge between calls with strongly normalizing arguments
is weak or strict, the problem is finite once its non-strict edges form a finite problem. -/
theorem reductionTriple_processor_sound {R : TRS sigma nu} (T : CallReductionTriple R)
    (P : Call sigma nu → Call sigma nu → Prop)
    (hP : ∀ {c d : Call sigma nu}, (∀ a ∈ c.2, SN R a) → (∀ a ∈ d.2, SN R a) → P c d →
      T.pairWeak c d ∨ T.pairStrict c d)
    (hfin : FiniteDP R (fun c d => P c d ∧ ¬ T.pairStrict c d)) : FiniteDP R P := by
  unfold FiniteDP at hfin ⊢
  refine wf_of_strict_or_weak (S := T.pairStrict) (W := T.pairWeak)
    (Q' := ChainP R (fun c d => P c d ∧ ¬ T.pairStrict c d)) T.strict_wf hfin T.weak_strict ?_
  rintro c d ⟨hc, hd, xs, hr, hp⟩
  have hrw := triple_reach T c.1 hr hc
  have hxs := argSteps_sn hr hc
  by_cases hs : T.pairStrict (c.1, xs) d
  · exact Or.inl (T.rules_strict hrw hs)
  · rcases hP hxs hd hp with hw | hs'
    · exact Or.inr ⟨T.rules_weak hrw hw, hc, hd, xs, hr, hp, hs⟩
    · exact absurd hs' hs

/-- A reduction pair on calls is the reduction triple whose two weak relations coincide. -/
def tripleOfPair {R : TRS sigma nu} (P : CallReductionPair R) : CallReductionTriple R where
  rulesWeak := P.weak
  pairWeak := P.weak
  pairStrict := P.strict
  rules_refl := P.weak_refl
  rules_trans := P.weak_trans
  rules_strict := P.weak_strict
  rules_weak := P.weak_trans
  weak_strict := P.weak_strict
  strict_wf := P.strict_wf
  arg_weak := P.arg_weak

/-- The composition law `rulesWeak ; pairWeak ⊆ pairWeak` depends on the roles: reading argument
steps by `≥` and weak pair edges by `=` of a measure breaks it at any two calls with different
measures. -/
theorem swapped_weak_roles_break_composition (μ : Call sigma nu → Nat) {c d : Call sigma nu}
    (h : μ d < μ c) : ¬ ∀ a b e : Call sigma nu, μ b ≤ μ a → μ e = μ b → μ e = μ a := by
  intro hall
  have := hall c d d h.le rfl
  omega

/-! ## Deleting a live edge -/

/-- The empty rewrite system over one symbol. -/
def emptyTRS : TRS Unit Nat := []

theorem emptyTRS_no_step (t u : Term Unit Nat) : ¬ Step emptyTRS t u := by
  intro h
  induction h with
  | root h =>
    obtain ⟨rule, hrule, -⟩ := h
    simp [emptyTRS] at hrule
  | arg _ _ _ _ ih => exact ih

theorem emptyTRS_sn (t : Term Unit Nat) : SN emptyTRS t :=
  Acc.intro _ fun u h => absurd h (emptyTRS_no_step t u)

/-- Every call is its own successor. -/
def selfLoop (c d : Call Unit Nat) : Prop := c = d

/-- Deleting a live edge is unsound: the problem without edges is finite, the self-loop problem is
not. -/
theorem deleting_live_pair_unsound :
    FiniteDP emptyTRS (fun _ _ => False) ∧ ¬ FiniteDP emptyTRS selfLoop := by
  refine ⟨⟨fun c => Acc.intro _ fun d h => h.2.2.choose_spec.2.elim⟩, fun h => ?_⟩
  have hloop : ChainP emptyTRS selfLoop ((), []) ((), []) :=
    ⟨fun a _ => emptyTRS_sn a, fun a _ => emptyTRS_sn a, [], .refl, rfl⟩
  exact (h.asymmetric _ _ hloop) hloop

/-! ## Argument filtering -/

/-- The arguments at the kept positions, in the order of `keep`. -/
def filterArgs (keep : List Nat) (xs : List (Term sigma nu)) : List (Term sigma nu) :=
  keep.filterMap fun i => xs[i]?

/-- The filtered call. -/
def filterCall (π : sigma → List Nat) (c : Call sigma nu) : Call sigma nu :=
  (c.1, filterArgs (π c.1) c.2)

/-- Rewriting an argument at a position that is not kept leaves the filtered arguments unchanged. -/
theorem filterArgs_step_outside (keep : List Nat) (pre post : List (Term sigma nu))
    (a b : Term sigma nu) (h : pre.length ∉ keep) :
    filterArgs keep (pre ++ a :: post) = filterArgs keep (pre ++ b :: post) := by
  unfold filterArgs
  apply List.filterMap_congr
  intro i hi
  have hne : i ≠ pre.length := fun he => h (he ▸ hi)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
  · rw [List.getElem?_append_right hgt.le, List.getElem?_append_right hgt.le]
    obtain ⟨k, hk⟩ : ∃ k, i - pre.length = k + 1 := ⟨i - pre.length - 1, by omega⟩
    rw [hk, List.getElem?_cons_succ, List.getElem?_cons_succ]

/-- A reduction pair on filtered calls induces a reduction pair on calls. -/
def filteredPair {R : TRS sigma nu} (π : sigma → List Nat) (P : CallReductionPair R)
    (hkeep : ∀ (f : sigma) {xs ys : List (Term sigma nu)}, (∀ a ∈ xs, SN R a) → ArgStep R xs ys →
      P.weak (filterCall π (f, xs)) (filterCall π (f, ys)))
    (hpair : ∀ rule ∈ R, ∀ (σ : Subst sigma nu) (f : sigma) (largs : List (Term sigma nu)),
      rule.lhs = .app f largs → ∀ (g : sigma) (targs : List (Term sigma nu)),
      IsSubterm (.app g targs) rule.rhs → IsDefined R g →
      (∀ a ∈ Subst.applyList σ largs, SN R a) → (∀ a ∈ Subst.applyList σ targs, SN R a) →
      P.strict (filterCall π (f, Subst.applyList σ largs)) (filterCall π (g, Subst.applyList σ targs))) :
    CallReductionPair R where
  weak c d := P.weak (filterCall π c) (filterCall π d)
  strict c d := P.strict (filterCall π c) (filterCall π d)
  weak_refl _ := P.weak_refl _
  weak_trans h₁ h₂ := P.weak_trans h₁ h₂
  weak_strict h₁ h₂ := P.weak_strict h₁ h₂
  strict_wf := InvImage.wf (filterCall π) P.strict_wf
  arg_weak f _ _ hxs h := hkeep f hxs h
  pair_strict := hpair

/-- The empty filtering keeps no argument, so no recursive self-call is strict under an irreflexive
strict relation; such a filtering removes no edge. -/
theorem emptyFilter_no_strict_self_call {R : TRS sigma nu} (P : CallReductionPair R)
    (hirr : ∀ c, ¬ P.strict c c) (f : sigma) (xs ys : List (Term sigma nu)) :
    ¬ P.strict (filterCall (fun _ => []) (f, xs)) (filterCall (fun _ => []) (f, ys)) := by
  have h : filterCall (fun _ : sigma => ([] : List Nat)) (f, xs) =
      filterCall (fun _ : sigma => ([] : List Nat)) (f, ys) := by
    simp [filterCall, filterArgs]
  rw [h]
  exact hirr _

/-! ## Equational quotients -/

section Quotients

variable {α : Type w}

/-- The relation `r` read on the classes of the equivalence `s`. -/
def QuotStep (r : α → α → Prop) (s : Setoid α) (x y : Quotient s) : Prop :=
  ∃ a b, Quotient.mk s a = x ∧ Quotient.mk s b = y ∧ r a b

/-- Termination of the quotient relation gives termination of the relation. -/
theorem wf_of_quotStep_wf (r : α → α → Prop) (s : Setoid α)
    (h : WellFounded (fun y x => QuotStep r s x y)) : WellFounded (fun b a => r a b) :=
  Subrelation.wf (fun {_ _} hab => ⟨_, _, rfl, rfl, hab⟩) (InvImage.wf (Quotient.mk s) h)

end Quotients

/-- The setoid relating every two booleans. -/
def trivialSetoid : Setoid Bool :=
  ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩

/-- The one-step relation `true → false`. -/
def trueToFalse (a b : Bool) : Prop := a = true ∧ b = false

/-- The converse fails: `true → false` terminates, while identifying `true` with `false` gives the
quotient a self-loop. -/
theorem quotient_self_loop_control :
    WellFounded (fun b a => trueToFalse a b) ∧
      ¬ WellFounded (fun y x => QuotStep trueToFalse trivialSetoid x y) := by
  refine ⟨?_, fun h => ?_⟩
  · let rank : Bool → Nat := fun b => if b then 1 else 0
    apply Subrelation.wf (r := fun y x : Bool => rank y < rank x)
    · intro y x hxy
      rcases hxy with ⟨rfl, rfl⟩
      decide
    · exact InvImage.wf rank Nat.lt_wfRel.wf
  · have hloop : QuotStep trueToFalse trivialSetoid (Quotient.mk _ true) (Quotient.mk _ true) :=
      ⟨true, false, rfl, Quotient.sound trivial, rfl, rfl⟩
    exact (h.asymmetric _ _ hloop) hloop

/-- The trivial quotient merges the two distinct normal forms of the empty relation. -/
theorem quotient_merges_normal_forms :
    (∀ b c : Bool, ¬ (fun _ _ : Bool => False) b c) ∧ true ≠ false ∧
      Quotient.mk trivialSetoid true = Quotient.mk trivialSetoid false :=
  ⟨fun _ _ h => h, by decide, Quotient.sound trivial⟩

/-! ## Sharing -/

section Sharing

variable {α : Type w} {S : Type v}

/-- A shared representation simulates rewriting when every shared step performs at least one rewrite
step on the readback. -/
def Simulates (step : α → α → Prop) (sstep : S → S → Prop) (readback : S → α) : Prop :=
  ∀ {s s'}, sstep s s' → Relation.TransGen step (readback s) (readback s')

/-- A simulating shared representation of a terminating relation terminates. -/
theorem wf_of_simulates {step : α → α → Prop} {sstep : S → S → Prop} {readback : S → α}
    (hsim : Simulates step sstep readback) (hwf : WellFounded (fun b a => step a b)) :
    WellFounded (fun s' s => sstep s s') := by
  have htg : WellFounded (fun b a => Relation.TransGen step a b) := by
    have h := hwf.transGen
    refine Subrelation.wf (fun {b a} hab => ?_) h
    exact Relation.transGen_swap.2 hab
  exact Subrelation.wf (fun {_ _} h => hsim h) (InvImage.wf readback htg)

/-- Paths with exactly `n` steps. -/
inductive RelPow (r : α → α → Prop) : Nat → α → α → Prop
  | zero (a : α) : RelPow r 0 a a
  | succ {n : Nat} {a b c : α} : RelPow r n a b → r b c → RelPow r (n + 1) a c

theorem RelPow.append {r : α → α → Prop} {m n : Nat} {a b c : α} (h₁ : RelPow r m a b)
    (h₂ : RelPow r n b c) : RelPow r (m + n) a c := by
  induction h₂ with
  | zero => simpa using h₁
  | succ _ hst ih => exact RelPow.succ (ih h₁) hst

theorem transGen_relPow {r : α → α → Prop} {a b : α} (h : Relation.TransGen r a b) :
    ∃ k, 1 ≤ k ∧ RelPow r k a b := by
  induction h with
  | single hab => exact ⟨1, le_rfl, RelPow.succ (RelPow.zero _) hab⟩
  | tail _ hbc ih =>
    obtain ⟨k, hk, hp⟩ := ih
    exact ⟨k + 1, by omega, RelPow.succ hp hbc⟩

/-- Costs: `n` shared steps read back to at least `n` rewrite steps. -/
theorem simulates_relPow {step : α → α → Prop} {sstep : S → S → Prop} {readback : S → α}
    (hsim : Simulates step sstep readback) {n : Nat} {s s' : S} (h : RelPow sstep n s s') :
    ∃ m, n ≤ m ∧ RelPow step m (readback s) (readback s') := by
  induction h with
  | zero a => exact ⟨0, le_rfl, RelPow.zero _⟩
  | succ _ hst ih =>
    obtain ⟨m, hm, hp⟩ := ih
    obtain ⟨k, hk, hq⟩ := transGen_relPow (hsim hst)
    exact ⟨m + k, by omega, hp.append hq⟩

end Sharing

/-- Same readback, target self-loop: the shared relation on `Unit` loops while its readback stays at
`0` and the relation on `Nat` is empty, so readback identity gives neither simulation nor
termination. -/
theorem sharing_same_readback_self_loop :
    (∀ s s' : Unit, (fun _ _ : Unit => True) s s' → (fun _ : Unit => (0 : Nat)) s =
      (fun _ : Unit => (0 : Nat)) s') ∧
      WellFounded (fun b a : Nat => (fun _ _ : Nat => False) a b) ∧
      ¬ WellFounded (fun s' s : Unit => (fun _ _ : Unit => True) s s') ∧
      ¬ Simulates (fun _ _ : Nat => False) (fun _ _ : Unit => True) (fun _ : Unit => (0 : Nat)) := by
  refine ⟨fun _ _ _ => rfl, ⟨fun a => Acc.intro _ fun _ h => h.elim⟩, fun h => ?_, fun h => ?_⟩
  · exact (h.asymmetric () () trivial) trivial
  · have := h (s := ()) (s' := ()) trivial
    obtain ⟨k, hk, hp⟩ := transGen_relPow this
    cases hp with
    | zero => omega
    | succ _ hst => exact hst

end OperatorKO7.Methods.OrientationClosure.ProcessorSemantics
