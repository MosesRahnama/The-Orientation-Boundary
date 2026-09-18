import OperatorKO7.Meta.Rewriting.CriticalPairComplete

/-!
# Termination from a well-founded measure: discharging the SN hypothesis

Roadmap source: the confluence toolkit. The Critical Pair Lemma corollary
`confluent_of_cp_joinable_of_SN` consumes a strong-normalization hypothesis on
`Step (renameTRS R)`, expressed as well-foundedness of the reverse step relation
`fun x y => Step (renameTRS R) y x`. This module supplies that hypothesis from a
concrete, monotone measure, completing the termination side of the confluence
pipeline: a measure into any well-founded order that strictly decreases on every
rewrite step proves strong normalization, and strong normalization plus
critical-pair joinability gives confluence.

## What this module delivers

The measure-to-termination bridge:

- `sn_of_measure_decreasing` : a measure `m : Term sigma nu → beta` into a type
  with a `WellFoundedRelation`, strictly decreasing on every `Step R` step,
  proves `WellFounded (flip (Step R))`, the strong-normalization shape. The pullback
  `InvImage.wf` carries well-foundedness back along `m`, and `Subrelation.wf` slots
  the reverse step relation under that pullback.
- `sn_of_natMeasure` : the `Nat`-valued corollary, where the decrease is the plain
  order `m t < m s`. This is the everyday termination certificate: any natural-number
  measure that drops on each step terminates.

The composition with confluence:

- `confluent_of_cp_joinable_of_measure` : a measure strictly decreasing on every
  `Step (renameTRS R)` step, together with critical-pair joinability, gives
  `AbsConfluent (Step (renameTRS R))`. The measure discharges strong normalization
  through `sn_of_measure_decreasing`, and `confluent_of_cp_joinable_of_SN` upgrades
  joinable critical pairs to confluence. This closes the SN side of the decision
  pipeline from a concrete measure.

Non-vacuity, a concrete terminating system:

- `Collapse.step_size_decreasing` : structural size strictly decreases on every
  rewrite step of the one-rule projection system `c(x) -> x`, established by
  induction on the step (a root contraction discards the wrapper symbol; a
  contextual step shrinks one argument slot).
- `Collapse.demo_SN` : the strong-normalization conclusion for that system, the
  size measure fed through `sn_of_natMeasure`.

Relation: Step (and its closure inside `AbsConfluent`).
Property: SN for the measure lemmas, confluence for the composition.

Trust: kernel-only; baseline-only under `#print axioms` (a subset of
`{propext, Classical.choice, Quot.sound}`). Any `Classical.choice`/`propext`
dependence is inherited from the `Finset`/`DecidableEq` plumbing of the
foundation modules.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting

open scoped Subst
open Subst

universe u v w

variable {sigma : Type u} {nu : Type v}

/-! ## The measure-to-termination bridge

A measure into a well-founded order that strictly decreases on every step proves
strong normalization. The reverse step relation `fun x y => Step R y x` (that is,
`flip (Step R)`) is a subrelation of the measure pullback `InvImage inst.rel m`, and
`InvImage.wf` transports well-foundedness back along `m`. -/

/-- Strong normalization from a strictly decreasing measure. Given a measure
`m : Term sigma nu → beta` into a type carrying a `WellFoundedRelation`, if every
one-step rewrite `Step R s t` strictly decreases the measure
(`inst.rel (m t) (m s)`), then `flip (Step R)` is well-founded; equivalently,
`Step R` is strongly normalizing. The reverse step relation embeds into the
measure pullback `InvImage inst.rel m`, which is well-founded by `InvImage.wf`, so
`Subrelation.wf` concludes. -/
theorem sn_of_measure_decreasing {beta : Type w} [inst : WellFoundedRelation beta]
    (R : TRS sigma nu) (m : Term sigma nu → beta)
    (dec : ∀ s t, Step R s t → inst.rel (m t) (m s)) :
    WellFounded (flip (Step R)) := by
  -- the reverse step relation embeds into the measure pullback `InvImage inst.rel m`
  have hsub : Subrelation (flip (Step R)) (InvImage inst.rel m) := by
    intro x y hxy
    -- `flip (Step R) x y` is `Step R y x`, and `dec y x` gives `inst.rel (m x) (m y)`
    exact dec y x hxy
  -- the pullback is well-founded; the subrelation inherits well-foundedness
  exact hsub.wf (InvImage.wf m inst.wf)

/-- Strong normalization from a strictly decreasing `Nat`-valued measure. If every
one-step rewrite `Step R s t` strictly drops a natural-number measure
(`m t < m s`), then `flip (Step R)` is well-founded. The everyday termination
certificate, the `Nat`-instance specialization of `sn_of_measure_decreasing`. -/
theorem sn_of_natMeasure (R : TRS sigma nu) (m : Term sigma nu → Nat)
    (dec : ∀ s t, Step R s t → m t < m s) :
    WellFounded (flip (Step R)) :=
  sn_of_measure_decreasing R m dec

/-! ## Composition with the Critical Pair Lemma corollary

A measure strictly decreasing on `Step (renameTRS R)` discharges the
strong-normalization hypothesis of `confluent_of_cp_joinable_of_SN`. The reverse
step relation `flip (Step (renameTRS R))` is definitionally
`fun x y => Step (renameTRS R) y x`, the shape that corollary consumes. -/

/-- Confluence from a decreasing measure and joinable critical pairs. If a measure
`m` strictly decreases (in a well-founded order) on every step of `renameTRS R`,
and every critical pair of `R` is joinable in `renameTRS R`, then
`Step (renameTRS R)` is confluent. The measure proves strong normalization via
`sn_of_measure_decreasing`; `confluent_of_cp_joinable_of_SN` then upgrades
critical-pair joinability to confluence. This discharges the SN hypothesis of the
confluence pipeline from a concrete measure. -/
theorem confluent_of_cp_joinable_of_measure {beta : Type w}
    [inst : WellFoundedRelation beta] [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) (m : Term sigma (RenVar nu) → beta)
    (dec : ∀ s t, Step (renameTRS R) s t → inst.rel (m t) (m s))
    (cpj : ∀ p ∈ criticalPairs R, joinable (renameTRS R) p.1 p.2) :
    AbsConfluent (Step (renameTRS R)) := by
  have hSN : WellFounded (flip (Step (renameTRS R))) :=
    sn_of_measure_decreasing (renameTRS R) m dec
  intro a b c hab hac
  exact confluent_of_cp_joinable_of_SN hSN cpj a b c hab hac

/-! ## Non-vacuity: a concrete terminating projection system

The one-rule system `c(x) -> x` (symbol `0` applied to a single argument, projected
onto that argument) is terminating: structural `size` strictly drops on every
rewrite step. A root contraction discards the wrapper symbol; a contextual step
shrinks one argument slot while the surrounding structure is unchanged. Feeding the
size measure through `sn_of_natMeasure` yields the strong-normalization conclusion. -/

namespace Collapse

/-- The projection rule `c(x) -> x`: wrapper symbol `0` applied to the single
variable `0`, rewriting to that variable. Its left-hand side is an application. -/
def collapseRule : Rule Nat Nat where
  lhs := .app 0 [.var 0]
  rhs := .var 0
  lhs_isApp := rfl

/-- The one-rule projection system. -/
def collapseTRS : TRS Nat Nat := [collapseRule]

/-- Size of a list with one slot singled out: the size sum over `pre ++ x :: post`
splits as the sizes of the prefix, the slot, and the suffix. This isolates the
contracted slot so a strict drop in that slot is a strict drop in the whole list. -/
theorem sizeList_middle (pre post : List (Term Nat Nat)) (x : Term Nat Nat) :
    Term.sizeList (pre ++ x :: post)
      = Term.sizeList pre + Term.size x + Term.sizeList post := by
  induction pre with
  | nil => simp [Term.sizeList]
  | cons a as ih => simp only [List.cons_append, Term.sizeList_cons, ih]; omega

/-- Structural size strictly decreases on every rewrite step of the projection
system `c(x) -> x`. By induction on the step: a root contraction sends
`c(t)` (size `1 + size t`) to `t` (size `size t`); a contextual step shrinks one
argument slot by the induction hypothesis, and `sizeList_middle` carries that strict
drop through the surrounding application. -/
theorem step_size_decreasing :
    ∀ s t : Term Nat Nat, Step collapseTRS s t → Term.size t < Term.size s := by
  intro s t h
  induction h with
  | @root s t hroot =>
      obtain ⟨rule, hrule, σ, hs, ht⟩ := hroot
      -- the singleton system forces `rule = collapseRule`
      rw [collapseTRS, List.mem_singleton] at hrule
      subst hrule
      -- `s = σ • c(x) = c(σ 0)`, `t = σ • x = σ 0`
      subst hs; subst ht
      show Term.size (σ • collapseRule.rhs) < Term.size (σ • collapseRule.lhs)
      rw [collapseRule]
      -- `σ • app 0 [var 0] = app 0 [σ 0]` and `σ • var 0 = σ 0`, computed by `simp`
      simp only [apply_app, applyList_cons, applyList_nil, apply_var,
        Term.size_app, Term.sizeList_cons, Term.sizeList_nil]
      have h0 := Term.one_le_size (σ 0)
      omega
  | @arg f pre post a b _hstep ih =>
      -- the contextual step shrinks the slot `a -> b`; the rest is unchanged
      simp only [Term.size_app, sizeList_middle]
      omega

/-- Strong normalization of the projection system `c(x) -> x`: the reverse step
relation `flip (Step collapseTRS)` is well-founded. The size measure strictly
decreases on every step (`step_size_decreasing`), so `sn_of_natMeasure` concludes.
A concrete, non-vacuous instance of the termination criterion. -/
theorem demo_SN : WellFounded (flip (Step collapseTRS)) :=
  sn_of_natMeasure collapseTRS Term.size step_size_decreasing

end Collapse

end OperatorKO7.Meta.Rewriting

/-! ## Verification: headline types and axiom audit -/

open OperatorKO7.Meta.Rewriting in
#check @sn_of_measure_decreasing
open OperatorKO7.Meta.Rewriting in
#check @sn_of_natMeasure
open OperatorKO7.Meta.Rewriting in
#check @confluent_of_cp_joinable_of_measure
open OperatorKO7.Meta.Rewriting in
#check @Collapse.step_size_decreasing
open OperatorKO7.Meta.Rewriting in
#check @Collapse.demo_SN

#print axioms OperatorKO7.Meta.Rewriting.sn_of_measure_decreasing
#print axioms OperatorKO7.Meta.Rewriting.sn_of_natMeasure
#print axioms OperatorKO7.Meta.Rewriting.confluent_of_cp_joinable_of_measure
#print axioms OperatorKO7.Meta.Rewriting.Collapse.step_size_decreasing
#print axioms OperatorKO7.Meta.Rewriting.Collapse.demo_SN
