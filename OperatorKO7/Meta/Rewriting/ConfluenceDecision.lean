import OperatorKO7.Meta.Rewriting.CriticalPairComplete

/-!
# A certified confluence decision procedure for a finite rewriting system

Roadmap source: the confluence-toolkit expansion on top of the verified Critical
Pair Lemma (`CriticalPairComplete.lean`). This module turns the Knuth-Bendix/Huet
characterization into an executable check: equip a finite term rewriting system
with a normalizer (a function returning, for each term, a reduct it reaches), run
it on both components of every critical pair, and accept when the two reducts
coincide. Strong normalization of the renamed system then upgrades the resulting
local confluence to confluence.

## What this module delivers

- `Normalizer R` : a function `nf` together with the reachability certificate
  `nf_reach : ∀ t, StepStar R t (nf t)`. Every value `nf t` is a reduct of `t`,
  so a shared `nf`-value certifies joinability.

- `joinable_of_nf_eq` : equal normal forms give joinability. When `nf s = nf t`,
  both `s` and `t` reach the common value `nf s`, so `joinable R s t`.

- `decideConfluence R norm` : the Boolean check. It runs the normalizer of
  `renameTRS R` on both components of every member of `criticalPairs R` and
  accepts when each pair shares a normal form. This is a real enumeration of the
  overlaps (`criticalPairs`), with one genuine comparison per emitted pair.

- `decideConfluence_sound` : when the check succeeds and `Step (renameTRS R)` is
  strongly normalizing (its `flip` is well-founded), `Step (renameTRS R)` is
  confluent (`AbsConfluent`). Route: the check makes every critical pair joinable
  (`joinable_of_nf_eq`), `critical_pair_lemma` turns that into local confluence,
  and `confluent_of_cp_joinable_of_SN` adds strong normalization to reach
  confluence.

- `decideConfluence_complete` : the reach direction. A confluent system whose
  normalizer returns genuine normal forms (irreducible reducts) passes the check:
  confluence drives the two reducts of each critical pair to the same normal form.

- `Demo` : a concrete confluent system `f(c) -> c`, an explicit `Normalizer`, the
  check evaluating to `true`, and the soundness conclusion applied under a clean
  strong-normalization hypothesis.

Trust: kernel-only; baseline-only under `#print axioms` (a subset of
`{propext, Classical.choice, Quot.sound}`). Any `Classical.choice`/`propext`
dependence is from `Finset`/`DecidableEq` plumbing inherited through the
foundation modules.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting

open scoped Subst
open Subst

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Normalizers

A normalizer for `R` assigns to each term a reduct it reaches. The reachability
certificate is the load-bearing field: it is what lets a shared normalizer value
witness joinability. -/

/-- A normalizer for a term rewriting system `R`: a function `nf` taking each term
to a term, together with the certificate that `nf t` is reachable from `t` by the
reflexive-transitive rewrite relation. The reachability field guarantees `nf t` is
a reduct of `t`. -/
structure Normalizer (R : TRS sigma nu) where
  /-- The normalizing function: each term is sent to a chosen reduct. -/
  nf : Term sigma nu → Term sigma nu
  /-- Each value `nf t` is reachable from `t` by the rewrite relation. -/
  nf_reach : ∀ t, StepStar R t (nf t)

/-- Equal normal forms give joinability: if a normalizer sends `s` and `t` to the
same value, then `s` and `t` are joinable, both reaching the common value
`norm.nf s`. -/
theorem joinable_of_nf_eq {R : TRS sigma nu} (norm : Normalizer R)
    {s t : Term sigma nu} (h : norm.nf s = norm.nf t) : joinable R s t :=
  ⟨norm.nf s, norm.nf_reach s, h ▸ norm.nf_reach t⟩

/-! ## The decision procedure

The check runs the normalizer of the renamed system on both components of every
critical pair, accepting when each pair shares a normal form. `criticalPairs R` is
a genuine enumeration of the system's overlaps, so this is a real check. -/

/-- The confluence check for a finite system `R` equipped with a normalizer for the
renamed system `renameTRS R`: every critical pair of `R` is tested for a shared
normal form. Accepts (`true`) exactly when every emitted critical pair has its two
components sent to the same value by `norm.nf`. -/
def decideConfluence [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) (norm : Normalizer (renameTRS R)) : Bool :=
  (criticalPairs R).all (fun p => decide (norm.nf p.1 = norm.nf p.2))

/-- Reading the check back: when `decideConfluence R norm = true`, every critical
pair of `R` has its components sent to a shared normal form, hence is joinable in
`renameTRS R`. This is the bridge from the Boolean check to the hypothesis of the
Critical Pair Lemma. -/
theorem cp_joinable_of_decideConfluence [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {norm : Normalizer (renameTRS R)}
    (h : decideConfluence R norm = true) :
    ∀ q ∈ criticalPairs R, joinable (renameTRS R) q.1 q.2 := by
  intro q hq
  rw [decideConfluence, List.all_eq_true] at h
  have hq' : decide (norm.nf q.1 = norm.nf q.2) = true := h q hq
  exact joinable_of_nf_eq norm (of_decide_eq_true hq')

/-- Soundness of the decision procedure: when the check succeeds and the one-step
relation `Step (renameTRS R)` is strongly normalizing (its `flip` is
well-founded), `Step (renameTRS R)` is confluent. The successful check makes every
critical pair joinable, `critical_pair_lemma` turns that into local confluence, and
`confluent_of_cp_joinable_of_SN` upgrades local confluence to confluence under
strong normalization. -/
theorem decideConfluence_sound [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {norm : Normalizer (renameTRS R)}
    (h : decideConfluence R norm = true)
    (hSN : WellFounded (flip (Step (renameTRS R)))) :
    AbsConfluent (Step (renameTRS R)) := by
  have hcp : ∀ q ∈ criticalPairs R, joinable (renameTRS R) q.1 q.2 :=
    cp_joinable_of_decideConfluence h
  intro a b c hab hac
  exact confluent_of_cp_joinable_of_SN hSN hcp a b c hab hac

/-! ## Completeness: a confluent system with genuine normal forms passes

The reach direction. If `renameTRS R` is confluent and the normalizer returns
genuine normal forms (each `nf t` is irreducible and reachable), then the two
reducts of every critical pair are driven to the same normal form, so the check
accepts. -/

/-- A normalizer returns normal forms when every value `nf t` is irreducible: no
one-step rewrite leaves `nf t`. Together with the reachability field of
`Normalizer`, this says `nf t` is a normal form `t` reaches. -/
def Normalizer.IsNF {R : TRS sigma nu} (norm : Normalizer R) : Prop :=
  ∀ t u, ¬ Step R (norm.nf t) u

/-- A reduction sequence out of an irreducible term is constant: if `n` admits no
one-step rewrite and `StepStar R n u`, then `u = n`. By induction on the closure;
the trailing-step case contradicts irreducibility. This is the uniqueness engine
for completeness. -/
theorem stepStar_eq_of_nf {R : TRS sigma nu} {n u : Term sigma nu}
    (hn : ∀ w, ¬ Step R n w) (h : StepStar R n u) : u = n := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨m, hnm, _⟩
  · rfl
  · exact absurd hnm (hn m)

/-- Completeness of the decision procedure: a confluent renamed system with a
normal-form normalizer passes the check. Each critical pair is a genuine peak
(`criticalPairs_sound`), so the shared source reaches both normal-form images;
joining those images through `AbsConfluent` and using irreducibility on both ends
forces them to coincide, so the per-pair comparison succeeds. -/
theorem decideConfluence_complete [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} (norm : Normalizer (renameTRS R))
    (hconf : AbsConfluent (Step (renameTRS R))) (hnf : norm.IsNF) :
    decideConfluence R norm = true := by
  rw [decideConfluence, List.all_eq_true]
  intro q hq
  rw [decide_eq_true_eq]
  -- the critical pair is a genuine peak `w -> q.1`, `w -> q.2`
  obtain ⟨w, hw1, hw2⟩ := criticalPairs_sound R hq
  -- both components reach their own normal form
  have hr1 : StepStar (renameTRS R) q.1 (norm.nf q.1) := norm.nf_reach q.1
  have hr2 : StepStar (renameTRS R) q.2 (norm.nf q.2) := norm.nf_reach q.2
  -- from the shared peak `w`, both normal forms are reached
  have hw1' : StepStar (renameTRS R) w (norm.nf q.1) :=
    (StepStar.single hw1).trans hr1
  have hw2' : StepStar (renameTRS R) w (norm.nf q.2) :=
    (StepStar.single hw2).trans hr2
  -- confluence joins the two normal forms; both being irreducible, the join is each
  obtain ⟨d, hd1, hd2⟩ := hconf w (norm.nf q.1) (norm.nf q.2) hw1' hw2'
  have he1 : d = norm.nf q.1 := stepStar_eq_of_nf (hnf q.1) hd1
  have he2 : d = norm.nf q.2 := stepStar_eq_of_nf (hnf q.2) hd2
  rw [← he1, ← he2]

end OperatorKO7.Meta.Rewriting

/-! ## Non-vacuity: a concrete confluent system passes the check

The system has one rule over `Nat`-symbols and `Nat`-variables:

* rule `f(c) -> c`, with `f` the symbol `0` and `c = app 2 []` a constant.

Its only overlap is the rule with a renamed copy of itself at the root, whose
critical pair has identical components `(c, c)`. So the check accepts under any
normalizer; the identity normalizer (each term reaches itself in zero steps) is the
cleanest witness. Under a clean strong-normalization hypothesis the soundness
conclusion gives confluence of the renamed system. -/

namespace OperatorKO7.Meta.Rewriting

namespace Demo

open scoped Subst

/-- The demonstration rule `f(c) -> c`: `f = 0`, `c = app 2 []`. The left-hand side
is an application. -/
def ruleFc : Rule Nat Nat where
  lhs := .app 0 [.app 2 []]
  rhs := .app 2 []
  lhs_isApp := rfl

/-- The one-rule demonstration system `[f(c) -> c]`. -/
def trs : TRS Nat Nat := [ruleFc]

/-- The identity normalizer for the renamed system: each term is its own reduct,
reached in zero steps. A genuine `Normalizer`, with the reachability field
discharged by reflexivity of the closure. -/
def idNormalizer : Normalizer (renameTRS trs) where
  nf := fun t => t
  nf_reach := fun t => StepStar.refl _ t

/-- The check accepts the demonstration system: its single critical pair has
identical components, so the identity normalizer sends each component to a shared
value. The enumeration `criticalPairs trs` and the per-pair comparison are
evaluated through the construction's equation lemmas. -/
theorem decideConfluence_trs_eq_true :
    decideConfluence trs idNormalizer = true := by
  simp [decideConfluence, idNormalizer, criticalPairs, trs, ruleFc, overlapPairs,
    overlapAt, renameRule, Term.rename, Term.renameList, nonVarPositions,
    nonVarPositionsList, Term.subtermAt, unify, solve, zipPairs, Subst.apply,
    Subst.applyList, Term.replaceAt, Term.replaceAtList]

/-- The soundness conclusion applied to the demonstration system: under a clean
strong-normalization hypothesis for the renamed system, the accepted check yields
confluence of `Step (renameTRS trs)`. The strong-normalization witness is taken as
a hypothesis, as the soundness route permits. -/
theorem demo_confluent_of_SN
    (hSN : WellFounded (flip (Step (renameTRS trs)))) :
    AbsConfluent (Step (renameTRS trs)) :=
  decideConfluence_sound decideConfluence_trs_eq_true hSN

end Demo

end OperatorKO7.Meta.Rewriting

/-! ## Verification: headline types and axiom audit -/

open OperatorKO7.Meta.Rewriting in
#check @Normalizer
open OperatorKO7.Meta.Rewriting in
#check @joinable_of_nf_eq
open OperatorKO7.Meta.Rewriting in
#check @decideConfluence
open OperatorKO7.Meta.Rewriting in
#check @cp_joinable_of_decideConfluence
open OperatorKO7.Meta.Rewriting in
#check @decideConfluence_sound
open OperatorKO7.Meta.Rewriting in
#check @Normalizer.IsNF
open OperatorKO7.Meta.Rewriting in
#check @stepStar_eq_of_nf
open OperatorKO7.Meta.Rewriting in
#check @decideConfluence_complete
open OperatorKO7.Meta.Rewriting in
#check @Demo.decideConfluence_trs_eq_true
open OperatorKO7.Meta.Rewriting in
#check @Demo.demo_confluent_of_SN

#print axioms OperatorKO7.Meta.Rewriting.joinable_of_nf_eq
#print axioms OperatorKO7.Meta.Rewriting.cp_joinable_of_decideConfluence
#print axioms OperatorKO7.Meta.Rewriting.decideConfluence_sound
#print axioms OperatorKO7.Meta.Rewriting.stepStar_eq_of_nf
#print axioms OperatorKO7.Meta.Rewriting.decideConfluence_complete
#print axioms OperatorKO7.Meta.Rewriting.Demo.decideConfluence_trs_eq_true
#print axioms OperatorKO7.Meta.Rewriting.Demo.demo_confluent_of_SN
