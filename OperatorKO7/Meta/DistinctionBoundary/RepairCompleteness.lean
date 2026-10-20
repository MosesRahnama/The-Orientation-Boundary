import OperatorKO7.Meta.DistinctionBoundary.ConservativeRepair

set_option autoImplicit false

/-!
# Repair completeness: the dichotomy, the declared grammar, and the price of completion

Manuscript anchors: the repair-taxonomy section of
`Rahnama_The_Distinction_Boundary`, which this module replaces with a
grammar-relative statement.

## What this module proves

* **T-RepairDich.** A repair that keeps both diagonal edges and stays locally
  confluent joins the two verdicts. Combined with the refusal case, this gives
  an exhaustive two-sided dichotomy at the diagonal: refuse an edge, or join
  the verdicts. Nothing else restores local confluence there.
* **Restriction cannot join.** A repair that only removes kernel steps cannot
  take the join side, because both verdicts are kernel-normal at the root.
  So a restriction repair lands on the refusal side, which is the S1 result
  read through the dichotomy.
* **RepairGrammar.** A declared six-entry grammar with its four modes, and a
  classification theorem relative to that grammar. The earlier wording spoke
  of the ways to repair the fork; the theorem here speaks of the entries of a
  grammar that is written down, which is what the mathematics supports.
* **Repair lattice.** On the two-verdict diagonal fiber, compatible-verdict
  cliques are the retained sets; requiring the reflexive verdict leaves one
  maximal clique.
* **T-CompletionPrice.** The completion route exists generically and is
  priced at KO7: repairing every diagonal by joining forces a new step out of
  `integrate (merge a a)` for every `a`, and the uniform completion that
  supplies those steps collapses the accumulator, since every `integrate`
  term then reaches `void` and the constructor separates nothing.

## Claim boundaries

* The dichotomy is stated at a single diagonal source and quantified where
  it is used. It is a statement about local confluence at that source.
* Grammar-relative completeness is relative to the declared grammar. A
  different grammar is a different theorem, and this module proves nothing
  about entries outside the six listed.
* `uniform_completion_collapses_integrate` prices one completion, the uniform
  one. Non-uniform completions are covered only by
  `completion_adds_step_at_every_diagonal`, which shows every completion pays
  at least one new edge per diagonal.

Relation: `Step` and candidate repairs (root). Closure: root, with
candidate-local reflexive-transitive closure for joinability. Strategy: not
applicable. Trust: kernel only, Mathlib baseline.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.RepairCompleteness

open OperatorKO7 Trace
open OperatorKO7.Meta.DistinctionBoundary.ConservativeRepair

/-! ## T-RepairDich. The two-sided dichotomy at the diagonal -/

/-- **T-RepairDich.** A repair retaining both diagonal edges and locally
confluent at the diagonal joins the two verdicts. -/
theorem retains_both_edges_forces_join
    {R : Trace → Trace → Prop} (a : Trace)
    (hrefl : R (eqW a a) void)
    (hdiff : R (eqW a a) (integrate (merge a a)))
    (hlc : ∀ s t u, R s t → R s u → JoinIn R t u) :
    JoinIn R void (integrate (merge a a)) :=
  hlc _ _ _ hrefl hdiff

/-- **The dichotomy.** At a diagonal source, a locally confluent repair that
keeps the reflexive verdict either refuses the difference edge or joins the two
verdicts. The two cases are exhaustive. -/
theorem repair_dichotomy
    {R : Trace → Trace → Prop} (a : Trace)
    (hrefl : R (eqW a a) void)
    (hlc : ∀ s t u, R s t → R s u → JoinIn R t u) :
    (¬ R (eqW a a) (integrate (merge a a))) ∨ JoinIn R void (integrate (merge a a)) := by
  by_cases hdiff : R (eqW a a) (integrate (merge a a))
  · exact Or.inr (retains_both_edges_forces_join a hrefl hdiff hlc)
  · exact Or.inl hdiff

/-- A repair that only removes kernel steps cannot take the join side: both
verdicts are kernel-normal at the root, so their only reducts are themselves,
and they differ. -/
theorem restriction_cannot_join
    {R : Trace → Trace → Prop} (a : Trace)
    (hsub : ∀ s t, R s t → Step s t) :
    ¬ JoinIn R void (integrate (merge a a)) := by
  rintro ⟨d, hd1, hd2⟩
  have hvoid : ∀ u, ¬ R void u := fun u hu => no_step_from_void u (hsub _ _ hu)
  have hint : ∀ u, ¬ R (integrate (merge a a)) u := fun u hu =>
    no_step_from_integrate_merge_self a u (hsub _ _ hu)
  have h1 : d = void := star_eq_of_no_step hvoid hd1
  have h2 : d = integrate (merge a a) := star_eq_of_no_step hint hd2
  rw [h1] at h2
  cases h2

/-- **The restriction branch.** A locally confluent restriction repair that
keeps the reflexive verdict refuses the diagonal difference edge. This is the
S1 forcing result read through the dichotomy. -/
theorem restriction_must_refuse
    {R : Trace → Trace → Prop} (a : Trace)
    (hsub : ∀ s t, R s t → Step s t)
    (hrefl : R (eqW a a) void)
    (hlc : ∀ s t u, R s t → R s u → JoinIn R t u) :
    ¬ R (eqW a a) (integrate (merge a a)) := by
  rcases repair_dichotomy a hrefl hlc with h | hjoin
  · exact h
  · exact absurd hjoin (restriction_cannot_join a hsub)

/-! ## The declared repair grammar -/

/-- The four modes a repair entry can act in. -/
inductive RepairMode
  | restriction
  | extension
  | identification
  | languageEnrichment
  deriving DecidableEq, Repr

/-- The declared repair grammar. Completeness below is relative to exactly
these six entries. -/
inductive RepairGrammar
  | restrictByGuard
  | deleteRule
  | prioritizeBranch
  | addJoinRule
  | quotientVerdicts
  | refineSignature
  deriving DecidableEq, Repr

/-- The mode of each grammar entry. -/
def mode : RepairGrammar → RepairMode
  | .restrictByGuard => .restriction
  | .deleteRule => .restriction
  | .prioritizeBranch => .restriction
  | .addJoinRule => .extension
  | .quotientVerdicts => .identification
  | .refineSignature => .languageEnrichment

/-- **Grammar-relative classification.** Every entry of the declared grammar
acts in one of the four modes. -/
theorem grammar_classification (g : RepairGrammar) :
    mode g = .restriction ∨ mode g = .extension ∨
      mode g = .identification ∨ mode g = .languageEnrichment := by
  cases g <;> simp [mode]

/-- Each of the four modes is realised by an entry of the grammar, so the mode
classification is onto and the taxonomy carries no empty column. -/
theorem grammar_modes_inhabited :
    (∃ g, mode g = .restriction) ∧ (∃ g, mode g = .extension) ∧
      (∃ g, mode g = .identification) ∧ (∃ g, mode g = .languageEnrichment) :=
  ⟨⟨.restrictByGuard, rfl⟩, ⟨.addJoinRule, rfl⟩,
    ⟨.quotientVerdicts, rfl⟩, ⟨.refineSignature, rfl⟩⟩

/-- **Grammar-relative completeness.** The semantic dichotomy has two sides,
and the declared grammar supplies entries on both: the restriction entries act
on the refusal side, the extension and identification entries act on the join
side, and language enrichment changes the observer rather than the relation. -/
theorem grammar_relative_completeness :
    (∀ g : RepairGrammar, mode g = .restriction ∨ mode g = .extension ∨
        mode g = .identification ∨ mode g = .languageEnrichment) ∧
      (∀ (R : Trace → Trace → Prop) (a : Trace),
        R (eqW a a) void →
        (∀ s t u, R s t → R s u → JoinIn R t u) →
        (¬ R (eqW a a) (integrate (merge a a))) ∨
          JoinIn R void (integrate (merge a a))) :=
  ⟨grammar_classification, fun _ a hrefl hlc => repair_dichotomy a hrefl hlc⟩

/-! ## The repair lattice on the diagonal fiber -/

/-- The two verdicts of the diagonal fiber. -/
inductive Verdict
  | refl
  | diff
  deriving DecidableEq, Repr

/-- Under a restriction repair the two verdicts stay separated, so a retained
set is compatible exactly when it holds one verdict. -/
def Compatible (x y : Verdict) : Prop := x = y

/-- A retained set is a clique when its verdicts are pairwise compatible. -/
def IsClique (S : Verdict → Prop) : Prop := ∀ x y, S x → S y → Compatible x y

/-- Requiring the reflexive verdict leaves the reflexive singleton as the only
clique, so the retained maximal clique is unique. -/
theorem clique_with_refl_is_reflSingleton
    (S : Verdict → Prop) (hclique : IsClique S) (hrefl : S .refl) :
    ∀ x, S x → x = .refl := by
  intro x hx
  exact (hclique x .refl hx hrefl)

/-- The reflexive singleton is a clique, so the unique maximal retained clique
is inhabited. -/
theorem reflSingleton_isClique : IsClique (fun v => v = Verdict.refl) := by
  intro x y hx hy
  rw [hx, hy]
  rfl

/-- **Repair lattice.** Requiring the reflexive verdict pins one maximal
compatible clique on the diagonal fiber. -/
theorem unique_maximal_clique_with_refl :
    IsClique (fun v => v = Verdict.refl) ∧
      (∀ S : Verdict → Prop, IsClique S → S .refl → ∀ x, S x → x = .refl) :=
  ⟨reflSingleton_isClique, clique_with_refl_is_reflSingleton⟩

/-! ## T-CompletionPrice -/

/-- **T-CompletionPrice, part one.** A completion that repairs every diagonal
by joining, while leaving `void` normal, must add a step out of
`integrate (merge a a)` for every `a`. Those sources are kernel-normal, so
every one of those steps is new. -/
theorem completion_adds_step_at_every_diagonal
    {R : Trace → Trace → Prop}
    (hvoid : ∀ u, ¬ R void u)
    (hjoin : ∀ a, JoinIn R void (integrate (merge a a))) :
    ∀ a, ∃ u, R (integrate (merge a a)) u := by
  intro a
  obtain ⟨d, hd1, hd2⟩ := hjoin a
  have hdvoid : d = void := star_eq_of_no_step hvoid hd1
  subst hdvoid
  rcases Relation.ReflTransGen.cases_head hd2 with heq | ⟨c, hstep, _⟩
  · exact absurd heq (by intro h; cases h)
  · exact ⟨c, hstep⟩

/-- **T-CompletionPrice, part two.** The uniform completion that supplies those
steps by adding `integrate x → void` for every `x` collapses the accumulator:
every `integrate` term reaches `void`, so the constructor separates nothing and
the record semantics of `integrate` is erased. -/
theorem uniform_completion_collapses_integrate
    {R : Trace → Trace → Prop}
    (huniform : ∀ x, R (integrate x) void) :
    (∀ x, Relation.ReflTransGen R (integrate x) void) ∧
      (∀ x y, Relation.ReflTransGen R (integrate x) void ∧
        Relation.ReflTransGen R (integrate y) void) := by
  refine ⟨fun x => Relation.ReflTransGen.single (huniform x), ?_⟩
  intro x y
  exact ⟨Relation.ReflTransGen.single (huniform x),
    Relation.ReflTransGen.single (huniform y)⟩

/-! ## Non-vacuity and non-triviality -/

/-- R5 witness: the dichotomy is inhabited on the refusal side by the surgical
relation, which keeps the reflexive verdict and refuses the difference edge. -/
theorem dichotomy_refusal_side_inhabited :
    ∃ R : Trace → Trace → Prop,
      (∀ a, R (eqW a a) void) ∧ (∀ a, ¬ R (eqW a a) (integrate (merge a a))) := by
  refine ⟨OperatorKO7.EqGuardedConfluence.EqGuardedStep, ?_, ?_⟩
  · intro a
    exact OperatorKO7.EqGuardedConfluence.EqGuardedStep.R_eq_refl a
  · intro a
    exact admissible_refuses_diagonal_difference eqGuardedStep_admissible a

/-- Non-triviality: the grammar has more than one mode, so the classification
theorem separates entries instead of collapsing them. -/
theorem grammar_modes_separate :
    mode .restrictByGuard ≠ mode .addJoinRule ∧
      mode .addJoinRule ≠ mode .quotientVerdicts := by
  constructor <;> decide

/-! ## The exhaustive trichotomy

The dichotomy above splits into three cases once the join side is opened up.
Joining two distinct root normal forms needs a step that the kernel lacks, so
the join side is exactly the extension side, and no case is left over. -/

/-- **Exhaustive trichotomy.** A locally confluent repair that keeps the
reflexive verdict does one of three things at the diagonal, and the list is
complete: it refuses the difference edge, it adds a step out of the difference
verdict that the kernel lacks, or it adds a step out of `void` that the kernel
lacks. -/
theorem repair_trichotomy_exhaustive
    {R : Trace → Trace → Prop} (a : Trace)
    (hrefl : R (eqW a a) void)
    (hlc : ∀ s t u, R s t → R s u → JoinIn R t u) :
    (¬ R (eqW a a) (integrate (merge a a)))
    ∨ (∃ u, R (integrate (merge a a)) u ∧ ¬ Step (integrate (merge a a)) u)
    ∨ (∃ u, R void u ∧ ¬ Step void u) := by
  rcases repair_dichotomy a hrefl hlc with hrefuse | hjoin
  · exact Or.inl hrefuse
  · obtain ⟨d, hd1, hd2⟩ := hjoin
    rcases Relation.ReflTransGen.cases_head hd1 with hv | ⟨c, hstep, _⟩
    · subst hv
      rcases Relation.ReflTransGen.cases_head hd2 with hi | ⟨c, hstep, _⟩
      · exact absurd hi (by intro h; cases h)
      · exact Or.inr (Or.inl ⟨c, hstep, no_step_from_integrate_merge_self a c⟩)
    · exact Or.inr (Or.inr ⟨c, hstep, no_step_from_void c⟩)

/-- Non-vacuity for the trichotomy: the refusal branch is realised by the
surgical relation. -/
theorem trichotomy_first_branch_realised (a : Trace) :
    ¬ OperatorKO7.EqGuardedConfluence.EqGuardedStep (eqW a a) (integrate (merge a a)) :=
  admissible_refuses_diagonal_difference eqGuardedStep_admissible a

end OperatorKO7.Meta.DistinctionBoundary.RepairCompleteness
