import OperatorKO7.Meta.UniqueNormalization.Section7SimultaneousClosure

/-!
# Reach gate for Section 7 simultaneous closure
-/

#check @List.Forall₂Marked
#check @OperatorKO7.Meta.UniqueNormalization.constructorShape
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorShape
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.seed
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.seed
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.refl
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.symm
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.trans
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.trans
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.argument
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.argument
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorClash
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorClash
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorCompatible.shape_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorCompatible.shape_eq
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorCompatible.argument
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorCompatible.argument
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorCompatible.no_clash
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorCompatible.no_clash
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.equivalence
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.equivalence
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.least
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.least
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.mono
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.idempotent
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.idempotent
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.compatible_of_no_clash
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.compatible_of_no_clash
#check @OperatorKO7.Meta.UniqueNormalization.exists_constructorCompatible_equivalence_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.exists_constructorCompatible_equivalence_iff
#check @OperatorKO7.Meta.UniqueNormalization.no_constructorCompatible_equivalence_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.no_constructorCompatible_equivalence_iff
#check @OperatorKO7.Meta.UniqueNormalization.equationListRel
#print axioms OperatorKO7.Meta.UniqueNormalization.equationListRel
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.finite_support
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorEqClosure.finite_support
#check @OperatorKO7.Meta.UniqueNormalization.constructorClash_iff_finite_seed
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorClash_iff_finite_seed
#check @OperatorKO7.Meta.UniqueNormalization.constructorCompatible_equivalence_finite_character
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorCompatible_equivalence_finite_character
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.ReplacementAmbient
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.ReplacementAmbient
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.replacementAmbient_iff_no_clash
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.replacementAmbient_iff_no_clash
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.replacementAmbient_finite_character
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.replacementAmbient_finite_character
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.replacementAmbient_or_finite_clash
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.replacementAmbient_or_finite_clash
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.ReplacementForkSound
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.ReplacementForkSound
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.translated_replacementSeed_fork_sound_of_ambient
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.translated_replacementSeed_fork_sound_of_ambient
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.translated_replacementSeed_fork_sound_of_no_clash
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.translated_replacementSeed_fork_sound_of_no_clash
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.translated_replacementSeed_fork_sound_of_finite_ambients
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.translated_replacementSeed_fork_sound_of_finite_ambients
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.translated_replacement_forkSound_or_finite_clash
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.translated_replacement_forkSound_or_finite_clash

namespace ConstructorClosureTests

open OperatorKO7.Meta.UniqueNormalization OperatorKO7.Meta.Rewriting

/-- Even an infinite term carrier has a compatible equivalence for the empty seed. -/
example : ∃ E : CRel Nat Nat, Equivalence E ∧ ConstructorCompatible E ∧
    ∀ a b, False → E a b := by
  refine ⟨(Eq : CRel Nat Nat), ⟨fun _ => rfl, Eq.symm, Eq.trans⟩, ?_, ?_⟩
  · intro a b ha _ hab
    subst b
    rcases ha with ⟨x, rfl⟩ | ⟨f, xs, rfl⟩
    · exact Or.inl ⟨x, rfl, rfl⟩
    · exact Or.inr ⟨f, xs, xs, rfl, rfl, forall₂_self (fun _ => rfl) xs⟩
  · intro a b h
    exact False.elim h

/-- Distinct variables form a recorded obstruction. -/
example : ConstructorClash (ConstructorEqClosure
    (equationListRel [(Term.var (sigma := Nat ⊕ Nat) 0, Term.var 1)])) := by
  exact ⟨.var 0, .var 1, ConTopped.var 0, ConTopped.var 1,
    .seed (List.mem_singleton_self _), by decide⟩

/-- Variable/constructor pairs form a recorded obstruction. -/
example : ConstructorClash (ConstructorEqClosure
    (equationListRel [(Term.var (sigma := Nat ⊕ Nat) 0, Term.app (.inl 0) [])])) := by
  exact ⟨.var 0, .app (.inl 0) [], ConTopped.var 0, ConTopped.app 0 [],
    .seed (List.mem_singleton_self _), by decide⟩

/-- Constructor symbol mismatches form a recorded obstruction. -/
example : ConstructorClash (ConstructorEqClosure (equationListRel
    [(Term.app (nu := Nat) (Sum.inl (β := Nat) 0) [], Term.app (.inl 1) [])])) := by
  exact ⟨.app (.inl 0) [], .app (.inl 1) [], ConTopped.app 0 [], ConTopped.app 1 [],
    .seed (List.mem_singleton_self _), by decide⟩

/-- Equal constructor symbols with unequal arities still form an obstruction. -/
example : ConstructorClash (ConstructorEqClosure (equationListRel
    [(Term.app (nu := Nat) (Sum.inl (β := Nat) 0) [], Term.app (.inl 0) [.var 0])])) := by
  exact ⟨.app (.inl 0) [], .app (.inl 0) [.var 0],
    ConTopped.app 0 [], ConTopped.app 0 [.var 0],
    .seed (List.mem_singleton_self _), by decide⟩

/-- Three seed equations force an argument equation not required by any one edge. -/
example {S : CRel Nat Nat} {u v p q : Term (Nat ⊕ Nat) Nat}
    (h₁ : S (.app (.inl 0) [u]) p) (h₂ : S p q)
    (h₃ : S q (.app (.inl 0) [v])) : ConstructorEqClosure S u v := by
  exact ConstructorEqClosure.argument
    (.trans (.seed h₁) (.trans (.seed h₂) (.seed h₃))) 0 (by simp) (by simp)

/-- An actual singleton proof graph has a replacement ambient on the full,
infinite translated-term carrier. -/
example :
    let c : Term (Nat ⊕ Nat) Nat := .app (.inl 0) []
    let rho := PGraph.empty [c] ([] : TRS (Nat ⊕ Nat) Nat)
    rho.ReplacementAmbient c c := by
  dsimp only
  refine ⟨(Eq : CRel Nat Nat), ⟨fun _ => rfl, Eq.symm, Eq.trans⟩, ?_, ?_⟩
  · intro a b ha _ hab
    subst b
    rcases ha with ⟨x, rfl⟩ | ⟨f, xs, rfl⟩
    · exact Or.inl ⟨x, rfl, rfl⟩
    · exact Or.inr ⟨f, xs, xs, rfl, rfl, forall₂_self (fun _ => rfl) xs⟩
  · intro x y hxy
    rcases hxy with hold | hnew
    · have hx : x = Term.app (.inl 0) [] := by simpa using hold.mem.1
      have hy : y = Term.app (.inl 0) [] := by simpa using hold.mem.2
      exact hx.trans hy.symm
    · have hx : x = Term.app (.inl 0) [] := by simpa using hnew.mem.1
      have hy : y = Term.app (.inl 0) [] := by simpa using hnew.mem.2
      exact hx.trans hy.symm

end ConstructorClosureTests

#check @List.Forall₂Marked.head
#check @List.Forall₂Marked.tail
#check @List.Forall₂Marked.toForall₂
#check @List.Forall₂Marked.exists_split

#check @OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence
#check @OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence.here
#check @OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence.symm
#check @OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence.rootTail
#check @OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence.barCompArg
#check @OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence.barCompTail
#check @OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence.tildeArg
#check @OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence.toDownOn
#check @OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence.rootWitness
#check @OperatorKO7.Meta.UniqueNormalization.DownOn.exists_occurring_missing_rootStep_of_sigmaClosedOn
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.missing_downOn_has_occurring_missing_rootStep
#check @OperatorKO7.Meta.UniqueNormalization.RootFailure
#check @OperatorKO7.Meta.UniqueNormalization.MissingRootArgumentDependency
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.rootFailure_has_dependency
#check @OperatorKO7.Meta.UniqueNormalization.missingRootPairs
#check @OperatorKO7.Meta.UniqueNormalization.mem_missingRootPairs_iff
#check @OperatorKO7.Meta.UniqueNormalization.missingRootPairs_eq_empty_iff_rootStepsRepresented
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.missingRootPairs_dependency_total
#check @OperatorKO7.Meta.UniqueNormalization.iterate_transGen_of_lt
#check @OperatorKO7.Meta.UniqueNormalization.finite_total_relation_has_transGen_cycle
#check @OperatorKO7.Meta.UniqueNormalization.MissingRootNode
#check @OperatorKO7.Meta.UniqueNormalization.MissingRootDependency
#check @OperatorKO7.Meta.UniqueNormalization.HasMissingRootDependencyCycle
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.missingRootDependency_total
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.hasMissingRootDependencyCycle_of_nonempty
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.not_rootStepsRepresented_iff_dependencyCycle
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.rootStepsRepresented_or_dependencyCycle

#print axioms List.Forall₂Marked
#print axioms List.Forall₂Marked.head
#print axioms List.Forall₂Marked.tail
#print axioms List.Forall₂Marked.toForall₂
#print axioms List.Forall₂Marked.exists_split

#print axioms OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence
#print axioms OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence.here
#print axioms OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence.rootTail
#print axioms OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence.barCompArg
#print axioms OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence.barCompTail
#print axioms OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence.tildeArg
#print axioms OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence.toDownOn
#print axioms OperatorKO7.Meta.UniqueNormalization.DownRootOccurrence.rootWitness
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.exists_occurring_missing_rootStep_of_sigmaClosedOn
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.missing_downOn_has_occurring_missing_rootStep
#print axioms OperatorKO7.Meta.UniqueNormalization.RootFailure
#print axioms OperatorKO7.Meta.UniqueNormalization.MissingRootArgumentDependency
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.rootFailure_has_dependency
#print axioms OperatorKO7.Meta.UniqueNormalization.missingRootPairs
#print axioms OperatorKO7.Meta.UniqueNormalization.mem_missingRootPairs_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.missingRootPairs_eq_empty_iff_rootStepsRepresented
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.missingRootPairs_dependency_total
#print axioms OperatorKO7.Meta.UniqueNormalization.iterate_transGen_of_lt
#print axioms OperatorKO7.Meta.UniqueNormalization.finite_total_relation_has_transGen_cycle
#print axioms OperatorKO7.Meta.UniqueNormalization.MissingRootNode
#print axioms OperatorKO7.Meta.UniqueNormalization.MissingRootDependency
#print axioms OperatorKO7.Meta.UniqueNormalization.HasMissingRootDependencyCycle
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.missingRootDependency_total
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.hasMissingRootDependencyCycle_of_nonempty
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.not_rootStepsRepresented_iff_dependencyCycle
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.rootStepsRepresented_or_dependencyCycle

#check @OperatorKO7.Meta.UniqueNormalization.PGraph.replacement_terminating
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.replacement_mem
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.replacement_greyOld
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.replacement_sound
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.ReplacementSeed
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.replacementSeed_sound
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.replacementSeed_new
#check @OperatorKO7.Meta.UniqueNormalization.CT.downOn_of_sound_base
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.of_contextGeneratedConstructorSlice
#check @OperatorKO7.Meta.UniqueNormalization.EqvOn.exists_reachable_constructor_outside_contextClosure
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.replacementSeed_context_sound
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.replacement_preserves_iff_displaced_edge
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.replacement_recovers_roots

#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.replacement_terminating
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.replacement_mem
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.replacement_greyOld
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.replacement_sound
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.ReplacementSeed
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.replacementSeed_sound
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.replacementSeed_new
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.downOn_of_sound_base
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.of_contextGeneratedConstructorSlice
#print axioms OperatorKO7.Meta.UniqueNormalization.EqvOn.exists_reachable_constructor_outside_contextClosure
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.replacementSeed_context_sound
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.replacement_preserves_iff_displaced_edge
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.replacement_recovers_roots

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

/-- The occurrence carrier is inhabited by the actual d(c) to c root step. -/
example : DownRootOccurrence Section7Active.terms Section7Active.rules
    Section7Active.once Section7Active.constant
    Section7Active.once Section7Active.constant := by
  exact DownRootOccurrence.here
    ((Section7Active.mem_terms _).2 (Or.inr (Or.inl rfl)))
    ((Section7Active.mem_terms _).2 (Or.inr (Or.inr rfl)))
    Section7Active.root_once
    (DownOn.refl ((Section7Active.mem_terms _).2 (Or.inr (Or.inr rfl))))

/-- The marked occurrence survives one enclosing destructor congruence. -/
example : DownRootOccurrence Section7Active.terms Section7Active.rules
    Section7Active.once Section7Active.constant
    Section7Active.twice Section7Active.once := by
  have hocc : DownRootOccurrence Section7Active.terms Section7Active.rules
      Section7Active.once Section7Active.constant
      Section7Active.once Section7Active.constant :=
    DownRootOccurrence.here
      ((Section7Active.mem_terms _).2 (Or.inr (Or.inl rfl)))
      ((Section7Active.mem_terms _).2 (Or.inr (Or.inr rfl)))
      Section7Active.root_once
      (DownOn.refl ((Section7Active.mem_terms _).2 (Or.inr (Or.inr rfl))))
  simpa [Section7Active.twice, Section7Active.once, Section7Active.wrap] using
    (DownRootOccurrence.tildeArg
      (p := Section7Active.once) (q := Section7Active.constant)
      (f := Sum.inr ()) (xp := []) (yp := [])
      (x := Section7Active.once) (y := Section7Active.constant)
      (xt := []) (yt := [])
      ((Section7Active.mem_terms _).2 (Or.inl rfl))
      ((Section7Active.mem_terms _).2 (Or.inr (Or.inl rfl)))
      List.Forall₂.nil Section7Active.down_once_constant hocc List.Forall₂.nil)

/-- A purported occurrence cannot certify a pair that is not a root rewrite. -/
example : ¬ DownRootOccurrence Section7Active.terms Section7Active.rules
    Section7Active.constant Section7Active.once
    Section7Active.once Section7Active.constant := by
  intro h
  have hroot := h.rootWitness.2.2
  have heq := (Section7Active.rootStep_iff _ _).mp hroot
  simp [Section7Active.constant, Section7Active.once, Section7Active.wrap] at heq

/-- The generic finite-cycle theorem is nonvacuous on the Boolean two-cycle. -/
example : ∃ b : Bool,
    Relation.TransGen (fun x y : Bool => y = !x) b b := by
  apply finite_total_relation_has_transGen_cycle
  intro b
  exact ⟨!b, rfl⟩

namespace Section7ReplacementControl

open Section7Active

/-- The changed node has an old parent and a missing root equation. -/
theorem replacement_at_non_normal_form :
    Trap.graph.par once = some twice ∧
      ¬ EqvOn terms Trap.graph.par once constant ∧
      Terminating (extendPar Trap.graph.par once constant) ∧
      DownOn terms rules once constant := by
  have ho : once ∈ terms := (mem_terms _).mpr (Or.inr (Or.inl rfl))
  have hc : constant ∈ terms := (mem_terms _).mpr (Or.inr (Or.inr rfl))
  have hn := Trap.once_not_eqv_constant
  refine ⟨by simp [Trap.graph, Trap.parent], hn,
    Trap.graph.replacement_terminating ho hc hn, ?_⟩
  exact Trap.graph.replacementSeed_sound terms_coalgebra rules_constructor
    ho hc hn (Or.inl root_once) (Trap.graph.replacementSeed_new ho hc)

/-- The temporary forest alone loses the displaced equation. -/
theorem replacement_loses_displaced_equation :
    EqvOn terms Trap.graph.par once twice ∧
      ¬ EqvOn terms (extendPar Trap.graph.par once constant) once twice := by
  have ho : once ∈ terms := (mem_terms _).mpr (Or.inr (Or.inl rfl))
  have ht : twice ∈ terms := (mem_terms _).mpr (Or.inl rfl)
  refine ⟨EqvOn.of_reach ho ht (Reach.head
    (show Trap.graph.par once = some twice from by simp [Trap.graph, Trap.parent])
    (Reach.refl twice)), ?_⟩
  rintro ⟨_, _, s, hos, hts⟩
  have hts' : twice = s := Trap.reach_eq_of_no_parent
    (by simp [extendPar, Trap.graph, Trap.parent]) hts
  subst s
  rcases hos.head_inv with heq | ⟨c, hoc, hct⟩
  · exact twice_ne_once heq.symm
  · have hc : constant = c := Option.some.inj
      ((extendPar_self Trap.graph.par once constant).symm.trans hoc)
    subst c
    have hct' : constant = twice := Trap.reach_eq_of_no_parent
      (by simp [extendPar, Trap.graph, Trap.parent, Ne.symm once_ne_constant]) hct
    exact twice_ne_constant hct'.symm

/-- The repaired two-edge parent map recovers the displaced equation and all
old equalities while retaining the requested new equation. -/
theorem repaired_parent_recovers_old_and_new :
    (∀ {x y}, EqvOn terms Trap.graph.par x y → EqvOn terms graph.par x y) ∧
      EqvOn terms graph.par once constant := by
  have hnew : ∀ {x y}, extendPar Trap.graph.par once constant x = some y →
      EqvOn terms graph.par x y := by
    intro x y hxy
    have hmem := Trap.graph.replacement_mem
      ((mem_terms _).mpr (Or.inr (Or.inl rfl)))
      ((mem_terms _).mpr (Or.inr (Or.inr rfl))) hxy
    exact ⟨hmem.1, hmem.2, constant, reach_constant hmem.1, reach_constant hmem.2⟩
  refine ⟨(Trap.graph.replacement_preserves_iff_displaced_edge
    once constant hnew).mpr ?_, hnew (extendPar_self _ once constant)⟩
  intro c hoc
  change Trap.parent once = some c at hoc
  have hc : c = twice := (Trap.parent_edge (a := once) (b := c) hoc).2
  subst c
  exact ⟨(mem_terms _).mpr (Or.inr (Or.inl rfl)),
    (mem_terms _).mpr (Or.inl rfl), constant,
    reach_constant ((mem_terms _).mpr (Or.inr (Or.inl rfl))),
    reach_constant ((mem_terms _).mpr (Or.inl rfl))⟩

end Section7ReplacementControl

#check @PGraph.replacementSeed_constructor_decomposition
#print axioms PGraph.replacementSeed_constructor_decomposition
#check @PGraph.replacementSeed_constructorCompatible
#print axioms PGraph.replacementSeed_constructorCompatible
#check @PGraph.replacementSeed_context_constructorCompatible
#print axioms PGraph.replacementSeed_context_constructorCompatible
#check @PGraph.translated_replacementSeed_fork_sound
#print axioms PGraph.translated_replacementSeed_fork_sound

/-- Compatibility applies to the actual replacement at a non-root node. -/
example : ConstructorCompatible
    (Section7Active.Trap.graph.ReplacementSeed Section7Active.once Section7Active.constant) := by
  apply Section7Active.Trap.graph.replacementSeed_constructorCompatible
    Section7Active.terms_coalgebra Section7Active.rules_constructor
  · exact (Section7Active.mem_terms _).mpr (Or.inr (Or.inl rfl))
  · exact (Section7Active.mem_terms _).mpr (Or.inr (Or.inr rfl))
  · exact Section7Active.Trap.once_not_eqv_constant
  · exact Or.inl Section7Active.root_once

/-- The compatible seed is not transitive on its concrete three-term carrier. -/
example : ¬ (∀ x y z, Section7Active.Trap.graph.ReplacementSeed
    Section7Active.once Section7Active.constant x y →
    Section7Active.Trap.graph.ReplacementSeed Section7Active.once Section7Active.constant y z →
    Section7Active.Trap.graph.ReplacementSeed Section7Active.once Section7Active.constant x z) := by
  intro htrans
  have ho : Section7Active.once ∈ Section7Active.terms :=
    (Section7Active.mem_terms _).mpr (Or.inr (Or.inl rfl))
  have hc : Section7Active.constant ∈ Section7Active.terms :=
    (Section7Active.mem_terms _).mpr (Or.inr (Or.inr rfl))
  have hold := Section7ReplacementControl.replacement_loses_displaced_equation.1
  have hbad := htrans Section7Active.twice Section7Active.once Section7Active.constant
    (Or.inl (EqvOn.symm hold))
    (Section7Active.Trap.graph.replacementSeed_new ho hc)
  rcases hbad with hOld | hNew
  · exact Section7Active.Trap.once_not_eqv_constant (EqvOn.trans hold hOld)
  · obtain ⟨_, _, s, hts, hcs⟩ := hNew
    have htp : extendPar Section7Active.Trap.graph.par Section7Active.once
        Section7Active.constant Section7Active.twice = none := by
      simp [extendPar, Section7Active.Trap.graph, Section7Active.Trap.parent]
    have hcp : extendPar Section7Active.Trap.graph.par Section7Active.once
        Section7Active.constant Section7Active.constant = none := by
      simp [extendPar, Section7Active.Trap.graph, Section7Active.Trap.parent,
        Ne.symm Section7Active.once_ne_constant]
    exact Section7Active.twice_ne_constant
      ((Section7Active.Trap.reach_eq_of_no_parent htp hts).trans
        (Section7Active.Trap.reach_eq_of_no_parent hcp hcs).symm)

#check @Section7ReplacementControl.replacement_at_non_normal_form
#check @Section7ReplacementControl.replacement_loses_displaced_equation
#check @Section7ReplacementControl.repaired_parent_recovers_old_and_new
#print axioms Section7ReplacementControl.replacement_at_non_normal_form
#print axioms Section7ReplacementControl.replacement_loses_displaced_equation
#print axioms Section7ReplacementControl.repaired_parent_recovers_old_and_new

#check @omegaUnifiable_of_constructor_bar
#print axioms omegaUnifiable_of_constructor_bar
#check @variables_related_of_constructor_bar
#print axioms variables_related_of_constructor_bar
#check @destructorLabel_instances_residual
#print axioms destructorLabel_instances_residual
#check @patternRule_instances_hat
#print axioms patternRule_instances_hat
#check @translated_semantic_fork_residual
#print axioms translated_semantic_fork_residual
#check @translated_semantic_fork_destructor_residual
#print axioms translated_semantic_fork_destructor_residual
#check @translated_semantic_fork_context
#print axioms translated_semantic_fork_context
#check @constructorTranslation_consistencyInvariant
#print axioms constructorTranslation_consistencyInvariant
#check @constructorTranslation_deterministic
#print axioms constructorTranslation_deterministic
#check @constructorTranslation_almost
#print axioms constructorTranslation_almost
#check @PGraph.MissingOld
#print axioms PGraph.MissingOld
#check @PGraph.ResidualOld
#print axioms PGraph.ResidualOld
#check @PGraph.ResidualPair
#print axioms PGraph.ResidualPair
#check @PGraph.residualCarrierCard
#print axioms PGraph.residualCarrierCard
#check @PGraph.residualPairUniverse
#print axioms PGraph.residualPairUniverse
#check @PGraph.mem_residualPairUniverse_iff
#print axioms PGraph.mem_residualPairUniverse_iff
#check @PGraph.card_residualPairUniverse
#print axioms PGraph.card_residualPairUniverse
#check @PGraph.residualSuccSet
#print axioms PGraph.residualSuccSet
#check @PGraph.residualIter
#print axioms PGraph.residualIter
#check @PGraph.mem_residualSuccSet_iff
#print axioms PGraph.mem_residualSuccSet_iff
#check @PGraph.residualIter_mono_succ
#print axioms PGraph.residualIter_mono_succ
#check @PGraph.residualIter_mono
#print axioms PGraph.residualIter_mono
#check @PGraph.residualIter_subset_pairUniverse
#print axioms PGraph.residualIter_subset_pairUniverse
#check @PGraph.residualIter_all_missing
#print axioms PGraph.residualIter_all_missing
#check @PGraph.residualIter_eq_succ_of_eq_succ_at
#print axioms PGraph.residualIter_eq_succ_of_eq_succ_at
#check @PGraph.residualIter_eq_succ_of_eq_succ_of_le
#print axioms PGraph.residualIter_eq_succ_of_eq_succ_of_le
#check @PGraph.card_residualIter_ge_of_strict_prefix
#print axioms PGraph.card_residualIter_ge_of_strict_prefix
#check @PGraph.residualIter_stabilizes_at_pairUniverse_card
#print axioms PGraph.residualIter_stabilizes_at_pairUniverse_card
#check @PGraph.oldResidualBatch
#print axioms PGraph.oldResidualBatch
#check @PGraph.oldResidualBatch_seed
#print axioms PGraph.oldResidualBatch_seed
#check @PGraph.oldResidualBatch_all_missing
#print axioms PGraph.oldResidualBatch_all_missing
#check @PGraph.oldResidualBatch_closed
#print axioms PGraph.oldResidualBatch_closed
#check @PGraph.oldResidualBatch_least
#print axioms PGraph.oldResidualBatch_least
#check @PGraph.residualSuccSet_oldResidualBatch
#print axioms PGraph.residualSuccSet_oldResidualBatch
#check @PGraph.oldResidualBatch_card_le
#print axioms PGraph.oldResidualBatch_card_le
#check @PGraph.ResidualBatchSpec
#print axioms PGraph.ResidualBatchSpec
#check @PGraph.old_residual_batch_spec
#print axioms PGraph.old_residual_batch_spec
#check @PGraph.missingOld_downOn
#print axioms PGraph.missingOld_downOn
#check @PGraph.ResidualBatchSeed
#print axioms PGraph.ResidualBatchSeed
#check @PGraph.residualBatchSeed_old
#print axioms PGraph.residualBatchSeed_old
#check @PGraph.residualBatchSeed_pair
#print axioms PGraph.residualBatchSeed_pair
#check @PGraph.residualBatchSeed_pair_symm
#print axioms PGraph.residualBatchSeed_pair_symm
#check @PGraph.residualBatchSeed_symm
#print axioms PGraph.residualBatchSeed_symm
#check @PGraph.ResidualBatchSpec.residualBatchSeed_mem
#print axioms PGraph.ResidualBatchSpec.residualBatchSeed_mem
#check @PGraph.ResidualBatchSpec.residualBatchSeed_sound
#print axioms PGraph.ResidualBatchSpec.residualBatchSeed_sound
#check @PGraph.ResidualBatchSpec.residualBatchContext_sound
#print axioms PGraph.ResidualBatchSpec.residualBatchContext_sound
#check @PGraph.residualBatchContext_of_old
#print axioms PGraph.residualBatchContext_of_old
#check @PGraph.residualBatchContext_pair
#print axioms PGraph.residualBatchContext_pair
#check @PGraph.ResidualBatchSpec.residual_contracta_supported
#print axioms PGraph.ResidualBatchSpec.residual_contracta_supported
#check @PGraph.oldResidualBatch_semantic_support
#print axioms PGraph.oldResidualBatch_semantic_support
#check @PGraph.residualBatchContext_iff_old
#print axioms PGraph.residualBatchContext_iff_old
#check @PGraph.residualBatchContext_eq_old
#print axioms PGraph.residualBatchContext_eq_old
#check @RootPeelPath
#print axioms RootPeelPath
#check @RootPeelPath.refl
#print axioms RootPeelPath.refl
#check @RootPeelPath.head
#print axioms RootPeelPath.head
#check @RootPeelPath.mem_left
#print axioms RootPeelPath.mem_left
#check @RootPeelPath.mem_right
#print axioms RootPeelPath.mem_right
#check @RootPeelPath.trans
#print axioms RootPeelPath.trans
#check @RootPeelPath.downOn_comp
#print axioms RootPeelPath.downOn_comp
#check @RootPeelPath.toDownOn
#print axioms RootPeelPath.toDownOn
#check @RootPeeledSeed
#print axioms RootPeeledSeed
#check @RootPeeledSeed.mem
#print axioms RootPeeledSeed.mem
#check @RootPeeledSeed.of_context
#print axioms RootPeeledSeed.of_context
#check @RootPeeledSeed.symm
#print axioms RootPeeledSeed.symm
#check @RootPeeledSeed.root_left
#print axioms RootPeeledSeed.root_left
#check @RootPeeledSeed.root_right
#print axioms RootPeeledSeed.root_right
#check @RootPeeledSeed.sound
#print axioms RootPeeledSeed.sound
#check @RootPeeledSeed.context_sound
#print axioms RootPeeledSeed.context_sound
#check @PGraph.of_rootPeeledConstructorArguments
#print axioms PGraph.of_rootPeeledConstructorArguments
#check @PGraph.ResidualBatchSpec.rootPeeledBatchSeed_sound
#print axioms PGraph.ResidualBatchSpec.rootPeeledBatchSeed_sound
#check @PGraph.ResidualBatchSpec.rootPeeledBatchContext_sound
#print axioms PGraph.ResidualBatchSpec.rootPeeledBatchContext_sound
#check @PGraph.ResidualBatchNode
#print axioms PGraph.ResidualBatchNode
#check @PGraph.ResidualBatchEdge
#print axioms PGraph.ResidualBatchEdge
#check @PGraph.HasResidualOldCycle
#print axioms PGraph.HasResidualOldCycle
#check @PGraph.TightEqualityComplete.translated_missing_barRel_has_root_residual
#print axioms PGraph.TightEqualityComplete.translated_missing_barRel_has_root_residual
#check @PGraph.TightEqualityComplete.translated_residualOld_total
#print axioms PGraph.TightEqualityComplete.translated_residualOld_total
#check @PGraph.TightEqualityComplete.translated_residualBatchEdge_total
#print axioms PGraph.TightEqualityComplete.translated_residualBatchEdge_total
#check @PGraph.TightEqualityComplete.translated_missingOld_has_residualCycle
#print axioms PGraph.TightEqualityComplete.translated_missingOld_has_residualCycle
#check @exists_equalityComplete_rootStepsRepresented_constructorTranslation
#print axioms exists_equalityComplete_rootStepsRepresented_constructorTranslation
#check @PGraph.TightEqualityComplete.translated_missing_fork_destructor
#print axioms PGraph.TightEqualityComplete.translated_missing_fork_destructor
#check @PGraph.TightEqualityComplete.translated_fork_constructor_eqv
#print axioms PGraph.TightEqualityComplete.translated_fork_constructor_eqv
#check @PGraph.translated_semantic_fork_eqv_or_grey
#print axioms PGraph.translated_semantic_fork_eqv_or_grey

namespace TranslatedResidualControl

/-- A nonempty rule set over one variable; no infinite-variable instance exists. -/
def groundRule : Rule Nat PUnit := ⟨.app 0 [], .app 1 [], rfl⟩

theorem ground_nonoverlap : NonOmegaOverlapping [groundRule] := by
  intro r hr r' hr' s hsub _ _
  have heq : r = groundRule := by simpa using hr
  have heq' : r' = groundRule := by simpa using hr'
  subst r
  subst r'
  refine ⟨rfl, ?_⟩
  change Subterm s (Term.app 0 []) at hsub
  cases hsub with
  | refl => rfl
  | arg hmem _ => simp at hmem

theorem ground_rhsDetermined : TRS.RhsDetermined [groundRule] := by
  intro r hr
  have heq : r = groundRule := by simpa using hr
  subst r
  apply determinedBy_of_occurs_subset
  intro x hx
  change VarOccurs x (Term.app 1 []) at hx
  obtain ⟨q, hq, _⟩ := hx.app_inv
  simp at hq

theorem finite_variable_invariant :
    ConsistencyInvariant (constructorTranslation [groundRule])
      (Down (constructorTranslation [groundRule])) :=
  constructorTranslation_consistencyInvariant ground_nonoverlap ground_rhsDetermined

end TranslatedResidualControl

example : Deterministic (constructorTranslation [TranslatedResidualControl.groundRule]) :=
  constructorTranslation_deterministic TranslatedResidualControl.ground_nonoverlap
    TranslatedResidualControl.ground_rhsDetermined

example : AlmostNonOmegaOverlapping
    (constructorTranslation [TranslatedResidualControl.groundRule]) :=
  constructorTranslation_almost TranslatedResidualControl.ground_nonoverlap
    TranslatedResidualControl.ground_rhsDetermined

example :
    ∃ rho : PGraph (coalgebraOf
      [Term.app (.inr 0) [], Term.app (.inr 1) []])
      (constructorTranslation [TranslatedResidualControl.groundRule]),
      rho.EqualityComplete ∧ RootStepsRepresented _ _ rho :=
  exists_equalityComplete_rootStepsRepresented_constructorTranslation
    (coalgebra_coalgebraOf _) TranslatedResidualControl.ground_nonoverlap
    TranslatedResidualControl.ground_rhsDetermined

#check @TranslatedResidualControl.groundRule
#print axioms TranslatedResidualControl.groundRule
#check @TranslatedResidualControl.ground_nonoverlap
#print axioms TranslatedResidualControl.ground_nonoverlap
#check @TranslatedResidualControl.ground_rhsDetermined
#print axioms TranslatedResidualControl.ground_rhsDetermined
#check @TranslatedResidualControl.finite_variable_invariant
#print axioms TranslatedResidualControl.finite_variable_invariant

/-- The translated finite-variable example has a nonidentity root rewrite. -/
example : rootStep (constructorTranslation [TranslatedResidualControl.groundRule])
    (Term.app (.inr 0) [] : Term (Nat ⊕ Nat) PUnit) (.app (.inr 1) []) := by
  exact ⟨transRule TranslatedResidualControl.groundRule,
    transRule_mem (List.mem_singleton_self _), (fun x => .var x), rfl, rfl⟩

/-- Distinct marker patterns over one variable retain their related output
arguments without constructing a two-variable generalisation. -/
example :
    hatRel (fun (a b : Term (Nat ⊕ Nat) PUnit) => a = b)
      (Subst.apply (fun _ => Term.app (.inl 0) [])
        (patternRuleOf (2, [Term.var PUnit.unit, Term.app 0 []])).rhs)
      (Subst.apply (fun _ => Term.app (.inl 0) [])
        (patternRuleOf (2, [Term.app 0 [], Term.var PUnit.unit])).rhs) := by
  apply patternRule_instances_hat
  exact ⟨.inr 2, [.app (.inl 0) [], .app (.inl 0) []],
    [.app (.inl 0) [], .app (.inl 0) []], ⟨2, rfl⟩, rfl, rfl,
    List.Forall₂.cons rfl (List.Forall₂.cons rfl List.Forall₂.nil)⟩

#check @PGraph.Tight.first_root_of_eqv_constructor
#print axioms PGraph.Tight.first_root_of_eqv_constructor
#check @PGraph.Tight.incoming_constructor_class_representative
#print axioms PGraph.Tight.incoming_constructor_class_representative
#check @PGraph.Tight.new_root_eq_old_constructor_class
#print axioms PGraph.Tight.new_root_eq_old_constructor_class
#check @PGraph.InitialAttachment
#print axioms PGraph.InitialAttachment
#check @PGraph.InitiallyAttached
#print axioms PGraph.InitiallyAttached
#check @PGraph.InitialMerge
#print axioms PGraph.InitialMerge
#check @PGraph.initiallyAttached_of_eqv
#print axioms PGraph.initiallyAttached_of_eqv
#check @PGraph.initialMerge_mem
#print axioms PGraph.initialMerge_mem
#check @PGraph.initialMerge_refl
#print axioms PGraph.initialMerge_refl
#check @PGraph.initialMerge_symm
#print axioms PGraph.initialMerge_symm
#check @PGraph.initialMerge_trans
#print axioms PGraph.initialMerge_trans
#check @PGraph.initialMerge_attachment
#print axioms PGraph.initialMerge_attachment
#check @PGraph.initialMerge_least
#print axioms PGraph.initialMerge_least
#check @PGraph.Tight.initiallyAttached_constructor_cases
#print axioms PGraph.Tight.initiallyAttached_constructor_cases
#check @PGraph.Tight.initiallyAttached_constructors_eq
#print axioms PGraph.Tight.initiallyAttached_constructors_eq
#check @PGraph.Tight.initialMerge_old_constructor_iff
#print axioms PGraph.Tight.initialMerge_old_constructor_iff
#check @PGraph.Tight.initialMerge_new_constructor_context
#print axioms PGraph.Tight.initialMerge_new_constructor_context
#check @PGraph.Tight.initialMerge_constructor_sound
#print axioms PGraph.Tight.initialMerge_constructor_sound
#check @translated_seed_fork_destructor_residual
#print axioms translated_seed_fork_destructor_residual
#check @translated_seed_fork_context
#print axioms translated_seed_fork_context
#check @constructorCompatible_intersection
#print axioms constructorCompatible_intersection
#check @translated_fork_sound_in_constructor_equivalence
#print axioms translated_fork_sound_in_constructor_equivalence

#check @ClassSink.Path
#print axioms ClassSink.Path
#check @ClassSink.Path.refl
#print axioms ClassSink.Path.refl
#check @ClassSink.Path.head
#print axioms ClassSink.Path.head
#check @ClassSink.Path.trans
#print axioms ClassSink.Path.trans
#check @ClassSink.Path.single
#print axioms ClassSink.Path.single
#check @ClassSink.PathN
#print axioms ClassSink.PathN
#check @ClassSink.PathN.refl
#print axioms ClassSink.PathN.refl
#check @ClassSink.PathN.head
#print axioms ClassSink.PathN.head
#check @ClassSink.Path.toPathN
#print axioms ClassSink.Path.toPathN
#check @ClassSink.exists_parent
#print axioms ClassSink.exists_parent
#check @PGraph.InitialEdge
#print axioms PGraph.InitialEdge
#check @PGraph.InitialEdge.old
#print axioms PGraph.InitialEdge.old
#check @PGraph.InitialEdge.reverse
#print axioms PGraph.InitialEdge.reverse
#check @PGraph.InitialEdge.out
#print axioms PGraph.InitialEdge.out
#check @PGraph.InitialEdge.into
#print axioms PGraph.InitialEdge.into
#check @PGraph.InitialEdge.contextOut
#print axioms PGraph.InitialEdge.contextOut
#check @PGraph.InitialEdge.contextInto
#print axioms PGraph.InitialEdge.contextInto
#check @PGraph.InitialEdge.initialMerge
#print axioms PGraph.InitialEdge.initialMerge
#check @PGraph.InitialEdge.tightOld
#print axioms PGraph.InitialEdge.tightOld
#check @PGraph.initialPath_of_reach
#print axioms PGraph.initialPath_of_reach
#check @PGraph.initialPath_reverse_nonRoot
#print axioms PGraph.initialPath_reverse_nonRoot
#check @PGraph.initialPath_class_to_normalRoot
#print axioms PGraph.initialPath_class_to_normalRoot
#check @PGraph.initialPath_class_via_nonRoot
#print axioms PGraph.initialPath_class_via_nonRoot
#check @PGraph.Tight.incoming_initial_route
#print axioms PGraph.Tight.incoming_initial_route
#check @PGraph.Tight.outgoing_context_initial_route
#print axioms PGraph.Tight.outgoing_context_initial_route
#check @PGraph.Tight.initiallyAttached_path
#print axioms PGraph.Tight.initiallyAttached_path
#check @PGraph.Tight.exists_initial_app_class_sink
#print axioms PGraph.Tight.exists_initial_app_class_sink
#check @PGraph.Tight.exists_initial_class_sink
#print axioms PGraph.Tight.exists_initial_class_sink
#check @PGraph.Tight.initial_class_sinks
#print axioms PGraph.Tight.initial_class_sinks
#check @PGraph.Tight.exists_initialInsertion
#print axioms PGraph.Tight.exists_initialInsertion
#check @PGraph.Tight.initialMerge_sound
#print axioms PGraph.Tight.initialMerge_sound
#check @PGraph.initialMerge_represents_roots
#print axioms PGraph.initialMerge_represents_roots
#check @PGraph.Tight.exists_initialInsertion_roots
#print axioms PGraph.Tight.exists_initialInsertion_roots

/-- The actual translated root attaches a fresh source to the old target. -/
example :
    (PGraph.empty [Term.app (.inr 1) []]
      (constructorTranslation [TranslatedResidualControl.groundRule])).InitialMerge
      (Term.app (.inr 0) []) (.app (.inr 0) []) (.app (.inr 1) []) := by
  apply PGraph.initialMerge_attachment
  refine ⟨by simp, Or.inl ?_⟩
  exact ⟨transRule TranslatedResidualControl.groundRule,
    transRule_mem (List.mem_singleton_self _), (fun x => .var x), rfl, rfl⟩

/-- The same step supplies an incoming attachment when the target is new. -/
example :
    (PGraph.empty [Term.app (.inr 0) []]
      (constructorTranslation [TranslatedResidualControl.groundRule])).InitialMerge
      (Term.app (.inr 1) []) (.app (.inr 1) []) (.app (.inr 0) []) := by
  apply PGraph.initialMerge_attachment
  refine ⟨by simp, Or.inr (Or.inl ?_)⟩
  exact ⟨transRule TranslatedResidualControl.groundRule,
    transRule_mem (List.mem_singleton_self _), (fun x => .var x), rfl, rfl⟩

/-- No edge attaches two distinct constants for the empty system. -/
example :
    ¬ (PGraph.empty [Term.app (.inl 0) []]
      ([] : TRS (Nat ⊕ Nat) PUnit)).InitialMerge
      (Term.app (.inl 1) []) (.app (.inl 1) []) (.app (.inl 0) []) := by
  intro h
  rcases h with hold | ⟨_, hc⟩
  · have hm := hold.1
    simp at hm
  · rcases hc with heq | ⟨b, ⟨hb, hstep⟩, _⟩
    · cases heq
    · have hbEq : b = Term.app (.inl 0) [] := by simpa using hb
      subst b
      rcases hstep with ⟨r, hr, _⟩ | ⟨r, hr, _⟩ | ⟨f, xs, ys, _, ha, hb, _⟩
      · cases hr
      · cases hr
      · have haF := (Term.app.inj ha).1
        have hbF := (Term.app.inj hb).1
        have hbad : (Sum.inl 1 : Nat ⊕ Nat) = Sum.inl 0 := haF.trans hbF.symm
        cases hbad

/-- A nonidentity old root produces a new constructor equality with a finite
invariant proof. The old carrier has both a destructor class and a constructor. -/
example : ∃ rho : PGraph
      [Term.app (.inr 0) [], Term.app (.inr 1) [], Term.app (.inl 2) [.app (.inr 1) []]]
      (constructorTranslation [TranslatedResidualControl.groundRule.{0}]),
    rho.InitialMerge (.app (.inl 2) [.app (.inr 0) []])
      (.app (.inl 2) [.app (.inr 0) []]) (.app (.inl 2) [.app (.inr 1) []]) ∧
    DownOn
      [.app (.inl 2) [.app (.inr 0) []], .app (.inr 0) [], .app (.inr 1) [],
        .app (.inl 2) [.app (.inr 1) []]]
      (constructorTranslation [TranslatedResidualControl.groundRule.{0}])
      (.app (.inl 2) [.app (.inr 0) []]) (.app (.inl 2) [.app (.inr 1) []]) ∧
    ∃ beta : PGraph
      [.app (.inl 2) [.app (.inr 0) []], .app (.inr 0) [], .app (.inr 1) [],
        .app (.inl 2) [.app (.inr 1) []]]
      (constructorTranslation [TranslatedResidualControl.groundRule.{0}]),
      beta.Tight ∧ EqvOn
        [.app (.inl 2) [.app (.inr 0) []], .app (.inr 0) [], .app (.inr 1) [],
          .app (.inl 2) [.app (.inr 1) []]] beta.par
        (.app (.inl 2) [.app (.inr 0) []]) (.app (.inl 2) [.app (.inr 1) []]) := by
  let l : Term (Nat ⊕ Nat) PUnit.{1} := .app (.inr 0) []
  let r : Term (Nat ⊕ Nat) PUnit.{1} := .app (.inr 1) []
  let c : Term (Nat ⊕ Nat) PUnit.{1} := .app (.inl 2) [r]
  let B := [l, r, c]
  have hB : Coalgebra B := by
    intro t ht s hst
    have ht' : t = l ∨ t = r ∨ t = c := by simpa [B] using ht
    rcases ht' with rfl | rfl | rfl
    · dsimp only [l] at hst
      cases hst with
      | refl => exact ht
      | arg hm _ => cases hm
    · dsimp only [r] at hst
      cases hst with
      | refl => exact ht
      | arg hm _ => cases hm
    · dsimp only [c] at hst
      cases hst with
      | refl => exact ht
      | arg hm hs =>
          have hm' := List.mem_singleton.mp hm
          subst hm'
          dsimp only [r] at hs
          cases hs with
          | refl => exact List.mem_cons_of_mem l (List.mem_cons_self ..)
          | arg hm _ => cases hm
  obtain ⟨rho, hrootOnly, hroot⟩ := exists_rootOnly_rootStepsRepresented hB
    (constructorRules_constructorTranslation [TranslatedResidualControl.groundRule.{0}])
    (fun {_ _ _} h₁ h₂ => constructorTranslation_deterministic
      TranslatedResidualControl.ground_nonoverlap
      TranslatedResidualControl.ground_rhsDetermined _ _ _ h₁ h₂)
  have hcl : SigmaClosedOn B (EqvOn B rho.par) := by
    intro x y hx hy hxy
    let symbol : Term (Nat ⊕ Nat) PUnit.{1} → Option (Nat ⊕ Nat)
      | .var _ => none
      | .app f _ => some f
    have hhead : symbol x = symbol y := by
      obtain ⟨f, xs, ys, _, rfl, rfl, _⟩ := hxy
      rfl
    have hx' : x = l ∨ x = r ∨ x = c := by simpa [B] using hx
    have hy' : y = l ∨ y = r ∨ y = c := by simpa [B] using hy
    rcases hx' with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl
    all_goals first | exact EqvOn.refl (by simp [B]) | simp [symbol, l, r, c] at hhead
  have hlr : EqvOn B rho.par l r := by
    apply hroot (by simp [B]) (by simp [B])
    exact ⟨transRule TranslatedResidualControl.groundRule,
      transRule_mem (List.mem_singleton_self _), (fun x => .var x), rfl, rfl⟩
  have hnew : Term.app (.inl 2) [l] ∉ B := by decide
  have hargs : ∀ x ∈ [l], x ∈ B := by
    intro x hx
    have heq : x = l := by simpa using hx
    subst x
    simp [B]
  have hatt : rho.InitialAttachment (.app (.inl 2) [l]) c := by
    refine ⟨by simp [B], Or.inr (Or.inr ?_)⟩
    exact ⟨.inl 2, [l], [r], trivial, rfl, rfl,
      List.Forall₂.cons hlr List.Forall₂.nil⟩
  have hm := rho.initialMerge_attachment hatt
  have hA : Coalgebra (.app (.inl 2) [l] :: B) := by
    intro t ht s hst
    rcases List.mem_cons.mp ht with rfl | ht
    · cases hst with
      | refl => exact List.mem_cons_self
      | arg hx hs => exact List.mem_cons_of_mem _ (hB _ (hargs _ hx) _ hs)
    · exact List.mem_cons_of_mem _ (hB _ ht _ hst)
  refine ⟨rho, hm, ?_, ?_⟩
  · exact hrootOnly.tight.initialMerge_constructor_sound hB
      TranslatedResidualControl.ground_nonoverlap
      TranslatedResidualControl.ground_rhsDetermined hcl hnew hargs
      (ConTopped.app 2 [l]) (ConTopped.app 2 [r]) hm
  · obtain ⟨beta, hbt, heq, _⟩ := hrootOnly.tight.exists_initialInsertion hB hA
      TranslatedResidualControl.ground_nonoverlap
      TranslatedResidualControl.ground_rhsDetermined hcl hnew
    exact ⟨beta, hbt, (heq _ _).mpr hm⟩

/-- A nontransitive seed is retained through two actual collapsing translated
roots; transitivity is required only of the ambient constructor relation. -/
example : ∃ S : CRel Nat PUnit.{1},
    ¬ (∀ x y z, S x y → S y z → S x z) ∧
    (S (.app (.inr 0) []) (.app (.inr 1) []) ∨
      barRel (DCT S) (.app (.inr 0) []) (.app (.inr 1) []) ∨
      hatRel S (.app (.inr 0) []) (.app (.inr 1) [])) := by
  let atom (n : Nat) : Term (Nat ⊕ Nat) PUnit.{1} := .app (.inr n) []
  let E : CRel Nat PUnit.{1} := fun x y => (∃ n, x = atom n) ∧ ∃ n, y = atom n
  let S : CRel Nat PUnit.{1} := fun x y =>
    (x = atom 0 ∧ y = atom 1) ∨ (x = atom 1 ∧ y = atom 2)
  let rule : Rule Nat PUnit.{1} := ⟨.app 3 [.var PUnit.unit], .var PUnit.unit, rfl⟩
  have hno : NonOmegaOverlapping [rule] := by
    intro p hp q hq s hsub happ _
    have hp' : p = rule := by simpa using hp
    have hq' : q = rule := by simpa using hq
    subst p
    subst q
    refine ⟨rfl, ?_⟩
    change Subterm s (Term.app 3 [Term.var PUnit.unit]) at hsub
    cases hsub with
    | refl => rfl
    | arg hm hs =>
        have hm' := List.mem_singleton.mp hm
        subst hm'
        have heq := Subterm.eq_of_var hs
        subst s
        cases happ
  have hvar : TRS.RhsDetermined [rule] := by
    intro p hp
    have hp' : p = rule := by simpa using hp
    subst p
    apply determinedBy_of_occurs_subset
    intro x hx
    change VarOccurs x (Term.var PUnit.unit) at hx
    cases hx
    exact VarOccurs.arg (List.mem_cons_self ..) VarOccurs.here
  have hCC : ConstructorCompatible E := by
    intro x y hx _ hxy
    obtain ⟨n, rfl⟩ := hxy.1
    exact (not_conTopped_destructor [] hx).elim
  have hSE : ∀ x y, S x y → E x y := by
    rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩
    · exact ⟨⟨1, rfl⟩, ⟨2, rfl⟩⟩
  have hSCC : ConstructorCompatible S := by
    intro x y hx _ hxy
    obtain ⟨n, rfl⟩ := (hSE x y hxy).1
    exact (not_conTopped_destructor [] hx).elim
  refine ⟨S, ?_, ?_⟩
  · intro htrans
    have hbad := htrans (atom 0) (atom 1) (atom 2)
      (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)
    simp [S, atom] at hbad
  · apply translated_seed_fork_destructor_residual (E := E) (R := [rule]) hno hvar
      (fun _ _ h => ⟨h.2, h.1⟩) (fun _ _ _ h₁ h₂ => ⟨h₁.1, h₂.2⟩) hCC hSE hSCC
      (a := .app (.inr 3) [atom 0]) (c := .app (.inr 3) [atom 1])
    · exact ⟨transRule rule, transRule_mem (List.mem_singleton_self _),
        (fun _ => atom 0), rfl, rfl⟩
    · exact ⟨.inr 3, [atom 0], [atom 1], ⟨3, rfl⟩, rfl, rfl,
        List.Forall₂.cons (Or.inl ⟨rfl, rfl⟩) List.Forall₂.nil⟩
    · exact ⟨transRule rule, transRule_mem (List.mem_singleton_self _),
        (fun _ => atom 1), rfl, rfl⟩

/-- The input relation has a two-cycle; the selected parent terminates and
retains an actual directed route on the non-term carrier. -/
example : ∃ g : Bool → Option Bool,
    WellFounded (fun y x => g x = some y) ∧
    (∀ {x y}, g x = some y → x ≠ y) ∧ ParentReplacement.Path g true false := by
  obtain ⟨g, hwf, hedge, hroute, _⟩ := ClassSink.exists_parent
    (fun _ : Bool => True) (fun _ _ : Bool => True)
    (fun x y : Bool => x ≠ y)
    (fun _ => ⟨trivial, trivial⟩) (fun _ _ => trivial)
    (fun _ _ _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ => trivial)
    (fun _ => false) (fun _ => rfl) (by
      intro x _
      cases x with
      | false => exact ClassSink.Path.refl false
      | true => exact ClassSink.Path.single (by decide))
  exact ⟨g, hwf, hedge, hroute true trivial⟩

/-- Initial insertion constructs an actual graph for an outgoing root. -/
example : ∃ beta : PGraph [Term.app (.inr 0) [], Term.app (.inr 1) []]
    (constructorTranslation [TranslatedResidualControl.groundRule.{0}]),
    beta.Tight ∧ EqvOn [.app (.inr 0) [], .app (.inr 1) []] beta.par
      (.app (.inr 0) []) (.app (.inr 1) []) := by
  let b : Term (Nat ⊕ Nat) PUnit.{1} := .app (.inr 1) []
  let a : Term (Nat ⊕ Nat) PUnit.{1} := .app (.inr 0) []
  let rho := PGraph.empty [b] (constructorTranslation [TranslatedResidualControl.groundRule.{0}])
  have hB : Coalgebra [b] := by
    intro t ht s hst
    have heq : t = b := by simpa using ht
    subst t
    dsimp only [b] at hst
    cases hst with
    | refl => exact ht
    | arg hm _ => cases hm
  have hA : Coalgebra [a, b] := by
    intro t ht s hst
    have heq : t = a ∨ t = b := by simpa using ht
    rcases heq with rfl | rfl
    all_goals
      dsimp only [a, b] at hst
      cases hst with
      | refl => exact ht
      | arg hm _ => cases hm
  have ht : rho.Tight := by intro x y h; cases h
  have hcl : SigmaClosedOn [b] (EqvOn [b] rho.par) := by
    intro x y hx hy _
    have hx' : x = b := by simpa using hx
    have hy' : y = b := by simpa using hy
    subst x
    subst y
    exact EqvOn.refl (by simp)
  obtain ⟨beta, hbt, heq, _⟩ := ht.exists_initialInsertion hB hA
    TranslatedResidualControl.ground_nonoverlap
    TranslatedResidualControl.ground_rhsDetermined hcl (by decide : a ∉ [b])
  refine ⟨beta, hbt, (heq _ _).mpr (rho.initialMerge_attachment ?_)⟩
  refine ⟨by simp [b], Or.inl ?_⟩
  exact ⟨transRule TranslatedResidualControl.groundRule,
    transRule_mem (List.mem_singleton_self _), (fun x => .var x), rfl, rfl⟩

/-- Incoming insertion reverses only root-free old routes, not the root step. -/
example : ∃ beta : PGraph [Term.app (.inr 1) [], Term.app (.inr 0) []]
    (constructorTranslation [TranslatedResidualControl.groundRule.{0}]),
    beta.Tight ∧ EqvOn [.app (.inr 1) [], .app (.inr 0) []] beta.par
      (.app (.inr 0) []) (.app (.inr 1) []) := by
  let b : Term (Nat ⊕ Nat) PUnit.{1} := .app (.inr 0) []
  let a : Term (Nat ⊕ Nat) PUnit.{1} := .app (.inr 1) []
  let rho := PGraph.empty [b] (constructorTranslation [TranslatedResidualControl.groundRule.{0}])
  have hB : Coalgebra [b] := by
    intro t ht s hst
    have heq : t = b := by simpa using ht
    subst t
    dsimp only [b] at hst
    cases hst with
    | refl => exact ht
    | arg hm _ => cases hm
  have hA : Coalgebra [a, b] := by
    intro t ht s hst
    have heq : t = a ∨ t = b := by simpa using ht
    rcases heq with rfl | rfl
    all_goals
      dsimp only [a, b] at hst
      cases hst with
      | refl => exact ht
      | arg hm _ => cases hm
  have ht : rho.Tight := by intro x y h; cases h
  have hcl : SigmaClosedOn [b] (EqvOn [b] rho.par) := by
    intro x y hx hy _
    have hx' : x = b := by simpa using hx
    have hy' : y = b := by simpa using hy
    subst x
    subst y
    exact EqvOn.refl (by simp)
  obtain ⟨beta, hbt, heq, _⟩ := ht.exists_initialInsertion hB hA
    TranslatedResidualControl.ground_nonoverlap
    TranslatedResidualControl.ground_rhsDetermined hcl (by decide : a ∉ [b])
  refine ⟨beta, hbt, (heq _ _).mpr (rho.initialMerge_symm
    (rho.initialMerge_attachment ?_))⟩
  refine ⟨by simp [b], Or.inr (Or.inl ?_)⟩
  exact ⟨transRule TranslatedResidualControl.groundRule,
    transRule_mem (List.mem_singleton_self _), (fun x => .var x), rfl, rfl⟩

/-- A fresh variable is inserted without an infinite-variable hypothesis. -/
example : ∃ beta : PGraph [Term.var PUnit.unit]
    (constructorTranslation [TranslatedResidualControl.groundRule.{0}]),
    beta.Tight ∧ beta.par (.var PUnit.unit) = none := by
  let rho := PGraph.empty ([] : List (Term (Nat ⊕ Nat) PUnit.{1}))
    (constructorTranslation [TranslatedResidualControl.groundRule.{0}])
  have hB : Coalgebra ([] : List (Term (Nat ⊕ Nat) PUnit.{1})) := by
    intro _ h
    cases h
  have hA : Coalgebra ([Term.var PUnit.unit] : List (Term (Nat ⊕ Nat) PUnit.{1})) := by
    intro t ht s hst
    have heq : t = Term.var PUnit.unit := by simpa using ht
    subst t
    have heq := Subterm.eq_of_var hst
    subst s
    simp
  have ht : rho.Tight := by intro x y h; cases h
  have hcl : SigmaClosedOn [] (EqvOn [] rho.par) := by intro _ _ h; cases h
  obtain ⟨beta, hbt, _, hedge⟩ := ht.exists_initialInsertion hB hA
    TranslatedResidualControl.ground_nonoverlap
    TranslatedResidualControl.ground_rhsDetermined hcl (by simp)
  refine ⟨beta, hbt, ?_⟩
  cases hp : beta.par (.var PUnit.unit) with
  | none => rfl
  | some y =>
      have hl := hedge hp
      cases hl with
      | old h => cases h
      | reverse h _ => cases h
      | out h _ => cases h
      | into h _ => cases h
      | contextOut h _ => cases h
      | contextInto h _ => cases h
