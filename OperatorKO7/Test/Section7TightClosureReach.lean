import OperatorKO7.Meta.UniqueNormalization.Section7TightClosure

set_option autoImplicit false

open OperatorKO7.Meta.UniqueNormalization

#check @PGraph.spliceParent
#print axioms PGraph.spliceParent
#check @PGraph.spliceParent_terminating
#print axioms PGraph.spliceParent_terminating
#check @PGraph.spliceParent_edge
#print axioms PGraph.spliceParent_edge
#check @PGraph.spliceParent_mem
#print axioms PGraph.spliceParent_mem
#check @PGraph.spliceParent_preserves
#print axioms PGraph.spliceParent_preserves
#check @PGraph.spliceParent_new
#print axioms PGraph.spliceParent_new
#check @PGraph.SpliceEq
#print axioms PGraph.SpliceEq
#check @PGraph.SpliceEq.symm
#print axioms PGraph.SpliceEq.symm
#check @PGraph.SpliceEq.trans
#print axioms PGraph.SpliceEq.trans
#check @PGraph.spliceParent_eqv_iff
#print axioms PGraph.spliceParent_eqv_iff
#check @PGraph.spliceParent_constructor_pair
#print axioms PGraph.spliceParent_constructor_pair
#check @PGraph.spliceGraph
#print axioms PGraph.spliceGraph
#check @PGraph.exists_constructor_splice
#print axioms PGraph.exists_constructor_splice
#check @PGraph.spliceParent_terminating_iff
#print axioms PGraph.spliceParent_terminating_iff
#check @PGraph.CrossConstructorSound
#print axioms PGraph.CrossConstructorSound
#check @PGraph.spliceParent_grey
#print axioms PGraph.spliceParent_grey
#check @PGraph.spliceParent_sound_iff_crossConstructorSound
#print axioms PGraph.spliceParent_sound_iff_crossConstructorSound
#check @PGraph.spliceGraphOfCrossSlice
#print axioms PGraph.spliceGraphOfCrossSlice
#check @PGraph.exists_splice_of_crossSlice
#print axioms PGraph.exists_splice_of_crossSlice
#check @PGraph.crossConstructorSound_of_constructor_roots
#print axioms PGraph.crossConstructorSound_of_constructor_roots

#check @PGraph.rootGraft
#print axioms PGraph.rootGraft
#check @PGraph.rootGraft_old_edge
#print axioms PGraph.rootGraft_old_edge
#check @PGraph.rootGraft_root_edge
#print axioms PGraph.rootGraft_root_edge
#check @PGraph.rootGraft_edge_iff
#print axioms PGraph.rootGraft_edge_iff
#check @PGraph.rootGraft_terminating_iff
#print axioms PGraph.rootGraft_terminating_iff
#check @PGraph.rootGraft_mem
#print axioms PGraph.rootGraft_mem
#check @PGraph.rootGraft_reach_roots
#print axioms PGraph.rootGraft_reach_roots
#check @PGraph.rootGraft_eqv_iff
#print axioms PGraph.rootGraft_eqv_iff
#check @PGraph.rootGraft_preserves
#print axioms PGraph.rootGraft_preserves
#check @PGraph.RootGraftEq
#print axioms PGraph.RootGraftEq
#check @PGraph.RootGraftConstructorSound
#print axioms PGraph.RootGraftConstructorSound
#check @PGraph.rootGraft_grey
#print axioms PGraph.rootGraft_grey
#check @PGraph.rootGraft_sound_iff_constructorSound
#print axioms PGraph.rootGraft_sound_iff_constructorSound
#check @PGraph.exists_rootGraft
#print axioms PGraph.exists_rootGraft
#check @PGraph.rootRouting
#print axioms PGraph.rootRouting
#check @PGraph.rootRouting_edge_iff
#print axioms PGraph.rootRouting_edge_iff
#check @PGraph.rootRouting_step
#print axioms PGraph.rootRouting_step
#check @PGraph.rootGraft_terminating_iff_routing
#print axioms PGraph.rootGraft_terminating_iff_routing
#check @PGraph.rootGraft_reach_routing
#print axioms PGraph.rootGraft_reach_routing
#check @PGraph.rootGraft_routing_reach
#print axioms PGraph.rootGraft_routing_reach
#check @PGraph.rootGraft_eqv_iff_routing
#print axioms PGraph.rootGraft_eqv_iff_routing
#check @PGraph.rootGraft_grey_of_routing
#print axioms PGraph.rootGraft_grey_of_routing

#check @CT.exists_missing_barRel_of_constructorClosed
#check @PGraph.TightEqualityComplete.eqvOn_of_nonRootReach_tightEdge
#check @PGraph.TightEqualityComplete.constructorClosed
#check @PGraph.Tight.destructorRoute
#check @PGraph.TightEqualityComplete.missing_barRel_has_root_residual
#check @PGraph.TightEqualityComplete.not_sigmaClosedOn_iff_missing_barRel
#check @PGraph.TightEqualityComplete.missing_barRel_has_subterm_residual

#print axioms CT.exists_missing_barRel_of_constructorClosed
#print axioms PGraph.TightEqualityComplete.eqvOn_of_nonRootReach_tightEdge
#print axioms PGraph.TightEqualityComplete.constructorClosed
#print axioms PGraph.Tight.destructorRoute
#print axioms PGraph.TightEqualityComplete.missing_barRel_has_root_residual
#print axioms PGraph.TightEqualityComplete.not_sigmaClosedOn_iff_missing_barRel
#print axioms PGraph.TightEqualityComplete.missing_barRel_has_subterm_residual

#check @SymbolsSatisfy
#check @SymbolsSatisfy.var
#check @SymbolsSatisfy.app
#check @SymbolsSatisfy.app_iff
#check @SymbolsSatisfy.of_apply
#check @SymbolsSatisfy.at_variable
#check @SymbolsSatisfy.relates_instances
#check @RhsSymbolsDescend
#check @RhsSymbolsDescend.semantic_pair
#check @PGraph.TightEqualityComplete.sigmaClosedOn_of_rhsSymbolsDescend
#check @PGraph.TightEqualityComplete.universal_of_rhsSymbolsDescend
#check @exists_tight_universal_of_rhsSymbolsDescend
#check @SymbolsSatisfy.of_conOnly
#check @RhsSymbolsDescend.of_constructor_rhs
#check @exists_tight_universal_of_constructor_rhs
#check @DownOn.trans_of_rhsSymbolsDescend
#check @Down.trans_of_rhsSymbolsDescend
#check @conv_eq_down_of_rhsSymbolsDescend

#print axioms SymbolsSatisfy
#print axioms SymbolsSatisfy.var
#print axioms SymbolsSatisfy.app
#print axioms SymbolsSatisfy.app_iff
#print axioms SymbolsSatisfy.of_apply
#print axioms SymbolsSatisfy.at_variable
#print axioms SymbolsSatisfy.relates_instances
#print axioms RhsSymbolsDescend
#print axioms RhsSymbolsDescend.semantic_pair
#print axioms PGraph.TightEqualityComplete.sigmaClosedOn_of_rhsSymbolsDescend
#print axioms PGraph.TightEqualityComplete.universal_of_rhsSymbolsDescend
#print axioms exists_tight_universal_of_rhsSymbolsDescend
#print axioms SymbolsSatisfy.of_conOnly
#print axioms RhsSymbolsDescend.of_constructor_rhs
#print axioms exists_tight_universal_of_constructor_rhs
#print axioms DownOn.trans_of_rhsSymbolsDescend
#print axioms Down.trans_of_rhsSymbolsDescend
#print axioms conv_eq_down_of_rhsSymbolsDescend

#check @PGraph.Universal.extends_from
#check @PGraph.EqualityComplete.universal_of_exists_universal
#check @PGraph.EqualityComplete.universal_of_rhsSymbolsDescend
#check @PGraph.exists_tightUniversal_extension_of_rhsSymbolsDescend
#check @constructorCompatible_conv_of_rhsSymbolsDescend
#check @consistent_of_rhsSymbolsDescend
#check @consistent_of_constructor_rhs

#print axioms PGraph.Universal.extends_from
#print axioms PGraph.EqualityComplete.universal_of_exists_universal
#print axioms PGraph.EqualityComplete.universal_of_rhsSymbolsDescend
#print axioms PGraph.exists_tightUniversal_extension_of_rhsSymbolsDescend
#print axioms constructorCompatible_conv_of_rhsSymbolsDescend
#print axioms consistent_of_rhsSymbolsDescend
#print axioms consistent_of_constructor_rhs

open OperatorKO7.Meta.Rewriting

namespace Section7TightClosureControls

private theorem active_tight : Section7Active.graph.Tight := by
  intro a b h
  rcases Section7Active.parent_edge h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl Section7Active.root_twice
  · exact Or.inl Section7Active.root_once

private theorem active_max : Section7Active.graph.TightEqualityComplete := by
  intro beta _ _ a b hab
  exact ⟨hab.1, hab.2.1, Section7Active.constant,
    Section7Active.reach_constant hab.1, Section7Active.reach_constant hab.2.1⟩

example : Section7Active.graph.Tight ∧ Section7Active.graph.TightEqualityComplete ∧
    rootStep Section7Active.rules Section7Active.once Section7Active.constant ∧
      Section7Active.once ≠ Section7Active.constant :=
  ⟨active_tight, active_max, Section7Active.root_once, Section7Active.once_ne_constant⟩

example : ¬ rootStep Section7Active.rules Section7Active.constant Section7Active.once := by
  rw [Section7Active.rootStep_iff]
  decide

private abbrev leftConstructor : Section7Active.T :=
  .app (.inl ()) [Section7Active.once]

private abbrev rightConstructor : Section7Active.T :=
  .app (.inl ()) [Section7Active.constant]

private abbrev carrier := coalgebraOf [leftConstructor, rightConstructor]

example : ∃ rho : PGraph carrier Section7Active.rules,
    rho.Tight ∧ rho.TightEqualityComplete ∧
      EqvOn carrier rho.par leftConstructor rightConstructor ∧
        leftConstructor ≠ rightConstructor := by
  have hA : Coalgebra carrier := coalgebra_coalgebraOf _
  obtain ⟨rho, htight, hmax, hroot⟩ :=
    exists_tightEqualityComplete_rootStepsRepresented_of_strong hA
      Section7Active.rules_constructor Section7Active.rules_strong
  have hl : leftConstructor ∈ carrier :=
    mem_coalgebraOf (by simp)
  have hr : rightConstructor ∈ carrier := mem_coalgebraOf (by simp)
  have harg : EqvOn carrier rho.par Section7Active.once Section7Active.constant :=
    hroot (hA.arg hl (by simp)) (hA.arg hr (by simp)) Section7Active.root_once
  refine ⟨rho, htight, hmax, ?_, by decide⟩
  apply hmax.constructorClosed hA Section7Active.rules_constructor htight hl hr
  exact Or.inr ⟨.inl (), [Section7Active.once], [Section7Active.constant],
    ⟨(), rfl⟩, rfl, rfl, List.Forall₂.cons harg List.Forall₂.nil⟩

example : ∃ rho : PGraph Section7Active.terms Section7Active.rules,
    rho.Tight ∧ rho.TightEqualityComplete ∧
      ¬ (∃ a b, a ∈ Section7Active.terms ∧ b ∈ Section7Active.terms ∧
        barRel (EqvOn Section7Active.terms rho.par) a b ∧
          ¬ EqvOn Section7Active.terms rho.par a b) := by
  refine ⟨Section7Active.graph, active_tight, active_max, ?_⟩
  rintro ⟨a, b, ha, hb, _, hmissing⟩
  exact hmissing ⟨ha, hb, Section7Active.constant,
    Section7Active.reach_constant ha, Section7Active.reach_constant hb⟩

private abbrev BTerm := Term (Bool ⊕ Bool) Unit
private abbrev c0 : BTerm := .app (.inl false) []
private abbrev c1 : BTerm := .app (.inl true) []
private abbrev d0 : BTerm := .app (.inr false) [c0]
private abbrev d1 : BTerm := .app (.inr false) [c1]
private abbrev testRelation (a b : BTerm) := a = b ∨ ConTopped a ∧ ConTopped b

example : ∃ x y : BTerm, Subterm x d0 ∧ Subterm y d1 ∧
    x ∈ coalgebraOf [d0, d1] ∧ y ∈ coalgebraOf [d0, d1] ∧
      barRel testRelation x y ∧ ¬ testRelation x y := by
  have hclosed : ∀ a b, a ∈ coalgebraOf [d0, d1] →
      b ∈ coalgebraOf [d0, d1] → hatEq testRelation a b → testRelation a b := by
    intro a b _ _ h
    exact Or.inr ⟨ConTopped.of_hatEq h,
      ConTopped.of_hatEq (hatEq.symm (E := testRelation)
        (fun _ _ h => h.elim (fun e => Or.inl e.symm)
          (fun h => Or.inr ⟨h.2, h.1⟩)) h)⟩
  have harg : testRelation c0 c1 :=
    Or.inr ⟨Or.inr ⟨false, [], rfl⟩, Or.inr ⟨true, [], rfl⟩⟩
  have hct : CT testRelation d0 d1 :=
    CT.app (List.Forall₂.cons (CT.base harg) List.Forall₂.nil)
  have hne : ¬ testRelation d0 d1 := by
    rintro (h | ⟨h, _⟩)
    · exact (by decide : d0 ≠ d1) h
    · rcases h with ⟨x, hx⟩ | ⟨f, xs, hfx⟩
      · cases hx
      · cases hfx
  exact CT.exists_missing_barRel_of_constructorClosed (coalgebra_coalgebraOf _)
    hclosed (mem_coalgebraOf (by simp)) (mem_coalgebraOf (by simp)) hct hne

private theorem active_rhs_constructor : ∀ r ∈ Section7Active.rules, ConOnly r.rhs := by
  intro r hr
  have hr' : r = Section7Active.rule := by simpa [Section7Active.rules] using hr
  subst r
  exact ConOnly.var ()

example (A : List Section7Active.T) (hA : Coalgebra A) :
    ∃ rho : PGraph A Section7Active.rules,
      rho.Tight ∧ RootStepsRepresented A Section7Active.rules rho ∧
        SigmaClosedOn A (EqvOn A rho.par) ∧ rho.Universal := by
  obtain ⟨rho, htight, _, hroot, hclosed, huniv⟩ :=
    exists_tight_universal_of_constructor_rhs hA Section7Active.rules_constructor
      Section7Active.rules_strong active_rhs_constructor
  exact ⟨rho, htight, hroot, hclosed, huniv⟩

private abbrev NT := Term (Nat ⊕ Nat) Unit
private def lowerRule : Rule (Nat ⊕ Nat) Unit where
  lhs := .app (.inr 0) [.var ()]
  rhs := .var ()
  lhs_isApp := rfl
private def upperRule : Rule (Nat ⊕ Nat) Unit where
  lhs := .app (.inr 1) [.var ()]
  rhs := .app (.inr 0) [.var ()]
  lhs_isApp := rfl
private abbrev twoRules : TRS (Nat ⊕ Nat) Unit := [upperRule, lowerRule]

private theorem twoRules_lhs (r : Rule (Nat ⊕ Nat) Unit) (hr : r ∈ twoRules) :
    ∃ d : Nat, r.lhs = .app (.inr d) [.var ()] := by
  rcases (by simpa [twoRules] using hr : r = upperRule ∨ r = lowerRule) with rfl | rfl
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

private theorem twoRules_constructor : ConstructorRules twoRules := by
  intro r hr
  obtain ⟨d, hlhs⟩ := twoRules_lhs r hr
  refine ⟨d, [.var ()], hlhs, ?_⟩
  intro p hp
  have hp' : p = .var () := by simpa using hp
  subst p
  exact ConOnly.var ()

private theorem twoRules_determined (r : Rule (Nat ⊕ Nat) Unit) (hr : r ∈ twoRules) :
    Rule.RhsDetermined r := by
  obtain ⟨d, hlhs⟩ := twoRules_lhs r hr
  intro s t h
  rw [hlhs] at h
  have he : s () = t () := by simpa [Subst.applyList_eq_map] using h
  have hst : s = t := funext (fun x => by cases x; exact he)
  rw [hst]

private theorem twoRules_strong : StronglyAlmostNonOmegaOverlapping twoRules := by
  have heads {f g : Nat ⊕ Nat} {xs ys : List NT}
      (h : OmegaUnifiable (.app f xs) (.app g ys)) : f = g := by
    obtain ⟨E, hE, hst⟩ := h
    unfold leftCopy rightCopy at hst
    simp only [Term.mapVar_app] at hst
    exact hE.symbol_eq hst
  constructor
  · intro r hr r' hr' s hs happ _
    obtain ⟨d, hlhs⟩ := twoRules_lhs r hr
    obtain ⟨f, args, a, heq, ha, hsa⟩ := hs
    rw [hlhs] at heq
    have hargs := (Term.app.inj heq).2
    have ha' : a = .var () := by simpa only [← hargs, List.mem_singleton] using ha
    subst a
    have hs' : s = .var () := hsa.eq_of_var
    subst s
    exact Bool.noConfusion happ
  · intro r hr r' hr' hu
    have he : r = r' := by
      rcases (by simpa [twoRules] using hr : r = upperRule ∨ r = lowerRule) with rfl | rfl <;>
        rcases (by simpa [twoRules] using hr' : r' = upperRule ∨ r' = lowerRule) with rfl | rfl
      · rfl
      · have h := heads hu
        cases h
      · have h := heads hu
        cases h
      · rfl
    subst r'
    refine ⟨CommonGeneralisation.self r (twoRules_determined r hr), ?_⟩
    intro x hx
    change VarOccurs x r.lhs
    obtain ⟨d, hlhs⟩ := twoRules_lhs r hr
    rw [hlhs]
    cases x
    exact VarOccurs.arg (by simp) .here

private theorem twoRules_descend : RhsSymbolsDescend twoRules Nat.lt := by
  intro r hr d ps hlhs
  rcases (by simpa [twoRules] using hr : r = upperRule ∨ r = lowerRule) with rfl | rfl
  · have hd : d = 1 := by simpa [upperRule] using (Term.app.inj hlhs).1.symm
    subst d
    apply SymbolsSatisfy.app (show Nat.lt 0 1 from Nat.zero_lt_succ 0)
    intro p hp
    have hp' : p = .var () := by simpa using hp
    subst p
    exact SymbolsSatisfy.var ()
  · exact SymbolsSatisfy.var ()

example (A : List NT) (hA : Coalgebra A) :
    ∃ rho : PGraph A twoRules, rho.Tight ∧ rho.TightEqualityComplete ∧
      RootStepsRepresented A twoRules rho ∧ SigmaClosedOn A (EqvOn A rho.par) ∧ rho.Universal :=
  exists_tight_universal_of_rhsSymbolsDescend hA twoRules_constructor
    twoRules_strong Nat.lt_wfRel.wf twoRules_descend

example (A : List NT) (hA : Coalgebra A) (rho : PGraph A twoRules)
    (hmax : rho.EqualityComplete) : rho.Universal :=
  hmax.universal_of_rhsSymbolsDescend hA twoRules_constructor
    twoRules_strong Nat.lt_wfRel.wf twoRules_descend

example : ConstructorCompatible (conv twoRules) ∧ Consistent twoRules :=
  ⟨constructorCompatible_conv_of_rhsSymbolsDescend twoRules_constructor
      twoRules_strong Nat.lt_wfRel.wf twoRules_descend,
    consistent_of_rhsSymbolsDescend twoRules_constructor
      twoRules_strong Nat.lt_wfRel.wf twoRules_descend⟩

example : ¬ conv twoRules (.app (.inl 0) []) (.app (.inl 1) []) := by
  intro h
  have hCC := constructorCompatible_conv_of_rhsSymbolsDescend twoRules_constructor
    twoRules_strong Nat.lt_wfRel.wf twoRules_descend
  rcases hCC _ _ (ConTopped.app 0 []) (ConTopped.app 1 []) h with
      ⟨x, hleft, _⟩ | ⟨f, xs, ys, hleft, hright, _⟩
  · cases hleft
  · have hf : f = 0 := by simpa using (Term.app.inj hleft).1.symm
    subst f
    cases (Term.app.inj hright).1

example : rootStep twoRules (.app (.inr 1) [.app (.inl 0) []])
      (.app (.inr 0) [.app (.inl 0) []]) ∧
    rootStep twoRules (.app (.inr 0) [.app (.inl 0) []]) (.app (.inl 0) []) := by
  constructor
  · exact ⟨upperRule, by simp [twoRules], fun _ => .app (.inl 0) [], rfl, rfl⟩
  · exact ⟨lowerRule, by simp [twoRules], fun _ => .app (.inl 0) [], rfl, rfl⟩

private def growingRule : Rule (Nat ⊕ Nat) Unit where
  lhs := .app (.inr 0) [.var ()]
  rhs := .app (.inl 0) [.app (.inr 0) [.var ()]]
  lhs_isApp := rfl

private theorem growing_strong : StronglyAlmostNonOmegaOverlapping [growingRule] := by
  have hdet : Rule.RhsDetermined growingRule := by
    intro s t h
    have he : s () = t () := by simpa [growingRule, Subst.applyList_eq_map] using h
    have hst : s = t := funext (fun x => by cases x; exact he)
    rw [hst]
  constructor
  · intro r hr r' hr' s hs happ _
    have hr' : r = growingRule := by simpa using hr
    subst r
    obtain ⟨f, args, a, heq, ha, hsa⟩ := hs
    change Term.app (.inr 0) [.var ()] = Term.app f args at heq
    have hargs := (Term.app.inj heq).2
    have ha' : a = .var () := by simpa only [← hargs, List.mem_singleton] using ha
    subst a
    have hs' : s = .var () := hsa.eq_of_var
    subst s
    exact Bool.noConfusion happ
  · intro r hr r' hr' _
    have he : r = growingRule := by simpa using hr
    have he' : r' = growingRule := by simpa using hr'
    subst r
    subst r'
    refine ⟨CommonGeneralisation.self growingRule hdet, ?_⟩
    intro x _
    cases x
    exact VarOccurs.arg (by simp) .here

example : StronglyAlmostNonOmegaOverlapping [growingRule] ∧
    ¬ (∃ lt : Nat → Nat → Prop, WellFounded lt ∧ RhsSymbolsDescend [growingRule] lt) := by
  refine ⟨growing_strong, ?_⟩
  rintro ⟨lt, hwf, hdesc⟩
  have hsymbols := hdesc growingRule (by simp) 0 [.var ()] rfl
  have hinner := (SymbolsSatisfy.app_iff.mp hsymbols).2
    (.app (.inr 0) [.var ()]) (by simp)
  have hself : lt 0 0 := (SymbolsSatisfy.app_iff.mp hinner).1
  have hirr : ∀ n, ¬ lt n n := by
    intro n
    induction hwf.apply n with
    | intro n _ ih => intro hn; exact ih n hn hn
  exact hirr 0 hself

end Section7TightClosureControls

#check @eqvOn_downOn_of_constructorSlice
#check @eqvOn_downOn_iff_constructorSlice
#check @PGraph.of_constructorSlice
#check @hatEq_of_reach_of_selfGrey
#check @constructorCompatible_eqvOn_of_selfGrey
#check @eqvOn_downOn_of_reachableConstructorSlice
#check @EqvOn.exists_reachable_constructor_failure
#print axioms eqvOn_downOn_of_constructorSlice
#print axioms eqvOn_downOn_iff_constructorSlice
#print axioms PGraph.of_constructorSlice
#print axioms hatEq_of_reach_of_selfGrey
#print axioms constructorCompatible_eqvOn_of_selfGrey
#print axioms eqvOn_downOn_of_reachableConstructorSlice
#print axioms EqvOn.exists_reachable_constructor_failure

#check @ConstructorSupportDependency
#check @eqvOn_downOn_of_wellFounded_constructorSupport
#check @PGraph.of_constructorSupport
#print axioms ConstructorSupportDependency
#print axioms eqvOn_downOn_of_wellFounded_constructorSupport
#print axioms PGraph.of_constructorSupport

namespace Section7CyclicSliceControls

abbrev T := Term (Bool ⊕ Bool) Unit
abbrev a : T := .app (.inr false) []
abbrev b : T := .app (.inl false) []
abbrev d (t : T) : T := .app (.inr true) [t]
abbrev c (t : T) : T := .app (.inl true) [t]
abbrev da : T := d a
abbrev db : T := d b
abbrev cda : T := c da
abbrev cdb : T := c db

def seedRule : Rule (Bool ⊕ Bool) Unit where
  lhs := a
  rhs := b
  lhs_isApp := rfl

def growingRule : Rule (Bool ⊕ Bool) Unit where
  lhs := d (.var ())
  rhs := c (d (.var ()))
  lhs_isApp := rfl

def rules : TRS (Bool ⊕ Bool) Unit := [seedRule, growingRule]
def terms : List T := coalgebraOf [cda, cdb]

theorem terms_coalgebra : Coalgebra terms := coalgebra_coalgebraOf _

theorem mem_terms (t : T) :
    t ∈ terms ↔ t = a ∨ t = b ∨ t = da ∨ t = db ∨ t = cda ∨ t = cdb := by
  simp [terms, coalgebraOf, subterms, subtermsList, cda, cdb, da, db, c, d, a, b,
    or_assoc, or_left_comm, or_comm]

theorem rules_constructor : ConstructorRules rules := by
  intro r hr
  rcases (by simpa [rules] using hr : r = seedRule ∨ r = growingRule) with rfl | rfl
  · exact ⟨false, [], rfl, by simp⟩
  · refine ⟨true, [.var ()], rfl, ?_⟩
    intro p hp
    have hp' : p = .var () := by simpa using hp
    subst p
    exact ConOnly.var ()

private theorem rhs_determined (r : Rule (Bool ⊕ Bool) Unit) (hr : r ∈ rules) :
    Rule.RhsDetermined r := by
  rcases (by simpa [rules] using hr : r = seedRule ∨ r = growingRule) with rfl | rfl
  · intro s t _
    rfl
  · intro s t h
    change d (s ()) = d (t ()) at h
    change c (d (s ())) = c (d (t ()))
    have he : s () = t () := by simpa [d] using h
    rw [he]

theorem rules_strong : StronglyAlmostNonOmegaOverlapping rules := by
  have heads {f g : Bool ⊕ Bool} {xs ys : List T}
      (h : OmegaUnifiable (.app f xs) (.app g ys)) : f = g := by
    obtain ⟨E, hE, hst⟩ := h
    unfold leftCopy rightCopy at hst
    simp only [Term.mapVar_app] at hst
    exact hE.symbol_eq hst
  constructor
  · intro r hr r' hr' s hs happ _
    rcases (by simpa [rules] using hr : r = seedRule ∨ r = growingRule) with rfl | rfl
    · obtain ⟨f, args, p, heq, hp, _⟩ := hs
      change Term.app (.inr false) [] = Term.app f args at heq
      have hargs := (Term.app.inj heq).2
      simp only [← hargs, List.not_mem_nil] at hp
    · obtain ⟨f, args, p, heq, hp, hsp⟩ := hs
      change Term.app (.inr true) [.var ()] = Term.app f args at heq
      have hargs := (Term.app.inj heq).2
      have hp' : p = .var () := by simpa only [← hargs, List.mem_singleton] using hp
      subst p
      have hs' : s = .var () := hsp.eq_of_var
      subst s
      exact Bool.noConfusion happ
  · intro r hr r' hr' hu
    have he : r = r' := by
      rcases (by simpa [rules] using hr : r = seedRule ∨ r = growingRule) with rfl | rfl <;>
        rcases (by simpa [rules] using hr' : r' = seedRule ∨ r' = growingRule) with rfl | rfl
      · rfl
      · have h := heads hu
        cases h
      · have h := heads hu
        cases h
      · rfl
    subst r'
    refine ⟨CommonGeneralisation.self r (rhs_determined r hr), ?_⟩
    intro x hx
    change VarOccurs x r.lhs
    rcases (by simpa [rules] using hr : r = seedRule ∨ r = growingRule) with rfl | rfl
    · change VarOccurs x (.app (.inl false) [] : T) at hx
      cases hx with
      | arg hp _ => simp at hp
    · cases x
      exact VarOccurs.arg (by simp) .here

theorem root_ab : rootStep rules a b :=
  ⟨seedRule, by simp [rules], fun _ => a, rfl, rfl⟩

theorem root_d (t : T) : rootStep rules (d t) (c (d t)) :=
  ⟨growingRule, by simp [rules], fun _ => t, rfl, rfl⟩

theorem rootStep_iff (x y : T) :
    rootStep rules x y ↔ (x = a ∧ y = b) ∨ ∃ t, x = d t ∧ y = c (d t) := by
  constructor
  · rintro ⟨r, hr, s, hx, hy⟩
    rcases (by simpa [rules] using hr : r = seedRule ∨ r = growingRule) with rfl | rfl
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨s (), hx, hy⟩
  · rintro (⟨rfl, rfl⟩ | ⟨t, rfl, rfl⟩)
    · exact root_ab
    · exact root_d t

def parent (t : T) : Option T :=
  if t = a then some b else if t = da then some cda else
    if t = db then some cdb else if t = cda then some cdb else none

theorem parent_edge {x y : T} (h : parent x = some y) :
    (x = a ∧ y = b) ∨ (x = da ∧ y = cda) ∨
      (x = db ∧ y = cdb) ∨ (x = cda ∧ y = cdb) := by
  by_cases h0 : x = a
  · subst x
    exact Or.inl ⟨rfl, by simpa [parent] using h.symm⟩
  · by_cases h1 : x = da
    · subst x
      exact Or.inr (Or.inl ⟨rfl, by simpa [parent, h0] using h.symm⟩)
    · by_cases h2 : x = db
      · subst x
        exact Or.inr (Or.inr (Or.inl ⟨rfl, by simpa [parent, h0, h1] using h.symm⟩))
      · by_cases h3 : x = cda
        · subst x
          exact Or.inr (Or.inr (Or.inr
            ⟨rfl, by simpa [parent, h0, h1, h2] using h.symm⟩))
        · simp [parent, h0, h1, h2, h3] at h

theorem parent_mem {x y : T} (h : parent x = some y) : x ∈ terms ∧ y ∈ terms := by
  rcases parent_edge h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [mem_terms]

private def rank (t : T) : Nat :=
  if t = da then 2 else if t = a ∨ t = db ∨ t = cda then 1 else 0

theorem parent_terminating : Terminating parent := by
  have hwf : WellFounded (fun x y : T => rank x < rank y) :=
    InvImage.wf (f := rank) Nat.lt_wfRel.wf
  have hsub : Subrelation (fun y x : T => parent x = some y)
      (fun y x : T => rank y < rank x) := by
    intro y x h
    rcases parent_edge h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  exact Subrelation.wf hsub hwf

private def sink (t : T) : T := if t = a ∨ t = b then b else cdb

private theorem parent_sink {x y : T} (h : parent x = some y) : sink x = sink y := by
  rcases parent_edge h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

private theorem reach_sink_eq {x y : T} (h : Reach parent x y) : sink x = sink y := by
  induction h with
  | refl x => rfl
  | head hedge _ ih => exact (parent_sink hedge).trans ih

private theorem reach_sink {t : T} (ht : t ∈ terms) : Reach parent t (sink t) := by
  rcases (mem_terms t).mp ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Reach.head (b := b) (by decide) (Reach.refl b)
  · exact Reach.refl b
  · exact Reach.head (b := cda) (by decide)
      (Reach.head (b := cdb) (by decide) (Reach.refl cdb))
  · exact Reach.head (b := cdb) (by decide) (Reach.refl cdb)
  · exact Reach.head (b := cdb) (by decide) (Reach.refl cdb)
  · exact Reach.refl cdb

private theorem eqv_iff {x y : T} :
    EqvOn terms parent x y ↔ x ∈ terms ∧ y ∈ terms ∧ sink x = sink y := by
  constructor
  · rintro ⟨hx, hy, s, hxs, hys⟩
    exact ⟨hx, hy, (reach_sink_eq hxs).trans (reach_sink_eq hys).symm⟩
  · rintro ⟨hx, hy, hs⟩
    refine ⟨hx, hy, sink x, reach_sink hx, ?_⟩
    rw [hs]
    exact reach_sink hy

theorem eqv_da_db : EqvOn terms parent da db :=
  eqv_iff.mpr ⟨by simp [mem_terms], by simp [mem_terms], by decide⟩

theorem hat_cda_cdb : hatEq (EqvOn terms parent) cda cdb :=
  Or.inr ⟨.inl true, [da], [db], ⟨true, rfl⟩, rfl, rfl,
    List.Forall₂.cons eqv_da_db List.Forall₂.nil⟩

theorem parent_grey {x y : T} (h : parent x = some y) :
    Grey terms rules (EqvOn terms parent) x y := by
  rcases parent_edge h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl root_ab
  · exact Or.inl (root_d a)
  · exact Or.inl (root_d b)
  · exact Or.inr (Or.inr hat_cda_cdb)

theorem down_ab : DownOn terms rules a b :=
  DownOn.rootComp (by simp [mem_terms]) (by simp [mem_terms]) root_ab
    (DownOn.refl (by simp [mem_terms]))

theorem down_da_db : DownOn terms rules da db :=
  DownOn.barCl (by simp [mem_terms]) (by simp [mem_terms])
    (List.Forall₂.cons down_ab List.Forall₂.nil)

theorem down_cda_cdb : DownOn terms rules cda cdb :=
  DownOn.hatCl (by simp [mem_terms]) (by simp [mem_terms])
    (List.Forall₂.cons down_da_db List.Forall₂.nil)

private theorem constructor_mem {t : T} (ht : t ∈ terms) (hc : ConTopped t) :
    t = b ∨ t = cda ∨ t = cdb := by
  rcases (mem_terms t).mp ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (not_conTopped_destructor [] hc).elim
  · exact Or.inl rfl
  · exact (not_conTopped_destructor [a] hc).elim
  · exact (not_conTopped_destructor [b] hc).elim
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem constructor_slice {x y : T} (hcx : ConTopped x) (hcy : ConTopped y)
    (he : EqvOn terms parent x y) : DownOn terms rules x y := by
  have hx := he.mem.1
  have hy := he.mem.2
  rcases constructor_mem hx hcx with rfl | rfl | rfl <;>
    rcases constructor_mem hy hcy with rfl | rfl | rfl
  · exact DownOn.refl hx
  · exact ((by decide : sink b ≠ sink cda) (eqv_iff.mp he).2.2).elim
  · exact ((by decide : sink b ≠ sink cdb) (eqv_iff.mp he).2.2).elim
  · exact ((by decide : sink cda ≠ sink b) (eqv_iff.mp he).2.2).elim
  · exact DownOn.refl hx
  · exact down_cda_cdb
  · exact ((by decide : sink cdb ≠ sink b) (eqv_iff.mp he).2.2).elim
  · exact DownOn.symm down_cda_cdb
  · exact DownOn.refl hx

def graph : PGraph terms rules :=
  PGraph.of_constructorSlice rules_constructor parent parent_mem parent_terminating
    parent_grey constructor_slice

theorem graph_tight : graph.Tight := by
  intro x y h
  rcases parent_edge h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl root_ab
  · exact Or.inl (root_d a)
  · exact Or.inl (root_d b)
  · exact Or.inr (Or.inr hat_cda_cdb)

def oldParent (t : T) : Option T :=
  if t = a then some b else if t = da then some cda else
    if t = db then some cdb else none

theorem old_parent_edge {x y : T} (h : oldParent x = some y) :
    (x = a ∧ y = b) ∨ (x = da ∧ y = cda) ∨ (x = db ∧ y = cdb) := by
  by_cases h0 : x = a
  · subst x
    exact Or.inl ⟨rfl, by simpa [oldParent] using h.symm⟩
  · by_cases h1 : x = da
    · subst x
      exact Or.inr (Or.inl ⟨rfl, by simpa [oldParent, h0] using h.symm⟩)
    · by_cases h2 : x = db
      · subst x
        exact Or.inr (Or.inr ⟨rfl, by simpa [oldParent, h0, h1] using h.symm⟩)
      · simp [oldParent, h0, h1, h2] at h

theorem old_parents_preserved {x y : T} (h : oldParent x = some y) : parent x = some y := by
  rcases old_parent_edge h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem old_parent_root {x y : T} (h : oldParent x = some y) : rootStep rules x y := by
  rcases old_parent_edge h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact root_ab
  · exact root_d a
  · exact root_d b

theorem old_parent_of_root {x y : T} (hx : x ∈ terms) (h : rootStep rules x y) :
    oldParent x = some y := by
  rcases (rootStep_iff x y).mp h with ⟨rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  · decide
  · have ht : t = a ∨ t = b := by
      simpa [mem_terms, a, b, da, db, cda, cdb, d, c] using hx
    rcases ht with rfl | rfl <;> decide

def oldGraph : PGraph terms rules where
  par := oldParent
  mem_edge := by
    intro x y h
    exact parent_mem (old_parents_preserved h)
  term := by
    have hsub : Subrelation (fun y x : T => oldParent x = some y)
        (fun y x : T => parent x = some y) := by
      intro y x h
      exact old_parents_preserved h
    exact Subrelation.wf hsub parent_terminating
  sub := by
    intro x y h
    apply graph.sub
    apply EqvOn.mono ?_ h
    intro p q hpq
    exact old_parents_preserved hpq
  grey := by
    intro x y h
    exact Or.inl (old_parent_root h)

theorem oldGraph_rootOnly : oldGraph.RootOnly := by
  intro x y h
  exact old_parent_root h

theorem oldGraph_rootRepresented : RootStepsRepresented terms rules oldGraph := by
  intro x y hx hy hroot
  exact EqvOn.of_reach hx hy
    (Reach.head (old_parent_of_root hx hroot) (Reach.refl y))

theorem graph_extends : oldGraph.Extends graph := by
  intro x y h
  exact old_parents_preserved h

theorem graph_rootRepresented : RootStepsRepresented terms rules graph := by
  intro x y hx hy hroot
  exact EqvOn.of_reach hx hy
    (Reach.head (old_parents_preserved (old_parent_of_root hx hroot)) (Reach.refl y))

private theorem tilde_head_eq {f g : Bool ⊕ Bool} {xs ys : List T}
    (h : tildeAll (EqvOn terms parent) (.app f xs) (.app g ys)) : f = g := by
  obtain ⟨k, as, bs, _, hx, hy, _⟩ := h
  exact (Term.app.inj hx).1.trans (Term.app.inj hy).1.symm

theorem graph_sigmaClosed : SigmaClosedOn terms (EqvOn terms graph.par) := by
  intro x y hx hy htilde
  rcases (mem_terms x).mp hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (mem_terms y).mp hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact eqv_iff.mpr ⟨hx, hy, by decide⟩
    | have hhead := tilde_head_eq htilde
      cases hhead

theorem graph_universal : graph.Universal :=
  graph.universal_of_rootStepsRepresented graph_sigmaClosed graph_rootRepresented

theorem graph_equalityComplete : graph.EqualityComplete := graph_universal.equalityComplete

private def oldSink (t : T) : T :=
  if t = da ∨ t = cda then cda else if t = db ∨ t = cdb then cdb else b

private theorem old_reach_sink_eq {x y : T} (h : Reach oldParent x y) :
    oldSink x = oldSink y := by
  induction h with
  | refl x => rfl
  | @head x z y hedge _ ih =>
      have he : oldSink x = oldSink z := by
        rcases old_parent_edge hedge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      exact he.trans ih

theorem old_missing_pair : ¬ EqvOn terms oldGraph.par da db := by
  rintro ⟨_, _, s, hds, hes⟩
  have he : oldSink da = oldSink db :=
    (old_reach_sink_eq hds).trans (old_reach_sink_eq hes).symm
  exact (by decide : oldSink da ≠ oldSink db) he

theorem new_pair : EqvOn terms graph.par da db ∧ da ≠ db :=
  ⟨eqv_da_db, by decide⟩

theorem growing_not_descending :
    ¬ ∃ lt : Bool → Bool → Prop, WellFounded lt ∧ RhsSymbolsDescend rules lt := by
  rintro ⟨lt, hwf, hdesc⟩
  have hsymbols := hdesc growingRule (by simp [rules]) true [.var ()] rfl
  have hinner := (SymbolsSatisfy.app_iff.mp hsymbols).2 (d (.var ())) (by simp)
  have hself : lt true true := (SymbolsSatisfy.app_iff.mp hinner).1
  have hirr : ∀ t, ¬ lt t t := by
    intro t
    induction hwf.apply t with
    | intro t _ ih => intro ht; exact ih t ht ht
  exact hirr true hself

theorem cyclic_control : ConstructorRules rules ∧ StronglyAlmostNonOmegaOverlapping rules ∧
    Coalgebra terms ∧ graph.Tight ∧ oldGraph.RootOnly ∧ oldGraph.Extends graph ∧
      RootStepsRepresented terms rules graph ∧ SigmaClosedOn terms (EqvOn terms graph.par) ∧
        graph.Universal ∧ graph.EqualityComplete ∧
        ¬ EqvOn terms oldGraph.par da db ∧ EqvOn terms graph.par da db :=
  ⟨rules_constructor, rules_strong, terms_coalgebra, graph_tight, oldGraph_rootOnly,
    graph_extends, graph_rootRepresented, graph_sigmaClosed, graph_universal,
    graph_equalityComplete, old_missing_pair, new_pair.1⟩

#check @T
#check @a
#check @b
#check @d
#check @c
#check @da
#check @db
#check @cda
#check @cdb
#check @seedRule
#check @growingRule
#check @rules
#check @terms
#check @terms_coalgebra
#check @mem_terms
#check @rules_constructor
#check @rhs_determined
#check @rules_strong
#check @root_ab
#check @root_d
#check @rootStep_iff
#check @parent
#check @parent_edge
#check @parent_mem
#check @rank
#check @parent_terminating
#check @sink
#check @parent_sink
#check @reach_sink_eq
#check @reach_sink
#check @eqv_iff
#check @eqv_da_db
#check @hat_cda_cdb
#check @parent_grey
#check @down_ab
#check @down_da_db
#check @down_cda_cdb
#check @constructor_mem
#check @constructor_slice
#check @graph
#check @graph_tight
#check @oldParent
#check @old_parent_edge
#check @old_parents_preserved
#check @old_parent_root
#check @old_parent_of_root
#check @oldGraph
#check @oldGraph_rootOnly
#check @oldGraph_rootRepresented
#check @graph_extends
#check @graph_rootRepresented
#check @tilde_head_eq
#check @graph_sigmaClosed
#check @graph_universal
#check @graph_equalityComplete
#check @oldSink
#check @old_reach_sink_eq
#check @old_missing_pair
#check @new_pair
#check @growing_not_descending
#check @cyclic_control
#print axioms T
#print axioms a
#print axioms b
#print axioms d
#print axioms c
#print axioms da
#print axioms db
#print axioms cda
#print axioms cdb
#print axioms seedRule
#print axioms growingRule
#print axioms rules
#print axioms terms
#print axioms terms_coalgebra
#print axioms mem_terms
#print axioms rules_constructor
#print axioms rhs_determined
#print axioms rules_strong
#print axioms root_ab
#print axioms root_d
#print axioms rootStep_iff
#print axioms parent
#print axioms parent_edge
#print axioms parent_mem
#print axioms rank
#print axioms parent_terminating
#print axioms sink
#print axioms parent_sink
#print axioms reach_sink_eq
#print axioms reach_sink
#print axioms eqv_iff
#print axioms eqv_da_db
#print axioms hat_cda_cdb
#print axioms parent_grey
#print axioms down_ab
#print axioms down_da_db
#print axioms down_cda_cdb
#print axioms constructor_mem
#print axioms constructor_slice
#print axioms graph
#print axioms graph_tight
#print axioms oldParent
#print axioms old_parent_edge
#print axioms old_parents_preserved
#print axioms old_parent_root
#print axioms old_parent_of_root
#print axioms oldGraph
#print axioms oldGraph_rootOnly
#print axioms oldGraph_rootRepresented
#print axioms graph_extends
#print axioms graph_rootRepresented
#print axioms tilde_head_eq
#print axioms graph_sigmaClosed
#print axioms graph_universal
#print axioms graph_equalityComplete
#print axioms oldSink
#print axioms old_reach_sink_eq
#print axioms old_missing_pair
#print axioms new_pair
#print axioms growing_not_descending
#print axioms cyclic_control

def argumentSeed (x y : T) : Prop :=
  (x = y ∧ x ∈ terms) ∨ (x = da ∧ y = db) ∨ (x = db ∧ y = da)

theorem argumentSeed_sound {x y : T} (h : argumentSeed x y) : DownOn terms rules x y := by
  rcases h with ⟨rfl, hx⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact DownOn.refl hx
  · exact down_da_db
  · exact DownOn.symm down_da_db

theorem constructor_support_empty (q p : T × T) :
    ¬ ConstructorSupportDependency terms parent argumentSeed q p := by
  rcases p with ⟨p₁, p₂⟩
  rintro ⟨_, hsource, he, f, xs, ys, x, y, hp₁, hp₂, hxy, harg, hnot, _⟩
  change p₁ = .app (.inl f) xs at hp₁
  change p₂ = .app (.inl f) ys at hp₂
  have hp₁mem := he.mem.1
  have hp₂mem := he.mem.2
  have hc₁ : ConTopped p₁ := by rw [hp₁]; exact Or.inr ⟨f, xs, rfl⟩
  have hc₂ : ConTopped p₂ := by rw [hp₂]; exact Or.inr ⟨f, ys, rfl⟩
  rcases constructor_mem he.mem.1 hc₁ with rfl | rfl | rfl <;>
    rcases constructor_mem he.mem.2 hc₂ with rfl | rfl | rfl <;>
    simp only [b, cda, cdb, c, Term.app.injEq, Sum.inl.injEq] at hp₁ hp₂ <;>
    rcases hp₁ with ⟨rfl, rfl⟩ <;> simp only [Bool.true_eq_false, Bool.false_eq_true,
      false_and, true_and] at hp₂ <;>
    try contradiction
  all_goals
    subst ys
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] at hxy
    rcases hxy with ⟨rfl, rfl⟩
    exact hnot (by simp [argumentSeed, mem_terms])

theorem constructor_support_wellFounded :
    WellFounded (ConstructorSupportDependency terms parent argumentSeed) :=
  ⟨fun p => Acc.intro p (fun q h => (constructor_support_empty q p h).elim)⟩

def supportGraph : PGraph terms rules :=
  PGraph.of_constructorSupport terms_coalgebra rules_constructor parent parent_mem
    parent_terminating parent_grey argumentSeed_sound constructor_support_wellFounded

theorem supportGraph_same_parent : supportGraph.par = parent := rfl

theorem supportGraph_universal : supportGraph.Universal := graph_universal

theorem support_cyclic_control :
    supportGraph.Universal ∧ EqvOn terms supportGraph.par da db ∧
      da ≠ db ∧ ¬ (∃ lt : Bool → Bool → Prop, WellFounded lt ∧ RhsSymbolsDescend rules lt) :=
  ⟨supportGraph_universal, eqv_da_db, by decide, growing_not_descending⟩

#check @argumentSeed
#check @argumentSeed_sound
#check @constructor_support_empty
#check @constructor_support_wellFounded
#check @supportGraph
#check @supportGraph_same_parent
#check @supportGraph_universal
#check @support_cyclic_control
#print axioms argumentSeed
#print axioms argumentSeed_sound
#print axioms constructor_support_empty
#print axioms constructor_support_wellFounded
#print axioms supportGraph
#print axioms supportGraph_same_parent
#print axioms supportGraph_universal
#print axioms support_cyclic_control

end Section7CyclicSliceControls

#check @DCT
#check @DCT.base
#check @DCT.least
#check @DCT.barClosed
#check @DCT.app
#check @DCT.mono
#check @DCT.toCT
#check @DCT.unfold
#check @DCT.conTopped_left_iff
#check @DCT.conTopped_right_iff
#check @DCT.constructorCompatible
#check @DCT.exists_missing_barRel
#check @DCT.destructorLabel_instances
#check @destructorLabel_instances_destructor_residual
#print axioms DCT
#print axioms DCT.base
#print axioms DCT.least
#print axioms DCT.barClosed
#print axioms DCT.app
#print axioms DCT.mono
#print axioms DCT.toCT
#print axioms DCT.unfold
#print axioms DCT.conTopped_left_iff
#print axioms DCT.conTopped_right_iff
#print axioms DCT.constructorCompatible
#print axioms DCT.exists_missing_barRel
#print axioms DCT.destructorLabel_instances
#print axioms destructorLabel_instances_destructor_residual

namespace DestructorContextControls

private abbrev T := Term (Nat ⊕ Nat) Nat
private def atom (n : Nat) : T := .app (.inr n) []
private def E (a b : T) : Prop := a = atom 0 ∧ b = atom 1

theorem base_constructorCompatible : ConstructorCompatible E := by
  intro a b ha _ hab
  exact (not_conTopped_destructor [] (hab.1 ▸ ha)).elim

theorem destructor_context_added :
    DCT E (.app (.inr 2) [atom 0]) (.app (.inr 2) [atom 1]) ∧
      ¬ E (.app (.inr 2) [atom 0]) (.app (.inr 2) [atom 1]) := by
  constructor
  · exact DCT.app (List.Forall₂.cons (DCT.base ⟨rfl, rfl⟩) List.Forall₂.nil)
  · simp [E, atom]

theorem constructor_context_excluded :
    CT E (.app (.inl 2) [atom 0]) (.app (.inl 2) [atom 1]) ∧
      ¬ DCT E (.app (.inl 2) [atom 0]) (.app (.inl 2) [atom 1]) := by
  constructor
  · exact CT.app (List.Forall₂.cons (CT.base ⟨rfl, rfl⟩) List.Forall₂.nil)
  · rw [DCT.conTopped_left_iff (ConTopped.app 2 _)]
    simp [E, atom]

theorem nested_rhs_destructor_context :
    DCT E (.app (.inr 2) [.app (.inr 3) [atom 0]])
      (.app (.inr 2) [.app (.inr 3) [atom 1]]) := by
  exact DCT.destructorLabel_instances
    (s := fun _ => atom 0) (t := fun _ => atom 1)
    (.app 2 [.app 3 [.var 0]]) (fun _ _ => ⟨rfl, rfl⟩)

example : ∃ x y, Subterm x (.app (.inr 2) [atom 0]) ∧
    Subterm y (.app (.inr 2) [atom 1]) ∧ barRel E x y ∧ ¬ E x y :=
  DCT.exists_missing_barRel destructor_context_added.1 destructor_context_added.2

#check @DestructorContextControls.base_constructorCompatible
#check @DestructorContextControls.destructor_context_added
#check @DestructorContextControls.constructor_context_excluded
#check @DestructorContextControls.nested_rhs_destructor_context
#print axioms DestructorContextControls.base_constructorCompatible
#print axioms DestructorContextControls.destructor_context_added
#print axioms DestructorContextControls.constructor_context_excluded
#print axioms DestructorContextControls.nested_rhs_destructor_context

end DestructorContextControls

#check @CT.one_new_app_iff
#check @DCT.one_new_app_iff
#check @CT.one_new_representatives_eq
#print axioms CT.one_new_app_iff
#print axioms DCT.one_new_app_iff
#print axioms CT.one_new_representatives_eq

namespace OneNewTermControls

open Section7Active

private abbrev E := EqvOn terms graph.par
private abbrev outside : T := .app (.inr ()) [twice]

private theorem old_closed : SigmaClosedOn terms E := by
  intro a b ha hb _
  exact ⟨ha, hb, constant, reach_constant ha, reach_constant hb⟩

private theorem outside_new : outside ∉ terms := by decide
private theorem outside_args : ∀ x ∈ [twice], x ∈ terms := by
  intro x hx
  have heq : x = twice := by simpa using hx
  subst x
  simp [mem_terms]

private theorem outside_to (a : T) (ha : a ∈ terms) :
    CT E outside (.app (.inr ()) [a]) := by
  apply CT.app
  exact List.Forall₂.cons (CT.base
    ⟨by simp [mem_terms], ha, constant, reach_constant (by simp [mem_terms]),
      reach_constant ha⟩) List.Forall₂.nil

example : outside ∉ terms ∧ tildeAll E outside once := by
  refine ⟨outside_new, (CT.one_new_app_iff terms_coalgebra old_closed
    (fun h => h.mem) outside_new outside_args (by simp [mem_terms])).mp ?_⟩
  exact outside_to constant (by simp [mem_terms])

example : DCT E outside once ↔ barRel E outside once :=
  DCT.one_new_app_iff terms_coalgebra old_closed (fun h => h.mem)
    outside_new outside_args (by simp [mem_terms])

example : E once twice ∧ once ≠ twice := by
  refine ⟨CT.one_new_representatives_eq terms_coalgebra old_closed
    (fun h => h.mem) (fun _ _ h => EqvOn.symm h)
    (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂) outside_new outside_args
    (by simp [mem_terms]) (by simp [mem_terms])
    (outside_to constant (by simp [mem_terms]))
    (outside_to once (by simp [mem_terms])), Ne.symm twice_ne_once⟩

end OneNewTermControls

namespace Section7CyclicSliceControls

private theorem old_constructor_nf {t : T} (ht : ConTopped t) : oldGraph.NF t := by
  cases he : oldParent t with
  | none => exact he
  | some u =>
      exact (not_conTopped_peel (A := terms) rules_constructor
        (Or.inl (old_parent_root he)) ht).elim

private theorem old_root_da : oldGraph.normalRoot da = cda := by
  have hp : Reach oldGraph.par da cda :=
    Reach.head (by decide) (Reach.refl _)
  have hn : oldGraph.NF cda := by change oldParent cda = none; decide
  exact (oldGraph.normalRoot_eq_of_reach hp).trans
    ((oldGraph.normalRoot_spec cda).1.toParentPath.eq_of_none hn).symm

private theorem old_root_db : oldGraph.normalRoot db = cdb := by
  have hp : Reach oldGraph.par db cdb :=
    Reach.head (by decide) (Reach.refl _)
  have hn : oldGraph.NF cdb := by change oldParent cdb = none; decide
  exact (oldGraph.normalRoot_eq_of_reach hp).trans
    ((oldGraph.normalRoot_spec cdb).1.toParentPath.eq_of_none hn).symm

private theorem old_bar_da_db : barRel (EqvOn terms oldGraph.par) da db := by
  refine ⟨.inr true, [a], [b], ⟨true, rfl⟩, rfl, rfl, ?_⟩
  exact List.Forall₂.cons (EqvOn.of_reach (by simp [mem_terms])
    (by simp [mem_terms]) (Reach.head (by decide) (Reach.refl _))) List.Forall₂.nil

private theorem splice_roots : hatEq (oldGraph.SpliceEq da db)
    (oldGraph.normalRoot da) (oldGraph.normalRoot db) := by
  rw [old_root_da, old_root_db]
  refine Or.inr ⟨.inl true, [da], [db], ⟨true, rfl⟩, rfl, rfl, ?_⟩
  exact List.Forall₂.cons (Or.inr (Or.inl
    ⟨EqvOn.refl (by simp [mem_terms]), EqvOn.refl (by simp [mem_terms])⟩))
    List.Forall₂.nil

/-- The construction repairs the recursive rule with a repeated destructor;
all inputs, including soundness of the new constructor equation, are proved. -/
theorem constructed_recursive_splice :
    ∃ beta : PGraph terms rules, beta.par = oldGraph.spliceParent da db ∧ beta.Tight ∧
      oldGraph.EqualityExtends beta ∧ EqvOn terms beta.par da db ∧
      RootStepsRepresented terms rules beta ∧
      (∀ x y, EqvOn terms beta.par x y ↔ oldGraph.SpliceEq da db x y) := by
  obtain ⟨beta, hp, ht, he, hab, hiff, hroot⟩ :=
    oldGraph.exists_constructor_splice rules_constructor oldGraph_rootOnly.tight
      old_constructor_nf (by simp [mem_terms]) (by simp [mem_terms]) old_missing_pair
      (Or.inr (Or.inl old_bar_da_db)) splice_roots
      (by simpa only [old_root_da, old_root_db] using down_cda_cdb)
  exact ⟨beta, hp, ht, he, hab, hroot oldGraph_rootRepresented, hiff⟩

#check @constructed_recursive_splice
#print axioms constructed_recursive_splice

/-- The general constructor-slice construction yields a universal graph on
the recursive six-term carrier; the root equations and context closure agree. -/
theorem general_splice_recursive_universal :
    ∃ beta : PGraph terms rules, beta.par = oldGraph.spliceParent da db ∧
      beta.Tight ∧ oldGraph.EqualityExtends beta ∧
      RootStepsRepresented terms rules beta ∧ beta.Universal := by
  have hcross : oldGraph.CrossConstructorSound da db :=
    oldGraph.crossConstructorSound_of_constructor_roots old_constructor_nf
      (by simpa only [old_root_da, old_root_db] using down_cda_cdb)
  obtain ⟨beta, hp, ht, hext, hnew, hiff, hroot⟩ :=
    oldGraph.exists_splice_of_crossSlice rules_constructor oldGraph_rootOnly.tight
      (by simp [mem_terms]) (by simp [mem_terms]) old_missing_pair
      (Or.inr (Or.inl old_bar_da_db)) (Or.inr (Or.inr splice_roots))
      (Or.inr (Or.inr splice_roots)) hcross
  have hbg : beta.EqualityExtends graph := by
    intro x y hxy
    rcases (hiff x y).mp hxy with hold | ⟨hxa, hby⟩ | ⟨hxb, hay⟩
    · exact EqvOn.mono graph_extends hold
    · exact (EqvOn.mono graph_extends hxa).trans
        (eqv_da_db.trans (EqvOn.mono graph_extends hby))
    · exact (EqvOn.mono graph_extends hxb).trans
        (eqv_da_db.symm.trans (EqvOn.mono graph_extends hay))
  have hgb : graph.EqualityExtends beta := by
    intro x y hxy
    apply EqvOn.mono_of_parent_eqv (g := parent) (h := beta.par) ?_ hxy
    intro p q hpq
    rcases parent_edge hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hext (EqvOn.of_reach (by simp [mem_terms]) (by simp [mem_terms])
        (Reach.head (by decide) (Reach.refl _)))
    · exact hext (EqvOn.of_reach (by simp [mem_terms]) (by simp [mem_terms])
        (Reach.head (by decide) (Reach.refl _)))
    · exact hext (EqvOn.of_reach (by simp [mem_terms]) (by simp [mem_terms])
        (Reach.head (by decide) (Reach.refl _)))
    · have hleft : EqvOn terms beta.par da cda := hext
        (EqvOn.of_reach (by simp [mem_terms]) (by simp [mem_terms])
          (Reach.head (by decide) (Reach.refl _)))
      have hright : EqvOn terms beta.par db cdb := hext
        (EqvOn.of_reach (by simp [mem_terms]) (by simp [mem_terms])
          (Reach.head (by decide) (Reach.refl _)))
      exact hleft.symm.trans (hnew.trans hright)
  have hclosed : SigmaClosedOn terms (EqvOn terms beta.par) := by
    intro x y hx hy hxy
    exact hgb (graph_sigmaClosed x y hx hy (tildeOn_mono (fun _ _ h => hbg h) hxy))
  have hr : RootStepsRepresented terms rules beta := hroot oldGraph_rootRepresented
  exact ⟨beta, hp, ht, hext, hr, beta.universal_of_rootStepsRepresented hclosed hr⟩

example : ¬ Terminating (oldGraph.spliceParent da cda) := by
  rw [oldGraph.spliceParent_terminating_iff (by simp [mem_terms]) (by simp [mem_terms])]
  intro h
  exact h (EqvOn.of_reach (by simp [mem_terms]) (by simp [mem_terms])
    (Reach.head (by decide) (Reach.refl _)))

#check @general_splice_recursive_universal
#print axioms general_splice_recursive_universal

private def recursiveRootBatch (x : T) : Option T := if x = cda then some cdb else none

private theorem recursiveRootBatch_edge {x y : T} (h : recursiveRootBatch x = some y) :
    x = cda ∧ y = cdb := by
  unfold recursiveRootBatch at h
  split at h <;> simp_all

private theorem recursiveRootBatch_roots {x y : T} (h : recursiveRootBatch x = some y) :
    oldGraph.NF x ∧ oldGraph.NF y := by
  obtain ⟨rfl, rfl⟩ := recursiveRootBatch_edge h
  change oldParent cda = none ∧ oldParent cdb = none
  decide

private theorem recursiveRootBatch_mem {x y : T} (h : recursiveRootBatch x = some y) :
    x ∈ terms ∧ y ∈ terms := by
  obtain ⟨rfl, rfl⟩ := recursiveRootBatch_edge h
  simp [mem_terms]

private theorem recursiveRootBatch_terminating : Terminating recursiveRootBatch := by
  apply Subrelation.wf (r := fun y x : T => (if y = cda then 1 else 0) <
    (if x = cda then 1 else 0)) ?_ (InvImage.wf (f := fun x : T =>
      if x = cda then 1 else 0) Nat.lt_wfRel.wf)
  intro y x h
  obtain ⟨rfl, rfl⟩ := recursiveRootBatch_edge h
  decide

private theorem recursiveRootBatch_parent : oldGraph.rootGraft recursiveRootBatch = parent := by
  funext t
  by_cases h0 : t = a <;> by_cases h1 : t = da <;> by_cases h2 : t = db <;>
    simp [PGraph.rootGraft, oldGraph, oldParent, recursiveRootBatch, parent, h0, h1, h2]

/-- The batch construction retains the three actual root contractions and
constructs the universal graph of the recursive fixture. -/
theorem root_graft_recursive_universal :
    ∃ beta : PGraph terms rules, beta.par = parent ∧ beta.Tight ∧
      oldGraph.Extends beta ∧ RootStepsRepresented terms rules beta ∧
      beta.Universal ∧ EqvOn terms beta.par da db ∧ ¬ EqvOn terms oldGraph.par da db := by
  have heq : ∀ x y, EqvOn terms parent x y ↔ oldGraph.RootGraftEq recursiveRootBatch x y := by
    intro x y
    rw [← recursiveRootBatch_parent]
    exact oldGraph.rootGraft_eqv_iff recursiveRootBatch (fun h => recursiveRootBatch_roots h)
  have hg : ∀ {x y}, recursiveRootBatch x = some y →
      Grey terms rules (oldGraph.RootGraftEq recursiveRootBatch) x y := by
    intro x y h
    obtain ⟨rfl, rfl⟩ := recursiveRootBatch_edge h
    exact Grey.mono (fun x y h => (heq x y).mp h) (parent_grey (by decide))
  have ht : ∀ {x y}, recursiveRootBatch x = some y →
      TightEdge rules (oldGraph.RootGraftEq recursiveRootBatch) x y := by
    intro x y h
    obtain ⟨rfl, rfl⟩ := recursiveRootBatch_edge h
    exact Or.inr (Or.inr (hatEq.mono (fun x y h => (heq x y).mp h) hat_cda_cdb))
  have hs : oldGraph.RootGraftConstructorSound recursiveRootBatch := by
    intro x y hx hy hxy
    exact constructor_slice hx hy ((heq x y).mpr hxy)
  obtain ⟨beta, hp, hbt, _, _, hroot⟩ := oldGraph.exists_rootGraft rules_constructor
    oldGraph_rootOnly.tight recursiveRootBatch (fun h => recursiveRootBatch_roots h)
    (fun h => recursiveRootBatch_mem h) recursiveRootBatch_terminating hg ht hs
  have hpar : beta.par = parent := hp.trans recursiveRootBatch_parent
  have hext : oldGraph.Extends beta := by
    intro x y h
    rw [hp]
    exact oldGraph.rootGraft_old_edge recursiveRootBatch h
  have hcl : SigmaClosedOn terms (EqvOn terms beta.par) := by
    rw [hpar]
    exact graph_sigmaClosed
  have hr : RootStepsRepresented terms rules beta := hroot oldGraph_rootRepresented
  refine ⟨beta, hpar, hbt, hext, hr, beta.universal_of_rootStepsRepresented hcl hr,
    ?_, old_missing_pair⟩
  rw [hpar]
  exact eqv_da_db

#check @root_graft_recursive_universal
#print axioms root_graft_recursive_universal

private def internalRootBatch (x : T) : Option T := if x = cda then some db else none

private theorem internalRootBatch_edge {x y : T} (h : internalRootBatch x = some y) :
    x = cda ∧ y = db := by unfold internalRootBatch at h; split at h <;> simp_all

private theorem internalRootBatch_source {x y : T} (h : internalRootBatch x = some y) :
    oldGraph.NF x := by
  obtain ⟨rfl, _⟩ := internalRootBatch_edge h
  change oldParent cda = none
  decide

private theorem internalRootBatch_routing :
    oldGraph.rootRouting internalRootBatch = recursiveRootBatch := by
  funext x
  by_cases hx : x = cda <;>
    simp [PGraph.rootRouting, internalRootBatch, recursiveRootBatch, hx, old_root_db]

/-- A parent-only control: the selected internal target is retained, its old
outgoing edge survives, and the complete parent still terminates. -/
theorem internal_target_parent_control :
    oldGraph.rootGraft internalRootBatch cda = some db ∧ ¬ oldGraph.NF db ∧
      oldGraph.rootGraft internalRootBatch db = some cdb ∧
      Terminating (oldGraph.rootGraft internalRootBatch) ∧
      EqvOn terms (oldGraph.rootGraft internalRootBatch) da db := by
  have hn : oldGraph.NF cda := by change oldParent cda = none; decide
  have hd : oldGraph.par db = some cdb := by decide
  have hterm : Terminating (oldGraph.rootGraft internalRootBatch) := by
    apply (oldGraph.rootGraft_terminating_iff_routing internalRootBatch
      (fun h => internalRootBatch_source h)).mpr
    rw [internalRootBatch_routing]
    exact recursiveRootBatch_terminating
  refine ⟨oldGraph.rootGraft_root_edge internalRootBatch hn (by simp [internalRootBatch]),
    ?_, oldGraph.rootGraft_old_edge internalRootBatch hd, hterm, ?_⟩
  · intro h
    change oldParent db = none at h
    have hne : oldParent db ≠ none := by decide
    exact hne h
  · apply (oldGraph.rootGraft_eqv_iff_routing internalRootBatch
      (fun h => internalRootBatch_source h)).mpr
    change da ∈ terms ∧ db ∈ terms ∧ EqvOn terms
      (oldGraph.rootRouting internalRootBatch) (oldGraph.normalRoot da) (oldGraph.normalRoot db)
    rw [internalRootBatch_routing, old_root_da, old_root_db]
    exact ⟨by simp [mem_terms], by simp [mem_terms], by simp [mem_terms],
      by simp [mem_terms], cdb, Reach.head (by simp [recursiveRootBatch]) (Reach.refl _),
      Reach.refl _⟩

/-- A terminating selection can point back into its own old class. The
installed two-cycle proves that checking q alone is insufficient. -/
theorem raw_parent_termination_insufficient :
    ∃ q : T → Option T, Terminating q ∧
      (∀ {x y}, q x = some y → oldGraph.NF x) ∧
      ¬ Terminating (oldGraph.rootGraft q) := by
  let q : T → Option T := fun x => if x = cda then some da else none
  have edge : ∀ {x y}, q x = some y → x = cda ∧ y = da := by
    intro x y h
    dsimp only [q] at h
    split at h <;> simp_all
  have hterm : Terminating q := by
    apply Subrelation.wf (r := fun y x : T => (if y = cda then 1 else 0) <
      (if x = cda then 1 else 0)) ?_ (InvImage.wf (f := fun x : T =>
        if x = cda then 1 else 0) Nat.lt_wfRel.wf)
    intro y x h
    obtain ⟨rfl, rfl⟩ := edge h
    decide
  have hn : oldGraph.NF cda := by change oldParent cda = none; decide
  refine ⟨q, hterm, ?_, ?_⟩
  · intro x y h
    obtain ⟨rfl, _⟩ := edge h
    exact hn
  · intro h
    exact h.no_parent_cycle (oldGraph.rootGraft_root_edge q hn (by simp [q]))
      (Reach.head (oldGraph.rootGraft_old_edge q (by decide : oldGraph.par da = some cda))
        (Reach.refl _))

#check @internal_target_parent_control
#print axioms internal_target_parent_control
#check @raw_parent_termination_insufficient
#print axioms raw_parent_termination_insufficient

example : ¬ Terminating (oldGraph.rootGraft (fun x => if x = cda then some cda else none)) := by
  intro h
  have hn : oldGraph.NF cda := by change oldParent cda = none; decide
  have he := oldGraph.rootGraft_root_edge (fun x => if x = cda then some cda else none)
    hn (by simp : (if cda = cda then some cda else none) = some cda)
  exact h.no_parent_cycle he (Reach.refl _)

end Section7CyclicSliceControls

#check @ContextRepresentative
#check @CT.one_new_representatives_eq_of_coalgebra
#check @OneTermContextExtension
#check @OneTermContextExtension.base
#check @OneTermContextExtension.mem
#check @OneTermContextExtension.refl
#check @OneTermContextExtension.symm
#check @OneTermContextExtension.old_iff
#check @OneTermContextExtension.isolated_iff
#check @OneTermContextExtension.variable_iff
#check @OneTermContextExtension.trans
#check @OneTermContextExtension.of_context
#check @OneTermContextExtension.sigmaClosedOn
#check @OneTermContextExtension.least
#check @OneTermContextExtension.constructorCompatible
#check @PGraph.eqvOn_largerCarrier_iff
#check @PGraph.liftCarrier
#check @PGraph.liftCarrier_par
#check @PGraph.liftCarrier_nf
#check @PGraph.liftCarrier_tight
#check @PGraph.eqvOn_subset_of_parent
#check @PGraph.exists_contextInsertion
#check @OneTermContextExtension.downOn

#print axioms ContextRepresentative
#print axioms CT.one_new_representatives_eq_of_coalgebra
#print axioms OneTermContextExtension
#print axioms OneTermContextExtension.base
#print axioms OneTermContextExtension.mem
#print axioms OneTermContextExtension.refl
#print axioms OneTermContextExtension.symm
#print axioms OneTermContextExtension.old_iff
#print axioms OneTermContextExtension.isolated_iff
#print axioms OneTermContextExtension.variable_iff
#print axioms OneTermContextExtension.trans
#print axioms OneTermContextExtension.of_context
#print axioms OneTermContextExtension.sigmaClosedOn
#print axioms OneTermContextExtension.least
#print axioms OneTermContextExtension.constructorCompatible
#print axioms PGraph.eqvOn_largerCarrier_iff
#print axioms PGraph.liftCarrier
#print axioms PGraph.liftCarrier_par
#print axioms PGraph.liftCarrier_nf
#print axioms PGraph.liftCarrier_tight
#print axioms PGraph.eqvOn_subset_of_parent
#print axioms PGraph.exists_contextInsertion
#print axioms OneTermContextExtension.downOn

namespace OneNewTermControls

open Section7Active

private theorem enlarged_coalgebra : Coalgebra (outside :: terms) := by
  simpa [outside, terms, coalgebraOf, subterms, subtermsList,
    twice, once, wrap, constant] using coalgebra_coalgebraOf [outside]

private theorem old_refl (x : T) (hx : x ∈ terms) : E x x := EqvOn.refl hx

private theorem inserted_context : CT E outside once :=
  outside_to constant (by simp [mem_terms])

private theorem inserted_equal : OneTermContextExtension E outside outside constant := by
  refine Or.inr ⟨once, constant, Or.inr ⟨rfl, inserted_context⟩, ?_, Or.inl rfl⟩
  exact ⟨by simp [mem_terms], by simp [mem_terms], constant,
    reach_constant (by simp [mem_terms]), Reach.refl _⟩

private theorem inserted_not_context : ¬ CT E outside constant := by
  intro h
  rcases CT.unfold.mp h with he | ⟨f, xs, ys, _, hl, hr, _⟩
  · exact outside_new he.mem.1
  · have hheads : (Sum.inr () : Unit ⊕ Unit) = Sum.inl () :=
      (Term.app.inj hl).1.trans (Term.app.inj hr).1.symm
    cases hheads

example : OneTermContextExtension E outside outside constant ∧
    ¬ CT E outside constant := ⟨inserted_equal, inserted_not_context⟩

example : ∀ x y z,
    OneTermContextExtension E outside x y →
    OneTermContextExtension E outside y z →
    OneTermContextExtension E outside x z := by
  intro x y z hxy hyz
  exact OneTermContextExtension.trans terms_coalgebra enlarged_coalgebra
    old_closed (fun h => h.mem) old_refl (fun _ _ h => h.symm)
    (fun _ _ _ h₁ h₂ => h₁.trans h₂) outside_new hxy hyz

example : SigmaClosedOn (outside :: terms) (OneTermContextExtension E outside) :=
  OneTermContextExtension.sigmaClosedOn terms_coalgebra enlarged_coalgebra
    old_closed old_refl (fun _ _ h => h.symm) outside_new

example : ConstructorCompatible (OneTermContextExtension E outside) :=
  OneTermContextExtension.constructorCompatible terms_coalgebra enlarged_coalgebra
    old_closed (fun h => h.mem) old_refl (fun _ _ h => h.symm)
    (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    (graph.constructorCompatible_eqvOn terms_coalgebra rules_constructor) outside_new

example : OneTermContextExtension E outside once constant ↔ E once constant :=
  OneTermContextExtension.old_iff outside_new
    (by simp [mem_terms]) (by simp [mem_terms])

example : ¬ ∀ x y z : T,
    ((x = outside ∧ y = outside) ∨ CT E x y) →
    ((y = outside ∧ z = outside) ∨ CT E y z) →
    ((x = outside ∧ z = outside) ∨ CT E x z) := by
  intro htrans
  have hbase : E once constant :=
    ⟨by simp [mem_terms], by simp [mem_terms], constant,
      reach_constant (by simp [mem_terms]), Reach.refl _⟩
  rcases htrans outside once constant (Or.inr inserted_context)
    (Or.inr (CT.base hbase)) with ⟨_, hbad⟩ | hbad
  · exact (show constant ≠ outside by decide) hbad
  · exact inserted_not_context hbad

example : ¬ OneTermContextExtension E (.var ()) (.var ()) constant := by
  have hnew : (Term.var () : T) ∉ terms := by decide
  rw [OneTermContextExtension.variable_iff (fun h : E _ _ => h.mem) hnew]
  rintro (⟨_, hbad⟩ | hbad)
  · exact (show constant ≠ (.var () : T) by decide) hbad
  · exact hnew hbad.mem.1

example : OneTermContextExtension E (.var ()) (.var ()) (.var ()) :=
  OneTermContextExtension.refl old_refl (by simp)

example : ∃ beta : PGraph (outside :: terms) rules,
    EqvOn (outside :: terms) beta.par outside constant ∧
      beta.par once = graph.par once ∧
      SigmaClosedOn (outside :: terms) (EqvOn (outside :: terms) beta.par) := by
  obtain ⟨beta, _, hoff, heq, hclosed, _⟩ :=
    graph.exists_contextInsertion terms_coalgebra enlarged_coalgebra
      rules_constructor old_closed outside_new
  exact ⟨beta, (heq outside constant).mpr inserted_equal,
    hoff once (by decide), hclosed⟩

example : DownOn (outside :: terms) rules outside constant :=
  OneTermContextExtension.downOn terms_coalgebra enlarged_coalgebra
    rules_constructor graph old_closed outside_new inserted_equal

example : (graph.liftCarrier (fun _ hx => List.mem_cons_of_mem (.var ()) hx)).NF
    (.var () : T) := graph.liftCarrier_nf _ (by decide)

example : ¬ EqvOn ((.var () : T) :: terms)
    (graph.liftCarrier (fun _ hx => List.mem_cons_of_mem (.var ()) hx)).par
    (.var ()) constant := by
  change ¬ EqvOn ((.var () : T) :: terms) graph.par (.var ()) constant
  rw [graph.eqvOn_largerCarrier_iff (fun _ hx => List.mem_cons_of_mem (.var ()) hx)]
  rintro (⟨hbad, _⟩ | hbad)
  · exact (show (.var () : T) ≠ constant by decide) hbad
  · exact (show (.var () : T) ∉ terms by decide) hbad.mem.1

end OneNewTermControls
