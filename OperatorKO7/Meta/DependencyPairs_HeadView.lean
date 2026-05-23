
/-!
# Minimal Head/Call-Head View for DP Extraction

This module removes the need for a full conversion into the canonical `FOTerm` syntax when
only dependency-pair extraction matters. An internal term syntax can expose just:

- its root head symbol, and
- the set of call heads appearing anywhere in the term.

That is already enough to recover the extracted call graph and the finite-SCC search /
contradiction surface.
-/

namespace OperatorKO7.DependencyPairsFragment

abbrev FiniteFirstOrderProcedure := FiniteFirstOrderEngine

namespace HasFiniteFirstOrderView

abbrev toFiniteFirstOrderProcedure {ε σ ν : Type} [DecidableEq σ]
    [HasFiniteFirstOrderView ε σ ν] (E : ε) :
    FiniteFirstOrderProcedure σ ν :=
  toFiniteFirstOrderEngine E

end HasFiniteFirstOrderView

/-- Minimal interface needed for dependency-pair call-head extraction from an internal term
syntax. -/
class HasCallHeadView (τ σ : Type) [DecidableEq σ] where
  head? : τ → Option σ
  allHeads : τ → Finset σ

namespace HasCallHeadView

variable {τ σ : Type} [DecidableEq σ] [HasCallHeadView τ σ]

/-- Root head symbol from the minimal call-head view. -/
abbrev rootHead? : τ → Option σ := HasCallHeadView.head?

/-- All recursive call heads from the minimal call-head view. -/
abbrev callHeads : τ → Finset σ := HasCallHeadView.allHeads

end HasCallHeadView

/-- The canonical `FOTerm` syntax already carries the needed head / call-head data. -/
instance instHasCallHeadViewFOTerm (σ ν : Type) [DecidableEq σ] :
    HasCallHeadView (FOTerm σ ν) σ where
  head? := FOTerm.head?
  allHeads := FOTerm.allHeads

/-- Explicit call-head view induced by a raw first-order term view. -/
def headViewOfFirstOrderTermView
    (τ σ ν : Type) [DecidableEq σ] [HasFirstOrderTermView τ σ ν] :
    HasCallHeadView τ σ where
  head? := by
    intro t
    exact FOTerm.head? (HasFirstOrderTermView.toFOTerm (τ := τ) (σ := σ) (ν := ν) t)
  allHeads := by
    intro t
    exact FOTerm.allHeads (HasFirstOrderTermView.toFOTerm (τ := τ) (σ := σ) (ν := ν) t)

/-- Extracted node data from a raw rule procedure exposing only head / call-head structure. -/
structure ExtractedHeadRuleNode (ρ σ : Type) [DecidableEq σ] where
  rule : ρ
  nodeKey : σ
  succKeys : Finset σ

/-- Finite rule procedure exposing only the head / call-head data needed by DP extraction. -/
structure FiniteHeadRuleProcedure (σ : Type) [DecidableEq σ] where
  Rule : Type
  Term : Type
  termView : HasCallHeadView Term σ
  rules : Array Rule
  lhs : Rule → Term
  rhs : Rule → Term

/-- Typeclass-level finite procedure view using only root-head and recursive-call-head data. -/
class HasFiniteHeadRuleView (ε σ : Type) [DecidableEq σ] where
  Rule : Type
  Term : Type
  termView : HasCallHeadView Term σ
  rules : ε → Array Rule
  lhs : Rule → Term
  rhs : Rule → Term

/-- Adapter from a canonical first-order procedure view to the smaller head-view procedure view. -/
def finiteHeadRuleViewOfFirstOrder
    (ε σ ν : Type) [DecidableEq σ] [H : HasFiniteFirstOrderView ε σ ν] :
    HasFiniteHeadRuleView ε σ where
  Rule := H.Rule
  Term := FOTerm σ ν
  termView := instHasCallHeadViewFOTerm σ ν
  rules := H.rules
  lhs := H.lhs
  rhs := H.rhs

/-- Adapter from a raw first-order procedure view to the smaller head-view procedure view. -/
def finiteHeadRuleViewOfRaw
    (ε σ ν : Type) [DecidableEq σ] [H : HasFiniteRawFirstOrderView ε σ ν] :
    HasFiniteHeadRuleView ε σ where
  Rule := H.Rule
  Term := H.Term
  termView := by
    let _ : HasFirstOrderTermView H.Term σ ν := H.termView
    exact headViewOfFirstOrderTermView H.Term σ ν
  rules := H.rules
  lhs := H.lhs
  rhs := H.rhs

namespace FiniteHeadRuleProcedure

variable {σ : Type} [DecidableEq σ] (E : FiniteHeadRuleProcedure σ)

/-- Defined heads of the raw head-view procedure. -/
def definedHeads : Finset σ :=
  let _ := E.termView
  E.rules.foldl
    (fun acc r =>
      match HasCallHeadView.rootHead? (E.lhs r) with
      | some f => insert f acc
      | none => acc)
    ∅

/-- Extract one call-graph node from the raw head-view procedure. -/
def extractNode? (defined : Finset σ) (r : E.Rule) : Option (ExtractedHeadRuleNode E.Rule σ) :=
  let _ := E.termView
  match HasCallHeadView.rootHead? (E.lhs r) with
  | none => none
  | some f =>
      some
        { rule := r
          nodeKey := f
          succKeys := (HasCallHeadView.callHeads (E.rhs r)).filter (· ∈ defined) }

/-- Extracted call-head nodes of the raw head-view procedure. -/
def extractedNodes : Array (ExtractedHeadRuleNode E.Rule σ) :=
  let defined := E.definedHeads
  E.rules.filterMap (E.extractNode? defined)

/-- Extracted call graph of the raw head-view procedure. -/
def extractedCallGraph : FiniteExtractedCallGraph σ :=
  FiniteExtractedCallGraph.ofArrayMap
    (nodes := E.extractedNodes)
    (nodeKey := ExtractedHeadRuleNode.nodeKey)
    (succKeys := ExtractedHeadRuleNode.succKeys)

/-- Direct SCC search on the raw head-view procedure. -/
noncomputable abbrev findNontrivialSCCPair? :
    Option (E.extractedCallGraph.Node × E.extractedCallGraph.Node) :=
  E.extractedCallGraph.findNontrivialSCCPair?

/-- SCC existence predicate on the raw head-view procedure. -/
abbrev HasNontrivialSCC : Prop :=
  E.extractedCallGraph.HasNontrivialSCC

/-- Standard SCC witness on the raw head-view procedure. -/
noncomputable abbrev toSCCCycle (h : E.HasNontrivialSCC) :
    SCCCycle E.extractedCallGraph.Node :=
  E.extractedCallGraph.toSCCCycle h

theorem hasNontrivialSCC_iff_exists_findNontrivialSCCPair? :
    E.HasNontrivialSCC ↔
      ∃ p : E.extractedCallGraph.Node × E.extractedCallGraph.Node,
        E.findNontrivialSCCPair? = some p := by
  simpa [FiniteHeadRuleProcedure.HasNontrivialSCC, FiniteHeadRuleProcedure.findNontrivialSCCPair?,
    FiniteHeadRuleProcedure.extractedCallGraph] using
    (FiniteExtractedCallGraph.hasNontrivialSCC_iff_exists_findNontrivialSCCPair?
      (G := E.extractedCallGraph))

theorem not_globalOrients_of_source_le_target_of_findNontrivialSCCPair?
    {m : E.extractedCallGraph.Node → Nat}
    {p : E.extractedCallGraph.Node × E.extractedCallGraph.Node}
    (hfind : E.findNontrivialSCCPair? = some p)
    (hge : m p.1 ≤ m p.2) :
    ¬ GlobalOrients E.extractedCallGraph.toFiniteCallGraph.Edge m (· < ·) := by
  simpa [FiniteHeadRuleProcedure.findNontrivialSCCPair?, FiniteHeadRuleProcedure.extractedCallGraph] using
    (FiniteExtractedCallGraph.not_globalOrients_of_source_le_target_of_findNontrivialSCCPair?
      (G := E.extractedCallGraph) hfind hge)

theorem not_globalOrients_of_source_le_target_of_hasNontrivialSCC
    {m : E.extractedCallGraph.Node → Nat}
    (h : E.HasNontrivialSCC)
    (hge : m (E.toSCCCycle h).source ≤ m (E.toSCCCycle h).target) :
    ¬ GlobalOrients E.extractedCallGraph.toFiniteCallGraph.Edge m (· < ·) := by
  simpa [FiniteHeadRuleProcedure.HasNontrivialSCC, FiniteHeadRuleProcedure.toSCCCycle,
    FiniteHeadRuleProcedure.extractedCallGraph] using
    (FiniteExtractedCallGraph.not_globalOrients_of_source_le_target_of_hasNontrivialSCC
      (G := E.extractedCallGraph) h hge)

/-- Any packaged canonical first-order procedure induces the smaller head-view procedure. -/
def ofFiniteFirstOrderProcedure {ν : Type} (F : FiniteFirstOrderProcedure σ ν) : FiniteHeadRuleProcedure σ where
  Rule := F.Rule
  Term := FOTerm σ ν
  termView := instHasCallHeadViewFOTerm σ ν
  rules := F.rules
  lhs := F.lhs
  rhs := F.rhs

/-- Any typeclass-exposed first-order procedure induces the smaller head-view procedure. -/
def ofFirstOrderView {ε ν : Type} [HasFiniteFirstOrderView ε σ ν] (e : ε) :
    FiniteHeadRuleProcedure σ :=
  ofFiniteFirstOrderProcedure
    (HasFiniteFirstOrderView.toFiniteFirstOrderProcedure (ε := ε) (σ := σ) (ν := ν) e)

/-- Any raw first-order procedure view induces the smaller head-view procedure. -/
def ofRawFirstOrderView {ε ν : Type} [HasFiniteRawFirstOrderView ε σ ν] (e : ε) :
    FiniteHeadRuleProcedure σ := by
  let H := (inferInstance : HasFiniteRawFirstOrderView ε σ ν)
  let _ : HasFirstOrderTermView H.Term σ ν := H.termView
  let termView : HasCallHeadView H.Term σ := headViewOfFirstOrderTermView H.Term σ ν
  exact
    { Rule := H.Rule
      Term := H.Term
      termView := termView
      rules := H.rules e
      lhs := H.lhs
      rhs := H.rhs }

end FiniteHeadRuleProcedure

namespace HasFiniteHeadRuleView

variable {ε σ : Type} [DecidableEq σ] [H : HasFiniteHeadRuleView ε σ]

/-- Package a typeclass-level head-view procedure as the canonical finite head-rule procedure. -/
def toFiniteHeadRuleProcedure (e : ε) : FiniteHeadRuleProcedure σ where
  Rule := H.Rule
  Term := H.Term
  termView := H.termView
  rules := H.rules e
  lhs := H.lhs
  rhs := H.rhs

/-- Defined heads recovered directly from a typeclass-level head-view procedure. -/
def definedHeads (e : ε) : Finset σ :=
  (toFiniteHeadRuleProcedure e).definedHeads

/-- Extracted nodes recovered directly from a typeclass-level head-view procedure. -/
def extractedNodes (e : ε) : Array (ExtractedHeadRuleNode H.Rule σ) :=
  (toFiniteHeadRuleProcedure e).extractedNodes

/-- Extracted call graph recovered directly from a typeclass-level head-view procedure. -/
def extractedCallGraph (e : ε) : FiniteExtractedCallGraph σ :=
  (toFiniteHeadRuleProcedure e).extractedCallGraph

end HasFiniteHeadRuleView

end OperatorKO7.DependencyPairsFragment
