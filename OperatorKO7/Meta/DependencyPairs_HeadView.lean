import OperatorKO7.Meta.DependencyPairs_FirstOrderEngine

/-!
# Caller-Supplied Head and Call-Head View

An internal term carrier supplies a root-head observation and a finite
collection of call heads. The collection is a `Finset`, so repeated occurrences
of one head collapse. This module constructs rule-level call-head records, a
graph, and SCC wrappers from those observations. Adequacy laws connecting the
observations to source syntax lie outside this interface.
-/

namespace OperatorKO7.DependencyPairsFragment

/-- Caller-supplied root-head and call-head observations for an internal term carrier. -/
class HasCallHeadView (τ σ : Type) [DecidableEq σ] where
  head? : τ → Option σ
  allHeads : τ → Finset σ

namespace HasCallHeadView

variable {τ σ : Type} [DecidableEq σ] [HasCallHeadView τ σ]

/-- Root head symbol from the minimal call-head view. -/
abbrev rootHead? : τ → Option σ := HasCallHeadView.head?

/-- Finite call-head collection returned by the supplied view. -/
abbrev callHeads : τ → Finset σ := HasCallHeadView.allHeads

end HasCallHeadView

/-- Head and call-head observations induced by the canonical `FOTerm` syntax. -/
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

/-- Rule-level call-head data from a raw engine exposing the two observations. -/
structure ExtractedHeadRuleNode (ρ σ : Type) [DecidableEq σ] where
  rule : ρ
  nodeKey : σ
  succKeys : Finset σ

/-- Finite rule engine exposing root-head and call-head observations. -/
structure FiniteHeadRuleEngine (σ : Type) [DecidableEq σ] where
  Rule : Type
  Term : Type
  termView : HasCallHeadView Term σ
  rules : Array Rule
  lhs : Rule → Term
  rhs : Rule → Term

/-- Typeclass-level finite engine view using only supplied root-head and call-head data. -/
class HasFiniteHeadRuleView (ε σ : Type) [DecidableEq σ] where
  Rule : Type
  Term : Type
  termView : HasCallHeadView Term σ
  rules : ε → Array Rule
  lhs : Rule → Term
  rhs : Rule → Term

/-- Adapter from a canonical first-order engine view to the smaller head-view engine view. -/
def finiteHeadRuleViewOfFirstOrder
    (ε σ ν : Type) [DecidableEq σ] [H : HasFiniteFirstOrderView ε σ ν] :
    HasFiniteHeadRuleView ε σ where
  Rule := H.Rule
  Term := FOTerm σ ν
  termView := instHasCallHeadViewFOTerm σ ν
  rules := H.rules
  lhs := H.lhs
  rhs := H.rhs

/-- Adapter from a raw first-order engine view to the smaller head-view engine view. -/
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

namespace FiniteHeadRuleEngine

variable {σ : Type} [DecidableEq σ] (E : FiniteHeadRuleEngine σ)

/-- Defined heads of the raw head-view engine. -/
def definedHeads : Finset σ :=
  let _ := E.termView
  E.rules.foldl
    (fun acc r =>
      match HasCallHeadView.rootHead? (E.lhs r) with
      | some f => insert f acc
      | none => acc)
    ∅

/-- Extract one call-graph node from the raw head-view engine. -/
def extractNode? (defined : Finset σ) (r : E.Rule) : Option (ExtractedHeadRuleNode E.Rule σ) :=
  let _ := E.termView
  match HasCallHeadView.rootHead? (E.lhs r) with
  | none => none
  | some f =>
      some
        { rule := r
          nodeKey := f
          succKeys := (HasCallHeadView.callHeads (E.rhs r)).filter (· ∈ defined) }

/-- Call-head records constructed from the raw head-view engine. -/
def extractedNodes : Array (ExtractedHeadRuleNode E.Rule σ) :=
  let defined := E.definedHeads
  E.rules.filterMap (E.extractNode? defined)

/-- Call graph constructed from the raw head-view engine. -/
def extractedCallGraph : FiniteExtractedCallGraph σ :=
  FiniteExtractedCallGraph.ofArrayMap
    (nodes := E.extractedNodes)
    (nodeKey := ExtractedHeadRuleNode.nodeKey)
    (succKeys := ExtractedHeadRuleNode.succKeys)

/-- Direct SCC search on the raw head-view engine. -/
noncomputable abbrev findNontrivialSCCPair? :
    Option (E.extractedCallGraph.Node × E.extractedCallGraph.Node) :=
  E.extractedCallGraph.findNontrivialSCCPair?

/-- SCC existence predicate on the raw head-view engine. -/
abbrev HasNontrivialSCC : Prop :=
  E.extractedCallGraph.HasNontrivialSCC

/-- Standard SCC witness on the raw head-view engine. -/
noncomputable abbrev toSCCCycle (h : E.HasNontrivialSCC) :
    SCCCycle E.extractedCallGraph.Node :=
  E.extractedCallGraph.toSCCCycle h

theorem hasNontrivialSCC_iff_exists_findNontrivialSCCPair? :
    E.HasNontrivialSCC ↔
      ∃ p : E.extractedCallGraph.Node × E.extractedCallGraph.Node,
        E.findNontrivialSCCPair? = some p := by
  simpa [FiniteHeadRuleEngine.HasNontrivialSCC, FiniteHeadRuleEngine.findNontrivialSCCPair?,
    FiniteHeadRuleEngine.extractedCallGraph] using
    (FiniteExtractedCallGraph.hasNontrivialSCC_iff_exists_findNontrivialSCCPair?
      (G := E.extractedCallGraph))

theorem not_globalOrients_of_source_le_target_of_findNontrivialSCCPair?
    {m : E.extractedCallGraph.Node → Nat}
    {p : E.extractedCallGraph.Node × E.extractedCallGraph.Node}
    (hfind : E.findNontrivialSCCPair? = some p)
    (hge : m p.1 ≤ m p.2) :
    ¬ GlobalOrients E.extractedCallGraph.toFiniteCallGraph.Edge m (· < ·) := by
  simpa [FiniteHeadRuleEngine.findNontrivialSCCPair?, FiniteHeadRuleEngine.extractedCallGraph] using
    (FiniteExtractedCallGraph.not_globalOrients_of_source_le_target_of_findNontrivialSCCPair?
      (G := E.extractedCallGraph) hfind hge)

theorem not_globalOrients_of_source_le_target_of_hasNontrivialSCC
    {m : E.extractedCallGraph.Node → Nat}
    (h : E.HasNontrivialSCC)
    (hge : m (E.toSCCCycle h).source ≤ m (E.toSCCCycle h).target) :
    ¬ GlobalOrients E.extractedCallGraph.toFiniteCallGraph.Edge m (· < ·) := by
  simpa [FiniteHeadRuleEngine.HasNontrivialSCC, FiniteHeadRuleEngine.toSCCCycle,
    FiniteHeadRuleEngine.extractedCallGraph] using
    (FiniteExtractedCallGraph.not_globalOrients_of_source_le_target_of_hasNontrivialSCC
      (G := E.extractedCallGraph) h hge)

/-- Any packaged canonical first-order engine induces the smaller head-view engine. -/
def ofFiniteFirstOrderEngine {ν : Type} (F : FiniteFirstOrderEngine σ ν) : FiniteHeadRuleEngine σ where
  Rule := F.Rule
  Term := FOTerm σ ν
  termView := instHasCallHeadViewFOTerm σ ν
  rules := F.rules
  lhs := F.lhs
  rhs := F.rhs

/-- Any typeclass-exposed first-order engine induces the smaller head-view engine. -/
def ofFirstOrderView {ε ν : Type} [HasFiniteFirstOrderView ε σ ν] (e : ε) :
    FiniteHeadRuleEngine σ :=
  ofFiniteFirstOrderEngine
    (HasFiniteFirstOrderView.toFiniteFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) e)

/-- Any raw first-order engine view induces the smaller head-view engine. -/
def ofRawFirstOrderView {ε ν : Type} [HasFiniteRawFirstOrderView ε σ ν] (e : ε) :
    FiniteHeadRuleEngine σ := by
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

end FiniteHeadRuleEngine

namespace HasFiniteHeadRuleView

variable {ε σ : Type} [DecidableEq σ] [H : HasFiniteHeadRuleView ε σ]

/-- Package a typeclass-level head-view engine as the canonical finite head-rule engine. -/
def toFiniteHeadRuleEngine (e : ε) : FiniteHeadRuleEngine σ where
  Rule := H.Rule
  Term := H.Term
  termView := H.termView
  rules := H.rules e
  lhs := H.lhs
  rhs := H.rhs

/-- Defined heads recovered directly from a typeclass-level head-view engine. -/
def definedHeads (e : ε) : Finset σ :=
  (toFiniteHeadRuleEngine e).definedHeads

/-- Call-head records constructed from a typeclass-level head-view engine. -/
def extractedNodes (e : ε) : Array (ExtractedHeadRuleNode H.Rule σ) :=
  (toFiniteHeadRuleEngine e).extractedNodes

/-- Call graph constructed from a typeclass-level head-view engine. -/
def extractedCallGraph (e : ε) : FiniteExtractedCallGraph σ :=
  (toFiniteHeadRuleEngine e).extractedCallGraph

end HasFiniteHeadRuleView

end OperatorKO7.DependencyPairsFragment
