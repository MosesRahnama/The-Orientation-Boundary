import Mathlib.Tactic
import OperatorKO7.Meta.Rewriting.Rewrite
import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore
import OperatorKO7.Meta.Methods.OrientationClosure.DependencyPairSoundness

/-!
# Method rows for the graph-calculi group of the Orientation Boundary closeout

Tier C method rows whose carriers leave the first-order term algebra. The subject is the free
recursor `recur(b, s, zero) → b`, `recur(b, s, succ n) → wrap(s, recur(b, s, n))`, translated to
graph rewriting, and the three methods are weighted type graphs (Bruggink, König, Nolte and
Zantema, ICGT 2015), generalized weighted type graphs over ordered semirings (same source), and
sharing-aware quasi-interpretations (Bonfante, Marion and Moyen, Theoretical Computer Science 2011).

Every row follows the P5 row contract: `Data`, `Laws`, `Accepts`, `Result` with a verdict line, a
`Witness` with `_laws`, `_result`, `_feature`, and `_mutation`, a `_sound` theorem, and a `_scope`
definition naming the omitted generality. Relation: the free schema of `SchemaCore`, never a
concrete KO7 term. External trust: none. Mathlib only.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness

universe u

/-! ## Shared native graph carries -/

/-- Arity of the four free-signature symbols. -/
def symArity : FreeSym → Nat
  | .zero => 0
  | .succ => 1
  | .wrap => 2
  | .recur => 3

/-- Arity of the zero symbol. -/
theorem symArity_zero : symArity FreeSym.zero = 0 := rfl

/-- Arity of the successor symbol. -/
theorem symArity_succ : symArity FreeSym.succ = 1 := rfl

/-- Arity of the wrapper symbol. -/
theorem symArity_wrap : symArity FreeSym.wrap = 2 := rfl

/-- Arity of the recursor symbol. -/
theorem symArity_recur : symArity FreeSym.recur = 3 := rfl

/-- A hypergraph over the free signature: nodes `Fin nodeCount`; each hyperedge carries one node
per argument position and one result node, so symbol occurrences share nodes. -/
structure Hypergraph where
  /-- Number of nodes. -/
  nodeCount : Nat
  /-- The hyperedges: a symbol, its argument attachments, and its result node. -/
  edges : List (Σ s : FreeSym, (Fin (symArity s) → Fin nodeCount) × Fin nodeCount)

/-- One DPO rule of a graph transformation system: a left side and a right side. -/
structure DPRule where
  /-- Left side of the rule. -/
  lhs : Hypergraph
  /-- Right side of the rule. -/
  rhs : Hypergraph

/-- A weighted type graph with at least two nodes, and a weight for every symbol occurrence
pattern of the free signature. -/
structure TypeGraph where
  /-- Number of type nodes. -/
  nodeCount : Nat
  /-- At least two nodes, so the graph is not the one-node flower. -/
  two_le : 2 ≤ nodeCount
  /-- Weight of a symbol occurrence from its argument types and result type. -/
  edgeWeight : (s : FreeSym) → (Fin (symArity s) → Fin nodeCount) → Fin nodeCount → Nat

/-- A weight algebra: the ordered semiring of Definition 5 of the source, with commutative
addition `⊕` and multiplication `⊗`, the strongly ordered addition law, and a well-founded strict
order. -/
structure WeightAlgebra where
  /-- Carrier of the semiring. -/
  W : Type
  /-- Non-strict order. -/
  le : W → W → Prop
  /-- Strict order. -/
  lt : W → W → Prop
  /-- Reflexivity. -/
  le_refl : ∀ x, le x x
  /-- Transitivity. -/
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  /-- Antisymmetry. -/
  le_antisymm : ∀ {x y}, le x y → le y x → x = y
  /-- Totality. -/
  le_total : ∀ x y, le x y ∨ le y x
  /-- The strict order is the strict part of the non-strict order. -/
  lt_iff : ∀ {x y}, lt x y ↔ le x y ∧ ¬ le y x
  /-- Semiring addition `⊕`. -/
  add : W → W → W
  /-- Semiring multiplication `⊗`. -/
  mul : W → W → W
  /-- Additive unit `0`. -/
  zero : W
  /-- Multiplicative unit `1`. -/
  one : W
  /-- Addition is commutative. -/
  add_comm : ∀ x y, add x y = add y x
  /-- Addition is associative. -/
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  /-- Zero is the additive unit. -/
  zero_add : ∀ x, add zero x = x
  /-- Zero is the additive unit on the right. -/
  add_zero : ∀ x, add x zero = x
  /-- Multiplication is commutative. -/
  mul_comm : ∀ x y, mul x y = mul y x
  /-- Multiplication is associative. -/
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  /-- One is the multiplicative unit. -/
  one_mul : ∀ x, mul one x = x
  /-- One is the multiplicative unit on the right. -/
  mul_one : ∀ x, mul x one = x
  /-- Zero annihilates multiplication. -/
  mul_zero : ∀ x, mul zero x = zero
  /-- Multiplication distributes over addition. -/
  left_distrib : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  /-- Addition is monotone in both arguments. -/
  add_le_add : ∀ {x y u z}, le x y → le u z → le (add x u) (add y z)
  /-- Multiplication is monotone in its right argument. -/
  mul_le_mul_left : ∀ {x y}, le x y → ∀ z, le (mul z x) (mul z y)
  /-- Strong orderedness: strictly larger summands give a strictly larger sum. -/
  add_lt_add : ∀ {x y z u}, lt x y → lt z u → lt (add x z) (add y u)
  /-- The strict order is well founded. -/
  lt_wf : WellFounded lt

/-- The source's `S<`: weights that preserve strict inequality under multiplication. -/
def StrictPreserving (A : WeightAlgebra) (c : A.W) : Prop :=
  ∀ {a b : A.W}, A.lt a b → A.lt (A.mul c a) (A.mul c b)

/-- Relative termination from a strict ranking and a terminating weak part.  Strict steps lower
the first component.  Weak steps either lower it or stay in one fibre, where well-foundedness of
the weak relation supplies the second component. -/
theorem WeightAlgebra.wellFounded_union_of_strict_measure_and_weak
    (A : WeightAlgebra) {α : Type*} (m : α → A.W)
    (strictStep weakStep : α → α → Prop)
    (hWeak : WellFounded (fun y x : α => weakStep x y))
    (hStrict : ∀ {x y : α}, strictStep x y → A.lt (m y) (m x))
    (hNoninc : ∀ {x y : α}, weakStep x y → A.le (m y) (m x)) :
    WellFounded (fun y x : α => strictStep x y ∨ weakStep x y) := by
  refine Subrelation.wf ?_
    (InvImage.wf (fun x : α => (m x, x)) (WellFounded.prod_lex A.lt_wf hWeak))
  intro y x hxy
  rcases hxy with hStrictStep | hWeakStep
  · exact Prod.lex_def.2 (Or.inl (hStrict hStrictStep))
  · by_cases hlt : A.lt (m y) (m x)
    · exact Prod.lex_def.2 (Or.inl hlt)
    · have hReverse : A.le (m x) (m y) := by
        by_contra hNotReverse
        exact hlt (A.lt_iff.2 ⟨hNoninc hWeakStep, hNotReverse⟩)
      have heq : m y = m x := A.le_antisymm (hNoninc hWeakStep) hReverse
      exact Prod.lex_def.2 (Or.inr ⟨heq, hWeakStep⟩)

/-- The arithmetic semiring on the natural numbers, the source's strictly ordered instance. -/
abbrev arithWeight : WeightAlgebra where
  W := Nat
  le := fun a b => a ≤ b
  lt := fun a b => a < b
  le_refl := Nat.le_refl
  le_trans := fun h1 h2 => Nat.le_trans h1 h2
  le_antisymm := fun h1 h2 => Nat.le_antisymm h1 h2
  le_total := Nat.le_total
  lt_iff := by
    intro x y
    constructor
    · intro h
      exact ⟨le_of_lt h, not_le_of_gt h⟩
    · intro h
      exact lt_of_le_of_ne h.1 (fun heq => h.2 (le_of_eq heq.symm))
  add := fun a b => a + b
  mul := fun a b => a * b
  zero := 0
  one := 1
  add_comm := Nat.add_comm
  add_assoc := Nat.add_assoc
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  mul_comm := Nat.mul_comm
  mul_assoc := Nat.mul_assoc
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  mul_zero := Nat.zero_mul
  left_distrib := Nat.left_distrib
  add_le_add := fun h1 h2 => Nat.add_le_add h1 h2
  mul_le_mul_left := fun {_ _} h z => Nat.mul_le_mul_left z h
  add_lt_add := fun h1 h2 => Nat.add_lt_add h1 h2
  lt_wf := Nat.lt_wfRel.wf

/-- A generalized weighted type graph over a weight algebra: at least two type nodes and a weight
in the algebra for every symbol occurrence pattern. -/
structure GeneralizedTypeGraph (A : WeightAlgebra) where
  /-- Number of type nodes. -/
  nodeCount : Nat
  /-- At least two nodes. -/
  two_le : 2 ≤ nodeCount
  /-- Weight of a symbol occurrence from its argument types and result type. -/
  edgeWeight : (s : FreeSym) → (Fin (symArity s) → Fin nodeCount) → Fin nodeCount → A.W

/-- Shared term graphs: a leaf, a binary node, and an explicit sharing node. -/
inductive SharedTerm where
  /-- A leaf constant. -/
  | leaf : SharedTerm
  /-- A binary node. -/
  | node : SharedTerm → SharedTerm → SharedTerm
  /-- A sharing node. -/
  | shared : SharedTerm → SharedTerm

/-! ## Row data -/

/-- Native data of `weightedTypeGraphEscape`: the weighted type graph, the rule list of the graph
transformation system, its native step relation, and the read-back relation to closed free terms. -/
structure weightedTypeGraphEscapeData where
  /-- The weighted type graph. -/
  typeGraph : TypeGraph
  /-- The rules of the graph transformation system. -/
  rules : List DPRule
  /-- The native step relation. -/
  step : Hypergraph → Hypergraph → Prop
  /-- The read-back relation to closed free terms. -/
  readBack : Hypergraph → FreeTerm Empty → Prop

/-- Native data of `generalizedWeightedTypeGraphs`: the weight algebra, the generalized weighted
type graph, the native weight aggregation, the rule list, the native step relation, and the
read-back relation. -/
structure generalizedWeightedTypeGraphsData where
  /-- The weight algebra. -/
  algebra : WeightAlgebra
  /-- The generalized weighted type graph. -/
  typeGraph : GeneralizedTypeGraph algebra
  /-- The native graph weight: the minimum over typings of the edge product. -/
  graphWeight : Hypergraph → algebra.W
  /-- The rules of the graph transformation system. -/
  rules : List DPRule
  /-- The native step relation. -/
  step : Hypergraph → Hypergraph → Prop
  /-- The read-back relation to closed free terms. -/
  readBack : Hypergraph → FreeTerm Empty → Prop

/-- Native data of `quasiInterpretationsSharingAware`: the weakly monotone assignment, the native
graph execution relation, and the read-back to closed free terms. -/
structure quasiInterpretationsSharingAwareData where
  /-- The quasi-interpretation. -/
  eval : SharedTerm → Nat
  /-- The native graph execution relation. -/
  exec : SharedTerm → SharedTerm → Prop
  /-- The read-back to closed free terms. -/
  readBack : SharedTerm → FreeTerm Empty

/-! ## Shared graph operations and the tropical weight -/

namespace Hypergraph

/-- Shift every node of a hypergraph by `k`. -/
def shift (k : Nat) (H : Hypergraph) : Hypergraph where
  nodeCount := k + H.nodeCount
  edges := H.edges.map (fun e =>
    ⟨e.1, (fun i => Fin.natAdd k (e.2.1 i)), Fin.natAdd k e.2.2⟩)

/-- The disjoint sum of two hypergraphs. -/
def sum (C H : Hypergraph) : Hypergraph where
  nodeCount := C.nodeCount + H.nodeCount
  edges := C.edges.map (fun e =>
      ⟨e.1, (fun i => Fin.castAdd H.nodeCount (e.2.1 i)), Fin.castAdd H.nodeCount e.2.2⟩)
    ++ (shift C.nodeCount H).edges

end Hypergraph

namespace TypeGraph

/-- The flower node, the first of the at least two nodes. -/
def flower (T : TypeGraph) : Fin T.nodeCount := ⟨0, by have h := T.two_le; omega⟩

end TypeGraph

/-- The empty attachment family. -/
def noAtt {n : Nat} : Fin 0 → Fin n := fun i => i.elim0

/-- One attachment. -/
def oneAtt {n : Nat} (a : Fin n) : Fin 1 → Fin n := fun _ => a

/-- Two attachments. -/
def twoAtt {n : Nat} (a b : Fin n) : Fin 2 → Fin n := fun i => if i = 0 then a else b

/-- Three attachments. -/
def threeAtt {n : Nat} (a b c : Fin n) : Fin 3 → Fin n :=
  fun i => if i = 0 then a else if i = 1 then b else c

/-- Weight of one hyperedge under a typing into a type graph. -/
def edgeWeightAt (T : TypeGraph) {H : Hypergraph} (φ : Fin H.nodeCount → Fin T.nodeCount)
    (e : Σ s : FreeSym, (Fin (symArity s) → Fin H.nodeCount) × Fin H.nodeCount) : Nat :=
  T.edgeWeight e.1 (fun i => φ (e.2.1 i)) (φ e.2.2)

/-- The summed edge weights of a hypergraph under a typing. -/
def edgeSum (T : TypeGraph) (H : Hypergraph) (φ : Fin H.nodeCount → Fin T.nodeCount) : Nat :=
  (H.edges.map (edgeWeightAt T φ)).sum

/-- The sum of a concatenated list of natural numbers. -/
theorem sum_append_nat (l₁ l₂ : List Nat) : (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  induction l₁ with
  | nil => simp
  | cons a as ih => simp [ih, Nat.add_assoc]

/-- The weight of a hypergraph: the minimum over its typings of the summed edge weights. -/
def graphWeight (T : TypeGraph) (H : Hypergraph) : Nat :=
  ((Finset.univ : Finset (Fin H.nodeCount → Fin T.nodeCount)).image
      (fun φ => edgeSum T H φ)).min'
    ⟨edgeSum T H (fun _ => TypeGraph.flower T),
      Finset.mem_image.mpr ⟨(fun _ => TypeGraph.flower T), Finset.mem_univ _, rfl⟩⟩

theorem graphWeight_le (T : TypeGraph) (H : Hypergraph)
    (φ : Fin H.nodeCount → Fin T.nodeCount) : graphWeight T H ≤ edgeSum T H φ :=
  (Finset.isLeast_min' _ _).2 (Finset.mem_image.mpr ⟨φ, Finset.mem_univ φ, rfl⟩)

theorem graphWeight_attained (T : TypeGraph) (H : Hypergraph) :
    ∃ φ : Fin H.nodeCount → Fin T.nodeCount, edgeSum T H φ = graphWeight T H := by
  have hmem : graphWeight T H ∈
      (Finset.univ : Finset (Fin H.nodeCount → Fin T.nodeCount)).image
        (fun φ => edgeSum T H φ) := (Finset.isLeast_min' _ _).1
  rw [Finset.mem_image] at hmem
  obtain ⟨φ, -, hφ⟩ := hmem
  exact ⟨φ, hφ⟩

/-- The edge sums split over the disjoint sum of two hypergraphs. -/
theorem edgeSum_sum (T : TypeGraph) (C H : Hypergraph)
    (φC : Fin C.nodeCount → Fin T.nodeCount) (φH : Fin H.nodeCount → Fin T.nodeCount) :
    edgeSum T (Hypergraph.sum C H) (Fin.append φC φH) = edgeSum T C φC + edgeSum T H φH := by
  unfold edgeSum Hypergraph.sum
  rw [List.map_append, sum_append_nat]
  congr 1
  · rw [List.map_map]
    congr 1
    refine List.map_congr_left (fun e _ => ?_)
    simp only [Function.comp_apply, edgeWeightAt]
    have harg : (fun i => Fin.append φC φH (Fin.castAdd H.nodeCount (e.2.1 i)))
        = fun i => φC (e.2.1 i) := by
      funext i
      exact Fin.append_left φC φH (e.2.1 i)
    have hres : Fin.append φC φH (Fin.castAdd H.nodeCount e.2.2) = φC e.2.2 :=
      Fin.append_left φC φH e.2.2
    rw [harg, hres]
  · unfold Hypergraph.shift
    rw [List.map_map]
    congr 1
    refine List.map_congr_left (fun e _ => ?_)
    simp only [Function.comp_apply, edgeWeightAt]
    have harg : (fun i => Fin.append φC φH (Fin.natAdd C.nodeCount (e.2.1 i)))
        = fun i => φH (e.2.1 i) := by
      funext i
      exact Fin.append_right φC φH (e.2.1 i)
    have hres : Fin.append φC φH (Fin.natAdd C.nodeCount e.2.2) = φH e.2.2 :=
      Fin.append_right φC φH e.2.2
    rw [harg, hres]

/-- The edge sums of a disjoint sum restrict to the edge sums of the two components. -/
theorem edgeSum_sum_split (T : TypeGraph) (C H : Hypergraph)
    (φ : Fin (C.nodeCount + H.nodeCount) → Fin T.nodeCount) :
    edgeSum T (Hypergraph.sum C H) φ =
      edgeSum T C (fun i => φ (Fin.castAdd H.nodeCount i)) +
        edgeSum T H (fun i => φ (Fin.natAdd C.nodeCount i)) := by
  unfold edgeSum Hypergraph.sum
  rw [List.map_append, sum_append_nat]
  congr 1
  · rw [List.map_map]
    rfl
  · unfold Hypergraph.shift
    rw [List.map_map]
    rfl

/-- The weight of a disjoint sum is the sum of the weights: the minimum of the sum of the two
independent typings is the sum of the minima. -/
theorem graphWeight_sum (T : TypeGraph) (C H : Hypergraph) :
    graphWeight T (Hypergraph.sum C H) = graphWeight T C + graphWeight T H := by
  apply le_antisymm
  · obtain ⟨φC, hC⟩ := graphWeight_attained T C
    obtain ⟨φH, hH⟩ := graphWeight_attained T H
    calc graphWeight T (Hypergraph.sum C H)
        ≤ edgeSum T (Hypergraph.sum C H) (Fin.append φC φH) := graphWeight_le _ _ _
      _ = edgeSum T C φC + edgeSum T H φH := edgeSum_sum T C H φC φH
      _ = graphWeight T C + graphWeight T H := by rw [hC, hH]
  · obtain ⟨φ, hφ⟩ := graphWeight_attained T (Hypergraph.sum C H)
    calc graphWeight T C + graphWeight T H
        ≤ edgeSum T C (fun i => φ (Fin.castAdd H.nodeCount i)) +
            edgeSum T H (fun i => φ (Fin.natAdd C.nodeCount i)) :=
          Nat.add_le_add (graphWeight_le _ _ _) (graphWeight_le _ _ _)
      _ = edgeSum T (Hypergraph.sum C H) φ := (edgeSum_sum_split T C H φ).symm
      _ = graphWeight T (Hypergraph.sum C H) := hφ

/-- A graph weight that is constant over all typings. -/
theorem graphWeight_eq_of_const (T : TypeGraph) (H : Hypergraph) (c : Nat)
    (h : ∀ φ : Fin H.nodeCount → Fin T.nodeCount, edgeSum T H φ = c) :
    graphWeight T H = c := by
  obtain ⟨φ, hφ⟩ := graphWeight_attained T H
  rw [← hφ, h φ]

/-! ## The free recursor as a graph transformation system -/

/-- Left side of the zero rule: `recur(b, s, zero)`. -/
def recurZeroLhs : Hypergraph where
  nodeCount := 4
  edges := [⟨.zero, (noAtt, 2)⟩, ⟨.recur, (threeAtt 0 1 2, 3)⟩]

/-- Right side of the zero rule: `b` as a one-node graph without edges. -/
def recurZeroRhs : Hypergraph where
  nodeCount := 1
  edges := []

/-- Left side of the successor rule: `recur(b, s, succ n)`. -/
def recurSuccLhs : Hypergraph where
  nodeCount := 5
  edges := [⟨.succ, (oneAtt 2, 3)⟩, ⟨.recur, (threeAtt 0 1 3, 4)⟩]

/-- Right side of the successor rule: `wrap(s, recur(b, s, n))`, with the step node `s` shared. -/
def recurSuccRhs : Hypergraph where
  nodeCount := 5
  edges := [⟨.recur, (threeAtt 0 1 2, 3)⟩, ⟨.wrap, (twoAtt 1 3, 4)⟩]

/-- The two DPO rules of the free recursor. -/
def freeRecursorDPRules : List DPRule :=
  [⟨recurZeroLhs, recurZeroRhs⟩, ⟨recurSuccLhs, recurSuccRhs⟩]

/-- The preorder symbol list of a closed free term: the tree encoding's receipt. -/
def termSymbols : FreeTerm Empty → List FreeSym
  | .var x => nomatch x
  | .zero => [.zero]
  | .succ t => .succ :: termSymbols t
  | .wrap a b => .wrap :: (termSymbols a ++ termSymbols b)
  | .recur b s n => .recur :: (termSymbols b ++ termSymbols s ++ termSymbols n)

/-- The symbol list of a hypergraph. -/
def graphSymbols (H : Hypergraph) : List FreeSym := H.edges.map (fun e => e.1)

/-- The edge list of a canonical graph with a prescribed symbol list, every attachment at node `0`
of a one-node graph. -/
def ofSymbolEdges : List FreeSym → List (Σ s : FreeSym, (Fin (symArity s) → Fin 1) × Fin 1)
  | [] => []
  | s :: ss => ⟨s, (fun _ => ⟨0, by omega⟩, ⟨0, by omega⟩)⟩ :: ofSymbolEdges ss

/-- A canonical one-node graph with a prescribed symbol list. -/
def ofSymbols (l : List FreeSym) : Hypergraph := ⟨1, ofSymbolEdges l⟩

theorem graphSymbols_ofSymbols (l : List FreeSym) : graphSymbols (ofSymbols l) = l := by
  induction l with
  | nil => rfl
  | cons s ss ih =>
      simp only [graphSymbols, ofSymbols, ofSymbolEdges, List.map_cons] at ih ⊢
      rw [ih]

/-- The read-back relation: a graph reads back to a closed free term when its symbol list is the
preorder symbol list of the term. -/
def ReadsBack (H : Hypergraph) (t : FreeTerm Empty) : Prop := graphSymbols H = termSymbols t

/-! ## Row `weightedTypeGraphEscape` -/

/-- Admissibility laws. Pinned to Bruggink, König, Nolte and Zantema, "Termination of Graph
Rewriting Systems using Weighted Type Graphs over Semirings", ICGT 2015, Definition 6 (weighted
type graph) with Definition 5 (ordered semiring): every step is an application of a listed rule at
a graph context, the weight of each symbol at the flower node is strictly positive, and the
read-back relation contains every closed free term's graph. -/
def weightedTypeGraphEscapeLaws (M : weightedTypeGraphEscapeData) : Prop :=
  (∀ {x y : Hypergraph}, M.step x y →
    ∃ (C : Hypergraph) (r : DPRule), r ∈ M.rules ∧ x = Hypergraph.sum C r.lhs ∧
      y = Hypergraph.sum C r.rhs) ∧
  (∀ s : FreeSym, 0 < M.typeGraph.edgeWeight s (fun _ => TypeGraph.flower M.typeGraph)
      (TypeGraph.flower M.typeGraph)) ∧
  (∀ t : FreeTerm Empty, M.readBack (ofSymbols (termSymbols t)) t)

/-- The method's acceptance: every listed rule strictly decreases the summed edge weight of every
typed left side. This is the source's Section 4 form of decreasingness. -/
def weightedTypeGraphEscapeAccepts (M : weightedTypeGraphEscapeData) : Prop :=
  ∀ r ∈ M.rules, ∀ φ : Fin r.lhs.nodeCount → Fin M.typeGraph.nodeCount,
    ∃ ψ : Fin r.rhs.nodeCount → Fin M.typeGraph.nodeCount,
      edgeSum M.typeGraph r.rhs ψ < edgeSum M.typeGraph r.lhs φ

/-- The method accepts the free recursor translated to graph rewriting and the yield is
termination of the graph rewriting relation together with the weight decrease on every step.
Verdict: escape. -/
def weightedTypeGraphEscapeResult (M : weightedTypeGraphEscapeData) : Prop :=
  weightedTypeGraphEscapeAccepts M ∧
  WellFounded (fun y x : Hypergraph => M.step x y) ∧
  (∀ {x y : Hypergraph}, M.step x y →
    graphWeight M.typeGraph y < graphWeight M.typeGraph x)

/-- A decreasing rule strictly decreases the graph weight of its two sides. -/
theorem weightedTypeGraphEscape_rule_decrease (M : weightedTypeGraphEscapeData)
    (hA : weightedTypeGraphEscapeAccepts M) {r : DPRule} (hr : r ∈ M.rules) :
    graphWeight M.typeGraph r.rhs < graphWeight M.typeGraph r.lhs := by
  obtain ⟨φ, hφ⟩ := graphWeight_attained M.typeGraph r.lhs
  obtain ⟨ψ, hψ⟩ := hA r hr φ
  calc graphWeight M.typeGraph r.rhs
      ≤ edgeSum M.typeGraph r.rhs ψ := graphWeight_le _ _ _
    _ < edgeSum M.typeGraph r.lhs φ := hψ
    _ = graphWeight M.typeGraph r.lhs := hφ

/-- Every step of a lawful accepting system strictly decreases the graph weight. -/
theorem weightedTypeGraphEscape_step_lt (M : weightedTypeGraphEscapeData)
    (hL : weightedTypeGraphEscapeLaws M) (hA : weightedTypeGraphEscapeAccepts M)
    {x y : Hypergraph} (h : M.step x y) :
    graphWeight M.typeGraph y < graphWeight M.typeGraph x := by
  obtain ⟨C, r, hr, rfl, rfl⟩ := hL.1 h
  rw [graphWeight_sum, graphWeight_sum]
  have hdec := weightedTypeGraphEscape_rule_decrease M hA hr
  omega

/-- The method's soundness theorem: acceptance makes the graph rewriting relation terminate. -/
theorem weightedTypeGraphEscape_sound :
    ∀ M, weightedTypeGraphEscapeLaws M → weightedTypeGraphEscapeAccepts M →
      weightedTypeGraphEscapeResult M := by
  intro M hL hA
  refine ⟨hA, ?_, ?_⟩
  · refine Subrelation.wf (fun {y x} h => weightedTypeGraphEscape_step_lt M hL hA h)
      (InvImage.wf (fun H : Hypergraph => graphWeight M.typeGraph H) Nat.lt_wfRel.wf)
  · intro x y h
    exact weightedTypeGraphEscape_step_lt M hL hA h

/-- The witness type graph has two nodes; the wrap edge is cheap on an off-diagonal pair of types
and expensive on the diagonal, so the node types carry information the one-node flower cannot. -/
def twoNodeGraph : TypeGraph where
  nodeCount := 2
  two_le := by decide
  edgeWeight := fun s args _r =>
    match s with
    | .zero => 1
    | .succ => 2
    | .recur => 2
    | .wrap =>
        if args (Fin.cast symArity_wrap.symm (0 : Fin 2)) =
            args (Fin.cast symArity_wrap.symm (1 : Fin 2)) then 3 else 0

/-- The non-flower node of the two-node witness graph. -/
def twoNodeGraphSecond : Fin twoNodeGraph.nodeCount := ⟨1, by decide⟩

/-- The witness system: the two DPO rules of the free recursor with the two-node type graph. -/
def weightedTypeGraphEscapeWitness : weightedTypeGraphEscapeData where
  typeGraph := twoNodeGraph
  rules := freeRecursorDPRules
  step := fun x y => ∃ (C : Hypergraph) (r : DPRule),
    r ∈ freeRecursorDPRules ∧ x = Hypergraph.sum C r.lhs ∧ y = Hypergraph.sum C r.rhs
  readBack := ReadsBack

theorem weightedTypeGraphEscapeWitness_laws :
    weightedTypeGraphEscapeLaws weightedTypeGraphEscapeWitness := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    exact h
  · intro s
    show 0 < twoNodeGraph.edgeWeight s (fun _ => TypeGraph.flower twoNodeGraph)
      (TypeGraph.flower twoNodeGraph)
    cases s <;> simp [twoNodeGraph, TypeGraph.flower]
  · intro t
    exact graphSymbols_ofSymbols _

theorem weightedTypeGraphEscapeWitness_accepts :
    weightedTypeGraphEscapeAccepts weightedTypeGraphEscapeWitness := by
  intro r hr φ
  simp only [weightedTypeGraphEscapeWitness, freeRecursorDPRules, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · change ∃ ψ : Fin recurZeroRhs.nodeCount → Fin twoNodeGraph.nodeCount,
      edgeSum twoNodeGraph recurZeroRhs ψ < edgeSum twoNodeGraph recurZeroLhs φ
    exact ⟨fun _ => TypeGraph.flower twoNodeGraph, by
      simp [edgeSum, recurZeroRhs, recurZeroLhs, edgeWeightAt, twoNodeGraph]⟩
  · change ∃ ψ : Fin recurSuccRhs.nodeCount → Fin twoNodeGraph.nodeCount,
      edgeSum twoNodeGraph recurSuccRhs ψ < edgeSum twoNodeGraph recurSuccLhs φ
    refine ⟨fun i => if i = (1 : Fin 5) then TypeGraph.flower twoNodeGraph
        else twoNodeGraphSecond, ?_⟩
    simp [edgeSum, recurSuccRhs, recurSuccLhs, edgeWeightAt, twoNodeGraph, twoAtt,
      TypeGraph.flower, twoNodeGraphSecond]

theorem weightedTypeGraphEscapeWitness_result :
    weightedTypeGraphEscapeResult weightedTypeGraphEscapeWitness :=
  weightedTypeGraphEscape_sound _ weightedTypeGraphEscapeWitness_laws
    weightedTypeGraphEscapeWitness_accepts

/-- The left sharing pattern: one wrap edge whose two arguments are distinct nodes. -/
def sharingPatternLeft : Hypergraph where
  nodeCount := 2
  edges := [⟨.wrap, (twoAtt 0 1, 0)⟩]

/-- The right sharing pattern: one wrap edge whose two arguments are the same node. -/
def sharingPatternRight : Hypergraph where
  nodeCount := 1
  edges := [⟨.wrap, (twoAtt 0 0, 0)⟩]

theorem graphWeight_sharingPatternLeft : graphWeight twoNodeGraph sharingPatternLeft = 0 := by
  apply le_antisymm
  · have h := graphWeight_le twoNodeGraph sharingPatternLeft
      (fun i : Fin 2 => if i = 0 then TypeGraph.flower twoNodeGraph else twoNodeGraphSecond)
    simpa [edgeSum, sharingPatternLeft, edgeWeightAt, twoNodeGraph, twoAtt, TypeGraph.flower,
      twoNodeGraphSecond] using h
  · exact Nat.zero_le _

theorem graphWeight_sharingPatternRight : graphWeight twoNodeGraph sharingPatternRight = 3 := by
  apply graphWeight_eq_of_const _ _ 3
  intro φ
  simp [edgeSum, sharingPatternRight, edgeWeightAt, twoNodeGraph, twoAtt]

/-- The one-node flower aggregation is blind to sharing: both patterns carry the same symbol list,
so the tree encoding cannot separate them. -/
theorem sharingPatterns_symbols_eq : graphSymbols sharingPatternLeft = graphSymbols sharingPatternRight := by
  simp [graphSymbols, sharingPatternLeft, sharingPatternRight]

/-- The feature of the witness: the two rules are accepted, the two-node typing separates the two
sharing patterns that the tree encoding cannot, and the tree encoding reads back. -/
theorem weightedTypeGraphEscapeWitness_feature :
    weightedTypeGraphEscapeAccepts weightedTypeGraphEscapeWitness ∧
    (∃ H₁ H₂ : Hypergraph,
      graphSymbols H₁ = graphSymbols H₂ ∧
      graphWeight twoNodeGraph H₁ ≠ graphWeight twoNodeGraph H₂) ∧
    ReadsBack (ofSymbols (termSymbols (.zero : FreeTerm Empty))) (.zero : FreeTerm Empty) := by
  refine ⟨weightedTypeGraphEscapeWitness_accepts, ?_, ?_⟩
  · refine ⟨sharingPatternLeft, sharingPatternRight, sharingPatterns_symbols_eq, ?_⟩
    rw [graphWeight_sharingPatternLeft, graphWeight_sharingPatternRight]
    decide
  · exact graphSymbols_ofSymbols _

/-- The mutation replaces the type graph by the zero weight graph, so the flower positivity law
fails at the zero symbol. -/
theorem weightedTypeGraphEscape_mutation :
    ¬ weightedTypeGraphEscapeLaws
      { weightedTypeGraphEscapeWitness with
        typeGraph := { twoNodeGraph with edgeWeight := fun _ _ _ => 0 } } := by
  intro h
  exact Nat.lt_irrefl 0 (by
    simpa [TypeGraph.flower, twoNodeGraph] using h.2.1 FreeSym.zero)

/-- Relative termination for strict and weak rule partitions in the disjoint-sum graph model. -/
def weightedTypeGraphEscape_scope : Prop :=
  ∀ (T : TypeGraph) (rulesLt rulesEq : List DPRule),
    (∀ r ∈ rulesLt, ∀ φ : Fin r.lhs.nodeCount → Fin T.nodeCount,
      ∃ ψ : Fin r.rhs.nodeCount → Fin T.nodeCount,
        edgeSum T r.rhs ψ < edgeSum T r.lhs φ) →
    (∀ r ∈ rulesEq, ∀ φ : Fin r.lhs.nodeCount → Fin T.nodeCount,
      ∃ ψ : Fin r.rhs.nodeCount → Fin T.nodeCount,
        edgeSum T r.rhs ψ ≤ edgeSum T r.lhs φ) →
    (WellFounded (fun y x : Hypergraph => ∃ C r, r ∈ rulesLt ++ rulesEq ∧
        x = Hypergraph.sum C r.lhs ∧ y = Hypergraph.sum C r.rhs) ↔
       WellFounded (fun y x : Hypergraph => ∃ C r, r ∈ rulesEq ∧
         x = Hypergraph.sum C r.lhs ∧ y = Hypergraph.sum C r.rhs))

/-- Context application of one rule from a list by disjoint graph sum. -/
def graphContextStep (rules : List DPRule) (x y : Hypergraph) : Prop :=
  ∃ C r, r ∈ rules ∧ x = Hypergraph.sum C r.lhs ∧ y = Hypergraph.sum C r.rhs

/-- Strict acceptance lowers the minimum graph weight after every disjoint-sum context. -/
theorem graphContextStep_lt (T : TypeGraph) (rules : List DPRule)
    (hRules : ∀ r ∈ rules, ∀ φ : Fin r.lhs.nodeCount → Fin T.nodeCount,
      ∃ ψ : Fin r.rhs.nodeCount → Fin T.nodeCount,
        edgeSum T r.rhs ψ < edgeSum T r.lhs φ)
    {x y : Hypergraph} (hxy : graphContextStep rules x y) :
    graphWeight T y < graphWeight T x := by
  obtain ⟨C, r, hr, rfl, rfl⟩ := hxy
  obtain ⟨φ, hφ⟩ := graphWeight_attained T r.lhs
  obtain ⟨ψ, hψ⟩ := hRules r hr φ
  have hRule : graphWeight T r.rhs < graphWeight T r.lhs := by
    calc
      graphWeight T r.rhs ≤ edgeSum T r.rhs ψ := graphWeight_le _ _ _
      _ < edgeSum T r.lhs φ := hψ
      _ = graphWeight T r.lhs := hφ
  rw [graphWeight_sum, graphWeight_sum]
  omega

/-- Weak acceptance does not increase the minimum graph weight after every disjoint-sum context. -/
theorem graphContextStep_le (T : TypeGraph) (rules : List DPRule)
    (hRules : ∀ r ∈ rules, ∀ φ : Fin r.lhs.nodeCount → Fin T.nodeCount,
      ∃ ψ : Fin r.rhs.nodeCount → Fin T.nodeCount,
        edgeSum T r.rhs ψ ≤ edgeSum T r.lhs φ)
    {x y : Hypergraph} (hxy : graphContextStep rules x y) :
    graphWeight T y ≤ graphWeight T x := by
  obtain ⟨C, r, hr, rfl, rfl⟩ := hxy
  obtain ⟨φ, hφ⟩ := graphWeight_attained T r.lhs
  obtain ⟨ψ, hψ⟩ := hRules r hr φ
  have hRule : graphWeight T r.rhs ≤ graphWeight T r.lhs := by
    calc
      graphWeight T r.rhs ≤ edgeSum T r.rhs ψ := graphWeight_le _ _ _
      _ ≤ edgeSum T r.lhs φ := hψ
      _ = graphWeight T r.lhs := hφ
  rw [graphWeight_sum, graphWeight_sum]
  omega

/-- The full relative-termination theorem for the row.  Adding strictly decreasing rules to a
terminating weak subsystem preserves termination; conversely, the weak subsystem is a
subrelation of the union. -/
theorem weightedTypeGraphEscape_scope_proven : weightedTypeGraphEscape_scope := by
  intro T rulesLt rulesEq hLt hEq
  constructor
  · intro hAll
    refine Subrelation.wf ?_ hAll
    intro y x hxy
    obtain ⟨C, r, hr, rfl, rfl⟩ := hxy
    exact ⟨C, r, List.mem_append_right _ hr, rfl, rfl⟩
  · intro hWeak
    have hUnion : WellFounded (fun y x : Hypergraph =>
        graphContextStep rulesLt x y ∨ graphContextStep rulesEq x y) :=
      arithWeight.wellFounded_union_of_strict_measure_and_weak
        (graphWeight T) (graphContextStep rulesLt) (graphContextStep rulesEq)
        hWeak (graphContextStep_lt T rulesLt hLt) (graphContextStep_le T rulesEq hEq)
    refine Subrelation.wf ?_ hUnion
    intro y x hxy
    obtain ⟨C, r, hr, rfl, rfl⟩ := hxy
    rcases List.mem_append.1 hr with hr | hr
    · exact Or.inl ⟨C, r, hr, rfl, rfl⟩
    · exact Or.inr ⟨C, r, hr, rfl, rfl⟩

/-- Exact method identity for weighted type graphs: native rule acceptance, contextual weight
transport, the general relative-termination theorem, and a non-flower sharing witness. -/
theorem weightedTypeGraphEscape_methodIdentity :
    weightedTypeGraphEscape_scope ∧
    weightedTypeGraphEscapeResult weightedTypeGraphEscapeWitness ∧
    graphWeight twoNodeGraph sharingPatternLeft ≠ graphWeight twoNodeGraph sharingPatternRight :=
  ⟨weightedTypeGraphEscape_scope_proven, weightedTypeGraphEscapeWitness_result, by
    rw [graphWeight_sharingPatternLeft, graphWeight_sharingPatternRight]
    decide⟩

/-! ## Row `generalizedWeightedTypeGraphs` -/

/-- The `⊗`-fold of a list of weights. -/
def wmul (A : WeightAlgebra) : List A.W → A.W
  | [] => A.one
  | a :: as => A.mul a (wmul A as)

/-- The edge product of a generalized type graph under a typing: the `⊗`-fold of the edge
weights (the source's `wT(t)`). -/
def gEdgeSum {A : WeightAlgebra} (G : GeneralizedTypeGraph A) (H : Hypergraph)
    (φ : Fin H.nodeCount → Fin G.nodeCount) : A.W :=
  wmul A (H.edges.map (fun e => G.edgeWeight e.1 (fun i => φ (e.2.1 i)) (φ e.2.2)))

/-- `m` is the minimum of `f` over a nonempty index type: a lower bound, the greatest lower bound,
and attained up to the non-strict order. -/
def IsMinOver {α : Type*} (A : WeightAlgebra) (f : α → A.W) (m : A.W) : Prop :=
  (∀ a, A.le m (f a)) ∧ (∀ x, (∀ a, A.le x (f a)) → A.le x m) ∧ (∃ a, A.le (f a) m)

/-- The flower node of a generalized type graph. -/
def GeneralizedTypeGraph.flower {A : WeightAlgebra} (G : GeneralizedTypeGraph A) : Fin G.nodeCount :=
  ⟨0, by have h := G.two_le; omega⟩

theorem WeightAlgebra.lt_of_le_of_lt (A : WeightAlgebra) {a b c : A.W} (hab : A.le a b)
    (hbc : A.lt b c) : A.lt a c := by
  refine A.lt_iff.mpr ⟨A.le_trans hab (A.lt_iff.mp hbc).1, ?_⟩
  intro hca
  exact (A.lt_iff.mp hbc).2 (A.le_trans hca hab)

theorem WeightAlgebra.lt_of_lt_of_le (A : WeightAlgebra) {a b c : A.W} (hab : A.lt a b)
    (hbc : A.le b c) : A.lt a c := by
  refine A.lt_iff.mpr ⟨A.le_trans (A.lt_iff.mp hab).1 hbc, ?_⟩
  intro hca
  exact (A.lt_iff.mp hab).2 (A.le_trans hbc hca)

/-- The minimum over typings of the arithmetic edge product. -/
def arithGraphWeight (G : GeneralizedTypeGraph arithWeight) (H : Hypergraph) : Nat :=
  ((Finset.univ : Finset (Fin H.nodeCount → Fin G.nodeCount)).image
      (fun φ => (gEdgeSum G H φ : Nat))).min'
    ⟨(gEdgeSum G H (fun _ => GeneralizedTypeGraph.flower G) : Nat),
      Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩

theorem arithGraphWeight_le (G : GeneralizedTypeGraph arithWeight) (H : Hypergraph)
    (φ : Fin H.nodeCount → Fin G.nodeCount) : arithGraphWeight G H ≤ (gEdgeSum G H φ : Nat) :=
  (Finset.isLeast_min' _ _).2 (Finset.mem_image.mpr ⟨φ, Finset.mem_univ φ, rfl⟩)

theorem arithGraphWeight_attained (G : GeneralizedTypeGraph arithWeight) (H : Hypergraph) :
    ∃ φ : Fin H.nodeCount → Fin G.nodeCount,
      (gEdgeSum G H φ : Nat) = arithGraphWeight G H := by
  have hmem : arithGraphWeight G H ∈
      (Finset.univ : Finset (Fin H.nodeCount → Fin G.nodeCount)).image
        (fun φ => (gEdgeSum G H φ : Nat)) := by
    unfold arithGraphWeight
    exact Finset.min'_mem _ _
  rw [Finset.mem_image] at hmem
  obtain ⟨φ, -, hφ⟩ := hmem
  exact ⟨φ, hφ⟩

theorem arithGraphWeight_isMin (G : GeneralizedTypeGraph arithWeight) (H : Hypergraph) :
    IsMinOver arithWeight (fun φ => (gEdgeSum G H φ : Nat)) (arithGraphWeight G H) := by
  have hlb : ∀ φ : Fin H.nodeCount → Fin G.nodeCount,
      arithWeight.le (arithGraphWeight G H) (gEdgeSum G H φ) :=
    fun φ => arithGraphWeight_le G H φ
  have hglb : ∀ x : Nat, (∀ φ : Fin H.nodeCount → Fin G.nodeCount,
      arithWeight.le x (gEdgeSum G H φ)) → arithWeight.le x (arithGraphWeight G H) := by
    intro x hx
    obtain ⟨φ, hφ⟩ := arithGraphWeight_attained G H
    rw [← hφ]
    exact hx φ
  have hatt : ∃ φ : Fin H.nodeCount → Fin G.nodeCount,
      arithWeight.le (gEdgeSum G H φ) (arithGraphWeight G H) := by
    obtain ⟨φ, hφ⟩ := arithGraphWeight_attained G H
    exact ⟨φ, by rw [hφ]⟩
  exact ⟨hlb, hglb, hatt⟩

/-- Admissibility laws. Pinned to Bruggink, König, Nolte and Zantema, ICGT 2015, Definition 5
(ordered semiring, strongly ordered addition), Definition 6 (weighted type graph over the
semiring), Definition 9 (strongly decreasing rule) and Lemma 4: every step is a root application
of a listed rule, the graph weight is the minimum over typings of the `⊗`-edge product, every edge
weight lies in `S<` (preserves strict inequality under `⊗`), and the read-back contains every
closed free term's symbol list. -/
def generalizedWeightedTypeGraphsLaws (M : generalizedWeightedTypeGraphsData) : Prop :=
  (∀ {x y : Hypergraph}, M.step x y → ∃ r ∈ M.rules, x = r.lhs ∧ y = r.rhs) ∧
  (∀ H : Hypergraph,
    IsMinOver M.algebra (fun φ => gEdgeSum M.typeGraph H φ) (M.graphWeight H)) ∧
  (∀ (s : FreeSym) (args : Fin (symArity s) → Fin M.typeGraph.nodeCount)
      (r : Fin M.typeGraph.nodeCount),
    StrictPreserving M.algebra (M.typeGraph.edgeWeight s args r)) ∧
  (∀ t : FreeTerm Empty, M.readBack (ofSymbols (termSymbols t)) t)

/-- The method's acceptance: every listed rule is strictly decreasing, that is, for every typing
of a left side there is a typing of the right side with a strictly smaller `⊗`-edge product. -/
def generalizedWeightedTypeGraphsAccepts (M : generalizedWeightedTypeGraphsData) : Prop :=
  ∀ r ∈ M.rules, ∀ φ : Fin r.lhs.nodeCount → Fin M.typeGraph.nodeCount,
    ∃ ψ : Fin r.rhs.nodeCount → Fin M.typeGraph.nodeCount,
      M.algebra.lt (gEdgeSum M.typeGraph r.rhs ψ) (gEdgeSum M.typeGraph r.lhs φ)

/-- The method accepts the free recursor translated to graph rewriting and the yield is
termination of the graph rewriting relation together with the weight decrease on every step.
Verdict: escape. -/
def generalizedWeightedTypeGraphsResult (M : generalizedWeightedTypeGraphsData) : Prop :=
  generalizedWeightedTypeGraphsAccepts M ∧
  WellFounded (fun y x : Hypergraph => M.step x y) ∧
  (∀ {x y : Hypergraph}, M.step x y →
    M.algebra.lt (M.graphWeight y) (M.graphWeight x))

/-- A strictly decreasing rule strictly decreases the graph weight of its two sides. -/
theorem generalizedWeightedTypeGraphs_rule_decrease (M : generalizedWeightedTypeGraphsData)
    (hL : generalizedWeightedTypeGraphsLaws M) (hA : generalizedWeightedTypeGraphsAccepts M)
    {r : DPRule} (hr : r ∈ M.rules) :
    M.algebra.lt (M.graphWeight r.rhs) (M.graphWeight r.lhs) := by
  obtain ⟨φ, hφ⟩ := (hL.2.1 r.lhs).2.2
  obtain ⟨ψ, hψ⟩ := hA r hr φ
  exact WeightAlgebra.lt_of_le_of_lt M.algebra ((hL.2.1 r.rhs).1 ψ)
    (WeightAlgebra.lt_of_lt_of_le M.algebra hψ hφ)

/-- Every step of a lawful accepting system strictly decreases the graph weight. -/
theorem generalizedWeightedTypeGraphs_step_lt (M : generalizedWeightedTypeGraphsData)
    (hL : generalizedWeightedTypeGraphsLaws M) (hA : generalizedWeightedTypeGraphsAccepts M)
    {x y : Hypergraph} (h : M.step x y) :
    M.algebra.lt (M.graphWeight y) (M.graphWeight x) := by
  obtain ⟨r, hr, rfl, rfl⟩ := hL.1 h
  exact generalizedWeightedTypeGraphs_rule_decrease M hL hA hr

/-- The method's soundness theorem: strong decreases make the graph rewriting relation
terminate. -/
theorem generalizedWeightedTypeGraphs_sound :
    ∀ M, generalizedWeightedTypeGraphsLaws M → generalizedWeightedTypeGraphsAccepts M →
      generalizedWeightedTypeGraphsResult M := by
  intro M hL hA
  refine ⟨hA, ?_, ?_⟩
  · refine Subrelation.wf (fun {y x} h => generalizedWeightedTypeGraphs_step_lt M hL hA h)
      (InvImage.wf (fun H : Hypergraph => M.graphWeight H) M.algebra.lt_wf)
  · intro x y h
    exact generalizedWeightedTypeGraphs_step_lt M hL hA h

/-- The two-node generalized type graph over the arithmetic semiring, with a positive weight for
every symbol occurrence and a node-dependent wrapper weight. -/
def twoNodeGTypeGraph : GeneralizedTypeGraph arithWeight where
  nodeCount := 2
  two_le := by decide
  edgeWeight := fun s args _r =>
    match s with
    | .zero => 1
    | .succ => 3
    | .recur => 2
    | .wrap =>
        if args (Fin.cast symArity_wrap.symm (0 : Fin 2)) =
            args (Fin.cast symArity_wrap.symm (1 : Fin 2)) then 2 else 1

/-- The non-flower node of the two-node generalized witness graph. -/
def twoNodeGTypeGraphSecond : Fin twoNodeGTypeGraph.nodeCount := ⟨1, by decide⟩

/-- The witness system: the two root rules of the free recursor with the arithmetic minimum
aggregation. -/
abbrev generalizedWeightedTypeGraphsWitness : generalizedWeightedTypeGraphsData where
  algebra := arithWeight
  typeGraph := twoNodeGTypeGraph
  graphWeight := arithGraphWeight twoNodeGTypeGraph
  rules := freeRecursorDPRules
  step := fun x y => ∃ r ∈ freeRecursorDPRules, x = r.lhs ∧ y = r.rhs
  readBack := ReadsBack

theorem generalizedWeightedTypeGraphsWitness_laws :
    generalizedWeightedTypeGraphsLaws generalizedWeightedTypeGraphsWitness := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y h
    exact h
  · intro H
    exact arithGraphWeight_isMin twoNodeGTypeGraph H
  · intro s args r
    show ∀ {a b : Nat}, a < b → (twoNodeGTypeGraph.edgeWeight s args r) * a <
      (twoNodeGTypeGraph.edgeWeight s args r) * b
    have hc : 0 < twoNodeGTypeGraph.edgeWeight s args r := by
      cases s <;> simp only [twoNodeGTypeGraph] <;> (try split) <;> decide
    intro a b hab
    exact Nat.mul_lt_mul_of_pos_left hab hc
  · intro t
    exact graphSymbols_ofSymbols _

theorem generalizedWeightedTypeGraphsWitness_accepts :
    generalizedWeightedTypeGraphsAccepts generalizedWeightedTypeGraphsWitness := by
  intro r hr φ
  simp only [freeRecursorDPRules, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · change ∃ ψ : Fin recurZeroRhs.nodeCount → Fin twoNodeGTypeGraph.nodeCount,
      arithWeight.lt (gEdgeSum twoNodeGTypeGraph recurZeroRhs ψ)
        (gEdgeSum twoNodeGTypeGraph recurZeroLhs φ)
    exact ⟨fun _ => GeneralizedTypeGraph.flower twoNodeGTypeGraph, by
      simp [gEdgeSum, wmul, recurZeroRhs, recurZeroLhs, twoNodeGTypeGraph, arithWeight]⟩
  · change ∃ ψ : Fin recurSuccRhs.nodeCount → Fin twoNodeGTypeGraph.nodeCount,
      arithWeight.lt (gEdgeSum twoNodeGTypeGraph recurSuccRhs ψ)
        (gEdgeSum twoNodeGTypeGraph recurSuccLhs φ)
    refine ⟨fun i => if i = (1 : Fin 5) then GeneralizedTypeGraph.flower twoNodeGTypeGraph
        else twoNodeGTypeGraphSecond, ?_⟩
    simp [gEdgeSum, wmul, recurSuccRhs, recurSuccLhs, twoNodeGTypeGraph, twoAtt,
      GeneralizedTypeGraph.flower, twoNodeGTypeGraphSecond, arithWeight]

theorem generalizedWeightedTypeGraphsWitness_result :
    generalizedWeightedTypeGraphsResult generalizedWeightedTypeGraphsWitness :=
  generalizedWeightedTypeGraphs_sound _ generalizedWeightedTypeGraphsWitness_laws
    generalizedWeightedTypeGraphsWitness_accepts

/-- The constant-weight generalized type graph: every edge weight is the multiplicative unit. -/
def constantGTypeGraph : GeneralizedTypeGraph arithWeight where
  nodeCount := 2
  two_le := by decide
  edgeWeight := fun _ _ _ => 1

/-- The unrelated constant coordinate is rejected: the successor rule's two sides have the same
product, so nothing strictly decreases. -/
theorem constantGTypeGraph_rejected :
    ¬ generalizedWeightedTypeGraphsAccepts
      { generalizedWeightedTypeGraphsWitness with typeGraph := constantGTypeGraph } := by
  intro h
  have hdec := h ⟨recurSuccLhs, recurSuccRhs⟩
    (by simp [freeRecursorDPRules])
    (fun _ => GeneralizedTypeGraph.flower constantGTypeGraph)
  obtain ⟨ψ, hψ⟩ := hdec
  have hψ' := hψ
  simp only [gEdgeSum, constantGTypeGraph, recurSuccLhs, recurSuccRhs, arithWeight] at hψ'
  exact absurd hψ' (by decide)

theorem twoNodeGTypeGraph_aggregation_control :
    ∃ (φ ψ : Fin sharingPatternLeft.nodeCount → Fin twoNodeGTypeGraph.nodeCount),
      (gEdgeSum twoNodeGTypeGraph sharingPatternLeft φ : Nat) ≠
        (gEdgeSum twoNodeGTypeGraph sharingPatternLeft ψ : Nat) := by
  refine ⟨fun i : Fin 2 => if i = 0 then GeneralizedTypeGraph.flower twoNodeGTypeGraph
      else twoNodeGTypeGraphSecond,
    fun _ => GeneralizedTypeGraph.flower twoNodeGTypeGraph, ?_⟩
  simp [gEdgeSum, wmul, sharingPatternLeft, twoNodeGTypeGraph, twoAtt,
    GeneralizedTypeGraph.flower, twoNodeGTypeGraphSecond, arithWeight]

/-- The feature of the witness: the two rules are accepted, the minimum over typings is engaged by
a node-dependent weight, every edge weight lies in `S<`, and the constant coordinate is
rejected. -/
theorem generalizedWeightedTypeGraphsWitness_feature :
    generalizedWeightedTypeGraphsAccepts generalizedWeightedTypeGraphsWitness ∧
    (∃ (φ ψ : Fin sharingPatternLeft.nodeCount → Fin twoNodeGTypeGraph.nodeCount),
      (gEdgeSum twoNodeGTypeGraph sharingPatternLeft φ : Nat) ≠
        (gEdgeSum twoNodeGTypeGraph sharingPatternLeft ψ : Nat)) ∧
    (¬ generalizedWeightedTypeGraphsAccepts
      { generalizedWeightedTypeGraphsWitness with typeGraph := constantGTypeGraph }) :=
  ⟨generalizedWeightedTypeGraphsWitness_accepts, twoNodeGTypeGraph_aggregation_control,
    constantGTypeGraph_rejected⟩

/-- The mutation replaces every edge weight by the zero element, so the strict-preservation law
fails at the zero weight. -/
theorem generalizedWeightedTypeGraphs_mutation :
    ¬ generalizedWeightedTypeGraphsLaws
      { generalizedWeightedTypeGraphsWitness with
        typeGraph := { twoNodeGTypeGraph with edgeWeight := fun _ _ _ => 0 } } := by
  intro h
  have h0 : StrictPreserving arithWeight (0 : Nat) := h.2.2.1 FreeSym.zero
    (fun _ => GeneralizedTypeGraph.flower twoNodeGTypeGraph)
    (GeneralizedTypeGraph.flower twoNodeGTypeGraph)
  exact Nat.lt_irrefl 0 (h0 (by decide : (0 : Nat) < 1))

/-- The full contextual scope: minimum graph weights, strong rule acceptance, multiplicative
transport through the chosen graph gluing, and strict preservation by every context weight imply
termination of all glued rule applications. -/
def generalizedWeightedTypeGraphs_scope : Prop :=
  ∀ (A : WeightAlgebra) (T : GeneralizedTypeGraph A) (Γ : List DPRule)
    (graphWeight : Hypergraph → A.W)
    (_ : ∀ H, IsMinOver A (fun φ => gEdgeSum T H φ) (graphWeight H))
    (_ : ∀ (s : FreeSym) (args : Fin (symArity s) → Fin T.nodeCount)
      (r : Fin T.nodeCount), StrictPreserving A (T.edgeWeight s args r))
    (glue : Hypergraph → Hypergraph → Hypergraph)
    (_ : ∀ C H, graphWeight (glue C H) = A.mul (graphWeight C) (graphWeight H))
    (_ : ∀ C, StrictPreserving A (graphWeight C))
    (_ : ∀ r ∈ Γ, ∀ φ : Fin r.lhs.nodeCount → Fin T.nodeCount,
      ∃ ψ : Fin r.rhs.nodeCount → Fin T.nodeCount,
        A.lt (gEdgeSum T r.rhs ψ) (gEdgeSum T r.lhs φ)),
      WellFounded (fun y x : Hypergraph => ∃ C r, r ∈ Γ ∧
        x = glue C r.lhs ∧ y = glue C r.rhs)

/-- Strong acceptance lowers the minimum weight of a generalized weighted type graph rule. -/
theorem generalizedGraphRule_decrease (A : WeightAlgebra) (T : GeneralizedTypeGraph A)
    (graphWeight : Hypergraph → A.W)
    (hMin : ∀ H, IsMinOver A (fun φ => gEdgeSum T H φ) (graphWeight H))
    (Γ : List DPRule)
    (hAccept : ∀ r ∈ Γ, ∀ φ : Fin r.lhs.nodeCount → Fin T.nodeCount,
      ∃ ψ : Fin r.rhs.nodeCount → Fin T.nodeCount,
        A.lt (gEdgeSum T r.rhs ψ) (gEdgeSum T r.lhs φ))
    {r : DPRule} (hr : r ∈ Γ) :
    A.lt (graphWeight r.rhs) (graphWeight r.lhs) := by
  obtain ⟨φ, hφ⟩ := (hMin r.lhs).2.2
  obtain ⟨ψ, hψ⟩ := hAccept r hr φ
  exact A.lt_of_le_of_lt ((hMin r.rhs).1 ψ) (A.lt_of_lt_of_le hψ hφ)

/-- The arbitrary-context generalized weighted type graph theorem, including the gluing law that
the unqualified version omitted. -/
theorem generalizedWeightedTypeGraphs_scope_proven : generalizedWeightedTypeGraphs_scope := by
  intro A T Γ graphWeight hMin _edgeStrict glue hGlue hContextStrict hAccept
  refine Subrelation.wf ?_ (InvImage.wf graphWeight A.lt_wf)
  intro y x hxy
  obtain ⟨C, r, hr, rfl, rfl⟩ := hxy
  change A.lt (graphWeight (glue C r.rhs)) (graphWeight (glue C r.lhs))
  rw [hGlue, hGlue]
  exact hContextStrict C (generalizedGraphRule_decrease A T graphWeight hMin Γ hAccept hr)

/-- The false extension obtained by dropping every gluing compatibility law. -/
def generalizedWeightedTypeGraphs_unglued_extension : Prop :=
  ∀ (Γ : List DPRule) (graphWeight : Hypergraph → Nat)
    (glue : Hypergraph → Hypergraph → Hypergraph),
    (∀ r ∈ Γ, graphWeight r.rhs < graphWeight r.lhs) →
    WellFounded (fun y x : Hypergraph => ∃ C r, r ∈ Γ ∧
      x = glue C r.lhs ∧ y = glue C r.rhs)

/-- A one-node-to-zero-node root decrease whose constant gluing identifies both sides. -/
def collapsingGraphRule : DPRule :=
  ⟨⟨1, []⟩, ⟨0, []⟩⟩

/-- Constant gluing destroys a strict root decrease by mapping both sides to the same graph. -/
def collapsingGraphGlue (_ _ : Hypergraph) : Hypergraph := ⟨0, []⟩

/-- Arbitrary gluing without a weight law cannot preserve termination. -/
theorem generalizedWeightedTypeGraphs_unglued_extension_false :
    ¬ generalizedWeightedTypeGraphs_unglued_extension := by
  intro h
  have hRoot : ∀ r ∈ [collapsingGraphRule], r.rhs.nodeCount < r.lhs.nodeCount := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    decide
  have hWF := h [collapsingGraphRule] Hypergraph.nodeCount collapsingGraphGlue hRoot
  have hLoop : ∃ C r, r ∈ [collapsingGraphRule] ∧
      (collapsingGraphGlue C r.lhs : Hypergraph) = collapsingGraphGlue C r.lhs ∧
      (collapsingGraphGlue C r.lhs : Hypergraph) = collapsingGraphGlue C r.rhs := by
    exact ⟨⟨0, []⟩, collapsingGraphRule, by simp, rfl, rfl⟩
  exact hWF.isIrrefl.irrefl (collapsingGraphGlue ⟨0, []⟩ collapsingGraphRule.lhs) hLoop

/-- Exact method identity for generalized weighted type graphs: the native ordered-semiring
certificate, the arbitrary compatible-gluing theorem, and the counterexample when compatibility
is removed. -/
theorem generalizedWeightedTypeGraphs_methodIdentity :
    generalizedWeightedTypeGraphsResult generalizedWeightedTypeGraphsWitness ∧
    generalizedWeightedTypeGraphs_scope ∧
    ¬ generalizedWeightedTypeGraphs_unglued_extension :=
  ⟨generalizedWeightedTypeGraphsWitness_result,
    generalizedWeightedTypeGraphs_scope_proven,
    generalizedWeightedTypeGraphs_unglued_extension_false⟩

/-! ## Row `quasiInterpretationsSharingAware` -/

/-- The unsharing read-back of a shared term graph. -/
def unshare : SharedTerm → FreeTerm Empty
  | .leaf => .zero
  | .node a b => .wrap (unshare a) (unshare b)
  | .shared a => unshare a

/-- The size of a closed free term. -/
def freeSize : FreeTerm Empty → Nat
  | .var x => nomatch x
  | .zero => 1
  | .succ t => freeSize t + 1
  | .wrap a b => freeSize a + freeSize b + 1
  | .recur b s n => freeSize b + freeSize s + freeSize n + 1

/-- The number of sharing nodes of a shared term graph. -/
def sharedCount : SharedTerm → Nat
  | .leaf => 0
  | .node a b => sharedCount a + sharedCount b
  | .shared a => sharedCount a + 1

/-- Admissibility laws. Pinned to Bonfante, Marion and Moyen, "Quasi-interpretations a way to
control resources", Theoretical Computer Science 412 (2011), Definition 3 and Proposition 4: the
assignment is weakly monotone with the subterm and constructor size bounds, the duplicating rule of
the free recursor is the native sharing contraction, and the read-back dominates the term
size. -/
def quasiInterpretationsSharingAwareLaws (M : quasiInterpretationsSharingAwareData) : Prop :=
  (1 ≤ M.eval .leaf) ∧
  (∀ a b : SharedTerm, M.eval a + M.eval b + 1 ≤ M.eval (.node a b)) ∧
  (∀ a : SharedTerm, M.eval a ≤ M.eval (.shared a)) ∧
  (∀ a : SharedTerm, M.exec (.node a a) (.shared a)) ∧
  (∀ t : SharedTerm, freeSize (M.readBack t) ≤ M.eval t)

/-- The method's acceptance: the quasi-interpretation weakly decreases on the execution relation,
which is the adapter image of the free duplicating rule. -/
def quasiInterpretationsSharingAwareAccepts (M : quasiInterpretationsSharingAwareData) : Prop :=
  ∀ {x y : SharedTerm}, M.exec x y → M.eval y ≤ M.eval x

/-- The method accepts the free duplicating rule on the sharing-aware carrier and the yield is the
source's Proposition 4 size bound: the quasi-interpretation of the input bounds the read-back size
of every value reached. Verdict: escape. -/
def quasiInterpretationsSharingAwareResult (M : quasiInterpretationsSharingAwareData) : Prop :=
  quasiInterpretationsSharingAwareAccepts M ∧
  (∀ t u : SharedTerm, Relation.ReflTransGen M.exec t u → freeSize (M.readBack u) ≤ M.eval t)

/-- The method's soundness theorem: the weak decrease along the execution relation and the size
domination give the reachable read-back bound. -/
theorem quasiInterpretationsSharingAware_sound :
    ∀ M, quasiInterpretationsSharingAwareLaws M → quasiInterpretationsSharingAwareAccepts M →
      quasiInterpretationsSharingAwareResult M := by
  intro M hL hA
  refine ⟨hA, ?_⟩
  intro t u hreach
  have hle : M.eval u ≤ M.eval t := by
    induction hreach with
    | refl => exact le_rfl
    | tail _ hstep ih => exact le_trans (hA hstep) ih
  exact le_trans (hL.2.2.2.2 u) hle

/-- The witness: the read-back size plus the number of sharing nodes, with the native sharing
contraction as execution. -/
def quasiInterpretationsSharingAwareWitness : quasiInterpretationsSharingAwareData where
  eval := fun t => freeSize (unshare t) + sharedCount t
  exec := fun x y => ∃ a : SharedTerm, x = .node a a ∧ y = .shared a
  readBack := unshare

theorem quasiInterpretationsSharingAwareWitness_laws :
    quasiInterpretationsSharingAwareLaws quasiInterpretationsSharingAwareWitness := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show 1 ≤ freeSize (unshare .leaf) + sharedCount .leaf
    simp [unshare, sharedCount, freeSize]
  · intro a b
    show freeSize (unshare a) + sharedCount a + (freeSize (unshare b) + sharedCount b) + 1 ≤
      freeSize (unshare (.node a b)) + sharedCount (.node a b)
    simp only [unshare, sharedCount, freeSize]
    omega
  · intro a
    show freeSize (unshare a) + sharedCount a ≤
      freeSize (unshare (.shared a)) + sharedCount (.shared a)
    simp only [unshare, sharedCount]
    omega
  · intro a
    exact ⟨a, rfl, rfl⟩
  · intro t
    show freeSize (unshare t) ≤ freeSize (unshare t) + sharedCount t
    exact Nat.le_add_right _ _

theorem quasiInterpretationsSharingAwareWitness_accepts :
    quasiInterpretationsSharingAwareAccepts quasiInterpretationsSharingAwareWitness := by
  intro x y h
  obtain ⟨a, rfl, rfl⟩ := h
  show freeSize (unshare (.shared a)) + sharedCount (.shared a) ≤
    freeSize (unshare (.node a a)) + sharedCount (.node a a)
  simp only [unshare, sharedCount, freeSize]
  omega

theorem quasiInterpretationsSharingAwareWitness_result :
    quasiInterpretationsSharingAwareResult quasiInterpretationsSharingAwareWitness :=
  quasiInterpretationsSharingAware_sound _ quasiInterpretationsSharingAwareWitness_laws
    quasiInterpretationsSharingAwareWitness_accepts

/-- The feature of the witness: the rule is accepted, two sharing patterns of one source term have
equal read-back and different cost, and a stutter step cannot be certified strictly, which is why
the method yields a size bound and not termination. -/
theorem quasiInterpretationsSharingAwareWitness_feature :
    quasiInterpretationsSharingAwareAccepts quasiInterpretationsSharingAwareWitness ∧
    (∃ x y : SharedTerm, unshare x = unshare y ∧ x ≠ y ∧
      quasiInterpretationsSharingAwareWitness.eval x ≠
        quasiInterpretationsSharingAwareWitness.eval y) ∧
    (¬ ∃ e : SharedTerm → Nat, ∀ x y : SharedTerm, y = x → e y < e x) := by
  refine ⟨quasiInterpretationsSharingAwareWitness_accepts, ?_, ?_⟩
  · refine ⟨.shared (.node .leaf .leaf), .node .leaf .leaf, ?_, ?_, ?_⟩
    · simp [unshare]
    · intro h
      exact SharedTerm.noConfusion h
    · simp only [quasiInterpretationsSharingAwareWitness, unshare, freeSize, sharedCount]
      decide
  · rintro ⟨e, he⟩
    exact Nat.lt_irrefl (e .leaf) (he .leaf .leaf rfl)

/-- The mutation replaces the assignment by the constant zero, so the leaf size bound fails. -/
theorem quasiInterpretationsSharingAware_mutation :
    ¬ quasiInterpretationsSharingAwareLaws
      { quasiInterpretationsSharingAwareWitness with eval := fun _ => 0 } := by
  intro h
  have h0 : (1 : Nat) ≤ 0 := h.1
  omega

/-- A quasi-interpretation paired with an independently well-founded reduction order that contains
every reversed execution edge. -/
structure SharingAwareQuasiTerminationCertificate (M : quasiInterpretationsSharingAwareData) where
  /-- The reduction order. -/
  order : SharedTerm → SharedTerm → Prop
  /-- Every execution step decreases in the reduction order. -/
  covers : ∀ {x y : SharedTerm}, M.exec x y → order y x
  /-- The reduction order is well founded. -/
  wellFounded : WellFounded order

/-- The full scope: the quasi-interpretation supplies the resource bound, while the paired strict
order supplies termination. -/
def quasiInterpretationsSharingAware_scope : Prop :=
  ∀ (M : quasiInterpretationsSharingAwareData), quasiInterpretationsSharingAwareLaws M →
    quasiInterpretationsSharingAwareAccepts M →
    SharingAwareQuasiTerminationCertificate M →
    quasiInterpretationsSharingAwareResult M ∧
      WellFounded (fun y x : SharedTerm => M.exec x y)

/-- Pairing a sharing-aware quasi-interpretation with a compatible reduction order gives both the
resource bound and termination. -/
theorem quasiInterpretationsSharingAware_scope_proven : quasiInterpretationsSharingAware_scope := by
  intro M hL hA C
  exact ⟨quasiInterpretationsSharingAware_sound M hL hA,
    Subrelation.wf (fun {_ _} h => C.covers h) C.wellFounded⟩

/-- Add a stutter edge to the lawful witness.  All quasi-interpretation inequalities remain true,
but the execution relation is not terminating. -/
def quasiInterpretationsSharingAwareLoop : quasiInterpretationsSharingAwareData where
  eval := quasiInterpretationsSharingAwareWitness.eval
  exec := fun x y => quasiInterpretationsSharingAwareWitness.exec x y ∨ y = x
  readBack := quasiInterpretationsSharingAwareWitness.readBack

theorem quasiInterpretationsSharingAwareLoop_laws :
    quasiInterpretationsSharingAwareLaws quasiInterpretationsSharingAwareLoop := by
  rcases quasiInterpretationsSharingAwareWitness_laws with ⟨hLeaf, hNode, hShared, hStep, hRead⟩
  exact ⟨hLeaf, hNode, hShared, fun a => Or.inl (hStep a), hRead⟩

theorem quasiInterpretationsSharingAwareLoop_accepts :
    quasiInterpretationsSharingAwareAccepts quasiInterpretationsSharingAwareLoop := by
  intro x y hxy
  rcases hxy with hxy | rfl
  · exact quasiInterpretationsSharingAwareWitness_accepts hxy
  · exact le_rfl

/-- The claim that quasi-interpretation acceptance alone proves termination. -/
def quasiInterpretationsSharingAware_unpaired_termination : Prop :=
  ∀ (M : quasiInterpretationsSharingAwareData), quasiInterpretationsSharingAwareLaws M →
    quasiInterpretationsSharingAwareAccepts M →
    WellFounded (fun y x : SharedTerm => M.exec x y)

/-- Weak quasi-interpretation inequalities alone do not prove termination: the lawful loop witness
contains a stutter edge. -/
theorem quasiInterpretationsSharingAware_unpaired_termination_false :
    ¬ quasiInterpretationsSharingAware_unpaired_termination := by
  intro h
  have hWF := h quasiInterpretationsSharingAwareLoop
    quasiInterpretationsSharingAwareLoop_laws quasiInterpretationsSharingAwareLoop_accepts
  have hLoop : quasiInterpretationsSharingAwareLoop.exec .leaf .leaf := Or.inr rfl
  exact hWF.isIrrefl.irrefl .leaf hLoop

/-- Exact method identity for sharing-aware quasi-interpretations: the universal reachable-size
bound, the paired-order termination theorem, and the self-loop refutation of termination from the
weak resource inequality alone. -/
theorem quasiInterpretationsSharingAware_methodIdentity :
    quasiInterpretationsSharingAwareResult quasiInterpretationsSharingAwareWitness ∧
    quasiInterpretationsSharingAware_scope ∧
    ¬ quasiInterpretationsSharingAware_unpaired_termination :=
  ⟨quasiInterpretationsSharingAwareWitness_result,
    quasiInterpretationsSharingAware_scope_proven,
    quasiInterpretationsSharingAware_unpaired_termination_false⟩

end OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi
