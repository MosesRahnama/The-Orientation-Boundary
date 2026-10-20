import OperatorKO7.Meta.Methods.OrientationClosure.DependencyPairSoundness
import Mathlib.Tactic

/-!
# Size-change termination for minimal dependency chains

A size-change graph of a dependency pair `f(largs) → g(targs)` of a rewrite system `R` has a strict
arc `(i, j, true)` when `targs[j]` is a proper subterm of `largs[i]` and a weak arc `(i, j, false)`
when `targs[j] = largs[i]` (`pairGraph`). Along a minimal chain step, a strict arc gives
`TransGen (StepOrSub R)` from the target argument to the source argument and a weak arc gives
`ReflTransGen (StepOrSub R)` (`minChainStep_arc_sound`).

If every idempotent graph of the composition closure from a symbol to itself has a strict self-arc
(`SCTCriterion`), the minimal chain relation is well founded (`minChain_wf_of_sct`); under the
variable condition every term is strongly normalizing (`terminating_of_sct`). The proof applies the
infinite Ramsey theorem for pairs (`ramsey_pairs`, proved with `Filter.hyperfilter`) to the composed
graphs of an infinite chain.

Controls: the graph `{(0, 0, true)}` is not sound for the chain step `f(c) → f(c)` of `f(x) → f(x)`
(`strictArc_control`); that system fails the criterion, has an infinite minimal chain, and does not
terminate (`loop_control`). The free recursor satisfies the criterion
(`freeRecursorTRS_sctCriterion`).
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.SizeChangeTermination

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness

universe u v

/-! ## Infinite Ramsey theorem for pairs -/

/-- Infinite Ramsey theorem for pairs with finitely many colours: every colouring of the pairs of
natural numbers by a finite type is constant on the pairs `i < j` of some strictly increasing
subsequence. The proof uses the non-principal ultrafilter `Filter.hyperfilter ℕ`. -/
theorem ramsey_pairs {κ : Type*} [Finite κ] (c : ℕ → ℕ → κ) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∃ k : κ, ∀ i j, i < j → c (g i) (g j) = k := by
  obtain ⟨U, hUcof⟩ : ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ Filter.cofinite :=
    ⟨Filter.hyperfilter ℕ, Filter.hyperfilter_le_cofinite⟩
  have hconst : ∀ φ : ℕ → κ, ∃ k, {j | φ j = k} ∈ U := by
    intro φ
    obtain ⟨k, hk⟩ := Ultrafilter.eq_pure_of_finite (U.map φ)
    have hmem : ({k} : Set κ) ∈ U.map φ := by
      rw [hk]
      exact Ultrafilter.mem_pure.2 (Set.mem_singleton k)
    exact ⟨k, Ultrafilter.mem_map.1 hmem⟩
  have hIoi : ∀ x : ℕ, Set.Ioi x ∈ U := by
    intro x
    have hcof : Set.Ioi x ∈ Filter.cofinite := by
      rw [Filter.mem_cofinite, Set.compl_Ioi]
      exact Set.finite_le_nat x
    exact hUcof hcof
  choose col hcol using fun i => hconst (c i)
  obtain ⟨k₀, hk₀⟩ := hconst col
  have hstep : ∀ S : {S : Set ℕ // S ∈ U ∧ S ⊆ {i | col i = k₀}}, ∃ x, x ∈ S.1 ∧
      S.1 ∩ {j | c x j = k₀} ∩ Set.Ioi x ∈ U ∧
        S.1 ∩ {j | c x j = k₀} ∩ Set.Ioi x ⊆ {i | col i = k₀} := by
    rintro ⟨S, hSU, hSA⟩
    obtain ⟨x, hx⟩ := Ultrafilter.nonempty_of_mem hSU
    have hxk : col x = k₀ := hSA hx
    have hrow : {j | c x j = k₀} ∈ U := by
      rw [← hxk]
      exact hcol x
    have hmem : S ∩ {j | c x j = k₀} ∩ Set.Ioi x ∈ (U : Filter ℕ) :=
      Filter.inter_mem (Filter.inter_mem hSU hrow) (hIoi x)
    exact ⟨x, hx, hmem, fun y hy => hSA hy.1.1⟩
  choose nx hnxS hnxU hnxA using hstep
  obtain ⟨seq, hseq⟩ : ∃ seq : ℕ → {S : Set ℕ // S ∈ U ∧ S ⊆ {i | col i = k₀}}, ∀ n,
      (seq (n + 1)).1 = (seq n).1 ∩ {j | c (nx (seq n)) j = k₀} ∩ Set.Ioi (nx (seq n)) :=
    ⟨fun n => Nat.rec (motive := fun _ => {S : Set ℕ // S ∈ U ∧ S ⊆ {i | col i = k₀}})
      ⟨{i | col i = k₀}, hk₀, subset_rfl⟩
      (fun _ S => ⟨S.1 ∩ {j | c (nx S) j = k₀} ∩ Set.Ioi (nx S), hnxU S, hnxA S⟩) n,
      fun _ => rfl⟩
  have hanti : ∀ m l, (seq (m + l)).1 ⊆ (seq m).1 := by
    intro m l
    induction l with
    | zero => exact subset_rfl
    | succ l ih =>
      intro y hy
      rw [← Nat.add_assoc, hseq] at hy
      exact ih hy.1.1
  have hkey : ∀ i j, i < j → c (nx (seq i)) (nx (seq j)) = k₀ ∧ nx (seq i) < nx (seq j) := by
    intro i j hij
    obtain ⟨l, rfl⟩ : ∃ l, j = i + 1 + l := ⟨j - (i + 1), by omega⟩
    have hmem := hanti (i + 1) l (hnxS (seq (i + 1 + l)))
    rw [hseq] at hmem
    exact ⟨hmem.1.2, hmem.2⟩
  refine ⟨fun n => nx (seq n), ?_, k₀, fun i j hij => (hkey i j hij).1⟩
  intro i j hij
  exact (hkey i j hij).2

/-! ## Size-change graphs -/

/-- A size-change graph: a finite set of arcs `(i, j, strict)` from argument position `i` of one
call to argument position `j` of the next call. -/
abbrev SCGraph : Type := Finset (ℕ × ℕ × Bool)

namespace SCGraph

/-- Composition of size-change graphs: arcs `(i, j, b₁)` and `(j, k, b₂)` compose to
`(i, k, b₁ || b₂)`, a strict arc when either composed arc is strict. -/
def comp (G H : SCGraph) : SCGraph :=
  ((G ×ˢ H).filter fun p => p.1.2.1 = p.2.1).image fun p => (p.1.1, p.2.2.1, p.1.2.2 || p.2.2.2)

theorem mem_comp {G H : SCGraph} {i k : ℕ} {b : Bool} :
    (i, k, b) ∈ comp G H ↔ ∃ j b₁ b₂, (i, j, b₁) ∈ G ∧ (j, k, b₂) ∈ H ∧ b = (b₁ || b₂) := by
  constructor
  · intro h
    obtain ⟨⟨⟨i', j, b₁⟩, ⟨j', k', b₂⟩⟩, hp, he⟩ := Finset.mem_image.1 h
    obtain ⟨hpq, hj⟩ := Finset.mem_filter.1 hp
    obtain ⟨hG, hH⟩ := Finset.mem_product.1 hpq
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hj' : j = j' := hj
    subst hj'
    exact ⟨j, b₁, b₂, hG, hH, rfl⟩
  · rintro ⟨j, b₁, b₂, hG, hH, rfl⟩
    exact Finset.mem_image.2 ⟨((i, j, b₁), (j, k, b₂)),
      Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hG, hH⟩, rfl⟩, rfl⟩

theorem comp_assoc (G H K : SCGraph) : comp (comp G H) K = comp G (comp H K) := by
  ext ⟨i, l, b⟩
  simp only [mem_comp]
  constructor
  · rintro ⟨k, b₁₂, b₃, ⟨j, b₁, b₂, h₁, h₂, rfl⟩, h₃, rfl⟩
    exact ⟨j, b₁, b₂ || b₃, h₁, ⟨k, b₂, b₃, h₂, h₃, rfl⟩,
      by cases b₁ <;> cases b₂ <;> cases b₃ <;> rfl⟩
  · rintro ⟨j, b₁, b₂₃, h₁, ⟨k, b₂, b₃, h₂, h₃, rfl⟩, rfl⟩
    exact ⟨k, b₁ || b₂, b₃, ⟨j, b₁, b₂, h₁, h₂, rfl⟩, h₃,
      by cases b₁ <;> cases b₂ <;> cases b₃ <;> rfl⟩

/-- Arcs whose two argument positions are below `N`. -/
private def box (N : ℕ) : SCGraph :=
  Finset.range N ×ˢ (Finset.range N ×ˢ (Finset.univ : Finset Bool))

private theorem mem_box {N i j : ℕ} {b : Bool} : (i, j, b) ∈ box N ↔ i < N ∧ j < N := by
  simp [box]

private theorem comp_subset_box {G H : SCGraph} {N : ℕ} (hG : G ⊆ box N) (hH : H ⊆ box N) :
    comp G H ⊆ box N := by
  rintro ⟨i, k, b⟩ hb
  obtain ⟨j, b₁, b₂, h₁, h₂, -⟩ := mem_comp.1 hb
  exact mem_box.2 ⟨(mem_box.1 (hG h₁)).1, (mem_box.1 (hH h₂)).2⟩

end SCGraph

variable {sigma : Type u} {nu : Type v}

/-! ## The graph of a dependency pair -/

/-- The syntactic relation of an arc of a dependency-pair graph: proper subterm for a strict arc,
equality for a weak arc. -/
def ArcLabel : Bool → Term sigma nu → Term sigma nu → Prop
  | true, t, l => ProperSubterm t l
  | false, t, l => t = l

open Classical in
/-- The size-change graph of the dependency pair `f(largs) → g(targs)`: a strict arc `(i, j, true)`
when `targs[j]` is a proper subterm of `largs[i]`, a weak arc `(i, j, false)` when they are
equal. -/
noncomputable def pairGraph (largs targs : List (Term sigma nu)) : SCGraph :=
  (Finset.range largs.length ×ˢ (Finset.range targs.length ×ˢ (Finset.univ : Finset Bool))).filter
    fun a => ∃ l t, largs[a.1]? = some l ∧ targs[a.2.1]? = some t ∧ ArcLabel a.2.2 t l

open Classical in
theorem mem_pairGraph {largs targs : List (Term sigma nu)} {i j : ℕ} {b : Bool} :
    (i, j, b) ∈ pairGraph largs targs ↔
      ∃ l t, largs[i]? = some l ∧ targs[j]? = some t ∧ ArcLabel b t l := by
  unfold pairGraph
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨l, t, hl, ht, -⟩ := h
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 hl
    obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.1 ht
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
    exact ⟨hi, hj⟩

/-! ## Soundness of graphs -/

/-- `y` lies below `x` for rewriting combined with passing to arguments: in one or more steps when
`b = true`, in zero or more steps when `b = false`. -/
def Descends (R : TRS sigma nu) : Bool → Term sigma nu → Term sigma nu → Prop
  | true, y, x => Relation.TransGen (StepOrSub R) y x
  | false, y, x => Relation.ReflTransGen (StepOrSub R) y x

private theorem Descends.trans {R : TRS sigma nu} {b₁ b₂ : Bool} {x y z : Term sigma nu}
    (h₁ : Descends R b₁ y x) (h₂ : Descends R b₂ z y) : Descends R (b₁ || b₂) z x := by
  cases b₁ <;> cases b₂
  · exact Relation.ReflTransGen.trans h₂ h₁
  · exact Relation.TransGen.trans_left h₂ h₁
  · exact Relation.TransGen.trans_right h₂ h₁
  · exact Relation.TransGen.trans h₂ h₁

/-- Every arc `(i, j, b)` of `G` is realized between the argument lists `xs` and `ys`: the `j`-th
entry of `ys` descends from the `i`-th entry of `xs`, strictly when `b = true`. -/
def GraphSound (R : TRS sigma nu) (G : SCGraph) (xs ys : List (Term sigma nu)) : Prop :=
  ∀ (i j : ℕ) (b : Bool), (i, j, b) ∈ G →
    ∃ x y, xs[i]? = some x ∧ ys[j]? = some y ∧ Descends R b y x

/-- Soundness composes along consecutive argument lists. -/
theorem GraphSound.comp {R : TRS sigma nu} {G H : SCGraph} {xs ys zs : List (Term sigma nu)}
    (hG : GraphSound R G xs ys) (hH : GraphSound R H ys zs) :
    GraphSound R (SCGraph.comp G H) xs zs := by
  intro i k b hb
  obtain ⟨j, b₁, b₂, h₁, h₂, rfl⟩ := SCGraph.mem_comp.1 hb
  obtain ⟨x, y, hx, hy, hxy⟩ := hG i j b₁ h₁
  obtain ⟨y', z, hy', hz, hyz⟩ := hH j k b₂ h₂
  rw [hy] at hy'
  cases hy'
  exact ⟨x, z, hx, hz, Descends.trans hxy hyz⟩

/-- The graph of a dependency pair is sound for every instance of the pair reached by argument
rewriting. -/
theorem pairGraph_sound {R : TRS sigma nu} {xs largs targs : List (Term sigma nu)}
    {σ : Subst sigma nu}
    (hreach : Relation.ReflTransGen (ArgStep R) xs (Subst.applyList σ largs)) :
    GraphSound R (pairGraph largs targs) xs (Subst.applyList σ targs) := by
  intro i j b hb
  obtain ⟨l, t, hl, ht, hlab⟩ := mem_pairGraph.1 hb
  have hx' : (Subst.applyList σ largs)[i]? = some (Subst.apply σ l) := by
    rw [Subst.applyList_eq_map, List.getElem?_map, hl]
    rfl
  have hy : (Subst.applyList σ targs)[j]? = some (Subst.apply σ t) := by
    rw [Subst.applyList_eq_map, List.getElem?_map, ht]
    rfl
  obtain ⟨x, hx, hxx⟩ := argSteps_getElem? hreach i _ hx'
  refine ⟨x, _, hx, hy, ?_⟩
  cases b with
  | true =>
    exact Relation.TransGen.trans_left (ProperSubterm.transGen (ProperSubterm.subst σ hlab))
      (steps_reflTransGen hxx)
  | false =>
    have hlt : t = l := hlab
    subst hlt
    exact steps_reflTransGen hxx

/-! ## Dependency pairs and chain steps -/

/-- `f(largs) → g(targs)` is a dependency pair of `R`: `f(largs)` is the left-hand side of a rule
and `g(targs)` a subterm of its right-hand side with a defined root `g`. -/
def IsDepPair (R : TRS sigma nu) (f : sigma) (largs : List (Term sigma nu)) (g : sigma)
    (targs : List (Term sigma nu)) : Prop :=
  ∃ rule ∈ R, rule.lhs = .app f largs ∧ IsSubterm (.app g targs) rule.rhs ∧ IsDefined R g

private theorem IsDepPair.isDefined_left {R : TRS sigma nu} {f g : sigma}
    {largs targs : List (Term sigma nu)} (h : IsDepPair R f largs g targs) : IsDefined R f := by
  obtain ⟨rule, hrule, hl, -, -⟩ := h
  exact ⟨rule, hrule, largs, hl⟩

/-- Every minimal chain step passes through a dependency pair: the source arguments rewrite to an
instance of the pair's left arguments, and the target arguments are the same instance of the pair's
right arguments. -/
theorem minChainStep_depPair {R : TRS sigma nu} {c d : sigma × List (Term sigma nu)}
    (h : MinChainStep R c d) : ∃ (largs targs : List (Term sigma nu)) (σ : Subst sigma nu),
      IsDepPair R c.1 largs d.1 targs ∧
        Relation.ReflTransGen (ArgStep R) c.2 (Subst.applyList σ largs) ∧
        d.2 = Subst.applyList σ targs := by
  obtain ⟨-, -, xs, hreach, rule, hrule, σ, hl, targs, hsub, hdef, hd⟩ := h
  obtain ⟨g0, largs, hg0⟩ := lhs_eq_app rule
  have hl' := hl
  rw [hg0, Subst.apply_app] at hl'
  simp only [Term.app.injEq] at hl'
  obtain ⟨hf, hxsEq⟩ := hl'
  refine ⟨largs, targs, σ, ⟨rule, hrule, ?_, hsub, hdef⟩, ?_, hd⟩
  · rw [hg0, hf]
  · rw [← hxsEq]
    exact hreach

/-- Arc soundness along a minimal chain step: the step passes through a dependency pair whose strict
arcs give `TransGen (StepOrSub R)` and whose weak arcs give `ReflTransGen (StepOrSub R)` from the
target argument to the source argument. -/
theorem minChainStep_arc_sound {R : TRS sigma nu} {c d : sigma × List (Term sigma nu)}
    (h : MinChainStep R c d) : ∃ largs targs : List (Term sigma nu),
      IsDepPair R c.1 largs d.1 targs ∧
      (∀ i j : ℕ, (i, j, true) ∈ pairGraph largs targs →
        ∃ x y, c.2[i]? = some x ∧ d.2[j]? = some y ∧ Relation.TransGen (StepOrSub R) y x) ∧
      (∀ i j : ℕ, (i, j, false) ∈ pairGraph largs targs →
        ∃ x y, c.2[i]? = some x ∧ d.2[j]? = some y ∧ Relation.ReflTransGen (StepOrSub R) y x) := by
  obtain ⟨largs, targs, σ, hdp, hreach, hd⟩ := minChainStep_depPair h
  have hs : GraphSound R (pairGraph largs targs) c.2 d.2 := by
    rw [hd]
    exact pairGraph_sound hreach
  exact ⟨largs, targs, hdp, fun i j hij => hs i j true hij, fun i j hij => hs i j false hij⟩

/-! ## A bound on argument positions -/

private theorem length_le_sizeList (args : List (Term sigma nu)) :
    args.length ≤ Term.sizeList args := by
  induction args with
  | nil => simp
  | cons a as ih =>
    rw [List.length_cons, Term.sizeList_cons]
    have := Term.one_le_size a
    omega

private theorem length_lt_size (f : sigma) (args : List (Term sigma nu)) :
    args.length < Term.size (Term.app f args) := by
  rw [Term.size_app]
  have := length_le_sizeList args
  omega

private theorem isSubterm_size_le {w t : Term sigma nu} (h : IsSubterm w t) :
    Term.size w ≤ Term.size t := by
  induction h with
  | refl => exact le_rfl
  | arg f args hmem _ ih => exact ih.trans (Term.size_lt_of_mem (f := f) hmem).le

/-- A bound on the argument positions of all dependency pairs of `R`. -/
private def sizeBound (R : TRS sigma nu) : ℕ :=
  (R.map fun rule => Term.size rule.lhs + Term.size rule.rhs).sum

private theorem le_sizeBound {R : TRS sigma nu} {rule : Rule sigma nu} (h : rule ∈ R) :
    Term.size rule.lhs + Term.size rule.rhs ≤ sizeBound R := by
  induction R with
  | nil => simp at h
  | cons r rs ih =>
    simp only [sizeBound, List.map_cons, List.sum_cons] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h
      omega

private theorem IsDepPair.length_le {R : TRS sigma nu} {f g : sigma}
    {largs targs : List (Term sigma nu)} (h : IsDepPair R f largs g targs) :
    largs.length ≤ sizeBound R ∧ targs.length ≤ sizeBound R := by
  obtain ⟨rule, hrule, hl, hsub, -⟩ := h
  have hb := le_sizeBound hrule
  have h1 := length_lt_size f largs
  have h2 := length_lt_size g targs
  have h3 := isSubterm_size_le hsub
  rw [← hl] at h1
  constructor <;> omega

private theorem pairGraph_subset_box {largs targs : List (Term sigma nu)} {N : ℕ}
    (hl : largs.length ≤ N) (ht : targs.length ≤ N) : pairGraph largs targs ⊆ SCGraph.box N := by
  rintro ⟨i, j, b⟩ hb
  obtain ⟨l, t, hl', ht', -⟩ := mem_pairGraph.1 hb
  obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 hl'
  obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.1 ht'
  exact SCGraph.mem_box.2 ⟨by omega, by omega⟩

private theorem finite_defined (R : TRS sigma nu) : Set.Finite {f | IsDefined R f} := by
  have hsub : {f | IsDefined R f} ⊆
      ⋃ rule ∈ {r | r ∈ R}, {f | ∃ largs : List (Term sigma nu), rule.lhs = .app f largs} := by
    rintro f ⟨rule, hrule, largs, hl⟩
    exact Set.mem_biUnion hrule ⟨largs, hl⟩
  refine Set.Finite.subset (Set.Finite.biUnion (List.finite_toSet R) fun rule _ => ?_) hsub
  refine Set.Subsingleton.finite ?_
  rintro f ⟨l₁, h₁⟩ g ⟨l₂, h₂⟩
  rw [h₁] at h₂
  exact (Term.app.inj h₂).1

/-! ## The composition closure and the criterion -/

/-- The composition closure of the dependency-pair graphs of `R`, indexed by source and target
symbols: every pair graph from `f` to `g`, and every composition of a closure graph from `f` to `g`
with a pair graph from `g` to `h`. -/
inductive SCClosure (R : TRS sigma nu) : sigma → sigma → SCGraph → Prop
  | pair {f g : sigma} {largs targs : List (Term sigma nu)} :
      IsDepPair R f largs g targs → SCClosure R f g (pairGraph largs targs)
  | comp {f g h : sigma} {G : SCGraph} {largs targs : List (Term sigma nu)} :
      SCClosure R f g G → IsDepPair R g largs h targs →
        SCClosure R f h (SCGraph.comp G (pairGraph largs targs))

/-- The closure is closed under composition of any two of its graphs. -/
theorem SCClosure.trans {R : TRS sigma nu} {f g h : sigma} {G H : SCGraph}
    (hG : SCClosure R f g G) (hH : SCClosure R g h H) : SCClosure R f h (SCGraph.comp G H) := by
  induction hH with
  | pair hp => exact SCClosure.comp hG hp
  | comp _ hp ih =>
    rw [← SCGraph.comp_assoc]
    exact SCClosure.comp ih hp

/-- The size-change criterion: every idempotent graph of the closure from a symbol to itself has a
strict self-arc `(i, i, true)`. -/
def SCTCriterion (R : TRS sigma nu) : Prop :=
  ∀ (f : sigma) (G : SCGraph), SCClosure R f f G → SCGraph.comp G G = G → ∃ i, (i, i, true) ∈ G

/-! ## Graphs along a chain -/

/-- The composition `P i ; P (i + 1) ; … ; P (i + n)` of consecutive graphs. -/
private def pathGraph (P : ℕ → SCGraph) (i : ℕ) : ℕ → SCGraph
  | 0 => P i
  | n + 1 => SCGraph.comp (pathGraph P i n) (P (i + n + 1))

private theorem pathGraph_succ (P : ℕ → SCGraph) (i n : ℕ) :
    pathGraph P i (n + 1) = SCGraph.comp (pathGraph P i n) (P (i + n + 1)) := rfl

private theorem pathGraph_split (P : ℕ → SCGraph) (i m : ℕ) : ∀ n,
    pathGraph P i (m + n + 1) = SCGraph.comp (pathGraph P i m) (pathGraph P (i + m + 1) n)
  | 0 => pathGraph_succ P i m
  | n + 1 => by
    rw [show m + (n + 1) + 1 = m + n + 1 + 1 by omega, pathGraph_succ, pathGraph_split P i m n,
      pathGraph_succ P (i + m + 1) n, SCGraph.comp_assoc,
      show i + (m + n + 1) + 1 = i + m + 1 + n + 1 by omega]

/-- The composed graph from call `i` to call `j` of a chain. -/
private def chainGraph (P : ℕ → SCGraph) (i j : ℕ) : SCGraph := pathGraph P i (j - i - 1)

private theorem chainGraph_split (P : ℕ → SCGraph) {i j l : ℕ} (hij : i < j) (hjl : j < l) :
    chainGraph P i l = SCGraph.comp (chainGraph P i j) (chainGraph P j l) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = i + m + 1 := ⟨j - i - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, l = i + m + 1 + n + 1 := ⟨l - (i + m + 1) - 1, by omega⟩
  unfold chainGraph
  rw [show i + m + 1 + n + 1 - i - 1 = m + n + 1 by omega, show i + m + 1 - i - 1 = m by omega,
    show i + m + 1 + n + 1 - (i + m + 1) - 1 = n by omega]
  exact pathGraph_split P i m n

private theorem pathGraph_sound {R : TRS sigma nu} {P : ℕ → SCGraph}
    {xs : ℕ → List (Term sigma nu)} (hP : ∀ n, GraphSound R (P n) (xs n) (xs (n + 1)))
    (i : ℕ) : ∀ n, GraphSound R (pathGraph P i n) (xs i) (xs (i + n + 1))
  | 0 => hP i
  | n + 1 => GraphSound.comp (pathGraph_sound hP i n) (hP (i + n + 1))

private theorem chainGraph_sound {R : TRS sigma nu} {P : ℕ → SCGraph}
    {xs : ℕ → List (Term sigma nu)} (hP : ∀ n, GraphSound R (P n) (xs n) (xs (n + 1)))
    {i j : ℕ} (hij : i < j) : GraphSound R (chainGraph P i j) (xs i) (xs j) := by
  have h := pathGraph_sound hP i (j - i - 1)
  rw [show i + (j - i - 1) + 1 = j by omega] at h
  exact h

private theorem pathGraph_closure {R : TRS sigma nu} {sym : ℕ → sigma}
    {L T : ℕ → List (Term sigma nu)} (hdp : ∀ n, IsDepPair R (sym n) (L n) (sym (n + 1)) (T n))
    (i : ℕ) :
    ∀ n, SCClosure R (sym i) (sym (i + n + 1)) (pathGraph (fun m => pairGraph (L m) (T m)) i n)
  | 0 => SCClosure.pair (hdp i)
  | n + 1 => SCClosure.comp (pathGraph_closure hdp i n) (hdp (i + n + 1))

private theorem chainGraph_closure {R : TRS sigma nu} {sym : ℕ → sigma}
    {L T : ℕ → List (Term sigma nu)} (hdp : ∀ n, IsDepPair R (sym n) (L n) (sym (n + 1)) (T n))
    {i j : ℕ} (hij : i < j) :
    SCClosure R (sym i) (sym j) (chainGraph (fun m => pairGraph (L m) (T m)) i j) := by
  have h := pathGraph_closure hdp i (j - i - 1)
  rw [show i + (j - i - 1) + 1 = j by omega] at h
  exact h

private theorem pathGraph_subset_box {P : ℕ → SCGraph} {N : ℕ}
    (hP : ∀ n, P n ⊆ SCGraph.box N) (i : ℕ) : ∀ n, pathGraph P i n ⊆ SCGraph.box N
  | 0 => hP i
  | n + 1 => SCGraph.comp_subset_box (pathGraph_subset_box hP i n) (hP (i + n + 1))

/-! ## Soundness -/

private theorem not_rel_self_of_acc {α : Sort*} {r : α → α → Prop} {a : α} (h : Acc r a) :
    ¬ r a a := by
  induction h with
  | intro x _ ih => exact fun hxx => ih x hxx hxx

/-- Size-change soundness for minimal chains: if every idempotent graph of the composition closure
from a symbol to itself has a strict self-arc, the minimal dependency-chain relation of `R` is well
founded. -/
theorem minChain_wf_of_sct {R : TRS sigma nu} (hsct : SCTCriterion R) :
    WellFounded (fun d c => MinChainStep R c d) := by
  rw [WellFounded.wellFounded_iff_no_descending_seq]
  refine ⟨fun ⟨ch, hch⟩ => ?_⟩
  have hch' : ∀ n, MinChainStep R (ch n) (ch (n + 1)) := hch
  choose L T σ hdp hreach hd using fun n => minChainStep_depPair (hch' n)
  have hsound : ∀ n, GraphSound R (pairGraph (L n) (T n)) (ch n).2 (ch (n + 1)).2 := by
    intro n
    rw [hd n]
    exact pairGraph_sound (hreach n)
  have hbox : ∀ i j, chainGraph (fun m => pairGraph (L m) (T m)) i j ∈
      (SCGraph.box (sizeBound R)).powerset := by
    intro i j
    refine Finset.mem_powerset.2 (pathGraph_subset_box (fun n => ?_) i _)
    obtain ⟨h1, h2⟩ := IsDepPair.length_le (hdp n)
    exact pairGraph_subset_box h1 h2
  have hdefd : ∀ n, (ch n).1 ∈ {f | IsDefined R f} := fun n => IsDepPair.isDefined_left (hdp n)
  haveI : Finite ↥{f | IsDefined R f} := (finite_defined R).to_subtype
  obtain ⟨g, hg, k, hk⟩ := ramsey_pairs fun i j =>
    ((⟨(ch j).1, hdefd j⟩ : ↥{f | IsDefined R f}),
      (⟨chainGraph (fun m => pairGraph (L m) (T m)) i j, hbox i j⟩ :
        {G : SCGraph // G ∈ (SCGraph.box (sizeBound R)).powerset}))
  have hsym : ∀ i j, i < j → (ch (g j)).1 = k.1.1 := fun i j hij =>
    congrArg Subtype.val (congrArg Prod.fst (hk i j hij))
  have hgr : ∀ i j, i < j → chainGraph (fun m => pairGraph (L m) (T m)) (g i) (g j) = k.2.1 :=
    fun i j hij => congrArg Subtype.val (congrArg Prod.snd (hk i j hij))
  have hidem : SCGraph.comp k.2.1 k.2.1 = k.2.1 := by
    have hs := chainGraph_split (fun m => pairGraph (L m) (T m))
      (hg (show 1 < 2 by norm_num)) (hg (show 2 < 3 by norm_num))
    rw [hgr 1 3 (by norm_num), hgr 1 2 (by norm_num), hgr 2 3 (by norm_num)] at hs
    exact hs.symm
  have hcl : SCClosure R (ch (g 1)).1 (ch (g 1)).1 k.2.1 := by
    have h : SCClosure R (ch (g 1)).1 (ch (g 2)).1
        (chainGraph (fun m => pairGraph (L m) (T m)) (g 1) (g 2)) :=
      chainGraph_closure (sym := fun n => (ch n).1) hdp (hg (show 1 < 2 by norm_num))
    rw [hgr 1 2 (by norm_num), (hsym 0 2 (by norm_num)).trans (hsym 0 1 (by norm_num)).symm] at h
    exact h
  obtain ⟨p, hp⟩ := hsct _ _ hcl hidem
  have hdesc : ∀ m, ∃ x y, (ch (g m)).2[p]? = some x ∧ (ch (g (m + 1))).2[p]? = some y ∧
      Relation.TransGen (StepOrSub R) y x := by
    intro m
    have hs := chainGraph_sound (P := fun q => pairGraph (L q) (T q)) (xs := fun q => (ch q).2)
      hsound (hg (show m < m + 1 by omega))
    rw [hgr m (m + 1) (by omega)] at hs
    exact hs p p true hp
  have key : ∀ x, Acc (Relation.TransGen (StepOrSub R)) x →
      ∀ m, (ch (g m)).2[p]? = some x → False := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro m hm
      obtain ⟨x', y, hx', hy, hyx⟩ := hdesc m
      rw [hm] at hx'
      cases hx'
      exact ih y hyx (m + 1) hy
  obtain ⟨x0, _, hx0, -, -⟩ := hdesc 0
  have hsn : SN R x0 := (hch' (g 0)).1 x0 (List.mem_of_getElem? hx0)
  exact key x0 (acc_stepOrSub_of_sn hsn).transGen 0 hx0

/-- Termination by the size-change criterion: under the variable condition, the criterion makes
every term strongly normalizing, through dependency-pair soundness. -/
theorem terminating_of_sct [DecidableEq nu] (R : TRS sigma nu)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) (hsct : SCTCriterion R) :
    ∀ t : Term sigma nu, SN R t :=
  terminating_of_minChain_wf R hvars (minChain_wf_of_sct hsct)

/-! ## Controls -/

private theorem not_properSubterm_var {t : Term sigma nu} {x : nu} :
    ¬ ProperSubterm t (.var x) := by
  intro h
  cases h

/-- Symbols of the looping control: a unary `f` and a constant `c`. -/
inductive LoopSym
  | f
  | c
  deriving DecidableEq

/-- The rule `f(x) → f(x)`. -/
def loopRule : Rule LoopSym Nat where
  lhs := .app .f [.var 0]
  rhs := .app .f [.var 0]
  lhs_isApp := rfl

/-- The one-rule system `f(x) → f(x)`. -/
def loopTRS : TRS LoopSym Nat := [loopRule]

/-- The argument list `[x]` of both sides of `f(x) → f(x)`. -/
def loopArgs : List (Term LoopSym Nat) := [.var 0]

/-- The call `f(c)`. -/
def loopCall : LoopSym × List (Term LoopSym Nat) := (.f, [.app .c []])

private theorem loopTRS_isDefined_f : IsDefined loopTRS .f :=
  ⟨loopRule, List.mem_singleton.2 rfl, loopArgs, rfl⟩

private theorem loopTRS_not_isDefined_c : ¬ IsDefined loopTRS .c := by
  rintro ⟨rule, hrule, largs, hl⟩
  obtain rfl := List.mem_singleton.1 hrule
  cases (Term.app.inj hl).1

private theorem loopTRS_sn_c : SN loopTRS (.app .c []) :=
  sn_app_of_not_defined loopTRS_not_isDefined_c [] (by simp)

private theorem loopTRS_depPair : IsDepPair loopTRS .f loopArgs .f loopArgs :=
  ⟨loopRule, List.mem_singleton.2 rfl, rfl, .refl _, loopTRS_isDefined_f⟩

private theorem loopTRS_minChainStep : MinChainStep loopTRS loopCall loopCall := by
  have hsn : ∀ a ∈ loopCall.2, SN loopTRS a := by
    intro a ha
    obtain rfl := List.mem_singleton.1 ha
    exact loopTRS_sn_c
  exact ⟨hsn, hsn, loopCall.2, .refl, loopRule, List.mem_singleton.2 rfl, fun _ => .app .c [], rfl,
    loopArgs, .refl _, loopTRS_isDefined_f, rfl⟩

private theorem loopTRS_loop : Step loopTRS (.app .f [.app .c []]) (.app .f [.app .c []]) :=
  Step.root ⟨loopRule, List.mem_singleton.2 rfl, fun _ => .app .c [], rfl, rfl⟩

private theorem mem_loopGraph {i j : ℕ} {b : Bool} :
    (i, j, b) ∈ pairGraph loopArgs loopArgs ↔ i = 0 ∧ j = 0 ∧ b = false := by
  rw [mem_pairGraph]
  constructor
  · rintro ⟨l, t, hl, ht, hlab⟩
    cases i with
    | succ i => simp [loopArgs] at hl
    | zero =>
      cases j with
      | succ j => simp [loopArgs] at ht
      | zero =>
        have hl' : Term.var 0 = l := Option.some.inj hl
        have ht' : Term.var 0 = t := Option.some.inj ht
        subst hl' ht'
        cases b with
        | true => exact (not_properSubterm_var hlab).elim
        | false => exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨.var 0, .var 0, rfl, rfl, rfl⟩

private theorem loopGraph_idem :
    SCGraph.comp (pairGraph loopArgs loopArgs) (pairGraph loopArgs loopArgs) =
      pairGraph loopArgs loopArgs := by
  ext ⟨i, j, b⟩
  rw [SCGraph.mem_comp, mem_loopGraph]
  constructor
  · rintro ⟨m, b₁, b₂, h₁, h₂, rfl⟩
    obtain ⟨rfl, rfl, rfl⟩ := mem_loopGraph.1 h₁
    obtain ⟨-, rfl, rfl⟩ := mem_loopGraph.1 h₂
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨0, false, false, mem_loopGraph.2 ⟨rfl, rfl, rfl⟩, mem_loopGraph.2 ⟨rfl, rfl, rfl⟩, rfl⟩

/-- A strict arc on a position that does not descend is unsound: `f(c) → f(c)` is a minimal chain
step of `f(x) → f(x)`, the graph `{(0, 0, true)}` is not sound for it, and the pair graph of the
step has no arc `(0, 0, true)`. -/
theorem strictArc_control :
    MinChainStep loopTRS loopCall loopCall ∧
      ¬ GraphSound loopTRS {(0, 0, true)} loopCall.2 loopCall.2 ∧
      (0, 0, true) ∉ pairGraph loopArgs loopArgs := by
  refine ⟨loopTRS_minChainStep, fun h => ?_, fun h => ?_⟩
  · obtain ⟨x, y, hx, hy, hyx⟩ := h 0 0 true (Finset.mem_singleton_self _)
    have hx' : Term.app LoopSym.c [] = x := Option.some.inj hx
    have hy' : Term.app LoopSym.c [] = y := Option.some.inj hy
    subst hx' hy'
    exact not_rel_self_of_acc (acc_stepOrSub_of_sn loopTRS_sn_c).transGen hyx
  · cases (mem_loopGraph.1 h).2.2

/-- A recursive pair whose idempotent closure graph has no strict self-arc: `f(x) → f(x)` satisfies
the variable condition, its pair graph from `f` to `f` is an idempotent closure graph with no arc
`(i, i, true)`, the criterion fails, an infinite minimal chain exists, the minimal chain relation is
not well founded, and `f(c)` is not strongly normalizing. -/
theorem loop_control :
    (∀ rule ∈ loopTRS, Term.vars rule.rhs ⊆ Term.vars rule.lhs) ∧
      SCClosure loopTRS .f .f (pairGraph loopArgs loopArgs) ∧
      SCGraph.comp (pairGraph loopArgs loopArgs) (pairGraph loopArgs loopArgs) =
        pairGraph loopArgs loopArgs ∧
      (∀ i : ℕ, (i, i, true) ∉ pairGraph loopArgs loopArgs) ∧
      ¬ SCTCriterion loopTRS ∧
      (∃ ch : ℕ → LoopSym × List (Term LoopSym Nat),
        ∀ n, MinChainStep loopTRS (ch n) (ch (n + 1))) ∧
      ¬ WellFounded (fun d c => MinChainStep loopTRS c d) ∧
      ¬ SN loopTRS (.app .f [.app .c []]) := by
  have hvars : ∀ rule ∈ loopTRS, Term.vars rule.rhs ⊆ Term.vars rule.lhs := by
    intro rule hrule
    obtain rfl := List.mem_singleton.1 hrule
    exact Finset.Subset.refl _
  have hnostrict : ∀ i : ℕ, (i, i, true) ∉ pairGraph loopArgs loopArgs := fun i h => by
    cases (mem_loopGraph.1 h).2.2
  refine ⟨hvars, .pair loopTRS_depPair, loopGraph_idem, hnostrict, fun hsct => ?_,
    ⟨fun _ => loopCall, fun _ => loopTRS_minChainStep⟩,
    fun hwf => not_rel_self_of_acc (hwf.apply loopCall) loopTRS_minChainStep,
    fun hsn => not_rel_self_of_acc hsn loopTRS_loop⟩
  obtain ⟨i, hi⟩ := hsct .f _ (.pair loopTRS_depPair) loopGraph_idem
  exact hnostrict i hi

/-! ## The free recursor -/

private theorem freeRecursorTRS_depPair {f g : FreeSym} {largs targs : List (Term FreeSym Nat)}
    (h : IsDepPair freeRecursorTRS f largs g targs) :
    largs = [.var 0, .var 1, .app .succ [.var 2]] ∧ targs = [.var 0, .var 1, .var 2] := by
  obtain ⟨rule, hrule, hl, hsub, hdef⟩ := h
  rw [freeRecursorTRS_defined_iff] at hdef
  subst hdef
  simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl
  · simp only [zeroRule] at hsub
    exact absurd hsub not_isSubterm_app_var
  · refine ⟨?_, succRule_rhs_recur_subterm hsub⟩
    simp only [succRule, Term.app.injEq] at hl
    exact hl.2.symm

private theorem freeRecursorTRS_pairGraph_strict {f g : FreeSym}
    {largs targs : List (Term FreeSym Nat)} (h : IsDepPair freeRecursorTRS f largs g targs) :
    (2, 2, true) ∈ pairGraph largs targs := by
  obtain ⟨rfl, rfl⟩ := freeRecursorTRS_depPair h
  exact mem_pairGraph.2 ⟨.app .succ [.var 2], .var 2, rfl, rfl,
    ProperSubterm.arg FreeSym.succ [Term.var 2] List.mem_cons_self (IsSubterm.refl _)⟩

private theorem freeRecursorTRS_closure_strict {f g : FreeSym} {G : SCGraph}
    (h : SCClosure freeRecursorTRS f g G) : (2, 2, true) ∈ G := by
  induction h with
  | pair hp => exact freeRecursorTRS_pairGraph_strict hp
  | comp _ hp ih =>
    exact SCGraph.mem_comp.2 ⟨2, true, true, ih, freeRecursorTRS_pairGraph_strict hp, rfl⟩

/-- The free recursor satisfies the size-change criterion: every graph of its closure has the strict
self-arc `(2, 2, true)` on the counter argument. -/
theorem freeRecursorTRS_sctCriterion : SCTCriterion freeRecursorTRS :=
  fun _ _ hG _ => ⟨2, freeRecursorTRS_closure_strict hG⟩

/-- The minimal chain relation of the free recursor is well founded by the size-change
criterion. -/
theorem freeRecursorTRS_minChain_wf_bySCT :
    WellFounded (fun d c => MinChainStep freeRecursorTRS c d) :=
  minChain_wf_of_sct freeRecursorTRS_sctCriterion

/-- The free recursor terminates by the size-change criterion. -/
theorem freeRecursorTRS_terminating_bySCT : ∀ t : Term FreeSym Nat, SN freeRecursorTRS t :=
  terminating_of_sct freeRecursorTRS freeRecursorTRS_vars freeRecursorTRS_sctCriterion

end OperatorKO7.Methods.OrientationClosure.SizeChangeTermination
