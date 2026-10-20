import OperatorKO7.Meta.BoundaryObserver.StochasticGraph
import OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite

set_option autoImplicit false

/-!
# The conflict graph of a deterministic reading

Manuscript: the paragraph
after `thm:stochastic-side-records` in the paper *Entangled Merged Pairs*.
The deterministic reading of `q : X → Y` has `K x y = 1` if `y = q x` and `0` otherwise. With a
target `P`, two inputs conflict exactly if they have one record and two target values. No edge
joins two fibers, the conflict graph is the union of its graphs on the fibers, and the graph on one
fiber is isomorphic to the complete multipartite graph with the target classes of the fiber as its
parts. On a finite input set the chromatic number, and the least number of side symbols that
admits a zero-error decoder, equal the largest number of target values on one fiber; for the
identity target that number is the largest fiber, the least size of a place coordinate.
Relation: graphs and decoders of finite channels. External trust: none.
-/

namespace OperatorKO7.Meta.BoundaryObserver.DeterministicConflictGraph

open StochasticGraph
open OperatorKO7.Meta.OperationalInexpressibility.Confusability
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit

variable {X Y V : Type*}

/-! ## The graph on each fiber is complete multipartite -/

/-- Two inputs conflict exactly if they have one record and two target values. -/
theorem conflict_adj_iff [Fintype Y] [DecidableEq Y] (q : X → Y) (P : X → V) (x x' : X) :
    (conflictGraph (deterministic q).prob P).Adj x x' ↔ q x = q x' ∧ P x ≠ P x' := by
  rw [deterministic_graph]
  exact confusabilityGraph_adj_iff q P x x'

/-- Inputs in two different fibers never conflict. -/
theorem not_adj_of_record_ne [Fintype Y] [DecidableEq Y] (q : X → Y) (P : X → V) {x x' : X}
    (h : q x ≠ q x') : ¬ (conflictGraph (deterministic q).prob P).Adj x x' :=
  fun ha => h ((conflict_adj_iff q P x x').mp ha).1

/-- The fiber of `q` over the record `y`. -/
abbrev fiber (q : X → Y) (y : Y) : Set X := {x | q x = y}

/-- The fibers of `q` are pairwise disjoint. -/
theorem fiber_pairwise_disjoint (q : X → Y) : Pairwise (Function.onFun Disjoint (fiber q)) := by
  intro y y' hne
  refine Set.disjoint_left.mpr (fun x hx hx' => hne ?_)
  have h1 : q x = y := hx
  have h2 : q x = y' := hx'
  exact h1.symm.trans h2

/-- The conflict graph restricted to the fiber over `y`. -/
abbrev fiberGraph [Fintype Y] [DecidableEq Y] (q : X → Y) (P : X → V) (y : Y) :
    SimpleGraph (fiber q y) :=
  (conflictGraph (deterministic q).prob P).induce (fiber q y)

/-- The target class of the attained value `v` inside the fiber over `y`. -/
abbrev targetClass (q : X → Y) (P : X → V) (y : Y) (v : FiberTargetValues q P y) :=
  {x : X // q x = y ∧ P x = v.1}

/-- Every part is nonempty: an attained value has a state of the fiber carrying it. -/
theorem targetClass_nonempty (q : X → Y) (P : X → V) (y : Y) (v : FiberTargetValues q P y) :
    Nonempty (targetClass q P y v) := by
  obtain ⟨x, hx, hv⟩ := v.2
  exact ⟨⟨x, hx, hv⟩⟩

/-- The graph on the fiber over `y` is the complete multipartite graph with the target classes of
the fiber as its parts. -/
def fiberGraphIso [Fintype Y] [DecidableEq Y] (q : X → Y) (P : X → V) (y : Y) :
    fiberGraph q P y ≃g SimpleGraph.completeMultipartiteGraph (targetClass q P y) where
  toFun x := ⟨⟨P x.1, x.1, x.2, rfl⟩, ⟨x.1, x.2, rfl⟩⟩
  invFun c := ⟨c.2.1, c.2.2.1⟩
  left_inv _ := rfl
  right_inv c := Sigma.subtype_ext (Subtype.ext c.2.2.2) rfl
  map_rel_iff' := by
    intro a b
    have ha : q a.1 = y := a.2
    have hb : q b.1 = y := b.2
    change (⟨P a.1, a.1, a.2, rfl⟩ : FiberTargetValues q P y) ≠ ⟨P b.1, b.1, b.2, rfl⟩ ↔
      (conflictGraph (deterministic q).prob P).Adj a.1 b.1
    rw [conflict_adj_iff]
    simp only [ne_eq, Subtype.mk.injEq]
    exact ⟨fun h => ⟨ha.trans hb.symm, h⟩, fun h => h.2⟩

/-- The graph on one fiber is complete multipartite: non-adjacency is transitive. -/
theorem fiberGraph_isCompleteMultipartite [Fintype Y] [DecidableEq Y] (q : X → Y) (P : X → V)
    (y : Y) : (fiberGraph q P y).IsCompleteMultipartite := by
  intro a b c hab hbc hac
  have ha : q a.1 = y := a.2
  have hb : q b.1 = y := b.2
  have hc : q c.1 = y := c.2
  have hab' : P a.1 = P b.1 := by
    by_contra hne
    exact hab ((conflict_adj_iff q P a.1 b.1).mpr ⟨ha.trans hb.symm, hne⟩)
  have hbc' : P b.1 = P c.1 := by
    by_contra hne
    exact hbc ((conflict_adj_iff q P b.1 c.1).mpr ⟨hb.trans hc.symm, hne⟩)
  exact ((conflict_adj_iff q P a.1 c.1).mp hac).2 (hab'.trans hbc')

/-- The conflict graph is the union of its graphs on the fibers, which are pairwise disjoint by
`fiber_pairwise_disjoint`: a disjoint union of complete multipartite graphs. -/
theorem conflictGraph_eq_iSup_fiberGraph [Fintype Y] [DecidableEq Y] (q : X → Y) (P : X → V) :
    conflictGraph (deterministic q).prob P =
      ⨆ y, (fiberGraph q P y).map (Function.Embedding.subtype (· ∈ fiber q y)) := by
  ext x x'
  rw [SimpleGraph.iSup_adj]
  constructor
  · intro h
    refine ⟨q x, ?_⟩
    rw [SimpleGraph.map_adj]
    exact ⟨⟨x, rfl⟩, ⟨x', ((conflict_adj_iff q P x x').mp h).1.symm⟩, h, rfl, rfl⟩
  · rintro ⟨y, h⟩
    rw [SimpleGraph.map_adj] at h
    obtain ⟨u, v, huv, rfl, rfl⟩ := h
    exact huv

/-- For a nonempty input set, the identity target admits an `n`-symbol side record with a
zero-error decoder exactly if `q` admits an `n`-valued place coordinate. -/
theorem deterministic_identity_decoder_iff_place [Fintype Y] [DecidableEq Y] [Nonempty X]
    (q : X → Y) (n : ℕ) :
    (∃ side : X → Fin n, ∃ d, Decodes (deterministic q).prob (id : X → X) side d) ↔
      ∃ p : X → Fin n, Function.Injective (fun x => (q x, p x)) := by
  rw [← colorable_iff_decoder, deterministic_graph, colorable_iff_exists_fin_resolving_channel]
  rfl

/-! ## The chromatic number is the largest number of target values on one fiber -/

/-- The chromatic number of the conflict graph is the largest number of target values on one
fiber. -/
theorem deterministic_chromaticNumber_eq [Fintype X] [Fintype Y] [DecidableEq Y]
    [DecidableEq V] (q : X → Y) (P : X → V) :
    (conflictGraph (deterministic q).prob P).chromaticNumber = (fiberMultiplicity q P : ℕ∞) := by
  rw [deterministic_graph]
  exact chromaticNumber_eq_fiberMultiplicity q P

/-- The least number of side symbols that admits a zero-error decoder is the largest number of
target values on one fiber. The empty input set gives the value zero. -/
theorem deterministic_least_side_alphabet [Fintype X] [Fintype Y] [DecidableEq Y]
    [DecidableEq V] (q : X → Y) (P : X → V) :
    IsLeast {n : ℕ | ∃ side : X → Fin n, ∃ d, Decodes (deterministic q).prob P side d}
      (fiberMultiplicity q P) := by
  rcases isEmpty_or_nonempty V with hV | hV
  · haveI : IsEmpty X := ⟨fun x => hV.false (P x)⟩
    have h0 : fiberMultiplicity q P = 0 := by
      unfold fiberMultiplicity
      rw [Finset.univ_eq_empty, Finset.image_empty, Finset.sup_empty]
      rfl
    rw [h0]
    refine ⟨⟨fun x => isEmptyElim x, fun yc => Fin.elim0 yc.2, fun x => isEmptyElim x⟩, ?_⟩
    intro n _
    exact Nat.zero_le n
  · have hset : {n : ℕ | ∃ side : X → Fin n, ∃ d, Decodes (deterministic q).prob P side d} =
        {n : ℕ | fiberMultiplicity q P ≤ n} := by
      ext n
      simp only [Set.mem_setOf_eq]
      rw [← colorable_iff_decoder, deterministic_graph, colorable_iff_fiberMultiplicity_le]
    rw [hset]
    exact ⟨le_refl (fiberMultiplicity q P), fun n hn => hn⟩

/-- The largest number of states on one fiber of `q`. -/
def largestFiber [Fintype X] [DecidableEq Y] (q : X → Y) : ℕ :=
  (Finset.univ.image q).sup fun y => (Finset.univ.filter fun x => q x = y).card

/-- For the identity target the largest number of target values on one fiber is the largest
fiber. -/
theorem fiberMultiplicity_id [Fintype X] [DecidableEq X] [DecidableEq Y] (q : X → Y) :
    fiberMultiplicity q (id : X → X) = largestFiber q := by
  unfold fiberMultiplicity largestFiber fiberVerdicts
  simp only [Finset.image_id]

/-- The least number of side symbols for zero-error recovery of the state through a deterministic
reading is the largest fiber. -/
theorem deterministic_identity_least_side_alphabet [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] (q : X → Y) :
    IsLeast {n : ℕ | ∃ side : X → Fin n, ∃ d,
      Decodes (deterministic q).prob (id : X → X) side d} (largestFiber q) := by
  rw [← fiberMultiplicity_id]
  exact deterministic_least_side_alphabet q id

/-- A fiber as a set has as many states as its finite filter. -/
theorem preimage_ncard [Fintype X] [DecidableEq Y] (q : X → Y) (y : Y) :
    (q ⁻¹' {y}).ncard = (Finset.univ.filter fun x => q x = y).card := by
  have hset : q ⁻¹' {y} = ↑(Finset.univ.filter fun x => q x = y) := by
    ext x
    simp
  rw [hset, Set.ncard_coe_finset]

/-- `thm:place`(i) on a finite input set: the least size of a place coordinate is the largest
fiber. -/
theorem largestFiber_isLeast_place [Fintype X] [DecidableEq Y] (q : X → Y) :
    IsLeast {n : ℕ | ∃ p : X → Fin n, Function.Injective (fun x => (q x, p x))}
      (largestFiber q) := by
  have hiff : ∀ n, (∃ p : X → Fin n, Function.Injective (fun x => (q x, p x))) ↔
      largestFiber q ≤ n := by
    intro n
    rw [PlaceCoordinates.exists_place_coordinate_iff]
    unfold largestFiber
    rw [Finset.sup_le_iff]
    constructor
    · intro h y _
      rw [← preimage_ncard]
      exact (h y).2
    · intro h y
      refine ⟨Set.toFinite _, ?_⟩
      rw [preimage_ncard]
      by_cases hy : y ∈ Finset.univ.image q
      · exact h y hy
      · have hempty : (Finset.univ.filter fun x => q x = y) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro x _ hx
          exact hy (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩)
        rw [hempty, Finset.card_empty]
        exact Nat.zero_le n
  exact ⟨(hiff (largestFiber q)).mpr le_rfl, fun n hn => (hiff n).mp hn⟩

/--
The paragraph after `thm:stochastic-side-records`, for `P` the identity.

Proves: on a finite input set the least number of side symbols with a zero-error decoder of the
state through the deterministic reading of `q`, the chromatic number of its conflict graph, and the
least size of a place coordinate of `q` all equal the largest fiber of `q`.
Relation: graphs and decoders of finite channels. Trust: kernel-only.
-/
theorem deterministic_identity_place_bound [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] (q : X → Y) :
    IsLeast {n : ℕ | ∃ side : X → Fin n, ∃ d,
      Decodes (deterministic q).prob (id : X → X) side d} (largestFiber q) ∧
    (conflictGraph (deterministic q).prob (id : X → X)).chromaticNumber =
      (largestFiber q : ℕ∞) ∧
    IsLeast {n : ℕ | ∃ p : X → Fin n, Function.Injective (fun x => (q x, p x))}
      (largestFiber q) := by
  refine ⟨deterministic_identity_least_side_alphabet q, ?_, largestFiber_isLeast_place q⟩
  rw [deterministic_chromaticNumber_eq, fiberMultiplicity_id]

end OperatorKO7.Meta.BoundaryObserver.DeterministicConflictGraph
