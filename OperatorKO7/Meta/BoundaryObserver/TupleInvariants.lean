import OperatorKO7.Meta.BoundaryObserver.PairInvariants

set_option autoImplicit false

/-!
# Finite relational records under invisible relabelling

Graph: `Audit/ledgers/operational-inexpressibility/TWO-VOIDS-PROOF-GRAPH.md`, M15.
Finite tuples are classified by their pointwise records and their full equality pattern, with
no finiteness assumption on the state space or observation classes. Independent relabellings of
the tuple positions instead preserve only their pointwise records.
Relation: common and componentwise actions of the record-preserving permutation group.
Trust: kernel-only.
-/

namespace OperatorKO7.Meta.BoundaryObserver.TupleInvariants

open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

/-- A finite partial tuple matching extends to a permutation within the observation classes. -/
theorem match_finite_tuple {X Q I : Type*} (q : X → Q) (a b : I → X) (S : Finset I)
    (hq : ∀ i ∈ S, q (a i) = q (b i))
    (heq : ∀ i ∈ S, ∀ j ∈ S, a i = a j ↔ b i = b j) :
    ∃ σ ∈ licenseStabilizer q, ∀ i ∈ S, σ (a i) = b i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, Subgroup.one_mem _, fun _ h => False.elim (Finset.notMem_empty _ h)⟩
  | insert k S hk ih =>
    obtain ⟨σ, hσ, hm⟩ := ih
      (fun i hi => hq i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj => heq i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    have hc : q (σ (a k)) = q (b k) := (hσ (a k)).trans (hq k (Finset.mem_insert_self _ _))
    refine ⟨Equiv.swap (σ (a k)) (b k) * σ,
      Subgroup.mul_mem _
        (by simpa only [observerSwap] using (swap_mem_licenseStabilizer_of_eq q hc)) hσ, ?_⟩
    intro i hi
    rw [Equiv.Perm.mul_apply]
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Equiv.swap_apply_left _ _
    · by_cases hik : a i = a k
      · have hbk : b i = b k :=
          (heq i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_self _ _)).mp hik
        rw [hik, Equiv.swap_apply_left, hbk]
      · have hleft : σ (a i) ≠ σ (a k) := fun h => hik (σ.injective h)
        have hright : σ (a i) ≠ b k := by
          rw [hm i hi]
          intro h
          exact hik ((heq i (Finset.mem_insert_of_mem hi) k
            (Finset.mem_insert_self _ _)).mpr h)
        rw [Equiv.swap_apply_of_ne_of_ne hleft hright, hm i hi]

/-- The orbit of any finite tuple is determined exactly by its observed values and repeated
occurrences. This extends the manuscript's pair theorem to every finite arity. -/
theorem tuple_orbit_iff {X Q I : Type*} [Fintype I] (q : X → Q) (a b : I → X) :
    (∃ σ ∈ licenseStabilizer q, ∀ i, σ (a i) = b i) ↔
      (∀ i, q (a i) = q (b i)) ∧ (∀ i j, a i = a j ↔ b i = b j) := by
  classical
  constructor
  · rintro ⟨σ, hσ, hm⟩
    constructor
    · intro i
      rw [← hm i]
      exact (hσ (a i)).symm
    · intro i j
      rw [← hm i, ← hm j]
      exact σ.injective.eq_iff.symm
  · rintro ⟨hq, heq⟩
    obtain ⟨σ, hσ, hm⟩ := match_finite_tuple q a b Finset.univ
      (fun i _ => hq i) (fun i _ j _ => heq i j)
    exact ⟨σ, hσ, fun i => hm i (Finset.mem_univ _)⟩

/-- Functions invariant under a common invisible relabelling depend exactly on the tuple's
pointwise record and full equality pattern. -/
theorem tuple_invariant_iff {X Q I V : Type*} [Fintype I] (q : X → Q) (F : (I → X) → V) :
    (∀ σ ∈ licenseStabilizer q, ∀ a, F (σ ∘ a) = F a) ↔
      ∀ a b, (∀ i, q (a i) = q (b i)) →
        (∀ i j, a i = a j ↔ b i = b j) → F a = F b := by
  constructor
  · intro h a b hq heq
    obtain ⟨σ, hσ, hm⟩ := (tuple_orbit_iff q a b).mpr ⟨hq, heq⟩
    have he : σ ∘ a = b := funext hm
    rw [← he]
    exact (h σ hσ a).symm
  · intro h σ hσ a
    exact h (σ ∘ a) a (fun i => hσ (a i))
      (fun i j => σ.injective.eq_iff)

/-- With independently chosen invisible relabellings at the positions, only the pointwise
records remain invariant. This holds even for an infinite index type. -/
theorem independent_invariant_iff {X Q I V : Type*} (q : X → Q) (F : (I → X) → V) :
    (∀ σ : I → Equiv.Perm X, (∀ i, σ i ∈ licenseStabilizer q) →
      ∀ a, F (fun i => σ i (a i)) = F a) ↔
      ∀ a b, (∀ i, q (a i) = q (b i)) → F a = F b := by
  classical
  constructor
  · intro h a b hq
    have hm := h (fun i => Equiv.swap (a i) (b i))
      (fun i => by simpa only [observerSwap] using
        (swap_mem_licenseStabilizer_of_eq q (hq i))) a
    simpa only [Equiv.swap_apply_left] using hm.symm
  · intro h σ hσ a
    exact h (fun i => σ i (a i)) a (fun i => hσ i (a i))

/-- One common relabelling preserves equality; an independent relabelling can change it even
while keeping both pointwise records fixed. -/
theorem shared_reference_is_necessary {X Q : Type*} (q : X → Q) {x y : X}
    (hne : x ≠ y) (hq : q x = q y) :
    (∀ σ : Equiv.Perm X, σ x = σ y ↔ x = y) ∧
      ∃ σ τ : Equiv.Perm X, σ ∈ licenseStabilizer q ∧ τ ∈ licenseStabilizer q ∧
        σ x ≠ τ x := by
  classical
  refine ⟨fun σ => σ.injective.eq_iff, Equiv.swap x y, 1,
    (by simpa only [observerSwap] using (swap_mem_licenseStabilizer_of_eq q hq)),
    Subgroup.one_mem _, ?_⟩
  simpa only [Equiv.swap_apply_left, Equiv.Perm.one_apply] using hne.symm

/-- The empty tuple has one orbit regardless of the observation classes. -/
theorem empty_tuple_orbit {X Q : Type*} (q : X → Q) (a b : Fin 0 → X) :
    ∃ σ ∈ licenseStabilizer q, ∀ i, σ (a i) = b i :=
  (tuple_orbit_iff q a b).mpr ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

end OperatorKO7.Meta.BoundaryObserver.TupleInvariants
