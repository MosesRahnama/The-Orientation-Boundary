import Mathlib

namespace OperatorKO7.Meta.LiteratureReview

/-!
Corollary `cor:uncontrollable-partition` states that maximal stable repairs
are exactly the pairs obtained from an uncontrollable subrelation by taking
its greatest invariant subpredicate of the permitted states and retaining
all raw edges that preserve that subpredicate.

The state type is arbitrary, predicates are sets, and reachability is
Mathlib's reflexive transitive closure. The supervisory interpretation
uses full state observation and control of individual edges for safety.
-/

set_option autoImplicit false

universe u

namespace UncontrollablePartition

variable {X : Type u}

def RelSubset (E R : X → X → Prop) : Prop :=
  ∀ ⦃x y : X⦄, E x y → R x y

def Invariant (E : X → X → Prop) (D : Set X) : Prop :=
  ∀ ⦃x y : X⦄, x ∈ D → E x y → y ∈ D

def box (E : X → X → Prop) (P : Set X) : Set X :=
  {x | ∀ y, Relation.ReflTransGen E x y → y ∈ P}

def safe (R : X → X → Prop) (D : Set X) : X → X → Prop :=
  fun x y => R x y ∧ (x ∈ D → y ∈ D)

def controllable (R U : X → X → Prop) : X → X → Prop :=
  fun x y => R x y ∧ ¬ U x y

structure StableRepair (R : X → X → Prop) (P : Set X)
    (E : X → X → Prop) (D : Set X) : Prop where
  edges : RelSubset E R
  domain : D ⊆ P
  closed : Invariant E D

def MaximalRepair (R : X → X → Prop) (P : Set X)
    (E : X → X → Prop) (D : Set X) : Prop :=
  StableRepair R P E D ∧
    ∀ (F : X → X → Prop) (A : Set X),
      StableRepair R P F A → RelSubset E F → D ⊆ A →
        F = E ∧ A = D

lemma relation_eq_of_subsets {E F : X → X → Prop}
    (hEF : RelSubset E F) (hFE : RelSubset F E) : E = F := by
  funext x y
  exact propext ⟨fun h => hEF h, fun h => hFE h⟩

lemma box_subset (E : X → X → Prop) (P : Set X) :
    box E P ⊆ P := by
  intro x hx
  exact hx x Relation.ReflTransGen.refl

lemma box_invariant (E : X → X → Prop) (P : Set X) :
    Invariant E (box E P) := by
  intro x y hx hxy z hyz
  exact hx z (Relation.ReflTransGen.head hxy hyz)

lemma invariant_path {E : X → X → Prop} {D : Set X}
    (hD : Invariant E D) {x y : X}
    (hxy : Relation.ReflTransGen E x y) (hx : x ∈ D) : y ∈ D := by
  induction hxy with
  | refl => exact hx
  | tail _ hstep ih => exact hD ih hstep

lemma subset_box {E : X → X → Prop} {P D : Set X}
    (hDP : D ⊆ P) (hD : Invariant E D) : D ⊆ box E P := by
  intro x hx y hxy
  exact hDP (invariant_path hD hxy hx)

lemma box_isGreatest (E : X → X → Prop) (P : Set X) :
    IsGreatest {D : Set X | D ⊆ P ∧ Invariant E D} (box E P) := by
  constructor
  · exact ⟨box_subset E P, box_invariant E P⟩
  · intro D hD
    exact subset_box hD.1 hD.2

lemma box_antitone {E F : X → X → Prop} (P : Set X)
    (hEF : RelSubset E F) : box F P ⊆ box E P := by
  intro x hx y hxy
  exact hx y (Relation.ReflTransGen.mono (fun _ _ h => hEF h) hxy)

lemma safe_subset (R : X → X → Prop) (D : Set X) :
    RelSubset (safe R D) R := by
  intro x y hxy
  exact hxy.1

lemma safe_invariant (R : X → X → Prop) (D : Set X) :
    Invariant (safe R D) D := by
  intro x y hx hxy
  exact hxy.2 hx

lemma subset_safe {R E : X → X → Prop} {D : Set X}
    (hER : RelSubset E R) (hD : Invariant E D) :
    RelSubset E (safe R D) := by
  intro x y hxy
  exact ⟨hER hxy, fun hx => hD hx hxy⟩

lemma safe_from_inside {R : X → X → Prop} {D : Set X}
    {x y : X} (hx : x ∈ D) :
    safe R D x y ↔ R x y ∧ y ∈ D := by
  constructor
  · intro h
    exact ⟨h.1, h.2 hx⟩
  · intro h
    exact ⟨h.1, fun _ => h.2⟩

lemma safe_from_outside {R : X → X → Prop} {D : Set X}
    {x y : X} (hx : x ∉ D) : safe R D x y ↔ R x y := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, fun hxD => False.elim (hx hxD)⟩

lemma stable_safe (R : X → X → Prop) {P D : Set X}
    (hDP : D ⊆ P) : StableRepair R P (safe R D) D :=
  ⟨safe_subset R D, hDP, safe_invariant R D⟩

lemma stable_box {R E : X → X → Prop} (P : Set X)
    (hER : RelSubset E R) : StableRepair R P E (box E P) :=
  ⟨hER, box_subset E P, box_invariant E P⟩

lemma maximal_normal_form {R E : X → X → Prop} {P D : Set X}
    (h : MaximalRepair R P E D) :
    E = safe R D ∧ D = box E P := by
  have hE := h.2 (safe R D) D
    (stable_safe R h.1.domain)
    (subset_safe h.1.edges h.1.closed)
    (fun _ hx => hx)
  have hD := h.2 E (box E P)
    (stable_box P h.1.edges)
    (fun _ _ hxy => hxy)
    (subset_box h.1.domain h.1.closed)
  exact ⟨hE.1.symm, hD.2.symm⟩

lemma normal_form_maximal {R E : X → X → Prop} {P D : Set X}
    (hE : E = safe R D) (hD : D = box E P) :
    MaximalRepair R P E D := by
  have hER : RelSubset E R := by
    rw [hE]
    exact safe_subset R D
  have hDP : D ⊆ P := by
    rw [hD]
    exact box_subset E P
  have hclosed : Invariant E D := by
    rw [hE]
    exact safe_invariant R D
  constructor
  · exact ⟨hER, hDP, hclosed⟩
  · intro F A hF hEF hDA
    have hEA : Invariant E A := by
      intro x y hx hxy
      exact hF.closed hx (hEF hxy)
    have hAD : A ⊆ D := by
      rw [hD]
      exact subset_box hF.domain hEA
    have hFE : RelSubset F E := by
      intro x y hxy
      rw [hE]
      exact ⟨hF.edges hxy, fun hx => hAD (hF.closed (hDA hx) hxy)⟩
    exact ⟨relation_eq_of_subsets hFE hEF, Set.Subset.antisymm hAD hDA⟩

lemma maximal_iff_normal_form {R E : X → X → Prop} {P D : Set X} :
    MaximalRepair R P E D ↔ E = safe R D ∧ D = box E P := by
  constructor
  · exact maximal_normal_form
  · intro h
    exact normal_form_maximal h.1 h.2

lemma partition_contains_uncontrollable {R U : X → X → Prop}
    (P : Set X) (hUR : RelSubset U R) :
    RelSubset U (safe R (box U P)) :=
  subset_safe hUR (box_invariant U P)

lemma partition_box {R U : X → X → Prop}
    (P : Set X) (hUR : RelSubset U R) :
    box (safe R (box U P)) P = box U P := by
  apply Set.Subset.antisymm
  · exact box_antitone P (partition_contains_uncontrollable P hUR)
  · exact subset_box (box_subset U P) (safe_invariant R (box U P))

lemma partition_maximal {R U : X → X → Prop}
    (P : Set X) (hUR : RelSubset U R) :
    MaximalRepair R P (safe R (box U P)) (box U P) :=
  normal_form_maximal rfl (partition_box P hUR).symm

lemma maximal_self_partition {R E : X → X → Prop} {P D : Set X}
    (h : MaximalRepair R P E D) :
    RelSubset E R ∧ D = box E P ∧ E = safe R D :=
  ⟨h.1.edges, (maximal_normal_form h).2, (maximal_normal_form h).1⟩

lemma partition_edges {R U : X → X → Prop} (P : Set X)
    (hUR : RelSubset U R) (x y : X) :
    safe R (box U P) x y ↔
      U x y ∨ (controllable R U x y ∧
        (x ∈ box U P → y ∈ box U P)) := by
  classical
  constructor
  · intro h
    by_cases hU : U x y
    · exact Or.inl hU
    · exact Or.inr ⟨⟨h.1, hU⟩, h.2⟩
  · intro h
    rcases h with hU | hC
    · exact partition_contains_uncontrollable P hUR hU
    · exact ⟨hC.1.1, hC.2⟩

lemma partition_edges_from_domain {R U : X → X → Prop}
    (P : Set X) (hUR : RelSubset U R)
    {x y : X} (hx : x ∈ box U P) :
    safe R (box U P) x y ↔
      U x y ∨ (controllable R U x y ∧ y ∈ box U P) := by
  constructor
  · intro h
    rcases (partition_edges P hUR x y).mp h with hU | hC
    · exact Or.inl hU
    · exact Or.inr ⟨hC.1, hC.2 hx⟩
  · intro h
    apply (partition_edges P hUR x y).mpr
    rcases h with hU | hC
    · exact Or.inl hU
    · exact Or.inr ⟨hC.1, fun _ => hC.2⟩

lemma partition_edge_greatest {R U F : X → X → Prop}
    (P : Set X) (hFR : RelSubset F R)
    (hF : Invariant F (box U P)) :
    RelSubset F (safe R (box U P)) :=
  subset_safe hFR hF

lemma partition_domain_comparison {R U F : X → X → Prop}
    {P A : Set X} (hF : StableRepair R P F A)
    (hUF : RelSubset U F) :
    A ⊆ box U P ∧
      ∀ ⦃x y : X⦄, x ∈ A → F x y → safe R (box U P) x y := by
  have hUA : Invariant U A := by
    intro x y hx hxy
    exact hF.closed hx (hUF hxy)
  have hA : A ⊆ box U P := subset_box hF.domain hUA
  constructor
  · exact hA
  · intro x y hx hxy
    exact ⟨hF.edges hxy, fun _ => hA (hF.closed hx hxy)⟩

lemma partition_path_comparison {R U F : X → X → Prop}
    {P A : Set X} (hF : StableRepair R P F A)
    (hUF : RelSubset U F) {x y : X} (hx : x ∈ A)
    (hxy : Relation.ReflTransGen F x y) :
    Relation.ReflTransGen (safe R (box U P)) x y := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath hstep ih =>
      exact Relation.ReflTransGen.tail ih
        ((partition_domain_comparison hF hUF).2
          (invariant_path hF.closed hpath hx) hstep)

lemma all_uncontrollable_edges (R : X → X → Prop) (P : Set X) :
    safe R (box R P) = R := by
  apply relation_eq_of_subsets
  · exact safe_subset R (box R P)
  · exact partition_contains_uncontrollable P (fun _ _ h => h)

lemma all_uncontrollable_maximal (R : X → X → Prop) (P : Set X) :
    MaximalRepair R P R (box R P) := by
  have h := partition_maximal (R := R) (U := R) P (fun _ _ h => h)
  rw [all_uncontrollable_edges R P] at h
  exact h

lemma box_empty (P : Set X) :
    box (fun (_ _ : X) => False) P = P := by
  apply Set.Subset.antisymm
  · exact box_subset _ P
  · apply subset_box (fun _ hx => hx)
    intro x y _ hxy
    exact False.elim hxy

lemma no_uncontrollable_edges (R : X → X → Prop) (P : Set X) :
    safe R (box (fun (_ _ : X) => False) P) = safe R P := by
  rw [box_empty P]

lemma no_uncontrollable_maximal (R : X → X → Prop) (P : Set X) :
    MaximalRepair R P (safe R P) P := by
  have hUR : RelSubset (fun (_ _ : X) => False) R := by
    intro x y hxy
    exact False.elim hxy
  have h := partition_maximal P hUR
  rw [box_empty P] at h
  exact h

end UncontrollablePartition

open UncontrollablePartition

theorem uncontrollable_partition {X : Type u}
    (R : X → X → Prop) (P : Set X)
    (E : X → X → Prop) (D : Set X) :
    MaximalRepair R P E D ↔
      ∃ U : X → X → Prop,
        RelSubset U R ∧ D = box U P ∧ E = safe R D := by
  constructor
  · intro h
    exact ⟨E, maximal_self_partition h⟩
  · rintro ⟨U, hUR, hD, hE⟩
    have h := partition_maximal P hUR
    rw [← hD] at h
    rw [← hE] at h
    exact h

end OperatorKO7.Meta.LiteratureReview
