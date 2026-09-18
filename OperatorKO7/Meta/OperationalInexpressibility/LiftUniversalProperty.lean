import OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
import OperatorKO7.Meta.OperationalInexpressibility.LicenseLattice

/-!
# The universal lift and the absent universal refusal

Every observer that refines `q` and licenses `P` refines the joint observer of `q` and `P`, and
the kernel of any observer with this property is the meet of the two kernels. A greatest set on
which `q` licenses `P` exists exactly when `q` licenses `P`.

Relation: observer refinement; inclusion of retained sets.
Property: universal property of the joint observer; absence of a greatest refusal at a collision.
Trust: kernel only.
Scope: arbitrary types.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.LiftUniversalProperty

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.LicenseLattice
open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse

universe u v w z

variable {X : Type u} {Q : Type v} {V : Type w}

/-- **The lift has a universal solution.** -/
theorem jointPair_greatest_licensingRefinement (q : X → Q) (P : X → V) :
    ObserverRefines (jointPair q P) q ∧ Licensed (jointPair q P) P ∧
      ∀ {R : Type z} (r : X → R), ObserverRefines r q → Licensed r P →
        ObserverRefines r (jointPair q P) := by
  refine ⟨fun h => congrArg Prod.fst h, fun x y h => congrArg Prod.snd h, ?_⟩
  intro R r hq hP x y h
  exact Prod.ext (hq h) (hP x y h)

theorem licensingRefinement_iff_kernel_le (q : X → Q) (P : X → V) {R : Type z} (r : X → R) :
    (ObserverRefines r q ∧ Licensed r P) ↔
      observerKernel r ≤ observerKernel q ⊓ observerKernel P := by
  rw [observerRefines_iff_kernel_le, licensed_iff_kernel_le, le_inf_iff]

/-- Any observer with the universal property has the meet kernel. -/
theorem observerKernel_eq_of_universal (q : X → Q) (P : X → V) {R : Type z} (r : X → R)
    (hq : ObserverRefines r q) (hP : Licensed r P)
    (huniv : ∀ (r' : X → Q × V), ObserverRefines r' q → Licensed r' P → ObserverRefines r' r) :
    observerKernel r = observerKernel q ⊓ observerKernel P := by
  apply le_antisymm
  · exact (licensingRefinement_iff_kernel_le q P r).1 ⟨hq, hP⟩
  · have hq' : ObserverRefines (jointPair q P) q := by
      intro x y h
      exact congrArg Prod.fst h
    have hP' : Licensed (jointPair q P) P := by
      intro x y h
      exact congrArg Prod.snd h
    have h1 : ObserverRefines (jointPair q P) r := huniv (jointPair q P) hq' hP'
    rw [observerRefines_iff_kernel_le, observerKernel_jointPair] at h1
    exact h1

/-- **Refusal has a universal solution only for licensed targets.** -/
theorem exists_greatest_licensedOn_iff (q : X → Q) (P : X → V) :
    (∃ G : Set X, LicensedOn G q P ∧ ∀ S : Set X, LicensedOn S q P → S ⊆ G) ↔ Licensed q P := by
  constructor
  · rintro ⟨G, hG, hmax⟩ x y hxy
    have hxG : x ∈ G := hmax {x} (by
      intro z hz w hw _
      rw [Set.mem_singleton_iff.1 hz, Set.mem_singleton_iff.1 hw]) (Set.mem_singleton x)
    have hyG : y ∈ G := hmax {y} (by
      intro z hz w hw _
      rw [Set.mem_singleton_iff.1 hz, Set.mem_singleton_iff.1 hw]) (Set.mem_singleton y)
    exact hG x hxG y hyG hxy
  · intro h
    exact ⟨Set.univ, (licensedOn_univ_iff q P).2 h, fun S _ => Set.subset_univ S⟩

theorem no_greatest_licensedOn_of_collision {q : X → Q} {P : X → V} {x y : X}
    (h : OperationallyInexpressibleAt q P x y) :
    ¬ ∃ G : Set X, LicensedOn G q P ∧ ∀ S : Set X, LicensedOn S q P → S ⊆ G := by
  rw [exists_greatest_licensedOn_iff]
  exact fun hl => h.2 (hl x y h.1)

/-- Control: the two-void collision admits no greatest refusal. -/
theorem twoVoids_no_greatest_refusal :
    ¬ ∃ G : Set (Fin 2), LicensedOn G (fun _ : Fin 2 => ()) (fun x : Fin 2 => x) ∧
      ∀ S : Set (Fin 2), LicensedOn S (fun _ : Fin 2 => ()) (fun x : Fin 2 => x) → S ⊆ G := by
  exact no_greatest_licensedOn_of_collision (q := fun _ : Fin 2 => ())
    (P := fun x : Fin 2 => x) (x := 0) (y := 1) ⟨rfl, by decide⟩

end OperatorKO7.Meta.OperationalInexpressibility.LiftUniversalProperty
