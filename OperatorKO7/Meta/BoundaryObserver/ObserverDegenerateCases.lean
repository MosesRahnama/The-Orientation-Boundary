import OperatorKO7.Meta.BoundaryObserver.RecursorDecidability

set_option autoImplicit false

/-!
# Empty content carriers and invariant resolving coordinates

Graph: Audit/ledgers/boundary-theorem/BOUNDARY-THEOREM-MATH-COMPLETION-PROOF-GRAPH.md, A13.
Manuscript: thm:recursor-decidability and the paragraph following thm:place.
The equivalences include empty carriers and injective observers. Every earlier
inhabited-carrier impossibility and general termination theorem stays unchanged.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ObserverDegenerateCases

open MergedPair RecursorDecidability PlaceCoordinates
open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

/-- On an empty content carrier every target is determined. -/
theorem empty_content_determines {T V : Type*} [IsEmpty T] (f : T × ℕ → V) :
    Determines (content (T := T)) f := by
  intro x
  exact isEmptyElim x.1

/-- The content determines the zero test if and only if there is no content. -/
theorem content_determines_observed_iff_empty (T : Type*) :
    Determines (content (T := T)) (observed (T := T)) ↔ IsEmpty T := by
  constructor
  · intro h
    refine ⟨fun t => ?_⟩
    letI : Nonempty T := ⟨t⟩
    exact observed_not_content_determined h
  · intro h
    letI : IsEmpty T := h
    exact empty_content_determines observed

/-- The content determines the whole counter if and only if there is no content. -/
theorem content_determines_counter_iff_empty (T : Type*) :
    Determines (content (T := T)) (counter (T := T)) ↔ IsEmpty T := by
  constructor
  · intro h
    refine ⟨fun t => ?_⟩
    letI : Nonempty T := ⟨t⟩
    exact counter_not_content_determined h
  · intro h
    letI : IsEmpty T := h
    exact empty_content_determines counter

/-- For every orienting measure the content-determination criterion is empty T. -/
theorem orienting_content_determined_iff_empty {T : Type*}
    (M : T × ℕ → ℕ) (hM : ∀ x y, Pass x y → M y < M x) :
    Determines content M ↔ IsEmpty T := by
  constructor
  · intro h
    refine ⟨fun t => ?_⟩
    letI : Nonempty T := ⟨t⟩
    exact orienting_measure_not_content_determined M hM h
  · intro h
    letI : IsEmpty T := h
    exact empty_content_determines M

/-- A content-determined orienting measure exists precisely in the empty case. -/
theorem content_orienter_exists_iff_empty (T : Type*) :
    (∃ M : T × ℕ → ℕ,
      (∀ x y, Pass x y → M y < M x) ∧ Determines content M) ↔ IsEmpty T := by
  constructor
  · rintro ⟨M, hM, hdet⟩
    exact (orienting_content_determined_iff_empty M hM).mp hdet
  · intro h
    letI : IsEmpty T := h
    exact ⟨counter, counter_orients, empty_content_determines counter⟩

/-- The universal termination statement and both determination regimes hold together. -/
theorem counted_recursion_all_carriers (T : Type*) :
    WellFounded (fun y x : T × ℕ => Pass x y) ∧
      (Determines (content (T := T)) observed ↔ IsEmpty T) ∧
      ((∃ M : T × ℕ → ℕ,
        (∀ x y, Pass x y → M y < M x) ∧ Determines content M) ↔ IsEmpty T) :=
  ⟨pass_wellFounded, content_determines_observed_iff_empty T,
    content_orienter_exists_iff_empty T⟩

/-- Empty is the case refuting unqualified nondetermination on every carrier. -/
theorem empty_counter_control :
    Determines (content (T := Empty)) observed ∧
      (∀ x y : Empty × ℕ, Pass x y → counter y < counter x) :=
  ⟨empty_content_determines observed, counter_orients⟩

/-- A coordinate already determined by the record can complete it only if
that record was injective. The converse includes empty domains. -/
theorem resolving_determined_iff_injective {X Q S : Type*}
    (q : X → Q) (p : X → S)
    (hp : Function.Injective (fun x => (q x, p x))) :
    Determines q p ↔ Function.Injective q := by
  constructor
  · intro h x y hq
    exact hp (Prod.ext hq (h x y hq))
  · intro h x y hq
    exact congrArg p (h hq)

/-- Invariance of a resolving coordinate under all invisible permutations is
equivalent to injectivity of the original observer. -/
theorem resolving_invariant_iff_injective {X Q S : Type*}
    (q : X → Q) (p : X → S)
    (hp : Function.Injective (fun x => (q x, p x))) :
    (∀ σ ∈ licenseStabilizer q, ∀ x, p (σ x) = p x) ↔
      Function.Injective q :=
  (determines_iff_invariant q p).symm.trans (resolving_determined_iff_injective q p hp)

/-- The same classification uses the inverse action on resolving coordinates. -/
theorem resolving_fixed_iff_injective {X Q S : Type*}
    (q : X → Q) (p : X → S)
    (hp : Function.Injective (fun x => (q x, p x))) :
    (∀ σ ∈ licenseStabilizer q, p ∘ σ.symm = p) ↔ Function.Injective q := by
  constructor
  · intro h
    apply (resolving_invariant_iff_injective q p hp).mp
    intro σ hσ x
    have hz := congrFun (h σ hσ) (σ x)
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hz.symm
  · intro h σ hσ
    funext x
    have hz : q (σ.symm x) = q x := by
      have hh := hσ (σ.symm x)
      simpa only [Equiv.apply_symm_apply] using hh.symm
    exact congrArg p (h hz)

/-- A merged pair forces every resolving coordinate to move under some
invisible permutation. -/
theorem merged_pair_moves_resolving_coordinate {X Q S : Type*}
    (q : X → Q) (p : X → S)
    (hp : Function.Injective (fun x => (q x, p x)))
    {x y : X} (hpair : IsMergedPair q x y) :
    ∃ σ ∈ licenseStabilizer q, p ∘ σ.symm ≠ p := by
  classical
  by_contra h
  push_neg at h
  exact hpair.1 ((resolving_fixed_iff_injective q p hp).mp h hpair.2)

/-- A bijective-on-fibers place coordinate satisfies the same criterion. -/
theorem place_coordinate_fixed_iff_injective {X Q : Type*}
    (q : X → Q) {n : ℕ} {p : X → Fin n} (hp : p ∈ PlaceCoord q n) :
    (∀ σ ∈ licenseStabilizer q, p ∘ σ.symm = p) ↔ Function.Injective q := by
  apply resolving_fixed_iff_injective q p
  intro x y h
  have hq : q x = q y := congrArg Prod.fst h
  have hxy : p x = p y := congrArg Prod.snd h
  exact (hp (q x) ⟨x, rfl⟩).injOn rfl hq.symm hxy

/-- The identity observer has an invariant resolving coordinate, including
on a singleton. This is the injective regime of the classification. -/
theorem identity_observer_fixed_control (X : Type*) :
    ∀ σ ∈ licenseStabilizer (id : X → X), (id : X → X) ∘ σ.symm = id := by
  apply (resolving_fixed_iff_injective (id : X → X) id
    (fun _ _ h => congrArg Prod.fst h)).mpr
  exact Function.injective_id

end OperatorKO7.Meta.BoundaryObserver.ObserverDegenerateCases
