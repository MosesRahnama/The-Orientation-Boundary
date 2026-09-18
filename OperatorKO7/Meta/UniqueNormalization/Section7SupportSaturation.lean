import OperatorKO7.Meta.UniqueNormalization.Section7SimultaneousClosure

/-!
# RTA 79 Section 7 staged support saturation

This module mechanizes roadmap steps M10 and M11. Starting from a finite seed
relation on one subterm-closed carrier, each round adds the carrier-restricted
context closure of root-peeled support from the previous round. The construction
stabilizes inside the finite square `A × A` and stays sound for `DownOn` whenever
the initial seed is independently sound.

At the stabilized relation `S*`, root peeling adds no new pair, and context
closure adds no new pair between carrier members. The specialization to
`ResidualBatchSeed` uses its existing independent `DownOn` soundness.

This file does not prove M12, construct the repaired parent graph, prove
transitivity of `DownOn`, or prove the full Klop theorem.

Relation: `DownOn A R` and finite pair relations on `A`.
Closure: `CT` and `RootPeeledSeed` only, with no transitivity constructor.
Strategy: full rewriting.
Trust: kernel checked; no external certificate or new axiom.
Scope: arbitrary signatures and variable types; finite list carrier `A`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

open scoped Classical in
/-- A finite pair set interpreted as a relation on translated terms. -/
noncomputable def PGraph.pairSetRel
    (S : Finset (PGraph.ResidualPair sigma nu)) : CRel sigma nu :=
  fun x y => (x, y) ∈ S

open scoped Classical in
/-- Restrict an arbitrary relation to the finite carrier square. -/
noncomputable def PGraph.supportPairSet
    (A : List (Term (sigma ⊕ sigma) nu)) (E : CRel sigma nu) :
    Finset (PGraph.ResidualPair sigma nu) :=
  (PGraph.residualPairUniverse A).filter (fun q => E q.1 q.2)

/-- Membership in the finite restriction records both carrier endpoints and the
original relation. -/
theorem PGraph.mem_supportPairSet_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {E : CRel sigma nu}
    {q : PGraph.ResidualPair sigma nu} :
    q ∈ PGraph.supportPairSet A E ↔ q.1 ∈ A ∧ q.2 ∈ A ∧ E q.1 q.2 := by
  classical
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqA, hE⟩
    rcases PGraph.mem_residualPairUniverse_iff.mp hqA with ⟨hq₁, hq₂⟩
    exact ⟨hq₁, hq₂, hE⟩
  · rintro ⟨hq₁, hq₂, hE⟩
    exact Finset.mem_filter.mpr
      ⟨PGraph.mem_residualPairUniverse_iff.mpr ⟨hq₁, hq₂⟩, hE⟩

/-- The finite restriction is contained in the carrier square. -/
theorem PGraph.supportPairSet_subset_pairUniverse
    (A : List (Term (sigma ⊕ sigma) nu)) (E : CRel sigma nu) :
    PGraph.supportPairSet A E ⊆ PGraph.residualPairUniverse A := by
  classical
  intro q hq
  exact (Finset.mem_filter.mp hq).1

open scoped Classical in
/-- One M10 support round. It keeps the previous finite relation and adds every
carrier pair in the context closure of its root-peeled support. -/
noncomputable def PGraph.supportSuccSet
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (S : Finset (PGraph.ResidualPair sigma nu)) :
    Finset (PGraph.ResidualPair sigma nu) :=
  S ∪ (PGraph.residualPairUniverse A).filter
    (fun q => CT (RootPeeledSeed A R (PGraph.pairSetRel S)) q.1 q.2)

/-- Exact membership in one M10 support round. -/
theorem PGraph.mem_supportSuccSet_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {S : Finset (PGraph.ResidualPair sigma nu)}
    {q : PGraph.ResidualPair sigma nu} :
    q ∈ PGraph.supportSuccSet A R S ↔
      q ∈ S ∨ q ∈ PGraph.residualPairUniverse A ∧
        CT (RootPeeledSeed A R (PGraph.pairSetRel S)) q.1 q.2 := by
  classical
  simp only [PGraph.supportSuccSet, Finset.mem_union, Finset.mem_filter]

open scoped Classical in
/-- Iterated M10 support expansion. -/
noncomputable def PGraph.supportIter
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (S : Finset (PGraph.ResidualPair sigma nu)) :
    Nat → Finset (PGraph.ResidualPair sigma nu)
  | 0 => S
  | n + 1 => PGraph.supportSuccSet A R (PGraph.supportIter A R S n)

/-- Every support stage is contained in the next one. -/
theorem PGraph.supportIter_mono_succ
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (S : Finset (PGraph.ResidualPair sigma nu)) (n : Nat) :
    PGraph.supportIter A R S n ⊆ PGraph.supportIter A R S (n + 1) := by
  intro q hq
  exact PGraph.mem_supportSuccSet_iff.mpr (Or.inl hq)

/-- Support expansion is monotone in the number of rounds. -/
theorem PGraph.supportIter_mono
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (S : Finset (PGraph.ResidualPair sigma nu)) {m n : Nat}
    (hmn : m ≤ n) :
    PGraph.supportIter A R S m ⊆ PGraph.supportIter A R S n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => exact fun _ h => h
  | succ k ih =>
      intro q hq
      apply PGraph.supportIter_mono_succ A R S (m + k)
      exact ih (by omega) hq

/-- If the initial relation lies in `A × A`, every support stage does. -/
theorem PGraph.supportIter_subset_pairUniverse
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {S : Finset (PGraph.ResidualPair sigma nu)}
    (hS : S ⊆ PGraph.residualPairUniverse A) :
    ∀ n, PGraph.supportIter A R S n ⊆ PGraph.residualPairUniverse A := by
  intro n
  induction n with
  | zero => exact hS
  | succ n ih =>
      intro q hq
      rcases PGraph.mem_supportSuccSet_iff.mp hq with hq | ⟨hqA, _⟩
      · exact ih hq
      · exact hqA

/-- Every M10 stage is independently sound when the initial seed is sound.
The proof uses `RootPeeledSeed.context_sound`, never transitivity of `DownOn`. -/
theorem PGraph.supportIter_sound
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu}
    {S : Finset (PGraph.ResidualPair sigma nu)}
    (hS : ∀ {x y}, PGraph.pairSetRel S x y → DownOn A R x y) :
    ∀ n {x y}, PGraph.pairSetRel (PGraph.supportIter A R S n) x y →
      DownOn A R x y := by
  intro n
  induction n with
  | zero =>
      intro x y hxy
      exact hS hxy
  | succ n ih =>
      intro x y hxy
      rcases PGraph.mem_supportSuccSet_iff.mp hxy with hxy | ⟨hmem, hct⟩
      · exact ih hxy
      · have hm := PGraph.mem_residualPairUniverse_iff.mp hmem
        exact RootPeeledSeed.context_sound hA (fun h => ih h) hm.1 hm.2 hct

/-- Once one support round is stable, every later support round is stable. -/
theorem PGraph.supportIter_eq_succ_of_eq_succ_at
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {S : Finset (PGraph.ResidualPair sigma nu)} {n k : Nat}
    (h : PGraph.supportIter A R S n = PGraph.supportIter A R S (n + 1)) :
    PGraph.supportIter A R S (n + k) =
      PGraph.supportIter A R S (n + k + 1) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have hs := congrArg (PGraph.supportSuccSet A R) ih
      simpa [Nat.add_assoc, PGraph.supportIter] using hs

/-- Stability at one round propagates to every later specified round. -/
theorem PGraph.supportIter_eq_succ_of_eq_succ_of_le
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {S : Finset (PGraph.ResidualPair sigma nu)} {m n : Nat}
    (h : PGraph.supportIter A R S m = PGraph.supportIter A R S (m + 1))
    (hmn : m ≤ n) :
    PGraph.supportIter A R S n = PGraph.supportIter A R S (n + 1) := by
  have hk : n = m + (n - m) := by omega
  rw [hk]
  simpa using PGraph.supportIter_eq_succ_of_eq_succ_at
    (A := A) (R := R) (S := S) (n := m) (k := n - m) h

/-- If every earlier support round grows strictly, round `n` has gained at least
`n` pairs over the initial seed. -/
theorem PGraph.card_supportIter_ge_of_strict_prefix
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (S : Finset (PGraph.ResidualPair sigma nu)) :
    ∀ n,
      (∀ m, m < n → PGraph.supportIter A R S m ⊂
        PGraph.supportIter A R S (m + 1)) →
      S.card + n ≤ (PGraph.supportIter A R S n).card
  | 0, _ => by simp [PGraph.supportIter]
  | n + 1, hstrict => by
      have hprefix : ∀ m, m < n → PGraph.supportIter A R S m ⊂
          PGraph.supportIter A R S (m + 1) := by
        intro m hm
        exact hstrict m (lt_trans hm (Nat.lt_succ_self n))
      have ih := PGraph.card_supportIter_ge_of_strict_prefix A R S n hprefix
      have hcard : (PGraph.supportIter A R S n).card <
          (PGraph.supportIter A R S (n + 1)).card :=
        Finset.card_lt_card (hstrict n (Nat.lt_succ_self n))
      omega

/-- M10 stabilizes by the cardinality of the finite carrier square. -/
theorem PGraph.supportIter_stabilizes_at_pairUniverse_card
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {S : Finset (PGraph.ResidualPair sigma nu)}
    (hS : S ⊆ PGraph.residualPairUniverse A) :
    PGraph.supportIter A R S (PGraph.residualPairUniverse A).card =
      PGraph.supportIter A R S ((PGraph.residualPairUniverse A).card + 1) := by
  classical
  by_contra hne
  have hstrict : ∀ m, m < (PGraph.residualPairUniverse A).card + 1 →
      PGraph.supportIter A R S m ⊂ PGraph.supportIter A R S (m + 1) := by
    intro m hm
    have hsub := PGraph.supportIter_mono_succ A R S m
    refine ⟨hsub, ?_⟩
    intro hback
    have heq := Finset.Subset.antisymm hsub hback
    exact hne (PGraph.supportIter_eq_succ_of_eq_succ_of_le
      (A := A) (R := R) (S := S) heq (by omega))
  have hlower := PGraph.card_supportIter_ge_of_strict_prefix A R S
    ((PGraph.residualPairUniverse A).card + 1) hstrict
  have hupper :
      (PGraph.supportIter A R S ((PGraph.residualPairUniverse A).card + 1)).card ≤
        (PGraph.residualPairUniverse A).card :=
    Finset.card_le_card (PGraph.supportIter_subset_pairUniverse hS _)
  omega

open scoped Classical in
/-- The stabilized M10 relation `S*`. -/
noncomputable def PGraph.supportClosure
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (S : Finset (PGraph.ResidualPair sigma nu)) :
    Finset (PGraph.ResidualPair sigma nu) :=
  PGraph.supportIter A R S (PGraph.residualPairUniverse A).card

/-- The stabilized support is a fixed point of one M10 round. -/
theorem PGraph.supportSuccSet_supportClosure
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {S : Finset (PGraph.ResidualPair sigma nu)}
    (hS : S ⊆ PGraph.residualPairUniverse A) :
    PGraph.supportSuccSet A R (PGraph.supportClosure A R S) =
      PGraph.supportClosure A R S := by
  classical
  have h := PGraph.supportIter_stabilizes_at_pairUniverse_card
    (A := A) (R := R) (S := S) hS
  simpa [PGraph.supportClosure, PGraph.supportIter] using h.symm

/-- The stabilized support remains inside the finite carrier square. -/
theorem PGraph.supportClosure_subset_pairUniverse
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {S : Finset (PGraph.ResidualPair sigma nu)}
    (hS : S ⊆ PGraph.residualPairUniverse A) :
    PGraph.supportClosure A R S ⊆ PGraph.residualPairUniverse A := by
  exact PGraph.supportIter_subset_pairUniverse hS _

/-- Every pair in the stabilized support is independently sound. -/
theorem PGraph.supportClosure_sound
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu}
    {S : Finset (PGraph.ResidualPair sigma nu)}
    (hS : ∀ {x y}, PGraph.pairSetRel S x y → DownOn A R x y)
    {x y : Term (sigma ⊕ sigma) nu}
    (hxy : PGraph.pairSetRel (PGraph.supportClosure A R S) x y) :
    DownOn A R x y :=
  PGraph.supportIter_sound hA hS _ hxy

/-- M11, root-peeled fixed point. At stabilization, root peeling creates no new
pair. -/
theorem PGraph.rootPeeled_supportClosure_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {S : Finset (PGraph.ResidualPair sigma nu)}
    (hS : S ⊆ PGraph.residualPairUniverse A)
    {x y : Term (sigma ⊕ sigma) nu} :
    RootPeeledSeed A R (PGraph.pairSetRel (PGraph.supportClosure A R S)) x y ↔
      PGraph.pairSetRel (PGraph.supportClosure A R S) x y := by
  classical
  constructor
  · intro hxy
    have hm := RootPeeledSeed.mem hxy
    have hu : (x, y) ∈ PGraph.residualPairUniverse A :=
      PGraph.mem_residualPairUniverse_iff.mpr hm
    have hnext : (x, y) ∈
        PGraph.supportSuccSet A R (PGraph.supportClosure A R S) :=
      PGraph.mem_supportSuccSet_iff.mpr (Or.inr ⟨hu, CT.base hxy⟩)
    rw [PGraph.supportSuccSet_supportClosure hS] at hnext
    exact hnext
  · intro hxy
    have hu := PGraph.supportClosure_subset_pairUniverse hS hxy
    have hm := PGraph.mem_residualPairUniverse_iff.mp hu
    exact RootPeeledSeed.of_context hm.1 hm.2 (CT.base hxy)

/-- M11, carrier context fixed point. Context closure of `S*` adds no new pair
between members of the finite carrier. -/
theorem PGraph.context_supportClosure_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {S : Finset (PGraph.ResidualPair sigma nu)}
    (hS : S ⊆ PGraph.residualPairUniverse A)
    {x y : Term (sigma ⊕ sigma) nu} (hx : x ∈ A) (hy : y ∈ A) :
    CT (PGraph.pairSetRel (PGraph.supportClosure A R S)) x y ↔
      PGraph.pairSetRel (PGraph.supportClosure A R S) x y := by
  classical
  constructor
  · intro hxy
    have hroot : CT
        (RootPeeledSeed A R (PGraph.pairSetRel (PGraph.supportClosure A R S)))
        x y :=
      CT.mono (fun _ _ h => (PGraph.rootPeeled_supportClosure_iff hS).mpr h) hxy
    have hu : (x, y) ∈ PGraph.residualPairUniverse A :=
      PGraph.mem_residualPairUniverse_iff.mpr ⟨hx, hy⟩
    have hnext : (x, y) ∈
        PGraph.supportSuccSet A R (PGraph.supportClosure A R S) :=
      PGraph.mem_supportSuccSet_iff.mpr (Or.inr ⟨hu, hroot⟩)
    rw [PGraph.supportSuccSet_supportClosure hS] at hnext
    exact hnext
  · intro hxy
    exact CT.base hxy

open scoped Classical in
/-- The finite M10 seed specialized to an independently sound residual batch. -/
noncomputable def PGraph.residualSupportSeedSet
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (O : Finset (PGraph.ResidualPair sigma nu)) :
    Finset (PGraph.ResidualPair sigma nu) :=
  PGraph.supportPairSet A (rho.ResidualBatchSeed O)

/-- The specialized finite seed is exactly `ResidualBatchSeed` on its actual
batch endpoints. -/
theorem PGraph.mem_residualSupportSeedSet_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu}
    {O : Finset (PGraph.ResidualPair sigma nu)}
    (hO : rho.ResidualBatchSpec p O) {q : PGraph.ResidualPair sigma nu} :
    q ∈ rho.residualSupportSeedSet O ↔ rho.ResidualBatchSeed O q.1 q.2 := by
  classical
  constructor
  · intro hq
    exact (PGraph.mem_supportPairSet_iff.mp hq).2.2
  · intro hq
    have hm := hO.residualBatchSeed_mem hq
    exact PGraph.mem_supportPairSet_iff.mpr ⟨hm.1, hm.2, hq⟩

open scoped Classical in
/-- The M10-M11 closure specialized to one residual batch. -/
noncomputable def PGraph.residualSupportClosure
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (O : Finset (PGraph.ResidualPair sigma nu)) :
    Finset (PGraph.ResidualPair sigma nu) :=
  PGraph.supportClosure A R (rho.residualSupportSeedSet O)

/-- The residual-batch M10 closure is independently sound for the original
`DownOn` relation. -/
theorem PGraph.ResidualBatchSpec.residualSupportClosure_sound
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu}
    {O : Finset (PGraph.ResidualPair sigma nu)}
    (hO : rho.ResidualBatchSpec p O)
    {x y : Term (sigma ⊕ sigma) nu}
    (hxy : PGraph.pairSetRel (rho.residualSupportClosure O) x y) :
    DownOn A R x y := by
  apply PGraph.supportClosure_sound hA
    (S := rho.residualSupportSeedSet O) ?_ hxy
  intro a b hab
  exact hO.residualBatchSeed_sound hA
    ((PGraph.mem_residualSupportSeedSet_iff hO).mp hab)

/-- M11 for a residual-support closure. Root peeling of the stabilized support
is exactly the stabilized support relation. No residual-batch specification is
needed for this fixed-point law; the specification is needed separately for
semantic soundness. -/
theorem PGraph.rootPeeled_residualSupportClosure_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {O : Finset (PGraph.ResidualPair sigma nu)}
    {x y : Term (sigma ⊕ sigma) nu} :
    RootPeeledSeed A R (PGraph.pairSetRel (rho.residualSupportClosure O)) x y ↔
      PGraph.pairSetRel (rho.residualSupportClosure O) x y := by
  apply PGraph.rootPeeled_supportClosure_iff
  exact PGraph.supportPairSet_subset_pairUniverse A (rho.ResidualBatchSeed O)

/-- M11 for a residual-support closure. `CT(S*) = S*` on actual carrier
endpoints. No residual-batch specification is needed for this fixed-point law. -/
theorem PGraph.context_residualSupportClosure_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {O : Finset (PGraph.ResidualPair sigma nu)}
    {x y : Term (sigma ⊕ sigma) nu} (hx : x ∈ A) (hy : y ∈ A) :
    CT (PGraph.pairSetRel (rho.residualSupportClosure O)) x y ↔
      PGraph.pairSetRel (rho.residualSupportClosure O) x y := by
  apply PGraph.context_supportClosure_iff
    (hS := PGraph.supportPairSet_subset_pairUniverse A (rho.ResidualBatchSeed O))
    hx hy

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.PGraph.pairSetRel
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportPairSet
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.mem_supportPairSet_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportPairSet_subset_pairUniverse
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportSuccSet
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.mem_supportSuccSet_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_mono_succ
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_mono
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_subset_pairUniverse
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_sound
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_eq_succ_of_eq_succ_at
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_eq_succ_of_eq_succ_of_le
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.card_supportIter_ge_of_strict_prefix
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_stabilizes_at_pairUniverse_card
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportClosure
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportSuccSet_supportClosure
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportClosure_subset_pairUniverse
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportClosure_sound
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.rootPeeled_supportClosure_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.context_supportClosure_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.residualSupportSeedSet
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.mem_residualSupportSeedSet_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.residualSupportClosure
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.ResidualBatchSpec.residualSupportClosure_sound
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.rootPeeled_residualSupportClosure_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.context_residualSupportClosure_iff

#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.pairSetRel
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportPairSet
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.mem_supportPairSet_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportPairSet_subset_pairUniverse
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportSuccSet
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.mem_supportSuccSet_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_mono_succ
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_subset_pairUniverse
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_sound
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_eq_succ_of_eq_succ_at
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_eq_succ_of_eq_succ_of_le
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.card_supportIter_ge_of_strict_prefix
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_stabilizes_at_pairUniverse_card
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportClosure
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportSuccSet_supportClosure
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportClosure_subset_pairUniverse
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportClosure_sound
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.rootPeeled_supportClosure_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.context_supportClosure_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.residualSupportSeedSet
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.mem_residualSupportSeedSet_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.residualSupportClosure
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.ResidualBatchSpec.residualSupportClosure_sound
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.rootPeeled_residualSupportClosure_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.context_residualSupportClosure_iff
