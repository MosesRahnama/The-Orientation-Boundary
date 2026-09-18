import OperatorKO7.Meta.UniqueNormalization.Section7SupportSaturation

/-!
# Section 7 diagonal support kernel

This module specializes the finite support saturation of `Section7SupportSaturation`
to the diagonal seed.  The resulting carrier relation is independently sound for
`DownOn`, contains every carrier reflexivity and root step, is symmetric, and is
closed under carrier contexts and root peeling.

The final `DownOn` inclusion is reduced to one explicit clause: absorption of the
destructor-prefix (`barComp`) generator.  No theorem in this file assumes or
asserts that this remaining clause follows from non-omega-overlap.

Relation: `DownOn A R` and the diagonal support kernel on `A`.
Closure: finite support saturation, context closure, root peeling.
Strategy: full rewriting.
Trust: kernel checked; no external certificate or new axiom.
Scope: arbitrary signatures, variables, rewrite systems, and finite list carriers.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

open scoped Classical in
/-- The diagonal seed on one finite carrier. -/
noncomputable def PGraph.diagonalSupportSeed
    (A : List (Term (sigma ⊕ sigma) nu)) :
    Finset (PGraph.ResidualPair sigma nu) :=
  PGraph.supportPairSet A (fun x y => x = y)

/-- Exact membership in the diagonal seed. -/
theorem PGraph.mem_diagonalSupportSeed_iff
    {A : List (Term (sigma ⊕ sigma) nu)}
    {q : PGraph.ResidualPair sigma nu} :
    q ∈ PGraph.diagonalSupportSeed A ↔
      q.1 ∈ A ∧ q.2 ∈ A ∧ q.1 = q.2 := by
  exact PGraph.mem_supportPairSet_iff

/-- The diagonal seed lies in the carrier square. -/
theorem PGraph.diagonalSupportSeed_subset_pairUniverse
    (A : List (Term (sigma ⊕ sigma) nu)) :
    PGraph.diagonalSupportSeed A ⊆ PGraph.residualPairUniverse A :=
  PGraph.supportPairSet_subset_pairUniverse A (fun x y => x = y)

/-- Every initial support pair remains in the stabilized support. -/
theorem PGraph.supportClosure_seed
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {S : Finset (PGraph.ResidualPair sigma nu)} {q : PGraph.ResidualPair sigma nu}
    (hq : q ∈ S) : q ∈ PGraph.supportClosure A R S := by
  have hmono := PGraph.supportIter_mono A R S
    (m := 0) (n := (PGraph.residualPairUniverse A).card) (Nat.zero_le _)
  exact hmono (by simpa [PGraph.supportIter] using hq)

/-- A symmetric finite seed stays symmetric after one support round. -/
theorem PGraph.pairSetRel_supportSuccSet_symm
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {S : Finset (PGraph.ResidualPair sigma nu)}
    (hS : ∀ {x y}, PGraph.pairSetRel S x y → PGraph.pairSetRel S y x)
    {x y : Term (sigma ⊕ sigma) nu}
    (hxy : PGraph.pairSetRel (PGraph.supportSuccSet A R S) x y) :
    PGraph.pairSetRel (PGraph.supportSuccSet A R S) y x := by
  classical
  rcases PGraph.mem_supportSuccSet_iff.mp hxy with hold | ⟨hmem, hctx⟩
  · exact PGraph.mem_supportSuccSet_iff.mpr (Or.inl (hS hold))
  · have hm := PGraph.mem_residualPairUniverse_iff.mp hmem
    have hmem' : (y, x) ∈ PGraph.residualPairUniverse A :=
      PGraph.mem_residualPairUniverse_iff.mpr ⟨hm.2, hm.1⟩
    have hrootSymm : ∀ a b,
        RootPeeledSeed A R (PGraph.pairSetRel S) a b →
          RootPeeledSeed A R (PGraph.pairSetRel S) b a := by
      intro a b hab
      exact RootPeeledSeed.symm (fun _ _ hs => hS hs) hab
    exact PGraph.mem_supportSuccSet_iff.mpr
      (Or.inr ⟨hmem', CT.symm hrootSymm hctx⟩)

/-- A symmetric finite seed remains symmetric at every support stage. -/
theorem PGraph.pairSetRel_supportIter_symm
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {S : Finset (PGraph.ResidualPair sigma nu)}
    (hS : ∀ {x y}, PGraph.pairSetRel S x y → PGraph.pairSetRel S y x) :
    ∀ n {x y},
      PGraph.pairSetRel (PGraph.supportIter A R S n) x y →
        PGraph.pairSetRel (PGraph.supportIter A R S n) y x := by
  intro n
  induction n with
  | zero =>
      intro x y hxy
      exact hS hxy
  | succ n ih =>
      intro x y hxy
      change PGraph.pairSetRel
        (PGraph.supportSuccSet A R (PGraph.supportIter A R S n)) y x
      apply PGraph.pairSetRel_supportSuccSet_symm
        (S := PGraph.supportIter A R S n) (fun h => ih h)
      simpa [PGraph.supportIter] using hxy

open scoped Classical in
/-- The stabilized support generated from carrier reflexivity alone. -/
noncomputable def PGraph.section7SupportKernel
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu) :
    CRel sigma nu :=
  PGraph.pairSetRel (PGraph.supportClosure A R (PGraph.diagonalSupportSeed A))

/-- Every kernel endpoint belongs to the carrier. -/
theorem PGraph.section7SupportKernel_mem
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {x y : Term (sigma ⊕ sigma) nu}
    (hxy : PGraph.section7SupportKernel A R x y) : x ∈ A ∧ y ∈ A := by
  have hu := PGraph.supportClosure_subset_pairUniverse
    (R := R) (PGraph.diagonalSupportSeed_subset_pairUniverse A) hxy
  exact PGraph.mem_residualPairUniverse_iff.mp hu

/-- The diagonal support kernel is independently sound for `DownOn`. -/
theorem PGraph.section7SupportKernel_sound
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu}
    {x y : Term (sigma ⊕ sigma) nu}
    (hxy : PGraph.section7SupportKernel A R x y) : DownOn A R x y := by
  apply PGraph.supportClosure_sound hA
    (S := PGraph.diagonalSupportSeed A) ?_ hxy
  intro a b hab
  have hm := PGraph.mem_diagonalSupportSeed_iff.mp hab
  have habEq : a = b := by simpa using hm.2.2
  subst b
  exact DownOn.refl (by simpa using hm.1)

/-- Every carrier member is related to itself by the kernel. -/
theorem PGraph.section7SupportKernel_refl
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {x : Term (sigma ⊕ sigma) nu} (hx : x ∈ A) :
    PGraph.section7SupportKernel A R x x := by
  apply PGraph.supportClosure_seed
  exact PGraph.mem_diagonalSupportSeed_iff.mpr ⟨hx, hx, rfl⟩

/-- The diagonal support kernel is symmetric. -/
theorem PGraph.section7SupportKernel_symm
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {x y : Term (sigma ⊕ sigma) nu}
    (hxy : PGraph.section7SupportKernel A R x y) :
    PGraph.section7SupportKernel A R y x := by
  apply PGraph.pairSetRel_supportIter_symm
    (S := PGraph.diagonalSupportSeed A)
    (n := (PGraph.residualPairUniverse A).card) ?_ hxy
  intro a b hab
  have hm := PGraph.mem_diagonalSupportSeed_iff.mp hab
  exact PGraph.mem_diagonalSupportSeed_iff.mpr ⟨hm.2.1, hm.1, hm.2.2.symm⟩

/-- Carrier context closure of the kernel is exactly the kernel. -/
theorem PGraph.section7SupportKernel_context_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {x y : Term (sigma ⊕ sigma) nu} (hx : x ∈ A) (hy : y ∈ A) :
    CT (PGraph.section7SupportKernel A R) x y ↔
      PGraph.section7SupportKernel A R x y := by
  exact PGraph.context_supportClosure_iff
    (hS := PGraph.diagonalSupportSeed_subset_pairUniverse A) hx hy

/-- Root peeling of the kernel is exactly the kernel. -/
theorem PGraph.section7SupportKernel_rootPeeled_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {x y : Term (sigma ⊕ sigma) nu} :
    RootPeeledSeed A R (PGraph.section7SupportKernel A R) x y ↔
      PGraph.section7SupportKernel A R x y := by
  exact PGraph.rootPeeled_supportClosure_iff
    (hS := PGraph.diagonalSupportSeed_subset_pairUniverse A)

/-- Every carrier root rewrite is contained in the kernel. -/
theorem PGraph.section7SupportKernel_of_rootStep
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {x y : Term (sigma ⊕ sigma) nu} (hx : x ∈ A) (hy : y ∈ A)
    (hroot : rootStep R x y) : PGraph.section7SupportKernel A R x y := by
  have hyy : RootPeeledSeed A R (PGraph.section7SupportKernel A R) y y :=
    RootPeeledSeed.of_context hy hy (CT.base (PGraph.section7SupportKernel_refl hy))
  exact PGraph.section7SupportKernel_rootPeeled_iff.mp
    (RootPeeledSeed.root_left hx hroot hyy)

/-- The kernel absorbs a root rewrite on the left. -/
theorem PGraph.section7SupportKernel_rootComp
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {x y z : Term (sigma ⊕ sigma) nu} (hx : x ∈ A)
    (hroot : rootStep R x y)
    (hyz : PGraph.section7SupportKernel A R y z) :
    PGraph.section7SupportKernel A R x z := by
  have hm := PGraph.section7SupportKernel_mem hyz
  have hyzRoot : RootPeeledSeed A R (PGraph.section7SupportKernel A R) y z :=
    RootPeeledSeed.of_context hm.1 hm.2 (CT.base hyz)
  exact PGraph.section7SupportKernel_rootPeeled_iff.mp
    (RootPeeledSeed.root_left hx hroot hyzRoot)

/-- Any one same-symbol context step over kernel arguments is in the kernel. -/
theorem PGraph.section7SupportKernel_of_tildeAll
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {x y : Term (sigma ⊕ sigma) nu} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : tildeAll (PGraph.section7SupportKernel A R) x y) :
    PGraph.section7SupportKernel A R x y := by
  apply (PGraph.section7SupportKernel_context_iff hx hy).mp
  exact CT.sigmaClosed x y
    (tildeOn_mono (fun _ _ h => CT.base h) hxy)

/-- The only `DownStepOn` generator not already proved for the diagonal support
kernel is destructor-prefix composition. -/
def PGraph.Section7SupportKernelBarAbsorbs
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu) : Prop :=
  ∀ (d : sigma) (as cs : List (Term (sigma ⊕ sigma) nu))
      (b : Term (sigma ⊕ sigma) nu),
    Term.app (.inr d) as ∈ A →
    List.Forall₂ (PGraph.section7SupportKernel A R) as cs →
    Term.app (.inr d) cs ∈ A →
    PGraph.section7SupportKernel A R (.app (.inr d) cs) b →
    PGraph.section7SupportKernel A R (.app (.inr d) as) b

/-- If the kernel absorbs the destructor-prefix generator, every finite
`DownOn` derivation is already in the kernel. -/
theorem PGraph.downOn_le_section7SupportKernel_of_barAbsorbs
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (hbar : PGraph.Section7SupportKernelBarAbsorbs A R)
    {x y : Term (sigma ⊕ sigma) nu} (hxy : DownOn A R x y) :
    PGraph.section7SupportKernel A R x y := by
  refine DownOn.induction
    (P := PGraph.section7SupportKernel A R) ?_ hxy
  intro p q hpq
  obtain ⟨hp, hq, hbody⟩ := hpq
  rcases hbody with heq | hinv | ⟨c, hc, hroot, htail⟩ |
      ⟨d, as, cs, hpShape, hargs, hmid, htail⟩ | hhat | hdes
  · subst q
    exact PGraph.section7SupportKernel_refl hp
  · exact PGraph.section7SupportKernel_symm hinv.2
  · exact PGraph.section7SupportKernel_rootComp hp hroot htail.2
  · subst p
    exact hbar d as cs q hp
      (forall₂_mono (fun _ _ h => h.2) hargs) hmid htail.2
  · exact PGraph.section7SupportKernel_of_tildeAll hp hq
      (tildeAll_of_hatRel (tildeOn_mono (fun _ _ h => h.2) hhat))
  · exact PGraph.section7SupportKernel_of_tildeAll hp hq
      (tildeAll_of_barRel (tildeOn_mono (fun _ _ h => h.2) hdes))

/-- Under destructor-prefix absorption, the diagonal support kernel is exactly
`DownOn` on the finite carrier. -/
theorem PGraph.section7SupportKernel_iff_downOn_of_barAbsorbs
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu}
    (hbar : PGraph.Section7SupportKernelBarAbsorbs A R)
    {x y : Term (sigma ⊕ sigma) nu} :
    PGraph.section7SupportKernel A R x y ↔ DownOn A R x y := by
  constructor
  · exact PGraph.section7SupportKernel_sound hA
  · exact PGraph.downOn_le_section7SupportKernel_of_barAbsorbs hbar

end OperatorKO7.Meta.UniqueNormalization
