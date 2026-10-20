import OperatorKO7.QEC.Operators.Basic
import OperatorKO7.QEC.Operators.TensorPower
import OperatorKO7.QEC.Operators.Projector
import OperatorKO7.QEC.Dicke.Basis

set_option autoImplicit false

/-!
# Knill-Laflamme subspace condition and wavefunction overlap

For a projector `P_C`, an error family `E` indexed by a type `I`, and a complex scalar family `c`, `KLCondition P_C E c` states that `P_C` is an orthogonal projector and each compressed error product equals `c a b • P_C`. This module proves the corresponding inner-product identity for any vector, the diagonal Dicke identity for weights in `S`, and a finite Dicke-sum identity.

The scope is the subspace-code form; this module states no subsystem-code condition or empirical physical-noise result. Its proofs use imported Mathlib inner-product and orthogonal-projection results.
-/

namespace QEC.Codes.KnillLaflamme

open QEC.Operators QEC.Operators.Projector QEC.Dicke.Basis
open scoped ComplexConjugate

variable {n : ℕ}

/-! ## 1. Error operator alias -/

/-- An n-qubit error operator. Alias for the operator-algebra carrier
on the actual n-qubit Hilbert space `QubitRegister n`. -/
abbrev ErrorOperator (n : ℕ) : Type _ := Op (QubitRegister n)

/-- The operator chain `P_C · adjoint (E_a) · E_b · P_C` from the
KL license. Sequencing follows Mathlib's `LinearMap.comp` convention:
`(P_C · A · B · P_C) psi = P_C (A (B (P_C psi)))`. Noncomputable
because `Op.adjoint` is. -/
noncomputable def KLOperatorChain (P_C : Op (QubitRegister n))
    (E_a E_b : ErrorOperator n) : Op (QubitRegister n) :=
  Op.comp (Op.comp (Op.comp P_C (Op.adjoint E_a)) E_b) P_C

@[simp] theorem KLOperatorChain_apply (P_C : Op (QubitRegister n))
    (E_a E_b : ErrorOperator n) (ψ : QubitRegister n) :
    KLOperatorChain P_C E_a E_b ψ
      = P_C (Op.adjoint E_a (E_b (P_C ψ))) := by
  simp [KLOperatorChain, Op.comp]

/-! ## 2. Knill-Laflamme license predicate -/

/-- The predicate `KLCondition P_C E c` requires `P_C` to be an orthogonal projector and every compressed product `P_C · adjoint (E a) · E b · P_C` to equal `c a b • P_C`. -/
structure KLCondition (P_C : Op (QubitRegister n))
    {I : Type} (E : I → ErrorOperator n) (c : I → I → ℂ) : Prop where
  isProjector : Op.IsProjector P_C
  factors :
    ∀ a b : I, KLOperatorChain P_C (E a) (E b) = c a b • P_C

/-- Accessor for the projector hypothesis. -/
theorem KLCondition.projector
    {P_C : Op (QubitRegister n)} {I : Type}
    {E : I → ErrorOperator n} {c : I → I → ℂ}
    (hKL : KLCondition P_C E c) : Op.IsProjector P_C :=
  hKL.isProjector

/-- Accessor for the KL factorisation identity. -/
theorem KLCondition.kl_chain_eq_smul
    {P_C : Op (QubitRegister n)} {I : Type}
    {E : I → ErrorOperator n} {c : I → I → ℂ}
    (hKL : KLCondition P_C E c) (a b : I) :
    KLOperatorChain P_C (E a) (E b) = c a b • P_C :=
  hKL.factors a b

/-! ## 3. Pointwise application of the KL identity -/

/-- Pointwise form of the KL factorisation. Under KL,
`(P_C · E_a† · E_b · P_C) psi = c_ab • (P_C psi)`. -/
theorem kl_license_smul_projector
    {P_C : Op (QubitRegister n)} {I : Type}
    {E : I → ErrorOperator n} {c : I → I → ℂ}
    (hKL : KLCondition P_C E c) (ψ : QubitRegister n) (a b : I) :
    KLOperatorChain P_C (E a) (E b) ψ = c a b • P_C ψ := by
  rw [hKL.factors a b]
  rfl

/-! ## 4. Wavefunction-overlap corollary -/

/-- Manuscript label `cor:kl-wf-overlap`: under `KLCondition`, the inner product `⟨ψ, (P_C · E_a† · E_b · P_C) ψ⟩` equals `c_ab * ⟨ψ, P_C ψ⟩` for any vector `ψ`. This is an inner-product overlap; the statement has no normalization hypothesis. For `ψ = |D_w⟩` with `w ∈ S`, the projector fixes the Dicke state, yielding the diagonal matrix identity below. -/
theorem kl_wf_overlap
    {P_C : Op (QubitRegister n)} {I : Type}
    {E : I → ErrorOperator n} {c : I → I → ℂ}
    (hKL : KLCondition P_C E c) (ψ : QubitRegister n) (a b : I) :
    inner ℂ ψ (KLOperatorChain P_C (E a) (E b) ψ)
      = c a b * inner ℂ ψ (P_C ψ) := by
  rw [kl_license_smul_projector hKL ψ a b]
  exact inner_smul_right ψ (P_C ψ) (c a b)

/-! ## 5. Dicke-basis projector evaluation -/

/-- For a code subspace
`codeSubspace n S = span{|D_w⟩ : w ∈ S}` and `w ∈ S`, the Dicke state
lies in the code subspace. -/
theorem dickeState_mem_codeSubspace
    (S : Finset (Fin (n + 1))) {w : Fin (n + 1)} (hw : w ∈ S) :
    dickeState n w ∈ codeSubspace n S := by
  apply Submodule.subset_span
  refine ⟨w, ?_, rfl⟩
  exact hw

/-- For `w ∈ S`, the code-subspace projector fixes the Dicke state:

```
  codeSubspaceProjector n S |D_w⟩ = |D_w⟩.
```

This is the Dicke-basis matrix-evaluation ingredient: it turns the
`kl_wf_overlap` identity (formulated through `P_C psi`) into a
direct Dicke matrix element when `psi = |D_w⟩` with `w ∈ S`. -/
theorem codeSubspaceProjector_dickeState_self
    (S : Finset (Fin (n + 1))) {w : Fin (n + 1)} (hw : w ∈ S) :
    codeSubspaceProjector n S (dickeState n w) = dickeState n w := by
  have hmem : dickeState n w ∈ codeSubspace n S :=
    dickeState_mem_codeSubspace S hw
  -- codeSubspaceProjector n S is starProjection coerced to a LinearMap.
  show ((codeSubspace n S).starProjection :
          QubitRegister n →L[ℂ] QubitRegister n) (dickeState n w)
        = dickeState n w
  exact Submodule.starProjection_eq_self_iff.mpr hmem

/-- A finite Dicke linear combination over `S` lies in the code subspace
`span{|D_w⟩ : w ∈ S}`. -/
theorem dickeLinearCombo_mem_codeSubspace
    (S : Finset (Fin (n + 1))) (coeff : Fin (n + 1) → ℂ) :
    (∑ w ∈ S, coeff w • dickeState n w) ∈ codeSubspace n S := by
  classical
  exact Submodule.sum_mem _ (fun w hw =>
    Submodule.smul_mem _ (coeff w) (dickeState_mem_codeSubspace S hw))

/-- The code-subspace projector fixes every finite Dicke linear combination
supported on `S`. -/
theorem codeSubspaceProjector_dickeLinearCombo_self
    (S : Finset (Fin (n + 1))) (coeff : Fin (n + 1) → ℂ) :
    codeSubspaceProjector n S (∑ w ∈ S, coeff w • dickeState n w)
      = ∑ w ∈ S, coeff w • dickeState n w := by
  have hmem : (∑ w ∈ S, coeff w • dickeState n w) ∈ codeSubspace n S :=
    dickeLinearCombo_mem_codeSubspace S coeff
  show ((codeSubspace n S).starProjection :
          QubitRegister n →L[ℂ] QubitRegister n)
        (∑ w ∈ S, coeff w • dickeState n w)
      = ∑ w ∈ S, coeff w • dickeState n w
  exact Submodule.starProjection_eq_self_iff.mpr hmem

/-! ## 6. Dicke-basis diagonal matrix evaluation (manuscript form) -/

/-- The Dicke states are normalised: `⟨D_w, D_w⟩ = 1`. -/
private theorem inner_dickeState_self_eq_one (w : Fin (n + 1)) :
    inner ℂ (dickeState n w) (dickeState n w) = (1 : ℂ) := by
  -- The orthonormal-family API: for an orthonormal family `f`,
  -- `inner (f i) (f j) = if i = j then 1 else 0`.
  have horth : ∀ i j : Fin (n + 1),
      inner ℂ (dickeState n i) (dickeState n j) = if i = j then (1 : ℂ) else 0 :=
    orthonormal_iff_ite.mp (dickeState_orthonormal n)
  have := horth w w
  simpa using this

/-- **Manuscript label `cor:kl-wf-overlap` (diagonal Dicke evaluation).**

Under the KL license with `P_C = codeSubspaceProjector n S` and any
`w ∈ S`, the diagonal Dicke matrix element of `E_a† · E_b` evaluates
to the KL scalar:

```
  ⟨D_w, adjoint (E_a) (E_b D_w)⟩  =  c_ab.
```

Proof: apply `kl_wf_overlap` at `psi = |D_w⟩`, then use
`codeSubspaceProjector_dickeState_self` (which kills the outer
`P_C` and the inner `P_C` because `P_C |D_w⟩ = |D_w⟩` for `w ∈ S`)
and `⟨D_w, D_w⟩ = 1` (from `dickeState_orthonormal`). -/
theorem kl_wf_overlap_dicke_diagonal
    {I : Type} {E : I → ErrorOperator n} {c : I → I → ℂ}
    {S : Finset (Fin (n + 1))}
    (hKL : KLCondition (codeSubspaceProjector n S) E c)
    {w : Fin (n + 1)} (hw : w ∈ S) (a b : I) :
    inner ℂ (dickeState n w)
        (Op.adjoint (E a) (E b (dickeState n w)))
      = c a b := by
  -- Convenient abbreviations.
  set P_C := codeSubspaceProjector n S with hPC_def
  have hP : P_C (dickeState n w) = dickeState n w :=
    codeSubspaceProjector_dickeState_self S hw
  have hHerm : Op.adjoint P_C = P_C := hKL.isProjector.hermitian
  -- Wavefunction-overlap identity at psi = |D_w⟩.
  have hovr := kl_wf_overlap hKL (dickeState n w) a b
  -- Simplify the RHS of hovr: inner |D_w⟩ (P_C |D_w⟩) → 1.
  rw [hP, inner_dickeState_self_eq_one w, mul_one] at hovr
  -- hovr : inner |D_w⟩ (KLOperatorChain P_C (E a) (E b) |D_w⟩) = c a b
  -- Expand KLOperatorChain and collapse the innermost P_C application:
  rw [KLOperatorChain_apply, hP] at hovr
  -- hovr : inner |D_w⟩ (P_C (Op.adjoint (E a) (E b |D_w⟩))) = c a b
  -- Collapse the outer P_C via self-adjoint + hP:
  --   inner |D_w⟩ (P_C X) = inner (adjoint P_C |D_w⟩) X
  --                        = inner (P_C |D_w⟩) X       (Hermitian)
  --                        = inner |D_w⟩ X            (hP)
  have hcollapse :
      inner ℂ (dickeState n w)
          (P_C (Op.adjoint (E a) (E b (dickeState n w))))
        = inner ℂ (dickeState n w)
            (Op.adjoint (E a) (E b (dickeState n w))) := by
    rw [← Op.adjoint_inner_left P_C (dickeState n w)
            (Op.adjoint (E a) (E b (dickeState n w)))]
    rw [hHerm, hP]
  rw [hcollapse] at hovr
  exact hovr

/-- **Manuscript label `cor:kl-wf-overlap` (finite Dicke-sum form).**

For a Dicke-supported state
`ψ = ∑ w ∈ S, coeff w • |D_w⟩`, the KL overlap identity expands into
the finite matrix-overlap check over the Dicke basis:

```
Σ_{w∈S} Σ_{w'∈S} coeff_w^* coeff_{w'}
  ⟨D_w | E_a† E_b | D_{w'}⟩
  = c_ab · ⟨ψ | P_C ψ⟩.
```
-/
theorem kl_wf_overlap_dicke_finite_matrix
    {I : Type} {E : I → ErrorOperator n} {c : I → I → ℂ}
    {S : Finset (Fin (n + 1))}
    (hKL : KLCondition (codeSubspaceProjector n S) E c)
    (coeff : Fin (n + 1) → ℂ) (a b : I) :
    (∑ w' ∈ S, coeff w' * ∑ w ∈ S,
      star (coeff w) *
        inner ℂ (dickeState n w)
          (Op.adjoint (E a) (E b (dickeState n w'))))
      =
      c a b *
        inner ℂ (∑ w ∈ S, coeff w • dickeState n w)
          (codeSubspaceProjector n S
            (∑ w ∈ S, coeff w • dickeState n w)) := by
  classical
  set ψ : QubitRegister n := ∑ w ∈ S, coeff w • dickeState n w with hψ
  set P_C : Op (QubitRegister n) := codeSubspaceProjector n S with hPC
  have hP : P_C ψ = ψ := by
    rw [hψ, hPC]
    exact codeSubspaceProjector_dickeLinearCombo_self S coeff
  have hHerm : Op.adjoint P_C = P_C := hKL.isProjector.hermitian
  have hovr := kl_wf_overlap hKL ψ a b
  rw [KLOperatorChain_apply, hP] at hovr
  have hcollapse :
      inner ℂ ψ (P_C (Op.adjoint (E a) (E b ψ)))
        = inner ℂ ψ (Op.adjoint (E a) (E b ψ)) := by
    rw [← Op.adjoint_inner_left P_C ψ (Op.adjoint (E a) (E b ψ))]
    rw [hHerm, hP]
  rw [hcollapse] at hovr
  have hsum :
      inner ℂ ψ (Op.adjoint (E a) (E b ψ))
        =
        ∑ w' ∈ S, coeff w' * ∑ w ∈ S,
          star (coeff w) *
            inner ℂ (dickeState n w)
              (Op.adjoint (E a) (E b (dickeState n w'))) := by
    subst ψ
    simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left,
      inner_smul_right]
    simp
  rw [← hsum]
  rw [hovr]
  rw [hP]


/-- Fully qualified name of the arbitrary-vector wavefunction-overlap theorem. -/
def kl_wf_overlap_anchor : String :=
  "QEC.Codes.KnillLaflamme.kl_wf_overlap"

/-- Fully qualified name of the diagonal Dicke overlap theorem. -/
def kl_wf_overlap_dicke_diagonal_anchor : String :=
  "QEC.Codes.KnillLaflamme.kl_wf_overlap_dicke_diagonal"

end QEC.Codes.KnillLaflamme



#check @QEC.Codes.KnillLaflamme.inner_dickeState_self_eq_one

#print axioms QEC.Codes.KnillLaflamme.ErrorOperator
#print axioms QEC.Codes.KnillLaflamme.KLOperatorChain
#print axioms QEC.Codes.KnillLaflamme.KLCondition
#print axioms QEC.Codes.KnillLaflamme.KLCondition.projector
#print axioms QEC.Codes.KnillLaflamme.KLCondition.kl_chain_eq_smul
#print axioms QEC.Codes.KnillLaflamme.inner_dickeState_self_eq_one
#print axioms QEC.Codes.KnillLaflamme.kl_wf_overlap_anchor
#print axioms QEC.Codes.KnillLaflamme.kl_wf_overlap_dicke_diagonal_anchor
