import OperatorKO7.QEC.Operators.Basic
import OperatorKO7.QEC.Operators.TensorPower
import OperatorKO7.QEC.Operators.Projector
import OperatorKO7.QEC.Dicke.Basis

set_option autoImplicit false

/-!
# Knill-Laflamme license and the Dicke-basis wavefunction-overlap corollary

Mechanization of manuscript labels `thm:kl-license` and
`cor:kl-wf-overlap` of `Rahnama_QEC_From_Boundary.tex`.

## Manuscript content

`thm:kl-license` (subspace-code form): for an orthogonal projector
`P_C` onto a proposed code subspace and a finite indexed family of
errors `E : I -> ErrorOperator n`, the Knill--Laflamme license holds
iff there exists a complex scalar family `c : I -> I -> C` with

```
  P_C · adjoint (E a) · E b · P_C  =  c a b • P_C        (for every a b : I)
```

`cor:kl-wf-overlap` (wavefunction-overlap form): under the KL license,
for any state vector `psi : QubitRegister n` and any pair `(a, b)`,
the bracketed matrix element factors through the projector:

```
  ⟨psi, P_C · adjoint (E a) · E b · P_C · psi⟩
    = c a b * ⟨psi, P_C · psi⟩
```

When `psi = dickeState n w` with `w ∈ S` and `P_C = codeSubspaceProjector n S`,
the projector eats the Dicke state (`P_C |D_w⟩ = |D_w⟩`) and the
overlap identity reduces to the manuscript's Dicke-basis matrix
evaluation:

```
  ⟨D_w, adjoint (E a) · E b · D_w⟩  =  c a b
```

## Public surfaces

* `ErrorOperator n` -- alias for `Op (QubitRegister n)`; the operator
  algebra on the actual `n`-qubit Hilbert space.
* `KLOperatorChain` -- the operator `P_C · adjoint (E_a) · E_b · P_C`.
* `KLCondition P_C E c` -- structural KL predicate, packaging the
  projector hypothesis on `P_C` and the factorisation identity for
  every `(a, b)`.
* `KLCondition.factors` -- accessor: the KL factorisation identity.
* `KLCondition.isProjector` -- accessor: the projector hypothesis.
* `kl_license_smul_projector` -- pointwise application of the KL
  identity to a state: `(P_C · E_a† · E_b · P_C) psi = c_ab • (P_C psi)`.
* `kl_wf_overlap` -- the wavefunction-overlap corollary:
  `⟨psi, (P_C · E_a† · E_b · P_C) psi⟩ = c_ab * ⟨psi, P_C psi⟩` for
  any `psi : QubitRegister n`.
* `codeSubspaceProjector_dickeState_self` -- Dicke-basis evaluation
  ingredient: `codeSubspaceProjector n S |D_w⟩ = |D_w⟩` for `w ∈ S`.
* `kl_wf_overlap_dicke_diagonal` -- the manuscript-facing Dicke-basis
  matrix evaluation: under KL with `P_C = codeSubspaceProjector n S`
  and `w ∈ S`, the diagonal Dicke matrix element of `E_a† · E_b`
  equals exactly `c_ab`.
* `kl_wf_overlap_anchor` -- audit-anchor `String` for downstream
  registries.

## Audit slots

```
Relation:    finite-dim complex Hilbert space `(C^2)^⊗n` realized as
             `QubitRegister n := EuclideanSpace C (Fin n → Bool)`.
Closure:     N/A (this is a structural-operator-algebra layer).
Strategy:    N/A.
Trust:       kernel-only. Inner-product manipulations go through Mathlib's existing
             inner-product-space and orthogonal-projection layer.
Scope:       subspace-code form of the Knill-Laflamme criterion.
             The subsystem form `P_C E_a† E_b P_C = I_L ⊗ M_ab`
             is implemented in `KnillLaflammeSubsystem`. The finite
             Dicke-sum overlap form is provided below by
             `kl_wf_overlap_dicke_finite_matrix`.
```
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

/-- **Manuscript label `thm:kl-license` (subspace-code form).**

For a projector `P_C` and a finite-indexed error family
`E : I -> ErrorOperator n`, the KL license certifies that each
restricted operator product `P_C · E_a† · E_b · P_C` is a scalar
multiple of `P_C`, with proportionality scalars `c : I -> I -> C`.

The fields are:
* `isProjector` -- `P_C` is an orthogonal projector (Hermitian +
  idempotent in the sense of `Op.IsProjector`);
* `factors`    -- the KL factorisation identity holds for every
  pair `(a, b)`. -/
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

/-- **Manuscript label `cor:kl-wf-overlap` (structural overlap form).**

Under the KL license, for any state `psi : QubitRegister n` and any
pair `(a, b)`, the bracketed matrix element through the KL operator
chain factors through the code-subspace fidelity:

```
  ⟨psi, (P_C · E_a† · E_b · P_C) psi⟩  =  c_ab * ⟨psi, P_C psi⟩.
```

This is the structural overlap identity behind the manuscript's
"Dicke-basis matrix-overlap" form. The Dicke-basis evaluation
follows by combining this identity with
`codeSubspaceProjector_dickeState_self` (Dicke states inside `S`
survive `P_C` unchanged); the diagonal Dicke matrix evaluation is
`kl_wf_overlap_dicke_diagonal` below. -/
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


/-- Audit anchor for the Knill-Laflamme well-formed overlap theorem. -/
def kl_wf_overlap_anchor : String :=
  "QEC.Codes.KnillLaflamme.kl_wf_overlap"

/-- Audit anchor for the Dicke-diagonal specialization of that overlap. -/
def kl_wf_overlap_dicke_diagonal_anchor : String :=
  "QEC.Codes.KnillLaflamme.kl_wf_overlap_dicke_diagonal"

end QEC.Codes.KnillLaflamme

/-! ## Reach and axiom parity (LASOT gate Q24) -/

#check @QEC.Codes.KnillLaflamme.inner_dickeState_self_eq_one

#print axioms QEC.Codes.KnillLaflamme.ErrorOperator
#print axioms QEC.Codes.KnillLaflamme.KLOperatorChain
#print axioms QEC.Codes.KnillLaflamme.KLCondition
#print axioms QEC.Codes.KnillLaflamme.KLCondition.projector
#print axioms QEC.Codes.KnillLaflamme.KLCondition.kl_chain_eq_smul
#print axioms QEC.Codes.KnillLaflamme.inner_dickeState_self_eq_one
#print axioms QEC.Codes.KnillLaflamme.kl_wf_overlap_anchor
#print axioms QEC.Codes.KnillLaflamme.kl_wf_overlap_dicke_diagonal_anchor
