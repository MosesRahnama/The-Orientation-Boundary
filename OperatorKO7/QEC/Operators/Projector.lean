import OperatorKO7.QEC.Operators.Basic
import OperatorKO7.QEC.Operators.TensorPower
import OperatorKO7.QEC.Dicke.Basis
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

set_option autoImplicit false

/-!
# Projector substrate: symmetric-subspace and code-subspace projectors

This module supplies the projector surface required by manuscript
labels `thm:kl-license`, `cor:kl-wf-overlap`, and
`prop:abstention-as-overlap`. The projectors are built from Mathlib's
`Submodule.subtypeL ∘L orthogonalProjection`-style construction, so
they are real orthogonal projectors on the actual `n`-qubit Hilbert
space `QubitRegister n`, not opaque markers.

## Public surfaces

* `symmetricSubspaceProjector n` -- orthogonal projector onto the
  symmetric subspace `SymmetricSpan n ⊆ QubitRegister n`.
* `codeSubspaceProjector n S` -- orthogonal projector onto the
  span of the Dicke states indexed by an arbitrary finset `S` of
  Hamming weights, i.e. `P_C = Σ_{w∈S} |D_w⟩⟨D_w|`.
* `symmetricSubspaceProjector_isProjector` -- the symmetric-subspace
  projector is an idempotent self-adjoint operator (`IsProjector`).
* `codeSubspaceProjector_isProjector` -- ditto for the code-subspace
  projector.
* `complement_norm_sq_eq` -- the abstention-rate identity
  `‖(id − P) ψ‖² = ‖ψ‖² − ‖P ψ‖²` for any orthogonal   projector.
-/

namespace QEC.Operators.Projector

open QEC.Dicke.Basis QEC.Operators
open scoped ComplexConjugate

variable {n : ℕ}

/-! ## 1. Symmetric-subspace projector -/

/-- Orthogonal projector onto the symmetric subspace `SymmetricSpan n`
of the `n`-qubit Hilbert space. Implemented via Mathlib's
`Submodule.starProjection`. -/
noncomputable def symmetricSubspaceProjector (n : ℕ) :
    Op (QubitRegister n) :=
  ((SymmetricSpan n).starProjection : QubitRegister n →L[ℂ] QubitRegister n)

/-- Pointwise idempotence of `starProjection`: applying it twice equals
applying it once. -/
private theorem starProjection_idempotent_apply
    (K : Submodule ℂ (QubitRegister n)) [K.HasOrthogonalProjection]
    (x : QubitRegister n) :
    K.starProjection (K.starProjection x) = K.starProjection x := by
  apply Submodule.starProjection_eq_self_iff.mpr
  exact Submodule.starProjection_apply_mem K x

/-- The symmetric-subspace projector is idempotent and self-adjoint. -/
theorem symmetricSubspaceProjector_isProjector (n : ℕ) :
    Op.IsProjector (symmetricSubspaceProjector n) := by
  refine ⟨?_, ?_⟩
  · -- Idempotence: P · P = P.
    apply LinearMap.ext
    intro ψ
    rw [Op.comp_apply]
    exact starProjection_idempotent_apply (SymmetricSpan n) ψ
  · -- Self-adjoint.
    show LinearMap.adjoint (symmetricSubspaceProjector n)
      = symmetricSubspaceProjector n
    apply LinearMap.ext
    intro ψ
    apply ext_inner_left ℂ
    intro φ
    have hadj : inner ℂ φ (LinearMap.adjoint (symmetricSubspaceProjector n) ψ)
              = inner ℂ ((symmetricSubspaceProjector n) φ) ψ :=
      LinearMap.adjoint_inner_right (E := QubitRegister n) (F := QubitRegister n)
        (symmetricSubspaceProjector n) φ ψ
    rw [hadj]
    -- Goal: ⟨(SymmetricSpan n).starProjection φ, ψ⟩ = ⟨φ, (SymmetricSpan n).starProjection ψ⟩
    exact Submodule.inner_starProjection_left_eq_right (SymmetricSpan n) φ ψ

/-! ## 2. Code-subspace projector via Dicke ONB -/

/-- Span of a finite subset of Dicke states inside the symmetric
subspace. For `S : Finset (Fin (n+1))`, this is
`C_coh = span {|D_w⟩ : w ∈ S}`. -/
noncomputable def codeSubspace (n : ℕ) (S : Finset (Fin (n + 1))) :
    Submodule ℂ (QubitRegister n) :=
  Submodule.span ℂ ((fun w : Fin (n + 1) => (dickeState n w)) '' (S : Set (Fin (n + 1))))

/-- The code subspace is contained in the symmetric subspace. -/
theorem codeSubspace_le_symmetricSpan
    (n : ℕ) (S : Finset (Fin (n + 1))) :
    codeSubspace n S ≤ SymmetricSpan n := by
  unfold codeSubspace SymmetricSpan
  apply Submodule.span_le.mpr
  intro x hx
  obtain ⟨w, _, hw⟩ := hx
  apply Submodule.subset_span
  exact ⟨w, hw⟩

/-- Orthogonal projector onto the code subspace. Implemented via
Mathlib's `Submodule.starProjection`. -/
noncomputable def codeSubspaceProjector (n : ℕ) (S : Finset (Fin (n + 1))) :
    Op (QubitRegister n) :=
  ((codeSubspace n S).starProjection : QubitRegister n →L[ℂ] QubitRegister n)

/-- The code-subspace projector is idempotent and self-adjoint. -/
theorem codeSubspaceProjector_isProjector
    (n : ℕ) (S : Finset (Fin (n + 1))) :
    Op.IsProjector (codeSubspaceProjector n S) := by
  refine ⟨?_, ?_⟩
  · apply LinearMap.ext
    intro ψ
    rw [Op.comp_apply]
    exact starProjection_idempotent_apply (codeSubspace n S) ψ
  · show LinearMap.adjoint (codeSubspaceProjector n S)
      = codeSubspaceProjector n S
    apply LinearMap.ext
    intro ψ
    apply ext_inner_left ℂ
    intro φ
    have hadj : inner ℂ φ (LinearMap.adjoint (codeSubspaceProjector n S) ψ)
              = inner ℂ ((codeSubspaceProjector n S) φ) ψ :=
      LinearMap.adjoint_inner_right (E := QubitRegister n) (F := QubitRegister n)
        (codeSubspaceProjector n S) φ ψ
    rw [hadj]
    exact Submodule.inner_starProjection_left_eq_right (codeSubspace n S) φ ψ

/-! ## 3. Abstention identity: ‖(I − P) ψ‖² = ‖ψ‖² − ‖P ψ‖² -/

/-- Pointwise identity for the orthogonal complement of an orthogonal
projector: applying `(id − P)` is the same as `ψ − P ψ`. -/
theorem complement_apply
    (P : Op (QubitRegister n)) (ψ : QubitRegister n) :
    ((Op.id : Op (QubitRegister n)) - P) ψ = ψ - P ψ := by
  simp [Op.id, LinearMap.sub_apply]

/-- **Abstention identity (orthogonal-projector form).** For an
orthogonal projector `P` on `QubitRegister n` and any vector `ψ`, the
squared norm of the complement projection equals the difference of
squared norms:
`‖(id − P) ψ‖² = ‖ψ‖² − ‖P ψ‖²`.

This is the structural form of `prop:abstention-as-overlap`:
`q_abst^wf = ‖(1 − P_C) ψ_α‖²`.

Proof: Pythagoras on the orthogonal decomposition
`ψ = P ψ + (id − P) ψ`, where `P ψ ⊥ (id − P) ψ` because
`P` is self-adjoint and idempotent. -/
theorem complement_norm_sq_eq
    {P : Op (QubitRegister n)} (hP : Op.IsProjector P)
    (ψ : QubitRegister n) :
    ‖((Op.id : Op (QubitRegister n)) - P) ψ‖ ^ 2 = ‖ψ‖ ^ 2 - ‖P ψ‖ ^ 2 := by
  -- We rely on the inner-product identity:
  --   ‖ψ − Pψ‖² + ‖Pψ‖² = ‖ψ‖²,
  -- which holds because ⟨ψ − Pψ, Pψ⟩ = 0 from P† = P, P² = P:
  --   ⟨ψ − Pψ, Pψ⟩ = ⟨ψ, Pψ⟩ − ⟨Pψ, Pψ⟩
  --                = ⟨ψ, Pψ⟩ − ⟨ψ, P(Pψ)⟩       (P self-adjoint)
  --                = ⟨ψ, Pψ⟩ − ⟨ψ, Pψ⟩            (P idempotent)
  --                = 0.
  rw [complement_apply]
  -- Show ‖Pψ‖² + ‖ψ − Pψ‖² = ‖ψ‖² via orthogonality of Pψ and ψ − Pψ.
  have horth : inner ℂ (P ψ) (ψ - P ψ) = 0 := by
    rw [inner_sub_right]
    -- ⟨Pψ, ψ⟩ − ⟨Pψ, Pψ⟩ = 0 since ⟨Pψ, Pψ⟩ = ⟨ψ, P² ψ⟩ = ⟨ψ, Pψ⟩
    --                              and ⟨Pψ, ψ⟩ = ⟨ψ, P† ψ⟩ = ⟨ψ, Pψ⟩.
    have hadj : inner ℂ (P ψ) ψ = inner ℂ ψ (P ψ) := by
      have := Op.adjoint_inner_right P ψ ψ
      rw [hP.hermitian] at this
      exact this.symm
    have hPP : inner ℂ (P ψ) (P ψ) = inner ℂ ψ (P ψ) := by
      have h1 : inner ℂ (P ψ) (P ψ) = inner ℂ ψ (Op.adjoint P (P ψ)) := by
        rw [Op.adjoint_inner_right]
      rw [hP.hermitian] at h1
      rw [h1, hP.apply_apply]
    rw [hadj, hPP, sub_self]
  -- Pythagoras: ‖Pψ + (ψ − Pψ)‖² = ‖Pψ‖² + ‖ψ − Pψ‖² when ⟨Pψ, ψ − Pψ⟩ = 0.
  have hsum : (P ψ) + (ψ - P ψ) = ψ := by abel
  have hpyth : ‖P ψ‖ ^ 2 + ‖ψ - P ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    have hortho_re : RCLike.re (inner ℂ (P ψ) (ψ - P ψ)) = 0 := by
      rw [horth]; simp
    have hnsq : ‖(P ψ) + (ψ - P ψ)‖ ^ 2
              = ‖P ψ‖ ^ 2 + ‖ψ - P ψ‖ ^ 2 := by
      rw [@norm_add_sq ℂ]
      rw [hortho_re]; ring
    rw [hsum] at hnsq
    exact hnsq.symm
  linarith [hpyth]

/-! ## 4. Convenience: complement projector is also a projector -/

/-- `id − P` is a projector when `P` is. (Re-export of
`Op.IsProjector.complement` for `QubitRegister n`.) -/
theorem complement_isProjector
    {P : Op (QubitRegister n)} (hP : Op.IsProjector P) :
    Op.IsProjector ((Op.id : Op (QubitRegister n)) - P) :=
  hP.complement

end QEC.Operators.Projector
