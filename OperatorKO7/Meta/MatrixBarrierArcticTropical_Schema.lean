import OperatorKO7.Meta.MatrixBarrierArbitrary_Schema
import OperatorKO7.Meta.ArcticBarrier_Schema

/-!
# Arctic/Tropical Matrix Scalarization Certificates

This module starts the finite-vector arctic/tropical matrix upgrade without claiming a full
semiring metatheory that the current artifact does not yet prove. The barrier theorems here
are certificate-backed:

- the carrier is an explicit finite vector family;
- the ambient comparison law is explicit;
- a theorem-visible scalarization certificate links that comparison to the already-landed
  arbitrary mixed-matrix scalarization barrier.

This yields real matrix-class barrier theorems while keeping the current limitation honest.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Finite-vector arctic carrier. -/
abbrev ArcticMatrixVec (d : Nat) := Fin d → ArcticNat

/-- Finite-vector tropical carrier. -/
abbrev TropicalMatrixVec (d : Nat) := MatrixVec d

/-- Finite part of an arctic vector, treating `bot` as `0` for the certificate-backed
scalarization interface. -/
@[simp] def arcticFinitePart {d : Nat} (v : ArcticMatrixVec d) : MatrixVec d :=
  fun i =>
    match v i with
    | ArcticNat.bot => 0
    | ArcticNat.fin n => n

/-- Identity scalarization for finite tropical vectors. -/
@[simp] def tropicalFinitePart {d : Nat} (v : TropicalMatrixVec d) : MatrixVec d :=
  v

/-- Explicit comparison and scalarization certificate for finite-vector arctic carriers. -/
structure ArcticMatrixCertificate (d : Nat) where
  weight : MatrixVec d
  scalarize : ArcticMatrixVec d → MatrixVec d
  lt : ArcticMatrixVec d → ArcticMatrixVec d → Prop
  nonstrict :
    ∀ {u v : ArcticMatrixVec d},
      lt u v → matrixScalarize weight (scalarize u) ≤ matrixScalarize weight (scalarize v)

/-- Explicit finite-vector arctic matrix interface backed by an arbitrary mixed-matrix
scalarization witness. -/
structure ArcticMatrixMeasure (S : StepDuplicatingSchema) (d : Nat) where
  eval : S.T → ArcticMatrixVec d
  scalarMeasure : MatrixArbitraryMeasure S d

/-- Explicit comparison and scalarization certificate for finite-vector tropical carriers. -/
structure TropicalMatrixCertificate (d : Nat) where
  weight : MatrixVec d
  scalarize : TropicalMatrixVec d → MatrixVec d
  lt : TropicalMatrixVec d → TropicalMatrixVec d → Prop
  nonstrict :
    ∀ {u v : TropicalMatrixVec d},
      lt u v → matrixScalarize weight (scalarize u) ≤ matrixScalarize weight (scalarize v)

/-- Explicit finite-vector tropical matrix interface backed by an arbitrary mixed-matrix
scalarization witness. -/
structure TropicalMatrixMeasure (S : StepDuplicatingSchema) (d : Nat) where
  eval : S.T → TropicalMatrixVec d
  scalarMeasure : MatrixArbitraryMeasure S d

/-- Certificate-backed arctic matrix barrier via the arbitrary mixed-matrix scalarization
theorem. -/
theorem no_arcticMatrix_orients_dup_step_of_scalar_dominance_pump
    {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticMatrixMeasure S d)
    (C : ArcticMatrixCertificate d)
    (hweight : C.weight = M.scalarMeasure.weight)
    (hscalarize : ∀ t : S.T, C.scalarize (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ (∀ (b s n : S.T),
      C.lt (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  have hunbounded' : HasUnboundedRange M.scalarMeasure.scalarAffine := by
    intro k
    rcases hunbounded k with ⟨t, ht⟩
    exact ⟨t, by simpa [MatrixArbitraryMeasure.scalarAffine] using ht⟩
  have heval :
      ∀ t : S.T,
        M.scalarMeasure.scalarAffine.eval t =
          matrixScalarize C.weight (C.scalarize (M.eval t)) := by
    intro t
    simp [MatrixArbitraryMeasure.scalarAffine, hweight, hscalarize t]
  exact
    no_orients_dup_step_of_projected_primary_dominance
      (μ := M.eval)
      (R := C.lt)
      (π := fun u => matrixScalarize C.weight (C.scalarize u))
      (hdom := fun {u v} huv => C.nonstrict huv)
      (M := M.scalarMeasure.scalarAffine)
      heval
      hunbounded'

/-- Certificate-backed tropical matrix barrier via the arbitrary mixed-matrix scalarization
theorem. -/
theorem no_tropicalMatrix_orients_dup_step_of_scalar_dominance_pump
    {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalMatrixMeasure S d)
    (C : TropicalMatrixCertificate d)
    (hweight : C.weight = M.scalarMeasure.weight)
    (hscalarize : ∀ t : S.T, C.scalarize (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ (∀ (b s n : S.T),
      C.lt (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  have hunbounded' : HasUnboundedRange M.scalarMeasure.scalarAffine := by
    intro k
    rcases hunbounded k with ⟨t, ht⟩
    exact ⟨t, by simpa [MatrixArbitraryMeasure.scalarAffine] using ht⟩
  have heval :
      ∀ t : S.T,
        M.scalarMeasure.scalarAffine.eval t =
          matrixScalarize C.weight (C.scalarize (M.eval t)) := by
    intro t
    simp [MatrixArbitraryMeasure.scalarAffine, hweight, hscalarize t]
  exact
    no_orients_dup_step_of_projected_primary_dominance
      (μ := M.eval)
      (R := C.lt)
      (π := fun u => matrixScalarize C.weight (C.scalarize u))
      (hdom := fun {u v} huv => C.nonstrict huv)
      (M := M.scalarMeasure.scalarAffine)
      heval
      hunbounded'

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
