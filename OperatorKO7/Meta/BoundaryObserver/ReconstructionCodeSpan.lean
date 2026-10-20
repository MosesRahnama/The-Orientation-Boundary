import OperatorKO7.Meta.BoundaryObserver.ReconstructionKnillLaflamme

set_option autoImplicit false

/-!
# All-code-matrix recovery from one Knill-Laflamme construction

The positive-syndrome donor and orthogonal-recovery donor already quantify
over every complex matrix supported on the code. This source reuses their
single constructed recovery without density spanning or polarization.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ReconstructionCodeSpan

open Matrix
open scoped BigOperators ComplexOrder
open OperatorKO7.Meta.BoundaryObserver.ReconstructionRecovery
open OperatorKO7.Meta.BoundaryObserver.ReconstructionKnillLaflamme

noncomputable section

abbrev Mat (n : ℕ) := ReconstructionRecovery.Mat n

/-- The same complete finite error family has a CPTP recovery on every
code-supported complex matrix if the exact scalar overlaps hold.
The construction includes the zero projector and dimension zero. -/
theorem knillLaflamme_all_code_matrices
    {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n)
    (hstar : p = dagger p) (hidem : p * p = p)
    (hcomplete : (∑ e : E, dagger (errors e) * errors e) = 1)
    (hKL : ∃ c : E → E → ℂ, ∀ a b,
      p * dagger (errors a) * errors b * p = c a b • p) :
    ∃ recovery : Mat n →ₗ[ℂ] Mat n,
      CompletelyPositive recovery ∧ TracePreserving recovery ∧
      ∀ a : Mat n, p * a * p = a →
        recovery (krausOutput errors a) = a := by
  classical
  by_cases hzero : p = 0
  · subst p
    refine ⟨LinearMap.id, completelyPositive_id n, tracePreserving_id n, ?_⟩
    intro a ha
    have hz : (0 : Mat n) = a := by
      simpa only [Matrix.zero_mul] using ha
    change krausOutput errors a = a
    rw [← hz, krausOutput_zero]
  · obtain ⟨c, hfactor⟩ := hKL
    let cm : Matrix E E ℂ := fun a b => c a b
    have hc : cm.PosSemidef :=
      overlapMatrix_posSemidef errors p hstar hidem hzero cm hfactor
    let u : Matrix E E ℂ := hc.1.eigenvectorUnitary
    let wt : E → ℝ := hc.1.eigenvalues
    have hu : u * uᴴ = 1 :=
      (hc.1.eigenvectorUnitary).property.2
    have hwt : ∀ d, 0 ≤ wt d := hc.eigenvalues_nonneg
    have hdiag : ∀ d e,
        p * dagger (rotatedErrors errors u d) *
          rotatedErrors errors u e * p =
          (Matrix.diagonal (fun k => (wt k : ℂ))) d e • p := by
      intro d e
      have hdiagm :
          uᴴ * cm * u = Matrix.diagonal (fun k : E => (wt k : ℂ)) :=
        hc.1.star_mul_self_mul_eq_diagonal
      rw [rotatedErrors_overlap errors p cm u hfactor d e, hdiagm]
    have hsum : (∑ d : E, (wt d : ℂ)) = 1 :=
      knillLaflamme_eigenweights_total errors p hzero hidem hcomplete
        cm hfactor hc
    have hsumPos :
        (∑ d : {k : E // 0 < wt k}, (wt d.val : ℂ)) = 1 :=
      positive_eigenweights_sum wt hwt hsum
    let syndrome : {k : E // 0 < wt k} → Mat n :=
      normalizedSyndromeErrors errors p u wt
    have hsupport (d : {k : E // 0 < wt k}) :
        syndrome d * p = syndrome d :=
      normalizedSyndromeErrors_mul_p errors p hidem u wt d
    have horth : ∀ d e : {k : E // 0 < wt k},
        dagger (syndrome d) * syndrome e =
          if d = e then p else 0 :=
      normalizedSyndromeErrors_orthogonal errors p hstar u wt hdiag
    refine ⟨orthogonalRecovery syndrome,
      orthogonalRecovery_completelyPositive syndrome,
      orthogonalRecovery_tracePreserving syndrome p hsupport
        (fun d e => (horth d e).trans (by split_ifs <;> rfl)), ?_⟩
    have hnoise : ∀ b : Mat n, p * b * p = b →
        krausOutput errors b =
          ∑ d : {k : E // 0 < wt k}, (wt d.val : ℂ) •
            (syndrome d * b * dagger (syndrome d)) := by
      intro b hb
      exact knillLaflamme_positive_syndrome_decomposition
        errors p hstar u hu wt hwt hdiag b hb
    intro a ha
    exact orthogonalRecovery_correct errors syndrome p
      (fun d : {k : E // 0 < wt k} => (wt d.val : ℂ))
      hsupport (fun d e => (horth d e).trans (by split_ifs <;> rfl))
      hsumPos hnoise a ha

/-- The zero projector has only the zero supported matrix.
The ambient identity recovery is CPTP even for an arbitrary finite error family. -/
theorem zero_projector_all_code_matrices
    {n : ℕ} {E : Type} [Fintype E] (errors : E → Mat n) :
    ∃ recovery : Mat n →ₗ[ℂ] Mat n,
      CompletelyPositive recovery ∧ TracePreserving recovery ∧
      ∀ a : Mat n, (0 : Mat n) * a * 0 = a →
        recovery (krausOutput errors a) = a := by
  refine ⟨LinearMap.id, completelyPositive_id n, tracePreserving_id n, ?_⟩
  intro a ha
  have hz : (0 : Mat n) = a := by
    simpa only [Matrix.zero_mul] using ha
  change krausOutput errors a = a
  rw [← hz, krausOutput_zero]

/-- The reverse direction needs only recovery on all supported matrices.
The donor necessity proof then uses the supported density matrices as a subset. -/
theorem knillLaflamme_all_code_matrices_necessity
    {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n)
    (hstar : p = dagger p) (hidem : p * p = p)
    (recovery : Mat n →ₗ[ℂ] Mat n)
    (hCP : CompletelyPositive recovery)
    (hTP : TracePreserving recovery)
    (hfixed : ∀ a : Mat n, p * a * p = a →
      recovery (krausOutput errors a) = a) :
    ∃ c : E → E → ℂ, ∀ i j,
      p * dagger (errors i) * errors j * p = c i j • p := by
  exact knillLaflamme_necessity errors p hstar hidem recovery hCP hTP
    (fun ρ hρ => hfixed ρ.val hρ)

/-- The exact finite-error KL equivalence holds for recovery on every
code-supported complex matrix. No assumption of positive dimension is needed. -/
theorem knillLaflamme_all_code_matrices_equivalence
    {n : ℕ} {E : Type} [Fintype E]
    (errors : E → Mat n) (p : Mat n)
    (hstar : p = dagger p) (hidem : p * p = p)
    (hcomplete : (∑ e : E, dagger (errors e) * errors e) = 1) :
    (∃ c : E → E → ℂ, ∀ i j,
      p * dagger (errors i) * errors j * p = c i j • p) ↔
      ∃ recovery : Mat n →ₗ[ℂ] Mat n,
        CompletelyPositive recovery ∧ TracePreserving recovery ∧
        ∀ a : Mat n, p * a * p = a →
          recovery (krausOutput errors a) = a := by
  constructor
  · exact knillLaflamme_all_code_matrices errors p hstar hidem hcomplete
  · rintro ⟨recovery, hCP, hTP, hfixed⟩
    exact knillLaflamme_all_code_matrices_necessity
      errors p hstar hidem recovery hCP hTP hfixed

/-- Public goal: exact KL overlap equations if and only if one constructive
CPTP recovery reverses the same finite error map on the entire code matrix span. -/
def CodeMatrixRecoveryGoal : Prop :=
  ∀ (n : ℕ) (E : Type) [Fintype E]
    (errors : E → Mat n) (p : Mat n)
    (_ : p = dagger p) (_ : p * p = p)
    (_ : (∑ e : E, dagger (errors e) * errors e) = 1),
    (∃ c : E → E → ℂ, ∀ i j,
      p * dagger (errors i) * errors j * p = c i j • p) ↔
      ∃ recovery : Mat n →ₗ[ℂ] Mat n,
        CompletelyPositive recovery ∧ TracePreserving recovery ∧
        ∀ a : Mat n, p * a * p = a →
          recovery (krausOutput errors a) = a

theorem codeMatrixRecoveryGoal : CodeMatrixRecoveryGoal := by
  intro n E inst errors p hstar hidem hcomplete
  exact knillLaflamme_all_code_matrices_equivalence
    errors p hstar hidem hcomplete

/-- The finite auxiliary register retains every matrix block. An exact
base-channel recovery therefore recovers its amplification for all blockwise
code-supported matrices, including off-diagonal ancillary blocks. -/
theorem amplify_code_recovery
    {n : ℕ} (p : Mat n)
    (f g : Mat n →ₗ[ℂ] Mat n)
    (hfixed : ∀ a : Mat n, p * a * p = a → g (f a) = a)
    (r : ℕ)
    (A : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ)
    (hsupported : ∀ i j : Fin r,
      p * (show Mat n from fun x y => A (i,x) (j,y)) * p =
        (show Mat n from fun x y => A (i,x) (j,y))) :
    ReconstructionRecovery.amplify g r
      (ReconstructionRecovery.amplify f r A) = A := by
  ext ⟨i, x⟩ ⟨j, y⟩
  change g (f (fun s t : Fin n => A (i,s) (j,t))) x y = A (i,x) (j,y)
  exact congrArg (fun b : Mat n => b x y)
    (hfixed _ (hsupported i j))

/-- The very same syndrome recovery acts correctly on every finite ancillary
extension. No ancillary dimension or state-positivity premise is added. -/
def AncillaryCodeRecoveryGoal : Prop :=
  ∀ (n : ℕ) (E : Type) [Fintype E]
    (errors : E → Mat n) (p : Mat n)
    (_ : p = dagger p) (_ : p * p = p)
    (_ : (∑ e : E, dagger (errors e) * errors e) = 1)
    (_ : ∃ c : E → E → ℂ, ∀ i j,
      p * dagger (errors i) * errors j * p = c i j • p),
    ∃ recovery : Mat n →ₗ[ℂ] Mat n,
      CompletelyPositive recovery ∧ TracePreserving recovery ∧
      ∀ (r : ℕ) (A : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ),
        (∀ i j : Fin r,
          p * (show Mat n from fun x y => A (i,x) (j,y)) * p =
            (show Mat n from fun x y => A (i,x) (j,y))) →
        ReconstructionRecovery.amplify recovery r
          (ReconstructionRecovery.amplify (krausLinearMap errors) r A) = A

theorem ancillaryCodeRecoveryGoal : AncillaryCodeRecoveryGoal := by
  intro n E inst errors p hstar hidem hcomplete hKL
  obtain ⟨recovery, hCP, hTP, hfixed⟩ :=
    knillLaflamme_all_code_matrices errors p hstar hidem hcomplete hKL
  refine ⟨recovery, hCP, hTP, ?_⟩
  intro r A hA
  apply amplify_code_recovery p (krausLinearMap errors) recovery
  · intro a ha
    exact hfixed a ha
  · exact hA

/-- The strengthened KL equivalence and its full finite-ancilla
realization form one independently reusable public quantum-code package. -/
def CodeSpanFullGoal : Prop :=
  CodeMatrixRecoveryGoal ∧ AncillaryCodeRecoveryGoal

theorem codeSpanFullGoal : CodeSpanFullGoal :=
  ⟨codeMatrixRecoveryGoal, ancillaryCodeRecoveryGoal⟩

end

end OperatorKO7.Meta.BoundaryObserver.ReconstructionCodeSpan
