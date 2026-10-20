import OperatorKO7.Meta.Recursor.SchemaTraceKernel
import OperatorKO7.Meta.SchemaConfessionDominance

/-!
# Proof entropy read off the leaf-schema trace

Proposition 11.14 defines the proof entropy of a trace term as the weighted size of the payload
copies in completed wrappers divided by the weighted size of the term. This module computes both
quantities on the live states `orbitState (base ia) (pay ib) k i` of the leaf-schema trace and
feeds them to `proof_entropy_nondecreasing`.

* `wrapperPayload_closed_form`: the completed wrappers of a live state hold payload weight
  `i * beta`; `wrapperPayload_eq_countG_mul` reads it as the `G` count times the payload weight.
* `trace_size_closed_form`: the weighted size is `i * (gamma + beta) + (k - i) + (c_0 + beta)`
  with `c_0 = phi + alpha + zeta`, the closed form of the proposition with `|G| = gamma`,
  `|b| = beta` and `c_* = c_0 + beta`.
* `trace_proofEntropy_nondecreasing`: the ratio of the two trace quantities is nondecreasing
  across the live stages, in cross-multiplied form.
* `trace_proofEntropy_zero`: the completed wrappers hold payload weight zero at stage zero.

Trust: kernel-only. No `sorry`, no `admit`, no new `axiom`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.ProofEntropyTrace

open OperatorKO7.Meta.Recursor.SchemaTraceKernel
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem

/-- Weighted size of the payload copies held by completed `G` wrappers: the left arguments of the
`G` spine above the active site. -/
def wrapperPayload (alpha beta gamma phi zeta : Nat) : SchemaTerm → Nat
  | .Z => 0
  | .S _ => 0
  | .base _ => 0
  | .pay _ => 0
  | .F _ _ _ => 0
  | .G y t => wsize alpha beta gamma phi zeta y + wrapperPayload alpha beta gamma phi zeta t

theorem wrapperPayload_gPow (alpha beta gamma phi zeta : Nat) (y t : SchemaTerm) (i : Nat) :
    wrapperPayload alpha beta gamma phi zeta (gPow y i t) =
      i * wsize alpha beta gamma phi zeta y + wrapperPayload alpha beta gamma phi zeta t := by
  induction i with
  | zero => simp [gPow]
  | succ i ih =>
      simp only [gPow, wrapperPayload, ih, Nat.succ_mul]
      omega

/-- On a live state the completed wrappers hold payload weight `i * beta`. -/
theorem wrapperPayload_closed_form (alpha beta gamma phi zeta ia ib k i : Nat) (hi : i ≤ k) :
    wrapperPayload alpha beta gamma phi zeta (orbitState (.base ia) (.pay ib) k i) =
      i * beta := by
  rw [orbitState, if_pos hi, wrapperPayload_gPow]
  simp [wsize, wrapperPayload]

/-- The payload weight in completed wrappers is the `G` count times the payload weight. -/
theorem wrapperPayload_eq_countG_mul (alpha beta gamma phi zeta ia ib k i : Nat) (hi : i ≤ k) :
    wrapperPayload alpha beta gamma phi zeta (orbitState (.base ia) (.pay ib) k i) =
      countG (orbitState (.base ia) (.pay ib) k i) * beta := by
  rw [wrapperPayload_closed_form alpha beta gamma phi zeta ia ib k i hi,
    countG_closed_form ia ib k i hi]

/-- The weighted size of a live state: `i (|G| + |b|) + (k - i) + c_*` with
`c_* = c_0 + |b|` and `c_0 = phi + alpha + zeta` free of the payload weight. -/
theorem trace_size_closed_form (alpha beta gamma phi zeta ia ib k i : Nat) (hi : i ≤ k) :
    wsize alpha beta gamma phi zeta (orbitState (.base ia) (.pay ib) k i) =
      i * (gamma + beta) + (k - i) + ((phi + alpha + zeta) + beta) := by
  rw [wsize_closed_form alpha beta gamma phi zeta ia ib k i hi]
  omega

/-- The numerator of the proposition is the trace quantity. -/
theorem wrapperPayload_eq_proofEntropyNumerator (alpha beta gamma phi zeta ia ib k i : Nat)
    (hi : i ≤ k) :
    wrapperPayload alpha beta gamma phi zeta (orbitState (.base ia) (.pay ib) k i) =
      proofEntropyNumerator i beta := by
  rw [wrapperPayload_closed_form alpha beta gamma phi zeta ia ib k i hi]
  rfl

/-- The denominator of the proposition is the trace quantity. -/
theorem wsize_eq_proofEntropyDenominator (alpha beta gamma phi zeta ia ib k i : Nat)
    (hi : i ≤ k) :
    wsize alpha beta gamma phi zeta (orbitState (.base ia) (.pay ib) k i) =
      proofEntropyDenominator k i (gamma + beta) (phi + alpha + beta + zeta) := by
  rw [wsize_closed_form alpha beta gamma phi zeta ia ib k i hi]
  rfl

/-- The proof entropy of the trace, the ratio of the two trace quantities, is nondecreasing across
every live stage. -/
theorem trace_proofEntropy_nondecreasing (alpha beta gamma phi zeta ia ib k i : Nat)
    (hi : i < k) :
    wrapperPayload alpha beta gamma phi zeta (orbitState (.base ia) (.pay ib) k i) *
        wsize alpha beta gamma phi zeta (orbitState (.base ia) (.pay ib) k (i + 1)) ≤
      wrapperPayload alpha beta gamma phi zeta (orbitState (.base ia) (.pay ib) k (i + 1)) *
        wsize alpha beta gamma phi zeta (orbitState (.base ia) (.pay ib) k i) := by
  have hle : i ≤ k := Nat.le_of_lt hi
  have hsucc : i + 1 ≤ k := Nat.succ_le_of_lt hi
  rw [wrapperPayload_eq_proofEntropyNumerator alpha beta gamma phi zeta ia ib k i hle,
    wrapperPayload_eq_proofEntropyNumerator alpha beta gamma phi zeta ia ib k (i + 1) hsucc,
    wsize_eq_proofEntropyDenominator alpha beta gamma phi zeta ia ib k (i + 1) hsucc,
    wsize_eq_proofEntropyDenominator alpha beta gamma phi zeta ia ib k i hle]
  exact proof_entropy_nondecreasing k beta (gamma + beta) (phi + alpha + beta + zeta) i

/-- At stage zero the completed wrappers hold no payload. -/
theorem trace_proofEntropy_zero (alpha beta gamma phi zeta ia ib k : Nat) :
    wrapperPayload alpha beta gamma phi zeta (orbitState (.base ia) (.pay ib) k 0) = 0 := by
  rw [wrapperPayload_closed_form alpha beta gamma phi zeta ia ib k 0 (Nat.zero_le k)]
  simp

end OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.ProofEntropyTrace
