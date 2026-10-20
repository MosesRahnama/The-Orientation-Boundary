import OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
import OperatorKO7.Meta.SafeStep.BranchEntropy

/-!
# The eqW diagonal is the echo vacuum (T4)

The Distinction-Boundary paper reads `eqW(void, void)` as "the object-level miniature of the informational
circular reference": a distinction-producing query issued against a zero-distinction input. This module
makes that reading a theorem on the licensed-channel deficit substrate.

The diagonal disequality query has one direct-surface cell (the querant already holds the identity datum
`void = void`), a disequality verdict `χ≠ ∈ Fin 2` (`0` = same, `1` = distinct), and the two raw kernel
branches `Fin 2` (the reflexive rule and the difference rule) equally available. On the diagonal both
branches report "same", so the channel conditional is the point mass on "same" regardless of which branch
fired: the answer carries no information about `χ≠` beyond what the direct surface already fixes.

* `eqW_diagonal_echo_vacuum` — the licensed-channel deficit is exactly `0`: the non-vacuous query returns
  vacuous (instance of `circular_reference_zero_deficit`).
* `eqW_diagonal_zero_residual` — `H(χ≠ | W0) = 0`: the querant had no residual uncertainty for any channel
  to resolve. This is the sharp echo-vacuum content (the upper end of the deficit bracket is itself zero).
* `eqW_diagonal_echo_vacuum_with_fork` — the same diagonal carries the information-face vacuum and the
  rewrite-face fracture (`eqW void void` forks): the unguarded difference branch manufactures a non-null
  record from a zero-deficit query, the rewrite-level echo vacuum.

## Claim typing (binding)
* PROVEN: the three theorems below (concrete `Fin 1 / Fin 2 / Fin 2` instances of the deficit machinery,
  plus the re-exported fork). Being concrete, they are non-vacuous by construction (R5).
* ANALOGY (docstring only): the identification of `χ≠`/the branches with a physical query channel; the
  formal content is the deficit and residual computations.

## Audit slots
- Relation: the kernel `Step` relation enters only through the re-exported `eqW void void` critical pair;
  the new content is finite information theory on a concrete query instance.
- Closure: `propext`, `Classical.choice`, `Quot.sound` (or a subset); verified by `#print axioms`.
- Trust: no `sorry`/`admit`/`axiom`/`opaque`/`partial`/`unsafe`/`native_decide`/`bv_decide`/`@[csimp]`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.InformationalIncompleteness.EqWDiagonalDeficit

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit

/-- **The eqW diagonal is the echo vacuum.** The diagonal disequality query has licensed-channel deficit
exactly zero: the channel's report about distinctness is a redundant copy of what `W0` (the identity datum
`void = void`) already fixes, so the non-vacuous query returns vacuous. Instance of
`circular_reference_zero_deficit` with the channel-constant conditional `pointMass 0` ("same"). -/
theorem eqW_diagonal_echo_vacuum :
    deficit (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ _ => pointMass (0 : Fin 2)) = 0 :=
  circular_reference_zero_deficit _ _ _
    (fun _ => by rw [Fin.sum_univ_two]; norm_num)
    (fun _ => pointMass (0 : Fin 2)) (fun _ _ => rfl)

/-- **No residual uncertainty on the diagonal.** `H(χ≠ | W0) = 0`: the direct surface already fixes the
disequality verdict (`void = void`), so there is no residual uncertainty for any channel to resolve. The
marginalised target collapses to the point mass on "same", whose entropy is zero. -/
theorem eqW_diagonal_zero_residual :
    condEntropyDirect (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ _ => pointMass (0 : Fin 2)) = 0 := by
  unfold condEntropyDirect
  rw [Fin.sum_univ_one, one_mul]
  have hmarg : (fun x : Fin 2 => ∑ _c : Fin 2, (1 : ℝ) / 2 * pointMass (0 : Fin 2) x)
      = pointMass (0 : Fin 2) := by
    funext x; rw [Fin.sum_univ_two]; ring
  rw [hmarg, H_pointMass]

/-- **The fork is the rewrite face of the echo vacuum.** The same diagonal carries the information-face
vacuum (deficit `0`, no residual uncertainty) and the rewrite-face fracture: the unguarded kernel forks at
`eqW void void`, manufacturing a non-null record from a zero-distinction input. The two faces meet on the
single diagonal. -/
theorem eqW_diagonal_echo_vacuum_with_fork :
    deficit (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
        (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ _ => pointMass (0 : Fin 2)) = 0
      ∧ condEntropyDirect (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
        (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ _ => pointMass (0 : Fin 2)) = 0
      ∧ CriticalPairAt (eqW void void) void (integrate (merge void void)) :=
  ⟨eqW_diagonal_echo_vacuum, eqW_diagonal_zero_residual,
    local_confluence_fails_at_eqW_void_void⟩

#print axioms eqW_diagonal_echo_vacuum
#print axioms eqW_diagonal_zero_residual
#print axioms eqW_diagonal_echo_vacuum_with_fork

end OperatorKO7.Meta.InformationalIncompleteness.EqWDiagonalDeficit
