import OperatorKO7.Kernel
import OperatorKO7.Meta.Confluence_Safe
import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly

/-!
# Branch entropy of the eqW confluence breaker

This module is the information-theoretic overlay on the already-mechanized
confluence-side boundary. It is net-new for the eqW paper, but it is now part of
the checked surface: it contains no `sorry`, no `admit`, no new `axiom`, no
`native_decide`, and no `@[csimp]`; the public theorem has been spot-checked with
`#print axioms`.

## What it adds

The orientation boundary and the confluence (Distinction) boundary already
discharge to a shared meta-level cost object, the META-HALT typed-output algebra:
the SafeStep repair is an instance of the typed-refusal meta-halt theorem
(`GaugeFixingGuard.safestep_is_meta_halt`), the disequality guard is the imported
license (`GaugeFixingGuard.SafeStepGuard`,
`SmugglingUndecidability.safestep_guard_smuggles_external_observer`), and the
eqW(void,void) fracture is packaged as a pre-undecidability fracture whose engine
output is a T3 confession certificate
(`SmugglingUndecidability.eqW_void_void_is_pre_undecidability_fracture`,
`MetaHalt.Predicate.TypedOutput.T3_confession`).

This module quantifies that event. Confluence failure at the breaker is exactly a
two-verdict source; the licensed relation collapses it to one verdict. In bits,
that is a collapse from `1` to `0`: a one-bit *branch entropy* collapse. The bit
is operational nondeterminism in the raw rewrite relation, not Shannon ignorance
about the term, so the cost is a preservation cost, not a discovery cost.

`verdictBits` is the binary specialization of `log2` on the verdict count; it is
defined by an explicit match so that it reduces definitionally (avoiding the
well-founded-recursion opacity of `Nat.log2`).
-/

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly

namespace OperatorKO7.Meta.SafeStep.BranchEntropy

/-- Branch entropy in bits: `log2` of the number of distinct terminal verdicts a
source admits, specialized to the binary case that occurs at a non-left-linear
critical pair (one verdict gives `0`, two or more give `1`). Defined by a
decidable comparison so the closed instances reduce under `decide`. -/
def verdictBits (n : Nat) : Nat := if n ≤ 1 then 0 else 1

@[simp] theorem verdictBits_one : verdictBits 1 = 0 := by decide
@[simp] theorem verdictBits_two : verdictBits 2 = 1 := by decide

/-- A confluence-breaking source carries two distinct unjoinable verdicts, hence
one bit of branch entropy; a confluent source carries one verdict, hence zero.
The confluence-preservation move is therefore a one-bit collapse. -/
theorem branchEntropy_collapse_one_bit :
    verdictBits 2 - verdictBits 1 = 1 := by decide

/-- The raw two-verdict fact at the canonical breaker, re-exported from
`EqWVoidAnomaly` as the source of the one branch-entropy bit. -/
theorem raw_two_unjoinable_verdicts :
    CriticalPairAt (eqW void void) void (integrate (merge void void)) :=
  local_confluence_fails_at_eqW_void_void

/-- The diagonal refusal certificate. The licensed difference branch requires a
disequality witness `a ≠ b`; on the diagonal that license type is empty, so the
negative certificate `¬ (a ≠ a)` is what the licensed layer carries to refuse the
otherwise-available raw difference branch. It is constant size for every `a`. -/
theorem diagonal_refusal (a : Trace) : ¬ (a ≠ a) := fun h => h rfl

/-- The branch-entropy collapse at the confluence breaker, packaged: the raw
relation carries two unjoinable verdicts (one bit), and the licensed layer pays a
diagonal refusal certificate to collapse to a single verdict (zero bits). The
positive off-diagonal license (`GaugeFixingGuard.SafeStepGuard`) and the
meta-halt T3 confession certificate (`SmugglingUndecidability`) are the cost
objects on the other side; this record is their information-theoretic measure. -/
structure BranchEntropyCollapse : Prop where
  raw_two : CriticalPairAt (eqW void void) void (integrate (merge void void))
  diagonal_refused : ¬ ((void : Trace) ≠ void)
  collapse_bits : verdictBits 2 - verdictBits 1 = 1

/-- The confluence breaker realizes a one-bit branch-entropy collapse paid for by
a refusal certificate. -/
theorem eqW_void_void_branchEntropy_collapse : BranchEntropyCollapse :=
  { raw_two := local_confluence_fails_at_eqW_void_void
    diagonal_refused := diagonal_refusal void
    collapse_bits := branchEntropy_collapse_one_bit }

end OperatorKO7.Meta.SafeStep.BranchEntropy
