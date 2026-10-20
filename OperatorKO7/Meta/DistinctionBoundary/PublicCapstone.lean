import OperatorKO7.Meta.DistinctionBoundary.ConservativeRepair
import OperatorKO7.Meta.DistinctionBoundary.RepairCompleteness
import OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness
import OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence
import OperatorKO7.Meta.SafeStep.SyntacticNonDerivability
import OperatorKO7.Meta.DistinctionBoundary.UniqueCheck
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.API

set_option autoImplicit false

/-!
# Public capstone: the five-declaration surface of the Distinction Boundary

One theorem per pillar, re-exported under stable public names. A reader who
understands these five declarations understands the paper.

1. `conservative_repair_forces_exact_distinction`: an admissible repair
   (retention obligations plus local confluence, no guard stated) admits the
   difference branch at a pair if and only if the pair is distinct. The guard
   is a conclusion, not a hypothesis.
2. `internal_observer_cannot_realize_repair`: no term of the seven-constructor
   signature is a sound and complete disequality discriminator, so the guard
   the repair is forced to recognise is not term-definable in the native
   language. Composition reading: pillar 1 forces the guard, this pillar denies
   its internal realization; a single cross-carrier composition theorem over
   one shared carrier is named wiring, not claimed here.
3. `repair_restriction_or_joinability`: any locally confluent repair of a
   determined diagonal fork either refuses an offending diagonal reduction or
   makes the two retained verdicts joinable.
4. `ko7_distinction_boundary`: the reflexive `eqW` diagonal is the unique root
   confluence obstruction of the KO7 kernel.
5. `ko7_guarded_globally_confluent`: the guarded relation is globally
   confluent; the surgical root relation `EqGuardedStep` is root confluent
   (`Meta.EqGuardedConfluence.confluentEqGuarded`).

Relation scope: pillar 1 and 4 at kernel root; pillar 5 covers the guarded
closure of the published development. Trust: kernel only, Mathlib baseline.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.PublicCapstone

open OperatorKO7

/-- **Pillar 1.** Conservative repair forces the guard: an admissible repair
admits the difference branch at `(a, b)` if and only if `a ≠ b`. -/
theorem capstone_conservative_repair_forces_exact_distinction
    {R : Trace → Trace → Prop}
    (hR : ConservativeRepair.AdmissibleRepair R) (a b : Trace) :
    R (Trace.eqW a b) (Trace.integrate (Trace.merge a b)) ↔ a ≠ b :=
  ConservativeRepair.conservative_repair_forces_exact_distinction hR a b

/-- **Pillar 2.** The internal observer cannot supply the forced guard: no
term of the seven-constructor signature realizes disequality soundly and
completely. -/
theorem internal_observer_cannot_realize_repair :
    ¬ ∃ (t : Meta.SafeStep.SigmaFreeAlgebra.SigmaTerm),
        ∀ (a b : Meta.SafeStep.SigmaFreeAlgebra.SigmaTerm),
          (a ≠ b) ↔
            (Meta.SafeStep.SigmaFreeAlgebra.evalSigma a b t ≠
              Meta.SafeStep.SigmaFreeAlgebra.SigmaTerm.void) :=
  Meta.SafeStep.SyntacticNonDerivability.disequality_not_sigma_expressible_unconditional

/-- **Pillar 3.** Any locally confluent repair keeping the reflexive verdict
either refuses the diagonal difference edge or joins the two verdicts. -/
theorem repair_restriction_or_joinability
    {R : Trace → Trace → Prop} (a : Trace)
    (hrefl : R (Trace.eqW a a) Trace.void)
    (hlc : ∀ s t u, R s t → R s u → ConservativeRepair.JoinIn R t u) :
    (¬ R (Trace.eqW a a) (Trace.integrate (Trace.merge a a))) ∨
      ConservativeRepair.JoinIn R Trace.void (Trace.integrate (Trace.merge a a)) :=
  RepairCompleteness.repair_dichotomy a hrefl hlc

/-- **Pillar 4.** The reflexive `eqW` diagonal is the unique root confluence
obstruction of the kernel. -/
theorem ko7_distinction_boundary (a : Trace) :
    ¬ MetaSN_KO7.LocalJoinStep a ↔ CriticalPairCompleteness.IsEqWDiagonal a :=
  CriticalPairCompleteness.eqW_diagonal_is_the_unique_root_obstruction a

/-- **Pillar 5.** The guarded development is globally confluent. -/
theorem ko7_guarded_globally_confluent : MetaSN_KO7.ConfluentSafe :=
  GlobalConfluence.safeStep_globally_confluent

/-- **Pillar 5, surgical form.** The minimal repair `EqGuardedStep` is root
confluent. -/
theorem ko7_surgical_root_confluent : EqGuardedConfluence.ConfluentEqGuarded :=
  EqGuardedConfluence.confluentEqGuarded

/-- **Pillar 6, the unique check.** The guard the repair forces is not one
equality test among several: any two sound and complete comparators agree
pointwise, so the executable content of the guard is determined. -/
theorem the_check_is_unique {c1 c2 : Trace -> Trace -> Bool}
    (h1 : UniqueCheck.IsCheck c1) (h2 : UniqueCheck.IsCheck c2) (a b : Trace) :
    c1 a b = c2 a b :=
  UniqueCheck.check_unique_pointwise h1 h2 a b

/-- **Pillar 7, the injectivity barrier.** A comparator reading its arguments
through an abstraction is a check only when that abstraction is injective, so
no finite-state, bounded-depth, or hashed realisation is a check on the
infinite carrier. -/
theorem the_check_tolerates_no_loss {beta : Type} {h : Trace -> beta}
    {c' : beta -> beta -> Bool}
    (hc : UniqueCheck.IsCheck (fun a b : Trace => c' (h a) (h b))) :
    Function.Injective h :=
  UniqueCheck.factored_check_forces_injective hc

/-- Schema-first minimal obstruction crown, re-exported through the public
capstone without weakening its exact theorem-bearing record type. -/
def schema_first_minimal_distinction_crown :=
  OperatorKO7.Meta.DistinctionBoundary.MinimalFork.minimal_distinction_boundary_crown

/-- The public universal embedding statement, with terminality and determined-
diagonal hypotheses visible at the call site. -/
def schema_first_exact_diagonal_contains_fork3 :=
  @OperatorKO7.Meta.DistinctionBoundary.MinimalFork.API.distinction_exact_schema_contains_fork3

/-- The public root/context scope wall for the minimal comparator. -/
def schema_first_guarded_root_vs_context_scope :=
  OperatorKO7.Meta.DistinctionBoundary.MinimalFork.API.distinction_guarded_root_vs_context_scope

/-- The public one-bit terminal-support theorem. Its type is structural and
contains no thermodynamic energy quantity. -/
def schema_first_one_bit_terminal_collapse :=
  OperatorKO7.Meta.DistinctionBoundary.MinimalFork.API.distinction_one_bit_terminal_collapse

/-- **The one-check boundary.** The five legs together: forced, unique,
lossless, unwritable in the native signature, purchasable by one comparator
extension. -/
theorem one_check_boundary :
    (∀ (R : Trace → Trace → Prop),
        ConservativeRepair.AdmissibleRepair R → ∀ a b : Trace,
          R (Trace.eqW a b) (Trace.integrate (Trace.merge a b)) ↔ a ≠ b) ∧
    (∀ (c₁ c₂ : Trace → Trace → Bool), UniqueCheck.IsCheck c₁ → UniqueCheck.IsCheck c₂ →
        ∀ a b, c₁ a b = c₂ a b) ∧
    (∀ {β : Type} (h : Trace → β) (c' : β → β → Bool),
        UniqueCheck.IsCheck (fun a b : Trace => c' (h a) (h b)) → Function.Injective h) ∧
    (¬ ∃ t : Meta.SafeStep.SigmaFreeAlgebra.SigmaTerm,
        ∀ a b : Meta.SafeStep.SigmaFreeAlgebra.SigmaTerm,
          (a ≠ b) ↔
            (Meta.SafeStep.SigmaFreeAlgebra.evalSigma a b t ≠
              Meta.SafeStep.SigmaFreeAlgebra.SigmaTerm.void)) ∧
    (UniqueCheck.IsCheck DiscriminatorExtension.structEq ∧
      ∀ (c : Trace → Trace → Bool), UniqueCheck.IsCheck c →
        ∀ a b, c a b = DiscriminatorExtension.structEq a b) :=
  UniqueCheck.one_check_boundary

end OperatorKO7.Meta.DistinctionBoundary.PublicCapstone
