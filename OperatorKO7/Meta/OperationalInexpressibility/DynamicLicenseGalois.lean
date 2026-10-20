import OperatorKO7.Meta.DistinctionBoundary.WriteClosure
import OperatorKO7.Meta.OperationalInexpressibility.RuleInvariantGalois

/-!
# Dynamic license Galois connection: KO7 positional instances

The generic rule-invariant Galois connection (the preservation maps, the
antitone Galois law, the two closure operators, and the singleton and family
invariant repairs) lives in the rule-invariant Galois module, a module that imports
no OperatorKO7 module. Its declarations keep the namespace of this module, so
`OperatorKO7.Meta.OperationalInexpressibility.DynamicLicenseGalois.<name>`
names the same declaration before and after the split.

This module imports that carrier and states the equality-guarded KO7
positional repair. Its confluence theorem uses the complete positional peak
classification, not the unary preservation Galois law: the repair freezes
equality congruence and may add both application positions forced by
recursive-context selection.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.DynamicLicenseGalois

/-! ## Singleton invariant repair -/

open OperatorKO7
open OperatorKO7.EqGuardedConfluence
open OperatorKO7.Meta.DistinctionBoundary.FreezePositions
open OperatorKO7.Meta.DistinctionBoundary.WriteClosure

/-- The positional repair has the exact selected relation named in its type,
is confluent, retains every requested non-equality position, and is the least
such confluent extension. -/
theorem positional_confluenceRepair_universal (S : CtorPos → Prop) :
    (¬ confluenceRepair S .eqW)
      ∧ (∀ c, S c → c ≠ .eqW → confluenceRepair S c)
      ∧ (confluenceRepair S .recD → confluenceRepair S .appL)
      ∧ (confluenceRepair S .recD → confluenceRepair S .appR)
      ∧ ConfluentOnPos (confluenceRepair S) EqGuardedStep
      ∧ (∀ T : CtorPos → Prop,
        ConfluentOnPos T EqGuardedStep →
        (∀ c, S c → c ≠ .eqW → T c) →
        SelectionLE (confluenceRepair S) T) := by
  exact ⟨confluenceRepair_freezes_eqW S,
    confluenceRepair_extends_nonEqW S,
    (confluenceRepair_writeClosed S).1,
    (confluenceRepair_writeClosed S).2,
    confluenceRepair_confluent S,
    fun T hT hExt => confluenceRepair_least hT hExt⟩

/-- Equality-congruence exclusion alone does not ensure confluence: selecting
only the recursive context leaves both contractum application positions
frozen and realizes the compiled recursor peak. -/
theorem recDOnly_not_confluent :
    (¬ recDSeed .eqW) ∧
      ¬ ConfluentOnPos recDSeed EqGuardedStep := by
  exact ⟨fun h => CtorPos.noConfusion h, recDSeed_not_confluent⟩

end OperatorKO7.Meta.OperationalInexpressibility.DynamicLicenseGalois
