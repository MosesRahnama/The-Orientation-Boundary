import OperatorKO7.Kernel
import OperatorKO7.Meta.SafeStep_Core
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.Core
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.TerminalMultiplicity

/-!
# KO7 local equality-witness cone

Relation: `Step` and `MetaSN_KO7.SafeStep`, restricted to the three-node cone
at `eqW void void`.  Closure: generic exact-length `Reach` on the local carrier.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone

open OperatorKO7 Trace
open MetaSN_KO7

inductive EqWBreakerNode where
  | source
  | reflVerdict
  | diffVerdict
deriving DecidableEq, Fintype, Repr

def embed : EqWBreakerNode -> Trace
  | .source => eqW void void
  | .reflVerdict => void
  | .diffVerdict => integrate (merge void void)

inductive LocalRaw : EqWBreakerNode -> EqWBreakerNode -> Prop
  | refl : LocalRaw .source .reflVerdict
  | diff : LocalRaw .source .diffVerdict

inductive LocalLicensed : EqWBreakerNode -> EqWBreakerNode -> Prop
  | refl : LocalLicensed .source .reflVerdict

theorem embed_injective : Function.Injective embed := by
  intro x y h
  cases x <;> cases y <;> simp [embed] at h <;> rfl

theorem raw_step_iff {x y : EqWBreakerNode} :
    LocalRaw x y <-> Step (embed x) (embed y) := by
  constructor
  · intro h
    cases h with
    | refl => exact Step.R_eq_refl void
    | diff => exact Step.R_eq_diff void void
  · intro h
    cases x with
    | source =>
        cases y with
        | source => cases h
        | reflVerdict => exact LocalRaw.refl
        | diffVerdict => exact LocalRaw.diff
    | reflVerdict => cases h
    | diffVerdict => cases h

theorem licensed_step_iff {x y : EqWBreakerNode} :
    LocalLicensed x y <-> SafeStep (embed x) (embed y) := by
  constructor
  · intro h
    cases h
    exact SafeStep.R_eq_refl void (by simp [MetaSN_DM.kappaM])
  · intro h
    cases x with
    | source =>
        cases y with
        | source => cases h
        | reflVerdict => exact LocalLicensed.refl
        | diffVerdict =>
            cases h with
            | R_eq_diff _ _ hne => exact False.elim (hne rfl)
    | reflVerdict => cases h
    | diffVerdict => cases h

theorem licensed_subrelation : IsLicensedSubrelation LocalLicensed LocalRaw := by
  intro x y h
  cases h
  exact LocalRaw.refl

theorem raw_diagonal_peak :
    LocalRaw .source .reflVerdict /\ LocalRaw .source .diffVerdict :=
  And.intro LocalRaw.refl LocalRaw.diff

theorem licensed_diagonal_singleton {y : EqWBreakerNode}
    (h : LocalLicensed .source y) : y = .reflVerdict := by
  cases h
  rfl

#print axioms raw_step_iff
#print axioms licensed_step_iff
#print axioms raw_diagonal_peak
#print axioms licensed_diagonal_singleton

end OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone
