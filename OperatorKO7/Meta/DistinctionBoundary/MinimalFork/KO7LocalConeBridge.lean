import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.UniversalEmbedding
import OperatorKO7.Meta.DistinctionBoundary.MinimalForkQuantitative
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone

/-!
# Exact local-cone bridge from the canonical `Fork3` to KO7

The theorem is deliberately local: it identifies the three marked states at
`eqW void void` and proves preservation/reflection of the restricted one-step
relations. It does not claim an equivalence of the entire KO7 carrier.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork

/-- Carrier equivalence between the two three-state local-cone presentations. -/
def fork3EquivKO7Node : Fork3 ≃ OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.EqWBreakerNode where
  toFun
    | .source => .source
    | .equal => .reflVerdict
    | .different => .diffVerdict
  invFun
    | .source => .source
    | .reflVerdict => .equal
    | .diffVerdict => .different
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x <;> rfl

/-- Raw local relations agree exactly under the carrier equivalence. -/
theorem fork3Step_iff_localRaw {x y : Fork3} :
    Fork3Step x y ↔ OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw (fork3EquivKO7Node x) (fork3EquivKO7Node y) := by
  cases x <;> cases y <;> constructor <;> intro h <;> cases h <;>
    first | exact OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw.refl | exact OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw.diff |
      exact Fork3Step.toEqual | exact Fork3Step.toDifferent

/-- Raw relation isomorphism to the existing KO7 local carrier. -/
def fork3LocalRawIso : RelIso Fork3Step OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw where
  toEquiv := fork3EquivKO7Node
  map_rel_iff := fork3Step_iff_localRaw

/-- Canonical map from `Fork3` into the live KO7 `Trace` carrier. -/
def fork3ToTrace (x : Fork3) : Trace := OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.embed (fork3EquivKO7Node x)

/-- The canonical map into `Trace` is injective. -/
theorem fork3ToTrace_injective : Function.Injective fork3ToTrace := by
  intro x y h
  apply fork3EquivKO7Node.injective
  exact OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.embed_injective h

/-- Raw canonical edges are exactly live kernel `Step` edges on the image. -/
theorem fork3Step_iff_ko7Step {x y : Fork3} :
    Fork3Step x y ↔ Step (fork3ToTrace x) (fork3ToTrace y) := by
  rw [fork3Step_iff_localRaw,
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.raw_step_iff]
  rfl

/-- Licensed relation agrees exactly with the existing KO7 local licensed relation. -/
theorem fork3LicensedStep_iff_localLicensed {x y : Fork3} :
    Fork3LicensedStep x y ↔
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalLicensed (fork3EquivKO7Node x) (fork3EquivKO7Node y) := by
  cases x <;> cases y <;> constructor <;> intro h <;> cases h <;>
    first | exact OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalLicensed.refl | exact Fork3LicensedStep.toEqual

/-- Licensed local relation isomorphism. -/
def fork3LocalLicensedIso : RelIso Fork3LicensedStep OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalLicensed where
  toEquiv := fork3EquivKO7Node
  map_rel_iff := fork3LicensedStep_iff_localLicensed

/-- Licensed canonical edges are exactly live `SafeStep` edges on the image. -/
theorem fork3LicensedStep_iff_ko7SafeStep {x y : Fork3} :
    Fork3LicensedStep x y ↔ MetaSN_KO7.SafeStep (fork3ToTrace x) (fork3ToTrace y) := by
  rw [fork3LicensedStep_iff_localLicensed,
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.licensed_step_iff]
  rfl

/-- Roadmap-stable licensed bridge name. The theorem states `SafeStep`
exactly and does not conflate it with the raw kernel relation. -/
theorem fork3LicensedStep_iff_safeStep {x y : Fork3} :
    Fork3LicensedStep x y ↔
      MetaSN_KO7.SafeStep (fork3ToTrace x) (fork3ToTrace y) :=
  fork3LicensedStep_iff_ko7SafeStep

/-- The KO7 raw diagonal cone is therefore relation-isomorphic—not merely
analogous—to the cardinality-minimal confluence obstruction. -/
theorem ko7_raw_local_cone_is_Fork3 :
    Nonempty (RelIso Fork3Step OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw) :=
  ⟨fork3LocalRawIso⟩

/-- The licensed KO7 local cone is the one-edge repair of the same carrier. -/
theorem ko7_licensed_local_cone_is_Fork3_repair :
    Nonempty (RelIso Fork3LicensedStep OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalLicensed) :=
  ⟨fork3LocalLicensedIso⟩

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge


