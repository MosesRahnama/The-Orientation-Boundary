import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.ReflectionInstanceBridge

/-!
# Cross-instance duck theorem

The standalone role-separated comparator and the equality-reflection comparator
have different ambient carriers and syntax. Their exact marked local reduction
cones are nevertheless relation-isomorphic because each is independently proved
isomorphic to the same canonical `Fork3` object.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork.CrossInstanceIsomorphism

open OperatorKO7.Meta.DistinctionBoundary.MinimalFork

/-- Exact relation isomorphism between the two independently built local cones. -/
noncomputable def classicLocalConeIsoReflectionLocalCone :
    RelIso
      (LocalConeStep OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.exactClassicFork OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0 OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.classic_terminalDiagonal)
      (LocalConeStep OperatorKO7.Meta.DistinctionBoundary.MinimalFork.ReflectionInstanceBridge.exactReflectionFork OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.base0 OperatorKO7.Meta.DistinctionBoundary.MinimalFork.ReflectionInstanceBridge.reflection_terminalDiagonal) :=
  OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.classicLocalConeIso.symm.trans OperatorKO7.Meta.DistinctionBoundary.MinimalFork.ReflectionInstanceBridge.reflectionLocalConeIso

/-- The cross-instance isomorphism is a genuine carrier equivalence. -/
theorem crossInstance_carrier_bijective :
    Function.Bijective classicLocalConeIsoReflectionLocalCone.toEquiv :=
  classicLocalConeIsoReflectionLocalCone.toEquiv.bijective

/-- Edge preservation and reflection are both present, not merely an analogy. -/
theorem crossInstance_relation_iff
    {x y : LocalConeCarrier OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.exactClassicFork OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0 OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.classic_terminalDiagonal} :
    LocalConeStep OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.exactClassicFork OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0 OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.classic_terminalDiagonal x y ↔
      LocalConeStep OperatorKO7.Meta.DistinctionBoundary.MinimalFork.ReflectionInstanceBridge.exactReflectionFork OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.base0 OperatorKO7.Meta.DistinctionBoundary.MinimalFork.ReflectionInstanceBridge.reflection_terminalDiagonal
        (classicLocalConeIsoReflectionLocalCone.toEquiv x)
        (classicLocalConeIsoReflectionLocalCone.toEquiv y) :=
  classicLocalConeIsoReflectionLocalCone.map_rel_iff

/-- Both independent instances and `Fork3` therefore realize the same marked
nonjoinable one-step obstruction up to relation isomorphism. -/
theorem independent_instances_share_Fork3_obstruction :
    Nonempty
      (RelIso
        (LocalConeStep OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.exactClassicFork OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0 OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.classic_terminalDiagonal)
        (LocalConeStep OperatorKO7.Meta.DistinctionBoundary.MinimalFork.ReflectionInstanceBridge.exactReflectionFork OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.base0 OperatorKO7.Meta.DistinctionBoundary.MinimalFork.ReflectionInstanceBridge.reflection_terminalDiagonal)) :=
  ⟨classicLocalConeIsoReflectionLocalCone⟩

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork.CrossInstanceIsomorphism

