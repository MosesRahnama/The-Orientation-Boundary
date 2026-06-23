import OperatorKO7.Meta.SchemaWitnessOrder

/-!
# Witness-channel coordinate of the orientation boundary (Informational Incompleteness, Theorem 6 / `thm:duality`)

Mechanizes the duality chain of `Rahnama_Informational_Incompleteness.tex`
`thm:duality`: on the canonical RDRS instance the following are equivalent
through definitional unfoldings,

  (1) `OB(t)`                               orientation-boundary predicate
  (2) no direct whole-term witness at `t`
  (3) the direct certificate interface `C0` is empty
  (4) the witness-channel deficit at `C0` is positive
  (5) the minimal witness order exceeds the direct level.

Only link (1)<->(2) carries content (the published biconditional
`SchemaWitnessTower.OB_iff_no_directWhole`); the remaining links are
definitional, so each bridge is `Iff.rfl` or that biconditional. This matches
the manuscript remark `rem:chained-defs` that the chain is a coordinate
identification, not a new theorem about the recursor.

## Audit slots

```
Relation: schema-level witness tower `SchemaWitnessTower S` over a
          `StepDuplicatingSchema` `S`; not a concrete Step / SafeStep / DPProblem.
Closure:  not applicable (Prop-level predicate equivalences).
Strategy: not applicable.
Trust:    kernel-only. No sorry/admit/axiom/native_decide/csimp/unsafe.
Scope:    every tower `Tw : SchemaWitnessTower S` and instance `x : S.T`.
```
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.InformationalIncompleteness.WitnessChannelBoundary

open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.SchemaWitnessTower

variable {S : OperatorKO7.StepDuplicating.StepDuplicatingSchema}

/--
Proves: (3) the direct certificate interface `C0` is empty at `x`, defined as
  the absence of a direct whole-term (`WLevel.directWhole`) witness. The direct
  interface is populated exactly by direct-whole witnesses, so emptiness is this
  negation.
Does not prove: emptiness of any other interface.
Relation: schema-level witness tower; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `Tw` and `x`.
-/
def directInterfaceEmpty (Tw : SchemaWitnessTower S) (x : S.T) : Prop :=
  ¬ HasWitness Tw x WLevel.directWhole

/--
Proves: (4) the witness-channel deficit at the direct interface is positive,
  i.e. the correct verdict has no direct-whole witness.
Does not prove: a quantitative Shannon deficit; this is the predicate form
  (`WitDef > 0` as the emptiness predicate of Definition `def:witness-info-inc`).
Relation: schema-level witness tower; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `Tw` and `x`.
-/
def witnessChannelDeficitPos (Tw : SchemaWitnessTower S) (x : S.T) : Prop :=
  ¬ HasWitness Tw x WLevel.directWhole

/--
Proves: (5) the minimal witness order exceeds the direct level
  (`kappa* (x) > directWhole`).
Does not prove: a finite numeric value of `kappa*`; this is the threshold form.
Relation: schema-level witness tower; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `Tw` and `x`.
-/
def minimalWitnessOrderGtDirect (Tw : SchemaWitnessTower S) (x : S.T) : Prop :=
  kappaGt Tw x WLevel.directWhole

/--
Proves: link (1)<->(3): the orientation boundary holds iff the direct
  certificate interface is empty. This is the only content-bearing link; it is
  the published biconditional `OB_iff_no_directWhole`.
Does not prove: semantic undecidability of the verdict.
Relation: schema-level witness tower.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `Tw` and `x`.
-/
theorem ob_iff_directInterfaceEmpty (Tw : SchemaWitnessTower S) (x : S.T) :
    OB Tw x ↔ directInterfaceEmpty Tw x :=
  OB_iff_no_directWhole Tw x

/--
Proves: link (3)<->(4): direct-interface emptiness equals positive
  witness-channel deficit (definitional).
Does not prove: any quantitative content.
Relation: schema-level witness tower.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `Tw` and `x`.
-/
theorem directInterfaceEmpty_iff_witnessChannelDeficitPos
    (Tw : SchemaWitnessTower S) (x : S.T) :
    directInterfaceEmpty Tw x ↔ witnessChannelDeficitPos Tw x :=
  Iff.rfl

/--
Proves: link (4)<->(5): positive witness-channel deficit equals
  `kappa* > directWhole`. Both unfold to "no direct-whole witness" via the
  published biconditional.
Does not prove: any quantitative content.
Relation: schema-level witness tower.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `Tw` and `x`.
-/
theorem witnessChannelDeficitPos_iff_minimalWitnessOrderGtDirect
    (Tw : SchemaWitnessTower S) (x : S.T) :
    witnessChannelDeficitPos Tw x ↔ minimalWitnessOrderGtDirect Tw x :=
  (OB_iff_no_directWhole Tw x).symm

/--
Proves: link (5)<->(1): `kappa* > directWhole` equals the orientation boundary
  (definitional; `OB` is by definition `kappaGt _ _ directWhole`).
Does not prove: anything beyond the definitional identity.
Relation: schema-level witness tower.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `Tw` and `x`.
-/
theorem minimalWitnessOrderGtDirect_iff_ob
    (Tw : SchemaWitnessTower S) (x : S.T) :
    minimalWitnessOrderGtDirect Tw x ↔ OB Tw x :=
  Iff.rfl

/--
Proves: the full witness-channel coordinate chain of `thm:duality` as the
  conjunction of the four bridge equivalences (1)<->(3)<->(4)<->(5)<->(1).
Does not prove: a new fact about the recursor; the chain is a coordinate
  identification (manuscript `rem:chained-defs`).
Relation: schema-level witness tower.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `Tw` and `x`.
-/
theorem witnessChannel_coordinate_of_OB
    (Tw : SchemaWitnessTower S) (x : S.T) :
    (OB Tw x ↔ directInterfaceEmpty Tw x) ∧
      (directInterfaceEmpty Tw x ↔ witnessChannelDeficitPos Tw x) ∧
        (witnessChannelDeficitPos Tw x ↔ minimalWitnessOrderGtDirect Tw x) ∧
          (minimalWitnessOrderGtDirect Tw x ↔ OB Tw x) :=
  ⟨ob_iff_directInterfaceEmpty Tw x,
    directInterfaceEmpty_iff_witnessChannelDeficitPos Tw x,
    witnessChannelDeficitPos_iff_minimalWitnessOrderGtDirect Tw x,
    minimalWitnessOrderGtDirect_iff_ob Tw x⟩

/-- Audit anchor for the witness-channel coordinate chain. -/
def witness_channel_boundary_anchor : String :=
  "OperatorKO7.Meta.InformationalIncompleteness.WitnessChannelBoundary.witnessChannel_coordinate_of_OB"

end OperatorKO7.Meta.InformationalIncompleteness.WitnessChannelBoundary
