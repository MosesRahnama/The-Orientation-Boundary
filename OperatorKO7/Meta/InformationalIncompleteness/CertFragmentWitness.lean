import OperatorKO7.Meta.InformationalIncompleteness.WitnessChannelBoundary

/-!
# Certified fragment as zero witness-channel deficit (Informational Incompleteness, Theorem 9.1)

`thm:cert-fragment-info` and `rem:fragment-complement`, at the certificate-interface
formulation the paper uses (`def:witness-info-inc`). A term in the certified
fragment is one for which a sound certificate exists at the certified order, i.e.
`HasWitness Tw x` holds at that order; its witness-channel deficit at that
interface is then zero. The orientation boundary is the complementary
positive-deficit region: a boundary term has no direct-whole witness (positive
direct deficit) yet may carry a transformed-call certificate (zero deficit at the
certified interface), which is the SafeStep escape of `rem:fragment-complement`.

## Audit slots

```
Relation: schema-level witness tower `SchemaWitnessTower S`; not a rewriting relation.
Closure:  not applicable (Prop-level predicate facts).
Trust:    kernel-only.
Scope:    every tower and instance, plus a non-vacuity witness configuration.
```
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.InformationalIncompleteness.CertFragmentWitness

open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.SchemaWitnessTower
open OperatorKO7.Meta.InformationalIncompleteness.WitnessChannelBoundary

variable {S : OperatorKO7.StepDuplicating.StepDuplicatingSchema}

/--
Proves: (`thm:cert-fragment-info`) a term in the certified fragment has zero
  witness-channel deficit at the certified interface. Membership in the fragment
  is `HasWitness Tw x ℓ` at the certified order `ℓ` (a sound certificate exists),
  and the witness-channel deficit at that interface is `¬ HasWitness Tw x ℓ`, so
  the deficit is excluded.
Does not prove: that any specific term is in the fragment; non-vacuity is
  recorded separately below.
Relation: schema-level witness tower.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `Tw`, `x`, and certified order `ℓ`.
-/
theorem cert_fragment_zero_deficit (Tw : SchemaWitnessTower S) (x : S.T)
    (ℓ : WLevel) (hcert : HasWitness Tw x ℓ) : ¬ ¬ HasWitness Tw x ℓ :=
  not_not_intro hcert

/--
Proves: (`rem:fragment-complement`) the certified fragment is the zero-deficit
  region and the orientation boundary is the positive-deficit region. For a
  boundary term with no direct-whole witness but a transformed-call certificate,
  the direct-interface deficit is positive (`witnessChannelDeficitPos`) while the
  certified (transformed-call) interface carries a witness (zero deficit). This is
  the SafeStep escape from the positive-deficit region into the zero-deficit
  region.
Does not prove: source-system strong normalisation; the certified witness is the
  certificate-interface hypothesis.
Relation: schema-level witness tower.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `Tw` and `x` in the boundary/escape configuration.
-/
theorem cert_fragment_complement (Tw : SchemaWitnessTower S) (x : S.T)
    (hno : ¬ HasWitness Tw x WLevel.directWhole)
    (hcert : HasWitness Tw x WLevel.transformedCall) :
    witnessChannelDeficitPos Tw x ∧ HasWitness Tw x WLevel.transformedCall :=
  ⟨hno, hcert⟩

/--
Proves: (Gate R5 non-vacuity) the certified-fragment / escape configuration is
  satisfiable. For any schema `S` and instance `x₀`, a schema-witness tower exists
  on which `x₀` has no direct-whole witness yet carries a transformed-call
  certificate, so `cert_fragment_complement` is non-vacuous.
Does not prove: that the canonical recursor realises this configuration; that is
  the published transformed-call witness of \cite{rahnama2026orientation}.
Relation: schema-level witness tower.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every schema `S` with an inhabited instance.
-/
theorem cert_fragment_nonvacuous
    (S : OperatorKO7.StepDuplicating.StepDuplicatingSchema) (x₀ : S.T) :
    ∃ Tw : SchemaWitnessTower S,
      ¬ HasWitness Tw x₀ WLevel.directWhole
        ∧ HasWitness Tw x₀ WLevel.transformedCall := by
  refine ⟨fun _ ℓ => ℓ = WLevel.transformedCall, ?_, ?_⟩
  · intro h
    have h' : WLevel.directWhole = WLevel.transformedCall := h
    exact absurd h' (by decide)
  · rfl

/-- Audit anchor for the certified-fragment witness surface. -/
def cert_fragment_witness_anchor : String :=
  "OperatorKO7.Meta.InformationalIncompleteness.CertFragmentWitness.cert_fragment_complement"

end OperatorKO7.Meta.InformationalIncompleteness.CertFragmentWitness
