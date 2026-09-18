import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.WitnessLanguageAdequacy

/-!
# Alternative carriers and prefix codes

An `AlternativeCarrier data` is a witness package containing a finite type, a
supplied equivalence with the reachable terminal support, supplied equalities
for two stored counts, and a supplied injective prefix-free code. Conditional
on such a package, the theorems identify each stored count with terminal
multiplicity. This file supplies no inhabitant of `AlternativeCarrier`.

## Formal scope

Relation: terminal support of the semantic scope relation.
Closure: reflexive-transitive reachability used by terminal support.
Trust: kernel-only finite cardinality and list-prefix reasoning.
Scope: consequences of a supplied carrier package for one finite semantic scope.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v w z

/-- `candidate` is a prefix of `word`. -/
def BitListPrefix (candidate word : List Bool) : Prop :=
  ∃ suffix, candidate ++ suffix = word

/-- A variable-length binary code is prefix-free on distinct inputs. -/
def IsPrefixFree {Alternative : Type z}
    (code : Alternative → List Bool) : Prop :=
  ∀ ⦃a b⦄, a ≠ b → ¬ BitListPrefix (code a) (code b)

/-- A finite carrier equipped with a supplied terminal-support equivalence, count equalities, and
an injective prefix-free binary code. -/
structure AlternativeCarrier
    {A : ARS.{u}} [Fintype A.Carrier]
    {Defect : Type v} {Action : Type w}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (data : SemanticConstructionData A Defect Action) where
  Alternative : Type z
  alternativeFintype : Fintype Alternative
  terminalEquiv :
    Alternative ≃ {x // x ∈ SemanticScope.terminalSupport data.scope}
  fixed_count_eq :
    data.fixedLengthAlternatives = Fintype.card Alternative
  prefix_count_eq :
    data.prefixCodeAlternatives = Fintype.card Alternative
  prefixCode : Alternative → List Bool
  prefixCode_injective : Function.Injective prefixCode
  prefixCode_prefixFree : IsPrefixFree prefixCode

attribute [instance] AlternativeCarrier.alternativeFintype

namespace AlternativeCarrier

variable {A : ARS.{u}} [Fintype A.Carrier]
variable {Defect : Type v} {Action : Type w}
variable [DecidableEq Defect] [Fintype Action] [DecidableEq Action]

/-- Uses the package's fixed-count equality and terminal equivalence to identify the stored count
with terminal multiplicity. -/
theorem fixed_count_eq_terminalMultiplicity
    {data : SemanticConstructionData A Defect Action}
    (carrier : AlternativeCarrier data) :
    data.fixedLengthAlternatives =
      SemanticScope.terminalMultiplicity data.scope := by
  rw [carrier.fixed_count_eq]
  calc
    Fintype.card carrier.Alternative =
        Fintype.card {x // x ∈ SemanticScope.terminalSupport data.scope} :=
      Fintype.card_congr carrier.terminalEquiv
    _ = (SemanticScope.terminalSupport data.scope).card := by simp
    _ = SemanticScope.terminalMultiplicity data.scope := rfl

/-- Uses the package's prefix-count equality and terminal equivalence to identify the stored count
with terminal multiplicity. -/
theorem prefix_count_eq_terminalMultiplicity
    {data : SemanticConstructionData A Defect Action}
    (carrier : AlternativeCarrier data) :
    data.prefixCodeAlternatives =
      SemanticScope.terminalMultiplicity data.scope := by
  rw [carrier.prefix_count_eq]
  calc
    Fintype.card carrier.Alternative =
        Fintype.card {x // x ∈ SemanticScope.terminalSupport data.scope} :=
      Fintype.card_congr carrier.terminalEquiv
    _ = (SemanticScope.terminalSupport data.scope).card := by simp
    _ = SemanticScope.terminalMultiplicity data.scope := rfl

#check @fixed_count_eq_terminalMultiplicity
#check @prefix_count_eq_terminalMultiplicity
#print axioms fixed_count_eq_terminalMultiplicity
#print axioms prefix_count_eq_terminalMultiplicity

end AlternativeCarrier
end OperatorKO7.Meta.LicensedBoundaryCalculus
