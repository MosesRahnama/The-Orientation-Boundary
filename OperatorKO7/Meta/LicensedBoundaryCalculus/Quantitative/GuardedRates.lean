import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.SemanticScope
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.FiniteDistinctionSurface

/-!
# Guarded quantitative observables

Rates and support-ratio entropies return `none` exactly when their sample space
is empty.  This removes totalized zero-denominator readings from theorem-facing
LBC APIs while preserving exact adapters to the existing Distinction surfaces.

## Audit slots

Relation: inherited from each semantic scope or finite distinction surface.
Closure: finite sample ratios and terminal-support ratios.
Trust: kernel-only arithmetic and classical finite enumeration.
Scope: guarded observables; no probabilistic interpretation is inferred.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- A rational rate exists exactly when its sample count is nonzero. -/
def guardedRate (hits samples : Nat) : Option Rat :=
  if samples = 0 then none else some (hits / samples)

theorem guardedRate_eq_none_iff (hits samples : Nat) :
    guardedRate hits samples = none ↔ samples = 0 := by
  unfold guardedRate
  by_cases h : samples = 0 <;> simp [h]

theorem guardedRate_eq_some_of_pos (hits samples : Nat) (hsamples : 0 < samples) :
    guardedRate hits samples = some (hits / samples : Rat) := by
  simp [guardedRate, hsamples.ne']

/-- A total extension choosing zero at empty support. -/
def zeroTotalizedRate (hits samples : Nat) : Rat :=
  if samples = 0 then 0 else hits / samples

/-- A second total extension choosing one at empty support. -/
def oneTotalizedRate (hits samples : Nat) : Rat :=
  if samples = 0 then 1 else hits / samples

/-- Agreement with the ordinary rate on every positive sample space. -/
def IsPositiveSampleRateExtension (rate : Nat -> Nat -> Rat) : Prop :=
  ∀ hits samples, 0 < samples ->
    rate hits samples = (hits / samples : Rat)

theorem zeroTotalizedRate_isExtension :
    IsPositiveSampleRateExtension zeroTotalizedRate := by
  intro hits samples hsamples
  simp [zeroTotalizedRate, hsamples.ne']

theorem oneTotalizedRate_isExtension :
    IsPositiveSampleRateExtension oneTotalizedRate := by
  intro hits samples hsamples
  simp [oneTotalizedRate, hsamples.ne']

/-- Positive-support laws leave the empty-support value underdetermined. -/
theorem totalizedRates_disagree_at_zero (hits : Nat) :
    zeroTotalizedRate hits 0 ≠ oneTotalizedRate hits 0 := by
  simp [zeroTotalizedRate, oneTotalizedRate]

/-- There is no unique total rate operation determined only by agreement on
positive sample spaces.  The option-valued boundary is therefore intrinsic. -/
theorem no_unique_total_rate_extension :
    ¬ (∃ rate : Nat -> Nat -> Rat,
      IsPositiveSampleRateExtension rate ∧
        ∀ other, IsPositiveSampleRateExtension other -> other = rate) := by
  rintro ⟨rate, _, hunique⟩
  have hzero := hunique zeroTotalizedRate zeroTotalizedRate_isExtension
  have hone := hunique oneTotalizedRate oneTotalizedRate_isExtension
  have heq : zeroTotalizedRate = oneTotalizedRate := hzero.trans hone.symm
  exact totalizedRates_disagree_at_zero 0 (congrFun (congrFun heq 0) 0)

/-- Scoped terminal-support collapse, absent unless both supports are inhabited. -/
noncomputable def structuralHartleyCollapse?
    {A : ARS.{u}} [Fintype A.Carrier]
    (raw licensed : SemanticScope A) : Option Real :=
  if SemanticScope.terminalMultiplicity raw = 0 then none
  else if SemanticScope.terminalMultiplicity licensed = 0 then none
  else
    some
      (Real.logb 2
        ((SemanticScope.terminalMultiplicity raw : Real) /
          (SemanticScope.terminalMultiplicity licensed : Real)))

theorem structuralHartleyCollapse?_eq_none_iff
    {A : ARS.{u}} [Fintype A.Carrier]
    (raw licensed : SemanticScope A) :
    structuralHartleyCollapse? raw licensed = none ↔
      SemanticScope.terminalMultiplicity raw = 0 ∨
        SemanticScope.terminalMultiplicity licensed = 0 := by
  unfold structuralHartleyCollapse?
  by_cases hraw : SemanticScope.terminalMultiplicity raw = 0
  · simp [hraw]
  · by_cases hlicensed : SemanticScope.terminalMultiplicity licensed = 0
    · simp [hraw, hlicensed]
    · simp [hraw, hlicensed]

theorem structuralHartleyCollapse?_eq_some_of_pos
    {A : ARS.{u}} [Fintype A.Carrier]
    (raw licensed : SemanticScope A)
    (hraw : 0 < SemanticScope.terminalMultiplicity raw)
    (hlicensed : 0 < SemanticScope.terminalMultiplicity licensed) :
    structuralHartleyCollapse? raw licensed =
      some
        (Real.logb 2
          ((SemanticScope.terminalMultiplicity raw : Real) /
            (SemanticScope.terminalMultiplicity licensed : Real))) := by
  simp [structuralHartleyCollapse?, hraw.ne', hlicensed.ne']

/-- Option-valued diagonal false-positive rate. -/
def diagonalFalsePositiveRate?
    {A : Type u} {V : Type v}
    [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
    (S : FiniteDistinctionSurface A V) : Option Rat :=
  guardedRate S.diagonalFalsePositive (Fintype.card A)

/-- Option-valued off-diagonal false-negative rate. -/
def offDiagonalFalseNegativeRate?
    {A : Type u} {V : Type v}
    [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
    (S : FiniteDistinctionSurface A V) : Option Rat :=
  guardedRate S.offDiagonalFalseNegative
    (Fintype.card A * (Fintype.card A - 1))

theorem diagonalFalsePositiveRate?_eq_some_guarded
    {A : Type u} {V : Type v}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype V] [DecidableEq V]
    (S : FiniteDistinctionSurface A V) :
    diagonalFalsePositiveRate? S =
      some (FiniteDistinctionSurface.diagonalFalsePositiveRateGuarded S) := by
  have hpos : 0 < Fintype.card A := Fintype.card_pos
  unfold diagonalFalsePositiveRate?
  rw [guardedRate_eq_some_of_pos _ _ hpos]
  unfold FiniteDistinctionSurface.diagonalFalsePositiveRateGuarded
  simp [hpos]

theorem offDiagonalFalseNegativeRate?_eq_some_guarded
    {A : Type u} {V : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype V] [DecidableEq V]
    (S : FiniteDistinctionSurface A V) (hcard : 2 ≤ Fintype.card A) :
    offDiagonalFalseNegativeRate? S =
      some (FiniteDistinctionSurface.offDiagonalFalseNegativeRateGuarded S hcard) := by
  have hden : 0 < Fintype.card A * (Fintype.card A - 1) :=
    FiniteDistinctionSurface.offDiagonal_denominator_pos hcard
  unfold offDiagonalFalseNegativeRate?
  rw [guardedRate_eq_some_of_pos _ _ hden]
  unfold FiniteDistinctionSurface.offDiagonalFalseNegativeRateGuarded
  have hone : 1 ≤ Fintype.card A := by omega
  simp [hcard, Nat.cast_sub hone]

/-- Local normalization makes the chain support ratio defined. -/
theorem chain_structuralHartleyCollapse_defined_fixture :
    ∃ h : Real,
      @structuralHartleyCollapse? chainARS_fixture
        (by change Fintype ChainNode; infer_instance)
        SemanticScope.chain_fixture SemanticScope.chain_fixture = some h := by
  letI : Fintype chainARS_fixture.Carrier := by
    change Fintype ChainNode
    infer_instance
  have hpos : 0 < SemanticScope.terminalMultiplicity SemanticScope.chain_fixture :=
    terminalMultiplicity_pos_of_normalizingAt SemanticScope.chain_normalizing_fixture
  exact
    ⟨Real.logb 2
      ((SemanticScope.terminalMultiplicity SemanticScope.chain_fixture : Real) /
        (SemanticScope.terminalMultiplicity SemanticScope.chain_fixture : Real)),
      structuralHartleyCollapse?_eq_some_of_pos _ _ hpos hpos⟩

#check guardedRate_eq_none_iff
#check no_unique_total_rate_extension
#check @structuralHartleyCollapse?_eq_none_iff
#check @diagonalFalsePositiveRate?_eq_some_guarded
#check @offDiagonalFalseNegativeRate?_eq_some_guarded
#check chain_structuralHartleyCollapse_defined_fixture
#print axioms guardedRate_eq_none_iff
#print axioms zeroTotalizedRate_isExtension
#print axioms oneTotalizedRate_isExtension
#print axioms totalizedRates_disagree_at_zero
#print axioms no_unique_total_rate_extension
#print axioms structuralHartleyCollapse?_eq_none_iff
#print axioms diagonalFalsePositiveRate?_eq_some_guarded
#print axioms offDiagonalFalseNegativeRate?_eq_some_guarded
#print axioms chain_structuralHartleyCollapse_defined_fixture

end OperatorKO7.Meta.LicensedBoundaryCalculus
