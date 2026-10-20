import OperatorKO7.Meta.SymbolicComparatorBarrier_Schema

/-!
# Coefficient-Weighted Variable-Condition Barrier: Schema Layer

The unweighted variable condition of `Meta/SymbolicComparatorBarrier_Schema.lean`
counts occurrences of a variable. Orderings with subterm coefficients count
occurrences weighted by the product of the argument coefficients along the path
from the root to the occurrence. This module carries that weighted count on the
primitive duplicating schema terms and shows that the weighted condition fails
for every coefficient assignment whose argument coefficients are all positive.

On `dupSrc = recur(b, s, succ n)` the variable `s` has weighted count
`recur₂`. On `dupTgt = wrap(s, recur(b, s, n))` it has weighted count
`wrap₁ + wrap₂ * recur₂`, which is at least `1 + recur₂` once both wrapper
coefficients are positive. Positivity of the two wrapper coefficients is what
carries the argument, and each of the two is shown load-bearing by an
assignment that drops it and satisfies the condition at every variable.
-/

namespace OperatorKO7.SymbolicComparatorBarrier

open SchemaVar

/-- Argument coefficients for the six argument positions of the duplicating
schema signature: one for the unary symbol, two for the wrapper, three for the
recursor. No positivity is imposed here, so the count recursion is available on
degenerate assignments as well. -/
structure CoefficientAssignment where
  succ : Nat
  wrap₁ : Nat
  wrap₂ : Nat
  recur₁ : Nat
  recur₂ : Nat
  recur₃ : Nat
  deriving DecidableEq, Repr

/-- Occurrences of `v`, each weighted by the product of the argument
coefficients on the path from the root. With every coefficient equal to `1`
this is `countVar`. -/
def weightedCount (A : CoefficientAssignment) (v : SchemaVar) : STerm → Nat
  | STerm.var w => if v = w then 1 else 0
  | STerm.base => 0
  | STerm.succ t => A.succ * weightedCount A v t
  | STerm.wrap x y => A.wrap₁ * weightedCount A v x + A.wrap₂ * weightedCount A v y
  | STerm.recur bT sT nT =>
      A.recur₁ * weightedCount A v bT + A.recur₂ * weightedCount A v sT
        + A.recur₃ * weightedCount A v nT

/-- Subterm coefficients in the sense of the ordering literature: every
argument coefficient is at least one. -/
structure SubtermCoefficients extends CoefficientAssignment where
  succ_pos : 1 ≤ toCoefficientAssignment.succ
  wrap₁_pos : 1 ≤ toCoefficientAssignment.wrap₁
  wrap₂_pos : 1 ≤ toCoefficientAssignment.wrap₂
  recur₁_pos : 1 ≤ toCoefficientAssignment.recur₁
  recur₂_pos : 1 ≤ toCoefficientAssignment.recur₂
  recur₃_pos : 1 ≤ toCoefficientAssignment.recur₃

theorem weightedCount_dupSrc_b (A : CoefficientAssignment) :
    weightedCount A b dupSrc = A.recur₁ := by
  simp [dupSrc, weightedCount]

theorem weightedCount_dupSrc_s (A : CoefficientAssignment) :
    weightedCount A s dupSrc = A.recur₂ := by
  simp [dupSrc, weightedCount]

theorem weightedCount_dupSrc_n (A : CoefficientAssignment) :
    weightedCount A n dupSrc = A.recur₃ * A.succ := by
  simp [dupSrc, weightedCount, Nat.mul_comm]

theorem weightedCount_dupTgt_b (A : CoefficientAssignment) :
    weightedCount A b dupTgt = A.wrap₂ * A.recur₁ := by
  simp [dupTgt, weightedCount]

theorem weightedCount_dupTgt_s (A : CoefficientAssignment) :
    weightedCount A s dupTgt = A.wrap₁ + A.wrap₂ * A.recur₂ := by
  simp [dupTgt, weightedCount]

theorem weightedCount_dupTgt_n (A : CoefficientAssignment) :
    weightedCount A n dupTgt = A.wrap₂ * A.recur₃ := by
  simp [dupTgt, weightedCount]

/-- A comparator carrying the coefficient-weighted variable condition for a
fixed assignment of subterm coefficients. -/
structure WeightedVariableConditionOrder (C : SubtermCoefficients) where
  gt : STerm → STerm → Prop
  variable_condition :
    ∀ {x y : STerm} {v : SchemaVar},
      gt x y →
        weightedCount C.toCoefficientAssignment v y ≤
          weightedCount C.toCoefficientAssignment v x

/-- The weighted count of the payload variable strictly increases across the
duplicating rule for every positive coefficient assignment. -/
theorem weightedCount_dup_payload_strict (C : SubtermCoefficients) :
    weightedCount C.toCoefficientAssignment s dupSrc <
      weightedCount C.toCoefficientAssignment s dupTgt := by
  rw [weightedCount_dupSrc_s, weightedCount_dupTgt_s]
  have hmul : C.toCoefficientAssignment.recur₂ ≤
      C.toCoefficientAssignment.wrap₂ * C.toCoefficientAssignment.recur₂ :=
    Nat.le_mul_of_pos_left _ C.wrap₂_pos
  have hw : 1 ≤ C.toCoefficientAssignment.wrap₁ := C.wrap₁_pos
  omega

theorem not_orients_dup_rule_weighted {C : SubtermCoefficients}
    (O : WeightedVariableConditionOrder C) : ¬ O.gt dupSrc dupTgt := by
  intro h
  have hle : weightedCount C.toCoefficientAssignment s dupTgt ≤
      weightedCount C.toCoefficientAssignment s dupSrc := O.variable_condition h
  have hlt := weightedCount_dup_payload_strict C
  omega

theorem no_subtermCoefficient_variable_condition_orients_dup_step :
    ¬ ∃ (C : SubtermCoefficients) (O : WeightedVariableConditionOrder C),
        O.gt dupSrc dupTgt := by
  rintro ⟨C, O, h⟩
  exact not_orients_dup_rule_weighted O h

/-! ## Positivity of the two wrapper coefficients is load-bearing -/

/-- Coefficients with the outer wrapper argument dropped. -/
def wrapFirstDegenerate : CoefficientAssignment where
  succ := 1
  wrap₁ := 0
  wrap₂ := 1
  recur₁ := 1
  recur₂ := 1
  recur₃ := 1

/-- Coefficients with the inner wrapper argument dropped. -/
def wrapSecondDegenerate : CoefficientAssignment where
  succ := 1
  wrap₁ := 1
  wrap₂ := 0
  recur₁ := 1
  recur₂ := 5
  recur₃ := 1

/-- Dropping `wrap₁` from the assignment lets the weighted condition hold at
every variable, so `wrap₁_pos` is consumed by the barrier and not decoration. -/
theorem wrapFirst_positivity_necessary :
    wrapFirstDegenerate.wrap₁ = 0 ∧
      ∀ v : SchemaVar,
        weightedCount wrapFirstDegenerate v dupTgt ≤
          weightedCount wrapFirstDegenerate v dupSrc := by
  refine ⟨rfl, ?_⟩
  intro v
  cases v <;> simp [wrapFirstDegenerate, dupSrc, dupTgt, weightedCount]

/-- Dropping `wrap₂` from the assignment lets the weighted condition hold at
every variable, so `wrap₂_pos` is consumed by the barrier and not decoration. -/
theorem wrapSecond_positivity_necessary :
    wrapSecondDegenerate.wrap₂ = 0 ∧
      ∀ v : SchemaVar,
        weightedCount wrapSecondDegenerate v dupTgt ≤
          weightedCount wrapSecondDegenerate v dupSrc := by
  refine ⟨rfl, ?_⟩
  intro v
  cases v <;> simp [wrapSecondDegenerate, dupSrc, dupTgt, weightedCount]

/-- With every coefficient equal to one the weighted count is the plain
occurrence count, so the unweighted barrier is the unit instance of this one. -/
def unitCoefficients : SubtermCoefficients where
  succ := 1
  wrap₁ := 1
  wrap₂ := 1
  recur₁ := 1
  recur₂ := 1
  recur₃ := 1
  succ_pos := Nat.le_refl 1
  wrap₁_pos := Nat.le_refl 1
  wrap₂_pos := Nat.le_refl 1
  recur₁_pos := Nat.le_refl 1
  recur₂_pos := Nat.le_refl 1
  recur₃_pos := Nat.le_refl 1

theorem weightedCount_of_all_one (A : CoefficientAssignment)
    (hsucc : A.succ = 1) (hwrap₁ : A.wrap₁ = 1) (hwrap₂ : A.wrap₂ = 1)
    (hrecur₁ : A.recur₁ = 1) (hrecur₂ : A.recur₂ = 1) (hrecur₃ : A.recur₃ = 1)
    (v : SchemaVar) (t : STerm) :
    weightedCount A v t = countVar v t := by
  induction t with
  | var w => simp [weightedCount, countVar]
  | base => simp [weightedCount, countVar]
  | succ t ih => simp [weightedCount, countVar, hsucc, ih]
  | wrap x y ihx ihy => simp [weightedCount, countVar, hwrap₁, hwrap₂, ihx, ihy]
  | recur bT sT nT ihb ihs ihn =>
      simp [weightedCount, countVar, hrecur₁, hrecur₂, hrecur₃, ihb, ihs, ihn]

theorem weightedCount_unitCoefficients (v : SchemaVar) (t : STerm) :
    weightedCount unitCoefficients.toCoefficientAssignment v t = countVar v t :=
  weightedCount_of_all_one _ rfl rfl rfl rfl rfl rfl v t

end OperatorKO7.SymbolicComparatorBarrier
