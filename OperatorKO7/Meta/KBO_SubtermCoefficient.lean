import OperatorKO7.Meta.SymbolicComparatorBarrier_Weighted_Schema
import OperatorKO7.Meta.SymbolicComparatorBarrier

/-!
# KBO with Subterm Coefficients: Carrier and Trace Bridge

A Knuth-Bendix order with subterm coefficients assigns to every argument
position a coefficient at least one, weights a term by
`w(f) + Σᵢ cᵢ(f) · w(tᵢ)`, and replaces the occurrence-counting variable
condition by the coefficient-weighted count of
`Meta/SymbolicComparatorBarrier_Weighted_Schema.lean`.

This module carries a concrete admissible model on the duplicating schema
signature, an inhabited comparison relation whose every arm carries the weighted
variable condition, the carrier-specialized obstruction at the actual KO7
recursor-successor root step, and the trace-level bridge that mirrors
`KBOImpossible.no_kbo_orients_ko7_rec_succ_trace`.

Both wrapper coefficients are at least one, so the payload variable's weighted
count rises from `recur₂` to `wrap₁ + wrap₂ · recur₂ ≥ 1 + recur₂` across the
duplicating rule. No choice of coefficients avoids this, which is why the row is
a barrier and not an escape conditioned on a coefficient assignment.
-/

namespace OperatorKO7.KBOSubtermCoefficient

open OperatorKO7.SymbolicComparatorBarrier

/-- The four function symbols of the duplicating-rule schema signature. -/
inductive SchemaFunctionSymbol where
  | base | succ | wrap | recur
  deriving DecidableEq, Repr

/-- An admissible KBO with subterm coefficients on the schema signature. The
symbol weights, precedence, and zero-weight side condition are the standard
admissibility data; `coefficients` adds the per-argument multipliers, each at
least one. -/
structure SubtermCoefficientKBO where
  coefficients : SubtermCoefficients
  variableWeight : Nat
  variableWeight_pos : 0 < variableWeight
  symbolWeight : SchemaFunctionSymbol → Nat
  constantWeight_ge_variable : variableWeight ≤ symbolWeight .base
  precedenceRank : SchemaFunctionSymbol → Nat
  precedenceRank_injective :
    ∀ f g : SchemaFunctionSymbol, precedenceRank f = precedenceRank g → f = g
  zeroWeightOnlySucc : ∀ f, symbolWeight f = 0 → f = .succ
  zeroWeightSuccMaximal : symbolWeight .succ = 0 →
    ∀ f, f ≠ .succ → precedenceRank f < precedenceRank .succ

/-- Term weight with subterm coefficients: each argument's weight is multiplied
by that position's coefficient. -/
def subtermCoefficientWeight (K : SubtermCoefficientKBO) : STerm → Nat
  | .var _ => K.variableWeight
  | .base => K.symbolWeight .base
  | .succ t => K.symbolWeight .succ + K.coefficients.succ * subtermCoefficientWeight K t
  | .wrap x y =>
      K.symbolWeight .wrap + K.coefficients.wrap₁ * subtermCoefficientWeight K x
        + K.coefficients.wrap₂ * subtermCoefficientWeight K y
  | .recur bT sT nT =>
      K.symbolWeight .recur + K.coefficients.recur₁ * subtermCoefficientWeight K bT
        + K.coefficients.recur₂ * subtermCoefficientWeight K sT
        + K.coefficients.recur₃ * subtermCoefficientWeight K nT

/-- The coefficient-weighted variable condition of this model. -/
def WeightedVariableCondition (K : SubtermCoefficientKBO) (x y : STerm) : Prop :=
  ∀ v : SchemaVar,
    weightedCount K.coefficients.toCoefficientAssignment v y ≤
      weightedCount K.coefficients.toCoefficientAssignment v x

/-- Root-symbol predicate used by the precedence arm. -/
def STerm.matchesSymbol : STerm → SchemaFunctionSymbol → Prop
  | .base, .base => True
  | .succ _, .succ => True
  | .wrap _ _, .wrap => True
  | .recur _ _ _, .recur => True
  | _, _ => False

/-- Nonempty iteration of the unary schema symbol over a variable, the standard
zero-weight unary arm. -/
inductive SuccIterationOfVar (v : SchemaVar) : STerm → Prop
  | once : SuccIterationOfVar v (.succ (.var v))
  | more {t : STerm} : SuccIterationOfVar v t → SuccIterationOfVar v (.succ t)

/-- KBO with subterm coefficients on the schema signature: strict weight,
strict root precedence at equal weight, lexicographic extension at equal root
and weight, and the admissible zero-weight unary-variable arm. Every arm carries
the coefficient-weighted variable condition. -/
inductive SubtermCoefficientKBOGt (K : SubtermCoefficientKBO) : STerm → STerm → Prop
  | weight {x y : STerm}
      (variableCondition : WeightedVariableCondition K x y)
      (weightStrict : subtermCoefficientWeight K y < subtermCoefficientWeight K x) :
      SubtermCoefficientKBOGt K x y
  | unaryVariable {v : SchemaVar} {x : STerm}
      (variableCondition : WeightedVariableCondition K x (.var v))
      (iteration : SuccIterationOfVar v x)
      (zeroUnaryWeight : K.symbolWeight .succ = 0) :
      SubtermCoefficientKBOGt K x (.var v)
  | precedence {x y : STerm} {fx fy : SchemaFunctionSymbol}
      (variableCondition : WeightedVariableCondition K x y)
      (weightEqual : subtermCoefficientWeight K x = subtermCoefficientWeight K y)
      (rootX : STerm.matchesSymbol x fx) (rootY : STerm.matchesSymbol y fy)
      (precedenceStrict : K.precedenceRank fy < K.precedenceRank fx) :
      SubtermCoefficientKBOGt K x y
  | succLex {x y : STerm}
      (variableCondition : WeightedVariableCondition K (.succ x) (.succ y))
      (weightEqual : subtermCoefficientWeight K (.succ x) = subtermCoefficientWeight K (.succ y))
      (argumentStrict : SubtermCoefficientKBOGt K x y) :
      SubtermCoefficientKBOGt K (.succ x) (.succ y)
  | wrapLeftLex {x₁ x₂ y₁ y₂ : STerm}
      (variableCondition : WeightedVariableCondition K (.wrap x₁ x₂) (.wrap y₁ y₂))
      (weightEqual : subtermCoefficientWeight K (.wrap x₁ x₂) =
        subtermCoefficientWeight K (.wrap y₁ y₂))
      (argumentStrict : SubtermCoefficientKBOGt K x₁ y₁) :
      SubtermCoefficientKBOGt K (.wrap x₁ x₂) (.wrap y₁ y₂)
  | wrapRightLex {x₁ x₂ y₂ : STerm}
      (variableCondition : WeightedVariableCondition K (.wrap x₁ x₂) (.wrap x₁ y₂))
      (weightEqual : subtermCoefficientWeight K (.wrap x₁ x₂) =
        subtermCoefficientWeight K (.wrap x₁ y₂))
      (argumentStrict : SubtermCoefficientKBOGt K x₂ y₂) :
      SubtermCoefficientKBOGt K (.wrap x₁ x₂) (.wrap x₁ y₂)
  | recurFirstLex {b₁ s₁ n₁ b₂ s₂ n₂ : STerm}
      (variableCondition :
        WeightedVariableCondition K (.recur b₁ s₁ n₁) (.recur b₂ s₂ n₂))
      (weightEqual : subtermCoefficientWeight K (.recur b₁ s₁ n₁) =
        subtermCoefficientWeight K (.recur b₂ s₂ n₂))
      (argumentStrict : SubtermCoefficientKBOGt K b₁ b₂) :
      SubtermCoefficientKBOGt K (.recur b₁ s₁ n₁) (.recur b₂ s₂ n₂)
  | recurSecondLex {bT s₁ n₁ s₂ n₂ : STerm}
      (variableCondition :
        WeightedVariableCondition K (.recur bT s₁ n₁) (.recur bT s₂ n₂))
      (weightEqual : subtermCoefficientWeight K (.recur bT s₁ n₁) =
        subtermCoefficientWeight K (.recur bT s₂ n₂))
      (argumentStrict : SubtermCoefficientKBOGt K s₁ s₂) :
      SubtermCoefficientKBOGt K (.recur bT s₁ n₁) (.recur bT s₂ n₂)
  | recurThirdLex {bT sT n₁ n₂ : STerm}
      (variableCondition :
        WeightedVariableCondition K (.recur bT sT n₁) (.recur bT sT n₂))
      (weightEqual : subtermCoefficientWeight K (.recur bT sT n₁) =
        subtermCoefficientWeight K (.recur bT sT n₂))
      (argumentStrict : SubtermCoefficientKBOGt K n₁ n₂) :
      SubtermCoefficientKBOGt K (.recur bT sT n₁) (.recur bT sT n₂)

/-- Every comparison of this model satisfies the coefficient-weighted variable
condition. -/
theorem SubtermCoefficientKBOGt.variableCondition {K : SubtermCoefficientKBO}
    {x y : STerm} (h : SubtermCoefficientKBOGt K x y) :
    WeightedVariableCondition K x y := by
  cases h <;> assumption

/-! ## An inhabited model with genuinely non-unit coefficients -/

/-- Coefficients that are not all one, so the carrier is a subterm-coefficient
KBO and not the plain occurrence-counting KBO. -/
def sampleCoefficients : SubtermCoefficients where
  succ := 1
  wrap₁ := 2
  wrap₂ := 3
  recur₁ := 1
  recur₂ := 2
  recur₃ := 1
  succ_pos := by decide
  wrap₁_pos := by decide
  wrap₂_pos := by decide
  recur₁_pos := by decide
  recur₂_pos := by decide
  recur₃_pos := by decide

/-- Concrete admissible model: positive symbol weights, strict precedence, and
the sample coefficients. -/
def finiteSubtermCoefficientKBO : SubtermCoefficientKBO where
  coefficients := sampleCoefficients
  variableWeight := 1
  variableWeight_pos := by decide
  symbolWeight := fun _ => 1
  constantWeight_ge_variable := by decide
  precedenceRank
    | .base => 0
    | .succ => 1
    | .wrap => 2
    | .recur => 3
  precedenceRank_injective := by
    intro f g h
    cases f <;> cases g <;> simp_all
  zeroWeightOnlySucc := by
    intro f h
    simp at h
  zeroWeightSuccMaximal := by
    intro h
    simp at h

/-- The strict-weight arm is inhabited. -/
theorem finiteSubtermCoefficientKBO_orients_strictWeight_witness :
    SubtermCoefficientKBOGt finiteSubtermCoefficientKBO (.succ .base) .base := by
  apply SubtermCoefficientKBOGt.weight
  · intro v
    cases v <;> decide
  · decide

/-- The equal-weight precedence arm is inhabited: with `wrap₁ = 2` and
`wrap₂ = 3` the wrapper over two constants weighs `6`, matching five nested
unary symbols over the constant. -/
theorem finiteSubtermCoefficientKBO_orients_precedence_witness :
    SubtermCoefficientKBOGt finiteSubtermCoefficientKBO
      (.wrap .base .base) (.succ (.succ (.succ (.succ (.succ .base))))) := by
  apply SubtermCoefficientKBOGt.precedence (fx := .wrap) (fy := .succ)
  · intro v
    cases v <;> decide
  · decide
  · trivial
  · trivial
  · decide

/-! ## The carrier-specialized obstruction -/

/-- No admissible KBO with subterm coefficients orients the duplicating schema
rule, whatever the coefficients. -/
theorem subtermCoefficientKBO_no_schema_orientation (K : SubtermCoefficientKBO) :
    ¬ SubtermCoefficientKBOGt K dupSrc dupTgt := by
  intro h
  have hv := h.variableCondition SchemaVar.s
  have hlt := weightedCount_dup_payload_strict K.coefficients
  omega

/-- A carrier-specialized obstruction at the actual KO7 recursor-successor root
step, in the shape the coverage evidence ledger consumes. -/
structure SubtermCoefficientKBORecSuccObstruction (K : SubtermCoefficientKBO) : Prop where
  noSchemaOrientation : ¬ SubtermCoefficientKBOGt K dupSrc dupTgt
  weightedPayloadStrict :
    weightedCount K.coefficients.toCoefficientAssignment SchemaVar.s dupSrc <
      weightedCount K.coefficients.toCoefficientAssignment SchemaVar.s dupTgt
  sourceInstantiation :
    instantiate Trace.void Trace.void Trace.void dupSrc =
      Trace.recΔ Trace.void Trace.void (Trace.delta Trace.void)
  targetInstantiation :
    instantiate Trace.void Trace.void Trace.void dupTgt =
      Trace.app Trace.void (Trace.recΔ Trace.void Trace.void Trace.void)
  actualRootStep :
    Step (Trace.recΔ Trace.void Trace.void (Trace.delta Trace.void))
      (Trace.app Trace.void (Trace.recΔ Trace.void Trace.void Trace.void))

/-- No admissible KBO with subterm coefficients orients the KO7 duplicating
recursor-successor root rule. -/
theorem subtermCoefficientKBO_no_ko7_rec_succ (K : SubtermCoefficientKBO) :
    SubtermCoefficientKBORecSuccObstruction K where
  noSchemaOrientation := subtermCoefficientKBO_no_schema_orientation K
  weightedPayloadStrict := weightedCount_dup_payload_strict K.coefficients
  sourceInstantiation := instantiate_dupSrc _ _ _
  targetInstantiation := instantiate_dupTgt _ _ _
  actualRootStep := Step.R_rec_succ _ _ _

/-- Exact subterm-coefficient KBO row proposition. -/
abbrev SubtermCoefficientKBORowClaim : Prop :=
  ∀ K : SubtermCoefficientKBO, SubtermCoefficientKBORecSuccObstruction K

/-! ## Trace-level bridge -/

/-- Trace-level bridge for the KO7 `rec_succ` rule: a concrete comparator on
instantiated schema terms that satisfies the coefficient-weighted variable
condition cannot orient the concrete rule instance. This mirrors
`KBOImpossible.no_kbo_orients_ko7_rec_succ_trace` with the weighted count in
place of the occurrence count. -/
theorem no_subtermCoefficientKBO_orients_ko7_rec_succ_trace
    (C : SubtermCoefficients) (gtT : Trace → Trace → Prop) (bT sT nT : Trace)
    (hvar : ∀ {x y : STerm} {v : SchemaVar},
      gtT (instantiate bT sT nT x) (instantiate bT sT nT y) →
        weightedCount C.toCoefficientAssignment v y ≤
          weightedCount C.toCoefficientAssignment v x) :
    ¬ gtT (Trace.recΔ bT sT (Trace.delta nT)) (Trace.app sT (Trace.recΔ bT sT nT)) := by
  intro hgt
  have hs : weightedCount C.toCoefficientAssignment SchemaVar.s dupTgt ≤
      weightedCount C.toCoefficientAssignment SchemaVar.s dupSrc := by
    apply hvar (x := dupSrc) (y := dupTgt) (v := SchemaVar.s)
    simpa [instantiate_dupSrc, instantiate_dupTgt] using hgt
  have hlt := weightedCount_dup_payload_strict C
  omega

end OperatorKO7.KBOSubtermCoefficient
