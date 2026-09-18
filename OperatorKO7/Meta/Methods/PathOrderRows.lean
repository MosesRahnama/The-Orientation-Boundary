import OperatorKO7.Meta.SymbolicComparatorBarrier_Weighted_Schema
import OperatorKO7.Meta.LPO_KO7
import OperatorKO7.Meta.BarrierPumpDischarge
import OperatorKO7.Meta.SafeStepCtx_Complexity_Cichon

/-!
# Carriers for the path-order rows of the RDRS coverage ledger (lane E1)

Eleven rows from the 76-row termination-method universe are reduced below to the method axioms
used by the KO7 verdict. Each ledger promotion must cite the corresponding row claim, its concrete
inhabitant or imported construction, and the adapter from the named method to this interface.

The KBO family shares one mechanism. Every variant, whether it adds an argument status, a
quasi-precedence with ordered-semiring weights, associative-commutative matching, ordinal weights,
an applicative encoding, or polynomial weight functions, keeps the coefficient-weighted variable
condition of `Meta/SymbolicComparatorBarrier_Weighted_Schema.lean`, and that condition alone
refuses the duplicating rule: the payload variable occurs once on the left and twice on the right,
so its weighted count strictly increases (`weightedCount_dup_payload_strict`). None of the extra
data touches the count, so none of it can help. `weightedSizeOrder` is the non-degenerate
inhabitant that keeps every claim from being vacuous.

The RPO family is the escape side. The KO7 path order of `Meta/LPO_KO7.lean` orients all eight
root rules and the full one-hole context closure with the precedence `recΔ` above `app`. The AC
row contains both the empty-theory LPO specialization and a nontrivial associative-commutative
equational reduction order whose strict part is the compiled polynomial rank. The permutation row
adds a nonidentity binary status. The fixed POP* safe/normal assignment is killed by duplication
of the safe step argument.

Relation: the schema duplicating rule `dupSrc → dupTgt`, and `Step` / `StepCtxFull` for the
escapes. Closure: root and full context.
External trust: none. Mathlib only.
-/

namespace OperatorKO7.Methods.PathOrderRows

open OperatorKO7
open OperatorKO7.SymbolicComparatorBarrier
open OperatorKO7.MetaLPO

/-- Function symbols of the schema signature, local to this module so that the ledger can import
it without a cycle. -/
inductive MethodSymbol where
  | base | succ | wrap | recur
  deriving DecidableEq, Repr

/-! ## The shared non-degenerate comparator -/

/-- Structural size of a schema term. -/
def stermSize : STerm → Nat
  | STerm.var _ => 1
  | STerm.base => 1
  | STerm.succ t => 1 + stermSize t
  | STerm.wrap x y => 1 + stermSize x + stermSize y
  | STerm.recur x y z => 1 + stermSize x + stermSize y + stermSize z

/-- The canonical comparator satisfying the coefficient-weighted variable condition: strictly
smaller size with no weighted variable count increasing. It is the witness that every row claim
below is a statement about a real order and not about an empty one. -/
def weightedSizeOrder (C : SubtermCoefficients) : WeightedVariableConditionOrder C where
  gt := fun x y =>
    (∀ v : SchemaVar,
        weightedCount C.toCoefficientAssignment v y ≤
          weightedCount C.toCoefficientAssignment v x)
      ∧ stermSize y < stermSize x
  variable_condition := fun h => h.1 _

/-- The comparator is not empty: it compares `succ base` with `base`. -/
theorem weightedSizeOrder_nondegenerate (C : SubtermCoefficients) :
    (weightedSizeOrder C).gt (STerm.succ STerm.base) STerm.base := by
  refine ⟨fun v => ?_, by simp [stermSize]⟩
  simp [weightedCount]

/-! ## KBO row carriers -/

/-- Argument status for a symbol: lexicographic or multiset. -/
inductive ArgStatus where
  | lex
  | mul
  deriving DecidableEq, Repr

/-- **kboWithStatus.** A coefficient-weighted comparator together with an argument status
assignment. Status refines the tie-break after the weight and precedence comparisons, so it is
extra data on the same carrier. -/
structure KBOWithStatusOrder : Type where
  coefficients : SubtermCoefficients
  status : MethodSymbol → ArgStatus
  order : WeightedVariableConditionOrder coefficients

abbrev KBOWithStatusRowClaim : Prop :=
  ∀ O : KBOWithStatusOrder, ¬ O.order.gt dupSrc dupTgt

theorem kboWithStatus_row_anchor : KBOWithStatusRowClaim :=
  fun O => not_orients_dup_rule_weighted O.order

/-- Non-vacuity: a lexicographic-status order exists. -/
def kboWithStatusWitness : KBOWithStatusOrder where
  coefficients := unitCoefficients
  status := fun _ => ArgStatus.lex
  order := weightedSizeOrder unitCoefficients

/-- **generalizedKBO.** Weights in an ordered commutative semiring and a quasi-precedence, which
may identify symbols. Neither field enters the variable condition. -/
structure GeneralizedKBOOrder (K : Type) [CommSemiring K] [PartialOrder K] : Type where
  coefficients : SubtermCoefficients
  weight : MethodSymbol → K
  quasiPrecedence : MethodSymbol → Nat
  order : WeightedVariableConditionOrder coefficients

abbrev GeneralizedKBORowClaim : Prop :=
  ∀ (K : Type) (_ : CommSemiring K) (_ : PartialOrder K),
    ∀ O : @GeneralizedKBOOrder K _ _, ¬ O.order.gt dupSrc dupTgt

theorem generalizedKBO_row_anchor : GeneralizedKBORowClaim :=
  fun _ _ _ O => not_orients_dup_rule_weighted O.order

/-- Non-vacuity: the natural-weight instance with a collapsing quasi-precedence. -/
def generalizedKBOWitness : @GeneralizedKBOOrder Nat _ _ where
  coefficients := unitCoefficients
  weight := fun _ => 1
  quasiPrecedence := fun _ => 0
  order := weightedSizeOrder unitCoefficients

/-! ### AC rearrangement leaves the variable counts alone -/

/-- One associative-commutative rearrangement of the wrapper symbol, closed under contexts. -/
inductive ACRearrange : STerm → STerm → Prop
  | commWrap (x y : STerm) : ACRearrange (STerm.wrap x y) (STerm.wrap y x)
  | assocWrap (x y z : STerm) :
      ACRearrange (STerm.wrap (STerm.wrap x y) z) (STerm.wrap x (STerm.wrap y z))
  | underSucc {x y : STerm} : ACRearrange x y → ACRearrange (STerm.succ x) (STerm.succ y)
  | underWrapLeft {x y : STerm} (z : STerm) :
      ACRearrange x y → ACRearrange (STerm.wrap x z) (STerm.wrap y z)
  | underWrapRight {x y : STerm} (z : STerm) :
      ACRearrange x y → ACRearrange (STerm.wrap z x) (STerm.wrap z y)
  | underRecur₁ {x y : STerm} (u v : STerm) :
      ACRearrange x y → ACRearrange (STerm.recur x u v) (STerm.recur y u v)
  | underRecur₂ {x y : STerm} (u v : STerm) :
      ACRearrange x y → ACRearrange (STerm.recur u x v) (STerm.recur u y v)
  | underRecur₃ {x y : STerm} (u v : STerm) :
      ACRearrange x y → ACRearrange (STerm.recur u v x) (STerm.recur u v y)

/-- **The AC variable-count invariant.** Rearranging the wrapper associatively or commutatively,
anywhere in a term, leaves every variable count unchanged. This is why the AC variable condition
refuses the duplicating rule for the same reason the syntactic one does. -/
theorem countVar_acRearrange {x y : STerm} (h : ACRearrange x y) (v : SchemaVar) :
    countVar v x = countVar v y := by
  induction h with
  | commWrap x y => simp [countVar]; omega
  | assocWrap x y z => simp [countVar]; omega
  | underSucc _ ih => simpa [countVar] using ih
  | underWrapLeft z _ ih => simp [countVar, ih]
  | underWrapRight z _ ih => simp [countVar, ih]
  | underRecur₁ u v _ ih => simp [countVar, ih]
  | underRecur₂ u v _ ih => simp [countVar, ih]
  | underRecur₃ u v _ ih => simp [countVar, ih]

/-- Rearrangement is invariant along finite chains too. -/
theorem countVar_acRearrange_star {x y : STerm}
    (h : Relation.ReflTransGen ACRearrange x y) (v : SchemaVar) :
    countVar v x = countVar v y := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (countVar_acRearrange hstep v)

/-- **acKBO.** An AC-compatible comparator: it satisfies the variable condition and is stable
under AC rearrangement of either side. -/
structure ACKBOOrder : Type where
  coefficients : SubtermCoefficients
  order : WeightedVariableConditionOrder coefficients
  acStable :
    ∀ {x x' y y' : STerm},
      Relation.ReflTransGen ACRearrange x x' → Relation.ReflTransGen ACRearrange y y' →
        order.gt x y → order.gt x' y'

abbrev ACKBORowClaim : Prop :=
  (∀ O : ACKBOOrder, ¬ O.order.gt dupSrc dupTgt) ∧
    (∀ {x y : STerm}, Relation.ReflTransGen ACRearrange x y → ∀ v, countVar v x = countVar v y)

theorem acKBO_row_anchor : ACKBORowClaim :=
  ⟨fun O => not_orients_dup_rule_weighted O.order,
    fun h v => countVar_acRearrange_star h v⟩

/-- Non-vacuity: the size comparator is AC-stable because AC rearrangement preserves both the
weighted counts and the size. -/
theorem stermSize_acRearrange {x y : STerm} (h : ACRearrange x y) : stermSize x = stermSize y := by
  induction h with
  | commWrap x y => simp [stermSize]; omega
  | assocWrap x y z => simp [stermSize]; omega
  | underSucc _ ih => simpa [stermSize] using ih
  | underWrapLeft z _ ih => simp [stermSize, ih]
  | underWrapRight z _ ih => simp [stermSize, ih]
  | underRecur₁ u v _ ih => simp [stermSize, ih]
  | underRecur₂ u v _ ih => simp [stermSize, ih]
  | underRecur₃ u v _ ih => simp [stermSize, ih]

theorem weightedCount_acRearrange_unit {x y : STerm}
    (h : Relation.ReflTransGen ACRearrange x y) (v : SchemaVar) :
    weightedCount unitCoefficients.toCoefficientAssignment v x =
      weightedCount unitCoefficients.toCoefficientAssignment v y := by
  rw [weightedCount_unitCoefficients, weightedCount_unitCoefficients]
  exact countVar_acRearrange_star h v

theorem stermSize_acRearrange_star {x y : STerm}
    (h : Relation.ReflTransGen ACRearrange x y) : stermSize x = stermSize y := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (stermSize_acRearrange hstep)

def acKBOWitness : ACKBOOrder where
  coefficients := unitCoefficients
  order := weightedSizeOrder unitCoefficients
  acStable := by
    intro x x' y y' hx hy hgt
    refine ⟨fun v => ?_, ?_⟩
    · rw [← weightedCount_acRearrange_unit hx v, ← weightedCount_acRearrange_unit hy v]
      exact hgt.1 v
    · rw [← stermSize_acRearrange_star hx, ← stermSize_acRearrange_star hy]
      exact hgt.2

/-- **transfiniteKBO.** Ordinal weights. The variable condition is unchanged. -/
structure TransfiniteKBOOrder : Type 1 where
  coefficients : SubtermCoefficients
  weight : MethodSymbol → Ordinal
  order : WeightedVariableConditionOrder coefficients

abbrev TransfiniteKBORowClaim : Prop :=
  ∀ O : TransfiniteKBOOrder, ¬ O.order.gt dupSrc dupTgt

theorem transfiniteKBO_row_anchor : TransfiniteKBORowClaim :=
  fun O => not_orients_dup_rule_weighted O.order

noncomputable def transfiniteKBOWitness : TransfiniteKBOOrder where
  coefficients := unitCoefficients
  weight := fun _ => Ordinal.omega0
  order := weightedSizeOrder unitCoefficients

/-! ### The applicative encoding preserves variable counts -/

/-- Applicative (lambda-free) terms over the schema signature: one binary application node and
nullary constants. -/
inductive AppTerm where
  | var : SchemaVar → AppTerm
  | const : MethodSymbol → AppTerm
  | app : AppTerm → AppTerm → AppTerm
  deriving DecidableEq, Repr

/-- Currying: every schema constructor becomes iterated application of its constant. -/
def curry : STerm → AppTerm
  | STerm.var v => AppTerm.var v
  | STerm.base => AppTerm.const MethodSymbol.base
  | STerm.succ t => AppTerm.app (AppTerm.const MethodSymbol.succ) (curry t)
  | STerm.wrap x y =>
      AppTerm.app (AppTerm.app (AppTerm.const MethodSymbol.wrap) (curry x)) (curry y)
  | STerm.recur x y z =>
      AppTerm.app (AppTerm.app (AppTerm.app (AppTerm.const MethodSymbol.recur) (curry x))
        (curry y)) (curry z)

def countVarApp (v : SchemaVar) : AppTerm → Nat
  | AppTerm.var w => if v = w then 1 else 0
  | AppTerm.const _ => 0
  | AppTerm.app x y => countVarApp v x + countVarApp v y

/-- Structural size on applicative terms. -/
def appTermSize : AppTerm → Nat
  | AppTerm.var _ => 1
  | AppTerm.const _ => 1
  | AppTerm.app x y => 1 + appTermSize x + appTermSize y

/-- **The applicative encoding is count preserving.** So the variable condition transports to the
lambda-free setting unchanged. -/
theorem countVarApp_curry (v : SchemaVar) (t : STerm) :
    countVarApp v (curry t) = countVar v t := by
  induction t with
  | var w => simp [curry, countVarApp, countVar]
  | base => simp [curry, countVarApp, countVar]
  | succ t ih => simp [curry, countVarApp, countVar, ih]
  | wrap x y ihx ihy => simp [curry, countVarApp, countVar, ihx, ihy]
  | recur x y z ihx ihy ihz =>
      simp [curry, countVarApp, countVar, ihx, ihy, ihz]

/-- **lambdaFreeKBO.** A strict, transitive, well-founded comparator on applicative terms
carrying the KBO variable condition.  The order laws are fields, so the universal obstruction is
about genuine reduction-order candidates rather than arbitrary predicates satisfying only one
side condition. -/
structure LambdaFreeKBOOrder : Type where
  gt : AppTerm → AppTerm → Prop
  variable_condition :
    ∀ {x y : AppTerm} {v : SchemaVar}, gt x y → countVarApp v y ≤ countVarApp v x
  transitive : Transitive gt
  wellFounded : WellFounded (fun y x => gt x y)

abbrev LambdaFreeKBORowClaim : Prop :=
  (∀ O : LambdaFreeKBOOrder, ¬ O.gt (curry dupSrc) (curry dupTgt)) ∧
    (∀ v t, countVarApp v (curry t) = countVar v t)

theorem lambdaFreeKBO_row_anchor : LambdaFreeKBORowClaim := by
  refine ⟨fun O h => ?_, countVarApp_curry⟩
  have hle := O.variable_condition (v := SchemaVar.s) h
  rw [countVarApp_curry, countVarApp_curry, countVar_dupSrc_s, countVar_dupTgt_s] at hle
  omega

/-- The concrete lambda-free KBO witness combines the variable condition with strict structural
size.  Its reverse is a subrelation of the natural-number measure order. -/
def lambdaFreeKBOWitness : LambdaFreeKBOOrder where
  gt := fun x y =>
    (∀ v, countVarApp v y ≤ countVarApp v x) ∧ appTermSize y < appTermSize x
  variable_condition := fun h => h.1 _
  transitive := by
    intro x y z hxy hyz
    exact ⟨fun v => (hyz.1 v).trans (hxy.1 v), hyz.2.trans hxy.2⟩
  wellFounded := by
    refine Subrelation.wf ?_
      (InvImage.wf appTermSize Nat.lt_wfRel.wf)
    intro y x h
    exact h.2

/-- The genuine lambda-free order is non-degenerate. -/
theorem lambdaFreeKBOWitness_nondegenerate :
    lambdaFreeKBOWitness.gt
      (AppTerm.app (AppTerm.const MethodSymbol.succ) (AppTerm.const MethodSymbol.base))
      (AppTerm.const MethodSymbol.base) := by
  refine ⟨fun v => ?_, by simp [appTermSize]⟩
  simp [countVarApp]

/-- **polynomialKBO.** KBO with polynomial weight functions per symbol. The weights are data on
the same coefficient-weighted carrier. -/
structure PolynomialKBOOrder : Type where
  coefficients : SubtermCoefficients
  weightPoly : MethodSymbol → Nat → Nat
  order : WeightedVariableConditionOrder coefficients

abbrev PolynomialKBORowClaim : Prop :=
  ∀ O : PolynomialKBOOrder, ¬ O.order.gt dupSrc dupTgt

theorem polynomialKBO_row_anchor : PolynomialKBORowClaim :=
  fun O => not_orients_dup_rule_weighted O.order

def polynomialKBOWitness : PolynomialKBOOrder where
  coefficients := unitCoefficients
  weightPoly := fun _ k => k * k + 1
  order := weightedSizeOrder unitCoefficients

/-! ## The RPO family: escapes carried by the KO7 path order -/

/-- The exported KO7 path order itself, not merely the rewrite relation it orients, is
well-founded in the descending direction. -/
theorem lpoOrder_KO7_wellFounded :
    WellFounded (fun y x : Trace => LPOOrder_KO7 x y) :=
  InvImage.wf encode OperatorKO7.LPOSchema.lpoOrder_wellFounded

/-- An equational path-order certificate.  Stability is stated on both arguments, so a future
nontrivial AC quotient cannot be smuggled in by merely adding an unused field. -/
structure EquationalPathOrderCertificate where
  equiv : Trace → Trace → Prop
  gt : Trace → Trace → Prop
  equiv_refl : Reflexive equiv
  equiv_symm : Symmetric equiv
  equiv_trans : Transitive equiv
  gt_trans : Transitive gt
  gt_wellFounded : WellFounded (fun y x => gt x y)
  gt_left_stable : ∀ {x x' y}, equiv x x' → gt x y → gt x' y
  gt_right_stable : ∀ {x y y'}, equiv y y' → gt x y → gt x y'
  orients_root : ∀ {a b}, Step a b → gt a b
  orients_context : ∀ {a b}, MetaSN_KO7.StepCtxFull a b → gt a b

/-! ### A nontrivial associative-commutative equational order -/

/-- One associative-commutative rearrangement of the binary `app` constructor, closed under every
trace context. -/
inductive TraceAppACOne : Trace → Trace → Prop
  | comm (x y : Trace) : TraceAppACOne (.app x y) (.app y x)
  | assoc (x y z : Trace) :
      TraceAppACOne (.app (.app x y) z) (.app x (.app y z))
  | delta {x y : Trace} : TraceAppACOne x y → TraceAppACOne (.delta x) (.delta y)
  | integrate {x y : Trace} : TraceAppACOne x y → TraceAppACOne (.integrate x) (.integrate y)
  | mergeLeft {x y : Trace} (z : Trace) :
      TraceAppACOne x y → TraceAppACOne (.merge x z) (.merge y z)
  | mergeRight (z : Trace) {x y : Trace} :
      TraceAppACOne x y → TraceAppACOne (.merge z x) (.merge z y)
  | appLeft {x y : Trace} (z : Trace) :
      TraceAppACOne x y → TraceAppACOne (.app x z) (.app y z)
  | appRight (z : Trace) {x y : Trace} :
      TraceAppACOne x y → TraceAppACOne (.app z x) (.app z y)
  | recurBase {x y : Trace} (s n : Trace) :
      TraceAppACOne x y → TraceAppACOne (.recΔ x s n) (.recΔ y s n)
  | recurStep (b : Trace) {x y : Trace} (n : Trace) :
      TraceAppACOne x y → TraceAppACOne (.recΔ b x n) (.recΔ b y n)
  | recurCounter (b s : Trace) {x y : Trace} :
      TraceAppACOne x y → TraceAppACOne (.recΔ b s x) (.recΔ b s y)
  | eqLeft {x y : Trace} (z : Trace) :
      TraceAppACOne x y → TraceAppACOne (.eqW x z) (.eqW y z)
  | eqRight (z : Trace) {x y : Trace} :
      TraceAppACOne x y → TraceAppACOne (.eqW z x) (.eqW z y)

/-- The polynomial termination rank is invariant under one AC rearrangement. -/
theorem W_traceAppACOne {x y : Trace} (h : TraceAppACOne x y) :
    OperatorKO7.PolyInterpretation.W x = OperatorKO7.PolyInterpretation.W y := by
  induction h <;> simp_all [OperatorKO7.PolyInterpretation.W] <;> omega

/-- The full app-AC equivalence closure. -/
abbrev TraceAppAC : Trace → Trace → Prop := Relation.EqvGen TraceAppACOne

theorem W_traceAppAC {x y : Trace} (h : TraceAppAC x y) :
    OperatorKO7.PolyInterpretation.W x = OperatorKO7.PolyInterpretation.W y := by
  induction h with
  | rel _ _ hxy => exact W_traceAppACOne hxy
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- The AC theory is nontrivial on concrete traces. -/
theorem traceAppAC_nontrivial :
    TraceAppAC (.app .void (.delta .void)) (.app (.delta .void) .void)
      ∧ (.app .void (.delta .void) : Trace) ≠ .app (.delta .void) .void := by
  constructor
  · exact Relation.EqvGen.rel _ _ (TraceAppACOne.comm .void (.delta .void))
  · simp

/-- A nontrivial app-AC compatible reduction order. Its strict part is the polynomial order that
already orients every root and contextual KO7 step. -/
def ko7AppACReductionOrder : EquationalPathOrderCertificate where
  equiv := TraceAppAC
  gt := fun x y =>
    OperatorKO7.PolyInterpretation.W y < OperatorKO7.PolyInterpretation.W x
  equiv_refl := fun x => Relation.EqvGen.refl x
  equiv_symm := by
    intro x y h
    exact Relation.EqvGen.symm _ _ h
  equiv_trans := by
    intro x y z hxy hyz
    exact Relation.EqvGen.trans _ _ _ hxy hyz
  gt_trans := by
    intro x y z hxy hyz
    exact Nat.lt_trans hyz hxy
  gt_wellFounded :=
    InvImage.wf OperatorKO7.PolyInterpretation.W Nat.lt_wfRel.wf
  gt_left_stable := by
    intro x x' y hxx' hxy
    have hw := W_traceAppAC hxx'
    simpa [hw] using hxy
  gt_right_stable := by
    intro x y y' hyy' hxy
    have hw := W_traceAppAC hyy'
    simpa [hw] using hxy
  orients_root := OperatorKO7.PolyInterpretation.W_orients_step
  orients_context := MetaSN_KO7.W_orients_stepCtxFull

theorem ko7AppACReductionOrder_nontrivial :
    ko7AppACReductionOrder.equiv (.app .void (.delta .void)) (.app (.delta .void) .void)
      ∧ (.app .void (.delta .void) : Trace) ≠ .app (.delta .void) .void :=
  traceAppAC_nontrivial

/-- The exact empty-theory specialization of equational RPO. -/
def ko7EmptyEquationalRPO : EquationalPathOrderCertificate where
  equiv := Eq
  gt := LPOOrder_KO7
  equiv_refl := fun _ => rfl
  equiv_symm := by
    intro x y hxy
    exact hxy.symm
  equiv_trans := by
    intro x y z hxy hyz
    exact hxy.trans hyz
  gt_trans := OperatorKO7.MetaLPO.lpoOrder_KO7_transitive
  gt_wellFounded := lpoOrder_KO7_wellFounded
  gt_left_stable := by rintro _ _ _ rfl h; exact h
  gt_right_stable := by rintro _ _ _ rfl h; exact h
  orients_root := fun h => lpo_to_lpoOrder_KO7 (lpo_orients_all_root_rules h)
  orients_context := lpoOrder_orients_stepCtxFull

theorem ko7EmptyEquationalRPO_equiv_iff_eq (x y : Trace) :
    ko7EmptyEquationalRPO.equiv x y ↔ x = y := Iff.rfl

/-- **acRPO.** KO7 has the exact empty-theory LPO specialization and, separately, a nontrivial
app-AC compatible equational reduction order. The latter proves that the AC quotient itself is no
obstruction; no unformalized recursive-path-order metatheorem is used. -/
abbrev ACRPORowClaim : Prop :=
  Nonempty EquationalPathOrderCertificate
    ∧ ko7AppACReductionOrder.equiv
      (.app .void (.delta .void)) (.app (.delta .void) .void)
    ∧ (.app .void (.delta .void) : Trace) ≠ .app (.delta .void) .void
    ∧ (∀ {x y : Trace}, TraceAppAC x y →
      OperatorKO7.PolyInterpretation.W x = OperatorKO7.PolyInterpretation.W y)
    ∧ (∀ x y, ko7EmptyEquationalRPO.equiv x y ↔ x = y)
    ∧ cetaRank KO7Sym.app < cetaRank KO7Sym.recΔ
    ∧ (∀ {a b : Trace}, Step a b → LPO_KO7 a b)
    ∧ (∀ {a b : Trace}, MetaSN_KO7.StepCtxFull a b → LPOOrder_KO7 a b)
    ∧ WellFounded (fun y x : Trace => LPOOrder_KO7 x y)
    ∧ WellFounded (fun a b : Trace => MetaSN_KO7.StepCtxFull b a)
    ∧ (∀ (μ : Trace → Nat),
        (∀ {s u : Trace}, LPO_KO7 s u → μ u < μ s) →
          ¬ ∃ M : StepDuplicating.StepDuplicatingSchema.AffineMeasure
            OperatorKO7.CompositionalImpossibility.ko7Schema, M.eval = μ)

theorem acRPO_row_anchor : ACRPORowClaim :=
  ⟨⟨ko7AppACReductionOrder⟩,
    ko7AppACReductionOrder_nontrivial.1,
    ko7AppACReductionOrder_nontrivial.2,
    fun h => W_traceAppAC h,
    ko7EmptyEquationalRPO_equiv_iff_eq, by decide,
    lpo_orients_all_root_rules, lpoOrder_orients_stepCtxFull,
    lpoOrder_KO7_wellFounded, wf_StepCtxFull_via_lpo,
    fun μ h => lpo_not_direct_measure μ h⟩

/-- **rpoModuloPermutation.** A permutation status on each symbol's argument tuple. -/
structure PermutationStatus : Type where
  perm : (f : KO7Sym) → Equiv.Perm (Fin (ko7Arity f))

/-- The two arguments selected by a permutation status for the binary `app` constructor. -/
def permuteApp (σ : Equiv.Perm (Fin 2)) (x y : Trace) : Trace :=
  let arg : Fin 2 → Trace := fun i => if i = 0 then x else y
  .app (arg (σ 0)) (arg (σ 1))

/-- A permutation-modular RPO specialization binds the status to the equational theory: the
permuted `app` term must be equivalent to the original term.  Thus a nonidentity status cannot be
stored as an unused decoration beside an unrelated order. -/
structure PermutationRPOCertificate : Type where
  status : PermutationStatus
  order : EquationalPathOrderCertificate
  app_status_compatible : ∀ x y : Trace,
    order.equiv (.app x y) (permuteApp (status.perm .app) x y)

def identityPermutationStatus : PermutationStatus where
  perm := fun _ => Equiv.refl _

/-- The nontrivial transposition on the concrete binary `app` argument type. -/
def swapFin2 : Equiv.Perm (Fin 2) :=
Equiv.swap (0 : Fin 2) (1 : Fin 2)

/-- A genuinely nonidentity status: the two arguments of `app` are exchanged. -/
def swapAppPermutationStatus : PermutationStatus where
perm
| .void => Equiv.refl _
| .delta => Equiv.refl _
| .integrate => Equiv.refl _
    | .merge => Equiv.refl _
    | .app => swapFin2
| .recΔ => Equiv.refl _
  | .eqW => Equiv.refl _

/-- The dependent `app` branch is definitionally the concrete binary swap. -/
theorem swapAppPermutationStatus_app :
    swapAppPermutationStatus.perm .app = swapFin2 := rfl

@[simp] theorem swapFin2_moves_zero :
    swapFin2 (0 : Fin 2) = (1 : Fin 2) := by
  simp [swapFin2]

/-- Backward-compatible public anchor: the `app` status is exactly the binary
swap and that swap moves argument `0` to argument `1`. -/
theorem swapAppPermutationStatus_moves_zero :
    swapAppPermutationStatus.perm .app = swapFin2
      ∧ swapFin2 (0 : Fin 2) = (1 : Fin 2) :=
  ⟨swapAppPermutationStatus_app, swapFin2_moves_zero⟩

theorem swapFin2_nonidentity : swapFin2 ≠ Equiv.refl (Fin 2) := by
  intro h
  have h10 : (1 : Fin 2) = 0 := calc
    (1 : Fin 2) = swapFin2 0 := swapFin2_moves_zero.symm
    _ = (Equiv.refl (Fin 2)) 0 := by rw [h]
    _ = 0 := rfl
  exact (by decide : (1 : Fin 2) ≠ 0) h10

theorem swapAppPermutationStatus_nonidentity :
    swapAppPermutationStatus.perm .app ≠ Equiv.refl (Fin 2) := by
  rw [swapAppPermutationStatus_app]
  exact swapFin2_nonidentity

@[simp] theorem permuteApp_swap (x y : Trace) :
    permuteApp (Equiv.swap (0 : Fin 2) (1 : Fin 2)) x y = .app y x := by
  simp [permuteApp]

def ko7PermutationRPO : PermutationRPOCertificate where
  status := swapAppPermutationStatus
  order := ko7AppACReductionOrder
  app_status_compatible := by
    intro x y
    change TraceAppAC (.app x y) (permuteApp swapFin2 x y)
    simpa [swapFin2] using Relation.EqvGen.rel _ _ (TraceAppACOne.comm x y)

abbrev RPOModuloPermutationRowClaim : Prop :=
  Nonempty PermutationRPOCertificate
    ∧ ko7PermutationRPO.status.perm .app = swapFin2
    ∧ swapFin2 (0 : Fin 2) = (1 : Fin 2)
    ∧ ko7PermutationRPO.status.perm .app ≠ Equiv.refl (Fin 2)
    ∧ ko7PermutationRPO.order.equiv
      (.app .void (.delta .void)) (.app (.delta .void) .void)
    ∧ (∀ x y : Trace,
      ko7PermutationRPO.order.equiv (.app x y)
        (permuteApp (ko7PermutationRPO.status.perm .app) x y))
    ∧ ACRPORowClaim

theorem rpoModuloPermutation_row_anchor : RPOModuloPermutationRowClaim :=
  ⟨⟨ko7PermutationRPO⟩, swapAppPermutationStatus_app, swapFin2_moves_zero,
    swapAppPermutationStatus_nonidentity, ko7AppACReductionOrder_nontrivial.1,
    ko7PermutationRPO.app_status_compatible, acRPO_row_anchor⟩

/-! ### POP* : the safe/normal separation -/

/-- Argument classification for the polynomial path order: an argument position is either normal,
where recursion may descend, or safe, where values are carried without driving the recursion. -/
inductive ArgKind where
  | normal
  | safe
  deriving DecidableEq, Repr

/-- The KO7 separation: the recursor's counter is normal, its base and step arguments are safe,
and the wrapper's two arguments are safe. -/
def ko7ArgKind : KO7Sym → Nat → ArgKind
  | KO7Sym.recΔ, 2 => ArgKind.normal
  | KO7Sym.delta, 0 => ArgKind.normal
  | _, _ => ArgKind.safe

/-- Number of occurrences of a variable carried by a safe argument of the root symbol.  This is
the exact safe-use invariant needed by the KO7 duplicating rule: a whole subtree passed through a
safe root argument contributes all of its occurrences. -/
def rootSafeCount (v : SchemaVar) : STerm → Nat
  | STerm.var _ | STerm.base => 0
  | STerm.succ t =>
      if ko7ArgKind KO7Sym.delta 0 = ArgKind.safe then countVar v t else 0
  | STerm.wrap x y =>
      (if ko7ArgKind KO7Sym.app 0 = ArgKind.safe then countVar v x else 0) +
      (if ko7ArgKind KO7Sym.app 1 = ArgKind.safe then countVar v y else 0)
  | STerm.recur b s n =>
      (if ko7ArgKind KO7Sym.recΔ 0 = ArgKind.safe then countVar v b else 0) +
      (if ko7ArgKind KO7Sym.recΔ 1 = ArgKind.safe then countVar v s else 0) +
      (if ko7ArgKind KO7Sym.recΔ 2 = ArgKind.safe then countVar v n else 0)

/-- Root-safe variables may not be duplicated by a predicative safe-linear rule. -/
def PredicativeSafeLinear (source target : STerm) : Prop :=
  ∀ v : SchemaVar, rootSafeCount v target ≤ rootSafeCount v source

theorem rootSafeCount_dupSrc_s : rootSafeCount SchemaVar.s dupSrc = 1 := by
  simp [rootSafeCount, ko7ArgKind, dupSrc, countVar]

theorem rootSafeCount_dupTgt_s : rootSafeCount SchemaVar.s dupTgt = 2 := by
  simp [rootSafeCount, ko7ArgKind, dupTgt, countVar]

/-- The KO7 duplicating rule violates the safe-linearity condition itself; an unrelated path-order
escape cannot turn it into a POP* certificate. -/
theorem dup_rule_not_predicative_safe_linear : ¬ PredicativeSafeLinear dupSrc dupTgt := by
  intro h
  have hs := h SchemaVar.s
  rw [rootSafeCount_dupSrc_s, rootSafeCount_dupTgt_s] at hs
  omega

/-- The load-bearing POP* fragment for this row.  A certificate must validate safe-linearity on
the actual KO7 duplicating rule under the declared safe/normal assignment. -/
structure KO7POPStarCertificate : Type where
  safeLinearDup : PredicativeSafeLinear dupSrc dupTgt

/-- No certificate satisfying the declared POP* safe-linearity interface exists. -/
theorem no_ko7POPStarCertificate : ¬ Nonempty KO7POPStarCertificate := by
  rintro ⟨C⟩
  exact dup_rule_not_predicative_safe_linear C.safeLinearDup

/-- **popStarFamily.** The separation places the duplicated step argument in a safe position and
the counter in a normal one. A safe argument of the source appears twice on the right-hand side,
once directly under the wrapper and once under the recursive call. Hence the exact POP* fragment
used by the row has no certificate. Ordinary LPO remains a separate escape and is not evidence
for this method family. -/
abbrev PopStarFamilyRowClaim : Prop :=
  ko7ArgKind KO7Sym.recΔ 2 = ArgKind.normal
    ∧ ko7ArgKind KO7Sym.recΔ 1 = ArgKind.safe
    ∧ ko7ArgKind KO7Sym.app 0 = ArgKind.safe
    ∧ countVar SchemaVar.s dupSrc = 1
    ∧ countVar SchemaVar.s dupTgt = 2
    ∧ ¬ PredicativeSafeLinear dupSrc dupTgt
    ∧ ¬ Nonempty KO7POPStarCertificate

theorem popStarFamily_row_anchor : PopStarFamilyRowClaim :=
  ⟨rfl, rfl, rfl, countVar_dupSrc_s, countVar_dupTgt_s,
    dup_rule_not_predicative_safe_linear, no_ko7POPStarCertificate⟩

/-! ### Simple termination and the embedding -/

/-- **simpleTerminationOrderType.** Read a simplification order as a `Nat`-valued direct measure
on a step-duplicating schema. Inside the affine class the barrier is unconditional after the pump
discharge, and the embedding-domination property that makes the order a simplification order is
not an extra hypothesis: it follows from the class axioms `1 ≤ wrap_left` and `1 ≤ wrap_right`.
The row is therefore a CONTRACT whose contract clause is discharged, not assumed. -/
abbrev SimpleTerminationOrderTypeRowClaim : Prop :=
  (∀ (S : StepDuplicating.StepDuplicatingSchema)
      (M : StepDuplicating.StepDuplicatingSchema.AffineMeasure S),
      ¬ (∀ (b s n : S.T),
        M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))))
    ∧ (∀ (S : StepDuplicating.StepDuplicatingSchema)
        (M : StepDuplicating.StepDuplicatingSchema.AffineMeasure S) (x y : S.T),
        M.eval x + M.eval y ≤ M.eval (S.wrap x y))
    ∧ (∀ {a b : Trace}, MetaSN_KO7.StepCtxFull a b → LPOOrder_KO7 a b)
    ∧ WellFounded (fun y x : Trace => LPOOrder_KO7 x y)

theorem simpleTerminationOrderType_row_anchor : SimpleTerminationOrderTypeRowClaim := by
  refine ⟨fun S M =>
    StepDuplicating.StepDuplicatingSchema.no_affine_orients_dup_step M, ?_,
    lpoOrder_orients_stepCtxFull, lpoOrder_KO7_wellFounded⟩
  intro S M x y
  have hl := M.h_wrap_left_pos
  have hr := M.h_wrap_right_pos
  have hx : M.eval x ≤ M.wrap_left * M.eval x := Nat.le_mul_of_pos_left _ hl
  have hy : M.eval y ≤ M.wrap_right * M.eval y := Nat.le_mul_of_pos_left _ hr
  rw [M.eval_wrap]
  omega

/-! ### Cichon and the slow-growing bound -/

/-- **cichonSlowGrowing.** The ordinal ranking of the guarded contextual relation yields the
slow-growing bound already compiled in `Meta/SafeStepCtx_Complexity_Cichon.lean`: the ordinal
notation attached to a trace sits below `ω`, its Cichoń value bounds the contextual derivation
length, and the bound is the exponential wrapper over the same measure. The import the row depends
on is the ordinal ranking, and it is named here. -/
abbrev CichonSlowGrowingRowClaim : Prop :=
  (∀ t : Trace, NONote.repr (MetaSN_KO7.ctxExpNote t) < (Ordinal.omega0))
    ∧ (∀ t : Trace,
        MetaSN_KO7.contextualExpBound (MetaSN_KO7.termSize t) ≤ MetaSN_KO7.ctxExpCichonBound t)
    ∧ (∀ (t u : Trace) (n : Nat), MetaSN_KO7.SafeStepCtxPow n t u →
        n + 1 ≤ MetaSN_KO7.ctxExpCichonBound t)

theorem cichonSlowGrowing_row_anchor : CichonSlowGrowingRowClaim :=
  ⟨MetaSN_KO7.ctxExpNote_lt_omega,
    MetaSN_KO7.contextualExpBound_le_ctxExpCichonBound,
    MetaSN_KO7.safeStepCtx_length_le_ctxExpCichonBound⟩

end OperatorKO7.Methods.PathOrderRows
