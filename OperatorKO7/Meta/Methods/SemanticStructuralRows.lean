import OperatorKO7.Meta.Step_Complexity_LowerBound
import OperatorKO7.Meta.NonlinearUnconstrainedExactLaw
import OperatorKO7.Meta.BarrierPumpDischarge
import OperatorKO7.Meta.SymbolicComparatorBarrier_Weighted_Schema
import OperatorKO7.Meta.PolyInterpretation_FullStep

/-!
# Carriers for the semantic and structural rows of the RDRS coverage ledger (lane E3)

Twelve rows sit in the semantic and structural layer: extended monotone algebras, finite-model
termination, the three match-bound rows, the four labelling rows, and the three rows whose content
is that the method has no carrier on `Trace` at all.

Three mechanisms carry the whole lane.

**Pigeonhole.** A finite carrier cannot host the doubling chain: a strictly increasing sequence in
a `Fintype` is injective and therefore bounded by the cardinality, so `finiteModelTermination` is a
theorem and not a heuristic.

**The single-exponential lower family.** `Meta/Step_Complexity_LowerBound.lean` exhibits a family
of KO7 terms whose contextual derivation length exceeds any linear function of the term size. Every
match-bound method certifies a linear derivational complexity, so the transport is the
contrapositive: the method cannot apply to this system. The linear-complexity theorem for
match-bounded systems is EXTERNAL; the transport and the lower family are compiled.

**Labelling has an exact boundary.** A labelling replaces each symbol by a labelled copy and does
not change the arity or the number of occurrences of a variable in a right-hand side. Hence every
variable-condition comparator that factors through label erasure still refuses the duplicating
rule. This is sharp: a concrete constructor-sensitive labelling carries a well-founded root-label
order that orients the labelled schema rule. Thus erasure-factored barriers lift, while genuinely
label-sensitive orders can escape.

Relation: the schema duplicating rule and `StepCtxFull`. Closure: root and full context.
External trust: the match-bound linear-complexity theorem, cited in the row docstrings.
-/

namespace OperatorKO7.Methods.SemanticStructuralRows

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.SymbolicComparatorBarrier

/-! ## Extended monotone algebras -/

/-- A weak/strict pair in the extended-monotone-algebra sense: a reflexive transitive weak
relation, a strict relation compatible with it, and a measure whose wrapper keeps both arguments
and whose counter gain is bounded. -/
structure ExtendedMonotoneAlgebra (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  weak : Nat → Nat → Prop
  strict : Nat → Nat → Prop
  weak_refl : ∀ a, weak a a
  strict_to_lt : ∀ {a b}, strict a b → a < b
  wrapCost : Nat
  wrap_keeps_arguments : ∀ x y, wrapCost + eval x + eval y ≤ eval (S.wrap x y)
  succGain : Nat
  counter_gain : ∀ b s n, eval (S.recur b s (S.succ n)) ≤ succGain + eval (S.recur b s n)

/-- **extendedMonotoneAlgebra.** CONTRACT: under the row's condition, that the strict relation of
the pair refines the numeric order, the barrier holds. The condition is what makes the pair an
algebra rather than an arbitrary relation, and it is consumed by the proof. -/
abbrev ExtendedMonotoneAlgebraRowClaim : Prop :=
  ∀ (S : StepDuplicatingSchema) (A : ExtendedMonotoneAlgebra S),
    ¬ (∀ (b s n : S.T),
      A.strict (A.eval (S.wrap s (S.recur b s n))) (A.eval (S.recur b s (S.succ n))))

theorem extendedMonotoneAlgebra_row_anchor : ExtendedMonotoneAlgebraRowClaim := by
  intro S A h
  exact no_unconstrainedDirect_orients_dup_step
    { eval := A.eval
      wrapCost := A.wrapCost
      wrap_keeps_arguments := A.wrap_keeps_arguments
      succGain := A.succGain
      counter_gain := A.counter_gain
      }
    (fun b s n => A.strict_to_lt (h b s n))

/-! ## Finite models -/

/-- A finite-model interpretation: a `Fintype` carrier with a numeric ranking whose wrapper
strictly increases the rank of its right argument. No injectivity or global monotonicity premise is
needed. -/
structure FiniteModelInterpretation (S : StepDuplicatingSchema) (α : Type) [Fintype α] where
  eval : S.T → α
  rank : α → Nat
  wrap_strict : ∀ x y, rank (eval y) < rank (eval (S.wrap x y))

/-- Every rank on a finite carrier is bounded by its exact finite supremum. -/
theorem finiteModel_rank_bounded {S : StepDuplicatingSchema} {α : Type} [Fintype α]
    (F : FiniteModelInterpretation S α) (x : α) :
    F.rank x ≤ Finset.univ.sup F.rank :=
  Finset.le_sup (Finset.mem_univ x)

/-- Every wrapper-doubling stage strictly increases the interpreted rank. -/
theorem finiteModel_wrapDouble_rank_strict
    {S : StepDuplicatingSchema} {α : Type} [Fintype α]
    (F : FiniteModelInterpretation S α) (k : Nat) :
    F.rank (F.eval (wrapDouble S S.base k)) <
      F.rank (F.eval (wrapDouble S S.base (k + 1))) := by
  simpa only [wrapDouble_succ] using
    F.wrap_strict (wrapDouble S S.base k) (wrapDouble S S.base k)

/-- The rank at depth `k` is at least the base rank plus `k`. -/
theorem finiteModel_wrapDouble_rank_lower
    {S : StepDuplicatingSchema} {α : Type} [Fintype α]
    (F : FiniteModelInterpretation S α) (k : Nat) :
    F.rank (F.eval S.base) + k ≤ F.rank (F.eval (wrapDouble S S.base k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hs := finiteModel_wrapDouble_rank_strict F k
      omega

/-- No finite carrier admits the declared strictly wrapper-increasing interpretation. The
contradiction is derived from `wrap_strict`; no rank-growth premise is assumed. -/
theorem finiteModelInterpretation_impossible
    {S : StepDuplicatingSchema} {α : Type} [Fintype α]
    (F : FiniteModelInterpretation S α) : False := by
  let B := Finset.univ.sup F.rank
  have hge := finiteModel_wrapDouble_rank_lower F (B + 1)
  have hle : F.rank (F.eval (wrapDouble S S.base (B + 1))) ≤ B := by
    have hsup := finiteModel_rank_bounded F (F.eval (wrapDouble S S.base (B + 1)))
    simpa [B] using hsup
  omega

/-- **finiteModelTermination.** The exact unconditional result: the finite interpretation type
itself is empty once wrapper strictness is required. -/
abbrev FiniteModelTerminationRowClaim : Prop :=
  ∀ (S : StepDuplicatingSchema) (α : Type) [Fintype α],
    ¬ Nonempty (FiniteModelInterpretation S α)

theorem finiteModelTermination_row_anchor : FiniteModelTerminationRowClaim := by
  intro S α _ h
  exact finiteModelInterpretation_impossible h.some

/-! ## Match bounds -/

/-- A method certifying linear derivational complexity: some constant bounds every derivation
length by that multiple of the starting term size. This is what a match-bound certificate gives,
and it is the only property the transport uses. -/
def CertifiesLinearComplexity (C : Nat) : Prop :=
  ∀ (t u : Trace) (m : Nat), MetaSN_KO7.StepCtxFullPow t m u → m ≤ C * MetaSN_KO7.termSize t

/-- **The transport.** KO7 admits no linear derivational-complexity certificate, so no
match-bounded certificate exists for it. The linear-complexity theorem for match-bounded systems is
EXTERNAL (Geser, Hofbauer, Waldmann); the contrapositive transport and the lower family are
compiled here. -/
theorem no_linear_complexity_certificate (C : Nat) : ¬ CertifiesLinearComplexity C := by
  intro hC
  obtain ⟨t, u, m, hpow, hgt⟩ := MetaSN_KO7.step_not_linear_derivational_complexity C
  have := hC t u m hpow
  omega

/-- **matchBounds.** -/
abbrev MatchBoundsRowClaim : Prop :=
  (∀ C : Nat, ¬ CertifiesLinearComplexity C)
    ∧ (∀ n : Nat, ∃ t u : Trace, ∃ m : Nat,
        MetaSN_KO7.termSize t = 5 * n + 3 ∧ MetaSN_KO7.StepCtxFullPow t m u ∧ 2 ^ n ≤ m)

theorem matchBounds_row_anchor : MatchBoundsRowClaim :=
  ⟨no_linear_complexity_certificate, MetaSN_KO7.stepCtxFull_has_singleExponential_lower_family⟩

/-- A raise-consistent match-bound certificate carries its own transformed height assignment and
the linear-complexity consequence required of the method. The no-go below consumes the consequence,
not the name of the method. -/
structure RaiseConsistentMatchBoundCertificate where
  linearConstant : Nat
  raisedHeight : Trace → Nat
  raise_consistent : ∀ {a b : Trace}, Step a b → raisedHeight b ≤ raisedHeight a + 1
  certifies_linear : CertifiesLinearComplexity linearConstant

theorem no_raiseConsistentMatchBoundCertificate :
    ¬ Nonempty RaiseConsistentMatchBoundCertificate := by
  rintro ⟨C⟩
  exact no_linear_complexity_certificate C.linearConstant C.certifies_linear

/-- **raiseConsistencyMatchBounds.** The distinct raise-consistency certificate type is empty,
because every inhabitant would carry the linear derivational-complexity certificate refuted by the
compiled exponential lower family. -/
abbrev RaiseConsistencyMatchBoundsRowClaim : Prop :=
  ¬ Nonempty RaiseConsistentMatchBoundCertificate
    ∧ (∀ n : Nat, ∃ t u : Trace, ∃ m : Nat,
        MetaSN_KO7.termSize t = 5 * n + 3 ∧
          MetaSN_KO7.StepCtxFullPow t m u ∧ 2 ^ n ≤ m)

theorem raiseConsistencyMatchBounds_row_anchor : RaiseConsistencyMatchBoundsRowClaim :=
  ⟨no_raiseConsistentMatchBoundCertificate,
    MetaSN_KO7.stepCtxFull_has_singleExponential_lower_family⟩

/-- Left linearity of the duplicating rule: no variable repeats on the left-hand side. -/
def leftLinearDup : Prop :=
  countVar SchemaVar.b dupSrc = 1 ∧ countVar SchemaVar.s dupSrc = 1 ∧
    countVar SchemaVar.n dupSrc = 1

theorem leftLinearDup_holds : leftLinearDup :=
  ⟨countVar_dupSrc_b, countVar_dupSrc_s, countVar_dupSrc_n⟩

/-- **leftLinearMatchBounds.** The rule is left linear, so the method applies syntactically; it
then fails by the same complexity transport. -/
abbrev LeftLinearMatchBoundsRowClaim : Prop :=
  leftLinearDup ∧ MatchBoundsRowClaim

theorem leftLinearMatchBounds_row_anchor : LeftLinearMatchBoundsRowClaim :=
  ⟨leftLinearDup_holds, matchBounds_row_anchor⟩

/-! ## Labelling -/

/-- A semantic labelling policy for the schema signature. -/
structure Labelling (L : Type) where
  baseLabel : L
  succLabel : STerm → L
  wrapLabel : STerm → STerm → L
  recurLabel : STerm → STerm → STerm → L

/-- The actual labelled term algebra. Labels decorate constructor occurrences and variables remain
unchanged. -/
inductive LabelledSTerm (L : Type) where
  | var : SchemaVar → LabelledSTerm L
  | base : L → LabelledSTerm L
  | succ : L → LabelledSTerm L → LabelledSTerm L
  | wrap : L → LabelledSTerm L → LabelledSTerm L → LabelledSTerm L
  | recur : L → LabelledSTerm L → LabelledSTerm L → LabelledSTerm L → LabelledSTerm L

/-- Apply a labelling policy to every constructor occurrence. -/
def labelTerm {L : Type} (ℓ : Labelling L) : STerm → LabelledSTerm L
  | STerm.var v => .var v
  | STerm.base => .base ℓ.baseLabel
  | STerm.succ t => .succ (ℓ.succLabel t) (labelTerm ℓ t)
  | STerm.wrap x y => .wrap (ℓ.wrapLabel x y) (labelTerm ℓ x) (labelTerm ℓ y)
  | STerm.recur x y z =>
      .recur (ℓ.recurLabel x y z) (labelTerm ℓ x) (labelTerm ℓ y) (labelTerm ℓ z)

/-- Erase labels from the labelled syntax. -/
def eraseLabels {L : Type} : LabelledSTerm L → STerm
  | .var v => STerm.var v
  | .base _ => STerm.base
  | .succ _ t => STerm.succ (eraseLabels t)
  | .wrap _ x y => STerm.wrap (eraseLabels x) (eraseLabels y)
  | .recur _ x y z => STerm.recur (eraseLabels x) (eraseLabels y) (eraseLabels z)

/-- Labelling followed by erasure is the identity on the source term. -/
@[simp] theorem eraseLabels_labelTerm {L : Type} (ℓ : Labelling L) (t : STerm) :
    eraseLabels (labelTerm ℓ t) = t := by
  induction t with
  | var v => rfl
  | base => rfl
  | succ t ih => simp [labelTerm, eraseLabels, ih]
  | wrap x y ihx ihy => simp [labelTerm, eraseLabels, ihx, ihy]
  | recur x y z ihx ihy ihz => simp [labelTerm, eraseLabels, ihx, ihy, ihz]

/-- Variable occurrence count on the labelled syntax. -/
def countVarLabelled {L : Type} (v : SchemaVar) : LabelledSTerm L → Nat
  | .var w => if v = w then 1 else 0
  | .base _ => 0
  | .succ _ t => countVarLabelled v t
  | .wrap _ x y => countVarLabelled v x + countVarLabelled v y
  | .recur _ x y z => countVarLabelled v x + countVarLabelled v y + countVarLabelled v z

/-- Labelling preserves every variable multiplicity. -/
theorem countVarLabelled_labelTerm {L : Type} (ℓ : Labelling L) (v : SchemaVar) (t : STerm) :
    countVarLabelled v (labelTerm ℓ t) = countVar v t := by
  induction t with
  | var w => simp [labelTerm, countVarLabelled, countVar]
  | base => rfl
  | succ t ih => simpa [labelTerm, countVarLabelled, countVar] using ih
  | wrap x y ihx ihy => simp [labelTerm, countVarLabelled, countVar, ihx, ihy]
  | recur x y z ihx ihy ihz =>
      simp [labelTerm, countVarLabelled, countVar, ihx, ihy, ihz]

/-- **Labelling preserves duplication.** The payload variable still occurs once on the left and
twice on the right after labelling, so every direct barrier that reads the occurrence counts lifts
to the labelled system unchanged. -/
theorem labelling_preserves_duplication {L : Type} (ℓ : Labelling L) :
    countVarLabelled SchemaVar.s (labelTerm ℓ dupSrc) = 1 ∧
      countVarLabelled SchemaVar.s (labelTerm ℓ dupTgt) = 2 := by
  rw [countVarLabelled_labelTerm, countVarLabelled_labelTerm,
    countVar_dupSrc_s, countVar_dupTgt_s]
  exact ⟨rfl, rfl⟩

/-- The variable condition still refuses the labelled duplicating rule. -/
theorem labelled_variable_condition_refuses {L : Type} (ℓ : Labelling L)
    (C : SubtermCoefficients) (O : WeightedVariableConditionOrder C) :
    ¬ O.gt (eraseLabels (labelTerm ℓ dupSrc)) (eraseLabels (labelTerm ℓ dupTgt)) := by
  simpa using not_orients_dup_rule_weighted O

/-- **semanticLabeling.** Import dependent: duplication and every comparator factoring through
label erasure remain blocked, while a genuinely label-sensitive order can orient the schema rule. -/
abbrev SemanticLabelingRowClaim : Prop :=
  ∀ (L : Type) (ℓ : Labelling L),
    (eraseLabels (labelTerm ℓ dupSrc) = dupSrc
      ∧ eraseLabels (labelTerm ℓ dupTgt) = dupTgt)
      ∧ (countVarLabelled SchemaVar.s (labelTerm ℓ dupSrc) = 1 ∧
        countVarLabelled SchemaVar.s (labelTerm ℓ dupTgt) = 2)
      ∧ ∀ (C : SubtermCoefficients) (O : WeightedVariableConditionOrder C),
          ¬ O.gt (eraseLabels (labelTerm ℓ dupSrc)) (eraseLabels (labelTerm ℓ dupTgt))

theorem semanticLabeling_row_anchor : SemanticLabelingRowClaim :=
  fun _ ℓ =>
    ⟨⟨eraseLabels_labelTerm ℓ dupSrc, eraseLabels_labelTerm ℓ dupTgt⟩,
      labelling_preserves_duplication ℓ, labelled_variable_condition_refuses ℓ⟩

/-! ### Exact erasure/label-sensitive boundary -/

/-- A labelled comparator is erasure-factored through the variable-condition class when its
decision on every labelled pair is exactly the decision of some unlabelled variable-condition
order after erasing labels. -/
def ErasureFactoredVariableCondition {L : Type}
    (gt : LabelledSTerm L → LabelledSTerm L → Prop) : Prop :=
  ∃ O : VariableConditionOrder,
    ∀ x y, gt x y ↔ O.gt (eraseLabels x) (eraseLabels y)

/-- Every erasure-factored variable-condition comparator refuses the labelled duplicating rule,
for every label type and every labelling policy. -/
theorem erasureFactoredVariableCondition_refuses
    {L : Type} (ℓ : Labelling L) (gt : LabelledSTerm L → LabelledSTerm L → Prop)
    (hfactor : ErasureFactoredVariableCondition gt) :
    ¬ gt (labelTerm ℓ dupSrc) (labelTerm ℓ dupTgt) := by
  rintro hgt
  obtain ⟨O, hO⟩ := hfactor
  have horients : O.gt dupSrc dupTgt := by
    simpa using (hO (labelTerm ℓ dupSrc) (labelTerm ℓ dupTgt)).mp hgt
  exact not_orients_dup_rule O horients

/-- Score only the label at the root constructor. -/
def rootLabelValue {L : Type} (score : L → Nat) : LabelledSTerm L → Nat
  | .var _ => 0
  | .base label => score label
  | .succ label _ => score label
  | .wrap label _ _ => score label
  | .recur label _ _ _ => score label

/-- Strict root-label comparison. -/
def RootLabelGt {L : Type} (score : L → Nat) (x y : LabelledSTerm L) : Prop :=
  rootLabelValue score y < rootLabelValue score x

/-- The reverse of strict root-label comparison is well founded for every label type and score. -/
theorem rootLabelGt_wellFounded {L : Type} (score : L → Nat) :
    WellFounded (fun x y : LabelledSTerm L => RootLabelGt score y x) := by
  exact InvImage.wf (rootLabelValue score) Nat.lt_wfRel.wf

/-- Strict root-label comparison is transitive. -/
theorem rootLabelGt_transitive {L : Type} (score : L → Nat) :
    Transitive (RootLabelGt score) := by
  intro x y z hxy hyz
  exact Nat.lt_trans hyz hxy

/-- Constructor-sensitive policy distinguishing a recursive-call root from a wrapper root. -/
def constructorRootLabelling : Labelling Bool where
  baseLabel := false
  succLabel := fun _ => false
  wrapLabel := fun _ _ => false
  recurLabel := fun _ _ _ => true

/-- Numeric score of the constructor-sensitive Boolean labels. -/
def boolLabelValue : Bool → Nat
  | false => 0
  | true => 1

/-- The label-sensitive root order strictly orients the labelled duplicating schema rule. -/
theorem constructorRootLabelling_orients_duplication :
    RootLabelGt boolLabelValue
      (labelTerm constructorRootLabelling dupSrc)
      (labelTerm constructorRootLabelling dupTgt) := by
  simp [RootLabelGt, rootLabelValue, labelTerm, constructorRootLabelling,
    boolLabelValue, dupSrc, dupTgt]

/-- The orienting root-label order cannot factor through any unlabelled variable-condition order. -/
theorem constructorRootLabelling_not_erasureFactored :
    ¬ ErasureFactoredVariableCondition (RootLabelGt boolLabelValue) := by
  intro hfactor
  exact erasureFactoredVariableCondition_refuses constructorRootLabelling
    (RootLabelGt boolLabelValue) hfactor constructorRootLabelling_orients_duplication

/-- Context compatibility for a labelled strict relation at successor positions. -/
def SuccContextCompatible {L : Type}
    (gt : LabelledSTerm L → LabelledSTerm L → Prop) : Prop :=
  ∀ label x y, gt x y → gt (.succ label x) (.succ label y)

/-- The orienting root-label relation is necessarily root-local: placing a comparison below a
successor erases the differing root labels and destroys strictness. -/
theorem rootLabelGt_not_succContextCompatible :
    ¬ SuccContextCompatible (RootLabelGt boolLabelValue) := by
  intro h
  have hxy :
      RootLabelGt boolLabelValue
        (LabelledSTerm.base true) (LabelledSTerm.base false) := by
    simp [RootLabelGt, rootLabelValue, boolLabelValue]
  have hctx := h false (LabelledSTerm.base true) (LabelledSTerm.base false) hxy
  simp [RootLabelGt, rootLabelValue, boolLabelValue] at hctx

/-- Sharp labelling boundary: erasure-factored variable-condition orders are universally blocked,
but a well-founded, transitive, genuinely label-sensitive order orients the same labelled rule. -/
theorem semanticLabeling_exact_boundary :
    (∀ (L : Type) (ℓ : Labelling L)
        (gt : LabelledSTerm L → LabelledSTerm L → Prop),
      ErasureFactoredVariableCondition gt →
        ¬ gt (labelTerm ℓ dupSrc) (labelTerm ℓ dupTgt))
      ∧ WellFounded
        (fun x y : LabelledSTerm Bool => RootLabelGt boolLabelValue y x)
      ∧ Transitive (RootLabelGt boolLabelValue)
      ∧ RootLabelGt boolLabelValue
        (labelTerm constructorRootLabelling dupSrc)
        (labelTerm constructorRootLabelling dupTgt)
      ∧ ¬ ErasureFactoredVariableCondition (RootLabelGt boolLabelValue)
      ∧ ¬ SuccContextCompatible (RootLabelGt boolLabelValue) := by
  exact ⟨fun _ ℓ gt => erasureFactoredVariableCondition_refuses ℓ gt,
    rootLabelGt_wellFounded boolLabelValue,
    rootLabelGt_transitive boolLabelValue,
    constructorRootLabelling_orients_duplication,
    constructorRootLabelling_not_erasureFactored,
    rootLabelGt_not_succContextCompatible⟩

/-- A predictive labelling generated by one Boolean prediction on complete source subterms. -/
def predictiveLabelling (predict : STerm → Bool) : Labelling Bool where
  baseLabel := predict .base
  succLabel := fun t => predict (.succ t)
  wrapLabel := fun x y => predict (.wrap x y)
  recurLabel := fun x y z => predict (.recur x y z)

/-- **predictiveLabeling.** Every prediction function gives a concrete labelling whose erasure and
payload multiplicities are exact.  Thus prediction alone cannot repair an erasure-factored
variable-condition order. -/
abbrev PredictiveLabelingRowClaim : Prop :=
  ∀ predict : STerm → Bool,
    eraseLabels (labelTerm (predictiveLabelling predict) dupSrc) = dupSrc
      ∧ eraseLabels (labelTerm (predictiveLabelling predict) dupTgt) = dupTgt
      ∧ countVarLabelled SchemaVar.s
          (labelTerm (predictiveLabelling predict) dupSrc) = 1
      ∧ countVarLabelled SchemaVar.s
          (labelTerm (predictiveLabelling predict) dupTgt) = 2
      ∧ ∀ (gt : LabelledSTerm Bool → LabelledSTerm Bool → Prop),
          ErasureFactoredVariableCondition gt →
            ¬ gt (labelTerm (predictiveLabelling predict) dupSrc)
              (labelTerm (predictiveLabelling predict) dupTgt)

theorem predictiveLabeling_row_anchor : PredictiveLabelingRowClaim := by
  intro predict
  exact ⟨eraseLabels_labelTerm _ _, eraseLabels_labelTerm _ _,
    (labelling_preserves_duplication (predictiveLabelling predict)).1,
    (labelling_preserves_duplication (predictiveLabelling predict)).2,
    fun gt => erasureFactoredVariableCondition_refuses (predictiveLabelling predict) gt⟩

/-- **rootLabeling.** The concrete constructor-root labelling realizes both sides of the sharp
boundary: all erasure-factored orders remain blocked, while its root-sensitive order is
well-founded, transitive, and orients the root rule, but is not successor-context compatible. -/
abbrev RootLabelingRowClaim : Prop :=
  WellFounded (fun x y : LabelledSTerm Bool => RootLabelGt boolLabelValue y x)
    ∧ Transitive (RootLabelGt boolLabelValue)
    ∧ RootLabelGt boolLabelValue
        (labelTerm constructorRootLabelling dupSrc)
        (labelTerm constructorRootLabelling dupTgt)
    ∧ ¬ ErasureFactoredVariableCondition (RootLabelGt boolLabelValue)
    ∧ ¬ SuccContextCompatible (RootLabelGt boolLabelValue)

theorem rootLabeling_row_anchor : RootLabelingRowClaim :=
  ⟨rootLabelGt_wellFounded boolLabelValue,
    rootLabelGt_transitive boolLabelValue,
    constructorRootLabelling_orients_duplication,
    constructorRootLabelling_not_erasureFactored,
    rootLabelGt_not_succContextCompatible⟩

/-- Self-labelling by the complete argument tuple of each constructor occurrence. -/
def selfLabelling : Labelling (List STerm) where
  baseLabel := []
  succLabel := fun t => [t]
  wrapLabel := fun x y => [x, y]
  recurLabel := fun x y z => [x, y, z]

/-- The source and target root labels of the duplicating rule are genuinely distinct. -/
theorem selfLabelling_dup_root_labels_ne :
    [STerm.var SchemaVar.b, STerm.var SchemaVar.s,
        STerm.succ (STerm.var SchemaVar.n)] ≠
      [STerm.var SchemaVar.s,
        STerm.recur (STerm.var SchemaVar.b) (STerm.var SchemaVar.s)
          (STerm.var SchemaVar.n)] := by
  intro h
  have := congrArg List.length h
  simp at this

/-- **selfLabelingEquational.** This is a distinct self-labelling carrier, not an alias for the
generic semantic row.  It preserves the term and multiplicities under erasure, records unequal
source/target argument tuples, and universally blocks every comparator that forgets those labels. -/
abbrev SelfLabelingEquationalRowClaim : Prop :=
  eraseLabels (labelTerm selfLabelling dupSrc) = dupSrc
    ∧ eraseLabels (labelTerm selfLabelling dupTgt) = dupTgt
    ∧ countVarLabelled SchemaVar.s (labelTerm selfLabelling dupSrc) = 1
    ∧ countVarLabelled SchemaVar.s (labelTerm selfLabelling dupTgt) = 2
    ∧ [STerm.var SchemaVar.b, STerm.var SchemaVar.s,
        STerm.succ (STerm.var SchemaVar.n)] ≠
      [STerm.var SchemaVar.s,
        STerm.recur (STerm.var SchemaVar.b) (STerm.var SchemaVar.s)
          (STerm.var SchemaVar.n)]
    ∧ ∀ (gt : LabelledSTerm (List STerm) → LabelledSTerm (List STerm) → Prop),
        ErasureFactoredVariableCondition gt →
          ¬ gt (labelTerm selfLabelling dupSrc) (labelTerm selfLabelling dupTgt)

theorem selfLabelingEquational_row_anchor : SelfLabelingEquationalRowClaim :=
  ⟨eraseLabels_labelTerm _ _, eraseLabels_labelTerm _ _,
    (labelling_preserves_duplication selfLabelling).1,
    (labelling_preserves_duplication selfLabelling).2,
    selfLabelling_dup_root_labels_ne,
    fun gt => erasureFactoredVariableCondition_refuses selfLabelling gt⟩

/-! ## Rows with no carrier on `Trace` -/

/-- A compiled non-applicability record: the method's stated requirement, and a proof that KO7
fails it. -/
structure NotApplicableRecord where
  requirement : Prop
  ko7Fails : ¬ requirement

/-- Determinism of the root relation. This is a graph-carrier property, not a requirement on
arbitrary internal relations in a category or topos. -/
def stepIsFunctional : Prop :=
  ∀ a b c : Trace, Step a b → Step a c → b = c

/-- The kernel is not functional at the equality diagonal, so no functional carrier represents
it. -/
theorem step_not_functional : ¬ stepIsFunctional := by
  intro h
  have h1 : Step (Trace.eqW Trace.void Trace.void) Trace.void := Step.R_eq_refl Trace.void
  have h2 : Step (Trace.eqW Trace.void Trace.void)
      (Trace.integrate (Trace.merge Trace.void Trace.void)) :=
    Step.R_eq_diff Trace.void Trace.void
  have := h _ _ _ h1 h2
  exact Trace.noConfusion this

/-- Proof-carrying non-applicability record for deterministic graph semantics. -/
def categoricalToposRecord : NotApplicableRecord where
  requirement := stepIsFunctional
  ko7Fails := step_not_functional

/-- A transport of the rewrite relation to the graph of a single endofunction. -/
structure DeterministicGraphTransport (α : Type) where
  encode : Trace → α
  encode_injective : Function.Injective encode
  next : α → α
  transports : ∀ {a b : Trace}, Step a b → next (encode a) = encode b

/-- The equality-diagonal fork prevents transport to a deterministic graph over every carrier. -/
theorem no_deterministicGraphTransport (α : Type) :
    ¬ Nonempty (DeterministicGraphTransport α) := by
  rintro ⟨T⟩
  have h1 := T.transports (Step.R_eq_refl Trace.void)
  have h2 := T.transports (Step.R_eq_diff Trace.void Trace.void)
  have heq :
      T.encode Trace.void = T.encode (Trace.integrate (Trace.merge Trace.void Trace.void)) :=
    h1.symm.trans h2
  exact Trace.noConfusion (T.encode_injective heq)

/-- A thin relational category: objects are traces and morphisms are propositions, with identity,
composition, and every root rewrite represented as a generating morphism.  A rank strictly drops
along every nonidentity morphism. -/
structure RelationalCategoryCarrier where
  Hom : Trace → Trace → Prop
  identity : ∀ t, Hom t t
  compose : ∀ {a b c}, Hom a b → Hom b c → Hom a c
  generator : ∀ {a b}, Step a b → Hom a b
  rank : Trace → Nat
  nonidentity_descends : ∀ {a b}, Hom a b → a ≠ b → rank b < rank a

/-- The polynomial termination rank is nonincreasing along the reflexive-transitive root
rewrite closure. -/
theorem stepStar_W_le {a b : Trace} (h : Relation.ReflTransGen Step a b) :
    OperatorKO7.PolyInterpretation.W b ≤ OperatorKO7.PolyInterpretation.W a := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
      exact (Nat.le_of_lt (OperatorKO7.PolyInterpretation.W_orients_step hstep)).trans ih

/-- A nonidentity root-rewrite path strictly lowers the polynomial rank. -/
theorem stepStar_W_lt_of_ne {a b : Trace} (h : Relation.ReflTransGen Step a b)
    (hne : a ≠ b) :
    OperatorKO7.PolyInterpretation.W b < OperatorKO7.PolyInterpretation.W a := by
  cases h with
  | refl => exact False.elim (hne rfl)
  | tail hprefix hstep =>
      exact (OperatorKO7.PolyInterpretation.W_orients_step hstep).trans_le
        (stepStar_W_le hprefix)

/-- The actual rewrite-path category generated by KO7's root relation. -/
def ko7RelationalCategory : RelationalCategoryCarrier where
  Hom := Relation.ReflTransGen Step
  identity := fun _ => Relation.ReflTransGen.refl
  compose := fun hab hbc => Relation.ReflTransGen.trans hab hbc
  generator := fun h => Relation.ReflTransGen.single h
  rank := OperatorKO7.PolyInterpretation.W
  nonidentity_descends := stepStar_W_lt_of_ne

/-- The equality-diagonal fork is represented by two morphisms with different codomains.  This is
legal in a relation category and is exactly what a deterministic endofunction cannot represent. -/
theorem relationalCategory_contains_equality_fork :
    ko7RelationalCategory.Hom (Trace.eqW Trace.void Trace.void) Trace.void ∧
      ko7RelationalCategory.Hom (Trace.eqW Trace.void Trace.void)
        (Trace.integrate (Trace.merge Trace.void Trace.void)) :=
  ⟨Relation.ReflTransGen.single (Step.R_eq_refl Trace.void),
    Relation.ReflTransGen.single (Step.R_eq_diff Trace.void Trace.void)⟩

/-- Exact failure object: determinism is too narrow to be a categorical inapplicability
criterion.  The endofunction transport is impossible, while a terminating relational category
exists and contains the very fork that caused the endofunction obstruction. -/
theorem deterministic_graph_obstruction_not_categorical_obstruction :
    (∀ α : Type, ¬ Nonempty (DeterministicGraphTransport α)) ∧
      (∀ {a b : Trace}, Step a b → ko7RelationalCategory.Hom a b) ∧
      (∀ {a b : Trace}, ko7RelationalCategory.Hom a b → a ≠ b →
        ko7RelationalCategory.rank b < ko7RelationalCategory.rank a) ∧
      ko7RelationalCategory.Hom (Trace.eqW Trace.void Trace.void) Trace.void ∧
      ko7RelationalCategory.Hom (Trace.eqW Trace.void Trace.void)
        (Trace.integrate (Trace.merge Trace.void Trace.void)) :=
  ⟨no_deterministicGraphTransport, ko7RelationalCategory.generator,
    ko7RelationalCategory.nonidentity_descends,
    relationalCategory_contains_equality_fork.1,
    relationalCategory_contains_equality_fork.2⟩

/-- **categoricalToposTermination.** The exact result is a separation theorem, not an
inapplicability claim: deterministic graph semantics is impossible, but the root rewrite system
has a terminating relational category containing the equality fork. -/
abbrev CategoricalToposTerminationRowClaim : Prop :=
  (∀ α : Type, ¬ Nonempty (DeterministicGraphTransport α)) ∧
    (∀ {a b : Trace}, Step a b → ko7RelationalCategory.Hom a b) ∧
    (∀ {a b : Trace}, ko7RelationalCategory.Hom a b → a ≠ b →
      ko7RelationalCategory.rank b < ko7RelationalCategory.rank a) ∧
    ko7RelationalCategory.Hom (Trace.eqW Trace.void Trace.void) Trace.void ∧
    ko7RelationalCategory.Hom (Trace.eqW Trace.void Trace.void)
      (Trace.integrate (Trace.merge Trace.void Trace.void))

theorem categoricalToposTermination_row_anchor : CategoricalToposTerminationRowClaim :=
  deterministic_graph_obstruction_not_categorical_obstruction

/-- **forwardClosures.** Forward closures need right linearity of every rule. The duplicating rule
is not right linear: the payload occurs twice on the right. -/
def rightLinearDup : Prop := countVar SchemaVar.s dupTgt ≤ 1

theorem dup_not_rightLinear : ¬ rightLinearDup := by
  intro h
  unfold rightLinearDup at h
  rw [countVar_dupTgt_s] at h
  omega

def forwardClosuresRecord : NotApplicableRecord where
  requirement := rightLinearDup
  ko7Fails := dup_not_rightLinear

abbrev ForwardClosuresRowClaim : Prop :=
  ¬ rightLinearDup ∧ ¬ stepIsFunctional

theorem forwardClosures_row_anchor : ForwardClosuresRowClaim :=
  ⟨dup_not_rightLinear, step_not_functional⟩

/-- The abstract descent core of quasi-decreasingness: source reduction is well founded and every
conditional premise is discharged by a positive source-reduction path. -/
def AbstractQuasiDecreasing {α : Type} (R C : α → α → Prop) : Prop :=
  WellFounded (fun a b => R b a) ∧
    ∀ {a b : α}, C a b → Relation.TransGen R a b

/-- The condition relation of an unconditional rewrite system. -/
def NoConditionalPremise {α : Type} : α → α → Prop := fun _ _ => False

/-- With no conditional premises, the abstract quasi-decreasing core is exactly strong
normalization of the source relation. -/
theorem abstractQuasiDecreasing_noConditions_iff {α : Type} (R : α → α → Prop) :
    AbstractQuasiDecreasing R NoConditionalPremise ↔ WellFounded (fun a b => R b a) := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    intro a b hab
    exact False.elim hab

/-- **quasiDecreasingness.** For the condition-free KO7 root system, the abstract core is
equivalent to strong normalization and is inhabited by the compiled polynomial proof. A transport
to any richer literature definition still requires that definition's typed adapter. -/
abbrev QuasiDecreasingnessRowClaim : Prop :=
  (AbstractQuasiDecreasing Step NoConditionalPremise ↔
      WellFounded (fun a b : Trace => Step b a)) ∧
    AbstractQuasiDecreasing Step NoConditionalPremise

theorem quasiDecreasingness_row_anchor : QuasiDecreasingnessRowClaim :=
  ⟨abstractQuasiDecreasing_noConditions_iff Step,
    ⟨OperatorKO7.PolyInterpretation.wf_StepRev_poly, fun {_ _} h => False.elim h⟩⟩

end OperatorKO7.Methods.SemanticStructuralRows
