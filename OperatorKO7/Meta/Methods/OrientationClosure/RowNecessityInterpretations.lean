import OperatorKO7.Meta.Methods.OrientationClosure.HypothesisNecessityBase
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsInterpretations

/-!
# B7 hypothesis necessity: the fifteen interpretation rows

Relation: each row's own acceptance predicate for the free duplicating rule
`recur b s (succ n) → wrap s (recur b s n)`.
Property: necessity of one law clause (barrier rows) or of one data field (escape rows).

| Row | Kind | Deleted clause or feature |
|---|---|---|
| `linearPolyQ` | deleted premise | `wrap_left_mono` |
| `linearPolyR` | deleted premise | `wrap_right_mono` |
| `negativeCoefficientPolynomial` | escape feature | `succ` |
| `maxPolynomial` | escape feature | `recur` |
| `nonlinearHigherDegreePolynomial` | escape feature | `succ` |
| `multilinearInterpretation` | escape feature | `recur` |
| `matrixNScalarProjection` | deleted premise | `wrapLeft_pos` |
| `matrixQRScalarProjection` | deleted premise | `wrapLeft_pos` |
| `arcticScalarProjection` | deleted premise | `wrap_sf` and `recur_sf` |
| `tropicalScalarProjection` | deleted premise | `wrap_sf` and `recur_sf` |
| `triangularMatrix` | deleted premise | `matrix.wrapLeft_pos` |
| `tupleInterpretationStrictS` | escape feature | `recur` |
| `strictMonotoneAlgebraArchimedean` | escape feature | `recur` |
| `extendedMonotoneAlgebra` | escape feature | `strict` |
| `finiteModelTermination` | deleted premise | `irrefl` |

The arctic and tropical rows also keep the covered split of their laws into `wrap_sf` and
`zero_fin`, `succ_sf`, `recur_sf`: each part forces the barrier alone.

The fields of `TupleData` and `EMAData` have types that depend on the dimension, so their lenses
read the field through a fixed bijection with `ℕ`; `set` still replaces that one field only.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.HypothesisNecessity

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.InterpretationLaws
open OperatorKO7.Methods.OrientationClosure.PolynomialOrientationDecision
open OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations

/-! ## linearPolyQ -/

def linearPolyQNecessityKind : RowNecessityKind := .deletedBarrierPremise

/-- The ten laws of `LinearPolyLaws` other than `wrap_left_mono`. -/
def linearPolyQOtherLaws (M : linearPolyQData) : Prop :=
  0 < M.δ ∧ 0 ≤ M.z ∧ 0 ≤ M.c0 ∧ 0 ≤ M.w0 ∧ 0 ≤ M.r0 ∧ 1 ≤ M.c1 ∧ 1 ≤ M.wy ∧ 1 ≤ M.rb ∧
    1 ≤ M.rs ∧ 1 ≤ M.rn

/-- The deleted clause `wrap_left_mono`. -/
def linearPolyQDeletedLaw (M : linearPolyQData) : Prop := 1 ≤ M.ws

theorem linearPolyQLaws_split (M : linearPolyQData) :
    linearPolyQLaws M ↔ linearPolyQOtherLaws M ∧ linearPolyQDeletedLaw M := by
  unfold linearPolyQLaws linearPolyQOtherLaws linearPolyQDeletedLaw
  constructor
  · intro h
    exact ⟨⟨h.delta_pos, h.z_nonneg, h.c0_nonneg, h.w0_nonneg, h.r0_nonneg, h.succ_mono,
      h.wrap_right_mono, h.recur_base_mono, h.recur_step_mono, h.recur_counter_mono⟩,
      h.wrap_left_mono⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, h11⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h11, h7, h8, h9, h10⟩

/-- The witness with wrapper payload coefficient `0`: every other law holds and the rule is
accepted. -/
def linearPolyQCountermodel :
    DeletedPremiseCountermodel linearPolyQOtherLaws linearPolyQDeletedLaw linearPolyQAccepts where
  datum := { linearPolyQWitness with ws := 0 }
  other := by norm_num [linearPolyQOtherLaws, linearPolyQWitness]
  deletedFails := by norm_num [linearPolyQDeletedLaw]
  accepts := linearPolyQ_mutation.2

def linearPolyQNecessityStatement : Prop :=
  BarrierPremiseNecessity linearPolyQLaws linearPolyQOtherLaws linearPolyQDeletedLaw
    linearPolyQAccepts

theorem linearPolyQ_necessity : linearPolyQNecessityStatement :=
  ⟨linearPolyQLaws_split, fun M hM => linearPolyQ_universal M hM, ⟨linearPolyQCountermodel⟩⟩

/-! ## linearPolyR -/

def linearPolyRNecessityKind : RowNecessityKind := .deletedBarrierPremise

/-- The ten laws of `LinearPolyLaws` other than `wrap_right_mono`. -/
def linearPolyROtherLaws (M : linearPolyRData) : Prop :=
  0 < M.δ ∧ 0 ≤ M.z ∧ 0 ≤ M.c0 ∧ 0 ≤ M.w0 ∧ 0 ≤ M.r0 ∧ 1 ≤ M.c1 ∧ 1 ≤ M.ws ∧ 1 ≤ M.rb ∧
    1 ≤ M.rs ∧ 1 ≤ M.rn

/-- The deleted clause `wrap_right_mono`. -/
def linearPolyRDeletedLaw (M : linearPolyRData) : Prop := 1 ≤ M.wy

theorem linearPolyRLaws_split (M : linearPolyRData) :
    linearPolyRLaws M ↔ linearPolyROtherLaws M ∧ linearPolyRDeletedLaw M := by
  unfold linearPolyRLaws linearPolyROtherLaws linearPolyRDeletedLaw
  constructor
  · intro h
    exact ⟨⟨h.delta_pos, h.z_nonneg, h.c0_nonneg, h.w0_nonneg, h.r0_nonneg, h.succ_mono,
      h.wrap_left_mono, h.recur_base_mono, h.recur_step_mono, h.recur_counter_mono⟩,
      h.wrap_right_mono⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, h11⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h11, h8, h9, h10⟩

/-- The witness with wrapper coefficient `1/2` on the recursive result. -/
noncomputable def linearPolyRCountermodel :
    DeletedPremiseCountermodel linearPolyROtherLaws linearPolyRDeletedLaw linearPolyRAccepts where
  datum := { linearPolyRWitness with wy := 1 / 2 }
  other := by norm_num [linearPolyROtherLaws, linearPolyRWitness]
  deletedFails := by norm_num [linearPolyRDeletedLaw]
  accepts := linearPolyR_mutation.2

def linearPolyRNecessityStatement : Prop :=
  BarrierPremiseNecessity linearPolyRLaws linearPolyROtherLaws linearPolyRDeletedLaw
    linearPolyRAccepts

theorem linearPolyR_necessity : linearPolyRNecessityStatement :=
  ⟨linearPolyRLaws_split, fun M hM => linearPolyR_universal M hM, ⟨linearPolyRCountermodel⟩⟩

/-! ## negativeCoefficientPolynomial -/

def negativeCoefficientPolynomialNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- The successor polynomial of a negative-coefficient table. -/
def negativeCoefficientPolynomialSuccLens :
    FeatureLens negativeCoefficientPolynomialData (ZPoly 1) where
  get M := M.succ
  set M v := { M with succ := v }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The witness with the successor `n ↦ n`. -/
def negativeCoefficientPolynomialIdSuccDatum : negativeCoefficientPolynomialData :=
  { negativeCoefficientPolynomialWitness with succ := .var 0 }

theorem negativeCoefficientPolynomialIdSuccDatum_laws :
    negativeCoefficientPolynomialLaws negativeCoefficientPolynomialIdSuccDatum := by
  have hW : NegCoeffLaws negativeCoefficientPolynomialWitness :=
    negativeCoefficientPolynomialWitness_laws
  refine ⟨fun x y h => h 0, hW.wrap_weak, hW.recur_weak,
    ⟨?_, fun z h => negW_strict.wrapLeft z h, fun z {_ _} h => negW_strict.wrapRight z h,
      fun s n h => negW_strict.recurBase s n h, fun b {_ _} n h => negW_strict.recurStep b n h,
      fun b s {_ _} h => negW_strict.recurCounter b s h⟩⟩
  intro x y h
  show ((x : ℤ)).toNat < ((y : ℤ)).toNat
  omega

theorem negativeCoefficientPolynomialIdSuccDatum_rejects :
    ¬ negativeCoefficientPolynomialAccepts negativeCoefficientPolynomialIdSuccDatum := by
  intro hA
  have h : negativeCoefficientPolynomialIdSuccDatum.interp.wrap 0
        (negativeCoefficientPolynomialIdSuccDatum.interp.recur 0 0 0) <
      negativeCoefficientPolynomialIdSuccDatum.interp.recur 0 0
        (negativeCoefficientPolynomialIdSuccDatum.interp.succ 0) :=
    (show RootRuleOrients _ (fun x y : ℕ => x < y) from hA).recurSucc 0 0 0
  have e1 : negativeCoefficientPolynomialIdSuccDatum.interp.succ 0 = 0 := rfl
  have e2 : negativeCoefficientPolynomialIdSuccDatum.interp.wrap 0
      (negativeCoefficientPolynomialIdSuccDatum.interp.recur 0 0 0) =
        0 + negativeCoefficientPolynomialIdSuccDatum.interp.recur 0 0 0 + 1 :=
    negW_wrap 0 _
  rw [e1, e2] at h
  omega

def negativeCoefficientPolynomialSuccControl :
    FeatureChangeControl negativeCoefficientPolynomialLaws negativeCoefficientPolynomialAccepts
      negativeCoefficientPolynomialSuccLens where
  base := negativeCoefficientPolynomialWitness
  baseLaws := negativeCoefficientPolynomialWitness_laws
  baseAccepts := negW_root
  value := .var 0
  valueDiffers := by
    intro h
    cases h
  changedLaws := negativeCoefficientPolynomialIdSuccDatum_laws
  changedRejects := negativeCoefficientPolynomialIdSuccDatum_rejects

def negativeCoefficientPolynomialNecessityStatement : Prop :=
  EscapeFeatureNecessity negativeCoefficientPolynomialLaws negativeCoefficientPolynomialAccepts
    negativeCoefficientPolynomialSuccLens

theorem negativeCoefficientPolynomial_necessity : negativeCoefficientPolynomialNecessityStatement :=
  ⟨negativeCoefficientPolynomialSuccControl⟩

/-! ## maxPolynomial -/

def maxPolynomialNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- The recursor max-polynomial. -/
def maxPolynomialRecurLens : FeatureLens maxPolynomialData (MExpr (Fin 3)) where
  get M := M.recur
  set M v := { M with recur := v }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The product recursor replaced by the sum `n + 1 + (s + s + b + 2)`. -/
def maxPolynomialRecurControl :
    FeatureChangeControl maxPolynomialLaws maxPolynomialAccepts maxPolynomialRecurLens where
  base := maxPolynomialWitness
  baseLaws := maxPolynomialWitness_laws
  baseAccepts := maxPolynomialWitness_root
  value := maxPolynomialMutant.recur
  valueDiffers := by
    intro h
    cases h
  changedLaws := maxPolynomial_mutation.1
  changedRejects := maxPolynomial_mutation.2

def maxPolynomialNecessityStatement : Prop :=
  EscapeFeatureNecessity maxPolynomialLaws maxPolynomialAccepts maxPolynomialRecurLens

theorem maxPolynomial_necessity : maxPolynomialNecessityStatement :=
  ⟨maxPolynomialRecurControl⟩

/-! ## nonlinearHigherDegreePolynomial -/

def nonlinearHigherDegreePolynomialNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- The successor monomial table. -/
def nonlinearHigherDegreePolynomialSuccLens :
    FeatureLens nonlinearHigherDegreePolynomialData (List UMono) where
  get M := M.succ
  set M v := { M with succ := v }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The unit successor offset `1` replaced by `0`. -/
def nonlinearHigherDegreePolynomialSuccControl :
    FeatureChangeControl nonlinearHigherDegreePolynomialLaws nonlinearHigherDegreePolynomialAccepts
      nonlinearHigherDegreePolynomialSuccLens where
  base := nonlinearHigherDegreePolynomialWitness
  baseLaws := nonlinearHigherDegreePolynomialWitness_laws
  baseAccepts := nonlinearHigherDegreePolynomialWitness_root
  value := unitSucc 0
  valueDiffers := by
    intro h
    have h' : unitSucc 0 = unitSucc 1 := h
    exact absurd (congrArg (fun l => uEval l 0) h') (by simp [uEval_unitSucc])
  changedLaws := nonlinearHigherDegreePolynomial_mutation.1
  changedRejects := nonlinearHigherDegreePolynomial_mutation.2

def nonlinearHigherDegreePolynomialNecessityStatement : Prop :=
  EscapeFeatureNecessity nonlinearHigherDegreePolynomialLaws nonlinearHigherDegreePolynomialAccepts
    nonlinearHigherDegreePolynomialSuccLens

theorem nonlinearHigherDegreePolynomial_necessity :
    nonlinearHigherDegreePolynomialNecessityStatement :=
  ⟨nonlinearHigherDegreePolynomialSuccControl⟩

/-! ## multilinearInterpretation -/

def multilinearInterpretationNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- The recursor monomial table. -/
def multilinearInterpretationRecurLens :
    FeatureLens multilinearInterpretationData (List RMono) where
  get M := M.recur
  set M v := { M with recur := v }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

theorem multilinearUncoupled_rEval (b s n : ℕ) :
    rEval (multilinearR 2 1 1 2 0 1 0 0) b s n = 2 + b + s + 2 * n + b * n := by
  simp only [multilinearR, rEval]
  ring

/-- The witness with step-counter coefficient `rsn = 0`: recursor `2 + b + s + 2n + b n`. -/
theorem multilinearInterpretationUncoupled_laws :
    multilinearInterpretationLaws
      { multilinearInterpretationWitness with recur := multilinearR 2 1 1 2 0 1 0 0 } := by
  have hW : MultilinearLaws multilinearInterpretationWitness :=
    multilinearInterpretationWitness_laws
  refine ⟨⟨fun h => hW.strict.succ h, fun z h => hW.strict.wrapLeft z h,
    fun z {_ _} h => hW.strict.wrapRight z h, ?_, ?_, ?_⟩, hW.succ_multilinear, hW.wrap_multilinear,
    by decide⟩
  · intro x y s n h
    show rEval (multilinearR 2 1 1 2 0 1 0 0) x s n < rEval (multilinearR 2 1 1 2 0 1 0 0) y s n
    rw [multilinearUncoupled_rEval, multilinearUncoupled_rEval]
    have := Nat.mul_le_mul_right n (le_of_lt h)
    omega
  · intro b x y n h
    show rEval (multilinearR 2 1 1 2 0 1 0 0) b x n < rEval (multilinearR 2 1 1 2 0 1 0 0) b y n
    rw [multilinearUncoupled_rEval, multilinearUncoupled_rEval]
    omega
  · intro b s x y h
    show rEval (multilinearR 2 1 1 2 0 1 0 0) b s x < rEval (multilinearR 2 1 1 2 0 1 0 0) b s y
    rw [multilinearUncoupled_rEval, multilinearUncoupled_rEval]
    have := Nat.mul_le_mul_left b (le_of_lt h)
    omega

def multilinearInterpretationRecurControl :
    FeatureChangeControl multilinearInterpretationLaws multilinearInterpretationAccepts
      multilinearInterpretationRecurLens where
  base := multilinearInterpretationWitness
  baseLaws := multilinearInterpretationWitness_laws
  baseAccepts := multilinearInterpretationWitness_root
  value := multilinearR 2 1 1 2 0 1 0 0
  valueDiffers := by
    intro h
    have h' : multilinearR 2 1 1 2 0 1 0 0 = multilinearR 2 1 1 2 0 1 1 0 := h
    exact absurd (congrArg (fun r => rEval r 0 1 1) h') (by decide)
  changedLaws := multilinearInterpretationUncoupled_laws
  changedRejects := multilinearInterpretation_mutation

def multilinearInterpretationNecessityStatement : Prop :=
  EscapeFeatureNecessity multilinearInterpretationLaws multilinearInterpretationAccepts
    multilinearInterpretationRecurLens

theorem multilinearInterpretation_necessity : multilinearInterpretationNecessityStatement :=
  ⟨multilinearInterpretationRecurControl⟩

/-! ## matrixNScalarProjection -/

def matrixNScalarProjectionNecessityKind : RowNecessityKind := .deletedBarrierPremise

/-- The five laws of `NatMatrixLaws` other than `wrapLeft_pos`. -/
def matrixNScalarProjectionOtherLaws (M : matrixNScalarProjectionData) : Prop :=
  1 ≤ M.succMat 0 0 ∧ 1 ≤ M.wrapRight 0 0 ∧ 1 ≤ M.recurBase 0 0 ∧ 1 ≤ M.recurStep 0 0 ∧
    1 ≤ M.recurCounter 0 0

/-- The deleted clause `wrapLeft_pos`. -/
def matrixNScalarProjectionDeletedLaw (M : matrixNScalarProjectionData) : Prop :=
  1 ≤ M.wrapLeft 0 0

theorem matrixNScalarProjectionLaws_split (M : matrixNScalarProjectionData) :
    matrixNScalarProjectionLaws M ↔
      matrixNScalarProjectionOtherLaws M ∧ matrixNScalarProjectionDeletedLaw M := by
  unfold matrixNScalarProjectionLaws matrixNScalarProjectionOtherLaws
    matrixNScalarProjectionDeletedLaw
  constructor
  · intro h
    exact ⟨⟨h.succ_pos, h.wrapRight_pos, h.recurBase_pos, h.recurStep_pos, h.recurCounter_pos⟩,
      h.wrapLeft_pos⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩
    exact ⟨h1, h6, h2, h3, h4, h5⟩

/-- The witness with wrapper payload matrix `0`. -/
def matrixNScalarProjectionCountermodel :
    DeletedPremiseCountermodel matrixNScalarProjectionOtherLaws matrixNScalarProjectionDeletedLaw
      matrixNScalarProjectionAccepts where
  datum := { matrixNScalarProjectionWitness with wrapLeft := 0 }
  other := by
    unfold matrixNScalarProjectionOtherLaws
    decide
  deletedFails := by
    unfold matrixNScalarProjectionDeletedLaw
    decide
  accepts := matrixNScalarProjection_mutation.2

def matrixNScalarProjectionNecessityStatement : Prop :=
  BarrierPremiseNecessity matrixNScalarProjectionLaws matrixNScalarProjectionOtherLaws
    matrixNScalarProjectionDeletedLaw matrixNScalarProjectionAccepts

theorem matrixNScalarProjection_necessity : matrixNScalarProjectionNecessityStatement :=
  ⟨matrixNScalarProjectionLaws_split, fun M hM => matrixNScalarProjection_universal M hM,
    ⟨matrixNScalarProjectionCountermodel⟩⟩

/-! ## matrixQRScalarProjection -/

def matrixQRScalarProjectionNecessityKind : RowNecessityKind := .deletedBarrierPremise

/-- The sixteen laws of `RealMatrixLaws` other than `wrapLeft_pos`. -/
def matrixQRScalarProjectionOtherLaws (M : matrixQRScalarProjectionData) : Prop :=
  0 < M.δ ∧ NonnegVec M.zeroVec ∧ NonnegMat M.succMat ∧ NonnegVec M.succVec ∧
    NonnegMat M.wrapLeft ∧ NonnegMat M.wrapRight ∧ NonnegVec M.wrapVec ∧ NonnegMat M.recurBase ∧
    NonnegMat M.recurStep ∧ NonnegMat M.recurCounter ∧ NonnegVec M.recurVec ∧
    1 ≤ M.succMat 0 0 ∧ 1 ≤ M.wrapRight 0 0 ∧ 1 ≤ M.recurBase 0 0 ∧ 1 ≤ M.recurStep 0 0 ∧
    1 ≤ M.recurCounter 0 0

/-- The deleted clause `wrapLeft_pos`. -/
def matrixQRScalarProjectionDeletedLaw (M : matrixQRScalarProjectionData) : Prop :=
  1 ≤ M.wrapLeft 0 0

theorem matrixQRScalarProjectionLaws_split (M : matrixQRScalarProjectionData) :
    matrixQRScalarProjectionLaws M ↔
      matrixQRScalarProjectionOtherLaws M ∧ matrixQRScalarProjectionDeletedLaw M := by
  unfold matrixQRScalarProjectionLaws matrixQRScalarProjectionOtherLaws
    matrixQRScalarProjectionDeletedLaw
  constructor
  · intro h
    exact ⟨⟨h.delta_pos, h.zeroVec_nonneg, h.succMat_nonneg, h.succVec_nonneg, h.wrapLeft_nonneg,
      h.wrapRight_nonneg, h.wrapVec_nonneg, h.recurBase_nonneg, h.recurStep_nonneg,
      h.recurCounter_nonneg, h.recurVec_nonneg, h.succ_pos, h.wrapRight_pos, h.recurBase_pos,
      h.recurStep_pos, h.recurCounter_pos⟩, h.wrapLeft_pos⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩, h17⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h17, h13, h14, h15, h16⟩

/-- The witness with wrapper payload matrix `0`. -/
noncomputable def matrixQRScalarProjectionCountermodel :
    DeletedPremiseCountermodel matrixQRScalarProjectionOtherLaws
      matrixQRScalarProjectionDeletedLaw matrixQRScalarProjectionAccepts where
  datum := { matrixQRScalarProjectionWitness with wrapLeft := 0 }
  other := by
    have hW : RealMatrixLaws matrixQRScalarProjectionWitness := matrixQRScalarProjectionWitness_laws
    exact ⟨hW.delta_pos, hW.zeroVec_nonneg, hW.succMat_nonneg, hW.succVec_nonneg,
      fun _ _ => le_refl 0, hW.wrapRight_nonneg, hW.wrapVec_nonneg, hW.recurBase_nonneg,
      hW.recurStep_nonneg, hW.recurCounter_nonneg, hW.recurVec_nonneg, hW.succ_pos,
      hW.wrapRight_pos, hW.recurBase_pos, hW.recurStep_pos, hW.recurCounter_pos⟩
  deletedFails := by
    show ¬ (1 : ℝ) ≤ (0 : RMat 1) 0 0
    norm_num
  accepts := matrixQRScalarProjection_mutation.2

def matrixQRScalarProjectionNecessityStatement : Prop :=
  BarrierPremiseNecessity matrixQRScalarProjectionLaws matrixQRScalarProjectionOtherLaws
    matrixQRScalarProjectionDeletedLaw matrixQRScalarProjectionAccepts

theorem matrixQRScalarProjection_necessity : matrixQRScalarProjectionNecessityStatement :=
  ⟨matrixQRScalarProjectionLaws_split, fun M hM => matrixQRScalarProjection_universal M hM,
    ⟨matrixQRScalarProjectionCountermodel⟩⟩

/-! ## arcticScalarProjection

The row is a barrier-premise row. Its obstruction is contextual masking by `max` at the
contextual relation of the row, and it uses the somewhere finiteness of the wrapper or of the
recursor: the datum `arcticMaskFreeDatum`, whose wrapper and recursor are `−∞` at every entry,
keeps `zero_fin` and `succ_sf` and is accepted, so the barrier is false with the clause pair
`wrap_sf`, `recur_sf` deleted (`arcticScalarProjection_lawFree_barrier_false` refutes the
law-free reading). No single clause is removable: the laws split into `wrap_sf` and the other
three clauses, and each part forces the barrier alone. The control is the lawful witness, which
orients every root instance of the duplicating rule and fails at the contextual relation. -/

/-- Necessity class of the arctic row: a barrier premise, the clause pair `wrap_sf`, `recur_sf`.
Changed from `lawFreeBarrierControl` by `arcticScalarProjection_lawFree_barrier_false`. -/
def arcticScalarProjectionNecessityKind : RowNecessityKind := .deletedBarrierPremise

/-- Part A of `ArcticLaws`: the clause `wrap_sf`. -/
def arcticScalarProjectionPartA (M : arcticScalarProjectionData) : Prop :=
  M.wrapVec 0 ≠ ⊥ ∨ M.wrapLeft 0 0 ≠ ⊥ ∨ M.wrapRight 0 0 ≠ ⊥

/-- Part B of `ArcticLaws`: the clauses `zero_fin`, `succ_sf` and `recur_sf`. -/
def arcticScalarProjectionPartB (M : arcticScalarProjectionData) : Prop :=
  M.zeroVec 0 ≠ ⊥ ∧ (M.succVec 0 ≠ ⊥ ∨ M.succMat 0 0 ≠ ⊥) ∧
    (M.recurVec 0 ≠ ⊥ ∨ M.recurBase 0 0 ≠ ⊥ ∨ M.recurStep 0 0 ≠ ⊥ ∨ M.recurCounter 0 0 ≠ ⊥)

theorem arcticScalarProjectionLaws_split (M : arcticScalarProjectionData) :
    arcticScalarProjectionLaws M ↔
      arcticScalarProjectionPartA M ∧ arcticScalarProjectionPartB M := by
  unfold arcticScalarProjectionLaws arcticScalarProjectionPartA arcticScalarProjectionPartB
  constructor
  · intro h
    exact ⟨h.wrap_sf, h.zero_fin, h.succ_sf, h.recur_sf⟩
  · rintro ⟨hA, h1, h2, h3⟩
    exact ⟨h1, h2, hA, h3⟩

/-- Contextual masking by `max` at the two wrapper contexts, for any two values `R` and `L` placed
in the hole: the argument of `arctic_context_barrier`, consuming only `wrap_sf`. -/
theorem arctic_wrap_masking (M : ArcticData)
    (hw : M.wrapVec 0 ≠ ⊥ ∨ M.wrapLeft 0 0 ≠ ⊥ ∨ M.wrapRight 0 0 ≠ ⊥) (R L : AVec M.d)
    (h : ∀ t : AVec M.d, AFin t →
      arcLt (M.interp.wrap t R) (M.interp.wrap t L) ∧
        arcLt (M.interp.wrap R t) (M.interp.wrap L t)) :
    False := by
  have hz : AFin (aConst 0 : AVec M.d) := WithBot.coe_ne_bot
  by_cases hA : ∃ j, M.wrapLeft 0 j ≠ ⊥
  · obtain ⟨j0, hj0⟩ := hA
    obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1 hj0
    obtain ⟨B1, hB1⟩ := wb_exists_ge (aAct M.wrapRight L 0)
    obtain ⟨B2, hB2⟩ := wb_exists_ge (aAct M.wrapRight R 0)
    obtain ⟨B3, hB3⟩ := wb_exists_ge (M.wrapVec 0)
    obtain ⟨K, hK1, hK2, hK3⟩ : ∃ K : ℕ, B1 ≤ K ∧ B2 ≤ K ∧ B3 ≤ K :=
      ⟨B1 + B2 + B3, by omega, by omega, by omega⟩
    have ht : AFin (aConst K : AVec M.d) := WithBot.coe_ne_bot
    have hP : WithBot.some K ≤ aAct M.wrapLeft (aConst K) 0 := by
      have h1 : M.wrapLeft 0 j0 + aConst K j0 ≤ aAct M.wrapLeft (aConst K) 0 :=
        Finset.le_sup (f := fun j => M.wrapLeft 0 j + aConst K j) (Finset.mem_univ j0)
      have h2 : WithBot.some K ≤ M.wrapLeft 0 j0 + aConst K j0 := by
        rw [← hm]
        show WithBot.some K ≤ WithBot.some m + WithBot.some K
        rw [← WithBot.coe_add]
        exact WithBot.coe_le_coe.2 (Nat.le_add_left K m)
      exact le_trans h2 h1
    have hc : M.wrapVec 0 ≤ aAct M.wrapLeft (aConst K) 0 :=
      le_trans hB3 (le_trans (WithBot.coe_le_coe.2 hK3) hP)
    have hwrapEq : ∀ X : AVec M.d, aAct M.wrapRight X 0 ≤ aAct M.wrapLeft (aConst K) 0 →
        M.interp.wrap (aConst K) X 0 = aAct M.wrapLeft (aConst K) 0 := by
      intro X hX
      show max (max (aAct M.wrapLeft (aConst K) 0) (aAct M.wrapRight X 0)) (M.wrapVec 0) = _
      rw [max_eq_left hX, max_eq_left hc]
    have key := (h (aConst K) ht).1 0
    rw [hwrapEq _ (le_trans hB2 (le_trans (WithBot.coe_le_coe.2 hK2) hP)),
      hwrapEq _ (le_trans hB1 (le_trans (WithBot.coe_le_coe.2 hK1) hP))] at key
    rcases key with h' | ⟨h', _⟩
    · exact lt_irrefl _ h'
    · exact ne_bot_of_le_ne_bot WithBot.coe_ne_bot hP h'
  · push_neg at hA
    have e : ∀ x : AVec M.d, aAct M.wrapLeft x 0 = ⊥ := by
      intro x
      apply (Finset.sup_eq_bot_iff _ _).2
      intro j _
      show M.wrapLeft 0 j + x j = ⊥
      rw [hA j, WithBot.bot_add]
    have hwrapEq : ∀ X : AVec M.d, M.interp.wrap X (aConst 0) 0 =
        max (max ⊥ (aAct M.wrapRight (aConst 0) 0)) (M.wrapVec 0) := by
      intro X
      show max (max (aAct M.wrapLeft X 0) (aAct M.wrapRight (aConst 0) 0)) (M.wrapVec 0) = _
      rw [e X]
    have hne : max (max ⊥ (aAct M.wrapRight (aConst 0 : AVec M.d) 0)) (M.wrapVec 0) ≠ ⊥ := by
      rcases hw with hv | hl | hr
      · exact ne_bot_of_le_ne_bot hv (le_max_right _ _)
      · exact absurd (hA 0) hl
      · obtain ⟨r, hr'⟩ := WithBot.ne_bot_iff_exists.1 hr
        have h1 : M.wrapRight 0 0 + aConst 0 0 ≤ aAct M.wrapRight (aConst 0 : AVec M.d) 0 :=
          Finset.le_sup (f := fun j => M.wrapRight 0 j + aConst 0 j) (Finset.mem_univ 0)
        have h2 : M.wrapRight 0 0 + (aConst 0 : AVec M.d) 0 ≠ ⊥ := by
          rw [← hr']
          show WithBot.some r + WithBot.some 0 ≠ ⊥
          rw [← WithBot.coe_add]
          exact WithBot.coe_ne_bot
        exact ne_bot_of_le_ne_bot (ne_bot_of_le_ne_bot h2 h1)
          (le_trans (le_max_right _ _) (le_max_left _ _))
    have key := (h (aConst 0) hz).2 0
    rw [hwrapEq, hwrapEq] at key
    rcases key with h' | ⟨h', _⟩
    · exact lt_irrefl _ h'
    · exact hne h'

/-- Part A alone forces the barrier. -/
theorem arcticScalarProjection_partA_barrier (M : arcticScalarProjectionData)
    (hA : arcticScalarProjectionPartA M) : ¬ arcticScalarProjectionAccepts M := by
  intro hacc
  have hz : AFin (aConst 0 : AVec M.d) := WithBot.coe_ne_bot
  exact arctic_wrap_masking M hA _ _ (fun t ht =>
    dupCtx_wrap_instances AFin M.interp arcLt hacc (aConst 0) (aConst 0) (aConst 0) t hz hz hz ht)

/-- Part B alone forces the barrier, through `recur_sf`. If the step row of the recursor reads a
finite entry, a large step argument masks the recursor's base argument in the base context, where
both sides are placed; otherwise the recursor ignores its step argument and the step context gives
two equal values, finite by `recur_sf`. -/
theorem arcticScalarProjection_partB_barrier (M : arcticScalarProjectionData)
    (hB : arcticScalarProjectionPartB M) : ¬ arcticScalarProjectionAccepts M := by
  intro hacc
  have hr := hB.2.2
  have hz : AFin (aConst 0 : AVec M.d) := WithBot.coe_ne_bot
  have noEq : ∀ x y : AVec M.d, arcLt x y → x 0 = y 0 → x 0 ≠ ⊥ → False := by
    intro x y hxy he hne
    rcases hxy 0 with h' | ⟨h', _⟩
    · rw [he] at h'
      exact lt_irrefl _ h'
    · exact hne h'
  have er : ∀ b s n : AVec M.d, M.interp.recur b s n 0 =
      max (max (max (aAct M.recurBase b 0) (aAct M.recurStep s 0)) (aAct M.recurCounter n 0))
        (M.recurVec 0) := fun _ _ _ => rfl
  by_cases hS : ∃ j, M.recurStep 0 j ≠ ⊥
  · obtain ⟨j0, hj0⟩ := hS
    obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1 hj0
    obtain ⟨B1, hB1⟩ := wb_exists_ge (aAct M.recurBase
      (M.interp.wrap (aConst 0) (M.interp.recur (aConst 0) (aConst 0) (aConst 0))) 0)
    obtain ⟨B2, hB2⟩ := wb_exists_ge (aAct M.recurBase
      (M.interp.recur (aConst 0) (aConst 0) (M.interp.succ (aConst 0))) 0)
    have ht : AFin (aConst (B1 + B2) : AVec M.d) := WithBot.coe_ne_bot
    have hP : WithBot.some (B1 + B2) ≤ aAct M.recurStep (aConst (B1 + B2)) 0 := by
      have h1 : M.recurStep 0 j0 + aConst (B1 + B2) j0 ≤ aAct M.recurStep (aConst (B1 + B2)) 0 :=
        Finset.le_sup (f := fun j => M.recurStep 0 j + aConst (B1 + B2) j) (Finset.mem_univ j0)
      have h2 : WithBot.some (B1 + B2) ≤ M.recurStep 0 j0 + aConst (B1 + B2) j0 := by
        rw [← hm]
        show WithBot.some (B1 + B2) ≤ WithBot.some m + WithBot.some (B1 + B2)
        rw [← WithBot.coe_add]
        exact WithBot.coe_le_coe.2 (Nat.le_add_left _ m)
      exact le_trans h2 h1
    have hρ : ∀ j,
        AFin ((fun j : ℕ => if j = 0 then (aConst 0 : AVec M.d) else aConst (B1 + B2)) j) := by
      intro j
      show AFin (if j = 0 then (aConst 0 : AVec M.d) else aConst (B1 + B2))
      split_ifs
      · exact hz
      · exact ht
    have key : arcLt
        (M.interp.recur (M.interp.wrap (aConst 0) (M.interp.recur (aConst 0) (aConst 0) (aConst 0)))
          (aConst (B1 + B2)) (aConst 0))
        (M.interp.recur (M.interp.recur (aConst 0) (aConst 0) (M.interp.succ (aConst 0)))
          (aConst (B1 + B2)) (aConst 0)) :=
      hacc _ hρ _ _
        (DupCtxStep.lift (.recurBase .hole (.var 1) (.var 0)) (.var 0) (.var 0) (.var 0))
    have hval : ∀ X : AVec M.d, aAct M.recurBase X 0 ≤ WithBot.some (B1 + B2) →
        M.interp.recur X (aConst (B1 + B2)) (aConst 0) 0 =
          max (max (aAct M.recurStep (aConst (B1 + B2)) 0) (aAct M.recurCounter (aConst 0) 0))
            (M.recurVec 0) := by
      intro X hX
      rw [er, max_eq_right (le_trans hX hP)]
    have e1 := hval _ (le_trans hB1 (WithBot.coe_le_coe.2 (Nat.le_add_right B1 B2)))
    have e2 := hval _ (le_trans hB2 (WithBot.coe_le_coe.2 (Nat.le_add_left B2 B1)))
    refine noEq _ _ key (e1.trans e2.symm) ?_
    rw [e1]
    exact ne_bot_of_le_ne_bot WithBot.coe_ne_bot
      (le_trans hP (le_trans (le_max_left _ _) (le_max_left _ _)))
  · push_neg at hS
    have e : ∀ X : AVec M.d, aAct M.recurStep X 0 = ⊥ := by
      intro X
      apply (Finset.sup_eq_bot_iff _ _).2
      intro j _
      show M.recurStep 0 j + X j = ⊥
      rw [hS j, WithBot.bot_add]
    have key : arcLt
        (M.interp.recur (aConst 0)
          (M.interp.wrap (aConst 0) (M.interp.recur (aConst 0) (aConst 0) (aConst 0))) (aConst 0))
        (M.interp.recur (aConst 0)
          (M.interp.recur (aConst 0) (aConst 0) (M.interp.succ (aConst 0))) (aConst 0)) :=
      hacc (fun _ => aConst 0) (fun _ => hz) _ _
        (DupCtxStep.lift (.recurStep (.var 0) .hole (.var 0)) (.var 0) (.var 0) (.var 0))
    have hval : ∀ X : AVec M.d, M.interp.recur (aConst 0) X (aConst 0) 0 =
        max (max (max (aAct M.recurBase (aConst 0) 0) ⊥) (aAct M.recurCounter (aConst 0) 0))
          (M.recurVec 0) := by
      intro X
      rw [er, e X]
    refine noEq _ _ key ((hval _).trans (hval _).symm) ?_
    rw [hval]
    have hfin : ∀ A : AMat M.d, A 0 0 ≠ ⊥ → aAct A (aConst 0 : AVec M.d) 0 ≠ ⊥ := by
      intro A hA
      obtain ⟨r, hr'⟩ := WithBot.ne_bot_iff_exists.1 hA
      have h1 : A 0 0 + aConst 0 0 ≤ aAct A (aConst 0 : AVec M.d) 0 :=
        Finset.le_sup (f := fun j => A 0 j + aConst 0 j) (Finset.mem_univ 0)
      have h2 : A 0 0 + (aConst 0 : AVec M.d) 0 ≠ ⊥ := by
        rw [← hr']
        show WithBot.some r + WithBot.some 0 ≠ ⊥
        rw [← WithBot.coe_add]
        exact WithBot.coe_ne_bot
      exact ne_bot_of_le_ne_bot h2 h1
    rcases hr with h | h | h | h
    · exact ne_bot_of_le_ne_bot h (le_max_right _ _)
    · exact ne_bot_of_le_ne_bot (hfin _ h)
        (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
    · exact absurd (hS 0) h
    · exact ne_bot_of_le_ne_bot (hfin _ h) (le_trans (le_max_right _ _) (le_max_left _ _))

/-- Nonduplicating control: a lawful arctic member orients the rule `succ x → x`, in which `x`
occurs once on each side, at the root on `ℕ × A^d`. -/
def arcticScalarProjectionNonduplicatingControl : Prop :=
  ∃ M : arcticScalarProjectionData, arcticScalarProjectionLaws M ∧
    ∀ ρ : Fin 1 → AVec M.d, (∀ i, AFin (ρ i)) →
      arcLt (M.interp.eval ρ (.var 0)) (M.interp.eval ρ (.succ (.var 0)))

theorem arcticScalarProjection_nonduplicatingControl :
    arcticScalarProjectionNonduplicatingControl :=
  ⟨{ arcticScalarProjectionWitness with succMat := fun _ _ => ((1 : ℕ) : WithBot ℕ) },
    ⟨WithBot.coe_ne_bot, Or.inr WithBot.coe_ne_bot, Or.inr (Or.inl WithBot.coe_ne_bot),
      Or.inr (Or.inr (Or.inl WithBot.coe_ne_bot))⟩,
    fun ρ hρ i => by
      have hi : i = 0 := Fin.eq_zero i
      subst hi
      left
      show ρ 0 0 < max (aAct (d := 0) (fun _ _ => ((1 : ℕ) : WithBot ℕ)) (ρ 0) 0) (⊥ : WithBot ℕ)
      rw [max_eq_left bot_le, aAct_one]
      obtain ⟨k, hk⟩ := WithBot.ne_bot_iff_exists.1 (hρ 0)
      rw [← hk]
      exact wb_coe_lt_one_add k⟩

/-- The contextual relation of the row rejects the nonduplicating rule as well: every lawful member
fails to decrease `succ x → x` under every one-hole context. -/
theorem arcticScalarProjection_nonduplicating_context_rejected (M : arcticScalarProjectionData)
    (hM : arcticScalarProjectionLaws M) :
    ¬ ∀ ρ : ℕ → AVec M.d, (∀ j, AFin (ρ j)) → ∀ C : FreeContext ℕ,
      arcLt (M.interp.eval ρ (C.plug (.var 0))) (M.interp.eval ρ (C.plug (.succ (.var 0)))) := by
  intro h
  have hz : AFin (aConst 0 : AVec M.d) := WithBot.coe_ne_bot
  refine arctic_wrap_masking M (show ArcticLaws M from hM).wrap_sf (aConst 0)
    (M.interp.succ (aConst 0)) (fun t ht => ?_)
  have hρ : ∀ j, AFin ((fun j : ℕ => if j = 0 then (aConst 0 : AVec M.d) else t) j) := by
    intro j
    show AFin (if j = 0 then (aConst 0 : AVec M.d) else t)
    split_ifs
    · exact hz
    · exact ht
  exact ⟨h _ hρ (.wrapRight (.var 1) .hole), h _ hρ (.wrapLeft .hole (.var 1))⟩

/-- The clauses `zero_fin` and `succ_sf` of `ArcticLaws`, kept by the deleted-premise
countermodel. -/
def arcticScalarProjectionOtherLaws (M : arcticScalarProjectionData) : Prop :=
  M.zeroVec 0 ≠ ⊥ ∧ (M.succVec 0 ≠ ⊥ ∨ M.succMat 0 0 ≠ ⊥)

/-- The deleted barrier premise: the clauses `wrap_sf` and `recur_sf` of `ArcticLaws`. -/
def arcticScalarProjectionDeletedLaw (M : arcticScalarProjectionData) : Prop :=
  (M.wrapVec 0 ≠ ⊥ ∨ M.wrapLeft 0 0 ≠ ⊥ ∨ M.wrapRight 0 0 ≠ ⊥) ∧
    (M.recurVec 0 ≠ ⊥ ∨ M.recurBase 0 0 ≠ ⊥ ∨ M.recurStep 0 0 ≠ ⊥ ∨ M.recurCounter 0 0 ≠ ⊥)

/-- Proves: the arctic laws are exactly the kept clauses together with the deleted clause pair.
Does not prove: anything about acceptance.
Relation: none. Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: every arctic datum. -/
theorem arcticScalarProjectionLaws_split_deleted (M : arcticScalarProjectionData) :
    arcticScalarProjectionLaws M ↔
      arcticScalarProjectionOtherLaws M ∧ arcticScalarProjectionDeletedLaw M := by
  unfold arcticScalarProjectionLaws arcticScalarProjectionOtherLaws
    arcticScalarProjectionDeletedLaw
  constructor
  · intro h
    exact ⟨⟨h.zero_fin, h.succ_sf⟩, h.wrap_sf, h.recur_sf⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩

/-- Dimension one, the wrapper and the recursor at `−∞` in every entry, the successor the
identity map `n ↦ 0 + n`, and the constant `0`. -/
abbrev arcticMaskFreeDatum : arcticScalarProjectionData where
  d := 0
  zeroVec := aConst 0
  succMat := fun _ _ => ((0 : ℕ) : WithBot ℕ)
  succVec := fun _ => ⊥
  wrapLeft := fun _ _ => ⊥
  wrapRight := fun _ _ => ⊥
  wrapVec := fun _ => ⊥
  recurBase := fun _ _ => ⊥
  recurStep := fun _ _ => ⊥
  recurCounter := fun _ _ => ⊥
  recurVec := fun _ => ⊥

/-- Proves: the action of the all-`−∞` matrix is `−∞` in every coordinate.
Does not prove: anything for other matrices.
Relation: none. Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: arctic vectors of dimension one. -/
theorem aAct_bot_matrix (v : AVec 0) (i : Fin (0 + 1)) :
    aAct (fun _ _ => (⊥ : WithBot ℕ)) v i = ⊥ :=
  (Finset.sup_eq_bot_iff _ _).2 (fun j _ => WithBot.bot_add (v j))

/-- Proves: the wrapper of `arcticMaskFreeDatum` returns the all-`−∞` vector.
Does not prove: anything for other data.
Relation: none. Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: `arcticMaskFreeDatum`. -/
theorem arcticMaskFreeDatum_wrap (x y : AVec 0) :
    arcticMaskFreeDatum.interp.wrap x y = fun _ => ⊥ := by
  funext i
  show max (max (aAct (fun _ _ => (⊥ : WithBot ℕ)) x i) (aAct (fun _ _ => (⊥ : WithBot ℕ)) y i))
    (⊥ : WithBot ℕ) = ⊥
  rw [aAct_bot_matrix, aAct_bot_matrix]
  simp

/-- Proves: the recursor of `arcticMaskFreeDatum` returns the all-`−∞` vector.
Does not prove: anything for other data.
Relation: none. Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: `arcticMaskFreeDatum`. -/
theorem arcticMaskFreeDatum_recur (b s n : AVec 0) :
    arcticMaskFreeDatum.interp.recur b s n = fun _ => ⊥ := by
  funext i
  show max (max (max (aAct (fun _ _ => (⊥ : WithBot ℕ)) b i)
    (aAct (fun _ _ => (⊥ : WithBot ℕ)) s i)) (aAct (fun _ _ => (⊥ : WithBot ℕ)) n i))
    (⊥ : WithBot ℕ) = ⊥
  rw [aAct_bot_matrix, aAct_bot_matrix, aAct_bot_matrix]
  simp

/-- Proves: the successor of `arcticMaskFreeDatum` keeps the all-`−∞` vector.
Does not prove: anything for finite arguments.
Relation: none. Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: `arcticMaskFreeDatum`. -/
theorem arcticMaskFreeDatum_succ_bot :
    arcticMaskFreeDatum.interp.succ (fun _ => ⊥) = fun _ => ⊥ := by
  funext i
  show max (aAct (fun _ _ => ((0 : ℕ) : WithBot ℕ)) (fun _ => (⊥ : WithBot ℕ)) i)
    (⊥ : WithBot ℕ) = ⊥
  have h : aAct (d := 0) (fun _ _ => ((0 : ℕ) : WithBot ℕ)) (fun _ => (⊥ : WithBot ℕ)) i = ⊥ :=
    (Finset.sup_eq_bot_iff _ _).2 (fun j _ => WithBot.add_bot _)
  rw [h]
  simp

/-- Proves: plugging a term whose value is the all-`−∞` vector into any one-hole context gives the
all-`−∞` vector under `arcticMaskFreeDatum`.
Does not prove: anything for other data.
Relation: none; values of plugged contexts.
Closure: one-hole constructor contexts. Strategy: not applicable.
Trust: kernel only.
Scope: `arcticMaskFreeDatum`, every valuation. -/
theorem arcticMaskFreeDatum_plug_bot (ρ : ℕ → AVec 0) (C : FreeContext ℕ) (t : FreeTerm ℕ)
    (ht : arcticMaskFreeDatum.interp.eval ρ t = fun _ => ⊥) :
    arcticMaskFreeDatum.interp.eval ρ (C.plug t) = fun _ => ⊥ := by
  induction C with
  | hole => exact ht
  | succ C ih =>
      show arcticMaskFreeDatum.interp.succ (arcticMaskFreeDatum.interp.eval ρ (C.plug t)) = _
      rw [ih]
      exact arcticMaskFreeDatum_succ_bot
  | wrapLeft C r _ => exact arcticMaskFreeDatum_wrap _ _
  | wrapRight l C _ => exact arcticMaskFreeDatum_wrap _ _
  | recurBase C s n _ => exact arcticMaskFreeDatum_recur _ _ _
  | recurStep b C n _ => exact arcticMaskFreeDatum_recur _ _ _
  | recurCounter b s C _ => exact arcticMaskFreeDatum_recur _ _ _

/-- Proves: `arcticMaskFreeDatum` is accepted: both sides of every contextual instance of the
duplicating rule take the all-`−∞` value, and `−∞ ≫ −∞` holds in every coordinate.
Does not prove: acceptance by any lawful datum; `arcticScalarProjection_universal` excludes it.
Relation: `DupCtxStep`, the duplicating rule under one-hole contexts.
Closure: one-hole constructor contexts. Strategy: full.
Trust: kernel only.
Scope: `arcticMaskFreeDatum`, every valuation into `ℕ × A^0`. -/
theorem arcticMaskFreeDatum_accepts : arcticScalarProjectionAccepts arcticMaskFreeDatum := by
  intro ρ _ a c hac
  cases hac with
  | lift C b s n =>
      rw [arcticMaskFreeDatum_plug_bot ρ C (.wrap s (.recur b s n)) (arcticMaskFreeDatum_wrap
          (arcticMaskFreeDatum.interp.eval ρ s)
          (arcticMaskFreeDatum.interp.eval ρ (.recur b s n))),
        arcticMaskFreeDatum_plug_bot ρ C (.recur b s (.succ n)) (arcticMaskFreeDatum_recur
          (arcticMaskFreeDatum.interp.eval ρ b) (arcticMaskFreeDatum.interp.eval ρ s)
          (arcticMaskFreeDatum.interp.eval ρ (.succ n)))]
      intro i
      exact Or.inr ⟨rfl, rfl⟩

/-- The countermodel of the deleted clause pair: `zero_fin` and `succ_sf` hold, `wrap_sf` fails,
and the datum is accepted. -/
def arcticScalarProjectionCountermodel :
    DeletedPremiseCountermodel arcticScalarProjectionOtherLaws arcticScalarProjectionDeletedLaw
      arcticScalarProjectionAccepts where
  datum := arcticMaskFreeDatum
  other := ⟨WithBot.coe_ne_bot, Or.inr WithBot.coe_ne_bot⟩
  deletedFails := fun h => by
    rcases h.1 with h1 | h1 | h1 <;> exact h1 rfl
  accepts := arcticMaskFreeDatum_accepts

/-- Stop line `LEAN_REFUTATION` of the law-free reading of the arctic row.
Proves: the arctic barrier is false without the laws: `arcticMaskFreeDatum` is accepted.
Does not prove: that any single law clause is removable; `arcticScalarProjection_partA_barrier`
and `arcticScalarProjection_partB_barrier` show it is not.
Relation: `DupCtxStep`. Closure: one-hole constructor contexts. Strategy: full.
Trust: kernel only.
Scope: arctic data of every dimension. -/
theorem arcticScalarProjection_lawFree_barrier_false :
    ¬ ∀ M : arcticScalarProjectionData, ¬ arcticScalarProjectionAccepts M :=
  fun h => h arcticMaskFreeDatum arcticMaskFreeDatum_accepts

/-- Proves: no control makes the arctic row a `UniversalBarrierNecessity` row.
Does not prove: anything about the other rows.
Relation: `DupCtxStep`. Closure: one-hole constructor contexts. Strategy: full.
Trust: kernel only.
Scope: the arctic row. -/
theorem arcticScalarProjection_not_universalBarrier (Control : Prop) :
    ¬ UniversalBarrierNecessity arcticScalarProjectionLaws arcticScalarProjectionAccepts Control :=
  fun h => arcticScalarProjection_lawFree_barrier_false h.2.1

/-- Contextual-masking control: a lawful arctic member orients every root instance of the
duplicating rule on `ℕ × A^d` and fails at the contextual relation of the row. -/
def arcticScalarProjectionContextControl : Prop :=
  ∃ M : arcticScalarProjectionData, arcticScalarProjectionLaws M ∧
    DupOrientedOn AFin M.interp arcLt ∧ ¬ arcticScalarProjectionAccepts M

/-- Proves: `arcticScalarProjectionContextControl`, by the lawful witness of the row.
Does not prove: orientation at the contextual relation.
Relation: the duplicating rule at the root and under one-hole contexts.
Closure: root for the orientation, one-hole contexts for the failure. Strategy: full.
Trust: kernel only.
Scope: `arcticScalarProjectionWitness`. -/
theorem arcticScalarProjection_contextControl : arcticScalarProjectionContextControl :=
  ⟨arcticScalarProjectionWitness, arcticScalarProjectionWitness_laws,
    arcticScalarProjectionWitness_root, arcticScalarProjectionWitness_result⟩

/-- Necessity statement of the arctic row: the clause pair `wrap_sf`, `recur_sf` is a barrier
premise whose deletion admits an accepted countermodel; the laws split into two parts, each of
which forces the barrier alone; and both the nonduplicating control and the contextual-masking
control hold. -/
def arcticScalarProjectionNecessityStatement : Prop :=
  BarrierPremiseNecessity arcticScalarProjectionLaws arcticScalarProjectionOtherLaws
      arcticScalarProjectionDeletedLaw arcticScalarProjectionAccepts ∧
    CoveredBarrierNecessity arcticScalarProjectionLaws arcticScalarProjectionPartA
      arcticScalarProjectionPartB arcticScalarProjectionAccepts
      (arcticScalarProjectionNonduplicatingControl ∧ arcticScalarProjectionContextControl)

/-- Proves: `arcticScalarProjectionNecessityStatement`.
Does not prove: a law-free barrier; `arcticScalarProjection_lawFree_barrier_false` refutes it.
Relation: `DupCtxStep`. Closure: one-hole constructor contexts. Strategy: full.
Trust: kernel only.
Scope: the arctic row. -/
theorem arcticScalarProjection_necessity : arcticScalarProjectionNecessityStatement :=
  ⟨⟨arcticScalarProjectionLaws_split_deleted, fun M hM => arcticScalarProjection_universal M hM,
      ⟨arcticScalarProjectionCountermodel⟩⟩,
    arcticScalarProjectionLaws_split,
    ⟨arcticScalarProjectionWitness, arcticScalarProjectionWitness_laws⟩,
    arcticScalarProjection_partA_barrier, arcticScalarProjection_partB_barrier,
    ⟨arcticScalarProjection_nonduplicatingControl, arcticScalarProjection_contextControl⟩⟩

/-! ## tropicalScalarProjection

The row is a barrier-premise row, dual to the arctic row. The datum `tropicalMaskFreeDatum`, whose
wrapper and recursor are `+∞` at every entry, keeps `zero_fin` and `succ_sf` and is accepted, so
the barrier is false with the clause pair `wrap_sf`, `recur_sf` deleted
(`tropicalScalarProjection_lawFree_barrier_false`). No single clause is removable, and the lawful
witness orients every root instance and fails at the contextual relation. -/

/-- Necessity class of the tropical row: a barrier premise, the clause pair `wrap_sf`,
`recur_sf`. Changed from `lawFreeBarrierControl` by
`tropicalScalarProjection_lawFree_barrier_false`. -/
def tropicalScalarProjectionNecessityKind : RowNecessityKind := .deletedBarrierPremise

/-- Part A of `TropicalLaws`: the clause `wrap_sf`. -/
def tropicalScalarProjectionPartA (M : tropicalScalarProjectionData) : Prop :=
  M.wrapVec 0 ≠ ⊤ ∨ M.wrapLeft 0 0 ≠ ⊤ ∨ M.wrapRight 0 0 ≠ ⊤

/-- Part B of `TropicalLaws`: the clauses `zero_fin`, `succ_sf` and `recur_sf`. -/
def tropicalScalarProjectionPartB (M : tropicalScalarProjectionData) : Prop :=
  M.zeroVec 0 ≠ ⊤ ∧ (M.succVec 0 ≠ ⊤ ∨ M.succMat 0 0 ≠ ⊤) ∧
    (M.recurVec 0 ≠ ⊤ ∨ M.recurBase 0 0 ≠ ⊤ ∨ M.recurStep 0 0 ≠ ⊤ ∨ M.recurCounter 0 0 ≠ ⊤)

theorem tropicalScalarProjectionLaws_split (M : tropicalScalarProjectionData) :
    tropicalScalarProjectionLaws M ↔
      tropicalScalarProjectionPartA M ∧ tropicalScalarProjectionPartB M := by
  unfold tropicalScalarProjectionLaws tropicalScalarProjectionPartA tropicalScalarProjectionPartB
  constructor
  · intro h
    exact ⟨h.wrap_sf, h.zero_fin, h.succ_sf, h.recur_sf⟩
  · rintro ⟨hA, h1, h2, h3⟩
    exact ⟨h1, h2, hA, h3⟩

theorem tAct_tConst_zero_le {d : ℕ} (A : TMat d) (v : TVec d) :
    tAct A (tConst 0) 0 ≤ tAct A v 0 :=
  Finset.le_inf (fun j _ => le_trans
    (Finset.inf_le (f := fun j => A 0 j + tConst 0 j) (Finset.mem_univ j))
    (add_le_add_left (wt_zero_le (v j)) _))

/-- Strict decrease at both wrapper contexts with zero arguments, for any two values `R` and `L`
in the hole, forces the wrapper's two zero-argument actions and its constant to be `+∞`. -/
theorem tropical_wrap_tops (M : TropicalData) (R L : TVec M.d)
    (k1 : tropLt (M.interp.wrap (tConst 0) R) (M.interp.wrap (tConst 0) L))
    (k2 : tropLt (M.interp.wrap R (tConst 0)) (M.interp.wrap L (tConst 0))) :
    tAct M.wrapLeft (tConst 0) 0 = ⊤ ∧ tAct M.wrapRight (tConst 0) 0 = ⊤ ∧ M.wrapVec 0 = ⊤ := by
  have ew : ∀ s y : TVec M.d, M.interp.wrap s y 0 =
      min (min (tAct M.wrapLeft s 0) (tAct M.wrapRight y 0)) (M.wrapVec 0) := fun _ _ => rfl
  have h1 := k1 0
  have h2 := k2 0
  rw [ew, ew] at h1
  rw [ew, ew] at h2
  rcases h1 with h1 | ⟨h1, -⟩ <;> rcases h2 with h2 | ⟨h2, -⟩
  · exact (lt_asymm (lt_of_le_of_lt (tAct_tConst_zero_le M.wrapRight R) (min3_lt_right h1))
      (lt_of_le_of_lt (tAct_tConst_zero_le M.wrapLeft R) (min3_lt_left h2))).elim
  · have hB := (min_eq_top.1 (min_eq_top.1 h2).1).2
    have hlt := lt_of_le_of_lt (tAct_tConst_zero_le M.wrapRight R) (min3_lt_right h1)
    rw [hB] at hlt
    exact (not_top_lt hlt).elim
  · have hA := (min_eq_top.1 (min_eq_top.1 h1).1).1
    have hlt := lt_of_le_of_lt (tAct_tConst_zero_le M.wrapLeft R) (min3_lt_left h2)
    rw [hA] at hlt
    exact (not_top_lt hlt).elim
  · exact ⟨(min_eq_top.1 (min_eq_top.1 h1).1).1, (min_eq_top.1 (min_eq_top.1 h2).1).2,
      (min_eq_top.1 h1).2⟩

/-- Part A alone forces the barrier. -/
theorem tropicalScalarProjection_partA_barrier (M : tropicalScalarProjectionData)
    (hA : tropicalScalarProjectionPartA M) : ¬ tropicalScalarProjectionAccepts M := by
  intro hacc
  have hz : TFin (tConst 0 : TVec M.d) := WithTop.coe_ne_top
  have hk := dupCtx_wrap_instances TFin M.interp tropLt hacc (tConst 0) (tConst 0) (tConst 0)
    (tConst 0) hz hz hz hz
  obtain ⟨hWL, hWR, hc⟩ := tropical_wrap_tops M _ _ hk.1 hk.2
  rcases hA with h | h | h
  · exact h hc
  · exact ne_top_of_le_ne_top (tfin_add h hz) (tAct_le_diag _ _) hWL
  · exact ne_top_of_le_ne_top (tfin_add h hz) (tAct_le_diag _ _) hWR

/-- Part B alone forces the barrier: the wrapper contexts force the wrapper to be `+∞` at the zero
arguments, so the right side of the root instance is `+∞`, while `succ_sf` and `recur_sf` keep the
left side finite. -/
theorem tropicalScalarProjection_partB_barrier (M : tropicalScalarProjectionData)
    (hB : tropicalScalarProjectionPartB M) : ¬ tropicalScalarProjectionAccepts M := by
  intro hacc
  obtain ⟨-, hs, hr⟩ := hB
  have hz : TFin (tConst 0 : TVec M.d) := WithTop.coe_ne_top
  have hk := dupCtx_wrap_instances TFin M.interp tropLt hacc (tConst 0) (tConst 0) (tConst 0)
    (tConst 0) hz hz hz hz
  obtain ⟨hWL, hWR, hc⟩ := tropical_wrap_tops M _ _ hk.1 hk.2
  have hole : tropLt (M.interp.wrap (tConst 0) (M.interp.recur (tConst 0) (tConst 0) (tConst 0)))
      (M.interp.recur (tConst 0) (tConst 0) (M.interp.succ (tConst 0))) :=
    hacc (fun _ => tConst 0) (fun _ => hz) _ _ (DupCtxStep.lift .hole (.var 0) (.var 0) (.var 0))
  have hsucc : M.interp.succ (tConst 0) 0 ≠ ⊤ := by
    show min (tAct M.succMat (tConst 0) 0) (M.succVec 0) ≠ ⊤
    rcases hs with h | h
    · exact ne_top_of_le_ne_top h (min_le_right _ _)
    · exact ne_top_of_le_ne_top (tfin_add h hz) (le_trans (min_le_left _ _) (tAct_le_diag _ _))
  have hL : M.interp.recur (tConst 0) (tConst 0) (M.interp.succ (tConst 0)) 0 ≠ ⊤ := by
    show min (min (min (tAct M.recurBase (tConst 0) 0) (tAct M.recurStep (tConst 0) 0))
      (tAct M.recurCounter (M.interp.succ (tConst 0)) 0)) (M.recurVec 0) ≠ ⊤
    rcases hr with h | h | h | h
    · exact ne_top_of_le_ne_top h (min_le_right _ _)
    · exact ne_top_of_le_ne_top (tfin_add h hz)
        (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
          (le_trans (min_le_left _ _) (tAct_le_diag _ _))))
    · exact ne_top_of_le_ne_top (tfin_add h hz)
        (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
          (le_trans (min_le_right _ _) (tAct_le_diag _ _))))
    · exact ne_top_of_le_ne_top (tfin_add h hsucc)
        (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (tAct_le_diag _ _)))
  have hmono : ⊤ ≤ tAct M.wrapRight (M.interp.recur (tConst 0) (tConst 0) (tConst 0)) 0 := by
    rw [← hWR]
    exact tAct_tConst_zero_le _ _
  have hR : M.interp.wrap (tConst 0) (M.interp.recur (tConst 0) (tConst 0) (tConst 0)) 0 = ⊤ := by
    show min (min (tAct M.wrapLeft (tConst 0) 0)
      (tAct M.wrapRight (M.interp.recur (tConst 0) (tConst 0) (tConst 0)) 0)) (M.wrapVec 0) = ⊤
    simp only [hWL, hc, top_le_iff.1 hmono, min_self]
  rcases hole 0 with h | ⟨_, h⟩
  · rw [hR] at h
    exact not_top_lt h
  · exact hL h

/-- Nonduplicating control: a lawful tropical member orients the rule `succ x → x` at the root on
the domain with finite first coordinate. -/
def tropicalScalarProjectionNonduplicatingControl : Prop :=
  ∃ M : tropicalScalarProjectionData, tropicalScalarProjectionLaws M ∧
    ∀ ρ : Fin 1 → TVec M.d, (∀ i, TFin (ρ i)) →
      tropLt (M.interp.eval ρ (.var 0)) (M.interp.eval ρ (.succ (.var 0)))

theorem tropicalScalarProjection_nonduplicatingControl :
    tropicalScalarProjectionNonduplicatingControl :=
  ⟨tropicalScalarProjectionWitness, tropicalScalarProjectionWitness_laws, fun ρ hρ i => by
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    left
    show ρ 0 0 < tropicalScalarProjectionWitness.interp.succ (ρ 0) 0
    rw [tropW_succ]
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (hρ 0)
    rw [← hk]
    exact wt_coe_lt_one_add k⟩

/-- The contextual relation of the row rejects the nonduplicating rule as well. -/
theorem tropicalScalarProjection_nonduplicating_context_rejected
    (M : tropicalScalarProjectionData) (hM : tropicalScalarProjectionLaws M) :
    ¬ ∀ ρ : ℕ → TVec M.d, (∀ j, TFin (ρ j)) → ∀ C : FreeContext ℕ,
      tropLt (M.interp.eval ρ (C.plug (.var 0))) (M.interp.eval ρ (C.plug (.succ (.var 0)))) := by
  intro h
  have hz : TFin (tConst 0 : TVec M.d) := WithTop.coe_ne_top
  obtain ⟨hWL, hWR, hc⟩ := tropical_wrap_tops M (tConst 0) (M.interp.succ (tConst 0))
    (h (fun _ => tConst 0) (fun _ => hz) (.wrapRight (.var 0) .hole))
    (h (fun _ => tConst 0) (fun _ => hz) (.wrapLeft .hole (.var 0)))
  rcases (show TropicalLaws M from hM).wrap_sf with h' | h' | h'
  · exact h' hc
  · exact ne_top_of_le_ne_top (tfin_add h' hz) (tAct_le_diag _ _) hWL
  · exact ne_top_of_le_ne_top (tfin_add h' hz) (tAct_le_diag _ _) hWR

/-- The clauses `zero_fin` and `succ_sf` of `TropicalLaws`, kept by the deleted-premise
countermodel. -/
def tropicalScalarProjectionOtherLaws (M : tropicalScalarProjectionData) : Prop :=
  M.zeroVec 0 ≠ ⊤ ∧ (M.succVec 0 ≠ ⊤ ∨ M.succMat 0 0 ≠ ⊤)

/-- The deleted barrier premise: the clauses `wrap_sf` and `recur_sf` of `TropicalLaws`. -/
def tropicalScalarProjectionDeletedLaw (M : tropicalScalarProjectionData) : Prop :=
  (M.wrapVec 0 ≠ ⊤ ∨ M.wrapLeft 0 0 ≠ ⊤ ∨ M.wrapRight 0 0 ≠ ⊤) ∧
    (M.recurVec 0 ≠ ⊤ ∨ M.recurBase 0 0 ≠ ⊤ ∨ M.recurStep 0 0 ≠ ⊤ ∨ M.recurCounter 0 0 ≠ ⊤)

/-- Proves: the tropical laws are exactly the kept clauses together with the deleted clause
pair.
Does not prove: anything about acceptance.
Relation: none. Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: every tropical datum. -/
theorem tropicalScalarProjectionLaws_split_deleted (M : tropicalScalarProjectionData) :
    tropicalScalarProjectionLaws M ↔
      tropicalScalarProjectionOtherLaws M ∧ tropicalScalarProjectionDeletedLaw M := by
  unfold tropicalScalarProjectionLaws tropicalScalarProjectionOtherLaws
    tropicalScalarProjectionDeletedLaw
  constructor
  · intro h
    exact ⟨⟨h.zero_fin, h.succ_sf⟩, h.wrap_sf, h.recur_sf⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩

/-- Dimension one, the wrapper and the recursor at `+∞` in every entry, the successor the
identity map `n ↦ 0 + n`, and the constant `0`. -/
abbrev tropicalMaskFreeDatum : tropicalScalarProjectionData where
  d := 0
  zeroVec := tConst 0
  succMat := fun _ _ => ((0 : ℕ) : WithTop ℕ)
  succVec := fun _ => ⊤
  wrapLeft := fun _ _ => ⊤
  wrapRight := fun _ _ => ⊤
  wrapVec := fun _ => ⊤
  recurBase := fun _ _ => ⊤
  recurStep := fun _ _ => ⊤
  recurCounter := fun _ _ => ⊤
  recurVec := fun _ => ⊤

/-- Proves: the action of the all-`+∞` matrix is `+∞` in every coordinate.
Does not prove: anything for other matrices.
Relation: none. Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: tropical vectors of dimension one. -/
theorem tAct_top_matrix (v : TVec 0) (i : Fin (0 + 1)) :
    tAct (fun _ _ => (⊤ : WithTop ℕ)) v i = ⊤ :=
  (Finset.inf_eq_top_iff _ _).2 (fun j _ => WithTop.top_add (v j))

/-- Proves: the wrapper of `tropicalMaskFreeDatum` returns the all-`+∞` vector.
Does not prove: anything for other data.
Relation: none. Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: `tropicalMaskFreeDatum`. -/
theorem tropicalMaskFreeDatum_wrap (x y : TVec 0) :
    tropicalMaskFreeDatum.interp.wrap x y = fun _ => ⊤ := by
  funext i
  show min (min (tAct (fun _ _ => (⊤ : WithTop ℕ)) x i) (tAct (fun _ _ => (⊤ : WithTop ℕ)) y i))
    (⊤ : WithTop ℕ) = ⊤
  rw [tAct_top_matrix, tAct_top_matrix]
  simp

/-- Proves: the recursor of `tropicalMaskFreeDatum` returns the all-`+∞` vector.
Does not prove: anything for other data.
Relation: none. Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: `tropicalMaskFreeDatum`. -/
theorem tropicalMaskFreeDatum_recur (b s n : TVec 0) :
    tropicalMaskFreeDatum.interp.recur b s n = fun _ => ⊤ := by
  funext i
  show min (min (min (tAct (fun _ _ => (⊤ : WithTop ℕ)) b i)
    (tAct (fun _ _ => (⊤ : WithTop ℕ)) s i)) (tAct (fun _ _ => (⊤ : WithTop ℕ)) n i))
    (⊤ : WithTop ℕ) = ⊤
  rw [tAct_top_matrix, tAct_top_matrix, tAct_top_matrix]
  simp

/-- Proves: the successor of `tropicalMaskFreeDatum` keeps the all-`+∞` vector.
Does not prove: anything for finite arguments.
Relation: none. Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: `tropicalMaskFreeDatum`. -/
theorem tropicalMaskFreeDatum_succ_top :
    tropicalMaskFreeDatum.interp.succ (fun _ => ⊤) = fun _ => ⊤ := by
  funext i
  show min (tAct (fun _ _ => ((0 : ℕ) : WithTop ℕ)) (fun _ => (⊤ : WithTop ℕ)) i)
    (⊤ : WithTop ℕ) = ⊤
  have h : tAct (d := 0) (fun _ _ => ((0 : ℕ) : WithTop ℕ)) (fun _ => (⊤ : WithTop ℕ)) i = ⊤ :=
    (Finset.inf_eq_top_iff _ _).2 (fun j _ => WithTop.add_top _)
  rw [h]
  simp

/-- Proves: plugging a term whose value is the all-`+∞` vector into any one-hole context gives
the all-`+∞` vector under `tropicalMaskFreeDatum`.
Does not prove: anything for other data.
Relation: none; values of plugged contexts.
Closure: one-hole constructor contexts. Strategy: not applicable.
Trust: kernel only.
Scope: `tropicalMaskFreeDatum`, every valuation. -/
theorem tropicalMaskFreeDatum_plug_top (ρ : ℕ → TVec 0) (C : FreeContext ℕ) (t : FreeTerm ℕ)
    (ht : tropicalMaskFreeDatum.interp.eval ρ t = fun _ => ⊤) :
    tropicalMaskFreeDatum.interp.eval ρ (C.plug t) = fun _ => ⊤ := by
  induction C with
  | hole => exact ht
  | succ C ih =>
      show tropicalMaskFreeDatum.interp.succ (tropicalMaskFreeDatum.interp.eval ρ (C.plug t)) = _
      rw [ih]
      exact tropicalMaskFreeDatum_succ_top
  | wrapLeft C r _ => exact tropicalMaskFreeDatum_wrap _ _
  | wrapRight l C _ => exact tropicalMaskFreeDatum_wrap _ _
  | recurBase C s n _ => exact tropicalMaskFreeDatum_recur _ _ _
  | recurStep b C n _ => exact tropicalMaskFreeDatum_recur _ _ _
  | recurCounter b s C _ => exact tropicalMaskFreeDatum_recur _ _ _

/-- Proves: `tropicalMaskFreeDatum` is accepted: both sides of every contextual instance of the
duplicating rule take the all-`+∞` value, and the dual strict order holds at `+∞` against `+∞`.
Does not prove: acceptance by any lawful datum; `tropicalScalarProjection_universal` excludes
it.
Relation: `DupCtxStep`, the duplicating rule under one-hole contexts.
Closure: one-hole constructor contexts. Strategy: full.
Trust: kernel only.
Scope: `tropicalMaskFreeDatum`, every valuation into the domain with finite first coordinate. -/
theorem tropicalMaskFreeDatum_accepts :
    tropicalScalarProjectionAccepts tropicalMaskFreeDatum := by
  intro ρ _ a c hac
  cases hac with
  | lift C b s n =>
      rw [tropicalMaskFreeDatum_plug_top ρ C (.wrap s (.recur b s n)) (tropicalMaskFreeDatum_wrap
          (tropicalMaskFreeDatum.interp.eval ρ s)
          (tropicalMaskFreeDatum.interp.eval ρ (.recur b s n))),
        tropicalMaskFreeDatum_plug_top ρ C (.recur b s (.succ n)) (tropicalMaskFreeDatum_recur
          (tropicalMaskFreeDatum.interp.eval ρ b) (tropicalMaskFreeDatum.interp.eval ρ s)
          (tropicalMaskFreeDatum.interp.eval ρ (.succ n)))]
      intro i
      exact Or.inr ⟨rfl, rfl⟩

/-- The countermodel of the deleted clause pair: `zero_fin` and `succ_sf` hold, `wrap_sf` fails,
and the datum is accepted. -/
def tropicalScalarProjectionCountermodel :
    DeletedPremiseCountermodel tropicalScalarProjectionOtherLaws
      tropicalScalarProjectionDeletedLaw tropicalScalarProjectionAccepts where
  datum := tropicalMaskFreeDatum
  other := ⟨WithTop.coe_ne_top, Or.inr WithTop.coe_ne_top⟩
  deletedFails := fun h => by
    rcases h.1 with h1 | h1 | h1 <;> exact h1 rfl
  accepts := tropicalMaskFreeDatum_accepts

/-- Stop line `LEAN_REFUTATION` of the law-free reading of the tropical row.
Proves: the tropical barrier is false without the laws: `tropicalMaskFreeDatum` is accepted.
Does not prove: that any single law clause is removable;
`tropicalScalarProjection_partA_barrier` and `tropicalScalarProjection_partB_barrier` show it is
not.
Relation: `DupCtxStep`. Closure: one-hole constructor contexts. Strategy: full.
Trust: kernel only.
Scope: tropical data of every dimension. -/
theorem tropicalScalarProjection_lawFree_barrier_false :
    ¬ ∀ M : tropicalScalarProjectionData, ¬ tropicalScalarProjectionAccepts M :=
  fun h => h tropicalMaskFreeDatum tropicalMaskFreeDatum_accepts

/-- Proves: no control makes the tropical row a `UniversalBarrierNecessity` row.
Does not prove: anything about the other rows.
Relation: `DupCtxStep`. Closure: one-hole constructor contexts. Strategy: full.
Trust: kernel only.
Scope: the tropical row. -/
theorem tropicalScalarProjection_not_universalBarrier (Control : Prop) :
    ¬ UniversalBarrierNecessity tropicalScalarProjectionLaws tropicalScalarProjectionAccepts
      Control :=
  fun h => tropicalScalarProjection_lawFree_barrier_false h.2.1

/-- Contextual-masking control: a lawful tropical member orients every root instance of the
duplicating rule on the domain with finite first coordinate and fails at the contextual relation
of the row. -/
def tropicalScalarProjectionContextControl : Prop :=
  ∃ M : tropicalScalarProjectionData, tropicalScalarProjectionLaws M ∧
    DupOrientedOn TFin M.interp tropLt ∧ ¬ tropicalScalarProjectionAccepts M

/-- Proves: `tropicalScalarProjectionContextControl`, by the lawful witness of the row.
Does not prove: orientation at the contextual relation.
Relation: the duplicating rule at the root and under one-hole contexts.
Closure: root for the orientation, one-hole contexts for the failure. Strategy: full.
Trust: kernel only.
Scope: `tropicalScalarProjectionWitness`. -/
theorem tropicalScalarProjection_contextControl : tropicalScalarProjectionContextControl :=
  ⟨tropicalScalarProjectionWitness, tropicalScalarProjectionWitness_laws,
    tropicalScalarProjectionWitness_root, tropicalScalarProjectionWitness_result⟩

/-- Necessity statement of the tropical row: the clause pair `wrap_sf`, `recur_sf` is a barrier
premise whose deletion admits an accepted countermodel; the laws split into two parts, each of
which forces the barrier alone; and both the nonduplicating control and the contextual-masking
control hold. -/
def tropicalScalarProjectionNecessityStatement : Prop :=
  BarrierPremiseNecessity tropicalScalarProjectionLaws tropicalScalarProjectionOtherLaws
      tropicalScalarProjectionDeletedLaw tropicalScalarProjectionAccepts ∧
    CoveredBarrierNecessity tropicalScalarProjectionLaws tropicalScalarProjectionPartA
      tropicalScalarProjectionPartB tropicalScalarProjectionAccepts
      (tropicalScalarProjectionNonduplicatingControl ∧ tropicalScalarProjectionContextControl)

/-- Proves: `tropicalScalarProjectionNecessityStatement`.
Does not prove: a law-free barrier; `tropicalScalarProjection_lawFree_barrier_false` refutes
it.
Relation: `DupCtxStep`. Closure: one-hole constructor contexts. Strategy: full.
Trust: kernel only.
Scope: the tropical row. -/
theorem tropicalScalarProjection_necessity : tropicalScalarProjectionNecessityStatement :=
  ⟨⟨tropicalScalarProjectionLaws_split_deleted,
      fun M hM => tropicalScalarProjection_universal M hM,
      ⟨tropicalScalarProjectionCountermodel⟩⟩,
    tropicalScalarProjectionLaws_split,
    ⟨tropicalScalarProjectionWitness, tropicalScalarProjectionWitness_laws⟩,
    tropicalScalarProjection_partA_barrier, tropicalScalarProjection_partB_barrier,
    ⟨tropicalScalarProjection_nonduplicatingControl, tropicalScalarProjection_contextControl⟩⟩

/-! ## triangularMatrix -/

def triangularMatrixNecessityKind : RowNecessityKind := .deletedBarrierPremise

/-- The eleven clauses of `TriangularLaws`, with `matrix` unfolded, other than
`matrix.wrapLeft_pos`. -/
def triangularMatrixOtherLaws (M : triangularMatrixData) : Prop :=
  1 ≤ M.succMat 0 0 ∧ 1 ≤ M.wrapRight 0 0 ∧ 1 ≤ M.recurBase 0 0 ∧ 1 ≤ M.recurStep 0 0 ∧
    1 ≤ M.recurCounter 0 0 ∧ UpperTri M.succMat ∧ UpperTri M.wrapLeft ∧ UpperTri M.wrapRight ∧
    UpperTri M.recurBase ∧ UpperTri M.recurStep ∧ UpperTri M.recurCounter

/-- The deleted clause `matrix.wrapLeft_pos`. -/
def triangularMatrixDeletedLaw (M : triangularMatrixData) : Prop := 1 ≤ M.wrapLeft 0 0

theorem triangularMatrixLaws_split (M : triangularMatrixData) :
    triangularMatrixLaws M ↔ triangularMatrixOtherLaws M ∧ triangularMatrixDeletedLaw M := by
  unfold triangularMatrixLaws triangularMatrixOtherLaws triangularMatrixDeletedLaw
  constructor
  · intro h
    exact ⟨⟨h.matrix.succ_pos, h.matrix.wrapRight_pos, h.matrix.recurBase_pos,
      h.matrix.recurStep_pos, h.matrix.recurCounter_pos, h.succ_tri, h.wrapLeft_tri,
      h.wrapRight_tri, h.recurBase_tri, h.recurStep_tri, h.recurCounter_tri⟩, h.matrix.wrapLeft_pos⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, h12⟩
    exact ⟨⟨h1, h12, h2, h3, h4, h5⟩, h6, h7, h8, h9, h10, h11⟩

/-- The witness with wrapper payload matrix `0`, which is upper triangular. -/
def triangularMatrixCountermodel :
    DeletedPremiseCountermodel triangularMatrixOtherLaws triangularMatrixDeletedLaw
      triangularMatrixAccepts where
  datum := { triangularMatrixWitness with wrapLeft := 0 }
  other := by
    unfold triangularMatrixOtherLaws UpperTri
    decide
  deletedFails := by
    unfold triangularMatrixDeletedLaw
    decide
  accepts := matrixNScalarProjection_mutation.2

def triangularMatrixNecessityStatement : Prop :=
  BarrierPremiseNecessity triangularMatrixLaws triangularMatrixOtherLaws triangularMatrixDeletedLaw
    triangularMatrixAccepts

theorem triangularMatrix_necessity : triangularMatrixNecessityStatement :=
  ⟨triangularMatrixLaws_split, fun M hM => triangularMatrix_universal M hM,
    ⟨triangularMatrixCountermodel⟩⟩

/-! ## tupleInterpretationStrictS -/

def tupleInterpretationStrictSNecessityKind : RowNecessityKind := .deletedEscapeFeature

deriving instance Countable for MExpr

/-- A fixed bijection between the recursor component tables of dimension `m + 1` and `ℕ`. -/
noncomputable def tupleRecurCode (m : ℕ) : (Fin (m + 1) → MExpr (Fin 3 × Fin (m + 1))) ≃ ℕ :=
  haveI : Infinite (MExpr (Fin 3 × Fin (m + 1))) :=
    Infinite.of_injective (MExpr.const (V := Fin 3 × Fin (m + 1))) (fun _ _ h => MExpr.const.inj h)
  Classical.choice nonempty_equiv_of_countable

/-- The recursor field of a tuple interpretation, read through `tupleRecurCode`. -/
noncomputable def tupleInterpretationStrictSRecurLens :
    FeatureLens tupleInterpretationStrictSData ℕ where
  get M := tupleRecurCode M.m M.recur
  set M v := { M with recur := (tupleRecurCode M.m).symm v }
  get_set M v := (tupleRecurCode M.m).apply_symm_apply v
  set_get M := by
    show { M with recur := (tupleRecurCode M.m).symm (tupleRecurCode M.m M.recur) } = M
    rw [Equiv.symm_apply_apply]
  set_set _ _ _ := rfl

theorem tupleInterpretationStrictSRecurLens_set_code (M : tupleInterpretationStrictSData)
    (r : Fin (M.m + 1) → MExpr (Fin 3 × Fin (M.m + 1))) :
    tupleInterpretationStrictSRecurLens.set M (tupleRecurCode M.m r) = { M with recur := r } := by
  show { M with recur := (tupleRecurCode M.m).symm (tupleRecurCode M.m r) } = { M with recur := r }
  rw [Equiv.symm_apply_apply]

/-- The witness recursor with the coupling removed from its first component. -/
def tupleUncoupledRecur :
    Fin (tupleInterpretationStrictSWitness.m + 1) →
      MExpr (Fin 3 × Fin (tupleInterpretationStrictSWitness.m + 1)) :=
  ![.add (.add (.add (.var (0, 0)) (.var (2, 0))) (.var (1, 0))) (.const 1),
    .add (.var (0, 1)) (.mul (.add (.var (2, 1)) (.const 1)) (.add (.var (1, 1)) (.const 1)))]

theorem tupleUncoupledRecur_ne : tupleUncoupledRecur ≠ tupleInterpretationStrictSWitness.recur := by
  intro h
  have h0 := congrFun h 0
  cases h0

theorem tupleUncoupled_laws :
    tupleInterpretationStrictSLaws
      { tupleInterpretationStrictSWitness with recur := tupleUncoupledRecur } := by
  have hW : TupleLaws tupleInterpretationStrictSWitness := tupleInterpretationStrictSWitness_laws
  refine ⟨hW.succ_first, hW.wrap_first_left, hW.wrap_first_right, ?_, ?_, ?_⟩
  · intro b s n a ha
    show Function.update b 0 a 0 + n 0 + s 0 + 1 < b 0 + n 0 + s 0 + 1
    rw [Function.update_apply, if_pos rfl]
    omega
  · intro b s n a ha
    show b 0 + n 0 + Function.update s 0 a 0 + 1 < b 0 + n 0 + s 0 + 1
    rw [Function.update_apply, if_pos rfl]
    omega
  · intro b s n a ha
    show b 0 + Function.update n 0 a 0 + s 0 + 1 < b 0 + n 0 + s 0 + 1
    rw [Function.update_apply, if_pos rfl]
    omega

theorem tupleUncoupled_rejects :
    ¬ tupleInterpretationStrictSAccepts
      { tupleInterpretationStrictSWitness with recur := tupleUncoupledRecur } := fun hA =>
  tupleInterpretationStrictS_mutation
    ⟨hA, tupleInterpretationStrictS_sound _ tupleUncoupled_laws hA⟩

noncomputable def tupleInterpretationStrictSRecurControl :
    FeatureChangeControl tupleInterpretationStrictSLaws tupleInterpretationStrictSAccepts
      tupleInterpretationStrictSRecurLens where
  base := tupleInterpretationStrictSWitness
  baseLaws := tupleInterpretationStrictSWitness_laws
  baseAccepts := tupW_root
  value := tupleRecurCode tupleInterpretationStrictSWitness.m tupleUncoupledRecur
  valueDiffers := fun h => tupleUncoupledRecur_ne ((tupleRecurCode _).injective h)
  changedLaws := by
    rw [tupleInterpretationStrictSRecurLens_set_code]
    exact tupleUncoupled_laws
  changedRejects := by
    rw [tupleInterpretationStrictSRecurLens_set_code]
    exact tupleUncoupled_rejects

def tupleInterpretationStrictSNecessityStatement : Prop :=
  EscapeFeatureNecessity tupleInterpretationStrictSLaws tupleInterpretationStrictSAccepts
    tupleInterpretationStrictSRecurLens

theorem tupleInterpretationStrictS_necessity : tupleInterpretationStrictSNecessityStatement :=
  ⟨tupleInterpretationStrictSRecurControl⟩

/-! ## strictMonotoneAlgebraArchimedean -/

def strictMonotoneAlgebraArchimedeanNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- The recursor operation of the algebra. -/
def strictMonotoneAlgebraArchimedeanRecurLens :
    FeatureLens strictMonotoneAlgebraArchimedeanData (ℕ → ℕ → ℕ → ℕ) where
  get M := M.recur
  set M v := { M with recur := v }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The coupled recursor replaced by the additive recursor `b + s + n + 1`. -/
def strictMonotoneAlgebraArchimedeanRecurControl :
    FeatureChangeControl strictMonotoneAlgebraArchimedeanLaws
      strictMonotoneAlgebraArchimedeanAccepts strictMonotoneAlgebraArchimedeanRecurLens where
  base := strictMonotoneAlgebraArchimedeanWitness
  baseLaws := strictMonotoneAlgebraArchimedeanWitness_laws
  baseAccepts := strictMonotoneAlgebraArchimedeanWitness_accepts
  value := fun b s n => b + s + n + 1
  valueDiffers := fun h => absurd (congrFun (congrFun (congrFun h 0) 0) 0) (by decide)
  changedLaws := strictMonotoneAlgebraArchimedean_mutation.1
  changedRejects := fun hA => strictMonotoneAlgebraArchimedean_mutation.2
    ⟨hA, strictMonotoneAlgebraArchimedean_sound _ strictMonotoneAlgebraArchimedean_mutation.1 hA⟩

def strictMonotoneAlgebraArchimedeanNecessityStatement : Prop :=
  EscapeFeatureNecessity strictMonotoneAlgebraArchimedeanLaws
    strictMonotoneAlgebraArchimedeanAccepts strictMonotoneAlgebraArchimedeanRecurLens

theorem strictMonotoneAlgebraArchimedean_necessity :
    strictMonotoneAlgebraArchimedeanNecessityStatement :=
  ⟨strictMonotoneAlgebraArchimedeanRecurControl⟩

/-! ## extendedMonotoneAlgebra -/

def extendedMonotoneAlgebraNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- A fixed bijection between the vectors of dimension `d + 1` and `ℕ`. -/
noncomputable def emaVecCode (d : ℕ) : NVec d ≃ ℕ :=
  Classical.choice nonempty_equiv_of_countable

/-- The strict relation of an extended monotone algebra, read through `emaVecCode`. -/
noncomputable def extendedMonotoneAlgebraStrictLens :
    FeatureLens extendedMonotoneAlgebraData (ℕ → ℕ → Prop) where
  get M a b := M.strict ((emaVecCode M.d).symm a) ((emaVecCode M.d).symm b)
  set M v := { M with strict := fun x y => v (emaVecCode M.d x) (emaVecCode M.d y) }
  get_set M v := by
    funext a b
    show v (emaVecCode M.d ((emaVecCode M.d).symm a)) (emaVecCode M.d ((emaVecCode M.d).symm b)) =
      v a b
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  set_get M := by
    show { M with strict := (fun x y => M.strict ((emaVecCode M.d).symm (emaVecCode M.d x))
      ((emaVecCode M.d).symm (emaVecCode M.d y))) } = M
    simp only [Equiv.symm_apply_apply]
  set_set _ _ _ := rfl

theorem extendedMonotoneAlgebraStrictLens_set_code (M : extendedMonotoneAlgebraData)
    (s : NVec M.d → NVec M.d → Prop) :
    extendedMonotoneAlgebraStrictLens.set M
        (fun a b => s ((emaVecCode M.d).symm a) ((emaVecCode M.d).symm b)) =
      { M with strict := s } := by
  show { M with strict := (fun x y => s ((emaVecCode M.d).symm (emaVecCode M.d x))
      ((emaVecCode M.d).symm (emaVecCode M.d y))) } = { M with strict := s }
  simp only [Equiv.symm_apply_apply]

/-- The operations of the witness are strictly monotone for the pointwise strict order. -/
theorem tupW_pointwise_strict :
    StrictContextLaws tupleInterpretationStrictSWitness.interp
      (fun x y : NVec 1 => ∀ i, x i < y i) where
  succ := by
    intro x y h
    show ∀ i : Fin 2, _
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show x 0 + 1 < y 0 + 1
      have := h 0
      omega
    · show x 1 + 1 < y 1 + 1
      have := h 1
      omega
  wrapLeft := by
    intro x y z h
    show ∀ i : Fin 2, _
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show x 0 + z 0 + 1 < y 0 + z 0 + 1
      have := h 0
      omega
    · show x 1 + z 1 + 1 < y 1 + z 1 + 1
      have := h 1
      omega
  wrapRight := by
    intro z x y h
    show ∀ i : Fin 2, _
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show z 0 + x 0 + 1 < z 0 + y 0 + 1
      have := h 0
      omega
    · show z 1 + x 1 + 1 < z 1 + y 1 + 1
      have := h 1
      omega
  recurBase := by
    intro x y s n h
    show ∀ i : Fin 2, _
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show x 0 + n 0 + (n 1 + 1) * (s 0 + 1) < y 0 + n 0 + (n 1 + 1) * (s 0 + 1)
      have := h 0
      omega
    · show x 1 + (n 1 + 1) * (s 1 + 1) < y 1 + (n 1 + 1) * (s 1 + 1)
      have := h 1
      omega
  recurStep := by
    intro b x y n h
    show ∀ i : Fin 2, _
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show b 0 + n 0 + (n 1 + 1) * (x 0 + 1) < b 0 + n 0 + (n 1 + 1) * (y 0 + 1)
      have := Nat.mul_lt_mul_of_pos_left (show x 0 + 1 < y 0 + 1 by have := h 0; omega)
        (show 0 < n 1 + 1 by omega)
      omega
    · show b 1 + (n 1 + 1) * (x 1 + 1) < b 1 + (n 1 + 1) * (y 1 + 1)
      have := Nat.mul_lt_mul_of_pos_left (show x 1 + 1 < y 1 + 1 by have := h 1; omega)
        (show 0 < n 1 + 1 by omega)
      omega
  recurCounter := by
    intro b s x y h
    show ∀ i : Fin 2, _
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show b 0 + x 0 + (x 1 + 1) * (s 0 + 1) < b 0 + y 0 + (y 1 + 1) * (s 0 + 1)
      have h0 := h 0
      have := Nat.mul_le_mul_right (s 0 + 1) (show x 1 + 1 ≤ y 1 + 1 by have := h 1; omega)
      omega
    · show b 1 + (x 1 + 1) * (s 1 + 1) < b 1 + (y 1 + 1) * (s 1 + 1)
      have := Nat.mul_lt_mul_of_pos_right (show x 1 + 1 < y 1 + 1 by have := h 1; omega)
        (show 0 < s 1 + 1 by omega)
      omega

/-- The witness with the pointwise strict order in place of `≫`. -/
theorem extendedMonotoneAlgebraPointwise_laws :
    extendedMonotoneAlgebraLaws
      { extendedMonotoneAlgebraWitness with strict := fun x y => ∀ i, x i < y i } := by
  refine ⟨?_, fun _ _ _ hyz hxy i => lt_of_le_of_lt (hxy i) (hyz i), tuple_weakContextLaws _,
    tupW_pointwise_strict⟩
  refine Subrelation.wf (r := InvImage (· < ·) (fun v : NVec 1 => v 0)) ?_
    (InvImage.wf _ Nat.lt_wfRel.wf)
  intro x y hxy
  exact hxy 0

noncomputable def extendedMonotoneAlgebraStrictControl :
    FeatureChangeControl extendedMonotoneAlgebraLaws extendedMonotoneAlgebraAccepts
      extendedMonotoneAlgebraStrictLens where
  base := extendedMonotoneAlgebraWitness
  baseLaws := extendedMonotoneAlgebraWitness_laws
  baseAccepts := tupW_root
  value := fun a b => ∀ i, ((emaVecCode 1).symm a) i < ((emaVecCode 1).symm b) i
  valueDiffers := by
    intro h
    have h2 : (∀ i, ((emaVecCode 1).symm (emaVecCode 1 ![0, 0])) i <
          ((emaVecCode 1).symm (emaVecCode 1 ![1, 0])) i) =
        vecLt ((emaVecCode 1).symm (emaVecCode 1 ![0, 0]))
          ((emaVecCode 1).symm (emaVecCode 1 ![1, 0])) :=
      congrFun (congrFun h (emaVecCode 1 ![0, 0])) (emaVecCode 1 ![1, 0])
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h2
    have hv : vecLt (![0, 0] : NVec 1) ![1, 0] := by
      unfold vecLt
      decide
    rw [← h2] at hv
    exact absurd (hv 1) (by decide)
  changedLaws := by
    rw [extendedMonotoneAlgebraStrictLens_set_code extendedMonotoneAlgebraWitness
      (fun x y => ∀ i, x i < y i)]
    exact extendedMonotoneAlgebraPointwise_laws
  changedRejects := by
    rw [extendedMonotoneAlgebraStrictLens_set_code extendedMonotoneAlgebraWitness
      (fun x y => ∀ i, x i < y i)]
    exact fun hA => extendedMonotoneAlgebra_mutation
      ⟨hA, extendedMonotoneAlgebra_sound _ extendedMonotoneAlgebraPointwise_laws hA⟩

def extendedMonotoneAlgebraNecessityStatement : Prop :=
  EscapeFeatureNecessity extendedMonotoneAlgebraLaws extendedMonotoneAlgebraAccepts
    extendedMonotoneAlgebraStrictLens

theorem extendedMonotoneAlgebra_necessity : extendedMonotoneAlgebraNecessityStatement :=
  ⟨extendedMonotoneAlgebraStrictControl⟩

/-! ## finiteModelTermination -/

def finiteModelTerminationNecessityKind : RowNecessityKind := .deletedBarrierPremise

/-- The seven clauses of `FiniteModelLaws`, with `strict_mono` unfolded, other than `irrefl`. -/
def finiteModelTerminationOtherLaws (M : finiteModelTerminationData) : Prop :=
  (∀ x y z, M.lt x y → M.lt y z → M.lt x z) ∧
    (∀ x y, M.lt x y → M.lt (M.interp.succ x) (M.interp.succ y)) ∧
    (∀ x y z, M.lt x y → M.lt (M.interp.wrap x z) (M.interp.wrap y z)) ∧
    (∀ z x y, M.lt x y → M.lt (M.interp.wrap z x) (M.interp.wrap z y)) ∧
    (∀ x y s n, M.lt x y → M.lt (M.interp.recur x s n) (M.interp.recur y s n)) ∧
    (∀ b x y n, M.lt x y → M.lt (M.interp.recur b x n) (M.interp.recur b y n)) ∧
    (∀ b s x y, M.lt x y → M.lt (M.interp.recur b s x) (M.interp.recur b s y))

/-- The deleted clause `irrefl`. -/
def finiteModelTerminationDeletedLaw (M : finiteModelTerminationData) : Prop :=
  ∀ x, ¬ M.lt x x

theorem finiteModelTerminationLaws_split (M : finiteModelTerminationData) :
    finiteModelTerminationLaws M ↔
      finiteModelTerminationOtherLaws M ∧ finiteModelTerminationDeletedLaw M := by
  unfold finiteModelTerminationLaws finiteModelTerminationOtherLaws finiteModelTerminationDeletedLaw
  constructor
  · intro h
    exact ⟨⟨h.trans, fun _ _ hxy => h.strict_mono.succ hxy,
      fun _ _ z hxy => h.strict_mono.wrapLeft z hxy, fun z _ _ hxy => h.strict_mono.wrapRight z hxy,
      fun _ _ s n hxy => h.strict_mono.recurBase s n hxy,
      fun b _ _ n hxy => h.strict_mono.recurStep b n hxy,
      fun b s _ _ hxy => h.strict_mono.recurCounter b s hxy⟩, h.irrefl⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩
    exact ⟨h8, h1, ⟨fun hxy => h2 _ _ hxy, fun z hxy => h3 _ _ z hxy,
      fun z {_ _} hxy => h4 z _ _ hxy,
      fun s n hxy => h5 _ _ s n hxy, fun b {_ _} n hxy => h6 b _ _ n hxy,
      fun b s {_ _} hxy => h7 b s _ _ hxy⟩⟩

/-- The one-point witness with the total relation. -/
def finiteModelTerminationCountermodel :
    DeletedPremiseCountermodel finiteModelTerminationOtherLaws finiteModelTerminationDeletedLaw
      finiteModelTerminationAccepts where
  datum := { finiteModelTerminationWitness with lt := fun _ _ => True }
  other := ⟨fun _ _ _ _ _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ => trivial,
    fun _ _ _ _ => trivial, fun _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial,
    fun _ _ _ _ _ => trivial⟩
  deletedFails := fun h => h 0 trivial
  accepts := finiteModelTermination_mutation.2

def finiteModelTerminationNecessityStatement : Prop :=
  BarrierPremiseNecessity finiteModelTerminationLaws finiteModelTerminationOtherLaws
    finiteModelTerminationDeletedLaw finiteModelTerminationAccepts

theorem finiteModelTermination_necessity : finiteModelTerminationNecessityStatement :=
  ⟨finiteModelTerminationLaws_split, fun M hM => finiteModelTermination_universal M hM,
    ⟨finiteModelTerminationCountermodel⟩⟩

end OperatorKO7.Methods.OrientationClosure.HypothesisNecessity
