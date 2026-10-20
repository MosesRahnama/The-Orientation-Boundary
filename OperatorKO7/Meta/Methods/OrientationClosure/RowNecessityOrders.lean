import OperatorKO7.Meta.Methods.OrientationClosure.HypothesisNecessityBase
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsKBO
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsPathOrders
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsOtherCalculi

/-!
# B7 necessity statements of the KBO, path-order and other-calculi method rows

Fifteen rows of `RDRSMethodFamily`. Each row states its necessity through one carrier of
`HypothesisNecessityBase`, applied to the row's own `Laws` and `Accepts`.

Relation: the row's own acceptance predicate for the free duplicating rule.
Property: necessity of one law clause (barrier) or one data field (escape), or a proof that the
laws fix the verdict.
External trust: none.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.HypothesisNecessity

open OperatorKO7.Meta.Rewriting (Term)

/-! ## Row `standardKBO` -/

def standardKBONecessityKind : RowNecessityKind := .lawFreeBarrierControl

/-- Nonduplicating control. `standardKBOAccepts` is hard-wired to the duplicating rule, so the
control is stated on the comparison it uses, `Gt (standardKBOCore M)`: every lawful standard KBO
orients every instance of the zero rule `recur b s zero → b`, which duplicates no variable. -/
def standardKBONonduplicatingControl : Prop :=
  ∀ M, MethodRowsKBO.standardKBOLaws M → ∀ b s : SchemaCore.FreeTerm ℕ,
    MethodRowsKBO.Gt (MethodRowsKBO.standardKBOCore M)
      (MethodRowsKBO.embed (.recur b s .zero)) (MethodRowsKBO.embed b)

theorem standardKBONonduplicatingControl_holds : standardKBONonduplicatingControl := by
  intro M hM b s
  exact MethodRowsKBO.gt_arg _ (MethodRowsKBO.standardKBOCore_laws hM)
    (fun a ha => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> exact MethodRowsKBO.wft_embed _ (fun _ => rfl) _)
    (by simp [MethodRowsKBO.KBOCore.Special]) (by simp)

/-- The standard KBO rejects the duplicating rule at every datum, lawful or not. -/
def standardKBONecessityStatement : Prop :=
  UniversalBarrierNecessity MethodRowsKBO.standardKBOLaws MethodRowsKBO.standardKBOAccepts
    standardKBONonduplicatingControl

theorem standardKBO_necessity : standardKBONecessityStatement :=
  ⟨⟨MethodRowsKBO.standardKBOWitness, MethodRowsKBO.standardKBOWitness_laws⟩,
    MethodRowsKBO.standardKBO_rejects, standardKBONonduplicatingControl_holds⟩

/-! ## Row `kboWithStatus` -/

def kboWithStatusNecessityKind : RowNecessityKind := .lawFreeBarrierControl

/-- Nonduplicating control. `kboWithStatusAccepts` is hard-wired to the duplicating rule, so the
control is stated on the comparison it uses, `Gt (kboWithStatusCore M)`: every lawful KBO with
status orients every instance of the zero rule `recur b s zero → b`. -/
def kboWithStatusNonduplicatingControl : Prop :=
  ∀ M, MethodRowsKBO.kboWithStatusLaws M → ∀ b s : SchemaCore.FreeTerm ℕ,
    MethodRowsKBO.Gt (MethodRowsKBO.kboWithStatusCore M)
      (MethodRowsKBO.embed (.recur b s .zero)) (MethodRowsKBO.embed b)

theorem kboWithStatusNonduplicatingControl_holds : kboWithStatusNonduplicatingControl := by
  intro M hM b s
  exact MethodRowsKBO.gt_arg _ (MethodRowsKBO.kboWithStatusCore_laws hM)
    (fun a ha => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> exact MethodRowsKBO.wft_embed _ (fun _ => rfl) _)
    (by simp [MethodRowsKBO.KBOCore.Special]) (by simp)

/-- The KBO with status rejects the duplicating rule at every datum, lawful or not. -/
def kboWithStatusNecessityStatement : Prop :=
  UniversalBarrierNecessity MethodRowsKBO.kboWithStatusLaws MethodRowsKBO.kboWithStatusAccepts
    kboWithStatusNonduplicatingControl

theorem kboWithStatus_necessity : kboWithStatusNecessityStatement :=
  ⟨⟨MethodRowsKBO.kboWithStatusWitness, MethodRowsKBO.kboWithStatusWitness_laws⟩,
    MethodRowsKBO.kboWithStatus_rejects, kboWithStatusNonduplicatingControl_holds⟩

/-! ## Row `generalizedKBO` -/

def generalizedKBONecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- The recursor interpretation of a generalized-KBO datum. -/
def generalizedKBOFeatureLens :
    FeatureLens MethodRowsKBO.generalizedKBOData (ℕ → ℕ → ℕ → ℕ) where
  get M := M.recurI
  set M v := { M with recurI := v }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Replacing the coupled recursor `(n + 1)(s + b + 2)` of the witness by the lawful uncoupled
`b + s + n + 2` loses acceptance. -/
def generalizedKBONecessityStatement : Prop :=
  EscapeFeatureNecessity MethodRowsKBO.generalizedKBOLaws MethodRowsKBO.generalizedKBOAccepts
    generalizedKBOFeatureLens

theorem generalizedKBO_necessity : generalizedKBONecessityStatement := by
  have hLaws : MethodRowsKBO.generalizedKBOLaws
      (generalizedKBOFeatureLens.set MethodRowsKBO.generalizedKBOWitness
        (fun b s n => b + s + n + 2)) :=
    { succ_mono := MethodRowsKBO.generalizedKBOWitness_laws.succ_mono
      wrap_mono_left := MethodRowsKBO.generalizedKBOWitness_laws.wrap_mono_left
      wrap_mono_right := MethodRowsKBO.generalizedKBOWitness_laws.wrap_mono_right
      recur_mono_1 := fun {a b} c d hab => show a + c + d + 2 ≤ b + c + d + 2 by omega
      recur_mono_2 := fun c {a b} d hab => show c + a + d + 2 ≤ c + b + d + 2 by omega
      recur_mono_3 := fun c d {a b} hab => show c + d + a + 2 ≤ c + d + b + 2 by omega
      succ_simple := MethodRowsKBO.generalizedKBOWitness_laws.succ_simple
      wrap_simple := MethodRowsKBO.generalizedKBOWitness_laws.wrap_simple
      recur_simple := fun a b c =>
        ⟨show a < a + b + c + 2 by omega, show b < a + b + c + 2 by omega,
          show c < a + b + c + 2 by omega⟩
      prec_irrefl := MethodRowsKBO.generalizedKBOWitness_laws.prec_irrefl
      prec_trans := MethodRowsKBO.generalizedKBOWitness_laws.prec_trans }
  have hRej : ¬ MethodRowsKBO.generalizedKBOAccepts
      (generalizedKBOFeatureLens.set MethodRowsKBO.generalizedKBOWitness
        (fun b s n => b + s + n + 2)) :=
    fun hA => MethodRowsKBO.generalizedKBO_mutation
      ⟨hA, MethodRowsKBO.generalizedKBO_sound _ hLaws hA⟩
  exact ⟨{ base := MethodRowsKBO.generalizedKBOWitness
           baseLaws := MethodRowsKBO.generalizedKBOWitness_laws
           baseAccepts := MethodRowsKBO.generalizedKBOWitness_accepts
           value := fun b s n => b + s + n + 2
           valueDiffers := fun h => hRej ((congrArg (fun v : ℕ → ℕ → ℕ → ℕ =>
             MethodRowsKBO.generalizedKBOAccepts
               (generalizedKBOFeatureLens.set MethodRowsKBO.generalizedKBOWitness v)) h).mpr
             MethodRowsKBO.generalizedKBOWitness_accepts)
           changedLaws := hLaws
           changedRejects := hRej }⟩

/-! ## Row `subtermCoefficientKBO` -/

def subtermCoefficientKBONecessityKind : RowNecessityKind := .deletedBarrierPremise

/-- The clauses of `subtermCoefficientKBOLaws` other than coefficient positivity. -/
def subtermCoefficientKBOOtherLaws (M : MethodRowsKBO.subtermCoefficientKBOData) : Prop :=
  0 < M.w0 ∧ M.w0 ≤ M.weight .zero ∧
    (M.weight .succ = 0 → ∀ g : MethodRowsKBO.SchemaSym, g ≠ .succ → M.prec .succ g) ∧
    (∀ f, ¬ M.prec f f) ∧ (∀ f g h, M.prec f g → M.prec g h → M.prec f h)

/-- Coefficient positivity, the clause consumed by `subtermCoefficientKBO_universal`. -/
def subtermCoefficientKBODeletedLaw (M : MethodRowsKBO.subtermCoefficientKBOData) : Prop :=
  ∀ f i, 1 ≤ M.coeff f i

/-- The witness with the coefficient of the first `wrap` position set to `0`. -/
def subtermCoefficientKBOCountermodel : MethodRowsKBO.subtermCoefficientKBOData :=
  { MethodRowsKBO.subtermCoefficientKBOWitness with coeff := MethodRowsKBO.scCoeffMutant }

def subtermCoefficientKBONecessityStatement : Prop :=
  BarrierPremiseNecessity MethodRowsKBO.subtermCoefficientKBOLaws subtermCoefficientKBOOtherLaws
    subtermCoefficientKBODeletedLaw MethodRowsKBO.subtermCoefficientKBOAccepts

theorem subtermCoefficientKBO_necessity : subtermCoefficientKBONecessityStatement :=
  ⟨fun _ => ⟨fun h => ⟨⟨h.w0_pos, h.zero_ge, h.succ_max, h.prec_irrefl, h.prec_trans⟩, h.coeff_pos⟩,
      fun ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩ => ⟨h1, h2, h6, h3, h4, h5⟩⟩,
    MethodRowsKBO.subtermCoefficientKBO_universal,
    ⟨{ datum := subtermCoefficientKBOCountermodel
       other := ⟨by decide, le_rfl, fun h => absurd h (by decide),
         MethodRowsKBO.rankPrec_irrefl _, MethodRowsKBO.rankPrec_trans _⟩
       deletedFails := fun h => absurd (h .wrap 0) (by decide)
       accepts := MethodRowsKBO.subtermCoefficientKBO_mutation.2 }⟩⟩

/-! ## Row `acKBO` -/

def acKBONecessityKind : RowNecessityKind := .lawFreeBarrierControl

/-- Nonduplicating control. `acKBOAccepts` is hard-wired to the duplicating rule, so the control
is stated on the comparison it uses, `acKBOGt M`: every lawful AC-invariant comparison orients
every instance of the zero rule `recur b s zero → b`. -/
def acKBONonduplicatingControl : Prop :=
  ∀ M, MethodRowsKBO.acKBOLaws M → ∀ b s : SchemaCore.FreeTerm ℕ,
    MethodRowsKBO.acKBOGt M (MethodRowsKBO.embed (.recur b s .zero)) (MethodRowsKBO.embed b)

theorem acKBONonduplicatingControl_holds : acKBONonduplicatingControl := by
  intro M hM b s
  refine ⟨fun x => ?_, ?_⟩
  · rw [MethodRowsKBO.cnt_embed_recur, MethodRowsKBO.cnt_embed_zero]
    omega
  · unfold MethodRowsKBO.acKeyLT MethodRowsKBO.acKey
    refine Prod.lex_def.2 (Or.inl (Prod.lex_def.2 (Or.inl ?_)))
    show MethodRowsKBO.acWt M (MethodRowsKBO.embed b) <
      MethodRowsKBO.acWt M (MethodRowsKBO.embed (.recur b s .zero))
    simp only [MethodRowsKBO.acWt, MethodRowsKBO.embed, MethodRowsKBO.ev_app,
      MethodRowsKBO.evL_cons, MethodRowsKBO.evL_nil, smul_eq_mul, one_mul, add_zero]
    have h0 := hM.w0_pos
    have h1 := hM.zero_ge
    omega

/-- The AC-invariant comparison rejects the duplicating rule at every datum, lawful or not. -/
def acKBONecessityStatement : Prop :=
  UniversalBarrierNecessity MethodRowsKBO.acKBOLaws MethodRowsKBO.acKBOAccepts
    acKBONonduplicatingControl

theorem acKBO_necessity : acKBONecessityStatement :=
  ⟨⟨MethodRowsKBO.acKBOWitness, MethodRowsKBO.acKBOWitness_laws⟩,
    MethodRowsKBO.acKBO_rejects, acKBONonduplicatingControl_holds⟩

/-! ## Row `transfiniteKBO` -/

def transfiniteKBONecessityKind : RowNecessityKind := .deletedBarrierPremise

/-- The clauses of `transfiniteKBOLaws` other than coefficient positivity. -/
def transfiniteKBOOtherLaws (M : MethodRowsKBO.transfiniteKBOData) : Prop :=
  0 < M.w0 ∧ (M.w0 : Ordinal) ≤ ONote.repr (M.weight .zero) ∧
    (ONote.repr (M.weight .succ) = 0 →
      ∀ g : MethodRowsKBO.SchemaSym, g ≠ .succ → M.prec .succ g) ∧
    (∀ f, ¬ M.prec f f) ∧ (∀ f g h, M.prec f g → M.prec g h → M.prec f h)

/-- Coefficient positivity, the clause consumed by `transfiniteKBO_universal`. -/
def transfiniteKBODeletedLaw (M : MethodRowsKBO.transfiniteKBOData) : Prop :=
  ∀ f i, 1 ≤ M.coeff f i

/-- Ordinal weights of the countermodel: `wrap` weighs `0`, every other symbol `1`. -/
def transfiniteKBOCountermodelWeight : MethodRowsKBO.SchemaSym → ONote
  | .zero => 1
  | .succ => 1
  | .wrap => 0
  | .recur => 1

/-- A transfinite KBO datum whose first `wrap` coefficient is `0`. -/
def transfiniteKBOCountermodel : MethodRowsKBO.transfiniteKBOData where
  w0 := 1
  weight := transfiniteKBOCountermodelWeight
  coeff := MethodRowsKBO.scCoeffMutant
  prec := MethodRowsKBO.rankPrec MethodRowsKBO.schemaRank

/-- Weight clause at every instance of the duplicating rule, in `NatOrdinal`: the two sides differ
by the weight of `wrap` against the weight of `succ`. -/
theorem transfiniteKBOCountermodel_weight_lt (b s n : SchemaCore.FreeTerm ℕ) :
    (MethodRowsKBO.transfiniteKBOCore transfiniteKBOCountermodel).wt
        (MethodRowsKBO.embed (.wrap s (.recur b s n))) <
      (MethodRowsKBO.transfiniteKBOCore transfiniteKBOCountermodel).wt
        (MethodRowsKBO.embed (.recur b s (.succ n))) := by
  have hw0 : (MethodRowsKBO.transfiniteKBOCore transfiniteKBOCountermodel).coeff .wrap 0 = 0 :=
    rfl
  have hw1 : (MethodRowsKBO.transfiniteKBOCore transfiniteKBOCountermodel).coeff .wrap 1 = 1 :=
    rfl
  have hr2 : (MethodRowsKBO.transfiniteKBOCore transfiniteKBOCountermodel).coeff .recur 2 = 1 :=
    rfl
  have hs0 : (MethodRowsKBO.transfiniteKBOCore transfiniteKBOCountermodel).coeff .succ 0 = 1 :=
    rfl
  have hlt : (MethodRowsKBO.transfiniteKBOCore transfiniteKBOCountermodel).weight .wrap <
      (MethodRowsKBO.transfiniteKBOCore transfiniteKBOCountermodel).weight .succ := by
    show Ordinal.toNatOrdinal (ONote.repr 0) < Ordinal.toNatOrdinal (ONote.repr 1)
    exact Ordinal.toNatOrdinal.lt_iff_lt.2 (by simp)
  have key : ∀ (A B C D E F : NatOrdinal) (c d : ℕ), A < B →
      A + (C + (c • D + (d • E + F))) < C + (c • D + (d • E + (B + F))) := by
    intro A B C D E F c d h
    rw [add_left_comm _ B, add_left_comm _ B, add_left_comm _ B]
    exact add_lt_add_right h _
  change (MethodRowsKBO.transfiniteKBOCore transfiniteKBOCountermodel).wt
      (Term.app .wrap [MethodRowsKBO.embed s, Term.app .recur
        [MethodRowsKBO.embed b, MethodRowsKBO.embed s, MethodRowsKBO.embed n]]) <
    (MethodRowsKBO.transfiniteKBOCore transfiniteKBOCountermodel).wt
      (Term.app .recur [MethodRowsKBO.embed b, MethodRowsKBO.embed s,
        Term.app .succ [MethodRowsKBO.embed n]])
  simp only [MethodRowsKBO.wt_app, MethodRowsKBO.ev_app, MethodRowsKBO.evL_cons,
    MethodRowsKBO.evL_nil, zero_add, add_zero, hw0, hw1, hr2, hs0, zero_smul, one_smul]
  exact key _ _ _ _ _ _ _ _ hlt

/-- The countermodel orients every instance of the duplicating rule by the weight clause. -/
theorem transfiniteKBOCountermodel_accepts :
    MethodRowsKBO.transfiniteKBOAccepts transfiniteKBOCountermodel := by
  intro b s n
  refine MethodRowsKBO.Gt.weight (fun x => ?_) (transfiniteKBOCountermodel_weight_lt b s n)
  simp only [MethodRowsKBO.embed, MethodRowsKBO.cnt_app, MethodRowsKBO.ev_app, zero_add,
    MethodRowsKBO.evL_cons, MethodRowsKBO.evL_nil, smul_eq_mul, MethodRowsKBO.transfiniteKBOCore,
    transfiniteKBOCountermodel, MethodRowsKBO.scCoeffMutant]
  omega

def transfiniteKBONecessityStatement : Prop :=
  BarrierPremiseNecessity MethodRowsKBO.transfiniteKBOLaws transfiniteKBOOtherLaws
    transfiniteKBODeletedLaw MethodRowsKBO.transfiniteKBOAccepts

theorem transfiniteKBO_necessity : transfiniteKBONecessityStatement :=
  ⟨fun _ => ⟨fun h => ⟨⟨h.w0_pos, h.zero_ge, h.succ_max, h.prec_irrefl, h.prec_trans⟩, h.coeff_pos⟩,
      fun ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩ => ⟨h1, h2, h6, h3, h4, h5⟩⟩,
    MethodRowsKBO.transfiniteKBO_universal,
    ⟨{ datum := transfiniteKBOCountermodel
       other := ⟨by decide,
         by simp [transfiniteKBOCountermodel, transfiniteKBOCountermodelWeight],
         fun h => absurd h (by simp [transfiniteKBOCountermodel, transfiniteKBOCountermodelWeight]),
         MethodRowsKBO.rankPrec_irrefl _, MethodRowsKBO.rankPrec_trans _⟩
       deletedFails := fun h => absurd (h .wrap 0) (by decide)
       accepts := transfiniteKBOCountermodel_accepts }⟩⟩

/-! ## Row `lambdaFreeKBO` -/

def lambdaFreeKBONecessityKind : RowNecessityKind := .lawFreeBarrierControl

/-- Nonduplicating control. `lambdaFreeKBOAccepts` is hard-wired to the curried duplicating rule,
so the control is stated on the comparison it uses, `lambdaFreeKBOGt M` through `lfCurry`: every
lawful lambda-free KBO orients every curried instance of the zero rule `recur b s zero → b`. -/
def lambdaFreeKBONonduplicatingControl : Prop :=
  ∀ M, MethodRowsKBO.lambdaFreeKBOLaws M → ∀ b s : SchemaCore.FreeTerm ℕ,
    MethodRowsKBO.lambdaFreeKBOGt M
      (MethodRowsKBO.lfCurry (MethodRowsKBO.embed (.recur b s .zero)))
      (MethodRowsKBO.lfCurry (MethodRowsKBO.embed b))

theorem lambdaFreeKBONonduplicatingControl_holds : lambdaFreeKBONonduplicatingControl := by
  intro M hM b s
  refine ⟨fun x => ?_, Prod.lex_def.2 (Or.inl ?_)⟩
  · rw [MethodRowsKBO.lfCount_curry, MethodRowsKBO.lfCount_curry, MethodRowsKBO.cnt_embed_recur,
      MethodRowsKBO.cnt_embed_zero]
    omega
  · show MethodRowsKBO.lfWeight M (MethodRowsKBO.lfCurry (MethodRowsKBO.embed b)) <
      MethodRowsKBO.lfWeight M (MethodRowsKBO.lfCurry (MethodRowsKBO.embed (.recur b s .zero)))
    rw [MethodRowsKBO.lfWeight_curry_embed_recur]
    have h0 := hM.appWeight_pos
    omega

/-- The lambda-free KBO rejects the curried duplicating rule at every datum, lawful or not. -/
def lambdaFreeKBONecessityStatement : Prop :=
  UniversalBarrierNecessity MethodRowsKBO.lambdaFreeKBOLaws MethodRowsKBO.lambdaFreeKBOAccepts
    lambdaFreeKBONonduplicatingControl

theorem lambdaFreeKBO_necessity : lambdaFreeKBONecessityStatement :=
  ⟨⟨MethodRowsKBO.lambdaFreeKBOWitness, MethodRowsKBO.lambdaFreeKBOWitness_laws⟩,
    MethodRowsKBO.lambdaFreeKBO_rejects, lambdaFreeKBONonduplicatingControl_holds⟩

/-! ## Row `polynomialKBO` -/

def polynomialKBONecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- The recursor monomial table of a polynomial-KBO datum. -/
def polynomialKBOFeatureLens :
    FeatureLens MethodRowsKBO.polynomialKBOData (List PolynomialOrientationDecision.RMono) where
  get P := P.R
  set P v := { P with R := v }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Replacing the coupled recursor table of the witness by the lawful linear table
`b + s + n + 2` loses acceptance. -/
def polynomialKBONecessityStatement : Prop :=
  EscapeFeatureNecessity MethodRowsKBO.polynomialKBOLaws MethodRowsKBO.polynomialKBOAccepts
    polynomialKBOFeatureLens

theorem polynomialKBO_necessity : polynomialKBONecessityStatement := by
  have hLaws : MethodRowsKBO.polynomialKBOLaws
      (polynomialKBOFeatureLens.set MethodRowsKBO.polynomialKBOWitness
        MethodRowsKBO.polynomialKBOLinearR) :=
    { slope_pos := MethodRowsKBO.polynomialKBOWitness_laws.slope_pos
      a_pos := MethodRowsKBO.polynomialKBOWitness_laws.a_pos
      wrap_simple := MethodRowsKBO.polynomialKBOWitness_laws.wrap_simple
      recur_simple := fun b s n => by
        show b < PolynomialOrientationDecision.rEval MethodRowsKBO.polynomialKBOLinearR b s n ∧
          s < PolynomialOrientationDecision.rEval MethodRowsKBO.polynomialKBOLinearR b s n ∧
          n < PolynomialOrientationDecision.rEval MethodRowsKBO.polynomialKBOLinearR b s n
        simp only [MethodRowsKBO.polynomialKBOLinearR, PolynomialOrientationDecision.rEval,
          pow_zero, pow_one, mul_one, one_mul, add_zero]
        exact ⟨by omega, by omega, by omega⟩
      prec_irrefl := MethodRowsKBO.polynomialKBOWitness_laws.prec_irrefl
      prec_trans := MethodRowsKBO.polynomialKBOWitness_laws.prec_trans }
  have hRej : ¬ MethodRowsKBO.polynomialKBOAccepts
      (polynomialKBOFeatureLens.set MethodRowsKBO.polynomialKBOWitness
        MethodRowsKBO.polynomialKBOLinearR) :=
    MethodRowsKBO.polynomialKBOWitness_feature.2.2
  exact ⟨{ base := MethodRowsKBO.polynomialKBOWitness
           baseLaws := MethodRowsKBO.polynomialKBOWitness_laws
           baseAccepts := MethodRowsKBO.polynomialKBOWitness_accepts
           value := MethodRowsKBO.polynomialKBOLinearR
           valueDiffers := fun h => hRej ((congrArg
             (fun v : List PolynomialOrientationDecision.RMono =>
               MethodRowsKBO.polynomialKBOAccepts
                 (polynomialKBOFeatureLens.set MethodRowsKBO.polynomialKBOWitness v)) h).mpr
             MethodRowsKBO.polynomialKBOWitness_accepts)
           changedLaws := hLaws
           changedRejects := hRej }⟩

/-! ## Rows with a precedence feature: `acRPO`, `rpoModuloPermutation`,
`simpleTerminationOrderType` -/

/-- The reversed rank precedence `recur < wrap < succ < zero` on the free signature. -/
def reversedSymPrec (a b : MethodRowsPathOrders.Sym) : Prop :=
  MethodRowsPathOrders.symRank b < MethodRowsPathOrders.symRank a

theorem reversedSymPrec_trans (a b c : MethodRowsPathOrders.Sym) (h₁ : reversedSymPrec a b)
    (h₂ : reversedSymPrec b c) : reversedSymPrec a c :=
  lt_trans h₂ h₁

theorem reversedSymPrec_wf : WellFounded reversedSymPrec :=
  @Finite.wellFounded_of_trans_of_irrefl MethodRowsPathOrders.Sym _ reversedSymPrec
    ⟨reversedSymPrec_trans⟩ ⟨fun a h => lt_irrefl (MethodRowsPathOrders.symRank a) h⟩

/-! ### Row `acRPO` -/

def acRPONecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- The precedence of an AC-RPO datum. -/
def acRPOFeatureLens :
    FeatureLens MethodRowsPathOrders.acRPOData
      (MethodRowsPathOrders.Sym → MethodRowsPathOrders.Sym → Prop) where
  get M := M.prec
  set M v := { M with prec := v }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Reversing the precedence of the witness keeps the laws and loses acceptance. -/
def acRPONecessityStatement : Prop :=
  EscapeFeatureNecessity MethodRowsPathOrders.acRPOLaws MethodRowsPathOrders.acRPOAccepts
    acRPOFeatureLens

theorem acRPO_necessity : acRPONecessityStatement := by
  have hLaws : MethodRowsPathOrders.acRPOLaws
      (acRPOFeatureLens.set MethodRowsPathOrders.acRPOWitness reversedSymPrec) :=
    ⟨reversedSymPrec_trans, reversedSymPrec_wf, MethodRowsPathOrders.acRPOWitness_laws.2.2⟩
  have hRej : ¬ MethodRowsPathOrders.acRPOAccepts
      (acRPOFeatureLens.set MethodRowsPathOrders.acRPOWitness reversedSymPrec) :=
    MethodRowsPathOrders.acRPO_mutation
  exact ⟨{ base := MethodRowsPathOrders.acRPOWitness
           baseLaws := MethodRowsPathOrders.acRPOWitness_laws
           baseAccepts := MethodRowsPathOrders.acRPOWitness_accepts
           value := reversedSymPrec
           valueDiffers := fun h => hRej ((congrArg
             (fun v : MethodRowsPathOrders.Sym → MethodRowsPathOrders.Sym → Prop =>
               MethodRowsPathOrders.acRPOAccepts
                 (acRPOFeatureLens.set MethodRowsPathOrders.acRPOWitness v)) h).mpr
             MethodRowsPathOrders.acRPOWitness_accepts)
           changedLaws := hLaws
           changedRejects := hRej }⟩

/-! ### Row `rpoModuloPermutation` -/

def rpoModuloPermutationNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- The precedence of an RPO-modulo-permutation datum. -/
def rpoModuloPermutationFeatureLens :
    FeatureLens MethodRowsPathOrders.rpoModuloPermutationData
      (MethodRowsPathOrders.Sym → MethodRowsPathOrders.Sym → Prop) where
  get M := M.prec
  set M v := { M with prec := v }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Reversing the precedence of the witness keeps the laws and loses acceptance. -/
def rpoModuloPermutationNecessityStatement : Prop :=
  EscapeFeatureNecessity MethodRowsPathOrders.rpoModuloPermutationLaws
    MethodRowsPathOrders.rpoModuloPermutationAccepts rpoModuloPermutationFeatureLens

theorem rpoModuloPermutation_necessity : rpoModuloPermutationNecessityStatement := by
  have hLaws : MethodRowsPathOrders.rpoModuloPermutationLaws
      (rpoModuloPermutationFeatureLens.set MethodRowsPathOrders.rpoModuloPermutationWitness
        reversedSymPrec) :=
    ⟨reversedSymPrec_trans, reversedSymPrec_wf⟩
  have hRej : ¬ MethodRowsPathOrders.rpoModuloPermutationAccepts
      (rpoModuloPermutationFeatureLens.set MethodRowsPathOrders.rpoModuloPermutationWitness
        reversedSymPrec) :=
    MethodRowsPathOrders.rpoModuloPermutation_mutation
  exact ⟨{ base := MethodRowsPathOrders.rpoModuloPermutationWitness
           baseLaws := MethodRowsPathOrders.rpoModuloPermutationWitness_laws
           baseAccepts := MethodRowsPathOrders.rpoModuloPermutationWitness_accepts
           value := reversedSymPrec
           valueDiffers := fun h => hRej ((congrArg
             (fun v : MethodRowsPathOrders.Sym → MethodRowsPathOrders.Sym → Prop =>
               MethodRowsPathOrders.rpoModuloPermutationAccepts
                 (rpoModuloPermutationFeatureLens.set
                   MethodRowsPathOrders.rpoModuloPermutationWitness v)) h).mpr
             MethodRowsPathOrders.rpoModuloPermutationWitness_accepts)
           changedLaws := hLaws
           changedRejects := hRej }⟩

/-! ### Row `simpleTerminationOrderType` -/

def simpleTerminationOrderTypeNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- The precedence of a simple-termination datum. -/
def simpleTerminationOrderTypeFeatureLens :
    FeatureLens MethodRowsPathOrders.simpleTerminationOrderTypeData
      (MethodRowsPathOrders.Sym → MethodRowsPathOrders.Sym → Prop) where
  get M := M.prec
  set M v := { M with prec := v }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Reversing the precedence of the witness keeps the laws and loses acceptance. -/
def simpleTerminationOrderTypeNecessityStatement : Prop :=
  EscapeFeatureNecessity MethodRowsPathOrders.simpleTerminationOrderTypeLaws
    MethodRowsPathOrders.simpleTerminationOrderTypeAccepts simpleTerminationOrderTypeFeatureLens

theorem simpleTerminationOrderType_necessity : simpleTerminationOrderTypeNecessityStatement := by
  have hLaws : MethodRowsPathOrders.simpleTerminationOrderTypeLaws
      (simpleTerminationOrderTypeFeatureLens.set
        MethodRowsPathOrders.simpleTerminationOrderTypeWitness reversedSymPrec) :=
    ⟨reversedSymPrec_trans, reversedSymPrec_wf⟩
  have hRej : ¬ MethodRowsPathOrders.simpleTerminationOrderTypeAccepts
      (simpleTerminationOrderTypeFeatureLens.set
        MethodRowsPathOrders.simpleTerminationOrderTypeWitness reversedSymPrec) :=
    MethodRowsPathOrders.simpleTerminationOrderType_mutation
  exact ⟨{ base := MethodRowsPathOrders.simpleTerminationOrderTypeWitness
           baseLaws := MethodRowsPathOrders.simpleTerminationOrderTypeWitness_laws
           baseAccepts := MethodRowsPathOrders.simpleTerminationOrderTypeWitness_accepts
           value := reversedSymPrec
           valueDiffers := fun h => hRej ((congrArg
             (fun v : MethodRowsPathOrders.Sym → MethodRowsPathOrders.Sym → Prop =>
               MethodRowsPathOrders.simpleTerminationOrderTypeAccepts
                 (simpleTerminationOrderTypeFeatureLens.set
                   MethodRowsPathOrders.simpleTerminationOrderTypeWitness v)) h).mpr
             MethodRowsPathOrders.simpleTerminationOrderTypeWitness_accepts)
           changedLaws := hLaws
           changedRejects := hRej }⟩

/-! ## Row `popStarFamily` -/

def popStarFamilyNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Whether the counter position of `recur` is safe in a POP* datum. -/
def popStarFamilyFeatureLens : FeatureLens MethodRowsPathOrders.popStarFamilyData Bool where
  get M := M.safeN
  set M v := { M with safeN := v }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Making the counter of the witness a safe position keeps the laws and loses acceptance. -/
def popStarFamilyNecessityStatement : Prop :=
  EscapeFeatureNecessity MethodRowsPathOrders.popStarFamilyLaws
    MethodRowsPathOrders.popStarFamilyAccepts popStarFamilyFeatureLens

theorem popStarFamily_necessity : popStarFamilyNecessityStatement := by
  have hLaws : MethodRowsPathOrders.popStarFamilyLaws
      (popStarFamilyFeatureLens.set MethodRowsPathOrders.popStarFamilyWitness true) :=
    MethodRowsPathOrders.popStarFamilyWitness_laws
  have hRej : ¬ MethodRowsPathOrders.popStarFamilyAccepts
      (popStarFamilyFeatureLens.set MethodRowsPathOrders.popStarFamilyWitness true) :=
    MethodRowsPathOrders.popStarFamily_mutation
  exact ⟨{ base := MethodRowsPathOrders.popStarFamilyWitness
           baseLaws := MethodRowsPathOrders.popStarFamilyWitness_laws
           baseAccepts := MethodRowsPathOrders.popStarFamilyWitness_accepts
           value := true
           valueDiffers := fun h => hRej ((congrArg (fun v : Bool =>
             MethodRowsPathOrders.popStarFamilyAccepts
               (popStarFamilyFeatureLens.set MethodRowsPathOrders.popStarFamilyWitness v)) h).mpr
             MethodRowsPathOrders.popStarFamilyWitness_accepts)
           changedLaws := hLaws
           changedRejects := hRej }⟩

/-! ## Row `cichonSlowGrowing` -/

def cichonSlowGrowingNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- The ordinal notation of a Cichon slow-growing datum. -/
def cichonSlowGrowingFeatureLens :
    FeatureLens MethodRowsPathOrders.cichonSlowGrowingData
      (∀ {ν : Type}, SchemaCore.FreeTerm ν → ONote) where
  get M := M.note
  set M v := { M with note := v }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Replacing the calibrated notation of the witness by `ofNat (1000 + size)` keeps the laws,
which constrain only the bound, and loses acceptance. -/
def cichonSlowGrowingNecessityStatement : Prop :=
  EscapeFeatureNecessity MethodRowsPathOrders.cichonSlowGrowingLaws
    MethodRowsPathOrders.cichonSlowGrowingAccepts cichonSlowGrowingFeatureLens

theorem cichonSlowGrowing_necessity : cichonSlowGrowingNecessityStatement := by
  have hLaws : MethodRowsPathOrders.cichonSlowGrowingLaws
      (cichonSlowGrowingFeatureLens.set MethodRowsPathOrders.cichonSlowGrowingWitness
        (fun {ν : Type} (t : SchemaCore.FreeTerm ν) =>
          ONote.ofNat (1000 + MethodRowsPathOrders.freeSize t))) :=
    MethodRowsPathOrders.cichonSlowGrowingWitness_laws
  have hRej : ¬ MethodRowsPathOrders.cichonSlowGrowingAccepts
      (cichonSlowGrowingFeatureLens.set MethodRowsPathOrders.cichonSlowGrowingWitness
        (fun {ν : Type} (t : SchemaCore.FreeTerm ν) =>
          ONote.ofNat (1000 + MethodRowsPathOrders.freeSize t))) :=
    MethodRowsPathOrders.cichonSlowGrowing_mutation
  exact ⟨{ base := MethodRowsPathOrders.cichonSlowGrowingWitness
           baseLaws := MethodRowsPathOrders.cichonSlowGrowingWitness_laws
           baseAccepts := MethodRowsPathOrders.cichonSlowGrowingWitness_accepts
           value := fun {ν : Type} (t : SchemaCore.FreeTerm ν) =>
             ONote.ofNat (1000 + MethodRowsPathOrders.freeSize t)
           valueDiffers := fun h => hRej ((congrArg
             (fun v : (∀ {ν : Type}, SchemaCore.FreeTerm ν → ONote) =>
               MethodRowsPathOrders.cichonSlowGrowingAccepts
                 (cichonSlowGrowingFeatureLens.set
                   MethodRowsPathOrders.cichonSlowGrowingWitness v)) h).mpr
             MethodRowsPathOrders.cichonSlowGrowingWitness_accepts)
           changedLaws := hLaws
           changedRejects := hRej }⟩

/-! ## Row `higherOrderTupleInterpretation` -/

def higherOrderTupleInterpretationNecessityKind : RowNecessityKind := .noApplicableHypothesis

/-- Every lawful cost-size tuple interpretation orients both free rules, so the laws fix the
verdict and no lawful single-feature change loses acceptance. -/
def higherOrderTupleInterpretationNecessityStatement : Prop :=
  NoApplicableHypothesis MethodRowsOtherCalculi.higherOrderTupleInterpretationLaws
    MethodRowsOtherCalculi.higherOrderTupleInterpretationAccepts .lawsDetermineVerdict

theorem higherOrderTupleInterpretation_necessity :
    higherOrderTupleInterpretationNecessityStatement := by
  have hacc : ∀ M, MethodRowsOtherCalculi.higherOrderTupleInterpretationLaws M →
      MethodRowsOtherCalculi.higherOrderTupleInterpretationAccepts M := fun M hL =>
    ⟨fun A μ b s => by
        rw [MethodRowsOtherCalculi.hotiCost_toA, MethodRowsOtherCalculi.hotiCost_toA]
        exact MethodRowsOtherCalculi.hotiFreeCost_zero M hL b s,
      fun A μ b s n => by
        rw [MethodRowsOtherCalculi.hotiCost_toA, MethodRowsOtherCalculi.hotiCost_toA]
        exact MethodRowsOtherCalculi.hotiFreeCost_dup M hL b s n⟩
  exact ⟨⟨MethodRowsOtherCalculi.higherOrderTupleInterpretationWitness,
      MethodRowsOtherCalculi.higherOrderTupleInterpretationWitness_laws⟩,
    fun M M' hM hM' => iff_of_true (hacc M hM) (hacc M' hM')⟩

/-! ## Row `infinitaryRewritingTermination` -/

def infinitaryRewritingTerminationNecessityKind : RowNecessityKind := .noApplicableHypothesis

/-- The laws contain the acceptance condition, so every lawful datum accepts and the laws fix
the verdict. -/
def infinitaryRewritingTerminationNecessityStatement : Prop :=
  NoApplicableHypothesis MethodRowsOtherCalculi.infinitaryRewritingTerminationLaws
    MethodRowsOtherCalculi.infinitaryRewritingTerminationAccepts .lawsDetermineVerdict

theorem infinitaryRewritingTermination_necessity :
    infinitaryRewritingTerminationNecessityStatement :=
  ⟨⟨MethodRowsOtherCalculi.infinitaryRewritingTerminationWitness,
      MethodRowsOtherCalculi.infinitaryRewritingTerminationWitness_laws⟩,
    fun _ _ hM hM' => iff_of_true hM.2.1 hM'.2.1⟩

end OperatorKO7.Methods.OrientationClosure.HypothesisNecessity
