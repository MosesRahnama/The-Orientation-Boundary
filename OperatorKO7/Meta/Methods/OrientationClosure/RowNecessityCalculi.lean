import OperatorKO7.Meta.Methods.OrientationClosure.HypothesisNecessityBase
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsConditionalConstrained
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsTypedCalculi
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsTypingDisciplines
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsGraphCalculi
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsProcessCalculi
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsSemanticFrameworks

/-!
# Hypothesis necessity of the conditional, typed, typing, graph, process and semantic rows

Twenty rows of the method universe, each with its necessity kind, its necessity statement on the
row's own laws and acceptance predicate, and the proof of that statement.

Relation: the row's own acceptance predicate for the free duplicating rule.
Property: necessity of one law clause or one data feature, stated by a concrete datum, or a proof
that the laws fix the verdict.
External trust: none.

The row `generalizedWeightedTypeGraphs` stores its type graph and its graph weight in fields whose
types depend on the weight algebra, so no lens on the full data reads one of them. Its statement
reads the laws and acceptance on the datum built from a two-node edge-weight table over the
arithmetic semiring, with every other field fixed to the witness and the graph weight the
arithmetic minimum that the laws require; the lens replaces the weights of `wrap` in that table.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.HypothesisNecessity

universe v

/-! ## Conditional and constrained rows -/

section ConditionalConstrainedRows

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained

/-! ### Row: twoDDPForCTRS -/

/-- The argument filtering of `recur♯`. -/
def twoDDPForCTRSRecurFilterLens : FeatureLens twoDDPForCTRSData (List Nat) where
  get M := M.filter CSym.recur
  set M w := { M with filter := Function.update M.filter CSym.recur w }
  get_set M w := by simp
  set_get M := by cases M; simp
  set_set M w w' := by cases M; simp

/-- Filtering `recur♯` to its payload changes the witness filtering at `recur` only. -/
theorem twoDDPForCTRSPayloadFilter_eq :
    Function.update twoDWitnessAlg.filter CSym.recur [1] = twoDPayloadAlg.filter := by
  funext g
  cases g <;> rfl

theorem twoDDPForCTRSRecurFilterLens_set_payload :
    twoDDPForCTRSRecurFilterLens.set twoDDPForCTRSWitness [1] = twoDPayloadAlg := by
  show ({ twoDWitnessAlg with filter := Function.update twoDWitnessAlg.filter CSym.recur [1] } :
      CondAlgebra CSym) = { twoDWitnessAlg with filter := twoDPayloadAlg.filter }
  rw [twoDDPForCTRSPayloadFilter_eq]

def twoDDPForCTRSNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Filtering `recur♯` to its payload instead of its counter keeps the laws and loses the strict
2D pairs. -/
def twoDDPForCTRSNecessityStatement : Prop :=
  EscapeFeatureNecessity twoDDPForCTRSLaws twoDDPForCTRSAccepts twoDDPForCTRSRecurFilterLens

theorem twoDDPForCTRS_necessity : twoDDPForCTRSNecessityStatement :=
  ⟨⟨twoDDPForCTRSWitness, twoDDPForCTRSWitness_laws, twoDDPForCTRSWitness_result.1, [1],
    by decide,
    by rw [twoDDPForCTRSRecurFilterLens_set_payload]; exact twoDDPForCTRS_mutation.1,
    by rw [twoDDPForCTRSRecurFilterLens_set_payload]; exact twoDDPForCTRS_mutation.2⟩⟩

/-! ### Row: operationalTerminationCTRS -/

/-- The interpretation of the marked symbol `recur♯`. -/
def operationalTerminationCTRSRecurMarkedLens :
    FeatureLens operationalTerminationCTRSData (List Nat → Nat) where
  get M := M.marked (Sum.inl CSym.recur)
  set M w := { M with marked := Function.update M.marked (Sum.inl CSym.recur) w }
  get_set M w := by simp
  set_get M := by cases M; simp
  set_set M w w' := by cases M; simp

/-- The blind algebra changes the witness interpretation at `recur♯` only. -/
theorem operationalTerminationCTRSBlindMarked_eq :
    Function.update uWitnessAlg.marked (Sum.inl CSym.recur) (fun _ => 0) = uBlindAlg.marked := by
  funext g xs
  rcases g with f | p
  · cases f <;> rfl
  · rfl

theorem operationalTerminationCTRSRecurMarkedLens_set_blind :
    operationalTerminationCTRSRecurMarkedLens.set operationalTerminationCTRSWitness (fun _ => 0) =
      uBlindAlg := by
  show ({ uWitnessAlg with
      marked := Function.update uWitnessAlg.marked (Sum.inl CSym.recur) (fun _ => 0) } :
      MarkedAlgebra (USym CSym)) = { uWitnessAlg with marked := uBlindAlg.marked }
  rw [operationalTerminationCTRSBlindMarked_eq]

def operationalTerminationCTRSNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Interpreting `recur♯` by the constant `0` keeps the laws and loses the strict dependency pairs
of the unraveling. -/
def operationalTerminationCTRSNecessityStatement : Prop :=
  EscapeFeatureNecessity operationalTerminationCTRSLaws operationalTerminationCTRSAccepts
    operationalTerminationCTRSRecurMarkedLens

theorem operationalTerminationCTRSBlind_laws :
    operationalTerminationCTRSLaws
      (operationalTerminationCTRSRecurMarkedLens.set operationalTerminationCTRSWitness
        (fun _ => 0)) := by
  rw [operationalTerminationCTRSRecurMarkedLens_set_blind]
  exact operationalTerminationCTRS_mutation.1

theorem operationalTerminationCTRSBlind_rejects :
    ¬ operationalTerminationCTRSAccepts
      (operationalTerminationCTRSRecurMarkedLens.set operationalTerminationCTRSWitness
        (fun _ => 0)) := by
  rw [operationalTerminationCTRSRecurMarkedLens_set_blind]
  exact operationalTerminationCTRS_mutation.2

theorem operationalTerminationCTRS_necessity : operationalTerminationCTRSNecessityStatement :=
  ⟨⟨operationalTerminationCTRSWitness, operationalTerminationCTRSWitness_laws,
    operationalTerminationCTRSWitness_result.1, fun _ => 0,
    fun h => absurd (congrFun h [0, 0, 0]) (by decide),
    operationalTerminationCTRSBlind_laws, operationalTerminationCTRSBlind_rejects⟩⟩

/-! ### Row: integerTermRewriting -/

/-- The value of the fresh constant of the reduction pair processor. -/
def integerTermRewritingBoundLens : FeatureLens integerTermRewritingData Int where
  get M := M.bound
  set M w := { M with bound := w }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

def integerTermRewritingNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Raising the fresh constant from `1` to `2` keeps the laws and loses the bounded pair. -/
def integerTermRewritingNecessityStatement : Prop :=
  EscapeFeatureNecessity integerTermRewritingLaws integerTermRewritingAccepts
    integerTermRewritingBoundLens

theorem integerTermRewriting_necessity : integerTermRewritingNecessityStatement :=
  ⟨⟨integerTermRewritingWitness, integerTermRewritingWitness_laws,
    integerTermRewritingWitness_result.1, 2, by decide, integerTermRewriting_mutation.1,
    integerTermRewriting_mutation.2⟩⟩

/-! ### Row: lctrs -/

/-- The bound of the value criterion. -/
def lctrsBoundLens : FeatureLens lctrsData Int where
  get M := M.bound
  set M w := { M with bound := w }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

def lctrsNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Raising the value bound from `0` to `1` keeps the laws and loses the value criterion. -/
def lctrsNecessityStatement : Prop :=
  EscapeFeatureNecessity lctrsLaws lctrsAccepts lctrsBoundLens

theorem lctrs_necessity : lctrsNecessityStatement :=
  ⟨⟨lctrsWitness, lctrsWitness_laws, lctrsWitness_accepts, 1, by decide, lctrs_mutation.1,
    lctrs_mutation.2⟩⟩

end ConditionalConstrainedRows

/-! ## Semantic-framework rows -/

section SemanticFrameworkRows

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.FreePolynomialTermination
open OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks

/-! ### Row: abstractInterpretationAdmittance -/

/-- The ranking of the abstract domain. -/
def abstractInterpretationAdmittanceRankLens :
    FeatureLens abstractInterpretationAdmittanceData (Nat → Nat) where
  get M := M.rank
  set M w := { M with rank := w }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

def abstractInterpretationAdmittanceNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Replacing the identity ranking by the constant ranking keeps the laws and loses the decrease
on the abstract transitions. -/
def abstractInterpretationAdmittanceNecessityStatement : Prop :=
  EscapeFeatureNecessity abstractInterpretationAdmittanceLaws
    abstractInterpretationAdmittanceAccepts abstractInterpretationAdmittanceRankLens

theorem abstractInterpretationAdmittance_necessity :
    abstractInterpretationAdmittanceNecessityStatement :=
  ⟨⟨abstractInterpretationAdmittanceWitness, abstractInterpretationAdmittanceWitness_laws,
    abstractInterpretationAdmittanceWitness_accepts, fun _ => 0,
    fun h => absurd (congrFun h 1) (by decide),
    abstractInterpretationAdmittance_unlinked_rank.1,
    abstractInterpretationAdmittance_unlinked_rank.2⟩⟩

/-! ### Row: categoricalToposTermination -/

/-- Under the backward morphism law, the image of every free term is accessible in the
coalgebra: each next state of an image is the image of a root step, and root steps are well
founded. -/
theorem categoricalToposTermination_hom_acc (M : categoricalToposTerminationData)
    (hL : categoricalToposTerminationLaws M) (t : FreeTerm Nat) :
    Acc (fun y x : M.X => y ∈ M.next x) (M.hom t) := by
  have hacc := (main_free_root_termination Nat).apply t
  induction hacc with
  | intro t _ ih =>
    refine Acc.intro _ fun y hy => ?_
    obtain ⟨u, hu, rfl⟩ := hL.2 t y hy
    exact ih u hu

/-- Every lawful coalgebra morphism is accepted. -/
theorem categoricalToposTermination_accepts_of_laws (M : categoricalToposTerminationData)
    (hL : categoricalToposTerminationLaws M) : categoricalToposTerminationAccepts M :=
  ⟨fun _ _ => categoricalToposTermination_hom_acc M hL _,
    fun _ _ _ => categoricalToposTermination_hom_acc M hL _⟩

def categoricalToposTerminationNecessityKind : RowNecessityKind := .noApplicableHypothesis

/-- The coalgebra-morphism laws transport well-foundedness of the root steps to the images of the
rule sources, so every lawful datum is accepted. -/
def categoricalToposTerminationNecessityStatement : Prop :=
  NoApplicableHypothesis categoricalToposTerminationLaws categoricalToposTerminationAccepts
    .lawsDetermineVerdict

theorem categoricalToposTermination_necessity : categoricalToposTerminationNecessityStatement :=
  ⟨⟨categoricalToposTerminationWitness, categoricalToposTerminationWitness_laws⟩,
    fun M M' hM hM' => iff_of_true (categoricalToposTermination_accepts_of_laws M hM)
      (categoricalToposTermination_accepts_of_laws M' hM')⟩

/-- No feature change of a lawful coalgebra morphism separates acceptance from rejection. -/
theorem categoricalToposTermination_no_feature_control {V : Sort v}
    (L : FeatureLens categoricalToposTerminationData V) :
    ¬ EscapeFeatureNecessity categoricalToposTerminationLaws categoricalToposTerminationAccepts L :=
  NoApplicableHypothesis.no_feature_control categoricalToposTermination_necessity L

/-! ### Row: higherOrderLCTRS -/

/-- The bound of the value criterion. -/
def higherOrderLCTRSBoundLens : FeatureLens higherOrderLCTRSData Int where
  get M := M.bound
  set M w := { M with bound := w }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

def higherOrderLCTRSNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Raising the value bound from `0` to `1` keeps the laws and loses the value criterion. -/
def higherOrderLCTRSNecessityStatement : Prop :=
  EscapeFeatureNecessity higherOrderLCTRSLaws higherOrderLCTRSAccepts higherOrderLCTRSBoundLens

theorem higherOrderLCTRS_necessity : higherOrderLCTRSNecessityStatement :=
  ⟨⟨higherOrderLCTRSWitness, higherOrderLCTRSWitness_laws, higherOrderLCTRSWitness_accepts, 1,
    by decide, higherOrderLCTRS_mutation.1, higherOrderLCTRS_mutation.2⟩⟩

end SemanticFrameworkRows

/-! ## Typed-calculi rows -/

section TypedCalculiRows

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi

/-! ### Row: horpoAdmittance -/

/-- Every precedence and status accepts the typed free system. -/
theorem horpoAdmittance_accepts_all (M : horpoAdmittanceData) : horpoAdmittanceAccepts M :=
  fun A => horpo_accepts_iter M.prec M.stat A

def horpoAdmittanceNecessityKind : RowNecessityKind := .noApplicableHypothesis

/-- The HORPO clauses accept both typed iterator rules under every precedence and status, so every
lawful datum is accepted. -/
def horpoAdmittanceNecessityStatement : Prop :=
  NoApplicableHypothesis horpoAdmittanceLaws horpoAdmittanceAccepts .lawsDetermineVerdict

theorem horpoAdmittance_necessity : horpoAdmittanceNecessityStatement :=
  ⟨⟨horpoAdmittanceWitness, horpoAdmittanceWitness_laws⟩, fun M M' _ _ =>
    iff_of_true (horpoAdmittance_accepts_all M) (horpoAdmittance_accepts_all M')⟩

/-- No feature change of a lawful precedence and status separates acceptance from rejection. -/
theorem horpoAdmittance_no_feature_control {V : Sort v} (L : FeatureLens horpoAdmittanceData V) :
    ¬ EscapeFeatureNecessity horpoAdmittanceLaws horpoAdmittanceAccepts L :=
  NoApplicableHypothesis.no_feature_control horpoAdmittance_necessity L

/-! ### Row: cpoAdmittance -/

/-- Every ingredient tuple accepts the typed free system. -/
theorem cpoAdmittance_accepts_all (M : cpoAdmittanceData) : cpoAdmittanceAccepts M :=
  fun A => ⟨cpo_zero_rule (.iter A) rfl M, cpo_iter_succ A M⟩

def cpoAdmittanceNecessityKind : RowNecessityKind := .noApplicableHypothesis

/-- The CPO clauses accept both typed iterator rules for every ingredient tuple, so every lawful
datum is accepted. -/
def cpoAdmittanceNecessityStatement : Prop :=
  NoApplicableHypothesis cpoAdmittanceLaws cpoAdmittanceAccepts .lawsDetermineVerdict

theorem cpoAdmittance_necessity : cpoAdmittanceNecessityStatement :=
  ⟨⟨cpoAdmittanceWitness, cpoAdmittanceWitness_laws⟩, fun M M' _ _ =>
    iff_of_true (cpoAdmittance_accepts_all M) (cpoAdmittance_accepts_all M')⟩

/-- No feature change of a lawful ingredient tuple separates acceptance from rejection. -/
theorem cpoAdmittance_no_feature_control {V : Sort v} (L : FeatureLens cpoAdmittanceData V) :
    ¬ EscapeFeatureNecessity cpoAdmittanceLaws cpoAdmittanceAccepts L :=
  NoApplicableHypothesis.no_feature_control cpoAdmittance_necessity L

/-! ### Row: generalSchemaAdmittance -/

/-- Every precedence and status accepts the typed free system. -/
theorem generalSchemaAdmittance_accepts_all (M : generalSchemaAdmittanceData) :
    generalSchemaAdmittanceAccepts M :=
  fun A => ⟨gs_zero_rule (.iter A) M.prec M.stat, gs_iter_succ A M.prec M.stat⟩

def generalSchemaAdmittanceNecessityKind : RowNecessityKind := .noApplicableHypothesis

/-- Both typed iterator rules follow the General Schema under every precedence and status, so
every lawful datum is accepted. -/
def generalSchemaAdmittanceNecessityStatement : Prop :=
  NoApplicableHypothesis generalSchemaAdmittanceLaws generalSchemaAdmittanceAccepts
    .lawsDetermineVerdict

theorem generalSchemaAdmittance_necessity : generalSchemaAdmittanceNecessityStatement :=
  ⟨⟨generalSchemaAdmittanceWitness, generalSchemaAdmittanceWitness_laws⟩, fun M M' _ _ =>
    iff_of_true (generalSchemaAdmittance_accepts_all M) (generalSchemaAdmittance_accepts_all M')⟩

/-- No feature change of a lawful precedence and status separates acceptance from rejection. -/
theorem generalSchemaAdmittance_no_feature_control {V : Sort v}
    (L : FeatureLens generalSchemaAdmittanceData V) :
    ¬ EscapeFeatureNecessity generalSchemaAdmittanceLaws generalSchemaAdmittanceAccepts L :=
  NoApplicableHypothesis.no_feature_control generalSchemaAdmittance_necessity L

/-! ### Row: sizedTypesAdmittance -/

/-- The size-annotated labels of the pattern variables at result type `nat`. -/
def sizedTypesAdmittanceNatLabelsLens : FeatureLens sizedTypesAdmittanceData (TVar → SzTy) where
  get M := M.labels natTy
  set M w := { M with labels := Function.update M.labels natTy w }
  get_set M w := by simp
  set_get M := by cases M; simp
  set_set M w w' := by cases M; simp

/-- The iterator labels at result type `nat` with the base labelled at the sort `o`. -/
def sizedTypesAdmittanceSoBaseLabels : TVar → SzTy
  | .b => .so
  | .s => liftTy (.arrow natTy natTy)
  | .n => .snat (.var 0)

/-- A variable whose label is `o` is typed only at `o`: the variable rule gives its label and
subtyping preserves `o`. -/
theorem sizedTypesAdmittance_var_b_so {g : TSym} {i : Nat} {Δ : TVar → SzTy} (hb : Δ .b = .so)
    {t : TTerm TVar} {σ : SzTy} (h : SzHas g i Δ t σ) : t = .var .b → σ = .so := by
  induction h with
  | var x =>
      intro hx
      cases hx
      exact hb
  | zero s => intro hx; cases hx
  | succ s _ _ => intro hx; cases hx
  | call _ _ _ _ _ _ => intro hx; cases hx
  | ap _ _ _ _ => intro hx; cases hx
  | sub _ hs ih =>
      intro hx
      have hσ := ih hx
      subst hσ
      cases hs
      rfl

theorem sizedTypesAdmittanceSoBase_laws :
    sizedTypesAdmittanceLaws
      (sizedTypesAdmittanceNatLabelsLens.set sizedTypesAdmittanceWitness
        sizedTypesAdmittanceSoBaseLabels) := by
  intro A
  show ¬ (Function.update (sizedIterLabels 0) natTy sizedTypesAdmittanceSoBaseLabels A .b).hasVar 0 ∧
    ¬ (Function.update (sizedIterLabels 0) natTy sizedTypesAdmittanceSoBaseLabels A .s).hasVar 0 ∧
    Function.update (sizedIterLabels 0) natTy sizedTypesAdmittanceSoBaseLabels A .n = .snat (.var 0)
  by_cases hA : A = natTy
  · subst hA
    simp only [Function.update_self]
    exact ⟨fun h => h, liftTy_noVar 0 _, rfl⟩
  · simp only [Function.update_of_ne hA]
    exact ⟨liftTy_noVar 0 A, liftTy_noVar 0 _, rfl⟩

theorem sizedTypesAdmittanceSoBase_rejects :
    ¬ sizedTypesAdmittanceAccepts
      (sizedTypesAdmittanceNatLabelsLens.set sizedTypesAdmittanceWitness
        sizedTypesAdmittanceSoBaseLabels) := by
  intro h
  have hb : Function.update (sizedIterLabels 0) natTy sizedTypesAdmittanceSoBaseLabels natTy .b =
      .so := by
    simp [sizedTypesAdmittanceSoBaseLabels]
  exact absurd (sizedTypesAdmittance_var_b_so hb (h natTy).1 rfl) (by decide)

def sizedTypesAdmittanceNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Labelling the base at the sort `o` in the result type `nat` keeps the freshness and counter
laws and makes the base untypable at its result type. -/
def sizedTypesAdmittanceNecessityStatement : Prop :=
  EscapeFeatureNecessity sizedTypesAdmittanceLaws sizedTypesAdmittanceAccepts
    sizedTypesAdmittanceNatLabelsLens

theorem sizedTypesAdmittance_necessity : sizedTypesAdmittanceNecessityStatement :=
  ⟨⟨sizedTypesAdmittanceWitness, sizedTypesAdmittanceWitness_laws,
    fun A => sized_iter_accepts 0 A, sizedTypesAdmittanceSoBaseLabels,
    fun h => absurd (congrFun h .b) (by decide),
    sizedTypesAdmittanceSoBase_laws, sizedTypesAdmittanceSoBase_rejects⟩⟩

end TypedCalculiRows

/-! ## Typing-discipline rows -/

section TypingDisciplineRows

open OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines

/-! ### Row: coqGuardAdmittance -/

/-- The declared decreasing parameter. -/
def coqGuardAdmittanceStructArgLens : FeatureLens coqGuardAdmittanceData Nat where
  get M := M.structArg
  set M w := { M with structArg := w }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

def coqGuardAdmittanceNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Declaring the payload instead of the counter as the decreasing parameter keeps the law and
fails the guard. -/
def coqGuardAdmittanceNecessityStatement : Prop :=
  EscapeFeatureNecessity coqGuardAdmittanceLaws coqGuardAdmittanceAccepts
    coqGuardAdmittanceStructArgLens

theorem coqGuardAdmittance_necessity : coqGuardAdmittanceNecessityStatement :=
  ⟨⟨coqGuardAdmittanceWitness, coqGuardAdmittanceWitness_laws,
    coqGuardAdmittanceWitness_accepts, 1, by decide, coqGuardAdmittance_mutation.1,
    coqGuardAdmittance_mutation.2⟩⟩

/-! ### Row: bellantoniCookSplit -/

/-- The normal or safe position of the payload `s`. -/
def bellantoniCookSplitPayloadPosLens : FeatureLens bellantoniCookSplitData Pos where
  get M := M.pos RV.s
  set M w := { M with pos := Function.update M.pos RV.s w }
  get_set M w := by simp
  set_get M := by cases M; simp
  set_set M w w' := by cases M; simp

def bellantoniCookSplitNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Making the payload safe keeps the counter normal and fails the safe-composition check. -/
def bellantoniCookSplitNecessityStatement : Prop :=
  EscapeFeatureNecessity bellantoniCookSplitLaws bellantoniCookSplitAccepts
    bellantoniCookSplitPayloadPosLens

theorem bellantoniCookSplit_necessity : bellantoniCookSplitNecessityStatement :=
  ⟨⟨bellantoniCookSplitWitness, bellantoniCookSplitWitness_laws,
    bellantoniCookSplitWitness_accepts, .safe, by decide, rfl,
    fun h => absurd ((bellantoniCook_accepts_iff _).1 h).2 (by decide)⟩⟩

/-! ### Row: linearLogicTypingBarrier -/

/-- The deleted clause: the formula of the payload `s` has no exponential. -/
def linearLogicTypingBarrierDeletedLaw (M : linearLogicTypingBarrierData) : Prop :=
  (M.ctx RV.s).ExpFree

/-- The retained clauses: the formulas of the base `b` and the counter `n` have no exponential. -/
def linearLogicTypingBarrierOtherLaws (M : linearLogicTypingBarrierData) : Prop :=
  (M.ctx RV.b).ExpFree ∧ (M.ctx RV.n).ExpFree

def linearLogicTypingBarrierNecessityKind : RowNecessityKind := .deletedBarrierPremise

/-- Without the exponential-free payload, the reusable payload `s : !B` keeps the other clauses
and types both sides of the successor rule. -/
def linearLogicTypingBarrierNecessityStatement : Prop :=
  BarrierPremiseNecessity linearLogicTypingBarrierLaws linearLogicTypingBarrierOtherLaws
    linearLogicTypingBarrierDeletedLaw linearLogicTypingBarrierAccepts

theorem linearLogicTypingBarrier_necessity : linearLogicTypingBarrierNecessityStatement :=
  ⟨fun _ => ⟨fun h => ⟨⟨h RV.b, h RV.n⟩, h RV.s⟩,
      fun ⟨⟨hb, hn⟩, hs⟩ x => by cases x <;> assumption⟩,
    linearLogicTypingBarrier_universal,
    ⟨⟨{ linearLogicTypingBarrierWitness with ctx := reusableCtx }, ⟨trivial, trivial⟩,
      fun h => h, linearLogicTypingBarrierWitness_feature.1⟩⟩⟩

/-! ### Row: ramifiedRecursionTypingBarrier -/

/-- The tier of the payload `s`. -/
def ramifiedRecursionTypingBarrierPayloadTierLens :
    FeatureLens ramifiedRecursionTypingBarrierData Nat where
  get M := M.tier RV.s
  set M w := { M with tier := Function.update M.tier RV.s w }
  get_set M w := by simp
  set_get M := by cases M; simp
  set_set M w w' := by cases M; simp

def ramifiedRecursionTypingBarrierNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Raising the payload to the counter tier keeps the ramification law and fails the tier
judgment, which needs the payload at the result tier. -/
def ramifiedRecursionTypingBarrierNecessityStatement : Prop :=
  EscapeFeatureNecessity ramifiedRecursionTypingBarrierLaws ramifiedRecursionTypingBarrierAccepts
    ramifiedRecursionTypingBarrierPayloadTierLens

theorem ramifiedRecursionTypingBarrier_necessity :
    ramifiedRecursionTypingBarrierNecessityStatement :=
  ⟨⟨ramifiedRecursionTypingBarrierWitness, ramifiedRecursionTypingBarrierWitness_laws,
    ramifiedRecursionTypingBarrierWitness_accepts, 1, by decide, Nat.zero_lt_one,
    fun h => absurd ((ramified_accepts_iff _).1 h).2.2 (by decide)⟩⟩

end TypingDisciplineRows

/-! ## Graph-calculi rows -/

section GraphCalculiRows

open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness
open OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi

/-! ### Row: weightedTypeGraphEscape -/

/-- The weighted type graph. -/
def weightedTypeGraphEscapeTypeGraphLens : FeatureLens weightedTypeGraphEscapeData TypeGraph where
  get M := M.typeGraph
  set M w := { M with typeGraph := w }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The witness type graph with every `wrap` occurrence at weight `3`, on and off the diagonal. -/
def weightedTypeGraphEscapeFlatWrapGraph : TypeGraph :=
  { twoNodeGraph with
    edgeWeight := Function.update twoNodeGraph.edgeWeight FreeSym.wrap (fun _ _ => 3) }

/-- The weight of a `wrap` occurrence whose two arguments have distinct types. -/
def weightedTypeGraphEscapeWrapProbe (T : TypeGraph) : Nat :=
  T.edgeWeight FreeSym.wrap
    (fun i => if i.val = 0 then T.flower else ⟨1, by have h := T.two_le; omega⟩) T.flower

theorem weightedTypeGraphEscapeFlatWrap_laws :
    weightedTypeGraphEscapeLaws
      { weightedTypeGraphEscapeWitness with typeGraph := weightedTypeGraphEscapeFlatWrapGraph } := by
  refine ⟨fun h => weightedTypeGraphEscapeWitness_laws.1 h, ?_,
    weightedTypeGraphEscapeWitness_laws.2.2⟩
  intro s
  cases s <;> decide

theorem weightedTypeGraphEscapeFlatWrap_rejects :
    ¬ weightedTypeGraphEscapeAccepts
      { weightedTypeGraphEscapeWitness with typeGraph := weightedTypeGraphEscapeFlatWrapGraph } := by
  intro h
  obtain ⟨ψ, hψ⟩ := h ⟨recurSuccLhs, recurSuccRhs⟩ (List.mem_cons_of_mem _ List.mem_cons_self)
    (fun _ => TypeGraph.flower weightedTypeGraphEscapeFlatWrapGraph)
  simp [edgeSum, edgeWeightAt, recurSuccLhs, recurSuccRhs, weightedTypeGraphEscapeFlatWrapGraph,
    Function.update_self, twoNodeGraph] at hψ

def weightedTypeGraphEscapeNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Making the weight of `wrap` independent of its argument types keeps the laws and loses the
decrease of the successor rule. -/
def weightedTypeGraphEscapeNecessityStatement : Prop :=
  EscapeFeatureNecessity weightedTypeGraphEscapeLaws weightedTypeGraphEscapeAccepts
    weightedTypeGraphEscapeTypeGraphLens

theorem weightedTypeGraphEscape_necessity : weightedTypeGraphEscapeNecessityStatement :=
  ⟨⟨weightedTypeGraphEscapeWitness, weightedTypeGraphEscapeWitness_laws,
    weightedTypeGraphEscapeWitness_accepts, weightedTypeGraphEscapeFlatWrapGraph,
    fun h => absurd (congrArg weightedTypeGraphEscapeWrapProbe h) (by decide),
    weightedTypeGraphEscapeFlatWrap_laws, weightedTypeGraphEscapeFlatWrap_rejects⟩⟩

/-! ### Row: generalizedWeightedTypeGraphs -/

/-- Edge-weight tables of two-node generalized type graphs over the arithmetic semiring. -/
abbrev generalizedWeightedTypeGraphsTable : Type :=
  (s : FreeSym) → (Fin (symArity s) → Fin 2) → Fin 2 → Nat

/-- The two-node generalized type graph of a table. -/
def generalizedWeightedTypeGraphsGraphOf (w : generalizedWeightedTypeGraphsTable) :
    GeneralizedTypeGraph arithWeight :=
  ⟨2, by decide, w⟩

/-- The row datum of a table: the witness system with the table's type graph and its arithmetic
minimum graph weight. -/
def generalizedWeightedTypeGraphsDataOf (w : generalizedWeightedTypeGraphsTable) :
    generalizedWeightedTypeGraphsData where
  algebra := arithWeight
  typeGraph := generalizedWeightedTypeGraphsGraphOf w
  graphWeight := arithGraphWeight (generalizedWeightedTypeGraphsGraphOf w)
  rules := freeRecursorDPRules
  step := fun x y => ∃ r ∈ freeRecursorDPRules, x = r.lhs ∧ y = r.rhs
  readBack := ReadsBack

/-- The weights of `wrap` occurrences in a table. -/
def generalizedWeightedTypeGraphsWrapLens :
    FeatureLens generalizedWeightedTypeGraphsTable
      ((Fin (symArity FreeSym.wrap) → Fin 2) → Fin 2 → Nat) where
  get w := w FreeSym.wrap
  set w u := Function.update w FreeSym.wrap u
  get_set w u := by simp
  set_get w := by simp
  set_set w u u' := by simp

/-- The witness table. -/
def generalizedWeightedTypeGraphsBaseTable : generalizedWeightedTypeGraphsTable :=
  twoNodeGTypeGraph.edgeWeight

theorem generalizedWeightedTypeGraphsBaseTable_pos (s : FreeSym)
    (args : Fin (symArity s) → Fin 2) (r : Fin 2) :
    0 < generalizedWeightedTypeGraphsBaseTable s args r := by
  cases s <;> simp only [generalizedWeightedTypeGraphsBaseTable, twoNodeGTypeGraph] <;>
    (try split) <;> decide

/-- A table with positive weights gives a lawful datum. -/
theorem generalizedWeightedTypeGraphsDataOf_laws (w : generalizedWeightedTypeGraphsTable)
    (hpos : ∀ s args r, 0 < w s args r) :
    generalizedWeightedTypeGraphsLaws (generalizedWeightedTypeGraphsDataOf w) := by
  refine ⟨fun h => h, fun H => arithGraphWeight_isMin _ H, ?_, fun _ => graphSymbols_ofSymbols _⟩
  intro s args r a b hab
  exact Nat.mul_lt_mul_of_pos_left hab (hpos s args r)

/-- The witness table with every `wrap` occurrence at weight `3`. -/
def generalizedWeightedTypeGraphsFlatWrapTable : generalizedWeightedTypeGraphsTable :=
  generalizedWeightedTypeGraphsWrapLens.set generalizedWeightedTypeGraphsBaseTable (fun _ _ => 3)

theorem generalizedWeightedTypeGraphsFlatWrapTable_pos (s : FreeSym)
    (args : Fin (symArity s) → Fin 2) (r : Fin 2) :
    0 < generalizedWeightedTypeGraphsFlatWrapTable s args r := by
  cases s <;>
    first
    | (show 0 < Function.update generalizedWeightedTypeGraphsBaseTable FreeSym.wrap
          (fun _ _ => 3) FreeSym.wrap args r
       rw [Function.update_self]; decide)
    | (show 0 < Function.update generalizedWeightedTypeGraphsBaseTable FreeSym.wrap
          (fun _ _ => 3) _ args r
       rw [Function.update_of_ne (by decide)]
       exact generalizedWeightedTypeGraphsBaseTable_pos _ _ _)

theorem generalizedWeightedTypeGraphsFlatWrap_rejects :
    ¬ generalizedWeightedTypeGraphsAccepts
      (generalizedWeightedTypeGraphsDataOf generalizedWeightedTypeGraphsFlatWrapTable) := by
  intro h
  obtain ⟨ψ, hψ⟩ := h ⟨recurSuccLhs, recurSuccRhs⟩ (List.mem_cons_of_mem _ List.mem_cons_self)
    (fun _ => ⟨0, by decide⟩)
  simp [gEdgeSum, wmul, recurSuccLhs, recurSuccRhs, generalizedWeightedTypeGraphsDataOf,
    generalizedWeightedTypeGraphsGraphOf, generalizedWeightedTypeGraphsFlatWrapTable,
    generalizedWeightedTypeGraphsWrapLens, generalizedWeightedTypeGraphsBaseTable,
    Function.update_self, twoNodeGTypeGraph, arithWeight] at hψ

def generalizedWeightedTypeGraphsNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- On two-node edge-weight tables over the arithmetic semiring, with every other field of the
witness fixed and the arithmetic minimum as graph weight, making the weight of `wrap` independent
of its argument types keeps the laws and loses the strong decrease of the successor rule. -/
def generalizedWeightedTypeGraphsNecessityStatement : Prop :=
  EscapeFeatureNecessity
    (fun w => generalizedWeightedTypeGraphsLaws (generalizedWeightedTypeGraphsDataOf w))
    (fun w => generalizedWeightedTypeGraphsAccepts (generalizedWeightedTypeGraphsDataOf w))
    generalizedWeightedTypeGraphsWrapLens

theorem generalizedWeightedTypeGraphs_necessity :
    generalizedWeightedTypeGraphsNecessityStatement :=
  ⟨⟨generalizedWeightedTypeGraphsBaseTable,
    generalizedWeightedTypeGraphsDataOf_laws _ generalizedWeightedTypeGraphsBaseTable_pos,
    generalizedWeightedTypeGraphsWitness_accepts, fun _ _ => 3,
    fun h => absurd (congrFun (congrFun h (fun i => if i.val = 0 then (0 : Fin 2) else 1)) 0)
      (by decide),
    generalizedWeightedTypeGraphsDataOf_laws _ generalizedWeightedTypeGraphsFlatWrapTable_pos,
    generalizedWeightedTypeGraphsFlatWrap_rejects⟩⟩

/-! ### Row: quasiInterpretationsSharingAware -/

/-- The quasi-interpretation. -/
def quasiInterpretationsSharingAwareEvalLens :
    FeatureLens quasiInterpretationsSharingAwareData (SharedTerm → Nat) where
  get M := M.eval
  set M w := { M with eval := w }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The witness assignment with each sharing node charged `3`. -/
def quasiInterpretationsSharingAwareHeavyShareEval (t : SharedTerm) : Nat :=
  freeSize (unshare t) + 3 * sharedCount t

theorem quasiInterpretationsSharingAwareHeavyShare_laws :
    quasiInterpretationsSharingAwareLaws
      { quasiInterpretationsSharingAwareWitness with
        eval := quasiInterpretationsSharingAwareHeavyShareEval } := by
  refine ⟨?_, ?_, ?_, fun a => ⟨a, rfl, rfl⟩, ?_⟩
  · show 1 ≤ freeSize (unshare .leaf) + 3 * sharedCount .leaf
    simp [unshare, sharedCount, freeSize]
  · intro a b
    show freeSize (unshare a) + 3 * sharedCount a + (freeSize (unshare b) + 3 * sharedCount b) + 1 ≤
      freeSize (unshare (.node a b)) + 3 * sharedCount (.node a b)
    simp only [unshare, sharedCount, freeSize]
    omega
  · intro a
    show freeSize (unshare a) + 3 * sharedCount a ≤
      freeSize (unshare (.shared a)) + 3 * sharedCount (.shared a)
    simp only [unshare, sharedCount]
    omega
  · intro t
    show freeSize (unshare t) ≤ freeSize (unshare t) + 3 * sharedCount t
    exact Nat.le_add_right _ _

theorem quasiInterpretationsSharingAwareHeavyShare_rejects :
    ¬ quasiInterpretationsSharingAwareAccepts
      { quasiInterpretationsSharingAwareWitness with
        eval := quasiInterpretationsSharingAwareHeavyShareEval } := by
  intro h
  have hle := h (x := .node .leaf .leaf) (y := .shared .leaf) ⟨.leaf, rfl, rfl⟩
  exact absurd hle (by decide)

def quasiInterpretationsSharingAwareNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Charging each sharing node `3` keeps the quasi-interpretation laws and makes the sharing
contraction increase the assignment. -/
def quasiInterpretationsSharingAwareNecessityStatement : Prop :=
  EscapeFeatureNecessity quasiInterpretationsSharingAwareLaws
    quasiInterpretationsSharingAwareAccepts quasiInterpretationsSharingAwareEvalLens

theorem quasiInterpretationsSharingAware_necessity :
    quasiInterpretationsSharingAwareNecessityStatement :=
  ⟨⟨quasiInterpretationsSharingAwareWitness, quasiInterpretationsSharingAwareWitness_laws,
    quasiInterpretationsSharingAwareWitness_accepts, quasiInterpretationsSharingAwareHeavyShareEval,
    fun h => absurd (congrFun h (.shared .leaf)) (by decide),
    quasiInterpretationsSharingAwareHeavyShare_laws,
    quasiInterpretationsSharingAwareHeavyShare_rejects⟩⟩

end GraphCalculiRows

/-! ## Process-calculi rows -/

section ProcessCalculiRows

open OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi

/-! ### Row: piCalculusTerminationTranslation -/

def piCalculusTerminationTranslationNecessityKind : RowNecessityKind := .noApplicableHypothesis

/-- The laws and the acceptance predicate are the same two conditions, so every lawful datum is
accepted. -/
def piCalculusTerminationTranslationNecessityStatement : Prop :=
  NoApplicableHypothesis piCalculusTerminationTranslationLaws
    piCalculusTerminationTranslationAccepts .lawsDetermineVerdict

theorem piCalculusTerminationTranslation_necessity :
    piCalculusTerminationTranslationNecessityStatement :=
  ⟨⟨piCalculusTerminationTranslationWitness, piCalculusTerminationTranslationWitness_laws⟩,
    fun _ _ hM hM' => iff_of_true hM hM'⟩

/-- No feature change of a lawful level and data certificate separates acceptance from
rejection. -/
theorem piCalculusTerminationTranslation_no_feature_control {V : Sort v}
    (L : FeatureLens piCalculusTerminationTranslationData V) :
    ¬ EscapeFeatureNecessity piCalculusTerminationTranslationLaws
      piCalculusTerminationTranslationAccepts L :=
  NoApplicableHypothesis.no_feature_control piCalculusTerminationTranslation_necessity L

/-! ### Row: lambdaMuSNViaCPS -/

def lambdaMuSNViaCPSNecessityKind : RowNecessityKind := .noApplicableHypothesis

/-- The laws and the acceptance predicate are the same image-decrease condition, so every lawful
translation is accepted. -/
def lambdaMuSNViaCPSNecessityStatement : Prop :=
  NoApplicableHypothesis lambdaMuSNViaCPSLaws lambdaMuSNViaCPSAccepts .lawsDetermineVerdict

theorem lambdaMuSNViaCPS_necessity : lambdaMuSNViaCPSNecessityStatement :=
  ⟨⟨lambdaMuSNViaCPSWitness, lambdaMuSNViaCPSWitness_laws⟩, fun _ _ hM hM' => iff_of_true hM hM'⟩

/-- No feature change of a lawful translation separates acceptance from rejection. -/
theorem lambdaMuSNViaCPS_no_feature_control {V : Sort v} (L : FeatureLens lambdaMuSNViaCPSData V) :
    ¬ EscapeFeatureNecessity lambdaMuSNViaCPSLaws lambdaMuSNViaCPSAccepts L :=
  NoApplicableHypothesis.no_feature_control lambdaMuSNViaCPS_necessity L

end ProcessCalculiRows

end OperatorKO7.Methods.OrientationClosure.HypothesisNecessity
