import Mathlib
import OperatorKO7.Meta.Methods.OrientationClosure.PolynomialOrientationDecision
import OperatorKO7.Meta.Methods.OrientationClosure.ContextLiftMetatheorem
import OperatorKO7.Meta.Methods.OrientationClosure.FreePolynomialTermination

/-!
# P5 method rows: algebraic and semantic interpretation methods

Fifteen rows of the Orientation Boundary method universe. Each row fixes the native data of its
method, the admissibility laws of its pinned primary definition, the method's own acceptance of
the free duplicating rule `recur b s (succ n) → wrap s (recur b s n)`
(`SchemaCore.RootStep.recurSucc`), and the proved verdict.

| Row | Verdict | Route |
|---|---|---|
| `linearPolyQ`, `linearPolyR` | barrier | P3.2 cell over a separated ordered field |
| `negativeCoefficientPolynomial` | escape | truncated cubic member; soundness by P3.4 |
| `maxPolynomial` | escape | coupled member with an active `max`; max-plus recursors in the P3.2 cell |
| `nonlinearHigherDegreePolynomial` | escape | P3.5 decides every unit-successor member |
| `multilinearInterpretation` | escape | P3.5 classification; step-counter coupling is necessary |
| `matrixNScalarProjection`, `triangularMatrix` | barrier | P3.2 cell at the tracked coordinate |
| `matrixQRScalarProjection` | barrier | P3.2 cell over the reals at the tracked coordinate |
| `arcticScalarProjection` | barrier | contextual masking by `max`; root orienter exists |
| `tropicalScalarProjection` | barrier | contextual masking by `min`; root orienter exists |
| `tupleInterpretationStrictS` | escape | cross-coupled first component; multiplication-free first components in the P3.2 cell |
| `strictMonotoneAlgebraArchimedean` | escape | coupled algebra; P3.1 blocks the uniform-gain subclass |
| `extendedMonotoneAlgebra` | escape | two-relation algebra; P3.2 blocks bounded tracked gain |
| `finiteModelTermination` | barrier | a finite strict carrier cannot host the growing chain |
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations

open OperatorKO7.StepDuplicating
open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.InterpretationLaws
open OperatorKO7.Methods.OrientationClosure.CellClassification
open OperatorKO7.Methods.OrientationClosure.CouplingTheorem
open OperatorKO7.Methods.OrientationClosure.PolynomialOrientationDecision
open OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem
open OperatorKO7.Methods.OrientationClosure.SignatureGeneric

/-! ## The free duplicating rule and the acceptance notions -/

/-- Left side `recur b s (succ n)` of the free duplicating rule; the rule variables `b, s, n` are
`0, 1, 2`. -/
def dupLhs : FreeTerm (Fin 3) := .recur (.var 0) (.var 1) (.succ (.var 2))

/-- Right side `wrap s (recur b s n)` of the free duplicating rule. -/
def dupRhs : FreeTerm (Fin 3) := .wrap (.var 1) (.recur (.var 0) (.var 1) (.var 2))

/-- The two sides are the free root step `RootStep.recurSucc`. -/
theorem dup_rootStep : RootStep dupLhs dupRhs := RootStep.recurSucc _ _ _

/-- Orientation of the free duplicating rule on a domain `D` of carrier values: every assignment
of the rule variables into `D` makes the value of the right side strictly smaller in `lt`. -/
def DupOrientedOn {α : Type} (D : α → Prop) (I : Interpretation α) (lt : α → α → Prop) : Prop :=
  ∀ ρ : Fin 3 → α, (∀ i, D (ρ i)) → lt (I.eval ρ dupRhs) (I.eval ρ dupLhs)

/-- Orientation of the free duplicating rule over the whole carrier. -/
def DupOriented {α : Type} (I : Interpretation α) (lt : α → α → Prop) : Prop :=
  DupOrientedOn (fun _ => True) I lt

/-- Rule orientation is the pointwise algebraic comparison at the three rule variables. -/
theorem dupOrientedOn_iff {α : Type} (D : α → Prop) (I : Interpretation α) (lt : α → α → Prop) :
    DupOrientedOn D I lt ↔
      ∀ b s n : α, D b → D s → D n → lt (I.wrap s (I.recur b s n)) (I.recur b s (I.succ n)) := by
  constructor
  · intro h b s n hb hs hn
    have hρ : ∀ i, D (![b, s, n] i) := by
      intro i
      fin_cases i
      · exact hb
      · exact hs
      · exact hn
    simpa [dupLhs, dupRhs] using h ![b, s, n] hρ
  · intro h ρ hρ
    simpa [dupLhs, dupRhs] using h (ρ 0) (ρ 1) (ρ 2) (hρ 0) (hρ 1) (hρ 2)

/-- Orientation over the whole carrier, stated pointwise. -/
theorem dupOriented_iff {α : Type} (I : Interpretation α) (lt : α → α → Prop) :
    DupOriented I lt ↔ ∀ b s n : α, lt (I.wrap s (I.recur b s n)) (I.recur b s (I.succ n)) := by
  rw [DupOriented, dupOrientedOn_iff]
  simp

/-- The termination statement a monotone-algebra soundness theorem yields on the free two-rule
system: the interpretation decreases along every contextual step under every valuation, and the
contextual relation is well founded over every variable type. -/
def CertifiesFreeTermination {α : Type} (I : Interpretation α) (lt : α → α → Prop) : Prop :=
  (∀ (ν : Type) (ρ : ν → α) (t u : FreeTerm ν), ContextStep t u → lt (I.eval ρ u) (I.eval ρ t)) ∧
    ∀ ν : Type, WellFounded (fun u t : FreeTerm ν => ContextStep t u)

/-- Soundness of the monotone-algebra method, consumed from P3.4: a well-founded strict relation,
strict monotonicity in every constructor argument and orientation of both root rules certify
termination of the free contextual relation. -/
theorem certifiesFreeTermination_of_laws {α : Type} (I : Interpretation α) (lt : α → α → Prop)
    (hwf : WellFounded lt) (hlaws : StrictContextLaws I lt) (hroot : RootRuleOrients I lt) :
    CertifiesFreeTermination I lt :=
  ⟨fun _ ρ _ _ h => interpretation_context_consumption I lt hlaws hroot ρ h,
    fun _ => interpretation_context_reverse_wellFounded I lt hlaws hroot hwf (fun _ => I.zero)⟩

/-! ## Bridges to P3 -/

/-- The carrier of an interpretation as a step-duplicating schema, so that the P3 theorems, which
are stated for every schema, apply to the interpretation's own values. -/
def valueSchema {α : Type} (I : Interpretation α) : StepDuplicatingSchema where
  T := α
  base := I.zero
  succ := I.succ
  wrap := I.wrap
  recur := I.recur

/-- P3.2 on an interpretation: a natural coordinate that every strict comparison decreases, placed
in the barrier cell at one base and counter value, excludes orientation of the rule. -/
theorem not_dupOriented_of_barrierCell {α : Type} (I : Interpretation α) (lt : α → α → Prop)
    (M : α → ℕ) (hM : ∀ {x y : α}, lt x y → M x < M y) (b n : α)
    (hw : WrapUnboundedAt (S := valueSchema I) M b n)
    (hg : GainBoundedAt (S := valueSchema I) M b n) :
    ¬ DupOriented I lt := by
  intro h
  exact barrier_cell_excludes_orientation (S := valueSchema I) M b n hw hg
    (fun s => hM ((dupOriented_iff I lt).1 h b s n))

/-- P3.2 over a preordered additive carrier and a domain of payloads. With `β = ℕ` and the full
domain the two hypotheses are exactly `WrapUnboundedAt` and `GainBoundedAt`
(`orderedCell_nat_iff`). -/
theorem ordered_barrier_cell_on {α β : Type} [Preorder β] [Add β] (I : Interpretation α)
    (D : α → Prop) (M : α → β) (b n : α)
    (hw : ∀ K : β, ∃ s : α, D s ∧ M (I.recur b s n) + K < M (I.wrap s (I.recur b s n)))
    (hg : ∃ K : β, ∀ s : α, D s → M (I.recur b s (I.succ n)) ≤ M (I.recur b s n) + K) :
    ¬ ∀ s : α, D s → M (I.wrap s (I.recur b s n)) < M (I.recur b s (I.succ n)) := by
  intro h
  obtain ⟨K, hK⟩ := hg
  obtain ⟨s, hs, hlt⟩ := hw K
  exact lt_irrefl _ (lt_of_lt_of_le (lt_trans hlt (h s hs)) (hK s hs))

/-- On natural numbers with the full domain, the hypotheses of `ordered_barrier_cell_on` are the
P3.2 cell predicates. -/
theorem orderedCell_nat_iff (I : Interpretation ℕ) (b n : ℕ) :
    ((∀ K : ℕ, ∃ s : ℕ, True ∧ I.recur b s n + K < I.wrap s (I.recur b s n)) ↔
        WrapUnboundedAt (S := valueSchema I) id b n) ∧
      ((∃ K : ℕ, ∀ s : ℕ, True → I.recur b s (I.succ n) ≤ I.recur b s n + K) ↔
        GainBoundedAt (S := valueSchema I) id b n) := by
  simp [WrapUnboundedAt, GainBoundedAt, valueSchema]

/-! ## Arbitrary signatures -/

/-- The free duplicating rule's left side over an arbitrary first-order signature. -/
def sigDupLhs {ι : Type} {arity : ι → ℕ} : SigTerm ι arity (Fin 3) :=
  .recur (.var 0) (.var 1) (.succ (.var 2))

/-- The free duplicating rule's right side over an arbitrary first-order signature. -/
def sigDupRhs {ι : Type} {arity : ι → ℕ} : SigTerm ι arity (Fin 3) :=
  .wrap (.var 1) (.recur (.var 0) (.var 1) (.var 2))

/-- The two sides are the signature root step `SigRootStep.recurSucc`. -/
theorem sigDup_rootStep {ι : Type} {arity : ι → ℕ} :
    SigRootStep (sigDupLhs (ι := ι) (arity := arity)) sigDupRhs :=
  SigRootStep.recurSucc _ _ _

/-- Over any signature, orienting the duplicating rule depends only on the four schema symbols:
no inert symbol occurs in the rule. -/
theorem sig_dupOrientedOn_iff {ι : Type} {arity : ι → ℕ} {α : Type} (D : α → Prop)
    (J : SigInterpretation ι arity α) (lt : α → α → Prop) :
    (∀ ρ : Fin 3 → α, (∀ i, D (ρ i)) → lt (J.eval ρ sigDupRhs) (J.eval ρ sigDupLhs)) ↔
      DupOrientedOn D J.toInterpretation lt := by
  simp only [DupOrientedOn, dupLhs, dupRhs, sigDupLhs, sigDupRhs, SigInterpretation.eval,
    Interpretation.eval]

/-- A natural-valued interpretation extended to an arbitrary signature by `1 + sum` on every inert
symbol. -/
def natSigExtension {ι : Type} (arity : ι → ℕ) (I : Interpretation ℕ) :
    SigInterpretation ι arity ℕ :=
  { toInterpretation := I, inertOp := fun _ args => (∑ i, args i) + 1 }

/-- The `1 + sum` extension keeps the strict monotone laws. -/
theorem natSigExtension_strict {ι : Type} (arity : ι → ℕ) (I : Interpretation ℕ)
    (h : StrictContextLaws I (fun x y : ℕ => x < y)) :
    SigStrictContextLaws (natSigExtension arity I) (fun x y : ℕ => x < y) where
  toStrictContextLaws := h
  inertArg := by
    intro f args i x y hxy
    show (∑ j, Function.update args i x j) + 1 < (∑ j, Function.update args i y j) + 1
    rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sum_update_of_mem (Finset.mem_univ i)]
    omega

/-- Over any first-order signature, a natural-valued member that satisfies the strict monotone
laws and orients both root rules proves termination of the full contextual relation. -/
theorem nat_signature_termination {ι : Type} (arity : ι → ℕ) (ν : Type) (I : Interpretation ℕ)
    (hlaws : StrictContextLaws I (fun x y : ℕ => x < y))
    (hroot : RootRuleOrients I (fun x y : ℕ => x < y)) :
    WellFounded (fun u t : SigTerm ι arity ν => SigContextStep t u) :=
  sig_contextStep_reverse_wellFounded (I := natSigExtension arity I) hroot
    (natSigExtension_strict arity I hlaws) Nat.lt_wfRel.wf (fun _ => 0)

/-! ## Linear polynomial interpretations over the rationals and the reals -/

/-- Coefficients of a linear polynomial interpretation of the four schema symbols, with the
separation `δ` of the strict order: `zero ↦ z`, `succ n ↦ c0 + c1 n`,
`wrap s y ↦ w0 + ws s + wy y`, `recur b s n ↦ r0 + rb b + rs s + rn n`. -/
structure LinearPolyData (K : Type) where
  δ : K
  z : K
  c0 : K
  c1 : K
  w0 : K
  ws : K
  wy : K
  r0 : K
  rb : K
  rs : K
  rn : K

/-- The linear interpretation of a coefficient table. -/
def LinearPolyData.interp {K : Type} [Add K] [Mul K] (M : LinearPolyData K) :
    Interpretation K where
  zero := M.z
  succ n := M.c0 + M.c1 * n
  wrap s y := M.w0 + M.ws * s + M.wy * y
  recur b s n := M.r0 + M.rb * b + M.rs * s + M.rn * n

/-- Lucas's separated order `x >_δ y ⟺ x - y ≥ δ`, stated with the smaller value first. -/
def sepLt {K : Type} [Add K] [LE K] (δ : K) (x y : K) : Prop := x + δ ≤ y

/-- Admissibility of a linear interpretation over the carrier `[0, ∞)`: a positive separation,
nonnegative constants (so the algebra maps the carrier into itself), and every variable
coefficient at least one (monotonicity for `>_δ`). -/
structure LinearPolyLaws {K : Type} [Zero K] [One K] [LT K] [LE K] (M : LinearPolyData K) :
    Prop where
  delta_pos : 0 < M.δ
  z_nonneg : 0 ≤ M.z
  c0_nonneg : 0 ≤ M.c0
  w0_nonneg : 0 ≤ M.w0
  r0_nonneg : 0 ≤ M.r0
  succ_mono : 1 ≤ M.c1
  wrap_left_mono : 1 ≤ M.ws
  wrap_right_mono : 1 ≤ M.wy
  recur_base_mono : 1 ≤ M.rb
  recur_step_mono : 1 ≤ M.rs
  recur_counter_mono : 1 ≤ M.rn

/-- The separated order is well founded on the nonnegative rationals. -/
theorem sepLt_wf_rat (δ : ℚ) (hδ : 0 < δ) :
    WellFounded (fun x y : {q : ℚ // 0 ≤ q} => sepLt δ x.1 y.1) := by
  refine Subrelation.wf (r := InvImage (· < ·) (fun x : {q : ℚ // 0 ≤ q} => ⌊x.1 / δ⌋₊)) ?_
    (InvImage.wf _ Nat.lt_wfRel.wf)
  intro x y hxy
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hx : 0 ≤ x.1 / δ := div_nonneg x.2 hδ.le
  have h1 : x.1 / δ + 1 ≤ y.1 / δ := by
    have e : x.1 / δ + 1 = (x.1 + δ) / δ := by field_simp
    rw [e]
    unfold sepLt at hxy
    gcongr
  have h2 := Nat.floor_mono h1
  rw [Nat.floor_add_one hx] at h2
  show ⌊x.1 / δ⌋₊ < ⌊y.1 / δ⌋₊
  omega

/-- The separated order is well founded on the nonnegative reals. -/
theorem sepLt_wf_real (δ : ℝ) (hδ : 0 < δ) :
    WellFounded (fun x y : {r : ℝ // 0 ≤ r} => sepLt δ x.1 y.1) := by
  refine Subrelation.wf (r := InvImage (· < ·) (fun x : {r : ℝ // 0 ≤ r} => ⌊x.1 / δ⌋₊)) ?_
    (InvImage.wf _ Nat.lt_wfRel.wf)
  intro x y hxy
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hx : 0 ≤ x.1 / δ := div_nonneg x.2 hδ.le
  have h1 : x.1 / δ + 1 ≤ y.1 / δ := by
    have e : x.1 / δ + 1 = (x.1 + δ) / δ := by field_simp
    rw [e]
    unfold sepLt at hxy
    gcongr
  have h2 := Nat.floor_mono h1
  rw [Nat.floor_add_one hx] at h2
  show ⌊x.1 / δ⌋₊ < ⌊y.1 / δ⌋₊
  omega

/-- Without separation the strict order on the nonnegative rationals has arbitrarily small drops
`1 > 1/2 > 1/3 > ⋯` and is not well founded. -/
theorem rat_lt_not_wf : ¬ WellFounded (fun x y : {q : ℚ // 0 ≤ q} => x.1 < y.1) := by
  intro h
  obtain ⟨a, ⟨k, rfl⟩, hmin⟩ := h.has_min (Set.range fun k : ℕ =>
    (⟨1 / ((k : ℚ) + 1), by positivity⟩ : {q : ℚ // 0 ≤ q})) ⟨_, ⟨0, rfl⟩⟩
  apply hmin ⟨1 / ((k : ℚ) + 1 + 1), by positivity⟩ ⟨k + 1, by ext; push_cast; ring⟩
  exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

/-- Without separation the strict order on the nonnegative reals is not well founded. -/
theorem real_lt_not_wf : ¬ WellFounded (fun x y : {r : ℝ // 0 ≤ r} => x.1 < y.1) := by
  intro h
  obtain ⟨a, ⟨k, rfl⟩, hmin⟩ := h.has_min (Set.range fun k : ℕ =>
    (⟨1 / ((k : ℝ) + 1), by positivity⟩ : {r : ℝ // 0 ≤ r})) ⟨_, ⟨0, rfl⟩⟩
  apply hmin ⟨1 / ((k : ℝ) + 1 + 1), by positivity⟩ ⟨k + 1, by ext; push_cast; ring⟩
  exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

/-! ### linearPolyQ -/

/-- Native data of `linearPolyQ`: a rational linear coefficient table with its separation. -/
abbrev linearPolyQData : Type := LinearPolyData ℚ

/-- Laws of `linearPolyQ`, pinned to S. Lucas, *Polynomials over the reals in proofs of
termination: from theory to practice*, RAIRO Theoretical Informatics and Applications
39(3):547–586, 2005, Section 3: the order `x >_δ y ⟺ x − y ≥ δ` with `δ > 0` (Theorem 1:
well founded on every `m`-bounded algebra over `A ⊆ ℝ`), here with `A = ℚ ∩ [0, ∞)`, and the
monotonicity criterion that every partial derivative is at least one. -/
def linearPolyQLaws (M : linearPolyQData) : Prop := LinearPolyLaws M

/-- The method accepts the free duplicating rule when every assignment of nonnegative rationals
gives `value(rhs) + δ ≤ value(lhs)`. -/
def linearPolyQAccepts (M : linearPolyQData) : Prop :=
  DupOrientedOn (fun x : ℚ => 0 ≤ x) M.interp (sepLt M.δ)

/-- Verdict: barrier. -/
def linearPolyQResult (M : linearPolyQData) : Prop := ¬ linearPolyQAccepts M

/-- Every lawful rational linear interpretation lies in the P3.2 barrier cell at `b = n = 0`: the
counter gain is the constant `rn * c0`, and the wrapper keeps the payload with coefficient at least
one. Consumed laws: `delta_pos`, the nonnegative constants, `wrap_left_mono`, `wrap_right_mono`
and `recur_step_mono`. -/
theorem linearPolyQ_universal :
    ∀ M : linearPolyQData, linearPolyQLaws M → linearPolyQResult M := by
  intro M hM hacc
  unfold linearPolyQLaws at hM
  have hor := (dupOrientedOn_iff _ _ _).1 hacc
  refine ordered_barrier_cell_on M.interp (fun x : ℚ => 0 ≤ x) id 0 0 ?_ ?_ ?_
  · intro K
    refine ⟨|K| + 1, by positivity, ?_⟩
    have hs : (0 : ℚ) ≤ |K| + 1 := by positivity
    have hrs : (0 : ℚ) ≤ M.rs * (|K| + 1) :=
      mul_nonneg (le_trans zero_le_one hM.recur_step_mono) hs
    have hy : (0 : ℚ) ≤ M.r0 + M.rb * 0 + M.rs * (|K| + 1) + M.rn * 0 := by
      have := hM.r0_nonneg
      linarith
    have h1 : |K| + 1 ≤ M.ws * (|K| + 1) := le_mul_of_one_le_left hs hM.wrap_left_mono
    have h2 := le_mul_of_one_le_left hy hM.wrap_right_mono
    have h3 := le_abs_self K
    have h4 := hM.w0_nonneg
    simp only [LinearPolyData.interp, id]
    linarith
  · refine ⟨M.rn * M.c0, fun s _ => ?_⟩
    simp only [LinearPolyData.interp, id]
    exact le_of_eq (by ring)
  · intro s hs
    have h := hor 0 s 0 le_rfl hs le_rfl
    unfold sepLt at h
    have := hM.delta_pos
    simp only [id]
    linarith

/-- Witness: `δ = 1/2`, `succ n = 1 + n`, `wrap s y = 3/2 s + y`,
`recur b s n = 2 + b + s + 3/2 n`. -/
def linearPolyQWitness : linearPolyQData where
  δ := 1 / 2
  z := 0
  c0 := 1
  c1 := 1
  w0 := 0
  ws := 3 / 2
  wy := 1
  r0 := 2
  rb := 1
  rs := 1
  rn := 3 / 2

theorem linearPolyQWitness_laws : linearPolyQLaws linearPolyQWitness := by
  unfold linearPolyQLaws
  constructor <;> norm_num [linearPolyQWitness]

theorem linearPolyQWitness_result : linearPolyQResult linearPolyQWitness :=
  linearPolyQ_universal _ linearPolyQWitness_laws

/-- Controls. Fractional coefficients: the witness's wrapper coefficient `3/2` is not a natural
number. Separated strictness: `>_δ` at the witness's `δ` is well founded on `ℚ ∩ [0, ∞)`, while the
unseparated strict order is not. Erased arguments: `linearPolyQ_mutation`. -/
theorem linearPolyQWitness_feature :
    (¬ ∃ k : ℕ, (k : ℚ) = linearPolyQWitness.ws) ∧
      WellFounded (fun x y : {q : ℚ // 0 ≤ q} => sepLt linearPolyQWitness.δ x.1 y.1) ∧
      ¬ WellFounded (fun x y : {q : ℚ // 0 ≤ q} => x.1 < y.1) := by
  refine ⟨?_, sepLt_wf_rat _ (by norm_num [linearPolyQWitness]), rat_lt_not_wf⟩
  rintro ⟨k, hk⟩
  have hk' : (k : ℚ) = 3 / 2 := by simpa [linearPolyQWitness] using hk
  have h2 : ((2 * k : ℕ) : ℚ) = 3 := by push_cast; linarith
  have h3 : 2 * k = 3 := by exact_mod_cast h2
  omega

/-- Erased argument: giving the witness's wrapper payload coefficient the value `0` violates the
monotonicity law, and the resulting interpretation accepts the rule; the law is load-bearing. -/
theorem linearPolyQ_mutation :
    ¬ linearPolyQLaws { linearPolyQWitness with ws := 0 } ∧
      linearPolyQAccepts { linearPolyQWitness with ws := 0 } := by
  constructor
  · intro h
    unfold linearPolyQLaws at h
    have := h.wrap_left_mono
    norm_num at this
  · rw [linearPolyQAccepts, dupOrientedOn_iff]
    intro b s n _ _ _
    simp only [LinearPolyData.interp, linearPolyQWitness, sepLt]
    linarith

/-- Over any signature, extending a lawful rational linear interpretation by arbitrary inert
operations does not orient the signature's duplicating rule. -/
theorem linearPolyQ_signature (ι : Type) (arity : ι → ℕ) (M : linearPolyQData)
    (ops : (f : ι) → (Fin (arity f) → ℚ) → ℚ) (hM : linearPolyQLaws M) :
    ¬ ∀ ρ : Fin 3 → ℚ, (∀ i, 0 ≤ ρ i) →
      sepLt M.δ (({ toInterpretation := M.interp, inertOp := ops } :
          SigInterpretation ι arity ℚ).eval ρ sigDupRhs)
        (({ toInterpretation := M.interp, inertOp := ops } :
          SigInterpretation ι arity ℚ).eval ρ sigDupLhs) :=
  fun h => linearPolyQ_universal M hM
    ((sig_dupOrientedOn_iff (fun x : ℚ => 0 ≤ x) _ (sepLt M.δ)).1 h)

/-! ### linearPolyR -/

/-- Native data of `linearPolyR`: a real linear coefficient table with its separation. -/
abbrev linearPolyRData : Type := LinearPolyData ℝ

/-- Laws of `linearPolyR`, pinned to S. Lucas, RAIRO Theoretical Informatics and Applications
39(3):547–586, 2005, Section 3: `x >_δ y ⟺ x − y ≥ δ` with `δ > 0` (Theorem 1), carrier
`A = [0, ∞) ⊆ ℝ`, partial derivatives at least one. The remark after Theorem 1 shows that `δ = 0`
loses well-foundedness. -/
def linearPolyRLaws (M : linearPolyRData) : Prop := LinearPolyLaws M

/-- Acceptance over all assignments of nonnegative reals. -/
def linearPolyRAccepts (M : linearPolyRData) : Prop :=
  DupOrientedOn (fun x : ℝ => 0 ≤ x) M.interp (sepLt M.δ)

/-- Verdict: barrier. -/
def linearPolyRResult (M : linearPolyRData) : Prop := ¬ linearPolyRAccepts M

/-- Every lawful real linear interpretation lies in the P3.2 barrier cell at `b = n = 0`. -/
theorem linearPolyR_universal :
    ∀ M : linearPolyRData, linearPolyRLaws M → linearPolyRResult M := by
  intro M hM hacc
  unfold linearPolyRLaws at hM
  have hor := (dupOrientedOn_iff _ _ _).1 hacc
  refine ordered_barrier_cell_on M.interp (fun x : ℝ => 0 ≤ x) id 0 0 ?_ ?_ ?_
  · intro K
    refine ⟨|K| + 1, by positivity, ?_⟩
    have hs : (0 : ℝ) ≤ |K| + 1 := by positivity
    have hrs : (0 : ℝ) ≤ M.rs * (|K| + 1) :=
      mul_nonneg (le_trans zero_le_one hM.recur_step_mono) hs
    have hy : (0 : ℝ) ≤ M.r0 + M.rb * 0 + M.rs * (|K| + 1) + M.rn * 0 := by
      have := hM.r0_nonneg
      linarith
    have h1 : |K| + 1 ≤ M.ws * (|K| + 1) := le_mul_of_one_le_left hs hM.wrap_left_mono
    have h2 := le_mul_of_one_le_left hy hM.wrap_right_mono
    have h3 := le_abs_self K
    have h4 := hM.w0_nonneg
    simp only [LinearPolyData.interp, id]
    linarith
  · refine ⟨M.rn * M.c0, fun s _ => ?_⟩
    simp only [LinearPolyData.interp, id]
    exact le_of_eq (by ring)
  · intro s hs
    have h := hor 0 s 0 le_rfl hs le_rfl
    unfold sepLt at h
    have := hM.delta_pos
    simp only [id]
    linarith

/-- Witness: `δ = 1/2`, `succ n = 1 + n`, `wrap s y = s + y`, `recur b s n = b + 4 s + n`. -/
noncomputable def linearPolyRWitness : linearPolyRData where
  δ := 1 / 2
  z := 0
  c0 := 1
  c1 := 1
  w0 := 0
  ws := 1
  wy := 1
  r0 := 0
  rb := 1
  rs := 4
  rn := 1

theorem linearPolyRWitness_laws : linearPolyRLaws linearPolyRWitness := by
  unfold linearPolyRLaws
  constructor <;> norm_num [linearPolyRWitness]

theorem linearPolyRWitness_result : linearPolyRResult linearPolyRWitness :=
  linearPolyR_universal _ linearPolyRWitness_laws

/-- Controls. Arbitrarily small drops: the unseparated strict order on `[0, ∞)` is not well
founded, while `>_δ` at the witness's `δ` is. Unattained values: acceptance quantifies over every
real, yet the witness already fails at the ground instance `b = zero`, `s = succ zero`,
`n = zero`, whose values are attained by closed terms. -/
theorem linearPolyRWitness_feature :
    ¬ WellFounded (fun x y : {r : ℝ // 0 ≤ r} => x.1 < y.1) ∧
      WellFounded (fun x y : {r : ℝ // 0 ≤ r} => sepLt linearPolyRWitness.δ x.1 y.1) ∧
      ¬ sepLt linearPolyRWitness.δ
          (linearPolyRWitness.interp.eval (Empty.elim : Empty → ℝ)
            (.wrap (.succ .zero) (.recur .zero (.succ .zero) .zero)))
          (linearPolyRWitness.interp.eval (Empty.elim : Empty → ℝ)
            (.recur .zero (.succ .zero) (.succ .zero))) := by
  refine ⟨real_lt_not_wf, sepLt_wf_real _ (by norm_num [linearPolyRWitness]), ?_⟩
  simp only [sepLt, Interpretation.eval, LinearPolyData.interp, linearPolyRWitness]
  norm_num

/-- Fractional coefficient below one: giving the witness's wrapper coefficient of the recursive
result the value `1/2` violates the partial-derivative law, and the resulting interpretation
accepts the rule. -/
theorem linearPolyR_mutation :
    ¬ linearPolyRLaws { linearPolyRWitness with wy := 1 / 2 } ∧
      linearPolyRAccepts { linearPolyRWitness with wy := 1 / 2 } := by
  constructor
  · intro h
    unfold linearPolyRLaws at h
    have := h.wrap_right_mono
    norm_num at this
  · rw [linearPolyRAccepts, dupOrientedOn_iff]
    intro b s n hb hs hn
    simp only [LinearPolyData.interp, linearPolyRWitness, sepLt]
    linarith

/-- Over any signature, extending a lawful real linear interpretation by arbitrary inert
operations does not orient the signature's duplicating rule. -/
theorem linearPolyR_signature (ι : Type) (arity : ι → ℕ) (M : linearPolyRData)
    (ops : (f : ι) → (Fin (arity f) → ℝ) → ℝ) (hM : linearPolyRLaws M) :
    ¬ ∀ ρ : Fin 3 → ℝ, (∀ i, 0 ≤ ρ i) →
      sepLt M.δ (({ toInterpretation := M.interp, inertOp := ops } :
          SigInterpretation ι arity ℝ).eval ρ sigDupRhs)
        (({ toInterpretation := M.interp, inertOp := ops } :
          SigInterpretation ι arity ℝ).eval ρ sigDupLhs) :=
  fun h => linearPolyR_universal M hM
    ((sig_dupOrientedOn_iff (fun x : ℝ => 0 ≤ x) _ (sepLt M.δ)).1 h)

/-! ## Common facts for natural-valued escape members -/

/-- A strictly increasing function on `ℕ` gains at least one per step. -/
theorem nat_strict_ge {f : ℕ → ℕ} (hf : ∀ x y : ℕ, x < y → f x < f y) (x : ℕ) :
    f 0 + x ≤ f x := by
  induction x with
  | zero => simp
  | succ k ih =>
      have := hf k (k + 1) (Nat.lt_succ_self k)
      omega

/-- A wrapper that is strictly monotone in both arguments keeps both, `s + y ≤ wrap s y`. -/
theorem wrap_ge_of_strict {I : Interpretation ℕ}
    (h : StrictContextLaws I (fun x y : ℕ => x < y)) (s y : ℕ) : s + y ≤ I.wrap s y := by
  have h1 : I.wrap 0 y + s ≤ I.wrap s y :=
    nat_strict_ge (f := fun x => I.wrap x y) (fun a b hab => h.wrapLeft y hab) s
  have h2 : I.wrap 0 0 + y ≤ I.wrap 0 y :=
    nat_strict_ge (f := fun x => I.wrap 0 x) (fun a b hab => h.wrapRight 0 hab) y
  omega

/-- P3.1 on an accepted natural-valued member: a wrapper that keeps both arguments at cost `c_w`
forces the counter gain above the payload value plus `c_w` at every instance. -/
theorem nat_escape_coupling (I : Interpretation ℕ) (c_w : ℕ)
    (hret : ∀ x y : ℕ, c_w + x + y ≤ I.wrap x y)
    (hroot : RootRuleOrients I (fun x y : ℕ => x < y)) (b s n : ℕ) :
    ((s : ℕ) : ℤ) + (c_w : ℤ) < counterGainZ (S := valueSchema I) id b s n :=
  retained_wrapper_forces_payload_coupled_gain (S := valueSchema I) id c_w hret
    (fun b s n => hroot.recurSucc b s n) b s n

/-! ## Polynomial interpretations with negative coefficients -/

/-- Polynomial expressions with integer coefficients in `k` variables. -/
inductive ZPoly (k : ℕ) where
  | const (c : ℤ)
  | var (i : Fin k)
  | add (p q : ZPoly k)
  | mul (p q : ZPoly k)

/-- Integer value of a polynomial expression. -/
def ZPoly.eval {k : ℕ} (x : Fin k → ℤ) : ZPoly k → ℤ
  | .const c => c
  | .var i => x i
  | .add p q => ZPoly.eval x p + ZPoly.eval x q
  | .mul p q => ZPoly.eval x p * ZPoly.eval x q

/-- Weak monotonicity over the integers in every argument, for the componentwise order. -/
def ZPoly.WeakMono {k : ℕ} (p : ZPoly k) : Prop :=
  ∀ x y : Fin k → ℤ, (∀ j, x j ≤ y j) → p.eval x ≤ p.eval y

/-- Integer polynomials for the four schema symbols. -/
structure NegCoeffData where
  zero : ℤ
  succ : ZPoly 1
  wrap : ZPoly 2
  recur : ZPoly 3

/-- The induced algebra over `ℕ`: every symbol is interpreted by `max {0, f_ℤ}`, which is
`Int.toNat` of the integer value. -/
def NegCoeffData.interp (M : NegCoeffData) : Interpretation ℕ where
  zero := M.zero.toNat
  succ n := (M.succ.eval ![(n : ℤ)]).toNat
  wrap s y := (M.wrap.eval ![(s : ℤ), (y : ℤ)]).toNat
  recur b s n := (M.recur.eval ![(b : ℤ), (s : ℤ), (n : ℤ)]).toNat

/-- Admissibility: weakly monotone integer interpretations, and a strictly monotone induced
natural algebra, which the direct termination method requires. -/
structure NegCoeffLaws (M : NegCoeffData) : Prop where
  succ_weak : M.succ.WeakMono
  wrap_weak : M.wrap.WeakMono
  recur_weak : M.recur.WeakMono
  strict : StrictContextLaws M.interp (fun x y : ℕ => x < y)

/-- Native data of `negativeCoefficientPolynomial`: integer polynomials for the four symbols. -/
abbrev negativeCoefficientPolynomialData : Type := NegCoeffData

/-- Laws of `negativeCoefficientPolynomial`, pinned to N. Hirokawa and A. Middeldorp,
*Polynomial interpretations with negative coefficients*, AISC 2004, LNAI 3249, pp. 185–198,
Definition 3 (the induced algebra `f_ℕ = max {0, f_ℤ}` of an integer algebra whose interpretations
are weakly monotone in all arguments) with Lemma 4 (it yields a reduction pair); their Section 4
shows that a negative variable coefficient such as `x − y` breaks weak monotonicity. For direct
termination the induced algebra must be strictly monotone (J. Endrullis, J. Waldmann, H. Zantema,
J. Automated Reasoning 40:195–220, 2008, Definition 1 and Theorem 3 part 1). The degree is not
restricted. -/
def negativeCoefficientPolynomialLaws (M : negativeCoefficientPolynomialData) : Prop :=
  NegCoeffLaws M

/-- Acceptance: the induced algebra orients both free root rules. -/
def negativeCoefficientPolynomialAccepts (M : negativeCoefficientPolynomialData) : Prop :=
  RootRuleOrients M.interp (fun x y : ℕ => x < y)

/-- Verdict: escape. -/
def negativeCoefficientPolynomialResult (M : negativeCoefficientPolynomialData) : Prop :=
  negativeCoefficientPolynomialAccepts M ∧
    CertifiesFreeTermination M.interp (fun x y : ℕ => x < y)

/-- Soundness: a lawful accepting member certifies termination of the free system. -/
theorem negativeCoefficientPolynomial_sound (M : negativeCoefficientPolynomialData)
    (hM : negativeCoefficientPolynomialLaws M) (hA : negativeCoefficientPolynomialAccepts M) :
    CertifiesFreeTermination M.interp (fun x y : ℕ => x < y) :=
  certifiesFreeTermination_of_laws M.interp _ Nat.lt_wfRel.wf
    (show NegCoeffLaws M from hM).strict hA

/-- `X = b + s + n + 1` as an integer expression in the three recursor arguments. -/
def negCubeBase : ZPoly 3 := .add (.add (.add (.var 0) (.var 1)) (.var 2)) (.const 1)

/-- Cubes are monotone on the integers. -/
theorem int_cube_mono {A B : ℤ} (h : A ≤ B) : A * A * A ≤ B * B * B := by
  nlinarith [mul_nonneg (sub_nonneg.2 h)
    (add_nonneg (add_nonneg (sq_nonneg (A + B)) (sq_nonneg A)) (sq_nonneg B))]

/-- Cubes are strictly monotone from one upward. -/
theorem int_cube_strict {A B : ℤ} (hA : 1 ≤ A) (h : A < B) : A * A * A < B * B * B := by
  have hq : 0 < A * A + A * B + B * B := by nlinarith
  nlinarith [mul_pos (sub_pos.2 h) hq]

/-- The truncated shifted cube is strictly monotone from one upward. -/
theorem cube_toNat_strict {A B : ℤ} (hA : 1 ≤ A) (h : A < B) :
    (A * A * A + -2).toNat < (B * B * B + -2).toNat := by
  have h1 := int_cube_strict hA h
  have hB : 2 ≤ B := by omega
  have hBB : 4 ≤ B * B := by nlinarith
  have h2 : 8 ≤ B * B * B := by nlinarith
  omega

/-- Witness: `zero ↦ 1`, `succ n ↦ n + 1`, `wrap s y ↦ s + y + 1`,
`recur b s n ↦ max {0, (b + s + n + 1)³ − 2}`; the negative constant is truncated at the origin. -/
def negativeCoefficientPolynomialWitness : negativeCoefficientPolynomialData where
  zero := 1
  succ := .add (.var 0) (.const 1)
  wrap := .add (.add (.var 0) (.var 1)) (.const 1)
  recur := .add (.mul (.mul negCubeBase negCubeBase) negCubeBase) (.const (-2))

theorem negW_zero : negativeCoefficientPolynomialWitness.interp.zero = 1 := rfl

theorem negW_succ (n : ℕ) : negativeCoefficientPolynomialWitness.interp.succ n = n + 1 := by
  show ((n : ℤ) + 1).toNat = n + 1
  omega

theorem negW_wrap (s y : ℕ) :
    negativeCoefficientPolynomialWitness.interp.wrap s y = s + y + 1 := by
  show ((s : ℤ) + (y : ℤ) + 1).toNat = s + y + 1
  omega

theorem negW_recur (b s n : ℕ) : negativeCoefficientPolynomialWitness.interp.recur b s n =
    (((b : ℤ) + s + n + 1) * ((b : ℤ) + s + n + 1) * ((b : ℤ) + s + n + 1) + -2).toNat :=
  rfl

theorem negW_strict :
    StrictContextLaws negativeCoefficientPolynomialWitness.interp (fun x y : ℕ => x < y) where
  succ := by
    intro x y h
    show negativeCoefficientPolynomialWitness.interp.succ x <
      negativeCoefficientPolynomialWitness.interp.succ y
    rw [negW_succ, negW_succ]
    omega
  wrapLeft := by
    intro x y z h
    show negativeCoefficientPolynomialWitness.interp.wrap x z <
      negativeCoefficientPolynomialWitness.interp.wrap y z
    rw [negW_wrap, negW_wrap]
    omega
  wrapRight := by
    intro z x y h
    show negativeCoefficientPolynomialWitness.interp.wrap z x <
      negativeCoefficientPolynomialWitness.interp.wrap z y
    rw [negW_wrap, negW_wrap]
    omega
  recurBase := by
    intro x y s n h
    show negativeCoefficientPolynomialWitness.interp.recur x s n <
      negativeCoefficientPolynomialWitness.interp.recur y s n
    rw [negW_recur, negW_recur]
    exact cube_toNat_strict (by omega) (by omega)
  recurStep := by
    intro b x y n h
    show negativeCoefficientPolynomialWitness.interp.recur b x n <
      negativeCoefficientPolynomialWitness.interp.recur b y n
    rw [negW_recur, negW_recur]
    exact cube_toNat_strict (by omega) (by omega)
  recurCounter := by
    intro b s x y h
    show negativeCoefficientPolynomialWitness.interp.recur b s x <
      negativeCoefficientPolynomialWitness.interp.recur b s y
    rw [negW_recur, negW_recur]
    exact cube_toNat_strict (by omega) (by omega)

theorem negativeCoefficientPolynomialWitness_laws :
    negativeCoefficientPolynomialLaws negativeCoefficientPolynomialWitness := by
  unfold negativeCoefficientPolynomialLaws
  refine ⟨?_, ?_, ?_, negW_strict⟩
  · intro x y h
    show x 0 + 1 ≤ y 0 + 1
    linarith [h 0]
  · intro x y h
    show x 0 + x 1 + 1 ≤ y 0 + y 1 + 1
    linarith [h 0, h 1]
  · intro x y h
    show (x 0 + x 1 + x 2 + 1) * (x 0 + x 1 + x 2 + 1) * (x 0 + x 1 + x 2 + 1) + -2 ≤
      (y 0 + y 1 + y 2 + 1) * (y 0 + y 1 + y 2 + 1) * (y 0 + y 1 + y 2 + 1) + -2
    have := int_cube_mono
      (show x 0 + x 1 + x 2 + 1 ≤ y 0 + y 1 + y 2 + 1 by linarith [h 0, h 1, h 2])
    linarith

/-- The successor instance of the witness in integer form. -/
theorem negW_step_key (b s n : ℕ) :
    s + (((b : ℤ) + s + n + 1) * ((b : ℤ) + s + n + 1) * ((b : ℤ) + s + n + 1) + -2).toNat
        + 1 <
      (((b : ℤ) + s + ((n + 1 : ℕ) : ℤ) + 1) * ((b : ℤ) + s + ((n + 1 : ℕ) : ℤ) + 1) *
        ((b : ℤ) + s + ((n + 1 : ℕ) : ℤ) + 1) + -2).toNat := by
  have e : ((b : ℤ) + s + ((n + 1 : ℕ) : ℤ) + 1) = ((b : ℤ) + s + n + 1) + 1 := by
    push_cast
    ring
  rw [e]
  generalize hX : (b : ℤ) + s + n + 1 = X
  have hX1 : 1 ≤ X := by omega
  have hsX : (s : ℤ) + 1 ≤ X := by omega
  have e2 : (X + 1) * (X + 1) * (X + 1) = X * X * X + 3 * (X * X) + 3 * X + 1 := by ring
  rw [e2]
  have hXX : X ≤ X * X := by nlinarith
  have hc : 1 ≤ X * X * X := by nlinarith
  omega

theorem negW_root :
    RootRuleOrients negativeCoefficientPolynomialWitness.interp (fun x y : ℕ => x < y) where
  recurZero := by
    intro b s
    show b < negativeCoefficientPolynomialWitness.interp.recur b s
      negativeCoefficientPolynomialWitness.interp.zero
    rw [negW_zero, negW_recur]
    have hX : (2 : ℤ) ≤ (b : ℤ) + s + ((1 : ℕ) : ℤ) + 1 := by push_cast; omega
    have hc : 4 * ((b : ℤ) + s + ((1 : ℕ) : ℤ) + 1) ≤
        ((b : ℤ) + s + ((1 : ℕ) : ℤ) + 1) * ((b : ℤ) + s + ((1 : ℕ) : ℤ) + 1) *
          ((b : ℤ) + s + ((1 : ℕ) : ℤ) + 1) := by nlinarith
    omega
  recurSucc := by
    intro b s n
    show negativeCoefficientPolynomialWitness.interp.wrap s
        (negativeCoefficientPolynomialWitness.interp.recur b s n) <
      negativeCoefficientPolynomialWitness.interp.recur b s
        (negativeCoefficientPolynomialWitness.interp.succ n)
    rw [negW_succ, negW_wrap, negW_recur, negW_recur]
    exact negW_step_key b s n

theorem negativeCoefficientPolynomialWitness_result :
    negativeCoefficientPolynomialResult negativeCoefficientPolynomialWitness :=
  ⟨negW_root, negativeCoefficientPolynomial_sound _ negativeCoefficientPolynomialWitness_laws
    negW_root⟩

/-- Controls. Negative variable coefficient versus only a negative constant: the polynomial
`x − y` is not weakly monotone (Hirokawa and Middeldorp 2004, Section 4); `x − 1` is weakly
monotone but its truncation is not strictly monotone; the truncation of `2x − 1` is strictly
monotone. Truncation boundary: the witness's recursor polynomial is `−1` at the origin, its
truncation is `0`, and strict monotonicity holds across that boundary. -/
theorem negativeCoefficientPolynomialWitness_feature :
    ¬ (ZPoly.add (.var 0) (.mul (.const (-1)) (.var 1)) : ZPoly 2).WeakMono ∧
      (ZPoly.add (.var 0) (.const (-1)) : ZPoly 1).WeakMono ∧
      ¬ StrictMono (fun x : ℕ => ((x : ℤ) + -1).toNat) ∧
      StrictMono (fun x : ℕ => (2 * (x : ℤ) + -1).toNat) ∧
      negativeCoefficientPolynomialWitness.recur.eval ![0, 0, 0] = -1 ∧
      negativeCoefficientPolynomialWitness.interp.recur 0 0 0 = 0 ∧
      negativeCoefficientPolynomialWitness.interp.recur 0 0 0 <
        negativeCoefficientPolynomialWitness.interp.recur 1 0 0 := by
  refine ⟨?_, ?_, ?_, ?_, by decide, by decide, by decide⟩
  · intro h
    have := h ![0, 0] ![0, 1] (by intro j; fin_cases j <;> decide)
    revert this
    decide
  · intro x y h
    show x 0 + -1 ≤ y 0 + -1
    linarith [h 0]
  · intro h
    have := h (show (0 : ℕ) < 1 by decide)
    revert this
    decide
  · intro a b hab
    show (2 * (a : ℤ) + -1).toNat < (2 * (b : ℤ) + -1).toNat
    omega

/-- P3.1 on the accepted witness: its wrapper keeps both arguments at cost one, so the counter gain
exceeds the payload value plus one at every instance. -/
theorem negativeCoefficientPolynomialWitness_coupling (b s n : ℕ) :
    ((s : ℕ) : ℤ) + ((1 : ℕ) : ℤ) <
      counterGainZ (S := valueSchema negativeCoefficientPolynomialWitness.interp) id b s n :=
  nat_escape_coupling _ 1 (fun x y => by rw [negW_wrap]; omega) negW_root b s n

/-- Truncation beyond the permitted bound: replacing the witness's recursor constant `−2` by `−9`
makes the truncation active at the first two values, and strict monotonicity fails. -/
theorem negativeCoefficientPolynomial_mutation :
    ¬ negativeCoefficientPolynomialLaws { negativeCoefficientPolynomialWitness with
        recur := .add (.mul (.mul negCubeBase negCubeBase) negCubeBase) (.const (-9)) } := by
  intro h
  unfold negativeCoefficientPolynomialLaws at h
  have := h.strict.recurBase 0 0 (show (0 : ℕ) < 1 by decide)
  revert this
  decide

/-- Over any signature, a lawful accepting member extended by `1 + sum` proves termination of the
full contextual relation. -/
theorem negativeCoefficientPolynomial_signature (ι : Type) (arity : ι → ℕ) (ν : Type)
    (M : negativeCoefficientPolynomialData) (hM : negativeCoefficientPolynomialLaws M)
    (hA : negativeCoefficientPolynomialAccepts M) :
    WellFounded (fun u t : SigTerm ι arity ν => SigContextStep t u) :=
  nat_signature_termination arity ν M.interp (show NegCoeffLaws M from hM).strict hA

/-! ## Max-polynomial interpretations -/

/-- Max-polynomial expressions over `ℕ` without subtraction, in variables `V`. -/
inductive MExpr (V : Type) where
  | const (c : ℕ)
  | var (v : V)
  | add (p q : MExpr V)
  | mul (p q : MExpr V)
  | maxE (p q : MExpr V)

/-- Value of a max-polynomial. -/
def MExpr.eval {V : Type} (x : V → ℕ) : MExpr V → ℕ
  | .const c => c
  | .var v => x v
  | .add p q => MExpr.eval x p + MExpr.eval x q
  | .mul p q => MExpr.eval x p * MExpr.eval x q
  | .maxE p q => max (MExpr.eval x p) (MExpr.eval x q)

/-- The max-plus fragment: no multiplication. -/
def MExpr.MulFree {V : Type} : MExpr V → Prop
  | .const _ => True
  | .var _ => True
  | .add p q => MExpr.MulFree p ∧ MExpr.MulFree q
  | .mul _ _ => False
  | .maxE p q => MExpr.MulFree p ∧ MExpr.MulFree q

/-- Number of variable occurrences. -/
def MExpr.size {V : Type} : MExpr V → ℕ
  | .const _ => 0
  | .var _ => 1
  | .add p q => MExpr.size p + MExpr.size q
  | .mul p q => MExpr.size p + MExpr.size q
  | .maxE p q => MExpr.size p + MExpr.size q

/-- Max-plus expressions are Lipschitz: moving every variable up by at most `d` raises the value by
at most `size * d`. -/
theorem MExpr.eval_le_of_mulFree {V : Type} (p : MExpr V) (hp : p.MulFree) (x y : V → ℕ)
    (d : ℕ) (h : ∀ v, y v ≤ x v + d) : p.eval y ≤ p.eval x + p.size * d := by
  induction p with
  | const c => simp [MExpr.eval, MExpr.size]
  | var v => simpa [MExpr.eval, MExpr.size] using h v
  | add p q ihp ihq =>
      simp only [MExpr.MulFree] at hp
      have h1 := ihp hp.1
      have h2 := ihq hp.2
      simp only [MExpr.eval, MExpr.size, add_mul]
      omega
  | mul p q _ _ =>
      simp only [MExpr.MulFree] at hp
  | maxE p q ihp ihq =>
      simp only [MExpr.MulFree] at hp
      have h1 := ihp hp.1
      have h2 := ihq hp.2
      simp only [MExpr.eval, MExpr.size, add_mul]
      omega

/-- Max-polynomials for the four schema symbols. -/
structure MaxPolyData where
  zero : ℕ
  succ : MExpr (Fin 1)
  wrap : MExpr (Fin 2)
  recur : MExpr (Fin 3)

/-- The natural interpretation of a max-polynomial table. -/
def MaxPolyData.interp (M : MaxPolyData) : Interpretation ℕ where
  zero := M.zero
  succ n := M.succ.eval ![n]
  wrap s y := M.wrap.eval ![s, y]
  recur b s n := M.recur.eval ![b, s, n]

/-- Native data of `maxPolynomial`: a max-polynomial for each symbol. -/
abbrev maxPolynomialData : Type := MaxPolyData

/-- Laws of `maxPolynomial`, pinned to C. Fuhs, J. Giesl, A. Middeldorp, P. Schneider-Kamp,
R. Thiemann, H. Zankl, *Maximal termination*, RTA 2008, LNCS 5117, pp. 110–125, Definition 13
(max-polynomials: closed under `+`, `∗`, `max`; interpretations over `ℕ` without subtraction); for
direct termination every interpretation is strictly monotone in every argument (Endrullis,
Waldmann, Zantema 2008, Theorem 3 part 1). -/
def maxPolynomialLaws (M : maxPolynomialData) : Prop :=
  StrictContextLaws M.interp (fun x y : ℕ => x < y)

/-- Acceptance: both free root rules are oriented. -/
def maxPolynomialAccepts (M : maxPolynomialData) : Prop :=
  RootRuleOrients M.interp (fun x y : ℕ => x < y)

/-- Verdict: escape. -/
def maxPolynomialResult (M : maxPolynomialData) : Prop :=
  maxPolynomialAccepts M ∧ CertifiesFreeTermination M.interp (fun x y : ℕ => x < y)

theorem maxPolynomial_sound (M : maxPolynomialData) (hM : maxPolynomialLaws M)
    (hA : maxPolynomialAccepts M) : CertifiesFreeTermination M.interp (fun x y : ℕ => x < y) :=
  certifiesFreeTermination_of_laws M.interp _ Nat.lt_wfRel.wf hM hA

/-- The max-plus subclass is blocked: a recursor without multiplication has counter gain at most
`size * succ 0` at `b = n = 0`, the strictly monotone wrapper keeps the payload, and the P3.2
barrier cell excludes orientation of the duplicating rule. -/
theorem maxPolynomial_maxPlus_barrier (M : maxPolynomialData) (hM : maxPolynomialLaws M)
    (hfree : M.recur.MulFree) : ¬ DupOriented M.interp (fun x y : ℕ => x < y) := by
  refine not_dupOriented_of_barrierCell M.interp (fun x y : ℕ => x < y) id (fun h => h) 0 0
    ?_ ?_
  · intro K
    refine ⟨K + 1, ?_⟩
    have := wrap_ge_of_strict hM (K + 1) (M.interp.recur 0 (K + 1) 0)
    show M.interp.recur 0 (K + 1) 0 + K < M.interp.wrap (K + 1) (M.interp.recur 0 (K + 1) 0)
    omega
  · refine ⟨M.recur.size * M.interp.succ 0, fun s => ?_⟩
    show M.recur.eval ![0, s, M.interp.succ 0] ≤
      M.recur.eval ![0, s, 0] + M.recur.size * M.interp.succ 0
    exact MExpr.eval_le_of_mulFree M.recur hfree _ _ _ (fun v => by fin_cases v <;> simp)

/-- Witness: `succ n ↦ n + 1`, `wrap s y ↦ y + s + max s 1`,
`recur b s n ↦ (n + 1)(s + s + b + 2)`. -/
def maxPolynomialWitness : maxPolynomialData where
  zero := 0
  succ := .add (.var 0) (.const 1)
  wrap := .add (.add (.var 1) (.var 0)) (.maxE (.var 0) (.const 1))
  recur := .mul (.add (.var 2) (.const 1))
    (.add (.add (.add (.var 1) (.var 1)) (.var 0)) (.const 2))

theorem maxPolynomialWitness_laws : maxPolynomialLaws maxPolynomialWitness := by
  unfold maxPolynomialLaws
  constructor
  · intro x y h
    show x + 1 < y + 1
    omega
  · intro x y z h
    show z + x + max x 1 < z + y + max y 1
    omega
  · intro z x y h
    show x + z + max z 1 < y + z + max z 1
    omega
  · intro x y s n h
    show (n + 1) * (s + s + x + 2) < (n + 1) * (s + s + y + 2)
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  · intro b x y n h
    show (n + 1) * (x + x + b + 2) < (n + 1) * (y + y + b + 2)
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  · intro b s x y h
    show (x + 1) * (s + s + b + 2) < (y + 1) * (s + s + b + 2)
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)

theorem maxPolynomialWitness_root :
    RootRuleOrients maxPolynomialWitness.interp (fun x y : ℕ => x < y) where
  recurZero := by
    intro b s
    show b < (0 + 1) * (s + s + b + 2)
    omega
  recurSucc := by
    intro b s n
    show (n + 1) * (s + s + b + 2) + s + max s 1 < (n + 1 + 1) * (s + s + b + 2)
    have hm : max s 1 ≤ s + 1 := max_le (by omega) (by omega)
    nlinarith

theorem maxPolynomialWitness_result : maxPolynomialResult maxPolynomialWitness :=
  ⟨maxPolynomialWitness_root,
    maxPolynomial_sound _ maxPolynomialWitness_laws maxPolynomialWitness_root⟩

/-- Controls. Offset and tie: the wrapper's `max s 1` takes the offset branch at `s = 0` and ties at
`s = 1`. Masking: for `s ≥ 1` the offset is masked and the wrapper is `y + 2 s`. Coupled escape:
the counter gain is `2 s + b + 2`, unbounded in the payload, and the recursor uses a product, so
the member lies outside the max-plus subclass of `maxPolynomial_maxPlus_barrier`. -/
theorem maxPolynomialWitness_feature :
    (∀ y, maxPolynomialWitness.interp.wrap 0 y = y + 1) ∧
      maxPolynomialWitness.interp.wrap 1 0 = 2 ∧
      (∀ s y, 1 ≤ s → maxPolynomialWitness.interp.wrap s y = y + 2 * s) ∧
      (∀ b s n, maxPolynomialWitness.interp.recur b s (maxPolynomialWitness.interp.succ n) =
        maxPolynomialWitness.interp.recur b s n + (2 * s + b + 2)) ∧
      ¬ maxPolynomialWitness.recur.MulFree := by
  refine ⟨fun y => ?_, by decide, fun s y hs => ?_, fun b s n => ?_, ?_⟩
  · show y + 0 + max 0 1 = y + 1
    omega
  · show y + s + max s 1 = y + 2 * s
    omega
  · show (n + 1 + 1) * (s + s + b + 2) = (n + 1) * (s + s + b + 2) + (2 * s + b + 2)
    ring
  · simp [maxPolynomialWitness, MExpr.MulFree]

/-- P3.1 on the accepted witness: the wrapper keeps both arguments at cost one. -/
theorem maxPolynomialWitness_coupling (b s n : ℕ) :
    ((s : ℕ) : ℤ) + ((1 : ℕ) : ℤ) <
      counterGainZ (S := valueSchema maxPolynomialWitness.interp) id b s n :=
  nat_escape_coupling _ 1 (fun x y => by
    show 1 + x + y ≤ y + x + max x 1
    omega) maxPolynomialWitness_root b s n

/-- The witness with its product recursor replaced by the sum `n + 1 + (s + s + b + 2)`. -/
def maxPolynomialMutant : maxPolynomialData :=
  { maxPolynomialWitness with
    recur := .add (.add (.var 2) (.const 1))
      (.add (.add (.add (.var 1) (.var 1)) (.var 0)) (.const 2)) }

/-- Removing the product: the mutant still satisfies the laws, lies in the max-plus subclass, and
does not accept the rule. -/
theorem maxPolynomial_mutation :
    maxPolynomialLaws maxPolynomialMutant ∧ ¬ maxPolynomialAccepts maxPolynomialMutant := by
  have hlaws : maxPolynomialLaws maxPolynomialMutant := by
    unfold maxPolynomialLaws
    constructor
    · intro x y h
      show x + 1 < y + 1
      omega
    · intro x y z h
      show z + x + max x 1 < z + y + max y 1
      omega
    · intro z x y h
      show x + z + max z 1 < y + z + max z 1
      omega
    · intro x y s n h
      show n + 1 + (s + s + x + 2) < n + 1 + (s + s + y + 2)
      omega
    · intro b x y n h
      show n + 1 + (x + x + b + 2) < n + 1 + (y + y + b + 2)
      omega
    · intro b s x y h
      show x + 1 + (s + s + b + 2) < y + 1 + (s + s + b + 2)
      omega
  refine ⟨hlaws, fun hA => ?_⟩
  apply maxPolynomial_maxPlus_barrier _ hlaws (by simp [maxPolynomialMutant, MExpr.MulFree])
  exact (dupOriented_iff _ _).2
    (fun b s n => (show RootRuleOrients _ _ from hA).recurSucc b s n)

theorem maxPolynomial_signature (ι : Type) (arity : ι → ℕ) (ν : Type) (M : maxPolynomialData)
    (hM : maxPolynomialLaws M) (hA : maxPolynomialAccepts M) :
    WellFounded (fun u t : SigTerm ι arity ν => SigContextStep t u) :=
  nat_signature_termination arity ν M.interp hM hA

/-! ## Natural polynomial interpretations: higher degree and multilinear tables -/

/-- Monomial tables over `ℕ` for the four symbols, in the representation of P3.5. -/
structure NatPolyData where
  z : ℕ
  succ : List UMono
  wrap : List WMono
  recur : List RMono

/-- The natural interpretation of the tables. -/
def NatPolyData.interp (M : NatPolyData) : Interpretation ℕ where
  zero := M.z
  succ n := uEval M.succ n
  wrap s y := wEval M.wrap s y
  recur b s n := rEval M.recur b s n

/-- The unit successor `n ↦ n + a` as a monomial table. -/
def unitSucc (a : ℕ) : List UMono := [⟨1, 1⟩, ⟨a, 0⟩]

theorem uEval_unitSucc (a n : ℕ) : uEval (unitSucc a) n = n + a := by
  simp [unitSucc, uEval]

/-- P3.5 decides every member whose successor table is a unit successor. -/
theorem natPoly_rootRuleOrients_iff_decide (M : NatPolyData) (a : ℕ) (h : M.succ = unitSucc a) :
    RootRuleOrients M.interp (fun x y : ℕ => x < y) ↔
      decideRootUnit M.z a M.wrap M.recur = true := by
  rw [decideRootUnit_iff]
  have hs : ∀ n, M.interp.succ n = (polyInterpretation M.z 1 a M.wrap M.recur).succ n := by
    intro n
    show uEval M.succ n = 1 * n + a
    rw [h, uEval_unitSucc]
    ring
  constructor
  · intro hr
    exact ⟨fun b s => hr.recurZero b s, fun b s n => by rw [← hs]; exact hr.recurSucc b s n⟩
  · intro hr
    exact ⟨fun b s => hr.recurZero b s, fun b s n => by rw [hs]; exact hr.recurSucc b s n⟩

/-- Strict monotone laws of the tables `unitSucc a`, `regionW = s + y + 1` and
`residualR = (b + s + 2)(n + 1)²`. -/
theorem residual_strict (a : ℕ) :
    StrictContextLaws
      ({ z := 0, succ := unitSucc a, wrap := regionW, recur := residualR } : NatPolyData).interp
      (fun x y : ℕ => x < y) where
  succ := by
    intro x y h
    show uEval (unitSucc a) x < uEval (unitSucc a) y
    rw [uEval_unitSucc, uEval_unitSucc]
    omega
  wrapLeft := by
    intro x y z h
    show wEval regionW x z < wEval regionW y z
    rw [wEval_regionW, wEval_regionW]
    show x + z + 1 < y + z + 1
    omega
  wrapRight := by
    intro z x y h
    show wEval regionW z x < wEval regionW z y
    rw [wEval_regionW, wEval_regionW]
    show z + x + 1 < z + y + 1
    omega
  recurBase := by
    intro x y s n h
    show rEval residualR x s n < rEval residualR y s n
    rw [rEval_residualR, rEval_residualR]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
  recurStep := by
    intro b x y n h
    show rEval residualR b x n < rEval residualR b y n
    rw [rEval_residualR, rEval_residualR]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
  recurCounter := by
    intro b s x y h
    show rEval residualR b s x < rEval residualR b s y
    rw [rEval_residualR, rEval_residualR]
    have h2 : (x + 1) ^ 2 < (y + 1) ^ 2 := by nlinarith
    exact Nat.mul_lt_mul_of_pos_left h2 (by omega)

/-! ### nonlinearHigherDegreePolynomial -/

/-- Native data of `nonlinearHigherDegreePolynomial`: monomial tables of arbitrary degree. -/
abbrev nonlinearHigherDegreePolynomialData : Type := NatPolyData

/-- Laws of `nonlinearHigherDegreePolynomial`: polynomial interpretations over `ℕ` of arbitrary
degree, as used in J. Endrullis, J. Waldmann, H. Zantema, *Matrix interpretations for proving
termination of term rewriting*, J. Automated Reasoning 40(2–3):195–220, 2008, Section 3 after
Theorem 3 ("A consists of the natural numbers ... all functions [f] are polynomials ... for part 1
strict monotonicity is required"): every interpretation is strictly monotone in every argument. -/
def nonlinearHigherDegreePolynomialLaws (M : nonlinearHigherDegreePolynomialData) : Prop :=
  StrictContextLaws M.interp (fun x y : ℕ => x < y)

/-- Acceptance: both free root rules are oriented. -/
def nonlinearHigherDegreePolynomialAccepts (M : nonlinearHigherDegreePolynomialData) : Prop :=
  RootRuleOrients M.interp (fun x y : ℕ => x < y)

/-- Verdict: escape. -/
def nonlinearHigherDegreePolynomialResult (M : nonlinearHigherDegreePolynomialData) : Prop :=
  nonlinearHigherDegreePolynomialAccepts M ∧
    CertifiesFreeTermination M.interp (fun x y : ℕ => x < y)

theorem nonlinearHigherDegreePolynomial_sound (M : nonlinearHigherDegreePolynomialData)
    (hM : nonlinearHigherDegreePolynomialLaws M) (hA : nonlinearHigherDegreePolynomialAccepts M) :
    CertifiesFreeTermination M.interp (fun x y : ℕ => x < y) :=
  certifiesFreeTermination_of_laws M.interp _ Nat.lt_wfRel.wf hM hA

/-- P3.5 decides every member with a unit successor. -/
theorem nonlinearHigherDegreePolynomial_decides (M : nonlinearHigherDegreePolynomialData) (a : ℕ)
    (h : M.succ = unitSucc a) :
    nonlinearHigherDegreePolynomialAccepts M ↔ decideRootUnit M.z a M.wrap M.recur = true :=
  natPoly_rootRuleOrients_iff_decide M a h

/-- Witness: `succ n ↦ n + 1`, `wrap s y ↦ s + y + 1`, `recur b s n ↦ (b + s + 2)(n + 1)²`, of
total degree three. -/
def nonlinearHigherDegreePolynomialWitness : nonlinearHigherDegreePolynomialData where
  z := 0
  succ := unitSucc 1
  wrap := regionW
  recur := residualR

theorem nonlinearHigherDegreePolynomialWitness_laws :
    nonlinearHigherDegreePolynomialLaws nonlinearHigherDegreePolynomialWitness :=
  residual_strict 1

theorem nonlinearHigherDegreePolynomialWitness_root :
    nonlinearHigherDegreePolynomialAccepts nonlinearHigherDegreePolynomialWitness :=
  (nonlinearHigherDegreePolynomial_decides _ 1 rfl).2 (by decide)

theorem nonlinearHigherDegreePolynomialWitness_result :
    nonlinearHigherDegreePolynomialResult nonlinearHigherDegreePolynomialWitness :=
  ⟨nonlinearHigherDegreePolynomialWitness_root,
    nonlinearHigherDegreePolynomial_sound _ nonlinearHigherDegreePolynomialWitness_laws
      nonlinearHigherDegreePolynomialWitness_root⟩

/-- A nonzero nonlinear recursor table without step-counter coupling: `s² + s + b + n + 2`. -/
def uncoupledR : List RMono :=
  [⟨1, 0, 2, 0⟩, ⟨1, 0, 1, 0⟩, ⟨1, 1, 0, 0⟩, ⟨1, 0, 0, 1⟩, ⟨2, 0, 0, 0⟩]

/-- Controls. The witness's table contains the monomial `s n²` of degree three; a nonzero
nonlinear table without coupling is decided and rejected by P3.5; the empty table is not an
admissible member. -/
theorem nonlinearHigherDegreePolynomialWitness_feature :
    (∃ m ∈ residualR, 0 < m.coeff ∧ 3 ≤ m.bDeg + m.sDeg + m.nDeg) ∧
      decideRootUnit 0 1 regionW uncoupledR = false ∧
      ¬ RootRuleOrients (polyInterpretation 0 1 1 regionW uncoupledR) (fun x y : ℕ => x < y) ∧
      ¬ nonlinearHigherDegreePolynomialLaws
        { nonlinearHigherDegreePolynomialWitness with recur := [] } := by
  refine ⟨⟨⟨1, 0, 1, 2⟩, by simp [residualR], by norm_num, by norm_num⟩, by decide,
    fun h => absurd ((decideRootUnit_iff 0 1 regionW uncoupledR).2 h) (by decide),
    fun h => ?_⟩
  unfold nonlinearHigherDegreePolynomialLaws at h
  have := h.recurBase 0 0 (show (0 : ℕ) < 1 by decide)
  exact absurd this (by decide)

/-- P3.1 on the accepted witness: the wrapper keeps both arguments at cost one. -/
theorem nonlinearHigherDegreePolynomialWitness_coupling (b s n : ℕ) :
    ((s : ℕ) : ℤ) + ((1 : ℕ) : ℤ) <
      counterGainZ (S := valueSchema nonlinearHigherDegreePolynomialWitness.interp) id b s n :=
  nat_escape_coupling _ 1 (fun x y => by
    show 1 + x + y ≤ wEval regionW x y
    rw [wEval_regionW]
    show 1 + x + y ≤ x + y + 1
    omega) nonlinearHigherDegreePolynomialWitness_root b s n

/-- Unit offset removed: with `succ n ↦ n` the tables still satisfy the laws, and P3.5 rejects the
member. -/
theorem nonlinearHigherDegreePolynomial_mutation :
    nonlinearHigherDegreePolynomialLaws
        { nonlinearHigherDegreePolynomialWitness with succ := unitSucc 0 } ∧
      ¬ nonlinearHigherDegreePolynomialAccepts
        { nonlinearHigherDegreePolynomialWitness with succ := unitSucc 0 } :=
  ⟨residual_strict 0, fun hA =>
    absurd ((nonlinearHigherDegreePolynomial_decides _ 0 rfl).1 hA) (by decide)⟩

theorem nonlinearHigherDegreePolynomial_signature (ι : Type) (arity : ι → ℕ) (ν : Type)
    (M : nonlinearHigherDegreePolynomialData) (hM : nonlinearHigherDegreePolynomialLaws M)
    (hA : nonlinearHigherDegreePolynomialAccepts M) :
    WellFounded (fun u t : SigTerm ι arity ν => SigContextStep t u) :=
  nat_signature_termination arity ν M.interp hM hA

/-! ### multilinearInterpretation -/

/-- Native data of `multilinearInterpretation`: monomial tables. -/
abbrev multilinearInterpretationData : Type := NatPolyData

/-- Admissibility of a multilinear member: strict monotonicity and every variable of degree at most
one in every monomial. -/
structure MultilinearLaws (M : NatPolyData) : Prop where
  strict : StrictContextLaws M.interp (fun x y : ℕ => x < y)
  succ_multilinear : ∀ m ∈ M.succ, m.deg ≤ 1
  wrap_multilinear : ∀ m ∈ M.wrap, m.sDeg ≤ 1 ∧ m.yDeg ≤ 1
  recur_multilinear : ∀ m ∈ M.recur, m.bDeg ≤ 1 ∧ m.sDeg ≤ 1 ∧ m.nDeg ≤ 1

/-- Laws of `multilinearInterpretation`: the natural polynomial method of Endrullis, Waldmann and
Zantema 2008, Theorem 3 part 1 (strict monotonicity), restricted to multilinear monomials, in which
every variable has degree at most one. -/
def multilinearInterpretationLaws (M : multilinearInterpretationData) : Prop := MultilinearLaws M

/-- Acceptance: both free root rules are oriented. -/
def multilinearInterpretationAccepts (M : multilinearInterpretationData) : Prop :=
  RootRuleOrients M.interp (fun x y : ℕ => x < y)

/-- Verdict: escape. -/
def multilinearInterpretationResult (M : multilinearInterpretationData) : Prop :=
  multilinearInterpretationAccepts M ∧ CertifiesFreeTermination M.interp (fun x y : ℕ => x < y)

theorem multilinearInterpretation_sound (M : multilinearInterpretationData)
    (hM : multilinearInterpretationLaws M) (hA : multilinearInterpretationAccepts M) :
    CertifiesFreeTermination M.interp (fun x y : ℕ => x < y) :=
  certifiesFreeTermination_of_laws M.interp _ Nat.lt_wfRel.wf
    (show MultilinearLaws M from hM).strict hA

/-- P3.5 decides every member with a unit successor. -/
theorem multilinearInterpretation_decides (M : multilinearInterpretationData) (a : ℕ)
    (h : M.succ = unitSucc a) :
    multilinearInterpretationAccepts M ↔ decideRootUnit M.z a M.wrap M.recur = true :=
  natPoly_rootRuleOrients_iff_decide M a h

theorem mlW_recur (b s n : ℕ) :
    rEval (multilinearR 2 1 1 2 0 1 1 0) b s n = (n + 1) * (b + s + 2) := by
  simp [multilinearR, rEval]
  ring

/-- Witness: `succ n ↦ n + 1`, `wrap s y ↦ 1 + s + y`, and the multilinear recursor
`2 + b + s + 2n + b n + s n = (n + 1)(b + s + 2)` with step-counter coefficient one. -/
def multilinearInterpretationWitness : multilinearInterpretationData where
  z := 0
  succ := unitSucc 1
  wrap := affineW 1 1 1
  recur := multilinearR 2 1 1 2 0 1 1 0

theorem multilinearInterpretationWitness_laws :
    multilinearInterpretationLaws multilinearInterpretationWitness := by
  unfold multilinearInterpretationLaws
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by decide, by decide, by decide⟩
  · intro x y h
    show uEval (unitSucc 1) x < uEval (unitSucc 1) y
    rw [uEval_unitSucc, uEval_unitSucc]
    omega
  · intro x y z h
    show wEval (affineW 1 1 1) x z < wEval (affineW 1 1 1) y z
    rw [wEval_affineW, wEval_affineW]
    omega
  · intro z x y h
    show wEval (affineW 1 1 1) z x < wEval (affineW 1 1 1) z y
    rw [wEval_affineW, wEval_affineW]
    omega
  · intro x y s n h
    show rEval (multilinearR 2 1 1 2 0 1 1 0) x s n < rEval (multilinearR 2 1 1 2 0 1 1 0) y s n
    rw [mlW_recur, mlW_recur]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  · intro b x y n h
    show rEval (multilinearR 2 1 1 2 0 1 1 0) b x n < rEval (multilinearR 2 1 1 2 0 1 1 0) b y n
    rw [mlW_recur, mlW_recur]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  · intro b s x y h
    show rEval (multilinearR 2 1 1 2 0 1 1 0) b s x < rEval (multilinearR 2 1 1 2 0 1 1 0) b s y
    rw [mlW_recur, mlW_recur]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)

theorem multilinearInterpretationWitness_root :
    multilinearInterpretationAccepts multilinearInterpretationWitness :=
  (multilinearInterpretation_decides _ 1 rfl).2 (by decide)

theorem multilinearInterpretationWitness_result :
    multilinearInterpretationResult multilinearInterpretationWitness :=
  ⟨multilinearInterpretationWitness_root,
    multilinearInterpretation_sound _ multilinearInterpretationWitness_laws
      multilinearInterpretationWitness_root⟩

/-- Controls. The exact P3.5 classification of affine wrappers over multilinear recursors with a
unit successor; with a wrapper that keeps its payload (`βw ≥ 1`) and its recursive result
(`γ = 1`), orientation needs a positive step-counter coefficient `rsn`; a nonzero uncoupled member
is rejected and the step-counter coupled witness is accepted. -/
theorem multilinearInterpretationWitness_feature :
    (∀ α βw γ r0 rb rs rn rbs rbn rsn rbsn a : ℕ,
      decideSuccUnit (affineW α βw γ) (multilinearR r0 rb rs rn rbs rbn rsn rbsn) a = true ↔
        (γ = 0 ∧ α < r0 + rn * a ∧ βw ≤ rs + rsn * a) ∨ (γ = 1 ∧ α < rn * a ∧ βw ≤ rsn * a)) ∧
      (∀ α βw r0 rb rs rn rbs rbn rbsn a : ℕ, 1 ≤ βw →
        decideSuccUnit (affineW α βw 1) (multilinearR r0 rb rs rn rbs rbn 0 rbsn) a = false) ∧
      decideRootUnit 0 1 (affineW 1 1 1) (multilinearR 2 1 1 2 0 1 0 0) = false ∧
      decideRootUnit 0 1 (affineW 1 1 1) (multilinearR 2 1 1 2 0 1 1 0) = true := by
  refine ⟨multilinear_affine_classification, ?_, by decide, by decide⟩
  intro α βw r0 rb rs rn rbs rbn rbsn a hβ
  cases hd : decideSuccUnit (affineW α βw 1) (multilinearR r0 rb rs rn rbs rbn 0 rbsn) a with
  | false => rfl
  | true =>
      exfalso
      have := (multilinear_affine_classification α βw 1 r0 rb rs rn rbs rbn 0 rbsn a).1 hd
      omega

/-- P3.1 on the accepted witness: the wrapper keeps both arguments at cost one. -/
theorem multilinearInterpretationWitness_coupling (b s n : ℕ) :
    ((s : ℕ) : ℤ) + ((1 : ℕ) : ℤ) <
      counterGainZ (S := valueSchema multilinearInterpretationWitness.interp) id b s n :=
  nat_escape_coupling _ 1 (fun x y => by
    show 1 + x + y ≤ wEval (affineW 1 1 1) x y
    rw [wEval_affineW]
    omega) multilinearInterpretationWitness_root b s n

/-- Step-counter coupling removed: with `rsn = 0` P3.5 rejects the member. -/
theorem multilinearInterpretation_mutation :
    ¬ multilinearInterpretationAccepts
      { multilinearInterpretationWitness with recur := multilinearR 2 1 1 2 0 1 0 0 } :=
  fun hA => absurd ((multilinearInterpretation_decides _ 1 rfl).1 hA) (by decide)

theorem multilinearInterpretation_signature (ι : Type) (arity : ι → ℕ) (ν : Type)
    (M : multilinearInterpretationData) (hM : multilinearInterpretationLaws M)
    (hA : multilinearInterpretationAccepts M) :
    WellFounded (fun u t : SigTerm ι arity ν => SigContextStep t u) :=
  nat_signature_termination arity ν M.interp (show MultilinearLaws M from hM).strict hA

/-! ## Matrix interpretations over the naturals -/

/-- Vectors of dimension `d + 1`; coordinate `0` is the tracked coordinate. -/
abbrev NVec (d : ℕ) : Type := Fin (d + 1) → ℕ

/-- Square matrices of dimension `d + 1`. -/
abbrev NMat (d : ℕ) : Type := Fin (d + 1) → Fin (d + 1) → ℕ

/-- Matrix-vector product over `ℕ`. -/
def nAct {d : ℕ} (A : NMat d) (v : NVec d) : NVec d := fun i => ∑ j, A i j * v j

theorem nAct_zero {d : ℕ} (A : NMat d) : nAct A 0 = 0 := by
  funext i
  simp [nAct]

theorem nAct_zero_mat {d : ℕ} (v : NVec d) : nAct (0 : NMat d) v = 0 := by
  funext i
  simp [nAct]

/-- The tracked coordinate of a product is at least its diagonal term. -/
theorem nAct_ge_diag {d : ℕ} (A : NMat d) (v : NVec d) : A 0 0 * v 0 ≤ nAct A v 0 :=
  Finset.single_le_sum (f := fun j => A 0 j * v j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ 0)

/-- The vector `c e₀`. -/
def nUnit {d : ℕ} (c : ℕ) : NVec d := fun i => if i = 0 then c else 0

theorem nUnit_zero {d : ℕ} (c : ℕ) : (nUnit c : NVec d) 0 = c := if_pos rfl

/-- A natural matrix interpretation: one matrix per argument position and one vector per symbol. -/
structure NatMatrixData where
  d : ℕ
  zeroVec : NVec d
  succMat : NMat d
  succVec : NVec d
  wrapLeft : NMat d
  wrapRight : NMat d
  wrapVec : NVec d
  recurBase : NMat d
  recurStep : NMat d
  recurCounter : NMat d
  recurVec : NVec d

/-- `[f](v₁, …, vₙ) = F₁ v₁ + ⋯ + Fₙ vₙ + f`. -/
def NatMatrixData.interp (M : NatMatrixData) : Interpretation (NVec M.d) where
  zero := M.zeroVec
  succ n := nAct M.succMat n + M.succVec
  wrap s y := nAct M.wrapLeft s + nAct M.wrapRight y + M.wrapVec
  recur b s n := nAct M.recurBase b + nAct M.recurStep s + nAct M.recurCounter n + M.recurVec

/-- The strict order of Endrullis, Waldmann and Zantema, smaller side first: `x < y` iff
`x₀ < y₀` and `xᵢ ≤ yᵢ` at every coordinate. -/
def vecLt {d : ℕ} (x y : NVec d) : Prop := x 0 < y 0 ∧ ∀ i, x i ≤ y i

/-- Monotonicity condition: the upper-left entry of every argument matrix is positive. -/
structure NatMatrixLaws (M : NatMatrixData) : Prop where
  succ_pos : 1 ≤ M.succMat 0 0
  wrapLeft_pos : 1 ≤ M.wrapLeft 0 0
  wrapRight_pos : 1 ≤ M.wrapRight 0 0
  recurBase_pos : 1 ≤ M.recurBase 0 0
  recurStep_pos : 1 ≤ M.recurStep 0 0
  recurCounter_pos : 1 ≤ M.recurCounter 0 0

/-- The P3.2 cell at the tracked coordinate: at `b = n = 0` the counter gain is the constant
`(R_n · succ 0)₀`, and the wrapper keeps both arguments because its diagonal entries are positive.
Consumed laws: `wrapLeft_pos` and `wrapRight_pos`. -/
theorem natMatrix_barrier (M : NatMatrixData) (hM : NatMatrixLaws M) :
    ¬ DupOriented M.interp vecLt := by
  refine not_dupOriented_of_barrierCell M.interp vecLt (fun v => v 0) (fun h => h.1) 0 0
    ?_ ?_
  · intro K
    refine ⟨nUnit (K + 1), ?_⟩
    have h1 := nAct_ge_diag M.wrapLeft (nUnit (K + 1))
    have h2 := nAct_ge_diag M.wrapRight (M.interp.recur 0 (nUnit (K + 1)) 0)
    have h3 := Nat.le_mul_of_pos_left ((nUnit (K + 1) : NVec M.d) 0) hM.wrapLeft_pos
    have h4 := Nat.le_mul_of_pos_left (M.interp.recur 0 (nUnit (K + 1)) 0 0) hM.wrapRight_pos
    rw [nUnit_zero] at h1 h3
    show M.interp.recur 0 (nUnit (K + 1)) 0 0 + K <
      nAct M.wrapLeft (nUnit (K + 1)) 0 + nAct M.wrapRight (M.interp.recur 0 (nUnit (K + 1)) 0) 0 +
        M.wrapVec 0
    omega
  · refine ⟨nAct M.recurCounter (M.interp.succ 0) 0, fun s => ?_⟩
    show (nAct M.recurBase 0 + nAct M.recurStep s + nAct M.recurCounter (M.interp.succ 0) +
        M.recurVec) 0 ≤
      (nAct M.recurBase 0 + nAct M.recurStep s + nAct M.recurCounter 0 + M.recurVec) 0 +
        nAct M.recurCounter (M.interp.succ 0) 0
    simp only [nAct_zero, Pi.add_apply, Pi.zero_apply]
    omega

/-- Every natural matrix interpretation is additive in the payload and the counter:
`R(b, s, n) + R(b, 0, 0) = R(b, s, 0) + R(b, 0, n)`. -/
theorem natMatrix_recur_additive (M : NatMatrixData) (b s n : NVec M.d) :
    M.interp.recur b s n + M.interp.recur b 0 0 = M.interp.recur b s 0 + M.interp.recur b 0 n := by
  funext i
  simp only [NatMatrixData.interp, nAct_zero, Pi.add_apply, Pi.zero_apply]
  omega

/-- Identity and shear matrices of dimension two. -/
def idMat2 : NMat 1 := ![![1, 0], ![0, 1]]

def shearMat2 : NMat 1 := ![![1, 1], ![0, 1]]

theorem nAct_idMat2 (v : NVec 1) : nAct idMat2 v = v := by
  funext i
  fin_cases i <;> simp [nAct, idMat2, Fin.sum_univ_two]

/-- A non-affine vector interpretation: the tracked coordinate carries the coupled polynomial
`(n₀ + 1)(s₀ + b₀ + 2)`, the other coordinate is zero. -/
def coupledVectorInterp : Interpretation (NVec 1) where
  zero := 0
  succ n := ![n 0 + 1, 0]
  wrap s y := ![s 0 + y 0 + 1, 0]
  recur b s n := ![(n 0 + 1) * (s 0 + b 0 + 2), 0]

theorem coupledVectorInterp_orients : DupOriented coupledVectorInterp vecLt := by
  rw [dupOriented_iff]
  intro b s n
  refine ⟨?_, fun i => ?_⟩
  · show s 0 + (n 0 + 1) * (s 0 + b 0 + 2) + 1 < (n 0 + 1 + 1) * (s 0 + b 0 + 2)
    nlinarith
  · fin_cases i
    · show s 0 + (n 0 + 1) * (s 0 + b 0 + 2) + 1 ≤ (n 0 + 1 + 1) * (s 0 + b 0 + 2)
      nlinarith
    · exact le_refl 0

/-- The unit vector of the tracked coordinate in dimension two. -/
def e0 : NVec 1 := ![1, 0]

/-! ### matrixNScalarProjection -/

/-- Native data of `matrixNScalarProjection`: a natural matrix interpretation. -/
abbrev matrixNScalarProjectionData : Type := NatMatrixData

/-- Laws of `matrixNScalarProjection`, pinned to J. Endrullis, J. Waldmann, H. Zantema, *Matrix
interpretations for proving termination of term rewriting*, J. Automated Reasoning
40(2–3):195–220, 2008: Definition 1 (extended monotone algebra) instantiated in Section 4 with
`A = ℕ^(d+1)`, `v > u ⟺ v₁ > u₁ ∧ vᵢ ≥ uᵢ`, and `[f](v₁, …, vₙ) = F₁v₁ + ⋯ + Fₙvₙ + f` whose
matrices have positive upper-left entry; Theorem 3 part 1 is the soundness theorem. -/
def matrixNScalarProjectionLaws (M : matrixNScalarProjectionData) : Prop := NatMatrixLaws M

/-- Acceptance: `[ℓ, α] > [r, α]` for every assignment `α` into `ℕ^(d+1)`. -/
def matrixNScalarProjectionAccepts (M : matrixNScalarProjectionData) : Prop :=
  DupOriented M.interp vecLt

/-- Verdict: barrier. -/
def matrixNScalarProjectionResult (M : matrixNScalarProjectionData) : Prop :=
  ¬ matrixNScalarProjectionAccepts M

theorem matrixNScalarProjection_universal :
    ∀ M : matrixNScalarProjectionData, matrixNScalarProjectionLaws M →
      matrixNScalarProjectionResult M :=
  fun M hM => natMatrix_barrier M hM

/-- Witness in dimension two: identity matrices, a shear matrix on the wrapper's payload, and the
successor vector `(1, 0)`. -/
def matrixNScalarProjectionWitness : matrixNScalarProjectionData where
  d := 1
  zeroVec := 0
  succMat := idMat2
  succVec := e0
  wrapLeft := shearMat2
  wrapRight := idMat2
  wrapVec := 0
  recurBase := idMat2
  recurStep := idMat2
  recurCounter := idMat2
  recurVec := 0

theorem matrixNScalarProjectionWitness_laws :
    matrixNScalarProjectionLaws matrixNScalarProjectionWitness := by
  unfold matrixNScalarProjectionLaws
  constructor <;> decide

theorem matrixNScalarProjectionWitness_result :
    matrixNScalarProjectionResult matrixNScalarProjectionWitness :=
  matrixNScalarProjection_universal _ matrixNScalarProjectionWitness_laws

/-- Controls. Untracked coordinates: the order allows a tie at the untracked coordinate and forbids
an increase there. Zero dimension: a zero-dimensional carrier has one point, so no irreflexive
relation relates two of its points; the data therefore fix dimension `d + 1`. Non-affine escape:
every matrix interpretation is additive in payload and counter, the coupled vector interpretation
is not, and it orients the rule under the same order. -/
theorem matrixNScalarProjectionWitness_feature :
    vecLt (![0, 5] : NVec 1) ![1, 5] ∧ ¬ vecLt (![0, 6] : NVec 1) ![1, 5] ∧
      (∀ R : (Fin 0 → ℕ) → (Fin 0 → ℕ) → Prop, (∀ u, ¬ R u u) → ∀ u v, ¬ R u v) ∧
      (∀ (M : NatMatrixData) (b s n : NVec M.d),
        M.interp.recur b s n + M.interp.recur b 0 0 =
          M.interp.recur b s 0 + M.interp.recur b 0 n) ∧
      coupledVectorInterp.recur 0 e0 e0 + coupledVectorInterp.recur 0 0 0 ≠
        coupledVectorInterp.recur 0 e0 0 + coupledVectorInterp.recur 0 0 e0 ∧
      DupOriented coupledVectorInterp vecLt := by
  refine ⟨by unfold vecLt; decide, by unfold vecLt; decide, ?_, natMatrix_recur_additive, ?_,
    coupledVectorInterp_orients⟩
  · intro R hR u v
    have : u = v := funext (fun i => Fin.elim0 i)
    subst this
    exact hR u
  · intro h
    have := congrFun h 0
    revert this
    decide

/-- Erased payload: giving the witness's wrapper payload matrix the value `0` violates the
monotonicity law, and the resulting interpretation accepts the rule. -/
theorem matrixNScalarProjection_mutation :
    ¬ matrixNScalarProjectionLaws { matrixNScalarProjectionWitness with wrapLeft := 0 } ∧
      matrixNScalarProjectionAccepts { matrixNScalarProjectionWitness with wrapLeft := 0 } := by
  constructor
  · intro h
    unfold matrixNScalarProjectionLaws at h
    exact absurd h.wrapLeft_pos (by decide)
  · unfold matrixNScalarProjectionAccepts
    rw [dupOriented_iff]
    intro b s n
    show vecLt (nAct (0 : NMat 1) s +
        nAct idMat2 (nAct idMat2 b + nAct idMat2 s + nAct idMat2 n + (0 : NVec 1)) + (0 : NVec 1))
      (nAct idMat2 b + nAct idMat2 s + nAct idMat2 (nAct idMat2 n + e0) + (0 : NVec 1))
    simp only [nAct_zero_mat, nAct_idMat2, vecLt, Pi.add_apply, Pi.zero_apply]
    refine ⟨?_, fun i => ?_⟩
    · have he : e0 0 = 1 := rfl
      omega
    · omega

theorem matrixNScalarProjection_signature (ι : Type) (arity : ι → ℕ)
    (M : matrixNScalarProjectionData) (ops : (f : ι) → (Fin (arity f) → NVec M.d) → NVec M.d)
    (hM : matrixNScalarProjectionLaws M) :
    ¬ ∀ ρ : Fin 3 → NVec M.d,
      vecLt (({ toInterpretation := M.interp, inertOp := ops } :
          SigInterpretation ι arity (NVec M.d)).eval ρ sigDupRhs)
        (({ toInterpretation := M.interp, inertOp := ops } :
          SigInterpretation ι arity (NVec M.d)).eval ρ sigDupLhs) :=
  fun h => matrixNScalarProjection_universal M hM
    ((sig_dupOrientedOn_iff (fun _ => True) _ vecLt).1 (fun ρ _ => h ρ))

/-! ### triangularMatrix -/

/-- Upper triangular with diagonal entries at most one. -/
def UpperTri {d : ℕ} (A : NMat d) : Prop :=
  (∀ i j : Fin (d + 1), j < i → A i j = 0) ∧ ∀ i, A i i ≤ 1

/-- Matrix product over `ℕ`. -/
def nMul {d : ℕ} (A B : NMat d) : NMat d := fun i j => ∑ l, A i l * B l j

/-- Identity matrix. -/
def nOne {d : ℕ} : NMat d := fun i j => if i = j then 1 else 0

/-- Matrix powers. -/
def nPow {d : ℕ} (A : NMat d) : ℕ → NMat d
  | 0 => nOne
  | k + 1 => nMul (nPow A k) A

/-- The triangular restriction is closed under products: the product is upper triangular and its
diagonal is the product of the diagonals. -/
theorem upperTri_mul {d : ℕ} {A B : NMat d} (hA : UpperTri A) (hB : UpperTri B) :
    UpperTri (nMul A B) := by
  constructor
  · intro i j hji
    apply Finset.sum_eq_zero
    intro l _
    rcases lt_or_ge l i with hl | hl
    · rw [hA.1 i l hl, zero_mul]
    · rw [hB.1 l j (lt_of_lt_of_le hji hl), mul_zero]
  · intro i
    have hdiag : nMul A B i i = A i i * B i i :=
      Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun l _ hli => by
        rcases lt_or_gt_of_ne hli with hl | hl
        · rw [hA.1 i l hl, zero_mul]
        · rw [hB.1 l i hl, mul_zero])
    rw [hdiag]
    calc A i i * B i i ≤ 1 * 1 := Nat.mul_le_mul (hA.2 i) (hB.2 i)
      _ = 1 := rfl

theorem upperTri_nOne {d : ℕ} : UpperTri (nOne : NMat d) := by
  constructor
  · intro i j hji
    simp [nOne, ne_of_gt hji]
  · intro i
    simp [nOne]

theorem upperTri_nPow {d : ℕ} {A : NMat d} (hA : UpperTri A) : ∀ k, UpperTri (nPow A k)
  | 0 => upperTri_nOne
  | k + 1 => upperTri_mul (upperTri_nPow hA k) hA

/-- Growth consequence in dimension two (Moser, Schnabl, Waldmann 2008, Lemma 5 with
`j − i = 1`): the off-diagonal entry of `A^k` grows at most linearly, `(A^k)₀₁ ≤ k A₀₁`. -/
theorem tri2_pow_offdiag {A : NMat 1} (hA : UpperTri A) (k : ℕ) : nPow A k 0 1 ≤ k * A 0 1 := by
  induction k with
  | zero => simp [nPow, nOne]
  | succ k ih =>
      have hd := (upperTri_nPow hA k).2 0
      have h11 := hA.2 1
      show nMul (nPow A k) A 0 1 ≤ (k + 1) * A 0 1
      have hsum : nMul (nPow A k) A 0 1 = nPow A k 0 0 * A 0 1 + nPow A k 0 1 * A 1 1 := by
        simp only [nMul, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
        rfl
      rw [hsum]
      have e1 : nPow A k 0 0 * A 0 1 ≤ 1 * A 0 1 := Nat.mul_le_mul_right _ hd
      have e2 : nPow A k 0 1 * A 1 1 ≤ (k * A 0 1) * 1 := Nat.mul_le_mul ih h11
      nlinarith

/-- Admissibility of a triangular matrix interpretation: the matrix laws and every argument matrix
upper triangular with diagonal entries at most one. -/
structure TriangularLaws (M : NatMatrixData) : Prop where
  matrix : NatMatrixLaws M
  succ_tri : UpperTri M.succMat
  wrapLeft_tri : UpperTri M.wrapLeft
  wrapRight_tri : UpperTri M.wrapRight
  recurBase_tri : UpperTri M.recurBase
  recurStep_tri : UpperTri M.recurStep
  recurCounter_tri : UpperTri M.recurCounter

/-- Native data of `triangularMatrix`: a natural matrix interpretation. -/
abbrev triangularMatrixData : Type := NatMatrixData

/-- Laws of `triangularMatrix`, pinned to G. Moser, A. Schnabl, J. Waldmann, *Complexity analysis
of term rewriting based on matrix and context dependent interpretations*, FSTTCS 2008, LIPIcs 2,
pp. 304–315, Definition 3 (upper triangular: `M_ij = 0` for `i > j` and `M_ii ≤ 1`; a triangular
matrix interpretation uses only such matrices) on top of the matrix method of Endrullis, Waldmann
and Zantema 2008; Lemma 5 and Theorem 6 give the polynomial growth. -/
def triangularMatrixLaws (M : triangularMatrixData) : Prop := TriangularLaws M

/-- Acceptance: `[ℓ, α] > [r, α]` for every assignment into `ℕ^(d+1)`. -/
def triangularMatrixAccepts (M : triangularMatrixData) : Prop := DupOriented M.interp vecLt

/-- Verdict: barrier. -/
def triangularMatrixResult (M : triangularMatrixData) : Prop := ¬ triangularMatrixAccepts M

/-- The triangular class is a subclass of the natural matrix class, so the tracked P3.2 cell
applies. -/
theorem triangularMatrix_universal :
    ∀ M : triangularMatrixData, triangularMatrixLaws M → triangularMatrixResult M :=
  fun M hM => natMatrix_barrier M (show TriangularLaws M from hM).matrix

/-- Witness: the matrix witness, whose matrices are all upper triangular with unit diagonal. -/
def triangularMatrixWitness : triangularMatrixData := matrixNScalarProjectionWitness

theorem triangularMatrixWitness_laws : triangularMatrixLaws triangularMatrixWitness := by
  unfold triangularMatrixLaws
  refine ⟨matrixNScalarProjectionWitness_laws, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (unfold UpperTri; decide)

theorem triangularMatrixWitness_result : triangularMatrixResult triangularMatrixWitness :=
  triangularMatrix_universal _ triangularMatrixWitness_laws

/-- Controls. Nontrivial off-diagonal entries: the wrapper's payload matrix is the shear
`[[1, 1], [0, 1]]`. Order and growth consequence: every power of it keeps diagonal entries at most
one and its off-diagonal entry grows at most linearly. -/
theorem triangularMatrixWitness_feature :
    triangularMatrixWitness.wrapLeft 0 1 = 1 ∧
      (∀ k, UpperTri (nPow triangularMatrixWitness.wrapLeft k)) ∧
      (∀ k, nPow shearMat2 k 0 1 ≤ k) := by
  have hsh : UpperTri shearMat2 := by unfold UpperTri; decide
  refine ⟨rfl, upperTri_nPow hsh, fun k => ?_⟩
  have := tri2_pow_offdiag hsh k
  have h1 : shearMat2 0 1 = 1 := rfl
  rw [h1, mul_one] at this
  exact this

/-- Removed triangularity: a nonzero entry below the diagonal of the wrapper's payload matrix
violates the triangular law. -/
theorem triangularMatrix_mutation :
    ¬ triangularMatrixLaws { triangularMatrixWitness with wrapLeft := ![![1, 1], ![1, 1]] } := by
  intro h
  unfold triangularMatrixLaws at h
  have := h.wrapLeft_tri.1 1 0 (by decide)
  revert this
  decide

theorem triangularMatrix_signature (ι : Type) (arity : ι → ℕ) (M : triangularMatrixData)
    (ops : (f : ι) → (Fin (arity f) → NVec M.d) → NVec M.d) (hM : triangularMatrixLaws M) :
    ¬ ∀ ρ : Fin 3 → NVec M.d,
      vecLt (({ toInterpretation := M.interp, inertOp := ops } :
          SigInterpretation ι arity (NVec M.d)).eval ρ sigDupRhs)
        (({ toInterpretation := M.interp, inertOp := ops } :
          SigInterpretation ι arity (NVec M.d)).eval ρ sigDupLhs) :=
  fun h => triangularMatrix_universal M hM
    ((sig_dupOrientedOn_iff (fun _ => True) _ vecLt).1 (fun ρ _ => h ρ))

/-! ### matrixQRScalarProjection -/

/-- Real vectors of dimension `d + 1`. -/
abbrev RVec (d : ℕ) : Type := Fin (d + 1) → ℝ

/-- Real square matrices of dimension `d + 1`. -/
abbrev RMat (d : ℕ) : Type := Fin (d + 1) → Fin (d + 1) → ℝ

/-- Matrix-vector product over `ℝ`. -/
def rAct {d : ℕ} (A : RMat d) (v : RVec d) : RVec d := fun i => ∑ j, A i j * v j

theorem rAct_zero {d : ℕ} (A : RMat d) : rAct A 0 = 0 := by
  funext i
  simp [rAct]

theorem rAct_zero_mat {d : ℕ} (v : RVec d) : rAct (0 : RMat d) v = 0 := by
  funext i
  simp [rAct]

/-- Entrywise nonnegative vectors, the carrier of the method. -/
def NonnegVec {d : ℕ} (v : RVec d) : Prop := ∀ i, 0 ≤ v i

/-- Entrywise nonnegative matrices. -/
def NonnegMat {d : ℕ} (A : RMat d) : Prop := ∀ i j, 0 ≤ A i j

theorem rAct_nonneg {d : ℕ} {A : RMat d} {v : RVec d} (hA : NonnegMat A) (hv : NonnegVec v) :
    NonnegVec (rAct A v) :=
  fun i => Finset.sum_nonneg (fun j _ => mul_nonneg (hA i j) (hv j))

theorem rAct_ge_diag {d : ℕ} {A : RMat d} {v : RVec d} (hA : NonnegMat A) (hv : NonnegVec v) :
    A 0 0 * v 0 ≤ rAct A v 0 :=
  Finset.single_le_sum (f := fun j => A 0 j * v j) (fun j _ => mul_nonneg (hA 0 j) (hv j))
    (Finset.mem_univ 0)

/-- The unit-direction vector `c e₀`. -/
def rUnit {d : ℕ} (c : ℝ) : RVec d := fun i => if i = 0 then c else 0

theorem rUnit_zero {d : ℕ} (c : ℝ) : (rUnit c : RVec d) 0 = c := if_pos rfl

theorem rUnit_nonneg {d : ℕ} {c : ℝ} (hc : 0 ≤ c) : NonnegVec (rUnit c : RVec d) := by
  intro i
  unfold rUnit
  split_ifs
  · exact hc
  · exact le_refl 0

/-- A real matrix interpretation with separation `δ`. -/
structure RealMatrixData where
  d : ℕ
  δ : ℝ
  zeroVec : RVec d
  succMat : RMat d
  succVec : RVec d
  wrapLeft : RMat d
  wrapRight : RMat d
  wrapVec : RVec d
  recurBase : RMat d
  recurStep : RMat d
  recurCounter : RMat d
  recurVec : RVec d

/-- `[f](v₁, …, vₙ) = F₁ v₁ + ⋯ + Fₙ vₙ + f` over `ℝ`. -/
def RealMatrixData.interp (M : RealMatrixData) : Interpretation (RVec M.d) where
  zero := M.zeroVec
  succ n := rAct M.succMat n + M.succVec
  wrap s y := rAct M.wrapLeft s + rAct M.wrapRight y + M.wrapVec
  recur b s n := rAct M.recurBase b + rAct M.recurStep s + rAct M.recurCounter n + M.recurVec

/-- The separated order on nonnegative real vectors, smaller side first: `x₀ + δ ≤ y₀` and
`xᵢ ≤ yᵢ` at every coordinate. -/
def rvecLt {d : ℕ} (δ : ℝ) (x y : RVec d) : Prop := x 0 + δ ≤ y 0 ∧ ∀ i, x i ≤ y i

/-- Admissibility: positive separation, nonnegative entries (the algebra maps nonnegative vectors
to nonnegative vectors), and argument matrices with upper-left entry at least one. -/
structure RealMatrixLaws (M : RealMatrixData) : Prop where
  delta_pos : 0 < M.δ
  zeroVec_nonneg : NonnegVec M.zeroVec
  succMat_nonneg : NonnegMat M.succMat
  succVec_nonneg : NonnegVec M.succVec
  wrapLeft_nonneg : NonnegMat M.wrapLeft
  wrapRight_nonneg : NonnegMat M.wrapRight
  wrapVec_nonneg : NonnegVec M.wrapVec
  recurBase_nonneg : NonnegMat M.recurBase
  recurStep_nonneg : NonnegMat M.recurStep
  recurCounter_nonneg : NonnegMat M.recurCounter
  recurVec_nonneg : NonnegVec M.recurVec
  succ_pos : 1 ≤ M.succMat 0 0
  wrapLeft_pos : 1 ≤ M.wrapLeft 0 0
  wrapRight_pos : 1 ≤ M.wrapRight 0 0
  recurBase_pos : 1 ≤ M.recurBase 0 0
  recurStep_pos : 1 ≤ M.recurStep 0 0
  recurCounter_pos : 1 ≤ M.recurCounter 0 0

/-- The separated vector order is well founded on nonnegative vectors, through its first
coordinate. -/
theorem rvecLt_wf {d : ℕ} (δ : ℝ) (hδ : 0 < δ) :
    WellFounded (fun x y : {v : RVec d // NonnegVec v} => rvecLt δ x.1 y.1) := by
  refine Subrelation.wf (r := InvImage (fun x y : {r : ℝ // 0 ≤ r} => sepLt δ x.1 y.1)
    (fun v : {v : RVec d // NonnegVec v} => (⟨v.1 0, v.2 0⟩ : {r : ℝ // 0 ≤ r}))) ?_
    (InvImage.wf _ (sepLt_wf_real δ hδ))
  intro x y hxy
  exact hxy.1

/-- The P3.2 cell over the reals at the tracked coordinate, at `b = n = 0`. -/
theorem realMatrix_barrier (M : RealMatrixData) (hM : RealMatrixLaws M) :
    ¬ DupOrientedOn NonnegVec M.interp (rvecLt M.δ) := by
  intro hacc
  have hor := (dupOrientedOn_iff _ _ _).1 hacc
  have h0 : NonnegVec (0 : RVec M.d) := fun _ => le_refl 0
  refine ordered_barrier_cell_on M.interp NonnegVec (fun v => v 0) 0 0 ?_ ?_ ?_
  · intro K
    have hc : (0 : ℝ) ≤ |K| + 1 := by positivity
    refine ⟨rUnit (|K| + 1), rUnit_nonneg hc, ?_⟩
    have hs := rUnit_nonneg (d := M.d) hc
    have hy : NonnegVec (M.interp.recur 0 (rUnit (|K| + 1)) 0) := by
      intro i
      show 0 ≤ rAct M.recurBase 0 i + rAct M.recurStep (rUnit (|K| + 1)) i +
        rAct M.recurCounter 0 i + M.recurVec i
      have a1 := rAct_nonneg hM.recurBase_nonneg h0 i
      have a2 := rAct_nonneg hM.recurStep_nonneg hs i
      have a3 := rAct_nonneg hM.recurCounter_nonneg h0 i
      have a4 := hM.recurVec_nonneg i
      linarith
    have h1 := rAct_ge_diag hM.wrapLeft_nonneg hs
    have h2 := rAct_ge_diag hM.wrapRight_nonneg hy
    have h3 := le_mul_of_one_le_left (hs 0) hM.wrapLeft_pos
    have h4 := le_mul_of_one_le_left (hy 0) hM.wrapRight_pos
    have h5 := hM.wrapVec_nonneg 0
    have h6 := le_abs_self K
    rw [rUnit_zero] at h1 h3
    show M.interp.recur 0 (rUnit (|K| + 1)) 0 0 + K <
      rAct M.wrapLeft (rUnit (|K| + 1)) 0 +
        rAct M.wrapRight (M.interp.recur 0 (rUnit (|K| + 1)) 0) 0 + M.wrapVec 0
    linarith
  · refine ⟨rAct M.recurCounter (M.interp.succ 0) 0, fun s _ => ?_⟩
    show (rAct M.recurBase 0 + rAct M.recurStep s + rAct M.recurCounter (M.interp.succ 0) +
        M.recurVec) 0 ≤
      (rAct M.recurBase 0 + rAct M.recurStep s + rAct M.recurCounter 0 + M.recurVec) 0 +
        rAct M.recurCounter (M.interp.succ 0) 0
    simp only [rAct_zero, Pi.add_apply, Pi.zero_apply]
    linarith
  · intro s hs
    have h := (hor 0 s 0 h0 hs h0).1
    have := hM.delta_pos
    linarith

/-- Native data of `matrixQRScalarProjection`: a real matrix interpretation with separation. -/
abbrev matrixQRScalarProjectionData : Type := RealMatrixData

/-- Laws of `matrixQRScalarProjection`, pinned to S. Lucas, *From matrix interpretations over the
rationals to matrix interpretations over the naturals*, arXiv:1007.0143 (AISC 2010), Section
"Matrix interpretations revisited" with block size `b = 1` over `ℝ₀`: the approach of Endrullis,
Waldmann and Zantema extended to real entries, compared by `x >_δ y ⟺ x − y ≥ δ` on the first
entry and `≥` entrywise, well founded for `δ > 0`; rational entries are the special case of rational
tables. The monotonicity condition is the upper-left entry at least one. -/
def matrixQRScalarProjectionLaws (M : matrixQRScalarProjectionData) : Prop := RealMatrixLaws M

/-- Acceptance over all nonnegative real vector assignments. -/
def matrixQRScalarProjectionAccepts (M : matrixQRScalarProjectionData) : Prop :=
  DupOrientedOn NonnegVec M.interp (rvecLt M.δ)

/-- Verdict: barrier. -/
def matrixQRScalarProjectionResult (M : matrixQRScalarProjectionData) : Prop :=
  ¬ matrixQRScalarProjectionAccepts M

theorem matrixQRScalarProjection_universal :
    ∀ M : matrixQRScalarProjectionData, matrixQRScalarProjectionLaws M →
      matrixQRScalarProjectionResult M :=
  fun M hM => realMatrix_barrier M hM

/-- Real identity matrix of dimension two. -/
noncomputable def idR2 : RMat 1 := ![![1, 0], ![0, 1]]

/-- A wrapper payload matrix with the genuine entry `3/2`. -/
noncomputable def wrapR2 : RMat 1 := ![![3 / 2, 1], ![0, 1]]

theorem rAct_idR2 (v : RVec 1) : rAct idR2 v = v := by
  funext i
  fin_cases i <;> simp [rAct, idR2, Fin.sum_univ_two]

/-- Witness with separation `δ = 1/100` and the entry `3/2`. -/
noncomputable def matrixQRScalarProjectionWitness : matrixQRScalarProjectionData where
  d := 1
  δ := 1 / 100
  zeroVec := 0
  succMat := idR2
  succVec := ![1, 0]
  wrapLeft := wrapR2
  wrapRight := idR2
  wrapVec := 0
  recurBase := idR2
  recurStep := idR2
  recurCounter := idR2
  recurVec := 0

theorem nonnegMat_idR2 : NonnegMat idR2 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [idR2]

theorem nonnegMat_wrapR2 : NonnegMat wrapR2 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [wrapR2]

theorem nonnegVec_e0R : NonnegVec (![1, 0] : RVec 1) := by
  intro i
  fin_cases i <;> norm_num

theorem idR2_pos : (1 : ℝ) ≤ idR2 0 0 := by norm_num [idR2]

theorem wrapR2_pos : (1 : ℝ) ≤ wrapR2 0 0 := by norm_num [wrapR2]

theorem matrixQRScalarProjectionWitness_laws :
    matrixQRScalarProjectionLaws matrixQRScalarProjectionWitness := by
  unfold matrixQRScalarProjectionLaws
  exact ⟨by norm_num [matrixQRScalarProjectionWitness], fun _ => le_refl 0, nonnegMat_idR2,
    nonnegVec_e0R, nonnegMat_wrapR2, nonnegMat_idR2, fun _ => le_refl 0, nonnegMat_idR2,
    nonnegMat_idR2, nonnegMat_idR2, fun _ => le_refl 0, idR2_pos, wrapR2_pos, idR2_pos,
    idR2_pos, idR2_pos, idR2_pos⟩

theorem matrixQRScalarProjectionWitness_result :
    matrixQRScalarProjectionResult matrixQRScalarProjectionWitness :=
  matrixQRScalarProjection_universal _ matrixQRScalarProjectionWitness_laws

/-- Controls. Genuine `3/2` entry: the wrapper's upper-left entry is not a natural number. Small
positive gap: `δ = 1/100`, and the separated order at this `δ` is well founded on nonnegative
vectors, while the unseparated order on nonnegative reals is not. Zero dimension: a
zero-dimensional carrier has one point. -/
theorem matrixQRScalarProjectionWitness_feature :
    (¬ ∃ k : ℕ, (k : ℝ) = matrixQRScalarProjectionWitness.wrapLeft 0 0) ∧
      matrixQRScalarProjectionWitness.δ = 1 / 100 ∧
      WellFounded (fun x y : {v : RVec 1 // NonnegVec v} =>
        rvecLt matrixQRScalarProjectionWitness.δ x.1 y.1) ∧
      ¬ WellFounded (fun x y : {r : ℝ // 0 ≤ r} => x.1 < y.1) ∧
      (∀ R : (Fin 0 → ℝ) → (Fin 0 → ℝ) → Prop, (∀ u, ¬ R u u) → ∀ u v, ¬ R u v) := by
  refine ⟨?_, rfl, rvecLt_wf _ (by norm_num [matrixQRScalarProjectionWitness]), real_lt_not_wf,
    ?_⟩
  · rintro ⟨k, hk⟩
    have hk' : (k : ℝ) = 3 / 2 := by simpa [matrixQRScalarProjectionWitness, wrapR2] using hk
    have h2 : ((2 * k : ℕ) : ℝ) = 3 := by push_cast; linarith
    have h3 : 2 * k = 3 := by exact_mod_cast h2
    omega
  · intro R hR u v
    have : u = v := funext (fun i => Fin.elim0 i)
    subst this
    exact hR u

/-- Erased payload: giving the witness's wrapper payload matrix the value `0` violates the
monotonicity law, and the resulting interpretation accepts the rule. -/
theorem matrixQRScalarProjection_mutation :
    ¬ matrixQRScalarProjectionLaws { matrixQRScalarProjectionWitness with wrapLeft := 0 } ∧
      matrixQRScalarProjectionAccepts { matrixQRScalarProjectionWitness with wrapLeft := 0 } := by
  constructor
  · intro h
    unfold matrixQRScalarProjectionLaws at h
    have := h.wrapLeft_pos
    norm_num at this
  · unfold matrixQRScalarProjectionAccepts
    rw [dupOrientedOn_iff]
    intro b s n _ _ _
    show rvecLt (1 / 100) (rAct (0 : RMat 1) s +
        rAct idR2 (rAct idR2 b + rAct idR2 s + rAct idR2 n + (0 : RVec 1)) + (0 : RVec 1))
      (rAct idR2 b + rAct idR2 s + rAct idR2 (rAct idR2 n + ![1, 0]) + (0 : RVec 1))
    simp only [rAct_zero_mat, rAct_idR2, rvecLt, Pi.add_apply, Pi.zero_apply]
    refine ⟨?_, fun i => ?_⟩
    · have he : (![1, 0] : RVec 1) 0 = 1 := rfl
      rw [he]
      linarith
    · have he : 0 ≤ (![1, 0] : RVec 1) i := by fin_cases i <;> norm_num
      linarith

theorem matrixQRScalarProjection_signature (ι : Type) (arity : ι → ℕ)
    (M : matrixQRScalarProjectionData) (ops : (f : ι) → (Fin (arity f) → RVec M.d) → RVec M.d)
    (hM : matrixQRScalarProjectionLaws M) :
    ¬ ∀ ρ : Fin 3 → RVec M.d, (∀ i, NonnegVec (ρ i)) →
      rvecLt M.δ (({ toInterpretation := M.interp, inertOp := ops } :
          SigInterpretation ι arity (RVec M.d)).eval ρ sigDupRhs)
        (({ toInterpretation := M.interp, inertOp := ops } :
          SigInterpretation ι arity (RVec M.d)).eval ρ sigDupLhs) :=
  fun h => matrixQRScalarProjection_universal M hM
    ((sig_dupOrientedOn_iff NonnegVec _ (rvecLt M.δ)).1 h)

/-! ## Acceptance for full termination along the rewrite relation -/

/-- Instances of the free duplicating rule under one-hole free contexts. -/
inductive DupCtxStep {ν : Type} : FreeTerm ν → FreeTerm ν → Prop
  | lift (C : FreeContext ν) (b s n : FreeTerm ν) :
      DupCtxStep (C.plug (.recur b s (.succ n))) (C.plug (.wrap s (.recur b s n)))

/-- Every such step is a step of the free contextual relation. -/
theorem DupCtxStep.contextStep {ν : Type} {a c : FreeTerm ν} (h : DupCtxStep a c) :
    ContextStep a c := by
  cases h with
  | lift C b s n => exact ContextStep.lift C (RootStep.recurSucc b s n)

/-- Decrease along the rewrite relation of the duplicating rule on a domain `D`: every contextual
instance decreases in `lt` under every valuation into `D`. -/
def DupCtxOrientedOn {α : Type} (D : α → Prop) (I : Interpretation α) (lt : α → α → Prop) :
    Prop :=
  ∀ ρ : ℕ → α, (∀ j, D (ρ j)) → ∀ a c : FreeTerm ℕ, DupCtxStep a c → lt (I.eval ρ c) (I.eval ρ a)

/-- Contextual decrease at the two wrapper contexts around one rule instance, with context
argument `t`. -/
theorem dupCtx_wrap_instances {α : Type} (D : α → Prop) (I : Interpretation α)
    (lt : α → α → Prop) (h : DupCtxOrientedOn D I lt) (b s n t : α) (hb : D b) (hs : D s)
    (hn : D n) (ht : D t) :
    lt (I.wrap t (I.wrap s (I.recur b s n))) (I.wrap t (I.recur b s (I.succ n))) ∧
      lt (I.wrap (I.wrap s (I.recur b s n)) t) (I.wrap (I.recur b s (I.succ n)) t) := by
  have hρ : ∀ j, D ((fun j : ℕ => if j = 0 then b else if j = 1 then s else
      if j = 2 then n else t) j) := by
    intro j
    show D (if j = 0 then b else if j = 1 then s else if j = 2 then n else t)
    split_ifs
    · exact hb
    · exact hs
    · exact hn
    · exact ht
  constructor
  · have := h _ hρ _ _ (DupCtxStep.lift (.wrapRight (.var 3) .hole) (.var 0) (.var 1) (.var 2))
    simpa [FreeContext.plug] using this
  · have := h _ hρ _ _ (DupCtxStep.lift (.wrapLeft .hole (.var 3)) (.var 0) (.var 1) (.var 2))
    simpa [FreeContext.plug] using this

/-! ## Arctic matrix interpretations -/

/-- Arctic vectors of dimension `d + 1` over `ℕ ∪ {−∞}`; `⊥` is `−∞`. -/
abbrev AVec (d : ℕ) : Type := Fin (d + 1) → WithBot ℕ

/-- Arctic square matrices. -/
abbrev AMat (d : ℕ) : Type := Fin (d + 1) → Fin (d + 1) → WithBot ℕ

/-- Arctic matrix action `(A ⊗ v)ᵢ = max_j (A i j + v j)`. -/
def aAct {d : ℕ} (A : AMat d) (v : AVec d) : AVec d :=
  fun i => Finset.univ.sup (fun j => A i j + v j)

/-- The constant arctic vector with every entry `K`. -/
def aConst {d : ℕ} (K : ℕ) : AVec d := fun _ => WithBot.some K

/-- The arctic vector `(K, −∞, …, −∞)`. -/
def aUnit {d : ℕ} (K : ℕ) : AVec d := fun i => if i = 0 then WithBot.some K else ⊥

/-- Arctic linear functions for the four schema symbols. -/
structure ArcticData where
  d : ℕ
  zeroVec : AVec d
  succMat : AMat d
  succVec : AVec d
  wrapLeft : AMat d
  wrapRight : AMat d
  wrapVec : AVec d
  recurBase : AMat d
  recurStep : AMat d
  recurCounter : AMat d
  recurVec : AVec d

/-- `[f](v₁, …, vₙ) = M₁ ⊗ v₁ ⊕ ⋯ ⊕ Mₙ ⊗ vₙ ⊕ c` with `⊕ = max` and `⊗ = +`. -/
def ArcticData.interp (M : ArcticData) : Interpretation (AVec M.d) where
  zero := M.zeroVec
  succ n := fun i => max (aAct M.succMat n i) (M.succVec i)
  wrap s y := fun i => max (max (aAct M.wrapLeft s i) (aAct M.wrapRight y i)) (M.wrapVec i)
  recur b s n := fun i =>
    max (max (max (aAct M.recurBase b i) (aAct M.recurStep s i)) (aAct M.recurCounter n i))
      (M.recurVec i)

/-- The domain `ℕ × A^d`: the first coordinate is finite. -/
def AFin {d : ℕ} (v : AVec d) : Prop := v 0 ≠ ⊥

/-- The strict order `≫`, pointwise, smaller side first: every coordinate increases strictly or
both coordinates are `−∞`. -/
def arcLt {d : ℕ} (x y : AVec d) : Prop := ∀ i, x i < y i ∨ (x i = ⊥ ∧ y i = ⊥)

/-- Somewhere finiteness of every symbol and a finite first coordinate of the constant. -/
structure ArcticLaws (M : ArcticData) : Prop where
  zero_fin : M.zeroVec 0 ≠ ⊥
  succ_sf : M.succVec 0 ≠ ⊥ ∨ M.succMat 0 0 ≠ ⊥
  wrap_sf : M.wrapVec 0 ≠ ⊥ ∨ M.wrapLeft 0 0 ≠ ⊥ ∨ M.wrapRight 0 0 ≠ ⊥
  recur_sf : M.recurVec 0 ≠ ⊥ ∨ M.recurBase 0 0 ≠ ⊥ ∨ M.recurStep 0 0 ≠ ⊥ ∨
    M.recurCounter 0 0 ≠ ⊥

/-- Every arctic value is bounded by a natural number. -/
theorem wb_exists_ge (x : WithBot ℕ) : ∃ B : ℕ, x ≤ WithBot.some B := by
  cases x with
  | bot => exact ⟨0, bot_le⟩
  | coe n => exact ⟨n, le_refl _⟩

/-- A finite offset does not decrease an arctic value. -/
theorem wb_le_coe_add (q : ℕ) (y : WithBot ℕ) : y ≤ WithBot.some q + y := by
  cases y with
  | bot => exact bot_le
  | coe n =>
      rw [← WithBot.coe_add]
      exact WithBot.coe_le_coe.2 (Nat.le_add_left n q)

/-- A finite arctic value is below its successor. -/
theorem wb_coe_lt_one_add (k : ℕ) : (WithBot.some k : WithBot ℕ) < 1 + WithBot.some k := by
  have h := WithBot.coe_lt_coe.2 (show k < 1 + k by omega)
  rwa [WithBot.coe_add, WithBot.coe_one] at h

/-- The action on `(K, −∞, …, −∞)` reads the first column only. -/
theorem aAct_aUnit {d : ℕ} (A : AMat d) (K : ℕ) (i : Fin (d + 1)) :
    aAct A (aUnit K) i = A i 0 + WithBot.some K := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    by_cases hj : j = 0
    · subst hj
      simp [aUnit]
    · simp [aUnit, hj]
  · calc A i 0 + WithBot.some K = A i 0 + aUnit K 0 := by simp [aUnit]
      _ ≤ aAct A (aUnit K) i :=
        Finset.le_sup (f := fun j => A i j + aUnit K j) (Finset.mem_univ 0)

/-- Contextual masking by `max`: no arctic interpretation over `ℕ × A^d` decreases along every
wrapper-context instance of the duplicating rule. If the wrapper reads its first argument at the
tracked row, a large first argument masks both sides; otherwise the wrapper ignores the instance
placed in its first argument, and somewhere finiteness keeps both sides finite and equal. Consumed
law: `wrap_sf`. -/
theorem arctic_context_barrier (M : ArcticData) (hM : ArcticLaws M) :
    ¬ DupCtxOrientedOn AFin M.interp arcLt := by
  intro hacc
  have hz : AFin (aConst 0 : AVec M.d) := WithBot.coe_ne_bot
  by_cases hA : ∃ j, M.wrapLeft 0 j ≠ ⊥
  · obtain ⟨j0, hj0⟩ := hA
    obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1 hj0
    obtain ⟨B1, hB1⟩ := wb_exists_ge
      (aAct M.wrapRight (M.interp.recur (aConst 0) (aConst 0) (M.interp.succ (aConst 0))) 0)
    obtain ⟨B2, hB2⟩ := wb_exists_ge
      (aAct M.wrapRight (M.interp.wrap (aConst 0) (M.interp.recur (aConst 0) (aConst 0)
        (aConst 0))) 0)
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
    have key := (dupCtx_wrap_instances AFin M.interp arcLt hacc (aConst 0) (aConst 0) (aConst 0)
      (aConst K) hz hz hz ht).1 0
    rw [hwrapEq _ (le_trans hB2 (le_trans (WithBot.coe_le_coe.2 hK2) hP)),
      hwrapEq _ (le_trans hB1 (le_trans (WithBot.coe_le_coe.2 hK1) hP))] at key
    rcases key with h | ⟨h, _⟩
    · exact lt_irrefl _ h
    · exact ne_bot_of_le_ne_bot WithBot.coe_ne_bot hP h
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
      rcases hM.wrap_sf with hw | hl | hr
      · exact ne_bot_of_le_ne_bot hw (le_max_right _ _)
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
    have key := (dupCtx_wrap_instances AFin M.interp arcLt hacc (aConst 0) (aConst 0) (aConst 0)
      (aConst 0) hz hz hz hz).2 0
    rw [hwrapEq, hwrapEq] at key
    rcases key with h | ⟨h, _⟩
    · exact lt_irrefl _ h
    · exact hne h

/-- Non-erasure at the root (the P3.2 max-plus alternative): if both wrapper diagonal entries at
the tracked coordinate are finite, the root rule is not oriented. With a finite payload entry of
the recursor, a large payload `(K, −∞, …)` masks the counter at both counters (gain zero) while the
wrapper keeps the recursive result; without it, the recursor ignores the payload and the wrapper's
payload branch grows past it. -/
theorem arctic_nonErasing_root_barrier (M : ArcticData) (hl : M.wrapLeft 0 0 ≠ ⊥)
    (hr : M.wrapRight 0 0 ≠ ⊥) : ¬ DupOrientedOn AFin M.interp arcLt := by
  intro hacc
  have hor := (dupOrientedOn_iff _ _ _).1 hacc
  have hz : AFin (aConst 0 : AVec M.d) := WithBot.coe_ne_bot
  have hu : ∀ K : ℕ, AFin (aUnit K : AVec M.d) := fun K => by
    show (aUnit K : AVec M.d) 0 ≠ ⊥
    simp [aUnit]
  obtain ⟨p, hp⟩ := WithBot.ne_bot_iff_exists.1 hl
  obtain ⟨q, hq⟩ := WithBot.ne_bot_iff_exists.1 hr
  have hrec : ∀ (K : ℕ) (m : AVec M.d), M.interp.recur (aConst 0) (aUnit K) m 0 =
      max (max (max (aAct M.recurBase (aConst 0) 0) (M.recurStep 0 0 + WithBot.some K))
        (aAct M.recurCounter m 0)) (M.recurVec 0) := by
    intro K m
    show max (max (max (aAct M.recurBase (aConst 0) 0) (aAct M.recurStep (aUnit K) 0))
      (aAct M.recurCounter m 0)) (M.recurVec 0) = _
    rw [aAct_aUnit]
  by_cases hs : M.recurStep 0 0 = ⊥
  · obtain ⟨B, hB⟩ := wb_exists_ge (max (max (max (aAct M.recurBase (aConst 0 : AVec M.d) 0) ⊥)
      (aAct M.recurCounter (M.interp.succ (aConst 0)) 0)) (M.recurVec 0))
    have key := hor (aConst 0) (aUnit B) (aConst 0) hz (hu B) hz 0
    rw [hrec, hs, WithBot.bot_add] at key
    have hw : WithBot.some (p + B) ≤
        M.interp.wrap (aUnit B) (M.interp.recur (aConst 0) (aUnit B) (aConst 0)) 0 := by
      have h1 : aAct M.wrapLeft (aUnit B) 0 ≤
          M.interp.wrap (aUnit B) (M.interp.recur (aConst 0) (aUnit B) (aConst 0)) 0 :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      rw [aAct_aUnit, ← hp, ← WithBot.coe_add] at h1
      exact h1
    rcases key with h | ⟨h1, _⟩
    · have h2 := lt_of_lt_of_le (lt_of_le_of_lt hw h) hB
      have h3 := WithBot.coe_lt_coe.1 h2
      omega
    · exact ne_bot_of_le_ne_bot WithBot.coe_ne_bot hw h1
  · obtain ⟨r, hrr⟩ := WithBot.ne_bot_iff_exists.1 hs
    obtain ⟨B1, hB1⟩ := wb_exists_ge (aAct M.recurBase (aConst 0 : AVec M.d) 0)
    obtain ⟨B2, hB2⟩ := wb_exists_ge (aAct M.recurCounter (aConst 0 : AVec M.d) 0)
    obtain ⟨B3, hB3⟩ := wb_exists_ge (aAct M.recurCounter (M.interp.succ (aConst 0)) 0)
    obtain ⟨B4, hB4⟩ := wb_exists_ge (M.recurVec 0)
    obtain ⟨K, hK⟩ : ∃ K : ℕ, B1 + B2 + B3 + B4 ≤ r + K := ⟨B1 + B2 + B3 + B4, by omega⟩
    have hval : ∀ m : AVec M.d, aAct M.recurCounter m 0 ≤ WithBot.some (B2 + B3) →
        M.interp.recur (aConst 0) (aUnit K) m 0 = WithBot.some (r + K) := by
      intro m hm
      rw [hrec, ← hrr, ← WithBot.coe_add]
      have e1 : aAct M.recurBase (aConst 0 : AVec M.d) 0 ≤ WithBot.some (r + K) :=
        le_trans hB1 (WithBot.coe_le_coe.2 (by omega))
      have e2 : aAct M.recurCounter m 0 ≤ WithBot.some (r + K) :=
        le_trans hm (WithBot.coe_le_coe.2 (by omega))
      have e3 : M.recurVec 0 ≤ WithBot.some (r + K) :=
        le_trans hB4 (WithBot.coe_le_coe.2 (by omega))
      rw [max_eq_right e1, max_eq_left e2, max_eq_left e3]
    have hv0 := hval (aConst 0) (le_trans hB2 (WithBot.coe_le_coe.2 (by omega)))
    have hv1 := hval (M.interp.succ (aConst 0)) (le_trans hB3 (WithBot.coe_le_coe.2 (by omega)))
    have hw : M.interp.recur (aConst 0) (aUnit K) (aConst 0) 0 ≤
        M.interp.wrap (aUnit K) (M.interp.recur (aConst 0) (aUnit K) (aConst 0)) 0 := by
      have h1 : aAct M.wrapRight (M.interp.recur (aConst 0) (aUnit K) (aConst 0)) 0 ≤
          M.interp.wrap (aUnit K) (M.interp.recur (aConst 0) (aUnit K) (aConst 0)) 0 :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      have h2 : M.wrapRight 0 0 + M.interp.recur (aConst 0) (aUnit K) (aConst 0) 0 ≤
          aAct M.wrapRight (M.interp.recur (aConst 0) (aUnit K) (aConst 0)) 0 :=
        Finset.le_sup (f := fun j => M.wrapRight 0 j +
          M.interp.recur (aConst 0) (aUnit K) (aConst 0) j) (Finset.mem_univ 0)
      have h3 : M.interp.recur (aConst 0) (aUnit K) (aConst 0) 0 ≤
          M.wrapRight 0 0 + M.interp.recur (aConst 0) (aUnit K) (aConst 0) 0 := by
        rw [← hq]
        exact wb_le_coe_add q _
      exact le_trans h3 (le_trans h2 h1)
    rw [hv0] at hw
    have key := hor (aConst 0) (aUnit K) (aConst 0) hz (hu K) hz 0
    rw [hv1] at key
    rcases key with h | ⟨_, h2⟩
    · exact lt_irrefl _ (lt_of_le_of_lt hw h)
    · exact WithBot.coe_ne_bot h2

/-- The action in dimension one. -/
theorem aAct_one (A : AMat 0) (v : AVec 0) (i : Fin (0 + 1)) : aAct A v i = A i 0 + v 0 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    have hj : j = 0 := Fin.eq_zero j
    subst hj
    exact le_refl _
  · exact Finset.le_sup (f := fun j => A i j + v j) (Finset.mem_univ 0)

/-! ### arcticScalarProjection -/

/-- Native data of `arcticScalarProjection`: arctic linear functions for the four symbols. -/
abbrev arcticScalarProjectionData : Type := ArcticData

/-- Laws of `arcticScalarProjection`, pinned to A. Koprowski and J. Waldmann, *Max/plus tree
automata for termination of term rewriting*, Acta Cybernetica 19(2):357–392, 2009: arctic linear
functions (Definition 4.4), the domain `ℕ × A^d` with the pointwise orders `≫` and `≥`
(Section 6), and somewhere finiteness (Definition 6.1). Their Theorem 6.7 gives full termination
only for symbols of arity at most one, because no arctic linear function of two or more arguments
is strictly monotone (Section 7); Theorem 7.1 is the top-termination variant. -/
def arcticScalarProjectionLaws (M : arcticScalarProjectionData) : Prop := ArcticLaws M

/-- Acceptance for full termination: the interpretation decreases in `≫` along every contextual
instance of the duplicating rule under every valuation into `ℕ × A^d`. -/
def arcticScalarProjectionAccepts (M : arcticScalarProjectionData) : Prop :=
  DupCtxOrientedOn AFin M.interp arcLt

/-- Verdict: barrier. -/
def arcticScalarProjectionResult (M : arcticScalarProjectionData) : Prop :=
  ¬ arcticScalarProjectionAccepts M

theorem arcticScalarProjection_universal :
    ∀ M : arcticScalarProjectionData, arcticScalarProjectionLaws M →
      arcticScalarProjectionResult M :=
  fun M hM => arctic_context_barrier M hM

/-- Witness in dimension one: `wrap s y ↦ max (0 + s) (−∞ + y) = s`, `recur b s n ↦ 1 + s`,
`succ n ↦ n`; the wrapper erases its recursive result with a `−∞` entry. -/
abbrev arcticScalarProjectionWitness : arcticScalarProjectionData where
  d := 0
  zeroVec := aConst 0
  succMat := fun _ _ => ((0 : ℕ) : WithBot ℕ)
  succVec := fun _ => ⊥
  wrapLeft := fun _ _ => ((0 : ℕ) : WithBot ℕ)
  wrapRight := fun _ _ => ⊥
  wrapVec := fun _ => ⊥
  recurBase := fun _ _ => ⊥
  recurStep := fun _ _ => ((1 : ℕ) : WithBot ℕ)
  recurCounter := fun _ _ => ⊥
  recurVec := fun _ => ⊥

theorem arcticScalarProjectionWitness_laws :
    arcticScalarProjectionLaws arcticScalarProjectionWitness :=
  ⟨WithBot.coe_ne_bot, Or.inr WithBot.coe_ne_bot, Or.inr (Or.inl WithBot.coe_ne_bot),
    Or.inr (Or.inr (Or.inl WithBot.coe_ne_bot))⟩

theorem arcticScalarProjectionWitness_result :
    arcticScalarProjectionResult arcticScalarProjectionWitness :=
  arcticScalarProjection_universal _ arcticScalarProjectionWitness_laws

theorem arcW_wrap (s y : AVec 0) : arcticScalarProjectionWitness.interp.wrap s y 0 = s 0 := by
  show max (max (aAct (d := 0) (fun _ _ => ((0 : ℕ) : WithBot ℕ)) s 0)
    (aAct (d := 0) (fun _ _ => (⊥ : WithBot ℕ)) y 0)) (⊥ : WithBot ℕ) = s 0
  simp [aAct_one]

theorem arcW_recur (b s n : AVec 0) :
    arcticScalarProjectionWitness.interp.recur b s n 0 = 1 + s 0 := by
  show max (max (max (aAct (d := 0) (fun _ _ => (⊥ : WithBot ℕ)) b 0)
    (aAct (d := 0) (fun _ _ => ((1 : ℕ) : WithBot ℕ)) s 0))
    (aAct (d := 0) (fun _ _ => (⊥ : WithBot ℕ)) n 0)) (⊥ : WithBot ℕ) = 1 + s 0
  simp [aAct_one]

/-- The witness orients the root rule with `≫` on `ℕ × A^0`. -/
theorem arcticScalarProjectionWitness_root :
    DupOrientedOn AFin arcticScalarProjectionWitness.interp arcLt := by
  rw [dupOrientedOn_iff]
  intro b s n _ hs _ i
  have hi : i = 0 := Fin.eq_zero i
  subst hi
  left
  rw [arcW_wrap, arcW_recur]
  obtain ⟨k, hk⟩ := WithBot.ne_bot_iff_exists.1 hs
  rw [← hk]
  exact wb_coe_lt_one_add k

/-- Controls. Infinities: `−∞ ≫ −∞` holds coordinatewise, which is why the domain fixes a finite
first coordinate; the witness's wrapper uses a `−∞` entry to erase its recursive result.
Root/context distinction: the witness orients the root rule, and `arctic_context_barrier` excludes
contextual decrease. Non-erasure: `arctic_nonErasing_root_barrier` blocks the root rule for every
member whose wrapper keeps both arguments at the tracked coordinate. -/
theorem arcticScalarProjectionWitness_feature :
    arcLt (fun _ => (⊥ : WithBot ℕ) : AVec 0) (fun _ => ⊥) ∧
      arcticScalarProjectionWitness.wrapRight 0 0 = ⊥ ∧
      DupOrientedOn AFin arcticScalarProjectionWitness.interp arcLt ∧
      ¬ DupCtxOrientedOn AFin arcticScalarProjectionWitness.interp arcLt :=
  ⟨fun _ => Or.inr ⟨rfl, rfl⟩, rfl, arcticScalarProjectionWitness_root,
    arctic_context_barrier _ arcticScalarProjectionWitness_laws⟩

/-- Erasing both wrapper arguments and the wrapper constant violates somewhere finiteness. -/
theorem arcticScalarProjection_mutation :
    ¬ arcticScalarProjectionLaws
      { arcticScalarProjectionWitness with wrapLeft := fun _ _ => ⊥ } := by
  intro h
  unfold arcticScalarProjectionLaws at h
  rcases h.wrap_sf with h1 | h1 | h1 <;> exact h1 rfl

/-- Over any signature, extending a lawful arctic interpretation by arbitrary inert operations
does not decrease along every contextual step of the signature's rewrite relation. -/
theorem arcticScalarProjection_signature (ι : Type) (arity : ι → ℕ)
    (M : arcticScalarProjectionData) (ops : (f : ι) → (Fin (arity f) → AVec M.d) → AVec M.d)
    (hM : arcticScalarProjectionLaws M) :
    ¬ ∀ ρ : ℕ → AVec M.d, (∀ j, AFin (ρ j)) → ∀ a c : SigTerm ι arity ℕ, SigContextStep a c →
      arcLt (({ toInterpretation := M.interp, inertOp := ops } :
          SigInterpretation ι arity (AVec M.d)).eval ρ c)
        (({ toInterpretation := M.interp, inertOp := ops } :
          SigInterpretation ι arity (AVec M.d)).eval ρ a) := by
  intro h
  apply arcticScalarProjection_universal M hM
  intro ρ hρ a c hac
  have hs := h ρ hρ (embed a) (embed c) (embed_contextStep hac.contextStep)
  rwa [SigInterpretation.eval_embed, SigInterpretation.eval_embed] at hs

/-! ## Tropical matrix interpretations -/

/-- Tropical vectors of dimension `d + 1` over `ℕ ∪ {+∞}`; `⊤` is `+∞`. -/
abbrev TVec (d : ℕ) : Type := Fin (d + 1) → WithTop ℕ

/-- Tropical square matrices. -/
abbrev TMat (d : ℕ) : Type := Fin (d + 1) → Fin (d + 1) → WithTop ℕ

/-- Tropical matrix action `(A ⊗ v)ᵢ = min_j (A i j + v j)`. -/
def tAct {d : ℕ} (A : TMat d) (v : TVec d) : TVec d :=
  fun i => Finset.univ.inf (fun j => A i j + v j)

/-- The constant tropical vector with every entry `K`. -/
def tConst {d : ℕ} (K : ℕ) : TVec d := fun _ => (K : WithTop ℕ)

/-- Tropical linear functions for the four schema symbols. -/
structure TropicalData where
  d : ℕ
  zeroVec : TVec d
  succMat : TMat d
  succVec : TVec d
  wrapLeft : TMat d
  wrapRight : TMat d
  wrapVec : TVec d
  recurBase : TMat d
  recurStep : TMat d
  recurCounter : TMat d
  recurVec : TVec d

/-- `[f](v₁, …, vₙ) = M₁ ⊗ v₁ ⊕ ⋯ ⊕ Mₙ ⊗ vₙ ⊕ c` with `⊕ = min` and `⊗ = +`. -/
def TropicalData.interp (M : TropicalData) : Interpretation (TVec M.d) where
  zero := M.zeroVec
  succ n := fun i => min (tAct M.succMat n i) (M.succVec i)
  wrap s y := fun i => min (min (tAct M.wrapLeft s i) (tAct M.wrapRight y i)) (M.wrapVec i)
  recur b s n := fun i =>
    min (min (min (tAct M.recurBase b i) (tAct M.recurStep s i)) (tAct M.recurCounter n i))
      (M.recurVec i)

/-- The domain: the first coordinate is finite. -/
def TFin {d : ℕ} (v : TVec d) : Prop := v 0 ≠ ⊤

/-- The dual strict order, pointwise, smaller side first: every coordinate increases strictly or
both coordinates are `+∞`. -/
def tropLt {d : ℕ} (x y : TVec d) : Prop := ∀ i, x i < y i ∨ (x i = ⊤ ∧ y i = ⊤)

/-- Somewhere finiteness of every symbol and a finite first coordinate of the constant. -/
structure TropicalLaws (M : TropicalData) : Prop where
  zero_fin : M.zeroVec 0 ≠ ⊤
  succ_sf : M.succVec 0 ≠ ⊤ ∨ M.succMat 0 0 ≠ ⊤
  wrap_sf : M.wrapVec 0 ≠ ⊤ ∨ M.wrapLeft 0 0 ≠ ⊤ ∨ M.wrapRight 0 0 ≠ ⊤
  recur_sf : M.recurVec 0 ≠ ⊤ ∨ M.recurBase 0 0 ≠ ⊤ ∨ M.recurStep 0 0 ≠ ⊤ ∨
    M.recurCounter 0 0 ≠ ⊤

theorem tAct_le_diag {d : ℕ} (A : TMat d) (v : TVec d) : tAct A v 0 ≤ A 0 0 + v 0 :=
  Finset.inf_le (f := fun j => A 0 j + v j) (Finset.mem_univ 0)

theorem tfin_add {a b : WithTop ℕ} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a + b ≠ ⊤ := by
  obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.1 ha
  obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.1 hb
  rw [← WithTop.coe_add]
  exact WithTop.coe_ne_top

theorem wt_zero_le (x : WithTop ℕ) : ((0 : ℕ) : WithTop ℕ) ≤ x := by
  cases x with
  | top => exact le_top
  | coe n => exact WithTop.coe_le_coe.2 (Nat.zero_le n)

/-- A finite tropical value is below its successor. -/
theorem wt_coe_lt_one_add (k : ℕ) : (WithTop.some k : WithTop ℕ) < 1 + WithTop.some k := by
  have h := WithTop.coe_lt_coe.2 (show k < 1 + k by omega)
  rwa [WithTop.coe_add, WithTop.coe_one] at h

/-- Under the laws every term evaluates into the domain. -/
theorem tropical_eval_fin (M : TropicalData) (hM : TropicalLaws M) (ρ : ℕ → TVec M.d)
    (hρ : ∀ j, TFin (ρ j)) (t : FreeTerm ℕ) : TFin (M.interp.eval ρ t) := by
  induction t with
  | var x => exact hρ x
  | zero => exact hM.zero_fin
  | succ t ih =>
      show min (tAct M.succMat (M.interp.eval ρ t) 0) (M.succVec 0) ≠ ⊤
      rcases hM.succ_sf with h | h
      · exact ne_top_of_le_ne_top h (min_le_right _ _)
      · exact ne_top_of_le_ne_top (tfin_add h ih) (le_trans (min_le_left _ _) (tAct_le_diag _ _))
  | wrap s t ihs iht =>
      show min (min (tAct M.wrapLeft (M.interp.eval ρ s) 0)
        (tAct M.wrapRight (M.interp.eval ρ t) 0)) (M.wrapVec 0) ≠ ⊤
      rcases hM.wrap_sf with h | h | h
      · exact ne_top_of_le_ne_top h (min_le_right _ _)
      · exact ne_top_of_le_ne_top (tfin_add h ihs)
          (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (tAct_le_diag _ _)))
      · exact ne_top_of_le_ne_top (tfin_add h iht)
          (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (tAct_le_diag _ _)))
  | recur b s n ihb ihs ihn =>
      show min (min (min (tAct M.recurBase (M.interp.eval ρ b) 0)
        (tAct M.recurStep (M.interp.eval ρ s) 0)) (tAct M.recurCounter (M.interp.eval ρ n) 0))
        (M.recurVec 0) ≠ ⊤
      rcases hM.recur_sf with h | h | h | h
      · exact ne_top_of_le_ne_top h (min_le_right _ _)
      · exact ne_top_of_le_ne_top (tfin_add h ihb)
          (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
            (le_trans (min_le_left _ _) (tAct_le_diag _ _))))
      · exact ne_top_of_le_ne_top (tfin_add h ihs)
          (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
            (le_trans (min_le_right _ _) (tAct_le_diag _ _))))
      · exact ne_top_of_le_ne_top (tfin_add h ihn)
          (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (tAct_le_diag _ _)))

theorem min3_lt_right {α : Type} [LinearOrder α] {P Q Q' c : α}
    (h : min (min P Q') c < min (min P Q) c) : Q' < P := by
  by_contra hPQ
  push_neg at hPQ
  have : min (min P Q) c ≤ min (min P Q') c :=
    min_le_min (by rw [min_eq_left hPQ]; exact min_le_left P Q) le_rfl
  exact absurd h (not_lt.2 this)

theorem min3_lt_left {α : Type} [LinearOrder α] {P P' Q c : α}
    (h : min (min P' Q) c < min (min P Q) c) : P' < Q := by
  by_contra hQP
  push_neg at hQP
  have : min (min P Q) c ≤ min (min P' Q) c :=
    min_le_min (by rw [min_eq_right hQP]; exact min_le_right P Q) le_rfl
  exact absurd h (not_lt.2 this)

/-- Contextual masking by `min`: no tropical interpretation decreases along every wrapper-context
instance of the duplicating rule. With every argument at the zero vector, a strict step inside the
second wrapper argument forces `min_j W_r(0, j) < min_j W_l(0, j)`, and a strict step inside the
first argument forces the reverse. Consumed laws: all four finiteness laws, through
`tropical_eval_fin`. -/
theorem tropical_context_barrier (M : TropicalData) (hM : TropicalLaws M) :
    ¬ DupCtxOrientedOn TFin M.interp tropLt := by
  intro hacc
  have hz : TFin (tConst 0 : TVec M.d) := WithTop.coe_ne_top
  have mono : ∀ (A : TMat M.d) (v : TVec M.d), tAct A (tConst 0) 0 ≤ tAct A v 0 :=
    fun A v => Finset.le_inf (fun j _ => le_trans
      (Finset.inf_le (f := fun j => A 0 j + tConst 0 j) (Finset.mem_univ j))
      (add_le_add_left (wt_zero_le (v j)) _))
  have fin1 : M.interp.wrap (tConst 0) (M.interp.wrap (tConst 0)
      (M.interp.recur (tConst 0) (tConst 0) (tConst 0))) 0 ≠ ⊤ :=
    tropical_eval_fin M hM (fun _ => tConst 0) (fun _ => hz)
      (.wrap (.var 3) (.wrap (.var 1) (.recur (.var 0) (.var 1) (.var 2))))
  have fin2 : M.interp.wrap (M.interp.wrap (tConst 0)
      (M.interp.recur (tConst 0) (tConst 0) (tConst 0))) (tConst 0) 0 ≠ ⊤ :=
    tropical_eval_fin M hM (fun _ => tConst 0) (fun _ => hz)
      (.wrap (.wrap (.var 1) (.recur (.var 0) (.var 1) (.var 2))) (.var 3))
  have hk := dupCtx_wrap_instances TFin M.interp tropLt hacc (tConst 0) (tConst 0) (tConst 0)
    (tConst 0) hz hz hz hz
  have k1 : min (min (tAct M.wrapLeft (tConst 0) 0)
      (tAct M.wrapRight (M.interp.wrap (tConst 0)
        (M.interp.recur (tConst 0) (tConst 0) (tConst 0))) 0)) (M.wrapVec 0) <
      min (min (tAct M.wrapLeft (tConst 0) 0)
        (tAct M.wrapRight (M.interp.recur (tConst 0) (tConst 0) (M.interp.succ (tConst 0))) 0))
        (M.wrapVec 0) :=
    (hk.1 0).resolve_right (fun h => fin1 h.1)
  have k2 : min (min (tAct M.wrapLeft (M.interp.wrap (tConst 0)
        (M.interp.recur (tConst 0) (tConst 0) (tConst 0))) 0)
        (tAct M.wrapRight (tConst 0) 0)) (M.wrapVec 0) <
      min (min (tAct M.wrapLeft (M.interp.recur (tConst 0) (tConst 0) (M.interp.succ (tConst 0))) 0)
        (tAct M.wrapRight (tConst 0) 0)) (M.wrapVec 0) :=
    (hk.2 0).resolve_right (fun h => fin2 h.1)
  have h1 := lt_of_le_of_lt (mono M.wrapRight _) (min3_lt_right k1)
  have h2 := lt_of_le_of_lt (mono M.wrapLeft _) (min3_lt_left k2)
  exact lt_asymm h1 h2

/-- The action in dimension one. -/
theorem tAct_one (A : TMat 0) (v : TVec 0) (i : Fin (0 + 1)) : tAct A v i = A i 0 + v 0 := by
  apply le_antisymm
  · exact Finset.inf_le (f := fun j => A i j + v j) (Finset.mem_univ 0)
  · apply Finset.le_inf
    intro j _
    have hj : j = 0 := Fin.eq_zero j
    subst hj
    exact le_refl _

/-! ### tropicalScalarProjection -/

/-- Native data of `tropicalScalarProjection`: tropical linear functions for the four symbols. -/
abbrev tropicalScalarProjectionData : Type := TropicalData

/-- Laws of `tropicalScalarProjection`: the tropical semiring `(ℕ ∪ {+∞}, min, +, +∞, 0)`, the
min-plus dual of the arctic interpretations of A. Koprowski and J. Waldmann, *Max/plus tree
automata for termination of term rewriting*, Acta Cybernetica 19(2):357–392, 2009: their linear
functions (Definition 4.4) dualized to `min`, the dual strict order (`x ≫ y` iff `x > y` or
`x = y = +∞`), the domain with finite first coordinate, and somewhere finiteness as in their
Section 6. -/
def tropicalScalarProjectionLaws (M : tropicalScalarProjectionData) : Prop := TropicalLaws M

/-- Acceptance for full termination: decrease along every contextual instance of the duplicating
rule under every valuation into the domain. -/
def tropicalScalarProjectionAccepts (M : tropicalScalarProjectionData) : Prop :=
  DupCtxOrientedOn TFin M.interp tropLt

/-- Verdict: barrier. -/
def tropicalScalarProjectionResult (M : tropicalScalarProjectionData) : Prop :=
  ¬ tropicalScalarProjectionAccepts M

theorem tropicalScalarProjection_universal :
    ∀ M : tropicalScalarProjectionData, tropicalScalarProjectionLaws M →
      tropicalScalarProjectionResult M :=
  fun M hM => tropical_context_barrier M hM

/-- Witness in dimension one: `wrap s y ↦ min (+∞ + s) (0 + y) = y`, `recur b s n ↦ n`,
`succ n ↦ 1 + n`; the wrapper erases its payload with a `+∞` entry. -/
abbrev tropicalScalarProjectionWitness : tropicalScalarProjectionData where
  d := 0
  zeroVec := tConst 0
  succMat := fun _ _ => ((1 : ℕ) : WithTop ℕ)
  succVec := fun _ => ⊤
  wrapLeft := fun _ _ => ⊤
  wrapRight := fun _ _ => ((0 : ℕ) : WithTop ℕ)
  wrapVec := fun _ => ⊤
  recurBase := fun _ _ => ⊤
  recurStep := fun _ _ => ⊤
  recurCounter := fun _ _ => ((0 : ℕ) : WithTop ℕ)
  recurVec := fun _ => ⊤

theorem tropicalScalarProjectionWitness_laws :
    tropicalScalarProjectionLaws tropicalScalarProjectionWitness :=
  ⟨WithTop.coe_ne_top, Or.inr WithTop.coe_ne_top, Or.inr (Or.inr WithTop.coe_ne_top),
    Or.inr (Or.inr (Or.inr WithTop.coe_ne_top))⟩

theorem tropicalScalarProjectionWitness_result :
    tropicalScalarProjectionResult tropicalScalarProjectionWitness :=
  tropicalScalarProjection_universal _ tropicalScalarProjectionWitness_laws

theorem tropW_wrap (s y : TVec 0) : tropicalScalarProjectionWitness.interp.wrap s y 0 = y 0 := by
  show min (min (tAct (d := 0) (fun _ _ => (⊤ : WithTop ℕ)) s 0)
    (tAct (d := 0) (fun _ _ => ((0 : ℕ) : WithTop ℕ)) y 0)) (⊤ : WithTop ℕ) = y 0
  simp [tAct_one]

theorem tropW_recur (b s n : TVec 0) :
    tropicalScalarProjectionWitness.interp.recur b s n 0 = n 0 := by
  show min (min (min (tAct (d := 0) (fun _ _ => (⊤ : WithTop ℕ)) b 0)
    (tAct (d := 0) (fun _ _ => (⊤ : WithTop ℕ)) s 0))
    (tAct (d := 0) (fun _ _ => ((0 : ℕ) : WithTop ℕ)) n 0)) (⊤ : WithTop ℕ) = n 0
  simp [tAct_one]

theorem tropW_succ (n : TVec 0) : tropicalScalarProjectionWitness.interp.succ n 0 = 1 + n 0 := by
  show min (tAct (d := 0) (fun _ _ => ((1 : ℕ) : WithTop ℕ)) n 0) (⊤ : WithTop ℕ) = 1 + n 0
  simp [tAct_one]

/-- The witness orients the root rule: `n < 1 + n` at the finite first coordinate. -/
theorem tropicalScalarProjectionWitness_root :
    DupOrientedOn TFin tropicalScalarProjectionWitness.interp tropLt := by
  rw [dupOrientedOn_iff]
  intro b s n _ _ hn i
  have hi : i = 0 := Fin.eq_zero i
  subst hi
  left
  rw [tropW_wrap, tropW_recur, tropW_recur, tropW_succ]
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hn
  rw [← hk]
  exact wt_coe_lt_one_add k

/-- Controls: the existing root orienter and its contextual failure. -/
theorem tropicalScalarProjectionWitness_feature :
    DupOrientedOn TFin tropicalScalarProjectionWitness.interp tropLt ∧
      ¬ DupCtxOrientedOn TFin tropicalScalarProjectionWitness.interp tropLt ∧
      tropicalScalarProjectionWitness.wrapLeft 0 0 = ⊤ :=
  ⟨tropicalScalarProjectionWitness_root,
    tropical_context_barrier _ tropicalScalarProjectionWitness_laws, rfl⟩

/-- Erasing the wrapper's recursive result as well violates somewhere finiteness. -/
theorem tropicalScalarProjection_mutation :
    ¬ tropicalScalarProjectionLaws
      { tropicalScalarProjectionWitness with wrapRight := fun _ _ => ⊤ } := by
  intro h
  unfold tropicalScalarProjectionLaws at h
  rcases h.wrap_sf with h1 | h1 | h1 <;> exact h1 rfl

/-- Over any signature, extending a lawful tropical interpretation by arbitrary inert operations
does not decrease along every contextual step of the signature's rewrite relation. -/
theorem tropicalScalarProjection_signature (ι : Type) (arity : ι → ℕ)
    (M : tropicalScalarProjectionData) (ops : (f : ι) → (Fin (arity f) → TVec M.d) → TVec M.d)
    (hM : tropicalScalarProjectionLaws M) :
    ¬ ∀ ρ : ℕ → TVec M.d, (∀ j, TFin (ρ j)) → ∀ a c : SigTerm ι arity ℕ, SigContextStep a c →
      tropLt (({ toInterpretation := M.interp, inertOp := ops } :
          SigInterpretation ι arity (TVec M.d)).eval ρ c)
        (({ toInterpretation := M.interp, inertOp := ops } :
          SigInterpretation ι arity (TVec M.d)).eval ρ a) := by
  intro h
  apply tropicalScalarProjection_universal M hM
  intro ρ hρ a c hac
  have hs := h ρ hρ (embed a) (embed c) (embed_contextStep hac.contextStep)
  rwa [SigInterpretation.eval_embed, SigInterpretation.eval_embed] at hs

/-! ## Tuple interpretations -/

/-- Max-polynomials are monotone in every variable. -/
theorem MExpr.eval_mono {V : Type} (p : MExpr V) {x y : V → ℕ} (h : ∀ v, x v ≤ y v) :
    p.eval x ≤ p.eval y := by
  induction p with
  | const c => exact le_refl _
  | var v =>
      simp only [MExpr.eval]
      exact h v
  | add p q ihp ihq =>
      simp only [MExpr.eval]
      exact Nat.add_le_add ihp ihq
  | mul p q ihp ihq =>
      simp only [MExpr.eval]
      exact Nat.mul_le_mul ihp ihq
  | maxE p q ihp ihq =>
      simp only [MExpr.eval]
      exact max_le_max ihp ihq

/-- The weak order `≥≥` of Yamada 2022, Definition 5, stated with the smaller vector first. -/
abbrev vecLe {d : ℕ} (x y : NVec d) : Prop := ∀ i, x i ≤ y i

/-- `≫` is well founded: every step lowers the first component. -/
theorem vecLt_wf (d : ℕ) : WellFounded (fun x y : NVec d => vecLt x y) := by
  refine Subrelation.wf (r := InvImage (· < ·) (fun v : NVec d => v 0)) ?_
    (InvImage.wf _ Nat.lt_wfRel.wf)
  intro x y hxy
  exact hxy.1

/-- `≫` on pairs: strict in the first component and weak in the second. -/
theorem vecLt_pair {n : ℕ} (hn : n = 1) {x y : NVec n} (h0 : x 0 < y 0) (h1 : x 1 ≤ y 1) :
    vecLt x y := by
  subst hn
  refine And.intro h0 (fun i => ?_)
  fin_cases i
  · exact le_of_lt h0
  · exact h1

theorem args1_le {m : ℕ} {v w : NVec m} (h : vecLe v w) :
    ∀ p : Fin 1 × Fin (m + 1), ![v] p.1 p.2 ≤ ![w] p.1 p.2 := by
  rintro ⟨j, i⟩
  fin_cases j
  exact h i

theorem args2_le_left {m : ℕ} {v w : NVec m} (z : NVec m) (h : vecLe v w) :
    ∀ p : Fin 2 × Fin (m + 1), ![v, z] p.1 p.2 ≤ ![w, z] p.1 p.2 := by
  rintro ⟨j, i⟩
  fin_cases j
  · exact h i
  · exact le_refl _

theorem args2_le_right {m : ℕ} {v w : NVec m} (z : NVec m) (h : vecLe v w) :
    ∀ p : Fin 2 × Fin (m + 1), ![z, v] p.1 p.2 ≤ ![z, w] p.1 p.2 := by
  rintro ⟨j, i⟩
  fin_cases j
  · exact le_refl _
  · exact h i

theorem args3_le_base {m : ℕ} {v w : NVec m} (s n : NVec m) (h : vecLe v w) :
    ∀ p : Fin 3 × Fin (m + 1), ![v, s, n] p.1 p.2 ≤ ![w, s, n] p.1 p.2 := by
  rintro ⟨j, i⟩
  fin_cases j
  · exact h i
  · exact le_refl _
  · exact le_refl _

theorem args3_le_step {m : ℕ} {v w : NVec m} (b n : NVec m) (h : vecLe v w) :
    ∀ p : Fin 3 × Fin (m + 1), ![b, v, n] p.1 p.2 ≤ ![b, w, n] p.1 p.2 := by
  rintro ⟨j, i⟩
  fin_cases j
  · exact le_refl _
  · exact h i
  · exact le_refl _

theorem args3_le_counter {m : ℕ} {v w : NVec m} (b s : NVec m) (h : vecLe v w) :
    ∀ p : Fin 3 × Fin (m + 1), ![b, s, v] p.1 p.2 ≤ ![b, s, w] p.1 p.2 := by
  rintro ⟨j, i⟩
  fin_cases j
  · exact le_refl _
  · exact le_refl _
  · exact h i

/-- Tuple interpretations of dimension `m + 1` over `ℕ` for the four schema symbols. Component `c`
of the value of a symbol is a max-polynomial in the variables `(j, i)`, the `i`-th component of the
`j`-th argument: a deriver into the tuple algebra of `(ℕ, +, ·, max)`. -/
structure TupleData where
  m : ℕ
  zero : NVec m
  succ : Fin (m + 1) → MExpr (Fin 1 × Fin (m + 1))
  wrap : Fin (m + 1) → MExpr (Fin 2 × Fin (m + 1))
  recur : Fin (m + 1) → MExpr (Fin 3 × Fin (m + 1))

/-- The algebra over `ℕ^{m+1}` derived from the component expressions. -/
def TupleData.interp (M : TupleData) : Interpretation (NVec M.m) where
  zero := M.zero
  succ n := fun c => (M.succ c).eval (fun p => ![n] p.1 p.2)
  wrap s y := fun c => (M.wrap c).eval (fun p => ![s, y] p.1 p.2)
  recur b s n := fun c => (M.recur c).eval (fun p => ![b, s, n] p.1 p.2)

/-- The first-component strictness criterion (Yamada 2022, Theorem 9) for the four symbols:
lowering the first component of one argument lowers the first component of the value. -/
structure TupleLaws (M : TupleData) : Prop where
  succ_first : ∀ (n : NVec M.m) (a : ℕ), a < n 0 →
    M.interp.succ (Function.update n 0 a) 0 < M.interp.succ n 0
  wrap_first_left : ∀ (s y : NVec M.m) (a : ℕ), a < s 0 →
    M.interp.wrap (Function.update s 0 a) y 0 < M.interp.wrap s y 0
  wrap_first_right : ∀ (s y : NVec M.m) (a : ℕ), a < y 0 →
    M.interp.wrap s (Function.update y 0 a) 0 < M.interp.wrap s y 0
  recur_first_base : ∀ (b s n : NVec M.m) (a : ℕ), a < b 0 →
    M.interp.recur (Function.update b 0 a) s n 0 < M.interp.recur b s n 0
  recur_first_step : ∀ (b s n : NVec M.m) (a : ℕ), a < s 0 →
    M.interp.recur b (Function.update s 0 a) n 0 < M.interp.recur b s n 0
  recur_first_counter : ∀ (b s n : NVec M.m) (a : ℕ), a < n 0 →
    M.interp.recur b s (Function.update n 0 a) 0 < M.interp.recur b s n 0

/-- Theorem 9 of Yamada 2022 at one argument position: a monotone vector map whose first component
drops with the first component of its argument is strictly monotone for `≫`. -/
theorem tuple_arg_strict {m : ℕ} (G : NVec m → NVec m)
    (hmono : ∀ v w : NVec m, vecLe v w → vecLe (G v) (G w))
    (hfirst : ∀ (v : NVec m) (a : ℕ), a < v 0 → G (Function.update v 0 a) 0 < G v 0)
    {x y : NVec m} (h : vecLt x y) : vecLt (G x) (G y) := by
  have hle : vecLe x (Function.update y 0 (x 0)) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      simp
    · rw [Function.update_apply, if_neg hi]
      exact h.2 i
  exact And.intro (lt_of_le_of_lt (hmono _ _ hle 0) (hfirst y (x 0) h.1)) (hmono x y h.2)

/-- Every tuple interpretation is weakly monotone for `≥≥` (Yamada 2022, Lemma 5). -/
theorem tuple_weakContextLaws (M : TupleData) : WeakContextLaws M.interp vecLe where
  succ := fun h c => MExpr.eval_mono (M.succ c) (args1_le h)
  wrapLeft := fun z h c => MExpr.eval_mono (M.wrap c) (args2_le_left z h)
  wrapRight := fun z {_ _} h c => MExpr.eval_mono (M.wrap c) (args2_le_right z h)
  recurBase := fun s n h c => MExpr.eval_mono (M.recur c) (args3_le_base s n h)
  recurStep := fun b {_ _} n h c => MExpr.eval_mono (M.recur c) (args3_le_step b n h)
  recurCounter := fun b s {_ _} h c => MExpr.eval_mono (M.recur c) (args3_le_counter b s h)

/-- A lawful tuple interpretation is strictly monotone for `≫` (Yamada 2022, Theorem 9). -/
theorem tuple_strictContextLaws (M : TupleData) (hM : TupleLaws M) :
    StrictContextLaws M.interp vecLt where
  succ := fun h => tuple_arg_strict (fun v => M.interp.succ v)
    (fun _ _ hvw => (tuple_weakContextLaws M).succ hvw) hM.succ_first h
  wrapLeft := fun z h => tuple_arg_strict (fun v => M.interp.wrap v z)
    (fun _ _ hvw => (tuple_weakContextLaws M).wrapLeft z hvw)
    (fun v a ha => hM.wrap_first_left v z a ha) h
  wrapRight := fun z {_ _} h => tuple_arg_strict (fun v => M.interp.wrap z v)
    (fun _ _ hvw => (tuple_weakContextLaws M).wrapRight z hvw)
    (fun v a ha => hM.wrap_first_right z v a ha) h
  recurBase := fun s n h => tuple_arg_strict (fun v => M.interp.recur v s n)
    (fun _ _ hvw => (tuple_weakContextLaws M).recurBase s n hvw)
    (fun v a ha => hM.recur_first_base v s n a ha) h
  recurStep := fun b {_ _} n h => tuple_arg_strict (fun v => M.interp.recur b v n)
    (fun _ _ hvw => (tuple_weakContextLaws M).recurStep b n hvw)
    (fun v a ha => hM.recur_first_step b v n a ha) h
  recurCounter := fun b s {_ _} h => tuple_arg_strict (fun v => M.interp.recur b s v)
    (fun _ _ hvw => (tuple_weakContextLaws M).recurCounter b s hvw)
    (fun v a ha => hM.recur_first_counter b s v a ha) h

/-- A lawful wrapper keeps both first components: `s₀ + y₀ ≤ wrap(s, y)₀`. -/
theorem tuple_wrap_ge (M : TupleData) (hM : TupleLaws M) (s y : NVec M.m) :
    s 0 + y 0 ≤ M.interp.wrap s y 0 := by
  have hf : M.interp.wrap (Function.update s 0 0) y 0 + s 0 ≤
      M.interp.wrap (Function.update s 0 (s 0)) y 0 :=
    nat_strict_ge (f := fun a => M.interp.wrap (Function.update s 0 a) y 0)
      (fun a a' h => by
        have := hM.wrap_first_left (Function.update s 0 a') y a
          (by rw [Function.update_apply, if_pos rfl]; exact h)
        rw [Function.update_idem] at this
        exact this) (s 0)
  have hg : M.interp.wrap (Function.update s 0 0) (Function.update y 0 0) 0 + y 0 ≤
      M.interp.wrap (Function.update s 0 0) (Function.update y 0 (y 0)) 0 :=
    nat_strict_ge (f := fun a => M.interp.wrap (Function.update s 0 0) (Function.update y 0 a) 0)
      (fun a a' h => by
        have := hM.wrap_first_right (Function.update s 0 0) (Function.update y 0 a') a
          (by rw [Function.update_apply, if_pos rfl]; exact h)
        rw [Function.update_idem] at this
        exact this) (y 0)
  rw [Function.update_eq_self] at hf hg
  omega

/-- Inert symbols over natural vectors: `f(v₁, …, vₖ) = v₁ + ⋯ + vₖ + 1` componentwise. -/
def vecSigExtension {ι : Type} (arity : ι → ℕ) {d : ℕ} (I : Interpretation (NVec d)) :
    SigInterpretation ι arity (NVec d) :=
  { toInterpretation := I, inertOp := fun _ args c => (∑ j, args j c) + 1 }

/-- The componentwise sum extension keeps strict monotonicity for `≫`. -/
theorem vecSigExtension_strict {ι : Type} (arity : ι → ℕ) {d : ℕ} (I : Interpretation (NVec d))
    (h : StrictContextLaws I vecLt) : SigStrictContextLaws (vecSigExtension arity I) vecLt where
  toStrictContextLaws := h
  inertArg := by
    intro f args i x y hxy
    have hle : ∀ c, ∀ j ∈ (Finset.univ : Finset (Fin (arity f))),
        Function.update args i x j c ≤ Function.update args i y j c := by
      intro c j _
      by_cases hj : j = i
      · subst hj
        simpa [Function.update_apply] using hxy.2 c
      · simp [hj]
    refine And.intro ?_ (fun c => ?_)
    · show (∑ j, Function.update args i x j 0) + 1 < (∑ j, Function.update args i y j 0) + 1
      have : ∑ j, Function.update args i x j 0 < ∑ j, Function.update args i y j 0 :=
        Finset.sum_lt_sum (hle 0)
          ⟨i, Finset.mem_univ i, by simpa [Function.update_apply] using hxy.1⟩
      omega
    · show (∑ j, Function.update args i x j c) + 1 ≤ (∑ j, Function.update args i y j c) + 1
      have : ∑ j, Function.update args i x j c ≤ ∑ j, Function.update args i y j c :=
        Finset.sum_le_sum (hle c)
      omega

/-! ### tupleInterpretationStrictS -/

/-- Native data of `tupleInterpretationStrictS`: a tuple dimension and max-polynomial component
expressions for the four symbols. -/
abbrev tupleInterpretationStrictSData : Type := TupleData

/-- Laws of `tupleInterpretationStrictS`, pinned to A. Yamada, *Tuple interpretations for termination
of term rewriting*, Journal of Automated Reasoning 66(4):667–688, 2022: the order pair `⟨≥≥, ≫⟩` on
`ℕ^{m+1}` (Definition 5: `≫` strict in the first component and weak in the others), the tuple
algebra of a deriver (Definition 6, weakly monotone by Lemma 5), and the first-component criterion
of Theorem 9, which makes the algebra strictly monotone in the sense of Definition 7. -/
def tupleInterpretationStrictSLaws (M : tupleInterpretationStrictSData) : Prop := TupleLaws M

/-- Acceptance: the tuple algebra orients both free root rules with `≫`. -/
def tupleInterpretationStrictSAccepts (M : tupleInterpretationStrictSData) : Prop :=
  RootRuleOrients M.interp vecLt

/-- Verdict: escape. -/
def tupleInterpretationStrictSResult (M : tupleInterpretationStrictSData) : Prop :=
  tupleInterpretationStrictSAccepts M ∧ CertifiesFreeTermination M.interp vecLt

/-- Soundness (Yamada 2022, Theorems 6, 7 and 9): `≫` is well founded, a lawful tuple algebra is
strictly monotone, and orientation of both root rules certifies termination of the free contextual
relation. -/
theorem tupleInterpretationStrictS_sound (M : tupleInterpretationStrictSData)
    (hM : tupleInterpretationStrictSLaws M) (hA : tupleInterpretationStrictSAccepts M) :
    CertifiesFreeTermination M.interp vecLt :=
  certifiesFreeTermination_of_laws M.interp vecLt (vecLt_wf M.m) (tuple_strictContextLaws M hM) hA

/-- The scalar consequence of `≫`: an accepted tuple algebra orients the rule in its first
component, the coordinate that P3 tracks. -/
theorem tupleInterpretationStrictS_firstComponent (M : tupleInterpretationStrictSData)
    (hA : tupleInterpretationStrictSAccepts M) (b s n : NVec M.m) :
    M.interp.wrap s (M.interp.recur b s n) 0 < M.interp.recur b s (M.interp.succ n) 0 :=
  ((show RootRuleOrients M.interp vecLt from hA).recurSucc b s n).1

/-- P3.2 on the first component: a lawful tuple algebra whose recursor has a multiplication-free
first component (affine, the matrix case, or max-plus) lies in the barrier cell at `b = n = 0`.
The payload enters the wrapper's first component with coefficient at least one (Theorem 9), while
the counter gain of a multiplication-free recursor at a fixed counter is bounded. -/
theorem tupleInterpretationStrictS_affineFirst_barrier (M : TupleData) (hM : TupleLaws M)
    (hmf : (M.recur 0).MulFree) : ¬ DupOriented M.interp vecLt := by
  refine not_dupOriented_of_barrierCell M.interp vecLt (fun v => v 0) (fun h => h.1)
    (fun _ => 0) (fun _ => 0) ?_ ?_
  · intro K
    refine ⟨fun _ => K + 1, ?_⟩
    have h : K + 1 + M.interp.recur (fun _ => 0) (fun _ => K + 1) (fun _ => 0) 0 ≤
        M.interp.wrap (fun _ => K + 1) (M.interp.recur (fun _ => 0) (fun _ => K + 1) (fun _ => 0))
          0 :=
      tuple_wrap_ge M hM (fun _ => K + 1) (M.interp.recur (fun _ => 0) (fun _ => K + 1) (fun _ => 0))
    show M.interp.recur (fun _ => 0) (fun _ => K + 1) (fun _ => 0) 0 + K <
      M.interp.wrap (fun _ => K + 1) (M.interp.recur (fun _ => 0) (fun _ => K + 1) (fun _ => 0)) 0
    omega
  · refine ⟨(M.recur 0).size * ∑ i, M.interp.succ (fun _ => 0) i, fun s => ?_⟩
    have hd : ∀ i, M.interp.succ (fun _ => 0) i ≤ ∑ j, M.interp.succ (fun _ => 0) j :=
      fun i => Finset.single_le_sum (f := fun j => M.interp.succ (fun _ => 0) j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    show M.interp.recur (fun _ => 0) s (M.interp.succ (fun _ => 0)) 0 ≤
      M.interp.recur (fun _ => 0) s (fun _ => 0) 0 +
        (M.recur 0).size * ∑ i, M.interp.succ (fun _ => 0) i
    exact MExpr.eval_le_of_mulFree (M.recur 0) hmf _ _ _ (by
      rintro ⟨j, i⟩
      fin_cases j
      · exact Nat.le_add_right _ _
      · exact Nat.le_add_right _ _
      · exact le_trans (hd i) (Nat.le_add_left _ _))

/-- Witness, a cost–size pair interpretation with a cross-coupled cost: `zero ↦ (0, 0)`,
`succ n ↦ (n₀ + 1, n₁ + 1)`, `wrap s y ↦ (s₀ + y₀ + 1, s₁ + y₁ + 1)`,
`recur b s n ↦ (b₀ + n₀ + (n₁ + 1)(s₀ + 1), b₁ + (n₁ + 1)(s₁ + 1))`. The cost of the recursor
multiplies the size of the counter by the cost of the step. -/
abbrev tupleInterpretationStrictSWitness : tupleInterpretationStrictSData where
  m := 1
  zero := fun _ => 0
  succ := ![.add (.var (0, 0)) (.const 1), .add (.var (0, 1)) (.const 1)]
  wrap := ![.add (.add (.var (0, 0)) (.var (1, 0))) (.const 1),
    .add (.add (.var (0, 1)) (.var (1, 1))) (.const 1)]
  recur := ![.add (.add (.var (0, 0)) (.var (2, 0)))
      (.mul (.add (.var (2, 1)) (.const 1)) (.add (.var (1, 0)) (.const 1))),
    .add (.var (0, 1)) (.mul (.add (.var (2, 1)) (.const 1)) (.add (.var (1, 1)) (.const 1)))]

theorem tupW_zero (i : Fin (tupleInterpretationStrictSWitness.m + 1)) :
    tupleInterpretationStrictSWitness.interp.zero i = 0 := rfl

theorem tupW_succ0 (n : NVec tupleInterpretationStrictSWitness.m) :
    tupleInterpretationStrictSWitness.interp.succ n 0 = n 0 + 1 := rfl

theorem tupW_succ1 (n : NVec tupleInterpretationStrictSWitness.m) :
    tupleInterpretationStrictSWitness.interp.succ n 1 = n 1 + 1 := rfl

theorem tupW_wrap0 (s y : NVec tupleInterpretationStrictSWitness.m) :
    tupleInterpretationStrictSWitness.interp.wrap s y 0 = s 0 + y 0 + 1 := rfl

theorem tupW_wrap1 (s y : NVec tupleInterpretationStrictSWitness.m) :
    tupleInterpretationStrictSWitness.interp.wrap s y 1 = s 1 + y 1 + 1 := rfl

theorem tupW_recur0 (b s n : NVec tupleInterpretationStrictSWitness.m) :
    tupleInterpretationStrictSWitness.interp.recur b s n 0 =
      b 0 + n 0 + (n 1 + 1) * (s 0 + 1) := rfl

theorem tupW_recur1 (b s n : NVec tupleInterpretationStrictSWitness.m) :
    tupleInterpretationStrictSWitness.interp.recur b s n 1 = b 1 + (n 1 + 1) * (s 1 + 1) := rfl

/-- The size component of the duplicating rule is an equality. -/
theorem tupW_dup_second (b s n : NVec tupleInterpretationStrictSWitness.m) :
    tupleInterpretationStrictSWitness.interp.wrap s
        (tupleInterpretationStrictSWitness.interp.recur b s n) 1 =
      tupleInterpretationStrictSWitness.interp.recur b s
        (tupleInterpretationStrictSWitness.interp.succ n) 1 := by
  rw [tupW_wrap1, tupW_recur1, tupW_recur1, tupW_succ1]
  ring

theorem tupleInterpretationStrictSWitness_laws :
    tupleInterpretationStrictSLaws tupleInterpretationStrictSWitness := by
  unfold tupleInterpretationStrictSLaws
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n a ha
    rw [tupW_succ0, tupW_succ0]
    have h0 : Function.update n 0 a 0 = a := by rw [Function.update_apply, if_pos rfl]
    omega
  · intro s y a ha
    rw [tupW_wrap0, tupW_wrap0]
    have h0 : Function.update s 0 a 0 = a := by rw [Function.update_apply, if_pos rfl]
    omega
  · intro s y a ha
    rw [tupW_wrap0, tupW_wrap0]
    have h0 : Function.update y 0 a 0 = a := by rw [Function.update_apply, if_pos rfl]
    omega
  · intro b s n a ha
    rw [tupW_recur0, tupW_recur0]
    have h0 : Function.update b 0 a 0 = a := by rw [Function.update_apply, if_pos rfl]
    omega
  · intro b s n a ha
    rw [tupW_recur0, tupW_recur0]
    have h0 : Function.update s 0 a 0 = a := by rw [Function.update_apply, if_pos rfl]
    rw [h0]
    nlinarith [Nat.mul_le_mul (le_refl (n 1 + 1)) (show a + 1 ≤ s 0 by omega)]
  · intro b s n a ha
    rw [tupW_recur0, tupW_recur0]
    have h0 : Function.update n 0 a 0 = a := by rw [Function.update_apply, if_pos rfl]
    have h1 : Function.update n 0 a 1 = n 1 := by
      rw [Function.update_apply, if_neg (by decide)]
    rw [h0, h1]
    omega

/-- The witness orients both free root rules with `≫`. -/
theorem tupW_root : RootRuleOrients tupleInterpretationStrictSWitness.interp vecLt where
  recurZero := by
    intro b s
    refine vecLt_pair rfl ?_ ?_
    · rw [tupW_recur0, tupW_zero, tupW_zero]
      nlinarith
    · rw [tupW_recur1, tupW_zero]
      nlinarith
  recurSucc := by
    intro b s n
    refine vecLt_pair rfl ?_ ?_
    · rw [tupW_wrap0, tupW_recur0, tupW_recur0, tupW_succ0, tupW_succ1]
      nlinarith
    · rw [tupW_dup_second]

theorem tupleInterpretationStrictSWitness_result :
    tupleInterpretationStrictSResult tupleInterpretationStrictSWitness :=
  And.intro tupW_root
    (tupleInterpretationStrictS_sound _ tupleInterpretationStrictSWitness_laws tupW_root)

/-- Lexicographic comparison of pairs, the alternate tuple order. -/
def lexLtPair {n : ℕ} (x y : NVec n) : Prop := x 0 < y 0 ∨ (x 0 = y 0 ∧ x 1 < y 1)

/-- Controls. The escape is non-affine: the first component of the recursor multiplies. It is
cross-coupled: the recursor's cost reads the counter's size. The size component of the rule is
only an equality, so the pointwise strict order does not orient the witness and `≫` is needed.
The lexicographic order is not preserved by the witness's recursor, so the lexicographic order
does not give a monotone algebra here. -/
theorem tupleInterpretationStrictSWitness_feature :
    ¬ (tupleInterpretationStrictSWitness.recur 0).MulFree ∧
      (∀ b s n : NVec tupleInterpretationStrictSWitness.m,
        tupleInterpretationStrictSWitness.interp.wrap s
            (tupleInterpretationStrictSWitness.interp.recur b s n) 1 =
          tupleInterpretationStrictSWitness.interp.recur b s
            (tupleInterpretationStrictSWitness.interp.succ n) 1) ∧
      lexLtPair (n := tupleInterpretationStrictSWitness.m) ![0, 5] ![1, 0] ∧
      ¬ lexLtPair
        (tupleInterpretationStrictSWitness.interp.recur (fun _ => 0) (fun _ => 0) ![0, 5])
        (tupleInterpretationStrictSWitness.interp.recur (fun _ => 0) (fun _ => 0) ![1, 0]) := by
  refine ⟨fun h => h.2, tupW_dup_second, Or.inl (by decide), ?_⟩
  unfold lexLtPair
  decide

/-- Removing the coupling from the first component of the recursor, `(b₀ + n₀ + s₀ + 1, …)`, loses
the orientation: at `b = s = n = 0` both sides have first component `2`. -/
theorem tupleInterpretationStrictS_mutation :
    ¬ tupleInterpretationStrictSResult
      { tupleInterpretationStrictSWitness with
        recur := ![.add (.add (.add (.var (0, 0)) (.var (2, 0))) (.var (1, 0))) (.const 1),
          .add (.var (0, 1))
            (.mul (.add (.var (2, 1)) (.const 1)) (.add (.var (1, 1)) (.const 1)))] } := by
  rintro ⟨hA, _⟩
  have h := ((show RootRuleOrients _ vecLt from hA).recurSucc (fun _ => 0) (fun _ => 0)
    (fun _ => 0)).1
  exact absurd h (by decide)

/-- Over any signature, a lawful accepting tuple algebra extended by componentwise sums on the
inert symbols proves termination of the full contextual relation. -/
theorem tupleInterpretationStrictS_signature (ι : Type) (arity : ι → ℕ) (ν : Type)
    (M : tupleInterpretationStrictSData) (hM : tupleInterpretationStrictSLaws M)
    (hA : tupleInterpretationStrictSAccepts M) :
    WellFounded (fun u t : SigTerm ι arity ν => SigContextStep t u) :=
  sig_contextStep_reverse_wellFounded (I := vecSigExtension arity M.interp) hA
    (vecSigExtension_strict arity M.interp (tuple_strictContextLaws M hM)) (vecLt_wf M.m)
    (fun _ => M.interp.zero)

/-! ### strictMonotoneAlgebraArchimedean -/

/-- Native data of `strictMonotoneAlgebraArchimedean`: an algebra on the natural numbers for the
four schema symbols. -/
abbrev strictMonotoneAlgebraArchimedeanData : Type := Interpretation ℕ

/-- Laws of `strictMonotoneAlgebraArchimedean`, pinned to A. Yamada, *Tuple interpretations for
termination of term rewriting*, Journal of Automated Reasoning 66(4):667–688, 2022, Definition 7
(a strictly monotone algebra is monotone for both `≥` and `>`; on `ℕ` strict monotonicity gives
weak monotonicity) with the well-founded order pair `(ℕ, ≥, >)` of Definition 1, the setting of
Theorem 7 (a TRS terminates iff a strictly monotone well-founded algebra orients it). The carrier is
Archimedean: every natural number is a payload value, which is the unbounded-payload premise of
P3.1. -/
def strictMonotoneAlgebraArchimedeanLaws (M : strictMonotoneAlgebraArchimedeanData) : Prop :=
  StrictContextLaws M (fun x y : ℕ => x < y)

/-- Acceptance: the algebra orients both free root rules. -/
def strictMonotoneAlgebraArchimedeanAccepts (M : strictMonotoneAlgebraArchimedeanData) : Prop :=
  RootRuleOrients M (fun x y : ℕ => x < y)

/-- Verdict: escape. -/
def strictMonotoneAlgebraArchimedeanResult (M : strictMonotoneAlgebraArchimedeanData) : Prop :=
  strictMonotoneAlgebraArchimedeanAccepts M ∧ CertifiesFreeTermination M (fun x y : ℕ => x < y)

/-- Soundness (Theorem 7, "if" direction). -/
theorem strictMonotoneAlgebraArchimedean_sound (M : strictMonotoneAlgebraArchimedeanData)
    (hM : strictMonotoneAlgebraArchimedeanLaws M) (hA : strictMonotoneAlgebraArchimedeanAccepts M) :
    CertifiesFreeTermination M (fun x y : ℕ => x < y) :=
  certifiesFreeTermination_of_laws M _ Nat.lt_wfRel.wf hM hA

/-- P3.1 on the uniform-gain subclass: a strictly monotone wrapper retains both arguments, the
Archimedean carrier has unbounded payloads, so a recursor whose counter gain is bounded by one
constant `g` for all arguments orients nothing. -/
theorem strictMonotoneAlgebraArchimedean_uniformGain_barrier
    (M : strictMonotoneAlgebraArchimedeanData) (hM : strictMonotoneAlgebraArchimedeanLaws M)
    (g : ℕ) (hgain : ∀ b s n : ℕ, M.recur b s (M.succ n) ≤ M.recur b s n + g) :
    ¬ strictMonotoneAlgebraArchimedeanAccepts M := by
  intro hA
  exact no_orientation_of_retention_bounded_gain_unbounded_payload (S := valueSchema M) id 0 g
    (fun (x y : ℕ) => by
      show 0 + x + y ≤ M.wrap x y
      have := wrap_ge_of_strict hM x y
      omega)
    hgain (fun K => ⟨K, le_refl K⟩)
    (fun b s n => (show RootRuleOrients M (fun x y : ℕ => x < y) from hA).recurSucc b s n)

/-- Witness: the coupled polynomial `zero ↦ 0`, `succ n ↦ n + 1`, `wrap s y ↦ s + y + 1`,
`recur b s n ↦ (n + 1)(s + b + 2)` of P3.4. -/
abbrev strictMonotoneAlgebraArchimedeanWitness : strictMonotoneAlgebraArchimedeanData :=
  FreePolynomialTermination.coupledInterpretation 1 2

theorem strictMonotoneAlgebraArchimedeanWitness_laws :
    strictMonotoneAlgebraArchimedeanLaws strictMonotoneAlgebraArchimedeanWitness :=
  FreePolynomialTermination.coupled_strictContextLaws (le_refl 1) (le_refl 2)

theorem strictMonotoneAlgebraArchimedeanWitness_accepts :
    strictMonotoneAlgebraArchimedeanAccepts strictMonotoneAlgebraArchimedeanWitness :=
  FreePolynomialTermination.coupled_rootRuleOrients (le_refl 1) (le_refl 2)

theorem strictMonotoneAlgebraArchimedeanWitness_result :
    strictMonotoneAlgebraArchimedeanResult strictMonotoneAlgebraArchimedeanWitness :=
  And.intro strictMonotoneAlgebraArchimedeanWitness_accepts
    (strictMonotoneAlgebraArchimedean_sound _ strictMonotoneAlgebraArchimedeanWitness_laws
      strictMonotoneAlgebraArchimedeanWitness_accepts)

/-- Controls. The escape is a strictly monotone coupled polynomial; its counter gain is not
uniformly bounded (else the P3.1 subclass barrier applies); P3.1 forces the gain above the payload
plus the wrapper cost at every instance. -/
theorem strictMonotoneAlgebraArchimedeanWitness_feature :
    (∀ b s n : ℕ, strictMonotoneAlgebraArchimedeanWitness.recur b s n = (n + 1) * (1 * s + b + 2)) ∧
      (¬ ∃ g : ℕ, ∀ b s n : ℕ,
        strictMonotoneAlgebraArchimedeanWitness.recur b s
            (strictMonotoneAlgebraArchimedeanWitness.succ n) ≤
          strictMonotoneAlgebraArchimedeanWitness.recur b s n + g) ∧
      ∀ b s n : ℕ, ((s : ℕ) : ℤ) + ((1 : ℕ) : ℤ) <
        counterGainZ (S := valueSchema strictMonotoneAlgebraArchimedeanWitness) id b s n :=
  ⟨fun _ _ _ => rfl,
    fun ⟨g, hg⟩ => strictMonotoneAlgebraArchimedean_uniformGain_barrier _
      strictMonotoneAlgebraArchimedeanWitness_laws g hg
      strictMonotoneAlgebraArchimedeanWitness_accepts,
    fun b s n => nat_escape_coupling strictMonotoneAlgebraArchimedeanWitness 1
      (fun x y => by show 1 + x + y ≤ x + y + 1; omega)
      strictMonotoneAlgebraArchimedeanWitness_accepts b s n⟩

/-- An additive recursor `b + s + n + 1` keeps the laws and has gain one, so the result fails. -/
theorem strictMonotoneAlgebraArchimedean_mutation :
    strictMonotoneAlgebraArchimedeanLaws
        { strictMonotoneAlgebraArchimedeanWitness with recur := fun b s n => b + s + n + 1 } ∧
      ¬ strictMonotoneAlgebraArchimedeanResult
        { strictMonotoneAlgebraArchimedeanWitness with recur := fun b s n => b + s + n + 1 } := by
  have hL : strictMonotoneAlgebraArchimedeanLaws
      { strictMonotoneAlgebraArchimedeanWitness with recur := fun b s n => b + s + n + 1 } := by
    unfold strictMonotoneAlgebraArchimedeanLaws
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x y h
      show x + 1 < y + 1
      omega
    · intro x y z h
      show x + z + 1 < y + z + 1
      omega
    · intro z x y h
      show z + x + 1 < z + y + 1
      omega
    · intro x y s n h
      show x + s + n + 1 < y + s + n + 1
      omega
    · intro b x y n h
      show b + x + n + 1 < b + y + n + 1
      omega
    · intro b s x y h
      show b + s + x + 1 < b + s + y + 1
      omega
  refine ⟨hL, fun hR => ?_⟩
  exact strictMonotoneAlgebraArchimedean_uniformGain_barrier _ hL 1
    (fun b s n => by show b + s + (n + 1) + 1 ≤ b + s + n + 1 + 1; omega) hR.1

/-- Over any signature, a lawful accepting member extended by `1 + sum` proves termination. -/
theorem strictMonotoneAlgebraArchimedean_signature (ι : Type) (arity : ι → ℕ) (ν : Type)
    (M : strictMonotoneAlgebraArchimedeanData) (hM : strictMonotoneAlgebraArchimedeanLaws M)
    (hA : strictMonotoneAlgebraArchimedeanAccepts M) :
    WellFounded (fun u t : SigTerm ι arity ν => SigContextStep t u) :=
  nat_signature_termination arity ν M hM hA

/-! ## Extended monotone algebras -/

/-- An algebra on natural vectors with two relations, each stated with the smaller value first:
`strict x y` is `y > x` and `weak x y` is `y ≳ x`. -/
structure EMAData where
  d : ℕ
  interp : Interpretation (NVec d)
  strict : NVec d → NVec d → Prop
  weak : NVec d → NVec d → Prop

/-- Endrullis, Waldmann and Zantema 2008, Definition 1: `>` well founded, `> · ≳ ⊆ >`, every
operation monotone for `≳` and, for an extended monotone algebra, for `>`. -/
structure EMALaws (M : EMAData) : Prop where
  strict_wf : WellFounded M.strict
  compat : ∀ x y z : NVec M.d, M.strict y z → M.weak x y → M.strict x z
  weak_mono : WeakContextLaws M.interp M.weak
  strict_mono : StrictContextLaws M.interp M.strict

/-! ### extendedMonotoneAlgebra -/

/-- Native data of `extendedMonotoneAlgebra`: carrier dimension, operations and both relations. -/
abbrev extendedMonotoneAlgebraData : Type := EMAData

/-- Laws of `extendedMonotoneAlgebra`, pinned to J. Endrullis, J. Waldmann and H. Zantema, *Matrix
interpretations for proving termination of term rewriting*, Journal of Automated Reasoning
40(2–3):195–220, 2008, Definition 1 (weakly and extended monotone algebras); Theorem 2 part 1 is
the soundness theorem and Theorem 3 part 1 the rule-removal form. -/
def extendedMonotoneAlgebraLaws (M : extendedMonotoneAlgebraData) : Prop := EMALaws M

/-- Acceptance (Theorem 2 part 1 with the free two-rule system as `R` and `S = ∅`): both root rules
decrease in `>` under every assignment. -/
def extendedMonotoneAlgebraAccepts (M : extendedMonotoneAlgebraData) : Prop :=
  RootRuleOrients M.interp M.strict

/-- Verdict: escape. -/
def extendedMonotoneAlgebraResult (M : extendedMonotoneAlgebraData) : Prop :=
  extendedMonotoneAlgebraAccepts M ∧ CertifiesFreeTermination M.interp M.strict

/-- Soundness (Theorem 2 part 1, "if" direction). -/
theorem extendedMonotoneAlgebra_sound (M : extendedMonotoneAlgebraData)
    (hM : extendedMonotoneAlgebraLaws M) (hA : extendedMonotoneAlgebraAccepts M) :
    CertifiesFreeTermination M.interp M.strict :=
  certifiesFreeTermination_of_laws M.interp M.strict (show EMALaws M from hM).strict_wf
    (show EMALaws M from hM).strict_mono hA

/-- P3.2 on the bounded-gain subclass: if every strict comparison lowers a natural coordinate `T`
and the member lies in the barrier cell for `T` at some `b, n`, the member does not accept. -/
theorem extendedMonotoneAlgebra_boundedGain_barrier (M : extendedMonotoneAlgebraData)
    (T : NVec M.d → ℕ) (hT : ∀ {x y : NVec M.d}, M.strict x y → T x < T y) (b n : NVec M.d)
    (hw : WrapUnboundedAt (S := valueSchema M.interp) T b n)
    (hg : GainBoundedAt (S := valueSchema M.interp) T b n) :
    ¬ extendedMonotoneAlgebraAccepts M := fun hA =>
  not_dupOriented_of_barrierCell M.interp M.strict T hT b n hw hg
    ((dupOriented_iff M.interp M.strict).2
      (show RootRuleOrients M.interp M.strict from hA).recurSucc)

/-- Witness: the pair algebra of Endrullis, Waldmann and Zantema's Example 1 order, `(m, n) > (m', n')`
iff `m > m'` and `n ≥ n'`, `≳` pointwise, on the cost–size operations of the tuple witness. -/
abbrev extendedMonotoneAlgebraWitness : extendedMonotoneAlgebraData where
  d := tupleInterpretationStrictSWitness.m
  interp := tupleInterpretationStrictSWitness.interp
  strict := vecLt
  weak := vecLe

theorem extendedMonotoneAlgebraWitness_laws :
    extendedMonotoneAlgebraLaws extendedMonotoneAlgebraWitness := by
  unfold extendedMonotoneAlgebraLaws
  exact ⟨vecLt_wf _,
    fun _ _ _ hyz hxy => And.intro (lt_of_le_of_lt (hxy 0) hyz.1) (fun i => le_trans (hxy i) (hyz.2 i)),
    tuple_weakContextLaws _,
    tuple_strictContextLaws _ tupleInterpretationStrictSWitness_laws⟩

theorem extendedMonotoneAlgebraWitness_result :
    extendedMonotoneAlgebraResult extendedMonotoneAlgebraWitness :=
  And.intro tupW_root (extendedMonotoneAlgebra_sound _ extendedMonotoneAlgebraWitness_laws tupW_root)

/-- Controls. The algebra is not constant. `≳` is not the union of `>` and equality. The rule
decreases strictly in the first coordinate and only weakly (with equality) in the second. -/
theorem extendedMonotoneAlgebraWitness_feature :
    extendedMonotoneAlgebraWitness.interp.succ extendedMonotoneAlgebraWitness.interp.zero ≠
        extendedMonotoneAlgebraWitness.interp.zero ∧
      (extendedMonotoneAlgebraWitness.weak ![1, 0] ![1, 1] ∧
        ¬ extendedMonotoneAlgebraWitness.strict ![1, 0] ![1, 1] ∧
        (![1, 0] : Fin 2 → ℕ) ≠ ![1, 1]) ∧
      ∀ b s n : NVec extendedMonotoneAlgebraWitness.d,
        extendedMonotoneAlgebraWitness.interp.wrap s
            (extendedMonotoneAlgebraWitness.interp.recur b s n) 1 =
          extendedMonotoneAlgebraWitness.interp.recur b s
            (extendedMonotoneAlgebraWitness.interp.succ n) 1 := by
  refine ⟨fun h => absurd (congrFun h 0) (by decide), ⟨?_, ?_, ?_⟩, fun b s n => tupW_dup_second b s n⟩
  · intro i
    fin_cases i <;> decide
  · intro h
    exact absurd h.1 (by decide)
  · intro h
    exact absurd (congrFun h 1) (by decide)

/-- Replacing `>` by the pointwise strict order loses acceptance: the second coordinate of the
rule is an equality. -/
theorem extendedMonotoneAlgebra_mutation :
    ¬ extendedMonotoneAlgebraResult
      { extendedMonotoneAlgebraWitness with strict := fun x y => ∀ i, x i < y i } := by
  rintro ⟨hA, _⟩
  have h := (show RootRuleOrients _ (fun x y : NVec extendedMonotoneAlgebraWitness.d =>
    ∀ i, x i < y i) from hA).recurSucc (fun _ => 0) (fun _ => 0) (fun _ => 0) 1
  exact lt_irrefl _ (lt_of_lt_of_eq h
    (tupW_dup_second (fun _ => 0) (fun _ => 0) (fun _ => 0)).symm)

/-- Over any signature, a lawful accepting member whose inert operations are strictly monotone for
`>` (an extended monotone algebra on the larger signature) proves termination. -/
theorem extendedMonotoneAlgebra_signature (ι : Type) (arity : ι → ℕ) (ν : Type)
    (M : extendedMonotoneAlgebraData)
    (ops : (f : ι) → (Fin (arity f) → NVec M.d) → NVec M.d)
    (hops : ∀ (f : ι) (args : Fin (arity f) → NVec M.d) (i : Fin (arity f)) {x y : NVec M.d},
      M.strict x y → M.strict (ops f (Function.update args i x)) (ops f (Function.update args i y)))
    (hM : extendedMonotoneAlgebraLaws M) (hA : extendedMonotoneAlgebraAccepts M) :
    WellFounded (fun u t : SigTerm ι arity ν => SigContextStep t u) :=
  sig_contextStep_reverse_wellFounded
    (I := ({ toInterpretation := M.interp, inertOp := ops } : SigInterpretation ι arity (NVec M.d)))
    hA { toStrictContextLaws := (show EMALaws M from hM).strict_mono, inertArg := hops }
    (show EMALaws M from hM).strict_wf (fun _ => M.interp.zero)

/-! ## Finite models -/

open Classical in
/-- Number of carrier values strictly below `x`. -/
noncomputable def belowCount {α : Type} [Fintype α] (lt : α → α → Prop) (x : α) : ℕ :=
  (Finset.univ.filter (fun y => lt y x)).card

theorem belowCount_lt {α : Type} [Fintype α] (lt : α → α → Prop) (hirr : ∀ x, ¬ lt x x)
    (htrans : ∀ x y z, lt x y → lt y z → lt x z) {x y : α} (h : lt x y) :
    belowCount lt x < belowCount lt y := by
  classical
  unfold belowCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨x, by simp [h], by simp [hirr x]⟩
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact htrans z x y hz h

theorem belowCount_le {α : Type} [Fintype α] (lt : α → α → Prop) (x : α) :
    belowCount lt x ≤ Fintype.card α := by
  classical
  unfold belowCount
  exact le_trans (Finset.card_filter_le _ _) (le_of_eq Finset.card_univ)

/-- A strict order on a finite carrier with a wrapper strictly monotone in its second argument does
not orient the duplicating rule: the values of `wrapⁱ(0, recur(0, 0, succᵏ 0))` form strict chains of
every length. -/
theorem finite_strict_dup_barrier {α : Type} [Fintype α] (I : Interpretation α)
    (lt : α → α → Prop) (hirr : ∀ x, ¬ lt x x) (htrans : ∀ x y z, lt x y → lt y z → lt x z)
    (hwr : ∀ z {x y : α}, lt x y → lt (I.wrap z x) (I.wrap z y)) : ¬ DupOriented I lt := by
  intro h
  have hor := (dupOriented_iff I lt).1 h
  have hit : ∀ (i : ℕ) {x y : α}, lt x y → lt ((I.wrap I.zero)^[i] x) ((I.wrap I.zero)^[i] y) := by
    intro i
    induction i with
    | zero =>
        intro x y hxy
        exact hxy
    | succ i ih =>
        intro x y hxy
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact hwr I.zero (ih hxy)
  have key : ∀ k i : ℕ,
      k ≤ belowCount lt ((I.wrap I.zero)^[i] (I.recur I.zero I.zero (I.succ^[k] I.zero))) := by
    intro k
    induction k with
    | zero =>
        intro i
        exact Nat.zero_le _
    | succ k ih =>
        intro i
        have h1 := belowCount_lt lt hirr htrans (hit i (hor I.zero I.zero (I.succ^[k] I.zero)))
        have h2 := ih (i + 1)
        rw [Function.iterate_succ_apply] at h2
        rw [Function.iterate_succ_apply']
        omega
  have h3 := key (Fintype.card α + 1) 0
  have h4 := belowCount_le lt
    ((I.wrap I.zero)^[0] (I.recur I.zero I.zero (I.succ^[Fintype.card α + 1] I.zero)))
  omega

/-- The strict-growth carrier is impossible: on a finite carrier no binary operation strictly
increases its second argument. -/
theorem finite_no_strict_growth {α : Type} [Fintype α] (lt : α → α → Prop)
    (hirr : ∀ x, ¬ lt x x) (htrans : ∀ x y z, lt x y → lt y z → lt x z)
    (w : α → α → α) (x0 : α) : ¬ ∀ x y, lt y (w x y) := by
  intro h
  have key : ∀ k : ℕ, k ≤ belowCount lt ((w x0)^[k] x0) := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        have := belowCount_lt lt hirr htrans (h x0 ((w x0)^[k] x0))
        omega
  have h1 := key (Fintype.card α + 1)
  have h2 := belowCount_le lt ((w x0)^[Fintype.card α + 1] x0)
  omega

/-- An algebra on a finite carrier `Fin (k + 1)` with a strict relation. -/
structure FiniteModelData where
  k : ℕ
  interp : Interpretation (Fin (k + 1))
  lt : Fin (k + 1) → Fin (k + 1) → Prop

/-- A strict order (irreflexive and transitive, hence well founded on the finite carrier) and strict
monotonicity of every operation. -/
structure FiniteModelLaws (M : FiniteModelData) : Prop where
  irrefl : ∀ x, ¬ M.lt x x
  trans : ∀ x y z, M.lt x y → M.lt y z → M.lt x z
  strict_mono : StrictContextLaws M.interp M.lt

/-- A two-element model of both free rules: both sides of every rule have the same value. -/
def boolModel : Interpretation Bool where
  zero := false
  succ := fun _ => true
  wrap := fun _ _ => true
  recur := fun b _ n => b || n

/-! ### finiteModelTermination -/

/-- Native data of `finiteModelTermination`: carrier size, operations and strict relation. -/
abbrev finiteModelTerminationData : Type := FiniteModelData

/-- Laws of `finiteModelTermination`: a strictly monotone algebra on a finite carrier, pinned to
A. Yamada, *Tuple interpretations for termination of term rewriting*, Journal of Automated
Reasoning 66(4):667–688, 2022, Definition 1 (order pair: `≻` irreflexive and, by compatibility,
transitive; on a finite carrier it is well founded) and Definition 7 (strictly monotone algebra),
the setting of Theorem 7, with the carrier `Fin (k + 1)`. The models of semantic labelling
(H. Zantema, *Termination of term rewriting by semantic labelling*, Fundamenta Informaticae
24:89–105, 1995) require only equal values of the two sides and appear in the controls. -/
def finiteModelTerminationLaws (M : finiteModelTerminationData) : Prop := FiniteModelLaws M

/-- Acceptance: the finite algebra orients the free duplicating rule. -/
def finiteModelTerminationAccepts (M : finiteModelTerminationData) : Prop :=
  DupOriented M.interp M.lt

/-- Verdict: barrier. -/
def finiteModelTerminationResult (M : finiteModelTerminationData) : Prop :=
  ¬ finiteModelTerminationAccepts M

/-- Every lawful finite member fails: the counter chain `recur(0, 0, succᵏ 0)` descends through
`k` strict steps under wrapper contexts, and a finite strict order has no chain longer than its
carrier. Consumed laws: `irrefl`, `trans`, `strict_mono.wrapRight`. -/
theorem finiteModelTermination_universal :
    ∀ M : finiteModelTerminationData, finiteModelTerminationLaws M →
      finiteModelTerminationResult M :=
  fun M hM => finite_strict_dup_barrier M.interp M.lt (show FiniteModelLaws M from hM).irrefl
    (show FiniteModelLaws M from hM).trans (show FiniteModelLaws M from hM).strict_mono.wrapRight

/-- Witness: the one-point algebra with the empty strict order. -/
abbrev finiteModelTerminationWitness : finiteModelTerminationData where
  k := 0
  interp := { zero := 0, succ := fun _ => 0, wrap := fun _ _ => 0, recur := fun _ _ _ => 0 }
  lt := fun _ _ => False

theorem finiteModelTerminationWitness_laws :
    finiteModelTerminationLaws finiteModelTerminationWitness := by
  unfold finiteModelTerminationLaws
  exact ⟨fun _ h => h, fun _ _ _ h _ => False.elim h,
    ⟨fun h => False.elim h, fun _ h => False.elim h, fun _ {_ _} h => False.elim h,
      fun _ _ h => False.elim h, fun _ {_ _} _ h => False.elim h,
      fun _ _ {_ _} h => False.elim h⟩⟩

theorem finiteModelTerminationWitness_result :
    finiteModelTerminationResult finiteModelTerminationWitness :=
  finiteModelTermination_universal _ finiteModelTerminationWitness_laws

/-- Controls. Weak one-point control: the one-point algebra is a model of both free rules (equal
values), so the weak comparison holds while the strict one is empty. Genuine finite model: the
two-element algebra `boolModel` is a model of both rules that separates `zero` from `succ zero`,
the kind of model semantic labelling uses. Strict growth: no finite carrier has a binary operation
that strictly increases its second argument. -/
theorem finiteModelTerminationWitness_feature :
    (∀ b s n : Fin 1,
      finiteModelTerminationWitness.interp.recur b s (finiteModelTerminationWitness.interp.succ n) =
        finiteModelTerminationWitness.interp.wrap s
          (finiteModelTerminationWitness.interp.recur b s n)) ∧
      (∀ b s : Fin 1,
        finiteModelTerminationWitness.interp.recur b s finiteModelTerminationWitness.interp.zero =
          b) ∧
      (∀ b s n : Bool, boolModel.recur b s (boolModel.succ n) = boolModel.wrap s (boolModel.recur b s n)) ∧
      (∀ b s : Bool, boolModel.recur b s boolModel.zero = b) ∧
      boolModel.succ boolModel.zero ≠ boolModel.zero ∧
      ∀ (k : ℕ) (lt : Fin (k + 1) → Fin (k + 1) → Prop) (w : Fin (k + 1) → Fin (k + 1) → Fin (k + 1)),
        (∀ x, ¬ lt x x) → (∀ x y z, lt x y → lt y z → lt x z) → ¬ ∀ x y, lt y (w x y) :=
  ⟨fun _ _ _ => rfl, fun b _ => (Fin.eq_zero b).symm, fun b _ _ => Bool.or_true b,
    fun b _ => Bool.or_false b, by decide,
    fun _ lt w hirr htrans => finite_no_strict_growth lt hirr htrans w 0⟩

/-- Making the strict relation total breaks irreflexivity, and the mutant then accepts. -/
theorem finiteModelTermination_mutation :
    ¬ finiteModelTerminationLaws { finiteModelTerminationWitness with lt := fun _ _ => True } ∧
      finiteModelTerminationAccepts { finiteModelTerminationWitness with lt := fun _ _ => True } :=
  ⟨fun h => (show FiniteModelLaws _ from h).irrefl 0 trivial, fun _ _ => trivial⟩

/-- Over any signature, a lawful finite member extended by arbitrary inert operations does not
orient the duplicating rule. -/
theorem finiteModelTermination_signature (ι : Type) (arity : ι → ℕ)
    (M : finiteModelTerminationData)
    (ops : (f : ι) → (Fin (arity f) → Fin (M.k + 1)) → Fin (M.k + 1))
    (hM : finiteModelTerminationLaws M) :
    ¬ ∀ ρ : Fin 3 → Fin (M.k + 1),
      M.lt (({ toInterpretation := M.interp, inertOp := ops } :
          SigInterpretation ι arity (Fin (M.k + 1))).eval ρ sigDupRhs)
        (({ toInterpretation := M.interp, inertOp := ops } :
          SigInterpretation ι arity (Fin (M.k + 1))).eval ρ sigDupLhs) :=
  fun h => finiteModelTermination_universal M hM
    ((sig_dupOrientedOn_iff (fun _ => True) _ M.lt).1 (fun ρ _ => h ρ))

end OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations
