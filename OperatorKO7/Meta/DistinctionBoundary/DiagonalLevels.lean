import OperatorKO7.Meta.DistinctionBoundary.DiscriminatorExtension
import OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra

set_option autoImplicit false

/-!
# Diagonal levels: copying, comparison, and self-evaluation

Manuscript / roadmap anchor: ROADMAP-09, Weld 6, section 6.2. The permitted
framing sentence for this material is section 6.3, quoted verbatim:

> "The program mechanizes the copy diagonal, the comparison diagonal, and the
> boundary object their junction forces; self-evaluation is a further structure
> the stack provably does not yet contain."

Nothing in this module is a Goedel result, and nothing here re-derives one.

## The three frozen levels

* `CopyDiagonal C` (D0): `copy : C → C × C` with `copy x = (x, x)`.
* `ComparisonDiagonal C` (D1): `test : C → C → Bool`, sound and complete for
  syntactic identity.
* `SelfEvaluationDiagonal C` (D2): `Code`, `quote`, `eval`, `diag`, and the
  self-application law `diag (quote x) = eval (quote x) x`. The field names
  match the absence record of `Meta/LawvereYanofskySeparation.lean`
  (`LawvereCodeObject.Code`, `LawvereCodeObject.quote`, and the evaluation slot
  of `LawvereEvaluationMap`), so presence and absence speak the same language.

## What is proved

* **D0 positive.** `traceCopyDiagonal`: the kernel carrier copies.
* **D1 positive.** `traceComparisonDiagonal`: the compiled comparator
  `DiscriminatorExtension.structEq` is the D1 witness.
* **D0 / D1 separation, clone-relative.** The unconditional form asked for by
  the roadmap sketch is *refuted*, not deferred:
  `comparisonDiagonal_nonempty_of_classical` builds a sound and complete
  `Bool`-valued test on every carrier from the ambient classical logic, so
  `unconditional_copy_not_comparison_refuted` shows no carrier can separate the
  two levels unconditionally in Lean. What does separate them is naturality:
  a copy diagonal is natural under *every* endomorphism of its carrier
  (`copyDiagonal_natural_under_every_map`) and a comparison diagonal is natural
  under *no* map that merges two distinct points
  (`no_natural_comparisonDiagonal_of_merge`). This is the compiled T-E interface
  of `ObserverExpressivity`, now stated at the level of the two structures.
  `traceEndomorphism_never_merges` records why the separating carrier cannot be
  the kernel carrier itself: `Trace` is the free algebra of the signature, so
  its only signature endomorphism is the identity.
* **D1 / D2 separation, definition-relative.** `InternalToSignature D` says the
  codes of `D` are kernel terms, its evaluator is a Sigma-term operation of the
  seven kernel constructors, and every unary Sigma-definable function has a
  code. `no_internal_selfEvaluationDiagonal` proves that no self-evaluation
  diagonal on `Trace` is internal in this sense. The mathematical core is
  `no_sigmaDefinable_universal_evaluator`: a Sigma-definable binary evaluator
  has a Sigma-definable delta-shifted diagonal, universality supplies a code for
  it, and that code is a fixed point of `delta`, which `delta_ne_self` forbids.

## Non-triviality and scope

* The obstruction is about *simultaneous* universality, not about representing
  functions at all: `sigmaDefinableBinary_of_unary` shows every single unary
  Sigma-definable function is represented at every code by a Sigma-definable
  evaluator.
* `InternalToSignature` is provably uninhabited for every `D`, so its
  non-vacuity is carried field by field:
  `internalToSignature_fields_are_individually_satisfiable` satisfies every
  field except universality, and `trivialSelfEvaluation_not_universal` shows
  universality is the field that fails. The emptiness is therefore a theorem
  about the evaluator, not a type error in the bookkeeping.
* `SelfEvaluationDiagonal Trace` is inhabited by a degenerate instance
  (`trivialSelfEvaluationDiagonal`), which is exactly why level 2 is stated
  relative to internality.
* The internality definition is the scope fence: a different signature, a
  different code discipline, or an evaluator outside the term clone is a
  different statement, and this module proves nothing about it.

Relation: not applicable (carrier-level and clone-level statements).
Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. `comparisonDiagonal_nonempty_of_classical`
and its corollary use `Classical.choice` deliberately, since the refutation they
carry is a statement about the ambient classical logic.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.DiagonalLevels

open OperatorKO7
open OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra
open OperatorKO7.Meta.DistinctionBoundary.DiscriminatorExtension

/-! ## The three frozen structures

These three declarations are frozen before any theorem below refers to them.
-/

/-- **D0, copying.** The duplicating diagonal on a carrier. -/
structure CopyDiagonal (C : Type*) where
  /-- The duplication map. -/
  copy : C → C × C
  /-- The duplication law: `copy` lands on the diagonal of `C × C`. -/
  copy_law : ∀ x, copy x = (x, x)

/-- **D1, comparison.** A `Bool`-valued equality surface on a carrier: sound
for syntactic identity and complete on the diagonal. -/
structure ComparisonDiagonal (C : Type*) where
  /-- The comparator. -/
  test : C → C → Bool
  /-- Soundness: a positive verdict forces identity. -/
  sound : ∀ a b, test a b = true → a = b
  /-- Completeness on the diagonal. -/
  complete : ∀ a, test a a = true

/-- **D2, self-evaluation.** An internal code type, a quotation map, an
evaluator, and a diagonal map satisfying the self-application law. Field names
mirror the absence record of `Meta/LawvereYanofskySeparation.lean`. -/
structure SelfEvaluationDiagonal (C : Type*) where
  /-- The code type. -/
  Code : Type*
  /-- Quotation of a carrier element as a code. -/
  quote : C → Code
  /-- Evaluation of a code at a carrier argument. -/
  eval : Code → C → C
  /-- The internal diagonal map `x ↦ eval(x, x)`, named on codes. -/
  diag : Code → C
  /-- The self-application law: the diagonal of a quotation is the evaluation of
  that quotation at the element it quotes. -/
  diag_law : ∀ x : C, diag (quote x) = eval (quote x) x

/-! ## D0 and D1 on the kernel carrier -/

/-- R5 witness for D0 on the kernel carrier. -/
def traceCopyDiagonal : CopyDiagonal Trace where
  copy := fun t => (t, t)
  copy_law := fun _ => rfl

/-- R5 witness for D1 on the kernel carrier: the compiled comparator of
`DiscriminatorExtension`. -/
def traceComparisonDiagonal : ComparisonDiagonal Trace where
  test := structEq
  sound := fun _ _ h => structEq_sound h
  complete := fun a => structEq_complete (rfl : a = a)

/-- Non-triviality of the D1 witness: the comparator separates a concrete pair
and identifies a concrete diagonal point. -/
theorem traceComparisonDiagonal_separates :
    traceComparisonDiagonal.test Trace.void Trace.void = true ∧
      traceComparisonDiagonal.test Trace.void (Trace.delta Trace.void) = false := by
  constructor <;> rfl

/-- Non-triviality of the D0 witness. -/
theorem traceCopyDiagonal_duplicates :
    traceCopyDiagonal.copy (Trace.delta Trace.void) =
      (Trace.delta Trace.void, Trace.delta Trace.void) := rfl

/-! ## The unconditional D0/D1 separation is refuted

Lean's ambient logic is classical, so a sound and complete `Bool`-valued test
exists on every carrier. The roadmap's unconditional sketch is therefore false
here, and the honest separation is the clone-relative one below.
-/

/-- Every carrier admits a sound and complete comparison diagonal, built from
classical decidability. This is a statement about the ambient logic: the
comparator it produces is not computable. -/
theorem comparisonDiagonal_nonempty_of_classical (C : Type*) :
    Nonempty (ComparisonDiagonal C) := by
  classical
  exact ⟨{ test := fun a b => decide (a = b)
           sound := fun _ _ h => of_decide_eq_true h
           complete := fun _ => decide_eq_true rfl }⟩

/-- **LEAN_REFUTATION.** No carrier carries a copy diagonal while failing to
carry a comparison diagonal, because the second condition is unsatisfiable in
Lean. The unconditional form of `copy_not_comparison` is thus refuted rather
than deferred. -/
theorem unconditional_copy_not_comparison_refuted :
    ¬ ∃ C : Type, Nonempty (CopyDiagonal C) ∧ ¬ Nonempty (ComparisonDiagonal C) := by
  rintro ⟨C, -, hno⟩
  exact hno (comparisonDiagonal_nonempty_of_classical C)

/-! ## The clone-relative D0/D1 separation -/

/-- Naturality of a copy diagonal under a self-map of its carrier: duplication
commutes with the map. -/
def CopyDiagonal.NaturalUnder {C : Type*} (D : CopyDiagonal C) (h : C → C) : Prop :=
  ∀ x, D.copy (h x) = (h (D.copy x).1, h (D.copy x).2)

/-- Naturality of a comparison diagonal under a self-map of its carrier. The
observation type is `Bool`, on which an endomorphism of the carrier acts
trivially, so naturality here is invariance of the verdict. -/
def ComparisonDiagonal.NaturalUnder {C : Type*} (D : ComparisonDiagonal C) (h : C → C) : Prop :=
  ∀ a b, D.test (h a) (h b) = D.test a b

/-- **D0 survives every endomorphism.** Copying is natural under every self-map
of the carrier, with no hypothesis on the map. -/
theorem copyDiagonal_natural_under_every_map {C : Type*}
    (D : CopyDiagonal C) (h : C → C) : D.NaturalUnder h := by
  intro x
  rw [D.copy_law (h x), D.copy_law x]

/-- **D1 fails on every merging endomorphism.** A comparison diagonal invariant
under a map that identifies two distinct points would call that pair equal.
No reflection hypothesis is needed: soundness and diagonal completeness carry
the whole argument. -/
theorem no_natural_comparisonDiagonal_of_merge {C : Type*}
    (h : C → C) (x y : C) (hxy : x ≠ y) (hmerge : h x = h y)
    (D : ComparisonDiagonal C) : ¬ D.NaturalUnder h := by
  intro hnat
  have hxy_test : D.test x y = D.test (h y) (h y) := by
    rw [← hnat x y, hmerge]
  exact hxy (D.sound x y (hxy_test.trans (D.complete (h y))))

/-- **The clone-relative separation.** On a carrier with a merging self-map,
every copy diagonal is natural and no comparison diagonal is. The witness is the
three-point carrier and the map merging `2` into `1`, the same shape as
`ObserverExpressivity.endomorphismHypotheses_nonvacuous`. -/
theorem copy_not_comparison_clone_relative :
    ∃ (C : Type) (h : C → C),
      Nonempty (CopyDiagonal C) ∧
        (∀ D : CopyDiagonal C, D.NaturalUnder h) ∧
        (∀ D : ComparisonDiagonal C, ¬ D.NaturalUnder h) := by
  refine ⟨Fin 3, fun i => if i = 2 then 1 else i,
    ⟨⟨fun x => (x, x), fun _ => rfl⟩⟩, ?_, ?_⟩
  · intro D
    exact copyDiagonal_natural_under_every_map D _
  · intro D
    refine no_natural_comparisonDiagonal_of_merge _ 1 2 ?_ ?_ D
    · decide
    · decide

/-! ## Why the separating carrier cannot be the kernel carrier

`Trace` is the free algebra of the seven-constructor signature, so it has
exactly one signature endomorphism and that endomorphism merges nothing. The
clone-relative separation above therefore has to live on a non-free carrier.
-/

/-- An endomorphism of the kernel carrier as a signature algebra: a self-map
commuting with all seven constructors. -/
structure TraceEndomorphism where
  /-- The underlying map. -/
  map : Trace → Trace
  /-- Commutation with `void`. -/
  map_void : map Trace.void = Trace.void
  /-- Commutation with `delta`. -/
  map_delta : ∀ t, map (Trace.delta t) = Trace.delta (map t)
  /-- Commutation with `integrate`. -/
  map_integrate : ∀ t, map (Trace.integrate t) = Trace.integrate (map t)
  /-- Commutation with `merge`. -/
  map_merge : ∀ a b, map (Trace.merge a b) = Trace.merge (map a) (map b)
  /-- Commutation with `app`. -/
  map_app : ∀ a b, map (Trace.app a b) = Trace.app (map a) (map b)
  /-- Commutation with `recΔ`. -/
  map_recΔ : ∀ a b c, map (Trace.recΔ a b c) = Trace.recΔ (map a) (map b) (map c)
  /-- Commutation with `eqW`. -/
  map_eqW : ∀ a b, map (Trace.eqW a b) = Trace.eqW (map a) (map b)

/-- R5 witness: the identity is a signature endomorphism. -/
def identityTraceEndomorphism : TraceEndomorphism where
  map := id
  map_void := rfl
  map_delta := fun _ => rfl
  map_integrate := fun _ => rfl
  map_merge := fun _ _ => rfl
  map_app := fun _ _ => rfl
  map_recΔ := fun _ _ _ => rfl
  map_eqW := fun _ _ => rfl

/-- Freeness: the identity is the only signature endomorphism of the kernel
carrier. Every commutation field is consumed, one per constructor. -/
theorem traceEndomorphism_is_identity (E : TraceEndomorphism) : ∀ t, E.map t = t := by
  intro t
  induction t with
  | void => exact E.map_void
  | delta s ih => rw [E.map_delta s, ih]
  | integrate s ih => rw [E.map_integrate s, ih]
  | merge a b iha ihb => rw [E.map_merge a b, iha, ihb]
  | app a b iha ihb => rw [E.map_app a b, iha, ihb]
  | recΔ a b c iha ihb ihc => rw [E.map_recΔ a b c, iha, ihb, ihc]
  | eqW a b iha ihb => rw [E.map_eqW a b, iha, ihb]

/-- No signature endomorphism of the kernel carrier merges two distinct terms,
so the merging hypothesis of `copy_not_comparison_clone_relative` cannot be met
on `Trace` itself. -/
theorem traceEndomorphism_never_merges (E : TraceEndomorphism) {x y : Trace}
    (hmerge : E.map x = E.map y) : x = y := by
  rw [← traceEndomorphism_is_identity E x, ← traceEndomorphism_is_identity E y]
  exact hmerge

/-! ## Sigma-definability on the kernel carrier

`SigmaTerm` is the term algebra of the seven kernel constructors with two
argument slots (`Meta/SafeStep/SigmaFreeAlgebra.lean`). `evalTrace` interprets
such a term in the kernel carrier.
-/

/-- Interpretation of a Sigma-term in the kernel carrier: `varA` receives `a`,
`varB` receives `b`, and every constructor maps to its kernel counterpart. -/
def evalTrace (a b : Trace) : SigmaTerm → Trace
  | .void => Trace.void
  | .varA => a
  | .varB => b
  | .delta s => Trace.delta (evalTrace a b s)
  | .integrate s => Trace.integrate (evalTrace a b s)
  | .merge s t => Trace.merge (evalTrace a b s) (evalTrace a b t)
  | .app s t => Trace.app (evalTrace a b s) (evalTrace a b t)
  | .recDelta s t u => Trace.recΔ (evalTrace a b s) (evalTrace a b t) (evalTrace a b u)
  | .eqW s t => Trace.eqW (evalTrace a b s) (evalTrace a b t)

/-- A unary function on the kernel carrier is Sigma-definable when a Sigma-term
computes it with the argument placed in both slots. -/
def SigmaDefinableUnary (f : Trace → Trace) : Prop :=
  ∃ u : SigmaTerm, ∀ x, f x = evalTrace x x u

/-- A binary function on the kernel carrier is Sigma-definable when a
Sigma-term computes it with the first argument in slot `varA` and the second in
slot `varB`. -/
def SigmaDefinableBinary (F : Trace → Trace → Trace) : Prop :=
  ∃ t : SigmaTerm, ∀ a x, F a x = evalTrace a x t

/-- The identity and `delta` are Sigma-definable, so the unary class is
inhabited and contains at least two distinct functions. -/
theorem sigmaDefinableUnary_nonvacuous :
    SigmaDefinableUnary (fun x => x) ∧ SigmaDefinableUnary Trace.delta := by
  constructor
  · exact ⟨SigmaTerm.varA, fun _ => rfl⟩
  · exact ⟨SigmaTerm.delta SigmaTerm.varA, fun _ => rfl⟩

/-- Projection and merging are Sigma-definable, so the binary class is
inhabited by non-degenerate operations. -/
theorem sigmaDefinableBinary_nonvacuous :
    SigmaDefinableBinary (fun a _ => a) ∧ SigmaDefinableBinary Trace.merge := by
  constructor
  · exact ⟨SigmaTerm.varA, fun _ _ => rfl⟩
  · exact ⟨SigmaTerm.merge SigmaTerm.varA SigmaTerm.varB, fun _ _ => rfl⟩

/-- Substitution of the second slot for the first, used to convert a unary
Sigma-definition into a binary one that ignores its code argument. -/
def substVarAByVarB : SigmaTerm → SigmaTerm
  | .void => .void
  | .varA => .varB
  | .varB => .varB
  | .delta s => .delta (substVarAByVarB s)
  | .integrate s => .integrate (substVarAByVarB s)
  | .merge s t => .merge (substVarAByVarB s) (substVarAByVarB t)
  | .app s t => .app (substVarAByVarB s) (substVarAByVarB t)
  | .recDelta s t u => .recDelta (substVarAByVarB s) (substVarAByVarB t) (substVarAByVarB u)
  | .eqW s t => .eqW (substVarAByVarB s) (substVarAByVarB t)

/-- The substitution law: after the substitution the first slot is dead, and the
value at `(a, x)` is the diagonal value of the original term at `x`. -/
theorem evalTrace_substVarAByVarB (a x : Trace) (u : SigmaTerm) :
    evalTrace a x (substVarAByVarB u) = evalTrace x x u := by
  induction u with
  | void => rfl
  | varA => rfl
  | varB => rfl
  | delta s ih => simp only [substVarAByVarB, evalTrace, ih]
  | integrate s ih => simp only [substVarAByVarB, evalTrace, ih]
  | merge s t ihs iht => simp only [substVarAByVarB, evalTrace, ihs, iht]
  | app s t ihs iht => simp only [substVarAByVarB, evalTrace, ihs, iht]
  | recDelta s t u ihs iht ihu => simp only [substVarAByVarB, evalTrace, ihs, iht, ihu]
  | eqW s t ihs iht => simp only [substVarAByVarB, evalTrace, ihs, iht]

/-- **Non-triviality of the no-go below.** Every single unary Sigma-definable
function is represented, at every code, by a Sigma-definable binary evaluator.
The obstruction proved next is therefore about simultaneous universality, not
about representing functions at all. -/
theorem sigmaDefinableBinary_of_unary {f : Trace → Trace} (h : SigmaDefinableUnary f) :
    ∃ E : Trace → Trace → Trace, SigmaDefinableBinary E ∧ ∀ c x, E c x = f x := by
  obtain ⟨u, hu⟩ := h
  refine ⟨fun _ x => f x, ⟨substVarAByVarB u, ?_⟩, fun _ _ => rfl⟩
  intro a x
  show f x = evalTrace a x (substVarAByVarB u)
  rw [hu x, evalTrace_substVarAByVarB]

/-! ## No internal universal evaluator -/

/-- `delta` has no fixed point in the kernel carrier. -/
theorem delta_ne_self : ∀ t : Trace, Trace.delta t ≠ t := by
  intro t
  induction t with
  | void => intro h; exact Trace.noConfusion h
  | delta s ih => intro h; injection h with h'; exact ih h'
  | integrate s _ => intro h; exact Trace.noConfusion h
  | merge a b _ _ => intro h; exact Trace.noConfusion h
  | app a b _ _ => intro h; exact Trace.noConfusion h
  | recΔ a b c _ _ _ => intro h; exact Trace.noConfusion h
  | eqW a b _ _ => intro h; exact Trace.noConfusion h

/-- The delta-shifted diagonal of a Sigma-definable binary evaluator is itself
Sigma-definable. This is the class-membership step of the no-go. -/
theorem sigmaDefinableUnary_delta_diagonal {E : Trace → Trace → Trace}
    (h : SigmaDefinableBinary E) :
    SigmaDefinableUnary (fun x => Trace.delta (E x x)) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨SigmaTerm.delta t, ?_⟩
  intro x
  show Trace.delta (E x x) = evalTrace x x (SigmaTerm.delta t)
  rw [ht x x]
  simp only [evalTrace]

/-- **The core no-go.** No Sigma-definable binary evaluator on the kernel
carrier is universal for the unary Sigma-definable functions.

Both premises are consumed: Sigma-definability puts the delta-shifted diagonal
`x ↦ delta (E x x)` inside the class, universality then supplies a code `c` for
it, and the resulting equation at `x = c` makes `E c c` a fixed point of
`delta`, which `delta_ne_self` forbids. -/
theorem no_sigmaDefinable_universal_evaluator :
    ¬ ∃ E : Trace → Trace → Trace,
        SigmaDefinableBinary E ∧
          ∀ f : Trace → Trace, SigmaDefinableUnary f → ∃ c : Trace, ∀ x, E c x = f x := by
  rintro ⟨E, hdef, huniv⟩
  obtain ⟨c, hc⟩ := huniv (fun x => Trace.delta (E x x))
    (sigmaDefinableUnary_delta_diagonal hdef)
  exact delta_ne_self (E c c) (hc c).symm

/-! ## The definition-relative D1/D2 separation -/

/-- Internality of a self-evaluation diagonal to the seven-constructor
signature. Three conditions, all load bearing:

* codes are kernel terms, presented as a retraction `encode ∘ decode = id`
  (only this direction is used, so the hypothesis is the weaker one);
* the evaluator, read on term codes, is a Sigma-term operation of the kernel
  constructors;
* every unary Sigma-definable function has a code.

The quotation and diagonal fields of `D` are not constrained here, which makes
the emptiness theorem below stronger. -/
structure InternalToSignature (D : SelfEvaluationDiagonal Trace) where
  /-- Terms viewed as codes. -/
  encode : Trace → D.Code
  /-- Codes read back as terms. -/
  decode : D.Code → Trace
  /-- Every code is the code of a term. -/
  encode_decode : ∀ c, encode (decode c) = c
  /-- The evaluator on term codes is a Sigma-term operation. -/
  evalDefinable : SigmaDefinableBinary (fun a x => D.eval (encode a) x)
  /-- The evaluator is universal for the unary Sigma-definable functions. -/
  evalUniversal : ∀ f : Trace → Trace, SigmaDefinableUnary f →
    ∃ c : D.Code, ∀ x, D.eval c x = f x

/-- **D1/D2 separation, negative half.** No self-evaluation diagonal on the
kernel carrier is internal to the seven-constructor signature. -/
theorem no_internal_selfEvaluationDiagonal (D : SelfEvaluationDiagonal Trace) :
    ¬ Nonempty (InternalToSignature D) := by
  rintro ⟨I⟩
  refine no_sigmaDefinable_universal_evaluator
    ⟨fun a x => D.eval (I.encode a) x, I.evalDefinable, ?_⟩
  intro f hf
  obtain ⟨c, hc⟩ := I.evalUniversal f hf
  refine ⟨I.decode c, ?_⟩
  intro x
  show D.eval (I.encode (I.decode c)) x = f x
  rw [I.encode_decode c]
  exact hc x

/-- R5 witness for the D2 structure: a degenerate self-evaluation diagonal on
the kernel carrier, with codes the terms themselves and evaluation the second
projection. Its existence is exactly why level 2 is stated relative to
internality. -/
def trivialSelfEvaluationDiagonal : SelfEvaluationDiagonal Trace where
  Code := Trace
  quote := fun t => t
  eval := fun _ x => x
  diag := fun c => c
  diag_law := fun _ => rfl

/-- The degenerate instance fails exactly at universality: its evaluator cannot
represent `delta`. -/
theorem trivialSelfEvaluation_not_universal :
    ¬ ∀ f : Trace → Trace, SigmaDefinableUnary f →
        ∃ c : trivialSelfEvaluationDiagonal.Code,
          ∀ x, trivialSelfEvaluationDiagonal.eval c x = f x := by
  intro huniv
  obtain ⟨c, hc⟩ := huniv Trace.delta (sigmaDefinableUnary_nonvacuous.2)
  exact delta_ne_self Trace.void (hc Trace.void).symm

/-- Non-vacuity for `InternalToSignature`, which is provably uninhabited: every
field except universality is simultaneously satisfiable on the degenerate
instance, so the emptiness is a theorem about the evaluator rather than a
contradiction in the bookkeeping fields. -/
theorem internalToSignature_fields_are_individually_satisfiable :
    ∃ (encode : Trace → trivialSelfEvaluationDiagonal.Code)
      (decode : trivialSelfEvaluationDiagonal.Code → Trace),
      (∀ c, encode (decode c) = c) ∧
        SigmaDefinableBinary (fun a x => trivialSelfEvaluationDiagonal.eval (encode a) x) := by
  refine ⟨fun t => t, fun c => c, fun _ => rfl, ⟨SigmaTerm.varB, ?_⟩⟩
  intro _ _
  rfl

/-- The degenerate instance is not internal, as an instance of the general
theorem. -/
theorem trivialSelfEvaluationDiagonal_not_internal :
    ¬ Nonempty (InternalToSignature trivialSelfEvaluationDiagonal) :=
  no_internal_selfEvaluationDiagonal trivialSelfEvaluationDiagonal

/-- **D1/D2 separation.** The kernel carrier has a comparison diagonal and no
signature-internal self-evaluation diagonal. -/
theorem comparison_not_selfEvaluation_definition_relative :
    Nonempty (ComparisonDiagonal Trace) ∧
      ∀ D : SelfEvaluationDiagonal Trace, ¬ Nonempty (InternalToSignature D) :=
  ⟨⟨traceComparisonDiagonal⟩, no_internal_selfEvaluationDiagonal⟩

/-! ## The ladder -/

/-- The three-level ledger of ROADMAP-09 section 6.1, as one statement: the
kernel carrier copies and compares; copying and comparison are separated at the
naturality interface on a merging carrier; and no self-evaluation diagonal on
the kernel carrier is internal to the seven-constructor signature. -/
theorem diagonal_levels_ladder :
    Nonempty (CopyDiagonal Trace) ∧
      Nonempty (ComparisonDiagonal Trace) ∧
      (∃ (C : Type) (h : C → C),
        Nonempty (CopyDiagonal C) ∧
          (∀ D : CopyDiagonal C, D.NaturalUnder h) ∧
          (∀ D : ComparisonDiagonal C, ¬ D.NaturalUnder h)) ∧
      (∀ D : SelfEvaluationDiagonal Trace, ¬ Nonempty (InternalToSignature D)) :=
  ⟨⟨traceCopyDiagonal⟩, ⟨traceComparisonDiagonal⟩, copy_not_comparison_clone_relative,
    no_internal_selfEvaluationDiagonal⟩

end OperatorKO7.Meta.DistinctionBoundary.DiagonalLevels
