import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSSemanticDirectMeasure

/-!
# RDRS Semantic Payload Sensitivity (Milestone S2)

Roadmap source:
`OperatorKO7-private/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`
Milestone S2.

Provides the semantic payload-observable, payload-lens, raw/decisive
payload-sensitivity, counter-forgetting, and counter-dominated
predicates over `SemanticMeasureData`. Classifies the counter-first
lex measure as raw payload-sensitive but NOT decisive payload-sensitive.

## Bible compliance

- W2: `set_option autoImplicit false`.
- W8: every theorem and `def` carries the structured docstring template.
- W5/R1: no forbidden trust-surface tokens from the Lean audit bible.
- Relation Gate: every theorem's `Relation:` line names the
  abstract `RDRSStep` carrier; not a concrete rewriting relation.
- The classification theorem
  `counter_first_lex_is_raw_payload_sensitive_not_decisive_payload_sensitive`
  is mandatory and proved here.
The counter-first lex example uses bare `SemanticMeasureData` rather than
fabricating directness evidence. Directness certificates are handled by
`RDRSSemanticDirectMeasure.lean`.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSSemanticPayloadSensitivity

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure

/-! ## Payload observable and payload lens -/

/--
Proves: a payload observable for an RDRS step pair `R`: a triple
  `(b, n, s₀, s₁)` of base / counter / two payload values such that
  the LHS terms at the two payloads are distinguishable.
Does not prove: that every RDRS admits a payload observable; the
  structure is inhabited only for RDRS step pairs whose LHS observes
  the payload.
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: per concrete `R`.
-/
structure PayloadObservable {B S N T : Type} (R : RDRSStep B S N T) where
  b : B
  n : N
  s₀ : S
  s₁ : S
  distinguishable_lhs : R.lhs b s₀ n ≠ R.lhs b s₁ n

/--
Proves: a payload lens for `R` is a typed observable `observe : T → P`
  on terms together with a payload-faithfulness witness: whenever
  LHS at two distinct payloads is distinguishable, the observation
  also distinguishes.
Does not prove: that the lens covers every payload distinction in
  the system; only the faithful direction is required.
Relation: abstract `RDRSStep B S N T`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: per concrete `R`.
-/
structure PayloadLens {B S N T : Type} (R : RDRSStep B S N T) where
  P : Type
  observe : T → P
  faithful :
    ∀ b n s₀ s₁,
      R.lhs b s₀ n ≠ R.lhs b s₁ n →
        observe (R.lhs b s₀ n) ≠ observe (R.lhs b s₁ n)

/-! ## Raw / decisive payload sensitivity -/

/--
Proves: `M` is raw payload-sensitive on `R`: there exists a base /
  counter / two payload values at which `M.μ` on the LHS takes
  distinct values.
Does not prove: that the descent on `R` actually uses payload; only
  that the measure mentions it.
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: per concrete `(R, M)` pair.
-/
def PayloadSensitiveRaw {B S N T : Type} (R : RDRSStep B S N T)
    (M : SemanticMeasureData T) : Prop :=
  ∃ b s s' n, M.μ (R.lhs b s n) ≠ M.μ (R.lhs b s' n)

/--
Proves: `M` is counter-forgetting on `R`: `M.μ` on both LHS and RHS
  is invariant under the payload coordinate at every base/counter
  combination. Equivalently, `M.μ` is payload-blind on `R`.
Does not prove: that `M` orients `R`; only payload-blindness.
Relation: abstract `RDRSStep B S N T`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: per concrete `(R, M)` pair.
-/
def CounterForgetting {B S N T : Type} (R : RDRSStep B S N T)
    (M : SemanticMeasureData T) : Prop :=
  (∀ b s s' n, M.μ (R.lhs b s n) = M.μ (R.lhs b s' n)) ∧
  (∀ b s s' n, M.μ (R.rhs b s n) = M.μ (R.rhs b s' n))

/--
Proves: `M`'s descent on `R` is counter-dominated: there exists a
  payload-blind measure `μc : T → M.A` (depending only on base and
  counter, not on payload) that orients `R` under `M`'s strict
  relation `M.ltA`.
Does not prove: that `M.μ` itself is payload-blind; only that a
  payload-blind alternative orients `R` with the same `ltA`.
Relation: abstract `RDRSStep B S N T`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: per concrete `(R, M)` pair.
-/
def CounterDominated {B S N T : Type} (R : RDRSStep B S N T)
    (M : SemanticMeasureData T) : Prop :=
  ∃ μc : T → M.A,
    (∀ b s s' n, μc (R.lhs b s n) = μc (R.lhs b s' n)) ∧
    (∀ b s s' n, μc (R.rhs b s n) = μc (R.rhs b s' n)) ∧
    Orients R μc M.ltA

/--
Proves: `M` is decisive payload-sensitive on `R`: `M` orients `R`,
  `M` is raw payload-sensitive on `R`, and there is no payload-blind
  alternative measure with the same `M.ltA` that orients `R`.
Does not prove: that `M.μ` is well-founded in any stronger sense
  than the `wf_ltA` field already guarantees.
Relation: abstract `RDRSStep B S N T`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: per concrete `(R, M)` pair.
-/
def PayloadSensitiveDecisive {B S N T : Type} (R : RDRSStep B S N T)
    (M : SemanticMeasureData T) : Prop :=
  Orients R M.μ M.ltA ∧
    PayloadSensitiveRaw R M ∧
      ¬ CounterDominated R M

/-! ## Theorem: decisive payload sensitivity rules out counter-forgetting -/

/--
Proves: if `M` is decisive payload-sensitive on `R`, then `M` is NOT
  counter-forgetting on `R`. (Contrapositive: a counter-forgetting
  measure that orients `R` is automatically a counter-dominated
  witness, hence cannot be decisive.)
Does not prove: any structural property beyond the bare implication;
  the proof composes the orientation conjunct of decisiveness with
  the counter-forgetting witness to produce the forbidden counter-
  dominated alternative.
Relation: abstract `RDRSStep B S N T`; not a concrete rewriting
  relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: parametric over `B`, `S`, `N`, `T`, `R`, and `M`.
-/
theorem payload_sensitive_decisive_not_counter_forgetting
    {B S N T : Type} (R : RDRSStep B S N T) (M : SemanticMeasureData T) :
    PayloadSensitiveDecisive R M → ¬ CounterForgetting R M := by
  rintro ⟨hOrient, _, hNoCD⟩ hCF
  apply hNoCD
  exact ⟨M.μ, hCF.1, hCF.2, hOrient⟩

/-! ## Counter-first lex worked example -/

/--
Proves: the counter-first lex RDRS step on `T = Nat × Nat`:
  LHS at `(n + 1, s)`, RHS at `(n, s)`. Counter on the first
  coordinate strictly decreases; payload `s` is preserved.
Does not prove: anything beyond the data.
Relation: `RDRSStep Unit Nat Nat (Nat × Nat)`.
Closure: not applicable (data definition).
Strategy: not applicable.
Trust: kernel-only.
Scope: this single concrete step pair.
-/
def counterFirstLex_R : RDRSStep Unit Nat Nat (Nat × Nat) where
  lhs _ s n := (n + 1, s)
  rhs _ s n := (n, s)

/--
Proves: well-foundedness of the first-coordinate strict order on
  `Nat × Nat`: `(fun p q => p.fst < q.fst)` is well-founded by
  `InvImage.wf` over `Nat.lt`.
Does not prove: well-foundedness of any lex order or any other
  composite relation.
Relation: not applicable (well-foundedness statement).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (`Nat.lt_wfRel.wf`).
Scope: the first-coordinate projection on `Nat × Nat`.
-/
theorem firstCoordLt_wf :
    WellFounded (fun (p q : Nat × Nat) => p.fst < q.fst) :=
  InvImage.wf Prod.fst Nat.lt_wfRel.wf

/--
Proves: the counter-first lex semantic measure data on `Nat × Nat`,
  with codomain `Nat × Nat`, strict relation given by first-coordinate
  `<`, well-foundedness via `firstCoordLt_wf`, and measure function `id`.
Does not prove: directness. This example is deliberately bare
  `SemanticMeasureData` so it does not fabricate no-oracle/no-DP
  evidence for the directness certificate interface.
Relation: parametric data; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: this single concrete `SemanticMeasureData (Nat × Nat)`.
-/
def counterFirstLex_M : SemanticMeasureData (Nat × Nat) where
  A := Nat × Nat
  ltA := fun p q => p.fst < q.fst
  wf_ltA := firstCoordLt_wf
  μ := id

/--
Proves: the counter-first lex measure on `counterFirstLex_R` is RAW
  payload-sensitive (the LHS values at distinct payloads differ:
  `(1, 0) ≠ (1, 1)`) but is NOT decisive payload-sensitive (the
  payload-blind alternative `fun p => (p.fst, 0)` orients
  `counterFirstLex_R` under the same first-coordinate strict
  relation).
Does not prove: anything about other measures or other RDRS step
  pairs.
Relation: `RDRSStep Unit Nat Nat (Nat × Nat)`; not a concrete
  rewriting relation.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: the single concrete `(counterFirstLex_R, counterFirstLex_M)`
  pair.
-/
theorem counter_first_lex_is_raw_payload_sensitive_not_decisive_payload_sensitive :
    PayloadSensitiveRaw counterFirstLex_R counterFirstLex_M ∧
      ¬ PayloadSensitiveDecisive counterFirstLex_R counterFirstLex_M := by
  refine ⟨?_, ?_⟩
  · -- Raw payload sensitivity: μ = id distinguishes (1, 0) and (1, 1).
    refine ⟨(), 0, 1, 0, ?_⟩
    intro h
    -- `M.μ` is `id`, so `h : (1, 0) = (1, 1)`; second components clash.
    have h2 : (0 : Nat) = 1 := (Prod.mk.inj h).2
    exact absurd h2 (by decide)
  · -- Not decisive: exhibit a payload-blind orienter.
    rintro ⟨_, _, hNoCD⟩
    apply hNoCD
    refine ⟨fun p => (p.fst, 0), ?_, ?_, ?_⟩
    · intro _ _ _ _; rfl
    · intro _ _ _ _; rfl
    · intro _ _ n
      show (n + 1 : Nat) > (n : Nat) -- after definitional reduction
      exact Nat.lt_succ_self n

/-- Audit anchor for the S2 payload-sensitivity surface. -/
def rdrs_semantic_payload_sensitivity_anchor : String :=
  "OperatorKO7.RDRSSemanticPayloadSensitivity.PayloadSensitiveDecisive"

end OperatorKO7.RDRSSemanticPayloadSensitivity
