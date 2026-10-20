import OperatorKO7.Meta.BoundaryGeneral.EchoDeficitBridge
import OperatorKO7.Meta.BoundaryGeneral.PersistentExogeny
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Cardinality

/-!
# Echo, emission peaks, and fixed-state dynamics

`RawEmitStep` has state-to-record edges, and record nodes are terminal. Given a null record that is not non-null, a raw emission of that record, and `FalseFormalLegitimacyAt`, the source state has a one-step peak with unjoinable record targets. The source state and both targets are pairwise distinct.

For an echo state under `LicensedSound` and `ObjectWitnessed`, with normalized object laws and the required raw emissions, `echo_fork_trap` proves zero licensed-channel deficit, false formal legitimacy, and nonconfluence at the source. For `EchoDynamics`, it also proves that `mass (run D t n) = mass t + n`, the state remains fixed, and no licensed non-null record appears at any run depth. These are statements about the abstract emission graph; identifying it with a term-rewriting critical pair requires a separate model instance.

Trust: Mathlib baseline; no `sorry`, `admit`, `axiom`, or `native_decide` occurs in this module.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryGeneral.EchoForkTrapCrown

open OperatorKO7.Meta.BoundaryGeneral.EchoLaw
open OperatorKO7.Meta.BoundaryGeneral.EchoDeficitBridge
open OperatorKO7.Meta.BoundaryGeneral.PersistentExogeny
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork

variable {E : Episode}

/-! ## The emission graph -/

/-- Nodes of the emission graph: licensing states and emitted records. -/
inductive EmitNode (E : Episode) where
  /-- A licensing state. -/
  | state (s : E.State)
  /-- An emitted record. -/
  | record (r : E.Record)

/-- The raw emission graph. A state steps to each record it raw-emits; records
are terminal, so the graph has depth one and every peak is an emission peak. -/
inductive RawEmitStep (E : Episode) : EmitNode E → EmitNode E → Prop where
  /-- A raw emission is an edge. -/
  | emit {s : E.State} {r : E.Record} :
      E.rawEmits s r → RawEmitStep E (EmitNode.state s) (EmitNode.record r)

/-- Records are normal forms of the emission graph. -/
theorem record_normalForm (r : E.Record) :
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm
      (RawEmitStep E) (EmitNode.record r) := by
  intro y h
  cases h

/-- Reachability from a record is trivial: a record reaches only itself. -/
theorem reach_from_record {r : E.Record} {z : EmitNode E}
    (h : Reach (RawEmitStep E) (EmitNode.record r) z) :
    z = EmitNode.record r := by
  obtain ⟨n, hsteps⟩ := h
  cases hsteps with
  | zero => rfl
  | succ hstep _ => cases hstep

/-- Distinct records are nonjoinable in the emission graph. -/
theorem records_nonjoinable {r₁ r₂ : E.Record} (hne : r₁ ≠ r₂) :
    ¬ Joinable (RawEmitStep E) (EmitNode.record r₁) (EmitNode.record r₂) := by
  rintro ⟨z, h1, h2⟩
  have e1 := reach_from_record h1
  have e2 := reach_from_record h2
  rw [e1] at e2
  exact hne (by injection e2)

/-! ## Emission graph nonconfluence -/

/-- If the null record is not non-null, a state raw-emits it, and false formal legitimacy holds, the graph has a one-step peak with unjoinable record targets. -/
theorem ffl_is_nonjoinable_peak
    {s : E.State} (hnull : ¬ E.nonnull E.null)
    (hnullRaw : E.rawEmits s E.null)
    (hffl : FalseFormalLegitimacyAt E s) :
    ∃ r, RawEmitStep E (EmitNode.state s) (EmitNode.record E.null)
      ∧ RawEmitStep E (EmitNode.state s) (EmitNode.record r)
      ∧ ¬ Joinable (RawEmitStep E)
          (EmitNode.record E.null) (EmitNode.record r) := by
  obtain ⟨r, hemit, _, hne⟩ := ffl_forces_second_raw_target hnull hffl
  exact ⟨r, RawEmitStep.emit hnullRaw, RawEmitStep.emit hemit,
    records_nonjoinable (fun h => hne h.symm)⟩

/-- Under the same premises, the peak has three pairwise distinct nodes: the source state and both emitted records. -/
theorem ffl_forces_three_distinct_nodes
    {s : E.State} (hnull : ¬ E.nonnull E.null)
    (hnullRaw : E.rawEmits s E.null)
    (hffl : FalseFormalLegitimacyAt E s) :
    ∃ r, EmitNode.state s ≠ (EmitNode.record E.null : EmitNode E)
      ∧ EmitNode.state s ≠ (EmitNode.record r : EmitNode E)
      ∧ (EmitNode.record E.null : EmitNode E) ≠ EmitNode.record r := by
  obtain ⟨r, hpk1, hpk2, hnj⟩ := ffl_is_nonjoinable_peak hnull hnullRaw hffl
  exact ⟨r, nonjoinable_peak_has_three_distinct_states hpk1 hpk2 hnj⟩

/-- Under these hypotheses, the raw emission graph is not confluent at the source state. -/
theorem ffl_not_confluentAt_source
    {s : E.State} (hnull : ¬ E.nonnull E.null)
    (hnullRaw : E.rawEmits s E.null)
    (hffl : FalseFormalLegitimacyAt E s) :
    ¬ ConfluentAt (RawEmitStep E) (EmitNode.state s) := by
  obtain ⟨r, hpk1, hpk2, hnj⟩ := ffl_is_nonjoinable_peak hnull hnullRaw hffl
  intro hconf
  exact hnj (hconf _ _ (reach_step hpk1) (reach_step hpk2))

/-! ## Combined consequences at one state -/

/-- For finite target and object types, under `LicensedSound`, `ObjectWitnessed`, an echo state, normalized object laws, and the stated raw-emission conditions, the theorem proves zero deficit, false formal legitimacy, source nonconfluence, mass growth by `n`, a fixed state, and no licensed non-null record at each run depth. -/
theorem echo_fork_trap
    {X : Type} [Fintype X] [Fintype E.Object]
    (hsound : LicensedSound E) (hwit : ObjectWitnessed E)
    (post : E.Answer → X → ℝ) (o₀ : E.Object)
    (μ : Fin 1 → ℝ) (ν : Fin 1 → E.Object → ℝ) (hν1 : ∀ w, ∑ c, ν w c = 1)
    (D : EchoDynamics E) (t : D.Trace)
    (hecho : EchoAt E (D.stateOf t))
    (hnull : ¬ E.nonnull E.null)
    (hnullRaw : E.rawEmits (D.stateOf t) E.null)
    (hraw : ∃ r, E.rawEmits (D.stateOf t) r ∧ E.nonnull r) :
    deficit μ ν (channelConditional E post (D.stateOf t)) = 0
      ∧ FalseFormalLegitimacyAt E (D.stateOf t)
      ∧ ¬ ConfluentAt (RawEmitStep E) (EmitNode.state (D.stateOf t))
      ∧ (∀ n, D.mass (run D t n) = D.mass t + n)
      ∧ (∀ n, D.stateOf (run D t n) = D.stateOf t)
      ∧ (∀ n, ¬ ∃ r, E.licensedEmits (D.stateOf (run D t n)) r ∧ E.nonnull r) := by
  have hffl : FalseFormalLegitimacyAt E (D.stateOf t) :=
    ffl_of_raw_nonnull_at_echo hsound hwit hecho hraw
  exact ⟨echo_forces_zero_deficit post (D.stateOf t) o₀ hecho μ ν hν1,
    hffl,
    ffl_not_confluentAt_source hnull hnullRaw hffl,
    run_mass D t,
    run_state D t,
    fun n => no_licensed_nonnull_at_any_run_depth hsound hwit D t hecho n⟩

/-! ## Combined echo-law structure -/

/-- The `EchoLawCrown` structure packages the echo classification, record exclusion, positive form, false-formal-legitimacy diagnosis, graph nonconfluence, dynamics, and dynamic law. -/
structure EchoLawCrown (E : Episode) : Prop where
  /-- Echo is equivalent to non-informativeness. -/
  classification : ∀ s : E.State, EchoAt E s ↔ ¬ InformativeAt E s
  /-- The law: an echo state emits no licensed non-null record. -/
  law : LicensedSound E → ObjectWitnessed E →
    ∀ s : E.State, EchoAt E s → ¬ ∃ r, E.licensedEmits s r ∧ E.nonnull r
  /-- The positive form: every licensed non-null record forces an exogenous channel. -/
  positive_form : LicensedSound E → ObjectWitnessed E →
    ∀ (s : E.State) (r : E.Record),
      E.licensedEmits s r → E.nonnull r → InformativeAt E s
  /-- The diagnosis: raw emission at an echo state is false formal legitimacy. -/
  diagnosis : LicensedSound E → ObjectWitnessed E →
    ∀ s : E.State, EchoAt E s → (∃ r, E.rawEmits s r ∧ E.nonnull r) →
      FalseFormalLegitimacyAt E s
  /-- False formal legitimacy implies that the raw emission graph is not confluent at the source. -/
  fork : ¬ E.nonnull E.null →
    ∀ s : E.State, E.rawEmits s E.null → FalseFormalLegitimacyAt E s →
      ¬ ConfluentAt (RawEmitStep E) (EmitNode.state s)
  /-- An `EchoDynamics` run increases mass by `n` and keeps the state fixed. -/
  trap : ∀ (D : EchoDynamics E) (t : D.Trace) (n : Nat),
    D.mass (run D t n) = D.mass t + n ∧ D.stateOf (run D t n) = D.stateOf t
  /-- An exogenous state either remains exogenous along `R` or reaches an echo state along `R`. -/
  dynamic : LicensedSound E → ObjectWitnessed E →
    ∀ (R : E.State → E.State → Prop) (s : E.State), Exogenous E s →
      PersistentExogenous E R s
        ∨ ∃ y, Relation.ReflTransGen R s y ∧ EchoAt E y
            ∧ ¬ ∃ r, E.licensedEmits y r ∧ E.nonnull r

/-- The preceding results provide an `EchoLawCrown` for every episode. -/
theorem echo_law_crown (E : Episode) : EchoLawCrown E where
  classification := echoAt_iff_not_informativeAt E
  law := fun hsound hwit _ hecho => no_licensed_nonnull_at_echo hsound hwit hecho
  positive_form := fun hsound hwit _ _ hemit hn =>
    nonnull_licensed_record_forces_informative_channel hsound hwit hemit hn
  diagnosis := fun hsound hwit _ hecho hraw =>
    ffl_of_raw_nonnull_at_echo hsound hwit hecho hraw
  fork := fun hnull _ hnullRaw hffl =>
    ffl_not_confluentAt_source hnull hnullRaw hffl
  trap := fun D t n => ⟨run_mass D t n, run_state D t n⟩
  dynamic := fun hsound hwit _ _ hs =>
    persistent_or_expired_at_named_state hsound hwit hs

end OperatorKO7.Meta.BoundaryGeneral.EchoForkTrapCrown
