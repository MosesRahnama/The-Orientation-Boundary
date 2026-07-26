/-!
# Projection sensitivity, non-circular staticity, and the provenance propositions

Three manuscript statements are asserted with terms the paper never defines.

* The boundary-factorization proposition describes the boundary as the set of statements
  "sensitive to the irreversible projection", without defining sensitivity.
* The staticity proposition defines static as "the three ingredients hold constant across
  trace stages" and then proves constancy from the ingredients being fixed data, which is
  circular.
* The provenance subsection states three propositions in terms of license, supporting span,
  downstream closure and exogenous provenance gain, none of which are defined.

This module supplies each definition and proves each statement, with a witness for every
existential and a counterexample where a hypothesis is load bearing.

Relation: abstract projections and answer records; no rewriting relation is involved.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only. No `sorry`, no `admit`, no new `axiom`, no native reduction.
-/

set_option autoImplicit false

universe u v w

namespace OperatorKO7.Meta.BoundaryGeneral.ProjectionSensitivityAndProvenance

/-! ### Determination by a projection -/

/-- A statement is determined by a projection when the projection's value fixes its truth:
any two points with the same image agree on it. -/
def DeterminedBy {Omega : Type u} {O : Type v}
    (p : Omega → O) (phi : Omega → Prop) : Prop :=
  ∀ x y, p x = p y → (phi x ↔ phi y)

/-- A statement is undetermined by a projection when it fails to be determined by it, so
deciding it needs content the projection forgets. -/
def NotDeterminedBy {Omega : Type u} {O : Type v}
    (p : Omega → O) (phi : Omega → Prop) : Prop :=
  ¬ DeterminedBy p phi

/-- The two-layer projection structure: a reversible layer the base system computes with,
and an irreversible layer the licensed step deposits content into. -/
structure ProjectionLayers (Omega : Type u) (Rev : Type v) (Irr : Type w) where
  /-- The reversible projection, visible to base-layer derivations. -/
  projRev : Omega → Rev
  /-- The irreversible projection, whose content the base layer forgets. -/
  projIrr : Omega → Irr

/--
Intent: **the boundary-factorization theorem**. If every base-derivable statement is
determined by the reversible projection, then every statement that projection leaves
undetermined lies outside base derivability. That set is the boundary.

Relation: abstract derivability predicate.
Trust: kernel-only.
Non-vacuity witness: `wrapperParity_is_not_determined_by_reversible_layer`.
-/
theorem statements_not_determined_by_reversible_layer_lie_outside_base_derivability
    {Omega : Type u} {Rev : Type v} {Irr : Type w}
    (L : ProjectionLayers Omega Rev Irr)
    (derivable : (Omega → Prop) → Prop)
    (hbase : ∀ phi, derivable phi → DeterminedBy L.projRev phi)
    (phi : Omega → Prop) (hsens : NotDeterminedBy L.projRev phi) :
    ¬ derivable phi :=
  fun hd => hsens (hbase phi hd)

/-! ### The wrapper example, which witnesses both sides -/

/-- A trace state read as a pair: the retained counter coordinate and the accumulated
wrapper multiplicity. -/
abbrev WrapperState : Type := Nat × Nat

/-- The two-layer projection on wrapper states: the counter is reversible, the wrapper
multiplicity is the irreversible deposit. -/
def wrapperLayers : ProjectionLayers WrapperState Nat Nat where
  projRev := Prod.fst
  projIrr := Prod.snd

/-- "The counter has run out." -/
def counterExhausted (s : WrapperState) : Prop := s.1 = 0

/-- "The wrapper multiplicity is even." -/
def wrapperParityEven (s : WrapperState) : Prop := s.2 % 2 = 0

/--
Proves: the counter statement is determined by the reversible projection, so it is
available to the base layer.
-/
theorem counterExhausted_is_determined_by_reversible_layer :
    DeterminedBy wrapperLayers.projRev counterExhausted := by
  intro x y hxy
  simp only [counterExhausted, wrapperLayers] at *
  rw [hxy]

/--
Proves: the reversible projection leaves the wrapper statement undetermined, so by
`statements_not_determined_by_reversible_layer_lie_outside_base_derivability` it lies in
the boundary of any base layer computing with the reversible content alone.
Gate R5 non-vacuity witness for the boundary.
-/
theorem wrapperParity_is_not_determined_by_reversible_layer :
    NotDeterminedBy wrapperLayers.projRev wrapperParityEven := by
  intro hdet
  have h := (hdet (0, 0) (0, 1) rfl).mp
  exact absurd (h rfl) (by simp [wrapperParityEven])

/-! ### Staticity, without assuming what is to be proved -/

/-- A projection transaction: a retained dimension, an external license, and a forgetting
witness, each read off the current state. -/
structure ProjectionTransaction
    (State : Type u) (Dim License Witness : Type v) where
  /-- The retained dimension. -/
  dim : State → Dim
  /-- The external license. -/
  license : State → License
  /-- The forgetting witness. -/
  witness : State → Witness

/-- The transaction is static along a trace when all three ingredients agree at every pair
of stages. -/
def IsStaticOn
    {State : Type u} {Dim License Witness : Type v}
    (T : ProjectionTransaction State Dim License Witness)
    (trace : Nat → State) : Prop :=
  ∀ m n,
    T.dim (trace m) = T.dim (trace n)
      ∧ T.license (trace m) = T.license (trace n)
      ∧ T.witness (trace m) = T.witness (trace n)

/--
Intent: **staticity from one-step license invariance**. The hypotheses are that the license
is unchanged by a single rewrite step, and that the license determines the retained
dimension and the forgetting witness. The conclusion is global constancy across the whole
trace.

This replaces the circular argument, whose hypothesis was already the conclusion.

Trust: kernel-only.
Non-vacuity witness: `canonicalTransaction_is_static`.
-/
theorem static_of_stepInvariant_license
    {State : Type u} {Dim License Witness : Type v}
    (T : ProjectionTransaction State Dim License Witness)
    (trace : Nat → State)
    (hstep : ∀ n, T.license (trace (n + 1)) = T.license (trace n))
    (hdim : ∀ s s', T.license s = T.license s' → T.dim s = T.dim s')
    (hwitness : ∀ s s', T.license s = T.license s' → T.witness s = T.witness s') :
    IsStaticOn T trace := by
  have hconst : ∀ n, T.license (trace n) = T.license (trace 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => rw [hstep k, ih]
  intro m n
  have hmn : T.license (trace m) = T.license (trace n) := by
    rw [hconst m, hconst n]
  exact ⟨hdim _ _ hmn, hmn, hwitness _ _ hmn⟩

/-- The canonical transaction on the duplicator: one license, one retained dimension, one
forgetting witness. -/
def canonicalTransaction : ProjectionTransaction Nat Unit Unit Unit where
  dim := fun _ => ()
  license := fun _ => ()
  witness := fun _ => ()

/-- Gate R5 witness: the repaired staticity theorem applies to the canonical transaction. -/
theorem canonicalTransaction_is_static (trace : Nat → Nat) :
    IsStaticOn canonicalTransaction trace :=
  static_of_stepInvariant_license canonicalTransaction trace
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

/--
Proves: the one-step invariance hypothesis is load bearing. A transaction whose license
changes with the stage fails staticity, so the repaired theorem is not vacuous.
-/
theorem stepInvariance_hypothesis_is_load_bearing :
    ∃ (T : ProjectionTransaction Nat Nat Nat Nat) (trace : Nat → Nat),
      ¬ IsStaticOn T trace := by
  refine ⟨⟨id, id, id⟩, id, ?_⟩
  intro hstatic
  have := (hstatic 0 1).1
  exact absurd this (by decide)

/-! ### Provenance, license, and endogenous collapse -/

/-- An exported answer: an optional supporting span, and an optional verdict license. -/
structure Answer (Span License : Type u) where
  /-- The retrieved supporting span, when the system returned one. -/
  span : Option Span
  /-- The verdict license, when the system named one. -/
  license : Option License

/-- The answer carries provenance when it returns a supporting span. -/
def HasProvenance {Span License : Type u} (a : Answer Span License) : Prop :=
  a.span.isSome = true

/-- The answer is licensed when it names a verdict license. -/
def IsLicensed {Span License : Type u} (a : Answer Span License) : Prop :=
  a.license.isSome = true

/--
Intent: **provenance falls short of license**. There is an answer that returns a correct
supporting span and still fails to license the verdict it exports.

Trust: kernel-only.
-/
theorem provenance_does_not_entail_license :
    ∃ a : Answer Unit Unit, HasProvenance a ∧ ¬ IsLicensed a :=
  ⟨⟨some (), none⟩, rfl, by simp [IsLicensed]⟩

/--
Proves: the two properties are independent in both directions, so neither substitutes for
the other.
-/
theorem license_does_not_entail_provenance :
    ∃ a : Answer Unit Unit, IsLicensed a ∧ ¬ HasProvenance a :=
  ⟨⟨none, some ()⟩, rfl, by simp [HasProvenance]⟩

/-- The witness-first acceptance gate: a verdict is accepted only when the answer carries
its license. -/
def witnessFirstAccepts {Span License : Type u} (a : Answer Span License) : Bool :=
  a.license.isSome

/--
Proves: the gate rejects a provenance-bearing answer that names no license.
-/
theorem witnessFirst_rejects_provenance_without_license :
    ∃ a : Answer Unit Unit,
      HasProvenance a ∧ witnessFirstAccepts a = false :=
  ⟨⟨some (), none⟩, rfl, rfl⟩

/-- The exogenous part of a response: the returned data lying outside the downstream
closure of the source state. -/
def exogenousGain {D : Type u} [DecidableEq D]
    (closure returned : List D) : List D :=
  returned.filter (fun d => !closure.contains d)

/--
Intent: **endogenous provenance collapse**. When every returned datum already lies in the
downstream closure of the source state, the exogenous gain is empty.

Trust: kernel-only.
-/
theorem endogenous_provenance_collapse
    {D : Type u} [DecidableEq D] (closure returned : List D)
    (h : ∀ d ∈ returned, d ∈ closure) :
    exogenousGain closure returned = [] := by
  simp only [exogenousGain, List.filter_eq_nil_iff]
  intro d hd
  simp only [Bool.not_eq_true, Bool.not_eq_false', List.contains_iff_mem]
  exact h d hd

/--
Proves: the collapse hypothesis is load bearing. A response returning a datum outside the
closure has non-empty exogenous gain.
Gate R5 non-vacuity witness.
-/
theorem exogenousGain_nonempty_off_closure :
    exogenousGain ([0] : List Nat) [1] = [1] := by
  decide

end OperatorKO7.Meta.BoundaryGeneral.ProjectionSensitivityAndProvenance
