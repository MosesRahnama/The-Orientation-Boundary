/-!
# Projection sensitivity, staticity, and provenance

A projection determines a statement when equal projected values imply equal truth values. If every base-derivable statement is determined by the reversible projection, every undetermined statement lies outside base derivability. The wrapper example gives one statement determined by the reversible coordinate and one statement that is not.

A projection record stores a dimension, license, and witness. If one-step changes preserve the license, and equal licenses determine the other two fields, all three fields are constant along a trace.

An answer stores optional support and license fields. Those fields are independent; the acceptance predicate requires a license. Exogenous gain consists of returned data outside downstream closure and is empty when all returned data lie in that closure.

Relation: abstract projections and answer records; no rewriting relation. Trust: kernel-only, with no `sorry`, `admit`, `axiom`, or native reduction.
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

/-- Separates a state into reversible and irreversible projections. -/
structure ProjectionLayers (Omega : Type u) (Rev : Type v) (Irr : Type w) where
  /-- The reversible projection, visible to base-layer derivations. -/
  projRev : Omega → Rev
  /-- The irreversible projection, whose content the base layer forgets. -/
  projIrr : Omega → Irr

/-- If every base-derivable statement is determined by the reversible projection, every statement not determined by that projection is not base-derivable. -/
theorem statements_not_determined_by_reversible_layer_lie_outside_base_derivability
    {Omega : Type u} {Rev : Type v} {Irr : Type w}
    (L : ProjectionLayers Omega Rev Irr)
    (derivable : (Omega → Prop) → Prop)
    (hbase : ∀ phi, derivable phi → DeterminedBy L.projRev phi)
    (phi : Omega → Prop) (hsens : NotDeterminedBy L.projRev phi) :
    ¬ derivable phi :=
  fun hd => hsens (hbase phi hd)

/-! ### Wrapper-state predicates -/

/-- A wrapper state stores a counter and wrapper multiplicity. -/
abbrev WrapperState : Type := Nat × Nat

/-- The projection retains the counter and records wrapper multiplicity separately. -/
def wrapperLayers : ProjectionLayers WrapperState Nat Nat where
  projRev := Prod.fst
  projIrr := Prod.snd

/-- The counter is exhausted when its value is zero. -/
def counterExhausted (s : WrapperState) : Prop := s.1 = 0

/-- The wrapper multiplicity is even when its remainder modulo two is zero. -/
def wrapperParityEven (s : WrapperState) : Prop := s.2 % 2 = 0

/-- Counter exhaustion is determined by the reversible projection. -/
theorem counterExhausted_is_determined_by_reversible_layer :
    DeterminedBy wrapperLayers.projRev counterExhausted := by
  intro x y hxy
  simp only [counterExhausted, wrapperLayers] at *
  rw [hxy]

/-- States `(0, 0)` and `(0, 1)` share a reversible coordinate and have different wrapper parity. -/
theorem wrapperParity_is_not_determined_by_reversible_layer :
    NotDeterminedBy wrapperLayers.projRev wrapperParityEven := by
  intro hdet
  have h := (hdet (0, 0) (0, 1) rfl).mp
  exact absurd (h rfl) (by simp [wrapperParityEven])

/-! ### Staticity from license invariance -/

/-- A projection record stores a dimension, license, and witness for each state. -/
structure ProjectionTransaction
    (State : Type u) (Dim License Witness : Type v) where
  /-- The retained dimension. -/
  dim : State → Dim
  /-- The external license. -/
  license : State → License
  /-- The forgetting witness. -/
  witness : State → Witness

/-- A projection record is static on a trace when its dimension, license, and witness agree at every pair of stages. -/
def IsStaticOn
    {State : Type u} {Dim License Witness : Type v}
    (T : ProjectionTransaction State Dim License Witness)
    (trace : Nat → State) : Prop :=
  ∀ m n,
    T.dim (trace m) = T.dim (trace n)
      ∧ T.license (trace m) = T.license (trace n)
      ∧ T.witness (trace m) = T.witness (trace n)

/-- If each step preserves the license, and equal licenses determine dimension and witness, then all three fields are constant along the trace. -/
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

/-- A constant projection record assigns unit values to its dimension, license, and witness. -/
def canonicalTransaction : ProjectionTransaction Nat Unit Unit Unit where
  dim := fun _ => ()
  license := fun _ => ()
  witness := fun _ => ()

/-- The constant projection record is static on every trace. -/
theorem canonicalTransaction_is_static (trace : Nat → Nat) :
    IsStaticOn canonicalTransaction trace :=
  static_of_stepInvariant_license canonicalTransaction trace
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

/-- A projection record with identity fields on the identity trace is not static. -/
theorem stepInvariance_hypothesis_is_load_bearing :
    ∃ (T : ProjectionTransaction Nat Nat Nat Nat) (trace : Nat → Nat),
      ¬ IsStaticOn T trace := by
  refine ⟨⟨id, id, id⟩, id, ?_⟩
  intro hstatic
  have := (hstatic 0 1).1
  exact absurd this (by decide)

/-! ### Provenance, license, and closure -/

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

/-- An answer can include a supporting span without a verdict license. -/
theorem provenance_does_not_entail_license :
    ∃ a : Answer Unit Unit, HasProvenance a ∧ ¬ IsLicensed a :=
  ⟨⟨some (), none⟩, rfl, by simp [IsLicensed]⟩

/-- An answer can have a verdict license without a supporting span. -/
theorem license_does_not_entail_provenance :
    ∃ a : Answer Unit Unit, IsLicensed a ∧ ¬ HasProvenance a :=
  ⟨⟨none, some ()⟩, rfl, by simp [HasProvenance]⟩

/-- The witness-first acceptance gate: a verdict is accepted only when the answer carries
its license. -/
def witnessFirstAccepts {Span License : Type u} (a : Answer Span License) : Bool :=
  a.license.isSome

/-- The acceptance predicate rejects an answer with a supporting span and no license. -/
theorem witnessFirst_rejects_provenance_without_license :
    ∃ a : Answer Unit Unit,
      HasProvenance a ∧ witnessFirstAccepts a = false :=
  ⟨⟨some (), none⟩, rfl, rfl⟩

/-- The exogenous part of a response: the returned data lying outside the downstream
closure of the source state. -/
def exogenousGain {D : Type u} [DecidableEq D]
    (closure returned : List D) : List D :=
  returned.filter (fun d => !closure.contains d)

/-- If every returned datum lies in the downstream closure, exogenous gain is empty. -/
theorem endogenous_provenance_collapse
    {D : Type u} [DecidableEq D] (closure returned : List D)
    (h : ∀ d ∈ returned, d ∈ closure) :
    exogenousGain closure returned = [] := by
  simp only [exogenousGain, List.filter_eq_nil_iff]
  intro d hd
  simp only [Bool.not_eq_true, Bool.not_eq_false', List.contains_iff_mem]
  exact h d hd

/-- A returned datum outside the downstream closure gives nonempty exogenous gain. -/
theorem exogenousGain_nonempty_off_closure :
    exogenousGain ([0] : List Nat) [1] = [1] := by
  decide

end OperatorKO7.Meta.BoundaryGeneral.ProjectionSensitivityAndProvenance
