import OperatorKO7.Meta.BoundaryObserver.DiagonalObservation

/-!
# A partial-value completion of self-evaluation

Proof graph: OBSERVATION-EXTENSIONS-PROOF-GRAPH.md, PS1.
Reading ledger: SYN-012 and SYN-014. Values are Option Bool; none is an unresolved result,
not a certificate of undecidability or nontermination. The interpreter itself is total.
The semantic equations are instantiated by a nonconstant two-code table.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation

/-- Negation fixes the unresolved value and exchanges the two definite values. -/
def negate : Option Bool → Option Bool
  | none => none
  | some b => some (!b)

theorem negate_none : negate none = none := rfl

theorem negate_some (b : Bool) : negate (some b) = some (!b) := rfl

theorem negate_involutive (v : Option Bool) : negate (negate v) = v := by
  cases v with
  | none => rfl
  | some b => cases b <;> rfl

/-- None is the only fixed point of the extended negation. -/
theorem negate_fixed_iff (v : Option Bool) : negate v = v ↔ v = none := by
  cases v with
  | none => exact iff_of_true rfl rfl
  | some b => cases b <;> decide

/-- An exact self-evaluation code in a negation-closed language is unresolved at the
negation of that code. No incompleteness or unresolved-output premise is assumed. -/
theorem self_evaluation_forces_none {C : Type*} (eval : C → C → Option Bool)
    (negCode : C → C) (hneg : ∀ c x, eval (negCode c) x = negate (eval c x))
    (s : C) (hself : ∀ c, eval s c = eval c c) :
    eval s (negCode s) = none ∧ eval (negCode s) (negCode s) = none := by
  have hfix : negate (eval s (negCode s)) = eval s (negCode s) :=
    (hneg s (negCode s)).symm.trans (hself (negCode s)).symm
  have hn := (negate_fixed_iff _).mp hfix
  exact ⟨hn, (hself (negCode s)).symm.trans hn⟩

/-- The two-code interpreter. False denotes the self-evaluation row, true its negation. -/
def witnessEval : Bool → Bool → Option Bool
  | c, false => some (!c)
  | _, true => none

theorem witnessEval_false (c : Bool) : witnessEval c false = some (!c) := rfl

theorem witnessEval_true (c : Bool) : witnessEval c true = none := rfl

theorem witness_negation (c x : Bool) : witnessEval (!c) x = negate (witnessEval c x) := by
  cases c <;> cases x <;> rfl

theorem witness_self_evaluation (c : Bool) : witnessEval false c = witnessEval c c := by
  cases c <;> rfl

/-- Both premises hold while the interpreter still supplies definite information. -/
theorem nonconstant_completion :
    (∀ c x, witnessEval (!c) x = negate (witnessEval c x)) ∧
    (∀ c, witnessEval false c = witnessEval c c) ∧
    witnessEval false false = some true ∧ witnessEval true false = some false ∧
    witnessEval false true = none :=
  ⟨witness_negation, witness_self_evaluation, rfl, rfl, rfl⟩

/-- A map commuting with the operations cannot send a fixed point into a fixed-point-free
carrier. This is the exact obstruction to an all-definite release preserving negation. -/
theorem no_readout_from_fixed_point {X Y : Type*} (f : X → X) (g : Y → Y)
    (x : X) (hx : f x = x) (hg : ∀ y, g y ≠ y) :
    ¬ ∃ h : X → Y, ∀ z, h (f z) = g (h z) := by
  rintro ⟨h, he⟩
  exact hg (h x) ((he x).symm.trans (congrArg h hx))

theorem no_total_boolean_readout :
    ¬ ∃ h : Option Bool → Bool, ∀ v, h (negate v) = !(h v) :=
  no_readout_from_fixed_point negate Bool.not none rfl (by intro b; cases b <;> decide)

/-- Restricting the readout to definite records gives an exact inverse, including negation. -/
theorem definite_readout (b : Bool) :
    (some b : Option Bool).getD false = b ∧ (negate (some b)).getD false = !b := by
  cases b <;> exact ⟨rfl, rfl⟩

/-- One operation on the enlarged output type is again fixed-point-free. -/
def cycle : Option Bool → Option Bool
  | none => some false
  | some false => some true
  | some true => none

theorem cycle_has_no_fixed_point (v : Option Bool) : cycle v ≠ v := by
  cases v with
  | none => decide
  | some b => cases b <;> decide

/-- The positive completion is relative to negation, not to every output operation. -/
theorem cycle_closed_language_has_no_self_evaluator {C : Type*}
    (eval : C → C → Option Bool) (cycleCode : C → C)
    (hcycle : ∀ c x, eval (cycleCode c) x = cycle (eval c x)) :
    ¬ ∃ s, ∀ c, eval s c = eval c c :=
  DiagonalObservation.no_internal_self_evaluator eval cycle cycle_has_no_fixed_point
    cycleCode hcycle

end OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation
