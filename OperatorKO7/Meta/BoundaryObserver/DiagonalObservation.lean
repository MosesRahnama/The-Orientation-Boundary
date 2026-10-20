import OperatorKO7.Meta.BoundaryObserver.MergedPair

set_option autoImplicit false

/-!
# The diagonal boundary of a self-observer

Graph: `Audit/ledgers/operational-inexpressibility/TWO-VOIDS-PROOF-GRAPH.md`, M16.
This constructs the missing diagonal predicate from an evaluator. A total observer whose codes
belong to the object type cannot represent all predicates on that type. An internal code for
self-evaluation is also impossible when the code language is closed under an output operation
without fixed points. Boolean negation supplies the concrete instance.
Relation: exact evaluation of total predicates, not a theorem of arithmetic completeness.
Trust: kernel-only. No System T implementation is duplicated.
-/

namespace OperatorKO7.Meta.BoundaryObserver.DiagonalObservation

/-- A predicate is represented when a code has that predicate as its exact semantics. -/
def Represented {C X V : Type*} (eval : C → X → V) (p : X → V) : Prop :=
  ∃ c, eval c = p

/-- Change the answer of a code applied to itself. -/
def diagonal {C V : Type*} (eval : C → C → V) (change : V → V) : C → V :=
  fun c => change (eval c c)

/-- A fixed-point-free change of the diagonal is not represented by any object code. -/
theorem diagonal_not_represented {C V : Type*} (eval : C → C → V) (change : V → V)
    (hchange : ∀ v, change v ≠ v) : ¬ Represented eval (diagonal eval change) := by
  rintro ⟨c, hc⟩
  exact hchange (eval c c) (congrFun hc c).symm

/-- No object-coded total evaluator enumerates all predicates when the output admits a
fixed-point-free operation. This includes empty code types. -/
theorem evaluator_not_surjective {C V : Type*} (eval : C → C → V) (change : V → V)
    (hchange : ∀ v, change v ≠ v) : ¬ Function.Surjective eval := by
  intro h
  exact diagonal_not_represented eval change hchange (h (diagonal eval change))

/-- The missing predicate for a Boolean evaluator is explicit, not merely existential. -/
theorem boolean_diagonal_missing {C : Type*} (eval : C → C → Bool) :
    ¬ Represented eval (fun c => !(eval c c)) :=
  diagonal_not_represented eval Bool.not (by intro b; cases b <;> decide)

/-- An arbitrary proposed quotation function fails on its own diagonal predicate at a stated
input, namely the quotation of that predicate. -/
theorem quotation_fails_at_diagonal {C V : Type*} (eval : C → C → V) (quote : (C → V) → C)
    (change : V → V) (hchange : ∀ v, change v ≠ v) :
    eval (quote (diagonal eval change)) (quote (diagonal eval change)) ≠
      diagonal eval change (quote (diagonal eval change)) := by
  intro h
  exact hchange _ h.symm

/-- A code language closed under a fixed-point-free change of output cannot contain an exact
self-evaluation code. The two stated semantic laws are the premises; incompleteness is not a
premise. -/
theorem no_internal_self_evaluator {C V : Type*} (eval : C → C → V)
    (change : V → V) (hchange : ∀ v, change v ≠ v) (negCode : C → C)
    (hneg : ∀ c x, eval (negCode c) x = change (eval c x)) :
    ¬ ∃ d, ∀ c, eval d c = eval c c := by
  rintro ⟨d, hd⟩
  have h : eval d (negCode d) = change (eval d (negCode d)) :=
    (hd (negCode d)).trans (hneg d (negCode d))
  exact hchange _ h.symm

/-- Boolean negation gives the self-evaluation obstruction for total Boolean code semantics. -/
theorem no_internal_boolean_self_evaluator {C : Type*} (eval : C → C → Bool)
    (negCode : C → C) (hneg : ∀ c x, eval (negCode c) x = !(eval c x)) :
    ¬ ∃ d, ∀ c, eval d c = eval c c :=
  no_internal_self_evaluator eval Bool.not (by intro b; cases b <;> decide) negCode hneg

/-- Changing the record type does not erase the diagonal obstruction when every report still
comes from a code in the object type. -/
theorem no_complete_same_carrier_observer {C R : Type*} (observe : C → R)
    (read : R → C → Bool) : ¬ ∀ p : C → Bool, ∃ c, ∀ x, read (observe c) x = p x := by
  intro h
  apply boolean_diagonal_missing (fun c => read (observe c))
  obtain ⟨c, hc⟩ := h (fun x => !(read (observe x) x))
  exact ⟨c, funext hc⟩

/-- Predicates themselves form an exact external record type for all predicates on the object
carrier. No encoding of that whole type back into object codes is assumed. -/
def externalRead {C V : Type*} (p : C → V) (x : C) : V := p x

/-- The external function record reads every predicate exactly. -/
theorem externalRead_complete {C V : Type*} (p : C → V) :
    ∃ r : C → V, ∀ x, externalRead r x = p x := ⟨p, fun _ => rfl⟩

/-- There is no semantics-preserving quotation of every external Boolean function into codes
of the original object type under a fixed total evaluator. -/
theorem no_total_quote_back {C : Type*} (eval : C → C → Bool) :
    ¬ ∃ quote : (C → Bool) → C, ∀ p x, eval (quote p) x = externalRead p x := by
  rintro ⟨quote, hquote⟩
  exact quotation_fails_at_diagonal eval quote Bool.not
    (by intro b; cases b <;> decide) (hquote _ _)

/-- Two distinct syntactic codes admit a decidable separator. This is not a uniform procedure
for computing the semantics of all codes. -/
theorem fixed_pair_separator {C : Type*} [DecidableEq C] {a b : C} (hab : a ≠ b) :
    ∃ test : C → Bool, test a = true ∧ test b = false := by
  refine ⟨fun x => decide (x = a), by simp, ?_⟩
  simp [hab.symm]

/-- Fixed-pair separation and the diagonal failure of a uniform evaluator hold together. -/
theorem pair_separation_not_uniform_truth {C : Type*} [DecidableEq C] {a b : C} (hab : a ≠ b)
    (eval : C → C → Bool) :
    (∃ test : C → Bool, test a = true ∧ test b = false) ∧
      ¬ Represented eval (fun c => !(eval c c)) :=
  ⟨fixed_pair_separator hab, boolean_diagonal_missing eval⟩

/-- Without closure under negation an internal self-evaluation code can exist: the one-code
constant language supplies the positive control. -/
theorem constant_language_has_self_evaluator :
    ∃ d : Unit, ∀ c : Unit, (fun _ _ : Unit => false) d c =
      (fun _ _ : Unit => false) c c := ⟨(), fun _ => rfl⟩

end OperatorKO7.Meta.BoundaryObserver.DiagonalObservation
