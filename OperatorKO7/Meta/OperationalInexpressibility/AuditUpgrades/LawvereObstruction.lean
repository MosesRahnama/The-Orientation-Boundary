import OperatorKO7.Meta.LawvereYanofskySeparation

/-!
# Lawvere obstruction on the code object of the dependency-pair confession

Proves: Lawvere's fixed-point theorem for a weakly point-surjective evaluation; no code type
carries a diagonal instance with a point-surjective evaluation and a fixed-point-free endomap;
on the one-node code object of the extracted-pair certificate every point-surjective evaluation
has a one-element value type, on which every endomap is the identity. Control: without
point-surjectivity a diagonal datum on that code object exists, and the successor constructor
of the kernel is fixed-point-free, so the obstruction rests on the evaluation side of the schema.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the code object is the node type of `primitiveDuplicatorFinitePairGraphCertificate`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.LawvereObstruction

open OperatorKO7
open OperatorKO7.LawvereYanofskySeparation

/-- Weak point-surjectivity: every map from codes to values is represented pointwise by a code. -/
def WeaklyPointSurjective {Code Value : Type} (evaluate : Code → Code → Value) : Prop :=
  ∀ f : Code → Value, ∃ c : Code, ∀ x : Code, evaluate c x = f x

/-- Lawvere's fixed-point theorem: under a weakly point-surjective evaluation every endomap of
the value type has a fixed point. -/
theorem lawvere_fixed_point {Code Value : Type} (evaluate : Code → Code → Value)
    (h : WeaklyPointSurjective evaluate) (g : Value → Value) : ∃ v : Value, g v = v := by
  obtain ⟨c, hc⟩ := h (fun x => g (evaluate x x))
  exact ⟨evaluate c c, (hc c).symm⟩

/-- A diagonal instance: a point-surjective evaluation and a fixed-point-free endomap of its values. -/
structure PointSurjectiveDiagonalInstance (Code Value : Type) where
  evaluate : Code → Code → Value
  pointSurjective : WeaklyPointSurjective evaluate
  endomap : Value → Value
  fixedPointFree : ∀ v : Value, endomap v ≠ v

/-- No code type carries a point-surjective diagonal instance. -/
theorem no_pointSurjectiveDiagonalInstance (Code Value : Type) :
    IsEmpty (PointSurjectiveDiagonalInstance Code Value) :=
  ⟨fun D => by
    obtain ⟨v, hv⟩ := lawvere_fixed_point D.evaluate D.pointSurjective D.endomap
    exact D.fixedPointFree v hv⟩

/-- The code object of the dependency-pair confession is the one-node type of its extracted pair. -/
theorem confession_code_object_eq_pairNode :
    primitiveDuplicatorDpConfessionStructure.pairCertificate.Node =
      PrimitiveDuplicatorPairNode := rfl

/-- On the one-node code object a point-surjective evaluation has a one-element value type. -/
theorem pairNode_pointSurjective_values_subsingleton {Value : Type}
    (evaluate : PrimitiveDuplicatorPairNode → PrimitiveDuplicatorPairNode → Value)
    (h : WeaklyPointSurjective evaluate) (v w : Value) : v = w := by
  obtain ⟨c, hc⟩ := h (fun _ => v)
  obtain ⟨d, hd⟩ := h (fun _ => w)
  have hcv : evaluate c .recSucc = v := hc .recSucc
  have hdw : evaluate d .recSucc = w := hd .recSucc
  cases c
  cases d
  exact hcv.symm.trans hdw

/-- On the one-node code object every endomap of the values of a point-surjective evaluation is
the identity. -/
theorem pairNode_pointSurjective_endomap_eq_id {Value : Type}
    (evaluate : PrimitiveDuplicatorPairNode → PrimitiveDuplicatorPairNode → Value)
    (h : WeaklyPointSurjective evaluate) (g : Value → Value) (v : Value) : g v = v :=
  pairNode_pointSurjective_values_subsingleton evaluate h (g v) v

/-- No point-surjective diagonal instance exists on the code object of the confession. -/
theorem no_pointSurjectiveDiagonal_on_confession_code_object (Value : Type) :
    IsEmpty (PointSurjectiveDiagonalInstance
      primitiveDuplicatorDpConfessionStructure.pairCertificate.Node Value) :=
  no_pointSurjectiveDiagonalInstance _ Value

/-- Control: without point-surjectivity a diagonal datum on the one-node code object exists, the
constant evaluation into `Bool` with Boolean negation; point-surjectivity carries the obstruction. -/
theorem pairNode_diagonal_datum_without_surjectivity_exists :
    ∃ (evaluate : PrimitiveDuplicatorPairNode → PrimitiveDuplicatorPairNode → Bool)
      (endomap : Bool → Bool),
      (∀ v : Bool, endomap v ≠ v) ∧ ¬ WeaklyPointSurjective evaluate := by
  refine ⟨fun _ _ => true, not, ?_, ?_⟩
  · intro v
    cases v <;> decide
  · intro h
    obtain ⟨c, hc⟩ := h (fun _ => false)
    have hx := hc c
    simp at hx

/-- Control: the successor constructor of the kernel is a fixed-point-free endomap of terms. -/
theorem trace_delta_fixedPointFree (t : Trace) : Trace.delta t ≠ t := by
  intro h
  have h1 := congrArg sizeOf h
  simp only [Trace.delta.sizeOf_spec] at h1
  omega

end OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.LawvereObstruction
