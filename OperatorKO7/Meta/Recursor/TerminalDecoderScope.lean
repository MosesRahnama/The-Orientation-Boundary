import OperatorKO7.Meta.Recursor.GaugeCost

/-!
# Scope of the terminal-record decoder, and why the sort separation is load bearing

`Meta/Recursor/GaugeCost.lean` proves decoder correctness and injectivity for canonical
`orbitState` records at positive depth, and its own header records that it does not prove
total decoding for every terminal term. The manuscript states the corresponding proposition
without that restriction: a total decoder recovering base identifier, payload identifier and
depth for every `G^K(Y, X)`, injective in all three data.

The unrestricted reading is false. If the base term may itself be a record frame carrying
the same payload, then `G^K(Y, G(Y, X')) = G^(K+1)(Y, X')`, and the triple is not recoverable.
`unsortedTerminalRecord_depth_not_recoverable` exhibits exactly that collision.

What rules the collision out in the artifact is the sort separation of the schema syntax:
`SchemaTerm.base` is a constructor distinct from `SchemaTerm.G`, so a base identifier is
never a record frame. `schemaTerm_base_is_never_frame_headed` records that fact, and
`decodeRecord_isSome_on_canonical_positive_depth` records the family on which the decoder is
total.

Relation: the schema term syntax and its record decoder.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only. No `sorry`, no `admit`, no new `axiom`, no native reduction.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Recursor.TerminalDecoderScope

open OperatorKO7.Meta.Recursor.SchemaTraceKernel
open OperatorKO7.Meta.Recursor.GaugeCost

/-! ### The sort separation that makes decoding well posed -/

/--
Proves: in the schema syntax a base identifier is never a record frame, so the peeling
decoder cannot mistake part of the base term for an emitted frame.

This is the hypothesis the manuscript's proposition needs and had dropped.
-/
theorem schemaTerm_base_is_never_frame_headed (ia : Nat) (x y : SchemaTerm) :
    (SchemaTerm.base ia) ≠ SchemaTerm.G x y := by
  intro h
  exact SchemaTerm.noConfusion h

/--
Proves: a payload identifier is likewise never a record frame.
-/
theorem schemaTerm_pay_is_never_frame_headed (ib : Nat) (x y : SchemaTerm) :
    (SchemaTerm.pay ib) ≠ SchemaTerm.G x y := by
  intro h
  exact SchemaTerm.noConfusion h

/--
Proves: the decoder is defined on every canonical terminal record of positive depth, which
is the family the manuscript's proposition should quantify over.
-/
theorem decodeRecord_isSome_on_canonical_positive_depth
    (ia ib k : Nat) (hk : 1 ≤ k) :
    (decodeRecord (orbitState (.base ia) (.pay ib) k (k + 1))).isSome = true := by
  rw [L9_decode_correct ia ib k hk]
  rfl

/-! ### Without the sort separation the decoder is not injective -/

/-- A record syntax with no sort separation: the base slot accepts any record, including a
record frame. This is the syntax the manuscript's unrestricted statement presupposes. -/
inductive UnsortedRecord : Type
  | leaf : Nat → UnsortedRecord
  | frame : Nat → UnsortedRecord → UnsortedRecord
deriving DecidableEq, Repr

/-- `K` record frames carrying payload `p`, wrapped around a base record. -/
def gStack (p : Nat) : Nat → UnsortedRecord → UnsortedRecord
  | 0, t => t
  | k + 1, t => .frame p (gStack p k t)

/--
Intent: **the collision**. Without the sort separation, two record configurations of
different depth and different base term produce the same terminal record, so no decoder
recovers the depth, and the terminal-record map fails injectivity.

Trust: kernel-only.
-/
theorem unsortedTerminalRecord_depth_not_recoverable :
    ∃ (p : Nat) (X X' : UnsortedRecord) (K K' : Nat),
      K ≠ K' ∧ X ≠ X' ∧ gStack p K X = gStack p K' X' := by
  refine ⟨0, .frame 0 (.leaf 0), .leaf 0, 0, 1, by omega, ?_, rfl⟩
  intro h
  exact UnsortedRecord.noConfusion h

/--
Proves: the collision is exactly the configuration the sort separation excludes, namely a
base slot that is itself frame headed with the same payload.
-/
theorem unsortedTerminalRecord_collision_is_frame_headed_base :
    ∃ (p : Nat) (X' : UnsortedRecord),
      gStack p 0 (.frame p X') = gStack p 1 X' :=
  ⟨0, .leaf 0, rfl⟩

/--
Proves: once the base slot is barred from being frame headed, the depth is recoverable at
the one place the collision could arise. This is the repaired hypothesis in its usable form.
-/
theorem gStack_succ_ne_of_base_not_frame_headed
    (p : Nat) (X X' : UnsortedRecord)
    (hbase : ∀ q Y, X ≠ .frame q Y) (K : Nat) :
    gStack p 0 X ≠ gStack p (K + 1) X' := by
  intro h
  exact hbase p (gStack p K X') h

end OperatorKO7.Meta.Recursor.TerminalDecoderScope
