/-!
# Distinction and record generation

A `RecordSurface` assigns records to pairs of terms. `DistinctionComplete` states that every emitted non-null record has distinct inputs. Under this condition, equal inputs cannot emit a non-null record, and every non-null emitted record certifies an inequality.

The concrete `ko7RecordSurface` maps equal inputs to `void` and distinct inputs to `diff a b`. `ko7_distinctionComplete` proves this surface is distinction-complete. `Broadcasts` requires two non-null records emitted for the same comparison. `no_self_broadcast` excludes this for equal inputs, while `broadcast_requires_distinction` proves that a broadcast requires distinct inputs. On the concrete surface, distinct inputs can use `diff a b` for both records.

Trust: no `sorry`, `axiom`, or `native_decide` occurs in this module.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord

/-! ### Abstract record-generating surface -/

/-- A record surface with a term type, record type, null record `void`, `nonnull` predicate, and emission relation `emits`. -/
structure RecordSurface where
  Witness : Type
  Record : Type
  void : Record
  nonnull : Record → Prop
  emits : Witness → Witness → Record → Prop

/-- The surface is *distinction-complete* when every non-null emitted record requires distinct
inputs: a non-null output can only arise from a genuine distinction `a ≠ b`. -/
def DistinctionComplete (S : RecordSurface) : Prop :=
  ∀ a b r, S.emits a b r → S.nonnull r → a ≠ b

/-- On a distinction-complete surface, equal inputs cannot emit a non-null record. -/
theorem equality_record_inert {S : RecordSurface} (h : DistinctionComplete S)
    {a : S.Witness} {r : S.Record} (he : S.emits a a r) : ¬ S.nonnull r := by
  intro hn
  exact h a a r he hn rfl

/-- Every non-null emitted record requires distinct inputs on a distinction-complete surface. -/
theorem nonnull_has_distinction {S : RecordSurface} (h : DistinctionComplete S)
    {a b : S.Witness} {r : S.Record} (he : S.emits a b r) (hn : S.nonnull r) : a ≠ b :=
  h a b r he hn

/-- Distinction completeness holds exactly when no reflexive input pair emits a non-null record. -/
theorem distinctionComplete_iff_no_reflexive_nonnull (S : RecordSurface) :
    DistinctionComplete S ↔
      ¬ ∃ (a : S.Witness) (r : S.Record), S.emits a a r ∧ S.nonnull r := by
  constructor
  · intro h hdiag
    rcases hdiag with ⟨a, r, he, hn⟩
    exact h a a r he hn rfl
  · intro h a b r he hn hab
    subst b
    exact h ⟨a, r, he, hn⟩

/-! ### Concrete `eqW` record surface -/

/-- The record type has a null case `void` and a pair case `diff a b`. -/
inductive Rec (W : Type) where
  | void
  | diff (a b : W)

/-- Only `diff` records are non-null. -/
def Rec.nonnull {W : Type} : Rec W → Prop
  | .void => False
  | .diff _ _ => True

/-- The concrete surface maps equal inputs to `void` and distinct inputs to `diff a b`. -/
def ko7RecordSurface (W : Type) : RecordSurface where
  Witness := W
  Record := Rec W
  void := Rec.void
  nonnull := Rec.nonnull
  emits := fun a b r => (a = b ∧ r = Rec.void) ∨ (a ≠ b ∧ r = Rec.diff a b)

/-- The concrete `eqW` record surface is distinction-complete. -/
theorem ko7_distinctionComplete (W : Type) : DistinctionComplete (ko7RecordSurface W) := by
  intro a b r he hn
  rcases he with ⟨_, hv⟩ | ⟨hne, _⟩
  · subst hv
    exact (hn : False).elim
  · exact hne

/-- On the concrete `eqW` surface, equal inputs cannot emit a non-null record. -/
theorem ko7_equality_record_inert (W : Type) (a : W) {r : Rec W}
    (he : (ko7RecordSurface W).emits a a r) : ¬ (ko7RecordSurface W).nonnull r :=
  equality_record_inert (ko7_distinctionComplete W) he

/-! ### Broadcasting from record surfaces

A broadcast consists of two non-null records emitted by the same input pair. Distinction completeness rules out a self-broadcast because equal inputs cannot emit a non-null record. -/

/-- A broadcast of `(a, b)` is a pair of non-null records each emitted by `(a, b)`. -/
def Broadcasts (S : RecordSurface) (a b : S.Witness) (r₁ r₂ : S.Record) : Prop :=
  (S.emits a b r₁ ∧ S.nonnull r₁) ∧ (S.emits a b r₂ ∧ S.nonnull r₂)

/-- On a distinction-complete surface, equal inputs cannot emit a pair of non-null records. -/
theorem no_self_broadcast {S : RecordSurface} (h : DistinctionComplete S) (a : S.Witness)
    (r₁ r₂ : S.Record) : ¬ Broadcasts S a a r₁ r₂ := by
  rintro ⟨⟨he₁, hn₁⟩, _⟩
  exact equality_record_inert h he₁ hn₁

/-- Every broadcast on a distinction-complete surface requires distinct inputs. -/
theorem broadcast_requires_distinction {S : RecordSurface} (h : DistinctionComplete S)
    {a b : S.Witness} {r₁ r₂ : S.Record} (hb : Broadcasts S a b r₁ r₂) : a ≠ b :=
  nonnull_has_distinction h hb.1.1 hb.1.2

/-- On the concrete `eqW` surface, distinct inputs can use `diff a b` for both emitted non-null records. -/
theorem ko7_broadcast_of_distinct (W : Type) {a b : W} (hab : a ≠ b) :
    Broadcasts (ko7RecordSurface W) a b (Rec.diff a b) (Rec.diff a b) :=
  ⟨⟨Or.inr ⟨hab, rfl⟩, trivial⟩, ⟨Or.inr ⟨hab, rfl⟩, trivial⟩⟩

#print axioms equality_record_inert
#print axioms distinctionComplete_iff_no_reflexive_nonnull
#print axioms ko7_equality_record_inert
#print axioms no_self_broadcast
#print axioms broadcast_requires_distinction
#print axioms ko7_broadcast_of_distinct

end OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord
