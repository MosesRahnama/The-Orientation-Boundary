/-!
# Theory XI: Distinction as the record-generating primitive

Boundary-general cross-paper packet, Theory XI. Information is distinction. On a record-generating
surface that is *distinction-complete* (every non-null record requires distinct inputs), a
derivation using only equality premises cannot emit a non-null record, and every non-null record is
licensed by at least one distinction event `a ≠ b`. The reflexive diagonal `eqW a a` is therefore
record-inert.

This is the rewrite-level formalization of "inequality is the minimal information-generating
operation": in the KO7 kernel the only record-emitting equality rule is `eqW a b → integrate(merge
a b)`, which fires precisely on a distinction `a ≠ b`, while `eqW a a → void` emits nothing.

`equality_record_inert` and `nonnull_has_distinction` are the load-bearing theorems;
`ko7_distinctionComplete` instantiates the surface on a concrete `eqW` record model so the
statements are non-vacuous.

No `sorry`, `axiom`, or `native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord

/-! ### Abstract record-generating surface -/

/-- A record-generating surface: witness terms, a record type with a null record `void`, a
`nonnull` predicate, and an emission relation `emits a b r` ("inputs `a`, `b` emit record `r`"). -/
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

/-- **Equality is record-inert (Corollary 11.5).** On a distinction-complete surface, reflexive
(equal) inputs cannot emit a non-null record. -/
theorem equality_record_inert {S : RecordSurface} (h : DistinctionComplete S)
    {a : S.Witness} {r : S.Record} (he : S.emits a a r) : ¬ S.nonnull r := by
  intro hn
  exact h a a r he hn rfl

/-- **Every non-null record is licensed by a distinction (Theorem 11.4).** -/
theorem nonnull_has_distinction {S : RecordSurface} (h : DistinctionComplete S)
    {a b : S.Witness} {r : S.Record} (he : S.emits a b r) (hn : S.nonnull r) : a ≠ b :=
  h a b r he hn

/-- Distinction-completeness is exactly the absence of a non-null reflexive emission. This is the
paper-facing biconditional form of `equality_record_inert`. -/
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

/-! ### A concrete `eqW` record surface (non-vacuity) -/

/-- The KO7-style record: `void` (from `eqW a a → void`) or a `diff` record (from
`eqW a b → integrate(merge a b)` for `a ≠ b`). -/
inductive Rec (W : Type) where
  | void
  | diff (a b : W)

/-- Only `diff` records are non-null. -/
def Rec.nonnull {W : Type} : Rec W → Prop
  | .void => False
  | .diff _ _ => True

/-- KO7 `eqW` record surface: `eqW a a → void` (reflexive), `eqW a b → diff a b` for `a ≠ b`. The
emission relation directly encodes the two `eqW` rules of the kernel. -/
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

/-- **Non-vacuity.** On the concrete `eqW` surface, a reflexive `eqW a a` emission is record-inert:
it cannot produce a non-null record. -/
theorem ko7_equality_record_inert (W : Type) (a : W) {r : Rec W}
    (he : (ko7RecordSurface W).emits a a r) : ¬ (ko7RecordSurface W).nonnull r :=
  equality_record_inert (ko7_distinctionComplete W) he

/-! ### No-broadcasting: a branch certificate cannot be self-broadcast

A non-null record is the confluence-side *branch certificate* of a distinction. Broadcasting it means
producing two independent non-null records of the same comparison, the analogue of copying the certificate
into two independent pieces of evidence. On a distinction-complete surface this is impossible for a
self-comparison: the diagonal certificate is null, so there is nothing to broadcast. -/

/-- A **broadcast** of a comparison `(a, b)`: a pair of non-null records each emitted by `(a, b)`, i.e.
two independent certificates of the same distinction. -/
def Broadcasts (S : RecordSurface) (a b : S.Witness) (r₁ r₂ : S.Record) : Prop :=
  (S.emits a b r₁ ∧ S.nonnull r₁) ∧ (S.emits a b r₂ ∧ S.nonnull r₂)

/-- **No self-broadcast (Theorem 11.6).** On a distinction-complete surface a self-comparison `(a, a)`
admits no broadcast: there is no non-null record to duplicate into independent evidence. The diagonal
branch certificate is null and cannot be broadcast. -/
theorem no_self_broadcast {S : RecordSurface} (h : DistinctionComplete S) (a : S.Witness)
    (r₁ r₂ : S.Record) : ¬ Broadcasts S a a r₁ r₂ := by
  rintro ⟨⟨he₁, hn₁⟩, _⟩
  exact equality_record_inert h he₁ hn₁

/-- **Broadcasting requires a genuine distinction (Theorem 11.7).** Any broadcast of `(a, b)` forces
`a ≠ b`: two independent certificates can only certify a real distinction, never a self-comparison. -/
theorem broadcast_requires_distinction {S : RecordSurface} (h : DistinctionComplete S)
    {a b : S.Witness} {r₁ r₂ : S.Record} (hb : Broadcasts S a b r₁ r₂) : a ≠ b :=
  nonnull_has_distinction h hb.1.1 hb.1.2

/-- **Non-vacuity.** On the concrete `eqW` surface, distinct inputs `a ≠ b` genuinely broadcast: both
records can be the `diff a b` certificate, each non-null. So `Broadcasts` is inhabited for a real
distinction, and the no-self-broadcast obstruction is not vacuous. -/
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
