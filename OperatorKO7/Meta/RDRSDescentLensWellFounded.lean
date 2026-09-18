import OperatorKO7.Meta.RDRSDescentLens

/-!
# The descent lens with codomain well-foundedness

`Meta/RDRSDescentLens.lean` states the lens interface with a codomain order `leB` and no
well-foundedness requirement on it. That is enough for the local contradiction
(`no_orients_of_lens_violation`): a single violated step refutes orientation. It is not enough for
the global statement the lens is usually read as making, that a successful lens rules out an
infinite run.

This module adds the missing datum as a field rather than leaving it outside the interface. A
`WellFoundedDescentLens` carries a strict codomain order together with a proof that it is well
founded, and a clause saying that a strict decrease upstairs forces a strict decrease downstairs.
With that field the global statement is a theorem: `no_infinite_stepChain_of_wellFounded_lens`
says an oriented step relation has no infinite chain, and `wellFounded_projected_step` gives the
closed form, that the reverse of the projected relation is well founded.

The field is load-bearing. `increasingLens` is a compiled lens whose codomain order is the reverse
order on the naturals, which is not well founded, and `increasingLens_has_infinite_chain` exhibits
the infinite chain it admits. Dropping the well-foundedness field therefore makes the global
statement false, not merely unproved.

Relation: the RDRS step interface. Closure: root.
External trust: none. Mathlib only.
-/

namespace OperatorKO7.RDRSDescentLens

variable {B S N T A : Type}

/-! ## No infinite descending sequence in a well-founded order -/

/-- A well-founded relation admits no infinite descending sequence. -/
theorem no_descending_seq {α : Type} {r : α → α → Prop} (hwf : WellFounded r)
    (f : Nat → α) (hf : ∀ n, r (f (n + 1)) (f n)) : False := by
  have key : ∀ a : α, ∀ n : Nat, f n ≠ a := by
    intro a
    induction hwf.apply a with
    | intro x _ ih =>
        intro n hn
        exact ih (f (n + 1)) (hn ▸ hf n) (n + 1) rfl
  exact key (f 0) 0 rfl

/-! ## The interface with the missing field -/

/-- A descent lens whose codomain carries a well-founded strict order, and whose strict clause
transports strict decrease from the measure to the projection. The three added fields are exactly
what the global reading of the lens needs and what the original interface left outside. -/
structure WellFoundedDescentLens
    (R : RDRSStep B S N T) (μ : T → A) (ltA : A → A → Prop)
    extends DescentLens R μ ltA where
  /-- The strict codomain order. -/
  ltB : Bq → Bq → Prop
  /-- It is well founded. -/
  wf : WellFounded ltB
  /-- A strict decrease upstairs forces a strict decrease downstairs. -/
  strict_of_lt :
    ∀ b s n,
      ltA (μ (R.rhs b s n)) (μ (R.lhs b s n)) →
        ltB (q (R.rhs b s n)) (q (R.lhs b s n))

/-- **The closed form.** The reverse of the projected relation on the source type is well founded,
so the lens bounds the run and not only one step. -/
theorem wellFounded_projected_step
    {R : RDRSStep B S N T} {μ : T → A} {ltA : A → A → Prop}
    (L : WellFoundedDescentLens R μ ltA) :
    WellFounded (fun x y : T => L.ltB (L.q x) (L.q y)) :=
  InvImage.wf L.q L.wf

/-- A chain of steps of the RDRS interface. -/
def StepChain (R : RDRSStep B S N T) (f : Nat → T) : Prop :=
  ∀ i : Nat, ∃ b s n, f i = R.lhs b s n ∧ f (i + 1) = R.rhs b s n

/-- **No infinite run.** If the step relation is oriented and a well-founded lens exists, there is
no infinite chain of steps. This is the statement the lens interface was read as making, now
proved from the interface rather than assumed beside it. -/
theorem no_infinite_stepChain_of_wellFounded_lens
    {R : RDRSStep B S N T} {μ : T → A} {ltA : A → A → Prop}
    (L : WellFoundedDescentLens R μ ltA) (hOrients : Orients R μ ltA)
    (f : Nat → T) (hf : StepChain R f) : False := by
  refine no_descending_seq (wellFounded_projected_step L) f ?_
  intro n
  obtain ⟨b, s, m, hl, hr⟩ := hf n
  have hstrict := L.strict_of_lt b s m (hOrients b s m)
  rw [hl, hr]
  exact hstrict

/-- Every well-founded lens is in particular a lens, so nothing proved with the old interface is
lost. -/
theorem wellFoundedDescentLens_is_descentLens
    {R : RDRSStep B S N T} {μ : T → A} {ltA : A → A → Prop}
    (L : WellFoundedDescentLens R μ ltA) :
    ∀ b s n,
      ltA (μ (R.rhs b s n)) (μ (R.lhs b s n)) →
        L.leB (L.q (R.rhs b s n)) (L.q (R.lhs b s n)) :=
  L.nonincrease_of_lt

/-! ## The well-foundedness field is load-bearing -/

/-- The one-step interface on the naturals whose right-hand side is the successor. -/
def natStep : RDRSStep Unit Unit Nat Nat where
  lhs := fun _ _ n => n
  rhs := fun _ _ n => n + 1

/-- A lens on that interface whose codomain order is the reverse order on the naturals, which is
not well founded. Its non-increase clause holds because every successor pair is non-increasing in
that reverse order, so it is a legitimate `DescentLens`. -/
def increasingLens :
    DescentLens natStep (fun n => n) (fun x y => x = y + 1) where
  Bq := Nat
  leB := fun x y => y ≤ x
  q := fun n => n
  nonincrease_of_lt := by
    intro _ _ n _
    omega

/-- The counterexample relation is genuinely oriented by the measure carried by
`increasingLens`; the infinite run below is therefore not an artifact of a failed orientation
premise. -/
theorem natStep_orients_increasing :
    Orients natStep (fun n => n) (fun x y => x = y + 1) := by
  intro _ _ n
  rfl

/-- **The infinite chain the reverse order admits.** The identity chain on the naturals is a step
chain of `natStep`, and the projection increases along it forever. A lens without the
well-foundedness field therefore does not bound the run. -/
theorem increasingLens_has_infinite_chain :
    StepChain natStep (fun n => n) := by
  intro i
  exact ⟨(), (), i, rfl, rfl⟩

/-- The reverse order on the naturals is not well founded, which is exactly the field the extended
interface adds. -/
theorem reverse_nat_order_not_wellFounded :
    ¬ WellFounded (fun x y : Nat => y < x) := by
  intro hwf
  exact no_descending_seq hwf (fun n => n) (fun n => Nat.lt_succ_self n)

/-- Exact counterexample to deleting codomain well-foundedness: the old lens exists, its measure
strictly orients every step, an infinite step chain exists, and the projected strict order is not
well founded. -/
theorem descentLens_without_wellFoundedness_counterexample :
    Nonempty (DescentLens natStep (fun n => n) (fun x y => x = y + 1))
      ∧ Orients natStep (fun n => n) (fun x y => x = y + 1)
      ∧ StepChain natStep (fun n => n)
      ∧ ¬ WellFounded (fun x y : Nat => y < x) :=
  ⟨⟨increasingLens⟩, natStep_orients_increasing,
    increasingLens_has_infinite_chain, reverse_nat_order_not_wellFounded⟩

end OperatorKO7.RDRSDescentLens
