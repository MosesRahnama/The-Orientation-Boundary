import OperatorKO7.Kernel
import OperatorKO7.Meta.PolyInterpretation_FullStep
import OperatorKO7.Meta.EqGuardedConfluence
import OperatorKO7.Meta.EqW_Guard_Barrier

set_option autoImplicit false

/-!
# Distinction-Boundary repair routes for the `eqW` diagonal (G1)

The Distinction Boundary paper enumerates several conceivable repairs of the
full-kernel `eqW` critical pair and proves only the **guard** route
(`OperatorKO7.Meta.SafeStep.GuardNecessity.guard_route_discharged`). The other
routes are named but unproven. This file discharges three of them as
*substantive* confluence-restoration theorems.

The obstruction (do **not** re-prove here; reused as an imported breaker):
the two kernel rules `Step.R_eq_refl a : Step (eqW a a) void` and
`Step.R_eq_diff a a : Step (eqW a a) (integrate (merge a a))` overlap at the
diagonal `eqW a a`, producing two *distinct full-kernel normal forms* that never
re-join, so `MetaSN_KO7.LocalJoinStep (eqW a a)` is impossible
(`OperatorKO7.Meta.EqW_Guard_Barrier.not_localJoinStep_eqW_refl`).

Three repairs, each restoring confluence at the diagonal:

1. **inert-witness route** (`InertStep`): both `eqW` rules removed. `eqW` is then
   inert data — nothing fires on it — so `eqW a a` is a normal form, the diagonal
   fork is gone, and the diagonal is (vacuously) locally joinable. We further
   prove the whole relation is confluent (Newman: SN + unique targets).
2. **delete-diff route** (`DeleteDiffStep`): only `R_eq_diff` removed, `R_eq_refl`
   kept. Then `eqW a a` has the *unique* reduct `void`, so the diagonal is locally
   joinable. The full relation is confluent (Newman). The guarded-relation
   confluence already proven in `EqGuardedConfluence` is re-exported under a
   paper-facing name as the companion guard/diff result.
3. **quotient route** (`DiagId`): identify the two diagonal verdicts `void` and
   `integrate (merge a a)` by the smallest equivalence relation containing that
   pair, pass to the `Quotient`, and prove the diagonal peak becomes joinable in
   the quotient (the two verdict classes coincide). `Quot.sound` is load-bearing.

Each route carries an explicit non-vacuity witness at `a := void`, exhibiting the
genuine full-kernel fork that the repair removes.

Relation:  Step (full unguarded kernel) for the breaker; per-route restricted /
           identified relations for the repairs.
Closure:   root critical pair at the diagonal `eqW a a`, reflexive-transitive
           closure for confluence.
Strategy:  full (unguarded) for the breaker; rule-deletion / quotient-identification
           for the repairs.
Trust:     kernel-only; every headline `#print axioms` is a subset of
           {propext, Classical.choice, Quot.sound}.

No `sorry`, `admit`, `axiom`, `constant`, `native_decide`, `bv_decide`,
`@[csimp]`, `extern`, `implemented_by`, `unsafe`, `partial`, or `opaque`.
-/

open OperatorKO7 Trace

namespace OperatorKO7.Meta.DistinctionBoundary.RepairRoutes

/-! ## 0. The shared breaker fork at the canonical witness `a := void`

Reused, not re-proven: the full kernel emits two distinct reducts from the
diagonal and they are unjoinable. We pin the canonical witness for the
non-vacuity obligations of all three routes. -/

/-- Non-vacuity anchor: in the **full** kernel both `eqW`-rules fire at the
diagonal witness `eqW void void`, giving the two distinct reducts `void` and
`integrate (merge void void)`. This is the fork each repair must remove. -/
theorem full_fork_at_void :
    Step (eqW void void) void ∧
      Step (eqW void void) (integrate (merge void void)) :=
  ⟨Step.R_eq_refl void, Step.R_eq_diff void void⟩

/-- Non-vacuity anchor: the full-kernel diagonal is genuinely broken
(`LocalJoinStep` fails at every `eqW a a`). Imported breaker; not re-proven. -/
theorem full_diagonal_broken (a : Trace) :
    ¬ MetaSN_KO7.LocalJoinStep (eqW a a) :=
  OperatorKO7.Meta.EqW_Guard_Barrier.not_localJoinStep_eqW_refl a

/-! ## 1. Inert-witness route

`eqW` becomes inert data: **both** kernel `eqW` rules are removed. The remaining
six rules never inspect an `eqW` head, so every `eqW a b` is a normal form and
the diagonal fork is gone. -/

/-- The KO7 root relation with **both** `eqW` rules removed. `eqW` is inert:
no rule fires on an `eqW` head. -/
inductive InertStep : Trace → Trace → Prop
  | R_int_delta (t) : InertStep (integrate (delta t)) void
  | R_merge_void_left (t) : InertStep (merge void t) t
  | R_merge_void_right (t) : InertStep (merge t void) t
  | R_merge_cancel (t) : InertStep (merge t t) t
  | R_rec_zero (b s) : InertStep (recΔ b s void) b
  | R_rec_succ (b s n) : InertStep (recΔ b s (delta n)) (app s (recΔ b s n))

/-- Reverse relation for the well-foundedness / Newman argument. -/
def InertStepRev : Trace → Trace → Prop := fun a b => InertStep b a

/-- Reflexive-transitive closure of the inert relation. -/
inductive InertStepStar : Trace → Trace → Prop
  | refl : ∀ t, InertStepStar t t
  | tail : ∀ {a b c}, InertStep a b → InertStepStar b c → InertStepStar a c

/-- Local joinability at a fixed source for the inert relation. -/
def LocalJoinInert (a : Trace) : Prop :=
  ∀ {b c}, InertStep a b → InertStep a c → ∃ d, InertStepStar b d ∧ InertStepStar c d

/-- Church-Rosser for the inert relation. -/
def ConfluentInert : Prop :=
  ∀ a b c, InertStepStar a b → InertStepStar a c →
    ∃ d, InertStepStar b d ∧ InertStepStar c d

theorem inert_sub_step : ∀ {a b : Trace}, InertStep a b → Step a b
  | _, _, InertStep.R_int_delta t => Step.R_int_delta t
  | _, _, InertStep.R_merge_void_left t => Step.R_merge_void_left t
  | _, _, InertStep.R_merge_void_right t => Step.R_merge_void_right t
  | _, _, InertStep.R_merge_cancel t => Step.R_merge_cancel t
  | _, _, InertStep.R_rec_zero b s => Step.R_rec_zero b s
  | _, _, InertStep.R_rec_succ b s n => Step.R_rec_succ b s n

theorem inertStar_trans {a b c : Trace}
    (h₁ : InertStepStar a b) (h₂ : InertStepStar b c) : InertStepStar a c := by
  induction h₁ with
  | refl => exact h₂
  | tail hab _ ih => exact InertStepStar.tail hab (ih h₂)

theorem inertStar_destruct {a c : Trace} (h : InertStepStar a c) :
    a = c ∨ ∃ b, InertStep a b ∧ InertStepStar b c := by
  cases h with
  | refl t => exact Or.inl rfl
  | tail hab hbc => exact Or.inr ⟨_, hab, hbc⟩

/-- The inert relation is well-founded (it is a subrelation of the full kernel,
which is SN by the polynomial interpretation). -/
theorem wf_InertStepRev : WellFounded InertStepRev := by
  have hsub : Subrelation InertStepRev (fun a b : Trace => Step b a) := by
    intro a b hab
    exact inert_sub_step hab
  exact Subrelation.wf hsub OperatorKO7.PolyInterpretation.wf_StepRev_poly

/-- **Diagonal is inert.** Under `InertStep`, `eqW a a` has **no** reduct: the
fork that broke the full kernel is gone. The `eqW` term is inert data. -/
theorem inertStep_eqW_diagonal_normalForm (a : Trace) :
    ¬ ∃ u, InertStep (eqW a a) u := by
  intro ⟨u, hu⟩
  cases hu

/-- More generally, **no** `eqW` head reduces under `InertStep`. -/
theorem inertStep_eqW_normalForm (a b : Trace) :
    ¬ ∃ u, InertStep (eqW a b) u := by
  intro ⟨u, hu⟩
  cases hu

/-- **Repair (inert route), diagonal.** With both `eqW` rules removed the
diagonal `eqW a a` is locally joinable: there is no fork, so local joinability
holds (vacuously over the empty set of reduct pairs). Contrast
`full_diagonal_broken`, where the full kernel admits the unjoinable fork.

Relation: InertStep.  Closure: root.  Strategy: both-`eqW`-rules-deleted.
Property: local_confluence (restored at the diagonal). -/
theorem inert_route_diagonal_localJoin (a : Trace) :
    LocalJoinInert (eqW a a) := by
  intro b c hb hc
  exact absurd ⟨b, hb⟩ (inertStep_eqW_diagonal_normalForm a)

/-- Unique-target determinism of the inert relation: every source has at most one
reduct. Proven by exhausting the six rule overlaps. -/
theorem inert_unique_target {a b c : Trace}
    (hb : InertStep a b) (hc : InertStep a c) : b = c := by
  cases hb <;> cases hc <;> rfl

/-- Local joinability everywhere for the inert relation (immediate from unique
targets). -/
theorem localJoin_all_inert : ∀ a : Trace, LocalJoinInert a := by
  intro a b c hb hc
  refine ⟨b, InertStepStar.refl b, ?_⟩
  cases inert_unique_target hb hc
  exact InertStepStar.refl b

private theorem inert_join_star_star_at
    (locAll : ∀ a, LocalJoinInert a) :
    ∀ x, Acc InertStepRev x →
      ∀ {y z : Trace}, InertStepStar x y → InertStepStar x z →
        ∃ d, InertStepStar y d ∧ InertStepStar z d := by
  intro x hx
  induction hx with
  | intro x _ ih =>
      intro y z hxy hxz
      have HY := inertStar_destruct hxy
      have HZ := inertStar_destruct hxz
      cases HY with
      | inl hEq =>
          cases hEq
          exact ⟨z, hxz, InertStepStar.refl z⟩
      | inr hy =>
          rcases hy with ⟨b1, hxb1, hb1y⟩
          cases HZ with
          | inl hEq2 =>
              cases hEq2
              exact ⟨y, InertStepStar.refl y, InertStepStar.tail hxb1 hb1y⟩
          | inr hz =>
              rcases hz with ⟨c1, hxc1, hc1z⟩
              rcases locAll x hxb1 hxc1 with ⟨e, hb1e, hc1e⟩
              rcases ih c1 hxc1 hc1e hc1z with ⟨d₁, hed₁, hzd₁⟩
              have hb1d₁ : InertStepStar b1 d₁ := inertStar_trans hb1e hed₁
              rcases ih b1 hxb1 hb1y hb1d₁ with ⟨d, hyd, hd₁d⟩
              exact ⟨d, hyd, inertStar_trans hzd₁ hd₁d⟩

/-- **Confluence of the inert route (whole relation).** Newman specialization:
SN (`wf_InertStepRev`) plus everywhere-local-joinability gives Church-Rosser.

Relation: InertStep.  Closure: reflexive-transitive.  Strategy: both-`eqW`-deleted.
Property: confluence. -/
theorem confluent_inert : ConfluentInert := by
  intro a b c hab hac
  exact inert_join_star_star_at localJoin_all_inert a (wf_InertStepRev.apply a) hab hac

/-- **Non-vacuity (inert route).** At the canonical witness `a := void`: the full
kernel admits the two distinct reducts `void` and `integrate (merge void void)`
from `eqW void void` (`full_fork_at_void`), yet under `InertStep` the term
`eqW void void` has *no* reduct at all. The repair genuinely removes the fork. -/
theorem inert_route_witness_void :
    (Step (eqW void void) void ∧
        Step (eqW void void) (integrate (merge void void))) ∧
      (¬ ∃ u, InertStep (eqW void void) u) :=
  ⟨full_fork_at_void, inertStep_eqW_diagonal_normalForm void⟩

/-! ## 2. Delete-diff route

Only the difference rule `R_eq_diff` is removed; the reflexive rule `R_eq_refl`
is kept. The diagonal then has the **unique** reduct `void`. -/

/-- The KO7 root relation with **`R_eq_diff` removed**, `R_eq_refl` kept. -/
inductive DeleteDiffStep : Trace → Trace → Prop
  | R_int_delta (t) : DeleteDiffStep (integrate (delta t)) void
  | R_merge_void_left (t) : DeleteDiffStep (merge void t) t
  | R_merge_void_right (t) : DeleteDiffStep (merge t void) t
  | R_merge_cancel (t) : DeleteDiffStep (merge t t) t
  | R_rec_zero (b s) : DeleteDiffStep (recΔ b s void) b
  | R_rec_succ (b s n) : DeleteDiffStep (recΔ b s (delta n)) (app s (recΔ b s n))
  | R_eq_refl (a) : DeleteDiffStep (eqW a a) void

/-- Reverse relation for the well-foundedness / Newman argument. -/
def DeleteDiffStepRev : Trace → Trace → Prop := fun a b => DeleteDiffStep b a

/-- Reflexive-transitive closure of the delete-diff relation. -/
inductive DeleteDiffStepStar : Trace → Trace → Prop
  | refl : ∀ t, DeleteDiffStepStar t t
  | tail : ∀ {a b c}, DeleteDiffStep a b → DeleteDiffStepStar b c → DeleteDiffStepStar a c

/-- Local joinability at a fixed source for the delete-diff relation. -/
def LocalJoinDeleteDiff (a : Trace) : Prop :=
  ∀ {b c}, DeleteDiffStep a b → DeleteDiffStep a c →
    ∃ d, DeleteDiffStepStar b d ∧ DeleteDiffStepStar c d

/-- Church-Rosser for the delete-diff relation. -/
def ConfluentDeleteDiff : Prop :=
  ∀ a b c, DeleteDiffStepStar a b → DeleteDiffStepStar a c →
    ∃ d, DeleteDiffStepStar b d ∧ DeleteDiffStepStar c d

theorem deleteDiff_sub_step : ∀ {a b : Trace}, DeleteDiffStep a b → Step a b
  | _, _, DeleteDiffStep.R_int_delta t => Step.R_int_delta t
  | _, _, DeleteDiffStep.R_merge_void_left t => Step.R_merge_void_left t
  | _, _, DeleteDiffStep.R_merge_void_right t => Step.R_merge_void_right t
  | _, _, DeleteDiffStep.R_merge_cancel t => Step.R_merge_cancel t
  | _, _, DeleteDiffStep.R_rec_zero b s => Step.R_rec_zero b s
  | _, _, DeleteDiffStep.R_rec_succ b s n => Step.R_rec_succ b s n
  | _, _, DeleteDiffStep.R_eq_refl a => Step.R_eq_refl a

theorem deleteDiffStar_trans {a b c : Trace}
    (h₁ : DeleteDiffStepStar a b) (h₂ : DeleteDiffStepStar b c) : DeleteDiffStepStar a c := by
  induction h₁ with
  | refl => exact h₂
  | tail hab _ ih => exact DeleteDiffStepStar.tail hab (ih h₂)

theorem deleteDiffStar_destruct {a c : Trace} (h : DeleteDiffStepStar a c) :
    a = c ∨ ∃ b, DeleteDiffStep a b ∧ DeleteDiffStepStar b c := by
  cases h with
  | refl t => exact Or.inl rfl
  | tail hab hbc => exact Or.inr ⟨_, hab, hbc⟩

/-- The delete-diff relation is well-founded (subrelation of the SN full kernel). -/
theorem wf_DeleteDiffStepRev : WellFounded DeleteDiffStepRev := by
  have hsub : Subrelation DeleteDiffStepRev (fun a b : Trace => Step b a) := by
    intro a b hab
    exact deleteDiff_sub_step hab
  exact Subrelation.wf hsub OperatorKO7.PolyInterpretation.wf_StepRev_poly

/-- **Diagonal has the unique reduct `void`.** Under `DeleteDiffStep`, the only
rule firing on `eqW a a` is `R_eq_refl`, so every reduct of `eqW a a` equals
`void`. The competing `integrate (merge a a)` verdict is gone. -/
theorem deleteDiffStep_eqW_diagonal_unique_void {a u : Trace}
    (h : DeleteDiffStep (eqW a a) u) : u = void := by
  cases h with
  | R_eq_refl _ => rfl

/-- There is at least one reduct: `eqW a a ⇒ void` under `DeleteDiffStep`. -/
theorem deleteDiffStep_eqW_diagonal_to_void (a : Trace) :
    DeleteDiffStep (eqW a a) void :=
  DeleteDiffStep.R_eq_refl a

/-- **Repair (delete-diff route), diagonal.** With `R_eq_diff` removed the
diagonal `eqW a a` reduces uniquely to `void`, hence is locally joinable.

Relation: DeleteDiffStep.  Closure: root.  Strategy: `R_eq_diff`-deleted.
Property: local_confluence (restored at the diagonal). -/
theorem deleteDiff_route_diagonal_localJoin (a : Trace) :
    LocalJoinDeleteDiff (eqW a a) := by
  intro b c hb hc
  have hb' : b = void := deleteDiffStep_eqW_diagonal_unique_void hb
  have hc' : c = void := deleteDiffStep_eqW_diagonal_unique_void hc
  refine ⟨void, ?_, ?_⟩
  · cases hb'; exact DeleteDiffStepStar.refl void
  · cases hc'; exact DeleteDiffStepStar.refl void

/-- Unique-target determinism of the delete-diff relation. -/
theorem deleteDiff_unique_target {a b c : Trace}
    (hb : DeleteDiffStep a b) (hc : DeleteDiffStep a c) : b = c := by
  cases hb <;> cases hc <;> rfl

/-- Local joinability everywhere for the delete-diff relation. -/
theorem localJoin_all_deleteDiff : ∀ a : Trace, LocalJoinDeleteDiff a := by
  intro a b c hb hc
  refine ⟨b, DeleteDiffStepStar.refl b, ?_⟩
  cases deleteDiff_unique_target hb hc
  exact DeleteDiffStepStar.refl b

private theorem deleteDiff_join_star_star_at
    (locAll : ∀ a, LocalJoinDeleteDiff a) :
    ∀ x, Acc DeleteDiffStepRev x →
      ∀ {y z : Trace}, DeleteDiffStepStar x y → DeleteDiffStepStar x z →
        ∃ d, DeleteDiffStepStar y d ∧ DeleteDiffStepStar z d := by
  intro x hx
  induction hx with
  | intro x _ ih =>
      intro y z hxy hxz
      have HY := deleteDiffStar_destruct hxy
      have HZ := deleteDiffStar_destruct hxz
      cases HY with
      | inl hEq =>
          cases hEq
          exact ⟨z, hxz, DeleteDiffStepStar.refl z⟩
      | inr hy =>
          rcases hy with ⟨b1, hxb1, hb1y⟩
          cases HZ with
          | inl hEq2 =>
              cases hEq2
              exact ⟨y, DeleteDiffStepStar.refl y, DeleteDiffStepStar.tail hxb1 hb1y⟩
          | inr hz =>
              rcases hz with ⟨c1, hxc1, hc1z⟩
              rcases locAll x hxb1 hxc1 with ⟨e, hb1e, hc1e⟩
              rcases ih c1 hxc1 hc1e hc1z with ⟨d₁, hed₁, hzd₁⟩
              have hb1d₁ : DeleteDiffStepStar b1 d₁ := deleteDiffStar_trans hb1e hed₁
              rcases ih b1 hxb1 hb1y hb1d₁ with ⟨d, hyd, hd₁d⟩
              exact ⟨d, hyd, deleteDiffStar_trans hzd₁ hd₁d⟩

/-- **Confluence of the delete-diff route (whole relation).** Newman: SN plus
everywhere-local-joinability gives Church-Rosser.

Relation: DeleteDiffStep.  Closure: reflexive-transitive.  Strategy: `R_eq_diff`-deleted.
Property: confluence. -/
theorem confluent_deleteDiff : ConfluentDeleteDiff := by
  intro a b c hab hac
  exact deleteDiff_join_star_star_at localJoin_all_deleteDiff a
    (wf_DeleteDiffStepRev.apply a) hab hac

/-- **Non-vacuity (delete-diff route).** At the canonical witness `a := void`: the
full kernel admits the two distinct reducts, yet under `DeleteDiffStep` the source
`eqW void void` reduces uniquely to `void` (and *only* to `void`). The repair kills
the competing verdict. -/
theorem deleteDiff_route_witness_void :
    (Step (eqW void void) void ∧
        Step (eqW void void) (integrate (merge void void))) ∧
      DeleteDiffStep (eqW void void) void ∧
      (∀ u, DeleteDiffStep (eqW void void) u → u = void) :=
  ⟨full_fork_at_void, deleteDiffStep_eqW_diagonal_to_void void,
    fun _ h => deleteDiffStep_eqW_diagonal_unique_void h⟩

/-- **Companion guarded/diff result, re-exported.** The intermediate fragment
that keeps *both* `eqW` rules but guards the diff branch by `a ≠ b` is already
proven Church-Rosser in `OperatorKO7.Meta.EqGuardedConfluence`. We re-export it
here under a Distinction-Boundary-facing name: guarding the diff branch (rather
than deleting it) also restores full confluence.

Relation: EqGuardedStep (full kernel, diff branch guarded by `a ≠ b`).
Closure: reflexive-transitive.  Property: confluence. -/
theorem eqGuarded_diff_route_confluent :
    OperatorKO7.EqGuardedConfluence.ConfluentEqGuarded :=
  OperatorKO7.EqGuardedConfluence.confluentEqGuarded

/-! ## 3. Quotient route

Keep the full kernel, but **identify** the two diagonal verdicts `void` and
`integrate (merge a a)`. We build the smallest equivalence relation containing
that single pair, pass to the quotient, and show the diagonal peak joins in the
quotient (the two verdict classes coincide). -/

/-- The smallest equivalence relation that identifies each diagonal verdict pair
`void ~ integrate (merge a a)`. Closed under reflexivity, symmetry, transitivity,
and the diagonal identification at every `a`. -/
inductive DiagId : Trace → Trace → Prop
  | base (a : Trace) : DiagId void (integrate (merge a a))
  | refl (t : Trace) : DiagId t t
  | symm {s t : Trace} : DiagId s t → DiagId t s
  | trans {r s t : Trace} : DiagId r s → DiagId s t → DiagId r t

theorem diagId_refl (t : Trace) : DiagId t t := DiagId.refl t
theorem diagId_symm {s t : Trace} (h : DiagId s t) : DiagId t s := DiagId.symm h
theorem diagId_trans {r s t : Trace} (h₁ : DiagId r s) (h₂ : DiagId s t) :
    DiagId r t := DiagId.trans h₁ h₂

/-- `DiagId` is an equivalence relation. -/
theorem diagId_equivalence : Equivalence DiagId :=
  { refl := DiagId.refl
    symm := DiagId.symm
    trans := DiagId.trans }

/-- The setoid identifying the diagonal verdicts. -/
def diagSetoid : Setoid Trace := ⟨DiagId, diagId_equivalence⟩

/-- The quotient of traces by the diagonal-verdict identification. -/
def TraceModDiag : Type := Quotient diagSetoid

/-- Class of a trace in the diagonal-verdict quotient. -/
def diagClass (t : Trace) : TraceModDiag := Quotient.mk diagSetoid t

/-- Two traces have equal class iff they are `DiagId`-related (sound + complete). -/
theorem diagClass_eq_iff {s t : Trace} : diagClass s = diagClass t ↔ DiagId s t :=
  Quotient.eq

/-- **The identification holds in the quotient.** The two diagonal verdicts `void`
and `integrate (merge a a)` collapse to a single class. This is the defining
content of the quotient route; it consumes `Quot.sound`. -/
theorem diagClass_verdicts_identified (a : Trace) :
    diagClass void = diagClass (integrate (merge a a)) :=
  Quotient.sound (DiagId.base a)

/-- The two diagonal verdicts are genuinely distinct *before* quotienting
(imported breaker fact), so the identification is non-trivial. -/
theorem verdicts_distinct_preQuotient (a : Trace) :
    (void : Trace) ≠ integrate (merge a a) :=
  OperatorKO7.Meta.EqW_Guard_Barrier.void_ne_integrate_merge_self a

/-- **Repair (quotient route), diagonal.** The full-kernel diagonal peak
`eqW a a ⇒ void` and `eqW a a ⇒ integrate (merge a a)` becomes joinable *up to the
identification*: the two verdicts step (reflexively) to representatives whose
quotient classes coincide.

This is the joinable-up-to-`DiagId` statement: there exist reducts `d₁` of `void`
and `d₂` of `integrate (merge a a)` (here the verdicts themselves) with
`DiagId d₁ d₂`. Equivalently the diagonal peak joins in `TraceModDiag`.

Relation: Step (full kernel) up to the `DiagId` identification.
Closure: root peak.  Strategy: quotient-identification of verdicts.
Property: local_confluence (restored modulo identification). -/
theorem quotient_route_diagonal_join (a : Trace) :
    ∃ d₁ d₂ : Trace,
      StepStar void d₁ ∧
        StepStar (integrate (merge a a)) d₂ ∧
        DiagId d₁ d₂ := by
  refine ⟨void, integrate (merge a a), StepStar.refl void,
    StepStar.refl (integrate (merge a a)), ?_⟩
  exact DiagId.base a

/-- **Repair (quotient route), diagonal, quotient form.** Exhibits the two
diagonal verdicts as a single point of `TraceModDiag`: the peak is confluent in
the quotient. -/
theorem quotient_route_diagonal_join_classes (a : Trace) :
    diagClass void = diagClass (integrate (merge a a)) :=
  diagClass_verdicts_identified a

/-- **Non-vacuity (quotient route).** At the canonical witness `a := void`: the two
verdicts `void` and `integrate (merge void void)` are distinct as traces
(`verdicts_distinct_preQuotient`) yet equal in the quotient
(`quotient_route_diagonal_join_classes`). The identification does real work — it
glues two genuinely different normal forms. -/
theorem quotient_route_witness_void :
    ((void : Trace) ≠ integrate (merge void void)) ∧
      diagClass void = diagClass (integrate (merge void void)) :=
  ⟨verdicts_distinct_preQuotient void, quotient_route_diagonal_join_classes void⟩

/-! ## 4. Axiom audit for the headline theorems

Every headline is kernel-only; each printed set must be a subset of
{propext, Classical.choice, Quot.sound}. The quotient route deliberately uses
`Quot.sound` (the identification is its content). -/

-- Inert-witness route
#print axioms inert_route_diagonal_localJoin
#print axioms confluent_inert
#print axioms inert_route_witness_void

-- Delete-diff route
#print axioms deleteDiff_route_diagonal_localJoin
#print axioms confluent_deleteDiff
#print axioms deleteDiff_route_witness_void
#print axioms eqGuarded_diff_route_confluent

-- Quotient route
#print axioms quotient_route_diagonal_join
#print axioms quotient_route_diagonal_join_classes
#print axioms quotient_route_witness_void

end OperatorKO7.Meta.DistinctionBoundary.RepairRoutes
