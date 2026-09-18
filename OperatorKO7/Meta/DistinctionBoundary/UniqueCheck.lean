import OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity
import OperatorKO7.Meta.DistinctionBoundary.DiscriminatorExtension
import OperatorKO7.Meta.DistinctionBoundary.ConservativeRepair
import OperatorKO7.Meta.SafeStep.SyntacticNonDerivability
import Mathlib.Data.Fintype.Pigeonhole

set_option autoImplicit false

/-!
# The unique check: uniqueness, the injectivity barrier, and canonicity

Manuscript anchors: `thm:check-unique`, `thm:injectivity-barrier`,
`thm:check-canonical`, `thm:one-check-boundary`, `rem:axis-injectivity` of
`Rahnama_The_Distinction_Boundary`. Roadmap: `ROADMAP-08-the-unique-check.md`.

## The three levels

The question this module settles is how many ways there are to decide whether
two things are the same. The answer separates by level.

* **Function.** Any two sound and complete comparators on a carrier compute the
  same Boolean function, the characteristic function of the diagonal
  (`check_unique_pointwise`, `check_eq_decide`). There is one check.
* **Mechanism.** Any sound and complete comparator preserves all of its input:
  it factors through no non-injective abstraction (`injectivity_barrier`).
  Finite-state observation, bounded-depth inspection, and fixed-range hashing
  are each non-injective on an infinite carrier, so none of them is a check
  (`no_finiteState_check`, `no_boundedDepth_check`, `no_hash_check`). On the
  kernel carrier the structural recursion is the canonical representative
  (`structEq_canonical`).
* **Algorithm.** Implementations still differ in traversal order and cost
  profile, and that multiplicity is real. It is not modelled here, and no
  claim is made that all correct implementations are the same procedure. The
  companion module `CheckRelocation` shows where the apparent shortcuts put
  the check instead of removing it.

## Relation to the clone no-go

`ObserverExpressivity.not_discriminator_of_natural_under_noninjective` proves
the same impossibility inside the term-clone setting, where the verdict is
decoded through the algebra itself and a collapse-reflection hypothesis is
therefore load carrying. `injectivity_barrier` reads the verdict directly, so
it needs no naturality, no signature, and no reflection hypothesis. The clone
theorem keeps its own face, which is what connects the development to
discriminator theory in universal algebra; the barrier below is the master
statement it instantiates (`clone_shaped_instance`).

## Scope

Uniqueness here is extensional and concerns deterministic total comparators.
Randomised checks that relax soundness to high probability are outside this
development by construction and are named as excluded, not refuted.

Relation: not a rewrite relation; carrier-level comparators. Closure: not
applicable. Trust: kernel only, Mathlib baseline.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.UniqueCheck

open OperatorKO7 Trace
open OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity
open OperatorKO7.Meta.DistinctionBoundary.DiscriminatorExtension

/-! ## The comparator interface -/

/-- A comparator answers `true` only on identical arguments. -/
def SoundEq {α : Type*} (c : α → α → Bool) : Prop :=
  ∀ a b, c a b = true → a = b

/-- A comparator answers `true` on every identical pair. -/
def CompleteEq {α : Type*} (c : α → α → Bool) : Prop :=
  ∀ a b, a = b → c a b = true

/-- The two obligations together. -/
structure IsCheck {α : Type*} (c : α → α → Bool) : Prop where
  sound : SoundEq c
  complete : CompleteEq c

/-! ## U1: there is one check -/

/-- **U1a, pointwise uniqueness.** Any two sound and complete comparators agree
at every pair. The proof is a case split on one comparator's verdict: a `true`
verdict transfers through soundness and completeness, and a `false` verdict
forces the arguments apart, which the other comparator's soundness respects. -/
theorem check_unique_pointwise {α : Type*} {c₁ c₂ : α → α → Bool}
    (h₁ : IsCheck c₁) (h₂ : IsCheck c₂) (a b : α) : c₁ a b = c₂ a b := by
  cases hv : c₁ a b with
  | true =>
      have hab : a = b := h₁.sound a b hv
      exact (h₂.complete a b hab).symm
  | false =>
      cases hv2 : c₂ a b with
      | true =>
          have hab : a = b := h₂.sound a b hv2
          have : c₁ a b = true := h₁.complete a b hab
          rw [hv] at this
          exact absurd this (by simp)
      | false => rfl

/-- **U1a, packaged.** The comparator is unique as a function. -/
theorem check_unique {α : Type*} {c₁ c₂ : α → α → Bool}
    (h₁ : IsCheck c₁) (h₂ : IsCheck c₂) : c₁ = c₂ := by
  funext a b
  exact check_unique_pointwise h₁ h₂ a b

/-- The decision procedure of a decidable-equality instance is a check. -/
theorem decide_isCheck {α : Type*} [DecidableEq α] :
    IsCheck (fun a b : α => decide (a = b)) := by
  refine ⟨?_, ?_⟩
  · intro a b h
    exact of_decide_eq_true h
  · intro a b h
    exact decide_eq_true h

/-- **U1b, canonical form.** On a carrier with decidable equality every check is
the characteristic function of the diagonal. This is the content of the phrase
`the check`: not one of several equality tests, but the equality test. -/
theorem check_eq_decide {α : Type*} [DecidableEq α] {c : α → α → Bool}
    (h : IsCheck c) (a b : α) : c a b = decide (a = b) :=
  check_unique_pointwise h decide_isCheck a b

/-- Non-triviality, half one: the constant-`true` comparator is complete and is
not sound, so completeness alone does not pin the check. -/
theorem constTrue_complete_not_sound :
    CompleteEq (fun _ _ : Trace => true) ∧ ¬ SoundEq (fun _ _ : Trace => true) := by
  refine ⟨fun _ _ _ => rfl, ?_⟩
  intro hs
  have := hs void (delta void) rfl
  exact Trace.noConfusion this

/-- Non-triviality, half two: the constant-`false` comparator is sound and is
not complete, so soundness alone does not pin the check either. Together with
the previous fact, `check_unique_pointwise` is not a tautology: it needs both
obligations. -/
theorem constFalse_sound_not_complete :
    SoundEq (fun _ _ : Trace => false) ∧ ¬ CompleteEq (fun _ _ : Trace => false) := by
  refine ⟨fun _ _ h => absurd h (by simp), ?_⟩
  intro hc
  have := hc void void rfl
  exact Bool.noConfusion this

/-! ## U2: the injectivity barrier -/

/-- **U2, positive form.** If a comparator that reads its arguments only
through `h` is sound and complete, then `h` is injective. A check therefore
tolerates no lossy preprocessing: whatever the comparator is allowed to see
must still separate everything the carrier separates. -/
theorem factored_check_forces_injective {α β : Type*}
    {h : α → β} {c' : β → β → Bool}
    (hc : IsCheck (fun a b : α => c' (h a) (h b))) : Function.Injective h := by
  intro x y hxy
  have hx : c' (h x) (h x) = true := hc.complete x x rfl
  have hxy' : c' (h x) (h y) = true := by rw [← hxy]; exact hx
  exact hc.sound x y hxy'

/-- **U2, barrier form.** No comparator factoring through a non-injective
abstraction is a check. -/
theorem injectivity_barrier {α β : Type*}
    {h : α → β} (hni : ¬ Function.Injective h) (c' : β → β → Bool) :
    ¬ IsCheck (fun a b : α => c' (h a) (h b)) := by
  intro hc
  exact hni (factored_check_forces_injective hc)

/-- **U2, collision form.** A single collision already refutes the factored
comparator, which is the shape every corollary below consumes. -/
theorem no_check_of_collision {α β : Type*}
    {h : α → β} {x y : α} (hne : x ≠ y) (hcol : h x = h y) (c' : β → β → Bool) :
    ¬ IsCheck (fun a b : α => c' (h a) (h b)) := by
  intro hc
  exact hne (factored_check_forces_injective hc hcol)

/-! ### Corollary 1: no finite-state check -/

/-- **U2 corollary 1.** On an infinite carrier no abstraction into a finite
state set supports a check. The finite-state observer bound of
`ObserverExpressivity` is this statement in the observer packaging. -/
theorem no_finiteState_check {α β : Type*} [Infinite α] [Finite β]
    (h : α → β) (c' : β → β → Bool) :
    ¬ IsCheck (fun a b : α => c' (h a) (h b)) := by
  obtain ⟨x, y, hne, hcol⟩ := Finite.exists_ne_map_eq_of_infinite h
  exact no_check_of_collision hne hcol c'

/-! ### Corollary 2: no bounded-depth check -/

/-- Truncation of a trace at depth `d`: subtrees below the cut are replaced by
the null record. -/
def truncate : ℕ → Trace → Trace
  | 0, _ => void
  | _ + 1, void => void
  | n + 1, delta t => delta (truncate n t)
  | n + 1, integrate t => integrate (truncate n t)
  | n + 1, merge a b => merge (truncate n a) (truncate n b)
  | n + 1, app a b => app (truncate n a) (truncate n b)
  | n + 1, recΔ a b c => recΔ (truncate n a) (truncate n b) (truncate n c)
  | n + 1, eqW a b => eqW (truncate n a) (truncate n b)

/-- Truncation at depth `d` sends every delta tower of height at least `d` to
the tower of height `d`, so it collapses the tail of the tower. -/
theorem truncate_dpow (d k : ℕ) : truncate d (dpow (d + k)) = dpow d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      have hstep : dpow (d + 1 + k) = delta (dpow (d + k)) := by
        have : d + 1 + k = (d + k) + 1 := by omega
        rw [this]
        rfl
      rw [hstep]
      show delta (truncate d (dpow (d + k))) = delta (dpow d)
      rw [ih]

/-- **U2 corollary 2.** No inspection bounded to a fixed depth supports a
check, at any depth bound. Two delta towers that agree down to the cut are
distinct terms with the same truncation. -/
theorem no_boundedDepth_check (d : ℕ) (c' : Trace → Trace → Bool) :
    ¬ IsCheck (fun a b : Trace => c' (truncate d a) (truncate d b)) := by
  refine no_check_of_collision (x := dpow (d + 1)) (y := dpow (d + 2)) ?_ ?_ c'
  · intro hEq
    have := dpow_injective hEq
    omega
  · rw [truncate_dpow d 1, truncate_dpow d 2]

/-- The depth-one instance, stated concretely: `delta void` and
`delta (delta void)` are the witnesses. -/
theorem no_depthOne_check (c' : Trace → Trace → Bool) :
    ¬ IsCheck (fun a b : Trace => c' (truncate 1 a) (truncate 1 b)) :=
  no_boundedDepth_check 1 c'

/-! ### Corollary 3: no hash shortcut -/

/-- **U2 corollary 3.** No deterministic hash into a fixed finite range
supports a check on an infinite carrier. A hash comparison alone is therefore
never a check; a hashed implementation that is correct carries a collision
resolver, and by `check_unique_pointwise` that resolver is the check. -/
theorem no_hash_check {α : Type*} [Infinite α] {k : ℕ}
    (hash : α → Fin k) (c' : Fin k → Fin k → Bool) :
    ¬ IsCheck (fun a b : α => c' (hash a) (hash b)) :=
  no_finiteState_check hash c'

/-- The kernel carrier is infinite, by the injectivity of the delta tower. -/
theorem trace_infinite : Infinite Trace :=
  Infinite.of_injective dpow dpow_injective

/-- The kernel instance of the hash corollary. -/
theorem no_hash_check_trace {k : ℕ} (hash : Trace → Fin k)
    (c' : Fin k → Fin k → Bool) :
    ¬ IsCheck (fun a b : Trace => c' (hash a) (hash b)) :=
  @no_hash_check Trace trace_infinite k hash c'

/-! ### Corollary 4: the clone-shaped instance -/

/-- **U2 corollary 4.** A non-injective endomorphism of any carrier refutes
every comparator reading through it. Instantiating at a signature endomorphism
recovers the semantic content of the clone no-go of `ObserverExpressivity`
without its naturality apparatus; the clone theorem keeps that apparatus for
its own connection to discriminator theory. -/
theorem clone_shaped_instance {α : Type*} {h : α → α}
    (hni : ¬ Function.Injective h) (c' : α → α → Bool) :
    ¬ IsCheck (fun a b : α => c' (h a) (h b)) :=
  injectivity_barrier hni c'

/-! ## U3: canonicity of the structural comparator -/

/-- The structural comparator of `DiscriminatorExtension` is a check. -/
theorem structEq_isCheck : IsCheck structEq := by
  refine ⟨?_, ?_⟩
  · intro a b h
    exact structEq_sound h
  · intro a b h
    exact structEq_complete h

/-- **U3.** Every check on the kernel carrier agrees pointwise with the
structural comparator. The structural recursion is therefore not one correct
algorithm among many: it is the canonical representative of the unique check,
and every correct comparator is an extensional reindexing of it. -/
theorem structEq_canonical {c : Trace → Trace → Bool} (h : IsCheck c)
    (a b : Trace) : c a b = structEq a b :=
  check_unique_pointwise h structEq_isCheck a b

/-- The same statement as a function identity. -/
theorem structEq_canonical_eq {c : Trace → Trace → Bool} (h : IsCheck c) :
    c = structEq :=
  check_unique h structEq_isCheck

/-- Canonicity meets the lower bound: the structural comparator recurses to
full depth, and by `no_boundedDepth_check` no shallower recursion is a check.
Stated as the conjunction that the manuscript quotes. -/
theorem structEq_full_depth_needed (d : ℕ) :
    IsCheck structEq ∧
      ∀ c' : Trace → Trace → Bool,
        ¬ IsCheck (fun a b : Trace => c' (truncate d a) (truncate d b)) :=
  ⟨structEq_isCheck, fun c' => no_boundedDepth_check d c'⟩

/-! ## U4: the one-check boundary -/

/-- **U4.** The five legs of the boundary, over the kernel diagonal.

1. Forced: an admissible repair admits the difference branch at a pair if and
   only if the pair is distinct, so the guard is a conclusion of the repair
   obligations and not an input to them.
2. Unique: any two checks agree, so the executable content of that guard is
   determined.
3. Lossless: no check factors through a non-injective abstraction, so no
   finite-state, bounded-depth, or hashed realisation exists.
4. Unwritable: no term of the seven-constructor signature realises the check.
5. Purchasable: the structural comparator of the extended signature is a check,
   and every check agrees with it.

The conjunction is the sentence the manuscript carries: the repair needs a
check, there is one check, the check tolerates no lossy shortcut, the native
language cannot write it, and one comparator extension is it. -/
theorem one_check_boundary :
    (∀ (R : Trace → Trace → Prop),
        ConservativeRepair.AdmissibleRepair R → ∀ a b : Trace,
          R (eqW a b) (integrate (merge a b)) ↔ a ≠ b) ∧
    (∀ (c₁ c₂ : Trace → Trace → Bool), IsCheck c₁ → IsCheck c₂ →
        ∀ a b, c₁ a b = c₂ a b) ∧
    (∀ {β : Type} (h : Trace → β) (c' : β → β → Bool),
        IsCheck (fun a b : Trace => c' (h a) (h b)) → Function.Injective h) ∧
    (¬ ∃ t : Meta.SafeStep.SigmaFreeAlgebra.SigmaTerm,
        ∀ a b : Meta.SafeStep.SigmaFreeAlgebra.SigmaTerm,
          (a ≠ b) ↔
            (Meta.SafeStep.SigmaFreeAlgebra.evalSigma a b t ≠
              Meta.SafeStep.SigmaFreeAlgebra.SigmaTerm.void)) ∧
    (IsCheck structEq ∧
      ∀ (c : Trace → Trace → Bool), IsCheck c → ∀ a b, c a b = structEq a b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro R hR a b
    exact ConservativeRepair.conservative_repair_forces_exact_distinction hR a b
  · intro c₁ c₂ h₁ h₂ a b
    exact check_unique_pointwise h₁ h₂ a b
  · intro β h c' hc
    exact factored_check_forces_injective hc
  · exact Meta.SafeStep.SyntacticNonDerivability.disequality_not_sigma_expressible_unconditional
  · exact ⟨structEq_isCheck, fun c hc a b => structEq_canonical hc a b⟩

/-! ## The axis datum

The orientation axis licenses a lossy abstraction: the dependency-pair
projection discards the payload coordinate, and the discard is sound because
the discarded structure is carrier-redundant for the termination verdict. The
distinction axis admits no lossy abstraction at all, by
`factored_check_forces_injective`. The two axes therefore separate on one
question, whether the licensed map may lose information. The finite record
below states the distinction side of that separation as a proposition about
the check; the orientation side is the redundant-discard dichotomy of the
published development, and the translation between the two sides is a research
target of the program, not a claim of this module. -/

/-- The distinction side of the axis datum: a licensed comparison map loses no
information. -/
theorem distinction_axis_forbids_loss {α β : Type*}
    (h : α → β) (c' : β → β → Bool)
    (hc : IsCheck (fun a b : α => c' (h a) (h b))) : Function.Injective h :=
  factored_check_forces_injective hc

/-- Payload blindness, the defining property of the orientation-axis
projection, stated on the kernel: the map identifies two recursor terms that
differ only in the step argument it discards. -/
def PayloadBlindAt {β : Type*} (h : Trace → β) (s s' : Trace) : Prop :=
  s ≠ s' ∧ h (recΔ void s void) = h (recΔ void s' void)

/-- **The axis separation, distinction side.** A payload-blind map supports no
check. The orientation axis licenses exactly such a map, because the discarded
payload is redundant for the termination verdict; the distinction axis refuses
the same map, because the discarded payload is not redundant for the identity
verdict. The two axes therefore differ on one question, whether the licensed
map may lose information, and this theorem is the distinction side of that
answer. The orientation side is the redundant-discard dichotomy of the
published development, and no translation between the two sides is claimed
here. -/
theorem payloadBlind_supports_no_check {β : Type*}
    {h : Trace → β} {s s' : Trace} (hpb : PayloadBlindAt h s s')
    (c' : β → β → Bool) :
    ¬ IsCheck (fun a b : Trace => c' (h a) (h b)) := by
  refine no_check_of_collision (x := recΔ void s void) (y := recΔ void s' void)
    ?_ hpb.2 c'
  intro hEq
  exact hpb.1 (Trace.recΔ.inj hEq).2.1

/-- Payload blindness is inhabited on the kernel: the constant map is blind at
every distinct pair, so the separation theorem is not vacuous. A sharper
witness is any measure reading the counter only. -/
theorem payloadBlind_nonvacuous :
    PayloadBlindAt (fun _ : Trace => (0 : ℕ)) void (delta void) := by
  refine ⟨?_, rfl⟩
  intro h
  exact Trace.noConfusion h

/-- R5 witness for the whole module: the check interface is inhabited on the
kernel carrier, and the barrier is non-vacuous there because a collapsing map
exists. -/
theorem module_nonvacuous :
    IsCheck structEq ∧
      ∃ (h : Trace → Trace), ¬ Function.Injective h := by
  refine ⟨structEq_isCheck, ⟨fun _ => void, ?_⟩⟩
  intro hinj
  have := hinj (a₁ := void) (a₂ := delta void) rfl
  exact Trace.noConfusion this

end OperatorKO7.Meta.DistinctionBoundary.UniqueCheck
