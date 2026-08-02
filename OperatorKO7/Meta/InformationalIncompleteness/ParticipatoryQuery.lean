import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
import OperatorKO7.Meta.InformationalIncompleteness.DiagonalEntropy
import OperatorKO7.Meta.InformationalIncompleteness.QueryInterface

/-!
# Participatory queries: when the act of querying bears on the object

The base query interface of `QueryInterface` is *passive*: the answer is a readout that does not change the
object. A *participatory* (active) query is one whose act bears on the object queried. The
information-theoretic content of "issuing the query couples the querant to the object" is that the querant's
record and the object's outcome acquire correlation that is created by the act and is absent under the null
(no-participation) action. The canonical physical instance is a measurement with back-action (the
measurement disturbs the system); a domain-specific instance (a capital query that moves the object it
queries) is developed elsewhere (the Boundary Premium Program), not here.

The querant's record is a deterministic function of the outcome given the placed action, so the correlation
`I(record ; outcome)` equals the entropy of the record law (the pushforward of the outcome law along the
record map). Load-bearing facts:

* `null_action_zero_correlation` — a flat record (the null action) yields zero correlation.
* `participation_creates_correlation` — an action that takes a distinguishing record on two
  positive-probability outcomes yields strictly positive correlation: the querant is non-separable from the
  object, created by the act. Reuses `query_confession_condEntropy_pos`.
* `effective_action_perturbs_object` — back-action: an action whose outcome law differs from the null is one
  that literally changes the object's distribution at some outcome.
* `resolution_arc` — the non-vacuous query becomes vacuous at the boundary event: the realised information is
  the pre-resolution entropy minus the post-resolution entropy, strictly positive for a non-vacuous
  pre-state with a complete (point-mass) resolution. Reuses `H_pointMass`.

Honesty: finite classical information theory. The quantum reading (entanglement, measurement back-action,
collapse) and any domain reading are interpretive labels carried in prose and docstrings, never in a
theorem; non-separability here is positive classical mutual information, never asserted to be physical
quantum entanglement. The module formalises the structural theorems, not the empirical claim that any real
act has a given effect. No rewriting relation. Trust: no `sorry`/`admit`/`axiom`/`native_decide`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.InformationalIncompleteness.ParticipatoryQuery

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.DiagonalEntropy
open OperatorKO7.Meta.InformationalIncompleteness.QueryInterface

variable {X Rec A : Type} [Fintype X] [Fintype Rec] [DecidableEq Rec]

/-! ## Pushforward bookkeeping (local; the record law is a pushforward of the outcome law). -/

omit [Fintype Rec] in
/-- The pushforward of a nonnegative weighting is nonnegative. -/
theorem pushforward_nonneg (e : X → Rec) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (r : Rec) :
    0 ≤ pushforward e p r := by
  unfold pushforward
  apply Finset.sum_nonneg
  intro x _
  by_cases h : e x = r
  · rw [if_pos h]; exact hp x
  · simp [if_neg h]

/-- The pushforward preserves total mass: `∑_r (pushforward e p) r = ∑_x p x`. -/
theorem pushforward_total_mass (e : X → Rec) (p : X → ℝ) :
    (∑ r, pushforward e p r) = ∑ x, p x := by
  unfold pushforward
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp

omit [Fintype Rec] in
/-- At a record value in the image, the pushforward mass is at least the mass of any preimage point. -/
theorem pushforward_ge_term (e : X → Rec) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (x : X) :
    p x ≤ pushforward e p (e x) := by
  unfold pushforward
  have hnn : ∀ x' ∈ Finset.univ, 0 ≤ (if e x' = e x then p x' else 0) := by
    intro x' _
    by_cases h : e x' = e x
    · rw [if_pos h]; exact hp x'
    · simp [if_neg h]
  have hle := Finset.single_le_sum hnn (Finset.mem_univ x)
  simpa using hle

/-! ## The participatory query. -/

/-- The querant's record law under action `a`: the pushforward of the outcome law along the record map. -/
noncomputable def recordLaw (R : A → X → Rec) (pObj : A → X → ℝ) (a : A) : Rec → ℝ :=
  pushforward (R a) (pObj a)

/-- The participation correlation `I(record ; outcome)` under action `a`, equal to the record-law entropy
(the record is a deterministic function of the outcome given the placed action). -/
noncomputable def participationInfo (R : A → X → Rec) (pObj : A → X → ℝ) (a : A) : ℝ :=
  H (recordLaw R pObj a)

/-- An action is `effective` (back-acting) if its outcome law differs from the null action's. -/
def effectiveAction (pObj : A → X → ℝ) (a a₀ : A) : Prop := pObj a ≠ pObj a₀

/--
Proves: the null action creates no correlation. If the record under `a₀` is flat (constant value `v`, i.e.
  no participation) and the outcome law under `a₀` is a probability distribution, then the participation
  correlation is zero. No participation, no coupling.
Does not prove: anything about non-null actions. Relation/Closure: not applicable. Trust: kernel-only.
Scope: every flat record value `v` and probability outcome law under `a₀`.
-/
theorem null_action_zero_correlation (R : A → X → Rec) (pObj : A → X → ℝ) (a₀ : A)
    (v : Rec) (hconst : ∀ x, R a₀ x = v) (hprob : ∑ x, pObj a₀ x = 1) :
    participationInfo R pObj a₀ = 0 := by
  unfold participationInfo recordLaw
  have hpf : pushforward (R a₀) (pObj a₀) = pointMass v := by
    funext r
    simp only [pushforward, pointMass]
    by_cases h : r = v
    · rw [if_pos h, ← hprob]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      have hx : R a₀ x = r := by rw [hconst x]; exact h.symm
      rw [if_pos hx]
    · rw [if_neg h]
      refine Finset.sum_eq_zero (fun x _ => ?_)
      have hx : R a₀ x ≠ r := by rw [hconst x]; exact fun hvr => h hvr.symm
      rw [if_neg hx]
  rw [hpf, H_pointMass]

/--
Proves: participation creates correlation (the querant is coupled to the object by the act). If under action
  `a` the outcome law is a sub-distribution and there are two positive-probability outcomes `x₁, x₂` with
  distinct records `R a x₁ ≠ R a x₂` (the action takes a distinguishing record), then the participation
  correlation is strictly positive: the querant's record and the object's outcome are non-separable, created
  by the act. Reuses `query_confession_condEntropy_pos` on the record law.
Does not prove: that any empirical action has this property (that is observed, not proved).
Relation/Closure: not applicable. Trust: kernel-only.
Scope: every action with a sub-distribution outcome law and two distinct-record positive-mass outcomes.
-/
theorem participation_creates_correlation (R : A → X → Rec) (pObj : A → X → ℝ) (a : A)
    (h0 : ∀ x, 0 ≤ pObj a x) (hsum : ∑ x, pObj a x ≤ 1)
    (x₁ x₂ : X) (hp1 : 0 < pObj a x₁) (hp2 : 0 < pObj a x₂)
    (hrec : R a x₁ ≠ R a x₂) :
    0 < participationInfo R pObj a := by
  unfold participationInfo recordLaw
  exact query_confession_condEntropy_pos (pushforward (R a) (pObj a))
    (pushforward_nonneg (R a) (pObj a) h0)
    (by rw [pushforward_total_mass]; exact hsum)
    (R a x₁) (R a x₂) hrec
    (lt_of_lt_of_le hp1 (pushforward_ge_term (R a) (pObj a) h0 x₁))
    (lt_of_lt_of_le hp2 (pushforward_ge_term (R a) (pObj a) h0 x₂))

omit [Fintype X] in
/--
Proves: back-action. An effective action (its outcome law differs from the null action's) changes the
  object's distribution at some outcome: `∃ x, pObj a x ≠ pObj a₀ x`. The querant is part of the object's
  law, not an outside observer.
Does not prove: a quantitative effect bound. Relation/Closure: not applicable. Trust: kernel-only.
Scope: every pair of actions with distinct outcome laws.
-/
theorem effective_action_perturbs_object (pObj : A → X → ℝ) (a a₀ : A)
    (h : effectiveAction pObj a a₀) : ∃ x, pObj a x ≠ pObj a₀ x := by
  by_contra hcon
  push_neg at hcon
  exact h (funext hcon)

/--
Proves: the resolution arc. A non-vacuous query (sub-distribution pre-resolution outcome law with two
  distinct positive-mass outcomes, so `H(pre) > 0`) that is completely resolved at the boundary event
  (post-state a point mass at the realised outcome, so `H(post) = 0`) yields a strictly positive realised
  information `0 < H(pre) - H(post)`. The non-vacuous query has become vacuous, and the entropy drop is
  exactly the information the boundary event committed. Reuses `query_confession_condEntropy_pos` and
  `H_pointMass`.
Does not prove: a model of the resolution channel; complete resolution is the `pointMass` hypothesis.
Relation/Closure: not applicable. Trust: kernel-only.
Scope: every non-vacuous pre-resolution sub-distribution and complete (point-mass) resolution.
-/
theorem resolution_arc [DecidableEq X] (p : X → ℝ) (h0 : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x ≤ 1)
    (x₁ x₂ : X) (hne : x₁ ≠ x₂) (hp1 : 0 < p x₁) (hp2 : 0 < p x₂) (x_real : X) :
    0 < H p - H (pointMass x_real) := by
  rw [H_pointMass, sub_zero]
  exact query_confession_condEntropy_pos p h0 hsum x₁ x₂ hne hp1 hp2

/-! ## R5 non-vacuity witnesses. -/

/-- R5 (participation couples querant to object): a single action that takes a distinguishing record (the
record tracks the outcome) on a binary uniform object law has strictly positive participation correlation. -/
theorem participation_witness_pos :
    0 < participationInfo (A := Fin 1) (X := Fin 2) (Rec := Fin 2)
      (fun _ x => x) (fun _ _ => (1 : ℝ) / 2) 0 :=
  participation_creates_correlation (fun _ x => x) (fun _ _ => (1 : ℝ) / 2) 0
    (fun _ => by norm_num) (by rw [Fin.sum_univ_two]; norm_num)
    (0 : Fin 2) (1 : Fin 2) (by norm_num) (by norm_num) (by decide)

/-- R5 (no participation, no coupling): a flat record (always the same value) on the same object law has
zero participation correlation. -/
theorem null_witness_zero :
    participationInfo (A := Fin 1) (X := Fin 2) (Rec := Fin 2)
      (fun _ _ => (0 : Fin 2)) (fun _ _ => (1 : ℝ) / 2) 0 = 0 :=
  null_action_zero_correlation (fun _ _ => (0 : Fin 2)) (fun _ _ => (1 : ℝ) / 2) 0
    (0 : Fin 2) (fun _ => rfl) (by rw [Fin.sum_univ_two]; norm_num)

/-! ## Headline axiom audit (subset of {propext, Classical.choice, Quot.sound}). -/

#print axioms null_action_zero_correlation
#print axioms participation_creates_correlation
#print axioms effective_action_perturbs_object
#print axioms resolution_arc
#print axioms participation_witness_pos
#print axioms null_witness_zero

end OperatorKO7.Meta.InformationalIncompleteness.ParticipatoryQuery
