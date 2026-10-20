import OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure

/-!
# Vector Grammar Closure: the unconditional matrix-side barrier

`Meta/BoundaryGeneral/DirectMeasureGrammarClosure.lean` closes the scalar side of the
direct barrier with no hypotheses beyond orientation itself: over the closed measure
grammar, `orients_implies_payload_blind` shows that orienting the duplicating step forces
payload-blindness. That statement is restricted to scalar measures.

This module lifts the same closure to vector-valued measures and to arbitrary ambient
orders on them, again with no pump hypothesis, no dominance hypothesis, and no
scalarization certificate. Three strengthenings carry the lift.

1. `weakly_orients_implies_payload_blind` weakens the hypothesis of the scalar theorem
   from strict decrease to nonincrease. Lexicographic and priority orders only ever force
   nonincrease of their primary coordinate, so the strict form cannot reach them.

2. `dominated_scalar_orients_implies_payload_blind` replaces the scalarization certificate
   by membership in the grammar. Any ambient order whose strict comparison forces
   nonincrease of a scalar functional that agrees with some grammar expression on the
   measure's image is blocked, whatever the functional is.

3. The componentwise, primary-first, and weighted-projection orders are then instances
   rather than separate theorems.

The resulting statement is uniform over dimension, over the choice of ambient order, and
over the choice of scalarization: a vector measure with grammar-expressible scalarization
orients the duplicating step only if that scalarization is payload-blind.

Trust: Mathlib-only; no `sorry`, no `admit`, no new top-level `axiom`, no `native_decide`,
no `@[csimp]`, no `unsafe`.
-/

namespace OperatorKO7.Meta.BoundaryGeneral.VectorGrammarClosure

open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure

/-! ## 1. Nonstrict orientation still forces payload-blindness -/

/-- Nonstrict orientation of the duplicating step: the measure fails to increase across
every duplicating rewrite. Strict orientation implies this, and lexicographic or
priority orders force exactly this much on their primary coordinate. -/
def WeaklyOrientsDupStep (m : Nat → Nat → Nat) : Prop :=
  ∀ c p L, 1 ≤ L → m c (p + L) ≤ m (c + 1) p

theorem weaklyOrients_of_orients {m : Nat → Nat → Nat} (h : OrientsDupStep m) :
    WeaklyOrientsDupStep m := fun c p L hL => Nat.le_of_lt (h c p L hL)

/-- **Nonstrict grammar closure.** Over the closed measure grammar, merely failing to
increase across the duplicating step already forces payload-blindness. No pump hypothesis,
no dominance hypothesis, no unboundedness hypothesis. -/
theorem weakly_orients_implies_payload_blind (e : MeasureExpr)
    (h : WeaklyOrientsDupStep e.eval) : PayloadBlind e.eval := by
  intro c p p'
  rcases eval_section_const_or_unbounded e c with hconst | hunb
  · exact hconst p p'
  · exfalso
    obtain ⟨q, hq⟩ := hunb (e.eval (c + 1) 0 + 1)
    have ho := h c 0 (q + 1) (Nat.succ_le_succ (Nat.zero_le q))
    have hge : e.eval c q ≤ e.eval c (0 + (q + 1)) :=
      eval_payloadMonotone e c q (0 + (q + 1)) (by omega)
    omega

/-- The strict form is recovered from the nonstrict form. -/
theorem orients_implies_payload_blind' (e : MeasureExpr)
    (h : OrientsDupStep e.eval) : PayloadBlind e.eval :=
  weakly_orients_implies_payload_blind e (weaklyOrients_of_orients h)

/-! ## 2. Vector-valued measures over the grammar -/

/-- A vector-valued direct measure of dimension `d`, each coordinate given by a grammar
expression on the canonical `(counter, payload)` carrier. -/
def VecMeasure (d : Nat) : Type := Fin d → MeasureExpr

/-- Pointwise evaluation of a vector measure. -/
def VecMeasure.eval {d : Nat} (M : VecMeasure d) (c p : Nat) : Fin d → Nat :=
  fun i => (M i).eval c p

/-- A vector measure orients the duplicating step under an ambient order `R` when every
duplicating rewrite is an `R`-descent. -/
def VecOrients {d : Nat} (M : VecMeasure d)
    (R : (Fin d → Nat) → (Fin d → Nat) → Prop) : Prop :=
  ∀ c p L, 1 ≤ L → R (M.eval c (p + L)) (M.eval (c + 1) p)

/-- An ambient order is dominated by a scalar functional when every strict comparison
forces that functional to fail to increase. This is the weakest useful link between an
order and a scalar reading of it: componentwise, lexicographic, priority, weighted-sum,
fixed-row, and row-sum orders all satisfy it. -/
def DominatedByScalar {d : Nat}
    (R : (Fin d → Nat) → (Fin d → Nat) → Prop) (pi : (Fin d → Nat) → Nat) : Prop :=
  ∀ u v, R u v → pi u ≤ pi v

/-! ## 3. The unconditional matrix-side barrier -/

/-- **Vector grammar closure.** Let `M` be a vector measure over the grammar, let `R` be any
ambient order on its codomain, and let `pi` be any scalar functional that `R` dominates. If
`pi` composed with `M` agrees with some grammar expression `e`, then orienting the
duplicating step under `R` forces `e` to be payload-blind.

The hypotheses are: the order dominates the scalar, and the scalar lands in the grammar.
There is no pump hypothesis, no base-dominance hypothesis, and no scalarization
certificate. -/
theorem dominated_scalar_orients_implies_payload_blind {d : Nat}
    (M : VecMeasure d) (R : (Fin d → Nat) → (Fin d → Nat) → Prop)
    (pi : (Fin d → Nat) → Nat) (e : MeasureExpr)
    (hpi : ∀ c p, pi (M.eval c p) = e.eval c p)
    (hdom : DominatedByScalar R pi)
    (horients : VecOrients M R) :
    PayloadBlind e.eval := by
  refine weakly_orients_implies_payload_blind e ?_
  intro c p L hL
  have hstep := hdom _ _ (horients c p L hL)
  rw [hpi c (p + L), hpi (c + 1) p] at hstep
  exact hstep

/-- Contrapositive reading: a payload-reading scalarization blocks orientation outright. -/
theorem payload_reading_scalar_blocks {d : Nat}
    (M : VecMeasure d) (R : (Fin d → Nat) → (Fin d → Nat) → Prop)
    (pi : (Fin d → Nat) → Nat) (e : MeasureExpr)
    (hpi : ∀ c p, pi (M.eval c p) = e.eval c p)
    (hdom : DominatedByScalar R pi)
    (hread : ¬ PayloadBlind e.eval) :
    ¬ VecOrients M R := by
  intro horients
  exact hread (dominated_scalar_orients_implies_payload_blind M R pi e hpi hdom horients)

/-! ## 4. The standard orders are instances -/

/-- Strict componentwise order. -/
def VecLt {d : Nat} (u v : Fin d → Nat) : Prop := ∀ i, u i < v i

/-- Componentwise order is dominated by every coordinate. -/
theorem vecLt_dominatedByScalar {d : Nat} (i : Fin d) :
    DominatedByScalar (d := d) VecLt (fun u => u i) :=
  fun _ _ h => Nat.le_of_lt (h i)

/-- Priority order with a designated primary coordinate compared first. -/
def PrimaryFirstLt {d : Nat} (i : Fin d) (u v : Fin d → Nat) : Prop :=
  u i < v i ∨ (u i = v i ∧ ∃ j, j ≠ i ∧ u j < v j)

/-- A primary-first order is dominated by its primary coordinate. -/
theorem primaryFirstLt_dominatedByScalar {d : Nat} (i : Fin d) :
    DominatedByScalar (d := d) (PrimaryFirstLt i) (fun u => u i) := by
  intro u v h
  rcases h with hlt | ⟨heq, _⟩
  · exact Nat.le_of_lt hlt
  · exact Nat.le_of_eq heq

/-- **Componentwise instance.** A vector measure over the grammar, ordered componentwise,
orients the duplicating step only if every coordinate is payload-blind. Unconditional. -/
theorem componentwise_orients_implies_all_payload_blind {d : Nat}
    (M : VecMeasure d) (horients : VecOrients M VecLt) (i : Fin d) :
    PayloadBlind (M i).eval :=
  dominated_scalar_orients_implies_payload_blind M VecLt (fun u => u i) (M i)
    (fun _ _ => rfl) (vecLt_dominatedByScalar i) horients

/-- **Primary-first instance.** A vector measure over the grammar, ordered with a
designated primary coordinate first, orients the duplicating step only if that primary
coordinate is payload-blind. Unconditional, and uniform over the choice of primary. -/
theorem primaryFirst_orients_implies_primary_payload_blind {d : Nat}
    (M : VecMeasure d) (i : Fin d) (horients : VecOrients M (PrimaryFirstLt i)) :
    PayloadBlind (M i).eval :=
  dominated_scalar_orients_implies_payload_blind M (PrimaryFirstLt i) (fun u => u i) (M i)
    (fun _ _ => rfl) (primaryFirstLt_dominatedByScalar i) horients

/-! ## 5. Weighted scalarizations land in the grammar -/

/-- The grammar expression realizing a weighted sum of the coordinates of a vector measure,
built by folding `smul` and `add` over a coordinate list. -/
def weightedExpr {d : Nat} (w : Fin d → Nat) (M : VecMeasure d) : List (Fin d) → MeasureExpr
  | [] => MeasureExpr.const 0
  | i :: rest => MeasureExpr.add (MeasureExpr.smul (w i) (M i)) (weightedExpr w M rest)

/-- The folded expression evaluates to the corresponding weighted sum. -/
theorem weightedExpr_eval {d : Nat} (w : Fin d → Nat) (M : VecMeasure d) :
    ∀ (l : List (Fin d)) (c p : Nat),
      (weightedExpr w M l).eval c p = (l.map (fun i => w i * (M i).eval c p)).sum
  | [], c, p => by simp [weightedExpr, MeasureExpr.eval]
  | i :: rest, c, p => by
      simp [weightedExpr, MeasureExpr.eval, weightedExpr_eval w M rest c p]

/-- The scalar functional realized by a weighted sum over a coordinate list. -/
def weightedProj {d : Nat} (w : Fin d → Nat) (l : List (Fin d)) (u : Fin d → Nat) : Nat :=
  (l.map (fun i => w i * u i)).sum

/-- **Weighted-projection instance.** Every natural-weighted sum of the coordinates is a
grammar expression, so any ambient order dominated by such a sum is blocked unless that sum
is payload-blind. This covers weighted scalar projections, fixed-row readings (a singleton
list with unit weight), and row sums (the full coordinate list with all weights one), with
no scalarization certificate and no pump. -/
theorem weighted_orients_implies_payload_blind {d : Nat}
    (M : VecMeasure d) (w : Fin d → Nat) (l : List (Fin d))
    (R : (Fin d → Nat) → (Fin d → Nat) → Prop)
    (hdom : DominatedByScalar R (weightedProj w l))
    (horients : VecOrients M R) :
    PayloadBlind (weightedExpr w M l).eval := by
  refine dominated_scalar_orients_implies_payload_blind M R (weightedProj w l)
    (weightedExpr w M l) ?_ hdom horients
  intro c p
  simp [weightedProj, weightedExpr_eval w M l c p, VecMeasure.eval]

/-! ## 6. Capstone -/

/-- The unconditional direct-measure barrier, scalar and vector sides together.

Read as one statement: a direct measure built from the counter and payload coordinates by
constants, sums, products, pointwise maxima, and natural scalar multiples orients the
duplicating step only if it is payload-blind. This holds for scalar measures under strict
decrease, for scalar measures under mere nonincrease, and for vector measures of any finite
dimension under any ambient order dominated by any grammar-expressible scalarization. -/
theorem unconditional_direct_measure_barrier :
    (∀ e : MeasureExpr, OrientsDupStep e.eval → PayloadBlind e.eval)
    ∧ (∀ e : MeasureExpr, WeaklyOrientsDupStep e.eval → PayloadBlind e.eval)
    ∧ (∀ (d : Nat) (M : VecMeasure d) (R : (Fin d → Nat) → (Fin d → Nat) → Prop)
        (pi : (Fin d → Nat) → Nat) (e : MeasureExpr),
        (∀ c p, pi (M.eval c p) = e.eval c p) →
        DominatedByScalar R pi →
        VecOrients M R →
        PayloadBlind e.eval) := by
  refine ⟨fun e h => orients_implies_payload_blind' e h,
    fun e h => weakly_orients_implies_payload_blind e h, ?_⟩
  intro d M R pi e hpi hdom horients
  exact dominated_scalar_orients_implies_payload_blind M R pi e hpi hdom horients

end OperatorKO7.Meta.BoundaryGeneral.VectorGrammarClosure
