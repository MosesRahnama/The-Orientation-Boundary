import OperatorKO7.Meta.BarrierPumpDischarge_Schema
import OperatorKO7.Meta.FreeStepDuplicatingSyntax

/-!
# The three dominance premises: where they are free, and where they are load-bearing

The bounded cross-term quadratic, bounded multilinear, and generalized bounded-polynomial
barriers each carry one remaining hypothesis after the growth half was discharged in
`Meta/BarrierPumpDischarge_Schema.lean`: `CrossTermBoundedAtBase`, `MultilinearDominatedAtBase`,
and `EventuallyDominatedAtBase`. This module settles all three, in both directions.

**Discharged.** Each premise follows from the class axioms `1 ≤ wrap_left` and `1 ≤ wrap_right`
alone as soon as the recursor does not couple the step argument to the counter: zero cross
coefficient in the quadratic family, no monomial using both the step and the counter in the
multilinear family, and counter exponent zero in every monomial of the polynomial family. On those
subclasses the three barriers are unconditional.

**Load-bearing.** Coupling is exactly what breaks them. `crossCoupledWeight` is one compiled
interpretation of the free syntax, presented as a member of all three classes at once, that
violates all three premises and orients the duplicating step strictly and uniformly. So each
premise is necessary, each theorem is sharp, and
`polynomial_orienter_violates_base_dominance` is non-vacuous.

The interpretation is `M(base) = 1`, `M(succ t) = 1 + M(t)`, `M(wrap x y) = M(x) + M(y)`, and
`M(recur b s n) = M(n) + M(s) · M(n)`. The single cross monomial `M(s) · M(n)` is what lets the
counter step multiply the step argument, so advancing the counter buys one extra copy of the step
argument and pays for the wrapper's duplication.

Relation: the schema duplicating step at the root. Closure: root.
External trust: none. Mathlib only.
Named method: bounded cross-term quadratic, bounded multilinear, and bounded polynomial direct
interpretations.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-! ## Discharge: the uncoupled subclasses are unconditional -/

/-- With no cross coefficient the bounded-coupling premise follows from the class axioms. -/
theorem crossTermBoundedAtBase_of_no_cross {S : StepDuplicatingSchema}
    (M : CrossTermQuadraticMeasure S) (hx : M.recur_cross = 0) :
    CrossTermBoundedAtBase M := by
  have hl := M.h_wrap_left_pos
  have hr := M.h_wrap_right_pos
  have hmul : M.recur_step ≤ M.wrap_right * M.recur_step :=
    Nat.le_mul_of_pos_left _ hr
  simp only [CrossTermBoundedAtBase, hx, Nat.zero_mul, Nat.add_zero]
  omega

/-- **The bounded cross-term quadratic barrier is unconditional on the uncoupled subclass.** -/
theorem no_crossTerm_orients_dup_step_of_no_cross {S : StepDuplicatingSchema}
    (M : CrossTermQuadraticMeasure S) (hx : M.recur_cross = 0) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) :=
  no_cross_quadratic_orients_dup_step_of_bounded M (crossTermBoundedAtBase_of_no_cross M hx)

/-- No monomial of the table uses both the step argument and the counter. -/
def NoStepCounterCoupling {S : StepDuplicatingSchema} (M : BoundedMultilinearMeasure S) : Prop :=
  ∀ m ∈ M.monomials, m.useStep = true → m.useCounter = false

/-- Without step-counter coupling the frozen step coefficient does not see the counter. -/
theorem monomialStepCoeffSum_counter_free (ms : List MultilinearMonomial)
    (h : ∀ m ∈ ms, m.useStep = true → m.useCounter = false) (B N N' : Nat) :
    monomialStepCoeffSum ms B N = monomialStepCoeffSum ms B N' := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      have hm := h m (List.mem_cons_self ..)
      have hrest : ∀ x ∈ ms, x.useStep = true → x.useCounter = false :=
        fun x hx => h x (List.mem_cons_of_mem _ hx)
      cases hstep : m.useStep with
      | false => simp [MultilinearMonomial.stepCoeff, hstep, ih hrest]
      | true =>
          simp [MultilinearMonomial.stepCoeff, hstep, hm hstep, MultilinearMonomial.factor,
            ih hrest]

/-- With no step-counter coupling the frozen dominance premise follows from the class axioms. -/
theorem multilinearDominatedAtBase_of_no_coupling {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) (h : NoStepCounterCoupling M) :
    MultilinearDominatedAtBase M := by
  have hl := M.h_wrap_left_pos
  have hr := M.h_wrap_right_pos
  have heq :
      M.stepCoeffSum M.c_base (M.succ_bias + M.succ_scale * M.c_base) =
        M.stepCoeffSum M.c_base M.c_base :=
    monomialStepCoeffSum_counter_free M.monomials h M.c_base _ _
  have hmul :
      M.recur_step + M.stepCoeffSum M.c_base M.c_base ≤
        M.wrap_right * (M.recur_step + M.stepCoeffSum M.c_base M.c_base) :=
    Nat.le_mul_of_pos_left _ hr
  simp only [MultilinearDominatedAtBase, heq]
  omega

/-- **The bounded multilinear barrier is unconditional on the uncoupled subclass.** -/
theorem no_multilinear_orients_dup_step_of_no_coupling {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) (h : NoStepCounterCoupling M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) :=
  no_multilinear_orients_dup_step_of_dominated M (multilinearDominatedAtBase_of_no_coupling M h)

/-- Every monomial of the polynomial table has counter exponent zero. -/
def NoCounterExponent {S : StepDuplicatingSchema} (M : BoundedPolynomialMeasure S) : Prop :=
  ∀ m ∈ M.monomials, m.counterPow = 0

/-- Without a counter exponent the frozen monomial sums at the two counters agree. -/
theorem polynomialMonomialSum_counter_free (ms : List PolynomialMonomial)
    (h : ∀ m ∈ ms, m.counterPow = 0) (B Sval N N' : Nat) :
    (ms.map (fun m => m.eval B Sval N)).sum = (ms.map (fun m => m.eval B Sval N')).sum := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      have hm := h m (List.mem_cons_self ..)
      have hrest : ∀ x ∈ ms, x.counterPow = 0 := fun x hx => h x (List.mem_cons_of_mem _ hx)
      simp only [List.map_cons, List.sum_cons]
      rw [ih hrest]
      simp [PolynomialMonomial.eval, hm]

/-- With no counter exponent the frozen dominance premise follows from the class axioms. -/
theorem eventuallyDominatedAtBase_of_no_counter_exponent {S : StepDuplicatingSchema}
    (M : BoundedPolynomialMeasure S) (h : NoCounterExponent M) :
    EventuallyDominatedAtBase M := by
  have hl := M.h_wrap_left_pos
  have hr := M.h_wrap_right_pos
  refine ⟨M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base), ?_⟩
  intro Sval hS
  have heq :
      (M.monomials.map
          (fun m => m.eval M.c_base Sval (M.succ_bias + M.succ_scale * M.c_base))).sum =
        (M.monomials.map (fun m => m.eval M.c_base Sval M.c_base)).sum :=
    polynomialMonomialSum_counter_free M.monomials h M.c_base Sval _ _
  have hmulL : M.recur_step * Sval ≤ M.wrap_right * (M.recur_step * Sval) :=
    Nat.le_mul_of_pos_left _ hr
  have hmulS : Sval ≤ M.wrap_left * Sval := Nat.le_mul_of_pos_left _ hl
  have hmulM :
      (M.monomials.map (fun m => m.eval M.c_base Sval M.c_base)).sum ≤
        M.wrap_right * (M.monomials.map (fun m => m.eval M.c_base Sval M.c_base)).sum :=
    Nat.le_mul_of_pos_left _ hr
  have hmulC :
      M.recur_const + M.recur_base * M.c_base ≤
        M.wrap_right * (M.recur_const + M.recur_base * M.c_base) :=
    Nat.le_mul_of_pos_left _ hr
  simp only [BoundedPolynomialMeasure.sourceFrozenAtBase,
    BoundedPolynomialMeasure.targetFrozenAtBase, heq]
  have hexpand :
      M.wrap_right *
          (M.recur_const + M.recur_base * M.c_base + M.recur_step * Sval +
            M.recur_counter * M.c_base +
            (M.monomials.map (fun m => m.eval M.c_base Sval M.c_base)).sum) =
        M.wrap_right * (M.recur_const + M.recur_base * M.c_base) +
          M.wrap_right * (M.recur_step * Sval) +
          M.wrap_right * (M.recur_counter * M.c_base) +
          M.wrap_right * (M.monomials.map (fun m => m.eval M.c_base Sval M.c_base)).sum := by
    ring
  rw [hexpand]
  omega

/-- **The generalized polynomial barrier is unconditional on the counter-uncoupled subclass.** -/
theorem no_polynomial_orients_dup_step_of_no_counter_exponent {S : StepDuplicatingSchema}
    (M : BoundedPolynomialMeasure S) (h : NoCounterExponent M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) :=
  no_polynomial_orients_dup_step_of_dominated M
    (eventuallyDominatedAtBase_of_no_counter_exponent M h)

/-! ## The necessity witness: one interpretation, three violated premises -/

/-- `M(base) = 1`, `M(succ t) = 1 + M(t)`, `M(wrap x y) = M(x) + M(y)`,
`M(recur b s n) = M(n) + M(s) · M(n)`. -/
def crossCoupledWeight : FreeTerm → Nat
  | FreeTerm.base => 1
  | FreeTerm.succ t => 1 + crossCoupledWeight t
  | FreeTerm.wrap x y => crossCoupledWeight x + crossCoupledWeight y
  | FreeTerm.recur _ s n => crossCoupledWeight n + crossCoupledWeight s * crossCoupledWeight n

/-- **The witness orients the duplicating step**, strictly and uniformly in the three
arguments. Advancing the counter buys one extra copy of the step argument through the cross
monomial, which pays for the wrapper's duplication and leaves one unit over. -/
theorem crossCoupledWeight_strictly_orients :
    ∀ (b s n : FreeTerm),
      crossCoupledWeight (freeSchema.wrap s (freeSchema.recur b s n)) <
        crossCoupledWeight (freeSchema.recur b s (freeSchema.succ n)) := by
  intro b s n
  simp only [freeSchema, crossCoupledWeight]
  have h : crossCoupledWeight s * (1 + crossCoupledWeight n) =
      crossCoupledWeight s + crossCoupledWeight s * crossCoupledWeight n := by ring
  rw [h]
  omega

/-- The witness as a member of the bounded cross-term quadratic class. -/
def crossCoupledQuadratic : CrossTermQuadraticMeasure freeSchema where
  eval := crossCoupledWeight
  c_base := 1
  succ_bias := 1
  succ_scale := 1
  wrap_const := 0
  wrap_left := 1
  wrap_right := 1
  recur_const := 0
  recur_base := 0
  recur_step := 0
  recur_counter := 1
  recur_quad := 0
  recur_cross := 1
  eval_base := rfl
  eval_succ := fun t => by simp [freeSchema, crossCoupledWeight]
  eval_wrap := fun x y => by simp [freeSchema, crossCoupledWeight]
  eval_recur := fun b s n => by simp [freeSchema, crossCoupledWeight]
  h_wrap_left_pos := le_refl 1
  h_wrap_right_pos := le_refl 1

/-- The witness as a member of the bounded multilinear class, with the single cross monomial
`M(s) · M(n)`. -/
def crossCoupledMultilinear : BoundedMultilinearMeasure freeSchema where
  eval := crossCoupledWeight
  c_base := 1
  succ_bias := 1
  succ_scale := 1
  wrap_const := 0
  wrap_left := 1
  wrap_right := 1
  recur_const := 0
  recur_base := 0
  recur_step := 0
  recur_counter := 1
  monomials := [{ coeff := 1, useBase := false, useStep := true, useCounter := true }]
  eval_base := rfl
  eval_succ := fun t => by simp [freeSchema, crossCoupledWeight]
  eval_wrap := fun x y => by simp [freeSchema, crossCoupledWeight]
  eval_recur := fun b s n => by simp [freeSchema, crossCoupledWeight]
  h_wrap_left_pos := le_refl 1
  h_wrap_right_pos := le_refl 1

/-- The witness as a member of the generalized bounded-polynomial class. -/
def crossCoupledPolynomial : BoundedPolynomialMeasure freeSchema where
  eval := crossCoupledWeight
  c_base := 1
  succ_bias := 1
  succ_scale := 1
  wrap_const := 0
  wrap_left := 1
  wrap_right := 1
  recur_const := 0
  recur_base := 0
  recur_step := 0
  recur_counter := 1
  monomials := [{ coeff := 1, basePow := 0, stepPow := 1, counterPow := 1 }]
  eval_base := rfl
  eval_succ := fun t => by simp [freeSchema, crossCoupledWeight]
  eval_wrap := fun x y => by simp [freeSchema, crossCoupledWeight]
  eval_recur := fun b s n => by simp [freeSchema, crossCoupledWeight]
  h_wrap_left_pos := le_refl 1
  h_wrap_right_pos := le_refl 1

/-! ## Each premise is load-bearing -/

/-- **`CrossTermBoundedAtBase` is necessary.** -/
theorem crossCoupledQuadratic_not_boundedAtBase :
    ¬ CrossTermBoundedAtBase crossCoupledQuadratic := by
  simp [CrossTermBoundedAtBase, crossCoupledQuadratic]

/-- **`MultilinearDominatedAtBase` is necessary.** -/
theorem crossCoupledMultilinear_not_dominatedAtBase :
    ¬ MultilinearDominatedAtBase crossCoupledMultilinear := by
  simp [MultilinearDominatedAtBase, crossCoupledMultilinear,
    BoundedMultilinearMeasure.stepCoeffSum]

/-- **`EventuallyDominatedAtBase` is necessary.** The frozen source polynomial exceeds the frozen
target polynomial by exactly one at every pumped value, so no cutoff exists. -/
theorem crossCoupledPolynomial_not_eventuallyDominated :
    ¬ EventuallyDominatedAtBase crossCoupledPolynomial := by
  rintro ⟨K, hK⟩
  have h := hK K (le_refl K)
  simp [BoundedPolynomialMeasure.sourceFrozenAtBase,
    BoundedPolynomialMeasure.targetFrozenAtBase, crossCoupledPolynomial] at h
  omega

/-- The witness is a compiled member of each of the three classes and orients the duplicating
step, so all three theorems are sharp: dropping the dominance premise makes each of them false. -/
theorem three_dominance_premises_are_sharp :
    (¬ CrossTermBoundedAtBase crossCoupledQuadratic
        ∧ ∀ b s n : FreeTerm,
            crossCoupledQuadratic.eval (freeSchema.wrap s (freeSchema.recur b s n)) <
              crossCoupledQuadratic.eval (freeSchema.recur b s (freeSchema.succ n)))
      ∧ (¬ MultilinearDominatedAtBase crossCoupledMultilinear
        ∧ ∀ b s n : FreeTerm,
            crossCoupledMultilinear.eval (freeSchema.wrap s (freeSchema.recur b s n)) <
              crossCoupledMultilinear.eval (freeSchema.recur b s (freeSchema.succ n)))
      ∧ (¬ EventuallyDominatedAtBase crossCoupledPolynomial
        ∧ ∀ b s n : FreeTerm,
            crossCoupledPolynomial.eval (freeSchema.wrap s (freeSchema.recur b s n)) <
              crossCoupledPolynomial.eval (freeSchema.recur b s (freeSchema.succ n))) :=
  ⟨⟨crossCoupledQuadratic_not_boundedAtBase, crossCoupledWeight_strictly_orients⟩,
   ⟨crossCoupledMultilinear_not_dominatedAtBase, crossCoupledWeight_strictly_orients⟩,
   ⟨crossCoupledPolynomial_not_eventuallyDominated, crossCoupledWeight_strictly_orients⟩⟩

/-- `polynomial_orienter_violates_base_dominance` is not vacuous: an orienter inside the class
exists, and its violation of the dominance condition is the one recorded above. -/
theorem polynomial_orienter_violates_base_dominance_nonvacuous :
    ¬ EventuallyDominatedAtBase crossCoupledPolynomial :=
  polynomial_orienter_violates_base_dominance crossCoupledPolynomial
    crossCoupledWeight_strictly_orients

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
