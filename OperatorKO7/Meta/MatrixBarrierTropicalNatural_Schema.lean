import OperatorKO7.Meta.MatrixBarrierNatural_Schema
import OperatorKO7.Meta.FreeStepDuplicatingSyntax

/-!
# The certificate-free tropical matrix barrier is false

`Meta/MatrixBarrierNatural_Schema.lean` and `Meta/MatrixBarrierArcticNatural_Schema.lean` prove
certificate-free barriers over the natural semiring and over the arctic (max-plus) semiring. Both
proofs run on one mechanism: the `(i, i)` entry of a matrix is a **lower** bound for coordinate `i`
of the action, so a positive wrapper diagonal entry forces the self-nested wrapper chain, or the
strictly oriented recursor chain, to grow without bound, while orientation caps it.

Over the tropical (min-plus) semiring the inequality reverses. Aggregation is `min`, so the
`(i, i)` entry of a matrix is an **upper** bound for coordinate `i` of the action
(`TropicalMatrix.act_le_diag`), and the wrapper bias caps the wrapper from above no matter how
large its diagonal entries are. There is no pump, and the barrier is not merely unproved: it is
false.

`tropicalEscapeMeasure` is the compiled witness. It is a one-dimensional min-plus interpretation of
the free syntax, both of whose wrapper diagonal entries are positive, whose coordinate is finite at
every term, and which orients the duplicating step strictly and uniformly. So the tropical analogue
of `no_natMatrix_orients_dup_step_of_tracked_strict` and of
`no_arcticMatrix_orients_dup_step_of_tracked_strict_pumpFree` fails, and any tropical barrier must
carry extra data. The scalarization certificates of
`Meta/MatrixBarrierArcticTropical_Schema.lean` are exactly such data, and
`tropicalEscapeMeasure_no_scalar_dominance` records that the witness carries none.

Relation: the schema duplicating step at the root. Closure: root.
External trust: none. Mathlib only.
Named method: tropical (min-plus) matrix interpretations; the order is a parameter.
Status: KILLED. The target statement is false; this module carries the counterexample.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-! ## The tropical semiring -/

/-- Tropical scalars: `top` is the neutral element of `min` and absorbs under `+`. -/
inductive TropicalNat where
  | top
  | fin : Nat → TropicalNat
  deriving DecidableEq, Repr

/-- Tropical addition: `min`, with `top` neutral. -/
def tropicalMin : TropicalNat → TropicalNat → TropicalNat
  | TropicalNat.top, y => y
  | x, TropicalNat.top => x
  | TropicalNat.fin a, TropicalNat.fin b => TropicalNat.fin (min a b)

/-- Tropical multiplication: `+`, with `top` absorbing. -/
def tropicalPlus : TropicalNat → TropicalNat → TropicalNat
  | TropicalNat.top, _ => TropicalNat.top
  | _, TropicalNat.top => TropicalNat.top
  | TropicalNat.fin a, TropicalNat.fin b => TropicalNat.fin (a + b)

/-- Tropical order: `top` is greatest, finite values compare as naturals. -/
def TropicalLe : TropicalNat → TropicalNat → Prop
  | _, TropicalNat.top => True
  | TropicalNat.top, TropicalNat.fin _ => False
  | TropicalNat.fin a, TropicalNat.fin b => a ≤ b

/-- Strict tropical comparison on a finite coordinate. -/
def TropicalLt : TropicalNat → TropicalNat → Prop
  | TropicalNat.fin x, TropicalNat.fin y => x < y
  | _, _ => False

theorem tropicalLe_refl (x : TropicalNat) : TropicalLe x x := by
  cases x <;> simp [TropicalLe]

theorem tropicalMin_le_left (x y : TropicalNat) : TropicalLe (tropicalMin x y) x := by
  cases x <;> cases y <;> simp [TropicalLe, tropicalMin]

theorem tropicalMin_le_right (x y : TropicalNat) : TropicalLe (tropicalMin x y) y := by
  cases x <;> cases y <;> simp [TropicalLe, tropicalMin]

/-! ## Tropical vectors, matrices, and the row action -/

/-- Tropical vectors of a fixed finite dimension. -/
abbrev TropicalVec (d : Nat) := Fin d → TropicalNat

/-- Coordinatewise tropical addition of vectors. -/
def tropicalVecMin {d : Nat} (u v : TropicalVec d) : TropicalVec d :=
  fun i => tropicalMin (u i) (v i)

/-- A tropical matrix in a fixed finite dimension. -/
structure TropicalMatrix (d : Nat) where
  coeff : Fin d → Fin d → TropicalNat

/-- The tropical fold is bounded above by every summand. -/
theorem tropicalLe_foldr_of_mem {α : Type} (f : α → TropicalNat) :
    ∀ (l : List α) {a : α}, a ∈ l →
      TropicalLe (l.foldr (fun x acc => tropicalMin (f x) acc) TropicalNat.top) (f a)
  | [], _, hmem => absurd hmem (by simp)
  | x :: xs, a, hmem => by
      rcases List.mem_cons.1 hmem with h | h
      · subst h
        exact tropicalMin_le_left _ _
      · refine le_trans_tropical (tropicalMin_le_right (f x) _) ?_
        exact tropicalLe_foldr_of_mem f xs h
where
  le_trans_tropical {x y z : TropicalNat} (h₁ : TropicalLe x y) (h₂ : TropicalLe y z) :
      TropicalLe x z := by
    cases x <;> cases y <;> cases z <;> simp_all [TropicalLe]
    omega

/-- The tropical matrix action: `min` over `j` of `coeff i j` times `v j`. -/
def TropicalMatrix.act {d : Nat} (A : TropicalMatrix d) (v : TropicalVec d) : TropicalVec d :=
  fun i =>
    (List.finRange d).foldr
      (fun j acc => tropicalMin (tropicalPlus (A.coeff i j) (v j)) acc) TropicalNat.top

/-- **The inequality that reverses.** Over the arctic semiring the diagonal term is a lower bound
for coordinate `i` of the action (`ArcticMatrix.diag_le_act`); over the tropical semiring it is an
upper bound. The pump that proves the natural and arctic barriers has no tropical analogue. -/
theorem TropicalMatrix.act_le_diag {d : Nat} (A : TropicalMatrix d) (v : TropicalVec d)
    (i : Fin d) :
    TropicalLe (A.act v i) (tropicalPlus (A.coeff i i) (v i)) :=
  tropicalLe_foldr_of_mem (fun j => tropicalPlus (A.coeff i j) (v j)) (List.finRange d)
    (List.mem_finRange i)

/-! ## Tropical matrix interpretations -/

/-- A tropical matrix interpretation of a step-duplicating schema: every constructor acts by
tropical matrices on the argument vectors, aggregated by tropical addition with a bias vector. No
weight vector and no scalarization certificate are part of the data. -/
structure TropicalNatMatrixMeasure (S : StepDuplicatingSchema) (d : Nat) where
  eval : S.T → TropicalVec d
  base_vec : TropicalVec d
  succ_bias : TropicalVec d
  succ_mat : TropicalMatrix d
  wrap_bias : TropicalVec d
  wrap_left : TropicalMatrix d
  wrap_right : TropicalMatrix d
  recur_bias : TropicalVec d
  recur_base : TropicalMatrix d
  recur_step : TropicalMatrix d
  recur_counter : TropicalMatrix d
  eval_base : eval S.base = base_vec
  eval_succ :
    ∀ t, eval (S.succ t) = tropicalVecMin succ_bias (succ_mat.act (eval t))
  eval_wrap :
    ∀ x y,
      eval (S.wrap x y) =
        tropicalVecMin wrap_bias
          (tropicalVecMin (wrap_left.act (eval x)) (wrap_right.act (eval y)))
  eval_recur :
    ∀ b s n,
      eval (S.recur b s n) =
        tropicalVecMin recur_bias
          (tropicalVecMin (recur_base.act (eval b))
            (tropicalVecMin (recur_step.act (eval s)) (recur_counter.act (eval n))))

/-- The tropical analogue of `WrapDiagPositive`: both wrapper matrices carry a finite positive
`(i, i)` entry. -/
def TropicalWrapDiagPositive {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalNatMatrixMeasure S d) (i : Fin d) : Prop :=
  (∃ k : Nat, M.wrap_left.coeff i i = TropicalNat.fin k ∧ 1 ≤ k) ∧
    (∃ k : Nat, M.wrap_right.coeff i i = TropicalNat.fin k ∧ 1 ≤ k)

/-! ## The counterexample -/

/-- The measure realized by `tropicalEscapeMeasure`. The wrapper is capped at `0` by its bias, the
recursor is pinned at `5` by its, and the successor sits between them. -/
def tropicalEscapeWeight : FreeTerm → Nat
  | FreeTerm.base => 5
  | FreeTerm.succ t => min 5 (tropicalEscapeWeight t)
  | FreeTerm.wrap _ _ => 0
  | FreeTerm.recur b s n =>
      min 5 (min (5 + tropicalEscapeWeight b)
        (min (5 + tropicalEscapeWeight s) (5 + tropicalEscapeWeight n)))

/-- Every value of the escape weight is at most `5`, and the recursor value is exactly `5`. -/
theorem tropicalEscapeWeight_recur (b s n : FreeTerm) :
    tropicalEscapeWeight (FreeTerm.recur b s n) = 5 := by
  simp [tropicalEscapeWeight]

/-- **The compiled tropical escape.** A one-dimensional min-plus interpretation of the free syntax
whose two wrapper diagonal entries are positive. -/
def tropicalEscapeMeasure : TropicalNatMatrixMeasure freeSchema 1 where
  eval := fun t _ => TropicalNat.fin (tropicalEscapeWeight t)
  base_vec := fun _ => TropicalNat.fin 5
  succ_bias := fun _ => TropicalNat.fin 5
  succ_mat := ⟨fun _ _ => TropicalNat.fin 0⟩
  wrap_bias := fun _ => TropicalNat.fin 0
  wrap_left := ⟨fun _ _ => TropicalNat.fin 1⟩
  wrap_right := ⟨fun _ _ => TropicalNat.fin 1⟩
  recur_bias := fun _ => TropicalNat.fin 5
  recur_base := ⟨fun _ _ => TropicalNat.fin 5⟩
  recur_step := ⟨fun _ _ => TropicalNat.fin 5⟩
  recur_counter := ⟨fun _ _ => TropicalNat.fin 5⟩
  eval_base := rfl
  eval_succ := by
    intro t
    funext i
    fin_cases i
    simp [freeSchema, tropicalEscapeWeight, tropicalVecMin, tropicalMin, TropicalMatrix.act,
      tropicalPlus, List.finRange]
  eval_wrap := by
    intro x y
    funext i
    fin_cases i
    simp [freeSchema, tropicalEscapeWeight, tropicalVecMin, tropicalMin, TropicalMatrix.act,
      tropicalPlus, List.finRange]
  eval_recur := by
    intro b s n
    funext i
    fin_cases i
    simp [freeSchema, tropicalEscapeWeight, tropicalVecMin, tropicalMin, TropicalMatrix.act,
      tropicalPlus, List.finRange]

/-- The witness is not evading through a degenerate diagonal: both wrapper diagonal entries are
positive. -/
theorem tropicalEscapeMeasure_wrapDiagPositive :
    TropicalWrapDiagPositive tropicalEscapeMeasure 0 :=
  ⟨⟨1, rfl, le_refl 1⟩, ⟨1, rfl, le_refl 1⟩⟩

/-- The witness is not evading through an empty comparison: its coordinate is finite at every
term. -/
theorem tropicalEscapeMeasure_coord_finite (t : FreeTerm) :
    tropicalEscapeMeasure.eval t 0 = TropicalNat.fin (tropicalEscapeWeight t) := rfl

/-- **The certificate-free tropical barrier is false.** The witness orients the duplicating step
strictly at coordinate `0`, uniformly in the three arguments. -/
theorem tropicalEscapeMeasure_strictly_orients :
    ∀ (b s n : FreeTerm),
      TropicalLt (tropicalEscapeMeasure.eval (freeSchema.wrap s (freeSchema.recur b s n)) 0)
        (tropicalEscapeMeasure.eval (freeSchema.recur b s (freeSchema.succ n)) 0) := by
  intro b s n
  simp only [tropicalEscapeMeasure, freeSchema, TropicalLt, tropicalEscapeWeight]
  omega

/-- **KILLED.** There is no certificate-free tropical matrix barrier: the tropical analogue of
`no_natMatrix_orients_dup_step_of_tracked_strict`, with positive wrapper diagonal entries and a
finite tracked coordinate, has a compiled counterexample. -/
theorem certificate_free_tropical_barrier_false :
    ∃ (M : TropicalNatMatrixMeasure freeSchema 1),
      TropicalWrapDiagPositive M 0 ∧
        (∃ (t : FreeTerm) (a : Nat), M.eval t 0 = TropicalNat.fin a) ∧
        (∀ (b s n : FreeTerm),
          TropicalLt (M.eval (freeSchema.wrap s (freeSchema.recur b s n)) 0)
            (M.eval (freeSchema.recur b s (freeSchema.succ n)) 0)) :=
  ⟨tropicalEscapeMeasure, tropicalEscapeMeasure_wrapDiagPositive,
    ⟨FreeTerm.base, 5, rfl⟩, tropicalEscapeMeasure_strictly_orients⟩

/-- The witness carries no scalar dominance datum: its wrapper values are `0` while its recursor
values are `5`, so no weight vector makes the wrapper dominate its right argument. This is why the
certificate-carrying tropical theorems of `Meta/MatrixBarrierArcticTropical_Schema.lean` are not
contradicted. -/
theorem tropicalEscapeMeasure_no_scalar_dominance :
    ¬ ∀ (x y : FreeTerm),
        TropicalLe (tropicalEscapeMeasure.eval y 0)
          (tropicalEscapeMeasure.eval (freeSchema.wrap x y) 0) := by
  intro h
  have := h FreeTerm.base (FreeTerm.recur FreeTerm.base FreeTerm.base FreeTerm.base)
  simp [tropicalEscapeMeasure, freeSchema, TropicalLe, tropicalEscapeWeight] at this

/-! ## Exact scope of the escape -/

/-- Strict compatibility of the wrapper with the tracked coordinate, the datum needed to lift a
root orientation through arbitrary wrapper contexts. -/
structure TropicalWrapStrictAt {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalNatMatrixMeasure S d) (i : Fin d) : Prop where
  left : ∀ {x x' y : S.T}, TropicalLt (M.eval x i) (M.eval x' i) →
    TropicalLt (M.eval (S.wrap x y) i) (M.eval (S.wrap x' y) i)
  right : ∀ {x y y' : S.T}, TropicalLt (M.eval y i) (M.eval y' i) →
    TropicalLt (M.eval (S.wrap x y) i) (M.eval (S.wrap x y') i)

/-- The root escape is not strictly compatible with the left wrapper context. -/
theorem tropicalEscapeMeasure_not_wrapStrict_left :
    ¬ ∀ {x x' y : FreeTerm},
        TropicalLt (tropicalEscapeMeasure.eval x 0) (tropicalEscapeMeasure.eval x' 0) →
          TropicalLt (tropicalEscapeMeasure.eval (freeSchema.wrap x y) 0)
            (tropicalEscapeMeasure.eval (freeSchema.wrap x' y) 0) := by
  intro h
  have hbad := h (x := freeSchema.wrap FreeTerm.base FreeTerm.base)
    (x' := FreeTerm.base) (y := FreeTerm.base) (by
      simp [tropicalEscapeMeasure, freeSchema, TropicalLt, tropicalEscapeWeight])
  simp [tropicalEscapeMeasure, freeSchema, TropicalLt, tropicalEscapeWeight] at hbad

/-- The root escape is not strictly compatible with the right wrapper context. -/
theorem tropicalEscapeMeasure_not_wrapStrict_right :
    ¬ ∀ {x y y' : FreeTerm},
        TropicalLt (tropicalEscapeMeasure.eval y 0) (tropicalEscapeMeasure.eval y' 0) →
          TropicalLt (tropicalEscapeMeasure.eval (freeSchema.wrap x y) 0)
            (tropicalEscapeMeasure.eval (freeSchema.wrap x y') 0) := by
  intro h
  have hbad := h (x := FreeTerm.base)
    (y := freeSchema.wrap FreeTerm.base FreeTerm.base) (y' := FreeTerm.base) (by
      simp [tropicalEscapeMeasure, freeSchema, TropicalLt, tropicalEscapeWeight])
  simp [tropicalEscapeMeasure, freeSchema, TropicalLt, tropicalEscapeWeight] at hbad

/-- **Exact P4 verdict.** The witness refutes the certificate-free root barrier, but it is not a
context-compatible termination interpretation: both wrapper compatibility laws fail. -/
theorem tropical_root_escape_not_context_compatible :
    (∀ (b s n : FreeTerm),
      TropicalLt (tropicalEscapeMeasure.eval (freeSchema.wrap s (freeSchema.recur b s n)) 0)
        (tropicalEscapeMeasure.eval (freeSchema.recur b s (freeSchema.succ n)) 0))
      ∧ ¬ TropicalWrapStrictAt tropicalEscapeMeasure 0 := by
  refine ⟨tropicalEscapeMeasure_strictly_orients, ?_⟩
  intro h
  exact tropicalEscapeMeasure_not_wrapStrict_left h.left

/-- Root duplicating steps and their closure under the two wrapper arguments on the free schema. -/
inductive FreeDupStepCtx : FreeTerm → FreeTerm → Prop
  | root (b s n : FreeTerm) :
      FreeDupStepCtx (freeSchema.recur b s (freeSchema.succ n))
        (freeSchema.wrap s (freeSchema.recur b s n))
  | wrap_left {x x' : FreeTerm} (y : FreeTerm) :
      FreeDupStepCtx x x' → FreeDupStepCtx (freeSchema.wrap x y) (freeSchema.wrap x' y)
  | wrap_right (x : FreeTerm) {y y' : FreeTerm} :
      FreeDupStepCtx y y' → FreeDupStepCtx (freeSchema.wrap x y) (freeSchema.wrap x y')

/-- A concrete contextualized duplicating step on which the root escape has equal values. -/
theorem tropicalEscapeMeasure_contextual_equality :
    FreeDupStepCtx
        (freeSchema.wrap FreeTerm.base
          (freeSchema.recur FreeTerm.base FreeTerm.base (freeSchema.succ FreeTerm.base)))
        (freeSchema.wrap FreeTerm.base
          (freeSchema.wrap FreeTerm.base
            (freeSchema.recur FreeTerm.base FreeTerm.base FreeTerm.base)))
      ∧ tropicalEscapeMeasure.eval
          (freeSchema.wrap FreeTerm.base
            (freeSchema.recur FreeTerm.base FreeTerm.base (freeSchema.succ FreeTerm.base))) 0 =
        tropicalEscapeMeasure.eval
          (freeSchema.wrap FreeTerm.base
            (freeSchema.wrap FreeTerm.base
              (freeSchema.recur FreeTerm.base FreeTerm.base FreeTerm.base))) 0 := by
  constructor
  · exact FreeDupStepCtx.wrap_right FreeTerm.base
      (FreeDupStepCtx.root FreeTerm.base FreeTerm.base FreeTerm.base)
  · rfl

/-- **The exact kill boundary.** The compiled tropical witness orients every root duplicating
step, but it does not orient the wrapper-context closure of that relation. -/
theorem tropicalEscapeMeasure_not_context_orienter :
    ¬ ∀ {a b : FreeTerm}, FreeDupStepCtx a b →
        TropicalLt (tropicalEscapeMeasure.eval b 0) (tropicalEscapeMeasure.eval a 0) := by
  intro h
  obtain ⟨hstep, heq⟩ := tropicalEscapeMeasure_contextual_equality
  have hlt := h hstep
  rw [heq] at hlt
  simp [tropicalEscapeMeasure, freeSchema, TropicalLt, tropicalEscapeWeight] at hlt

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
