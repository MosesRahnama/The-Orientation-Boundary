import OperatorKO7.Meta.ArcticBarrier_Schema
import OperatorKO7.Meta.MatrixBarrierNatural_Schema

/-!
# Certificate-Free Arctic Matrix Barrier

`Meta/MatrixBarrierNatural_Schema.lean` shows that a natural matrix interpretation whose two
wrapper matrices carry a positive `(i, i)` entry cannot orient the duplicating step, uniformly
in the dimension and with no scalarization certificate. This module carries the same argument
over the arctic semiring, where addition is `max` and multiplication is `+`, with `bot`
absorbing under multiplication and neutral under `max`.

The mechanism is the natural-matrix one with `max` in place of `+`. The `(i, i)` entry of a
matrix lower-bounds coordinate `i` of the action, so a finite positive diagonal entry
`fin k` with `1 ≤ k` makes the wrapper shift coordinate `i` upward by at least `k`. Along the
self-nested chain `t, wrap t t, wrap (wrap t t) (wrap t t), ...` coordinate `i` therefore
grows by at least `k` per level, while an order that keeps coordinate `i` nonincreasing across
the duplicating step bounds that coordinate by a constant read off the counter matrix at
`succ base`. The two facts collide.

Main theorems:

* `no_arcticMatrix_orients_dup_step_of_tracked_nonincreasing`: any order whose strict
  comparison forces `ArcticLe` on coordinate `i` fails, once coordinate `i` is finite at some
  term.
* `no_arcticMatrix_orients_dup_step_of_tracked_strict_pumpFree`: any order whose strict
  comparison forces `ArcticLt` on coordinate `i` fails whenever the two wrapper diagonal entries
  are finite. No positivity or separately supplied finite-value premise remains.

Positivity is load-bearing only for the nonincreasing comparison. With both wrapper `(i, i)`
entries equal to `fin 0`, `constantArcticMeasure` has every value `fin 0`, so the nonstrict
comparison holds at every triple. Strict comparison supplies its own pump, and there finiteness is
the exact remaining premise: the compiled `arcticBotRightMeasure` drops it and orients the root
duplicating step.

Relation: the schema duplicating step at the root. Closure: root.
External trust: none. Mathlib only.
Named method: arctic (max-plus) matrix interpretations; the order is a parameter.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-! ## The arctic semiring operations and order -/

/-- Arctic addition: `max`, with `bot` neutral. -/
def arcticMax : ArcticNat → ArcticNat → ArcticNat
  | ArcticNat.bot, y => y
  | x, ArcticNat.bot => x
  | ArcticNat.fin a, ArcticNat.fin b => ArcticNat.fin (max a b)

/-- Arctic multiplication: `+`, with `bot` absorbing. -/
def arcticPlus : ArcticNat → ArcticNat → ArcticNat
  | ArcticNat.bot, _ => ArcticNat.bot
  | _, ArcticNat.bot => ArcticNat.bot
  | ArcticNat.fin a, ArcticNat.fin b => ArcticNat.fin (a + b)

/-- Arctic order: `bot` is least, finite values compare as naturals. -/
def ArcticLe : ArcticNat → ArcticNat → Prop
  | ArcticNat.bot, _ => True
  | ArcticNat.fin _, ArcticNat.bot => False
  | ArcticNat.fin a, ArcticNat.fin b => a ≤ b

theorem arcticLe_refl (x : ArcticNat) : ArcticLe x x := by
  cases x <;> simp [ArcticLe]

theorem arcticLe_trans {x y z : ArcticNat} (h₁ : ArcticLe x y) (h₂ : ArcticLe y z) :
    ArcticLe x z := by
  cases x <;> cases y <;> cases z <;> simp_all [ArcticLe]
  omega

/-- A finite lower bound forces the upper value to be finite and at least as large. -/
theorem arcticLe_fin_left {m : Nat} {x : ArcticNat} (h : ArcticLe (ArcticNat.fin m) x) :
    ∃ a : Nat, x = ArcticNat.fin a ∧ m ≤ a := by
  cases x with
  | bot => exact absurd h (by simp [ArcticLe])
  | fin a => exact ⟨a, rfl, h⟩

theorem arcticLe_arcticMax_left (x y : ArcticNat) : ArcticLe x (arcticMax x y) := by
  cases x <;> cases y <;> simp [ArcticLe, arcticMax]

theorem arcticLe_arcticMax_right (x y : ArcticNat) : ArcticLe y (arcticMax x y) := by
  cases x <;> cases y <;> simp [ArcticLe, arcticMax]

theorem arcticMax_le {x y z : ArcticNat} (h₁ : ArcticLe x z) (h₂ : ArcticLe y z) :
    ArcticLe (arcticMax x y) z := by
  cases x <;> cases y <;> cases z <;> simp_all [ArcticLe, arcticMax]

/-- A finite lower bound on an arctic max is a finite lower bound on one of its two sides. -/
theorem arcticLe_fin_arcticMax {m : Nat} {y z : ArcticNat}
    (h : ArcticLe (ArcticNat.fin m) (arcticMax y z)) :
    (∃ a : Nat, y = ArcticNat.fin a ∧ m ≤ a) ∨ (∃ a : Nat, z = ArcticNat.fin a ∧ m ≤ a) := by
  cases y <;> cases z <;> simp_all [ArcticLe, arcticMax]

/-! ## Arctic vectors, matrices, and the row action -/

/-- Arctic vectors of a fixed finite dimension. -/
abbrev ArcticVec (d : Nat) := Fin d → ArcticNat

/-- Coordinatewise arctic addition of vectors. -/
def arcticVecMax {d : Nat} (u v : ArcticVec d) : ArcticVec d :=
  fun i => arcticMax (u i) (v i)

/-- An arctic matrix in a fixed finite dimension. -/
structure ArcticMatrix (d : Nat) where
  coeff : Fin d → Fin d → ArcticNat

/-- Every summand of an arctic fold is bounded by the fold. -/
theorem arcticLe_foldr_of_mem {α : Type} (f : α → ArcticNat) :
    ∀ (l : List α) {a : α}, a ∈ l →
      ArcticLe (f a)
        (l.foldr (fun x acc => arcticMax (f x) acc) ArcticNat.bot)
  | [], _, hmem => absurd hmem (by simp)
  | x :: xs, a, hmem => by
      rcases List.mem_cons.1 hmem with h | h
      · subst h
        exact arcticLe_arcticMax_left _ _
      · exact arcticLe_trans (arcticLe_foldr_of_mem f xs h)
          (arcticLe_arcticMax_right _ _)

/-- The arctic matrix action: `max` over `j` of `coeff i j` times `v j`. -/
def ArcticMatrix.act {d : Nat} (A : ArcticMatrix d) (v : ArcticVec d) : ArcticVec d :=
  fun i =>
    (List.finRange d).foldr
      (fun j acc => arcticMax (arcticPlus (A.coeff i j) (v j)) acc) ArcticNat.bot

/-- The diagonal term is a lower bound for coordinate `i` of the action. -/
theorem ArcticMatrix.diag_le_act {d : Nat} (A : ArcticMatrix d) (v : ArcticVec d) (i : Fin d) :
    ArcticLe (arcticPlus (A.coeff i i) (v i)) (A.act v i) :=
  arcticLe_foldr_of_mem (fun j => arcticPlus (A.coeff i j) (v j)) (List.finRange d)
    (List.mem_finRange i)

/-- A finite positive diagonal entry shifts a finite coordinate upward by at least that
entry. -/
theorem ArcticMatrix.shift_le_act {d : Nat} (A : ArcticMatrix d) (v : ArcticVec d) (i : Fin d)
    {k a : Nat} (hA : A.coeff i i = ArcticNat.fin k) (hv : v i = ArcticNat.fin a) :
    ArcticLe (ArcticNat.fin (k + a)) (A.act v i) := by
  have h := A.diag_le_act v i
  rw [hA, hv] at h
  simpa [arcticPlus] using h

/-! ## Arctic matrix interpretations -/

/-- An arctic matrix interpretation of a step-duplicating schema: every constructor acts by
arctic matrices on the argument vectors, aggregated by arctic addition with a bias vector. No
weight vector and no scalarization certificate are part of the data. -/
structure ArcticNatMatrixMeasure (S : StepDuplicatingSchema) (d : Nat) where
  eval : S.T → ArcticVec d
  base_vec : ArcticVec d
  succ_bias : ArcticVec d
  succ_mat : ArcticMatrix d
  wrap_bias : ArcticVec d
  wrap_left : ArcticMatrix d
  wrap_right : ArcticMatrix d
  recur_bias : ArcticVec d
  recur_base : ArcticMatrix d
  recur_step : ArcticMatrix d
  recur_counter : ArcticMatrix d
  eval_base : eval S.base = base_vec
  eval_succ :
    ∀ t, eval (S.succ t) = arcticVecMax succ_bias (succ_mat.act (eval t))
  eval_wrap :
    ∀ x y,
      eval (S.wrap x y) =
        arcticVecMax wrap_bias
          (arcticVecMax (wrap_left.act (eval x)) (wrap_right.act (eval y)))
  eval_recur :
    ∀ b s n,
      eval (S.recur b s n) =
        arcticVecMax recur_bias
          (arcticVecMax (recur_base.act (eval b))
            (arcticVecMax (recur_step.act (eval s)) (recur_counter.act (eval n))))

/-- The arctic analogue of `WrapDiagPositive`: both wrapper matrices carry a finite positive
`(i, i)` entry. -/
def ArcticWrapDiagPositive {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticNatMatrixMeasure S d) (i : Fin d) : Prop :=
  (∃ k : Nat, M.wrap_left.coeff i i = ArcticNat.fin k ∧ 1 ≤ k) ∧
    (∃ k : Nat, M.wrap_right.coeff i i = ArcticNat.fin k ∧ 1 ≤ k)

/-- The wrapper dominates its left argument at coordinate `i`. -/
theorem arctic_wrap_left_lower {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticNatMatrixMeasure S d) (i : Fin d) (x y : S.T) :
    ArcticLe (arcticPlus (M.wrap_left.coeff i i) (M.eval x i)) (M.eval (S.wrap x y) i) := by
  rw [M.eval_wrap]
  exact arcticLe_trans (M.wrap_left.diag_le_act (M.eval x) i)
    (arcticLe_trans (arcticLe_arcticMax_left _ _) (arcticLe_arcticMax_right _ _))

/-- The wrapper dominates its right argument at coordinate `i`. -/
theorem arctic_wrap_right_lower {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticNatMatrixMeasure S d) (i : Fin d) (x y : S.T) :
    ArcticLe (arcticPlus (M.wrap_right.coeff i i) (M.eval y i)) (M.eval (S.wrap x y) i) := by
  rw [M.eval_wrap]
  exact arcticLe_trans (M.wrap_right.diag_le_act (M.eval y) i)
    (arcticLe_trans (arcticLe_arcticMax_right _ _) (arcticLe_arcticMax_right _ _))

/-- The recursor at the successor counter is dominated by the recursor at the plain counter
together with the counter term at `succ base`. Only the counter matrix distinguishes them. -/
theorem arctic_recur_succ_le {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticNatMatrixMeasure S d) (i : Fin d) (s : S.T) :
    ArcticLe (M.eval (S.recur S.base s (S.succ S.base)) i)
      (arcticMax (M.eval (S.recur S.base s S.base) i)
        (M.recur_counter.act (M.eval (S.succ S.base)) i)) := by
  have hY := arcticLe_arcticMax_left (M.eval (S.recur S.base s S.base) i)
      (M.recur_counter.act (M.eval (S.succ S.base)) i)
  have hD := arcticLe_arcticMax_right (M.eval (S.recur S.base s S.base) i)
      (M.recur_counter.act (M.eval (S.succ S.base)) i)
  have hbias : ArcticLe (M.recur_bias i) (M.eval (S.recur S.base s S.base) i) := by
    rw [M.eval_recur]
    exact arcticLe_arcticMax_left _ _
  have hbase :
      ArcticLe (M.recur_base.act (M.eval S.base) i) (M.eval (S.recur S.base s S.base) i) := by
    rw [M.eval_recur]
    exact arcticLe_trans (arcticLe_arcticMax_left _ _) (arcticLe_arcticMax_right _ _)
  have hstep :
      ArcticLe (M.recur_step.act (M.eval s) i) (M.eval (S.recur S.base s S.base) i) := by
    rw [M.eval_recur]
    exact arcticLe_trans (arcticLe_arcticMax_left _ _)
      (arcticLe_trans (arcticLe_arcticMax_right _ _) (arcticLe_arcticMax_right _ _))
  rw [M.eval_recur]
  refine arcticMax_le (arcticLe_trans hbias hY) (arcticMax_le (arcticLe_trans hbase hY) ?_)
  exact arcticMax_le (arcticLe_trans hstep hY) hD

/-- The self-nested wrapper chain grows by at least `k` per level in coordinate `i`. -/
theorem arctic_eval_wrapDouble_coord_ge {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticNatMatrixMeasure S d) {i : Fin d} {k : Nat}
    (hk : M.wrap_left.coeff i i = ArcticNat.fin k) (hkpos : 1 ≤ k)
    {t : S.T} {a : Nat} (ht : M.eval t i = ArcticNat.fin a) (m : Nat) :
    ArcticLe (ArcticNat.fin (a + m)) (M.eval (wrapDouble S t m) i) := by
  induction m with
  | zero => simpa [wrapDouble_zero, ht] using arcticLe_refl (ArcticNat.fin a)
  | succ m ih =>
      obtain ⟨c, hc, hac⟩ := arcticLe_fin_left ih
      have hstep := M.wrap_left.shift_le_act (M.eval (wrapDouble S t m)) i hk hc
      have hlow := arctic_wrap_left_lower M i (wrapDouble S t m) (wrapDouble S t m)
      rw [hk, hc] at hlow
      simp only [arcticPlus] at hlow
      rw [wrapDouble_succ]
      exact arcticLe_trans (by simpa [ArcticLe] using (by omega : a + (m + 1) ≤ k + c)) hlow

/-! ## The barrier -/

/-- **Arctic matrix barrier, nonincreasing form.** Any order whose strict comparison forces
coordinate `i` to be arctic-nonincreasing fails to orient the duplicating step, provided both
wrapper matrices carry a finite positive `(i, i)` entry and coordinate `i` is finite at some
term. -/
theorem no_arcticMatrix_orients_dup_step_of_tracked_nonincreasing
    {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticNatMatrixMeasure S d) {i : Fin d} (hi : ArcticWrapDiagPositive M i)
    {R : ArcticVec d → ArcticVec d → Prop}
    (hR : ∀ {u v : ArcticVec d}, R u v → ArcticLe (u i) (v i))
    (hfin : ∃ (t : S.T) (a : Nat), M.eval t i = ArcticNat.fin a) :
    ¬ (∀ (b s n : S.T),
      R (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  obtain ⟨⟨kl, hkl, hklpos⟩, ⟨kr, hkr, hkrpos⟩⟩ := hi
  obtain ⟨t, a, ht⟩ := hfin
  set D : ArcticNat := M.recur_counter.act (M.eval (S.succ S.base)) i with hD
  -- every term whose coordinate `i` is finite is bounded by `D`
  have key : ∀ (s : S.T) (x : Nat), M.eval s i = ArcticNat.fin x →
      ∃ dd : Nat, D = ArcticNat.fin dd ∧ x ≤ dd := by
    intro s x hx
    have hstep : ArcticLe (M.eval (S.wrap s (S.recur S.base s S.base)) i)
        (M.eval (S.recur S.base s (S.succ S.base)) i) := hR (h S.base s S.base)
    have hupper := arctic_recur_succ_le M i s
    have hlowL := arctic_wrap_left_lower M i s (S.recur S.base s S.base)
    have hlowR := arctic_wrap_right_lower M i s (S.recur S.base s S.base)
    rw [hkl, hx] at hlowL
    simp only [arcticPlus] at hlowL
    have hchainL :
        ArcticLe (ArcticNat.fin (kl + x))
          (arcticMax (M.eval (S.recur S.base s S.base) i) D) :=
      arcticLe_trans hlowL (arcticLe_trans hstep hupper)
    rcases arcticLe_fin_arcticMax hchainL with ⟨y, hY, hxy⟩ | ⟨dd, hDd, hxd⟩
    · -- the recursor value at the plain counter is finite; the right wrapper pushes past it
      rw [hkr, hY] at hlowR
      simp only [arcticPlus] at hlowR
      have hchainR :
          ArcticLe (ArcticNat.fin (kr + y))
            (arcticMax (M.eval (S.recur S.base s S.base) i) D) :=
        arcticLe_trans hlowR (arcticLe_trans hstep hupper)
      rcases arcticLe_fin_arcticMax hchainR with ⟨y', hY', hyy⟩ | ⟨dd, hDd, hyd⟩
      · rw [hY] at hY'
        cases hY'
        omega
      · exact ⟨dd, hDd, by omega⟩
    · exact ⟨dd, hDd, by omega⟩
  obtain ⟨dd, hDfin, _⟩ := key t a ht
  have hgrow := arctic_eval_wrapDouble_coord_ge M hkl hklpos ht (dd + 1)
  obtain ⟨c, hc, hac⟩ := arcticLe_fin_left hgrow
  obtain ⟨dd', hDfin', hcle⟩ := key (wrapDouble S t (dd + 1)) c hc
  rw [hDfin] at hDfin'
  cases hDfin'
  omega

/-- **Arctic matrix barrier, strict form.** Any order whose strict comparison forces strict
arctic decrease of coordinate `i` fails to orient the duplicating step, provided only that both
wrapper matrices carry a finite positive `(i, i)` entry. Strict comparison at
`(base, base, base)` makes coordinate `i` finite there. -/
theorem no_arcticMatrix_orients_dup_step_of_tracked_strict
    {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticNatMatrixMeasure S d) {i : Fin d} (hi : ArcticWrapDiagPositive M i)
    {R : ArcticVec d → ArcticVec d → Prop}
    (hR : ∀ {u v : ArcticVec d}, R u v → ArcticLt (u i) (v i)) :
    ¬ (∀ (b s n : S.T),
      R (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hbase := hR (h S.base S.base S.base)
  have hfin : ∃ (t : S.T) (a : Nat), M.eval t i = ArcticNat.fin a := by
    cases hc : M.eval (S.recur S.base S.base (S.succ S.base)) i with
    | bot =>
        rw [hc] at hbase
        cases M.eval (S.wrap S.base (S.recur S.base S.base S.base)) i <;>
          simp [ArcticLt] at hbase
    | fin a => exact ⟨_, a, hc⟩
  refine no_arcticMatrix_orients_dup_step_of_tracked_nonincreasing M hi ?_ hfin h
  intro u v huv
  have := hR huv
  cases hu : u i <;> cases hv : v i <;> simp_all [ArcticLt, ArcticLe]
  omega

/-! ## The pump-free strict barrier

`no_arcticMatrix_orients_dup_step_of_tracked_strict` above carries the positivity premise
inherited from the natural-matrix argument, which pumps the self-nested wrapper chain. Strict
comparison supplies its own pump: the recursor chain `recur base base (succ^m base)` grows by at
least one per level from strictness alone, so positivity is not needed. What remains load-bearing
is that the two wrapper diagonal entries are finite, because `bot` absorbs under arctic
multiplication and erases the lower bound. `arcticBotRightMeasure` below is the compiled orienter
with a `bot` right wrapper diagonal. -/

/-- Both wrapper diagonal entries are finite. Strictly weaker than `ArcticWrapDiagPositive`,
which also demands each is at least `1`. -/
def ArcticWrapDiagFinite {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticNatMatrixMeasure S d) (i : Fin d) : Prop :=
  (∃ k : Nat, M.wrap_left.coeff i i = ArcticNat.fin k) ∧
    (∃ k : Nat, M.wrap_right.coeff i i = ArcticNat.fin k)

theorem arcticWrapDiagPositive_finite {S : StepDuplicatingSchema} {d : Nat}
    {M : ArcticNatMatrixMeasure S d} {i : Fin d} (h : ArcticWrapDiagPositive M i) :
    ArcticWrapDiagFinite M i := by
  obtain ⟨⟨kl, hkl, -⟩, ⟨kr, hkr, -⟩⟩ := h
  exact ⟨⟨kl, hkl⟩, ⟨kr, hkr⟩⟩

/-- Strict arctic comparison forces both sides finite. -/
theorem arcticLt_fin {x y : ArcticNat} (h : ArcticLt x y) :
    ∃ a b : Nat, x = ArcticNat.fin a ∧ y = ArcticNat.fin b ∧ a < b := by
  cases x <;> cases y <;> simp_all [ArcticLt]

/-- **Every coordinate is bounded by the counter constant.** With both wrapper diagonal entries
finite and the duplicating step strictly oriented, the value of coordinate `i` at every term is
at most the finite counter constant `recur_counter.act (eval (succ base)) i`. No positivity. -/
theorem arctic_coord_le_counter_of_strict
    {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticNatMatrixMeasure S d) {i : Fin d} (hi : ArcticWrapDiagFinite M i)
    (h : ∀ (b s n : S.T),
      ArcticLt (M.eval (S.wrap s (S.recur b s n)) i) (M.eval (S.recur b s (S.succ n)) i))
    (s : S.T) {x : Nat} (hx : M.eval s i = ArcticNat.fin x) :
    ∃ dd : Nat, M.recur_counter.act (M.eval (S.succ S.base)) i = ArcticNat.fin dd ∧ x ≤ dd := by
  obtain ⟨⟨kl, hkl⟩, ⟨kr, hkr⟩⟩ := hi
  obtain ⟨w, v, hw, hv, hwv⟩ := arcticLt_fin (h S.base s S.base)
  have hupper := arctic_recur_succ_le M i s
  rw [hv] at hupper
  have hlowL := arctic_wrap_left_lower M i s (S.recur S.base s S.base)
  rw [hkl, hx, hw] at hlowL
  simp only [arcticPlus, ArcticLe] at hlowL
  have hcut :
      ArcticLe (ArcticNat.fin (kl + x + 1))
        (arcticMax (M.eval (S.recur S.base s S.base) i)
          (M.recur_counter.act (M.eval (S.succ S.base)) i)) :=
    arcticLe_trans (by simpa [ArcticLe] using (by omega : kl + x + 1 ≤ v)) hupper
  rcases arcticLe_fin_arcticMax hcut with ⟨y, hY, hxy⟩ | ⟨dd, hDd, hxd⟩
  · -- the recursor value at the plain counter is finite; strictness rules that branch out
    have hlowR := arctic_wrap_right_lower M i s (S.recur S.base s S.base)
    rw [hkr, hY, hw] at hlowR
    simp only [arcticPlus, ArcticLe] at hlowR
    have hcutR :
        ArcticLe (ArcticNat.fin (kr + y + 1))
          (arcticMax (M.eval (S.recur S.base s S.base) i)
            (M.recur_counter.act (M.eval (S.succ S.base)) i)) :=
      arcticLe_trans (by simpa [ArcticLe] using (by omega : kr + y + 1 ≤ v)) hupper
    rcases arcticLe_fin_arcticMax hcutR with ⟨y', hY', hyy⟩ | ⟨dd, hDd, hyd⟩
    · rw [hY] at hY'
      cases hY'
      omega
    · exact ⟨dd, hDd, by omega⟩
  · exact ⟨dd, hDd, by omega⟩

/-- The strictly oriented recursor chain gains at least one unit of coordinate `i` per level. -/
theorem arctic_recur_chain_ge_of_strict
    {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticNatMatrixMeasure S d) {i : Fin d} {kr : Nat}
    (hkr : M.wrap_right.coeff i i = ArcticNat.fin kr)
    (h : ∀ (b s n : S.T),
      ArcticLt (M.eval (S.wrap s (S.recur b s n)) i) (M.eval (S.recur b s (S.succ n)) i))
    {a₁ : Nat}
    (ha₁ : M.eval (S.recur S.base S.base (succIter S 1)) i = ArcticNat.fin a₁) :
    ∀ m : Nat, ∃ c : Nat,
      M.eval (S.recur S.base S.base (succIter S (m + 1))) i = ArcticNat.fin c ∧ a₁ + m ≤ c := by
  intro m
  induction m with
  | zero => exact ⟨a₁, ha₁, by omega⟩
  | succ m ih =>
      obtain ⟨c, hc, hac⟩ := ih
      obtain ⟨w, v, hw, hv, hwv⟩ := h S.base S.base (succIter S (m + 1))
        |> arcticLt_fin
      have hlowR :=
        arctic_wrap_right_lower M i S.base (S.recur S.base S.base (succIter S (m + 1)))
      rw [hkr, hc, hw] at hlowR
      simp only [arcticPlus, ArcticLe] at hlowR
      exact ⟨v, by simpa [succIter] using hv, by omega⟩

/-- **Arctic matrix barrier, strict form, pump free.** Any order whose strict comparison forces
strict arctic decrease of coordinate `i` fails to orient the duplicating step, needing only that
both wrapper diagonal entries are finite. Positivity is not used. -/
theorem no_arcticMatrix_orients_dup_step_of_tracked_strict_pumpFree
    {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticNatMatrixMeasure S d) {i : Fin d} (hi : ArcticWrapDiagFinite M i)
    {R : ArcticVec d → ArcticVec d → Prop}
    (hR : ∀ {u v : ArcticVec d}, R u v → ArcticLt (u i) (v i)) :
    ¬ (∀ (b s n : S.T),
      R (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hlt : ∀ (b s n : S.T),
      ArcticLt (M.eval (S.wrap s (S.recur b s n)) i) (M.eval (S.recur b s (S.succ n)) i) :=
    fun b s n => hR (h b s n)
  obtain ⟨kr, hkr⟩ := hi.2
  obtain ⟨w₀, a₁, -, ha₁, -⟩ := arcticLt_fin (hlt S.base S.base S.base)
  rw [show S.succ S.base = succIter S 1 from rfl] at ha₁
  obtain ⟨dd, hD, -⟩ :=
    arctic_coord_le_counter_of_strict M hi hlt (S.recur S.base S.base (succIter S 1)) ha₁
  obtain ⟨c, hc, hac⟩ := arctic_recur_chain_ge_of_strict M hkr hlt ha₁ (dd + 1)
  obtain ⟨dd', hD', hcd⟩ :=
    arctic_coord_le_counter_of_strict M hi hlt
      (S.recur S.base S.base (succIter S (dd + 2))) hc
  rw [hD] at hD'
  cases hD'
  omega

/-- **The wrapper-diagonal dichotomy.** At every coordinate, either both wrapper diagonal entries
are finite, in which case the strict barrier applies with no further premise, or one of them is
`bot`. -/
theorem arcticWrapDiagFinite_or_bot {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticNatMatrixMeasure S d) (i : Fin d) :
    ArcticWrapDiagFinite M i ∨
      M.wrap_left.coeff i i = ArcticNat.bot ∨ M.wrap_right.coeff i i = ArcticNat.bot := by
  by_cases hl : M.wrap_left.coeff i i = ArcticNat.bot
  · exact Or.inr (Or.inl hl)
  · by_cases hr : M.wrap_right.coeff i i = ArcticNat.bot
    · exact Or.inr (Or.inr hr)
    · refine Or.inl ⟨?_, ?_⟩
      · cases hl' : M.wrap_left.coeff i i with
        | bot => exact absurd hl' hl
        | fin k => exact ⟨k, rfl⟩
      · cases hr' : M.wrap_right.coeff i i with
        | bot => exact absurd hr' hr
        | fin k => exact ⟨k, rfl⟩
/-! ## Positivity is load-bearing -/

/-- Every entry `fin 0`, every value `fin 0`: the chain never moves. -/
def constantArcticMeasure (S : StepDuplicatingSchema) : ArcticNatMatrixMeasure S 1 where
  eval := fun _ _ => ArcticNat.fin 0
  base_vec := fun _ => ArcticNat.fin 0
  succ_bias := fun _ => ArcticNat.fin 0
  succ_mat := ⟨fun _ _ => ArcticNat.fin 0⟩
  wrap_bias := fun _ => ArcticNat.fin 0
  wrap_left := ⟨fun _ _ => ArcticNat.fin 0⟩
  wrap_right := ⟨fun _ _ => ArcticNat.fin 0⟩
  recur_bias := fun _ => ArcticNat.fin 0
  recur_base := ⟨fun _ _ => ArcticNat.fin 0⟩
  recur_step := ⟨fun _ _ => ArcticNat.fin 0⟩
  recur_counter := ⟨fun _ _ => ArcticNat.fin 0⟩
  eval_base := rfl
  eval_succ := by
    intro t
    funext i
    fin_cases i
    simp [arcticVecMax, arcticMax, ArcticMatrix.act, arcticPlus, List.finRange]
  eval_wrap := by
    intro x y
    funext i
    fin_cases i
    simp [arcticVecMax, arcticMax, ArcticMatrix.act, arcticPlus, List.finRange]
  eval_recur := by
    intro b s n
    funext i
    fin_cases i
    simp [arcticVecMax, arcticMax, ArcticMatrix.act, arcticPlus, List.finRange]

/-- With both wrapper diagonal entries equal to `fin 0` the nonstrict comparison holds at every
triple, so the positivity premise of the nonincreasing barrier cannot be dropped. -/
theorem constantArcticMeasure_nonstrict_orients (S : StepDuplicatingSchema) :
    ∀ (b s n : S.T),
      ArcticLe ((constantArcticMeasure S).eval (S.wrap s (S.recur b s n)) 0)
        ((constantArcticMeasure S).eval (S.recur b s (S.succ n)) 0) :=
  fun _ _ _ => arcticLe_refl _

/-- The same interpretation has a finite coordinate everywhere, so the failure is the dropped
positivity and not a missing finite value. -/
theorem constantArcticMeasure_coord_finite (S : StepDuplicatingSchema) (t : S.T) :
    (constantArcticMeasure S).eval t 0 = ArcticNat.fin 0 :=
  rfl

/-- Its wrapper diagonal entries are `fin 0`, so `ArcticWrapDiagPositive` fails at the only
coordinate. -/
theorem constantArcticMeasure_not_wrapDiagPositive (S : StepDuplicatingSchema) :
    ¬ ArcticWrapDiagPositive (constantArcticMeasure S) 0 := by
  rintro ⟨⟨k, hk, hkpos⟩, -⟩
  simp only [constantArcticMeasure] at hk
  cases hk
  omega

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
