import OperatorKO7.Meta.Methods.OrientationClosure.CouplingTheorem
import Mathlib.Tactic

/-!
# Coupling at every duplication arity

The `r`-ary duplicating rule `recur b s (succ n) → wrap_r (s, …, s) (recur b s n)` emits `r` copies of
the payload beside the recursive value. A measure that retains every wrapper argument at cost `c_w`
and orients the rule has counter gain above `r · M s + c_w` (`rary_retention_forces_gain`). With a
uniform bound on the gain and unbounded payload values no such measure orients the rule, at every
arity `r ≥ 1` (`rary_barrier`). The hypothesis `r ≥ 1` is necessary: at arity `0` the rule copies no
payload and a retentive measure with bounded gain orients it (`rary_barrier_needs_positive_arity`).
Orientation is the integer law wrapper cost below counter gain, and a bounded gain with unbounded
wrapper cost excludes orientation (`rary_barrier_cell`).

At arity `1`, the schema of a binary step-duplicating schema `S` has the same orientation predicate
(`ofBinary_orients_iff`, by definition) and the same retention predicate (`ofBinary_retains_iff`),
so the barrier at arity `1` is the binary coupling barrier of P3.1
(`rary_one_barrier_iff_binary`).
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.RaryCoupling

open OperatorKO7.StepDuplicating
open OperatorKO7.Methods.OrientationClosure.CouplingTheorem

/-- A step-duplicating schema at frame arity `r`: the wrapper takes `r` frame arguments and the
recursive value. -/
structure RarySchema (r : Nat) where
  T : Type
  base : T
  succ : T → T
  wrapR : (Fin r → T) → T → T
  recur : T → T → T → T

variable {r : Nat}

/-- Orientation of the `r`-ary duplicating rule. -/
def OrientsR (S : RarySchema r) (M : S.T → Nat) : Prop :=
  ∀ b s n : S.T, M (S.wrapR (fun _ => s) (S.recur b s n)) < M (S.recur b s (S.succ n))

/-- Retention of every frame argument and of the recursive value at cost `c_w`. -/
def RetainsR (S : RarySchema r) (M : S.T → Nat) (c_w : Nat) : Prop :=
  ∀ (xs : Fin r → S.T) (y : S.T), c_w + (∑ i, M (xs i)) + M y ≤ M (S.wrapR xs y)

/-- Integer counter gain at one instance. -/
def gainR (S : RarySchema r) (M : S.T → Nat) (b s n : S.T) : Int :=
  (M (S.recur b s (S.succ n)) : Int) - (M (S.recur b s n) : Int)

/-- Integer wrapper cost at one instance. -/
def wrapCostR (S : RarySchema r) (M : S.T → Nat) (b s n : S.T) : Int :=
  (M (S.wrapR (fun _ => s) (S.recur b s n)) : Int) - (M (S.recur b s n) : Int)

/-- Orientation is the integer law: wrapper cost below counter gain. -/
theorem orientsR_iff_cost_lt_gain (S : RarySchema r) (M : S.T → Nat) :
    OrientsR S M ↔ ∀ b s n : S.T, wrapCostR S M b s n < gainR S M b s n := by
  unfold OrientsR wrapCostR gainR
  constructor
  · intro h b s n
    have := h b s n
    omega
  · intro h b s n
    have := h b s n
    omega

/-- Retaining all `r` copies forces the counter gain above `r · M s + c_w`. -/
theorem rary_retention_forces_gain (S : RarySchema r) (M : S.T → Nat) (c_w : Nat)
    (hret : RetainsR S M c_w) (hor : OrientsR S M) (b s n : S.T) :
    ((r * M s + c_w : Nat) : Int) < gainR S M b s n := by
  have h1 := hret (fun _ => s) (S.recur b s n)
  have h2 := hor b s n
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  unfold gainR
  generalize r * M s = k at h1 ⊢
  omega

/-- The coupling barrier at every positive arity. -/
theorem rary_barrier (S : RarySchema r) (hr : 1 ≤ r) (M : S.T → Nat) (c_w g : Nat)
    (hret : RetainsR S M c_w)
    (hgain : ∀ b s n : S.T, M (S.recur b s (S.succ n)) ≤ M (S.recur b s n) + g)
    (hunb : ∀ K : Nat, ∃ s : S.T, K ≤ M s) : ¬ OrientsR S M := by
  intro hor
  obtain ⟨s, hs⟩ := hunb (g + 1)
  have hc := rary_retention_forces_gain S M c_w hret hor S.base s S.base
  have hg := hgain S.base s S.base
  have hrs : M s ≤ r * M s := Nat.le_mul_of_pos_left _ hr
  unfold gainR at hc
  generalize r * M s = k at hc hrs
  omega

/-- The barrier cell at every arity: a uniformly bounded gain with unbounded wrapper cost excludes
orientation. -/
theorem rary_barrier_cell (S : RarySchema r) (M : S.T → Nat) (g : Int)
    (hgain : ∀ b s n : S.T, gainR S M b s n ≤ g)
    (hcost : ∀ K : Int, ∃ b s n : S.T, K ≤ wrapCostR S M b s n) : ¬ OrientsR S M := by
  intro hor
  obtain ⟨b, s, n, hK⟩ := hcost g
  have hlt := (orientsR_iff_cost_lt_gain S M).1 hor b s n
  have hg := hgain b s n
  omega

/-! ## Arity zero -/

/-- At arity `0`: natural numbers, recursor value `2 n`, and a wrapper adding one. -/
abbrev zeroAritySchema : RarySchema 0 where
  T := Nat
  base := 0
  succ := fun n => n + 1
  wrapR := fun _ y => y + 1
  recur := fun _ _ n => 2 * n

/-- The hypothesis `r ≥ 1` of the barrier is necessary: at arity `0` the identity measure retains
every argument at cost `0`, has gain `2`, has unbounded payload values, and orients the rule. -/
theorem rary_barrier_needs_positive_arity :
    RetainsR zeroAritySchema id 0 ∧
      (∀ b s n : zeroAritySchema.T,
        id (zeroAritySchema.recur b s (zeroAritySchema.succ n)) ≤
          id (zeroAritySchema.recur b s n) + 2) ∧
      (∀ K : Nat, ∃ s : zeroAritySchema.T, K ≤ id s) ∧
      OrientsR zeroAritySchema id := by
  refine ⟨?_, ?_, fun K => ⟨K, le_rfl⟩, ?_⟩
  · intro xs y
    simp [zeroAritySchema]
  · rintro b s (n : Nat)
    show 2 * (n + 1) ≤ 2 * n + 2
    omega
  · rintro b s (n : Nat)
    show 2 * n + 1 < 2 * (n + 1)
    omega

/-! ## Arity one recovers the binary statement -/

/-- The arity-one schema of a binary step-duplicating schema. -/
def ofBinary (S : StepDuplicatingSchema) : RarySchema 1 where
  T := S.T
  base := S.base
  succ := S.succ
  wrapR := fun xs y => S.wrap (xs 0) y
  recur := S.recur

theorem ofBinary_orients_iff (S : StepDuplicatingSchema) (M : S.T → Nat) :
    OrientsR (ofBinary S) M ↔
      ∀ b s n : S.T, M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n)) :=
  Iff.rfl

theorem ofBinary_retains_iff (S : StepDuplicatingSchema) (M : S.T → Nat) (c_w : Nat) :
    RetainsR (ofBinary S) M c_w ↔ ∀ x y : S.T, c_w + M x + M y ≤ M (S.wrap x y) := by
  constructor
  · intro h x y
    have := h (fun _ => x) y
    simpa [ofBinary] using this
  · intro h xs y
    have := h (xs 0) y
    simpa [ofBinary, Fin.sum_univ_one] using this

/-- At arity `1` the `r`-ary barrier and the binary coupling barrier of P3.1 are one statement. -/
theorem rary_one_barrier_iff_binary (S : StepDuplicatingSchema) (M : S.T → Nat) (c_w : Nat) :
    (RetainsR (ofBinary S) M c_w → ¬ OrientsR (ofBinary S) M) ↔
      ((∀ x y : S.T, c_w + M x + M y ≤ M (S.wrap x y)) →
        ¬ ∀ b s n : S.T, M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n))) := by
  rw [ofBinary_retains_iff, ofBinary_orients_iff]

/-- Both sides of `rary_one_barrier_iff_binary` hold: the arity-one barrier is derived here, and the
binary barrier is `no_orientation_of_retention_bounded_gain_unbounded_payload`. -/
theorem rary_one_barrier_and_binary (S : StepDuplicatingSchema) (M : S.T → Nat) (c_w g : Nat)
    (hgain : ∀ b s n : S.T, M (S.recur b s (S.succ n)) ≤ M (S.recur b s n) + g)
    (hunb : ∀ K : Nat, ∃ s : S.T, K ≤ M s) :
    (RetainsR (ofBinary S) M c_w → ¬ OrientsR (ofBinary S) M) ∧
      ((∀ x y : S.T, c_w + M x + M y ≤ M (S.wrap x y)) →
        ¬ ∀ b s n : S.T, M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n))) :=
  ⟨fun hret => rary_barrier (ofBinary S) le_rfl M c_w g hret hgain hunb,
    fun hret => no_orientation_of_retention_bounded_gain_unbounded_payload M c_w g hret hgain hunb⟩

end OperatorKO7.Methods.OrientationClosure.RaryCoupling
