import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Range
import Mathlib.Data.Set.Function
import Mathlib.Tactic
import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax
import OperatorKO7.Meta.HigherOrderRewriting_TypeCostBoundary
import OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
import OperatorKO7.Meta.OperationalInexpressibility.ObserverTargetCore
import OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse

/-!
# L44 timing side channel as a boundary: equal outputs, different running times

A recursor loop that returns the recursive result unchanged yields `zero` at every secret
bound, while the leftmost-outermost step count grows with that bound. Functional output
therefore does not license running time, the timing fiber has no finite capacity, and the
constant-time discipline is the refusal that keeps only numerals. This is the framework's
reading of timing attacks (Kocher 1996, ESTABLISHED, cited).

Relation: `stepLO` and `normalizeFuel`; observer `output f`; target `betaCost f`.
Closure: fuelled leftmost-outermost iteration count to a normal form.
Strategy: leftmost-outermost, not the full `Step` relation.
Trust: kernel-only; `decide` fixtures on closed terms; no axioms beyond the Lean baseline.
Scope: Gödel System T carrier; family `drain n`; fuel `f` with `c n ≤ f`; refusal on numerals.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniversalBoundary.TimingChannelBoundary

open OperatorKO7.HigherOrderRewritingSystemT
open OperatorKO7.HigherOrderRewritingTypeCostBoundary
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
open OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive

/-! ## NameGate: carrier, fuel lemmas, observer/boundary API -/

#check @natLit
#check @stepLO
#check @normalizeFuel
#check @betaCost
#check @infer
#check @normalizeFuel_mono
#check @betaCost_churchApp
#check @church_fiber_unbounded
#check @TypedBoundary
#check @TypedBoundary.verdict_not_observation_function
#check @OperationallyInexpressibleAt
#check @FactorsThrough
#check @not_factorsThrough_of_collision
#check @LicensedOn

/-! ## Drain family -/

/-- Recursor loop that returns the recursive result unchanged, discarding the predecessor. -/
def drain (n : Nat) : SysTTerm :=
  .natrec .zero (.lam .nat (.lam .nat (.var 0))) (natLit n)

private abbrev drainStep : SysTTerm := .lam .nat (.lam .nat (.var 0))

private theorem infer_natLit : ∀ n, infer [] (natLit n) = some SysTTy.nat := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [natLit, infer, ih]

private theorem infer_drainStep :
    infer [] drainStep = some (.arrow .nat (.arrow .nat .nat)) :=
  rfl

private theorem infer_natrec_eq (z s n : SysTTerm) :
    infer [] (.natrec z s n) =
      match infer [] z, infer [] s, infer [] n with
      | some A, some (.arrow .nat (.arrow A' A'')), some .nat =>
          if A = A' then if A = A'' then some A else none else none
      | _, _, _ => none :=
  rfl

/--
Proves: `infer [] (drain n) = some nat` for every `n`.
Does not prove: completeness of `infer`, or any cost fact.
Relation: `infer` (the type observer).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the drain family in the empty context.
-/
theorem drain_typed : ∀ n, infer [] (drain n) = some .nat := by
  intro n
  unfold drain
  rw [infer_natrec_eq, show infer [] SysTTerm.zero = some SysTTy.nat from rfl,
      infer_drainStep, infer_natLit n]
  rfl

/-! ## Q49: kernel-evaluated closed instances before the cost formula -/

example : normalizeFuel 200 (drain 0) = some (.zero, 1) := by decide
example : normalizeFuel 200 (drain 2) = some (.zero, 7) := by decide
example : normalizeFuel 200 (drain 5) = some (.zero, 16) := by decide

/-- Leftmost-outermost step count of `drain n`: three steps per unit plus the final `recZero`. -/
def c (n : Nat) : Nat := 3 * n + 1

example : c 0 = 1 := rfl
example : c 2 = 7 := rfl
example : c 5 = 16 := rfl

/-! ## Exact cost of drain by induction on the recursor bound -/

private theorem stepLO_beta (A : SysTTy) (b u : SysTTerm) :
    stepLO (.app (.lam A b) u) = some (subst 0 u b) :=
  rfl

private theorem stepLO_app_app (g u a : SysTTerm) :
    stepLO (.app (.app g u) a) =
      match stepLO (.app g u) with
      | some f' => some (.app f' a)
      | none =>
        match stepLO a with
        | some a' => some (.app (.app g u) a')
        | none => none :=
  rfl

private theorem stepLO_drain_zero : stepLO (drain 0) = some .zero :=
  rfl

private theorem stepLO_drain_succ (n : Nat) :
    stepLO (drain (n + 1)) =
      some (.app (.app drainStep (natLit n)) (drain n)) :=
  rfl

private theorem subst_drainStep_body (u : SysTTerm) :
    subst 0 u (.lam .nat (.var 0)) = .lam .nat (.var 0) :=
  rfl

private theorem stepLO_drain_beta1 (n : Nat) :
    stepLO (.app (.app drainStep (natLit n)) (drain n)) =
      some (.app (.lam .nat (.var 0)) (drain n)) := by
  rw [stepLO_app_app, stepLO_beta, subst_drainStep_body]

private theorem stepLO_id_beta (u : SysTTerm) :
    stepLO (.app (.lam .nat (.var 0)) u) = some u :=
  rfl

private theorem normalizeFuel_of_normal (fuel : Nat) {t : SysTTerm}
    (h : stepLO t = none) : normalizeFuel fuel t = some (t, 0) := by
  cases fuel with
  | zero =>
      unfold normalizeFuel
      rw [h]
  | succ _ =>
      unfold normalizeFuel
      rw [h]

private theorem normalizeFuel_of_step {fuel : Nat} {t t' nf : SysTTerm} {cost : Nat}
    (hstep : stepLO t = some t')
    (hnf : normalizeFuel fuel t' = some (nf, cost)) :
    normalizeFuel (fuel + 1) t = some (nf, cost + 1) := by
  unfold normalizeFuel
  simp [hstep, hnf]

private theorem stepLO_zero : stepLO SysTTerm.zero = none :=
  rfl

private theorem normalizeFuel_drain_exact :
    ∀ n, normalizeFuel (c n) (drain n) = some (.zero, c n)
  | 0 => by
      have hgo :=
        normalizeFuel_of_step stepLO_drain_zero
          (normalizeFuel_of_normal 0 stepLO_zero)
      simpa [c] using hgo
  | n + 1 => by
      have hrest := normalizeFuel_drain_exact n
      have h3 := normalizeFuel_of_step (stepLO_id_beta (drain n)) hrest
      have h2 := normalizeFuel_of_step (stepLO_drain_beta1 n) h3
      have h1 := normalizeFuel_of_step (stepLO_drain_succ n) h2
      have hc : c (n + 1) = c n + 3 := by
        unfold c
        omega
      rw [hc]
      exact h1

/--
Proves: if `c n ≤ f` then `normalizeFuel f (drain n) = some (zero, c n)`.
Does not prove: a cost for an arbitrary recursor, or normalization under full `Step`.
Relation: `normalizeFuel` iterating `stepLO`.
Closure: `c n` leftmost-outermost steps.
Strategy: leftmost-outermost.
Trust: kernel-only; closed instances `n = 0, 2, 5` at fuel 200 checked by `decide` first.
Scope: every drain bound `n` and every sufficient fuel `f`.
-/
theorem normalizeFuel_drain : ∀ n f, c n ≤ f →
    normalizeFuel f (drain n) = some (.zero, c n) := by
  intro n f hle
  exact normalizeFuel_mono (c n) f (drain n) (.zero, c n) (normalizeFuel_drain_exact n) hle

/--
Proves: if `c n ≤ f` then the normal form of `drain n` at fuel `f` is `zero`.
Does not prove: uniqueness of this normal form under full `Step`.
Relation: first projection of `normalizeFuel`.
Closure: `c n` leftmost-outermost steps.
Strategy: leftmost-outermost.
Trust: kernel-only.
Scope: every drain bound `n` and every sufficient fuel `f`.
-/
theorem output_drain : ∀ n f, c n ≤ f →
    (normalizeFuel f (drain n)).map Prod.fst = some .zero := by
  intro n f hle
  rw [normalizeFuel_drain n f hle]
  rfl

/--
Proves: if `c n ≤ f` then `betaCost f (drain n) = some (c n)`.
Does not prove: a cost for other families or for fuel below `c n`.
Relation: `betaCost` (the `stepLO`-step count extracted from `normalizeFuel`).
Closure: `c n` leftmost-outermost steps.
Strategy: leftmost-outermost.
Trust: kernel-only.
Scope: every drain bound `n` and every sufficient fuel `f`.
-/
theorem betaCost_drain : ∀ n f, c n ≤ f → betaCost f (drain n) = some (c n) := by
  intro n f hle
  unfold betaCost
  rw [normalizeFuel_drain n f hle]
  rfl

/-! ## Observer, collision, unlicensed timing -/

/-- Functional output at fuel `f`: the normal form, if normalization finishes. -/
def output (f : Nat) (t : SysTTerm) : Option SysTTerm :=
  (normalizeFuel f t).map Prod.fst

/--
Proves: distinct drain bounds collide for `output f` against `betaCost f`.
Does not prove: a collision for an arbitrary pair of terms, or for fuel below both costs.
Relation: observer-fiber equality of `output f` versus inequality of `betaCost f`.
Closure: not applicable.
Strategy: leftmost-outermost cost, at fuel `f`.
Trust: kernel-only.
Scope: every `m ≠ n` with `c m ≤ f` and `c n ≤ f`.
-/
theorem timing_collision : ∀ f m n, m ≠ n → c m ≤ f → c n ≤ f →
    OperationallyInexpressibleAt (output f) (betaCost f) (drain m) (drain n) := by
  intro f m n hne hm hn
  refine ⟨?obs, ?ver⟩
  · unfold output
    rw [output_drain m f hm, output_drain n f hn]
  · rw [betaCost_drain m f hm, betaCost_drain n f hn]
    intro heq
    have hcost : c m = c n := Option.some_injective _ heq
    have hmul : 3 * m = 3 * n := by
      unfold c at hcost
      exact Nat.add_right_cancel hcost
    exact hne (Nat.mul_left_cancel (by decide : (0 : Nat) < 3) hmul)

/--
Proves: `betaCost f` does not factor through `output f` on any pair of drain bounds that both finish.
Does not prove: the same obstruction at fuel below both costs, or for a different observer.
Relation: `FactorsThrough` on `output f` versus `betaCost f`.
Closure: not applicable.
Strategy: leftmost-outermost cost.
Trust: kernel-only.
Scope: every `m ≠ n` with `c m ≤ f` and `c n ≤ f`.
-/
theorem output_does_not_license_timing : ∀ f m n, m ≠ n → c m ≤ f → c n ≤ f →
    ¬ FactorsThrough (output f) (betaCost f) := by
  intro f m n hne hm hn
  exact not_factorsThrough_of_collision (timing_collision f m n hne hm hn)

/-! ## TypedBoundary at fuel 200 -/

private theorem output_drain_eq_zero (n f : Nat) (hle : c n ≤ f) :
    output f (drain n) = some .zero :=
  output_drain n f hle

/--
Proves: the drain pair `(drain 2, drain 5)` is a `TypedBoundary` with output observer
`output 200` and cost verdict `betaCost 200`.
Does not prove: a boundary at a different fuel, or for an arbitrary pair.
Relation: `TypedBoundary` (universal boundary primitive).
Closure: not applicable.
Strategy: leftmost-outermost cost at fuel 200.
Trust: kernel-only; uses the Q49 fixtures at 2 and 5.
Scope: states `drain 2` and `drain 5`.
-/
def timingBoundary : TypedBoundary where
  State := SysTTerm
  Obs := Option SysTTerm
  Verdict := Option Nat
  observe := output 200
  verdict := betaCost 200
  s₁ := drain 2
  s₂ := drain 5
  obs_eq := by
    have h2 : c 2 ≤ 200 := by decide
    have h5 : c 5 ≤ 200 := by decide
    rw [output_drain_eq_zero 2 200 h2, output_drain_eq_zero 5 200 h5]
  verdict_ne := by
    have h2 : c 2 ≤ 200 := by decide
    have h5 : c 5 ≤ 200 := by decide
    rw [betaCost_drain 2 200 h2, betaCost_drain 5 200 h5]
    decide

/--
Proves: `betaCost 200` is not a function of the cheap output observation `output 200`.
Does not prove: the same at every fuel, or that no licensed channel recovers the cost.
Relation: `TypedBoundary.verdict_not_observation_function` on `timingBoundary`.
Closure: not applicable.
Strategy: leftmost-outermost cost at fuel 200.
Trust: kernel-only.
Scope: all `SysTTerm` states under `output 200` and `betaCost 200`.
-/
theorem timingBoundary_obeys_law :
    ¬ ∃ decode : Option SysTTerm → Option Nat,
        ∀ s : SysTTerm, betaCost 200 s = decode (output 200 s) :=
  TypedBoundary.verdict_not_observation_function timingBoundary

/-! ## No finite capacity -/

private theorem natLit_injective : Function.Injective natLit := by
  intro m n h
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ _ => cases h
  | succ m ih =>
      cases n with
      | zero => cases h
      | succ n =>
          injection h with hnat
          exact congrArg Nat.succ (ih hnat)

private theorem drain_injective : Function.Injective drain := by
  intro m n h
  injection h with _ _ hlit
  exact natLit_injective hlit

private theorem c_le_of_lt {m k : Nat} (hm : m < k) : c m ≤ c k := by
  unfold c
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.le_of_lt hm)) 1

private theorem c_injective : Function.Injective c := by
  intro m n h
  unfold c at h
  exact Nat.mul_left_cancel (by decide : (0 : Nat) < 3) (Nat.add_right_cancel h)

/--
Proves: the `output (c k)`-fiber over `some zero` contains finite sets of every cardinality whose
`betaCost (c k)` values are pairwise distinct.
Does not prove: that the fiber equals the drain family, or a cost formula at fuel below `c k`.
Relation: `output (c k)` (normal-form observer) and `betaCost (c k)` (leftmost-outermost cost).
Closure: not applicable.
Strategy: leftmost-outermost cost at fuel `c k`.
Trust: kernel-only.
Scope: every `k : Nat`; the image `Finset.image drain (Finset.range k)`.
-/
theorem timing_fiber_unbounded :
    ∀ k, ∃ S : Finset SysTTerm,
      S.card = k ∧
      (∀ t ∈ S, output (c k) t = some .zero) ∧
      (S : Set SysTTerm).InjOn (betaCost (c k)) := by
  intro k
  refine ⟨Finset.image drain (Finset.range k), ?card, ?out, ?inj⟩
  · rw [Finset.card_image_of_injective _ drain_injective, Finset.card_range]
  · intro t ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    exact output_drain_eq_zero n (c k) (c_le_of_lt (Finset.mem_range.mp hn))
  · intro t ht u hu hcost
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
    have hm' := c_le_of_lt (Finset.mem_range.mp hm)
    have hn' := c_le_of_lt (Finset.mem_range.mp hn)
    have hmcost := betaCost_drain m (c k) hm'
    have hncost := betaCost_drain n (c k) hn'
    rw [hmcost, hncost] at hcost
    exact congrArg drain (c_injective (Option.some_injective _ hcost))

/-! ## Refusal branch: constant-time numerals -/

private theorem stepLO_natLit : ∀ n, stepLO (natLit n) = none
  | 0 => rfl
  | n + 1 => by
      unfold natLit stepLO
      rw [stepLO_natLit n]
      rfl

private theorem normalizeFuel_natLit (f n : Nat) :
    normalizeFuel f (natLit n) = some (natLit n, 0) :=
  normalizeFuel_of_normal f (stepLO_natLit n)

/--
Proves: on the family of numerals, `output f` licenses `betaCost f` at every fuel.
Does not prove: licensing on any family that still contains a recursor redex.
Relation: `LicensedOn` for `output f` versus `betaCost f`.
Closure: not applicable.
Strategy: numerals are already normal, so the count is `0` on the whole family.
Trust: kernel-only.
Scope: every fuel `f`; the retained set `{t | ∃ n, t = natLit n}`.
-/
theorem constant_time_family_licensed :
    ∀ f, LicensedOn {t | ∃ n, t = natLit n} (output f) (betaCost f) := by
  intro f t ht u hu _hobs
  obtain ⟨m, rfl⟩ := ht
  obtain ⟨n, rfl⟩ := hu
  have ht' : betaCost f (natLit m) = some 0 := by
    unfold betaCost
    rw [normalizeFuel_natLit]
    rfl
  have hu' : betaCost f (natLit n) = some 0 := by
    unfold betaCost
    rw [normalizeFuel_natLit]
    rfl
  rw [ht', hu']

/-! ## Non-vacuity: items 4 and 6 at m = 2, n = 5, k = 3 -/

/--
Proves: `drain 2` and `drain 5` collide at fuel 200.
Does not prove: a collision at a fuel below 16.
Relation: `OperationallyInexpressibleAt (output 200) (betaCost 200)`.
Closure: not applicable.
Strategy: leftmost-outermost cost at fuel 200.
Trust: kernel-only.
Scope: the pair `m = 2`, `n = 5`.
-/
theorem timing_collision_two_five :
    OperationallyInexpressibleAt (output 200) (betaCost 200) (drain 2) (drain 5) :=
  timing_collision 200 2 5 (by decide) (by decide) (by decide)

/--
Proves: `betaCost 200` does not factor through `output 200`.
Does not prove: the same obstruction at fuel below 16.
Relation: `FactorsThrough (output 200) (betaCost 200)`.
Closure: not applicable.
Strategy: apply `output_does_not_license_timing` at `m = 2`, `n = 5`.
Trust: kernel-only.
Scope: fuel 200.
-/
theorem output_does_not_license_timing_two_five :
    ¬ FactorsThrough (output 200) (betaCost 200) :=
  output_does_not_license_timing 200 2 5 (by decide) (by decide) (by decide)

/--
Proves: some three-element drain set lies in the `output (c 3)`-fiber over `zero` with pairwise
distinct costs.
Does not prove: a listing of every term in that fiber.
Relation: `timing_fiber_unbounded` at `k = 3`.
Closure: not applicable.
Strategy: instantiate the unbounded-fiber theorem.
Trust: kernel-only.
Scope: cardinality 3.
-/
theorem timing_fiber_unbounded_three :
    ∃ S : Finset SysTTerm,
      S.card = 3 ∧
      (∀ t ∈ S, output (c 3) t = some .zero) ∧
      (S : Set SysTTerm).InjOn (betaCost (c 3)) :=
  timing_fiber_unbounded 3

end OperatorKO7.Meta.UniversalBoundary.TimingChannelBoundary
