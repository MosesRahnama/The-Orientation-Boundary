import OperatorKO7.Meta.Recursor.CanonicalExecution
import OperatorKO7.Meta.Recursor.MassProfileIdentity
import OperatorKO7.Meta.ContextClosed_SN_Full

/-!
# Weighted constructor-cost mass on the fixed-input canonical execution

This module connects `CanonicalExecution.canonicalExecution` to the constructor-cost
algebra used by the mass-profile argument.  For explicit constructor costs, the real
fixed-input execution has slope `appCost - deltaCost`, while the actual
`SelfEmbeddingStep` orbit from the same initial state has slope `deltaCost`.  The two
pointwise profiles therefore agree at every displayed stage under the sharp
calibration `appCost = 2 * deltaCost`.

The unit-cost specialization does not satisfy that calibration.  Its counter and
`app` contributions cancel, so its mass profile is constant while the `delta` orbit
grows.  The failed unit-cost equality remains recorded as an explicit non-equality
theorem.  A separate, genuine two-cycle with the same initial state and the same mass
profile remains as the generic unit-cost indistinguishability theorem.

Relation: the full contextual closure `MetaSN_KO7.StepCtxFull` for the canonical
execution; a separately declared two-cycle relation for the comparison process.
Closure: finite canonical execution stages and an infinite two-cycle orbit.
Strategy: full contextual steps generated from the KO7 root contractions; not
otherwise applicable.
Trust: kernel-checked proof terms only.
Scope: exactly the explicit weighted equations below.  Equality with the `delta`
orbit is conditional on the stated factor-two calibration; no equality is claimed
for arbitrary measures.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Recursor.CanonicalExecutionMassProfile

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem
open OperatorKO7.Meta.Recursor.CanonicalExecution
open OperatorKO7.Meta.Recursor.MassProfileIdentity

universe u

/-! ## Concrete KO7 base-duplicating system -/

/-- The kernel `Trace` recursor and its full contextual relation packaged as the
base-duplicating system consumed by `canonicalExecution`. -/
def ko7BaseSystem : BaseDuplicatingSystem where
  toStepDuplicatingSystem := {
    toStepDuplicatingSchema := {
      T := Trace
      base := void
      succ := delta
      wrap := app
      recur := recΔ
    }
    Step := MetaSN_KO7.StepCtxFull
    dup_step := by
      intro b s n
      exact MetaSN_KO7.StepCtxFull.root (OperatorKO7.Step.R_rec_succ b s n)
  }
  base_step := by
    intro b s
    exact MetaSN_KO7.StepCtxFull.root (OperatorKO7.Step.R_rec_zero b s)

/-- `app`-right context closure supplies the wrapper-closure premise used by the
canonical execution theorem. -/
theorem ko7BaseSystem_wrapContextClosed : WrapContextClosed ko7BaseSystem := by
  intro s a b h
  exact MetaSN_KO7.StepCtxFull.appR h

/-- Adjacent displayed stages are connected by the exact schema `StepStar` over
the full contextual KO7 relation. -/
theorem ko7CanonicalExecution_stage_step (b s : Trace) (k : Nat) (i : Fin k) :
    BaseDuplicatingSystem.StepStar (Sys := ko7BaseSystem)
      (canonicalExecution ko7BaseSystem b s k i.castSucc)
      (canonicalExecution ko7BaseSystem b s k i.succ) :=
  canonicalExecution_stage_step ko7BaseSystem ko7BaseSystem_wrapContextClosed b s k i

/-- Exact one-edge lift through an `app`-right wrapper chain. -/
theorem ko7BaseSystem_wrapChainContextClosed (s : Trace) (n : Nat)
    {a b : Trace} (h : MetaSN_KO7.StepCtxFull a b) :
    MetaSN_KO7.StepCtxFull
      (ko7BaseSystem.wrapChain s n a)
      (ko7BaseSystem.wrapChain s n b) := by
  induction n with
  | zero =>
      simpa [BaseDuplicatingSystem.wrapChain] using h
  | succ n ih =>
      simpa [BaseDuplicatingSystem.wrapChain] using
        MetaSN_KO7.StepCtxFull.appR ih

/-- Adjacent displayed stages are related by one exact
`MetaSN_KO7.StepCtxFull` edge, not merely by its reflexive-transitive closure. -/
theorem ko7CanonicalExecution_stage_stepCtxFull
    (b s : Trace) (k : Nat) (i : Fin k) :
    MetaSN_KO7.StepCtxFull
      (canonicalExecution ko7BaseSystem b s k i.castSucc)
      (canonicalExecution ko7BaseSystem b s k i.succ) := by
  change MetaSN_KO7.StepCtxFull
    (ko7BaseSystem.canonicalTrace b s k i.val)
    (ko7BaseSystem.canonicalTrace b s k (i.val + 1))
  unfold BaseDuplicatingSystem.canonicalTrace
  have hroot : MetaSN_KO7.StepCtxFull
      (ko7BaseSystem.recur b s (ko7BaseSystem.counter (k - i.val)))
      (ko7BaseSystem.wrap s
        (ko7BaseSystem.recur b s
          (ko7BaseSystem.counter (k - i.val - 1)))) :=
    ko7BaseSystem.canonical_dup_step b s i.isLt
  have hlift := ko7BaseSystem_wrapChainContextClosed s i.val hroot
  have hsub : k - i.val - 1 = k - (i.val + 1) := by omega
  simpa [hsub, BaseDuplicatingSystem.wrapChain_push] using hlift

/-- The relation underlying the concrete canonical execution is strongly
normalizing by the existing full contextual polynomial theorem. -/
theorem ko7BaseSystem_contextStep_stronglyNormalizing :
    WellFounded (fun a b : Trace => ko7BaseSystem.Step b a) := by
  exact MetaSN_KO7.wf_StepCtxFullRev_poly

/-! ## General weighted constructor-cost observer algebra -/

/-- A payload-blind constructor-cost algebra on the execution spine.

All four costs are explicit.  Constructors not named here are irrelevant to the
canonical execution and the `SelfEmbeddingStep` comparison orbit.
-/
structure WeightedCostExecutionAlgebra where
  mu : Trace → Nat
  voidCost : Nat
  deltaCost : Nat
  appCost : Nat
  recDeltaCost : Nat
  mu_void : mu void = voidCost
  mu_delta : ∀ t : Trace, mu (delta t) = mu t + deltaCost
  mu_app : ∀ s t : Trace, mu (app s t) = mu t + appCost
  mu_recDelta : ∀ b s u : Trace, mu (recΔ b s u) = mu u + recDeltaCost

/-- A concrete weighted algebra for every choice of the four constructor costs.
Constructors outside the execution spine inherit the mass of their final recursive
argument.
-/
def weightedExecutionMass
    (voidCost deltaCost appCost recDeltaCost : Nat) : Trace → Nat
  | void => voidCost
  | delta t =>
      weightedExecutionMass voidCost deltaCost appCost recDeltaCost t + deltaCost
  | integrate t => weightedExecutionMass voidCost deltaCost appCost recDeltaCost t
  | merge _ t => weightedExecutionMass voidCost deltaCost appCost recDeltaCost t
  | app _ t =>
      weightedExecutionMass voidCost deltaCost appCost recDeltaCost t + appCost
  | recΔ _ _ u =>
      weightedExecutionMass voidCost deltaCost appCost recDeltaCost u + recDeltaCost
  | eqW _ t => weightedExecutionMass voidCost deltaCost appCost recDeltaCost t

/-- Non-vacuity witness: arbitrary natural constructor costs induce a weighted
execution algebra. -/
def weightedExecutionAlgebra
    (voidCost deltaCost appCost recDeltaCost : Nat) :
    WeightedCostExecutionAlgebra where
  mu := weightedExecutionMass voidCost deltaCost appCost recDeltaCost
  voidCost := voidCost
  deltaCost := deltaCost
  appCost := appCost
  recDeltaCost := recDeltaCost
  mu_void := by rfl
  mu_delta := by
    intro t
    rfl
  mu_app := by
    intro s t
    rfl
  mu_recDelta := by
    intro b s u
    rfl

/-- Concrete non-vacuity witness for the sharp calibration: base cost `0`,
`delta` cost `1`, `app` cost `2`, and `recΔ` cost `1`. -/
def factorTwoCalibratedExecutionAlgebra : WeightedCostExecutionAlgebra :=
  weightedExecutionAlgebra 0 1 2 1

/-- The concrete weighted witness satisfies the sharp factor-two calibration. -/
theorem factorTwoCalibratedExecutionAlgebra_calibration :
    factorTwoCalibratedExecutionAlgebra.appCost =
      2 * factorTwoCalibratedExecutionAlgebra.deltaCost := by
  rfl

/-- Weighted counter mass is the explicit base cost plus counter depth times the
`delta` cost. -/
theorem weightedCost_counter_mass (A : WeightedCostExecutionAlgebra) (n : Nat) :
    A.mu (ko7BaseSystem.counter n) = A.voidCost + n * A.deltaCost := by
  induction n with
  | zero =>
      simpa [ko7BaseSystem] using A.mu_void
  | succ n ih =>
      change A.mu (delta (ko7BaseSystem.counter n)) =
        A.voidCost + (n + 1) * A.deltaCost
      rw [A.mu_delta, ih, Nat.succ_mul]
      omega

/-- A wrapper chain contributes exactly its length times the explicit `app`
cost. -/
theorem weightedCost_wrapChain_mass (A : WeightedCostExecutionAlgebra)
    (s t : Trace) (n : Nat) :
    A.mu (ko7BaseSystem.wrapChain s n t) = A.mu t + n * A.appCost := by
  induction n with
  | zero => simp
  | succ n ih =>
      change A.mu (app s (ko7BaseSystem.wrapChain s n t)) =
        A.mu t + (n + 1) * A.appCost
      rw [A.mu_app, ih, Nat.succ_mul]
      omega

/-- Exact weighted constructor-cost algebra for every displayed stage of the real
fixed-input execution. -/
theorem weightedCost_canonicalExecution_mass
    (A : WeightedCostExecutionAlgebra)
    (b s : Trace) (k : Nat) (i : Fin (k + 1)) :
    A.mu (canonicalExecution ko7BaseSystem b s k i) =
      A.voidCost + (k - i.val) * A.deltaCost + A.recDeltaCost +
        i.val * A.appCost := by
  change A.mu (ko7BaseSystem.wrapChain s i.val
    (recΔ b s (ko7BaseSystem.counter (k - i.val)))) = _
  rw [weightedCost_wrapChain_mass, A.mu_recDelta, weightedCost_counter_mass]

/-- The mass of the actual self-embedding orbit under an arbitrary explicit
`delta` cost. -/
theorem weightedCost_selfEmbeddingOrbit_mass
    (A : WeightedCostExecutionAlgebra) (t : Trace) (n : Nat) :
    A.mu (selfEmbeddingOrbit t n) = A.mu t + n * A.deltaCost := by
  induction n with
  | zero => simp [selfEmbeddingOrbit]
  | succ n ih =>
      change A.mu (delta (selfEmbeddingOrbit t n)) =
        A.mu t + (n + 1) * A.deltaCost
      rw [A.mu_delta, ih, Nat.succ_mul]
      omega

/-! ## Uniform-cost observer algebra -/

/-- A payload-blind unit-cost algebra on the execution carrier.

The `app` equation is load-bearing: the frame costs one independently of its
payload argument.  The `recΔ` equation likewise observes only the counter input.
-/
structure UniformCostExecutionAlgebra where
  mu : Trace → Nat
  mu_app : ∀ s t : Trace, mu (app s t) = mu t + 1
  mu_recDelta : ∀ b s u : Trace, mu (recΔ b s u) = mu u + 1
  mu_delta : ∀ t : Trace, mu (delta t) = mu t + 1

/-- A concrete inhabitant of the uniform-cost algebra.  Constructors outside the
execution spine are assigned the mass of their final recursive argument. -/
def uniformExecutionMass : Trace → Nat
  | void => 0
  | delta t => uniformExecutionMass t + 1
  | integrate t => uniformExecutionMass t
  | merge _ t => uniformExecutionMass t
  | app _ t => uniformExecutionMass t + 1
  | recΔ _ _ u => uniformExecutionMass u + 1
  | eqW _ t => uniformExecutionMass t

/-- Non-vacuity witness for `UniformCostExecutionAlgebra`. -/
def uniformExecutionAlgebra : UniformCostExecutionAlgebra where
  mu := uniformExecutionMass
  mu_app := by
    intro s t
    rfl
  mu_recDelta := by
    intro b s u
    rfl
  mu_delta := by
    intro t
    rfl

/-- Counter mass is the base mass plus the counter depth. -/
theorem uniformCost_counter_mass (A : UniformCostExecutionAlgebra) (n : Nat) :
    A.mu (ko7BaseSystem.counter n) = A.mu void + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change A.mu (delta (ko7BaseSystem.counter n)) = A.mu void + (n + 1)
      rw [A.mu_delta, ih]
      omega

/-- Each wrapper in the canonical frame chain contributes exactly one unit. -/
theorem uniformCost_wrapChain_mass (A : UniformCostExecutionAlgebra)
    (s t : Trace) (n : Nat) :
    A.mu (ko7BaseSystem.wrapChain s n t) = A.mu t + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change A.mu (app s (ko7BaseSystem.wrapChain s n t)) = A.mu t + (n + 1)
      rw [A.mu_app, ih]
      omega

/-! ## Exact mass profile of the real canonical execution -/

/-- The mass profile of the fixed-input canonical execution. -/
def canonicalExecutionMassProfile (A : UniformCostExecutionAlgebra)
    (b s : Trace) (k : Nat) : Fin (k + 1) → Nat :=
  fun i => A.mu (canonicalExecution ko7BaseSystem b s k i)

/--
Proves: mass on the actual fixed-input execution is affine in the displayed stage,
with slope zero and intercept `A.mu void + k + 1`.

The counter contribution `k - i` and the `i` emitted frames cancel.  This is not
the positive-slope input-family theorem for `RecursorOrbit`.
-/
theorem canonicalExecution_mass_affine (A : UniformCostExecutionAlgebra)
    (b s : Trace) (k : Nat) (i : Fin (k + 1)) :
    A.mu (canonicalExecution ko7BaseSystem b s k i) = A.mu void + k + 1 := by
  change A.mu (ko7BaseSystem.wrapChain s i.val
    (recΔ b s (ko7BaseSystem.counter (k - i.val)))) = A.mu void + k + 1
  rw [uniformCost_wrapChain_mass, A.mu_recDelta, uniformCost_counter_mass]
  have hi : i.val ≤ k := Nat.le_of_lt_succ i.isLt
  omega

/-- The complete finite mass profile is the constant affine profile. -/
theorem canonicalExecution_massProfile_eq_constant (A : UniformCostExecutionAlgebra)
    (b s : Trace) (k : Nat) :
    canonicalExecutionMassProfile A b s k = fun _ => A.mu void + k + 1 := by
  funext i
  exact canonicalExecution_mass_affine A b s k i

/-- Every observer that factors through a single stage's mass is constant along the
actual canonical execution. -/
theorem massObserver_constant_on_canonicalExecution
    {α : Sort u} (observe : Nat → α) (A : UniformCostExecutionAlgebra)
    (b s : Trace) (k : Nat) (i j : Fin (k + 1)) :
    observe (A.mu (canonicalExecution ko7BaseSystem b s k i)) =
      observe (A.mu (canonicalExecution ko7BaseSystem b s k j)) := by
  rw [canonicalExecution_mass_affine, canonicalExecution_mass_affine]

/-! ## The proposed `delta` comparison is impossible beyond the initial stage -/

/-- The finite prefix of the `delta` self-embedding orbit launched from the exact
initial state of the canonical execution. -/
def canonicalDeltaOrbit (b s : Trace) (k : Nat) : Fin (k + 1) → Trace :=
  fun i => selfEmbeddingOrbit
    (canonicalExecution ko7BaseSystem b s k (0 : Fin (k + 1))) i.val

/-- Consecutive displayed states of `canonicalDeltaOrbit` are genuine steps of
the actual `SelfEmbeddingStep` relation. -/
theorem canonicalDeltaOrbit_stage_step (b s : Trace) (k : Nat) (i : Fin k) :
    SelfEmbeddingStep
      (canonicalDeltaOrbit b s k i.castSucc)
      (canonicalDeltaOrbit b s k i.succ) := by
  simpa [canonicalDeltaOrbit] using
    (selfEmbeddingStep_orbit_succ
      (canonicalExecution ko7BaseSystem b s k (0 : Fin (k + 1))) i.val)

/-- Exact weighted mass of the actual `SelfEmbeddingStep` prefix launched from
the canonical execution's own initial state. -/
theorem weightedCost_canonicalDeltaOrbit_mass
    (A : WeightedCostExecutionAlgebra)
    (b s : Trace) (k : Nat) (i : Fin (k + 1)) :
    A.mu (canonicalDeltaOrbit b s k i) =
      A.mu (canonicalExecution ko7BaseSystem b s k (0 : Fin (k + 1))) +
        i.val * A.deltaCost := by
  simpa [canonicalDeltaOrbit] using
    (weightedCost_selfEmbeddingOrbit_mass A
      (canonicalExecution ko7BaseSystem b s k (0 : Fin (k + 1))) i.val)

/--
Proves: under the factor-two calibration `appCost = 2 * deltaCost`, the real
fixed-input canonical execution and the actual `SelfEmbeddingStep` orbit from
the same initial state have equal mass at every displayed index.

Relation: `MetaSN_KO7.StepCtxFull` on the left and `SelfEmbeddingStep` on the
right.
Closure: finite displayed prefixes indexed by `Fin (k + 1)`.
Trust: kernel-only.
-/
theorem weightedCost_canonicalExecution_mass_eq_canonicalDeltaOrbit
    (A : WeightedCostExecutionAlgebra)
    (b s : Trace) (k : Nat)
    (hcal : A.appCost = 2 * A.deltaCost)
    (i : Fin (k + 1)) :
    A.mu (canonicalExecution ko7BaseSystem b s k i) =
      A.mu (canonicalDeltaOrbit b s k i) := by
  have hi : i.val ≤ k := Nat.le_of_lt_succ i.isLt
  have hkMul :
      k * A.deltaCost =
        (k - i.val) * A.deltaCost + i.val * A.deltaCost := by
    calc
      k * A.deltaCost = ((k - i.val) + i.val) * A.deltaCost := by
        rw [Nat.sub_add_cancel hi]
      _ = (k - i.val) * A.deltaCost + i.val * A.deltaCost := by
        rw [Nat.add_mul]
  calc
    A.mu (canonicalExecution ko7BaseSystem b s k i) =
        A.voidCost + (k - i.val) * A.deltaCost + A.recDeltaCost +
          i.val * A.appCost :=
      weightedCost_canonicalExecution_mass A b s k i
    _ = A.voidCost + k * A.deltaCost + A.recDeltaCost +
          i.val * A.deltaCost := by
      rw [hcal, hkMul]
      ring
    _ = A.mu (canonicalDeltaOrbit b s k i) := by
      symm
      calc
        A.mu (canonicalDeltaOrbit b s k i) =
            A.mu (canonicalExecution ko7BaseSystem b s k
              (0 : Fin (k + 1))) + i.val * A.deltaCost :=
          weightedCost_canonicalDeltaOrbit_mass A b s k i
        _ = A.voidCost + k * A.deltaCost + A.recDeltaCost +
              i.val * A.deltaCost := by
          rw [weightedCost_canonicalExecution_mass]
          simp

/-- Equality of the complete finite weighted mass profiles under the sharp
factor-two calibration. -/
theorem weightedCost_canonicalExecution_massProfile_eq_canonicalDeltaOrbit
    (A : WeightedCostExecutionAlgebra)
    (b s : Trace) (k : Nat)
    (hcal : A.appCost = 2 * A.deltaCost) :
    (fun i : Fin (k + 1) ↦
      A.mu (canonicalExecution ko7BaseSystem b s k i)) =
    (fun i : Fin (k + 1) ↦ A.mu (canonicalDeltaOrbit b s k i)) := by
  funext i
  exact weightedCost_canonicalExecution_mass_eq_canonicalDeltaOrbit
    A b s k hcal i

/-- Every observer factoring through the complete finite weighted mass profile
returns the same value on the terminating canonical execution and the actual
self-embedding prefix under the factor-two calibration. -/
theorem weightedMassProfileObserver_cannot_separate_canonicalExecution_from_selfEmbeddingOrbit
    {α : Sort u} (A : WeightedCostExecutionAlgebra)
    (b s : Trace) (k : Nat)
    (hcal : A.appCost = 2 * A.deltaCost)
    (observe : (Fin (k + 1) → Nat) → α) :
    observe (fun i => A.mu (canonicalExecution ko7BaseSystem b s k i)) =
      observe (fun i => A.mu (canonicalDeltaOrbit b s k i)) := by
  rw [weightedCost_canonicalExecution_massProfile_eq_canonicalDeltaOrbit
    A b s k hcal]

/-- Sharpness of the factor-two calibration.  At every positive execution depth,
pointwise equality with the actual self-embedding prefix holds if and only if
`appCost = 2 * deltaCost`. -/
theorem weightedCost_canonicalExecution_massProfile_eq_canonicalDeltaOrbit_iff
    (A : WeightedCostExecutionAlgebra)
    (b s : Trace) (k : Nat) (hk : 0 < k) :
    (∀ i : Fin (k + 1),
      A.mu (canonicalExecution ko7BaseSystem b s k i) =
        A.mu (canonicalDeltaOrbit b s k i)) ↔
      A.appCost = 2 * A.deltaCost := by
  constructor
  · intro hpoint
    let i : Fin (k + 1) := ⟨1, Nat.succ_lt_succ hk⟩
    have hmass := hpoint i
    rw [weightedCost_canonicalExecution_mass,
      weightedCost_canonicalDeltaOrbit_mass,
      weightedCost_canonicalExecution_mass] at hmass
    simp [i] at hmass
    have hkOne : 1 ≤ k := hk
    have hkMul :
        k * A.deltaCost = (k - 1) * A.deltaCost + A.deltaCost := by
      calc
        k * A.deltaCost = ((k - 1) + 1) * A.deltaCost := by
          rw [Nat.sub_add_cancel hkOne]
        _ = (k - 1) * A.deltaCost + A.deltaCost := by
          simp [Nat.add_mul]
    rw [hkMul] at hmass
    omega
  · intro hcal i
    exact weightedCost_canonicalExecution_mass_eq_canonicalDeltaOrbit
      A b s k hcal i

/-- The `delta` comparison profile has positive unit slope from the shared start. -/
theorem canonicalDeltaOrbit_mass_affine (A : UniformCostExecutionAlgebra)
    (b s : Trace) (k : Nat) (i : Fin (k + 1)) :
    A.mu (canonicalDeltaOrbit b s k i) =
      A.mu (canonicalExecution ko7BaseSystem b s k (0 : Fin (k + 1))) + i.val := by
  exact selfEmbeddingOrbit_mass _ i.val A.mu A.mu_delta

/-- The two profiles agree at the shared initial state. -/
theorem canonicalExecution_mass_eq_deltaOrbit_at_zero
    (A : UniformCostExecutionAlgebra) (b s : Trace) (k : Nat) :
    A.mu (canonicalExecution ko7BaseSystem b s k (0 : Fin (k + 1))) =
      A.mu (canonicalDeltaOrbit b s k (0 : Fin (k + 1))) := by
  rfl

/--
Stop-line theorem: at every positive displayed index, the actual canonical execution
and the `delta` self-embedding orbit from the same initial state have different mass.
Thus the roadmap's proposed pointwise equality with that orbit is incompatible with
its own three unit-cost equations.
-/
theorem canonicalExecution_mass_ne_deltaOrbit_of_pos
    (A : UniformCostExecutionAlgebra) (b s : Trace) (k : Nat)
    (i : Fin (k + 1)) (hi : 0 < i.val) :
    A.mu (canonicalExecution ko7BaseSystem b s k i) ≠
      A.mu (canonicalDeltaOrbit b s k i) := by
  have hleft := canonicalExecution_mass_affine A b s k i
  have hstart := canonicalExecution_mass_affine A b s k (0 : Fin (k + 1))
  have hright := canonicalDeltaOrbit_mass_affine A b s k i
  rw [hleft, hright, hstart]
  omega

/-! ## Corrected comparison: an equal-mass genuine circular process -/

/-- Two equal-mass states: the canonical source and a `delta`-wrapped counter at
the same depth. -/
def massMatchedCircularState (b s : Trace) (k : Nat) : Bool → Trace
  | false => canonicalExecution ko7BaseSystem b s k (0 : Fin (k + 1))
  | true => delta (ko7BaseSystem.counter k)

/-- The two comparison states are syntactically distinct. -/
theorem massMatchedCircularState_false_ne_true (b s : Trace) (k : Nat) :
    massMatchedCircularState b s k false ≠
      massMatchedCircularState b s k true := by
  change recΔ b s (ko7BaseSystem.counter k) ≠
    delta (ko7BaseSystem.counter k)
  intro h
  cases h

/-- The genuine two-cycle relation on the two mass-matched states.  It is a
comparison relation, not the KO7 kernel relation and not `SelfEmbeddingStep`. -/
inductive MassMatchedCircularStep (b s : Trace) (k : Nat) : Trace → Trace → Prop
  | forward : MassMatchedCircularStep b s k
      (massMatchedCircularState b s k false)
      (massMatchedCircularState b s k true)
  | backward : MassMatchedCircularStep b s k
      (massMatchedCircularState b s k true)
      (massMatchedCircularState b s k false)

/-- The comparison relation is genuinely non-strongly-normalizing because it
contains both directions of a two-cycle. -/
theorem massMatchedCircularStep_not_stronglyNormalizing
    (b s : Trace) (k : Nat) :
    ¬ WellFounded (fun x y => MassMatchedCircularStep b s k y x) := by
  intro hwf
  have hforward :
      (fun x y => MassMatchedCircularStep b s k y x)
        (massMatchedCircularState b s k true)
        (massMatchedCircularState b s k false) :=
    MassMatchedCircularStep.forward
  have hbackward :
      (fun x y => MassMatchedCircularStep b s k y x)
        (massMatchedCircularState b s k false)
        (massMatchedCircularState b s k true) :=
    MassMatchedCircularStep.backward
  exact (hwf.asymmetric
    (massMatchedCircularState b s k true)
    (massMatchedCircularState b s k false) hforward) hbackward

/-- Alternating control bit for the infinite comparison orbit. -/
def alternateBit : Nat → Bool
  | 0 => false
  | n + 1 => !(alternateBit n)

/-- Infinite orbit through the two mass-matched circular states. -/
def massMatchedCircularOrbit (b s : Trace) (k : Nat) (n : Nat) : Trace :=
  massMatchedCircularState b s k (alternateBit n)

@[simp] theorem massMatchedCircularOrbit_zero (b s : Trace) (k : Nat) :
    massMatchedCircularOrbit b s k 0 =
      canonicalExecution ko7BaseSystem b s k (0 : Fin (k + 1)) :=
  rfl

/-- Consecutive comparison-orbit states follow the declared two-cycle relation. -/
theorem massMatchedCircularOrbit_step (b s : Trace) (k n : Nat) :
    MassMatchedCircularStep b s k
      (massMatchedCircularOrbit b s k n)
      (massMatchedCircularOrbit b s k (n + 1)) := by
  cases h : alternateBit n with
  | false =>
      simpa [massMatchedCircularOrbit, alternateBit, h] using
        (MassMatchedCircularStep.forward (b := b) (s := s) (k := k))
  | true =>
      simpa [massMatchedCircularOrbit, alternateBit, h] using
        (MassMatchedCircularStep.backward (b := b) (s := s) (k := k))

/-- Both states of the circular comparison have exactly the canonical execution's
unchanging mass. -/
theorem massMatchedCircularState_mass (A : UniformCostExecutionAlgebra)
    (b s : Trace) (k : Nat) (bit : Bool) :
    A.mu (massMatchedCircularState b s k bit) = A.mu void + k + 1 := by
  cases bit with
  | false =>
      exact canonicalExecution_mass_affine A b s k (0 : Fin (k + 1))
  | true =>
      change A.mu (delta (ko7BaseSystem.counter k)) = A.mu void + k + 1
      rw [A.mu_delta, uniformCost_counter_mass]

/-- The whole infinite comparison orbit has constant mass. -/
theorem massMatchedCircularOrbit_mass_constant (A : UniformCostExecutionAlgebra)
    (b s : Trace) (k n : Nat) :
    A.mu (massMatchedCircularOrbit b s k n) = A.mu void + k + 1 :=
  massMatchedCircularState_mass A b s k (alternateBit n)

/-- Pointwise mass identity between the real fixed-input execution and the finite
prefix of the genuine nonterminating two-cycle launched from the same state. -/
theorem canonicalExecution_mass_eq_massMatchedCircular
    (A : UniformCostExecutionAlgebra) (b s : Trace) (k : Nat)
    (i : Fin (k + 1)) :
    A.mu (canonicalExecution ko7BaseSystem b s k i) =
      A.mu (massMatchedCircularOrbit b s k i.val) := by
  rw [canonicalExecution_mass_affine, massMatchedCircularOrbit_mass_constant]

/-- Equality of the complete finite mass profiles. -/
theorem canonicalExecution_massProfile_eq_massMatchedCircular
    (A : UniformCostExecutionAlgebra) (b s : Trace) (k : Nat) :
    (fun i : Fin (k + 1) =>
      A.mu (canonicalExecution ko7BaseSystem b s k i)) =
    (fun i : Fin (k + 1) =>
      A.mu (massMatchedCircularOrbit b s k i.val)) := by
  funext i
  exact canonicalExecution_mass_eq_massMatchedCircular A b s k i

/-- Every observer factoring through the complete finite mass profile returns the
same value on the terminating canonical execution and the nonterminating comparison
orbit.  The theorem says nothing about observers of syntax, relations, or payloads. -/
theorem massProfileObserver_cannot_separate_canonicalExecution_from_massMatchedCircular
    {α : Sort u} (A : UniformCostExecutionAlgebra) (b s : Trace) (k : Nat)
    (observe : (Fin (k + 1) → Nat) → α) :
    observe (fun i => A.mu (canonicalExecution ko7BaseSystem b s k i)) =
      observe (fun i => A.mu (massMatchedCircularOrbit b s k i.val)) := by
  rw [canonicalExecution_massProfile_eq_massMatchedCircular]

end OperatorKO7.Meta.Recursor.CanonicalExecutionMassProfile
