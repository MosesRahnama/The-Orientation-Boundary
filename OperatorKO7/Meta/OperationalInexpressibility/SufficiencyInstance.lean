import OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery
import OperatorKO7.Meta.OperationalInexpressibility.TargetKernelQuotient
import OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

/-!
# Sufficiency and definability instances

A statistic of the observation is sufficient for a target when the posterior law of the target
depends on each positive-mass observation only through the statistic. Take the full observation to
be the source state itself, read through the deterministic kernel of the identity map. An observer,
used as a statistic of the full observation, is then sufficient for a target exactly when the
target is constant on the positive-prior states of each observer fiber; with a full-support prior
this is the license criterion. The Bayes risk through an observer equals the Bayes risk of the full
observation exactly when the observer is sufficient. The target-kernel quotient is sufficient and
every sufficient observer refines it, so it is the coarsest sufficient observer: the deterministic
instance of the minimal sufficient statistic (Lehmann and Scheffe 1950; Bahadur 1954 for the
general statistical notion, cited and not proved here).

In a stochastic model the two notions separate: the identity statistic of the fully noisy binary
model is sufficient, and the target is not constant on the joint support.

The definability form of the stabilizer criterion is the set-level Padoa criterion (Padoa 1901;
Beth 1953 for first-order definability, cited and not proved here): with a nonempty verdict type, a
target is a function of the observer exactly when every observer-preserving permutation leaves it
invariant. The empty-world fixture shows that the nonempty verdict type is required.

Relation: equality of posteriors on positive-mass observations; observer refinement.
Property: sufficiency, risk attainment, coarsest sufficient observer, definability.
Trust: kernel only.
Scope: finite source and observation types with rational priors (sufficiency); arbitrary types
(definability).
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.SufficiencyInstance

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel
open OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery
open OperatorKO7.Meta.OperationalInexpressibility.TargetKernel
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

universe u v w z

/-! ## Sufficient statistics -/

/-- A statistic `T` of the observation is sufficient for the target `P` when the posterior of `P`
is equal at any two positive-mass observations with equal statistic. -/
def Sufficient {X : Type u} {O : Type v} {V : Type w} {S : Type z} [Fintype X] [Fintype O]
    [DecidableEq V] (M : RationalObservationModel X O) (P : X → V) (T : O → S) : Prop :=
  ∀ o₁ o₂, observationMass M o₁ ≠ 0 → observationMass M o₂ ≠ 0 → T o₁ = T o₂ →
    posterior? M P o₁ = posterior? M P o₂

/-- The identity statistic is sufficient in every model. -/
theorem sufficient_id {X : Type u} {O : Type v} {V : Type w} [Fintype X] [Fintype O]
    [DecidableEq V] (M : RationalObservationModel X O) (P : X → V) :
    Sufficient M P (id : O → O) :=
  fun _ _ _ _ h => congrArg (posterior? M P) h

/-! ## The full observation -/

section IdentityModel

variable {X : Type u} {V : Type w} [Fintype X] (prior : X → ℚ) (h0 : ∀ x, 0 ≤ prior x)
  (h1 : ∑ x, prior x = 1)

/-- The full observation of a state has the prior mass of that state. -/
theorem observationMass_identityModel [DecidableEq X] (x : X) :
    observationMass (deterministicModel prior h0 h1 (id : X → X)) x = prior x := by
  unfold observationMass
  rw [Finset.sum_eq_single x]
  · simp [deterministicModel]
  · intro y _ hyx
    simp [deterministicModel, hyx]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- The joint law of a target with the full observation. -/
theorem joint_identityModel [DecidableEq X] [DecidableEq V] (P : X → V) (v : V) (x : X) :
    joint (deterministicModel prior h0 h1 (id : X → X)) P v x =
      if P x = v then prior x else 0 := by
  unfold joint
  rw [Finset.sum_eq_single x]
  · simp [deterministicModel]
  · intro y _ hyx
    simp [deterministicModel, hyx]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- At a positive-prior state the posterior of the target given the full observation is the
point mass at the target value. -/
theorem posterior?_identityModel [DecidableEq X] [DecidableEq V] (P : X → V) {x : X}
    (hx : prior x ≠ 0) :
    posterior? (deterministicModel prior h0 h1 (id : X → X)) P x =
      some fun v => if P x = v then 1 else 0 := by
  unfold posterior?
  rw [observationMass_identityModel prior h0 h1, if_neg hx]
  congr 1
  funext v
  rw [joint_identityModel prior h0 h1]
  split_ifs <;> simp [hx]

/-- **Sufficiency in the deterministic model.** A statistic of the full observation is sufficient
for a target exactly when the target is constant on the positive-prior states with equal
statistic. -/
theorem sufficient_identityModel_iff [DecidableEq X] [DecidableEq V] {S : Type z} (P : X → V)
    (T : X → S) :
    Sufficient (deterministicModel prior h0 h1 (id : X → X)) P T ↔
      ∀ x y, prior x ≠ 0 → prior y ≠ 0 → T x = T y → P x = P y := by
  unfold Sufficient
  simp only [observationMass_identityModel prior h0 h1]
  constructor
  · intro h x y hx hy hT
    have hpost := h x y hx hy hT
    rw [posterior?_identityModel prior h0 h1 P hx, posterior?_identityModel prior h0 h1 P hy]
      at hpost
    by_contra hne
    have hval : (if P x = P x then (1 : ℚ) else 0) = if P y = P x then 1 else 0 :=
      congrFun (Option.some.inj hpost) (P x)
    have hl : (if P x = P x then (1 : ℚ) else 0) = 1 := if_pos rfl
    have hr : (if P y = P x then (1 : ℚ) else 0) = 0 := if_neg fun h => hne h.symm
    rw [hl, hr] at hval
    exact one_ne_zero hval
  · intro h x y hx hy hT
    rw [posterior?_identityModel prior h0 h1 P hx, posterior?_identityModel prior h0 h1 P hy,
      h x y hx hy hT]

/-- With a full-support prior, sufficiency of an observer is the license criterion. -/
theorem sufficient_identityModel_iff_licensed [DecidableEq X] [DecidableEq V]
    (hpos : ∀ x, 0 < prior x) {Q : Type z} (q : X → Q) (P : X → V) :
    Sufficient (deterministicModel prior h0 h1 (id : X → X)) P q ↔ Licensed q P := by
  rw [sufficient_identityModel_iff prior h0 h1 P q]
  exact ⟨fun h x y hxy => h x y (hpos x).ne' (hpos y).ne' hxy,
    fun h x y _ _ hxy => h x y hxy⟩

/-- The full observation has zero Bayes risk for every target. -/
theorem bayesRisk_identityModel_eq_zero [DecidableEq X] [Fintype V] [DecidableEq V]
    (EV : Enumeration V) (P : X → V) :
    bayesRisk EV (deterministicModel prior h0 h1 (id : X → X)) P = 0 := by
  rw [bayesRisk_eq_zero_iff_licensedOnJointSupport]
  intro o v w hv hw
  rw [joint_identityModel prior h0 h1] at hv hw
  by_cases hPv : P o = v
  · by_cases hPw : P o = w
    · exact hPv.symm.trans hPw
    · rw [if_neg hPw] at hw
      exact absurd hw (lt_irrefl 0)
  · rw [if_neg hPv] at hv
    exact absurd hv (lt_irrefl 0)

/-- A deterministic observer has zero Bayes risk exactly when the target is constant on the
positive-prior states of each observer fiber. -/
theorem bayesRisk_deterministic_eq_zero_iff [Fintype V] [DecidableEq V] {Q : Type z} [Fintype Q]
    [DecidableEq Q] (EV : Enumeration V) (q : X → Q) (P : X → V) :
    bayesRisk EV (deterministicModel prior h0 h1 q) P = 0 ↔
      ∀ x y, prior x ≠ 0 → prior y ≠ 0 → q x = q y → P x = P y := by
  rw [bayesRisk_eq_zero_iff_licensedOnJointSupport]
  constructor
  · intro h x y hx hy hq
    have hxpos : 0 < prior x := lt_of_le_of_ne (h0 x) (Ne.symm hx)
    have hypos : 0 < prior y := lt_of_le_of_ne (h0 y) (Ne.symm hy)
    exact h (q x) (P x) (P y)
      ((deterministic_joint_pos_iff prior h0 h1 q P (P x) (q x)).2 ⟨x, hxpos, rfl, rfl⟩)
      ((deterministic_joint_pos_iff prior h0 h1 q P (P y) (q x)).2 ⟨y, hypos, rfl, hq.symm⟩)
  · intro h o v w hv hw
    obtain ⟨x, hx, rfl, hxo⟩ := (deterministic_joint_pos_iff prior h0 h1 q P v o).1 hv
    obtain ⟨y, hy, rfl, hyo⟩ := (deterministic_joint_pos_iff prior h0 h1 q P w o).1 hw
    exact h x y hx.ne' hy.ne' (hxo.trans hyo.symm)

/-- **A sufficient observer attains the risk of the full observation**, and only a sufficient
observer does: the Bayes risk through the observer equals the Bayes risk of the full observation
exactly when the observer is sufficient. -/
theorem bayesRisk_eq_fullObservation_iff_sufficient [DecidableEq X] [Fintype V] [DecidableEq V]
    {Q : Type z} [Fintype Q] [DecidableEq Q] (EV : Enumeration V) (q : X → Q) (P : X → V) :
    bayesRisk EV (deterministicModel prior h0 h1 q) P =
        bayesRisk EV (deterministicModel prior h0 h1 (id : X → X)) P ↔
      Sufficient (deterministicModel prior h0 h1 (id : X → X)) P q := by
  rw [bayesRisk_identityModel_eq_zero prior h0 h1 EV P,
    bayesRisk_deterministic_eq_zero_iff prior h0 h1 EV q P,
    sufficient_identityModel_iff prior h0 h1 P q]

/-- **The target-kernel quotient is the coarsest sufficient observer.** With a full-support prior
the quotient by equality of target values is sufficient, and every sufficient observer refines
it. -/
theorem targetKernelQuotient_coarsest_sufficientStatistic [DecidableEq X] [DecidableEq V]
    (hpos : ∀ x, 0 < prior x) (P : X → V) :
    Sufficient (deterministicModel prior h0 h1 (id : X → X)) P (targetKernelQuotientMap P) ∧
      ∀ {S : Type z} (T : X → S), Sufficient (deterministicModel prior h0 h1 (id : X → X)) P T →
        ObserverRefines T (targetKernelQuotientMap P) := by
  refine ⟨(sufficient_identityModel_iff_licensed prior h0 h1 hpos _ P).2
      (targetKernelQuotient_licenses_target P), fun T hT => ?_⟩
  exact every_licensed_observer_refines_targetKernelQuotient T P
    ((sufficient_identityModel_iff_licensed prior h0 h1 hpos T P).1 hT)

end IdentityModel

/-! ## Stochastic separation -/

/-- **Separation in a stochastic model.** In the fully noisy binary model the identity statistic is
sufficient, while the target is not constant on the joint support. -/
theorem fullyNoisyBinary_sufficient_not_licensedOnJointSupport :
    Sufficient fullyNoisyBinary (fun x : Fin 2 => x) (id : Fin 2 → Fin 2) ∧
      ¬ LicensedOnJointSupport fullyNoisyBinary (fun x : Fin 2 => x) := by
  refine ⟨sufficient_id fullyNoisyBinary _, fun h => ?_⟩
  have hzero := (bayesRisk_eq_zero_iff_licensedOnJointSupport binaryTargetEnumeration
    fullyNoisyBinary (fun x : Fin 2 => x)).2 h
  rw [fullyNoisyBinary_risk_half] at hzero
  norm_num at hzero

end OperatorKO7.Meta.OperationalInexpressibility.SufficiencyInstance

namespace OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

universe u v w

/-- **Set-level Padoa criterion.** With a nonempty verdict type, a target is a function of the
observer exactly when every observer-preserving permutation of the source leaves it invariant. -/
theorem padoa_definable_iff_stabilizer_invariant {X : Type u} {Q : Type v} {V : Type w}
    [Nonempty V] (q : X → Q) (P : X → V) :
    VerdictDeterminedBy q P ↔ ∀ σ : licenseStabilizer q, ∀ x, P (σ.1 x) = P x := by
  constructor
  · intro h
    exact (licensed_iff_stabilizer_invariant q P).1
      (fun x y hxy => (factorsThrough_of_verdictDeterminedBy q P h) hxy)
  · intro h
    exact verdictDeterminedBy_of_factorsThrough q P
      (fun {x y} hxy => (licensed_iff_stabilizer_invariant q P).2 h x y hxy)

/-- **The nonempty verdict type is required.** On the empty world with empty verdicts every
permutation leaves the target invariant, and the target is not a function of the observer. -/
theorem padoa_nonempty_verdict_is_required :
    (∀ σ : licenseStabilizer emptyWorldObserve, ∀ x,
        emptyWorldTarget (σ.1 x) = emptyWorldTarget x) ∧
      ¬ VerdictDeterminedBy emptyWorldObserve emptyWorldTarget :=
  ⟨fun _ x => x.elim, emptyWorldTarget_not_verdictDeterminedBy⟩

end OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer
