import OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery
import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore

/-!
# Blackwell order for deterministic observers

A deterministic observer turns a finite rational prior into an observation model whose kernel is
the point mass at the observed value. For two deterministic observers on a finite source, the
refinement order and the order of Bayes risks coincide: the first observer refines the second
exactly when, for every finite target and every rational prior, its minimum 0-1 Bayes risk is at
most that of the second. The forward direction composes decoders. The reverse direction takes the
second observer itself as the target and places half of the prior on each of two states that the
first observer identifies and the second separates. A single target does not suffice: two
observers can have equal risk for one target while neither refines the other.

For stochastic observation models the garbling direction holds: composing the observation kernel
with a rational Markov kernel never lowers the Bayes risk, for every target and every prior. The
converse for stochastic experiments is Blackwell's comparison theorem (Blackwell 1951, 1953;
Sherman 1951; Stein 1951), which this module cites and does not prove.

Relation: observer refinement; order of minimum Bayes risks.
Property: equivalence of the two preorders on deterministic observers; garbling monotonicity.
Trust: kernel only; the simulating decoder uses classical choice of representatives.
Scope: finite source, observation, and target types with decidable equality and explicit target
enumerations; all rational priors.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.BlackwellOrder

open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel
open OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

universe u v w z

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## Correct mass of a deterministic observer -/

omit [DecidableEq X] in
/-- The correct-classification mass of a decoder reading a deterministic observer is the prior
mass of the states it classifies correctly. -/
theorem correctMass_deterministicModel {O : Type v} {V : Type w} [Fintype O] [DecidableEq O]
    [DecidableEq V] (prior : X → ℚ) (h0 : ∀ x, 0 ≤ prior x) (h1 : ∑ x, prior x = 1)
    (q : X → O) (P : X → V) (d : O → V) :
    correctMass (deterministicModel prior h0 h1 q) P d =
      ∑ x, if P x = d (q x) then prior x else 0 := by
  unfold correctMass joint deterministicModel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (q x)]
  · simp
  · intro o _ ho
    simp [Ne.symm ho]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## Refinement implies risk dominance -/

open Classical in
/-- A decoder of the first observation that applies a decoder of the second observation to the
second observation of a representative state. Observations outside the image use the fallback. -/
noncomputable def simulatingDecoder {O₁ : Type v} {O₂ : Type w} {V : Type z}
    (q₁ : X → O₁) (q₂ : X → O₂) (d₂ : O₂ → V) (fallback : O₁ → V) : O₁ → V :=
  fun o₁ => if h : ∃ x, q₁ x = o₁ then d₂ (q₂ (Classical.choose h)) else fallback o₁

omit [DecidableEq X] in
/-- Under refinement the simulating decoder agrees with the second decoder on every state. -/
theorem simulatingDecoder_apply {O₁ : Type v} {O₂ : Type w} {V : Type z}
    {q₁ : X → O₁} {q₂ : X → O₂} (href : ObserverRefines q₁ q₂) (d₂ : O₂ → V)
    (fallback : O₁ → V) (x : X) :
    simulatingDecoder q₁ q₂ d₂ fallback (q₁ x) = d₂ (q₂ x) := by
  classical
  have h : ∃ y, q₁ y = q₁ x := ⟨x, rfl⟩
  unfold simulatingDecoder
  rw [dif_pos h]
  exact congrArg d₂ (href (Classical.choose_spec h))

omit [DecidableEq X] in
/-- **Refinement implies risk dominance.** If the first observer refines the second, then for
every finite target and every rational prior its minimum Bayes risk is at most that of the
second. -/
theorem bayesRisk_le_of_refines {O₁ : Type v} {O₂ : Type w} {V : Type z}
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂] [Fintype V] [DecidableEq V]
    (EV : Enumeration V) (prior : X → ℚ) (h0 : ∀ x, 0 ≤ prior x) (h1 : ∑ x, prior x = 1)
    {q₁ : X → O₁} {q₂ : X → O₂} (href : ObserverRefines q₁ q₂) (P : X → V) :
    bayesRisk EV (deterministicModel prior h0 h1 q₁) P ≤
      bayesRisk EV (deterministicModel prior h0 h1 q₂) P := by
  let d₂ := bayesDecoder EV (deterministicModel prior h0 h1 q₂) P
  let d₁ := simulatingDecoder q₁ q₂ d₂ (bayesDecoder EV (deterministicModel prior h0 h1 q₁) P)
  have hd : ∀ x, d₁ (q₁ x) = d₂ (q₂ x) := fun x =>
    simulatingDecoder_apply (q₁ := q₁) (q₂ := q₂) href d₂ _ x
  have hmass : correctMass (deterministicModel prior h0 h1 q₁) P d₁ =
      correctMass (deterministicModel prior h0 h1 q₂) P d₂ := by
    rw [correctMass_deterministicModel, correctMass_deterministicModel]
    apply Finset.sum_congr rfl
    intro x _
    rw [hd x]
  calc bayesRisk EV (deterministicModel prior h0 h1 q₁) P
      ≤ risk (deterministicModel prior h0 h1 q₁) P d₁ := bayesRisk_le_risk EV _ P d₁
    _ = risk (deterministicModel prior h0 h1 q₂) P d₂ := by
        unfold risk
        rw [hmass]
    _ = bayesRisk EV (deterministicModel prior h0 h1 q₂) P := rfl

/-! ## Risk dominance on the second observer implies refinement -/

/-- The two-point prior with half of the mass on each of two distinct states. -/
def halfHalfPrior (x y : X) (z : X) : ℚ :=
  if z = x then 1 / 2 else if z = y then 1 / 2 else 0

omit [Fintype X] in
theorem halfHalfPrior_nonneg (x y : X) : ∀ z, 0 ≤ halfHalfPrior x y z := by
  intro z
  unfold halfHalfPrior
  split_ifs <;> norm_num

theorem halfHalfPrior_sum_one {x y : X} (hxy : x ≠ y) : ∑ z, halfHalfPrior x y z = 1 := by
  rw [Finset.sum_eq_add x y hxy]
  · simp [halfHalfPrior, Ne.symm hxy]
    norm_num
  · intro c _ hc
    simp [halfHalfPrior, hc.1, hc.2]
  · intro h
    exact absurd (Finset.mem_univ x) h
  · intro h
    exact absurd (Finset.mem_univ y) h

/-- **Risk dominance on two-point priors implies refinement.** If, for the second observer as
target and every prior with mass one half on each of two distinct states, the Bayes risk through
the first observer is at most the Bayes risk through the second, then the first observer refines
the second. -/
theorem refines_of_bayesRisk_le_twoPoint {O₁ : Type v} {O₂ : Type w}
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (EO₂ : Enumeration O₂) (q₁ : X → O₁) (q₂ : X → O₂)
    (h : ∀ (x y : X) (hxy : x ≠ y),
      bayesRisk EO₂ (deterministicModel (halfHalfPrior x y) (halfHalfPrior_nonneg x y)
          (halfHalfPrior_sum_one hxy) q₁) q₂ ≤
        bayesRisk EO₂ (deterministicModel (halfHalfPrior x y) (halfHalfPrior_nonneg x y)
          (halfHalfPrior_sum_one hxy) q₂) q₂) :
    ObserverRefines q₁ q₂ := by
  intro x y hxy
  by_contra hne
  have hxy' : x ≠ y := fun hsame => hne (hsame ▸ rfl)
  let prior := halfHalfPrior x y
  have h0 : ∀ z, 0 ≤ prior z := halfHalfPrior_nonneg x y
  have h1 : ∑ z, prior z = 1 := halfHalfPrior_sum_one hxy'
  -- the second observer recovers its own value with risk zero
  have hzero : bayesRisk EO₂ (deterministicModel prior h0 h1 q₂) q₂ = 0 := by
    apply le_antisymm _ (bayesRisk_nonneg EO₂ _ q₂)
    calc bayesRisk EO₂ (deterministicModel prior h0 h1 q₂) q₂
        ≤ risk (deterministicModel prior h0 h1 q₂) q₂ id := bayesRisk_le_risk EO₂ _ q₂ id
      _ = 0 := by
          unfold risk
          rw [correctMass_deterministicModel]
          simp [h1]
  -- the first observer confuses the two states, so it misclassifies one of them
  have hhalf : 1 / 2 ≤ bayesRisk EO₂ (deterministicModel prior h0 h1 q₁) q₂ := by
    let d := bayesDecoder EO₂ (deterministicModel prior h0 h1 q₁) q₂
    have hsum : correctMass (deterministicModel prior h0 h1 q₁) q₂ d ≤ 1 / 2 := by
      rw [correctMass_deterministicModel]
      rw [Finset.sum_eq_add x y hxy']
      · have hdx : d (q₁ y) = d (q₁ x) := by rw [hxy]
        simp only [prior, halfHalfPrior, if_true, if_neg (Ne.symm hxy')]
        by_cases hx : q₂ x = d (q₁ x)
        · have hy : ¬ q₂ y = d (q₁ y) := by
            rw [hdx, ← hx]
            exact fun h => hne h.symm
          simp [hx, hy]
        · by_cases hy : q₂ y = d (q₁ y)
          · simp [hx, hy]
          · simp [hx, hy]
      · intro c _ hc
        simp [prior, halfHalfPrior, hc.1, hc.2]
      · intro hmem
        exact absurd (Finset.mem_univ x) hmem
      · intro hmem
        exact absurd (Finset.mem_univ y) hmem
    show 1 / 2 ≤ 1 - correctMass (deterministicModel prior h0 h1 q₁) q₂ d
    linarith
  have hle : bayesRisk EO₂ (deterministicModel prior h0 h1 q₁) q₂ ≤
      bayesRisk EO₂ (deterministicModel prior h0 h1 q₂) q₂ := h x y hxy'
  rw [hzero] at hle
  linarith

/-- **Risk dominance implies refinement.** If, for the second observer as target and every
rational prior, the Bayes risk through the first observer is at most the Bayes risk through the
second, then the first observer refines the second. The two-point priors of
`refines_of_bayesRisk_le_twoPoint` suffice. -/
theorem refines_of_bayesRisk_le_self {O₁ : Type v} {O₂ : Type w}
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (EO₂ : Enumeration O₂) (q₁ : X → O₁) (q₂ : X → O₂)
    (h : ∀ (prior : X → ℚ) (h0 : ∀ x, 0 ≤ prior x) (h1 : ∑ x, prior x = 1),
      bayesRisk EO₂ (deterministicModel prior h0 h1 q₁) q₂ ≤
        bayesRisk EO₂ (deterministicModel prior h0 h1 q₂) q₂) :
    ObserverRefines q₁ q₂ :=
  refines_of_bayesRisk_le_twoPoint EO₂ q₁ q₂ fun _ _ _ => h _ _ _

/-- **Blackwell order for deterministic observers.** The first observer refines the second
exactly when, for every finite target and every rational prior, its minimum Bayes risk is at most
that of the second. -/
theorem refines_iff_bayesRisk_le {O₁ : Type v} {O₂ : Type w}
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (EO₂ : Enumeration O₂) (q₁ : X → O₁) (q₂ : X → O₂) :
    ObserverRefines q₁ q₂ ↔
      ∀ (V : Type w) [Fintype V] [DecidableEq V] (EV : Enumeration V) (P : X → V)
        (prior : X → ℚ) (h0 : ∀ x, 0 ≤ prior x) (h1 : ∑ x, prior x = 1),
        bayesRisk EV (deterministicModel prior h0 h1 q₁) P ≤
          bayesRisk EV (deterministicModel prior h0 h1 q₂) P := by
  constructor
  · intro href V _ _ EV P prior h0 h1
    exact bayesRisk_le_of_refines EV prior h0 h1 href P
  · intro h
    exact refines_of_bayesRisk_le_self EO₂ q₁ q₂ fun prior h0 h1 => h O₂ EO₂ q₂ prior h0 h1

/-! ## One target does not suffice -/

/-- The enumeration of the one-point target type. -/
def unitTargetEnumeration : Enumeration Unit :=
  ⟨[()], List.nodup_singleton (), fun _ => List.mem_singleton.2 rfl⟩

omit [DecidableEq X] in
/-- Every deterministic observer has zero Bayes risk for the constant target. -/
theorem bayesRisk_constant_target_eq_zero {O : Type v} [Fintype O] [DecidableEq O]
    (prior : X → ℚ) (h0 : ∀ x, 0 ≤ prior x) (h1 : ∑ x, prior x = 1) (q : X → O) :
    bayesRisk unitTargetEnumeration (deterministicModel prior h0 h1 q) (fun _ => ()) = 0 := by
  apply le_antisymm _ (bayesRisk_nonneg _ _ _)
  calc bayesRisk unitTargetEnumeration (deterministicModel prior h0 h1 q) (fun _ => ())
      ≤ risk (deterministicModel prior h0 h1 q) (fun _ => ()) (fun _ => ()) :=
        bayesRisk_le_risk _ _ _ _
    _ = 0 := by
        unfold risk
        rw [correctMass_deterministicModel]
        simp [h1]

/-- **Quantifier control.** The two coordinate observers of `Bool × Bool` have equal Bayes risk
for the constant target under every prior, and the first coordinate does not refine the second. -/
theorem single_target_does_not_determine_refinement :
    (∀ (prior : Bool × Bool → ℚ) (h0 : ∀ x, 0 ≤ prior x) (h1 : ∑ x, prior x = 1),
      bayesRisk unitTargetEnumeration (deterministicModel prior h0 h1 Prod.fst) (fun _ => ()) =
        bayesRisk unitTargetEnumeration (deterministicModel prior h0 h1 Prod.snd) (fun _ => ())) ∧
      ¬ ObserverRefines (Prod.fst : Bool × Bool → Bool) Prod.snd := by
  refine ⟨fun prior h0 h1 => by
    rw [bayesRisk_constant_target_eq_zero, bayesRisk_constant_target_eq_zero], ?_⟩
  intro h
  have hbad : (false : Bool) = true := @h (false, false) (false, true) rfl
  cases hbad

/-! ## Garbling direction for stochastic observation models -/

/-- Composition of an observation model with a rational post-processing kernel. -/
def garble {O : Type v} {O₂ : Type w} [Fintype O] [Fintype O₂]
    (M : RationalObservationModel X O) (G : RationalPostProcessing O O₂) :
    RationalObservationModel X O₂ where
  prior := M.prior
  kernel x o₂ := ∑ o, M.kernel x o * G.kernel o o₂
  prior_nonneg := M.prior_nonneg
  prior_sum_one := M.prior_sum_one
  kernel_nonneg x o₂ :=
    Finset.sum_nonneg fun o _ => mul_nonneg (M.kernel_nonneg x o) (G.nonneg o o₂)
  kernel_sum_one x := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, G.sum_one, mul_one]
    exact M.kernel_sum_one x

omit [DecidableEq X] in
/-- The joint law of the garbled model is the processed joint law of the original model. -/
theorem joint_garble {O : Type v} {O₂ : Type w} {V : Type z} [Fintype O] [Fintype O₂]
    [DecidableEq V] (M : RationalObservationModel X O) (G : RationalPostProcessing O O₂)
    (P : X → V) (v : V) (o₂ : O₂) :
    joint (garble M G) P v o₂ = ∑ o, G.kernel o o₂ * joint M P v o := by
  unfold joint
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x = v
  · simp only [hx, if_true, garble, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro o _
    ring
  · simp [hx]

omit [DecidableEq X] in
/-- **Garbling cannot lower the Bayes risk.** For every target and every prior, the minimum Bayes
risk of an observation model is at most that of its composition with any rational Markov
kernel. -/
theorem bayesRisk_le_of_garbling {O : Type v} {O₂ : Type w} {V : Type z}
    [Fintype O] [DecidableEq O] [Fintype O₂] [DecidableEq O₂] [Fintype V] [DecidableEq V]
    (EV : Enumeration V) (M : RationalObservationModel X O) (G : RationalPostProcessing O O₂)
    (P : X → V) :
    bayesRisk EV M P ≤ bayesRisk EV (garble M G) P := by
  rw [bayesRisk_eq_one_sub_sum_max, bayesRisk_eq_one_sub_sum_max]
  apply sub_le_sub_left
  calc ∑ o₂, joint (garble M G) P (bayesTarget EV (garble M G) P o₂) o₂
      = ∑ o₂, ∑ o, G.kernel o o₂ * joint M P (bayesTarget EV (garble M G) P o₂) o := by
        simp_rw [joint_garble]
    _ ≤ ∑ o₂, ∑ o, G.kernel o o₂ * joint M P (bayesTarget EV M P o) o := by
        apply Finset.sum_le_sum
        intro o₂ _
        apply Finset.sum_le_sum
        intro o _
        exact mul_le_mul_of_nonneg_left (joint_le_bayesTarget EV M P o _) (G.nonneg o o₂)
    _ = ∑ o, ∑ o₂, G.kernel o o₂ * joint M P (bayesTarget EV M P o) o := Finset.sum_comm
    _ = ∑ o, joint M P (bayesTarget EV M P o) o := by
        apply Finset.sum_congr rfl
        intro o _
        rw [← Finset.sum_mul, G.sum_one, one_mul]

end OperatorKO7.Meta.OperationalInexpressibility.BlackwellOrder
