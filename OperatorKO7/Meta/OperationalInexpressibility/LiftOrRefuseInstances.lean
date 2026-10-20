import OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorRoleGate
import OperatorKO7.Meta.SafeStep_Core
import OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra

/-!
# Lift or refuse: the recursor role gate and the diagonal guard

The two boundary instances of the paper take opposite repairs.

The free recursor's value observer reads the same generator at the frame position and at the active
position of the successor output, so it does not license the role. The dependency-pair channel is a
lift: a side channel licenses the role exactly when it decodes the dependency-pair decision; the
channel uses two symbols; two is the least number any licensing lift uses; and the bit count of the
least lift is the bit the role channel spends. The maximal refusals keep one role each and refuse
half of a uniform prior.

The diagonal target of `eqW a b` is whether `a = b`. The observer that sees nothing of the pair does
not license it, and its maximal refusals are exactly the diagonal and the off-diagonal. The kernel
rule `R_eq_diff` fires on every pair; the guarded `SafeStep` rule fires exactly on the off-diagonal
refusal, and `R_eq_refl` fires only inside the diagonal refusal. The lift needs one separating bit,
and no Sigma term read through its `void` test supplies that bit; the published obstruction
`disequality_not_sigma_expressible_unconditional` follows.

Trust: kernel only.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuseInstances

open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit
open OperatorKO7.Meta.OperationalInexpressibility.Confusability
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorRoleGate
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
open OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra

universe u

/-! ## The recursor role gate: a lift -/

/-- Sums over the two roles. -/
theorem sum_role (f : Role → ℚ) : ∑ r, f r = f Role.frame + f Role.active := by
  show ∑ r ∈ ({Role.frame, Role.active} : Finset Role), f r = _
  exact Finset.sum_pair (by decide)

/-- Both roles carry the generator. -/
theorem generatorValue_apply (K : FreeBoundaryKernel) (r : Role) :
    generatorValue K r = K.generator :=
  rfl

/-- The value observer reads the same generator at both roles, and the role target tells them
apart. -/
theorem roleGate_collision (K : FreeBoundaryKernel) :
    OperationallyInexpressibleAt (generatorValue K) (id : Role → Role) Role.frame Role.active :=
  ⟨rfl, by decide⟩

/-- **The lifts are the dependency-pair decoders.** A side channel on the two roles licenses the
role through the value observer exactly when it separates the two roles, and exactly when it
decodes the dependency-pair decision. -/
theorem roleGate_lift_iff (K : FreeBoundaryKernel) {C : Type u} (c : Role → C) :
    (Licensed (augmentObserver (generatorValue K) c) (id : Role → Role) ↔
        c Role.frame ≠ c Role.active) ∧
      (Licensed (augmentObserver (generatorValue K) c) (id : Role → Role) ↔
        ∃ decode : C → Bool, ∀ r, decode (c r) = actualDPChannel K r) := by
  have hsep : Licensed (augmentObserver (generatorValue K) c) (id : Role → Role) ↔
      c Role.frame ≠ c Role.active := by
    constructor
    · exact collision_separated_by_lift (roleGate_collision K) c
    · intro hne x y hxy
      have hc : c x = c y := congrArg Prod.snd hxy
      cases x <;> cases y
      · rfl
      · exact absurd hc hne
      · exact absurd hc.symm hne
      · rfl
  exact ⟨hsep, hsep.trans (channel_decodes_iff_separates K c).symm⟩

/-- **The dependency-pair channel is a least lift.** It licenses the role through the value
observer; the fiber multiplicity is two, so no licensing lift uses fewer than two symbols; and the
least lift's bit count `⌈log₂ 2⌉ = 1` equals the bit the role channel spends. -/
theorem roleGate_dpChannel_least_lift (K : FreeBoundaryKernel) :
    Licensed (augmentObserver (generatorValue K) (actualDPChannel K)) (id : Role → Role) ∧
      fiberMultiplicity (generatorValue K) (id : Role → Role) = 2 ∧
      (∀ (k : ℕ) (s : Role → Fin k),
        Licensed (augmentObserver (generatorValue K) s) (id : Role → Role) → 2 ≤ k) ∧
      (fiberDeficit (generatorValue K) (id : Role → Role) : ℝ) = spentBits K := by
  have hmult : fiberMultiplicity (generatorValue K) (id : Role → Role) = 2 := by
    haveI : Nonempty Role := ⟨Role.frame⟩
    have hconst : generatorValue K = fun _ => K.generator := funext (generatorValue_apply K)
    rw [hconst, fiberMultiplicity_const, Finset.image_id, Finset.card_univ]
    rfl
  refine ⟨(roleGate_lift_iff K (actualDPChannel K)).1.2
      (freeRecursor_dp_channel_is_exogenous_separator K).2, hmult, ?_, ?_⟩
  · intro k s hs
    rw [← hmult]
    exact (least_lift_eq_fiberMultiplicity _ _).2 k s hs
  · have hdef : fiberDeficit (generatorValue K) (id : Role → Role) = 1 := by
      change Nat.clog 2 (fiberMultiplicity (generatorValue K) (id : Role → Role)) = 1
      rw [hmult]
      exact Nat.clog_eq_one (le_refl 2) (le_refl 2)
    rw [hdef, spentBits_eq_one]
    norm_num

/-- **The alternative repair refuses one role.** The maximal refusals of the value observer keep
exactly one role. -/
theorem roleGate_maximal_refusals (K : FreeBoundaryKernel) (S : Set Role) :
    MaximalLicensedOn S (generatorValue K) (id : Role → Role) ↔
      S = {Role.frame} ∨ S = {Role.active} := by
  haveI : Nonempty Role := ⟨Role.frame⟩
  rw [maximalLicensedOn_iff]
  constructor
  · rintro ⟨d, -, rfl⟩
    cases hd : d K.generator
    · left
      ext r
      cases r <;> simp [correctSet, generatorValue_apply, hd]
    · right
      ext r
      cases r <;> simp [correctSet, generatorValue_apply, hd]
  · rintro (rfl | rfl)
    · refine ⟨fun _ => Role.frame, fun _ => ⟨Role.frame, rfl, rfl⟩, ?_⟩
      ext r
      cases r <;> simp [correctSet]
    · refine ⟨fun _ => Role.active, fun _ => ⟨Role.active, rfl, rfl⟩, ?_⟩
      ext r
      cases r <;> simp [correctSet]

/-- **Refusal costs half of a uniform prior.** Keeping the frame role is licensed and refuses one
half, and every licensed retained set refuses at least one half. -/
theorem roleGate_least_refusal (K : FreeBoundaryKernel) :
    LicensedOn (↑({Role.frame} : Finset Role) : Set Role) (generatorValue K) (id : Role → Role) ∧
      refusedMass (fun _ : Role => (1 / 2 : ℚ)) {Role.frame} = 1 / 2 ∧
      ∀ S : Finset Role, LicensedOn (↑S : Set Role) (generatorValue K) (id : Role → Role) →
        1 / 2 ≤ refusedMass (fun _ : Role => (1 / 2 : ℚ)) S := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy _
    have hx' : x = Role.frame := by simpa using hx
    have hy' : y = Role.frame := by simpa using hy
    rw [hx', hy']
  · unfold refusedMass
    rw [sum_role]
    simp
  · intro S hS
    have h := refusedMass_ge_min_of_collision (fun _ : Role => (1 / 2 : ℚ)) (fun _ => by norm_num)
      (roleGate_collision K) hS
    simpa using h

/-- **The recursor role gate takes the lift.** The value observer collides on the two roles; the
dependency-pair channel licenses the role with the least number of symbols, whose bit count is the
spent bit; the alternative refusals keep one role and refuse half of a uniform prior. -/
theorem roleGate_lift_or_refuse (K : FreeBoundaryKernel) :
    OperationallyInexpressibleAt (generatorValue K) (id : Role → Role) Role.frame Role.active ∧
    Licensed (augmentObserver (generatorValue K) (actualDPChannel K)) (id : Role → Role) ∧
    fiberMultiplicity (generatorValue K) (id : Role → Role) = 2 ∧
    (fiberDeficit (generatorValue K) (id : Role → Role) : ℝ) = spentBits K ∧
    (∀ S : Set Role, MaximalLicensedOn S (generatorValue K) (id : Role → Role) ↔
      S = {Role.frame} ∨ S = {Role.active}) ∧
    refusedMass (fun _ : Role => (1 / 2 : ℚ)) {Role.frame} = 1 / 2 ∧
    (∀ S : Finset Role, LicensedOn (↑S : Set Role) (generatorValue K) (id : Role → Role) →
      1 / 2 ≤ refusedMass (fun _ : Role => (1 / 2 : ℚ)) S) :=
  ⟨roleGate_collision K, (roleGate_dpChannel_least_lift K).1,
    (roleGate_dpChannel_least_lift K).2.1, (roleGate_dpChannel_least_lift K).2.2.2,
    roleGate_maximal_refusals K, (roleGate_least_refusal K).2.1, (roleGate_least_refusal K).2.2⟩

/-! ## The diagonal guard: a refusal -/

section Diagonal

variable {W : Type u}

/-- The diagonal target: whether the two components agree. -/
def isDiagonal [DecidableEq W] (p : W × W) : Bool := decide (p.1 = p.2)

/-- The observer that sees nothing of a pair. -/
def pairBlind (_ : W × W) : Unit := ()

/-- **Diagonal collision.** Two distinct values give a diagonal pair and an off-diagonal pair that
`pairBlind` does not separate. -/
theorem diagonal_collision [DecidableEq W] {w₀ w₁ : W} (h : w₀ ≠ w₁) :
    OperationallyInexpressibleAt (pairBlind (W := W)) isDiagonal (w₀, w₀) (w₀, w₁) := by
  refine ⟨rfl, ?_⟩
  simp [isDiagonal, h]

/-- The correctness set of the decoder that always answers "different" is the off-diagonal. -/
theorem correctSet_different [DecidableEq W] :
    correctSet (pairBlind (W := W)) isDiagonal (fun _ => false) = {p | p.1 ≠ p.2} := by
  ext p
  simp [correctSet, isDiagonal]

/-- The correctness set of the decoder that always answers "same" is the diagonal. -/
theorem correctSet_same [DecidableEq W] :
    correctSet (pairBlind (W := W)) isDiagonal (fun _ => true) = {p | p.1 = p.2} := by
  ext p
  simp [correctSet, isDiagonal]

/-- **Maximal refusals of the diagonal target.** When `W` has two distinct values, the maximal
refusals of `pairBlind` are exactly the diagonal and the off-diagonal. -/
theorem diagonal_maximal_refusals [DecidableEq W] {w₀ w₁ : W} (h : w₀ ≠ w₁) (S : Set (W × W)) :
    MaximalLicensedOn S (pairBlind (W := W)) isDiagonal ↔
      S = {p | p.1 = p.2} ∨ S = {p | p.1 ≠ p.2} := by
  rw [maximalLicensedOn_iff]
  constructor
  · rintro ⟨d, -, rfl⟩
    cases hd : d ()
    · right
      have hfun : d = fun _ => false := funext fun u => by cases u; exact hd
      rw [hfun, correctSet_different]
    · left
      have hfun : d = fun _ => true := funext fun u => by cases u; exact hd
      rw [hfun, correctSet_same]
  · rintro (rfl | rfl)
    · exact ⟨fun _ => true, fun _ => ⟨(w₀, w₀), rfl, by simp [isDiagonal]⟩, correctSet_same.symm⟩
    · exact ⟨fun _ => false, fun _ => ⟨(w₀, w₁), rfl, by simp [isDiagonal, h]⟩,
        correctSet_different.symm⟩

/-- The diagonal target is itself a two-symbol side channel that licenses it. -/
theorem diagonal_self_lift [DecidableEq W] :
    Licensed (augmentObserver (pairBlind (W := W)) isDiagonal) isDiagonal := by
  intro p p' hpp
  exact congrArg Prod.snd hpp

/-- One side symbol never licenses the diagonal target when `W` has two distinct values. -/
theorem diagonal_no_one_symbol_lift [DecidableEq W] {w₀ w₁ : W} (h : w₀ ≠ w₁) :
    ¬ ∃ s : W × W → Fin 1, Licensed (augmentObserver (pairBlind (W := W)) s) isDiagonal := by
  rintro ⟨s, hs⟩
  exact collision_separated_by_lift (diagonal_collision h) s hs (Subsingleton.elim _ _)

end Diagonal

/-- The side channel that evaluates the Sigma term `t` at a pair and tests the value for `void`. -/
def sigmaVoidTest (t : SigmaTerm) (p : SigmaTerm × SigmaTerm) : Bool :=
  decide (evalSigma p.1 p.2 t = SigmaTerm.void)

/-- **No Sigma term supplies the lift.** For every Sigma term `t`, the side channel
`sigmaVoidTest t` does not lift `pairBlind` to a license of the diagonal target. -/
theorem no_sigmaVoidTest_lift (t : SigmaTerm) :
    ¬ Licensed (augmentObserver (pairBlind (W := SigmaTerm)) (sigmaVoidTest t)) isDiagonal := by
  intro hlic
  have key : ∀ p p' : SigmaTerm × SigmaTerm, sigmaVoidTest t p = sigmaVoidTest t p' →
      isDiagonal p = isDiagonal p' := by
    intro p p' hp
    apply hlic p p'
    simp only [augmentObserver, pairBlind, hp]
  have hdiag : isDiagonal (SigmaTerm.void, SigmaTerm.void) ≠
      isDiagonal (SigmaTerm.void, SigmaTerm.delta SigmaTerm.void) := by
    simp [isDiagonal]
  have hdiag' : isDiagonal (SigmaTerm.void, SigmaTerm.void) ≠
      isDiagonal (SigmaTerm.delta SigmaTerm.void, SigmaTerm.void) := by
    simp [isDiagonal]
  cases t with
  | void => exact hdiag (key _ _ (by simp [sigmaVoidTest, evalSigma]))
  | varA => exact hdiag (key _ _ (by simp [sigmaVoidTest, evalSigma]))
  | varB => exact hdiag' (key _ _ (by simp [sigmaVoidTest, evalSigma]))
  | delta s => exact hdiag (key _ _ (by simp [sigmaVoidTest, evalSigma]))
  | integrate s => exact hdiag (key _ _ (by simp [sigmaVoidTest, evalSigma]))
  | merge s1 s2 => exact hdiag (key _ _ (by simp [sigmaVoidTest, evalSigma]))
  | app s1 s2 => exact hdiag (key _ _ (by simp [sigmaVoidTest, evalSigma]))
  | recDelta s1 s2 s3 => exact hdiag (key _ _ (by simp [sigmaVoidTest, evalSigma]))
  | eqW s1 s2 => exact hdiag (key _ _ (by simp [sigmaVoidTest, evalSigma]))

/-- The published obstruction `disequality_not_sigma_expressible_unconditional` follows: a Sigma
term whose `void` test expressed disequality would supply the lift. -/
theorem disequality_not_sigma_expressible_of_no_lift :
    ¬ ∃ t : SigmaTerm, ∀ a b : SigmaTerm, (a ≠ b) ↔ (evalSigma a b t ≠ SigmaTerm.void) := by
  rintro ⟨t, ht⟩
  apply no_sigmaVoidTest_lift t
  have hd : ∀ p : SigmaTerm × SigmaTerm, isDiagonal p = sigmaVoidTest t p := by
    intro p
    unfold isDiagonal sigmaVoidTest
    by_cases hp : p.1 = p.2
    · have hv : evalSigma p.1 p.2 t = SigmaTerm.void := by
        by_contra hv
        exact (ht p.1 p.2).2 hv hp
      rw [decide_eq_true hp, decide_eq_true hv]
    · have hv : evalSigma p.1 p.2 t ≠ SigmaTerm.void := (ht p.1 p.2).1 hp
      rw [decide_eq_false hp, decide_eq_false hv]
  intro p p' hpp
  have hs : sigmaVoidTest t p = sigmaVoidTest t p' := congrArg Prod.snd hpp
  rw [hd p, hd p', hs]

/-- **The guarded difference rule is the off-diagonal refusal.** `SafeStep` rewrites `eqW a b` to
`integrate (merge a b)` exactly when `(a, b)` lies in the correctness set of the decoder that always
answers "different". -/
theorem safeStep_eqDiff_iff_mem_correctSet (a b : OperatorKO7.Trace) :
    MetaSN_KO7.SafeStep (OperatorKO7.Trace.eqW a b)
        (OperatorKO7.Trace.integrate (OperatorKO7.Trace.merge a b)) ↔
      (a, b) ∈ correctSet (pairBlind (W := OperatorKO7.Trace)) isDiagonal (fun _ => false) := by
  rw [correctSet_different]
  constructor
  · intro h
    cases h with
    | R_eq_diff _ _ hne => exact hne
  · intro hne
    exact MetaSN_KO7.SafeStep.R_eq_diff a b hne

/-- `SafeStep` rewrites `eqW a b` to `void` only inside the diagonal refusal. -/
theorem safeStep_eqRefl_mem_correctSet {a b : OperatorKO7.Trace}
    (h : MetaSN_KO7.SafeStep (OperatorKO7.Trace.eqW a b) OperatorKO7.Trace.void) :
    (a, b) ∈ correctSet (pairBlind (W := OperatorKO7.Trace)) isDiagonal (fun _ => true) := by
  rw [correctSet_same]
  cases h with
  | R_eq_refl _ _ => exact rfl

/-- **The diagonal guard takes the refusal.** On pairs of traces, `pairBlind` does not license the
diagonal target and no one-symbol lift repairs it; the maximal refusals are the diagonal and the
off-diagonal; the kernel rule `R_eq_diff` fires on every pair, while the `SafeStep` rule fires
exactly on the off-diagonal refusal and `R_eq_refl` only inside the diagonal refusal. On Sigma terms
the one-bit lift exists as a side channel, and no Sigma term read through its `void` test supplies
it. -/
theorem diagonalGuard_lift_or_refuse :
    OperationallyInexpressibleAt (pairBlind (W := OperatorKO7.Trace)) isDiagonal
      (OperatorKO7.Trace.void, OperatorKO7.Trace.void)
      (OperatorKO7.Trace.void, OperatorKO7.Trace.delta OperatorKO7.Trace.void) ∧
    (¬ ∃ s : OperatorKO7.Trace × OperatorKO7.Trace → Fin 1,
      Licensed (augmentObserver (pairBlind (W := OperatorKO7.Trace)) s) isDiagonal) ∧
    (∀ S : Set (OperatorKO7.Trace × OperatorKO7.Trace),
      MaximalLicensedOn S (pairBlind (W := OperatorKO7.Trace)) isDiagonal ↔
        S = {p | p.1 = p.2} ∨ S = {p | p.1 ≠ p.2}) ∧
    (∀ a b : OperatorKO7.Trace,
      OperatorKO7.Step (OperatorKO7.Trace.eqW a b)
        (OperatorKO7.Trace.integrate (OperatorKO7.Trace.merge a b))) ∧
    {p : OperatorKO7.Trace × OperatorKO7.Trace |
        MetaSN_KO7.SafeStep (OperatorKO7.Trace.eqW p.1 p.2)
          (OperatorKO7.Trace.integrate (OperatorKO7.Trace.merge p.1 p.2))} =
      correctSet (pairBlind (W := OperatorKO7.Trace)) isDiagonal (fun _ => false) ∧
    {p : OperatorKO7.Trace × OperatorKO7.Trace |
        MetaSN_KO7.SafeStep (OperatorKO7.Trace.eqW p.1 p.2) OperatorKO7.Trace.void} ⊆
      correctSet (pairBlind (W := OperatorKO7.Trace)) isDiagonal (fun _ => true) ∧
    Licensed (augmentObserver (pairBlind (W := SigmaTerm)) isDiagonal) isDiagonal ∧
    (∀ t : SigmaTerm,
      ¬ Licensed (augmentObserver (pairBlind (W := SigmaTerm)) (sigmaVoidTest t)) isDiagonal) := by
  have hne : OperatorKO7.Trace.void ≠ OperatorKO7.Trace.delta OperatorKO7.Trace.void := by
    intro h
    cases h
  refine ⟨diagonal_collision hne, diagonal_no_one_symbol_lift hne, diagonal_maximal_refusals hne,
    OperatorKO7.Step.R_eq_diff, ?_, ?_, diagonal_self_lift, no_sigmaVoidTest_lift⟩
  · ext p
    exact safeStep_eqDiff_iff_mem_correctSet p.1 p.2
  · intro p hp
    exact safeStep_eqRefl_mem_correctSet hp

end OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuseInstances
