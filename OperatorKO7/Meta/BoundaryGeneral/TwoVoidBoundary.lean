import OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw
import OperatorKO7.Meta.OperationalInexpressibility.LiftUniversalProperty
import OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer
import OperatorKO7.Meta.DistinctionBoundary.ObservationalDiagonalFork
import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
import OperatorKO7.Meta.SafeStep.SyntacticNonDerivability

set_option autoImplicit false

/-!
# The two-void boundary

The frame and active occurrences of `void` have equal value projections and distinct roles. Every map factoring through the value projection agrees on the pair, while a Boolean separator exists. The file also states swap invariance, finite-symbol licensing and decoding results. The term clause concerns `Step` at the root, in one step.

Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

open OperatorKO7 Trace

namespace OperatorKO7.Meta.BoundaryGeneral.TwoVoidBoundary

open OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance

/-! ## A pair of points: the two self-tests and the swap -/

section Pair

variable {D : Type*}

/-- The self-test of a point accepts that point. -/
theorem boolSeparator_self (p : D) : boolSeparator p p = true := by
  simp [boolSeparator]

/-- The self-test of a point rejects every other point. -/
theorem boolSeparator_of_ne {p x : D} (h : x ≠ p) : boolSeparator p x = false := by
  simp [boolSeparator, h]

/-- On a pair of distinct points, each self-test is the negation of the other. -/
theorem boolSeparator_pair_complement {p q : D} (h : p ≠ q) :
    boolSeparator p p = !boolSeparator q p ∧ boolSeparator p q = !boolSeparator q q := by
  simp [boolSeparator_self, boolSeparator_of_ne h, boolSeparator_of_ne h.symm]

/-- A Boolean map that separates a pair agrees on the pair with one of the two self-tests. -/
theorem separator_is_selfTest {p q : D} (h : p ≠ q) (f : D → Bool) (hf : f p ≠ f q) :
    (f p = boolSeparator p p ∧ f q = boolSeparator p q) ∨
      (f p = boolSeparator q p ∧ f q = boolSeparator q q) := by
  rw [boolSeparator_self, boolSeparator_self, boolSeparator_of_ne h, boolSeparator_of_ne h.symm]
  cases hp : f p <;> cases hq : f q <;> simp_all

variable [DecidableEq D]

/-- The swap of a pair maps the self-test of one point to the self-test of the other. -/
theorem boolSeparator_swap (p q x : D) :
    boolSeparator p (Equiv.swap p q x) = boolSeparator q x := by
  by_cases hx : x = q
  · rw [hx, Equiv.swap_apply_right, boolSeparator_self, boolSeparator_self]
  · have hne : Equiv.swap p q x ≠ p := by
      intro h
      apply hx
      have h' := congrArg (Equiv.swap p q) h
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at h'
    rw [boolSeparator_of_ne hne, boolSeparator_of_ne hx]

/-- A map is unchanged by the swap of a pair if and only if it takes one value on the pair. -/
theorem swap_invariant_iff {Z : Type*} (p q : D) (f : D → Z) :
    (∀ x, f (Equiv.swap p q x) = f x) ↔ f p = f q := by
  constructor
  · intro h
    have hp := h p
    rw [Equiv.swap_apply_left] at hp
    exact hp.symm
  · intro h x
    by_cases hp : x = p
    · rw [hp, Equiv.swap_apply_left]
      exact h.symm
    · by_cases hq : x = q
      · rw [hq, Equiv.swap_apply_right]
        exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hp hq]

/-- The swap of two points with one observation keeps every observation. -/
theorem swap_mem_licenseStabilizer {Q : Type*} (obs : D → Q) {p q : D} (h : obs p = obs q) :
    Equiv.swap p q ∈ OperationalInexpressibility.LicenseStabilizer.licenseStabilizer obs := by
  show ∀ x, obs (Equiv.swap p q x) = obs x
  exact (swap_invariant_iff p q obs).2 h

end Pair

/-! ## The two occurrences of `void` -/

/-- The frame occurrence of `void`. -/
def voidFrame : Occ Trace := (void, Role.frame)

/-- The active occurrence of `void`. -/
def voidActive : Occ Trace := (void, Role.active)

/-- The value observer on occurrences of traces. -/
def voidValue : Occ Trace → Trace := payloadValueProj

/-- The two occurrences are different. -/
theorem voidFrame_ne_voidActive : voidFrame ≠ voidActive :=
  occ_frame_ne_active void

/-- The two occurrences have one value. -/
theorem voidValue_eq : voidValue voidFrame = voidValue voidActive := rfl

/-- The fiber of the value observer over `void` is the pair. -/
theorem voidValue_fiber (o : Occ Trace) (h : voidValue o = void) :
    o = voidFrame ∨ o = voidActive := by
  obtain ⟨t, r⟩ := o
  have ht : t = void := h
  subst ht
  cases r
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The pair is a collision of the value observer against the identity target. -/
theorem voidPair_collision :
    OperationalInexpressibility.DirectGrammarBoundary.OperationallyInexpressibleAt
      voidValue (fun o : Occ Trace => o) voidFrame voidActive :=
  ⟨rfl, voidFrame_ne_voidActive⟩

/-! ## The pair as the two-point fixture -/

/-- The pair as a map from the two-point type. -/
def voidPair (i : Fin 2) : Occ Trace :=
  (void, if i = 0 then Role.frame else Role.active)

/-- Every point of the pair has value `void`. -/
theorem voidPair_value (i : Fin 2) : voidValue (voidPair i) = void := rfl

/-- The pair map is injective. -/
theorem voidPair_injective : Function.Injective voidPair := by
  intro i j h
  apply Fin.fin_two_eq_of_eq_zero_iff
  have hrole : (if i = 0 then Role.frame else Role.active) =
      (if j = 0 then Role.frame else Role.active) := congrArg Prod.snd h
  constructor
  · intro hi
    by_contra hj
    rw [if_pos hi, if_neg hj] at hrole
    exact Role.noConfusion hrole
  · intro hj
    by_contra hi
    rw [if_neg hi, if_pos hj] at hrole
    exact Role.noConfusion hrole

/-- The value observer and the identity target, pulled back along the pair, license the same sets
as the two-state fixture with one observation and the identity target. -/
theorem voidPair_licensedOn_iff (S : Set (Fin 2)) :
    OperationalInexpressibility.LiftOrRefuse.LicensedOn S
        (fun i : Fin 2 => voidValue (voidPair i)) voidPair ↔
      OperationalInexpressibility.LiftOrRefuse.LicensedOn S
        (fun _ : Fin 2 => ()) (fun x : Fin 2 => x) := by
  constructor
  · intro h x hx y hy _
    exact voidPair_injective (h x hx y hy rfl)
  · intro h x hx y hy _
    exact congrArg voidPair (h x hx y hy rfl)

/-- Two side symbols resolve the pair and one side symbol does not. -/
theorem voidPair_two_symbols :
    (∃ s : Fin 2 → Fin 2,
        OperationalInexpressibility.LicenseCriterion.Licensed
          (OperationalInexpressibility.Confusability.augmentObserver
            (fun i : Fin 2 => voidValue (voidPair i)) s) voidPair) ∧
      ¬ ∃ s : Fin 2 → Fin 1,
        OperationalInexpressibility.LicenseCriterion.Licensed
          (OperationalInexpressibility.Confusability.augmentObserver
            (fun i : Fin 2 => voidValue (voidPair i)) s) voidPair := by
  constructor
  · refine ⟨fun i => i, ?_⟩
    intro x y h
    have hxy : x = y := congrArg Prod.snd h
    rw [hxy]
  · rintro ⟨s, hs⟩
    have h01 : voidPair 0 = voidPair 1 :=
      hs 0 1 (congrArg (fun c : Fin 1 => ((void : Trace), c)) (Subsingleton.elim (s 0) (s 1)))
    exact absurd (voidPair_injective h01) (by decide)

/-! ## Comparison through the value and through value plus role -/

/-- No decoder that receives only the two values returns a correct record on the pair and on
its diagonal. -/
theorem voidPair_no_value_decoder
    (decoder : Trace × Trace → DistinctionBoundary.ObservationalDiagonalFork.MapCone) :
    ¬ (DistinctionBoundary.ObservationalDiagonalFork.RecordCorrect voidFrame voidFrame
          (decoder (voidValue voidFrame, voidValue voidFrame)) ∧
        DistinctionBoundary.ObservationalDiagonalFork.RecordCorrect voidFrame voidActive
          (decoder (voidValue voidFrame, voidValue voidActive))) :=
  DistinctionBoundary.ObservationalDiagonalFork.collapsed_pair_decoder_failure
    voidValue decoder voidValue_eq voidFrame_ne_voidActive

/-- A decoder that receives value and role returns a correct record on every pair. -/
theorem voidPair_role_decoder :
    ∃ decoder, DistinctionBoundary.ObservationalDiagonalFork.ObservedDecoderCorrect
      (fun o : Occ Trace => (voidValue o, o.2)) decoder :=
  (DistinctionBoundary.ObservationalDiagonalFork.joint_decoder_exists_iff_injective
    voidValue (fun o : Occ Trace => o.2)).2 (fun _ _ h => h)

/-! ## The theorem -/

/-- On the frame and active occurrences of `void`, the value projection agrees while the roles differ. The theorem combines value-factored refusal, Boolean separation, maximal licensed sets, symbol-count limits, swap invariance, decoding results, and the two root reducts of `eqW void void` with nonexpressibility of their difference. The one-bit channel comparison is stated separately. -/
theorem two_void_boundary :
    (voidValue voidFrame = voidValue voidActive ∧ voidFrame ≠ voidActive) ∧
    (∀ f : Occ Trace → Bool, ValueFactored voidValue f → f voidFrame = f voidActive) ∧
    (∃ f : Occ Trace → Bool, f voidFrame ≠ f voidActive) ∧
    (∀ f : Occ Trace → Bool, f voidFrame ≠ f voidActive → ¬ ValueFactored voidValue f) ∧
    ((∃ S : Set (Occ Trace),
        OperationalInexpressibility.LiftOrRefuse.MaximalLicensedOn S voidValue
          (fun o : Occ Trace => o) ∧ voidFrame ∈ S ∧ voidActive ∉ S) ∧
      ∃ T : Set (Occ Trace),
        OperationalInexpressibility.LiftOrRefuse.MaximalLicensedOn T voidValue
          (fun o : Occ Trace => o) ∧ voidActive ∈ T ∧ voidFrame ∉ T) ∧
    (¬ ∃ G : Set (Occ Trace),
        OperationalInexpressibility.LiftOrRefuse.LicensedOn G voidValue (fun o : Occ Trace => o) ∧
          ∀ S : Set (Occ Trace),
            OperationalInexpressibility.LiftOrRefuse.LicensedOn S voidValue
              (fun o : Occ Trace => o) → S ⊆ G) ∧
    ((∃ s : Fin 2 → Fin 2,
        OperationalInexpressibility.LicenseCriterion.Licensed
          (OperationalInexpressibility.Confusability.augmentObserver
            (fun i : Fin 2 => voidValue (voidPair i)) s) voidPair) ∧
      ¬ ∃ s : Fin 2 → Fin 1,
        OperationalInexpressibility.LicenseCriterion.Licensed
          (OperationalInexpressibility.Confusability.augmentObserver
            (fun i : Fin 2 => voidValue (voidPair i)) s) voidPair) ∧
    (Equiv.swap voidFrame voidActive ∈
        OperationalInexpressibility.LicenseStabilizer.licenseStabilizer voidValue ∧
      ∀ o : Occ Trace,
        boolSeparator voidFrame (Equiv.swap voidFrame voidActive o) = boolSeparator voidActive o) ∧
    ((∀ decoder : Trace × Trace → DistinctionBoundary.ObservationalDiagonalFork.MapCone,
        ¬ (DistinctionBoundary.ObservationalDiagonalFork.RecordCorrect voidFrame voidFrame
              (decoder (voidValue voidFrame, voidValue voidFrame)) ∧
            DistinctionBoundary.ObservationalDiagonalFork.RecordCorrect voidFrame voidActive
              (decoder (voidValue voidFrame, voidValue voidActive)))) ∧
      ∃ decoder, DistinctionBoundary.ObservationalDiagonalFork.ObservedDecoderCorrect
        (fun o : Occ Trace => (voidValue o, o.2)) decoder) ∧
    ((Step (eqW void void) void ∧ Step (eqW void void) (integrate (merge void void))) ∧
      ¬ ∃ t : SafeStep.SigmaFreeAlgebra.SigmaTerm,
        ∀ a b : SafeStep.SigmaFreeAlgebra.SigmaTerm,
          (a ≠ b) ↔
            (SafeStep.SigmaFreeAlgebra.evalSigma a b t ≠
              SafeStep.SigmaFreeAlgebra.SigmaTerm.void)) :=
  ⟨⟨voidValue_eq, voidFrame_ne_voidActive⟩,
    fun f hf => (payloadTwoActionBoundary void).refuses_valueFactored f hf,
    (payloadTwoActionBoundary void).lifts_separator,
    fun f hf => (payloadTwoActionBoundary void).separator_is_exogenous (f := f) hf,
    OperationalInexpressibility.LiftOrRefuse.maximal_refusals_of_collision voidPair_collision,
    OperationalInexpressibility.LiftUniversalProperty.no_greatest_licensedOn_of_collision
      voidPair_collision,
    voidPair_two_symbols,
    ⟨swap_mem_licenseStabilizer voidValue voidValue_eq,
      fun o => boolSeparator_swap voidFrame voidActive o⟩,
    ⟨voidPair_no_value_decoder, voidPair_role_decoder⟩,
    ⟨SafeStep.EqWVoidAnomaly.eqW_void_void_admits_two_normal_forms,
      SafeStep.SyntacticNonDerivability.disequality_not_sigma_expressible_unconditional⟩⟩

/-- On Fork3, the role-constant channel has Omega gap one and the role-resolving channel has gap zero, so their gap difference is one bit. -/
theorem two_void_role_bit :
    OverproductionGap.overproductionGap DistinctionBoundary.MinimalFork.Fork3Step
        DistinctionBoundary.MinimalFork.Fork3.source OverproductionGap.unitSurface
        OverproductionGap.roleWeights OverproductionGap.roleEcho -
      OverproductionGap.overproductionGap DistinctionBoundary.MinimalFork.Fork3Step
        DistinctionBoundary.MinimalFork.Fork3.source OverproductionGap.unitSurface
        OverproductionGap.roleWeights OverproductionGap.roleResolving = 1 :=
  OverproductionGap.one_bit_dp_exchange

/-- The two self-tests are complements on the pair. A Boolean map preserves the swap exactly when it agrees on both points, and the value fiber over `void` consists of these two occurrences. -/
theorem two_void_inside_outside :
    (∀ f : Occ Trace → Bool, f voidFrame ≠ f voidActive →
        (f voidFrame = boolSeparator voidFrame voidFrame ∧
            f voidActive = boolSeparator voidFrame voidActive) ∨
          (f voidFrame = boolSeparator voidActive voidFrame ∧
            f voidActive = boolSeparator voidActive voidActive)) ∧
    (boolSeparator voidFrame voidFrame = !boolSeparator voidActive voidFrame ∧
      boolSeparator voidFrame voidActive = !boolSeparator voidActive voidActive) ∧
    (∀ f : Occ Trace → Bool,
        (∀ o, f (Equiv.swap voidFrame voidActive o) = f o) ↔ f voidFrame = f voidActive) ∧
    (∀ o : Occ Trace, voidValue o = void → o = voidFrame ∨ o = voidActive) :=
  ⟨fun f hf => separator_is_selfTest voidFrame_ne_voidActive f hf,
    boolSeparator_pair_complement voidFrame_ne_voidActive,
    fun f => swap_invariant_iff voidFrame voidActive f,
    voidValue_fiber⟩

end OperatorKO7.Meta.BoundaryGeneral.TwoVoidBoundary
