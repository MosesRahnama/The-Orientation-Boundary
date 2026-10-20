import OperatorKO7.Meta.BoundaryObserver.ReconstructionGeneralGNS
import OperatorKO7.Meta.BoundaryObserver.ReconstructionLimitCompletion
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# S4.3: arbitrary-state GNS dynamics and compatible-stage state recovery

nodes G7, G8, G9, with exact pending graph patch in Supervisor Inbox430.

The flow consists of source C-star automorphisms, the group and state-invariance
laws, and pointwise source norm-continuity. None of the GNS representation,
Hilbert-space isometry, unitary equivalence, covariance, or strong continuity
is assumed as input. The quotient is the sealed QSpace of ReconstructionGeneralGNS
and is entered ONLY by classOf; its norm is the state seminorm, not the
original C-star norm. No multiplicative-character restriction is used.
No bounded Hamiltonian or zero generator is inferred.
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped ComplexOrder
open OperatorKO7.Meta.BoundaryObserver.ReconstructionGeneralGNS
open OperatorKO7.Meta.BoundaryObserver.ReconstructionLimitCompletion
open OperatorKO7.Meta.BoundaryObserver.ReconstructionLimitCompletion.PositiveFunctional

namespace OperatorKO7.Meta.BoundaryObserver.ReconstructionGNSDynamics

universe u v w

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (ω : A →ₚ[ℂ] ℂ)

/-- Genuine time-indexed source star automorphisms, with separately licensed
state invariance and pointwise norm continuity at every source algebra element.
The conclusion never assumes a Hilbert-space flow as a structure field. -/
structure InvariantStarFlow where
  «at» : ℝ → A ≃⋆ₐ[ℂ] A
  at_zero : ∀ a : A, «at» 0 a = a
  at_add : ∀ s t (a : A), «at» (s + t) a = «at» s («at» t a)
  state_invariant : ∀ t (a : A), ω («at» t a) = ω a
  continuous_source : ∀ a : A, Continuous (fun t : ℝ => «at» t a)

omit [StarOrderedRing A] in
/-- State invariance and star multiplicativity preserve the actual
state sesquilinear form on all pairs of algebra elements. -/
theorem invariant_form (D : InvariantStarFlow ω) (t : ℝ) (a b : A) :
    form ω (D.at t a) (D.at t b) = form ω a b := by
  change ω (star (D.at t a) * D.at t b) = ω (star a * b)
  rw [← map_star, ← map_mul]
  exact D.state_invariant t (star a * b)

/-- Every source automorphism maps the null space into itself and back.
Null equivalence is derived from the form, not added as a flow field. -/
theorem invariant_null_iff (D : InvariantStarFlow ω) (t : ℝ) (a : A) :
    D.at t a ∈ nullSubmodule ω ↔ a ∈ nullSubmodule ω := by
  change form ω (D.at t a) (D.at t a) = 0 ↔ form ω a a = 0
  rw [invariant_form ω D t a a]

/-- The actual source action descends through the sealed state quotient. -/
def quotientFlow (D : InvariantStarFlow ω) (t : ℝ) :
    QSpace ω →ₗ[ℂ] QSpace ω where
  toFun := fun x =>
    Quotient.liftOn x
      (fun a : A => (classOf ω (D.at t a) : QSpace ω)) (by
        intro a b hab
        apply (Submodule.Quotient.eq (nullSubmodule ω)).mpr
        have hnull : a - b ∈ nullSubmodule ω :=
          (Submodule.Quotient.eq (nullSubmodule ω)).mp (Quotient.sound hab)
        have hinv := (invariant_null_iff ω D t (a - b)).mpr hnull
        simpa only [map_sub] using hinv)
  map_add' := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    change classOf ω (D.at t (a + b)) =
      classOf ω (D.at t a) + classOf ω (D.at t b)
    rw [map_add, classOf_add]
  map_smul' := by
    intro c x
    refine Quotient.inductionOn x ?_
    intro a
    change classOf ω (D.at t (c • a)) = c • classOf ω (D.at t a)
    rw [map_smul, classOf_smul]

@[simp]
theorem quotientFlow_class (D : InvariantStarFlow ω) (t : ℝ) (a : A) :
    quotientFlow ω D t (classOf ω a) = classOf ω (D.at t a) := rfl

/-- The quotient form proves preservation of the true state inner product. -/
theorem quotientFlow_inner (D : InvariantStarFlow ω) (t : ℝ)
    (x y : QSpace ω) :
    inner ℂ (quotientFlow ω D t x) (quotientFlow ω D t y) =
      inner ℂ x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  change form ω (D.at t a) (D.at t b) = form ω a b
  exact invariant_form ω D t a b

/-- Equality of quadratic forms gives the norm identity for the sealed QSpace. -/
theorem quotientFlow_norm (D : InvariantStarFlow ω) (t : ℝ)
    (x : QSpace ω) :
    ‖quotientFlow ω D t x‖ = ‖x‖ := by
  have h := quotientFlow_inner ω D t x x
  have hx := norm_sq_eq_re_inner (𝕜 := ℂ) x
  have hy := norm_sq_eq_re_inner (𝕜 := ℂ) (quotientFlow ω D t x)
  rw [h] at hy
  nlinarith [norm_nonneg x, norm_nonneg (quotientFlow ω D t x)]

/-- Actual complex-linear quotient isometry, not a scalar character action. -/
def quotientIsometry (D : InvariantStarFlow ω) (t : ℝ) :
    QSpace ω →ₗᵢ[ℂ] QSpace ω :=
  { quotientFlow ω D t with
    norm_map' := quotientFlow_norm ω D t }

theorem quotientFlow_zero (D : InvariantStarFlow ω) (x : QSpace ω) :
    quotientFlow ω D 0 x = x := by
  obtain ⟨a, rfl⟩ := classOf_surjective ω x
  rw [quotientFlow_class, D.at_zero]

theorem quotientFlow_add (D : InvariantStarFlow ω) (s t : ℝ)
    (x : QSpace ω) :
    quotientFlow ω D (s + t) x =
      quotientFlow ω D s (quotientFlow ω D t x) := by
  obtain ⟨a, rfl⟩ := classOf_surjective ω x
  rw [quotientFlow_class, quotientFlow_class, quotientFlow_class, D.at_add]

/-- The quotient inverse is determined by negative time, not assumed. -/
theorem quotientFlow_inverse (D : InvariantStarFlow ω) (t : ℝ)
    (x : QSpace ω) :
    quotientFlow ω D (-t) (quotientFlow ω D t x) = x := by
  rw [← quotientFlow_add, neg_add_cancel, quotientFlow_zero]

/-- Map the quotient isometry to the uniform Hilbert completion. -/
def hilbertValue (D : InvariantStarFlow ω) (t : ℝ) :
    Hilbert ω → Hilbert ω :=
  UniformSpace.Completion.map (quotientIsometry ω D t)

theorem hilbertValue_continuous (D : InvariantStarFlow ω) (t : ℝ) :
    Continuous (hilbertValue ω D t) :=
  UniformSpace.Completion.continuous_map

@[simp]
theorem hilbertValue_class (D : InvariantStarFlow ω) (t : ℝ)
    (x : QSpace ω) :
    hilbertValue ω D t (x : Hilbert ω) =
      ((quotientFlow ω D t x : QSpace ω) : Hilbert ω) := by
  exact UniformSpace.Completion.map_coe
    (quotientIsometry ω D t).isometry.uniformContinuous x

/-- The completed operator is complex-linear, proved on its dense quotient. -/
theorem hilbertValue_add (D : InvariantStarFlow ω) (t : ℝ)
    (x y : Hilbert ω) :
    hilbertValue ω D t (x + y) =
      hilbertValue ω D t x + hilbertValue ω D t y := by
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq
      ((hilbertValue_continuous ω D t).comp
        (continuous_fst.add continuous_snd))
      (((hilbertValue_continuous ω D t).comp continuous_fst).add
        ((hilbertValue_continuous ω D t).comp continuous_snd))) ?_
  intro a b
  rw [← UniformSpace.Completion.coe_add, hilbertValue_class,
    map_add, UniformSpace.Completion.coe_add, hilbertValue_class, hilbertValue_class]

theorem hilbertValue_smul (D : InvariantStarFlow ω) (t : ℝ)
    (c : ℂ) (x : Hilbert ω) :
    hilbertValue ω D t (c • x) = c • hilbertValue ω D t x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq
      ((hilbertValue_continuous ω D t).comp (continuous_id.const_smul c))
      ((hilbertValue_continuous ω D t).const_smul c)) ?_
  intro a
  rw [← UniformSpace.Completion.coe_smul, hilbertValue_class,
    map_smul, UniformSpace.Completion.coe_smul, hilbertValue_class]

/-- Bundle the completed source action as a continuous linear operator. -/
def hilbertOperator (D : InvariantStarFlow ω) (t : ℝ) :
    Hilbert ω →L[ℂ] Hilbert ω where
  toFun := hilbertValue ω D t
  map_add' := hilbertValue_add ω D t
  map_smul' := hilbertValue_smul ω D t
  cont := hilbertValue_continuous ω D t

/-- The completed isometry follows from the quotient norm, using dense-range
continuity. Nothing identifies the quotient norm with the C-star norm. -/
theorem hilbertValue_norm (D : InvariantStarFlow ω) (t : ℝ)
    (x : Hilbert ω) : ‖hilbertValue ω D t x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (hilbertValue_continuous ω D t).norm continuous_norm) ?_
  intro a
  rw [hilbertValue_class, UniformSpace.Completion.norm_coe,
    UniformSpace.Completion.norm_coe, quotientFlow_norm]

def hilbertIsometry (D : InvariantStarFlow ω) (t : ℝ) :
    Hilbert ω →ₗᵢ[ℂ] Hilbert ω :=
  { (hilbertOperator ω D t).toLinearMap with
    norm_map' := hilbertValue_norm ω D t }

theorem hilbertValue_dist (D : InvariantStarFlow ω) (t : ℝ)
    (x y : Hilbert ω) :
    dist (hilbertValue ω D t x) (hilbertValue ω D t y) = dist x y :=
  (hilbertIsometry ω D t).isometry.dist_eq x y

theorem hilbertValue_zero (D : InvariantStarFlow ω) (x : Hilbert ω) :
    hilbertValue ω D 0 x = x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (hilbertValue_continuous ω D 0) continuous_id) ?_
  intro a
  rw [hilbertValue_class, quotientFlow_zero]

theorem hilbertValue_group (D : InvariantStarFlow ω) (s t : ℝ)
    (x : Hilbert ω) :
    hilbertValue ω D (s + t) x =
      hilbertValue ω D s (hilbertValue ω D t x) := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (hilbertValue_continuous ω D (s + t))
      ((hilbertValue_continuous ω D s).comp
        (hilbertValue_continuous ω D t))) ?_
  intro a
  rw [hilbertValue_class, hilbertValue_class, hilbertValue_class,
    quotientFlow_add]

theorem hilbertValue_inverse (D : InvariantStarFlow ω) (t : ℝ)
    (x : Hilbert ω) :
    hilbertValue ω D (-t) (hilbertValue ω D t x) = x := by
  rw [← hilbertValue_group, neg_add_cancel, hilbertValue_zero]

/-- The Hilbert-space maps are genuinely onto because negative time supplies
their inverse. Thus they are unitary complex-linear isometric equivalences. -/
def hilbertUnitary (D : InvariantStarFlow ω) (t : ℝ) :
    Hilbert ω ≃ₗᵢ[ℂ] Hilbert ω :=
  LinearIsometryEquiv.ofSurjective (hilbertIsometry ω D t) (by
    intro x
    refine ⟨hilbertValue ω D (-t) x, ?_⟩
    change hilbertValue ω D t (hilbertValue ω D (-t) x) = x
    rw [← hilbertValue_group, add_neg_cancel, hilbertValue_zero])

@[simp]
theorem hilbertUnitary_apply (D : InvariantStarFlow ω) (t : ℝ)
    (x : Hilbert ω) :
    hilbertUnitary ω D t x = hilbertValue ω D t x := rfl

/-- Preservation of the complex inner product on the WHOLE Hilbert space. -/
theorem hilbertValue_inner (D : InvariantStarFlow ω) (t : ℝ)
    (x y : Hilbert ω) :
    inner ℂ (hilbertValue ω D t x) (hilbertValue ω D t y) =
      inner ℂ x y := by
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq
      (((hilbertValue_continuous ω D t).comp continuous_fst).inner
        ((hilbertValue_continuous ω D t).comp continuous_snd))
      (continuous_fst.inner continuous_snd)) ?_
  intro a b
  rw [hilbertValue_class, hilbertValue_class,
    UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe]
  exact quotientFlow_inner ω D t a b

/-- In a star-algebra equivalence, the source unit is fixed.
The vector [1] remains a genuinely cyclic source memory vector. -/
theorem hilbertValue_cyclic (D : InvariantStarFlow ω) (t : ℝ) :
    hilbertValue ω D t (cyclicVector ω) = cyclicVector ω := by
  change hilbertValue ω D t
    ((classOf ω (1 : A) : QSpace ω) : Hilbert ω) =
      ((classOf ω (1 : A) : QSpace ω) : Hilbert ω)
  rw [hilbertValue_class, quotientFlow_class, map_one]

/-- Covariance couples the FULL GNS representation to the same source
star automorphism at every time, not merely to one prepared endpoint. -/
theorem hilbertValue_covariant (D : InvariantStarFlow ω) (t : ℝ)
    (a : A) (x : Hilbert ω) :
    hilbertValue ω D t (representation ω a x) =
      representation ω (D.at t a) (hilbertValue ω D t x) := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq
      ((hilbertValue_continuous ω D t).comp (representation ω a).continuous)
      ((representation ω (D.at t a)).continuous.comp
        (hilbertValue_continuous ω D t))) ?_
  intro q
  refine Quotient.inductionOn q ?_
  intro b
  change hilbertValue ω D t
      (action ω a ((classOf ω b : QSpace ω) : Hilbert ω)) =
    action ω (D.at t a)
      (hilbertValue ω D t ((classOf ω b : QSpace ω) : Hilbert ω))
  rw [action_mk, hilbertValue_class, quotientFlow_class,
    hilbertValue_class, quotientFlow_class, action_mk, map_mul]

/-! The normalization assumption now has real work: it proves that the
classOf map into the STATE-norm quotient is uniformly bounded, so pointwise
norm-continuity of the original flow transfers to the dense quotient orbit. -/

def classLinear : A →ₗ[ℂ] QSpace ω where
  toFun := classOf ω
  map_add' := classOf_add ω
  map_smul' := classOf_smul ω

theorem classOf_norm_le (hω : ω 1 = 1) (a : A) :
    ‖classOf ω a‖ ≤ ‖a‖ := by
  have hunit : seminorm ω (1 : A) = 1 := by
    have h := norm_cyclicVector ω hω
    change ‖((classOf ω (1 : A) : QSpace ω) : Hilbert ω)‖ = 1 at h
    simpa only [UniformSpace.Completion.norm_coe, norm_quotient_mk] using h
  calc
    ‖classOf ω a‖ = seminorm ω a := norm_quotient_mk ω a
    _ = seminorm ω (a * 1) := by rw [mul_one]
    _ ≤ ‖a‖ * seminorm ω 1 := seminorm_left_mul_le ω a 1
    _ = ‖a‖ := by rw [hunit, mul_one]

def classContinuous (hω : ω 1 = 1) : A →L[ℂ] QSpace ω :=
  (classLinear ω).mkContinuous 1
    (fun a => by simpa only [one_mul] using classOf_norm_le ω hω a)

theorem quotientOrbit_continuous (hω : ω 1 = 1)
    (D : InvariantStarFlow ω) (a : A) :
    Continuous (fun t : ℝ => quotientFlow ω D t (classOf ω a)) := by
  have h := (classContinuous ω hω).continuous.comp (D.continuous_source a)
  simpa only [quotientFlow_class] using h

theorem hilbertDenseOrbit_continuous (hω : ω 1 = 1)
    (D : InvariantStarFlow ω) (a : A) :
    Continuous (fun t : ℝ =>
      hilbertValue ω D t ((classOf ω a : QSpace ω) : Hilbert ω)) := by
  have h := (UniformSpace.Completion.toComplL : QSpace ω →L[ℂ] Hilbert ω).continuous.comp
    (quotientOrbit_continuous ω hω D a)
  simpa only [hilbertValue_class] using h

/-- Strong continuity from the actual source action. For each x, choose a
dense quotient vector q within epsilon/4. Isometry bounds both errors by
‖x-q‖, while source norm continuity controls the q-orbit by epsilon/2.
No zero-generator or character argument occurs. -/
theorem hilbertStrongContinuous (hω : ω 1 = 1)
    (D : InvariantStarFlow ω) (x : Hilbert ω) :
    Continuous (fun t : ℝ => hilbertValue ω D t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hdense : DenseRange (fun q : QSpace ω => (q : Hilbert ω)) :=
    UniformSpace.Completion.denseRange_coe
  have hx : x ∈ closure
      (Set.range (fun q : QSpace ω => (q : Hilbert ω))) := hdense x
  obtain ⟨v, ⟨q, rfl⟩, hq⟩ :=
    (Metric.mem_closure_iff.mp hx) (ε / 4) (by positivity)
  have hqcont : ContinuousAt
      (fun t : ℝ => hilbertValue ω D t (q : Hilbert ω)) t₀ := by
    obtain ⟨a, ha⟩ := classOf_surjective ω q
    subst q
    exact (hilbertDenseOrbit_continuous ω hω D a).continuousAt
  have hnear :=
    (Metric.tendsto_nhds.mp hqcont) (ε / 2) (by positivity)
  filter_upwards [hnear] with t ht
  have hq' : dist (q : Hilbert ω) x < ε / 4 := by
    simpa only [dist_comm] using hq
  calc
    dist (hilbertValue ω D t x) (hilbertValue ω D t₀ x) ≤
        dist (hilbertValue ω D t x) (hilbertValue ω D t (q : Hilbert ω)) +
          dist (hilbertValue ω D t (q : Hilbert ω))
            (hilbertValue ω D t₀ x) :=
      dist_triangle _ _ _
    _ ≤ dist (hilbertValue ω D t x)
          (hilbertValue ω D t (q : Hilbert ω)) +
        (dist (hilbertValue ω D t (q : Hilbert ω))
          (hilbertValue ω D t₀ (q : Hilbert ω)) +
         dist (hilbertValue ω D t₀ (q : Hilbert ω))
          (hilbertValue ω D t₀ x)) := by
        gcongr
        exact dist_triangle _ _ _
    _ = dist x (q : Hilbert ω) +
        dist (hilbertValue ω D t (q : Hilbert ω))
          (hilbertValue ω D t₀ (q : Hilbert ω)) +
        dist (q : Hilbert ω) x := by
          rw [hilbertValue_dist, hilbertValue_dist, add_assoc]
    _ < ε := by linarith

/-- Every unitary orbit is continuous, and the group, covariance, vector
state and fixed cyclic vector are consequences of source data only. -/
def GeneralHilbertDynamicsGoal (_ : ω 1 = 1) (D : InvariantStarFlow ω) : Prop :=
    (∀ s t (x : Hilbert ω),
      hilbertValue ω D (s + t) x =
        hilbertValue ω D s (hilbertValue ω D t x)) ∧
    (∀ t (x : Hilbert ω),
      hilbertValue ω D (-t) (hilbertValue ω D t x) = x) ∧
    (∀ t (x y : Hilbert ω),
      inner ℂ (hilbertValue ω D t x) (hilbertValue ω D t y) =
        inner ℂ x y) ∧
    (∀ t, hilbertValue ω D t (cyclicVector ω) = cyclicVector ω) ∧
    (∀ t (a : A) (x : Hilbert ω),
      hilbertValue ω D t (representation ω a x) =
        representation ω (D.at t a) (hilbertValue ω D t x)) ∧
    (∀ x : Hilbert ω, Continuous
      (fun t : ℝ => hilbertValue ω D t x)) ∧
    ‖cyclicVector ω‖ = 1

theorem generalHilbertDynamicsGoal (hω : ω 1 = 1)
    (D : InvariantStarFlow ω) :
    GeneralHilbertDynamicsGoal ω hω D :=
  ⟨hilbertValue_group ω D, hilbertValue_inverse ω D,
   hilbertValue_inner ω D, hilbertValue_cyclic ω D,
   hilbertValue_covariant ω D, hilbertStrongContinuous ω hω D,
   norm_cyclicVector ω hω⟩

/-! The following state identity and uniqueness use a compatible positive
finite-stage family and ITS OWN completed functional. There is no claim
identifying this arbitrary state with the geometric thermodynamic source. -/
section CompatibleStageRecovery

variable {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable {S : IsometricStarSystem ι}
variable [∀ i, PartialOrder (S.Fiber i)]
variable [∀ i, StarOrderedRing (S.Fiber i)]
variable (Ω : CompatibleStateFamily S)

/-- Exact vector-state recovery for every actual stage algebra element. -/
theorem compatibleStageStateIdentity (i : ι) (a : S.Fiber i) :
    inner ℂ (cyclicVector Ω.completionState)
      (representation Ω.completionState (S.stageMap i a)
        (cyclicVector Ω.completionState)) = Ω.state i a := by
  calc
    inner ℂ (cyclicVector Ω.completionState)
      (representation Ω.completionState (S.stageMap i a)
        (cyclicVector Ω.completionState)) =
      Ω.completionState (S.stageMap i a) :=
        state_identity Ω.completionState (S.stageMap i a)
    _ = Ω.state i a := Ω.completionState_on_stage i a

/-- Normalization has a genuine observable consequence in the GNS space. -/
theorem compatibleStageCyclicUnit :
    ‖cyclicVector Ω.completionState‖ = 1 :=
  norm_cyclicVector Ω.completionState Ω.completionState_one

/-- A continuous functional agreeing with all stage vector expectations
is uniquely the original completed positive state functional. -/
theorem compatibleStateUnique (f : S.Completion →L[ℂ] ℂ)
    (hf : ∀ i (a : S.Fiber i),
      f (S.stageMap i a) =
        inner ℂ (cyclicVector Ω.completionState)
          (representation Ω.completionState (S.stageMap i a)
            (cyclicVector Ω.completionState))) :
    f = Ω.completionLinear := by
  apply Ω.completionLinear_unique f
  intro i a
  rw [hf i a, compatibleStageStateIdentity Ω i a]

/-- The stage identities, unique state and normalized GNS vector are
constructed together from Ω, with no character or physical-source cast. -/
def CompatibleGeneralGNSRecoveryGoal : Prop :=
    (∀ i (a : S.Fiber i),
      inner ℂ (cyclicVector Ω.completionState)
        (representation Ω.completionState (S.stageMap i a)
          (cyclicVector Ω.completionState)) = Ω.state i a) ∧
    ‖cyclicVector Ω.completionState‖ = 1 ∧
    (∀ f : S.Completion →L[ℂ] ℂ,
      (∀ i (a : S.Fiber i),
        f (S.stageMap i a) =
          inner ℂ (cyclicVector Ω.completionState)
            (representation Ω.completionState (S.stageMap i a)
              (cyclicVector Ω.completionState))) →
      f = Ω.completionLinear)

theorem compatibleGeneralGNSRecoveryGoal :
    CompatibleGeneralGNSRecoveryGoal Ω :=
  ⟨compatibleStageStateIdentity Ω,
    compatibleStageCyclicUnit Ω,
    compatibleStateUnique Ω⟩

end CompatibleStageRecovery
end OperatorKO7.Meta.BoundaryObserver.ReconstructionGNSDynamics
