import OperatorKO7.Meta.BoundaryObserver.ReconstructionLimits
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import OperatorKO7.Meta.BoundaryObserver.ReconstructionLimitThermodynamics

/-!
# C* completion of a directed system of finite stages

An isometric star system has C* algebras as stages and coherent unital star embeddings that
preserve the norm. Its algebraic direct limit carries the descended norm, product, scalar
action, and adjoint, and satisfies the C* norm identity. The limit is a sealed definition, so
the quotient topology of the underlying quotient type is not an instance on it. Its uniform
completion is a C* algebra into which every stage embeds isometrically, coherently, and with
dense joint range. A compatible family of normalized positive stage states descends to a
positive norm-one functional on the limit and extends uniquely to the completion as a
positive normalized state. The positive form of a state on a C* algebra satisfies the
Cauchy-Schwarz inequality, and its null space is a left ideal.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Classical ComplexOrder

namespace OperatorKO7.Meta.BoundaryObserver
namespace ReconstructionLimitCompletion

universe u v

/-- The supplied data consist of C* stages and coherent norm-preserving unital star maps. -/
structure IsometricStarSystem (ι : Type u) [Preorder ι] where
  Fiber : ι → Type v
  [fiberCStar : ∀ i, CStarAlgebra (Fiber i)]
  embed : ∀ i j, i ≤ j → Fiber i →⋆ₐ[ℂ] Fiber j
  embed_self : ∀ i a, embed i i le_rfl a = a
  embed_comp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) a,
    embed j k hjk (embed i j hij a) = embed i k (hij.trans hjk) a
  embed_norm : ∀ i j (h : i ≤ j) a, ‖embed i j h a‖ = ‖a‖

attribute [instance] IsometricStarSystem.fiberCStar

/-! ### The uniform completion of a pre-C* algebra

The constructions are stated for an abstract normed complex star algebra with the C* norm
identity, then specialized to the algebraic direct limit. The completion carries the
continuous extensions of the product, the scalar action and the adjoint. -/

section CStarCompletion

variable (A : Type v) [NormedRing A] [StarRing A] [CStarRing A] [NormedAlgebra ℂ A]
  [StarModule ℂ A]

/-- The completion of a normed complex algebra is a normed complex algebra. -/
noncomputable def completionNormedAlgebraOf :
    NormedAlgebra ℂ (UniformSpace.Completion A) where
  norm_smul_le := norm_smul_le

attribute [local instance] completionNormedAlgebraOf

/-- The adjoint of the completion is the continuous extension of the adjoint. -/
noncomputable def completionStarOf : Star (UniformSpace.Completion A) where
  star := UniformSpace.Completion.map (star : A → A)

attribute [local instance] completionStarOf

omit [NormedAlgebra ℂ A] [StarModule ℂ A] in
theorem completionOf_star_coe (x : A) :
    star (x : UniformSpace.Completion A) = ((star x : A) : UniformSpace.Completion A) :=
  UniformSpace.Completion.map_coe star_isometry.uniformContinuous x

omit [CStarRing A] [NormedAlgebra ℂ A] [StarModule ℂ A] in
theorem completionOf_continuous_star :
    Continuous (star : UniformSpace.Completion A → UniformSpace.Completion A) :=
  UniformSpace.Completion.continuous_map

/-- The extended adjoint is an involutive anti-multiplicative additive map. -/
noncomputable def completionStarRingOf : StarRing (UniformSpace.Completion A) where
  toStar := completionStarOf A
  star_involutive := by
    intro x
    refine UniformSpace.Completion.induction_on x
      (isClosed_eq ((completionOf_continuous_star A).comp (completionOf_continuous_star A))
        continuous_id) ?_
    intro a
    rw [completionOf_star_coe, completionOf_star_coe, star_star]
  star_mul := by
    intro x y
    refine UniformSpace.Completion.induction_on₂ x y
      (isClosed_eq ((completionOf_continuous_star A).comp (continuous_fst.mul continuous_snd))
        (((completionOf_continuous_star A).comp continuous_snd).mul
          ((completionOf_continuous_star A).comp continuous_fst))) ?_
    intro a b
    rw [← UniformSpace.Completion.coe_mul, completionOf_star_coe, star_mul,
      UniformSpace.Completion.coe_mul, completionOf_star_coe, completionOf_star_coe]
  star_add := by
    intro x y
    refine UniformSpace.Completion.induction_on₂ x y
      (isClosed_eq ((completionOf_continuous_star A).comp (continuous_fst.add continuous_snd))
        (((completionOf_continuous_star A).comp continuous_fst).add
          ((completionOf_continuous_star A).comp continuous_snd))) ?_
    intro a b
    rw [← UniformSpace.Completion.coe_add, completionOf_star_coe, star_add,
      UniformSpace.Completion.coe_add, completionOf_star_coe, completionOf_star_coe]

attribute [local instance] completionStarRingOf

/-- The extended adjoint is conjugate linear. -/
noncomputable def completionStarModuleOf : StarModule ℂ (UniformSpace.Completion A) where
  star_smul := by
    intro c x
    refine UniformSpace.Completion.induction_on x
      (isClosed_eq ((completionOf_continuous_star A).comp (continuous_id.const_smul c))
        ((completionOf_continuous_star A).const_smul (star c))) ?_
    intro a
    rw [← UniformSpace.Completion.coe_smul, completionOf_star_coe, star_smul,
      UniformSpace.Completion.coe_smul, completionOf_star_coe]

attribute [local instance] completionStarModuleOf

/-- The C* norm identity extends from the dense algebra to the completion. -/
noncomputable def completionCStarRingOf : CStarRing (UniformSpace.Completion A) where
  norm_mul_self_le := by
    intro x
    refine UniformSpace.Completion.induction_on x
      (isClosed_le (continuous_norm.mul continuous_norm)
        (((completionOf_continuous_star A).mul continuous_id).norm)) ?_
    intro a
    rw [completionOf_star_coe, ← UniformSpace.Completion.coe_mul,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
    exact CStarRing.norm_mul_self_le a

attribute [local instance] completionCStarRingOf

/-- The completion of a pre-C* algebra is a C* algebra. -/
noncomputable def completionCStarAlgebraOf : CStarAlgebra (UniformSpace.Completion A) where

end CStarCompletion

namespace IsometricStarSystem

variable {ι : Type u} [Preorder ι] (S : IsometricStarSystem.{u, v} ι)

instance directed : DirectedSystem S.Fiber (fun i j h => S.embed i j h) where
  map_self := by
    intro i a
    exact S.embed_self i a
  map_map := by
    intro k j i hij hjk a
    exact S.embed_comp i j k hij hjk a

variable [IsDirected ι (· ≤ ·)] [Nonempty ι]

/-- The carrier is the actual quotient by eventual equality at a common stage. It is a
sealed definition, so the quotient topology of the underlying quotient type is not an
instance on it, and the only topology is the one of the limit norm constructed below. -/
def AlgebraicLimit : Type (max u v) :=
  DirectLimit S.Fiber (fun i j h => S.embed i j h)

instance algebraicRing : Ring S.AlgebraicLimit :=
  inferInstanceAs (Ring (DirectLimit S.Fiber (fun i j h => S.embed i j h)))

instance algebraicModule : Module ℂ S.AlgebraicLimit :=
  inferInstanceAs (Module ℂ (DirectLimit S.Fiber (fun i j h => S.embed i j h)))

/-- Each stage enters the algebraic quotient through its canonical unital ring map. -/
def algebraicRingMap (i : ι) : S.Fiber i →+* S.AlgebraicLimit :=
  DirectLimit.Ring.of S.Fiber (fun i j h => S.embed i j h) i

theorem algebraicRingMap_smul (i : ι) (c : ℂ) (a : S.Fiber i) :
    S.algebraicRingMap i (c • a) = c • S.algebraicRingMap i a := by
  rfl

/-- The norm descends because every transition preserves the stage norm. -/
def size : S.AlgebraicLimit → ℝ :=
  DirectLimit.lift (f := fun i j h => S.embed i j h)
    (fun i (a : S.Fiber i) => ‖a‖)
    (fun i j h a => (S.embed_norm i j h a).symm)

theorem size_of (i : ι) (a : S.Fiber i) :
    S.size (S.algebraicRingMap i a) = ‖a‖ := by
  rfl

theorem size_representatives (i j : ι) (a : S.Fiber i) (b : S.Fiber j)
    (h : S.algebraicRingMap i a = S.algebraicRingMap j b) : ‖a‖ = ‖b‖ := by
  exact congrArg S.size h

/-- The quotient norm satisfies all ring-norm laws, including definiteness. -/
def algebraicRingNorm : RingNorm S.AlgebraicLimit where
  toFun := S.size
  map_zero' := by
    rw [← map_zero (S.algebraicRingMap (Classical.arbitrary ι)), size_of, norm_zero]
  add_le' := by
    intro x y
    refine DirectLimit.induction₂ (f := fun i j h => S.embed i j h) ?_ x y
    intro i a b
    change S.size (S.algebraicRingMap i a + S.algebraicRingMap i b) ≤
      S.size (S.algebraicRingMap i a) + S.size (S.algebraicRingMap i b)
    rw [← map_add (S.algebraicRingMap i) a b]
    exact norm_add_le a b
  neg' := by
    intro x
    refine DirectLimit.induction (f := fun i j h => S.embed i j h) ?_ x
    intro i a
    change S.size (-S.algebraicRingMap i a) = S.size (S.algebraicRingMap i a)
    rw [← map_neg (S.algebraicRingMap i) a]
    exact norm_neg a
  mul_le' := by
    intro x y
    refine DirectLimit.induction₂ (f := fun i j h => S.embed i j h) ?_ x y
    intro i a b
    change S.size (S.algebraicRingMap i a * S.algebraicRingMap i b) ≤
      S.size (S.algebraicRingMap i a) * S.size (S.algebraicRingMap i b)
    rw [← map_mul (S.algebraicRingMap i) a b]
    exact norm_mul_le a b
  eq_zero_of_map_eq_zero' := by
    intro x
    refine DirectLimit.induction (f := fun i j h => S.embed i j h) ?_ x
    intro i a ha
    change ‖a‖ = 0 at ha
    change S.algebraicRingMap i a = 0
    rw [norm_eq_zero.mp ha, map_zero]

instance algebraicNormedRing : NormedRing S.AlgebraicLimit :=
  S.algebraicRingNorm.toNormedRing

theorem algebraic_norm_eq_size (x : S.AlgebraicLimit) : ‖x‖ = S.size x := by
  rfl

instance algebraicAlgebra : Algebra ℂ S.AlgebraicLimit :=
  Algebra.ofModule
    (by
      intro c x y
      refine DirectLimit.induction₂ (f := fun i j h => S.embed i j h) ?_ x y
      intro i a b
      change c • S.algebraicRingMap i a * S.algebraicRingMap i b =
        c • (S.algebraicRingMap i a * S.algebraicRingMap i b)
      rw [← algebraicRingMap_smul, ← map_mul, smul_mul_assoc,
        algebraicRingMap_smul, map_mul])
    (by
      intro c x y
      refine DirectLimit.induction₂ (f := fun i j h => S.embed i j h) ?_ x y
      intro i a b
      change S.algebraicRingMap i a * c • S.algebraicRingMap i b =
        c • (S.algebraicRingMap i a * S.algebraicRingMap i b)
      rw [← algebraicRingMap_smul, ← map_mul, mul_smul_comm,
        algebraicRingMap_smul, map_mul])

instance algebraicNormedAlgebra : NormedAlgebra ℂ S.AlgebraicLimit where
  norm_smul_le := by
    intro c x
    refine DirectLimit.induction (f := fun i j h => S.embed i j h) ?_ x
    intro i a
    change S.size (c • S.algebraicRingMap i a) ≤ ‖c‖ * S.size (S.algebraicRingMap i a)
    rw [← algebraicRingMap_smul]
    exact norm_smul_le c a

/-- The adjoint descends through the same representative relation. -/
def adjoint : S.AlgebraicLimit → S.AlgebraicLimit :=
  DirectLimit.map
    (f₁ := fun i j h => S.embed i j h)
    (f₂ := fun i j h => S.embed i j h)
    (fun i (a : S.Fiber i) => star a)
    (fun i j h a => map_star (S.embed i j h) a)

theorem adjoint_of (i : ι) (a : S.Fiber i) :
    S.adjoint (S.algebraicRingMap i a) = S.algebraicRingMap i (star a) := by
  rfl

instance algebraicStarRing : StarRing S.AlgebraicLimit where
  star := S.adjoint
  star_involutive := by
    intro x
    refine DirectLimit.induction (f := fun i j h => S.embed i j h) ?_ x
    intro i a
    change S.adjoint (S.adjoint (S.algebraicRingMap i a)) = S.algebraicRingMap i a
    rw [adjoint_of, adjoint_of, star_star]
  star_mul := by
    intro x y
    refine DirectLimit.induction₂ (f := fun i j h => S.embed i j h) ?_ x y
    intro i a b
    change S.adjoint (S.algebraicRingMap i a * S.algebraicRingMap i b) =
      S.adjoint (S.algebraicRingMap i b) * S.adjoint (S.algebraicRingMap i a)
    rw [← map_mul (S.algebraicRingMap i) a b, adjoint_of, star_mul,
      map_mul, adjoint_of, adjoint_of]
  star_add := by
    intro x y
    refine DirectLimit.induction₂ (f := fun i j h => S.embed i j h) ?_ x y
    intro i a b
    change S.adjoint (S.algebraicRingMap i a + S.algebraicRingMap i b) =
      S.adjoint (S.algebraicRingMap i a) + S.adjoint (S.algebraicRingMap i b)
    rw [← map_add (S.algebraicRingMap i) a b, adjoint_of, star_add,
      map_add, adjoint_of, adjoint_of]

instance algebraicStarModule : StarModule ℂ S.AlgebraicLimit where
  star_smul := by
    intro c x
    refine DirectLimit.induction (f := fun i j h => S.embed i j h) ?_ x
    intro i a
    change S.adjoint (c • S.algebraicRingMap i a) =
      star c • S.adjoint (S.algebraicRingMap i a)
    rw [← algebraicRingMap_smul, adjoint_of, star_smul,
      algebraicRingMap_smul, adjoint_of]

instance algebraicCStarRing : CStarRing S.AlgebraicLimit where
  norm_mul_self_le := by
    intro x
    refine DirectLimit.induction (f := fun i j h => S.embed i j h) ?_ x
    intro i a
    change S.size (S.algebraicRingMap i a) * S.size (S.algebraicRingMap i a) ≤
      S.size (S.adjoint (S.algebraicRingMap i a) * S.algebraicRingMap i a)
    rw [adjoint_of, ← map_mul]
    exact CStarRing.norm_mul_self_le a

/-- The canonical stage maps preserve the scalar action and adjoint as well as the unit. -/
def algebraicMap (i : ι) : S.Fiber i →⋆ₐ[ℂ] S.AlgebraicLimit where
  __ := S.algebraicRingMap i
  commutes' := by
    intro c
    change S.algebraicRingMap i (algebraMap ℂ (S.Fiber i) c) = algebraMap ℂ S.AlgebraicLimit c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, algebraicRingMap_smul,
      map_one]
  map_star' := by
    intro a
    rfl

theorem algebraicMap_norm (i : ι) (a : S.Fiber i) :
    ‖S.algebraicMap i a‖ = ‖a‖ := by
  rfl

/-- The stage norm law supplies a bundled linear isometry. -/
def algebraicIsometry (i : ι) : S.Fiber i →ₗᵢ[ℂ] S.AlgebraicLimit where
  __ := (S.algebraicMap i).toAlgHom.toLinearMap
  norm_map' := S.algebraicMap_norm i

theorem algebraicMap_injective (i : ι) : Function.Injective (S.algebraicMap i) :=
  (S.algebraicIsometry i).injective

/-- The specified C* completion is the Hausdorff uniform completion of the constructed norm. -/
abbrev Completion := UniformSpace.Completion S.AlgebraicLimit

instance completionNormedAlgebra : NormedAlgebra ℂ S.Completion :=
  completionNormedAlgebraOf S.AlgebraicLimit

instance completionStarRing : StarRing S.Completion :=
  completionStarRingOf S.AlgebraicLimit

theorem completion_star_coe (x : S.AlgebraicLimit) :
    star (x : S.Completion) = ((star x : S.AlgebraicLimit) : S.Completion) :=
  completionOf_star_coe S.AlgebraicLimit x

instance completionContinuousStar : ContinuousStar S.Completion where
  continuous_star := completionOf_continuous_star S.AlgebraicLimit

instance completionStarModule : StarModule ℂ S.Completion :=
  completionStarModuleOf S.AlgebraicLimit

instance completionCStarRing : CStarRing S.Completion :=
  completionCStarRingOf S.AlgebraicLimit

instance completionCStarAlgebra : CStarAlgebra S.Completion :=
  completionCStarAlgebraOf S.AlgebraicLimit

theorem completion_complete : CompleteSpace S.Completion :=
  UniformSpace.Completion.completeSpace S.AlgebraicLimit

/-- The algebraic limit enters its completion through the canonical unital star homomorphism. -/
def algebraicIntoCompletion : S.AlgebraicLimit →⋆ₐ[ℂ] S.Completion where
  __ := (UniformSpace.Completion.coeRingHom : S.AlgebraicLimit →+* S.Completion)
  commutes' := by
    intro c
    rfl
  map_star' := by
    intro a
    exact (S.completion_star_coe a).symm

/-- Every stage enters the completion by the constructed algebraic inclusion. -/
def stageMap (i : ι) : S.Fiber i →⋆ₐ[ℂ] S.Completion :=
  S.algebraicIntoCompletion.comp (S.algebraicMap i)

theorem stageMap_norm (i : ι) (a : S.Fiber i) : ‖S.stageMap i a‖ = ‖a‖ := by
  change ‖(S.algebraicMap i a : S.Completion)‖ = ‖a‖
  rw [UniformSpace.Completion.norm_coe, algebraicMap_norm]

/-- The stage inclusion is bundled as a linear isometry into the completion. -/
def stageIsometry (i : ι) : S.Fiber i →ₗᵢ[ℂ] S.Completion where
  __ := (S.stageMap i).toAlgHom.toLinearMap
  norm_map' := S.stageMap_norm i

theorem stageMap_isometry (i : ι) : Isometry (S.stageMap i) :=
  (S.stageIsometry i).isometry

theorem stageMap_injective (i : ι) : Function.Injective (S.stageMap i) :=
  (S.stageIsometry i).injective

theorem stageMap_coherent (i j : ι) (h : i ≤ j) (a : S.Fiber i) :
    S.stageMap j (S.embed i j h a) = S.stageMap i a := by
  apply congrArg S.algebraicIntoCompletion
  exact DirectLimit.Ring.of_f (f := fun i j h => S.embed i j h) h a

theorem stageMap_dense : DenseRange (fun p : Σ i, S.Fiber i => S.stageMap p.1 p.2) := by
  have hrange : Set.range (fun p : Σ i, S.Fiber i => S.stageMap p.1 p.2) =
      Set.range S.algebraicIntoCompletion := by
    ext z
    constructor
    · rintro ⟨⟨i, a⟩, rfl⟩
      exact ⟨S.algebraicMap i a, rfl⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨i, b, h⟩ := DirectLimit.exists_eq_mk
        (f := fun i j h => S.embed i j h) a
      subst a
      exact ⟨⟨i, b⟩, rfl⟩
  change Dense (Set.range (fun p : Σ i, S.Fiber i => S.stageMap p.1 p.2))
  rw [hrange]
  exact UniformSpace.Completion.denseRange_coe

/-- The completed direct system has faithful coherent isometric stages with dense combined range. -/
def DirectedCStarCompletionGoal : Prop :=
  (∀ i (a : S.Fiber i), ‖S.algebraicMap i a‖ = ‖a‖) ∧
  (∀ x : S.AlgebraicLimit, ‖star x * x‖ = ‖x‖ * ‖x‖) ∧
  (∀ i, Function.Injective (S.stageMap i)) ∧
  (∀ i, Isometry (S.stageMap i)) ∧
  (∀ i j (h : i ≤ j) (a : S.Fiber i),
    S.stageMap j (S.embed i j h a) = S.stageMap i a) ∧
  DenseRange (fun p : Σ i, S.Fiber i => S.stageMap p.1 p.2) ∧
  CompleteSpace S.Completion ∧
  (∀ x : S.Completion, ‖star x * x‖ = ‖x‖ * ‖x‖)

theorem directedCStarCompletionGoal : S.DirectedCStarCompletionGoal := by
  exact ⟨S.algebraicMap_norm, fun _ => CStarRing.norm_star_mul_self,
    S.stageMap_injective, S.stageMap_isometry, S.stageMap_coherent,
    S.stageMap_dense, S.completion_complete, fun _ => CStarRing.norm_star_mul_self⟩

end IsometricStarSystem

/-- The generic construction specializes to the original repeat-tail finite fibers. -/
def repeatTailSystem : IsometricStarSystem ℕ where
  Fiber := ReconstructionLimits.FiniteFiber
  fiberCStar := fun _ => inferInstance
  embed := ReconstructionLimits.stageEmbed
  embed_self := ReconstructionLimits.stageEmbed_self
  embed_comp := by
    intro i j k hij hjk a
    exact ReconstructionLimits.stageEmbed_comp hij hjk a
  embed_norm := by
    intro i j h a
    exact ReconstructionLimits.stageEmbed_norm h a

theorem core_norm_eq_limitSize (x : repeatTailSystem.AlgebraicLimit) :
    ‖x‖ = ReconstructionLimits.limitSize x := by
  refine DirectLimit.induction (f := fun i j h => repeatTailSystem.embed i j h) ?_ x
  intro i a
  rfl

theorem core_star_eq_limitAdjoint (x : repeatTailSystem.AlgebraicLimit) :
    star x = ReconstructionLimits.limitAdjoint x := by
  refine DirectLimit.induction (f := fun i j h => repeatTailSystem.embed i j h) ?_ x
  intro i a
  rfl

/-- The concrete completion uses the norm already defined on the existing algebraic limit. -/
abbrev FiberCompletion := repeatTailSystem.Completion

/-- The original algebraic limit embeds into the specialized C* completion. -/
def coreIntoCompletion : repeatTailSystem.AlgebraicLimit →⋆ₐ[ℂ] FiberCompletion :=
  repeatTailSystem.algebraicIntoCompletion

theorem core_stage_completion (n : ℕ) (a : ReconstructionLimits.FiniteFiber n) :
    repeatTailSystem.stageMap n a =
      coreIntoCompletion (ReconstructionLimits.intoLimit n a) := by
  rfl

/-- The specialization identifies the generic norm and adjoint with the original concrete maps. -/
def RepeatTailCompletionGoal : Prop :=
  repeatTailSystem.DirectedCStarCompletionGoal ∧
  (∀ x : repeatTailSystem.AlgebraicLimit, ‖x‖ = ReconstructionLimits.limitSize x) ∧
  (∀ x : repeatTailSystem.AlgebraicLimit,
    star x = ReconstructionLimits.limitAdjoint x) ∧
  (∀ n (a : ReconstructionLimits.FiniteFiber n),
    repeatTailSystem.stageMap n a =
      coreIntoCompletion (ReconstructionLimits.intoLimit n a))

theorem repeatTailCompletionGoal : RepeatTailCompletionGoal := by
  exact ⟨repeatTailSystem.directedCStarCompletionGoal,
    core_norm_eq_limitSize, core_star_eq_limitAdjoint, core_stage_completion⟩


namespace PositiveFunctional

variable {A : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (ω : A →ₚ[ℂ] ℂ)

/-- The positive functional determines its sesquilinear form. -/
def form (a b : A) : ℂ := ω (star a * b)

theorem form_conj_symm (a b : A) :
    star (form ω b a) = form ω a b := by
  change star (ω (star b * a)) = ω (star a * b)
  rw [← map_star, star_mul, star_star]

theorem form_nonneg (a : A) : 0 ≤ form ω a a :=
  ω.map_nonneg (star_mul_self_nonneg a)

theorem form_re_nonneg (a : A) : 0 ≤ (form ω a a).re :=
  (Complex.nonneg_iff.mp (form_nonneg ω a)).1

theorem form_im_zero (a : A) : (form ω a a).im = 0 :=
  (Complex.nonneg_iff.mp (form_nonneg ω a)).2.symm

omit [StarOrderedRing A] in
theorem form_add_left (a b c : A) :
    form ω (a + b) c = form ω a c + form ω b c := by
  change ω (star (a + b) * c) = ω (star a * c) + ω (star b * c)
  rw [star_add, add_mul, map_add]

omit [StarOrderedRing A] in
theorem form_add_right (a b c : A) :
    form ω a (b + c) = form ω a b + form ω a c := by
  change ω (star a * (b + c)) = ω (star a * b) + ω (star a * c)
  rw [mul_add, map_add]

omit [StarOrderedRing A] in
theorem form_smul_left (r : ℂ) (a b : A) :
    form ω (r • a) b = star r * form ω a b := by
  change ω (star (r • a) * b) = star r * ω (star a * b)
  rw [star_smul, smul_mul_assoc, map_smul, smul_eq_mul]

omit [StarOrderedRing A] in
theorem form_smul_right (r : ℂ) (a b : A) :
    form ω a (r • b) = r * form ω a b := by
  change ω (star a * (r • b)) = r * ω (star a * b)
  rw [mul_smul_comm, map_smul, smul_eq_mul]

omit [StarOrderedRing A] in
theorem form_sub_left (a b c : A) :
    form ω (a - b) c = form ω a c - form ω b c := by
  change ω (star (a - b) * c) = ω (star a * c) - ω (star b * c)
  rw [star_sub, sub_mul, map_sub]

omit [StarOrderedRing A] in
theorem form_sub_right (a b c : A) :
    form ω a (b - c) = form ω a b - form ω a c := by
  change ω (star a * (b - c)) = ω (star a * b) - ω (star a * c)
  rw [mul_sub, map_sub]

omit [StarOrderedRing A] in
theorem form_zero_left (a : A) : form ω 0 a = 0 := by
  change ω (star (0 : A) * a) = 0
  rw [star_zero, zero_mul, map_zero]

omit [StarOrderedRing A] in
theorem form_zero_right (a : A) : form ω a 0 = 0 := by
  change ω (star a * 0) = 0
  rw [mul_zero, map_zero]

/-- The pre-inner-product laws follow from positivity and linearity of the functional. -/
def formCore : PreInnerProductSpace.Core ℂ A where
  inner := form ω
  conj_inner_symm := form_conj_symm ω
  re_inner_nonneg := form_re_nonneg ω
  add_left := form_add_left ω
  smul_left := fun a b r => form_smul_left ω r a b

theorem form_cauchySchwarz (a b : A) :
    ‖form ω a b‖ ^ 2 ≤ (form ω a a).re * (form ω b b).re := by
  letI : PreInnerProductSpace.Core ℂ A := formCore ω
  have h := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) a b
  change ‖form ω a b‖ * ‖form ω b a‖ ≤
    (form ω a a).re * (form ω b b).re at h
  have hn : ‖form ω b a‖ = ‖form ω a b‖ := by
    rw [← form_conj_symm ω b a, norm_star]
  simpa only [hn, pow_two] using h

theorem form_null_left {a : A} (ha : form ω a a = 0) (b : A) :
    form ω a b = 0 := by
  have h := form_cauchySchwarz ω a b
  rw [ha, Complex.zero_re, zero_mul] at h
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (form ω a b)]

theorem form_null_right {b : A} (hb : form ω b b = 0) (a : A) :
    form ω a b = 0 := by
  rw [← form_conj_symm ω a b, form_null_left ω hb a, star_zero]

theorem form_re_eq_zero_iff (a : A) :
    (form ω a a).re = 0 ↔ form ω a a = 0 := by
  constructor
  · intro h
    exact Complex.ext h (form_im_zero ω a)
  · intro h
    rw [h, Complex.zero_re]

/-- The state seminorm is the square root of the positive quadratic form. -/
def seminorm (a : A) : ℝ := Real.sqrt (form ω a a).re

omit [StarOrderedRing A] in
theorem seminorm_nonneg (a : A) : 0 ≤ seminorm ω a :=
  Real.sqrt_nonneg _

theorem seminorm_sq (a : A) :
    seminorm ω a ^ 2 = (form ω a a).re :=
  Real.sq_sqrt (form_re_nonneg ω a)

theorem seminorm_eq_zero_iff (a : A) :
    seminorm ω a = 0 ↔ form ω a a = 0 := by
  rw [seminorm, Real.sqrt_eq_zero (form_re_nonneg ω a)]
  exact form_re_eq_zero_iff ω a

theorem form_left_mul_bound (a b : A) :
    (form ω (a * b) (a * b)).re ≤ ‖a‖ ^ 2 * (form ω b b).re := by
  have hle := CStarAlgebra.conjugate_le_norm_smul (a := b) (b := star a * a)
    (IsSelfAdjoint.star_mul_self a)
  have h : ω (star b * (star a * a) * b) ≤ ω (‖star a * a‖ • (star b * b)) := ω.monotone' hle
  rw [← Complex.coe_smul, map_smul, smul_eq_mul] at h
  have hr := (Complex.le_def.mp h).1
  rw [Complex.re_ofReal_mul, CStarRing.norm_star_mul_self] at hr
  change (ω (star (a * b) * (a * b))).re ≤
    ‖a‖ ^ 2 * (ω (star b * b)).re
  simpa only [star_mul, mul_assoc, pow_two] using hr

theorem seminorm_left_mul_le (a b : A) :
    seminorm ω (a * b) ≤ ‖a‖ * seminorm ω b := by
  have h := form_left_mul_bound ω a b
  rw [← seminorm_sq ω (a * b), ← seminorm_sq ω b] at h
  have hn := mul_nonneg (norm_nonneg a) (seminorm_nonneg ω b)
  nlinarith [seminorm_nonneg ω (a * b)]

theorem norm_apply_le (hω : ω 1 = 1) (a : A) : ‖ω a‖ ≤ ‖a‖ := by
  have hcs := form_cauchySchwarz ω (1 : A) a
  simp only [form, star_one, one_mul, hω, Complex.one_re] at hcs
  have hpos := PositiveLinearMap.norm_apply_le_of_nonneg ω (star a * a)
    (star_mul_self_nonneg a)
  rw [hω, norm_one, one_mul, CStarRing.norm_star_mul_self] at hpos
  have hre := Complex.re_le_norm (ω (star a * a))
  nlinarith [norm_nonneg (ω a), norm_nonneg a]

/-- The null submodule has exactly the zero-quadratic-form elements as its carrier. -/
def nullSubmodule : Submodule ℂ A where
  carrier := {a | form ω a a = 0}
  zero_mem' := form_zero_left ω 0
  add_mem' := by
    intro a b ha hb
    have ha' : form ω a a = 0 := ha
    have hb' : form ω b b = 0 := hb
    change form ω (a + b) (a + b) = 0
    simp only [form_add_left, form_add_right, ha', hb', form_null_left ω ha' b,
      form_null_left ω hb' a, add_zero]
  smul_mem' := by
    intro r a ha
    change form ω (r • a) (r • a) = 0
    rw [form_smul_left, form_smul_right, ha, mul_zero, mul_zero]

theorem mem_nullSubmodule (a : A) :
    a ∈ nullSubmodule ω ↔ form ω a a = 0 :=
  Iff.rfl

theorem mem_nullSubmodule_iff_seminorm (a : A) :
    a ∈ nullSubmodule ω ↔ seminorm ω a = 0 :=
  (seminorm_eq_zero_iff ω a).symm

theorem null_left_mul (a : A) {b : A} (hb : b ∈ nullSubmodule ω) :
    a * b ∈ nullSubmodule ω := by
  have hb' := (mem_nullSubmodule_iff_seminorm ω b).mp hb
  apply (mem_nullSubmodule_iff_seminorm ω (a * b)).mpr
  have h := seminorm_left_mul_le ω a b
  rw [hb', mul_zero] at h
  exact le_antisymm h (seminorm_nonneg ω (a * b))

/-- The zero-seminorm subspace is also a left ideal in the original algebra. -/
def nullIdeal : Ideal A where
  carrier := {a | form ω a a = 0}
  zero_mem' := (nullSubmodule ω).zero_mem
  add_mem' := (nullSubmodule ω).add_mem
  smul_mem' := fun a _ hb => null_left_mul ω a hb

theorem mem_nullIdeal_iff (a : A) :
    a ∈ nullIdeal ω ↔ seminorm ω a = 0 :=
  (seminorm_eq_zero_iff ω a).symm

theorem form_congr {a a' b b' : A}
    (ha : a - a' ∈ nullSubmodule ω) (hb : b - b' ∈ nullSubmodule ω) :
    form ω a b = form ω a' b' := by
  have hleft := form_null_left ω ha b
  have hright := form_null_right ω hb a'
  rw [form_sub_left] at hleft
  rw [form_sub_right] at hright
  exact (sub_eq_zero.mp hleft).trans (sub_eq_zero.mp hright)

/-- The positive-form goal records the derived bounds and the exact null carrier. -/
def PositiveFormBoundGoal : Prop :=
  (∀ a b : A,
    ‖form ω a b‖ ^ 2 ≤ (form ω a a).re * (form ω b b).re) ∧
  (∀ a : A, a ∈ nullSubmodule ω ↔ seminorm ω a = 0) ∧
  (∀ a b : A, b ∈ nullSubmodule ω → a * b ∈ nullSubmodule ω) ∧
  (∀ a b : A, seminorm ω (a * b) ≤ ‖a‖ * seminorm ω b) ∧
  (∀ a a' b b' : A, a - a' ∈ nullSubmodule ω →
    b - b' ∈ nullSubmodule ω → form ω a b = form ω a' b') ∧
  (ω 1 = 1 → ∀ a : A, ‖ω a‖ ≤ ‖a‖)

theorem positiveFormBoundGoal : PositiveFormBoundGoal ω := by
  exact ⟨form_cauchySchwarz ω, mem_nullSubmodule_iff_seminorm ω,
    fun a _ hb => null_left_mul ω a hb, seminorm_left_mul_le ω,
    fun _ _ _ _ ha hb => form_congr ω ha hb, norm_apply_le ω⟩

end PositiveFunctional

namespace IsometricStarSystem

variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable (S : IsometricStarSystem ι)

/-- The completion carries the spectral order of its constructed C* algebra. -/
instance completionOrder : PartialOrder S.Completion :=
  CStarAlgebra.spectralOrder S.Completion

instance completionStarOrderedRing : StarOrderedRing S.Completion :=
  CStarAlgebra.spectralOrderedRing S.Completion

end IsometricStarSystem

/-- The supplied family consists of normalized positive linear maps with stage compatibility. -/
structure CompatibleStateFamily {ι : Type u} [Preorder ι] (S : IsometricStarSystem ι)
    [∀ i, PartialOrder (S.Fiber i)] where
  state : ∀ i, S.Fiber i →ₚ[ℂ] ℂ
  normalized : ∀ i, state i 1 = 1
  compatible : ∀ i j (h : i ≤ j) a, state j (S.embed i j h a) = state i a

namespace CompatibleStateFamily

variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable {S : IsometricStarSystem ι}
variable [∀ i, PartialOrder (S.Fiber i)] [∀ i, StarOrderedRing (S.Fiber i)]
variable (Ω : CompatibleStateFamily S)

/-- The compatible family descends through the actual algebraic direct limit. -/
def algebraic : S.AlgebraicLimit →ₗ[ℂ] ℂ :=
  DirectLimit.Module.lift ℂ ι S.Fiber (fun i j h => S.embed i j h)
    (fun i => (Ω.state i).toLinearMap) Ω.compatible

theorem algebraic_on_stage (i : ι) (a : S.Fiber i) :
    Ω.algebraic (S.algebraicMap i a) = Ω.state i a := rfl

theorem algebraic_representatives {i j : ι} {a : S.Fiber i} {b : S.Fiber j}
    (h : S.algebraicMap i a = S.algebraicMap j b) :
    Ω.state i a = Ω.state j b := by
  exact congrArg Ω.algebraic h

theorem algebraic_one : Ω.algebraic 1 = 1 := by
  let i : ι := Classical.arbitrary ι
  rw [← map_one (S.algebraicMap i), algebraic_on_stage, Ω.normalized]

theorem algebraic_square_nonneg (x : S.AlgebraicLimit) :
    0 ≤ Ω.algebraic (star x * x) := by
  refine DirectLimit.induction (f := fun i j h => S.embed i j h) ?_ x
  intro i a
  change 0 ≤ Ω.algebraic (star (S.algebraicMap i a) * S.algebraicMap i a)
  rw [← map_star, ← map_mul, algebraic_on_stage]
  exact (Ω.state i).map_nonneg (star_mul_self_nonneg a)

theorem algebraic_norm_apply_le (x : S.AlgebraicLimit) :
    ‖Ω.algebraic x‖ ≤ ‖x‖ := by
  refine DirectLimit.induction (f := fun i j h => S.embed i j h) ?_ x
  intro i a
  change ‖Ω.algebraic (S.algebraicMap i a)‖ ≤ ‖S.algebraicMap i a‖
  rw [algebraic_on_stage, S.algebraicMap_norm]
  exact PositiveFunctional.norm_apply_le (Ω.state i) (Ω.normalized i) a

/-- The derived norm-one bound supplies continuity on the algebraic limit. -/
def algebraicContinuous : S.AlgebraicLimit →L[ℂ] ℂ :=
  Ω.algebraic.mkContinuous 1
    (fun x => by simpa only [one_mul] using Ω.algebraic_norm_apply_le x)

theorem algebraicContinuous_apply (x : S.AlgebraicLimit) :
    Ω.algebraicContinuous x = Ω.algebraic x := rfl

/-- The functional extends through the specified uniform completion. -/
def completionValue : S.Completion → ℂ :=
  UniformSpace.Completion.extension Ω.algebraicContinuous

theorem completionValue_continuous : Continuous Ω.completionValue :=
  UniformSpace.Completion.continuous_extension

theorem completionValue_on_algebraic (a : S.AlgebraicLimit) :
    Ω.completionValue (S.algebraicIntoCompletion a) = Ω.algebraic a :=
  UniformSpace.Completion.extension_coe Ω.algebraicContinuous.uniformContinuous a

theorem completionValue_add (x y : S.Completion) :
    Ω.completionValue (x + y) = Ω.completionValue x + Ω.completionValue y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq
      (Ω.completionValue_continuous.comp (continuous_fst.add continuous_snd))
      ((Ω.completionValue_continuous.comp continuous_fst).add
        (Ω.completionValue_continuous.comp continuous_snd))
  · intro a b
    change Ω.completionValue
      ((S.algebraicIntoCompletion a) + S.algebraicIntoCompletion b) =
      Ω.completionValue (S.algebraicIntoCompletion a) +
        Ω.completionValue (S.algebraicIntoCompletion b)
    rw [← map_add, completionValue_on_algebraic, completionValue_on_algebraic,
      completionValue_on_algebraic, map_add]

theorem completionValue_smul (c : ℂ) (x : S.Completion) :
    Ω.completionValue (c • x) = c • Ω.completionValue x := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      (Ω.completionValue_continuous.comp (continuous_id.const_smul c))
      (Ω.completionValue_continuous.const_smul c)
  · intro a
    change Ω.completionValue (c • S.algebraicIntoCompletion a) =
      c • Ω.completionValue (S.algebraicIntoCompletion a)
    rw [← map_smul, completionValue_on_algebraic, completionValue_on_algebraic, map_smul]

/-- The extension is a constructed continuous complex-linear functional. -/
def completionLinear : S.Completion →L[ℂ] ℂ where
  toFun := Ω.completionValue
  map_add' := Ω.completionValue_add
  map_smul' := Ω.completionValue_smul
  cont := Ω.completionValue_continuous

theorem completionLinear_on_algebraic (a : S.AlgebraicLimit) :
    Ω.completionLinear (S.algebraicIntoCompletion a) = Ω.algebraic a :=
  Ω.completionValue_on_algebraic a

theorem completionLinear_on_stage (i : ι) (a : S.Fiber i) :
    Ω.completionLinear (S.stageMap i a) = Ω.state i a := by
  exact Ω.completionLinear_on_algebraic (S.algebraicMap i a)

theorem completionLinear_one : Ω.completionLinear 1 = 1 := by
  rw [← map_one S.algebraicIntoCompletion, completionLinear_on_algebraic, algebraic_one]

theorem completionLinear_norm_apply_le (x : S.Completion) :
    ‖Ω.completionLinear x‖ ≤ ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le Ω.completionLinear.continuous.norm continuous_norm) ?_
  intro a
  change ‖Ω.completionLinear (S.algebraicIntoCompletion a)‖ ≤
    ‖(a : UniformSpace.Completion S.AlgebraicLimit)‖
  rw [completionLinear_on_algebraic, UniformSpace.Completion.norm_coe]
  exact Ω.algebraic_norm_apply_le a

theorem completionLinear_square_nonneg (x : S.Completion) :
    0 ≤ Ω.completionLinear (star x * x) := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le continuous_const
      (Ω.completionLinear.continuous.comp (continuous_star.mul continuous_id))) ?_
  intro a
  change 0 ≤ Ω.completionLinear
    (star (S.algebraicIntoCompletion a) * S.algebraicIntoCompletion a)
  rw [← map_star, ← map_mul, completionLinear_on_algebraic]
  exact Ω.algebraic_square_nonneg a

theorem completionLinear_nonneg (x : S.Completion) (hx : 0 ≤ x) :
    0 ≤ Ω.completionLinear x := by
  rw [StarOrderedRing.nonneg_iff] at hx
  refine AddSubmonoid.closure_induction ?_ ?_ ?_ hx
  · rintro _ ⟨a, rfl⟩
    exact Ω.completionLinear_square_nonneg a
  · rw [map_zero]
  · intro a b _ _ ha hb
    rw [map_add]
    exact add_nonneg ha hb

/-- Positivity of the continuous extension follows from its values on squares. -/
def completionState : S.Completion →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ Ω.completionLinear.toLinearMap Ω.completionLinear_nonneg

theorem completionState_apply (x : S.Completion) :
    Ω.completionState x = Ω.completionLinear x := rfl

theorem completionState_on_stage (i : ι) (a : S.Fiber i) :
    Ω.completionState (S.stageMap i a) = Ω.state i a :=
  Ω.completionLinear_on_stage i a

theorem completionState_one : Ω.completionState 1 = 1 :=
  Ω.completionLinear_one

theorem completionState_norm_apply_le (x : S.Completion) :
    ‖Ω.completionState x‖ ≤ ‖x‖ :=
  Ω.completionLinear_norm_apply_le x

theorem completionLinear_norm : ‖Ω.completionLinear‖ = 1 := by
  have h01 : (0 : S.Completion) ≠ 1 := by
    intro h
    have h' := congrArg Ω.completionLinear h
    rw [map_zero, completionLinear_one] at h'
    exact zero_ne_one h'
  letI : Nontrivial S.Completion := ⟨⟨0, 1, h01⟩⟩
  apply le_antisymm
  · apply Ω.completionLinear.opNorm_le_bound zero_le_one
    intro x
    rw [one_mul]
    exact Ω.completionLinear_norm_apply_le x
  · simpa only [completionLinear_one, norm_one, mul_one] using
      Ω.completionLinear.le_opNorm (1 : S.Completion)

theorem completionLinear_unique (f : S.Completion →L[ℂ] ℂ)
    (hf : ∀ i (a : S.Fiber i), f (S.stageMap i a) = Ω.state i a) :
    f = Ω.completionLinear := by
  apply ContinuousLinearMap.ext
  intro x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq f.continuous Ω.completionLinear.continuous) ?_
  intro a
  refine DirectLimit.induction (f := fun i j h => S.embed i j h) ?_ a
  intro i b
  change f (S.stageMap i b) = Ω.completionLinear (S.stageMap i b)
  rw [hf, completionLinear_on_stage]

/-- Compatible normalized positive states have one continuous normalized positive limit extension. -/
def CompatiblePositiveLimitGoal : Prop :=
  (∀ i j (a : S.Fiber i) (b : S.Fiber j),
    S.algebraicMap i a = S.algebraicMap j b → Ω.state i a = Ω.state j b) ∧
  (∀ x : S.AlgebraicLimit, 0 ≤ Ω.algebraic (star x * x)) ∧
  (∀ x : S.AlgebraicLimit, ‖Ω.algebraic x‖ ≤ ‖x‖) ∧
  Ω.algebraic 1 = 1 ∧
  (∀ i (a : S.Fiber i), Ω.completionState (S.stageMap i a) = Ω.state i a) ∧
  Ω.completionState 1 = 1 ∧
  (∀ x : S.Completion, 0 ≤ x → 0 ≤ Ω.completionState x) ∧
  (∀ x : S.Completion, ‖Ω.completionState x‖ ≤ ‖x‖) ∧
  ‖Ω.completionLinear‖ = 1 ∧
  (∀ f : S.Completion →L[ℂ] ℂ,
    (∀ i (a : S.Fiber i), f (S.stageMap i a) = Ω.state i a) →
      f = Ω.completionLinear)

theorem compatiblePositiveLimitGoal : CompatiblePositiveLimitGoal Ω := by
  exact ⟨fun _ _ _ _ h => Ω.algebraic_representatives h,
    Ω.algebraic_square_nonneg, Ω.algebraic_norm_apply_le, Ω.algebraic_one,
    Ω.completionState_on_stage, Ω.completionState_one,
    fun _ hx => Ω.completionState.map_nonneg hx,
    Ω.completionState_norm_apply_le, Ω.completionLinear_norm, Ω.completionLinear_unique⟩

end CompatibleStateFamily

end ReconstructionLimitCompletion
end OperatorKO7.Meta.BoundaryObserver
