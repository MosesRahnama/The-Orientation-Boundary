import OperatorKO7.Meta.BoundaryGeneral.PersistentExogeny
import OperatorKO7.Meta.BoundaryGeneral.EchoDeficitBridge
import OperatorKO7.Meta.BoundaryGeneral.EchoLawInstance

/-!
# Structural and quantitative exogeny

`Exogenous E s` records `InformativeAt E s`. `QuantExogenous E post μ ν s` records a nonzero licensed-channel deficit. The persistent predicates require their condition at every `Relation.ReflTransGen R` successor. When the channel-cell weights `ν` sum to one, nonzero deficit implies structural exogeny; the same implication holds for persistent predicates.

Given a nonzero deficit at the source, quantitative persistence holds exactly when no reachable state has zero deficit. A Boolean episode provides a strictness example: the channel reads the object while a point-mass channel weighting gives zero deficit.

Scope: `post`, `μ`, and `ν` remain explicit parameters. Relation: arbitrary one-step `R` on `E.State`. Closure: `Relation.ReflTransGen R`.
Trust: kernel-only. No `sorry`/`admit`/`axiom`/`native_decide`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryGeneral.QuantitativeExogeny

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.BoundaryGeneral.EchoLaw
open OperatorKO7.Meta.BoundaryGeneral.EchoDeficitBridge
open OperatorKO7.Meta.BoundaryGeneral.PersistentExogeny
open OperatorKO7.Meta.BoundaryGeneral.EchoLawInstance

/-! ## Box monotonicity -/

/-- The persistent-license operator is monotone in its predicate. -/
theorem box_mono {α : Type} {R : α → α → Prop} {P Q : α → Prop}
    (hPQ : ∀ x, P x → Q x) {x : α} (h : Box R P x) : Box R Q x :=
  ⟨hPQ x h.holds, fun y hy => hPQ y (h.persists y hy)⟩

/-! ## The quantitative license -/

variable {E : Episode} {X : Type} [Fintype X] [Fintype E.Object]

/-- Quantitative exogeny means that the licensed-channel deficit at `s` is nonzero. -/
def QuantExogenous (E : Episode) {X : Type} [Fintype X] [Fintype E.Object]
    (post : E.Answer → X → Real) (μ : Fin 1 → Real) (ν : Fin 1 → E.Object → Real)
    (s : E.State) : Prop :=
  deficit μ ν (channelConditional E post s) ≠ 0

/-- Persistent quantitative exogeny means nonzero licensed deficit at `s` and every reachable state. -/
def PersistentQuantExogenous (E : Episode) {X : Type} [Fintype X] [Fintype E.Object]
    (post : E.Answer → X → Real) (μ : Fin 1 → Real) (ν : Fin 1 → E.Object → Real)
    (R : E.State → E.State → Prop) (s : E.State) : Prop :=
  Box R (QuantExogenous E post μ ν) s

/-- A nonzero licensed deficit fails to persist exactly when some reachable state has zero deficit. -/
theorem quant_license_expiry_iff_reachable_zero_gain
    (post : E.Answer → X → Real) (μ : Fin 1 → Real) (ν : Fin 1 → E.Object → Real)
    {R : E.State → E.State → Prop} {s : E.State}
    (hs : QuantExogenous E post μ ν s) :
    ¬ PersistentQuantExogenous E post μ ν R s ↔
      ∃ y, Relation.ReflTransGen R s y ∧
        deficit μ ν (channelConditional E post y) = 0 := by
  constructor
  · intro hnot
    refine Classical.byContradiction (fun hno => ?_)
    refine hnot ⟨hs, fun y hy => ?_⟩
    intro hzero
    exact hno ⟨y, hy, hzero⟩
  · rintro ⟨y, hy, hzero⟩ hbox
    exact hbox.persists y hy hzero

/-! ## The quantitative license refines the structural one -/

/-- With normalized channel-cell weights and a fixed object baseline, nonzero licensed deficit implies that the channel reads the object. -/
theorem quantExogenous_imp_exogenous
    (post : E.Answer → X → Real) (μ : Fin 1 → Real) (ν : Fin 1 → E.Object → Real)
    (o₀ : E.Object) (hν1 : ∀ w, ∑ c, ν w c = 1)
    {s : E.State} (h : QuantExogenous E post μ ν s) : Exogenous E s :=
  positive_deficit_forces_informative_channel post s o₀ μ ν hν1 h

/-- The refinement lifts to the persistent form. -/
theorem persistentQuant_imp_persistent
    (post : E.Answer → X → Real) (μ : Fin 1 → Real) (ν : Fin 1 → E.Object → Real)
    (o₀ : E.Object) (hν1 : ∀ w, ∑ c, ν w c = 1)
    {R : E.State → E.State → Prop} {s : E.State}
    (h : PersistentQuantExogenous E post μ ν R s) : PersistentExogenous E R s :=
  box_mono (fun _ hx => quantExogenous_imp_exogenous post μ ν o₀ hν1 hx) h

/-! ## The containment is strict -/

/-- If all channel-cell weight is on one cell, the licensed deficit is zero for every channel conditional. -/
theorem deficit_eq_zero_of_pointMass_weights
    {W Cn Xt : Type} [Fintype W] [Fintype Cn] [Fintype Xt] [DecidableEq Cn]
    (μ : W → Real) (c₀ : Cn) (r : W → Cn → Xt → Real) :
    deficit μ (fun _ => pointMass c₀) r = 0 := by
  unfold deficit condEntropyDirect condEntropyLicensed
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero (fun w _ => ?_)
  have hmix : (fun x => ∑ c, pointMass c₀ c * r w c x) = r w c₀ := by
    funext x
    refine Finset.sum_eq_single_of_mem c₀ (Finset.mem_univ c₀) (fun b _ hb => ?_) |>.trans ?_
    · simp [pointMass, hb]
    · simp [pointMass]
  have hlic : (∑ c, pointMass c₀ c * H (r w c)) = H (r w c₀) := by
    refine Finset.sum_eq_single_of_mem c₀ (Finset.mem_univ c₀) (fun b _ hb => ?_) |>.trans ?_
    · simp [pointMass, hb]
    · simp [pointMass]
  rw [hmix, hlic]
  ring

/-- The comparator episode's object carrier is the Boolean probe, so it is
finite. Stated as an instance because structure projection blocks the search. -/
instance eqwEpisodeObjectFintype (W : Type) [DecidableEq W] :
    Fintype (eqwEpisode W).Object :=
  inferInstanceAs (Fintype Bool)

/-- The same carrier has decidable equality. -/
instance eqwEpisodeObjectDecEq (W : Type) [DecidableEq W] :
    DecidableEq (eqwEpisode W).Object :=
  inferInstanceAs (DecidableEq Bool)

/-- At the off-diagonal state, the channel reads the object. A point-mass channel weighting gives zero deficit, so structural exogeny holds while quantitative exogeny fails. -/
theorem exogenous_without_quantExogenous
    (post : Bool → Fin 2 → Real) :
    Exogenous (eqwEpisode Bool) (true, false) ∧
      ¬ QuantExogenous (eqwEpisode Bool) (X := Fin 2) post (fun _ => 1)
          (fun _ => pointMass false) (true, false) := by
  refine ⟨eqwEpisode_informative_off_diagonal (by decide), ?_⟩
  unfold QuantExogenous
  rw [deficit_eq_zero_of_pointMass_weights]
  exact fun h => h rfl

/-! ## Pointwise implication and strictness -/

/-- The theorem proves pointwise refinement under normalized channel-cell weights and gives a structural state with zero licensed deficit. -/
theorem quantitative_exogeny_law (post : Bool → Fin 2 → Real) :
    (∀ (F : Episode) [Fintype F.Object] (p : F.Answer → Fin 2 → Real)
      (μ : Fin 1 → Real) (ν : Fin 1 → F.Object → Real),
        F.Object → (∀ w, ∑ c, ν w c = 1) → ∀ (s : F.State),
          QuantExogenous F p μ ν s → Exogenous F s) ∧
    Exogenous (eqwEpisode Bool) (true, false) ∧
    ¬ QuantExogenous (eqwEpisode Bool) (X := Fin 2) post (fun _ => 1)
        (fun _ => pointMass false) (true, false) :=
  ⟨fun _ _ p μ ν o₀ hν1 _ h => quantExogenous_imp_exogenous p μ ν o₀ hν1 h,
   (exogenous_without_quantExogenous post).1,
   (exogenous_without_quantExogenous post).2⟩

end OperatorKO7.Meta.BoundaryGeneral.QuantitativeExogeny
