import OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapDPExchange
import OperatorKO7.Meta.InformationalIncompleteness.EqWDiagonalDeficit
import OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
import OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity

set_option autoImplicit false

/-!
# Role-split law

Elementary schema over a carrier `D` with a value map `v : D → V`. The content
is the instances and the bit count, not the schema itself.

With a value map and a point pair: `p = q` refuses every coordinate; the middle
case `v p = v q ∧ p ≠ q` is a role split, a separator exists, and every
separator is exogenous to `v`.
-/

open Classical
open OperatorKO7 Trace

namespace OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw

open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
open OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.InformationalIncompleteness.EqWDiagonalDeficit
open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure

/-- A map factors through the value projection. -/
def ValueFactored {D V Z : Type*} (v : D → V) (f : D → Z) : Prop :=
  ∃ g : V → Z, f = g ∘ v

/-- A separator of a value-identified pair cannot factor through `v`. -/
theorem separator_not_valueFactored {D V Z : Type*} (v : D → V) {p q : D}
    {f : D → Z} (hv : v p = v q) (hf : f p ≠ f q) :
    ¬ ValueFactored v f := by
  rintro ⟨g, hg⟩
  have : f p = f q := by
    rw [hg, Function.comp_apply, Function.comp_apply, hv]
  exact hf this

/-- Equality of the pair refuses every coordinate. -/
theorem diagonal_refuses_every_coordinate {D Z : Type*} {p q : D}
    (h : p = q) (f : D → Z) : f p = f q :=
  h ▸ rfl

/-- Value-factored maps are blind to role. -/
theorem value_blind_of_valueFactored {D V Z : Type*} (v : D → V) {p q : D}
    {f : D → Z} (hv : v p = v q) (hf : ValueFactored v f) : f p = f q := by
  rcases hf with ⟨g, hg⟩
  rw [hg, Function.comp_apply, Function.comp_apply, hv]

/-- Query trichotomy: equal, role-split, or value-split. -/
theorem boundary_query_trichotomy {D V : Type*} (v : D → V) (p q : D) :
    p = q ∨ (v p = v q ∧ p ≠ q) ∨ v p ≠ v q := by
  by_cases h : p = q
  · exact Or.inl h
  · by_cases hv : v p = v q
    · exact Or.inr (Or.inl ⟨hv, h⟩)
    · exact Or.inr (Or.inr hv)

/-- The middle case of the trichotomy. -/
def RoleSplit {D V : Type*} (v : D → V) (p q : D) : Prop :=
  v p = v q ∧ p ≠ q

/-- A Bool-valued separator of a pair, using classical equality tests. -/
noncomputable def boolSeparator {D : Type*} (p : D) : D → Bool :=
  fun x => decide (x = p)

theorem boolSeparator_separates {D : Type*} {p q : D} (h : p ≠ q) :
    boolSeparator p p ≠ boolSeparator p q := by
  simp [boolSeparator]
  exact Ne.symm h

/-- One value map and one pair carrying the two boundary actions: every
value-factored coordinate refuses a distinction, while a role separator exists. -/
structure TwoActionBoundary (D V : Type*) where
  value : D → V
  frame : D
  active : D
  sameValue : value frame = value active
  differentRole : frame ≠ active

theorem TwoActionBoundary.refuses_valueFactored {D V : Type*}
    (B : TwoActionBoundary D V) {Z : Type*} (f : D → Z)
    (hf : ValueFactored B.value f) : f B.frame = f B.active :=
  value_blind_of_valueFactored B.value B.sameValue hf

theorem TwoActionBoundary.lifts_separator {D V : Type*}
    (B : TwoActionBoundary D V) :
    ∃ f : D → Bool, f B.frame ≠ f B.active :=
  ⟨boolSeparator B.frame, boolSeparator_separates B.differentRole⟩

theorem TwoActionBoundary.separator_is_exogenous {D V Z : Type*}
    (B : TwoActionBoundary D V) {f : D → Z}
    (hf : f B.frame ≠ f B.active) : ¬ ValueFactored B.value f :=
  separator_not_valueFactored B.value B.sameValue hf

/-- Exact REFUSE/LIFT characterization.  Refusal is tested on the value carrier itself:
the identity value observation is already complete for deciding whether `v p = v q`.  Once that
equality holds, `value_blind_of_valueFactored` upgrades the refusal to every separately chosen
codomain.  This avoids the false universe-level claim that one fixed arbitrary codomain universe
must itself contain a separating observation for every possible value carrier. -/
theorem roleSplit_iff {D V : Type*} (v : D → V) (p q : D) :
    RoleSplit v p q ↔
      (∀ f : D → V, ValueFactored v f → f p = f q) ∧
        ∃ f : D → Bool, f p ≠ f q := by
  constructor
  · intro h
    refine ⟨fun f hf => value_blind_of_valueFactored v h.1 hf, ?_⟩
    exact ⟨boolSeparator p, boolSeparator_separates h.2⟩
  · intro ⟨hblind, ⟨f, hf⟩⟩
    have hne : p ≠ q := by
      intro heq
      exact hf (heq ▸ rfl)
    have hv : v p = v q := by
      have hfact : ValueFactored v v := ⟨id, rfl⟩
      exact hblind v hfact
    exact ⟨hv, hne⟩

/-- Exact refuse/lift/exogeneity characterization of a role split.  The lifted separator and its
failure to factor through the value map are supplied by the same function. -/
theorem roleSplit_iff_refuse_lift_exogenous {D V : Type*} (v : D → V) (p q : D) :
    RoleSplit v p q ↔
      (∀ f : D → V, ValueFactored v f → f p = f q) ∧
        ∃ f : D → Bool, f p ≠ f q ∧ ¬ ValueFactored v f := by
  constructor
  · intro h
    let f := boolSeparator p
    have hsep : f p ≠ f q := boolSeparator_separates h.2
    exact ⟨fun g hg => value_blind_of_valueFactored v h.1 hg,
      ⟨f, hsep, separator_not_valueFactored v h.1 hsep⟩⟩
  · rintro ⟨hblind, ⟨f, hsep, _⟩⟩
    exact (roleSplit_iff v p q).2 ⟨hblind, ⟨f, hsep⟩⟩

/-- Recursor instance: frame and active occurrences of `()` split on role. -/
def valueProj : Occ Unit → Unit := fun o => o.1

theorem recursor_roleSplit :
    RoleSplit valueProj (((), Role.frame) : Occ Unit) ((), Role.active) :=
  ⟨rfl, occ_frame_ne_active ()⟩

def recursorTwoActionBoundary : TwoActionBoundary (Occ Unit) Unit where
  value := valueProj
  frame := ((), Role.frame)
  active := ((), Role.active)
  sameValue := rfl
  differentRole := occ_frame_ne_active ()

/-- The refuse and lift actions are realized on the same two occurrences and
the same value projection. -/
theorem recursor_two_actions_same_boundary :
    (∀ {Z : Type*} (f : Occ Unit → Z),
        ValueFactored valueProj f →
          f ((), Role.frame) = f ((), Role.active))
      ∧ (∃ f : Occ Unit → Bool,
          f ((), Role.frame) ≠ f ((), Role.active))
      ∧ (∀ {Z : Type*} (f : Occ Unit → Z),
          f ((), Role.frame) ≠ f ((), Role.active) →
            ¬ ValueFactored valueProj f) :=
  ⟨fun f hf => recursorTwoActionBoundary.refuses_valueFactored f hf,
    recursorTwoActionBoundary.lifts_separator,
    fun f hf => recursorTwoActionBoundary.separator_is_exogenous (f := f) hf⟩

/-! ## The payload-generic instance

`recursorTwoActionBoundary` lives on `Occ Unit`, where the value projection is constant because
the value type has one element. The law is about a value map that identifies two occurrences of
the *same* payload, so the instance with content is payload-generic: for any carrier `α` and any
payload `a`, the frame and active occurrences of `a` share a value and differ in role. The `Unit`
instance is the case `α = Unit`, and the recursor's own instance is the case `α = Trace` at the
duplicated step argument. -/

/-- Payload-generic role split: two occurrences of the same payload, one frame and one active. -/
def payloadValueProj {α : Type*} : Occ α → α := fun o => o.1

/-- The payload-generic two-action boundary at a payload `a`. -/
def payloadTwoActionBoundary {α : Type*} (a : α) : TwoActionBoundary (Occ α) α where
  value := payloadValueProj
  frame := (a, Role.frame)
  active := (a, Role.active)
  sameValue := rfl
  differentRole := occ_frame_ne_active a

/-- The refuse, lift, and exogeneity actions on the duplicated step argument of the recursor,
stated at `Occ Trace` on an arbitrary payload term. -/
theorem payload_two_actions_same_boundary (s : Trace) :
    (∀ {Z : Type*} (f : Occ Trace → Z),
        ValueFactored payloadValueProj f →
          f (s, Role.frame) = f (s, Role.active))
      ∧ (∃ f : Occ Trace → Bool,
          f (s, Role.frame) ≠ f (s, Role.active))
      ∧ (∀ {Z : Type*} (f : Occ Trace → Z),
          f (s, Role.frame) ≠ f (s, Role.active) →
            ¬ ValueFactored payloadValueProj f) :=
  ⟨fun f hf => (payloadTwoActionBoundary s).refuses_valueFactored f hf,
    (payloadTwoActionBoundary s).lifts_separator,
    fun f hf => (payloadTwoActionBoundary s).separator_is_exogenous (f := f) hf⟩

/-- The activity predicate separates the two occurrences of any payload, and is exogenous to the
value projection at every payload. -/
theorem payload_separator_exogenous {α : Type*} (a : α) :
    ¬ ValueFactored (payloadValueProj (α := α))
        (fun o : Occ α => decide (isActive o)) :=
  separator_not_valueFactored (v := payloadValueProj)
    (p := ((a, Role.frame) : Occ α)) (q := (a, Role.active))
    (f := fun o : Occ α => decide (isActive o))
    rfl (by simp [isActive])

/-- The `Unit` instance is the payload-generic one at `a = ()`. -/
theorem recursorTwoActionBoundary_eq_payload :
    recursorTwoActionBoundary = payloadTwoActionBoundary () := rfl

/-- The payload-generic law is strictly wider than the `Unit` instance: at `Occ Trace` the value
projection is onto, so it separates payloads while remaining blind to role. -/
theorem payloadValueProj_surjective :
    Function.Surjective (payloadValueProj (α := Trace)) :=
  fun a => ⟨(a, Role.frame), rfl⟩

/-- The live activity predicate is a separator exogenous to value. -/
theorem recursor_separator_exogenous :
    ¬ ValueFactored valueProj
        (fun o : Occ Unit => decide (isActive o)) :=
  separator_not_valueFactored (v := valueProj)
    (p := (((), Role.frame) : Occ Unit)) (q := ((), Role.active))
    (f := fun o : Occ Unit => decide (isActive o))
    rfl (by simp [isActive])

/-- Equality-diagonal refuse face: every coordinate agrees on `void = void`,
and the same diagonal is the compiled echo vacuum with fork. -/
theorem eqW_diagonal_refuses {Z : Type*} (f : Trace → Z) : f void = f void :=
  rfl

def eqW_refuse_face :=
  eqW_diagonal_echo_vacuum_with_fork

/-- The LIFT case's price is one bit. -/
def lift_supplies_one_bit :=
  one_bit_dp_exchange

/-- Cross-axis conjunction: the direct orientation grammar must forget payload,
while a natural comparison cannot discriminate across a collapsed pair. The
same-pair role action is `recursor_two_actions_same_boundary` above. -/
theorem boundary_two_actions :
    (∀ e : MeasureExpr,
      OrientsDupStep e.eval ↔ PayloadBlind e.eval ∧ CounterStrict e.eval) ∧
      ∀ {A : Type*} (nil : A) (h : A → A) (t : A → A → A)
        (_hrefl : ∀ z, h z = nil → z = nil) (x y : A) (_hxy : x ≠ y)
        (_hmerge : h x = h y) (_hnat : NaturalUnder h t),
        ¬ IsDiscriminator nil t :=
  ⟨orients_iff_payloadBlind_and_counterStrict,
    @not_discriminator_of_natural_under_noninjective⟩

end OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw
