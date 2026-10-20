import OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapDPExchange
import OperatorKO7.Meta.InformationalIncompleteness.EqWDiagonalDeficit
import OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
import OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity
import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorRoleGate

set_option autoImplicit false

/-!
# Role-split law

Elementary schema over a carrier `D` with a value map `v : D → V`. The content
is the instances and the bit count, not the schema itself.

With a value map and a point pair: `p = q` refuses every coordinate; the middle
case `v p = v q ∧ p ≠ q` is a role split, a separator exists, and every
separator is exogenous to `v`.

The free-recursor instance is stated at `Occ RecursorTerm` on the located generator
occurrences `generatorFrame K` and `generatorActive K` of the successor output
(`freeRecursor_located_trichotomy`, `freeRecursor_located_two_actions`), with the
activity predicate as the separator and equal to the extraction channel
(`freeRecursor_activity_eq_dpChannel`).
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
instance is the case `α = Unit`, the KO7 kernel instance is the case `α = Trace`, and the
free-recursor instance at the located occurrences of the successor output is the case
`α = RecursorTerm` at the generator (`freeRecursorTwoActionBoundary_eq_payload` below). -/

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

/-! ## The free-recursor instance at the located occurrences

The successor output `G(s, F(b, s, n))` of one root step `FreeRecursorStep K.source K.output` of
the free recursor carries its generator at the paths `[0]` (frame copy) and `[1, 1]` (active copy)
(`FreeRecursorRoleGate.generatorOccurrence`). Read as points of `Occ RecursorTerm`, the two located
occurrences are `generatorFrame K` and `generatorActive K`. With the value projection onto payload
terms, the trichotomy at this pair lands in its middle case; the activity predicate is the
separator, it equals the extraction channel `actualDPChannel` computed from the actual output
branches, and it does not factor through the value projection. The boundary object at this pair is
the payload-generic boundary of this module at the payload `K.generator`. -/

section FreeRecursorInstance

open OperatorKO7.Meta.Recursor.DPConfessionLicense (RecursorTerm)
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorRoleGate
  (FreeBoundaryKernel generatorFrame generatorActive generatorValue generatorOccurrence
    generatorPath subtermAt actualDPChannel actualDPChannel_frame actualDPChannel_active)

/-- The two-action boundary of the free recursor at its located generator occurrences.
Proves: no proposition; it packages the value projection `payloadValueProj` on
`Occ RecursorTerm` with the frame point `generatorFrame K` and the active point
`generatorActive K`, which share a value and differ in role.
Does not prove: that the points are located in the output; `freeRecursor_located_two_actions`
proves the paths.
Relation: one root step `FreeRecursorStep K.source K.output` supplies the output; no closure.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: every `FreeBoundaryKernel` `K`. -/
def freeRecursorTwoActionBoundary (K : FreeBoundaryKernel) :
    TwoActionBoundary (Occ RecursorTerm) RecursorTerm where
  value := payloadValueProj
  frame := generatorFrame K
  active := generatorActive K
  sameValue := rfl
  differentRole := occ_frame_ne_active K.generator

/-- Proves: the free-recursor boundary is the payload-generic boundary of this module at the
payload `K.generator`, so every payload-generic lemma applies to the located occurrences.
Does not prove: anything beyond this definitional identity.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only. Scope: every `FreeBoundaryKernel` `K`. -/
theorem freeRecursorTwoActionBoundary_eq_payload (K : FreeBoundaryKernel) :
    freeRecursorTwoActionBoundary K = payloadTwoActionBoundary K.generator := rfl

/-- Proves: the located generator occurrences of the successor output form a role split for the
value projection onto payload terms: equal values, different occurrences.
Does not prove: a role split for any other pair of positions of the output.
Relation: one root step `FreeRecursorStep K.source K.output` supplies the output; no closure.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: every `FreeBoundaryKernel` `K`. -/
theorem freeRecursor_located_roleSplit (K : FreeBoundaryKernel) :
    RoleSplit payloadValueProj (generatorFrame K) (generatorActive K) :=
  ⟨rfl, (freeRecursorTwoActionBoundary K).differentRole⟩

/-- The role-split trichotomy instantiated at the located occurrences.
Proves: at `generatorFrame K` and `generatorActive K` with `payloadValueProj`, the first case of
`boundary_query_trichotomy` (equal points) fails, the middle case (role split) holds, and the
third case (different values) fails.
Does not prove: the trichotomy for other pairs; `boundary_query_trichotomy` is the general law.
Relation: one root step `FreeRecursorStep K.source K.output` supplies the output; no closure.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: every `FreeBoundaryKernel` `K`. -/
theorem freeRecursor_located_trichotomy (K : FreeBoundaryKernel) :
    generatorFrame K ≠ generatorActive K ∧
      RoleSplit payloadValueProj (generatorFrame K) (generatorActive K) ∧
      ¬ payloadValueProj (generatorFrame K) ≠ payloadValueProj (generatorActive K) :=
  ⟨(freeRecursor_located_roleSplit K).2, freeRecursor_located_roleSplit K,
    fun h => h (freeRecursor_located_roleSplit K).1⟩

/-- Proves: on the located occurrences the activity predicate is the extraction channel: for each
role `r`, the activity of the occurrence `(generatorValue K r, r)` equals `actualDPChannel K r`,
the comparison of the containing output branch with the extracted call.
Does not prove: a statement about occurrences outside the output.
Relation: one root step `FreeRecursorStep K.source K.output` and its extracted call; no closure.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: every `FreeBoundaryKernel` `K` and both roles. -/
theorem freeRecursor_activity_eq_dpChannel (K : FreeBoundaryKernel) (r : Role) :
    decide (isActive ((generatorValue K r, r) : Occ RecursorTerm)) = actualDPChannel K r := by
  cases r <;> simp [isActive, actualDPChannel_frame, actualDPChannel_active]

/-- The refuse, lift and exogeneity actions at the located occurrences of the free recursor.
Proves: the frame and active points carry the generator at the output paths `[0]` and `[1, 1]`;
every map that factors through the value projection agrees on them; the activity predicate
separates them; and the activity predicate does not factor through the value projection.
Does not prove: separation by a value-factored map, which the second conjunct refutes.
Relation: one root step `FreeRecursorStep K.source K.output` supplies the output; no closure.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: every `FreeBoundaryKernel` `K`. -/
theorem freeRecursor_located_two_actions (K : FreeBoundaryKernel) :
    subtermAt K.output (generatorPath Role.frame) = some (generatorFrame K).1 ∧
      subtermAt K.output (generatorPath Role.active) = some (generatorActive K).1 ∧
      (∀ {Z : Type*} (f : Occ RecursorTerm → Z),
        ValueFactored payloadValueProj f → f (generatorFrame K) = f (generatorActive K)) ∧
      decide (isActive (generatorFrame K)) ≠ decide (isActive (generatorActive K)) ∧
      ¬ ValueFactored (payloadValueProj (α := RecursorTerm))
        (fun o : Occ RecursorTerm => decide (isActive o)) :=
  ⟨(generatorOccurrence K Role.frame).at_path, (generatorOccurrence K Role.active).at_path,
    fun f hf => (freeRecursorTwoActionBoundary K).refuses_valueFactored f hf,
    by simp [isActive, generatorFrame, generatorActive],
    payload_separator_exogenous K.generator⟩

end FreeRecursorInstance

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
