import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsConditionalConstrained
import OperatorKO7.Meta.Methods.OrientationClosure.FreePolynomialTermination
import Mathlib.Tactic

/-!
# Method rows: semantic frameworks (group W3)

Three Tier C rows whose native language is a semantic framework:
`abstractInterpretationAdmittance` (Cousot and Cousot), `categoricalToposTermination`
(well-founded coalgebras of the powerset functor on `Set`), and `higherOrderLCTRS`
(higher-order constrained rewriting with the value criterion).
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness
open OperatorKO7.Methods.OrientationClosure.InterpretationLaws
open OperatorKO7.Methods.OrientationClosure.PolynomialRegion
open OperatorKO7.Methods.OrientationClosure.FreePolynomialTermination
open OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained

/-! ## Row `abstractInterpretationAdmittance` -/

/-- Native data of `abstractInterpretationAdmittance`: the abstraction of free terms into the
numeric abstract domain, the abstract transitions, the abstract action of one-hole contexts, and
the ranking of the abstract domain. -/
structure abstractInterpretationAdmittanceData where
  /-- Abstraction of free terms. -/
  abst : FreeTerm Nat → Nat
  /-- Abstract transitions, computed from the two rules. -/
  next : Nat → Nat → Prop
  /-- The abstract action of a one-hole context. -/
  push : FreeContext Nat → Nat → Nat
  /-- The ranking of the abstract domain. -/
  rank : Nat → Nat

/-- Laws of `abstractInterpretationAdmittance` (Cousot and Cousot, *Abstract interpretation: a
unified lattice model for static analysis of programs by construction or approximation of
fixpoints*, POPL 1977, and *An abstract interpretation framework for termination*, POPL 2012, the
ranking abstraction): the abstract transitions contain the transition of every instance of the
two free rules, they are closed under the abstract action of one-hole contexts, and the abstract
context action commutes with the abstraction. -/
def abstractInterpretationAdmittanceLaws (M : abstractInterpretationAdmittanceData) : Prop :=
  (∀ b s : FreeTerm Nat, M.next (M.abst (.recur b s .zero)) (M.abst b)) ∧
  (∀ b s n : FreeTerm Nat,
    M.next (M.abst (.recur b s (.succ n))) (M.abst (.wrap s (.recur b s n)))) ∧
  (∀ (C : FreeContext Nat) {a b : Nat}, M.next a b → M.next (M.push C a) (M.push C b)) ∧
  (∀ (C : FreeContext Nat) (t : FreeTerm Nat), M.push C (M.abst t) = M.abst (C.plug t))

/-- The method accepts the free two-rule system when the ranking strictly decreases on every
abstract transition (Cousot and Cousot, POPL 2012, the ranking abstraction). Adapter: the
transitions of the two rules are the abstract transitions named in
`abstractInterpretationAdmittanceLaws`, so acceptance covers the duplicating rule. -/
def abstractInterpretationAdmittanceAccepts (M : abstractInterpretationAdmittanceData) : Prop :=
  ∀ {a b : Nat}, M.next a b → M.rank b < M.rank a

/-- Verdict: escape. Acceptance of the abstraction yields that every contextual step of the free
recursor strictly decreases the abstract ranking of the source term, which is the termination
statement of the generic simulation theorem. -/
def abstractInterpretationAdmittanceResult (M : abstractInterpretationAdmittanceData) : Prop :=
  abstractInterpretationAdmittanceAccepts M ∧
    ∀ {t u : FreeTerm Nat}, ContextStep t u → M.rank (M.abst u) < M.rank (M.abst t)

/-- The root step of the free recursor is an abstract transition under the laws. -/
theorem abstractInterpretationAdmittance_next_of_root
    {M : abstractInterpretationAdmittanceData}
    (hL : abstractInterpretationAdmittanceLaws M) {t u : FreeTerm Nat} (h : RootStep t u) :
    M.next (M.abst t) (M.abst u) := by
  cases h with
  | recurZero => exact hL.1 _ _
  | recurSucc => exact hL.2.1 _ _ _

/-- The context closure of the laws lifts an abstract transition to any one-hole context. -/
theorem abstractInterpretationAdmittance_lift
    {M : abstractInterpretationAdmittanceData}
    (hL : abstractInterpretationAdmittanceLaws M) (C : FreeContext Nat)
    {a b : FreeTerm Nat} (h : M.next (M.abst a) (M.abst b)) :
    M.next (M.abst (C.plug a)) (M.abst (C.plug b)) := by
  have h1 := hL.2.2.1 C h
  rwa [hL.2.2.2 C a, hL.2.2.2 C b] at h1

/-- Simulation: the laws carry every contextual step to an abstract transition. -/
theorem abstractInterpretationAdmittance_next_of_contextStep
    {M : abstractInterpretationAdmittanceData}
    (hL : abstractInterpretationAdmittanceLaws M) {t u : FreeTerm Nat} (h : ContextStep t u) :
    M.next (M.abst t) (M.abst u) := by
  cases h with
  | lift C hroot =>
    exact abstractInterpretationAdmittance_lift hL C
      (abstractInterpretationAdmittance_next_of_root hL hroot)

/-- Soundness: laws plus acceptance yield the ranking decrease on every contextual step. -/
theorem abstractInterpretationAdmittance_sound :
    ∀ M, abstractInterpretationAdmittanceLaws M → abstractInterpretationAdmittanceAccepts M →
      abstractInterpretationAdmittanceResult M := by
  intro M hL hA
  refine ⟨hA, ?_⟩
  intro t u hstep
  exact hA (abstractInterpretationAdmittance_next_of_contextStep hL hstep)

/-- The coupled polynomial interpretation of `PolynomialRegion` at the paper's parameters
`α = 1, β = 2`, read on the numeric abstract domain of the witness. -/
def admittanceInterp : Interpretation Nat := coupledInterpretation 1 2

/-- The witness abstraction: the coupled polynomial value with every variable at zero. -/
def admittanceValue (t : FreeTerm Nat) : Nat := admittanceInterp.eval (fun _ => 0) t

/-- The abstract action of a one-hole context on the numeric domain, the context read as a
function of the hole's value under the witness interpretation. -/
def admittancePush : FreeContext Nat → Nat → Nat
  | .hole, a => a
  | .succ C, a => admittanceInterp.succ (admittancePush C a)
  | .wrapLeft C r, a => admittanceInterp.wrap (admittancePush C a) (admittanceValue r)
  | .wrapRight l C, a => admittanceInterp.wrap (admittanceValue l) (admittancePush C a)
  | .recurBase C s n, a =>
      admittanceInterp.recur (admittancePush C a) (admittanceValue s) (admittanceValue n)
  | .recurStep b C n, a =>
      admittanceInterp.recur (admittanceValue b) (admittancePush C a) (admittanceValue n)
  | .recurCounter b s C, a =>
      admittanceInterp.recur (admittanceValue b) (admittanceValue s) (admittancePush C a)

/-- The witness context action commutes with the abstraction. -/
theorem admittancePush_comm (C : FreeContext Nat) (t : FreeTerm Nat) :
    admittancePush C (admittanceValue t) = admittanceValue (C.plug t) := by
  induction C with
  | hole => rfl
  | succ C ih =>
      simp only [admittancePush, FreeContext.plug]
      rw [ih]
      simp only [admittanceValue, Interpretation.eval]
  | wrapLeft C r ih =>
      simp only [admittancePush, FreeContext.plug]
      rw [ih]
      simp only [admittanceValue, Interpretation.eval]
  | wrapRight l C ih =>
      simp only [admittancePush, FreeContext.plug]
      rw [ih]
      simp only [admittanceValue, Interpretation.eval]
  | recurBase C s n ih =>
      simp only [admittancePush, FreeContext.plug]
      rw [ih]
      simp only [admittanceValue, Interpretation.eval]
  | recurStep b C n ih =>
      simp only [admittancePush, FreeContext.plug]
      rw [ih]
      simp only [admittanceValue, Interpretation.eval]
  | recurCounter b s C ih =>
      simp only [admittancePush, FreeContext.plug]
      rw [ih]
      simp only [admittanceValue, Interpretation.eval]

/-- The witness context action is strictly monotone in the hole value. -/
theorem admittancePush_strict (C : FreeContext Nat) {a b : Nat} (h : a < b) :
    admittancePush C a < admittancePush C b := by
  have hlaws : StrictContextLaws admittanceInterp (fun x y : Nat => x < y) :=
    coupled_strictContextLaws (α := 1) (β := 2) (by decide) (by decide)
  induction C with
  | hole => exact h
  | succ C ih => exact hlaws.succ ih
  | wrapLeft C r ih => exact hlaws.wrapLeft (admittanceValue r) ih
  | wrapRight l C ih => exact hlaws.wrapRight (admittanceValue l) ih
  | recurBase C s n ih => exact hlaws.recurBase (admittanceValue s) (admittanceValue n) ih
  | recurStep b C n ih => exact hlaws.recurStep (admittanceValue b) (admittanceValue n) ih
  | recurCounter b s C ih =>
      exact hlaws.recurCounter (admittanceValue b) (admittanceValue s) ih

/-- Witness: the coupled polynomial interpretation at `α = 1, β = 2`; the abstract transitions are
the strict order on `Nat`, contexts act by the interpretation, and the ranking is the identity. -/
def abstractInterpretationAdmittanceWitness : abstractInterpretationAdmittanceData where
  abst := admittanceValue
  next := fun a b => b < a
  push := admittancePush
  rank := fun a => a

theorem abstractInterpretationAdmittanceWitness_laws :
    abstractInterpretationAdmittanceLaws abstractInterpretationAdmittanceWitness := by
  have hroot : RootRuleOrients admittanceInterp (fun x y : Nat => x < y) :=
    coupled_rootRuleOrients (α := 1) (β := 2) (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b s
    exact hroot.recurZero (admittanceValue b) (admittanceValue s)
  · intro b s n
    exact hroot.recurSucc (admittanceValue b) (admittanceValue s) (admittanceValue n)
  · intro C a b hab
    exact admittancePush_strict C hab
  · intro C t
    exact admittancePush_comm C t

theorem abstractInterpretationAdmittanceWitness_accepts :
    abstractInterpretationAdmittanceAccepts abstractInterpretationAdmittanceWitness := by
  intro a b hab
  exact hab

theorem abstractInterpretationAdmittanceWitness_result :
    abstractInterpretationAdmittanceResult abstractInterpretationAdmittanceWitness :=
  abstractInterpretationAdmittance_sound _ abstractInterpretationAdmittanceWitness_laws
    abstractInterpretationAdmittanceWitness_accepts

/-- A coarse abstraction: every term abstracts to `0`, every abstract pair is a transition, the
context action is constant, and the ranking is the identity. Its abstract graph has the spurious
cycle `0 → 0`, it satisfies the laws, and it fails acceptance. -/
def abstractInterpretationAdmittanceSpuriousCycle : abstractInterpretationAdmittanceData where
  abst := fun _ => 0
  next := fun _ _ => True
  push := fun _ _ => 0
  rank := fun a => a

theorem abstractInterpretationAdmittanceSpuriousCycle_laws :
    abstractInterpretationAdmittanceLaws abstractInterpretationAdmittanceSpuriousCycle := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [abstractInterpretationAdmittanceSpuriousCycle]

theorem abstractInterpretationAdmittanceSpuriousCycle_not_accepts :
    ¬ abstractInterpretationAdmittanceAccepts abstractInterpretationAdmittanceSpuriousCycle := by
  intro h
  exact absurd (h (a := 0) (b := 0) trivial) (Nat.lt_irrefl 0)

/-- The witness with the ranking not linked to the abstract transitions: the constant ranking
keeps the laws and loses acceptance. -/
theorem abstractInterpretationAdmittance_unlinked_rank :
    abstractInterpretationAdmittanceLaws
        { abstractInterpretationAdmittanceWitness with rank := fun _ => 0 } ∧
      ¬ abstractInterpretationAdmittanceAccepts
        { abstractInterpretationAdmittanceWitness with rank := fun _ => 0 } := by
  constructor
  · exact abstractInterpretationAdmittanceWitness_laws
  · intro h
    exact absurd (h (a := 1) (b := 0) (by simp [abstractInterpretationAdmittanceWitness]))
      (Nat.lt_irrefl 0)

/-- The witness successor instance drops the abstraction by the base value plus one. -/
theorem admittanceValue_recurSucc (b s n : FreeTerm Nat) :
    admittanceValue (.recur b s (.succ n)) =
      admittanceValue (.wrap s (.recur b s n)) + (admittanceValue b + 1) := by
  simp only [admittanceValue, admittanceInterp, coupledInterpretation, Interpretation.eval,
    recursorEval, wrapperEval, successorEval]
  ring

/-- **Defining feature.** The coupled polynomial abstraction admits the recursor: both rules are
abstract transitions, the context action is closed and commuting, and the ranking strictly
decreases on every abstract transition, with the successor step dropping by the base value plus
one. A coarse abstraction whose graph has the spurious cycle `0 → 0` satisfies the laws and fails
acceptance, and a ranking not linked to the transitions satisfies the laws and fails acceptance. -/
theorem abstractInterpretationAdmittanceWitness_feature :
    abstractInterpretationAdmittanceResult abstractInterpretationAdmittanceWitness ∧
      (∀ b s n : FreeTerm Nat,
        admittanceValue (.recur b s (.succ n)) =
          admittanceValue (.wrap s (.recur b s n)) + (admittanceValue b + 1)) ∧
      abstractInterpretationAdmittanceSpuriousCycle.next 0 0 ∧
      abstractInterpretationAdmittanceLaws abstractInterpretationAdmittanceSpuriousCycle ∧
      (¬ abstractInterpretationAdmittanceAccepts abstractInterpretationAdmittanceSpuriousCycle) ∧
      (¬ abstractInterpretationAdmittanceAccepts
        { abstractInterpretationAdmittanceWitness with rank := fun _ => 0 }) :=
  ⟨abstractInterpretationAdmittanceWitness_result,
    admittanceValue_recurSucc,
    trivial,
    abstractInterpretationAdmittanceSpuriousCycle_laws,
    abstractInterpretationAdmittanceSpuriousCycle_not_accepts,
    abstractInterpretationAdmittance_unlinked_rank.2⟩

/-- **Mutation.** The foreign abstract graph `b + 1 < a`, which demands a gap of two, everything
else as in the witness: the successor step drops the abstraction by the base value plus one, which
is one when the base is `zero`, so the transition of the duplicating rule lies outside the graph
and the law fails. -/
theorem abstractInterpretationAdmittance_mutation :
    ¬ abstractInterpretationAdmittanceLaws
      { abstractInterpretationAdmittanceWitness with next := fun a b => b + 1 < a } := by
  intro h
  have h1 := h.2.1 FreeTerm.zero FreeTerm.zero FreeTerm.zero
  have h4 : (fun a b : Nat => b + 1 < a)
      (admittanceValue (.recur .zero .zero (.succ .zero)))
      (admittanceValue (.wrap .zero (.recur .zero .zero .zero))) := h1
  have hval : admittanceValue (.recur .zero .zero (.succ .zero)) = 4 := by
    simp only [admittanceValue, admittanceInterp, coupledInterpretation, Interpretation.eval,
      recursorEval, successorEval]
  have hval2 : admittanceValue (.wrap .zero (.recur .zero .zero .zero)) = 3 := by
    simp only [admittanceValue, admittanceInterp, coupledInterpretation, Interpretation.eval,
      recursorEval, wrapperEval]
  rw [hval, hval2] at h4
  omega

/-- **Scope.** Soundness of a ranking abstraction over an arbitrary abstract domain and
concretization. Coverage is explicit: every concrete term must have an abstract representative. -/
def abstractInterpretationAdmittance_scope : Prop :=
  ∀ (β : Type) (γ : β → Set (FreeTerm Nat)) (next : β → β → Prop) (ρ : β → Nat),
    (∀ t : FreeTerm Nat, ∃ a : β, t ∈ γ a) →
      (∀ {a b : β}, next a b → ρ b < ρ a) →
      (∀ ⦃a : β⦄ (t : FreeTerm Nat), t ∈ γ a →
        ∀ u : FreeTerm Nat, ContextStep t u → ∃ b : β, u ∈ γ b ∧ next a b) →
      ∀ t : FreeTerm Nat, Acc (fun u t => ContextStep t u) t

/-- A ranking abstraction for an arbitrary concrete relation. Every concrete object has an
abstract representative, concrete steps are simulated, and abstract steps decrease a natural
rank. -/
structure RankingAbstraction (α β : Type) (R : α → α → Prop) where
  concretizes : β → Set α
  next : β → β → Prop
  rank : β → Nat
  covers : ∀ x, ∃ a, x ∈ concretizes a
  simulates : ∀ {a} {x}, x ∈ concretizes a → ∀ {y}, R x y →
    ∃ b, y ∈ concretizes b ∧ next a b
  decreases : ∀ {a b}, next a b → rank b < rank a

/-- Universal soundness of ranking abstractions. This theorem is independent of the free
recursor and applies to every carrier, concrete relation, and abstract domain. -/
theorem RankingAbstraction.wellFounded {α β : Type} {R : α → α → Prop}
    (A : RankingAbstraction α β R) : WellFounded (fun y x => R x y) := by
  have hnext : WellFounded (fun b a => A.next a b) :=
    Subrelation.wf (fun {_ _} h => A.decreases h) (InvImage.wf A.rank Nat.lt_wfRel.wf)
  refine ⟨fun x => ?_⟩
  obtain ⟨a, hxa⟩ := A.covers x
  have haa := hnext.apply a
  revert x
  induction haa with
  | intro a _ ih =>
      intro x hxa
      refine Acc.intro x (fun y hxy => ?_)
      obtain ⟨b, hyb, hab⟩ := A.simulates hxa hxy
      exact ih b hab y hyb

/-- The row's recorded free-system scope is fully proved. Its stronger method content is the
arbitrary-relation theorem `RankingAbstraction.wellFounded`. -/
theorem abstractInterpretationAdmittance_scope_proven :
    abstractInterpretationAdmittance_scope := by
  intro β γ next ρ hcover hdec hsim t
  let A : RankingAbstraction (FreeTerm Nat) β ContextStep :=
    { concretizes := γ
      next := next
      rank := ρ
      covers := hcover
      simulates := by
        intro a x hx y hxy
        exact hsim x hx y hxy
      decreases := hdec }
  exact A.wellFounded.apply t

/-- Exact method identity for abstract-interpretation termination. -/
theorem abstractInterpretationAdmittance_methodIdentity :
    (∀ {α β : Type} {R : α → α → Prop}, RankingAbstraction α β R →
      WellFounded (fun y x => R x y)) ∧ abstractInterpretationAdmittance_scope :=
  ⟨fun A => A.wellFounded, abstractInterpretationAdmittance_scope_proven⟩

/-! ## Row `categoricalToposTermination` -/

/-- Native data of `categoricalToposTermination`: a coalgebra of the powerset functor on `Set` and
a coalgebra morphism from the free recursor's root-step coalgebra. -/
structure categoricalToposTerminationData where
  /-- Carrier of the coalgebra. -/
  X : Type
  /-- The coalgebra: the powerset functor at each state. -/
  next : X → Set X
  /-- The coalgebra morphism from the free recursor's step coalgebra. -/
  hom : FreeTerm Nat → X

/-- Taylor's well-foundedness of a coalgebra of the powerset functor: every subset closed under the
next-time operator is the whole carrier (Jeannin, Kozen and Silva, *Well-founded coalgebras*,
Mathematical Structures in Computer Science 2017, after Taylor's definition). -/
def coalgebraWellFounded {X : Type} (next : X → Set X) : Prop :=
  ∀ S : X → Prop, (∀ x, (∀ y, y ∈ next x → S y) → S x) → ∀ x, S x

/-- Taylor's induction principle is accessibility of the step relation. -/
theorem coalgebraWellFounded_iff_acc {X : Type} (next : X → Set X) :
    coalgebraWellFounded next ↔ ∀ x, Acc (fun y x : X => y ∈ next x) x := by
  constructor
  · intro h x
    exact h (fun x => Acc (fun y x : X => y ∈ next x) x) (fun x ih => Acc.intro x ih) x
  · intro h S hS x
    have hx := h x
    induction hx with
    | intro y _ ih => exact hS y ih

/-- Accessibility forbids an infinite path. -/
theorem no_infinite_path_of_acc {X : Type} {next : X → Set X} {x : X}
    (h : Acc (fun y x : X => y ∈ next x) x) :
    ¬ ∃ p : Nat → X, p 0 = x ∧ ∀ n, p (n + 1) ∈ next (p n) := by
  induction h with
  | intro x hr ih =>
    rintro ⟨p, h0, hp⟩
    exact ih (p 1) (by rw [← h0]; exact hp 0)
      ⟨fun n => p (n + 1), rfl, fun n => hp (n + 1)⟩

/-- A well-founded powerset coalgebra has no infinite path. -/
theorem coalgebraWellFounded_no_infinite_path {X : Type} {next : X → Set X}
    (h : coalgebraWellFounded next) :
    ¬ ∃ p : Nat → X, ∀ n, p (n + 1) ∈ next (p n) := by
  rintro ⟨p, hp⟩
  exact no_infinite_path_of_acc ((coalgebraWellFounded_iff_acc next).1 h (p 0)) ⟨p, rfl, hp⟩

/-- Laws of `categoricalToposTermination` (Jeannin, Kozen and Silva 2017): `hom` is a coalgebra
morphism from the free recursor's root-step coalgebra, that is, the image of every root step is a
next-state and every next-state of an image is the image of a root step. -/
def categoricalToposTerminationLaws (M : categoricalToposTerminationData) : Prop :=
  (∀ {t u : FreeTerm Nat}, RootStep t u → M.hom u ∈ M.next (M.hom t)) ∧
  (∀ (t : FreeTerm Nat) (y : M.X), y ∈ M.next (M.hom t) →
    ∃ u : FreeTerm Nat, RootStep t u ∧ M.hom u = y)

/-- The method accepts the free two-rule system when the images of the two rule sources are well
founded in the coalgebra. Adapter: the free recursor's step coalgebra is the root-step relation on
`FreeTerm Nat`. -/
def categoricalToposTerminationAccepts (M : categoricalToposTerminationData) : Prop :=
  (∀ b s : FreeTerm Nat, Acc (fun y x : M.X => y ∈ M.next x) (M.hom (.recur b s .zero))) ∧
  (∀ b s n : FreeTerm Nat,
    Acc (fun y x : M.X => y ∈ M.next x) (M.hom (.recur b s (.succ n))))

/-- Verdict: escape. Acceptance yields that no infinite next-path starts at the image of any free
term, in particular at the images of the two rule sources. -/
def categoricalToposTerminationResult (M : categoricalToposTerminationData) : Prop :=
  categoricalToposTerminationAccepts M ∧
    ∀ t : FreeTerm Nat, ¬ ∃ p : Nat → M.X, p 0 = M.hom t ∧ ∀ n, p (n + 1) ∈ M.next (p n)

/-- Soundness: the forward morphism law turns acceptance of the two rule sources into acceptance of
the image of every free term, and accessibility forbids an infinite path. -/
theorem categoricalToposTermination_sound :
    ∀ M, categoricalToposTerminationLaws M → categoricalToposTerminationAccepts M →
      categoricalToposTerminationResult M := by
  intro M hL hA
  refine ⟨hA, ?_⟩
  intro t
  exact no_infinite_path_of_acc (Acc.inv (hA.1 t .zero) (hL.1 (RootStep.recurZero t .zero)))

/-- Witness: the free recursor's own root-step coalgebra, with the identity morphism. -/
def categoricalToposTerminationWitness : categoricalToposTerminationData where
  X := FreeTerm Nat
  next := fun t => {u | RootStep t u}
  hom := fun t => t

theorem categoricalToposTerminationWitness_laws :
    categoricalToposTerminationLaws categoricalToposTerminationWitness := by
  refine ⟨?_, ?_⟩
  · intro t u h
    exact h
  · intro t y hy
    exact ⟨y, hy, rfl⟩

theorem categoricalToposTerminationWitness_accepts :
    categoricalToposTerminationAccepts categoricalToposTerminationWitness :=
  ⟨fun _ _ => (main_free_root_termination Nat).apply _,
    fun _ _ _ => (main_free_root_termination Nat).apply _⟩

theorem categoricalToposTerminationWitness_result :
    categoricalToposTerminationResult categoricalToposTerminationWitness :=
  categoricalToposTermination_sound _ categoricalToposTerminationWitness_laws
    categoricalToposTerminationWitness_accepts

/-- A looping coalgebra: one state, one self-loop, with the constant morphism. -/
def categoricalToposTerminationLoop : categoricalToposTerminationData where
  X := Unit
  next := fun _ => Set.univ
  hom := fun _ => ()

theorem categoricalToposTerminationLoop_path :
    ∃ p : Nat → Unit, ∀ n, p (n + 1) ∈ categoricalToposTerminationLoop.next (p n) :=
  ⟨fun _ => (), fun _ => trivial⟩

theorem categoricalToposTerminationLoop_not_accepts :
    ¬ categoricalToposTerminationAccepts categoricalToposTerminationLoop := by
  intro h
  exact no_infinite_path_of_acc (h.1 .zero .zero) ⟨fun _ => (), rfl, fun _ => trivial⟩

theorem categoricalToposTerminationLoop_not_laws :
    ¬ categoricalToposTerminationLaws categoricalToposTerminationLoop := by
  intro h
  obtain ⟨u, hroot, -⟩ := h.2 (.var 0) () trivial
  cases hroot

/-- The free recursor's own coalgebra is well founded in Taylor's sense. -/
theorem categoricalToposTerminationWitness_coalgebra :
    coalgebraWellFounded categoricalToposTerminationWitness.next :=
  (coalgebraWellFounded_iff_acc _).2 fun t => (main_free_root_termination Nat).apply t

/-- **Defining feature.** The free recursor's root-step coalgebra is well founded and has no
infinite path; a looping coalgebra on the unit type has one and fails the exactness law and
acceptance. -/
theorem categoricalToposTerminationWitness_feature :
    coalgebraWellFounded categoricalToposTerminationWitness.next ∧
      categoricalToposTerminationResult categoricalToposTerminationWitness ∧
      (¬ categoricalToposTerminationAccepts categoricalToposTerminationLoop) ∧
      (¬ categoricalToposTerminationLaws categoricalToposTerminationLoop) ∧
      (∃ p : Nat → Unit,
        ∀ n, p (n + 1) ∈ categoricalToposTerminationLoop.next (p n)) ∧
      (¬ ∃ p : Nat → FreeTerm Nat,
        ∀ n, p (n + 1) ∈ categoricalToposTerminationWitness.next (p n)) :=
  ⟨categoricalToposTerminationWitness_coalgebra,
    categoricalToposTerminationWitness_result,
    categoricalToposTerminationLoop_not_accepts,
    categoricalToposTerminationLoop_not_laws,
    categoricalToposTerminationLoop_path,
    coalgebraWellFounded_no_infinite_path categoricalToposTerminationWitness_coalgebra⟩

/-- **Mutation.** The identity morphism is replaced by the constant morphism to `var 0`, everything
else as in the witness: the forward law fails, because `var 0` has no root step. -/
theorem categoricalToposTermination_mutation :
    ¬ categoricalToposTerminationLaws
      { categoricalToposTerminationWitness with hom := fun _ => .var 0 } := by
  intro h
  have hroot := h.1 (RootStep.recurZero FreeTerm.zero FreeTerm.zero)
  cases hroot

/-- **Scope.** Every well-founded powerset coalgebra on every carrier has no infinite path. -/
def categoricalToposTermination_scope : Prop :=
  ∀ (X : Type) (next : X → Set X), coalgebraWellFounded next →
    ¬ ∃ p : Nat → X, ∀ n, p (n + 1) ∈ next (p n)

/-- The powerset-coalgebra scope is fully proved for every carrier and transition coalgebra. -/
theorem categoricalToposTermination_scope_proven : categoricalToposTermination_scope :=
  fun _X _next h => coalgebraWellFounded_no_infinite_path h

/-- Exact method identity for the categorical row: well-founded powerset coalgebras have no
infinite path, and the row witness is an exact coalgebra morphism in both directions. -/
theorem categoricalToposTermination_methodIdentity :
    categoricalToposTermination_scope ∧
      categoricalToposTerminationLaws categoricalToposTerminationWitness ∧
      coalgebraWellFounded categoricalToposTerminationWitness.next :=
  ⟨categoricalToposTermination_scope_proven,
    categoricalToposTerminationWitness_laws,
    categoricalToposTerminationWitness_coalgebra⟩

/-! ## Row `higherOrderLCTRS` -/

/-- Term symbols of the higher-order recursor: the application symbol, the recursor and the
wrapper. The layer is applicative, so a term symbol may be applied to any argument list, and the
higher-order pattern `F x` is the application of a variable. -/
inductive HUser where
  | happ
  | hrec
  | hwrap
  deriving DecidableEq

/-- Native data of `higherOrderLCTRS`: a projection of the constrained dependency-pair argument
and the integer bound of the value criterion. -/
structure higherOrderLCTRSData where
  /-- Projection of a term symbol to an argument position. -/
  proj : HUser → Nat
  /-- The integer bound of the value criterion. -/
  bound : Int

/-- Terms of the higher-order constrained recursor: the applicative layer over `HUser`. -/
abbrev HTerm : Type := Term (LSym HUser) Nat

/-- An integer value. -/
def hlit (n : Int) : HTerm := .app (.inr (.lit n)) []

/-- `rec(F, b, x) → F x (rec(F, b, x − 1)) [x > 0]`. -/
def hRecSucc : LRule HUser Nat :=
  ⟨.app (.inl .hrec) [.var 0, .var 1, .var 2],
    .app (.inl .happ) [.app (.inl .happ) [.var 0, .var 2],
      .app (.inl .hrec) [.var 0, .var 1, .app (.inr .sub) [.var 2, hlit 1]]],
    .app (.inr .gt) [.var 2, hlit 0], rfl⟩

/-- `rec(F, b, x) → b [x ≤ 0]`. -/
def hRecZero : LRule HUser Nat :=
  ⟨.app (.inl .hrec) [.var 0, .var 1, .var 2], .var 1, .app (.inr .le) [.var 2, hlit 0], rfl⟩

/-- The higher-order recursor with its two constraints (Guo and Kop, *Higher-order LCTRSs*,
ESOP 2024, in the applicative layer). -/
def higherOrderRecursor : List (LRule HUser Nat) := [hRecSucc, hRecZero]

theorem mem_higherOrderRecursor {ρ : LRule HUser Nat} (h : ρ ∈ higherOrderRecursor) :
    ρ = hRecSucc ∨ ρ = hRecZero := by
  simpa [higherOrderRecursor] using h

theorem higherOrderRecursor_termRooted : LTermRooted higherOrderRecursor := by
  intro ρ hρ
  rcases mem_higherOrderRecursor hρ with rfl | rfl
  exacts [⟨_, _, rfl⟩, ⟨_, _, rfl⟩]

theorem higherOrderRecursor_defined_iff (g : HUser) :
    LDefined higherOrderRecursor g ↔ g = .hrec := by
  constructor
  · rintro ⟨ρ, hρ, largs, hl⟩
    rcases mem_higherOrderRecursor hρ with rfl | rfl <;>
      simp only [hRecSucc, hRecZero, Term.app.injEq, Sum.inl.injEq] at hl <;> exact hl.1.symm
  · rintro rfl
    exact ⟨hRecSucc, by simp [higherOrderRecursor], _, rfl⟩

/-- The application symbol is not defined: the recursive call is reached below a variable-headed
application. -/
theorem higherOrderRecursor_happ_not_defined : ¬ LDefined higherOrderRecursor .happ := by
  intro h
  have hh : HUser.happ = HUser.hrec := (higherOrderRecursor_defined_iff .happ).1 h
  cases hh

/-- The only `rec`-rooted subterm of the successor rule's right-hand side is the recursive call,
reached through the application of the variable `F`. -/
theorem hRecSucc_rhs_recur_subterm {targs : List HTerm}
    (h : IsSubterm (.app (.inl .hrec) targs) hRecSucc.rhs) :
    targs = [.var 0, .var 1, .app (.inr .sub) [.var 2, hlit 1]] := by
  have hm := mem_subtermsT_of_isSubterm h
  simp [hRecSucc, subtermsT, subtermsL, hlit] at hm
  exact hm

/-- The substitution of `F`, `b`, `x` for the variables `0`, `1`, `2`. -/
def hsub3 (F b x : HTerm) : Subst (LSym HUser) Nat :=
  fun v => if v = 0 then F else if v = 1 then b else x

/-- A substitution that respects the higher-order recursive rule instantiates the counter by a
positive integer. -/
theorem respects_hRecSucc {γ : Subst (LSym HUser) Nat} (h : Respects hRecSucc γ) :
    ∃ n : Int, γ 2 = hlit n ∧ 0 < n := by
  obtain ⟨v, hv⟩ := h.1 2 (by simp [LVars, hRecSucc, hlit])
  have hc := h.2
  rcases v with n | (_ | _)
  · refine ⟨n, hv, ?_⟩
    simp [hRecSucc, hv, valT, hlit, jeval, jevalL, jop] at hc
    exact hc
  · simp [hRecSucc, hv, valT, hlit, jeval, jevalL, jop] at hc
  · simp [hRecSucc, hv, valT, hlit, jeval, jevalL, jop] at hc

/-- Laws of `higherOrderLCTRS` (Kop, *Termination of LCTRSs*, WST 2013, Definition 9, lifted to the
applicative layer): the projection assigns a marked symbol one of its argument positions. -/
def higherOrderLCTRSLaws (M : higherOrderLCTRSData) : Prop :=
  ∀ g, LDefined higherOrderRecursor g → M.proj g < 3

/-- The value criterion (Kop 2013, Theorem 10; Guo, Hagens, Kop and Vale, *Higher-order constrained
dependency pairs*, MFCS 2024, for the higher-order layer) accepts the dependency pair
`rec♯(F, b, x) → rec♯(F, b, x − 1) [x > 0]`: under the constraint the projected counter is a
value above the bound that decreases. -/
def higherOrderLCTRSAccepts (M : higherOrderLCTRSData) : Prop :=
  ValueCriterion higherOrderRecursor M.proj M.bound

/-- Verdict: escape. -/
def higherOrderLCTRSResult (M : higherOrderLCTRSData) : Prop :=
  higherOrderLCTRSAccepts M ∧ ∀ t : HTerm, RSN (LRoot higherOrderRecursor) t

/-- Soundness through the value criterion and the constrained dependency-pair theorem, with the
recursive call extracted through the applicative layer of the right-hand side. -/
theorem higherOrderLCTRS_sound :
    ∀ M, higherOrderLCTRSLaws M → higherOrderLCTRSAccepts M → higherOrderLCTRSResult M := by
  intro M hL hA
  exact ⟨hA, lctrs_terminating_of_chains higherOrderRecursor higherOrderRecursor_termRooted
    (wf_lChain_of_valueCriterion higherOrderRecursor higherOrderRecursor_termRooted
      M.proj M.bound hA)⟩

/-- The witness: project to the counter, bound `0`. -/
def higherOrderLCTRSWitness : higherOrderLCTRSData := ⟨fun _ => 2, 0⟩

theorem higherOrderLCTRSWitness_laws : higherOrderLCTRSLaws higherOrderLCTRSWitness :=
  fun _ _ => by norm_num [higherOrderLCTRSWitness]

theorem higherOrderLCTRSWitness_accepts :
    higherOrderLCTRSAccepts higherOrderLCTRSWitness := by
  intro ρ hρ f largs hf g targs hsub hdef γ hresp
  rw [higherOrderRecursor_defined_iff] at hdef
  subst hdef
  rcases mem_higherOrderRecursor hρ with rfl | rfl
  · simp only [hRecSucc, Term.app.injEq, Sum.inl.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have ht := hRecSucc_rhs_recur_subterm hsub
    subst ht
    obtain ⟨n, hn, hpos⟩ := respects_hRecSucc hresp
    refine ⟨n, n - 1, ?_, ?_, by omega, by simpa [higherOrderLCTRSWitness] using hpos⟩
    · simp [higherOrderLCTRSWitness, hn, hlit, jeval, jevalL, jop]
    · simp [higherOrderLCTRSWitness, hn, hlit, jeval, jevalL, jop]
  · have hm := mem_subtermsT_of_isSubterm hsub
    simp [hRecZero, subtermsT] at hm

theorem higherOrderLCTRSWitness_result :
    higherOrderLCTRSResult higherOrderLCTRSWitness :=
  higherOrderLCTRS_sound _ higherOrderLCTRSWitness_laws higherOrderLCTRSWitness_accepts

/-- The successor rule with its constraint dropped. -/
def hRecSuccTrue : LRule HUser Nat :=
  ⟨.app (.inl .hrec) [.var 0, .var 1, .var 2],
    .app (.inl .happ) [.app (.inl .happ) [.var 0, .var 2],
      .app (.inl .hrec) [.var 0, .var 1, .app (.inr .sub) [.var 2, hlit 1]]],
    .app (.inr .tt) [], rfl⟩

/-- The unconstrained successor rule alone. -/
def higherOrderLoop : List (LRule HUser Nat) := [hRecSuccTrue]

/-- The unconstrained successor rule applies at every counter. -/
theorem hRecSuccTrue_step (F b x : HTerm) :
    LRoot higherOrderLoop (.app (.inl .hrec) [F, b, x])
      (.app (.inl .happ) [.app (.inl .happ) [F, x],
        .app (.inl .hrec) [F, b, .app (.inr .sub) [x, hlit 1]]]) := by
  refine Or.inl ⟨hRecSuccTrue, by simp [higherOrderLoop], hsub3 F b x, ?_, ?_, ?_⟩
  · exact ⟨fun y hy => absurd hy (by
        simp [LVars, hRecSuccTrue, hlit]
        tauto),
      by simp [hRecSuccTrue, jeval, jevalL, jop]⟩
  · simp [hRecSuccTrue, hsub3, hlit, Subst.apply_app, Subst.applyList_nil]
  · simp [hRecSuccTrue, hsub3, hlit, Subst.apply_app, Subst.applyList_nil]

/-- The counter term `x − 1` unfolded `n` times. -/
def hsubCounter : Nat → HTerm
  | 0 => hlit 0
  | n + 1 => .app (.inr .sub) [hsubCounter n, hlit 1]

/-- The `n` nested applications above the loop's redex. -/
def hloopCtx : Nat → HTerm → HTerm
  | 0, t => t
  | n + 1, t => hloopCtx n (.app (.inl .happ) [.app (.inl .happ) [hlit 0, hsubCounter n], t])

theorem hloopCtx_lift {a b : HTerm} (h : CtxStep (LRoot higherOrderLoop) a b) :
    ∀ n, CtxStep (LRoot higherOrderLoop) (hloopCtx n a) (hloopCtx n b)
  | 0 => h
  | n + 1 => by
    show CtxStep (LRoot higherOrderLoop)
      (hloopCtx n (.app (.inl .happ) [.app (.inl .happ) [hlit 0, hsubCounter n], a]))
      (hloopCtx n (.app (.inl .happ) [.app (.inl .happ) [hlit 0, hsubCounter n], b]))
    exact hloopCtx_lift (CtxStep.arg (.inl .happ)
      [.app (.inl .happ) [hlit 0, hsubCounter n]] [] h) n

/-- The `n`-th term of the loop: the redex at counter `hsubCounter n` under `n` applications. -/
def hloopTerm (n : Nat) : HTerm :=
  hloopCtx n (.app (.inl .hrec) [hlit 0, hlit 0, hsubCounter n])

theorem hloopTerm_step (n : Nat) :
    CtxStep (LRoot higherOrderLoop) (hloopTerm n) (hloopTerm (n + 1)) := by
  have hroot : CtxStep (LRoot higherOrderLoop)
      (.app (.inl .hrec) [hlit 0, hlit 0, hsubCounter n])
      (.app (.inl .happ) [.app (.inl .happ) [hlit 0, hsubCounter n],
        .app (.inl .hrec) [hlit 0, hlit 0, .app (.inr .sub) [hsubCounter n, hlit 1]]]) :=
    CtxStep.root (hRecSuccTrue_step (hlit 0) (hlit 0) (hsubCounter n))
  exact hloopCtx_lift hroot n

/-- An infinite step sequence forbids accessibility. -/
theorem not_acc_of_chain {α : Type} {r : α → α → Prop} {p : Nat → α}
    (h : ∀ n, r (p (n + 1)) (p n)) : ¬ Acc r (p 0) := by
  intro hacc
  have key : ∀ x, Acc r x → ¬ ∃ q : Nat → α, q 0 = x ∧ ∀ n, r (q (n + 1)) (q n) := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      rintro ⟨q, h0, hq⟩
      exact ih (q 1) (by rw [← h0]; exact hq 0) ⟨fun n => q (n + 1), rfl, fun n => hq (n + 1)⟩
  exact key (p 0) hacc ⟨p, rfl, h⟩

/-- The unconstrained successor rule loops through the negative integers. -/
theorem hloopTerm_not_terminating : ¬ RSN (LRoot higherOrderLoop) (hloopTerm 0) :=
  not_acc_of_chain (r := fun u t => CtxStep (LRoot higherOrderLoop) t u) hloopTerm_step

/-- **Defining feature.** The successor right-hand side is an application whose head is the variable
`F`; the dependency-pair extraction passes through that application node to the recursive call. The
constraint is substituted by the matched counter: it holds at `x = 3` and fails at `x = -1`. Theory
evaluation of `3 − 1` to `2` is a calculation step, and the rule without its constraint loops
through the negative integers. -/
theorem higherOrderLCTRSWitness_feature :
    (hRecSucc.rhs = .app (.inl .happ) [.app (.inl .happ) [.var 0, .var 2],
        .app (.inl .hrec) [.var 0, .var 1, .app (.inr .sub) [.var 2, hlit 1]]] ∧
      (∀ targs : List HTerm, IsSubterm (.app (.inl .hrec) targs) hRecSucc.rhs →
        targs = [.var 0, .var 1, .app (.inr .sub) [.var 2, hlit 1]]) ∧
      ¬ LDefined higherOrderRecursor .happ) ∧
    (Respects hRecSucc (hsub3 (hlit 0) (hlit 0) (hlit 3)) ∧
      ¬ Respects hRecSucc (hsub3 (hlit 0) (hlit 0) (hlit (-1)))) ∧
    CtxStep (LRoot higherOrderRecursor) (.app (.inr .sub) [hlit 3, hlit 1]) (hlit 2) ∧
    ¬ RSN (LRoot higherOrderLoop) (hloopTerm 0) := by
  refine ⟨⟨rfl, fun targs hsub => hRecSucc_rhs_recur_subterm hsub, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact higherOrderRecursor_happ_not_defined
  · refine ⟨fun x hx => ?_, ?_⟩
    · have hx2 : x = 2 := by
        simp [LVars, hRecSucc, hlit] at hx
        omega
      subst hx2
      exact ⟨.int 3, rfl⟩
    · simp [hRecSucc, hsub3, hlit, jeval, jevalL, jop]
  · intro h
    have hc := h.2
    simp [hRecSucc, hsub3, hlit, jeval, jevalL, jop] at hc
  · refine CtxStep.root (Or.inr ⟨.sub, [hlit 3, hlit 1], .int 2, trivial, rfl, ?_, ?_, rfl⟩)
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      exacts [⟨.int 3, rfl⟩, ⟨.int 1, rfl⟩]
    · simp [hlit, jeval, jevalL, jop]
  · exact hloopTerm_not_terminating

/-- The witness with the value bound `1`. -/
def higherOrderLCTRSBound1 : higherOrderLCTRSData := ⟨fun _ => 2, 1⟩

/-- Raising the value bound to `1` keeps the laws and loses the criterion: at `x = 1` the constraint
`x > 0` holds, and `1 ≻ 0` fails for the bound `1`. -/
theorem higherOrderLCTRS_mutation :
    higherOrderLCTRSLaws higherOrderLCTRSBound1 ∧
      ¬ higherOrderLCTRSAccepts higherOrderLCTRSBound1 := by
  refine ⟨fun _ _ => by norm_num [higherOrderLCTRSBound1], fun h => ?_⟩
  have hresp : Respects hRecSucc (hsub3 (hlit 0) (hlit 0) (hlit 1)) := by
    refine ⟨fun x hx => ?_, ?_⟩
    · have hx2 : x = 2 := by
        simp [LVars, hRecSucc, hlit] at hx
        omega
      subst hx2
      exact ⟨.int 1, rfl⟩
    · simp [hRecSucc, hsub3, hlit, jeval, jevalL, jop]
  obtain ⟨n, m, hn, -, -, hbn⟩ := h hRecSucc (by simp [higherOrderRecursor]) .hrec
    [.var 0, .var 1, .var 2] rfl .hrec [.var 0, .var 1, .app (.inr .sub) [.var 2, hlit 1]]
    (IsSubterm.arg (.inl .happ) [.app (.inl .happ) [.var 0, .var 2],
      .app (.inl .hrec) [.var 0, .var 1, .app (.inr .sub) [.var 2, hlit 1]]] (by simp)
      (IsSubterm.refl _))
    ((higherOrderRecursor_defined_iff _).2 rfl) _ hresp
  simp [hsub3, hlit, higherOrderLCTRSBound1, Subst.applyList_eq_map, Subst.apply_var,
    jeval, jevalL, jop] at hn
  simp [higherOrderLCTRSBound1] at hbn
  omega

/-- **Scope.** The arbitrary-signature applicative constrained-rewriting layer: every rooted rule
set satisfying the value criterion terminates. -/
def higherOrderLCTRS_scope : Prop :=
  ∀ (F : Type) (R : List (LRule F Nat)) (ν : F → Nat) (b : Int),
    LTermRooted R → ValueCriterion R ν b → ∀ t : Term (LSym F) Nat, RSN (LRoot R) t

/-- The arbitrary-signature constrained applicative theorem is fully discharged by the generic
dependency-pair chain theorem and the value criterion. -/
theorem higherOrderLCTRS_scope_proven : higherOrderLCTRS_scope := by
  intro F R ν b hroot hvalue t
  exact lctrs_terminating_of_chains R hroot
    (wf_lChain_of_valueCriterion R hroot ν b hvalue) t

/-- Exact method identity for the implemented higher-order LCTRS layer: the theorem quantifies
over every user signature and constrained rule set in the applicative encoding, while the
concrete recursor demonstrates the variable-headed higher-order call and its value decrease. -/
theorem higherOrderLCTRS_methodIdentity :
    higherOrderLCTRS_scope ∧ higherOrderLCTRSLaws higherOrderLCTRSWitness ∧
      higherOrderLCTRSAccepts higherOrderLCTRSWitness :=
  ⟨higherOrderLCTRS_scope_proven, higherOrderLCTRSWitness_laws,
    higherOrderLCTRSWitness_accepts⟩

end OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks
