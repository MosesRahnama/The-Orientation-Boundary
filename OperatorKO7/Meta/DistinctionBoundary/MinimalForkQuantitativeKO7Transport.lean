import OperatorKO7.Meta.DistinctionBoundary.MinimalForkQuantitative
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity

/-!
# Quantitative transport along the proved KO7 local-cone isomorphisms

The KO7 multiplicities are derived here from the canonical `Fork3` profile by
relation isomorphism. This is a transport proof, not an equality of two
independently computed numerals.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u v

/-- Exact paths transport forward along a relation isomorphism. -/
theorem RelIso.steps_map {A : Type u} {B : Type v}
    {RA : A → A → Prop} {RB : B → B → Prop}
    (e : RelIso RA RB) {n : Nat} {x y : A}
    (h : Steps RA n x y) : Steps RB n (e.toEquiv x) (e.toEquiv y) := by
  induction h with
  | zero => exact Steps.zero _
  | @succ n a b c hab hbc ih =>
      exact Steps.succ (e.map_rel_iff.mp hab) ih

/-- Exact reachability transports forward. -/
theorem RelIso.reach_map {A : Type u} {B : Type v}
    {RA : A → A → Prop} {RB : B → B → Prop}
    (e : RelIso RA RB) {x y : A} (h : Reach RA x y) :
    Reach RB (e.toEquiv x) (e.toEquiv y) := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, e.steps_map hn⟩

/-- Exact reachability is reflected as well. -/
theorem RelIso.reach_iff {A : Type u} {B : Type v}
    {RA : A → A → Prop} {RB : B → B → Prop}
    (e : RelIso RA RB) {x y : A} :
    Reach RA x y ↔ Reach RB (e.toEquiv x) (e.toEquiv y) := by
  constructor
  · exact e.reach_map
  · intro h
    have hs := e.symm.reach_map h
    simpa only [RelIso.symm, Equiv.symm_apply_apply] using hs

/-- Normal forms transport and reflect. -/
theorem RelIso.normalForm_iff {A : Type u} {B : Type v}
    {RA : A → A → Prop} {RB : B → B → Prop}
    (e : RelIso RA RB) {x : A} :
    Quantitative.NormalForm RA x ↔
      Quantitative.NormalForm RB (e.toEquiv x) := by
  constructor
  · intro h y hy
    have hback : RA x (e.toEquiv.symm y) := by
      exact e.map_rel_iff.mpr (by simpa using hy)
    exact h _ hback
  · intro h y hy
    have hfor : RB (e.toEquiv x) (e.toEquiv y) := e.map_rel_iff.mp hy
    exact h _ hfor

/-- Terminal-support membership is preserved exactly. -/
theorem RelIso.mem_terminalSupport_iff
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {RA : A → A → Prop} {RB : B → B → Prop}
    (e : RelIso RA RB) {source x : A} :
    x ∈ terminalSupport RA source ↔
      e.toEquiv x ∈ terminalSupport RB (e.toEquiv source) := by
  rw [mem_terminalSupport, mem_terminalSupport, e.reach_iff, e.normalForm_iff]

/-- Equivalence between the two terminal-support subtypes. -/
noncomputable def RelIso.terminalSupportEquiv
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {RA : A → A → Prop} {RB : B → B → Prop}
    (e : RelIso RA RB) (source : A) :
    {x // x ∈ terminalSupport RA source} ≃
      {y // y ∈ terminalSupport RB (e.toEquiv source)} where
  toFun x := ⟨e.toEquiv x.1, e.mem_terminalSupport_iff.mp x.2⟩
  invFun y := by
    refine ⟨e.toEquiv.symm y.1, ?_⟩
    apply (e.mem_terminalSupport_iff
      (source := source) (x := e.toEquiv.symm y.1)).mpr
    simpa only [Equiv.apply_symm_apply] using y.2
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp

/-- Terminal multiplicity is invariant under relation isomorphism. -/
theorem RelIso.terminalMultiplicity_eq
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {RA : A → A → Prop} {RB : B → B → Prop}
    (e : RelIso RA RB) (source : A) :
    terminalMultiplicity RA source =
      terminalMultiplicity RB (e.toEquiv source) := by
  have hcard := Fintype.card_congr (e.terminalSupportEquiv source)
  simpa [terminalMultiplicity, Fintype.card_coe] using hcard

/-- KO7 raw local multiplicity is transported from canonical `Fork3`. -/
theorem ko7_raw_terminalMultiplicity_transport :
    terminalMultiplicity OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw .source = 2 := by
  have h := OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.fork3LocalRawIso.terminalMultiplicity_eq Fork3.source
  simpa using h.symm.trans fork3_raw_terminalMultiplicity_eq_two

/-- KO7 licensed local multiplicity is transported from the one-edge canonical repair. -/
theorem ko7_licensed_terminalMultiplicity_transport :
    terminalMultiplicity OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalLicensed .source = 1 := by
  have h := OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge.fork3LocalLicensedIso.terminalMultiplicity_eq Fork3.source
  simpa using h.symm.trans fork3_licensed_terminalMultiplicity_eq_one

/-- Transported raw multiplicity agrees with the independently existing KO7 theorem. -/
theorem ko7_raw_transport_agrees_existing :
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity.raw_terminalMultiplicity_eq_two = ko7_raw_terminalMultiplicity_transport := by
  rfl

/-- Transported licensed multiplicity agrees with the independently existing KO7 theorem. -/
theorem ko7_licensed_transport_agrees_existing :
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity.licensed_terminalMultiplicity_eq_one = ko7_licensed_terminalMultiplicity_transport := by
  rfl

/-- KO7's local terminal-support reduction is therefore the transported canonical 2→1 collapse. -/
theorem ko7_terminalMultiplicity_two_to_one_by_transport :
    terminalMultiplicity OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalRaw .source = 2 ∧
      terminalMultiplicity OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.LocalLicensed .source = 1 :=
  ⟨ko7_raw_terminalMultiplicity_transport,
    ko7_licensed_terminalMultiplicity_transport⟩

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork



