import OperatorKO7.Meta.OperationalInexpressibility.RelationalRecovery

/-!
# Side channels for set-valued certificate tasks

For a set-valued certificate task, states sharing one observer value and one side symbol must admit
one common certificate. This is a hypergraph coloring condition: every subset with no common
certificate must use more than one side symbol. Pairwise conflict graphs can miss higher-order
incompatibility.

Relation: equality on observer fibers and side-channel color classes.
Property: partial-decoder recovery and hypergraph coloring equivalence.
Trust: kernel-only; the decoder construction uses classical choice.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.RelationalSideChannel

open OperatorKO7.Meta.OperationalInexpressibility.RelationalRecovery

universe u v w z

/-- Source states that share one observation and one side symbol. -/
def ColorCell {X : Type u} {Q : Type v} {C : Type w}
    (q : X → Q) (color : X → C) (q0 : Q) (c : C) : Set X :=
  {x | q x = q0 ∧ color x = c}

/-- One witness is admissible at every state of the selected set. -/
def CommonWitnessOn {X : Type u} {W : Type z}
    (admissible : X → W → Prop) (S : Set X) : Prop :=
  ∃ witness, ∀ x, x ∈ S → admissible x witness

/-- Every realized observer/color cell has a common admissible certificate. -/
def CellwiseCompatible {X : Type u} {Q : Type v} {C : Type w} {W : Type z}
    (q : X → Q) (admissible : X → W → Prop) (color : X → C) : Prop :=
  ∀ q0 c, Set.Nonempty (ColorCell q color q0 c) →
    CommonWitnessOn admissible (ColorCell q color q0 c)

/-- A partial side-channel decoder needs a value only on realized observer/color pairs. -/
def PartialRelationalSideChannel
    {X : Type u} {Q : Type v} {C : Type w} {W : Type z}
    (q : X → Q) (admissible : X → W → Prop) (color : X → C) : Prop :=
  ∃ decode : Q → C → Option W,
    ∀ x, ∃ witness, decode (q x) (color x) = some witness ∧ admissible x witness

/-- A partial decoder exists exactly when every realized color cell has a common witness. -/
theorem partialRelationalSideChannel_iff_cellwiseCompatible
    {X : Type u} {Q : Type v} {C : Type w} {W : Type z}
    (q : X → Q) (admissible : X → W → Prop) (color : X → C) :
    PartialRelationalSideChannel q admissible color ↔
      CellwiseCompatible q admissible color := by
  classical
  constructor
  · rintro ⟨decode, hdecode⟩ q0 c ⟨x0, hx0⟩
    obtain ⟨witness, hcell, hwitness⟩ := hdecode x0
    refine ⟨witness, ?_⟩
    intro x hx
    obtain ⟨wx, hxcell, hxwitness⟩ := hdecode x
    have hsame : decode (q x) (color x) = decode (q x0) (color x0) := by
      simp [hx.1, hx.2, hx0.1, hx0.2]
    have hsome : some wx = some witness := by
      rw [← hxcell, hsame, hcell]
    have heq : wx = witness := Option.some.inj hsome
    simpa [heq] using hxwitness
  · intro hcells
    let cellWitness : Q → C → Option W := fun q0 c =>
      if h : Set.Nonempty (ColorCell q color q0 c) then
        some (Classical.choose (hcells q0 c h))
      else none
    refine ⟨cellWitness, ?_⟩
    intro x
    have hnonempty : Set.Nonempty (ColorCell q color (q x) (color x)) :=
      ⟨x, rfl, rfl⟩
    refine ⟨Classical.choose (hcells (q x) (color x) hnonempty), ?_, ?_⟩
    · simp [cellWitness, hnonempty]
    · exact Classical.choose_spec (hcells (q x) (color x) hnonempty) x ⟨rfl, rfl⟩

/-- A fiber subset uses one observer value. -/
def FiberContained {X : Type u} {Q : Type v} (q : X → Q) (S : Set X) : Prop :=
  ∃ q0, Set.Nonempty S ∧ ∀ x, x ∈ S → q x = q0

/-- A bad fiber subset has no common admissible certificate. -/
def BadFiberSubset {X : Type u} {Q : Type v} {W : Type z}
    (q : X → Q) (admissible : X → W → Prop) (S : Set X) : Prop :=
  FiberContained q S ∧ ¬ CommonWitnessOn admissible S

/-- A set is monochromatic under the side-channel encoder. -/
def Monochromatic {X : Type u} {C : Type w} (color : X → C) (S : Set X) : Prop :=
  ∃ c, ∀ x, x ∈ S → color x = c

/-- Hypergraph-valid coloring: every fiber subset lacking a common certificate uses at least two colors. -/
def AvoidsBadMonochromaticSubsets
    {X : Type u} {Q : Type v} {C : Type w} {W : Type z}
    (q : X → Q) (admissible : X → W → Prop) (color : X → C) : Prop :=
  ∀ S, BadFiberSubset q admissible S → ¬ Monochromatic color S

/-- Cellwise compatibility is equivalent to coloring every bad fiber hyperedge non-monochromatically. -/
theorem cellwiseCompatible_iff_avoidsBadMonochromaticSubsets
    {X : Type u} {Q : Type v} {C : Type w} {W : Type z}
    (q : X → Q) (admissible : X → W → Prop) (color : X → C) :
    CellwiseCompatible q admissible color ↔
      AvoidsBadMonochromaticSubsets q admissible color := by
  classical
  constructor
  · intro hcells S hbad hmono
    rcases hbad.1 with ⟨q0, hSne, hq⟩
    rcases hmono with ⟨c, hc⟩
    have hcellne : Set.Nonempty (ColorCell q color q0 c) := by
      rcases hSne with ⟨x0, hx0⟩
      exact ⟨x0, hq x0 hx0, hc x0 hx0⟩
    obtain ⟨witness, hwitness⟩ := hcells q0 c hcellne
    apply hbad.2
    refine ⟨witness, ?_⟩
    intro x hx
    exact hwitness x ⟨hq x hx, hc x hx⟩
  · intro hcolor q0 c hcellne
    by_contra hcommon
    let S : Set X := ColorCell q color q0 c
    have hbad : BadFiberSubset q admissible S := by
      refine ⟨?_, hcommon⟩
      exact ⟨q0, hcellne, fun x hx => hx.1⟩
    have hmono : Monochromatic color S :=
      ⟨c, fun x hx => hx.2⟩
    exact hcolor S hbad hmono

/-- The partial side-channel problem is exactly the fiber-hypergraph coloring problem. -/
theorem partialRelationalSideChannel_iff_hypergraphColoring
    {X : Type u} {Q : Type v} {C : Type w} {W : Type z}
    (q : X → Q) (admissible : X → W → Prop) (color : X → C) :
    PartialRelationalSideChannel q admissible color ↔
      AvoidsBadMonochromaticSubsets q admissible color := by
  rw [partialRelationalSideChannel_iff_cellwiseCompatible,
    cellwiseCompatible_iff_avoidsBadMonochromaticSubsets]

/-! ## Three-state higher-order incompatibility control -/

/-- One side symbol merges all three states. -/
def threeWayUnitColor (_ : Fin 3) : Unit := ()

/-- A one-symbol side channel still leaves the three-way admissibility conflict unresolved. -/
theorem threeWay_one_symbol_fails :
    ¬ PartialRelationalSideChannel threeWayObserver threeWayAdmissible threeWayUnitColor := by
  intro h
  have hcells := (partialRelationalSideChannel_iff_cellwiseCompatible
    threeWayObserver threeWayAdmissible threeWayUnitColor).1 h
  have hne : Set.Nonempty (ColorCell threeWayObserver threeWayUnitColor () ()) :=
    ⟨0, rfl, rfl⟩
  obtain ⟨witness, hwitness⟩ := hcells () () hne
  have hself := hwitness witness ⟨rfl, rfl⟩
  exact hself rfl

/-- Two side symbols are enough: states zero and one share `false`; state two uses `true`. -/
def threeWayTwoColor : Fin 3 → Bool
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => false
  | ⟨2, _⟩ => true

/-- Decoder for the two-symbol fixture. The false cell uses witness two; the true cell uses witness zero. -/
def threeWayTwoDecoder (_ : Unit) : Bool → Option (Fin 3)
  | false => some 2
  | true => some 0

/-- The two-symbol encoder has an admissible decoder for every source state. -/
theorem threeWay_two_symbols_succeed :
    PartialRelationalSideChannel threeWayObserver threeWayAdmissible threeWayTwoColor := by
  refine ⟨threeWayTwoDecoder, ?_⟩
  intro x
  fin_cases x
  · exact ⟨2, rfl, by simp [threeWayAdmissible]⟩
  · exact ⟨2, rfl, by simp [threeWayAdmissible]⟩
  · exact ⟨0, rfl, by simp [threeWayAdmissible]⟩

/-- The fixture separates pairwise graph compatibility from the true hypergraph requirement:
every pair is compatible, one color fails, and two colors succeed. -/
theorem threeWay_higherOrder_sideChannel_separation :
    PairwiseFiberCompatible threeWayObserver threeWayAdmissible ∧
      ¬ PartialRelationalSideChannel threeWayObserver threeWayAdmissible threeWayUnitColor ∧
      PartialRelationalSideChannel threeWayObserver threeWayAdmissible threeWayTwoColor :=
  ⟨threeWay_pairwiseFiberCompatible, threeWay_one_symbol_fails,
    threeWay_two_symbols_succeed⟩

end OperatorKO7.Meta.OperationalInexpressibility.RelationalSideChannel
