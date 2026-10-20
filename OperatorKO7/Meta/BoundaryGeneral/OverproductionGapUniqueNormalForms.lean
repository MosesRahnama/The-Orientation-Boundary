import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapConceptBridge
import OperatorKO7.Meta.UniqueNormalization.UNStatement

/-!
# The overproduction gap and unique normal forms

Campaign: the overproduction-gap programme (`KO7-LLM-Benchmark\1.paper\OMEGA-RESEARCH-PROGRAM.md`) and the
unique-normal-form section of the Distinction Boundary manuscript (RTA open problem #79).

The overproduction gap `overproductionGap R source μ ν r` is the base-two logarithm of the number of normal
forms reachable from `source`, minus the licensed information of a channel in bits. This module relates it to
the two uniqueness properties of normal forms. For a relation `R`:

* `UniqueReachableNormalForms R` (UN→): no element reaches two distinct normal forms;
* `UniqueConvertibleNormalForms R` (UN=): normal forms related by the equivalence closure of `R` coincide.

## Results

1. **Identification on finite carriers.** UN→ holds exactly when no element branches
   (`uniqueReachableNormalForms_iff_branchingFree`), exactly when no element raises a boundary event against a
   zero-gain channel (`uniqueReachableNormalForms_iff_zeroGainBoundaryEventFree`), and exactly when the gap is
   at most zero at every element against every nonnegative-gain channel
   (`uniqueReachableNormalForms_iff_gapNonpos`).
2. **UN= gives a nonpositive gap** (`gapNonpos_of_uniqueConvertibleNormalForms`), and a boundary event against a
   nonnegative-gain channel refutes UN= (`boundaryEvent_refutes_uniqueConvertibleNormalForms`).
3. **The fence.** `BridgeStep` (`a → b`, `a → c`, `c → c`, `d → c`, `d → e`) and `SplitStep` (`a → b`,
   `c → c`, `d → e`) have the same terminal support at every element, hence the same gap against every
   channel; `SplitStep` has UN=, and `BridgeStep` fails it because `b ← a → c ← d → e` joins the distinct normal
   forms `b` and `e` (`overproductionGap_leaves_uniqueConvertibleNormalForms_undetermined`). Consequently UN→
   and a nonpositive gap each fail to imply UN= on finite relations
   (`uniqueReachableNormalForms_not_imp_uniqueConvertibleNormalForms`,
   `gapNonpos_not_imp_uniqueConvertibleNormalForms`).
4. **Transport to term rewriting.** For a term rewriting system `R` and an injective map `ι` from a finite type
   onto a set of terms closed under one rewrite step, `fragmentStep R ι` is the rewrite relation read on that
   set. UN→ of `R`, and hence UN= of `R`, makes the gap of every such fragment nonpositive
   (`fragment_gapNonpos_of_UNred`, `fragment_gapNonpos_of_UNconv`); a boundary event on a fragment refutes both
   properties of `R` (`not_UNred_of_fragment_boundaryEvent`, `not_UNconv_of_fragment_boundaryEvent`). When every
   term lies in such a fragment, UN→ holds exactly when every fragment gap is nonpositive
   (`UNred_iff_fragmentGapNonpos`).
5. **Rewriting instances.** `forkTRS` (`a → b`, `a → c`) raises a one-bit boundary event on its constants and
   fails UN= (`forkTRS_fragment_boundaryEvent`, `forkTRS_not_UNconv`). `bridgeTRS` realizes `BridgeStep` on its
   constants: the gap of that fragment is nonpositive, and the failure of UN= (two normal forms joined by a
   conversion) lies inside the same fragment (`bridgeTRS_fragment_gapNonpos_and_not_UNconv`).

Proves: the statements above, on the declared carriers.
Does not prove: UN= for any system of the non-omega-overlapping class; any statement about terms outside a
finite step-closed fragment (the finite-fragment premise of `UNred_iff_fragmentGapNonpos` is explicit).
Relation: a caller-supplied relation on a finite carrier; for rewriting, `OperatorKO7.Meta.Rewriting.Step`
read on a fragment.
Closure: `Reach` for the gap; `Relation.EqvGen` for UN= of relations; `StepStar` and `conv` for the rewriting
properties `UNred` and `UNconv`.
Strategy: full rewriting.
Trust: kernel checked; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`, `unsafe` or `opaque`. Axiom
footprints are printed by `Test/OmegaFamilyReach.lean`.
-/

set_option autoImplicit false

/-! ## Uniqueness vocabulary for relations -/

namespace OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u

/-- **UN→ for a relation**: no element reaches two distinct normal forms. -/
def UniqueReachableNormalForms {T : Type u} (R : T → T → Prop) : Prop :=
  ∀ s n₁ n₂, Reach R s n₁ → NormalForm R n₁ → Reach R s n₂ → NormalForm R n₂ → n₁ = n₂

/-- **UN= for a relation**: normal forms related by the equivalence closure of the relation coincide. -/
def UniqueConvertibleNormalForms {T : Type u} (R : T → T → Prop) : Prop :=
  ∀ n₁ n₂, NormalForm R n₁ → NormalForm R n₂ → Relation.EqvGen R n₁ n₂ → n₁ = n₂

/-- **No strict branching**: at every element, fewer than two normal forms are reachable. -/
def BranchingFree {T : Type u} [Fintype T] (R : T → T → Prop) : Prop :=
  ∀ source, ¬ BranchingAt R source

end OperatorKO7.Meta.DistinctionBoundary.Quantitative

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGapUniqueNormalForms

open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap

universe u v w

noncomputable section

/-! ## Reachability helpers -/

/-- A reachable pair lies in the equivalence closure. -/
theorem eqvGen_of_reach {T : Type u} {R : T → T → Prop} {x y : T} (h : Reach R x y) :
    Relation.EqvGen R x y := by
  rcases h with ⟨n, hn⟩
  induction hn with
  | zero x => exact Relation.EqvGen.refl x
  | succ hxy _ ih => exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hxy) ih

/-- A predicate closed backward along the relation passes from a reachable target to the source. -/
theorem reach_backward_invariant {T : Type u} {R : T → T → Prop} (P : T → Prop)
    (hstep : ∀ x y, R x y → P y → P x) {x z : T} (h : Reach R x z) : P z → P x := by
  rcases h with ⟨n, hn⟩
  induction hn with
  | zero => exact id
  | succ hxy _ ih => exact fun hz => hstep _ _ hxy (ih hz)

/-! ## Identification on finite carriers -/

/-- **UN→ is terminal multiplicity at most one at every element.** -/
theorem uniqueReachableNormalForms_iff_terminalMultiplicity_le_one {T : Type u} [Fintype T]
    (R : T → T → Prop) :
    UniqueReachableNormalForms R ↔ ∀ source, terminalMultiplicity R source ≤ 1 := by
  constructor
  · intro h source
    unfold terminalMultiplicity
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [mem_terminalSupport] at ha hb
    exact h source a b ha.1 ha.2 hb.1 hb.2
  · intro h s n₁ n₂ h₁ hn₁ h₂ hn₂
    have hle := h s
    unfold terminalMultiplicity at hle
    rw [Finset.card_le_one] at hle
    exact hle n₁ (mem_terminalSupport.mpr ⟨h₁, hn₁⟩) n₂ (mem_terminalSupport.mpr ⟨h₂, hn₂⟩)

/-- **UN→ is the absence of strict branching.** -/
theorem uniqueReachableNormalForms_iff_branchingFree {T : Type u} [Fintype T] (R : T → T → Prop) :
    UniqueReachableNormalForms R ↔ BranchingFree R := by
  rw [uniqueReachableNormalForms_iff_terminalMultiplicity_le_one]
  unfold BranchingFree BranchingAt
  constructor
  · intro h source hbr
    have := h source
    omega
  · intro h source
    have := h source
    omega

/-- At most one reachable normal form gives zero terminal Hartley entropy. -/
theorem terminalHartleyEntropy_eq_zero_of_le_one {T : Type u} [Fintype T] {R : T → T → Prop}
    {source : T} (h : terminalMultiplicity R source ≤ 1) : terminalHartleyEntropy R source = 0 := by
  unfold terminalHartleyEntropy
  rcases (by omega : terminalMultiplicity R source = 0 ∨ terminalMultiplicity R source = 1) with h0 | h1
  · rw [h0, Nat.cast_zero, Real.logb_zero]
  · rw [h1, Nat.cast_one, Real.logb_one]

/-- Two or more reachable normal forms give positive terminal Hartley entropy. -/
theorem terminalHartleyEntropy_pos_of_two_le {T : Type u} [Fintype T] {R : T → T → Prop}
    {source : T} (h : 2 ≤ terminalMultiplicity R source) : 0 < terminalHartleyEntropy R source := by
  unfold terminalHartleyEntropy
  refine Real.logb_pos (by norm_num) ?_
  have h2 : (2 : ℝ) ≤ (terminalMultiplicity R source : ℝ) := by exact_mod_cast h
  linarith

/-- At an element with at most one reachable normal form the gap is at most zero against every
nonnegative-gain channel. -/
theorem overproductionGap_nonpos_of_terminalMultiplicity_le_one {T : Type u} [Fintype T]
    {R : T → T → Prop} {source : T}
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (h : terminalMultiplicity R source ≤ 1) (hd : 0 ≤ deficit μ ν r) :
    overproductionGap R source μ ν r ≤ 0 := by
  unfold overproductionGap
  rw [terminalHartleyEntropy_eq_zero_of_le_one h]
  have := deficitBits_nonneg_of_nonneg μ ν r hd
  linarith

/-- **No boundary event against a zero-gain channel**, at every element. -/
def ZeroGainBoundaryEventFree {T : Type u} [Fintype T] (R : T → T → Prop) : Prop :=
  ∀ (source : T) {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ),
    deficit μ ν r = 0 → ¬ BoundaryEvent R source μ ν r

/-- **The gap is at most zero** at every element against every nonnegative-gain channel. -/
def GapNonpos {T : Type u} [Fintype T] (R : T → T → Prop) : Prop :=
  ∀ (source : T) {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ),
    0 ≤ deficit μ ν r → overproductionGap R source μ ν r ≤ 0

/-- **UN→ is the absence of boundary events against zero-gain channels.** The reverse direction uses the
echo channel, whose licensed gain is zero. -/
theorem uniqueReachableNormalForms_iff_zeroGainBoundaryEventFree {T : Type u} [Fintype T]
    (R : T → T → Prop) :
    UniqueReachableNormalForms R ↔ ZeroGainBoundaryEventFree R := by
  rw [uniqueReachableNormalForms_iff_branchingFree]
  unfold BranchingFree ZeroGainBoundaryEventFree
  constructor
  · intro h source _ _ _ _ _ _ μ ν r hd hev
    exact h source ((boundaryEvent_iff_branchingAt R source μ ν r hd).mp hev)
  · intro h source hbr
    exact h source unitSurface uniformChannelWeights echoChannel echoChannel_deficit_zero
      ((boundaryEvent_iff_branchingAt R source _ _ _ echoChannel_deficit_zero).mpr hbr)

/-- **UN→ is a nonpositive gap against every nonnegative-gain channel.** -/
theorem uniqueReachableNormalForms_iff_gapNonpos {T : Type u} [Fintype T] (R : T → T → Prop) :
    UniqueReachableNormalForms R ↔ GapNonpos R := by
  rw [uniqueReachableNormalForms_iff_terminalMultiplicity_le_one]
  unfold GapNonpos
  constructor
  · intro h source _ _ _ _ _ _ μ ν r hd
    exact overproductionGap_nonpos_of_terminalMultiplicity_le_one μ ν r (h source) hd
  · intro h source
    by_contra hgt
    have h2 : 2 ≤ terminalMultiplicity R source := by omega
    have hpos := terminalHartleyEntropy_pos_of_two_le h2
    have hgap := h source unitSurface uniformChannelWeights echoChannel
      (le_of_eq echoChannel_deficit_zero.symm)
    rw [overproductionGap_eq_hartley_of_zero_deficit R source _ _ _ echoChannel_deficit_zero] at hgap
    linarith

/-! ## UN= and the gap -/

/-- **UN= implies UN→** for every relation: a common source puts two reachable normal forms in one
equivalence class. -/
theorem uniqueReachableNormalForms_of_uniqueConvertibleNormalForms {T : Type u} {R : T → T → Prop}
    (h : UniqueConvertibleNormalForms R) : UniqueReachableNormalForms R := by
  intro s n₁ n₂ h₁ hn₁ h₂ hn₂
  exact h n₁ n₂ hn₁ hn₂
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (eqvGen_of_reach h₁)) (eqvGen_of_reach h₂))

/-- **UN= gives a nonpositive gap** at every element against every nonnegative-gain channel. -/
theorem gapNonpos_of_uniqueConvertibleNormalForms {T : Type u} [Fintype T] {R : T → T → Prop}
    (h : UniqueConvertibleNormalForms R) : GapNonpos R :=
  (uniqueReachableNormalForms_iff_gapNonpos R).mp
    (uniqueReachableNormalForms_of_uniqueConvertibleNormalForms h)

/-- **UN= excludes boundary events against zero-gain channels.** -/
theorem zeroGainBoundaryEventFree_of_uniqueConvertibleNormalForms {T : Type u} [Fintype T]
    {R : T → T → Prop} (h : UniqueConvertibleNormalForms R) : ZeroGainBoundaryEventFree R :=
  (uniqueReachableNormalForms_iff_zeroGainBoundaryEventFree R).mp
    (uniqueReachableNormalForms_of_uniqueConvertibleNormalForms h)

/-- **A boundary event refutes UN→**, against any nonnegative-gain channel. -/
theorem boundaryEvent_refutes_uniqueReachableNormalForms {T : Type u} [Fintype T]
    {R : T → T → Prop} {source : T} {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    {μ : W → ℝ} {ν : W → Cn → ℝ} {r : W → Cn → X → ℝ}
    (hd : 0 ≤ deficit μ ν r) (hev : BoundaryEvent R source μ ν r) :
    ¬ UniqueReachableNormalForms R := by
  intro h
  have hg := (uniqueReachableNormalForms_iff_gapNonpos R).mp h
  unfold GapNonpos at hg
  have := hg source μ ν r hd
  unfold BoundaryEvent at hev
  linarith

/-- **A boundary event refutes UN=**, against any nonnegative-gain channel. -/
theorem boundaryEvent_refutes_uniqueConvertibleNormalForms {T : Type u} [Fintype T]
    {R : T → T → Prop} {source : T} {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    {μ : W → ℝ} {ν : W → Cn → ℝ} {r : W → Cn → X → ℝ}
    (hd : 0 ≤ deficit μ ν r) (hev : BoundaryEvent R source μ ν r) :
    ¬ UniqueConvertibleNormalForms R :=
  fun h => boundaryEvent_refutes_uniqueReachableNormalForms hd hev
    (uniqueReachableNormalForms_of_uniqueConvertibleNormalForms h)

/-! ## The fence: equal gaps, different UN= -/

/-- Five elements. -/
inductive BridgeNode where
  | a
  | b
  | c
  | d
  | e
deriving DecidableEq, Fintype

/-- `a → b`, `a → c`, `c → c`, `d → c`, `d → e`. The path `b ← a → c ← d → e` joins `b` and `e`. -/
inductive BridgeStep : BridgeNode → BridgeNode → Prop where
  | ab : BridgeStep .a .b
  | ac : BridgeStep .a .c
  | cc : BridgeStep .c .c
  | dc : BridgeStep .d .c
  | de : BridgeStep .d .e

/-- `a → b`, `c → c`, `d → e`: the bridge relation with the two edges into `c` from `a` and `d` removed. -/
inductive SplitStep : BridgeNode → BridgeNode → Prop where
  | ab : SplitStep .a .b
  | cc : SplitStep .c .c
  | de : SplitStep .d .e

/-- The normal forms of `BridgeStep` are `b` and `e`. -/
theorem bridge_normalForm_iff (x : BridgeNode) :
    NormalForm BridgeStep x ↔ x = .b ∨ x = .e := by
  constructor
  · intro hx
    cases x with
    | a => exact absurd BridgeStep.ab (hx .b)
    | b => exact Or.inl rfl
    | c => exact absurd BridgeStep.cc (hx .c)
    | d => exact absurd BridgeStep.de (hx .e)
    | e => exact Or.inr rfl
  · rintro (rfl | rfl) <;> intro y h <;> cases h

/-- The normal forms of `SplitStep` are `b` and `e`. -/
theorem split_normalForm_iff (x : BridgeNode) :
    NormalForm SplitStep x ↔ x = .b ∨ x = .e := by
  constructor
  · intro hx
    cases x with
    | a => exact absurd SplitStep.ab (hx .b)
    | b => exact Or.inl rfl
    | c => exact absurd SplitStep.cc (hx .c)
    | d => exact absurd SplitStep.de (hx .e)
    | e => exact Or.inr rfl
  · rintro (rfl | rfl) <;> intro y h <;> cases h

/-- In `BridgeStep`, exactly `a` and `b` reach `b`. -/
theorem bridge_reach_b_iff (x : BridgeNode) : Reach BridgeStep x .b ↔ x = .a ∨ x = .b := by
  constructor
  · intro h
    refine reach_backward_invariant (fun z : BridgeNode => z = .a ∨ z = .b) ?_ h (Or.inr rfl)
    intro _ _ hpq hq
    cases hpq <;> rcases hq with hq | hq <;> first | exact Or.inl rfl | exact Or.inr rfl | cases hq
  · rintro (rfl | rfl)
    · exact reach_step BridgeStep.ab
    · exact reach_refl _

/-- In `BridgeStep`, exactly `d` and `e` reach `e`. -/
theorem bridge_reach_e_iff (x : BridgeNode) : Reach BridgeStep x .e ↔ x = .d ∨ x = .e := by
  constructor
  · intro h
    refine reach_backward_invariant (fun z : BridgeNode => z = .d ∨ z = .e) ?_ h (Or.inr rfl)
    intro _ _ hpq hq
    cases hpq <;> rcases hq with hq | hq <;> first | exact Or.inl rfl | exact Or.inr rfl | cases hq
  · rintro (rfl | rfl)
    · exact reach_step BridgeStep.de
    · exact reach_refl _

/-- In `SplitStep`, exactly `a` and `b` reach `b`. -/
theorem split_reach_b_iff (x : BridgeNode) : Reach SplitStep x .b ↔ x = .a ∨ x = .b := by
  constructor
  · intro h
    refine reach_backward_invariant (fun z : BridgeNode => z = .a ∨ z = .b) ?_ h (Or.inr rfl)
    intro _ _ hpq hq
    cases hpq <;> rcases hq with hq | hq <;> first | exact Or.inl rfl | exact Or.inr rfl | cases hq
  · rintro (rfl | rfl)
    · exact reach_step SplitStep.ab
    · exact reach_refl _

/-- In `SplitStep`, exactly `d` and `e` reach `e`. -/
theorem split_reach_e_iff (x : BridgeNode) : Reach SplitStep x .e ↔ x = .d ∨ x = .e := by
  constructor
  · intro h
    refine reach_backward_invariant (fun z : BridgeNode => z = .d ∨ z = .e) ?_ h (Or.inr rfl)
    intro _ _ hpq hq
    cases hpq <;> rcases hq with hq | hq <;> first | exact Or.inl rfl | exact Or.inr rfl | cases hq
  · rintro (rfl | rfl)
    · exact reach_step SplitStep.de
    · exact reach_refl _

/-- **The two relations have the same terminal support at every element.** -/
theorem bridge_terminalSupport_eq_split (source : BridgeNode) :
    terminalSupport BridgeStep source = terminalSupport SplitStep source := by
  ext n
  rw [mem_terminalSupport, mem_terminalSupport, bridge_normalForm_iff, split_normalForm_iff]
  constructor
  · rintro ⟨hr, hn | hn⟩ <;> subst hn
    · exact ⟨(split_reach_b_iff source).mpr ((bridge_reach_b_iff source).mp hr), Or.inl rfl⟩
    · exact ⟨(split_reach_e_iff source).mpr ((bridge_reach_e_iff source).mp hr), Or.inr rfl⟩
  · rintro ⟨hr, hn | hn⟩ <;> subst hn
    · exact ⟨(bridge_reach_b_iff source).mpr ((split_reach_b_iff source).mp hr), Or.inl rfl⟩
    · exact ⟨(bridge_reach_e_iff source).mpr ((split_reach_e_iff source).mp hr), Or.inr rfl⟩

/-- The two relations have the same terminal multiplicity at every element. -/
theorem bridge_terminalMultiplicity_eq_split (source : BridgeNode) :
    terminalMultiplicity BridgeStep source = terminalMultiplicity SplitStep source := by
  unfold terminalMultiplicity
  rw [bridge_terminalSupport_eq_split]

/-- **The two relations have the same gap** at every element against every channel. -/
theorem bridge_overproductionGap_eq_split (source : BridgeNode)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) :
    overproductionGap BridgeStep source μ ν r = overproductionGap SplitStep source μ ν r := by
  unfold overproductionGap terminalHartleyEntropy
  rw [bridge_terminalMultiplicity_eq_split]

/-- `BridgeStep` has UN→: `a` and `b` reach only `b`, `d` and `e` reach only `e`, and `c` reaches no normal
form. -/
theorem bridge_uniqueReachableNormalForms : UniqueReachableNormalForms BridgeStep := by
  intro s n₁ n₂ h₁ hn₁ h₂ hn₂
  rcases (bridge_normalForm_iff n₁).mp hn₁ with rfl | rfl <;>
    rcases (bridge_normalForm_iff n₂).mp hn₂ with rfl | rfl
  · rfl
  · rcases (bridge_reach_b_iff s).mp h₁ with rfl | rfl <;>
      rcases (bridge_reach_e_iff _).mp h₂ with h | h <;> cases h
  · rcases (bridge_reach_e_iff s).mp h₁ with rfl | rfl <;>
      rcases (bridge_reach_b_iff _).mp h₂ with h | h <;> cases h
  · rfl

/-- The classes `{a, b}`, `{c}`, `{d, e}` of `SplitStep`. -/
def splitClass : BridgeNode → Nat
  | .a => 0
  | .b => 0
  | .c => 1
  | .d => 2
  | .e => 2

/-- The equivalence closure of `SplitStep` stays inside one class. -/
theorem splitClass_eq_of_eqvGen {x y : BridgeNode} (h : Relation.EqvGen SplitStep x y) :
    splitClass x = splitClass y := by
  induction h with
  | rel _ _ hxy => cases hxy <;> rfl
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **`SplitStep` has UN=.** -/
theorem split_uniqueConvertibleNormalForms : UniqueConvertibleNormalForms SplitStep := by
  intro n₁ n₂ hn₁ hn₂ hconv
  have hcls := splitClass_eq_of_eqvGen hconv
  rcases (split_normalForm_iff n₁).mp hn₁ with rfl | rfl <;>
    rcases (split_normalForm_iff n₂).mp hn₂ with rfl | rfl
  · rfl
  · exact absurd hcls (by decide)
  · exact absurd hcls (by decide)
  · rfl

/-- The path `b ← a → c ← d → e` in the equivalence closure of `BridgeStep`. -/
theorem bridge_eqvGen_b_e : Relation.EqvGen BridgeStep .b .e :=
  Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ BridgeStep.ab))
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ BridgeStep.ac)
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ BridgeStep.dc))
        (Relation.EqvGen.rel _ _ BridgeStep.de)))

/-- **`BridgeStep` fails UN=**: `b` and `e` are distinct normal forms in one equivalence class. -/
theorem bridge_not_uniqueConvertibleNormalForms : ¬ UniqueConvertibleNormalForms BridgeStep := by
  intro h
  unfold UniqueConvertibleNormalForms at h
  have hbe := h .b .e ((bridge_normalForm_iff _).mpr (Or.inl rfl))
    ((bridge_normalForm_iff _).mpr (Or.inr rfl)) bridge_eqvGen_b_e
  exact absurd hbe (by decide)

/-- **The fence.** Two relations on one finite carrier have the same gap at every element against every
channel, and exactly one of them has UN=. The gap therefore leaves UN= undetermined. -/
theorem overproductionGap_leaves_uniqueConvertibleNormalForms_undetermined :
    (∀ (source : BridgeNode) {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
      (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ),
      overproductionGap BridgeStep source μ ν r = overproductionGap SplitStep source μ ν r) ∧
    UniqueConvertibleNormalForms SplitStep ∧ ¬ UniqueConvertibleNormalForms BridgeStep :=
  ⟨fun source => bridge_overproductionGap_eq_split source,
    split_uniqueConvertibleNormalForms, bridge_not_uniqueConvertibleNormalForms⟩

/-- **UN→ fails to imply UN= on finite relations.** -/
theorem uniqueReachableNormalForms_not_imp_uniqueConvertibleNormalForms :
    ¬ ∀ (T : Type) [Fintype T] (R : T → T → Prop),
      UniqueReachableNormalForms R → UniqueConvertibleNormalForms R := by
  intro h
  exact bridge_not_uniqueConvertibleNormalForms
    (h BridgeNode BridgeStep bridge_uniqueReachableNormalForms)

/-- **A nonpositive gap fails to imply UN= on finite relations.** -/
theorem gapNonpos_not_imp_uniqueConvertibleNormalForms :
    ¬ ∀ (T : Type) [Fintype T] (R : T → T → Prop), GapNonpos R → UniqueConvertibleNormalForms R := by
  intro h
  exact bridge_not_uniqueConvertibleNormalForms
    (h BridgeNode BridgeStep
      ((uniqueReachableNormalForms_iff_gapNonpos BridgeStep).mp bridge_uniqueReachableNormalForms))

/-! ## Transport to term rewriting -/

section Rewriting

open OperatorKO7.Meta.Rewriting

variable {sigma : Type u} {nu : Type v}

/-- **The rewrite relation read on a set of terms**: `x` steps to `y` when the term of `x` rewrites in one
step to the term of `y`. -/
def fragmentStep {F : Type w} (R : TRS sigma nu) (ι : F → Term sigma nu) : F → F → Prop :=
  fun x y => Step R (ι x) (ι y)

/-- A path in a fragment is a rewrite sequence. -/
theorem stepStar_of_fragment_reach {F : Type w} {R : TRS sigma nu} {ι : F → Term sigma nu}
    {x y : F} (h : Reach (fragmentStep R ι) x y) : StepStar R (ι x) (ι y) := by
  rcases h with ⟨n, hn⟩
  induction hn with
  | zero => exact StepStar.refl R _
  | succ hxy _ ih => exact StepStar.head hxy ih

/-- A rewrite sequence out of a step-closed fragment stays in the fragment. -/
theorem fragment_reach_of_stepStar {F : Type w} {R : TRS sigma nu} {ι : F → Term sigma nu}
    (hclosed : ∀ x u, Step R (ι x) u → ∃ y, ι y = u) {x : F} {t : Term sigma nu}
    (h : StepStar R (ι x) t) : ∃ y, ι y = t ∧ Reach (fragmentStep R ι) x y := by
  induction h with
  | refl => exact ⟨x, rfl, reach_refl x⟩
  | tail _ hstep ih =>
      obtain ⟨y, rfl, hy⟩ := ih
      obtain ⟨z, hz⟩ := hclosed y _ hstep
      refine ⟨z, hz, reach_trans hy (reach_step ?_)⟩
      show Step R (ι y) (ι z)
      rw [hz]
      exact hstep

/-- **Normal forms of a step-closed fragment are normal forms of the system.** -/
theorem fragment_normalForm_iff {F : Type w} {R : TRS sigma nu} {ι : F → Term sigma nu}
    (hclosed : ∀ x u, Step R (ι x) u → ∃ y, ι y = u) (x : F) :
    NormalForm (fragmentStep R ι) x ↔ UniqueNormalization.NormalForm R (ι x) := by
  constructor
  · intro hx u hu
    obtain ⟨y, rfl⟩ := hclosed x u hu
    exact hx y hu
  · intro hx y hy
    exact hx (ι y) hy

/-- **UN→ of the system gives UN→ on every injective step-closed fragment.** -/
theorem fragment_uniqueReachableNormalForms_of_UNred {F : Type w} {R : TRS sigma nu}
    {ι : F → Term sigma nu} (hinj : Function.Injective ι)
    (hclosed : ∀ x u, Step R (ι x) u → ∃ y, ι y = u) (hun : UniqueNormalization.UNred R) :
    UniqueReachableNormalForms (fragmentStep R ι) := by
  intro s n₁ n₂ h₁ hn₁ h₂ hn₂
  exact hinj (hun (ι s) (ι n₁) (ι n₂) ((fragment_normalForm_iff hclosed n₁).mp hn₁)
    ((fragment_normalForm_iff hclosed n₂).mp hn₂) (stepStar_of_fragment_reach h₁)
    (stepStar_of_fragment_reach h₂))

/-- **UN→ of the system makes the gap of every finite injective step-closed fragment nonpositive.** -/
theorem fragment_gapNonpos_of_UNred {F : Type w} [Fintype F] {R : TRS sigma nu}
    {ι : F → Term sigma nu} (hinj : Function.Injective ι)
    (hclosed : ∀ x u, Step R (ι x) u → ∃ y, ι y = u) (hun : UniqueNormalization.UNred R) :
    GapNonpos (fragmentStep R ι) :=
  (uniqueReachableNormalForms_iff_gapNonpos _).mp
    (fragment_uniqueReachableNormalForms_of_UNred hinj hclosed hun)

/-- **UN= of the system makes the gap of every finite injective step-closed fragment nonpositive.** -/
theorem fragment_gapNonpos_of_UNconv {F : Type w} [Fintype F] {R : TRS sigma nu}
    {ι : F → Term sigma nu} (hinj : Function.Injective ι)
    (hclosed : ∀ x u, Step R (ι x) u → ∃ y, ι y = u) (hun : UniqueNormalization.UNconv R) :
    GapNonpos (fragmentStep R ι) :=
  fragment_gapNonpos_of_UNred hinj hclosed (UniqueNormalization.UNred_of_UNconv hun)

/-- **A boundary event on a fragment refutes UN→ of the system.** -/
theorem not_UNred_of_fragment_boundaryEvent {F : Type w} [Fintype F] {R : TRS sigma nu}
    {ι : F → Term sigma nu} (hinj : Function.Injective ι)
    (hclosed : ∀ x u, Step R (ι x) u → ∃ y, ι y = u) {source : F}
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    {μ : W → ℝ} {ν : W → Cn → ℝ} {r : W → Cn → X → ℝ}
    (hd : 0 ≤ deficit μ ν r) (hev : BoundaryEvent (fragmentStep R ι) source μ ν r) :
    ¬ UniqueNormalization.UNred R :=
  fun hun => boundaryEvent_refutes_uniqueReachableNormalForms hd hev
    (fragment_uniqueReachableNormalForms_of_UNred hinj hclosed hun)

/-- **A boundary event on a fragment refutes UN= of the system.** -/
theorem not_UNconv_of_fragment_boundaryEvent {F : Type w} [Fintype F] {R : TRS sigma nu}
    {ι : F → Term sigma nu} (hinj : Function.Injective ι)
    (hclosed : ∀ x u, Step R (ι x) u → ∃ y, ι y = u) {source : F}
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    {μ : W → ℝ} {ν : W → Cn → ℝ} {r : W → Cn → X → ℝ}
    (hd : 0 ≤ deficit μ ν r) (hev : BoundaryEvent (fragmentStep R ι) source μ ν r) :
    ¬ UniqueNormalization.UNconv R :=
  fun hun => not_UNred_of_fragment_boundaryEvent hinj hclosed hd hev
    (UniqueNormalization.UNred_of_UNconv hun)

/-- Every term lies in the image of an injective map from a finite type whose image is closed under one
rewrite step. -/
def HasFiniteStepClosedFragments (R : TRS sigma nu) : Prop :=
  ∀ t : Term sigma nu, ∃ (F : Type) (_ : Fintype F) (ι : F → Term sigma nu) (x : F),
    Function.Injective ι ∧ (∀ y u, Step R (ι y) u → ∃ z, ι z = u) ∧ ι x = t

/-- Every finite injective step-closed fragment has a nonpositive gap at every element against every
nonnegative-gain channel. -/
def FragmentGapNonpos (R : TRS sigma nu) : Prop :=
  ∀ (F : Type) [Fintype F] (ι : F → Term sigma nu), Function.Injective ι →
    (∀ y u, Step R (ι y) u → ∃ z, ι z = u) → GapNonpos (fragmentStep R ι)

/-- **UN→ of the system gives a nonpositive gap on every finite injective step-closed fragment.** -/
theorem fragmentGapNonpos_of_UNred {R : TRS sigma nu} (hun : UniqueNormalization.UNred R) :
    FragmentGapNonpos R := by
  intro _ _ _ hinj hclosed
  exact fragment_gapNonpos_of_UNred hinj hclosed hun

/-- **UN→ is a nonpositive gap on every fragment, for systems whose terms lie in finite step-closed
fragments.** The premise supplies a fragment containing the source of any two reachable normal forms. -/
theorem UNred_iff_fragmentGapNonpos {R : TRS sigma nu} (hfin : HasFiniteStepClosedFragments R) :
    UniqueNormalization.UNred R ↔ FragmentGapNonpos R := by
  refine ⟨fragmentGapNonpos_of_UNred, ?_⟩
  intro hgap s t u ht hu hst hsu
  obtain ⟨F, _, ι, x, hinj, hclosed, rfl⟩ := hfin s
  obtain ⟨y₁, rfl, hy₁⟩ := fragment_reach_of_stepStar hclosed hst
  obtain ⟨y₂, rfl, hy₂⟩ := fragment_reach_of_stepStar hclosed hsu
  have huniq : UniqueReachableNormalForms (fragmentStep R ι) :=
    (uniqueReachableNormalForms_iff_gapNonpos _).mpr (hgap F ι hinj hclosed)
  exact congrArg ι (huniq x y₁ y₂ hy₁ ((fragment_normalForm_iff hclosed y₁).mpr ht) hy₂
    ((fragment_normalForm_iff hclosed y₂).mpr hu))

/-- The empty system admits no rewrite step. -/
theorem step_nil_false {s t : Term sigma nu} : ¬ Step ([] : TRS sigma nu) s t := by
  intro h
  induction h with
  | root hr =>
      obtain ⟨_, hmem, -⟩ := hr
      simp at hmem
  | arg _ _ _ _ ih => exact ih

/-- The premise of `UNred_iff_fragmentGapNonpos` is satisfiable: in the empty system every term is its own
one-element fragment. -/
theorem nil_hasFiniteStepClosedFragments : HasFiniteStepClosedFragments ([] : TRS sigma nu) := by
  intro t
  refine ⟨Unit, inferInstance, fun _ => t, (), ?_, ?_, rfl⟩
  · intro _ _ _
    rfl
  · intro _ _ h
    exact absurd h step_nil_false

end Rewriting

/-! ## Rewriting instances -/

section Instances

open OperatorKO7.Meta.Rewriting

/-- The rule rewriting the constant `k` to the constant `l`. -/
def constRule (k l : Nat) : Rule Nat Nat := ⟨.app k [], .app l [], rfl⟩

/-- The system of constant rules listed by `pairs`. -/
def constTRS (pairs : List (Nat × Nat)) : TRS Nat Nat := pairs.map (fun p => constRule p.1 p.2)

/-- **One step from a constant** in a system of constant rules. -/
theorem step_const_iff (pairs : List (Nat × Nat)) (k : Nat) (u : Term Nat Nat) :
    Step (constTRS pairs) (.app k []) u ↔ ∃ l, (k, l) ∈ pairs ∧ u = .app l [] := by
  constructor
  · intro h
    rcases UniqueNormalization.Step.app_inv h with hr | ⟨_, _, _, _, hargs, -, -⟩
    · obtain ⟨rule, hrule, σ, hs, hu⟩ := hr
      rw [constTRS, List.mem_map] at hrule
      obtain ⟨⟨k', l⟩, hmem, rfl⟩ := hrule
      simp only [constRule, Subst.apply_app, Subst.applyList_nil, Term.app.injEq, and_true] at hs hu
      subst hs
      exact ⟨l, hmem, hu⟩
    · simp at hargs
  · rintro ⟨l, hmem, rfl⟩
    exact Step.rootStep_step (constTRS pairs) (rule := constRule k l)
      (List.mem_map.mpr ⟨(k, l), hmem, rfl⟩) Subst.id

/-- A constant is a normal form exactly when no listed rule starts at it. -/
theorem normalForm_const_iff (pairs : List (Nat × Nat)) (k : Nat) :
    UniqueNormalization.NormalForm (constTRS pairs) (.app k []) ↔ ∀ l, (k, l) ∉ pairs := by
  constructor
  · intro h l hmem
    exact h (.app l []) ((step_const_iff pairs k _).mpr ⟨l, hmem, rfl⟩)
  · intro h u hu
    obtain ⟨l, hmem, -⟩ := (step_const_iff pairs k u).mp hu
    exact h l hmem

/-- Symbol codes `a = 0`, `b = 1`, `c = 2`, `d = 3`, `e = 4`. -/
def nodeCode : BridgeNode → Nat
  | .a => 0
  | .b => 1
  | .c => 2
  | .d => 3
  | .e => 4

/-- The constant term of an element. -/
def nodeTerm (x : BridgeNode) : Term Nat Nat := .app (nodeCode x) []

/-- Distinct elements have distinct constants. -/
theorem nodeTerm_injective : Function.Injective nodeTerm := by
  intro x y h
  simp only [nodeTerm, Term.app.injEq, and_true] at h
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

/-- **Closure of the constant fragment**: every right-hand side of a listed rule is an element's constant. -/
theorem constTRS_fragment_closed (pairs : List (Nat × Nat))
    (hcodes : ∀ p ∈ pairs, ∃ y : BridgeNode, nodeCode y = p.2) :
    ∀ x u, Step (constTRS pairs) (nodeTerm x) u → ∃ y, nodeTerm y = u := by
  intro x u h
  obtain ⟨l, hmem, rfl⟩ := (step_const_iff pairs (nodeCode x) u).mp h
  obtain ⟨y, hy⟩ := hcodes _ hmem
  exact ⟨y, congrArg (fun k => Term.app k []) hy⟩

/-- `a → b`, `a → c`. -/
def forkPairs : List (Nat × Nat) := [(0, 1), (0, 2)]

/-- `a → b`, `a → c`, `c → c`, `d → c`, `d → e`. -/
def bridgePairs : List (Nat × Nat) := [(0, 1), (0, 2), (2, 2), (3, 2), (3, 4)]

/-- The system `a → b`, `a → c` over constant symbols. -/
def forkTRS : TRS Nat Nat := constTRS forkPairs

/-- The system `a → b`, `a → c`, `c → c`, `d → c`, `d → e` over constant symbols. -/
def bridgeTRS : TRS Nat Nat := constTRS bridgePairs

/-- Every right-hand side of `forkPairs` is an element's constant. -/
theorem forkPairs_codes : ∀ p ∈ forkPairs, ∃ y : BridgeNode, nodeCode y = p.2 := by
  intro p hp
  simp only [forkPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨.b, rfl⟩
  · exact ⟨.c, rfl⟩

/-- Every right-hand side of `bridgePairs` is an element's constant. -/
theorem bridgePairs_codes : ∀ p ∈ bridgePairs, ∃ y : BridgeNode, nodeCode y = p.2 := by
  intro p hp
  simp only [bridgePairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact ⟨.b, rfl⟩
  · exact ⟨.c, rfl⟩
  · exact ⟨.c, rfl⟩
  · exact ⟨.c, rfl⟩
  · exact ⟨.e, rfl⟩

/-- **`forkTRS` raises a one-bit boundary event** at `a` on its constants, against the echo channel. -/
theorem forkTRS_fragment_boundaryEvent :
    BoundaryEvent (fragmentStep forkTRS nodeTerm) .a unitSurface uniformChannelWeights echoChannel := by
  have hclosed := constTRS_fragment_closed forkPairs forkPairs_codes
  have hab : fragmentStep forkTRS nodeTerm .a .b :=
    (step_const_iff forkPairs 0 _).mpr ⟨1, by simp [forkPairs], rfl⟩
  have hac : fragmentStep forkTRS nodeTerm .a .c :=
    (step_const_iff forkPairs 0 _).mpr ⟨2, by simp [forkPairs], rfl⟩
  have hnb : NormalForm (fragmentStep forkTRS nodeTerm) .b :=
    (fragment_normalForm_iff hclosed .b).mpr
      ((normalForm_const_iff forkPairs 1).mpr (fun l => by simp [forkPairs]))
  have hnc : NormalForm (fragmentStep forkTRS nodeTerm) .c :=
    (fragment_normalForm_iff hclosed .c).mpr
      ((normalForm_const_iff forkPairs 2).mpr (fun l => by simp [forkPairs]))
  have hmult : 2 ≤ terminalMultiplicity (fragmentStep forkTRS nodeTerm) .a := by
    have h1 : 1 < (terminalSupport (fragmentStep forkTRS nodeTerm) .a).card :=
      Finset.one_lt_card.mpr ⟨.b, mem_terminalSupport.mpr ⟨reach_step hab, hnb⟩,
        .c, mem_terminalSupport.mpr ⟨reach_step hac, hnc⟩, by decide⟩
    unfold terminalMultiplicity
    omega
  exact boundary_event_of_zero_deficit_of_two_terminals _ _ _ _ _ echoChannel_deficit_zero hmult

/-- **`forkTRS` fails UN=**, by the fragment refutation. -/
theorem forkTRS_not_UNconv : ¬ UniqueNormalization.UNconv forkTRS :=
  not_UNconv_of_fragment_boundaryEvent nodeTerm_injective
    (constTRS_fragment_closed forkPairs forkPairs_codes)
    (le_of_eq echoChannel_deficit_zero.symm) forkTRS_fragment_boundaryEvent

/-- On its constants, `bridgeTRS` steps exactly along `BridgeStep`. -/
theorem bridgeTRS_fragmentStep_iff (x y : BridgeNode) :
    fragmentStep bridgeTRS nodeTerm x y ↔ BridgeStep x y := by
  show Step (constTRS bridgePairs) (.app (nodeCode x) []) (.app (nodeCode y) []) ↔ BridgeStep x y
  rw [step_const_iff]
  constructor
  · rintro ⟨l, hmem, hl⟩
    simp only [Term.app.injEq, and_true] at hl
    subst hl
    cases x <;> cases y <;> first | constructor | exact absurd hmem (by decide)
  · intro h
    cases h <;> exact ⟨_, by decide, rfl⟩

/-- The constant fragment of `bridgeTRS` is the relation `BridgeStep`. -/
theorem bridgeTRS_fragmentStep_eq : fragmentStep bridgeTRS nodeTerm = BridgeStep := by
  funext x y
  exact propext (bridgeTRS_fragmentStep_iff x y)

/-- The constant fragment of `bridgeTRS` is closed under one rewrite step. -/
theorem bridgeTRS_fragment_closed : ∀ x u, Step bridgeTRS (nodeTerm x) u → ∃ y, nodeTerm y = u :=
  constTRS_fragment_closed bridgePairs bridgePairs_codes

/-- The gap of the constant fragment of `bridgeTRS` is nonpositive. -/
theorem bridgeTRS_fragment_gapNonpos : GapNonpos (fragmentStep bridgeTRS nodeTerm) := by
  rw [bridgeTRS_fragmentStep_eq]
  exact (uniqueReachableNormalForms_iff_gapNonpos BridgeStep).mp bridge_uniqueReachableNormalForms

/-- `b` is a normal form of `bridgeTRS`. -/
theorem bridgeTRS_normalForm_b : UniqueNormalization.NormalForm bridgeTRS (nodeTerm .b) :=
  (normalForm_const_iff bridgePairs 1).mpr (fun l => by simp [bridgePairs])

/-- `e` is a normal form of `bridgeTRS`. -/
theorem bridgeTRS_normalForm_e : UniqueNormalization.NormalForm bridgeTRS (nodeTerm .e) :=
  (normalForm_const_iff bridgePairs 4).mpr (fun l => by simp [bridgePairs])

/-- The conversion `b ← a → c ← d → e` in `bridgeTRS`. -/
theorem bridgeTRS_conv_b_e : UniqueNormalization.conv bridgeTRS (nodeTerm .b) (nodeTerm .e) := by
  have hab : Step bridgeTRS (nodeTerm .a) (nodeTerm .b) := (bridgeTRS_fragmentStep_iff .a .b).mpr .ab
  have hac : Step bridgeTRS (nodeTerm .a) (nodeTerm .c) := (bridgeTRS_fragmentStep_iff .a .c).mpr .ac
  have hdc : Step bridgeTRS (nodeTerm .d) (nodeTerm .c) := (bridgeTRS_fragmentStep_iff .d .c).mpr .dc
  have hde : Step bridgeTRS (nodeTerm .d) (nodeTerm .e) := (bridgeTRS_fragmentStep_iff .d .e).mpr .de
  have h1 : UniqueNormalization.conv bridgeTRS (nodeTerm .b) (nodeTerm .a) :=
    UniqueNormalization.conv.symm (UniqueNormalization.conv.of_step hab)
  have h2 : UniqueNormalization.conv bridgeTRS (nodeTerm .a) (nodeTerm .c) :=
    UniqueNormalization.conv.of_step hac
  have h3 : UniqueNormalization.conv bridgeTRS (nodeTerm .c) (nodeTerm .d) :=
    UniqueNormalization.conv.symm (UniqueNormalization.conv.of_step hdc)
  have h4 : UniqueNormalization.conv bridgeTRS (nodeTerm .d) (nodeTerm .e) :=
    UniqueNormalization.conv.of_step hde
  exact UniqueNormalization.conv.trans h1
    (UniqueNormalization.conv.trans h2 (UniqueNormalization.conv.trans h3 h4))

/-- **`bridgeTRS` fails UN=.** -/
theorem bridgeTRS_not_UNconv : ¬ UniqueNormalization.UNconv bridgeTRS := by
  intro h
  unfold UniqueNormalization.UNconv at h
  have hbe := h (nodeTerm .b) (nodeTerm .e) bridgeTRS_normalForm_b bridgeTRS_normalForm_e
    bridgeTRS_conv_b_e
  exact absurd (nodeTerm_injective hbe) (by decide)

/-- **The rewriting fence.** The constants of `bridgeTRS` form an injective step-closed fragment with a
nonpositive gap at every element against every nonnegative-gain channel, the two normal forms `b` and `e` and
their conversion lie in that fragment, and `bridgeTRS` fails UN=. -/
theorem bridgeTRS_fragment_gapNonpos_and_not_UNconv :
    Function.Injective nodeTerm ∧
    (∀ x u, Step bridgeTRS (nodeTerm x) u → ∃ y, nodeTerm y = u) ∧
    GapNonpos (fragmentStep bridgeTRS nodeTerm) ∧
    UniqueNormalization.NormalForm bridgeTRS (nodeTerm .b) ∧
    UniqueNormalization.NormalForm bridgeTRS (nodeTerm .e) ∧
    UniqueNormalization.conv bridgeTRS (nodeTerm .b) (nodeTerm .e) ∧
    nodeTerm .b ≠ nodeTerm .e ∧
    ¬ UniqueNormalization.UNconv bridgeTRS :=
  ⟨nodeTerm_injective, bridgeTRS_fragment_closed, bridgeTRS_fragment_gapNonpos,
    bridgeTRS_normalForm_b, bridgeTRS_normalForm_e, bridgeTRS_conv_b_e,
    fun h => absurd (nodeTerm_injective h) (by decide), bridgeTRS_not_UNconv⟩

end Instances

end

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGapUniqueNormalForms
