import OperatorKO7.Meta.DistinctionBoundary.Quantitative.Core
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log

/-!
# Terminal multiplicity and structural confluence entropy

For a finite carrier, `terminalSupport R source` is the set of reachable `R`-normal forms. Under
`NormalizingAt R source`, source confluence is equivalent to support cardinality one. The module also
defines the base-two logarithm of terminal multiplicity and the corresponding `Nat.clog 2` value.
All abstract results use caller-supplied relations and the `Reach` closure from `Core`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u

noncomputable section

/-- Reachable normal forms below one source, on a finite carrier. -/
def terminalSupport {T : Type u} [Fintype T] (R : T -> T -> Prop) (source : T) : Finset T := by
  classical
  exact Finset.univ.filter (fun n => Reach R source n ∧ NormalForm R n)

@[simp]
theorem mem_terminalSupport {T : Type u} [Fintype T] {R : T -> T -> Prop}
    {source n : T} :
    n ∈ terminalSupport R source ↔ Reach R source n ∧ NormalForm R n := by
  classical
  simp [terminalSupport]

/-- The number of reachable normal forms below `source`. -/
def terminalMultiplicity {T : Type u} [Fintype T]
    (R : T -> T -> Prop) (source : T) : Nat :=
  (terminalSupport R source).card

/-- Local normalization supplies at least one reachable normal form. -/
theorem terminalSupport_nonempty_of_normalizingAt {T : Type u} [Fintype T]
    {R : T -> T -> Prop} {source : T} (hnorm : NormalizingAt R source) :
    (terminalSupport R source).Nonempty := by
  rcases hnorm source (reach_refl source) with ⟨n, hnReach, hnNormal⟩
  exact ⟨n, mem_terminalSupport.mpr ⟨hnReach, hnNormal⟩⟩

/-- Local normalization makes terminal multiplicity strictly positive. -/
theorem terminalMultiplicity_pos_of_normalizingAt {T : Type u} [Fintype T]
    {R : T -> T -> Prop} {source : T} (hnorm : NormalizingAt R source) :
    0 < terminalMultiplicity R source := by
  exact Finset.card_pos.mpr (terminalSupport_nonempty_of_normalizingAt hnorm)

/-- Source confluence and local normalization give terminal multiplicity one. -/
theorem terminalMultiplicity_eq_one_of_confluentAt {T : Type u} [Fintype T]
    {R : T -> T -> Prop} {source : T} (hnorm : NormalizingAt R source)
    (hconf : ConfluentAt R source) : terminalMultiplicity R source = 1 := by
  classical
  rcases terminalSupport_nonempty_of_normalizingAt hnorm with ⟨n, hn⟩
  unfold terminalMultiplicity
  apply Finset.card_eq_one.mpr
  refine ⟨n, ?_⟩
  ext x
  constructor
  · intro hx
    have hxData := mem_terminalSupport.mp hx
    have hnData := mem_terminalSupport.mp hn
    have hxn : x = n :=
      unique_normalForm_of_confluentAt hconf
        hxData.1 hxData.2 hnData.1 hnData.2
    simp [hxn]
  · intro hx
    have hxn : x = n := by simpa using hx
    simpa [hxn] using hn

/-- Terminal multiplicity one plus local normalization implies source confluence. -/
theorem confluentAt_of_terminalMultiplicity_eq_one {T : Type u} [Fintype T]
    {R : T -> T -> Prop} {source : T} (hnorm : NormalizingAt R source)
    (hmult : terminalMultiplicity R source = 1) : ConfluentAt R source := by
  classical
  apply confluentAt_of_unique_normalForms hnorm
  intro n1 n2 h1 hn1 h2 hn2
  have hs1 : n1 ∈ terminalSupport R source :=
    mem_terminalSupport.mpr ⟨h1, hn1⟩
  have hs2 : n2 ∈ terminalSupport R source :=
    mem_terminalSupport.mpr ⟨h2, hn2⟩
  have hcard : (terminalSupport R source).card = 1 := hmult
  rcases Finset.card_eq_one.mp hcard with ⟨n, hsupp⟩
  have hn1eq : n1 = n := by
    rw [hsupp] at hs1
    simpa using hs1
  have hn2eq : n2 = n := by
    rw [hsupp] at hs2
    simpa using hs2
  exact hn1eq.trans hn2eq.symm

/-- Multiplicity one characterizes source confluence under the explicit local
normalization premise. -/
theorem confluentAt_iff_terminalMultiplicity_eq_one {T : Type u} [Fintype T]
    {R : T -> T -> Prop} {source : T} (hnorm : NormalizingAt R source) :
    ConfluentAt R source ↔ terminalMultiplicity R source = 1 :=
  ⟨terminalMultiplicity_eq_one_of_confluentAt hnorm,
   confluentAt_of_terminalMultiplicity_eq_one hnorm⟩

/-- Base-two logarithm of the reachable terminal-support cardinality. -/
def terminalHartleyEntropy {T : Type u} [Fintype T]
    (R : T -> T -> Prop) (source : T) : Real :=
  Real.logb 2 (terminalMultiplicity R source : Real)

/-- Base-two ceiling logarithm of the reachable terminal-support cardinality. -/
def terminalCeilLog2 {T : Type u} [Fintype T]
    (R : T -> T -> Prop) (source : T) : Nat :=
  Nat.clog 2 (terminalMultiplicity R source)

/-- Positive terminal multiplicity makes zero Hartley entropy equivalent to
multiplicity one. -/
theorem terminalHartleyEntropy_eq_zero_iff_multiplicity_eq_one
    {T : Type u} [Fintype T] {R : T -> T -> Prop} {source : T}
    (hnorm : NormalizingAt R source) :
    terminalHartleyEntropy R source = 0 ↔ terminalMultiplicity R source = 1 := by
  have hmpos : 0 < terminalMultiplicity R source :=
    terminalMultiplicity_pos_of_normalizingAt hnorm
  constructor
  · intro hzero
    unfold terminalHartleyEntropy at hzero
    rcases Real.logb_eq_zero.mp hzero with hb0 | hb1 | hbneg | hm0 | hm1 | hmneg
    · norm_num at hb0
    · norm_num at hb1
    · norm_num at hbneg
    · have : terminalMultiplicity R source = 0 := by exact_mod_cast hm0
      omega
    · exact_mod_cast hm1
    · have hnonneg : (0 : Real) ≤ (terminalMultiplicity R source : Real) := by positivity
      linarith
  · intro hm
    simp [terminalHartleyEntropy, hm, Real.logb_one]

/-- Under local normalization, characterize zero terminal Hartley entropy by source confluence. -/
theorem terminalHartleyEntropy_eq_zero_iff_confluentAt
    {T : Type u} [Fintype T] {R : T -> T -> Prop} {source : T}
    (hnorm : NormalizingAt R source) :
    terminalHartleyEntropy R source = 0 ↔ ConfluentAt R source := by
  rw [terminalHartleyEntropy_eq_zero_iff_multiplicity_eq_one hnorm]
  exact (confluentAt_iff_terminalMultiplicity_eq_one hnorm).symm

/-- Under local normalization, characterize zero `terminalCeilLog2` by source confluence. -/
theorem terminalCeilLog2_eq_zero_iff_confluentAt
    {T : Type u} [Fintype T] {R : T -> T -> Prop} {source : T}
    (hnorm : NormalizingAt R source) :
    terminalCeilLog2 R source = 0 ↔ ConfluentAt R source := by
  have hmpos : 0 < terminalMultiplicity R source :=
    terminalMultiplicity_pos_of_normalizingAt hnorm
  constructor
  · intro hzero
    have hmle : terminalMultiplicity R source ≤ 1 := by
      by_contra hnot
      have hm2 : 2 ≤ terminalMultiplicity R source := by omega
      have hclog : 0 < Nat.clog 2 (terminalMultiplicity R source) :=
        Nat.clog_pos (by omega) hm2
      exact (Nat.ne_of_gt hclog) hzero
    have hmone : terminalMultiplicity R source = 1 := by omega
    exact (confluentAt_iff_terminalMultiplicity_eq_one hnorm).mpr hmone
  · intro hconf
    have hmone := (confluentAt_iff_terminalMultiplicity_eq_one hnorm).mp hconf
    simp [terminalCeilLog2, hmone, Nat.clog_one_right]

/-- Every `L` step is also an `R` step. -/
def IsLicensedSubrelation {T : Type u}
    (L R : T -> T -> Prop) : Prop :=
  ∀ ⦃x y⦄, L x y -> R x y

/-- Map an `L` path to an `R` path of the same length using a subrelation witness. -/
theorem steps_of_licensedSubrelation {T : Type u} {L R : T -> T -> Prop}
    (hsub : IsLicensedSubrelation L R) {n : Nat} {x y : T}
    (hsteps : Steps L n x y) : Steps R n x y := by
  induction hsteps with
  | zero => exact Steps.zero _
  | succ hstep _ ih => exact Steps.succ (hsub hstep) ih

/-- A subrelation witness maps `L` reachability into `R` reachability. -/
theorem reach_of_licensedSubrelation {T : Type u} {L R : T -> T -> Prop}
    (hsub : IsLicensedSubrelation L R) {x y : T} (hreach : Reach L x y) :
    Reach R x y := by
  rcases hreach with ⟨n, hn⟩
  exact ⟨n, steps_of_licensedSubrelation hsub hn⟩

/-- Base-two logarithm of the ratio between terminal multiplicities for arbitrary relations `R` and
`L`. This definition itself carries no subrelation or licensing premise. -/
def structuralHartleyCollapse {T : Type u} [Fintype T]
    (R L : T -> T -> Prop) (source : T) : Real :=
  Real.logb 2
    ((terminalMultiplicity R source : Real) /
      (terminalMultiplicity L source : Real))

/-- Ratio definition with local-normalization witnesses ensuring positive terminal multiplicities. -/
def structuralHartleyCollapseGuarded {T : Type u} [Fintype T]
    {R L : T -> T -> Prop} {source : T}
    (_hR : NormalizingAt R source) (_hL : NormalizingAt L source) : Real :=
  structuralHartleyCollapse R L source

theorem structuralHartleyCollapseGuarded_eq_log_ratio
    {T : Type u} [Fintype T] {R L : T -> T -> Prop} {source : T}
    (hR : NormalizingAt R source) (hL : NormalizingAt L source) :
    structuralHartleyCollapseGuarded hR hL =
      Real.logb 2 ((terminalMultiplicity R source : Real) /
        (terminalMultiplicity L source : Real)) := rfl

theorem structuralHartleyCollapseGuarded_nonneg
    {T : Type u} [Fintype T] {R L : T -> T -> Prop} {source : T}
    (hR : NormalizingAt R source) (hL : NormalizingAt L source)
    (hle : terminalMultiplicity L source <= terminalMultiplicity R source) :
    0 <= structuralHartleyCollapseGuarded hR hL := by
  rw [structuralHartleyCollapseGuarded_eq_log_ratio]
  apply Real.logb_nonneg (by norm_num : (1 : Real) < 2)
  have hpos : 0 < terminalMultiplicity L source :=
    terminalMultiplicity_pos_of_normalizingAt hL
  have hden_pos : 0 < (terminalMultiplicity L source : Real) := by
    exact_mod_cast hpos
  have hleReal :
      (terminalMultiplicity L source : Real) <=
        (terminalMultiplicity R source : Real) := by
    exact_mod_cast hle
  rw [le_div_iff₀ hden_pos]
  simpa [one_mul] using hleReal

/-! ## Finite chain and fork fixtures -/

/-- The concrete chain from `Core` has terminal multiplicity one. -/
theorem chain_terminalMultiplicity_eq_one :
    terminalMultiplicity ChainStep .source = 1 :=
  terminalMultiplicity_eq_one_of_confluentAt
    chain_normalizingAt_source chain_confluentAt_source

/-- The concrete terminal fork has its two leaves as terminal support. -/
theorem fork_terminalSupport_eq :
    terminalSupport ForkStep .source = {.left, .right} := by
  classical
  ext x
  cases x with
  | source =>
      constructor
      · intro hx
        have hnormal := (mem_terminalSupport.mp hx).2
        exact False.elim (hnormal .left ForkStep.goLeft)
      · simp
  | left =>
      constructor
      · intro _
        simp
      · intro _
        exact mem_terminalSupport.mpr
          ⟨reach_step ForkStep.goLeft, fork_left_normal⟩
  | right =>
      constructor
      · intro _
        simp
      · intro _
        exact mem_terminalSupport.mpr
          ⟨reach_step ForkStep.goRight, fork_right_normal⟩

/-- The fork has terminal multiplicity two. -/
theorem fork_terminalMultiplicity_eq_two :
    terminalMultiplicity ForkStep .source = 2 := by
  simp [terminalMultiplicity, fork_terminalSupport_eq]

/-- The fork's terminal Hartley entropy equals one. -/
theorem fork_terminalHartleyEntropy_eq_one :
    terminalHartleyEntropy ForkStep .source = 1 := by
  rw [terminalHartleyEntropy, fork_terminalMultiplicity_eq_two]
  exact Real.logb_self_eq_one (by norm_num)

/-! ## Four-way relation and one-edge subrelation -/

inductive FourForkNode where
  | source
  | a
  | b
  | c
  | d
deriving DecidableEq, Fintype

inductive FourForkStep : FourForkNode -> FourForkNode -> Prop where
  | goA : FourForkStep .source .a
  | goB : FourForkStep .source .b
  | goC : FourForkStep .source .c
  | goD : FourForkStep .source .d

inductive FourForkLicensedStep : FourForkNode -> FourForkNode -> Prop where
  | goA : FourForkLicensedStep .source .a

theorem fourFork_a_normal : NormalForm FourForkStep .a := by
  intro y h
  cases h

theorem fourFork_b_normal : NormalForm FourForkStep .b := by
  intro y h
  cases h

theorem fourFork_c_normal : NormalForm FourForkStep .c := by
  intro y h
  cases h

theorem fourFork_d_normal : NormalForm FourForkStep .d := by
  intro y h
  cases h

theorem fourForkLicensed_a_normal : NormalForm FourForkLicensedStep .a := by
  intro y h
  cases h

theorem fourForkLicensed_b_normal : NormalForm FourForkLicensedStep .b := by
  intro y h
  cases h

theorem fourForkLicensed_c_normal : NormalForm FourForkLicensedStep .c := by
  intro y h
  cases h

theorem fourForkLicensed_d_normal : NormalForm FourForkLicensedStep .d := by
  intro y h
  cases h

theorem fourFork_normalizingAt_source :
    NormalizingAt FourForkStep .source := by
  intro x _
  cases x with
  | source => exact ⟨.a, reach_step FourForkStep.goA, fourFork_a_normal⟩
  | a => exact ⟨.a, reach_refl _, fourFork_a_normal⟩
  | b => exact ⟨.b, reach_refl _, fourFork_b_normal⟩
  | c => exact ⟨.c, reach_refl _, fourFork_c_normal⟩
  | d => exact ⟨.d, reach_refl _, fourFork_d_normal⟩

theorem fourForkLicensed_normalizingAt_source :
    NormalizingAt FourForkLicensedStep .source := by
  intro x _
  cases x with
  | source =>
      exact ⟨.a, reach_step FourForkLicensedStep.goA, fourForkLicensed_a_normal⟩
  | a => exact ⟨.a, reach_refl _, fourForkLicensed_a_normal⟩
  | b => exact ⟨.b, reach_refl _, fourForkLicensed_b_normal⟩
  | c => exact ⟨.c, reach_refl _, fourForkLicensed_c_normal⟩
  | d => exact ⟨.d, reach_refl _, fourForkLicensed_d_normal⟩

theorem fourFork_terminalSupport_eq :
    terminalSupport FourForkStep .source = {.a, .b, .c, .d} := by
  classical
  ext x
  cases x with
  | source =>
      constructor
      · intro hx
        have hnormal := (mem_terminalSupport.mp hx).2
        exact False.elim (hnormal .a FourForkStep.goA)
      · simp
  | a =>
      constructor
      · intro _; simp
      · intro _
        exact mem_terminalSupport.mpr
          ⟨reach_step FourForkStep.goA, fourFork_a_normal⟩
  | b =>
      constructor
      · intro _; simp
      · intro _
        exact mem_terminalSupport.mpr
          ⟨reach_step FourForkStep.goB, fourFork_b_normal⟩
  | c =>
      constructor
      · intro _; simp
      · intro _
        exact mem_terminalSupport.mpr
          ⟨reach_step FourForkStep.goC, fourFork_c_normal⟩
  | d =>
      constructor
      · intro _; simp
      · intro _
        exact mem_terminalSupport.mpr
          ⟨reach_step FourForkStep.goD, fourFork_d_normal⟩

theorem fourForkLicensed_terminalSupport_eq :
    terminalSupport FourForkLicensedStep .source = {.a} := by
  classical
  ext x
  cases x with
  | source =>
      constructor
      · intro hx
        have hnormal := (mem_terminalSupport.mp hx).2
        exact False.elim (hnormal .a FourForkLicensedStep.goA)
      · simp
  | a =>
      constructor
      · intro _; simp
      · intro _
        exact mem_terminalSupport.mpr
          ⟨reach_step FourForkLicensedStep.goA, fourForkLicensed_a_normal⟩
  | b =>
      constructor
      · intro hx
        rcases mem_terminalSupport.mp hx with ⟨⟨n, hn⟩, _⟩
        cases hn with
        | succ hstep rest =>
            cases hstep
            cases rest with
            | succ hnext _ => cases hnext
      · simp
  | c =>
      constructor
      · intro hx
        rcases mem_terminalSupport.mp hx with ⟨⟨n, hn⟩, _⟩
        cases hn with
        | succ hstep rest =>
            cases hstep
            cases rest with
            | succ hnext _ => cases hnext
      · simp
  | d =>
      constructor
      · intro hx
        rcases mem_terminalSupport.mp hx with ⟨⟨n, hn⟩, _⟩
        cases hn with
        | succ hstep rest =>
            cases hstep
            cases rest with
            | succ hnext _ => cases hnext
      · simp

theorem fourFork_terminalMultiplicity_eq_four :
    terminalMultiplicity FourForkStep .source = 4 := by
  simp [terminalMultiplicity, fourFork_terminalSupport_eq]

theorem fourForkLicensed_terminalMultiplicity_eq_one :
    terminalMultiplicity FourForkLicensedStep .source = 1 := by
  simp [terminalMultiplicity, fourForkLicensed_terminalSupport_eq]

theorem fourForkLicensed_isSubrelation :
    IsLicensedSubrelation FourForkLicensedStep FourForkStep := by
  intro x y h
  cases h
  exact FourForkStep.goA

theorem fourFork_not_confluentAt_source :
    Not (ConfluentAt FourForkStep .source) := by
  intro hconf
  rcases hconf .a .b (reach_step FourForkStep.goA) (reach_step FourForkStep.goB) with
    ⟨z, hza, hzb⟩
  have hzaEq : z = .a := eq_of_normalForm_reach fourFork_a_normal hza
  have hzbEq : z = .b := eq_of_normalForm_reach fourFork_b_normal hzb
  cases hzaEq.symm.trans hzbEq

theorem fourForkLicensed_confluentAt_source :
    ConfluentAt FourForkLicensedStep .source := by
  apply confluentAt_of_terminalMultiplicity_eq_one
    fourForkLicensed_normalizingAt_source
  exact fourForkLicensed_terminalMultiplicity_eq_one

/-- The logarithm of the four-to-one terminal-multiplicity ratio equals two. -/
theorem fourFork_structuralHartleyCollapse_eq_two :
    structuralHartleyCollapse FourForkStep FourForkLicensedStep .source = 2 := by
  rw [structuralHartleyCollapse, fourFork_terminalMultiplicity_eq_four,
    fourForkLicensed_terminalMultiplicity_eq_one]
  norm_num only [Nat.cast_ofNat, div_one]
  have hfour : (4 : Real) = (2 : Real) ^ 2 := by norm_num
  rw [hfour, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num

/-! ## Necessity of the local-normalization premise

`NormalizingAt R source` requires every term reachable from `source` to reach a
normal form, which is strictly stronger than requiring a normal form for
`source` alone. The witness below shows the stronger reading is load bearing:
weakening the premise to "the source has a normal form" makes
`confluentAt_iff_terminalMultiplicity_eq_one` false in its right-to-left
direction. The carrier is a three-state system in which the source branches to a
normal form and to a self-looping state. -/

inductive EscapeNode where
  | source
  | loop
  | terminal
deriving DecidableEq, Fintype

/-- `source` branches to a normal form and to a self-looping state. -/
inductive EscapeStep : EscapeNode -> EscapeNode -> Prop where
  | toTerminal : EscapeStep .source .terminal
  | toLoop : EscapeStep .source .loop
  | spin : EscapeStep .loop .loop

theorem escape_terminal_normal : NormalForm EscapeStep .terminal := by
  intro y h; cases h

/-- The looping state reaches itself alone. -/
theorem escape_reach_loop {x : EscapeNode} (h : Reach EscapeStep .loop x) :
    x = .loop := by
  rcases h with ⟨n, hn⟩
  induction n generalizing x with
  | zero => cases hn; rfl
  | succ k ih =>
      cases hn with
      | succ hstep rest =>
          cases hstep
          exact ih rest

/-- The looping state reaches no normal form, so the strong premise fails. -/
theorem escape_not_normalizingAt_source : Not (NormalizingAt EscapeStep .source) := by
  intro hnorm
  rcases hnorm .loop (reach_step EscapeStep.toLoop) with ⟨n, hn, hnNF⟩
  have hEq : n = EscapeNode.loop := escape_reach_loop hn
  exact hnNF .loop (hEq ▸ EscapeStep.spin)

/-- The source itself does reach a normal form: the weakened premise holds. -/
theorem escape_source_has_normalForm :
    ∃ n, Reach EscapeStep .source n ∧ NormalForm EscapeStep n :=
  ⟨.terminal, reach_step EscapeStep.toTerminal, escape_terminal_normal⟩

theorem escape_terminalSupport_eq :
    terminalSupport EscapeStep .source = {EscapeNode.terminal} := by
  classical
  ext x
  simp only [mem_terminalSupport, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hxNF⟩
    cases x with
    | source => exact absurd (hxNF .terminal) (by simp [EscapeStep.toTerminal])
    | loop => exact absurd (hxNF .loop) (by simp [EscapeStep.spin])
    | terminal => rfl
  · rintro rfl
    exact ⟨reach_step EscapeStep.toTerminal, escape_terminal_normal⟩

theorem escape_terminalMultiplicity_eq_one :
    terminalMultiplicity EscapeStep .source = 1 := by
  unfold terminalMultiplicity
  rw [escape_terminalSupport_eq]
  simp

/-- Multiplicity one fails to give source confluence once the premise is
weakened: `loop` and `terminal` are both reachable and never join. -/
theorem escape_not_confluentAt_source : Not (ConfluentAt EscapeStep .source) := by
  intro hconf
  rcases hconf .loop .terminal (reach_step EscapeStep.toLoop)
      (reach_step EscapeStep.toTerminal) with ⟨z, hzl, hzt⟩
  have hzLoop : z = EscapeNode.loop := escape_reach_loop hzl
  have hzTerm : z = EscapeNode.terminal := eq_of_normalForm_reach escape_terminal_normal hzt
  exact absurd (hzLoop.symm.trans hzTerm) (by simp)

/-- HEADLINE: the local-normalization premise of
`confluentAt_iff_terminalMultiplicity_eq_one` cannot be weakened to "the source
has a normal form". There is a finite system whose source has a normal form and
whose terminal multiplicity is one, yet which fails source confluence. -/
theorem normalizingAt_premise_cannot_be_weakened :
    ∃ (T : Type) (_ : Fintype T) (R : T -> T -> Prop) (source : T),
      (∃ n, Reach R source n ∧ NormalForm R n) ∧
      terminalMultiplicity R source = 1 ∧
      Not (ConfluentAt R source) :=
  ⟨EscapeNode, inferInstance, EscapeStep, .source,
   escape_source_has_normalForm,
   escape_terminalMultiplicity_eq_one,
   escape_not_confluentAt_source⟩

#check @confluentAt_iff_terminalMultiplicity_eq_one
#check @terminalHartleyEntropy_eq_zero_iff_confluentAt
#check @terminalCeilLog2_eq_zero_iff_confluentAt
#check @fourFork_structuralHartleyCollapse_eq_two
#check @normalizingAt_premise_cannot_be_weakened
#print axioms normalizingAt_premise_cannot_be_weakened
#print axioms escape_not_normalizingAt_source

#print axioms confluentAt_iff_terminalMultiplicity_eq_one
#print axioms terminalHartleyEntropy_eq_zero_iff_confluentAt
#print axioms terminalCeilLog2_eq_zero_iff_confluentAt
#print axioms chain_terminalMultiplicity_eq_one
#print axioms fork_terminalMultiplicity_eq_two
#print axioms fourFork_not_confluentAt_source
#print axioms fourForkLicensed_confluentAt_source
#print axioms fourFork_structuralHartleyCollapse_eq_two

end

end OperatorKO7.Meta.DistinctionBoundary.Quantitative
