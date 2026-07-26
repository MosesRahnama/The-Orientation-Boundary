import Mathlib

/-!
# Generic quantitative core for the Distinction Boundary

This file contains no KO7 syntax or reduction relation. It supplies exact-length
paths, reachability, normal forms, joinability, source confluence, and the local
normalization condition used by the quantitative Distinction Boundary laws.

Relation: the caller-supplied one-step relation `R`.
Closure: `Reach R`, the existential exact-length reflexive-transitive closure.
Strategy: none; all one-step paths are admitted.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u

/-- An exact `n`-step path in a caller-supplied relation. -/
inductive Steps {T : Type u} (R : T -> T -> Prop) : Nat -> T -> T -> Prop where
  | zero (x : T) : Steps R 0 x x
  | succ {n : Nat} {x y z : T} : R x y -> Steps R n y z -> Steps R (n + 1) x z

/-- Concatenation of exact-length paths. -/
theorem Steps.append {T : Type u} {R : T -> T -> Prop}
    {m n : Nat} {x y z : T} (hxy : Steps R m x y) (hyz : Steps R n y z) :
    Steps R (m + n) x z := by
  induction hxy with
  | zero => simpa using hyz
  | @succ k a b c hab hbc ih =>
      convert Steps.succ hab (ih hyz) using 1
      omega

/-- Reflexive-transitive reachability, retaining an exact-length witness. -/
def Reach {T : Type u} (R : T -> T -> Prop) (x y : T) : Prop :=
  exists n, Steps R n x y

theorem reach_refl {T : Type u} {R : T -> T -> Prop} (x : T) : Reach R x x :=
  ⟨0, Steps.zero x⟩

theorem reach_step {T : Type u} {R : T -> T -> Prop} {x y : T} (h : R x y) :
    Reach R x y :=
  ⟨1, by simpa using Steps.succ h (Steps.zero y)⟩

theorem reach_trans {T : Type u} {R : T -> T -> Prop} {x y z : T}
    (hxy : Reach R x y) (hyz : Reach R y z) : Reach R x z := by
  rcases hxy with ⟨m, hm⟩
  rcases hyz with ⟨n, hn⟩
  exact ⟨m + n, hm.append hn⟩

/-- A term is normal when no one-step reduct leaves it. -/
def NormalForm {T : Type u} (R : T -> T -> Prop) (x : T) : Prop :=
  forall y, Not (R x y)

/-- Two terms are joinable when they reach a common reduct. -/
def Joinable {T : Type u} (R : T -> T -> Prop) (x y : T) : Prop :=
  exists z, Reach R x z /\ Reach R y z

/-- Confluence restricted to the cone reachable from one source. -/
def ConfluentAt {T : Type u} (R : T -> T -> Prop) (source : T) : Prop :=
  forall x y, Reach R source x -> Reach R source y -> Joinable R x y

/-- Every reduct below `source` can itself reach a normal form. This is the
local normalization premise needed for unique-normal-form completeness. -/
def NormalizingAt {T : Type u} (R : T -> T -> Prop) (source : T) : Prop :=
  forall x, Reach R source x -> exists n, Reach R x n /\ NormalForm R n

/-- Reachability out of a normal form is constant. -/
theorem eq_of_normalForm_reach {T : Type u} {R : T -> T -> Prop} {n x : T}
    (hn : NormalForm R n) (h : Reach R n x) : x = n := by
  rcases h with ⟨k, hk⟩
  cases hk with
  | zero => rfl
  | succ hstep _ => exact False.elim (hn _ hstep)

/-- Source confluence forces any two reachable normal forms to coincide. -/
theorem unique_normalForm_of_confluentAt {T : Type u} {R : T -> T -> Prop}
    {source n1 n2 : T} (hconf : ConfluentAt R source)
    (h1 : Reach R source n1) (hn1 : NormalForm R n1)
    (h2 : Reach R source n2) (hn2 : NormalForm R n2) : n1 = n2 := by
  rcases hconf n1 n2 h1 h2 with ⟨z, hz1, hz2⟩
  have hzn1 : z = n1 := eq_of_normalForm_reach hn1 hz1
  have hzn2 : z = n2 := eq_of_normalForm_reach hn2 hz2
  exact hzn1.symm.trans hzn2

/-- Under local normalization, uniqueness of reachable normal forms is also
sufficient for source confluence. -/
theorem confluentAt_of_unique_normalForms {T : Type u} {R : T -> T -> Prop}
    {source : T} (hnorm : NormalizingAt R source)
    (huniq : forall n1 n2,
      Reach R source n1 -> NormalForm R n1 ->
      Reach R source n2 -> NormalForm R n2 -> n1 = n2) :
    ConfluentAt R source := by
  intro x y hx hy
  rcases hnorm x hx with ⟨nx, hnx, hnxNF⟩
  rcases hnorm y hy with ⟨ny, hny, hnyNF⟩
  have hsx : Reach R source nx := reach_trans hx hnx
  have hsy : Reach R source ny := reach_trans hy hny
  have hEq : nx = ny := huniq nx ny hsx hnxNF hsy hnyNF
  exact ⟨nx, hnx, hEq ▸ hny⟩

/-! ## Concrete non-vacuity and negative relation -/

inductive ChainNode where
  | source
  | terminal
deriving DecidableEq, Fintype

inductive ChainStep : ChainNode -> ChainNode -> Prop where
  | descend : ChainStep .source .terminal

theorem chain_terminal_normal : NormalForm ChainStep .terminal := by
  intro y h
  cases h

theorem chain_normalizingAt_source : NormalizingAt ChainStep .source := by
  intro x hx
  rcases hx with ⟨n, hn⟩
  cases hn with
  | zero => exact ⟨.terminal, reach_step ChainStep.descend, chain_terminal_normal⟩
  | succ hstep rest =>
      cases hstep
      have hEq : x = ChainNode.terminal := eq_of_normalForm_reach chain_terminal_normal ⟨_, rest⟩
      subst x
      exact ⟨.terminal, reach_refl _, chain_terminal_normal⟩

theorem chain_confluentAt_source : ConfluentAt ChainStep .source := by
  apply confluentAt_of_unique_normalForms chain_normalizingAt_source
  intro n1 n2 _ hn1 _ hn2
  cases n1 <;> cases n2
  · rfl
  · exact False.elim (hn1 _ ChainStep.descend)
  · exact False.elim (hn2 _ ChainStep.descend)
  · rfl

inductive ForkNode where
  | source
  | left
  | right
deriving DecidableEq, Fintype

inductive ForkStep : ForkNode -> ForkNode -> Prop where
  | goLeft : ForkStep .source .left
  | goRight : ForkStep .source .right

theorem fork_left_normal : NormalForm ForkStep .left := by
  intro y h
  cases h

theorem fork_right_normal : NormalForm ForkStep .right := by
  intro y h
  cases h

theorem fork_not_confluentAt_source : Not (ConfluentAt ForkStep .source) := by
  intro hconf
  rcases hconf .left .right (reach_step ForkStep.goLeft) (reach_step ForkStep.goRight) with
    ⟨z, hzL, hzR⟩
  have hzl : z = .left := eq_of_normalForm_reach fork_left_normal hzL
  have hzr : z = .right := eq_of_normalForm_reach fork_right_normal hzR
  cases hzl.symm.trans hzr

#print axioms unique_normalForm_of_confluentAt
#print axioms confluentAt_of_unique_normalForms
#print axioms chain_confluentAt_source
#print axioms fork_not_confluentAt_source

end OperatorKO7.Meta.DistinctionBoundary.Quantitative
