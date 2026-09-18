import OperatorKO7.Meta.UniqueNormalization.ConditionalDecreasingAdapter
import Mathlib.Computability.Primrec

/-!
# RTA #79 route R2: fresh-variable encoding for the generic hub transform

The generic hub linearization needs infinitely many fresh variables while keeping
the original right-hand side verbatim. On `Nat` variables we reserve one tail
segment above every variable occurring in the source rule. A duplicate occurrence
of original variable `x` with duplicate index `k` is encoded as
`base + Nat.pair x k`. The collapse map decodes the pair from that tail segment
and fixes every variable below `base`.

This gives a total, injective fresh namespace without a lookup table. It is the
freshness/collapse substrate for the stateful occurrence splitter used by
`linHub`.

Trust: kernel checked. No external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

/-- Maximum of a list of natural numbers, with `0` for the empty list. -/
def maxNatList : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxNatList xs)

/-- Every member is bounded by `maxNatList`. -/
theorem le_maxNatList_of_mem {x : Nat} :
    ∀ {xs : List Nat}, x ∈ xs → x ≤ maxNatList xs := by
  intro xs hx
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact (ih hx).trans (Nat.le_max_right _ _)

/-- One greater than every original variable occurring in either side of a rule. -/
def ruleFreshBase {sigma : Type*} (rule : Rule sigma Nat) : Nat :=
  max (maxNatList (Term.varOccurrences rule.lhs))
      (maxNatList (Term.varOccurrences rule.rhs)) + 1

/-- Every left-hand-side occurrence lies strictly below the fresh base. -/
theorem lhs_occ_lt_ruleFreshBase {sigma : Type*} {rule : Rule sigma Nat}
    {x : Nat} (hx : x ∈ Term.varOccurrences rule.lhs) :
    x < ruleFreshBase rule := by
  have hle : x ≤ maxNatList (Term.varOccurrences rule.lhs) :=
    le_maxNatList_of_mem hx
  exact lt_of_le_of_lt (hle.trans (Nat.le_max_left _ _)) (Nat.lt_succ_self _)

/-- Every right-hand-side occurrence lies strictly below the fresh base. -/
theorem rhs_occ_lt_ruleFreshBase {sigma : Type*} {rule : Rule sigma Nat}
    {x : Nat} (hx : x ∈ Term.varOccurrences rule.rhs) :
    x < ruleFreshBase rule := by
  have hle : x ≤ maxNatList (Term.varOccurrences rule.rhs) :=
    le_maxNatList_of_mem hx
  exact lt_of_le_of_lt (hle.trans (Nat.le_max_right _ _)) (Nat.lt_succ_self _)

/-- Fresh code for duplicate index `k` of original variable `x`. -/
def hubFresh (base x k : Nat) : Nat :=
  base + Nat.pair x k

/-- Decode the original variable from the reserved fresh tail, fixing every
variable below the base. -/
def hubCollapse (base v : Nat) : Nat :=
  if v < base then v else (v - base).unpair.1

/-- Original variables below the base are fixed by collapse. -/
@[simp] theorem hubCollapse_of_lt {base v : Nat} (h : v < base) :
    hubCollapse base v = v := by
  simp [hubCollapse, h]

/-- Every fresh code lies in the reserved tail. -/
theorem le_hubFresh (base x k : Nat) : base ≤ hubFresh base x k := by
  simp [hubFresh]

/-- A fresh code never lies below its base. -/
theorem not_hubFresh_lt (base x k : Nat) : ¬ hubFresh base x k < base := by
  exact Nat.not_lt_of_ge (le_hubFresh base x k)

/-- Collapse decodes every fresh code exactly to its original variable. -/
@[simp] theorem hubCollapse_hubFresh (base x k : Nat) :
    hubCollapse base (hubFresh base x k) = x := by
  simp [hubCollapse, hubFresh, Nat.unpair_pair]

/-- Fresh codes are injective in `(original variable, duplicate index)`. -/
theorem hubFresh_injective {base x k y j : Nat}
    (h : hubFresh base x k = hubFresh base y j) : x = y ∧ k = j := by
  have hp : Nat.pair x k = Nat.pair y j := by
    exact Nat.add_left_cancel h
  have hu := congrArg Nat.unpair hp
  simpa [Nat.unpair_pair] using hu

/-- Distinct duplicate indices of one original variable receive distinct fresh
codes. -/
theorem hubFresh_ne_of_index_ne {base x k j : Nat} (hkj : k ≠ j) :
    hubFresh base x k ≠ hubFresh base x j := by
  intro h
  exact hkj (hubFresh_injective h).2

/-- A fresh code cannot collide with any original variable below the base. -/
theorem hubFresh_ne_of_lt_base {base x k v : Nat} (hv : v < base) :
    hubFresh base x k ≠ v := by
  intro h
  have hge := le_hubFresh base x k
  rw [h] at hge
  exact (Nat.not_le_of_lt hv) hge

/-- Occurrence witnesses are exactly represented in `varOccurrences` in the
forward direction needed by the hub construction. -/
theorem VarOccurs.mem_varOccurrences {sigma : Type*} {x : Nat}
    {t : Term sigma Nat} (h : VarOccurs x t) : x ∈ Term.varOccurrences t := by
  induction h with
  | here => simp [Term.varOccurrences]
  | @arg f args a ha _ ih =>
      simp only [Term.varOccurrences, List.mem_flatMap]
      exact ⟨a, ha, ih⟩

/-- The collapse map fixes every variable occurring in the original left-hand
side of a rule. -/
theorem hubCollapse_lhs_occ {sigma : Type*} {rule : Rule sigma Nat}
    {x : Nat} (hx : x ∈ Term.varOccurrences rule.lhs) :
    hubCollapse (ruleFreshBase rule) x = x :=
  hubCollapse_of_lt (lhs_occ_lt_ruleFreshBase hx)

/-- The collapse map fixes every variable occurring in the original right-hand
side of a rule. -/
theorem hubCollapse_rhs_occ {sigma : Type*} {rule : Rule sigma Nat}
    {x : Nat} (hx : x ∈ Term.varOccurrences rule.rhs) :
    hubCollapse (ruleFreshBase rule) x = x :=
  hubCollapse_of_lt (rhs_occ_lt_ruleFreshBase hx)

/-- Therefore collapse leaves the original right-hand side verbatim. -/
theorem hubCollapse_rhs {sigma : Type*} (rule : Rule sigma Nat) :
    Term.mapVar (hubCollapse (ruleFreshBase rule)) rule.rhs = rule.rhs := by
  apply mapVar_id_on
  intro x hx
  exact hubCollapse_rhs_occ hx.mem_varOccurrences

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.maxNatList
#check @OperatorKO7.Meta.UniqueNormalization.le_maxNatList_of_mem
#check @OperatorKO7.Meta.UniqueNormalization.ruleFreshBase
#check @OperatorKO7.Meta.UniqueNormalization.lhs_occ_lt_ruleFreshBase
#check @OperatorKO7.Meta.UniqueNormalization.rhs_occ_lt_ruleFreshBase
#check @OperatorKO7.Meta.UniqueNormalization.hubFresh
#check @OperatorKO7.Meta.UniqueNormalization.hubCollapse
#check @OperatorKO7.Meta.UniqueNormalization.hubCollapse_of_lt
#check @OperatorKO7.Meta.UniqueNormalization.le_hubFresh
#check @OperatorKO7.Meta.UniqueNormalization.not_hubFresh_lt
#check @OperatorKO7.Meta.UniqueNormalization.hubCollapse_hubFresh
#check @OperatorKO7.Meta.UniqueNormalization.hubFresh_injective
#check @OperatorKO7.Meta.UniqueNormalization.hubFresh_ne_of_index_ne
#check @OperatorKO7.Meta.UniqueNormalization.hubFresh_ne_of_lt_base
#check @OperatorKO7.Meta.UniqueNormalization.VarOccurs.mem_varOccurrences
#check @OperatorKO7.Meta.UniqueNormalization.hubCollapse_lhs_occ
#check @OperatorKO7.Meta.UniqueNormalization.hubCollapse_rhs_occ
#check @OperatorKO7.Meta.UniqueNormalization.hubCollapse_rhs

#print axioms OperatorKO7.Meta.UniqueNormalization.le_maxNatList_of_mem
#print axioms OperatorKO7.Meta.UniqueNormalization.lhs_occ_lt_ruleFreshBase
#print axioms OperatorKO7.Meta.UniqueNormalization.rhs_occ_lt_ruleFreshBase
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCollapse_of_lt
#print axioms OperatorKO7.Meta.UniqueNormalization.le_hubFresh
#print axioms OperatorKO7.Meta.UniqueNormalization.not_hubFresh_lt
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCollapse_hubFresh
#print axioms OperatorKO7.Meta.UniqueNormalization.hubFresh_injective
#print axioms OperatorKO7.Meta.UniqueNormalization.hubFresh_ne_of_index_ne
#print axioms OperatorKO7.Meta.UniqueNormalization.hubFresh_ne_of_lt_base
#print axioms OperatorKO7.Meta.UniqueNormalization.VarOccurs.mem_varOccurrences
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCollapse_lhs_occ
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCollapse_rhs_occ
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCollapse_rhs
