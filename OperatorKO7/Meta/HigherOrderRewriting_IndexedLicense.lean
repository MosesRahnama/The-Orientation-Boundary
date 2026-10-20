import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax
import OperatorKO7.Meta.HigherOrderRewriting_TypeCostBoundary
import OperatorKO7.Meta.HigherOrderRewriting_TypedDirectMeasureBarrier
import OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse

/-!
# L2 indexed license for the System T Church family

The simple type observer cannot license leftmost-outermost beta cost on the Church family. Adding
the syntactic Church index does license that cost on the family, while every fixed finite side
channel still collides on a large enough initial segment. Singleton refusal is licensed, while two
different Church terms cannot both be retained once the fuel covers both costs.

External grounding, ESTABLISHED only: Girard, Scedrov, and Scott, "Bounded Linear Logic: A Modular
Approach to Polynomial-Time Computability", Theoretical Computer Science 97 (1992); Dal Lago and
Gaboardi, "Linear Dependent Types and Relative Completeness", LMCS 8(4:11) (2012). These sources
motivate indexed resource information. No result from either source is imported as a Lean premise.

Relation: equality of observations for LicensedOn; betaCost iterates stepLO.
Closure: observer fibers on the Church family; finite side-channel fibers; one beta substitution in
the duplication-count statement.
Strategy: leftmost-outermost for betaCost; no strategy claim for the syntactic occurrence count.
Trust: kernel-only.
Scope: the System T Church family churchApp n, the plain type observer infer [], and the
syntactic index inherited from the L12 occurrence reader.
-/

set_option autoImplicit false

namespace OperatorKO7.HigherOrderRewritingIndexedLicense

open OperatorKO7.HigherOrderRewritingSystemT
open OperatorKO7.HigherOrderRewritingTypeCostBoundary
open OperatorKO7.HigherOrderRewritingTypedDirectMeasureBarrier
open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse

/-- The L2 index is exactly the L12 head-bound-variable occurrence reader. -/
abbrev churchIndex : SysTTerm → Nat := headBoundVarOccurrences

/--
Proves: the inherited Church index reads n on churchApp n.
Does not prove: that the index determines arbitrary System T terms.
Relation: equality of the syntactic observer.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every n : Nat.
-/
theorem churchIndex_churchApp (n : Nat) : churchIndex (churchApp n) = n :=
  headBoundVarOccurrences_churchApp n

/-- The retained carrier used by the L2 license claims. -/
def ChurchFamily : Set SysTTerm := Set.range churchApp

/--
Proves: distinct natural indices give distinct Church applications.
Does not prove: injectivity of any larger System T encoding.
Relation: equality of SysTTerm.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the map churchApp : Nat → SysTTerm.
-/
theorem churchApp_injective : Function.Injective churchApp := by
  intro m n hmn
  have hindex := congrArg churchIndex hmn
  rw [churchIndex_churchApp, churchIndex_churchApp] at hindex
  exact hindex

/- Q49 controls: the two values used by the first collision are computed before the theorem. -/
example : betaCost 3 (churchApp 0) = some 2 := by decide
example : betaCost 3 (churchApp 1) = some 3 := by decide

/--
Proves: with fuel at least three, the plain type observer does not license beta cost on the full
Church family.
Does not prove: failure below fuel three, or failure for an observer carrying extra information.
Relation: LicensedOn ChurchFamily (infer []) (betaCost f).
Closure: observer-fiber equality on the Church family.
Strategy: leftmost-outermost beta cost.
Trust: kernel-only.
Scope: every f : Nat with 3 ≤ f; witnesses churchApp 0 and churchApp 1.
-/
theorem plain_observer_not_licensedOn_church :
    ∀ f, 3 ≤ f → ¬ LicensedOn ChurchFamily (infer []) (betaCost f) := by
  intro f hf hlicensed
  have hobs : infer [] (churchApp 0) = infer [] (churchApp 1) := by
    rw [infer_churchApp, infer_churchApp]
  have hcost := hlicensed
    (churchApp 0) ⟨0, rfl⟩
    (churchApp 1) ⟨1, rfl⟩
    hobs
  have h0 : betaCost f (churchApp 0) = some 2 := by
    simpa using betaCost_churchApp 0 f (Nat.le_trans (by decide : 2 ≤ 3) hf)
  have h1 : betaCost f (churchApp 1) = some 3 := by
    simpa using betaCost_churchApp 1 f hf
  rw [h0, h1] at hcost
  exact (by decide : (some 2 : Option Nat) ≠ some 3) hcost

/-- The type observer augmented by the inherited syntactic Church index. -/
def indexedObserver (t : SysTTerm) : Option SysTTy × Nat :=
  (infer [] t, churchIndex t)

/--
Proves: the indexed observer licenses beta cost on the Church family for every fuel.
Does not prove: licensing on terms outside the Church family.
Relation: LicensedOn ChurchFamily indexedObserver (betaCost f).
Closure: observer-fiber equality on the Church family.
Strategy: leftmost-outermost beta cost.
Trust: kernel-only.
Scope: every f : Nat.
-/
theorem indexed_observer_licensedOn_church :
    ∀ f, LicensedOn ChurchFamily indexedObserver (betaCost f) := by
  intro f x hx y hy hobs
  rcases hx with ⟨m, rfl⟩
  rcases hy with ⟨n, rfl⟩
  have hindex :
      churchIndex (churchApp m) = churchIndex (churchApp n) :=
    congrArg Prod.snd hobs
  rw [churchIndex_churchApp, churchIndex_churchApp] at hindex
  subst n
  rfl

/--
Proves: no side channel with k symbols licenses beta cost at fuel k + 2 on the full Church
family.
Does not prove: failure of an unbounded side channel, or failure on a smaller retained family.
Relation: LicensedOn ChurchFamily (fun t => (infer [] t, s t)) (betaCost (k + 2)).
Closure: observer-fiber equality on the Church family.
Strategy: leftmost-outermost beta cost.
Trust: kernel-only.
Scope: every k : Nat and every s : SysTTerm → Fin k.
-/
theorem no_finite_side_channel_licenses_church :
    ∀ (k : Nat) (s : SysTTerm → Fin k),
      ¬ LicensedOn ChurchFamily (fun t => (infer [] t, s t)) (betaCost (k + 2)) := by
  intro k s hlicensed
  let side : Fin (k + 1) → Fin k := fun i => s (churchApp i.1)
  have hcard : Fintype.card (Fin k) < Fintype.card (Fin (k + 1)) := by
    simp
  obtain ⟨i, j, hij, hside⟩ := Fintype.exists_ne_map_eq_of_card_lt side hcard
  have hobs :
      (infer [] (churchApp i.1), s (churchApp i.1)) =
        (infer [] (churchApp j.1), s (churchApp j.1)) := by
    apply Prod.ext
    · rw [infer_churchApp, infer_churchApp]
    · simpa [side] using hside
  have hcost := hlicensed
    (churchApp i.1) ⟨i.1, rfl⟩
    (churchApp j.1) ⟨j.1, rfl⟩
    hobs
  have hi0 : i.1 ≤ k := Nat.lt_succ_iff.mp i.2
  have hj0 : j.1 ≤ k := Nat.lt_succ_iff.mp j.2
  have hi : i.1 + 2 ≤ k + 2 := Nat.add_le_add_right hi0 2
  have hj : j.1 + 2 ≤ k + 2 := Nat.add_le_add_right hj0 2
  rw [betaCost_churchApp i.1 (k + 2) hi, betaCost_churchApp j.1 (k + 2) hj] at hcost
  have hvals : i.1 + 2 = j.1 + 2 := Option.some_injective _ hcost
  have hfin : i = j := Fin.ext (Nat.add_right_cancel hvals)
  exact hij hfin

/--
Proves: any singleton Church retained set is licensed by the plain type observer for any fuel.
Does not prove: maximality of that retained set.
Relation: LicensedOn {churchApp n} (infer []) (betaCost f).
Closure: singleton retained set.
Strategy: leftmost-outermost beta cost.
Trust: kernel-only.
Scope: every fuel f and Church index n.
-/
theorem singleton_church_licensedOn :
    ∀ f n, LicensedOn ({churchApp n} : Set SysTTerm) (infer []) (betaCost f) := by
  intro f n x hx y hy _
  have hx' : x = churchApp n := Set.mem_singleton_iff.mp hx
  have hy' : y = churchApp n := Set.mem_singleton_iff.mp hy
  rw [hx', hy']

/--
Proves: two distinct Church terms cannot both be retained under the plain observer when fuel
covers both exact costs.
Does not prove: failure when one of the two exact costs exceeds the fuel.
Relation: LicensedOn {churchApp m, churchApp n} (infer []) (betaCost f).
Closure: two-element retained set.
Strategy: leftmost-outermost beta cost.
Trust: kernel-only.
Scope: every distinct m,n with m + 2 ≤ f and n + 2 ≤ f.
-/
theorem two_church_not_licensedOn :
    ∀ f m n, m ≠ n → m + 2 ≤ f → n + 2 ≤ f →
      ¬ LicensedOn ({churchApp m, churchApp n} : Set SysTTerm) (infer []) (betaCost f) := by
  intro f m n hmn hm hn hlicensed
  have hobs : infer [] (churchApp m) = infer [] (churchApp n) := by
    rw [infer_churchApp, infer_churchApp]
  have hcost := hlicensed
    (churchApp m) (by simp)
    (churchApp n) (by simp)
    hobs
  rw [betaCost_churchApp m f hm, betaCost_churchApp n f hn] at hcost
  apply hmn
  exact Nat.add_right_cancel (Option.some_injective _ hcost)

/-- Count occurrences of u as a subterm, including the root occurrence. -/
def count (u : SysTTerm) : SysTTerm → Nat
  | .var n => if .var n = u then 1 else 0
  | .lam A b => (if .lam A b = u then 1 else 0) + count u b
  | .app f a => (if .app f a = u then 1 else 0) + count u f + count u a
  | .zero => if .zero = u then 1 else 0
  | .succ t => (if .succ t = u then 1 else 0) + count u t
  | .natrec z s n =>
      (if .natrec z s n = u then 1 else 0) + count u z + count u s + count u n

/- Q49 controls: the requested duplication counts are computed before the theorem. -/
example : count succFn (subst 0 succFn (.lam .nat (churchBody 0))) = 0 := by decide
example : count succFn (subst 0 succFn (.lam .nat (churchBody 1))) = 1 := by decide
example : count succFn (subst 0 succFn (.lam .nat (churchBody 2))) = 2 := by decide

private theorem count_succFn_succChain :
    ∀ n, count succFn (succChain n (.var 0)) = n := by
  intro n
  induction n with
  | zero =>
      decide
  | succ n ih =>
      change
        (if (.app succFn (succChain n (.var 0)) : SysTTerm) = succFn then 1 else 0) +
            count succFn succFn + count succFn (succChain n (.var 0)) = n + 1
      have hroot : (.app succFn (succChain n (.var 0)) : SysTTerm) ≠ succFn := by
        simp [succFn]
      have hself : count succFn succFn = 1 := by decide
      rw [if_neg hroot, hself, ih]
      omega

private theorem count_succFn_lam_succChain :
    ∀ n, count succFn (.lam .nat (succChain n (.var 0))) = n := by
  intro n
  cases n with
  | zero =>
      decide
  | succ n =>
      change
        (if (.lam .nat (.app succFn (succChain n (.var 0))) : SysTTerm) = succFn then 1 else 0) +
            count succFn (.app succFn (succChain n (.var 0))) = n + 1
      have hroot :
          (.lam .nat (.app succFn (succChain n (.var 0))) : SysTTerm) ≠ succFn := by
        simp [succFn]
      have hchain := count_succFn_succChain (n + 1)
      change count succFn (.app succFn (succChain n (.var 0))) = n + 1 at hchain
      rw [if_neg hroot, hchain, Nat.zero_add]

/--
Proves: after the first Church beta substitution, the substituted successor function occurs
exactly n times as a subterm.
Does not prove: a reduction-length formula or an orientation theorem.
Relation: equality of the syntactic subterm count after the carrier's subst.
Closure: one beta substitution expression, not a rewrite closure.
Strategy: not applicable.
Trust: kernel-only; the cases n = 0,1,2 are computed above.
Scope: every Church index n.
-/
theorem church_first_beta_duplicates_function :
    ∀ n,
      count succFn (subst 0 succFn (SysTTerm.lam SysTTy.nat (churchBody n))) = n := by
  intro n
  change
    count succFn
      (.lam .nat (subst 1 (shift 1 0 succFn) (churchBody n))) = n
  have hshift : shift 1 0 succFn = succFn := by decide
  rw [hshift, subst_churchBody]
  exact count_succFn_lam_succChain n

end OperatorKO7.HigherOrderRewritingIndexedLicense
