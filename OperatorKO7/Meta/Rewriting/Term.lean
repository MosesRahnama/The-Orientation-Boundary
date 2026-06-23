import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

/-!
# First-order terms for the generic rewriting library

Roadmap source: `ROADMAP-01-generic-critical-pair-lemma.md`, sections 4 and 5
(`Meta/Rewriting/Term.lean`). This is Wave 1 of the rewriting foundation: a
clean, self-contained first-order term type over an arbitrary signature `sigma`
and variable type `nu`, with a custom nested-`List` eliminator so structural
recursion through the argument list goes through, a `DecidableEq` instance, a
structural size, and the occurring-variable set.

The SHAPE mirrors the proven `FOTm` blueprint at
`Meta/EstimatedDPGraphTcap.lean:43,52` (variable/application over `List`, with a
custom recursor `FOTm.rec'`). This layer is standalone: it does not import the
dependency-pair internals, so the downstream unification and critical-pair
development can rest on its own API.

Trust: kernel-only; baseline-only under `#print axioms` (subset of
`{propext, Classical.choice, Quot.sound}`). The `Classical.choice` and `propext`
dependence that appears is from `Finset`/`DecidableEq` plumbing only.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting

universe u v

/-- First-order term over a signature `sigma` and a variable type `nu`: a
variable, or a function symbol applied to a list of argument terms. Mirrors the
`FOTm` blueprint syntax with the symbol and variable types made generic. -/
inductive Term (sigma : Type u) (nu : Type v) : Type (max u v)
  | var : nu → Term sigma nu
  | app : sigma → List (Term sigma nu) → Term sigma nu

namespace Term

variable {sigma : Type u} {nu : Type v}

/-- Custom induction principle giving, in the `app` case, the induction
hypothesis on every argument in the list. This is the nested-`List` recursor
mirroring `FOTm.rec'`; it lets later recursive definitions and proofs descend
through the argument list. -/
@[elab_as_elim]
def rec' {motive : Term sigma nu → Prop}
    (hvar : ∀ x, motive (.var x))
    (happ : ∀ f args, (∀ a ∈ args, motive a) → motive (.app f args)) :
    ∀ t, motive t
  | .var x => hvar x
  | .app f args => happ f args (fun a ha =>
      have _hmem : a ∈ args := ha
      rec' hvar happ a)
  termination_by t => sizeOf t
  decreasing_by
    · exact List.sizeOf_lt_of_mem ha |>.trans_le (by
        simp only [Term.app.sizeOf_spec]; omega)

/-- The term is an application (a function symbol applied to arguments). -/
def isApp : Term sigma nu → Bool
  | .var _ => false
  | .app _ _ => true

/-- The term is a variable. -/
def isVar : Term sigma nu → Bool
  | .var _ => true
  | .app _ _ => false

@[simp] theorem isApp_var (x : nu) : (Term.var (sigma := sigma) x).isApp = false := rfl
@[simp] theorem isApp_app (f : sigma) (args : List (Term sigma nu)) :
    (Term.app f args).isApp = true := rfl
@[simp] theorem isVar_var (x : nu) : (Term.var (sigma := sigma) x).isVar = true := rfl
@[simp] theorem isVar_app (f : sigma) (args : List (Term sigma nu)) :
    (Term.app f args).isVar = false := rfl

mutual
/-- Structural size: a variable has size `1`, an application has size
`1 + sum of argument sizes`. Defined through the list with an auxiliary
`sizeList` so the nested recursion is structural. -/
def size : Term sigma nu → Nat
  | .var _ => 1
  | .app _ args => 1 + sizeList args
/-- Sum of sizes over an argument list. -/
def sizeList : List (Term sigma nu) → Nat
  | [] => 0
  | a :: as => size a + sizeList as
end

@[simp] theorem size_var (x : nu) : size (Term.var (sigma := sigma) x) = 1 := rfl
@[simp] theorem size_app (f : sigma) (args : List (Term sigma nu)) :
    size (Term.app f args) = 1 + sizeList args := rfl
@[simp] theorem sizeList_nil : sizeList ([] : List (Term sigma nu)) = 0 := rfl
@[simp] theorem sizeList_cons (a : Term sigma nu) (as : List (Term sigma nu)) :
    sizeList (a :: as) = size a + sizeList as := rfl

/-- The size of every term is at least `1`. -/
theorem one_le_size (t : Term sigma nu) : 1 ≤ size t := by
  cases t with
  | var x => simp
  | app f args => simp only [size_app]; omega

/-- An argument's size is strictly below the size of the application carrying it. -/
theorem size_lt_of_mem {f : sigma} {args : List (Term sigma nu)} {a : Term sigma nu}
    (ha : a ∈ args) : size a < size (Term.app f args) := by
  simp only [size_app]
  have hsum : size a ≤ sizeList args := by
    clear f
    induction args with
    | nil => simp at ha
    | cons b bs ih =>
        simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · simp only [sizeList_cons]; omega
        · have := ih ha
          simp only [sizeList_cons]
          have hb := one_le_size b
          omega
  omega

mutual
/-- The set of variables occurring in a term. Defined through the list with an
auxiliary `varsList` so the nested recursion is structural. -/
def vars [DecidableEq nu] : Term sigma nu → Finset nu
  | .var x => {x}
  | .app _ args => varsList args
/-- Union of variable sets over an argument list. -/
def varsList [DecidableEq nu] : List (Term sigma nu) → Finset nu
  | [] => ∅
  | a :: as => vars a ∪ varsList as
end

@[simp] theorem vars_var [DecidableEq nu] (x : nu) :
    vars (Term.var (sigma := sigma) x) = {x} := rfl
@[simp] theorem vars_app [DecidableEq nu] (f : sigma) (args : List (Term sigma nu)) :
    vars (Term.app f args) = varsList args := rfl
@[simp] theorem varsList_nil [DecidableEq nu] :
    varsList ([] : List (Term sigma nu)) = ∅ := rfl
@[simp] theorem varsList_cons [DecidableEq nu] (a : Term sigma nu)
    (as : List (Term sigma nu)) :
    varsList (a :: as) = vars a ∪ varsList as := rfl

/-- Membership in `varsList` is membership in some argument's variable set. -/
theorem mem_varsList_iff [DecidableEq nu] {x : nu} {args : List (Term sigma nu)} :
    x ∈ varsList args ↔ ∃ a ∈ args, x ∈ vars a := by
  induction args with
  | nil => simp
  | cons a as ih =>
      simp only [varsList_cons, Finset.mem_union, List.mem_cons, ih]
      constructor
      · rintro (h | ⟨b, hb, hx⟩)
        · exact ⟨a, Or.inl rfl, h⟩
        · exact ⟨b, Or.inr hb, hx⟩
      · rintro ⟨b, hb | hb, hx⟩
        · exact Or.inl (hb ▸ hx)
        · exact Or.inr ⟨b, hb, hx⟩

/-! ## DecidableEq -/

mutual
/-- Structural decidable equality on terms, threaded through the argument list
with an auxiliary list comparator so the nested recursion is structural. The
public instance `instDecidableEq` is built from `decEq`. -/
def decEq [DecidableEq sigma] [DecidableEq nu] :
    (s t : Term sigma nu) → Decidable (s = t)
  | .var x, .var y =>
      if h : x = y then .isTrue (by rw [h]) else .isFalse (by simp [h])
  | .var _, .app _ _ => .isFalse (by simp)
  | .app _ _, .var _ => .isFalse (by simp)
  | .app f xs, .app g ys =>
      if hfg : f = g then
        match decEqList xs ys with
        | .isTrue h => .isTrue (by rw [hfg, h])
        | .isFalse h => .isFalse (by simp [hfg, h])
      else .isFalse (by simp [hfg])
/-- Structural decidable equality on argument lists, the list companion of
`decEq`. -/
def decEqList [DecidableEq sigma] [DecidableEq nu] :
    (xs ys : List (Term sigma nu)) → Decidable (xs = ys)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (by simp)
  | _ :: _, [] => .isFalse (by simp)
  | x :: xs, y :: ys =>
      match decEq x y with
      | .isTrue hx =>
          match decEqList xs ys with
          | .isTrue hxs => .isTrue (by rw [hx, hxs])
          | .isFalse hxs => .isFalse (by simp [hxs])
      | .isFalse hx => .isFalse (by simp [hx])
end

instance instDecidableEq [DecidableEq sigma] [DecidableEq nu] :
    DecidableEq (Term sigma nu) := decEq

end Term

end OperatorKO7.Meta.Rewriting

/-! ## Axiom audit -/

#print axioms OperatorKO7.Meta.Rewriting.Term.rec'
#print axioms OperatorKO7.Meta.Rewriting.Term.size
#print axioms OperatorKO7.Meta.Rewriting.Term.vars
#print axioms OperatorKO7.Meta.Rewriting.Term.size_lt_of_mem
#print axioms OperatorKO7.Meta.Rewriting.Term.mem_varsList_iff
#print axioms OperatorKO7.Meta.Rewriting.Term.instDecidableEq
