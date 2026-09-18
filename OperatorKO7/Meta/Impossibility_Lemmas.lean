import OperatorKO7.Kernel
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith
import OperatorKO7.Meta.ComputableMeasure
-- Counterexamples for selected termination-measure families.

/-!
# Counterexamples for selected measure families

This module records explicit counterexamples for several simple measures on the
KO7 trace syntax. Each result is limited to the definition named in its theorem.

The counterexamples cover `kappa + k`, a two-component lexicographic measure,
a root `delta` flag, constellation size, and the additive `simpleSize` measure.
The imported safe-step measure is included only as a contrasting certified
construction; this module does not classify all termination orderings.
-/


namespace OperatorKO7
namespace Impossibility

 -- Short local names for the declarations below.
 open OperatorKO7 Trace
 open Prod (Lex)

/-! The declarations below are concrete witnesses over `Trace` and `Step`. -/

end Impossibility
end OperatorKO7

namespace OperatorKO7
namespace Impossibility

-- These proofs refute the particular measure definitions stated below. They do
-- not establish a universal lower bound over all termination methods.

-- Shorten local names for the active content below.
open Trace
open Prod (Lex)

namespace FailedMeasures

/-- A depth-based counter for `recΔ` nodes. -/
@[simp]
def kappa : Trace → Nat
  | recΔ _ _ n => kappa n + 1
  | delta t    => kappa t
  | integrate t=> kappa t
  | merge a b  => max (kappa a) (kappa b)
  | app a b    => max (kappa a) (kappa b)
  | eqW a b    => max (kappa a) (kappa b)
  | _          => 0

/-- A simple size-based ordinal measure. The definition is not needed,
only its type, to demonstrate the failure of lexicographic ordering. -/
def mu (_t : Trace) : Nat := 0

/-! ### Theorem 1: Failure of `kappa + k`
For the defined `kappa`, adding the same fixed constant to both sides does not
orient every `rec_succ` instance. The witness uses a nested `delta` term.
-/
theorem kappa_plus_k_fails (k : Nat) :
  ¬ (∀ (b s n : Trace),
      kappa (app s (recΔ b s n)) + k < kappa (recΔ b s (delta n)) + k) := by
  -- We prove this by providing a concrete counterexample.
  push_neg
  -- The counterexample uses a nested `delta` to show the additive bump `+1` from
  -- the outer `delta` is cancelled by the `+1` from the inner `recΔ`.
  use void, void, delta void
  -- The goal is now a concrete inequality, which we can simplify.
  -- After simp, the goal is `¬(1 + k < 1 + k)`.
  simp [kappa]

/-! ### Theorem 2: Failure of Simple Lexicography
The defined two-component lexicographic pair `(kappa, mu)` fails on a concrete
`rec_succ` instance because both components tie.
-/
theorem simple_lex_fails :
  ¬ (∀ (b s n : Trace),
      Lex (·<·) (·<·)
        (kappa (app s (recΔ b s n)), mu (app s (recΔ b s n)))
        (kappa (recΔ b s (delta n)), mu (recΔ b s (delta n)))) := by
  push_neg
  -- The counterexample is `n := void`, which becomes the base case for `recΔ`
  -- after one step.
  use void, recΔ void void void, void
  -- After substituting, we need to show the Lex relation does not hold.
  -- This reduces to `¬ Lex (·<·) (·<·) (1, 0) (1, 0)`, which is decidable.
  simp [kappa, mu]; decide

end FailedMeasures

/-! ## Boolean delta flag

The root-shape flag increases on a concrete `merge` step, so this flag by itself
does not decrease on every `Step`. -/
namespace FlagFailure

/-- Top-shape flag: 1 only when the term is headed by `delta`. -/
@[simp] def deltaFlagTop : Trace → Nat
  | Trace.delta _ => 1
  | _             => 0

/-- Concrete increase: `merge void (delta void) → delta void` raises `deltaFlagTop`
from 0 to 1. This shows a flag-only primary component can increase on a legal
kernel step (violates lex monotonicity if used unguarded). -/
theorem merge_void_raises_flag :
    let t := Trace.delta Trace.void
    OperatorKO7.Step (Trace.merge Trace.void t) t ∧
    deltaFlagTop (Trace.merge Trace.void t) < deltaFlagTop t := by
  intro t; constructor
  · -- The step exists by R_merge_void_left
    exact OperatorKO7.Step.R_merge_void_left t
  · -- Compute flags: top of `merge void (delta void)` is not `delta`.
    -- top of `t` is `delta`.
    -- After simplification, the goal becomes `0 < 1`.
    have ht : t = Trace.delta Trace.void := rfl
    simp [deltaFlagTop, ht]

end FlagFailure

/-! ## Branchwise definitional equalities

The two constructor clauses of `f` reduce definitionally, while the corresponding
constant global equation is refuted by the `B` constructor. -/
namespace RflGate

inductive Two where | A | B deriving DecidableEq, Repr

def f : Two → Nat
  | .A => 0
  | .B => 1

-- Per-branch rfl (passes):
theorem f_Two_A_eq_zero : f Two.A = 0 := rfl
theorem f_Two_B_eq_one : f Two.B = 1 := rfl

-- Over-strong global law fails: not (∀ x, f x = 0)
theorem not_forall_f_eq_zero : ¬ (∀ x, f x = 0) := by
  intro h
  -- f B = 1 contradicts h B : f B = 0
  exact Nat.one_ne_zero (by simpa [f] using h Two.B)

end RflGate

/-! ## Imported safe-step measure examples

`Meta/ComputableMeasure.lean` supplies the `Lex3c` decrease and well-foundedness
theorems used below for the selected guarded `SafeStep` relation. -/

namespace KO7_FixPathExamples

open OperatorKO7.MetaCM

-- The `rec_succ` constructor strictly decreases the imported `Lex3c` measure.
lemma rec_succ_drops (b s n : Trace) :
   Lex3c (mu3c (app s (recΔ b s n)))
         (mu3c (recΔ b s (delta n))) := by
   simpa using drop_R_rec_succ_c b s n

-- The aggregate theorem supplies the same decrease for this safe-step instance.
lemma safe_decrease_rec_succ (b s n : Trace) :
   Lex3c (mu3c (app s (recΔ b s n)))
         (mu3c (recΔ b s (delta n))) := by
   simpa using
     (measure_decreases_safe_c
        (MetaSN_KO7.SafeStep.R_rec_succ b s n))

-- Well-foundedness of the reverse safe-step relation.
theorem wf_safe : WellFounded MetaSN_KO7.SafeStepRev := wf_SafeStepRev_c

end KO7_FixPathExamples

/-! ## Additional imported decrease instances -/

namespace Computable_FixPathExamples

open OperatorKO7.MetaCM

lemma drop_rec_succ (b s n : Trace) :
  Lex3c (mu3c (app s (recΔ b s n))) (mu3c (recΔ b s (delta n))) := by
  simpa using drop_R_rec_succ_c b s n

lemma drop_merge_void_left (t : Trace) (hδ : MetaSN_KO7.deltaFlag t = 0) :
  Lex3c (mu3c t) (mu3c (merge void t)) := by
  simpa using drop_R_merge_void_left_c t hδ

lemma drop_eq_diff (a b : Trace) :
  Lex3c (mu3c (integrate (merge a b))) (mu3c (eqW a b)) := by
  simpa using drop_R_eq_diff_c a b

end Computable_FixPathExamples

/-! ## Constellation-shape examples

The abstraction below retains constructor shape and forgets leaf content. The
proved results establish constructor inequality and failure of its additive node
count on the duplicating rule. They make no claim about every order on shapes.
-/
namespace ConstellationFailure

/-- A constellation is an abstraction of term structure (shape without content).
    Note: We use `recNode` instead of `rec` to avoid conflict with the eliminator. -/
inductive Constellation where
  | atom : Constellation
  | deltaNode : Constellation → Constellation
  | integrateNode : Constellation → Constellation
  | mergeNode : Constellation → Constellation → Constellation
  | appNode : Constellation → Constellation → Constellation
  | recNode : Constellation → Constellation → Constellation → Constellation
  | eqNode : Constellation → Constellation → Constellation
  deriving DecidableEq, Repr

/-- Extract constellation from a trace (forgetting content, keeping shape). -/
def toConstellation : Trace → Constellation
  | .void => .atom
  | .delta t => .deltaNode (toConstellation t)
  | .integrate t => .integrateNode (toConstellation t)
  | .merge a b => .mergeNode (toConstellation a) (toConstellation b)
  | .app a b => .appNode (toConstellation a) (toConstellation b)
  | .recΔ b s n => .recNode (toConstellation b) (toConstellation s) (toConstellation n)
  | .eqW a b => .eqNode (toConstellation a) (toConstellation b)

/-- The two sides of the delta-duplication step have different root constructors
in the constellation abstraction. -/
theorem constellation_shapes_differ (b s n : Trace) :
    toConstellation (app s (recΔ b s n)) ≠ toConstellation (recΔ b s (delta n)) := by
  simp only [toConstellation]
  intro h
  cases h

/-- A simple constellation size measure (counting nodes). -/
def constellationSize : Constellation → Nat
  | .atom => 1
  | .deltaNode c => constellationSize c + 1
  | .integrateNode c => constellationSize c + 1
  | .mergeNode a b => constellationSize a + constellationSize b + 1
  | .appNode a b => constellationSize a + constellationSize b + 1
  | .recNode b s n => constellationSize b + constellationSize s + constellationSize n + 1
  | .eqNode a b => constellationSize a + constellationSize b + 1

/-- The right side of the delta-duplication rule has at least the left side's
    constellation size when `s` has constellation size at least one.
    LHS: recNode(b, s, deltaNode(n)) has size = |b| + |s| + (|n| + 1) + 1
    RHS: appNode(s, recNode(b, s, n)) has size = |s| + (|b| + |s| + |n| + 1) + 1
    Difference: RHS - LHS = |s| - 1 ≥ 0 when |s| ≥ 1. -/
theorem constellation_size_not_decreasing (b s n : Trace)
    (hs : constellationSize (toConstellation s) ≥ 1) :
    constellationSize (toConstellation (app s (recΔ b s n))) ≥
    constellationSize (toConstellation (recΔ b s (delta n))) := by
  simp only [toConstellation, constellationSize]
  omega

end ConstellationFailure

/-! ## Additive-size behavior of the duplicating rule

The rule `recΔ b s (delta n) -> app s (recΔ b s n)` duplicates `s` while
removing one outer `delta` from the recursive argument. The following theorems
compute its effect on the particular additive measure `simpleSize`. -/
namespace UncheckedRecursionFailure

/-- Additive size on the trace constructors. -/
def simpleSize : Trace → Nat
  | .void => 0
  | .delta t => simpleSize t + 1
  | .integrate t => simpleSize t + 1
  | .merge a b => simpleSize a + simpleSize b + 1
  | .app a b => simpleSize a + simpleSize b + 1
  | .recΔ b s n => simpleSize b + simpleSize s + simpleSize n + 1
  | .eqW a b => simpleSize a + simpleSize b + 1

/-- The rec_succ rule is the structural barrier for additive measures.
    LHS: simpleSize(recΔ b s (delta n)) = |b| + |s| + (|n| + 1) + 1 = |b| + |s| + |n| + 2
    RHS: simpleSize(app s (recΔ b s n)) = |s| + (|b| + |s| + |n| + 1) + 1 = 2|s| + |b| + |n| + 2
    Difference: RHS - LHS = |s| >= 0. -/
theorem rec_succ_additive_barrier (b s n : Trace) :
    simpleSize (app s (recΔ b s n)) ≥ simpleSize (recΔ b s (delta n)) := by
  simp only [simpleSize]
  omega

/-- The right side is strictly larger when `s` has positive `simpleSize`. -/
theorem rec_succ_size_increases (b s n : Trace) (hs : simpleSize s ≥ 1) :
    simpleSize (app s (recΔ b s n)) > simpleSize (recΔ b s (delta n)) := by
  simp only [simpleSize]
  omega

/-- The full `Step` relation contains an instance of the duplicating rule. -/
theorem full_step_permits_barrier :
    ∃ b s n, Step (recΔ b s (delta n)) (app s (recΔ b s n)) := by
  exact ⟨void, void, void, Step.R_rec_succ void void void⟩

/-- The imported computable measure proves well-foundedness of the reverse
    selected `SafeStep` relation. -/
theorem wf_SafeStepRev_via_computable :
    WellFounded MetaSN_KO7.SafeStepRev := OperatorKO7.MetaCM.wf_SafeStepRev_c

end UncheckedRecursionFailure

end Impossibility
end OperatorKO7
