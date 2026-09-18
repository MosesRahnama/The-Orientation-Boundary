import OperatorKO7.Kernel
import OperatorKO7.Meta.UniqueNormalization.Fence
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Crown

/-!
# The KO7 kernel simulates into the encoded fence system

Campaign: `Roadmaps\klop\ROADMAP.md`, WP-K1a.

`Fence.lean` states the four clauses about `ko7TRS`, a first-order
term rewriting system over `Term Nat Nat`. This file connects that system to the
KO7 kernel itself: `enc` encodes `OperatorKO7.Trace` into `Term Nat Nat`, and
`step_enc` proves every one of the kernel's eight root rules is a root
contraction of `ko7TRS`.

The file is separate from `Fence.lean` because `OperatorKO7.Kernel` declares
`Step`, `StepStar` and `NormalForm` at `OperatorKO7.*`, which would shadow the
rewriting library's declarations of the same spelling inside any namespace
nested under `OperatorKO7`. Everything here therefore lives in a top-level
namespace and names the kernel declarations in full.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace KO7FenceBridge

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization.KO7Fence
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork

/-- Encode a KO7 `Trace` as a first-order term over the symbol codes fixed in
`Fence.lean`. -/
def enc : OperatorKO7.Trace → Term Nat Nat
  | .void => .app 0 []
  | .delta t => .app 1 [enc t]
  | .integrate t => .app 2 [enc t]
  | .merge a b => .app 3 [enc a, enc b]
  | .app a b => .app 4 [enc a, enc b]
  | .recΔ a b c => .app 5 [enc a, enc b, enc c]
  | .eqW a b => .app 6 [enc a, enc b]

/-- A substitution fixing the images of variables `0`, `1` and `2`. -/
def sub3 (a b c : Term Nat Nat) : Subst Nat Nat :=
  fun v => if v = 0 then a else if v = 1 then b else c

/-- **The encoding simulates every kernel step.** Each of the eight kernel rules
becomes one root contraction of `ko7TRS`, so the fence results of `Fence.lean`
are results about the KO7 kernel's own rules and not about a loosely related
system. -/
theorem step_enc {a b : OperatorKO7.Trace} (h : OperatorKO7.Step a b) :
    Step ko7TRS (enc a) (enc b) := by
  cases h with
  | R_int_delta t =>
      exact Step.root ⟨rIntDelta, by simp [ko7TRS], constSub (enc t), rfl, rfl⟩
  | R_merge_void_left =>
      exact Step.root ⟨rMergeVL, by simp [ko7TRS], constSub (enc b), rfl, rfl⟩
  | R_merge_void_right =>
      exact Step.root ⟨rMergeVR, by simp [ko7TRS], constSub (enc b), rfl, rfl⟩
  | R_merge_cancel =>
      exact Step.root ⟨rMergeCancel, by simp [ko7TRS], constSub (enc b), rfl, rfl⟩
  | R_rec_zero b s =>
      exact Step.root ⟨rRecZero, by simp [ko7TRS],
        sub3 (enc b) (enc s) (.app 0 []), rfl, rfl⟩
  | R_rec_succ b s n =>
      exact Step.root ⟨rRecSucc, by simp [ko7TRS],
        sub3 (enc b) (enc s) (enc n), rfl, rfl⟩
  | R_eq_refl a =>
      exact Step.root ⟨rEqRefl, by simp [ko7TRS], constSub (enc a), rfl, rfl⟩
  | R_eq_diff a b =>
      exact Step.root ⟨rEqDiff, by simp [ko7TRS],
        sub3 (enc a) (enc b) (enc b), rfl, rfl⟩

/-- The two terms of the fence are the encodings of the kernel terms they are
named for. -/
theorem enc_named :
    enc .void = tVoid ∧
      enc (.integrate .void) = tIntVoid ∧
      enc (.merge .void .void) = tMergeVV ∧
      enc (.integrate (.merge .void .void)) = tIntMergeVV ∧
      enc (.eqW .void .void) = tEqVV :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The canonical three-state fork embedded directly in the KO7 kernel's
`eqW(void,void)` diagonal. -/
def fork3Kernel : Fork3 → OperatorKO7.Trace
  | .source => .eqW .void .void
  | .equal => .void
  | .different => .integrate (.merge .void .void)

/-- The three Fork3 states remain distinct after embedding in the KO7 kernel. -/
theorem fork3Kernel_injective : Function.Injective fork3Kernel := by
  intro x y h
  cases x <;> cases y <;> simp [fork3Kernel] at h ⊢

/-- Every canonical Fork3 edge is literally one of the two kernel diagonal
contractions. -/
theorem fork3Kernel_step {x y : Fork3} (h : Fork3Step x y) :
    OperatorKO7.Step (fork3Kernel x) (fork3Kernel y) := by
  cases h with
  | toEqual => exact OperatorKO7.Step.R_eq_refl .void
  | toDifferent => exact OperatorKO7.Step.R_eq_diff .void .void

/-- The Fork3 relation is exactly the kernel relation induced on the three embedded
states, not merely a forward simulation. -/
theorem fork3Kernel_step_iff {x y : Fork3} :
    Fork3Step x y ↔ OperatorKO7.Step (fork3Kernel x) (fork3Kernel y) := by
  constructor
  · exact fork3Kernel_step
  · intro h
    cases x <;> cases y <;> cases h <;>
      first | exact Fork3Step.toEqual | exact Fork3Step.toDifferent

/-- **The KO7 diagonal contains the initial nonjoinable Fork3 atom.** The first
conjunct gives an injective carrier embedding; the second gives exact relation
reflection on its image; the third imports the already-mechanized initiality theorem for
`fork3Pointed`. This is the full Clause 3 promised by WP-K1a, not merely a
nonjoinable peak. -/
theorem kernel_diagonal_contains_initial_fork3 :
    Function.Injective fork3Kernel ∧
      (∀ x y : Fork3, Fork3Step x y ↔
        OperatorKO7.Step (fork3Kernel x) (fork3Kernel y)) ∧
      Nonempty (CategoryTheory.Limits.IsInitial (fork3Pointed : PointedFork.{0})) :=
  ⟨fork3Kernel_injective, fun _ _ => fork3Kernel_step_iff,
    (minimal_distinction_boundary_crown.{0}).initial⟩

/-- Encoding the Fork3 kernel embedding gives the reified KO7 fence embedding. -/
theorem fork3_reified_step {x y : Fork3} (h : Fork3Step x y) :
    OperatorKO7.Meta.Rewriting.Step ko7TRS
      (enc (fork3Kernel x)) (enc (fork3Kernel y)) :=
  step_enc (fork3Kernel_step h)

/-- The kernel's own diagonal fork, transported: `eqW(void, void)` contracts to
`void` by `R_eq_refl` and to `integrate(merge(void, void))` by `R_eq_diff`, and
the two results have no common reduct in the encoded system. -/
theorem kernel_diagonal_fork :
    Step ko7TRS (enc (.eqW .void .void)) (enc .void) ∧
      Step ko7TRS (enc (.eqW .void .void)) (enc (.integrate (.merge .void .void))) ∧
      ¬ joinable ko7TRS (enc .void) (enc (.integrate (.merge .void .void))) :=
  ⟨step_enc (OperatorKO7.Step.R_eq_refl .void),
    step_enc (OperatorKO7.Step.R_eq_diff .void .void),
    diagonal_peak_not_joinable.2.2⟩

end KO7FenceBridge

/-! ## Reach and axiom audit -/

#check @KO7FenceBridge.enc
#check @KO7FenceBridge.step_enc
#check @KO7FenceBridge.fork3Kernel
#check @KO7FenceBridge.fork3Kernel_injective
#check @KO7FenceBridge.fork3Kernel_step
#check @KO7FenceBridge.fork3Kernel_step_iff
#check @KO7FenceBridge.kernel_diagonal_contains_initial_fork3
#check @KO7FenceBridge.fork3_reified_step

#print axioms KO7FenceBridge.step_enc
#print axioms KO7FenceBridge.enc_named
#print axioms KO7FenceBridge.fork3Kernel_injective
#print axioms KO7FenceBridge.fork3Kernel_step
#print axioms KO7FenceBridge.fork3Kernel_step_iff
#print axioms KO7FenceBridge.kernel_diagonal_contains_initial_fork3
#print axioms KO7FenceBridge.fork3_reified_step
#print axioms KO7FenceBridge.kernel_diagonal_fork
