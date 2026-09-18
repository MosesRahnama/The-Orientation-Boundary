import OperatorKO7.Meta.UniqueNormalization.FenceKernelBridge
import OperatorKO7.Meta.UniqueNormalization.Fence

/-!
# Reach test: the KO7 fence

Campaign: `Roadmaps\klop\ROADMAP.md`, WP-K1a, gate G1a.

This gate imports every module it checks. It asserts that the fence carries
**exactly the four clauses** of the work package and exercises each on the
concrete system, and that the encoded system really is the KO7 kernel's, through
the simulation theorem.

`Fence.lean` states no universal necessity claim, and none is checked here. This gate
uses only the explicit KO7 witness and makes no classification claim about arbitrary UN=
failures or any separate fixture.
-/

set_option autoImplicit false

namespace UN79FenceReach

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization
open OperatorKO7.Meta.UniqueNormalization.KO7Fence

#check @ko7TRS
#check @rIntDelta
#check @rMergeVL
#check @rMergeVR
#check @rMergeCancel
#check @rRecZero
#check @rRecSucc
#check @rEqRefl
#check @rEqDiff
#check @mem_ko7TRS
#check @tVoid
#check @tIntVoid
#check @tMergeVV
#check @tIntMergeVV
#check @tEqVV
#check @constSub
#check @rEqRefl_ne_rEqDiff
#check @eqW_unifiable
#check @eqW_omegaUnifiable
#check @not_nonOverlapping
#check @not_nonOmegaOverlapping
#check @tVoid_normalForm
#check @tIntVoid_normalForm
#check @step_diag_void
#check @step_diag_int
#check @step_mergeVV_void
#check @step_intMergeVV_intVoid
#check @conv_void_intVoid
#check @not_UNconv
#check @not_UNred
#check @eq_of_pair_split
#check @step_mergeVV_eq
#check @afterInt
#check @afterInt_step
#check @afterInt_stepStar
#check @diagonal_peak_not_joinable
#check @rhsDetermined
#check @hypothesis_required
#check @KO7FenceBridge.enc
#check @KO7FenceBridge.sub3
#check @KO7FenceBridge.step_enc
#check @KO7FenceBridge.enc_named
#check @KO7FenceBridge.fork3Kernel
#check @KO7FenceBridge.fork3Kernel_injective
#check @KO7FenceBridge.fork3Kernel_step
#check @KO7FenceBridge.fork3Kernel_step_iff
#check @KO7FenceBridge.kernel_diagonal_contains_initial_fork3
#check @KO7FenceBridge.fork3_reified_step
#check @KO7FenceBridge.kernel_diagonal_fork

/-! ## Axiom parity -/

#print axioms ko7TRS
#print axioms rIntDelta
#print axioms rMergeVL
#print axioms rMergeVR
#print axioms rMergeCancel
#print axioms rRecZero
#print axioms rRecSucc
#print axioms rEqRefl
#print axioms rEqDiff
#print axioms mem_ko7TRS
#print axioms constSub
#print axioms rEqRefl_ne_rEqDiff
#print axioms eqW_unifiable
#print axioms eqW_omegaUnifiable
#print axioms not_nonOverlapping
#print axioms not_nonOmegaOverlapping
#print axioms tVoid
#print axioms tIntVoid
#print axioms tMergeVV
#print axioms tIntMergeVV
#print axioms tEqVV
#print axioms tVoid_normalForm
#print axioms tIntVoid_normalForm
#print axioms step_diag_void
#print axioms step_diag_int
#print axioms step_mergeVV_void
#print axioms step_intMergeVV_intVoid
#print axioms conv_void_intVoid
#print axioms not_UNconv
#print axioms not_UNred
#print axioms eq_of_pair_split
#print axioms step_mergeVV_eq
#print axioms afterInt
#print axioms afterInt_step
#print axioms afterInt_stepStar
#print axioms diagonal_peak_not_joinable
#print axioms rhsDetermined
#print axioms hypothesis_required
#print axioms KO7FenceBridge.enc
#print axioms KO7FenceBridge.sub3
#print axioms KO7FenceBridge.step_enc
#print axioms KO7FenceBridge.enc_named
#print axioms KO7FenceBridge.fork3Kernel
#print axioms KO7FenceBridge.fork3Kernel_injective
#print axioms KO7FenceBridge.fork3Kernel_step
#print axioms KO7FenceBridge.fork3Kernel_step_iff
#print axioms KO7FenceBridge.kernel_diagonal_contains_initial_fork3
#print axioms KO7FenceBridge.fork3_reified_step
#print axioms KO7FenceBridge.kernel_diagonal_fork

/-- Clause 1. The `eqW` pair unifies finitely, so KO7 is outside both classes. -/
example : ¬ NonOverlapping ko7TRS ∧ ¬ NonOmegaOverlapping ko7TRS :=
  ⟨not_nonOverlapping, not_nonOmegaOverlapping⟩

/-- Clause 2. KO7 fails UN= and UN->. -/
example : ¬ UNconv ko7TRS ∧ ¬ UNred ko7TRS := ⟨not_UNconv, not_UNred⟩

/-- Clause 3. The diagonal peak is a non-joinable one-step peak. -/
example :
    Step ko7TRS tEqVV tVoid ∧ Step ko7TRS tEqVV tIntMergeVV ∧
      ¬ joinable ko7TRS tVoid tIntMergeVV :=
  diagonal_peak_not_joinable

/-- Clause 4. The hypothesis is required, with the variable condition satisfied
so the failure is separate from the `FreshRhs` phenomenon. -/
example :
    TRS.RhsDetermined ko7TRS ∧
      ¬ NonOverlapping ko7TRS ∧ ¬ NonOmegaOverlapping ko7TRS ∧
      ¬ UNconv ko7TRS ∧ ¬ UNred ko7TRS ∧
      ¬ joinable ko7TRS tVoid tIntMergeVV :=
  hypothesis_required

/-- The encoded system is the KO7 kernel's: every kernel step is a step of
`ko7TRS` under the encoding. -/
example {a b : OperatorKO7.Trace} (h : OperatorKO7.Step a b) :
    Step ko7TRS (KO7FenceBridge.enc a) (KO7FenceBridge.enc b) :=
  KO7FenceBridge.step_enc h

/-- The kernel's own diagonal fork, with its two contracta non-joinable. -/
example :
    Step ko7TRS (KO7FenceBridge.enc (.eqW .void .void)) (KO7FenceBridge.enc .void) ∧
      Step ko7TRS (KO7FenceBridge.enc (.eqW .void .void))
        (KO7FenceBridge.enc (.integrate (.merge .void .void))) ∧
      ¬ joinable ko7TRS (KO7FenceBridge.enc .void)
        (KO7FenceBridge.enc (.integrate (.merge .void .void))) :=
  KO7FenceBridge.kernel_diagonal_fork

/-- Sanity, by computation: `void` and `integrate(void)` really are distinct
terms, so clause 2 is not vacuous. -/
example : tVoid ≠ tIntVoid := by decide

end UN79FenceReach
