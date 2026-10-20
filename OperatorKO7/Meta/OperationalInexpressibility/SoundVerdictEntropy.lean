import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
import OperatorKO7.Meta.Methods.OrientationClosure.DependencyPairSoundness

/-!
# A sound verdict gives no information about a terminating instance

A Boolean verdict is sound for a property when it returns true exactly where the property holds.
At an instance where the property holds, every sound verdict returns true, so the output of any
finite family of sound verdicts under a probability law is a point mass and has zero Shannon
entropy. The free recursor terminates, so this holds for termination verdicts at the recursor.

Relation: evaluation of verdicts at one instance.
Property: the output law is a point mass; zero entropy.
Trust: kernel only.
Scope: arbitrary instance types; finite families of verdicts with real weights summing to one.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.SoundVerdictEntropy

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness

universe u

/-- A Boolean verdict is sound for `holds` when it returns true exactly where `holds` is true. -/
def SoundVerdict {α : Type u} (holds : α → Prop) (v : α → Bool) : Prop :=
  ∀ a, v a = true ↔ holds a

theorem SoundVerdict.eq_true {α : Type u} {holds : α → Prop} {v : α → Bool}
    (hv : SoundVerdict holds v) {a : α} (ha : holds a) : v a = true :=
  (hv a).2 ha

/-- The law of the output at `a` of a finite family of verdicts with weights `w`. -/
noncomputable def outputLaw {ι : Type} [Fintype ι] {α : Type u} (V : ι → α → Bool) (w : ι → ℝ)
    (a : α) : Bool → ℝ :=
  fun b => ∑ i, if V i a = b then w i else 0

theorem outputLaw_eq_pointMass {ι : Type} [Fintype ι] {α : Type u} {holds : α → Prop}
    (V : ι → α → Bool) (w : ι → ℝ) (hw1 : ∑ i, w i = 1)
    (hsound : ∀ i, w i ≠ 0 → SoundVerdict holds (V i)) {a : α} (ha : holds a) :
    outputLaw V w a = pointMass true := by
  funext b
  cases b with
  | false =>
      unfold outputLaw pointMass
      rw [if_neg (by decide : ¬((false : Bool) = true))]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hwi : w i = 0
      · simp [hwi]
      · have htrue : V i a = true := (hsound i hwi).eq_true ha
        rw [htrue]
        simp
  | true =>
      unfold outputLaw pointMass
      rw [if_pos rfl]
      have h : ∀ i, (if V i a = true then w i else (0 : ℝ)) = w i := by
        intro i
        by_cases hwi : w i = 0
        · simp [hwi]
        · rw [if_pos ((hsound i hwi).eq_true ha)]
      simp only [h, hw1]

/-- **Zero entropy of the output.** -/
theorem outputLaw_entropy_zero {ι : Type} [Fintype ι] {α : Type u} {holds : α → Prop}
    (V : ι → α → Bool) (w : ι → ℝ) (hw1 : ∑ i, w i = 1)
    (hsound : ∀ i, w i ≠ 0 → SoundVerdict holds (V i)) {a : α} (ha : holds a) :
    H (outputLaw V w a) = 0 := by
  rw [outputLaw_eq_pointMass V w hw1 hsound ha]
  exact H_pointMass true

/-- Every sound termination verdict is true on the free recursor. -/
theorem recursor_soundVerdict_true (v : TRS FreeSym Nat → Bool)
    (hv : SoundVerdict (fun R => ∀ t, SN R t) v) : v freeRecursorTRS = true :=
  hv.eq_true freeRecursorTRS_terminating

theorem recursor_outputLaw_entropy_zero {ι : Type} [Fintype ι] (V : ι → TRS FreeSym Nat → Bool)
    (w : ι → ℝ) (hw1 : ∑ i, w i = 1)
    (hsound : ∀ i, w i ≠ 0 → SoundVerdict (fun R => ∀ t, SN R t) (V i)) :
    H (outputLaw V w freeRecursorTRS) = 0 :=
  outputLaw_entropy_zero V w hw1 hsound freeRecursorTRS_terminating

end OperatorKO7.Meta.OperationalInexpressibility.SoundVerdictEntropy
