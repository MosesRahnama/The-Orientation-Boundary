import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
import OperatorKO7.Meta.OperationalInexpressibility.KO7ObservationVerdict

/-!
# Verdict-informational deficit on a terminating cell

This module distinguishes uncertainty over a sound termination verdict from
uncertainty over a termination witness.  A prior ranges over verdict functions,
not over already chosen Boolean values.  If the prior is normalized and supported
on verdict functions sound for the relation-level strong-normalization predicate,
then a proved terminating cell pushes every such verdict function to `true`.
The induced verdict marginal is therefore derived to be a point mass and has zero
Shannon entropy.

Relation: the relation carried by
`OperationalInexpressibility.KO7ObservationVerdict.RelationSystem`.
Closure: strong normalization is well-foundedness of the reverse relation.
Strategy: full root relation for the recursor cell.
Trust: kernel-checked proof terms plus the finite real-entropy substrate.
Scope: normalized real priors supported on sound verdict functions.  This does not
claim zero entropy for witnesses or for priors assigning mass to unsound verdicts.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.InformationalIncompleteness.VerdictDeficit

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.OperationalInexpressibility.KO7ObservationVerdict

/-- A Boolean verdict function on the concrete two-system carrier. -/
abbrev VerdictFunction := RelationSystem → Bool

/-- Soundness means that `true` is returned exactly on strongly normalizing
relation systems. -/
def IsSoundVerdict (verdict : VerdictFunction) : Prop :=
  ∀ system, verdict system = true ↔ StrongNormalizationVerdict system

/-- A prior is supported on sound verdict functions when every unsound function
has zero mass. -/
def SupportedOnSoundVerdicts (prior : VerdictFunction → ℝ) : Prop :=
  ∀ verdict, ¬ IsSoundVerdict verdict → prior verdict = 0

/-- A strong-normalization proof determines every sound verdict function at that
cell. -/
theorem soundVerdict_eq_true_of_terminating
    (system : RelationSystem) (hSN : StrongNormalizationVerdict system)
    (verdict : VerdictFunction) (hsound : IsSoundVerdict verdict) :
    verdict system = true :=
  (hsound system).2 hSN

/-- In particular, every sound verdict function returns `true` on the concrete
KO7 recursor relation. -/
theorem soundVerdict_recursor_eq_true
    (verdict : VerdictFunction) (hsound : IsSoundVerdict verdict) :
    verdict RelationSystem.recursor = true :=
  soundVerdict_eq_true_of_terminating RelationSystem.recursor
    recursor_strongNormalizationVerdict verdict hsound

/-- Push a prior over verdict functions through evaluation at one system cell. -/
noncomputable def verdictCellMarginal (system : RelationSystem)
    (prior : VerdictFunction → ℝ) : Bool → ℝ :=
  fun result => ∑ verdict, if verdict system = result then prior verdict else 0

/-- On a proved terminating cell, every normalized prior supported on sound verdict
functions induces the point mass at `true`.

The point mass is a conclusion here, not an input: termination and sound-support
force every positive-prior verdict function to agree at the cell.
-/
theorem verdictCellMarginal_eq_pointMass_of_terminating
    (system : RelationSystem) (hSN : StrongNormalizationVerdict system)
    (prior : VerdictFunction → ℝ)
    (htotal : ∑ verdict, prior verdict = 1)
    (hsupport : SupportedOnSoundVerdicts prior) :
    verdictCellMarginal system prior = pointMass true := by
  classical
  have htrue : ∀ verdict : VerdictFunction,
      (if verdict system = true then prior verdict else 0) = prior verdict := by
    intro verdict
    by_cases hs : IsSoundVerdict verdict
    · have hv : verdict system = true :=
        soundVerdict_eq_true_of_terminating system hSN verdict hs
      simp [hv]
    · have hp : prior verdict = 0 := hsupport verdict hs
      by_cases hv : verdict system = true
      · simp [hv, hp]
      · simp [hv, hp]
  have hfalse : ∀ verdict : VerdictFunction,
      (if verdict system = false then prior verdict else 0) = 0 := by
    intro verdict
    by_cases hs : IsSoundVerdict verdict
    · have hv : verdict system = true :=
        soundVerdict_eq_true_of_terminating system hSN verdict hs
      simp [hv]
    · have hp : prior verdict = 0 := hsupport verdict hs
      by_cases hv : verdict system = false
      · simp [hv, hp]
      · simp [hv]
  funext result
  cases result with
  | false =>
      change (∑ verdict, if verdict system = false then prior verdict else 0) =
        (if false = true then 1 else 0)
      simp only [Bool.false_eq_true, if_false]
      apply Finset.sum_eq_zero
      intro verdict _
      exact hfalse verdict
  | true =>
      change (∑ verdict, if verdict system = true then prior verdict else 0) =
        (if true = true then 1 else 0)
      calc
        (∑ verdict, if verdict system = true then prior verdict else 0) =
            ∑ verdict, prior verdict := by
              apply Finset.sum_congr rfl
              intro verdict _
              exact htrue verdict
        _ = 1 := htotal
        _ = (if true = true then 1 else 0) := by simp

/--
Headline verdict-deficit theorem.  A strong-normalization proof determines the
sound verdict at the cell under every normalized sound-support prior, so its
verdict entropy is zero.

Does not prove: that witness entropy is zero, or that an unlicensed observer can
construct the strong-normalization proof.
-/
theorem verdict_deficit_zero_of_terminating
    (system : RelationSystem) (hSN : StrongNormalizationVerdict system)
    (prior : VerdictFunction → ℝ)
    (htotal : ∑ verdict, prior verdict = 1)
    (hsupport : SupportedOnSoundVerdicts prior) :
    H (verdictCellMarginal system prior) = 0 := by
  rw [verdictCellMarginal_eq_pointMass_of_terminating
    system hSN prior htotal hsupport]
  exact H_pointMass true

/-! ## Canonical non-vacuity witness and KO7 specialization -/

/-- The already verified finite termination verdict is itself sound. -/
theorem terminationVerdict_isSound : IsSoundVerdict terminationVerdict := by
  intro system
  exact terminationVerdict_eq_true_iff system

/-- A concrete prior concentrated on the verified sound verdict function. -/
noncomputable def canonicalSoundVerdictPrior : VerdictFunction → ℝ :=
  by
    classical
    exact pointMass terminationVerdict

/-- The canonical sound-verdict prior is normalized. -/
theorem canonicalSoundVerdictPrior_total :
    ∑ verdict, canonicalSoundVerdictPrior verdict = 1 := by
  classical
  simp [canonicalSoundVerdictPrior, pointMass]

/-- The canonical prior assigns zero mass to every unsound verdict function. -/
theorem canonicalSoundVerdictPrior_supported :
    SupportedOnSoundVerdicts canonicalSoundVerdictPrior := by
  classical
  intro verdict hunsound
  have hne : verdict ≠ terminationVerdict := by
    intro heq
    apply hunsound
    rw [heq]
    exact terminationVerdict_isSound
  simp [canonicalSoundVerdictPrior, pointMass, hne]

/-- The concrete KO7 recursor cell has zero verdict deficit under every normalized
prior supported on sound verdict functions, using the mechanized full-root
strong-normalization theorem. -/
theorem ko7_recursor_verdict_deficit_zero
    (prior : VerdictFunction → ℝ)
    (htotal : ∑ verdict, prior verdict = 1)
    (hsupport : SupportedOnSoundVerdicts prior) :
    H (verdictCellMarginal RelationSystem.recursor prior) = 0 :=
  verdict_deficit_zero_of_terminating RelationSystem.recursor
    recursor_strongNormalizationVerdict prior htotal hsupport

/-- Fully inhabited instance of the KO7 verdict-deficit theorem. -/
theorem ko7_recursor_canonicalPrior_verdict_deficit_zero :
    H (verdictCellMarginal RelationSystem.recursor canonicalSoundVerdictPrior) = 0 :=
  ko7_recursor_verdict_deficit_zero canonicalSoundVerdictPrior
    canonicalSoundVerdictPrior_total canonicalSoundVerdictPrior_supported

end OperatorKO7.Meta.InformationalIncompleteness.VerdictDeficit
