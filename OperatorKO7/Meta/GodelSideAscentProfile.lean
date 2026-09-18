import OperatorKO7.Meta.ClassicalAscentProfile
import OperatorKO7.Meta.DistinctionBoundary.GodelFirstIncompleteness
import OperatorKO7.Meta.DistinctionBoundary.GodelNonstandardModel
import OperatorKO7.Meta.LicensedBoundaryCalculus.LicensedAscentTransport
import OperatorKO7.Meta.SafeStep.AscentProfileDegeneracy

/-!
# Compiled Gödel side of the six-step profile

`godel1931PaperAscentProfile` is a synthetic all-`True` model. This module
fills the six stages with compiled objects from the live Gödel stack: the
checker proves something, falsum is not a Gödel sentence, `ConQ` is unprovable,
`ModelInf` models Q and refutes `ConQ`, and `¬ConQ` is unprovable.

The licensed-ascent object below packages those two facts as a one-step expiry
(a Q-theorem to `ConQ`). It is not a Hilbert derivation. The corner map to
`quotationAscent` sends that one repaired step to the quote/eval peak.

Trust: kernel-only. No `sorry`/`admit`/`axiom`/`native_decide`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OperatorKO7.Meta.GodelSideAscentProfile

open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ClassicalAscentProfile
open OperatorKO7.Meta.DistinctionBoundary.GodelArith
open OperatorKO7.Meta.DistinctionBoundary.GodelPartial
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicenseExpiryCategory
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicensedAscent
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicensedAscentTransport
open OperatorKO7 Trace

/-- The six compiled Gödel stages, none stipulated as `True`. -/
def godelCompiledAscentProfile : AscentProfile where
  shape := {
    hasBaseSystem := ∃ φ : Formula, Provable φ
    hasSelfObstruction := ¬ (evalForm env0 falsum ↔ ¬ Provable falsum)
    blockedInBase := ¬ Provable ConQ
    hasStrongerFramework := ModelsQ ModelInf
    resolvedInFramework := ¬ evalFormIn ModelInf env0Inf ConQ
    licensedReimport := ¬ Provable (Formula.not ConQ)
  }
  family := AscentFamily.reflection

theorem godelCompiledAscentProfile_realizes :
    RealizesSixStepShape godelCompiledAscentProfile.shape :=
  ⟨⟨Formula.eq Term.zero Term.zero, eq_refl_is_provable⟩,
    falsum_not_a_godel_sentence,
    godel_second_incompleteness_Q_unconditional,
    modelInf_qAxioms,
    modelInf_not_conQ,
    not_provable_not_conQ_unconditional⟩

theorem godelCompiledAscentProfile_compatible :
    CompatibleWithDp godelCompiledAscentProfile :=
  (OperatorKO7.Meta.SafeStep.AscentProfileDegeneracy.compatibleWithDp_iff_realizes
    godelCompiledAscentProfile).2 ⟨godelCompiledAscentProfile_realizes, rfl⟩

/-- Issue cell: a compiled Q-theorem. -/
def godelIssue : Formula := Formula.eq Term.zero Term.zero

theorem godelIssue_ne_ConQ : godelIssue ≠ ConQ := by
  intro h
  simp [godelIssue, ConQ] at h

/-- One-step packaging: the theorem steps to `ConQ`. Not a checker derivation. -/
def godelCheckerStep : Formula → Formula → Prop :=
  fun φ ψ => φ = godelIssue ∧ ψ = ConQ

def godelCheckerExpiry : ExpiryObject where
  Carrier := Formula
  dynamics := godelCheckerStep
  license := Provable
  issue := godelIssue
  consume := ConQ
  crossing := ⟨rfl, rfl⟩
  issue_licensed := eq_refl_is_provable
  consume_unlicensed := godel_second_incompleteness_Q_unconditional

def godelCheckerAscent : LicensedAscentObject where
  toExpiryObject := godelCheckerExpiry
  obstruction := ConQ
  obstruction_unlicensed := godel_second_incompleteness_Q_unconditional
  repaired := godelCheckerStep
  repaired_sub := fun h => h
  repaired_licensed := fun h => by
    have hx : _ = godelIssue := h.1
    simpa [hx] using eq_refl_is_provable
  repair_witness := ⟨godelIssue, ConQ, rfl, rfl⟩

theorem godelCheckerAscent_realizes :
    RealizesSixStepShape (toAscentProfile godelCheckerAscent).shape :=
  toAscentProfile_realizes godelCheckerAscent

/-- Corner map: `ConQ` to the quote value, every other formula to the peak source. -/
def godelToQuoteFun (φ : Formula) : QuoteEvalCfg :=
  if φ = ConQ then QuoteEvalCfg.value Trace.void else freezePeakSource

theorem godelToQuoteFun_issue :
    godelToQuoteFun godelIssue = freezePeakSource := by
  simp [godelToQuoteFun, godelIssue_ne_ConQ]

theorem godelToQuoteFun_consume :
    godelToQuoteFun ConQ = QuoteEvalCfg.value Trace.void := by
  simp [godelToQuoteFun]

/-- The packaging object transports to quotation ascent by the corner map. -/
def godelToQuotation : AscentHom godelCheckerAscent quotationAscent where
  toFun := godelToQuoteFun
  issue_map := godelToQuoteFun_issue
  consume_map := godelToQuoteFun_consume
  dynamics_preserve := by
    intro x y h
    have hx : x = godelIssue := h.1
    have hy : y = ConQ := h.2
    subst hx
    subst hy
    simpa [godelToQuoteFun_issue, godelToQuoteFun_consume] using
      freeze_peak_eval_converge
  license_preserve := by
    intro x hx
    have hxne : x ≠ ConQ := by
      intro h
      subst h
      exact godel_second_incompleteness_Q_unconditional hx
    simp [godelToQuoteFun, hxne]
    exact quotationAscent.issue_licensed
  obstruction_map := godelToQuoteFun_consume
  repaired_preserve := by
    intro x y h
    have hx : x = godelIssue := h.1
    have hy : y = ConQ := h.2
    subst hx
    subst hy
    refine ⟨?_, quotationAscent.issue_licensed⟩
    simpa [godelToQuoteFun_issue, godelToQuoteFun_consume] using
      freeze_peak_eval_converge

theorem godel_transports_to_quotation :
    Nonempty (AscentHom godelCheckerAscent quotationAscent) :=
  ⟨godelToQuotation⟩

end OperatorKO7.Meta.GodelSideAscentProfile
