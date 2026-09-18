import OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope
import OperatorKO7.Meta.Rewriting.CriticalPairLemma

/-! # Nonconfluence and distinct normal forms of the full contextual relation -/

namespace MetaSN_KO7

open OperatorKO7 Trace
open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope

theorem stepCtxFull_not_locally_confluent : ¬ AbsLocalConfluent StepCtxFull := by
  intro h
  exact eqW_void_void_ctx_not_joinable
    (h (eqW void void) void (integrate (merge void void))
      (StepCtxFull.root (Step.R_eq_refl void))
      (StepCtxFull.root (Step.R_eq_diff void void)))

theorem stepCtxFull_not_confluent : ¬ AbsConfluent StepCtxFull := by
  intro h
  apply stepCtxFull_not_locally_confluent
  intro a b c hab hac
  exact h a b c (Relation.ReflTransGen.single hab) (Relation.ReflTransGen.single hac)

theorem integrate_void_ctx_normal {t : Trace} : ¬ StepCtxFull (integrate void) t := by
  intro h
  cases h with
  | root h => cases h
  | integrate h => exact void_normal h

/-- The same source has two distinct contextual normal forms. -/
theorem stepCtxFull_two_normal_forms :
    CtxStar (eqW void void) void ∧
    CtxStar (eqW void void) (integrate void) ∧
    (∀ t, ¬ StepCtxFull void t) ∧
    (∀ t, ¬ StepCtxFull (integrate void) t) ∧
    void ≠ integrate void := by
  refine ⟨Relation.ReflTransGen.single (StepCtxFull.root (Step.R_eq_refl void)),
    ?_, fun _ => void_normal, fun _ => integrate_void_ctx_normal, by decide⟩
  exact Relation.ReflTransGen.head (StepCtxFull.root (Step.R_eq_diff void void))
    (Relation.ReflTransGen.single
      (StepCtxFull.integrate (StepCtxFull.root (Step.R_merge_cancel void))))

/-- A function cannot both identify every contextual step and fix every normal form. -/
theorem stepCtxFull_no_invariant_normalizer :
    ¬ ∃ nf : Trace → Trace,
      (∀ {a b}, StepCtxFull a b → nf a = nf b) ∧
      (∀ a, (∀ b, ¬ StepCtxFull a b) → nf a = a) := by
  rintro ⟨nf, hinv, hfix⟩
  have hstar : ∀ {a b}, CtxStar a b → nf a = nf b := by
    intro a b h
    induction h with
    | refl => rfl
    | tail _ hs ih => exact ih.trans (hinv hs)
  obtain ⟨hv, hi, hnv, hni, hne⟩ := stepCtxFull_two_normal_forms
  exact hne (by simpa [hfix void hnv, hfix (integrate void) hni]
    using (hstar hv).symm.trans (hstar hi))

end MetaSN_KO7
