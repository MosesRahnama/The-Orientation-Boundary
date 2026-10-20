import OperatorKO7.Meta.SafeStep_Ctx
import OperatorKO7.Meta.SafeStepCtx_Confluence
import OperatorKO7.Meta.ContextClosed_SN
import OperatorKO7.Meta.EqGuardedConfluence
import OperatorKO7.Meta.DistinctionBoundary.DeltaThawBoundary
import Mathlib.Logic.Relation

set_option autoImplicit false

/-!
# Contextual SafeStep with delta congruence

`SafeStepCtx` has no `delta` constructor. The official expanded relation is
`CtxOn Sdelta SafeStep`, the constructor-selective closure that enables every
head except `eqW`. That is exactly `safeStepDeltaCongruenceConfluent`.

This file does not edit `SafeStep`. It proves the missing delta step, strong
normalization by subrelation, local join, and Newman confluence.
-/

open OperatorKO7 Trace
open MetaSN_DM
open MetaSN_KO7
open OperatorKO7.EqGuardedConfluence
open OperatorKO7.Meta.DistinctionBoundary.FreezeSetForced
open OperatorKO7.Meta.DistinctionBoundary.DeltaThawBoundary

namespace OperatorKO7.Meta.DistinctionBoundary.SafeStepDeltaConfluence

/-- Enable every constructor congruence except `eqW`. This thaws `delta`. -/
def Sdelta : Ctor → Prop :=
  fun c => c ≠ Ctor.eqW

theorem Sdelta_not_eqW : ¬ Sdelta Ctor.eqW :=
  fun h => h rfl

theorem Sdelta_delta : Sdelta Ctor.delta :=
  fun h => Ctor.noConfusion h

theorem Sdelta_integrate : Sdelta Ctor.integrate :=
  fun h => Ctor.noConfusion h

theorem Sdelta_merge : Sdelta Ctor.merge :=
  fun h => Ctor.noConfusion h

theorem Sdelta_app : Sdelta Ctor.app :=
  fun h => Ctor.noConfusion h

theorem Sdelta_recD : Sdelta Ctor.recD :=
  fun h => Ctor.noConfusion h

theorem Sdelta_align : Sdelta Ctor.recD → Sdelta Ctor.app :=
  fun _ h => Ctor.noConfusion h

abbrev SafeDelta : Trace → Trace → Prop :=
  CtxOn Sdelta SafeStep

abbrev SafeDeltaStar : Trace → Trace → Prop :=
  CtxStarOn Sdelta SafeStep

theorem ctxOn_safe_sub_eqGuarded :
    ∀ {a b : Trace}, CtxOn Sdelta SafeStep a b → CtxOn Sdelta EqGuardedStep a b
  | _, _, .root h => .root (safeStep_sub_eqGuarded h)
  | _, _, .delta e h => .delta e (ctxOn_safe_sub_eqGuarded h)
  | _, _, .integrate e h => .integrate e (ctxOn_safe_sub_eqGuarded h)
  | _, _, .mergeL e h => .mergeL e (ctxOn_safe_sub_eqGuarded h)
  | _, _, .mergeR e h => .mergeR e (ctxOn_safe_sub_eqGuarded h)
  | _, _, .appL e h => .appL e (ctxOn_safe_sub_eqGuarded h)
  | _, _, .appR e h => .appR e (ctxOn_safe_sub_eqGuarded h)
  | _, _, .recB e h => .recB e (ctxOn_safe_sub_eqGuarded h)
  | _, _, .recS e h => .recS e (ctxOn_safe_sub_eqGuarded h)
  | _, _, .recN e h => .recN e (ctxOn_safe_sub_eqGuarded h)
  | _, _, .eqWL e h => .eqWL e (ctxOn_safe_sub_eqGuarded h)
  | _, _, .eqWR e h => .eqWR e (ctxOn_safe_sub_eqGuarded h)

theorem wf_safeDeltaRev : WellFounded (fun a b : Trace => SafeDelta b a) := by
  have hsub : Subrelation (fun a b : Trace => SafeDelta b a)
      (CtxOnRev Sdelta EqGuardedStep) := by
    intro a b h
    exact ctxOn_safe_sub_eqGuarded h
  exact Subrelation.wf hsub (wf_ctxOn_eqGuarded_rev Sdelta)

theorem not_safeStep_of_delta (t u : Trace) : ¬ SafeStep (delta t) u := by
  intro h
  cases h

theorem not_safeStepCtx_delta_merge :
    ¬ SafeStepCtx (delta (merge void void)) (delta void) := by
  intro h
  cases h with
  | root hroot => exact not_safeStep_of_delta _ _ hroot

/-- The missing congruence step, now present in `CtxOn Sdelta SafeStep`. -/
theorem delta_congruence_merge_void :
    SafeDelta (delta (merge void void)) (delta void) :=
  CtxOn.delta Sdelta_delta
    (CtxOn.root (SafeStep.R_merge_void_left void deltaFlag_void))

theorem expanded_strictly_extends_ctx :
    SafeDelta (delta (merge void void)) (delta void) ∧
      ¬ SafeStepCtx (delta (merge void void)) (delta void) :=
  ⟨delta_congruence_merge_void, not_safeStepCtx_delta_merge⟩

theorem named_prop_is_confluentOn_safe :
    safeStepDeltaCongruenceConfluent = ConfluentOn Sdelta SafeStep :=
  rfl

theorem safeStep_unique_target {a b c : Trace}
    (hb : SafeStep a b) (hc : SafeStep a c) : b = c :=
  eqGuarded_unique_target (safeStep_sub_eqGuarded hb) (safeStep_sub_eqGuarded hc)

theorem safeStep_target_deltaFlag_zero {a b : Trace} (h : SafeStep a b) :
    deltaFlag b = 0 := by
  cases h with
  | R_int_delta t => rfl
  | R_merge_void_left t hδ => exact hδ
  | R_merge_void_right t hδ => exact hδ
  | R_merge_cancel t hδ _ => exact hδ
  | R_rec_zero b s hδ => exact hδ
  | R_rec_succ b s n => rfl
  | R_eq_refl a _ => rfl
  | R_eq_diff a b _ => rfl

theorem no_safeDelta_from_void {u : Trace} : ¬ SafeDelta void u := by
  intro h
  cases h with
  | root hs => cases hs

theorem kappaM_rec_ne_zero (b s n : Trace) : kappaM (recΔ b s n) ≠ 0 := by
  simp [kappaM]

theorem kappaM_union_eq_zero {x y : Trace}
    (h : kappaM x ∪ kappaM y = 0) : kappaM x = 0 ∧ kappaM y = 0 := by
  constructor
  · ext n
    have hn : max (Multiset.count n (kappaM x)) (Multiset.count n (kappaM y)) = 0 := by
      simpa [Multiset.count_union] using congrArg (fun m => Multiset.count n m) h
    exact (Nat.max_eq_zero_iff.mp hn).1
  · ext n
    have hn : max (Multiset.count n (kappaM x)) (Multiset.count n (kappaM y)) = 0 := by
      simpa [Multiset.count_union] using congrArg (fun m => Multiset.count n m) h
    exact (Nat.max_eq_zero_iff.mp hn).2

theorem kappaM_zero_of_safeStep {a b : Trace} (h : SafeStep a b)
    (h0 : kappaM a = 0) : kappaM b = 0 := by
  cases h with
  | R_int_delta t => rfl
  | R_merge_void_left t _ =>
      simpa [kappaM] using h0
  | R_merge_void_right t _ =>
      simpa [kappaM] using h0
  | R_merge_cancel t _ _ =>
      exact (kappaM_union_eq_zero (by simpa [kappaM] using h0)).1
  | R_rec_zero b s _ =>
      exact (kappaM_rec_ne_zero b s void h0).elim
  | R_rec_succ b s n =>
      exact (kappaM_rec_ne_zero b s (delta n) h0).elim
  | R_eq_refl a _ => rfl
  | R_eq_diff a b _ =>
      simpa [kappaM] using h0

theorem kappaM_zero_of_safeDelta {a b : Trace} (h : SafeDelta a b)
    (h0 : kappaM a = 0) : kappaM b = 0 := by
  induction h with
  | root hs => exact kappaM_zero_of_safeStep hs h0
  | delta _ _ ih =>
      exact ih (by simpa [kappaM] using h0)
  | integrate _ _ ih =>
      exact ih (by simpa [kappaM] using h0)
  | mergeL _ h₁ ih =>
      have hx : kappaM _ = 0 ∧ kappaM _ = 0 :=
        kappaM_union_eq_zero (by simpa [kappaM] using h0)
      simpa [kappaM, hx.2] using ih hx.1
  | mergeR _ h₁ ih =>
      have hx : kappaM _ = 0 ∧ kappaM _ = 0 :=
        kappaM_union_eq_zero (by simpa [kappaM] using h0)
      simpa [kappaM, hx.1] using ih hx.2
  | appL _ h₁ ih =>
      have hx : kappaM _ = 0 ∧ kappaM _ = 0 :=
        kappaM_union_eq_zero (by simpa [kappaM] using h0)
      simpa [kappaM, hx.2] using ih hx.1
  | appR _ h₁ ih =>
      have hx : kappaM _ = 0 ∧ kappaM _ = 0 :=
        kappaM_union_eq_zero (by simpa [kappaM] using h0)
      simpa [kappaM, hx.1] using ih hx.2
  | recB _ _ _ =>
      exact (kappaM_rec_ne_zero _ _ _ h0).elim
  | recS _ _ _ =>
      exact (kappaM_rec_ne_zero _ _ _ h0).elim
  | recN _ _ _ =>
      exact (kappaM_rec_ne_zero _ _ _ h0).elim
  | eqWL e _ _ => exact absurd e Sdelta_not_eqW
  | eqWR e _ _ => exact absurd e Sdelta_not_eqW

theorem deltaFlag_eq_zero_of_kappaM_zero {t : Trace} (h : kappaM t = 0) :
    deltaFlag t = 0 := by
  cases t with
  | recΔ b s n => exact (kappaM_rec_ne_zero b s n h).elim
  | void => rfl
  | delta t => rfl
  | integrate t => rfl
  | merge a b => rfl
  | app a b => rfl
  | eqW a b => rfl

theorem exists_of_deltaFlag_one {t : Trace} (h : deltaFlag t = 1) :
    ∃ b s n, t = recΔ b s (delta n) := by
  cases t with
  | recΔ b s n =>
      cases n with
      | delta n => exact ⟨b, s, n, rfl⟩
      | void => simp [deltaFlag] at h
      | integrate n => simp [deltaFlag] at h
      | merge a b' => simp [deltaFlag] at h
      | app a b' => simp [deltaFlag] at h
      | recΔ b' s' n' => simp [deltaFlag] at h
      | eqW a b' => simp [deltaFlag] at h
  | void => simp [deltaFlag] at h
  | delta t => simp [deltaFlag] at h
  | integrate t => simp [deltaFlag] at h
  | merge a b => simp [deltaFlag] at h
  | app a b => simp [deltaFlag] at h
  | eqW a b => simp [deltaFlag] at h

/-- Join a `R_rec_zero` root against a congruence step of the base. -/
theorem recZero_base_joins {b b' s : Trace} (hδ : deltaFlag b = 0)
    (h : SafeDelta b b') :
    ∃ d, SafeDeltaStar b d ∧ SafeDeltaStar (recΔ b' s void) d := by
  cases h with
  | root hr =>
      have hδ' : deltaFlag b' = 0 := safeStep_target_deltaFlag_zero hr
      exact ⟨b', Relation.ReflTransGen.single (CtxOn.root hr),
        Relation.ReflTransGen.single
          (CtxOn.root (SafeStep.R_rec_zero _ _ hδ'))⟩
  | @delta t u enabled h₁ =>
      have hδ' : deltaFlag (delta u) = 0 := rfl
      exact ⟨delta u, Relation.ReflTransGen.single (CtxOn.delta Sdelta_delta h₁),
        Relation.ReflTransGen.single
          (CtxOn.root (SafeStep.R_rec_zero (delta u) s hδ'))⟩
  | @integrate t u enabled h₁ =>
      have hδ' : deltaFlag (integrate u) = 0 := rfl
      exact ⟨integrate u,
        Relation.ReflTransGen.single (CtxOn.integrate Sdelta_integrate h₁),
        Relation.ReflTransGen.single
          (CtxOn.root (SafeStep.R_rec_zero (integrate u) s hδ'))⟩
  | @mergeL a a' b enabled h₁ =>
      have hδ' : deltaFlag (merge a' b) = 0 := rfl
      exact ⟨merge a' b,
        Relation.ReflTransGen.single (CtxOn.mergeL Sdelta_merge h₁),
        Relation.ReflTransGen.single
          (CtxOn.root (SafeStep.R_rec_zero (merge a' b) s hδ'))⟩
  | @mergeR a b b' enabled h₁ =>
      have hδ' : deltaFlag (merge a b') = 0 := rfl
      exact ⟨merge a b',
        Relation.ReflTransGen.single (CtxOn.mergeR Sdelta_merge h₁),
        Relation.ReflTransGen.single
          (CtxOn.root (SafeStep.R_rec_zero (merge a b') s hδ'))⟩
  | @appL a a' b enabled h₁ =>
      have hδ' : deltaFlag (app a' b) = 0 := rfl
      exact ⟨app a' b,
        Relation.ReflTransGen.single (CtxOn.appL Sdelta_app h₁),
        Relation.ReflTransGen.single
          (CtxOn.root (SafeStep.R_rec_zero (app a' b) s hδ'))⟩
  | @appR a b b' enabled h₁ =>
      have hδ' : deltaFlag (app a b') = 0 := rfl
      exact ⟨app a b',
        Relation.ReflTransGen.single (CtxOn.appR Sdelta_app h₁),
        Relation.ReflTransGen.single
          (CtxOn.root (SafeStep.R_rec_zero (app a b') s hδ'))⟩
  | @recB bb bb' st nn enabled h₁ =>
      have hδ' : deltaFlag (recΔ bb' st nn) = 0 := by
        cases nn <;> simp [deltaFlag] at hδ ⊢
      exact ⟨recΔ bb' st nn,
        Relation.ReflTransGen.single (CtxOn.recB Sdelta_recD h₁),
        Relation.ReflTransGen.single
          (CtxOn.root (SafeStep.R_rec_zero (recΔ bb' st nn) s hδ'))⟩
  | @recS bb st st' nn enabled h₁ =>
      have hδ' : deltaFlag (recΔ bb st' nn) = 0 := by
        cases nn <;> simp [deltaFlag] at hδ ⊢
      exact ⟨recΔ bb st' nn,
        Relation.ReflTransGen.single (CtxOn.recS Sdelta_recD h₁),
        Relation.ReflTransGen.single
          (CtxOn.root (SafeStep.R_rec_zero (recΔ bb st' nn) s hδ'))⟩
  | @recN bb st nn nn' enabled h₁ =>
      by_cases hflag : deltaFlag (recΔ bb st nn') = 0
      · exact ⟨recΔ bb st nn',
          Relation.ReflTransGen.single (CtxOn.recN Sdelta_recD h₁),
          Relation.ReflTransGen.single
            (CtxOn.root (SafeStep.R_rec_zero (recΔ bb st nn') s hflag))⟩
      · have h1 : deltaFlag (recΔ bb st nn') = 1 := by
          rcases deltaFlag_range (recΔ bb st nn') with h0 | h1
          · exact (hflag h0).elim
          · exact h1
        obtain ⟨xb, sb, zb, hshape⟩ := exists_of_deltaFlag_one h1
        injection hshape with hbb hst hnn
        subst hbb; subst hst; subst hnn
        refine ⟨app st (recΔ bb st zb), ?left, ?right⟩
        · exact (Relation.ReflTransGen.single
              (CtxOn.recN Sdelta_recD h₁)).tail
            (CtxOn.root (SafeStep.R_rec_succ bb st zb))
        · exact (Relation.ReflTransGen.single
              (CtxOn.recB Sdelta_recD
                (CtxOn.root (SafeStep.R_rec_succ bb st zb)))).tail
            (CtxOn.root (SafeStep.R_rec_zero (app st (recΔ bb st zb)) s
              (by simp [deltaFlag])))
  | eqWL e _ => exact absurd e Sdelta_not_eqW
  | eqWR e _ => exact absurd e Sdelta_not_eqW

theorem mergeVoidRight_joins {t t' : Trace} (_hδ : deltaFlag t = 0)
    (h : SafeDelta t t') :
    ∃ d, SafeDeltaStar t d ∧ SafeDeltaStar (merge t' void) d := by
  by_cases hflag : deltaFlag t' = 0
  · exact ⟨t', Relation.ReflTransGen.single h,
      Relation.ReflTransGen.single
        (CtxOn.root (SafeStep.R_merge_void_right t' hflag))⟩
  · have h1 : deltaFlag t' = 1 := by
      rcases deltaFlag_range t' with h0 | h1
      · exact (hflag h0).elim
      · exact h1
    obtain ⟨xb, sb, zb, rfl⟩ := exists_of_deltaFlag_one h1
    refine ⟨app sb (recΔ xb sb zb), ?_, ?_⟩
    · exact (Relation.ReflTransGen.single h).tail
        (CtxOn.root (SafeStep.R_rec_succ xb sb zb))
    · exact (Relation.ReflTransGen.single
          (CtxOn.mergeL Sdelta_merge
            (CtxOn.root (SafeStep.R_rec_succ xb sb zb)))).tail
        (CtxOn.root (SafeStep.R_merge_void_right _ (by simp [deltaFlag])))

theorem mergeVoidLeft_joins {t t' : Trace} (_hδ : deltaFlag t = 0)
    (h : SafeDelta t t') :
    ∃ d, SafeDeltaStar t d ∧ SafeDeltaStar (merge void t') d := by
  by_cases hflag : deltaFlag t' = 0
  · exact ⟨t', Relation.ReflTransGen.single h,
      Relation.ReflTransGen.single
        (CtxOn.root (SafeStep.R_merge_void_left t' hflag))⟩
  · have h1 : deltaFlag t' = 1 := by
      rcases deltaFlag_range t' with h0 | h1
      · exact (hflag h0).elim
      · exact h1
    obtain ⟨xb, sb, zb, rfl⟩ := exists_of_deltaFlag_one h1
    refine ⟨app sb (recΔ xb sb zb), ?_, ?_⟩
    · exact (Relation.ReflTransGen.single h).tail
        (CtxOn.root (SafeStep.R_rec_succ xb sb zb))
    · exact (Relation.ReflTransGen.single
          (CtxOn.mergeR Sdelta_merge
            (CtxOn.root (SafeStep.R_rec_succ xb sb zb)))).tail
        (CtxOn.root (SafeStep.R_merge_void_left _ (by simp [deltaFlag])))

/-- Root-versus-arbitrary local peaks of `SafeDelta`. -/
theorem safeDelta_root_peak_joins {a b c : Trace}
    (hr : SafeStep a b) (hac : SafeDelta a c) :
    ∃ d, SafeDeltaStar b d ∧ SafeDeltaStar c d := by
  cases hac with
  | root hr' =>
      obtain rfl := safeStep_unique_target hr hr'
      exact ⟨b, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | delta enabled h' =>
      cases hr
  | integrate enabled h' =>
      cases hr with
      | R_int_delta t =>
          cases h' with
          | root hs => cases hs
          | delta _ h'' =>
              exact ⟨void, Relation.ReflTransGen.refl,
                Relation.ReflTransGen.single
                  (CtxOn.root (SafeStep.R_int_delta _))⟩
  | @mergeL a a' b enabled h' =>
      cases hr with
      | R_merge_void_left t hδ => exact absurd h' no_safeDelta_from_void
      | R_merge_void_right t hδ =>
          exact mergeVoidRight_joins hδ h'
      | R_merge_cancel t hδ h0 =>
          have h0' : kappaM a' = 0 := kappaM_zero_of_safeDelta h' h0
          have hδ' : deltaFlag a' = 0 := deltaFlag_eq_zero_of_kappaM_zero h0'
          refine ⟨a', Relation.ReflTransGen.single h', ?_⟩
          exact (Relation.ReflTransGen.single
              (CtxOn.mergeR Sdelta_merge h')).tail
            (CtxOn.root (SafeStep.R_merge_cancel a' hδ' h0'))
  | @mergeR a b b' enabled h' =>
      cases hr with
      | R_merge_void_left t hδ =>
          exact mergeVoidLeft_joins hδ h'
      | R_merge_void_right t hδ => exact absurd h' no_safeDelta_from_void
      | R_merge_cancel t hδ h0 =>
          have h0' : kappaM b' = 0 := kappaM_zero_of_safeDelta h' h0
          have hδ' : deltaFlag b' = 0 := deltaFlag_eq_zero_of_kappaM_zero h0'
          refine ⟨b', Relation.ReflTransGen.single h', ?_⟩
          exact (Relation.ReflTransGen.single
              (CtxOn.mergeL Sdelta_merge h')).tail
            (CtxOn.root (SafeStep.R_merge_cancel b' hδ' h0'))
  | appL enabled h' => cases hr
  | appR enabled h' => cases hr
  | recB enabled h' =>
      cases hr with
      | R_rec_zero b s hδ =>
          exact recZero_base_joins hδ h'
      | R_rec_succ b s n =>
          exact ⟨_,
            Relation.ReflTransGen.single
              (CtxOn.appR Sdelta_app (CtxOn.recB Sdelta_recD h')),
            Relation.ReflTransGen.single
              (CtxOn.root (SafeStep.R_rec_succ _ _ _))⟩
  | recS enabled h' =>
      cases hr with
      | R_rec_zero b s hδ =>
          exact ⟨b, Relation.ReflTransGen.refl,
            Relation.ReflTransGen.single
              (CtxOn.root (SafeStep.R_rec_zero _ _ hδ))⟩
      | R_rec_succ b s n =>
          exact ⟨_,
            (Relation.ReflTransGen.single
              (CtxOn.appL Sdelta_app h')).tail
              (CtxOn.appR Sdelta_app (CtxOn.recS Sdelta_recD h')),
            Relation.ReflTransGen.single
              (CtxOn.root (SafeStep.R_rec_succ _ _ _))⟩
  | recN enabled h' =>
      cases hr with
      | R_rec_zero b s hδ => exact absurd h' no_safeDelta_from_void
      | R_rec_succ b s n =>
          cases h' with
          | root hs => cases hs
          | delta _ h'' =>
              exact ⟨_,
                Relation.ReflTransGen.single
                  (CtxOn.appR Sdelta_app (CtxOn.recN Sdelta_recD h'')),
                Relation.ReflTransGen.single
                  (CtxOn.root (SafeStep.R_rec_succ _ _ _))⟩
  | eqWL enabled h' => exact absurd enabled Sdelta_not_eqW
  | eqWR enabled h' => exact absurd enabled Sdelta_not_eqW

theorem safeDelta_local_join :
    ∀ {a b : Trace}, SafeDelta a b →
      ∀ c : Trace, SafeDelta a c →
        ∃ d, SafeDeltaStar b d ∧ SafeDeltaStar c d := by
  intro a b hab
  induction hab with
  | root hr =>
      intro c hac
      exact safeDelta_root_peak_joins hr hac
  | delta enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr => cases hr
      | delta enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarOn_delta enabled hd₁, ctxStarOn_delta enabled hd₂⟩
  | integrate enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr =>
          obtain ⟨d, hd₁, hd₂⟩ := safeDelta_root_peak_joins hr (CtxOn.integrate enabled h₁)
          exact ⟨d, hd₂, hd₁⟩
      | integrate enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarOn_integrate enabled hd₁, ctxStarOn_integrate enabled hd₂⟩
  | mergeL enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr =>
          obtain ⟨d, hd₁, hd₂⟩ := safeDelta_root_peak_joins hr (CtxOn.mergeL enabled h₁)
          exact ⟨d, hd₂, hd₁⟩
      | mergeL enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarOn_mergeL enabled hd₁, ctxStarOn_mergeL enabled hd₂⟩
      | mergeR enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOn.mergeR enabled h₂),
            Relation.ReflTransGen.single (CtxOn.mergeL enabled h₁)⟩
  | mergeR enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr =>
          obtain ⟨d, hd₁, hd₂⟩ := safeDelta_root_peak_joins hr (CtxOn.mergeR enabled h₁)
          exact ⟨d, hd₂, hd₁⟩
      | mergeL enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOn.mergeL enabled h₂),
            Relation.ReflTransGen.single (CtxOn.mergeR enabled h₁)⟩
      | mergeR enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarOn_mergeR enabled hd₁, ctxStarOn_mergeR enabled hd₂⟩
  | appL enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr => cases hr
      | appL enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarOn_appL enabled hd₁, ctxStarOn_appL enabled hd₂⟩
      | appR enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOn.appR enabled h₂),
            Relation.ReflTransGen.single (CtxOn.appL enabled h₁)⟩
  | appR enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr => cases hr
      | appL enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOn.appL enabled h₂),
            Relation.ReflTransGen.single (CtxOn.appR enabled h₁)⟩
      | appR enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarOn_appR enabled hd₁, ctxStarOn_appR enabled hd₂⟩
  | recB enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr =>
          obtain ⟨d, hd₁, hd₂⟩ := safeDelta_root_peak_joins hr (CtxOn.recB enabled h₁)
          exact ⟨d, hd₂, hd₁⟩
      | recB enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarOn_recB enabled hd₁, ctxStarOn_recB enabled hd₂⟩
      | recS enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOn.recS enabled h₂),
            Relation.ReflTransGen.single (CtxOn.recB enabled h₁)⟩
      | recN enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOn.recN enabled h₂),
            Relation.ReflTransGen.single (CtxOn.recB enabled h₁)⟩
  | recS enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr =>
          obtain ⟨d, hd₁, hd₂⟩ := safeDelta_root_peak_joins hr (CtxOn.recS enabled h₁)
          exact ⟨d, hd₂, hd₁⟩
      | recB enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOn.recB enabled h₂),
            Relation.ReflTransGen.single (CtxOn.recS enabled h₁)⟩
      | recS enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarOn_recS enabled hd₁, ctxStarOn_recS enabled hd₂⟩
      | recN enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOn.recN enabled h₂),
            Relation.ReflTransGen.single (CtxOn.recS enabled h₁)⟩
  | recN enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr =>
          obtain ⟨d, hd₁, hd₂⟩ := safeDelta_root_peak_joins hr (CtxOn.recN enabled h₁)
          exact ⟨d, hd₂, hd₁⟩
      | recB enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOn.recB enabled h₂),
            Relation.ReflTransGen.single (CtxOn.recN enabled h₁)⟩
      | recS enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOn.recS enabled h₂),
            Relation.ReflTransGen.single (CtxOn.recN enabled h₁)⟩
      | recN enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarOn_recN enabled hd₁, ctxStarOn_recN enabled hd₂⟩
  | eqWL enabled h₁ ih => exact absurd enabled Sdelta_not_eqW
  | eqWR enabled h₁ ih => exact absurd enabled Sdelta_not_eqW

private theorem safeDelta_join_star_star :
    ∀ x : Trace, Acc (fun a b : Trace => SafeDelta b a) x →
      ∀ {y z : Trace}, SafeDeltaStar x y → SafeDeltaStar x z →
        ∃ d, SafeDeltaStar y d ∧ SafeDeltaStar z d := by
  intro x hx
  induction hx with
  | intro x _ ih =>
      intro y z hxy hxz
      rcases Relation.ReflTransGen.cases_head hxy with rfl | ⟨b₁, hxb₁, hb₁y⟩
      · exact ⟨z, hxz, Relation.ReflTransGen.refl⟩
      · rcases Relation.ReflTransGen.cases_head hxz with rfl | ⟨c₁, hxc₁, hc₁z⟩
        · exact ⟨y, Relation.ReflTransGen.refl,
            Relation.ReflTransGen.head hxb₁ hb₁y⟩
        · obtain ⟨e, hb₁e, hc₁e⟩ := safeDelta_local_join hxb₁ _ hxc₁
          obtain ⟨d₁, hed₁, hzd₁⟩ := ih c₁ hxc₁ hc₁e hc₁z
          obtain ⟨d, hyd, hd₁d⟩ := ih b₁ hxb₁ hb₁y (hb₁e.trans hed₁)
          exact ⟨d, hyd, hzd₁.trans hd₁d⟩

/-- Newman confluence of contextual `SafeStep` with delta congruence. -/
theorem confluent_safeDelta : ConfluentOn Sdelta SafeStep := by
  intro a b c hab hac
  exact safeDelta_join_star_star a (wf_safeDeltaRev.apply a) hab hac

/-- The named remaining conjecture is now a theorem. -/
theorem safeStepDeltaCongruenceConfluent_holds :
    safeStepDeltaCongruenceConfluent :=
  confluent_safeDelta

theorem safeStepCtx_already_confluent : ConfluentSafeCtx :=
  confluentSafeCtx

end OperatorKO7.Meta.DistinctionBoundary.SafeStepDeltaConfluence
