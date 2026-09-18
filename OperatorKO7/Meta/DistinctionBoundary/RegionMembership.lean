/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Kernel
import OperatorKO7.Meta.DistinctionBoundary.ContextualClassification
import OperatorKO7.Meta.SafeStep_Complexity

/-!
# Executable region membership (Roadmap 09, Weld 3, W3-A)

`ctxReducts` is the certified one-step enumerator for `StepCtxFull`: root
reducts by rule pattern match, plus congruence recursion. Soundness and
completeness against the inductive relation are both proved (K21 live-relation
iff). Bounded search `reachesDeltaHeadFuel` decides delta-head reachability
with unconditional soundness. Completeness is typed under an explicit fuel
hypothesis (`StepCtxFullPow` length); that bound transports from the
polynomial witness `W` already proved for `StepCtxFull` (not merely
`SafeStepCtx`), so completeness is upgraded to fuel `W a`.

The classifier join/nonjoin verdict on the fueled region is the composition
of this Bool with `diagonal_ctx_joins_iff_reaches_delta`.

Relation: `StepCtxFull`. Closure: `CtxStar` / `StepCtxFullPow`.
Trust: kernel only, Mathlib baseline. No `native_decide`.
-/

set_option autoImplicit false

open OperatorKO7 Trace
open MetaSN_KO7
open OperatorKO7.PolyInterpretation
open OperatorKO7.Meta.DistinctionBoundary.ContextualClassification
open OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope

namespace OperatorKO7.Meta.DistinctionBoundary.RegionMembership

/-! ## Root enumerator (unguarded `Step`) -/

/-- Executable one-step *root* reducts of the unguarded kernel `Step`. -/
def rootReducts : Trace → List Trace
  | integrate (delta _) => [void]
  | merge a b =>
      (if a = void then [b] else []) ++
      (if b = void then [a] else []) ++
      (if a = b then [a] else [])
  | recΔ b _s void => [b]
  | recΔ b s (delta n) => [app s (recΔ b s n)]
  | eqW a b =>
      (if a = b then [void] else []) ++ [integrate (merge a b)]
  | _ => []

private theorem mem_of_if_singleton {α : Type} [DecidableEq α] {p : Prop}
    [Decidable p] {x y : α} (h : x ∈ if p then [y] else []) : p ∧ x = y := by
  by_cases hp : p
  · simp [hp] at h
    exact ⟨hp, h⟩
  · simp [hp] at h

theorem rootReducts_sound {t u : Trace} (h : u ∈ rootReducts t) : Step t u := by
  cases t with
  | void => simp [rootReducts] at h
  | delta _ => simp [rootReducts] at h
  | integrate x =>
      cases x with
      | delta t' =>
          simp [rootReducts] at h
          subst h
          exact Step.R_int_delta t'
      | void => simp [rootReducts] at h
      | integrate _ => simp [rootReducts] at h
      | merge _ _ => simp [rootReducts] at h
      | app _ _ => simp [rootReducts] at h
      | recΔ _ _ _ => simp [rootReducts] at h
      | eqW _ _ => simp [rootReducts] at h
  | merge a b =>
      simp only [rootReducts] at h
      rw [List.mem_append, List.mem_append] at h
      rcases h with (hL | hR) | hC
      · obtain ⟨ha, hu⟩ := mem_of_if_singleton hL
        subst ha
        subst hu
        exact Step.R_merge_void_left u
      · obtain ⟨hb, hu⟩ := mem_of_if_singleton hR
        subst hb
        subst hu
        exact Step.R_merge_void_right u
      · obtain ⟨hab, hu⟩ := mem_of_if_singleton hC
        subst hab
        subst hu
        exact Step.R_merge_cancel u
  | app _ _ => simp [rootReducts] at h
  | recΔ b s n =>
      cases n
      · simp [rootReducts] at h
        subst h
        exact Step.R_rec_zero u s
      · simp [rootReducts] at h
        subst h
        exact Step.R_rec_succ _ s _
      · simp [rootReducts] at h
      · simp [rootReducts] at h
      · simp [rootReducts] at h
      · simp [rootReducts] at h
      · simp [rootReducts] at h
  | eqW a b =>
      simp only [rootReducts] at h
      rw [List.mem_append, List.mem_singleton] at h
      rcases h with hRefl | hDiff
      · obtain ⟨hab, hu⟩ := mem_of_if_singleton hRefl
        subst hab
        subst hu
        exact Step.R_eq_refl a
      · subst hDiff
        exact Step.R_eq_diff a b

theorem rootReducts_complete {t u : Trace} (h : Step t u) : u ∈ rootReducts t := by
  cases h with
  | R_int_delta t' =>
      simp [rootReducts]
  | R_merge_void_left t' =>
      simp [rootReducts]
  | R_merge_void_right t' =>
      simp [rootReducts]
  | R_merge_cancel t' =>
      simp [rootReducts]
  | R_rec_zero b s =>
      simp [rootReducts]
  | R_rec_succ b s n =>
      simp [rootReducts]
  | R_eq_refl a =>
      simp [rootReducts]
  | R_eq_diff a b =>
      simp [rootReducts]

/-! ## Contextual enumerator (`StepCtxFull`) -/

/-- One-step `StepCtxFull` reducts: root rules plus congruence recursion. -/
def ctxReducts : Trace → List Trace
  | void => []
  | delta t => (ctxReducts t).map delta
  | integrate t => rootReducts (integrate t) ++ (ctxReducts t).map integrate
  | merge a b =>
      rootReducts (merge a b) ++
        (ctxReducts a).map (fun a' => merge a' b) ++
        (ctxReducts b).map (fun b' => merge a b')
  | app a b =>
      (ctxReducts a).map (fun a' => app a' b) ++
        (ctxReducts b).map (fun b' => app a b')
  | recΔ b s n =>
      rootReducts (recΔ b s n) ++
        (ctxReducts b).map (fun b' => recΔ b' s n) ++
        (ctxReducts s).map (fun s' => recΔ b s' n) ++
        (ctxReducts n).map (fun n' => recΔ b s n')
  | eqW a b =>
      rootReducts (eqW a b) ++
        (ctxReducts a).map (fun a' => eqW a' b) ++
        (ctxReducts b).map (fun b' => eqW a b')

/-- Soundness: every enumerated reduct is a genuine `StepCtxFull` step. -/
theorem ctxReducts_sound {t u : Trace} (h : u ∈ ctxReducts t) : StepCtxFull t u := by
  induction t generalizing u with
  | void => simp [ctxReducts] at h
  | delta t ih =>
      simp only [ctxReducts] at h
      rw [List.mem_map] at h
      obtain ⟨t', ht', rfl⟩ := h
      exact StepCtxFull.delta (ih ht')
  | integrate t ih =>
      simp only [ctxReducts] at h
      rw [List.mem_append, List.mem_map] at h
      rcases h with hroot | ⟨t', ht', rfl⟩
      · exact StepCtxFull.root (rootReducts_sound hroot)
      · exact StepCtxFull.integrate (ih ht')
  | merge a b iha ihb =>
      simp only [ctxReducts] at h
      rw [List.mem_append, List.mem_append, List.mem_map, List.mem_map] at h
      rcases h with (hroot | ⟨a', ha', rfl⟩) | ⟨b', hb', rfl⟩
      · exact StepCtxFull.root (rootReducts_sound hroot)
      · exact StepCtxFull.mergeL (iha ha')
      · exact StepCtxFull.mergeR (ihb hb')
  | app a b iha ihb =>
      simp only [ctxReducts] at h
      rw [List.mem_append, List.mem_map, List.mem_map] at h
      rcases h with ⟨a', ha', rfl⟩ | ⟨b', hb', rfl⟩
      · exact StepCtxFull.appL (iha ha')
      · exact StepCtxFull.appR (ihb hb')
  | recΔ b s n ihb ihs ihn =>
      simp only [ctxReducts] at h
      rw [List.mem_append, List.mem_append, List.mem_append,
          List.mem_map, List.mem_map, List.mem_map] at h
      rcases h with ((hroot | ⟨b', hb', rfl⟩) | ⟨s', hs', rfl⟩) | ⟨n', hn', rfl⟩
      · exact StepCtxFull.root (rootReducts_sound hroot)
      · exact StepCtxFull.recB (ihb hb')
      · exact StepCtxFull.recS (ihs hs')
      · exact StepCtxFull.recN (ihn hn')
  | eqW a b iha ihb =>
      simp only [ctxReducts] at h
      rw [List.mem_append, List.mem_append, List.mem_map, List.mem_map] at h
      rcases h with (hroot | ⟨a', ha', rfl⟩) | ⟨b', hb', rfl⟩
      · exact StepCtxFull.root (rootReducts_sound hroot)
      · exact StepCtxFull.eqWL (iha ha')
      · exact StepCtxFull.eqWR (ihb hb')

private theorem mem_rootReducts_mem_ctxReducts {t u : Trace}
    (h : u ∈ rootReducts t) : u ∈ ctxReducts t := by
  cases t with
  | void => simp [rootReducts] at h
  | delta _ => simp [rootReducts] at h
  | integrate _ =>
      simp only [ctxReducts]
      exact List.mem_append_left _ h
  | merge _ _ =>
      simp only [ctxReducts]
      exact List.mem_append_left _ (List.mem_append_left _ h)
  | app _ _ => simp [rootReducts] at h
  | recΔ _ _ _ =>
      simp only [ctxReducts]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))
  | eqW _ _ =>
      simp only [ctxReducts]
      exact List.mem_append_left _ (List.mem_append_left _ h)

theorem ctxReducts_complete {t u : Trace} (h : StepCtxFull t u) : u ∈ ctxReducts t := by
  induction h with
  | root hs =>
      exact mem_rootReducts_mem_ctxReducts (rootReducts_complete hs)
  | delta _ ih =>
      simp only [ctxReducts]
      exact List.mem_map.mpr ⟨_, ih, rfl⟩
  | integrate _ ih =>
      simp only [ctxReducts]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩)
  | mergeL _ ih =>
      simp only [ctxReducts]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩))
  | mergeR _ ih =>
      simp only [ctxReducts]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩)
  | appL _ ih =>
      simp only [ctxReducts]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨_, ih, rfl⟩)
  | appR _ ih =>
      simp only [ctxReducts]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩)
  | recB _ ih =>
      simp only [ctxReducts]
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩)))
  | recS _ ih =>
      simp only [ctxReducts]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩))
  | recN _ ih =>
      simp only [ctxReducts]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩)
  | eqWL _ ih =>
      simp only [ctxReducts]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩))
  | eqWR _ ih =>
      simp only [ctxReducts]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩)

/-- K21 live-relation iff: the enumerator is exactly `StepCtxFull`. -/
theorem ctxReducts_iff (t u : Trace) : u ∈ ctxReducts t ↔ StepCtxFull t u :=
  ⟨ctxReducts_sound, ctxReducts_complete⟩

/-! ## Bounded delta-head search -/

def isDeltaHead : Trace → Bool
  | delta _ => true
  | _ => false

theorem isDeltaHead_eq_true {a : Trace} :
    isDeltaHead a = true ↔ ∃ t', a = delta t' := by
  cases a <;> simp [isDeltaHead]

/-- Bounded search for a delta-headed contextual reduct. Fuel 0 inspects `a`
itself; fuel `n+1` inspects `a` and every one-step `ctxReducts` child at fuel `n`. -/
def reachesDeltaHeadFuel : Nat → Trace → Bool
  | 0, a => isDeltaHead a
  | n + 1, a => isDeltaHead a || (ctxReducts a).any (reachesDeltaHeadFuel n)

/-- Unconditional soundness: a true answer is a real region member. -/
theorem reachesDeltaHead_sound {fuel : Nat} {a : Trace}
    (h : reachesDeltaHeadFuel fuel a = true) :
    ∃ t', CtxStar a (delta t') := by
  induction fuel generalizing a with
  | zero =>
      simp [reachesDeltaHeadFuel] at h
      obtain ⟨t', rfl⟩ := isDeltaHead_eq_true.mp h
      exact ⟨t', Relation.ReflTransGen.refl⟩
  | succ n ih =>
      simp [reachesDeltaHeadFuel, Bool.or_eq_true, List.any_eq_true] at h
      rcases h with hδ | ⟨u, hu, hu'⟩
      · obtain ⟨t', rfl⟩ := isDeltaHead_eq_true.mp hδ
        exact ⟨t', Relation.ReflTransGen.refl⟩
      · obtain ⟨t', ht'⟩ := ih hu'
        exact ⟨t', Relation.ReflTransGen.head (ctxReducts_sound hu) ht'⟩

theorem reachesDeltaHeadFuel_succ (n : Nat) (a : Trace)
    (h : reachesDeltaHeadFuel n a = true) :
    reachesDeltaHeadFuel (n + 1) a = true := by
  induction n generalizing a with
  | zero =>
      simp [reachesDeltaHeadFuel] at h
      simp [reachesDeltaHeadFuel, h]
  | succ n ih =>
      unfold reachesDeltaHeadFuel at h ⊢
      cases hδ : isDeltaHead a
      · simp [hδ] at h ⊢
        obtain ⟨u, hu, hu'⟩ := h
        exact ⟨u, hu, ih u hu'⟩
      · rfl

theorem reachesDeltaHeadFuel_mono {a : Trace} {n m : Nat}
    (hle : n ≤ m) (h : reachesDeltaHeadFuel n a = true) :
    reachesDeltaHeadFuel m a = true := by
  induction hle with
  | refl => exact h
  | step _ ih => exact reachesDeltaHeadFuel_succ _ _ ih

/-- Completeness under an explicit counted-path fuel bound. -/
private theorem complete_pow {a b : Trace} {n : Nat}
    (hpow : StepCtxFullPow a n b) (hδ : isDeltaHead b = true) :
    reachesDeltaHeadFuel n a = true := by
  induction hpow with
  | refl t =>
      simpa [reachesDeltaHeadFuel] using hδ
  | tail hab _ ih =>
      unfold reachesDeltaHeadFuel
      refine (Bool.or_eq_true _ _).mpr (Or.inr ?_)
      rw [List.any_eq_true]
      exact ⟨_, ctxReducts_complete hab, ih hδ⟩

theorem reachesDeltaHead_complete_of_bound {a t' : Trace} {n fuel : Nat}
    (hpow : StepCtxFullPow a n (delta t')) (hle : n ≤ fuel) :
    reachesDeltaHeadFuel fuel a = true :=
  reachesDeltaHeadFuel_mono hle (complete_pow hpow rfl)

private theorem pow_snoc {a b c : Trace} {n : Nat}
    (h : StepCtxFullPow a n b) (hstep : StepCtxFull b c) :
    StepCtxFullPow a (n + 1) c := by
  induction h with
  | refl => exact StepCtxFullPow.tail hstep (StepCtxFullPow.refl c)
  | tail hab hbc ih => exact StepCtxFullPow.tail hab (ih hstep)

theorem pow_of_ctxStar {a b : Trace} (h : CtxStar a b) :
    ∃ n, StepCtxFullPow a n b := by
  induction h with
  | refl => exact ⟨0, StepCtxFullPow.refl a⟩
  | tail _ hstep ih =>
      obtain ⟨n, hp⟩ := ih
      exact ⟨n + 1, pow_snoc hp hstep⟩

/-- Upgrade: `W` orients `StepCtxFull`, so path length is `< W a`. Completeness
holds at fuel `W a` with no extra hypothesis. The SafeStepCtx derivation-length
bound is not used; this is the StepCtxFull polynomial bound already compiled. -/
theorem reachesDeltaHead_complete_of_W {a t' : Trace}
    (h : CtxStar a (delta t')) :
    reachesDeltaHeadFuel (W a) a = true := by
  obtain ⟨n, hpow⟩ := pow_of_ctxStar h
  exact reachesDeltaHead_complete_of_bound hpow
    (Nat.le_of_lt (stepCtxFullPow_length_lt_W hpow))

theorem reachesDeltaHeadFuel_W_iff (a : Trace) :
    reachesDeltaHeadFuel (W a) a = true ↔ ∃ t', CtxStar a (delta t') :=
  ⟨reachesDeltaHead_sound, fun ⟨_, h⟩ => reachesDeltaHead_complete_of_W h⟩

/-- On the fueled region, the classifier join verdict is the Bool composed
with `diagonal_ctx_joins_iff_reaches_delta`. -/
theorem boundary_membership_decidable_on_fueled_region
    (fuel : Nat) (a : Trace) (h : reachesDeltaHeadFuel fuel a = true) :
    JoinCtx void (integrate (merge a a)) :=
  (diagonal_ctx_joins_iff_reaches_delta a).mpr (reachesDeltaHead_sound h)

theorem classifier_join_iff_fueled_W (a : Trace) :
    JoinCtx void (integrate (merge a a)) ↔
      reachesDeltaHeadFuel (W a) a = true := by
  rw [diagonal_ctx_joins_iff_reaches_delta, reachesDeltaHeadFuel_W_iff]

/-! ## R5: closed-term evaluation by `rfl` -/

theorem reaches_void_fuel0 : reachesDeltaHeadFuel 0 void = false := rfl

theorem reaches_delta_fuel0 : reachesDeltaHeadFuel 0 (delta void) = true := rfl

theorem reaches_merge_fuel1 :
    reachesDeltaHeadFuel 1 (merge void (delta void)) = true := rfl

theorem reaches_void (n : Nat) : reachesDeltaHeadFuel n void = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [reachesDeltaHeadFuel, isDeltaHead, ctxReducts]

end OperatorKO7.Meta.DistinctionBoundary.RegionMembership
