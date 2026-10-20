import OperatorKO7.Meta.DistinctionBoundary.GodelPartial
import OperatorKO7.Meta.DistinctionBoundary.FreezeSetForced
import OperatorKO7.Meta.Decision.ReflectiveDependencyPairs

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Closure of the partiality escape

Left composition has extensional fixed points. Freeze-substitution of
successor does not. That is the compiled kill of the overstated recursion
form: substitution generates the diagonal, and the diagonal is what
successor excludes.

Quotation is not a kernel constructor. The `{eqW}` freeze does not restore
decode-quote stability under merge. Self-representability transported
through quotation is an identity reflective pair and is refused.

NameGate: no `goedel_first`, no `incompleteness`, no `feferman_completeness`.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelPartial

open OperatorKO7
open OperatorKO7.Meta.DistinctionBoundary.DiagonalLevels
open OperatorKO7.Meta.DistinctionBoundary.FreezeSetForced
open OperatorKO7.EqGuardedConfluence
open OperatorKO7.Meta.Decision.ReflectiveDependencyPairs
open Multiset

/-! ## Compose unfolding and successor iff -/

theorem convergesTo_compose {f g : PartialCode} {x v : Trace} :
    convergesTo (.compose f g) x v ↔
      ∃ u, convergesTo g x u ∧ convergesTo f u v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => cases hn
    | succ n =>
      cases hu : step n g x with
      | none =>
        have h' : (step n g x).bind (step n f) = some v := hn
        rw [hu] at h'
        cases h'
      | some u =>
        have hf : step n f u = some v := by
          have h' : (step n g x).bind (step n f) = some v := hn
          rw [hu] at h'
          exact h'
        exact ⟨u, ⟨n, hu⟩, ⟨n, hf⟩⟩
  · rintro ⟨u, ⟨n, hn⟩, ⟨m, hm⟩⟩
    cases n with
    | zero => cases hn
    | succ n =>
      cases m with
      | zero => cases hm
      | succ m =>
        let N := max (n + 1) (m + 1)
        have hgN : step N g x = some u :=
          step_mono (Nat.le_max_left (n + 1) (m + 1)) hn
        have hfN : step N f u = some v :=
          step_mono (Nat.le_max_right (n + 1) (m + 1)) hm
        refine ⟨N + 1, ?_⟩
        change (step N g x).bind (step N f) = some v
        rw [hgN]
        exact hfN

theorem convergesTo_succ_iff (x v : Trace) :
    convergesTo .succ x v ↔ v = Trace.delta x := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => cases hn
    | succ _n =>
      injection hn with hvu
      exact hvu.symm
  · rintro rfl
    exact ⟨1, rfl⟩

theorem compose_diverge_left_diverges (g : PartialCode) (x : Trace) :
    diverges (.compose .diverge g) x := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    cases hg : step n g x with
    | none =>
      change (step n g x).bind (step n .diverge) = none
      rw [hg]
      rfl
    | some u =>
      change (step n g x).bind (step n .diverge) = none
      rw [hg]
      exact step_diverge n u

/-! ## SizeOf occurs checks -/

theorem sizeOf_void : sizeOf (Trace.void : Trace) = 1 :=
  rfl

theorem sizeOf_delta (t : Trace) : sizeOf (Trace.delta t) = 1 + sizeOf t :=
  rfl

theorem sizeOf_merge (a b : Trace) :
    sizeOf (Trace.merge a b) = 1 + sizeOf a + sizeOf b :=
  rfl

theorem sizeOf_app (a b : Trace) :
    sizeOf (Trace.app a b) = 1 + sizeOf a + sizeOf b :=
  rfl

theorem sizeOf_code_succ : sizeOf PartialCode.succ = 1 := rfl
theorem sizeOf_code_proj : sizeOf PartialCode.proj = 1 := rfl
theorem sizeOf_code_call : sizeOf PartialCode.call = 1 := rfl
theorem sizeOf_code_diverge : sizeOf PartialCode.diverge = 1 := rfl
theorem sizeOf_code_const (t : Trace) :
    sizeOf (PartialCode.const t) = 1 + sizeOf t := rfl
theorem sizeOf_code_compose (f g : PartialCode) :
    sizeOf (PartialCode.compose f g) = 1 + sizeOf f + sizeOf g := rfl

theorem sizeOf_encode_call : sizeOf (encode PartialCode.call) = 4 := by
  simp [encode, sizeOf_delta, sizeOf_void]

theorem ne_delta_merge_void_self (t : Trace) :
    t ≠ Trace.delta (Trace.merge Trace.void t) := by
  intro h
  have hs := congrArg sizeOf h
  simp [sizeOf_delta, sizeOf_merge, sizeOf_void] at hs
  omega

theorem ne_delta_app_merge_void (t H : Trace) :
    t ≠ Trace.delta (Trace.app (Trace.merge Trace.void t) H) := by
  intro h
  have hs := congrArg sizeOf h
  simp [sizeOf_delta, sizeOf_app, sizeOf_merge, sizeOf_void] at hs
  omega

theorem ne_delta_app_right_merge (A t : Trace) :
    t ≠ Trace.delta (Trace.app A (Trace.merge Trace.void t)) := by
  intro h
  have hs := congrArg sizeOf h
  simp [sizeOf_delta, sizeOf_app, sizeOf_merge, sizeOf_void] at hs
  omega

theorem ne_app_merge_void_self (A t : Trace) :
    t ≠ Trace.app A (Trace.merge Trace.void t) := by
  intro h
  have hs := congrArg sizeOf h
  simp [sizeOf_app, sizeOf_merge, sizeOf_void] at hs
  omega

theorem ne_delta_app_delta_void_merge (u : Trace) :
    u ≠ Trace.delta (Trace.app (Trace.delta Trace.void)
      (Trace.merge Trace.void u)) := by
  intro h
  have hs := congrArg sizeOf h
  simp [sizeOf_delta, sizeOf_app, sizeOf_merge, sizeOf_void] at hs
  omega

theorem ne_app_succ_merge_void (u : Trace) :
    u ≠ Trace.app (encode .succ) (Trace.merge Trace.void u) := by
  intro h
  have hs := congrArg sizeOf h
  simp [encode, sizeOf_app, sizeOf_merge, sizeOf_delta, sizeOf_void] at hs
  omega

theorem ne_merge_void_delta_app (w A : Trace) :
    w ≠ Trace.merge Trace.void (Trace.delta (Trace.app A w)) := by
  intro h
  have hs := congrArg sizeOf h
  simp [sizeOf_merge, sizeOf_void, sizeOf_delta, sizeOf_app] at hs
  omega

/-! ## Call-free evaluator (honest on the sharp-kill witness) -/

def evalWF : PartialCode → Trace → Option Trace
  | .diverge, _ => none
  | .proj, x => some x
  | .succ, x => some (Trace.delta x)
  | .const t, _ => some t
  | .compose f g, x => (evalWF g x).bind (evalWF f)
  | .call, _ => none

theorem evalWF_succ_eq_step (x : Trace) :
    evalWF .succ x = step 1 .succ x :=
  rfl

theorem evalWF_proj_eq_step (x : Trace) :
    evalWF .proj x = step 1 .proj x :=
  rfl

theorem evalWF_diverge_eq_step (x : Trace) :
    evalWF .diverge x = step 1 .diverge x :=
  rfl

theorem evalWF_const_eq_step (t x : Trace) :
    evalWF (.const t) x = step 1 (.const t) x :=
  rfl

theorem evalWF_call_none (x : Trace) : evalWF .call x = none :=
  rfl

theorem call_diverges_at_void : diverges .call Trace.void := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    change step n (quote Trace.void) Trace.void = none
    rw [quote_void_eq_diverge]
    exact step_diverge n Trace.void

/-! ## Totality classification: constant or iterated successor -/

def containsCall : PartialCode → Bool
  | .call => true
  | .compose f g => containsCall f || containsCall g
  | _ => false

theorem containsCall_compose_false {f g : PartialCode}
    (h : containsCall (.compose f g) = false) :
    containsCall f = false ∧ containsCall g = false :=
  Bool.or_eq_false_iff.mp h

def deltaIter : Nat → Trace → Trace
  | 0, x => x
  | n + 1, x => Trace.delta (deltaIter n x)

theorem deltaIter_zero (x : Trace) : deltaIter 0 x = x :=
  rfl

theorem deltaIter_succ (n : Nat) (x : Trace) :
    deltaIter (n + 1) x = Trace.delta (deltaIter n x) :=
  rfl

theorem deltaIter_add (m n : Nat) (x : Trace) :
    deltaIter (m + n) x = deltaIter m (deltaIter n x) := by
  induction m with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ m ih =>
    rw [Nat.succ_add, deltaIter_succ, ih, deltaIter_succ]

theorem deltaIter_four (x : Trace) :
    deltaIter 4 x =
      Trace.delta (Trace.delta (Trace.delta (Trace.delta x))) :=
  rfl

theorem deltaIter_void_ne (k : Nat) :
    deltaIter k Trace.void ≠
      deltaIter k (Trace.delta Trace.void) := by
  induction k with
  | zero =>
    intro h
    exact Trace.noConfusion h
  | succ k ih =>
    intro h
    injection h with h'
    exact ih h'

theorem not_constant_of_deltaIter {e : PartialCode} {k : Nat} {v : Trace}
    (h : ∀ x, convergesTo e x (deltaIter k x)) :
    ¬ ∀ x, convergesTo e x v := by
  intro hc
  have h0 := convergesTo_unique (h Trace.void) (hc Trace.void)
  have h1 :=
    convergesTo_unique (h (Trace.delta Trace.void))
      (hc (Trace.delta Trace.void))
  exact deltaIter_void_ne k (h0.trans h1.symm)

theorem call_diverges_at_own_code :
    ∀ n, step n .call (encode .call) = none
  | 0 => rfl
  | n + 1 => by
    have hw : quote (encode .call) = .call := quote_encode .call
    change step n (quote (encode .call)) (encode .call) = none
    rw [hw]
    exact call_diverges_at_own_code n

theorem decode_delta4 (t : Trace) :
    decode (Trace.delta (Trace.delta (Trace.delta (Trace.delta t)))) =
      none := by
  cases t <;> rfl

theorem quote_deltaIter_add_four (n : Nat) :
    quote (deltaIter (n + 4) Trace.void) = .diverge := by
  have hshape :
      deltaIter (n + 4) Trace.void =
        Trace.delta (Trace.delta (Trace.delta (Trace.delta
          (deltaIter n Trace.void)))) := by
    rw [show n + 4 = 4 + n from Nat.add_comm n 4, deltaIter_add,
      deltaIter_four]
  simp [quote, hshape, decode_delta4]

theorem convergesTo_compose_assoc {f1 f2 g : PartialCode} {x v : Trace} :
    convergesTo (.compose (.compose f1 f2) g) x v ↔
      convergesTo (.compose f1 (.compose f2 g)) x v := by
  constructor
  · intro h
    obtain ⟨u, hgu, hf⟩ := convergesTo_compose.mp h
    obtain ⟨w, hf2, hf1⟩ := convergesTo_compose.mp hf
    exact convergesTo_compose.mpr
      ⟨w, convergesTo_compose.mpr ⟨u, hgu, hf2⟩, hf1⟩
  · intro h
    obtain ⟨w, hinner, hf1⟩ := convergesTo_compose.mp h
    obtain ⟨u, hgu, hf2⟩ := convergesTo_compose.mp hinner
    exact convergesTo_compose.mpr
      ⟨u, hgu, convergesTo_compose.mpr ⟨w, hf2, hf1⟩⟩

theorem compose_call_of_deltaIter_not_total {g : PartialCode} {k : Nat}
    (hg : ∀ x, convergesTo g x (deltaIter k x)) :
    ¬ ∀ x, ∃ v, convergesTo (.compose .call g) x v := by
  intro htot
  match k with
  | 0 =>
    obtain ⟨_v, hv⟩ := htot Trace.void
    obtain ⟨u, hgu, hcu⟩ := convergesTo_compose.mp hv
    have hu : u = Trace.void := by
      have hgv := hg Trace.void
      rw [deltaIter_zero] at hgv
      exact convergesTo_unique hgu hgv
    subst hu
    obtain ⟨n, hn⟩ := hcu
    have hd := call_diverges_at_void n
    rw [hd] at hn
    cases hn
  | 1 =>
    let x := Trace.delta (Trace.delta Trace.void)
    obtain ⟨_v, hv⟩ := htot x
    obtain ⟨u, hgu, hcu⟩ := convergesTo_compose.mp hv
    have hu : u = encode .call :=
      convergesTo_unique hgu (by
        have hgx := hg x
        change convergesTo g x (encode .call) at hgx
        exact hgx)
    subst hu
    obtain ⟨n, hn⟩ := hcu
    have hd := call_diverges_at_own_code n
    rw [hd] at hn
    cases hn
  | 2 =>
    let x := Trace.delta Trace.void
    obtain ⟨_v, hv⟩ := htot x
    obtain ⟨u, hgu, hcu⟩ := convergesTo_compose.mp hv
    have hu : u = encode .call :=
      convergesTo_unique hgu (by
        have hgx := hg x
        change convergesTo g x (encode .call) at hgx
        exact hgx)
    subst hu
    obtain ⟨n, hn⟩ := hcu
    have hd := call_diverges_at_own_code n
    rw [hd] at hn
    cases hn
  | n + 3 =>
    obtain ⟨_v, hv⟩ := htot Trace.void
    obtain ⟨u, hgu, hcu⟩ := convergesTo_compose.mp hv
    have hu : u = deltaIter (n + 3) Trace.void :=
      convergesTo_unique hgu (hg Trace.void)
    subst hu
    obtain ⟨m, hm⟩ := hcu
    cases n with
    | zero =>
      have henc : deltaIter 3 Trace.void = encode .call := rfl
      rw [henc] at hm
      have hd := call_diverges_at_own_code m
      rw [hd] at hm
      cases hm
    | succ n =>
      have hq : quote (deltaIter (n + 1 + 3) Trace.void) = .diverge := by
        rw [show n + 1 + 3 = n + 4 from rfl]
        exact quote_deltaIter_add_four n
      cases m with
      | zero => cases hm
      | succ m =>
        change step m (quote (deltaIter (n + 1 + 3) Trace.void))
            (deltaIter (n + 1 + 3) Trace.void) = some _v at hm
        rw [hq] at hm
        have hd := step_diverge m (deltaIter (n + 1 + 3) Trace.void)
        rw [hd] at hm
        cases hm

theorem compose_class_of (f g : PartialCode)
    (hg : (∃ t, ∀ x, convergesTo g x t) ∨
      (∃ k, ∀ x, convergesTo g x (deltaIter k x)))
    (htot : ∀ x, ∃ v, convergesTo (.compose f g) x v) :
    (∃ t, ∀ x, convergesTo (.compose f g) x t) ∨
      (∃ k, ∀ x, convergesTo (.compose f g) x (deltaIter k x)) := by
  induction f generalizing g hg with
  | diverge =>
    obtain ⟨_v, hv⟩ := htot Trace.void
    obtain ⟨u, _hgu, hfu⟩ := convergesTo_compose.mp hv
    obtain ⟨n, hn⟩ := hfu
    have hd := step_diverge n u
    rw [hd] at hn
    cases hn
  | proj =>
    cases hg with
    | inl hconst =>
      obtain ⟨t, ht⟩ := hconst
      refine Or.inl ⟨t, ?_⟩
      intro x
      exact convergesTo_compose.mpr
        ⟨t, ht x, (convergesTo_proj_iff t t).mpr rfl⟩
    | inr hdelta =>
      obtain ⟨k, hk⟩ := hdelta
      refine Or.inr ⟨k, ?_⟩
      intro x
      exact convergesTo_compose.mpr
        ⟨deltaIter k x, hk x, (convergesTo_proj_iff _ _).mpr rfl⟩
  | succ =>
    cases hg with
    | inl hconst =>
      obtain ⟨t, ht⟩ := hconst
      refine Or.inl ⟨Trace.delta t, ?_⟩
      intro x
      exact convergesTo_compose.mpr
        ⟨t, ht x, (convergesTo_succ_iff t _).mpr rfl⟩
    | inr hdelta =>
      obtain ⟨k, hk⟩ := hdelta
      refine Or.inr ⟨k + 1, ?_⟩
      intro x
      refine convergesTo_compose.mpr ⟨deltaIter k x, hk x, ?_⟩
      have : deltaIter (k + 1) x = Trace.delta (deltaIter k x) := rfl
      rw [this]
      exact (convergesTo_succ_iff (deltaIter k x) _).mpr rfl
  | const t =>
    refine Or.inl ⟨t, ?_⟩
    intro x
    obtain ⟨v, hv⟩ := htot x
    obtain ⟨u, _hgu, hfu⟩ := convergesTo_compose.mp hv
    have hv' : v = t := (convergesTo_const_iff t u v).mp hfu
    subst hv'
    exact hv
  | call =>
    cases hg with
    | inl hconst =>
      obtain ⟨s, hs⟩ := hconst
      obtain ⟨v0, hv0⟩ := htot Trace.void
      obtain ⟨u0, hgu0, hcu0⟩ := convergesTo_compose.mp hv0
      have hu0 : u0 = s := convergesTo_unique hgu0 (hs Trace.void)
      refine Or.inl ⟨v0, ?_⟩
      intro x
      obtain ⟨v, hv⟩ := htot x
      obtain ⟨u, hgu, hcu⟩ := convergesTo_compose.mp hv
      have hu : u = s := convergesTo_unique hgu (hs x)
      have hcu' : convergesTo .call s v := hu ▸ hcu
      have hcu0' : convergesTo .call s v0 := hu0 ▸ hcu0
      have : v = v0 := convergesTo_unique hcu' hcu0'
      exact this ▸ hv
    | inr hdelta =>
      obtain ⟨k, hk⟩ := hdelta
      exact (compose_call_of_deltaIter_not_total hk htot).elim
  | compose f1 f2 ih1 ih2 =>
    have hinner_tot : ∀ x, ∃ v, convergesTo (.compose f2 g) x v := by
      intro x
      obtain ⟨v, hv⟩ := htot x
      obtain ⟨u, hgu, hf⟩ := convergesTo_compose.mp hv
      obtain ⟨w, hf2, _hf1⟩ := convergesTo_compose.mp hf
      exact ⟨w, convergesTo_compose.mpr ⟨u, hgu, hf2⟩⟩
    have hinner := ih2 g hg hinner_tot
    have htot' : ∀ x, ∃ v,
        convergesTo (.compose f1 (.compose f2 g)) x v := by
      intro x
      obtain ⟨v, hv⟩ := htot x
      exact ⟨v, convergesTo_compose_assoc.mp hv⟩
    have houter := ih1 (.compose f2 g) hinner htot'
    cases houter with
    | inl hconst =>
      obtain ⟨t, ht⟩ := hconst
      refine Or.inl ⟨t, ?_⟩
      intro x
      exact convergesTo_compose_assoc.mpr (ht x)
    | inr hdelta =>
      obtain ⟨k, hk⟩ := hdelta
      refine Or.inr ⟨k, ?_⟩
      intro x
      exact convergesTo_compose_assoc.mpr (hk x)

theorem total_const_or_deltaIter (e : PartialCode)
    (htot : ∀ x, ∃ v, convergesTo e x v) :
    (∃ t, ∀ x, convergesTo e x t) ∨
      (∃ k, ∀ x, convergesTo e x (deltaIter k x)) := by
  induction e with
  | diverge =>
    obtain ⟨_v, ⟨n, hn⟩⟩ := htot Trace.void
    have hd := step_diverge n Trace.void
    rw [hd] at hn
    cases hn
  | proj =>
    refine Or.inr ⟨0, ?_⟩
    intro x
    rw [deltaIter_zero]
    exact (convergesTo_proj_iff x x).mpr rfl
  | succ =>
    refine Or.inr ⟨1, ?_⟩
    intro x
    exact (convergesTo_succ_iff x (deltaIter 1 x)).mpr rfl
  | const t =>
    exact Or.inl ⟨t, fun _x => ⟨1, rfl⟩⟩
  | call =>
    obtain ⟨_v, ⟨n, hn⟩⟩ := htot Trace.void
    have hd := call_diverges_at_void n
    rw [hd] at hn
    cases hn
  | compose f g _ihf ihg =>
    have hgtot : ∀ x, ∃ v, convergesTo g x v := by
      intro x
      obtain ⟨v, hv⟩ := htot x
      obtain ⟨u, hgu, _⟩ := convergesTo_compose.mp hv
      exact ⟨u, hgu⟩
    exact compose_class_of f g (ihg hgtot) htot

theorem callFree_value_size {e : PartialCode} {x v : Trace}
    (hc : containsCall e = false) (h : convergesTo e x v) :
    sizeOf v < sizeOf (encode e) + sizeOf x := by
  induction e generalizing x v with
  | diverge =>
    obtain ⟨n, hn⟩ := h
    have hd := step_diverge n x
    rw [hd] at hn
    cases hn
  | proj =>
    have hv := (convergesTo_proj_iff x v).mp h
    subst hv
    simp [encode]
  | succ =>
    have hv := (convergesTo_succ_iff x v).mp h
    subst hv
    simp [encode]
  | const t =>
    have hv := (convergesTo_const_iff t x v).mp h
    subst hv
    simp [encode]
    omega
  | call =>
    simp [containsCall] at hc
  | compose f g ihf ihg =>
    obtain ⟨hf, hg⟩ := containsCall_compose_false hc
    obtain ⟨u, hgu, hfu⟩ := convergesTo_compose.mp h
    have hsu := ihg hg hgu
    have hsv := ihf hf hfu
    simp [encode, sizeOf_app] at hsu hsv ⊢
    omega

theorem callFree_not_constantly_delta {e : PartialCode}
    (hc : containsCall e = false)
    (h : ∀ x, convergesTo e x (Trace.delta (encode e))) : False := by
  have hs := callFree_value_size hc (h Trace.void)
  simp [sizeOf_delta, sizeOf_void] at hs
  omega

/-! ## No code is constantly `delta` of its own encoding -/

def leftHead : PartialCode → PartialCode
  | .compose f _ => leftHead f
  | c => c

theorem leftHead_const_eval {e : PartialCode} {r t x : Trace}
    (hh : leftHead e = .const r) (h : convergesTo e x t) : t = r := by
  induction e generalizing x t with
  | const s =>
    have hh' : PartialCode.const s = .const r := hh
    injection hh' with hr
    rw [hr] at h
    exact (convergesTo_const_iff r x t).mp h
  | compose f g ih =>
    simp only [leftHead] at hh
    obtain ⟨u, _hgu, hfu⟩ := convergesTo_compose.mp h
    exact ih hh hfu
  | diverge => simp [leftHead] at hh
  | proj => simp [leftHead] at hh
  | succ => simp [leftHead] at hh
  | call => simp [leftHead] at hh

theorem leftHead_const_eval_all {e : PartialCode} {r t : Trace}
    (hh : leftHead e = .const r) (h : ∀ x, convergesTo e x t) : t = r :=
  leftHead_const_eval hh (h Trace.void)

theorem encode_of_leftHead_const {e : PartialCode} {r : Trace}
    (hh : leftHead e = .const r) :
    sizeOf r + 2 ≤ sizeOf (encode e) := by
  induction e with
  | const s =>
    injection hh with hh'
    subst hh'
    simp [encode, sizeOf_merge, sizeOf_void]
    omega
  | compose f g ih =>
    simp [leftHead] at hh
    have hfg := ih hh
    simp [encode, sizeOf_app]
    omega
  | diverge => simp [leftHead] at hh
  | proj => simp [leftHead] at hh
  | succ => simp [leftHead] at hh
  | call => simp [leftHead] at hh

theorem leftHead_ne_compose (e f g : PartialCode) :
    leftHead e ≠ .compose f g := by
  induction e with
  | compose f' _ ih => exact ih
  | diverge => intro h; cases h
  | proj => intro h; cases h
  | succ => intro h; cases h
  | const _ => intro h; cases h
  | call => intro h; cases h

theorem leftHead_diverge_diverges {e : PartialCode}
    (hh : leftHead e = .diverge) (x : Trace) : diverges e x := by
  induction e generalizing x with
  | diverge => exact diverges_diverge x
  | compose f g ih =>
    simp only [leftHead] at hh
    intro n
    cases n with
    | zero => rfl
    | succ n =>
      cases hg : step n g x with
      | none =>
        change (step n g x).bind (step n f) = none
        rw [hg]
        rfl
      | some u =>
        change (step n g x).bind (step n f) = none
        rw [hg]
        exact ih hh u n
  | proj => simp [leftHead] at hh
  | succ => simp [leftHead] at hh
  | const _ => simp [leftHead] at hh
  | call => simp [leftHead] at hh

theorem leftHead_succ_is_delta {e : PartialCode} {x t : Trace}
    (hh : leftHead e = .succ) (h : convergesTo e x t) :
    ∃ u, t = Trace.delta u := by
  induction e generalizing x t with
  | succ => exact ⟨x, (convergesTo_succ_iff x t).mp h⟩
  | compose f _g ih =>
    simp only [leftHead] at hh
    obtain ⟨u, _hgu, hfu⟩ := convergesTo_compose.mp h
    exact ih hh hfu
  | diverge => simp [leftHead] at hh
  | proj => simp [leftHead] at hh
  | const _ => simp [leftHead] at hh
  | call => simp [leftHead] at hh


def IsCompound : Trace → Prop
  | .merge _ _ => True
  | .app _ _ => True
  | _ => False

theorem isCompound_merge (a b : Trace) : IsCompound (Trace.merge a b) :=
  trivial

theorem isCompound_app (a b : Trace) : IsCompound (Trace.app a b) :=
  trivial

theorem not_compound_delta (t : Trace) : ¬ IsCompound (Trace.delta t) :=
  fun h => h

theorem not_compound_void : ¬ IsCompound Trace.void :=
  fun h => h

theorem trace_size_pos (t : Trace) : 1 ≤ sizeOf t := by
  induction t with
  | void => rw [sizeOf_void]
  | delta a ih => rw [sizeOf_delta]; omega
  | integrate a ih =>
    have : sizeOf (Trace.integrate a) = 1 + sizeOf a := rfl
    rw [this]; omega
  | merge a b iha ihb => rw [sizeOf_merge]; omega
  | app a b iha ihb => rw [sizeOf_app]; omega
  | recΔ a b c iha ihb ihc =>
    have : sizeOf (Trace.recΔ a b c) = 1 + sizeOf a + sizeOf b + sizeOf c :=
      rfl
    rw [this]; omega
  | eqW a b iha ihb =>
    have : sizeOf (Trace.eqW a b) = 1 + sizeOf a + sizeOf b := rfl
    rw [this]; omega

theorem app_size_ge_three (a b : Trace) : 3 ≤ sizeOf (Trace.app a b) := by
  rw [sizeOf_app]
  have := trace_size_pos a
  have := trace_size_pos b
  omega

theorem encode_size_pos (e : PartialCode) : 1 ≤ sizeOf (encode e) := by
  induction e with
  | diverge => rw [encode, sizeOf_void]
  | proj => rw [encode, sizeOf_delta, sizeOf_void]; omega
  | succ => rw [encode, sizeOf_delta, sizeOf_delta, sizeOf_void]; omega
  | call =>
    rw [encode, sizeOf_delta, sizeOf_delta, sizeOf_delta, sizeOf_void]
    omega
  | const t =>
    rw [encode, sizeOf_merge, sizeOf_void]
    have := trace_size_pos t
    omega
  | compose f g ihf ihg =>
    rw [encode, sizeOf_app]
    omega

theorem sizeOf_encode_compose (f g : PartialCode) :
    sizeOf (encode (.compose f g)) =
      1 + sizeOf (encode f) + sizeOf (encode g) := by
  rw [encode, sizeOf_app]

theorem encode_le_compose_left (f g : PartialCode) :
    sizeOf (encode f) ≤ sizeOf (encode (.compose f g)) := by
  rw [sizeOf_encode_compose]
  have := encode_size_pos g
  omega

theorem encode_le_compose_right (f g : PartialCode) :
    sizeOf (encode g) ≤ sizeOf (encode (.compose f g)) := by
  rw [sizeOf_encode_compose]
  have := encode_size_pos f
  omega

theorem step_compose_some {f g : PartialCode} {x t : Trace} {n : Nat}
    (h : step (n + 1) (.compose f g) x = some t) :
    ∃ u, step n g x = some u ∧ step n f u = some t := by
  rw [step_compose] at h
  cases hstep : step n g x with
  | none =>
    rw [hstep] at h
    cases h
  | some u =>
    rw [hstep] at h
    exact ⟨u, rfl, h⟩

mutual

theorem step_compound_from_atom :
    ∀ {n : Nat} {f : PartialCode} {x t : Trace},
      step n f x = some t → IsCompound t → ¬ IsCompound x →
        sizeOf t + 2 ≤ sizeOf (encode f)
  | 0, _, _, _, h, _, _ => by cases h
  | n + 1, f, x, t, h, ht, hx => by
    cases f with
    | diverge =>
      rw [step_diverge] at h
      cases h
    | proj =>
      have hx' : t = x := by
        rw [step_proj] at h
        injection h with h'
        exact h'.symm
      exact False.elim (hx (hx' ▸ ht))
    | succ =>
      have ht' : t = Trace.delta x := by
        rw [step_succ] at h
        injection h with h'
        exact h'.symm
      exact False.elim (not_compound_delta x (ht' ▸ ht))
    | const r =>
      have hr : t = r := by
        rw [step_const] at h
        injection h with h'
        exact h'.symm
      subst hr
      rw [encode, sizeOf_merge, sizeOf_void]
      omega
    | call =>
      have h' : step n (quote x) x = some t := by
        rw [step_call] at h
        exact h
      cases hxdec : decode x with
      | none =>
        have hq : quote x = .diverge := by simp [quote, hxdec]
        rw [hq, step_diverge] at h'
        cases h'
      | some c =>
        have henc : encode c = x := encode_of_decode hxdec
        cases c with
        | const _ =>
          rw [← henc, encode] at hx
          exact False.elim (hx trivial)
        | compose _ _ =>
          rw [← henc, encode] at hx
          exact False.elim (hx trivial)
        | diverge =>
          have hq : quote x = .diverge := by simp [quote, hxdec]
          rw [hq, step_diverge] at h'
          cases h'
        | proj =>
          have hq : quote x = .proj := by simp [quote, hxdec]
          rw [hq] at h'
          cases n with
          | zero => cases h'
          | succ n =>
            rw [step_proj] at h'
            have hx' : t = x := by
              injection h' with hxy
              exact hxy.symm
            exact False.elim (hx (hx' ▸ ht))
        | succ =>
          have hq : quote x = .succ := by simp [quote, hxdec]
          rw [hq] at h'
          cases n with
          | zero => cases h'
          | succ n =>
            rw [step_succ] at h'
            have ht' : t = Trace.delta x := by
              injection h' with hxy
              exact hxy.symm
            exact False.elim (not_compound_delta x (ht' ▸ ht))
        | call =>
          have henc' : x = encode .call := by
            have := encode_of_decode hxdec
            simp [encode] at this
            exact this.symm
          rw [henc'] at h
          have hd := call_diverges_at_own_code (n + 1)
          rw [hd] at h
          cases h
    | compose f g =>
      obtain ⟨u, hgu, hfu⟩ := step_compose_some h
      by_cases hu : IsCompound u
      · have hgsz := step_compound_from_atom hgu hu hx
        have hfsz := eval_compound_le hfu ht
        cases hfsz with
        | inl h1 =>
          have henc := sizeOf_encode_compose f g
          have hgpos := encode_size_pos g
          omega
        | inr h2 =>
          have henc := sizeOf_encode_compose f g
          have hfpos := encode_size_pos f
          omega
      · have hfsz := step_compound_from_atom hfu ht hu
        have henc := sizeOf_encode_compose f g
        have hgpos := encode_size_pos g
        omega
termination_by n => n

theorem eval_compound_le :
    ∀ {n : Nat} {f : PartialCode} {x t : Trace},
      step n f x = some t → IsCompound t →
        sizeOf t ≤ sizeOf (encode f) ∨ sizeOf t ≤ sizeOf x
  | 0, _, _, _, h, _ => by cases h
  | n + 1, f, x, t, h, ht => by
    cases f with
    | diverge =>
      rw [step_diverge] at h
      cases h
    | proj =>
      have hx' : t = x := by
        rw [step_proj] at h
        injection h with h'
        exact h'.symm
      subst hx'
      exact Or.inr le_rfl
    | succ =>
      have ht' : t = Trace.delta x := by
        rw [step_succ] at h
        injection h with h'
        exact h'.symm
      exact False.elim (not_compound_delta x (ht' ▸ ht))
    | const r =>
      have hr : t = r := by
        rw [step_const] at h
        injection h with h'
        exact h'.symm
      subst hr
      refine Or.inl ?_
      rw [encode, sizeOf_merge, sizeOf_void]
      omega
    | call =>
      have h' : step n (quote x) x = some t := by
        rw [step_call] at h
        exact h
      cases hq : decode x with
      | none =>
        have hq' : quote x = .diverge := by simp [quote, hq]
        rw [hq', step_diverge] at h'
        cases h'
      | some c =>
        have henc : encode c = x := encode_of_decode hq
        have hq' : quote x = c := by simp [quote, hq]
        rw [hq'] at h'
        have ih := eval_compound_le h' ht
        cases ih with
        | inl h1 =>
          rw [henc] at h1
          exact Or.inr h1
        | inr h2 => exact Or.inr h2
    | compose f g =>
      obtain ⟨u, hgu, hfu⟩ := step_compose_some h
      have ihf := eval_compound_le hfu ht
      cases ihf with
      | inl h1 =>
        exact Or.inl (h1.trans (encode_le_compose_left f g))
      | inr h2 =>
        by_cases hu : IsCompound u
        · have ihg := eval_compound_le hgu hu
          cases ihg with
          | inl h3 =>
            exact Or.inl ((h2.trans h3).trans (encode_le_compose_right f g))
          | inr h4 => exact Or.inr (h2.trans h4)
        · have hfsz := step_compound_from_atom hfu ht hu
          exact Or.inl (by
            have henc := sizeOf_encode_compose f g
            have hgpos := encode_size_pos g
            omega)
termination_by n => n

end

theorem eval_compound_le_conv {f : PartialCode} {x t : Trace}
    (h : convergesTo f x t) (ht : IsCompound t) :
    sizeOf t ≤ sizeOf (encode f) ∨ sizeOf t ≤ sizeOf x :=
  let ⟨n, hn⟩ := h
  eval_compound_le hn ht

theorem step_compound_from_atom_conv {f : PartialCode} {x t : Trace}
    (h : convergesTo f x t) (ht : IsCompound t) (hx : ¬ IsCompound x) :
    sizeOf t + 2 ≤ sizeOf (encode f) :=
  let ⟨n, hn⟩ := h
  step_compound_from_atom hn ht hx


mutual

theorem copy_delta_of_app :
    ∀ {n : Nat} {f : PartialCode} {x tgt : Trace},
      step n f x = some (Trace.delta tgt) →
        (∃ a b, tgt = Trace.app a b) →
          ¬ IsCompound x →
            ¬ (sizeOf tgt ≤ sizeOf (encode f)) →
              x = Trace.delta tgt
  | 0, _, _, _, h, _, _, _ => by cases h
  | n + 1, f, x, tgt, h, happ, hx, hbig => by
    cases f with
    | diverge =>
      rw [step_diverge] at h
      cases h
    | proj =>
      have hx' : x = Trace.delta tgt := by
        rw [step_proj] at h
        injection h
      exact hx'
    | succ =>
      have hx' : x = tgt := by
        rw [step_succ] at h
        injection h with h'
        injection h'
      obtain ⟨a, b, hab⟩ := happ
      exact False.elim (hx (by
        rw [hx', hab]
        exact isCompound_app a b))
    | const r =>
      have hr : r = Trace.delta tgt := by
        rw [step_const] at h
        injection h
      subst hr
      refine False.elim (hbig ?_)
      rw [encode, sizeOf_merge, sizeOf_void, sizeOf_delta]
      omega
    | call =>
      have h' : step n (quote x) x = some (Trace.delta tgt) := by
        rw [step_call] at h
        exact h
      cases hq : decode x with
      | none =>
        have hq' : quote x = .diverge := by simp [quote, hq]
        rw [hq', step_diverge] at h'
        cases h'
      | some c =>
        have henc : encode c = x := encode_of_decode hq
        cases c with
        | const _ =>
          rw [← henc, encode] at hx
          exact False.elim (hx trivial)
        | compose _ _ =>
          rw [← henc, encode] at hx
          exact False.elim (hx trivial)
        | diverge =>
          have hq' : quote x = .diverge := by simp [quote, hq]
          rw [hq', step_diverge] at h'
          cases h'
        | proj =>
          have hq' : quote x = .proj := by simp [quote, hq]
          rw [hq'] at h'
          cases n with
          | zero => cases h'
          | succ n =>
            rw [step_proj] at h'
            injection h'
        | succ =>
          have hq' : quote x = .succ := by simp [quote, hq]
          rw [hq'] at h'
          cases n with
          | zero => cases h'
          | succ n =>
            rw [step_succ] at h'
            have hx' : x = tgt := by
              injection h' with hxy
              injection hxy
            obtain ⟨a, b, hab⟩ := happ
            exact False.elim (hx (by
              rw [hx', hab]
              exact isCompound_app a b))
        | call =>
          have henc' : x = encode .call := by
            have := encode_of_decode hq
            simp [encode] at this
            exact this.symm
          rw [henc'] at h
          have hd := call_diverges_at_own_code (n + 1)
          rw [hd] at h
          cases h
    | compose f g =>
      obtain ⟨u, hgu, hfu⟩ := step_compose_some h
      have hltf : ¬ (sizeOf tgt ≤ sizeOf (encode f)) := by
        intro hle
        exact hbig (hle.trans (encode_le_compose_left f g))
      by_cases hu : IsCompound u
      · have hf := eval_delta_app_le hfu happ
        have hgsz := step_compound_from_atom hgu hu hx
        cases hf with
        | inl h1 => exact False.elim (hltf h1)
        | inr h2 =>
          have henc := sizeOf_encode_compose f g
          have hfpos := encode_size_pos f
          omega
      · have hu' := copy_delta_of_app hfu happ hu hltf
        have hltg : ¬ (sizeOf tgt ≤ sizeOf (encode g)) := by
          intro hle
          exact hbig (hle.trans (encode_le_compose_right f g))
        have hgu' : step n g x = some (Trace.delta tgt) := by
          rw [← hu']
          exact hgu
        exact copy_delta_of_app hgu' happ hx hltg
termination_by n => n

theorem eval_delta_app_le :
    ∀ {n : Nat} {f : PartialCode} {x tgt : Trace},
      step n f x = some (Trace.delta tgt) →
        (∃ a b, tgt = Trace.app a b) →
          sizeOf tgt ≤ sizeOf (encode f) ∨ sizeOf tgt ≤ sizeOf x
  | 0, _, _, _, h, _ => by cases h
  | n + 1, f, x, tgt, h, happ => by
    cases f with
    | diverge =>
      rw [step_diverge] at h
      cases h
    | proj =>
      have hx' : x = Trace.delta tgt := by
        rw [step_proj] at h
        injection h
      subst hx'
      exact Or.inr (by rw [sizeOf_delta]; omega)
    | succ =>
      have hx' : x = tgt := by
        rw [step_succ] at h
        injection h with h'
        injection h'
      subst hx'
      exact Or.inr le_rfl
    | const r =>
      have hr : r = Trace.delta tgt := by
        rw [step_const] at h
        injection h
      subst hr
      refine Or.inl ?_
      rw [encode, sizeOf_merge, sizeOf_void, sizeOf_delta]
      omega
    | call =>
      have h' : step n (quote x) x = some (Trace.delta tgt) := by
        rw [step_call] at h
        exact h
      cases hq : decode x with
      | none =>
        have hq' : quote x = .diverge := by simp [quote, hq]
        rw [hq', step_diverge] at h'
        cases h'
      | some c =>
        have henc : encode c = x := encode_of_decode hq
        have hq' : quote x = c := by simp [quote, hq]
        rw [hq'] at h'
        have ih := eval_delta_app_le h' happ
        cases ih with
        | inl h1 =>
          rw [henc] at h1
          exact Or.inr h1
        | inr h2 => exact Or.inr h2
    | compose f g =>
      obtain ⟨u, hgu, hfu⟩ := step_compose_some h
      have ihf := eval_delta_app_le hfu happ
      cases ihf with
      | inl h1 =>
        exact Or.inl (h1.trans (encode_le_compose_left f g))
      | inr h2 =>
        by_cases hleF : sizeOf tgt ≤ sizeOf (encode f)
        · exact Or.inl (hleF.trans (encode_le_compose_left f g))
        · by_cases hu : IsCompound u
          · have ihg := eval_compound_le hgu hu
            cases ihg with
            | inl h3 =>
              exact Or.inl ((h2.trans h3).trans (encode_le_compose_right f g))
            | inr h4 => exact Or.inr (h2.trans h4)
          · have hu' := copy_delta_of_app hfu happ hu hleF
            have ihg := eval_delta_app_le (hu' ▸ hgu) happ
            cases ihg with
            | inl h3 =>
              exact Or.inl (h3.trans (encode_le_compose_right f g))
            | inr h4 => exact Or.inr h4
termination_by n => n

end

theorem eval_delta_app_le_conv {f : PartialCode} {x tgt : Trace}
    (h : convergesTo f x (Trace.delta tgt))
    (happ : ∃ a b, tgt = Trace.app a b) :
    sizeOf tgt ≤ sizeOf (encode f) ∨ sizeOf tgt ≤ sizeOf x :=
  let ⟨n, hn⟩ := h
  eval_delta_app_le hn happ

theorem own_delta_app_le {c : PartialCode} {tgt : Trace}
    (h : convergesTo c (encode c) (Trace.delta tgt))
    (happ : ∃ a b, tgt = Trace.app a b) :
    sizeOf tgt ≤ sizeOf (encode c) := by
  cases eval_delta_app_le_conv h happ with
  | inl h1 => exact h1
  | inr h2 => exact h2

theorem constant_compound_size {e : PartialCode} {t : Trace}
    (h : ∀ x, convergesTo e x t) (ht : IsCompound t) :
    sizeOf t + 2 ≤ sizeOf (encode e) := by
  induction e generalizing t with
  | diverge =>
    obtain ⟨n, hn⟩ := h Trace.void
    rw [step_diverge] at hn
    cases hn
  | proj =>
    have hv : t = Trace.void := (convergesTo_proj_iff _ _).mp (h Trace.void)
    subst hv
    exact False.elim (not_compound_void ht)
  | succ =>
    have hv : t = Trace.delta Trace.void :=
      (convergesTo_succ_iff _ _).mp (h Trace.void)
    subst hv
    exact False.elim (not_compound_delta _ ht)
  | const r =>
    have hr : t = r := (convergesTo_const_iff r Trace.void t).mp (h Trace.void)
    subst hr
    rw [encode, sizeOf_merge, sizeOf_void]
    omega
  | call =>
    obtain ⟨n, hn⟩ := h Trace.void
    have hd := call_diverges_at_void n
    rw [hd] at hn
    cases hn
  | compose f g ihf ihg =>
    have hgtot : ∀ x, ∃ u, convergesTo g x u := by
      intro x
      obtain ⟨u, hgu, _⟩ := convergesTo_compose.mp (h x)
      exact ⟨u, hgu⟩
    cases total_const_or_deltaIter g hgtot with
    | inl hs =>
      obtain ⟨s, hs⟩ := hs
      obtain ⟨u, hgu, hfu⟩ := convergesTo_compose.mp (h Trace.void)
      have hu : u = s := convergesTo_unique hgu (hs Trace.void)
      have hf : convergesTo f s t := hu ▸ hfu
      have hle := eval_compound_le_conv hf ht
      cases hle with
      | inl h1 =>
        have henc := sizeOf_encode_compose f g
        have hgpos := encode_size_pos g
        omega
      | inr h2 =>
        by_cases hsc : IsCompound s
        · have ih := ihg hs hsc
          have henc := sizeOf_encode_compose f g
          omega
        · have hsz := step_compound_from_atom_conv hf ht hsc
          have henc := sizeOf_encode_compose f g
          have hgpos := encode_size_pos g
          omega
    | inr hk =>
      obtain ⟨k, hk⟩ := hk
      cases k with
      | zero =>
        have hf : ∀ x, convergesTo f x t := by
          intro x
          obtain ⟨u, hgu, hfu⟩ := convergesTo_compose.mp (h x)
          have hu : u = x := by
            have hgx := hk x
            rw [deltaIter_zero] at hgx
            exact convergesTo_unique hgu hgx
          exact hu ▸ hfu
        exact (ihf hf ht).trans (encode_le_compose_left f g)
      | succ k =>
        obtain ⟨u, hgu, hfu⟩ := convergesTo_compose.mp (h Trace.void)
        have hu : u = deltaIter (k + 1) Trace.void :=
          convergesTo_unique hgu (hk Trace.void)
        have hx : ¬ IsCompound (deltaIter (k + 1) Trace.void) := by
          rw [deltaIter_succ]
          exact not_compound_delta _
        have hf : convergesTo f (deltaIter (k + 1) Trace.void) t := hu ▸ hfu
        have hsz := step_compound_from_atom_conv hf ht hx
        exact hsz.trans (encode_le_compose_left f g)

def restOf : PartialCode → PartialCode
  | .compose (.compose f1 f2) g => .compose (restOf (.compose f1 f2)) g
  | .compose _ g => g
  | .succ => .proj
  | .proj => .proj
  | .call => .proj
  | .diverge => .proj
  | .const _ => .proj

theorem restOf_size_lt_compose (f g : PartialCode) :
    sizeOf (restOf (PartialCode.compose f g)) <
      sizeOf (PartialCode.compose f g) := by
  cases f with
  | compose f1 f2 =>
    have ih := restOf_size_lt_compose f1 f2
    change sizeOf (PartialCode.compose
        (restOf (PartialCode.compose f1 f2)) g) <
      sizeOf (PartialCode.compose (PartialCode.compose f1 f2) g)
    rw [sizeOf_code_compose, sizeOf_code_compose]
    omega
  | succ =>
    change sizeOf g < sizeOf (PartialCode.compose PartialCode.succ g)
    rw [sizeOf_code_compose, sizeOf_code_succ]
    omega
  | proj =>
    change sizeOf g < sizeOf (PartialCode.compose PartialCode.proj g)
    rw [sizeOf_code_compose, sizeOf_code_proj]
    omega
  | call =>
    change sizeOf g < sizeOf (PartialCode.compose PartialCode.call g)
    rw [sizeOf_code_compose, sizeOf_code_call]
    omega
  | diverge =>
    change sizeOf g < sizeOf (PartialCode.compose PartialCode.diverge g)
    rw [sizeOf_code_compose, sizeOf_code_diverge]
    omega
  | const r =>
    change sizeOf g < sizeOf (PartialCode.compose (PartialCode.const r) g)
    rw [sizeOf_code_compose, sizeOf_code_const]
    omega

theorem restOf_leftHead_succ {e : PartialCode} {x t : Trace}
    (hl : leftHead e = .succ) (h : convergesTo e x t) :
    ∃ u, t = Trace.delta u ∧ convergesTo (restOf e) x u := by
  induction e generalizing x t with
  | succ =>
    exact ⟨x, (convergesTo_succ_iff x t).mp h, (convergesTo_proj_iff x x).mpr rfl⟩
  | compose f g ih =>
    simp only [leftHead] at hl
    obtain ⟨w, hgw, hfw⟩ := convergesTo_compose.mp h
    obtain ⟨u, htu, hrest⟩ := ih hl hfw
    cases f with
    | compose f1 f2 =>
      exact ⟨u, htu, convergesTo_compose.mpr ⟨w, hgw, hrest⟩⟩
    | succ =>
      have huw : u = w := (convergesTo_proj_iff w u).mp hrest
      exact ⟨w, huw ▸ htu, hgw⟩
    | diverge => simp [leftHead] at hl
    | proj => simp [leftHead] at hl
    | const _ => simp [leftHead] at hl
    | call => simp [leftHead] at hl
  | diverge => simp [leftHead] at hl
  | proj => simp [leftHead] at hl
  | const _ => simp [leftHead] at hl
  | call => simp [leftHead] at hl

theorem restOf_leftHead_call {e : PartialCode} {x t : Trace}
    (hl : leftHead e = .call) (h : convergesTo e x t) :
    ∃ s, convergesTo (restOf e) x s ∧ convergesTo .call s t := by
  induction e generalizing x t with
  | call =>
    exact ⟨x, (convergesTo_proj_iff x x).mpr rfl, h⟩
  | compose f g ih =>
    simp only [leftHead] at hl
    obtain ⟨w, hgw, hfw⟩ := convergesTo_compose.mp h
    cases f with
    | compose f1 f2 =>
      obtain ⟨s, hrs, hcs⟩ := ih hl hfw
      exact ⟨s, convergesTo_compose.mpr ⟨w, hgw, hrs⟩, hcs⟩
    | call =>
      exact ⟨w, hgw, hfw⟩
    | diverge => simp [leftHead] at hl
    | proj => simp [leftHead] at hl
    | succ => simp [leftHead] at hl
    | const _ => simp [leftHead] at hl
  | diverge => simp [leftHead] at hl
  | proj => simp [leftHead] at hl
  | succ => simp [leftHead] at hl
  | const _ => simp [leftHead] at hl

theorem convergesTo_call_restOf {e : PartialCode} {x t : Trace}
    (hl : leftHead e = .call) :
    convergesTo e x t ↔
      convergesTo (.compose .call (restOf e)) x t := by
  induction e generalizing x t with
  | call =>
    constructor
    · intro h
      exact convergesTo_compose.mpr
        ⟨x, (convergesTo_proj_iff x x).mpr rfl, h⟩
    · intro h
      obtain ⟨u, hpu, hcu⟩ := convergesTo_compose.mp h
      have hu : u = x := (convergesTo_proj_iff x u).mp hpu
      exact hu ▸ hcu
  | compose f g ih =>
    simp only [leftHead] at hl
    cases f with
    | call =>
      constructor <;> intro h <;> exact h
    | compose f1 f2 =>
      constructor
      · intro h
        obtain ⟨w, hgw, hfw⟩ := convergesTo_compose.mp h
        have := (ih hl).mp hfw
        obtain ⟨s, hrs, hcs⟩ := convergesTo_compose.mp this
        exact convergesTo_compose.mpr
          ⟨s, convergesTo_compose.mpr ⟨w, hgw, hrs⟩, hcs⟩
      · intro h
        obtain ⟨s, hrest, hcs⟩ := convergesTo_compose.mp h
        obtain ⟨w, hgw, hrs⟩ := convergesTo_compose.mp hrest
        have hfw := (ih hl).mpr (convergesTo_compose.mpr ⟨s, hrs, hcs⟩)
        exact convergesTo_compose.mpr ⟨w, hgw, hfw⟩
    | diverge => simp [leftHead] at hl
    | proj => simp [leftHead] at hl
    | succ => simp [leftHead] at hl
    | const _ => simp [leftHead] at hl
  | diverge => simp [leftHead] at hl
  | proj => simp [leftHead] at hl
  | succ => simp [leftHead] at hl
  | const _ => simp [leftHead] at hl

theorem sizeOf_encode_call_rest {e : PartialCode}
    (hl : leftHead e = .call) (hc : ∃ f g, e = .compose f g) :
    sizeOf (Trace.app (encode .call) (encode (restOf e))) =
      sizeOf (encode e) := by
  obtain ⟨f, g, he⟩ := hc
  subst he
  simp only [leftHead] at hl
  induction f generalizing g with
  | call =>
    simp [restOf, encode, sizeOf_app]
  | compose f1 f2 ih =>
    simp only [leftHead] at hl
    have ih' := ih f2 hl
    change sizeOf (Trace.app (encode PartialCode.call)
        (encode (PartialCode.compose
          (restOf (PartialCode.compose f1 f2)) g))) =
      sizeOf (encode (PartialCode.compose
        (PartialCode.compose f1 f2) g))
    rw [sizeOf_app, sizeOf_encode_compose, sizeOf_encode_compose]
    rw [sizeOf_app] at ih'
    omega
  | diverge => simp [leftHead] at hl
  | proj => simp [leftHead] at hl
  | succ => simp [leftHead] at hl
  | const _ => simp [leftHead] at hl

theorem encode_restOf_succ_code {f : PartialCode}
    (hl : leftHead f = .succ) (hne : f ≠ .succ) :
    sizeOf (encode (restOf f)) + 4 ≤ sizeOf (encode f) := by
  induction f with
  | succ => exact (hne rfl).elim
  | compose f1 f2 ih1 _ih2 =>
    simp only [leftHead] at hl
    cases f1 with
    | succ =>
      simp [restOf, sizeOf_encode_compose, encode, sizeOf_delta, sizeOf_void]
      omega
    | compose a b =>
      have hne1 : PartialCode.compose a b ≠ .succ := by intro h; cases h
      have hsz := ih1 hl hne1
      simp [restOf, sizeOf_encode_compose] at hsz ⊢
      omega
    | diverge => simp [leftHead] at hl
    | proj => simp [leftHead] at hl
    | const _ => simp [leftHead] at hl
    | call => simp [leftHead] at hl
  | diverge => simp [leftHead] at hl
  | proj => simp [leftHead] at hl
  | const _ => simp [leftHead] at hl
  | call => simp [leftHead] at hl

theorem restOf_leftHead_proj {e : PartialCode} {x t : Trace}
    (hl : leftHead e = .proj) (h : convergesTo e x t) :
    convergesTo (restOf e) x t := by
  induction e generalizing x t with
  | proj => exact h
  | compose f g ih =>
    simp only [leftHead] at hl
    obtain ⟨w, hgw, hfw⟩ := convergesTo_compose.mp h
    cases f with
    | compose f1 f2 =>
      exact convergesTo_compose.mpr ⟨w, hgw, ih hl hfw⟩
    | proj =>
      have hw : t = w := (convergesTo_proj_iff w t).mp hfw
      exact hw ▸ hgw
    | diverge => simp [leftHead] at hl
    | succ => simp [leftHead] at hl
    | const _ => simp [leftHead] at hl
    | call => simp [leftHead] at hl
  | diverge => simp [leftHead] at hl
  | succ => simp [leftHead] at hl
  | const _ => simp [leftHead] at hl
  | call => simp [leftHead] at hl

theorem encode_restOf_compose_le (f g : PartialCode) :
    sizeOf (encode (restOf (.compose f g))) ≤
      sizeOf (encode (.compose f g)) := by
  cases f with
  | compose f1 f2 =>
    have ih := encode_restOf_compose_le f1 f2
    change sizeOf (encode (PartialCode.compose
        (restOf (PartialCode.compose f1 f2)) g)) ≤
      sizeOf (encode (PartialCode.compose (PartialCode.compose f1 f2) g))
    rw [sizeOf_encode_compose, sizeOf_encode_compose]
    omega
  | succ => exact encode_le_compose_right _ _
  | proj => exact encode_le_compose_right _ _
  | call => exact encode_le_compose_right _ _
  | diverge => exact encode_le_compose_right _ _
  | const _ => exact encode_le_compose_right _ _

mutual

theorem constant_avoids_delta_app (e : PartialCode) {tgt : Trace}
    (h : ∀ x, convergesTo e x (Trace.delta tgt))
    (happ : ∃ a b, tgt = Trace.app a b)
    (hle : sizeOf (encode e) ≤ sizeOf tgt) : False := by
  cases hl : leftHead e with
  | const r =>
    have ht : Trace.delta tgt = r := leftHead_const_eval_all hl h
    have hb := encode_of_leftHead_const hl
    rw [← ht, sizeOf_delta] at hb
    omega
  | succ =>
    have h0 := h Trace.void
    have h1 := h (Trace.delta Trace.void)
    cases e with
    | succ =>
      have hv0 : Trace.delta tgt = Trace.delta Trace.void :=
        (convergesTo_succ_iff Trace.void (Trace.delta tgt)).mp h0
      have hv1 : Trace.delta tgt =
          Trace.delta (Trace.delta Trace.void) :=
        (convergesTo_succ_iff (Trace.delta Trace.void)
          (Trace.delta tgt)).mp h1
      injection hv0 with htgt
      rw [htgt] at hv1
      injection hv1 with hbad
      exact nomatch hbad
    | compose f g =>
      obtain ⟨u, htu, hrest⟩ := restOf_leftHead_succ hl (h Trace.void)
      have hu : u = tgt := by
        injection htu with h'
        exact h'.symm
      have hrestall : ∀ x, convergesTo (restOf (.compose f g)) x tgt := by
        intro x
        obtain ⟨u', htu', hr'⟩ := restOf_leftHead_succ hl (h x)
        have : u' = tgt := by
          injection htu' with h'
          exact h'.symm
        exact this ▸ hr'
      obtain ⟨a, b, hab⟩ := happ
      have htcomp : IsCompound tgt := by
        rw [hab]
        exact isCompound_app a b
      have hsz := constant_compound_size hrestall htcomp
      have hne : PartialCode.compose f g ≠ .succ := by intro h'; cases h'
      have hgap := encode_restOf_succ_code hl hne
      omega
    | diverge => simp [leftHead] at hl
    | proj => simp [leftHead] at hl
    | const _ => simp [leftHead] at hl
    | call => simp [leftHead] at hl
  | diverge =>
    have hd := leftHead_diverge_diverges hl Trace.void
    obtain ⟨n, hn⟩ := h Trace.void
    have hnone := hd n
    rw [hnone] at hn
    cases hn
  | compose f g =>
    exact False.elim (leftHead_ne_compose e f g hl)
  | proj =>
    cases he : e with
    | proj =>
      rw [he] at h
      have hv : Trace.delta tgt = Trace.void :=
        (convergesTo_proj_iff Trace.void (Trace.delta tgt)).mp (h Trace.void)
      exact nomatch hv
    | compose f g =>
      have hrest : ∀ x, convergesTo (restOf e) x (Trace.delta tgt) :=
        fun x => restOf_leftHead_proj hl (h x)
      have hle' : sizeOf (encode (restOf e)) ≤ sizeOf tgt := by
        rw [he] at hle ⊢
        exact (encode_restOf_compose_le f g).trans hle
      have hdec : sizeOf (restOf e) < sizeOf e := by
        rw [he]
        exact restOf_size_lt_compose f g
      exact constant_avoids_delta_app (restOf e) hrest happ hle'
    | diverge =>
      rw [he] at hl; cases hl
    | succ =>
      rw [he] at hl; cases hl
    | const _ =>
      rw [he] at hl; cases hl
    | call =>
      rw [he] at hl; cases hl
  | call =>
    cases he : e with
    | call =>
      obtain ⟨n, hn⟩ := h Trace.void
      rw [he] at hn
      have hd := call_diverges_at_void n
      rw [hd] at hn
      cases hn
    | compose f g =>
      have htot : ∀ x, ∃ v,
          convergesTo (.compose .call (restOf e)) x v := by
        intro x
        exact ⟨_, (convergesTo_call_restOf hl).mp (h x)⟩
      have hgtot : ∀ x, ∃ u, convergesTo (restOf e) x u := by
        intro x
        obtain ⟨u, hgu, _⟩ :=
          convergesTo_compose.mp ((convergesTo_call_restOf hl).mp (h x))
        exact ⟨u, hgu⟩
      have hdec : sizeOf (restOf e) < sizeOf e := by
        rw [he]
        exact restOf_size_lt_compose f g
      cases total_const_or_deltaIter (restOf e) hgtot with
      | inr hk =>
        obtain ⟨k, hk⟩ := hk
        exact (compose_call_of_deltaIter_not_total hk htot).elim
      | inl hs =>
        obtain ⟨s, hs⟩ := hs
        obtain ⟨u, hgu, hcu⟩ :=
          convergesTo_compose.mp ((convergesTo_call_restOf hl).mp
            (h Trace.void))
        have hu : u = s := convergesTo_unique hgu (hs Trace.void)
        have hcu' : convergesTo .call s (Trace.delta tgt) := hu ▸ hcu
        have hle' :
            sizeOf (Trace.app (encode .call) (encode (restOf e))) ≤
              sizeOf tgt := by
          have hsz := sizeOf_encode_call_rest hl ⟨f, g, he⟩
          rw [hsz]
          exact hle
        exact call_at_const_avoids hs hcu' happ hle'
    | diverge =>
      rw [he] at hl; cases hl
    | proj =>
      rw [he] at hl; cases hl
    | succ =>
      rw [he] at hl; cases hl
    | const _ =>
      rw [he] at hl; cases hl
termination_by (sizeOf e, (0 : Nat))
decreasing_by
  all_goals (simp_wf; omega)

theorem call_at_const_avoids {g : PartialCode} {s tgt : Trace}
    (hs : ∀ x, convergesTo g x s)
    (hf : convergesTo .call s (Trace.delta tgt))
    (happ : ∃ a b, tgt = Trace.app a b)
    (hle : sizeOf (Trace.app (encode .call) (encode g)) ≤ sizeOf tgt) :
    False := by
  have hself : convergesTo (quote s) s (Trace.delta tgt) :=
    (convergesTo_call_iff s _).mp hf
  cases hq : decode s with
  | none =>
    have hqdiv : quote s = .diverge := by simp [quote, hq]
    obtain ⟨n, hn⟩ := hself
    rw [hqdiv] at hn
    have hd := step_diverge n s
    rw [hd] at hn
    cases hn
  | some c =>
    have henc : encode c = s := encode_of_decode hq
    have hq' : quote s = c := by simp [quote, hq]
    rw [hq'] at hself
    cases c with
    | diverge =>
      obtain ⟨n, hn⟩ := hself
      have hd := step_diverge n s
      rw [hd] at hn
      cases hn
    | proj =>
      have hs' : Trace.delta tgt = s :=
        (convergesTo_proj_iff s (Trace.delta tgt)).mp hself
      have hgs : ∀ x, convergesTo g x (Trace.delta tgt) :=
        fun x => hs'.symm ▸ hs x
      have hle' : sizeOf (encode g) ≤ sizeOf tgt := by
        simp [encode, sizeOf_app, sizeOf_delta, sizeOf_void] at hle
        omega
      exact constant_avoids_delta_app g hgs happ hle'
    | succ =>
      have hs' : s = tgt := by
        have ht' : Trace.delta tgt = Trace.delta s :=
          (convergesTo_succ_iff s (Trace.delta tgt)).mp hself
        injection ht' with hxy
        exact hxy.symm
      obtain ⟨a, b, hab⟩ := happ
      have htcomp : IsCompound s := by
        rw [hs', hab]
        exact isCompound_app a b
      have hsz := constant_compound_size (t := s) hs htcomp
      rw [hs'] at hsz
      simp [encode, sizeOf_app, sizeOf_delta, sizeOf_void,
        sizeOf_encode_call] at hle hsz
      omega
    | const r =>
      have hr : Trace.delta tgt = r :=
        (convergesTo_const_iff r s (Trace.delta tgt)).mp hself
      subst hr
      have hsmerge : s = Trace.merge Trace.void (Trace.delta tgt) := by
        simp [encode] at henc
        exact henc.symm
      have htcomp : IsCompound s := by
        rw [hsmerge]
        exact isCompound_merge _ _
      have hsz := constant_compound_size (t := s) hs htcomp
      rw [hsmerge, sizeOf_merge, sizeOf_void, sizeOf_delta] at hsz
      simp [encode, sizeOf_app, sizeOf_delta, sizeOf_void,
        sizeOf_encode_call] at hle
      omega
    | call =>
      have hs' : s = encode .call := by
        simp [encode] at henc
        exact henc.symm
      rw [hs'] at hself
      obtain ⟨n, hn⟩ := hself
      have hd := call_diverges_at_own_code n
      rw [hd] at hn
      cases hn
    | compose c1 c2 =>
      have hsapp : s = encode (.compose c1 c2) := henc.symm
      subst hsapp
      have htcomp : IsCompound (encode (.compose c1 c2)) := by
        simp [encode]
        exact isCompound_app _ _
      have hsz := constant_compound_size (t := encode (.compose c1 c2))
        hs htcomp
      have hown := own_delta_app_le (c := .compose c1 c2) hself happ
      simp [encode, sizeOf_app, sizeOf_encode_compose, sizeOf_encode_call,
        sizeOf_delta, sizeOf_void] at hle hsz hown
      omega
termination_by (sizeOf g, (1 : Nat))
decreasing_by
  all_goals (simp_wf; omega)

end

theorem constant_avoids_own_encode (e : PartialCode) {t : Trace}
    (h : ∀ x, convergesTo e x t) : t ≠ Trace.delta (encode e) := by
  intro heq
  subst heq
  cases e with
  | diverge =>
    obtain ⟨n, hn⟩ := h Trace.void
    rw [step_diverge] at hn
    cases hn
  | proj =>
    have hv : Trace.delta (encode .proj) = Trace.void :=
      (convergesTo_proj_iff Trace.void (Trace.delta (encode .proj))).mp
        (h Trace.void)
    exact Trace.noConfusion hv
  | succ =>
    have h0 := (convergesTo_succ_iff Trace.void _).mp (h Trace.void)
    have h1 := (convergesTo_succ_iff (Trace.delta Trace.void) _).mp
      (h (Trace.delta Trace.void))
    injection (h0.symm.trans h1) with h'
    exact Trace.noConfusion h'
  | const r =>
    have hr : Trace.delta (encode (.const r)) = r :=
      (convergesTo_const_iff r Trace.void _).mp (h Trace.void)
    exact ne_delta_merge_void_self r hr.symm
  | call =>
    obtain ⟨n, hn⟩ := h Trace.void
    have hd := call_diverges_at_void n
    rw [hd] at hn
    cases hn
  | compose f g =>
    exact constant_avoids_delta_app (.compose f g) h
      ⟨encode f, encode g, by simp [encode]⟩ le_rfl

theorem not_constantly_delta_encode (e : PartialCode) :
    ¬ ∀ x, convergesTo e x (Trace.delta (encode e)) := by
  intro h
  exact constant_avoids_own_encode e h rfl


/-! ## Generated operators: left composition vs freeze-succ -/

def freezeSuccOp (c : PartialCode) : PartialCode :=
  freezeSubst .succ (encode c)

theorem freezeSuccOp_beh (c : PartialCode) (y v : Trace) :
    convergesTo (freezeSuccOp c) y v ↔ v = Trace.delta (encode c) := by
  constructor
  · intro h
    have h' := freezeSubst_tracks.mp h
    exact (convergesTo_succ_iff (encode c) v).mp h'
  · intro hv
    subst hv
    exact freezeSubst_tracks.mpr ⟨1, rfl⟩

/-- Kill: freeze-substitution of successor, as an operator on codes, has
no extensional fixed point. -/
theorem freeze_succ_operator_has_no_extensional_fp :
    ¬ ∃ e, BehEq e (freezeSuccOp e) := by
  rintro ⟨e, h⟩
  have hconst : ∀ x, convergesTo e x (Trace.delta (encode e)) := by
    intro x
    exact (h x (Trace.delta (encode e))).mpr
      ((freezeSuccOp_beh e x (Trace.delta (encode e))).mpr rfl)
  exact not_constantly_delta_encode e hconst

inductive LeftComposeOp : (PartialCode → PartialCode) → Prop
  | succ : LeftComposeOp (fun c => .compose .succ c)
  | proj : LeftComposeOp (fun c => .compose .proj c)
  | const (t : Trace) : LeftComposeOp (fun c => .compose (.const t) c)
  | diverge : LeftComposeOp (fun c => .compose .diverge c)

theorem compose_diverge_diverge_beh :
    BehEq .diverge (.compose .diverge .diverge) :=
  BehEq_of_everywhere_diverge diverges_diverge
    (fun x => compose_diverge_left_diverges .diverge x)

theorem left_compose_op_has_extensional_fp {F : PartialCode → PartialCode}
    (h : LeftComposeOp F) : ∃ e, BehEq e (F e) := by
  cases h with
  | succ => exact ⟨.diverge, second_recursion_form_left_succ_beh⟩
  | proj => exact ⟨.proj, second_recursion_form_proj⟩
  | const t => exact ⟨.const t, second_recursion_form_const t⟩
  | diverge => exact ⟨.diverge, compose_diverge_diverge_beh⟩

theorem live_succ_op_is_left_succ (c : PartialCode) :
    liveSubst .succ (encode c) = .compose .succ c := by
  simp [liveSubst, quote_encode]

theorem live_succ_operator_has_extensional_fp :
    ∃ e, BehEq e (liveSubst .succ (encode e)) := by
  refine ⟨.diverge, ?_⟩
  rw [live_succ_op_is_left_succ]
  exact second_recursion_form_left_succ_beh

/-- Duck: live substitution of successor is left-succ and has an
extensional FP; freeze substitution of successor has none. -/
theorem live_succ_has_fp_freeze_succ_does_not :
    (∃ e, BehEq e (liveSubst .succ (encode e))) ∧
      ¬ ∃ e, BehEq e (freezeSuccOp e) :=
  ⟨live_succ_operator_has_extensional_fp,
    freeze_succ_operator_has_no_extensional_fp⟩

theorem generated_op_fp_characterization :
    (∀ F, LeftComposeOp F → ∃ e, BehEq e (F e)) ∧
      ¬ ∃ e, BehEq e (freezeSuccOp e) :=
  ⟨fun _ h => left_compose_op_has_extensional_fp h,
    freeze_succ_operator_has_no_extensional_fp⟩

inductive GeneratedOp : (PartialCode → PartialCode) → Prop
  | left {F : PartialCode → PartialCode} : LeftComposeOp F → GeneratedOp F
  | freezeSucc : GeneratedOp freezeSuccOp

theorem generated_op_fp_split :
    (∀ F, GeneratedOp F → LeftComposeOp F → ∃ e, BehEq e (F e)) ∧
      GeneratedOp freezeSuccOp ∧ ¬ ∃ e, BehEq e (freezeSuccOp e) :=
  ⟨fun _ _ h => left_compose_op_has_extensional_fp h,
    GeneratedOp.freezeSucc, freeze_succ_operator_has_no_extensional_fp⟩

/-! ## Quote freeze coupling (Problem freeze) -/

theorem stale_decode_quote_behaviours_do_not_join :
    convergesTo (quote (Trace.merge Trace.void Trace.void)) Trace.void
        Trace.void ∧
      diverges (quote Trace.void) Trace.void ∧
      EqGuardedStep (Trace.merge Trace.void Trace.void) Trace.void :=
  ⟨⟨1, rfl⟩, diverges_diverge Trace.void,
    EqGuardedStep.R_merge_void_left Trace.void⟩

theorem Ctor_is_seven (c : Ctor) :
    c = .void ∨ c = .delta ∨ c = .integrate ∨ c = .merge ∨ c = .app ∨
      c = .recD ∨ c = .eqW := by
  cases c with
  | void => exact Or.inl rfl
  | delta => exact Or.inr (Or.inl rfl)
  | integrate => exact Or.inr (Or.inr (Or.inl rfl))
  | merge => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | app => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | recD => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | eqW => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

theorem quote_not_a_kernel_constructor (c : Ctor) :
    c = .void ∨ c = .delta ∨ c = .integrate ∨ c = .merge ∨ c = .app ∨
      c = .recD ∨ c = .eqW :=
  Ctor_is_seven c

/-- The compiled freeze characterization has no quotation slot. -/
theorem freeze_characterization_has_no_quote_slot (S : Ctor → Prop) :
    (ConfluentOn S EqGuardedStep ↔
      (¬ S Ctor.eqW ∧ (S Ctor.recD → S Ctor.app))) ∧
      ∀ c : Ctor,
        c = .void ∨ c = .delta ∨ c = .integrate ∨ c = .merge ∨ c = .app ∨
          c = .recD ∨ c = .eqW :=
  ⟨confluentOn_eqGuarded_iff S, Ctor_is_seven⟩

/-- The `{eqW}` freeze restores kernel confluence and does not stabilize
decode-quote: merge still reduces, and the two quotations differ. -/
theorem eqW_freeze_does_not_stabilize_quote :
    ConfluentOn (fun c : Ctor => c ≠ Ctor.eqW) EqGuardedStep ∧
      quote (Trace.merge Trace.void Trace.void) ≠ quote Trace.void ∧
      EqGuardedStep (Trace.merge Trace.void Trace.void) Trace.void :=
  ⟨fullMinusEqW_confluent, fun h =>
      (PartialCode.noConfusion
        (quote_merge_void_void.symm.trans (h.trans quote_void_eq_diverge)) :
        False),
    EqGuardedStep.R_merge_void_left Trace.void⟩

theorem quote_freeze_coupling :
    convergesTo (quote (Trace.merge Trace.void Trace.void)) Trace.void
        Trace.void ∧
      diverges (quote Trace.void) Trace.void ∧
      ConfluentOn (fun c : Ctor => c ≠ Ctor.eqW) EqGuardedStep ∧
      ¬ ConfluentOn (fun _ : Ctor => True) EqGuardedStep :=
  ⟨⟨1, rfl⟩, diverges_diverge Trace.void, fullMinusEqW_confluent,
    fullThaw_not_confluent⟩

/-! ## Rank transport through quotation (Problem rank) -/

def quoteTransportState (_c : PartialCode) : MetaQueryState where
  metaState := 0
  activeQuery := 0
  obligations := ({0} : Multiset Obligation)
  budget := 1

theorem quote_rank_transport_preserves_rank (c d : PartialCode) :
    rank (quoteTransportState c) = rank (quoteTransportState d) :=
  rfl

theorem quote_self_representability_identity_blocked (c : PartialCode) :
    ¬ ReflectiveStep (quoteTransportState c) (quoteTransportState c) :=
  identity_reflective_pair_blocked (quoteTransportState c)

theorem quote_self_representability_cycle_blocked (c : PartialCode) :
    ¬ Relation.TransGen ReflectiveStep (quoteTransportState c)
      (quoteTransportState c) :=
  fun h => mutual_reflective_cycle_requires_descent h

theorem quote_justification_rank_is_wf : WellFounded RankLT :=
  wf_RankLT

/-- Using a code to license that same code's representability is an
identity step on the transported rank, hence refused. -/
theorem quote_self_license_is_refused (c : PartialCode) :
    ¬ ReflectiveStep (quoteTransportState c) (quoteTransportState c) ∧
      WellFounded RankLT :=
  ⟨quote_self_representability_identity_blocked c, wf_RankLT⟩

end OperatorKO7.Meta.DistinctionBoundary.GodelPartial
