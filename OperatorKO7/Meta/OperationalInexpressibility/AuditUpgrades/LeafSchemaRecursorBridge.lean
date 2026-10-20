import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorContext
import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorWitnessOrder

/-!
# Trace law of the free recursor under the context closure

Proves: for normal terms `a`, `b` and a counter depth `k`, the stage terms
`t_i = G^i(b, F(a, b, S^(k-i)(0)))` and the record `G^k(b, a)` form the only maximal rewrite
sequence of the context-closed relation `R_ctx` from `t_0`; it has `k + 1` steps, and from stage
`i` the remaining maximal derivation has `k - i + 1` steps. Along the spine, the counter of the
active site reads `k - i`, the frame count reads `i` and the count of payload slots holding `b`
reads `i + 1`. The counter and the frame count are invariant under every relabelling of the
payload slots; the counter decreases along the trace, the frame count increases, and the
payload count changes under a relabelling.
Relation: `FreeRecursorContext.Step`, root rules closed under every one-hole context.
Closure: context closure; maximal finite sequences.
Strategy: full.
Trust: kernel-only.
Scope: `a` and `b` normal for `R_ctx`; arbitrary otherwise.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.LeafSchemaRecursorBridge

open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorContext
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorWitnessOrder

/-- The context-closed step relation of the free recursor. -/
abbrev CtxStep : RecursorTerm → RecursorTerm → Prop :=
  OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorContext.Step

/-- One-hole contexts of the free syntax. -/
abbrev Ctx : Type := OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorContext.Context

/-- Normal form for the context-closed relation. -/
def Normal (t : RecursorTerm) : Prop := ∀ u, ¬ CtxStep t u

/-- `i` wrapper frames `G(b, ·)` above a term. -/
def wrap (b : RecursorTerm) : Nat → RecursorTerm → RecursorTerm
  | 0, t => t
  | i + 1, t => .app b (wrap b i t)

/-- Stage `i` of the trace from `F(a, b, S^k(0))`. -/
def stage (a b : RecursorTerm) (k i : Nat) : RecursorTerm :=
  wrap b i (.recR a b (counterTerm (k - i)))

/-- The terminal record `G^k(b, a)`. -/
def record (a b : RecursorTerm) (k : Nat) : RecursorTerm :=
  wrap b k a

/-! ## Inversion of the context-closed step -/

theorem step_exists {s u : RecursorTerm} (h : CtxStep s u) :
    ∃ (C : Ctx) (x y : RecursorTerm), FreeRecursorStep x y ∧ s = C.fill x ∧ u = C.fill y := by
  cases h with
  | inContext C hs => exact ⟨C, _, _, hs, rfl, rfl⟩

/-- A step from a frame with a normal left slot happens in its right argument. -/
theorem step_app_inv {x t u : RecursorTerm} (hx : Normal x) (h : CtxStep (.app x t) u) :
    ∃ t', u = .app x t' ∧ CtxStep t t' := by
  obtain ⟨C, p, q, hs, hsx, rfl⟩ := step_exists h
  cases C with
  | hole =>
    simp only [FreeRecursorContext.Context.fill] at hsx
    subst hsx
    cases hs
  | appLeft C b' =>
    simp only [FreeRecursorContext.Context.fill] at hsx
    injection hsx with h1 h2
    have hstep : CtxStep x (C.fill q) := by rw [h1]; exact FreeRecursorContext.Step.inContext C hs
    exact (hx _ hstep).elim
  | appRight a' C =>
    simp only [FreeRecursorContext.Context.fill] at hsx
    injection hsx with h1 h2
    refine ⟨C.fill q, ?_, ?_⟩
    · simp only [FreeRecursorContext.Context.fill, h1]
    · rw [h2]; exact FreeRecursorContext.Step.inContext C hs
  | delta C => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx
  | integrate C => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx
  | mergeLeft C b' => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx
  | mergeRight a' C => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx
  | eqLeft C b' => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx
  | eqRight a' C => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx
  | recBase C s n => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx
  | recPayload b' C n => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx
  | recCounter b' s C => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx

/-- A step from a recursor site with normal arguments is a root step. -/
theorem step_recR_inv {a b n u : RecursorTerm} (ha : Normal a) (hb : Normal b) (hn : Normal n)
    (h : CtxStep (.recR a b n) u) : FreeRecursorStep (.recR a b n) u := by
  obtain ⟨C, p, q, hs, hsx, rfl⟩ := step_exists h
  cases C with
  | hole =>
    simp only [FreeRecursorContext.Context.fill] at hsx ⊢
    subst hsx
    exact hs
  | recBase C s n' =>
    simp only [FreeRecursorContext.Context.fill] at hsx
    injection hsx with h1 h2 h3
    have hstep : CtxStep a (C.fill q) := by rw [h1]; exact FreeRecursorContext.Step.inContext C hs
    exact (ha _ hstep).elim
  | recPayload b' C n' =>
    simp only [FreeRecursorContext.Context.fill] at hsx
    injection hsx with h1 h2 h3
    have hstep : CtxStep b (C.fill q) := by rw [h2]; exact FreeRecursorContext.Step.inContext C hs
    exact (hb _ hstep).elim
  | recCounter b' s C =>
    simp only [FreeRecursorContext.Context.fill] at hsx
    injection hsx with h1 h2 h3
    have hstep : CtxStep n (C.fill q) := by rw [h3]; exact FreeRecursorContext.Step.inContext C hs
    exact (hn _ hstep).elim
  | delta C => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx
  | integrate C => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx
  | mergeLeft C b' => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx
  | mergeRight a' C => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx
  | appLeft C b' => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx
  | appRight a' C => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx
  | eqLeft C b' => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx
  | eqRight a' C => simp only [FreeRecursorContext.Context.fill] at hsx; cases hsx

theorem normalize_counterTerm (m : Nat) : FreeRecursorContext.normalize (counterTerm m) = counterTerm m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [counterTerm, FreeRecursorContext.normalize, ih]

theorem counterTerm_normal (m : Nat) : Normal (counterTerm m) :=
  (freeRecursor_ctx_normal_iff_fixed _).2 (normalize_counterTerm m)

/-! ## Steps of the stage terms -/

theorem step_wrap_iff {b : RecursorTerm} (hb : Normal b) (i : Nat) (t : RecursorTerm) :
    ∀ u, CtxStep (wrap b i t) u ↔ ∃ t', u = wrap b i t' ∧ CtxStep t t' := by
  induction i with
  | zero =>
    intro u
    simp only [wrap]
    exact ⟨fun h => ⟨u, rfl, h⟩, fun ⟨t', hu, h⟩ => by subst hu; exact h⟩
  | succ i ih =>
    intro u
    simp only [wrap]
    constructor
    · intro h
      obtain ⟨t'', rfl, h''⟩ := step_app_inv hb h
      obtain ⟨t', rfl, h'⟩ := (ih t'').1 h''
      exact ⟨t', rfl, h'⟩
    · rintro ⟨t', rfl, h'⟩
      have hin := FreeRecursorContext.step_in_context ((ih _).2 ⟨t', rfl, h'⟩) (.appRight b .hole)
      simpa only [FreeRecursorContext.Context.fill] using hin

theorem wrap_app (b : RecursorTerm) (i : Nat) (t : RecursorTerm) :
    wrap b i (.app b t) = wrap b (i + 1) t := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [wrap] at ih ⊢; rw [ih]

theorem site_step_succ_iff {a b : RecursorTerm} (ha : Normal a) (hb : Normal b) (m : Nat)
    (u : RecursorTerm) :
    CtxStep (.recR a b (counterTerm (m + 1))) u ↔ u = .app b (.recR a b (counterTerm m)) := by
  constructor
  · intro h
    have hr := step_recR_inv ha hb (counterTerm_normal (m + 1)) h
    simp only [counterTerm] at hr
    cases hr
    rfl
  · rintro rfl
    exact FreeRecursorContext.root_step (.succ a b (counterTerm m))

theorem site_step_zero_iff {a b : RecursorTerm} (ha : Normal a) (hb : Normal b)
    (u : RecursorTerm) :
    CtxStep (.recR a b .void) u ↔ u = a := by
  constructor
  · intro h
    have hr := step_recR_inv ha hb (counterTerm_normal 0) h
    cases hr
    rfl
  · intro hu
    rw [hu]
    exact FreeRecursorContext.root_step (.zero a b)

/-- Each live stage below the last has exactly one reduct, the next stage. -/
theorem stage_step_iff {a b : RecursorTerm} (ha : Normal a) (hb : Normal b) {k i : Nat}
    (hi : i < k) (u : RecursorTerm) :
    CtxStep (stage a b k i) u ↔ u = stage a b k (i + 1) := by
  have hk : k - i = (k - (i + 1)) + 1 := by omega
  unfold stage
  rw [hk, step_wrap_iff hb]
  constructor
  · rintro ⟨t', rfl, h'⟩
    rw [(site_step_succ_iff ha hb _ _).1 h', wrap_app]
  · rintro rfl
    exact ⟨_, (wrap_app b i _).symm, (site_step_succ_iff ha hb _ _).2 rfl⟩

/-- The last live stage has exactly one reduct, the terminal record. -/
theorem stage_last_step_iff {a b : RecursorTerm} (ha : Normal a) (hb : Normal b) (k : Nat)
    (u : RecursorTerm) :
    CtxStep (stage a b k k) u ↔ u = record a b k := by
  unfold stage record
  rw [Nat.sub_self, step_wrap_iff hb]
  constructor
  · rintro ⟨t', rfl, h'⟩
    rw [(site_step_zero_iff ha hb _).1 h']
  · rintro rfl
    exact ⟨a, rfl, (site_step_zero_iff ha hb _).2 rfl⟩

/-- The terminal record is normal. -/
theorem record_normal {a b : RecursorTerm} (ha : Normal a) (hb : Normal b) (k : Nat) :
    Normal (record a b k) := by
  intro u h
  obtain ⟨t', _, h'⟩ := (step_wrap_iff hb k a u).1 h
  exact ha _ h'

/-- Every live stage has a reduct. -/
theorem stage_not_normal {a b : RecursorTerm} (ha : Normal a) (hb : Normal b) {k i : Nat}
    (hi : i ≤ k) : ¬ Normal (stage a b k i) := by
  intro hn
  rcases Nat.lt_or_ge i k with hlt | hge
  · exact hn _ ((stage_step_iff ha hb hlt _).2 rfl)
  · have hik : i = k := by omega
    subst hik
    exact hn _ ((stage_last_step_iff ha hb i _).2 rfl)

/-! ## The unique maximal derivation -/

/-- Trace law under the context closure: from stage `i`, every maximal derivation follows the
stages, ends at the terminal record, and has `k - i + 1` steps. -/
theorem trace_from_stage {a b : RecursorTerm} (ha : Normal a) (hb : Normal b) {k i : Nat}
    (hi : i ≤ k) (f : Nat → RecursorTerm) (L : Nat) (h0 : f 0 = stage a b k i)
    (hstep : ∀ j < L, CtxStep (f j) (f (j + 1))) (hmax : Normal (f L)) :
    L = k - i + 1 ∧ (∀ j, i + j ≤ k → f j = stage a b k (i + j)) ∧
      f (k - i + 1) = record a b k := by
  have claim : ∀ j, i + j ≤ k → j ≤ L → f j = stage a b k (i + j) := by
    intro j
    induction j with
    | zero => intro _ _; simpa using h0
    | succ j ih =>
      intro hj hjL
      have hprev := ih (by omega) (by omega)
      have hs := hstep j (by omega)
      rw [hprev] at hs
      have hnext := (stage_step_iff ha hb (show i + j < k by omega) _).1 hs
      rw [hnext, Nat.add_assoc]
  have hL1 : k - i + 1 ≤ L := by
    by_contra hcon
    have hle : L ≤ k - i := by omega
    have hfL := claim L (by omega) le_rfl
    rw [hfL] at hmax
    exact stage_not_normal ha hb (show i + L ≤ k by omega) hmax
  have hlast : f (k - i) = stage a b k k := by
    rw [claim (k - i) (by omega) (by omega)]
    congr 1
    omega
  have hrec : f (k - i + 1) = record a b k := by
    have hs := hstep (k - i) (by omega)
    rw [hlast] at hs
    exact (stage_last_step_iff ha hb k _).1 hs
  refine ⟨?_, fun j hj => claim j hj (by omega), hrec⟩
  by_contra hne
  have hs := hstep (k - i + 1) (by omega)
  rw [hrec] at hs
  exact record_normal ha hb k _ hs

/-- Trace law from `F(a, b, S^k(0))`: the unique maximal derivation has `k + 1` steps. -/
theorem trace_law_ctx {a b : RecursorTerm} (ha : Normal a) (hb : Normal b) (k : Nat)
    (f : Nat → RecursorTerm) (L : Nat) (h0 : f 0 = .recR a b (counterTerm k))
    (hstep : ∀ j < L, CtxStep (f j) (f (j + 1))) (hmax : Normal (f L)) :
    L = k + 1 ∧ (∀ j, j ≤ k → f j = stage a b k j) ∧ f (k + 1) = record a b k := by
  have h0' : f 0 = stage a b k 0 := by simpa [stage, wrap] using h0
  obtain ⟨hL, hst, hr⟩ := trace_from_stage ha hb (Nat.zero_le k) f L h0' hstep hmax
  refine ⟨by simpa using hL, fun j hj => by simpa using hst j (by simpa using hj), by simpa using hr⟩

/-- The stage sequence with the record appended is a maximal derivation. -/
theorem trace_is_derivation {a b : RecursorTerm} (ha : Normal a) (hb : Normal b) (k : Nat) :
    (∀ i < k, CtxStep (stage a b k i) (stage a b k (i + 1))) ∧
      CtxStep (stage a b k k) (record a b k) ∧ Normal (record a b k) :=
  ⟨fun _ hi => (stage_step_iff ha hb hi _).2 rfl, (stage_last_step_iff ha hb k _).2 rfl,
    record_normal ha hb k⟩

/-! ## Readings along the spine -/

/-- Counter of the active site: the successor depth of the third argument under the frames. -/
def spineCounter : RecursorTerm → Nat
  | .app _ t => spineCounter t
  | .recR _ _ n => FreeRecursorKernel.deltaPrefix n
  | _ => 0

/-- Number of wrapper frames on the spine. -/
def spineFrames : RecursorTerm → Nat
  | .app _ t => spineFrames t + 1
  | _ => 0

/-- Number of payload slots on the spine holding `b`: frame slots and the active site's slot. -/
def spinePayload (b : RecursorTerm) : RecursorTerm → Nat
  | .app x t => (if x = b then 1 else 0) + spinePayload b t
  | .recR _ s _ => if s = b then 1 else 0
  | _ => 0

theorem spineCounter_wrap (b : RecursorTerm) (i : Nat) (t : RecursorTerm) :
    spineCounter (wrap b i t) = spineCounter t := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [wrap, spineCounter] using ih

theorem spineFrames_wrap (b : RecursorTerm) (i : Nat) (t : RecursorTerm) :
    spineFrames (wrap b i t) = i + spineFrames t := by
  induction i with
  | zero => simp [wrap]
  | succ i ih => simp only [wrap, spineFrames, ih]; omega

theorem spinePayload_wrap (b : RecursorTerm) (i : Nat) (t : RecursorTerm) :
    spinePayload b (wrap b i t) = i + spinePayload b t := by
  induction i with
  | zero => simp [wrap]
  | succ i ih => simp only [wrap, spinePayload, ih, if_true]; omega

theorem stage_counter (a b : RecursorTerm) (k i : Nat) :
    spineCounter (stage a b k i) = k - i := by
  simp [stage, spineCounter_wrap, spineCounter, FreeRecursorWitnessOrder.deltaPrefix_counterTerm]

theorem stage_frames (a b : RecursorTerm) (k i : Nat) : spineFrames (stage a b k i) = i := by
  simp [stage, spineFrames_wrap, spineFrames]

theorem stage_payload (a b : RecursorTerm) (k i : Nat) :
    spinePayload b (stage a b k i) = i + 1 := by
  simp [stage, spinePayload_wrap, spinePayload]

/-- Offset law on the live stages: payload slots exceed frames by one. -/
theorem stage_offset (a b : RecursorTerm) (k i : Nat) :
    spinePayload b (stage a b k i) = spineFrames (stage a b k i) + 1 := by
  rw [stage_payload, stage_frames]

/-- Counter plus frames is the depth on every live stage. -/
theorem stage_counter_add_frames (a b : RecursorTerm) {k i : Nat} (hi : i ≤ k) :
    spineCounter (stage a b k i) + spineFrames (stage a b k i) = k := by
  rw [stage_counter, stage_frames]; omega

theorem record_frames (a b : RecursorTerm) (k : Nat) :
    spineFrames (record a b k) = k + spineFrames a := spineFrames_wrap b k a

theorem record_payload (a b : RecursorTerm) (k : Nat) :
    spinePayload b (record a b k) = k + spinePayload b a := spinePayload_wrap b k a

/-- With a base that carries neither a frame nor a payload slot on its spine, the record has
`k` frames and `k` payload slots holding `b`. -/
theorem record_counts_of_bare_base (a b : RecursorTerm) (k : Nat) (h1 : spineFrames a = 0)
    (h2 : spinePayload b a = 0) :
    spineFrames (record a b k) = k ∧ spinePayload b (record a b k) = k := by
  rw [record_frames, record_payload, h1, h2]; omega

/-- Residual work: from stage `i` the maximal derivation has `ctr(t_i) + 1` steps. -/
theorem residual_work_eq_counter_succ {a b : RecursorTerm} (ha : Normal a) (hb : Normal b)
    {k i : Nat} (hi : i ≤ k) (f : Nat → RecursorTerm) (L : Nat) (h0 : f 0 = stage a b k i)
    (hstep : ∀ j < L, CtxStep (f j) (f (j + 1))) (hmax : Normal (f L)) :
    L = spineCounter (stage a b k i) + 1 := by
  rw [stage_counter]
  exact (trace_from_stage ha hb hi f L h0 hstep hmax).1

/-! ## Relabelling the payload slots -/

/-- Replace the payload slots along the spine by the values of `f`, in order. -/
def relabelSpine : (Nat → RecursorTerm) → RecursorTerm → RecursorTerm
  | f, .app _ t => .app (f 0) (relabelSpine (fun j => f (j + 1)) t)
  | f, .recR a _ n => .recR a (f 0) n
  | _, t => t

theorem spineCounter_relabel (f : Nat → RecursorTerm) (t : RecursorTerm) :
    spineCounter (relabelSpine f t) = spineCounter t := by
  induction t generalizing f with
  | app x t _ iht => exact iht _
  | recR a s n _ _ _ => rfl
  | void => rfl
  | delta t _ => rfl
  | integrate t _ => rfl
  | merge x y _ _ => rfl
  | eqWit x y _ _ => rfl

theorem spineFrames_relabel (f : Nat → RecursorTerm) (t : RecursorTerm) :
    spineFrames (relabelSpine f t) = spineFrames t := by
  induction t generalizing f with
  | app x t _ iht => exact congrArg (· + 1) (iht _)
  | recR a s n _ _ _ => rfl
  | void => rfl
  | delta t _ => rfl
  | integrate t _ => rfl
  | merge x y _ _ => rfl
  | eqWit x y _ _ => rfl

theorem spinePayload_relabel_const_wrap (b c : RecursorTerm) (hcb : c ≠ b) (i : Nat)
    (t : RecursorTerm) :
    spinePayload b (relabelSpine (fun _ => c) (wrap b i t)) =
      spinePayload b (relabelSpine (fun _ => c) t) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show (if c = b then 1 else 0) + spinePayload b (relabelSpine (fun _ => c) (wrap b i t)) = _
    rw [if_neg hcb, ih, Nat.zero_add]

/-- Relabelling every payload slot with a term different from `b` empties the payload count. -/
theorem stage_payload_relabel_const (a b c : RecursorTerm) (hcb : c ≠ b) (k i : Nat) :
    spinePayload b (relabelSpine (fun _ => c) (stage a b k i)) = 0 := by
  unfold stage
  rw [spinePayload_relabel_const_wrap b c hcb]
  show (if c = b then 1 else 0) = 0
  rw [if_neg hcb]

/-- Among the counter, the frame count and the payload count, the counter is the coordinate
that is invariant under every relabelling of the payload slots and decreases along the trace:
the frame count is invariant and increases, and the payload count increases and changes under a
relabelling. -/
theorem counter_unique_relabelInvariant_decreasing (a b : RecursorTerm) {k i : Nat}
    (hi : i < k) :
    ((∀ f, spineCounter (relabelSpine f (stage a b k i)) = spineCounter (stage a b k i)) ∧
      spineCounter (stage a b k (i + 1)) < spineCounter (stage a b k i)) ∧
    ((∀ f, spineFrames (relabelSpine f (stage a b k i)) = spineFrames (stage a b k i)) ∧
      spineFrames (stage a b k i) < spineFrames (stage a b k (i + 1))) ∧
    ((∃ f, spinePayload b (relabelSpine f (stage a b k i)) ≠ spinePayload b (stage a b k i)) ∧
      spinePayload b (stage a b k i) < spinePayload b (stage a b k (i + 1))) := by
  refine ⟨⟨fun f => spineCounter_relabel f _, ?_⟩, ⟨fun f => spineFrames_relabel f _, ?_⟩, ?_, ?_⟩
  · rw [stage_counter, stage_counter]; omega
  · rw [stage_frames, stage_frames]; omega
  · let c : RecursorTerm := if b = .void then .delta .void else .void
    have hcb : c ≠ b := by
      by_cases hb : b = .void
      · simp only [c, if_pos hb, hb]; exact fun h => RecursorTerm.noConfusion h
      · simp only [c, if_neg hb]; exact fun h => hb h.symm
    refine ⟨fun _ => c, ?_⟩
    rw [stage_payload_relabel_const a b c hcb, stage_payload]
    omega
  · rw [stage_payload, stage_payload]; omega

end OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.LeafSchemaRecursorBridge
