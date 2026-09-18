import OperatorKO7.Meta.DistinctionBoundary.GodelPartial
import OperatorKO7.Meta.DistinctionBoundary.GodelPartialClosure

set_option autoImplicit false
set_option maxHeartbeats 400000

/-!
# Acceptability of the partial numbering (ROADMAP-12 §10.1.1)

The finite combinator numbering is not acceptable: it has no universal
interpreter. Left composition by an arbitrary code still has an
extensional fixed point (the everywhere-divergent code). Freeze-succ is
not an effective index transformer, which is why it can fail to have a
fixed point without contradicting Kleene.

A small relative interpreter extension adds combinators `apply` and `cons`.
`apply` interprets embedded `PartialCode` programs supplied in an `app` pair;
`cons` constructs that pair.  This is **not** an acceptable numbering of the
full `AccCode` carrier and does not prove a full s-m-n theorem for `AccCode`.
Freeze-succ remains non-effective on the embedded old carrier.

NameGate: no `goedel_first`, no `incompleteness`, no `feferman_completeness`.
Do not call the unrestricted left-compose fixed point a general Kleene SRT.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelPartial

open OperatorKO7

def pairArg (e : PartialCode) (x : Trace) : Trace :=
  Trace.app (encode e) x

def IsUniversal (U : PartialCode) : Prop :=
  ∀ e x v, convergesTo U (pairArg e x) v ↔ convergesTo e x v

def EffectiveTransformer (F : PartialCode → PartialCode) : Prop :=
  ∃ f : PartialCode, ∀ c, convergesTo f (encode c) (encode (F c))

def HasInternalSMN (S : PartialCode) : Prop :=
  ∀ e x, convergesTo S (pairArg e x) (encode (freezeSubst e x))

structure AcceptableNumbering : Prop where
  universal : ∃ U, IsUniversal U
  smn : ∃ S, HasInternalSMN S

def pairProj : Trace := pairArg .proj Trace.void

def pairSucc : Trace := pairArg .succ Trace.void

def rightSpine : PartialCode → Nat
  | .compose _ g => rightSpine g + 1
  | _ => 0

theorem compose_right_diverge_diverges (f : PartialCode) (x : Trace) :
    diverges (.compose f .diverge) x := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    have hd : step n .diverge x = none := step_diverge n x
    change (step n .diverge x).bind (step n f) = none
    rw [hd]
    rfl

theorem not_convergesTo_of_diverges {c : PartialCode} {x v : Trace}
    (h : diverges c x) : ¬ convergesTo c x v := by
  rintro ⟨n, hn⟩
  have := h n
  rw [this] at hn
  cases hn

theorem quote_pair_proj :
    quote pairProj = .compose .proj .diverge := by
  simp [pairProj, pairArg, quote, encode, decode]

theorem call_diverges_at_pair_proj : diverges .call pairProj := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    change step n (quote pairProj) pairProj = none
    rw [quote_pair_proj]
    exact compose_right_diverge_diverges .proj pairProj n

theorem decode_delta_none_of_not_void_chain (t : Trace)
    (h0 : t ≠ Trace.void)
    (h1 : t ≠ Trace.delta Trace.void)
    (h2 : t ≠ Trace.delta (Trace.delta Trace.void)) :
    decode (Trace.delta t) = none := by
  cases t with
  | void => exact (h0 rfl).elim
  | delta t' =>
    cases t' with
    | void => exact (h1 rfl).elim
    | delta t'' =>
      cases t'' with
      | void => exact (h2 rfl).elim
      | delta _ => rfl
      | integrate _ => rfl
      | merge _ _ => rfl
      | app _ _ => rfl
      | recΔ _ _ _ => rfl
      | eqW _ _ => rfl
    | integrate _ => rfl
    | merge _ _ => rfl
    | app _ _ => rfl
    | recΔ _ _ _ => rfl
    | eqW _ _ => rfl
  | integrate _ => rfl
  | merge _ _ => rfl
  | app _ _ => rfl
  | recΔ _ _ _ => rfl
  | eqW _ _ => rfl

theorem pairProj_ne_void : pairProj ≠ Trace.void := by
  intro h
  simp [pairProj, pairArg, encode] at h

theorem pairProj_ne_delta_void : pairProj ≠ Trace.delta Trace.void := by
  intro h
  simp [pairProj, pairArg, encode] at h

theorem pairProj_ne_delta2_void :
    pairProj ≠ Trace.delta (Trace.delta Trace.void) := by
  intro h
  simp [pairProj, pairArg, encode] at h

theorem deltaIter_pairProj_ne_void_chain (k : Nat) :
    deltaIter k pairProj ≠ Trace.void ∧
      deltaIter k pairProj ≠ Trace.delta Trace.void ∧
      deltaIter k pairProj ≠ Trace.delta (Trace.delta Trace.void) := by
  induction k with
  | zero =>
    exact ⟨pairProj_ne_void, pairProj_ne_delta_void, pairProj_ne_delta2_void⟩
  | succ k ih =>
    refine ⟨fun h => Trace.noConfusion h, ?_, ?_⟩
    · intro h
      injection h with h'
      exact ih.1 h'
    · intro h
      injection h with h'
      exact ih.2.1 h'

theorem quote_deltaIter_succ_pairProj (k : Nat) :
    quote (deltaIter (k + 1) pairProj) = .diverge := by
  have h := deltaIter_pairProj_ne_void_chain k
  have hd :=
    decode_delta_none_of_not_void_chain (deltaIter k pairProj) h.1 h.2.1 h.2.2
  simp [quote, deltaIter, hd]

theorem call_diverges_at_deltaIter_succ_pairProj (k : Nat) :
    diverges .call (deltaIter (k + 1) pairProj) := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    change step n (quote (deltaIter (k + 1) pairProj))
        (deltaIter (k + 1) pairProj) = none
    rw [quote_deltaIter_succ_pairProj]
    exact step_diverge n _

theorem call_diverges_at_deltaIter_pairProj (k : Nat) :
    diverges .call (deltaIter k pairProj) := by
  cases k with
  | zero =>
    simpa [deltaIter] using call_diverges_at_pair_proj
  | succ k =>
    exact call_diverges_at_deltaIter_succ_pairProj k

theorem sizeOf_compose_assoc (f g1 g2 : PartialCode) :
    sizeOf (PartialCode.compose (PartialCode.compose f g1) g2) =
      sizeOf (PartialCode.compose f (PartialCode.compose g1 g2)) := by
  rw [sizeOf_code_compose, sizeOf_code_compose, sizeOf_code_compose,
    sizeOf_code_compose]
  omega

theorem not_universal_at (U : PartialCode) (k : Nat) :
    ¬ (convergesTo U (deltaIter k pairProj) Trace.void ∧
        convergesTo U (deltaIter k pairSucc)
          (Trace.delta Trace.void)) := by
  match U with
  | .diverge =>
    intro ⟨hp, _⟩
    exact not_convergesTo_of_diverges (diverges_diverge _) hp
  | .proj =>
    intro ⟨hp, _⟩
    have hv : Trace.void = deltaIter k pairProj :=
      (convergesTo_proj_iff _ _).mp hp
    cases k with
    | zero =>
      exact (pairProj_ne_void hv.symm).elim
    | succ _ =>
      exact Trace.noConfusion hv
  | .succ =>
    intro ⟨hp, _⟩
    have hv : Trace.void = Trace.delta (deltaIter k pairProj) :=
      (convergesTo_succ_iff (deltaIter k pairProj) Trace.void).mp hp
    exact Trace.noConfusion hv
  | .const r =>
    intro ⟨hp, hs⟩
    have hr0 : Trace.void = r := (convergesTo_const_iff r _ _).mp hp
    have hr1 : Trace.delta Trace.void = r :=
      (convergesTo_const_iff r _ _).mp hs
    exact Trace.noConfusion (hr0.trans hr1.symm)
  | .call =>
    intro ⟨hp, _⟩
    exact not_convergesTo_of_diverges
      (call_diverges_at_deltaIter_pairProj k) hp
  | .compose f g =>
    match g with
    | .compose g1 g2 =>
      intro ⟨hp, hs⟩
      have hp' :
          convergesTo (.compose (.compose f g1) g2)
            (deltaIter k pairProj) Trace.void :=
        (convergesTo_compose_assoc).mpr hp
      have hs' :
          convergesTo (.compose (.compose f g1) g2)
            (deltaIter k pairSucc) (Trace.delta Trace.void) :=
        (convergesTo_compose_assoc).mpr hs
      exact not_universal_at (.compose (.compose f g1) g2) k ⟨hp', hs'⟩
    | .diverge =>
      intro ⟨hp, _⟩
      exact not_convergesTo_of_diverges
        (compose_right_diverge_diverges f _) hp
    | .proj =>
      intro ⟨hp, hs⟩
      have hu : convergesTo f (deltaIter k pairProj) Trace.void := by
        obtain ⟨u, hgu, hfu⟩ := convergesTo_compose.mp hp
        have : u = deltaIter k pairProj :=
          (convergesTo_proj_iff _ _).mp hgu
        exact this ▸ hfu
      have hw :
          convergesTo f (deltaIter k pairSucc) (Trace.delta Trace.void) := by
        obtain ⟨w, hgw, hfw⟩ := convergesTo_compose.mp hs
        have : w = deltaIter k pairSucc :=
          (convergesTo_proj_iff _ _).mp hgw
        exact this ▸ hfw
      exact not_universal_at f k ⟨hu, hw⟩
    | .succ =>
      intro ⟨hp, hs⟩
      have hu :
          convergesTo f (deltaIter (k + 1) pairProj) Trace.void := by
        obtain ⟨u, hgu, hfu⟩ := convergesTo_compose.mp hp
        have : u = Trace.delta (deltaIter k pairProj) :=
          (convergesTo_succ_iff (deltaIter k pairProj) u).mp hgu
        simpa [deltaIter, this] using hfu
      have hw :
          convergesTo f (deltaIter (k + 1) pairSucc)
            (Trace.delta Trace.void) := by
        obtain ⟨w, hgw, hfw⟩ := convergesTo_compose.mp hs
        have : w = Trace.delta (deltaIter k pairSucc) :=
          (convergesTo_succ_iff (deltaIter k pairSucc) w).mp hgw
        simpa [deltaIter, this] using hfw
      exact not_universal_at f (k + 1) ⟨hu, hw⟩
    | .const r =>
      intro ⟨hp, hs⟩
      obtain ⟨u, hgu, hfu⟩ := convergesTo_compose.mp hp
      have hu : u = r := (convergesTo_const_iff r _ _).mp hgu
      obtain ⟨w, hgw, hfw⟩ := convergesTo_compose.mp hs
      have hw : w = r := (convergesTo_const_iff r _ _).mp hgw
      have hne : Trace.void = Trace.delta Trace.void :=
        convergesTo_unique (hu ▸ hfu) (hw ▸ hfw)
      exact Trace.noConfusion hne
    | .call =>
      intro ⟨hp, _⟩
      obtain ⟨u, hgu, _hfu⟩ := convergesTo_compose.mp hp
      exact not_convergesTo_of_diverges
        (call_diverges_at_deltaIter_pairProj k) hgu
termination_by (sizeOf U, rightSpine U)
decreasing_by
  all_goals (simp_wf; simp [rightSpine]; omega)

theorem not_universal_on_proj_succ (U : PartialCode) :
    ¬ (convergesTo U pairProj Trace.void ∧
        convergesTo U pairSucc (Trace.delta Trace.void)) := by
  simpa [deltaIter] using not_universal_at U 0

theorem IsUniversal.forces_proj_succ {U : PartialCode} (h : IsUniversal U) :
    convergesTo U pairProj Trace.void ∧
      convergesTo U pairSucc (Trace.delta Trace.void) :=
  ⟨(h .proj Trace.void Trace.void).mpr ⟨1, rfl⟩,
    (h .succ Trace.void (Trace.delta Trace.void)).mpr ⟨1, rfl⟩⟩

theorem no_universal_interpreter (U : PartialCode) : ¬ IsUniversal U := by
  intro h
  exact not_universal_on_proj_succ U h.forces_proj_succ

theorem numbering_not_acceptable : ¬ AcceptableNumbering := by
  intro h
  obtain ⟨U, hU⟩ := h.universal
  exact no_universal_interpreter U hU

theorem left_compose_any_has_extensional_fp (g : PartialCode) :
    ∃ e, BehEq e (.compose g e) :=
  ⟨.diverge,
    BehEq_of_everywhere_diverge diverges_diverge
      (fun x => compose_right_diverge_diverges g x)⟩

theorem freezeSuccOp_encode_diverge :
    encode (freezeSuccOp .diverge) =
      Trace.app (Trace.delta (Trace.delta Trace.void))
        (Trace.merge Trace.void Trace.void) :=
  rfl

theorem freezeSuccOp_encode_proj :
    encode (freezeSuccOp .proj) =
      Trace.app (Trace.delta (Trace.delta Trace.void))
        (Trace.merge Trace.void (Trace.delta Trace.void)) :=
  rfl

theorem freezeSuccOp_encode_diverge_ne_proj :
    encode (freezeSuccOp .diverge) ≠ encode (freezeSuccOp .proj) := by
  intro h
  simp [freezeSuccOp_encode_diverge, freezeSuccOp_encode_proj] at h

theorem freezeSuccOp_encode_is_app (c : PartialCode) :
    ∃ a b, encode (freezeSuccOp c) = Trace.app a b :=
  ⟨encode .succ, encode (.const (encode c)), rfl⟩

def freezeOutDiverge : Trace := encode (freezeSuccOp .diverge)

def freezeOutProj : Trace := encode (freezeSuccOp .proj)

def isCompoundB : Trace → Bool
  | .merge _ _ => true
  | .app _ _ => true
  | _ => false

theorem isCompound_iff_b (t : Trace) :
    IsCompound t ↔ isCompoundB t = true := by
  cases t <;> simp [IsCompound, isCompoundB]

theorem compound_size_ge_three (t : Trace) (h : IsCompound t) :
    3 ≤ sizeOf t := by
  cases t with
  | merge a b =>
    rw [sizeOf_merge]
    have := trace_size_pos a
    have := trace_size_pos b
    omega
  | app a b => exact app_size_ge_three a b
  | void => cases h
  | delta _ => cases h
  | integrate _ => cases h
  | recΔ _ _ _ => cases h
  | eqW _ _ => cases h

theorem call_atom_not_compound {s t : Trace}
    (hs : ¬ IsCompound s) (ht : IsCompound t) :
    ¬ convergesTo .call s t := by
  intro h
  have hsz := step_compound_from_atom_conv h ht hs
  have hge := compound_size_ge_three t ht
  have henc : sizeOf (encode PartialCode.call) = 4 := sizeOf_encode_call
  omega

theorem freezeOutDiverge_is_compound : IsCompound freezeOutDiverge :=
  trivial

theorem freezeOutProj_is_compound : IsCompound freezeOutProj :=
  trivial

theorem not_two_distinct_compounds (U : PartialCode) {t1 t2 : Trace}
    (ht1 : IsCompound t1) (ht2 : IsCompound t2) (hne : t1 ≠ t2) :
    ¬ (convergesTo U Trace.void t1 ∧
        convergesTo U (Trace.delta Trace.void) t2) := by
  intro ⟨hp, hs⟩
  cases hhd : leftHead U with
  | const r =>
    exact hne
      ((leftHead_const_eval hhd hp).trans (leftHead_const_eval hhd hs).symm)
  | succ =>
    obtain ⟨u, hu⟩ := leftHead_succ_is_delta hhd hp
    exact not_compound_delta u (hu ▸ ht1)
  | diverge =>
    exact not_convergesTo_of_diverges
      (leftHead_diverge_diverges hhd Trace.void) hp
  | compose f g =>
    exact (leftHead_ne_compose U f g hhd).elim
  | proj =>
    match hU : U with
    | PartialCode.proj =>
      have hv : t1 = Trace.void := (convergesTo_proj_iff _ _).mp hp
      exact not_compound_void (hv ▸ ht1)
    | PartialCode.compose f g =>
      exact not_two_distinct_compounds
        (restOf (PartialCode.compose f g)) ht1 ht2 hne
        ⟨restOf_leftHead_proj (hU ▸ hhd) hp,
          restOf_leftHead_proj (hU ▸ hhd) hs⟩
    | PartialCode.diverge => simp [leftHead] at hhd
    | PartialCode.succ => simp [leftHead] at hhd
    | PartialCode.const _ => simp [leftHead] at hhd
    | PartialCode.call => simp [leftHead] at hhd
  | call =>
    match hU : U with
    | PartialCode.call =>
      exact not_convergesTo_of_diverges call_diverges_at_void hp
    | PartialCode.compose f g =>
      obtain ⟨s, hrest, hcall⟩ := restOf_leftHead_call (hU ▸ hhd) hp
      obtain ⟨s2, hrest2, hcall2⟩ := restOf_leftHead_call (hU ▸ hhd) hs
      if hsB : isCompoundB s = true then
        if hs2B : isCompoundB s2 = true then
          if heq : s = s2 then
            exact hne (convergesTo_unique hcall (heq ▸ hcall2))
          else
            exact not_two_distinct_compounds
              (restOf (PartialCode.compose f g))
              ((isCompound_iff_b s).mpr hsB)
              ((isCompound_iff_b s2).mpr hs2B) heq
              ⟨hrest, hrest2⟩
        else
          exact call_atom_not_compound
            (fun hcmp => hs2B ((isCompound_iff_b s2).mp hcmp)) ht2 hcall2
      else
        exact call_atom_not_compound
          (fun hcmp => hsB ((isCompound_iff_b s).mp hcmp)) ht1 hcall
    | PartialCode.diverge => simp [leftHead] at hhd
    | PartialCode.proj => simp [leftHead] at hhd
    | PartialCode.succ => simp [leftHead] at hhd
    | PartialCode.const _ => simp [leftHead] at hhd
termination_by sizeOf U
decreasing_by
  · simp_wf; subst hU; exact restOf_size_lt_compose f g
  · simp_wf; subst hU; exact restOf_size_lt_compose f g

theorem freezeSuccOp_not_effective : ¬ EffectiveTransformer freezeSuccOp := by
  rintro ⟨f, hf⟩
  exact not_two_distinct_compounds f freezeOutDiverge_is_compound
    freezeOutProj_is_compound freezeSuccOp_encode_diverge_ne_proj
    ⟨hf .diverge, hf .proj⟩

theorem freezeSucc_kill_compatible_with_missing_kleene_premises :
    ¬ AcceptableNumbering ∧ ¬ EffectiveTransformer freezeSuccOp ∧
      ¬ ∃ e, BehEq e (freezeSuccOp e) :=
  ⟨numbering_not_acceptable, freezeSuccOp_not_effective,
    freeze_succ_operator_has_no_extensional_fp⟩

/-! ## Small relative interpreter extension -/

inductive AccCode : Type
  | embed : PartialCode → AccCode
  | apply : AccCode
  | cons : Trace → AccCode
  | compose : AccCode → AccCode → AccCode
deriving DecidableEq, Repr

def stepAcc : Nat → AccCode → Trace → Option Trace
  | 0, _, _ => none
  | n + 1, .embed c, x => step (n + 1) c x
  | n + 1, .apply, x =>
      match x with
      | Trace.app a b => stepAcc n (.embed (quote a)) b
      | _ => none
  | _n + 1, .cons a, b => some (Trace.app a b)
  | n + 1, .compose f g, x => (stepAcc n g x).bind (stepAcc n f)

def convergesToAcc (c : AccCode) (x v : Trace) : Prop :=
  ∃ n, stepAcc n c x = some v

def divergesAcc (c : AccCode) (x : Trace) : Prop :=
  ∀ n, stepAcc n c x = none

theorem stepAcc_zero (c : AccCode) (x : Trace) : stepAcc 0 c x = none :=
  rfl

theorem stepAcc_embed (n : Nat) (c : PartialCode) (x : Trace) :
    stepAcc (n + 1) (.embed c) x = step (n + 1) c x :=
  rfl

theorem stepAcc_apply_app (n : Nat) (a b : Trace) :
    stepAcc (n + 1) .apply (Trace.app a b) =
      stepAcc n (.embed (quote a)) b :=
  rfl

theorem stepAcc_cons (n : Nat) (a b : Trace) :
    stepAcc (n + 1) (.cons a) b = some (Trace.app a b) :=
  rfl

theorem embed_tracks (c : PartialCode) (x v : Trace) :
    convergesToAcc (.embed c) x v ↔ convergesTo c x v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => cases hn
    | succ n => exact ⟨n + 1, hn⟩
  · rintro ⟨n, hn⟩
    cases n with
    | zero => cases hn
    | succ n => exact ⟨n + 1, hn⟩

theorem apply_is_universal (e : PartialCode) (x v : Trace) :
    convergesToAcc .apply (Trace.app (encode e) x) v ↔
      convergesTo e x v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => cases hn
    | succ n =>
      have hn' : stepAcc n (.embed (quote (encode e))) x = some v := by
        simpa [stepAcc] using hn
      have hq : quote (encode e) = e := quote_encode e
      rw [hq] at hn'
      exact (embed_tracks e x v).mp ⟨n, hn'⟩
  · rintro ⟨n, hn⟩
    cases n with
    | zero => cases hn
    | succ n =>
      refine ⟨n + 2, ?_⟩
      have hq : quote (encode e) = e := quote_encode e
      change stepAcc (n + 1) (.embed (quote (encode e))) x = some v
      rw [hq, stepAcc_embed]
      exact hn

def InterpretsPartialCode (U : AccCode) : Prop :=
  ∀ e x v, convergesToAcc U (Trace.app (encode e) x) v ↔ convergesTo e x v

theorem apply_interprets_partialCode : InterpretsPartialCode .apply :=
  apply_is_universal

theorem cons_pairs (a b : Trace) :
    convergesToAcc (.cons a) b (Trace.app a b) :=
  ⟨1, rfl⟩

theorem cons_pairs_embedded_code (e : PartialCode) (x : Trace) :
    convergesToAcc (.cons (encode e)) x (pairArg e x) :=
  cons_pairs (encode e) x

/-- Exact relative property actually proved by the extension. -/
structure PartialCodeInterpreterExtension : Prop where
  interpreter : InterpretsPartialCode .apply
  pairing : ∀ e x, convergesToAcc (.cons (encode e)) x (pairArg e x)

theorem partialCode_interpreter_extension : PartialCodeInterpreterExtension :=
  ⟨apply_interprets_partialCode, cons_pairs_embedded_code⟩

def freezeSuccAcc (c : PartialCode) : AccCode :=
  .embed (freezeSuccOp c)

theorem freezeSuccOp_not_effective_on_embed :
    ¬ ∃ f : PartialCode,
        ∀ c, convergesToAcc (.embed f) (encode c)
          (encode (freezeSuccOp c)) := by
  rintro ⟨f, hf⟩
  exact freezeSuccOp_not_effective ⟨f, fun c => (embed_tracks f _ _).mp (hf c)⟩

end OperatorKO7.Meta.DistinctionBoundary.GodelPartial
