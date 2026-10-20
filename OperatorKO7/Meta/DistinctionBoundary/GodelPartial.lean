import OperatorKO7.Meta.DistinctionBoundary.GodelObject
import OperatorKO7.Meta.EqGuardedConfluence

set_option autoImplicit false

/-!
# Partiality escape: fuelled interpreter with decode-quote

The total schematic object of `GodelObject.lean` is the smaller-class
escape. Its verdict is `quote_represented_are_constants`: every
quote-represented map is constant, and `S_D = id`. This module takes the
remaining non-degenerate route: evaluation is partial, quotation is a
tagged decode, and self-application is actual application of the decoded
code to its own encoding.

Representation is agreement of behaviours (`convergesTo` / `diverges`),
not a total `eval`. The successor combinator is quote-represented and
depends on its argument. The composite `compose succ call` fails to
converge at its own code for the diagonal reason: a defined value would
be a fixed point of `delta`.

NameGate: no `goedel_first`, no `incompleteness`, no `feferman_completeness`.
This is not an incompleteness theorem. It does not inhabit
`InternalToSignature` on Trace. It does not totalize `none` to fill a
total `SelfEvaluationDiagonal`.

Relation: fuel-indexed step, behaviours in Prop.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelPartial

open OperatorKO7
open OperatorKO7.Meta.DistinctionBoundary.DiagonalLevels
open OperatorKO7.Meta.DistinctionBoundary
open OperatorKO7.EqGuardedConfluence

/-! ## Codes, tagged encoding, decode-quote -/

inductive PartialCode : Type
  | diverge : PartialCode
  | proj : PartialCode
  | succ : PartialCode
  | const : Trace → PartialCode
  | compose : PartialCode → PartialCode → PartialCode
  | call : PartialCode
deriving DecidableEq, Repr

def encode : PartialCode → Trace
  | .diverge => Trace.void
  | .proj => Trace.delta Trace.void
  | .succ => Trace.delta (Trace.delta Trace.void)
  | .call => Trace.delta (Trace.delta (Trace.delta Trace.void))
  | .const t => Trace.merge Trace.void t
  | .compose f g => Trace.app (encode f) (encode g)

def decode : Trace → Option PartialCode
  | .void => some .diverge
  | .delta .void => some .proj
  | .delta (.delta .void) => some .succ
  | .delta (.delta (.delta .void)) => some .call
  | .delta _ => none
  | .merge .void t => some (.const t)
  | .merge _ _ => none
  | .app a b =>
      match decode a, decode b with
      | some f, some g => some (.compose f g)
      | _, _ => none
  | .integrate _ => none
  | .recΔ _ _ _ => none
  | .eqW _ _ => none

theorem decode_encode : ∀ c : PartialCode, decode (encode c) = some c
  | .diverge => rfl
  | .proj => rfl
  | .succ => rfl
  | .call => rfl
  | .const _ => rfl
  | .compose f g => by
      change
        (match decode (encode f), decode (encode g) with
          | some f', some g' => some (PartialCode.compose f' g')
          | _, _ => none) =
          some (PartialCode.compose f g)
      rw [decode_encode f, decode_encode g]

theorem encode_of_decode {t : Trace} {c : PartialCode}
    (h : decode t = some c) : encode c = t := by
  induction t generalizing c with
  | void =>
    cases h
    rfl
  | delta a _ =>
    cases a with
    | void =>
      cases h
      rfl
    | delta b =>
      cases b with
      | void =>
        cases h
        rfl
      | delta d =>
        cases d with
        | void =>
          cases h
          rfl
        | delta _ => cases h
        | integrate _ => cases h
        | merge _ _ => cases h
        | app _ _ => cases h
        | recΔ _ _ _ => cases h
        | eqW _ _ => cases h
      | integrate _ => cases h
      | merge _ _ => cases h
      | app _ _ => cases h
      | recΔ _ _ _ => cases h
      | eqW _ _ => cases h
    | integrate _ => cases h
    | merge _ _ => cases h
    | app _ _ => cases h
    | recΔ _ _ _ => cases h
    | eqW _ _ => cases h
  | integrate _ _ =>
    cases h
  | merge a b _ _ =>
    cases a with
    | void =>
      cases h
      rfl
    | delta _ => cases h
    | integrate _ => cases h
    | merge _ _ => cases h
    | app _ _ => cases h
    | recΔ _ _ _ => cases h
    | eqW _ _ => cases h
  | app a b iha ihb =>
    cases hf : decode a with
    | none =>
      change
        (match decode a, decode b with
          | some f, some g => some (PartialCode.compose f g)
          | _, _ => none) =
          some c at h
      rw [hf] at h
      cases h
    | some f =>
      cases hg : decode b with
      | none =>
        change
          (match decode a, decode b with
            | some f, some g => some (PartialCode.compose f g)
            | _, _ => none) =
            some c at h
        rw [hf, hg] at h
        cases h
      | some g =>
        change
          (match decode a, decode b with
            | some f, some g => some (PartialCode.compose f g)
            | _, _ => none) =
            some c at h
        rw [hf, hg] at h
        cases h
        simp [encode, iha hf, ihb hg]
  | recΔ _ _ _ _ _ _ =>
    cases h
  | eqW _ _ _ _ =>
    cases h

def quote (t : Trace) : PartialCode :=
  (decode t).getD .diverge

theorem quote_encode (c : PartialCode) : quote (encode c) = c := by
  show (decode (encode c)).getD .diverge = c
  rw [decode_encode]
  rfl

theorem encode_injective {c d : PartialCode} (h : encode c = encode d) :
    c = d := by
  have hc := decode_encode c
  have hd := decode_encode d
  rw [h] at hc
  rw [hc] at hd
  injection hd

/-! ## Fuel interpreter -/

def step : Nat → PartialCode → Trace → Option Trace
  | 0, _, _ => none
  | _n + 1, .diverge, _ => none
  | _n + 1, .proj, x => some x
  | _n + 1, .succ, x => some (Trace.delta x)
  | _n + 1, .const t, _ => some t
  | n + 1, .compose f g, x => (step n g x).bind (step n f)
  | n + 1, .call, x => step n (quote x) x

theorem step_zero (c : PartialCode) (x : Trace) : step 0 c x = none :=
  rfl

theorem step_diverge (n : Nat) (x : Trace) : step n .diverge x = none := by
  cases n <;> rfl

theorem step_proj (n : Nat) (x : Trace) : step (n + 1) .proj x = some x :=
  rfl

theorem step_succ (n : Nat) (x : Trace) :
    step (n + 1) .succ x = some (Trace.delta x) :=
  rfl

theorem step_const (n : Nat) (t x : Trace) :
    step (n + 1) (.const t) x = some t :=
  rfl

theorem step_compose (n : Nat) (f g : PartialCode) (x : Trace) :
    step (n + 1) (.compose f g) x = (step n g x).bind (step n f) :=
  rfl

theorem step_call (n : Nat) (x : Trace) :
    step (n + 1) .call x = step n (quote x) x :=
  rfl

theorem step_mono {n m : Nat} {c : PartialCode} {x v : Trace}
    (hle : n ≤ m) (h : step n c x = some v) : step m c x = some v := by
  induction n generalizing m c x v with
  | zero =>
    cases h
  | succ n ih =>
    cases m with
    | zero =>
      exact (Nat.not_succ_le_zero n hle).elim
    | succ m =>
      have hnm : n ≤ m := Nat.le_of_succ_le_succ hle
      cases c with
      | diverge =>
        cases h
      | proj =>
        exact h
      | succ =>
        exact h
      | const t =>
        exact h
      | compose f g =>
        cases hg : step n g x with
        | none =>
          have h' : (step n g x).bind (step n f) = some v := h
          rw [hg] at h'
          cases h'
        | some u =>
          have hf : step n f u = some v := by
            have h' : (step n g x).bind (step n f) = some v := h
            rw [hg] at h'
            exact h'
          have hg' : step m g x = some u := ih hnm hg
          have hf' : step m f u = some v := ih hnm hf
          have : (step m g x).bind (step m f) = some v := by
            rw [hg']
            exact hf'
          exact this
      | call =>
        exact ih (m := m) (c := quote x) (x := x) (v := v) hnm h

/-! ## Behaviours -/

def convergesTo (c : PartialCode) (x v : Trace) : Prop :=
  ∃ n, step n c x = some v

def diverges (c : PartialCode) (x : Trace) : Prop :=
  ∀ n, step n c x = none

def BehRepresents (c : PartialCode) (f : Trace → Option Trace) : Prop :=
  ∀ x : Trace,
    (f x = none ∧ diverges c x) ∨
      (∃ v, f x = some v ∧ convergesTo c x v)

def QuoteRepresents (f : Trace → Option Trace) : Prop :=
  ∃ t : Trace, BehRepresents (quote t) f

def BehEq (c d : PartialCode) : Prop :=
  ∀ x v : Trace, convergesTo c x v ↔ convergesTo d x v

theorem convergesTo_unique {c : PartialCode} {x v w : Trace}
    (hv : convergesTo c x v) (hw : convergesTo c x w) : v = w := by
  obtain ⟨n, hn⟩ := hv
  obtain ⟨m, hm⟩ := hw
  cases Nat.le_total n m with
  | inl hle =>
    have hn' := step_mono hle hn
    injection (hn'.symm.trans hm)
  | inr hle =>
    have hm' := step_mono hle hm
    injection (hn.symm.trans hm')

theorem diverges_diverge (x : Trace) : diverges .diverge x :=
  fun n => step_diverge n x

/-! ## Sharp kill: successor is represented and non-degenerate -/

def succBeh (x : Trace) : Option Trace := some (Trace.delta x)

theorem successor_map_is_represented : BehRepresents .succ succBeh := by
  intro x
  refine Or.inr ⟨Trace.delta x, rfl, ⟨1, rfl⟩⟩

theorem succBeh_argument_dependent :
    ∃ x y : Trace, succBeh x ≠ succBeh y :=
  ⟨Trace.void, Trace.delta Trace.void, fun h => by
    injection h with h
    injection h with h
    exact Trace.noConfusion h⟩

theorem succBeh_not_pointwise_identity :
    ∃ x : Trace, succBeh x ≠ some x :=
  ⟨Trace.void, fun h => by
    injection h with h
    exact delta_ne_self Trace.void h⟩

theorem succBeh_has_no_value_fixed_point : ¬ ∃ x, succBeh x = some x := by
  rintro ⟨x, hx⟩
  injection hx with hx
  exact delta_ne_self x hx

/-- Pre-registered kill for this wave: the represented class contains a
map that depends on its argument and is neither the identity nor a
constant. The total schematic object fails this kill
(`schematic_fails_sharp_kill`). -/
theorem succ_survives_sharp_kill :
    BehRepresents .succ succBeh ∧
      (∃ x y : Trace, succBeh x ≠ succBeh y) ∧
      (∃ x : Trace, succBeh x ≠ some x) :=
  ⟨successor_map_is_represented, succBeh_argument_dependent,
    succBeh_not_pointwise_identity⟩

theorem succ_is_quote_represented : QuoteRepresents succBeh := by
  refine ⟨encode .succ, ?_⟩
  rw [quote_encode]
  exact successor_map_is_represented

/-! ## Self-application is not identity -/

theorem encode_succ_ne_delta_encode_succ :
    Trace.delta (encode .succ) ≠ encode .succ := by
  intro h
  injection h with h
  injection h with h
  exact Trace.noConfusion h

/-- Decode-quote makes self-application genuine: `quote (encode succ)`
is `succ`, which sends its own code to a distinct value. -/
theorem selfap_not_identity :
    ∃ t v : Trace, convergesTo (quote t) t v ∧ v ≠ t := by
  refine ⟨encode .succ, Trace.delta (encode .succ), ?_,
    encode_succ_ne_delta_encode_succ⟩
  rw [quote_encode]
  exact ⟨1, rfl⟩

theorem proj_has_defined_fixed_point (x : Trace) :
    convergesTo .proj x x :=
  ⟨1, rfl⟩

/-! ## Call tracks self-application; composite tracks `delta ∘ S_D` -/

theorem convergesTo_call_iff (x v : Trace) :
    convergesTo .call x v ↔ convergesTo (quote x) x v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => cases hn
    | succ n => exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, hn⟩

theorem convergesTo_compose_succ_call {x v : Trace} :
    convergesTo (.compose .succ .call) x v ↔
      ∃ u, convergesTo .call x u ∧ v = Trace.delta u := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => cases hn
    | succ n =>
      cases hu : step n .call x with
      | none =>
        have h' : (step n .call x).bind (step n .succ) = some v := hn
        rw [hu] at h'
        cases h'
      | some u =>
        have hs : step n .succ u = some v := by
          have h' : (step n .call x).bind (step n .succ) = some v := hn
          rw [hu] at h'
          exact h'
        cases n with
        | zero => cases hs
        | succ n =>
          refine ⟨u, ⟨n + 1, hu⟩, ?_⟩
          injection hs with hvu
          exact hvu.symm
  · rintro ⟨u, ⟨n, hn⟩, hv⟩
    subst hv
    cases n with
    | zero => cases hn
    | succ n =>
      refine ⟨n + 2, ?_⟩
      change
        (step (n + 1) .call x).bind (step (n + 1) .succ) =
          some (Trace.delta u)
      rw [hn]
      rfl

def diagonalComposite : PartialCode := .compose .succ .call

def diagonalWitness : Trace := encode diagonalComposite

theorem quote_diagonalWitness : quote diagonalWitness = diagonalComposite :=
  quote_encode _

theorem compose_succ_call_tracks_delta_selfap (y v : Trace) :
    convergesTo (quote diagonalWitness) y v ↔
      ∃ u, convergesTo (quote y) y u ∧ v = Trace.delta u := by
  rw [quote_diagonalWitness]
  constructor
  · intro h
    obtain ⟨u, hu, hv⟩ := convergesTo_compose_succ_call.mp h
    exact ⟨u, (convergesTo_call_iff y u).mp hu, hv⟩
  · rintro ⟨u, hu, hv⟩
    exact
      convergesTo_compose_succ_call.mpr
        ⟨u, (convergesTo_call_iff y u).mpr hu, hv⟩

/-- If the successor composite converged at its own code, the value would
be a fixed point of `delta`. This is the diagonal reason, not the
id/const dichotomy. -/
theorem diagonal_successor_if_converges_is_delta_fp {z : Trace}
    (h : convergesTo diagonalComposite diagonalWitness z) :
    Trace.delta z = z := by
  obtain ⟨u, hu, hz⟩ := convergesTo_compose_succ_call.mp h
  have hu' : convergesTo (quote diagonalWitness) diagonalWitness u :=
    (convergesTo_call_iff diagonalWitness u).mp hu
  rw [quote_diagonalWitness] at hu'
  have huniq : u = z := convergesTo_unique hu' h
  calc
    Trace.delta z = Trace.delta u := congrArg Trace.delta huniq.symm
    _ = z := hz.symm

/-- Failure object: the representing code of `delta ∘ S_D` diverges at
its own encoding, because a defined value would fix `delta`. -/
theorem diagonal_successor_composite_diverges_at_own_code :
    diverges diagonalComposite diagonalWitness := by
  intro n
  cases hn : step n diagonalComposite diagonalWitness with
  | none => rfl
  | some z =>
    exact (delta_ne_self z
      (diagonal_successor_if_converges_is_delta_fp ⟨n, hn⟩)).elim

/-! ## Partial fixed-point theorem with content -/

/-- Kleene-shaped recovery: when quote-representation of `g ∘ S_D`
converges at the witness, the value is a fixed point of `g`. -/
theorem partial_fp_when_converges (g : Trace → Trace) (x z : Trace)
    (hrep : ∀ y v, convergesTo (quote x) y v ↔
      ∃ u, convergesTo (quote y) y u ∧ v = g u)
    (hdef : convergesTo (quote x) x z) : g z = z := by
  obtain ⟨u, hu, hz⟩ := (hrep x z).mp hdef
  have : u = z := convergesTo_unique hu hdef
  subst this
  exact hz.symm

/-- Fuel-counting companion: `compose c call` unfolds `call` into itself
at its own encoding, so the step is never defined. -/
theorem compose_call_step_none (c : PartialCode) :
    ∀ n, step n (.compose c .call) (encode (.compose c .call)) = none
  | 0 => rfl
  | n + 1 => by
      let w := encode (.compose c .call)
      have hw : quote w = .compose c .call := quote_encode _
      have hcall : step n .call w = none := by
        cases n with
        | zero => rfl
        | succ m =>
          have : step (m + 1) .call w = step m (quote w) w := rfl
          rw [this, hw]
          exact compose_call_step_none c m
      have : step (n + 1) (.compose c .call) w =
          (step n .call w).bind (step n c) := rfl
      rw [this, hcall]
      rfl

theorem constant_after_call_diverges_at_its_own_code :
    diverges (.compose (.const Trace.void) .call)
      (encode (.compose (.const Trace.void) .call)) :=
  compose_call_step_none (.const Trace.void)

/-! ## Substitution: freeze and live -/

def freezeSubst (c : PartialCode) (x : Trace) : PartialCode :=
  .compose c (.const x)

def liveSubst (c : PartialCode) (x : Trace) : PartialCode :=
  .compose c (quote x)

theorem freezeSubst_tracks {c : PartialCode} {x y v : Trace} :
    convergesTo (freezeSubst c x) y v ↔ convergesTo c x v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => cases hn
    | succ n =>
      cases n with
      | zero => cases hn
      | succ n =>
        have h' : (step (n + 1) (.const x) y).bind (step (n + 1) c) =
            some v := hn
        have hx : step (n + 1) (.const x) y = some x := rfl
        rw [hx] at h'
        exact ⟨n + 1, h'⟩
  · rintro ⟨n, hn⟩
    cases n with
    | zero => cases hn
    | succ n =>
      refine ⟨n + 2, ?_⟩
      change (step (n + 1) (.const x) y).bind (step (n + 1) c) = some v
      have hx : step (n + 1) (.const x) y = some x := rfl
      rw [hx]
      exact hn

theorem freeze_subst_succ_converges_to_delta (G y : Trace) :
    convergesTo (freezeSubst .succ G) y (Trace.delta G) :=
  ⟨2, rfl⟩

theorem freeze_and_live_disagree_at_r5 :
    convergesTo (freezeSubst .proj Trace.void) (Trace.delta Trace.void)
        Trace.void ∧
      diverges (liveSubst .proj Trace.void) (Trace.delta Trace.void) := by
  refine ⟨⟨2, rfl⟩, ?_⟩
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    have hd : step n .diverge (Trace.delta Trace.void) = none :=
      step_diverge n (Trace.delta Trace.void)
    change
      (step n .diverge (Trace.delta Trace.void)).bind (step n .proj) = none
    rw [hd]
    rfl

theorem merge_void_delta_ne_self :
    ∀ G : Trace, Trace.merge Trace.void (Trace.delta G) ≠ G
  | .merge a b, h => by
      injection h with ha hb
      cases ha
      cases b with
      | delta t =>
        injection hb with ht
        exact merge_void_delta_ne_self t ht
      | void => cases hb
      | integrate _ => cases hb
      | merge _ _ => cases hb
      | app _ _ => cases hb
      | recΔ _ _ _ => cases hb
      | eqW _ _ => cases hb
  | .void, h => by cases h
  | .delta _, h => by cases h
  | .integrate _, h => by cases h
  | .app _ _, h => by cases h
  | .recΔ _ _ _, h => by cases h
  | .eqW _ _, h => by cases h

/-- First-order freeze diagonal for `succ` would require a code equal to
`const (delta G)` at `G`, which the free algebra forbids. -/
theorem freeze_diagonal_naive_candidate_impossible (G : Trace) :
    encode (.const (Trace.delta G)) ≠ G :=
  merge_void_delta_ne_self G

/-! ## Second recursion form (Kleene, combinator fragment) -/

theorem diverges_compose_succ_diverge (x : Trace) :
    diverges (.compose .succ .diverge) x := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    have hd : step n .diverge x = none := diverges_diverge x n
    change (step n .diverge x).bind (step n .succ) = none
    rw [hd]
    rfl

/-- Left composition with successor has an extensional fixed point: the
everywhere-divergent code. This is the content of the recursion form
on this combinator; the value-level Lawvere fixed point is the `some`
case, which does not arise here. -/
theorem second_recursion_form_left_succ :
    ∃ e : PartialCode, ∀ x, diverges e x ∧ diverges (.compose .succ e) x :=
  ⟨.diverge, fun x => ⟨diverges_diverge x, diverges_compose_succ_diverge x⟩⟩

theorem BehEq_of_everywhere_diverge {c d : PartialCode}
    (hc : ∀ x, diverges c x) (hd : ∀ x, diverges d x) : BehEq c d := by
  intro x v
  constructor
  · rintro ⟨n, hn⟩
    have := hc x n
    rw [this] at hn
    cases hn
  · rintro ⟨n, hn⟩
    have := hd x n
    rw [this] at hn
    cases hn

theorem second_recursion_form_left_succ_beh :
    BehEq .diverge (.compose .succ .diverge) :=
  BehEq_of_everywhere_diverge diverges_diverge diverges_compose_succ_diverge

theorem convergesTo_compose_succ {e : PartialCode} {x v : Trace}
    (h : convergesTo e x v) :
    convergesTo (.compose .succ e) x (Trace.delta v) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => cases hn
  | succ n =>
    refine ⟨n + 2, ?_⟩
    change
      (step (n + 1) e x).bind (step (n + 1) .succ) = some (Trace.delta v)
    rw [hn]
    rfl

theorem not_convergesTo_of_left_succ_fp (e : PartialCode)
    (h : BehEq e (.compose .succ e)) (x v : Trace) :
    ¬ convergesTo e x v := by
  intro he
  have hc := convergesTo_compose_succ he
  have he' : convergesTo e x (Trace.delta v) := (h x (Trace.delta v)).mpr hc
  have hv := convergesTo_unique he he'
  exact delta_ne_self v hv.symm

/-- Any behavioural fixed point of left-succ is everywhere divergent.
The empty behaviour is the unique extensional solution. -/
theorem left_succ_behavioural_fp_must_diverge (e : PartialCode)
    (h : BehEq e (.compose .succ e)) (x : Trace) : diverges e x := by
  intro n
  cases hn : step n e x with
  | none => rfl
  | some v => exact (not_convergesTo_of_left_succ_fp e h x v ⟨n, hn⟩).elim

theorem convergesTo_const_iff (t x v : Trace) :
    convergesTo (.const t) x v ↔ v = t := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => cases hn
    | succ _n =>
      injection hn with hvu
      exact hvu.symm
  · rintro rfl
    exact ⟨1, rfl⟩

theorem convergesTo_compose_const_const_iff (t x v : Trace) :
    convergesTo (.compose (.const t) (.const t)) x v ↔ v = t := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => cases hn
    | succ n =>
      cases n with
      | zero => cases hn
      | succ _n =>
        injection hn with hvu
        exact hvu.symm
  · rintro rfl
    exact ⟨2, rfl⟩

theorem second_recursion_form_const (t : Trace) :
    BehEq (.const t) (.compose (.const t) (.const t)) := by
  intro x v
  rw [convergesTo_const_iff, convergesTo_compose_const_const_iff]

theorem convergesTo_proj_iff (x v : Trace) :
    convergesTo .proj x v ↔ v = x := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => cases hn
    | succ _n =>
      injection hn with hvu
      exact hvu.symm
  · rintro rfl
    exact ⟨1, rfl⟩

theorem second_recursion_form_proj :
    BehEq .proj (.compose .proj .proj) := by
  intro x v
  constructor
  · intro h
    have hv := (convergesTo_proj_iff x v).mp h
    subst hv
    exact ⟨2, rfl⟩
  · rintro ⟨n, hn⟩
    cases n with
    | zero => cases hn
    | succ n =>
      cases n with
      | zero => cases hn
      | succ _n =>
        injection hn with hv
        subst hv
        exact ⟨1, rfl⟩

/-! ## Totalization does not invent a `delta` fixed point -/

def totalize (o : Option Trace) : Trace := o.getD Trace.void

theorem totalization_does_not_produce_delta_fixed_point (n : Nat) :
    totalize (step n (quote diagonalWitness) diagonalWitness) ≠
      Trace.delta
        (totalize (step n (quote diagonalWitness) diagonalWitness)) := by
  have hnone :
      step n (quote diagonalWitness) diagonalWitness = none := by
    rw [quote_diagonalWitness]
    exact diagonal_successor_composite_diverges_at_own_code n
  have hz : totalize (step n (quote diagonalWitness) diagonalWitness) =
      Trace.void := by
    simp [totalize, hnone]
  rw [hz]
  exact (delta_ne_self Trace.void).symm

/-! ## G8: quotation is unstable under the merge reduction -/

theorem quote_merge_void_void :
    quote (Trace.merge Trace.void Trace.void) = .const Trace.void :=
  rfl

theorem quote_void_eq_diverge : quote Trace.void = .diverge := rfl

theorem quote_not_stable_under_merge :
    quote (Trace.merge Trace.void Trace.void) ≠ quote Trace.void ∧
      EqGuardedStep (Trace.merge Trace.void Trace.void) Trace.void :=
  And.intro (fun h => by cases h)
    (EqGuardedStep.R_merge_void_left Trace.void)

/-! ## Duck: smaller-class cost versus this object's successor -/

/-- The total schematic object quote-represents only constants. This
object quote-represents `succBeh`. -/
theorem smaller_class_versus_partial_successor :
    (∀ f, Godel.represents Godel.schematicSelfEvaluation f →
      ∃ t, ∀ y, f y = t) ∧
      QuoteRepresents succBeh :=
  ⟨fun _f hf => Godel.quote_represented_are_constants hf,
    succ_is_quote_represented⟩

end OperatorKO7.Meta.DistinctionBoundary.GodelPartial
