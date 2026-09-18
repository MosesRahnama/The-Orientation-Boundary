import OperatorKO7.Kernel
import OperatorKO7.Meta.LPO_Schema
import OperatorKO7.Meta.ContextClosed_SN_Full
import OperatorKO7.Meta.CompositionalMeasure_Impossibility
import OperatorKO7.Meta.BarrierPumpDischarge_Schema
import OperatorKO7.Meta.StepDuplicatingSchema

set_option autoImplicit false

/-!
# Transitive equal-tail path-order instance on the KO7 kernel

Precedence follows the CeTA certificate (`Artifacts/ttt2/KO7_LPO.cpf`):
eqW 3, recΔ 1, delta 1, app/merge/integrate/void 0, all lex status.

`LPO_KO7` is the one-step generator used by the explicit root calculations.
`LPOOrder_KO7` is its transitive closure and is the exported strict order used
by the termination theorem.  This is a kernel replay of the equal-tail
fragment below, not a claim that Lean parses or replays the external CPF.

Root-precedence cannot fire on `R_int_delta` because integrate and void share
rank 0. The compiled orientation uses subterm through `delta` (rank 1).
-/

open OperatorKO7
open OperatorKO7.LPOSchema
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open MetaSN_KO7

namespace OperatorKO7.MetaLPO

inductive KO7Sym : Type
  | void
  | delta
  | integrate
  | merge
  | app
  | recΔ
  | eqW
  deriving DecidableEq, Repr

/-- CeTA LPO precedence from `KO7_LPO.cpf`. -/
def cetaRank : KO7Sym → Nat
  | .eqW => 3
  | .recΔ => 1
  | .delta => 1
  | .app => 0
  | .merge => 0
  | .integrate => 0
  | .void => 0

def ko7Arity : KO7Sym → Nat
  | .void => 0
  | .delta => 1
  | .integrate => 1
  | .merge => 2
  | .app => 2
  | .recΔ => 3
  | .eqW => 2

def ko7Sig : FOSig where
  σ := KO7Sym
  arity := ko7Arity
  rank := cetaRank

@[simp] theorem ko7Sig_arity : ko7Sig.arity = ko7Arity := rfl
@[simp] theorem ko7Sig_rank : ko7Sig.rank = cetaRank := rfl
@[simp] theorem ko7Sig_σ : ko7Sig.σ = KO7Sym := rfl

def unary (t : FOTerm ko7Sig) : Fin 1 → FOTerm ko7Sig :=
  fun _ => t

def pairArgs (a b : FOTerm ko7Sig) : Fin 2 → FOTerm ko7Sig :=
  fun i => if i.val = 0 then a else b

def tripleArgs (a b c : FOTerm ko7Sig) : Fin 3 → FOTerm ko7Sig :=
  fun i => if i.val = 0 then a else if i.val = 1 then b else c

private theorem fin2_eq_zero_or_one (i : Fin 2) :
    i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
  match i with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr rfl

private theorem fin3_eq_zero_one_or_two (i : Fin 3) :
    i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ := by
  match i with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr (Or.inl rfl)
  | ⟨2, _⟩ => exact Or.inr (Or.inr rfl)

theorem unary_update (t u : FOTerm ko7Sig) :
    @updateArg ko7Sig KO7Sym.delta (unary t) ⟨0, by decide⟩ u = unary u := by
  funext i
  have hi : i = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
  subst hi
  simp [updateArg, unary]

theorem pairArgs_update_left (a a' b : FOTerm ko7Sig) :
    @updateArg ko7Sig KO7Sym.merge (pairArgs a b) ⟨0, by decide⟩ a' = pairArgs a' b := by
  funext i
  rcases fin2_eq_zero_or_one i with hi | hi <;> subst hi <;> simp [updateArg, pairArgs]

theorem pairArgs_update_right (a b b' : FOTerm ko7Sig) :
    @updateArg ko7Sig KO7Sym.merge (pairArgs a b) ⟨1, by decide⟩ b' = pairArgs a b' := by
  funext i
  rcases fin2_eq_zero_or_one i with hi | hi <;> subst hi <;> simp [updateArg, pairArgs]

theorem pairArgs_update_left_app (a a' b : FOTerm ko7Sig) :
    @updateArg ko7Sig KO7Sym.app (pairArgs a b) ⟨0, by decide⟩ a' = pairArgs a' b := by
  funext i
  rcases fin2_eq_zero_or_one i with hi | hi <;> subst hi <;> simp [updateArg, pairArgs]

theorem pairArgs_update_right_app (a b b' : FOTerm ko7Sig) :
    @updateArg ko7Sig KO7Sym.app (pairArgs a b) ⟨1, by decide⟩ b' = pairArgs a b' := by
  funext i
  rcases fin2_eq_zero_or_one i with hi | hi <;> subst hi <;> simp [updateArg, pairArgs]

theorem pairArgs_update_left_eqW (a a' b : FOTerm ko7Sig) :
    @updateArg ko7Sig KO7Sym.eqW (pairArgs a b) ⟨0, by decide⟩ a' = pairArgs a' b := by
  funext i
  rcases fin2_eq_zero_or_one i with hi | hi <;> subst hi <;> simp [updateArg, pairArgs]

theorem pairArgs_update_right_eqW (a b b' : FOTerm ko7Sig) :
    @updateArg ko7Sig KO7Sym.eqW (pairArgs a b) ⟨1, by decide⟩ b' = pairArgs a b' := by
  funext i
  rcases fin2_eq_zero_or_one i with hi | hi <;> subst hi <;> simp [updateArg, pairArgs]

theorem unary_update_integrate (t u : FOTerm ko7Sig) :
    @updateArg ko7Sig KO7Sym.integrate (unary t) ⟨0, by decide⟩ u = unary u := by
  funext i
  have hi : i = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
  subst hi
  simp [updateArg, unary]

theorem tripleArgs_update_zero (a a' b c : FOTerm ko7Sig) :
    @updateArg ko7Sig KO7Sym.recΔ (tripleArgs a b c) ⟨0, by decide⟩ a' =
      tripleArgs a' b c := by
  funext i
  rcases fin3_eq_zero_one_or_two i with hi | hi | hi <;> subst hi <;>
    simp [updateArg, tripleArgs]

theorem tripleArgs_update_one (a b b' c : FOTerm ko7Sig) :
    @updateArg ko7Sig KO7Sym.recΔ (tripleArgs a b c) ⟨1, by decide⟩ b' =
      tripleArgs a b' c := by
  funext i
  rcases fin3_eq_zero_one_or_two i with hi | hi | hi <;> subst hi <;>
    simp [updateArg, tripleArgs]

theorem tripleArgs_update_two (a b c c' : FOTerm ko7Sig) :
    @updateArg ko7Sig KO7Sym.recΔ (tripleArgs a b c) ⟨2, by decide⟩ c' =
      tripleArgs a b c' := by
  funext i
  rcases fin3_eq_zero_one_or_two i with hi | hi | hi <;> subst hi
  · simp [updateArg, tripleArgs]
  · simp [updateArg, tripleArgs]
  · simp [updateArg]
    have hii : (⟨2, by decide⟩ : Fin 3) = (2 : Fin 3) := Fin.ext rfl
    rw [hii, Function.update_self]
    simp [tripleArgs]

def encode : Trace → FOTerm ko7Sig
  | Trace.void => FOTerm.app KO7Sym.void Fin.elim0
  | Trace.delta t => FOTerm.app KO7Sym.delta (unary (encode t))
  | Trace.integrate t => FOTerm.app KO7Sym.integrate (unary (encode t))
  | Trace.merge a b => FOTerm.app KO7Sym.merge (pairArgs (encode a) (encode b))
  | Trace.app a b => FOTerm.app KO7Sym.app (pairArgs (encode a) (encode b))
  | Trace.recΔ b s n => FOTerm.app KO7Sym.recΔ (tripleArgs (encode b) (encode s) (encode n))
  | Trace.eqW a b => FOTerm.app KO7Sym.eqW (pairArgs (encode a) (encode b))

/-- One-step path-order generator on encoded KO7 traces. -/
def LPO_KO7 (s t : Trace) : Prop := LPO ko7Sig (encode s) (encode t)

/-- Transitive strict path order on encoded KO7 traces. -/
def LPOOrder_KO7 (s t : Trace) : Prop := LPOOrder ko7Sig (encode s) (encode t)

theorem lpo_to_lpoOrder_KO7 {s t : Trace} (h : LPO_KO7 s t) :
    LPOOrder_KO7 s t :=
  lpo_to_lpoOrder h

theorem lpoOrder_KO7_transitive : Transitive LPOOrder_KO7 := by
  intro a b c hab hbc
  exact lpoOrder_transitive hab hbc

/-- CeTA assigns integrate and void the same rank, so root-precedence cannot
orient `integrate (delta t) → void`. -/
theorem ceta_root_prec_blocked_on_R_int_delta :
    ¬ ko7Sig.rank KO7Sym.void < ko7Sig.rank KO7Sym.integrate := by
  decide

theorem lpo_delta_arg (t : Trace) : LPO_KO7 (Trace.delta t) t :=
  lpo_subterm (S := ko7Sig) (f := KO7Sym.delta) (unary (encode t)) ⟨0, by decide⟩

theorem lpo_R_int_delta (t : Trace) : LPO_KO7 (Trace.integrate (Trace.delta t)) Trace.void := by
  refine LPO.subGt (S := ko7Sig) (f := KO7Sym.integrate) (i := ⟨0, by decide⟩) ?_
  refine LPO.prec (S := ko7Sig) (f := KO7Sym.delta) (g := KO7Sym.void) ?_
      (fun j => j.elim0)
  decide

theorem lpo_R_merge_void_left (t : Trace) : LPO_KO7 (Trace.merge Trace.void t) t := by
  simpa [LPO_KO7, encode, pairArgs] using
    lpo_subterm (S := ko7Sig) (f := KO7Sym.merge)
      (pairArgs (encode Trace.void) (encode t)) ⟨1, by decide⟩

theorem lpo_R_merge_void_right (t : Trace) : LPO_KO7 (Trace.merge t Trace.void) t := by
  simpa [LPO_KO7, encode, pairArgs] using
    lpo_subterm (S := ko7Sig) (f := KO7Sym.merge)
      (pairArgs (encode t) (encode Trace.void)) ⟨0, by decide⟩

theorem lpo_R_merge_cancel (t : Trace) : LPO_KO7 (Trace.merge t t) t := by
  simpa [LPO_KO7, encode, pairArgs] using
    lpo_subterm (S := ko7Sig) (f := KO7Sym.merge)
      (pairArgs (encode t) (encode t)) ⟨0, by decide⟩

theorem lpo_R_rec_zero (base step : Trace) :
    LPO_KO7 (Trace.recΔ base step Trace.void) base := by
  simpa [LPO_KO7, encode, tripleArgs] using
    lpo_subterm (S := ko7Sig) (f := KO7Sym.recΔ)
      (tripleArgs (encode base) (encode step) (encode Trace.void)) ⟨0, by decide⟩

theorem lpo_R_rec_inner (base step n : Trace) :
    LPO_KO7 (Trace.recΔ base step (Trace.delta n)) (Trace.recΔ base step n) := by
  refine lpo_lex_equal_tail (S := ko7Sig) (f := KO7Sym.recΔ) (k := ⟨2, by decide⟩) ?_ ?_ ?_
  · intro i hi
    have hlt : i.val < 2 := by simpa [ko7Sig, ko7Arity] using hi
    rcases fin3_eq_zero_one_or_two i with h | h | h <;> subst h
    · rfl
    · rfl
    · exact (Nat.lt_irrefl _ hlt).elim
  · exact lpo_delta_arg n
  · intro i hi
    have hgt : 2 < i.val := by simpa [ko7Sig, ko7Arity] using hi
    have : i.val < 3 := i.isLt
    omega

theorem lpo_R_rec_succ (base step n : Trace) :
    LPO_KO7 (Trace.recΔ base step (Trace.delta n))
      (Trace.app step (Trace.recΔ base step n)) := by
  refine LPO.prec (S := ko7Sig) (f := KO7Sym.recΔ) (g := KO7Sym.app) ?_ ?_
  · decide
  · intro j
    cases j using Fin.cases with
    | zero =>
        exact lpo_subterm (S := ko7Sig) (f := KO7Sym.recΔ)
          (tripleArgs (encode base) (encode step) (encode (Trace.delta n)))
          ⟨1, by decide⟩
    | succ j =>
        cases j using Fin.cases with
        | zero => exact lpo_R_rec_inner base step n
        | succ j => exact j.elim0

theorem lpo_R_eq_refl (x : Trace) : LPO_KO7 (Trace.eqW x x) Trace.void := by
  refine LPO.prec (S := ko7Sig) (f := KO7Sym.eqW) (g := KO7Sym.void) ?_
      (fun j => j.elim0)
  decide

theorem lpo_R_eq_to_merge (x y : Trace) : LPO_KO7 (Trace.eqW x y) (Trace.merge x y) := by
  refine LPO.prec (S := ko7Sig) (f := KO7Sym.eqW) (g := KO7Sym.merge) ?_ ?_
  · decide
  · intro j
    cases j using Fin.cases with
    | zero =>
        exact lpo_subterm (S := ko7Sig) (f := KO7Sym.eqW)
          (pairArgs (encode x) (encode y)) ⟨0, by decide⟩
    | succ j =>
        cases j using Fin.cases with
        | zero =>
            exact lpo_subterm (S := ko7Sig) (f := KO7Sym.eqW)
              (pairArgs (encode x) (encode y)) ⟨1, by decide⟩
        | succ j => exact j.elim0

theorem lpo_R_eq_diff (x y : Trace) :
    LPO_KO7 (Trace.eqW x y) (Trace.integrate (Trace.merge x y)) := by
  refine LPO.prec (S := ko7Sig) (f := KO7Sym.eqW) (g := KO7Sym.integrate) ?_ ?_
  · decide
  · intro j
    cases j using Fin.cases with
    | zero => exact lpo_R_eq_to_merge x y
    | succ j => exact j.elim0

theorem lpo_orients_step : ∀ {a b : Trace}, Step a b → LPO_KO7 a b
  | _, _, Step.R_int_delta t => lpo_R_int_delta t
  | _, _, Step.R_merge_void_left t => lpo_R_merge_void_left t
  | _, _, Step.R_merge_void_right t => lpo_R_merge_void_right t
  | _, _, Step.R_merge_cancel t => lpo_R_merge_cancel t
  | _, _, Step.R_rec_zero b s => lpo_R_rec_zero b s
  | _, _, Step.R_rec_succ b s n => lpo_R_rec_succ b s n
  | _, _, Step.R_eq_refl a => lpo_R_eq_refl a
  | _, _, Step.R_eq_diff a b => lpo_R_eq_diff a b

theorem lpo_orients_all_root_rules {a b : Trace} (h : Step a b) : LPO_KO7 a b :=
  lpo_orients_step h

/-- Every KO7 root rule is oriented by the exported transitive order. -/
theorem lpoOrder_orients_step {a b : Trace} (h : Step a b) : LPOOrder_KO7 a b :=
  lpo_to_lpoOrder_KO7 (lpo_orients_step h)

theorem lpo_orients_stepCtxFull {a b : Trace} (h : StepCtxFull a b) : LPO_KO7 a b := by
  induction h with
  | root h => exact lpo_orients_step h
  | delta h ih =>
      rename_i t u
      have hmono :=
        lpo_monotone (S := ko7Sig) (f := KO7Sym.delta) (args := unary (encode t))
          (i := ⟨0, by decide⟩) (s := encode t) (t := encode u) ih
      have hL :
          @updateArg ko7Sig KO7Sym.delta (unary (encode t)) ⟨0, by decide⟩ (encode t) =
            unary (encode t) := by
        simp [updateArg, unary]
      rw [hL, unary_update (encode t) (encode u)] at hmono
      simpa [LPO_KO7, encode] using hmono
  | integrate h ih =>
      rename_i t u
      have hmono :=
        lpo_monotone (S := ko7Sig) (f := KO7Sym.integrate) (args := unary (encode t))
          (i := ⟨0, by decide⟩) (s := encode t) (t := encode u) ih
      have hL :
          @updateArg ko7Sig KO7Sym.integrate (unary (encode t)) ⟨0, by decide⟩ (encode t) =
            unary (encode t) := by
        simp [updateArg, unary]
      rw [hL, unary_update_integrate (encode t) (encode u)] at hmono
      simpa [LPO_KO7, encode] using hmono
  | mergeL h ih =>
      rename_i a a' b
      have hmono :=
        lpo_monotone (S := ko7Sig) (f := KO7Sym.merge)
          (args := pairArgs (encode a) (encode b)) (i := ⟨0, by decide⟩)
          (s := encode a) (t := encode a') ih
      have hL :
          @updateArg ko7Sig KO7Sym.merge (pairArgs (encode a) (encode b)) ⟨0, by decide⟩
            (encode a) = pairArgs (encode a) (encode b) := by
        simp [updateArg, pairArgs]
      rw [hL, pairArgs_update_left (encode a) (encode a') (encode b)] at hmono
      simpa [LPO_KO7, encode] using hmono
  | mergeR h ih =>
      rename_i a b b'
      have hmono :=
        lpo_monotone (S := ko7Sig) (f := KO7Sym.merge)
          (args := pairArgs (encode a) (encode b)) (i := ⟨1, by decide⟩)
          (s := encode b) (t := encode b') ih
      have hL :
          @updateArg ko7Sig KO7Sym.merge (pairArgs (encode a) (encode b)) ⟨1, by decide⟩
            (encode b) = pairArgs (encode a) (encode b) := by
        simp [updateArg, pairArgs]
      rw [hL, pairArgs_update_right (encode a) (encode b) (encode b')] at hmono
      simpa [LPO_KO7, encode] using hmono
  | appL h ih =>
      rename_i a a' b
      have hmono :=
        lpo_monotone (S := ko7Sig) (f := KO7Sym.app)
          (args := pairArgs (encode a) (encode b)) (i := ⟨0, by decide⟩)
          (s := encode a) (t := encode a') ih
      have hL :
          @updateArg ko7Sig KO7Sym.app (pairArgs (encode a) (encode b)) ⟨0, by decide⟩
            (encode a) = pairArgs (encode a) (encode b) := by
        simp [updateArg, pairArgs]
      rw [hL, pairArgs_update_left_app (encode a) (encode a') (encode b)] at hmono
      simpa [LPO_KO7, encode] using hmono
  | appR h ih =>
      rename_i a b b'
      have hmono :=
        lpo_monotone (S := ko7Sig) (f := KO7Sym.app)
          (args := pairArgs (encode a) (encode b)) (i := ⟨1, by decide⟩)
          (s := encode b) (t := encode b') ih
      have hL :
          @updateArg ko7Sig KO7Sym.app (pairArgs (encode a) (encode b)) ⟨1, by decide⟩
            (encode b) = pairArgs (encode a) (encode b) := by
        simp [updateArg, pairArgs]
      rw [hL, pairArgs_update_right_app (encode a) (encode b) (encode b')] at hmono
      simpa [LPO_KO7, encode] using hmono
  | recB h ih =>
      rename_i b b' s n
      have hmono :=
        lpo_monotone (S := ko7Sig) (f := KO7Sym.recΔ)
          (args := tripleArgs (encode b) (encode s) (encode n)) (i := ⟨0, by decide⟩)
          (s := encode b) (t := encode b') ih
      have hL :
          @updateArg ko7Sig KO7Sym.recΔ (tripleArgs (encode b) (encode s) (encode n))
            ⟨0, by decide⟩ (encode b) = tripleArgs (encode b) (encode s) (encode n) := by
        simp [updateArg, tripleArgs]
      rw [hL, tripleArgs_update_zero (encode b) (encode b') (encode s) (encode n)] at hmono
      simpa [LPO_KO7, encode] using hmono
  | recS h ih =>
      rename_i b s s' n
      have hmono :=
        lpo_monotone (S := ko7Sig) (f := KO7Sym.recΔ)
          (args := tripleArgs (encode b) (encode s) (encode n)) (i := ⟨1, by decide⟩)
          (s := encode s) (t := encode s') ih
      have hL :
          @updateArg ko7Sig KO7Sym.recΔ (tripleArgs (encode b) (encode s) (encode n))
            ⟨1, by decide⟩ (encode s) = tripleArgs (encode b) (encode s) (encode n) := by
        simp [updateArg, tripleArgs]
      rw [hL, tripleArgs_update_one (encode b) (encode s) (encode s') (encode n)] at hmono
      simpa [LPO_KO7, encode] using hmono
  | recN h ih =>
      rename_i b s n n'
      have hmono :=
        lpo_monotone (S := ko7Sig) (f := KO7Sym.recΔ)
          (args := tripleArgs (encode b) (encode s) (encode n)) (i := ⟨2, by decide⟩)
          (s := encode n) (t := encode n') ih
      have hL :
          @updateArg ko7Sig KO7Sym.recΔ (tripleArgs (encode b) (encode s) (encode n))
            ⟨2, by decide⟩ (encode n) = tripleArgs (encode b) (encode s) (encode n) := by
        simp [updateArg, tripleArgs]
      rw [hL, tripleArgs_update_two (encode b) (encode s) (encode n) (encode n')] at hmono
      simpa [LPO_KO7, encode] using hmono
  | eqWL h ih =>
      rename_i a a' b
      have hmono :=
        lpo_monotone (S := ko7Sig) (f := KO7Sym.eqW)
          (args := pairArgs (encode a) (encode b)) (i := ⟨0, by decide⟩)
          (s := encode a) (t := encode a') ih
      have hL :
          @updateArg ko7Sig KO7Sym.eqW (pairArgs (encode a) (encode b)) ⟨0, by decide⟩
            (encode a) = pairArgs (encode a) (encode b) := by
        simp [updateArg, pairArgs]
      rw [hL, pairArgs_update_left_eqW (encode a) (encode a') (encode b)] at hmono
      simpa [LPO_KO7, encode] using hmono
  | eqWR h ih =>
      rename_i a b b'
      have hmono :=
        lpo_monotone (S := ko7Sig) (f := KO7Sym.eqW)
          (args := pairArgs (encode a) (encode b)) (i := ⟨1, by decide⟩)
          (s := encode b) (t := encode b') ih
      have hL :
          @updateArg ko7Sig KO7Sym.eqW (pairArgs (encode a) (encode b)) ⟨1, by decide⟩
            (encode b) = pairArgs (encode a) (encode b) := by
        simp [updateArg, pairArgs]
      rw [hL, pairArgs_update_right_eqW (encode a) (encode b) (encode b')] at hmono
      simpa [LPO_KO7, encode] using hmono

/-- Every one-step full-context reduction is oriented by the exported
transitive path order. -/
theorem lpoOrder_orients_stepCtxFull {a b : Trace} (h : StepCtxFull a b) :
    LPOOrder_KO7 a b :=
  lpo_to_lpoOrder_KO7 (lpo_orients_stepCtxFull h)

theorem wf_StepCtxFull_via_lpo :
    WellFounded (fun a b : Trace => StepCtxFull b a) := by
  let r : FOTerm ko7Sig → FOTerm ko7Sig → Prop := LPOOrderRev
  have hsub :
      Subrelation (fun a b : Trace => StepCtxFull b a)
        (InvImage r encode) := by
    intro a b h
    exact lpoOrder_orients_stepCtxFull h
  exact Subrelation.wf hsub (InvImage.wf encode lpoOrder_wellFounded)

/-- Subterm is an LPO axiom; no affine global orienter of `Step` exists. -/
theorem lpo_imports_subterm_property :
    (∀ a b : Trace, LPO_KO7 (Trace.app a b) b) ∧
    (∀ M : AffineMeasure ko7Schema, ¬ GlobalOrients ko7System M.eval (· < ·)) := by
  refine ⟨?_, fun M => no_global_orients_affine (Sys := ko7System) M⟩
  intro a b
  exact lpo_subterm (S := ko7Sig) (f := KO7Sym.app)
    (pairArgs (encode a) (encode b)) ⟨1, by decide⟩

/-- The exported transitive order imports the same subterm property while the
direct affine class remains impossible. -/
theorem lpoOrder_imports_subterm_property :
    (∀ a b : Trace, LPOOrder_KO7 (Trace.app a b) b) ∧
    (∀ M : AffineMeasure ko7Schema, ¬ GlobalOrients ko7System M.eval (· < ·)) := by
  refine ⟨?_, fun M => no_global_orients_affine (Sys := ko7System) M⟩
  intro a b
  exact lpoOrder_subterm (S := ko7Sig) (f := KO7Sym.app)
    (pairArgs (encode a) (encode b)) ⟨1, by decide⟩

theorem lpo_not_direct_measure (μ : Trace → Nat)
    (hrep : ∀ {s t : Trace}, LPO_KO7 s t → μ t < μ s) :
    ¬ ∃ M : AffineMeasure ko7Schema, M.eval = μ :=
  global_orienter_not_affine_representable (Sys := ko7System) μ
    (fun {_ _} hstep => hrep (lpo_orients_step hstep))

theorem lpoOrder_not_direct_measure (μ : Trace → Nat)
    (hrep : ∀ {s t : Trace}, LPOOrder_KO7 s t → μ t < μ s) :
    ¬ ∃ M : AffineMeasure ko7Schema, M.eval = μ :=
  global_orienter_not_affine_representable (Sys := ko7System) μ
    (fun {_ _} hstep => hrep (lpoOrder_orients_step hstep))

end OperatorKO7.MetaLPO
