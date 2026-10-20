/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.ProofSearchBoundary
import Mathlib.Tactic

/-!
# The O3 `rho` episode: exact identity, counterexamples, and the trace

The mathematical content of the O3 orientation attempt on the free two-rule
recursor schema, with the promotion/migration analysis attached.

Terms are built from `zero`, `succ`, the wrapper `G`, and the recursor `F`.
The rewrite under study is

`F(b, s, succ n) → G(s, F(b, s, n))`.

* `rho` counts the `F`-nodes whose third argument is `succ`-headed.  The
  exact step identity over `ℤ` is

  `rho (G s (F b s n)) - rho (F b s (succ n)) = rho s + eps n - 1`,

  where `eps n = 1` on `succ`-headed `n` and `0` otherwise.  The two summands
  are the two independent failure reasons: the copied payload `rho s`, and
  the residual call still counted by `eps n`.
* The counterexample `F(0,0,S(S(0))) → G(0,F(0,0,S(0)))` keeps `rho` at `1`;
  the naive proposal predicts a drop to `0`, and the archived correction
  `rho(after) = rho(before) - 1 + rho(s)` also predicts `0`.  Both fail by
  `decide`.
* The positive control `polyM`, `polyM (F b s n) = M b + (M s + 2)*(M n + 1)`,
  orients the step with margin exactly `1` and the base rule with margin
  `M s + 2`: the failure of `rho` does not generalize to all whole-term
  interpretations.

The trace fixture tracks two constraints, `k_dup` (payload copied) and
`k_nested` (residual call counted on `succ`-headed `n`), across the four
states diagnose → naive → corrected → exact.  The correction
`CorrectionDischarges k_dup` while `PromotionMigrates k_nested`, so the
corrected state still fails `Consumes`; the first diagnostic-consumption
boundary is the edge `t0 → t1`.

Trust: kernel only, Mathlib baseline.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ProofSearchBoundary.O3Rho

open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.LicensedBoundaryCalculus
open OperatorKO7.Meta.ProofSearchBoundary

/-- Terms of the free two-rule recursor schema. -/
inductive O3Term where
  | zero
  | succ : O3Term → O3Term
  | G : O3Term → O3Term → O3Term
  | F : O3Term → O3Term → O3Term → O3Term
  deriving DecidableEq, Repr

open O3Term

/-- The residual-successor indicator: `1` exactly on `succ`-headed terms. -/
def eps : O3Term → Nat
  | .succ _ => 1
  | _ => 0

/-- The O3 counting measure: the number of `F`-nodes with `succ`-headed third
argument. -/
def rho : O3Term → Nat
  | .zero => 0
  | .succ t => rho t
  | .G s t => rho s + rho t
  | .F b s n => eps n + rho b + rho s + rho n

/-- The exact step identity: the change of `rho` across
`F(b,s,S n) → G(s,F(b,s,n))` is `rho s + eps n - 1`. -/
theorem rho_exact_identity (b s n : O3Term) :
    ((rho (G s (F b s n)) : ℤ) - (rho (F b s (succ n)) : ℤ)) =
      (rho s : ℤ) + (eps n : ℤ) - 1 := by
  simp only [rho, eps]
  omega

/-- The counterexample needing no complex payload: the before-term counts
`1`. -/
theorem rho_counterexample_before :
    rho (F zero zero (succ (succ zero))) = 1 := by
  decide

/-- ... and the after-term still counts `1`. -/
theorem rho_counterexample_after :
    rho (G zero (F zero zero (succ zero))) = 1 := by
  decide

/-- The naive proposal (`rho` drops by exactly `1`) is false. -/
theorem naiveDrop_identity_fails :
    ∃ b s n : O3Term,
      (rho (G s (F b s n)) : ℤ) ≠ (rho (F b s (succ n)) : ℤ) - 1 := by
  refine ⟨zero, zero, succ zero, ?_⟩
  decide

/-- The archived correction (`rho(after) = rho(before) - 1 + rho(s)`) is
false: it predicts `0` on the counterexample. -/
theorem correctedDup_identity_fails :
    ∃ b s n : O3Term,
      (rho (G s (F b s n)) : ℤ) ≠
        (rho (F b s (succ n)) : ℤ) - 1 + (rho s : ℤ) := by
  refine ⟨zero, zero, succ zero, ?_⟩
  decide

/-- The exact identity specializes to the counterexample: the change is
`0`, not `-1`. -/
theorem rho_counterexample_exact :
    ((rho (G zero (F zero zero (succ zero))) : ℤ) -
        (rho (F zero zero (succ (succ zero))) : ℤ)) = 0 := by
  decide

/-- The valid whole-term repair: the coupled natural-number polynomial. -/
def polyM : O3Term → Nat
  | .zero => 0
  | .succ t => polyM t + 1
  | .G s t => polyM s + polyM t + 1
  | .F b s n => polyM b + (polyM s + 2) * (polyM n + 1)

/-- The step margin is exactly `1`. -/
theorem polyM_step_margin (b s n : O3Term) :
    polyM (F b s (succ n)) = polyM (G s (F b s n)) + 1 := by
  simp only [polyM]
  ring

/-- The base-rule margin is `polyM s + 2`. -/
theorem polyM_base_margin (b s : O3Term) :
    polyM (F b s zero) = polyM b + (polyM s + 2) := by
  simp only [polyM]
  ring

/-- The polynomial strictly decreases across the recursor step. -/
theorem polyM_step_strict (b s n : O3Term) :
    polyM (G s (F b s n)) < polyM (F b s (succ n)) := by
  rw [polyM_step_margin]
  exact Nat.lt_succ_self _

/-- The polynomial is strictly increasing along the successor. -/
theorem polyM_succ_strict (t : O3Term) : polyM t < polyM (succ t) := by
  simp only [polyM]
  exact Nat.lt_succ_self _

/-! ## The manuscript's first instance: the copied payload alone -/

/-- The payload `q = F(0, 0, S(0))` of the manuscript's first instance. -/
def payloadQ : O3Term := F zero zero (succ zero)

/-- `F(0, q, S(0)) → G(q, F(0, q, 0))` keeps `rho` at `2`. -/
theorem rho_payload_counterexample :
    rho (F zero payloadQ (succ zero)) = 2 ∧
      rho (G payloadQ (F zero payloadQ zero)) = 2 := by
  decide

/-- On that instance the residual call is not `succ`-headed, so the copied
payload alone refutes the naive drop. -/
theorem naiveDrop_fails_on_payload :
    (rho (G payloadQ (F zero payloadQ zero)) : ℤ) ≠
      (rho (F zero payloadQ (succ zero)) : ℤ) - 1 := by
  decide

/-! ## Contextual termination of the two-rule system

The manuscript states that `polyM` is strictly monotone in each constructor
argument and yields a contextual termination proof for the two rules
`F(b, s, 0) → b` and `F(b, s, S(n)) → G(s, F(b, s, n))`. -/

/-- The two root rules. -/
inductive O3Root : O3Term → O3Term → Prop
  | base (b s : O3Term) : O3Root (F b s zero) b
  | step (b s n : O3Term) : O3Root (F b s (succ n)) (G s (F b s n))

/-- The contextual closure: a root step at any position. -/
inductive O3Ctx : O3Term → O3Term → Prop
  | root {t u : O3Term} : O3Root t u → O3Ctx t u
  | underSucc {t u : O3Term} : O3Ctx t u → O3Ctx (succ t) (succ u)
  | underGLeft {t u : O3Term} (v : O3Term) :
      O3Ctx t u → O3Ctx (G t v) (G u v)
  | underGRight {t u : O3Term} (v : O3Term) :
      O3Ctx t u → O3Ctx (G v t) (G v u)
  | underF1 {t u : O3Term} (s n : O3Term) :
      O3Ctx t u → O3Ctx (F t s n) (F u s n)
  | underF2 {t u : O3Term} (b n : O3Term) :
      O3Ctx t u → O3Ctx (F b t n) (F b u n)
  | underF3 {t u : O3Term} (b s : O3Term) :
      O3Ctx t u → O3Ctx (F b s t) (F b s u)

/-- Every contextual step strictly lowers `polyM`: the root margins plus strict
monotonicity in every argument position. -/
theorem polyM_lt_of_o3Ctx {t u : O3Term} (h : O3Ctx t u) :
    polyM u < polyM t := by
  induction h with
  | root hr =>
      cases hr with
      | base b s =>
          rw [polyM_base_margin]
          omega
      | step b s n => exact polyM_step_strict b s n
  | underSucc _ ih =>
      simp only [polyM]
      omega
  | underGLeft v _ ih =>
      simp only [polyM]
      omega
  | underGRight v _ ih =>
      simp only [polyM]
      omega
  | underF1 s n _ ih =>
      simp only [polyM]
      exact Nat.add_lt_add_right ih _
  | underF2 b n _ ih =>
      simp only [polyM]
      exact Nat.add_lt_add_left
        (Nat.mul_lt_mul_of_pos_right (Nat.add_lt_add_right ih 2)
          (Nat.succ_pos _)) _
  | underF3 b s _ ih =>
      simp only [polyM]
      exact Nat.add_lt_add_left
        (Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_right ih 1)
          (by omega)) _

/-- The contextual two-rule relation terminates. -/
theorem o3Ctx_wellFounded : WellFounded (fun u t : O3Term => O3Ctx t u) :=
  Subrelation.wf (q := fun u t : O3Term => O3Ctx t u)
    (r := InvImage (· < ·) polyM) (fun h => polyM_lt_of_o3Ctx h)
    (measure polyM).wf

/-! ## The four-state O3 trace with two tracked constraints -/

inductive O3Constraint where
  | kDup
  | kNested
  deriving DecidableEq, Repr

inductive O3Proposal where
  | diagnose
  | naiveDrop
  | correctedDup
  | exactIdentity
  deriving DecidableEq, Repr

inductive O3Target where
  | recursorStepSN
  deriving DecidableEq, Repr

inductive O3Obligation where
  | strictDropAllTriplets
  deriving DecidableEq, Repr

abbrev O3State :=
  ProofSearchState O3Target O3Constraint O3Obligation O3Proposal

/-- Both constraints apply to every drop claim across the copying step; the
diagnostic state makes no drop claim. -/
def O3Applicable :
    O3Constraint → O3Target → List O3Obligation → O3Proposal → Prop
  | .kDup, _, _, .naiveDrop => True
  | .kDup, _, _, .correctedDup => True
  | .kDup, _, _, .exactIdentity => True
  | .kNested, _, _, .naiveDrop => True
  | .kNested, _, _, .correctedDup => True
  | .kNested, _, _, .exactIdentity => True
  | _, _, _, _ => False

/-- `naiveDrop` handles neither constraint; `correctedDup` handles the
payload duplication only; `exactIdentity` handles both. -/
def O3Handles :
    O3Constraint → O3Target → List O3Obligation → O3Proposal → Prop
  | .kDup, _, _, .correctedDup => True
  | .kDup, _, _, .exactIdentity => True
  | .kNested, _, _, .exactIdentity => True
  | _, _, _, _ => False

/-- The audit rejects each proposal under each applicable unhandled
constraint. -/
def O3AuditRejects :
    O3Constraint → O3Target → List O3Obligation → O3Proposal → Prop
  | .kDup, _, _, .naiveDrop => True
  | .kNested, _, _, .naiveDrop => True
  | .kNested, _, _, .correctedDup => True
  | _, _, _, _ => False

/-- The two constraints tracked across the O3 trace. -/
def o3Blockers : List O3Constraint :=
  [.kDup, .kNested]

/-- The open obligation carried by the O3 trace. -/
def o3Obligations : List O3Obligation :=
  [.strictDropAllTriplets]

/-- Diagnostic state: the constraints are recorded, no drop claim is made. -/
def t0 : O3State where
  target := .recursorStepSN
  known := o3Blockers
  openObligations := o3Obligations
  proposal := .diagnose
  status := .«open»

/-- The naive proposal, certified: "`rho` drops by exactly `1`". -/
def t1 : O3State where
  target := .recursorStepSN
  known := o3Blockers
  openObligations := o3Obligations
  proposal := .naiveDrop
  status := .certified

/-- The archived correction, certified: "`rho(after) = rho(before) - 1 +
rho(s)`". -/
def t2 : O3State where
  target := .recursorStepSN
  known := o3Blockers
  openObligations := o3Obligations
  proposal := .correctedDup
  status := .certified

/-- The exact identity, certified. -/
def t3 : O3State where
  target := .recursorStepSN
  known := o3Blockers
  openObligations := o3Obligations
  proposal := .exactIdentity
  status := .certified

/-- The O3 proposal dynamics. -/
inductive O3NextProposal : O3State → O3State → Prop
  | first : O3NextProposal t0 t1
  | second : O3NextProposal t1 t2
  | third : O3NextProposal t2 t3

noncomputable instance : DecidablePred (Consumes O3Applicable O3Handles) := by
  intro s
  exact Classical.propDecidable _

theorem t0_consumes : Consumes O3Applicable O3Handles t0 := by
  simp [Consumes, t0, o3Blockers, o3Obligations, O3Applicable, O3Handles]

theorem t1_not_consumes : ¬ Consumes O3Applicable O3Handles t1 := by
  simp [Consumes, t1, o3Blockers, o3Obligations, O3Applicable, O3Handles]

theorem t2_not_consumes : ¬ Consumes O3Applicable O3Handles t2 := by
  simp [Consumes, t2, o3Blockers, o3Obligations, O3Applicable, O3Handles]

theorem t3_consumes : Consumes O3Applicable O3Handles t3 := by
  simp [Consumes, t3, o3Blockers, o3Obligations, O3Applicable, O3Handles]

/-- The O3 audit is sound. -/
theorem o3AuditRejects_sound : AuditSound O3Handles O3AuditRejects := by
  intro k T O h hrej hhandles
  cases k <;> cases h <;>
    simp [O3AuditRejects] at hrej <;> simp [O3Handles] at hhandles

/-- The naive state is a self-application gap under both constraints. -/
theorem t1_selfApplicationGap :
    SelfApplicationGap O3Applicable O3AuditRejects t1 := by
  refine ⟨.kDup, ?_, ?_, ?_⟩ <;>
    simp [t1, o3Blockers, O3Applicable, O3AuditRejects]

/-- The corrected state is still a self-application gap, now under the
nested-residual constraint alone. -/
theorem t2_selfApplicationGap :
    SelfApplicationGap O3Applicable O3AuditRejects t2 := by
  refine ⟨.kNested, ?_, ?_, ?_⟩ <;>
    simp [t2, o3Blockers, O3Applicable, O3AuditRejects]

/-- The correction truly removes the payload-duplication promotion. -/
theorem correction_discharges_dup :
    CorrectionDischarges O3Applicable O3Handles .kDup t1 t2 := by
  refine ⟨?_, ?_, ?_, .inl ?_⟩ <;>
    simp [t1, t2, o3Blockers, O3Applicable, O3Handles]

/-- The correction does not remove the nested-residual promotion: it
migrates it. -/
theorem promotion_migrates_nested :
    PromotionMigrates O3Applicable O3Handles .kNested t1 t2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [t1, t2, o3Blockers, O3Applicable, O3Handles]

/-- Migration implies the corrected state still fails `Consumes`: the generic
route, not a recomputation. -/
theorem t2_not_consumes_via_migration :
    ¬ Consumes O3Applicable O3Handles t2 :=
  promotionMigrates_not_consumes O3Applicable O3Handles
    promotion_migrates_nested

/-- The naive state commits without consuming. -/
theorem t1_unsupportedPromotion :
    UnsupportedPromotion O3Applicable O3Handles t1 :=
  ⟨rfl, t1_not_consumes⟩

/-- The corrected state still commits without consuming. -/
theorem t2_unsupportedPromotion :
    UnsupportedPromotion O3Applicable O3Handles t2 :=
  ⟨rfl, t2_not_consumes⟩

/-- The exact-identity state is licensed. -/
theorem t3_licensed : Licensed O3Applicable O3Handles t3 :=
  fun _ => t3_consumes

/-- The explicit trace from the diagnostic state to the corrected state. -/
def o3Trace : FinitePath O3NextProposal t0 t2 :=
  .cons O3NextProposal.first
    (.cons O3NextProposal.second (.refl t2))

/-- Generic first-crossing extraction over the O3 trace. -/
theorem o3_extracted_failure :
    Nonempty
      (FailureObject O3NextProposal (Consumes O3Applicable O3Handles)
        t0 t2 o3Trace) := by
  exact FailureObject.of_explicit_path o3Trace t0_consumes t2_not_consumes

/-- The concrete first-crossing object: the boundary edge is exactly the
first proposal edge `t0 → t1`. -/
def o3FirstFailure :
    FailureObject O3NextProposal (Consumes O3Applicable O3Handles)
      t0 t2 o3Trace where
  lastSafe := t0
  firstFail := t1
  sourceSafe := t0_consumes
  endpointFails := t2_not_consumes
  safePrefix := .refl t0
  safePrefixProof := .refl t0_consumes
  crossing := ⟨O3NextProposal.first, t0_consumes, t1_not_consumes⟩
  suffix := .cons O3NextProposal.second (.refl t2)
  decomposition := rfl

theorem o3FirstFailure_lastSafe : o3FirstFailure.lastSafe = t0 := rfl

theorem o3FirstFailure_firstFail : o3FirstFailure.firstFail = t1 := rfl

theorem o3FirstFailure_crossing :
    BoundaryEdge O3NextProposal (Consumes O3Applicable O3Handles) t0 t1 :=
  o3FirstFailure.crossing

theorem o3_prescription_not_persistent :
    ¬ PrescriptionPersistent O3Applicable O3Handles O3NextProposal t0 := by
  simpa [PrescriptionPersistent] using FailureObject.not_box o3FirstFailure

/-! ## Audit of the answer key

`O3Handles` is a table.  The theorem `o3Handles_answer_key` shows that on every
applicable pair it agrees with a semantic predicate computed from `rho`: a
proposal handles `kDup` when its claimed change of `rho` is exact on every
instance whose recursive call is not `succ`-headed, and handles `kNested` when
it is exact on every instance whose payload counts `0`. -/

/-- The actual change of `rho` across the recursor step. -/
def actualDelta (b s n : O3Term) : ℤ :=
  (rho (G s (F b s n)) : ℤ) - (rho (F b s (succ n)) : ℤ)

theorem actualDelta_eq (b s n : O3Term) :
    actualDelta b s n = (rho s : ℤ) + (eps n : ℤ) - 1 :=
  rho_exact_identity b s n

/-- The change of `rho` each proposal claims; the diagnostic state claims
nothing. -/
def claimedDelta : O3Proposal → O3Term → O3Term → O3Term → ℤ
  | .diagnose, b, s, n => actualDelta b s n
  | .naiveDrop, _, _, _ => -1
  | .correctedDup, _, s, _ => (rho s : ℤ) - 1
  | .exactIdentity, _, s, n => (rho s : ℤ) + (eps n : ℤ) - 1

/-- The semantic reading of handling. -/
def SemanticHandles : O3Constraint → O3Proposal → Prop
  | .kDup, p => ∀ b s n, eps n = 0 → actualDelta b s n = claimedDelta p b s n
  | .kNested, p => ∀ b s n, rho s = 0 → actualDelta b s n = claimedDelta p b s n

/-- The table `O3Handles` agrees with the semantic reading on every applicable
pair. -/
theorem o3Handles_answer_key (k : O3Constraint) (T : O3Target)
    (O : List O3Obligation) (p : O3Proposal) (happ : O3Applicable k T O p) :
    O3Handles k T O p ↔ SemanticHandles k p := by
  cases k <;> cases p
  · exact happ.elim
  · refine ⟨fun h => h.elim, fun h => ?_⟩
    exact absurd (h zero payloadQ zero rfl) (by decide)
  · refine ⟨fun _ b s n hn => ?_, fun _ => trivial⟩
    rw [actualDelta_eq]
    show (rho s : ℤ) + (eps n : ℤ) - 1 = (rho s : ℤ) - 1
    rw [hn]
    simp
  · exact ⟨fun _ b s n _ => actualDelta_eq b s n, fun _ => trivial⟩
  · exact happ.elim
  · refine ⟨fun h => h.elim, fun h => ?_⟩
    exact absurd (h zero zero (succ zero) rfl) (by decide)
  · refine ⟨fun h => h.elim, fun h => ?_⟩
    exact absurd (h zero zero (succ zero) rfl) (by decide)
  · exact ⟨fun _ b s n _ => actualDelta_eq b s n, fun _ => trivial⟩

end OperatorKO7.Meta.ProofSearchBoundary.O3Rho
