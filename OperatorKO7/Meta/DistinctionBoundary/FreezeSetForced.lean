/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.DistinctionBoundary.ContextualConfluence
import OperatorKO7.Meta.ContextClosed_SN_Full
import OperatorKO7.Meta.Rewriting.CriticalPairLemma

/-!
# Constructor-selective contextual closure for the equality-guarded KO7 relation

`CtxOn S R` closes a root relation `R` exactly under the constructor positions
selected by `S`.  The relation used in this file is the surgical eight-rule
relation `EqGuardedStep`, not a SafeStep relation.

The first half of Weld 1 is unconditional: enabling congruence below `eqW`
transports the compiled contextual instability witness, while strong
normalization is inherited from the full contextual kernel relation.

The second half resolves the roadmap targets with a correction. W1-B as
originally stated (`eqW ∉ S` alone suffices for confluence) is FALSE:
`R_rec_succ` writes its contractum under an `app` head, so thawing `recD`
while freezing `app` produces an unjoinable peak
(`recD_thaw_app_freeze_breaks_confluence`). The corrected crown is

`ConfluentOn S EqGuardedStep ↔ (¬ S .eqW ∧ (S .recD → S .app))`

(`confluentOn_eqGuarded_iff`), proved by a complete local peak enumeration
plus inherited strong normalization and an `Acc`-recursion Newman diamond.
At full thaw of everything except `eqW`, the original least-freeze reading
survives verbatim (`eqW_least_freeze_at_full_thaw`).

Relation: `CtxOn S EqGuardedStep` (constructor-selective contextual closure of
the surgical equality-guarded root relation). Closure:
`Relation.ReflTransGen`. Trust: kernel only, Mathlib baseline.
-/

set_option autoImplicit false

open OperatorKO7 Trace
open OperatorKO7.EqGuardedConfluence
open MetaSN_KO7

namespace OperatorKO7.Meta.DistinctionBoundary.FreezeSetForced

/-- The seven constructor heads whose immediate argument positions can be
enabled or frozen in a constructor-selective contextual closure. -/
inductive Ctor where
  | void
  | delta
  | integrate
  | merge
  | app
  | recD
  | eqW
  -- D3: dropped `deriving DecidableEq, Repr`. Repo grep found no dependents
  -- of the emitted instances; they were public and unused.

/-- Constructor-selective contextual closure of `R`.

`root` is always available.  Each of the eleven congruence constructors is
available exactly when the corresponding constructor head belongs to `S`.
The nullary constructor `void` has no congruence position. -/
inductive CtxOn (S : Ctor → Prop) (R : Trace → Trace → Prop) : Trace → Trace → Prop
  | root {a b : Trace} : R a b → CtxOn S R a b
  | delta {t u : Trace} (enabled : S .delta) :
      CtxOn S R t u → CtxOn S R (.delta t) (.delta u)
  | integrate {t u : Trace} (enabled : S .integrate) :
      CtxOn S R t u → CtxOn S R (.integrate t) (.integrate u)
  | mergeL {a a' b : Trace} (enabled : S .merge) :
      CtxOn S R a a' → CtxOn S R (.merge a b) (.merge a' b)
  | mergeR {a b b' : Trace} (enabled : S .merge) :
      CtxOn S R b b' → CtxOn S R (.merge a b) (.merge a b')
  | appL {a a' b : Trace} (enabled : S .app) :
      CtxOn S R a a' → CtxOn S R (.app a b) (.app a' b)
  | appR {a b b' : Trace} (enabled : S .app) :
      CtxOn S R b b' → CtxOn S R (.app a b) (.app a b')
  | recB {b b' s n : Trace} (enabled : S .recD) :
      CtxOn S R b b' → CtxOn S R (.recΔ b s n) (.recΔ b' s n)
  | recS {b s s' n : Trace} (enabled : S .recD) :
      CtxOn S R s s' → CtxOn S R (.recΔ b s n) (.recΔ b s' n)
  | recN {b s n n' : Trace} (enabled : S .recD) :
      CtxOn S R n n' → CtxOn S R (.recΔ b s n) (.recΔ b s n')
  | eqWL {a a' b : Trace} (enabled : S .eqW) :
      CtxOn S R a a' → CtxOn S R (.eqW a b) (.eqW a' b)
  | eqWR {a b b' : Trace} (enabled : S .eqW) :
      CtxOn S R b b' → CtxOn S R (.eqW a b) (.eqW a b')

/-- Reflexive-transitive reduction under the constructor-selective closure. -/
abbrev CtxStarOn (S : Ctor → Prop) (R : Trace → Trace → Prop) : Trace → Trace → Prop :=
  Relation.ReflTransGen (CtxOn S R)

/-- Confluence of the constructor-selective contextual closure of `R`. -/
def ConfluentOn (S : Ctor → Prop) (R : Trace → Trace → Prop) : Prop :=
  ∀ a b c : Trace,
    CtxStarOn S R a b →
    CtxStarOn S R a c →
    ∃ d : Trace, CtxStarOn S R b d ∧ CtxStarOn S R c d

/-- Reverse of the constructor-selective contextual relation. -/
def CtxOnRev (S : Ctor → Prop) (R : Trace → Trace → Prop) : Trace → Trace → Prop :=
  fun a b => CtxOn S R b a

/-- Every constructor-selective equality-guarded step is a full contextual
kernel step.  This is the load-bearing transport used for inherited strong
normalization. -/
theorem ctxOn_eqGuarded_sub_stepCtxFull (S : Ctor → Prop) :
    ∀ {a b : Trace}, CtxOn S EqGuardedStep a b → StepCtxFull a b
  | _, _, .root h => StepCtxFull.root (eqGuarded_sub_step h)
  | _, _, .delta _ h => StepCtxFull.delta (ctxOn_eqGuarded_sub_stepCtxFull S h)
  | _, _, .integrate _ h => StepCtxFull.integrate (ctxOn_eqGuarded_sub_stepCtxFull S h)
  | _, _, .mergeL _ h => StepCtxFull.mergeL (ctxOn_eqGuarded_sub_stepCtxFull S h)
  | _, _, .mergeR _ h => StepCtxFull.mergeR (ctxOn_eqGuarded_sub_stepCtxFull S h)
  | _, _, .appL _ h => StepCtxFull.appL (ctxOn_eqGuarded_sub_stepCtxFull S h)
  | _, _, .appR _ h => StepCtxFull.appR (ctxOn_eqGuarded_sub_stepCtxFull S h)
  | _, _, .recB _ h => StepCtxFull.recB (ctxOn_eqGuarded_sub_stepCtxFull S h)
  | _, _, .recS _ h => StepCtxFull.recS (ctxOn_eqGuarded_sub_stepCtxFull S h)
  | _, _, .recN _ h => StepCtxFull.recN (ctxOn_eqGuarded_sub_stepCtxFull S h)
  | _, _, .eqWL _ h => StepCtxFull.eqWL (ctxOn_eqGuarded_sub_stepCtxFull S h)
  | _, _, .eqWR _ h => StepCtxFull.eqWR (ctxOn_eqGuarded_sub_stepCtxFull S h)

/-- Strong normalization of every constructor-selective equality-guarded
closure, inherited as a subrelation of `StepCtxFullRev`. -/
theorem wf_ctxOn_eqGuarded_rev (S : Ctor → Prop) :
    WellFounded (CtxOnRev S EqGuardedStep) := by
  have hsub : Subrelation (CtxOnRev S EqGuardedStep) StepCtxFullRev := by
    intro a b hab
    change CtxOn S EqGuardedStep b a at hab
    change StepCtxFull b a
    exact ctxOn_eqGuarded_sub_stepCtxFull S hab
  exact Subrelation.wf hsub wf_StepCtxFullRev_poly

/-- The closed source used to transport the compiled `eqW` contextual
instability witness. -/
def instabilityWitness : Trace := .eqW (.merge .void .void) .void

/-- The unequal-branch verdict reached from `instabilityWitness`. -/
def instabilityDifferenceVerdict : Trace :=
  .integrate (.merge (.merge .void .void) .void)

/-- The root difference branch of the transported instability peak. -/
theorem instabilityWitness_to_difference (S : Ctor → Prop) :
    CtxStarOn S EqGuardedStep instabilityWitness instabilityDifferenceVerdict := by
  apply Relation.ReflTransGen.single
  apply CtxOn.root
  exact EqGuardedStep.R_eq_diff _ _
    ContextualConfluence.witness_args_distinct

/-- Enabling `eqW` congruence exposes the equality branch of the transported
instability peak. -/
theorem instabilityWitness_to_void {S : Ctor → Prop} (heqW : S .eqW) :
    CtxStarOn S EqGuardedStep instabilityWitness .void := by
  have hmerge : CtxOn S EqGuardedStep (.merge .void .void) .void :=
    CtxOn.root (EqGuardedStep.R_merge_void_left .void)
  have hctx : CtxOn S EqGuardedStep instabilityWitness (.eqW .void .void) := by
    exact CtxOn.eqWL heqW hmerge
  have hrefl : CtxOn S EqGuardedStep (.eqW .void .void) .void :=
    CtxOn.root (EqGuardedStep.R_eq_refl .void)
  exact Relation.ReflTransGen.head hctx (Relation.ReflTransGen.single hrefl)

/-- The finite cone containing every constructor-selective reduct of the
transported difference verdict. -/
def OnInstabilityDifferenceCone (x : Trace) : Prop :=
  x = instabilityDifferenceVerdict ∨
  x = .integrate (.merge .void .void) ∨
  x = .integrate .void

private theorem no_ctxOn_eqGuarded_from_void {S : Ctor → Prop} {u : Trace} :
    ¬ CtxOn S EqGuardedStep .void u := by
  intro h
  cases h with
  | root hs => cases hs

private theorem ctxOn_eqGuarded_merge_void_void {S : Ctor → Prop} {u : Trace}
    (h : CtxOn S EqGuardedStep (.merge .void .void) u) : u = .void := by
  cases h with
  | root hs => cases hs <;> rfl
  | mergeL _ h' => exact absurd h' no_ctxOn_eqGuarded_from_void
  | mergeR _ h' => exact absurd h' no_ctxOn_eqGuarded_from_void

private theorem ctxOn_eqGuarded_merge_mergeVoid_void {S : Ctor → Prop} {u : Trace}
    (h : CtxOn S EqGuardedStep (.merge (.merge .void .void) .void) u) :
    u = .merge .void .void := by
  cases h with
  | root hs => cases hs; rfl
  | mergeL _ h' =>
      have hu := ctxOn_eqGuarded_merge_void_void h'
      rw [hu]
  | mergeR _ h' => exact absurd h' no_ctxOn_eqGuarded_from_void

/-- The transported difference cone is closed under `CtxOn S EqGuardedStep`
for arbitrary `S`; no case uses `eqW` congruence. -/
theorem onInstabilityDifferenceCone_step {S : Ctor → Prop} {x y : Trace}
    (hx : OnInstabilityDifferenceCone x)
    (hxy : CtxOn S EqGuardedStep x y) :
    OnInstabilityDifferenceCone y := by
  rcases hx with rfl | rfl | rfl
  · cases hxy with
    | root hs => cases hs
    | integrate _ hinner =>
        have hy := ctxOn_eqGuarded_merge_mergeVoid_void hinner
        rw [hy]
        exact Or.inr (Or.inl rfl)
  · cases hxy with
    | root hs => cases hs
    | integrate _ hinner =>
        have hy := ctxOn_eqGuarded_merge_void_void hinner
        rw [hy]
        exact Or.inr (Or.inr rfl)
  · cases hxy with
    | root hs => cases hs
    | integrate _ hinner => exact absurd hinner no_ctxOn_eqGuarded_from_void

/-- Every constructor-selective reduct of a cone member remains in the cone. -/
theorem onInstabilityDifferenceCone_star {S : Ctor → Prop} {x y : Trace}
    (hx : OnInstabilityDifferenceCone x)
    (hxy : CtxStarOn S EqGuardedStep x y) :
    OnInstabilityDifferenceCone y := by
  induction hxy with
  | refl => exact hx
  | tail _ hstep ih => exact onInstabilityDifferenceCone_step ih hstep

/-- `void` is outside the transported difference cone. -/
theorem void_not_onInstabilityDifferenceCone :
    ¬ OnInstabilityDifferenceCone .void := by
  rintro (h | h | h) <;> exact Trace.noConfusion h

private theorem ctxOnStar_eqGuarded_sub_ctxStarFull {S : Ctor → Prop}
    {a b : Trace} (h : CtxStarOn S EqGuardedStep a b) :
    ContextualDiagonalScope.CtxStar a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (ctxOn_eqGuarded_sub_stepCtxFull S hstep)

/-- The two endpoints of the transported peak have no common reduct, for every
constructor-selection predicate `S`. -/
theorem instabilityDifference_not_joinable_void (S : Ctor → Prop) :
    ¬ ∃ d : Trace,
      CtxStarOn S EqGuardedStep instabilityDifferenceVerdict d ∧
      CtxStarOn S EqGuardedStep .void d := by
  rintro ⟨d, hdifference, hvoid⟩
  have hdvoid : d = .void :=
    ContextualDiagonalScope.ctxStar_void
      (ctxOnStar_eqGuarded_sub_ctxStarFull hvoid)
  subst d
  exact void_not_onInstabilityDifferenceCone
    (onInstabilityDifferenceCone_star (Or.inl rfl) hdifference)

/-- W1-A (necessity): if congruence below `eqW` is enabled, the surgical
equality-guarded relation is not confluent under `CtxOn S`. -/
theorem eqW_congruence_breaks_confluence {S : Ctor → Prop}
    (heqW : S .eqW) : ¬ ConfluentOn S EqGuardedStep := by
  intro hconfluent
  obtain ⟨d, hdifference, hvoid⟩ := hconfluent instabilityWitness
    instabilityDifferenceVerdict .void
    (instabilityWitness_to_difference S)
    (instabilityWitness_to_void heqW)
  exact instabilityDifference_not_joinable_void S ⟨d, hdifference, hvoid⟩

/-! ## Stage 2A: the roadmap W1-B statement is false

The roadmap conjectured that freezing `eqW` alone restores confluence for every
selection `S`. That statement is refuted here. The rule `R_rec_succ` writes its
contractum under an `app` head, and no root rule of `EqGuardedStep` has an
`app` head, so when `recD` congruence is enabled while `app` congruence is
frozen, the peak between `R_rec_succ` and a step inside the base argument
reaches two normal forms that never rejoin.

STATEMENT CHANGE (logged per LASOT Rule W3):
Old W1-B target: `eqW ∉ S → ConfluentOn S EqGuardedStep`.
Refutation: `recD_thaw_app_freeze_breaks_confluence` below.
Corrected sufficiency: `freeze_eqW_recAppAligned_restores_confluence`.
Old W1-C target: `ConfluentOn S EqGuardedStep ↔ eqW ∉ S`.
Corrected crown: `confluentOn_eqGuarded_iff`,
`ConfluentOn S EqGuardedStep ↔ (¬ S .eqW ∧ (S .recD → S .app))`.
At full thaw of everything except `eqW` the original characterization survives
verbatim (`eqW_least_freeze_at_full_thaw`). -/

/-- `delta void` has no constructor-selective equality-guarded step: no root
rule has a `delta` head, and the argument `void` is irreducible. -/
private theorem ctxOn_eqGuarded_deltaVoid_normal {S : Ctor → Prop} {u : Trace} :
    ¬ CtxOn S EqGuardedStep (.delta .void) u := by
  intro h
  cases h with
  | root hs => cases hs
  | delta _ h' => exact no_ctxOn_eqGuarded_from_void h'

/-- With `app` congruence frozen, every `app`-headed term is a normal form of
the constructor-selective closure: no root rule of `EqGuardedStep` has an
`app` head. Relation: `CtxOn S EqGuardedStep`. Property: normal_form. -/
theorem ctxOn_eqGuarded_app_normal {S : Ctor → Prop} (happ : ¬ S .app)
    {x y u : Trace} : ¬ CtxOn S EqGuardedStep (.app x y) u := by
  intro h
  cases h with
  | root hs => cases hs
  | appL enabled _ => exact happ enabled
  | appR enabled _ => exact happ enabled

/-- A term with no outgoing constructor-selective step reaches only itself. -/
private theorem ctxStarOn_eq_of_normal {S : Ctor → Prop} {R : Trace → Trace → Prop}
    {x : Trace} (hx : ∀ u, ¬ CtxOn S R x u) {d : Trace}
    (h : CtxStarOn S R x d) : d = x := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact absurd (ih ▸ hstep) (hx _)

/-- The finite cone containing every constructor-selective reduct of the
congruence leg of the refutation peak, for any `S` with `app` frozen. -/
def OnRecFreezeCone (x : Trace) : Prop :=
  x = .recΔ .void .void (.delta .void) ∨
  x = .app .void (.recΔ .void .void .void)

/-- The refutation cone is closed under `CtxOn S EqGuardedStep` whenever `app`
congruence is frozen. -/
theorem onRecFreezeCone_step {S : Ctor → Prop} (happ : ¬ S .app) {x y : Trace}
    (hx : OnRecFreezeCone x) (hxy : CtxOn S EqGuardedStep x y) :
    OnRecFreezeCone y := by
  rcases hx with rfl | rfl
  · cases hxy with
    | root hs =>
        cases hs with
        | R_rec_succ => exact Or.inr rfl
    | recB _ h' => exact absurd h' no_ctxOn_eqGuarded_from_void
    | recS _ h' => exact absurd h' no_ctxOn_eqGuarded_from_void
    | recN _ h' => exact absurd h' ctxOn_eqGuarded_deltaVoid_normal
  · exact absurd hxy (ctxOn_eqGuarded_app_normal happ)

/-- Every constructor-selective reduct of a refutation-cone member remains in
the cone, `app` frozen. -/
theorem onRecFreezeCone_star {S : Ctor → Prop} (happ : ¬ S .app) {x y : Trace}
    (hx : OnRecFreezeCone x) (hxy : CtxStarOn S EqGuardedStep x y) :
    OnRecFreezeCone y := by
  induction hxy with
  | refl => exact hx
  | tail _ hstep ih => exact onRecFreezeCone_step happ ih hstep

/-- **W1-B as stated in the roadmap is false.** Thawing `recD` while freezing
`app` breaks confluence of the constructor-selective equality-guarded closure,
independently of the `eqW` freeze. The peak source is
`recΔ (merge void void) void (delta void)`: the root `R_rec_succ` contraction
buries the unreduced base `merge void void` under the frozen `app` head, while
the `recB` congruence step normalizes the base first; the two routes reach
distinct normal forms.

Relation: `CtxOn S EqGuardedStep`. Closure: `Relation.ReflTransGen`.
Property: non-confluence witness. Trust: kernel only. -/
theorem recD_thaw_app_freeze_breaks_confluence {S : Ctor → Prop}
    (hrec : S .recD) (happ : ¬ S .app) : ¬ ConfluentOn S EqGuardedStep := by
  intro hconfluent
  have hpeakRoot : CtxStarOn S EqGuardedStep
      (.recΔ (.merge .void .void) .void (.delta .void))
      (.app .void (.recΔ (.merge .void .void) .void .void)) :=
    Relation.ReflTransGen.single (CtxOn.root (EqGuardedStep.R_rec_succ _ _ _))
  have hpeakCong : CtxStarOn S EqGuardedStep
      (.recΔ (.merge .void .void) .void (.delta .void))
      (.recΔ .void .void (.delta .void)) :=
    Relation.ReflTransGen.single
      (CtxOn.recB hrec (CtxOn.root (EqGuardedStep.R_merge_void_left .void)))
  obtain ⟨d, hdApp, hdRec⟩ := hconfluent _ _ _ hpeakRoot hpeakCong
  have hdEq : d = .app .void (.recΔ (.merge .void .void) .void .void) :=
    ctxStarOn_eq_of_normal (fun _ => ctxOn_eqGuarded_app_normal happ) hdApp
  have hcone : OnRecFreezeCone d := onRecFreezeCone_star happ (Or.inl rfl) hdRec
  rw [hdEq] at hcone
  rcases hcone with h | h
  · exact Trace.noConfusion h
  · injection h with h₁ h₂
    injection h₂ with h₃ h₄ h₅
    exact Trace.noConfusion h₃

/-- Non-vacuity instance of the refutation at the concrete selection that thaws
exactly `recD`. -/
theorem recDOnly_not_confluent :
    ¬ ConfluentOn (fun c => c = Ctor.recD) EqGuardedStep :=
  recD_thaw_app_freeze_breaks_confluence rfl (fun h => Ctor.noConfusion h)

/-! ## Stage 2B: star lifting and the complete local peak enumeration -/

/-- Star lifting of `delta` congruence. -/
theorem ctxStarOn_delta {S : Ctor → Prop} {R : Trace → Trace → Prop}
    (enabled : S .delta) {t u : Trace} (h : CtxStarOn S R t u) :
    CtxStarOn S R (.delta t) (.delta u) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (CtxOn.delta enabled hstep)

/-- Star lifting of `integrate` congruence. -/
theorem ctxStarOn_integrate {S : Ctor → Prop} {R : Trace → Trace → Prop}
    (enabled : S .integrate) {t u : Trace} (h : CtxStarOn S R t u) :
    CtxStarOn S R (.integrate t) (.integrate u) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (CtxOn.integrate enabled hstep)

/-- Star lifting of left `merge` congruence. -/
theorem ctxStarOn_mergeL {S : Ctor → Prop} {R : Trace → Trace → Prop}
    (enabled : S .merge) {a a' b : Trace} (h : CtxStarOn S R a a') :
    CtxStarOn S R (.merge a b) (.merge a' b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (CtxOn.mergeL enabled hstep)

/-- Star lifting of right `merge` congruence. -/
theorem ctxStarOn_mergeR {S : Ctor → Prop} {R : Trace → Trace → Prop}
    (enabled : S .merge) {a b b' : Trace} (h : CtxStarOn S R b b') :
    CtxStarOn S R (.merge a b) (.merge a b') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (CtxOn.mergeR enabled hstep)

/-- Star lifting of left `app` congruence. -/
theorem ctxStarOn_appL {S : Ctor → Prop} {R : Trace → Trace → Prop}
    (enabled : S .app) {a a' b : Trace} (h : CtxStarOn S R a a') :
    CtxStarOn S R (.app a b) (.app a' b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (CtxOn.appL enabled hstep)

/-- Star lifting of right `app` congruence. -/
theorem ctxStarOn_appR {S : Ctor → Prop} {R : Trace → Trace → Prop}
    (enabled : S .app) {a b b' : Trace} (h : CtxStarOn S R b b') :
    CtxStarOn S R (.app a b) (.app a b') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (CtxOn.appR enabled hstep)

/-- Star lifting of `recΔ` base congruence. -/
theorem ctxStarOn_recB {S : Ctor → Prop} {R : Trace → Trace → Prop}
    (enabled : S .recD) {b b' s n : Trace} (h : CtxStarOn S R b b') :
    CtxStarOn S R (.recΔ b s n) (.recΔ b' s n) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (CtxOn.recB enabled hstep)

/-- Star lifting of `recΔ` step congruence. -/
theorem ctxStarOn_recS {S : Ctor → Prop} {R : Trace → Trace → Prop}
    (enabled : S .recD) {b s s' n : Trace} (h : CtxStarOn S R s s') :
    CtxStarOn S R (.recΔ b s n) (.recΔ b s' n) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (CtxOn.recS enabled hstep)

/-- Star lifting of `recΔ` numeral congruence. -/
theorem ctxStarOn_recN {S : Ctor → Prop} {R : Trace → Trace → Prop}
    (enabled : S .recD) {b s n n' : Trace} (h : CtxStarOn S R n n') :
    CtxStarOn S R (.recΔ b s n) (.recΔ b s n') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (CtxOn.recN enabled hstep)

/-- **The root-versus-arbitrary peak enumeration.** Under `eqW` frozen and the
alignment `recD → app`, every peak between a root `EqGuardedStep` contraction
and any constructor-selective step out of the same source joins. Root/root
peaks close by root determinism (`eqGuarded_unique_target`); the non-left-linear
`R_merge_cancel` peaks close by re-reducing the surviving copy; the duplicating
`R_rec_succ` peaks close by replaying the inner step under `app`/`recΔ`
congruence, which is exactly where the `recD → app` alignment is consumed.
No measure argument is used anywhere (LASOT K-check 1/2: joins are explicit
step sequences, termination enters only through inherited SN later).

Relation: `CtxOn S EqGuardedStep`. Closure: `Relation.ReflTransGen`.
Property: local peak joinability. -/
theorem ctxOn_root_peak_joins {S : Ctor → Prop}
    (heqW : ¬ S .eqW) (halign : S .recD → S .app)
    {a b c : Trace} (hr : EqGuardedStep a b) (hac : CtxOn S EqGuardedStep a c) :
    ∃ d : Trace, CtxStarOn S EqGuardedStep b d ∧ CtxStarOn S EqGuardedStep c d := by
  cases hac with
  | root hr' =>
      obtain rfl := eqGuarded_unique_target hr hr'
      exact ⟨b, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | delta enabled h' => cases hr
  | integrate enabled h' =>
      cases hr with
      | R_int_delta =>
          cases h' with
          | root hs => cases hs
          | delta _ h'' =>
              exact ⟨.void, Relation.ReflTransGen.refl,
                Relation.ReflTransGen.single (CtxOn.root (EqGuardedStep.R_int_delta _))⟩
  | mergeL enabled h' =>
      cases hr with
      | R_merge_void_left => exact absurd h' no_ctxOn_eqGuarded_from_void
      | R_merge_void_right =>
          exact ⟨_, Relation.ReflTransGen.single h',
            Relation.ReflTransGen.single
              (CtxOn.root (EqGuardedStep.R_merge_void_right _))⟩
      | R_merge_cancel =>
          refine ⟨_, Relation.ReflTransGen.single h', ?_⟩
          exact (Relation.ReflTransGen.single (CtxOn.mergeR enabled h')).tail
            (CtxOn.root (EqGuardedStep.R_merge_cancel _))
  | mergeR enabled h' =>
      cases hr with
      | R_merge_void_left =>
          exact ⟨_, Relation.ReflTransGen.single h',
            Relation.ReflTransGen.single
              (CtxOn.root (EqGuardedStep.R_merge_void_left _))⟩
      | R_merge_void_right => exact absurd h' no_ctxOn_eqGuarded_from_void
      | R_merge_cancel =>
          refine ⟨_, Relation.ReflTransGen.single h', ?_⟩
          exact (Relation.ReflTransGen.single (CtxOn.mergeL enabled h')).tail
            (CtxOn.root (EqGuardedStep.R_merge_cancel _))
  | appL enabled h' => cases hr
  | appR enabled h' => cases hr
  | recB enabled h' =>
      cases hr with
      | R_rec_zero =>
          exact ⟨_, Relation.ReflTransGen.single h',
            Relation.ReflTransGen.single
              (CtxOn.root (EqGuardedStep.R_rec_zero _ _))⟩
      | R_rec_succ =>
          exact ⟨_,
            Relation.ReflTransGen.single
              (CtxOn.appR (halign enabled) (CtxOn.recB enabled h')),
            Relation.ReflTransGen.single
              (CtxOn.root (EqGuardedStep.R_rec_succ _ _ _))⟩
  | recS enabled h' =>
      cases hr with
      | R_rec_zero =>
          exact ⟨_, Relation.ReflTransGen.refl,
            Relation.ReflTransGen.single
              (CtxOn.root (EqGuardedStep.R_rec_zero _ _))⟩
      | R_rec_succ =>
          exact ⟨_,
            (Relation.ReflTransGen.single
              (CtxOn.appL (halign enabled) h')).tail
              (CtxOn.appR (halign enabled) (CtxOn.recS enabled h')),
            Relation.ReflTransGen.single
              (CtxOn.root (EqGuardedStep.R_rec_succ _ _ _))⟩
  | recN enabled h' =>
      cases hr with
      | R_rec_zero => exact absurd h' no_ctxOn_eqGuarded_from_void
      | R_rec_succ =>
          cases h' with
          | root hs => cases hs
          | delta _ h'' =>
              exact ⟨_,
                Relation.ReflTransGen.single
                  (CtxOn.appR (halign enabled) (CtxOn.recN enabled h'')),
                Relation.ReflTransGen.single
                  (CtxOn.root (EqGuardedStep.R_rec_succ _ _ _))⟩
  | eqWL enabled h' => exact absurd enabled heqW
  | eqWR enabled h' => exact absurd enabled heqW

/-- **Local confluence of the aligned frozen closure.** Every local peak of
`CtxOn S EqGuardedStep` joins when `eqW` is frozen and `recD → app` holds.
Root-involving peaks are `ctxOn_root_peak_joins`; same-position congruence
peaks join by the inner induction hypothesis lifted through the star
congruence lemmas; distinct-position congruence peaks commute in one step
each.

Relation: `CtxOn S EqGuardedStep`. Closure: `Relation.ReflTransGen`.
Property: local_confluence. -/
theorem ctxOn_local_join {S : Ctor → Prop}
    (heqW : ¬ S .eqW) (halign : S .recD → S .app) :
    ∀ {a b : Trace}, CtxOn S EqGuardedStep a b →
      ∀ c : Trace, CtxOn S EqGuardedStep a c →
        ∃ d : Trace, CtxStarOn S EqGuardedStep b d ∧ CtxStarOn S EqGuardedStep c d := by
  intro a b hab
  induction hab with
  | root hr =>
      intro c hac
      exact ctxOn_root_peak_joins heqW halign hr hac
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
          obtain ⟨d, hd₁, hd₂⟩ :=
            ctxOn_root_peak_joins heqW halign hr (CtxOn.integrate enabled h₁)
          exact ⟨d, hd₂, hd₁⟩
      | integrate enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarOn_integrate enabled hd₁, ctxStarOn_integrate enabled hd₂⟩
  | mergeL enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr =>
          obtain ⟨d, hd₁, hd₂⟩ :=
            ctxOn_root_peak_joins heqW halign hr (CtxOn.mergeL enabled h₁)
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
          obtain ⟨d, hd₁, hd₂⟩ :=
            ctxOn_root_peak_joins heqW halign hr (CtxOn.mergeR enabled h₁)
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
          obtain ⟨d, hd₁, hd₂⟩ :=
            ctxOn_root_peak_joins heqW halign hr (CtxOn.recB enabled h₁)
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
          obtain ⟨d, hd₁, hd₂⟩ :=
            ctxOn_root_peak_joins heqW halign hr (CtxOn.recS enabled h₁)
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
          obtain ⟨d, hd₁, hd₂⟩ :=
            ctxOn_root_peak_joins heqW halign hr (CtxOn.recN enabled h₁)
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
  | eqWL enabled h₁ ih => exact absurd enabled heqW
  | eqWR enabled h₁ ih => exact absurd enabled heqW

/-! ## Stage 3: Newman and the corrected crown -/

/-- Newman core: local joinability plus accessibility joins star peaks. The
`Acc` recursion is the same diamond as `EqGuardedConfluence.join_star_star_at`,
written over the constructor-selective closure. -/
private theorem ctxOn_join_star_star {S : Ctor → Prop}
    (loc : ∀ {a b : Trace}, CtxOn S EqGuardedStep a b →
      ∀ c : Trace, CtxOn S EqGuardedStep a c →
        ∃ d : Trace, CtxStarOn S EqGuardedStep b d ∧ CtxStarOn S EqGuardedStep c d) :
    ∀ x : Trace, Acc (CtxOnRev S EqGuardedStep) x →
      ∀ {y z : Trace}, CtxStarOn S EqGuardedStep x y → CtxStarOn S EqGuardedStep x z →
        ∃ d : Trace, CtxStarOn S EqGuardedStep y d ∧ CtxStarOn S EqGuardedStep z d := by
  intro x hx
  induction hx with
  | intro x _ ih =>
      intro y z hxy hxz
      rcases Relation.ReflTransGen.cases_head hxy with rfl | ⟨b₁, hxb₁, hb₁y⟩
      · exact ⟨z, hxz, Relation.ReflTransGen.refl⟩
      · rcases Relation.ReflTransGen.cases_head hxz with rfl | ⟨c₁, hxc₁, hc₁z⟩
        · exact ⟨y, Relation.ReflTransGen.refl,
            Relation.ReflTransGen.head hxb₁ hb₁y⟩
        · obtain ⟨e, hb₁e, hc₁e⟩ := loc hxb₁ _ hxc₁
          obtain ⟨d₁, hed₁, hzd₁⟩ := ih c₁ hxc₁ hc₁e hc₁z
          obtain ⟨d, hyd, hd₁d⟩ := ih b₁ hxb₁ hb₁y (hb₁e.trans hed₁)
          exact ⟨d, hyd, hzd₁.trans hd₁d⟩

/-- **Corrected W1-B (sufficiency).** Freezing `eqW` restores confluence of the
constructor-selective equality-guarded closure whenever the selection also
satisfies the alignment `recD → app`: thawing the recursor requires thawing its
output channel. Strong normalization is inherited from the full contextual
kernel relation by subrelation (`wf_ctxOn_eqGuarded_rev`); no fresh measure is
introduced (LASOT K-check 1/2).

Relation: `CtxOn S EqGuardedStep`. Closure: `Relation.ReflTransGen`.
Property: confluence. Trust: kernel only. -/
theorem freeze_eqW_recAppAligned_restores_confluence {S : Ctor → Prop}
    (heqW : ¬ S .eqW) (halign : S .recD → S .app) :
    ConfluentOn S EqGuardedStep := by
  intro a b c hab hac
  exact ctxOn_join_star_star (ctxOn_local_join heqW halign) a
    ((wf_ctxOn_eqGuarded_rev S).apply a) hab hac

/-- **The corrected crown (W1-C).** The constructor-selective equality-guarded
closure is confluent exactly when `eqW` congruence is frozen and the selection
aligns the recursor with its output channel. The confluence boundary of the
surgical relation is therefore two-dimensional: the comparator freeze `eqW`
(forced by verdict stability) plus the alignment `recD → app` (forced by the
duplicating recursor rule writing under `app`).

Relation: `CtxOn S EqGuardedStep`. Closure: `Relation.ReflTransGen`.
Property: confluence characterization. Trust: kernel only. -/
theorem confluentOn_eqGuarded_iff (S : Ctor → Prop) :
    ConfluentOn S EqGuardedStep ↔ (¬ S .eqW ∧ (S .recD → S .app)) := by
  constructor
  · intro hconf
    refine ⟨fun heqW => eqW_congruence_breaks_confluence heqW hconf, ?_⟩
    intro hrec
    by_contra happ
    exact recD_thaw_app_freeze_breaks_confluence hrec happ hconf
  · rintro ⟨heqW, halign⟩
    exact freeze_eqW_recAppAligned_restores_confluence heqW halign

/-- Full thaw is not confluent: the `eqW` congruence alone already breaks it. -/
theorem fullThaw_not_confluent :
    ¬ ConfluentOn (fun _ : Ctor => True) EqGuardedStep :=
  eqW_congruence_breaks_confluence trivial

/-- The selection that freezes exactly `eqW` is confluent. -/
theorem fullMinusEqW_confluent :
    ConfluentOn (fun c : Ctor => c ≠ Ctor.eqW) EqGuardedStep :=
  freeze_eqW_recAppAligned_restores_confluence
    (fun h => h rfl) (fun _ h => Ctor.noConfusion h)

/-- **The least-freeze statement that survives the correction.** At the top of
the selection lattice, freezing `eqW` alone separates confluent from
non-confluent: the closure with everything except `eqW` enabled is confluent,
and the full closure is not. This is the boundary-object existence statement
the Distinction paper may carry; the general lattice answer is
`confluentOn_eqGuarded_iff`. -/
theorem eqW_least_freeze_at_full_thaw :
    ConfluentOn (fun c : Ctor => c ≠ Ctor.eqW) EqGuardedStep ∧
    ¬ ConfluentOn (fun _ : Ctor => True) EqGuardedStep :=
  ⟨fullMinusEqW_confluent, fullThaw_not_confluent⟩

/-! ## D1: full-thaw simulation against compiled `EqGuardedStepCtx`

Two-way one-step simulation between `CtxOn (fun _ => True) EqGuardedStep`
and the compiled `ContextualConfluence.EqGuardedStepCtx`, lifted through
`ReflTransGen.mono`, then the confluence iff. The corollary shows that
`fullThaw_not_confluent` recovers `eqGuardedStepCtx_not_confluent`. -/

/-- D1: full-thaw constructor-selective step is a compiled contextual step. -/
private theorem ctxOn_fullThaw_to_eqGuardedStepCtx :
    ∀ {a b : Trace}, CtxOn (fun _ => True) EqGuardedStep a b →
      ContextualConfluence.EqGuardedStepCtx a b
  | _, _, .root h => ContextualConfluence.EqGuardedStepCtx.root h
  | _, _, .delta _ h =>
      ContextualConfluence.EqGuardedStepCtx.delta (ctxOn_fullThaw_to_eqGuardedStepCtx h)
  | _, _, .integrate _ h =>
      ContextualConfluence.EqGuardedStepCtx.integrate (ctxOn_fullThaw_to_eqGuardedStepCtx h)
  | _, _, .mergeL _ h =>
      ContextualConfluence.EqGuardedStepCtx.mergeL (ctxOn_fullThaw_to_eqGuardedStepCtx h)
  | _, _, .mergeR _ h =>
      ContextualConfluence.EqGuardedStepCtx.mergeR (ctxOn_fullThaw_to_eqGuardedStepCtx h)
  | _, _, .appL _ h =>
      ContextualConfluence.EqGuardedStepCtx.appL (ctxOn_fullThaw_to_eqGuardedStepCtx h)
  | _, _, .appR _ h =>
      ContextualConfluence.EqGuardedStepCtx.appR (ctxOn_fullThaw_to_eqGuardedStepCtx h)
  | _, _, .recB _ h =>
      ContextualConfluence.EqGuardedStepCtx.recB (ctxOn_fullThaw_to_eqGuardedStepCtx h)
  | _, _, .recS _ h =>
      ContextualConfluence.EqGuardedStepCtx.recS (ctxOn_fullThaw_to_eqGuardedStepCtx h)
  | _, _, .recN _ h =>
      ContextualConfluence.EqGuardedStepCtx.recN (ctxOn_fullThaw_to_eqGuardedStepCtx h)
  | _, _, .eqWL _ h =>
      ContextualConfluence.EqGuardedStepCtx.eqWL (ctxOn_fullThaw_to_eqGuardedStepCtx h)
  | _, _, .eqWR _ h =>
      ContextualConfluence.EqGuardedStepCtx.eqWR (ctxOn_fullThaw_to_eqGuardedStepCtx h)

/-- D1: compiled contextual step is a full-thaw constructor-selective step. -/
private theorem eqGuardedStepCtx_to_ctxOn_fullThaw :
    ∀ {a b : Trace}, ContextualConfluence.EqGuardedStepCtx a b →
      CtxOn (fun _ : Ctor => True) EqGuardedStep a b
  | _, _, .root hr => CtxOn.root hr
  | _, _, .delta h => CtxOn.delta trivial (eqGuardedStepCtx_to_ctxOn_fullThaw h)
  | _, _, .integrate h => CtxOn.integrate trivial (eqGuardedStepCtx_to_ctxOn_fullThaw h)
  | _, _, .mergeL h => CtxOn.mergeL trivial (eqGuardedStepCtx_to_ctxOn_fullThaw h)
  | _, _, .mergeR h => CtxOn.mergeR trivial (eqGuardedStepCtx_to_ctxOn_fullThaw h)
  | _, _, .appL h => CtxOn.appL trivial (eqGuardedStepCtx_to_ctxOn_fullThaw h)
  | _, _, .appR h => CtxOn.appR trivial (eqGuardedStepCtx_to_ctxOn_fullThaw h)
  | _, _, .recB h => CtxOn.recB trivial (eqGuardedStepCtx_to_ctxOn_fullThaw h)
  | _, _, .recS h => CtxOn.recS trivial (eqGuardedStepCtx_to_ctxOn_fullThaw h)
  | _, _, .recN h => CtxOn.recN trivial (eqGuardedStepCtx_to_ctxOn_fullThaw h)
  | _, _, .eqWL h => CtxOn.eqWL trivial (eqGuardedStepCtx_to_ctxOn_fullThaw h)
  | _, _, .eqWR h => CtxOn.eqWR trivial (eqGuardedStepCtx_to_ctxOn_fullThaw h)

/-- D1: one-step two-way simulation at full thaw. -/
theorem ctxOn_fullThaw_iff_eqGuardedStepCtx {a b : Trace} :
    CtxOn (fun _ : Ctor => True) EqGuardedStep a b ↔
      ContextualConfluence.EqGuardedStepCtx a b :=
  ⟨ctxOn_fullThaw_to_eqGuardedStepCtx, eqGuardedStepCtx_to_ctxOn_fullThaw⟩

/-- D1: two-way simulation of full-thaw confluence against the compiled
contextual confluence predicate. Relation: `CtxOn (fun _ => True) EqGuardedStep`
versus `EqGuardedStepCtx`. Closure: `Relation.ReflTransGen`. -/
theorem conf_bridge :
    ConfluentOn (fun _ : Ctor => True) EqGuardedStep ↔
      ContextualConfluence.ConfluentEqGuardedCtx := by
  have hstar_to_compiled {x y : Trace}
      (h : CtxStarOn (fun _ : Ctor => True) EqGuardedStep x y) :
      ContextualConfluence.EqGuardedCtxStar x y :=
    Relation.ReflTransGen.mono (fun _ _ => ctxOn_fullThaw_to_eqGuardedStepCtx) h
  have hstar_from_compiled {x y : Trace}
      (h : ContextualConfluence.EqGuardedCtxStar x y) :
      CtxStarOn (fun _ : Ctor => True) EqGuardedStep x y :=
    Relation.ReflTransGen.mono (fun _ _ => eqGuardedStepCtx_to_ctxOn_fullThaw) h
  constructor
  · intro hconf a b c hab hac
    obtain ⟨d, hbd, hcd⟩ := hconf a b c (hstar_from_compiled hab) (hstar_from_compiled hac)
    exact ⟨d, hstar_to_compiled hbd, hstar_to_compiled hcd⟩
  · intro hconf a b c hab hac
    obtain ⟨d, hbd, hcd⟩ := hconf a b c (hstar_to_compiled hab) (hstar_to_compiled hac)
    exact ⟨d, hstar_from_compiled hbd, hstar_from_compiled hcd⟩

/-- D1: `fullThaw_not_confluent` recovers the compiled non-confluence theorem. -/
theorem fullThaw_not_confluent_recovers_eqGuardedStepCtx_not_confluent :
    ¬ ContextualConfluence.ConfluentEqGuardedCtx :=
  fun h => fullThaw_not_confluent (conf_bridge.mpr h)

/-- Non-vacuity of the frozen instance (LASOT Gate R5): under the selection
freezing exactly `eqW`, a concrete source genuinely branches through two
distinct one-step reducts and the branches rejoin. The closure is inhabited,
branching, and joining; the confluence theorem for it is not vacuous. -/
theorem frozen_instance_concrete_peak :
    CtxOn (fun c : Ctor => c ≠ Ctor.eqW) EqGuardedStep
      (.merge (.merge .void .void) (.merge .void .void)) (.merge .void .void) ∧
    CtxOn (fun c : Ctor => c ≠ Ctor.eqW) EqGuardedStep
      (.merge (.merge .void .void) (.merge .void .void))
      (.merge .void (.merge .void .void)) ∧
    ∃ d : Trace,
      CtxStarOn (fun c : Ctor => c ≠ Ctor.eqW) EqGuardedStep
        (.merge .void .void) d ∧
      CtxStarOn (fun c : Ctor => c ≠ Ctor.eqW) EqGuardedStep
        (.merge .void (.merge .void .void)) d := by
  refine ⟨CtxOn.root (EqGuardedStep.R_merge_cancel _),
    CtxOn.mergeL (fun h => Ctor.noConfusion h)
      (CtxOn.root (EqGuardedStep.R_merge_void_left _)),
    .void,
    Relation.ReflTransGen.single (CtxOn.root (EqGuardedStep.R_merge_cancel _)),
    ?_⟩
  exact (Relation.ReflTransGen.single
      (CtxOn.root (EqGuardedStep.R_merge_void_left _))).tail
    (CtxOn.root (EqGuardedStep.R_merge_void_left _))

/-- D4: `R_rec_succ` branching-and-rejoining witness at the selection that
freezes exactly `eqW`. The alignment premise `recD → app` is exercised: the
root contraction writes under an `app` head, and the join uses `appR`/`recB`
congruence (app thawed). Relation: `CtxOn (fun c => c ≠ Ctor.eqW) EqGuardedStep`.
Closure: `Relation.ReflTransGen`. Property: non-vacuity witness. -/
theorem recSucc_peak_witness_at_frozen_selection :
    CtxOn (fun c : Ctor => c ≠ Ctor.eqW) EqGuardedStep
      (.recΔ (.merge .void .void) .void (.delta .void))
      (.app .void (.recΔ (.merge .void .void) .void .void)) ∧
    CtxOn (fun c : Ctor => c ≠ Ctor.eqW) EqGuardedStep
      (.recΔ (.merge .void .void) .void (.delta .void))
      (.recΔ .void .void (.delta .void)) ∧
    ∃ d : Trace,
      CtxStarOn (fun c : Ctor => c ≠ Ctor.eqW) EqGuardedStep
        (.app .void (.recΔ (.merge .void .void) .void .void)) d ∧
      CtxStarOn (fun c : Ctor => c ≠ Ctor.eqW) EqGuardedStep
        (.recΔ .void .void (.delta .void)) d := by
  refine ⟨CtxOn.root (EqGuardedStep.R_rec_succ _ _ _),
    CtxOn.recB (fun h => Ctor.noConfusion h)
      (CtxOn.root (EqGuardedStep.R_merge_void_left _)),
    .app .void (.recΔ .void .void .void),
    Relation.ReflTransGen.single
      (CtxOn.appR (fun h => Ctor.noConfusion h)
        (CtxOn.recB (fun h => Ctor.noConfusion h)
          (CtxOn.root (EqGuardedStep.R_merge_void_left _)))),
    Relation.ReflTransGen.single
      (CtxOn.root (EqGuardedStep.R_rec_succ _ _ _))⟩

end OperatorKO7.Meta.DistinctionBoundary.FreezeSetForced
