/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.DistinctionBoundary.FreezeSetForced

/-!
# Positional freeze crown for the equality-guarded KO7 relation

This module refines the constructor-grade crown of
`Meta/DistinctionBoundary/FreezeSetForced.lean`. That crown gates both
`app` argument positions with a single flag `S .app`. Here the flags split:
`appL` and `appR` are independent. At any selection with `appL = appR = S .app`,
the two closures agree (`ctxOnPos_ofCtor_iff_ctxOn`, `conf_bridge_pos`).

The write-closure reading refines with the split. A constructor whose rule
writes into position `p` of another constructor cannot be thawed without
thawing `p`. `R_rec_succ` writes the unreduced base into the *right* argument
of `app` and copies the step argument into the *left* argument of `app`.
Thawing `recD` therefore forces both `appR` (the recB family, B2-S) and
`appL` (the recS family, the named open peak of the one-sided alignment).

The dispatch's one-sided candidate

`ConfluentOnPos S EqGuardedStep ↔ (¬ S .eqW ∧ (S .recD → S .appR))`

is FALSE. Sufficiency fails at the recS peak
`recΔ void (merge void void) (delta void)` under the B2-S joining selection
(`eqW` frozen, `appL` frozen, `appR` thawed). The corrected positional crown is

`ConfluentOnPos S EqGuardedStep ↔
  (¬ S .eqW ∧ (S .recD → S .appL) ∧ (S .recD → S .appR))`

proved by the B1 local-peak enumeration with the `appL`/`appR` case split.
Strong normalization is inherited from `StepCtxFull` by subrelation; no fresh
measure is introduced.

Relation: `CtxOnPos S EqGuardedStep`. Closure: `Relation.ReflTransGen`.
Trust: kernel only, Mathlib baseline.
-/

set_option autoImplicit false

open OperatorKO7 Trace
open OperatorKO7.EqGuardedConfluence
open MetaSN_KO7
open OperatorKO7.Meta.DistinctionBoundary.FreezeSetForced
  (Ctor CtxOn CtxStarOn ConfluentOn)

namespace OperatorKO7.Meta.DistinctionBoundary.FreezePositions

/-- Constructor heads with `app` split into independent left and right
positions. -/
inductive CtorPos where
  | void
  | delta
  | integrate
  | merge
  | appL
  | appR
  | recD
  | eqW

/-- Positional constructor-selective contextual closure of `R`.

`root` is always available. Each congruence constructor is available exactly
when the corresponding positional flag belongs to `S`. The nullary constructor
`void` has no congruence position. `appL` and `appR` are independent. -/
inductive CtxOnPos (S : CtorPos → Prop) (R : Trace → Trace → Prop) :
    Trace → Trace → Prop
  | root {a b : Trace} : R a b → CtxOnPos S R a b
  | delta {t u : Trace} (enabled : S .delta) :
      CtxOnPos S R t u → CtxOnPos S R (.delta t) (.delta u)
  | integrate {t u : Trace} (enabled : S .integrate) :
      CtxOnPos S R t u → CtxOnPos S R (.integrate t) (.integrate u)
  | mergeL {a a' b : Trace} (enabled : S .merge) :
      CtxOnPos S R a a' → CtxOnPos S R (.merge a b) (.merge a' b)
  | mergeR {a b b' : Trace} (enabled : S .merge) :
      CtxOnPos S R b b' → CtxOnPos S R (.merge a b) (.merge a b')
  | appL {a a' b : Trace} (enabled : S .appL) :
      CtxOnPos S R a a' → CtxOnPos S R (.app a b) (.app a' b)
  | appR {a b b' : Trace} (enabled : S .appR) :
      CtxOnPos S R b b' → CtxOnPos S R (.app a b) (.app a b')
  | recB {b b' s n : Trace} (enabled : S .recD) :
      CtxOnPos S R b b' → CtxOnPos S R (.recΔ b s n) (.recΔ b' s n)
  | recS {b s s' n : Trace} (enabled : S .recD) :
      CtxOnPos S R s s' → CtxOnPos S R (.recΔ b s n) (.recΔ b s' n)
  | recN {b s n n' : Trace} (enabled : S .recD) :
      CtxOnPos S R n n' → CtxOnPos S R (.recΔ b s n) (.recΔ b s n')
  | eqWL {a a' b : Trace} (enabled : S .eqW) :
      CtxOnPos S R a a' → CtxOnPos S R (.eqW a b) (.eqW a' b)
  | eqWR {a b b' : Trace} (enabled : S .eqW) :
      CtxOnPos S R b b' → CtxOnPos S R (.eqW a b) (.eqW a b')

/-- Reflexive-transitive reduction under the positional closure. -/
abbrev CtxStarPos (S : CtorPos → Prop) (R : Trace → Trace → Prop) :
    Trace → Trace → Prop :=
  Relation.ReflTransGen (CtxOnPos S R)

/-- Confluence of the positional constructor-selective contextual closure. -/
def ConfluentOnPos (S : CtorPos → Prop) (R : Trace → Trace → Prop) : Prop :=
  ∀ a b c : Trace,
    CtxStarPos S R a b →
    CtxStarPos S R a c →
    ∃ d : Trace, CtxStarPos S R b d ∧ CtxStarPos S R c d

/-- Reverse of the positional contextual relation. -/
def CtxOnPosRev (S : CtorPos → Prop) (R : Trace → Trace → Prop) :
    Trace → Trace → Prop :=
  fun a b => CtxOnPos S R b a

/-- Embed a constructor-grade selection as a positional selection with
`appL` and `appR` both equal to `S .app`. -/
def ofCtor (S : Ctor → Prop) : CtorPos → Prop
  | .void => S .void
  | .delta => S .delta
  | .integrate => S .integrate
  | .merge => S .merge
  | .appL => S .app
  | .appR => S .app
  | .recD => S .recD
  | .eqW => S .eqW

/-- Every positional equality-guarded step is a full contextual kernel step.
Load-bearing transport for inherited strong normalization. -/
theorem ctxOnPos_eqGuarded_sub_stepCtxFull (S : CtorPos → Prop) :
    ∀ {a b : Trace}, CtxOnPos S EqGuardedStep a b → StepCtxFull a b
  | _, _, .root h => StepCtxFull.root (eqGuarded_sub_step h)
  | _, _, .delta _ h => StepCtxFull.delta (ctxOnPos_eqGuarded_sub_stepCtxFull S h)
  | _, _, .integrate _ h =>
      StepCtxFull.integrate (ctxOnPos_eqGuarded_sub_stepCtxFull S h)
  | _, _, .mergeL _ h => StepCtxFull.mergeL (ctxOnPos_eqGuarded_sub_stepCtxFull S h)
  | _, _, .mergeR _ h => StepCtxFull.mergeR (ctxOnPos_eqGuarded_sub_stepCtxFull S h)
  | _, _, .appL _ h => StepCtxFull.appL (ctxOnPos_eqGuarded_sub_stepCtxFull S h)
  | _, _, .appR _ h => StepCtxFull.appR (ctxOnPos_eqGuarded_sub_stepCtxFull S h)
  | _, _, .recB _ h => StepCtxFull.recB (ctxOnPos_eqGuarded_sub_stepCtxFull S h)
  | _, _, .recS _ h => StepCtxFull.recS (ctxOnPos_eqGuarded_sub_stepCtxFull S h)
  | _, _, .recN _ h => StepCtxFull.recN (ctxOnPos_eqGuarded_sub_stepCtxFull S h)
  | _, _, .eqWL _ h => StepCtxFull.eqWL (ctxOnPos_eqGuarded_sub_stepCtxFull S h)
  | _, _, .eqWR _ h => StepCtxFull.eqWR (ctxOnPos_eqGuarded_sub_stepCtxFull S h)

/-- Strong normalization of every positional equality-guarded closure,
inherited as a subrelation of `StepCtxFullRev`. -/
theorem wf_ctxOnPos_eqGuarded_rev (S : CtorPos → Prop) :
    WellFounded (CtxOnPosRev S EqGuardedStep) := by
  have hsub : Subrelation (CtxOnPosRev S EqGuardedStep) StepCtxFullRev := by
    intro a b hab
    change CtxOnPos S EqGuardedStep b a at hab
    change StepCtxFull b a
    exact ctxOnPos_eqGuarded_sub_stepCtxFull S hab
  exact Subrelation.wf hsub wf_StepCtxFullRev_poly

/-! ## Bridge: positional closure at `appL = appR = S.app` equals `CtxOn S` -/

private theorem ctxOnPos_ofCtor_to_ctxOn (S : Ctor → Prop) :
    ∀ {a b : Trace}, CtxOnPos (ofCtor S) EqGuardedStep a b → CtxOn S EqGuardedStep a b
  | _, _, .root h => CtxOn.root h
  | _, _, .delta e h => CtxOn.delta e (ctxOnPos_ofCtor_to_ctxOn S h)
  | _, _, .integrate e h => CtxOn.integrate e (ctxOnPos_ofCtor_to_ctxOn S h)
  | _, _, .mergeL e h => CtxOn.mergeL e (ctxOnPos_ofCtor_to_ctxOn S h)
  | _, _, .mergeR e h => CtxOn.mergeR e (ctxOnPos_ofCtor_to_ctxOn S h)
  | _, _, .appL e h => CtxOn.appL e (ctxOnPos_ofCtor_to_ctxOn S h)
  | _, _, .appR e h => CtxOn.appR e (ctxOnPos_ofCtor_to_ctxOn S h)
  | _, _, .recB e h => CtxOn.recB e (ctxOnPos_ofCtor_to_ctxOn S h)
  | _, _, .recS e h => CtxOn.recS e (ctxOnPos_ofCtor_to_ctxOn S h)
  | _, _, .recN e h => CtxOn.recN e (ctxOnPos_ofCtor_to_ctxOn S h)
  | _, _, .eqWL e h => CtxOn.eqWL e (ctxOnPos_ofCtor_to_ctxOn S h)
  | _, _, .eqWR e h => CtxOn.eqWR e (ctxOnPos_ofCtor_to_ctxOn S h)

private theorem ctxOn_to_ctxOnPos_ofCtor (S : Ctor → Prop) :
    ∀ {a b : Trace}, CtxOn S EqGuardedStep a b → CtxOnPos (ofCtor S) EqGuardedStep a b
  | _, _, .root h => CtxOnPos.root h
  | _, _, .delta e h => CtxOnPos.delta e (ctxOn_to_ctxOnPos_ofCtor S h)
  | _, _, .integrate e h => CtxOnPos.integrate e (ctxOn_to_ctxOnPos_ofCtor S h)
  | _, _, .mergeL e h => CtxOnPos.mergeL e (ctxOn_to_ctxOnPos_ofCtor S h)
  | _, _, .mergeR e h => CtxOnPos.mergeR e (ctxOn_to_ctxOnPos_ofCtor S h)
  | _, _, .appL e h => CtxOnPos.appL e (ctxOn_to_ctxOnPos_ofCtor S h)
  | _, _, .appR e h => CtxOnPos.appR e (ctxOn_to_ctxOnPos_ofCtor S h)
  | _, _, .recB e h => CtxOnPos.recB e (ctxOn_to_ctxOnPos_ofCtor S h)
  | _, _, .recS e h => CtxOnPos.recS e (ctxOn_to_ctxOnPos_ofCtor S h)
  | _, _, .recN e h => CtxOnPos.recN e (ctxOn_to_ctxOnPos_ofCtor S h)
  | _, _, .eqWL e h => CtxOnPos.eqWL e (ctxOn_to_ctxOnPos_ofCtor S h)
  | _, _, .eqWR e h => CtxOnPos.eqWR e (ctxOn_to_ctxOnPos_ofCtor S h)

/-- One-step two-way simulation: positional closure at `ofCtor S` equals
constructor-grade `CtxOn S`. Relation: `CtxOnPos (ofCtor S) EqGuardedStep`
versus `CtxOn S EqGuardedStep`. -/
theorem ctxOnPos_ofCtor_iff_ctxOn (S : Ctor → Prop) {a b : Trace} :
    CtxOnPos (ofCtor S) EqGuardedStep a b ↔ CtxOn S EqGuardedStep a b :=
  ⟨ctxOnPos_ofCtor_to_ctxOn S, ctxOn_to_ctxOnPos_ofCtor S⟩

/-- Confluence bridge: at `appL = appR = S .app` the positional crown and the
constructor-grade crown agree. Relation: `CtxOnPos (ofCtor S) EqGuardedStep`
versus `CtxOn S EqGuardedStep`. Closure: `Relation.ReflTransGen`. -/
theorem conf_bridge_pos (S : Ctor → Prop) :
    ConfluentOnPos (ofCtor S) EqGuardedStep ↔ ConfluentOn S EqGuardedStep := by
  have hstar_to {x y : Trace}
      (h : CtxStarPos (ofCtor S) EqGuardedStep x y) :
      CtxStarOn S EqGuardedStep x y :=
    Relation.ReflTransGen.mono (fun _ _ => ctxOnPos_ofCtor_to_ctxOn S) h
  have hstar_from {x y : Trace}
      (h : CtxStarOn S EqGuardedStep x y) :
      CtxStarPos (ofCtor S) EqGuardedStep x y :=
    Relation.ReflTransGen.mono (fun _ _ => ctxOn_to_ctxOnPos_ofCtor S) h
  constructor
  · intro hconf a b c hab hac
    obtain ⟨d, hbd, hcd⟩ := hconf a b c (hstar_from hab) (hstar_from hac)
    exact ⟨d, hstar_to hbd, hstar_to hcd⟩
  · intro hconf a b c hab hac
    obtain ⟨d, hbd, hcd⟩ := hconf a b c (hstar_to hab) (hstar_to hac)
    exact ⟨d, hstar_from hbd, hstar_from hcd⟩

/-! ## B2-S peak family (R5 join + non-triviality stuck) -/

/-- B2-S Probe A selection: `eqW` frozen, `appL` frozen, `appR` thawed, rest
thawed. -/
def selAppRThawed : CtorPos → Prop
  | .eqW => False
  | .appL => False
  | _ => True

/-- B2-S Probe B selection: `eqW` frozen, `appR` frozen, `appL` thawed, rest
thawed. -/
def selAppRFrozen : CtorPos → Prop
  | .eqW => False
  | .appR => False
  | _ => True

/-- B1 refutation peak, reused as the recB family. -/
def b1Peak : Trace :=
  .recΔ (.merge .void .void) .void (.delta .void)

def b1RootReduct : Trace :=
  .app .void (.recΔ (.merge .void .void) .void .void)

def b1CongReduct : Trace :=
  .recΔ .void .void (.delta .void)

def b1ExpectedJoin : Trace :=
  .app .void (.recΔ .void .void .void)

private theorem no_ctxOnPos_from_void {S : CtorPos → Prop} {u : Trace} :
    ¬ CtxOnPos S EqGuardedStep .void u := by
  intro h
  cases h with
  | root hs => cases hs

private theorem ctxOnPos_deltaVoid_normal {S : CtorPos → Prop} {u : Trace} :
    ¬ CtxOnPos S EqGuardedStep (.delta .void) u := by
  intro h
  cases h with
  | root hs => cases hs
  | delta _ h' => exact no_ctxOnPos_from_void h'

/-- An `app void y` term is normal whenever `appR` is frozen: no root rule has
an `app` head, the left argument `void` is irreducible, and the right slot is
frozen. Relation: `CtxOnPos S EqGuardedStep`. Property: normal_form. -/
theorem ctxOnPos_app_void_left_stuck {S : CtorPos → Prop} (hR : ¬ S .appR)
    {y u : Trace} : ¬ CtxOnPos S EqGuardedStep (.app .void y) u := by
  intro h
  cases h with
  | root hs => cases hs
  | appL _ h' => exact no_ctxOnPos_from_void h'
  | appR enabled _ => exact hR enabled

private theorem ctxStarPos_eq_of_normal {S : CtorPos → Prop}
    {R : Trace → Trace → Prop} {x : Trace}
    (hx : ∀ u, ¬ CtxOnPos S R x u) {d : Trace}
    (h : CtxStarPos S R x d) : d = x := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact absurd (ih ▸ hstep) (hx _)

/-- R5: at the B1 peak, thawing `appR` with `appL` frozen joins.
Relation: `CtxOnPos selAppRThawed EqGuardedStep`. Closure:
`Relation.ReflTransGen`. Property: reachability. -/
theorem positional_peak_joins_appR_thawed :
    CtxStarPos selAppRThawed EqGuardedStep b1RootReduct b1ExpectedJoin ∧
      CtxStarPos selAppRThawed EqGuardedStep b1CongReduct b1ExpectedJoin :=
  ⟨Relation.ReflTransGen.single
      (CtxOnPos.appR trivial
        (CtxOnPos.recB trivial
          (CtxOnPos.root (EqGuardedStep.R_merge_void_left .void)))),
    Relation.ReflTransGen.single (CtxOnPos.root (EqGuardedStep.R_rec_succ _ _ _))⟩

/-- Congruence cone of the B1 recB peak, closed whenever `appR` is frozen. -/
def OnB1CongCone (x : Trace) : Prop :=
  x = b1CongReduct ∨ x = b1ExpectedJoin

theorem onB1CongCone_step {S : CtorPos → Prop} (hR : ¬ S .appR) {x y : Trace}
    (hx : OnB1CongCone x) (hxy : CtxOnPos S EqGuardedStep x y) :
    OnB1CongCone y := by
  rcases hx with rfl | rfl
  · cases hxy with
    | root hs =>
        cases hs with
        | R_rec_succ => exact Or.inr rfl
    | recB _ h' => exact absurd h' no_ctxOnPos_from_void
    | recS _ h' => exact absurd h' no_ctxOnPos_from_void
    | recN _ h' => exact absurd h' ctxOnPos_deltaVoid_normal
  · exact absurd hxy (ctxOnPos_app_void_left_stuck hR)

theorem onB1CongCone_star {S : CtorPos → Prop} (hR : ¬ S .appR) {x y : Trace}
    (hx : OnB1CongCone x) (hxy : CtxStarPos S EqGuardedStep x y) :
    OnB1CongCone y := by
  induction hxy with
  | refl => exact hx
  | tail _ hstep ih => exact onB1CongCone_step hR ih hstep

/-- Non-triviality: the mirror selection ( `appR` frozen, `appL` thawed) is
stuck at the B1 peak. Relation: `CtxOnPos selAppRFrozen EqGuardedStep`.
Property: non-confluence witness. -/
theorem positional_peak_stuck_appR_frozen :
    ¬ ∃ d : Trace,
        CtxStarPos selAppRFrozen EqGuardedStep b1RootReduct d ∧
          CtxStarPos selAppRFrozen EqGuardedStep b1CongReduct d := by
  rintro ⟨d, hdRoot, hdCong⟩
  have hdEq : d = b1RootReduct :=
    ctxStarPos_eq_of_normal
      (fun _ => ctxOnPos_app_void_left_stuck (fun h => h)) hdRoot
  have hcone : OnB1CongCone d :=
    onB1CongCone_star (fun h => h) (Or.inl rfl) hdCong
  rw [hdEq] at hcone
  rcases hcone with h | h
  · exact Trace.noConfusion h
  · injection h with _ h2
    injection h2 with h3 _ _
    exact Trace.noConfusion h3

/-! ## Necessity: eqW freeze, recD → appR, recD → appL -/

def instabilityWitness : Trace := .eqW (.merge .void .void) .void

def instabilityDifferenceVerdict : Trace :=
  .integrate (.merge (.merge .void .void) .void)

theorem instabilityWitness_to_difference (S : CtorPos → Prop) :
    CtxStarPos S EqGuardedStep instabilityWitness instabilityDifferenceVerdict := by
  apply Relation.ReflTransGen.single
  apply CtxOnPos.root
  exact EqGuardedStep.R_eq_diff _ _ ContextualConfluence.witness_args_distinct

theorem instabilityWitness_to_void {S : CtorPos → Prop} (heqW : S .eqW) :
    CtxStarPos S EqGuardedStep instabilityWitness .void := by
  have hmerge : CtxOnPos S EqGuardedStep (.merge .void .void) .void :=
    CtxOnPos.root (EqGuardedStep.R_merge_void_left .void)
  have hctx : CtxOnPos S EqGuardedStep instabilityWitness (.eqW .void .void) :=
    CtxOnPos.eqWL heqW hmerge
  have hrefl : CtxOnPos S EqGuardedStep (.eqW .void .void) .void :=
    CtxOnPos.root (EqGuardedStep.R_eq_refl .void)
  exact Relation.ReflTransGen.head hctx (Relation.ReflTransGen.single hrefl)

def OnInstabilityDifferenceCone (x : Trace) : Prop :=
  x = instabilityDifferenceVerdict ∨
  x = .integrate (.merge .void .void) ∨
  x = .integrate .void

private theorem ctxOnPos_merge_void_void {S : CtorPos → Prop} {u : Trace}
    (h : CtxOnPos S EqGuardedStep (.merge .void .void) u) : u = .void := by
  cases h with
  | root hs => cases hs <;> rfl
  | mergeL _ h' => exact absurd h' no_ctxOnPos_from_void
  | mergeR _ h' => exact absurd h' no_ctxOnPos_from_void

private theorem ctxOnPos_merge_mergeVoid_void {S : CtorPos → Prop} {u : Trace}
    (h : CtxOnPos S EqGuardedStep (.merge (.merge .void .void) .void) u) :
    u = .merge .void .void := by
  cases h with
  | root hs => cases hs; rfl
  | mergeL _ h' =>
      have hu := ctxOnPos_merge_void_void h'
      rw [hu]
  | mergeR _ h' => exact absurd h' no_ctxOnPos_from_void

theorem onInstabilityDifferenceCone_step {S : CtorPos → Prop} {x y : Trace}
    (hx : OnInstabilityDifferenceCone x)
    (hxy : CtxOnPos S EqGuardedStep x y) :
    OnInstabilityDifferenceCone y := by
  rcases hx with rfl | rfl | rfl
  · cases hxy with
    | root hs => cases hs
    | integrate _ hinner =>
        have hy := ctxOnPos_merge_mergeVoid_void hinner
        rw [hy]
        exact Or.inr (Or.inl rfl)
  · cases hxy with
    | root hs => cases hs
    | integrate _ hinner =>
        have hy := ctxOnPos_merge_void_void hinner
        rw [hy]
        exact Or.inr (Or.inr rfl)
  · cases hxy with
    | root hs => cases hs
    | integrate _ hinner => exact absurd hinner no_ctxOnPos_from_void

theorem onInstabilityDifferenceCone_star {S : CtorPos → Prop} {x y : Trace}
    (hx : OnInstabilityDifferenceCone x)
    (hxy : CtxStarPos S EqGuardedStep x y) :
    OnInstabilityDifferenceCone y := by
  induction hxy with
  | refl => exact hx
  | tail _ hstep ih => exact onInstabilityDifferenceCone_step ih hstep

theorem void_not_onInstabilityDifferenceCone :
    ¬ OnInstabilityDifferenceCone .void := by
  rintro (h | h | h) <;> exact Trace.noConfusion h

private theorem ctxStarPos_eqGuarded_sub_ctxStarFull {S : CtorPos → Prop}
    {a b : Trace} (h : CtxStarPos S EqGuardedStep a b) :
    ContextualDiagonalScope.CtxStar a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih
        (ctxOnPos_eqGuarded_sub_stepCtxFull S hstep)

theorem instabilityDifference_not_joinable_void (S : CtorPos → Prop) :
    ¬ ∃ d : Trace,
      CtxStarPos S EqGuardedStep instabilityDifferenceVerdict d ∧
      CtxStarPos S EqGuardedStep .void d := by
  rintro ⟨d, hdifference, hvoid⟩
  have hdvoid : d = .void :=
    ContextualDiagonalScope.ctxStar_void
      (ctxStarPos_eqGuarded_sub_ctxStarFull hvoid)
  subst d
  exact void_not_onInstabilityDifferenceCone
    (onInstabilityDifferenceCone_star (Or.inl rfl) hdifference)

/-- Necessity of the `eqW` freeze, transported to every positional selection.
Relation: `CtxOnPos S EqGuardedStep`. Property: non-confluence witness. -/
theorem eqW_congruence_breaks_confluence_pos {S : CtorPos → Prop}
    (heqW : S .eqW) : ¬ ConfluentOnPos S EqGuardedStep := by
  intro hconfluent
  obtain ⟨d, hdifference, hvoid⟩ := hconfluent instabilityWitness
    instabilityDifferenceVerdict .void
    (instabilityWitness_to_difference S)
    (instabilityWitness_to_void heqW)
  exact instabilityDifference_not_joinable_void S ⟨d, hdifference, hvoid⟩

/-- Necessity of `recD → appR`. The recB family of the B1 peak is stuck
whenever `appR` is frozen, even if `appL` is thawed. Relation:
`CtxOnPos S EqGuardedStep`. Property: non-confluence witness. -/
theorem recD_thaw_appR_freeze_breaks_confluence {S : CtorPos → Prop}
    (hrec : S .recD) (hR : ¬ S .appR) : ¬ ConfluentOnPos S EqGuardedStep := by
  intro hconfluent
  have hpeakRoot : CtxStarPos S EqGuardedStep b1Peak b1RootReduct :=
    Relation.ReflTransGen.single (CtxOnPos.root (EqGuardedStep.R_rec_succ _ _ _))
  have hpeakCong : CtxStarPos S EqGuardedStep b1Peak b1CongReduct :=
    Relation.ReflTransGen.single
      (CtxOnPos.recB hrec (CtxOnPos.root (EqGuardedStep.R_merge_void_left .void)))
  obtain ⟨d, hdApp, hdRec⟩ := hconfluent _ _ _ hpeakRoot hpeakCong
  have hdEq : d = b1RootReduct :=
    ctxStarPos_eq_of_normal (fun _ => ctxOnPos_app_void_left_stuck hR) hdApp
  have hcone : OnB1CongCone d := onB1CongCone_star hR (Or.inl rfl) hdRec
  rw [hdEq] at hcone
  rcases hcone with h | h
  · exact Trace.noConfusion h
  · injection h with _ h2
    injection h2 with h3 _ _
    exact Trace.noConfusion h3

/-- The recS peak: `R_rec_succ` copies a reducible step argument into the left
slot of `app`. This is the named open peak of the one-sided `recD → appR`
candidate. -/
def recSPeak : Trace :=
  .recΔ .void (.merge .void .void) (.delta .void)

def recSRootReduct : Trace :=
  .app (.merge .void .void) (.recΔ .void (.merge .void .void) .void)

def recSCongReduct : Trace :=
  .recΔ .void .void (.delta .void)

/-- Congruence cone of the recS peak. Closed for every positional selection. -/
def OnRecSCongCone (x : Trace) : Prop :=
  x = recSCongReduct ∨
  x = .app .void (.recΔ .void .void .void) ∨
  x = .app .void .void

theorem onRecSCongCone_step {S : CtorPos → Prop} {x y : Trace}
    (hx : OnRecSCongCone x) (hxy : CtxOnPos S EqGuardedStep x y) :
    OnRecSCongCone y := by
  rcases hx with rfl | rfl | rfl
  · cases hxy with
    | root hs =>
        cases hs with
        | R_rec_succ => exact Or.inr (Or.inl rfl)
    | recB _ h' => exact absurd h' no_ctxOnPos_from_void
    | recS _ h' => exact absurd h' no_ctxOnPos_from_void
    | recN _ h' => exact absurd h' ctxOnPos_deltaVoid_normal
  · cases hxy with
    | root hs => cases hs
    | appL _ h' => exact absurd h' no_ctxOnPos_from_void
    | appR _ h' =>
        cases h' with
        | root hs =>
            cases hs with
            | R_rec_zero => exact Or.inr (Or.inr rfl)
        | recB _ h'' => exact absurd h'' no_ctxOnPos_from_void
        | recS _ h'' => exact absurd h'' no_ctxOnPos_from_void
        | recN _ h'' => exact absurd h'' no_ctxOnPos_from_void
  · cases hxy with
    | root hs => cases hs
    | appL _ h' => exact absurd h' no_ctxOnPos_from_void
    | appR _ h' => exact absurd h' no_ctxOnPos_from_void

theorem onRecSCongCone_star {S : CtorPos → Prop} {x y : Trace}
    (hx : OnRecSCongCone x) (hxy : CtxStarPos S EqGuardedStep x y) :
    OnRecSCongCone y := by
  induction hxy with
  | refl => exact hx
  | tail _ hstep ih => exact onRecSCongCone_step ih hstep

private theorem ctxOnPos_app_mergeVoid_left_stays {S : CtorPos → Prop}
    (hL : ¬ S .appL) {t u : Trace}
    (h : CtxOnPos S EqGuardedStep (.app (.merge .void .void) t) u) :
    ∃ t', u = .app (.merge .void .void) t' := by
  cases h with
  | root hs => cases hs
  | appL enabled _ => exact absurd enabled hL
  | appR _ _ => exact ⟨_, rfl⟩

private theorem ctxStarPos_app_mergeVoid_left_stays {S : CtorPos → Prop}
    (hL : ¬ S .appL) {t d : Trace}
    (h : CtxStarPos S EqGuardedStep (.app (.merge .void .void) t) d) :
    ∃ t', d = .app (.merge .void .void) t' := by
  induction h with
  | refl => exact ⟨t, rfl⟩
  | tail _ hstep ih =>
      obtain ⟨t', rfl⟩ := ih
      exact ctxOnPos_app_mergeVoid_left_stays hL hstep

theorem app_mergeVoid_not_onRecSCongCone {t : Trace} :
    ¬ OnRecSCongCone (.app (.merge .void .void) t) := by
  rintro (h | h | h)
  · exact Trace.noConfusion h
  · injection h with h1 _
    exact Trace.noConfusion h1
  · injection h with h1 _
    exact Trace.noConfusion h1

/-- Necessity of `recD → appL`. The recS peak is unjoinable whenever `appL` is
frozen, even if `appR` is thawed. This is the refuting peak of the dispatch's
one-sided candidate `recD → appR`. Relation: `CtxOnPos S EqGuardedStep`.
Property: non-confluence witness. -/
theorem recD_thaw_appL_freeze_breaks_confluence {S : CtorPos → Prop}
    (hrec : S .recD) (hL : ¬ S .appL) : ¬ ConfluentOnPos S EqGuardedStep := by
  intro hconfluent
  have hpeakRoot : CtxStarPos S EqGuardedStep recSPeak recSRootReduct :=
    Relation.ReflTransGen.single (CtxOnPos.root (EqGuardedStep.R_rec_succ _ _ _))
  have hpeakCong : CtxStarPos S EqGuardedStep recSPeak recSCongReduct :=
    Relation.ReflTransGen.single
      (CtxOnPos.recS hrec (CtxOnPos.root (EqGuardedStep.R_merge_void_left .void)))
  obtain ⟨d, hdRoot, hdCong⟩ := hconfluent _ _ _ hpeakRoot hpeakCong
  obtain ⟨t', ht'⟩ := ctxStarPos_app_mergeVoid_left_stays hL hdRoot
  have hcone : OnRecSCongCone d :=
    onRecSCongCone_star (Or.inl rfl) hdCong
  rw [ht'] at hcone
  exact app_mergeVoid_not_onRecSCongCone hcone

/-- The dispatch's one-sided positional iff is false. The B2-S joining
selection satisfies `¬ eqW ∧ (recD → appR)` and fails confluence at `recSPeak`.
-/
theorem confluentOnPos_appR_only_iff_refuted :
    ¬ (∀ S : CtorPos → Prop,
        ConfluentOnPos S EqGuardedStep ↔
          (¬ S .eqW ∧ (S .recD → S .appR))) := by
  intro h
  have hrhs : ¬ selAppRThawed .eqW ∧
      (selAppRThawed .recD → selAppRThawed .appR) :=
    ⟨fun h => h, fun _ => trivial⟩
  have hconf : ConfluentOnPos selAppRThawed EqGuardedStep := (h _).mpr hrhs
  exact recD_thaw_appL_freeze_breaks_confluence trivial (fun h => h) hconf

/-! ## Star lifts and the complete local peak enumeration -/

theorem ctxStarPos_delta {S : CtorPos → Prop} {R : Trace → Trace → Prop}
    (enabled : S .delta) {t u : Trace} (h : CtxStarPos S R t u) :
    CtxStarPos S R (.delta t) (.delta u) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (CtxOnPos.delta enabled hstep)

theorem ctxStarPos_integrate {S : CtorPos → Prop} {R : Trace → Trace → Prop}
    (enabled : S .integrate) {t u : Trace} (h : CtxStarPos S R t u) :
    CtxStarPos S R (.integrate t) (.integrate u) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (CtxOnPos.integrate enabled hstep)

theorem ctxStarPos_mergeL {S : CtorPos → Prop} {R : Trace → Trace → Prop}
    (enabled : S .merge) {a a' b : Trace} (h : CtxStarPos S R a a') :
    CtxStarPos S R (.merge a b) (.merge a' b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (CtxOnPos.mergeL enabled hstep)

theorem ctxStarPos_mergeR {S : CtorPos → Prop} {R : Trace → Trace → Prop}
    (enabled : S .merge) {a b b' : Trace} (h : CtxStarPos S R b b') :
    CtxStarPos S R (.merge a b) (.merge a b') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (CtxOnPos.mergeR enabled hstep)

theorem ctxStarPos_appL {S : CtorPos → Prop} {R : Trace → Trace → Prop}
    (enabled : S .appL) {a a' b : Trace} (h : CtxStarPos S R a a') :
    CtxStarPos S R (.app a b) (.app a' b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (CtxOnPos.appL enabled hstep)

theorem ctxStarPos_appR {S : CtorPos → Prop} {R : Trace → Trace → Prop}
    (enabled : S .appR) {a b b' : Trace} (h : CtxStarPos S R b b') :
    CtxStarPos S R (.app a b) (.app a b') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (CtxOnPos.appR enabled hstep)

theorem ctxStarPos_recB {S : CtorPos → Prop} {R : Trace → Trace → Prop}
    (enabled : S .recD) {b b' s n : Trace} (h : CtxStarPos S R b b') :
    CtxStarPos S R (.recΔ b s n) (.recΔ b' s n) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (CtxOnPos.recB enabled hstep)

theorem ctxStarPos_recS {S : CtorPos → Prop} {R : Trace → Trace → Prop}
    (enabled : S .recD) {b s s' n : Trace} (h : CtxStarPos S R s s') :
    CtxStarPos S R (.recΔ b s n) (.recΔ b s' n) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (CtxOnPos.recS enabled hstep)

theorem ctxStarPos_recN {S : CtorPos → Prop} {R : Trace → Trace → Prop}
    (enabled : S .recD) {b s n n' : Trace} (h : CtxStarPos S R n n') :
    CtxStarPos S R (.recΔ b s n) (.recΔ b s n') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (CtxOnPos.recN enabled hstep)

/-- Root-versus-arbitrary peak enumeration under `eqW` frozen and the
two-sided alignment `recD → appL` and `recD → appR`. The recB and recN
families consume `appR`; the recS family consumes both `appL` and `appR`.
Relation: `CtxOnPos S EqGuardedStep`. Property: local peak joinability. -/
theorem ctxOnPos_root_peak_joins {S : CtorPos → Prop}
    (heqW : ¬ S .eqW) (halignL : S .recD → S .appL) (halignR : S .recD → S .appR)
    {a b c : Trace} (hr : EqGuardedStep a b)
    (hac : CtxOnPos S EqGuardedStep a c) :
    ∃ d : Trace, CtxStarPos S EqGuardedStep b d ∧ CtxStarPos S EqGuardedStep c d := by
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
                Relation.ReflTransGen.single
                  (CtxOnPos.root (EqGuardedStep.R_int_delta _))⟩
  | mergeL enabled h' =>
      cases hr with
      | R_merge_void_left => exact absurd h' no_ctxOnPos_from_void
      | R_merge_void_right =>
          exact ⟨_, Relation.ReflTransGen.single h',
            Relation.ReflTransGen.single
              (CtxOnPos.root (EqGuardedStep.R_merge_void_right _))⟩
      | R_merge_cancel =>
          refine ⟨_, Relation.ReflTransGen.single h', ?_⟩
          exact (Relation.ReflTransGen.single (CtxOnPos.mergeR enabled h')).tail
            (CtxOnPos.root (EqGuardedStep.R_merge_cancel _))
  | mergeR enabled h' =>
      cases hr with
      | R_merge_void_left =>
          exact ⟨_, Relation.ReflTransGen.single h',
            Relation.ReflTransGen.single
              (CtxOnPos.root (EqGuardedStep.R_merge_void_left _))⟩
      | R_merge_void_right => exact absurd h' no_ctxOnPos_from_void
      | R_merge_cancel =>
          refine ⟨_, Relation.ReflTransGen.single h', ?_⟩
          exact (Relation.ReflTransGen.single (CtxOnPos.mergeL enabled h')).tail
            (CtxOnPos.root (EqGuardedStep.R_merge_cancel _))
  | appL enabled h' => cases hr
  | appR enabled h' => cases hr
  | recB enabled h' =>
      cases hr with
      | R_rec_zero =>
          exact ⟨_, Relation.ReflTransGen.single h',
            Relation.ReflTransGen.single
              (CtxOnPos.root (EqGuardedStep.R_rec_zero _ _))⟩
      | R_rec_succ =>
          exact ⟨_,
            Relation.ReflTransGen.single
              (CtxOnPos.appR (halignR enabled) (CtxOnPos.recB enabled h')),
            Relation.ReflTransGen.single
              (CtxOnPos.root (EqGuardedStep.R_rec_succ _ _ _))⟩
  | recS enabled h' =>
      cases hr with
      | R_rec_zero =>
          exact ⟨_, Relation.ReflTransGen.refl,
            Relation.ReflTransGen.single
              (CtxOnPos.root (EqGuardedStep.R_rec_zero _ _))⟩
      | R_rec_succ =>
          exact ⟨_,
            (Relation.ReflTransGen.single
              (CtxOnPos.appL (halignL enabled) h')).tail
              (CtxOnPos.appR (halignR enabled) (CtxOnPos.recS enabled h')),
            Relation.ReflTransGen.single
              (CtxOnPos.root (EqGuardedStep.R_rec_succ _ _ _))⟩
  | recN enabled h' =>
      cases hr with
      | R_rec_zero => exact absurd h' no_ctxOnPos_from_void
      | R_rec_succ =>
          cases h' with
          | root hs => cases hs
          | delta _ h'' =>
              exact ⟨_,
                Relation.ReflTransGen.single
                  (CtxOnPos.appR (halignR enabled) (CtxOnPos.recN enabled h'')),
                Relation.ReflTransGen.single
                  (CtxOnPos.root (EqGuardedStep.R_rec_succ _ _ _))⟩
  | eqWL enabled h' => exact absurd enabled heqW
  | eqWR enabled h' => exact absurd enabled heqW

/-- Local confluence of the two-sided aligned frozen positional closure.
Relation: `CtxOnPos S EqGuardedStep`. Property: local_confluence. -/
theorem ctxOnPos_local_join {S : CtorPos → Prop}
    (heqW : ¬ S .eqW) (halignL : S .recD → S .appL) (halignR : S .recD → S .appR) :
    ∀ {a b : Trace}, CtxOnPos S EqGuardedStep a b →
      ∀ c : Trace, CtxOnPos S EqGuardedStep a c →
        ∃ d : Trace, CtxStarPos S EqGuardedStep b d ∧
          CtxStarPos S EqGuardedStep c d := by
  intro a b hab
  induction hab with
  | root hr =>
      intro c hac
      exact ctxOnPos_root_peak_joins heqW halignL halignR hr hac
  | delta enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr => cases hr
      | delta enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarPos_delta enabled hd₁, ctxStarPos_delta enabled hd₂⟩
  | integrate enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr =>
          obtain ⟨d, hd₁, hd₂⟩ :=
            ctxOnPos_root_peak_joins heqW halignL halignR hr
              (CtxOnPos.integrate enabled h₁)
          exact ⟨d, hd₂, hd₁⟩
      | integrate enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarPos_integrate enabled hd₁,
            ctxStarPos_integrate enabled hd₂⟩
  | mergeL enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr =>
          obtain ⟨d, hd₁, hd₂⟩ :=
            ctxOnPos_root_peak_joins heqW halignL halignR hr
              (CtxOnPos.mergeL enabled h₁)
          exact ⟨d, hd₂, hd₁⟩
      | mergeL enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarPos_mergeL enabled hd₁, ctxStarPos_mergeL enabled hd₂⟩
      | mergeR enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOnPos.mergeR enabled h₂),
            Relation.ReflTransGen.single (CtxOnPos.mergeL enabled h₁)⟩
  | mergeR enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr =>
          obtain ⟨d, hd₁, hd₂⟩ :=
            ctxOnPos_root_peak_joins heqW halignL halignR hr
              (CtxOnPos.mergeR enabled h₁)
          exact ⟨d, hd₂, hd₁⟩
      | mergeL enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOnPos.mergeL enabled h₂),
            Relation.ReflTransGen.single (CtxOnPos.mergeR enabled h₁)⟩
      | mergeR enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarPos_mergeR enabled hd₁, ctxStarPos_mergeR enabled hd₂⟩
  | appL enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr => cases hr
      | appL enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarPos_appL enabled hd₁, ctxStarPos_appL enabled hd₂⟩
      | appR enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOnPos.appR enabled₂ h₂),
            Relation.ReflTransGen.single (CtxOnPos.appL enabled h₁)⟩
  | appR enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr => cases hr
      | appL enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOnPos.appL enabled₂ h₂),
            Relation.ReflTransGen.single (CtxOnPos.appR enabled h₁)⟩
      | appR enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarPos_appR enabled hd₁, ctxStarPos_appR enabled hd₂⟩
  | recB enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr =>
          obtain ⟨d, hd₁, hd₂⟩ :=
            ctxOnPos_root_peak_joins heqW halignL halignR hr
              (CtxOnPos.recB enabled h₁)
          exact ⟨d, hd₂, hd₁⟩
      | recB enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarPos_recB enabled hd₁, ctxStarPos_recB enabled hd₂⟩
      | recS enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOnPos.recS enabled h₂),
            Relation.ReflTransGen.single (CtxOnPos.recB enabled h₁)⟩
      | recN enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOnPos.recN enabled h₂),
            Relation.ReflTransGen.single (CtxOnPos.recB enabled h₁)⟩
  | recS enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr =>
          obtain ⟨d, hd₁, hd₂⟩ :=
            ctxOnPos_root_peak_joins heqW halignL halignR hr
              (CtxOnPos.recS enabled h₁)
          exact ⟨d, hd₂, hd₁⟩
      | recB enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOnPos.recB enabled h₂),
            Relation.ReflTransGen.single (CtxOnPos.recS enabled h₁)⟩
      | recS enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarPos_recS enabled hd₁, ctxStarPos_recS enabled hd₂⟩
      | recN enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOnPos.recN enabled h₂),
            Relation.ReflTransGen.single (CtxOnPos.recS enabled h₁)⟩
  | recN enabled h₁ ih =>
      intro c hac
      cases hac with
      | root hr =>
          obtain ⟨d, hd₁, hd₂⟩ :=
            ctxOnPos_root_peak_joins heqW halignL halignR hr
              (CtxOnPos.recN enabled h₁)
          exact ⟨d, hd₂, hd₁⟩
      | recB enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOnPos.recB enabled h₂),
            Relation.ReflTransGen.single (CtxOnPos.recN enabled h₁)⟩
      | recS enabled₂ h₂ =>
          exact ⟨_, Relation.ReflTransGen.single (CtxOnPos.recS enabled h₂),
            Relation.ReflTransGen.single (CtxOnPos.recN enabled h₁)⟩
      | recN enabled₂ h₂ =>
          obtain ⟨d, hd₁, hd₂⟩ := ih _ h₂
          exact ⟨_, ctxStarPos_recN enabled hd₁, ctxStarPos_recN enabled hd₂⟩
  | eqWL enabled h₁ ih => exact absurd enabled heqW
  | eqWR enabled h₁ ih => exact absurd enabled heqW

private theorem ctxOnPos_join_star_star {S : CtorPos → Prop}
    (loc : ∀ {a b : Trace}, CtxOnPos S EqGuardedStep a b →
      ∀ c : Trace, CtxOnPos S EqGuardedStep a c →
        ∃ d : Trace, CtxStarPos S EqGuardedStep b d ∧
          CtxStarPos S EqGuardedStep c d) :
    ∀ x : Trace, Acc (CtxOnPosRev S EqGuardedStep) x →
      ∀ {y z : Trace}, CtxStarPos S EqGuardedStep x y →
        CtxStarPos S EqGuardedStep x z →
        ∃ d : Trace, CtxStarPos S EqGuardedStep y d ∧
          CtxStarPos S EqGuardedStep z d := by
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

/-- Sufficiency of the two-sided alignment. Freezing `eqW` restores confluence
of the positional closure whenever thawing `recD` thaws both `appL` and
`appR`. SN is inherited; no fresh measure. Relation:
`CtxOnPos S EqGuardedStep`. Property: confluence. -/
theorem freeze_eqW_recAppPosAligned_restores_confluence {S : CtorPos → Prop}
    (heqW : ¬ S .eqW) (halignL : S .recD → S .appL) (halignR : S .recD → S .appR) :
    ConfluentOnPos S EqGuardedStep := by
  intro a b c hab hac
  exact ctxOnPos_join_star_star (ctxOnPos_local_join heqW halignL halignR) a
    ((wf_ctxOnPos_eqGuarded_rev S).apply a) hab hac

/-- **Corrected positional crown.** Confluence holds exactly when `eqW` is
frozen and thawing `recD` thaws both `app` positions. The dispatch's one-sided
candidate `recD → appR` is refuted by `confluentOnPos_appR_only_iff_refuted`.
At `appL = appR = S .app` this recovers `confluentOn_eqGuarded_iff` via
`conf_bridge_pos`.

Relation: `CtxOnPos S EqGuardedStep`. Closure: `Relation.ReflTransGen`.
Property: confluence characterization. -/
theorem confluentOnPos_eqGuarded_iff (S : CtorPos → Prop) :
    ConfluentOnPos S EqGuardedStep ↔
      (¬ S .eqW ∧ (S .recD → S .appL) ∧ (S .recD → S .appR)) := by
  constructor
  · intro hconf
    refine ⟨fun heqW => eqW_congruence_breaks_confluence_pos heqW hconf, ?_, ?_⟩
    · intro hrec
      by_contra hL
      exact recD_thaw_appL_freeze_breaks_confluence hrec hL hconf
    · intro hrec
      by_contra hR
      exact recD_thaw_appR_freeze_breaks_confluence hrec hR hconf
  · rintro ⟨heqW, halignL, halignR⟩
    exact freeze_eqW_recAppPosAligned_restores_confluence heqW halignL halignR

end OperatorKO7.Meta.DistinctionBoundary.FreezePositions
