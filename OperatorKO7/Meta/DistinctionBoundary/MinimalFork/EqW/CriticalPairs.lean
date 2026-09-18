import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.Context
import OperatorKO7.Meta.Rewriting.CriticalPairComplete
import OperatorKO7.Meta.Rewriting.TerminationCriterion

/-!
# Deep first-order reification of the minimal equality-witness TRS

This file reifies the three-symbol/two-rule system in the repository's generic
first-order rewriting library. The reflexive rule remains nonlinear: the same
variable occurs twice on its left-hand side. Generic contextual rewriting and
critical-pair machinery therefore apply to the actual first-order artifact, not
to an ad-hoc root simulator.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork
namespace DeepEqW

open scoped OperatorKO7.Meta.Rewriting.Subst
open OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe v

/-- Exactly the three designated role-collapsed symbols. -/
inductive Sym where
  | same
  | different
  | eqW
  deriving DecidableEq, Fintype, Repr

/-- Two rule variables are sufficient: `x` and `y`. -/
abbrev Var := Fin 2

abbrev Tm := OperatorKO7.Meta.Rewriting.Term Sym Var
abbrev RenTm := OperatorKO7.Meta.Rewriting.Term Sym (OperatorKO7.Meta.Rewriting.RenVar Var)

/-- Deep constants and binary equality-witness constructor. -/
def tSame : Tm := .app .same []
def tDifferent : Tm := .app .different []
def tEqW (a b : Tm) : Tm := .app .eqW [a,b]

def x0 : Tm := .var 0
def x1 : Tm := .var 1

/-- Nonlinear reflexive rule `eqW(x,x) -> same`. -/
def reflRule : OperatorKO7.Meta.Rewriting.Rule Sym Var where
  lhs := tEqW x0 x0
  rhs := tSame
  lhs_isApp := rfl

/-- Totalized difference rule `eqW(x,y) -> different`. -/
def diffRule : OperatorKO7.Meta.Rewriting.Rule Sym Var where
  lhs := tEqW x0 x1
  rhs := tDifferent
  lhs_isApp := rfl

/-- The complete deep minimal TRS; there are no other rules. -/
def minimalTRS : OperatorKO7.Meta.Rewriting.TRS Sym Var := [reflRule, diffRule]

/-- The deep artifact contains exactly two syntactic rules. -/
theorem minimalTRS_rule_count : minimalTRS.length = 2 := rfl

/-- Both rules are present. -/
theorem reflRule_mem : reflRule ∈ minimalTRS := by simp [minimalTRS]
theorem diffRule_mem : diffRule ∈ minimalTRS := by simp [minimalTRS]

/-- The reflexive rule is genuinely nonlinear: its two arguments are the same variable. -/
theorem reflRule_nonlinear_shape :
    reflRule.lhs = .app .eqW [.var 0, .var 0] := rfl

/-- Ground encoding of the custom recursive syntax into the deep first-order syntax. -/
def encode : MiniEqWTerm → Tm
  | .same => tSame
  | .different => tDifferent
  | .eqW a b => tEqW (encode a) (encode b)

/-- Decoder for the well-formed ground image; variables and malformed arities are rejected. -/
def decode : Tm → Option MiniEqWTerm
  | .var _ => none
  | .app .same [] => some .same
  | .app .different [] => some .different
  | .app .eqW [a,b] =>
      match decode a, decode b with
      | some a', some b' => some (.eqW a' b')
      | _, _ => none
  | _ => none

@[simp] theorem decode_encode (t : MiniEqWTerm) : decode (encode t) = some t := by
  induction t with
  | same => rfl
  | different => rfl
  | eqW a b iha ihb => simp [encode, tEqW, decode, iha, ihb]

/-- Ground encoding is injective. -/
theorem encode_injective : Function.Injective encode := by
  intro a b h
  have := congrArg decode h
  simpa using this

/-- The encoded terms are variable-free. -/
theorem encode_is_ground (t : MiniEqWTerm) : OperatorKO7.Meta.Rewriting.Term.vars (encode t) = ∅ := by
  induction t with
  | same => simp [encode, tSame]
  | different => simp [encode, tDifferent]
  | eqW a b iha ihb =>
      simp [encode, tEqW, iha, ihb]

/- Query-symbol count on arbitrary deep terms. Variables contribute no query symbol. -/
mutual
def deepEqWCount {ν : Type v} : OperatorKO7.Meta.Rewriting.Term Sym ν → Nat
  | .var _ => 0
  | .app f args => (if f = .eqW then 1 else 0) + deepEqWCountList args

def deepEqWCountList {ν : Type v} : List (OperatorKO7.Meta.Rewriting.Term Sym ν) → Nat
  | [] => 0
  | a :: as => deepEqWCount a + deepEqWCountList as
end

@[simp] theorem deepEqWCount_tSame : deepEqWCount tSame = 0 := rfl
@[simp] theorem deepEqWCount_tDifferent : deepEqWCount tDifferent = 0 := rfl
@[simp] theorem deepEqWCount_tEqW (a b : Tm) :
    deepEqWCount (tEqW a b) = deepEqWCount a + deepEqWCount b + 1 := by
  simp [deepEqWCount, deepEqWCountList, tEqW]
  omega

/-- The deep count agrees with the custom count on the ground image. -/
theorem deepEqWCount_encode (t : MiniEqWTerm) :
    deepEqWCount (encode t) = miniEqWCount t := by
  induction t with
  | same => rfl
  | different => rfl
  | eqW a b iha ihb => simp [encode, miniEqWCount, iha, ihb]

/-- Substitution used by the reflexive custom-to-deep root bridge. -/
def reflSubst (a : MiniEqWTerm) : OperatorKO7.Meta.Rewriting.Subst Sym Var := fun _ => encode a

/-- Substitution used by the difference custom-to-deep root bridge. -/
def diffSubst (a b : MiniEqWTerm) : OperatorKO7.Meta.Rewriting.Subst Sym Var := fun i =>
  if i = (0 : Var) then encode a else encode b

/-- Every custom raw root step is a genuine generic deep root step. -/
theorem customRoot_to_deepRoot {s t : MiniEqWTerm}
    (h : MiniEqWRootStep s t) :
    OperatorKO7.Meta.Rewriting.rootStep minimalTRS (encode s) (encode t) := by
  cases h with
  | refl a =>
      refine ⟨reflRule, reflRule_mem, reflSubst a, ?_, ?_⟩
      · simp [encode, tEqW, reflRule, x0, reflSubst, OperatorKO7.Meta.Rewriting.Subst.apply,
          OperatorKO7.Meta.Rewriting.Subst.applyList]
      · simp [encode, tSame, reflRule,
          OperatorKO7.Meta.Rewriting.Subst.applyList]
  | diff a b =>
      refine ⟨diffRule, diffRule_mem, diffSubst a b, ?_, ?_⟩
      · simp [encode, tEqW, diffRule, x0, x1, diffSubst, OperatorKO7.Meta.Rewriting.Subst.apply,
          OperatorKO7.Meta.Rewriting.Subst.applyList]
      · simp [encode, tDifferent, diffRule,
          OperatorKO7.Meta.Rewriting.Subst.applyList]

/-- Exact first-order rule inventory: any rule in the TRS is one of the two declarations. -/
theorem mem_minimalTRS_iff {r : OperatorKO7.Meta.Rewriting.Rule Sym Var} :
    r ∈ minimalTRS ↔ r = reflRule ∨ r = diffRule := by
  simp [minimalTRS]

/-- Every generic deep root step between encoded ground terms reflects to the
custom raw root relation. Malformed substitution images are excluded by decoding
the equality with the encoded source. -/
theorem deepRoot_to_customRoot {s t : MiniEqWTerm}
    (h : OperatorKO7.Meta.Rewriting.rootStep minimalTRS (encode s) (encode t)) :
    MiniEqWRootStep s t := by
  rcases h with ⟨r, hr, σ, hs, ht⟩
  rcases (mem_minimalTRS_iff.mp hr) with rfl | rfl
  · have hsource := congrArg decode hs
    have htarget := congrArg decode ht
    cases h0 : decode (σ 0) with
    | none =>
        simp [reflRule, tEqW, tSame, x0, decode,
          OperatorKO7.Meta.Rewriting.Subst.apply, OperatorKO7.Meta.Rewriting.Subst.applyList, h0] at hsource
    | some q =>
        have hsq : s = .eqW q q := by
          simpa [encode, reflRule, tEqW, tSame, x0, decode,
            OperatorKO7.Meta.Rewriting.Subst.apply, OperatorKO7.Meta.Rewriting.Subst.applyList, h0] using hsource
        have htq : t = .same := by
          simpa [encode, reflRule, tSame, decode,
            OperatorKO7.Meta.Rewriting.Subst.apply, OperatorKO7.Meta.Rewriting.Subst.applyList] using htarget
        subst s
        subst t
        exact MiniEqWRootStep.refl q
  · have hsource := congrArg decode hs
    have htarget := congrArg decode ht
    cases h0 : decode (σ 0) with
    | none =>
        simp [diffRule, tEqW, tDifferent, x0, x1, decode,
          OperatorKO7.Meta.Rewriting.Subst.apply, OperatorKO7.Meta.Rewriting.Subst.applyList, h0] at hsource
    | some q0 =>
      cases h1 : decode (σ 1) with
      | none =>
          simp [diffRule, tEqW, tDifferent, x0, x1, decode,
            OperatorKO7.Meta.Rewriting.Subst.apply, OperatorKO7.Meta.Rewriting.Subst.applyList, h0, h1] at hsource
      | some q1 =>
          have hs12 : s = .eqW q0 q1 := by
            simpa [encode, diffRule, tEqW, tDifferent, x0, x1, decode,
              OperatorKO7.Meta.Rewriting.Subst.apply, OperatorKO7.Meta.Rewriting.Subst.applyList, h0, h1] using hsource
          have htq : t = .different := by
            simpa [encode, diffRule, tDifferent, decode,
              OperatorKO7.Meta.Rewriting.Subst.apply, OperatorKO7.Meta.Rewriting.Subst.applyList] using htarget
          subst s
          subst t
          exact MiniEqWRootStep.diff q0 q1

/-- Root correspondence is exact on encoded ground terms. -/
theorem customRoot_iff_deepRoot {s t : MiniEqWTerm} :
    MiniEqWRootStep s t ↔ OperatorKO7.Meta.Rewriting.rootStep minimalTRS (encode s) (encode t) :=
  ⟨customRoot_to_deepRoot, deepRoot_to_customRoot⟩

/-- Every custom raw root step is therefore a generic contextual `Step`. -/
theorem customRoot_to_deepStep {s t : MiniEqWTerm}
    (h : MiniEqWRootStep s t) :
    OperatorKO7.Meta.Rewriting.Step minimalTRS (encode s) (encode t) :=
  OperatorKO7.Meta.Rewriting.Step.root (customRoot_to_deepRoot h)

/-- Every custom context step transports to the generic deep contextual relation. -/
theorem customCtx_to_deepStep {s t : MiniEqWTerm}
    (h : MiniEqWCtxStep s t) :
    OperatorKO7.Meta.Rewriting.Step minimalTRS (encode s) (encode t) := by
  induction h with
  | root hr => exact customRoot_to_deepStep hr
  | @left a a' b _ ih =>
      simpa [encode, tEqW] using OperatorKO7.Meta.Rewriting.Step.arg .eqW [] [encode b] ih
  | @right a b b' _ ih =>
      simpa [encode, tEqW] using OperatorKO7.Meta.Rewriting.Step.arg .eqW [encode a] [] ih

/-- Every generic deep contextual step between encoded ground terms reflects
exactly to the custom unrestricted context relation.  The only non-root generic
contexts compatible with the encoded image are the left and right arguments of
`eqW`; the list-shape proof below excludes every malformed or deeper-arity
context rather than assuming image closure. -/
theorem deepStep_to_customCtx {s t : MiniEqWTerm}
    (h : OperatorKO7.Meta.Rewriting.Step minimalTRS (encode s) (encode t)) :
    MiniEqWCtxStep s t := by
  generalize hs : encode s = ds at h
  generalize ht : encode t = dt at h
  induction h generalizing s t with
  | root hr =>
      rw [← hs, ← ht] at hr
      exact MiniEqWCtxStep.root (deepRoot_to_customRoot hr)
  | @arg f pre post a b hab ih =>
      cases s <;> cases t <;>
        simp [encode, tSame, tDifferent, tEqW] at hs ht
      case eqW.eqW sa sb ta tb =>
        rcases hs with ⟨rfl, hs⟩
        rcases ht with ⟨_, ht⟩
        cases pre with
        | nil =>
            simp at hs ht
            have hsb : sb = tb := encode_injective (by
              have hsingleton : [encode sb] = [encode tb] := hs.2.trans ht.2.symm
              simpa using hsingleton)
            subst tb
            exact MiniEqWCtxStep.left (ih hs.1 ht.1)
        | cons p pre' =>
            cases pre' with
            | nil =>
                simp at hs ht
                have hsa : sa = ta := encode_injective (hs.1.trans ht.1.symm)
                subst ta
                exact MiniEqWCtxStep.right (ih hs.2.1 ht.2.1)
            | cons q pre'' =>
                simp at hs

/-- The compact custom context relation and the generic first-order rewrite
relation are identical on encoded ground terms. -/
theorem customCtx_iff_deepStep {s t : MiniEqWTerm} :
    MiniEqWCtxStep s t ↔
      OperatorKO7.Meta.Rewriting.Step minimalTRS (encode s) (encode t) :=
  ⟨customCtx_to_deepStep, deepStep_to_customCtx⟩

/-- A generic root contraction starting in the encoded image remains in that
image and carries an exact custom root-step witness. -/
theorem deepRoot_from_encode {s : MiniEqWTerm} {u : Tm}
    (h : OperatorKO7.Meta.Rewriting.rootStep minimalTRS (encode s) u) :
    ∃ t : MiniEqWTerm, u = encode t ∧ MiniEqWRootStep s t := by
  rcases h with ⟨r, hr, σ, hs, ht⟩
  rcases (mem_minimalTRS_iff.mp hr) with rfl | rfl
  · have hsource := congrArg decode hs
    cases h0 : decode (σ 0) with
    | none =>
        simp [reflRule, tEqW, tSame, x0, decode,
          OperatorKO7.Meta.Rewriting.Subst.apply,
          OperatorKO7.Meta.Rewriting.Subst.applyList, h0] at hsource
    | some q =>
        have hsq : s = .eqW q q := by
          simpa [encode, reflRule, tEqW, tSame, x0, decode,
            OperatorKO7.Meta.Rewriting.Subst.apply,
            OperatorKO7.Meta.Rewriting.Subst.applyList, h0] using hsource
        have hut : u = encode .same := by
          simpa [encode, tSame, reflRule,
            OperatorKO7.Meta.Rewriting.Subst.applyList] using ht
        subst s
        exact ⟨.same, hut, MiniEqWRootStep.refl q⟩
  · have hsource := congrArg decode hs
    cases h0 : decode (σ 0) with
    | none =>
        simp [diffRule, tEqW, tDifferent, x0, x1, decode,
          OperatorKO7.Meta.Rewriting.Subst.apply,
          OperatorKO7.Meta.Rewriting.Subst.applyList, h0] at hsource
    | some q0 =>
      cases h1 : decode (σ 1) with
      | none =>
          simp [diffRule, tEqW, tDifferent, x0, x1, decode,
            OperatorKO7.Meta.Rewriting.Subst.apply,
            OperatorKO7.Meta.Rewriting.Subst.applyList, h0, h1] at hsource
      | some q1 =>
          have hs12 : s = .eqW q0 q1 := by
            simpa [encode, diffRule, tEqW, tDifferent, x0, x1, decode,
              OperatorKO7.Meta.Rewriting.Subst.apply,
              OperatorKO7.Meta.Rewriting.Subst.applyList, h0, h1] using hsource
          have hut : u = encode .different := by
            simpa [encode, tDifferent, diffRule,
              OperatorKO7.Meta.Rewriting.Subst.applyList] using ht
          subst s
          exact ⟨.different, hut, MiniEqWRootStep.diff q0 q1⟩

/-- The encoded ground-term image is forward closed under the generic contextual
rewrite relation, and the image successor comes with the corresponding custom
context step. -/
theorem deepStep_from_encode {s : MiniEqWTerm} {u : Tm}
    (h : OperatorKO7.Meta.Rewriting.Step minimalTRS (encode s) u) :
    ∃ t : MiniEqWTerm, u = encode t ∧ MiniEqWCtxStep s t := by
  generalize hs : encode s = ds at h
  induction h generalizing s with
  | root hr =>
      rw [← hs] at hr
      rcases deepRoot_from_encode hr with ⟨t, rfl, hst⟩
      exact ⟨t, rfl, MiniEqWCtxStep.root hst⟩
  | @arg f pre post a b hab ih =>
      cases s <;> simp [encode, tSame, tDifferent, tEqW] at hs
      case eqW sa sb =>
        rcases hs with ⟨rfl, hs⟩
        cases pre with
        | nil =>
            simp at hs
            rcases ih hs.1 with ⟨ta, hb, hstep⟩
            refine ⟨.eqW ta sb, ?_, MiniEqWCtxStep.left hstep⟩
            rw [hb, ← hs.2]
            rfl
        | cons p pre' =>
            cases pre' with
            | nil =>
                simp at hs
                rcases ih hs.2.1 with ⟨tb, hb, hstep⟩
                refine ⟨.eqW sa tb, ?_, MiniEqWCtxStep.right hstep⟩
                rw [hb, ← hs.1, hs.2.2]
                rfl
            | cons q pre'' =>
                simp at hs

/-- The entire generic deep reduction cone below an encoded term stays in the
encoded image, with an exact custom reachability witness. -/
theorem deepStepStar_from_encode {s : MiniEqWTerm} {u : Tm}
    (h : OperatorKO7.Meta.Rewriting.StepStar minimalTRS (encode s) u) :
    ∃ t : MiniEqWTerm, u = encode t ∧ Reach MiniEqWCtxStep s t := by
  induction h with
  | refl => exact ⟨s, rfl, reach_refl _⟩
  | tail hstar hstep ih =>
      rcases ih with ⟨m, rfl, hsm⟩
      rcases deepStep_from_encode hstep with ⟨t, hut, hmt⟩
      exact ⟨t, hut, reach_trans hsm (reach_step hmt)⟩

/-- Exact closure preservation from the custom path encoding into the generic
first-order reflexive-transitive closure. -/
theorem customReach_to_deepStepStar {s t : MiniEqWTerm}
    (h : Reach MiniEqWCtxStep s t) :
    OperatorKO7.Meta.Rewriting.StepStar minimalTRS (encode s) (encode t) := by
  rcases h with ⟨n, hn⟩
  induction hn with
  | zero => exact OperatorKO7.Meta.Rewriting.StepStar.refl minimalTRS _
  | @succ n a b c hab hbc ih =>
      exact OperatorKO7.Meta.Rewriting.StepStar.head
        (customCtx_to_deepStep hab) ih

/-- Exact closure reflection from the generic deep TRS back to the custom path
encoding, again restricted to encoded ground terms. -/
theorem deepStepStar_to_customReach {s t : MiniEqWTerm}
    (h : OperatorKO7.Meta.Rewriting.StepStar minimalTRS (encode s) (encode t)) :
    Reach MiniEqWCtxStep s t := by
  rcases deepStepStar_from_encode h with ⟨u, htu, hreach⟩
  have hEq : t = u := encode_injective htu
  subst u
  exact hreach

/-- The two reflexive-transitive closure artifacts agree exactly on the encoded
minimal equality-witness language. -/
theorem customReach_iff_deepStepStar {s t : MiniEqWTerm} :
    Reach MiniEqWCtxStep s t ↔
      OperatorKO7.Meta.Rewriting.StepStar minimalTRS (encode s) (encode t) :=
  ⟨customReach_to_deepStepStar, deepStepStar_to_customReach⟩

/-- Deep root normal forms for the two verdict constants. -/
theorem tSame_root_normal : ∀ u, ¬ OperatorKO7.Meta.Rewriting.rootStep minimalTRS tSame u := by
  intro u h
  rcases h with ⟨r, hr, σ, hs, _⟩
  rcases (mem_minimalTRS_iff.mp hr) with rfl | rfl <;>
    simp [tSame, reflRule, diffRule, tEqW, x0, x1,
      OperatorKO7.Meta.Rewriting.Subst.apply, OperatorKO7.Meta.Rewriting.Subst.applyList] at hs

/-- `different` is also a deep root normal form. -/
theorem tDifferent_root_normal : ∀ u, ¬ OperatorKO7.Meta.Rewriting.rootStep minimalTRS tDifferent u := by
  intro u h
  rcases h with ⟨r, hr, σ, hs, _⟩
  rcases (mem_minimalTRS_iff.mp hr) with rfl | rfl <;>
    simp [tDifferent, reflRule, diffRule, tEqW, x0, x1,
      OperatorKO7.Meta.Rewriting.Subst.apply, OperatorKO7.Meta.Rewriting.Subst.applyList] at hs

/-- Deep list count is additive over append. -/
theorem deepEqWCountList_append {ν : Type v} (xs ys : List (OperatorKO7.Meta.Rewriting.Term Sym ν)) :
    deepEqWCountList (xs ++ ys) = deepEqWCountList xs + deepEqWCountList ys := by
  induction xs with
  | nil => simp [deepEqWCountList]
  | cons x xs ih => simp [deepEqWCountList, ih, Nat.add_assoc]

/-- Every generic deep root contraction strictly lowers the EqW-symbol count. -/
theorem deepRoot_count_decreases {s t : Tm}
    (h : OperatorKO7.Meta.Rewriting.rootStep minimalTRS s t) :
    deepEqWCount t < deepEqWCount s := by
  rcases h with ⟨r, hr, σ, hs, ht⟩
  rcases (mem_minimalTRS_iff.mp hr) with rfl | rfl
  · rw [hs, ht]
    simp [reflRule, tEqW, tSame, x0, deepEqWCount, deepEqWCountList,
      OperatorKO7.Meta.Rewriting.Subst.apply, OperatorKO7.Meta.Rewriting.Subst.applyList]
  · rw [hs, ht]
    simp [diffRule, tEqW, tDifferent, x0, x1, deepEqWCount, deepEqWCountList,
      OperatorKO7.Meta.Rewriting.Subst.apply, OperatorKO7.Meta.Rewriting.Subst.applyList]

/-- Every generic deep contextual step strictly lowers the EqW-symbol count. -/
theorem deepStep_count_decreases {s t : Tm}
    (h : OperatorKO7.Meta.Rewriting.Step minimalTRS s t) : deepEqWCount t < deepEqWCount s := by
  induction h with
  | root hr => exact deepRoot_count_decreases hr
  | @arg f pre post a b hab ih =>
      simp only [deepEqWCount, deepEqWCountList_append, deepEqWCountList]
      omega

/-- The generic deep TRS is strongly normalizing under unrestricted context rewriting. -/
theorem deep_minimalTRS_SN : WellFounded (flip (OperatorKO7.Meta.Rewriting.Step minimalTRS)) :=
  OperatorKO7.Meta.Rewriting.sn_of_natMeasure minimalTRS deepEqWCount
    (fun _ _ h => deepStep_count_decreases h)

/-- Renamed verdict constants used by the generic critical-pair system. -/
def renSame : RenTm := .app .same []
def renDifferent : RenTm := .app .different []

def badCriticalPair : RenTm × RenTm := (renSame, renDifferent)
def badCriticalPairSymm : RenTm × RenTm := (renDifferent, renSame)

/-- Exact rule inventory of the renamed two-rule system. -/
theorem mem_renamed_minimalTRS_iff
    {r : OperatorKO7.Meta.Rewriting.Rule Sym (OperatorKO7.Meta.Rewriting.RenVar Var)} :
    r ∈ OperatorKO7.Meta.Rewriting.renameTRS minimalTRS ↔
      r = OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) reflRule ∨
      r = OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) diffRule ∨
      r = OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) reflRule ∨
      r = OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) diffRule := by
  simp [OperatorKO7.Meta.Rewriting.renameTRS, minimalTRS]

/-- Every root step of the renamed TRS strictly lowers the same structural count. -/
theorem deepRenamedRoot_count_decreases {s t : RenTm}
    (h : OperatorKO7.Meta.Rewriting.rootStep (OperatorKO7.Meta.Rewriting.renameTRS minimalTRS) s t) :
    deepEqWCount t < deepEqWCount s := by
  rcases h with ⟨r, hr, σ, hs, ht⟩
  rcases (mem_renamed_minimalTRS_iff.mp hr) with rfl | rfl | rfl | rfl
  all_goals
    rw [hs, ht]
    simp [OperatorKO7.Meta.Rewriting.renameRule, reflRule, diffRule,
      tEqW, tSame, tDifferent, x0, x1, deepEqWCount, deepEqWCountList,
      OperatorKO7.Meta.Rewriting.Term.rename, OperatorKO7.Meta.Rewriting.Term.renameList,
      OperatorKO7.Meta.Rewriting.Subst.apply, OperatorKO7.Meta.Rewriting.Subst.applyList]

/-- Every contextual step of the renamed TRS strictly lowers the structural count. -/
theorem deepRenamedStep_count_decreases {s t : RenTm}
    (h : OperatorKO7.Meta.Rewriting.Step (OperatorKO7.Meta.Rewriting.renameTRS minimalTRS) s t) :
    deepEqWCount t < deepEqWCount s := by
  induction h with
  | root hr => exact deepRenamedRoot_count_decreases hr
  | @arg f pre post a b hab ih =>
      simp only [deepEqWCount, deepEqWCountList_append, deepEqWCountList]
      omega

/-- The renamed critical-pair system is strongly normalizing too. -/
theorem deep_renamed_minimalTRS_SN :
    WellFounded (flip (OperatorKO7.Meta.Rewriting.Step (OperatorKO7.Meta.Rewriting.renameTRS minimalTRS))) :=
  OperatorKO7.Meta.Rewriting.sn_of_natMeasure (OperatorKO7.Meta.Rewriting.renameTRS minimalTRS) deepEqWCount
    (fun _ _ h => deepRenamedStep_count_decreases h)

/-- The renamed equal verdict has no outgoing contextual rewrite. -/
theorem renSame_normal :
    ¬ ∃ u, OperatorKO7.Meta.Rewriting.Step (OperatorKO7.Meta.Rewriting.renameTRS minimalTRS) renSame u := by
  rintro ⟨u, h⟩
  have hd := deepRenamedStep_count_decreases h
  simp [renSame, deepEqWCount, deepEqWCountList] at hd

/-- The renamed difference verdict has no outgoing contextual rewrite. -/
theorem renDifferent_normal :
    ¬ ∃ u, OperatorKO7.Meta.Rewriting.Step (OperatorKO7.Meta.Rewriting.renameTRS minimalTRS) renDifferent u := by
  rintro ⟨u, h⟩
  have hd := deepRenamedStep_count_decreases h
  simp [renDifferent, deepEqWCount, deepEqWCountList] at hd

/-- Reachability from a step-normal term in the renamed system is trivial. -/
theorem eq_of_renamed_normal_stepStar
    {x y : RenTm}
    (hn : ¬ ∃ u, OperatorKO7.Meta.Rewriting.Step
      (OperatorKO7.Meta.Rewriting.renameTRS minimalTRS) x u)
    (h : OperatorKO7.Meta.Rewriting.StepStar
      (OperatorKO7.Meta.Rewriting.renameTRS minimalTRS) x y) : x = y := by
  induction h with
  | refl => rfl
  | tail hab hbc ih =>
      rw [← ih] at hbc
      exact False.elim (hn ⟨_, hbc⟩)

/-- The two renamed verdict constants are not joinable. -/
theorem badCriticalPair_not_joinable :
    ¬ OperatorKO7.Meta.Rewriting.joinable (OperatorKO7.Meta.Rewriting.renameTRS minimalTRS) renSame renDifferent := by
  rintro ⟨z, hsz, hdz⟩
  have hSame : renSame = z := eq_of_renamed_normal_stepStar renSame_normal hsz
  have hDiff : renDifferent = z := eq_of_renamed_normal_stepStar renDifferent_normal hdz
  have : renSame = renDifferent := hSame.trans hDiff.symm
  cases this

/-- Constant substitution witnessing that every ordered pair of the two rule
left-hand sides has a common root instance. -/
def allSameRenSubst : OperatorKO7.Meta.Rewriting.Subst Sym
    (OperatorKO7.Meta.Rewriting.RenVar Var) := fun _ => renSame

private theorem overlapAt_root_refl_refl :
    OperatorKO7.Meta.Rewriting.overlapAt
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) reflRule)
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) reflRule) [] =
      some (renSame, renSame) := by
  have hsub : OperatorKO7.Meta.Rewriting.Term.subtermAt
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) reflRule).lhs [] =
      some (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) reflRule).lhs := by simp
  have hcommon :
      OperatorKO7.Meta.Rewriting.Subst.apply allSameRenSubst
        (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) reflRule).lhs =
      OperatorKO7.Meta.Rewriting.Subst.apply allSameRenSubst
        (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) reflRule).lhs := by
    simp [allSameRenSubst, renSame, OperatorKO7.Meta.Rewriting.renameRule,
      reflRule, tEqW, x0, OperatorKO7.Meta.Rewriting.Term.rename,
      OperatorKO7.Meta.Rewriting.Term.renameList, OperatorKO7.Meta.Rewriting.Subst.apply,
      OperatorKO7.Meta.Rewriting.Subst.applyList]
  obtain ⟨c1, c2, hpair, _ρ, _h1, _h2⟩ :=
    OperatorKO7.Meta.Rewriting.overlapAt_complete
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) reflRule)
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) reflRule) [] hsub hcommon
  obtain ⟨_sub, μ, _hs, _hu, hc1, hc2⟩ :=
    OperatorKO7.Meta.Rewriting.overlapAt_eq_some hpair
  have hc1' : c1 = renSame := by
    simpa [renSame, OperatorKO7.Meta.Rewriting.renameRule, reflRule, tSame,
      OperatorKO7.Meta.Rewriting.Term.rename, OperatorKO7.Meta.Rewriting.Term.renameList,
      OperatorKO7.Meta.Rewriting.Subst.apply, OperatorKO7.Meta.Rewriting.Subst.applyList] using hc1
  have hc2' : c2 = renSame := by
    simpa [renSame, OperatorKO7.Meta.Rewriting.renameRule, reflRule, tSame,
      OperatorKO7.Meta.Rewriting.Term.replaceAt, OperatorKO7.Meta.Rewriting.Term.rename,
      OperatorKO7.Meta.Rewriting.Term.renameList, OperatorKO7.Meta.Rewriting.Subst.apply,
      OperatorKO7.Meta.Rewriting.Subst.applyList] using hc2
  subst c1
  subst c2
  exact hpair

private theorem overlapAt_root_refl_diff :
    OperatorKO7.Meta.Rewriting.overlapAt
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) reflRule)
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) diffRule) [] =
      some (renSame, renDifferent) := by
  have hsub : OperatorKO7.Meta.Rewriting.Term.subtermAt
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) reflRule).lhs [] =
      some (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) reflRule).lhs := by simp
  have hcommon :
      OperatorKO7.Meta.Rewriting.Subst.apply allSameRenSubst
        (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) reflRule).lhs =
      OperatorKO7.Meta.Rewriting.Subst.apply allSameRenSubst
        (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) diffRule).lhs := by
    simp [allSameRenSubst, renSame, OperatorKO7.Meta.Rewriting.renameRule,
      reflRule, diffRule, tEqW, x0, x1, OperatorKO7.Meta.Rewriting.Term.rename,
      OperatorKO7.Meta.Rewriting.Term.renameList, OperatorKO7.Meta.Rewriting.Subst.apply,
      OperatorKO7.Meta.Rewriting.Subst.applyList]
  obtain ⟨c1, c2, hpair, _ρ, _h1, _h2⟩ :=
    OperatorKO7.Meta.Rewriting.overlapAt_complete
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) reflRule)
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) diffRule) [] hsub hcommon
  obtain ⟨_sub, μ, _hs, _hu, hc1, hc2⟩ :=
    OperatorKO7.Meta.Rewriting.overlapAt_eq_some hpair
  have hc1' : c1 = renSame := by
    simpa [renSame, OperatorKO7.Meta.Rewriting.renameRule, reflRule, tSame,
      OperatorKO7.Meta.Rewriting.Term.rename, OperatorKO7.Meta.Rewriting.Term.renameList,
      OperatorKO7.Meta.Rewriting.Subst.apply, OperatorKO7.Meta.Rewriting.Subst.applyList] using hc1
  have hc2' : c2 = renDifferent := by
    simpa [renDifferent, OperatorKO7.Meta.Rewriting.renameRule, diffRule, tDifferent,
      OperatorKO7.Meta.Rewriting.Term.replaceAt, OperatorKO7.Meta.Rewriting.Term.rename,
      OperatorKO7.Meta.Rewriting.Term.renameList, OperatorKO7.Meta.Rewriting.Subst.apply,
      OperatorKO7.Meta.Rewriting.Subst.applyList] using hc2
  subst c1
  subst c2
  exact hpair

private theorem overlapAt_root_diff_refl :
    OperatorKO7.Meta.Rewriting.overlapAt
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) diffRule)
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) reflRule) [] =
      some (renDifferent, renSame) := by
  have hsub : OperatorKO7.Meta.Rewriting.Term.subtermAt
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) diffRule).lhs [] =
      some (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) diffRule).lhs := by simp
  have hcommon :
      OperatorKO7.Meta.Rewriting.Subst.apply allSameRenSubst
        (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) diffRule).lhs =
      OperatorKO7.Meta.Rewriting.Subst.apply allSameRenSubst
        (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) reflRule).lhs := by
    simp [allSameRenSubst, renSame, OperatorKO7.Meta.Rewriting.renameRule,
      reflRule, diffRule, tEqW, x0, x1, OperatorKO7.Meta.Rewriting.Term.rename,
      OperatorKO7.Meta.Rewriting.Term.renameList, OperatorKO7.Meta.Rewriting.Subst.apply,
      OperatorKO7.Meta.Rewriting.Subst.applyList]
  obtain ⟨c1, c2, hpair, _ρ, _h1, _h2⟩ :=
    OperatorKO7.Meta.Rewriting.overlapAt_complete
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) diffRule)
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) reflRule) [] hsub hcommon
  obtain ⟨_sub, μ, _hs, _hu, hc1, hc2⟩ :=
    OperatorKO7.Meta.Rewriting.overlapAt_eq_some hpair
  have hc1' : c1 = renDifferent := by
    simpa [renDifferent, OperatorKO7.Meta.Rewriting.renameRule, diffRule, tDifferent,
      OperatorKO7.Meta.Rewriting.Term.rename, OperatorKO7.Meta.Rewriting.Term.renameList,
      OperatorKO7.Meta.Rewriting.Subst.apply, OperatorKO7.Meta.Rewriting.Subst.applyList] using hc1
  have hc2' : c2 = renSame := by
    simpa [renSame, OperatorKO7.Meta.Rewriting.renameRule, reflRule, tSame,
      OperatorKO7.Meta.Rewriting.Term.replaceAt, OperatorKO7.Meta.Rewriting.Term.rename,
      OperatorKO7.Meta.Rewriting.Term.renameList, OperatorKO7.Meta.Rewriting.Subst.apply,
      OperatorKO7.Meta.Rewriting.Subst.applyList] using hc2
  subst c1
  subst c2
  exact hpair

private theorem overlapAt_root_diff_diff :
    OperatorKO7.Meta.Rewriting.overlapAt
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) diffRule)
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) diffRule) [] =
      some (renDifferent, renDifferent) := by
  have hsub : OperatorKO7.Meta.Rewriting.Term.subtermAt
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) diffRule).lhs [] =
      some (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) diffRule).lhs := by simp
  have hcommon :
      OperatorKO7.Meta.Rewriting.Subst.apply allSameRenSubst
        (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) diffRule).lhs =
      OperatorKO7.Meta.Rewriting.Subst.apply allSameRenSubst
        (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) diffRule).lhs := by
    simp [allSameRenSubst, renSame, OperatorKO7.Meta.Rewriting.renameRule,
      diffRule, tEqW, x0, x1, OperatorKO7.Meta.Rewriting.Term.rename,
      OperatorKO7.Meta.Rewriting.Term.renameList, OperatorKO7.Meta.Rewriting.Subst.apply,
      OperatorKO7.Meta.Rewriting.Subst.applyList]
  obtain ⟨c1, c2, hpair, _ρ, _h1, _h2⟩ :=
    OperatorKO7.Meta.Rewriting.overlapAt_complete
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) diffRule)
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) diffRule) [] hsub hcommon
  obtain ⟨_sub, μ, _hs, _hu, hc1, hc2⟩ :=
    OperatorKO7.Meta.Rewriting.overlapAt_eq_some hpair
  have hc1' : c1 = renDifferent := by
    simpa [renDifferent, OperatorKO7.Meta.Rewriting.renameRule, diffRule, tDifferent,
      OperatorKO7.Meta.Rewriting.Term.rename, OperatorKO7.Meta.Rewriting.Term.renameList,
      OperatorKO7.Meta.Rewriting.Subst.apply, OperatorKO7.Meta.Rewriting.Subst.applyList] using hc1
  have hc2' : c2 = renDifferent := by
    simpa [renDifferent, OperatorKO7.Meta.Rewriting.renameRule, diffRule, tDifferent,
      OperatorKO7.Meta.Rewriting.Term.replaceAt, OperatorKO7.Meta.Rewriting.Term.rename,
      OperatorKO7.Meta.Rewriting.Term.renameList, OperatorKO7.Meta.Rewriting.Subst.apply,
      OperatorKO7.Meta.Rewriting.Subst.applyList] using hc2
  subst c1
  subst c2
  exact hpair

private theorem overlapPairs_refl_refl :
    OperatorKO7.Meta.Rewriting.overlapPairs
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) reflRule)
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) reflRule) =
      [(renSame, renSame)] := by
  rw [OperatorKO7.Meta.Rewriting.overlapPairs]
  have hpos : OperatorKO7.Meta.Rewriting.nonVarPositions
      (OperatorKO7.Meta.Rewriting.renameRule
        (OperatorKO7.Meta.Rewriting.renL Var) reflRule).lhs = [[]] := by
    simp [OperatorKO7.Meta.Rewriting.nonVarPositions,
      OperatorKO7.Meta.Rewriting.nonVarPositionsList,
      OperatorKO7.Meta.Rewriting.renameRule, reflRule, tEqW, x0,
      OperatorKO7.Meta.Rewriting.Term.rename,
      OperatorKO7.Meta.Rewriting.Term.renameList]
  rw [hpos]
  simp only [List.filterMap_cons, List.filterMap_nil, overlapAt_root_refl_refl]

private theorem overlapPairs_refl_diff :
    OperatorKO7.Meta.Rewriting.overlapPairs
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) reflRule)
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) diffRule) =
      [(renSame, renDifferent)] := by
  rw [OperatorKO7.Meta.Rewriting.overlapPairs]
  have hpos : OperatorKO7.Meta.Rewriting.nonVarPositions
      (OperatorKO7.Meta.Rewriting.renameRule
        (OperatorKO7.Meta.Rewriting.renL Var) reflRule).lhs = [[]] := by
    simp [OperatorKO7.Meta.Rewriting.nonVarPositions,
      OperatorKO7.Meta.Rewriting.nonVarPositionsList,
      OperatorKO7.Meta.Rewriting.renameRule, reflRule, tEqW, x0,
      OperatorKO7.Meta.Rewriting.Term.rename,
      OperatorKO7.Meta.Rewriting.Term.renameList]
  rw [hpos]
  simp only [List.filterMap_cons, List.filterMap_nil, overlapAt_root_refl_diff]

private theorem overlapPairs_diff_refl :
    OperatorKO7.Meta.Rewriting.overlapPairs
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) diffRule)
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) reflRule) =
      [(renDifferent, renSame)] := by
  rw [OperatorKO7.Meta.Rewriting.overlapPairs]
  have hpos : OperatorKO7.Meta.Rewriting.nonVarPositions
      (OperatorKO7.Meta.Rewriting.renameRule
        (OperatorKO7.Meta.Rewriting.renL Var) diffRule).lhs = [[]] := by
    simp [OperatorKO7.Meta.Rewriting.nonVarPositions,
      OperatorKO7.Meta.Rewriting.nonVarPositionsList,
      OperatorKO7.Meta.Rewriting.renameRule, diffRule, tEqW, x0, x1,
      OperatorKO7.Meta.Rewriting.Term.rename,
      OperatorKO7.Meta.Rewriting.Term.renameList]
  rw [hpos]
  simp only [List.filterMap_cons, List.filterMap_nil, overlapAt_root_diff_refl]

private theorem overlapPairs_diff_diff :
    OperatorKO7.Meta.Rewriting.overlapPairs
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renL Var) diffRule)
      (OperatorKO7.Meta.Rewriting.renameRule (OperatorKO7.Meta.Rewriting.renR Var) diffRule) =
      [(renDifferent, renDifferent)] := by
  rw [OperatorKO7.Meta.Rewriting.overlapPairs]
  have hpos : OperatorKO7.Meta.Rewriting.nonVarPositions
      (OperatorKO7.Meta.Rewriting.renameRule
        (OperatorKO7.Meta.Rewriting.renL Var) diffRule).lhs = [[]] := by
    simp [OperatorKO7.Meta.Rewriting.nonVarPositions,
      OperatorKO7.Meta.Rewriting.nonVarPositionsList,
      OperatorKO7.Meta.Rewriting.renameRule, diffRule, tEqW, x0, x1,
      OperatorKO7.Meta.Rewriting.Term.rename,
      OperatorKO7.Meta.Rewriting.Term.renameList]
  rw [hpos]
  simp only [List.filterMap_cons, List.filterMap_nil, overlapAt_root_diff_diff]

/-- Exact generic critical-pair list. The two nontrivial entries are the same
bad pair in opposite ordered-rule orientations. -/
theorem criticalPairs_exact :
    OperatorKO7.Meta.Rewriting.criticalPairs minimalTRS =
      [(renSame, renSame), badCriticalPair,
        badCriticalPairSymm, (renDifferent, renDifferent)] := by
  simp [OperatorKO7.Meta.Rewriting.criticalPairs, minimalTRS,
    overlapPairs_refl_refl, overlapPairs_refl_diff,
    overlapPairs_diff_refl, overlapPairs_diff_diff,
    badCriticalPair, badCriticalPairSymm]

/-- The bad pair is actually emitted by generic critical-pair enumeration. -/
theorem badCriticalPair_mem : badCriticalPair ∈ OperatorKO7.Meta.Rewriting.criticalPairs minimalTRS := by
  rw [criticalPairs_exact]
  simp [badCriticalPair]

/-- Its ordered symmetric counterpart is emitted as well. -/
theorem badCriticalPairSymm_mem :
    badCriticalPairSymm ∈ OperatorKO7.Meta.Rewriting.criticalPairs minimalTRS := by
  rw [criticalPairs_exact]
  simp [badCriticalPairSymm]

/-- Every nontrivial critical pair is one of the two orientations of the unique
same/different obstruction. -/
theorem nontrivial_criticalPair_iff_bad_or_symm
    {q : RenTm × RenTm} (hq : q ∈ OperatorKO7.Meta.Rewriting.criticalPairs minimalTRS) :
    q.1 ≠ q.2 ↔ q = badCriticalPair ∨ q = badCriticalPairSymm := by
  rw [criticalPairs_exact] at hq
  simp at hq
  rcases hq with rfl | rfl | rfl | rfl
  · simp [badCriticalPair, badCriticalPairSymm, renSame, renDifferent]
  · simp [badCriticalPair, renSame, renDifferent]
  · simp [badCriticalPairSymm, renSame, renDifferent]
  · simp [badCriticalPair, badCriticalPairSymm, renSame, renDifferent]

/-- Generic critical-pair enumeration has exactly four ordered overlaps. -/
theorem criticalPairs_length_eq_four :
    (OperatorKO7.Meta.Rewriting.criticalPairs minimalTRS).length = 4 := by
  rw [criticalPairs_exact]
  rfl

/-- The generic Critical Pair Lemma refutes local confluence from the emitted
nonjoinable pair; this is independent of the custom recursive relation proof. -/
theorem deep_generic_not_localConfluent :
    ¬ OperatorKO7.Meta.Rewriting.localConfluent (OperatorKO7.Meta.Rewriting.renameTRS minimalTRS) := by
  intro hlc
  have hall := (OperatorKO7.Meta.Rewriting.critical_pair_lemma minimalTRS).mp hlc
  exact badCriticalPair_not_joinable (hall badCriticalPair badCriticalPair_mem)

/-- Rule count and nonlinearity are both directly visible in the deep artifact. -/
theorem deep_artifact_identity :
    minimalTRS.length = 2 ∧
      reflRule.lhs = .app .eqW [.var 0, .var 0] ∧
      diffRule.lhs = .app .eqW [.var 0, .var 1] :=
  ⟨rfl, rfl, rfl⟩

end DeepEqW

/-! ## Roadmap-stable deep-TRS surface -/

/-- Three-symbol carrier used by the deep first-order reification. -/
abbrev MiniEqWSym := DeepEqW.Sym

/-- Non-left-linear reflexive rule `eqW(x,x) -> same`. -/
abbrev minimalEqW_reflRule := DeepEqW.reflRule

/-- Totalized difference rule `eqW(x,y) -> different`. -/
abbrev minimalEqW_diffRule := DeepEqW.diffRule

/-- Exact two-rule deep first-order TRS. -/
abbrev minimalEqWTRS := DeepEqW.minimalTRS

/-- The deep artifact contains exactly two rules. -/
theorem minimalEqW_rule_count_eq_two : minimalEqWTRS.length = 2 :=
  DeepEqW.minimalTRS_rule_count

/-- The reflexive rule retains the repeated variable literally. -/
theorem minimalEqW_refl_rule_repeats_variable :
    minimalEqW_reflRule.lhs =
      OperatorKO7.Meta.Rewriting.Term.app .eqW
        [OperatorKO7.Meta.Rewriting.Term.var 0,
          OperatorKO7.Meta.Rewriting.Term.var 0] :=
  DeepEqW.reflRule_nonlinear_shape

/-- Exact custom/deep root-step correspondence on encoded terms. -/
theorem minimalEqW_custom_root_iff_generic_rootStep
    {s t : MiniEqWTerm} :
    MiniEqWRootStep s t ↔
      OperatorKO7.Meta.Rewriting.rootStep minimalEqWTRS
        (DeepEqW.encode s) (DeepEqW.encode t) :=
  DeepEqW.customRoot_iff_deepRoot

/-- Compatibility spelling retained for the obligation ledger. -/
theorem minimalEqW_custom_root_iff_generic_root
    {s t : MiniEqWTerm} :
    MiniEqWRootStep s t ↔
      OperatorKO7.Meta.Rewriting.rootStep minimalEqWTRS
        (DeepEqW.encode s) (DeepEqW.encode t) :=
  minimalEqW_custom_root_iff_generic_rootStep

/-- Exact custom/deep unrestricted-context correspondence on encoded terms. -/
theorem minimalEqW_custom_ctx_iff_generic_step
    {s t : MiniEqWTerm} :
    MiniEqWCtxStep s t ↔
      OperatorKO7.Meta.Rewriting.Step minimalEqWTRS
        (DeepEqW.encode s) (DeepEqW.encode t) :=
  DeepEqW.customCtx_iff_deepStep

/-- Complete generic critical-pair list. The only nontrivial pair occurs in the
two ordered orientations `(same,different)` and `(different,same)`. -/
theorem minimalEqW_criticalPairs_exact :
    OperatorKO7.Meta.Rewriting.criticalPairs minimalEqWTRS =
      [(DeepEqW.renSame, DeepEqW.renSame), DeepEqW.badCriticalPair,
        DeepEqW.badCriticalPairSymm,
        (DeepEqW.renDifferent, DeepEqW.renDifferent)] :=
  DeepEqW.criticalPairs_exact

/-- The emitted nontrivial deep critical pair is not joinable. -/
theorem minimalEqW_deep_criticalPair_unjoinable :
    ¬ OperatorKO7.Meta.Rewriting.joinable
      (OperatorKO7.Meta.Rewriting.renameTRS minimalEqWTRS)
      DeepEqW.badCriticalPair.1 DeepEqW.badCriticalPair.2 :=
  DeepEqW.badCriticalPair_not_joinable

/-- The generic first-order contextual relation is not locally confluent. -/
theorem minimalEqW_deep_not_localConfluent :
    ¬ OperatorKO7.Meta.Rewriting.localConfluent
      (OperatorKO7.Meta.Rewriting.renameTRS minimalEqWTRS) :=
  DeepEqW.deep_generic_not_localConfluent

/-- The generic first-order contextual relation is strongly normalizing. -/
theorem minimalEqW_deep_SN :
    WellFounded
      (flip (OperatorKO7.Meta.Rewriting.Step minimalEqWTRS)) :=
  DeepEqW.deep_minimalTRS_SN

/-- The deep symbol carrier attains the three-symbol comparator grammar and the
artifact simultaneously preserves the exact two rules and nonlinear reflexive
left-hand side. -/
theorem miniEqWSym_attains_three :
    Fintype.card MiniEqWSym = 3 ∧
      minimalEqWTRS.length = 2 ∧
      minimalEqW_reflRule.lhs =
        OperatorKO7.Meta.Rewriting.Term.app .eqW
          [OperatorKO7.Meta.Rewriting.Term.var 0,
            OperatorKO7.Meta.Rewriting.Term.var 0] := by
  exact ⟨by decide, minimalEqW_rule_count_eq_two,
    minimalEqW_refl_rule_repeats_variable⟩

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork


