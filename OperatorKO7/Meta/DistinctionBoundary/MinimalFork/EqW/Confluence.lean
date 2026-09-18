import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.Termination

/-!
# Root confluence boundary of the minimal EqW system

The raw root relation terminates but has a nonjoinable diagonal peak. The guarded
root relation is deterministic and therefore globally confluent. The theorem
`miniEqW_raw_nontrivial_peak_iff_diagonal` proves that the diagonal overlap is the
only source shape with two distinct one-step raw verdicts.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- Raw `same` is a root normal form. -/
theorem miniEqW_same_rawRoot_normal : NormalForm MiniEqWRootStep .same := by
  intro y h
  cases h

/-- Raw `different` is a root normal form. -/
theorem miniEqW_different_rawRoot_normal : NormalForm MiniEqWRootStep .different := by
  intro y h
  cases h

/-- Roadmap-stable equal-verdict root normal-form name. -/
theorem minimalEqW_same_root_normal : NormalForm MiniEqWRootStep .same :=
  miniEqW_same_rawRoot_normal

/-- Roadmap-stable different-verdict root normal-form name. -/
theorem minimalEqW_different_root_normal : NormalForm MiniEqWRootStep .different :=
  miniEqW_different_rawRoot_normal

/-- The two raw verdicts are unjoinable. -/
theorem miniEqW_raw_verdicts_unjoinable :
    ¬ Joinable MiniEqWRootStep .same .different := by
  rintro ⟨z, hs, hd⟩
  have hzs : z = .same := eq_of_normalForm_reach miniEqW_same_rawRoot_normal hs
  have hzd : z = .different :=
    eq_of_normalForm_reach miniEqW_different_rawRoot_normal hd
  exact miniEqW_same_ne_different (hzs.symm.trans hzd)

/-- Roadmap-stable verdict-unjoinability name. -/
theorem minimalEqW_verdicts_unjoinable :
    ¬ Joinable MiniEqWRootStep .same .different :=
  miniEqW_raw_verdicts_unjoinable

/-- Every raw diagonal query has the nonjoinable two-verdict peak. -/
theorem minimalEqW_diagonal_not_confluent (a : MiniEqWTerm) :
    ¬ ConfluentAt MiniEqWRootStep (.eqW a a) := by
  intro hconf
  exact miniEqW_raw_verdicts_unjoinable
    (hconf .same .different
      (reach_step (MiniEqWRootStep.refl a))
      (reach_step (MiniEqWRootStep.diff a a)))

/-- The smallest closed diagonal is terminating but nonconfluent. -/
theorem minimalEqW_closed_diagonal_not_confluent :
    ¬ ConfluentAt MiniEqWRootStep miniEqWClosedDiagonal :=
  minimalEqW_diagonal_not_confluent .same

/-- The guarded root relation is functional: a source has at most one target. -/
theorem miniEqW_guardedRoot_functional
    {s l r : MiniEqWTerm}
    (hl : MiniEqWGuardedRootStep s l)
    (hr : MiniEqWGuardedRootStep s r) : l = r := by
  cases hl with
  | refl x =>
      cases hr with
      | refl _ => rfl
      | diff _ _ hne => exact False.elim (hne rfl)
  | diff x y hxy =>
      cases hr with
      | refl _ => exact False.elim (hxy rfl)
      | diff _ _ _ => rfl

/-- Finite paths of a functional relation from the same source are comparable by
reachability. -/
theorem functional_steps_comparable
    {T : Type} {R : T → T → Prop}
    (hfun : ∀ {s l r}, R s l → R s r → l = r)
    {m n : Nat} {s x y : T}
    (hx : Steps R m s x) (hy : Steps R n s y) :
    Reach R x y ∨ Reach R y x := by
  induction hx generalizing n y with
  | zero =>
      exact Or.inl ⟨n, hy⟩
  | @succ m s a x hsa hax ih =>
      cases hy with
      | zero =>
          exact Or.inr ⟨m + 1, Steps.succ hsa hax⟩
      | @succ n s b y hsb hby =>
          have hab : a = b := hfun hsa hsb
          subst b
          exact ih hby

/-- Every functional relation is confluent on every finite reachability cone. -/
theorem confluentAt_of_functional
    {T : Type} {R : T → T → Prop}
    (hfun : ∀ {s l r}, R s l → R s r → l = r)
    (source : T) : ConfluentAt R source := by
  intro x y hx hy
  rcases hx with ⟨m, hmx⟩
  rcases hy with ⟨n, hny⟩
  rcases functional_steps_comparable (R := R) hfun hmx hny with hxy | hyx
  · exact ⟨y, hxy, reach_refl y⟩
  · exact ⟨x, reach_refl x, hyx⟩

/-- Guarding the difference rule restores root confluence globally. -/
theorem guarded_root_confluent (source : MiniEqWTerm) :
    ConfluentAt MiniEqWGuardedRootStep source :=
  confluentAt_of_functional (R := MiniEqWGuardedRootStep)
    miniEqW_guardedRoot_functional source

/-- A raw root source has two *distinct* one-step targets iff it is diagonal. -/
theorem miniEqW_raw_nontrivial_peak_iff_diagonal (s : MiniEqWTerm) :
    (∃ l r, MiniEqWRootStep s l ∧ MiniEqWRootStep s r ∧ l ≠ r) ↔
      ∃ a, s = .eqW a a := by
  constructor
  · rintro ⟨l, r, hl, hr, hne⟩
    rcases (miniEqW_rawRoot_iff.mp hl) with
      ⟨a, hsa, hls⟩ | ⟨a, b, hsab, hld⟩
    · rcases (miniEqW_rawRoot_iff.mp hr) with
        ⟨c, hsc, hrs⟩ | ⟨c, d, hscd, hrd⟩
      · exact False.elim (hne (hls.trans hrs.symm))
      · exact ⟨a, hsa⟩
    · rcases (miniEqW_rawRoot_iff.mp hr) with
        ⟨c, hsc, hrs⟩ | ⟨c, d, hscd, hrd⟩
      · exact ⟨c, hsc⟩
      · exact False.elim (hne (hld.trans hrd.symm))
  · rintro ⟨a, rfl⟩
    exact ⟨.same, .different,
      MiniEqWRootStep.refl a, MiniEqWRootStep.diff a a,
      miniEqW_same_ne_different⟩

/-- One-step local-join predicate used by the root-only comparison results. -/
def RootLocalJoinAt (R : MiniEqWTerm → MiniEqWTerm → Prop)
    (source : MiniEqWTerm) : Prop :=
  ∀ {l r}, R source l → R source r → Joinable R l r

/-- Guarded root is locally confluent at every source. -/
theorem guarded_root_localConfluent (source : MiniEqWTerm) :
    RootLocalJoinAt MiniEqWGuardedRootStep source := by
  intro l r hl hr
  have hEq : l = r := miniEqW_guardedRoot_functional hl hr
  subst r
  exact ⟨l, reach_refl l, reach_refl l⟩

/-- Raw root local-join failure occurs exactly on a diagonal query. -/
theorem minimalEqW_bad_root_iff_diagonal (s : MiniEqWTerm) :
    ¬ RootLocalJoinAt MiniEqWRootStep s ↔ ∃ a, s = .eqW a a := by
  constructor
  · intro hbad
    by_contra hdiag
    apply hbad
    intro l r hl hr
    have hlr : l = r := by
      by_contra hne
      exact hdiag ((miniEqW_raw_nontrivial_peak_iff_diagonal s).mp
        ⟨l, r, hl, hr, hne⟩)
    subst r
    exact ⟨l, reach_refl l, reach_refl l⟩
  · rintro ⟨a, rfl⟩ hlocal
    exact miniEqW_raw_verdicts_unjoinable
      (hlocal (MiniEqWRootStep.refl a) (MiniEqWRootStep.diff a a))

/-- Every non-diagonal source of the raw root relation is functional at that source. -/
theorem miniEqW_raw_functional_off_diagonal
    {s l r : MiniEqWTerm}
    (hdiag : ¬ ∃ a, s = .eqW a a)
    (hl : MiniEqWRootStep s l) (hr : MiniEqWRootStep s r) : l = r := by
  by_contra hne
  exact hdiag ((miniEqW_raw_nontrivial_peak_iff_diagonal s).mp
    ⟨l, r, hl, hr, hne⟩)

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
