import OperatorKO7.Meta.SafeStep.GenericDiagonalFork

set_option autoImplicit false

namespace OperatorKO7.Meta.SafeStep.EqualityReflectionInstance

open OperatorKO7.Meta.SafeStep.GenericDiagonalFork

inductive TyTerm : Type
  | reflVerdict : TyTerm
  | impossibleDiseqVerdict : TyTerm
  | base0 : TyTerm
  | base1 : TyTerm
  | idQuery : TyTerm -> TyTerm -> TyTerm
  deriving DecidableEq

inductive EqReflectionRel : TyTerm -> TyTerm -> Prop
  | idRefl (x : TyTerm) :
      EqReflectionRel (TyTerm.idQuery x x) TyTerm.reflVerdict
  | reflectedDiseq (x y : TyTerm) :
      EqReflectionRel (TyTerm.idQuery x y) TyTerm.impossibleDiseqVerdict

inductive EqReflectionStar : TyTerm -> TyTerm -> Prop
  | refl (t : TyTerm) : EqReflectionStar t t
  | tail {x y z : TyTerm} :
      EqReflectionRel x y -> EqReflectionStar y z -> EqReflectionStar x z

def EqReflectionNF (t : TyTerm) : Prop :=
  Not (exists u, EqReflectionRel t u)

theorem eqReflectionStar_of_rel {x y : TyTerm}
    (h : EqReflectionRel x y) : EqReflectionStar x y :=
  EqReflectionStar.tail h (EqReflectionStar.refl y)

theorem eqReflection_nf_reflVerdict :
    EqReflectionNF TyTerm.reflVerdict := by
  rintro ⟨u, h⟩
  cases h

theorem eqReflection_nf_impossibleDiseqVerdict :
    EqReflectionNF TyTerm.impossibleDiseqVerdict := by
  rintro ⟨u, h⟩
  cases h

theorem eqReflection_nf_no_forward {x y : TyTerm}
    (hnf : EqReflectionNF x) (h : EqReflectionStar x y) : x = y := by
  cases h with
  | refl _ => rfl
  | tail hxy _ => exact False.elim (hnf ⟨_, hxy⟩)

def equalityReflectionFork : DiagonalForkSchema TyTerm where
  R := EqReflectionRel
  RStar := EqReflectionStar
  E := TyTerm.idQuery
  Z := TyTerm.reflVerdict
  D := fun _ _ => TyTerm.impossibleDiseqVerdict
  refl_rule := EqReflectionRel.idRefl
  diff_rule := EqReflectionRel.reflectedDiseq
  rstar_refl := EqReflectionStar.refl
  rstar_single := eqReflectionStar_of_rel

theorem equalityReflection_verdicts_not_join :
    Not (DiagonalVerdictsJoin equalityReflectionFork TyTerm.base0) := by
  rintro ⟨d, hleft, hright⟩
  have hdl : d = TyTerm.reflVerdict :=
    (eqReflection_nf_no_forward eqReflection_nf_reflVerdict hleft).symm
  have hdr : d = TyTerm.impossibleDiseqVerdict :=
    (eqReflection_nf_no_forward eqReflection_nf_impossibleDiseqVerdict hright).symm
  have hbad : (TyTerm.reflVerdict : TyTerm) = TyTerm.impossibleDiseqVerdict :=
    hdl.symm.trans hdr
  cases hbad

/-- A third independent finite diagonal-fork genus instance, modeled on equality reflection. -/
theorem equalityReflection_localConfluence_fails :
    Not (LocalJoinAt equalityReflectionFork
      (equalityReflectionFork.E TyTerm.base0 TyTerm.base0)) :=
  localConfluence_fails_at_diagonal equalityReflectionFork TyTerm.base0
    equalityReflection_verdicts_not_join

#print axioms equalityReflection_localConfluence_fails

end OperatorKO7.Meta.SafeStep.EqualityReflectionInstance
