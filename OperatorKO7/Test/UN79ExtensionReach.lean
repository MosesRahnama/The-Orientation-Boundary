import OperatorKO7.Meta.UniqueNormalization.SignatureExtension

#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_theorem68_nontrivial
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_theorem68_nontrivial
#check @OperatorKO7.Meta.UniqueNormalization.UNred_of_theorem68_nontrivial
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_theorem68_nontrivial
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_section7_nontrivial
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_section7_nontrivial
#check @OperatorKO7.Meta.UniqueNormalization.UNred_of_section7_nontrivial
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_section7_nontrivial

/-!
# Reach check: Proposition 22, the signature extension, and the Section 7 summit

Campaign: `Roadmaps\klop\ROADMAP.md`, wave 7.

Every declaration named here is elaborated from the module that owns it, so a
rename or a weakening in `UnificationTransport.lean`, `Proposition22.lean` or
`SignatureExtension.lean` fails this file.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.UN79ExtensionReach

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Ground unification used by the signature extension -/

#check @Ground
#check @Ground.of_arg
#check @Ground.isApp
#check @Ground.subterm
#check @Ground.mapVar_eq
#check @Ground.leftCopy_eq_rightCopy
#check @eq_of_unifClosure_ground
#check @eq_of_ground_omegaUnifiable
#check @not_omegaUnifiable_of_ground_ne
#check @eq_of_ground_infiniteOmegaUnifiable
#check @not_infiniteOmegaUnifiable_of_ground_ne
#check @exists_match_of_ground_omegaUnifiable
#check @exists_match_of_ground_infiniteOmegaUnifiable
#check @subterm_not_omegaUnifiable_of_ground_normalForm
#check @subterm_not_infiniteOmegaUnifiable_of_ground_normalForm

#print axioms OperatorKO7.Meta.UniqueNormalization.Ground
#print axioms OperatorKO7.Meta.UniqueNormalization.Ground.of_arg
#print axioms OperatorKO7.Meta.UniqueNormalization.Ground.isApp
#print axioms OperatorKO7.Meta.UniqueNormalization.Ground.subterm
#print axioms OperatorKO7.Meta.UniqueNormalization.Ground.mapVar_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.Ground.leftCopy_eq_rightCopy
#print axioms OperatorKO7.Meta.UniqueNormalization.eq_of_unifClosure_ground
#print axioms OperatorKO7.Meta.UniqueNormalization.eq_of_ground_omegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.not_omegaUnifiable_of_ground_ne
#print axioms OperatorKO7.Meta.UniqueNormalization.eq_of_ground_infiniteOmegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.not_infiniteOmegaUnifiable_of_ground_ne
#print axioms OperatorKO7.Meta.UniqueNormalization.exists_match_of_ground_omegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.exists_match_of_ground_infiniteOmegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.subterm_not_omegaUnifiable_of_ground_normalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.subterm_not_infiniteOmegaUnifiable_of_ground_normalForm

/-! ## Omega-unifiability transport -/

#check @mapSym_eq_var
#check @mapSym_eq_app
#check @symPush
#check @pushEqv
#check @PushWitness
#check @pushEqv_refl
#check @pushEqv_symm
#check @pushEqv_trans
#check @forall₂_pushEqv_refl
#check @forall₂_pushEqv_symm
#check @forall₂_pushEqv_trans
#check @forall₂_pushEqv_of_forall₂
#check @decomp_pushed
#check @pushWitness_of_rel
#check @pushWitness_refl
#check @pushWitness_symm
#check @pushWitness_trans
#check @pushWitness_of_pushEqv
#check @unifClosure_pushEqv
#check @mapSym_mapVar
#check @omegaUnifiableShared_mapSym
#check @omegaUnifiable_mapSym
#check @infiniteOmegaUnifiable_mapSym
#check @omegaUnifiable_mapSym_iff_of_leftInverse
#check @infiniteOmegaUnifiable_mapSym_iff_of_leftInverse
#check @omegaUnifiable_eraseLabel
#check @infiniteOmegaUnifiable_eraseLabel
#check @Term.mapVar_mapVar
#check @OmegaUnifiable.symm
#check @InfiniteOmegaUnifiable.symm
#check @root_eq_of_omegaUnifiable
#check @root_eq_of_infiniteOmegaUnifiable

#print axioms OperatorKO7.Meta.UniqueNormalization.mapSym_eq_var
#print axioms OperatorKO7.Meta.UniqueNormalization.mapSym_eq_app
#print axioms OperatorKO7.Meta.UniqueNormalization.symPush
#print axioms OperatorKO7.Meta.UniqueNormalization.pushEqv
#print axioms OperatorKO7.Meta.UniqueNormalization.PushWitness
#print axioms OperatorKO7.Meta.UniqueNormalization.pushEqv_refl
#print axioms OperatorKO7.Meta.UniqueNormalization.pushEqv_symm
#print axioms OperatorKO7.Meta.UniqueNormalization.pushEqv_trans
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_pushEqv_refl
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_pushEqv_symm
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_pushEqv_trans
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_pushEqv_of_forall₂
#print axioms OperatorKO7.Meta.UniqueNormalization.decomp_pushed
#print axioms OperatorKO7.Meta.UniqueNormalization.pushWitness_of_rel
#print axioms OperatorKO7.Meta.UniqueNormalization.pushWitness_refl
#print axioms OperatorKO7.Meta.UniqueNormalization.pushWitness_symm
#print axioms OperatorKO7.Meta.UniqueNormalization.pushWitness_trans
#print axioms OperatorKO7.Meta.UniqueNormalization.pushWitness_of_pushEqv
#print axioms OperatorKO7.Meta.UniqueNormalization.unifClosure_pushEqv
#print axioms OperatorKO7.Meta.UniqueNormalization.mapSym_mapVar
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiableShared_mapSym
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiable_mapSym
#print axioms OperatorKO7.Meta.UniqueNormalization.infiniteOmegaUnifiable_mapSym
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiable_mapSym_iff_of_leftInverse
#print axioms OperatorKO7.Meta.UniqueNormalization.infiniteOmegaUnifiable_mapSym_iff_of_leftInverse
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiable_eraseLabel
#print axioms OperatorKO7.Meta.UniqueNormalization.infiniteOmegaUnifiable_eraseLabel
#print axioms OperatorKO7.Meta.UniqueNormalization.Term.mapVar_mapVar
#print axioms OperatorKO7.Meta.UniqueNormalization.OmegaUnifiable.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.InfiniteOmegaUnifiable.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.root_eq_of_omegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.root_eq_of_infiniteOmegaUnifiable

example {tau : Type u} (f : sigma → tau) {s t : Term sigma nu} (h : OmegaUnifiable s t) :
    OmegaUnifiable (Term.mapSym f s) (Term.mapSym f t) :=
  omegaUnifiable_mapSym f h

example {tau : Type u} (f : sigma → tau) (g : tau → sigma)
    (hgf : Function.LeftInverse g f) {s t : Term sigma nu} :
    OmegaUnifiable (Term.mapSym f s) (Term.mapSym f t) ↔ OmegaUnifiable s t :=
  omegaUnifiable_mapSym_iff_of_leftInverse f g hgf

example {s t : Term sigma nu} (h : OmegaUnifiable s t) : OmegaUnifiable t s := h.symm

/-! ## Proposition 22 -/

#check @VarOccurs.mapSym
#check @VarOccurs.of_mapSym
#check @varOccurs_destructorPattern
#check @varOccurs_of_destructorPattern
#check @map_eq_map_pointwise
#check @agree_of_apply_eq_occurs
#check @determinedBy_of_occurs_subset
#check @size_le_size_apply
#check @sizeList_le_sizeList_map
#check @growAt
#check @growAt_self
#check @growAt_of_ne
#check @size_lt_size_apply_growAt
#check @occurs_of_determinedBy
#check @Rule.lhs_app
#check @transRule_occurs
#check @transRule_rhsDetermined
#check @subterm_of_mem_appNodes
#check @properSubterm_of_mem_properAppNodes
#check @exists_rule_of_mem_patternNodes
#check @ConOnly.subterm
#check @omegaUnifiable_of_destructorPattern
#check @prop22_root_overlaps
#check @prop22_rule_rule
#check @prop22_rule_pattern
#check @listSubst
#check @map_listSubst_range
#check @freshVars
#check @apply_freshVars
#check @varOccurs_app_of_app
#check @length_eq_of_omegaUnifiable
#check @prop22_pattern_pattern
#check @prop22
#check @consistencyInvariant_constructorTranslation

#print axioms OperatorKO7.Meta.UniqueNormalization.VarOccurs.mapSym
#print axioms OperatorKO7.Meta.UniqueNormalization.VarOccurs.of_mapSym
#print axioms OperatorKO7.Meta.UniqueNormalization.varOccurs_destructorPattern
#print axioms OperatorKO7.Meta.UniqueNormalization.varOccurs_of_destructorPattern
#print axioms OperatorKO7.Meta.UniqueNormalization.map_eq_map_pointwise
#print axioms OperatorKO7.Meta.UniqueNormalization.agree_of_apply_eq_occurs
#print axioms OperatorKO7.Meta.UniqueNormalization.determinedBy_of_occurs_subset
#print axioms OperatorKO7.Meta.UniqueNormalization.size_le_size_apply
#print axioms OperatorKO7.Meta.UniqueNormalization.sizeList_le_sizeList_map
#print axioms OperatorKO7.Meta.UniqueNormalization.growAt
#print axioms OperatorKO7.Meta.UniqueNormalization.growAt_self
#print axioms OperatorKO7.Meta.UniqueNormalization.growAt_of_ne
#print axioms OperatorKO7.Meta.UniqueNormalization.size_lt_size_apply_growAt
#print axioms OperatorKO7.Meta.UniqueNormalization.occurs_of_determinedBy
#print axioms OperatorKO7.Meta.UniqueNormalization.Rule.lhs_app
#print axioms OperatorKO7.Meta.UniqueNormalization.transRule_occurs
#print axioms OperatorKO7.Meta.UniqueNormalization.transRule_rhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.subterm_of_mem_appNodes
#print axioms OperatorKO7.Meta.UniqueNormalization.properSubterm_of_mem_properAppNodes
#print axioms OperatorKO7.Meta.UniqueNormalization.exists_rule_of_mem_patternNodes
#print axioms OperatorKO7.Meta.UniqueNormalization.ConOnly.subterm
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiable_of_destructorPattern
#print axioms OperatorKO7.Meta.UniqueNormalization.prop22_root_overlaps
#print axioms OperatorKO7.Meta.UniqueNormalization.prop22_rule_rule
#print axioms OperatorKO7.Meta.UniqueNormalization.prop22_rule_pattern
#print axioms OperatorKO7.Meta.UniqueNormalization.listSubst
#print axioms OperatorKO7.Meta.UniqueNormalization.map_listSubst_range
#print axioms OperatorKO7.Meta.UniqueNormalization.freshVars
#print axioms OperatorKO7.Meta.UniqueNormalization.apply_freshVars
#print axioms OperatorKO7.Meta.UniqueNormalization.varOccurs_app_of_app
#print axioms OperatorKO7.Meta.UniqueNormalization.length_eq_of_omegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.prop22_pattern_pattern
#print axioms OperatorKO7.Meta.UniqueNormalization.prop22
#print axioms OperatorKO7.Meta.UniqueNormalization.consistencyInvariant_constructorTranslation

example [Infinite nu] {R : TRS sigma nu} (hno : NonOmegaOverlapping R)
    (hvar : TRS.RhsDetermined R) :
    StronglyAlmostNonOmegaOverlapping (constructorTranslation R) :=
  prop22 hno hvar

example [Infinite nu] {R : TRS sigma nu} (hno : NonOmegaOverlapping R)
    (hvar : TRS.RhsDetermined R) :
    ConsistencyInvariant (constructorTranslation R) (Down (constructorTranslation R)) :=
  consistencyInvariant_constructorTranslation hno hvar

/-! ## The signature extension of Theorem 69 -/

#check @Rule.mapSym
#check @Step.mapSym
#check @conv.mapSym
#check @conv.subst
#check @ExtSym
#check @frozenVar
#check @freshSym
#check @liftTerm
#check @freezeSubst
#check @freeze
#check @freeze_var
#check @freeze_app
#check @VarOccurs.of_apply
#check @ground_freeze
#check @unfreeze
#check @unfreezeList
#check @unfreezeList_eq_map
#check @unfreeze_freeze
#check @freeze_injective
#check @unfreeze_apply_lift
#check @extRuleFreshL
#check @extRuleFreshR
#check @extSystem
#check @mem_extSystem
#check @lifted_mem_extSystem
#check @not_step_frozenVar
#check @normalForm_freeze
#check @step_extFreshL
#check @step_extFreshR
#check @conv_freeze
#check @conv_var_var_ext
#check @Subterm.mapSym
#check @subterm_of_mapSym
#check @subterm_of_freeze
#check @subterm_freeze_root
#check @freeze_injective'
#check @unliftSym
#check @mapSym_unlift_mapSym
#check @omegaUnifiable_head
#check @subterm_freshLhs
#check @not_omegaUnifiable_freeze_lifted
#check @not_omegaUnifiable_freeze_fresh
#check @nonOmegaOverlapping_ext
#check @rhsDetermined_lift
#check @rhsDetermined_ext
#check @UNconv_of_theorem68
#check @UNred_of_theorem68
#check @consistent_of_down_trans
#check @UNconv_of_section7
#check @UNred_of_section7

#print axioms OperatorKO7.Meta.UniqueNormalization.Rule.mapSym
#print axioms OperatorKO7.Meta.UniqueNormalization.Step.mapSym
#print axioms OperatorKO7.Meta.UniqueNormalization.conv.mapSym
#print axioms OperatorKO7.Meta.UniqueNormalization.conv.subst
#print axioms OperatorKO7.Meta.UniqueNormalization.ExtSym
#print axioms OperatorKO7.Meta.UniqueNormalization.frozenVar
#print axioms OperatorKO7.Meta.UniqueNormalization.freshSym
#print axioms OperatorKO7.Meta.UniqueNormalization.liftTerm
#print axioms OperatorKO7.Meta.UniqueNormalization.freezeSubst
#print axioms OperatorKO7.Meta.UniqueNormalization.freeze
#print axioms OperatorKO7.Meta.UniqueNormalization.freeze_var
#print axioms OperatorKO7.Meta.UniqueNormalization.freeze_app
#print axioms OperatorKO7.Meta.UniqueNormalization.VarOccurs.of_apply
#print axioms OperatorKO7.Meta.UniqueNormalization.ground_freeze
#print axioms OperatorKO7.Meta.UniqueNormalization.unfreeze
#print axioms OperatorKO7.Meta.UniqueNormalization.unfreezeList
#print axioms OperatorKO7.Meta.UniqueNormalization.unfreezeList_eq_map
#print axioms OperatorKO7.Meta.UniqueNormalization.unfreeze_freeze
#print axioms OperatorKO7.Meta.UniqueNormalization.freeze_injective
#print axioms OperatorKO7.Meta.UniqueNormalization.unfreeze_apply_lift
#print axioms OperatorKO7.Meta.UniqueNormalization.extRuleFreshL
#print axioms OperatorKO7.Meta.UniqueNormalization.extRuleFreshR
#print axioms OperatorKO7.Meta.UniqueNormalization.extSystem
#print axioms OperatorKO7.Meta.UniqueNormalization.mem_extSystem
#print axioms OperatorKO7.Meta.UniqueNormalization.lifted_mem_extSystem
#print axioms OperatorKO7.Meta.UniqueNormalization.not_step_frozenVar
#print axioms OperatorKO7.Meta.UniqueNormalization.normalForm_freeze
#print axioms OperatorKO7.Meta.UniqueNormalization.step_extFreshL
#print axioms OperatorKO7.Meta.UniqueNormalization.step_extFreshR
#print axioms OperatorKO7.Meta.UniqueNormalization.conv_freeze
#print axioms OperatorKO7.Meta.UniqueNormalization.conv_var_var_ext
#print axioms OperatorKO7.Meta.UniqueNormalization.Subterm.mapSym
#print axioms OperatorKO7.Meta.UniqueNormalization.subterm_of_mapSym
#print axioms OperatorKO7.Meta.UniqueNormalization.subterm_of_freeze
#print axioms OperatorKO7.Meta.UniqueNormalization.subterm_freeze_root
#print axioms OperatorKO7.Meta.UniqueNormalization.freeze_injective'
#print axioms OperatorKO7.Meta.UniqueNormalization.unliftSym
#print axioms OperatorKO7.Meta.UniqueNormalization.mapSym_unlift_mapSym
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiable_head
#print axioms OperatorKO7.Meta.UniqueNormalization.subterm_freshLhs
#print axioms OperatorKO7.Meta.UniqueNormalization.not_omegaUnifiable_freeze_lifted
#print axioms OperatorKO7.Meta.UniqueNormalization.not_omegaUnifiable_freeze_fresh
#print axioms OperatorKO7.Meta.UniqueNormalization.nonOmegaOverlapping_ext
#print axioms OperatorKO7.Meta.UniqueNormalization.rhsDetermined_lift
#print axioms OperatorKO7.Meta.UniqueNormalization.rhsDetermined_ext
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_theorem68
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_theorem68
#print axioms OperatorKO7.Meta.UniqueNormalization.consistent_of_down_trans
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_section7
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_section7

example {R : TRS sigma nu} {t u : Term sigma nu} {x y : nu} (s : Term sigma nu)
    (hs : NormalForm R s) : NormalForm (extSystem R t u x y) (freeze s) :=
  normalForm_freeze s hs

example {R : TRS sigma nu} (hno : NonOmegaOverlapping R) {t u : Term sigma nu}
    (ht : NormalForm R t) (hu : NormalForm R u) (hne : t ≠ u) (x y : nu) :
    NonOmegaOverlapping (extSystem R t u x y) :=
  nonOmegaOverlapping_ext hno ht hu hne x y

example {R : TRS sigma nu} (hvar : TRS.RhsDetermined R) (t u : Term sigma nu) (x y : nu) :
    TRS.RhsDetermined (extSystem R t u x y) :=
  rhsDetermined_ext hvar t u x y

example {R : TRS sigma nu} {t u : Term sigma nu} (x y : nu) (h : conv R t u) :
    conv (extSystem R t u x y) (.var x) (.var y) :=
  conv_var_var_ext x y h

/-! ## The summit -/

example [Infinite nu] {R : TRS sigma nu}
    (htrans : ∀ S : TRS (ExtSym sigma nu) nu, NonOmegaOverlapping S → TRS.RhsDetermined S →
      ∀ p q r : Term (ExtSym sigma nu ⊕ ExtSym sigma nu) nu,
        Down (constructorTranslation S) p q → Down (constructorTranslation S) q r →
          Down (constructorTranslation S) p r)
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) : UNconv R ∧ UNred R :=
  ⟨UNconv_of_section7 htrans hno hvar, UNred_of_section7 htrans hno hvar⟩

end OperatorKO7.Test.UN79ExtensionReach
