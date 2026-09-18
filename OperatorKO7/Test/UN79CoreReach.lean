import OperatorKO7.Meta.UniqueNormalization.Lemma52

#check @OperatorKO7.Meta.UniqueNormalization.PGraph.extend_one_exact
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.extend_one_exact

#check @OperatorKO7.Meta.UniqueNormalization.terminating_extendPar_of_no_return
#print axioms OperatorKO7.Meta.UniqueNormalization.terminating_extendPar_of_no_return

/-!
# Reach check: the consistency core of the Klop campaign

Campaign: `Roadmaps\klop\ROADMAP.md`, wave 5 and wave 6.

Every declaration named here is elaborated from the module that owns it, so a
rename or a weakening in `ConsistencyCore.lean`, `DownRelation.lean`,
`Lemma36.lean`, `Theorem37.lean`, `Summit.lean`, `Coalgebra.lean`, `Forest.lean`,
`ProofGraph.lean`, or `Lemma52.lean` fails this file. The import is deliberately
`Lemma52`, the top of the current Section-7 carrier stack, so the gate cannot pass
against stale declarations from only the earlier summit reduction.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.UN79CoreReach

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## The tilde algebra and `CT` -/

#check @forall₂_of_pointwise
#check @pointwise_of_forall₂
#check @forall₂_mono
#check @forall₂_flip
#check @OperatorKO7.Meta.UniqueNormalization.forall₂_swap
#check @forall₂_self
#check @CRel
#check @tildeOn
#check @tildeAll
#check @hatRel
#check @barRel
#check @tildeOn_mono
#check @tildeOn_mono_pred
#check @tildeAll_of_hatRel
#check @tildeAll_of_barRel
#check @hatRel_or_barRel_of_tildeAll
#check @tildeOn_flip
#check @SigmaClosed
#check @CT
#check @CT.base
#check @CT.least
#check @CT.sigmaClosed
#check @CT.app
#check @CT.mono
#check @constructorCompatible_flip
#check @constructorCompatible_iSup
#check @ConOnly
#check @ConOnly.var
#check @ConOnly.app
#check @ConOnly.app_inv
#check @ConOnly.constructorLabel
#check @lemma33
#check @lemma34
#check @cor35
#check @cor35_of_barRel

#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_of_pointwise
#print axioms OperatorKO7.Meta.UniqueNormalization.pointwise_of_forall₂
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_flip
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_swap
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_self
#print axioms OperatorKO7.Meta.UniqueNormalization.CRel
#print axioms OperatorKO7.Meta.UniqueNormalization.tildeOn
#print axioms OperatorKO7.Meta.UniqueNormalization.tildeAll
#print axioms OperatorKO7.Meta.UniqueNormalization.hatRel
#print axioms OperatorKO7.Meta.UniqueNormalization.barRel
#print axioms OperatorKO7.Meta.UniqueNormalization.tildeOn_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.tildeOn_mono_pred
#print axioms OperatorKO7.Meta.UniqueNormalization.tildeAll_of_hatRel
#print axioms OperatorKO7.Meta.UniqueNormalization.tildeAll_of_barRel
#print axioms OperatorKO7.Meta.UniqueNormalization.hatRel_or_barRel_of_tildeAll
#print axioms OperatorKO7.Meta.UniqueNormalization.tildeOn_flip
#print axioms OperatorKO7.Meta.UniqueNormalization.SigmaClosed
#print axioms OperatorKO7.Meta.UniqueNormalization.CT
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.base
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.least
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.sigmaClosed
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.app
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorCompatible_flip
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorCompatible_iSup
#print axioms OperatorKO7.Meta.UniqueNormalization.ConOnly
#print axioms OperatorKO7.Meta.UniqueNormalization.ConOnly.var
#print axioms OperatorKO7.Meta.UniqueNormalization.ConOnly.app
#print axioms OperatorKO7.Meta.UniqueNormalization.ConOnly.app_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.ConOnly.constructorLabel
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma33
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma34
#print axioms OperatorKO7.Meta.UniqueNormalization.cor35
#print axioms OperatorKO7.Meta.UniqueNormalization.cor35_of_barRel

example (E : CRel sigma nu) : SigmaClosed (CT E) := CT.sigmaClosed

example (E : CRel sigma nu) (a b : Term (sigma ⊕ sigma) nu) (h : E a b) : CT E a b :=
  CT.base h

example (E : CRel sigma nu) {t u : Term (sigma ⊕ sigma) nu} (h : hatRel E t u) :
    tildeAll E t u :=
  tildeAll_of_hatRel h

/-! ## Corollary 35, the step the campaign audit had reported as blocked -/

example {S : CRel sigma nu} (hS : ConstructorCompatible S)
    {F : sigma} {ps : List (Term (sigma ⊕ sigma) nu)}
    (hps : ∀ p ∈ ps, ConOnly p)
    {r : Term (sigma ⊕ sigma) nu}
    (hvar : ∀ x : nu, VarOccurs x r → VarOccurs x (.app (Sum.inr F) ps))
    {a b : Subst (sigma ⊕ sigma) nu}
    (hbar : List.Forall₂ S (ps.map (Subst.apply a)) (ps.map (Subst.apply b))) :
    CT S (Subst.apply a r) (Subst.apply b r) :=
  cor35 hS hps hvar hbar

/-! ## The relation `⇓` -/

example (R : TRS (sigma ⊕ sigma) nu) : SigmaClosed (Down R) := Down.sigmaClosed R

example {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R) :
    ConstructorCompatible (Down R) :=
  Down.constructorCompatible hR

example {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R) {x y : nu}
    (h : Down R (.var x) (.var y)) : x = y :=
  Down.consistent hR h

example {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : Step R a b) : Down R a b :=
  Down.of_step h

#check @ConstructorRules
#check @not_conTopped_destructor
#check @rootStep_source_destructor
#check @DownStep
#check @DownStep_mono
#check @Down
#check @Down.least
#check @Down.closed
#check @Down.refl
#check @Down.symm
#check @Down.rootComp
#check @Down.barComp
#check @Down.hatCl
#check @Down.barCl
#check @Down.tildeCl
#check @Down.induction
#check @Down.sigmaClosed
#check @forall₂_append_middle
#check @Down.of_rootStep
#check @Down.of_step
#check @Down.constructorCompatible
#check @Down.consistent

#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorRules
#print axioms OperatorKO7.Meta.UniqueNormalization.not_conTopped_destructor
#print axioms OperatorKO7.Meta.UniqueNormalization.rootStep_source_destructor
#print axioms OperatorKO7.Meta.UniqueNormalization.DownStep
#print axioms OperatorKO7.Meta.UniqueNormalization.DownStep_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.Down
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.least
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.closed
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.rootComp
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.barComp
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.hatCl
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.barCl
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.tildeCl
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.induction
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.sigmaClosed
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_append_middle
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.of_rootStep
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.of_step
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.constructorCompatible
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.consistent

/-! ## Lemma 36, Theorem 37, Corollary 45 -/

#check @valuate
#check @valuateList
#check @valuate_var
#check @valuate_app
#check @valuateList_nil
#check @valuateList_cons
#check @valuateList_eq_map
#check @valuate_mapVar
#check @forall₂_of_map₂
#check @forall₂_map₂_of
#check @forall₂_and_mem
#check @not_conOnly_destructor
#check @ConOnly.mapVar
#check @LinkRel
#check @LinkRel.refl
#check @LinkRel.symm
#check @LinkRel.trans
#check @Cert36
#check @lemma36

#print axioms OperatorKO7.Meta.UniqueNormalization.valuate
#print axioms OperatorKO7.Meta.UniqueNormalization.valuateList
#print axioms OperatorKO7.Meta.UniqueNormalization.valuate_var
#print axioms OperatorKO7.Meta.UniqueNormalization.valuate_app
#print axioms OperatorKO7.Meta.UniqueNormalization.valuateList_nil
#print axioms OperatorKO7.Meta.UniqueNormalization.valuateList_cons
#print axioms OperatorKO7.Meta.UniqueNormalization.valuateList_eq_map
#print axioms OperatorKO7.Meta.UniqueNormalization.valuate_mapVar
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_of_map₂
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_map₂_of
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_and_mem
#print axioms OperatorKO7.Meta.UniqueNormalization.not_conOnly_destructor
#print axioms OperatorKO7.Meta.UniqueNormalization.ConOnly.mapVar
#print axioms OperatorKO7.Meta.UniqueNormalization.LinkRel
#print axioms OperatorKO7.Meta.UniqueNormalization.LinkRel.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.LinkRel.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.LinkRel.trans
#print axioms OperatorKO7.Meta.UniqueNormalization.Cert36
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma36

example {S : CRel sigma nu}
    (hsymm : ∀ x y : Term (sigma ⊕ sigma) nu, S x y → S y x)
    (htrans : ∀ x y z : Term (sigma ⊕ sigma) nu, S x y → S y z → S x z)
    (hCC : ConstructorCompatible S)
    {F : sigma} {ps qs : List (Term (sigma ⊕ sigma) nu)}
    (hps : ∀ p ∈ ps, ConOnly p) (hqs : ∀ q ∈ qs, ConOnly q)
    {a b : Subst (sigma ⊕ sigma) nu}
    (hall : List.Forall₂ S (ps.map (Subst.apply a)) (qs.map (Subst.apply b))) :
    OmegaUnifiable (Term.app (Sum.inr F) ps) (Term.app (Sum.inr F) qs) :=
  lemma36 hsymm htrans hCC hps hqs hall

example {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R) :
    ConsistencyInvariant R (Down R) :=
  cor45 hR hstrong

#check @StronglyAlmostNonOmegaOverlapping
#check @ConsistencyInvariant
#check @ConOnly.of_apply
#check @thm37
#check @cor45

#print axioms OperatorKO7.Meta.UniqueNormalization.StronglyAlmostNonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.ConsistencyInvariant
#print axioms OperatorKO7.Meta.UniqueNormalization.ConOnly.of_apply
#print axioms OperatorKO7.Meta.UniqueNormalization.thm37
#print axioms OperatorKO7.Meta.UniqueNormalization.cor45

/-! ## Section 7 finite-coalgebra and proof-graph carrier -/

#check @Coalgebra
#check @Coalgebra.arg
#check @DownStepOn
#check @DownStepOn_mono
#check @DownOn
#check @DownOn.least
#check @DownOn.closed
#check @DownOn.induction
#check @DownOn.mem
#check @DownOn.refl
#check @DownOn.symm
#check @DownOn.rootComp
#check @DownOn.barComp
#check @DownOn.hatCl
#check @DownOn.barCl
#check @DownOn.tildeCl
#check @DownOn.toDown
#check @forall₂_self_of
#check @forall₂_append_middle_of
#check @DownOn.of_step
#check @Subterm.app_inv
#check @Subterm.trans
#check @subterms
#check @subtermsList
#check @subterms_var
#check @subterms_app
#check @subtermsList_nil
#check @subtermsList_cons
#check @mem_subtermsList
#check @mem_subterms_iff
#check @coalgebraOf
#check @mem_coalgebraOf
#check @coalgebra_coalgebraOf

#print axioms OperatorKO7.Meta.UniqueNormalization.Coalgebra
#print axioms OperatorKO7.Meta.UniqueNormalization.Coalgebra.arg
#print axioms OperatorKO7.Meta.UniqueNormalization.DownStepOn
#print axioms OperatorKO7.Meta.UniqueNormalization.DownStepOn_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.least
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.closed
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.induction
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.mem
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.rootComp
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.barComp
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.hatCl
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.barCl
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.tildeCl
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.toDown
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_self_of
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_append_middle_of
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.of_step
#print axioms OperatorKO7.Meta.UniqueNormalization.Subterm.app_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.Subterm.trans
#print axioms OperatorKO7.Meta.UniqueNormalization.subterms
#print axioms OperatorKO7.Meta.UniqueNormalization.subtermsList
#print axioms OperatorKO7.Meta.UniqueNormalization.subterms_var
#print axioms OperatorKO7.Meta.UniqueNormalization.subterms_app
#print axioms OperatorKO7.Meta.UniqueNormalization.subtermsList_nil
#print axioms OperatorKO7.Meta.UniqueNormalization.subtermsList_cons
#print axioms OperatorKO7.Meta.UniqueNormalization.mem_subtermsList
#print axioms OperatorKO7.Meta.UniqueNormalization.mem_subterms_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.coalgebraOf
#print axioms OperatorKO7.Meta.UniqueNormalization.mem_coalgebraOf
#print axioms OperatorKO7.Meta.UniqueNormalization.coalgebra_coalgebraOf

#check @hatEq
#check @hatEq.mono
#check @ConTopped.of_hatEq
#check @DownOn.constructorCompatible
#check @DownOn.hatEq_of_conTopped
#check @Up
#check @Reach
#check @Reach.refl
#check @Reach.head
#check @Terminating
#check @Reach.trans
#check @Reach.head_inv
#check @Reach.comparable
#check @EqvOn
#check @EqvOn.mem
#check @EqvOn.refl
#check @EqvOn.symm
#check @EqvOn.trans
#check @EqvOn.of_reach
#check @extendPar
#check @extendPar_self
#check @extendPar_of_ne
#check @extendPar_edge
#check @Reach.extend_of_not_reach
#check @terminating_extendPar

#print axioms OperatorKO7.Meta.UniqueNormalization.hatEq
#print axioms OperatorKO7.Meta.UniqueNormalization.hatEq.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.ConTopped.of_hatEq
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.constructorCompatible
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.hatEq_of_conTopped
#print axioms OperatorKO7.Meta.UniqueNormalization.Up
#print axioms OperatorKO7.Meta.UniqueNormalization.Reach
#print axioms OperatorKO7.Meta.UniqueNormalization.Reach.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.Reach.head
#print axioms OperatorKO7.Meta.UniqueNormalization.Terminating
#print axioms OperatorKO7.Meta.UniqueNormalization.Reach.trans
#print axioms OperatorKO7.Meta.UniqueNormalization.Reach.head_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.Reach.comparable
#print axioms OperatorKO7.Meta.UniqueNormalization.EqvOn
#print axioms OperatorKO7.Meta.UniqueNormalization.EqvOn.mem
#print axioms OperatorKO7.Meta.UniqueNormalization.EqvOn.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.EqvOn.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.EqvOn.trans
#print axioms OperatorKO7.Meta.UniqueNormalization.EqvOn.of_reach
#print axioms OperatorKO7.Meta.UniqueNormalization.extendPar
#print axioms OperatorKO7.Meta.UniqueNormalization.extendPar_self
#print axioms OperatorKO7.Meta.UniqueNormalization.extendPar_of_ne
#print axioms OperatorKO7.Meta.UniqueNormalization.extendPar_edge
#print axioms OperatorKO7.Meta.UniqueNormalization.Reach.extend_of_not_reach
#print axioms OperatorKO7.Meta.UniqueNormalization.terminating_extendPar

#check @forall₂_trans
#check @hatEq.trans
#check @ConTopped.of_hatEq_right
#check @ReachN
#check @ReachN.toReach
#check @Reach.toReachN
#check @Grey
#check @PGraph
#check @PGraph.eqvGen_up_mem_iff
#check @PGraph.reach_to_eqvGen_up
#check @PGraph.eqvOn_iff_eqvGen_up
#check @PGraph.NF
#check @hatEq_of_grey_of_conTopped
#check @conTopped_of_reach
#check @PGraph.mk
#check @PGraph.par
#check @PGraph.mem_edge
#check @PGraph.term
#check @PGraph.sub
#check @PGraph.grey
#check @hatEq.symm
#check @PGraph.hatEq_of_reach
#check @PGraph.constructorCompatible
#check @Reach.mono
#check @EqvOn.mono
#check @Grey.mono
#check @PGraph.Extends
#check @PGraph.Extends.refl
#check @PGraph.Extends.trans
#check @PGraph.Complete
#check @PGraph.nf_iff
#check @PGraph.roots
#check @PGraph.roots_ssubset_of_proper
#check @PGraph.exists_complete_extension

#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_trans
#print axioms OperatorKO7.Meta.UniqueNormalization.hatEq.trans
#print axioms OperatorKO7.Meta.UniqueNormalization.ConTopped.of_hatEq_right
#print axioms OperatorKO7.Meta.UniqueNormalization.ReachN
#print axioms OperatorKO7.Meta.UniqueNormalization.ReachN.toReach
#print axioms OperatorKO7.Meta.UniqueNormalization.Reach.toReachN
#print axioms OperatorKO7.Meta.UniqueNormalization.Grey
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.mk
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.par
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.mem_edge
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.term
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.sub
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.grey
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.eqvGen_up_mem_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.reach_to_eqvGen_up
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.eqvOn_iff_eqvGen_up
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.NF
#print axioms OperatorKO7.Meta.UniqueNormalization.hatEq_of_grey_of_conTopped
#print axioms OperatorKO7.Meta.UniqueNormalization.conTopped_of_reach
#print axioms OperatorKO7.Meta.UniqueNormalization.hatEq.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.hatEq_of_reach
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.constructorCompatible
#print axioms OperatorKO7.Meta.UniqueNormalization.Reach.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.EqvOn.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.Grey.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.Extends
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.Extends.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.Extends.trans
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.Complete
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.nf_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.roots
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.roots_ssubset_of_proper
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.exists_complete_extension

#check @ReachN.zero_inv
#check @ReachN.succ_inv
#check @exists_root
#check @hatEq.symm
#check @downOn_of_hatEq
#check @downOn_peel
#check @not_conTopped_peel
#check @lemma52_diag
#check @lemma52
#check @PGraph.extend_one
#check @PGraph.mem_of_reach_right
#check @PGraph.constructorClosed_of_complete

#print axioms OperatorKO7.Meta.UniqueNormalization.ReachN.zero_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.ReachN.succ_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.exists_root
#print axioms OperatorKO7.Meta.UniqueNormalization.downOn_of_hatEq
#print axioms OperatorKO7.Meta.UniqueNormalization.downOn_peel
#print axioms OperatorKO7.Meta.UniqueNormalization.not_conTopped_peel
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma52_diag
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma52
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.extend_one
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.mem_of_reach_right
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.constructorClosed_of_complete

/-! ## Section 7 targeted proof graphs: Definitions 57--63 and Lemmas 61--64 reduction -/

#check @BarStepOn
#check @BarStepOn.symm
#check @BarReachOn
#check @BarReachOn.refl
#check @BarReachOn.head
#check @BarReachOn.trans
#check @BarReachOn.symm
#check @BarReachN
#check @BarReachN.refl
#check @BarReachN.head
#check @BarReachN.toBarReach
#check @BarReachOn.toBarReachN
#check @BarReachN.zero_inv
#check @BarReachN.succ_inv
#check @barClassSetoid
#check @BarClass
#check @barClassOf
#check @RedexClass
#check @Target
#check @Target.mk
#check @Target.pick
#check @Target.pick_mem
#check @Target.inFiber
#check @Target.redexPriority
#check @ClassHasRedex
#check @classHasRedex_of_redexClass
#check @exists_targetRepresentative
#check @targetRepresentative
#check @targetRepresentative_spec
#check @canonicalTarget
#check @Target.pick_eq_of_barReach
#check @Target.distance
#check @Target.distance_spec
#check @Target.eq_target_of_distance_zero
#check @Target.exists_distance_decreasing_step
#check @Target.next
#check @Target.next_spec
#check @Target.parent
#check @Target.parent_eq_some_next
#check @Target.parent_edge
#check @Target.parent_terminating
#check @Target.parent_eq_none_of_target
#check @PGraph.empty
#check @Target.baseGraph
#check @Target.baseGraph_par
#check @Target.barReach_of_parentReach
#check @GuidedParentStep
#check @GuidedReach
#check @GuidedReach.toReach
#check @GuidedReach.toBarReach
#check @Target.guidedReach_baseGraph_of_parentReach
#check @Target.guidedReach_baseGraph
#check @GuidedReach.mono
#check @Reach.toReflTransGenRev
#check @Terminating.no_parent_cycle
#check @TargetedPGraph
#check @TargetedPGraph.mk
#check @TargetedPGraph.graph
#check @TargetedPGraph.target
#check @TargetedPGraph.guided_or_nf
#check @TargetedPGraph.target_exit
#check @TargetedPGraph.Extends
#check @Target.baseTargeted
#check @TargetedPGraph.AllGuided
#check @Target.baseTargeted_allGuided
#check @Target.exists_complete_targeted
#check @exists_complete_targeted
#check @SigmaClosedOn
#check @TargetedPGraph.sigmaClosedOn_of_all_guided
#check @TargetedPGraph.sigmaClosedOn_of_complete
#check @PGraph.Universal
#check @PGraph.universal_iff_down_subset
#check @TargetedPGraph.universal_of_complete_of_rootClosure

#print axioms OperatorKO7.Meta.UniqueNormalization.BarStepOn
#print axioms OperatorKO7.Meta.UniqueNormalization.BarStepOn.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachOn
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachOn.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachOn.head
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachOn.trans
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachOn.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachN
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachN.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachN.head
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachN.toBarReach
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachOn.toBarReachN
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachN.zero_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachN.succ_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.barClassSetoid
#print axioms OperatorKO7.Meta.UniqueNormalization.BarClass
#print axioms OperatorKO7.Meta.UniqueNormalization.barClassOf
#print axioms OperatorKO7.Meta.UniqueNormalization.RedexClass
#print axioms OperatorKO7.Meta.UniqueNormalization.Target
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.mk
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.pick
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.pick_mem
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.inFiber
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.redexPriority
#print axioms OperatorKO7.Meta.UniqueNormalization.ClassHasRedex
#print axioms OperatorKO7.Meta.UniqueNormalization.classHasRedex_of_redexClass
#print axioms OperatorKO7.Meta.UniqueNormalization.exists_targetRepresentative
#print axioms OperatorKO7.Meta.UniqueNormalization.targetRepresentative
#print axioms OperatorKO7.Meta.UniqueNormalization.targetRepresentative_spec
#print axioms OperatorKO7.Meta.UniqueNormalization.canonicalTarget
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.pick_eq_of_barReach
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.distance
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.distance_spec
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.eq_target_of_distance_zero
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.exists_distance_decreasing_step
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.next
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.next_spec
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.parent
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.parent_eq_some_next
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.parent_edge
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.parent_terminating
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.parent_eq_none_of_target
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.empty
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.baseGraph
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.baseGraph_par
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.barReach_of_parentReach
#print axioms OperatorKO7.Meta.UniqueNormalization.GuidedParentStep
#print axioms OperatorKO7.Meta.UniqueNormalization.GuidedReach
#print axioms OperatorKO7.Meta.UniqueNormalization.GuidedReach.toReach
#print axioms OperatorKO7.Meta.UniqueNormalization.GuidedReach.toBarReach
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.guidedReach_baseGraph_of_parentReach
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.guidedReach_baseGraph
#print axioms OperatorKO7.Meta.UniqueNormalization.GuidedReach.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.Reach.toReflTransGenRev
#print axioms OperatorKO7.Meta.UniqueNormalization.Terminating.no_parent_cycle
#print axioms OperatorKO7.Meta.UniqueNormalization.TargetedPGraph
#print axioms OperatorKO7.Meta.UniqueNormalization.TargetedPGraph.mk
#print axioms OperatorKO7.Meta.UniqueNormalization.TargetedPGraph.graph
#print axioms OperatorKO7.Meta.UniqueNormalization.TargetedPGraph.target
#print axioms OperatorKO7.Meta.UniqueNormalization.TargetedPGraph.guided_or_nf
#print axioms OperatorKO7.Meta.UniqueNormalization.TargetedPGraph.target_exit
#print axioms OperatorKO7.Meta.UniqueNormalization.TargetedPGraph.Extends
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.baseTargeted
#print axioms OperatorKO7.Meta.UniqueNormalization.TargetedPGraph.AllGuided
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.baseTargeted_allGuided
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.exists_complete_targeted
#print axioms OperatorKO7.Meta.UniqueNormalization.exists_complete_targeted
#print axioms OperatorKO7.Meta.UniqueNormalization.SigmaClosedOn
#print axioms OperatorKO7.Meta.UniqueNormalization.TargetedPGraph.sigmaClosedOn_of_all_guided
#print axioms OperatorKO7.Meta.UniqueNormalization.TargetedPGraph.sigmaClosedOn_of_complete
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.Universal
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.universal_iff_down_subset
#print axioms OperatorKO7.Meta.UniqueNormalization.TargetedPGraph.universal_of_complete_of_rootClosure

/-! ## The summit reduction -/

example {R : TRS (sigma ⊕ sigma) nu}
    (htrans : ∀ x y z : Term (sigma ⊕ sigma) nu, Down R x y → Down R y z → Down R x z)
    (a b : Term (sigma ⊕ sigma) nu) : conv R a b ↔ Down R a b :=
  conv_eq_down htrans a b

example (R : TRS sigma nu) : ConstructorRules (constructorTranslation R) :=
  constructorRules_constructorTranslation R

example {R : TRS sigma nu} {x y : nu} (hxy : x ≠ y)
    (htrans : ∀ S : TRS sigma nu, NonOmegaOverlapping S → TRS.RhsDetermined S →
      ∀ p q r : Term (sigma ⊕ sigma) nu,
        Down (constructorTranslation S) p q → Down (constructorTranslation S) q r →
        Down (constructorTranslation S) p r)
    (hclass : ∀ t u : Term sigma nu, NormalForm R t → NormalForm R u →
      conv R t u → t ≠ u →
      ∃ F : sigma, NonOmegaOverlapping (extendedTRS R F t u x y) ∧
        TRS.RhsDetermined (extendedTRS R F t u x y)) :
    UNconv R ∧ UNred R :=
  ⟨UNconv_of_down_trans hxy htrans hclass, UNred_of_down_trans hxy htrans hclass⟩

#check @constructorRules_constructorTranslation
#check @Down.to_conv
#check @Down.of_conv
#check @conv_eq_down
#check @constructorCompatible_conv_of_down_trans
#check @UNconv_of_down_trans
#check @UNred_of_down_trans

#print axioms OperatorKO7.Meta.UniqueNormalization.constructorRules_constructorTranslation
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.to_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.of_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.conv_eq_down
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorCompatible_conv_of_down_trans
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_down_trans
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_down_trans

/-! ## Exact parent replacement on arbitrary carriers -/

#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path.refl
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path.head
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path.head
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Terminating
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Terminating
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.replace
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.replace
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.cut
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.cut
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.replace_self
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.replace_self
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.replace_of_ne
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.replace_of_ne
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.replace_edge
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.replace_edge
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.cut_edge
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.cut_edge
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path.mono
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path.eq_of_none
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path.eq_of_none
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path.toReflTransGenRev
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path.toReflTransGenRev
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Terminating.no_cycle
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Terminating.no_cycle
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path.replace_to_source
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path.replace_to_source
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path.cut_to_source
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path.cut_to_source
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.path_cut_to_source_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.path_cut_to_source_iff
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.terminating_replace_of_no_return
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.terminating_replace_of_no_return
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.terminating_replace_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.terminating_replace_iff
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.terminating_cut_of_replace
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.terminating_cut_of_replace
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.replace_cut
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.replace_cut
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.terminating_replace_iff_cut
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.terminating_replace_iff_cut
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.descendingParent
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.descendingParent
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.descendingParent_terminating
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.descendingParent_terminating
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.non_root_replacement_terminates
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.non_root_replacement_terminates
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.backward_replacement_not_terminating
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.backward_replacement_not_terminating
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.selfLoopParent
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.selfLoopParent
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.selfLoopParent_not_terminating
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.selfLoopParent_not_terminating
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.selfLoop_replacement_terminates
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.selfLoop_replacement_terminates
#check @OperatorKO7.Meta.UniqueNormalization.extendPar_eq_replace
#print axioms OperatorKO7.Meta.UniqueNormalization.extendPar_eq_replace
#check @OperatorKO7.Meta.UniqueNormalization.Reach.toParentPath
#print axioms OperatorKO7.Meta.UniqueNormalization.Reach.toParentPath
#check @OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path.toReach
#print axioms OperatorKO7.Meta.UniqueNormalization.ParentReplacement.Path.toReach
#check @OperatorKO7.Meta.UniqueNormalization.terminating_extendPar_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.terminating_extendPar_iff
#check @OperatorKO7.Meta.UniqueNormalization.terminating_extendPar_iff_cut
#print axioms OperatorKO7.Meta.UniqueNormalization.terminating_extendPar_iff_cut

example {α : Type u} (g : α → Option α) (a b : α) :
    ParentReplacement.Terminating (ParentReplacement.replace g a b) ↔
      ParentReplacement.Terminating (ParentReplacement.cut g a) ∧
        ¬ ParentReplacement.Path g b a :=
  ParentReplacement.terminating_replace_iff_cut

example :
    ¬ ParentReplacement.Terminating ParentReplacement.selfLoopParent ∧
      ParentReplacement.Terminating
        (ParentReplacement.replace ParentReplacement.selfLoopParent 1 0) :=
  ⟨ParentReplacement.selfLoopParent_not_terminating,
    ParentReplacement.selfLoop_replacement_terminates⟩

#check @OperatorKO7.Meta.UniqueNormalization.EqvOn.mono_of_parent_eqv
#print axioms OperatorKO7.Meta.UniqueNormalization.EqvOn.mono_of_parent_eqv
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.reroot_one
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.reroot_one
#check @OperatorKO7.Meta.UniqueNormalization.ReversibleReach
#print axioms OperatorKO7.Meta.UniqueNormalization.ReversibleReach
#check @OperatorKO7.Meta.UniqueNormalization.ReversibleReach.toReach
#print axioms OperatorKO7.Meta.UniqueNormalization.ReversibleReach.toReach
#check @OperatorKO7.Meta.UniqueNormalization.ReversibleReach.trans
#print axioms OperatorKO7.Meta.UniqueNormalization.ReversibleReach.trans
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.reroot_reversible
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.reroot_reversible
#check @OperatorKO7.Meta.UniqueNormalization.GuidedReach.reversible
#print axioms OperatorKO7.Meta.UniqueNormalization.GuidedReach.reversible
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.repair_along_reversible_path
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.repair_along_reversible_path
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.repair_rootStep_along_guided_path
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.repair_rootStep_along_guided_path
#check @OperatorKO7.Meta.UniqueNormalization.ReversibleReach.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.ReversibleReach.refl
#check @OperatorKO7.Meta.UniqueNormalization.ReversibleReach.head
#print axioms OperatorKO7.Meta.UniqueNormalization.ReversibleReach.head

/-! ## Completion by represented equalities -/

#check @OperatorKO7.Meta.UniqueNormalization.PGraph.EqualityExtends
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.EqualityExtends
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.EqualityExtends.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.EqualityExtends.refl
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.EqualityExtends.trans
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.EqualityExtends.trans
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.EqualityComplete
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.EqualityComplete
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.eqvPairs
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.eqvPairs
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.mem_eqvPairs
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.mem_eqvPairs
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.eqvPairs_subset_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.eqvPairs_subset_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.eqvGap
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.eqvGap
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.eqvGap_lt_of_strict_equality_extension
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.eqvGap_lt_of_strict_equality_extension
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.exists_equalityComplete
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.exists_equalityComplete
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.EqualityComplete.complete
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.EqualityComplete.complete
#check @OperatorKO7.Meta.UniqueNormalization.equality_extension_chain_length_le
#print axioms OperatorKO7.Meta.UniqueNormalization.equality_extension_chain_length_le
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.EqualityComplete.grey_of_reversible_to_root
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.EqualityComplete.grey_of_reversible_to_root
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.EqualityComplete.rootStep_of_guided_to_root
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.EqualityComplete.rootStep_of_guided_to_root
#check @OperatorKO7.Meta.UniqueNormalization.exists_equalityComplete_with_guided_rootClosure
#print axioms OperatorKO7.Meta.UniqueNormalization.exists_equalityComplete_with_guided_rootClosure

example {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) :
    ∃ beta : PGraph A R, rho.EqualityExtends beta ∧ beta.Complete := by
  obtain ⟨beta, hab, hmax⟩ := rho.exists_equalityComplete
  exact ⟨beta, hab, hmax.complete⟩

example (R : TRS (Unit ⊕ Unit) Unit) :
    ∃ rho : PGraph [] R, rho.EqualityComplete := by
  obtain ⟨rho, _, hmax⟩ := (PGraph.empty [] R).exists_equalityComplete
  exact ⟨rho, hmax⟩

/-! ## Normal roots and attained inter-fiber exit distances -/

#check @OperatorKO7.Meta.UniqueNormalization.PGraph.normalRoot
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.normalRoot
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.normalRoot_spec
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.normalRoot_spec
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.normalRoot_mem
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.normalRoot_mem
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.normalRoot_eq_of_reach
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.normalRoot_eq_of_reach
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.eqvOn_iff_normalRoot_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.eqvOn_iff_normalRoot_eq
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.eqv_of_barReach
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.eqv_of_barReach
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.normalRoot_eq_of_barReach
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.normalRoot_eq_of_barReach
#check @OperatorKO7.Meta.UniqueNormalization.Target.baseGraph_barClosed
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.baseGraph_barClosed
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.mono
#check @OperatorKO7.Meta.UniqueNormalization.exists_equalityComplete_barClosed
#print axioms OperatorKO7.Meta.UniqueNormalization.exists_equalityComplete_barClosed
#check @OperatorKO7.Meta.UniqueNormalization.FiberRouteN
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberRouteN
#check @OperatorKO7.Meta.UniqueNormalization.FiberRouteN.prepend_bar
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberRouteN.prepend_bar
#check @OperatorKO7.Meta.UniqueNormalization.FiberRouteN.zero_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberRouteN.zero_iff
#check @OperatorKO7.Meta.UniqueNormalization.FiberRouteN.succ_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberRouteN.succ_inv
#check @OperatorKO7.Meta.UniqueNormalization.Reach.toFiberRouteN
#print axioms OperatorKO7.Meta.UniqueNormalization.Reach.toFiberRouteN
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.fiberDistance
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.fiberDistance
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.fiberDistance_spec
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.fiberDistance_spec
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.fiberDistance_le
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.fiberDistance_le
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.fiberDistance_zero_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.fiberDistance_zero_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.fiberDistance_eq_of_barReach
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.fiberDistance_eq_of_barReach
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.exists_distance_decreasing_exit
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.exists_distance_decreasing_exit
#check @OperatorKO7.Meta.UniqueNormalization.FiberRouteN.zero
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberRouteN.zero
#check @OperatorKO7.Meta.UniqueNormalization.FiberRouteN.head
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberRouteN.head

example {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a : Term (sigma ⊕ sigma) nu) (ha : rho.NF a) :
    rho.fiberDistance a = 0 := by
  apply (rho.fiberDistance_zero_iff a).mpr
  have heq := (rho.normalRoot_spec a).1.toParentPath.eq_of_none ha
  rw [← heq]
  exact BarReachOn.refl a

example (R : TRS (Unit ⊕ Unit) Unit) :
    (PGraph.empty [] R).fiberDistance (.var ()) = 0 := by
  apply (PGraph.fiberDistance_zero_iff _ _).mpr
  have heq := (PGraph.normalRoot_spec (PGraph.empty [] R) (.var ())).1.toParentPath.eq_of_none
    (show (PGraph.empty [] R).par (.var ()) = none from rfl)
  rw [← heq]
  exact BarReachOn.refl _

/-! ## Targets selected from actual decreasing exits -/

#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.normalRoot_eq_of_barReach_all
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.normalRoot_eq_of_barReach_all
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.fiberDistance_eq_of_barReach_all
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.fiberDistance_eq_of_barReach_all
#check @OperatorKO7.Meta.UniqueNormalization.FiberExit
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberExit
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.exitChoice
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.exitChoice
#check @OperatorKO7.Meta.UniqueNormalization.RedexClass.not_conTopped_source
#print axioms OperatorKO7.Meta.UniqueNormalization.RedexClass.not_conTopped_source
#check @OperatorKO7.Meta.UniqueNormalization.FiberExit.rootStep_of_redexClass
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberExit.rootStep_of_redexClass
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetPick
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetPick
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetExit
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetExit
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetPick_mem
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetPick_mem
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetPick_inFiber
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetPick_inFiber
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetPick_distance
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetPick_distance
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetExit_spec
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetExit_spec
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetExit_none_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetExit_none_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retarget
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retarget
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retarget_pick_distance
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retarget_pick_distance
#check @OperatorKO7.Meta.UniqueNormalization.FiberExit.mk
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberExit.mk
#check @OperatorKO7.Meta.UniqueNormalization.FiberExit.src
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberExit.src
#check @OperatorKO7.Meta.UniqueNormalization.FiberExit.dst
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberExit.dst
#check @OperatorKO7.Meta.UniqueNormalization.FiberExit.src_mem
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberExit.src_mem
#check @OperatorKO7.Meta.UniqueNormalization.FiberExit.dst_mem
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberExit.dst_mem
#check @OperatorKO7.Meta.UniqueNormalization.FiberExit.sameFiber
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberExit.sameFiber
#check @OperatorKO7.Meta.UniqueNormalization.FiberExit.edge
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberExit.edge
#check @OperatorKO7.Meta.UniqueNormalization.FiberExit.distance_src
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberExit.distance_src
#check @OperatorKO7.Meta.UniqueNormalization.FiberExit.distance_drop
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberExit.distance_drop
#check @OperatorKO7.Meta.UniqueNormalization.FiberExit.exits
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberExit.exits

example {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (a : Term (sigma ⊕ sigma) nu) :
    rho.fiberDistance a = rho.fiberDistance a :=
  hclosed.fiberDistance_eq_of_barReach_all (BarReachOn.refl a)

example {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (C : BarClass A R)
    (hzero : rho.fiberDistance (hclosed.retargetPick C) = 0) :
    hclosed.retargetExit C = none :=
  (hclosed.retargetExit_none_iff C).mpr hzero

/-! ## Actual reconstructed parents and targeted equality completion -/

#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_of_target
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_of_target
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_of_nontarget
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_of_nontarget
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_edge
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_edge
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_decreases
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_decreases
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_terminating
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_terminating
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_extends_target
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_extends_target
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_old_eqv
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_old_eqv
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_normalRoot_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_normalRoot_eq
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_mem_reach
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_mem_reach
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetSink
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetSink
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetSink_eq_of_normalRoot_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetSink_eq_of_normalRoot_eq
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_terminal_eq_sink
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_terminal_eq_sink
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_reaches_sink
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_reaches_sink
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_eqv_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetParent_eqv_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetGraph
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetGraph
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetGraph_eqv_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargetGraph_eqv_iff
#check @OperatorKO7.Meta.UniqueNormalization.Target.guidedReach_of_parent_extension
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.guidedReach_of_parent_extension
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargeted
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargeted
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargeted_allGuided
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargeted_allGuided
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargeted_equalityComplete
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.BarClosed.retargeted_equalityComplete
#check @OperatorKO7.Meta.UniqueNormalization.exists_equalityComplete_targeted
#print axioms OperatorKO7.Meta.UniqueNormalization.exists_equalityComplete_targeted

example {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    (a b : Term (sigma ⊕ sigma) nu) :
    EqvOn A (hclosed.retargeted hR).graph.par a b ↔ EqvOn A rho.par a b :=
  hclosed.retargetGraph_eqv_iff hR a b

example (R : TRS (Unit ⊕ Unit) Unit) (hR : ConstructorRules R) :
    ∃ rho : TargetedPGraph [] R, rho.AllGuided := by
  have hclosed : (PGraph.empty [] R).BarClosed := by
    intro a b hbar
    exact (List.not_mem_nil hbar.1).elim
  exact ⟨hclosed.retargeted hR, hclosed.retargeted_allGuided hR⟩

#check @OperatorKO7.Meta.UniqueNormalization.CT.unfold
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.unfold

#check @OperatorKO7.Meta.UniqueNormalization.CT.eq_of_sigmaClosed
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.eq_of_sigmaClosed

#check @OperatorKO7.Meta.UniqueNormalization.CT.idempotent
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.idempotent

#check @OperatorKO7.Meta.UniqueNormalization.CT.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.refl

#check @OperatorKO7.Meta.UniqueNormalization.CT.flip
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.flip

#check @OperatorKO7.Meta.UniqueNormalization.CT.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.symm

#check @OperatorKO7.Meta.UniqueNormalization.CT.var_left_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.var_left_iff

#check @OperatorKO7.Meta.UniqueNormalization.CT.var_right_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.var_right_iff

#check @OperatorKO7.Meta.UniqueNormalization.CT.constructorCompatible
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.constructorCompatible

#check @OperatorKO7.Meta.UniqueNormalization.CT.constructor_apps_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.constructor_apps_iff

example : CT (fun (_ _ : Term (Unit ⊕ Unit) Unit) => False)
    (.app (.inl ()) []) (.app (.inl ()) []) :=
  CT.app List.Forall₂.nil

example : ¬ CT (fun (_ _ : Term (Unit ⊕ Unit) Unit) => False) (.var ()) (.var ()) := by
  intro h
  exact CT.var_left_iff.mp h

#check @OperatorKO7.Meta.UniqueNormalization.forall₂_compose_of_mem
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_compose_of_mem

#check @OperatorKO7.Meta.UniqueNormalization.CT.transitiveOn_of_base_absorption
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.transitiveOn_of_base_absorption

#check @OperatorKO7.Meta.UniqueNormalization.CT.transitiveOn_of_base_context
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.transitiveOn_of_base_context

#check @OperatorKO7.Meta.UniqueNormalization.CT.transitiveOn_iff_base_context
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.transitiveOn_iff_base_context

#check @OperatorKO7.Meta.UniqueNormalization.CT.transitive_iff_base_context
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.transitive_iff_base_context

example {sigma : Type u} {nu : Type v}
    (a b c : Term (sigma ⊕ sigma) nu)
    (hab : CT (fun p q => p = q) a b) (hbc : CT (fun p q => p = q) b c) :
    CT (fun p q => p = q) a c := by
  apply (CT.transitive_iff_base_context (E := fun (p q : Term (sigma ⊕ sigma) nu) => p = q)
    (fun _ _ h => h.symm) (fun _ _ _ h₁ h₂ => h₁.trans h₂)).mpr ?_ a b c hab hbc
  intro p q r hpq hqr
  subst q
  exact CT.sigmaClosed p r hqr


#check @OperatorKO7.Meta.UniqueNormalization.Coalgebra.nil
#print axioms OperatorKO7.Meta.UniqueNormalization.Coalgebra.nil

#check @OperatorKO7.Meta.UniqueNormalization.Coalgebra.append
#print axioms OperatorKO7.Meta.UniqueNormalization.Coalgebra.append

#check @OperatorKO7.Meta.UniqueNormalization.DownOn.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.mono

#check @OperatorKO7.Meta.UniqueNormalization.DownOn.append_left
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.append_left

#check @OperatorKO7.Meta.UniqueNormalization.DownOn.append_right
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.append_right

#check @OperatorKO7.Meta.UniqueNormalization.forall₂_downOn_exists
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_downOn_exists

#check @OperatorKO7.Meta.UniqueNormalization.Down.exists_finite_coalgebra
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.exists_finite_coalgebra

#check @OperatorKO7.Meta.UniqueNormalization.Down.iff_exists_finite_coalgebra
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.iff_exists_finite_coalgebra

#check @OperatorKO7.Meta.UniqueNormalization.Down.pair_exists_finite_coalgebra
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.pair_exists_finite_coalgebra

#check @OperatorKO7.Meta.UniqueNormalization.Down.trans_of_finite_coalgebras
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.trans_of_finite_coalgebras

example {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (hab : rootStep R a b) :
    ∃ A, Coalgebra A ∧ DownOn A R a b ∧ DownOn A R b a :=
  Down.pair_exists_finite_coalgebra (Down.rootComp hab (Down.refl b))
    (Down.symm (Down.rootComp hab (Down.refl b)))

example :
    ∃ A, Coalgebra A ∧
      DownOn A
        ([{ lhs := .app (Sum.inr ()) [.var ()], rhs := .var (), lhs_isApp := rfl }] :
          TRS (Unit ⊕ Unit) Unit)
        (.app (.inr ()) [.var ()]) (.var ()) := by
  apply Down.exists_finite_coalgebra
  apply Down.rootComp (c := Term.var ())
  · exact ⟨_, List.mem_singleton_self _, Subst.id, by simp [Subst.id], by simp [Subst.id]⟩
  · exact Down.refl _


end OperatorKO7.Test.UN79CoreReach
