import OperatorKO7.Meta.Methods.OrientationClosure.HypothesisNecessityBase
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsLabelingBounds
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsSortedConstrained

/-!
# Hypothesis necessity of the labelling, match-bound and sorted or constrained rows

Thirteen rows of the method universe, each with its necessity kind, its necessity statement on the
row's own laws and acceptance predicate, and the proof of that statement.

Relation: the row's own acceptance predicate for the free recursor or the free schema.
Property: necessity of one law clause or one data feature, stated by a concrete datum, or a proof
that the laws fix the verdict.
External trust: none.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.HypothesisNecessity

universe v

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness
open OperatorKO7.Methods.OrientationClosure.ProcessorSemantics

/-! ## Labelling, match-bound, forward-closure and quasi-decreasingness rows -/

section LabelingBoundsRows

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate
open OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity
open OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds

/-! ### Row: semanticLabeling -/

/-- The labelling of a semantic-labelling datum. -/
def semanticLabelingLabelLens :
    FeatureLens semanticLabelingData (FreeSym → Option (List ℕ → ℕ)) where
  get M := M.ℓ
  set M w := { M with ℓ := w }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

def semanticLabelingNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Replacing the counter labelling of the witness by the constant labelling keeps the model and
the positive coefficients and loses the orientation of the labelled successor rule. -/
def semanticLabelingNecessityStatement : Prop :=
  EscapeFeatureNecessity semanticLabelingLaws semanticLabelingAccepts semanticLabelingLabelLens

theorem semanticLabeling_necessity : semanticLabelingNecessityStatement := by
  have hRej : ¬ semanticLabelingAccepts
      (semanticLabelingLabelLens.set semanticLabelingWitness constLab) :=
    semanticLabeling_mutation.2
  exact ⟨{ base := semanticLabelingWitness
           baseLaws := semanticLabelingWitness_laws
           baseAccepts := semanticLabelingWitness_accepts
           value := constLab
           valueDiffers := fun h => hRej ((congrArg
             (fun w : FreeSym → Option (List ℕ → ℕ) =>
               semanticLabelingAccepts (semanticLabelingLabelLens.set semanticLabelingWitness w))
             h).mpr semanticLabelingWitness_accepts)
           changedLaws := semanticLabeling_mutation.1
           changedRejects := hRej }⟩

/-! ### Row: rootLabeling -/

/-- The recursor slice of a root-labelling base interpretation: the operations of every labelled
recursor symbol. -/
def rootLabelingRecurLens :
    FeatureLens rootLabelingData (Option (List FreeSym) → List ℕ → ℕ) where
  get J o xs := J.interp (FreeSym.recur, o) xs
  set J w := ⟨fun g xs => if g.1 = FreeSym.recur then w g.2 xs else J.interp g xs⟩
  get_set J w := by
    funext o xs
    simp
  set_get J := by
    obtain ⟨interp⟩ := J
    simp only [Alg.mk.injEq]
    funext g xs
    obtain ⟨f, o⟩ := g
    by_cases hf : f = FreeSym.recur
    · subst hf
      simp
    · simp [hf]
  set_set J w w' := by
    simp only [Alg.mk.injEq]
    funext g xs
    by_cases hg : g.1 = FreeSym.recur <;> simp [hg]

/-- Replacing the recursor slice of the witness by `1 + Σ xs` gives the label-blind linear
interpretation. -/
theorem rootLabelingRecurLens_set_linear :
    rootLabelingRecurLens.set rootLabelingWitness (fun _ xs => 1 + xs.sum) =
      blindAlg cpLinAlg := by
  show Alg.mk _ = Alg.mk _
  simp only [Alg.mk.injEq]
  funext g xs
  obtain ⟨f, o⟩ := g
  cases f <;> rfl

def rootLabelingNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Replacing the coupled recursor operations of the witness by the linear form `1 + Σ xs` keeps
strict monotonicity and loses the orientation of the root-labelled flat-context closure. -/
def rootLabelingNecessityStatement : Prop :=
  EscapeFeatureNecessity rootLabelingLaws rootLabelingAccepts rootLabelingRecurLens

theorem rootLabeling_necessity : rootLabelingNecessityStatement :=
  ⟨{ base := rootLabelingWitness
     baseLaws := rootLabelingWitness_laws
     baseAccepts := rootLabelingWitness_accepts
     value := fun _ xs => 1 + xs.sum
     valueDiffers := fun h => absurd (congrFun (congrFun h none) [0, 0, 1]) (by decide)
     changedLaws := by rw [rootLabelingRecurLens_set_linear]; exact rootLabeling_mutation.1
     changedRejects := by rw [rootLabelingRecurLens_set_linear]; exact rootLabeling_mutation.2 }⟩

/-! ### Row: selfLabelingEquational -/

/-- The numerical reading of the classes in a self-labelling datum. -/
def selfLabelingEquationalReadingLens :
    FeatureLens selfLabelingEquationalData (Term FreeSym Nat → ℕ) where
  get D := D.Φ
  set D w := { D with Φ := w }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- With the zero reading every labelled recursor is `1 + b + s + n`, and the labelled successor
rule is not oriented. -/
theorem selfLabelingEquationalZeroReading_rejects :
    ¬ selfLabelingEquationalAccepts
      (selfLabelingEquationalReadingLens.set selfLabelingEquationalWitness (fun _ => 0)) := by
  intro h
  have key := h succRule (by simp [freeRecursorTRS]) (fun _ => Quotient.mk _ fz) (fun _ => 0)
  simp [selfLabelingEquationalReadingLens, selfLabelingEquationalWitness, SelfLabData.base,
    succRule, selfLab, linForm, linSum] at key

def selfLabelingEquationalNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Replacing the wrapper-count reading of the witness by the zero reading keeps the equational
theory, hence the laws, and loses the orientation of the self-labelled successor rule. -/
def selfLabelingEquationalNecessityStatement : Prop :=
  EscapeFeatureNecessity selfLabelingEquationalLaws selfLabelingEquationalAccepts
    selfLabelingEquationalReadingLens

theorem selfLabelingEquational_necessity : selfLabelingEquationalNecessityStatement :=
  ⟨{ base := selfLabelingEquationalWitness
     baseLaws := selfLabelingEquationalWitness_laws
     baseAccepts := selfLabelingEquationalWitness_accepts
     value := fun _ => 0
     valueDiffers := fun h => selfLabelingEquationalZeroReading_rejects ((congrArg
       (fun w : Term FreeSym Nat → ℕ => selfLabelingEquationalAccepts
         (selfLabelingEquationalReadingLens.set selfLabelingEquationalWitness w)) h).mpr
       selfLabelingEquationalWitness_accepts)
     changedLaws := selfLabelingEquationalWitness_laws
     changedRejects := selfLabelingEquationalZeroReading_rejects }⟩

/-! ### Row: quasiDecreasingness -/

/-- The successor redex `recur(zero, zero, succ zero)`. -/
def quasiDecreasingnessPoint : Term FreeSym Nat := fr fz fz (fs fz)

/-- The reduced successor set of the point: the proper subterms of the point and every term below
one of them in the coupled-polynomial order. -/
def quasiDecreasingnessRow (c : Term FreeSym Nat) : Prop :=
  ∃ y, ProperSubterm y quasiDecreasingnessPoint ∧ (c = y ∨ algGt cpAlg y c)

/-- The successor set of a term in an order. -/
def quasiDecreasingnessPointLens : FeatureLens quasiDecreasingnessData (Term FreeSym Nat → Prop) :=
  pointLens quasiDecreasingnessPoint

/-- The witness order with the successor set of the point replaced by the reduced set. -/
def quasiDecreasingnessReducedOrder : quasiDecreasingnessData :=
  quasiDecreasingnessPointLens.set quasiDecreasingnessWitness quasiDecreasingnessRow

theorem quasiDecreasingnessReducedOrder_apply (x : Term FreeSym Nat) :
    quasiDecreasingnessReducedOrder x =
      if x = quasiDecreasingnessPoint then quasiDecreasingnessRow else algGt cpAlg x :=
  Function.update_apply _ _ _ _

theorem quasiDecreasingnessRow_below {c : Term FreeSym Nat} (h : quasiDecreasingnessRow c) :
    algGt cpAlg quasiDecreasingnessPoint c := by
  obtain ⟨y, hy, rfl | hyc⟩ := h
  · exact algGt_of_properSubterm cpAlg cpAlg_sub hy
  · exact fun β => lt_trans (hyc β) (algGt_of_properSubterm cpAlg cpAlg_sub hy β)

theorem quasiDecreasingnessReducedOrder_below (x c : Term FreeSym Nat)
    (h : quasiDecreasingnessReducedOrder x c) : algGt cpAlg x c := by
  rw [quasiDecreasingnessReducedOrder_apply] at h
  split_ifs at h with hx
  · subst hx
    exact quasiDecreasingnessRow_below h
  · exact h

theorem quasiDecreasingnessReducedOrder_laws :
    quasiDecreasingnessLaws quasiDecreasingnessReducedOrder := by
  refine ⟨Subrelation.wf (fun {_ _} h => quasiDecreasingnessReducedOrder_below _ _ h)
      (algGt_wf cpAlg), fun a b => ⟨fun h => .single (Or.inl h), fun h => ?_⟩⟩
  have hgt : ∀ {x y : Term FreeSym Nat}, Relation.TransGen
      (fun x y => quasiDecreasingnessReducedOrder x y ∨ ProperSubterm y x) x y →
        algGt cpAlg x y := by
    intro x y hxy
    induction hxy with
    | single h =>
      exact h.elim (quasiDecreasingnessReducedOrder_below _ _)
        (algGt_of_properSubterm cpAlg cpAlg_sub)
    | tail _ h ih =>
      intro β
      exact lt_trans (h.elim (quasiDecreasingnessReducedOrder_below _ _)
        (algGt_of_properSubterm cpAlg cpAlg_sub) β) (ih β)
  rw [quasiDecreasingnessReducedOrder_apply]
  split_ifs with ha
  · subst ha
    obtain ⟨c, hc, hcb⟩ := Relation.TransGen.head'_iff.1 h
    have hrow : quasiDecreasingnessRow c := by
      rcases hc with hc | hc
      · rw [quasiDecreasingnessReducedOrder_apply, if_pos rfl] at hc
        exact hc
      · exact ⟨c, hc, Or.inl rfl⟩
    obtain ⟨y, hy, hcy⟩ := hrow
    refine ⟨y, hy, ?_⟩
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 hcb with rfl | hcb'
    · exact hcy
    · have hcb'' := hgt hcb'
      rcases hcy with rfl | hyc
      · exact Or.inr hcb''
      · exact Or.inr fun β => lt_trans (hcb'' β) (hyc β)
  · exact hgt h

theorem quasiDecreasingness_eval_le_of_isSubterm {w t : Term FreeSym Nat} (h : IsSubterm w t)
    (β : Nat → ℕ) : Alg.eval cpAlg β w ≤ Alg.eval cpAlg β t := by
  induction h with
  | refl => exact le_rfl
  | arg f args hmem _ ih =>
    rw [Alg.eval_app]
    exact le_trans ih (cpAlg_sub f _ _ (List.mem_map_of_mem hmem)).le

theorem quasiDecreasingness_properSubterm_point_eval_le {y : Term FreeSym Nat}
    (hy : ProperSubterm y quasiDecreasingnessPoint) : Alg.eval cpAlg (fun _ => 0) y ≤ 2 := by
  have key : ∀ {w t : Term FreeSym Nat}, ProperSubterm w t → t = quasiDecreasingnessPoint →
      Alg.eval cpAlg (fun _ => 0) w ≤ 2 := by
    intro w t h ht
    cases h with
    | arg f args hmem hs =>
      simp only [quasiDecreasingnessPoint, fr, fs, fz, Term.app.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      refine le_trans (quasiDecreasingness_eval_le_of_isSubterm hs _) ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;> simp [cpAlg]
  exact key hy rfl

/-- The contractum `wrap(zero, recur(zero, zero, zero))` of the point lies outside the reduced
set. -/
theorem quasiDecreasingnessRow_not_contractum : ¬ quasiDecreasingnessRow (fw fz (fr fz fz fz)) := by
  rintro ⟨y, hy, hyc⟩
  have hle := quasiDecreasingness_properSubterm_point_eval_le hy
  have hval : Alg.eval cpAlg (fun _ => 0) (fw fz (fr fz fz fz)) = 10 := by
    simp [cpAlg, fw, fr, fz]
  rcases hyc with rfl | hyc
  · omega
  · have := hyc (fun _ => 0)
    omega

theorem quasiDecreasingnessReducedOrder_rejects :
    ¬ quasiDecreasingnessAccepts quasiDecreasingnessReducedOrder := by
  intro hA
  have hstep := hA.1 quasiDecreasingnessPoint (fw fz (fr fz fz fz))
    ((cStep_ofTRS_iff freeRecursorTRS _ _).2 (step_succ fz fz fz))
  rw [quasiDecreasingnessReducedOrder_apply, if_pos rfl] at hstep
  exact quasiDecreasingnessRow_not_contractum hstep

def quasiDecreasingnessNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Replacing the successor set of the redex `recur(zero, zero, succ zero)` in the witness order by
its proper subterms and everything below them keeps well-foundedness and `≻ = (≻ ∪ ▷)⁺`, and
loses the successor step of that redex. -/
def quasiDecreasingnessNecessityStatement : Prop :=
  EscapeFeatureNecessity quasiDecreasingnessLaws quasiDecreasingnessAccepts
    quasiDecreasingnessPointLens

theorem quasiDecreasingness_necessity : quasiDecreasingnessNecessityStatement := by
  have hgt : algGt cpAlg quasiDecreasingnessPoint (fw fz (fr fz fz fz)) := by
    intro β
    simp [quasiDecreasingnessPoint, cpAlg, fw, fr, fs, fz]
  exact ⟨{ base := quasiDecreasingnessWitness
           baseLaws := quasiDecreasingnessWitness_laws
           baseAccepts := quasiDecreasingnessWitness_accepts
           value := quasiDecreasingnessRow
           valueDiffers := fun h =>
             quasiDecreasingnessRow_not_contractum (cast (congrFun h _).symm hgt)
           changedLaws := quasiDecreasingnessReducedOrder_laws
           changedRejects := quasiDecreasingnessReducedOrder_rejects }⟩

/-! ### Row: matchBounds -/

/-- The retained clause of `matchBoundsLaws`: source soundness. -/
def matchBoundsOtherLaws (M : matchBoundsData) : Prop :=
  ∀ {s t : FreeTerm Nat}, M.sys s t → M.raised (M.raiseT s) (M.raiseT t)

/-- The deleted clause: every raised transition consumes one height unit. -/
def matchBoundsDeletedLaw (M : matchBoundsData) : Prop :=
  ∀ {a b : RaisedTerm Nat}, M.raised a b → M.height b + 1 ≤ M.height a

/-- The witness with the raised height set to zero. -/
def matchBoundsCountermodel : matchBoundsData := { matchBoundsWitness with height := fun _ => 0 }

def matchBoundsNecessityKind : RowNecessityKind := .deletedBarrierPremise

/-- Without transition decrease, the witness with height zero keeps source soundness, covers the
free contextual steps and closes the linear bound with constant zero. -/
def matchBoundsNecessityStatement : Prop :=
  BarrierPremiseNecessity matchBoundsLaws matchBoundsOtherLaws matchBoundsDeletedLaw
    matchBoundsAccepts

theorem matchBounds_necessity : matchBoundsNecessityStatement :=
  ⟨fun _ => Iff.rfl, matchBounds_universal,
    ⟨{ datum := matchBoundsCountermodel
       other := matchBoundsWitness_laws.1
       deletedFails := fun hdec => matchBounds_mutation ⟨matchBoundsWitness_laws.1, hdec⟩
       accepts := ⟨fun _ _ => Iff.rfl, fun _ => Nat.zero_le _⟩ }⟩⟩

/-! ### Row: raiseConsistencyMatchBounds -/

/-- The source system of a raise-consistency datum. -/
def raiseConsistencyMatchBoundsSysLens :
    FeatureLens raiseConsistencyMatchBoundsData (FreeTerm Nat → FreeTerm Nat → Prop) where
  get M := M.sys
  set M w := { M with sys := w }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

theorem raiseConsistencyMatchBoundsEmptySys_rejects :
    ¬ raiseConsistencyMatchBoundsAccepts
      (raiseConsistencyMatchBoundsSysLens.set raiseConsistencyMatchBoundsWitness
        (fun _ _ => False)) :=
  fun hA => (hA (.recur .zero .zero (.succ .zero)) (.wrap .zero (.recur .zero .zero .zero))).mpr
    (rootStep_contextStep (.recurSucc .zero .zero .zero))

def raiseConsistencyMatchBoundsNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Replacing the source system of the witness by the empty system keeps the three laws, which it
satisfies vacuously or through the unchanged raised system, and loses the adapter to the free
contextual steps. -/
def raiseConsistencyMatchBoundsNecessityStatement : Prop :=
  EscapeFeatureNecessity raiseConsistencyMatchBoundsLaws raiseConsistencyMatchBoundsAccepts
    raiseConsistencyMatchBoundsSysLens

theorem raiseConsistencyMatchBounds_necessity :
    raiseConsistencyMatchBoundsNecessityStatement :=
  ⟨{ base := raiseConsistencyMatchBoundsWitness
     baseLaws := raiseConsistencyMatchBoundsWitness_laws
     baseAccepts := fun _ _ => Iff.rfl
     value := fun _ _ => False
     valueDiffers := fun h => raiseConsistencyMatchBoundsEmptySys_rejects ((congrArg
       (fun w : FreeTerm Nat → FreeTerm Nat → Prop => raiseConsistencyMatchBoundsAccepts
         (raiseConsistencyMatchBoundsSysLens.set raiseConsistencyMatchBoundsWitness w)) h).mpr
       (fun _ _ => Iff.rfl))
     changedLaws := ⟨fun h => False.elim h, raiseConsistencyMatchBoundsWitness_laws.2.1,
       fun h => False.elim h⟩
     changedRejects := raiseConsistencyMatchBoundsEmptySys_rejects }⟩

/-! ### Row: leftLinearMatchBounds -/

/-- The retained clauses of `leftLinearMatchBoundsLaws`: left-linearity and source soundness. -/
def leftLinearMatchBoundsOtherLaws (M : leftLinearMatchBoundsData) : Prop :=
  (freeVars M.lhs).Nodup ∧ ∀ {s t : FreeTerm Nat}, M.sys s t → M.raised (M.raiseT s) (M.raiseT t)

/-- The deleted clause: every raised transition consumes one height unit. -/
def leftLinearMatchBoundsDeletedLaw (M : leftLinearMatchBoundsData) : Prop :=
  ∀ {a b : RaisedTerm Nat}, M.raised a b → M.height b + 1 ≤ M.height a

/-- The witness with the raised height set to zero. -/
def leftLinearMatchBoundsCountermodel : leftLinearMatchBoundsData :=
  { leftLinearMatchBoundsWitness with height := fun _ => 0 }

def leftLinearMatchBoundsNecessityKind : RowNecessityKind := .deletedBarrierPremise

/-- Without transition decrease, the witness with height zero keeps the left-linear left-hand side
and source soundness, covers the free contextual steps and closes the linear bound with constant
zero. -/
def leftLinearMatchBoundsNecessityStatement : Prop :=
  BarrierPremiseNecessity leftLinearMatchBoundsLaws leftLinearMatchBoundsOtherLaws
    leftLinearMatchBoundsDeletedLaw leftLinearMatchBoundsAccepts

theorem leftLinearMatchBounds_necessity : leftLinearMatchBoundsNecessityStatement :=
  ⟨fun _ => and_assoc.symm, leftLinearMatchBounds_universal,
    ⟨{ datum := leftLinearMatchBoundsCountermodel
       other := ⟨leftLinearMatchBoundsWitness_laws.1, leftLinearMatchBoundsWitness_laws.2.1⟩
       deletedFails := fun hdec => by
         have h0 : (0 : Nat) + 1 ≤ 0 :=
           hdec (leftLinearMatchBoundsWitness_laws.2.1
             (rootStep_contextStep (.recurSucc .zero .zero .zero)))
         omega
       accepts := ⟨fun _ _ => Iff.rfl, fun _ => Nat.zero_le _⟩ }⟩⟩

/-! ### Row: predictiveLabeling -/

/-- The source system of a predictive-labelling datum. -/
def predictiveLabelingSysLens :
    FeatureLens predictiveLabelingData (FreeTerm Nat → FreeTerm Nat → Prop) where
  get M := M.sys
  set M w := { M with sys := w }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

theorem predictiveLabelingEmptySys_rejects :
    ¬ predictiveLabelingAccepts
      (predictiveLabelingSysLens.set predictiveLabelingWitness (fun _ _ => False)) :=
  fun hA => (hA (.recur .zero .zero (.succ .zero)) (.wrap .zero (.recur .zero .zero .zero))).mpr
    (rootStep_contextStep (.recurSucc .zero .zero .zero))

def predictiveLabelingNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Replacing the source system of the witness by the empty system keeps prediction consistency,
source soundness and the labelled height drop, and loses the adapter to the free contextual
steps. -/
def predictiveLabelingNecessityStatement : Prop :=
  EscapeFeatureNecessity predictiveLabelingLaws predictiveLabelingAccepts predictiveLabelingSysLens

theorem predictiveLabeling_necessity : predictiveLabelingNecessityStatement :=
  ⟨{ base := predictiveLabelingWitness
     baseLaws := predictiveLabelingWitness_laws
     baseAccepts := fun _ _ => Iff.rfl
     value := fun _ _ => False
     valueDiffers := fun h => predictiveLabelingEmptySys_rejects ((congrArg
       (fun w : FreeTerm Nat → FreeTerm Nat → Prop => predictiveLabelingAccepts
         (predictiveLabelingSysLens.set predictiveLabelingWitness w)) h).mpr (fun _ _ => Iff.rfl))
     changedLaws := ⟨predictiveLabelingWitness_laws.1, fun h => False.elim h,
       predictiveLabelingWitness_laws.2.2⟩
     changedRejects := predictiveLabelingEmptySys_rejects }⟩

/-! ### Row: forwardClosures -/

/-- The deleted clause: the certified right-hand side is right-linear. -/
def forwardClosuresDeletedLaw (M : forwardClosuresData) : Prop :=
  (freeVars M.rhs).Nodup

/-- The retained clauses of `forwardClosuresLaws`. -/
def forwardClosuresOtherLaws (M : forwardClosuresData) : Prop :=
  (∀ {s t : FreeTerm Nat}, M.sys s t → ContextStep s t) ∧
    (∀ σ : Nat → FreeTerm Nat, M.closure (FreeTerm.subst σ M.rhs)) ∧
    (∀ {s t : FreeTerm Nat}, M.sys s t → M.closure s → M.closure t)

/-- The witness with the duplicating right-hand side certified. -/
def forwardClosuresCountermodel : forwardClosuresData :=
  { forwardClosuresWitness with rhs := schemaRhsSucc }

def forwardClosuresNecessityKind : RowNecessityKind := .deletedBarrierPremise

/-- Without right-linearity, the witness with the duplicating right-hand side keeps the other
closure clauses and is accepted. -/
def forwardClosuresNecessityStatement : Prop :=
  BarrierPremiseNecessity forwardClosuresLaws forwardClosuresOtherLaws forwardClosuresDeletedLaw
    forwardClosuresAccepts

theorem forwardClosures_necessity : forwardClosuresNecessityStatement :=
  ⟨fun _ => and_comm, forwardClosures_universal,
    ⟨{ datum := forwardClosuresCountermodel
       other := ⟨fun h => h, fun _ => trivial, fun _ _ => trivial⟩
       deletedFails := fun h => absurd h (by decide : ¬ (freeVars schemaRhsSucc).Nodup)
       accepts := ⟨rfl, fun _ _ => Iff.rfl⟩ }⟩⟩

end LabelingBoundsRows

/-! ## Context-sensitive, many-sorted and order-sorted rows -/

section SortedConstrainedRows

open OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained

/-! ### Row: contextSensitiveDP -/

/-- The active positions of `recur` in a replacement map. -/
def contextSensitiveDPRecurLens : FeatureLens contextSensitiveDPData (Nat → Bool) :=
  pointLens FreeSym.recur

/-- Blocking the counter position of `recur` is a change of the `recur` positions only. -/
theorem contextSensitiveDPRecurLens_set_blocked :
    contextSensitiveDPRecurLens.set contextSensitiveDPWitness
        (fun i => if i = 2 then false else contextSensitiveDPWitness FreeSym.recur i) =
      contextSensitiveDPMutant := by
  funext f i
  cases f <;>
    simp [contextSensitiveDPRecurLens, pointLens, contextSensitiveDPMutant]

def contextSensitiveDPNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Blocking the counter position of `recur` in the witness map keeps the replacement-map and
conservativeness laws and loses the context-sensitive subterm criterion. -/
def contextSensitiveDPNecessityStatement : Prop :=
  EscapeFeatureNecessity contextSensitiveDPLaws contextSensitiveDPAccepts
    contextSensitiveDPRecurLens

theorem contextSensitiveDP_necessity : contextSensitiveDPNecessityStatement :=
  ⟨{ base := contextSensitiveDPWitness
     baseLaws := contextSensitiveDPWitness_laws
     baseAccepts := ⟨muProj, contextSensitiveDPWitness_accepts⟩
     value := fun i => if i = 2 then false else contextSensitiveDPWitness FreeSym.recur i
     valueDiffers := fun h => absurd (congrFun h 2) (by decide)
     changedLaws := by
       rw [contextSensitiveDPRecurLens_set_blocked]
       exact contextSensitiveDP_mutation.1
     changedRejects := by
       rw [contextSensitiveDPRecurLens_set_blocked]
       exact contextSensitiveDP_mutation.2 }⟩

/-! ### Row: typeIntroduction -/

theorem typeIntroduction_zeroRule_not_duplicating : ∀ rule ∈ [zeroRule], ¬ IsDuplicating rule := by
  intro rule hrule ⟨x, hx⟩
  simp only [List.mem_singleton] at hrule
  subst hrule
  by_cases h0 : x = 0
  · subst h0
    simp [zeroRule, occ, occList] at hx
  · simp [zeroRule, occ, occList, Ne.symm h0] at hx

theorem typeIntroduction_zeroRule_size_lt {t u : Term FreeSym Nat} (h : Step [zeroRule] t u) :
    Term.size u < Term.size t := by
  induction h with
  | root h =>
    obtain ⟨rule, hrule, σ, rfl, rfl⟩ := h
    simp only [List.mem_singleton] at hrule
    subst hrule
    simp only [zeroRule, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
      Subst.apply_var, Term.size_app, Term.sizeList_cons, Term.sizeList_nil]
    omega
  | arg sym pre post _ ih =>
    simp only [Term.size_app, sizeList_append, Term.sizeList_cons]
    omega

theorem typeIntroduction_zeroRule_sn (t : Term FreeSym Nat) : SN [zeroRule] t :=
  (Subrelation.wf (fun {_ _} h => typeIntroduction_zeroRule_size_lt h)
    (InvImage.wf Term.size Nat.lt_wfRel.wf)).apply t

/-- Nonduplicating control. For every lawful attachment, the zero rule `recur(b, s, zero) → b`
alone, which duplicates no variable, meets Zantema's side condition and its sorted system
terminates: both objects of `typeIntroductionAccepts` hold for it. -/
def typeIntroductionNonduplicatingControl : Prop :=
  ∀ A, typeIntroductionLaws A →
    ZantemaCondition [zeroRule] ∧ SortedTerminates fArity A [zeroRule]

theorem typeIntroductionNonduplicatingControl_holds : typeIntroductionNonduplicatingControl :=
  fun _ _ => ⟨Or.inr typeIntroduction_zeroRule_not_duplicating,
    fun t _ _ => Subrelation.accessible (fun h => h.2) (typeIntroduction_zeroRule_sn t)⟩

def typeIntroductionNecessityKind : RowNecessityKind := .lawFreeBarrierControl

/-- Type introduction rejects the free recursor at every attachment, lawful or not, because the
zero rule collapses and the successor rule duplicates. -/
def typeIntroductionNecessityStatement : Prop :=
  UniversalBarrierNecessity typeIntroductionLaws typeIntroductionAccepts
    typeIntroductionNonduplicatingControl

theorem typeIntroduction_necessity : typeIntroductionNecessityStatement :=
  ⟨⟨typeIntroductionWitness, typeIntroductionWitness_laws⟩,
    fun _ hA => freeRecursor_not_zantema hA.1, typeIntroductionNonduplicatingControl_holds⟩

/-! ### Row: manySortedPersistence -/

/-- Every attachment accepts: the free recursor terminates, so its sorted system terminates. -/
theorem manySortedPersistence_accepts_all (M : manySortedPersistenceData) :
    manySortedPersistenceAccepts M :=
  fun t _ _ => Subrelation.accessible (fun h => h.2) (freeRecursor_terminates_via_manySorted t)

def manySortedPersistenceNecessityKind : RowNecessityKind := .noApplicableHypothesis

/-- Sorted termination holds at every datum, so the laws fix the verdict. -/
def manySortedPersistenceNecessityStatement : Prop :=
  NoApplicableHypothesis manySortedPersistenceLaws manySortedPersistenceAccepts
    .lawsDetermineVerdict

theorem manySortedPersistence_necessity : manySortedPersistenceNecessityStatement :=
  ⟨⟨manySortedPersistenceWitness, manySortedPersistenceWitness_laws⟩, fun M M' _ _ =>
    iff_of_true (manySortedPersistence_accepts_all M) (manySortedPersistence_accepts_all M')⟩

/-- No feature change of a lawful datum separates acceptance from rejection. -/
theorem manySortedPersistence_no_feature_control {V : Sort v}
    (L : FeatureLens manySortedPersistenceData V) :
    ¬ EscapeFeatureNecessity manySortedPersistenceLaws manySortedPersistenceAccepts L :=
  NoApplicableHypothesis.no_feature_control manySortedPersistence_necessity L

/-! ### Row: orderSortedDP -/

def orderSortedDPNecessityKind : RowNecessityKind := .noApplicableHypothesis

/-- The counter projection meets the subterm criterion at every order-sorted signature, so the
laws fix the verdict. -/
def orderSortedDPNecessityStatement : Prop :=
  NoApplicableHypothesis orderSortedDPLaws orderSortedDPAccepts .lawsDetermineVerdict

theorem orderSortedDP_necessity : orderSortedDPNecessityStatement :=
  ⟨⟨orderSortedDPWitness, orderSortedDPWitness_laws⟩, fun M M' _ _ =>
    iff_of_true ⟨muProj, free_os_criterion M⟩ ⟨muProj, free_os_criterion M'⟩⟩

/-- No feature change of a lawful signature separates acceptance from rejection. -/
theorem orderSortedDP_no_feature_control {V : Sort v} (L : FeatureLens orderSortedDPData V) :
    ¬ EscapeFeatureNecessity orderSortedDPLaws orderSortedDPAccepts L :=
  NoApplicableHypothesis.no_feature_control orderSortedDP_necessity L

end SortedConstrainedRows

end OperatorKO7.Methods.OrientationClosure.HypothesisNecessity
