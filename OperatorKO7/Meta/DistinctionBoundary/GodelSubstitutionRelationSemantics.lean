import OperatorKO7.Meta.DistinctionBoundary.GodelProofRelationSemantics

set_option autoImplicit false

/-!
# Standard-model semantics of the coded substitution relation

`substRel` is kept unchanged.  This module proves soundness of its beta-coded
formula-substitution trace on arbitrary raw codes and completeness on canonical
formula encodings, then packages the canonical graph used by the diagonal
sentence.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

private theorem termSubstGraph_sound (y inC outC : Nat)
    (h : TermSubstGraph (numCode y) inC outC) :
    outC = substTermCode y inC := by
  rcases h with ⟨c, d, L, hlast, htrace⟩
  exact termSubstTrace_entry_sound y c d L (numCode y) rfl htrace
    L (Nat.le_refl L) inC outC hlast.symm

/-- Numeric beta trace for the existing `formSubstClosed` graph. -/
def FormSubstTrace (c d L ncode : Nat) : Prop :=
  ∀ i, i ≤ L → ∃ inC outC,
    ccons inC outC = beta c d i ∧ FormSubstJustNat c d i ncode inC outC

/-- Every accepted formula-substitution trace computes the live raw-code substitution function. -/
theorem formSubstTrace_entry_sound (y c d L : Nat)
    (htrace : FormSubstTrace c d L (numCode y)) :
    ∀ i, i ≤ L → ∀ inC outC,
      beta c d i = ccons inC outC → outC = substFormCode y inC := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
      intro hi inC outC hentry
      rcases htrace i hi with ⟨inC', outC', hentry', hjust⟩
      have hp : inC = inC' ∧ outC = outC' :=
        ccons_injective (hentry.symm.trans hentry'.symm)
      rcases hp with ⟨rfl, rfl⟩
      rcases hjust with heq | hnot | himp | hall
      · rcases heq with ⟨a, b, a', b', hin, hout, ha, hb⟩
        have ha' := termSubstGraph_sound y a a' ha
        have hb' := termSubstGraph_sound y b b' hb
        rw [hin, hout, substFormCode_eq, ha', hb']
      · rcases hnot with ⟨a, a', j, hin, hout, hj, hβ⟩
        have hjL : j ≤ L := Nat.le_trans (Nat.le_of_lt hj) hi
        have hchild : a' = substFormCode y a := ih j hj hjL a a' hβ.symm
        rw [hin, hout, substFormCode_not, hchild]
      · rcases himp with ⟨a, b, a', b', j, k, hin, hout, hj, hk, hβj, hβk⟩
        have hjL : j ≤ L := Nat.le_trans (Nat.le_of_lt hj) hi
        have hkL : k ≤ L := Nat.le_trans (Nat.le_of_lt hk) hi
        have ha' : a' = substFormCode y a := ih j hj hjL a a' hβj.symm
        have hb' : b' = substFormCode y b := ih k hk hkL b b' hβk.symm
        rw [hin, hout, substFormCode_imp, ha', hb']
      · rcases hall with ⟨x, a, a', j, hin, hcases⟩
        rcases hcases with hzero | hpos
        · rcases hzero with ⟨hx, hout⟩
          subst x
          rw [hout, hin, substFormCode_all_zero]
        · rcases hpos with ⟨hx, hout, hj, hβ⟩
          obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hx
          have hjL : j ≤ L := Nat.le_trans (Nat.le_of_lt hj) hi
          have hchild : a' = substFormCode y a := ih j hj hjL a a' hβ.symm
          rw [hin, hout, substFormCode_all_pos, hchild]

private theorem eval_formSubstClosed_var210 (env : Nat → Nat)
    (x z : Nat) :
    evalForm env (formSubstClosed (numeral x) (numeral z) (Term.var 210)) ↔
      ∃ c d L, ccons x z = beta c d L ∧ FormSubstTrace c d L (env 210) := by
  simp [formSubstClosed, FormSubstTrace, eval_existsF, eval_andF,
    evalForm_all, evalForm_imp, eval_leF_var_var, eval_betaF_vars_ccons,
    eval_betaF_vars_ccons_numerals, eval_formSubstJust_tableVars,
    evalTerm, evalTerm_numeral]

private def FormChildrenBefore (xs : List Formula) (i : Nat) : Formula → Prop
  | Formula.eq _ _ => True
  | Formula.not a => ∃ j, j < i ∧ xs[j]? = some a
  | Formula.imp a b =>
      ∃ j k, j < i ∧ k < i ∧ xs[j]? = some a ∧ xs[k]? = some b
  | Formula.all _ a => ∃ j, j < i ∧ xs[j]? = some a

private def FormPostorderOK (xs : List Formula) : Prop :=
  ∀ i a, xs[i]? = some a → FormChildrenBefore xs i a

private theorem formChildrenBefore_append_left {xs ys : List Formula}
    {i : Nat} {a : Formula} (hi : i < xs.length)
    (h : FormChildrenBefore xs i a) : FormChildrenBefore (xs ++ ys) i a := by
  cases a with
  | eq _ _ => trivial
  | not b =>
      rcases h with ⟨j, hj, hb⟩
      refine ⟨j, hj, ?_⟩
      rw [List.getElem?_append_left (Nat.lt_trans hj hi)]
      exact hb
  | imp b c =>
      rcases h with ⟨j, k, hj, hk, hb, hc⟩
      refine ⟨j, k, hj, hk, ?_, ?_⟩
      · rw [List.getElem?_append_left (Nat.lt_trans hj hi)]
        exact hb
      · rw [List.getElem?_append_left (Nat.lt_trans hk hi)]
        exact hc
  | all _ b =>
      rcases h with ⟨j, hj, hb⟩
      refine ⟨j, hj, ?_⟩
      rw [List.getElem?_append_left (Nat.lt_trans hj hi)]
      exact hb

private theorem formChildrenBefore_append_right {xs ys : List Formula}
    {i : Nat} {a : Formula} (h : FormChildrenBefore ys i a) :
    FormChildrenBefore (xs ++ ys) (xs.length + i) a := by
  cases a with
  | eq _ _ => trivial
  | not b =>
      rcases h with ⟨j, hj, hb⟩
      refine ⟨xs.length + j, by omega, ?_⟩
      rw [List.getElem?_append_right (Nat.le_add_right _ _)]
      simpa using hb
  | imp b c =>
      rcases h with ⟨j, k, hj, hk, hb, hc⟩
      refine ⟨xs.length + j, xs.length + k, by omega, by omega, ?_, ?_⟩
      · rw [List.getElem?_append_right (Nat.le_add_right _ _)]
        simpa using hb
      · rw [List.getElem?_append_right (Nat.le_add_right _ _)]
        simpa using hc
  | all _ b =>
      rcases h with ⟨j, hj, hb⟩
      refine ⟨xs.length + j, by omega, ?_⟩
      rw [List.getElem?_append_right (Nat.le_add_right _ _)]
      simpa using hb

private theorem formPostorderOK_nil : FormPostorderOK [] := by
  intro i a h
  simp at h

private theorem formPostorderOK_append {xs ys : List Formula}
    (hx : FormPostorderOK xs) (hy : FormPostorderOK ys) :
    FormPostorderOK (xs ++ ys) := by
  intro i a hia
  rcases getElem?_append_cases hia with hleft | hright
  · exact formChildrenBefore_append_left hleft.1 (hx i a hleft.2)
  · rcases hright with ⟨hi, hia'⟩
    have hs := formChildrenBefore_append_right (xs := xs) (hy (i - xs.length) a hia')
    have heq : xs.length + (i - xs.length) = i := Nat.add_sub_of_le hi
    simpa [heq] using hs

private theorem formPostorderOK_snoc {xs : List Formula} {a : Formula}
    (hx : FormPostorderOK xs)
    (hroot : FormChildrenBefore (xs ++ [a]) xs.length a) :
    FormPostorderOK (xs ++ [a]) := by
  intro i b hib
  by_cases hi : i < xs.length
  · have hpre : xs[i]? = some b := by
      rw [← List.getElem?_append_left hi]
      exact hib
    exact formChildrenBefore_append_left hi (hx i b hpre)
  · have hlen : i = xs.length := by
      have hlt := getElem?_some_lt hib
      simp [List.length_append] at hlt
      omega
    subst hlen
    have hba : b = a := by
      have ha : (xs ++ [a])[xs.length]? = some a := by simp
      exact Option.some.inj (hib.symm.trans ha)
    subst hba
    exact hroot

private theorem formPostorder_ok : ∀ a : Formula, FormPostorderOK (formPostorder a)
  | Formula.eq _ _ => formPostorderOK_snoc formPostorderOK_nil trivial
  | Formula.not a => by
      apply formPostorderOK_snoc (formPostorder_ok a)
      have hne := formPostorder_ne_nil a
      refine ⟨(formPostorder a).length - 1,
        Nat.pred_lt (List.length_pos_iff.mpr hne).ne', ?_⟩
      have hidx : (formPostorder a).length - 1 < (formPostorder a).length :=
        Nat.pred_lt (List.length_pos_iff.mpr hne).ne'
      rw [List.getElem?_append_left hidx]
      exact getLast?_some_getElem? (formPostorder_getLast a) hne
  | Formula.imp a b => by
      apply formPostorderOK_snoc
        (formPostorderOK_append (formPostorder_ok a) (formPostorder_ok b))
      have ha := formPostorder_ne_nil a
      have hb := formPostorder_ne_nil b
      have hapos : 0 < (formPostorder a).length := List.length_pos_iff.mpr ha
      have hbpos : 0 < (formPostorder b).length := List.length_pos_iff.mpr hb
      refine ⟨(formPostorder a).length - 1,
        (formPostorder a).length + ((formPostorder b).length - 1), ?_, ?_, ?_, ?_⟩
      · simp [List.length_append]
        omega
      · simp [List.length_append]
        omega
      · have hjouter : (formPostorder a).length - 1 <
            (formPostorder a ++ formPostorder b).length := by
          simp [List.length_append]
          omega
        have houter := List.getElem?_append_left
          (l₂ := [Formula.imp a b]) hjouter
        have hinner := List.getElem?_append_left
          (l₂ := formPostorder b) (Nat.pred_lt hapos.ne')
        exact houter.trans (hinner.trans
          (getLast?_some_getElem? (formPostorder_getLast a) ha))
      · have hkouter : (formPostorder a).length + ((formPostorder b).length - 1) <
            (formPostorder a ++ formPostorder b).length := by
          simp [List.length_append]
          omega
        have houter := List.getElem?_append_left
          (l₂ := [Formula.imp a b]) hkouter
        have hinner := List.getElem?_append_right
          (l₁ := formPostorder a) (l₂ := formPostorder b)
          (i := (formPostorder a).length + ((formPostorder b).length - 1))
          (Nat.le_add_right _ _)
        exact houter.trans (hinner.trans (by
          simpa using getLast?_some_getElem? (formPostorder_getLast b) hb))
  | Formula.all _ a => by
      apply formPostorderOK_snoc (formPostorder_ok a)
      have hne := formPostorder_ne_nil a
      refine ⟨(formPostorder a).length - 1,
        Nat.pred_lt (List.length_pos_iff.mpr hne).ne', ?_⟩
      have hidx : (formPostorder a).length - 1 < (formPostorder a).length :=
        Nat.pred_lt (List.length_pos_iff.mpr hne).ne'
      rw [List.getElem?_append_left hidx]
      exact getLast?_some_getElem? (formPostorder_getLast a) hne

private theorem termSubstGraph_complete (y : Nat) (t : Term) :
    TermSubstGraph (numCode y) (encodeTerm t) (substTermCode y (encodeTerm t)) :=
  termSubstTrace_complete y t

private def formTable (y : Nat) (root : Formula) (i : Nat) : Nat :=
  match (formPostorder root)[i]? with
  | some a => formPair y a
  | none => 0

private theorem formTable_entry_local (y : Nat) (root node : Formula)
    (c d L i : Nat) (hi : i ≤ L)
    (hnode : (formPostorder root)[i]? = some node)
    (hpack : ∀ j, j ≤ L → beta c d j = formTable y root j) :
    FormSubstJustNat c d i (numCode y) (encodeFormula node)
      (substFormCode y (encodeFormula node)) := by
  have hchildren := formPostorder_ok root i node hnode
  cases node with
  | eq s t =>
      refine Or.inl ⟨encodeTerm s, encodeTerm t,
        substTermCode y (encodeTerm s), substTermCode y (encodeTerm t),
        rfl, substFormCode_eq y (encodeTerm s) (encodeTerm t),
        termSubstGraph_complete y s, termSubstGraph_complete y t⟩
  | not a =>
      rcases hchildren with ⟨j, hj, hja⟩
      refine Or.inr (Or.inl ⟨encodeFormula a, substFormCode y (encodeFormula a), j,
        rfl, substFormCode_not y (encodeFormula a), hj, ?_⟩)
      have hβ := hpack j (Nat.le_trans (Nat.le_of_lt hj) hi)
      simp only [formTable, hja, formPair] at hβ
      exact hβ.symm
  | imp a b =>
      rcases hchildren with ⟨j, k, hj, hk, hja, hkb⟩
      refine Or.inr (Or.inr (Or.inl ⟨encodeFormula a, encodeFormula b,
        substFormCode y (encodeFormula a), substFormCode y (encodeFormula b), j, k,
        rfl, substFormCode_imp y (encodeFormula a) (encodeFormula b), hj, hk, ?_, ?_⟩))
      · have hβ := hpack j (Nat.le_trans (Nat.le_of_lt hj) hi)
        simp only [formTable, hja, formPair] at hβ
        exact hβ.symm
      · have hβ := hpack k (Nat.le_trans (Nat.le_of_lt hk) hi)
        simp only [formTable, hkb, formPair] at hβ
        exact hβ.symm
  | all x a =>
      rcases hchildren with ⟨j, hj, hja⟩
      refine Or.inr (Or.inr (Or.inr ⟨x, encodeFormula a,
        substFormCode y (encodeFormula a), j, rfl, ?_⟩))
      cases x with
      | zero =>
          exact Or.inl ⟨rfl, by simp [substFormCode_all_zero, encodeFormula]⟩
      | succ q =>
          refine Or.inr ⟨Nat.succ_ne_zero q, ?_, hj, ?_⟩
          · exact substFormCode_all_pos y q (encodeFormula a)
          · have hβ := hpack j (Nat.le_trans (Nat.le_of_lt hj) hi)
            simp only [formTable, hja, formPair] at hβ
            exact hβ.symm

/-- Every canonical formula encoding has a complete beta-coded substitution trace. -/
theorem formSubstTrace_complete (y : Nat) (φ : Formula) :
    ∃ c d L,
      ccons (encodeFormula φ) (substFormCode y (encodeFormula φ)) = beta c d L ∧
        FormSubstTrace c d L (numCode y) := by
  let L := (formPostorder φ).length - 1
  obtain ⟨c, d, hpack⟩ := beta_exists L (formTable y φ)
  refine ⟨c, d, L, ?_, ?_⟩
  · have hne := formPostorder_ne_nil φ
    have hroot : (formPostorder φ)[L]? = some φ := by
      dsimp [L]
      exact getLast?_some_getElem? (formPostorder_getLast φ) hne
    have hβ := hpack L (Nat.le_refl L)
    simp only [formTable, hroot, formPair] at hβ
    exact hβ.symm
  · intro i hi
    have hilt : i < (formPostorder φ).length := by
      dsimp [L] at hi
      have hpos : 0 < (formPostorder φ).length :=
        List.length_pos_iff.mpr (formPostorder_ne_nil φ)
      omega
    let node : Formula := (formPostorder φ)[i]
    have hnode : (formPostorder φ)[i]? = some node := by
      simpa [node] using List.getElem?_eq_getElem hilt
    refine ⟨encodeFormula node, substFormCode y (encodeFormula node), ?_, ?_⟩
    · have hβ := hpack i hi
      simp only [formTable, hnode, formPair] at hβ
      exact hβ.symm
    · exact formTable_entry_local y φ node c d L i hi hnode hpack

private theorem eval_termSubstClosed_vars_241_243_numeral (env : Nat → Nat) (ncode : Nat) :
    evalForm env (termSubstClosed (Term.var 241) (Term.var 243) (numeral ncode)) ↔
      TermSubstGraph ncode (env 241) (env 243) := by
  simp [termSubstClosed, TermSubstGraph, TermSubstTrace, eval_existsF,
    eval_andF, evalForm_all, evalForm_imp, eval_leF_var_var,
    eval_betaF_vars_ccons, eval_termSubstJust_tableVars]

private theorem eval_termSubstClosed_vars_242_244_numeral (env : Nat → Nat) (ncode : Nat) :
    evalForm env (termSubstClosed (Term.var 242) (Term.var 244) (numeral ncode)) ↔
      TermSubstGraph ncode (env 242) (env 244) := by
  simp [termSubstClosed, TermSubstGraph, TermSubstTrace, eval_existsF,
    eval_andF, evalForm_all, evalForm_imp, eval_leF_var_var,
    eval_betaF_vars_ccons, eval_termSubstJust_tableVars]

private theorem eval_formSubstJust_tableVars_numeral (env : Nat → Nat) (ncode : Nat) :
    evalForm env (formSubstJust (Term.var 250) (Term.var 251) (Term.var 253)
      (numeral ncode) (Term.var 254) (Term.var 255)) ↔
      FormSubstJustNat (env 250) (env 251) (env 253) ncode
        (env 254) (env 255) := by
  simp [formSubstJust, FormSubstJustNat, formSubstEqCase,
    formSubstNotCase, formSubstImpCase, formSubstAllCase,
    eval_existsF, eval_andF, eval_orF, eval_eqCcons, eval_cconsTerm,
    eval_ltF_var_var, eval_betaF_vars_ccons,
    eval_termSubstClosed_vars_241_243_numeral,
    eval_termSubstClosed_vars_242_244_numeral,
    evalForm, evalTerm, evalTerm_numeral]

private theorem eval_formSubstClosed_numerals (env : Nat → Nat)
    (x z ncode : Nat) :
    evalForm env (formSubstClosed (numeral x) (numeral z) (numeral ncode)) ↔
      ∃ c d L, ccons x z = beta c d L ∧ FormSubstTrace c d L ncode := by
  simp [formSubstClosed, FormSubstTrace, eval_existsF, eval_andF,
    evalForm_all, evalForm_imp, eval_leF_var_var, eval_betaF_vars_ccons,
    eval_betaF_vars_ccons_numerals, eval_formSubstJust_tableVars_numeral]

/-- Soundness of the object-language formula substitution table on raw input codes. -/
theorem formSubstClosed_sound (env : Nat → Nat) (y x z : Nat)
    (h : evalForm env
      (formSubstClosed (numeral x) (numeral z) (numeral (numCode y)))) :
    z = substFormCode y x := by
  rcases (eval_formSubstClosed_numerals env x z (numCode y)).1 h with
    ⟨c, d, L, hlast, htrace⟩
  exact formSubstTrace_entry_sound y c d L htrace L (Nat.le_refl L) x z hlast.symm

/-- Completeness of the object-language formula substitution table on canonical formula codes. -/
theorem formSubstClosed_complete (env : Nat → Nat) (y : Nat) (φ : Formula) :
    evalForm env (formSubstClosed (numeral (encodeFormula φ))
      (numeral (substFormCode y (encodeFormula φ))) (numeral (numCode y))) := by
  apply (eval_formSubstClosed_numerals env _ _ _).2
  exact formSubstTrace_complete y φ

/-- `substRel` is the exact standard-model graph of numeral substitution on canonical formula codes. -/
theorem eval_substRel_formulaCode (env : Nat → Nat) (φ : Formula) (y z : Nat) :
    evalForm env (substRel (numeral (formulaCode φ)) (numeral y) (numeral z)) ↔
      z = formulaCode (substNum φ y) := by
  constructor
  · intro h
    unfold substRel at h
    rw [eval_existsF] at h
    rcases h with ⟨ncode, h⟩
    let e : Nat → Nat := fun w => if w = 210 then ncode else env w
    rw [eval_andF] at h
    rcases h with ⟨hnum, hform⟩
    have hvfresh : freshNumCode (Term.var 210) := by
      apply var_freshNumCode
      omega
    have hnumSem := (eval_numCodeRel e (numeral y) (Term.var 210)
      (numeral_freshNumCode y) hvfresh).1 hnum
    have hncode : ncode = numCode y := by
      simpa [e, evalTerm, evalTerm_numeral] using hnumSem
    rcases (eval_formSubstClosed_var210 e (formulaCode φ) z).1 hform with
      ⟨c, d, L, hlast, htrace⟩
    have htrace' : FormSubstTrace c d L (numCode y) := by
      simpa [e, hncode] using htrace
    have hz := formSubstTrace_entry_sound y c d L htrace'
      L (Nat.le_refl L) (formulaCode φ) z hlast.symm
    rw [substFormCode_formulaCode] at hz
    exact hz
  · intro hz
    subst z
    unfold substRel
    rw [eval_existsF]
    refine ⟨numCode y, ?_⟩
    let e : Nat → Nat := fun w => if w = 210 then numCode y else env w
    rw [eval_andF]
    constructor
    · have hvfresh : freshNumCode (Term.var 210) := by
        apply var_freshNumCode
        omega
      apply (eval_numCodeRel e (numeral y) (Term.var 210)
        (numeral_freshNumCode y) hvfresh).2
      simp [e, evalTerm, evalTerm_numeral]
    · apply (eval_formSubstClosed_var210 e
        (formulaCode φ) (formulaCode (substNum φ y))).2
      rcases formSubstTrace_complete y φ with ⟨c, d, L, hlast, htrace⟩
      refine ⟨c, d, L, ?_, ?_⟩
      · simpa [formulaCode_eq, substFormCode_encode] using hlast
      · simpa [e] using htrace

/-- Equivalent graph statement in the executable `codeSubstNat` vocabulary. -/
theorem eval_substRel_codeSubstNat (env : Nat → Nat) (φ : Formula) (y z : Nat) :
    evalForm env (substRel (numeral (formulaCode φ)) (numeral y) (numeral z)) ↔
      z = codeSubstNat (formulaCode φ) y := by
  rw [eval_substRel_formulaCode, codeSubstNat_formulaCode]

/-- Any result admitted by the canonical substitution graph decodes to the substituted formula. -/
theorem substRel_result_decodes {φ : Formula} {y z : Nat}
    (h : evalForm env0
      (substRel (numeral (formulaCode φ)) (numeral y) (numeral z))) :
    decodeFormula? z = some (substNum φ y) := by
  have hz := (eval_substRel_formulaCode env0 φ y z).1 h
  rw [hz]
  exact decodeFormula?_formulaCode (substNum φ y)

/-- Functional uniqueness of canonical substitution outputs. -/
theorem substRel_result_unique {φ : Formula} {y z₁ z₂ : Nat}
    (h₁ : evalForm env0
      (substRel (numeral (formulaCode φ)) (numeral y) (numeral z₁)))
    (h₂ : evalForm env0
      (substRel (numeral (formulaCode φ)) (numeral y) (numeral z₂))) :
    z₁ = z₂ := by
  rw [(eval_substRel_formulaCode env0 φ y z₁).1 h₁,
    (eval_substRel_formulaCode env0 φ y z₂).1 h₂]

/-- The diagonal substitution used by `arithGodelSentence` is admitted by `substRel`. -/
theorem substRel_godel_diagonal :
    evalForm env0 (substRel (numeral godelMatrixCode) (numeral godelMatrixCode)
      (numeral (formulaCode arithGodelSentence))) := by
  have h := (eval_substRel_formulaCode env0 godelMatrix godelMatrixCode
    (formulaCode arithGodelSentence)).2
  simpa [godelMatrixCode, arithGodelSentence] using h rfl
end OperatorKO7.Meta.DistinctionBoundary.GodelArith


namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

private theorem eval_formSubstClosed_var0_var2_var210 (env : Nat → Nat) :
    evalForm env (formSubstClosed (Term.var 0) (Term.var 2) (Term.var 210)) ↔
      ∃ c d L, ccons (env 0) (env 2) = beta c d L ∧
        FormSubstTrace c d L (env 210) := by
  simp [formSubstClosed, FormSubstTrace, eval_existsF, eval_andF,
    evalForm_all, evalForm_imp, eval_leF_var_var, eval_betaF_vars_ccons,
    eval_formSubstJust_tableVars]

private theorem substFormCode_godel_diagonal :
    substFormCode godelMatrixCode godelMatrixCode =
      formulaCode arithGodelSentence := by
  have hinput : godelMatrixCode = encodeFormula godelMatrix :=
    godelMatrixCode_eq.trans (formulaCode_eq godelMatrix)
  calc
    substFormCode godelMatrixCode godelMatrixCode =
        substFormCode godelMatrixCode (encodeFormula godelMatrix) := by rw [hinput]
    _ = encodeFormula (substNum godelMatrix godelMatrixCode) :=
      substFormCode_encode godelMatrixCode godelMatrix
    _ = encodeFormula arithGodelSentence := by
      exact congrArg encodeFormula arithGodel_eq_subst.symm
    _ = formulaCode arithGodelSentence := (formulaCode_eq _).symm

/-- Open diagonal substitution semantics used by the arithmetized Gödel matrix. -/
theorem eval_substRel_godel_open (env : Nat → Nat)
    (h0 : env 0 = godelMatrixCode) :
    evalForm env (substRel (Term.var 0) (Term.var 0) (Term.var 2)) ↔
      env 2 = formulaCode arithGodelSentence := by
  unfold substRel
  rw [eval_existsF]
  constructor
  · rintro ⟨ncode, h⟩
    let e210 : Nat → Nat := fun w => if w = 210 then ncode else env w
    rw [eval_andF] at h
    rcases h with ⟨hnum, hform⟩
    have hvar0 : freshNumCode (Term.var 0) := by
      apply var_freshNumCode
      omega
    have hvar210 : freshNumCode (Term.var 210) := by
      apply var_freshNumCode
      omega
    have hnSem := (eval_numCodeRel e210 (Term.var 0) (Term.var 210) hvar0 hvar210).1 hnum
    have hn : ncode = numCode godelMatrixCode := by
      simpa [e210, evalTerm, h0] using hnSem
    rcases (eval_formSubstClosed_var0_var2_var210 e210).1 hform with
      ⟨c, d, L, hlast, htrace⟩
    have htrace' : FormSubstTrace c d L (numCode godelMatrixCode) := by
      simpa [e210, hn] using htrace
    have hz := formSubstTrace_entry_sound godelMatrixCode c d L htrace'
      L (Nat.le_refl L) (e210 0) (e210 2) hlast.symm
    have hz' : env 2 = substFormCode godelMatrixCode godelMatrixCode := by
      simpa [e210, h0] using hz
    exact hz'.trans substFormCode_godel_diagonal
  · intro hz
    refine ⟨numCode godelMatrixCode, ?_⟩
    let e210 : Nat → Nat := fun w => if w = 210 then numCode godelMatrixCode else env w
    rw [eval_andF]
    constructor
    · have hvar0 : freshNumCode (Term.var 0) := by
        apply var_freshNumCode
        omega
      have hvar210 : freshNumCode (Term.var 210) := by
        apply var_freshNumCode
        omega
      apply (eval_numCodeRel e210 (Term.var 0) (Term.var 210) hvar0 hvar210).2
      simp [e210, evalTerm, h0]
    · apply (eval_formSubstClosed_var0_var2_var210 e210).2
      rcases formSubstTrace_complete godelMatrixCode godelMatrix with
        ⟨c, d, L, hlast, htrace⟩
      refine ⟨c, d, L, ?_, ?_⟩
      · have hinput : encodeFormula godelMatrix = godelMatrixCode :=
          (godelMatrixCode_eq.trans (formulaCode_eq godelMatrix)).symm
        have houtCode :
            substFormCode godelMatrixCode (encodeFormula godelMatrix) =
              formulaCode arithGodelSentence := by
          calc
            substFormCode godelMatrixCode (encodeFormula godelMatrix) =
                encodeFormula (substNum godelMatrix godelMatrixCode) :=
              substFormCode_encode godelMatrixCode godelMatrix
            _ = encodeFormula arithGodelSentence :=
              congrArg encodeFormula arithGodel_eq_subst.symm
            _ = formulaCode arithGodelSentence := (formulaCode_eq _).symm
        have hlast' : ccons godelMatrixCode (formulaCode arithGodelSentence) = beta c d L := by
          rw [← hinput, ← houtCode]
          exact hlast
        have he0 : e210 0 = godelMatrixCode := by simp [e210, h0]
        have he2 : e210 2 = formulaCode arithGodelSentence := by simp [e210, hz]
        calc
          ccons (e210 0) (e210 2) = ccons godelMatrixCode (formulaCode arithGodelSentence) :=
            congrArg₂ ccons he0 he2
          _ = beta c d L := hlast'
      · simpa [e210] using htrace

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
