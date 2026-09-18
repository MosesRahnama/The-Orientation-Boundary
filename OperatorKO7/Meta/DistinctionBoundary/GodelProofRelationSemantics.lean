import OperatorKO7.Meta.DistinctionBoundary.GodelFOEval

set_option autoImplicit false

/-!
# Proof-relation recoding semantics

The live checker and the object-language proof relation use different proof
encodings. This module builds the recoding bridge without changing either
encoding. The recursive `ProofTree` checker remains the source interface;
`proofRel` continues to consume a beta-packed Hilbert sequence.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

open Term

def TermSubstJustAtNat (c d i x u inC outC : Nat) : Prop :=
  (inC = ccons 0 0 ∧ outC = ccons 0 0) ∨
  (∃ a a' j, inC = ccons 1 a ∧ outC = ccons 1 a' ∧ j < i ∧
    ccons a a' = beta c d j) ∨
  (∃ a b a' b' j k,
    inC = ccons 2 (ccons a b) ∧ outC = ccons 2 (ccons a' b') ∧
      j < i ∧ k < i ∧ ccons a a' = beta c d j ∧ ccons b b' = beta c d k) ∨
  (∃ a b a' b' j k,
    inC = ccons 3 (ccons a b) ∧ outC = ccons 3 (ccons a' b') ∧
      j < i ∧ k < i ∧ ccons a a' = beta c d j ∧ ccons b b' = beta c d k) ∨
  ((inC = ccons 4 x ∧ outC = u) ∨
    ((∃ k, inC = ccons 4 k ∧ k ≠ x) ∧ outC = inC))

theorem eval_termSubstJustAt_tableVars (env : Nat → Nat) (x u : Nat) :
    evalForm env (termSubstJustAt (Term.var 290) (Term.var 291) (Term.var 293)
      (numeral x) (numeral u) (Term.var 294) (Term.var 295)) ↔
      TermSubstJustAtNat (env 290) (env 291) (env 293) x u (env 294) (env 295) := by
  simp [termSubstJustAt, TermSubstJustAtNat, termSubstZeroCase,
    termSubstSuccCase, termSubstAddCase, termSubstMulCase, termSubstVarCaseAt,
    eval_existsF, eval_andF, eval_orF, eval_eqCcons, eval_cconsTerm,
    eval_ltF_var_var, eval_betaF_vars_ccons, evalForm, evalTerm, evalTerm_numeral]

def TermSubstTraceAt (c d L x u : Nat) : Prop :=
  ∀ i, i ≤ L → ∃ inC outC,
    ccons inC outC = beta c d i ∧ TermSubstJustAtNat c d i x u inC outC

private theorem eval_termSubstClosedAt_numerals (env : Nat → Nat)
    (inC outC x u : Nat) :
    evalForm env (termSubstClosedAt (numeral inC) (numeral outC)
      (numeral x) (numeral u)) ↔
      ∃ c d L, ccons inC outC = beta c d L ∧ TermSubstTraceAt c d L x u := by
  simp [termSubstClosedAt, TermSubstTraceAt, eval_existsF, eval_andF,
    evalForm_all, evalForm_imp, eval_leF_var_var, eval_betaF_vars_ccons,
    eval_betaF_vars_ccons_numerals, eval_termSubstJustAt_tableVars]

private def termPairAt (x : Nat) (u t : Term) : Nat :=
  ccons (encodeTerm t) (encodeTerm (substTerm x u t))

private def termTableAt (x : Nat) (u root : Term) (i : Nat) : Nat :=
  match (termPostorder root)[i]? with
  | some t => termPairAt x u t
  | none => 0

private theorem termTableAt_entry_local (x : Nat) (u root node : Term)
    (c d L i : Nat) (hi : i ≤ L)
    (hnode : (termPostorder root)[i]? = some node)
    (hpack : ∀ j, j ≤ L → beta c d j = termTableAt x u root j) :
    TermSubstJustAtNat c d i x (encodeTerm u) (encodeTerm node)
      (encodeTerm (substTerm x u node)) := by
  have hchildren := termPostorder_ok root i node hnode
  cases node with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ t =>
      rcases hchildren with ⟨j, hj, hjt⟩
      refine Or.inr (Or.inl ⟨encodeTerm t, encodeTerm (substTerm x u t), j,
        rfl, rfl, hj, ?_⟩)
      have hb := hpack j (Nat.le_trans (Nat.le_of_lt hj) hi)
      simp only [termTableAt, hjt, termPairAt] at hb
      exact hb.symm
  | add s t =>
      rcases hchildren with ⟨j, k, hj, hk, hjs, hkt⟩
      refine Or.inr (Or.inr (Or.inl ⟨encodeTerm s, encodeTerm t,
        encodeTerm (substTerm x u s), encodeTerm (substTerm x u t), j, k,
        rfl, rfl, hj, hk, ?_, ?_⟩))
      · have hb := hpack j (Nat.le_trans (Nat.le_of_lt hj) hi)
        simp only [termTableAt, hjs, termPairAt] at hb
        exact hb.symm
      · have hb := hpack k (Nat.le_trans (Nat.le_of_lt hk) hi)
        simp only [termTableAt, hkt, termPairAt] at hb
        exact hb.symm
  | mul s t =>
      rcases hchildren with ⟨j, k, hj, hk, hjs, hkt⟩
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨encodeTerm s, encodeTerm t,
        encodeTerm (substTerm x u s), encodeTerm (substTerm x u t), j, k,
        rfl, rfl, hj, hk, ?_, ?_⟩)))
      · have hb := hpack j (Nat.le_trans (Nat.le_of_lt hj) hi)
        simp only [termTableAt, hjs, termPairAt] at hb
        exact hb.symm
      · have hb := hpack k (Nat.le_trans (Nat.le_of_lt hk) hi)
        simp only [termTableAt, hkt, termPairAt] at hb
        exact hb.symm
  | var n =>
      by_cases hnx : n = x
      · subst n
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        exact ⟨rfl, by simp [substTerm]⟩
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
        refine ⟨⟨n, rfl, hnx⟩, ?_⟩
        simp [substTerm, hnx]

theorem termSubstTraceAt_complete (x : Nat) (u t : Term) :
    ∃ c d L,
      ccons (encodeTerm t) (encodeTerm (substTerm x u t)) = beta c d L ∧
      TermSubstTraceAt c d L x (encodeTerm u) := by
  let L := (termPostorder t).length - 1
  obtain ⟨c, d, hpack⟩ := beta_exists L (termTableAt x u t)
  refine ⟨c, d, L, ?_, ?_⟩
  · have hne := termPostorder_ne_nil t
    have hroot : (termPostorder t)[L]? = some t := by
      dsimp [L]
      exact getLast?_some_getElem? (termPostorder_getLast t) hne
    have hb := hpack L (Nat.le_refl L)
    simp only [termTableAt, hroot, termPairAt] at hb
    exact hb.symm
  · intro i hi
    have hilt : i < (termPostorder t).length := by
      dsimp [L] at hi
      have hpos : 0 < (termPostorder t).length :=
        List.length_pos_iff.mpr (termPostorder_ne_nil t)
      omega
    let node : Term := (termPostorder t)[i]
    have hnode : (termPostorder t)[i]? = some node := by
      simpa [node] using List.getElem?_eq_getElem hilt
    refine ⟨encodeTerm node, encodeTerm (substTerm x u node), ?_, ?_⟩
    · have hb := hpack i hi
      simp only [termTableAt, hnode, termPairAt] at hb
      exact hb.symm
    · exact termTableAt_entry_local x u t node c d L i hi hnode hpack

theorem termSubstClosedAt_complete (env : Nat → Nat) (x : Nat) (u t : Term) :
    evalForm env (termSubstClosedAt (numeral (encodeTerm t))
      (numeral (encodeTerm (substTerm x u t))) (numeral x) (numeral (encodeTerm u))) := by
  apply (eval_termSubstClosedAt_numerals env _ _ _ _).2
  exact termSubstTraceAt_complete x u t

private def TermSubstGraphAt (x u inC outC : Nat) : Prop :=
  ∃ c d L, ccons inC outC = beta c d L ∧ TermSubstTraceAt c d L x u

private theorem eval_termSubstClosedAt_vars_261_263 (env : Nat → Nat) (x u : Nat) :
    evalForm env (termSubstClosedAt (Term.var 261) (Term.var 263)
      (numeral x) (numeral u)) ↔
      TermSubstGraphAt x u (env 261) (env 263) := by
  simp [termSubstClosedAt, TermSubstGraphAt, TermSubstTraceAt,
    eval_existsF, eval_andF, evalForm_all, evalForm_imp,
    eval_leF_var_var, eval_betaF_vars_ccons, eval_termSubstJustAt_tableVars]

private theorem eval_termSubstClosedAt_vars_262_264 (env : Nat → Nat) (x u : Nat) :
    evalForm env (termSubstClosedAt (Term.var 262) (Term.var 264)
      (numeral x) (numeral u)) ↔
      TermSubstGraphAt x u (env 262) (env 264) := by
  simp [termSubstClosedAt, TermSubstGraphAt, TermSubstTraceAt,
    eval_existsF, eval_andF, evalForm_all, evalForm_imp,
    eval_leF_var_var, eval_betaF_vars_ccons, eval_termSubstJustAt_tableVars]

private theorem termSubstGraphAt_complete (x : Nat) (u t : Term) :
    TermSubstGraphAt x (encodeTerm u) (encodeTerm t)
      (encodeTerm (substTerm x u t)) := by
  exact termSubstTraceAt_complete x u t

private def FormSubstJustAtNat (c d i x u inC outC : Nat) : Prop :=
  (∃ a b a' b',
    inC = ccons 0 (ccons a b) ∧ outC = ccons 0 (ccons a' b') ∧
      TermSubstGraphAt x u a a' ∧ TermSubstGraphAt x u b b') ∨
  (∃ a a' j, inC = ccons 1 a ∧ outC = ccons 1 a' ∧ j < i ∧
    ccons a a' = beta c d j) ∨
  (∃ a b a' b' j k,
    inC = ccons 2 (ccons a b) ∧ outC = ccons 2 (ccons a' b') ∧
      j < i ∧ k < i ∧ ccons a a' = beta c d j ∧ ccons b b' = beta c d k) ∨
  (∃ y a a' j,
    inC = ccons 3 (ccons y a) ∧
      ((y = x ∧ outC = inC) ∨
        (y ≠ x ∧ outC = ccons 3 (ccons y a') ∧ j < i ∧
          ccons a a' = beta c d j)))

private theorem eval_formSubstJustAt_tableVars (env : Nat → Nat) (x u : Nat) :
    evalForm env (formSubstJustAt (Term.var 270) (Term.var 271) (Term.var 273)
      (numeral x) (numeral u) (Term.var 274) (Term.var 275)) ↔
      FormSubstJustAtNat (env 270) (env 271) (env 273) x u
        (env 274) (env 275) := by
  simp [formSubstJustAt, FormSubstJustAtNat, formSubstEqCaseAt,
    formSubstNotCase, formSubstImpCase, formSubstAllCaseAt,
    eval_existsF, eval_andF, eval_orF, eval_eqCcons, eval_cconsTerm,
    eval_ltF_var_var, eval_betaF_vars_ccons,
    eval_termSubstClosedAt_vars_261_263, eval_termSubstClosedAt_vars_262_264,
    evalForm, evalTerm, evalTerm_numeral]

private def FormSubstTraceAt (c d L x u : Nat) : Prop :=
  ∀ i, i ≤ L → ∃ inC outC,
    ccons inC outC = beta c d i ∧ FormSubstJustAtNat c d i x u inC outC

private theorem eval_formSubstAtClosed_numerals (env : Nat → Nat)
    (body outC x u : Nat) :
    evalForm env (formSubstAtClosed (numeral body) (numeral outC)
      (numeral x) (numeral u)) ↔
      ∃ c d L, ccons body outC = beta c d L ∧ FormSubstTraceAt c d L x u := by
  simp [formSubstAtClosed, FormSubstTraceAt, eval_existsF, eval_andF,
    evalForm_all, evalForm_imp, eval_leF_var_var, eval_betaF_vars_ccons,
    eval_betaF_vars_ccons_numerals, eval_formSubstJustAt_tableVars]

private def FormChildrenBefore (xs : List Formula) (i : Nat) : Formula → Prop
  | Formula.eq _ _ => True
  | Formula.not a => ∃ j, j < i ∧ xs[j]? = some a
  | Formula.imp a b => ∃ j k, j < i ∧ k < i ∧ xs[j]? = some a ∧ xs[k]? = some b
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
      · rw [List.getElem?_append_left (Nat.lt_trans hj hi)]; exact hb
      · rw [List.getElem?_append_left (Nat.lt_trans hk hi)]; exact hc
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
      · rw [List.getElem?_append_right (Nat.le_add_right _ _)]; simpa using hb
      · rw [List.getElem?_append_right (Nat.le_add_right _ _)]; simpa using hc
  | all _ b =>
      rcases h with ⟨j, hj, hb⟩
      refine ⟨xs.length + j, by omega, ?_⟩
      rw [List.getElem?_append_right (Nat.le_add_right _ _)]
      simpa using hb

private theorem formPostorderOK_nil : FormPostorderOK [] := by
  intro i a h
  simp at h

private theorem formPostorderOK_append {xs ys : List Formula}
    (hx : FormPostorderOK xs) (hy : FormPostorderOK ys) : FormPostorderOK (xs ++ ys) := by
  intro i a hia
  rcases getElem?_append_cases hia with hleft | hright
  · exact formChildrenBefore_append_left hleft.1 (hx i a hleft.2)
  · rcases hright with ⟨hi, hia'⟩
    have hs := formChildrenBefore_append_right (xs := xs) (hy (i - xs.length) a hia')
    have heq : xs.length + (i - xs.length) = i := Nat.add_sub_of_le hi
    simpa [heq] using hs

private theorem formPostorderOK_snoc {xs : List Formula} {a : Formula}
    (hx : FormPostorderOK xs)
    (hroot : FormChildrenBefore (xs ++ [a]) xs.length a) : FormPostorderOK (xs ++ [a]) := by
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
      apply formPostorderOK_snoc (formPostorderOK_append (formPostorder_ok a) (formPostorder_ok b))
      have ha := formPostorder_ne_nil a
      have hb := formPostorder_ne_nil b
      have hapos : 0 < (formPostorder a).length := List.length_pos_iff.mpr ha
      have hbpos : 0 < (formPostorder b).length := List.length_pos_iff.mpr hb
      refine ⟨(formPostorder a).length - 1,
        (formPostorder a).length + ((formPostorder b).length - 1), ?_, ?_, ?_, ?_⟩
      · simp [List.length_append]; omega
      · simp [List.length_append]; omega
      · have hjouter : (formPostorder a).length - 1 <
            (formPostorder a ++ formPostorder b).length := by
          simp [List.length_append]; omega
        have houter := List.getElem?_append_left
          (l₂ := [Formula.imp a b]) hjouter
        have hinner := List.getElem?_append_left
          (l₂ := formPostorder b) (Nat.pred_lt hapos.ne')
        exact houter.trans (hinner.trans
          (getLast?_some_getElem? (formPostorder_getLast a) ha))
      · have hkouter : (formPostorder a).length + ((formPostorder b).length - 1) <
            (formPostorder a ++ formPostorder b).length := by
          simp [List.length_append]; omega
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

private def formPairAt (x : Nat) (u : Term) (a : Formula) : Nat :=
  ccons (encodeFormula a) (encodeFormula (substForm x u a))

private def formTableAt (x : Nat) (u : Term) (root : Formula) (i : Nat) : Nat :=
  match (formPostorder root)[i]? with
  | some a => formPairAt x u a
  | none => 0

private theorem formTableAt_entry_local (x : Nat) (u : Term) (root node : Formula)
    (c d L i : Nat) (hi : i ≤ L)
    (hnode : (formPostorder root)[i]? = some node)
    (hpack : ∀ j, j ≤ L → beta c d j = formTableAt x u root j) :
    FormSubstJustAtNat c d i x (encodeTerm u) (encodeFormula node)
      (encodeFormula (substForm x u node)) := by
  have hchildren := formPostorder_ok root i node hnode
  cases node with
  | eq s t =>
      refine Or.inl ⟨encodeTerm s, encodeTerm t,
        encodeTerm (substTerm x u s), encodeTerm (substTerm x u t), rfl, rfl, ?_, ?_⟩
      · exact termSubstGraphAt_complete x u s
      · exact termSubstGraphAt_complete x u t
  | not a =>
      rcases hchildren with ⟨j, hj, hja⟩
      refine Or.inr (Or.inl ⟨encodeFormula a, encodeFormula (substForm x u a), j, rfl, rfl, hj, ?_⟩)
      have hb := hpack j (Nat.le_trans (Nat.le_of_lt hj) hi)
      simp only [formTableAt, hja, formPairAt] at hb
      exact hb.symm
  | imp a b =>
      rcases hchildren with ⟨j, k, hj, hk, hja, hkb⟩
      refine Or.inr (Or.inr (Or.inl ⟨encodeFormula a, encodeFormula b,
        encodeFormula (substForm x u a), encodeFormula (substForm x u b), j, k,
        rfl, rfl, hj, hk, ?_, ?_⟩))
      · have hb := hpack j (Nat.le_trans (Nat.le_of_lt hj) hi)
        simp only [formTableAt, hja, formPairAt] at hb
        exact hb.symm
      · have hb := hpack k (Nat.le_trans (Nat.le_of_lt hk) hi)
        simp only [formTableAt, hkb, formPairAt] at hb
        exact hb.symm
  | all y a =>
      rcases hchildren with ⟨j, hj, hja⟩
      refine Or.inr (Or.inr (Or.inr ⟨y, encodeFormula a,
        encodeFormula (substForm x u a), j, rfl, ?_⟩))
      by_cases hyx : y = x
      · subst y
        exact Or.inl ⟨rfl, by simp [substForm]⟩
      · refine Or.inr ⟨hyx, ?_, hj, ?_⟩
        · simp [substForm, hyx, encodeFormula]
        · have hb := hpack j (Nat.le_trans (Nat.le_of_lt hj) hi)
          simp only [formTableAt, hja, formPairAt] at hb
          exact hb.symm

private theorem formSubstTraceAt_complete (x : Nat) (u : Term) (a : Formula) :
    ∃ c d L,
      ccons (encodeFormula a) (encodeFormula (substForm x u a)) = beta c d L ∧
      FormSubstTraceAt c d L x (encodeTerm u) := by
  let L := (formPostorder a).length - 1
  obtain ⟨c, d, hpack⟩ := beta_exists L (formTableAt x u a)
  refine ⟨c, d, L, ?_, ?_⟩
  · have hne := formPostorder_ne_nil a
    have hroot : (formPostorder a)[L]? = some a := by
      dsimp [L]
      exact getLast?_some_getElem? (formPostorder_getLast a) hne
    have hb := hpack L (Nat.le_refl L)
    simp only [formTableAt, hroot, formPairAt] at hb
    exact hb.symm
  · intro i hi
    have hilt : i < (formPostorder a).length := by
      dsimp [L] at hi
      have hpos : 0 < (formPostorder a).length := List.length_pos_iff.mpr (formPostorder_ne_nil a)
      omega
    let node : Formula := (formPostorder a)[i]
    have hnode : (formPostorder a)[i]? = some node := by
      simpa [node] using List.getElem?_eq_getElem hilt
    refine ⟨encodeFormula node, encodeFormula (substForm x u node), ?_, ?_⟩
    · have hb := hpack i hi
      simp only [formTableAt, hnode, formPairAt] at hb
      exact hb.symm
    · exact formTableAt_entry_local x u a node c d L i hi hnode hpack

theorem formSubstAtClosed_complete (env : Nat → Nat) (x : Nat) (u : Term) (a : Formula) :
    evalForm env (formSubstAtClosed (numeral (encodeFormula a))
      (numeral (encodeFormula (substForm x u a))) (numeral x) (numeral (encodeTerm u))) := by
  apply (eval_formSubstAtClosed_numerals env _ _ _ _).2
  exact formSubstTraceAt_complete x u a


private theorem eval_betaF_four_vars (env : Nat → Nat) {c d i a : Nat}
    (hi51 : i ≠ 51) (hd51 : d ≠ 51) (ha51 : a ≠ 51)
    (hc52 : c ≠ 52) (hi52 : i ≠ 52) (hd52 : d ≠ 52) (ha52 : a ≠ 52) :
    evalForm env (betaF (Term.var c) (Term.var d) (Term.var i) (Term.var a)) ↔
      env a = beta (env c) (env d) (env i) := by
  simpa [evalTerm] using
    (eval_betaF env (Term.var c) (Term.var d) (Term.var i) (Term.var a)
      (by simp [termHasVar, hi51]) (by simp [termHasVar, hd51])
      (by simp [termHasVar, ha51]) (by simp [termHasVar, hc52])
      (by simp [termHasVar, hi52]) (by simp [termHasVar, hd52])
      (by simp [termHasVar, ha52]))

private theorem eval_betaF_three_vars_numeral (env : Nat → Nat) {c d i : Nat} (a : Nat)
    (hi51 : i ≠ 51) (hd51 : d ≠ 51)
    (hc52 : c ≠ 52) (hi52 : i ≠ 52) (hd52 : d ≠ 52) :
    evalForm env (betaF (Term.var c) (Term.var d) (Term.var i) (numeral a)) ↔
      a = beta (env c) (env d) (env i) := by
  simpa [evalTerm, evalTerm_numeral] using
    (eval_betaF env (Term.var c) (Term.var d) (Term.var i) (numeral a)
      (by simp [termHasVar, hi51]) (by simp [termHasVar, hd51])
      (numeral_closed a 51) (by simp [termHasVar, hc52])
      (by simp [termHasVar, hi52]) (by simp [termHasVar, hd52])
      (numeral_closed a 52))

private def TermNodeClosedNat (c d i : Nat) : Prop :=
  (beta c d i = ccons 0 0) ∨
  (∃ a j, beta c d i = ccons 1 a ∧ j < i ∧ a = beta c d j) ∨
  (∃ a b j k, beta c d i = ccons 2 (ccons a b) ∧
    j < i ∧ k < i ∧ a = beta c d j ∧ b = beta c d k) ∨
  (∃ a b j k, beta c d i = ccons 3 (ccons a b) ∧
    j < i ∧ k < i ∧ a = beta c d j ∧ b = beta c d k)

private theorem eval_termNodeClosedF_tableVars (env : Nat → Nat) :
    evalForm env (termNodeClosedF (Term.var 280) (Term.var 281) (Term.var 283)) ↔
      TermNodeClosedNat (env 280) (env 281) (env 283) := by
  simp [termNodeClosedF, TermNodeClosedNat, eval_existsF, eval_andF, eval_orF,
    eval_eqCcons, eval_cconsTerm, eval_ltF_var_var, eval_betaF_four_vars,
    evalForm, evalTerm, evalTerm_numeral]

private def TermClosedTrace (c d L : Nat) : Prop :=
  ∀ i, i ≤ L → TermNodeClosedNat c d i

private theorem eval_termClosedPack_numeral (env : Nat → Nat) (code : Nat) :
    evalForm env (termClosedPack (numeral code)) ↔
      ∃ c d L, code = beta c d L ∧ TermClosedTrace c d L := by
  simp [termClosedPack, TermClosedTrace, eval_existsF, eval_andF,
    evalForm_all, evalForm_imp, eval_leF_var_var, eval_betaF_three_vars_numeral,
    eval_termNodeClosedF_tableVars, evalTerm, evalTerm_numeral]

private theorem termPostorder_mem_closed :
    ∀ root : Term, isClosedTerm root = true → ∀ node, node ∈ termPostorder root →
      isClosedTerm node = true
  | Term.zero, _, node, hmem => by
      simp [termPostorder] at hmem
      subst node
      rfl
  | Term.succ t, ht, node, hmem => by
      simp [termPostorder] at hmem
      rcases hmem with hmem | rfl
      · exact termPostorder_mem_closed t ht node hmem
      · simpa [isClosedTerm] using ht
  | Term.add s t, ht, node, hmem => by
      simp [isClosedTerm, Bool.and_eq_true] at ht
      simp [termPostorder] at hmem
      rcases hmem with hs | htmem | rfl
      · exact termPostorder_mem_closed s ht.1 node hs
      · exact termPostorder_mem_closed t ht.2 node htmem
      · simp [isClosedTerm, ht]
  | Term.mul s t, ht, node, hmem => by
      simp [isClosedTerm, Bool.and_eq_true] at ht
      simp [termPostorder] at hmem
      rcases hmem with hs | htmem | rfl
      · exact termPostorder_mem_closed s ht.1 node hs
      · exact termPostorder_mem_closed t ht.2 node htmem
      · simp [isClosedTerm, ht]
  | Term.var n, ht, node, hmem => by
      simp [isClosedTerm] at ht

private def closedTermTable (root : Term) (i : Nat) : Nat :=
  match (termPostorder root)[i]? with
  | some t => encodeTerm t
  | none => 0

private theorem closedTermTable_entry_local (root node : Term) (hclosed : isClosedTerm root = true)
    (c d L i : Nat) (hi : i ≤ L) (hnode : (termPostorder root)[i]? = some node)
    (hpack : ∀ j, j ≤ L → beta c d j = closedTermTable root j) :
    TermNodeClosedNat c d i := by
  have hchildren := termPostorder_ok root i node hnode
  have hmem : node ∈ termPostorder root := List.mem_of_getElem? hnode
  have hnclosed := termPostorder_mem_closed root hclosed node hmem
  cases node with
  | zero =>
      exact Or.inl (by
        have hb := hpack i hi
        simp only [closedTermTable, hnode, encodeTerm] at hb
        exact hb)
  | succ t =>
      rcases hchildren with ⟨j, hj, hjt⟩
      refine Or.inr (Or.inl ⟨encodeTerm t, j, ?_, hj, ?_⟩)
      · have hb := hpack i hi
        simp only [closedTermTable, hnode, encodeTerm] at hb
        exact hb
      · have hb := hpack j (Nat.le_trans (Nat.le_of_lt hj) hi)
        simp only [closedTermTable, hjt] at hb
        exact hb.symm
  | add s t =>
      rcases hchildren with ⟨j, k, hj, hk, hjs, hkt⟩
      refine Or.inr (Or.inr (Or.inl ⟨encodeTerm s, encodeTerm t, j, k, ?_, hj, hk, ?_, ?_⟩))
      · have hb := hpack i hi
        simp only [closedTermTable, hnode, encodeTerm] at hb
        exact hb
      · have hb := hpack j (Nat.le_trans (Nat.le_of_lt hj) hi)
        simp only [closedTermTable, hjs] at hb
        exact hb.symm
      · have hb := hpack k (Nat.le_trans (Nat.le_of_lt hk) hi)
        simp only [closedTermTable, hkt] at hb
        exact hb.symm
  | mul s t =>
      rcases hchildren with ⟨j, k, hj, hk, hjs, hkt⟩
      refine Or.inr (Or.inr (Or.inr ⟨encodeTerm s, encodeTerm t, j, k, ?_, hj, hk, ?_, ?_⟩))
      · have hb := hpack i hi
        simp only [closedTermTable, hnode, encodeTerm] at hb
        exact hb
      · have hb := hpack j (Nat.le_trans (Nat.le_of_lt hj) hi)
        simp only [closedTermTable, hjs] at hb
        exact hb.symm
      · have hb := hpack k (Nat.le_trans (Nat.le_of_lt hk) hi)
        simp only [closedTermTable, hkt] at hb
        exact hb.symm
  | var n => simp [isClosedTerm] at hnclosed

private theorem termClosedTrace_complete (t : Term) (ht : isClosedTerm t = true) :
    ∃ c d L, encodeTerm t = beta c d L ∧ TermClosedTrace c d L := by
  let L := (termPostorder t).length - 1
  obtain ⟨c, d, hpack⟩ := beta_exists L (closedTermTable t)
  refine ⟨c, d, L, ?_, ?_⟩
  · have hne := termPostorder_ne_nil t
    have hroot : (termPostorder t)[L]? = some t := by
      dsimp [L]
      exact getLast?_some_getElem? (termPostorder_getLast t) hne
    have hb := hpack L (Nat.le_refl L)
    simp only [closedTermTable, hroot] at hb
    exact hb.symm
  · intro i hi
    have hilt : i < (termPostorder t).length := by
      dsimp [L] at hi
      have hpos : 0 < (termPostorder t).length := List.length_pos_iff.mpr (termPostorder_ne_nil t)
      omega
    let node : Term := (termPostorder t)[i]
    have hnode : (termPostorder t)[i]? = some node := by
      simpa [node] using List.getElem?_eq_getElem hilt
    exact closedTermTable_entry_local t node ht c d L i hi hnode hpack

theorem termClosedPack_complete (env : Nat → Nat) (t : Term)
    (ht : isClosedTerm t = true) : evalForm env (termClosedPack (numeral (encodeTerm t))) := by
  apply (eval_termClosedPack_numeral env (encodeTerm t)).2
  exact termClosedTrace_complete t ht


private theorem shape_of_q (φ : Formula) (h : isQAxiom φ = true) :
    AxiomCodeShape (encodeFormula φ) := by
  simp [isQAxiom] at h
  rcases h with h | h7
  · rcases h with h | h6
    · rcases h with h | h5
      · rcases h with h | h4
        · rcases h with h | h3
          · rcases h with h1 | h2
            · left; left; exact congrArg encodeFormula h1
            · left; right; left; exact congrArg encodeFormula h2
          · left; right; right; left; exact congrArg encodeFormula h3
        · left; right; right; right; left; exact congrArg encodeFormula h4
      · left; right; right; right; right; left; exact congrArg encodeFormula h5
    · left; right; right; right; right; right; left; exact congrArg encodeFormula h6
  · left; right; right; right; right; right; right; exact congrArg encodeFormula h7

private theorem shape_of_refl (φ : Formula) (h : isEqRefl φ = true) :
    AxiomCodeShape (encodeFormula φ) := by
  cases φ with
  | eq s t =>
      simp [isEqRefl] at h
      subst t
      exact Or.inr (Or.inl ⟨encodeTerm s, rfl⟩)
  | not _ => simp [isEqRefl] at h
  | imp _ _ => simp [isEqRefl] at h
  | all _ _ => simp [isEqRefl] at h

private theorem shape_of_id (φ : Formula) (h : isAxId φ = true) :
    AxiomCodeShape (encodeFormula φ) := by
  cases φ with
  | imp a b =>
      simp [isAxId] at h
      subst b
      exact Or.inr (Or.inr (Or.inl ⟨encodeFormula a, rfl⟩))
  | eq _ _ => simp [isAxId] at h
  | not _ => simp [isAxId] at h
  | all _ _ => simp [isAxId] at h

private theorem shape_of_k (φ : Formula) (h : isAxK φ = true) :
    AxiomCodeShape (encodeFormula φ) := by
  cases φ with
  | imp a bc =>
      cases bc with
      | imp b c =>
          simp [isAxK] at h
          subst c
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨encodeFormula a, encodeFormula b, rfl⟩)))
      | eq _ _ => simp [isAxK] at h
      | not _ => simp [isAxK] at h
      | all _ _ => simp [isAxK] at h
  | eq _ _ => simp [isAxK] at h
  | not _ => simp [isAxK] at h
  | all _ _ => simp [isAxK] at h

private theorem shape_of_s (φ : Formula) (h : isAxS φ = true) :
    AxiomCodeShape (encodeFormula φ) := by
  cases φ with
  | imp lhs rhs =>
      cases lhs with
      | imp a bc =>
          cases bc with
          | imp b c =>
              cases rhs with
              | imp ab ac =>
                  cases ab with
                  | imp a' b' =>
                      cases ac with
                      | imp a'' c' =>
                          simp [isAxS] at h
                          rcases h with ⟨rfl, rfl, rfl, rfl⟩
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                            ⟨encodeFormula a, encodeFormula b, encodeFormula c, rfl⟩))))
                      | eq _ _ => simp [isAxS] at h
                      | not _ => simp [isAxS] at h
                      | all _ _ => simp [isAxS] at h
                  | eq _ _ => simp [isAxS] at h
                  | not _ => simp [isAxS] at h
                  | all _ _ => simp [isAxS] at h
              | eq _ _ => simp [isAxS] at h
              | not _ => simp [isAxS] at h
              | all _ _ => simp [isAxS] at h
          | eq _ _ => simp [isAxS] at h
          | not _ => simp [isAxS] at h
          | all _ _ => simp [isAxS] at h
      | eq _ _ => simp [isAxS] at h
      | not _ => simp [isAxS] at h
      | all _ _ => simp [isAxS] at h
  | eq _ _ => simp [isAxS] at h
  | not _ => simp [isAxS] at h
  | all _ _ => simp [isAxS] at h

private theorem shape_of_dne (φ : Formula) (h : isAxDNE φ = true) :
    AxiomCodeShape (encodeFormula φ) := by
  cases φ with
  | imp nn b =>
      cases nn with
      | not n =>
          cases n with
          | not a =>
              simp [isAxDNE] at h
              subst b
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨encodeFormula a, rfl⟩))))
          | eq _ _ => simp [isAxDNE] at h
          | imp _ _ => simp [isAxDNE] at h
          | all _ _ => simp [isAxDNE] at h
      | eq _ _ => simp [isAxDNE] at h
      | imp _ _ => simp [isAxDNE] at h
      | all _ _ => simp [isAxDNE] at h
  | eq _ _ => simp [isAxDNE] at h
  | not _ => simp [isAxDNE] at h
  | all _ _ => simp [isAxDNE] at h

theorem axiomCodeShape_encode_of_isAxiom (φ : Formula) (h : isAxiom φ = true) :
    AxiomCodeShape (encodeFormula φ) := by
  simp only [isAxiom, Bool.or_eq_true] at h
  rcases h with h | hid
  · rcases h with h | hrefl
    · rcases h with h | hdne
      · rcases h with h | hs
        · rcases h with hq | hk
          · exact shape_of_q φ hq
          · exact shape_of_k φ hk
        · exact shape_of_s φ hs
      · exact shape_of_dne φ hdne
    · exact shape_of_refl φ hrefl
  · exact shape_of_id φ hid


private theorem eval_termSubstJustAt_allVars (env : Nat → Nat) :
    evalForm env (termSubstJustAt (Term.var 290) (Term.var 291) (Term.var 293)
      (Term.var 63) (Term.var 65) (Term.var 294) (Term.var 295)) ↔
      TermSubstJustAtNat (env 290) (env 291) (env 293) (env 63) (env 65)
        (env 294) (env 295) := by
  simp [termSubstJustAt, TermSubstJustAtNat, termSubstZeroCase,
    termSubstSuccCase, termSubstAddCase, termSubstMulCase, termSubstVarCaseAt,
    eval_existsF, eval_andF, eval_orF, eval_eqCcons, eval_cconsTerm,
    eval_ltF_var_var, eval_betaF_vars_ccons, evalForm, evalTerm, evalTerm_numeral]

private theorem eval_termSubstClosedAt_allVars_261_263 (env : Nat → Nat) :
    evalForm env (termSubstClosedAt (Term.var 261) (Term.var 263)
      (Term.var 63) (Term.var 65)) ↔
      ∃ c d L, ccons (env 261) (env 263) = beta c d L ∧
        TermSubstTraceAt c d L (env 63) (env 65) := by
  simp [termSubstClosedAt, TermSubstTraceAt, eval_existsF, eval_andF,
    evalForm_all, evalForm_imp, eval_leF_var_var, eval_betaF_vars_ccons,
    eval_termSubstJustAt_allVars]

private theorem eval_termSubstClosedAt_allVars_262_264 (env : Nat → Nat) :
    evalForm env (termSubstClosedAt (Term.var 262) (Term.var 264)
      (Term.var 63) (Term.var 65)) ↔
      ∃ c d L, ccons (env 262) (env 264) = beta c d L ∧
        TermSubstTraceAt c d L (env 63) (env 65) := by
  simp [termSubstClosedAt, TermSubstTraceAt, eval_existsF, eval_andF,
    evalForm_all, evalForm_imp, eval_leF_var_var, eval_betaF_vars_ccons,
    eval_termSubstJustAt_allVars]

private theorem eval_formSubstJustAt_allVars (env : Nat → Nat) :
    evalForm env (formSubstJustAt (Term.var 270) (Term.var 271) (Term.var 273)
      (Term.var 63) (Term.var 65) (Term.var 274) (Term.var 275)) ↔
      FormSubstJustAtNat (env 270) (env 271) (env 273) (env 63) (env 65)
        (env 274) (env 275) := by
  simp [formSubstJustAt, FormSubstJustAtNat, TermSubstGraphAt, formSubstEqCaseAt,
    formSubstNotCase, formSubstImpCase, formSubstAllCaseAt,
    eval_existsF, eval_andF, eval_orF, eval_eqCcons, eval_cconsTerm,
    eval_ltF_var_var, eval_betaF_vars_ccons,
    eval_termSubstClosedAt_allVars_261_263, eval_termSubstClosedAt_allVars_262_264,
    evalForm, evalTerm, evalTerm_numeral]

private theorem eval_formSubstAtClosed_allVars (env : Nat → Nat) :
    evalForm env (formSubstAtClosed (Term.var 64) (Term.var 55)
      (Term.var 63) (Term.var 65)) ↔
      ∃ c d L, ccons (env 64) (env 55) = beta c d L ∧
        FormSubstTraceAt c d L (env 63) (env 65) := by
  simp [formSubstAtClosed, FormSubstTraceAt, eval_existsF, eval_andF,
    evalForm_all, evalForm_imp, eval_leF_var_var, eval_betaF_vars_ccons,
    eval_formSubstJustAt_allVars]

private theorem eval_termClosedPack_var65 (env : Nat → Nat) :
    evalForm env (termClosedPack (Term.var 65)) ↔
      ∃ c d L, env 65 = beta c d L ∧ TermClosedTrace c d L := by
  simp [termClosedPack, TermClosedTrace, eval_existsF, eval_andF,
    evalForm_all, evalForm_imp, eval_leF_var_var, eval_betaF_four_vars,
    eval_termNodeClosedF_tableVars]
/-- A checked closed-instantiation Hilbert line satisfies the object-language `specJustF` branch. -/
theorem specJustF_complete (env : Nat → Nat) (c d i j x : Nat) (t : Term) (φ : Formula)
    (hc : env 40 = c) (hd : env 41 = d) (hi : env 43 = i)
    (hcur : beta c d i = encodeFormula (substForm x t φ))
    (hprev : beta c d j = encodeFormula (Formula.all x φ))
    (hj : j < i) (ht : isClosedTerm t = true) :
    evalForm env (specJustF (Term.var 40) (Term.var 41) (Term.var 43)) := by
  refine (eval_existsF env 55 _).2 ⟨encodeFormula (substForm x t φ), ?_⟩
  let e55 : Nat → Nat := fun y => if y = 55 then encodeFormula (substForm x t φ) else env y
  refine (eval_existsF e55 61 _).2 ⟨j, ?_⟩
  let e61 : Nat → Nat := fun y => if y = 61 then j else e55 y
  refine (eval_existsF e61 62 _).2 ⟨encodeFormula (Formula.all x φ), ?_⟩
  let e62 : Nat → Nat := fun y => if y = 62 then encodeFormula (Formula.all x φ) else e61 y
  refine (eval_existsF e62 63 _).2 ⟨x, ?_⟩
  let e63 : Nat → Nat := fun y => if y = 63 then x else e62 y
  refine (eval_existsF e63 64 _).2 ⟨encodeFormula φ, ?_⟩
  let e64 : Nat → Nat := fun y => if y = 64 then encodeFormula φ else e63 y
  refine (eval_existsF e64 65 _).2 ⟨encodeTerm t, ?_⟩
  let e65 : Nat → Nat := fun y => if y = 65 then encodeTerm t else e64 y
  rw [eval_andF]
  constructor
  · apply (eval_betaF_four_vars e65 (c := 40) (d := 41) (i := 43) (a := 55)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2
    simp [e65, e64, e63, e62, e61, e55, hc, hd, hi, hcur]
  · rw [eval_andF]
    constructor
    · exact (eval_ltF_var_var e65 (x := 61) (y := 43) (by decide) (by decide)).2 (by
        simpa [e65, e64, e63, e62, e61, e55, hi] using hj)
    · rw [eval_andF]
      constructor
      · apply (eval_betaF_four_vars e65 (c := 40) (d := 41) (i := 61) (a := 62)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2
        simp [e65, e64, e63, e62, e61, e55, hc, hd, hprev]
      · rw [eval_andF]
        constructor
        · apply (eval_eqCcons e65 (Term.var 62) (numeral 3)
            (cconsTerm (Term.var 63) (Term.var 64))).2
          simp [e65, e64, e63, e62, e61, e55, evalTerm, evalTerm_numeral,
            eval_cconsTerm, encodeFormula]
        · rw [eval_andF]
          constructor
          · apply (eval_formSubstAtClosed_allVars e65).2
            simpa [e65, e64, e63, e62, e61, e55] using
              (formSubstTraceAt_complete x t φ)
          · apply (eval_termClosedPack_var65 e65).2
            simpa [e65, e64, e63, e62, e61, e55] using
              (termClosedTrace_complete t ht)
def JustifiedNat (c d i : Nat) : Prop :=
  AxiomCodeShape (beta c d i) ∨
  (∃ j k, j < i ∧ k < i ∧
    beta c d j = ccons 2 (ccons (beta c d k) (beta c d i))) ∨
  (∃ j x, j < i ∧ beta c d i = ccons 3 (ccons x (beta c d j)))

theorem eval_justifiedF_vars (env : Nat → Nat) :
    evalForm env (justifiedF (Term.var 40) (Term.var 41) (Term.var 43)) ↔
      JustifiedNat (env 40) (env 41) (env 43) := by
  simp [justifiedF, JustifiedNat, eval_existsF, eval_andF, eval_orF,
    eval_betaF_four_vars, eval_isAxiomF_var55,
    eval_ltF_var_var, isImpF, isGenF, eval_eqCcons, eval_cconsTerm,
    evalForm, evalTerm, evalTerm_numeral]


private def proofSeqCode (p : ProofTree) (i : Nat) : Nat :=
  match (flattenProof p)[i]? with
  | some φ => encodeFormula φ
  | none => 0

private def proofSeqLast (p : ProofTree) : Nat := (flattenProof p).length - 1

private noncomputable def proofBetaC (p : ProofTree) : Nat :=
  Classical.choose (beta_exists (proofSeqLast p) (proofSeqCode p))

private noncomputable def proofBetaD (p : ProofTree) : Nat :=
  Classical.choose (Classical.choose_spec
    (beta_exists (proofSeqLast p) (proofSeqCode p)))

private theorem proofBeta_spec (p : ProofTree) :
    ∀ i, i ≤ proofSeqLast p → beta (proofBetaC p) (proofBetaD p) i = proofSeqCode p i := by
  exact Classical.choose_spec (Classical.choose_spec
    (beta_exists (proofSeqLast p) (proofSeqCode p)))

private noncomputable def packedProofCode (p : ProofTree) : Nat :=
  ccons (proofBetaC p) (ccons (proofBetaD p) (proofSeqLast p))

private noncomputable def proofLineEnv (p : ProofTree) (i : Nat) : Nat → Nat :=
  fun y => if y = 43 then i else if y = 42 then proofSeqLast p
    else if y = 41 then proofBetaD p else if y = 40 then proofBetaC p else env0 y

private theorem proofBeta_at_entry (p : ProofTree) {i : Nat} {φ : Formula}
    (hi : i ≤ proofSeqLast p) (hentry : (flattenProof p)[i]? = some φ) :
    beta (proofBetaC p) (proofBetaD p) i = encodeFormula φ := by
  rw [proofBeta_spec p i hi]
  simp [proofSeqCode, hentry]

private theorem proofLine_complete {p : ProofTree} {goal : Formula} (hp : check p = some goal)
    (i : Nat) (hi : i ≤ proofSeqLast p) :
    evalForm (proofLineEnv p i)
      (orF (justifiedF (Term.var 40) (Term.var 41) (Term.var 43))
        (specJustF (Term.var 40) (Term.var 41) (Term.var 43))) := by
  have hne := flatten_ne_nil_of_check hp
  have hpos : 0 < (flattenProof p).length := List.length_pos_iff.mpr hne
  have hilt : i < (flattenProof p).length := by
    dsimp [proofSeqLast] at hi
    omega
  have hjust := flatten_hilbert p goal hp i hilt
  apply (eval_orF _ _ _).2
  rcases hjust.2 with hax | hmp | hgen | hspec
  · left
    apply (eval_justifiedF_vars (proofLineEnv p i)).2
    change JustifiedNat (proofBetaC p) (proofBetaD p) i
    rcases hax with ⟨φ, hentry, haxiom⟩
    left
    have hβ := proofBeta_at_entry p hi hentry
    rw [hβ]
    exact axiomCodeShape_encode_of_isAxiom φ haxiom
  · left
    apply (eval_justifiedF_vars (proofLineEnv p i)).2
    change JustifiedNat (proofBetaC p) (proofBetaD p) i
    rcases hmp with ⟨j, k, a, b, hj, hk, himp, ha, hb⟩
    right; left
    refine ⟨j, k, hj, hk, ?_⟩
    have hjle : j ≤ proofSeqLast p := Nat.le_trans (Nat.le_of_lt hj) hi
    have hkle : k ≤ proofSeqLast p := Nat.le_trans (Nat.le_of_lt hk) hi
    have hjβ := proofBeta_at_entry p hjle himp
    have hkβ := proofBeta_at_entry p hkle ha
    have hiβ := proofBeta_at_entry p hi hb
    rw [hjβ, hkβ, hiβ]
    rfl
  · left
    apply (eval_justifiedF_vars (proofLineEnv p i)).2
    change JustifiedNat (proofBetaC p) (proofBetaD p) i
    rcases hgen with ⟨j, x, φ, hj, hbody, hall⟩
    right; right
    refine ⟨j, x, hj, ?_⟩
    have hjle : j ≤ proofSeqLast p := Nat.le_trans (Nat.le_of_lt hj) hi
    have hjβ := proofBeta_at_entry p hjle hbody
    have hiβ := proofBeta_at_entry p hi hall
    rw [hjβ, hiβ]
    rfl
  · right
    rcases hspec with ⟨j, x, t, φ, hj, ht, huni, hsub⟩
    have hjle : j ≤ proofSeqLast p := Nat.le_trans (Nat.le_of_lt hj) hi
    have hprev := proofBeta_at_entry p hjle huni
    have hcur := proofBeta_at_entry p hi hsub
    apply specJustF_complete (proofLineEnv p i) (proofBetaC p) (proofBetaD p)
      i j x t φ
    · simp [proofLineEnv]
    · simp [proofLineEnv]
    · simp [proofLineEnv]
    · exact hcur
    · exact hprev
    · exact hj
    · exact ht


/-- Every checked proof tree yields a beta-packed Hilbert certificate satisfying `proofRel`. -/
theorem proofRel_packed_of_check {p : ProofTree} {φ : Formula}
    (hp : check p = some φ) :
    evalForm env0 (proofRel (numeral (packedProofCode p))
      (numeral (encodeFormula φ))) := by
  unfold proofRel
  rw [eval_existsF]
  refine ⟨proofBetaC p, ?_⟩
  let e40 : Nat → Nat := fun y => if y = 40 then proofBetaC p else env0 y
  rw [eval_existsF]
  refine ⟨proofBetaD p, ?_⟩
  let e41 : Nat → Nat := fun y => if y = 41 then proofBetaD p else e40 y
  rw [eval_existsF]
  refine ⟨proofSeqLast p, ?_⟩
  let e42 : Nat → Nat := fun y => if y = 42 then proofSeqLast p else e41 y
  rw [eval_andF]
  constructor
  · apply (eval_eqCcons e42 (numeral (packedProofCode p)) (Term.var 40)
      (cconsTerm (Term.var 41) (Term.var 42))).2
    simp [e42, e41, e40, packedProofCode, evalTerm, evalTerm_numeral,
      eval_cconsTerm]
  · rw [eval_andF]
    constructor
    · have hlast := flatten_last_of_check p φ hp
      have hne := flatten_ne_nil_of_check hp
      have hentry : (flattenProof p)[proofSeqLast p]? = some φ := by
        dsimp [proofSeqLast]
        exact getLast?_some_getElem? hlast hne
      have hβ := proofBeta_at_entry p (Nat.le_refl _) hentry
      apply (eval_betaF e42 (Term.var 40) (Term.var 41) (Term.var 42)
        (numeral (encodeFormula φ))
        (by simp [termHasVar]) (by simp [termHasVar])
        (numeral_closed _ 51) (by simp [termHasVar])
        (by simp [termHasVar]) (by simp [termHasVar])
        (numeral_closed _ 52)).2
      simpa [e42, e41, e40, evalTerm, evalTerm_numeral] using hβ.symm
    · rw [evalForm_all]
      intro i
      rw [evalForm_imp]
      intro hle
      have hle' : i ≤ proofSeqLast p := by
        have hleSem := (eval_leF_var_var
          (fun y => if y = 43 then i else e42 y)
          (x := 43) (y := 42) (by decide) (by decide)).1 hle
        simpa [e42, e41, e40, evalTerm] using hleSem
      have hline := proofLine_complete hp i hle'
      simpa [proofLineEnv, e42, e41, e40] using hline
/-- A `proofRel` certificate built from a checked proof has the checked conclusion as its terminal code. -/
theorem proofRel_packed_target_of_check {p : ProofTree} {φ : Formula} {m : Nat}
    (hp : check p = some φ)
    (hrel : evalForm env0 (proofRel (numeral (packedProofCode p)) (numeral m))) :
    m = encodeFormula φ := by
  unfold proofRel at hrel
  rw [eval_existsF] at hrel
  rcases hrel with ⟨c, hrel⟩
  let e40 : Nat → Nat := fun y => if y = 40 then c else env0 y
  rw [eval_existsF] at hrel
  rcases hrel with ⟨d, hrel⟩
  let e41 : Nat → Nat := fun y => if y = 41 then d else e40 y
  rw [eval_existsF] at hrel
  rcases hrel with ⟨L, hrel⟩
  let e42 : Nat → Nat := fun y => if y = 42 then L else e41 y
  rw [eval_andF] at hrel
  rcases hrel with ⟨hpack, hrest⟩
  rw [eval_andF] at hrest
  rcases hrest with ⟨hterminal, _⟩
  have hpackEq : packedProofCode p = ccons c (ccons d L) := by
    have h := (eval_eqCcons e42 (numeral (packedProofCode p)) (Term.var 40)
      (cconsTerm (Term.var 41) (Term.var 42))).1 hpack
    simpa [e42, e41, e40, evalTerm, evalTerm_numeral, eval_cconsTerm] using h
  have houter := ccons_injective (by
    simpa [packedProofCode] using hpackEq)
  have hc : proofBetaC p = c := houter.1
  have hinner := ccons_injective houter.2
  have hd : proofBetaD p = d := hinner.1
  have hL : proofSeqLast p = L := hinner.2
  have htermEq : m = beta c d L := by
    have h := (eval_betaF e42 (Term.var 40) (Term.var 41) (Term.var 42)
      (numeral m)
      (by simp [termHasVar]) (by simp [termHasVar])
      (numeral_closed _ 51) (by simp [termHasVar])
      (by simp [termHasVar]) (by simp [termHasVar])
      (numeral_closed _ 52)).1 hterminal
    simpa [e42, e41, e40, evalTerm, evalTerm_numeral] using h
  have hlast := flatten_last_of_check p φ hp
  have hne := flatten_ne_nil_of_check hp
  have hentry : (flattenProof p)[proofSeqLast p]? = some φ := by
    dsimp [proofSeqLast]
    exact getLast?_some_getElem? hlast hne
  have hβ := proofBeta_at_entry p (Nat.le_refl _) hentry
  rw [← hc, ← hd, ← hL] at htermEq
  exact htermEq.trans hβ
def aliasZeroTermCode : Nat := 4

theorem uncpair_three : uncpair 3 = (0, 0) := by rfl

theorem decodeTerm_alias_zero_of_pos {fuel : Nat} (h : 0 < fuel) :
    decodeTerm fuel aliasZeroTermCode = some Term.zero := by
  cases fuel with
  | zero => omega
  | succ fuel => simp [decodeTerm, aliasZeroTermCode, uncpair_three]

theorem decodeTerm_alias_zero : decodeTerm? aliasZeroTermCode = some Term.zero := by
  apply decodeTerm_alias_zero_of_pos
  simp [aliasZeroTermCode]

def aliasEqZeroCode : Nat := ccons 0 (ccons aliasZeroTermCode aliasZeroTermCode)

def zeroEqZero : Formula := Formula.eq Term.zero Term.zero

theorem decodeFormula_alias_zeroEqZero :
    decodeFormula? aliasEqZeroCode = some zeroEqZero := by
  have hpos : 0 < aliasEqZeroCode :=
    Nat.zero_lt_of_ne_zero (by simp [aliasEqZeroCode, ccons_ne_zero])
  have hdec : decodeTerm aliasEqZeroCode aliasZeroTermCode = some Term.zero :=
    decodeTerm_alias_zero_of_pos hpos
  have hdec' : decodeTerm (ccons 0 (ccons 4 4)) 4 = some Term.zero := by
    simpa [aliasEqZeroCode, aliasZeroTermCode] using hdec
  simp [decodeFormula?, aliasEqZeroCode, zeroEqZero, decodeFormula,
    ccons_ne_zero, uncpair_pred_ccons, hdec', aliasZeroTermCode]

theorem zeroEqZero_valid : check (.ax zeroEqZero) = some zeroEqZero := by
  simp [zeroEqZero, check, eq_refl_axiom]

theorem isProofCode_alias_conclusion :
    isProofCode (encodeProof (.ax zeroEqZero)) aliasEqZeroCode = true := by
  unfold isProofCode
  rw [decodeProof?_encode, decodeFormula_alias_zeroEqZero]
  simp [zeroEqZero_valid]

theorem zeroEqZero_code_ne_alias : encodeFormula zeroEqZero ≠ aliasEqZeroCode := by
  intro h
  have ho := ccons_injective (by simpa [zeroEqZero, aliasEqZeroCode, encodeFormula] using h)
  have hi := ccons_injective ho.2
  have hz : ccons 0 0 = aliasZeroTermCode := hi.1
  have : 1 = 4 := by simpa [ccons, cpair, aliasZeroTermCode] using hz
  omega

theorem proofRel_pack_terminal {s m : Nat}
    (h : evalForm env0 (proofRel (numeral s) (numeral m))) :
    ∃ c d L, s = ccons c (ccons d L) ∧ m = beta c d L := by
  unfold proofRel at h
  rw [eval_existsF] at h
  rcases h with ⟨c, h⟩
  let e40 : Nat → Nat := fun y => if y = 40 then c else env0 y
  rw [eval_existsF] at h
  rcases h with ⟨d, h⟩
  let e41 : Nat → Nat := fun y => if y = 41 then d else e40 y
  rw [eval_existsF] at h
  rcases h with ⟨L, h⟩
  let e42 : Nat → Nat := fun y => if y = 42 then L else e41 y
  rw [eval_andF] at h
  rcases h with ⟨hpack, hrest⟩
  rw [eval_andF] at hrest
  rcases hrest with ⟨hterm, _⟩
  refine ⟨c, d, L, ?_, ?_⟩
  · have hp := (eval_eqCcons e42 (numeral s) (Term.var 40)
      (cconsTerm (Term.var 41) (Term.var 42))).1 hpack
    simpa [e42, e41, e40, evalTerm, evalTerm_numeral, eval_cconsTerm] using hp
  · have ht := (eval_betaF e42 (Term.var 40) (Term.var 41) (Term.var 42)
      (numeral m)
      (by simp [termHasVar]) (by simp [termHasVar]) (numeral_closed _ 51)
      (by simp [termHasVar]) (by simp [termHasVar]) (by simp [termHasVar])
      (numeral_closed _ 52)).1 hterm
    simpa [e42, e41, e40, evalTerm, evalTerm_numeral] using ht

theorem proofRel_target_unique {s m₁ m₂ : Nat}
    (h₁ : evalForm env0 (proofRel (numeral s) (numeral m₁)))
    (h₂ : evalForm env0 (proofRel (numeral s) (numeral m₂))) : m₁ = m₂ := by
  rcases proofRel_pack_terminal h₁ with ⟨c₁, d₁, L₁, hp₁, ht₁⟩
  rcases proofRel_pack_terminal h₂ with ⟨c₂, d₂, L₂, hp₂, ht₂⟩
  have ho := ccons_injective (hp₁.symm.trans hp₂)
  have hi := ccons_injective ho.2
  calc
    m₁ = beta c₁ d₁ L₁ := ht₁
    _ = beta c₂ d₂ L₂ := by rw [ho.1, hi.1, hi.2]
    _ = m₂ := ht₂.symm

theorem no_total_proofRecoding_bridge :
    ¬ ∃ ρ : Nat → Nat, ∀ n m,
      isProofCode n m = true ↔
        evalForm env0 (proofRel (numeral (ρ n)) (numeral m)) := by
  rintro ⟨ρ, hρ⟩
  have hc : isProofCode (encodeProof (.ax zeroEqZero)) (encodeFormula zeroEqZero) = true :=
    (isProofCode_iff (.ax zeroEqZero) zeroEqZero).2 zeroEqZero_valid
  have ha : isProofCode (encodeProof (.ax zeroEqZero)) aliasEqZeroCode = true :=
    isProofCode_alias_conclusion
  have hr₁ := (hρ (encodeProof (.ax zeroEqZero)) (encodeFormula zeroEqZero)).1 hc
  have hr₂ := (hρ (encodeProof (.ax zeroEqZero)) aliasEqZeroCode).1 ha
  exact zeroEqZero_code_ne_alias (proofRel_target_unique hr₁ hr₂)


private def rawTerm (n : Nat) : Term :=
  if hn : n = 0 then Term.zero
  else
    let p := uncpair (n - 1)
    if hp : ccons p.1 p.2 = n then
      match p.1 with
      | 0 => Term.zero
      | 1 => Term.succ (rawTerm p.2)
      | 2 =>
          if hq0 : p.2 = 0 then Term.zero else
          let q := uncpair (p.2 - 1)
          if hq : ccons q.1 q.2 = p.2 then Term.add (rawTerm q.1) (rawTerm q.2)
          else Term.zero
      | 3 =>
          if hq0 : p.2 = 0 then Term.zero else
          let q := uncpair (p.2 - 1)
          if hq : ccons q.1 q.2 = p.2 then Term.mul (rawTerm q.1) (rawTerm q.2)
          else Term.zero
      | 4 => Term.var p.2
      | _ => Term.zero
    else Term.zero
termination_by n
decreasing_by
  all_goals
    first
    | have ht := ccons_gt_tail (uncpair (n - 1)).1 (uncpair (n - 1)).2
      rw [hp] at ht
      exact ht
    | have hqhead := ccons_gt_head (uncpair ((uncpair (n - 1)).2 - 1)).1
          (uncpair ((uncpair (n - 1)).2 - 1)).2
      rw [hq] at hqhead
      have ht := ccons_gt_tail (uncpair (n - 1)).1 (uncpair (n - 1)).2
      rw [hp] at ht
      exact Nat.lt_trans hqhead ht
    | have hqtail := ccons_gt_tail (uncpair ((uncpair (n - 1)).2 - 1)).1
          (uncpair ((uncpair (n - 1)).2 - 1)).2
      rw [hq] at hqtail
      have ht := ccons_gt_tail (uncpair (n - 1)).1 (uncpair (n - 1)).2
      rw [hp] at ht
      exact Nat.lt_trans hqtail ht

private def rawFormula (n : Nat) : Formula :=
  if hn : n = 0 then Formula.eq Term.zero Term.zero
  else
    let p := uncpair (n - 1)
    if hp : ccons p.1 p.2 = n then
      match p.1 with
      | 0 =>
          if hq0 : p.2 = 0 then Formula.eq Term.zero Term.zero else
          let q := uncpair (p.2 - 1)
          if hq : ccons q.1 q.2 = p.2 then Formula.eq (rawTerm q.1) (rawTerm q.2)
          else Formula.eq Term.zero Term.zero
      | 1 => Formula.not (rawFormula p.2)
      | 2 =>
          if hq0 : p.2 = 0 then Formula.eq Term.zero Term.zero else
          let q := uncpair (p.2 - 1)
          if hq : ccons q.1 q.2 = p.2 then Formula.imp (rawFormula q.1) (rawFormula q.2)
          else Formula.eq Term.zero Term.zero
      | 3 =>
          if hq0 : p.2 = 0 then Formula.eq Term.zero Term.zero else
          let q := uncpair (p.2 - 1)
          if hq : ccons q.1 q.2 = p.2 then Formula.all q.1 (rawFormula q.2)
          else Formula.eq Term.zero Term.zero
      | _ => Formula.eq Term.zero Term.zero
    else Formula.eq Term.zero Term.zero
termination_by n
decreasing_by
  all_goals
    first
    | have ht := ccons_gt_tail (uncpair (n - 1)).1 (uncpair (n - 1)).2
      rw [hp] at ht
      exact ht
    | have hqhead := ccons_gt_head (uncpair ((uncpair (n - 1)).2 - 1)).1
          (uncpair ((uncpair (n - 1)).2 - 1)).2
      rw [hq] at hqhead
      have ht := ccons_gt_tail (uncpair (n - 1)).1 (uncpair (n - 1)).2
      rw [hp] at ht
      exact Nat.lt_trans hqhead ht
    | have hqtail := ccons_gt_tail (uncpair ((uncpair (n - 1)).2 - 1)).1
          (uncpair ((uncpair (n - 1)).2 - 1)).2
      rw [hq] at hqtail
      have ht := ccons_gt_tail (uncpair (n - 1)).1 (uncpair (n - 1)).2
      rw [hp] at ht
      exact Nat.lt_trans hqtail ht

private theorem rawTerm_zero : rawTerm (ccons 0 0) = Term.zero := by
  rw [rawTerm.eq_1]
  simp only [ccons_ne_zero, dite_false, uncpair_pred_ccons, dif_pos]

private theorem rawTerm_succ (a : Nat) : rawTerm (ccons 1 a) = Term.succ (rawTerm a) := by
  rw [rawTerm.eq_1]
  simp only [ccons_ne_zero, dite_false, uncpair_pred_ccons, dif_pos]

private theorem rawTerm_add (a b : Nat) :
    rawTerm (ccons 2 (ccons a b)) = Term.add (rawTerm a) (rawTerm b) := by
  rw [rawTerm.eq_1]
  simp only [ccons_ne_zero, dite_false, uncpair_pred_ccons, dif_pos]

private theorem rawTerm_mul (a b : Nat) :
    rawTerm (ccons 3 (ccons a b)) = Term.mul (rawTerm a) (rawTerm b) := by
  rw [rawTerm.eq_1]
  simp only [ccons_ne_zero, dite_false, uncpair_pred_ccons, dif_pos]

private theorem rawTerm_var (x : Nat) : rawTerm (ccons 4 x) = Term.var x := by
  rw [rawTerm.eq_1]
  simp only [ccons_ne_zero, dite_false, uncpair_pred_ccons, dif_pos]

private theorem rawFormula_eq (a b : Nat) :
    rawFormula (ccons 0 (ccons a b)) = Formula.eq (rawTerm a) (rawTerm b) := by
  rw [rawFormula.eq_1]
  simp only [ccons_ne_zero, dite_false, uncpair_pred_ccons, dif_pos]

private theorem rawFormula_not (a : Nat) :
    rawFormula (ccons 1 a) = Formula.not (rawFormula a) := by
  rw [rawFormula.eq_1]
  simp only [ccons_ne_zero, dite_false, uncpair_pred_ccons, dif_pos]

private theorem rawFormula_imp (a b : Nat) :
    rawFormula (ccons 2 (ccons a b)) = Formula.imp (rawFormula a) (rawFormula b) := by
  rw [rawFormula.eq_1]
  simp only [ccons_ne_zero, dite_false, uncpair_pred_ccons, dif_pos]

private theorem rawFormula_all (x a : Nat) :
    rawFormula (ccons 3 (ccons x a)) = Formula.all x (rawFormula a) := by
  rw [rawFormula.eq_1]
  simp only [ccons_ne_zero, dite_false, uncpair_pred_ccons, dif_pos]

private theorem rawTerm_encode : ∀ t : Term, rawTerm (encodeTerm t) = t
  | Term.zero => rawTerm_zero
  | Term.succ t => by rw [encodeTerm, rawTerm_succ, rawTerm_encode t]
  | Term.add s t => by rw [encodeTerm, rawTerm_add, rawTerm_encode s, rawTerm_encode t]
  | Term.mul s t => by rw [encodeTerm, rawTerm_mul, rawTerm_encode s, rawTerm_encode t]
  | Term.var x => rawTerm_var x

private theorem rawFormula_encode : ∀ φ : Formula, rawFormula (encodeFormula φ) = φ
  | Formula.eq s t => by rw [encodeFormula, rawFormula_eq, rawTerm_encode s, rawTerm_encode t]
  | Formula.not φ => by rw [encodeFormula, rawFormula_not, rawFormula_encode φ]
  | Formula.imp a b => by rw [encodeFormula, rawFormula_imp, rawFormula_encode a, rawFormula_encode b]
  | Formula.all x φ => by rw [encodeFormula, rawFormula_all, rawFormula_encode φ]

private theorem rawFormula_axiomCodeShape (n : Nat) (h : AxiomCodeShape n) :
    isAxiom (rawFormula n) = true := by
  rcases h with hq | hrefl | hid | hk | hs | hdne
  · rcases hq with h1 | h2 | h3 | h4 | h5 | h6 | h7
    · rw [h1, rawFormula_encode]; simp [isAxiom, isQAxiom]
    · rw [h2, rawFormula_encode]; simp [isAxiom, isQAxiom]
    · rw [h3, rawFormula_encode]; simp [isAxiom, isQAxiom]
    · rw [h4, rawFormula_encode]; simp [isAxiom, isQAxiom]
    · rw [h5, rawFormula_encode]; simp [isAxiom, isQAxiom]
    · rw [h6, rawFormula_encode]; simp [isAxiom, isQAxiom]
    · rw [h7, rawFormula_encode]; simp [isAxiom, isQAxiom]
  · rcases hrefl with ⟨a, rfl⟩
    rw [rawFormula_eq]
    exact eq_refl_axiom (rawTerm a)
  · rcases hid with ⟨a, rfl⟩
    rw [rawFormula_imp]
    simp [isAxiom, isAxId]
  · rcases hk with ⟨a, b, rfl⟩
    rw [rawFormula_imp, rawFormula_imp]
    simp [isAxiom, isAxK]
  · rcases hs with ⟨a, b, c, rfl⟩
    repeat' rw [rawFormula_imp]
    simp [isAxiom, isAxS]
  · rcases hdne with ⟨a, rfl⟩
    rw [rawFormula_imp, rawFormula_not, rawFormula_not]
    simp [isAxiom, isAxDNE]

private theorem rawFormula_axiom_sound (n : Nat) (h : AxiomCodeShape n) (env : Nat → Nat) :
    evalForm env (rawFormula n) := by
  exact check_sound (.ax (rawFormula n)) (rawFormula n) env (by
    simp [check, rawFormula_axiomCodeShape n h])

/-- A zero proof certificate cannot satisfy the beta-packed proof relation. -/
theorem proofRel_zero_false (t : Nat) :
    ¬ evalForm env0 (proofRel (numeral 0) (numeral t)) := by
  intro h
  unfold proofRel at h
  rw [eval_existsF] at h
  rcases h with ⟨c, h⟩
  rw [eval_existsF] at h
  rcases h with ⟨d, h⟩
  rw [eval_existsF] at h
  rcases h with ⟨L, h⟩
  rw [eval_andF] at h
  rcases h with ⟨heq, _⟩
  have he := (eval_eqCcons _ _ _ _).1 heq
  have he' : 0 = ccons c (ccons d L) := by
    simpa [evalTerm, evalTerm_numeral, eval_cconsTerm] using he
  exact (ccons_ne_zero c (ccons d L)) he'.symm

/-- Recode a decoded, checker-accepted recursive proof into the beta-packed Hilbert certificate expected by `proofRel`. -/
noncomputable def proofRecoding (n : Nat) : Nat :=
  match decodeProof? n with
  | none => 0
  | some p =>
      match check p with
      | none => 0
      | some _ => packedProofCode p

/-- Canonical encoded proof trees recode to their packed Hilbert certificate when the checker accepts them. -/
theorem proofRecoding_encode_of_check {p : ProofTree} {φ : Formula}
    (hp : check p = some φ) :
    proofRecoding (encodeProof p) = packedProofCode p := by
  simp [proofRecoding, decodeProof?_encode, hp]

/-- The sound-and-complete recoding bridge on canonical formula codes. -/
theorem isProofCode_iff_proofRel_recoded_formula (n : Nat) (φ : Formula) :
    isProofCode n (encodeFormula φ) = true ↔
      evalForm env0 (proofRel (numeral (proofRecoding n))
        (numeral (encodeFormula φ))) := by
  cases hdec : decodeProof? n with
  | none =>
      constructor
      · intro h
        simp [isProofCode, hdec] at h
      · intro h
        apply False.elim
        apply proofRel_zero_false (encodeFormula φ)
        simpa [proofRecoding, hdec] using h
  | some p =>
      cases hcheck : check p with
      | none =>
          constructor
          · intro h
            simp [isProofCode, hdec, hcheck, decodeFormula?_encode] at h
          · intro h
            apply False.elim
            apply proofRel_zero_false (encodeFormula φ)
            simpa [proofRecoding, hdec, hcheck] using h
      | some ψ =>
          constructor
          · intro h
            have hpφ : check p = some φ := by
              simpa [isProofCode, hdec, decodeFormula?_encode] using h
            have hrel := proofRel_packed_of_check hpφ
            simpa [proofRecoding, hdec, hcheck] using hrel
          · intro h
            have hrel : evalForm env0 (proofRel (numeral (packedProofCode p))
                (numeral (encodeFormula φ))) := by
              simpa [proofRecoding, hdec, hcheck] using h
            have hcode : encodeFormula φ = encodeFormula ψ :=
              proofRel_packed_target_of_check hcheck hrel
            have hφψ : φ = ψ := encodeFormula_injective hcode
            have hcheck' : check p = some φ := by simpa [hφψ] using hcheck
            simpa [isProofCode, hdec, decodeFormula?_encode, hcheck']

/-- The bridge in the opaque `formulaCode` vocabulary used by `bewOf`. -/
theorem isProofCode_iff_proofRel_recoded_formulaCode (n : Nat) (φ : Formula) :
    isProofCode n (formulaCode φ) = true ↔
      evalForm env0 (proofRel (numeral (proofRecoding n))
        (numeral (formulaCode φ))) := by
  rw [formulaCode_eq]
  exact isProofCode_iff_proofRel_recoded_formula n φ
end OperatorKO7.Meta.DistinctionBoundary.GodelArith
















namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith
open Term

private theorem termSubstTraceAt_raw_sound (x u c d L : Nat)
    (htrace : TermSubstTraceAt c d L x u) :
    ∀ i, i ≤ L → ∀ inC outC,
      beta c d i = ccons inC outC →
      rawTerm outC = substTerm x (rawTerm u) (rawTerm inC) := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
      intro hi inC outC hentry
      rcases htrace i hi with ⟨inC', outC', hentry', hjust⟩
      have hp : inC = inC' ∧ outC = outC' :=
        ccons_injective (hentry.symm.trans hentry'.symm)
      rcases hp with ⟨rfl, rfl⟩
      rcases hjust with hzero | hsucc | hadd | hmul | hvar
      · rw [hzero.1, hzero.2, rawTerm_zero]
        rfl
      · rcases hsucc with ⟨a, a', j, hin, hout, hj, hβ⟩
        have hjL : j ≤ L := Nat.le_trans (Nat.le_of_lt hj) hi
        have hchild := ih j hj hjL a a' hβ.symm
        rw [hin, hout, rawTerm_succ, rawTerm_succ, hchild]
        rfl
      · rcases hadd with ⟨a, b, a', b', j, k, hin, hout, hj, hk, hβj, hβk⟩
        have hjL : j ≤ L := Nat.le_trans (Nat.le_of_lt hj) hi
        have hkL : k ≤ L := Nat.le_trans (Nat.le_of_lt hk) hi
        have hleft := ih j hj hjL a a' hβj.symm
        have hright := ih k hk hkL b b' hβk.symm
        rw [hin, hout, rawTerm_add, rawTerm_add, hleft, hright]
        rfl
      · rcases hmul with ⟨a, b, a', b', j, k, hin, hout, hj, hk, hβj, hβk⟩
        have hjL : j ≤ L := Nat.le_trans (Nat.le_of_lt hj) hi
        have hkL : k ≤ L := Nat.le_trans (Nat.le_of_lt hk) hi
        have hleft := ih j hj hjL a a' hβj.symm
        have hright := ih k hk hkL b b' hβk.symm
        rw [hin, hout, rawTerm_mul, rawTerm_mul, hleft, hright]
        rfl
      · rcases hvar with hhit | hmiss
        · rcases hhit with ⟨hin, hout⟩
          rw [hin, hout, rawTerm_var]
          simp [substTerm]
        · rcases hmiss with ⟨⟨k, hin, hk⟩, hout⟩
          rw [hout, hin, rawTerm_var]
          simp [substTerm, hk]

#print axioms termSubstTraceAt_raw_sound
end OperatorKO7.Meta.DistinctionBoundary.GodelArith

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith
open Term

private theorem termSubstGraphAt_raw_sound (x u inC outC : Nat)
    (h : TermSubstGraphAt x u inC outC) :
    rawTerm outC = substTerm x (rawTerm u) (rawTerm inC) := by
  rcases h with ⟨c, d, L, hlast, htrace⟩
  exact termSubstTraceAt_raw_sound x u c d L htrace L (Nat.le_refl L)
    inC outC hlast.symm

private theorem formSubstTraceAt_raw_sound (x u c d L : Nat)
    (htrace : FormSubstTraceAt c d L x u) :
    ∀ i, i ≤ L → ∀ inC outC,
      beta c d i = ccons inC outC →
      rawFormula outC = substForm x (rawTerm u) (rawFormula inC) := by
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
        have ha' := termSubstGraphAt_raw_sound x u a a' ha
        have hb' := termSubstGraphAt_raw_sound x u b b' hb
        rw [hin, hout, rawFormula_eq, rawFormula_eq, ha', hb']
        rfl
      · rcases hnot with ⟨a, a', j, hin, hout, hj, hβ⟩
        have hjL : j ≤ L := Nat.le_trans (Nat.le_of_lt hj) hi
        have hchild := ih j hj hjL a a' hβ.symm
        rw [hin, hout, rawFormula_not, rawFormula_not, hchild]
        rfl
      · rcases himp with ⟨a, b, a', b', j, k, hin, hout, hj, hk, hβj, hβk⟩
        have hjL : j ≤ L := Nat.le_trans (Nat.le_of_lt hj) hi
        have hkL : k ≤ L := Nat.le_trans (Nat.le_of_lt hk) hi
        have ha' := ih j hj hjL a a' hβj.symm
        have hb' := ih k hk hkL b b' hβk.symm
        rw [hin, hout, rawFormula_imp, rawFormula_imp, ha', hb']
        rfl
      · rcases hall with ⟨y, a, a', j, hin, hcases⟩
        rcases hcases with hhit | hmiss
        · rcases hhit with ⟨hyx, hout⟩
          subst y
          rw [hout, hin, rawFormula_all]
          simp [substForm]
        · rcases hmiss with ⟨hyx, hout, hj, hβ⟩
          have hjL : j ≤ L := Nat.le_trans (Nat.le_of_lt hj) hi
          have hchild := ih j hj hjL a a' hβ.symm
          rw [hin, hout, rawFormula_all, rawFormula_all, hchild]
          simp [substForm, hyx]

private theorem formSubstGraphAt_raw_sound (x u inC outC : Nat)
    (h : ∃ c d L, ccons inC outC = beta c d L ∧ FormSubstTraceAt c d L x u) :
    rawFormula outC = substForm x (rawTerm u) (rawFormula inC) := by
  rcases h with ⟨c, d, L, hlast, htrace⟩
  exact formSubstTraceAt_raw_sound x u c d L htrace L (Nat.le_refl L)
    inC outC hlast.symm

#print axioms formSubstTraceAt_raw_sound
end OperatorKO7.Meta.DistinctionBoundary.GodelArith

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith
open Term

private theorem termClosedTrace_raw_closed (c d L : Nat)
    (htrace : TermClosedTrace c d L) :
    ∀ i, i ≤ L → isClosedTerm (rawTerm (beta c d i)) = true := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
      intro hi
      rcases htrace i hi with hzero | hsucc | hadd | hmul
      · rw [hzero, rawTerm_zero]
        rfl
      · rcases hsucc with ⟨a, j, hcur, hj, hchildCode⟩
        have hjL : j ≤ L := Nat.le_trans (Nat.le_of_lt hj) hi
        have hchild := ih j hj hjL
        rw [hcur, rawTerm_succ, hchildCode]
        simp [isClosedTerm, hchild]
      · rcases hadd with ⟨a, b, j, k, hcur, hj, hk, ha, hb⟩
        have hjL : j ≤ L := Nat.le_trans (Nat.le_of_lt hj) hi
        have hkL : k ≤ L := Nat.le_trans (Nat.le_of_lt hk) hi
        have hja := ih j hj hjL
        have hkb := ih k hk hkL
        rw [hcur, rawTerm_add, ha, hb]
        simp [isClosedTerm, hja, hkb]
      · rcases hmul with ⟨a, b, j, k, hcur, hj, hk, ha, hb⟩
        have hjL : j ≤ L := Nat.le_trans (Nat.le_of_lt hj) hi
        have hkL : k ≤ L := Nat.le_trans (Nat.le_of_lt hk) hi
        have hja := ih j hj hjL
        have hkb := ih k hk hkL
        rw [hcur, rawTerm_mul, ha, hb]
        simp [isClosedTerm, hja, hkb]

#print axioms termClosedTrace_raw_closed
end OperatorKO7.Meta.DistinctionBoundary.GodelArith

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith
open Term

private def SpecJustifiedNat (c d i : Nat) : Prop :=
  ∃ j x body outC u,
    outC = beta c d i ∧
    j < i ∧
    beta c d j = ccons 3 (ccons x body) ∧
    (∃ c' d' L', ccons body outC = beta c' d' L' ∧
      FormSubstTraceAt c' d' L' x u) ∧
    (∃ c'' d'' L'', u = beta c'' d'' L'' ∧ TermClosedTrace c'' d'' L'')

private theorem eval_specJustF_vars (env : Nat → Nat) :
    evalForm env (specJustF (Term.var 40) (Term.var 41) (Term.var 43)) ↔
      SpecJustifiedNat (env 40) (env 41) (env 43) := by
  simp [specJustF, SpecJustifiedNat, eval_existsF, eval_andF,
    eval_betaF_four_vars, eval_ltF_var_var, eval_eqCcons, eval_cconsTerm,
    eval_formSubstAtClosed_allVars, eval_termClosedPack_var65,
    evalTerm, evalTerm_numeral]

#print axioms eval_specJustF_vars
end OperatorKO7.Meta.DistinctionBoundary.GodelArith

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith
open Term

private def rawProofSeq (c d L : Nat) : List Formula :=
  (List.range (L + 1)).map (fun i => rawFormula (beta c d i))

private theorem rawProofSeq_length (c d L : Nat) :
    (rawProofSeq c d L).length = L + 1 := by
  simp [rawProofSeq]

private theorem rawProofSeq_get (c d L i : Nat) (hi : i ≤ L) :
    (rawProofSeq c d L)[i]? = some (rawFormula (beta c d i)) := by
  unfold rawProofSeq
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  rfl

private theorem rawProofSeq_ne_nil (c d L : Nat) : rawProofSeq c d L ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [rawProofSeq] at this

private theorem rawProofSeq_last (c d L : Nat) :
    (rawProofSeq c d L).getLast? = some (rawFormula (beta c d L)) := by
  simp [rawProofSeq, List.getLast?_map, List.getLast?_range]

private theorem rawProofSeq_hilbert (c d L : Nat)
    (hlines : ∀ i, i ≤ L → JustifiedNat c d i ∨ SpecJustifiedNat c d i) :
    HilbertSeq (rawProofSeq c d L) := by
  intro i hi
  have hiL : i ≤ L := by
    rw [rawProofSeq_length] at hi
    omega
  refine ⟨hi, ?_⟩
  rcases hlines i hiL with hjust | hspec
  · rcases hjust with hax | hmp | hgen
    · exact Or.inl ⟨rawFormula (beta c d i), rawProofSeq_get c d L i hiL,
        rawFormula_axiomCodeShape _ hax⟩
    · rcases hmp with ⟨j, k, hj, hk, hcode⟩
      refine Or.inr (Or.inl ⟨j, k, rawFormula (beta c d k),
        rawFormula (beta c d i), hj, hk, ?_, ?_, ?_⟩)
      · rw [rawProofSeq_get c d L j (Nat.le_trans (Nat.le_of_lt hj) hiL)]
        rw [hcode, rawFormula_imp]
      · exact rawProofSeq_get c d L k (Nat.le_trans (Nat.le_of_lt hk) hiL)
      · exact rawProofSeq_get c d L i hiL
    · rcases hgen with ⟨j, x, hj, hcode⟩
      refine Or.inr (Or.inr (Or.inl ⟨j, x, rawFormula (beta c d j), hj, ?_, ?_⟩))
      · exact rawProofSeq_get c d L j (Nat.le_trans (Nat.le_of_lt hj) hiL)
      · rw [rawProofSeq_get c d L i hiL]
        rw [hcode, rawFormula_all]
  · rcases hspec with ⟨j, x, body, outC, u, hout, hj, hprev, hsubst, hclosed⟩
    rcases hsubst with ⟨sc, sd, sL, hsubstLast, hsubstTrace⟩
    rcases hclosed with ⟨tc, td, tL, hu, hclosedTrace⟩
    have hsubstSem := formSubstTraceAt_raw_sound x u sc sd sL hsubstTrace
      sL (Nat.le_refl sL) body outC hsubstLast.symm
    have htClosed0 := termClosedTrace_raw_closed tc td tL hclosedTrace tL (Nat.le_refl tL)
    have htClosed : isClosedTerm (rawTerm u) = true := by
      rw [hu]
      exact htClosed0
    refine Or.inr (Or.inr (Or.inr ⟨j, x, rawTerm u, rawFormula body, hj,
      htClosed, ?_, ?_⟩))
    · rw [rawProofSeq_get c d L j (Nat.le_trans (Nat.le_of_lt hj) hiL)]
      rw [hprev, rawFormula_all]
    · rw [rawProofSeq_get c d L i hiL]
      rw [← hout]
      exact congrArg some hsubstSem

#print axioms rawProofSeq_hilbert
end OperatorKO7.Meta.DistinctionBoundary.GodelArith

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith
open Term

/-- Any beta-packed object-language proof certificate ending at `m` reconstructs a real proof of the interpreted formula `rawFormula m`. -/
theorem proofRel_implies_provable_raw {s m : Nat}
    (hrel : evalForm env0 (proofRel (numeral s) (numeral m))) :
    Provable (rawFormula m) := by
  unfold proofRel at hrel
  rw [eval_existsF] at hrel
  rcases hrel with ⟨c, hrel⟩
  let e40 : Nat → Nat := fun y => if y = 40 then c else env0 y
  rw [eval_existsF] at hrel
  rcases hrel with ⟨d, hrel⟩
  let e41 : Nat → Nat := fun y => if y = 41 then d else e40 y
  rw [eval_existsF] at hrel
  rcases hrel with ⟨L, hrel⟩
  let e42 : Nat → Nat := fun y => if y = 42 then L else e41 y
  rw [eval_andF] at hrel
  rcases hrel with ⟨_hpack, hrest⟩
  rw [eval_andF] at hrest
  rcases hrest with ⟨hterminal, hall⟩
  have hm : m = beta c d L := by
    have ht := (eval_betaF e42 (Term.var 40) (Term.var 41) (Term.var 42)
      (numeral m)
      (by simp [termHasVar]) (by simp [termHasVar]) (numeral_closed _ 51)
      (by simp [termHasVar]) (by simp [termHasVar]) (by simp [termHasVar])
      (numeral_closed _ 52)).1 hterminal
    simpa [e42, e41, e40, evalTerm, evalTerm_numeral] using ht
  have hlines : ∀ i, i ≤ L → JustifiedNat c d i ∨ SpecJustifiedNat c d i := by
    intro i hi
    have halli := (evalForm_all e42 43 _).1 hall i
    rw [evalForm_imp] at halli
    let ei : Nat → Nat := fun y => if y = 43 then i else e42 y
    have hle : evalForm ei (leF (Term.var 43) (Term.var 42)) := by
      apply (eval_leF_var_var ei (x := 43) (y := 42) (by decide) (by decide)).2
      simpa [ei, e42, e41, e40] using hi
    have hor := halli hle
    rcases (eval_orF ei _ _).1 hor with hj | hs
    · left
      have := (eval_justifiedF_vars ei).1 hj
      simpa [ei, e42, e41, e40] using this
    · right
      have := (eval_specJustF_vars ei).1 hs
      simpa [ei, e42, e41, e40] using this
  have hseq := rawProofSeq_hilbert c d L hlines
  apply hilbert_implies_provable
  refine ⟨rawProofSeq c d L, ?_, rawProofSeq_ne_nil c d L, hseq⟩
  rw [hm, rawProofSeq_last]

/-- Arbitrary `proofRel` witnesses are sound at canonical formula codes. -/
theorem proofRel_implies_provable {s : Nat} {φ : Formula}
    (hrel : evalForm env0 (proofRel (numeral s) (numeral (encodeFormula φ)))) :
    Provable φ := by
  have h := proofRel_implies_provable_raw hrel
  simpa [rawFormula_encode] using h

#print axioms proofRel_implies_provable_raw
#print axioms proofRel_implies_provable
end OperatorKO7.Meta.DistinctionBoundary.GodelArith

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith
open Term

/-- Updating an environment at a variable absent from a formula preserves its truth value. -/
theorem evalForm_update_fresh (env : Nat → Nat) (x n : Nat) :
    ∀ φ : Formula, formHasVar x φ = false →
      (evalForm (envUpdate env x n) φ ↔ evalForm env φ)
  | Formula.eq s t, h => by
      simp [formHasVar, Bool.or_eq_false_iff] at h
      have hs := evalTerm_fresh x s h.1 env n
      have ht := evalTerm_fresh x t h.2 env n
      simpa [evalForm, envUpdate] using congrArg₂ Eq hs ht
  | Formula.not φ, h => by
      simp [formHasVar] at h
      simpa [evalForm] using not_congr (evalForm_update_fresh env x n φ h)
  | Formula.imp φ ψ, h => by
      simp [formHasVar, Bool.or_eq_false_iff] at h
      simpa [evalForm] using
        imp_congr (evalForm_update_fresh env x n φ h.1)
          (evalForm_update_fresh env x n ψ h.2)
  | Formula.all y φ, h => by
      by_cases hyx : y = x
      · subst y
        dsimp [evalForm]
        constructor
        · intro hall k
          have henv : ∀ z,
              envUpdate (envUpdate env x n) x k z = envUpdate env x k z := by
            intro z
            by_cases hz : z = x <;> simp [envUpdate, hz]
          exact (evalForm_env_eq_aux φ henv).1 (hall k)
        · intro hall k
          have henv : ∀ z,
              envUpdate env x k z = envUpdate (envUpdate env x n) x k z := by
            intro z
            by_cases hz : z = x <;> simp [envUpdate, hz]
          exact (evalForm_env_eq_aux φ henv).1 (hall k)
      · simp [formHasVar, hyx] at h
        dsimp [evalForm]
        constructor
        · intro hall k
          have hcomm : ∀ z,
              envUpdate (envUpdate env x n) y k z =
                envUpdate (envUpdate env y k) x n z := by
            intro z
            by_cases hzx : z = x
            · subst z
              simp [envUpdate, Ne.symm hyx]
            · by_cases hzy : z = y
              · subst z
                simp [envUpdate, hzx]
              · simp [envUpdate, hzx, hzy]
          have hleft : evalForm (envUpdate (envUpdate env y k) x n) φ :=
            (evalForm_env_eq_aux φ hcomm).1 (hall k)
          exact (evalForm_update_fresh (envUpdate env y k) x n φ h).1 hleft
        · intro hall k
          have hfresh := (evalForm_update_fresh (envUpdate env y k) x n φ h).2 (hall k)
          have hcomm : ∀ z,
              envUpdate (envUpdate env y k) x n z =
                envUpdate (envUpdate env x n) y k z := by
            intro z
            by_cases hzx : z = x
            · subst z
              simp [envUpdate, Ne.symm hyx]
            · by_cases hzy : z = y
              · subst z
                simp [envUpdate, hzx]
              · simp [envUpdate, hzx, hzy]
          exact (evalForm_env_eq_aux φ hcomm).1 hfresh

private theorem proofLineFormula_fresh_zero :
    formHasVar 0
      (orF (justifiedF (Term.var 40) (Term.var 41) (Term.var 43))
        (specJustF (Term.var 40) (Term.var 41) (Term.var 43))) = false := by
  decide

/-- A checked proof can be packed directly under the open variable-0 witness environment used by `bewOf`. -/
theorem proofRel_packed_of_check_var0 {p : ProofTree} {φ : Formula}
    (hp : check p = some φ) :
    evalForm (envUpdate env0 0 (packedProofCode p))
      (proofRel (Term.var 0) (numeral (encodeFormula φ))) := by
  unfold proofRel
  rw [eval_existsF]
  refine ⟨proofBetaC p, ?_⟩
  let e0 : Nat → Nat := envUpdate env0 0 (packedProofCode p)
  let e40 : Nat → Nat := fun y => if y = 40 then proofBetaC p else e0 y
  rw [eval_existsF]
  refine ⟨proofBetaD p, ?_⟩
  let e41 : Nat → Nat := fun y => if y = 41 then proofBetaD p else e40 y
  rw [eval_existsF]
  refine ⟨proofSeqLast p, ?_⟩
  let e42 : Nat → Nat := fun y => if y = 42 then proofSeqLast p else e41 y
  rw [eval_andF]
  constructor
  · apply (eval_eqCcons e42 (Term.var 0) (Term.var 40)
      (cconsTerm (Term.var 41) (Term.var 42))).2
    simp [e42, e41, e40, e0, envUpdate, packedProofCode,
      evalTerm, eval_cconsTerm]
  · rw [eval_andF]
    constructor
    · have hlast := flatten_last_of_check p φ hp
      have hne := flatten_ne_nil_of_check hp
      have hentry : (flattenProof p)[proofSeqLast p]? = some φ := by
        dsimp [proofSeqLast]
        exact getLast?_some_getElem? hlast hne
      have hβ := proofBeta_at_entry p (Nat.le_refl _) hentry
      apply (eval_betaF e42 (Term.var 40) (Term.var 41) (Term.var 42)
        (numeral (encodeFormula φ))
        (by simp [termHasVar]) (by simp [termHasVar])
        (numeral_closed _ 51) (by simp [termHasVar])
        (by simp [termHasVar]) (by simp [termHasVar])
        (numeral_closed _ 52)).2
      simpa [e42, e41, e40, e0, evalTerm, evalTerm_numeral] using hβ.symm
    · rw [evalForm_all]
      intro i
      rw [evalForm_imp]
      intro hle
      have hle' : i ≤ proofSeqLast p := by
        have hleSem := (eval_leF_var_var
          (fun y => if y = 43 then i else e42 y)
          (x := 43) (y := 42) (by decide) (by decide)).1 hle
        simpa [e42, e41, e40, e0, evalTerm] using hleSem
      have hline := proofLine_complete hp i hle'
      let targetEnv : Nat → Nat := fun y => if y = 43 then i else e42 y
      let baseEnv : Nat → Nat := proofLineEnv p i
      have hupdated : evalForm (envUpdate baseEnv 0 (packedProofCode p))
          (orF (justifiedF (Term.var 40) (Term.var 41) (Term.var 43))
            (specJustF (Term.var 40) (Term.var 41) (Term.var 43))) :=
        (evalForm_update_fresh baseEnv 0 (packedProofCode p) _
          proofLineFormula_fresh_zero).2 hline
      have henv : ∀ z,
          envUpdate baseEnv 0 (packedProofCode p) z = targetEnv z := by
        intro z
        by_cases hz0 : z = 0
        · subst z
          simp [baseEnv, targetEnv, proofLineEnv, e42, e41, e40, e0, envUpdate]
        · by_cases hz43 : z = 43
          · subst z
            simp [baseEnv, targetEnv, proofLineEnv, e42, e41, e40, e0, envUpdate]
          · by_cases hz42 : z = 42
            · subst z
              simp [baseEnv, targetEnv, proofLineEnv, e42, e41, e40, e0, envUpdate]
            · by_cases hz41 : z = 41
              · subst z
                simp [baseEnv, targetEnv, proofLineEnv, e42, e41, e40, e0, envUpdate]
              · by_cases hz40 : z = 40
                · subst z
                  simp [baseEnv, targetEnv, proofLineEnv, e42, e41, e40, e0, envUpdate]
                · simp [baseEnv, targetEnv, proofLineEnv, e42, e41, e40, e0,
                    envUpdate, hz0, hz43, hz42, hz41, hz40]
      exact (evalForm_env_eq_aux _ henv).1 hupdated

/-- Any `proofRel` certificate under the open variable-0 witness environment is sound at a closed numeric conclusion. -/
theorem proofRel_var0_implies_provable_raw (env : Nat → Nat) {m : Nat}
    (hrel : evalForm env (proofRel (Term.var 0) (numeral m))) :
    Provable (rawFormula m) := by
  unfold proofRel at hrel
  rw [eval_existsF] at hrel
  rcases hrel with ⟨c, hrel⟩
  let e40 : Nat → Nat := fun y => if y = 40 then c else env y
  rw [eval_existsF] at hrel
  rcases hrel with ⟨d, hrel⟩
  let e41 : Nat → Nat := fun y => if y = 41 then d else e40 y
  rw [eval_existsF] at hrel
  rcases hrel with ⟨L, hrel⟩
  let e42 : Nat → Nat := fun y => if y = 42 then L else e41 y
  rw [eval_andF] at hrel
  rcases hrel with ⟨_hpack, hrest⟩
  rw [eval_andF] at hrest
  rcases hrest with ⟨hterminal, hall⟩
  have hm : m = beta c d L := by
    have ht := (eval_betaF e42 (Term.var 40) (Term.var 41) (Term.var 42)
      (numeral m)
      (by simp [termHasVar]) (by simp [termHasVar]) (numeral_closed _ 51)
      (by simp [termHasVar]) (by simp [termHasVar]) (by simp [termHasVar])
      (numeral_closed _ 52)).1 hterminal
    simpa [e42, e41, e40, evalTerm, evalTerm_numeral] using ht
  have hlines : ∀ i, i ≤ L → JustifiedNat c d i ∨ SpecJustifiedNat c d i := by
    intro i hi
    have halli := (evalForm_all e42 43 _).1 hall i
    rw [evalForm_imp] at halli
    let ei : Nat → Nat := fun y => if y = 43 then i else e42 y
    have hle : evalForm ei (leF (Term.var 43) (Term.var 42)) := by
      apply (eval_leF_var_var ei (x := 43) (y := 42) (by decide) (by decide)).2
      simpa [ei, e42, e41, e40] using hi
    have hor := halli hle
    rcases (eval_orF ei _ _).1 hor with hj | hs
    · left
      have := (eval_justifiedF_vars ei).1 hj
      simpa [ei, e42, e41, e40] using this
    · right
      have := (eval_specJustF_vars ei).1 hs
      simpa [ei, e42, e41, e40] using this
  have hseq := rawProofSeq_hilbert c d L hlines
  apply hilbert_implies_provable
  refine ⟨rawProofSeq c d L, ?_, rawProofSeq_ne_nil c d L, hseq⟩
  rw [hm, rawProofSeq_last]

/-- Open-witness soundness specialized to canonical formula codes. -/
theorem proofRel_var0_implies_provable (env : Nat → Nat) {φ : Formula}
    (hrel : evalForm env (proofRel (Term.var 0) (numeral (encodeFormula φ)))) :
    Provable φ := by
  have h := proofRel_var0_implies_provable_raw env hrel
  simpa [rawFormula_encode] using h

end OperatorKO7.Meta.DistinctionBoundary.GodelArith

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith
open Term

private theorem proofLineFormula_fresh_one :
    formHasVar 1
      (orF (justifiedF (Term.var 40) (Term.var 41) (Term.var 43))
        (specJustF (Term.var 40) (Term.var 41) (Term.var 43))) = false := by
  decide

private theorem proofLineFormula_fresh_two :
    formHasVar 2
      (orF (justifiedF (Term.var 40) (Term.var 41) (Term.var 43))
        (specJustF (Term.var 40) (Term.var 41) (Term.var 43))) = false := by
  decide

/-- A checked proof is valid under the variable-1 proof witness and variable-2 conclusion environment used by the Gödel matrix. -/
theorem proofRel_packed_of_check_vars12 {p : ProofTree} {φ : Formula}
    (hp : check p = some φ) :
    evalForm (envUpdate (envUpdate env0 1 (packedProofCode p)) 2 (encodeFormula φ))
      (proofRel (Term.var 1) (Term.var 2)) := by
  unfold proofRel
  rw [eval_existsF]
  refine ⟨proofBetaC p, ?_⟩
  let e12 : Nat → Nat :=
    envUpdate (envUpdate env0 1 (packedProofCode p)) 2 (encodeFormula φ)
  let e40 : Nat → Nat := fun y => if y = 40 then proofBetaC p else e12 y
  rw [eval_existsF]
  refine ⟨proofBetaD p, ?_⟩
  let e41 : Nat → Nat := fun y => if y = 41 then proofBetaD p else e40 y
  rw [eval_existsF]
  refine ⟨proofSeqLast p, ?_⟩
  let e42 : Nat → Nat := fun y => if y = 42 then proofSeqLast p else e41 y
  rw [eval_andF]
  constructor
  · apply (eval_eqCcons e42 (Term.var 1) (Term.var 40)
      (cconsTerm (Term.var 41) (Term.var 42))).2
    simp [e42, e41, e40, e12, envUpdate, packedProofCode,
      evalTerm, eval_cconsTerm]
  · rw [eval_andF]
    constructor
    · have hlast := flatten_last_of_check p φ hp
      have hne := flatten_ne_nil_of_check hp
      have hentry : (flattenProof p)[proofSeqLast p]? = some φ := by
        dsimp [proofSeqLast]
        exact getLast?_some_getElem? hlast hne
      have hβ := proofBeta_at_entry p (Nat.le_refl _) hentry
      apply (eval_betaF e42 (Term.var 40) (Term.var 41) (Term.var 42)
        (Term.var 2)
        (by simp [termHasVar]) (by simp [termHasVar]) (by simp [termHasVar])
        (by simp [termHasVar]) (by simp [termHasVar]) (by simp [termHasVar])
        (by simp [termHasVar])).2
      simpa [e42, e41, e40, e12, envUpdate, evalTerm] using hβ.symm
    · rw [evalForm_all]
      intro i
      rw [evalForm_imp]
      intro hle
      have hle' : i ≤ proofSeqLast p := by
        have hleSem := (eval_leF_var_var
          (fun y => if y = 43 then i else e42 y)
          (x := 43) (y := 42) (by decide) (by decide)).1 hle
        simpa [e42, e41, e40, e12, evalTerm] using hleSem
      have hline := proofLine_complete hp i hle'
      let targetEnv : Nat → Nat := fun y => if y = 43 then i else e42 y
      let baseEnv : Nat → Nat := proofLineEnv p i
      have h1 : evalForm (envUpdate baseEnv 1 (packedProofCode p))
          (orF (justifiedF (Term.var 40) (Term.var 41) (Term.var 43))
            (specJustF (Term.var 40) (Term.var 41) (Term.var 43))) :=
        (evalForm_update_fresh baseEnv 1 (packedProofCode p) _
          proofLineFormula_fresh_one).2 hline
      have h12 : evalForm
          (envUpdate (envUpdate baseEnv 1 (packedProofCode p)) 2 (encodeFormula φ))
          (orF (justifiedF (Term.var 40) (Term.var 41) (Term.var 43))
            (specJustF (Term.var 40) (Term.var 41) (Term.var 43))) :=
        (evalForm_update_fresh (envUpdate baseEnv 1 (packedProofCode p))
          2 (encodeFormula φ) _ proofLineFormula_fresh_two).2 h1
      have henv : ∀ z,
          envUpdate (envUpdate baseEnv 1 (packedProofCode p)) 2 (encodeFormula φ) z =
            targetEnv z := by
        intro z
        by_cases hz1 : z = 1
        · subst z
          simp [baseEnv, targetEnv, proofLineEnv, e42, e41, e40, e12, envUpdate]
        · by_cases hz2 : z = 2
          · subst z
            simp [baseEnv, targetEnv, proofLineEnv, e42, e41, e40, e12, envUpdate]
          · by_cases hz43 : z = 43
            · subst z
              simp [baseEnv, targetEnv, proofLineEnv, e42, e41, e40, e12, envUpdate]
            · by_cases hz42 : z = 42
              · subst z
                simp [baseEnv, targetEnv, proofLineEnv, e42, e41, e40, e12, envUpdate]
              · by_cases hz41 : z = 41
                · subst z
                  simp [baseEnv, targetEnv, proofLineEnv, e42, e41, e40, e12, envUpdate]
                · by_cases hz40 : z = 40
                  · subst z
                    simp [baseEnv, targetEnv, proofLineEnv, e42, e41, e40, e12, envUpdate]
                  · simp [baseEnv, targetEnv, proofLineEnv, e42, e41, e40, e12,
                      envUpdate, hz1, hz2, hz43, hz42, hz41, hz40]
      exact (evalForm_env_eq_aux _ henv).1 h12

/-- Arbitrary matrix proof witnesses are sound for the formula code carried in variable 2. -/
theorem proofRel_vars12_implies_provable_raw (env : Nat → Nat)
    (hrel : evalForm env (proofRel (Term.var 1) (Term.var 2))) :
    Provable (rawFormula (env 2)) := by
  unfold proofRel at hrel
  rw [eval_existsF] at hrel
  rcases hrel with ⟨c, hrel⟩
  let e40 : Nat → Nat := fun y => if y = 40 then c else env y
  rw [eval_existsF] at hrel
  rcases hrel with ⟨d, hrel⟩
  let e41 : Nat → Nat := fun y => if y = 41 then d else e40 y
  rw [eval_existsF] at hrel
  rcases hrel with ⟨L, hrel⟩
  let e42 : Nat → Nat := fun y => if y = 42 then L else e41 y
  rw [eval_andF] at hrel
  rcases hrel with ⟨_hpack, hrest⟩
  rw [eval_andF] at hrest
  rcases hrest with ⟨hterminal, hall⟩
  have hm : env 2 = beta c d L := by
    have ht := (eval_betaF e42 (Term.var 40) (Term.var 41) (Term.var 42)
      (Term.var 2)
      (by simp [termHasVar]) (by simp [termHasVar]) (by simp [termHasVar])
      (by simp [termHasVar]) (by simp [termHasVar]) (by simp [termHasVar])
      (by simp [termHasVar])).1 hterminal
    simpa [e42, e41, e40, evalTerm] using ht
  have hlines : ∀ i, i ≤ L → JustifiedNat c d i ∨ SpecJustifiedNat c d i := by
    intro i hi
    have halli := (evalForm_all e42 43 _).1 hall i
    rw [evalForm_imp] at halli
    let ei : Nat → Nat := fun y => if y = 43 then i else e42 y
    have hle : evalForm ei (leF (Term.var 43) (Term.var 42)) := by
      apply (eval_leF_var_var ei (x := 43) (y := 42) (by decide) (by decide)).2
      simpa [ei, e42, e41, e40] using hi
    have hor := halli hle
    rcases (eval_orF ei _ _).1 hor with hj | hs
    · left
      have := (eval_justifiedF_vars ei).1 hj
      simpa [ei, e42, e41, e40] using this
    · right
      have := (eval_specJustF_vars ei).1 hs
      simpa [ei, e42, e41, e40] using this
  have hseq := rawProofSeq_hilbert c d L hlines
  apply hilbert_implies_provable
  refine ⟨rawProofSeq c d L, ?_, rawProofSeq_ne_nil c d L, hseq⟩
  rw [hm, rawProofSeq_last]

/-- Matrix proof soundness specialized to a canonical formula code in variable 2. -/
theorem proofRel_vars12_implies_provable (env : Nat → Nat) {φ : Formula}
    (h2 : env 2 = encodeFormula φ)
    (hrel : evalForm env (proofRel (Term.var 1) (Term.var 2))) :
    Provable φ := by
  have h := proofRel_vars12_implies_provable_raw env hrel
  simpa [h2, rawFormula_encode] using h

/-- Public matrix adapter: the recoded checked proof inhabits `proofRel` with the canonical formula code. -/
theorem proofRel_recoded_of_check_vars12 {p : ProofTree} {φ : Formula}
    (hp : check p = some φ) :
    evalForm
      (envUpdate (envUpdate env0 1 (proofRecoding (encodeProof p)))
        2 (formulaCode φ))
      (proofRel (Term.var 1) (Term.var 2)) := by
  have h := proofRel_packed_of_check_vars12 hp
  rw [← proofRecoding_encode_of_check hp] at h
  rw [← formulaCode_eq φ] at h
  exact h
end OperatorKO7.Meta.DistinctionBoundary.GodelArith

