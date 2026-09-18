import OperatorKO7.Meta.DistinctionBoundary.GodelRepresentability

set_option autoImplicit false

/-!
# Standard-model evaluation of the arithmetized graphs

This file develops Nat-evaluation infrastructure for `numCodeRel` and the
recursive term/formula substitution tables used by the Hilbert encoding.
The current file does **not** yet prove complete standard-model semantics for
`proofRel` or `substRel`, and therefore does not discharge the diagonal
equivalence `eval arithGodelSentence ↔ ¬ Provable arithGodelSentence`.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

theorem evalForm_eq (env : Nat → Nat) (s t : Term) :
    evalForm env (Formula.eq s t) ↔ evalTerm env s = evalTerm env t :=
  Iff.rfl

theorem evalForm_not (env : Nat → Nat) (φ : Formula) :
    evalForm env (Formula.not φ) ↔ ¬ evalForm env φ :=
  Iff.rfl

theorem evalForm_imp (env : Nat → Nat) (φ ψ : Formula) :
    evalForm env (Formula.imp φ ψ) ↔ (evalForm env φ → evalForm env ψ) :=
  Iff.rfl

theorem evalForm_all (env : Nat → Nat) (x : Nat) (φ : Formula) :
    evalForm env (Formula.all x φ) ↔
      ∀ n : Nat, evalForm (fun y => if y = x then n else env y) φ :=
  Iff.rfl

theorem evalTerm_update_fresh (env : Nat → Nat) (x n : Nat) (t : Term)
    (ht : termHasVar x t = false) :
    evalTerm (fun y => if y = x then n else env y) t = evalTerm env t :=
  evalTerm_fresh x t ht env n

theorem pair_of_ccons (a b : Nat) :
    (uncpair (ccons a b - 1)).1 = a ∧ (uncpair (ccons a b - 1)).2 = b := by
  simp [uncpair_pred_ccons]

theorem substTermCode_zero (y : Nat) :
    substTermCode y (ccons 0 0) = ccons 0 0 := by
  have hne : ccons 0 0 ≠ 0 := ccons_ne_zero 0 0
  rw [substTermCode, dif_neg hne]
  simp [uncpair_pred_ccons]

theorem substTermCode_succ (y n : Nat) :
    substTermCode y (ccons 1 n) = ccons 1 (substTermCode y n) := by
  have hne : ccons 1 n ≠ 0 := ccons_ne_zero 1 n
  rw [substTermCode, dif_neg hne]
  simp [uncpair_pred_ccons]

theorem substTermCode_add (y s t : Nat) :
    substTermCode y (ccons 2 (ccons s t)) =
      ccons 2 (ccons (substTermCode y s) (substTermCode y t)) := by
  have hne : ccons 2 (ccons s t) ≠ 0 := ccons_ne_zero _ _
  have hne2 : ccons s t ≠ 0 := ccons_ne_zero s t
  rw [substTermCode, dif_neg hne]
  simp [uncpair_pred_ccons, hne2]

theorem substTermCode_mul (y s t : Nat) :
    substTermCode y (ccons 3 (ccons s t)) =
      ccons 3 (ccons (substTermCode y s) (substTermCode y t)) := by
  have hne : ccons 3 (ccons s t) ≠ 0 := ccons_ne_zero _ _
  have hne2 : ccons s t ≠ 0 := ccons_ne_zero s t
  rw [substTermCode, dif_neg hne]
  simp [uncpair_pred_ccons, hne2]

theorem substTermCode_var0 (y : Nat) :
    substTermCode y (ccons 4 0) = numCode y := by
  have hne : ccons 4 0 ≠ 0 := ccons_ne_zero 4 0
  rw [substTermCode, dif_neg hne]
  simp [uncpair_pred_ccons]

theorem substTermCode_var_pos (y k : Nat) :
    substTermCode y (ccons 4 (k + 1)) = ccons 4 (k + 1) := by
  have hne : ccons 4 (k + 1) ≠ 0 := ccons_ne_zero _ _
  rw [substTermCode, dif_neg hne]
  simp [uncpair_pred_ccons]

theorem substFormCode_eq (y s t : Nat) :
    substFormCode y (ccons 0 (ccons s t)) =
      ccons 0 (ccons (substTermCode y s) (substTermCode y t)) := by
  have hne : ccons 0 (ccons s t) ≠ 0 := ccons_ne_zero _ _
  have hne2 : ccons s t ≠ 0 := ccons_ne_zero s t
  rw [substFormCode, dif_neg hne]
  simp [uncpair_pred_ccons, hne2]

theorem substFormCode_not (y a : Nat) :
    substFormCode y (ccons 1 a) = ccons 1 (substFormCode y a) := by
  have hne : ccons 1 a ≠ 0 := ccons_ne_zero _ _
  rw [substFormCode, dif_neg hne]
  simp [uncpair_pred_ccons]

theorem substFormCode_imp (y a b : Nat) :
    substFormCode y (ccons 2 (ccons a b)) =
      ccons 2 (ccons (substFormCode y a) (substFormCode y b)) := by
  have hne : ccons 2 (ccons a b) ≠ 0 := ccons_ne_zero _ _
  have hne2 : ccons a b ≠ 0 := ccons_ne_zero a b
  rw [substFormCode, dif_neg hne]
  simp [uncpair_pred_ccons, hne2]

theorem substFormCode_all_zero (y a : Nat) :
    substFormCode y (ccons 3 (ccons 0 a)) = ccons 3 (ccons 0 a) := by
  have hne : ccons 3 (ccons 0 a) ≠ 0 := ccons_ne_zero _ _
  have hne2 : ccons 0 a ≠ 0 := ccons_ne_zero 0 a
  rw [substFormCode, dif_neg hne]
  simp [uncpair_pred_ccons, hne2]

theorem substFormCode_all_pos (y x a : Nat) :
    substFormCode y (ccons 3 (ccons (x + 1) a)) =
      ccons 3 (ccons (x + 1) (substFormCode y a)) := by
  have hne : ccons 3 (ccons (x + 1) a) ≠ 0 := ccons_ne_zero _ _
  have hne2 : ccons (x + 1) a ≠ 0 := ccons_ne_zero _ _
  rw [substFormCode, dif_neg hne]
  simp [uncpair_pred_ccons, hne2]

def freshNumCode (t : Term) : Prop :=
  termHasVar 50 t = false ∧ termHasVar 51 t = false ∧ termHasVar 52 t = false ∧
    termHasVar 80 t = false ∧ termHasVar 81 t = false ∧
      termHasVar 82 t = false ∧ termHasVar 83 t = false

theorem numeral_freshNumCode (n : Nat) : freshNumCode (numeral n) :=
  ⟨numeral_closed n 50, numeral_closed n 51, numeral_closed n 52,
    numeral_closed n 80, numeral_closed n 81, numeral_closed n 82,
    numeral_closed n 83⟩

theorem var_freshNumCode {x : Nat}
    (h : x ≠ 50 ∧ x ≠ 51 ∧ x ≠ 52 ∧ x ≠ 80 ∧ x ≠ 81 ∧ x ≠ 82 ∧ x ≠ 83) :
    freshNumCode (Term.var x) := by
  simp [freshNumCode, termHasVar, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2]

theorem numCode_zero : numCode 0 = ccons 0 0 := rfl

theorem numCode_succ (n : Nat) : numCode (n + 1) = ccons 1 (numCode n) := rfl

theorem numCode_beta_chain (c d n : Nat)
    (h0 : beta c d 0 = ccons 0 0)
    (hstep : ∀ i, i < n → beta c d (i + 1) = ccons 1 (beta c d i)) :
    ∀ i, i ≤ n → beta c d i = numCode i := by
  intro i
  induction i with
  | zero =>
    intro _
    simpa [numCode_zero] using h0
  | succ i ih =>
    intro hi
    have hi' : i < n := Nat.lt_of_succ_le hi
    have hle : i ≤ n := Nat.le_of_lt hi'
    rw [numCode_succ, hstep i hi', ih hle]

theorem eval_numCodeRel (env : Nat → Nat) (y z : Term)
    (hy : freshNumCode y) (hz : freshNumCode z) :
    evalForm env (numCodeRel y z) ↔
      evalTerm env z = numCode (evalTerm env y) := by
  unfold numCodeRel
  rw [eval_existsF]
  constructor
  · intro ⟨c, hc⟩
    rw [eval_existsF] at hc
    rcases hc with ⟨d, hd⟩
    rw [eval_andF, eval_andF] at hd
    rcases hd with ⟨h0, hlast, hstep⟩
    set env2 : Nat → Nat :=
      fun w => if w = 81 then d else if w = 80 then c else env w
    have ey : evalTerm env2 y = evalTerm env y := by
      have h81 :=
        evalTerm_update_fresh (fun w => if w = 80 then c else env w) 81 d y
          hy.2.2.2.2.1
      have h80 := evalTerm_update_fresh env 80 c y hy.2.2.2.1
      exact h81.trans h80
    have ez : evalTerm env2 z = evalTerm env z := by
      have h81 :=
        evalTerm_update_fresh (fun w => if w = 80 then c else env w) 81 d z
          hz.2.2.2.2.1
      have h80 := evalTerm_update_fresh env 80 c z hz.2.2.2.1
      exact h81.trans h80
    have h0' : beta c d 0 = ccons 0 0 := by
      have hβ := eval_betaF env2 (Term.var 80) (Term.var 81) (numeral 0)
        (cconsTerm (numeral 0) (numeral 0))
        (numeral_closed 0 51) (by simp [termHasVar])
        (by simp [termHasVar_cconsTerm, numeral_closed])
        (by simp [termHasVar]) (numeral_closed 0 52)
        (by simp [termHasVar])
        (by simp [termHasVar_cconsTerm, numeral_closed])
      have h0e : evalForm env2
          (betaF (Term.var 80) (Term.var 81) (numeral 0)
            (cconsTerm (numeral 0) (numeral 0))) := h0
      have := hβ.1 h0e
      simpa [env2, evalTerm, evalTerm_numeral, eval_cconsTerm] using this.symm
    have hlast' : evalTerm env z = beta c d (evalTerm env y) := by
      have hβ := eval_betaF env2 (Term.var 80) (Term.var 81) y z
        hy.2.1 (by simp [termHasVar]) hz.2.1
        (by simp [termHasVar]) hy.2.2.1 (by simp [termHasVar]) hz.2.2.1
      have hle : evalForm env2 (betaF (Term.var 80) (Term.var 81) y z) := hlast
      have := hβ.1 hle
      simpa [env2, evalTerm, ey, ez] using this
    have hstep' : ∀ i, i < evalTerm env y →
        beta c d (i + 1) = ccons 1 (beta c d i) := by
      intro i hi
      have hall := (evalForm_all env2 82 _).1 hstep i
      rw [evalForm_imp] at hall
      have hlt : evalForm (fun w => if w = 82 then i else env2 w)
          (ltF (Term.var 82) y) := by
        have hltβ := eval_ltF (fun w => if w = 82 then i else env2 w)
          (Term.var 82) y (by simp [termHasVar]) hy.2.1
        apply hltβ.2
        have ey3 :
            evalTerm (fun w => if w = 82 then i else env2 w) y =
              evalTerm env y :=
          (evalTerm_update_fresh env2 82 i y hy.2.2.2.2.2.1).trans ey
        simpa [evalTerm, ey3] using hi
      rcases (eval_existsF _ 83 _).1 (hall hlt) with ⟨a, ha⟩
      rw [eval_andF] at ha
      rcases ha with ⟨ha1, ha2⟩
      set env4 : Nat → Nat :=
        fun w => if w = 83 then a else if w = 82 then i else env2 w
      have hβ1 := eval_betaF env4 (Term.var 80) (Term.var 81)
        (Term.var 82) (Term.var 83)
        (by simp [termHasVar]) (by simp [termHasVar]) (by simp [termHasVar])
        (by simp [termHasVar]) (by simp [termHasVar]) (by simp [termHasVar])
        (by simp [termHasVar])
      have ha1e : evalForm env4
          (betaF (Term.var 80) (Term.var 81) (Term.var 82) (Term.var 83)) := ha1
      have ha1' := hβ1.1 ha1e
      have ha_eq : a = beta c d i := by
        simpa [env4, env2, evalTerm] using ha1'
      have hβ2 := eval_betaF env4 (Term.var 80) (Term.var 81)
        (Term.succ (Term.var 82)) (cconsTerm (numeral 1) (Term.var 83))
        (by simp [termHasVar]) (by simp [termHasVar])
        (by simp [termHasVar_cconsTerm, termHasVar, numeral_closed])
        (by simp [termHasVar]) (by simp [termHasVar]) (by simp [termHasVar])
        (by simp [termHasVar_cconsTerm, termHasVar, numeral_closed])
      have ha2e : evalForm env4
          (betaF (Term.var 80) (Term.var 81) (Term.succ (Term.var 82))
            (cconsTerm (numeral 1) (Term.var 83))) := ha2
      have ha2' := hβ2.1 ha2e
      have : ccons 1 a = beta c d (i + 1) := by
        simpa [env4, env2, evalTerm, evalTerm_numeral, eval_cconsTerm] using ha2'
      rw [ha_eq] at this
      exact this.symm
    have hchain := numCode_beta_chain c d (evalTerm env y) h0' hstep'
    have := hchain (evalTerm env y) (Nat.le_refl _)
    exact hlast'.trans this
  · intro hzcode
    let n := evalTerm env y
    obtain ⟨c, d, hpack⟩ := beta_exists n numCode
    refine ⟨c, ?_⟩
    rw [eval_existsF]
    refine ⟨d, ?_⟩
    set env2 : Nat → Nat :=
      fun w => if w = 81 then d else if w = 80 then c else env w
    rw [eval_andF, eval_andF]
    have ey : evalTerm env2 y = n := by
      have h81 :=
        evalTerm_update_fresh (fun w => if w = 80 then c else env w) 81 d y
          hy.2.2.2.2.1
      have h80 := evalTerm_update_fresh env 80 c y hy.2.2.2.1
      exact h81.trans h80
    have ez : evalTerm env2 z = evalTerm env z := by
      have h81 :=
        evalTerm_update_fresh (fun w => if w = 80 then c else env w) 81 d z
          hz.2.2.2.2.1
      have h80 := evalTerm_update_fresh env 80 c z hz.2.2.2.1
      exact h81.trans h80
    refine ⟨?h0, ?hlast, ?hstep⟩
    · have hβ := eval_betaF env2 (Term.var 80) (Term.var 81) (numeral 0)
        (cconsTerm (numeral 0) (numeral 0))
        (numeral_closed 0 51) (by simp [termHasVar])
        (by simp [termHasVar_cconsTerm, numeral_closed])
        (by simp [termHasVar]) (numeral_closed 0 52)
        (by simp [termHasVar])
        (by simp [termHasVar_cconsTerm, numeral_closed])
      apply hβ.2
      have h0p : beta c d 0 = numCode 0 := hpack 0 (Nat.zero_le _)
      simpa [env2, evalTerm, evalTerm_numeral, eval_cconsTerm, numCode_zero]
        using h0p.symm
    · have hβ := eval_betaF env2 (Term.var 80) (Term.var 81) y z
        hy.2.1 (by simp [termHasVar]) hz.2.1
        (by simp [termHasVar]) hy.2.2.1 (by simp [termHasVar]) hz.2.2.1
      apply hβ.2
      have hnp : beta c d n = numCode n := hpack n (Nat.le_refl _)
      simpa [env2, evalTerm, ey, ez, hzcode] using hnp.symm
    · rw [evalForm_all]
      intro i
      rw [evalForm_imp]
      intro hlt
      have hltβ := eval_ltF (fun w => if w = 82 then i else env2 w)
        (Term.var 82) y (by simp [termHasVar]) hy.2.1
      have ey3 :
          evalTerm (fun w => if w = 82 then i else env2 w) y = n :=
        (evalTerm_update_fresh env2 82 i y hy.2.2.2.2.2.1).trans ey
      have hi : i < n := by
        have := hltβ.1 hlt
        simpa [evalTerm, ey3] using this
      rw [eval_existsF]
      refine ⟨numCode i, ?_⟩
      rw [eval_andF]
      set env4 : Nat → Nat :=
        fun w => if w = 83 then numCode i else if w = 82 then i else env2 w
      constructor
      · have hβ := eval_betaF env4 (Term.var 80) (Term.var 81)
          (Term.var 82) (Term.var 83)
          (by simp [termHasVar]) (by simp [termHasVar]) (by simp [termHasVar])
          (by simp [termHasVar]) (by simp [termHasVar]) (by simp [termHasVar])
          (by simp [termHasVar])
        apply hβ.2
        have hip : beta c d i = numCode i :=
          hpack i (Nat.le_of_lt hi)
        simpa [env4, env2, evalTerm] using hip.symm
      · have hβ := eval_betaF env4 (Term.var 80) (Term.var 81)
          (Term.succ (Term.var 82)) (cconsTerm (numeral 1) (Term.var 83))
          (by simp [termHasVar]) (by simp [termHasVar])
          (by simp [termHasVar_cconsTerm, termHasVar, numeral_closed])
          (by simp [termHasVar]) (by simp [termHasVar]) (by simp [termHasVar])
          (by simp [termHasVar_cconsTerm, termHasVar, numeral_closed])
        apply hβ.2
        have his : beta c d (i + 1) = numCode (i + 1) :=
          hpack (i + 1) (Nat.succ_le_of_lt hi)
        simpa [env4, env2, evalTerm, evalTerm_numeral, eval_cconsTerm, numCode_succ]
          using his.symm

def termPostorder : Term → List Term
  | Term.zero => [Term.zero]
  | Term.succ t => termPostorder t ++ [Term.succ t]
  | Term.add s t => termPostorder s ++ termPostorder t ++ [Term.add s t]
  | Term.mul s t => termPostorder s ++ termPostorder t ++ [Term.mul s t]
  | Term.var n => [Term.var n]

theorem termPostorder_ne_nil : ∀ t : Term, termPostorder t ≠ []
  | Term.zero => List.cons_ne_nil _ _
  | Term.succ t => List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  | Term.add s t => List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  | Term.mul s t => List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  | Term.var n => List.cons_ne_nil _ _

theorem termPostorder_getLast :
    ∀ t : Term, (termPostorder t).getLast? = some t
  | Term.zero => rfl
  | Term.succ t => getLast?_concat (termPostorder t) (Term.succ t)
  | Term.add s t => getLast?_concat (termPostorder s ++ termPostorder t) (Term.add s t)
  | Term.mul s t => getLast?_concat (termPostorder s ++ termPostorder t) (Term.mul s t)
  | Term.var n => rfl

def termPair (y : Nat) (t : Term) : Nat :=
  ccons (encodeTerm t) (substTermCode y (encodeTerm t))

def termTable (y : Nat) (t : Term) (i : Nat) : Nat :=
  match (termPostorder t)[i]? with
  | some s => termPair y s
  | none => 0

theorem termPostorder_succ_child (t : Term) :
    (termPostorder (Term.succ t))[(termPostorder t).length - 1]? = some t := by
  have hne := termPostorder_ne_nil t
  have hidx : (termPostorder t).length - 1 < (termPostorder t).length :=
    Nat.pred_lt (List.length_pos_iff.mpr hne).ne'
  have : (termPostorder (Term.succ t))[(termPostorder t).length - 1]? =
      (termPostorder t)[(termPostorder t).length - 1]? := by
    simp [termPostorder, List.getElem?_append_left hidx]
  rw [this]
  exact getLast?_some_getElem? (termPostorder_getLast t) hne

theorem termPostorder_succ_self (t : Term) :
    (termPostorder (Term.succ t))[(termPostorder t).length]? = some (Term.succ t) := by
  simp [termPostorder, List.getElem?_append_right]

def formPostorder : Formula → List Formula
  | Formula.eq s t => [Formula.eq s t]
  | Formula.not φ => formPostorder φ ++ [Formula.not φ]
  | Formula.imp a b => formPostorder a ++ formPostorder b ++ [Formula.imp a b]
  | Formula.all x φ => formPostorder φ ++ [Formula.all x φ]

theorem formPostorder_ne_nil : ∀ φ : Formula, formPostorder φ ≠ []
  | Formula.eq _ _ => List.cons_ne_nil _ _
  | Formula.not φ => List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  | Formula.imp _ _ => List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  | Formula.all _ φ => List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)

theorem formPostorder_getLast :
    ∀ φ : Formula, (formPostorder φ).getLast? = some φ
  | Formula.eq _ _ => rfl
  | Formula.not φ => getLast?_concat (formPostorder φ) (Formula.not φ)
  | Formula.imp a b =>
      getLast?_concat (formPostorder a ++ formPostorder b) (Formula.imp a b)
  | Formula.all x φ => getLast?_concat (formPostorder φ) (Formula.all x φ)

def formPair (y : Nat) (φ : Formula) : Nat :=
  ccons (encodeFormula φ) (substFormCode y (encodeFormula φ))

theorem getElem?_append_cases {α : Type} {l1 l2 : List α} {i : Nat} {a : α}
    (h : (l1 ++ l2)[i]? = some a) :
    (i < l1.length ∧ l1[i]? = some a) ∨
      (l1.length ≤ i ∧ l2[i - l1.length]? = some a) := by
  by_cases hi : i < l1.length
  · exact Or.inl ⟨hi, (List.getElem?_append_left hi).symm.trans h⟩
  · have hle : l1.length ≤ i := Nat.le_of_not_lt hi
    have : (l1 ++ l2)[i]? = l2[i - l1.length]? :=
      List.getElem?_append_right hle
    exact Or.inr ⟨hle, this.symm.trans h⟩

theorem getElem?_some_lt {α : Type} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : i < l.length := by
  cases Nat.lt_or_ge i l.length with
  | inl hlt => exact hlt
  | inr hge =>
    have : l[i]? = none := List.getElem?_eq_none hge
    simp [this] at h

theorem termPostorder_succ_prev :
    ∀ t u : Term, ∀ i : Nat,
      (termPostorder t)[i]? = some (Term.succ u) →
        ∃ j, j < i ∧ (termPostorder t)[j]? = some u
  | Term.zero, u, i, h => by
    change ([Term.zero] : List Term)[i]? = some (Term.succ u) at h
    cases i <;> simp at h
  | Term.succ t, u, i, h => by
    change (termPostorder t ++ [Term.succ t])[i]? = some (Term.succ u) at h
    cases getElem?_append_cases h with
    | inl hleft =>
      rcases hleft with ⟨hi, hih⟩
      rcases termPostorder_succ_prev t u i hih with ⟨j, hj, hj'⟩
      refine ⟨j, hj, ?_⟩
      change (termPostorder t ++ [Term.succ t])[j]? = some u
      rw [List.getElem?_append_left (Nat.lt_trans hj hi)]
      exact hj'
    | inr hright =>
      rcases hright with ⟨hle, hlast⟩
      have hk : i - (termPostorder t).length = 0 := by
        cases hnat : i - (termPostorder t).length with
        | zero => rfl
        | succ k => simp [hnat] at hlast
      have hsu : Term.succ t = Term.succ u := by
        simpa [hk] using hlast
      injection hsu with hu
      subst hu
      have hne := termPostorder_ne_nil t
      have hi : i = (termPostorder t).length := by omega
      subst hi
      refine ⟨(termPostorder t).length - 1,
        Nat.pred_lt (List.length_pos_iff.mpr hne).ne', ?_⟩
      change (termPostorder t ++ [Term.succ t])[(termPostorder t).length - 1]? =
        some t
      have hidx : (termPostorder t).length - 1 < (termPostorder t).length :=
        Nat.pred_lt (List.length_pos_iff.mpr hne).ne'
      rw [List.getElem?_append_left hidx]
      exact getLast?_some_getElem? (termPostorder_getLast t) hne
  | Term.add s t, u, i, h => by
    change ((termPostorder s ++ termPostorder t) ++ [Term.add s t])[i]? =
      some (Term.succ u) at h
    cases getElem?_append_cases h with
    | inl hmid =>
      rcases hmid with ⟨hi, hst⟩
      cases getElem?_append_cases hst with
      | inl hs =>
        rcases hs with ⟨hslen, hih⟩
        rcases termPostorder_succ_prev s u i hih with ⟨j, hj, hj'⟩
        refine ⟨j, hj, ?_⟩
        change ((termPostorder s ++ termPostorder t) ++ [Term.add s t])[j]? =
          some u
        have hj1 : j < (termPostorder s).length := Nat.lt_trans hj hslen
        have hj2 : j < (termPostorder s ++ termPostorder t).length := by
          simp [List.length_append]; omega
        rw [List.getElem?_append_left hj2, List.getElem?_append_left hj1]
        exact hj'
      | inr ht =>
        rcases ht with ⟨hle, hih⟩
        rcases termPostorder_succ_prev t u (i - (termPostorder s).length) hih with
          ⟨j, hj, hj'⟩
        have hihlt := getElem?_some_lt hih
        have hjlt : j < (termPostorder t).length := Nat.lt_trans hj hihlt
        refine ⟨(termPostorder s).length + j, by omega, ?_⟩
        have hge : (termPostorder s).length ≤ (termPostorder s).length + j :=
          Nat.le_add_right _ _
        have hmid : (termPostorder s ++ termPostorder t)[(termPostorder s).length + j]? = some u := by
          rw [List.getElem?_append_right hge]
          simpa [Nat.add_sub_cancel_left] using hj'
        have hlt1 : (termPostorder s).length + j < (termPostorder s ++ termPostorder t).length := by
          simp [List.length_append]; omega
        rw [termPostorder, List.getElem?_append_left hlt1]
        exact hmid
    | inr hlast =>
      rcases hlast with ⟨_, hf⟩
      simp [List.length_append] at hf
      cases k : i - ((termPostorder s).length + (termPostorder t).length) with
      | zero => simp [k] at hf
      | succ n => simp [k] at hf
  | Term.mul s t, u, i, h => by
    change ((termPostorder s ++ termPostorder t) ++ [Term.mul s t])[i]? =
      some (Term.succ u) at h
    cases getElem?_append_cases h with
    | inl hmid =>
      rcases hmid with ⟨hi, hst⟩
      cases getElem?_append_cases hst with
      | inl hs =>
        rcases hs with ⟨hslen, hih⟩
        rcases termPostorder_succ_prev s u i hih with ⟨j, hj, hj'⟩
        refine ⟨j, hj, ?_⟩
        change ((termPostorder s ++ termPostorder t) ++ [Term.mul s t])[j]? =
          some u
        have hj1 : j < (termPostorder s).length := Nat.lt_trans hj hslen
        have hj2 : j < (termPostorder s ++ termPostorder t).length := by
          simp [List.length_append]; omega
        rw [List.getElem?_append_left hj2, List.getElem?_append_left hj1]
        exact hj'
      | inr ht =>
        rcases ht with ⟨hle, hih⟩
        rcases termPostorder_succ_prev t u (i - (termPostorder s).length) hih with
          ⟨j, hj, hj'⟩
        have hihlt := getElem?_some_lt hih
        have hjlt : j < (termPostorder t).length := Nat.lt_trans hj hihlt
        refine ⟨(termPostorder s).length + j, by omega, ?_⟩
        have hge : (termPostorder s).length ≤ (termPostorder s).length + j :=
          Nat.le_add_right _ _
        have hmid : (termPostorder s ++ termPostorder t)[(termPostorder s).length + j]? = some u := by
          rw [List.getElem?_append_right hge]
          simpa [Nat.add_sub_cancel_left] using hj'
        have hlt1 : (termPostorder s).length + j < (termPostorder s ++ termPostorder t).length := by
          simp [List.length_append]; omega
        rw [termPostorder, List.getElem?_append_left hlt1]
        exact hmid
    | inr hlast =>
      rcases hlast with ⟨_, hf⟩
      simp [List.length_append] at hf
      cases k : i - ((termPostorder s).length + (termPostorder t).length) with
      | zero => simp [k] at hf
      | succ n => simp [k] at hf
  | Term.var n, u, i, h => by
    change ([Term.var n] : List Term)[i]? = some (Term.succ u) at h
    cases i <;> simp at h

/-! ## Formula-code recognizers used by the Hilbert-sequence graph -/

theorem eval_isQ1F_var55 (env : Nat → Nat) :
    evalForm env (isQ1F (Term.var 55)) ↔ env 55 = encodeFormula q1 := by
  simp [isQ1F, eval_existsF, eval_andF, eval_eqCcons, eval_cconsTerm,
    evalForm, evalTerm, evalTerm_numeral, q1, encodeFormula, encodeTerm]

theorem eval_isQ2F_var55 (env : Nat → Nat) :
    evalForm env (isQ2F (Term.var 55)) ↔ env 55 = encodeFormula q2 := by
  simp [isQ2F, eval_existsF, eval_andF, eval_eqCcons, eval_cconsTerm,
    evalForm, evalTerm, evalTerm_numeral, q2, encodeFormula, encodeTerm]

theorem eval_isQ3F_var55 (env : Nat → Nat) :
    evalForm env (isQ3F (Term.var 55)) ↔ env 55 = encodeFormula q3 := by
  simp [isQ3F, eval_existsF, eval_andF, eval_eqCcons, eval_cconsTerm,
    evalForm, evalTerm, evalTerm_numeral, q3, encodeFormula, encodeTerm]

theorem eval_isQ4F_var55 (env : Nat → Nat) :
    evalForm env (isQ4F (Term.var 55)) ↔ env 55 = encodeFormula q4 := by
  simp [isQ4F, eval_existsF, eval_andF, eval_eqCcons, eval_cconsTerm,
    evalForm, evalTerm, evalTerm_numeral, q4, encodeFormula, encodeTerm]

theorem eval_isQ5F_var55 (env : Nat → Nat) :
    evalForm env (isQ5F (Term.var 55)) ↔ env 55 = encodeFormula q5 := by
  simp [isQ5F, eval_existsF, eval_andF, eval_eqCcons, eval_cconsTerm,
    evalForm, evalTerm, evalTerm_numeral, q5, encodeFormula, encodeTerm]

theorem eval_isQ6F_var55 (env : Nat → Nat) :
    evalForm env (isQ6F (Term.var 55)) ↔ env 55 = encodeFormula q6 := by
  simp [isQ6F, eval_existsF, eval_andF, eval_eqCcons, eval_cconsTerm,
    evalForm, evalTerm, evalTerm_numeral, q6, encodeFormula, encodeTerm]

theorem eval_isQ7F_var55 (env : Nat → Nat) :
    evalForm env (isQ7F (Term.var 55)) ↔ env 55 = encodeFormula q7 := by
  simp [isQ7F, eval_existsF, eval_andF, eval_orF, eval_eqCcons, eval_cconsTerm,
    evalForm, evalTerm, evalTerm_numeral, q7, existsF, orF, encodeFormula, encodeTerm]

theorem eval_isEqReflF_var55 (env : Nat → Nat) :
    evalForm env (isEqReflF (Term.var 55)) ↔
      ∃ a, env 55 = ccons 0 (ccons a a) := by
  simp [isEqReflF, eval_existsF, eval_eqCcons, eval_cconsTerm,
    evalForm, evalTerm, evalTerm_numeral]

theorem eval_isAxIdF_var55 (env : Nat → Nat) :
    evalForm env (isAxIdF (Term.var 55)) ↔
      ∃ a, env 55 = ccons 2 (ccons a a) := by
  simp [isAxIdF, eval_existsF, eval_eqCcons, eval_cconsTerm,
    evalForm, evalTerm, evalTerm_numeral]

theorem eval_isAxKF_var55 (env : Nat → Nat) :
    evalForm env (isAxKF (Term.var 55)) ↔
      ∃ a b, env 55 = ccons 2 (ccons a (ccons 2 (ccons b a))) := by
  simp [isAxKF, eval_existsF, eval_eqCcons, eval_cconsTerm,
    evalForm, evalTerm, evalTerm_numeral]

theorem eval_isAxDNEF_var55 (env : Nat → Nat) :
    evalForm env (isAxDNEF (Term.var 55)) ↔
      ∃ a, env 55 = ccons 2 (ccons (ccons 1 (ccons 1 a)) a) := by
  simp [isAxDNEF, eval_existsF, eval_andF, eval_eqCcons, eval_cconsTerm,
    evalForm, evalTerm, evalTerm_numeral]

theorem eval_isAxSF_var55 (env : Nat → Nat) :
    evalForm env (isAxSF (Term.var 55)) ↔
      ∃ a b c,
        env 55 = ccons 2
          (ccons (ccons 2 (ccons a (ccons 2 (ccons b c))))
            (ccons 2 (ccons (ccons 2 (ccons a b))
              (ccons 2 (ccons a c))))) := by
  simp [isAxSF, eval_existsF, eval_andF, eval_eqCcons, eval_cconsTerm,
    evalForm, evalTerm, evalTerm_numeral]

def AxiomCodeShape (n : Nat) : Prop :=
  (n = encodeFormula q1 ∨ n = encodeFormula q2 ∨ n = encodeFormula q3 ∨
    n = encodeFormula q4 ∨ n = encodeFormula q5 ∨ n = encodeFormula q6 ∨
    n = encodeFormula q7) ∨
  (∃ a, n = ccons 0 (ccons a a)) ∨
  (∃ a, n = ccons 2 (ccons a a)) ∨
  (∃ a b, n = ccons 2 (ccons a (ccons 2 (ccons b a)))) ∨
  (∃ a b c,
    n = ccons 2
      (ccons (ccons 2 (ccons a (ccons 2 (ccons b c))))
        (ccons 2 (ccons (ccons 2 (ccons a b))
          (ccons 2 (ccons a c)))))) ∨
  (∃ a, n = ccons 2 (ccons (ccons 1 (ccons 1 a)) a))

theorem eval_isQAxiomF_var55 (env : Nat → Nat) :
    evalForm env (isQAxiomF (Term.var 55)) ↔
      env 55 = encodeFormula q1 ∨ env 55 = encodeFormula q2 ∨
      env 55 = encodeFormula q3 ∨ env 55 = encodeFormula q4 ∨
      env 55 = encodeFormula q5 ∨ env 55 = encodeFormula q6 ∨
      env 55 = encodeFormula q7 := by
  simp [isQAxiomF, eval_orF, eval_isQ1F_var55, eval_isQ2F_var55,
    eval_isQ3F_var55, eval_isQ4F_var55, eval_isQ5F_var55,
    eval_isQ6F_var55, eval_isQ7F_var55]

theorem eval_isAxiomF_var55 (env : Nat → Nat) :
    evalForm env (isAxiomF (Term.var 55)) ↔ AxiomCodeShape (env 55) := by
  simp [isAxiomF, AxiomCodeShape, eval_orF, eval_isQAxiomF_var55,
    eval_isEqReflF_var55, eval_isAxIdF_var55, eval_isAxKF_var55,
    eval_isAxSF_var55, eval_isAxDNEF_var55]

/-! ## Numeric semantics of the recursive substitution tables -/

def TermSubstJustNat (c d i ncode inC outC : Nat) : Prop :=
  (inC = ccons 0 0 ∧ outC = ccons 0 0) ∨
  (∃ a a' j, inC = ccons 1 a ∧ outC = ccons 1 a' ∧ j < i ∧
    ccons a a' = beta c d j) ∨
  (∃ a b a' b' j k,
    inC = ccons 2 (ccons a b) ∧ outC = ccons 2 (ccons a' b') ∧
      j < i ∧ k < i ∧ ccons a a' = beta c d j ∧
      ccons b b' = beta c d k) ∨
  (∃ a b a' b' j k,
    inC = ccons 3 (ccons a b) ∧ outC = ccons 3 (ccons a' b') ∧
      j < i ∧ k < i ∧ ccons a a' = beta c d j ∧
      ccons b b' = beta c d k) ∨
  ((inC = ccons 4 0 ∧ outC = ncode) ∨
    ((∃ k, inC = ccons 4 k ∧ 0 < k) ∧ outC = inC))

theorem eval_ltF_var_numeral (env : Nat → Nat) {x : Nat} (n : Nat)
    (hx : x ≠ 51) :
    evalForm env (ltF (Term.var x) (numeral n)) ↔ env x < n := by
  simpa [evalTerm, evalTerm_numeral] using
    (eval_ltF env (Term.var x) (numeral n)
      (by simp [termHasVar, hx]) (numeral_closed n 51))

theorem eval_ltF_numeral_var (env : Nat → Nat) (n : Nat) {x : Nat}
    (hx : x ≠ 51) :
    evalForm env (ltF (numeral n) (Term.var x)) ↔ n < env x := by
  simpa [evalTerm, evalTerm_numeral] using
    (eval_ltF env (numeral n) (Term.var x)
      (numeral_closed n 51) (by simp [termHasVar, hx]))

theorem eval_ltF_var_var (env : Nat → Nat) {x y : Nat}
    (hx : x ≠ 51) (hy : y ≠ 51) :
    evalForm env (ltF (Term.var x) (Term.var y)) ↔ env x < env y := by
  simpa [evalTerm] using
    (eval_ltF env (Term.var x) (Term.var y)
      (by simp [termHasVar, hx]) (by simp [termHasVar, hy]))

theorem eval_betaF_numeral_var_ccons (env : Nat → Nat) (c d : Nat)
    {i a b : Nat}
    (hi51 : i ≠ 51) (hi52 : i ≠ 52)
    (ha51 : a ≠ 51) (ha52 : a ≠ 52)
    (hb51 : b ≠ 51) (hb52 : b ≠ 52) :
    evalForm env (betaF (numeral c) (numeral d) (Term.var i)
      (cconsTerm (Term.var a) (Term.var b))) ↔
      ccons (env a) (env b) = beta c d (env i) := by
  simpa [evalTerm, evalTerm_numeral, eval_cconsTerm] using
    (eval_betaF env (numeral c) (numeral d) (Term.var i)
      (cconsTerm (Term.var a) (Term.var b))
      (by simp [termHasVar, hi51]) (numeral_closed d 51)
      (by simp [termHasVar_cconsTerm, termHasVar, ha51, hb51])
      (numeral_closed c 52) (by simp [termHasVar, hi52])
      (numeral_closed d 52)
      (by simp [termHasVar_cconsTerm, termHasVar, ha52, hb52]))

theorem eval_leF_var_var (env : Nat → Nat) {x y : Nat}
    (hx : x ≠ 50) (hy : y ≠ 50) :
    evalForm env (leF (Term.var x) (Term.var y)) ↔ env x ≤ env y := by
  simpa [evalTerm] using
    (eval_leF env (Term.var x) (Term.var y)
      (by simp [termHasVar, hx]) (by simp [termHasVar, hy]))

theorem eval_betaF_vars_ccons (env : Nat → Nat) {c d i a b : Nat}
    (hi51 : i ≠ 51) (hd51 : d ≠ 51) (ha51 : a ≠ 51) (hb51 : b ≠ 51)
    (hc52 : c ≠ 52) (hi52 : i ≠ 52) (hd52 : d ≠ 52)
    (ha52 : a ≠ 52) (hb52 : b ≠ 52) :
    evalForm env (betaF (Term.var c) (Term.var d) (Term.var i)
      (cconsTerm (Term.var a) (Term.var b))) ↔
      ccons (env a) (env b) = beta (env c) (env d) (env i) := by
  simpa [evalTerm, eval_cconsTerm] using
    (eval_betaF env (Term.var c) (Term.var d) (Term.var i)
      (cconsTerm (Term.var a) (Term.var b))
      (by simp [termHasVar, hi51]) (by simp [termHasVar, hd51])
      (by simp [termHasVar_cconsTerm, termHasVar, ha51, hb51])
      (by simp [termHasVar, hc52]) (by simp [termHasVar, hi52])
      (by simp [termHasVar, hd52])
      (by simp [termHasVar_cconsTerm, termHasVar, ha52, hb52]))

theorem eval_betaF_vars_ccons_numerals (env : Nat → Nat) {c d i : Nat}
    (a b : Nat) (hi51 : i ≠ 51) (hd51 : d ≠ 51)
    (hc52 : c ≠ 52) (hi52 : i ≠ 52) (hd52 : d ≠ 52) :
    evalForm env (betaF (Term.var c) (Term.var d) (Term.var i)
      (cconsTerm (numeral a) (numeral b))) ↔
      ccons a b = beta (env c) (env d) (env i) := by
  simpa [evalTerm, evalTerm_numeral, eval_cconsTerm] using
    (eval_betaF env (Term.var c) (Term.var d) (Term.var i)
      (cconsTerm (numeral a) (numeral b))
      (by simp [termHasVar, hi51]) (by simp [termHasVar, hd51])
      (by simp [termHasVar_cconsTerm, numeral_closed])
      (by simp [termHasVar, hc52]) (by simp [termHasVar, hi52])
      (by simp [termHasVar, hd52])
      (by simp [termHasVar_cconsTerm, numeral_closed]))

theorem eval_termSubstJust_numerals (env : Nat → Nat)
    (c d i ncode inC outC : Nat) :
    evalForm env (termSubstJust (numeral c) (numeral d) (numeral i)
      (numeral ncode) (numeral inC) (numeral outC)) ↔
      TermSubstJustNat c d i ncode inC outC := by
  simp [termSubstJust, TermSubstJustNat, termSubstZeroCase,
    termSubstSuccCase, termSubstAddCase, termSubstMulCase,
    termSubstVarCase, eval_existsF, eval_andF, eval_orF,
    eval_eqCcons, eval_cconsTerm, eval_ltF_var_numeral,
    eval_ltF_numeral_var, eval_betaF_numeral_var_ccons,
    evalForm, evalTerm, evalTerm_numeral]

theorem eval_termSubstJust_tableVars (env : Nat → Nat) (ncode : Nat) :
    evalForm env (termSubstJust (Term.var 220) (Term.var 221) (Term.var 223)
      (numeral ncode) (Term.var 224) (Term.var 225)) ↔
      TermSubstJustNat (env 220) (env 221) (env 223) ncode
        (env 224) (env 225) := by
  simp [termSubstJust, TermSubstJustNat, termSubstZeroCase,
    termSubstSuccCase, termSubstAddCase, termSubstMulCase,
    termSubstVarCase, eval_existsF, eval_andF, eval_orF,
    eval_eqCcons, eval_cconsTerm, eval_ltF_var_numeral, eval_ltF_var_var,
    eval_ltF_numeral_var, eval_betaF_vars_ccons,
    evalForm, evalTerm, evalTerm_numeral]

def TermSubstTrace (c d L ncode : Nat) : Prop :=
  ∀ i, i ≤ L → ∃ inC outC,
    ccons inC outC = beta c d i ∧
      TermSubstJustNat c d i ncode inC outC

theorem termSubstTrace_entry_sound (y c d L ncode : Nat)
    (hncode : ncode = numCode y)
    (htrace : TermSubstTrace c d L ncode) :
    ∀ i, i ≤ L → ∀ inC outC,
      beta c d i = ccons inC outC →
        outC = substTermCode y inC := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
      intro hi inC outC hentry
      rcases htrace i hi with ⟨inC', outC', hentry', hjust⟩
      have hp : inC = inC' ∧ outC = outC' :=
        ccons_injective (hentry.symm.trans hentry'.symm)
      rcases hp with ⟨rfl, rfl⟩
      rcases hjust with hzero | hsucc | hadd | hmul | hvar
      · rw [hzero.1, hzero.2, substTermCode_zero]
      · rcases hsucc with ⟨a, a', j, hin, hout, hj, hβ⟩
        have hjL : j ≤ L := Nat.le_trans (Nat.le_of_lt hj) hi
        have hchild : a' = substTermCode y a :=
          ih j hj hjL a a' hβ.symm
        rw [hin, hout, substTermCode_succ, hchild]
      · rcases hadd with ⟨a, b, a', b', j, k, hin, hout, hj, hk, hβj, hβk⟩
        have hjL : j ≤ L := Nat.le_trans (Nat.le_of_lt hj) hi
        have hkL : k ≤ L := Nat.le_trans (Nat.le_of_lt hk) hi
        have hleft : a' = substTermCode y a :=
          ih j hj hjL a a' hβj.symm
        have hright : b' = substTermCode y b :=
          ih k hk hkL b b' hβk.symm
        rw [hin, hout, substTermCode_add, hleft, hright]
      · rcases hmul with ⟨a, b, a', b', j, k, hin, hout, hj, hk, hβj, hβk⟩
        have hjL : j ≤ L := Nat.le_trans (Nat.le_of_lt hj) hi
        have hkL : k ≤ L := Nat.le_trans (Nat.le_of_lt hk) hi
        have hleft : a' = substTermCode y a :=
          ih j hj hjL a a' hβj.symm
        have hright : b' = substTermCode y b :=
          ih k hk hkL b b' hβk.symm
        rw [hin, hout, substTermCode_mul, hleft, hright]
      · rcases hvar with hzero | hpos
        · rw [hzero.1, hzero.2, hncode, substTermCode_var0]
        · rcases hpos with ⟨⟨k, hin, hk⟩, hout⟩
          obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
          rw [hout, hin, substTermCode_var_pos]

theorem eval_termSubstClosed_numerals (env : Nat → Nat)
    (x z ncode : Nat) :
    evalForm env (termSubstClosed (numeral x) (numeral z) (numeral ncode)) ↔
      ∃ c d L, ccons x z = beta c d L ∧ TermSubstTrace c d L ncode := by
  simp [termSubstClosed, TermSubstTrace, eval_existsF, eval_andF,
    evalForm_all, evalForm_imp, eval_leF_var_var,
    eval_betaF_vars_ccons, eval_betaF_vars_ccons_numerals,
    eval_termSubstJust_tableVars,
    evalTerm, evalTerm_numeral]

/-! ## Certified postorder traces for term substitution -/

def TermChildrenBefore (xs : List Term) (i : Nat) : Term → Prop
  | Term.zero => True
  | Term.succ t => ∃ j, j < i ∧ xs[j]? = some t
  | Term.add s t =>
      ∃ j k, j < i ∧ k < i ∧ xs[j]? = some s ∧ xs[k]? = some t
  | Term.mul s t =>
      ∃ j k, j < i ∧ k < i ∧ xs[j]? = some s ∧ xs[k]? = some t
  | Term.var _ => True

def TermPostorderOK (xs : List Term) : Prop :=
  ∀ i t, xs[i]? = some t → TermChildrenBefore xs i t

theorem termChildrenBefore_append_left {xs ys : List Term} {i : Nat} {t : Term}
    (hi : i < xs.length) (h : TermChildrenBefore xs i t) :
    TermChildrenBefore (xs ++ ys) i t := by
  cases t with
  | zero => trivial
  | var _ => trivial
  | succ u =>
      rcases h with ⟨j, hj, hju⟩
      refine ⟨j, hj, ?_⟩
      rw [List.getElem?_append_left (Nat.lt_trans hj hi)]
      exact hju
  | add u v =>
      rcases h with ⟨j, k, hj, hk, hju, hkv⟩
      refine ⟨j, k, hj, hk, ?_, ?_⟩
      · rw [List.getElem?_append_left (Nat.lt_trans hj hi)]
        exact hju
      · rw [List.getElem?_append_left (Nat.lt_trans hk hi)]
        exact hkv
  | mul u v =>
      rcases h with ⟨j, k, hj, hk, hju, hkv⟩
      refine ⟨j, k, hj, hk, ?_, ?_⟩
      · rw [List.getElem?_append_left (Nat.lt_trans hj hi)]
        exact hju
      · rw [List.getElem?_append_left (Nat.lt_trans hk hi)]
        exact hkv

theorem termChildrenBefore_append_right {xs ys : List Term} {i : Nat} {t : Term}
    (h : TermChildrenBefore ys i t) :
    TermChildrenBefore (xs ++ ys) (xs.length + i) t := by
  cases t with
  | zero => trivial
  | var _ => trivial
  | succ u =>
      rcases h with ⟨j, hj, hju⟩
      refine ⟨xs.length + j, by omega, ?_⟩
      rw [List.getElem?_append_right (Nat.le_add_right _ _)]
      simpa using hju
  | add u v =>
      rcases h with ⟨j, k, hj, hk, hju, hkv⟩
      refine ⟨xs.length + j, xs.length + k, by omega, by omega, ?_, ?_⟩
      · rw [List.getElem?_append_right (Nat.le_add_right _ _)]
        simpa using hju
      · rw [List.getElem?_append_right (Nat.le_add_right _ _)]
        simpa using hkv
  | mul u v =>
      rcases h with ⟨j, k, hj, hk, hju, hkv⟩
      refine ⟨xs.length + j, xs.length + k, by omega, by omega, ?_, ?_⟩
      · rw [List.getElem?_append_right (Nat.le_add_right _ _)]
        simpa using hju
      · rw [List.getElem?_append_right (Nat.le_add_right _ _)]
        simpa using hkv

theorem termPostorderOK_nil : TermPostorderOK [] := by
  intro i t h
  simp at h

theorem termPostorderOK_append {xs ys : List Term}
    (hx : TermPostorderOK xs) (hy : TermPostorderOK ys) :
    TermPostorderOK (xs ++ ys) := by
  intro i t hit
  rcases getElem?_append_cases hit with hleft | hright
  · exact termChildrenBefore_append_left hleft.1 (hx i t hleft.2)
  · rcases hright with ⟨hi, hit'⟩
    have hlocal := hy (i - xs.length) t hit'
    have hshift := termChildrenBefore_append_right (xs := xs) hlocal
    have heq : xs.length + (i - xs.length) = i := Nat.add_sub_of_le hi
    simpa [heq] using hshift

theorem termPostorderOK_snoc {xs : List Term} {t : Term}
    (hx : TermPostorderOK xs)
    (hroot : TermChildrenBefore (xs ++ [t]) xs.length t) :
    TermPostorderOK (xs ++ [t]) := by
  intro i u hiu
  by_cases hi : i < xs.length
  · have hpre : xs[i]? = some u := by
      rw [← List.getElem?_append_left hi]
      exact hiu
    exact termChildrenBefore_append_left hi (hx i u hpre)
  · have hlen : i = xs.length := by
      have hlt := getElem?_some_lt hiu
      simp [List.length_append] at hlt
      omega
    subst hlen
    have hu : u = t := by
      have ht : (xs ++ [t])[xs.length]? = some t := by simp
      exact Option.some.inj (hiu.symm.trans ht)
    subst hu
    exact hroot

theorem termPostorder_ok : ∀ t : Term, TermPostorderOK (termPostorder t)
  | Term.zero => by
      exact termPostorderOK_snoc termPostorderOK_nil trivial
  | Term.var n => by
      exact termPostorderOK_snoc termPostorderOK_nil trivial
  | Term.succ t => by
      apply termPostorderOK_snoc (termPostorder_ok t)
      have hne := termPostorder_ne_nil t
      refine ⟨(termPostorder t).length - 1,
        Nat.pred_lt (List.length_pos_iff.mpr hne).ne',
        termPostorder_succ_child t⟩
  | Term.add s t => by
      apply termPostorderOK_snoc
        (termPostorderOK_append (termPostorder_ok s) (termPostorder_ok t))
      have hs := termPostorder_ne_nil s
      have ht := termPostorder_ne_nil t
      have hspos : 0 < (termPostorder s).length := List.length_pos_iff.mpr hs
      have htpos : 0 < (termPostorder t).length := List.length_pos_iff.mpr ht
      refine ⟨(termPostorder s).length - 1,
        (termPostorder s).length + ((termPostorder t).length - 1), ?_, ?_, ?_, ?_⟩
      · simp [List.length_append]
        omega
      · simp [List.length_append]
        omega
      · have hjlt : (termPostorder s).length - 1 <
            (termPostorder s ++ termPostorder t).length := by
          simp [List.length_append]
          omega
        have houter := List.getElem?_append_left (l₂ := [Term.add s t]) hjlt
        have hprefix :
            (termPostorder s ++ termPostorder t)[(termPostorder s).length - 1]? =
              some s := by
          have hinner := List.getElem?_append_left
            (l₂ := termPostorder t) (Nat.pred_lt hspos.ne')
          exact hinner.trans (getLast?_some_getElem? (termPostorder_getLast s) hs)
        exact houter.trans hprefix
      · have hklt : (termPostorder s).length + ((termPostorder t).length - 1) <
            (termPostorder s ++ termPostorder t).length := by
          simp [List.length_append]
          omega
        have houter := List.getElem?_append_left (l₂ := [Term.add s t]) hklt
        have hprefix :
            (termPostorder s ++ termPostorder t)[(termPostorder s).length +
              ((termPostorder t).length - 1)]? = some t := by
          have hinner := List.getElem?_append_right
            (l₁ := termPostorder s) (l₂ := termPostorder t)
            (i := (termPostorder s).length + ((termPostorder t).length - 1))
            (Nat.le_add_right _ _)
          exact hinner.trans (by
            simpa using getLast?_some_getElem? (termPostorder_getLast t) ht)
        exact houter.trans hprefix
  | Term.mul s t => by
      apply termPostorderOK_snoc
        (termPostorderOK_append (termPostorder_ok s) (termPostorder_ok t))
      have hs := termPostorder_ne_nil s
      have ht := termPostorder_ne_nil t
      have hspos : 0 < (termPostorder s).length := List.length_pos_iff.mpr hs
      have htpos : 0 < (termPostorder t).length := List.length_pos_iff.mpr ht
      refine ⟨(termPostorder s).length - 1,
        (termPostorder s).length + ((termPostorder t).length - 1), ?_, ?_, ?_, ?_⟩
      · simp [List.length_append]
        omega
      · simp [List.length_append]
        omega
      · have hjlt : (termPostorder s).length - 1 <
            (termPostorder s ++ termPostorder t).length := by
          simp [List.length_append]
          omega
        have houter := List.getElem?_append_left (l₂ := [Term.mul s t]) hjlt
        have hprefix :
            (termPostorder s ++ termPostorder t)[(termPostorder s).length - 1]? =
              some s := by
          have hinner := List.getElem?_append_left
            (l₂ := termPostorder t) (Nat.pred_lt hspos.ne')
          exact hinner.trans (getLast?_some_getElem? (termPostorder_getLast s) hs)
        exact houter.trans hprefix
      · have hklt : (termPostorder s).length + ((termPostorder t).length - 1) <
            (termPostorder s ++ termPostorder t).length := by
          simp [List.length_append]
          omega
        have houter := List.getElem?_append_left (l₂ := [Term.mul s t]) hklt
        have hprefix :
            (termPostorder s ++ termPostorder t)[(termPostorder s).length +
              ((termPostorder t).length - 1)]? = some t := by
          have hinner := List.getElem?_append_right
            (l₁ := termPostorder s) (l₂ := termPostorder t)
            (i := (termPostorder s).length + ((termPostorder t).length - 1))
            (Nat.le_add_right _ _)
          exact hinner.trans (by
            simpa using getLast?_some_getElem? (termPostorder_getLast t) ht)
        exact houter.trans hprefix

theorem termTable_entry_local (y c d L : Nat) (root node : Term) (i : Nat)
    (hi : i ≤ L) (hnode : (termPostorder root)[i]? = some node)
    (hpack : ∀ j, j ≤ L → beta c d j = termTable y root j) :
    TermSubstJustNat c d i (numCode y) (encodeTerm node)
      (substTermCode y (encodeTerm node)) := by
  have hchildren := termPostorder_ok root i node hnode
  cases node with
  | zero =>
      exact Or.inl ⟨rfl, substTermCode_zero y⟩
  | succ t =>
      rcases hchildren with ⟨j, hj, hjnode⟩
      apply Or.inr
      apply Or.inl
      refine ⟨encodeTerm t, substTermCode y (encodeTerm t), j,
        rfl, substTermCode_succ y (encodeTerm t), hj, ?_⟩
      have hβ := hpack j (Nat.le_trans (Nat.le_of_lt hj) hi)
      simp only [termTable, hjnode, termPair] at hβ
      exact hβ.symm
  | add s t =>
      rcases hchildren with ⟨j, k, hj, hk, hjs, hkt⟩
      apply Or.inr
      apply Or.inr
      apply Or.inl
      refine ⟨encodeTerm s, encodeTerm t,
        substTermCode y (encodeTerm s), substTermCode y (encodeTerm t), j, k,
        rfl, substTermCode_add y (encodeTerm s) (encodeTerm t), hj, hk, ?_, ?_⟩
      · have hβ := hpack j (Nat.le_trans (Nat.le_of_lt hj) hi)
        simp only [termTable, hjs, termPair] at hβ
        exact hβ.symm
      · have hβ := hpack k (Nat.le_trans (Nat.le_of_lt hk) hi)
        simp only [termTable, hkt, termPair] at hβ
        exact hβ.symm
  | mul s t =>
      rcases hchildren with ⟨j, k, hj, hk, hjs, hkt⟩
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inl
      refine ⟨encodeTerm s, encodeTerm t,
        substTermCode y (encodeTerm s), substTermCode y (encodeTerm t), j, k,
        rfl, substTermCode_mul y (encodeTerm s) (encodeTerm t), hj, hk, ?_, ?_⟩
      · have hβ := hpack j (Nat.le_trans (Nat.le_of_lt hj) hi)
        simp only [termTable, hjs, termPair] at hβ
        exact hβ.symm
      · have hβ := hpack k (Nat.le_trans (Nat.le_of_lt hk) hi)
        simp only [termTable, hkt, termPair] at hβ
        exact hβ.symm
  | var n =>
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      cases n with
      | zero =>
          exact Or.inl ⟨rfl, substTermCode_var0 y⟩
      | succ n =>
          exact Or.inr ⟨⟨n + 1, rfl, Nat.succ_pos n⟩,
            substTermCode_var_pos y n⟩

theorem termSubstTrace_complete (y : Nat) (t : Term) :
    ∃ c d L,
      ccons (encodeTerm t) (substTermCode y (encodeTerm t)) = beta c d L ∧
        TermSubstTrace c d L (numCode y) := by
  let L := (termPostorder t).length - 1
  obtain ⟨c, d, hpack⟩ := beta_exists L (termTable y t)
  refine ⟨c, d, L, ?_, ?_⟩
  · have hne := termPostorder_ne_nil t
    have hroot : (termPostorder t)[L]? = some t := by
      dsimp [L]
      exact getLast?_some_getElem? (termPostorder_getLast t) hne
    have hβ := hpack L (Nat.le_refl L)
    simp only [termTable, hroot, termPair] at hβ
    exact hβ.symm
  · intro i hi
    have hpos : 0 < (termPostorder t).length :=
      List.length_pos_iff.mpr (termPostorder_ne_nil t)
    have hilt : i < (termPostorder t).length := by
      dsimp [L] at hi
      omega
    let node : Term := (termPostorder t)[i]
    have hnode : (termPostorder t)[i]? = some node := by
      simpa [node] using List.getElem?_eq_getElem hilt
    refine ⟨encodeTerm node, substTermCode y (encodeTerm node), ?_, ?_⟩
    · have hβ := hpack i hi
      simp only [termTable, hnode, termPair] at hβ
      exact hβ.symm
    · exact termTable_entry_local y c d L t node i hi hnode hpack

theorem termSubstClosed_sound (env : Nat → Nat) (y x z : Nat)
    (h : evalForm env
      (termSubstClosed (numeral x) (numeral z) (numeral (numCode y)))) :
    z = substTermCode y x := by
  rcases (eval_termSubstClosed_numerals env x z (numCode y)).1 h with
    ⟨c, d, L, hlast, htrace⟩
  exact termSubstTrace_entry_sound y c d L (numCode y) rfl htrace
    L (Nat.le_refl L) x z hlast.symm

theorem termSubstClosed_complete (env : Nat → Nat) (y : Nat) (t : Term) :
    evalForm env (termSubstClosed (numeral (encodeTerm t))
      (numeral (substTermCode y (encodeTerm t))) (numeral (numCode y))) := by
  apply (eval_termSubstClosed_numerals env _ _ _).2
  exact termSubstTrace_complete y t

def TermSubstGraph (ncode inC outC : Nat) : Prop :=
  ∃ c d L, ccons inC outC = beta c d L ∧ TermSubstTrace c d L ncode

theorem eval_termSubstJust_tableVars_codeVar210 (env : Nat → Nat) :
    evalForm env (termSubstJust (Term.var 220) (Term.var 221) (Term.var 223)
      (Term.var 210) (Term.var 224) (Term.var 225)) ↔
      TermSubstJustNat (env 220) (env 221) (env 223) (env 210)
        (env 224) (env 225) := by
  simp [termSubstJust, TermSubstJustNat, termSubstZeroCase,
    termSubstSuccCase, termSubstAddCase, termSubstMulCase,
    termSubstVarCase, eval_existsF, eval_andF, eval_orF,
    eval_eqCcons, eval_cconsTerm, eval_ltF_var_var,
    eval_ltF_numeral_var, eval_betaF_vars_ccons,
    evalForm, evalTerm, evalTerm_numeral]

theorem eval_termSubstClosed_vars_241_243_210 (env : Nat → Nat) :
    evalForm env (termSubstClosed (Term.var 241) (Term.var 243) (Term.var 210)) ↔
      TermSubstGraph (env 210) (env 241) (env 243) := by
  simp [termSubstClosed, TermSubstGraph, TermSubstTrace, eval_existsF,
    eval_andF, evalForm_all, evalForm_imp, eval_leF_var_var,
    eval_betaF_vars_ccons, eval_termSubstJust_tableVars_codeVar210,
    evalTerm]

theorem eval_termSubstClosed_vars_242_244_210 (env : Nat → Nat) :
    evalForm env (termSubstClosed (Term.var 242) (Term.var 244) (Term.var 210)) ↔
      TermSubstGraph (env 210) (env 242) (env 244) := by
  simp [termSubstClosed, TermSubstGraph, TermSubstTrace, eval_existsF,
    eval_andF, evalForm_all, evalForm_imp, eval_leF_var_var,
    eval_betaF_vars_ccons, eval_termSubstJust_tableVars_codeVar210,
    evalTerm]

def FormSubstJustNat (c d i ncode inC outC : Nat) : Prop :=
  (∃ a b a' b',
    inC = ccons 0 (ccons a b) ∧ outC = ccons 0 (ccons a' b') ∧
      TermSubstGraph ncode a a' ∧ TermSubstGraph ncode b b') ∨
  (∃ a a' j, inC = ccons 1 a ∧ outC = ccons 1 a' ∧ j < i ∧
    ccons a a' = beta c d j) ∨
  (∃ a b a' b' j k,
    inC = ccons 2 (ccons a b) ∧ outC = ccons 2 (ccons a' b') ∧
      j < i ∧ k < i ∧ ccons a a' = beta c d j ∧
      ccons b b' = beta c d k) ∨
  (∃ x a a' j,
    inC = ccons 3 (ccons x a) ∧
      ((x = 0 ∧ outC = inC) ∨
        (x ≠ 0 ∧ outC = ccons 3 (ccons x a') ∧ j < i ∧
          ccons a a' = beta c d j)))

theorem eval_formSubstJust_tableVars (env : Nat → Nat) :
    evalForm env (formSubstJust (Term.var 250) (Term.var 251) (Term.var 253)
      (Term.var 210) (Term.var 254) (Term.var 255)) ↔
      FormSubstJustNat (env 250) (env 251) (env 253) (env 210)
        (env 254) (env 255) := by
  simp [formSubstJust, FormSubstJustNat, formSubstEqCase,
    formSubstNotCase, formSubstImpCase, formSubstAllCase,
    eval_existsF, eval_andF, eval_orF, eval_eqCcons, eval_cconsTerm,
    eval_ltF_var_var, eval_betaF_vars_ccons,
    eval_termSubstClosed_vars_241_243_210,
    eval_termSubstClosed_vars_242_244_210,
    evalForm, evalTerm, evalTerm_numeral]

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
