import OperatorKO7.Meta.DistinctionBoundary.GodelFixedPointSemantics

set_option autoImplicit false

/-!
# Tarski's undefinability of truth for the checker's arithmetic

The diagonal lemma of `GodelFixedPointSemantics` is stated for the provability
matrix `godelMatrix` only. This module builds the diagonal matrix of an
arbitrary formula `ψ` on the same coded substitution relation `substRel`,
proves that its numeral instance at its own code is a sentence true in the
standard model exactly when `ψ` holds at the code of that sentence
(`general_diagonal`, `diagSentence_isSentence`), and derives Tarski's theorem:
no formula of the language defines truth for sentences
(`tarski_undefinability`).

The control `pair_separator_definable` states that the formula `x = ⌜γ⌝` of
the Gödel sentence `γ` is true at `⌜γ⌝`, false at `⌜¬γ⌝`, and agrees with
truth on the pair `{γ, ¬γ}`: the obstruction of the pair is of record and not
of definability.

Codes are written with `formulaCode`, the opaque wrapper of `encodeFormula`
(`formulaCode_eq`); `definesTruth_iff_encode` states the truth condition with
`encodeFormula`.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-! ## Resets of variables to zero -/

/-- `resetVars ks ψ` binds every variable of `ks` to zero in front of `ψ`. -/
def resetVars : List Nat → Formula → Formula
  | [], ψ => ψ
  | k :: ks, ψ =>
      existsF k (andF (Formula.eq (Term.var k) Term.zero) (resetVars ks ψ))

/-- The environment after the resets of `resetVars ks`. -/
def resetEnv : List Nat → (Nat → Nat) → Nat → Nat
  | [], e => e
  | k :: ks, e => resetEnv ks (envUpdate e k 0)

theorem resetEnv_apply : ∀ (ks : List Nat) (e : Nat → Nat) (y : Nat),
    resetEnv ks e y = if y ∈ ks then 0 else e y
  | [], e, y => by simp [resetEnv]
  | k :: ks, e, y => by
      rw [resetEnv, resetEnv_apply ks]
      by_cases hy : y ∈ ks
      · simp [hy]
      · by_cases hk : y = k
        · subst hk
          simp [hy, envUpdate]
        · simp [hy, hk, envUpdate]

theorem eval_resetVars : ∀ (ks : List Nat) (e : Nat → Nat) (ψ : Formula),
    evalForm e (resetVars ks ψ) ↔ evalForm (resetEnv ks e) ψ
  | [], e, ψ => Iff.rfl
  | k :: ks, e, ψ => by
      rw [resetVars, eval_existsF]
      constructor
      · rintro ⟨n, hn⟩
        rw [eval_andF] at hn
        rcases hn with ⟨h0, hrest⟩
        have hn0 : n = 0 := by simpa [evalForm, evalTerm] using h0
        subst hn0
        exact (eval_resetVars ks _ ψ).1 hrest
      · intro h
        refine ⟨0, ?_⟩
        rw [eval_andF]
        exact ⟨by simp [evalForm, evalTerm], (eval_resetVars ks _ ψ).2 h⟩

theorem formHasVar_resetVars (x : Nat) : ∀ (ks : List Nat) (ψ : Formula),
    formHasVar x (resetVars ks ψ) = if x ∈ ks then false else formHasVar x ψ
  | [], ψ => by simp [resetVars]
  | k :: ks, ψ => by
      have ih := formHasVar_resetVars x ks ψ
      by_cases hk : k = x
      · subst hk
        simp [resetVars, existsF, andF, formHasVar]
      · have hk' : x ≠ k := fun h => hk h.symm
        simp [resetVars, existsF, andF, formHasVar, termHasVar, hk, hk', ih]

/-! ## A bound on the variables of a formula -/

/-- The largest variable index in a term. -/
def termMaxVar : Term → Nat
  | Term.zero => 0
  | Term.succ t => termMaxVar t
  | Term.add s t => max (termMaxVar s) (termMaxVar t)
  | Term.mul s t => max (termMaxVar s) (termMaxVar t)
  | Term.var y => y

/-- The largest variable index in a formula, bound variables excluded. -/
def formMaxVar : Formula → Nat
  | Formula.eq s t => max (termMaxVar s) (termMaxVar t)
  | Formula.not φ => formMaxVar φ
  | Formula.imp φ ψ => max (formMaxVar φ) (formMaxVar ψ)
  | Formula.all _ φ => formMaxVar φ

theorem termHasVar_of_maxVar_lt (x : Nat) :
    ∀ t : Term, termMaxVar t < x → termHasVar x t = false
  | Term.zero, _ => rfl
  | Term.succ t, h => termHasVar_of_maxVar_lt x t h
  | Term.add s t, h => by
      simp only [termMaxVar, Nat.max_lt] at h
      simp [termHasVar, termHasVar_of_maxVar_lt x s h.1,
        termHasVar_of_maxVar_lt x t h.2]
  | Term.mul s t, h => by
      simp only [termMaxVar, Nat.max_lt] at h
      simp [termHasVar, termHasVar_of_maxVar_lt x s h.1,
        termHasVar_of_maxVar_lt x t h.2]
  | Term.var y, h => by
      simp only [termMaxVar] at h
      simp only [termHasVar, decide_eq_false_iff_not]
      omega

theorem formHasVar_of_maxVar_lt (x : Nat) :
    ∀ φ : Formula, formMaxVar φ < x → formHasVar x φ = false
  | Formula.eq s t, h => by
      simp only [formMaxVar, Nat.max_lt] at h
      simp [formHasVar, termHasVar_of_maxVar_lt x s h.1,
        termHasVar_of_maxVar_lt x t h.2]
  | Formula.not φ, h => formHasVar_of_maxVar_lt x φ h
  | Formula.imp φ ψ, h => by
      simp only [formMaxVar, Nat.max_lt] at h
      simp [formHasVar, formHasVar_of_maxVar_lt x φ h.1,
        formHasVar_of_maxVar_lt x ψ h.2]
  | Formula.all _ φ, h => by
      simp [formHasVar, formHasVar_of_maxVar_lt x φ h]

/-! ## Free variables after the substitution of a numeral for variable 0 -/

theorem termHasVar_subst_zero (n : Nat) :
    ∀ t : Term, termHasVar 0 (substTerm 0 (numeral n) t) = false
  | Term.zero => rfl
  | Term.succ t => by simp [substTerm, termHasVar, termHasVar_subst_zero n t]
  | Term.add s t => by
      simp [substTerm, termHasVar, termHasVar_subst_zero n s, termHasVar_subst_zero n t]
  | Term.mul s t => by
      simp [substTerm, termHasVar, termHasVar_subst_zero n s, termHasVar_subst_zero n t]
  | Term.var y => by
      by_cases hy : y = 0
      · simp [substTerm, hy, numeral_closed]
      · simp [substTerm, termHasVar, hy]

theorem termHasVar_subst_ne (n : Nat) {x : Nat} (hx : x ≠ 0) :
    ∀ t : Term, termHasVar x (substTerm 0 (numeral n) t) = termHasVar x t
  | Term.zero => rfl
  | Term.succ t => by simp [substTerm, termHasVar, termHasVar_subst_ne n hx t]
  | Term.add s t => by
      simp [substTerm, termHasVar, termHasVar_subst_ne n hx s, termHasVar_subst_ne n hx t]
  | Term.mul s t => by
      simp [substTerm, termHasVar, termHasVar_subst_ne n hx s, termHasVar_subst_ne n hx t]
  | Term.var y => by
      by_cases hy : y = 0
      · subst hy
        have hx' : (0 = x) = False := propext ⟨fun h => hx h.symm, False.elim⟩
        simp [substTerm, termHasVar, numeral_closed, hx']
      · simp [substTerm, termHasVar, hy]

theorem formHasVar_subst_zero (n : Nat) :
    ∀ φ : Formula, formHasVar 0 (substForm 0 (numeral n) φ) = false
  | Formula.eq s t => by
      simp [substForm, formHasVar, termHasVar_subst_zero]
  | Formula.not φ => by simp [substForm, formHasVar, formHasVar_subst_zero n φ]
  | Formula.imp φ ψ => by
      simp [substForm, formHasVar, formHasVar_subst_zero n φ, formHasVar_subst_zero n ψ]
  | Formula.all y φ => by
      by_cases hy : y = 0
      · subst hy
        simp [substForm, formHasVar]
      · simp [substForm, formHasVar, hy, formHasVar_subst_zero n φ]

theorem formHasVar_subst_ne (n : Nat) {x : Nat} (hx : x ≠ 0) :
    ∀ φ : Formula, formHasVar x (substForm 0 (numeral n) φ) = formHasVar x φ
  | Formula.eq s t => by
      simp [substForm, formHasVar, termHasVar_subst_ne n hx]
  | Formula.not φ => by simp [substForm, formHasVar, formHasVar_subst_ne n hx φ]
  | Formula.imp φ ψ => by
      simp [substForm, formHasVar, formHasVar_subst_ne n hx φ,
        formHasVar_subst_ne n hx ψ]
  | Formula.all y φ => by
      by_cases hy : y = 0
      · subst hy
        simp [substForm]
      · simp [substForm, formHasVar, hy, formHasVar_subst_ne n hx φ]

/-! ## The free variables of the open substitution relation -/

/-- The variable indices of a term, with repetitions. -/
def termVarList : Term → List Nat
  | Term.zero => []
  | Term.succ t => termVarList t
  | Term.add s t => termVarList s ++ termVarList t
  | Term.mul s t => termVarList s ++ termVarList t
  | Term.var y => [y]

/-- The free variable indices of a formula, with repetitions. -/
def freeVarList : Formula → List Nat
  | Formula.eq s t => termVarList s ++ termVarList t
  | Formula.not φ => freeVarList φ
  | Formula.imp φ ψ => freeVarList φ ++ freeVarList ψ
  | Formula.all y φ => (freeVarList φ).filter (fun v => v != y)

theorem mem_termVarList_of_termHasVar (x : Nat) :
    ∀ t : Term, termHasVar x t = true → x ∈ termVarList t
  | Term.zero, h => by simp [termHasVar] at h
  | Term.succ t, h => mem_termVarList_of_termHasVar x t h
  | Term.add s t, h => by
      simp only [termHasVar, Bool.or_eq_true] at h
      rcases h with h | h
      · exact List.mem_append_left _ (mem_termVarList_of_termHasVar x s h)
      · exact List.mem_append_right _ (mem_termVarList_of_termHasVar x t h)
  | Term.mul s t, h => by
      simp only [termHasVar, Bool.or_eq_true] at h
      rcases h with h | h
      · exact List.mem_append_left _ (mem_termVarList_of_termHasVar x s h)
      · exact List.mem_append_right _ (mem_termVarList_of_termHasVar x t h)
  | Term.var y, h => by
      simp only [termHasVar, decide_eq_true_eq] at h
      simp [termVarList, h]

theorem mem_freeVarList_of_formHasVar (x : Nat) :
    ∀ φ : Formula, formHasVar x φ = true → x ∈ freeVarList φ
  | Formula.eq s t, h => by
      simp only [formHasVar, Bool.or_eq_true] at h
      rcases h with h | h
      · exact List.mem_append_left _ (mem_termVarList_of_termHasVar x s h)
      · exact List.mem_append_right _ (mem_termVarList_of_termHasVar x t h)
  | Formula.not φ, h => mem_freeVarList_of_formHasVar x φ h
  | Formula.imp φ ψ, h => by
      simp only [formHasVar, Bool.or_eq_true] at h
      rcases h with h | h
      · exact List.mem_append_left _ (mem_freeVarList_of_formHasVar x φ h)
      · exact List.mem_append_right _ (mem_freeVarList_of_formHasVar x ψ h)
  | Formula.all y φ, h => by
      by_cases hy : y = x
      · simp [formHasVar, hy] at h
      · simp only [formHasVar, hy, if_false] at h
        simp only [freeVarList, List.mem_filter, bne_iff_ne, ne_eq]
        exact ⟨mem_freeVarList_of_formHasVar x φ h, fun h' => hy h'.symm⟩

theorem substRel_open_freeVarList :
    (freeVarList (substRel (Term.var 0) (Term.var 0) (Term.var 2))).all
      (fun v => v == 0 || v == 2) = true := by
  decide

/-- The open substitution relation `substRel(v0, v0, v2)` has the free variables `0` and `2` only. -/
theorem substRel_open_free (x : Nat) (h0 : x ≠ 0) (h2 : x ≠ 2) :
    formHasVar x (substRel (Term.var 0) (Term.var 0) (Term.var 2)) = false := by
  cases hx : formHasVar x (substRel (Term.var 0) (Term.var 0) (Term.var 2)) with
  | false => rfl
  | true =>
      have hm := mem_freeVarList_of_formHasVar x _ hx
      have hv := List.all_eq_true.1 substRel_open_freeVarList x hm
      simp only [Bool.or_eq_true, beq_iff_eq] at hv
      omega

/-! ## The open substitution relation at the code of an arbitrary matrix -/

/-- At an environment sending variable 0 to the code of a matrix `δ`, the open
substitution relation `substRel(v0, v0, v2)` holds exactly when variable 2 is
the code of the numeral instance of `δ` at its own code. The statement
generalizes `eval_substRel_godel_open` from `godelMatrix` to every `δ`. -/
theorem eval_substRel_diag_open (δ : Formula) (env : Nat → Nat)
    (h0 : env 0 = formulaCode δ) :
    evalForm env (substRel (Term.var 0) (Term.var 0) (Term.var 2)) ↔
      env 2 = formulaCode (substNum δ (formulaCode δ)) := by
  have hdiag : substFormCode (formulaCode δ) (formulaCode δ) =
      formulaCode (substNum δ (formulaCode δ)) :=
    substFormCode_formulaCode (formulaCode δ) δ
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
    have hn : ncode = numCode (formulaCode δ) := by
      simpa [e210, evalTerm, h0] using hnSem
    rcases (eval_formSubstClosed_var0_var2_var210 e210).1 hform with
      ⟨c, d, L, hlast, htrace⟩
    have htrace' : FormSubstTrace c d L (numCode (formulaCode δ)) := by
      simpa [e210, hn] using htrace
    have hz := formSubstTrace_entry_sound (formulaCode δ) c d L htrace'
      L (Nat.le_refl L) (e210 0) (e210 2) hlast.symm
    have hz' : env 2 = substFormCode (formulaCode δ) (formulaCode δ) := by
      simpa [e210, h0] using hz
    exact hz'.trans hdiag
  · intro hz
    refine ⟨numCode (formulaCode δ), ?_⟩
    let e210 : Nat → Nat := fun w => if w = 210 then numCode (formulaCode δ) else env w
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
      rcases formSubstTrace_complete (formulaCode δ) δ with ⟨c, d, L, hlast, htrace⟩
      refine ⟨c, d, L, ?_, ?_⟩
      · have hgoal : ccons (formulaCode δ) (formulaCode (substNum δ (formulaCode δ))) =
            beta c d L := by
          rw [← hdiag]
          rw [formulaCode_eq δ] at hlast ⊢
          exact hlast
        have he0 : e210 0 = formulaCode δ := by simp [e210, h0]
        have he2 : e210 2 = formulaCode (substNum δ (formulaCode δ)) := by simp [e210, hz]
        calc
          ccons (e210 0) (e210 2) =
              ccons (formulaCode δ) (formulaCode (substNum δ (formulaCode δ))) :=
            congrArg₂ ccons he0 he2
          _ = beta c d L := hgoal
      · simpa [e210] using htrace

/-! ## The general diagonal lemma -/

/-- The variables reset by the diagonal matrix of `ψ`: `1, …, formMaxVar ψ + 2`. -/
def diagResets (ψ : Formula) : List Nat :=
  List.range' 1 (formMaxVar ψ + 2)

theorem zero_not_mem_diagResets (ψ : Formula) : 0 ∉ diagResets ψ := by
  rw [diagResets, List.mem_range'_1]
  intro h
  omega

theorem two_mem_diagResets (ψ : Formula) : 2 ∈ diagResets ψ := by
  rw [diagResets, List.mem_range'_1]
  constructor <;> omega

theorem maxVar_lt_of_not_mem_diagResets (ψ : Formula) {x : Nat} (hx : x ≠ 0)
    (hm : x ∉ diagResets ψ) : formMaxVar ψ < x := by
  rw [diagResets, List.mem_range'_1] at hm
  by_contra hlt
  exact hm ⟨Nat.pos_of_ne_zero hx, by omega⟩

/-- Diagonal matrix of `ψ`: `∃ z (substRel(x, x, z) ∧ ψ(z))`, with `x` the
variable 0, `z` the variable 2, the argument `z` passed to the variable 0 of
`ψ`, and every other variable of `ψ` up to `formMaxVar ψ` reset to zero. -/
def diagMatrix (ψ : Formula) : Formula :=
  existsF 2 (andF (substRel (Term.var 0) (Term.var 0) (Term.var 2))
    (existsF 0 (andF (Formula.eq (Term.var 0) (Term.var 2))
      (resetVars (diagResets ψ) ψ))))

/-- The diagonal sentence of `ψ`: the numeral instance of `diagMatrix ψ` at its own code. -/
def diagSentence (ψ : Formula) : Formula :=
  substNum (diagMatrix ψ) (formulaCode (diagMatrix ψ))

theorem diagSentence_eq (ψ : Formula) :
    diagSentence ψ = substNum (diagMatrix ψ) (formulaCode (diagMatrix ψ)) :=
  rfl

theorem eval_diagMatrix_iff (ψ : Formula) (n : Nat) :
    evalForm (envUpdate env0 0 n) (diagMatrix ψ) ↔
      ∃ z : Nat,
        evalForm (fun y => if y = 2 then z else envUpdate env0 0 n y)
            (substRel (Term.var 0) (Term.var 0) (Term.var 2)) ∧
          evalForm (envUpdate env0 0 z) ψ := by
  unfold diagMatrix
  rw [eval_existsF]
  apply exists_congr
  intro z
  rw [eval_andF]
  apply and_congr Iff.rfl
  rw [eval_existsF]
  constructor
  · rintro ⟨w, hw⟩
    rw [eval_andF] at hw
    rcases hw with ⟨hwz, hr⟩
    have hw' : w = z := by simpa [evalForm, evalTerm] using hwz
    subst hw'
    rw [eval_resetVars] at hr
    refine (evalForm_env_eq_aux ψ ?_).1 hr
    intro y
    rw [resetEnv_apply]
    by_cases hy0 : y = 0
    · subst hy0
      simp [zero_not_mem_diagResets, envUpdate]
    · by_cases hyk : y ∈ diagResets ψ
      · simp [hyk, hy0, envUpdate, env0]
      · have hy2 : y ≠ 2 := fun h => hyk (by rw [h]; exact two_mem_diagResets ψ)
        simp [hyk, hy0, hy2, envUpdate, env0]
  · intro h
    refine ⟨z, ?_⟩
    rw [eval_andF]
    refine ⟨by simp [evalForm, evalTerm], ?_⟩
    rw [eval_resetVars]
    refine (evalForm_env_eq_aux ψ ?_).2 h
    intro y
    rw [resetEnv_apply]
    by_cases hy0 : y = 0
    · subst hy0
      simp [zero_not_mem_diagResets, envUpdate]
    · by_cases hyk : y ∈ diagResets ψ
      · simp [hyk, hy0, envUpdate, env0]
      · have hy2 : y ≠ 2 := fun h => hyk (by rw [h]; exact two_mem_diagResets ψ)
        simp [hyk, hy0, hy2, envUpdate, env0]

/-- General diagonal lemma for the checker's arithmetic: for every formula `ψ`,
the diagonal sentence of `ψ` is true in the standard model exactly when `ψ`
holds at the code of that sentence. -/
theorem general_diagonal (ψ : Formula) :
    evalForm env0 (diagSentence ψ) ↔
      evalForm env0 (substNum ψ (formulaCode (diagSentence ψ))) := by
  rw [evalForm_substNum env0 (formulaCode (diagSentence ψ)) ψ]
  rw [diagSentence_eq ψ]
  rw [evalForm_substNum env0 (formulaCode (diagMatrix ψ)) (diagMatrix ψ)]
  rw [eval_diagMatrix_iff]
  constructor
  · rintro ⟨z, hS, hψ⟩
    have hz := (eval_substRel_diag_open (diagMatrix ψ) _ (by simp [envUpdate])).1 hS
    have hz' : z = formulaCode (substNum (diagMatrix ψ) (formulaCode (diagMatrix ψ))) := by
      simpa using hz
    rw [← hz']
    exact hψ
  · intro h
    refine ⟨formulaCode (substNum (diagMatrix ψ) (formulaCode (diagMatrix ψ))), ?_, h⟩
    exact (eval_substRel_diag_open (diagMatrix ψ) _ (by simp [envUpdate])).2 (by simp)

theorem diagMatrix_free (ψ : Formula) (x : Nat) (hx : x ≠ 0) :
    formHasVar x (diagMatrix ψ) = false := by
  by_cases h2 : x = 2
  · subst h2
    simp [diagMatrix, existsF, formHasVar]
  · have hS := substRel_open_free x hx h2
    have hR : formHasVar x (resetVars (diagResets ψ) ψ) = false := by
      rw [formHasVar_resetVars]
      by_cases hm : x ∈ diagResets ψ
      · simp [hm]
      · simp only [hm, if_false]
        exact formHasVar_of_maxVar_lt x ψ (maxVar_lt_of_not_mem_diagResets ψ hx hm)
    have h0x : (0 = x) = False := propext ⟨fun h => hx h.symm, False.elim⟩
    have h2x : (2 = x) = False := propext ⟨fun h => h2 h.symm, False.elim⟩
    simp [diagMatrix, existsF, andF, formHasVar, termHasVar, hS, hR, h0x, h2x]

/-- The diagonal sentence of every formula has no free variable. -/
theorem diagSentence_isSentence (ψ : Formula) : IsSentence (diagSentence ψ) := by
  intro x
  show formHasVar x (substForm 0 (numeral (formulaCode (diagMatrix ψ))) (diagMatrix ψ)) = false
  by_cases hx : x = 0
  · subst hx
    exact formHasVar_subst_zero _ _
  · rw [formHasVar_subst_ne _ hx]
    exact diagMatrix_free ψ x hx

/-! ## Tarski's theorem -/

/-- `T` defines truth in the standard model on sentences: for every sentence
`φ`, the instance of `T` at the code of `φ` is true exactly when `φ` is true. -/
def DefinesTruth (T : Formula) : Prop :=
  ∀ φ : Formula, IsSentence φ →
    (evalForm env0 (substNum T (formulaCode φ)) ↔ evalForm env0 φ)

/-- The truth condition of `DefinesTruth` with the codes of `encodeFormula`. -/
theorem definesTruth_iff_encode (T : Formula) :
    DefinesTruth T ↔ ∀ φ : Formula, IsSentence φ →
      (evalForm env0 (substNum T (encodeFormula φ)) ↔ evalForm env0 φ) := by
  simp only [DefinesTruth, formulaCode_eq]

theorem substNum_not_eq (φ : Formula) (n : Nat) :
    substNum (Formula.not φ) n = Formula.not (substNum φ n) :=
  rfl

/-- Tarski's undefinability of truth for the checker's arithmetic: no formula
of the language defines truth in the standard model on sentences. -/
theorem tarski_undefinability : ¬ ∃ T : Formula, DefinesTruth T := by
  rintro ⟨T, hT⟩
  have hdiag := general_diagonal (Formula.not T)
  rw [substNum_not_eq, evalForm_not] at hdiag
  have hdef := hT (diagSentence (Formula.not T)) (diagSentence_isSentence _)
  exact iff_not_self (hdiag.trans (not_congr hdef))

/-! ## The control: the Gödel pair is separated by a definable formula -/

theorem formula_not_ne_self (φ : Formula) : Formula.not φ ≠ φ := by
  intro h
  have hs := congrArg sizeOf h
  simp at hs

/-- The formula `x = ⌜γ⌝` of the Gödel sentence `γ = arithGodelSentence`. -/
def godelSeparator : Formula :=
  Formula.eq (Term.var 0) (numeral (formulaCode arithGodelSentence))

theorem eval_godelSeparator (n : Nat) :
    evalForm env0 (substNum godelSeparator n) ↔ n = formulaCode arithGodelSentence := by
  rw [evalForm_substNum]
  simp [godelSeparator, evalForm, evalTerm, envUpdate, evalTerm_numeral]

/-- `S` separates the Gödel sentence from its negation and agrees with truth
on the pair `{γ, ¬γ}`. -/
def SeparatesGodelPair (S : Formula) : Prop :=
  evalForm env0 (substNum S (formulaCode arithGodelSentence)) ∧
    ¬ evalForm env0 (substNum S (formulaCode (Formula.not arithGodelSentence))) ∧
    (evalForm env0 (substNum S (formulaCode arithGodelSentence)) ↔
      evalForm env0 arithGodelSentence) ∧
    (evalForm env0 (substNum S (formulaCode (Formula.not arithGodelSentence))) ↔
      evalForm env0 (Formula.not arithGodelSentence))

/-- The formula `x = ⌜γ⌝` separates `γ` from `¬γ` and agrees with truth on
that pair: the obstruction of the pair is of record and not of definability. -/
theorem pair_separator_definable : SeparatesGodelPair godelSeparator := by
  have hγ : evalForm env0 arithGodelSentence :=
    eval_arithGodelSentence_iff_not_provable.2 godel_first_incompleteness_Q_unconditional.1
  have hne : formulaCode (Formula.not arithGodelSentence) ≠ formulaCode arithGodelSentence :=
    fun h => formula_not_ne_self _ (formulaCode_injective h)
  have h1 : evalForm env0 (substNum godelSeparator (formulaCode arithGodelSentence)) :=
    (eval_godelSeparator _).2 rfl
  have h2 : ¬ evalForm env0
      (substNum godelSeparator (formulaCode (Formula.not arithGodelSentence))) :=
    fun h => hne ((eval_godelSeparator _).1 h)
  have h3 : ¬ evalForm env0 (Formula.not arithGodelSentence) :=
    fun h => (evalForm_not env0 _).1 h hγ
  exact ⟨h1, h2, iff_of_true h1 hγ, iff_of_false h2 h3⟩

/-- Tarski's theorem with its control. -/
def TarskiGoal : Prop :=
  (¬ ∃ T : Formula, DefinesTruth T) ∧ SeparatesGodelPair godelSeparator

theorem tarskiGoal : TarskiGoal :=
  ⟨tarski_undefinability, pair_separator_definable⟩

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
