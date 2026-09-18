import OperatorKO7.Meta.DistinctionBoundary.GodelSubstitutionRelationSemantics
import OperatorKO7.Meta.DistinctionBoundary.GodelFirstIncompleteness
set_option autoImplicit false
namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- The arithmetized provability predicate is semantically equivalent to the live proof calculus. -/
theorem eval_bewOf_iff_provable (φ : Formula) :
    evalForm env0 (bewOf φ) ↔ Provable φ := by
  unfold bewOf
  rw [eval_existsF]
  constructor
  · rintro ⟨s, hs⟩
    have hs' : evalForm (envUpdate env0 0 s)
        (proofRel (Term.var 0) (numeral (encodeFormula φ))) := by
      simpa [envUpdate, formulaCode_eq] using hs
    exact proofRel_var0_implies_provable (envUpdate env0 0 s) hs'
  · rintro ⟨p, hp⟩
    refine ⟨proofRecoding (encodeProof p), ?_⟩
    have h := proofRel_packed_of_check_var0 hp
    rw [← proofRecoding_encode_of_check hp] at h
    simpa [envUpdate, formulaCode_eq] using h

#check eval_bewOf_iff_provable
#print axioms eval_bewOf_iff_provable


private theorem proofRel_vars12_fresh_zero :
    formHasVar 0 (proofRel (Term.var 1) (Term.var 2)) = false := by
  decide

private theorem eval_godelMatrix_body_iff_provable :
    evalForm (envUpdate env0 0 godelMatrixCode)
      (existsF 1 (existsF 2
        (andF (substRel (Term.var 0) (Term.var 0) (Term.var 2))
          (proofRel (Term.var 1) (Term.var 2))))) ↔
      Provable arithGodelSentence := by
  let envG : Nat → Nat := envUpdate env0 0 godelMatrixCode
  constructor
  · intro h
    have hOuter : evalForm envG
        (existsF 1 (existsF 2
          (andF (substRel (Term.var 0) (Term.var 0) (Term.var 2))
            (proofRel (Term.var 1) (Term.var 2))))) := by
      simpa [envG] using h
    rcases (eval_existsF envG 1 _).1 hOuter with ⟨pcode, h1⟩
    let e1 : Nat → Nat := envUpdate envG 1 pcode
    have h1' : evalForm e1
        (existsF 2 (andF (substRel (Term.var 0) (Term.var 0) (Term.var 2))
          (proofRel (Term.var 1) (Term.var 2)))) := by
      simpa [e1, envUpdate] using h1
    rcases (eval_existsF e1 2 _).1 h1' with ⟨z, h2⟩
    let e2 : Nat → Nat := envUpdate e1 2 z
    have h2' : evalForm e2
        (andF (substRel (Term.var 0) (Term.var 0) (Term.var 2))
          (proofRel (Term.var 1) (Term.var 2))) := by
      simpa [e2, envUpdate] using h2
    rcases (eval_andF e2 _ _).1 h2' with ⟨hsubst, hproof⟩
    have h0 : e2 0 = godelMatrixCode := by
      simp [e2, e1, envG, envUpdate]
    have hz : e2 2 = formulaCode arithGodelSentence :=
      (eval_substRel_godel_open e2 h0).1 hsubst
    have hz' : e2 2 = encodeFormula arithGodelSentence :=
      hz.trans (formulaCode_eq arithGodelSentence)
    exact proofRel_vars12_implies_provable e2 hz' hproof
  · rintro ⟨p, hp⟩
    apply (eval_existsF envG 1 _).2
    refine ⟨proofRecoding (encodeProof p), ?_⟩
    let e1 : Nat → Nat := envUpdate envG 1 (proofRecoding (encodeProof p))
    have hInner : evalForm e1
        (existsF 2 (andF (substRel (Term.var 0) (Term.var 0) (Term.var 2))
          (proofRel (Term.var 1) (Term.var 2)))) := by
      apply (eval_existsF e1 2 _).2
      refine ⟨formulaCode arithGodelSentence, ?_⟩
      let e2 : Nat → Nat := envUpdate e1 2 (formulaCode arithGodelSentence)
      have h0 : e2 0 = godelMatrixCode := by
        simp [e2, e1, envG, envUpdate]
      have hsubst : evalForm e2
          (substRel (Term.var 0) (Term.var 0) (Term.var 2)) := by
        apply (eval_substRel_godel_open e2 h0).2
        simp [e2, envUpdate]
      have hbase := proofRel_recoded_of_check_vars12 hp
      let baseEnv : Nat → Nat :=
        envUpdate (envUpdate env0 1 (proofRecoding (encodeProof p))) 2
          (formulaCode arithGodelSentence)
      have hbase' : evalForm baseEnv (proofRel (Term.var 1) (Term.var 2)) := by
        simpa [baseEnv] using hbase
      have hadded : evalForm (envUpdate baseEnv 0 godelMatrixCode)
          (proofRel (Term.var 1) (Term.var 2)) :=
        (evalForm_update_fresh baseEnv 0 godelMatrixCode _
          proofRel_vars12_fresh_zero).2 hbase'
      have henv : ∀ x, envUpdate baseEnv 0 godelMatrixCode x = e2 x := by
        intro x
        by_cases hx0 : x = 0
        · subst x
          simp [baseEnv, e2, e1, envG, envUpdate]
        · by_cases hx1 : x = 1
          · subst x
            simp [baseEnv, e2, e1, envG, envUpdate]
          · by_cases hx2 : x = 2
            · subst x
              simp [baseEnv, e2, e1, envG, envUpdate]
            · simp [baseEnv, e2, e1, envG, envUpdate, hx0, hx1, hx2]
      have hproof : evalForm e2 (proofRel (Term.var 1) (Term.var 2)) :=
        (evalForm_env_eq_aux _ henv).1 hadded
      have hAnd := (eval_andF e2
        (substRel (Term.var 0) (Term.var 0) (Term.var 2))
        (proofRel (Term.var 1) (Term.var 2))).2 ⟨hsubst, hproof⟩
      simpa [e2, envUpdate] using hAnd
    simpa [e1, envG, envUpdate] using hInner
/-- The matrix at its own code is true exactly when the Gödel sentence is unprovable. -/
theorem eval_godelMatrix_at_code_iff_not_provable :
    evalForm (envUpdate env0 0 godelMatrixCode) godelMatrix ↔
      ¬ Provable arithGodelSentence := by
  unfold godelMatrix
  rw [evalForm_not]
  exact not_congr eval_godelMatrix_body_iff_provable

/-- Standard-model fixed-point semantics for the live arithmetized Gödel sentence. -/
theorem eval_arithGodelSentence_iff_not_provable :
    evalForm env0 arithGodelSentence ↔ ¬ Provable arithGodelSentence := by
  rw [arithGodel_eq_subst]
  exact (evalForm_substNum env0 godelMatrixCode godelMatrix).trans
    eval_godelMatrix_at_code_iff_not_provable

/-- The previously explicit fixed-point premise is inhabited by the live arithmetization. -/
theorem arithGodelFixedPointSemantics_holds : ArithGodelFixedPointSemantics := by
  exact eval_arithGodelSentence_iff_not_provable

/-- Unconditional first incompleteness for the compiled Robinson-Q checker. -/
theorem godel_first_incompleteness_Q_unconditional :
    ¬ Provable arithGodelSentence ∧
      ¬ Provable (Formula.not arithGodelSentence) :=
  godel_first_incompleteness_Q arithGodelFixedPointSemantics_holds

#check eval_godelMatrix_body_iff_provable
#check eval_arithGodelSentence_iff_not_provable
#check arithGodelFixedPointSemantics_holds
#check godel_first_incompleteness_Q_unconditional
#print axioms eval_godelMatrix_body_iff_provable
#print axioms eval_arithGodelSentence_iff_not_provable
#print axioms arithGodelFixedPointSemantics_holds
#print axioms godel_first_incompleteness_Q_unconditional
end OperatorKO7.Meta.DistinctionBoundary.GodelArith

