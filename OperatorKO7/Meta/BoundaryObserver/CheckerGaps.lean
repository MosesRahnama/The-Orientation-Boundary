import OperatorKO7.Meta.BoundaryObserver.EqualityRepair
import OperatorKO7.Meta.DistinctionBoundary.GodelGeneralSemantics
import OperatorKO7.Meta.DistinctionBoundary.GodelInductionChecker

/-!
# Two true sentences the checkers do not prove

Manuscript: the paragraph before Theorem `thm:godel-equality-repair` and Remark
`rem:godel-negation-gap`.

The base checker `T_0` has reflexivity as its only equality axiom. Reading addition as the second
projection, multiplication as zero and `a = b` as `a = b ∨ a = 0` validates every axiom and rule of
`T_0` and every induction instance, and falsifies the true equation `S(S(0)+0) = S(S(0))`; `T_0`
therefore does not prove it.

The repaired checker `T_E` adds the five equality schemes. The valuation that reads terms,
equations, implications and universal quantifiers in `ℕ`, reads `¬(s = t)` as true only when `t` has
value `0` and `s` a nonzero value, reads `¬∀x A` classically and reads every other negation as false,
validates every axiom and rule of `T_E` and every induction instance, and falsifies the true sentence
`¬(0 = S(0))`; `T_E` therefore does not prove it.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.CheckerGaps

open OperatorKO7.Meta.DistinctionBoundary.GodelArith
open OperatorKO7.Meta.BoundaryObserver.EqualityRepair

/-! ## The interpretation for the base checker -/

/-- `ℕ` with addition read as the second projection and multiplication as zero. -/
abbrev projStructure : ArithStructure where
  Carrier := ℕ
  zero := 0
  succ := fun n => n + 1
  add := fun _ b => b
  mul := fun _ _ => 0

/-- The translation that reads `s = t` as `s = t ∨ s = 0`. -/
def eqOrZero : Formula → Formula
  | .eq s t => orF (.eq s t) (.eq s Term.zero)
  | .not φ => .not (eqOrZero φ)
  | .imp φ ψ => .imp (eqOrZero φ) (eqOrZero ψ)
  | .all x φ => .all x (eqOrZero φ)

/-- The interpretation of the base checker's language with `a = b` read as `a = b ∨ a = 0`. -/
def evalAlt (env : ℕ → ℕ) (φ : Formula) : Prop :=
  evalFormIn projStructure env (eqOrZero φ)

@[simp] theorem pt_zero (env : ℕ → ℕ) : evalTermIn projStructure env Term.zero = 0 := rfl

@[simp] theorem pt_succ (env : ℕ → ℕ) (t : Term) :
    evalTermIn projStructure env (Term.succ t) = evalTermIn projStructure env t + 1 := rfl

@[simp] theorem pt_add (env : ℕ → ℕ) (s t : Term) :
    evalTermIn projStructure env (Term.add s t) = evalTermIn projStructure env t := rfl

@[simp] theorem pt_mul (env : ℕ → ℕ) (s t : Term) :
    evalTermIn projStructure env (Term.mul s t) = 0 := rfl

@[simp] theorem pt_var (env : ℕ → ℕ) (x : ℕ) :
    evalTermIn projStructure env (Term.var x) = env x := rfl

theorem evalAlt_eq (env : ℕ → ℕ) (s t : Term) :
    evalAlt env (.eq s t) ↔ (evalTermIn projStructure env s = evalTermIn projStructure env t ∨
      evalTermIn projStructure env s = 0) :=
  evalFormIn_orF projStructure env (.eq s t) (.eq s Term.zero)

theorem evalAlt_not (env : ℕ → ℕ) (φ : Formula) : evalAlt env (.not φ) ↔ ¬ evalAlt env φ :=
  Iff.rfl

theorem evalAlt_imp (env : ℕ → ℕ) (φ ψ : Formula) :
    evalAlt env (.imp φ ψ) ↔ (evalAlt env φ → evalAlt env ψ) := Iff.rfl

theorem evalAlt_all (env : ℕ → ℕ) (x : ℕ) (φ : Formula) :
    evalAlt env (.all x φ) ↔ ∀ n : ℕ, evalAlt (fun y => if y = x then n else env y) φ := Iff.rfl

theorem evalAlt_andF (env : ℕ → ℕ) (φ ψ : Formula) :
    evalAlt env (andF φ ψ) ↔ evalAlt env φ ∧ evalAlt env ψ :=
  evalFormIn_andF projStructure env (eqOrZero φ) (eqOrZero ψ)

theorem eqOrZero_subst (x : ℕ) (u : Term) :
    ∀ φ : Formula, eqOrZero (substForm x u φ) = substForm x u (eqOrZero φ)
  | .eq s t => by simp [eqOrZero, substForm, orF, substTerm]
  | .not φ => by simp [eqOrZero, substForm, eqOrZero_subst x u φ]
  | .imp φ ψ => by simp [eqOrZero, substForm, eqOrZero_subst x u φ, eqOrZero_subst x u ψ]
  | .all y φ => by
      by_cases h : y = x
      · simp [eqOrZero, substForm, h]
      · simp [eqOrZero, substForm, h, eqOrZero_subst x u φ]

theorem evalAlt_subst_closed (env : ℕ → ℕ) (x : ℕ) (u : Term) (hu : isClosedTerm u = true)
    (φ : Formula) :
    evalAlt env (substForm x u φ) ↔
      evalAlt (envUpdateIn projStructure env x (evalTermIn projStructure env u)) φ := by
  unfold evalAlt
  rw [eqOrZero_subst]
  exact evalFormIn_subst_closed projStructure env x u hu (eqOrZero φ)

/-- Substitution of a term whose only variable is the substituted one, in every structure. -/
theorem evalFormIn_subst_free (M : ArithStructure) (x : ℕ) (u : Term)
    (hu : ∀ y, y ≠ x → termHasVar y u = false) :
    ∀ (φ : Formula) (env : ℕ → M.Carrier),
      evalFormIn M env (substForm x u φ) ↔
        evalFormIn M (envUpdateIn M env x (evalTermIn M env u)) φ
  | .eq s t, env => by
      simp only [substForm, evalFormIn, evalTermIn_subst]
  | .not φ, env => by
      simp only [substForm, evalFormIn, evalFormIn_subst_free M x u hu φ env]
  | .imp φ ψ, env => by
      simp only [substForm, evalFormIn, evalFormIn_subst_free M x u hu φ env,
        evalFormIn_subst_free M x u hu ψ env]
  | .all y φ, env => by
      by_cases hyx : y = x
      · subst hyx
        rw [show substForm y u (Formula.all y φ) = Formula.all y φ from if_pos rfl]
        simp only [evalFormIn]
        refine forall_congr' (fun a => evalFormIn_env_eq_aux M φ (fun z => ?_))
        simp only [envUpdateIn]
        by_cases hz : z = y <;> simp [hz]
      · rw [show substForm x u (Formula.all y φ) = Formula.all y (substForm x u φ) from if_neg hyx]
        simp only [evalFormIn]
        refine forall_congr' (fun a => ?_)
        rw [evalFormIn_subst_free M x u hu φ]
        have hval : evalTermIn M (fun w => if w = y then a else env w) u = evalTermIn M env u :=
          evalTermIn_fresh M y u (hu y hyx) env a
        rw [hval]
        exact evalFormIn_env_eq_aux M φ (fun z => envUpdateIn_if_comm M env hyx _ a z)

theorem evalAlt_subst_selfSucc (env : ℕ → ℕ) (x : ℕ) (φ : Formula) :
    evalAlt env (substForm x (inductionStepTerm x) φ) ↔
      evalAlt (envUpdateIn projStructure env x (env x + 1)) φ := by
  unfold evalAlt
  rw [eqOrZero_subst]
  exact evalFormIn_subst_free projStructure x (inductionStepTerm x)
    (fun y hy => by simp [inductionStepTerm, termHasVar, hy, Ne.symm hy]) (eqOrZero φ) env

/-- Every induction instance holds in the interpretation. -/
theorem evalAlt_inductionAxiom (env : ℕ → ℕ) (x : ℕ) (φ : Formula) :
    evalAlt env (inductionAxiom x φ) := by
  unfold inductionAxiom
  rw [evalAlt_imp]
  intro hante
  obtain ⟨hbase, hstep⟩ := (evalAlt_andF env _ _).1 hante
  rw [evalAlt_subst_closed env x Term.zero rfl] at hbase
  rw [evalAlt_all] at hstep ⊢
  intro n
  induction n with
  | zero => exact hbase
  | succ k ih =>
      have h1 := (evalAlt_imp _ _ _).1 (hstep k) ih
      rw [evalAlt_subst_selfSucc] at h1
      refine (evalFormIn_env_eq_aux projStructure (eqOrZero φ) (fun z => ?_)).1 h1
      simp only [envUpdateIn]
      by_cases hz : z = x <;> simp [hz]

theorem evalAlt_isQAxiom (env : ℕ → ℕ) {φ : Formula} (h : isQAxiom φ = true) :
    evalAlt env φ := by
  rcases (isQAxiom_iff φ).1 h with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
  · simp [q1, evalAlt_all, evalAlt_not, evalAlt_eq]
  · simp only [q2, evalAlt_all, evalAlt_imp, evalAlt_eq, pt_succ, pt_var]
    intro n m h
    simp at h ⊢
    omega
  · simp [q3, evalAlt_all, evalAlt_eq]
  · simp [q4, evalAlt_all, evalAlt_eq]
  · simp [q5, evalAlt_all, evalAlt_eq]
  · simp [q6, evalAlt_all, evalAlt_eq]
  · simp only [q7, orF, existsF, evalAlt_all, evalAlt_imp, evalAlt_not, evalAlt_eq, pt_zero,
      pt_succ, pt_var]
    intro n hn hall
    simp at hn hall
    exact (hall (n - 1)).1 (by omega)

theorem evalAlt_isAxiom (env : ℕ → ℕ) {φ : Formula} (hax : isAxiom φ = true) : evalAlt env φ := by
  simp only [isAxiom, Bool.or_eq_true] at hax
  rcases hax with (((((hQ | hK) | hS) | hDNE) | hR) | hId)
  · exact evalAlt_isQAxiom env hQ
  · rcases isAxK_shape hK with ⟨a, b, rfl⟩
    rw [evalAlt_imp, evalAlt_imp]
    intro ha _
    exact ha
  · rcases isAxS_shape hS with ⟨a, b, c, rfl⟩
    simp only [evalAlt_imp]
    intro habc hab ha
    exact habc ha (hab ha)
  · rcases isAxDNE_shape hDNE with ⟨a, rfl⟩
    simp only [evalAlt_imp, evalAlt_not]
    intro hnn
    exact Classical.not_not.mp hnn
  · cases φ with
    | eq s t =>
      have hst : s = t := by simpa [isEqRefl] using hR
      subst hst
      exact (evalAlt_eq env s s).2 (Or.inl rfl)
    | not _ => simp [isEqRefl] at hR
    | imp _ _ => simp [isEqRefl] at hR
    | all _ _ => simp [isEqRefl] at hR
  · cases φ with
    | imp a b =>
      have hab : a = b := by simpa [isAxId] using hId
      subst hab
      rw [evalAlt_imp]
      exact id
    | eq _ _ => simp [isAxId] at hId
    | not _ => simp [isAxId] at hId
    | all _ _ => simp [isAxId] at hId

/-- **Soundness of the base checker for the interpretation.** -/
theorem check_sound_alt :
    ∀ p : ProofTree, ∀ φ : Formula, ∀ env : ℕ → ℕ, check p = some φ → evalAlt env φ := by
  intro p
  induction p with
  | ax ψ =>
      intro φ env h
      simp [check] at h
      rcases h with ⟨hax, rfl⟩
      exact evalAlt_isAxiom env hax
  | mp p q ihp ihq =>
      intro φ env h
      cases hp : check p with
      | none => simp [check, hp] at h
      | some a =>
        cases hq : check q with
        | none => simp [check, hp, hq] at h
        | some c =>
          cases a with
          | imp u v =>
              simp [check, hp, hq] at h
              rcases h with ⟨rfl, rfl⟩
              exact (evalAlt_imp env u v).1 (ihp (Formula.imp u v) env hp) (ihq u env hq)
          | eq _ _ => simp [check, hp, hq] at h
          | not _ => simp [check, hp, hq] at h
          | all _ _ => simp [check, hp, hq] at h
  | gen x p ih =>
      intro φ env h
      cases hp : check p with
      | none => simp [check, hp] at h
      | some ψ =>
        simp [check, hp] at h
        cases h
        rw [evalAlt_all]
        intro n
        exact ih ψ (fun y => if y = x then n else env y) hp
  | spec x t p ih =>
      intro φ env h
      cases hp : check p with
      | none => simp [check, hp] at h
      | some a =>
        cases a with
        | all y ψ =>
          simp [check, hp] at h
          rcases h with ⟨⟨rfl, ht⟩, rfl⟩
          have hall := (evalAlt_all env x ψ).1 (ih (Formula.all x ψ) env hp)
          exact (evalAlt_subst_closed env x t ht ψ).2 (hall (evalTermIn projStructure env t))
        | eq _ _ => simp [check, hp] at h
        | not _ => simp [check, hp] at h
        | imp _ _ => simp [check, hp] at h

/-- The true closed equation `S(S(0)+0) = S(S(0))`. -/
def congruenceWitness : Formula :=
  .eq (.succ (.add (.succ .zero) .zero)) (.succ (.succ .zero))

/-- **The base checker misses a true closed equation.** The interpretation validates every axiom
and rule of `T_0` and every induction instance, and falsifies `S(S(0)+0) = S(S(0))`, which is true
on `ℕ`; `T_0` does not prove it. -/
theorem base_checker_equation_gap :
    (∀ p φ (env : ℕ → ℕ), check p = some φ → evalAlt env φ) ∧
    (∀ (env : ℕ → ℕ) x φ, evalAlt env (inductionAxiom x φ)) ∧
    evalForm env0 congruenceWitness ∧ ¬ evalAlt env0 congruenceWitness ∧
    ¬ Provable congruenceWitness := by
  have hfalse : ¬ evalAlt env0 congruenceWitness := by
    rw [congruenceWitness, evalAlt_eq]
    simp
  refine ⟨check_sound_alt, evalAlt_inductionAxiom, rfl, hfalse, ?_⟩
  rintro ⟨p, hp⟩
  exact hfalse (check_sound_alt p _ env0 hp)

/-! ## The valuation for the repaired checker -/

/-- The valuation of the negation gap: terms, equations, implications and universal quantifiers
read in `ℕ`; `¬(s = t)` true only when `t` has value `0` and `s` a nonzero value; `¬∀x A` the
classical negation; every other negation false. -/
def evalNeg (env : ℕ → ℕ) : Formula → Prop
  | .eq s t => evalTerm env s = evalTerm env t
  | .not (.eq s t) => evalTerm env t = 0 ∧ evalTerm env s ≠ 0
  | .not (.not _) => False
  | .not (.imp _ _) => False
  | .not (.all x φ) => ¬ evalNeg env (.all x φ)
  | .imp φ ψ => evalNeg env φ → evalNeg env ψ
  | .all x φ => ∀ n : ℕ, evalNeg (envUpdate env x n) φ

theorem evalNeg_imp (env : ℕ → ℕ) (φ ψ : Formula) :
    evalNeg env (.imp φ ψ) ↔ (evalNeg env φ → evalNeg env ψ) := by
  simp only [evalNeg]

theorem evalNeg_all (env : ℕ → ℕ) (x : ℕ) (φ : Formula) :
    evalNeg env (.all x φ) ↔ ∀ n : ℕ, evalNeg (envUpdate env x n) φ := by
  simp only [evalNeg]

theorem evalNeg_subst_closed (x : ℕ) (u : Term) (hu : isClosedTerm u = true) :
    ∀ (φ : Formula) (env : ℕ → ℕ),
      evalNeg env (substForm x u φ) ↔ evalNeg (envUpdate env x (evalTerm env u)) φ
  | .eq s t, env => by simp only [substForm, evalNeg, evalTerm_subst]
  | .not (.eq s t), env => by simp only [substForm, evalNeg, evalTerm_subst]
  | .not (.not φ), env => by simp only [substForm, evalNeg]
  | .not (.imp φ ψ), env => by simp only [substForm, evalNeg]
  | .not (.all y φ), env => by
      have ih := evalNeg_subst_closed x u hu (.all y φ) env
      by_cases hyx : y = x
      · rw [show substForm x u (Formula.all y φ) = Formula.all y φ from if_pos hyx] at ih
        rw [show substForm x u (Formula.not (Formula.all y φ)) =
          Formula.not (Formula.all y φ) by simp [substForm, hyx]]
        simp only [evalNeg]
        exact not_congr ih
      · rw [show substForm x u (Formula.all y φ) = Formula.all y (substForm x u φ) from
          if_neg hyx] at ih
        rw [show substForm x u (Formula.not (Formula.all y φ)) =
          Formula.not (Formula.all y (substForm x u φ)) by simp [substForm, hyx]]
        simp only [evalNeg]
        exact not_congr ih
  | .imp φ ψ, env => by
      simp only [substForm, evalNeg]
      exact imp_congr (evalNeg_subst_closed x u hu φ env) (evalNeg_subst_closed x u hu ψ env)
  | .all y φ, env => by
      by_cases hyx : y = x
      · subst hyx
        rw [show substForm y u (Formula.all y φ) = Formula.all y φ from if_pos rfl]
        simp only [evalNeg]
        refine forall_congr' (fun n => ?_)
        rw [show envUpdate (envUpdate env y (evalTerm env u)) y n = envUpdate env y n from
          funext (fun z => envUpdate_same env y (evalTerm env u) n z)]
      · rw [show substForm x u (Formula.all y φ) = Formula.all y (substForm x u φ) from if_neg hyx]
        simp only [evalNeg]
        refine forall_congr' (fun n => ?_)
        rw [evalNeg_subst_closed x u hu φ (envUpdate env y n),
          isClosedTerm_eval_indep u hu (envUpdate env y n) env]
        rw [show envUpdate (envUpdate env y n) x (evalTerm env u) =
            envUpdate (envUpdate env x (evalTerm env u)) y n from
          funext (fun z => envUpdate_comm env hyx (evalTerm env u) n z)]

/-- Formulas built from equations, implications and universal quantifiers. -/
def noNeg : Formula → Bool
  | .eq _ _ => true
  | .not _ => false
  | .imp φ ψ => noNeg φ && noNeg ψ
  | .all _ φ => noNeg φ

theorem evalNeg_iff_evalForm : ∀ (φ : Formula), noNeg φ = true → ∀ env : ℕ → ℕ,
    (evalNeg env φ ↔ evalForm env φ)
  | .eq s t, _, env => Iff.rfl
  | .not _, h, _ => by simp [noNeg] at h
  | .imp φ ψ, h, env => by
      simp only [noNeg, Bool.and_eq_true] at h
      simp only [evalNeg, evalForm]
      exact imp_congr (evalNeg_iff_evalForm φ h.1 env) (evalNeg_iff_evalForm ψ h.2 env)
  | .all x φ, h, env => by
      simp only [noNeg] at h
      simp only [evalNeg, evalForm]
      exact forall_congr' (fun n => evalNeg_iff_evalForm φ h (envUpdate env x n))

theorem noNeg_of_isEqAxiom {φ : Formula} (h : isEqAxiom φ = true) : noNeg φ = true := by
  simp only [isEqAxiom, Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h) | h
  · unfold isEqSym at h
    split at h
    · rfl
    · exact absurd h Bool.false_ne_true
  · unfold isEqTrans at h
    split at h
    · rfl
    · exact absurd h Bool.false_ne_true
  · unfold isEqSucc at h
    split at h
    · rfl
    · exact absurd h Bool.false_ne_true
  · unfold isEqAdd at h
    split at h
    · rfl
    · exact absurd h Bool.false_ne_true
  · unfold isEqMul at h
    split at h
    · rfl
    · exact absurd h Bool.false_ne_true

theorem evalNeg_isQAxiom (env : ℕ → ℕ) {φ : Formula} (h : isQAxiom φ = true) :
    evalNeg env φ := by
  rcases (isQAxiom_iff φ).1 h with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
  · simp [q1, evalNeg, evalTerm]
  · simp only [q2, evalNeg, evalTerm]
    intro n m h
    omega
  · simp [q3, evalNeg, evalTerm]
  · simp only [q4, evalNeg, evalTerm]
    intro _ _
    omega
  · simp [q5, evalNeg, evalTerm]
  · simp only [q6, evalNeg, evalTerm]
    intro _ _
    exact Nat.mul_succ _ _
  · simp only [q7, orF, existsF, evalNeg, evalTerm]
    intro n _ hall
    exact absurd (hall 0).1 (by simp)

theorem evalNeg_isAxiomE (env : ℕ → ℕ) {φ : Formula} (h : isAxiomE φ = true) : evalNeg env φ := by
  simp only [isAxiomE, Bool.or_eq_true] at h
  rcases h with hax | hE
  · simp only [isAxiom, Bool.or_eq_true] at hax
    rcases hax with (((((hQ | hK) | hS) | hDNE) | hR) | hId)
    · exact evalNeg_isQAxiom env hQ
    · rcases isAxK_shape hK with ⟨a, b, rfl⟩
      simp only [evalNeg]
      intro ha _
      exact ha
    · rcases isAxS_shape hS with ⟨a, b, c, rfl⟩
      simp only [evalNeg]
      intro habc hab ha
      exact habc ha (hab ha)
    · rcases isAxDNE_shape hDNE with ⟨a, rfl⟩
      simp only [evalNeg]
      exact False.elim
    · cases φ with
      | eq s t =>
        have hst : s = t := by simpa [isEqRefl] using hR
        subst hst
        exact rfl
      | not _ => simp [isEqRefl] at hR
      | imp _ _ => simp [isEqRefl] at hR
      | all _ _ => simp [isEqRefl] at hR
    · cases φ with
      | imp a b =>
        have hab : a = b := by simpa [isAxId] using hId
        subst hab
        simp only [evalNeg]
        exact id
      | eq _ _ => simp [isAxId] at hId
      | not _ => simp [isAxId] at hId
      | all _ _ => simp [isAxId] at hId
  · exact (evalNeg_iff_evalForm φ (noNeg_of_isEqAxiom hE) env).2
      (eval_isAxiomE env (by simp [isAxiomE, hE]))

/-- **Soundness of the repaired checker for the valuation.** -/
theorem checkE_sound_neg :
    ∀ p : ProofTree, ∀ φ : Formula, ∀ env : ℕ → ℕ, checkE p = some φ → evalNeg env φ := by
  intro p
  induction p with
  | ax ψ =>
      intro φ env h
      simp [checkE] at h
      rcases h with ⟨hax, rfl⟩
      exact evalNeg_isAxiomE env hax
  | mp p q ihp ihq =>
      intro φ env h
      cases hp : checkE p with
      | none => simp [checkE, hp] at h
      | some a =>
        cases hq : checkE q with
        | none => simp [checkE, hp, hq] at h
        | some c =>
          cases a with
          | imp u v =>
              simp [checkE, hp, hq] at h
              rcases h with ⟨rfl, rfl⟩
              exact (evalNeg_imp env u v).1 (ihp (Formula.imp u v) env hp) (ihq u env hq)
          | eq _ _ => simp [checkE, hp, hq] at h
          | not _ => simp [checkE, hp, hq] at h
          | all _ _ => simp [checkE, hp, hq] at h
  | gen x p ih =>
      intro φ env h
      cases hp : checkE p with
      | none => simp [checkE, hp] at h
      | some ψ =>
        simp [checkE, hp] at h
        cases h
        rw [evalNeg_all]
        intro n
        exact ih ψ (envUpdate env x n) hp
  | spec x t p ih =>
      intro φ env h
      cases hp : checkE p with
      | none => simp [checkE, hp] at h
      | some a =>
        cases a with
        | all y ψ =>
          simp [checkE, hp] at h
          rcases h with ⟨⟨rfl, ht⟩, rfl⟩
          have hall := (evalNeg_all env x ψ).1 (ih (Formula.all x ψ) env hp)
          exact (evalNeg_subst_closed x t ht ψ env).2 (hall (evalTerm env t))
        | eq _ _ => simp [checkE, hp] at h
        | not _ => simp [checkE, hp] at h
        | imp _ _ => simp [checkE, hp] at h

/-- Every induction instance holds under the valuation: its conjunctive antecedent is the
negation of an implication, which the valuation reads as false. -/
theorem evalNeg_inductionAxiom (env : ℕ → ℕ) (x : ℕ) (φ : Formula) :
    evalNeg env (inductionAxiom x φ) := by
  simp only [inductionAxiom, andF, evalNeg]
  exact False.elim

/-- The true negated equation `¬(0 = S(0))`. -/
def negationWitness : Formula := .not (.eq .zero (.succ .zero))

/-- **The repaired checker misses a true negated equation.** The valuation validates every axiom
and rule of `T_E` and every induction instance, and falsifies `¬(0 = S(0))`, which is true on `ℕ`;
`T_E` does not prove it. -/
theorem repaired_checker_negation_gap :
    (∀ p φ (env : ℕ → ℕ), checkE p = some φ → evalNeg env φ) ∧
    (∀ (env : ℕ → ℕ) x φ, evalNeg env (inductionAxiom x φ)) ∧
    evalForm env0 negationWitness ∧ ¬ evalNeg env0 negationWitness ∧
    ¬ ProvableE negationWitness := by
  have hfalse : ¬ evalNeg env0 negationWitness := by
    simp [negationWitness, evalNeg, evalTerm]
  refine ⟨checkE_sound_neg, evalNeg_inductionAxiom, ?_, hfalse, ?_⟩
  · simp [negationWitness, evalForm, evalTerm]
  · rintro ⟨p, hp⟩
    exact hfalse (checkE_sound_neg p _ env0 hp)

end OperatorKO7.Meta.BoundaryObserver.CheckerGaps
