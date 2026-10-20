import OperatorKO7.Meta.DistinctionBoundary.GodelArithmetization

/-!
# Equality repair of the arithmetic checker

Manuscript: Theorem `thm:godel-equality-repair` of the Observation-Boundary Principle.

The checker `T_0` (`GodelArith.check`) has the seven Robinson axioms, equality reflexivity, the schemes
`K`, `S`, identity and double-negation elimination, and the rules of modus ponens, generalization and
closed specialization. The checker `T_E` adds five equality schemes for arbitrary terms:

* `s = t → t = s`;
* `s = t → (t = u → s = u)`;
* `s = t → S(s) = S(t)`;
* `s = s' → (t = t' → s + t = s' + t')`;
* `s = s' → (t = t' → s · t = s' · t')`.

This module proves that every `T_0` proof is a `T_E` proof, that `T_E` is sound on `ℕ`, and that for
closed terms `T_E ⊢ s = t` holds exactly when `s` and `t` have the same value: every closed term is
provably equal to the numeral of its value, through the numeral identities `m + n = m+n` and
`m · n = mn` derived from the Robinson axioms by congruence, transitivity and induction on `n`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.EqualityRepair

open OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-! ## The five equality schemes and the repaired checker -/

/-- The symmetry scheme `s = t → t = s`. -/
def isEqSym : Formula → Bool
  | Formula.imp (Formula.eq s t) (Formula.eq t' s') => decide (s = s' ∧ t = t')
  | _ => false

/-- The transitivity scheme `s = t → (t = u → s = u)`. -/
def isEqTrans : Formula → Bool
  | Formula.imp (Formula.eq s t) (Formula.imp (Formula.eq t' u) (Formula.eq s' u')) =>
      decide (t = t' ∧ s = s' ∧ u = u')
  | _ => false

/-- The successor congruence scheme `s = t → S(s) = S(t)`. -/
def isEqSucc : Formula → Bool
  | Formula.imp (Formula.eq s t) (Formula.eq (Term.succ s') (Term.succ t')) =>
      decide (s = s' ∧ t = t')
  | _ => false

/-- The addition congruence scheme `s = s' → (t = t' → s + t = s' + t')`. -/
def isEqAdd : Formula → Bool
  | Formula.imp (Formula.eq s s') (Formula.imp (Formula.eq t t')
      (Formula.eq (Term.add a b) (Term.add a' b'))) =>
      decide (a = s ∧ a' = s' ∧ b = t ∧ b' = t')
  | _ => false

/-- The multiplication congruence scheme `s = s' → (t = t' → s · t = s' · t')`. -/
def isEqMul : Formula → Bool
  | Formula.imp (Formula.eq s s') (Formula.imp (Formula.eq t t')
      (Formula.eq (Term.mul a b) (Term.mul a' b'))) =>
      decide (a = s ∧ a' = s' ∧ b = t ∧ b' = t')
  | _ => false

/-- The five equality schemes. -/
def isEqAxiom (φ : Formula) : Bool :=
  isEqSym φ || isEqTrans φ || isEqSucc φ || isEqAdd φ || isEqMul φ

/-- The axioms of `T_E`: the axioms of `T_0` and the five equality schemes. -/
def isAxiomE (φ : Formula) : Bool := isAxiom φ || isEqAxiom φ

/-- The repaired checker `T_E` on the proof trees of `T_0`. -/
def checkE : ProofTree → Option Formula
  | .ax φ => if isAxiomE φ then some φ else none
  | .mp p q =>
      match checkE p, checkE q with
      | some (Formula.imp a b), some c => if a = c then some b else none
      | _, _ => none
  | .gen x p =>
      match checkE p with
      | some φ => some (Formula.all x φ)
      | none => none
  | .spec x t p =>
      match checkE p with
      | some (Formula.all y φ) =>
          if decide (x = y) && isClosedTerm t then some (substForm x t φ) else none
      | _ => none

/-- Provability in `T_E`. -/
def ProvableE (φ : Formula) : Prop := ∃ p : ProofTree, checkE p = some φ

theorem isAxiomE_of_isAxiom {φ : Formula} (h : isAxiom φ = true) : isAxiomE φ = true := by
  simp [isAxiomE, h]

/-- Every `T_0` proof is a `T_E` proof with the same conclusion. -/
theorem check_to_checkE :
    ∀ p : ProofTree, ∀ φ : Formula, check p = some φ → checkE p = some φ
  | .ax ψ, φ, h => by
      simp [check] at h
      rcases h with ⟨hax, rfl⟩
      simp [checkE, isAxiomE_of_isAxiom hax]
  | .mp p q, φ, h => by
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
              have hpE := check_to_checkE p (Formula.imp u v) hp
              have hqE := check_to_checkE q u hq
              simp [checkE, hpE, hqE]
          | eq _ _ => simp [check, hp, hq] at h
          | not _ => simp [check, hp, hq] at h
          | all _ _ => simp [check, hp, hq] at h
  | .gen x p, φ, h => by
      cases hp : check p with
      | none => simp [check, hp] at h
      | some ψ =>
          simp [check, hp] at h
          cases h
          have hpE := check_to_checkE p ψ hp
          simp [checkE, hpE]
  | .spec x t p, φ, h => by
      cases hp : check p with
      | none => simp [check, hp] at h
      | some a =>
        cases a with
        | all y ψ =>
          simp [check, hp] at h
          rcases h with ⟨⟨rfl, ht⟩, rfl⟩
          have hpE := check_to_checkE p (Formula.all x ψ) hp
          simp [checkE, hpE, ht]
        | eq _ _ => simp [check, hp] at h
        | not _ => simp [check, hp] at h
        | imp _ _ => simp [check, hp] at h

/-- `T_E` extends `T_0`. -/
theorem provable_to_provableE {φ : Formula} : Provable φ → ProvableE φ := by
  rintro ⟨p, hp⟩
  exact ⟨p, check_to_checkE p φ hp⟩

/-! ## Soundness on `ℕ` -/

theorem eval_isEqSym (env : Nat → Nat) {φ : Formula} (h : isEqSym φ = true) : evalForm env φ := by
  unfold isEqSym at h
  split at h
  · simp only [decide_eq_true_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [evalForm]
    exact fun h1 => h1.symm
  · exact absurd h Bool.false_ne_true

theorem eval_isEqTrans (env : Nat → Nat) {φ : Formula} (h : isEqTrans φ = true) :
    evalForm env φ := by
  unfold isEqTrans at h
  split at h
  · simp only [decide_eq_true_eq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [evalForm]
    exact fun h1 h2 => h1.trans h2
  · exact absurd h Bool.false_ne_true

theorem eval_isEqSucc (env : Nat → Nat) {φ : Formula} (h : isEqSucc φ = true) :
    evalForm env φ := by
  unfold isEqSucc at h
  split at h
  · simp only [decide_eq_true_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [evalForm, evalTerm]
    exact fun h1 => by rw [h1]
  · exact absurd h Bool.false_ne_true

theorem eval_isEqAdd (env : Nat → Nat) {φ : Formula} (h : isEqAdd φ = true) :
    evalForm env φ := by
  unfold isEqAdd at h
  split at h
  · simp only [decide_eq_true_eq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp only [evalForm, evalTerm]
    exact fun h1 h2 => by rw [h1, h2]
  · exact absurd h Bool.false_ne_true

theorem eval_isEqMul (env : Nat → Nat) {φ : Formula} (h : isEqMul φ = true) :
    evalForm env φ := by
  unfold isEqMul at h
  split at h
  · simp only [decide_eq_true_eq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp only [evalForm, evalTerm]
    exact fun h1 h2 => by rw [h1, h2]
  · exact absurd h Bool.false_ne_true

/-- Every axiom of `T_E` is true on `ℕ` under every environment. -/
theorem eval_isAxiomE (env : Nat → Nat) {φ : Formula} (h : isAxiomE φ = true) :
    evalForm env φ := by
  simp only [isAxiomE, isEqAxiom, Bool.or_eq_true] at h
  rcases h with h | (((h | h) | h) | h) | h
  · exact eval_isAxiom env h
  · exact eval_isEqSym env h
  · exact eval_isEqTrans env h
  · exact eval_isEqSucc env h
  · exact eval_isEqAdd env h
  · exact eval_isEqMul env h

/-- **Soundness of `T_E` on `ℕ`.** -/
theorem checkE_sound :
    ∀ p : ProofTree, ∀ φ : Formula, ∀ env : Nat → Nat,
      checkE p = some φ → evalForm env φ := by
  intro p
  induction p with
  | ax ψ =>
      intro φ env h
      simp [checkE] at h
      rcases h with ⟨hax, rfl⟩
      exact eval_isAxiomE env hax
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
              exact (ihp (Formula.imp u v) env hp) (ihq u env hq)
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
          have hall := ih (Formula.all x ψ) env hp
          have hinst := hall (evalTerm env t)
          exact (evalForm_subst_closed env x t ht ψ).2 hinst
        | eq _ _ => simp [checkE, hp] at h
        | not _ => simp [checkE, hp] at h
        | imp _ _ => simp [checkE, hp] at h

theorem provableE_sound {φ : Formula} (h : ProvableE φ) (env : Nat → Nat) : evalForm env φ := by
  rcases h with ⟨p, hp⟩
  exact checkE_sound p φ env hp

/-- `T_E` is consistent. -/
theorem provableE_consistent : ¬ ProvableE falsum := fun h =>
  evalForm_falsum env0 (provableE_sound h env0)

/-! ## Derived rules of `T_E` -/

theorem pE_ax {φ : Formula} (h : isAxiomE φ = true) : ProvableE φ :=
  ⟨.ax φ, by simp [checkE, h]⟩

theorem pE_mp {a b : Formula} (h1 : ProvableE (Formula.imp a b)) (h2 : ProvableE a) :
    ProvableE b := by
  obtain ⟨p, hp⟩ := h1
  obtain ⟨q, hq⟩ := h2
  exact ⟨.mp p q, by simp [checkE, hp, hq]⟩

theorem pE_spec {x : Nat} {t : Term} {φ : Formula} (h : ProvableE (Formula.all x φ))
    (ht : isClosedTerm t = true) : ProvableE (substForm x t φ) := by
  obtain ⟨p, hp⟩ := h
  exact ⟨.spec x t p, by simp [checkE, hp, ht]⟩

theorem pE_refl (t : Term) : ProvableE (Formula.eq t t) :=
  pE_ax (isAxiomE_of_isAxiom (eq_refl_axiom t))

theorem pE_symm {s t : Term} (h : ProvableE (Formula.eq s t)) : ProvableE (Formula.eq t s) :=
  pE_mp (pE_ax (φ := Formula.imp (Formula.eq s t) (Formula.eq t s))
    (by simp [isAxiomE, isEqAxiom, isEqSym])) h

theorem pE_trans {s t u : Term} (h1 : ProvableE (Formula.eq s t))
    (h2 : ProvableE (Formula.eq t u)) : ProvableE (Formula.eq s u) :=
  pE_mp (pE_mp (pE_ax (φ := Formula.imp (Formula.eq s t)
    (Formula.imp (Formula.eq t u) (Formula.eq s u)))
    (by simp [isAxiomE, isEqAxiom, isEqTrans])) h1) h2

theorem pE_succ {s t : Term} (h : ProvableE (Formula.eq s t)) :
    ProvableE (Formula.eq (Term.succ s) (Term.succ t)) :=
  pE_mp (pE_ax (φ := Formula.imp (Formula.eq s t) (Formula.eq (Term.succ s) (Term.succ t)))
    (by simp [isAxiomE, isEqAxiom, isEqSucc])) h

theorem pE_add {s s' t t' : Term} (h1 : ProvableE (Formula.eq s s'))
    (h2 : ProvableE (Formula.eq t t')) :
    ProvableE (Formula.eq (Term.add s t) (Term.add s' t')) :=
  pE_mp (pE_mp (pE_ax (φ := Formula.imp (Formula.eq s s') (Formula.imp (Formula.eq t t')
    (Formula.eq (Term.add s t) (Term.add s' t'))))
    (by simp [isAxiomE, isEqAxiom, isEqAdd])) h1) h2

theorem pE_mul {s s' t t' : Term} (h1 : ProvableE (Formula.eq s s'))
    (h2 : ProvableE (Formula.eq t t')) :
    ProvableE (Formula.eq (Term.mul s t) (Term.mul s' t')) :=
  pE_mp (pE_mp (pE_ax (φ := Formula.imp (Formula.eq s s') (Formula.imp (Formula.eq t t')
    (Formula.eq (Term.mul s t) (Term.mul s' t'))))
    (by simp [isAxiomE, isEqAxiom, isEqMul])) h1) h2

/-! ## Numeral arithmetic in `T_E` -/

theorem substTerm_numeral (x : Nat) (u : Term) :
    ∀ m : Nat, substTerm x u (numeral m) = numeral m
  | 0 => rfl
  | m + 1 => by
      show Term.succ (substTerm x u (numeral m)) = Term.succ (numeral m)
      rw [substTerm_numeral x u m]

theorem hq3 : isAxiomE q3 = true := isAxiomE_of_isAxiom (by simp [isAxiom, isQAxiom])
theorem hq4 : isAxiomE q4 = true := isAxiomE_of_isAxiom (by simp [isAxiom, isQAxiom])
theorem hq5 : isAxiomE q5 = true := isAxiomE_of_isAxiom (by simp [isAxiom, isQAxiom])
theorem hq6 : isAxiomE q6 = true := isAxiomE_of_isAxiom (by simp [isAxiom, isQAxiom])

theorem pE_q3 (m : Nat) : ProvableE (Formula.eq (Term.add (numeral m) Term.zero) (numeral m)) := by
  have h := pE_spec (pE_ax hq3) (isClosedTerm_numeral m)
  simpa [substForm, substTerm] using h

theorem pE_q4 (m n : Nat) :
    ProvableE (Formula.eq (Term.add (numeral m) (Term.succ (numeral n)))
      (Term.succ (Term.add (numeral m) (numeral n)))) := by
  have h1 := pE_spec (pE_ax hq4) (isClosedTerm_numeral m)
  simp [substForm, substTerm] at h1
  have h2 := pE_spec h1 (isClosedTerm_numeral n)
  simpa [substForm, substTerm, substTerm_numeral] using h2

theorem pE_q5 (m : Nat) : ProvableE (Formula.eq (Term.mul (numeral m) Term.zero) Term.zero) := by
  have h := pE_spec (pE_ax hq5) (isClosedTerm_numeral m)
  simpa [substForm, substTerm] using h

theorem pE_q6 (m n : Nat) :
    ProvableE (Formula.eq (Term.mul (numeral m) (Term.succ (numeral n)))
      (Term.add (Term.mul (numeral m) (numeral n)) (numeral m))) := by
  have h1 := pE_spec (pE_ax hq6) (isClosedTerm_numeral m)
  simp [substForm, substTerm] at h1
  have h2 := pE_spec h1 (isClosedTerm_numeral n)
  simpa [substForm, substTerm, substTerm_numeral] using h2

/-- `T_E ⊢ m + n = m+n` for numerals. -/
theorem pE_numAdd (m : Nat) :
    ∀ n : Nat, ProvableE (Formula.eq (Term.add (numeral m) (numeral n)) (numeral (m + n)))
  | 0 => pE_q3 m
  | n + 1 => pE_trans (pE_q4 m n) (pE_succ (pE_numAdd m n))

/-- `T_E ⊢ m · n = mn` for numerals. -/
theorem pE_numMul (m : Nat) :
    ∀ n : Nat, ProvableE (Formula.eq (Term.mul (numeral m) (numeral n)) (numeral (m * n)))
  | 0 => pE_q5 m
  | n + 1 => pE_trans (pE_trans (pE_q6 m n) (pE_add (pE_numMul m n) (pE_refl (numeral m))))
      (pE_numAdd (m * n) m)

/-- Every closed term is `T_E`-provably equal to the numeral of its value. -/
theorem pE_closed_numeral : ∀ t : Term, isClosedTerm t = true →
    ProvableE (Formula.eq t (numeral (evalTerm env0 t)))
  | Term.zero, _ => pE_refl Term.zero
  | Term.succ t, h => pE_succ (pE_closed_numeral t h)
  | Term.add s t, h => by
      simp only [isClosedTerm, Bool.and_eq_true] at h
      exact pE_trans (pE_add (pE_closed_numeral s h.1) (pE_closed_numeral t h.2)) (pE_numAdd _ _)
  | Term.mul s t, h => by
      simp only [isClosedTerm, Bool.and_eq_true] at h
      exact pE_trans (pE_mul (pE_closed_numeral s h.1) (pE_closed_numeral t h.2)) (pE_numMul _ _)
  | Term.var _, h => by simp [isClosedTerm] at h

/-- Closed terms with equal values are `T_E`-provably equal. -/
theorem closed_eq_complete {s t : Term} (hs : isClosedTerm s = true) (ht : isClosedTerm t = true)
    (h : evalTerm env0 s = evalTerm env0 t) : ProvableE (Formula.eq s t) := by
  have h1 := pE_closed_numeral s hs
  have h2 := pE_closed_numeral t ht
  rw [h] at h1
  exact pE_trans h1 (pE_symm h2)

/-- **Closed equations of `T_E`.** For closed terms, `T_E ⊢ s = t` if and only if `s` and `t` have
the same value in `ℕ`. -/
theorem closed_eq_iff {s t : Term} (hs : isClosedTerm s = true) (ht : isClosedTerm t = true) :
    ProvableE (Formula.eq s t) ↔ evalTerm env0 s = evalTerm env0 t :=
  ⟨fun h => provableE_sound h env0, closed_eq_complete hs ht⟩

/-- The true equation `S(S(0) + 0) = S(S(0))`, unprovable in `T_0`, is a theorem of `T_E`. -/
theorem repaired_example :
    ProvableE (Formula.eq (Term.succ (Term.add (Term.succ Term.zero) Term.zero))
      (Term.succ (Term.succ Term.zero))) :=
  closed_eq_complete rfl rfl rfl

end OperatorKO7.Meta.BoundaryObserver.EqualityRepair
