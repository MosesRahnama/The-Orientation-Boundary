import OperatorKO7.Meta.DistinctionBoundary.GodelInductionChecker

set_option autoImplicit false

/-!
# Sigma-one route audit for the induction-strengthened checker

The roadmap predicted external Sigma-one completeness after adjoining the full
induction schema. That prediction is false for the live checker because its
logical equality interface contains reflexivity but no equality substitution or
congruence rule.

We prove the failure by a second sound interpretation of the entire extended
checker. Variables still range over `Nat`, so every induction instance is
valid. The weak arithmetic interprets addition as second projection,
multiplication as zero, and object-language equality by

  weakEq a b := a = b or a = 0.

All seven Q axioms, every logical axiom, MP, generalization, closed
specialization, and every induction instance remain valid. Yet the closed
quantifier-free standard truth

  S(S(0) + 0) = S(S(0))

is false in the weak interpretation. Hence it is not `ProvableI`. Since every
bounded formula is in the declared Sigma-one class, the universal external
Sigma-one completeness theorem required by the HBL route is refuted.

This is a checker-interface no-go, not a no-go for arithmetic with a standard
equality calculus.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- Weak arithmetic term interpretation used to audit the equality interface. -/
def weakEvalTerm (env : Nat → Nat) : Term → Nat
  | .zero => 0
  | .succ t => weakEvalTerm env t + 1
  | .add _s t => weakEvalTerm env t
  | .mul _s _t => 0
  | .var x => env x

/-- Nontransitive licensed equality. Every zero-left equation is accepted. -/
def weakEq (a b : Nat) : Prop := a = b ∨ a = 0

/-- Formula semantics over the weak arithmetic interpretation. -/
def weakEvalForm (env : Nat → Nat) : Formula → Prop
  | .eq s t => weakEq (weakEvalTerm env s) (weakEvalTerm env t)
  | .not φ => ¬ weakEvalForm env φ
  | .imp φ ψ => weakEvalForm env φ → weakEvalForm env ψ
  | .all x φ => ∀ n : Nat, weakEvalForm (envUpdate env x n) φ

/-- Encoded existential has ordinary existential semantics. -/
theorem weakEval_existsF (env : Nat → Nat) (x : Nat) (φ : Formula) :
    weakEvalForm env (existsF x φ) ↔
      ∃ n : Nat, weakEvalForm (envUpdate env x n) φ := by
  classical
  simp [existsF, weakEvalForm]

/-- Encoded conjunction has ordinary conjunction semantics. -/
theorem weakEval_andF (env : Nat → Nat) (φ ψ : Formula) :
    weakEvalForm env (andF φ ψ) ↔
      weakEvalForm env φ ∧ weakEvalForm env ψ := by
  classical
  simp [andF, weakEvalForm]

/-- Encoded disjunction has ordinary disjunction semantics. -/
theorem weakEval_orF (env : Nat → Nat) (φ ψ : Formula) :
    weakEvalForm env (orF φ ψ) ↔
      weakEvalForm env φ ∨ weakEvalForm env ψ := by
  unfold orF
  change (¬ weakEvalForm env φ → weakEvalForm env ψ) ↔
    weakEvalForm env φ ∨ weakEvalForm env ψ
  constructor
  · intro h
    by_cases hp : weakEvalForm env φ
    · exact Or.inl hp
    · exact Or.inr (h hp)
  · rintro (hp | hq) hn
    · exact False.elim (hn hp)
    · exact hq

/-- Weak term semantics respects arbitrary term substitution. -/
theorem weakEvalTerm_subst (env : Nat → Nat) (x : Nat) (u : Term) (t : Term) :
    weakEvalTerm env (substTerm x u t) =
      weakEvalTerm (envUpdate env x (weakEvalTerm env u)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change weakEvalTerm env (substTerm x u t) + 1 =
        weakEvalTerm (envUpdate env x (weakEvalTerm env u)) t + 1
      exact congrArg (fun n => n + 1) ih
  | add s t ihs iht =>
      change weakEvalTerm env (substTerm x u t) =
        weakEvalTerm (envUpdate env x (weakEvalTerm env u)) t
      exact iht
  | mul s t ihs iht => rfl
  | var y =>
      by_cases hy : y = x
      · subst y
        simp [substTerm, weakEvalTerm, envUpdate]
      · simp [substTerm, weakEvalTerm, envUpdate, hy]

/-- Closed terms have environment-independent weak denotation. -/
theorem isClosedTerm_weakEvalTerm_indep (t : Term)
    (ht : isClosedTerm t = true) :
    ∀ env env' : Nat → Nat, weakEvalTerm env t = weakEvalTerm env' t := by
  induction t with
  | zero => intro env env'; rfl
  | succ t ih =>
      intro env env'
      simp [isClosedTerm] at ht
      exact congrArg (fun n => n + 1) (ih ht env env')
  | add s t ihs iht =>
      intro env env'
      simp [isClosedTerm, Bool.and_eq_true] at ht
      exact iht ht.2 env env'
  | mul s t ihs iht => intro env env'; rfl
  | var x => simp [isClosedTerm] at ht

/-- Pointwise equal environments satisfy the same weak formulas. -/
theorem weakEvalForm_env_eq (φ : Formula) :
    ∀ {env env' : Nat → Nat}, (∀ z, env z = env' z) →
      (weakEvalForm env φ ↔ weakEvalForm env' φ) := by
  induction φ with
  | eq s t =>
      intro env env' henv
      have hs : weakEvalTerm env s = weakEvalTerm env' s := by
        induction s with
        | zero => rfl
        | succ s ih => exact congrArg (fun n => n + 1) ih
        | add a b iha ihb => exact ihb
        | mul a b iha ihb => rfl
        | var z => exact henv z
      have ht : weakEvalTerm env t = weakEvalTerm env' t := by
        induction t with
        | zero => rfl
        | succ t ih => exact congrArg (fun n => n + 1) ih
        | add a b iha ihb => exact ihb
        | mul a b iha ihb => rfl
        | var z => exact henv z
      simp [weakEvalForm, hs, ht]
  | not φ ih =>
      intro env env' henv
      simp [weakEvalForm, ih henv]
  | imp φ ψ ihφ ihψ =>
      intro env env' henv
      simp [weakEvalForm, ihφ henv, ihψ henv]
  | all y φ ih =>
      intro env env' henv
      simp only [weakEvalForm]
      constructor
      · intro h n
        have hi := ih (env := envUpdate env y n)
          (env' := envUpdate env' y n) (by
            intro z
            by_cases hz : z = y <;> simp [envUpdate, hz, henv z])
        exact hi.1 (h n)
      · intro h n
        have hi := ih (env := envUpdate env y n)
          (env' := envUpdate env' y n) (by
            intro z
            by_cases hz : z = y <;> simp [envUpdate, hz, henv z])
        exact hi.2 (h n)

/-- Closed substitution has the expected weak semantics. -/
theorem weakEvalForm_subst_closed (env : Nat → Nat) (x : Nat) (u : Term)
    (hu : isClosedTerm u = true) :
    ∀ φ : Formula,
      weakEvalForm env (substForm x u φ) ↔
        weakEvalForm (envUpdate env x (weakEvalTerm env u)) φ := by
  intro φ
  induction φ generalizing env with
  | eq s t =>
      simp [substForm, weakEvalForm, weakEvalTerm_subst]
  | not φ ih =>
      simp [substForm, weakEvalForm, ih]
  | imp φ ψ ihφ ihψ =>
      simp [substForm, weakEvalForm, ihφ, ihψ]
  | all y φ ih =>
      by_cases hyx : y = x
      · subst y
        simp only [substForm, if_pos, weakEvalForm]
        constructor
        · intro h n
          have henv : ∀ z,
              envUpdate (envUpdate env x (weakEvalTerm env u)) x n z =
                envUpdate env x n z := by
            intro z
            exact envUpdate_same env x (weakEvalTerm env u) n z
          exact (weakEvalForm_env_eq φ henv).2 (h n)
        · intro h n
          have henv : ∀ z,
              envUpdate env x n z =
                envUpdate (envUpdate env x (weakEvalTerm env u)) x n z := by
            intro z
            exact (envUpdate_same env x (weakEvalTerm env u) n z).symm
          exact (weakEvalForm_env_eq φ henv).2 (h n)
      · simp only [substForm, if_neg hyx, weakEvalForm]
        constructor
        · intro h n
          have hsub := (ih (env := envUpdate env y n)).1 (h n)
          have hu' : weakEvalTerm (envUpdate env y n) u = weakEvalTerm env u :=
            isClosedTerm_weakEvalTerm_indep u hu _ _
          have henv : ∀ z,
              envUpdate (envUpdate env y n) x
                  (weakEvalTerm (envUpdate env y n) u) z =
                envUpdate (envUpdate env x (weakEvalTerm env u)) y n z := by
            intro z
            rw [hu']
            exact envUpdate_comm env hyx (weakEvalTerm env u) n z
          exact (weakEvalForm_env_eq φ henv).1 hsub
        · intro h n
          have hu' : weakEvalTerm (envUpdate env y n) u = weakEvalTerm env u :=
            isClosedTerm_weakEvalTerm_indep u hu _ _
          have henv : ∀ z,
              envUpdate (envUpdate env x (weakEvalTerm env u)) y n z =
                envUpdate (envUpdate env y n) x
                  (weakEvalTerm (envUpdate env y n) u) z := by
            intro z
            rw [hu']
            exact (envUpdate_comm env hyx (weakEvalTerm env u) n z).symm
          have htarget := (weakEvalForm_env_eq φ henv).1 (h n)
          exact (ih (env := envUpdate env y n)).2 htarget

/-- Weak semantics of the self-successor substitution. -/
theorem weakEvalForm_subst_selfSucc (env : Nat → Nat) (x : Nat) :
    ∀ φ : Formula,
      weakEvalForm env (substForm x (inductionStepTerm x) φ) ↔
        weakEvalForm (envUpdate env x (env x + 1)) φ := by
  intro φ
  induction φ generalizing env with
  | eq s t =>
      rw [show substForm x (inductionStepTerm x) (Formula.eq s t) =
        Formula.eq (substTerm x (inductionStepTerm x) s)
          (substTerm x (inductionStepTerm x) t) by rfl]
      simp only [weakEvalForm]
      rw [weakEvalTerm_subst, weakEvalTerm_subst]
      rfl
  | not φ ih =>
      simp [substForm, weakEvalForm, ih]
  | imp φ ψ ihφ ihψ =>
      simp [substForm, weakEvalForm, ihφ, ihψ]
  | all y φ ih =>
      by_cases hyx : y = x
      · subst y
        simp only [substForm, if_pos, weakEvalForm]
        constructor
        · intro h n
          have henv : ∀ z,
              envUpdate (envUpdate env x (env x + 1)) x n z =
                envUpdate env x n z := by
            intro z
            exact envUpdate_same env x (env x + 1) n z
          exact (weakEvalForm_env_eq φ henv).2 (h n)
        · intro h n
          have henv : ∀ z,
              envUpdate env x n z =
                envUpdate (envUpdate env x (env x + 1)) x n z := by
            intro z
            exact (envUpdate_same env x (env x + 1) n z).symm
          exact (weakEvalForm_env_eq φ henv).2 (h n)
      · simp only [substForm, if_neg hyx, weakEvalForm]
        constructor
        · intro h n
          have hsub := (ih (env := envUpdate env y n)).1 (h n)
          have hxy : x ≠ y := Ne.symm hyx
          have hxval : envUpdate env y n x = env x := by simp [envUpdate, hxy]
          have henv : ∀ z,
              envUpdate (envUpdate env y n) x (envUpdate env y n x + 1) z =
                envUpdate (envUpdate env x (env x + 1)) y n z := by
            intro z
            rw [hxval]
            exact (envUpdate_selfSucc_comm env hyx n z).symm
          exact (weakEvalForm_env_eq φ henv).1 hsub
        · intro h n
          have hxy : x ≠ y := Ne.symm hyx
          have hxval : envUpdate env y n x = env x := by simp [envUpdate, hxy]
          have henv : ∀ z,
              envUpdate (envUpdate env x (env x + 1)) y n z =
                envUpdate (envUpdate env y n) x (envUpdate env y n x + 1) z := by
            intro z
            rw [hxval]
            exact envUpdate_selfSucc_comm env hyx n z
          have htarget := (weakEvalForm_env_eq φ henv).1 (h n)
          exact (ih (env := envUpdate env y n)).2 htarget

/-- Q1 in the weak interpretation. -/
theorem weak_q1 (env : Nat → Nat) : weakEvalForm env q1 := by
  intro a
  change ¬ weakEq (a + 1) 0
  simp [weakEq]

/-- Q2 in the weak interpretation. -/
theorem weak_q2 (env : Nat → Nat) : weakEvalForm env q2 := by
  intro a b
  change weakEq (a + 1) (b + 1) → weakEq a b
  intro h
  rcases h with hEq | hZero
  · left
    omega
  · omega

/-- Q3 in the weak interpretation. -/
theorem weak_q3 (env : Nat → Nat) : weakEvalForm env q3 := by
  intro a
  change weakEq 0 a
  exact Or.inr rfl

/-- Q4 in the weak interpretation. -/
theorem weak_q4 (env : Nat → Nat) : weakEvalForm env q4 := by
  intro a b
  change weakEq (b + 1) (b + 1)
  exact Or.inl rfl

/-- Q5 in the weak interpretation. -/
theorem weak_q5 (env : Nat → Nat) : weakEvalForm env q5 := by
  intro a
  change weakEq 0 0
  exact Or.inl rfl

/-- Q6 in the weak interpretation. -/
theorem weak_q6 (env : Nat → Nat) : weakEvalForm env q6 := by
  intro a b
  change weakEq 0 a
  exact Or.inr rfl

/-- Q7 in the weak interpretation. -/
theorem weak_q7 (env : Nat → Nat) : weakEvalForm env q7 := by
  intro a
  rw [weakEval_orF]
  cases a with
  | zero =>
      left
      change weakEq 0 0
      exact Or.inl rfl
  | succ n =>
      right
      rw [weakEval_existsF]
      refine ⟨n, ?_⟩
      change weakEq (n + 1) (n + 1)
      exact Or.inl rfl

/-- Every one of the seven Q axioms is valid in the weak interpretation. -/
theorem weakEval_isQAxiom (env : Nat → Nat) {φ : Formula}
    (h : isQAxiom φ = true) : weakEvalForm env φ := by
  have hmem := (isQAxiom_iff_mem φ).1 h
  simp [qAxioms] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact weak_q1 env
  · exact weak_q2 env
  · exact weak_q3 env
  · exact weak_q4 env
  · exact weak_q5 env
  · exact weak_q6 env
  · exact weak_q7 env

/-- Every original logical/equality axiom is valid in the weak interpretation. -/
theorem weakEval_isAxiom (env : Nat → Nat) {φ : Formula}
    (hax : isAxiom φ = true) : weakEvalForm env φ := by
  simp [isAxiom, Bool.or_eq_true] at hax
  rcases hax with (((((hQ | hK) | hS) | hDNE) | hR) | hId)
  · exact weakEval_isQAxiom env hQ
  · rcases isAxK_shape hK with ⟨a, b, rfl⟩
    intro ha _hb
    exact ha
  · rcases isAxS_shape hS with ⟨a, b, c, rfl⟩
    intro habc hab ha
    exact habc ha (hab ha)
  · rcases isAxDNE_shape hDNE with ⟨a, rfl⟩
    intro hnn
    exact Classical.not_not.mp hnn
  · cases φ with
    | eq s t =>
      have hst : s = t := by simpa [isEqRefl] using hR
      subst hst
      exact Or.inl rfl
    | not _ => simp [isEqRefl] at hR
    | imp _ _ => simp [isEqRefl] at hR
    | all _ _ => simp [isEqRefl] at hR
  · cases φ with
    | imp a b =>
      have hab : a = b := by simpa [isAxId] using hId
      subst hab
      intro ha
      exact ha
    | eq _ _ => simp [isAxId] at hId
    | not _ => simp [isAxId] at hId
    | all _ _ => simp [isAxId] at hId

/-- Every induction-schema instance remains valid in the weak interpretation
because variables still range over the standard natural-number successor
chain. -/
theorem weakEval_inductionAxiom (env : Nat → Nat) (x : Nat) (φ : Formula) :
    weakEvalForm env (inductionAxiom x φ) := by
  intro hante
  have hpair := (weakEval_andF env
    (substForm x Term.zero φ)
    (Formula.all x
      (Formula.imp φ (substForm x (inductionStepTerm x) φ)))).1 hante
  have hbaseSub := hpair.1
  have hstep := hpair.2
  have hbase : weakEvalForm (envUpdate env x 0) φ := by
    have hsubst := weakEvalForm_subst_closed env x Term.zero (by rfl) φ
    simpa [weakEvalTerm] using hsubst.1 hbaseSub
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
      have hstepN := hstep n
      have hnextSub : weakEvalForm (envUpdate env x n)
          (substForm x (inductionStepTerm x) φ) := hstepN ih
      have hsem := (weakEvalForm_subst_selfSucc (envUpdate env x n) x φ).1 hnextSub
      have henv : ∀ z,
          envUpdate (envUpdate env x n) x (envUpdate env x n x + 1) z =
            envUpdate env x (n + 1) z := by
        intro z
        by_cases hz : z = x <;> simp [envUpdate, hz]
      exact (weakEvalForm_env_eq φ henv).1 hsem

/-- Every extended axiom is weak-valid. -/
theorem weakEval_isAxiomI (env : Nat → Nat) {φ : Formula}
    (hax : isAxiomI φ = true) : weakEvalForm env φ := by
  simp [isAxiomI, Bool.or_eq_true] at hax
  rcases hax with hOld | hInd
  · exact weakEval_isAxiom env hOld
  · rcases (isIndAxiom_iff φ).1 hInd with ⟨x, ψ, rfl⟩
    exact weakEval_inductionAxiom env x ψ

/-- The complete induction checker is sound in the weak interpretation. -/
theorem checkI_weak_sound :
    ∀ p : ProofTree, ∀ φ : Formula, ∀ env : Nat → Nat,
      checkI p = some φ → weakEvalForm env φ := by
  intro p
  induction p with
  | ax ψ =>
      intro φ env h
      simp [checkI] at h
      rcases h with ⟨hax, rfl⟩
      exact weakEval_isAxiomI env hax
  | mp p q ihp ihq =>
      intro φ env h
      cases hp : checkI p with
      | none => simp [checkI, hp] at h
      | some a =>
        cases hq : checkI q with
        | none => simp [checkI, hp, hq] at h
        | some c =>
          cases a with
          | imp u v =>
              simp [checkI, hp, hq] at h
              rcases h with ⟨rfl, rfl⟩
              exact (ihp (Formula.imp u v) env hp) (ihq u env hq)
          | eq _ _ => simp [checkI, hp, hq] at h
          | not _ => simp [checkI, hp, hq] at h
          | all _ _ => simp [checkI, hp, hq] at h
  | gen x p ih =>
      intro φ env h
      cases hp : checkI p with
      | none => simp [checkI, hp] at h
      | some ψ =>
        simp [checkI, hp] at h
        cases h
        intro n
        exact ih ψ (envUpdate env x n) hp
  | spec x t p ih =>
      intro φ env h
      cases hp : checkI p with
      | none => simp [checkI, hp] at h
      | some a =>
        cases a with
        | all y ψ =>
          simp [checkI, hp] at h
          rcases h with ⟨⟨rfl, ht⟩, rfl⟩
          have hall := ih (Formula.all x ψ) env hp
          have hinst := hall (weakEvalTerm env t)
          exact (weakEvalForm_subst_closed env x t ht ψ).2 hinst
        | eq _ _ => simp [checkI, hp] at h
        | not _ => simp [checkI, hp] at h
        | imp _ _ => simp [checkI, hp] at h

/-- Weak soundness of extended provability. -/
theorem provableI_weak_sound {φ : Formula} (h : ProvableI φ)
    (env : Nat → Nat) : weakEvalForm env φ := by
  rcases h with ⟨p, hp⟩
  exact checkI_weak_sound p φ env hp

/-! ## Declared Sigma-one class and the route-killing sentence -/

/-- A syntactic Sigma-one class. It contains every quantifier-free formula,
closes under positive conjunction/disjunction and existential quantification,
and includes explicitly bounded existential/universal quantifiers. -/
inductive IsSigma1 : Formula → Prop
  | bounded {φ : Formula} : isBounded φ = true → IsSigma1 φ
  | and {φ ψ : Formula} : IsSigma1 φ → IsSigma1 ψ → IsSigma1 (andF φ ψ)
  | or {φ ψ : Formula} : IsSigma1 φ → IsSigma1 ψ → IsSigma1 (orF φ ψ)
  | exists (x : Nat) {φ : Formula} : IsSigma1 φ → IsSigma1 (existsF x φ)
  | boundedExists (x : Nat) (t : Term) {φ : Formula} :
      IsSigma1 φ → IsSigma1 (existsF x (andF (leF (Term.var x) t) φ))
  | boundedAll (x : Nat) (t : Term) {φ : Formula} :
      IsSigma1 φ → IsSigma1
        (Formula.all x (Formula.imp (leF (Term.var x) t) φ))

/-- The closed atomic standard truth that exposes the missing equality
congruence interface. -/
def sigmaOneCounterexample : Formula :=
  Formula.eq
    (Term.succ (Term.add (Term.succ Term.zero) Term.zero))
    (Term.succ (Term.succ Term.zero))

/-- The counterexample is quantifier-free and hence Sigma-one. -/
theorem sigmaOneCounterexample_isSigma1 : IsSigma1 sigmaOneCounterexample := by
  apply IsSigma1.bounded
  rfl

/-- The counterexample is closed. -/
theorem sigmaOneCounterexample_sentence : IsSentence sigmaOneCounterexample := by
  intro x
  rfl

/-- The counterexample is true in standard Nat arithmetic. -/
theorem sigmaOneCounterexample_true : evalForm env0 sigmaOneCounterexample := by
  rfl

/-- The same formula is false in the weak checker model. -/
theorem sigmaOneCounterexample_weak_false :
    ¬ weakEvalForm env0 sigmaOneCounterexample := by
  simp [sigmaOneCounterexample, weakEvalForm, weakEvalTerm, weakEq]

/-- Therefore the induction-strengthened checker cannot prove this standard
true atomic formula. -/
theorem sigmaOneCounterexample_not_provableI :
    ¬ ProvableI sigmaOneCounterexample := by
  intro h
  exact sigmaOneCounterexample_weak_false (provableI_weak_sound h env0)

/-- The exact external Sigma-one completeness proposition requested by the HBL
roadmap. -/
def Sigma1Completeness : Prop :=
  ∀ φ : Formula,
    IsSigma1 φ → IsSentence φ → evalForm env0 φ → ProvableI φ

/-- Full external Sigma-one completeness is impossible for the current
induction-strengthened checker. The obstruction is already a closed atomic
formula. -/
theorem sigma1_complete_impossible : ¬ Sigma1Completeness := by
  intro h
  exact sigmaOneCounterexample_not_provableI
    (h sigmaOneCounterexample sigmaOneCounterexample_isSigma1
      sigmaOneCounterexample_sentence sigmaOneCounterexample_true)

/-- Explicit missing-law classification. The route fails at equality
congruence/rewriting before internal Sigma-one completeness is reached. -/
structure SigmaOneRouteKill : Prop where
  standardTrue : evalForm env0 sigmaOneCounterexample
  sigmaOne : IsSigma1 sigmaOneCounterexample
  closed : IsSentence sigmaOneCounterexample
  notDerivable : ¬ ProvableI sigmaOneCounterexample
  externalCompletenessImpossible : ¬ Sigma1Completeness

/-- Closed route-kill package. -/
theorem sigmaOne_route_killed : SigmaOneRouteKill where
  standardTrue := sigmaOneCounterexample_true
  sigmaOne := sigmaOneCounterexample_isSigma1
  closed := sigmaOneCounterexample_sentence
  notDerivable := sigmaOneCounterexample_not_provableI
  externalCompletenessImpossible := sigma1_complete_impossible

#check @weakEvalTerm
#check @weakEq
#check @weakEvalForm
#check @weakEval_isQAxiom
#check @weakEval_inductionAxiom
#check @checkI_weak_sound
#check @provableI_weak_sound
#check @IsSigma1
#check @sigmaOneCounterexample
#check @sigmaOneCounterexample_isSigma1
#check @sigmaOneCounterexample_true
#check @sigmaOneCounterexample_not_provableI
#check @Sigma1Completeness
#check @sigma1_complete_impossible
#check @SigmaOneRouteKill
#check @sigmaOne_route_killed
#print axioms weakEval_isQAxiom
#print axioms weakEval_inductionAxiom
#print axioms checkI_weak_sound
#print axioms provableI_weak_sound
#print axioms sigmaOneCounterexample_isSigma1
#print axioms sigmaOneCounterexample_true
#print axioms sigmaOneCounterexample_not_provableI
#print axioms sigma1_complete_impossible
#print axioms sigmaOne_route_killed

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
