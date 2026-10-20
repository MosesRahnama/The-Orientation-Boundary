import OperatorKO7.Meta.DistinctionBoundary.GodelStandardQInterpretation

/-!
# General structure semantics for the compiled Robinson-Q checker

This module interprets the live `Term`, `Formula`, and `ProofTree` syntax in an
arbitrary arithmetic structure. It proves that the existing checker is sound in
every structure satisfying the seven formulas in `qAxioms`.

The construction is pinned to the existing Nat evaluator by
`evalTermIn_nat` and `evalFormIn_nat`. The specialization rule is handled by a
closed-term substitution theorem in the general structure, not by assuming a
new logical axiom.

Relation: the live `check` relation on `ProofTree` and `Formula`.
Closure: one checked proof tree; `Provable` is existential over checked trees.
Trust: kernel checked, Mathlib baseline only.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

universe u

/-- A first-order arithmetic structure for the exact language used by the live
compiled checker. -/
structure ArithStructure where
  Carrier : Type u
  zero : Carrier
  succ : Carrier → Carrier
  add : Carrier → Carrier → Carrier
  mul : Carrier → Carrier → Carrier

/-- Interpretation of live arithmetic terms in an arbitrary structure. -/
def evalTermIn (M : ArithStructure) (env : Nat → M.Carrier) : Term → M.Carrier
  | .zero => M.zero
  | .succ t => M.succ (evalTermIn M env t)
  | .add s t => M.add (evalTermIn M env s) (evalTermIn M env t)
  | .mul s t => M.mul (evalTermIn M env s) (evalTermIn M env t)
  | .var x => env x

/-- Interpretation of live formulas in an arbitrary structure. -/
def evalFormIn (M : ArithStructure) (env : Nat → M.Carrier) : Formula → Prop
  | .eq s t => evalTermIn M env s = evalTermIn M env t
  | .not φ => ¬ evalFormIn M env φ
  | .imp φ ψ => evalFormIn M env φ → evalFormIn M env ψ
  | .all x φ => ∀ a : M.Carrier, evalFormIn M (fun y => if y = x then a else env y) φ

/-- Environment update for the general semantics. -/
def envUpdateIn (M : ArithStructure) (env : Nat → M.Carrier)
    (x : Nat) (a : M.Carrier) : Nat → M.Carrier :=
  fun y => if y = x then a else env y

/-- The standard natural-number structure, written with the same successor
operation as the existing `evalTerm`. -/
def natStructure : ArithStructure where
  Carrier := Nat
  zero := 0
  succ := fun n => n + 1
  add := Nat.add
  mul := Nat.mul

/-- The general term evaluator specializes exactly to the existing Nat
semantics. -/
theorem evalTermIn_nat (env : Nat → Nat) (t : Term) :
    evalTermIn natStructure env t = evalTerm env t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change natStructure.succ (evalTermIn natStructure env t) = evalTerm env t + 1
      rw [ih]
      rfl
  | add s t ihs iht =>
      change natStructure.add (evalTermIn natStructure env s)
          (evalTermIn natStructure env t) = evalTerm env s + evalTerm env t
      rw [ihs, iht]
      rfl
  | mul s t ihs iht =>
      change natStructure.mul (evalTermIn natStructure env s)
          (evalTermIn natStructure env t) = evalTerm env s * evalTerm env t
      rw [ihs, iht]
      rfl
  | var x => rfl

/-- The general formula evaluator specializes exactly to the existing Nat
semantics. -/
theorem evalFormIn_nat (env : Nat → Nat) (φ : Formula) :
    evalFormIn natStructure env φ ↔ evalForm env φ := by
  induction φ generalizing env with
  | eq s t => simp [evalFormIn, evalForm, evalTermIn_nat]
  | not φ ih => simp [evalFormIn, evalForm, ih]
  | imp φ ψ ihφ ihψ => simp [evalFormIn, evalForm, ihφ, ihψ]
  | all x φ ih =>
      simp only [evalFormIn, evalForm]
      constructor
      · intro h n
        exact (ih (fun y => if y = x then n else env y)).1 (h n)
      · intro h n
        exact (ih (fun y => if y = x then n else env y)).2 (h n)

/-- Closed terms have environment-independent denotation in every arithmetic
structure. -/
theorem isClosedTerm_evalTermIn_indep (M : ArithStructure) (t : Term)
    (ht : isClosedTerm t = true) :
    ∀ env env' : Nat → M.Carrier, evalTermIn M env t = evalTermIn M env' t := by
  induction t with
  | zero => intro env env'; rfl
  | succ t ih =>
      intro env env'
      simp [isClosedTerm] at ht
      simp [evalTermIn, ih ht env env']
  | add s t ihs iht =>
      intro env env'
      simp [isClosedTerm, Bool.and_eq_true] at ht
      simp [evalTermIn, ihs ht.1 env env', iht ht.2 env env']
  | mul s t ihs iht =>
      intro env env'
      simp [isClosedTerm, Bool.and_eq_true] at ht
      simp [evalTermIn, ihs ht.1 env env', iht ht.2 env env']
  | var x => simp [isClosedTerm] at ht

/-- Updating a variable absent from a term does not change its denotation in an
arbitrary arithmetic structure. -/
theorem evalTermIn_fresh (M : ArithStructure) (x : Nat) :
    ∀ t : Term, termHasVar x t = false →
      ∀ env : Nat → M.Carrier, ∀ a : M.Carrier,
        evalTermIn M (fun y => if y = x then a else env y) t =
          evalTermIn M env t
  | .zero, _, _, _ => rfl
  | .succ t, ht, env, a => by
      simp [termHasVar] at ht
      simp [evalTermIn, evalTermIn_fresh M x t ht env a]
  | .add s t, ht, env, a => by
      simp [termHasVar, Bool.or_eq_false_iff] at ht
      simp [evalTermIn, evalTermIn_fresh M x s ht.1 env a,
        evalTermIn_fresh M x t ht.2 env a]
  | .mul s t, ht, env, a => by
      simp [termHasVar, Bool.or_eq_false_iff] at ht
      simp [evalTermIn, evalTermIn_fresh M x s ht.1 env a,
        evalTermIn_fresh M x t ht.2 env a]
  | .var y, ht, env, a => by
      simp [termHasVar, decide_eq_false_iff_not] at ht
      simp [evalTermIn, ht]
/-- General term substitution semantics. -/
theorem evalTermIn_subst (M : ArithStructure) (env : Nat → M.Carrier)
    (x : Nat) (u : Term) :
    ∀ t : Term,
      evalTermIn M env (substTerm x u t) =
        evalTermIn M (envUpdateIn M env x (evalTermIn M env u)) t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => simp [substTerm, evalTermIn, ih]
  | add s t ihs iht => simp [substTerm, evalTermIn, ihs, iht]
  | mul s t ihs iht => simp [substTerm, evalTermIn, ihs, iht]
  | var y =>
      by_cases h : y = x
      · subst h
        simp [substTerm, evalTermIn, envUpdateIn]
      · simp [substTerm, evalTermIn, envUpdateIn, h]

/-- Pointwise equal environments satisfy the same formulas. -/
theorem evalFormIn_env_eq_aux (M : ArithStructure) (φ : Formula) :
    ∀ {env env' : Nat → M.Carrier}, (∀ z, env z = env' z) →
      (evalFormIn M env φ ↔ evalFormIn M env' φ) := by
  induction φ with
  | eq s t =>
      intro env env' h
      have hs : evalTermIn M env s = evalTermIn M env' s := by
        induction s with
        | zero => rfl
        | succ s ih => simp [evalTermIn, ih]
        | add a b iha ihb => simp [evalTermIn, iha, ihb]
        | mul a b iha ihb => simp [evalTermIn, iha, ihb]
        | var z => exact h z
      have ht : evalTermIn M env t = evalTermIn M env' t := by
        induction t with
        | zero => rfl
        | succ t ih => simp [evalTermIn, ih]
        | add a b iha ihb => simp [evalTermIn, iha, ihb]
        | mul a b iha ihb => simp [evalTermIn, iha, ihb]
        | var z => exact h z
      simp [evalFormIn, hs, ht]
  | not φ ih =>
      intro env env' h
      simp [evalFormIn, ih h]
  | imp φ ψ ihφ ihψ =>
      intro env env' h
      simp [evalFormIn, ihφ h, ihψ h]
  | all y φ ih =>
      intro env env' h
      simp only [evalFormIn]
      constructor
      · intro hall a
        have henv : ∀ z,
            (fun w => if w = y then a else env w) z =
              (fun w => if w = y then a else env' w) z := by
          intro z
          by_cases hz : z = y
          · simp [hz]
          · simp [hz, h z]
        exact (ih henv).1 (hall a)
      · intro hall a
        have henv : ∀ z,
            (fun w => if w = y then a else env' w) z =
              (fun w => if w = y then a else env w) z := by
          intro z
          by_cases hz : z = y
          · simp [hz]
          · simp [hz, (h z).symm]
        exact (ih henv).1 (hall a)

/-- Updating distinct variables commutes in the general semantics. -/
theorem envUpdateIn_if_comm (M : ArithStructure) (env : Nat → M.Carrier)
    {x y : Nat} (hne : y ≠ x) (a b : M.Carrier) (z : Nat) :
    envUpdateIn M (fun w => if w = y then b else env w) x a z =
      (if z = y then b else envUpdateIn M env x a z) := by
  simp only [envUpdateIn]
  by_cases hz : z = x
  · by_cases hy : z = y
    · exact False.elim (hne (hy.symm.trans hz))
    · rw [if_pos hz, if_neg hy, if_pos hz]
  · by_cases hy : z = y
    · rw [if_neg hz, if_pos hy]
      simp [hy]
    · rw [if_neg hz, if_neg hy, if_neg hz]
      simp [hy]

/-- Closed substitution has the expected semantics in every arithmetic
structure. -/
theorem evalFormIn_subst_closed (M : ArithStructure)
    (env : Nat → M.Carrier) (x : Nat) (u : Term)
    (hu : isClosedTerm u = true) :
    ∀ φ : Formula,
      evalFormIn M env (substForm x u φ) ↔
        evalFormIn M (envUpdateIn M env x (evalTermIn M env u)) φ := by
  intro φ
  induction φ generalizing env with
  | eq s t =>
      simp [substForm, evalFormIn, evalTermIn_subst]
  | not φ ih =>
      simp [substForm, evalFormIn, ih]
  | imp φ ψ ihφ ihψ =>
      simp [substForm, evalFormIn, ihφ, ihψ]
  | all y φ ih =>
      by_cases hxy : y = x
      · subst hxy
        simp only [substForm, if_pos, evalFormIn]
        constructor
        · intro hall a
          have henv : ∀ z,
              envUpdateIn M (envUpdateIn M env y (evalTermIn M env u)) y a z =
                envUpdateIn M env y a z := by
            intro z
            by_cases hz : z = y <;> simp [envUpdateIn, hz]
          exact (evalFormIn_env_eq_aux M φ henv).2 (hall a)
        · intro hall a
          have henv : ∀ z,
              envUpdateIn M env y a z =
                envUpdateIn M (envUpdateIn M env y (evalTermIn M env u)) y a z := by
            intro z
            by_cases hz : z = y <;> simp [envUpdateIn, hz]
          exact (evalFormIn_env_eq_aux M φ henv).2 (hall a)
      · simp only [substForm, if_neg hxy, evalFormIn]
        constructor
        · intro hall a
          have hsub := (ih (env := fun w => if w = y then a else env w)).1 (hall a)
          have hu' :
              evalTermIn M (fun w => if w = y then a else env w) u =
                evalTermIn M env u :=
            isClosedTerm_evalTermIn_indep M u hu _ _
          have henv : ∀ z,
              envUpdateIn M (fun w => if w = y then a else env w) x
                  (evalTermIn M (fun w => if w = y then a else env w) u) z =
                (fun w => if w = y then a else
                  envUpdateIn M env x (evalTermIn M env u) w) z := by
            intro z
            have hcomm := envUpdateIn_if_comm M env hxy
              (evalTermIn M (fun w => if w = y then a else env w) u) a z
            simpa [hu'] using hcomm
          exact (evalFormIn_env_eq_aux M φ henv).1 hsub
        · intro hall a
          have hu' :
              evalTermIn M (fun w => if w = y then a else env w) u =
                evalTermIn M env u :=
            isClosedTerm_evalTermIn_indep M u hu _ _
          have henv : ∀ z,
              (fun w => if w = y then a else
                envUpdateIn M env x (evalTermIn M env u) w) z =
                envUpdateIn M (fun w => if w = y then a else env w) x
                  (evalTermIn M (fun w => if w = y then a else env w) u) z := by
            intro z
            have hcomm := envUpdateIn_if_comm M env hxy
              (evalTermIn M (fun w => if w = y then a else env w) u) a z
            simpa [hu'] using hcomm.symm
          have hpre := (evalFormIn_env_eq_aux M φ henv).1 (hall a)
          exact (ih (env := fun w => if w = y then a else env w)).2 hpre


/-! ## Derived connective semantics -/

/-- Existential formulas evaluate as existential quantification in every
arithmetic structure. -/
theorem evalFormIn_existsF (M : ArithStructure) (env : Nat → M.Carrier)
    (x : Nat) (φ : Formula) :
    evalFormIn M env (existsF x φ) ↔
      ∃ a : M.Carrier, evalFormIn M (fun y => if y = x then a else env y) φ := by
  dsimp [existsF, evalFormIn]
  constructor
  · intro h
    rcases Classical.not_forall.mp h with ⟨a, ha⟩
    exact ⟨a, Classical.not_not.mp ha⟩
  · rintro ⟨a, ha⟩ hall
    exact hall a ha

/-- The encoded conjunction has ordinary conjunction semantics in every
arithmetic structure. -/
theorem evalFormIn_andF (M : ArithStructure) (env : Nat → M.Carrier)
    (phi psi : Formula) :
    evalFormIn M env (andF phi psi) ↔
      evalFormIn M env phi ∧ evalFormIn M env psi := by
  classical
  dsimp [andF, evalFormIn]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact Classical.byContradiction (fun hphi =>
        h (fun hphi' => False.elim (hphi hphi')))
    · exact Classical.byContradiction (fun hpsi =>
        h (fun _ => hpsi))
  · rintro ⟨hphi, hpsi⟩ himp
    exact himp hphi hpsi


/-- The encoded disjunction has ordinary disjunction semantics in every
arithmetic structure. -/
theorem evalFormIn_orF (M : ArithStructure) (env : Nat → M.Carrier)
    (φ ψ : Formula) :
    evalFormIn M env (orF φ ψ) ↔ evalFormIn M env φ ∨ evalFormIn M env ψ := by
  dsimp [orF, evalFormIn]
  constructor
  · intro h
    by_cases hφ : evalFormIn M env φ
    · exact Or.inl hφ
    · exact Or.inr (h hφ)
  · intro h hφ
    exact h.elim (fun hp => False.elim (hφ hp)) id
/-! ## Soundness of the live checker in every model of the seven Q axioms -/

/-- A structure models the exact seven-formula arithmetic layer of the live
checker. -/
def ModelsQ (M : ArithStructure) : Prop :=
  ∀ φ : Formula, φ ∈ qAxioms → ∀ env : Nat → M.Carrier, evalFormIn M env φ

/-- Equality reflexivity is valid in every arithmetic structure. -/
theorem evalFormIn_eq_refl (M : ArithStructure) (env : Nat → M.Carrier)
    (t : Term) : evalFormIn M env (.eq t t) := by
  rfl

/-- Every recognized Robinson-Q axiom is valid in a declared model of the
seven-formula arithmetic layer. -/
theorem evalFormIn_isQAxiom (M : ArithStructure) (hQ : ModelsQ M)
    (env : Nat → M.Carrier) {φ : Formula} (h : isQAxiom φ = true) :
    evalFormIn M env φ :=
  hQ φ ((isQAxiom_iff_mem φ).1 h) env

/-- Every formula accepted by the full live axiom recognizer is valid in any
model of the seven Q axioms. -/
theorem evalFormIn_isAxiom (M : ArithStructure) (hQ : ModelsQ M)
    (env : Nat → M.Carrier) {φ : Formula} (hax : isAxiom φ = true) :
    evalFormIn M env φ := by
  simp [isAxiom, Bool.or_eq_true] at hax
  rcases hax with (((((hQax | hK) | hS) | hDNE) | hR) | hId)
  · exact evalFormIn_isQAxiom M hQ env hQax
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
      exact evalFormIn_eq_refl M env s
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

/-- The live proof-tree checker is sound in every arithmetic structure that
models the exact seven-formula Q layer. -/
theorem check_sound_in (M : ArithStructure) (hQ : ModelsQ M) :
    ∀ p : ProofTree, ∀ φ : Formula, ∀ env : Nat → M.Carrier,
      check p = some φ → evalFormIn M env φ := by
  intro p
  induction p with
  | ax ψ =>
    intro φ env h
    simp [check] at h
    rcases h with ⟨hax, rfl⟩
    exact evalFormIn_isAxiom M hQ env hax
  | mp p q ihp ihq =>
    intro φ env h
    cases hp : check p with
    | none =>
      simp [check, hp] at h
    | some a =>
      cases hq' : check q with
      | none =>
        simp [check, hp, hq'] at h
      | some c =>
        simp [check, hp, hq'] at h
        cases a with
        | imp u v =>
          simp at h
          rcases h with ⟨hc, hφ⟩
          subst hc
          subst hφ
          have himp := ihp (Formula.imp u v) env hp
          have hu := ihq u env hq'
          exact himp hu
        | eq _ _ => simp at h
        | not _ => simp at h
        | all _ _ => simp at h
  | gen x p ih =>
    intro φ env h
    cases hp : check p with
    | none =>
      simp [check, hp] at h
    | some ψ =>
      simp [check, hp] at h
      cases h
      dsimp [evalFormIn]
      intro a
      exact ih ψ (fun y => if y = x then a else env y) hp
  | spec x t p ih =>
    intro φ env h
    cases hp : check p with
    | none =>
      simp [check, hp] at h
    | some ψ =>
      cases ψ with
      | all y body =>
        simp [check, hp] at h
        rcases h with ⟨⟨hx, ht⟩, hφ⟩
        subst hx
        subst hφ
        have hall := ih (Formula.all x body) env hp
        have hinst := hall (evalTermIn M env t)
        exact (evalFormIn_subst_closed M env x t ht body).2 hinst
      | eq _ _ => simp [check, hp] at h
      | not _ => simp [check, hp] at h
      | imp _ _ => simp [check, hp] at h

/-- Every theorem of the live compiled checker is true in every model of its
seven arithmetic axioms. -/
theorem provable_sound_in (M : ArithStructure) (hQ : ModelsQ M)
    {φ : Formula} (h : Provable φ) (env : Nat → M.Carrier) :
    evalFormIn M env φ := by
  rcases h with ⟨p, hp⟩
  exact check_sound_in M hQ p φ env hp

/-- The general soundness theorem specializes to the already-compiled Nat
semantics. -/
theorem provable_sound_in_nat_agrees {φ : Formula} (_h : Provable φ)
    (env : Nat → Nat) :
    evalFormIn natStructure env φ ↔ evalForm env φ :=
  evalFormIn_nat env φ

end OperatorKO7.Meta.DistinctionBoundary.GodelArith


