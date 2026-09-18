import OperatorKO7.Meta.DistinctionBoundary.GodelStandardQInterpretation
import OperatorKO7.Meta.DistinctionBoundary.GodelFirstIncompleteness

set_option autoImplicit false

/-!
# Induction-strengthened checker for the live arithmetic syntax

This module extends the compiled Robinson-Q checker by the full first-order
induction schema over its existing named-variable formula language. The schema
is recognized syntactically and therefore remains decidable. No semantic
oracle is added.

For a variable `x` and formula `φ`, the induction axiom is

  (φ[0/x] ∧ ∀x (φ → φ[S(x)/x])) → ∀x φ.

The existing substitution operator is capture-safe for the step term `S(x)`:
under a binder for `x` it stops, and under every other binder the inserted term
contains only `x`. We prove the corresponding semantic substitution theorem,
then Nat-validity of every induction instance and soundness of the extended
checker.

Relation: checked `ProofTree` derivability with `isAxiomI` at leaves.
Closure: MP, generalization, and closed specialization as in the live checker.
Trust: kernel checked; Mathlib baseline only.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- Step term used by the induction schema. -/
def inductionStepTerm (x : Nat) : Term := Term.succ (Term.var x)

/-- One full induction-schema instance. -/
def inductionAxiom (x : Nat) (φ : Formula) : Formula :=
  Formula.imp
    (andF
      (substForm x Term.zero φ)
      (Formula.all x
        (Formula.imp φ (substForm x (inductionStepTerm x) φ))))
    (Formula.all x φ)

/-- Decidable syntactic recognizer for the induction schema. -/
def isIndAxiom : Formula → Bool
  | Formula.imp a (Formula.all x φ) => decide (a =
      andF
        (substForm x Term.zero φ)
        (Formula.all x
          (Formula.imp φ (substForm x (inductionStepTerm x) φ))))
  | _ => false

/-- Exact shape theorem for the induction recognizer. -/
theorem isIndAxiom_iff (ψ : Formula) :
    isIndAxiom ψ = true ↔ ∃ x φ, ψ = inductionAxiom x φ := by
  cases ψ with
  | imp a b =>
      cases b with
      | all x φ =>
          simp [isIndAxiom, inductionAxiom]
      | eq _ _ => simp [isIndAxiom, inductionAxiom]
      | not _ => simp [isIndAxiom, inductionAxiom]
      | imp _ _ => simp [isIndAxiom, inductionAxiom]
  | eq _ _ => simp [isIndAxiom, inductionAxiom]
  | not _ => simp [isIndAxiom, inductionAxiom]
  | all _ _ => simp [isIndAxiom, inductionAxiom]

/-- Extended axiom recognizer: the live Q/logical axioms plus induction. -/
def isAxiomI (φ : Formula) : Bool := isAxiom φ || isIndAxiom φ

/-- Extended checker over the existing proof-tree datatype. -/
def checkI : ProofTree → Option Formula
  | .ax φ => if isAxiomI φ then some φ else none
  | .mp p q =>
      match checkI p, checkI q with
      | some (Formula.imp a b), some c => if a = c then some b else none
      | _, _ => none
  | .gen x p =>
      match checkI p with
      | some φ => some (Formula.all x φ)
      | none => none
  | .spec x t p =>
      match checkI p with
      | some (Formula.all y φ) =>
          if decide (x = y) && isClosedTerm t then some (substForm x t φ) else none
      | _ => none

/-- Provability in the induction-strengthened checker. -/
def ProvableI (φ : Formula) : Prop := ∃ p : ProofTree, checkI p = some φ

/-- Every original axiom is an extended axiom. -/
theorem isAxiom_implies_isAxiomI {φ : Formula} (h : isAxiom φ = true) :
    isAxiomI φ = true := by
  simp [isAxiomI, h]

/-- Every original checked proof remains checked by the induction extension. -/
theorem check_to_checkI :
    ∀ p : ProofTree, ∀ φ : Formula, check p = some φ → checkI p = some φ
  | .ax ψ, φ, h => by
      simp [check] at h
      rcases h with ⟨hax, rfl⟩
      simp [checkI, isAxiom_implies_isAxiomI hax]
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
              have hpI := check_to_checkI p (Formula.imp u v) hp
              have hqI := check_to_checkI q u hq
              simp [checkI, hpI, hqI]
          | eq _ _ => simp [check, hp, hq] at h
          | not _ => simp [check, hp, hq] at h
          | all _ _ => simp [check, hp, hq] at h
  | .gen x p, φ, h => by
      cases hp : check p with
      | none => simp [check, hp] at h
      | some ψ =>
          simp [check, hp] at h
          cases h
          have hpI := check_to_checkI p ψ hp
          simp [checkI, hpI]
  | .spec x t p, φ, h => by
      cases hp : check p with
      | none => simp [check, hp] at h
      | some a =>
        cases a with
        | all y ψ =>
          simp [check, hp] at h
          rcases h with ⟨⟨rfl, ht⟩, rfl⟩
          have hpI := check_to_checkI p (Formula.all x ψ) hp
          simp [checkI, hpI, ht]
        | eq _ _ => simp [check, hp] at h
        | not _ => simp [check, hp] at h
        | imp _ _ => simp [check, hp] at h

/-- The original theory embeds in the induction extension. -/
theorem provable_to_provableI {φ : Formula} : Provable φ → ProvableI φ := by
  rintro ⟨p, hp⟩
  exact ⟨p, check_to_checkI p φ hp⟩

/-- Substitution of `S(x)` in terms has the expected environment semantics. -/
theorem evalTerm_subst_selfSucc (env : Nat → Nat) (x : Nat) (t : Term) :
    evalTerm env (substTerm x (inductionStepTerm x) t) =
      evalTerm (envUpdate env x (env x + 1)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change evalTerm env (substTerm x (inductionStepTerm x) t) + 1 =
        evalTerm (envUpdate env x (env x + 1)) t + 1
      exact congrArg (fun n => n + 1) ih
  | add s t ihs iht =>
      change evalTerm env (substTerm x (inductionStepTerm x) s) +
          evalTerm env (substTerm x (inductionStepTerm x) t) =
        evalTerm (envUpdate env x (env x + 1)) s +
          evalTerm (envUpdate env x (env x + 1)) t
      rw [ihs, iht]
  | mul s t ihs iht =>
      change evalTerm env (substTerm x (inductionStepTerm x) s) *
          evalTerm env (substTerm x (inductionStepTerm x) t) =
        evalTerm (envUpdate env x (env x + 1)) s *
          evalTerm (envUpdate env x (env x + 1)) t
      rw [ihs, iht]
  | var y =>
      by_cases hy : y = x
      · subst y
        simp [substTerm, evalTerm, inductionStepTerm, envUpdate]
      · simp [substTerm, evalTerm, envUpdate, hy]

/-- Updating the substituted variable and then a distinct binder equals
updating the binder first and then the substituted variable with its unchanged
old value. -/
theorem envUpdate_selfSucc_comm (env : Nat → Nat) {x y : Nat} (hyx : y ≠ x)
    (a : Nat) (z : Nat) :
    envUpdate (envUpdate env x (env x + 1)) y a z =
      envUpdate (envUpdate env y a) x (env x + 1) z := by
  exact (envUpdate_comm env hyx (env x + 1) a z).symm

/-- Substitution of `S(x)` in formulas has the expected environment semantics. -/
theorem evalForm_subst_selfSucc (env : Nat → Nat) (x : Nat) :
    ∀ φ : Formula,
      evalForm env (substForm x (inductionStepTerm x) φ) ↔
        evalForm (envUpdate env x (env x + 1)) φ
  | .eq s t => by
      simp [substForm, evalForm, evalTerm_subst_selfSucc]
  | .not φ => by
      simp [substForm, evalForm, evalForm_subst_selfSucc env x φ]
  | .imp φ ψ => by
      simp [substForm, evalForm, evalForm_subst_selfSucc env x φ,
        evalForm_subst_selfSucc env x ψ]
  | .all y φ => by
      by_cases hyx : y = x
      · subst y
        simp only [substForm, if_pos, evalForm]
        constructor
        · intro h a
          have henv : ∀ z,
              envUpdate (envUpdate env x (env x + 1)) x a z =
                envUpdate env x a z := by
            intro z
            exact envUpdate_same env x (env x + 1) a z
          exact (evalForm_env_eq φ henv).2 (h a)
        · intro h a
          have henv : ∀ z,
              envUpdate env x a z =
                envUpdate (envUpdate env x (env x + 1)) x a z := by
            intro z
            exact (envUpdate_same env x (env x + 1) a z).symm
          exact (evalForm_env_eq φ henv).2 (h a)
      · simp only [substForm, if_neg hyx, evalForm]
        constructor
        · intro h a
          have hsub := (evalForm_subst_selfSucc
            (envUpdate env y a) x φ).1 (h a)
          have hxy : x ≠ y := Ne.symm hyx
          have henv : ∀ z,
              envUpdate (envUpdate env y a) x
                  (envUpdate env y a x + 1) z =
                envUpdate (envUpdate env x (env x + 1)) y a z := by
            intro z
            have hxval : envUpdate env y a x = env x := by
              simp [envUpdate, hxy]
            rw [hxval]
            exact (envUpdate_selfSucc_comm env hyx a z).symm
          exact (evalForm_env_eq φ henv).1 hsub
        · intro h a
          have hxy : x ≠ y := Ne.symm hyx
          have hxval : envUpdate env y a x = env x := by
            simp [envUpdate, hxy]
          have henv : ∀ z,
              envUpdate (envUpdate env x (env x + 1)) y a z =
                envUpdate (envUpdate env y a) x
                  (envUpdate env y a x + 1) z := by
            intro z
            rw [hxval]
            exact envUpdate_selfSucc_comm env hyx a z
          have htarget : evalForm
              (envUpdate (envUpdate env y a) x
                (envUpdate env y a x + 1)) φ :=
            (evalForm_env_eq φ henv).1 (h a)
          exact (evalForm_subst_selfSucc (envUpdate env y a) x φ).2 htarget

/-- Every induction instance is valid in the standard Nat interpretation. -/
theorem eval_inductionAxiom (env : Nat → Nat) (x : Nat) (φ : Formula) :
    evalForm env (inductionAxiom x φ) := by
  intro hante
  have hpair := (eval_andF env
    (substForm x Term.zero φ)
    (Formula.all x
      (Formula.imp φ (substForm x (inductionStepTerm x) φ)))).1 hante
  have hbaseSub := hpair.1
  have hstep := hpair.2
  have hbase : evalForm (envUpdate env x 0) φ := by
    have hsubst := evalForm_subst_closed env x Term.zero (by rfl) φ
    simpa [evalTerm] using hsubst.1 hbaseSub
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
      have hstepN := hstep n
      have hnextSub :
          evalForm (envUpdate env x n)
            (substForm x (inductionStepTerm x) φ) :=
        hstepN ih
      have hsem := (evalForm_subst_selfSucc (envUpdate env x n) x φ).1 hnextSub
      have henv : ∀ z,
          envUpdate (envUpdate env x n) x
              (envUpdate env x n x + 1) z =
            envUpdate env x (n + 1) z := by
        intro z
        by_cases hz : z = x <;> simp [envUpdate, hz]
      exact (evalForm_env_eq φ henv).1 hsem

/-- Every extended axiom is true in the standard Nat interpretation. -/
theorem eval_isAxiomI (env : Nat → Nat) {φ : Formula}
    (hax : isAxiomI φ = true) : evalForm env φ := by
  simp [isAxiomI, Bool.or_eq_true] at hax
  rcases hax with hOld | hInd
  · exact eval_isAxiom env hOld
  · rcases (isIndAxiom_iff φ).1 hInd with ⟨x, ψ, rfl⟩
    exact eval_inductionAxiom env x ψ

/-- Soundness of the induction-strengthened checker on Nat. -/
theorem checkI_sound :
    ∀ p : ProofTree, ∀ φ : Formula, ∀ env : Nat → Nat,
      checkI p = some φ → evalForm env φ := by
  intro p
  induction p with
  | ax ψ =>
      intro φ env h
      simp [checkI] at h
      rcases h with ⟨hax, rfl⟩
      exact eval_isAxiomI env hax
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
          have hinst := hall (evalTerm env t)
          exact (evalForm_subst_closed env x t ht ψ).2 hinst
        | eq _ _ => simp [checkI, hp] at h
        | not _ => simp [checkI, hp] at h
        | imp _ _ => simp [checkI, hp] at h

/-- Every theorem of the induction-strengthened checker is true on Nat. -/
theorem provableI_sound {φ : Formula} (h : ProvableI φ) (env : Nat → Nat) :
    evalForm env φ := by
  rcases h with ⟨p, hp⟩
  exact checkI_sound p φ env hp

/-- Consistency of the induction-strengthened checker. -/
theorem induction_checker_consistent : ¬ ProvableI falsum := by
  intro h
  exact evalForm_falsum env0 (provableI_sound h env0)

/-- Every syntactic induction instance is directly provable as an axiom leaf. -/
theorem inductionAxiom_provableI (x : Nat) (φ : Formula) :
    ProvableI (inductionAxiom x φ) := by
  refine ⟨ProofTree.ax (inductionAxiom x φ), ?_⟩
  simp [checkI, isAxiomI, isIndAxiom, inductionAxiom]

/-! ## Independent derivability presentation -/

/-- Axiom predicate of the induction-strengthened checker. -/
def CompiledIAxiom (φ : Formula) : Prop := isAxiomI φ = true

/-- Hilbert derivability independent of the `ProofTree` representation. -/
inductive CompiledIDerives : Formula → Prop
  | ax {φ : Formula} : CompiledIAxiom φ → CompiledIDerives φ
  | mp {a b : Formula} :
      CompiledIDerives (Formula.imp a b) →
      CompiledIDerives a → CompiledIDerives b
  | gen (x : Nat) {φ : Formula} :
      CompiledIDerives φ → CompiledIDerives (Formula.all x φ)
  | spec (x : Nat) (t : Term) {φ : Formula} :
      isClosedTerm t = true →
      CompiledIDerives (Formula.all x φ) →
      CompiledIDerives (substForm x t φ)

/-- Independent induction derivations serialize as checked proof trees. -/
theorem compiledIDerives_to_provableI {φ : Formula}
    (h : CompiledIDerives φ) : ProvableI φ := by
  induction h with
  | @ax φ hax =>
      exact ⟨ProofTree.ax φ, by simp [checkI, CompiledIAxiom] at hax ⊢; exact hax⟩
  | mp hab ha ihab iha =>
      rcases ihab with ⟨p, hp⟩
      rcases iha with ⟨q, hq⟩
      exact ⟨ProofTree.mp p q, by simp [checkI, hp, hq]⟩
  | gen x h ih =>
      rcases ih with ⟨p, hp⟩
      exact ⟨ProofTree.gen x p, by simp [checkI, hp]⟩
  | spec x t ht h ih =>
      rcases ih with ⟨p, hp⟩
      exact ⟨ProofTree.spec x t p, by simp [checkI, hp, ht]⟩

/-- Every checked extended proof induces an independent derivation. -/
theorem proofTree_checkI_to_compiledIDerives :
    ∀ p : ProofTree, ∀ φ : Formula,
      checkI p = some φ → CompiledIDerives φ
  | .ax ψ, φ, h => by
      simp [checkI] at h
      rcases h with ⟨hax, rfl⟩
      exact CompiledIDerives.ax hax
  | .mp p q, φ, h => by
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
              exact CompiledIDerives.mp
                (proofTree_checkI_to_compiledIDerives p (Formula.imp u v) hp)
                (proofTree_checkI_to_compiledIDerives q u hq)
          | eq _ _ => simp [checkI, hp, hq] at h
          | not _ => simp [checkI, hp, hq] at h
          | all _ _ => simp [checkI, hp, hq] at h
  | .gen x p, φ, h => by
      cases hp : checkI p with
      | none => simp [checkI, hp] at h
      | some ψ =>
        simp [checkI, hp] at h
        cases h
        exact CompiledIDerives.gen x
          (proofTree_checkI_to_compiledIDerives p ψ hp)
  | .spec x t p, φ, h => by
      cases hp : checkI p with
      | none => simp [checkI, hp] at h
      | some a =>
        cases a with
        | all y ψ =>
          simp [checkI, hp] at h
          rcases h with ⟨⟨rfl, ht⟩, rfl⟩
          exact CompiledIDerives.spec x t ht
            (proofTree_checkI_to_compiledIDerives p (Formula.all x ψ) hp)
        | eq _ _ => simp [checkI, hp] at h
        | not _ => simp [checkI, hp] at h
        | imp _ _ => simp [checkI, hp] at h

/-- Exact adequacy theorem for the induction-strengthened checker. -/
theorem compiledIDerives_iff_provableI (φ : Formula) :
    CompiledIDerives φ ↔ ProvableI φ := by
  constructor
  · exact compiledIDerives_to_provableI
  · rintro ⟨p, hp⟩
    exact proofTree_checkI_to_compiledIDerives p φ hp

/-- Every original compiled-Q derivation embeds into the induction extension. -/
theorem compiledQDerives_to_compiledIDerives {φ : Formula}
    (h : CompiledQDerives φ) : CompiledIDerives φ := by
  apply (compiledIDerives_iff_provableI φ).2
  exact provable_to_provableI ((compiledQDerives_iff_provable φ).1 h)

/-- All seven Robinson-Q axioms remain derivation leaves in the extension. -/
theorem compiledI_all_q_axioms (φ : Formula) (h : φ ∈ qAxioms) :
    CompiledIDerives φ :=
  compiledQDerives_to_compiledIDerives (compiledQ_all_q_axioms φ h)

/-- Every syntactic induction instance is an independent derivation leaf. -/
theorem compiledI_induction (x : Nat) (φ : Formula) :
    CompiledIDerives (inductionAxiom x φ) := by
  apply CompiledIDerives.ax
  simp [CompiledIAxiom, isAxiomI, isIndAxiom, inductionAxiom]

#check @CompiledIAxiom
#check @CompiledIDerives
#check @compiledIDerives_to_provableI
#check @proofTree_checkI_to_compiledIDerives
#check @compiledIDerives_iff_provableI
#check @compiledQDerives_to_compiledIDerives
#check @compiledI_all_q_axioms
#check @compiledI_induction

#check @inductionAxiom
#check @isIndAxiom
#check @isIndAxiom_iff
#check @isAxiomI
#check @checkI
#check @ProvableI
#check @check_to_checkI
#check @provable_to_provableI
#check @evalTerm_subst_selfSucc
#check @evalForm_subst_selfSucc
#check @eval_inductionAxiom
#check @eval_isAxiomI
#check @checkI_sound
#check @provableI_sound
#check @induction_checker_consistent
#check @inductionAxiom_provableI
#print axioms isIndAxiom_iff
#print axioms check_to_checkI
#print axioms provable_to_provableI
#print axioms evalTerm_subst_selfSucc
#print axioms evalForm_subst_selfSucc
#print axioms eval_inductionAxiom
#print axioms eval_isAxiomI
#print axioms checkI_sound
#print axioms provableI_sound
#print axioms induction_checker_consistent
#print axioms inductionAxiom_provableI
#print axioms compiledIDerives_to_provableI
#print axioms proofTree_checkI_to_compiledIDerives
#print axioms compiledIDerives_iff_provableI
#print axioms compiledQDerives_to_compiledIDerives
#print axioms compiledI_all_q_axioms
#print axioms compiledI_induction

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
