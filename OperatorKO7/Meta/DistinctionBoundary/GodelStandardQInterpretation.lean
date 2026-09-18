import OperatorKO7.Meta.DistinctionBoundary.GodelRobinsonQ

set_option autoImplicit false

/-!
# Bidirectional derivability interpretation for the compiled Robinson-Q fragment

The live `ProofTree` checker is a Hilbert-style calculus over the seven Robinson-Q
axioms together with its explicit logical/equality axiom recognizers and the
MP/generalization/closed-specialization rules.  It is not advertised here as a
complete textbook first-order equality calculus: the current checker does not
contain a general equality-substitution axiom schema.

This module supplies the closure-dispatch alternative for W1(e): an independent
inductive derivability relation for exactly the compiled fragment, and a
bidirectional theorem showing that it has precisely the same derivable formulas
as `ProofTree/check`.  This removes the checker-tree representation from the
mathematical statement of derivability without strengthening the underlying
logic.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- The recursively decidable axiom predicate of the compiled Q fragment. -/
def CompiledQAxiom (φ : Formula) : Prop :=
  isAxiom φ = true

/-- Axiom membership in the compiled Q fragment is decidable. -/
def compiledQAxiomDecidable (φ : Formula) : Decidable (CompiledQAxiom φ) := by
  unfold CompiledQAxiom
  infer_instance

/-- Inductive Hilbert derivability for the exact fragment implemented by the
compiled checker.  This relation is independent of proof-tree coding. -/
inductive CompiledQDerives : Formula → Prop
  | ax {φ : Formula} : CompiledQAxiom φ → CompiledQDerives φ
  | mp {a b : Formula} :
      CompiledQDerives (Formula.imp a b) → CompiledQDerives a → CompiledQDerives b
  | gen (x : Nat) {φ : Formula} :
      CompiledQDerives φ → CompiledQDerives (Formula.all x φ)
  | spec (x : Nat) (t : Term) {φ : Formula} :
      isClosedTerm t = true →
      CompiledQDerives (Formula.all x φ) →
      CompiledQDerives (substForm x t φ)

/-- Every inductive compiled-Q derivation can be serialized as a checked
`ProofTree`. -/
theorem compiledQDerives_to_provable {φ : Formula}
    (h : CompiledQDerives φ) : Provable φ := by
  induction h with
  | @ax φ hax =>
      refine ⟨ProofTree.ax φ, ?_⟩
      change check (ProofTree.ax φ) = some φ
      simpa [check, CompiledQAxiom] using hax
  | mp hab ha ihab iha =>
      rcases ihab with ⟨p, hp⟩
      rcases iha with ⟨q, hq⟩
      change check p = some _ at hp
      change check q = some _ at hq
      refine ⟨ProofTree.mp p q, ?_⟩
      change check (ProofTree.mp p q) = some _
      simp [check, hp, hq]
  | gen x h ih =>
      rcases ih with ⟨p, hp⟩
      change check p = some _ at hp
      refine ⟨ProofTree.gen x p, ?_⟩
      change check (ProofTree.gen x p) = some _
      simp [check, hp]
  | spec x t ht h ih =>
      rcases ih with ⟨p, hp⟩
      change check p = some _ at hp
      refine ⟨ProofTree.spec x t p, ?_⟩
      change check (ProofTree.spec x t p) = some _
      simp [check, hp, ht]

/-- Every checked proof tree induces an inductive compiled-Q derivation. -/
theorem proofTree_check_to_compiledQDerives :
    ∀ p : ProofTree, ∀ φ : Formula, check p = some φ → CompiledQDerives φ
  | .ax ψ, φ, h => by
      simp [check] at h
      rcases h with ⟨hax, rfl⟩
      exact CompiledQDerives.ax hax
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
            exact CompiledQDerives.mp
              (proofTree_check_to_compiledQDerives p (Formula.imp u v) hp)
              (proofTree_check_to_compiledQDerives q u hq)
          | eq _ _ => simp [check, hp, hq] at h
          | not _ => simp [check, hp, hq] at h
          | all _ _ => simp [check, hp, hq] at h
  | .gen x p, φ, h => by
      cases hp : check p with
      | none => simp [check, hp] at h
      | some ψ =>
        simp [check, hp] at h
        cases h
        exact CompiledQDerives.gen x
          (proofTree_check_to_compiledQDerives p ψ hp)
  | .spec x t p, φ, h => by
      cases hp : check p with
      | none => simp [check, hp] at h
      | some a =>
        cases a with
        | all y ψ =>
          simp [check, hp] at h
          rcases h with ⟨⟨rfl, ht⟩, rfl⟩
          exact CompiledQDerives.spec x t ht
            (proofTree_check_to_compiledQDerives p (Formula.all x ψ) hp)
        | eq _ _ => simp [check, hp] at h
        | not _ => simp [check, hp] at h
        | imp _ _ => simp [check, hp] at h

/-- Bidirectional derivability equivalence between the explicit compiled-Q
Hilbert relation and the live checker. -/
theorem compiledQDerives_iff_provable (φ : Formula) :
    CompiledQDerives φ ↔ Provable φ := by
  constructor
  · exact compiledQDerives_to_provable
  · rintro ⟨p, hp⟩
    exact proofTree_check_to_compiledQDerives p φ hp

/-- The compiled Robinson-Q axioms are genuine derivation leaves in the
inductive presentation. -/
theorem compiledQ_q1 : CompiledQDerives q1 :=
  CompiledQDerives.ax q1_axiom

/-- The seventh Robinson-Q axiom is also an inductive derivation leaf. -/
theorem compiledQ_q7 : CompiledQDerives q7 :=
  CompiledQDerives.ax (by simp [CompiledQAxiom, isAxiom, q7_is_axiom])

/-! ## Coverage of the arithmetical axiom layer

The seven Robinson-Q axioms are the whole arithmetical layer of the compiled
recognizer: `isQAxiom_iff_mem` states the recognizer accepts a formula exactly
when it is one of the seven, so the arithmetical strength of the fragment is
pinned from both sides.  The logical layer (`isAxK`, `isAxS`, `isAxDNE`,
`isEqRefl`, `isAxId`) stays as declared in `GodelRobinsonQ`, and a general
equality-substitution schema stays outside the fragment. -/

/-- The arithmetical axiom layer of the compiled recognizer, as a list. -/
def qAxioms : List Formula := [q1, q2, q3, q4, q5, q6, q7]

/-- The arithmetical layer has seven members. -/
theorem qAxioms_length : qAxioms.length = 7 := rfl

/-- The arithmetical recognizer accepts a formula exactly when it is one of the
seven Robinson-Q axioms.  Both directions matter: the left-to-right direction
bounds the arithmetical strength of the fragment above, the right-to-left
direction records that every Robinson-Q axiom is present. -/
theorem isQAxiom_iff_mem (φ : Formula) : isQAxiom φ = true ↔ φ ∈ qAxioms := by
  simp [isQAxiom, qAxioms, or_assoc]

/-- Each Robinson-Q axiom is recognized by the full axiom recognizer of the
compiled checker. -/
theorem qAxiom_is_axiom (φ : Formula) (h : φ ∈ qAxioms) : isAxiom φ = true := by
  have hq : isQAxiom φ = true := (isQAxiom_iff_mem φ).mpr h
  simp [isAxiom, hq]

/-- Every Robinson-Q axiom is an inductive derivation leaf of the compiled
fragment.  With `compiledQ_q1` and `compiledQ_q7` this covers the seven. -/
theorem compiledQ_all_q_axioms (φ : Formula) (h : φ ∈ qAxioms) :
    CompiledQDerives φ :=
  CompiledQDerives.ax (qAxiom_is_axiom φ h)

/-- Robinson Q sits inside the live checker: every one of its axioms is
provable by a checked proof tree. -/
theorem robinsonQ_axioms_provable (φ : Formula) (h : φ ∈ qAxioms) : Provable φ :=
  (compiledQDerives_iff_provable φ).mp (compiledQ_all_q_axioms φ h)

/-- The second Robinson-Q axiom as an inductive derivation leaf. -/
theorem compiledQ_q2 : CompiledQDerives q2 :=
  compiledQ_all_q_axioms q2 (by simp [qAxioms])

/-- The third Robinson-Q axiom as an inductive derivation leaf. -/
theorem compiledQ_q3 : CompiledQDerives q3 :=
  compiledQ_all_q_axioms q3 (by simp [qAxioms])

/-- The fourth Robinson-Q axiom as an inductive derivation leaf. -/
theorem compiledQ_q4 : CompiledQDerives q4 :=
  compiledQ_all_q_axioms q4 (by simp [qAxioms])

/-- The fifth Robinson-Q axiom as an inductive derivation leaf. -/
theorem compiledQ_q5 : CompiledQDerives q5 :=
  compiledQ_all_q_axioms q5 (by simp [qAxioms])

/-- The sixth Robinson-Q axiom as an inductive derivation leaf. -/
theorem compiledQ_q6 : CompiledQDerives q6 :=
  compiledQ_all_q_axioms q6 (by simp [qAxioms])

/-- Non-vacuity separator for the arithmetical layer: falsum stays outside it,
so the recognizer of `isQAxiom_iff_mem` rejects at least one formula. -/
theorem falsum_not_mem_qAxioms : falsum ∉ qAxioms := by
  intro h
  have hq : isQAxiom falsum = true := (isQAxiom_iff_mem falsum).mpr h
  rw [falsum_not_q_axiom] at hq
  exact Bool.false_ne_true hq

#check CompiledQAxiom
#check compiledQAxiomDecidable
#check CompiledQDerives
#check compiledQDerives_to_provable
#check proofTree_check_to_compiledQDerives
#check compiledQDerives_iff_provable
#check compiledQ_q1
#check compiledQ_q7
#check qAxioms
#check isQAxiom_iff_mem
#check qAxiom_is_axiom
#check compiledQ_all_q_axioms
#check robinsonQ_axioms_provable
#print axioms compiledQDerives_to_provable
#print axioms proofTree_check_to_compiledQDerives
#print axioms compiledQDerives_iff_provable
#print axioms compiledQ_q1
#print axioms compiledQ_q7
#print axioms qAxioms_length
#print axioms isQAxiom_iff_mem
#print axioms qAxiom_is_axiom
#print axioms compiledQ_all_q_axioms
#print axioms robinsonQ_axioms_provable
#print axioms compiledQ_q2
#print axioms compiledQ_q3
#print axioms compiledQ_q4
#print axioms compiledQ_q5
#print axioms compiledQ_q6
#print axioms falsum_not_mem_qAxioms

end OperatorKO7.Meta.DistinctionBoundary.GodelArith



