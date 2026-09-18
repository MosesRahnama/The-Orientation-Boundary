import OperatorKO7.Meta.DistinctionBoundary.GodelDerivability

set_option autoImplicit false

/-!
# Gödel's first incompleteness theorem

The theorem quantifies over the real `ProofTree` checker and `Provable`.
A sentence true on Nat exactly when unprovable is independent. Falsum is
not such a sentence. The current arithmetized `arithGodelSentence` receives
that theorem only under an explicit fixed-point-semantics premise; the live
`GodelFOEval` stack does not yet discharge that premise. Omega-consistency of
Q is derived from Nat-soundness together with numeral-substitution correctness.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

theorem envUpdate_same (env : Nat → Nat) (x n m : Nat) (z : Nat) :
    envUpdate (envUpdate env x n) x m z = envUpdate env x m z := by
  simp [envUpdate]
  by_cases hz : z = x
  · simp [hz]
  · simp [hz]

theorem envUpdate_comm (env : Nat → Nat) {x y : Nat} (hne : y ≠ x)
    (n m : Nat) (z : Nat) :
    envUpdate (envUpdate env y m) x n z =
      envUpdate (envUpdate env x n) y m z := by
  unfold envUpdate
  by_cases hz : z = x
  · by_cases hy : z = y
    · exact False.elim (hne (hy.symm.trans hz))
    · rw [if_pos hz, if_neg hy, if_pos hz]
  · by_cases hy : z = y
    · rw [if_neg hz, if_pos hy, if_pos hy]
    · rw [if_neg hz, if_neg hy, if_neg hy, if_neg hz]

theorem evalTerm_subst_numeral (env : Nat → Nat) (x n : Nat) (t : Term) :
    evalTerm env (substTerm x (numeral n) t) =
      evalTerm (envUpdate env x n) t := by
  have := evalTerm_subst env x (numeral n) t
  simpa [evalTerm_numeral] using this

theorem evalForm_env_eq (φ : Formula) {env env' : Nat → Nat}
    (h : ∀ z, env z = env' z) :
    evalForm env φ ↔ evalForm env' φ :=
  evalForm_env_eq_aux φ h

theorem evalForm_subst_numeral (env : Nat → Nat) (x n : Nat) (φ : Formula) :
    evalForm env (substForm x (numeral n) φ) ↔
      evalForm (envUpdate env x n) φ := by
  have := evalForm_subst_closed env x (numeral n) (isClosedTerm_numeral n) φ
  simpa [evalTerm_numeral] using this

/-- Gödel's first incompleteness theorem: a sentence equivalent on Nat to
its own unprovability is independent of Q. -/
theorem godel_first_incompleteness
    (G : Formula) (hG : evalForm env0 G ↔ ¬ Provable G) :
    ¬ Provable G ∧ ¬ Provable (Formula.not G) :=
  independence_from_godel_equivalence G hG

/-- Exact missing semantic bridge for the current arithmetized sentence. -/
def ArithGodelFixedPointSemantics : Prop :=
  evalForm env0 arithGodelSentence ↔ ¬ Provable arithGodelSentence

/-- Conditional arithmetic instance.  This theorem does not pretend the live
`proofRel`/`substRel` evaluator has already discharged the fixed point. -/
theorem godel_first_incompleteness_Q
    (hFixed : ArithGodelFixedPointSemantics) :
    ¬ Provable arithGodelSentence ∧ ¬ Provable (Formula.not arithGodelSentence) :=
  godel_first_incompleteness arithGodelSentence hFixed

/-- Representability form: a checker-representing Bew and a fixed point of
`not ∘ Bew` yield independence. -/
theorem godel_first_incompleteness_from_representability
    (Bew : Formula → Formula) (hRep : RepresentsChecker Bew)
    (G : Formula) (hFix : G = Formula.not (Bew G)) :
    ¬ Provable G ∧ ¬ Provable (Formula.not G) :=
  represents_checker_implies_independence Bew hRep G hFix

theorem falsum_not_a_godel_sentence :
    ¬ (evalForm env0 falsum ↔ ¬ Provable falsum) := by
  intro h
  have hf : ¬ evalForm env0 falsum := evalForm_falsum env0
  have hp : ¬ Provable falsum := q_consistent
  exact hf (h.2 hp)

theorem eq_refl_is_provable : Provable (Formula.eq Term.zero Term.zero) :=
  ⟨.ax (Formula.eq Term.zero Term.zero), by
    simp [ValidProof, check, isAxiom, isEqRefl, isQAxiom, isAxK, isAxS, isAxDNE]⟩

/-- Syntactic ω-consistency: a proved existential has some numeral instance
whose negation is unprovable. -/
def OmegaConsistent : Prop :=
  ∀ φ : Formula,
    Provable (existsF 0 φ) →
      ∃ n : Nat, ¬ Provable (Formula.not (substNum φ n))

/-- Semantic witness form used internally to derive syntactic ω-consistency. -/
def SemanticOmegaWitness : Prop :=
  ∀ φ : Formula,
    Provable (existsF 0 φ) →
      ∃ n : Nat, evalForm env0 (substNum φ n)

theorem q_semantic_omega_witness : SemanticOmegaWitness := by
  intro φ hEx
  have ht := provable_sound hEx env0
  dsimp [existsF, evalForm] at ht
  have hex : ¬ ∀ n : Nat,
      ¬ evalForm (fun y => if y = 0 then n else env0 y) φ := by
    simpa [evalForm] using ht
  obtain ⟨n, hn⟩ := Classical.not_forall.mp hex
  have hn' : evalForm (fun y => if y = 0 then n else env0 y) φ :=
    Classical.not_not.mp hn
  have henv : ∀ z, (fun y => if y = 0 then n else env0 y) z = envUpdate env0 0 n z := by
    intro z
    rfl
  refine ⟨n, ?_⟩
  exact (evalForm_substNum env0 n φ).2 ((evalForm_env_eq φ henv).1 hn')

theorem semantic_omega_implies_syntactic (h : SemanticOmegaWitness) :
    OmegaConsistent := by
  intro φ hEx
  rcases h φ hEx with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro hp
  exact (provable_sound hp env0) hn

theorem q_omega_consistent : OmegaConsistent :=
  semantic_omega_implies_syntactic q_semantic_omega_witness

/-- Consistency of Q forbids a formula and its negation both being theorems.
This is the meta-level Rosser explosion, proved from Nat-soundness. The
proof-code order is not required at the meta level; it is required only to
internalize the same argument as a Q-derivation. -/
theorem consistent_not_both {φ : Formula}
    (hp : Provable φ) (hn : Provable (Formula.not φ)) : False := by
  have ht := provable_sound hp env0
  have hnt := provable_sound hn env0
  exact hnt ht

theorem q1_not_rosser_independent :
    ¬ (¬ Provable q1 ∧ ¬ Provable (Formula.not q1)) := by
  intro h
  exact h.1 q1_provable

/-- A dummy identity on `RosserBew` is not a Rosser incompleteness theorem.
The maximal true replacement is `consistent_not_both`. -/
def ProofLt (p q : ProofTree) : Prop :=
  encodeProof p < encodeProof q

theorem proofLt_irrefl (p : ProofTree) : ¬ ProofLt p p :=
  Nat.lt_irrefl _

theorem rosser_order_unused_at_meta {φ : Formula} {p q : ProofTree}
    (hp : check p = some φ) (hq : check q = some (Formula.not φ)) :
    False :=
  consistent_not_both ⟨p, hp⟩ ⟨q, hq⟩

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
