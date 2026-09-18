import OperatorKO7.Meta.DistinctionBoundary.GodelArithmetization

set_option autoImplicit false

/-!
# Derivability conditions for the representing checker

D1 packs a checked proof into `Provable` and, at the object-language
layer, into `Bew`. D2 is modus ponens on proof trees. Internal D3 is
the implication `Bew(φ) → Bew(Bew(φ))` as a theorem of the theory; the
meta lift from D1 is `Provable(Bew φ) → Provable(Bew(Bew φ))`. A dummy
constant Bew that is an axiom does not represent the checker.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

theorem derivability_D1 {φ : Formula} (h : Provable φ) :
    ∃ p : ProofTree, check p = some φ :=
  h

theorem derivability_D1_pack {φ : Formula} {p : ProofTree}
    (h : check p = some φ) : Provable φ :=
  ⟨p, h⟩

theorem derivability_D2 {a b : Formula} {p q : ProofTree}
    (hp : check p = some (Formula.imp a b))
    (hq : check q = some a) :
    check (ProofTree.mp p q) = some b := by
  simp [check, hp, hq]

theorem derivability_D2_provable {a b : Formula}
    (himp : Provable (Formula.imp a b)) (ha : Provable a) :
    Provable b := by
  rcases himp with ⟨p, hp⟩
  rcases ha with ⟨q, hq⟩
  exact ⟨ProofTree.mp p q, derivability_D2 hp hq⟩

theorem proof_has_code {φ : Formula} {p : ProofTree}
    (h : check p = some φ) :
    encodeProof p ≠ 0 ∧ check p = some φ :=
  ⟨encodeProof_ne_zero p, h⟩

/-- Meta D3: D1 applied to `Bew φ`. This is not yet the internalized
implication `⊢ Bew(φ) → Bew(Bew(φ))`. -/
theorem derivability_D3_meta
    {Bew : Formula → Formula}
    (hD1 : ∀ ψ : Formula, Provable ψ → Provable (Bew ψ))
    {φ : Formula} (h : Provable (Bew φ)) :
    Provable (Bew (Bew φ)) :=
  hD1 (Bew φ) h

/-- Object-language D3: `⊢ Bew(φ) → Bew(Bew(φ))`. This is the Hilbert-Bernays
internalization that meta D1 does not supply. -/
def InternalD3Missing (Bew : Formula → Formula) : Prop :=
  ∀ φ : Formula, Provable (Formula.imp (Bew φ) (Bew (Bew φ)))

/-- From `⊢ ¬Bew(⊥) → G` and unprovability of `G`, modus ponens forbids
`⊢ ¬Bew(⊥)`. This is the last Hilbert-Bernays step; it does not itself
produce `⊢ ¬Bew(⊥) → G`. -/
theorem internal_D3_implies_G2
    (Bew : Formula → Formula)
    (G : Formula)
    (hD2 : ∀ a b : Formula, Provable (Formula.imp a b) → Provable a → Provable b)
    (hImp : Provable (Formula.imp (Formula.not (Bew falsum)) G))
    (hUnpr : ¬ Provable G) :
    ¬ Provable (Formula.not (Bew falsum)) := by
  intro hC
  exact hUnpr (hD2 (Formula.not (Bew falsum)) G hImp hC)

def RepresentsChecker (Bew : Formula → Formula) : Prop :=
  ∀ φ : Formula, evalForm env0 (Bew φ) ↔ Provable φ

theorem eq_refl_bew_does_not_represent :
    ¬ RepresentsChecker (fun _ => Formula.eq Term.zero Term.zero) := by
  intro h
  have hTrue : evalForm env0 (Formula.eq Term.zero Term.zero) := by
    dsimp [evalForm, evalTerm]
  have hP : Provable (Formula.eq Term.zero (Term.succ Term.zero)) :=
    (h (Formula.eq Term.zero (Term.succ Term.zero))).1 hTrue
  have hSound := provable_sound hP env0
  exact Nat.zero_ne_add_one 0 hSound

/-- The constant theorem `0=0` is object-language D3, because identity
implications are axioms, but it does not represent the proof checker. -/
theorem internal_D3_not_forced :
    ¬ RepresentsChecker (fun _ => Formula.eq Term.zero Term.zero) ∧
      InternalD3Missing (fun _ => Formula.eq Term.zero Term.zero) := by
  refine ⟨eq_refl_bew_does_not_represent, ?_⟩
  intro φ
  exact ⟨ProofTree.ax (Formula.imp
      (Formula.eq Term.zero Term.zero)
      (Formula.eq Term.zero Term.zero)), by
    simp [ValidProof, check, isAxiom, isAxId, isEqRefl, isQAxiom, isAxK, isAxS,
      isAxDNE]⟩

/-- Soundness plus a Nat-equivalence with unprovability yields independence. -/
theorem independence_from_godel_equivalence
    (G : Formula) (hG : evalForm env0 G ↔ ¬ Provable G) :
    ¬ Provable G ∧ ¬ Provable (Formula.not G) := by
  constructor
  · intro hP
    have hTrue : evalForm env0 G := provable_sound hP env0
    exact (hG.1 hTrue) hP
  · intro hN
    have hNot : evalForm env0 (Formula.not G) := provable_sound hN env0
    have hFalse : ¬ evalForm env0 G := by
      simpa [evalForm] using hNot
    have hNP : ¬ Provable G := fun hP => hFalse (provable_sound hP env0)
    exact hFalse (hG.2 hNP)

/-- A representing checker and a syntactic fixed point `G = ¬Bew(G)`
give the Gödel equivalence on Nat, hence independence. -/
theorem represents_checker_implies_independence
    (Bew : Formula → Formula) (hRep : RepresentsChecker Bew)
    (G : Formula) (hFix : G = Formula.not (Bew G)) :
    ¬ Provable G ∧ ¬ Provable (Formula.not G) := by
  apply independence_from_godel_equivalence G
  constructor
  · intro hTrue hP
    have hB : evalForm env0 (Bew G) := (hRep G).2 hP
    have hNG : evalForm env0 (Formula.not (Bew G)) := by
      rw [← hFix]
      exact hTrue
    exact hNG hB
  · intro hNP
    rw [hFix]
    intro hB
    exact hNP ((hRep G).1 hB)

/-- Object-language D1 at codes: a checked proof yields a proof-code
witness for `isProofCode`. -/
theorem derivability_D1_object {φ : Formula} (h : Provable φ) :
    ∃ n : Nat, isProofCode n (formulaCode φ) = true :=
  isProofCode_of_provable h

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
