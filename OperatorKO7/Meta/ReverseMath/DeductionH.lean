import OperatorKO7.Meta.ReverseMath.DeductionFO

/-!
# Hypothetical derivations and the deduction theorem for `DerivableFO`

A Hilbert calculus cannot directly assume a hypothesis; this module adds the standard
*deduction-theorem* layer on top of `DeductionFO.DerivableFO`. `DerivableH T Γ φ` means "`φ` is
derivable from the local hypotheses `Γ` (a list of open formulas)", encoded as
`DerivableFO T (Γ.foldr (· → ·) φ)`. The deduction theorem (`deduction`) and its inverse
(`assume_intro`) are then *definitional* (up to `List.foldr_append`), and `mp_H`, `lift`, and
`assume_last` give full hypothetical reasoning — the machinery needed to construct the case-branch
implications of the SCT object derivation.

Everything reduces to the propositional core (`ax_k`, `ax_s`, `mp`) of `DerivableFO`, so soundness is
inherited: `DerivableH T [] φ` is `DerivableFO T φ`.

No `sorry`, `axiom`, or `native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath.DeductionH

open FirstOrder Language OperatorKO7.ReverseMath.DeductionFO

variable {L : FirstOrder.Language} {T : L.Theory}

/-! ### Propositional combinators on `DerivableFO` -/

/-- `A → A` (the `I = SKK` combinator). -/
theorem imp_self {n : ℕ} (A : L.BoundedFormula Empty n) : DerivableFO T (A.imp A) :=
  DerivableFO.mp (DerivableFO.mp (DerivableFO.ax_s A (A.imp A) A) (DerivableFO.ax_k A (A.imp A)))
    (DerivableFO.ax_k A A)

/-- Transitivity of implication. -/
theorem imp_trans {n : ℕ} {A B C : L.BoundedFormula Empty n} (h₁ : DerivableFO T (A.imp B))
    (h₂ : DerivableFO T (B.imp C)) : DerivableFO T (A.imp C) :=
  DerivableFO.mp
    (DerivableFO.mp (DerivableFO.ax_s A B C) (DerivableFO.mp (DerivableFO.ax_k (B.imp C) A) h₂)) h₁

/-! ### Hypothetical derivations -/

/-- `φ` is derivable from local hypotheses `Γ`, encoded by chained implication. -/
def DerivableH (T : L.Theory) {n : ℕ} (Γ : List (L.BoundedFormula Empty n))
    (φ : L.BoundedFormula Empty n) : Prop :=
  DerivableFO T (Γ.foldr (·.imp ·) φ)

/-- A closed derivation holds under any hypotheses (weakening by iterated `ax_k`). -/
theorem lift {n : ℕ} {φ : L.BoundedFormula Empty n} (h : DerivableFO T φ) :
    ∀ Γ : List (L.BoundedFormula Empty n), DerivableH T Γ φ
  | [] => h
  | A :: Γ => DerivableFO.mp (DerivableFO.ax_k _ A) (lift h Γ)

/-- The context-`S` combinator: under a context `Γ`, implication distributes (the engine of `mp_H`). -/
theorem S_ctx {n : ℕ} (A B : L.BoundedFormula Empty n) :
    ∀ Γ : List (L.BoundedFormula Empty n),
      DerivableFO T ((Γ.foldr (·.imp ·) (A.imp B)).imp
        ((Γ.foldr (·.imp ·) A).imp (Γ.foldr (·.imp ·) B)))
  | [] => imp_self (A.imp B)
  | G :: Γ =>
      imp_trans
        (DerivableFO.mp (DerivableFO.ax_s G _ _)
          (DerivableFO.mp (DerivableFO.ax_k _ G) (S_ctx A B Γ)))
        (DerivableFO.ax_s G _ _)

/-- Modus ponens under hypotheses. -/
theorem mp_H {n : ℕ} {Γ : List (L.BoundedFormula Empty n)} {A B : L.BoundedFormula Empty n}
    (h₁ : DerivableH T Γ (A.imp B)) (h₂ : DerivableH T Γ A) : DerivableH T Γ B :=
  DerivableFO.mp (DerivableFO.mp (S_ctx A B Γ) h₁) h₂

/-- The most-recently-assumed hypothesis is derivable. -/
theorem assume_last {n : ℕ} (Γ : List (L.BoundedFormula Empty n))
    (A : L.BoundedFormula Empty n) : DerivableH T (Γ ++ [A]) A := by
  unfold DerivableH
  rw [List.foldr_append]
  exact lift (imp_self A) Γ

/-- **Deduction theorem**: discharge the last hypothesis. -/
theorem deduction {n : ℕ} {Γ : List (L.BoundedFormula Empty n)} {A B : L.BoundedFormula Empty n}
    (h : DerivableH T (Γ ++ [A]) B) : DerivableH T Γ (A.imp B) := by
  unfold DerivableH at h ⊢
  rwa [List.foldr_append] at h

/-- Inverse deduction: introduce a hypothesis. -/
theorem assume_intro {n : ℕ} {Γ : List (L.BoundedFormula Empty n)} {A B : L.BoundedFormula Empty n}
    (h : DerivableH T Γ (A.imp B)) : DerivableH T (Γ ++ [A]) B := by
  unfold DerivableH at h ⊢
  rw [List.foldr_append]
  exact h

/-- Lift a closed axiom/theorem of `DerivableFO` into any context (alias of `lift`). -/
theorem ofClosed {n : ℕ} {Γ : List (L.BoundedFormula Empty n)} {φ : L.BoundedFormula Empty n}
    (h : DerivableFO T φ) : DerivableH T Γ φ := lift h Γ

/-- A theory axiom holds under any hypotheses. -/
theorem hyp_H {Γ : List (L.Sentence)} {φ : L.Sentence} (h : φ ∈ T) : DerivableH T Γ φ :=
  lift (DerivableFO.hyp h) Γ

/-! ### Hypothetical-context versions of the connective/quantifier rules -/

variable {n : ℕ} {Γ : List (L.BoundedFormula Empty n)} {A B C : L.BoundedFormula Empty n}

/-- Disjunction introduction (left), hypothetical. -/
theorem or_inl_H (h : DerivableH T Γ A) : DerivableH T Γ (A ⊔ B) :=
  mp_H (lift (DerivableFO.or_inl A B) Γ) h

/-- Disjunction introduction (right), hypothetical. -/
theorem or_inr_H (h : DerivableH T Γ B) : DerivableH T Γ (A ⊔ B) :=
  mp_H (lift (DerivableFO.or_inr A B) Γ) h

/-- Disjunction elimination (case analysis), hypothetical: assume each disjunct in turn. -/
theorem or_elim_H (h : DerivableH T Γ (A ⊔ B)) (ha : DerivableH T (Γ ++ [A]) C)
    (hb : DerivableH T (Γ ++ [B]) C) : DerivableH T Γ C :=
  mp_H (mp_H (mp_H (lift (DerivableFO.or_elim A B C) Γ) h) (deduction ha)) (deduction hb)

/-- Conjunction introduction, hypothetical. -/
theorem and_intro_H (ha : DerivableH T Γ A) (hb : DerivableH T Γ B) : DerivableH T Γ (A ⊓ B) :=
  mp_H (mp_H (lift (DerivableFO.and_intro A B) Γ) ha) hb

/-- Conjunction elimination (left), hypothetical. -/
theorem and_left_H (h : DerivableH T Γ (A ⊓ B)) : DerivableH T Γ A :=
  mp_H (lift (DerivableFO.and_left A B) Γ) h

/-- Conjunction elimination (right), hypothetical. -/
theorem and_right_H (h : DerivableH T Γ (A ⊓ B)) : DerivableH T Γ B :=
  mp_H (lift (DerivableFO.and_right A B) Γ) h

/-- Ex falso, hypothetical. -/
theorem falsum_elim_H (h : DerivableH T Γ (⊥ : L.BoundedFormula Empty n)) : DerivableH T Γ A :=
  mp_H (lift (DerivableFO.falsum_elim A) Γ) h

/-- Excluded middle, hypothetical. -/
theorem em_H (A : L.BoundedFormula Empty n) : DerivableH T Γ (A ⊔ A.not) :=
  lift (DerivableFO.em A) Γ

/-- Existential introduction with a witness term, hypothetical. -/
theorem ex_intro_H {φ : L.BoundedFormula Empty (n + 1)} (t : L.Term (Empty ⊕ Fin n))
    (h : DerivableH T Γ (Substitution.instantiateTop t φ)) : DerivableH T Γ φ.ex :=
  mp_H (lift (DerivableFO.ax_ex_intro t) Γ) h

/-- Existential elimination, hypothetical. -/
theorem ex_elim_H {P : L.BoundedFormula Empty (n + 1)}
    (h₁ : DerivableH T Γ P.ex) (h₂ : DerivableH T Γ (∀' (P.imp (C.liftAt 1 n)))) :
    DerivableH T Γ C :=
  mp_H (mp_H (lift (DerivableFO.ax_ex_elim P C) Γ) h₁) h₂

/-- Weakening: an unused hypothesis can be appended to the end of the context (so any earlier
hypothesis is reachable via `weaken (assume_last …)`). -/
theorem weaken {φ : L.BoundedFormula Empty n} (h : DerivableH T Γ φ) :
    DerivableH T (Γ ++ [A]) φ := by
  have h' : DerivableH T Γ (A.imp φ) := mp_H (lift (DerivableFO.ax_k φ A) Γ) h
  show DerivableFO T ((Γ ++ [A]).foldr (·.imp ·) φ)
  rw [List.foldr_append]
  exact h'

end OperatorKO7.ReverseMath.DeductionH
