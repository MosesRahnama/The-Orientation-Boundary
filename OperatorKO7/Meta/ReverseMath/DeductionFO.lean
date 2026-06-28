import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import OperatorKO7.Meta.ReverseMath.Substitution

/-!
# A sound first-order calculus over de Bruijn `BoundedFormula` (generalization-capable)

The propositional `Meta/ReverseMath/Deduction.lean` derives only closed `Sentence`s and so cannot
prove a *universally quantified* theorem (Hilbert generalization needs a free/open variable). This
module upgrades the proof system to operate on `BoundedFormula Empty n` (de Bruijn bound variables),
with the universal-closure reading: `DerivableFO T φ` for `φ : BoundedFormula Empty n` means "`T`
proves `φ` for all values of its `n` open variables". This makes **generalization** (`all_intro`) and
**specialization** (`all_elim`) sound, which is exactly what an object derivation of a `∀∃` sentence
needs.

## Soundness reading

`derivableFO_sound`: if `M ⊨ T` then for every `DerivableFO T φ` and every environment
`env : Fin n → M`, `φ.Realize default env`. At `n = 0` (a `Sentence`) this is the usual `M ⊨ φ`.

Rules: `hyp` (theory axioms), `mp`, classical-propositional `ax_k`/`ax_s`/`ax_dne` (at every level),
`all_intro` (generalization: `φ ⊢ ∀ φ`), `all_elim` (specialization: `∀ φ ⊢ φ`). Each is purely
syntactic and individually sound; instantiation at terms and the equality axioms are the next
constructors to add for the full object derivation.

No `sorry`, `axiom`, `native_decide`, or semantic-premise smuggling.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath.DeductionFO

open FirstOrder Language

variable {L : FirstOrder.Language}

/-- A sound first-order derivability relation over open `BoundedFormula Empty n`, relative to a
theory `T`. `DerivableFO T φ` reads "`T` proves `φ` for all values of its open variables". -/
inductive DerivableFO (T : L.Theory) : {n : ℕ} → L.BoundedFormula Empty n → Prop
  /-- Hypothesis: a sentence of the theory is derivable. -/
  | hyp {φ : L.Sentence} (h : φ ∈ T) : DerivableFO T φ
  /-- Modus ponens (at any level). -/
  | mp {n : ℕ} {φ ψ : L.BoundedFormula Empty n} (h₁ : DerivableFO T (φ.imp ψ))
      (h₂ : DerivableFO T φ) : DerivableFO T ψ
  /-- Hilbert axiom **K** at level `n`. -/
  | ax_k {n : ℕ} (φ ψ : L.BoundedFormula Empty n) : DerivableFO T (φ.imp (ψ.imp φ))
  /-- Hilbert axiom **S** at level `n`. -/
  | ax_s {n : ℕ} (φ ψ χ : L.BoundedFormula Empty n) :
      DerivableFO T ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Classical double-negation elimination at level `n`. -/
  | ax_dne {n : ℕ} (φ : L.BoundedFormula Empty n) : DerivableFO T (φ.not.not.imp φ)
  /-- **Generalization**: if `φ` is derivable (for all values of its open variables) then so is
  `∀ φ`. -/
  | all_intro {n : ℕ} {φ : L.BoundedFormula Empty (n + 1)} (h : DerivableFO T φ) :
      DerivableFO T φ.all
  /-- **Specialization**: if `∀ φ` is derivable then `φ` is derivable (for all values of its open
  variables). -/
  | all_elim {n : ℕ} {φ : L.BoundedFormula Empty (n + 1)} (h : DerivableFO T φ.all) :
      DerivableFO T φ
  /-- **Specialization at a term**: from `∀ φ` derive `φ[t]` (the outermost bound variable
  instantiated by `t`). The first-order specialization axiom in rule form. -/
  | spec {n : ℕ} {φ : L.BoundedFormula Empty (n + 1)} (t : L.Term (Empty ⊕ Fin n))
      (h : DerivableFO T φ.all) : DerivableFO T (Substitution.instantiateTop t φ)
  /-- **Existential introduction**: from a witness instance `φ[t]` derive `∃ φ`. -/
  | ex_intro {n : ℕ} {φ : L.BoundedFormula Empty (n + 1)} (t : L.Term (Empty ⊕ Fin n))
      (h : DerivableFO T (Substitution.instantiateTop t φ)) : DerivableFO T φ.ex
  /-- Equality reflexivity. -/
  | eq_refl {n : ℕ} (t : L.Term (Empty ⊕ Fin n)) : DerivableFO T (t.bdEqual t)
  /-- Leibniz substitution of equals: `s = t → ψ[s] → ψ[t]`. -/
  | eq_leibniz {n : ℕ} (ψ : L.BoundedFormula Empty (n + 1)) (s t : L.Term (Empty ⊕ Fin n)) :
      DerivableFO T ((s.bdEqual t).imp
        ((Substitution.instantiateTop s ψ).imp (Substitution.instantiateTop t ψ)))
  /-- Disjunction introduction (left). -/
  | or_inl {n : ℕ} (A B : L.BoundedFormula Empty n) : DerivableFO T (A.imp (A ⊔ B))
  /-- Disjunction introduction (right). -/
  | or_inr {n : ℕ} (A B : L.BoundedFormula Empty n) : DerivableFO T (B.imp (A ⊔ B))
  /-- Disjunction elimination (case analysis). -/
  | or_elim {n : ℕ} (A B C : L.BoundedFormula Empty n) :
      DerivableFO T ((A ⊔ B).imp ((A.imp C).imp ((B.imp C).imp C)))
  /-- Conjunction introduction. -/
  | and_intro {n : ℕ} (A B : L.BoundedFormula Empty n) : DerivableFO T (A.imp (B.imp (A ⊓ B)))
  /-- Conjunction elimination (left). -/
  | and_left {n : ℕ} (A B : L.BoundedFormula Empty n) : DerivableFO T ((A ⊓ B).imp A)
  /-- Conjunction elimination (right). -/
  | and_right {n : ℕ} (A B : L.BoundedFormula Empty n) : DerivableFO T ((A ⊓ B).imp B)
  /-- Ex falso quodlibet. -/
  | falsum_elim {n : ℕ} (A : L.BoundedFormula Empty n) :
      DerivableFO T ((⊥ : L.BoundedFormula Empty n).imp A)
  /-- Classical excluded middle. -/
  | em {n : ℕ} (A : L.BoundedFormula Empty n) : DerivableFO T (A ⊔ A.not)
  /-- **Existential elimination** (eigenvariable rule): from `∃ φ` and a uniform derivation
  `∀ (φ → C)` with `C` not mentioning the bound variable (encoded by `C.liftAt 1 n`), derive `C`. -/
  | ex_elim {n : ℕ} {P : L.BoundedFormula Empty (n + 1)} {C : L.BoundedFormula Empty n}
      (h₁ : DerivableFO T P.ex) (h₂ : DerivableFO T (∀' (P.imp (C.liftAt 1 n)))) :
      DerivableFO T C
  /-- Existential introduction in axiom (implication) form: `φ[t] → ∃ φ`. -/
  | ax_ex_intro {n : ℕ} {φ : L.BoundedFormula Empty (n + 1)} (t : L.Term (Empty ⊕ Fin n)) :
      DerivableFO T ((Substitution.instantiateTop t φ).imp φ.ex)
  /-- Existential elimination in axiom (implication) form. -/
  | ax_ex_elim {n : ℕ} (P : L.BoundedFormula Empty (n + 1)) (C : L.BoundedFormula Empty n) :
      DerivableFO T (P.ex.imp ((∀' (P.imp (C.liftAt 1 n))).imp C))
  /-- Existential monotonicity: from `∀ (P → Q)` derive `∃ P → ∃ Q`. -/
  | ex_mono {n : ℕ} {P Q : L.BoundedFormula Empty (n + 1)} (h : DerivableFO T (∀' (P.imp Q))) :
      DerivableFO T (P.ex.imp Q.ex)

/-- **Soundness** of `DerivableFO`. If `M ⊨ T`, every derivable open formula is realized under every
environment; at level `0` (a `Sentence`) this is `M ⊨ φ`. Proved by induction; `all_intro`/`all_elim`
use `Fin.snoc`/`Fin.snoc_init_self`. -/
theorem derivableFO_sound {M : Type*} [L.Structure M] [Nonempty M] {T : L.Theory}
    (hT : M ⊨ T) : ∀ {n : ℕ} {φ : L.BoundedFormula Empty n}, DerivableFO T φ →
      ∀ env : Fin n → M, φ.Realize default env := by
  haveI : M ⊨ T := hT
  intro n φ h
  induction h with
  | hyp hmem =>
      intro env
      rw [Subsingleton.elim env (default : Fin 0 → M)]
      exact Theory.realize_sentence_of_mem T hmem
  | mp _ _ ih₁ ih₂ =>
      intro env
      have h₁ := ih₁ env
      rw [BoundedFormula.realize_imp] at h₁
      exact h₁ (ih₂ env)
  | ax_k φ ψ =>
      intro env
      simp only [BoundedFormula.realize_imp]
      intro hφ _
      exact hφ
  | ax_s φ ψ χ =>
      intro env
      simp only [BoundedFormula.realize_imp]
      intro habc hab ha
      exact habc ha (hab ha)
  | ax_dne φ =>
      intro env
      simp only [BoundedFormula.realize_imp, BoundedFormula.realize_not]
      intro hnn
      exact not_not.mp hnn
  | all_intro _ ih =>
      intro env
      rw [BoundedFormula.realize_all]
      intro a
      exact ih (Fin.snoc env a)
  | all_elim _ ih =>
      intro env
      have h₂ := ih (Fin.init env)
      rw [BoundedFormula.realize_all] at h₂
      have h₃ := h₂ (env (Fin.last _))
      rwa [Fin.snoc_init_self] at h₃
  | spec t _ ih =>
      intro env
      rw [Substitution.realize_instantiateTop]
      have h₂ := ih env
      rw [BoundedFormula.realize_all] at h₂
      exact h₂ (t.realize (Sum.elim default env))
  | ex_intro t _ ih =>
      intro env
      rw [BoundedFormula.realize_ex]
      refine ⟨t.realize (Sum.elim default env), ?_⟩
      have h₂ := ih env
      rwa [Substitution.realize_instantiateTop] at h₂
  | eq_refl t => intro env; rfl
  | eq_leibniz ψ s t =>
      intro env
      simp only [BoundedFormula.realize_imp, BoundedFormula.realize_bdEqual,
        Substitution.realize_instantiateTop]
      intro hst hs
      rw [← hst]; exact hs
  | or_inl A B =>
      intro env; simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]; exact Or.inl
  | or_inr A B =>
      intro env; simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]; exact Or.inr
  | or_elim A B C =>
      intro env
      simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
      rintro (ha | hb) hac hbc
      · exact hac ha
      · exact hbc hb
  | and_intro A B =>
      intro env
      simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
      exact fun ha hb => ⟨ha, hb⟩
  | and_left A B =>
      intro env
      simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
      exact And.left
  | and_right A B =>
      intro env
      simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
      exact And.right
  | falsum_elim A =>
      intro env
      simp only [BoundedFormula.realize_imp, BoundedFormula.realize_bot]
      exact False.elim
  | em A =>
      intro env
      simp only [BoundedFormula.realize_sup, BoundedFormula.realize_not]
      exact Classical.em _
  | ex_elim _ _ ih₁ ih₂ =>
      intro env
      have he := ih₁ env
      rw [BoundedFormula.realize_ex] at he
      obtain ⟨a, ha⟩ := he
      have hf := ih₂ env
      rw [BoundedFormula.realize_all] at hf
      have himp := hf a
      rw [BoundedFormula.realize_imp] at himp
      have hc := himp ha
      rw [BoundedFormula.realize_liftAt_one_self, Fin.snoc_comp_castSucc] at hc
      exact hc
  | ax_ex_intro t =>
      intro env
      rw [BoundedFormula.realize_imp, Substitution.realize_instantiateTop]
      intro h
      rw [BoundedFormula.realize_ex]
      exact ⟨t.realize (Sum.elim default env), h⟩
  | ax_ex_elim P C =>
      intro env
      rw [BoundedFormula.realize_imp, BoundedFormula.realize_ex]
      rintro ⟨a, ha⟩
      rw [BoundedFormula.realize_imp, BoundedFormula.realize_all]
      intro hf
      have himp := hf a
      rw [BoundedFormula.realize_imp] at himp
      have hc := himp ha
      rw [BoundedFormula.realize_liftAt_one_self, Fin.snoc_comp_castSucc] at hc
      exact hc
  | ex_mono _ ih =>
      intro env
      rw [BoundedFormula.realize_imp, BoundedFormula.realize_ex, BoundedFormula.realize_ex]
      rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      have hf := ih env
      rw [BoundedFormula.realize_all] at hf
      have himp := hf a
      rw [BoundedFormula.realize_imp] at himp
      exact himp ha

/-- At level `0`, `DerivableFO` of a sentence is sound against `M ⊨ φ` (the usual reading). -/
theorem derivableFO_sound_sentence {M : Type*} [L.Structure M] [Nonempty M] {T : L.Theory}
    (hT : M ⊨ T) {φ : L.Sentence} (h : DerivableFO T φ) : M ⊨ φ :=
  derivableFO_sound hT h default

end OperatorKO7.ReverseMath.DeductionFO
