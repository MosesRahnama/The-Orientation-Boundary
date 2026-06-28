import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

/-!
# Capture-avoiding de Bruijn substitution for `BoundedFormula Empty n`

Mathlib's `BoundedFormula.subst` substitutes only the *free* variables (the `α` parameter) and
`BoundedFormula.toFormula` frees *all* bound variables; neither instantiates a single de Bruijn bound
variable under binders. This module supplies the missing parallel substitution `substAll` (replace
every bound variable `i : Fin n` by a term `σ i`, with the correct lifting under quantifiers) and its
realization lemma, plus the special case `instantiateTop` (instantiate the outermost bound variable
with a term) needed for the first-order specialization axiom and existential introduction of the
`DeductionFO` object derivation.

No `sorry`, `axiom`, or `native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath.Substitution

open FirstOrder Language BoundedFormula

variable {L : FirstOrder.Language}

/-- Lift a bound-variable substitution under one quantifier: the existing images are widened to make
room for a fresh top variable, which maps to itself. -/
def liftSubst {n m : ℕ} (σ : Fin n → L.Term (Empty ⊕ Fin m)) :
    Fin (n + 1) → L.Term (Empty ⊕ Fin (m + 1)) :=
  Fin.snoc (fun j => (σ j).liftAt 1 m) (Term.var (Sum.inr (Fin.last m)))

/-- Parallel capture-avoiding substitution: replace each bound variable `i : Fin n` of `φ` by the
term `σ i`, lifting `σ` under each quantifier. -/
def substAll : {n m : ℕ} → (Fin n → L.Term (Empty ⊕ Fin m)) → L.BoundedFormula Empty n →
    L.BoundedFormula Empty m
  | _, _, _, falsum => falsum
  | _, _, σ, equal t₁ t₂ =>
      equal (t₁.subst (Sum.elim (fun e => e.elim) σ)) (t₂.subst (Sum.elim (fun e => e.elim) σ))
  | _, _, σ, rel R ts => rel R (fun i => (ts i).subst (Sum.elim (fun e => e.elim) σ))
  | _, _, σ, imp φ ψ => imp (substAll σ φ) (substAll σ ψ)
  | _, _, σ, all φ => all (substAll (liftSubst σ) φ)

/-- **Realization of parallel substitution.** Substituting bound variables by `σ` and then realizing
in `env` is the same as realizing `φ` in the environment that sends bound variable `i` to the value
of `σ i`. The substitution lemma underlying first-order specialization. -/
theorem realize_substAll {M : Type*} [L.Structure M] {n : ℕ} (φ : L.BoundedFormula Empty n) :
    ∀ {m : ℕ} (σ : Fin n → L.Term (Empty ⊕ Fin m)) (env : Fin m → M),
      (substAll σ φ).Realize default env ↔
        φ.Realize default (fun i => (σ i).realize (Sum.elim default env)) := by
  have henv : ∀ {k m' : ℕ} (σ : Fin k → L.Term (Empty ⊕ Fin m')) (env' : Fin m' → M),
      (fun a => ((Sum.elim (fun e : Empty => e.elim) σ) a).realize (Sum.elim (default : Empty → M) env'))
        = Sum.elim (default : Empty → M) (fun i => (σ i).realize (Sum.elim default env')) := by
    intro k m' σ env'; funext a; cases a with
    | inl e => exact e.elim
    | inr i => rfl
  induction φ with
  | falsum => intro m σ env; exact Iff.rfl
  | equal t₁ t₂ =>
      intro m σ env
      simp only [substAll, BoundedFormula.Realize, Term.realize_subst, henv]
  | rel R ts =>
      intro m σ env
      simp only [substAll, BoundedFormula.Realize, Term.realize_subst, henv]
  | imp φ ψ ihφ ihψ =>
      intro m σ env
      simp only [substAll, BoundedFormula.realize_imp, ihφ, ihψ]
  | all φ ih =>
      intro m σ env
      have hbound : ∀ a : M,
          (fun i => ((liftSubst σ) i).realize (Sum.elim (default : Empty → M) (Fin.snoc env a)))
            = Fin.snoc (fun i => (σ i).realize (Sum.elim default env)) a := by
        intro a; funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [liftSubst]
        · have hlift : ((σ j).liftAt 1 m).realize (Sum.elim (default : Empty → M) (Fin.snoc env a))
              = (σ j).realize (Sum.elim default env) := by
            rw [Term.realize_liftAt]
            congr 1
            funext x
            rcases x with e | i
            · rfl
            · simp only [Function.comp_apply, Sum.map_inr, Sum.elim_inr]
              rw [if_pos i.isLt, show Fin.castAdd 1 i = Fin.castSucc i from Fin.ext rfl,
                Fin.snoc_castSucc]
          simp only [liftSubst, Fin.snoc_castSucc]
          exact hlift
      simp only [substAll, BoundedFormula.realize_all, ih, hbound]

/-- Instantiate the outermost (highest-index) bound variable of `φ : BoundedFormula Empty (n+1)`
with a term `t : Term (Empty ⊕ Fin n)`, leaving the remaining `n` bound variables in place. -/
def instantiateTop {n : ℕ} (t : L.Term (Empty ⊕ Fin n)) (φ : L.BoundedFormula Empty (n + 1)) :
    L.BoundedFormula Empty n :=
  substAll (Fin.snoc (fun i => Term.var (Sum.inr i)) t) φ

/-- **Realization of top instantiation.** Instantiating the outermost bound variable with `t` and
realizing in `env` equals realizing `φ` in `env` extended by the value of `t`. This is the semantic
content of the first-order specialization axiom `(∀ φ) → φ[t]`. -/
theorem realize_instantiateTop {M : Type*} [L.Structure M] {n : ℕ}
    (t : L.Term (Empty ⊕ Fin n)) (φ : L.BoundedFormula Empty (n + 1)) (env : Fin n → M) :
    (instantiateTop t φ).Realize default env ↔
      φ.Realize default (Fin.snoc env (t.realize (Sum.elim default env))) := by
  rw [instantiateTop, realize_substAll]
  refine Iff.of_eq (congrArg _ ?_)
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

end OperatorKO7.ReverseMath.Substitution
