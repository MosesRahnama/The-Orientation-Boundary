import OperatorKO7.Meta.BoundaryObserver.PrimrecDefinability
import OperatorKO7.Meta.DistinctionBoundary.TarskiUndefinability

/-!
# Incompleteness of every sound primitive-recursive proof predicate

Manuscript: the last sentence of Theorem `thm:godel-equality-repair` of the Observation-Boundary
Principle.

A proof predicate is given by a Boolean relation `prf` on numbers: `φ` is provable when
`prf n ⌜φ⌝ = true` for some `n`. When `prf` is primitive recursive, Proposition VII
(`definable_of_primrec`) gives a formula `Bew(x)` with `ℕ ⊨ Bew(⌜φ⌝)` exactly when `φ` is provable,
and the diagonal sentence of `¬ Bew` (`general_diagonal`) is true on `ℕ` exactly when it is
unprovable. Soundness then makes it and its negation unprovable.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.SoundExtensionIncompleteness

open OperatorKO7.Meta.DistinctionBoundary.GodelArith
open OperatorKO7.Meta.BoundaryObserver.PrimrecDefinability

/-- Provability through a proof relation on codes. -/
def ProvBy (prf : ℕ → ℕ → Bool) (φ : Formula) : Prop :=
  ∃ n, prf n (encodeFormula φ) = true

/-- The indicator of the proof relation on paired codes. -/
def prfInd (prf : ℕ → ℕ → Bool) (k : ℕ) : ℕ :=
  cond (prf k.unpair.1 k.unpair.2) 1 0

theorem prfInd_primrec {prf : ℕ → ℕ → Bool} (h : Primrec₂ prf) : Nat.Primrec (prfInd prf) := by
  have h1 : Primrec (fun k : ℕ => prf k.unpair.1 k.unpair.2) :=
    h.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
  exact Primrec.nat_iff.1 (Primrec.cond h1 (Primrec.const 1) (Primrec.const 0))

/-- The provability formula with free variable `0`, built from a definition of the indicator at
variables `53` and `54`. -/
def bewForm (φI : Formula) : Formula :=
  existsF 55 (existsF 53 (existsF 54 (andF (PairF 55 0 53)
    (andF φI (Formula.eq (Term.var 54) (Term.succ Term.zero))))))

theorem bewForm_spec {prf : ℕ → ℕ → Bool} {φI : Formula} (hI : DefinesAt (prfInd prf) φI 53 54)
    (env : ℕ → ℕ) : evalForm env (bewForm φI) ↔ ∃ n, prf n (env 0) = true := by
  have hI' : ∀ e, evalForm e φI ↔ prfInd prf (e 53) = e 54 := hI
  simp only [bewForm, eval_ex, eval_andF, hI', eval_eqv, evalTerm,
    eval_PairF _ (show (55 : ℕ) ≠ 51 by decide) (show (0 : ℕ) ≠ 51 by decide)]
  simp (disch := decide) only [upd_same, upd_ne]
  constructor
  · rintro ⟨p, k, o, hk, hio, ho⟩
    refine ⟨p, ?_⟩
    rw [hk, ho] at hio
    simp only [prfInd, Nat.unpair_pair] at hio
    cases hp : prf p (env 0)
    · rw [hp] at hio
      simp at hio
    · rfl
  · rintro ⟨p, hp⟩
    refine ⟨p, Nat.pair p (env 0), 1, rfl, ?_, rfl⟩
    simp [prfInd, Nat.unpair_pair, hp]

/-- **Incompleteness of sound primitive-recursive proof predicates.** The sentence has no free
variable. -/
theorem sound_primrec_incompleteness (prf : ℕ → ℕ → Bool) (hprf : Primrec₂ prf)
    (hsound : ∀ φ, ProvBy prf φ → evalForm env0 φ) :
    ∃ γ : Formula, IsSentence γ ∧ (evalForm env0 γ ↔ ¬ ProvBy prf γ) ∧ ¬ ProvBy prf γ ∧
      ¬ ProvBy prf (Formula.not γ) := by
  obtain ⟨φI, hI⟩ := definable_of_primrec (prfInd_primrec hprf) 53 54 (le_refl _) (by decide)
  refine ⟨diagSentence (Formula.not (bewForm φI)), diagSentence_isSentence _, ?_⟩
  set γ := diagSentence (Formula.not (bewForm φI)) with hγ
  have hfix : evalForm env0 γ ↔ ¬ ProvBy prf γ := by
    rw [general_diagonal, evalForm_substNum, eval_not, bewForm_spec hI]
    simp only [envUpdate, if_true, ProvBy, formulaCode_eq]
    exact Iff.rfl
  have hnp : ¬ ProvBy prf γ := fun hp => (hfix.1 (hsound γ hp)) hp
  refine ⟨hfix, hnp, fun hp => ?_⟩
  exact (hsound _ hp) (hfix.2 hnp)

end OperatorKO7.Meta.BoundaryObserver.SoundExtensionIncompleteness
