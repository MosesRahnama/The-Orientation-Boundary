import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite

/-!
# Diagonal-entropy lemma (Informational Incompleteness, Lemma 4.1 / `lem:diagonal`)

Full form of `lem:diagonal`: `H(Δ_m Y) = H(Y)`. The `m`-fold diagonal copy
`Δ_m Y = (Y, …, Y)` is the pushforward of `Y` along the injective diagonal
embedding `diag : α → (Fin m → α)`, with zero mass off the diagonal. This file
proves entropy invariance under ANY injective pushforward (zeros off the image
carry `negMulLog 0 = 0`, the image reindexes by injectivity) and instantiates it
at the diagonal embedding. This is the load-bearing anchor of the
carrier-capacity bound: duplicated payload copies add raw carrier mass but no
independent Shannon information.

## Audit slots

```
Relation: not applicable (finite-alphabet information functional).
Closure:  not applicable.
Trust:    kernel-only; `noncomputable` real-analysis surface only.
Scope:    every injective `e : α → β` and the diagonal embedding.
```
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.InformationalIncompleteness.DiagonalEntropy

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite

/-- Pushforward of a distribution `p : α → ℝ` along `e : α → β`:
`pushforward e p b = ∑ a, [e a = b] p a`. -/
noncomputable def pushforward {α β : Type} [Fintype α] [DecidableEq β]
    (e : α → β) (p : α → ℝ) : β → ℝ :=
  fun b => ∑ a, if e a = b then p a else 0

/--
Proves: for injective `e`, the pushforward at an image point recovers the
  original mass: `pushforward e p (e a) = p a`.
Does not prove: anything about off-image points (those are zero).
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every injective `e` and every `a`.
-/
theorem pushforward_apply_image {α β : Type} [Fintype α] [DecidableEq α]
    [DecidableEq β] (e : α → β) (he : Function.Injective e) (p : α → ℝ) (a : α) :
    pushforward e p (e a) = p a := by
  unfold pushforward
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ ha'
    have : e a' ≠ e a := fun h => ha' (he h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ a) h

/--
Proves: the diagonal-entropy lemma in injective-pushforward form:
  `H (pushforward e p) = H p` for injective `e`. Off-image points contribute
  `negMulLog 0 = 0`; the image reindexes to `α` by injectivity.
Does not prove: anything for non-injective `e` (the conclusion can fail there).
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every injective `e : α → β` and `p : α → ℝ`.
-/
theorem H_pushforward_injective {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α → β) (he : Function.Injective e)
    (p : α → ℝ) : H (pushforward e p) = H p := by
  unfold H
  have hzero : ∀ b ∈ Finset.univ, b ∉ Finset.univ.image e →
      Real.negMulLog (pushforward e p b) = 0 := by
    intro b _ hb
    have hpf : pushforward e p b = 0 := by
      unfold pushforward
      apply Finset.sum_eq_zero
      intro a _
      have hne : e a ≠ b := by
        intro h
        exact hb (Finset.mem_image.2 ⟨a, Finset.mem_univ a, h⟩)
      simp [hne]
    rw [hpf]; simp [Real.negMulLog]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) hzero]
  rw [Finset.sum_image (fun a _ a' _ h => he h)]
  apply Finset.sum_congr rfl
  intro a _
  rw [pushforward_apply_image e he p a]

/-- The `m`-fold diagonal embedding `α → (Fin m → α)`, `a ↦ (a, …, a)`. -/
def diag (α : Type) (m : ℕ) : α → (Fin m → α) := fun a _ => a

/--
Proves: the diagonal embedding is injective when `m ≥ 1`.
Does not prove: injectivity for `m = 0` (where `Fin 0 → α` is a singleton).
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `α` and `m` with `0 < m`.
-/
theorem diag_injective {α : Type} {m : ℕ} (hm : 0 < m) :
    Function.Injective (diag α m) := by
  intro a a' h
  have := congrFun h ⟨0, hm⟩
  simpa [diag] using this

/--
Proves: the diagonal-entropy lemma `lem:diagonal`: `H(Δ_m Y) = H(Y)`. The
  `m`-fold diagonal copy (pushforward along `diag`, `m ≥ 1`) has the same Shannon
  entropy as the original distribution: identical copies add no independent
  information.
Does not prove: the per-step carrier-mass growth (that is `CarrierBurden`); this
  is the orthogonal information statement.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `Fintype α` with `DecidableEq α`, `m ≥ 1`, and `p : α → ℝ`.
-/
theorem diagonal_entropy_eq {α : Type} [Fintype α] [DecidableEq α]
    {m : ℕ} (hm : 0 < m) (p : α → ℝ) :
    H (pushforward (diag α m) p) = H p :=
  H_pushforward_injective (diag α m) (diag_injective hm) p

/-- Audit anchor for the diagonal-entropy lemma. -/
def diagonal_entropy_anchor : String :=
  "OperatorKO7.Meta.InformationalIncompleteness.DiagonalEntropy.diagonal_entropy_eq"

end OperatorKO7.Meta.InformationalIncompleteness.DiagonalEntropy
