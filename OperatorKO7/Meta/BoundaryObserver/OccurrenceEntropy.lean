import OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy
import OperatorKO7.Meta.BoundaryObserver.RecursorDecidability

set_option autoImplicit false

/-!
# The entropy of an occurrence splits into content and place

The paragraph after `prop:complement` of the Observation-Boundary Principle (ledger row 09-016).
An occurrence is a pair `(c, p)` of a content in `Y` and a place in `R`; the pair map is injective
(`PlaceCoordinates.content_place_injective`), so a law of occurrences is the joint law of content
and place. Presented by content weights `λ` and place conditionals `κ y`, the occurrence law
`λ y · κ y r` has entropy `H(λ) + Σ_y λ y H(κ y)`: the chain rule
`ConditionalEntropy.entropy_chain_rule` on the occurrence carrier `Y × R` with the content and place
projections. At the `i`th term of the recursor reduction the `i + 1` copies of the step argument `b`
form one content fiber; under the uniform place law the place term is `log (i + 1)`, the entropy the
content observer leaves on `i + 1` passes (`RecursorDecidability.content_leaves_log`), so the
occurrence carries `H(b) + log₂ (i + 1)` bits.

Relation: none. Entropies in nats; the bit form divides by `log 2`. Trust: kernel-only. No `sorry`,
`admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.OccurrenceEntropy

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy

open scoped BigOperators

/-- The occurrence law on `Y × R` (content first) with content weights `lam` and place
conditionals `kap`. -/
def occLaw {Y R : Type} (lam : Y → ℝ) (kap : Y → R → ℝ) : Y × R → ℝ :=
  fun o => lam o.1 * kap o.1 o.2

/-- Unfolding lemma of `occLaw`. -/
theorem occLaw_apply {Y R : Type} (lam : Y → ℝ) (kap : Y → R → ℝ) (y : Y) (r : R) :
    occLaw lam kap (y, r) = lam y * kap y r := rfl

/-- The content marginal of the occurrence law is the content law when every place conditional
is normalized. -/
theorem occLaw_content_marginal {Y R : Type} [Fintype R] (lam : Y → ℝ) (kap : Y → R → ℝ)
    (hk : ∀ y, ∑ r, kap y r = 1) (y : Y) :
    ∑ r, occLaw lam kap (y, r) = lam y := by
  simp only [occLaw_apply, ← Finset.mul_sum, hk y, mul_one]

/--
Proves: `H(occurrence) = H(content) + H(place | content)`: the entropy of the occurrence law with
content weights `lam` and normalized place conditionals `kap` is `H lam + condEntropy lam kap`.
Scope: paragraph after `prop:complement`; row 09-016. Entropies in nats.
Trust: kernel-only.
-/
theorem occurrence_entropy_chain_rule {Y R : Type} [Fintype Y] [Fintype R]
    (lam : Y → ℝ) (kap : Y → R → ℝ) (hk : ∀ y, ∑ r, kap y r = 1) :
    H (occLaw lam kap) = H lam + condEntropy lam kap := by
  have hrel : H (fun o : Y × R => jointDist lam kap ((Equiv.prodComm R Y).symm o)) =
      H (jointDist lam kap) :=
    H_relabel_eq (Equiv.prodComm R Y) (jointDist lam kap)
  have hfun : (fun o : Y × R => jointDist lam kap ((Equiv.prodComm R Y).symm o)) =
      occLaw lam kap := by
    funext o
    rfl
  rw [hfun] at hrel
  rw [hrel]
  exact entropy_chain_rule lam kap hk

/-- The uniform place law on `i + 1` places. -/
noncomputable def uniformPlace {Y : Type} (i : ℕ) : Y → Fin (i + 1) → ℝ :=
  fun _ _ => 1 / ((i : ℝ) + 1)

/-- The uniform place law is normalized. -/
theorem uniformPlace_total {Y : Type} (i : ℕ) (y : Y) :
    ∑ r : Fin (i + 1), uniformPlace (Y := Y) i y r = 1 := by
  simp only [uniformPlace, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h : ((i : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-- The uniform law on `i + 1` places has entropy `log (i + 1)`. -/
theorem H_uniformPlace {Y : Type} (i : ℕ) (y : Y) :
    H (uniformPlace (Y := Y) i y) = Real.log ((i : ℝ) + 1) := by
  unfold H uniformPlace
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hne : (i : ℝ) + 1 ≠ 0 := ne_of_gt hpos
  have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  unfold Real.negMulLog
  rw [hcast, one_div, Real.log_inv]
  have hx : ((i : ℝ) + 1) * ((i : ℝ) + 1)⁻¹ = 1 := mul_inv_cancel₀ hne
  calc ((i : ℝ) + 1) * (-((i : ℝ) + 1)⁻¹ * -Real.log ((i : ℝ) + 1))
      = (((i : ℝ) + 1) * ((i : ℝ) + 1)⁻¹) * Real.log ((i : ℝ) + 1) := by ring
    _ = Real.log ((i : ℝ) + 1) := by rw [hx, one_mul]

/--
Proves: with the uniform place law on `i + 1` copies, the place term `H(place | content)` equals
`log (i + 1)`, the entropy the content observer leaves on `i + 1` passes
(`RecursorDecidability.content_leaves_log`).
Scope: row 09-016; `prop:counter-cost` (ii). Trust: kernel-only.
-/
theorem condEntropy_uniformPlace {Y : Type} [Fintype Y] (b : Y → ℝ) (hb : ∑ y, b y = 1)
    (i : ℕ) :
    condEntropy b (uniformPlace i) = Real.log ((i : ℝ) + 1) ∧
      condEntropy b (uniformPlace i) =
        RecursorDecidability.leftEntropy (fun _ : Fin (i + 1) => ()) := by
  have h1 : condEntropy b (uniformPlace i) = Real.log ((i : ℝ) + 1) := by
    unfold condEntropy
    simp only [H_uniformPlace, ← Finset.sum_mul, hb, one_mul]
  refine ⟨h1, ?_⟩
  rw [h1, RecursorDecidability.content_leaves_log]

/--
The copy instance.

Proves: for a content law `b` and the uniform place law on the `i + 1` copies, the occurrence law
has entropy `H(b) + log (i + 1)` in nats, and `H(b)/log 2 + log₂ (i + 1)` in bits.
Scope: the paragraph after `prop:complement`; row 09-016. Trust: kernel-only.
-/
theorem copy_occurrence_entropy {Y : Type} [Fintype Y] (b : Y → ℝ) (hb : ∑ y, b y = 1)
    (i : ℕ) :
    H (occLaw b (uniformPlace i)) = H b + Real.log ((i : ℝ) + 1) ∧
      H (occLaw b (uniformPlace i)) / Real.log 2 =
        H b / Real.log 2 + Real.logb 2 ((i : ℝ) + 1) := by
  have hchain := occurrence_entropy_chain_rule b (uniformPlace i) (uniformPlace_total i)
  rw [(condEntropy_uniformPlace b hb i).1] at hchain
  refine ⟨hchain, ?_⟩
  rw [hchain, add_div, Real.logb]

/-- Non-vacuity: one content of mass one and two copies give `log 2`, one bit. -/
example : H (occLaw (fun _ : Unit => (1 : ℝ)) (uniformPlace 1)) = Real.log 2 := by
  have h := (copy_occurrence_entropy (fun _ : Unit => (1 : ℝ)) (by simp) 1).1
  rw [h]
  have h0 : H (fun _ : Unit => (1 : ℝ)) = 0 := by simp [H]
  rw [h0]
  norm_num

end OperatorKO7.Meta.BoundaryObserver.OccurrenceEntropy
