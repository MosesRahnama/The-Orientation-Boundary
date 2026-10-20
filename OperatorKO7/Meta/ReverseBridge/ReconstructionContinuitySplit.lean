import Mathlib

/-!
# Continuity of reversible families on finite and amplitude carriers

On a finite carrier with closed points, finiteness forces the discrete topology
(`Finite.instDiscreteTopology`), and a continuous map from the preconnected line into a discrete
space is constant. Every continuous path of states, and every one-parameter family of reversible
transformations with continuous orbits, is therefore constant (`classical_state_path_frozen`,
`reversible_family_frozen`), and no such family starting at the identity carries a state to a
different state (`no_continuous_swap`).

The two-dimensional real amplitude carrier has a continuous one-parameter group of reversible
maps, the rotation family `rot t` (`rot_zero`, `rot_add`, `rot_reversible`,
`rot_entry_continuous`), and `rot (π/2)` carries `e₀` to `e₁` (`rot_moves_basis`).
`continuity_split` states both results on the concrete carriers `Bool` and `Fin 2 → ℝ`.

Hardy's continuity axiom asks for a continuous reversible transformation between any two pure
states. The first result shows that a finite carrier with closed points admits no such
transformation between distinct states, and the second exhibits one on the amplitude carrier.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ReverseBridge.ReconstructionContinuitySplit

open Real

/-! ## Continuous paths on finite carriers with closed points -/

/-- A continuous map from a preconnected parameter space into a discrete space is constant. -/
theorem continuous_to_discrete_frozen {T P : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    [TopologicalSpace P] [DiscreteTopology P] {f : T → P} (hf : Continuous f) (s t : T) :
    f s = f t :=
  ((IsLocallyConstant.iff_continuous f).mpr hf).apply_eq_of_preconnectedSpace s t

/-- On a finite carrier with closed points, every continuous path of states is constant:
finiteness and closed points force the discrete topology, and a continuous map from the
connected line into a discrete space is constant. -/
theorem classical_state_path_frozen {X : Type*} [TopologicalSpace X] [T1Space X] [Finite X]
    {γ : ℝ → X} (hγ : Continuous γ) (s t : ℝ) : γ s = γ t :=
  continuous_to_discrete_frozen hγ s t

/-- On a finite carrier with closed points, every one-parameter family of reversible
transformations with continuous orbits is constant at every state. -/
theorem reversible_family_frozen {X : Type*} [TopologicalSpace X] [T1Space X] [Finite X]
    {f : ℝ → (X ≃ X)} (hf : ∀ x : X, Continuous fun t => f t x) (t : ℝ) (x : X) :
    f t x = f 0 x :=
  continuous_to_discrete_frozen (hf x) t 0

/-- On a finite carrier with closed points, no one-parameter family of reversible
transformations with continuous orbits that starts at the identity carries a state `x` to a
different state `y`. -/
theorem no_continuous_swap {X : Type*} [TopologicalSpace X] [T1Space X] [Finite X]
    {x y : X} (hxy : x ≠ y) :
    ¬ ∃ f : ℝ → (X ≃ X),
        (∀ z : X, Continuous fun t => f t z) ∧ f 0 = Equiv.refl X ∧ ∃ T : ℝ, f T x = y := by
  rintro ⟨f, hf, h0, T, hT⟩
  have hfrozen : f T x = f 0 x := reversible_family_frozen hf T x
  rw [h0] at hfrozen
  exact hxy (hfrozen.symm.trans hT)

/-- On the carrier `Bool`, no reversible family with continuous orbits carries `false` to
`true`. -/
theorem bool_no_continuous_swap :
    ¬ ∃ f : ℝ → (Bool ≃ Bool),
        (∀ b : Bool, Continuous fun t => f t b) ∧ f 0 = Equiv.refl Bool ∧
          ∃ T : ℝ, f T false = true :=
  no_continuous_swap (by decide)

/-! ## The rotation family on the amplitude carrier -/

/-- The rotation family on the 2-dimensional real amplitude carrier: the canonical continuous
one-parameter reversible group. -/
noncomputable def rot (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]

/-- The family starts at the identity. -/
theorem rot_zero : rot 0 = 1 := by
  unfold rot
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `rot (s + t) = rot s * rot t`: the family is a homomorphism from `(ℝ, +)` into the
reversible maps, by the cosine and sine addition formulas. -/
theorem rot_add (s t : ℝ) : rot (s + t) = rot s * rot t := by
  unfold rot
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

/-- `rot t * rot (-t) = 1`: every member of the family is reversible, with its inverse in the
same family. -/
theorem rot_reversible (t : ℝ) : rot t * rot (-t) = 1 := by
  rw [← rot_add, add_neg_cancel, rot_zero]

/-- Every matrix entry of the family is a continuous function of the parameter. -/
theorem rot_entry_continuous (i j : Fin 2) : Continuous fun t => rot t i j := by
  unfold rot
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-- `rot (π/2)` carries the basis state `e₀` to the basis state `e₁`. -/
theorem rot_moves_basis :
    (rot (Real.pi / 2)).mulVec (Pi.single (0 : Fin 2) (1 : ℝ))
      = Pi.single (1 : Fin 2) (1 : ℝ) := by
  unfold rot
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Real.cos_pi_div_two, Real.sin_pi_div_two]

/-! ## Both results on concrete carriers -/

/-- On the finite carrier `Bool`, every reversible family with continuous orbits is constant,
while the amplitude carrier `Fin 2 → ℝ` has a continuous one-parameter reversible group that
carries `e₀` to `e₁`. -/
theorem continuity_split :
    (∀ f : ℝ → (Bool ≃ Bool), (∀ b : Bool, Continuous fun t => f t b) →
        ∀ (t : ℝ) (b : Bool), f t b = f 0 b)
      ∧ (rot 0 = 1 ∧ (∀ s t : ℝ, rot (s + t) = rot s * rot t)
          ∧ (∀ t : ℝ, rot t * rot (-t) = 1)
          ∧ (∀ i j : Fin 2, Continuous fun t => rot t i j)
          ∧ (rot (Real.pi / 2)).mulVec (Pi.single (0 : Fin 2) (1 : ℝ))
              = Pi.single (1 : Fin 2) (1 : ℝ)) :=
  ⟨fun _ hf t b => reversible_family_frozen hf t b,
    rot_zero, rot_add, rot_reversible, rot_entry_continuous, rot_moves_basis⟩

-- Axiom inventory (must be a subset of `{propext, Classical.choice, Quot.sound}`).
#print axioms continuous_to_discrete_frozen
#print axioms classical_state_path_frozen
#print axioms reversible_family_frozen
#print axioms no_continuous_swap
#print axioms bool_no_continuous_swap
#print axioms rot_zero
#print axioms rot_add
#print axioms rot_reversible
#print axioms rot_entry_continuous
#print axioms rot_moves_basis
#print axioms continuity_split

end OperatorKO7.Meta.ReverseBridge.ReconstructionContinuitySplit
