import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Dicke basis and symmetric-sector dimension

This module formalizes manuscript definition `def:dicke-basis` and proposition
`prop:sym-logical-dim` on the actual `n`-qubit Hilbert space
`EuclideanSpace ℂ (Fin n → Bool)`.

## Architecture

`QubitRegister n` is the `n`-qubit Hilbert space carrier (bitstring index set
`Fin n → Bool`). `dickeState n w` is the Hamming-weight-`w` Dicke
superposition on this carrier — the actual manuscript object,
$\ket{D_w^n} = (1/\sqrt{\binom{n}{w}}) \sum_{|x|=w} \ket{x}$.
`SymmetricSpan n` is the submodule spanned by `{dickeState n w}_w`; this is
the symmetric subspace of the manuscript.

The coordinate-model alias `SymmetricSubspace n := EuclideanSpace ℂ (Fin (n+1))`
and the standard basis vectors `dickeBasisVector n w := EuclideanSpace.single w 1`
are retained as the coordinate model for the spectrum statement.
The unitary isomorphism `dickeIso n : SymmetricSpan n ≃ₗᵢ[ℂ] SymmetricSubspace n`
(built from the orthonormal family `dickeState n`) is the bridge that ports
the spectrum statement on the coordinate carrier back to the actual symmetric
subspace of `n` qubits.

## Manuscript labels mechanized here

* `def:dicke-basis`      -> `dickeState`
* `prop:sym-logical-dim` -> `dim_symmetricSpan_eq_succ`
                            (legacy coordinate variant: `dim_eq_succ`)
-/

namespace QEC.Dicke.Basis

open scoped BigOperators
open Finset

/-- Manuscript label `def:dicke-basis`.

`QubitRegister n` is the `n`-qubit Hilbert space, identified with the
`L²` space indexed by computational-basis bitstrings `Fin n → Bool`. -/
abbrev QubitRegister (n : ℕ) : Type := EuclideanSpace ℂ (Fin n → Bool)

/-- Manuscript label `def:dicke-basis`.

`hammingWeight n x` is the number of indices where the bitstring `x` is `true`. -/
def hammingWeight (n : ℕ) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i = true)).card

/-- Manuscript label `def:dicke-basis`.

`hammingOrbit n w` is the Finset of length-`n` bitstrings with Hamming
weight `w`. -/
def hammingOrbit (n : ℕ) (w : Fin (n + 1)) : Finset (Fin n → Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).filter (fun x => hammingWeight n x = w.1)

private def indicatorOfFinset {n : ℕ} (s : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ s)

private def supportFinset {n : ℕ} (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i = true)

private theorem hammingWeight_indicatorOfFinset {n : ℕ} (s : Finset (Fin n)) :
    hammingWeight n (indicatorOfFinset s) = s.card := by
  unfold hammingWeight indicatorOfFinset
  congr 1
  apply Finset.ext
  intro i
  simp

private theorem indicatorOfFinset_injective (n : ℕ) :
    Function.Injective (indicatorOfFinset (n := n)) := by
  intro s t h
  ext i
  have hcong := congrArg (fun x : Fin n → Bool => x i) h
  simp [indicatorOfFinset] at hcong
  exact hcong

private theorem indicatorOfFinset_supportFinset {n : ℕ} (x : Fin n → Bool) :
    indicatorOfFinset (supportFinset x) = x := by
  funext i
  by_cases h : x i = true
  · simp [indicatorOfFinset, supportFinset, h]
  · have hf : x i = false := by cases hxi : x i <;> simp_all
    simp [indicatorOfFinset, supportFinset, hf]

/-- The number of bitstrings of length `n` with Hamming weight `w.1` equals
`Nat.choose n w.1`. -/
theorem card_hammingOrbit (n : ℕ) (w : Fin (n + 1)) :
    (hammingOrbit n w).card = Nat.choose n w.1 := by
  classical
  have hbij :
      hammingOrbit n w =
        ((Finset.univ : Finset (Fin n)).powersetCard w.1).image
          (fun s : Finset (Fin n) => indicatorOfFinset s) := by
    apply Finset.ext
    intro x
    simp only [hammingOrbit, mem_filter, mem_image, mem_powersetCard,
      mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · intro hw
      refine ⟨supportFinset x, ⟨Finset.subset_univ _, ?_⟩,
        indicatorOfFinset_supportFinset x⟩
      simpa [supportFinset, hammingWeight] using hw
    · rintro ⟨s, ⟨_, hcard⟩, hsx⟩
      subst hsx
      rw [hammingWeight_indicatorOfFinset]
      exact hcard
  rw [hbij,
    Finset.card_image_of_injective _ (indicatorOfFinset_injective n),
    Finset.card_powersetCard]
  simp

/-- `Nat.choose n w.1` is positive for `w : Fin (n+1)`. -/
private theorem choose_pos_of_fin {n : ℕ} (w : Fin (n + 1)) :
    0 < Nat.choose n w.1 :=
  Nat.choose_pos (Nat.lt_succ_iff.mp w.2)

/-- The Hamming-weight orbit is nonempty for any `w : Fin (n+1)`. -/
private theorem hammingOrbit_nonempty (n : ℕ) (w : Fin (n + 1)) :
    (hammingOrbit n w).Nonempty := by
  rw [← Finset.card_pos, card_hammingOrbit]
  exact choose_pos_of_fin w

/-- The Hamming weight of any element of `hammingOrbit n w` is `w.1`. -/
private theorem hammingWeight_of_mem_orbit {n : ℕ} {w : Fin (n + 1)}
    {x : Fin n → Bool} (hx : x ∈ hammingOrbit n w) :
    hammingWeight n x = w.1 := by
  simpa [hammingOrbit] using (Finset.mem_filter.mp hx).2

/-- Distinct Hamming-weight orbits are disjoint. -/
private theorem hammingOrbit_disjoint {n : ℕ} {w w' : Fin (n + 1)} (h : w ≠ w') :
    Disjoint (hammingOrbit n w) (hammingOrbit n w') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  have hw : hammingWeight n x = w.1 := hammingWeight_of_mem_orbit hx
  have hw' : hammingWeight n x = w'.1 := hammingWeight_of_mem_orbit hx'
  exact h (Fin.ext (hw.symm.trans hw'))

/-- Manuscript label `def:dicke-basis`.

`dickeState n w` is the Hamming-weight-`w` Dicke state on `n` qubits:
$\ket{D_w^n} = (1/\sqrt{\binom{n}{w}}) \sum_{|x|=w} \ket{x}$. -/
noncomputable def dickeState (n : ℕ) (w : Fin (n + 1)) : QubitRegister n :=
  ((Real.sqrt (Nat.choose n w.1 : ℝ))⁻¹ : ℂ) •
    ∑ x ∈ hammingOrbit n w, EuclideanSpace.single x (1 : ℂ)

/-- Manuscript label `def:dicke-basis` (coordinate model).

`SymmetricSubspace n` is the `(n+1)`-dimensional coordinate carrier used by
the spectrum theorem in `Ladders.lean`. The unitary isomorphism `dickeIso`
below identifies it with the concrete `SymmetricSpan`. -/
abbrev SymmetricSubspace (n : ℕ) : Type := EuclideanSpace ℂ (Fin (n + 1))

/-- Manuscript label `def:dicke-basis` (coordinate model).

`dickeBasisVector n w` is the `w`-th standard basis vector of the
coordinate carrier `SymmetricSubspace n`. -/
noncomputable def dickeBasisVector (n : ℕ) (w : Fin (n + 1)) :
    SymmetricSubspace n :=
  EuclideanSpace.single w (1 : ℂ)

/-- `CoordinateSpace n` is an alias for `SymmetricSubspace n`, exposing the
abstract `Fin (n+1)`-indexed Hilbert-space carrier used by the spectrum
theorem in `Ladders.lean`. -/
abbrev CoordinateSpace (n : ℕ) : Type := SymmetricSubspace n

/-- Inner product of two single-basis vectors in `QubitRegister n`. -/
private theorem inner_single_single_self {n : ℕ} (x : Fin n → Bool) :
    @inner ℂ _ _ (EuclideanSpace.single x (1 : ℂ))
        (EuclideanSpace.single x (1 : ℂ)) = (1 : ℂ) := by
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  simp

private theorem inner_single_single_of_ne {n : ℕ} {x y : Fin n → Bool}
    (h : y ≠ x) :
    @inner ℂ _ _ (EuclideanSpace.single x (1 : ℂ))
        (EuclideanSpace.single y (1 : ℂ)) = (0 : ℂ) := by
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  have : ¬ x = y := fun hxy => h hxy.symm
  simp [this]

/-- The squared root of `n.choose w.1` is nonzero (as a real). -/
private theorem sqrt_choose_ne_zero {n : ℕ} (w : Fin (n + 1)) :
    Real.sqrt (Nat.choose n w.1 : ℝ) ≠ 0 := by
  have hpos : (0 : ℝ) < (Nat.choose n w.1 : ℝ) := by
    exact_mod_cast choose_pos_of_fin w
  exact (Real.sqrt_pos.mpr hpos).ne'

/-- `(√C(n,w))² = C(n,w)` as a real. -/
private theorem sq_sqrt_choose {n : ℕ} (w : Fin (n + 1)) :
    Real.sqrt (Nat.choose n w.1 : ℝ) * Real.sqrt (Nat.choose n w.1 : ℝ) =
      (Nat.choose n w.1 : ℝ) :=
  Real.mul_self_sqrt (by exact_mod_cast (Nat.zero_le _))

/-- Inner product of `dickeState`s on `QubitRegister n`. -/
private theorem inner_dickeState_eq (n : ℕ) (w w' : Fin (n + 1)) :
    @inner ℂ _ _ (dickeState n w) (dickeState n w') = if w = w' then 1 else 0 := by
  classical
  unfold dickeState
  rw [inner_smul_left, inner_smul_right, sum_inner]
  -- For each x in orbit(w), compute the inner product with the sum.
  have heach : ∀ x ∈ hammingOrbit n w,
      @inner ℂ _ _ (EuclideanSpace.single x (1 : ℂ))
        (∑ y ∈ hammingOrbit n w', EuclideanSpace.single y (1 : ℂ)) =
      if w = w' then (1 : ℂ) else 0 := by
    intro x hx
    rw [inner_sum]
    by_cases hww : w = w'
    · subst hww
      simp only [if_true]
      rw [Finset.sum_eq_single x]
      · exact inner_single_single_self x
      · intro y _ hyx
        exact inner_single_single_of_ne hyx
      · intro hxnot; exact (hxnot hx).elim
    · simp only [hww, if_false]
      apply Finset.sum_eq_zero
      intro y hy
      by_cases hyx : y = x
      · subst hyx
        have hdis := hammingOrbit_disjoint hww
        rw [Finset.disjoint_left] at hdis
        exact (hdis hx hy).elim
      · exact inner_single_single_of_ne hyx
  rw [Finset.sum_congr rfl heach, Finset.sum_const]
  rw [show (hammingOrbit n w).card = Nat.choose n w.1 from card_hammingOrbit n w]
  -- Combine scalars.
  by_cases hww : w = w'
  · subst hww
    simp only [if_true]
    have hC_real : (Nat.choose n w.1 : ℝ) ≠ 0 :=
      (by exact_mod_cast (choose_pos_of_fin w).ne' : (Nat.choose n w.1 : ℝ) ≠ 0)
    have hne : Real.sqrt (Nat.choose n w.1 : ℝ) ≠ 0 := sqrt_choose_ne_zero w
    have hsq : Real.sqrt (Nat.choose n w.1 : ℝ) *
        Real.sqrt (Nat.choose n w.1 : ℝ) = (Nat.choose n w.1 : ℝ) := sq_sqrt_choose w
    -- LHS shape:
    -- ((↑(Real.sqrt _)⁻¹ : ℂ))† * (((↑(Real.sqrt _)⁻¹ : ℂ)) * (C(n,w) • 1))
    -- where the • on ℂ comes from `Finset.sum_const`.
    -- Conjugation of a real-cast inverse is itself.
    rw [show
        (starRingEnd ℂ) ((Real.sqrt (Nat.choose n w.1 : ℝ))⁻¹ : ℂ) =
          ((Real.sqrt (Nat.choose n w.1 : ℝ))⁻¹ : ℂ) from by
          rw [map_inv₀, Complex.conj_ofReal]]
    rw [nsmul_eq_mul, mul_one]
    -- Goal: r⁻¹ * (r⁻¹ * ↑C) = 1, where r = √C and r * r = C.
    have hrne : ((Real.sqrt (Nat.choose n w.1 : ℝ)) : ℂ) ≠ 0 := by
      exact_mod_cast hne
    have hrsq : ((Real.sqrt (Nat.choose n w.1 : ℝ)) : ℂ) *
        ((Real.sqrt (Nat.choose n w.1 : ℝ)) : ℂ) =
        ((Nat.choose n w.1 : ℂ)) := by
      rw [← Complex.ofReal_mul, hsq]; push_cast; rfl
    -- Goal: r⁻¹ * (r⁻¹ * ↑C) = 1 with r = √C and r² = ↑C.
    rw [show ((Nat.choose n w.1 : ℂ)) =
        ((Real.sqrt (Nat.choose n w.1 : ℝ)) : ℂ) *
          ((Real.sqrt (Nat.choose n w.1 : ℝ)) : ℂ) from hrsq.symm]
    field_simp
  · simp [hww]

/-- Manuscript label `def:dicke-basis`.

The Dicke states form an orthonormal family on `QubitRegister n`. -/
theorem dickeState_orthonormal (n : ℕ) :
    Orthonormal ℂ (dickeState n) := by
  rw [orthonormal_iff_ite]
  intro w w'
  exact inner_dickeState_eq n w w'

/-- Manuscript label `def:dicke-basis`.

The Dicke-coordinate vectors form an orthonormal family. -/
theorem dickeBasis_orthonormal (n : ℕ) :
    Orthonormal ℂ (dickeBasisVector n) := by
  simpa [dickeBasisVector] using
    (EuclideanSpace.orthonormal_single :
      Orthonormal ℂ (fun i : Fin (n + 1) => EuclideanSpace.single i (1 : ℂ)))

/-- Manuscript label `prop:sym-logical-dim` (coordinate model).

The Dicke-coordinate symmetric carrier has dimension `n + 1`. -/
theorem dim_eq_succ (n : ℕ) :
    Module.finrank ℂ (SymmetricSubspace n) = n + 1 := by
  simp [SymmetricSubspace]

/-- Manuscript label `def:dicke-basis`.

`SymmetricSpan n` is the symmetric subspace of `QubitRegister n`,
defined as the span of the Dicke states. -/
noncomputable def SymmetricSpan (n : ℕ) : Submodule ℂ (QubitRegister n) :=
  Submodule.span ℂ (Set.range (dickeState n))

/-- The Dicke states are linearly independent. -/
private theorem dickeState_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (dickeState n) :=
  (dickeState_orthonormal n).linearIndependent

/-- Manuscript label `prop:sym-logical-dim`.

The symmetric subspace of `n` qubits has dimension `n + 1`. -/
theorem dim_symmetricSpan_eq_succ (n : ℕ) :
    Module.finrank ℂ (SymmetricSpan n) = n + 1 := by
  classical
  rw [SymmetricSpan, finrank_span_eq_card (dickeState_linearIndependent n)]
  simp

/-- Manuscript label `def:dicke-basis`.

The Dicke state, viewed as an element of `SymmetricSpan n`. -/
noncomputable def dickeFamilyInSpan (n : ℕ) (w : Fin (n + 1)) : SymmetricSpan n :=
  ⟨dickeState n w, Submodule.subset_span (Set.mem_range_self w)⟩

/-- The lifted Dicke family is orthonormal in the symmetric subspace. -/
private theorem dickeFamilyInSpan_orthonormal (n : ℕ) :
    Orthonormal ℂ (dickeFamilyInSpan n) := by
  -- Inner product on a submodule is the restriction of the ambient inner product.
  rw [orthonormal_iff_ite]
  intro w w'
  -- The inner product on the submodule coincides with the inner product of
  -- the underlying vectors.
  exact (orthonormal_iff_ite.mp (dickeState_orthonormal n)) w w'

/-- The lifted Dicke family is linearly independent in the symmetric subspace. -/
private theorem dickeFamilyInSpan_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (dickeFamilyInSpan n) :=
  (dickeFamilyInSpan_orthonormal n).linearIndependent

private instance finiteDimensional_symmetricSpan (n : ℕ) :
    FiniteDimensional ℂ (SymmetricSpan n) := by
  apply FiniteDimensional.of_finrank_pos
  rw [dim_symmetricSpan_eq_succ]
  exact Nat.succ_pos n

/-- The lifted Dicke family spans the symmetric subspace (i.e. forms a basis). -/
private theorem dickeFamilyInSpan_span_eq_top (n : ℕ) :
    Submodule.span ℂ (Set.range (dickeFamilyInSpan n)) = ⊤ := by
  apply LinearIndependent.span_eq_top_of_card_eq_finrank
    (dickeFamilyInSpan_linearIndependent n)
  rw [dim_symmetricSpan_eq_succ]
  simp

/-- Orthonormal basis of `SymmetricSpan n` indexed by Hamming weights. -/
noncomputable def dickeONB (n : ℕ) :
    OrthonormalBasis (Fin (n + 1)) ℂ (SymmetricSpan n) :=
  OrthonormalBasis.mk (dickeFamilyInSpan_orthonormal n)
    (le_of_eq (dickeFamilyInSpan_span_eq_top n).symm)

/-- Manuscript label `def:dicke-basis`.

The orthonormal basis `dickeONB` sends weight `w` to `dickeFamilyInSpan n w`. -/
@[simp] theorem dickeONB_apply (n : ℕ) (w : Fin (n + 1)) :
    dickeONB n w = dickeFamilyInSpan n w := by
  unfold dickeONB
  rw [OrthonormalBasis.coe_mk]

/-- Manuscript label `def:dicke-basis`.

`dickeIso n` is the canonical unitary isomorphism between the real symmetric
subspace `SymmetricSpan n` (a submodule of `QubitRegister n`) and the abstract
coordinate carrier `SymmetricSubspace n = EuclideanSpace ℂ (Fin (n+1))`. The
isomorphism ports the spectrum statement on the coordinate carrier back to
the actual symmetric subspace of `n` qubits. -/
noncomputable def dickeIso (n : ℕ) :
    SymmetricSpan n ≃ₗᵢ[ℂ] SymmetricSubspace n :=
  (dickeONB n).repr

/-- Manuscript label `def:dicke-basis`.

The Dicke isomorphism sends the lifted Dicke state to the standard basis
vector of the coordinate carrier. -/
theorem dickeIso_apply (n : ℕ) (w : Fin (n + 1)) :
    dickeIso n (dickeFamilyInSpan n w) = EuclideanSpace.single w (1 : ℂ) := by
  unfold dickeIso
  rw [← dickeONB_apply n w]
  exact (dickeONB n).repr_self w

end QEC.Dicke.Basis
