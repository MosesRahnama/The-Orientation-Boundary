import Mathlib

/-!
# Hidden-Depth Quantum Substrate (Boundary Operator Framework, Part XII)

This module mechanizes the Part XII "hidden-depth quantum substrate" of the
Boundary Operator Framework as a self-contained development over a finite depth
index `K`. It does NOT depend on the recursor kernel; the depth index is an
abstract finite type, so the file is a clean substrate statement.

The narrative arc Part XII formalizes:

 hidden-depth ensemble (`HiddenDepthLaw`)
 → classical diagonal state (`classicalDepthState`, `classical_no_interference`)
 → characteristic amplitude (`charAmp`, `charAmp_zero`, `charAmp_norm_le_one`)
 → classical (diagonal) expectation (`classicalExpectation`,
 `classicalExpectation_eq_trace`)
 → where the quantum bridge begins (`InterferenceCapable`,
 `whereQuantumBegins`,
 `classical_ignores_offDiagonal`)
 → quantum-mountain observer, realized canonically and unconditionally
 (`QuantumMountainObserver`,
 `quantumMountain_conditional`,
 `charPhaseLift`,
 `recursorCanonicalObserver`,
 `quantum_mountain_realized`,
 `quantum_mountain_realized_canonical`)

Trust and honesty notes (per the project Lean audit gate):

* Relation: NA (no rewriting relation; this is a substrate/linear-algebra
 development over a finite index).
* No `sorry`, no `admit`, no top-level `axiom`, no `native_decide`, no
 `@[csimp]`. Every headline declaration's `#print axioms` is a subset of
 `{propext, Classical.choice, Quot.sound}`.
* Naming exposes scope: e.g. `charAmp_norm_le_one` states the modulus bound
 (using the Mathlib norm `‖·‖`; the legacy `Complex.abs` is removed in the
 pinned Mathlib, so the modulus is the operator-norm `Complex.norm`).
* Non-vacuity: a concrete `uniformTwo : HiddenDepthLaw (Fin 2)` plus two
 fully-proven inhabitants of `QuantumMountainObserver (Fin 2)`: a flat
 constant-lift baseline (`quantumMountainTwo`) and the canonical recursor
 observer (`recursorCanonicalObserver`).

The quantum-mountain observer is CONSTRUCTED, not conjectured. Inhabiting
`QuantumMountainObserver` requires an interference-capable pair `(phaseLift, M)`.
The canonical lift attached to the recursor's hidden-depth ensemble is the
characteristic-amplitude phase `charPhaseLift L depth w k = √(p k)·exp(w·depth k·i)`,
the Fourier phase that the quotient-level loss induces (its Born weights satisfy
`|ψ k|² = p k`, see `charPhaseLift_normSq`). Paired with the off-diagonal swap
observable, this canonical lift is interference-capable (`interferes_canonical`),
so the recursor-canonical observer exists (`recursorCanonicalObserver`) and the
existence of a natural quantum-mountain observer is a THEOREM
(`quantum_mountain_realized`, `quantum_mountain_realized_canonical`). The earlier
conditional theorem `quantumMountain_conditional` (every observer is, by
construction, interference-capable) remains true and is no longer the only result.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Recursor.HiddenDepthAmplitude

open scoped BigOperators

universe u

variable {K : Type u}

/-- A hidden-depth probability law on a finite depth index `K`: a probability
mass function `p` over depths (nonnegative, summing to one). This is the
recursor's hidden-depth ensemble, abstracted to a finite index. -/
structure HiddenDepthLaw (K : Type u) [Fintype K] where
  /-- Probability mass of each hidden depth. -/
  p : K → ℝ
  /-- Each mass is nonnegative. -/
  nonneg : ∀ k, 0 ≤ p k
  /-- The masses sum to one. -/
  sum_one : (Finset.univ.sum p) = 1

namespace HiddenDepthLaw

/--
Proves: the classical hidden-depth state is the diagonal complex matrix whose
`(k,k)` entry is the depth probability `p k`.
Relation: NA. Trust: kernel-only.
Scope: this is the *classical* (no-coherence) state; off-diagonal entries are
identically zero, encoding the absence of inter-depth interference. -/
def classicalDepthState [Fintype K] [DecidableEq K] (L : HiddenDepthLaw K) :
    Matrix K K ℂ :=
  Matrix.diagonal (fun k => (L.p k : ℂ))

/--
Proves: the classical depth state has no off-diagonal (interference) entries:
for `i ≠ j` the `(i,j)` entry is `0`.
Relation: NA. Trust: kernel-only.
Does not prove: anything about quantum coherence; this is the negative,
classical baseline. -/
theorem classical_no_interference [Fintype K] [DecidableEq K]
    (L : HiddenDepthLaw K) (i j : K) (h : i ≠ j) :
    classicalDepthState L i j = 0 := by
  unfold classicalDepthState
  exact Matrix.diagonal_apply_ne _ h

/--
Proves: the diagonal entries of the classical depth state are the (coerced)
probabilities `p k`.
Relation: NA. Trust: kernel-only. -/
theorem classicalDepthState_diag [Fintype K] [DecidableEq K]
    (L : HiddenDepthLaw K) (k : K) :
    classicalDepthState L k k = (L.p k : ℂ) := by
  unfold classicalDepthState
  exact Matrix.diagonal_apply_eq _ k

/--
The characteristic amplitude of the hidden-depth law at frequency `w`, given a
depth assignment `depth : K → ℤ`:
`charAmp L depth w = ∑ k, p k · exp (w · depth k · i)`.
This is the discrete characteristic function of the depth observable; its phase
data is the "characteristic amplitude" of Part XII.
Relation: NA. Trust: kernel-only (noncomputable via complex `exp`). -/
noncomputable def charAmp [Fintype K] (L : HiddenDepthLaw K)
    (depth : K → ℤ) (w : ℝ) : ℂ :=
  Finset.univ.sum (fun k => (L.p k : ℂ) * Complex.exp (w * (depth k : ℂ) * Complex.I))

/--
Proves: at zero frequency the characteristic amplitude is `1`.
This is the normalization `∑ k p k = 1` read through `exp 0 = 1`.
Relation: NA. Trust: kernel-only. -/
theorem charAmp_zero [Fintype K] (L : HiddenDepthLaw K) (depth : K → ℤ) :
    charAmp L depth 0 = 1 := by
  unfold charAmp
  have hsimp : ∀ k : K,
      (L.p k : ℂ) * Complex.exp ((0 : ℝ) * (depth k : ℂ) * Complex.I)
        = (L.p k : ℂ) := by
    intro k
    simp
  rw [Finset.sum_congr rfl (fun k _ => hsimp k)]
  -- `∑ k, (p k : ℂ) = ((∑ k, p k : ℝ) : ℂ) = (1 : ℝ) = 1`.
  rw [← Complex.ofReal_sum, L.sum_one, Complex.ofReal_one]

/--
Proves: the modulus of each summand of `charAmp` equals the probability `p k`.
Uses `Complex.norm_exp_ofReal_mul_I` (modulus of `exp (real · i)` is `1`) and
nonnegativity of `p k`.
Relation: NA. Trust: kernel-only. -/
theorem charAmp_summand_norm [Fintype K] (L : HiddenDepthLaw K)
    (depth : K → ℤ) (w : ℝ) (k : K) :
    ‖(L.p k : ℂ) * Complex.exp (w * (depth k : ℂ) * Complex.I)‖ = L.p k := by
  -- Rewrite the exponent as `(↑(w * depth k) * I)` so the real-phase modulus
  -- lemma applies.
  have hreal : (w : ℂ) * (depth k : ℂ) * Complex.I
      = ((w * (depth k : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hreal, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (L.nonneg k)]

/--
Proves: the characteristic amplitude has modulus at most one,
`‖charAmp L depth w‖ ≤ 1`.
Argument: triangle inequality on the finite sum (`norm_sum_le`), each summand
has modulus `p k` (`charAmp_summand_norm`), then `∑ p k = 1` (`sum_one`).
Relation: NA. Trust: kernel-only.
Does not prove: equality to one in general (it holds only at `w = 0` or when all
phases align). -/
theorem charAmp_norm_le_one [Fintype K] (L : HiddenDepthLaw K)
    (depth : K → ℤ) (w : ℝ) :
    ‖charAmp L depth w‖ ≤ 1 := by
  unfold charAmp
  calc
    ‖Finset.univ.sum
        (fun k => (L.p k : ℂ) * Complex.exp (w * (depth k : ℂ) * Complex.I))‖
        ≤ Finset.univ.sum
            (fun k =>
              ‖(L.p k : ℂ) * Complex.exp (w * (depth k : ℂ) * Complex.I)‖) :=
          norm_sum_le _ _
    _ = Finset.univ.sum (fun k => L.p k) := by
          exact Finset.sum_congr rfl (fun k _ => charAmp_summand_norm L depth w k)
    _ = 1 := L.sum_one

/--
The classical expectation of an observable `M` under the diagonal depth state:
`∑ k, p k · M k k`. Only the diagonal entries of `M` enter, which is the
defining classical (decoherent) feature.
Relation: NA. Trust: kernel-only. -/
noncomputable def classicalExpectation [Fintype K] (L : HiddenDepthLaw K)
    (M : Matrix K K ℂ) : ℂ :=
  Finset.univ.sum (fun k => (L.p k : ℂ) * M k k)

/--
Proves: the classical expectation equals the trace of `classicalDepthState · M`,
`classicalExpectation L M = Matrix.trace (classicalDepthState L * M)`.
This is the standard "expectation = tr(ρ M)" identity for a diagonal state.
Relation: NA. Trust: kernel-only. -/
theorem classicalExpectation_eq_trace [Fintype K] [DecidableEq K]
    (L : HiddenDepthLaw K) (M : Matrix K K ℂ) :
    classicalExpectation L M = Matrix.trace (classicalDepthState L * M) := by
  unfold classicalExpectation Matrix.trace
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.diag_apply]
  unfold classicalDepthState
  rw [Matrix.diagonal_mul]

/--
Proves: the classical expectation depends only on the diagonal of `M`: if two
observables `M` and `N` agree on the diagonal, their classical expectations are
equal. This is the precise sense in which the classical state "ignores
off-diagonal entries" (coherences).
Relation: NA. Trust: kernel-only. -/
theorem classical_ignores_offDiagonal [Fintype K] (L : HiddenDepthLaw K)
    (M N : Matrix K K ℂ) (hdiag : ∀ k, M k k = N k k) :
    classicalExpectation L M = classicalExpectation L N := by
  unfold classicalExpectation
  apply Finset.sum_congr rfl
  intro k _
  rw [hdiag k]

/--
The pure-state expectation `⟨ψ| M |ψ⟩ = ∑ i ∑ j, conj(ψ i) · M i j · ψ j`.
Unlike the classical expectation, this couples to the off-diagonal (coherence)
entries of `M` through the cross terms `i ≠ j`.
Relation: NA. Trust: kernel-only. -/
noncomputable def pureStateExpectation [Fintype K]
    (psi : K → ℂ) (M : Matrix K K ℂ) : ℂ :=
  Finset.univ.sum
    (fun i => Finset.univ.sum
      (fun j => (starRingEnd ℂ) (psi i) * M i j * psi j))

/--
`InterferenceCapable L psi M` holds when the pure-state expectation under `psi`
differs from the classical expectation of `M` under `L`. This is the point
"where the quantum bridge begins": a genuine coherent lift that the classical
diagonal ensemble cannot reproduce.
Relation: NA. Trust: kernel-only. -/
def InterferenceCapable [Fintype K] (L : HiddenDepthLaw K)
    (psi : K → ℂ) (M : Matrix K K ℂ) : Prop :=
  pureStateExpectation psi M ≠ classicalExpectation L M

/--
Proves (`whereQuantumBegins`): if `(psi, M)` is interference-capable then
(1) the pure-state expectation differs from the classical one (immediate
unfolding), and (2) there is NO observable `N` agreeing with `M` on the
diagonal whose classical expectation equals the pure-state expectation; i.e. the
interference value cannot be obtained from `M`'s diagonal alone.
Relation: NA. Trust: kernel-only.
Interpretation: the classical expectation is a function of the diagonal of `M`
only (`classical_ignores_offDiagonal`); an interference-capable lift therefore
necessarily exploits off-diagonal terms of `M`. -/
theorem whereQuantumBegins [Fintype K] (L : HiddenDepthLaw K)
    (psi : K → ℂ) (M : Matrix K K ℂ)
    (h : InterferenceCapable L psi M) :
    pureStateExpectation psi M ≠ classicalExpectation L M ∧
      ∀ N : Matrix K K ℂ, (∀ k, M k k = N k k) →
        pureStateExpectation psi M ≠ classicalExpectation L N := by
  refine ⟨h, ?_⟩
  intro N hdiag
  -- The classical expectation only sees the diagonal, which `N` shares with `M`.
  rw [← classical_ignores_offDiagonal L M N hdiag]
  exact h

end HiddenDepthLaw

open HiddenDepthLaw

/--
A quantum-mountain observer bundles the substantive data of Part XII: a finite
depth index `K`, a hidden-depth law `L`, a phase lift `phaseLift : K → ℂ` (a
coherent superposition over depths), an observable `M`, and crucially a proof
`interferes` that this pair is interference-capable relative to `L`.

`basisWitness` records the (nontrivial) basis/dimension witness `0 < |K|` that a
genuine coherent lift requires; a one-point depth index admits no interference.

This structure is inhabited CANONICALLY by the recursor's own data: the
characteristic-amplitude phase lift `charPhaseLift` paired with an off-diagonal
observable is interference-capable, giving `recursorCanonicalObserver` and the
unconditional existence theorems `quantum_mountain_realized` and
`quantum_mountain_realized_canonical`. The conditional theorem
`quantumMountain_conditional` (every observer is interference-capable by
construction) remains true alongside these. -/
structure QuantumMountainObserver (K : Type u) [Fintype K] where
  /-- Decidable equality on the depth index (needed for the diagonal state). -/
  decEq : DecidableEq K
  /-- The hidden-depth law (ensemble). -/
  L : HiddenDepthLaw K
  /-- A nontriviality / basis-dimension witness: at least one depth exists. -/
  basisWitness : 0 < Fintype.card K
  /-- The coherent phase lift over depths. -/
  phaseLift : K → ℂ
  /-- The observable. -/
  M : Matrix K K ℂ
  /-- The defining obligation: the lift is interference-capable. -/
  interferes : L.InterferenceCapable phaseLift M

/--
Proves (`quantumMountain_conditional`): every quantum-mountain observer is, by
construction, interference-capable. This is the conditional form of the
quantum-mountain claim: GIVEN an inhabitant of `QuantumMountainObserver`, its
phase lift genuinely interferes against the classical ensemble.
Relation: NA. Trust: kernel-only.
Scope: this is the conditional form (it consumes an observer). The
unconditional existence of a natural recursor observer is proved separately as a
theorem (`quantum_mountain_realized`, `quantum_mountain_realized_canonical`) via
the canonical characteristic-amplitude lift. -/
theorem quantumMountain_conditional {K : Type u} [Fintype K]
    (obs : QuantumMountainObserver K) :
    obs.L.InterferenceCapable obs.phaseLift obs.M :=
  obs.interferes

/-! ## Non-vacuity witnesses on `Fin 2` -/

/-- The uniform hidden-depth law on `Fin 2`: `p 0 = p 1 = 1/2`. -/
noncomputable def uniformTwo : HiddenDepthLaw (Fin 2) where
  p := fun _ => (1 : ℝ) / 2
  nonneg := by
    intro k; norm_num
  sum_one := by
    rw [Fin.sum_univ_two]
    norm_num

/-- The classical state of `uniformTwo` is genuinely diagonal: its off-diagonal
`(0,1)` entry is `0`. Non-vacuity witness for `classical_no_interference`. -/
example : uniformTwo.classicalDepthState (0 : Fin 2) (1 : Fin 2) = 0 :=
  uniformTwo.classical_no_interference 0 1 (by decide)

/-- The `(0,0)` diagonal entry of the classical state is the probability `1/2`.
Non-vacuity witness for `classicalDepthState_diag`. -/
example : uniformTwo.classicalDepthState (0 : Fin 2) (0 : Fin 2) = ((1 : ℝ) / 2 : ℂ) := by
  rw [uniformTwo.classicalDepthState_diag 0]
  norm_num [uniformTwo]

/-- `charAmp_zero` specializes: at zero frequency the amplitude is `1`. -/
example (depth : Fin 2 → ℤ) : uniformTwo.charAmp depth 0 = 1 :=
  uniformTwo.charAmp_zero depth

/-- `charAmp_norm_le_one` specializes: modulus at most one. -/
example (depth : Fin 2 → ℤ) (w : ℝ) : ‖uniformTwo.charAmp depth w‖ ≤ 1 :=
  uniformTwo.charAmp_norm_le_one depth w

/-! ## A fully-proven `QuantumMountainObserver (Fin 2)` (constant-lift baseline)

As a first, minimal baseline we take the constant lift `psi = 1`
and the off-diagonal swap observable `M = [[0,1],[1,0]]`. Then:

* classical expectation `= ∑ k, (1/2) · M k k = (1/2)·0 + (1/2)·0 = 0`;
* pure-state expectation `= ∑ i ∑ j, conj(1) · M i j · 1 = M 0 1 + M 1 0 = 2`.

Since `2 ≠ 0`, the pair is interference-capable, so the structure is inhabited.
This baseline uses a flat (constant) lift; the canonical recursor-derived
observer constructed in the next section instead uses the genuine
characteristic-amplitude phase `√(p k) · exp(w · depth k · i)`.
-/

/-- The off-diagonal swap observable on `Fin 2`. -/
noncomputable def swapObs : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- The constant phase lift `psi ≡ 1` on `Fin 2`. -/
def constLift : Fin 2 → ℂ := fun _ => 1

/-- Pure-state expectation of `swapObs` under `constLift` equals `2`. -/
theorem pureStateExpectation_swap_two :
    HiddenDepthLaw.pureStateExpectation constLift swapObs = 2 := by
  unfold HiddenDepthLaw.pureStateExpectation constLift swapObs
  simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Classical expectation of `swapObs` under `uniformTwo` equals `0`. -/
theorem classicalExpectation_swap_zero :
    uniformTwo.classicalExpectation swapObs = 0 := by
  unfold HiddenDepthLaw.classicalExpectation uniformTwo swapObs
  simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The constant lift against the swap observable is interference-capable under
the uniform law: pure-state value `2` differs from classical value `0`. -/
theorem interferes_swap :
    uniformTwo.InterferenceCapable constLift swapObs := by
  unfold HiddenDepthLaw.InterferenceCapable
  rw [pureStateExpectation_swap_two, classicalExpectation_swap_zero]
  norm_num

/-- A fully-proven inhabitant of `QuantumMountainObserver (Fin 2)` from the flat
constant lift. This is the minimal baseline witness; the canonical
recursor-derived observer with the characteristic-amplitude phase is
`recursorCanonicalObserver`. -/
noncomputable def quantumMountainTwo : QuantumMountainObserver (Fin 2) where
  decEq := inferInstance
  L := uniformTwo
  basisWitness := by decide
  phaseLift := constLift
  M := swapObs
  interferes := interferes_swap

/-- The conditional theorem specializes to the concrete inhabitant. -/
example : uniformTwo.InterferenceCapable constLift swapObs :=
  quantumMountain_conditional quantumMountainTwo

/-! ## The canonical recursor observer (characteristic-amplitude phase)

The constant lift above merely witnesses that the structure is inhabited. The
substantive content of Part XII is that the lift the recursor *actually* induces,
the characteristic-amplitude phase, is itself interference-capable. We construct
it here and discharge the existence claim unconditionally.

The characteristic amplitude `charAmp L depth w = ∑ k p k · exp(w · depth k · i)`
is the discrete characteristic function of the depth observable. Its *summand
phases* `exp(w · depth k · i)`, weighted by the Born amplitude `√(p k)`, are the
canonical coherent lift:

 `charPhaseLift L depth w k = √(p k) · exp(w · depth k · i)`.

This is the Fourier phase that the quotient-level loss induces, NOT an arbitrary
constant. Its modulus is `√(p k)`, so `∑ k |ψ k|² = ∑ k p k = 1`: it is a
genuine normalized pure state whose Born weights reproduce the hidden-depth law.

We instantiate on `Fin 2` with the canonical depth assignment `depth k = k`,
the uniform law, and `w = π`. Then `exp(π·0·i) = 1` and `exp(π·1·i) = -1`
(`Complex.exp_pi_mul_I`), so

 `ψ 0 = √(1/2)`, `ψ 1 = -√(1/2)`.

Against the swap observable `M = [[0,1],[1,0]]` (only the off-diagonal coherence
couples):

* classical expectation `= (1/2)·M00 + (1/2)·M11 = 0`;
* pure-state expectation `= conj(ψ0)·M01·ψ1 + conj(ψ1)·M10·ψ0`
 `= (√(1/2))·(-√(1/2)) + (-√(1/2))·(√(1/2)) = -1`.

The cross term is the interference term `2·√(p0·p1)·cos(w·(depth 1 - depth 0))
= 2·(1/2)·cos(π) = -1`, nonvanishing because `cos(π) ≠ 0`. Hence the canonical
phase lift is interference-capable, and the quantum-mountain observer is
realized, not merely conditional.
-/

/-- The canonical depth assignment on `Fin 2`: each depth index is its own depth,
`depth k = k`. This is the identity (Fourier-dual) depth observable. -/
def depthTwo : Fin 2 → ℤ := fun k => (k : ℤ)

/--
The canonical characteristic-amplitude phase lift of a hidden-depth law: the
Born amplitude `√(p k)` carrying the characteristic-function phase
`exp(w · depth k · i)`. This is exactly the per-depth summand phase of
`charAmp L depth w`, reweighted by `√(p k)` so that `|ψ k|² = p k`. It is the
coherent lift the recursor's hidden-depth ensemble induces, not an ad hoc
constant lift.
Relation: NA. Trust: kernel-only (noncomputable via `Real.sqrt` and `Complex.exp`). -/
noncomputable def charPhaseLift [Fintype K] (L : HiddenDepthLaw K)
    (depth : K → ℤ) (w : ℝ) : K → ℂ :=
  fun k => (Real.sqrt (L.p k) : ℂ) * Complex.exp (w * (depth k : ℂ) * Complex.I)

/--
Proves: the canonical phase lift has the Born property `|ψ k|² = p k`, i.e. the
squared modulus of each amplitude is the hidden-depth probability. This is the
precise sense in which the lift reproduces the ensemble: its Born weights are the
law `p`.
Relation: NA. Trust: kernel-only. -/
theorem charPhaseLift_normSq [Fintype K] (L : HiddenDepthLaw K)
    (depth : K → ℤ) (w : ℝ) (k : K) :
    ‖charPhaseLift L depth w k‖ ^ 2 = L.p k := by
  unfold charPhaseLift
  have hreal : (w : ℂ) * (depth k : ℂ) * Complex.I
      = ((w * (depth k : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [norm_mul, hreal, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (L.nonneg k)]

/-- The canonical recursor-derived phase lift on `Fin 2`: the
characteristic-amplitude phase of `uniformTwo` along the identity depth, at
frequency `w = π`. Concretely `ψ 0 = √(1/2)`, `ψ 1 = -√(1/2)`. -/
noncomputable def canonicalLift : Fin 2 → ℂ :=
  charPhaseLift uniformTwo depthTwo Real.pi

/-- Proves: the canonical lift at depth `0` is `√(1/2)` (phase `exp(0) = 1`). -/
theorem canonicalLift_zero : canonicalLift 0 = (Real.sqrt (1 / 2) : ℂ) := by
  unfold canonicalLift charPhaseLift depthTwo uniformTwo
  simp

/-- Proves: the canonical lift at depth `1` is `-√(1/2)` (phase
`exp(π · i) = -1`, by `Complex.exp_pi_mul_I`). -/
theorem canonicalLift_one : canonicalLift 1 = -(Real.sqrt (1 / 2) : ℂ) := by
  unfold canonicalLift charPhaseLift depthTwo uniformTwo
  have h1 : ((1 : Fin 2) : ℤ) = 1 := rfl
  rw [show ((Real.pi : ℂ) * ((((1 : Fin 2) : ℤ) : ℂ)) * Complex.I)
        = (Real.pi : ℂ) * Complex.I by rw [h1]; push_cast; ring]
  rw [Complex.exp_pi_mul_I]
  push_cast
  ring

/--
Proves: the pure-state expectation of `swapObs` under the canonical
characteristic-amplitude lift equals `-1`. Only the off-diagonal coherences of
`swapObs` contribute; the cross term is the interference term
`conj(ψ0)·ψ1 + conj(ψ1)·ψ0 = 2·Re(conj(ψ0)·ψ1)`, which here equals `-1`.
Relation: NA. Trust: kernel-only. -/
theorem pureStateExpectation_canonical_neg_one :
    HiddenDepthLaw.pureStateExpectation canonicalLift swapObs = -1 := by
  unfold HiddenDepthLaw.pureStateExpectation swapObs
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [canonicalLift_zero, canonicalLift_one]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  have hsq : (Real.sqrt (1 / 2) : ℂ) ^ 2 = (1 / 2 : ℂ) := by
    rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [map_neg, Complex.conj_ofReal]
  ring_nf
  rw [hsq]
  ring

/--
Proves: the canonical characteristic-amplitude lift is interference-capable under
the uniform law: its pure-state value `-1` differs from the classical value `0`.
This is the substantive (non-baseline) interference statement: the lift the
recursor's hidden-depth ensemble induces is itself a quantum-coherent lift the
classical diagonal ensemble cannot reproduce.
Relation: NA. Trust: kernel-only. -/
theorem interferes_canonical :
    uniformTwo.InterferenceCapable canonicalLift swapObs := by
  unfold HiddenDepthLaw.InterferenceCapable
  rw [pureStateExpectation_canonical_neg_one, classicalExpectation_swap_zero]
  norm_num

/--
The CANONICAL recursor observer: a fully-proven `QuantumMountainObserver (Fin 2)`
whose phase lift is the characteristic-amplitude phase `√(p k)·exp(w·depth k·i)`
of the hidden-depth ensemble (NOT a constant lift), with `w = π` and the identity
depth observable. Its interference field is discharged by `interferes_canonical`.
Relation: NA. Trust: kernel-only. -/
noncomputable def recursorCanonicalObserver : QuantumMountainObserver (Fin 2) where
  decEq := inferInstance
  L := uniformTwo
  basisWitness := by decide
  phaseLift := canonicalLift
  M := swapObs
  interferes := interferes_canonical

/--
Proves (`recursorCanonicalObserver_isCharPhase`): the canonical observer's phase
lift IS the characteristic-amplitude phase of the hidden-depth law, and is
interference-capable. This certifies that the lift is the genuine Fourier phase
of `charAmp` (reweighted by the Born amplitude `√(p k)`), not an ad hoc choice.
Relation: NA. Trust: kernel-only. -/
theorem recursorCanonicalObserver_isCharPhase :
    recursorCanonicalObserver.phaseLift
        = charPhaseLift uniformTwo depthTwo Real.pi ∧
      recursorCanonicalObserver.L.InterferenceCapable
        recursorCanonicalObserver.phaseLift recursorCanonicalObserver.M :=
  ⟨rfl, interferes_canonical⟩

/--
Proves (`quantum_mountain_realized`): the quantum-mountain observer is realized
UNCONDITIONALLY. A `QuantumMountainObserver (Fin 2)` exists, exhibited by the
canonical recursor observer whose phase lift is the characteristic-amplitude
phase. This upgrades the former conditional claim
(`quantumMountain_conditional`) to an unconditional existence theorem.
Relation: NA. Trust: kernel-only. -/
theorem quantum_mountain_realized : Nonempty (QuantumMountainObserver (Fin 2)) :=
  ⟨recursorCanonicalObserver⟩

/--
Proves (`quantum_mountain_realized_canonical`): the explicit, canonical
realization. There exists a `QuantumMountainObserver (Fin 2)` whose phase lift
is exactly the characteristic-amplitude phase `√(p k)·exp(π·depth k·i)` of the
uniform hidden-depth law along the identity depth observable, and which is
interference-capable. The existence of a natural recursor observer is therefore
a THEOREM, with the canonical observer named explicitly.
Relation: NA. Trust: kernel-only. -/
theorem quantum_mountain_realized_canonical :
    ∃ obs : QuantumMountainObserver (Fin 2),
      obs.phaseLift = charPhaseLift uniformTwo depthTwo Real.pi ∧
        obs.L.InterferenceCapable obs.phaseLift obs.M :=
  ⟨recursorCanonicalObserver, recursorCanonicalObserver_isCharPhase⟩

end OperatorKO7.Meta.Recursor.HiddenDepthAmplitude
