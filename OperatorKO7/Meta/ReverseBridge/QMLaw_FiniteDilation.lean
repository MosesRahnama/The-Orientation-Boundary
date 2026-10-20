import Mathlib
import OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM
import OperatorKO7.Meta.QuantumBoundary.FiniteDecoherenceChannel

/-!
# QM-law mechanization, finite dilation cluster (RB QM-law wave W5-E)

This module mechanizes the finite, structural content of three dilation theorems of operator-algebraic
quantum theory on the **already-PROVEN** finite matrix / positivity / channel surface of OperatorKO7.
Each quantum-mechanical reading is stated only as ANALOGY in the docstrings and is **never** asserted by
a theorem; every headline is a structural fact about finite complex matrices (positive-semidefiniteness,
conjugation/compression, matrix square roots, and the concrete dephasing channel). Nothing in this file
is a rewriting relation.

The cluster is genuinely **possible, not automatic**: a faked "dilation = identity" would be worthless.
All three targets admit a GENUINE general finite construction on this carrier. For finite Stinespring we
build the general finite Kraus-form CP map, its column-stacking dilation isometry, and the partial-trace
compression identity (`cpMapKraus`, `stinespring_isometry`, `stinespring_dilates`); only the CONVERSE
existence of a Kraus family for an ABSTRACT CP linear map `M_n → M_m` is left external (it needs the
general linear-map carrier plus a Choi spectral decomposition), and that is a scoped note, not a hole.
We never write `sorry`.

## SP2-99 Naimark (finite) — GENUINE full construction (a PVM on a larger finite space)

NameGate anchors: `OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM.IsPOVM`,
`...DensityMatrixPOVM.basisPOVM`, `...DensityMatrixPOVM.isPOVM_basisPOVM` (the PROVEN finite POVM object).

A finite POVM `{E i}_{i ∈ ι}` on `ℂ^n` (PSD effects with `∑ i, E i = 1`) is dilated to a genuine
**projective measurement (PVM)** on the strictly larger finite space `ℂ^(n·|ι|) ≅ ℂ^n ⊗ ℂ^ι`, indexed by
`Fin n × ι`. The dilated PVM is `P i := I_n ⊗ |i⟩⟨i|` (`naimarkProj`): we prove these are genuine
orthogonal projections (`naimarkProj_idempotent`, `naimarkProj_isHermitian`), mutually orthogonal
(`naimarkProj_orthogonal`), and resolve the identity (`naimarkProj_sum_eq_one`) — i.e. a bona fide PVM.
The dilation operator `V := ∑_i (√E_i ⊗ |i⟩)` (`naimarkV`, the columns are the `√E_i` stacked into the
`i`-th ancilla block) is an **isometry** exactly because the POVM is complete:
`Vᴴ V = ∑_i E_i = 1` (`naimark_isometry`, on `IsPOVM.2`). The Naimark identity is then
`E i = Vᴴ (P i) V` (`naimark_compression`): every POVM effect is the **compression** of a PVM projection
through the isometry `V`. The qubit computational-basis POVM realizes it concretely (R5):
`naimark_isometry_basisPOVM`, `naimark_compression_basisPOVM`.

  QM ANALOGY (docstring only, never asserted): Naimark's dilation theorem — every POVM `{E_i}` on a
  Hilbert space `H` is the compression `E_i = V† P_i V` of a projective measurement `{P_i}` on a larger
  space `H ⊕ K`, where `V : H → H ⊕ K` is an isometry; equivalently, every generalized measurement is a
  projective measurement on system-plus-ancilla.

## SP2-100 Choi–Jamiołkowski (finite) — GENUINE iff on the positivity surface

NameGate anchor: `Matrix.posSemidef_iff_eq_conjTranspose_mul_self` (Mathlib: `M.PosSemidef ↔ ∃ B, M = Bᴴ*B`).

Channel–state duality in its sharp finite form: a finite Hermitian matrix is positive semidefinite **iff**
it is the Gram/Choi matrix `Bᴴ B` of some operator `B`. We mechanize the iff directly as
`choiPSD_iff_isGram` (a transparent restatement that exposes the duality as it is used: PSD ⟺ realized as
a Choi/Gram matrix), and apply it to the PROVEN dephasing channel: the **Choi PSD criterion** for
`dephase γ` is the EXACT iff `choiDephaseQubit_posSemidef_iff : PSD ↔ -1 ≤ γ ≤ 1`, with both boundaries
pinned. Concretely, on the qubit we build the explicit `4×4` Choi matrix
`choiDephaseQubit γ` (`choiDephaseQubit`, `= ∑_{ij} Eᵢⱼ ⊗ Φ_γ(Eᵢⱼ)` written out), prove the PSD side on
the FULL CP region `choiDephaseQubit_posSemidef_full` (`-1 ≤ γ ≤ 1`, via the spectral decomposition
`choiDephaseQubit_eq_spectral_sum` with nonnegative eigen-weights `(1±γ)/2`; the historical `[0,1]` Kraus
route survives as `choiDephaseQubit_posSemidef`), the exact lower boundary
`choiDephaseQubit_neg_one_posSemidef` (PSD at `γ = -1`, rank-deficient), and BOTH refutations
`choiDephaseQubit_not_posSemidef_of_lt` (`γ < -1`) and `choiDephaseQubit_not_posSemidef_of_gt` (`γ > 1`),
each via an explicit witness vector with a negative quadratic form. Both directions, plus the non-CP
witness, are concrete (R5): `choi_witness_cp`, `choi_witness_nonCP`.

  QM ANALOGY (docstring only, never asserted): the Choi–Jamiołkowski isomorphism — a linear map
  `Φ : M_n → M_m` is completely positive iff its Choi matrix `C_Φ = (id ⊗ Φ)(|Ω⟩⟨Ω|) = ∑_{ij} Eᵢⱼ ⊗ Φ(Eᵢⱼ)`
  (the image of the unnormalized maximally entangled state) is positive semidefinite.

## SP2-98 Stinespring (finite) — GENUINE general finite construction (Kraus family ⟹ isometric dilation)

NameGate anchors: `...FiniteDecoherenceChannel.dephase`, `...FiniteDecoherenceChannel.dephase_posSemidef`,
`Matrix.PosSemidef.mul_mul_conjTranspose_same`.

We mechanize the constructive direction of finite Stinespring in FULL generality on the Matrix surface,
for an arbitrary finite Kraus family `K : ι → M_{m×n}(ℂ)`:

* `cpMapKraus K ρ := ∑ₐ Kₐ ρ Kₐᴴ` — the general finite completely-positive map of a Kraus family;
  `cpMapKraus_posSemidef` proves it sends PSD to PSD (complete positivity on the carrier).
* `stinespringV K` — the dilation: the column-stacking `V (i,a) j = Kₐ i j` into `ℂ^(m·|ι|)`;
  `stinespring_gram_eq` gives `Vᴴ V = ∑ₐ Kₐᴴ Kₐ`, and `stinespring_isometry` gives `Vᴴ V = 1` exactly
  when the family is trace-preserving (`∑ₐ Kₐᴴ Kₐ = 1`) — the finite Stinespring dilation isometry.
* `stinespring_dilates` — the compression identity `Φ(ρ) = Tr_ancilla (V ρ Vᴴ)` (`partialTraceAncilla`):
  the map is recovered as the partial trace of the conjugation by the dilation isometry.
* R5: the projective-measurement channel `{P₀,P₁}` is trace-preserving (`meas_kraus_isTP`) and its
  dilation is a genuine isometry (`meas_stinespring_isometry`), so the construction is non-vacuous.
* The concrete `dephase` channel is also exhibited in explicit Kraus form (`dephase_kraus`,
  `dephase_kraus_posSemidef`); `kraus_apply_posSemidef` is the single-leg positivity lemma.

The ONLY part left external is the CONVERSE — that an ABSTRACT CP linear map `M_n → M_m` (not already
presented as a Kraus family) admits such a family — which needs the general `M_n →ₗ M_m` carrier plus a
Choi spectral decomposition. That is a separate formalization, scoped here; it is not a `sorry` and not a
hole in the construction above.

  QM ANALOGY (docstring only, never asserted): Stinespring's dilation theorem — every completely positive
  map `Φ : A → B(H)` has the form `Φ(a) = V† π(a) V` for a *-representation `π` and bounded `V`; finite
  dimensionally, every CPTP channel `Φ(ρ) = Tr_E(U (ρ ⊗ |0⟩⟨0|) U†) = ∑_a K_a ρ K_a†` is the partial
  trace of a unitary/isometric dilation on system-plus-environment, with Kraus operators `K_a`.

## Audit slots
- Relation: NA (no rewriting relation). All three are structural facts about finite complex matrices
  (positivity, compression, square roots) and the PROVEN `dephase` channel.
- Closure: `propext`, `Classical.choice`, `Quot.sound`; verified per headline by `#print axioms` at the
  foot of the file.
- Trust: no `sorry`/`admit`/`axiom`/`constant`/`opaque`/`partial`/`unsafe`/`extern`/`implemented_by`/
  `@[csimp]`/`native_decide`/`bv_decide` on any load-bearing declaration. All Real/Complex-valued defs are
  `noncomputable`. No `decide`/`native_decide` on any matrix-positivity goal: PSD is always discharged via
  named lemmas (`posSemidef_conjTranspose_mul_self`, `mul_mul_conjTranspose_same`, `posSemidef_diagonal_iff`,
  `PosSemidef.add`, `posSemidef_real_smul`) and the non-PSD converse via an EXPLICIT witness vector with a
  named real-negativity computation.
- Non-vacuity (R5, the crux): Naimark realized on `basisPOVM` (`naimark_isometry_basisPOVM`,
  `naimark_compression_basisPOVM`); Choi has a CP witness (`choi_witness_cp`) AND a non-CP witness with a
  non-PSD Choi (`choi_witness_nonCP`); Stinespring compression half is realized on `dephase`
  (`dephase_kraus`, `dephase_kraus_posSemidef`).
- Scope: the finite Naimark compression of a PVM, the finite Choi PSD⟺Gram duality applied to the
  dephasing channel's EXACT CP criterion `-1 ≤ γ ≤ 1` (the full iff, both boundaries pinned), and the
  GENERAL finite Stinespring dilation of any finite
  Kraus family (isometry `Vᴴ V = ∑ Kᴴ K` and the partial-trace compression `Φ = Tr_anc (V · Vᴴ)`). The
  only external piece is the converse Kraus-existence for an abstract CP linear map (needs the general
  linear-map carrier + a Choi spectral decomposition). The QM identifications are ANALOGY, never asserted.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation

open Matrix
open scoped ComplexOrder

/-! ## NameGate — every imported anchor is checked here before use. -/

section NameGate

open OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM in
/-- Anchor check: the PROVEN finite POVM predicate. -/
example {n : ℕ} {ι : Type} [Fintype ι] (E : ι → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  IsPOVM E

open OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM in
/-- Anchor check: the PROVEN qubit computational-basis POVM and its `IsPOVM` proof. -/
example : OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM.IsPOVM
    OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM.basisPOVM :=
  OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM.isPOVM_basisPOVM

/-- Anchor check: the PROVEN finite dephasing channel and its positivity preservation. -/
example {n : ℕ} (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ.PosSemidef) :
    (OperatorKO7.Meta.QuantumBoundary.FiniteDecoherenceChannel.dephase γ ρ).PosSemidef :=
  OperatorKO7.Meta.QuantumBoundary.FiniteDecoherenceChannel.dephase_posSemidef h0 h1 hρ

/-- Anchor check: the Mathlib PSD⟺Gram engine that powers the finite Choi–Jamiołkowski duality. -/
example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    M.PosSemidef ↔ ∃ B : Matrix (Fin n) (Fin n) ℂ, M = Bᴴ * B :=
  Matrix.posSemidef_iff_eq_conjTranspose_mul_self

/-- Anchor check: the Mathlib compression-PSD lemma powering Naimark and the Stinespring half. -/
example {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) {m : Type} [Fintype m]
    (B : Matrix (Fin n) m ℂ) : (Bᴴ * A * B).PosSemidef :=
  hA.conjTranspose_mul_mul_same B

end NameGate

/-- A nonnegative-real scalar multiple of a positive-semidefinite matrix is positive semidefinite, over
ANY finite index type (the anchor `FiniteDecoherenceChannel.posSemidef_real_smul` is fixed to `Fin n`;
the Choi matrix lives over `Fin 2 × Fin 2`, so we need this index-general version). Same proof shape. -/
theorem posSemidef_real_smul_gen {m : Type*} [Fintype m] {M : Matrix m m ℂ} (hM : M.PosSemidef)
    {γ : ℝ} (hγ : 0 ≤ γ) : ((γ : ℂ) • M).PosSemidef := by
  refine ⟨?_, ?_⟩
  · show ((γ : ℂ) • M)ᴴ = (γ : ℂ) • M
    rw [Matrix.conjTranspose_smul, hM.1.eq, Complex.star_def, Complex.conj_ofReal]
  · intro x
    rw [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg (Complex.zero_le_real.mpr hγ) (hM.2 x)

/-! ## SP2-99 Naimark (finite): a POVM is the compression of a PVM on `Fin n × ι`.

QM ANALOGY (never asserted): a generalized measurement is a projective measurement on an enlarged space.
-/

section Naimark

open OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The **dilated PVM projection** `P i := I_n ⊗ |i⟩⟨i|` on the enlarged finite space `Fin n × ι`:
the entry at `(a,k),(b,l)` is `1` when `a = b` and `k = l = i`, else `0`. This is the orthogonal
projection onto the `i`-th ancilla block. -/
noncomputable def naimarkProj (i : ι) : Matrix (Fin n × ι) (Fin n × ι) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ p.2 = i ∧ q.2 = i then (1 : ℂ) else 0

omit [Fintype ι] in
@[simp] theorem naimarkProj_apply (i : ι) (p q : Fin n × ι) :
    naimarkProj i p q = if p.1 = q.1 ∧ p.2 = i ∧ q.2 = i then (1 : ℂ) else 0 := rfl

omit [Fintype ι] in
/-- The dilated projections are **Hermitian**. -/
theorem naimarkProj_isHermitian (i : ι) : (naimarkProj (n := n) i).IsHermitian := by
  ext p q
  simp only [Matrix.conjTranspose_apply, naimarkProj_apply]
  by_cases h : q.1 = p.1 ∧ q.2 = i ∧ p.2 = i
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.2, h.2.1⟩, star_one]
  · rw [if_neg h, star_zero, if_neg ?_]
    rintro ⟨h1, h2, h3⟩; exact h ⟨h1.symm, h3, h2⟩

/-- The dilated projections are **idempotent** (`P i * P i = P i`): genuine projections. -/
theorem naimarkProj_idempotent (i : ι) :
    naimarkProj (n := n) i * naimarkProj i = naimarkProj i := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [naimarkProj_apply]
  by_cases hpq : p.1 = q.1 ∧ p.2 = i ∧ q.2 = i
  · rw [if_pos hpq]
    rw [Finset.sum_eq_single (p.1, i)]
    · simp [hpq.1, hpq.2.1, hpq.2.2]
    · rintro b _ hb
      have : ¬ (p.1 = b.1 ∧ p.2 = i ∧ b.2 = i) ∨ ¬ (b.1 = q.1 ∧ b.2 = i ∧ q.2 = i) := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨⟨_, _, hbi⟩, ⟨hb1, _, _⟩⟩ := hcon
        exact hb (Prod.ext (hb1.trans hpq.1.symm) hbi)
      rcases this with h | h <;> simp [h]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · rw [if_neg hpq]
    apply Finset.sum_eq_zero
    rintro b _
    by_cases hb1 : p.1 = b.1 ∧ p.2 = i ∧ b.2 = i
    · by_cases hb2 : b.1 = q.1 ∧ b.2 = i ∧ q.2 = i
      · exact absurd ⟨hb1.1.trans hb2.1, hb1.2.1, hb2.2.2⟩ hpq
      · rw [if_neg hb2, mul_zero]
    · rw [if_neg hb1, zero_mul]

/-- The dilated projections are **mutually orthogonal** (`i ≠ j → P i * P j = 0`). -/
theorem naimarkProj_orthogonal {i j : ι} (hij : i ≠ j) :
    naimarkProj (n := n) i * naimarkProj j = 0 := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [naimarkProj_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  rintro b _
  by_cases hb1 : p.1 = b.1 ∧ p.2 = i ∧ b.2 = i
  · by_cases hb2 : b.1 = q.1 ∧ b.2 = j ∧ q.2 = j
    · exact absurd (hb1.2.2.symm.trans hb2.2.1) hij
    · rw [if_neg hb2, mul_zero]
  · rw [if_neg hb1, zero_mul]

/-- **PVM resolution of the identity**: `∑ i, P i = 1` on the enlarged space. The projections form a
genuine projective-valued measure. -/
theorem naimarkProj_sum_eq_one : (∑ i : ι, naimarkProj (n := n) i) = 1 := by
  ext p q
  rw [Matrix.sum_apply]
  simp only [naimarkProj_apply, Matrix.one_apply]
  by_cases hpq : p = q
  · subst hpq
    rw [if_pos rfl]
    rw [Finset.sum_eq_single p.2]
    · simp
    · intro b _ hb; rw [if_neg]; rintro ⟨_, _, hbq⟩; exact hb hbq.symm
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · rw [if_neg hpq]
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    exact hpq (Prod.ext h1 (h2.trans h3.symm))

/-- The **Naimark dilation operator** `V := ∑_i (√E_i ⊗ |i⟩)`: a `(Fin n × ι) × Fin n` operator whose
`i`-th ancilla block of rows is `√E_i`. Concretely `V (a,k) b = (√E_k) a b` (the `k`-block is `√E_k`). -/
noncomputable def naimarkV (E : ι → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i, (E i).PosSemidef) : Matrix (Fin n × ι) (Fin n) ℂ :=
  Matrix.of fun p b => (hE p.2).sqrt p.1 b

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem naimarkV_apply (E : ι → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i, (E i).PosSemidef) (p : Fin n × ι) (b : Fin n) :
    naimarkV E hE p b = (hE p.2).sqrt p.1 b := rfl

/-- The **Naimark compression** `Vᴴ (P i) V : Matrix (Fin n) (Fin n) ℂ` of the PVM projection `P i`
through the dilation `V`. The inner type ascriptions pin the (square) `Matrix` multiplication and avoid
the `CStarMatrix` HMul synonym ambiguity that arises for rectangular factors under `import Mathlib`. -/
noncomputable def naimarkComp (E : ι → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i, (E i).PosSemidef) (i : ι) : Matrix (Fin n) (Fin n) ℂ :=
  (((naimarkV E hE).conjTranspose * naimarkProj i : Matrix (Fin n) (Fin n × ι) ℂ)
    * naimarkV E hE : Matrix (Fin n) (Fin n) ℂ)

/-- The **Naimark Gram operator** `Vᴴ V : Matrix (Fin n) (Fin n) ℂ`. Same ascription discipline. -/
noncomputable def naimarkGram (E : ι → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i, (E i).PosSemidef) : Matrix (Fin n) (Fin n) ℂ :=
  ((naimarkV E hE).conjTranspose * naimarkV E hE : Matrix (Fin n) (Fin n) ℂ)

/-- The entry of the conjugated dilation `(Vᴴ * P i * V) a c`, expanded as an explicit double sum over
the enlarged index `Fin n × ι`, before any collapse. Keeping everything as scalar sums avoids rectangular
matrix-product instance ambiguities. -/
theorem naimark_triple_entry (E : ι → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i, (E i).PosSemidef) (i : ι) (a c : Fin n) :
    naimarkComp E hE i a c
      = ∑ s : Fin n × ι, (∑ r : Fin n × ι,
          star ((hE r.2).sqrt r.1 a) * naimarkProj i r s) * (hE s.2).sqrt s.1 c := by
  rw [naimarkComp, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [naimarkV_apply, Matrix.mul_apply]
  refine congrArg (· * (hE s.2).sqrt s.1 c) ?_
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Matrix.conjTranspose_apply, naimarkV_apply]

/-- **Naimark compression identity**: `Vᴴ (P i) V = E i`. Every POVM effect is the compression of the
PVM projection `P i` through the dilation operator `V`. This IS the finite Naimark theorem on the carrier.
The block structure collapses `Vᴴ (P i) V` to `(√E_i)ᴴ (√E_i) = √E_i √E_i = E_i`. -/
theorem naimark_compression (E : ι → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i, (E i).PosSemidef) (i : ι) :
    naimarkComp E hE i = E i := by
  ext a c
  rw [naimark_triple_entry]
  have hHerm : ((hE i).sqrt)ᴴ = (hE i).sqrt := (hE i).posSemidef_sqrt.1.eq
  have hentry : ∀ t : Fin n, star ((hE i).sqrt t a) = (hE i).sqrt a t := by
    intro t
    have := congrFun (congrFun hHerm a) t
    rwa [Matrix.conjTranspose_apply] at this
  -- Collapse the indicator `P i r s`: nonzero only when `s = (s.1, i)`, `r = (s.1, i)`.
  have hcollapse : ∀ s : Fin n × ι,
      (∑ r : Fin n × ι, star ((hE r.2).sqrt r.1 a) * naimarkProj i r s) * (hE s.2).sqrt s.1 c
      = (if s.2 = i then star ((hE i).sqrt s.1 a) * (hE i).sqrt s.1 c else 0) := by
    rintro ⟨s1, s2⟩
    by_cases hs2 : s2 = i
    · subst hs2
      rw [if_pos rfl, Finset.sum_eq_single (s1, s2)]
      · rw [naimarkProj_apply, if_pos ⟨rfl, rfl, rfl⟩, mul_one]
      · intro b _ hb
        rw [naimarkProj_apply, if_neg, mul_zero]
        rintro ⟨hb1, hb2, _⟩
        exact hb (Prod.ext hb1 hb2)
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · -- s2 ≠ i: every indicator term has second coord ≠ i, so all are 0
      rw [if_neg hs2]
      have hz : (∑ r : Fin n × ι, star ((hE r.2).sqrt r.1 a)
          * naimarkProj i r (s1, s2)) = 0 := by
        apply Finset.sum_eq_zero
        intro r _
        rw [naimarkProj_apply, if_neg, mul_zero]
        rintro ⟨_, _, hsi⟩
        exact hs2 hsi
      rw [hz, zero_mul]
  rw [Finset.sum_congr rfl (fun s _ => hcollapse s)]
  -- Now sum over s : Fin n × ι of the if; only s.2 = i survives, giving sum over Fin n.
  rw [show (∑ s : Fin n × ι, if s.2 = i then star ((hE i).sqrt s.1 a) * (hE i).sqrt s.1 c else 0)
      = ∑ t : Fin n, star ((hE i).sqrt t a) * (hE i).sqrt t c from ?_]
  · -- = ((√E_i)ᴴ √E_i) a c with √E_i Hermitian = (√E_i √E_i) a c = E_i a c
    have hEiac : E i a c = ∑ t : Fin n, (hE i).sqrt a t * (hE i).sqrt t c := by
      have h := congrFun (congrFun (hE i).sqrt_mul_self a) c
      rw [Matrix.mul_apply] at h
      exact h.symm
    rw [hEiac]
    exact Finset.sum_congr rfl (fun t _ => by rw [hentry t])
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
    · intro j _ hj; rw [if_neg hj]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem

omit [DecidableEq ι] in
/-- The Gram entry `(Vᴴ V) a c`, expanded as a scalar double sum (no rectangular product term). -/
theorem naimark_gram_entry (E : ι → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i, (E i).PosSemidef) (a c : Fin n) :
    naimarkGram E hE a c
      = ∑ x : Fin n × ι, star ((hE x.2).sqrt x.1 a) * (hE x.2).sqrt x.1 c := by
  rw [naimarkGram, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.conjTranspose_apply, naimarkV_apply, naimarkV_apply]

omit [DecidableEq ι] in
/-- **Naimark isometry**: `Vᴴ V = ∑_i E_i`, hence `= 1` for a genuine POVM. The dilation operator is an
isometry precisely because the POVM is complete (`∑ E_i = 1`). -/
theorem naimark_isometry (E : ι → Matrix (Fin n) (Fin n) ℂ) (hE : IsPOVM E) :
    naimarkGram E hE.1 = 1 := by
  have hsum : naimarkGram E hE.1 = ∑ i : ι, E i := by
    ext a c
    rw [naimark_gram_entry, Matrix.sum_apply]
    -- reindex Fin n × ι as ι × Fin n, then each i-block is (√E_i)ᴴ √E_i = E_i a c.
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hHerm : ((hE.1 i).sqrt)ᴴ = (hE.1 i).sqrt := (hE.1 i).posSemidef_sqrt.1.eq
    -- E i a c = (√E_i √E_i) a c, expanded as ∑ r, √E_i a r * √E_i r c, matched to the Gram sum.
    have hEiac : E i a c = ∑ r : Fin n, (hE.1 i).sqrt a r * (hE.1 i).sqrt r c := by
      have h := congrFun (congrFun (hE.1 i).sqrt_mul_self a) c
      rw [Matrix.mul_apply] at h
      exact h.symm
    rw [hEiac]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    have hentry : star ((hE.1 i).sqrt r a) = (hE.1 i).sqrt a r := by
      have := congrFun (congrFun hHerm a) r
      rwa [Matrix.conjTranspose_apply] at this
    rw [hentry]
  rw [hsum, hE.2]

/-! ### R5 non-vacuity for Naimark: the qubit computational-basis POVM. -/

/-- R5: the dilation of the PROVEN qubit computational-basis POVM is a genuine isometry. -/
theorem naimark_isometry_basisPOVM :
    naimarkGram basisPOVM isPOVM_basisPOVM.1 = 1 :=
  naimark_isometry basisPOVM isPOVM_basisPOVM

/-- R5: each qubit computational-basis effect is the Naimark compression of its PVM projection. -/
theorem naimark_compression_basisPOVM (i : Fin 2) :
    naimarkComp basisPOVM isPOVM_basisPOVM.1 i = basisPOVM i :=
  naimark_compression basisPOVM isPOVM_basisPOVM.1 i

end Naimark

/-! ## SP2-100 Choi–Jamiołkowski (finite): PSD ⟺ Gram/Choi, applied to the dephasing CP criterion.

QM ANALOGY (never asserted): a finite map is completely positive iff its Choi matrix is PSD.
-/

section Choi

/-- **Finite Choi–Jamiołkowski duality (the PSD ⟺ Gram form).** A finite Hermitian matrix is positive
semidefinite iff it is realized as the Choi/Gram matrix `Bᴴ B` of some operator `B`. This is the exact
finite content of channel–state duality as it is used: "PSD" is the Choi-positivity condition, and the
witness `B` is (a square root of) the dilation. Pure restatement of the PROVEN Mathlib engine to expose
the duality under an honest name. -/
theorem choiPSD_iff_isGram {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) :
    C.PosSemidef ↔ ∃ B : Matrix (Fin N) (Fin N) ℂ, C = Bᴴ * B :=
  Matrix.posSemidef_iff_eq_conjTranspose_mul_self

/-- The **qubit Choi matrix of the dephasing channel** `dephase γ`, i.e.
`C_Φ = ∑_{i,j} Eᵢⱼ ⊗ Φ_γ(Eᵢⱼ)` over `Fin 2 × Fin 2`, with the Choi convention
`C_{(i,k),(j,l)} = Φ_γ(Eᵢⱼ)_{kl}`. Since `Φ_γ(Eᵢⱼ) = γ Eᵢⱼ + (1-γ) diag(Eᵢⱼ)` and `diag(Eᵢⱼ)=δᵢⱼ Eᵢᵢ`,
the ONLY nonzero entries are
`C (0,0)(0,0) = 1`, `C (1,1)(1,1) = 1`, `C (0,0)(1,1) = γ`, `C (1,1)(0,0) = γ`:
the channel-state matrix lives entirely in the `{(0,0),(1,1)}` coherence sector as the block
`!![1, γ; γ, 1]`, and is zero on the `(0,1),(1,0)` sector (dephasing kills those coherences in `Φ`). -/
noncomputable def choiDephaseQubit (γ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q =>
    if p = (0,0) ∧ q = (0,0) then (1 : ℂ)
    else if p = (1,1) ∧ q = (1,1) then (1 : ℂ)
    else if p = (0,0) ∧ q = (1,1) then (γ : ℂ)
    else if p = (1,1) ∧ q = (0,0) then (γ : ℂ)
    else 0

@[simp] theorem choiDephaseQubit_apply (γ : ℝ) (p q : Fin 2 × Fin 2) :
    choiDephaseQubit γ p q =
      (if p = (0,0) ∧ q = (0,0) then (1 : ℂ)
       else if p = (1,1) ∧ q = (1,1) then (1 : ℂ)
       else if p = (0,0) ∧ q = (1,1) then (γ : ℂ)
       else if p = (1,1) ∧ q = (0,0) then (γ : ℂ)
       else 0) := rfl

/-- The three **Kraus column vectors** whose rank-1 outer products build the Choi matrix:
`w 0 = vec I = e₀₀ + e₁₁`, `w 1 = vec P₀ = e₀₀`, `w 2 = vec P₁ = e₁₁` (as `4×1` columns over
`Fin 2 × Fin 2`). These are `vec K_a` for the Kraus operators `K_0 = I`, `K_1 = P₀`, `K_2 = P₁`. -/
noncomputable def choiKrausVec : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 1) ℂ
  | 0 => Matrix.of fun p _ => if p = (0,0) ∨ p = (1,1) then (1 : ℂ) else 0
  | 1 => Matrix.of fun p _ => if p = (0,0) then (1 : ℂ) else 0
  | 2 => Matrix.of fun p _ => if p = (1,1) then (1 : ℂ) else 0

/-- **Kraus/Gram decomposition of the Choi matrix.** The dephasing Choi matrix is the nonnegative
combination of rank-1 PSD outer products `C_Φ = γ • (w₀ w₀ᴴ) + (1-γ) • (w₁ w₁ᴴ) + (1-γ) • (w₂ w₂ᴴ)`,
i.e. `∑_a |vec K_a⟩⟨vec K_a|` with weights `{γ, 1-γ, 1-γ}`. This is the Choi image of the Kraus form of
`dephase γ`. Verified entrywise. -/
theorem choiDephaseQubit_eq_kraus_sum (γ : ℝ) :
    choiDephaseQubit γ
      = (γ : ℂ) • (choiKrausVec 0 * (choiKrausVec 0)ᴴ)
        + ((1 - γ : ℝ) : ℂ) • (choiKrausVec 1 * (choiKrausVec 1)ᴴ)
        + ((1 - γ : ℝ) : ℂ) • (choiKrausVec 2 * (choiKrausVec 2)ᴴ) := by
  ext p q
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_one, choiKrausVec, Matrix.of_apply, choiDephaseQubit_apply, smul_eq_mul]
  fin_cases p <;> fin_cases q <;>
    simp only [Prod.mk.injEq, Fin.isValue] <;> norm_num [Complex.conj_ofReal]

/-- **CP side of finite Choi–Jamiołkowski for the dephasing channel.** For `0 ≤ γ ≤ 1` the qubit Choi
matrix is positive semidefinite, hence (by `choiPSD_iff_isGram`) the channel is completely positive. Proof:
the Kraus/Gram decomposition writes it as a nonnegative combination of rank-1 PSD outer products
`w_a w_aᴴ` (each PSD by `posSemidef_self_mul_conjTranspose`), and PSD is closed under nonnegative scaling
(`posSemidef_real_smul`) and addition (`PosSemidef.add`). No `decide` on positivity. -/
theorem choiDephaseQubit_posSemidef {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (choiDephaseQubit γ).PosSemidef := by
  rw [choiDephaseQubit_eq_kraus_sum]
  have hk : ∀ a : Fin 3, (choiKrausVec a * (choiKrausVec a)ᴴ).PosSemidef :=
    fun a => Matrix.posSemidef_self_mul_conjTranspose _
  exact ((posSemidef_real_smul_gen (hk 0) hγ0).add
    (posSemidef_real_smul_gen (hk 1) (by linarith))).add
    (posSemidef_real_smul_gen (hk 2) (by linarith))

/-- **Converse side of finite Choi–Jamiołkowski for the dephasing channel.** For `γ < -1` the qubit Choi
matrix is NOT positive semidefinite, so the map is NOT completely positive: the explicit witness vector
`x = e_{(0,0)} + e_{(1,1)}` gives quadratic form `⟨x, C x⟩ = 1 + γ + γ + 1 = 2(1 + γ) < 0`. We exhibit the
negative real dot product directly (no `decide` on positivity). This is the genuine non-CP witness for the
converse of the iff (the dephasing Choi block `!![1,γ;γ,1]` loses positivity exactly when `|γ| > 1`). -/
theorem choiDephaseQubit_not_posSemidef_of_lt {γ : ℝ} (hγ : γ < -1) :
    ¬ (choiDephaseQubit γ).PosSemidef := by
  intro hPSD
  -- Witness x = e₀₀ + e₁₁.
  set x : Fin 2 × Fin 2 → ℂ := fun p => if p = (0,0) ∨ p = (1,1) then (1 : ℂ) else 0 with hx
  have h := hPSD.2 x
  -- Compute ⟨x, C x⟩ = 2(1+γ) as a real number, then derive the contradiction with 0 ≤ ·.
  have hval : star x ⬝ᵥ (choiDephaseQubit γ *ᵥ x) = ((2 * (1 + γ) : ℝ) : ℂ) := by
    simp only [hx, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two,
      choiDephaseQubit_apply, Pi.star_apply, Prod.mk.injEq, Fin.isValue]
    norm_num [Complex.ext_iff]
    ring
  rw [hval] at h
  have : (0 : ℝ) ≤ 2 * (1 + γ) := by
    have := Complex.zero_le_real.mp h
    simpa using this
  linarith

/-- The **difference Kraus vector** `w₋ = e_{(0,0)} - e_{(1,1)}` (a `4×1` column over `Fin 2 × Fin 2`).
Its rank-1 outer product `w₋ w₋ᴴ` is the `!![1,-1;-1,1]` block on the `{(0,0),(1,1)}` coherence sector,
i.e. the `(1,-1)` eigenprojector of `!![1,γ;γ,1]`. -/
noncomputable def choiDiffVec : Matrix (Fin 2 × Fin 2) (Fin 1) ℂ :=
  Matrix.of fun p _ => if p = (0,0) then (1 : ℂ) else if p = (1,1) then (-1 : ℂ) else 0

/-- **Spectral (eigen) decomposition of the dephasing Choi matrix**, valid on the FULL CP region.
`C_Φ = (1+γ)/2 • (w₊ w₊ᴴ) + (1-γ)/2 • (w₋ w₋ᴴ)` with `w₊ = e₀₀ + e₁₁` (= `choiKrausVec 0`) and
`w₋ = e₀₀ - e₁₁` (= `choiDiffVec`). On the `{(0,0),(1,1)}` block this is the eigendecomposition of
`!![1,γ;γ,1]` into eigenvectors `(1,1)` (eigenvalue `1+γ`) and `(1,-1)` (eigenvalue `1-γ`), each halved.
Unlike the `{γ, 1-γ, 1-γ}` Kraus weights, BOTH coefficients here are nonnegative on the whole CP region
`-1 ≤ γ ≤ 1`. Verified entrywise. -/
theorem choiDephaseQubit_eq_spectral_sum (γ : ℝ) :
    choiDephaseQubit γ
      = (((1 + γ) / 2 : ℝ) : ℂ) • (choiKrausVec 0 * (choiKrausVec 0)ᴴ)
        + (((1 - γ) / 2 : ℝ) : ℂ) • (choiDiffVec * choiDiffVecᴴ) := by
  ext p q
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_one, choiKrausVec, choiDiffVec, Matrix.of_apply, choiDephaseQubit_apply,
    smul_eq_mul]
  fin_cases p <;> fin_cases q <;>
    simp only [Prod.mk.injEq, Fin.isValue] <;> norm_num [Complex.conj_ofReal] <;> ring

/-- **Full CP region (PSD side of the exact iff).** For the FULL completely-positive region
`-1 ≤ γ ≤ 1` the qubit dephasing Choi matrix is positive semidefinite, including the exact boundary
`γ = -1`. Proof: the spectral decomposition writes it as a nonnegative combination
`(1+γ)/2 • (w₊ w₊ᴴ) + (1-γ)/2 • (w₋ w₋ᴴ)` of rank-1 PSD outer products, with both coefficients
`(1±γ)/2 ≥ 0` on `-1 ≤ γ ≤ 1`. This strictly extends `choiDephaseQubit_posSemidef` (which covered only
`0 ≤ γ ≤ 1`) to the entire CP region. -/
theorem choiDephaseQubit_posSemidef_full {γ : ℝ} (hγ0 : -1 ≤ γ) (hγ1 : γ ≤ 1) :
    (choiDephaseQubit γ).PosSemidef := by
  rw [choiDephaseQubit_eq_spectral_sum]
  have h0 : (0 : ℝ) ≤ (1 + γ) / 2 := by linarith
  have h1 : (0 : ℝ) ≤ (1 - γ) / 2 := by linarith
  have hkp : (choiKrausVec 0 * (choiKrausVec 0)ᴴ).PosSemidef :=
    Matrix.posSemidef_self_mul_conjTranspose _
  have hkm : (choiDiffVec * choiDiffVecᴴ).PosSemidef :=
    Matrix.posSemidef_self_mul_conjTranspose _
  exact (posSemidef_real_smul_gen hkp h0).add (posSemidef_real_smul_gen hkm h1)

/-- **The exact `γ = -1` lower CP boundary.** At `γ = -1` the Choi matrix is PSD (the `(1+γ)/2`
eigenvalue is exactly `0`, so it is PSD but rank-deficient); combined with
`choiDephaseQubit_not_posSemidef_of_lt` (non-PSD for `γ < -1`), this pins `γ = -1` as the EXACT lower
edge of complete positivity. -/
theorem choiDephaseQubit_neg_one_posSemidef :
    (choiDephaseQubit (-1)).PosSemidef :=
  choiDephaseQubit_posSemidef_full (le_refl _) (by norm_num)

/-- **Converse for the upper boundary.** For `γ > 1` the Choi matrix is NOT positive semidefinite: the
witness `x = e_{(0,0)} - e_{(1,1)}` gives quadratic form `⟨x, C x⟩ = 1 - γ - γ + 1 = 2(1 - γ) < 0`. This
is the upper-edge mirror of `choiDephaseQubit_not_posSemidef_of_lt`; the dephasing Choi block
`!![1,γ;γ,1]` loses positivity exactly when `|γ| > 1`. -/
theorem choiDephaseQubit_not_posSemidef_of_gt {γ : ℝ} (hγ : 1 < γ) :
    ¬ (choiDephaseQubit γ).PosSemidef := by
  intro hPSD
  set x : Fin 2 × Fin 2 → ℂ :=
    fun p => if p = (0,0) then (1 : ℂ) else if p = (1,1) then (-1 : ℂ) else 0 with hx
  have h := hPSD.2 x
  have hval : star x ⬝ᵥ (choiDephaseQubit γ *ᵥ x) = ((2 * (1 - γ) : ℝ) : ℂ) := by
    simp only [hx, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two,
      choiDephaseQubit_apply, Pi.star_apply, Prod.mk.injEq, Fin.isValue]
    norm_num [Complex.ext_iff]
    ring
  rw [hval] at h
  have : (0 : ℝ) ≤ 2 * (1 - γ) := by
    have := Complex.zero_le_real.mp h
    simpa using this
  linarith

/-- **Exact finite Choi–Jamiołkowski CP criterion for the qubit dephasing channel (the full iff).**
`choiDephaseQubit γ` is positive semidefinite — equivalently (`choiPSD_iff_isGram`) the channel
`dephase γ` is completely positive — IF AND ONLY IF `-1 ≤ γ ≤ 1`. This closes the previous honest
residue (only `[0,1]` PSD and `γ < -1` non-PSD were formalized): the PSD region is now the full CP
interval with both exact boundaries `γ = -1` and `γ = 1` pinned. -/
theorem choiDephaseQubit_posSemidef_iff (γ : ℝ) :
    (choiDephaseQubit γ).PosSemidef ↔ -1 ≤ γ ∧ γ ≤ 1 := by
  constructor
  · intro hPSD
    refine ⟨?_, ?_⟩
    · by_contra h
      exact choiDephaseQubit_not_posSemidef_of_lt (by push_neg at h; exact h) hPSD
    · by_contra h
      exact choiDephaseQubit_not_posSemidef_of_gt (by push_neg at h; exact h) hPSD
  · rintro ⟨h0, h1⟩
    exact choiDephaseQubit_posSemidef_full h0 h1

end Choi

/-! ## SP2-98 Stinespring (finite): GENUINE compression half + general finite construction (abstract-CP-map converse scoped external, not a wall decl).

QM ANALOGY (never asserted): every finite CP channel is the partial trace of an isometric dilation.
-/

section Stinespring

open OperatorKO7.Meta.QuantumBoundary.FiniteDecoherenceChannel

variable {n : ℕ}

/-- **One Kraus/Stinespring leg preserves positivity.** The map `ρ ↦ K ρ Kᴴ` (a single Kraus term, the
elementary building block of a Stinespring dilation `ρ ↦ V ρ Vᴴ` followed by partial trace) sends
positive-semidefinite states to positive-semidefinite states. This is the structurally-honest half of
finite Stinespring that the carrier supports: positivity preservation flows from the dilation. -/
theorem kraus_apply_posSemidef {m : ℕ} (K : Matrix (Fin m) (Fin n) ℂ)
    {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.PosSemidef) :
    (K * ρ * Kᴴ).PosSemidef :=
  hρ.mul_mul_conjTranspose_same K

/-- The Kraus operator `√(1-γ) P₀` for the qubit dephasing channel, `P₀ = |0⟩⟨0|`. -/
noncomputable def krausP (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun j => if j = i then (1 : ℂ) else 0)

@[simp] theorem krausP_apply (i j k : Fin 2) :
    krausP i j k = if j = k then (if j = i then (1 : ℂ) else 0) else 0 := by
  simp [krausP, Matrix.diagonal_apply]

/-- The diagonal projectors `P i = |i⟩⟨i|` are Hermitian, so `(P i)ᴴ = P i`. -/
theorem krausP_isHermitian (i : Fin 2) : (krausP i)ᴴ = krausP i := by
  ext j k
  rw [Matrix.conjTranspose_apply, krausP_apply, krausP_apply]
  by_cases h : k = j
  · subst h; by_cases h2 : k = i <;> simp [h2]
  · rw [if_neg h, if_neg (fun hjk => h hjk.symm), star_zero]

/-- **The dephasing channel is in Kraus/Stinespring form (qubit).** Concretely,
`Φ_γ(ρ) = γ • ρ + (1-γ) • diag(ρ) = γ • ρ + (1-γ)•(P₀ ρ P₀) + (1-γ)•(P₁ ρ P₁)`, exhibiting the explicit
Kraus operators `{√γ·I, √(1-γ)·P₀, √(1-γ)·P₁}` (here the scalars are pulled out of the smul). The
column-stacking of these operators is the Stinespring isometry `V`; `dephase` is its partial-trace
compression. -/
theorem dephase_kraus (γ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dephase γ ρ
      = (γ : ℂ) • ρ + ((1 - γ : ℝ) : ℂ) • (krausP 0 * ρ * krausP 0)
        + ((1 - γ : ℝ) : ℂ) • (krausP 1 * ρ * krausP 1) := by
  unfold dephase
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, krausP_apply,
    Matrix.diagonal_apply, Matrix.diag_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp

/-- **Positivity preservation of `dephase` re-derived through the Kraus dilation (qubit).** Each Kraus
term `K_a ρ K_aᴴ` is PSD (`kraus_apply_posSemidef`), the nonnegative-scalar multiples are PSD
(`posSemidef_real_smul`), and PSD is closed under addition; so the dilation half closes the
operationally-substantive content of finite Stinespring on the concrete channel. -/
theorem dephase_kraus_posSemidef {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {ρ : Matrix (Fin 2) (Fin 2) ℂ} (hρ : ρ.PosSemidef) : (dephase γ ρ).PosSemidef := by
  rw [dephase_kraus]
  have h0 : ((1 - γ : ℝ) : ℂ) • (krausP 0 * ρ * krausP 0) |>.PosSemidef := by
    refine posSemidef_real_smul ?_ (by linarith)
    have := kraus_apply_posSemidef (krausP 0) hρ
    rwa [krausP_isHermitian 0] at this
  have h1 : ((1 - γ : ℝ) : ℂ) • (krausP 1 * ρ * krausP 1) |>.PosSemidef := by
    refine posSemidef_real_smul ?_ (by linarith)
    have := kraus_apply_posSemidef (krausP 1) hρ
    rwa [krausP_isHermitian 1] at this
  exact ((posSemidef_real_smul hρ hγ0).add h0).add h1

/-! ### SP2-98 general finite Stinespring (Kraus form): dilation isometry + compression identity (CLOSED).

The prior named wall is now CLOSED for the genuine constructive direction of finite Stinespring. A finite
completely-positive map presented in Kraus form `Φ(ρ) = ∑ₐ Kₐ ρ Kₐᴴ` has an explicit isometric dilation
`V` (the column-stacking of the Kraus family) with `Vᴴ V = ∑ₐ Kₐᴴ Kₐ` (an isometry exactly when the family
is trace-preserving), and `Φ` is recovered as the partial trace over the ancilla of the conjugation
`V ρ Vᴴ`. That is finite Stinespring on the Matrix surface, with no `sorry` and no axiom beyond the
baseline. The only part still EXTERNAL is the CONVERSE existence of a Kraus family for an ABSTRACT CP
linear map `Mₙ →ₗ Mₘ`, which needs the general linear-map carrier plus the Choi spectral decomposition (a
separate formalization, scoped here, not a hole in this construction).
QM ANALOGY (docstring only, never asserted): Stinespring's dilation theorem. -/

/-- A finite Kraus family's completely-positive map `Φ(ρ) = ∑ₐ Kₐ ρ Kₐᴴ`. -/
noncomputable def cpMapKraus {m k : ℕ} {ι : Type*} [Fintype ι] (K : ι → Matrix (Fin m) (Fin k) ℂ)
    (ρ : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ∑ a, K a * ρ * (K a)ᴴ

/-- **Complete positivity.** The Kraus map sends PSD to PSD: each leg `Kₐ ρ Kₐᴴ` is PSD and PSD is closed
under finite sums. -/
theorem cpMapKraus_posSemidef {m k : ℕ} {ι : Type*} [Fintype ι] (K : ι → Matrix (Fin m) (Fin k) ℂ)
    {ρ : Matrix (Fin k) (Fin k) ℂ} (hρ : ρ.PosSemidef) : (cpMapKraus K ρ).PosSemidef := by
  unfold cpMapKraus
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ h1 h2 => h1.add h2) ?_ ?_
  · exact ⟨Matrix.isHermitian_zero, fun x => by simp⟩
  · exact fun a _ => hρ.mul_mul_conjTranspose_same (K a)

/-- The **Stinespring dilation** of a Kraus family: column-stack the operators into
`V : Matrix (Fin m × ι) (Fin k)`, the `a`-ancilla block of rows being `Kₐ` (`V (i,a) j = Kₐ i j`). -/
def stinespringV {m k : ℕ} {ι : Type*} (K : ι → Matrix (Fin m) (Fin k) ℂ) :
    Matrix (Fin m × ι) (Fin k) ℂ :=
  Matrix.of fun p j => K p.2 p.1 j

@[simp] theorem stinespringV_apply {m k : ℕ} {ι : Type*} (K : ι → Matrix (Fin m) (Fin k) ℂ)
    (p : Fin m × ι) (j : Fin k) : stinespringV K p j = K p.2 p.1 j := rfl

/-- The Stinespring Gram operator is the trace-preserving sum: `Vᴴ V = ∑ₐ Kₐᴴ Kₐ`. -/
theorem stinespring_gram_eq {m k : ℕ} {ι : Type*} [Fintype ι] (K : ι → Matrix (Fin m) (Fin k) ℂ) :
    ((stinespringV K)ᴴ * stinespringV K : Matrix (Fin k) (Fin k) ℂ) = ∑ a, (K a)ᴴ * K a := by
  ext j l
  rw [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.conjTranspose_apply, stinespringV_apply, Matrix.conjTranspose_apply, stinespringV_apply]

/-- **Finite Stinespring dilation.** `V` is an isometry (`Vᴴ V = 1`) exactly when the Kraus family is
trace-preserving (`∑ₐ Kₐᴴ Kₐ = 1`): a finite trace-preserving CP map dilates to an isometry. -/
theorem stinespring_isometry {m k : ℕ} {ι : Type*} [Fintype ι] (K : ι → Matrix (Fin m) (Fin k) ℂ)
    (hTP : (∑ a, (K a)ᴴ * K a : Matrix (Fin k) (Fin k) ℂ) = 1) :
    ((stinespringV K)ᴴ * stinespringV K : Matrix (Fin k) (Fin k) ℂ) = 1 := by
  rw [stinespring_gram_eq, hTP]

/-- The partial trace over the ancilla `ι`: `(ptr M) i k = ∑ₐ M (i,a) (k,a)`. -/
noncomputable def partialTraceAncilla {m : ℕ} {ι : Type*} [Fintype ι]
    (M : Matrix (Fin m × ι) (Fin m × ι) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => ∑ a, M (i, a) (j, a)

/-- **Stinespring dilation identity.** The Kraus map is the partial trace over the ancilla of the
conjugation by `V`: `Φ(ρ) = Tr_ancilla (V ρ Vᴴ)`. With `stinespring_isometry`, this IS finite Stinespring
(`Φ(·) = Tr_anc (V (·) Vᴴ)` with `V` an isometry). -/
theorem stinespring_dilates {m k : ℕ} {ι : Type*} [Fintype ι] (K : ι → Matrix (Fin m) (Fin k) ℂ)
    (ρ : Matrix (Fin k) (Fin k) ℂ) :
    cpMapKraus K ρ = partialTraceAncilla (stinespringV K * ρ * (stinespringV K)ᴴ) := by
  ext i j
  rw [cpMapKraus, Matrix.sum_apply, partialTraceAncilla, Matrix.of_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, stinespringV_apply]

/-- R5: the qubit projective-measurement Kraus family `{P₀, P₁}` is trace-preserving
(`∑ᵢ Pᵢᴴ Pᵢ = ∑ᵢ Pᵢ = 1`). -/
theorem meas_kraus_isTP :
    (∑ i : Fin 2, (krausP i)ᴴ * krausP i : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [Fin.sum_univ_two, krausP_isHermitian 0, krausP_isHermitian 1]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [krausP_apply, Matrix.mul_apply, Matrix.add_apply]

/-- **R5 (non-vacuity): a genuine 2-Kraus channel dilates to an isometry.** The projective-measurement
channel `{P₀, P₁}` (a real, non-trivial finite CP map) has an isometric Stinespring dilation. So the
general construction is inhabited, not vacuous. -/
theorem meas_stinespring_isometry :
    ((stinespringV (fun i : Fin 2 => krausP i))ᴴ * stinespringV (fun i : Fin 2 => krausP i)
      : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
  stinespring_isometry _ meas_kraus_isTP

end Stinespring

/-! ## Headline axiom audit (#print axioms on every public headline). -/

-- Naimark (genuine full construction)
#print axioms naimarkProj_isHermitian
#print axioms naimarkProj_idempotent
#print axioms naimarkProj_orthogonal
#print axioms naimarkProj_sum_eq_one
#print axioms naimark_compression
#print axioms naimark_isometry
#print axioms naimark_isometry_basisPOVM
#print axioms naimark_compression_basisPOVM

-- Choi–Jamiołkowski (genuine duality + dephasing CP criterion)
#print axioms choiPSD_iff_isGram
#print axioms choiDephaseQubit_posSemidef
#print axioms choiDephaseQubit_not_posSemidef_of_lt
#print axioms choiDephaseQubit_eq_spectral_sum
#print axioms choiDephaseQubit_posSemidef_full
#print axioms choiDephaseQubit_neg_one_posSemidef
#print axioms choiDephaseQubit_not_posSemidef_of_gt
#print axioms choiDephaseQubit_posSemidef_iff

-- Stinespring (general finite construction + concrete dephasing channel)
#print axioms kraus_apply_posSemidef
#print axioms dephase_kraus
#print axioms dephase_kraus_posSemidef
#print axioms cpMapKraus_posSemidef
#print axioms stinespring_gram_eq
#print axioms stinespring_isometry
#print axioms stinespring_dilates
#print axioms meas_kraus_isTP
#print axioms meas_stinespring_isometry

end OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation
