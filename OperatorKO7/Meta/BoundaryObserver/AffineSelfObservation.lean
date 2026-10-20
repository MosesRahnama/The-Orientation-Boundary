import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive

/-!
# Source-bound certificates for affine self-observation

Proof graph: OBSERVATION-EXTENSIONS-PROOF-GRAPH.md, AS1-AS3.
Reading ledger: SYN-016, SYN-023, SYN-024. A finite family of linear equations is the
retained observation. Kernel vectors are the indistinguishable changes of state.
The scalar field is arbitrary; Boolean affine equations are the ZMod 2 instance.
This proves certificate soundness and existence, not the Python elimination implementation.
-/

set_option autoImplicit false
open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation

open OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive

section Linear
variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

/-- The differences invisible to a linear observer are exactly its kernel. -/
theorem observation_eq_iff_kernel_difference (M : V →ₗ[K] W) (x y : V) :
    M x = M y ↔ M (x - y) = 0 := by
  rw [map_sub, sub_eq_zero]

/-- An inhabited affine fiber is precisely one solution translated by the kernel. -/
theorem solution_iff_kernel_translate (M : V →ₗ[K] W) (b : W) (p x : V)
    (hp : M p = b) : M x = b ↔ ∃ k, M k = 0 ∧ x = p + k := by
  constructor
  · intro hx
    refine ⟨x - p, by rw [map_sub, hx, hp, sub_self], ?_⟩
    abel
  · rintro ⟨k, hk, rfl⟩
    rw [map_add, hp, hk, add_zero]

/-- A linear target is forced on a nonempty fiber exactly when every invisible change
has zero target value. Nonemptiness is witnessed by p, not hidden in the definition. -/
theorem target_forced_iff_kernel (M : V →ₗ[K] W) (L : V →ₗ[K] K)
    (b : W) (p : V) (hp : M p = b) :
    (∀ x, M x = b → L x = L p) ↔ ∀ k, M k = 0 → L k = 0 := by
  constructor
  · intro h k hk
    have he := h (p + k) (by rw [map_add, hp, hk, add_zero])
    have he' : L p + L k = L p + 0 := by simpa only [map_add, add_zero] using he
    exact add_left_cancel he'
  · intro h x hx
    obtain ⟨k, hk, rfl⟩ := (solution_iff_kernel_translate M b p x hp).mp hx
    rw [map_add, h k hk, add_zero]

/-- Failure of the kernel criterion produces actual states of the existing boundary carrier. -/
def kernelBoundary (M : V →ₗ[K] W) (L : V →ₗ[K] K) (p k : V)
    (hk : M k = 0) (hL : L k ≠ 0) : TypedBoundary where
  State := V
  Obs := W
  Verdict := K
  observe := M
  verdict := L
  s₁ := p
  s₂ := p + k
  obs_eq := by rw [map_add, hk, add_zero]
  verdict_ne := by
    intro h
    apply hL
    have h' : L p + L k = L p + 0 := by simpa only [map_add, add_zero] using h.symm
    exact add_left_cancel h'

/-- The generic observer-boundary no-go applies to the actual affine collision. -/
theorem kernel_witness_excludes_readout (M : V →ₗ[K] W) (L : V →ₗ[K] K)
    (p k : V) (hk : M k = 0) (hL : L k ≠ 0) :
    ¬ ∃ f : W → K, ∀ x, L x = f (M x) :=
  (kernelBoundary M L p k hk hL).verdict_not_observation_function

/-- A supplied left-annihilator with a nonzero value at b refutes every source solution. -/
theorem annihilator_refutes (M : V →ₗ[K] W) (b : W) (l : W →ₗ[K] K)
    (hzero : l.comp M = 0) (hb : l b ≠ 0) : ¬ ∃ x, M x = b := by
  rintro ⟨x, hx⟩
  apply hb
  have h := LinearMap.congr_fun hzero x
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, hx] using h

/-- A left-annihilator certificate exists for every b outside the actual linear range. -/
theorem no_solution_iff_annihilator (M : V →ₗ[K] W) (b : W) :
    (¬ ∃ x, M x = b) ↔ ∃ l : W →ₗ[K] K, l.comp M = 0 ∧ l b ≠ 0 := by
  constructor
  · intro hn
    have hb : b ∉ LinearMap.range M := by simpa only [LinearMap.mem_range] using hn
    obtain ⟨l, hl, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hb inferInstance
    refine ⟨l, ?_, hl⟩
    ext x
    have hm : l (M x) ∈ Submodule.map l (LinearMap.range M) :=
      Submodule.mem_map.mpr ⟨M x, LinearMap.mem_range.mpr ⟨x, rfl⟩, rfl⟩
    rw [hmap] at hm
    exact hm
  · rintro ⟨l, hzero, hb⟩
    exact annihilator_refutes M b l hzero hb

end Linear

section Rows
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype I]

/-- The right side is bound to every original equation, not to a transformed problem. -/
def Satisfies (rows : I → V →ₗ[K] K) (b : I → K) (x : V) : Prop :=
  ∀ i, rows i x = b i

/-- A source-row linear combination proves a target value on every source solution. -/
theorem row_certificate_sound (rows : I → V →ₗ[K] K) (L : V →ₗ[K] K)
    (b c : I → K) (hc : ∑ i, c i • rows i = L) (x : V) (hx : Satisfies rows b x) :
    L x = ∑ i, c i * b i := by
  have h := LinearMap.congr_fun hc x
  have hx' : ∀ i, rows i x = b i := hx
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hx'] using h.symm

/-- Every target forced by finitely many linear equations has a row-combination certificate.
The space of unknowns need not be finite-dimensional. -/
theorem target_forced_iff_row_certificate (rows : I → V →ₗ[K] K)
    (L : V →ₗ[K] K) (b : I → K) (p : V) (hp : Satisfies rows b p) :
    (∀ x, Satisfies rows b x → L x = L p) ↔ ∃ c : I → K, ∑ i, c i • rows i = L := by
  constructor
  · intro h
    have hk : (⨅ i, LinearMap.ker (rows i)) ≤ LinearMap.ker L := by
      intro k hm
      have hki (i : I) : rows i k = 0 := (Submodule.mem_iInf _).mp hm i
      have he := h (p + k) (by intro i; rw [map_add, hp i, hki i, add_zero])
      change L k = 0
      have he' : L p + L k = L p + 0 := by simpa only [map_add, add_zero] using he
      exact add_left_cancel he'
    exact (Submodule.mem_span_range_iff_exists_fun K).mp (mem_span_of_iInf_ker_le_ker hk)
  · rintro ⟨c, hc⟩ x hx
    exact (row_certificate_sound rows L b c hc x hx).trans
      (row_certificate_sound rows L b c hc p hp).symm

/-- The proof-producing alternative to a forced value is a checked invisible displacement. -/
theorem no_row_certificate_iff_kernel_witness (rows : I → V →ₗ[K] K)
    (L : V →ₗ[K] K) :
    (¬ ∃ c : I → K, ∑ i, c i • rows i = L) ↔
      ∃ k, (∀ i, rows i k = 0) ∧ L k ≠ 0 := by
  classical
  constructor
  · intro h
    by_contra hn
    have hk : (⨅ i, LinearMap.ker (rows i)) ≤ LinearMap.ker L := by
      intro k hm
      change L k = 0
      by_contra hl
      exact hn ⟨k, fun i => (Submodule.mem_iInf _).mp hm i, hl⟩
    exact h ((Submodule.mem_span_range_iff_exists_fun K).mp (mem_span_of_iInf_ker_le_ker hk))
  · rintro ⟨k, hk, hl⟩ ⟨c, hc⟩
    apply hl
    simpa using row_certificate_sound rows L (fun _ => 0) c hc k hk

/-- The two alternatives cannot hold together. -/
theorem forced_or_kernel_witness (rows : I → V →ₗ[K] K) (L : V →ₗ[K] K) :
    (∃ c : I → K, ∑ i, c i • rows i = L) ∨
    (∃ k, (∀ i, rows i k = 0) ∧ L k ≠ 0) := by
  classical
  by_cases h : ∃ c : I → K, ∑ i, c i • rows i = L
  · exact Or.inl h
  · exact Or.inr ((no_row_certificate_iff_kernel_witness rows L).mp h)

/-- A row combination with zero left side and nonzero right side is an inconsistency receipt. -/
theorem inconsistent_row_certificate (rows : I → V →ₗ[K] K) (b c : I → K)
    (hzero : ∑ i, c i • rows i = 0) (hb : ∑ i, c i * b i ≠ 0) :
    ¬ ∃ x, Satisfies rows b x := by
  rintro ⟨x, hx⟩
  exact hb (row_certificate_sound rows 0 b c hzero x hx).symm

/-- Every inconsistency in finitely many linear equations has a source-row certificate.
This is an existence theorem over a field, not a bound on the cost of finding the coefficients. -/
theorem no_solution_iff_row_refutation (rows : I → V →ₗ[K] K) (b : I → K) :
    (¬ ∃ x, Satisfies rows b x) ↔
      ∃ c : I → K, (∑ i, c i • rows i) = 0 ∧ (∑ i, c i * b i) ≠ 0 := by
  constructor
  · intro hn
    have hn' : ¬ ∃ x, LinearMap.pi rows x = b := by
      rintro ⟨x, hx⟩
      exact hn ⟨x, fun i => congrFun hx i⟩
    obtain ⟨l, hcomp, hb⟩ := (no_solution_iff_annihilator (LinearMap.pi rows) b).mp hn'
    let proj : I → (I → K) →ₗ[K] K := fun i => LinearMap.proj i
    have hk : (⨅ i, LinearMap.ker (proj i)) ≤ LinearMap.ker l := by
      intro z hz
      have he : z = 0 := by
        funext i
        exact (Submodule.mem_iInf _).mp hz i
      change l z = 0
      rw [he, map_zero]
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
      (mem_span_of_iInf_ker_le_ker hk)
    have hl (z : I → K) : l z = ∑ i, c i * z i := by
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        proj, LinearMap.proj_apply] using (LinearMap.congr_fun hc z).symm
    refine ⟨c, ?_, ?_⟩
    · ext x
      have h := LinearMap.congr_fun hcomp x
      simpa only [LinearMap.comp_apply, hl, LinearMap.pi_apply, LinearMap.zero_apply,
        LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using h
    · rw [← hl b]
      exact hb
  · rintro ⟨c, hzero, hb⟩
    exact inconsistent_row_certificate rows b c hzero hb

/-- Every finite linear observation has a certificate of inconsistency, a forced-target
certificate with a solution, or a solution and an invisible target-changing direction. -/
theorem source_certificate_trichotomy (rows : I → V →ₗ[K] K) (b : I → K)
    (L : V →ₗ[K] K) :
    (∃ c : I → K, (∑ i, c i • rows i) = 0 ∧ (∑ i, c i * b i) ≠ 0) ∨
    (∃ (p : V) (c : I → K), Satisfies rows b p ∧ (∑ i, c i • rows i) = L) ∨
    (∃ p k, Satisfies rows b p ∧ (∀ i, rows i k = 0) ∧ L k ≠ 0) := by
  classical
  by_cases hs : ∃ p, Satisfies rows b p
  · obtain ⟨p, hp⟩ := hs
    rcases forced_or_kernel_witness rows L with ⟨c, hc⟩ | ⟨k, hk, hl⟩
    · exact Or.inr (Or.inl ⟨p, c, hp, hc⟩)
    · exact Or.inr (Or.inr ⟨p, k, hp, hk, hl⟩)
  · exact Or.inl ((no_solution_iff_row_refutation rows b).mp hs)

omit [Fintype I] in
/-- A nonzero target displacement yields two source solutions with unequal target values. -/
theorem ambiguity_certificate_sound (rows : I → V →ₗ[K] K) (b : I → K)
    (L : V →ₗ[K] K) (p k : V) (hp : Satisfies rows b p)
    (hk : ∀ i, rows i k = 0) (hl : L k ≠ 0) :
    Satisfies rows b (p + k) ∧ L p ≠ L (p + k) := by
  refine ⟨fun i => by rw [map_add, hp i, hk i, add_zero], ?_⟩
  intro he
  apply hl
  have he' : L p + L k = L p + 0 := by simpa only [map_add, add_zero] using he.symm
  exact add_left_cancel he'

omit [Fintype I] in
/-- Reversible changes to the retained equation vector preserve every target fiber exactly. -/
theorem equivalent_equation_readout {J : Type}
    (M : V →ₗ[K] (I → K)) (R : (I → K) ≃ₗ[K] (J → K)) (b : I → K) (x : V) :
    R (M x) = R b ↔ M x = b := R.injective.eq_iff

end Rows

/-! ## Three Boolean systems with the same unresolved local update -/

/-- A pair of defining Boolean expressions. -/
def boolEquations (mode : Fin 3) (x y : Bool) : Prop :=
  x = y ∧ match mode.val with
    | 0 => y = x
    | 1 => y = !x
    | _ => y = (x ^^ y)

/-- The local update retains None when a required input is unresolved. -/
def localUpdate (mode : Fin 3) (v : Option Bool × Option Bool) : Option Bool × Option Bool :=
  (v.2, match mode.val with
    | 0 => v.1
    | 1 => v.1.map Bool.not
    | _ => do let x ← v.1; let y ← v.2; pure (x ^^ y))

theorem localUpdate_bottom (mode : Fin 3) : localUpdate mode (none, none) = (none, none) := by
  fin_cases mode <;> rfl

theorem copy_solutions (x y : Bool) :
    boolEquations 0 x y ↔ (x = false ∧ y = false) ∨ (x = true ∧ y = true) := by
  cases x <;> cases y <;> unfold boolEquations <;> decide

theorem negation_no_solution : ¬ ∃ x y, boolEquations 1 x y := by
  unfold boolEquations
  decide

theorem cancellation_unique_solution (x y : Bool) :
    boolEquations 2 x y ↔ x = false ∧ y = false := by
  cases x <;> cases y <;> unfold boolEquations <;> decide

/-- The bottom-only record cannot even distinguish consistency from inconsistency. -/
def localDiagnosticBoundary : TypedBoundary where
  State := Fin 3
  Obs := Option Bool × Option Bool
  Verdict := Prop
  observe := fun mode => localUpdate mode (none, none)
  verdict := fun mode => ∃ x y, boolEquations mode x y
  s₁ := 0
  s₂ := 1
  obs_eq := rfl
  verdict_ne := by
    intro h
    have h0 : ∃ x y, boolEquations 0 x y := ⟨false, false, by unfold boolEquations; decide⟩
    exact negation_no_solution (h ▸ h0)

theorem no_bottom_only_consistency_detector :
    ¬ ∃ read : (Option Bool × Option Bool) → Prop,
      ∀ mode : Fin 3, (∃ x y, boolEquations mode x y) =
        read (localUpdate mode (none, none)) :=
  localDiagnosticBoundary.verdict_not_observation_function

/-! ## The same examples inside the linear certificate model -/

abbrev Bit := ZMod 2

def bit (b : Bool) : Bit := if b then 1 else 0

def affineRows (mode : Fin 3) (i : Fin 2) : (Bit × Bit) →ₗ[Bit] Bit :=
  if i.val = 0 then LinearMap.fst Bit Bit Bit + LinearMap.snd Bit Bit Bit
  else if mode.val = 2 then LinearMap.fst Bit Bit Bit
  else LinearMap.fst Bit Bit Bit + LinearMap.snd Bit Bit Bit

def affineRhs (mode : Fin 3) (i : Fin 2) : Bit := if mode.val = 1 ∧ i.val = 1 then 1 else 0

/-- The Boolean examples and the field equations have exactly the same solutions. -/
theorem bool_equations_linear_iff (mode : Fin 3) (x y : Bool) :
    boolEquations mode x y ↔ Satisfies (affineRows mode) (affineRhs mode) (bit x, bit y) := by
  fin_cases mode <;> cases x <;> cases y <;>
    unfold boolEquations Satisfies <;> decide

/-- The cancellation system's second row certifies x, and the sum of its rows certifies y. -/
theorem cancellation_row_certificates :
    affineRows 2 1 = LinearMap.fst Bit Bit Bit ∧
    affineRows 2 0 + affineRows 2 1 = LinearMap.snd Bit Bit Bit := by
  constructor
  · rfl
  · apply LinearMap.ext
    intro v
    change (v.1 + v.2) + v.1 = v.2
    have ht : (2 : Bit) = 0 := by decide
    calc
      _ = (2 : Bit) * v.1 + v.2 := by ring
      _ = v.2 := by rw [ht, zero_mul, zero_add]

/-- In the negating cycle the sum of the two source rows is zero, but the right sum is one. -/
theorem negation_row_refutation :
    affineRows 1 0 + affineRows 1 1 = 0 ∧ affineRhs 1 0 + affineRhs 1 1 = 1 := by
  constructor
  · apply LinearMap.ext
    intro v
    change (v.1 + v.2) + (v.1 + v.2) = 0
    have ht : (2 : Bit) = 0 := by decide
    calc
      _ = (2 : Bit) * (v.1 + v.2) := by ring
      _ = 0 := by rw [ht, zero_mul]
  · norm_num [affineRhs]

/-- The two copy-cycle solutions differ by an actual nonzero kernel vector. -/
theorem copy_kernel_vector :
    Satisfies (affineRows 0) (affineRhs 0) (0, 0) ∧
    Satisfies (affineRows 0) (affineRhs 0) (1, 1) ∧
    (LinearMap.fst Bit Bit Bit) (1, 1) ≠ 0 := by
  unfold Satisfies
  decide

/-- Every kernel vector acts by a record-preserving translation permutation.
A nonzero kernel vector sends each state to a distinct state with the same record. -/
theorem kernel_translation_invisible {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (M : V →ₗ[K] W) (v : V) (hv : v ∈ LinearMap.ker M) :
    (Equiv.addRight v : Equiv.Perm V) ∈
      {σ : Equiv.Perm V | ∀ x : V, M (σ x) = M x} ∧
    (v ≠ 0 → ∀ x : V, x ≠ x + v ∧ M x = M (x + v)) := by
  have hker : M v = 0 := (LinearMap.mem_ker).mp hv
  have hmap (x : V) : M (x + v) = M x := by
    rw [map_add, hker, add_zero]
  constructor
  · intro x
    exact hmap x
  · intro hn x
    refine ⟨?_, (hmap x).symm⟩
    intro he
    apply hn
    have he' : x + v = x + 0 := by simpa only [add_zero] using he.symm
    exact add_left_cancel he'

end OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation
