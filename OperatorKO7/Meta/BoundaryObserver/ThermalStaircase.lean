import OperatorKO7.Meta.BoundaryObserver.ThermalReset
import OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction

set_option autoImplicit false

/-!
# The Landauer bound as the infimum of finite heat: the staircase of Gibbs swaps

A staircase is a finite list of reservoir Hamiltonians on copies of the system carrier; step k swaps
the system with a fresh reservoir in its Gibbs state, so the system leaves step k in the Gibbs state
of reservoir k and the heat of step k is the reservoir heat of the existing definition. The total
heat obeys β Q = S(ρ) − S(final) + Σ D(ρ_{k−1} ‖ γ_k). In the eigenbasis of ρ every strictly positive
spectrum q is the Gibbs state of the Hamiltonian with levels −log(q i)/β, the relative entropy of
two spectra in one basis is their Kullback-Leibler divergence, and that divergence is at most the
chi-square divergence. A straight path of N steps from a slight mixture of ρ to a nearly pure
spectrum has total chi-square at most a constant over N, so a finite staircase (the route of Reeb
and Wolf, New J. Phys. 16, 103011, 2014) leaves entropy below η at β Q at most S(ρ) − S(final) + η.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ThermalStaircase

open Matrix
open BoundaryReconstruction.Thermal
open BoundarySingularity.Thermal
open ThermalReset
open Filter Topology
open scoped Kronecker ComplexOrder BigOperators

noncomputable section

/-- A reservoir Hamiltonian on a copy of the system carrier, carried with its Hermitian proof. -/
abbrev Hamiltonian (ι : Type) := {h : Matrix ι ι ℂ // h.IsHermitian}

/-! ## The sequential staircase and its exact heat balance -/

section Sequential
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The system state after the listed swaps, applied in list order: each step is the existing
thermal operation of the swap with a fresh reservoir in the Gibbs state of its Hamiltonian. -/
def stairOutput (β : ℝ) : List (Hamiltonian ι) → Matrix ι ι ℂ → Matrix ι ι ℂ
  | [], rho => rho
  | H :: L, rho => stairOutput β L (marginalLeft (thermalJoint swapUnitary rho H.2 β))

/-- The total heat of the staircase: the sum of the per-step reservoir heats. -/
def stairHeat (β : ℝ) : List (Hamiltonian ι) → Matrix ι ι ℂ → ℝ
  | [], _ => 0
  | H :: L, rho => reservoirHeat swapUnitary rho H.2 β +
      stairHeat β L (marginalLeft (thermalJoint swapUnitary rho H.2 β))

/-- The sum of the per-step Landauer deficits D(ρ_{k−1} ‖ γ_k), each against the Gibbs state of
the reservoir of that step. -/
def stairDeficit (β : ℝ) : List (Hamiltonian ι) → Matrix ι ι ℂ → ℝ
  | [], _ => 0
  | H :: L, rho => relativeEntropy rho (gibbsState H.2 β) + stairDeficit β L (gibbsState H.2 β)

/-- A unit-trace input leaves the first swap in the Gibbs state of the first reservoir. -/
theorem stairOutput_cons (β : ℝ) (H : Hamiltonian ι) (L : List (Hamiltonian ι))
    {rho : Matrix ι ι ℂ} (htr : rho.trace = 1) :
    stairOutput β (H :: L) rho = stairOutput β L (gibbsState H.2 β) := by
  simp only [stairOutput, swap_output rho htr H.2 β]

theorem stairHeat_cons (β : ℝ) (H : Hamiltonian ι) (L : List (Hamiltonian ι))
    {rho : Matrix ι ι ℂ} (htr : rho.trace = 1) :
    stairHeat β (H :: L) rho =
      reservoirHeat swapUnitary rho H.2 β + stairHeat β L (gibbsState H.2 β) := by
  simp only [stairHeat, swap_output rho htr H.2 β]

/-- The exact balance of the staircase: β Q = S(ρ) − S(final) + Σ D(ρ_{k−1} ‖ γ_k), with every
deficit nonnegative. -/
theorem stair_balance (β : ℝ) (L : List (Hamiltonian ι)) {rho : Matrix ι ι ℂ}
    (hrho : rho.PosSemidef) (htr : rho.trace = 1) :
    β * stairHeat β L rho =
        entropy rho - entropy (stairOutput β L rho) + stairDeficit β L rho ∧
      0 ≤ stairDeficit β L rho := by
  induction L generalizing rho with
  | nil =>
    simp only [stairHeat, stairOutput, stairDeficit]
    exact ⟨by ring, le_rfl⟩
  | cons H L ih =>
    obtain ⟨hb, hd⟩ := swap_balance rho hrho htr H.2 β
    obtain ⟨hi, hid⟩ := ih (gibbsState_posDef H.2 β).posSemidef (gibbsState_trace H.2 β)
    rw [stairHeat_cons β H L htr, stairOutput_cons β H L htr]
    simp only [stairDeficit]
    refine ⟨?_, add_nonneg hd hid⟩
    rw [mul_add, hb, hi]
    ring

/-- The Landauer lower bound for every staircase. -/
theorem stair_landauer (β : ℝ) (L : List (Hamiltonian ι)) {rho : Matrix ι ι ℂ}
    (hrho : rho.PosSemidef) (htr : rho.trace = 1) :
    entropy rho - entropy (stairOutput β L rho) ≤ β * stairHeat β L rho := by
  obtain ⟨hb, hd⟩ := stair_balance β L hrho htr
  linarith

/-- Appending a last reservoir fixes the final system state to its Gibbs state. -/
theorem stairOutput_append_single (β : ℝ) (H : Hamiltonian ι) (L : List (Hamiltonian ι))
    {rho : Matrix ι ι ℂ} (htr : rho.trace = 1) :
    stairOutput β (L ++ [H]) rho = gibbsState H.2 β := by
  induction L generalizing rho with
  | nil =>
    rw [List.nil_append, stairOutput_cons β H [] htr]
    rfl
  | cons H' L ih =>
    rw [List.cons_append, stairOutput_cons β H' _ htr]
    exact ih (gibbsState_trace H'.2 β)

end Sequential

/-! ## Gibbs reservoirs for every strictly positive spectrum, and the divergences -/

section Spectral
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The reservoir Hamiltonian with levels −log(q i)/β in the basis u. -/
def levelHamiltonian (u : Matrix.unitaryGroup ι ℂ) (β : ℝ) (q : ι → ℝ) : Hamiltonian ι :=
  ⟨spectralLift u (fun i => -Real.log (q i) / β), spectralLift_hermitian u _⟩

/-- A strictly positive probability vector. -/
def FullSpectrum (q : ι → ℝ) : Prop := (∀ i, 0 < q i) ∧ ∑ i, q i = 1

/-- Every strictly positive spectrum in the basis u is the Gibbs state at inverse temperature β of
its level Hamiltonian. -/
theorem levelHamiltonian_gibbs (u : Matrix.unitaryGroup ι ℂ) {β : ℝ} (hβ : β ≠ 0)
    {q : ι → ℝ} (hq : FullSpectrum q) :
    gibbsState (levelHamiltonian u β q).2 β = spectralLift u q := by
  have he : ∀ i, -β * (-Real.log (q i) / β) = Real.log (q i) := by
    intro i
    have hr : -β * (-Real.log (q i) / β) = Real.log (q i) * (β / β) := by ring
    rw [hr, div_self hβ, mul_one]
  have hexp : ∀ i, Real.exp (Real.log (q i)) = q i := fun i => Real.exp_log (hq.1 i)
  have hw : gibbsWeight β (fun i => -Real.log (q i) / β) = q := by
    funext i
    simp only [gibbsWeight, partition, he, hexp, hq.2, div_one]
  calc
    gibbsState (levelHamiltonian u β q).2 β =
        spectralLift u (gibbsWeight β (fun i => -Real.log (q i) / β)) :=
      gibbsState_spectralLift u _ β
    _ = spectralLift u q := by rw [hw]

/-- The Kullback-Leibler divergence of two spectra, in nats. -/
def klDiv (p q : ι → ℝ) : ℝ := -(∑ i, Real.negMulLog (p i)) - ∑ i, p i * Real.log (q i)

/-- The chi-square divergence of two spectra. -/
def chiSq (p q : ι → ℝ) : ℝ := ∑ i, (p i - q i) ^ 2 / q i

omit [Fintype ι] in
theorem basisWeight_one (i j : ι) :
    basisWeight (1 : Matrix ι ι ℂ) i j = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simp [basisWeight]
  · simp [basisWeight, h]

/-- In one basis the matrix relative entropy is the Kullback-Leibler divergence of the spectra. -/
theorem relativeEntropy_common_basis (u : Matrix.unitaryGroup ι ℂ) (p q : ι → ℝ) :
    relativeEntropy (spectralLift u p) (spectralLift u q) = klDiv p q := by
  rw [relativeEntropy_spectralLift, unitary.coe_star_mul_self]
  simp only [basisWeight_one, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, klDiv]

/-- One term of the divergence bound: a log(a/b) ≤ (a − b)²/b + a − b. -/
theorem kl_term_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    -Real.negMulLog a - a * Real.log b ≤ (a - b) ^ 2 / b + a - b := by
  rcases ha.eq_or_lt with h | h
  · subst h
    have h2 : (0 - b) ^ 2 / b = b := by
      rw [zero_sub, neg_sq, sq, mul_self_div_self]
    rw [h2, Real.negMulLog_zero]
    linarith
  · have key : (a - b) ^ 2 / b + a - b = a * (a / b - 1) := by
      field_simp
      ring
    calc
      -Real.negMulLog a - a * Real.log b = a * (Real.log a - Real.log b) := by
        simp only [Real.negMulLog]
        ring
      _ = a * Real.log (a / b) := by rw [Real.log_div h.ne' hb.ne']
      _ ≤ a * (a / b - 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos h hb)) h.le
      _ = _ := key.symm

omit [DecidableEq ι] in
/-- The Kullback-Leibler divergence is at most the chi-square divergence. -/
theorem klDiv_le_chiSq {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq : FullSpectrum q) : klDiv p q ≤ chiSq p q := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun i _ => kl_term_le (p i) (q i) (hp i) (hq.1 i))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, hp1,
    hq.2] at h
  unfold klDiv chiSq
  linarith

/-- The staircase of level Hamiltonians for a list of spectra in the basis u. -/
def spectralStair (u : Matrix.unitaryGroup ι ℂ) (β : ℝ) (Q : List (ι → ℝ)) :
    List (Hamiltonian ι) :=
  Q.map (levelHamiltonian u β)

theorem spectralStair_cons (u : Matrix.unitaryGroup ι ℂ) (β : ℝ) (q : ι → ℝ)
    (Q : List (ι → ℝ)) :
    spectralStair u β (q :: Q) = levelHamiltonian u β q :: spectralStair u β Q := rfl

/-- The divergences along a chain of spectra starting from p. -/
def chainKL : (ι → ℝ) → List (ι → ℝ) → ℝ
  | _, [] => 0
  | p, q :: Q => klDiv p q + chainKL q Q

/-- The staircase deficit of a spectral input is the chain of Kullback-Leibler divergences. -/
theorem spectralStair_deficit (u : Matrix.unitaryGroup ι ℂ) {β : ℝ} (hβ : β ≠ 0)
    (Q : List (ι → ℝ)) (p : ι → ℝ) (hQ : ∀ q ∈ Q, FullSpectrum q) :
    stairDeficit β (spectralStair u β Q) (spectralLift u p) = chainKL p Q := by
  induction Q generalizing p with
  | nil => rfl
  | cons q Q ih =>
    have hq := hQ q (List.mem_cons.2 (Or.inl rfl))
    have hrest : ∀ r ∈ Q, FullSpectrum r := fun r hr => hQ r (List.mem_cons.2 (Or.inr hr))
    rw [spectralStair_cons]
    simp only [stairDeficit, chainKL]
    rw [levelHamiltonian_gibbs u hβ hq, relativeEntropy_common_basis, ih q hrest]

theorem spectralStair_append_single (u : Matrix.unitaryGroup ι ℂ) (β : ℝ) (Q : List (ι → ℝ))
    (q : ι → ℝ) :
    spectralStair u β (Q ++ [q]) = spectralStair u β Q ++ [levelHamiltonian u β q] := by
  simp only [spectralStair, List.map_append, List.map_cons, List.map_nil]

end Spectral

/-! ## The straight path of spectra and its divergence budget -/

/-- The terms f s, f (s + 1), ..., f (s + n − 1). -/
def pathList {α : Type} (f : ℕ → α) : ℕ → ℕ → List α
  | _, 0 => []
  | s, n + 1 => f s :: pathList f (s + 1) n

theorem pathList_succ {α : Type} (f : ℕ → α) (s n : ℕ) :
    pathList f s (n + 1) = f s :: pathList f (s + 1) n := rfl

theorem pathList_succ_right {α : Type} (f : ℕ → α) : ∀ (n s : ℕ),
    pathList f s (n + 1) = pathList f s n ++ [f (s + n)]
  | 0, _ => rfl
  | n + 1, s => by
    have h := pathList_succ_right f n (s + 1)
    have e : s + 1 + n = s + (n + 1) := by omega
    rw [e] at h
    rw [pathList_succ f s (n + 1), h, pathList_succ f s n, List.cons_append]

theorem mem_pathList {α : Type} (f : ℕ → α) {x : α} : ∀ (n s : ℕ), x ∈ pathList f s n →
    ∃ k, s ≤ k ∧ k < s + n ∧ x = f k
  | 0, s, h => by simp [pathList] at h
  | n + 1, s, h => by
    rw [pathList_succ, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨s, le_rfl, by omega, h⟩
    · obtain ⟨k, hk1, hk2, hk⟩ := mem_pathList f n (s + 1) h
      exact ⟨k, by omega, by omega, hk⟩

section Path
variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A chain of n steps whose every divergence is at most c has total divergence at most n c. -/
theorem chainKL_pathList_le (f : ℕ → ι → ℝ) (c : ℝ) : ∀ (n s : ℕ),
    (∀ k, s ≤ k → k < s + n → klDiv (f k) (f (k + 1)) ≤ c) →
    chainKL (f s) (pathList f (s + 1) n) ≤ n * c
  | 0, s, _ => by simp [pathList, chainKL]
  | n + 1, s, h => by
    rw [pathList_succ]
    simp only [chainKL]
    have h1 := h s le_rfl (by omega)
    have h2 := chainKL_pathList_le f c n (s + 1) (fun k hk1 hk2 => h k (by omega) (by omega))
    push_cast
    linarith

/-- Step k of the straight path from a to b in N steps. -/
def linearPath (a b : ι → ℝ) (N k : ℕ) : ι → ℝ := fun i => a i + ((k : ℝ) / N) * (b i - a i)

omit [Fintype ι] [DecidableEq ι] in
theorem linearPath_zero (a b : ι → ℝ) (N : ℕ) : linearPath a b N 0 = a := by
  funext i
  simp [linearPath]

omit [Fintype ι] [DecidableEq ι] in
theorem linearPath_last (a b : ι → ℝ) {N : ℕ} (hN : N ≠ 0) : linearPath a b N N = b := by
  funext i
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
  simp only [linearPath, div_self hN', one_mul]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- Every point of the path up to step N stays above the smaller endpoint value. -/
theorem linearPath_ge_min (a b : ι → ℝ) {N k : ℕ} (hk : k ≤ N) (i : ι) :
    min (a i) (b i) ≤ linearPath a b N k i := by
  have ht0 : 0 ≤ (k : ℝ) / N := div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg N)
  have ht1 : (k : ℝ) / N ≤ 1 := div_le_one_of_le₀ (Nat.cast_le.2 hk) (Nat.cast_nonneg N)
  have h1 : (1 - (k : ℝ) / N) * min (a i) (b i) ≤ (1 - (k : ℝ) / N) * a i :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
  have h2 : ((k : ℝ) / N) * min (a i) (b i) ≤ ((k : ℝ) / N) * b i :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) ht0
  simp only [linearPath]
  linarith

omit [DecidableEq ι] in
/-- Every point of the path up to step N is a strictly positive probability vector. -/
theorem linearPath_full {a b : ι → ℝ} (ha : FullSpectrum a) (hb : FullSpectrum b) {N k : ℕ}
    (hk : k ≤ N) : FullSpectrum (linearPath a b N k) := by
  refine ⟨fun i => lt_of_lt_of_le (lt_min (ha.1 i) (hb.1 i)) (linearPath_ge_min a b hk i), ?_⟩
  simp only [linearPath]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, ha.2, hb.2]
  ring

/-- The path constant Σ (b i − a i)² / min(a i, b i). -/
def pathConstant (a b : ι → ℝ) : ℝ := ∑ i, (b i - a i) ^ 2 / min (a i) (b i)

omit [DecidableEq ι] in
theorem pathConstant_nonneg {a b : ι → ℝ} (ha : FullSpectrum a) (hb : FullSpectrum b) :
    0 ≤ pathConstant a b :=
  Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (lt_min (ha.1 i) (hb.1 i)).le)

omit [DecidableEq ι] in
/-- One step of the path has chi-square divergence at most the path constant over N². -/
theorem linearPath_step_chiSq {a b : ι → ℝ} (ha : FullSpectrum a) (hb : FullSpectrum b)
    {N k : ℕ} (hk : k + 1 ≤ N) :
    chiSq (linearPath a b N k) (linearPath a b N (k + 1)) ≤ pathConstant a b / (N : ℝ) ^ 2 := by
  unfold chiSq pathConstant
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  have hm : 0 < min (a i) (b i) := lt_min (ha.1 i) (hb.1 i)
  have hge := linearPath_ge_min a b hk i
  have hd : linearPath a b N k i - linearPath a b N (k + 1) i = -((b i - a i) / N) := by
    simp only [linearPath, Nat.cast_add, Nat.cast_one]
    ring
  rw [hd, neg_sq, div_pow, div_right_comm]
  exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_left (sq_nonneg _) hm hge)
    (by positivity)

omit [DecidableEq ι] in
/-- The N steps of the path from a cost at most the path constant over N in total. -/
theorem linearPath_chain_le {a b : ι → ℝ} (ha : FullSpectrum a) (hb : FullSpectrum b) {N : ℕ}
    (hN : 0 < N) :
    chainKL a (pathList (linearPath a b N) 1 N) ≤ pathConstant a b / N := by
  have h := chainKL_pathList_le (linearPath a b N) (pathConstant a b / (N : ℝ) ^ 2) N 0
    (fun k _ hk => (klDiv_le_chiSq (fun i => ((linearPath_full ha hb (N := N) (k := k)
      (by omega)).1 i).le) (linearPath_full ha hb (N := N) (k := k) (by omega)).2
      (linearPath_full ha hb (N := N) (k := k + 1) (by omega))).trans
      (linearPath_step_chiSq ha hb (by omega)))
  rw [Nat.zero_add, linearPath_zero] at h
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  calc
    chainKL a (pathList (linearPath a b N) 1 N) ≤ (N : ℝ) * (pathConstant a b / (N : ℝ) ^ 2) := h
    _ = pathConstant a b / N := by rw [sq, ← div_div, mul_div_cancel₀ _ hN']

/-- The point spectrum at i0. -/
def pointSpectrum (i0 : ι) : ι → ℝ := fun i => if i = i0 then 1 else 0

omit [Fintype ι] in
theorem pointSpectrum_nonneg (i0 : ι) (i : ι) : 0 ≤ pointSpectrum i0 i := by
  unfold pointSpectrum
  split_ifs <;> norm_num

theorem pointSpectrum_sum (i0 : ι) : ∑ i, pointSpectrum i0 i = 1 := by
  simp [pointSpectrum]

/-- The mixture (1 − ε) x + ε u with the uniform spectrum u. -/
def mixUniform (x : ι → ℝ) (ε : ℝ) : ι → ℝ := fun i => (1 - ε) * x i + ε / Fintype.card ι

omit [DecidableEq ι] in
theorem mixUniform_full [Nonempty ι] {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hx1 : ∑ i, x i = 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) : FullSpectrum (mixUniform x ε) := by
  have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  refine ⟨fun i => ?_, ?_⟩
  · have h1 : 0 ≤ (1 - ε) * x i := mul_nonneg (by linarith) (hx i)
    have h2 : 0 < ε / Fintype.card ι := div_pos hε0 hd
    simp only [mixUniform]
    linarith
  · simp only [mixUniform]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hx1, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_div_cancel₀ _ hd.ne']
    ring

omit [DecidableEq ι] in
/-- The chi-square divergence of a spectrum from its ε-mixture is at most ε times a constant. -/
theorem chiSq_mixUniform_le [Nonempty ι] {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    chiSq p (mixUniform p ε) ≤
      ε * ((Fintype.card ι : ℝ) * ∑ i, (p i - 1 / Fintype.card ι) ^ 2) := by
  have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hd' : (Fintype.card ι : ℝ) ≠ 0 := hd.ne'
  have hε' : ε ≠ 0 := hε0.ne'
  unfold chiSq
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hlow : ε / Fintype.card ι ≤ mixUniform p ε i := by
    have h1 : 0 ≤ (1 - ε) * p i := mul_nonneg (by linarith) (hp i)
    simp only [mixUniform]
    linarith
  have hdiff : p i - mixUniform p ε i = ε * (p i - 1 / Fintype.card ι) := by
    simp only [mixUniform]
    ring
  rw [hdiff]
  calc
    (ε * (p i - 1 / Fintype.card ι)) ^ 2 / mixUniform p ε i ≤
        (ε * (p i - 1 / Fintype.card ι)) ^ 2 / (ε / Fintype.card ι) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (div_pos hε0 hd) hlow
    _ = ε * ((Fintype.card ι : ℝ) * (p i - 1 / Fintype.card ι) ^ 2) := by
      field_simp
      ring

omit [DecidableEq ι] in
/-- A small enough mixture keeps the first divergence below any positive bound. -/
theorem exists_mixUniform_klDiv_le [Nonempty ι] {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ klDiv p (mixUniform p ε) ≤ η := by
  obtain ⟨c, hc_eq, hc⟩ : ∃ c : ℝ,
      c = (Fintype.card ι : ℝ) * ∑ i, (p i - 1 / Fintype.card ι) ^ 2 ∧ 0 ≤ c :=
    ⟨_, rfl, mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun i _ => sq_nonneg _))⟩
  have hpos : 0 < min 1 (η / (c + 1)) := lt_min one_pos (div_pos hη (by linarith))
  refine ⟨min 1 (η / (c + 1)), hpos, min_le_left _ _, ?_⟩
  have hmix := mixUniform_full hp0 hp1 hpos (min_le_left _ _)
  calc
    klDiv p (mixUniform p (min 1 (η / (c + 1)))) ≤ chiSq p (mixUniform p (min 1 (η / (c + 1)))) :=
      klDiv_le_chiSq hp0 hp1 hmix
    _ ≤ min 1 (η / (c + 1)) * c := by
      have h := chiSq_mixUniform_le hp0 hpos (min_le_left _ _)
      rwa [← hc_eq] at h
    _ ≤ η / (c + 1) * c := mul_le_mul_of_nonneg_right (min_le_right _ _) hc
    _ ≤ η := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith

/-- A mixture of a point spectrum with small enough weight has entropy below any positive bound. -/
theorem exists_mix_point_entropy_lt [Nonempty ι] (i0 : ι) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∑ i, Real.negMulLog (mixUniform (pointSpectrum i0) δ i) < η := by
  have hF : Continuous (fun δ : ℝ => ∑ i, Real.negMulLog (mixUniform (pointSpectrum i0) δ i)) := by
    unfold mixUniform
    fun_prop
  have hF0 : (∑ i, Real.negMulLog (mixUniform (pointSpectrum i0) 0 i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [mixUniform, pointSpectrum, sub_zero, one_mul, zero_div, add_zero]
    split_ifs <;> simp
  have ht := hF.tendsto 0
  simp only [hF0] at ht
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (ht.eventually_lt_const hη)
  have hm : 0 < min (r / 2) 1 := lt_min (by linarith) one_pos
  refine ⟨min (r / 2) 1, hm, min_le_right _ _, hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hm]
  exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

/-- For every positive bound some number of steps puts the path cost below it. -/
theorem exists_steps {K : ℝ} (hK : 0 ≤ K) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧ K / N ≤ η := by
  obtain ⟨N, hN⟩ := exists_nat_gt (K / η)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg hK hη.le) hN
  refine ⟨N, Nat.cast_pos.1 hNpos, ?_⟩
  rw [div_le_iff₀ hNpos]
  rw [div_lt_iff₀ hη] at hN
  linarith

/-- The staircase along the straight path from a to b in N steps, applied to a spectral input:
its final state is the spectral matrix of b and its deficit is at most D(p ‖ a) plus the path
constant over N. -/
theorem linear_staircase [Nonempty ι] (u : Matrix.unitaryGroup ι ℂ) {β : ℝ} (hβ : β ≠ 0)
    {p : ι → ℝ} (htr : (spectralLift u p).trace = 1) {a b : ι → ℝ} (ha : FullSpectrum a)
    (hb : FullSpectrum b) {N : ℕ} (hN : 0 < N) :
    stairOutput β (spectralStair u β (pathList (linearPath a b N) 0 (N + 1)))
        (spectralLift u p) = spectralLift u b ∧
      stairDeficit β (spectralStair u β (pathList (linearPath a b N) 0 (N + 1)))
          (spectralLift u p) ≤ klDiv p a + pathConstant a b / N := by
  have hQ : ∀ q ∈ pathList (linearPath a b N) 0 (N + 1), FullSpectrum q := by
    intro q hq
    obtain ⟨k, -, hk, rfl⟩ := mem_pathList (linearPath a b N) (N + 1) 0 hq
    exact linearPath_full ha hb (by omega)
  constructor
  · rw [pathList_succ_right, Nat.zero_add, linearPath_last a b hN.ne',
      spectralStair_append_single, stairOutput_append_single β _ _ htr,
      levelHamiltonian_gibbs u hβ hb]
  · rw [spectralStair_deficit u hβ _ p hQ, pathList_succ, Nat.zero_add]
    simp only [chainKL]
    rw [linearPath_zero]
    linarith [linearPath_chain_le ha hb hN]

/-- Heat attainment by a finite staircase, in every finite dimension: every density matrix is left
below any positive entropy η by finitely many swaps with Gibbs reservoirs, at a total heat with
S(ρ) − S(final) ≤ β Q ≤ S(ρ) − S(final) + η. -/
theorem staircase_attains_landauer [Nonempty ι] {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef)
    (htr : rho.trace = 1) {β : ℝ} (hβ : 0 < β) {η : ℝ} (hη : 0 < η) :
    ∃ L : List (Hamiltonian ι),
      entropy (stairOutput β L rho) < η ∧
      entropy rho - entropy (stairOutput β L rho) ≤ β * stairHeat β L rho ∧
      β * stairHeat β L rho ≤ entropy rho - entropy (stairOutput β L rho) + η := by
  obtain ⟨u, p, hρ, hp0, hp1⟩ : ∃ (u : Matrix.unitaryGroup ι ℂ) (p : ι → ℝ),
      spectralLift u p = rho ∧ (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 :=
    ⟨_, _, spectralLift_eigenvalues hrho.1, fun i => hrho.eigenvalues_nonneg i,
      (eigenvalues_sum_trace hrho.1).trans (congrArg Complex.re htr)⟩
  subst hρ
  obtain ⟨i0⟩ : Nonempty ι := inferInstance
  obtain ⟨δ, hδ0, hδ1, hδη⟩ := exists_mix_point_entropy_lt i0 hη
  have hb := mixUniform_full (pointSpectrum_nonneg i0) (pointSpectrum_sum i0) hδ0 hδ1
  obtain ⟨ε, hε0, hε1, hεη⟩ := exists_mixUniform_klDiv_le hp0 hp1 (half_pos hη)
  have ha := mixUniform_full hp0 hp1 hε0 hε1
  obtain ⟨N, hN0, hNη⟩ := exists_steps (pathConstant_nonneg ha hb) (half_pos hη)
  obtain ⟨hout, hdef⟩ := linear_staircase u hβ.ne' htr ha hb hN0
  obtain ⟨hbal, hdnn⟩ := stair_balance β (spectralStair u β (pathList
    (linearPath (mixUniform p ε) (mixUniform (pointSpectrum i0) δ) N) 0 (N + 1))) hrho htr
  refine ⟨spectralStair u β (pathList
    (linearPath (mixUniform p ε) (mixUniform (pointSpectrum i0) δ) N) 0 (N + 1)), ?_, ?_, ?_⟩
  · rw [hout, entropy_spectralLift]
    exact hδη
  · linarith
  · linarith

end Path

/-! ## Two thermal operations in sequence are one thermal operation, and their heats add -/

section Regroup
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A unitary carried to another index type by an equivalence. -/
def reindexUnitary (e : α ≃ β) (w : Matrix.unitaryGroup β ℂ) : Matrix.unitaryGroup α ℂ := by
  refine ⟨(w : Matrix β β ℂ).submatrix e e, ?_, ?_⟩
  · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      ← Matrix.star_eq_conjTranspose, unitary.coe_star_mul_self, Matrix.submatrix_one_equiv]
  · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      ← Matrix.star_eq_conjTranspose, unitary_mul_adjoint, Matrix.submatrix_one_equiv]

theorem reindexUnitary_coe (e : α ≃ β) (w : Matrix.unitaryGroup β ℂ) :
    ((reindexUnitary e w : Matrix.unitaryGroup α ℂ) : Matrix α α ℂ) =
      (w : Matrix β β ℂ).submatrix e e := rfl

/-- Conjugation by a carried unitary is the carried conjugation. -/
theorem rotate_reindex (e : α ≃ β) (w : Matrix.unitaryGroup β ℂ) (M : Matrix β β ℂ) :
    rotate (reindexUnitary e w) (M.submatrix e e) = (rotate w M).submatrix e e := by
  simp only [rotate]
  rw [reindexUnitary_coe, Matrix.star_eq_conjTranspose ((w : Matrix β β ℂ).submatrix e e),
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    ← Matrix.star_eq_conjTranspose]

/-- Conjugation by a product of unitaries is the composition of the two conjugations. -/
theorem rotate_mul (V U : Matrix.unitaryGroup α ℂ) (X : Matrix α α ℂ) :
    rotate (V * U) X = rotate V (rotate U X) := by
  simp only [rotate, Matrix.UnitaryGroup.mul_val, StarMul.star_mul, mul_assoc]

end Regroup

section Compose
variable {ι κ ν : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ν] [DecidableEq ν]

/-- The regrouping (system, (first bath, second bath)) to ((system, first bath), second bath). -/
def assocFirst (ι κ ν : Type) : ι × (κ × ν) ≃ (ι × κ) × ν where
  toFun x := ((x.1, x.2.1), x.2.2)
  invFun y := (y.1.1, (y.1.2, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The regrouping (system, (first bath, second bath)) to ((system, second bath), first bath). -/
def assocSecond (ι κ ν : Type) : ι × (κ × ν) ≃ (ι × ν) × κ where
  toFun x := ((x.1, x.2.2), x.2.1)
  invFun y := (y.1.1, (y.2, y.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The exchange of the two bath slots: ((x, s), r) ↦ ((x, r), s). -/
def slotSwap (ι κ ν : Type) : (ι × ν) × κ → (ι × κ) × ν := fun z => ((z.1.1, z.2), z.1.2)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν] in
theorem kronecker_assocFirst (rho : Matrix ι ι ℂ) (A : Matrix κ κ ℂ) (B : Matrix ν ν ℂ) :
    rho ⊗ₖ (A ⊗ₖ B) =
      ((rho ⊗ₖ A) ⊗ₖ B).submatrix (assocFirst ι κ ν) (assocFirst ι κ ν) := by
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, assocFirst, Equiv.coe_fn_mk]
  ring

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν] in
theorem regroup_slotSwap (Y : Matrix (ι × κ) (ι × κ) ℂ) (B : Matrix ν ν ℂ) :
    (Y ⊗ₖ B).submatrix (assocFirst ι κ ν) (assocFirst ι κ ν) =
      ((Y ⊗ₖ B).submatrix (slotSwap ι κ ν) (slotSwap ι κ ν)).submatrix
        (assocSecond ι κ ν) (assocSecond ι κ ν) := rfl

omit [DecidableEq ι] in
/-- The partial trace over the bath commutes with a left factor acting on the system alone. -/
theorem marginalLeft_kron_mul (a : Matrix ι ι ℂ) (X : Matrix (ι × κ) (ι × κ) ℂ) :
    marginalLeft ((a ⊗ₖ (1 : Matrix κ κ ℂ)) * X) = a * marginalLeft X := by
  ext i j
  simp only [marginalLeft, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.mul_sum]
  exact Finset.sum_comm

omit [DecidableEq ι] in
theorem marginalLeft_mul_kron (a : Matrix ι ι ℂ) (X : Matrix (ι × κ) (ι × κ) ℂ) :
    marginalLeft (X * (a ⊗ₖ (1 : Matrix κ κ ℂ))) = marginalLeft X * a := by
  ext i j
  simp only [marginalLeft, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_mul]
  exact Finset.sum_comm

omit [DecidableEq ι] in
/-- The partial trace over the system is cyclic for a factor acting on the system alone. -/
theorem marginalRight_kron_mul (a : Matrix ι ι ℂ) (X : Matrix (ι × κ) (ι × κ) ℂ) :
    marginalRight ((a ⊗ₖ (1 : Matrix κ κ ℂ)) * X) =
      marginalRight (X * (a ⊗ₖ (1 : Matrix κ κ ℂ))) := by
  ext r s
  simp only [marginalRight, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => mul_comm _ _))

/-- A unitary acting on the system and one bath leaves the partial trace over the other bath
to act on its marginal. -/
theorem marginalLeft_rotate_tensor (v : Matrix.unitaryGroup ι ℂ)
    (Z : Matrix (ι × κ) (ι × κ) ℂ) :
    marginalLeft (rotate (tensorUnitary v (1 : Matrix.unitaryGroup κ ℂ)) Z) =
      rotate v (marginalLeft Z) := by
  simp only [rotate, tensorUnitary, Matrix.UnitaryGroup.one_val, star_tensor, star_one]
  rw [marginalLeft_mul_kron, marginalLeft_kron_mul]

/-- The same unitary leaves the marginal of the untouched bath unchanged. -/
theorem marginalRight_rotate_tensor (v : Matrix.unitaryGroup ι ℂ)
    (Z : Matrix (ι × κ) (ι × κ) ℂ) :
    marginalRight (rotate (tensorUnitary v (1 : Matrix.unitaryGroup κ ℂ)) Z) =
      marginalRight Z := by
  simp only [rotate, tensorUnitary, Matrix.UnitaryGroup.one_val, star_tensor, star_one]
  rw [mul_assoc, marginalRight_kron_mul, mul_assoc, ← Matrix.mul_kronecker_mul,
    unitary.coe_star_mul_self, one_mul, Matrix.one_kronecker_one, mul_one]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] [DecidableEq ν] in
theorem marginalLeft_assocSecond (W : Matrix ((ι × ν) × κ) ((ι × ν) × κ) ℂ) :
    marginalLeft (W.submatrix (assocSecond ι κ ν) (assocSecond ι κ ν)) =
      marginalLeft (marginalLeft W) := by
  ext i j
  simp only [marginalLeft, Matrix.submatrix_apply, assocSecond, Equiv.coe_fn_mk,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] [DecidableEq ν] in
theorem marginalLeft_marginalRight_assocSecond (W : Matrix ((ι × ν) × κ) ((ι × ν) × κ) ℂ) :
    marginalLeft (marginalRight (W.submatrix (assocSecond ι κ ν) (assocSecond ι κ ν))) =
      marginalRight W := by
  ext r t
  simp only [marginalLeft, marginalRight, Matrix.submatrix_apply, assocSecond, Equiv.coe_fn_mk,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [DecidableEq ι] [DecidableEq κ] [Fintype ν] [DecidableEq ν] in
theorem marginalRight_marginalRight_assocSecond (W : Matrix ((ι × ν) × κ) ((ι × ν) × κ) ℂ) :
    marginalRight (marginalRight (W.submatrix (assocSecond ι κ ν) (assocSecond ι κ ν))) =
      marginalRight (marginalLeft W) := by
  ext s t
  simp only [marginalLeft, marginalRight, Matrix.submatrix_apply, assocSecond, Equiv.coe_fn_mk]
  exact Finset.sum_comm

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] [Fintype ν] [DecidableEq ν] in
theorem marginalLeft_slotSwap (Y : Matrix (ι × κ) (ι × κ) ℂ) (B : Matrix ν ν ℂ) :
    marginalLeft ((Y ⊗ₖ B).submatrix (slotSwap ι κ ν) (slotSwap ι κ ν)) =
      marginalLeft Y ⊗ₖ B := by
  ext ⟨x, s⟩ ⟨y, t⟩
  simp only [marginalLeft, Matrix.submatrix_apply, slotSwap, Matrix.kronecker_apply,
    Finset.sum_mul]

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] [DecidableEq ν] in
theorem marginalRight_slotSwap (Y : Matrix (ι × κ) (ι × κ) ℂ) (B : Matrix ν ν ℂ) :
    marginalRight ((Y ⊗ₖ B).submatrix (slotSwap ι κ ν) (slotSwap ι κ ν)) =
      B.trace • marginalRight Y := by
  ext r t
  simp only [marginalRight, Matrix.submatrix_apply, slotSwap, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.mul_sum, mul_comm]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem marginalLeft_sub (X Y : Matrix (ι × κ) (ι × κ) ℂ) :
    marginalLeft (X - Y) = marginalLeft X - marginalLeft Y := by
  ext i j
  simp only [marginalLeft, Matrix.sub_apply, Finset.sum_sub_distrib]

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem marginalRight_sub (X Y : Matrix (ι × κ) (ι × κ) ℂ) :
    marginalRight (X - Y) = marginalRight X - marginalRight Y := by
  ext r s
  simp only [marginalRight, Matrix.sub_apply, Finset.sum_sub_distrib]

/-- The energy of the joint bath Hamiltonian a ⊗ 1 + 1 ⊗ b splits over the two bath marginals. -/
theorem meanEnergy_composeHam (a : Matrix κ κ ℂ) (b : Matrix ν ν ℂ)
    (X : Matrix (κ × ν) (κ × ν) ℂ) :
    meanEnergy (a ⊗ₖ (1 : Matrix ν ν ℂ) + (1 : Matrix κ κ ℂ) ⊗ₖ b) X =
      meanEnergy a (marginalLeft X) + meanEnergy b (marginalRight X) := by
  simp only [meanEnergy, add_mul, Matrix.trace_add, Complex.add_re]
  rw [Matrix.trace_mul_comm (a ⊗ₖ (1 : Matrix ν ν ℂ)),
    Matrix.trace_mul_comm ((1 : Matrix κ κ ℂ) ⊗ₖ b), trace_tensor_left, trace_tensor_right,
    Matrix.trace_mul_comm (marginalLeft X), Matrix.trace_mul_comm (marginalRight X)]

theorem spectralLift_add (u : Matrix.unitaryGroup ι ℂ) (p q : ι → ℝ) :
    spectralLift u (fun i => p i + q i) = spectralLift u p + spectralLift u q := by
  simp only [spectralLift, rotate, realDiagonal, Complex.ofReal_add, ← Matrix.diagonal_add,
    mul_add, add_mul]

theorem spectralLift_const_one (u : Matrix.unitaryGroup ι ℂ) :
    spectralLift u (fun _ => (1 : ℝ)) = 1 := by
  simp only [spectralLift, rotate, realDiagonal, Complex.ofReal_one, Matrix.diagonal_one, mul_one,
    unitary_mul_adjoint]

/-- The joint bath Hamiltonian of two Hermitian bath Hamiltonians. -/
def composeHam (a : Matrix κ κ ℂ) (b : Matrix ν ν ℂ) : Matrix (κ × ν) (κ × ν) ℂ :=
  a ⊗ₖ (1 : Matrix ν ν ℂ) + (1 : Matrix κ κ ℂ) ⊗ₖ b

/-- The joint bath Hamiltonian is diagonal in the product eigenbasis with the summed levels. -/
theorem composeHam_spectral {a : Matrix κ κ ℂ} {b : Matrix ν ν ℂ} (ha : a.IsHermitian)
    (hb : b.IsHermitian) :
    composeHam a b = spectralLift (tensorUnitary ha.eigenvectorUnitary hb.eigenvectorUnitary)
      (fun x => ha.eigenvalues x.1 + hb.eigenvalues x.2) := by
  rw [spectralLift_add (tensorUnitary ha.eigenvectorUnitary hb.eigenvectorUnitary)
      (fun x => ha.eigenvalues x.1) (fun x => hb.eigenvalues x.2)]
  have h1 := tensor_spectralLift ha.eigenvectorUnitary hb.eigenvectorUnitary ha.eigenvalues
    (fun _ => (1 : ℝ))
  have h2 := tensor_spectralLift ha.eigenvectorUnitary hb.eigenvectorUnitary (fun _ => (1 : ℝ))
    hb.eigenvalues
  simp only [mul_one, one_mul, spectralLift_const_one, spectralLift_eigenvalues] at h1 h2
  rw [← h1, ← h2]
  rfl

theorem composeHam_hermitian {a : Matrix κ κ ℂ} {b : Matrix ν ν ℂ} (ha : a.IsHermitian)
    (hb : b.IsHermitian) : (composeHam a b).IsHermitian := by
  rw [composeHam_spectral ha hb]
  exact spectralLift_hermitian _ _

omit [DecidableEq κ] [DecidableEq ν] in
/-- Gibbs weights of summed levels are products of the Gibbs weights of the two baths. -/
theorem gibbsWeight_add [Nonempty κ] [Nonempty ν] (β : ℝ) (e : κ → ℝ) (f : ν → ℝ)
    (x : κ × ν) :
    gibbsWeight β (fun y => e y.1 + f y.2) x = gibbsWeight β e x.1 * gibbsWeight β f x.2 := by
  have h : ∀ y : κ × ν, Real.exp (-β * (e y.1 + f y.2)) =
      Real.exp (-β * e y.1) * Real.exp (-β * f y.2) := by
    intro y
    rw [← Real.exp_add]
    ring_nf
  simp only [gibbsWeight, partition, h, Fintype.sum_prod_type, ← Finset.sum_mul_sum]
  rw [mul_div_mul_comm]

/-- The Gibbs state of the joint bath Hamiltonian is the product of the two Gibbs states. -/
theorem gibbsState_composeHam [Nonempty κ] [Nonempty ν] {a : Matrix κ κ ℂ}
    {b : Matrix ν ν ℂ} (ha : a.IsHermitian) (hb : b.IsHermitian) (β : ℝ) :
    gibbsState (composeHam_hermitian ha hb) β = gibbsState ha β ⊗ₖ gibbsState hb β := by
  rw [gibbsState_congr (composeHam_hermitian ha hb) (spectralLift_hermitian _ _)
    (composeHam_spectral ha hb) β, gibbsState_spectralLift]
  unfold gibbsState
  rw [tensor_spectralLift]
  exact congrArg (spectralLift _) (funext fun x => gibbsWeight_add β _ _ x)

/-- The joint unitary: u on the system and the first bath, then v on the system and the second. -/
def composeUnitary (u : Matrix.unitaryGroup (ι × κ) ℂ) (v : Matrix.unitaryGroup (ι × ν) ℂ) :
    Matrix.unitaryGroup (ι × (κ × ν)) ℂ :=
  reindexUnitary (assocSecond ι κ ν) (tensorUnitary v (1 : Matrix.unitaryGroup κ ℂ)) *
    reindexUnitary (assocFirst ι κ ν) (tensorUnitary u (1 : Matrix.unitaryGroup ν ℂ))

theorem rotate_tensor_one (u : Matrix.unitaryGroup (ι × κ) ℂ) (Y : Matrix (ι × κ) (ι × κ) ℂ)
    (B : Matrix ν ν ℂ) :
    rotate (tensorUnitary u (1 : Matrix.unitaryGroup ν ℂ)) (Y ⊗ₖ B) = rotate u Y ⊗ₖ B := by
  simp only [rotate, tensorUnitary, Matrix.UnitaryGroup.one_val, star_tensor, star_one,
    ← Matrix.mul_kronecker_mul, one_mul, mul_one]

/-- The joint state of the composed operation, written through the two actual unitaries. -/
theorem rotate_composeUnitary (u : Matrix.unitaryGroup (ι × κ) ℂ)
    (v : Matrix.unitaryGroup (ι × ν) ℂ) (rho : Matrix ι ι ℂ) (A : Matrix κ κ ℂ)
    (B : Matrix ν ν ℂ) :
    rotate (composeUnitary u v) (rho ⊗ₖ (A ⊗ₖ B)) =
      (rotate (tensorUnitary v (1 : Matrix.unitaryGroup κ ℂ))
        ((rotate u (rho ⊗ₖ A) ⊗ₖ B).submatrix (slotSwap ι κ ν) (slotSwap ι κ ν))).submatrix
          (assocSecond ι κ ν) (assocSecond ι κ ν) := by
  rw [kronecker_assocFirst, composeUnitary, rotate_mul, rotate_reindex, rotate_tensor_one,
    regroup_slotSwap, rotate_reindex]

/-- The system output of the composed operation is the output of v on the output of u. -/
theorem composeUnitary_output [Nonempty κ] [Nonempty ν] (u : Matrix.unitaryGroup (ι × κ) ℂ)
    (v : Matrix.unitaryGroup (ι × ν) ℂ) (rho : Matrix ι ι ℂ) {a : Matrix κ κ ℂ}
    (ha : a.IsHermitian) {b : Matrix ν ν ℂ} (hb : b.IsHermitian) (β : ℝ) :
    marginalLeft (thermalJoint (composeUnitary u v) rho (composeHam_hermitian ha hb) β) =
      marginalLeft (thermalJoint v (marginalLeft (thermalJoint u rho ha β)) hb β) := by
  simp only [thermalJoint, gibbsState_composeHam ha hb β, rotate_composeUnitary,
    marginalLeft_assocSecond, marginalLeft_rotate_tensor, marginalLeft_slotSwap]

/-- The heat of the composed operation is the heat of u plus the heat of v on the output of u. -/
theorem composeUnitary_heat [Nonempty κ] [Nonempty ν] (u : Matrix.unitaryGroup (ι × κ) ℂ)
    (v : Matrix.unitaryGroup (ι × ν) ℂ) (rho : Matrix ι ι ℂ) {a : Matrix κ κ ℂ}
    (ha : a.IsHermitian) {b : Matrix ν ν ℂ} (hb : b.IsHermitian) (β : ℝ) :
    reservoirHeat (composeUnitary u v) rho (composeHam_hermitian ha hb) β =
      reservoirHeat u rho ha β + reservoirHeat v (marginalLeft (thermalJoint u rho ha β)) hb β := by
  simp only [reservoirHeat, thermalJoint, gibbsState_composeHam ha hb β, rotate_composeUnitary,
    composeHam, meanEnergy_composeHam, marginalLeft_sub, marginalRight_sub,
    marginalLeft_kronecker, marginalRight_kronecker, gibbsState_trace, one_smul,
    marginalLeft_marginalRight_assocSecond, marginalRight_marginalRight_assocSecond,
    marginalRight_rotate_tensor, marginalLeft_rotate_tensor, marginalRight_slotSwap,
    marginalLeft_slotSwap]

end Compose

/-! ## The staircase as one finite thermal operation -/

/-- A finite thermal operation on the system carrier ι: a finite nonempty bath with a Hermitian
Hamiltonian, and one joint unitary on the system and the bath. -/
structure ThermalOperation (ι : Type) [Fintype ι] [DecidableEq ι] where
  /-- The bath carrier. -/
  bath : Type
  [bathFintype : Fintype bath]
  [bathDecidableEq : DecidableEq bath]
  [bathNonempty : Nonempty bath]
  /-- The joint unitary on the system and the bath. -/
  joint : Matrix.unitaryGroup (ι × bath) ℂ
  /-- The bath Hamiltonian, in joules. -/
  ham : Matrix bath bath ℂ
  ham_hermitian : ham.IsHermitian

attribute [instance] ThermalOperation.bathFintype ThermalOperation.bathDecidableEq
  ThermalOperation.bathNonempty

namespace ThermalOperation

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The system state after the operation: the partial trace of the actual joint state. -/
def output (T : ThermalOperation ι) (rho : Matrix ι ι ℂ) (β : ℝ) : Matrix ι ι ℂ :=
  marginalLeft (thermalJoint T.joint rho T.ham_hermitian β)

/-- The heat of the operation: the reservoir heat of the existing definition. -/
def heat (T : ThermalOperation ι) (rho : Matrix ι ι ℂ) (β : ℝ) : ℝ :=
  reservoirHeat T.joint rho T.ham_hermitian β

/-- Operation T₁ followed by operation T₂ on a fresh bath: one joint unitary on the system and
the product bath, with the summed bath Hamiltonian. -/
def compose (T₁ T₂ : ThermalOperation ι) : ThermalOperation ι where
  bath := T₁.bath × T₂.bath
  joint := composeUnitary T₁.joint T₂.joint
  ham := composeHam T₁.ham T₂.ham
  ham_hermitian := composeHam_hermitian T₁.ham_hermitian T₂.ham_hermitian

/-- The operation with a one-point bath, the identity unitary and the zero Hamiltonian. -/
def idle : ThermalOperation ι where
  bath := Unit
  joint := 1
  ham := 0
  ham_hermitian := Matrix.isHermitian_zero

/-- The swap of the system with a fresh reservoir of the given Hamiltonian. -/
def swapStep [Nonempty ι] (H : Hamiltonian ι) : ThermalOperation ι where
  bath := ι
  joint := swapUnitary
  ham := H.1
  ham_hermitian := H.2

theorem compose_output (T₁ T₂ : ThermalOperation ι) (rho : Matrix ι ι ℂ) (β : ℝ) :
    (T₁.compose T₂).output rho β = T₂.output (T₁.output rho β) β :=
  composeUnitary_output T₁.joint T₂.joint rho T₁.ham_hermitian T₂.ham_hermitian β

theorem compose_heat (T₁ T₂ : ThermalOperation ι) (rho : Matrix ι ι ℂ) (β : ℝ) :
    (T₁.compose T₂).heat rho β = T₁.heat rho β + T₂.heat (T₁.output rho β) β :=
  composeUnitary_heat T₁.joint T₂.joint rho T₁.ham_hermitian T₂.ham_hermitian β

theorem idle_output (rho : Matrix ι ι ℂ) (β : ℝ) :
    (idle : ThermalOperation ι).output rho β = rho := by
  simp only [output, idle, thermalJoint, rotate, Matrix.UnitaryGroup.one_val, star_one, one_mul,
    mul_one, marginalLeft_kronecker, gibbsState_trace, one_smul]

theorem idle_heat (rho : Matrix ι ι ℂ) (β : ℝ) : (idle : ThermalOperation ι).heat rho β = 0 := by
  simp only [heat, idle, reservoirHeat, meanEnergy, zero_mul, Matrix.trace_zero, Complex.zero_re]

/-- The output of every finite operation on a density matrix is a density matrix. -/
theorem output_density (T : ThermalOperation ι) {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef)
    (htr : rho.trace = 1) (β : ℝ) :
    (T.output rho β).PosSemidef ∧ (T.output rho β).trace = 1 := by
  obtain ⟨hp, ht⟩ := thermalJoint_density T.joint hrho htr T.ham_hermitian β
  exact ⟨marginalLeft_posSemidef hp, (marginalLeft_trace _).trans ht⟩

/-- The Landauer lower bound for every finite operation, from the existing joint-unitary balance. -/
theorem landauer (T : ThermalOperation ι) {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef)
    (htr : rho.trace = 1) {β : ℝ} (hβ : 0 < β) :
    entropy rho - entropy (T.output rho β) ≤ β * T.heat rho β := by
  have h := (div_le_iff₀ hβ).1 (landauer_from_unitary T.joint hrho htr T.ham_hermitian β hβ)
  simp only [output, heat]
  linarith

end ThermalOperation

section Joint
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The staircase as one finite thermal operation: the swaps composed into one joint unitary on
the system and the product of all the reservoirs, with the summed reservoir Hamiltonian. -/
def stairOperation : List (Hamiltonian ι) → ThermalOperation ι
  | [] => ThermalOperation.idle
  | H :: L => (ThermalOperation.swapStep H).compose (stairOperation L)

theorem stairOperation_cons (H : Hamiltonian ι) (L : List (Hamiltonian ι)) :
    stairOperation (H :: L) = (ThermalOperation.swapStep H).compose (stairOperation L) := rfl

/-- The joint unitary of a staircase is the composite of the first swap with the joint unitary of
the remaining steps. -/
theorem stairOperation_joint_cons (H : Hamiltonian ι) (L : List (Hamiltonian ι)) :
    (stairOperation (H :: L)).joint = composeUnitary swapUnitary (stairOperation L).joint := rfl

/-- The one joint operation leaves the system in the state of the sequential staircase. -/
theorem stairOperation_output (β : ℝ) (L : List (Hamiltonian ι)) (rho : Matrix ι ι ℂ) :
    (stairOperation L).output rho β = stairOutput β L rho := by
  induction L generalizing rho with
  | nil => exact ThermalOperation.idle_output rho β
  | cons H L ih =>
    rw [stairOperation_cons, ThermalOperation.compose_output, ih]
    rfl

/-- The heat of the one joint operation is the sum of the per-step reservoir heats. -/
theorem stairOperation_heat (β : ℝ) (L : List (Hamiltonian ι)) (rho : Matrix ι ι ℂ) :
    (stairOperation L).heat rho β = stairHeat β L rho := by
  induction L generalizing rho with
  | nil => exact ThermalOperation.idle_heat rho β
  | cons H L ih =>
    rw [stairOperation_cons, ThermalOperation.compose_heat, ih]
    rfl

/-- Every reservoir of the staircase has the dimension d of the system, so the joint bath of a
staircase of n steps has dimension d^n: the bath grows with the number of steps. -/
theorem stairOperation_bath_card (L : List (Hamiltonian ι)) :
    Fintype.card (stairOperation L).bath = Fintype.card ι ^ L.length := by
  induction L with
  | nil => exact Fintype.card_unit
  | cons H L ih =>
    rw [List.length_cons, pow_succ, ← ih]
    exact (Fintype.card_prod ι (stairOperation L).bath).trans (mul_comm _ _)

end Joint

/-! ## The Landauer bound is the infimum of finite heat -/

section Infimum
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A density matrix has nonnegative entropy. -/
theorem entropy_nonneg_density {a : Matrix ι ι ℂ} (ha : a.PosSemidef) (hta : a.trace = 1) :
    0 ≤ entropy a := by
  rw [entropy_eq_eigenvalues ha.1]
  have hsum : ∑ i, ha.1.eigenvalues i = 1 :=
    (eigenvalues_sum_trace ha.1).trans (congrArg Complex.re hta)
  apply Finset.sum_nonneg
  intro i _
  apply Real.negMulLog_nonneg (ha.eigenvalues_nonneg i)
  rw [← hsum]
  exact Finset.single_le_sum (fun j _ => ha.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- The Landauer bound is the infimum of the heat of finite thermal operations, in every finite
dimension: every finite operation pays β Q ≥ S(ρ) − S(final), and for every η > 0 one finite
operation, the staircase, leaves entropy below η at β Q ≤ S(ρ) − S(final) + η. -/
theorem landauer_infimum [Nonempty ι] {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef)
    (htr : rho.trace = 1) {β : ℝ} (hβ : 0 < β) :
    (∀ T : ThermalOperation ι, entropy rho - entropy (T.output rho β) ≤ β * T.heat rho β) ∧
    (∀ η : ℝ, 0 < η → ∃ T : ThermalOperation ι, entropy (T.output rho β) < η ∧
      β * T.heat rho β ≤ entropy rho - entropy (T.output rho β) + η) := by
  refine ⟨fun T => T.landauer hrho htr hβ, fun η hη => ?_⟩
  obtain ⟨L, h1, -, h3⟩ := staircase_attains_landauer hrho htr hβ hη
  refine ⟨stairOperation L, ?_, ?_⟩
  · rw [stairOperation_output]
    exact h1
  · rw [stairOperation_output, stairOperation_heat]
    exact h3

/-- The same statement on the raw data of BoundaryReconstruction.Thermal: a finite bath, a joint
unitary and a Hermitian bath Hamiltonian. -/
theorem landauer_infimum_unitary [Nonempty ι] {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef)
    (htr : rho.trace = 1) {β : ℝ} (hβ : 0 < β) {η : ℝ} (hη : 0 < η) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (_ : Nonempty κ)
      (u : Matrix.unitaryGroup (ι × κ) ℂ) (h : Matrix κ κ ℂ) (hh : h.IsHermitian),
      entropy (marginalLeft (thermalJoint u rho hh β)) < η ∧
      entropy rho - entropy (marginalLeft (thermalJoint u rho hh β)) ≤
        β * reservoirHeat u rho hh β ∧
      β * reservoirHeat u rho hh β ≤
        entropy rho - entropy (marginalLeft (thermalJoint u rho hh β)) + η := by
  obtain ⟨hlow, hup⟩ := landauer_infimum hrho htr hβ
  obtain ⟨T, h1, h2⟩ := hup η hη
  exact ⟨T.bath, inferInstance, inferInstance, inferInstance, T.joint, T.ham, T.ham_hermitian,
    h1, hlow T, h2⟩

/-- Heat attainment: for every η > 0 some finite thermal operation leaves entropy below η at a
heat within η/β of the Landauer value S(ρ)/β. -/
theorem heat_attains_landauer [Nonempty ι] {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef)
    (htr : rho.trace = 1) {β : ℝ} (hβ : 0 < β) {η : ℝ} (hη : 0 < η) :
    ∃ T : ThermalOperation ι, entropy (T.output rho β) < η ∧
      |β * T.heat rho β - entropy rho| < η := by
  obtain ⟨hlow, hup⟩ := landauer_infimum hrho htr hβ
  obtain ⟨T, h1, h2⟩ := hup (η / 2) (half_pos hη)
  have hl := hlow T
  obtain ⟨hp, ht⟩ := T.output_density hrho htr β
  have h0 := entropy_nonneg_density hp ht
  refine ⟨T, by linarith, ?_⟩
  rw [abs_lt]
  constructor <;> linarith

/-- The pair case: every density matrix of the pair is reset below η at a heat within η/β of its
Landauer value. -/
theorem pair_heat_attains_landauer {rho : Matrix Bool Bool ℂ} (hrho : rho.PosSemidef)
    (htr : rho.trace = 1) {β : ℝ} (hβ : 0 < β) {η : ℝ} (hη : 0 < η) :
    ∃ T : ThermalOperation Bool, entropy (T.output rho β) < η ∧
      |β * T.heat rho β - entropy rho| < η :=
  heat_attains_landauer hrho htr hβ hη

/-- The fair pair is erased below η at a heat within η/β of log 2/β. -/
theorem fair_pair_heat_attains {β : ℝ} (hβ : 0 < β) {η : ℝ} (hη : 0 < η) :
    ∃ T : ThermalOperation Bool, entropy (T.output fairPair β) < η ∧
      |β * T.heat fairPair β - Real.log 2| < η := by
  have h := heat_attains_landauer fairPair_posDef.posSemidef fairPair_trace hβ hη
  rwa [fairPair_entropy] at h

/-- The single swap with a two-level bath of gap E does not attain the bound: its heat on the fair
pair is E(1/2 − 1/(1 + e^{βE})), which grows without bound as E grows. -/
theorem fair_pair_single_swap_heat_diverges {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun E : ℝ => reservoirHeat swapUnitary fairPair (twoLevel_hermitian E) β)
      atTop atTop := by
  have hf : (fairPair true true).re = 1 / 2 := by
    simp [fairPair, realDiagonal]
  simp only [twoLevel_swap_heat, hf]
  have hg : Tendsto (fun E : ℝ => 1 / 2 - 1 / (1 + Real.exp (β * E))) atTop (𝓝 (1 / 2)) := by
    have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub (twoLevel_weight_tendsto β hβ)
    simpa using h
  exact tendsto_id.atTop_mul_pos (by norm_num) hg

end Infimum

/-! ## The reservoir gaps increase step by step along the staircase -/

section Gaps
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The energy of level i above level i0 in the level Hamiltonian of the spectrum q, whose levels
are −log(q j)/β. -/
def levelGap (β : ℝ) (q : ι → ℝ) (i0 i : ι) : ℝ := -Real.log (q i) / β - -Real.log (q i0) / β

omit [Fintype ι] [DecidableEq ι] in
/-- Along the straight path the gap of level i over level i0 grows strictly at every step when
b is more concentrated on i0 than a, in the sense a(i) b(i0) > a(i0) b(i). -/
theorem linearPath_gap_lt {β : ℝ} (hβ : 0 < β) {a b : ι → ℝ} (ha : ∀ j, 0 < a j)
    (hb : ∀ j, 0 < b j) {N k : ℕ} (hk : k + 1 ≤ N) {i0 i : ι}
    (hcross : a i0 * b i < a i * b i0) :
    levelGap β (linearPath a b N k) i0 i < levelGap β (linearPath a b N (k + 1)) i0 i := by
  have hpos : ∀ m, m ≤ N → ∀ j, 0 < linearPath a b N m j := fun m hm j =>
    lt_of_lt_of_le (lt_min (ha j) (hb j)) (linearPath_ge_min a b hm j)
  have hx0 := hpos k (by omega) i0
  have hy0 := hpos k (by omega) i
  have hx1 := hpos (k + 1) hk i0
  have hy1 := hpos (k + 1) hk i
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hid : linearPath a b N (k + 1) i0 * linearPath a b N k i -
      linearPath a b N k i0 * linearPath a b N (k + 1) i =
        (1 / (N : ℝ)) * (a i * b i0 - a i0 * b i) := by
    simp only [linearPath, Nat.cast_add, Nat.cast_one]
    ring
  have hcr : 0 < (1 / (N : ℝ)) * (a i * b i0 - a i0 * b i) :=
    mul_pos (div_pos one_pos hNpos) (by linarith)
  have hratio : linearPath a b N k i0 / linearPath a b N k i <
      linearPath a b N (k + 1) i0 / linearPath a b N (k + 1) i := by
    rw [div_lt_div_iff₀ hy0 hy1]
    linarith
  have hlog := Real.log_lt_log (div_pos hx0 hy0) hratio
  rw [Real.log_div hx0.ne' hy0.ne', Real.log_div hx1.ne' hy1.ne'] at hlog
  have e0 : levelGap β (linearPath a b N k) i0 i =
      (Real.log (linearPath a b N k i0) - Real.log (linearPath a b N k i)) / β := by
    unfold levelGap
    ring
  have e1 : levelGap β (linearPath a b N (k + 1)) i0 i =
      (Real.log (linearPath a b N (k + 1) i0) - Real.log (linearPath a b N (k + 1) i)) / β := by
    unfold levelGap
    ring
  rw [e0, e1]
  exact div_lt_div_of_pos_right hlog hβ

/-- The mixtures of the staircase satisfy the concentration condition when δ < ε. -/
theorem mixUniform_cross [Nonempty ι] {p : ι → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    {ε δ : ℝ} (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδε : δ < ε) {i0 i : ι}
    (hi : i ≠ i0) :
    mixUniform p ε i0 * mixUniform (pointSpectrum i0) δ i <
      mixUniform p ε i * mixUniform (pointSpectrum i0) δ i0 := by
  have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hpi0 : p i0 ≤ 1 := by
    rw [← hp1]
    exact Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i0)
  have hbi : mixUniform (pointSpectrum i0) δ i = δ / Fintype.card ι := by
    simp only [mixUniform, pointSpectrum, if_neg hi, mul_zero, zero_add]
  have hb0 : mixUniform (pointSpectrum i0) δ i0 = 1 - δ + δ / Fintype.card ι := by
    simp only [mixUniform, pointSpectrum, if_true, mul_one]
  have hai : ε / Fintype.card ι ≤ mixUniform p ε i := by
    have := mul_nonneg (sub_nonneg.2 hε1) (hp0 i)
    simp only [mixUniform]
    linarith
  have hai0 : mixUniform p ε i0 ≤ 1 - ε + ε / Fintype.card ι := by
    have := mul_le_mul_of_nonneg_left hpi0 (sub_nonneg.2 hε1)
    simp only [mixUniform]
    linarith
  have hb0nn : 0 ≤ 1 - δ + δ / Fintype.card ι := by
    have := div_pos hδ0 hd
    linarith
  have hbinn : 0 ≤ δ / Fintype.card ι := (div_pos hδ0 hd).le
  rw [hbi, hb0]
  have h1 := mul_le_mul_of_nonneg_left hai hb0nn
  have h2 := mul_le_mul_of_nonneg_right hai0 hbinn
  have h3 : (1 - δ + δ / Fintype.card ι) * (ε / Fintype.card ι) -
      (1 - ε + ε / Fintype.card ι) * (δ / Fintype.card ι) = (ε - δ) / Fintype.card ι := by
    ring
  have h4 : 0 < (ε - δ) / Fintype.card ι := div_pos (by linarith) hd
  nlinarith

/-- A mixture of a point spectrum with small enough weight, below any given positive bound m, has
entropy below any positive bound η. -/
theorem exists_mix_point_entropy_lt_below [Nonempty ι] (i0 : ι) {η : ℝ} (hη : 0 < η) {m : ℝ}
    (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧ δ < m ∧ δ ≤ 1 ∧
      ∑ i, Real.negMulLog (mixUniform (pointSpectrum i0) δ i) < η := by
  have hF : Continuous (fun δ : ℝ => ∑ i, Real.negMulLog (mixUniform (pointSpectrum i0) δ i)) := by
    unfold mixUniform
    fun_prop
  have hF0 : (∑ i, Real.negMulLog (mixUniform (pointSpectrum i0) 0 i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [mixUniform, pointSpectrum, sub_zero, one_mul, zero_div, add_zero]
    split_ifs <;> simp
  have ht := hF.tendsto 0
  simp only [hF0] at ht
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (ht.eventually_lt_const hη)
  have hpos : 0 < min (r / 2) (min 1 (m / 2)) := lt_min (by linarith) (lt_min one_pos (by linarith))
  refine ⟨min (r / 2) (min 1 (m / 2)), hpos, ?_, ?_, hball ?_⟩
  · exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

/-- The staircase route of Reeb and Wolf in full: an explicit basis u, endpoints a and b, a number
of steps N and a ground level i0, whose N + 1 reservoirs have level gaps over i0 that increase
strictly at every step, leave every density matrix below entropy η at a heat with
S(ρ) − S(final) ≤ β Q ≤ S(ρ) − S(final) + η. -/
theorem staircase_attains_landauer_increasing_gaps [Nonempty ι] {rho : Matrix ι ι ℂ}
    (hrho : rho.PosSemidef) (htr : rho.trace = 1) {β : ℝ} (hβ : 0 < β) {η : ℝ} (hη : 0 < η) :
    ∃ (u : Matrix.unitaryGroup ι ℂ) (a b : ι → ℝ) (N : ℕ) (i0 : ι),
      entropy (stairOutput β (spectralStair u β (pathList (linearPath a b N) 0 (N + 1))) rho) < η ∧
      entropy rho -
          entropy (stairOutput β (spectralStair u β (pathList (linearPath a b N) 0 (N + 1))) rho) ≤
        β * stairHeat β (spectralStair u β (pathList (linearPath a b N) 0 (N + 1))) rho ∧
      β * stairHeat β (spectralStair u β (pathList (linearPath a b N) 0 (N + 1))) rho ≤
        entropy rho -
          entropy (stairOutput β (spectralStair u β (pathList (linearPath a b N) 0 (N + 1))) rho) +
            η ∧
      ∀ k, k < N → ∀ i, i ≠ i0 →
        levelGap β (linearPath a b N k) i0 i < levelGap β (linearPath a b N (k + 1)) i0 i := by
  obtain ⟨u, p, hρ, hp0, hp1⟩ : ∃ (u : Matrix.unitaryGroup ι ℂ) (p : ι → ℝ),
      spectralLift u p = rho ∧ (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 :=
    ⟨_, _, spectralLift_eigenvalues hrho.1, fun i => hrho.eigenvalues_nonneg i,
      (eigenvalues_sum_trace hrho.1).trans (congrArg Complex.re htr)⟩
  subst hρ
  obtain ⟨i0⟩ : Nonempty ι := inferInstance
  obtain ⟨ε, hε0, hε1, hεη⟩ := exists_mixUniform_klDiv_le hp0 hp1 (half_pos hη)
  have ha := mixUniform_full hp0 hp1 hε0 hε1
  obtain ⟨δ, hδ0, hδε, hδ1, hδη⟩ := exists_mix_point_entropy_lt_below i0 hη hε0
  have hb := mixUniform_full (pointSpectrum_nonneg i0) (pointSpectrum_sum i0) hδ0 hδ1
  obtain ⟨N, hN0, hNη⟩ := exists_steps (pathConstant_nonneg ha hb) (half_pos hη)
  obtain ⟨hout, hdef⟩ := linear_staircase u hβ.ne' htr ha hb hN0
  obtain ⟨hbal, hdnn⟩ := stair_balance β (spectralStair u β (pathList
    (linearPath (mixUniform p ε) (mixUniform (pointSpectrum i0) δ) N) 0 (N + 1))) hrho htr
  refine ⟨u, mixUniform p ε, mixUniform (pointSpectrum i0) δ, N, i0, ?_, ?_, ?_, ?_⟩
  · rw [hout, entropy_spectralLift]
    exact hδη
  · linarith
  · linarith
  · intro k hk i hi
    exact linearPath_gap_lt hβ ha.1 hb.1 (by omega)
      (mixUniform_cross hp0 hp1 hε1 hδ0 hδε hi)

end Gaps

/-! ## Relative entropy against an arbitrary reference state

For a reference `b` put `K = -log b`, with the native logarithm sending a zero eigenvalue to zero.
The relative entropy of `a` against `b` is the change of the mean of `K` minus the change of the
spectral entropy. Under support inclusion the entropy change is therefore bounded by the change of
the mean of `K`, with equality only at `a = b`. The Gibbs balance of `relativeEntropy_gibbs_eq` is
the case `b = gibbsState`. -/

section Reference
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Mean of the reference operator `K = -log b` in the state `a`. -/
def modularMean (b a : Matrix ι ι ℂ) : ℝ := -(a * matrixLog b).trace.re

/-- Relative entropy is the change of the reference mean minus the change of entropy. -/
theorem relativeEntropy_eq_modular_sub_entropy {a b : Matrix ι ι ℂ}
    (ha : a.IsHermitian) (hb : b.IsHermitian) :
    relativeEntropy a b =
      (modularMean b a - modularMean b b) - (entropy a - entropy b) := by
  rw [relativeEntropy_eq ha, modularMean, modularMean, entropy_eq_neg_trace_mul_log hb]
  ring

/-- Under support inclusion, the entropy change is at most the change of the reference mean. -/
theorem entropy_change_le_modular {a b : Matrix ι ι ℂ}
    (ha : a.PosSemidef) (hb : b.PosSemidef) (hta : a.trace = 1) (htb : b.trace = 1)
    (hker : SupportLE a b) :
    entropy a - entropy b ≤ modularMean b a - modularMean b b := by
  have h := relativeEntropy_nonneg ha hb hta htb hker
  rw [relativeEntropy_eq_modular_sub_entropy ha.1 hb.1] at h
  linarith

/-- The entropy change equals the change of the reference mean only at the reference state. -/
theorem entropy_change_eq_modular_iff {a b : Matrix ι ι ℂ}
    (ha : a.PosSemidef) (hb : b.PosSemidef) (hta : a.trace = 1) (htb : b.trace = 1)
    (hker : SupportLE a b) :
    entropy a - entropy b = modularMean b a - modularMean b b ↔ a = b := by
  rw [← relativeEntropy_eq_zero_iff ha hb hta htb hker,
    relativeEntropy_eq_modular_sub_entropy ha.1 hb.1]
  constructor <;> intro h <;> linarith

end Reference

/-- Control: against the maximally mixed qubit reference, a pure basis state has zero change of
the reference mean and positive relative entropy, so the relative entropy is not bounded by the
change of the reference mean without a nonnegative entropy change. -/
theorem modular_gap_control :
    modularMean (spectralLift (1 : Matrix.unitaryGroup (Fin 2) ℂ) (fun _ => (1 / 2 : ℝ)))
        (spectralLift (1 : Matrix.unitaryGroup (Fin 2) ℂ) ![1, 0]) -
      modularMean (spectralLift (1 : Matrix.unitaryGroup (Fin 2) ℂ) (fun _ => (1 / 2 : ℝ)))
        (spectralLift (1 : Matrix.unitaryGroup (Fin 2) ℂ) (fun _ => (1 / 2 : ℝ))) <
      relativeEntropy (spectralLift (1 : Matrix.unitaryGroup (Fin 2) ℂ) ![1, 0])
        (spectralLift (1 : Matrix.unitaryGroup (Fin 2) ℂ) (fun _ => (1 / 2 : ℝ))) := by
  rw [relativeEntropy_eq_modular_sub_entropy (spectralLift_hermitian _ _)
    (spectralLift_hermitian _ _), entropy_spectralLift, entropy_spectralLift]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.negMulLog, one_div, Real.log_inv, Real.log_one, Real.log_zero]
  nlinarith

end

end OperatorKO7.Meta.BoundaryObserver.ThermalStaircase
