import OperatorKO7.Meta.BoundaryObserver.ThermalStaircase

/-!
# Reset given a record

Manuscript: Corollary `cor:conditional-reset`.

A diagonal state with law `p` on a finite carrier `X` and an observer `q : X → O` give, for every
record value `o` of positive mass, the normalized restriction `ρ_o` of the state to the fiber of
`o`. A record-conditioned operation is a family `T_o` of finite thermal operations, `T_o` applied
to `ρ_o`, with heat `∑ₒ p(o) Q_{T_o}` and conditional output entropy `∑ₒ p(o) S(σ_{T_o})`.
Every such family pays `β ∑ₒ p(o) Q_{T_o} ≥ H(X | q(X)) - ∑ₒ p(o) S(σ_{T_o})`, the bound is
approached, and the least heat limit at vanishing conditional output entropy is
`H(X | q(X)) / β`. That limit is zero exactly when no merged pair of `q` carries mass on both of
its states, and it equals `S(ρ) / β` exactly when `q` is constant on the support of `p`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix Filter Topology
open scoped BigOperators ComplexOrder
open OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Thermal
open OperatorKO7.Meta.BoundaryObserver.ThermalStaircase

namespace OperatorKO7.Meta.BoundaryObserver.ConditionalReset

variable {X O : Type} [Fintype X] [DecidableEq X] [Fintype O] [DecidableEq O]

/-- The mass `p(o)` of the record value `o`. -/
noncomputable def recordMass (p : X → ℝ) (q : X → O) (o : O) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => q x = o), p x

/-- The conditional law of `X` given the record value `o`, zero outside the fiber. -/
noncomputable def condLaw (p : X → ℝ) (q : X → O) (o : O) (x : X) : ℝ :=
  if q x = o then p x / recordMass p q o else 0

/-- The normalized restriction `ρ_o` of the diagonal state to the fiber of `o`. -/
noncomputable def condState (p : X → ℝ) (q : X → O) (o : O) : Matrix X X ℂ :=
  realDiagonal (condLaw p q o)

/-- Shannon entropy of a finite law, in nats. -/
noncomputable def shannon {A : Type} [Fintype A] (r : A → ℝ) : ℝ := ∑ a, Real.negMulLog (r a)

/-- The conditional entropy `H(X | q(X)) = ∑ₒ p(o) H(p(· | o))`. -/
noncomputable def condEntropy (p : X → ℝ) (q : X → O) : ℝ :=
  ∑ o, recordMass p q o * shannon (condLaw p q o)

/-- The heat `∑ₒ p(o) Q_{T_o}` of a record-conditioned operation. -/
noncomputable def condHeat (p : X → ℝ) (q : X → O) (T : O → ThermalOperation X) (β : ℝ) : ℝ :=
  ∑ o, recordMass p q o * (T o).heat (condState p q o) β

/-- The conditional output entropy `∑ₒ p(o) S(σ_{T_o})`. -/
noncomputable def condOutputEntropy (p : X → ℝ) (q : X → O) (T : O → ThermalOperation X)
    (β : ℝ) : ℝ :=
  ∑ o, recordMass p q o * entropy ((T o).output (condState p q o) β)

theorem negMulLog_eq_zero_iff_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.negMulLog x = 0 ↔ x = 0 ∨ x = 1 := by
  rw [show Real.negMulLog x = -x * Real.log x from rfl, mul_eq_zero, neg_eq_zero,
    Real.log_eq_zero]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
    · linarith
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))

section Laws

variable (p : X → ℝ) (q : X → O)

theorem recordMass_nonneg (hp : ∀ x, 0 ≤ p x) (o : O) : 0 ≤ recordMass p q o :=
  Finset.sum_nonneg fun x _ => hp x

theorem sum_recordMass (hp1 : ∑ x, p x = 1) : ∑ o, recordMass p q o = 1 := by
  unfold recordMass
  rw [Finset.sum_fiberwise Finset.univ q p, hp1]

theorem le_recordMass (hp : ∀ x, 0 ≤ p x) (x : X) : p x ≤ recordMass p q (q x) :=
  Finset.single_le_sum (fun y _ => hp y) (by simp)

theorem condLaw_nonneg (hp : ∀ x, 0 ≤ p x) (o : O) (x : X) : 0 ≤ condLaw p q o x := by
  unfold condLaw
  split_ifs
  · exact div_nonneg (hp x) (recordMass_nonneg p q hp o)
  · exact le_rfl

theorem condLaw_le_one (hp : ∀ x, 0 ≤ p x) (o : O) (x : X) : condLaw p q o x ≤ 1 := by
  unfold condLaw
  split_ifs with h
  · subst h
    rcases (recordMass_nonneg p q hp (q x)).eq_or_lt with h0 | h0
    · rw [← h0, div_zero]; exact zero_le_one
    · exact (div_le_one h0).2 (le_recordMass p q hp x)
  · exact zero_le_one

theorem sum_condLaw (o : O) (hm : 0 < recordMass p q o) : ∑ x, condLaw p q o x = 1 := by
  unfold condLaw
  rw [← Finset.sum_filter, ← Finset.sum_div]
  exact div_self hm.ne'

theorem condState_posSemidef (hp : ∀ x, 0 ≤ p x) (o : O) : (condState p q o).PosSemidef :=
  Matrix.PosSemidef.diagonal fun x => Complex.zero_le_real.mpr (condLaw_nonneg p q hp o x)

theorem condState_trace (o : O) (hm : 0 < recordMass p q o) : (condState p q o).trace = 1 := by
  rw [condState, realDiagonal, Matrix.trace_diagonal]
  rw [← Complex.ofReal_sum, sum_condLaw p q o hm, Complex.ofReal_one]

theorem rotate_one (a : Matrix X X ℂ) : rotate (1 : Matrix.unitaryGroup X ℂ) a = a := by
  simp [rotate]

/-- `S(ρ_o) = H(p(· | o))`: the diagonal state carries the entropy of its diagonal. -/
theorem entropy_condState (o : O) : entropy (condState p q o) = shannon (condLaw p q o) := by
  have h := entropy_spectralLift (1 : Matrix.unitaryGroup X ℂ) (condLaw p q o)
  rwa [spectralLift, rotate_one] at h

theorem entropy_realDiagonal : entropy (realDiagonal p) = shannon p := by
  have h := entropy_spectralLift (1 : Matrix.unitaryGroup X ℂ) p
  rwa [spectralLift, rotate_one] at h

/-- The displayed identity `H(X | q(X)) = ∑ₒ p(o) S(ρ_o)`. -/
theorem condEntropy_eq_sum_entropy :
    condEntropy p q = ∑ o, recordMass p q o * entropy (condState p q o) := by
  unfold condEntropy
  simp_rw [entropy_condState]

theorem shannon_condLaw_nonneg (hp : ∀ x, 0 ≤ p x) (o : O) : 0 ≤ shannon (condLaw p q o) :=
  Finset.sum_nonneg fun x _ =>
    Real.negMulLog_nonneg (condLaw_nonneg p q hp o x) (condLaw_le_one p q hp o x)

/-- One record value of the chain rule:
`p(o) H(p(· | o)) = ∑_{x ∈ q⁻¹(o)} -p(x) log p(x) + p(o) log p(o)`. -/
theorem mass_mul_shannon (hp : ∀ x, 0 ≤ p x) (o : O) :
    recordMass p q o * shannon (condLaw p q o) =
      (∑ x ∈ Finset.univ.filter (fun x => q x = o), Real.negMulLog (p x)) -
        Real.negMulLog (recordMass p q o) := by
  rcases (recordMass_nonneg p q hp o).eq_or_lt with h0 | h0
  · have hz : ∀ x ∈ Finset.univ.filter (fun x => q x = o), p x = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hp x).1 h0.symm
    rw [← h0, zero_mul, Real.negMulLog_zero, sub_zero]
    exact (Finset.sum_eq_zero fun x hx => by rw [hz x hx, Real.negMulLog_zero]).symm
  · unfold shannon
    rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => q x = o)]
    have hout : ∑ x ∈ Finset.univ.filter (fun x => ¬ q x = o),
        recordMass p q o * Real.negMulLog (condLaw p q o x) = 0 :=
      Finset.sum_eq_zero fun x hx => by
        rw [Finset.mem_filter] at hx
        simp [condLaw, hx.2]
    rw [hout, add_zero]
    have hin : ∀ x ∈ Finset.univ.filter (fun x => q x = o),
        recordMass p q o * Real.negMulLog (condLaw p q o x) =
          Real.negMulLog (p x) - p x / recordMass p q o * Real.negMulLog (recordMass p q o) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have hpx : p x = recordMass p q o * (p x / recordMass p q o) := by field_simp
      have hmul := Real.negMulLog_mul (recordMass p q o) (p x / recordMass p q o)
      rw [← hpx] at hmul
      simp only [condLaw, if_pos hx.2]
      linarith
    rw [Finset.sum_congr rfl hin, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div]
    rw [show ∑ x ∈ Finset.univ.filter (fun x => q x = o), p x = recordMass p q o from rfl,
      div_self h0.ne', one_mul]

/-- The chain rule `H(X | q(X)) = H(X) - H(q(X))`. -/
theorem condEntropy_chain (hp : ∀ x, 0 ≤ p x) :
    condEntropy p q = shannon p - shannon (recordMass p q) := by
  unfold condEntropy
  simp_rw [mass_mul_shannon p q hp]
  rw [Finset.sum_sub_distrib, Finset.sum_fiberwise Finset.univ q (fun x => Real.negMulLog (p x))]
  rfl

end Laws

section Heat

variable [Nonempty X] (p : X → ℝ) (q : X → O)

/-- **The record-conditioned heat bound.** -/
theorem condHeat_bound (hp : ∀ x, 0 ≤ p x) (T : O → ThermalOperation X) {β : ℝ} (hβ : 0 < β) :
    condEntropy p q - condOutputEntropy p q T β ≤ β * condHeat p q T β := by
  rw [condEntropy_eq_sum_entropy, condOutputEntropy, condHeat, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun o _ => ?_
  rcases (recordMass_nonneg p q hp o).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · have h := (T o).landauer (condState_posSemidef p q hp o) (condState_trace p q o h0) hβ
    nlinarith

theorem condOutputEntropy_nonneg (hp : ∀ x, 0 ≤ p x) (T : O → ThermalOperation X) (β : ℝ) :
    0 ≤ condOutputEntropy p q T β := by
  refine Finset.sum_nonneg fun o _ => ?_
  rcases (recordMass_nonneg p q hp o).eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]
  · obtain ⟨hd, ht⟩ := (T o).output_density (condState_posSemidef p q hp o)
      (condState_trace p q o h0) β
    exact mul_nonneg h0.le (entropy_nonneg_density hd ht)

/-- **Attainment.** For every `η > 0` some record-conditioned operation has conditional output
entropy below `η` and `β` times its heat within `η` of `H(X | q(X))`. -/
theorem condHeat_attains (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) {β : ℝ} (hβ : 0 < β)
    {η : ℝ} (hη : 0 < η) :
    ∃ T : O → ThermalOperation X, condOutputEntropy p q T β < η ∧
      |β * condHeat p q T β - condEntropy p q| < η := by
  have hchoice : ∀ o, ∃ T : ThermalOperation X, 0 < recordMass p q o →
      entropy (T.output (condState p q o) β) < η ∧
        |β * T.heat (condState p q o) β - entropy (condState p q o)| < η := by
    intro o
    by_cases h : 0 < recordMass p q o
    · obtain ⟨T, h1, h2⟩ := heat_attains_landauer (condState_posSemidef p q hp o)
        (condState_trace p q o h) hβ hη
      exact ⟨T, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨ThermalOperation.idle, fun h' => absurd h' h⟩
  choose T hT using hchoice
  have hsum := sum_recordMass p q hp1
  obtain ⟨o₀, -, ho₀⟩ : ∃ o ∈ Finset.univ, 0 < recordMass p q o := by
    by_contra hcon
    push_neg at hcon
    have : ∑ o, recordMass p q o ≤ 0 := Finset.sum_nonpos fun o h => hcon o h
    linarith
  refine ⟨T, ?_, ?_⟩
  · calc condOutputEntropy p q T β < ∑ o, recordMass p q o * η := by
          refine Finset.sum_lt_sum (fun o _ => ?_) ⟨o₀, Finset.mem_univ _, ?_⟩
          · rcases (recordMass_nonneg p q hp o).eq_or_lt with h0 | h0
            · rw [← h0]; simp
            · exact mul_le_mul_of_nonneg_left (hT o h0).1.le h0.le
          · exact mul_lt_mul_of_pos_left (hT o₀ ho₀).1 ho₀
      _ = η := by rw [← Finset.sum_mul, hsum, one_mul]
  · rw [condHeat, condEntropy_eq_sum_entropy, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc |∑ o, (β * (recordMass p q o * (T o).heat (condState p q o) β) -
          recordMass p q o * entropy (condState p q o))|
        ≤ ∑ o, |β * (recordMass p q o * (T o).heat (condState p q o) β) -
          recordMass p q o * entropy (condState p q o)| := Finset.abs_sum_le_sum_abs _ _
      _ < ∑ o, recordMass p q o * η := by
          refine Finset.sum_lt_sum (fun o _ => ?_) ⟨o₀, Finset.mem_univ _, ?_⟩
          · rcases (recordMass_nonneg p q hp o).eq_or_lt with h0 | h0
            · rw [← h0]; simp
            · rw [show β * (recordMass p q o * (T o).heat (condState p q o) β) -
                  recordMass p q o * entropy (condState p q o) = recordMass p q o *
                  (β * (T o).heat (condState p q o) β - entropy (condState p q o)) by ring,
                abs_mul, abs_of_pos h0]
              exact mul_le_mul_of_nonneg_left (hT o h0).2.le h0.le
          · rw [show β * (recordMass p q o₀ * (T o₀).heat (condState p q o₀) β) -
                recordMass p q o₀ * entropy (condState p q o₀) = recordMass p q o₀ *
                (β * (T o₀).heat (condState p q o₀) β - entropy (condState p q o₀)) by ring,
              abs_mul, abs_of_pos ho₀]
            exact mul_lt_mul_of_pos_left (hT o₀ ho₀).2 ho₀
      _ = η := by rw [← Finset.sum_mul, hsum, one_mul]

/-- **The least heat limit** among record-conditioned operations whose conditional output entropy
tends to zero is `H(X | q(X)) / β`. -/
theorem condHeat_least_limit (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) {β : ℝ} (hβ : 0 < β) :
    IsLeast {L : ℝ | ∃ T : ℕ → O → ThermalOperation X,
        Tendsto (fun n => condOutputEntropy p q (T n) β) atTop (𝓝 0) ∧
          Tendsto (fun n => condHeat p q (T n) β) atTop (𝓝 L)} (condEntropy p q / β) := by
  refine ⟨?_, ?_⟩
  · have hη : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
    choose T hT using fun n : ℕ => condHeat_attains p q hp hp1 hβ (hη n)
    refine ⟨T, ?_, ?_⟩
    · exact squeeze_zero (fun n => condOutputEntropy_nonneg p q hp (T n) β)
        (fun n => (hT n).1.le) tendsto_one_div_add_atTop_nhds_zero_nat
    · have hdiff : Tendsto (fun n => β * condHeat p q (T n) β - condEntropy p q) atTop (𝓝 0) :=
        squeeze_zero_norm (fun n => (hT n).2.le) tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun n => (β * condHeat p q (T n) β - condEntropy p q + condEntropy p q)
          / β) atTop (𝓝 ((0 + condEntropy p q) / β)) :=
        (hdiff.add_const _).div_const β
      rw [zero_add] at h2
      refine h2.congr fun n => ?_
      field_simp
  · rintro L ⟨T, hS, hQ⟩
    have hle : condEntropy p q - 0 ≤ β * L :=
      le_of_tendsto_of_tendsto' (hS.const_sub (condEntropy p q)) (hQ.const_mul β)
        (fun n => condHeat_bound p q hp (T n) hβ)
    rw [div_le_iff₀ hβ]
    linarith

end Heat

section Zero

variable (p : X → ℝ) (q : X → O)

/-- The limit `H(X | q(X)) / β` vanishes if and only if no merged pair of `q` carries positive
mass on both of its states. -/
theorem condEntropy_eq_zero_iff (hp : ∀ x, 0 ≤ p x) :
    condEntropy p q = 0 ↔ ∀ x y, x ≠ y → q x = q y → ¬ (0 < p x ∧ 0 < p y) := by
  have hterm : ∀ o, 0 ≤ recordMass p q o * shannon (condLaw p q o) := fun o =>
    mul_nonneg (recordMass_nonneg p q hp o) (shannon_condLaw_nonneg p q hp o)
  constructor
  · intro h x y hxy hq ⟨hx, hy⟩
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun o _ => hterm o).1 h (q x) (Finset.mem_univ _)
    have hpair : p x + p y ≤ recordMass p q (q x) := by
      rw [← Finset.sum_pair hxy]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (by intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl <;> simp [hq])
        (fun z _ _ => hp z)
    have hm : 0 < recordMass p q (q x) := by linarith
    have hs : shannon (condLaw p q (q x)) = 0 := by
      rcases mul_eq_zero.1 hz with h0 | h0
      · linarith
      · exact h0
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun z _ =>
      Real.negMulLog_nonneg (condLaw_nonneg p q hp (q x) z)
        (condLaw_le_one p q hp (q x) z)).1 hs
    have hone : ∀ z, q z = q x → 0 < p z → p z = recordMass p q (q x) := by
      intro z hzq hzp
      have hc := (negMulLog_eq_zero_iff_of_nonneg (condLaw_nonneg p q hp (q x) z)).1
        (hall z (Finset.mem_univ _))
      simp only [condLaw, if_pos hzq] at hc
      rcases hc with hc | hc
      · exact absurd hc (div_pos hzp hm).ne'
      · rw [div_eq_one_iff_eq hm.ne'] at hc
        exact hc
    have h1 := hone x rfl hx
    have h2 := hone y hq.symm hy
    linarith
  · intro h
    refine Finset.sum_eq_zero fun o _ => ?_
    rcases (recordMass_nonneg p q hp o).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul]
    · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun z _ => ?_)
      rw [negMulLog_eq_zero_iff_of_nonneg (condLaw_nonneg p q hp o z)]
      unfold condLaw
      split_ifs with hzq
      · rcases (hp z).eq_or_lt with hz0 | hz0
        · left; rw [← hz0, zero_div]
        · right
          rw [div_eq_one_iff_eq h0.ne']
          symm
          unfold recordMass
          rw [Finset.sum_eq_single z]
          · intro y hy hyz
            rw [Finset.mem_filter] at hy
            rcases (hp y).eq_or_lt with hy0 | hy0
            · exact hy0.symm
            · exact absurd ⟨hy0, hz0⟩ (h y z hyz (hy.2.trans hzq.symm))
          · intro hz
            exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ z, hzq⟩) hz
      · left; rfl

/-- The limit equals `S(ρ) / β` if and only if `q` is constant on the support of `p`. -/
theorem condEntropy_eq_entropy_iff (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    condEntropy p q = entropy (realDiagonal p) ↔ ∀ x y, 0 < p x → 0 < p y → q x = q y := by
  rw [entropy_realDiagonal, condEntropy_chain p q hp]
  have hmass : ∀ o, 0 ≤ recordMass p q o := recordMass_nonneg p q hp
  have hle1 : ∀ o, recordMass p q o ≤ 1 := fun o => by
    rw [← sum_recordMass p q hp1]
    exact Finset.single_le_sum (fun o _ => hmass o) (Finset.mem_univ o)
  have hsh : shannon p - shannon (recordMass p q) = shannon p ↔
      ∀ o, recordMass p q o = 0 ∨ recordMass p q o = 1 := by
    rw [sub_eq_self]
    unfold shannon
    rw [Finset.sum_eq_zero_iff_of_nonneg fun o _ => Real.negMulLog_nonneg (hmass o) (hle1 o)]
    simp only [Finset.mem_univ, true_implies]
    exact forall_congr' fun o => negMulLog_eq_zero_iff_of_nonneg (hmass o)
  rw [hsh]
  constructor
  · intro h x y hx hy
    by_contra hne
    have hx1 : recordMass p q (q x) = 1 := by
      rcases h (q x) with h0 | h0
      · have := le_recordMass p q hp x; linarith
      · exact h0
    have hy1 : recordMass p q (q y) = 1 := by
      rcases h (q y) with h0 | h0
      · have := le_recordMass p q hp y; linarith
      · exact h0
    have h2 : recordMass p q (q x) + recordMass p q (q y) ≤ ∑ o, recordMass p q o := by
      rw [← Finset.sum_pair hne]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun o _ _ => hmass o)
    rw [sum_recordMass p q hp1] at h2
    linarith
  · intro h o
    by_cases hex : ∃ x, q x = o ∧ 0 < p x
    · obtain ⟨x, hxo, hxp⟩ := hex
      right
      rw [← hp1]
      unfold recordMass
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun z => q z = o)]
      have hout : ∑ z ∈ Finset.univ.filter (fun z => ¬ q z = o), p z = 0 :=
        Finset.sum_eq_zero fun z hz => by
          rw [Finset.mem_filter] at hz
          rcases (hp z).eq_or_lt with hz0 | hz0
          · exact hz0.symm
          · exact absurd ((h z x hz0 hxp).trans hxo) hz.2
      rw [hout, add_zero]
    · left
      push_neg at hex
      exact Finset.sum_eq_zero fun z hz => by
        rw [Finset.mem_filter] at hz
        exact le_antisymm (hex z hz.2) (hp z)

end Zero

end OperatorKO7.Meta.BoundaryObserver.ConditionalReset
