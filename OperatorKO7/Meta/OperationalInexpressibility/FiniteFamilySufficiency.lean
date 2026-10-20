import OperatorKO7.Meta.OperationalInexpressibility.SufficiencyInstance

/-!
# Minimal sufficiency for finite families

For a finite family of rational likelihoods and a prior of full support, sufficiency of a
statistic of the sample for the parameter is the factorization of the likelihood. The posterior
map is sufficient and is a function of every sufficient statistic, and two samples have equal
posteriors exactly when their likelihood vectors are proportional.

Relation: equality of posteriors on samples of positive weight.
Property: factorization criterion; minimal sufficiency of the posterior map.
Trust: kernel only.
Scope: finite parameter and sample types; rational likelihoods; full-support prior where stated.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.FiniteFamilySufficiency

open OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery
open OperatorKO7.Meta.OperationalInexpressibility.SufficiencyInstance

universe u v w

/-- A finite family of rational probability vectors on `Y`, indexed by the parameter. -/
structure FiniteFamily (Θ : Type u) (Y : Type v) [Fintype Y] where
  p : Θ → Y → ℚ
  nonneg : ∀ θ y, 0 ≤ p θ y
  sum_one : ∀ θ, ∑ y, p θ y = 1

variable {Θ : Type u} {Y : Type v} [Fintype Θ] [DecidableEq Θ] [Fintype Y] [DecidableEq Y]

/-- The joint model: parameter from `π`, sample from `p θ`, observation the sample. -/
noncomputable def familyModel (F : FiniteFamily Θ Y) (π : Θ → ℚ) (hπ0 : ∀ θ, 0 ≤ π θ)
    (hπ1 : ∑ θ, π θ = 1) : RationalObservationModel (Θ × Y) Y :=
  deterministicModel (fun x => π x.1 * F.p x.1 x.2)
    (fun x => mul_nonneg (hπ0 x.1) (F.nonneg x.1 x.2))
    (by
      rw [Fintype.sum_prod_type]
      have h : ∀ θ : Θ, (∑ y, π θ * F.p θ y) = π θ * 1 := by
        intro θ
        rw [← Finset.mul_sum, F.sum_one]
      simp only [h]
      simpa using hπ1)
    Prod.snd

variable (F : FiniteFamily Θ Y) (π : Θ → ℚ) (hπ0 : ∀ θ, 0 ≤ π θ) (hπ1 : ∑ θ, π θ = 1)

theorem joint_familyModel (θ : Θ) (y : Y) :
    joint (familyModel F π hπ0 hπ1) Prod.fst θ y = π θ * F.p θ y := by
  classical
  unfold joint familyModel deterministicModel
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single θ]
  · rw [Finset.sum_eq_single y]
    · simp
    · intro y' _ hy'
      simp [hy']
    · intro hy
      exact absurd (Finset.mem_univ y) hy
  · intro θ' _ hθ'
    simp [hθ']
  · intro hθ
    exact absurd (Finset.mem_univ θ) hθ

omit [DecidableEq Θ] in
theorem observationMass_familyModel (y : Y) :
    observationMass (familyModel F π hπ0 hπ1) y = ∑ θ, π θ * F.p θ y := by
  classical
  unfold observationMass familyModel deterministicModel
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro θ _
  rw [Finset.sum_eq_single y]
  · simp
  · intro y' _ hy'
    simp [hy']
  · intro hy
    exact absurd (Finset.mem_univ y) hy

/-- Fisher and Neyman factorization with nonnegative factors. -/
def FactorizationSufficient {S : Type*} (T : Y → S) : Prop :=
  ∃ (g : Θ → S → ℚ) (h : Y → ℚ), (∀ θ s, 0 ≤ g θ s) ∧ (∀ y, 0 ≤ h y) ∧
    ∀ θ y, F.p θ y = g θ (T y) * h y

/-- Two samples whose likelihood vectors are positive multiples of each other. -/
def LikelihoodProportional (y y' : Y) : Prop :=
  ∃ c : ℚ, 0 < c ∧ ∀ θ, F.p θ y = c * F.p θ y'

private theorem observationMass_nonneg {X : Type*} {O : Type*} [Fintype X] [Fintype O]
    (M : RationalObservationModel X O) (o : O) : 0 ≤ observationMass M o := by
  unfold observationMass
  exact Finset.sum_nonneg fun x _ => mul_nonneg (M.prior_nonneg x) (M.kernel_nonneg x o)

omit [DecidableEq Θ] in
/-- A zero mass forces every likelihood to vanish. -/
theorem p_eq_zero_of_observationMass_eq_zero (hπpos : ∀ θ, 0 < π θ) {y : Y}
    (hy : observationMass (familyModel F π hπ0 hπ1) y = 0) (θ : Θ) : F.p θ y = 0 := by
  classical
  have hsum := observationMass_familyModel F π hπ0 hπ1 y
  rw [hy] at hsum
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun θ _ => mul_nonneg (hπ0 θ) (F.nonneg θ y))).1 hsum.symm θ (Finset.mem_univ θ)
  exact (mul_eq_zero.1 hall).resolve_left (hπpos θ).ne'

theorem posterior?_familyModel_eq_iff (hπpos : ∀ θ, 0 < π θ) {y y' : Y}
    (hy : observationMass (familyModel F π hπ0 hπ1) y ≠ 0)
    (hy' : observationMass (familyModel F π hπ0 hπ1) y' ≠ 0) :
    posterior? (familyModel F π hπ0 hπ1) Prod.fst y =
        posterior? (familyModel F π hπ0 hπ1) Prod.fst y' ↔
      LikelihoodProportional F y y' := by
  classical
  have hmy : 0 < observationMass (familyModel F π hπ0 hπ1) y :=
    lt_of_le_of_ne (observationMass_nonneg _ y) (Ne.symm hy)
  have hmy' : 0 < observationMass (familyModel F π hπ0 hπ1) y' :=
    lt_of_le_of_ne (observationMass_nonneg _ y') (Ne.symm hy')
  constructor
  · intro h
    have hfun : (fun v => joint (familyModel F π hπ0 hπ1) Prod.fst v y /
          observationMass (familyModel F π hπ0 hπ1) y) =
        (fun v => joint (familyModel F π hπ0 hπ1) Prod.fst v y' /
          observationMass (familyModel F π hπ0 hπ1) y') := by
      have h' := h
      rw [posterior?, posterior?, if_neg hy, if_neg hy'] at h'
      exact Option.some.inj h'
    refine ⟨observationMass (familyModel F π hπ0 hπ1) y /
      observationMass (familyModel F π hπ0 hπ1) y', div_pos hmy hmy', fun θ => ?_⟩
    have hv := congrFun hfun θ
    rw [joint_familyModel, joint_familyModel] at hv
    have hv' := hv
    field_simp at hv'
    have key : F.p θ y * observationMass (familyModel F π hπ0 hπ1) y' =
        F.p θ y' * observationMass (familyModel F π hπ0 hπ1) y := by
      have h2 : π θ * (F.p θ y * observationMass (familyModel F π hπ0 hπ1) y') =
          π θ * (F.p θ y' * observationMass (familyModel F π hπ0 hπ1) y) := by
        rw [← mul_assoc, ← mul_assoc]
        exact hv'
      exact mul_left_cancel₀ (hπpos θ).ne' h2
    field_simp
    linear_combination key
  · rintro ⟨c, hc, hprop⟩
    have hmass : observationMass (familyModel F π hπ0 hπ1) y =
        c * observationMass (familyModel F π hπ0 hπ1) y' := by
      rw [observationMass_familyModel, observationMass_familyModel]
      calc ∑ θ, π θ * F.p θ y = ∑ θ, π θ * (c * F.p θ y') := by
            apply Finset.sum_congr rfl
            intro θ _
            rw [hprop θ]
        _ = c * ∑ θ, π θ * F.p θ y' := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro θ _
            ring
    rw [posterior?, posterior?, if_neg hy, if_neg hy', Option.some.injEq]
    funext v
    rw [joint_familyModel, joint_familyModel, hmass]
    rw [hprop v]
    field_simp
    ring

/-- **Sufficiency is factorization** for a full-support prior. -/
theorem sufficient_familyModel_iff_factorization (hπpos : ∀ θ, 0 < π θ) {S : Type w} (T : Y → S) :
    Sufficient (familyModel F π hπ0 hπ1) Prod.fst T ↔ FactorizationSufficient F T := by
  classical
  constructor
  · intro hT
    let g : Θ → S → ℚ := fun θ t =>
      if h : ∃ y₀, observationMass (familyModel F π hπ0 hπ1) y₀ ≠ 0 ∧ T y₀ = t then
        joint (familyModel F π hπ0 hπ1) Prod.fst θ (Classical.choose h) /
          observationMass (familyModel F π hπ0 hπ1) (Classical.choose h) / π θ
      else 0
    refine ⟨g, fun y => observationMass (familyModel F π hπ0 hπ1) y, ?_, ?_, ?_⟩
    · intro θ t
      dsimp only [g]
      split_ifs with h
      · have hmpos : 0 < observationMass (familyModel F π hπ0 hπ1) (Classical.choose h) :=
          lt_of_le_of_ne (observationMass_nonneg _ _) (Ne.symm (Classical.choose_spec h).1)
        have hj : 0 ≤ joint (familyModel F π hπ0 hπ1) Prod.fst θ (Classical.choose h) :=
          joint_nonneg _ _ _ _
        exact div_nonneg (div_nonneg hj hmpos.le) (hπpos θ).le
      · norm_num
    · intro y
      exact observationMass_nonneg _ y
    · intro θ y
      dsimp only [g]
      by_cases hy : observationMass (familyModel F π hπ0 hπ1) y = 0
      · rw [hy, mul_zero]
        exact p_eq_zero_of_observationMass_eq_zero F π hπ0 hπ1 hπpos hy θ
      · have hex : ∃ y₀, observationMass (familyModel F π hπ0 hπ1) y₀ ≠ 0 ∧ T y₀ = T y :=
          ⟨y, hy, rfl⟩
        rw [dif_pos hex]
        have hmchoose : observationMass (familyModel F π hπ0 hπ1) (Classical.choose hex) ≠ 0 :=
          (Classical.choose_spec hex).1
        have hchoose : T (Classical.choose hex) = T y := (Classical.choose_spec hex).2
        have hpost := hT (Classical.choose hex) y hmchoose hy hchoose
        rw [posterior?, posterior?, if_neg hmchoose, if_neg hy, Option.some.injEq] at hpost
        have hval := congrFun hpost θ
        rw [joint_familyModel, joint_familyModel] at hval
        have hval' := hval
        field_simp at hval'
        have key : F.p θ (Classical.choose hex) *
            observationMass (familyModel F π hπ0 hπ1) y =
            F.p θ y * observationMass (familyModel F π hπ0 hπ1) (Classical.choose hex) := by
          have h2 : π θ * (F.p θ (Classical.choose hex) *
                observationMass (familyModel F π hπ0 hπ1) y) =
              π θ * (F.p θ y *
                observationMass (familyModel F π hπ0 hπ1) (Classical.choose hex)) := by
            rw [← mul_assoc, ← mul_assoc]
            exact hval'
          exact mul_left_cancel₀ (hπpos θ).ne' h2
        have hgval : joint (familyModel F π hπ0 hπ1) Prod.fst θ (Classical.choose hex) /
              observationMass (familyModel F π hπ0 hπ1) (Classical.choose hex) / π θ =
            F.p θ y / observationMass (familyModel F π hπ0 hπ1) y := by
          rw [joint_familyModel, mul_div_assoc,
            mul_div_cancel_left₀ (F.p θ (Classical.choose hex) /
              observationMass (familyModel F π hπ0 hπ1) (Classical.choose hex)) (hπpos θ).ne']
          rw [div_eq_div_iff hmchoose hy]
          exact key
        rw [hgval, div_mul_cancel₀ _ hy]
  · rintro ⟨g, h, hg0, hh0, hfac⟩
    intro y y' hy hy' hTy
    have hhne : h y' ≠ 0 := by
      intro hzero
      have : observationMass (familyModel F π hπ0 hπ1) y' = 0 := by
        rw [observationMass_familyModel]
        apply Finset.sum_eq_zero
        intro θ _
        rw [hfac θ y', hzero]
        ring
      exact hy' this
    have hhne_y : h y ≠ 0 := by
      intro hzero
      have : observationMass (familyModel F π hπ0 hπ1) y = 0 := by
        rw [observationMass_familyModel]
        apply Finset.sum_eq_zero
        intro θ _
        rw [hfac θ y, hzero]
        ring
      exact hy this
    have hmass : observationMass (familyModel F π hπ0 hπ1) y =
        (h y / h y') * observationMass (familyModel F π hπ0 hπ1) y' := by
      rw [observationMass_familyModel, observationMass_familyModel]
      calc ∑ θ, π θ * F.p θ y = ∑ θ, π θ * ((h y / h y') * F.p θ y') := by
            apply Finset.sum_congr rfl
            intro θ _
            rw [hfac θ y, hfac θ y', hTy]
            field_simp
            ring
        _ = (h y / h y') * ∑ θ, π θ * F.p θ y' := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro θ _
            ring
    rw [posterior?, posterior?, if_neg hy, if_neg hy', Option.some.injEq]
    funext v
    rw [joint_familyModel, joint_familyModel, hmass]
    rw [hfac v y, hfac v y', hTy]
    field_simp
    ring

/-- **Minimal sufficiency of the posterior map.** -/
theorem posterior_minimalSufficient (hπpos : ∀ θ, 0 < π θ) :
    FactorizationSufficient F (posterior? (familyModel F π hπ0 hπ1) Prod.fst) ∧
      ∀ {S : Type w} (T : Y → S), FactorizationSufficient F T →
        ∀ y y', observationMass (familyModel F π hπ0 hπ1) y ≠ 0 →
          observationMass (familyModel F π hπ0 hπ1) y' ≠ 0 → T y = T y' →
            posterior? (familyModel F π hπ0 hπ1) Prod.fst y =
              posterior? (familyModel F π hπ0 hπ1) Prod.fst y' := by
  constructor
  · exact (sufficient_familyModel_iff_factorization F π hπ0 hπ1 hπpos
      (posterior? (familyModel F π hπ0 hπ1) Prod.fst)).1
      (fun _ _ _ _ h => h)
  · intro S T hT y y' hy hy' hTy
    exact (sufficient_familyModel_iff_factorization F π hπ0 hπ1 hπpos T).2 hT
      y y' hy hy' hTy

private def fullSupportFixtureP (θ y : Fin 2) : ℚ :=
  if θ = 0 then 1 / 2 else if y = 0 then 1 else 0

private def fullSupportFixture : FiniteFamily (Fin 2) (Fin 2) where
  p := fullSupportFixtureP
  nonneg := by
    intro θ y
    unfold fullSupportFixtureP
    split_ifs <;> norm_num
  sum_one := by
    intro θ
    unfold fullSupportFixtureP
    fin_cases θ <;> norm_num [Fin.sum_univ_two]

private theorem fullSupportFixture_p00 : fullSupportFixture.p 0 0 = 1 / 2 := by
  norm_num [fullSupportFixture, fullSupportFixtureP]

private theorem fullSupportFixture_p01 : fullSupportFixture.p 0 1 = 1 / 2 := by
  norm_num [fullSupportFixture, fullSupportFixtureP]

private theorem fullSupportFixture_p10 : fullSupportFixture.p 1 0 = 1 := by
  norm_num [fullSupportFixture, fullSupportFixtureP]

private theorem fullSupportFixture_p11 : fullSupportFixture.p 1 1 = 0 := by
  norm_num [fullSupportFixture, fullSupportFixtureP]

/-- **Full support is required.** A prior with a zero entry makes a constant statistic sufficient
while the likelihood does not factor through it. -/
theorem fullSupport_is_required : ∃ (F : FiniteFamily (Fin 2) (Fin 2)) (π : Fin 2 → ℚ)
    (hπ0 : ∀ θ, 0 ≤ π θ) (hπ1 : ∑ θ, π θ = 1),
    Sufficient (familyModel F π hπ0 hπ1) Prod.fst (fun _ => ()) ∧
      ¬ FactorizationSufficient F (fun _ : Fin 2 => ()) := by
  classical
  have hπ0 : ∀ θ : Fin 2, 0 ≤ (fun θ : Fin 2 => if θ = 0 then (1 : ℚ) else 0) θ := by
    intro θ
    show 0 ≤ (if θ = 0 then (1 : ℚ) else 0)
    split_ifs <;> norm_num
  have hπ1 : ∑ θ : Fin 2, (fun θ : Fin 2 => if θ = 0 then (1 : ℚ) else 0) θ = 1 := by
    rw [Fin.sum_univ_two]
    norm_num
  refine ⟨fullSupportFixture, fun θ => if θ = 0 then (1 : ℚ) else 0, hπ0, hπ1, ?_, ?_⟩
  · intro y y' _ _ _
    have hval : ∀ y : Fin 2, posterior?
          (familyModel fullSupportFixture (fun θ : Fin 2 => if θ = 0 then (1 : ℚ) else 0) hπ0 hπ1)
          Prod.fst y = some (fun θ : Fin 2 => if θ = 0 then (1 : ℚ) else 0) := by
      intro y
      unfold posterior?
      have hm : observationMass
          (familyModel fullSupportFixture (fun θ : Fin 2 => if θ = 0 then (1 : ℚ) else 0) hπ0 hπ1)
          y = 1 / 2 := by
        rw [observationMass_familyModel]
        fin_cases y <;> rw [Fin.sum_univ_two] <;>
          norm_num [fullSupportFixture, fullSupportFixtureP]
      rw [if_neg (by rw [hm]; norm_num), Option.some.injEq]
      funext v
      rw [joint_familyModel, hm]
      fin_cases v <;> fin_cases y <;> norm_num [fullSupportFixture, fullSupportFixtureP]
    rw [hval y, hval y']
  · rintro ⟨g, h, hg0, hh0, hfac⟩
    have h10 : g 1 () * h 0 = 1 := by
      have := hfac 1 0
      rw [fullSupportFixture_p10] at this
      exact this.symm
    have h11 : g 1 () * h 1 = 0 := by
      have := hfac 1 1
      rw [fullSupportFixture_p11] at this
      exact this.symm
    have h01 : g 0 () * h 1 = 1 / 2 := by
      have := hfac 0 1
      rw [fullSupportFixture_p01] at this
      exact this.symm
    have hg1 : g 1 () ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at h10
      norm_num at h10
    have hh1 : h 1 = 0 := (mul_eq_zero.1 h11).resolve_left hg1
    rw [hh1, mul_zero] at h01
    norm_num at h01

end OperatorKO7.Meta.OperationalInexpressibility.FiniteFamilySufficiency
