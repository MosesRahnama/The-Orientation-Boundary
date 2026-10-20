import OperatorKO7.Meta.OperationalInexpressibility.KTryVulnerability

set_option autoImplicit false

/-!
# Threshold acceptance on the exact posterior

`prop:threshold-acceptance` of the Observation-Boundary Principle (ledger row 16-025). On a finite
state set with weights `μ`, an observer `q` and a target `P`, the threshold rule accepts a record
`o` when its heaviest target class carries at least the fraction `τ` of the weight of the fiber of
`o`, and returns that class. It is Chow's error-reject rule with the exact posterior, so its
calibration holds by construction.

* `errorMass_le`: on the accepted records the rule errs on at most `(1 - τ)` times their weight,
  for every `τ` and every weight function.
* `thresholdAcceptance_tau_one_eq_observerRetained`: with positive weights the accepted set at
  `τ = 1` is `observerAccepted q P 1`, the set `S_1` of `thm:observer-measurable-refusal`, so its
  refused weight is `R_1^obs`.
* `leastTopFraction_errorMass_eq_repairFrontier`: at the least top-class fraction every record is
  accepted and the error is `repairFrontier μ q P 1`, the `R_1` of `thm:lift-refusal-frontier`,
  through `KTryVulnerability.repairFrontier_eq_sub_kTryVulnerability`.
* `acceptedSet_antitone`: a larger threshold accepts fewer states; the refused weight against the
  error between the two ends is the error-reject curve.

The QEC abstention decoder (`QEC.Codes.BranchLicense.accepted_cohort_mean_error_le`) is the instance
with errors as states, the syndrome as the record and the correction class as the target.

Relation: none. Trust: kernel-only, with `Classical.choice` for the choice of a heaviest class and
the decidability of real inequalities. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ThresholdAcceptance

open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
open OperatorKO7.Meta.OperationalInexpressibility.KTryVulnerability
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit

open scoped BigOperators

variable {X Q V : Type} [Fintype X] [Fintype Q] [DecidableEq Q] [Fintype V] [DecidableEq V]

/-- The weight of the fiber of the record `o`. -/
def fiberWeight (μ : X → ℝ) (q : X → Q) (o : Q) : ℝ :=
  ∑ x, if q x = o then μ x else 0

/-- The weight of the target class `v` inside the fiber of `o`. -/
def classWeight (μ : X → ℝ) (q : X → Q) (P : X → V) (o : Q) (v : V) : ℝ :=
  ∑ x, if q x = o ∧ P x = v then μ x else 0

omit [Fintype Q] in
theorem fiberWeight_def (μ : X → ℝ) (q : X → Q) (o : Q) :
    fiberWeight μ q o = ∑ x, if q x = o then μ x else 0 := rfl

omit [Fintype Q] [Fintype V] in
theorem classWeight_def (μ : X → ℝ) (q : X → Q) (P : X → V) (o : Q) (v : V) :
    classWeight μ q P o v = ∑ x, if q x = o ∧ P x = v then μ x else 0 := rfl

variable [Nonempty V]

/-- The weight of the heaviest target class inside the fiber of `o`. -/
noncomputable def topWeight (μ : X → ℝ) (q : X → Q) (P : X → V) (o : Q) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (classWeight μ q P o)

/-- A heaviest target class inside the fiber of `o`: the class the rule returns. -/
noncomputable def topClass (μ : X → ℝ) (q : X → Q) (P : X → V) (o : Q) : V :=
  Classical.choose (Finset.exists_max_image Finset.univ (classWeight μ q P o)
    Finset.univ_nonempty)

omit [Fintype Q] in
theorem classWeight_le_topWeight (μ : X → ℝ) (q : X → Q) (P : X → V) (o : Q) (v : V) :
    classWeight μ q P o v ≤ topWeight μ q P o :=
  Finset.le_sup' (classWeight μ q P o) (Finset.mem_univ v)

omit [Fintype Q] in
theorem classWeight_topClass (μ : X → ℝ) (q : X → Q) (P : X → V) (o : Q) :
    classWeight μ q P o (topClass μ q P o) = topWeight μ q P o := by
  have hspec := Classical.choose_spec (Finset.exists_max_image Finset.univ
    (classWeight μ q P o) Finset.univ_nonempty)
  apply le_antisymm (classWeight_le_topWeight μ q P o _)
  apply Finset.sup'_le
  intro v _
  exact hspec.2 v (Finset.mem_univ v)

/-- The threshold rule accepts the record `o` at threshold `τ`. -/
def Accepts (μ : X → ℝ) (q : X → Q) (P : X → V) (τ : ℝ) (o : Q) : Prop :=
  τ * fiberWeight μ q o ≤ topWeight μ q P o

omit [Fintype Q] in
theorem accepts_iff (μ : X → ℝ) (q : X → Q) (P : X → V) (τ : ℝ) (o : Q) :
    Accepts μ q P τ o ↔ τ * fiberWeight μ q o ≤ topWeight μ q P o := Iff.rfl

open Classical in
/-- The states with an accepted record. -/
noncomputable def acceptedSet (μ : X → ℝ) (q : X → Q) (P : X → V) (τ : ℝ) : Finset X :=
  Finset.univ.filter fun x => Accepts μ q P τ (q x)

omit [Fintype Q] in
theorem mem_acceptedSet (μ : X → ℝ) (q : X → Q) (P : X → V) (τ : ℝ) (x : X) :
    x ∈ acceptedSet μ q P τ ↔ Accepts μ q P τ (q x) := by
  classical
  simp [acceptedSet]

open Classical in
/-- The weight of the accepted states. -/
noncomputable def acceptedMass (μ : X → ℝ) (q : X → Q) (P : X → V) (τ : ℝ) : ℝ :=
  ∑ x, if Accepts μ q P τ (q x) then μ x else 0

open Classical in
/-- The weight of the accepted states with a target outside the returned class. -/
noncomputable def errorMass (μ : X → ℝ) (q : X → Q) (P : X → V) (τ : ℝ) : ℝ :=
  ∑ x, if Accepts μ q P τ (q x) ∧ P x ≠ topClass μ q P (q x) then μ x else 0

/-- Sum over states as a sum over records of sums over fibers. -/
theorem sum_fiberwise (q : X → Q) (g : X → ℝ) :
    ∑ x, g x = ∑ o, ∑ x, if q x = o then g x else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_ite_eq]
  simp

omit [Fintype Q] [Fintype V] [Nonempty V] in
/-- The fiber weight minus a class weight is the weight of the other classes. -/
theorem fiberWeight_sub_classWeight (μ : X → ℝ) (q : X → Q) (P : X → V) (o : Q) (v : V) :
    fiberWeight μ q o - classWeight μ q P o v = ∑ x, if q x = o ∧ P x ≠ v then μ x else 0 := by
  unfold fiberWeight classWeight
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hq : q x = o <;> by_cases hp : P x = v <;> simp [hq, hp]

open Classical in
/-- The error weight is the sum over accepted records of the fiber weight minus the top weight. -/
theorem errorMass_eq_fiberwise (μ : X → ℝ) (q : X → Q) (P : X → V) (τ : ℝ) :
    errorMass μ q P τ =
      ∑ o, if Accepts μ q P τ o then fiberWeight μ q o - topWeight μ q P o else 0 := by
  unfold errorMass
  rw [sum_fiberwise q]
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : Accepts μ q P τ o
  · rw [if_pos ho, ← classWeight_topClass μ q P o, fiberWeight_sub_classWeight]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hq : q x = o
    · subst hq
      simp [ho]
    · simp [hq]
  · rw [if_neg ho]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hq : q x = o
    · subst hq
      simp [ho]
    · simp [hq]

open Classical in
/-- The accepted weight is the sum of the fiber weights of the accepted records. -/
theorem acceptedMass_eq_fiberwise (μ : X → ℝ) (q : X → Q) (P : X → V) (τ : ℝ) :
    acceptedMass μ q P τ = ∑ o, if Accepts μ q P τ o then fiberWeight μ q o else 0 := by
  unfold acceptedMass
  rw [sum_fiberwise q]
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : Accepts μ q P τ o
  · rw [if_pos ho]
    unfold fiberWeight
    apply Finset.sum_congr rfl
    intro x _
    by_cases hq : q x = o
    · subst hq
      simp [ho]
    · simp [hq]
  · rw [if_neg ho]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hq : q x = o
    · subst hq
      simp [ho]
    · simp [hq]

/--
`prop:threshold-acceptance`, the error bound.

Proves: on the accepted records the threshold rule errs on at most `(1 - τ)` times the accepted
weight: the conditional error is at most `1 - τ`. No sign condition on `τ` or on the weights.
Scope: row 16-025. Trust: kernel-only, `Classical.choice`.
-/
theorem errorMass_le (μ : X → ℝ) (q : X → Q) (P : X → V) (τ : ℝ) :
    errorMass μ q P τ ≤ (1 - τ) * acceptedMass μ q P τ := by
  classical
  rw [errorMass_eq_fiberwise, acceptedMass_eq_fiberwise, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o _
  by_cases ho : Accepts μ q P τ o
  · rw [if_pos ho, if_pos ho]
    have h := ho
    rw [accepts_iff] at h
    linarith
  · rw [if_neg ho, if_neg ho, mul_zero]

omit [Fintype Q] in
/-- A larger threshold accepts fewer records, for nonnegative fiber weights. -/
theorem acceptedSet_antitone (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (q : X → Q) (P : X → V)
    {τ τ' : ℝ} (hle : τ ≤ τ') : acceptedSet μ q P τ' ⊆ acceptedSet μ q P τ := by
  intro x hx
  rw [mem_acceptedSet] at hx ⊢
  have hW : 0 ≤ fiberWeight μ q (q x) := by
    unfold fiberWeight
    exact Finset.sum_nonneg (fun y _ => by split_ifs <;> simp [hμ y])
  have := mul_le_mul_of_nonneg_right hle hW
  unfold Accepts at hx ⊢
  linarith

/-! ## The end `τ = 1` -/

omit [Fintype Q] [Fintype V] [Nonempty V] in
/-- With positive weights, the fiber weight is at most a class weight iff every state of the fiber
carries that class. -/
theorem fiberWeight_le_classWeight_iff (μ : X → ℝ) (hμ : ∀ x, 0 < μ x) (q : X → Q)
    (P : X → V) (o : Q) (v : V) :
    fiberWeight μ q o ≤ classWeight μ q P o v ↔ ∀ y, q y = o → P y = v := by
  have hsub := fiberWeight_sub_classWeight μ q P o v
  constructor
  · intro hle y hy
    by_contra hne
    have hpos : 0 < ∑ x, (if q x = o ∧ P x ≠ v then μ x else 0) := by
      apply Finset.sum_pos'
      · intro x _
        split_ifs
        · exact (hμ x).le
        · exact le_rfl
      · exact ⟨y, Finset.mem_univ y, by simp [hy, hne, hμ y]⟩
    linarith
  · intro hall
    have hzero : ∑ x, (if q x = o ∧ P x ≠ v then μ x else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      by_cases hq : q x = o
      · simp [hq, hall x hq]
      · simp [hq]
    linarith

omit [Fintype Q] in
/-- With positive weights, the rule accepts at `τ = 1` exactly the records with a fiber of one
target class. -/
theorem accepts_one_iff (μ : X → ℝ) (hμ : ∀ x, 0 < μ x) (q : X → Q) (P : X → V) (o : Q) :
    Accepts μ q P 1 o ↔ ∃ v, ∀ y, q y = o → P y = v := by
  rw [accepts_iff, one_mul]
  constructor
  · intro h
    refine ⟨topClass μ q P o, ?_⟩
    rw [← fiberWeight_le_classWeight_iff μ hμ q P o, classWeight_topClass]
    exact h
  · rintro ⟨v, hv⟩
    exact le_trans ((fiberWeight_le_classWeight_iff μ hμ q P o v).mpr hv)
      (classWeight_le_topWeight μ q P o v)

omit [Fintype Q] [Fintype V] in
/-- The fiber of `o` attains at most one target value iff some class contains every state of the
fiber. -/
theorem fiberVerdicts_card_le_one_iff (q : X → Q) (P : X → V) (o : Q) :
    (fiberVerdicts q P o).card ≤ 1 ↔ ∃ v, ∀ y, q y = o → P y = v := by
  rw [Finset.card_le_one]
  constructor
  · intro h
    by_cases hex : ∃ y, q y = o
    · obtain ⟨y0, hy0⟩ := hex
      refine ⟨P y0, fun y hy => ?_⟩
      apply h
      · exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨y0, Finset.mem_filter.mpr ⟨Finset.mem_univ y0, hy0⟩, rfl⟩
    · obtain ⟨v⟩ := ‹Nonempty V›
      exact ⟨v, fun y hy => absurd ⟨y, hy⟩ hex⟩
  · rintro ⟨v, hv⟩ a ha b hb
    obtain ⟨ya, hya, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨yb, hyb, rfl⟩ := Finset.mem_image.mp hb
    rw [hv ya (Finset.mem_filter.mp hya).2, hv yb (Finset.mem_filter.mp hyb).2]

omit [Fintype Q] in
/--
`prop:threshold-acceptance`, the end `τ = 1`.

Proves: with positive weights the accepted set at `τ = 1` is `observerAccepted q P 1`, the greatest
union of fibers on which one side symbol recovers the target (`S_1` of
`thm:observer-measurable-refusal`).
Scope: row 16-025, the Lean name the ledger asks for. Trust: kernel-only.
-/
theorem thresholdAcceptance_tau_one_eq_observerRetained (μ : X → ℝ) (hμ : ∀ x, 0 < μ x)
    (q : X → Q) (P : X → V) :
    acceptedSet μ q P 1 = observerAccepted q P 1 := by
  ext x
  rw [mem_acceptedSet, accepts_one_iff μ hμ q P (q x), ← fiberVerdicts_card_le_one_iff]
  simp [observerAccepted]

open Classical in
omit [Fintype Q] in
/--
Proves: with positive weights the weight the rule refuses at `τ = 1` is `R_1^obs`, the weight of
the states in fibers with more than one target value.
Scope: row 16-025, `eq:observer-measurable-refusal`. Trust: kernel-only.
-/
theorem thresholdAcceptance_tau_one_refusedMass (μ : X → ℝ) (hμ : ∀ x, 0 < μ x)
    (q : X → Q) (P : X → V) :
    refusedMass μ (acceptedSet μ q P 1) =
      ∑ x, if 1 < (fiberVerdicts q P (q x)).card then μ x else 0 := by
  classical
  rw [thresholdAcceptance_tau_one_eq_observerRetained μ hμ q P]
  exact observerAccepted_refusedMass_eq μ q P 1

/-! ## The end at the least top-class fraction -/

omit [Fintype Q] in
/-- With nonnegative weights, the best list of at most one target value at `o` keeps the top
weight. -/
theorem sup_boundedLists_one_eq_topWeight (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (q : X → Q)
    (P : X → V) (o : Q) :
    (boundedLists (V := V) 1).sup' ⟨∅, empty_mem_boundedLists 1⟩ (keptMass μ q P o) =
      topWeight μ q P o := by
  have hkept : ∀ v, keptMass μ q P o {v} = classWeight μ q P o v := by
    intro v
    unfold keptMass classWeight
    apply Finset.sum_congr rfl
    intro x _
    simp [Finset.mem_singleton]
  apply le_antisymm
  · apply Finset.sup'_le
    intro W hW
    have hcard : W.card ≤ 1 := (Finset.mem_filter.mp hW).2
    rcases Finset.card_le_one_iff_subset_singleton.mp hcard with ⟨v, hv⟩
    rcases Finset.subset_singleton_iff.mp hv with h0 | h1
    · subst h0
      have h0' : keptMass μ q P o ∅ = 0 := by
        unfold keptMass
        simp
      rw [h0']
      exact le_trans (by
        unfold classWeight
        exact Finset.sum_nonneg (fun y _ => by split_ifs <;> simp [hμ y]))
        (classWeight_le_topWeight μ q P o v)
    · subst h1
      rw [hkept]
      exact classWeight_le_topWeight μ q P o v
  · rw [← classWeight_topClass μ q P o, ← hkept]
    apply Finset.le_sup'
    simp [boundedLists]

/-- With nonnegative weights the one-try vulnerability is the sum of the top weights. -/
theorem kTryVulnerability_one_eq_sum_topWeight (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (q : X → Q)
    (P : X → V) : kTryVulnerability μ q P 1 = ∑ o, topWeight μ q P o := by
  unfold kTryVulnerability
  apply Finset.sum_congr rfl
  intro o _
  exact sup_boundedLists_one_eq_topWeight μ hμ q P o

/--
Proves: with nonnegative weights, a threshold that accepts every attained record gives the error
weight `repairFrontier μ q P 1`, the least refused weight `R_1` of a one-symbol repair, equal to the
total weight minus the sum of the top class weights.
Scope: `prop:threshold-acceptance`, the forced-decision end; row 16-025. Trust: kernel-only.
-/
theorem errorMass_eq_repairFrontier_of_all_accepted (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (q : X → Q) (P : X → V) (τ : ℝ) (hall : ∀ x, Accepts μ q P τ (q x)) :
    errorMass μ q P τ = repairFrontier μ q P 1 := by
  classical
  rw [repairFrontier_eq_sub_kTryVulnerability, kTryVulnerability_one_eq_sum_topWeight μ hμ,
    errorMass_eq_fiberwise]
  have hterm : ∀ o, (if Accepts μ q P τ o then fiberWeight μ q o - topWeight μ q P o else 0) =
      fiberWeight μ q o - topWeight μ q P o := by
    intro o
    by_cases hex : ∃ x, q x = o
    · obtain ⟨x, rfl⟩ := hex
      rw [if_pos (hall x)]
    · have hW : fiberWeight μ q o = 0 := by
        unfold fiberWeight
        apply Finset.sum_eq_zero
        intro x _
        rw [if_neg (fun h => hex ⟨x, h⟩)]
      have hC : ∀ v, classWeight μ q P o v = 0 := by
        intro v
        unfold classWeight
        apply Finset.sum_eq_zero
        intro x _
        rw [if_neg (fun h => hex ⟨x, h.1⟩)]
      have hT : topWeight μ q P o = 0 := by
        rw [← classWeight_topClass]
        exact hC _
      split_ifs <;> simp [hW, hT]
  rw [Finset.sum_congr rfl (fun o _ => hterm o), Finset.sum_sub_distrib]
  congr 1
  rw [sum_fiberwise q μ]
  rfl

/-- The least top-class fraction over the states. -/
noncomputable def leastTopFraction [Nonempty X] (μ : X → ℝ) (q : X → Q) (P : X → V) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun x => topWeight μ q P (q x) / fiberWeight μ q (q x))

omit [Fintype Q] in
/-- With positive weights the top weight of an attained record is positive and at most the fiber
weight. -/
theorem topWeight_pos_le (μ : X → ℝ) (hμ : ∀ x, 0 < μ x) (q : X → Q) (P : X → V) (x : X) :
    0 < topWeight μ q P (q x) ∧ topWeight μ q P (q x) ≤ fiberWeight μ q (q x) := by
  have hcls : μ x ≤ classWeight μ q P (q x) (P x) := by
    unfold classWeight
    have := Finset.single_le_sum (f := fun y => if q y = q x ∧ P y = P x then μ y else 0)
      (fun y _ => by dsimp only; split_ifs <;> simp [(hμ y).le]) (Finset.mem_univ x)
    simpa using this
  refine ⟨lt_of_lt_of_le (hμ x) (le_trans hcls (classWeight_le_topWeight μ q P (q x) (P x))), ?_⟩
  rw [← classWeight_topClass]
  have hsub := fiberWeight_sub_classWeight μ q P (q x) (topClass μ q P (q x))
  have hnn : 0 ≤ ∑ y, (if q y = q x ∧ P y ≠ topClass μ q P (q x) then μ y else 0) :=
    Finset.sum_nonneg (fun y _ => by split_ifs <;> simp [(hμ y).le])
  linarith

/--
`prop:threshold-acceptance`, the end at the least top-class fraction.

Proves: with positive weights on a nonempty state set the least top-class fraction lies in
`(0, 1]`, the rule accepts every record at that threshold, and its error weight there is
`repairFrontier μ q P 1`, the error `R_1` of the forced decision.
Scope: row 16-025. Trust: kernel-only.
-/
theorem leastTopFraction_errorMass_eq_repairFrontier [Nonempty X] (μ : X → ℝ)
    (hμ : ∀ x, 0 < μ x) (q : X → Q) (P : X → V) :
    0 < leastTopFraction μ q P ∧ leastTopFraction μ q P ≤ 1 ∧
      (∀ x, Accepts μ q P (leastTopFraction μ q P) (q x)) ∧
      errorMass μ q P (leastTopFraction μ q P) = repairFrontier μ q P 1 := by
  have hfrac : ∀ x, 0 < topWeight μ q P (q x) / fiberWeight μ q (q x) ∧
      topWeight μ q P (q x) / fiberWeight μ q (q x) ≤ 1 := by
    intro x
    obtain ⟨htop, hle⟩ := topWeight_pos_le μ hμ q P x
    have hW : 0 < fiberWeight μ q (q x) := lt_of_lt_of_le htop hle
    exact ⟨div_pos htop hW, (div_le_one hW).mpr hle⟩
  have hall : ∀ x, Accepts μ q P (leastTopFraction μ q P) (q x) := by
    intro x
    obtain ⟨htop, hle⟩ := topWeight_pos_le μ hμ q P x
    have hW : 0 < fiberWeight μ q (q x) := lt_of_lt_of_le htop hle
    have hmin : leastTopFraction μ q P ≤ topWeight μ q P (q x) / fiberWeight μ q (q x) :=
      Finset.inf'_le _ (Finset.mem_univ x)
    rw [accepts_iff]
    rw [le_div_iff₀ hW] at hmin
    exact hmin
  obtain ⟨x0⟩ := ‹Nonempty X›
  refine ⟨?_, ?_, hall,
    errorMass_eq_repairFrontier_of_all_accepted μ (fun x => (hμ x).le) q P _ hall⟩
  · obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := X))
      (fun x => topWeight μ q P (q x) / fiberWeight μ q (q x))
    unfold leastTopFraction
    rw [hx]
    exact (hfrac x).1
  · exact le_trans (Finset.inf'_le _ (Finset.mem_univ x0)) (hfrac x0).2

/-! ## Non-vacuity -/

/-- A fair pair with one record and the identity target: at `τ = 1` the accepted set is the empty
set `observerAccepted` of that pair. -/
example : acceptedSet (fun _ : Bool => (1 : ℝ) / 2) (fun _ => ()) id 1 =
    observerAccepted (fun _ : Bool => ()) id 1 :=
  thresholdAcceptance_tau_one_eq_observerRetained _ (fun _ => by norm_num) _ _

end OperatorKO7.Meta.BoundaryObserver.ThresholdAcceptance
