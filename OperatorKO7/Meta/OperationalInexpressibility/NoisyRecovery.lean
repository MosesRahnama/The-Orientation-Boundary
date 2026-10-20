import OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel

/-!
# Noisy recovery and exact Bayes risk

A finite rational prior and stochastic observation kernel determine their joint
law. The posterior is derived from that joint law whenever the observation has
positive mass. Zero-mass observations carry no posterior obligation.

The 0-1 Bayes decoder is synthesized by exhaustive finite maximization. The
same finite search is reused for side encoders. No efficiency claim is made.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery

open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel

universe u v w z

/-- Finite rational prior plus stochastic observation kernel. -/
structure RationalObservationModel (X : Type u) (O : Type v)
    [Fintype X] [Fintype O] where
  prior : X → ℚ
  kernel : X → O → ℚ
  prior_nonneg : ∀ x, 0 ≤ prior x
  prior_sum_one : ∑ x, prior x = 1
  kernel_nonneg : ∀ x o, 0 ≤ kernel x o
  kernel_sum_one : ∀ x, ∑ o, kernel x o = 1

variable {X : Type u} {O : Type v} {V : Type w}
variable [Fintype X] [Fintype O] [Fintype V]
variable [DecidableEq X] [DecidableEq O] [DecidableEq V]

/-- Joint mass of target value `v` and observation `o`. -/
def joint (M : RationalObservationModel X O) (P : X → V) (v : V) (o : O) : ℚ :=
  ∑ x, if P x = v then M.prior x * M.kernel x o else 0

/-- Marginal observation mass derived from the same prior and kernel. -/
def observationMass (M : RationalObservationModel X O) (o : O) : ℚ :=
  ∑ x, M.prior x * M.kernel x o

/-- Bayes posterior derived from the joint law. `none` means exactly a zero-mass
observation. -/
def posterior? (M : RationalObservationModel X O) (P : X → V) (o : O) :
    Option (V → ℚ) :=
  if observationMass M o = 0 then none
  else some fun v => joint M P v o / observationMass M o

omit [Fintype V] [DecidableEq X] [DecidableEq O] in
/-- Every joint cell has nonnegative mass. -/
theorem joint_nonneg
    (M : RationalObservationModel X O) (P : X → V) (v : V) (o : O) :
    0 ≤ joint M P v o := by
  unfold joint
  apply Finset.sum_nonneg
  intro x _
  split
  · exact mul_nonneg (M.prior_nonneg x) (M.kernel_nonneg x o)
  · exact le_rfl

omit [DecidableEq X] [DecidableEq O] in
/-- Joint masses sum to the observation marginal. -/
theorem sum_joint_eq_observationMass
    (M : RationalObservationModel X O) (P : X → V) (o : O) :
    ∑ v, joint M P v o = observationMass M o := by
  unfold joint observationMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

omit [DecidableEq X] [DecidableEq O] in
/-- Observation masses sum to one. -/
theorem sum_observationMass_eq_one (M : RationalObservationModel X O) :
    ∑ o, observationMass M o = 1 := by
  unfold observationMass
  rw [Finset.sum_comm]
  calc
    ∑ x, ∑ o, M.prior x * M.kernel x o
        = ∑ x, M.prior x * (∑ o, M.kernel x o) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
    _ = ∑ x, M.prior x := by simp [M.kernel_sum_one]
    _ = 1 := M.prior_sum_one

omit [DecidableEq X] [DecidableEq O] in
/-- A positive-mass observation receives a normalized posterior. -/
theorem posterior?_sum_one
    (M : RationalObservationModel X O) (P : X → V) (o : O)
    (ho : observationMass M o ≠ 0) :
    ∃ post, posterior? M P o = some post ∧ ∑ v, post v = 1 := by
  refine ⟨fun v => joint M P v o / observationMass M o, ?_, ?_⟩
  · simp [posterior?, ho]
  · calc
      ∑ v, joint M P v o / observationMass M o =
          (∑ v, joint M P v o) / observationMass M o := by
            rw [Finset.sum_div]
      _ = observationMass M o / observationMass M o := by
            rw [sum_joint_eq_observationMass]
      _ = 1 := div_self ho

omit [Fintype V] [DecidableEq X] [DecidableEq O] in
/-- Every derived positive-mass posterior cell is nonnegative. -/
theorem posterior?_nonneg
    (M : RationalObservationModel X O) (P : X → V) (o : O)
    {post : V → ℚ} (hpost : posterior? M P o = some post) :
    ∀ v, 0 ≤ post v := by
  intro v
  unfold posterior? at hpost
  split at hpost
  · simp at hpost
  · next hmass =>
      simp at hpost
      subst post
      have hobs : 0 ≤ observationMass M o := by
        unfold observationMass
        exact Finset.sum_nonneg fun x _ =>
          mul_nonneg (M.prior_nonneg x) (M.kernel_nonneg x o)
      exact div_nonneg (joint_nonneg M P v o) hobs

omit [DecidableEq X] [DecidableEq O] in
/-- One target/observation joint cell never exceeds the full observation mass. -/
theorem joint_le_observationMass
    (M : RationalObservationModel X O) (P : X → V) (v : V) (o : O) :
    joint M P v o ≤ observationMass M o := by
  rw [← sum_joint_eq_observationMass M P o]
  exact Finset.single_le_sum (fun w _ => joint_nonneg M P w o) (by simp)

omit [Fintype V] [DecidableEq X] [DecidableEq O] in
/-- Zero observation mass is the only reason the derived posterior is absent. -/
theorem posterior?_eq_none_iff
    (M : RationalObservationModel X O) (P : X → V) (o : O) :
    posterior? M P o = none ↔ observationMass M o = 0 := by
  simp [posterior?]

/-- Deterministic finite argmax. The supplied default is compared with every
listed candidate. -/
def argmaxBy {A : Type u} {B : Type v} [LinearOrder B]
    (score : A → B) (default : A) : List A → A
  | [] => default
  | a :: as =>
      let best := argmaxBy score default as
      if score best < score a then a else best

/-- Deterministic finite argmin. -/
def argminBy {A : Type u} {B : Type v} [LinearOrder B]
    (score : A → B) (default : A) : List A → A
  | [] => default
  | a :: as =>
      let best := argminBy score default as
      if score a < score best then a else best

/-- Optional finite argmin with an explicit empty-list result. -/
def argminBy? {A : Type u} {B : Type v} [LinearOrder B]
    (score : A → B) : List A → Option A
  | [] => none
  | a :: as => some (argminBy score a (a :: as))

/-- The finite argmax result belongs to the supplied default plus candidate list. -/
theorem argmaxBy_mem_default_cons {A : Type u} {B : Type v} [LinearOrder B]
    (score : A → B) (default : A) :
    ∀ xs : List A, argmaxBy score default xs ∈ default :: xs := by
  intro xs
  induction xs with
  | nil => simp [argmaxBy]
  | cons x xs ih =>
      simp only [argmaxBy]
      split
      · simp
      · have hb : argmaxBy score default xs ∈ default :: xs := ih
        simp only [List.mem_cons] at hb ⊢
        rcases hb with hbd | hb
        · exact Or.inl hbd
        · exact Or.inr (Or.inr hb)

/-- Every listed score is bounded by the finite argmax. -/
theorem le_argmaxBy_of_mem {A : Type u} {B : Type v} [LinearOrder B]
    (score : A → B) (default a : A) :
    ∀ {xs : List A}, a ∈ xs → score a ≤ score (argmaxBy score default xs) := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro ha
      simp only [List.mem_cons] at ha
      simp only [argmaxBy]
      let best := argmaxBy score default xs
      split
      · next hlt =>
          rcases ha with rfl | ha
          · exact le_rfl
          · exact (ih ha).trans (le_of_lt hlt)
      · next hnlt =>
          rcases ha with rfl | ha
          · exact le_of_not_gt hnlt
          · exact ih ha

/-- The finite argmin result belongs to the supplied default plus candidate list. -/
theorem argminBy_mem_default_cons {A : Type u} {B : Type v} [LinearOrder B]
    (score : A → B) (default : A) :
    ∀ xs : List A, argminBy score default xs ∈ default :: xs := by
  intro xs
  induction xs with
  | nil => simp [argminBy]
  | cons x xs ih =>
      simp only [argminBy]
      split
      · simp
      · have hb : argminBy score default xs ∈ default :: xs := ih
        simp only [List.mem_cons] at hb ⊢
        rcases hb with hbd | hb
        · exact Or.inl hbd
        · exact Or.inr (Or.inr hb)

/-- Every listed score is above the finite argmin. -/
theorem argminBy_le_of_mem {A : Type u} {B : Type v} [LinearOrder B]
    (score : A → B) (default a : A) :
    ∀ {xs : List A}, a ∈ xs → score (argminBy score default xs) ≤ score a := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro ha
      simp only [List.mem_cons] at ha
      simp only [argminBy]
      let best := argminBy score default xs
      split
      · next hlt =>
          rcases ha with rfl | ha
          · exact le_rfl
          · exact le_trans (le_of_lt hlt) (ih ha)
      · next hnlt =>
          rcases ha with rfl | ha
          · exact le_of_not_gt hnlt
          · exact ih ha

/-- Optional argmax, with `none` only for an empty candidate list. -/
def argmaxBy? {A : Type u} {B : Type v} [LinearOrder B]
    (score : A → B) : List A → Option A
  | [] => none
  | a :: as => some (argmaxBy score a (a :: as))

@[simp] theorem argmaxBy?_eq_none_iff {A : Type u} {B : Type v} [LinearOrder B]
    (score : A → B) (xs : List A) :
    argmaxBy? score xs = none ↔ xs = [] := by
  cases xs <;> simp [argmaxBy?]

@[simp] theorem argminBy?_eq_none_iff {A : Type u} {B : Type v} [LinearOrder B]
    (score : A → B) (xs : List A) :
    argminBy? score xs = none ↔ xs = [] := by
  cases xs <;> simp [argminBy?]

/-- A successful optional argmax belongs to the supplied list and dominates it. -/
theorem argmaxBy?_maximal {A : Type u} {B : Type v} [LinearOrder B]
    (score : A → B) {xs : List A} {a : A}
    (h : argmaxBy? score xs = some a) :
    a ∈ xs ∧ ∀ b ∈ xs, score b ≤ score a := by
  cases xs with
  | nil => simp [argmaxBy?] at h
  | cons d ds =>
      simp [argmaxBy?] at h
      subst a
      refine ⟨?_, ?_⟩
      · simpa using argmaxBy_mem_default_cons score d (d :: ds)
      · intro b hb
        exact le_argmaxBy_of_mem score d b hb

omit [Fintype V] [DecidableEq X] [DecidableEq O] in
/-- The target enumeration is nonempty whenever a normalized source prior and a
total target map exist. This derives the decoding default from the finite input
model instead of assuming an unrelated `Inhabited V`. -/
theorem targetEnumeration_nonempty
    (EV : Enumeration V) (M : RationalObservationModel X O) (P : X → V) :
    EV.items ≠ [] := by
  intro hempty
  have hV : IsEmpty V := ⟨fun v => by
    have hv := EV.complete v
    simp [hempty] at hv⟩
  have hX : IsEmpty X := ⟨fun x => hV.false (P x)⟩
  letI : IsEmpty X := hX
  have hzero : (∑ x, M.prior x) = 0 := by simp
  rw [M.prior_sum_one] at hzero
  norm_num at hzero

/-- Deterministic maximum over a complete target enumeration. The impossible
empty branch is discharged from the normalized model itself. -/
def maxTarget (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) (score : V → ℚ) : V :=
  match h : argmaxBy? score EV.items with
  | some v => v
  | none => False.elim ((targetEnumeration_nonempty EV M P)
      ((argmaxBy?_eq_none_iff score EV.items).1 h))

/-- Bayes target at one observation. Enumeration order only breaks ties. -/
def bayesTarget (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) (o : O) : V :=
  maxTarget EV M P (fun v => joint M P v o)

omit [Fintype V] [DecidableEq X] [DecidableEq O] in
/-- Every target cell mass is bounded by the selected Bayes cell. -/
theorem joint_le_bayesTarget
    (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) (o : O) (v : V) :
    joint M P v o ≤ joint M P (bayesTarget EV M P o) o := by
  unfold bayesTarget maxTarget
  split
  · next best hbest =>
      exact (argmaxBy?_maximal (fun v => joint M P v o) hbest).2 v (EV.complete v)
  · next hnone =>
      exact False.elim ((targetEnumeration_nonempty EV M P)
        ((argmaxBy?_eq_none_iff (fun v => joint M P v o) EV.items).1 hnone))

/-- Correct classification mass of a deterministic decoder. -/
def correctMass (M : RationalObservationModel X O) (P : X → V) (d : O → V) : ℚ :=
  ∑ o, joint M P (d o) o

/-- 0-1 classification risk. -/
def risk (M : RationalObservationModel X O) (P : X → V) (d : O → V) : ℚ :=
  1 - correctMass M P d

/-- Executable Bayes decoder. -/
def bayesDecoder (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) : O → V := bayesTarget EV M P

/-- Exact minimum Bayes risk. -/
def bayesRisk (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) : ℚ := risk M P (bayesDecoder EV M P)

omit [Fintype V] [DecidableEq X] [DecidableEq O] in
/-- Closed form `1 - sum_o max_v J(v,o)`, with the maximum represented by the
executable Bayes target. -/
theorem bayesRisk_eq_one_sub_sum_max
    (EV : Enumeration V) (M : RationalObservationModel X O) (P : X → V) :
    bayesRisk EV M P = 1 - ∑ o, joint M P (bayesTarget EV M P o) o := rfl

omit [DecidableEq X] [DecidableEq O] in
/-- Bayes risk is nonnegative. -/
theorem bayesRisk_nonneg
    (EV : Enumeration V) (M : RationalObservationModel X O) (P : X → V) :
    0 ≤ bayesRisk EV M P := by
  unfold bayesRisk risk correctMass bayesDecoder
  apply sub_nonneg.mpr
  calc
    ∑ o, joint M P (bayesTarget EV M P o) o
        ≤ ∑ o, observationMass M o := by
          apply Finset.sum_le_sum
          intro o _
          exact joint_le_observationMass M P _ o
    _ = 1 := sum_observationMass_eq_one M

omit [Fintype V] [DecidableEq X] [DecidableEq O] in
/-- Bayes risk is at most one. -/
theorem bayesRisk_le_one
    (EV : Enumeration V) (M : RationalObservationModel X O) (P : X → V) :
    bayesRisk EV M P ≤ 1 := by
  unfold bayesRisk risk correctMass bayesDecoder
  have hnonneg : 0 ≤ ∑ o, joint M P (bayesTarget EV M P o) o :=
    Finset.sum_nonneg fun o _ => joint_nonneg M P _ o
  linarith

omit [DecidableEq X] [DecidableEq O] in
/-- Exact normalized Bayes-risk interval. -/
theorem bayesRisk_mem_unitInterval
    (EV : Enumeration V) (M : RationalObservationModel X O) (P : X → V) :
    0 ≤ bayesRisk EV M P ∧ bayesRisk EV M P ≤ 1 :=
  ⟨bayesRisk_nonneg EV M P, bayesRisk_le_one EV M P⟩

omit [Fintype V] [DecidableEq X] [DecidableEq O] in
/-- No deterministic decoder has lower 0-1 risk. -/
theorem bayesRisk_le_risk
    (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) (d : O → V) :
    bayesRisk EV M P ≤ risk M P d := by
  unfold bayesRisk risk correctMass bayesDecoder
  apply sub_le_sub_left
  apply Finset.sum_le_sum
  intro o _
  exact joint_le_bayesTarget EV M P o (d o)

/-- Randomized decoder with finite rational row distributions. -/
structure RandomDecoder (O : Type v) (V : Type w) [Fintype V] where
  weight : O → V → ℚ
  nonneg : ∀ o v, 0 ≤ weight o v
  sum_one : ∀ o, ∑ v, weight o v = 1

/-- Correct mass of a randomized decoder. -/
def randomizedCorrectMass (M : RationalObservationModel X O) (P : X → V)
    (D : RandomDecoder O V) : ℚ :=
  ∑ o, ∑ v, D.weight o v * joint M P v o

/-- Randomized 0-1 risk. -/
def randomizedRisk (M : RationalObservationModel X O) (P : X → V)
    (D : RandomDecoder O V) : ℚ := 1 - randomizedCorrectMass M P D

omit [DecidableEq X] [DecidableEq O] in
/-- Randomization cannot improve the Bayes optimum. -/
theorem bayesRisk_le_randomizedRisk
    (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) (D : RandomDecoder O V) :
    bayesRisk EV M P ≤ randomizedRisk M P D := by
  unfold bayesRisk risk correctMass bayesDecoder randomizedRisk randomizedCorrectMass
  apply sub_le_sub_left
  apply Finset.sum_le_sum
  intro o _
  calc
    ∑ v, D.weight o v * joint M P v o
        ≤ ∑ v, D.weight o v * joint M P (bayesTarget EV M P o) o := by
          apply Finset.sum_le_sum
          intro v _
          exact mul_le_mul_of_nonneg_left
            (joint_le_bayesTarget EV M P o v) (D.nonneg o v)
    _ = joint M P (bayesTarget EV M P o) o := by
      rw [← Finset.sum_mul, D.sum_one, one_mul]

/-- Support-relative exact recovery: all target mass outside the selected
Bayes target is zero. Zero-probability cells impose no equality. -/
def TargetPureOnSupport (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) : Prop :=
  ∀ o v, v ≠ bayesTarget EV M P o → joint M P v o = 0

/-- Gap between one observation's total mass and its best target mass. -/
def cellErrorMass (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) (o : O) : ℚ :=
  observationMass M o - joint M P (bayesTarget EV M P o) o

omit [DecidableEq X] [DecidableEq O] in
/-- Every cell error is nonnegative. -/
theorem cellErrorMass_nonneg
    (EV : Enumeration V) (M : RationalObservationModel X O) (P : X → V) (o : O) :
    0 ≤ cellErrorMass EV M P o := by
  unfold cellErrorMass
  rw [← sum_joint_eq_observationMass M P o]
  apply sub_nonneg.mpr
  exact Finset.single_le_sum (fun v _ => joint_nonneg M P v o) (by simp)

omit [Fintype V] [DecidableEq X] [DecidableEq O] in
/-- Bayes risk is the sum of the per-observation error masses. -/
theorem bayesRisk_eq_sum_cellErrorMass
    (EV : Enumeration V) (M : RationalObservationModel X O) (P : X → V) :
    bayesRisk EV M P = ∑ o, cellErrorMass EV M P o := by
  rw [bayesRisk_eq_one_sub_sum_max, ← sum_observationMass_eq_one M]
  simp [cellErrorMass, Finset.sum_sub_distrib]

omit [DecidableEq X] [DecidableEq O] in
/-- Zero Bayes error is equivalent to one target carrying all positive mass in
each observation cell. -/
theorem bayesRisk_eq_zero_iff_targetPure
    (EV : Enumeration V) (M : RationalObservationModel X O) (P : X → V) :
    bayesRisk EV M P = 0 ↔ TargetPureOnSupport EV M P := by
  rw [bayesRisk_eq_sum_cellErrorMass]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun o _ => cellErrorMass_nonneg EV M P o)]
  constructor
  · intro h o v hv
    have hcell := h o (by simp)
    unfold cellErrorMass at hcell
    rw [← sum_joint_eq_observationMass M P o] at hcell
    have hsumErase : ∑ u ∈ (Finset.univ.erase (bayesTarget EV M P o)), joint M P u o = 0 := by
      rw [← Finset.sum_erase_add _ _ (by simp)] at hcell
      linarith
    have hvMem : v ∈ (Finset.univ.erase (bayesTarget EV M P o)) := by simp [hv]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun u hu => joint_nonneg M P u o)).1 hsumErase v hvMem
    exact hz
  · intro h o ho
    unfold cellErrorMass
    rw [← sum_joint_eq_observationMass M P o,
      ← Finset.sum_erase_add _ _ (by simp)]
    have hzero : ∑ u ∈ (Finset.univ.erase (bayesTarget EV M P o)), joint M P u o = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      exact h o u (by simpa using (Finset.mem_erase.mp hu).1)
    rw [hzero]
    ring

/-- Exact target constancy on positive joint-mass observation cells. -/
def LicensedOnJointSupport (M : RationalObservationModel X O) (P : X → V) : Prop :=
  ∀ o v w, 0 < joint M P v o → 0 < joint M P w o → v = w

omit [Fintype V] [DecidableEq X] [DecidableEq O] in
/-- The Bayes-cell formulation is exactly support licensing. -/
theorem targetPure_iff_licensedOnJointSupport
    (EV : Enumeration V) (M : RationalObservationModel X O) (P : X → V) :
    TargetPureOnSupport EV M P ↔ LicensedOnJointSupport M P := by
  constructor
  · intro hpure o v w hv hw
    have hvb : v = bayesTarget EV M P o := by
      by_contra hne
      have hz := hpure o v hne
      linarith
    have hwb : w = bayesTarget EV M P o := by
      by_contra hne
      have hz := hpure o w hne
      linarith
    exact hvb.trans hwb.symm
  · intro hlic o v hne
    by_contra hnz
    have hv : 0 < joint M P v o :=
      lt_of_le_of_ne (joint_nonneg M P v o) (Ne.symm hnz)
    have hb : 0 < joint M P (bayesTarget EV M P o) o :=
      hv.trans_le (joint_le_bayesTarget EV M P o v)
    exact hne (hlic o v (bayesTarget EV M P o) hv hb)

omit [DecidableEq X] [DecidableEq O] in
/-- Zero Bayes error is exactly licensing on positive joint support. -/
theorem bayesRisk_eq_zero_iff_licensedOnJointSupport
    (EV : Enumeration V) (M : RationalObservationModel X O) (P : X → V) :
    bayesRisk EV M P = 0 ↔ LicensedOnJointSupport M P := by
  rw [bayesRisk_eq_zero_iff_targetPure,
    targetPure_iff_licensedOnJointSupport]

/-- Exact licensing on the full carrier is stronger than support-relative
recovery because a prior may assign zero mass to a collision. -/
def FullCarrierDeterministic (q : X → O) (P : X → V) : Prop :=
  ∀ x y, q x = q y → P x = P y

/-- A deterministic observation kernel induced by a map. -/
def deterministicModel (prior : X → ℚ)
    (hprior0 : ∀ x, 0 ≤ prior x) (hprior1 : ∑ x, prior x = 1)
    (q : X → O) : RationalObservationModel X O where
  prior := prior
  kernel := fun x o => if q x = o then 1 else 0
  prior_nonneg := hprior0
  prior_sum_one := hprior1
  kernel_nonneg := by intro x o; split <;> norm_num
  kernel_sum_one := by intro x; simp

omit [Fintype V] [DecidableEq X] in
/-- Positive joint mass for a deterministic observation is equivalent to an
input with positive prior mass, matching target, and matching observation. -/
theorem deterministic_joint_pos_iff
    (prior : X → ℚ) (hprior0 : ∀ x, 0 ≤ prior x)
    (hprior1 : ∑ x, prior x = 1) (q : X → O) (P : X → V)
    (v : V) (o : O) :
    0 < joint (deterministicModel prior hprior0 hprior1 q) P v o ↔
      ∃ x, 0 < prior x ∧ P x = v ∧ q x = o := by
  unfold joint deterministicModel
  constructor
  · intro hsum
    have hnonneg : ∀ x ∈ (Finset.univ : Finset X),
        0 ≤ (if P x = v then prior x * (if q x = o then 1 else 0) else 0) := by
      intro x _
      split
      · split <;> simp [hprior0 x]
      · exact le_rfl
    rcases (Finset.sum_pos_iff_of_nonneg hnonneg).1 hsum with ⟨x, _, hx⟩
    by_cases hp : P x = v
    · by_cases hq : q x = o
      · simp [hp, hq] at hx
        exact ⟨x, hx, hp, hq⟩
      · simp [hp, hq] at hx
    · simp [hp] at hx
  · rintro ⟨x, hx, hp, hq⟩
    have hterm :
        0 < (if P x = v then prior x * (if q x = o then 1 else 0) else 0) := by
      simp [hp, hq, hx]
    have hnonneg : ∀ y ∈ (Finset.univ : Finset X),
        0 ≤ (if P y = v then prior y * (if q y = o then 1 else 0) else 0) := by
      intro y _
      split
      · split <;> simp [hprior0 y]
      · exact le_rfl
    have hle' := Finset.single_le_sum hnonneg (show x ∈ (Finset.univ : Finset X) by simp)
    have hle :
        (if P x = v then prior x * (if q x = o then 1 else 0) else 0) ≤
          ∑ y, (if P y = v then prior y * (if q y = o then 1 else 0) else 0) := by
      simpa using hle'
    exact hterm.trans_le hle

omit [Fintype V] [DecidableEq X] in
/-- With a positive prior on every input, support licensing for a deterministic
observer is equivalent to full-carrier licensing. -/
theorem deterministic_fullSupport_licensed_iff_fullCarrier
    (prior : X → ℚ) (hprior0 : ∀ x, 0 ≤ prior x)
    (hprior1 : ∑ x, prior x = 1) (hpriorPos : ∀ x, 0 < prior x)
    (q : X → O) (P : X → V) :
    LicensedOnJointSupport (deterministicModel prior hprior0 hprior1 q) P ↔
      FullCarrierDeterministic q P := by
  constructor
  · intro hlic x y hq
    have hx : 0 < joint (deterministicModel prior hprior0 hprior1 q) P (P x) (q x) :=
      (deterministic_joint_pos_iff prior hprior0 hprior1 q P (P x) (q x)).2
        ⟨x, hpriorPos x, rfl, rfl⟩
    have hy : 0 < joint (deterministicModel prior hprior0 hprior1 q) P (P y) (q x) :=
      (deterministic_joint_pos_iff prior hprior0 hprior1 q P (P y) (q x)).2
        ⟨y, hpriorPos y, rfl, hq.symm⟩
    exact hlic (q x) (P x) (P y) hx hy
  · intro hfull o v w hv hw
    rcases (deterministic_joint_pos_iff prior hprior0 hprior1 q P v o).1 hv with
      ⟨x, _, hxP, hxq⟩
    rcases (deterministic_joint_pos_iff prior hprior0 hprior1 q P w o).1 hw with
      ⟨y, _, hyP, hyq⟩
    exact hxP.symm.trans ((hfull x y (hxq.trans hyq.symm)).trans hyP)

/-- Canonical explicit target enumeration for the binary fixtures below. -/
def binaryTargetEnumeration : Enumeration (Fin 2) where
  items := [0, 1]
  nodup := by decide
  complete := by intro x; fin_cases x <;> decide

/-- Support-relative zero risk can coexist with a full-carrier collision. -/
def zeroMassCollisionModel : RationalObservationModel (Fin 2) Unit :=
  deterministicModel
    (fun x : Fin 2 => if x = 0 then 1 else 0)
    (by intro x; fin_cases x <;> norm_num)
    (by norm_num [Fin.sum_univ_two])
    (fun _ => ())

/-- The zero-mass second point is invisible to Bayes risk. -/
theorem zeroMassCollision_support_pure :
    bayesRisk binaryTargetEnumeration zeroMassCollisionModel (fun x => x) = 0 := by
  rw [bayesRisk_eq_zero_iff_licensedOnJointSupport]
  intro o v w hv hw
  have hv' : 0 < joint
      (deterministicModel
        (fun x : Fin 2 => if x = 0 then 1 else 0)
        (by intro x; fin_cases x <;> norm_num)
        (by norm_num [Fin.sum_univ_two])
        (fun _ : Fin 2 => ())) (fun x => x) v o := by
    simpa [zeroMassCollisionModel] using hv
  have hw' : 0 < joint
      (deterministicModel
        (fun x : Fin 2 => if x = 0 then 1 else 0)
        (by intro x; fin_cases x <;> norm_num)
        (by norm_num [Fin.sum_univ_two])
        (fun _ : Fin 2 => ())) (fun x => x) w o := by
    simpa [zeroMassCollisionModel] using hw
  rcases (deterministic_joint_pos_iff
      (fun x : Fin 2 => if x = 0 then 1 else 0)
      (by intro x; fin_cases x <;> norm_num)
      (by norm_num [Fin.sum_univ_two])
      (fun _ : Fin 2 => ()) (fun x => x) v o).1 hv' with ⟨x, hx, hxv, _⟩
  rcases (deterministic_joint_pos_iff
      (fun x : Fin 2 => if x = 0 then 1 else 0)
      (by intro x; fin_cases x <;> norm_num)
      (by norm_num [Fin.sum_univ_two])
      (fun _ : Fin 2 => ()) (fun x => x) w o).1 hw' with ⟨y, hy, hyw, _⟩
  have hx0 : x = 0 := by
    fin_cases x <;> norm_num at hx ⊢
  have hy0 : y = 0 := by
    fin_cases y <;> norm_num at hy ⊢
  calc
    v = x := hxv.symm
    _ = 0 := hx0
    _ = y := hy0.symm
    _ = w := hyw

/-- The same fixture is not licensed on the whole carrier. -/
theorem zeroMassCollision_not_fullCarrier :
    ¬ FullCarrierDeterministic (fun _ : Fin 2 => ()) (fun x => x) := by
  intro h
  have := h 0 1 rfl
  norm_num at this

/-! ## Deterministic post-processing -/

variable {O₂ : Type z} [Fintype O₂] [DecidableEq O₂]

/-- Joint law after deterministic post-processing of the observation. -/
def postJoint (M : RationalObservationModel X O) (P : X → V)
    (g : O → O₂) (v : V) (o₂ : O₂) : ℚ :=
  ∑ o, if g o = o₂ then joint M P v o else 0

/-- Bayes target after post-processing. -/
def postBayesTarget (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) (g : O → O₂) (o₂ : O₂) : V :=
  maxTarget EV M P (fun v => postJoint M P g v o₂)

/-- Minimum error available to a decoder that sees only `g o`. -/
def postProcessedRisk (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) (g : O → O₂) : ℚ :=
  1 - ∑ o₂, postJoint M P g (postBayesTarget EV M P g o₂) o₂

omit [Fintype V] [DecidableEq X] [DecidableEq O] in
/-- The post-processed optimum is the original risk of the composed decoder. -/
theorem postProcessedRisk_eq_composed_risk
    (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) (g : O → O₂) :
    postProcessedRisk EV M P g =
      risk M P (fun o => postBayesTarget EV M P g (g o)) := by
  unfold postProcessedRisk risk correctMass postJoint
  rw [Finset.sum_comm]
  apply congrArg (fun q : ℚ => 1 - q)
  apply Finset.sum_congr rfl
  intro o _
  simp

omit [Fintype V] [DecidableEq X] [DecidableEq O] in
/-- Deterministic post-processing cannot reduce the minimum 0-1 Bayes error. -/
theorem bayesRisk_le_postProcessedRisk
    (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) (g : O → O₂) :
    bayesRisk EV M P ≤ postProcessedRisk EV M P g := by
  rw [postProcessedRisk_eq_composed_risk]
  exact bayesRisk_le_risk EV M P _

/-- Finite rational randomized processing of observations. -/
structure RationalPostProcessing (O : Type v) (O₂ : Type z) [Fintype O₂] where
  kernel : O → O₂ → ℚ
  nonneg : ∀ o o₂, 0 ≤ kernel o o₂
  sum_one : ∀ o, ∑ o₂, kernel o o₂ = 1

/-- Joint target/output mass after randomized observation processing. -/
def randomizedPostJoint
    (M : RationalObservationModel X O) (P : X → V)
    (G : RationalPostProcessing O O₂) (v : V) (o₂ : O₂) : ℚ :=
  ∑ o, G.kernel o o₂ * joint M P v o

/-- Bayes target after randomized processing. -/
def randomizedPostBayesTarget
    (EV : Enumeration V) (M : RationalObservationModel X O) (P : X → V)
    (G : RationalPostProcessing O O₂) (o₂ : O₂) : V :=
  maxTarget EV M P (fun v => randomizedPostJoint M P G v o₂)

/-- Minimum 0-1 risk after randomized processing. -/
def randomizedPostProcessedRisk
    (EV : Enumeration V) (M : RationalObservationModel X O) (P : X → V)
    (G : RationalPostProcessing O O₂) : ℚ :=
  1 - ∑ o₂, randomizedPostJoint M P G
    (randomizedPostBayesTarget EV M P G o₂) o₂

omit [Fintype V] [DecidableEq X] [DecidableEq O] [DecidableEq O₂] in
/-- One processed decision cell is bounded by the weighted original Bayes
cells. -/
theorem randomizedPostJoint_bayes_le
    (EV : Enumeration V) (M : RationalObservationModel X O) (P : X → V)
    (G : RationalPostProcessing O O₂) (o₂ : O₂) :
    randomizedPostJoint M P G (randomizedPostBayesTarget EV M P G o₂) o₂ ≤
      ∑ o, G.kernel o o₂ * joint M P (bayesTarget EV M P o) o := by
  unfold randomizedPostJoint
  apply Finset.sum_le_sum
  intro o _
  exact mul_le_mul_of_nonneg_left
    (joint_le_bayesTarget EV M P o (randomizedPostBayesTarget EV M P G o₂))
    (G.nonneg o o₂)

omit [Fintype V] [DecidableEq X] [DecidableEq O] [DecidableEq O₂] in
/-- Randomized post-processing obeys the 0-1 Bayes data-processing inequality:
processing the observation cannot lower the minimum error. -/
theorem bayesRisk_le_randomizedPostProcessedRisk
    (EV : Enumeration V) (M : RationalObservationModel X O) (P : X → V)
    (G : RationalPostProcessing O O₂) :
    bayesRisk EV M P ≤ randomizedPostProcessedRisk EV M P G := by
  rw [bayesRisk_eq_one_sub_sum_max]
  unfold randomizedPostProcessedRisk
  apply sub_le_sub_left
  calc
    ∑ o₂, randomizedPostJoint M P G
        (randomizedPostBayesTarget EV M P G o₂) o₂
        ≤ ∑ o₂, ∑ o, G.kernel o o₂ * joint M P (bayesTarget EV M P o) o := by
          apply Finset.sum_le_sum
          intro o₂ _
          exact randomizedPostJoint_bayes_le EV M P G o₂
    _ = ∑ o, ∑ o₂, G.kernel o o₂ * joint M P (bayesTarget EV M P o) o :=
      Finset.sum_comm
    _ = ∑ o, joint M P (bayesTarget EV M P o) o := by
      apply Finset.sum_congr rfl
      intro o _
      rw [← Finset.sum_mul, G.sum_one, one_mul]

/-! ## Finite exhaustive side-encoder search -/

variable {C : Type z} [Fintype C] [DecidableEq C]

/-- A successful optional argmin minimizes the score over the supplied list. -/
theorem argminBy?_minimal {A : Type u} {B : Type v} [LinearOrder B]
    (score : A → B) {xs : List A} {a : A}
    (h : argminBy? score xs = some a) :
    a ∈ xs ∧ ∀ b ∈ xs, score a ≤ score b := by
  cases xs with
  | nil => simp [argminBy?] at h
  | cons d ds =>
      simp [argminBy?] at h
      subst a
      refine ⟨?_, ?_⟩
      · simpa using argminBy_mem_default_cons score d (d :: ds)
      · intro b hb
        exact argminBy_le_of_mem score d b hb

/-- Joint law after adding a deterministic side encoder to the noisy
observation. -/
def sideJoint (M : RationalObservationModel X O) (P : X → V) (s : X → C)
    (v : V) (oc : O × C) : ℚ :=
  ∑ x, if P x = v ∧ s x = oc.2 then M.prior x * M.kernel x oc.1 else 0

/-- Best target for one combined observation under a fixed side encoder. -/
def sideBayesTarget (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) (s : X → C) (oc : O × C) : V :=
  maxTarget EV M P (fun v => sideJoint M P s v oc)

/-- Exact side-encoder Bayes risk. -/
def sideRisk (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) (s : X → C) : ℚ :=
  1 - ∑ oc : O × C, sideJoint M P s (sideBayesTarget EV M P s oc) oc

/-- All output tables of the requested length, generated from an explicit
output alphabet list. -/
def tableLists (alphabet : List C) : Nat → List (List C)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun c =>
      (tableLists alphabet n).map fun tail => c :: tail

omit [Fintype C] [DecidableEq C] in
/-- Every generated table has the requested length. -/
theorem tableLists_length {alphabet : List C} :
    ∀ {n : Nat} {xs : List C}, xs ∈ tableLists alphabet n → xs.length = n := by
  intro n
  induction n with
  | zero => intro xs h; simpa [tableLists] using h
  | succ n ih =>
      intro xs h
      simp only [tableLists, List.mem_flatMap, List.mem_map] at h
      rcases h with ⟨c, _, tail, htail, rfl⟩
      simp [ih htail]

omit [Fintype X] [Fintype C] in
/-- The table obtained by evaluating any function on the explicit input list is
present in the exhaustive table enumeration. -/
theorem mapped_function_table_mem
    (EX : Enumeration X) (EC : Enumeration C) (s : X → C) :
    EX.items.map s ∈ tableLists EC.items EX.items.length := by
  induction EX.items with
  | nil => simp [tableLists]
  | cons x xs ih =>
      simp only [List.map_cons, List.length_cons, tableLists, List.mem_flatMap,
        List.mem_map]
      refine ⟨s x, EC.complete (s x), xs.map s, ?_, rfl⟩
      exact ih

/-- Convert a complete value table into the corresponding total side encoder. -/
def encoderOfTable (EX : Enumeration X) (values : List C)
    (hlen : values.length = EX.items.length) : X → C := fun x =>
  values.get ⟨EX.items.idxOf x, by
    rw [hlen]
    exact List.idxOf_lt_length_iff.2 (EX.complete x)⟩

omit [Fintype X] [Fintype C] [DecidableEq C] in
/-- Reading the table generated by a function returns that function. -/
theorem encoderOfMappedFunction_eq
    (EX : Enumeration X) (s : X → C) :
    encoderOfTable EX (EX.items.map s) (by simp) = s := by
  funext x
  simp [encoderOfTable, List.getElem_map, List.getElem_idxOf]

/-- All deterministic side encoders generated from explicit input/output
enumerations. This is executable and does not enumerate a `Finset` of functions. -/
def sideEncoderCandidates (EX : Enumeration X) (EC : Enumeration C) : List (X → C) :=
  (tableLists EC.items EX.items.length).attach.map fun entry =>
    encoderOfTable EX entry.1 (tableLists_length entry.2)

omit [Fintype X] [Fintype C] in
/-- The explicit table enumeration covers every deterministic encoder. -/
theorem sideEncoderCandidates_complete
    (EX : Enumeration X) (EC : Enumeration C) (s : X → C) :
    s ∈ sideEncoderCandidates EX EC := by
  let values := EX.items.map s
  have hmem : values ∈ tableLists EC.items EX.items.length :=
    mapped_function_table_mem EX EC s
  have hatt : (⟨values, hmem⟩ : {x // x ∈ tableLists EC.items EX.items.length}) ∈
      (tableLists EC.items EX.items.length).attach := by simp
  have hmap := List.mem_map_of_mem
    (f := fun entry : {x // x ∈ tableLists EC.items EX.items.length} =>
      encoderOfTable EX entry.1 (tableLists_length entry.2)) hatt
  simpa [sideEncoderCandidates, values, encoderOfMappedFunction_eq] using hmap

/-- Exhaustive finite optimum over every deterministic side encoder `X → C`,
computed from explicit enumerations of both finite carriers. -/
def bestSideEncoder? (EX : Enumeration X) (EC : Enumeration C)
    (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) : Option (X → C) :=
  argminBy? (sideRisk EV M P) (sideEncoderCandidates EX EC)

omit [Fintype V] [DecidableEq O] in
/-- Every returned side encoder attains the minimum over the entire finite
function space. -/
theorem bestSideEncoder?_minimal
    (EX : Enumeration X) (EC : Enumeration C)
    (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) {best : X → C}
    (h : bestSideEncoder? EX EC EV M P = some best) :
    ∀ s : X → C, sideRisk EV M P best ≤ sideRisk EV M P s := by
  have hmin := (argminBy?_minimal (sideRisk EV M P) h).2
  intro s
  exact hmin s (sideEncoderCandidates_complete EX EC s)

omit [Fintype V] [DecidableEq O] in
/-- Search returns `none` exactly when there is no deterministic encoder. This
includes nonempty input with empty output alphabet, while the empty input has
its unique empty function. -/
theorem bestSideEncoder?_eq_none_iff
    (EX : Enumeration X) (EC : Enumeration C)
    (EV : Enumeration V) (M : RationalObservationModel X O) (P : X → V) :
    bestSideEncoder? EX EC EV M P = none ↔ IsEmpty (X → C) := by
  rw [bestSideEncoder?, argminBy?_eq_none_iff]
  constructor
  · intro hempty
    exact ⟨fun s => by
      have hs := sideEncoderCandidates_complete EX EC s
      rw [hempty] at hs
      simp at hs⟩
  · intro hEmpty
    apply List.eq_nil_iff_forall_not_mem.2
    intro s hs
    exact hEmpty.false s

/-- Successful optional optimum, exposed without an unrelated default. -/
def bestSideEncoder
    (EX : Enumeration X) (EC : Enumeration C)
    (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) : Option (X → C) :=
  bestSideEncoder? EX EC EV M P

omit [Fintype V] [DecidableEq O] in
/-- Every returned total wrapper is globally minimum. -/
theorem bestSideEncoder_minimal
    (EX : Enumeration X) (EC : Enumeration C)
    (EV : Enumeration V) (M : RationalObservationModel X O)
    (P : X → V) {best : X → C}
    (h : bestSideEncoder EX EC EV M P = some best) (s : X → C) :
    sideRisk EV M P best ≤ sideRisk EV M P s :=
  bestSideEncoder?_minimal EX EC EV M P h s

/-! ## Fully noisy fixture -/

/-- A two-state source with an observation independent of the source. -/
def fullyNoisyBinary : RationalObservationModel (Fin 2) (Fin 2) where
  prior := fun _ => 1 / 2
  kernel := fun _ _ => 1 / 2
  prior_nonneg := by intro; norm_num
  prior_sum_one := by norm_num [Fin.sum_univ_two]
  kernel_nonneg := by intro; norm_num
  kernel_sum_one := by intro; norm_num [Fin.sum_univ_two]

/-- In the fully noisy binary fixture the Bayes error is exactly one half. -/
theorem fullyNoisyBinary_risk_half :
    bayesRisk binaryTargetEnumeration fullyNoisyBinary (fun x => x) = 1 / 2 := by
  norm_num [bayesRisk, risk, correctMass, bayesDecoder, bayesTarget, argmaxBy, joint,
    fullyNoisyBinary, binaryTargetEnumeration]

end OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery
