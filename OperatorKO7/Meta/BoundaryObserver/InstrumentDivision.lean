import OperatorKO7.Meta.BoundaryObserver.InstrumentLoss
import OperatorKO7.Meta.BoundaryObserver.InstrumentComposition
import OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
import OperatorKO7.Meta.BoundaryObserver.BoundaryPole

set_option autoImplicit false
open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryObserver.InstrumentDivision

open InstrumentLoss InstrumentComposition ProtocolResolution

/-- The fair label assigns false to the first state and true to the second state. -/
def pairState {X : Type*} (x₀ x₁ : X) (b : Bool) : X :=
  if b then x₁ else x₀

/-- The three-variable joint mass of the fair input label, recorded outcome and retained state. -/
noncomputable def pairJointMass {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) (b : Bool) (r : R) (t : T) : ℝ :=
  (1 / 2 : ℝ) * I.weight (pairState x₀ x₁ b) r t

/-- The label-and-record marginal of the instrument's three-variable law. -/
noncomputable def pairRecordMass {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) (b : Bool) (r : R) : ℝ :=
  ∑ t, pairJointMass I x₀ x₁ b r t

/-- The conditional entropy of the label after the outcome alone, in bits. -/
noncomputable def recordUncertainty {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) : ℝ :=
  ∑ r, massUncertainty (fun b : Bool => pairRecordMass I x₀ x₁ b r)

/-- The information read into the recorded outcome, I(B;r), in bits. -/
noncomputable def readPart {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) : ℝ :=
  jointMI (fun br : Bool × R => pairRecordMass I x₀ x₁ br.1 br.2)

/-- The remaining label uncertainty H(B|r,t), including any initial label ambiguity, in bits. -/
noncomputable def erasedPart {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) : ℝ :=
  ∑ rt : R × T, massUncertainty (fun b : Bool => pairJointMass I x₀ x₁ b rt.1 rt.2)

/-- The information retained behind the record, I(B;t|r), in bits. -/
noncomputable def retainedPart {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) : ℝ :=
  recordUncertainty I x₀ x₁ - erasedPart I x₀ x₁

/-- The uniform Boolean label has exactly one bit of entropy. -/
private theorem fair_label_entropy :
    entropy (binaryPrior (1 / 2)) = 1 := by
  unfold entropy
  rw [binaryPrior_entropy]
  have hh : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [hh, Real.binEntropy_two_inv]
  exact div_self (Real.log_pos one_lt_two).ne'

/-- Summing the instrument's record marginal recovers the fair label. -/
theorem pairRecordMass_label_marginal {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T)
    (x₀ x₁ : X) (b : Bool) :
    (∑ r, pairRecordMass I x₀ x₁ b r) = binaryPrior (1 / 2) b := by
  change (∑ r, ∑ t, (1 / 2 : ℝ) * I.weight (pairState x₀ x₁ b) r t) =
    binaryPrior (1 / 2) b
  calc
    _ = (1 / 2 : ℝ) * (∑ r, ∑ t, I.weight (pairState x₀ x₁ b) r t) := by
      simp only [Finset.mul_sum]
    _ = (1 / 2 : ℝ) := by rw [I.total]; ring
    _ = binaryPrior (1 / 2) b := by cases b <;> norm_num [binaryPrior]

/-- Joint mutual information is prior entropy minus the remaining slice uncertainty. -/
private theorem jointMI_eq_entropy_sub_slices {Y : Type} [Fintype Y]
    (p : Bool × Y → ℝ) :
    jointMI p = entropy (fun b : Bool => ∑ y, p (b, y)) -
      ∑ y, massUncertainty (fun b : Bool => p (b, y)) := by
  unfold jointMI massUncertainty
  rw [entropy_joint_slices]
  simp only [Finset.sum_sub_distrib]
  rw [← entropy_eq_sum (fun y => ∑ b, p (b, y))]
  ring

/-- Outcome information is one bit minus uncertainty left behind the outcome. -/
theorem readPart_eq_one_sub_recordUncertainty {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T) (x₀ x₁ : X) :
    readPart I x₀ x₁ = 1 - recordUncertainty I x₀ x₁ := by
  unfold readPart recordUncertainty
  rw [jointMI_eq_entropy_sub_slices]
  have hp : (fun b : Bool => ∑ r, pairRecordMass I x₀ x₁ b r) =
      binaryPrior (1 / 2) := by
    funext b
    exact pairRecordMass_label_marginal I x₀ x₁ b
  rw [hp, fair_label_entropy]

/-- The read, retained and erased amounts partition the uniform bit for every finite instrument. -/
theorem act_division_chain_rule {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) :
    readPart I x₀ x₁ + retainedPart I x₀ x₁ + erasedPart I x₀ x₁ = 1 := by
  rw [retainedPart, readPart_eq_one_sub_recordUncertainty]
  ring

/-- A concentrated Boolean slice has no conditional uncertainty. -/
private theorem uncertainty_false_only :
    massUncertainty (fun b : Bool => if b then (0 : ℝ) else 1 / 2) = 0 := by
  simp [massUncertainty, entropy_eq_sum, entropyTerm_zero]

/-- A concentrated Boolean slice at true has no conditional uncertainty. -/
private theorem uncertainty_true_only :
    massUncertainty (fun b : Bool => if b then (1 / 2 : ℝ) else 0) = 0 := by
  simp [massUncertainty, entropy_eq_sum, entropyTerm_zero]

/-- The slice with equal fair Boolean masses contains one bit. -/
private theorem uncertainty_fair :
    massUncertainty (fun _ : Bool => (1 / 2 : ℝ)) = 1 := by
  rw [massUncertainty_of_total_one _ (by norm_num [Fintype.sum_bool])]
  have he : (fun _ : Bool => (1 / 2 : ℝ)) = binaryPrior (1 / 2) := by
    funext b
    cases b <;> norm_num [binaryPrior]
  rw [he, fair_label_entropy]

/-- The conditional uncertainty of a uniform bit after a deterministic symbol is one
bit for identical outputs and zero bits for distinct outputs. -/
private theorem point_label_uncertainty {Y : Type} [Fintype Y] [DecidableEq Y] (u v : Y) :
    (∑ y : Y, massUncertainty (fun b : Bool =>
      if (if b then v else u) = y then (1 / 2 : ℝ) else 0)) =
        if u = v then 1 else 0 := by
  classical
  by_cases huv : u = v
  · subst v
    have hh (y : Y) : massUncertainty (fun b : Bool =>
        if (if b then u else u) = y then (1 / 2 : ℝ) else 0) =
        if u = y then 1 else 0 := by
      by_cases hy : u = y
      · have he : (fun b : Bool =>
            if (if b then u else u) = y then (1 / 2 : ℝ) else 0) =
            (fun _ : Bool => (1 / 2 : ℝ)) := by
          funext b
          cases b <;> simp [hy]
        rw [he, uncertainty_fair]
        simp [hy]
      · have he : (fun b : Bool =>
            if (if b then u else u) = y then (1 / 2 : ℝ) else 0) =
            (fun _ : Bool => (0 : ℝ)) := by
          funext b
          cases b <;> simp [hy]
        rw [he, massUncertainty_zero]
        simp [hy]
    calc
      _ = (∑ y : Y, if u = y then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro y _
        simpa using hh y
      _ = 1 := by simp
      _ = (if u = u then 1 else 0) := by simp
  · have hh (y : Y) : massUncertainty (fun b : Bool =>
        if (if b then v else u) = y then (1 / 2 : ℝ) else 0) = 0 := by
      by_cases hu : u = y
      · have hv : v ≠ y := by
          intro he
          exact huv (hu.trans he.symm)
        have he : (fun b : Bool =>
            if (if b then v else u) = y then (1 / 2 : ℝ) else 0) =
            (fun b : Bool => if b then 0 else 1 / 2) := by
          funext b
          cases b <;> simp [hu, hv]
        rw [he, uncertainty_false_only]
      · by_cases hv : v = y
        · have he : (fun b : Bool =>
              if (if b then v else u) = y then (1 / 2 : ℝ) else 0) =
              (fun b : Bool => if b then 1 / 2 else 0) := by
            funext b
            cases b <;> simp [hu, hv]
          rw [he, uncertainty_true_only]
        · have he : (fun b : Bool =>
              if (if b then v else u) = y then (1 / 2 : ℝ) else 0) =
              (fun _ : Bool => (0 : ℝ)) := by
            funext b
            cases b <;> simp [hu, hv]
          rw [he, massUncertainty_zero]
    calc
      _ = (∑ y : Y, (0 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro y _
        exact hh y
      _ = 0 := by simp
      _ = (if u = v then 1 else 0) := by simp [huv]

/-- The deterministic joint-output mass is a half-weight point mass for each label. -/
private theorem pairJointMass_deterministic {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] [DecidableEq R] [DecidableEq T]
    (I : Instrument X R T) (x₀ x₁ : X) (b : Bool) (rt : R × T) :
    pairJointMass (deterministic I) x₀ x₁ b rt.1 rt.2 =
      if joint I (pairState x₀ x₁ b) = rt then (1 / 2 : ℝ) else 0 := by
  classical
  rcases rt with ⟨r, t⟩
  simp only [pairJointMass, deterministic, joint, Prod.mk.injEq,
    mul_ite, mul_one, mul_zero]

/-- The erased amount of a deterministic instrument is one bit precisely for a joint collision. -/
private theorem erasedPart_deterministic {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] [DecidableEq R] [DecidableEq T]
    (I : Instrument X R T) (x₀ x₁ : X) :
    erasedPart (deterministic I) x₀ x₁ =
      if joint I x₀ = joint I x₁ then 1 else 0 := by
  unfold erasedPart
  calc
    (∑ rt : R × T, massUncertainty (fun b : Bool =>
      pairJointMass (deterministic I) x₀ x₁ b rt.1 rt.2)) =
      (∑ rt : R × T, massUncertainty (fun b : Bool =>
        if (if b then joint I x₁ else joint I x₀) = rt then (1 / 2 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro rt _
        have he : (fun b : Bool => pairJointMass (deterministic I) x₀ x₁ b rt.1 rt.2) =
            (fun b : Bool =>
              if (if b then joint I x₁ else joint I x₀) = rt then (1 / 2 : ℝ) else 0) := by
          funext b
          cases b <;> simp [pairState, pairJointMass_deterministic]
        rw [he]
    _ = _ := point_label_uncertainty (joint I x₀) (joint I x₁)

/-- Zero deterministic erasure is equivalent to separation by the recorded outcome and post-state. -/
theorem deterministic_erased_zero_iff_separates {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : Instrument X R T) (x₀ x₁ : X) :
    erasedPart (deterministic I) x₀ x₁ = 0 ↔ joint I x₀ ≠ joint I x₁ := by
  classical
  rw [erasedPart_deterministic]
  by_cases h : joint I x₀ = joint I x₁ <;> simp [h]

/-- The label-and-outcome mass is half of the chosen state's outcome marginal. -/
theorem pairRecordMass_half_outcome {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T)
    (x₀ x₁ : X) (b : Bool) (r : R) :
    pairRecordMass I x₀ x₁ b r =
      (1 / 2 : ℝ) * outcomeLaw I (pairState x₀ x₁ b) r := by
  simp only [pairRecordMass, pairJointMass, outcomeLaw, Finset.mul_sum]

/-- Matching outcome laws make the label-and-record mass a product law. -/
private theorem pairRecordMass_eq_product {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T)
    (x₀ x₁ : X) (h : ∀ r, outcomeLaw I x₀ r = outcomeLaw I x₁ r)
    (b : Bool) (r : R) :
    pairRecordMass I x₀ x₁ b r =
      binaryPrior (1 / 2) b * outcomeLaw I x₀ r := by
  rw [pairRecordMass_half_outcome]
  cases b with
  | false => norm_num [pairState, binaryPrior]
  | true =>
      simpa [pairState, binaryPrior] using
        (congrArg (fun a : ℝ => (1 / 2 : ℝ) * a) (h r)).symm

/-- A single outcome law on the two input states reads zero bits. -/
theorem readPart_zero_of_equal_outcomes {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T)
    (x₀ x₁ : X) (h : ∀ r, outcomeLaw I x₀ r = outcomeLaw I x₁ r) :
    readPart I x₀ x₁ = 0 := by
  unfold readPart
  have hp : (fun br : Bool × R => pairRecordMass I x₀ x₁ br.1 br.2) =
      (fun br : Bool × R => binaryPrior (1 / 2) br.1 * outcomeLaw I x₀ br.2) := by
    funext br
    exact pairRecordMass_eq_product I x₀ x₁ h br.1 br.2
  rw [hp]
  exact jointMI_product_zero (binaryPrior (1 / 2)) (outcomeLaw I x₀)
    (binaryPrior_total _) (outcomeLaw_normalized I x₀)

/-- A singleton outcome alphabet cannot carry information about the input bit. -/
theorem readPart_unit_outcome_zero {X : Type*} {T : Type}
    [Fintype T] (I : StochasticInstrument X Unit T) (x₀ x₁ : X) :
    readPart I x₀ x₁ = 0 := by
  apply readPart_zero_of_equal_outcomes I x₀ x₁
  intro r
  cases r
  have h₀ : outcomeLaw I x₀ () = 1 := by
    simpa using outcomeLaw_normalized I x₀
  have h₁ : outcomeLaw I x₁ () = 1 := by
    simpa using outcomeLaw_normalized I x₁
  exact h₀.trans h₁.symm

/-- The first-state outcome law defines a finite normalized reading for every instrument. -/
noncomputable def instrumentOutcomeReading {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T) :
    BoundaryPole.Reading X R :=
  fun x => {
    mass := outcomeLaw I x
    nonnegative := by
      intro r
      exact Finset.sum_nonneg (fun t _ => I.nonneg x r t)
    total := outcomeLaw_normalized I x
  }

/-- An outcome reading determined by q cannot read a bit from a q-merged input pair. -/
theorem record_determined_read_part_zero {X Q : Type*} {R T : Type}
    [Fintype R] [Fintype T] (q : X → Q) (I : StochasticInstrument X R T)
    (x₀ x₁ : X) (hmerged : q x₀ = q x₁)
    (hdet : BoundaryPole.RecordDetermined q (instrumentOutcomeReading I)) :
    readPart I x₀ x₁ = 0 := by
  apply readPart_zero_of_equal_outcomes I x₀ x₁
  intro r
  exact congrArg (fun p : FiniteLaw R => p.mass r) (hdet x₀ x₁ hmerged)

/-- A deterministic instrument's record marginal is the point mass of its read function. -/
private theorem pairRecordMass_deterministic {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] [DecidableEq R]
    (I : Instrument X R T) (x₀ x₁ : X) (b : Bool) (r : R) :
    pairRecordMass (deterministic I) x₀ x₁ b r =
      if I.read (pairState x₀ x₁ b) = r then (1 / 2 : ℝ) else 0 := by
  rw [pairRecordMass_half_outcome]
  have hout : outcomeLaw (deterministic I) (pairState x₀ x₁ b) r =
      if I.read (pairState x₀ x₁ b) = r then (1 : ℝ) else 0 := by
    classical
    by_cases hr : I.read (pairState x₀ x₁ b) = r
    · simp [outcomeLaw, deterministic, hr]
    · simp [outcomeLaw, deterministic, hr]
  rw [hout]
  by_cases hr : I.read (pairState x₀ x₁ b) = r <;> simp [hr]

/-- The deterministic outcome-only uncertainty is one bit for an outcome collision. -/
private theorem recordUncertainty_deterministic {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] [DecidableEq R]
    (I : Instrument X R T) (x₀ x₁ : X) :
    recordUncertainty (deterministic I) x₀ x₁ =
      if I.read x₀ = I.read x₁ then 1 else 0 := by
  unfold recordUncertainty
  calc
    (∑ r : R, massUncertainty (fun b : Bool =>
      pairRecordMass (deterministic I) x₀ x₁ b r)) =
      (∑ r : R, massUncertainty (fun b : Bool =>
        if (if b then I.read x₁ else I.read x₀) = r then (1 / 2 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro r _
        have he : (fun b : Bool => pairRecordMass (deterministic I) x₀ x₁ b r) =
            (fun b : Bool =>
              if (if b then I.read x₁ else I.read x₀) = r then (1 / 2 : ℝ) else 0) := by
          funext b
          cases b <;> simp [pairState, pairRecordMass_deterministic]
        rw [he]
    _ = _ := point_label_uncertainty (I.read x₀) (I.read x₁)

/-- Distinct deterministic side-symbol outcomes read the entire fair label in one act. -/
theorem side_symbol_read_part_one {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : Instrument X R T) (x₀ x₁ : X)
    (h : I.read x₀ ≠ I.read x₁) :
    readPart (deterministic I) x₀ x₁ = 1 := by
  classical
  rw [readPart_eq_one_sub_recordUncertainty, recordUncertainty_deterministic]
  simp [h]

/-- Silent keep and silent erase read no bit, but erase zero and one bit respectively. -/
theorem keep_erase_division :
    (readPart (deterministic silentKeep) false true = 0 ∧
      erasedPart (deterministic silentKeep) false true = 0) ∧
    (readPart (deterministic silentErase) false true = 0 ∧
      erasedPart (deterministic silentErase) false true = 1) := by
  constructor
  · constructor
    · exact readPart_unit_outcome_zero (deterministic silentKeep) false true
    · rw [erasedPart_deterministic]
      simp [joint, silentKeep]
  · constructor
    · exact readPart_unit_outcome_zero (deterministic silentErase) false true
    · rw [erasedPart_deterministic]
      simp [joint, silentErase]

/-- Conditioning on a finer finite outcome cannot increase the uncertainty of a Boolean
label; zero-mass cells contribute zero without a positivity premise. -/
private theorem uncertainty_sum_le {A : Type} [Fintype A]
    (m : A → Bool → ℝ) (hm : ∀ a b, 0 ≤ m a b) :
    (∑ a, massUncertainty (m a)) ≤
      massUncertainty (fun b : Bool => ∑ a, m a b) := by
  classical
  let c : ℝ := ∑ a, (m a true + m a false)
  have hc : 0 ≤ c := Finset.sum_nonneg (fun a _ =>
    add_nonneg (hm a true) (hm a false))
  by_cases hcz : c = 0
  · have hzero (a : A) (b : Bool) : m a b = 0 := by
      have hle : m a true + m a false ≤ c :=
        Finset.single_le_sum (fun a _ => add_nonneg (hm a true) (hm a false))
          (Finset.mem_univ a)
      have hsum : m a true + m a false = 0 := by
        apply le_antisymm
        · rw [hcz] at hle
          exact hle
        · exact add_nonneg (hm a true) (hm a false)
      cases b <;> linarith [hm a true, hm a false]
    have he (a : A) : m a = fun _ => 0 := by
      funext b
      exact hzero a b
    simp [he, hzero, massUncertainty_zero]
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcz)
    let n : A → Bool → ℝ := fun a b => m a b / c
    have hn (a : A) (b : Bool) : 0 ≤ n a b :=
      div_nonneg (hm a b) hc
    have htot : (∑ a, (n a true + n a false)) = 1 := by
      dsimp [n]
      simp only [← add_div, ← Finset.sum_div]
      exact div_self hcz
    have hfair : (∑ a, massUncertainty (n a)) ≤
        Real.binEntropy (∑ a, n a true) / Real.log 2 := by
      simpa using (ResolutionAttainment.sum_massUncertainty_le_binEntropy
        Finset.univ n hn (by simpa using htot) (fun _ => false))
    have hsum : (∑ a, n a true) + (∑ a, n a false) = 1 := by
      rw [← Finset.sum_add_distrib]
      exact htot
    have hpos : 0 < (∑ a, n a true) + (∑ a, n a false) := by
      rw [hsum]
      norm_num
    have hmar : massUncertainty (fun b : Bool => ∑ a, n a b) =
        Real.binEntropy (∑ a, n a true) / Real.log 2 := by
      rw [ResolutionAttainment.massUncertainty_bool _ hpos, hsum]
      simp
    have hscale (a : A) (b : Bool) : m a b = c * n a b := by
      dsimp [n]
      field_simp [hcz]
    have hmarScale : (fun b : Bool => ∑ a, m a b) =
        (fun b : Bool => c * (∑ a, n a b)) := by
      funext b
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact hscale a b
    calc
      (∑ a, massUncertainty (m a)) =
          ∑ a, c * massUncertainty (n a) := by
        apply Finset.sum_congr rfl
        intro a _
        have he : m a = fun b => c * n a b := by
          funext b
          exact hscale a b
        rw [he, massUncertainty_scale]
      _ = c * (∑ a, massUncertainty (n a)) := by rw [Finset.mul_sum]
      _ ≤ c * massUncertainty (fun b : Bool => ∑ a, n a b) :=
        mul_le_mul_of_nonneg_left (hfair.trans_eq hmar.symm) hc
      _ = massUncertainty (fun b : Bool => ∑ a, m a b) := by
        rw [hmarScale, massUncertainty_scale]

/-- A finite normalized channel cannot reduce Boolean conditional uncertainty. -/
private theorem uncertainty_kernel_mono {S U : Type} [Fintype S] [Fintype U]
    (m : Bool → S → ℝ) (hm : ∀ b s, 0 ≤ m b s)
    (K : S → U → ℝ) (hK : ∀ s u, 0 ≤ K s u)
    (hKtotal : ∀ s, ∑ u, K s u = 1) :
    (∑ s, massUncertainty (fun b : Bool => m b s)) ≤
      ∑ u, massUncertainty (fun b : Bool => ∑ s, m b s * K s u) := by
  have hscale (s : S) (u : U) :
      massUncertainty (fun b : Bool => m b s * K s u) =
        K s u * massUncertainty (fun b : Bool => m b s) := by
    have he : (fun b : Bool => m b s * K s u) =
        (fun b : Bool => K s u * m b s) := by
      funext b
      ring
    rw [he, massUncertainty_scale]
  calc
    (∑ s, massUncertainty (fun b : Bool => m b s)) =
        ∑ s, ∑ u, massUncertainty (fun b : Bool => m b s * K s u) := by
      apply Finset.sum_congr rfl
      intro s _
      simp_rw [hscale s]
      rw [← Finset.sum_mul, hKtotal s, one_mul]
    _ = ∑ u, ∑ s, massUncertainty (fun b : Bool => m b s * K s u) :=
      Finset.sum_comm
    _ ≤ ∑ u, massUncertainty (fun b : Bool => ∑ s, m b s * K s u) := by
      apply Finset.sum_le_sum
      intro u _
      exact uncertainty_sum_le (fun s b => m b s * K s u)
        (fun s b => mul_nonneg (hm b s) (hK s u))

/-- The continuation retains the first outcome and otherwise uses only its post-state. -/
private noncomputable def continuationKernel {R T W U : Type}
    [Fintype R] [Fintype T] [Fintype W] [Fintype U]
    (J : R → StochasticInstrument T W U) (rt : R × T) (out : (R × W) × U) : ℝ := by
  classical
  exact if out.1.1 = rt.1 then (J rt.1).weight rt.2 out.1.2 out.2 else 0

/-- Every continuation row is nonnegative, including a mismatched first outcome. -/
private theorem continuationKernel_nonnegative {R T W U : Type}
    [Fintype R] [Fintype T] [Fintype W] [Fintype U]
    (J : R → StochasticInstrument T W U) (rt : R × T) (out : (R × W) × U) :
    0 ≤ continuationKernel J rt out := by
  classical
  unfold continuationKernel
  split_ifs
  · exact (J rt.1).nonneg rt.2 out.1.2 out.2
  · exact le_refl _

/-- Every continuation row sums to one, with the first outcome retained exactly. -/
private theorem continuationKernel_total {R T W U : Type}
    [Fintype R] [Fintype T] [Fintype W] [Fintype U]
    (J : R → StochasticInstrument T W U) (rt : R × T) :
    (∑ out : (R × W) × U, continuationKernel J rt out) = 1 := by
  classical
  calc
    (∑ out : (R × W) × U, continuationKernel J rt out) =
      ∑ r : R, if r = rt.1 then (∑ w : W, ∑ u : U, (J rt.1).weight rt.2 w u)
        else 0 := by
          simp [continuationKernel, Fintype.sum_prod_type]
    _ = 1 := by simp [(J rt.1).total rt.2]

/-- The continuation mixture reproduces the actual adaptive-composition joint law. -/
private theorem continuation_pair_mass {X : Type*} {R T W U : Type}
    [Fintype R] [Fintype T] [Fintype W] [Fintype U]
    (I : StochasticInstrument X R T) (J : R → StochasticInstrument T W U)
    (x₀ x₁ : X) (b : Bool) (out : (R × W) × U) :
    (∑ rt : R × T, pairJointMass I x₀ x₁ b rt.1 rt.2 *
      continuationKernel J rt out) =
      pairJointMass (sequential I J) x₀ x₁ b out.1 out.2 := by
  classical
  rcases out with ⟨⟨r, w⟩, u⟩
  simp [pairJointMass, sequential, continuationKernel,
    Fintype.sum_prod_type, mul_ite, mul_assoc, ← Finset.mul_sum]

/-- A continuation acting on the retained post-state cannot reduce erased label entropy,
even when it is chosen adaptively from the first recorded outcome. -/
theorem erased_ge_under_continuation {X : Type*} {R T W U : Type}
    [Fintype R] [Fintype T] [Fintype W] [Fintype U]
    (I : StochasticInstrument X R T) (J : R → StochasticInstrument T W U)
    (x₀ x₁ : X) :
    erasedPart I x₀ x₁ ≤ erasedPart (sequential I J) x₀ x₁ := by
  have hm : ∀ b (rt : R × T), 0 ≤ pairJointMass I x₀ x₁ b rt.1 rt.2 := by
    intro b rt
    exact mul_nonneg (by norm_num) (I.nonneg (pairState x₀ x₁ b) rt.1 rt.2)
  have hkernel :
      (∑ rt : R × T, massUncertainty
        (fun b : Bool => pairJointMass I x₀ x₁ b rt.1 rt.2)) ≤
        ∑ out : (R × W) × U, massUncertainty
          (fun b : Bool => ∑ rt : R × T,
            pairJointMass I x₀ x₁ b rt.1 rt.2 * continuationKernel J rt out) :=
    uncertainty_kernel_mono
      (fun b (rt : R × T) => pairJointMass I x₀ x₁ b rt.1 rt.2) hm
      (continuationKernel J) (continuationKernel_nonnegative J)
      (continuationKernel_total J)
  calc
    erasedPart I x₀ x₁ =
        ∑ rt : R × T, massUncertainty
          (fun b : Bool => pairJointMass I x₀ x₁ b rt.1 rt.2) := rfl
    _ ≤ ∑ out : (R × W) × U, massUncertainty
          (fun b : Bool => ∑ rt : R × T,
            pairJointMass I x₀ x₁ b rt.1 rt.2 * continuationKernel J rt out) := hkernel
    _ = erasedPart (sequential I J) x₀ x₁ := by
      unfold erasedPart
      apply Finset.sum_congr rfl
      intro out _
      have he : (fun b : Bool => ∑ rt : R × T,
            pairJointMass I x₀ x₁ b rt.1 rt.2 * continuationKernel J rt out) =
          (fun b : Bool =>
            pairJointMass (sequential I J) x₀ x₁ b out.1 out.2) := by
        funext b
        exact continuation_pair_mass I J x₀ x₁ b out
      rw [he]

/-- The information read and retained together cannot grow under any stochastic adaptive
continuation that observes only the first record and its surviving state. -/
theorem kept_le_under_continuation {X : Type*} {R T W U : Type}
    [Fintype R] [Fintype T] [Fintype W] [Fintype U]
    (I : StochasticInstrument X R T) (J : R → StochasticInstrument T W U)
    (x₀ x₁ : X) :
    readPart (sequential I J) x₀ x₁ + retainedPart (sequential I J) x₀ x₁ ≤
      readPart I x₀ x₁ + retainedPart I x₀ x₁ := by
  have hbefore := act_division_chain_rule I x₀ x₁
  have hafter := act_division_chain_rule (sequential I J) x₀ x₁
  have hmono := erased_ge_under_continuation I J x₀ x₁
  linarith

/-! ## The three parts of the bit lie in the unit interval

Manuscript: `prop:act-division`.
For every normalized finite instrument, every pair of input states and the fair input label, each of
the read, retained and erased parts lies between zero and one bit. The bounds come from the actual
masses: the uncertainty of nonnegative masses is nonnegative, and summing a coordinate out of the
masses cannot lower the uncertainty of the label, so `erasedPart ≤ recordUncertainty ≤ 1`. No bound
uses the three-part sum `act_division_chain_rule`.
-/

/-- A Boolean slice of nonnegative masses has nonnegative uncertainty. -/
theorem massUncertainty_bool_nonneg (m : Bool → ℝ) (hm : ∀ b, 0 ≤ m b) :
    0 ≤ massUncertainty m := by
  rcases (add_nonneg (hm true) (hm false)).eq_or_lt with h0 | hpos
  · have ht : m true = 0 := by linarith [hm true, hm false]
    have hf : m false = 0 := by linarith [hm true, hm false]
    have he : m = fun _ => 0 := by
      funext b
      cases b
      · exact hf
      · exact ht
    rw [he, massUncertainty_zero]
  · rw [ResolutionAttainment.massUncertainty_bool m hpos]
    apply div_nonneg _ (Real.log_pos one_lt_two).le
    apply mul_nonneg hpos.le
    apply Real.binEntropy_nonneg
    · exact div_nonneg (hm true) hpos.le
    · exact (div_le_one hpos).mpr (le_add_of_nonneg_right (hm false))

/-- Summing a finite coordinate out of nonnegative masses cannot lower the uncertainty of a
Boolean label: the summed uncertainties of the slices are at most the uncertainty of their sum. -/
theorem massUncertainty_sum_le_marginal {A : Type} [Fintype A] (m : A → Bool → ℝ)
    (hm : ∀ a b, 0 ≤ m a b) :
    (∑ a, massUncertainty (m a)) ≤ massUncertainty (fun b : Bool => ∑ a, m a b) :=
  uncertainty_sum_le m hm

/-- Every label, outcome and post-state mass of the fair pair is nonnegative. -/
theorem pairJointMass_nonneg {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) (b : Bool) (r : R) (t : T) :
    0 ≤ pairJointMass I x₀ x₁ b r t :=
  mul_nonneg (by norm_num) (I.nonneg (pairState x₀ x₁ b) r t)

/-- Every label and outcome mass of the fair pair is nonnegative. -/
theorem pairRecordMass_nonneg {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) (b : Bool) (r : R) :
    0 ≤ pairRecordMass I x₀ x₁ b r :=
  Finset.sum_nonneg (fun t _ => pairJointMass_nonneg I x₀ x₁ b r t)

/-- The erased part `H(B | r, t)` is nonnegative: each term is the uncertainty of nonnegative
masses. -/
theorem erasedPart_nonneg {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) : 0 ≤ erasedPart I x₀ x₁ :=
  Finset.sum_nonneg (fun rt _ => massUncertainty_bool_nonneg _
    (fun b => pairJointMass_nonneg I x₀ x₁ b rt.1 rt.2))

/-- The uncertainty `H(B | r)` left behind the outcome is nonnegative. -/
theorem recordUncertainty_nonneg {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) : 0 ≤ recordUncertainty I x₀ x₁ :=
  Finset.sum_nonneg (fun r _ => massUncertainty_bool_nonneg _
    (fun b => pairRecordMass_nonneg I x₀ x₁ b r))

/-- Summing the post-state out of the masses: `H(B | r, t) ≤ H(B | r)`. -/
theorem erasedPart_le_recordUncertainty {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) :
    erasedPart I x₀ x₁ ≤ recordUncertainty I x₀ x₁ := by
  unfold erasedPart recordUncertainty
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro r _
  exact uncertainty_sum_le (fun t b => pairJointMass I x₀ x₁ b r t)
    (fun t b => pairJointMass_nonneg I x₀ x₁ b r t)

/-- Summing the outcome out of the masses: `H(B | r) ≤ H(B)`, one bit for the fair label. -/
theorem recordUncertainty_le_one {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) : recordUncertainty I x₀ x₁ ≤ 1 := by
  have hmono := uncertainty_sum_le (fun r b => pairRecordMass I x₀ x₁ b r)
    (fun r b => pairRecordMass_nonneg I x₀ x₁ b r)
  have hprior : (fun b : Bool => ∑ r, pairRecordMass I x₀ x₁ b r) = binaryPrior (1 / 2) := by
    funext b
    exact pairRecordMass_label_marginal I x₀ x₁ b
  have hone : massUncertainty (binaryPrior (1 / 2)) = 1 := by
    rw [massUncertainty_of_total_one _ (binaryPrior_total _), fair_label_entropy]
  unfold recordUncertainty
  calc (∑ r, massUncertainty (fun b : Bool => pairRecordMass I x₀ x₁ b r))
      ≤ massUncertainty (fun b : Bool => ∑ r, pairRecordMass I x₀ x₁ b r) := hmono
    _ = 1 := by rw [hprior, hone]

/-- The read part `I(B; r)` is nonnegative, since `H(B | r) ≤ H(B)`. -/
theorem readPart_nonneg {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) : 0 ≤ readPart I x₀ x₁ := by
  rw [readPart_eq_one_sub_recordUncertainty]
  linarith [recordUncertainty_le_one I x₀ x₁]

/-- The read part is at most one bit, since `H(B | r) ≥ 0`. -/
theorem readPart_le_one {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) : readPart I x₀ x₁ ≤ 1 := by
  rw [readPart_eq_one_sub_recordUncertainty]
  linarith [recordUncertainty_nonneg I x₀ x₁]

/-- The retained part `I(B; t | r)` is nonnegative, since `H(B | r, t) ≤ H(B | r)`. -/
theorem retainedPart_nonneg {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) : 0 ≤ retainedPart I x₀ x₁ := by
  unfold retainedPart
  linarith [erasedPart_le_recordUncertainty I x₀ x₁]

/-- The retained part is at most one bit, since `H(B | r) ≤ 1` and `H(B | r, t) ≥ 0`. -/
theorem retainedPart_le_one {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) : retainedPart I x₀ x₁ ≤ 1 := by
  unfold retainedPart
  linarith [recordUncertainty_le_one I x₀ x₁, erasedPart_nonneg I x₀ x₁]

/-- The erased part is at most one bit, since `H(B | r, t) ≤ H(B | r) ≤ 1`. -/
theorem erasedPart_le_one {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) : erasedPart I x₀ x₁ ≤ 1 :=
  (erasedPart_le_recordUncertainty I x₀ x₁).trans (recordUncertainty_le_one I x₀ x₁)

/--
`prop:act-division`, the three parts as amounts of the bit.

Proves: for every normalized finite stochastic instrument `I`, every pair of input states
`x₀`, `x₁` and the fair input label, the read part, the retained part and the erased part each lie
in `[0, 1]`, in bits.
Does not use: the three-part sum `act_division_chain_rule`; every bound comes from the actual masses
and from the monotonicity of uncertainty under summing out a coordinate.
Relation: the finite joint law of the label, the outcome and the post-state. Trust: kernel-only.
-/
theorem act_division_parts_unit_interval {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) :
    (0 ≤ readPart I x₀ x₁ ∧ readPart I x₀ x₁ ≤ 1) ∧
    (0 ≤ retainedPart I x₀ x₁ ∧ retainedPart I x₀ x₁ ≤ 1) ∧
    (0 ≤ erasedPart I x₀ x₁ ∧ erasedPart I x₀ x₁ ≤ 1) :=
  ⟨⟨readPart_nonneg I x₀ x₁, readPart_le_one I x₀ x₁⟩,
    ⟨retainedPart_nonneg I x₀ x₁, retainedPart_le_one I x₀ x₁⟩,
    ⟨erasedPart_nonneg I x₀ x₁, erasedPart_le_one I x₀ x₁⟩⟩

/-- Each upper bound is attained: the keep instrument retains the whole bit, the erase instrument
erases it, and the read-and-erase instrument reads it. -/
theorem act_division_upper_bounds_attained :
    retainedPart (deterministic silentKeep) false true = 1 ∧
    erasedPart (deterministic silentErase) false true = 1 ∧
    readPart (deterministic readAndErase) false true = 1 := by
  refine ⟨?_, keep_erase_division.2.2,
    side_symbol_read_part_one readAndErase false true (by simp [readAndErase])⟩
  unfold retainedPart
  rw [recordUncertainty_deterministic, keep_erase_division.1.2]
  simp [silentKeep]


/-! ## Initial ambiguity and intrinsic loss

The old erasedPart is remaining label uncertainty.
Subtracting initial label ambiguity identifies loss caused by the instrument itself.
-/

/-- The fair label is initially ambiguous exactly when both labels select the same state. -/
noncomputable def initialAmbiguity {X : Type*} (x₀ x₁ : X) : ℝ := by
  classical
  exact if x₀ = x₁ then 1 else 0

/-- Label uncertainty added by the instrument, after subtracting ambiguity already in the input. -/
noncomputable def intrinsicErasedPart {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) : ℝ :=
  erasedPart I x₀ x₁ - initialAmbiguity x₀ x₁

/-- Identical inputs leave the independent fair label completely unknown. -/
theorem erasedPart_self {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x : X) : erasedPart I x x = 1 := by
  unfold erasedPart
  calc
    _ = ∑ rt : R × T, I.weight x rt.1 rt.2 := by
      apply Finset.sum_congr rfl
      intro rt _
      have hmass : (fun b : Bool => pairJointMass I x x b rt.1 rt.2) =
          (fun _ : Bool => I.weight x rt.1 rt.2 * (1 / 2 : ℝ)) := by
        funext b
        simp [pairJointMass, pairState, mul_comm]
      rw [hmass, massUncertainty_scale, uncertainty_fair, mul_one]
    _ = 1 := by
      rw [Fintype.sum_prod_type]
      exact I.total x

theorem initialAmbiguity_unit_interval {X : Type*} (x₀ x₁ : X) :
    0 ≤ initialAmbiguity x₀ x₁ ∧ initialAmbiguity x₀ x₁ ≤ 1 := by
  classical
  unfold initialAmbiguity
  split_ifs <;> norm_num

theorem intrinsicErasedPart_self {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x : X) : intrinsicErasedPart I x x = 0 := by
  simp [intrinsicErasedPart, erasedPart_self, initialAmbiguity]

theorem intrinsicErasedPart_nonneg {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) : 0 ≤ intrinsicErasedPart I x₀ x₁ := by
  classical
  by_cases h : x₀ = x₁
  · subst x₁
    rw [intrinsicErasedPart_self]
  · simpa [intrinsicErasedPart, initialAmbiguity, h] using erasedPart_nonneg I x₀ x₁

theorem intrinsicErasedPart_le_one {X : Type*} {R T : Type} [Fintype R] [Fintype T]
    (I : StochasticInstrument X R T) (x₀ x₁ : X) : intrinsicErasedPart I x₀ x₁ ≤ 1 := by
  unfold intrinsicErasedPart
  linarith [(initialAmbiguity_unit_interval x₀ x₁).1, erasedPart_le_one I x₀ x₁]

/-- Initial ambiguity, read information, retained information and intrinsic loss partition the bit. -/
theorem act_division_with_initial_ambiguity {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T) (x₀ x₁ : X) :
    initialAmbiguity x₀ x₁ + readPart I x₀ x₁ + retainedPart I x₀ x₁ +
      intrinsicErasedPart I x₀ x₁ = 1 := by
  unfold intrinsicErasedPart
  linarith [act_division_chain_rule I x₀ x₁]

/-- Each term in the corrected four-part decomposition is an amount between zero and one bit. -/
theorem act_division_four_parts_unit_interval {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T) (x₀ x₁ : X) :
    (0 ≤ initialAmbiguity x₀ x₁ ∧ initialAmbiguity x₀ x₁ ≤ 1) ∧
    (0 ≤ readPart I x₀ x₁ ∧ readPart I x₀ x₁ ≤ 1) ∧
    (0 ≤ retainedPart I x₀ x₁ ∧ retainedPart I x₀ x₁ ≤ 1) ∧
    (0 ≤ intrinsicErasedPart I x₀ x₁ ∧ intrinsicErasedPart I x₀ x₁ ≤ 1) :=
  ⟨initialAmbiguity_unit_interval x₀ x₁,
    ⟨readPart_nonneg I x₀ x₁, readPart_le_one I x₀ x₁⟩,
    ⟨retainedPart_nonneg I x₀ x₁, retainedPart_le_one I x₀ x₁⟩,
    ⟨intrinsicErasedPart_nonneg I x₀ x₁, intrinsicErasedPart_le_one I x₀ x₁⟩⟩

/-- Adaptive continuation cannot undo intrinsic information loss. -/
theorem intrinsicErasedPart_ge_under_continuation {X : Type*} {R T W U : Type}
    [Fintype R] [Fintype T] [Fintype W] [Fintype U]
    (I : StochasticInstrument X R T) (J : R → StochasticInstrument T W U)
    (x₀ x₁ : X) :
    intrinsicErasedPart I x₀ x₁ ≤ intrinsicErasedPart (sequential I J) x₀ x₁ := by
  exact sub_le_sub_right (erased_ge_under_continuation I J x₀ x₁) _

/-- A restorer for the two selected states need not recover their labels when they coincide. -/
def PairRecoverable {X R T : Type*} (I : Instrument X R T) (x₀ x₁ : X) : Prop :=
  ∃ restore : R × T → X, restore (joint I x₀) = x₀ ∧ restore (joint I x₁) = x₁

theorem pairRecoverable_iff_collision_implies_eq {X R T : Type*}
    (I : Instrument X R T) (x₀ x₁ : X) :
    PairRecoverable I x₀ x₁ ↔ (joint I x₀ = joint I x₁ → x₀ = x₁) := by
  classical
  constructor
  · rintro ⟨restore, h₀, h₁⟩ h
    exact h₀.symm.trans ((congrArg restore h).trans h₁)
  · intro h
    refine ⟨fun rt => if rt = joint I x₀ then x₀ else x₁, by simp, ?_⟩
    by_cases he : joint I x₁ = joint I x₀
    · simp [he, h he.symm]
    · simp [he]

theorem deterministic_intrinsic_zero_iff_collision_implies_eq {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : Instrument X R T) (x₀ x₁ : X) :
    intrinsicErasedPart (deterministic I) x₀ x₁ = 0 ↔
      (joint I x₀ = joint I x₁ → x₀ = x₁) := by
  classical
  rw [intrinsicErasedPart, erasedPart_deterministic]
  by_cases h : x₀ = x₁
  · subst x₁
    simp [initialAmbiguity]
  · by_cases he : joint I x₀ = joint I x₁ <;> simp [initialAmbiguity, h, he]

/-- Zero intrinsic loss is precisely restoration on the selected pair, including coincident inputs. -/
theorem deterministic_intrinsic_zero_iff_pairRecoverable {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : Instrument X R T) (x₀ x₁ : X) :
    intrinsicErasedPart (deterministic I) x₀ x₁ = 0 ↔ PairRecoverable I x₀ x₁ := by
  rw [deterministic_intrinsic_zero_iff_collision_implies_eq,
    pairRecoverable_iff_collision_implies_eq]

/-- Vanishing intrinsic loss on all fair input pairs exactly characterizes global restoration. -/
theorem recoverable_iff_all_pairs_intrinsic_zero {X : Type*} [Nonempty X] {R T : Type}
    [Fintype R] [Fintype T] (I : Instrument X R T) :
    Recoverable I ↔ ∀ x₀ x₁, intrinsicErasedPart (deterministic I) x₀ x₁ = 0 := by
  rw [recoverable_iff_joint_injective]
  constructor
  · intro h x₀ x₁
    exact (deterministic_intrinsic_zero_iff_collision_implies_eq I x₀ x₁).mpr
      (fun he => h he)
  · intro h x₀ x₁ he
    exact (deterministic_intrinsic_zero_iff_collision_implies_eq I x₀ x₁).mp
      (h x₀ x₁) he

/-- A recovered input can retain one bit of initial label ambiguity and have zero intrinsic loss. -/
theorem recovered_state_with_initial_ambiguity :
    Recoverable silentKeep ∧ erasedPart (deterministic silentKeep) false false = 1 ∧
      intrinsicErasedPart (deterministic silentKeep) false false = 0 := by
  exact ⟨equal_records_different_recovery.2.1, erasedPart_self _ _,
    intrinsicErasedPart_self _ _⟩

#check @initialAmbiguity
#check @intrinsicErasedPart
#check @erasedPart_self
#check @initialAmbiguity_unit_interval
#check @intrinsicErasedPart_self
#check @intrinsicErasedPart_nonneg
#check @intrinsicErasedPart_le_one
#check @act_division_with_initial_ambiguity
#check @act_division_four_parts_unit_interval
#check @intrinsicErasedPart_ge_under_continuation
#check @PairRecoverable
#check @pairRecoverable_iff_collision_implies_eq
#check @deterministic_intrinsic_zero_iff_collision_implies_eq
#check @deterministic_intrinsic_zero_iff_pairRecoverable
#check @recoverable_iff_all_pairs_intrinsic_zero
#check @recovered_state_with_initial_ambiguity

#print axioms initialAmbiguity
#print axioms intrinsicErasedPart
#print axioms erasedPart_self
#print axioms initialAmbiguity_unit_interval
#print axioms intrinsicErasedPart_self
#print axioms intrinsicErasedPart_nonneg
#print axioms intrinsicErasedPart_le_one
#print axioms act_division_with_initial_ambiguity
#print axioms act_division_four_parts_unit_interval
#print axioms intrinsicErasedPart_ge_under_continuation
#print axioms PairRecoverable
#print axioms pairRecoverable_iff_collision_implies_eq
#print axioms deterministic_intrinsic_zero_iff_collision_implies_eq
#print axioms deterministic_intrinsic_zero_iff_pairRecoverable
#print axioms recoverable_iff_all_pairs_intrinsic_zero
#print axioms recovered_state_with_initial_ambiguity

end OperatorKO7.Meta.BoundaryObserver.InstrumentDivision
