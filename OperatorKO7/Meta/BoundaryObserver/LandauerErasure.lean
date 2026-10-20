import OperatorKO7.Meta.BoundaryObserver.InstrumentDivision
import OperatorKO7.Meta.BoundaryObserver.InstrumentLoss

set_option autoImplicit false
open scoped BigOperators

/-!
# Counting the bit erased by resetting a retained record

Proof graph: Audit/ledgers/boundary-theorem/BOUNDARY-THEOREM-MATH-COMPLETION-PROOF-GRAPH.md,
node N24. This module accounts for the information lost by erasure or by clearing
a recorded outcome. It makes no claim about heat or physical work.
-/

namespace OperatorKO7.Meta.BoundaryObserver.LandauerErasure

open InstrumentDivision InstrumentLoss InstrumentComposition ProtocolResolution

/-- On the fair Boolean pair, silent erasure loses one bit and reads none,
while silent retention preserves the bit and also reads none. -/
theorem erase_charges_one_bit :
    (readPart (deterministic silentErase) false true = 0 ∧
      erasedPart (deterministic silentErase) false true = 1) ∧
    (readPart (deterministic silentKeep) false true = 0 ∧
      erasedPart (deterministic silentKeep) false true = 0) := by
  exact ⟨keep_erase_division.2, keep_erase_division.1⟩

/-- Clearing a recorded outcome leaves its old post-state distribution unchanged
and replaces the outcome alphabet by the single value of Unit. -/
noncomputable def forgetRecord {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T) :
    StochasticInstrument X Unit T where
  weight x _ t := stateLaw I x t
  nonneg := by
    intro x r t
    exact Finset.sum_nonneg (fun y _ => I.nonneg x y t)
  total := by
    intro x
    simpa using stateLaw_normalized I x

/-- Forgetting a recorded outcome preserves each probability of the retained state. -/
theorem forgetRecord_preserves_stateLaw {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T)
    (x : X) (t : T) :
    stateLaw (forgetRecord I) x t = stateLaw I x t := by
  simp [stateLaw, forgetRecord]

/-- Clearing the outcome record turns the fair input bit into the sum of
the original read, retained and erased parts, less the information retained
in the post-state. Equivalently, the new erased part is one minus that retained part. -/
theorem erasedPart_forgetRecord {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T)
    (x₀ x₁ : X) :
    (erasedPart (forgetRecord I) x₀ x₁ =
      erasedPart I x₀ x₁ + readPart I x₀ x₁ + retainedPart I x₀ x₁ -
      retainedPart (forgetRecord I) x₀ x₁) ∧
    (erasedPart (forgetRecord I) x₀ x₁ =
      1 - retainedPart (forgetRecord I) x₀ x₁) := by
  have hbefore := act_division_chain_rule I x₀ x₁
  have hafter := act_division_chain_rule (forgetRecord I) x₀ x₁
  have hread := readPart_unit_outcome_zero (forgetRecord I) x₀ x₁
  constructor <;> linarith

/-- A deterministic read-and-reset operation records the entire fair bit without
erasing it; clearing its record erases exactly that previously read bit. -/
theorem reset_after_read_costs_read_bit :
    (readPart (deterministic readAndErase) false true = 1 ∧
      erasedPart (deterministic readAndErase) false true = 0) ∧
    erasedPart (forgetRecord (deterministic readAndErase)) false true = 1 := by
  have hread : readPart (deterministic readAndErase) false true = 1 := by
    apply side_symbol_read_part_one
    simp [readAndErase]
  have hzero : erasedPart (deterministic readAndErase) false true = 0 := by
    apply (deterministic_erased_zero_iff_separates readAndErase false true).2
    simp [joint, readAndErase]
  have hweight (x : Bool) (r : Unit) (t : Bool) :
      (forgetRecord (deterministic readAndErase)).weight x r t =
      (deterministic silentErase).weight x r t := by
    cases r
    cases x <;> cases t <;>
      simp [forgetRecord, stateLaw, deterministic, readAndErase, silentErase] <;> decide
  have hsame :
      erasedPart (forgetRecord (deterministic readAndErase)) false true =
      erasedPart (deterministic silentErase) false true := by
    unfold erasedPart
    apply Finset.sum_congr rfl
    intro rt _
    apply congrArg massUncertainty
    funext b
    simp only [pairJointMass]
    rw [hweight]
  exact ⟨⟨hread, hzero⟩, hsame.trans (keep_erase_division.2.2)⟩


/-! ## The information cost of clearing an outcome while retaining the post-state -/

/-- The classical conditional uncertainty of the recorded outcome given the retained
post-state, H(R|T), measured in bits from the actual finite joint mass. This
number is not a bound on physical heat. -/
noncomputable def recordGivenStateEntropy {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T)
    (x₀ x₁ : X) : ℝ :=
  ∑ t : T, massUncertainty
    (fun r : R => ∑ b : Bool, pairJointMass I x₀ x₁ b r t)

/-- The residual record noise after the label and the retained state are known,
H(R|B,T). A record may contain noise independent of the input label. -/
noncomputable def recordGivenLabelStateEntropy {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T)
    (x₀ x₁ : X) : ℝ :=
  ∑ t : T, ∑ b : Bool,
    massUncertainty (fun r : R => pairJointMass I x₀ x₁ b r t)

/-- The extra label information carried by the record beyond the post-state:
I(B;R|T) = H(R|T) - H(R|B,T). This uses the normalized finite instrument,
not a thermodynamic erasure model. -/
noncomputable def resetConditionalInformation {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T)
    (x₀ x₁ : X) : ℝ :=
  recordGivenStateEntropy I x₀ x₁ - recordGivenLabelStateEntropy I x₀ x₁

/-- The reset outcome is a singleton, and each label-and-post-state mass is
the sum of the original masses over the cleared outcome. -/
theorem forgetRecord_pairJointMass {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T)
    (x₀ x₁ : X) (b : Bool) (t : T) :
    pairJointMass (forgetRecord I) x₀ x₁ b () t =
      ∑ r : R, pairJointMass I x₀ x₁ b r t := by
  change (1 / 2 : ℝ) * (∑ r : R, I.weight (pairState x₀ x₁ b) r t) =
    ∑ r : R, (1 / 2 : ℝ) * I.weight (pairState x₀ x₁ b) r t
  rw [Finset.mul_sum]

/-- The erased label uncertainty after clearing the record is H(B|T), with
the original post-state law and no missing output mass. -/
theorem erasedPart_forgetRecord_eq_labelGivenState {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T)
    (x₀ x₁ : X) :
    erasedPart (forgetRecord I) x₀ x₁ =
      ∑ t : T, massUncertainty
        (fun b : Bool => ∑ r : R, pairJointMass I x₀ x₁ b r t) := by
  unfold erasedPart
  rw [Fintype.sum_prod_type, Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro t _
  apply congrArg massUncertainty
  funext b
  exact forgetRecord_pairJointMass I x₀ x₁ b t

/-- The old erased label uncertainty H(B|R,T) is a sum over each retained
post-state and then each original outcome. -/
theorem erasedPart_eq_labelGivenRecordState {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T)
    (x₀ x₁ : X) :
    erasedPart I x₀ x₁ =
      ∑ t : T, ∑ r : R,
        massUncertainty (fun b : Bool => pairJointMass I x₀ x₁ b r t) := by
  unfold erasedPart
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Conditional-information chain symmetry for a finite slice. This is an
entropy identity and does not assume heat cost. -/
private theorem massUncertainty_exchange {A B : Type}
    [Fintype A] [Fintype B] (m : A → B → ℝ) :
    massUncertainty (fun a : A => ∑ b : B, m a b) -
        (∑ b : B, massUncertainty (fun a : A => m a b)) =
      massUncertainty (fun b : B => ∑ a : A, m a b) -
        (∑ a : A, massUncertainty (fun b : B => m a b)) := by
  have htotal : (∑ a : A, ∑ b : B, m a b) =
      ∑ b : B, ∑ a : A, m a b := Finset.sum_comm
  have hterms : (∑ b : B, ∑ a : A, entropyTerm (m a b)) =
      ∑ a : A, ∑ b : B, entropyTerm (m a b) := Finset.sum_comm
  simp only [massUncertainty, entropy_eq_sum, Finset.sum_sub_distrib]
  rw [htotal, hterms]
  ring

/-- General record-reset identity on every finite normalized stochastic
instrument: clearing R while retaining T increases erased label information
by I(B;R|T). The same increment is H(R|T)-H(R|B,T), so a noisy record's
entire H(R|T) is not automatically information about B. -/
theorem reset_erasure_increment_eq_conditional_information {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T)
    (x₀ x₁ : X) :
    erasedPart (forgetRecord I) x₀ x₁ - erasedPart I x₀ x₁ =
      resetConditionalInformation I x₀ x₁ := by
  rw [erasedPart_forgetRecord_eq_labelGivenState,
    erasedPart_eq_labelGivenRecordState]
  unfold resetConditionalInformation recordGivenStateEntropy recordGivenLabelStateEntropy
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  exact massUncertainty_exchange
    (fun b r => pairJointMass I x₀ x₁ b r t)

/-- Conditioning a Boolean label on a finite nonnegative array cannot increase
its uncertainty. This works even if the array is an unnormalized slice with
zero-mass cells; it is the concavity step behind reset monotonicity. -/
private theorem finiteMassUncertainty_sum_le {A : Type} [Fintype A]
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

/-- The reset increment is nonnegative for normalized finite instruments.
No independent physical heat or work conclusion follows. -/
theorem resetConditionalInformation_nonnegative {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T)
    (x₀ x₁ : X) : 0 ≤ resetConditionalInformation I x₀ x₁ := by
  have hmono : erasedPart I x₀ x₁ ≤ erasedPart (forgetRecord I) x₀ x₁ := by
    rw [erasedPart_eq_labelGivenRecordState,
      erasedPart_forgetRecord_eq_labelGivenState]
    apply Finset.sum_le_sum
    intro t _
    exact finiteMassUncertainty_sum_le
      (fun r b => pairJointMass I x₀ x₁ b r t)
      (fun r b => mul_nonneg (by norm_num)
        (I.nonneg (pairState x₀ x₁ b) r t))
  have hid := reset_erasure_increment_eq_conditional_information I x₀ x₁
  linarith

/-- Clearing the outcome loses no additional label information exactly in the
zero conditional-information regime. No implication about physical reset work
is asserted. -/
theorem reset_erasure_eq_iff_conditional_information_zero {X : Type*} {R T : Type}
    [Fintype R] [Fintype T] (I : StochasticInstrument X R T)
    (x₀ x₁ : X) :
    erasedPart (forgetRecord I) x₀ x₁ = erasedPart I x₀ x₁ ↔
      resetConditionalInformation I x₀ x₁ = 0 := by
  have h := reset_erasure_increment_eq_conditional_information I x₀ x₁
  constructor <;> intro he <;> linarith

/-- This deterministic instrument records the label and retains an identical
copy in its post-state. Clearing the outcome cannot erase the retained copy. -/
def readAndKeep : Instrument Bool Bool Bool := ⟨id, id⟩

/-- A repeated bit was fully read, yet erasing its recorded copy loses no
additional information about the original label. This refutes the blanket
identity that reset loss always equals the read amount. -/
theorem readAndKeep_reset_counterexample :
    readPart (deterministic readAndKeep) false true = 1 ∧
      erasedPart (deterministic readAndKeep) false true = 0 ∧
      erasedPart (forgetRecord (deterministic readAndKeep)) false true = 0 ∧
      resetConditionalInformation (deterministic readAndKeep) false true = 0 := by
  have hread : readPart (deterministic readAndKeep) false true = 1 := by
    apply side_symbol_read_part_one
    simp [readAndKeep]
  have herase : erasedPart (deterministic readAndKeep) false true = 0 := by
    apply (deterministic_erased_zero_iff_separates readAndKeep false true).2
    simp [joint, readAndKeep]
  have hweight (x : Bool) (r : Unit) (t : Bool) :
      (forgetRecord (deterministic readAndKeep)).weight x r t =
        (deterministic silentKeep).weight x r t := by
    cases r
    cases x <;> cases t <;>
      simp [forgetRecord, stateLaw, deterministic, readAndKeep, silentKeep]
  have hsame :
      erasedPart (forgetRecord (deterministic readAndKeep)) false true =
        erasedPart (deterministic silentKeep) false true := by
    unfold erasedPart
    apply Finset.sum_congr rfl
    intro rt _
    apply congrArg massUncertainty
    funext b
    simp only [pairJointMass]
    rw [hweight]
  have hforgot : erasedPart (forgetRecord (deterministic readAndKeep)) false true = 0 :=
    hsame.trans keep_erase_division.1.2
  have hcond : resetConditionalInformation (deterministic readAndKeep) false true = 0 :=
    (reset_erasure_eq_iff_conditional_information_zero
      (deterministic readAndKeep) false true).mp (hforgot.trans herase.symm)
  exact ⟨hread, herase, hforgot, hcond⟩

end OperatorKO7.Meta.BoundaryObserver.LandauerErasure
