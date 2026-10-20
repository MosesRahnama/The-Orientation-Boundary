import OperatorKO7.Meta.Recursor.SchemaTraceKernel

/-!
# Frame accumulation and counter descent along the recursor trace

Every recursive firing of the schema recursor removes one successor layer from the counter and
adds one frame. The frame count never decreases along the canonical trace, including its terminal
base step, and the counter of a source state is the successor of the counter of its reduct. The
payload mass of a live stage is at least the number of payload positions times the payload weight,
while the counter side has dropped by the stage index.

Relation: `SStep` on schema terms; the canonical orbit `orbitState`.
Property: per-firing exchange laws on every instance of the step rule; frame monotonicity and
counter reconstruction along the trace; the payload mass bound.
Trust: kernel only.
Scope: the schema trace kernel with leaf base and payload.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.RecursorTraceAsymmetry

open OperatorKO7.Meta.Recursor.SchemaTraceKernel

/-! ## The two rules -/

/-- **The step rule adds one frame** on every instance: the reduct carries the frames of the
source, one new frame, and the frames inside the copied payload. -/
theorem stepRule_countG (x y n : SchemaTerm) :
    countG (.G y (.F x y n)) = countG (.F x y (.S n)) + 1 + countG y := by
  simp only [countG]
  omega

/-- **The step rule removes one successor layer**: the source counter is the successor of the
reduct counter, so the source counter is reconstructed from the reduct by one application of
`S`. -/
theorem stepRule_ctr (x y n : SchemaTerm) :
    ctr (.F x y (.S n)) = ctr (.G y (.F x y n)) + 1 := by
  simp only [ctr, sHeight]

/-- **The base rule removes no frame outside the erased payload**: the reduct keeps every frame
of the base argument. -/
theorem baseRule_countG (x y : SchemaTerm) :
    countG x ≤ countG (.F x y .Z) := by
  simp only [countG]
  omega

/-- **A congruence step keeps the frame difference of the inner step.** -/
theorem congG_countG_sub (y t t' : SchemaTerm) :
    countG (.G y t') - countG (.G y t) = countG t' - countG t := by
  simp only [countG]
  omega

/-! ## The canonical trace -/

/-- **One frame per firing**: the frame count rises by one across every recursive firing of the
canonical trace. -/
theorem orbit_countG_succ (ia ib k i : Nat) (hi : i < k) :
    countG (orbitState (.base ia) (.pay ib) k (i + 1)) =
      countG (orbitState (.base ia) (.pay ib) k i) + 1 := by
  rw [countG_closed_form ia ib k (i + 1) (by omega), countG_closed_form ia ib k i (by omega)]

/-- **One successor layer per firing**: the counter of the source is the successor of the
counter of the reduct, on every recursive firing of the canonical trace. -/
theorem orbit_ctr_succ (ia ib k i : Nat) (hi : i < k) :
    ctr (orbitState (.base ia) (.pay ib) k i) =
      ctr (orbitState (.base ia) (.pay ib) k (i + 1)) + 1 := by
  rw [ctr_closed_form ia ib k i (by omega), ctr_closed_form ia ib k (i + 1) (by omega)]
  omega

/-- **Frames persist**: the frame count never decreases along the canonical trace, through the
recursive firings and through the terminal base step. -/
theorem orbit_countG_mono (ia ib k i j : Nat) (hij : i ≤ j) (hj : j ≤ k + 1) :
    countG (orbitState (.base ia) (.pay ib) k i) ≤
      countG (orbitState (.base ia) (.pay ib) k j) := by
  rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
  · rw [countG_closed_form ia ib k i (by omega), countG_closed_form ia ib k j (by omega)]
    exact hij
  · have hjeq : j = k + 1 := by omega
    subst hjeq
    rcases Nat.lt_or_ge i (k + 1) with hik | hik
    · rw [countG_closed_form ia ib k i (by omega), countG_terminal]
      omega
    · have hieq : i = k + 1 := by omega
      subst hieq
      exact le_refl _

/-- **The terminal record keeps every frame**: after `k` firings the record carries `k`
frames, and the counter of every live stage plus its frame count is the depth. -/
theorem orbit_frames_and_counter (ia ib k i : Nat) (hi : i ≤ k) :
    countG (orbitState (.base ia) (.pay ib) k (k + 1)) = k ∧
      ctr (orbitState (.base ia) (.pay ib) k i) +
        countG (orbitState (.base ia) (.pay ib) k i) = k := by
  refine ⟨countG_terminal ia ib k, ?_⟩
  rw [ctr_closed_form ia ib k i hi, countG_closed_form ia ib k i hi]
  omega

/-! ## Payload mass against counter descent -/

/-- **Payload mass grows with the stage**: the weighted size of a live stage is at least
`(i + 1)` times the payload weight, one unit per payload position. -/
theorem orbit_payload_mass_ge (alpha beta gamma phi zeta ia ib k i : Nat) (hi : i ≤ k) :
    (i + 1) * beta ≤
      wsize alpha beta gamma phi zeta (orbitState (.base ia) (.pay ib) k i) := by
  rw [wsize_closed_form alpha beta gamma phi zeta ia ib k i hi]
  nlinarith [Nat.zero_le (i * gamma), Nat.zero_le (k - i), Nat.zero_le (phi + alpha + zeta)]

/-- **The counter side drops by the stage index** while the payload positions rise by it. -/
theorem orbit_counter_drop_payload_rise (ia ib k i : Nat) (hi : i ≤ k) :
    ctr (orbitState (.base ia) (.pay ib) k i) + i = k ∧
      countPay (orbitState (.base ia) (.pay ib) k i) = i + 1 := by
  refine ⟨?_, countPay_closed_form ia ib k i hi⟩
  rw [ctr_closed_form ia ib k i hi]
  omega

/-- Control: the base rule erases the payload argument, so its frames leave with it. Frame
persistence is a statement about the frames outside the erased payload and about the canonical
trace, whose payload is a leaf. -/
theorem baseRule_erases_payload_frames :
    countG (SchemaTerm.F (.base 0) (.G (.pay 0) (.base 1)) .Z) = 1 ∧
      countG (SchemaTerm.base 0) = 0 := by
  constructor <;> rfl

end OperatorKO7.Meta.OperationalInexpressibility.RecursorTraceAsymmetry
