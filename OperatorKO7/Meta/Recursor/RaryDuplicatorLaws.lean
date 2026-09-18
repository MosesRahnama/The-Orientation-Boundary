import OperatorKO7.Meta.Recursor.RaryDuplicator
import OperatorKO7.Meta.Recursor.TraceAction
import OperatorKO7.Meta.Recursor.TraceInvariants
import OperatorKO7.Meta.Recursor.GaugeCost
import OperatorKO7.Meta.SchemaNormMismatch

/-!
# The quantitative laws at every duplication arity

The operational-inexpressibility paper states its quantitative laws for the binary duplicating
recursor, which emits one frame copy beside the recursive callee. The `r`-ary rule emits `r` frame
copies. This module carries each law to arbitrary `r`, with `r = 1` recovering the published
statement as an equality rather than a limit or an analogy.

At frame arity `r` every level of the live orbit lays down `r` wrapper cells instead of one. The
frame-action, partition, and crossover laws therefore use the binary formulas at wrapper weight
`r · w`. The payload burden does not: every live state has one active payload in addition to the
`r*i` frame payloads. Its exact formula is `conMassR`, and the difference from blind substitution
is proved below. Every quantity is connected to `rOrbit`; none is introduced only by renaming a
binary formula.

The laws carried here are the six the paper names: the trace-action closed form, the mass
partition, the crossover point, the dominance of the omitted burden over the residual descent, the
inefficiency coefficient, and the gauge cost. The gauge cost already has its own `r`-ary theorem in
`Meta/Recursor/RaryDuplicator.lean` (`L10_gauge_r`), which is re-exported here so the six sit
together.

Arity is load-bearing: at `r = 0` the rule emits no frame, so the confessed structural frame mass
is zero (`conMassCellR_zero_arity`). The live payload mass remains `(k+1)w`, because the active
callee is still present (`conMassR_zero_arity`). Duplication is exactly the additional mass term.

Relation: the `r`-ary duplicating step of `Meta/Recursor/RaryDuplicator.lean`. Closure: root.
External trust: none. Mathlib only.
-/

namespace OperatorKO7.Meta.Recursor.RaryDuplicatorLaws

open OperatorKO7.Meta.Recursor.TraceAction
open OperatorKO7.Meta.Recursor.TraceInvariants
open OperatorKO7.Meta.Recursor.RaryDuplicator
open Finset

/-! ## The `r`-ary quantities -/

/-- Confessed structural mass of one cell at frame arity `r`. -/
def conMassCellR (k w r : Nat) : Nat := conMassCell k (r * w)

/-- Trace action at frame arity `r`. -/
def traceActionR (k w cstar r : Nat) : Nat := traceAction k (r * w) cstar

/-- Crossover index at frame arity `r`. -/
def istarR (k cstar w r : Nat) : Nat := istar k cstar (r * w)

/-- Inefficiency coefficient at frame arity `r`. -/
noncomputable def inefficiencyCoefficientR (k w r : Nat) : ℝ :=
  (((2 * conMassR k w r : Nat) : ℝ) / (2 * Real.log (k + 1)))

/-- Frame mass carried by the actual live `r`-ary orbit at level `i`. -/
def raryFrameMassAt (ia ib k r i w : Nat) : Nat :=
  (countPayR (rOrbit (.base ia) (.pay ib) k r i) - 1) * w

/-- Live action at level `i`, read from the actual orbit. -/
def raryLiveActionAt (ia ib k r i w cstar : Nat) : Nat :=
  raryFrameMassAt ia ib k r i w + (k - i) + cstar

/-- The live orbit contains exactly `r*i` frame payloads at level `i`. -/
theorem raryFrameMassAt_eq (ia ib k r i w : Nat) (hi : i ≤ k) :
    raryFrameMassAt ia ib k r i w = i * (r * w) := by
  unfold raryFrameMassAt
  rw [L10_trace_law_r ia ib k r i hi]
  simp
  ring

/-- The per-level live action is the summand used by the closed form. -/
theorem raryLiveActionAt_eq (ia ib k r i w cstar : Nat) (hi : i ≤ k) :
    raryLiveActionAt ia ib k r i w cstar = i * (r * w) + (k - i) + cstar := by
  rw [raryLiveActionAt, raryFrameMassAt_eq ia ib k r i w hi]

/-- **Live bridge for Law 3.** The closed action is the sum read from `rOrbit`. -/
theorem traceActionR_eq_live_sum (ia ib k r w cstar : Nat) :
    traceActionR k w cstar r =
      ∑ i ∈ Finset.range (k + 1), raryLiveActionAt ia ib k r i w cstar := by
  rw [traceActionR]
  symm
  calc
    (∑ i ∈ Finset.range (k + 1), raryLiveActionAt ia ib k r i w cstar) =
        ∑ i ∈ Finset.range (k + 1), (i * (r * w) + (k - i) + cstar) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := by
        have hlt : i < k + 1 := Finset.mem_range.mp hi
        omega
      rw [raryLiveActionAt_eq ia ib k r i w cstar hik]
    _ = traceAction k (r * w) cstar := formula_sum_bridge k (r * w) cstar

/-- **Live bridge for structural frame mass.** -/
theorem conMassCellR_eq_live_sum (ia ib k r w : Nat) :
    conMassCellR k w r =
      ∑ i ∈ Finset.range (k + 1), raryFrameMassAt ia ib k r i w := by
  unfold conMassCellR conMassCell
  symm
  calc
    (∑ i ∈ Finset.range (k + 1), raryFrameMassAt ia ib k r i w) =
        ∑ i ∈ Finset.range (k + 1), i * (r * w) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := by
        have hlt : i < k + 1 := Finset.mem_range.mp hi
        omega
      rw [raryFrameMassAt_eq ia ib k r i w hik]
    _ = tri k * (r * w) := by
      rw [← Finset.sum_mul, sum_range_id_eq_tri]

/-- **Live bridge for payload mass.** The formula includes the single active payload present at
every state; this is the term blind weight substitution misses for `r ≠ 1`. -/
theorem conMassR_eq_live_sum (ia ib k r w : Nat) :
    conMassR k w r =
      ∑ i ∈ Finset.range (k + 1),
        countPayR (rOrbit (.base ia) (.pay ib) k r i) * w := by
  symm
  calc
    (∑ i ∈ Finset.range (k + 1),
        countPayR (rOrbit (.base ia) (.pay ib) k r i) * w) =
        ∑ i ∈ Finset.range (k + 1), (r * i + 1) * w := by
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := by
        have hlt : i < k + 1 := Finset.mem_range.mp hi
        omega
      rw [L10_trace_law_r ia ib k r i hik]
    _ = ∑ i ∈ Finset.range (k + 1), (i * (r * w) + w) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = tri k * (r * w) + (k + 1) * w := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_range_id_eq_tri]
      simp
    _ = conMassR k w r := by
      simp [conMassR]
      ring

/-- Blind substitution overcounts the one active payload by exactly `r - 1` copies per state. -/
theorem scaled_binary_payload_mass_gap (k w r : Nat) (hr : 1 ≤ r) :
    conMassPayManuscript k (r * w) =
      conMassR k w r + (r - 1) * (k + 1) * w := by
  have hre : r = (r - 1) + 1 := by omega
  rw [hre]
  simp [conMassPayManuscript, conMassR, tri]
  ring

/-- **The exact transport.** The three frame quantities are binary quantities at weight `r*w`;
the live payload mass carries the explicit active-payload correction. -/
theorem rary_is_binary_at_scaled_weight (k w cstar r : Nat) (hr : 1 ≤ r) :
    conMassCellR k w r = conMassCell k (r * w)
      ∧ traceActionR k w cstar r = traceAction k (r * w) cstar
      ∧ istarR k cstar w r = istar k cstar (r * w)
      ∧ conMassPayManuscript k (r * w) =
          conMassR k w r + (r - 1) * (k + 1) * w :=
  ⟨rfl, rfl, rfl, scaled_binary_payload_mass_gap k w r hr⟩

/-! ## Recovery at `r = 1` -/

theorem conMassCellR_one (k w : Nat) : conMassCellR k w 1 = conMassCell k w := by
  simp [conMassCellR]

theorem traceActionR_one (k w cstar : Nat) :
    traceActionR k w cstar 1 = traceAction k w cstar := by
  simp [traceActionR]

theorem istarR_one (k cstar w : Nat) : istarR k cstar w 1 = istar k cstar w := by
  simp [istarR]

theorem conMassR_one (k w : Nat) :
    conMassR k w 1 = conMassPayManuscript k w := by
  simp [conMassR, conMassPayManuscript, tri]
  ring

theorem inefficiencyCoefficientR_one (k w : Nat) :
    inefficiencyCoefficientR k w 1 =
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.inefficiencyCoefficient
        k w := by
  have hnumNat :
      2 * conMassR k w 1 = (k + 1) * (k + 2) * w := by
    rw [conMassR_one]
    unfold conMassPayManuscript
    calc
      2 * (tri (k + 1) * w) = (2 * tri (k + 1)) * w := by ring
      _ = ((k + 1) * (k + 2)) * w := by rw [two_mul_tri]
      _ = (k + 1) * (k + 2) * w := rfl
  unfold inefficiencyCoefficientR
  rw [OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.inefficiencyCoefficient_def]
  congr 1
  exact_mod_cast hnumNat

/-- Live payload mass is monotone in frame arity. -/
theorem conMassR_mono_arity (k w : Nat) {r r' : Nat} (hrr' : r ≤ r') :
    conMassR k w r ≤ conMassR k w r' := by
  have hmain := Nat.mul_le_mul_right (tri k * w) hrr'
  simpa [conMassR, Nat.mul_assoc] using
    Nat.add_le_add_right hmain ((k + 1) * w)

/-- Above the zero-length singularity, the live inefficiency coefficient is monotone in arity. -/
theorem inefficiencyCoefficientR_mono_arity (k w : Nat) {r r' : Nat}
    (hk : 1 ≤ k) (hrr' : r ≤ r') :
    inefficiencyCoefficientR k w r ≤ inefficiencyCoefficientR k w r' := by
  unfold inefficiencyCoefficientR
  apply div_le_div_of_nonneg_right
  · exact_mod_cast (Nat.mul_le_mul_left 2 (conMassR_mono_arity k w hrr'))
  · have : 0 < Real.log (k + 1) := Real.log_pos (by exact_mod_cast (show 1 < k + 1 by omega))
    positivity

/-! ## Arity is load-bearing -/

/-- At arity zero the rule emits no frame and the confessed mass vanishes, so the laws below carry
no content there. Duplication is what makes the mass positive. -/
theorem conMassCellR_zero_arity (k w : Nat) : conMassCellR k w 0 = 0 := by
  simp [conMassCellR, conMassCell]

/-- At arity zero there is no duplicated frame mass, but each of the `k+1` live states still
contains its unique active payload. -/
theorem conMassR_zero_arity (k w : Nat) : conMassR k w 0 = (k + 1) * w := by
  simp [conMassR]

/-- The live payload mass is the active-callee mass plus the duplicated-frame mass. This identity
separates the arity-zero base from the exact contribution of duplication at every arity. -/
theorem conMassR_eq_active_add_frames (k w r : Nat) :
    conMassR k w r = (k + 1) * w + r * (tri k * w) := by
  simp [conMassR]
  ring

/-- At every positive arity and positive wrapper weight the confessed mass is positive from the
first level onward. -/
theorem conMassCellR_pos (k w r : Nat) (hk : 1 ≤ k) (hw : 1 ≤ w) (hr : 1 ≤ r) :
    0 < conMassCellR k w r := by
  have htri : 0 < tri k := by
    cases k with
    | zero => omega
    | succ k => simp [tri]
  have : 0 < r * w := Nat.mul_pos hr hw
  simpa [conMassCellR, conMassCell] using Nat.mul_pos htri this

/-! ## Law 3 at arity `r`: the closed form -/

theorem L3_action_closed_r (k w cstar r : Nat) :
    2 * traceActionR k w cstar r =
      k * (k + 1) * (r * w + 1) + 2 * (k + 1) * cstar :=
  L3_action_closed k (r * w) cstar

/-! ## Law 4 at arity `r`: the mass partition -/

/-- **The mass partition holds at every frame arity.** The wrapper-weighted trace action splits
into the confessed structural mass and the counter budget, with the frame arity entering only
through the total wrapper mass `r · w` laid down per level. -/
theorem L4_partition_identity_r (k w cstar r : Nat) :
    (r * w) * (2 * traceActionR k w cstar r) =
      (r * w + 1) * (2 * conMassCellR k w r) +
        2 * (r * w) * (k + 1) * cstar :=
  L4_partition_identity k (r * w) cstar

/-! ## Law 5 at arity `r`: the crossover -/

/-- The integer envelope of the crossover fraction at frame arity `r`. -/
theorem L5_fraction_r (k cstar w r : Nat) (hw : 1 ≤ r * w) :
    k + cstar ≤ istarR k cstar w r * (r * w + 1) ∧
      istarR k cstar w r * (r * w + 1) ≤ k + cstar + r * w :=
  L5_fraction k cstar (r * w) hw

/-- **The crossover law holds at every frame arity.** Before the crossover index the wrapper mass
laid down so far is strictly below the residual descent plus the counter budget. -/
theorem L5_crossover_minimal_r (k cstar w r j : Nat) (hw : 1 ≤ r * w)
    (hj : j < istarR k cstar w r) :
    j * (r * w) < (k - j) + cstar :=
  L5_crossover_minimal k cstar (r * w) j hw hj

/-! ## Dominance at arity `r` -/

/-- **The omitted burden dominates the residual descent at every frame arity.** At and beyond the
crossover index the accumulated wrapper mass is at least the residual descent plus the counter
budget, so the confessed burden has overtaken the work the projection retains. -/
theorem rary_dominance_at_crossover (k cstar w r : Nat) (hw : 1 ≤ r * w) :
    k + cstar ≤ istarR k cstar w r * (r * w + 1) :=
  (L5_fraction_r k cstar w r hw).1

/-! ## Inefficiency at arity `r` -/

/-- **The inefficiency coefficient diverges at every positive frame arity.** -/
theorem inefficiencyCoefficientR_unbounded_atTop (w r : Nat) (hw : 1 ≤ r * w) :
    ∀ N : Nat, ∃ k : Nat, (N : ℝ) ≤ inefficiencyCoefficientR k w r := by
  have hr : 1 ≤ r := by
    cases r with
    | zero => simp at hw
    | succ r => omega
  have hw' : 1 ≤ w := by
    cases w with
    | zero => simp at hw
    | succ w => omega
  intro N
  let k := 2 * N + 1
  refine ⟨k, ?_⟩
  calc
    (N : ℝ) ≤
        OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.inefficiencyCoefficient
          k w := by
      simpa [k] using
        OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.inefficiencyCoefficient_unbounded
          w hw' N
    _ = inefficiencyCoefficientR k w 1 := (inefficiencyCoefficientR_one k w).symm
    _ ≤ inefficiencyCoefficientR k w r :=
      inefficiencyCoefficientR_mono_arity k w (by simp [k]) hr

/-! ## Gauge cost at arity `r` -/

/-- The gauge law at frame arity `r`, re-exported from `Meta/Recursor/RaryDuplicator.lean` so the
six laws sit together. -/
theorem L10_gauge_r_export (ia ib k r i : Nat) (hi : i ≤ k) :
    OperatorKO7.Meta.Recursor.RaryDuplicator.countPayR
        (OperatorKO7.Meta.Recursor.RaryDuplicator.rOrbit
          (OperatorKO7.Meta.Recursor.RaryDuplicator.RTerm.base ia)
          (OperatorKO7.Meta.Recursor.RaryDuplicator.RTerm.pay ib) k r i) = r * i + 1
      ∧ k < 2 ^ OperatorKO7.Meta.Recursor.GaugeCost.projBits k :=
  OperatorKO7.Meta.Recursor.RaryDuplicator.L10_gauge_r ia ib k r i hi

/-! ## One universal package -/

/-- All six quantitative laws, their three live-orbit bridges, and the gauge theorem at one
arbitrary frame arity. Positivity-dependent clauses are implications, so the package itself is
unconditional in `r` and records the degenerate `r = 0` boundary without hiding it. -/
structure RaryQuantitativeLawPackage (ia ib w cstar r : Nat) : Prop where
  actionLive : ∀ k,
    traceActionR k w cstar r =
      ∑ i ∈ Finset.range (k + 1), raryLiveActionAt ia ib k r i w cstar
  frameMassLive : ∀ k,
    conMassCellR k w r =
      ∑ i ∈ Finset.range (k + 1), raryFrameMassAt ia ib k r i w
  payloadMassLive : ∀ k,
    conMassR k w r =
      ∑ i ∈ Finset.range (k + 1),
        countPayR (rOrbit (.base ia) (.pay ib) k r i) * w
  actionClosed : ∀ k,
    2 * traceActionR k w cstar r =
      k * (k + 1) * (r * w + 1) + 2 * (k + 1) * cstar
  partition : ∀ k,
    (r * w) * (2 * traceActionR k w cstar r) =
      (r * w + 1) * (2 * conMassCellR k w r) +
        2 * (r * w) * (k + 1) * cstar
  crossoverFraction : ∀ k, 1 ≤ r * w →
    k + cstar ≤ istarR k cstar w r * (r * w + 1) ∧
      istarR k cstar w r * (r * w + 1) ≤ k + cstar + r * w
  crossoverMinimal : ∀ k j, 1 ≤ r * w → j < istarR k cstar w r →
    j * (r * w) < (k - j) + cstar
  dominanceAtCrossover : ∀ k, 1 ≤ r * w →
    k + cstar ≤ istarR k cstar w r * (r * w + 1)
  inefficiencyUnbounded : 1 ≤ r * w →
    ∀ N : Nat, ∃ k : Nat, (N : ℝ) ≤ inefficiencyCoefficientR k w r
  gauge : ∀ k i, i ≤ k →
    countPayR (rOrbit (.base ia) (.pay ib) k r i) = r * i + 1 ∧
      k < 2 ^ OperatorKO7.Meta.Recursor.GaugeCost.projBits k

/-- **Universal r-ary crown.** The complete quantitative package is inhabited for every natural
frame arity, including the explicit zero-arity boundary. -/
theorem rary_quantitative_laws_all_arities (ia ib w cstar r : Nat) :
    RaryQuantitativeLawPackage ia ib w cstar r where
  actionLive := fun k => traceActionR_eq_live_sum ia ib k r w cstar
  frameMassLive := fun k => conMassCellR_eq_live_sum ia ib k r w
  payloadMassLive := fun k => conMassR_eq_live_sum ia ib k r w
  actionClosed := fun k => L3_action_closed_r k w cstar r
  partition := fun k => L4_partition_identity_r k w cstar r
  crossoverFraction := fun k hw => L5_fraction_r k cstar w r hw
  crossoverMinimal := fun k j hw hj => L5_crossover_minimal_r k cstar w r j hw hj
  dominanceAtCrossover := fun k hw => rary_dominance_at_crossover k cstar w r hw
  inefficiencyUnbounded := inefficiencyCoefficientR_unbounded_atTop w r
  gauge := fun k i hi => L10_gauge_r_export ia ib k r i hi

/-! ## The six laws recover the published statements at `r = 1` -/

/-- **Recovery.** At `r = 1` every `r`-ary law is the published binary law, as an equality of the
quantities and not as a limit. -/
theorem rary_laws_recover_binary (k w cstar : Nat) :
    conMassCellR k w 1 = conMassCell k w
      ∧ traceActionR k w cstar 1 = traceAction k w cstar
      ∧ istarR k cstar w 1 = istar k cstar w
      ∧ inefficiencyCoefficientR k w 1 =
          OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.inefficiencyCoefficient
            k w
      ∧ conMassR k w 1 = conMassPayManuscript k w
      ∧ (2 * traceActionR k w cstar 1 = k * (k + 1) * (w + 1) + 2 * (k + 1) * cstar)
      ∧ (w * (2 * traceActionR k w cstar 1) =
          (w + 1) * (2 * conMassCellR k w 1) + 2 * w * (k + 1) * cstar) := by
  refine ⟨conMassCellR_one k w, traceActionR_one k w cstar, istarR_one k cstar w,
    inefficiencyCoefficientR_one k w, conMassR_one k w, ?_, ?_⟩
  · simpa using L3_action_closed_r k w cstar 1
  · simpa using L4_partition_identity_r k w cstar 1

end OperatorKO7.Meta.Recursor.RaryDuplicatorLaws
