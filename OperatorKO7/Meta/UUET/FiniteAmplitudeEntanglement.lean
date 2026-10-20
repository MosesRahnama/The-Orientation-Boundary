import OperatorKO7.Meta.UUET.EntanglementMagnitude

set_option autoImplicit false

/-!
# UUET finite two-branch amplitude entanglement carrier (U-58)

This refines the boolean/product `EntanglementMagnitude` (U-57) into a richer
finite carrier: a *normalized two-branch weight* with a continuous amplitude
entanglement scalar.

`TwoBranchWeight` is a real branch weight `p` with `0 <= p <= 1` (the
complementary branch carries `1 - p`). `amplitudeEntanglement w := p * (1 - p)`
is a concurrence-like nonnegative scalar: maximal `1/4` at the balanced state
`p = 1/2`, and zero exactly when one branch is certain (`p = 0` or `p = 1`), i.e.
when the state is separable / a committed classical record.

What is proven: normalization, nonnegativity, the AM-GM upper bound `<= 1/4`, the
separability characterization (`= 0 iff one branch certain`), the balanced
canonical nonvacuity witness, the terminal-record / committed-branch collapse, a
Born-legality alignment (a collapsed branch carries the nonnegative U-05 Born
weight), and the recovery of the older U-57 boolean product proxy as a coarse
shadow (both are premeasurement-positive and both collapse on commitment).

Scope and honesty: FINITE STRUCTURAL Lean over real branch weights. This is NOT a
physical entanglement/concurrence theorem (no Hilbert space, no density matrix);
the reading of `p*(1-p)` as physical concurrence is a structural model, not a Lean
claim. No `sorry`, `admit`, new `axiom`, `native_decide`, `bv_decide`, `@[csimp]`,
`unsafe`, `partial`, or `opaque`. Headline declarations are `#print axioms`-checked
against the baseline whitelist `{propext, Classical.choice, Quot.sound}`.
-/

namespace OperatorKO7.Meta.UUET

open OperatorKO7.Meta.BoundaryOperator.BoundaryWeightBornRatio

noncomputable section

/-- A normalized finite two-branch weight: branch 0 carries `p` with
`0 <= p <= 1`; branch 1 carries `1 - p`. -/
structure TwoBranchWeight where
  p : ℝ
  nonneg : 0 ≤ p
  le_one : p ≤ 1

namespace TwoBranchWeight

/-- The complementary branch weight `1 - p`. -/
def q (w : TwoBranchWeight) : ℝ := 1 - w.p

theorem q_nonneg (w : TwoBranchWeight) : 0 ≤ w.q := by
  unfold q; linarith [w.le_one]

theorem q_le_one (w : TwoBranchWeight) : w.q ≤ 1 := by
  unfold q; linarith [w.nonneg]

/-- The two branch weights are normalized. -/
theorem normalized (w : TwoBranchWeight) : w.p + w.q = 1 := by
  unfold q; ring

end TwoBranchWeight

/-- Finite amplitude-entanglement scalar of a two-branch weight: `p * (1 - p)`.
Concurrence-like, maximal at the balanced state, zero when one branch is certain.
A finite structural proxy, NOT a physical entanglement measure. -/
def amplitudeEntanglement (w : TwoBranchWeight) : ℝ := w.p * w.q

theorem amplitudeEntanglement_nonneg (w : TwoBranchWeight) :
    0 ≤ amplitudeEntanglement w :=
  mul_nonneg w.nonneg w.q_nonneg

/-- **Separability characterization.** The amplitude entanglement is zero iff one
branch is certain (`p = 0` or `p = 1`): a separable / committed classical record. -/
theorem amplitudeEntanglement_eq_zero_iff (w : TwoBranchWeight) :
    amplitudeEntanglement w = 0 ↔ w.p = 0 ∨ w.p = 1 := by
  unfold amplitudeEntanglement TwoBranchWeight.q
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [h]; ring)

/-- **AM-GM upper bound.** The amplitude entanglement never exceeds `1/4`. -/
theorem amplitudeEntanglement_le_quarter (w : TwoBranchWeight) :
    amplitudeEntanglement w ≤ 1 / 4 := by
  unfold amplitudeEntanglement TwoBranchWeight.q
  nlinarith [sq_nonneg (w.p - 1 / 2)]

/-- The balanced two-branch state `p = 1/2`, the maximally-entangled canonical
witness. -/
def balancedBranch : TwoBranchWeight where
  p := 1 / 2
  nonneg := by norm_num
  le_one := by norm_num

theorem balancedBranch_amplitude : amplitudeEntanglement balancedBranch = 1 / 4 := by
  unfold amplitudeEntanglement balancedBranch TwoBranchWeight.q
  norm_num

/-- **Canonical nonvacuity witness.** The balanced state has strictly positive
amplitude entanglement. -/
theorem balancedBranch_pos : 0 < amplitudeEntanglement balancedBranch := by
  rw [balancedBranch_amplitude]; norm_num

/-- A certain (committed) two-branch state `p = 1`: one branch carries all weight. -/
def collapsedBranch : TwoBranchWeight where
  p := 1
  nonneg := by norm_num
  le_one := le_refl 1

/-- **Terminal-record / committed-branch collapse.** A certain branch (committed
classical record) has zero amplitude entanglement (separable). -/
theorem collapsedBranch_amplitude : amplitudeEntanglement collapsedBranch = 0 := by
  unfold amplitudeEntanglement collapsedBranch TwoBranchWeight.q
  norm_num

/-- **Born-legality alignment.** A collapsed (certain) two-branch outcome has zero
amplitude entanglement and carries the nonnegative gauge-invariant accepted-shot
Born weight of U-05: a separable committed record with a legal weight. -/
theorem amplitudeEntanglement_born_legality
    (w : TwoBranchWeight) (hcollapse : w.p = 0 ∨ w.p = 1)
    (g e k : ℝ) (hg : 0 < g) (he : 0 ≤ e) (hk : 0 ≤ k) :
    amplitudeEntanglement w = 0 ∧ 0 ≤ bornRatio g e k :=
  ⟨(amplitudeEntanglement_eq_zero_iff w).2 hcollapse,
    (uuet_born_weight_over_legal_branches g e k hg he hk).1⟩

/-- **Recovery of the U-57 product proxy as a coarse shadow.** The two qualitative
facts of the boolean product proxy `entanglementMagnitude` (premeasurement-positive,
collapse to zero when an axis is licensed) are reproduced by this finite amplitude
carrier (positive at the balanced state, zero at a certain branch). The new carrier
refines the old; the old is its coarse boolean shadow. -/
theorem finiteAmplitude_recovers_product_shadow :
    0 < amplitudeEntanglement balancedBranch
      ∧ amplitudeEntanglement collapsedBranch = 0
      ∧ 0 < entanglementMagnitude false false
      ∧ entanglementMagnitude true false = 0 :=
  ⟨balancedBranch_pos, collapsedBranch_amplitude,
    entanglementMagnitude_premeasurement_pos,
    (entanglementMagnitude_zero_iff_some_licensed true false).2 (Or.inl rfl)⟩

/-- Non-vacuity: balanced amplitude `1/4`, strictly positive, collapsed amplitude
`0`, the global `<= 1/4` bound, and global nonnegativity. -/
theorem finiteAmplitudeEntanglement_nonvacuous :
    amplitudeEntanglement balancedBranch = 1 / 4
      ∧ 0 < amplitudeEntanglement balancedBranch
      ∧ amplitudeEntanglement collapsedBranch = 0
      ∧ (∀ w : TwoBranchWeight, amplitudeEntanglement w ≤ 1 / 4)
      ∧ (∀ w : TwoBranchWeight, 0 ≤ amplitudeEntanglement w) :=
  ⟨balancedBranch_amplitude, balancedBranch_pos, collapsedBranch_amplitude,
    amplitudeEntanglement_le_quarter, amplitudeEntanglement_nonneg⟩

#print axioms amplitudeEntanglement_nonneg
#print axioms amplitudeEntanglement_eq_zero_iff
#print axioms amplitudeEntanglement_le_quarter
#print axioms balancedBranch_pos
#print axioms collapsedBranch_amplitude
#print axioms amplitudeEntanglement_born_legality
#print axioms finiteAmplitude_recovers_product_shadow
#print axioms finiteAmplitudeEntanglement_nonvacuous

end

end OperatorKO7.Meta.UUET
