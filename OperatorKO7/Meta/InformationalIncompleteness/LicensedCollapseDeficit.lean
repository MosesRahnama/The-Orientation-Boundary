import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
import OperatorKO7.Meta.SafeStep.BranchEntropy
import OperatorKO7.Meta.Physics.ConfessionLandauerExact

/-!
# The unified licensed-collapse deficit (T1): both axes, one functional

The Distinction-Boundary paper reads the termination witness-channel deficit and the confluence branch
entropy as "two coordinates of one boundary" on a "common substrate ... both are finite-Shannon
quantities that an external license, not the base system, is licensed to collapse." This module makes
that one functional.

A `LicensedCollapse` over a finite verdict alphabet `V` carries a multivalued pre-license verdict
distribution (strictly positive Shannon entropy: the base system cannot determine the verdict) and a
determinate post-license verdict (a point mass: the imported license pins it). The `collapseDeficit` is
the pre-license verdict entropy, the residual the license removes. It is strictly positive before the
license and zero after (`collapseDeficit_pos`, `licensed_residual_zero`).

* **Confluence axis.** The two unjoinable branches at `eqW a a` (`void` / `integrate(merge a b)`), fair
  before the disequality guard; the guard pins the surviving `void` verdict. `collapseDeficit = log 2`,
  the one bit of `BranchEntropy.verdictBits` (`confluence_collapse_matches_branch_entropy`).
* **Termination axis.** The certificate level (direct-adequate vs needs-ascent), uncertain before the
  Arts-Giesl soundness license; the license pins the transformed-call level.

`boundary_collapse_unified` packages both as instances of the one functional: each has a strictly
positive pre-license deficit collapsing to a determinate verdict with zero residual. The *magnitudes*
can differ (the confluence load is a fixed bit, the termination carrier burden grows; that separation is
`AxisGrowthSeparation`), but the *collapse* is the shared object. The collapsed bit bears the Landauer
floor on the `BoundaryOperator` carrier (`Physics.ConfessionLandauerSplit`); this module supplies its
information-theoretic measure, the carrier supplies its thermodynamic cost.

## Claim typing (binding)
* PROVEN: every theorem below (finite-alphabet Shannon entropy over the audited `ShannonFinite`
  substrate; two concrete `Fin 2` instances).
* ANALOGY (docstring only): the identification of the two `Fin 2` alphabets with physical verdict
  channels, and the dynamical "license import" gloss; the formal content is the positive-to-zero
  collapse of the verdict entropy.

## Audit slots
- Relation: not applicable (finite information functional); the `verdictBits` collapse anchor enters only
  as a count in `confluence_collapse_matches_branch_entropy`.
- Closure: `propext`, `Classical.choice`, `Quot.sound` (or a subset); verified by `#print axioms`.
- Trust: no `sorry`/`admit`/`axiom`/`opaque`/`partial`/`unsafe`/`native_decide`/`bv_decide`/`@[csimp]`.
- Non-vacuity (R5): the two instances `confluenceCollapse`, `terminationCollapse` are concrete; each
  field is discharged.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace OperatorKO7.Meta.InformationalIncompleteness.LicensedCollapseDeficit

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite

/-- The fair binary verdict register has entropy `log 2`: one bit of pre-license verdict uncertainty. -/
theorem H_uniformFin2 : H (fun _ : Fin 2 => (1 : ℝ) / 2) = Real.log 2 := by
  unfold H
  rw [Fin.sum_univ_two]
  simp [Real.negMulLog, one_div, Real.log_inv]
  ring

/-- A licensed collapse over a finite verdict alphabet `V`: a multivalued pre-license verdict
distribution (strictly positive entropy: the base system cannot determine the verdict) together with a
determinate post-license verdict (a point mass: the imported license pins it). -/
structure LicensedCollapse (V : Type) [Fintype V] [DecidableEq V] where
  /-- The pre-license verdict distribution (before the external license is imported). -/
  preLicense : V → ℝ
  /-- The determinate verdict the imported license pins. -/
  postVerdict : V
  pre_nonneg : ∀ v, 0 ≤ preLicense v
  pre_sum : ∑ v, preLicense v = 1
  pre_multivalued : 0 < H preLicense

namespace LicensedCollapse

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The residual verdict-uncertainty the external license removes: the pre-license verdict entropy. -/
def collapseDeficit (L : LicensedCollapse V) : ℝ := H L.preLicense

/-- **The license does genuine work.** Before the license the verdict deficit is strictly positive: the
base system cannot determine the verdict on its own. -/
theorem collapseDeficit_pos (L : LicensedCollapse V) : 0 < L.collapseDeficit :=
  L.pre_multivalued

/-- **The license collapses the residual to zero.** After the license the verdict is determinate (a point
mass), so the residual verdict entropy is zero. -/
theorem licensed_residual_zero (L : LicensedCollapse V) : H (pointMass L.postVerdict) = 0 :=
  H_pointMass _

end LicensedCollapse

/-- **Confluence-axis instance.** The two unjoinable branches at the `eqW` diagonal (`void` /
`integrate(merge)`), fair before the disequality license; the guard pins the surviving `void` verdict.
`collapseDeficit = log 2`. -/
def confluenceCollapse : LicensedCollapse (Fin 2) where
  preLicense := fun _ => 1 / 2
  postVerdict := 0
  pre_nonneg := fun _ => by norm_num
  pre_sum := by rw [Fin.sum_univ_two]; norm_num
  pre_multivalued := by rw [H_uniformFin2]; exact Real.log_pos (by norm_num)

/-- **Termination-axis instance.** The certificate level (direct-adequate vs needs-ascent), uncertain
before the Arts-Giesl soundness license; the license pins the transformed-call level. `Fin 2` is the
minimal witness (the certificate channel can be larger; the magnitude separation is in
`AxisGrowthSeparation`). -/
def terminationCollapse : LicensedCollapse (Fin 2) where
  preLicense := fun _ => 1 / 2
  postVerdict := 1
  pre_nonneg := fun _ => by norm_num
  pre_sum := by rw [Fin.sum_univ_two]; norm_num
  pre_multivalued := by rw [H_uniformFin2]; exact Real.log_pos (by norm_num)

/-- **The unified boundary collapse.** Both axes are instances of one nonnegative licensed-collapse
deficit: each carries a multivalued pre-license verdict with strictly positive deficit, which the
external license collapses to a determinate verdict with zero residual. The shared object is the
licensed collapse; the magnitudes can differ (`AxisGrowthSeparation`). -/
theorem boundary_collapse_unified :
    (0 < confluenceCollapse.collapseDeficit
        ∧ H (pointMass confluenceCollapse.postVerdict) = 0)
      ∧ (0 < terminationCollapse.collapseDeficit
        ∧ H (pointMass terminationCollapse.postVerdict) = 0) :=
  ⟨⟨confluenceCollapse.collapseDeficit_pos, confluenceCollapse.licensed_residual_zero⟩,
    ⟨terminationCollapse.collapseDeficit_pos, terminationCollapse.licensed_residual_zero⟩⟩

/-- The confluence-axis collapse deficit is exactly `log 2`. -/
theorem confluence_collapseDeficit_eq_log_two :
    confluenceCollapse.collapseDeficit = Real.log 2 :=
  H_uniformFin2

/-- **The confluence collapse is one bit.** The real-valued confluence collapse deficit `log 2` is the
information-theoretic measure of the integer one-bit branch-entropy collapse
`verdictBits 2 - verdictBits 1 = 1` of `BranchEntropy`. -/
theorem confluence_collapse_matches_branch_entropy :
    OperatorKO7.Meta.SafeStep.BranchEntropy.verdictBits 2
        - OperatorKO7.Meta.SafeStep.BranchEntropy.verdictBits 1 = 1
      ∧ confluenceCollapse.collapseDeficit = Real.log 2 :=
  ⟨OperatorKO7.Meta.SafeStep.BranchEntropy.branchEntropy_collapse_one_bit,
    confluence_collapseDeficit_eq_log_two⟩

open OperatorKO7.Meta.Physics.LandauerHeatBound
open OperatorKO7.Meta.Physics.ConfessionLandauerSplit
open OperatorKO7.Meta.Physics.ConfessionLandauerExact

/-- **The collapsed verdict bit bears the Landauer floor.** The confluence collapse deficit is exactly
one bit, `log 2`, and the committed one-bit distinction record (the recursor confession event, which
commits exactly one reliable bit) has Landauer floor exactly `kB * T * log 2`: the same `log 2` factor.
The information-side collapse and the cost-side floor are one and the same bit. The physical-heat
realization stays conditional on the C1 to C6 applicability package and the heat law
(`ConfessionLandauerSplit`); this statement is about the defined floor functional and the verdict
entropy, with no physical hypothesis. -/
theorem confluence_collapse_bears_landauer_floor (kB T : ℝ) :
    confluenceCollapse.collapseDeficit = Real.log 2
      ∧ landauerLowerBound (recursorConfessionEvent 0) kB T = kB * T * Real.log 2 := by
  refine ⟨confluence_collapseDeficit_eq_log_two, ?_⟩
  rw [landauerLowerBound_eq_perBit_mul_bits, oneBit_reliableRecordBitCount, Nat.cast_one, mul_one]

#print axioms H_uniformFin2
#print axioms LicensedCollapse.collapseDeficit_pos
#print axioms LicensedCollapse.licensed_residual_zero
#print axioms boundary_collapse_unified
#print axioms confluence_collapseDeficit_eq_log_two
#print axioms confluence_collapse_matches_branch_entropy
#print axioms confluence_collapse_bears_landauer_floor

end OperatorKO7.Meta.InformationalIncompleteness.LicensedCollapseDeficit
