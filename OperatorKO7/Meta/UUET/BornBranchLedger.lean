import OperatorKO7.QEC.Dicke.BornQuotient
import OperatorKO7.Meta.BoundaryOperator.BoundaryWeightBornRatio
import OperatorKO7.Meta.QEC.BornRatioQECSpecialization

set_option autoImplicit false

/-!
# UUET Born weights over legal branches (U-05)

A UUET Born weight is assigned to a legal branch, not to its gauge orbit. This module
imports the two real Born anchors and states the UUET-facing facts:

* `uuet_born_weight_gauge_invariant`: multiplying an amplitude by a unit-modulus wrapper
 phase leaves its Born weight unchanged (the gauge phase contributes nothing to the
 weight), from `QEC.Dicke.BornQuotient.kills_gauge`;
* `uuet_born_weight_over_legal_branches`: the accepted-shot Born ratio over two
 nonnegative boundary masses with a gauge-orbit multiplicity is nonnegative and bounded
 by the ground-controlled dominant ratio, from `BoundaryWeightBornRatio`;
* `uuet_born_nonvacuous`: the QEC Method-4 empirical amplitude is exactly such a Born
 weight over legal branches (the concrete instance).

This file contains no `sorry`, no `admit`, no new `axiom`, no `native_decide`, no
`bv_decide`, no `@[csimp]`, no `unsafe`, no `partial`, and no `opaque`. Headline
declarations are `#print axioms`-checked at the bottom against the baseline whitelist.

Claim type: the gauge invariance and the ratio bounds are PROVEN-IN-LEAN (complex- and
real-analytic facts). The reading of these ratios as physical Born collapse probabilities
is STRUCTURAL MODEL, not a Lean theorem.
-/

namespace OperatorKO7.Meta.UUET

open OperatorKO7.QEC.Codes
open OperatorKO7.Meta.BoundaryOperator.BoundaryWeightBornRatio

/-- **Born weights are gauge-invariant.** Multiplying a complex amplitude by a
unit-modulus wrapper phase leaves its Born weight (squared norm) unchanged: the weight is
assigned to the legal branch, not to its gauge orbit. -/
theorem uuet_born_weight_gauge_invariant (c : ℂ) (φ : ℝ) :
    ‖c * Complex.exp (Complex.I * φ)‖ ^ 2 = ‖c‖ ^ 2 :=
  QEC.Dicke.BornQuotient.kills_gauge c φ

/-- **A UUET Born weight over legal branches** is the accepted-shot ratio over a ground
boundary mass `g`, an excited boundary mass `e`, and a gauge-orbit multiplicity `k`. It is
nonnegative and bounded above by the ground-controlled dominant ratio `2e / g`. -/
theorem uuet_born_weight_over_legal_branches (g e k : ℝ)
    (hg : 0 < g) (he : 0 ≤ e) (hk : 0 ≤ k) :
    0 ≤ bornRatio g e k ∧ bornRatio g e k ≤ 2 * e / g :=
  ⟨bornRatio_nonneg g e k hg he hk, bornRatio_dominant_bound g e k hg he hk⟩

/-- **Non-vacuity (R5).** The QEC Method-4 empirical accepted amplitude is exactly a UUET
Born weight over legal branches, with ground mass `(1-p)^n`, excited mass `(p/3)^n`, and
gauge multiplicity `3`. -/
theorem uuet_born_nonvacuous (p : ℝ) (n : ℕ) :
    KnillLaflammeEmpirical.methodFourEmpiricalAmplitude p n
      = bornRatio ((1 - p) ^ n) ((p / 3) ^ n) 3 :=
  qec_methodFour_is_bornRatio p n

#print axioms uuet_born_weight_gauge_invariant
#print axioms uuet_born_weight_over_legal_branches
#print axioms uuet_born_nonvacuous

end OperatorKO7.Meta.UUET
