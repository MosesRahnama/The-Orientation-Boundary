/-
The separable positivity form for successor slopes.

T-DEC-2 asks: on the class the successor decision leaves open
(`decideSuccAff = none`, so the wrapper has no `y`-square and no `y`-payload monomial and the
`y`-coefficient is at least two and at most the leading counter power), decide the successor
orientation for slopes of two or more.

This module states that question in its exact separable form. For such a wrapper the successor
gain is

`rEval R b s (β * n + a) - wLin W 0 * rEval R b s n - wEval W s 0`,

which expands monomial by monomial to `sum b ^ i * s ^ j * Q_ij(n) - C(s)` with
`C(s) = W(s, 0)` (`separableSum_eq_sepDiff`), and orientation is exactly its positivity over all
bases, payloads and counters (`orientsSucc_iff_sepDiff`). The zero-step sign condition is proved;
sufficiency of the zero-step condition together with the one-step condition is proved; the exact
residual goal is recorded, without any decidability claim, and both outcomes at slope two are
reproduced from the decision module.
-/
import OperatorKO7.Meta.Methods.OrientationClosure.PolynomialOrientationDecision

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.SeparableSlopes

open OperatorKO7.Methods.OrientationClosure.PolynomialOrientationDecision

/-- The separable difference for one successor step: the successor gain less the wrapper's
consumption of `n` and less the payload cost `W(s, 0)`. -/
def sepDiff (W : List WMono) (R : List RMono) (β a b s n : Nat) : Int :=
  (rEval R b s (β * n + a) : Int) - (wLin W 0 : Int) * (rEval R b s n : Int) -
    (wEval W s 0 : Int)

/-- Under the open-class wrapper shape the separable difference is the successor gain less the
normal-form wrapper value. -/
theorem sepDiff_eq_normal (W : List WMono) (R : List RMono) (β a b s n : Nat)
    (h1 : ¬ HasYSquare W) (h2 : ¬ HasYPayload W) :
    sepDiff W R β a b s n =
      (rEval R b s (β * n + a) : Int) - (wEval W s (rEval R b s n) : Int) := by
  unfold sepDiff
  have h := wEval_normal W h1 h2 s (rEval R b s n)
  have hcast : (wEval W s (rEval R b s n) : Int) =
      (wLin W 0 : Int) * (rEval R b s n : Int) + (wEval W s 0 : Int) := by
    rw [h]
    push_cast
    ring
  rw [hcast]
  ring

/-- The exact separable form: on the open class, orientation of the successor rule is the
positivity of the separable difference over every base, payload and counter. -/
theorem orientsSucc_iff_sepDiff (W : List WMono) (R : List RMono) (β a : Nat)
    (h1 : ¬ HasYSquare W) (h2 : ¬ HasYPayload W) :
    OrientsSucc W R β a ↔ ∀ b s n, 0 < sepDiff W R β a b s n := by
  constructor
  · intro hor b s n
    have hlt := hor b s n
    have hcast : (wEval W s (rEval R b s n) : Int) < (rEval R b s (β * n + a) : Int) := by
      exact_mod_cast hlt
    rw [sepDiff_eq_normal W R β a b s n h1 h2]
    omega
  · intro hpos b s n
    have h := hpos b s n
    rw [sepDiff_eq_normal W R β a b s n h1 h2] at h
    have h' : (wEval W s (rEval R b s n) : Int) < (rEval R b s (β * n + a) : Int) := by
      omega
    exact_mod_cast h'

/-- Zero-step sign condition: orientation forces the separable difference to be positive at
counter zero for every base and payload. -/
theorem orientsSucc_zero_step {W : List WMono} {R : List RMono} {β a : Nat}
    (hor : OrientsSucc W R β a) (h1 : ¬ HasYSquare W) (h2 : ¬ HasYPayload W) (b s : Nat) :
    0 < sepDiff W R β a b s 0 :=
  (orientsSucc_iff_sepDiff W R β a h1 h2).1 hor b s 0

/-- Sufficiency bridge: the zero-step sign condition together with the one-step sign condition
proves orientation. The step condition is the exact residual obligation at successor counters. -/
theorem orientsSucc_of_zero_and_step {W : List WMono} {R : List RMono} {β a : Nat}
    (h1 : ¬ HasYSquare W) (h2 : ¬ HasYPayload W)
    (hz : ∀ b s, 0 < sepDiff W R β a b s 0)
    (hstep : ∀ b s n, 0 < sepDiff W R β a b s n → 0 < sepDiff W R β a b s (n + 1)) :
    OrientsSucc W R β a := by
  refine (orientsSucc_iff_sepDiff W R β a h1 h2).2 fun b s n => ?_
  induction n with
  | zero => exact hz b s
  | succ n ih => exact hstep b s n ih

/-- The counter polynomial of one monomial: the successor gain less the consumed value. -/
def monomialCounterPoly (β a w k n : Nat) : Int :=
  ((β * n + a) ^ k : Int) - (w : Int) * (n ^ k : Int)

/-- The separable sum written monomial by monomial: `sum b ^ i * s ^ j * Q_ij(n) - C(s)`. -/
def separableSum (W : List WMono) (R : List RMono) (β a b s n : Nat) : Int :=
  (R.map (fun m => (m.coeff : Int) * (b ^ m.bDeg : Int) * (s ^ m.sDeg : Int) *
    monomialCounterPoly β a (wLin W 0) m.nDeg n)).sum - (wEval W s 0 : Int)

/-- The separable sum is additive over the monomial list. -/
theorem separableSum_cons (W : List WMono) (m : RMono) (R : List RMono) (β a b s n : Nat) :
    separableSum W (m :: R) β a b s n =
      (m.coeff : Int) * (b ^ m.bDeg : Int) * (s ^ m.sDeg : Int) *
        monomialCounterPoly β a (wLin W 0) m.nDeg n + separableSum W R β a b s n := by
  unfold separableSum
  simp only [List.map_cons, List.sum_cons]
  ring

/-- The monomial-by-monomial separable sum is the separable difference. -/
theorem separableSum_eq_sepDiff (W : List WMono) (R : List RMono) (β a b s n : Nat) :
    separableSum W R β a b s n = sepDiff W R β a b s n := by
  induction R with
  | nil =>
    unfold separableSum sepDiff
    simp only [List.map_nil, List.sum_nil, rEval, Nat.cast_zero, mul_zero]
    ring
  | cons m R ih =>
    rw [separableSum_cons, ih]
    simp only [sepDiff, monomialCounterPoly, rEval]
    push_cast
    ring

/-- The class the decision leaves open admits both outcomes at slope two, so the residual goal
below is genuinely two-sided. -/
theorem residual_two_sided :
    decideSuccAff residualW residualR 2 1 = none ∧ OrientsSucc residualW residualR 2 1 ∧
      decideSuccAff residualW residualRFail 2 1 = none ∧
        ¬ OrientsSucc residualW residualRFail 2 1 :=
  ⟨residual_orienting_member.1, residual_orienting_member.2,
    residual_nonorienting_member.1, residual_nonorienting_member.2⟩

/-- The exact residual goal of T-DEC-2: for a wrapper in the open class and a successor slope of
two or more, decide the separable positivity form `sum b ^ i * s ^ j * Q_ij(n) - C(s) > 0` over
all bases, payloads and counters. This is recorded, not claimed decidable. -/
def ResidualGoal (W : List WMono) (R : List RMono) (β a : Nat) : Prop :=
  ∀ b s n, 0 < sepDiff W R β a b s n

/-- The residual goal is exactly orientation on the open class. -/
theorem residualGoal_iff_orientsSucc (W : List WMono) (R : List RMono) (β a : Nat)
    (h1 : ¬ HasYSquare W) (h2 : ¬ HasYPayload W) :
    ResidualGoal W R β a ↔ OrientsSucc W R β a :=
  (orientsSucc_iff_sepDiff W R β a h1 h2).symm

end OperatorKO7.Methods.OrientationClosure.SeparableSlopes
