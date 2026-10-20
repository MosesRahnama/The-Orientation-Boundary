import OperatorKO7.Meta.UUET.PreEntanglement

set_option autoImplicit false

/-!
# UUET pre-entanglement CHSH scope wall (U-PRE-CHSH)

`PreEntanglement.lean` mechanizes the common-cause (shared committed record)
sector and its docstring promises "no Bell-violation claim". This module turns
that honesty sentence into a theorem: every deterministic local strategy over
the shared record satisfies the CHSH bound `|S| <= 2`, so the Phase-1 carrier
provably cannot express a Bell violation. The quantum Tsirelson value lives in
a different lane (`QMLaw_TsirelsonLiebRobinson`) and is NOT claimed here.

Proven here:

* `chsh_pointwise`: for a fixed record value, the four-term signed combination
  of products of local ±1 outputs is exactly `+2` or `-2` (the 16-case
  Boolean fact);
* `chsh_classical_bound`: for every strategy pair and every record weight in
  `[0,1]`, `|CHSH| <= 2`;
* `chsh_below_tsirelson_threshold`: the classical value stays strictly below
  the Tsirelson threshold `2 sqrt 2 > 14/5` (honesty direction only);
* `preEntanglementCHSH_nonvacuous`: the all-`+1` strategy at weight `1/2`
  attains exactly `2`, so the bound is tight and non-vacuous.

Claim type: PROVEN-IN-LEAN for the finite rational local-hidden-record
algebra. This is the classical (local realist) side of the fence; it makes no
statement about quantum correlations.
-/

namespace OperatorKO7.Meta.UUET.PreEntanglementCHSH

/-- The ±1 value of a Boolean output. -/
def sign (b : Bool) : ℤ := if b then 1 else -1

/-- Pointwise correlator at a fixed record value `r`: the signed
CHSH combination of the four setting products, over ℚ. Arguments are the
local outputs `A(setting, r)` and `B(setting, r)` at the two settings. -/
def pointwise (a0 a1 b0 b1 : Bool) : ℚ :=
  ((sign a0 * sign b0 + sign a0 * sign b1 + sign a1 * sign b0
      - sign a1 * sign b1 : ℤ) : ℚ)

/-- A deterministic local strategy: (setting, shared record) -> output. -/
abbrev Strategy := Bool → Bool → Bool

/-- Correlator at settings `(x, y)` for strategies `A`, `B` and record weight
`w` (record true with weight `w`), over ℚ. -/
def correlator (A B : Strategy) (w : ℚ) (x y : Bool) : ℚ :=
  w * ((sign (A x true) * sign (B y true) : ℤ) : ℚ)
    + (1 - w) * ((sign (A x false) * sign (B y false) : ℤ) : ℚ)

/-- The CHSH functional `E00 + E01 + E10 - E11`. -/
def chsh (A B : Strategy) (w : ℚ) : ℚ :=
  correlator A B w false false + correlator A B w false true
    + correlator A B w true false - correlator A B w true true

/-- Pointwise CHSH identity: the fixed-record combination is exactly ±2. -/
theorem chsh_pointwise (a0 a1 b0 b1 : Bool) :
    pointwise a0 a1 b0 b1 = 2 ∨ pointwise a0 a1 b0 b1 = -2 := by
  unfold pointwise sign
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> norm_num

/-- `|pointwise| <= 2` for every strategy value assignment. -/
theorem abs_pointwise_le_two (a0 a1 b0 b1 : Bool) :
    |pointwise a0 a1 b0 b1| ≤ 2 := by
  rcases chsh_pointwise a0 a1 b0 b1 with h | h <;> rw [h] <;> norm_num

/-- CHSH factors as the record-weighted convex combination of the two
pointwise correlators. -/
theorem chsh_eq_weighted (A B : Strategy) (w : ℚ) :
    chsh A B w
      = w * pointwise (A false true) (A true true) (B false true) (B true true)
        + (1 - w) * pointwise (A false false) (A true false) (B false false) (B true false) := by
  unfold chsh correlator pointwise
  push_cast
  ring

/-- The classical CHSH bound: for every strategy pair and every record weight
in `[0,1]`, `|CHSH| <= 2`. Local hidden records cannot exceed the classical
value. -/
theorem chsh_classical_bound (A B : Strategy) (w : ℚ)
    (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    |chsh A B w| ≤ 2 := by
  rw [chsh_eq_weighted]
  set P := pointwise (A false true) (A true true) (B false true) (B true true) with hP
  set Q := pointwise (A false false) (A true false) (B false false) (B true false) with hQ
  have hPb := abs_le.1 (abs_pointwise_le_two (A false true) (A true true) (B false true) (B true true))
  have hQb := abs_le.1 (abs_pointwise_le_two (A false false) (A true false) (B false false) (B true false))
  rw [← hP] at hPb
  rw [← hQ] at hQb
  rw [abs_le]
  constructor <;> nlinarith [hPb.1, hPb.2, hQb.1, hQb.2, h0, h1]

/-- Honesty direction: the classical carrier stays strictly below the
Tsirelson threshold `2 sqrt 2` (finite surrogate `14/5 < 2 sqrt 2`). No
quantum value is claimed proven here. -/
theorem chsh_below_tsirelson_threshold (A B : Strategy) (w : ℚ)
    (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    chsh A B w < 14 / 5 := by
  have h := abs_le.1 (chsh_classical_bound A B w h0 h1)
  linarith [h.2]

/-- Non-vacuity: the all-`true` strategy pair at weight `1/2` attains CHSH `= 2`
exactly, so the classical bound is tight. -/
theorem preEntanglementCHSH_nonvacuous :
    chsh (fun _ _ => true) (fun _ _ => true) (1 / 2) = 2 := by
  unfold chsh correlator sign
  norm_num

#print axioms chsh_pointwise
#print axioms abs_pointwise_le_two
#print axioms chsh_eq_weighted
#print axioms chsh_classical_bound
#print axioms chsh_below_tsirelson_threshold
#print axioms preEntanglementCHSH_nonvacuous

end OperatorKO7.Meta.UUET.PreEntanglementCHSH
