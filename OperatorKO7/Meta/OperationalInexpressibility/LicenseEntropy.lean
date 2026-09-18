import OperatorKO7.Meta.PolyInterpretation_Family
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchangeGeneral

/-!
# Construction-choice Hartley complexity and confession-role Shannon complexity

Relation: full KO7 `Step` on the construction side; the `r`-ary role channel on the
confession side.
Closure: root.
Strategy: root-only on the construction side; not applicable on the role-information side.
Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`.

This module deliberately separates two quantities that were previously given one overloaded
"license entropy" name. On the construction (W1) side, the finite-choice Hartley complexity
of selecting among `N` distinct orienters is `log₂ N`; `w1_orienting_family` makes these
finite support sizes unbounded. On the confession (W2) side, the active-versus-frame flag
carries a Shannon binary entropy `h₂(1/(r+1))`, exactly one bit only at `r = 1` and at most
one bit for every arity. For `r > 1`, that flag is not the full role information: the
unresolved frame index contributes the residual `(r/(r+1)) log₂ r`, and adding the two recovers
the full role Hartley value `log₂(r+1)`. That last statement is an identity between the
quantities defined here; the derivation of both terms from the actual dependency-pair kernel is
`rary_dp_exchange` in `Meta/BoundaryGeneral/OverproductionGapRoleExchangeGeneral.lean`.

These are heterogeneous complexity coordinates, not one intrinsic scalar whose numerical
comparison has theorem-independent meaning. Raw certificates may be non-unique on both
sides; the statements here concern finite construction-choice support and the explicit role
law only.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.LicenseEntropy

open OperatorKO7 Trace
open OperatorKO7.PolyInterpretation.Family
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchangeGeneral

noncomputable section

/-- Hartley complexity, in bits, of a finite support of `N` candidate W1 construction
witnesses. This is a support-cardinality quantity, not a Shannon entropy on the infinite
family and not a certificate serialization length. -/
def w1FiniteChoiceHartley (N : Nat) : ℝ := Real.logb 2 (N : ℝ)

/-- Shannon binary entropy, in bits, of the active-versus-frame flag among `r + 1`
occurrences. It does not resolve the frame index when `r > 1`. -/
def w2ActiveFlagShannon (r : Nat) : ℝ := activeShareEntropyBits r

/-- Full role support Hartley complexity for one active role and `r` distinct frame roles. -/
def w2FullRoleHartley (r : Nat) : ℝ := Real.logb 2 (r + 1 : Nat)

/-- Residual Shannon information, in bits, of the frame index after the active/frame flag:
with probability `r/(r+1)` the occurrence is a frame, and the conditional frame law is
uniform over `r` roles. -/
def w2ResidualFrameShannon (r : Nat) : ℝ :=
  ((r : ℝ) / (r + 1 : Nat)) * Real.logb 2 (r : ℝ)

/-- The finite-choice Hartley complexity of `2^k` candidates is `k` bits. -/
theorem w1FiniteChoiceHartley_two_pow (k : Nat) : w1FiniteChoiceHartley (2 ^ k) = k := by
  unfold w1FiniteChoiceHartley
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]

/-- **W1 finite-choice Hartley complexity is unbounded**, and every requested lower
bound is exceeded by an injective finite family of orienters of full `Step`. -/
theorem w1_finite_choice_hartley_unbounded (B : ℝ) :
    ∃ N : Nat, B < w1FiniteChoiceHartley N ∧
      ∃ f : Fin N → (Trace → Nat),
        Function.Injective f ∧
          ∀ i : Fin N, ∀ {x y : Trace}, Step x y → f i y < f i x := by
  refine ⟨2 ^ (Nat.ceil B + 1), ?_, w1_orienting_family _⟩
  rw [w1FiniteChoiceHartley_two_pow]
  have h1 : B ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B
  have h2 : ((Nat.ceil B + 1 : Nat) : ℝ) = (Nat.ceil B : ℝ) + 1 := by push_cast; ring
  rw [h2]
  linarith

/-- The active/frame flag has exactly one bit of Shannon entropy at the binary recursor. -/
theorem w2_active_flag_shannon_one_at_binary : w2ActiveFlagShannon 1 = 1 := by
  unfold w2ActiveFlagShannon
  rw [activeShareEntropyBits_closed (le_refl 1)]
  norm_num [Real.logb_self_eq_one]

/-- The active/frame flag Shannon entropy never exceeds one bit at any arity. -/
theorem w2_active_flag_shannon_le_one (r : Nat) : w2ActiveFlagShannon r ≤ 1 := by
  unfold w2ActiveFlagShannon activeShareEntropyBits
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_one hlog]
  exact Real.binEntropy_le_log_two

/-- The active/frame flag Shannon entropy is nonnegative at every arity. -/
theorem w2_active_flag_shannon_nonneg (r : Nat) : 0 ≤ w2ActiveFlagShannon r := by
  unfold w2ActiveFlagShannon activeShareEntropyBits
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  apply div_nonneg _ hlog.le
  apply Real.binEntropy_nonneg
  · positivity
  · have hrNat : 1 ≤ r + 1 := Nat.succ_le_succ (Nat.zero_le r)
    have hr' : (1 : ℝ) ≤ (r + 1 : Nat) := by exact_mod_cast hrNat
    rw [div_le_one (by positivity)]
    exact hr'

/-- **Role-information decomposition.** At every positive arity the full role Hartley support
splits into the active/frame Shannon bit plus the residual frame-index term.

Scope: this is an arithmetic identity between the three quantities defined above.
`w2ResidualFrameShannon` is introduced by its closed formula, which is the conditional entropy
of the uniform law on the `r` frame roles, so the identity records the decomposition instead of
deriving the residual from an evidence channel. The channel-level derivation, where both terms
are read off the actual dependency-pair kernel, is `dpChannel_deficitBits_eq_activeShareEntropy`,
`dpChannel_gap`, and `rary_dp_exchange` in
`Meta/BoundaryGeneral/OverproductionGapRoleExchangeGeneral.lean`. -/
theorem w2_role_information_chain_rule {r : Nat} (hr : 1 ≤ r) :
    w2FullRoleHartley r = w2ActiveFlagShannon r + w2ResidualFrameShannon r := by
  unfold w2FullRoleHartley w2ActiveFlagShannon w2ResidualFrameShannon
  rw [activeShareEntropyBits_closed hr]
  ring

/-- With no frame roles, each role-information quantity is zero. -/
theorem w2_role_information_zero :
    w2FullRoleHartley 0 = 0 ∧ w2ActiveFlagShannon 0 = 0 ∧
      w2ResidualFrameShannon 0 = 0 := by
  norm_num [w2FullRoleHartley, w2ActiveFlagShannon, activeShareEntropyBits,
    w2ResidualFrameShannon, Real.binEntropy]

/-- Role information decomposes at every natural arity, including zero. -/
theorem w2_role_information_chain_rule_all_nat (r : Nat) :
    w2FullRoleHartley r = w2ActiveFlagShannon r + w2ResidualFrameShannon r := by
  cases r with
  | zero => rw [w2_role_information_zero.1, w2_role_information_zero.2.1,
      w2_role_information_zero.2.2, add_zero]
  | succ r => exact w2_role_information_chain_rule (Nat.succ_le_succ (Nat.zero_le r))

/-- With one frame, there is no residual frame-index uncertainty. -/
theorem w2_residual_frame_shannon_zero_at_binary : w2ResidualFrameShannon 1 = 0 := by
  unfold w2ResidualFrameShannon
  norm_num [Real.logb_self_eq_one]

/-- With one frame, the full role Hartley support is exactly one bit. -/
theorem w2_full_role_hartley_one_at_binary : w2FullRoleHartley 1 = 1 := by
  unfold w2FullRoleHartley
  norm_num [Real.logb_self_eq_one]

/-- **Construction-choice versus confession-role profile.** W1 finite-support Hartley
complexity is unbounded. W2 active/frame Shannon complexity is at most one bit and equals
one at binary arity, while the full role information is recovered only after adding the
residual frame-index term. This theorem packages heterogeneous coordinates without asserting
that they are one intrinsic entropy. -/
theorem construction_choice_vs_confession_role_profile :
    (∀ B : ℝ, ∃ N : Nat, B < w1FiniteChoiceHartley N ∧
      ∃ f : Fin N → (Trace → Nat),
        Function.Injective f ∧
          ∀ i : Fin N, ∀ {x y : Trace}, Step x y → f i y < f i x) ∧
    (∀ r : Nat, w2ActiveFlagShannon r ≤ 1) ∧
    w2ActiveFlagShannon 1 = 1 ∧
    (∀ r : Nat, 1 ≤ r →
      w2FullRoleHartley r = w2ActiveFlagShannon r + w2ResidualFrameShannon r) ∧
    w2ResidualFrameShannon 1 = 0 :=
  ⟨w1_finite_choice_hartley_unbounded,
    w2_active_flag_shannon_le_one,
    w2_active_flag_shannon_one_at_binary,
    fun _ hr => w2_role_information_chain_rule hr,
    w2_residual_frame_shannon_zero_at_binary⟩

end

end OperatorKO7.Meta.OperationalInexpressibility.LicenseEntropy
