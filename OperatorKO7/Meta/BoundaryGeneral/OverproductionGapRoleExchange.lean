import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapDPExchange
import OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy

/-!
# The m-ary operational-role exchange

The binary DP exchange lives on `Fork3` with a two-letter role alphabet. This
module supplies the star carrier with `m` terminals and the same accounting on
the role alphabet `Fin m`: a value-blind channel leaves gap `log₂ m`; the
resolving role channel supplies `log₂ m` bits and closes the gap; the exchange
is `Ω_value − Ω_role = log₂ m`. The case `m = 0` is compiled as a non-example
(the source is itself the unique terminal; there is no role alphabet).

This layer is the finite-alphabet generalization of `one_bit_dp_exchange`. It
does not invent a new deficit; it instantiates `overproductionGap` on the star.

Trust: kernel-only. No `sorry`/`admit`/`axiom`/`native_decide`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchange

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
  (terminalSupport terminalMultiplicity terminalHartleyEntropy mem_terminalSupport
    reach_refl reach_step)

private abbrev QNormalForm {T : Type} (R : T → T → Prop) (x : T) : Prop :=
  OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm R x

private abbrev QReach {T : Type} (R : T → T → Prop) (x y : T) : Prop :=
  OperatorKO7.Meta.DistinctionBoundary.Quantitative.Reach R x y

noncomputable section

/-- Source `0` steps to each of the `m` nonzero cells of `Fin (m + 1)`. -/
def starStep (m : ℕ) : Fin (m + 1) → Fin (m + 1) → Prop :=
  fun s t => s = 0 ∧ t ≠ 0

/-- A nonzero cell is a terminal: it has no outgoing star step. -/
theorem star_terminal_normal {m : ℕ} {t : Fin (m + 1)} (ht : t ≠ 0) :
    QNormalForm (starStep m) t := by
  intro u hstep
  exact ht hstep.1

/-- The source is reachable from itself. -/
theorem star_reach_source (m : ℕ) : QReach (starStep m) 0 0 :=
  reach_refl 0

/-- Every terminal is a one-step reduct of the source. -/
theorem star_reach_terminal {m : ℕ} {t : Fin (m + 1)} (ht : t ≠ 0) :
    QReach (starStep m) 0 t :=
  reach_step ⟨rfl, ht⟩

/-- Under `1 ≤ m` the source is not a normal form: it steps to cell `1`. -/
theorem star_source_not_normal {m : ℕ} (hm : 1 ≤ m) :
    ¬ QNormalForm (starStep m) 0 := by
  intro hnf
  let t : Fin (m + 1) := ⟨1, Nat.lt_succ_of_le hm⟩
  have ht : t ≠ 0 := by
    intro h
    have hval := congrArg Fin.val h
    simp [t] at hval
  exact hnf t ⟨rfl, ht⟩

/-- Reachable normal forms of the star are exactly the nonzero cells. -/
theorem star_terminalSupport {m : ℕ} (hm : 1 ≤ m) :
    terminalSupport (starStep m) 0 = Finset.univ.erase 0 := by
  ext x
  simp [mem_terminalSupport, Finset.mem_erase]
  constructor
  · intro ⟨_, hnf⟩
    intro hx0
    subst hx0
    exact star_source_not_normal hm hnf
  · intro hne
    exact ⟨star_reach_terminal hne, star_terminal_normal hne⟩

/-- Terminal support of the star has size `m`. -/
theorem star_terminalMultiplicity {m : ℕ} (hm : 1 ≤ m) :
    terminalMultiplicity (starStep m) 0 = m := by
  unfold terminalMultiplicity
  rw [star_terminalSupport hm, Finset.card_erase_of_mem (Finset.mem_univ 0),
    Finset.card_univ, Fintype.card_fin]
  exact Nat.add_sub_cancel m 1

/-- Hartley entropy of the star is `log₂ m`. -/
theorem star_terminalHartleyEntropy {m : ℕ} (hm : 1 ≤ m) :
    terminalHartleyEntropy (starStep m) 0 = Real.logb 2 (m : ℝ) := by
  unfold terminalHartleyEntropy
  rw [star_terminalMultiplicity hm]

/-- `m = 0` non-example: the unique cell is a terminal, multiplicity one. -/
theorem star_zero_source_normal : QNormalForm (starStep 0) 0 := by
  intro t hstep
  have ht : t = 0 := Fin.ext (Nat.lt_one_iff.mp t.isLt)
  exact hstep.2 ht

/-- `m = 0` non-example: the source is the unique reachable normal form. -/
theorem star_zero_terminalMultiplicity :
    terminalMultiplicity (starStep 0) 0 = 1 := by
  unfold terminalMultiplicity
  apply Finset.card_eq_one.mpr
  refine ⟨0, ?_⟩
  ext x
  simp [mem_terminalSupport]
  constructor
  · intro
    exact Fin.ext (Nat.lt_one_iff.mp x.isLt)
  · intro hx
    have : x = 0 := by simpa using hx
    subst this
    exact ⟨star_reach_source 0, star_zero_source_normal⟩

/-- Uniform weights on the `m`-letter role alphabet. -/
def uniformRoleWeights (m : ℕ) : Fin 1 → Fin m → ℝ :=
  fun _ _ => (1 : ℝ) / m

/-- Uniform role weights sum to one when `1 ≤ m`. -/
theorem uniformRoleWeights_sum_one {m : ℕ} (hm : 1 ≤ m) :
    ∀ w, ∑ c : Fin m, uniformRoleWeights m w c = 1 := by
  intro w
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (Nat.succ_le_iff.mp hm)
  simp only [uniformRoleWeights]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ : Finset (Fin m)).card : ℝ) = m := by
    simp [Finset.card_univ, Fintype.card_fin]
  rw [hcard]
  field_simp [hmpos.ne']

/-- **The echo channel on `Fin m`.** Constant across roles. -/
def roleEcho (m : ℕ) : Fin 1 → Fin m → Fin m → ℝ :=
  fun _ _ _ => (1 : ℝ) / m

/-- **The resolving channel on `Fin m`.** Role `i` determines terminal `i`. -/
def roleResolving (m : ℕ) : Fin 1 → Fin m → Fin m → ℝ :=
  fun _ c => pointMass c

/-- A value-blind channel on the star leaves gap `log₂ m`. -/
theorem roleBlind_gap_log {m : ℕ} (hm : 1 ≤ m)
    {X : Type} [Fintype X]
    (r : Fin 1 → Fin m → X → ℝ) (v : Fin 1 → X → ℝ)
    (hconst : ∀ w c, r w c = v w) :
    overproductionGap (starStep m) 0 unitSurface (uniformRoleWeights m) r =
      Real.logb 2 (m : ℝ) :=
  echo_multiplicity_forces_gap (starStep m) 0 unitSurface
    (uniformRoleWeights m) r (uniformRoleWeights_sum_one hm) v hconst m
    (star_terminalMultiplicity hm)

/-- The star echo channel leaves gap `log₂ m`. -/
theorem roleEcho_gap_log {m : ℕ} (hm : 1 ≤ m) :
    overproductionGap (starStep m) 0 unitSurface (uniformRoleWeights m)
      (roleEcho m) = Real.logb 2 (m : ℝ) :=
  roleBlind_gap_log hm (roleEcho m) (fun _ _ => (1 : ℝ) / m) (fun _ _ => rfl)

/-- Mixture of uniform point-masses is the uniform mass on `Fin m`. -/
theorem roleResolving_mixture_eq_uniform {m : ℕ} (_hm : 1 ≤ m) (w : Fin 1) :
    (fun x : Fin m =>
      ∑ c : Fin m, uniformRoleWeights m w c * roleResolving m w c x) =
      uniformMass (Fin m) := by
  funext x
  have hsum : ∑ c : Fin m, pointMass c x = 1 := by
    rw [Finset.sum_eq_single x]
    · simp [pointMass]
    · intro c _ hcx
      simp [pointMass, Ne.symm hcx]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  simp only [uniformRoleWeights, roleResolving, uniformMass, Fintype.card_fin]
  rw [← Finset.mul_sum, hsum, mul_one]

/-- Direct conditional entropy of the resolving role channel is `log m` nats. -/
theorem roleResolving_condEntropyDirect {m : ℕ} (hm : 1 ≤ m) :
    condEntropyDirect unitSurface (uniformRoleWeights m) (roleResolving m) =
      Real.log (m : ℝ) := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (Nat.succ_le_iff.mp hm)
  unfold condEntropyDirect unitSurface
  rw [Fin.sum_univ_one, one_mul, roleResolving_mixture_eq_uniform hm _]
  simpa [Fintype.card_fin] using H_uniformMass_eq_log_card (Fin m)

/-- Residual entropy of each resolving cell is zero. -/
theorem roleResolving_residual_zero {m : ℕ} (w : Fin 1) (c : Fin m) :
    H (roleResolving m w c) = 0 :=
  H_pointMass c

/-- Raw deficit of the resolving role channel is `log m` nats. -/
theorem roleResolving_deficit_log {m : ℕ} (hm : 1 ≤ m) :
    deficit unitSurface (uniformRoleWeights m) (roleResolving m) =
      Real.log (m : ℝ) := by
  rw [deficit_eq_condEntropyDirect_of_zero_residual unitSurface
    (uniformRoleWeights m) (roleResolving m)
    (fun w c => roleResolving_residual_zero w c)]
  exact roleResolving_condEntropyDirect hm

/-- The resolving role channel supplies `log₂ m` bits. -/
theorem roleResolving_deficitBits_log {m : ℕ} (hm : 1 ≤ m) :
    deficitBits unitSurface (uniformRoleWeights m) (roleResolving m) =
      Real.logb 2 (m : ℝ) := by
  unfold deficitBits Real.logb
  rw [roleResolving_deficit_log hm]

/-- The resolving role channel closes the star gap. -/
theorem roleResolving_gap_zero_m {m : ℕ} (hm : 1 ≤ m) :
    overproductionGap (starStep m) 0 unitSurface (uniformRoleWeights m)
      (roleResolving m) = 0 := by
  unfold overproductionGap
  rw [star_terminalHartleyEntropy hm, roleResolving_deficitBits_log hm, sub_self]

/-- **The m-ary exchange.** `Ω_value − Ω_role = log₂ m`. -/
theorem m_ary_role_exchange {m : ℕ} (hm : 1 ≤ m) :
    overproductionGap (starStep m) 0 unitSurface (uniformRoleWeights m)
        (roleEcho m) -
      overproductionGap (starStep m) 0 unitSurface (uniformRoleWeights m)
        (roleResolving m) =
      Real.logb 2 (m : ℝ) := by
  rw [roleEcho_gap_log hm, roleResolving_gap_zero_m hm, sub_zero]

/-- On the equiprobable fiber the role entropy in bits equals `Ω_value`.
`Y` is constant on that fiber, so `H(R | Y) = H(R)`. -/
theorem role_entropy_eq_gap {m : ℕ} (hm : 1 ≤ m) :
    HBits (uniformMass (Fin m)) =
      overproductionGap (starStep m) 0 unitSurface (uniformRoleWeights m)
        (roleEcho m) := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (Nat.succ_le_iff.mp hm)
  rw [HBits_uniformMass_eq_logb_card, Fintype.card_fin, roleEcho_gap_log hm]

/-- Binary specialization recovers `one_bit_dp_exchange` as equality of reals. -/
theorem binary_case :
    (overproductionGap (starStep 2) 0 unitSurface (uniformRoleWeights 2)
        (roleEcho 2) -
      overproductionGap (starStep 2) 0 unitSurface (uniformRoleWeights 2)
        (roleResolving 2)) =
    (overproductionGap Fork3Step Fork3.source unitSurface
        OverproductionGap.roleWeights OverproductionGap.roleEcho -
      overproductionGap Fork3Step Fork3.source unitSurface
        OverproductionGap.roleWeights OverproductionGap.roleResolving) := by
  have hstar := m_ary_role_exchange (by decide : 1 ≤ 2)
  have hfork := one_bit_dp_exchange
  have hlog : Real.logb 2 ((2 : ℕ) : ℝ) = 1 := by
    norm_cast
    exact Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)
  rw [hstar, hfork, hlog]

end

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchange
