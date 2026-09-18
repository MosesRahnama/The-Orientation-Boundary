import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchange
import OperatorKO7.Meta.Recursor.RaryDuplicator

/-!
# Role-law and duplication-arity exchange

This module extends the finite star calculation in two directions.  An arbitrary
probability law on a finite role alphabet exchanges its Shannon entropy with the
overproduction gap.  For an `r`-frame duplicator, the active-versus-frame channel
spends the binary active/frame entropy and leaves the frame-index entropy.

Relation: `starStep m` for the information calculation and `RStep r` for the
live duplicator witness.  Trust: kernel checked.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchangeGeneral

universe u

open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchange
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy

noncomputable section

/-- A probability law on the role alphabet, constant over the one-cell direct surface. -/
def roleWeightsOf {m : Nat} (nu : Fin m -> Real) : Fin 1 -> Fin m -> Real :=
  fun _ c => nu c

/-- The mixture of role-indexed point masses is the role law itself. -/
theorem roleResolving_mixture_eq_law {m : Nat} (nu : Fin m -> Real) (w : Fin 1) :
    (fun x : Fin m =>
      ∑ c : Fin m, roleWeightsOf nu w c *
        OverproductionGapRoleExchange.roleResolving m w c x) = nu := by
  funext x
  rw [Finset.sum_eq_single x]
  · simp [roleWeightsOf, OverproductionGapRoleExchange.roleResolving, pointMass]
  · intro c _ hcx
    simp [roleWeightsOf, OverproductionGapRoleExchange.roleResolving, pointMass,
      Ne.symm hcx]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- A role-constant channel leaves the whole `log₂ m` star gap. -/
theorem general_valueBlind_gap {m : Nat} (hm : 1 <= m)
    (nu : Fin m -> Real) (hnu1 : ∑ c, nu c = 1)
    {X : Type} [Fintype X]
    (r : Fin 1 -> Fin m -> X -> Real) (v : Fin 1 -> X -> Real)
    (hconst : ∀ w c, r w c = v w) :
    overproductionGap (starStep m) 0 unitSurface (roleWeightsOf nu) r =
      Real.logb 2 (m : Real) := by
  exact echo_multiplicity_forces_gap (starStep m) 0 unitSurface
    (roleWeightsOf nu) r
    (fun _ => by simpa [roleWeightsOf] using hnu1) v hconst m
    (star_terminalMultiplicity hm)

/-- The direct target mixture of the resolving channel is the role law. -/
theorem general_roleResolving_condEntropyDirect {m : Nat}
    (nu : Fin m -> Real) :
    condEntropyDirect unitSurface (roleWeightsOf nu)
      (OverproductionGapRoleExchange.roleResolving m) = H nu := by
  unfold condEntropyDirect unitSurface
  rw [Fin.sum_univ_one, one_mul, roleResolving_mixture_eq_law]

/-- The resolving channel has zero residual entropy in every role cell. -/
theorem general_roleResolving_residual_zero {m : Nat} (w : Fin 1) (c : Fin m) :
    H (OverproductionGapRoleExchange.roleResolving m w c) = 0 :=
  H_pointMass c

/-- The resolving channel supplies the entropy of the role law in nats. -/
theorem general_roleResolving_deficit {m : Nat} (nu : Fin m -> Real) :
    deficit unitSurface (roleWeightsOf nu)
      (OverproductionGapRoleExchange.roleResolving m) = H nu := by
  rw [deficit_eq_condEntropyDirect_of_zero_residual unitSurface
    (roleWeightsOf nu) (OverproductionGapRoleExchange.roleResolving m)
    general_roleResolving_residual_zero]
  exact general_roleResolving_condEntropyDirect nu

/-- The resolving channel supplies the entropy of the role law in bits. -/
theorem general_roleResolving_deficitBits {m : Nat} (nu : Fin m -> Real) :
    deficitBits unitSurface (roleWeightsOf nu)
      (OverproductionGapRoleExchange.roleResolving m) = HBits nu := by
  unfold deficitBits HBits
  rw [general_roleResolving_deficit]

/-- The role-resolving gap is the Hartley envelope minus the role entropy. -/
theorem general_role_gap {m : Nat} (hm : 1 <= m) (nu : Fin m -> Real) :
    overproductionGap (starStep m) 0 unitSurface (roleWeightsOf nu)
        (OverproductionGapRoleExchange.roleResolving m) =
      Real.logb 2 (m : Real) - HBits nu := by
  unfold overproductionGap
  rw [star_terminalHartleyEntropy hm, general_roleResolving_deficitBits]

/-- The exchange between a role-constant channel and role resolution is `H(nu)` bits. -/
theorem general_role_exchange {m : Nat} (hm : 1 <= m)
    (nu : Fin m -> Real) (hnu1 : ∑ c, nu c = 1)
    {X : Type} [Fintype X]
    (r : Fin 1 -> Fin m -> X -> Real) (v : Fin 1 -> X -> Real)
    (hconst : ∀ w c, r w c = v w) :
    overproductionGap (starStep m) 0 unitSurface (roleWeightsOf nu) r -
      overproductionGap (starStep m) 0 unitSurface (roleWeightsOf nu)
        (OverproductionGapRoleExchange.roleResolving m) = HBits nu := by
  rw [general_valueBlind_gap hm nu hnu1 r v hconst, general_role_gap hm]
  ring

/-- The role-resolving gap is nonnegative for every probability law. -/
theorem general_role_gap_nonneg {m : Nat} (hm : 1 <= m)
    (nu : Fin m -> Real) (hnu0 : ∀ c, 0 <= nu c) (hnu1 : ∑ c, nu c = 1) :
    0 <= overproductionGap (starStep m) 0 unitSurface (roleWeightsOf nu)
      (OverproductionGapRoleExchange.roleResolving m) := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (Nat.succ_le_iff.mp hm)
  rw [general_role_gap hm]
  exact sub_nonneg.mpr (by
    simpa [Fintype.card_fin] using HBits_le_logb_card nu hnu0 hnu1)

/-- Equality in the finite Shannon-Hartley bound characterizes uniform mass. -/
theorem H_eq_log_card_iff_eq_uniformMass
    {alpha : Type} [Fintype alpha] [Nonempty alpha]
    (p : alpha -> Real) (hp0 : ∀ x, 0 <= p x) (hsum : ∑ x, p x = 1) :
    H p = Real.log (Fintype.card alpha : Real) <-> p = uniformMass alpha := by
  constructor
  · intro hH
    let n : Real := Fintype.card alpha
    let w : alpha -> Real := fun _ => 1 / n
    have hn : 0 < n := by
      dsimp [n]
      exact card_cast_pos alpha
    have hw0 : ∀ i ∈ (Finset.univ : Finset alpha), 0 < w i := by
      intro i hi
      exact one_div_pos.mpr hn
    have hw1 : ∑ i ∈ (Finset.univ : Finset alpha), w i = 1 := by
      simp [w, n, hn.ne']
    have hmem : ∀ i ∈ (Finset.univ : Finset alpha), p i ∈ Set.Ici (0 : Real) := by
      intro i hi
      exact Set.mem_Ici.mpr (hp0 i)
    have hcenter : ∑ i ∈ (Finset.univ : Finset alpha), w i • p i = 1 / n := by
      simp only [w, smul_eq_mul]
      rw [← Finset.mul_sum, hsum, mul_one]
    have hright : ∑ i ∈ (Finset.univ : Finset alpha),
        w i • Real.negMulLog (p i) = (1 / n) * H p := by
      simp only [w, smul_eq_mul, H, ← Finset.mul_sum]
    have hlog : Real.log (1 / n) = - Real.log n := by
      rw [one_div, Real.log_inv]
    have hjensen :
        Real.negMulLog (∑ i ∈ (Finset.univ : Finset alpha), w i • p i) =
          ∑ i ∈ (Finset.univ : Finset alpha), w i • Real.negMulLog (p i) := by
      rw [hcenter, hright, hH]
      change -(1 / n) * Real.log (1 / n) = (1 / n) * Real.log n
      rw [hlog]
      ring
    have hall := (Real.strictConcaveOn_negMulLog.map_sum_eq_iff hw0 hw1 hmem).mp hjensen
    funext x
    have hx := hall x (Finset.mem_univ x)
    rw [hcenter] at hx
    simpa [uniformMass, n] using hx
  · intro hp
    subst hp
    exact H_uniformMass_eq_log_card alpha

/-- Equality in the bit-valued Shannon-Hartley bound characterizes uniform mass. -/
theorem HBits_eq_logb_card_iff_eq_uniformMass
    {alpha : Type} [Fintype alpha] [Nonempty alpha]
    (p : alpha -> Real) (hp0 : ∀ x, 0 <= p x) (hsum : ∑ x, p x = 1) :
    HBits p = Real.logb 2 (Fintype.card alpha : Real) <->
      p = uniformMass alpha := by
  unfold HBits Real.logb
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  constructor
  · intro h
    apply (H_eq_log_card_iff_eq_uniformMass p hp0 hsum).mp
    apply (div_left_inj' hlog2).mp
    exact h
  · intro hp
    apply (div_left_inj' hlog2).mpr
    exact (H_eq_log_card_iff_eq_uniformMass p hp0 hsum).mpr hp

/-- The role-resolving gap vanishes precisely for the uniform role law. -/
theorem general_role_gap_eq_zero_iff {m : Nat} (hm : 1 <= m)
    (nu : Fin m -> Real) (hnu0 : ∀ c, 0 <= nu c) (hnu1 : ∑ c, nu c = 1) :
    overproductionGap (starStep m) 0 unitSurface (roleWeightsOf nu)
        (OverproductionGapRoleExchange.roleResolving m) = 0 <->
      nu = uniformMass (Fin m) := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (Nat.succ_le_iff.mp hm)
  rw [general_role_gap hm, sub_eq_zero]
  simpa [Fintype.card_fin, eq_comm] using
    (HBits_eq_logb_card_iff_eq_uniformMass nu hnu0 hnu1)

/-- At `m = 0` no probability law exists, so the positive-cardinality premise
of the role-law exchange is necessary. -/
theorem no_role_law_zero :
    ¬ ∃ nu : Fin 0 -> Real, ∑ c, nu c = 1 := by
  rintro ⟨nu, hnu⟩
  simp at hnu

/-! ## Relation-independent finite role law -/

/-- A role law on an arbitrary finite role type. -/
def finiteRoleWeightsOf {C : Type} (nu : C -> Real) : Fin 1 -> C -> Real :=
  fun _ c => nu c

/-- Full resolution on an arbitrary finite role type. -/
def finiteRoleResolving {C : Type} [Fintype C] [DecidableEq C] :
    Fin 1 -> C -> C -> Real :=
  fun _ c => pointMass c

/-- The mixture of arbitrary finite role point masses is the role law. -/
theorem finiteRoleResolving_mixture_eq_law
    {C : Type} [Fintype C] [DecidableEq C]
    (nu : C -> Real) (w : Fin 1) :
    (fun x : C => ∑ c : C, finiteRoleWeightsOf nu w c * finiteRoleResolving w c x) = nu := by
  funext x
  rw [Finset.sum_eq_single x]
  · simp [finiteRoleWeightsOf, finiteRoleResolving, pointMass]
  · intro c _ hcx
    simp [finiteRoleWeightsOf, finiteRoleResolving, pointMass, Ne.symm hcx]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- Full finite-role resolution supplies exactly the role entropy in bits. -/
theorem finiteRoleResolving_deficitBits
    {C : Type} [Fintype C] [DecidableEq C]
    (nu : C -> Real) :
    deficitBits unitSurface (finiteRoleWeightsOf nu) finiteRoleResolving = HBits nu := by
  unfold deficitBits deficit condEntropyDirect condEntropyLicensed unitSurface HBits
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  simp only [one_mul, finiteRoleResolving_mixture_eq_law]
  have hzero : ∀ c : C, H (finiteRoleResolving (0 : Fin 1) c) = 0 := by
    intro c
    exact H_pointMass c
  simp [hzero]

/-- On every finite relation, a role-constant evidence channel leaves the
entire terminal Hartley entropy when role cardinality equals terminal multiplicity. -/
theorem finite_relation_valueBlind_gap
    {T : Type u} [Fintype T] {C X : Type} [Fintype C] [Fintype X]
    (R : T -> T -> Prop) (source : T)
    (nu : C -> Real) (hnu1 : ∑ c, nu c = 1)
    (hcard : OperatorKO7.Meta.DistinctionBoundary.Quantitative.terminalMultiplicity R source =
      Fintype.card C)
    (evidence : Fin 1 -> C -> X -> Real) (v : Fin 1 -> X -> Real)
    (hconst : ∀ w c, evidence w c = v w) :
    overproductionGap R source unitSurface (finiteRoleWeightsOf nu) evidence =
      Real.logb 2 (Fintype.card C : Real) := by
  exact echo_multiplicity_forces_gap R source unitSurface (finiteRoleWeightsOf nu)
    evidence (fun _ => by simpa [finiteRoleWeightsOf] using hnu1) v hconst
    (Fintype.card C) hcard

/-- On every finite relation, full role resolution leaves the Hartley envelope
minus the Shannon entropy of the role law. -/
theorem finite_relation_role_gap
    {T : Type u} [Fintype T] {C : Type} [Fintype C] [DecidableEq C]
    (R : T -> T -> Prop) (source : T)
    (nu : C -> Real)
    (hcard : OperatorKO7.Meta.DistinctionBoundary.Quantitative.terminalMultiplicity R source =
      Fintype.card C) :
    overproductionGap R source unitSurface (finiteRoleWeightsOf nu) finiteRoleResolving =
      Real.logb 2 (Fintype.card C : Real) - HBits nu := by
  unfold overproductionGap OperatorKO7.Meta.DistinctionBoundary.Quantitative.terminalHartleyEntropy
  rw [hcard, finiteRoleResolving_deficitBits]

/-- **Relation-independent role exchange.** For every finite relation whose
terminal multiplicity matches its finite role alphabet, upgrading any
role-constant channel to full role resolution exchanges exactly `HBits nu`. -/
theorem finite_relation_role_exchange
    {T : Type u} [Fintype T] {C X : Type} [Fintype C] [DecidableEq C] [Fintype X]
    (R : T -> T -> Prop) (source : T)
    (nu : C -> Real) (hnu1 : ∑ c, nu c = 1)
    (hcard : OperatorKO7.Meta.DistinctionBoundary.Quantitative.terminalMultiplicity R source =
      Fintype.card C)
    (evidence : Fin 1 -> C -> X -> Real) (v : Fin 1 -> X -> Real)
    (hconst : ∀ w c, evidence w c = v w) :
    overproductionGap R source unitSurface (finiteRoleWeightsOf nu) evidence -
      overproductionGap R source unitSurface (finiteRoleWeightsOf nu) finiteRoleResolving =
      HBits nu := by
  rw [finite_relation_valueBlind_gap R source nu hnu1 hcard evidence v hconst,
    finite_relation_role_gap R source nu hcard]
  ring

/-- The relation-independent residual gap is nonnegative for every probability law. -/
theorem finite_relation_role_gap_nonneg
    {T : Type u} [Fintype T] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
    (R : T -> T -> Prop) (source : T)
    (nu : C -> Real) (hnu0 : ∀ c, 0 <= nu c) (hnu1 : ∑ c, nu c = 1)
    (hcard : OperatorKO7.Meta.DistinctionBoundary.Quantitative.terminalMultiplicity R source =
      Fintype.card C) :
    0 <= overproductionGap R source unitSurface (finiteRoleWeightsOf nu)
      finiteRoleResolving := by
  rw [finite_relation_role_gap R source nu hcard]
  exact sub_nonneg.mpr (HBits_le_logb_card nu hnu0 hnu1)

/-- The relation-independent residual vanishes exactly at the uniform role law. -/
theorem finite_relation_role_gap_eq_zero_iff
    {T : Type u} [Fintype T] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
    (R : T -> T -> Prop) (source : T)
    (nu : C -> Real) (hnu0 : ∀ c, 0 <= nu c) (hnu1 : ∑ c, nu c = 1)
    (hcard : OperatorKO7.Meta.DistinctionBoundary.Quantitative.terminalMultiplicity R source =
      Fintype.card C) :
    overproductionGap R source unitSurface (finiteRoleWeightsOf nu)
        finiteRoleResolving = 0 ↔
      nu = uniformMass C := by
  rw [finite_relation_role_gap R source nu hcard, sub_eq_zero]
  simpa [eq_comm] using HBits_eq_logb_card_iff_eq_uniformMass nu hnu0 hnu1

/-- Uniform roles recover the `m`-ary exchange already proved for the star. -/
theorem uniform_case {m : Nat} (hm : 1 <= m) :
    overproductionGap (starStep m) 0 unitSurface (uniformRoleWeights m)
          (roleEcho m) -
        overproductionGap (starStep m) 0 unitSurface (uniformRoleWeights m)
          (roleResolving m) = Real.logb 2 (m : Real) :=
  m_ary_role_exchange hm

/-! ## Duplication arity -/

/-- Uniform mass on the `r` frame identities, embedded in `Fin (r + 1)` with
zero mass at the active cell `0`. -/
def frameUniform (r : Nat) : Fin (r + 1) -> Real :=
  fun x => if x = 0 then 0 else 1 / (r : Real)

/-- The embedded frame law is normalized for every positive duplication arity. -/
theorem frameUniform_sum_one {r : Nat} (hr : 1 <= r) :
    ∑ x : Fin (r + 1), frameUniform r x = 1 := by
  rw [Fin.sum_univ_succ]
  have hr0 : (r : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hr))
  simp [frameUniform, hr0]

/-- The embedded frame law has `log r` nats of entropy. -/
theorem H_frameUniform_eq_log {r : Nat} (hr : 1 <= r) :
    H (frameUniform r) = Real.log (r : Real) := by
  unfold H
  rw [Fin.sum_univ_succ]
  have hr0 : (r : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hr))
  have hlog : Real.log (1 / (r : Real)) = -Real.log (r : Real) := by
    rw [one_div, Real.log_inv]
  simp only [frameUniform, if_pos, Fin.succ_ne_zero, if_false, Finset.sum_const,
    nsmul_eq_mul, Real.negMulLog_def, hlog]
  field_simp

/-- The dependency-pair evidence channel for an `r`-frame duplicator. Role
`0` resolves the active callee. Every nonzero role identifies only that the
occurrence is a frame and leaves the frame index uniformly unresolved. -/
def dpChannel (r : Nat) : Fin 1 -> Fin (r + 1) -> Fin (r + 1) -> Real :=
  fun _ c => if c = 0 then pointMass 0 else frameUniform r

/-- The active role is fully resolved. -/
theorem dpChannel_active (r : Nat) (w : Fin 1) :
    dpChannel r w 0 = pointMass 0 := by
  simp [dpChannel]

/-- Every frame role induces the same unresolved frame-index law. -/
theorem dpChannel_frame {r : Nat} (w : Fin 1) (c : Fin (r + 1)) (hc : c ≠ 0) :
    dpChannel r w c = frameUniform r := by
  simp [dpChannel, hc]

/-- The active/frame channel preserves the uniform terminal marginal. -/
theorem dpChannel_mixture_eq_uniform {r : Nat} (hr : 1 <= r) (w : Fin 1) :
    (fun x : Fin (r + 1) =>
      ∑ c : Fin (r + 1), uniformRoleWeights (r + 1) w c * dpChannel r w c x) =
      uniformMass (Fin (r + 1)) := by
  funext x
  refine Fin.cases ?_ (fun i => ?_) x
  · rw [Fin.sum_univ_succ]
    simp [uniformRoleWeights, dpChannel, pointMass, frameUniform, uniformMass]
  · rw [Fin.sum_univ_succ]
    have hr0 : (r : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hr))
    simp only [uniformRoleWeights, dpChannel, pointMass, frameUniform, uniformMass,
      Fin.succ_ne_zero, if_pos, if_false, Fintype.card_fin]
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
    ring

/-- Before licensing, the uniform `r+1` terminal law has `log (r+1)` nats of entropy. -/
theorem dpChannel_condEntropyDirect {r : Nat} (hr : 1 <= r) :
    condEntropyDirect unitSurface (uniformRoleWeights (r + 1)) (dpChannel r) =
      Real.log (r + 1 : Nat) := by
  haveI : Nonempty (Fin (r + 1)) := inferInstance
  unfold condEntropyDirect unitSurface
  rw [Fin.sum_univ_one, one_mul, dpChannel_mixture_eq_uniform hr]
  simpa [Fintype.card_fin] using H_uniformMass_eq_log_card (Fin (r + 1))

/-- After licensing, exactly the frame-index entropy remains. -/
theorem dpChannel_condEntropyLicensed {r : Nat} (hr : 1 <= r) :
    condEntropyLicensed unitSurface (uniformRoleWeights (r + 1)) (dpChannel r) =
      (r : Real) / (r + 1 : Nat) * Real.log (r : Real) := by
  unfold condEntropyLicensed unitSurface
  rw [Fin.sum_univ_one, one_mul, Fin.sum_univ_succ]
  have hr0 : (r : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hr))
  simp only [uniformRoleWeights, dpChannel, if_pos, H_pointMass, mul_zero,
    Fin.succ_ne_zero, if_false, H_frameUniform_eq_log hr, zero_add, Finset.sum_const,
    nsmul_eq_mul]
  simp only [Finset.card_univ, Fintype.card_fin]
  ring

/-- The active-versus-frame channel supplies the binary active-share entropy. -/
theorem dpChannel_deficitBits {r : Nat} (hr : 1 <= r) :
    deficitBits unitSurface (uniformRoleWeights (r + 1)) (dpChannel r) =
      Real.logb 2 (r + 1 : Nat) -
        ((r : Real) / (r + 1 : Nat)) * Real.logb 2 (r : Real) := by
  unfold deficitBits deficit Real.logb
  rw [dpChannel_condEntropyDirect hr, dpChannel_condEntropyLicensed hr]
  ring

/-- Binary entropy, in bits, of the active share among `r+1` occurrences. -/
def activeShareEntropyBits (r : Nat) : Real :=
  Real.binEntropy (1 / (r + 1 : Nat)) / Real.log 2

/-- Closed form of the active-versus-frame binary entropy. -/
theorem activeShareEntropyBits_closed {r : Nat} (hr : 1 <= r) :
    activeShareEntropyBits r =
      Real.logb 2 (r + 1 : Nat) -
        ((r : Real) / (r + 1 : Nat)) * Real.logb 2 (r : Real) := by
  have hrpos : (0 : Real) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  have hr1pos : (0 : Real) < r + 1 := by positivity
  have hr0 : (r : Real) ≠ 0 := hrpos.ne'
  have hr10 : (r + 1 : Real) ≠ 0 := hr1pos.ne'
  have hsub : (1 : Real) - 1 / (r + 1 : Real) = r / (r + 1 : Real) := by
    field_simp
  have hsubInv : (1 : Real) - (r + 1 : Real)⁻¹ = r / (r + 1 : Real) := by
    simpa [one_div] using hsub
  have hlogInv' : Real.log ((r + 1 : Real)⁻¹) = -Real.log (r + 1 : Real) := by
    rw [Real.log_inv]
  have hlogDiv : Real.log ((r : Real) / (r + 1 : Real)) =
      Real.log (r : Real) - Real.log (r + 1 : Real) := by
    rw [Real.log_div hr0 hr10]
  unfold activeShareEntropyBits Real.logb
  norm_num [Nat.cast_add, Nat.cast_one]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hsubInv]
  simp only [Real.negMulLog_def, hlogInv', hlogDiv]
  field_simp
  ring

/-- The DP deficit is exactly the binary entropy of the active/frame decision. -/
theorem dpChannel_deficitBits_eq_activeShareEntropy {r : Nat} (hr : 1 <= r) :
    deficitBits unitSurface (uniformRoleWeights (r + 1)) (dpChannel r) =
      activeShareEntropyBits r := by
  rw [dpChannel_deficitBits hr, activeShareEntropyBits_closed hr]

/-- The frame-copy identity left unlicensed by the dependency-pair channel. -/
theorem dpChannel_gap {r : Nat} (hr : 1 <= r) :
    overproductionGap (starStep (r + 1)) 0 unitSurface
        (uniformRoleWeights (r + 1)) (dpChannel r) =
      ((r : Real) / (r + 1 : Nat)) * Real.logb 2 (r : Real) := by
  unfold overproductionGap
  rw [star_terminalHartleyEntropy (m := r + 1) (by omega), dpChannel_deficitBits hr]
  ring

/-- Upgrading a value-blind channel to the active/frame channel spends exactly
the active-versus-frame entropy. -/
theorem rary_dp_exchange {r : Nat} (hr : 1 <= r) :
    overproductionGap (starStep (r + 1)) 0 unitSurface
        (uniformRoleWeights (r + 1)) (roleEcho (r + 1)) -
      overproductionGap (starStep (r + 1)) 0 unitSurface
        (uniformRoleWeights (r + 1)) (dpChannel r) =
      Real.logb 2 (r + 1 : Nat) -
        ((r : Real) / (r + 1 : Nat)) * Real.logb 2 (r : Real) := by
  rw [roleEcho_gap_log (m := r + 1) (by omega), dpChannel_gap hr]

/-- Full role resolution closes the overproduction gap at every positive arity. -/
theorem full_role_resolution_closes (r : Nat) :
    overproductionGap (starStep (r + 1)) 0 unitSurface
        (uniformRoleWeights (r + 1))
          (OverproductionGapRoleExchange.roleResolving (r + 1)) = 0 :=
  roleResolving_gap_zero_m (m := r + 1) (by omega)

/-- With one frame, active/frame evidence is full role resolution. -/
theorem dpChannel_one_eq_roleResolving_two :
    dpChannel 1 = OverproductionGapRoleExchange.roleResolving 2 := by
  funext w c x
  refine Fin.cases ?_ (fun i => ?_) c
  · simp [dpChannel, OverproductionGapRoleExchange.roleResolving]
  · have hi : i = 0 := Fin.eq_zero i
    subst i
    refine Fin.cases ?_ (fun j => ?_) x
    · simp [dpChannel, frameUniform, OverproductionGapRoleExchange.roleResolving,
        pointMass]
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      simp [dpChannel, frameUniform, OverproductionGapRoleExchange.roleResolving,
        pointMass]

/-- One frame is the unique arity at which the active/frame channel resolves
the whole role alphabet: its residual gap is zero and its exchange is one bit. -/
theorem rary_one_frame :
    overproductionGap (starStep 2) 0 unitSurface (uniformRoleWeights 2)
        (dpChannel 1) = 0 ∧
      overproductionGap (starStep 2) 0 unitSurface (uniformRoleWeights 2)
          (roleEcho 2) -
        overproductionGap (starStep 2) 0 unitSurface (uniformRoleWeights 2)
          (dpChannel 1) = 1 := by
  constructor
  · simpa using dpChannel_gap (r := 1) (by decide)
  · rw [rary_dp_exchange (r := 1) (by decide)]
    norm_num [Real.logb_self_eq_one (by norm_num : (1 : Real) < 2)]

/-- The one-frame exchange is the original `Fork3` one-bit theorem as an
equality of real numbers. -/
theorem rary_one_frame_eq_one_bit_exchange :
    (overproductionGap (starStep 2) 0 unitSurface (uniformRoleWeights 2)
        (roleEcho 2) -
      overproductionGap (starStep 2) 0 unitSurface (uniformRoleWeights 2)
        (dpChannel 1)) =
    (overproductionGap
        OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Fork3Step
        OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Fork3.source unitSurface
        OverproductionGap.roleWeights OverproductionGap.roleEcho -
      overproductionGap
        OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Fork3Step
        OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Fork3.source unitSurface
        OverproductionGap.roleWeights OverproductionGap.roleResolving) := by
  rw [dpChannel_one_eq_roleResolving_two]
  exact binary_case

/-- With at least two frame copies, the DP channel leaves positive frame identity. -/
theorem frame_ambiguity_pos {r : Nat} (hr : 2 <= r) :
    0 < overproductionGap (starStep (r + 1)) 0 unitSurface
      (uniformRoleWeights (r + 1)) (dpChannel r) := by
  rw [dpChannel_gap (hr.trans' (by omega))]
  apply mul_pos
  · positivity
  · exact Real.logb_pos (by norm_num) (by exact_mod_cast hr)

/-- At arity zero the unique role is active and the DP channel is already fully resolving. -/
theorem rary_zero_nonexample :
    dpChannel 0 = OverproductionGapRoleExchange.roleResolving 1 := by
  funext w c x
  have hc : c = 0 := Fin.eq_zero c
  subst c
  simp [dpChannel, OverproductionGapRoleExchange.roleResolving]

/-! ## Live `RStep` occurrence bridge -/

/-- The `r` frame positions and the single active-callee position in an
`RStep.stepRule` contractum. -/
abbrev RaryOcc (r : Nat) := Fin r ⊕ Unit

/-- Relabel the live occurrence carrier by the finite-star roles, reserving
`0` for the active callee and `i+1` for frame `i`. -/
def raryOccEquiv (r : Nat) : RaryOcc r ≃ Fin (r + 1) where
  toFun
    | Sum.inl i => i.succ
    | Sum.inr _ => 0
  invFun x := Fin.cases (Sum.inr ()) (fun i => Sum.inl i) x
  left_inv o := by cases o <;> simp
  right_inv x := by refine Fin.cases ?_ (fun i => ?_) x <;> simp

/-- The payload value is identical at every frame and active occurrence. -/
def raryValue {r : Nat} (y : OperatorKO7.Meta.Recursor.RaryDuplicator.RTerm) :
    RaryOcc r -> OperatorKO7.Meta.Recursor.RaryDuplicator.RTerm :=
  fun _ => y

/-- The deterministic dependency-pair observation: false for a frame and true
for the active recursive callee. -/
def raryDPChannel {r : Nat} : RaryOcc r -> Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

/-- Every frame is separated from the active callee by the DP discriminator. -/
theorem raryDP_separates {r : Nat} (i : Fin r) :
    raryDPChannel (Sum.inl i : RaryOcc r) ≠ raryDPChannel (Sum.inr () : RaryOcc r) := by
  simp [raryDPChannel]

/-- At positive arity the DP discriminator cannot factor through the constant
payload-value projection. -/
theorem raryDP_not_value_factored {r : Nat} (hr : 1 <= r)
    (y : OperatorKO7.Meta.Recursor.RaryDuplicator.RTerm) :
    ¬ ∃ q : OperatorKO7.Meta.Recursor.RaryDuplicator.RTerm -> Bool,
        ∀ o : RaryOcc r, raryDPChannel o = q (raryValue y o) := by
  rintro ⟨q, hq⟩
  let i : Fin r := ⟨0, Nat.zero_lt_of_lt hr⟩
  have hf := hq (Sum.inl i)
  have ha := hq (Sum.inr ())
  simp [raryDPChannel, raryValue] at hf ha
  exact Bool.false_ne_true (hf.symm.trans ha)

/-- The stochastic evidence induced by the live active/frame discriminator. -/
def raryDPEvidence (r : Nat) : RaryOcc r -> RaryOcc r -> Real
  | Sum.inr _, Sum.inr _ => 1
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inl _, Sum.inl _ => 1 / (r : Real)

/-- Under `raryOccEquiv`, the live occurrence evidence is exactly `dpChannel`. -/
theorem raryDP_evidence_eq_dpChannel (r : Nat) (o x : RaryOcc r) :
    raryDPEvidence r o x =
      dpChannel r 0 (raryOccEquiv r o) (raryOccEquiv r x) := by
  cases o <;> cases x <;>
    simp [raryDPEvidence, raryOccEquiv, dpChannel, pointMass, frameUniform]

/-- The deterministic discriminator is precisely the zero/nonzero partition
of the finite-star role alphabet. -/
theorem raryDPChannel_true_iff_role_zero {r : Nat} (o : RaryOcc r) :
    raryDPChannel o = true ↔ raryOccEquiv r o = 0 := by
  cases o <;> simp [raryDPChannel, raryOccEquiv]

/-- Payload attached to each indexed occurrence of the concrete step-rule
contractum. Frames are read from `List.replicate`; the active occurrence is
the recursive call's payload argument. -/
def raryContractumPayload (r : Nat)
    (y : OperatorKO7.Meta.Recursor.RaryDuplicator.RTerm) :
    RaryOcc r -> OperatorKO7.Meta.Recursor.RaryDuplicator.RTerm
  | Sum.inl i => (List.replicate r y)[i]
  | Sum.inr _ => y

/-- Every concrete frame and the active callee carry the same payload. -/
theorem raryContractumPayload_eq (r : Nat)
    (y : OperatorKO7.Meta.Recursor.RaryDuplicator.RTerm) (o : RaryOcc r) :
    raryContractumPayload r y o = y := by
  cases o with
  | inl i => simp [raryContractumPayload]
  | inr u => simp [raryContractumPayload]

/-- The live contractum contains exactly `r+1` indexed payload occurrences. -/
theorem rary_occurrence_count (r : Nat) : Fintype.card (RaryOcc r) = r + 1 := by
  simp [RaryOcc]

/-- `RStep.stepRule` reconstructed from its indexed frame and active payload
occurrences. This binds the information calculation to the actual rewrite relation. -/
theorem rary_stepRule_occurrence_indexed (r : Nat)
    (x y n : OperatorKO7.Meta.Recursor.RaryDuplicator.RTerm) :
    OperatorKO7.Meta.Recursor.RaryDuplicator.RStep r
      (.F x y (.S n))
      (.G (List.ofFn (fun i : Fin r => raryContractumPayload r y (Sum.inl i)))
        (.F x (raryContractumPayload r y (Sum.inr ())) n)) := by
  simpa [raryContractumPayload] using
    (OperatorKO7.Meta.Recursor.RaryDuplicator.RStep.stepRule (r := r) x y n)

/-- **Arity-general license law.** The live `r`-frame rewrite rule has `r+1`
payload-identical occurrences. The DP observation does not factor through that
payload, supplies exactly the active/frame information, leaves exactly the
frame-index entropy, and the derivation length remains blind to `r`. -/
theorem rary_license_is_active_bit {r : Nat} (hr : 1 <= r)
    (ia ib ia' ib' k r' : Nat) :
    Fintype.card (RaryOcc r) = r + 1 ∧
      (∀ y : OperatorKO7.Meta.Recursor.RaryDuplicator.RTerm, ∀ o : RaryOcc r,
        raryContractumPayload r y o = y) ∧
      (∀ x y n : OperatorKO7.Meta.Recursor.RaryDuplicator.RTerm,
        OperatorKO7.Meta.Recursor.RaryDuplicator.RStep r
          (.F x y (.S n))
          (.G (List.ofFn (fun i : Fin r =>
            raryContractumPayload r y (Sum.inl i)))
            (.F x (raryContractumPayload r y (Sum.inr ())) n))) ∧
      (∀ o x : RaryOcc r,
        raryDPEvidence r o x =
          dpChannel r 0 (raryOccEquiv r o) (raryOccEquiv r x)) ∧
      (∀ y : OperatorKO7.Meta.Recursor.RaryDuplicator.RTerm,
        ¬ ∃ q : OperatorKO7.Meta.Recursor.RaryDuplicator.RTerm -> Bool,
          ∀ o : RaryOcc r, raryDPChannel o = q (raryValue y o)) ∧
      deficitBits unitSurface (uniformRoleWeights (r + 1)) (dpChannel r) =
        Real.logb 2 (r + 1 : Nat) -
          ((r : Real) / (r + 1 : Nat)) * Real.logb 2 (r : Real) ∧
      overproductionGap (starStep (r + 1)) 0 unitSurface
          (uniformRoleWeights (r + 1)) (dpChannel r) =
        ((r : Real) / (r + 1 : Nat)) * Real.logb 2 (r : Real) ∧
      (OperatorKO7.Meta.Recursor.RaryDuplicator.RStepsTo r
          (OperatorKO7.Meta.Recursor.RaryDuplicator.rOrbit (.base ia) (.pay ib) k r 0)
          (k + 1)
          (OperatorKO7.Meta.Recursor.RaryDuplicator.rOrbit (.base ia) (.pay ib) k r (k + 1)) ∧
        OperatorKO7.Meta.Recursor.RaryDuplicator.RStepsTo r'
          (OperatorKO7.Meta.Recursor.RaryDuplicator.rOrbit (.base ia') (.pay ib') k r' 0)
          (k + 1)
          (OperatorKO7.Meta.Recursor.RaryDuplicator.rOrbit (.base ia') (.pay ib') k r' (k + 1))) := by
  refine ⟨rary_occurrence_count r, (fun y o => raryContractumPayload_eq r y o),
    (fun x y n => rary_stepRule_occurrence_indexed r x y n),
    raryDP_evidence_eq_dpChannel r, (fun y => raryDP_not_value_factored hr y),
    dpChannel_deficitBits hr, dpChannel_gap hr, ?_⟩
  exact OperatorKO7.Meta.Recursor.RaryDuplicator.L10_runtime_r_blind
    ia ib ia' ib' k r r'

/-! ## The residual role gap is a divergence from the uniform law

`general_role_gap` computes the residual as `log₂ m − H(ν)`. That expression is the
Kullback-Leibler divergence of the role law from the uniform law, converted to bits: the residual
is the exact amount by which the role law departs from uniform, and not an unnamed remainder. Its
nonnegativity and its vanishing exactly at the uniform law are Gibbs' inequality, already
available here as `general_role_gap_nonneg` and `general_role_gap_eq_zero_iff`. -/

/-- Kullback-Leibler divergence of a finite law from the uniform law, in nats. -/
noncomputable def klFromUniform {C : Type} [Fintype C] (nu : C -> Real) : Real :=
  ∑ c, nu c * Real.log (nu c * (Fintype.card C : Real))

/-- Termwise split of the divergence summand. Valid at `nu c = 0` because both sides vanish. -/
theorem klFromUniform_term_split {C : Type} [Fintype C] [Nonempty C]
    (nu : C -> Real) (c : C) :
    nu c * Real.log (nu c * (Fintype.card C : Real)) =
      nu c * Real.log (nu c) + nu c * Real.log (Fintype.card C : Real) := by
  by_cases h : nu c = 0
  · simp [h]
  · have hcard : (Fintype.card C : Real) ≠ 0 := ne_of_gt (card_cast_pos C)
    rw [Real.log_mul h hcard]
    ring

/-- The divergence in nats equals `log |C| − H(nu)`. -/
theorem klFromUniform_eq_log_card_sub_H {C : Type} [Fintype C] [Nonempty C]
    (nu : C -> Real) (hnu1 : ∑ c, nu c = 1) :
    klFromUniform nu = Real.log (Fintype.card C : Real) - H nu := by
  unfold klFromUniform H
  have hsplit :
      ∑ c, nu c * Real.log (nu c * (Fintype.card C : Real)) =
        (∑ c, nu c * Real.log (nu c)) +
          (∑ c, nu c) * Real.log (Fintype.card C : Real) := by
    rw [Finset.sum_congr rfl (fun c _ => klFromUniform_term_split nu c),
      Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [hsplit, hnu1, one_mul]
  have hneg : ∑ c, Real.negMulLog (nu c) = -(∑ c, nu c * Real.log (nu c)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun c _ => by simp [Real.negMulLog])
  rw [hneg]
  ring

/-- **The residual role gap is the divergence of the role law from the uniform law, in bits.** -/
theorem general_role_gap_eq_kl {m : Nat} (hm : 1 <= m)
    (nu : Fin m -> Real) (hnu1 : ∑ c, nu c = 1) :
    overproductionGap (starStep m) 0 unitSurface (roleWeightsOf nu)
        (OverproductionGapRoleExchange.roleResolving m) =
      klFromUniform nu / Real.log 2 := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (Nat.succ_le_iff.mp hm)
  rw [general_role_gap hm, klFromUniform_eq_log_card_sub_H nu hnu1]
  unfold HBits Real.logb
  simp [Fintype.card_fin, sub_div]

/-- The same identity on an arbitrary finite relation and role alphabet. -/
theorem finite_relation_role_gap_eq_kl
    {T : Type u} [Fintype T] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
    (R : T -> T -> Prop) (source : T)
    (nu : C -> Real) (hnu1 : ∑ c, nu c = 1)
    (hcard : OperatorKO7.Meta.DistinctionBoundary.Quantitative.terminalMultiplicity R source =
      Fintype.card C) :
    overproductionGap R source unitSurface (finiteRoleWeightsOf nu) finiteRoleResolving =
      klFromUniform nu / Real.log 2 := by
  rw [finite_relation_role_gap R source nu hcard,
    klFromUniform_eq_log_card_sub_H nu hnu1]
  unfold HBits Real.logb
  simp [sub_div]

/-- Gibbs: the divergence from the uniform law is nonnegative. -/
theorem klFromUniform_nonneg {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
    (nu : C -> Real) (hnu0 : ∀ c, 0 <= nu c) (hnu1 : ∑ c, nu c = 1) :
    0 <= klFromUniform nu := by
  rw [klFromUniform_eq_log_card_sub_H nu hnu1, sub_nonneg]
  exact H_le_log_card nu hnu0 hnu1

/-- Gibbs, equality case: the divergence vanishes exactly at the uniform law. -/
theorem klFromUniform_eq_zero_iff_uniform {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
    (nu : C -> Real) (hnu0 : ∀ c, 0 <= nu c) (hnu1 : ∑ c, nu c = 1) :
    klFromUniform nu = 0 <-> nu = uniformMass C := by
  rw [klFromUniform_eq_log_card_sub_H nu hnu1, sub_eq_zero]
  have hlog2 : Real.log 2 ≠ 0 := by positivity
  constructor
  · intro heq
    refine (HBits_eq_logb_card_iff_eq_uniformMass nu hnu0 hnu1).1 ?_
    unfold HBits Real.logb
    rw [heq]
  · intro heq
    have h2 := (HBits_eq_logb_card_iff_eq_uniformMass nu hnu0 hnu1).2 heq
    unfold HBits Real.logb at h2
    field_simp at h2
    linarith [h2]

end

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchangeGeneral
