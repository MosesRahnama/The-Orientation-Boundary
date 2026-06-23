import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
import OperatorKO7.Meta.Physics.ConfessionLandauerExact

/-!
# Constructive Landauer on a finite probability space: the reversible-swap erasure model

This module gives a fully finite, constructive proof that erasing one bit is paid for by an exactly
equal entropy increase in a bath, using nothing beyond finite Shannon entropy on a `Fintype`
(`ShannonFinite.H`) and a reversible relabeling (`Equiv`). No continuous analysis, no measure theory,
no general subadditivity, and no monotone-convergence machinery is used. The carrier is the concrete
two-register space `Fin 2 × Fin 2` and the reversible dynamics is the swap `Equiv.prodComm`.

The physical reading: a register holding one fair bit (`unif`, entropy `log 2`) is reset against a
bath slot initially in a determinate state (`reset = pointMass 0`, entropy `0`). The *reversible*
SWAP exchanges the two slots; afterwards the register is determinate (entropy `0`, the bit is erased)
and the bath carries the fair bit (entropy `log 2`). The total joint entropy is conserved because a
permutation of a finite sample space is an entropy-preserving relabeling. So the `log 2` removed from
the register reappears, exactly, as `log 2` injected into the bath. This is the information-theoretic
content of the Landauer bound, made constructive on a finite space; the thermodynamic floor
`kB·T·log 2` per erased bit is imported from `ConfessionLandauerExact` and tied to this one erased bit.

## Claim typing (binding)

* PROVEN-IN-LEAN (the theorems below): permutation invariance of finite Shannon entropy; the four
  marginal entropy values (register `log 2 → 0`, bath `0 → log 2`); the exact total-entropy
  conservation `H Pout = H Pin`; the bundled ledger; and the one-bit Landauer-floor corollary. All
  compose `ShannonFinite` anchors (`H_uniformFin2`, `H_pointMass`) and `ConfessionLandauerExact`
  (`landauerLowerBound_eq_perBit_mul_bits`) with standard `Real`/`Finset`/`Equiv` facts.
* This module proves the *information ledger* (entropy in = entropy out) constructively and identifies
  the per-bit thermodynamic floor. It does not assert that this particular finite model is realized by
  any specific physical device; the floor identification with released heat remains the conditional
  statement carried in `ConfessionLandauerSplit`, which is not used here.

## Audit slots
- Relation: NA (real-valued information functional on a finite sample space; no rewriting relation).
- Closure: `propext`, `Classical.choice`, `Quot.sound` (or a subset); verified by `#print axioms` below.
- Trust: no `sorry`/`admit`/`axiom`/`opaque`/`partial`/`unsafe`/`native_decide`/`bv_decide`/`@[csimp]`.
- Non-vacuity (R5): the entire construction is the concrete model on `Fin 2 × Fin 2`; the marginal
  theorems exhibit a genuine `log 2 ↔ 0` exchange (`erasure_entropy_ledger`), and
  `erased_bit_bears_landauer_floor` exhibits the concrete floor `kB·T·log 2` for the one erased bit.
  Non-triviality: every entropy value is computed (`log 2`, `0`), never a tautology or accessor.
- Scope: finite-alphabet distributions only; the conservation identity is the genuine permutation
  invariance of `H`, not a definitional rewrite.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace OperatorKO7.Meta.Physics.LandauerErasureFinite

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.Physics.ConfessionLandauerExact
open OperatorKO7.Meta.Physics.LandauerHeatBound
open OperatorKO7.Meta.Physics.ConfessionLandauerSplit

/-! ## 0. The fair-bit entropy value (`H (1/2, 1/2) = log 2`)

`ShannonFinite` exposes `H_pointMass` (determinate ⇒ entropy `0`); the companion fair-`Fin 2` value
`H (fun _ => 1/2) = log 2` is established at
`OperatorKO7.Meta.InformationalIncompleteness.LicensedCollapseDeficit.H_uniformFin2`, but that module
sits behind a heavy TRS import subtree. To keep this finite-Landauer file dependent on only
`ShannonFinite` + `ConfessionLandauerExact`, the one-line value is restated here directly from the
`H`/`negMulLog` definitions (the same proof as the established lemma); it is reused below, not
re-derived per call. -/

/-- Proves: the fair one-bit distribution on `Fin 2` has entropy `log 2`,
`H (fun _ : Fin 2 => 1/2) = Real.log 2`. (Value-level restatement of the established
`LicensedCollapseDeficit.H_uniformFin2`, kept local to avoid its heavy import.) -/
theorem H_uniformFin2 : H (fun _ : Fin 2 => (1 : ℝ) / 2) = Real.log 2 := by
  unfold H
  rw [Fin.sum_univ_two]
  simp [Real.negMulLog, one_div, Real.log_inv]
  ring

/-! ## 1. Permutation invariance of finite Shannon entropy -/

/--
Proves: a reversible relabeling of a finite sample space conserves Shannon entropy. For a `Fintype V`
  and a self-equivalence `e : V ≃ V`, `H (fun v => p (e v)) = H p`. Reindexing the `negMulLog`
  summands along the bijection `e` leaves the finite sum unchanged.
Does not prove: any continuous, asymptotic, or subadditivity property; this is the exact finite
  invariance only.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel-only (reindexing a finite sum by an equivalence).
Scope: every `Fintype V`, every `e : V ≃ V`, and every `p : V → ℝ`.
-/
theorem entropy_invariant_under_equiv {V : Type} [Fintype V] (e : V ≃ V) (p : V → ℝ) :
    H (fun v => p (e v)) = H p := by
  unfold H
  exact Equiv.sum_comp e (fun v => Real.negMulLog (p v))

/-! ## 2. The reversible erasure model on `Fin 2 × Fin 2` -/

/-- Register input: one fair bit, `unif _ = 1/2`. Its Shannon entropy is `log 2` (`H_uniformFin2`). -/
def unif : Fin 2 → ℝ := fun _ => (1 : ℝ) / 2

/-- Bath-slot input: the determinate (reset) state, `pointMass 0`. Its Shannon entropy is `0`
(`H_pointMass`). -/
def reset : Fin 2 → ℝ := pointMass (0 : Fin 2)

/-- The joint input distribution on `Fin 2 × Fin 2`: independent register `⊗` bath,
`Pin (r, z) = unif r * reset z`. -/
def Pin : Fin 2 × Fin 2 → ℝ := fun p => unif p.1 * reset p.2

/-- The reversible dynamics: the SWAP `Equiv.prodComm` exchanging register and bath slots. -/
def swap : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2) := Equiv.prodComm (Fin 2) (Fin 2)

/-- The pushforward of `Pin` under the SWAP: `Pout x = Pin (swap.symm x)`. Concretely
`Pout (r, z) = unif z * reset r` (the slots are exchanged). -/
def Pout : Fin 2 × Fin 2 → ℝ := fun x => Pin (swap.symm x)

/-- Register marginal of a joint distribution: sum out the bath coordinate. -/
def regMarginal (P : Fin 2 × Fin 2 → ℝ) : Fin 2 → ℝ := fun r => ∑ z, P (r, z)

/-- Bath marginal of a joint distribution: sum out the register coordinate. -/
def bathMarginal (P : Fin 2 × Fin 2 → ℝ) : Fin 2 → ℝ := fun z => ∑ r, P (r, z)

/-! ### Probability-mass bookkeeping (the two slots are normalized). -/

/-- The fair register bit is normalized: `∑ r, unif r = 1`. -/
theorem sum_unif : (∑ r, unif r) = 1 := by
  simp [unif]

/-- The reset bath slot is normalized: `∑ z, reset z = 1`. -/
theorem sum_reset : (∑ z, reset z) = 1 := by
  rw [Fin.sum_univ_two]; simp [reset, pointMass]

/-! ### Pointwise pushforward form. -/

/-- The pushforward written out: `Pout (r, z) = unif z * reset r`. The SWAP exchanges the two slots,
so the register coordinate of the output reads the bath's input law and vice versa. -/
theorem Pout_apply (r z : Fin 2) : Pout (r, z) = unif z * reset r := by
  unfold Pout swap Pin
  rw [Equiv.prodComm_symm, Equiv.prodComm_apply]
  rfl

/-! ### Register marginal: erased (`log 2 → 0`). -/

/-- Proves: the input register marginal is the fair bit, `regMarginal Pin = unif`. Summing the bath
  out of the independent joint leaves `unif r * (∑ z, reset z) = unif r * 1`. -/
theorem regMarginal_Pin : regMarginal Pin = unif := by
  funext r
  unfold regMarginal
  have hr : (∑ z, Pin (r, z)) = unif r * (∑ z, reset z) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z _ => rfl)
  rw [hr, sum_reset, mul_one]

/-- Proves: the output register marginal is determinate, `regMarginal Pout = reset`. After the SWAP the
  register carries the bath's old (reset) law: `∑ z, unif z * reset r = (∑ z, unif z) * reset r`. -/
theorem regMarginal_Pout : regMarginal Pout = reset := by
  funext r
  unfold regMarginal
  have hr : (∑ z, Pout (r, z)) = (∑ z, unif z) * reset r := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun z _ => Pout_apply r z)
  rw [hr, sum_unif, one_mul]

/-- Proves: the register starts at entropy `log 2`. `H (regMarginal Pin) = log 2`. -/
theorem H_regMarginal_Pin : H (regMarginal Pin) = Real.log 2 := by
  rw [regMarginal_Pin]; exact H_uniformFin2

/-- Proves: the register ends at entropy `0`: the bit has been erased. `H (regMarginal Pout) = 0`. -/
theorem H_regMarginal_Pout : H (regMarginal Pout) = 0 := by
  rw [regMarginal_Pout]; exact H_pointMass (0 : Fin 2)

/-! ### Bath marginal: absorbs (`0 → log 2`). -/

/-- Proves: the input bath marginal is determinate, `bathMarginal Pin = reset`. Summing the register
  out of the independent joint leaves `(∑ r, unif r) * reset z = 1 * reset z`. -/
theorem bathMarginal_Pin : bathMarginal Pin = reset := by
  funext z
  unfold bathMarginal
  have hz : (∑ r, Pin (r, z)) = (∑ r, unif r) * reset z := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun r _ => rfl)
  rw [hz, sum_unif, one_mul]

/-- Proves: the output bath marginal is the fair bit, `bathMarginal Pout = unif`. The bath has absorbed
  the bit: `∑ r, unif z * reset r = unif z * (∑ r, reset r)`. -/
theorem bathMarginal_Pout : bathMarginal Pout = unif := by
  funext z
  unfold bathMarginal
  have hz : (∑ r, Pout (r, z)) = unif z * (∑ r, reset r) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r _ => Pout_apply r z)
  rw [hz, sum_reset, mul_one]

/-- Proves: the bath starts at entropy `0`. `H (bathMarginal Pin) = 0`. -/
theorem H_bathMarginal_Pin : H (bathMarginal Pin) = 0 := by
  rw [bathMarginal_Pin]; exact H_pointMass (0 : Fin 2)

/-- Proves: the bath ends at entropy `log 2`: it has absorbed the erased bit.
  `H (bathMarginal Pout) = log 2`. -/
theorem H_bathMarginal_Pout : H (bathMarginal Pout) = Real.log 2 := by
  rw [bathMarginal_Pout]; exact H_uniformFin2

/-! ### Total joint entropy is conserved by the reversible SWAP. -/

/-- Proves: the reversible SWAP conserves total joint Shannon entropy, `H Pout = H Pin`. This is item
  (1), `entropy_invariant_under_equiv`, applied to the permutation `swap.symm` of `Fin 2 × Fin 2`: the
  output joint is exactly the input joint reindexed along a bijection, so the finite entropy sum is
  unchanged. No marginal independence or subadditivity is invoked; it is the exact permutation law.
Relation: not applicable. Closure: not applicable. Trust: kernel-only. -/
theorem H_Pout_eq_H_Pin : H Pout = H Pin := by
  have h := entropy_invariant_under_equiv swap.symm Pin
  simpa [Pout] using h

/-! ## 3. The erasure entropy ledger -/

/--
Proves: constructive Landauer on the finite space `Fin 2 × Fin 2`, bundled. For the reversible-SWAP
  erasure model:
  (1) the register loses exactly `log 2`: its entropy goes `log 2 → 0`;
  (2) the bath gains exactly `log 2`: its entropy goes `0 → log 2`;
  (3) the total joint entropy is conserved: `H Pout = H Pin`.
  Reading (1)+(2)+(3) together: the one erased bit (`log 2` removed from the register) is paid for by
  an exactly equal `log 2` increase in the bath, with no net change in total entropy. This is the
  information-ledger form of the Landauer principle, proved constructively on a finite probability
  space with only `Equiv` reindexing and the two base entropy values.
Does not prove: that this floor is dissipated heat; the thermodynamic identification is conditional and
  kept in `ConfessionLandauerSplit`. The per-bit thermodynamic floor is tied to the erased bit in
  `erased_bit_bears_landauer_floor`.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel-only. Scope: the concrete `Fin 2 × Fin 2` reversible-swap model.
-/
theorem erasure_entropy_ledger :
    (H (regMarginal Pin) = Real.log 2 ∧ H (regMarginal Pout) = 0)
    ∧ (H (bathMarginal Pin) = 0 ∧ H (bathMarginal Pout) = Real.log 2)
    ∧ H Pout = H Pin :=
  ⟨⟨H_regMarginal_Pin, H_regMarginal_Pout⟩,
   ⟨H_bathMarginal_Pin, H_bathMarginal_Pout⟩,
   H_Pout_eq_H_Pin⟩

/-- Proves: the bath-entropy increase exactly equals the register-entropy decrease, both `log 2`. The
  erased bit is conserved, not destroyed: the register's lost `log 2` reappears as the bath's gained
  `log 2`. This is the explicit "paid for by an equal bath increase" reading of the ledger. -/
theorem bath_gain_eq_register_loss :
    H (bathMarginal Pout) - H (bathMarginal Pin)
      = H (regMarginal Pin) - H (regMarginal Pout) := by
  rw [H_bathMarginal_Pout, H_bathMarginal_Pin, H_regMarginal_Pin, H_regMarginal_Pout]

/-! ## 4. The one erased bit bears the exact Landauer floor `kB·T·log 2` -/

/--
Proves: the single bit erased by the reversible-SWAP model bears exactly the Landauer floor
  `kB·T·log 2`. Specializing `ConfessionLandauerExact.landauerLowerBound_eq_perBit_mul_bits` to the
  one-bit `recursorConfessionEvent 0` (`reliableRecordBitCount = 1`), the defined floor is
  `kB·T·log 2 · 1 = kB·T·log 2`. This is the thermodynamic price of the exactly-one bit whose `log 2`
  of register entropy was shown (in `erasure_entropy_ledger`) to be transferred to the bath.
Does not prove: that this floor is released heat (conditional; see `ConfessionLandauerSplit`); only the
  closed-form value of the defined floor for the one-bit case, tied to the single erased bit of the
  finite model.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel-only (imported `ConfessionLandauerExact` floor + `reliableRecordBitCount = 1`).
Scope: the one-bit confession event; the defined floor quantity, not released heat.
-/
theorem erased_bit_bears_landauer_floor (kB T : ℝ) :
    landauerLowerBound (recursorConfessionEvent 0) kB T = kB * T * Real.log 2 := by
  rw [landauerLowerBound_eq_perBit_mul_bits, oneBit_reliableRecordBitCount]
  simp

/-! ## Axiom inventory (must each be a subset of `{propext, Classical.choice, Quot.sound}`) -/

#print axioms entropy_invariant_under_equiv
#print axioms erasure_entropy_ledger
#print axioms H_Pout_eq_H_Pin
#print axioms erased_bit_bears_landauer_floor

/-! ## Headline `#check`s -/

#check @entropy_invariant_under_equiv
#check @erasure_entropy_ledger
#check @erased_bit_bears_landauer_floor

end OperatorKO7.Meta.Physics.LandauerErasureFinite
