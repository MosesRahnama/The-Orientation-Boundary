import OperatorKO7.Meta.SchemaConfessionDominance
import OperatorKO7.Meta.Recursor.TraceAction

/-!
# Asymptotic clauses of the trace laws

Limits the paper states for the canonical trace: the trace action over the
squared depth, the proof-entropy fraction with the paper's constant
`c* = c0 + |b|`, the share of completed wrapper-cell mass in the trace action,
and the crossover stage over the depth. Each limit is read off an exact
identity already proved for the trace.
-/

namespace OperatorKO7.Meta.OperationalInexpressibility.ClaimAsymptotics

open Filter
open OperatorKO7.Meta.Recursor.TraceAction
open OperatorKO7.Meta.Recursor.TraceInvariants
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem

/-- The trace action over the squared depth tends to `(w + 1) / 2`. -/
theorem traceAction_div_sq_tendsto (w c : Nat) :
    Tendsto (fun k : ℕ => (traceAction k w c : ℝ) / (k : ℝ) ^ 2) atTop
      (nhds (((w : ℝ) + 1) / 2)) := by
  have h1 : Tendsto (fun k : ℕ => (1 : ℝ) / k) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hA1 : Tendsto (fun k : ℕ => (1 : ℝ) + 1 / (k : ℝ)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add h1
  have hB1 : Tendsto (fun k : ℕ => 1 / (k : ℝ) + 1 / (k : ℝ) * (1 / (k : ℝ))) atTop
      (nhds 0) := by
    simpa using h1.add (h1.mul h1)
  have hlim : Tendsto (fun k : ℕ => ((w : ℝ) + 1) / 2 * ((1 : ℝ) + 1 / (k : ℝ)) +
      (c : ℝ) * (1 / (k : ℝ) + 1 / (k : ℝ) * (1 / (k : ℝ)))) atTop
      (nhds (((w : ℝ) + 1) / 2)) := by
    simpa using (hA1.const_mul (((w : ℝ) + 1) / 2)).add (hB1.const_mul (c : ℝ))
  refine hlim.congr' (eventually_atTop.2 ⟨1, fun k hk => ?_⟩)
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hA : (2 : ℝ) * traceAction k w c = (k : ℝ) * (k + 1) * (w + 1) + 2 * (k + 1) * c := by
    exact_mod_cast L3_action_closed k w c
  have hA' : (traceAction k w c : ℝ) =
      ((k : ℝ) * (k + 1) * (w + 1) + 2 * (k + 1) * c) / 2 := by
    linarith
  dsimp only
  rw [hA']
  field_simp
  ring

/-- With the paper's constant `c* = c0 + |b|`, the proof-entropy fraction of a
stage `i ≥ 1` tends to `i / (i + 1)` as the payload size grows. -/
theorem proof_entropy_tendsto_ratio (k i wrapSize c0 : Nat) (hi : 1 ≤ i) :
    Tendsto (fun p : ℕ => proofEntropyValue k i p wrapSize (c0 + p)) atTop
      (nhds ((i : ℝ) / ((i : ℝ) + 1))) := by
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = i * wrapSize + (k - i) + c0 := ⟨_, rfl⟩
  have h1 : Tendsto (fun p : ℕ => (1 : ℝ) / p) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hden : Tendsto (fun p : ℕ => ((i : ℝ) + 1) + (D : ℝ) * (1 / (p : ℝ))) atTop
      (nhds ((i : ℝ) + 1)) := by
    simpa using (tendsto_const_nhds (x := (i : ℝ) + 1)).add (h1.const_mul (D : ℝ))
  have hlim : Tendsto (fun p : ℕ => (i : ℝ) / (((i : ℝ) + 1) + (D : ℝ) * (1 / (p : ℝ))))
      atTop (nhds ((i : ℝ) / ((i : ℝ) + 1))) :=
    (tendsto_const_nhds (x := (i : ℝ))).div hden (by positivity)
  refine hlim.congr' (eventually_atTop.2 ⟨1, fun p hp => ?_⟩)
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have htot : (proofEntropyTotalSize k i p wrapSize (c0 + p) : ℝ) = ((i : ℝ) + 1) * p + D := by
    have hnat : proofEntropyTotalSize k i p wrapSize (c0 + p) = (i + 1) * p + D := by
      rw [hD]
      unfold proofEntropyTotalSize
      ring
    rw [hnat]
    push_cast
    ring
  have hpos : ((i : ℝ) + 1) * p + D ≠ 0 := by positivity
  have hden0 : ((i : ℝ) + 1) + (D : ℝ) * (1 / (p : ℝ)) ≠ 0 := by positivity
  simp only [proofEntropyValue, htot]
  field_simp

/-- The completed wrapper-cell mass is asymptotically the fraction `w / (w + 1)`
of the trace action. -/
theorem conMassCell_div_traceAction_tendsto (w c : Nat) :
    Tendsto (fun k : ℕ => (conMassCell k w : ℝ) / (traceAction k w c : ℝ)) atTop
      (nhds ((w : ℝ) / ((w : ℝ) + 1))) := by
  have h1 : Tendsto (fun k : ℕ => (1 : ℝ) / k) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hden : Tendsto (fun k : ℕ => ((w : ℝ) + 1) + 2 * (c : ℝ) * (1 / (k : ℝ))) atTop
      (nhds ((w : ℝ) + 1)) := by
    simpa using (tendsto_const_nhds (x := (w : ℝ) + 1)).add (h1.const_mul (2 * (c : ℝ)))
  have hlim : Tendsto (fun k : ℕ => (w : ℝ) / (((w : ℝ) + 1) + 2 * (c : ℝ) * (1 / (k : ℝ))))
      atTop (nhds ((w : ℝ) / ((w : ℝ) + 1))) :=
    (tendsto_const_nhds (x := (w : ℝ))).div hden (by positivity)
  refine hlim.congr' (eventually_atTop.2 ⟨1, fun k hk => ?_⟩)
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have htri : (2 : ℝ) * tri k = (k : ℝ) * (k + 1) := by exact_mod_cast two_mul_tri k
  have hC : (conMassCell k w : ℝ) = (k : ℝ) * (k + 1) * w / 2 := by
    have hcast : (conMassCell k w : ℝ) = (tri k : ℝ) * w := by simp [conMassCell]
    have htri' : (tri k : ℝ) = (k : ℝ) * (k + 1) / 2 := by linarith
    rw [hcast, htri']
    ring
  have hA : (traceAction k w c : ℝ) = ((k : ℝ) * (k + 1) * (w + 1) + 2 * (k + 1) * c) / 2 := by
    have h' : (2 : ℝ) * traceAction k w c = (k : ℝ) * (k + 1) * (w + 1) + 2 * (k + 1) * c := by
      exact_mod_cast L3_action_closed k w c
    linarith
  have hApos : (k : ℝ) * (k + 1) * (w + 1) + 2 * (k + 1) * c ≠ 0 := by
    have hprod : 0 < (k : ℝ) * (k + 1) * (w + 1) :=
      mul_pos (mul_pos hkpos (by positivity)) (by positivity)
    have hrest : 0 ≤ 2 * ((k : ℝ) + 1) * c := by positivity
    exact (add_pos_of_pos_of_nonneg hprod hrest).ne'
  have hden0 : ((w : ℝ) + 1) + 2 * (c : ℝ) * (1 / (k : ℝ)) ≠ 0 := by positivity
  dsimp only
  rw [hC, hA]
  field_simp
  ring

/-- The crossover stage over the depth tends to `1 / (w + 1)`. -/
theorem istar_div_tendsto (c w : Nat) (hw : 1 ≤ w) :
    Tendsto (fun k : ℕ => (istar k c w : ℝ) / k) atTop (nhds (1 / ((w : ℝ) + 1))) := by
  have h1 : Tendsto (fun k : ℕ => (1 : ℝ) / k) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hlow : Tendsto (fun k : ℕ => 1 / ((w : ℝ) + 1) * (1 + (c : ℝ) * (1 / (k : ℝ))))
      atTop (nhds (1 / ((w : ℝ) + 1))) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add (h1.const_mul (c : ℝ))).const_mul
      (1 / ((w : ℝ) + 1))
  have hup : Tendsto (fun k : ℕ => 1 / ((w : ℝ) + 1) * (1 + ((c : ℝ) + w) * (1 / (k : ℝ))))
      atTop (nhds (1 / ((w : ℝ) + 1))) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add
      (h1.const_mul ((c : ℝ) + w))).const_mul (1 / ((w : ℝ) + 1))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hl : ((k : ℝ) + c) ≤ (istar k c w : ℝ) * ((w : ℝ) + 1) := by
      exact_mod_cast (L5_fraction k c w hw).1
    rw [le_div_iff₀ hk0]
    have e : 1 / ((w : ℝ) + 1) * (1 + (c : ℝ) * (1 / (k : ℝ))) * k =
        ((k : ℝ) + c) / ((w : ℝ) + 1) := by
      field_simp
      ring
    rw [e, div_le_iff₀ (by positivity)]
    exact hl
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hu : (istar k c w : ℝ) * ((w : ℝ) + 1) ≤ (k : ℝ) + c + w := by
      exact_mod_cast (L5_fraction k c w hw).2
    rw [div_le_iff₀ hk0]
    have e : 1 / ((w : ℝ) + 1) * (1 + ((c : ℝ) + w) * (1 / (k : ℝ))) * k =
        ((k : ℝ) + c + w) / ((w : ℝ) + 1) := by
      field_simp
      ring
    rw [e, le_div_iff₀ (by positivity)]
    exact hu

end OperatorKO7.Meta.OperationalInexpressibility.ClaimAsymptotics
