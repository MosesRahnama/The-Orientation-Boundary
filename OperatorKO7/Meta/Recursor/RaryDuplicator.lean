import OperatorKO7.Meta.Recursor.GaugeCost
import OperatorKO7.Meta.RecordEmissionNecessity

/-!
# The r-ary duplicator model

The defined rewrite relation emits `r` copies of its payload at each recursive step. The file proves
runtime, payload-count, and arithmetic mass formulas for that relation. Its architectural section
counts generator positions in the specifically constructed term `multiFrameRhs`; it does not prove a
necessity theorem for arbitrary r-ary duplicator encodings.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Recursor.RaryDuplicator

open GaugeCost
open TraceAction

inductive RTerm where
  | Z : RTerm
  | S : RTerm -> RTerm
  | base : Nat -> RTerm
  | pay : Nat -> RTerm
  | F : RTerm -> RTerm -> RTerm -> RTerm
  | G : List RTerm -> RTerm -> RTerm
deriving Repr

inductive RStep (r : Nat) : RTerm -> RTerm -> Prop where
  | baseRule (x y : RTerm) : RStep r (.F x y .Z) x
  | stepRule (x y n : RTerm) :
      RStep r (.F x y (.S n)) (.G (List.replicate r y) (.F x y n))
  | congG (ys : List RTerm) (t t' : RTerm) :
      RStep r t t' -> RStep r (.G ys t) (.G ys t')

def RNormal (r : Nat) (t : RTerm) : Prop := forall u, Not (RStep r t u)

theorem RStep.functional {r : Nat} {t u v : RTerm}
    (hu : RStep r t u) (hv : RStep r t v) : u = v := by
  induction hu generalizing v with
  | baseRule x y => cases hv; rfl
  | stepRule x y n => cases hv; rfl
  | congG ys t t' h ih =>
      cases hv with
      | congG _ _ v' hv' => exact congrArg (RTerm.G ys) (ih hv')

def rSPow : Nat -> RTerm
  | 0 => .Z
  | n + 1 => .S (rSPow n)

def rGPow (ys : List RTerm) : Nat -> RTerm -> RTerm
  | 0, t => t
  | i + 1, t => .G ys (rGPow ys i t)

def rOrbit (a b : RTerm) (k r i : Nat) : RTerm :=
  if i <= k then
    rGPow (List.replicate r b) i (.F a b (rSPow (k - i)))
  else rGPow (List.replicate r b) k a

def countPayR : RTerm -> Nat
  | .Z => 0
  | .S n => countPayR n
  | .base _ => 0
  | .pay _ => 1
  | .F x y n => countPayR x + countPayR y + countPayR n
  | .G ys t => (ys.map countPayR).sum + countPayR t

theorem rGPow_succ_right (ys : List RTerm) (t : RTerm) (i : Nat) :
    rGPow ys i (.G ys t) = rGPow ys (i + 1) t := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [rGPow, ih]

theorem rstep_rGPow (r : Nat) (ys : List RTerm) {t u : RTerm} (i : Nat)
    (h : RStep r t u) : RStep r (rGPow ys i t) (rGPow ys i u) := by
  induction i with
  | zero => exact h
  | succ i ih => exact RStep.congG ys _ _ ih

theorem rstep_from_rGPow (r : Nat) (ys : List RTerm) {t u : RTerm} (i : Nat)
    (h : RStep r (rGPow ys i t) u) :
    Exists fun v => RStep r t v ∧ u = rGPow ys i v := by
  induction i generalizing u with
  | zero => exact ⟨u, h, rfl⟩
  | succ i ih =>
      cases h with
      | congG _ _ u' hinner =>
          obtain ⟨v, htv, rfl⟩ := ih hinner
          exact ⟨v, htv, rfl⟩

theorem rbase_normal (r ia : Nat) : RNormal r (.base ia) := by
  intro u h
  cases h

theorem rnormal_rGPow (r : Nat) (ys : List RTerm) (t : RTerm) (i : Nat)
    (ht : RNormal r t) :
    RNormal r (rGPow ys i t) := by
  intro u h
  obtain ⟨v, htv, _⟩ := rstep_from_rGPow r ys i h
  exact ht v htv

theorem rOrbit_step (a b : RTerm) (k r i : Nat) (hi : i <= k) :
    RStep r (rOrbit a b k r i) (rOrbit a b k r (i + 1)) := by
  by_cases hlt : i < k
  · have hi1 : i + 1 <= k := by omega
    have hsub : k - i = (k - (i + 1)) + 1 := by omega
    rw [rOrbit, if_pos hi, rOrbit, if_pos hi1, hsub]
    simp only [rSPow]
    have hroot := RStep.stepRule (r := r) a b (rSPow (k - (i + 1)))
    simpa only [rGPow_succ_right] using
      rstep_rGPow r (List.replicate r b) i hroot
  · have hik : i = k := by omega
    subst i
    rw [rOrbit, if_pos (le_refl k), rOrbit, if_neg (by omega)]
    simp only [Nat.sub_self, rSPow]
    exact rstep_rGPow r (List.replicate r b) k (RStep.baseRule a b)

inductive RStepsTo (r : Nat) : RTerm -> Nat -> RTerm -> Prop where
  | refl (t : RTerm) : RStepsTo r t 0 t
  | step {t u v : RTerm} {n : Nat} :
      RStep r t u -> RStepsTo r u n v -> RStepsTo r t (n + 1) v

theorem RStepsTo.normal_unique {r : Nat} {t u v : RTerm} {n m : Nat}
    (h1 : RStepsTo r t n u) (hu : RNormal r u)
    (h2 : RStepsTo r t m v) (hv : RNormal r v) :
    n = m ∧ u = v := by
  induction h1 generalizing m v with
  | refl t =>
      cases h2 with
      | refl => exact ⟨rfl, rfl⟩
      | step h _ => exact False.elim (hu _ h)
  | @step t t' u n hstep hrest ih =>
      cases h2 with
      | refl => exact False.elim (hv _ hstep)
      | @step _ v' v m hstep' hrest' =>
          have heq : t' = v' := RStep.functional hstep hstep'
          subst v'
          obtain ⟨hn, huv⟩ := ih hu hrest' hv
          exact ⟨congrArg (fun q => q + 1) hn, huv⟩

theorem rCanonical_steps_from_aux (a b : RTerm) (k r : Nat) :
    forall d i, i <= k -> k - i = d ->
      RStepsTo r (rOrbit a b k r i) (d + 1) (rOrbit a b k r (k + 1)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro i hi hd
      cases d with
      | zero =>
          have hik : i = k := by omega
          subst i
          exact RStepsTo.step (rOrbit_step a b k r k (le_refl k)) (RStepsTo.refl _)
      | succ d =>
          have hi1 : i + 1 <= k := by omega
          have hnext : k - (i + 1) = d := by omega
          have htail := ih d (by omega) (i + 1) hi1 hnext
          exact RStepsTo.step (rOrbit_step a b k r i hi) htail

theorem rCanonical_steps (ia ib k r : Nat) :
    RStepsTo r (rOrbit (.base ia) (.pay ib) k r 0) (k + 1)
      (rOrbit (.base ia) (.pay ib) k r (k + 1)) := by
  simpa using rCanonical_steps_from_aux (.base ia) (.pay ib) k r k 0
    (Nat.zero_le k) rfl

theorem rOrbit_terminal_normal (ia ib k r : Nat) :
    RNormal r (rOrbit (.base ia) (.pay ib) k r (k + 1)) := by
  rw [rOrbit, if_neg (by omega)]
  exact rnormal_rGPow r (List.replicate r (.pay ib)) (.base ia) k
    (rbase_normal r ia)

theorem countPayR_rSPow (n : Nat) : countPayR (rSPow n) = 0 := by
  induction n with
  | zero => simp [rSPow, countPayR]
  | succ n ih => simpa [rSPow, countPayR] using ih

theorem countPayR_replicate (ib r : Nat) :
    ((List.replicate r (.pay ib)).map countPayR).sum = r := by
  simp [countPayR]

theorem countPayR_rGPow (ib r i : Nat) (t : RTerm) :
    countPayR (rGPow (List.replicate r (.pay ib)) i t) =
      i * r + countPayR t := by
  induction i with
  | zero => simp [rGPow]
  | succ i ih =>
      simp only [rGPow, countPayR, countPayR_replicate, ih, Nat.succ_mul]
      omega

/-- Law 10 trace law: payload multiplicity is `r*i+1` at every live state. -/
theorem L10_trace_law_r (ia ib k r i : Nat) (hi : i <= k) :
    countPayR (rOrbit (.base ia) (.pay ib) k r i) = r * i + 1 := by
  rw [rOrbit, if_pos hi, countPayR_rGPow]
  simp [countPayR, countPayR_rSPow, Nat.mul_comm]

/-- Law 10 runtime: derivation length is independent of payload and `r`. -/
theorem L10_runtime_r_blind (ia ib ia' ib' k r r' : Nat) :
    RStepsTo r (rOrbit (.base ia) (.pay ib) k r 0) (k + 1)
        (rOrbit (.base ia) (.pay ib) k r (k + 1)) ∧
      RStepsTo r' (rOrbit (.base ia') (.pay ib') k r' 0) (k + 1)
        (rOrbit (.base ia') (.pay ib') k r' (k + 1)) :=
  ⟨rCanonical_steps ia ib k r, rCanonical_steps ia' ib' k r'⟩

/-- Law 10 maximality: every r-ary derivation ending normally has length `k+1`. -/
theorem L10_runtime_unique (ia ib k r n : Nat) (u : RTerm)
    (h : RStepsTo r (rOrbit (.base ia) (.pay ib) k r 0) n u)
    (hu : RNormal r u) :
    n = k + 1 ∧ u = rOrbit (.base ia) (.pay ib) k r (k + 1) := by
  exact RStepsTo.normal_unique h hu (rCanonical_steps ia ib k r)
    (rOrbit_terminal_normal ia ib k r)

def conMassR (k beta r : Nat) : Nat :=
  r * tri k * beta + (k + 1) * beta

/-- Law 10 exact cumulative payload mass for the r-ary family. -/
theorem L10_con_r_closed (k beta r : Nat) :
    2 * conMassR k beta r =
      beta * (r * k * (k + 1) + 2 * (k + 1)) := by
  have htri := two_mul_tri k
  unfold conMassR
  calc
    2 * (r * tri k * beta + (k + 1) * beta) =
        r * (2 * tri k) * beta + 2 * (k + 1) * beta := by ring
    _ = beta * (r * k * (k + 1) + 2 * (k + 1)) := by rw [htri]; ring

/-- Law 10 integer envelope encoding linear scaling in duplication order. -/
theorem L10_scaling_envelope (k beta r : Nat) :
    r * beta * k * k <= 2 * conMassR k beta r ∧
      2 * conMassR k beta r <=
        r * beta * (k + 1) * (k + 1) + 2 * (k + 1) * beta := by
  rw [L10_con_r_closed]
  have hrhs :
      beta * (r * k * (k + 1) + 2 * (k + 1)) =
        r * beta * k * (k + 1) + 2 * (k + 1) * beta := by ring
  rw [hrhs]
  constructor
  · have hmain : r * beta * k * k <= r * beta * k * (k + 1) := by
      exact Nat.mul_le_mul_left (r * beta * k) (Nat.le_succ k)
    exact hmain.trans (Nat.le_add_right _ _)
  · have hmain : r * beta * k * (k + 1) <=
        r * beta * (k + 1) * (k + 1) := by
      have hk := Nat.mul_le_mul_left (r * beta) (Nat.le_succ k)
      exact Nat.mul_le_mul_right (k + 1) hk
    exact Nat.add_le_add_right hmain _

/-- Law 10 gauge pair: carrier multiplicity scales with `r`, projection storage does not. -/
theorem L10_gauge_r (ia ib k r i : Nat) (hi : i <= k) :
    countPayR (rOrbit (.base ia) (.pay ib) k r i) = r * i + 1 ∧
      k < 2 ^ projBits k :=
  ⟨L10_trace_law_r ia ib k r i hi, (L8_projection_comparison k).1⟩

namespace Architectural

open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.RecordTerm

def emitFrames : Nat -> RecordTerm -> RecordTerm
  | 0, t => t
  | m + 1, t => .frame .gen (emitFrames m t)

def multiFrameRhs (m : Nat) (n : RecordCounter) : RecordTerm :=
  emitFrames m (.active .base .gen n)

theorem generatorPositions_emitFrames (m : Nat) (t : RecordTerm) :
    (generatorPositions (emitFrames m t)).length =
      m + (generatorPositions t).length := by
  induction m with
  | zero => simp [emitFrames]
  | succ m ih => simp [emitFrames, generatorPositions, ih, Nat.add_assoc]; omega

theorem multiFrameRhs_generator_count (m : Nat) (n : RecordCounter) :
    (generatorPositions (multiFrameRhs m n)).length = m + 1 := by
  simp [multiFrameRhs, generatorPositions_emitFrames, generatorPositions]

theorem multiFrameRhs_emits (m : Nat) (n : RecordCounter) (hm : 1 <= m) :
    emitsNewRecordFrame (multiFrameRhs m n) := by
  cases m with
  | zero => omega
  | succ m => simp [multiFrameRhs, emitFrames, emitsNewRecordFrame]

theorem multiFrameRhs_preserves (m : Nat) (n : RecordCounter) :
    preservesRecursiveGenerator (multiFrameRhs m n) := by
  induction m with
  | zero => simp [multiFrameRhs, emitFrames, preservesRecursiveGenerator]
  | succ m ih => simpa [multiFrameRhs, emitFrames, preservesRecursiveGenerator] using ih

/-- In the constructed term `multiFrameRhs m n`, the `m` frames and active site yield `m + 1`
generator positions; for positive `m`, two distinct positions exist. -/
theorem L10_architectural_r (m : Nat) (n : RecordCounter) (hm : 1 <= m) :
    (generatorPositions (multiFrameRhs m n)).length = m + 1 ∧
      exists p q,
        p ≠ q ∧ p ∈ generatorPositions (multiFrameRhs m n) ∧
          q ∈ generatorPositions (multiFrameRhs m n) := by
  refine ⟨multiFrameRhs_generator_count m n, ?_⟩
  rcases architectural_necessity_of_payload_duplication
      (multiFrameRhs_emits m n hm) (multiFrameRhs_preserves m n) with
    ⟨p, q, hpq, hp, hq, _, _⟩
  exact ⟨p, q, hpq, hp, hq⟩

end Architectural

theorem sample_rary_mass : conMassR 3 2 2 = 32 := by decide

theorem sample_rary_payload_count :
    countPayR (rOrbit (.base 0) (.pay 1) 3 2 2) = 5 := by
  norm_num [rOrbit, rGPow, rSPow, countPayR]

/-- Concrete negative discriminator: unary and binary duplication differ at stage two. -/
theorem binary_not_unary_at_stage_two :
    countPayR (rOrbit (.base 0) (.pay 1) 3 2 2) ≠
      countPayR (rOrbit (.base 0) (.pay 1) 3 1 2) := by
  norm_num [rOrbit, rGPow, rSPow, countPayR]

end OperatorKO7.Meta.Recursor.RaryDuplicator
