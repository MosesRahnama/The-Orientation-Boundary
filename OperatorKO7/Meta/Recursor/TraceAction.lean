import OperatorKO7.Meta.Recursor.TraceInvariants

/-!
# Trace action and confession partitions

Laws 3 and 4.  The division-free identities are primary; asymptotic readings
in the manuscript are consequences of these exact natural-number equalities.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Recursor.TraceAction

open Finset
open SchemaTraceKernel
open TraceInvariants

def tri : Nat -> Nat
  | 0 => 0
  | n + 1 => tri n + (n + 1)

theorem two_mul_tri (n : Nat) : 2 * tri n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [tri, Nat.mul_add]
      nlinarith

/-- Live-trace action functional. This is a cost along the displayed trace, not an invariant action
functional over all transformed proof objects. The legacy name `traceAction` is kept for downstream
compatibility. -/
def traceAction (k w cstar : Nat) : Nat :=
  tri k * (w + 1) + (k + 1) * cstar

/-- Clarified alias for `traceAction`: the quantity is computed on the live trace. -/
def liveTraceAction (k w cstar : Nat) : Nat :=
  traceAction k w cstar

/-- The clarified alias is definitionally the legacy trace-action functional. -/
theorem liveTraceAction_eq_traceAction (k w cstar : Nat) :
    liveTraceAction k w cstar = traceAction k w cstar := rfl

def conMassCell (k w : Nat) : Nat := tri k * w

def conMassPayManuscript (k beta : Nat) : Nat := tri (k + 1) * beta

theorem sum_range_id_eq_tri (k : Nat) :
    (Finset.range (k + 1)).sum (fun i => i) = tri k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      rfl

theorem sum_range_k_sub_eq_tri (k : Nat) :
    (Finset.range (k + 1)).sum (fun i => k - i) = tri k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have hpoint : forall i, i ∈ Finset.range (k + 1) ->
          (k + 1 - i) = (k - i) + 1 := by
        intro i hi
        simp only [Finset.mem_range] at hi
        omega
      rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
        Nat.sub_self, Nat.add_zero]
      rw [ih]
      rfl

theorem formula_sum_bridge (k w cstar : Nat) :
    (Finset.range (k + 1)).sum
        (fun i => i * w + (k - i) + cstar) = traceAction k w cstar := by
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_mul, sum_range_id_eq_tri, sum_range_k_sub_eq_tri]
  simp [traceAction, Nat.mul_add, Nat.add_mul, Finset.sum_const]

/-- Law 3: the syntactic sum has the exact division-free closed form. -/
theorem L3_action_syntactic
    (alpha beta gamma phi zeta ia ib k : Nat) :
    2 * (Finset.range (k + 1)).sum (fun i =>
      wsize alpha beta gamma phi zeta
        (orbitState (.base ia) (.pay ib) k i)) =
      k * (k + 1) * (gamma + beta + 1) +
        2 * (k + 1) * (phi + alpha + beta + zeta) := by
  have hpoint : forall i, i ∈ Finset.range (k + 1) ->
      wsize alpha beta gamma phi zeta
          (orbitState (.base ia) (.pay ib) k i) =
        i * (gamma + beta) + (k - i) +
          (phi + alpha + beta + zeta) := by
    intro i hi
    apply wsize_closed_form
    simp only [Finset.mem_range] at hi
    omega
  rw [Finset.sum_congr rfl hpoint,
    formula_sum_bridge k (gamma + beta) (phi + alpha + beta + zeta)]
  unfold traceAction
  rw [Nat.mul_add, ← Nat.mul_assoc, two_mul_tri]
  ring

/-- Law 3 generic closed form. -/
theorem L3_action_closed (k w cstar : Nat) :
    2 * traceAction k w cstar =
      k * (k + 1) * (w + 1) + 2 * (k + 1) * cstar := by
  unfold traceAction
  rw [Nat.mul_add, ← Nat.mul_assoc, two_mul_tri]
  ring

/-- Law 3 bridge from the closed functional to the syntax sum. -/
theorem L3_action_bridge
    (alpha beta gamma phi zeta ia ib k : Nat) :
    traceAction k (gamma + beta) (phi + alpha + beta + zeta) =
      (Finset.range (k + 1)).sum (fun i =>
        wsize alpha beta gamma phi zeta
          (orbitState (.base ia) (.pay ib) k i)) := by
  calc
    traceAction k (gamma + beta) (phi + alpha + beta + zeta) =
        (Finset.range (k + 1)).sum (fun i =>
          i * (gamma + beta) + (k - i) + (phi + alpha + beta + zeta)) :=
      (formula_sum_bridge k (gamma + beta) (phi + alpha + beta + zeta)).symm
    _ = (Finset.range (k + 1)).sum (fun i =>
        wsize alpha beta gamma phi zeta
          (orbitState (.base ia) (.pay ib) k i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      symm
      apply wsize_closed_form
      simp only [Finset.mem_range] at hi
      omega

/-- Law 3 integer envelope encoding the second quadratic invariant. -/
theorem L3_second_quadratic_invariant (k w cstar : Nat) :
    k * k * (w + 1) <= 2 * traceAction k w cstar ∧
      2 * traceAction k w cstar <=
        k * k * (w + 1) + (k + 1) * (w + 1) +
          2 * (k + 1) * cstar := by
  rw [L3_action_closed]
  constructor <;> nlinarith

/-- Law 4: exact partition between wrapper-cell mass and retained trace mass. -/
theorem L4_partition_identity (k w cstar : Nat) :
    w * (2 * traceAction k w cstar) =
      (w + 1) * (2 * conMassCell k w) +
        2 * w * (k + 1) * cstar := by
  have hcon : 2 * conMassCell k w = k * (k + 1) * w := by
    unfold conMassCell
    rw [← Nat.mul_assoc, two_mul_tri]
  rw [L3_action_closed, hcon]
  ring

/-- Law 4 exact residual and one-sided fraction envelope. -/
theorem L4_fraction_envelope (k w cstar : Nat) :
    w * (2 * traceAction k w cstar) =
        (w + 1) * (2 * conMassCell k w) +
          2 * w * (k + 1) * cstar ∧
      conMassCell k w * (w + 1) <= traceAction k w cstar * w := by
  constructor
  · exact L4_partition_identity k w cstar
  · have h := L4_partition_identity k w cstar
    have hle :
        (w + 1) * (2 * conMassCell k w) <=
          w * (2 * traceAction k w cstar) := by
      rw [h]
      exact Nat.le_add_right _ _
    have hle' :
        2 * (conMassCell k w * (w + 1)) <=
          2 * (traceAction k w cstar * w) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hle
    exact Nat.le_of_mul_le_mul_left hle' (by decide)

/-- Law 4: exact closed form of the manuscript's payload confession mass. -/
theorem L4_manuscript_con (k beta : Nat) :
    2 * conMassPayManuscript k beta = (k + 1) * (k + 2) * beta := by
  unfold conMassPayManuscript
  rw [← Nat.mul_assoc, two_mul_tri]

/-- Law 4: division-free lower and upper envelopes for confession dominance. -/
theorem L4_dominance_ratio (k beta : Nat) :
    k * k * beta <= 2 * conMassPayManuscript k beta ∧
      2 * conMassPayManuscript k beta <= (k + 2) * (k + 2) * beta := by
  rw [L4_manuscript_con]
  constructor <;> nlinarith

theorem sample_trace_action : traceAction 3 3 6 = 48 := by decide

theorem sample_con_mass_cell : conMassCell 3 3 = 18 := by decide

theorem sample_partition :
    3 * (2 * traceAction 3 3 6) =
      4 * (2 * conMassCell 3 3) + 2 * 3 * 4 * 6 := by decide

theorem sample_manuscript_con : conMassPayManuscript 3 2 = 20 := by decide

end OperatorKO7.Meta.Recursor.TraceAction
