import Mathlib.Logic.Relation
import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax

/-!
# Confluence of System T by Tait–Martin-Löf parallel reduction

This module proves that the carrier's full reduction `Step` is confluent, by the
Tait–Martin-Löf parallel reduction `Par` and Takahashi's complete development `dev`.
The calculus is orthogonal (left-linear, pairwise non-overlapping root patterns
`app (lam _ _) _`, `natrec _ _ zero`, `natrec _ _ (succ _)`), so the first-order
`eqW` distinction boundary has no counterpart here: there is no syntactic equality
tester and no critical overlap to freeze.

Relation: `Step` (the carrier's full contextual one-step reduction).
Closure: `StepStar` (reflexive-transitive closure of `Step`); `Par` is an auxiliary
one-parallel-step relation whose reflexive-transitive closure coincides with `StepStar`.
Strategy: full (every redex, every constructor context). Not `stepLO`.
Trust: kernel-only; no axioms beyond the Lean baseline.
Scope: every System T term (open and closed) of the shared carrier.

Does not prove: termination (lane L4) and nothing about extensions of the calculus
with a syntactic equality tester.

Shift and substitution algebra used by substitutivity of `Par` is proved in this
namespace under the prefix `par_`, so it does not collide with
`OperatorKO7.Meta.HigherOrderRewriting_Substitution` when that module lands.
-/

set_option autoImplicit false

namespace OperatorKO7.HigherOrderRewritingConfluence

open OperatorKO7.HigherOrderRewritingSystemT
open Relation

/-! ## Shift and substitution algebra (prefix `par_`) -/

private def par_shiftIdx (d c n : Nat) : Nat := if n < c then n else n + d

private theorem par_shiftIdx_zero (c n : Nat) : par_shiftIdx 0 c n = n := by
  unfold par_shiftIdx
  split_ifs <;> omega

private theorem par_shiftIdx_comp (d1 d2 c n : Nat) :
    par_shiftIdx d1 c (par_shiftIdx d2 c n) = par_shiftIdx (d1 + d2) c n := by
  unfold par_shiftIdx
  split_ifs <;> omega

private theorem par_shiftIdx_add (d e c n : Nat) :
    par_shiftIdx d (c + e) (par_shiftIdx e c n) = par_shiftIdx (d + e) c n := by
  unfold par_shiftIdx
  split_ifs <;> omega

private theorem par_shiftIdx_comm (d1 d2 c1 c2 n : Nat) (h : c1 ≤ c2) :
    par_shiftIdx d1 c1 (par_shiftIdx d2 c2 n) =
      par_shiftIdx d2 (c2 + d1) (par_shiftIdx d1 c1 n) := by
  unfold par_shiftIdx
  split_ifs <;> omega

private theorem par_shift_var (d c n : Nat) :
    shift d c (.var n) = .var (par_shiftIdx d c n) := by
  unfold shift par_shiftIdx
  split_ifs <;> rfl

private theorem par_shift_zero (c : Nat) (t : SysTTerm) : shift 0 c t = t := by
  induction t generalizing c with
  | var n => rw [par_shift_var, par_shiftIdx_zero]
  | lam A b ih => simp [shift, ih]
  | app f a ihf iha => simp [shift, ihf, iha]
  | zero => rfl
  | succ t ih => simp [shift, ih]
  | natrec z s n ihz ihs ihn => simp [shift, ihz, ihs, ihn]

/--
Proves: two shifts at the same cutoff compose by adding the distances.
Does not prove: commutation at distinct cutoffs.
Relation: equality of `shift`; not a rewrite relation.
Closure: not applicable.
Trust: kernel-only.
Scope: every pair of distances, every cutoff, every term.
-/
theorem par_shift_shift (d1 d2 c : Nat) (t : SysTTerm) :
    shift d1 c (shift d2 c t) = shift (d1 + d2) c t := by
  induction t generalizing c with
  | var n => simp [par_shift_var, par_shiftIdx_comp]
  | lam A b ih => simp [shift, ih]
  | app f a ihf iha => simp [shift, ihf, iha]
  | zero => rfl
  | succ t ih => simp [shift, ih]
  | natrec z s n ihz ihs ihn => simp [shift, ihz, ihs, ihn]

private theorem par_shift_shift_add (d e c : Nat) (t : SysTTerm) :
    shift d (c + e) (shift e c t) = shift (d + e) c t := by
  induction t generalizing c with
  | var n => simp [par_shift_var, par_shiftIdx_add]
  | lam A b ih =>
      simp [shift]
      have h := ih (c + 1)
      have heq : c + 1 + e = c + e + 1 := by omega
      rw [heq] at h
      exact h
  | app f a ihf iha => simp [shift, ihf, iha]
  | zero => rfl
  | succ t ih => simp [shift, ih]
  | natrec z s n ihz ihs ihn => simp [shift, ihz, ihs, ihn]

private theorem par_shift_shift_comm (d1 d2 c1 c2 : Nat) (h : c1 ≤ c2) (t : SysTTerm) :
    shift d1 c1 (shift d2 c2 t) = shift d2 (c2 + d1) (shift d1 c1 t) := by
  induction t generalizing c1 c2 with
  | var n => simp [par_shift_var, par_shiftIdx_comm d1 d2 c1 c2 n h]
  | lam A b ih =>
      simp [shift]
      have hih := ih (c1 + 1) (c2 + 1) (Nat.succ_le_succ h)
      have heq : c2 + 1 + d1 = c2 + d1 + 1 := by omega
      rw [heq] at hih
      exact hih
  | app f a ihf iha => simp [shift, ihf c1 c2 h, iha c1 c2 h]
  | zero => rfl
  | succ t ih => simp [shift, ih c1 c2 h]
  | natrec z s n ihz ihs ihn => simp [shift, ihz c1 c2 h, ihs c1 c2 h, ihn c1 c2 h]

private theorem par_shift_one_comm (d c : Nat) (t : SysTTerm) :
    shift d (c + 1) (shift 1 0 t) = shift 1 0 (shift d c t) :=
  (par_shift_shift_comm 1 d 0 c (Nat.zero_le c) t).symm

private theorem par_subst_shift_cancel (j : Nat) (u t : SysTTerm) :
    subst j u (shift 1 j t) = t := by
  induction t generalizing j u with
  | var n =>
      unfold shift subst
      by_cases h : n < j
      · simp [h]
      · have h1 : ¬ n + 1 < j := by omega
        have h2 : ¬ n + 1 = j := by omega
        simp [h, h1, h2]
  | lam A b ih => exact congrArg (SysTTerm.lam A) (ih (j + 1) (shift 1 0 u))
  | app f a ihf iha => simp [shift, subst, ihf, iha]
  | zero => rfl
  | succ t ih => simp [shift, subst, ih]
  | natrec z s n ihz ihs ihn => simp [shift, subst, ihz, ihs, ihn]

private theorem par_subst_shift_at (j k c : Nat) (hcj : c ≤ j) (v t : SysTTerm) :
    subst (j + k) (shift (k + c) 0 v) (shift k c t) =
      shift k c (subst j (shift c 0 v) t) := by
  induction t generalizing j k c v with
  | var n =>
      by_cases hnj : n < j
      · have hnjk : n < j + k := by omega
        by_cases hnc : n < c
        · simp [shift, subst, hnc, hnj, hnjk]
        · have hnadd : n + k < j + k := by omega
          simp [shift, subst, hnc, hnj, hnadd]
      · by_cases heq : n = j
        · rw [heq]
          have hge : ¬ j < c := by omega
          simp [shift, subst, hge]
          have hsc : shift k c (shift c 0 v) = shift (k + c) 0 v := by
            simpa using par_shift_shift_add k c 0 v
          exact hsc.symm
        · have _hgt : j < n := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hnj) (Ne.symm heq)
          have hge : ¬ n < c := by omega
          have hnadd_lt : ¬ (n + k) < (j + k) := by omega
          have hpred : ¬ n - 1 < c := by omega
          simp [shift, subst, hge, hnj, heq, hnadd_lt, hpred]
          have hidx : n + k - 1 = n - 1 + k := by omega
          simp [hidx]
  | lam A b ih =>
      have ih' := ih (j + 1) k (c + 1) (Nat.succ_le_succ hcj) v
      have h1 : shift 1 0 (shift (k + c) 0 v) = shift (k + c + 1) 0 v := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          par_shift_shift 1 (k + c) 0 v
      have h2 : shift 1 0 (shift c 0 v) = shift (c + 1) 0 v := by
        simpa [Nat.add_comm 1 c] using par_shift_shift 1 c 0 v
      have hjk : j + 1 + k = j + k + 1 := by omega
      have hkc : k + (c + 1) = k + c + 1 := by omega
      simp [shift, subst, h1, h2]
      rw [hjk, hkc] at ih'
      exact ih'
  | app f a ihf iha => simp [shift, subst, ihf j k c hcj v, iha j k c hcj v]
  | zero => rfl
  | succ t ih => simp [shift, subst, ih j k c hcj v]
  | natrec z s n ihz ihs ihn =>
      simp [shift, subst, ihz j k c hcj v, ihs j k c hcj v, ihn j k c hcj v]

private theorem par_subst_shift (j k : Nat) (v t : SysTTerm) :
    subst (j + k) (shift k 0 v) (shift k 0 t) = shift k 0 (subst j v t) := by
  have h := par_subst_shift_at j k 0 (Nat.zero_le j) v t
  simpa [Nat.add_zero, par_shift_zero] using h

/--
Proves: shifting a substitution at a hole at or below the cutoff equals substituting
the shifted term into the term shifted one extra binder.
Does not prove: the case `c < j`.
Relation: equality of `shift` and `subst`; not a rewrite relation.
Closure: not applicable.
Trust: kernel-only.
Scope: every term; hypothesis `j ≤ c`.
-/
theorem par_shift_subst (d c j : Nat) (hj : j ≤ c) (u t : SysTTerm) :
    shift d c (subst j u t) = subst j (shift d c u) (shift d (c + 1) t) := by
  induction t generalizing d c j u with
  | var n =>
      by_cases hnj : n < j
      · have hnc : n < c := Nat.lt_of_lt_of_le hnj hj
        have hnc1 : n < c + 1 := Nat.lt_succ_of_lt hnc
        simp [shift, subst, hnj, hnc, hnc1]
      · by_cases heq : n = j
        · rw [heq]
          have hnc1 : j < c + 1 := Nat.lt_succ_of_le hj
          simp [shift, subst, hnc1]
        · have hgt : j < n := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hnj) (Ne.symm heq)
          by_cases hnc : n - 1 < c
          · have hn : n < c + 1 := by omega
            simp [shift, subst, hnj, heq, hnc, hn]
          · have hn : ¬ n < c + 1 := by omega
            have hnjd_lt : ¬ n + d < j := by omega
            have hnjd_eq : ¬ n + d = j := by omega
            have : n - 1 + d = n + d - 1 := by omega
            simp [shift, subst, hnj, heq, hnc, hn, hnjd_lt, hnjd_eq, this]
  | lam A b ih =>
      have ih' := ih d (c + 1) (j + 1) (Nat.succ_le_succ hj) (shift 1 0 u)
      have hcomm : shift d (c + 1) (shift 1 0 u) = shift 1 0 (shift d c u) :=
        par_shift_one_comm d c u
      simp [shift, subst]
      rw [← hcomm]
      exact ih'
  | app f a ihf iha => simp [shift, subst, ihf d c j hj u, iha d c j hj u]
  | zero => rfl
  | succ t ih => simp [shift, subst, ih d c j hj u]
  | natrec z s n ihz ihs ihn =>
      simp [shift, subst, ihz d c j hj u, ihs d c j hj u, ihn d c j hj u]

/-- Instance of `par_shift_subst` in the `n = j` branch, kernel-evaluated. -/
theorem par_shift_subst_instance :
    shift 1 2 (subst 1 .zero (.var 1)) =
      subst 1 (shift 1 2 .zero) (shift 1 3 (.var 1)) :=
  par_shift_subst 1 2 1 (by omega) .zero (.var 1)

/-- Second instance of `par_shift_subst`, in the `n < j` branch. -/
theorem par_shift_subst_instance_lt :
    shift 1 2 (subst 1 .zero (.var 0)) =
      subst 1 (shift 1 2 .zero) (shift 1 3 (.var 0)) :=
  par_shift_subst 1 2 1 (by omega) .zero (.var 0)

private theorem par_subst_subst_gen (k j : Nat) (u v t : SysTTerm) :
    subst (j + k) (shift k 0 v) (subst k (shift k 0 u) t) =
      subst k (shift k 0 (subst j v u))
        (subst (j + k + 1) (shift (k + 1) 0 v) t) := by
  induction t generalizing k j u v with
  | var n =>
      by_cases hnk : n < k
      · have hnj : n < j + k := by omega
        have hnj1 : n < j + k + 1 := by omega
        simp [subst, hnk, hnj, hnj1]
      · by_cases heq : n = k
        · rw [heq]
          have hklt : ¬ k < k := by omega
          have hklt1 : k < j + k + 1 := by omega
          simp only [subst, hklt, hklt1, ite_true, ite_false]
          exact par_subst_shift j k v u
        · have _hgt : k < n := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hnk) (Ne.symm heq)
          have hnpred : ¬ n - 1 < k := by omega
          by_cases hnj1 : n < j + k + 1
          · have hnj : n - 1 < j + k := by omega
            simp [subst, hnk, heq, hnj, hnj1]
          · by_cases hneq : n = j + k + 1
            · rw [hneq]
              have hklt : ¬ (j + k + 1) < k := by omega
              have hne : ¬ j + k + 1 = k := by omega
              have hadd : shift 1 k (shift k 0 v) = shift (k + 1) 0 v := by
                simpa [Nat.add_comm k 1] using par_shift_shift_add 1 k 0 v
              simp [subst, hklt, hne]
              rw [← hadd, par_subst_shift_cancel]
            · have hnpred_j : ¬ n - 1 < j + k := by omega
              have hneq_j : ¬ n - 1 = j + k := by omega
              have hne_k : n - 1 ≠ k := by omega
              simp [subst, hnk, heq, hneq, hnpred, hnpred_j, hneq_j, hnj1, hne_k]
  | lam A b ih =>
      have ih' := ih (k + 1) j u v
      have hs1 : shift 1 0 (shift k 0 v) = shift (k + 1) 0 v := by
        simpa [Nat.add_comm 1 k] using par_shift_shift 1 k 0 v
      have hs2 : shift 1 0 (shift k 0 u) = shift (k + 1) 0 u := by
        simpa [Nat.add_comm 1 k] using par_shift_shift 1 k 0 u
      have hs3 : shift 1 0 (shift k 0 (subst j v u)) = shift (k + 1) 0 (subst j v u) := by
        simpa [Nat.add_comm 1 k] using par_shift_shift 1 k 0 (subst j v u)
      have hs4 : shift 1 0 (shift (k + 1) 0 v) = shift (k + 1 + 1) 0 v := by
        have h := par_shift_shift 1 (k + 1) 0 v
        simpa [Nat.add_comm 1 (k + 1)] using h
      simp [subst, hs1, hs2, hs3, hs4]
      have hjk : j + (k + 1) = j + k + 1 := by omega
      have hjk1 : j + (k + 1) + 1 = j + k + 1 + 1 := by omega
      simpa [hjk, hjk1] using ih'
  | app f a ihf iha => simp [subst, ihf, iha]
  | zero => rfl
  | succ t ih => simp [subst, ih]
  | natrec z s n ihz ihs ihn => simp [subst, ihz, ihs, ihn]

/--
Proves: substituting `v` into a contractum `subst 0 u t` equals first pushing `v`
under the binder then substituting the already-substituted argument.
Does not prove: composition at two positive holes without the private generator.
Relation: equality of `subst`; not a rewrite relation.
Closure: not applicable.
Trust: kernel-only.
Scope: every index `j`, every pair of substitutes, every term.
-/
theorem par_subst_subst (j : Nat) (u v t : SysTTerm) :
    subst j v (subst 0 u t) =
      subst 0 (subst j v u) (subst (j + 1) (shift 1 0 v) t) := by
  simpa [par_shift_zero] using par_subst_subst_gen 0 j u v t

/-- Instance of `par_subst_subst` on the substituted variable. -/
theorem par_subst_subst_instance :
    subst 0 .zero (subst 0 (.succ .zero) (.var 0)) =
      subst 0 (subst 0 .zero (.succ .zero)) (subst 1 (shift 1 0 .zero) (.var 0)) :=
  par_subst_subst 0 (.succ .zero) .zero (.var 0)

/-- Second instance of `par_subst_subst`, under an abstraction. -/
theorem par_subst_subst_instance_lam :
    subst 0 .zero (subst 0 (.succ .zero) (.lam .nat (.var 1))) =
      subst 0 (subst 0 .zero (.succ .zero))
        (subst 1 (shift 1 0 .zero) (.lam .nat (.var 1))) :=
  par_subst_subst 0 (.succ .zero) .zero (.lam .nat (.var 1))

/-! ## Parallel reduction -/

/-- Tait–Martin-Löf parallel reduction of System T: reflexive on variables and
`zero`, congruent on every constructor, and contracting a beta, recZero, or recSucc
redex whose parts have already reduced in parallel.

Relation: `Par` (one parallel step). Closure: one parallel step.
Strategy: full (every redex may contract in the same parallel step). -/
inductive Par : SysTTerm → SysTTerm → Prop where
  | var (n : Nat) : Par (.var n) (.var n)
  | zero : Par .zero .zero
  | lam (A : SysTTy) {b b' : SysTTerm} : Par b b' → Par (.lam A b) (.lam A b')
  | app {f f' a a' : SysTTerm} : Par f f' → Par a a' → Par (.app f a) (.app f' a')
  | succ {t t' : SysTTerm} : Par t t' → Par (.succ t) (.succ t')
  | natrec {z z' s s' n n' : SysTTerm} :
      Par z z' → Par s s' → Par n n' →
        Par (.natrec z s n) (.natrec z' s' n')
  | beta (A : SysTTy) {b b' u u' : SysTTerm} :
      Par b b' → Par u u' → Par (.app (.lam A b) u) (subst 0 u' b')
  | recZero {z z' s s' : SysTTerm} :
      Par z z' → Par s s' → Par (.natrec z s .zero) z'
  | recSucc {z z' s s' n n' : SysTTerm} :
      Par z z' → Par s s' → Par n n' →
        Par (.natrec z s (.succ n)) (.app (.app s' n') (.natrec z' s' n'))

/--
Proves: `Par` is reflexive.
Does not prove: that `Par` is a closure of `Step` (see `step_par` and `par_stepStar`).
Relation: `Par`.
Closure: one parallel step.
Trust: kernel-only.
Scope: every System T term.
-/
theorem par_refl : ∀ t : SysTTerm, Par t t
  | .var n => Par.var n
  | .zero => Par.zero
  | .lam A b => Par.lam A (par_refl b)
  | .app f a => Par.app (par_refl f) (par_refl a)
  | .succ t => Par.succ (par_refl t)
  | .natrec z s n => Par.natrec (par_refl z) (par_refl s) (par_refl n)

/--
Proves: `Par` is closed under `shift`.
Does not prove: that `shift` creates or destroys redexes.
Relation: `Par`.
Closure: one parallel step.
Trust: kernel-only.
Scope: every distance, cutoff, and parallel pair.
-/
theorem par_shift {t t' : SysTTerm} (d c : Nat) (h : Par t t') :
    Par (shift d c t) (shift d c t') := by
  induction h generalizing c with
  | var n =>
      by_cases hnc : n < c
      · simp [shift, hnc]
        exact Par.var n
      · simp [shift, hnc]
        exact Par.var (n + d)
  | zero => exact Par.zero
  | lam A _ ih => exact Par.lam A (ih (c + 1))
  | app _ _ ihf iha => exact Par.app (ihf c) (iha c)
  | succ _ ih => exact Par.succ (ih c)
  | natrec _ _ _ ihz ihs ihn => exact Par.natrec (ihz c) (ihs c) (ihn c)
  | @beta A b b' u u' _ _ ihb iha =>
      have hbeta := Par.beta A (ihb (c + 1)) (iha c)
      have heq : shift d c (subst 0 u' b') =
          subst 0 (shift d c u') (shift d (c + 1) b') :=
        par_shift_subst d c 0 (Nat.zero_le c) u' b'
      rw [shift, shift, heq]
      exact hbeta
  | recZero _ _ ihz ihs => exact Par.recZero (ihz c) (ihs c)
  | recSucc _ _ _ ihz ihs ihn => exact Par.recSucc (ihz c) (ihs c) (ihn c)

/--
Proves: `Par` is substitutive in both the body and the substitute.
Does not prove: a one-step `Step` analogue (a stepping substitute may take many
`Step` steps).
Relation: `Par`.
Closure: one parallel step.
Trust: kernel-only.
Scope: every hole, every parallel pair of bodies, every parallel pair of substitutes.
-/
theorem par_subst {b b' u u' : SysTTerm} (j : Nat) (hb : Par b b') (hu : Par u u') :
    Par (subst j u b) (subst j u' b') := by
  induction hb generalizing j u u' with
  | var n =>
      unfold subst
      split_ifs with hlt heq
      · exact Par.var n
      · exact hu
      · exact Par.var (n - 1)
  | zero => exact Par.zero
  | lam A _ ih =>
      exact Par.lam A (ih (j + 1) (par_shift 1 0 hu))
  | app _ _ ihf iha =>
      exact Par.app (ihf j hu) (iha j hu)
  | succ _ ih =>
      exact Par.succ (ih j hu)
  | natrec _ _ _ ihz ihs ihn =>
      exact Par.natrec (ihz j hu) (ihs j hu) (ihn j hu)
  | @beta A b b' v v' _ _ ihb iha =>
      have hbeta := Par.beta A (ihb (j + 1) (par_shift 1 0 hu)) (iha j hu)
      have heq : subst j u' (subst 0 v' b') =
          subst 0 (subst j u' v') (subst (j + 1) (shift 1 0 u') b') :=
        par_subst_subst j v' u' b'
      rw [subst, subst, heq]
      exact hbeta
  | recZero _ _ ihz ihs =>
      exact Par.recZero (ihz j hu) (ihs j hu)
  | recSucc _ _ _ ihz ihs ihn =>
      exact Par.recSucc (ihz j hu) (ihs j hu) (ihn j hu)

/--
Proves: every one-step `Step` is a parallel step.
Does not prove: the converse (a parallel step may contract several redexes).
Relation: `Step` and `Par`.
Closure: one step / one parallel step.
Trust: kernel-only.
Scope: every one-step pair.
-/
theorem step_par {t u : SysTTerm} (h : Step t u) : Par t u := by
  induction h with
  | beta A b u => exact Par.beta A (par_refl b) (par_refl u)
  | recZero z s => exact Par.recZero (par_refl z) (par_refl s)
  | recSucc z s n => exact Par.recSucc (par_refl z) (par_refl s) (par_refl n)
  | appL a _ ih => exact Par.app ih (par_refl a)
  | appR f _ ih => exact Par.app (par_refl f) ih
  | lam A _ ih => exact Par.lam A ih
  | succ _ ih => exact Par.succ ih
  | recZ s n _ ih => exact Par.natrec ih (par_refl s) (par_refl n)
  | recS z n _ ih => exact Par.natrec (par_refl z) ih (par_refl n)
  | recN z s _ ih => exact Par.natrec (par_refl z) (par_refl s) ih

private theorem stepStar_lam (A : SysTTy) {b b' : SysTTerm} (h : StepStar b b') :
    StepStar (SysTTerm.lam A b) (SysTTerm.lam A b') :=
  ReflTransGen.lift (fun t : SysTTerm => SysTTerm.lam A t)
    (fun _ _ ht => Step.lam A ht) h

private theorem stepStar_appL (a : SysTTerm) {f f' : SysTTerm} (h : StepStar f f') :
    StepStar (SysTTerm.app f a) (SysTTerm.app f' a) :=
  ReflTransGen.lift (fun t : SysTTerm => SysTTerm.app t a)
    (fun _ _ ht => Step.appL a ht) h

private theorem stepStar_appR (f : SysTTerm) {a a' : SysTTerm} (h : StepStar a a') :
    StepStar (SysTTerm.app f a) (SysTTerm.app f a') :=
  ReflTransGen.lift (fun t : SysTTerm => SysTTerm.app f t)
    (fun _ _ ht => Step.appR f ht) h

private theorem stepStar_app {f f' a a' : SysTTerm}
    (hf : StepStar f f') (ha : StepStar a a') :
    StepStar (.app f a) (.app f' a') :=
  (stepStar_appL a hf).trans (stepStar_appR f' ha)

private theorem stepStar_succ {t t' : SysTTerm} (h : StepStar t t') :
    StepStar (SysTTerm.succ t) (SysTTerm.succ t') :=
  ReflTransGen.lift (fun t : SysTTerm => SysTTerm.succ t)
    (fun _ _ ht => Step.succ ht) h

private theorem stepStar_recZ (s n : SysTTerm) {z z' : SysTTerm} (h : StepStar z z') :
    StepStar (SysTTerm.natrec z s n) (SysTTerm.natrec z' s n) :=
  ReflTransGen.lift (fun t : SysTTerm => SysTTerm.natrec t s n)
    (fun _ _ ht => Step.recZ s n ht) h

private theorem stepStar_recS (z n : SysTTerm) {s s' : SysTTerm} (h : StepStar s s') :
    StepStar (SysTTerm.natrec z s n) (SysTTerm.natrec z s' n) :=
  ReflTransGen.lift (fun t : SysTTerm => SysTTerm.natrec z t n)
    (fun _ _ ht => Step.recS z n ht) h

private theorem stepStar_recN (z s : SysTTerm) {n n' : SysTTerm} (h : StepStar n n') :
    StepStar (SysTTerm.natrec z s n) (SysTTerm.natrec z s n') :=
  ReflTransGen.lift (fun t : SysTTerm => SysTTerm.natrec z s t)
    (fun _ _ ht => Step.recN z s ht) h

private theorem stepStar_natrec {z z' s s' n n' : SysTTerm}
    (hz : StepStar z z') (hs : StepStar s s') (hn : StepStar n n') :
    StepStar (.natrec z s n) (.natrec z' s' n') :=
  ((stepStar_recZ s n hz).trans (stepStar_recS z' n hs)).trans (stepStar_recN z' s' hn)

/--
Proves: every parallel step is a `StepStar` sequence.
Does not prove: a bound on the number of `Step` steps.
Relation: `Par` and `StepStar`.
Closure: one parallel step realized as the reflexive-transitive closure of `Step`.
Trust: kernel-only.
Scope: every parallel pair.
-/
theorem par_stepStar {t u : SysTTerm} (h : Par t u) : StepStar t u := by
  induction h with
  | var n => exact ReflTransGen.refl
  | zero => exact ReflTransGen.refl
  | lam A _ ih => exact stepStar_lam A ih
  | app _ _ ihf iha => exact stepStar_app ihf iha
  | succ _ ih => exact stepStar_succ ih
  | natrec _ _ _ ihz ihs ihn => exact stepStar_natrec ihz ihs ihn
  | @beta A b b' v v' _ _ ihb iha =>
      have hcong : StepStar (SysTTerm.app (SysTTerm.lam A b) v)
          (SysTTerm.app (SysTTerm.lam A b') v') :=
        stepStar_app (stepStar_lam A ihb) iha
      exact hcong.trans (ReflTransGen.single (Step.beta A b' v'))
  | @recZero z z' s s' _ _ ihz ihs =>
      have hcong : StepStar (SysTTerm.natrec z s SysTTerm.zero)
          (SysTTerm.natrec z' s' SysTTerm.zero) :=
        stepStar_natrec ihz ihs ReflTransGen.refl
      exact hcong.trans (ReflTransGen.single (Step.recZero z' s'))
  | @recSucc z z' s s' n n' _ _ _ ihz ihs ihn =>
      have hcong : StepStar (SysTTerm.natrec z s (SysTTerm.succ n))
          (SysTTerm.natrec z' s' (SysTTerm.succ n')) :=
        stepStar_natrec ihz ihs (stepStar_succ ihn)
      exact hcong.trans (ReflTransGen.single (Step.recSucc z' s' n'))

/--
Proves: `StepStar` is the reflexive-transitive closure of `Par`.
Does not prove: confluence (see `stepStar_confluent`).
Relation: `StepStar` and `Par`.
Closure: reflexive-transitive.
Trust: kernel-only.
Scope: every pair of terms.
-/
theorem stepStar_eq_parStar {t u : SysTTerm} :
    StepStar t u ↔ ReflTransGen Par t u := by
  constructor
  · intro h
    exact h.mono (fun _ _ ht => step_par ht)
  · intro h
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ hpar ih => exact ih.trans (par_stepStar hpar)

/-! ## Complete development and the Takahashi triangle -/

/-- Takahashi complete development: contract every beta, recZero, and recSucc redex
in one parallel sweep, developing every proper subterm.

Relation: the graph of `dev` lies inside `Par` (see `par_dev` at `u = t` via `par_refl`).
Strategy: full; every redex of the source is contracted. -/
def dev : SysTTerm → SysTTerm
  | .var n => .var n
  | .zero => .zero
  | .lam A b => .lam A (dev b)
  | .succ t => .succ (dev t)
  | .app (.lam _A b) u => subst 0 (dev u) (dev b)
  | .app f a => .app (dev f) (dev a)
  | .natrec z _s .zero => dev z
  | .natrec z s (.succ n) => .app (.app (dev s) (dev n)) (.natrec (dev z) (dev s) (dev n))
  | .natrec z s n => .natrec (dev z) (dev s) (dev n)

/--
Proves: every parallel reduct of `t` parallel-reduces to `dev t` (Takahashi triangle).
Does not prove: that `dev t` is a `Step`-normal form (it is not, in general).
Relation: `Par`.
Closure: one parallel step on each side of the triangle.
Trust: kernel-only.
Scope: every parallel pair.
-/
theorem par_dev {t u : SysTTerm} (h : Par t u) : Par u (dev t) := by
  induction h with
  | var n => exact Par.var n
  | zero => exact Par.zero
  | lam A _ ih => exact Par.lam A ih
  | succ _ ih => exact Par.succ ih
  | @app f f' a a' hf ha ihf iha =>
      cases f with
      | lam A b =>
          cases hf with
          | lam _ _ =>
              cases ihf with
              | lam _ ihb =>
                  exact Par.beta A ihb iha
      | var n => exact Par.app ihf iha
      | app f1 f2 => exact Par.app ihf iha
      | zero => exact Par.app ihf iha
      | succ t => exact Par.app ihf iha
      | natrec z s n => exact Par.app ihf iha
  | @beta A b b' v v' hb hv ihb ihv =>
      exact par_subst 0 ihb ihv
  | @natrec z z' s s' n n' hz hs hn ihz ihs ihn =>
      cases n with
      | zero =>
          cases hn
          exact Par.recZero ihz ihs
      | succ n0 =>
          cases hn with
          | succ _ =>
              cases ihn with
              | succ ihn0 =>
                  exact Par.recSucc ihz ihs ihn0
      | var k => exact Par.natrec ihz ihs ihn
      | lam A b => exact Par.natrec ihz ihs ihn
      | app f a => exact Par.natrec ihz ihs ihn
      | natrec z2 s2 n2 => exact Par.natrec ihz ihs ihn
  | recZero _ _ ihz _ihs =>
      exact ihz
  | recSucc _ _ _ ihz ihs ihn =>
      exact Par.app (Par.app ihs ihn) (Par.natrec ihz ihs ihn)

/--
Proves: `Par` has the diamond property, with common reduct `dev t`.
Does not prove: a one-step `Step` diamond (full `Step` is not a diamond:
the fork fixture below takes two `Step` steps to join).
Relation: `Par`.
Closure: one parallel step.
Trust: kernel-only.
Scope: every parallel peak.
-/
theorem par_diamond {t u v : SysTTerm} (hu : Par t u) (hv : Par t v) :
    ∃ w, Par u w ∧ Par v w :=
  ⟨dev t, par_dev hu, par_dev hv⟩

/--
Proves: `StepStar` is confluent.
Does not prove: termination (lane L4) and nothing about extensions of the
calculus with a syntactic equality tester. The first-order `eqW` distinction
boundary has no counterpart on this orthogonal carrier.
Relation: `Step`.
Closure: `StepStar`.
Strategy: full.
Trust: kernel-only.
Scope: every peak of `StepStar`.
-/
theorem stepStar_confluent {t u v : SysTTerm}
    (hu : StepStar t u) (hv : StepStar t v) :
    ∃ w, StepStar u w ∧ StepStar v w := by
  have hParU : ReflTransGen Par t u := (stepStar_eq_parStar.mp hu)
  have hParV : ReflTransGen Par t v := (stepStar_eq_parStar.mp hv)
  have hstrip :
      ∀ a b c, Par a b → Par a c →
        ∃ d, ReflGen Par b d ∧ ReflTransGen Par c d := by
    intro a b c hab hac
    obtain ⟨d, hbd, hcd⟩ := par_diamond hab hac
    exact ⟨d, ReflGen.single hbd, ReflTransGen.single hcd⟩
  obtain ⟨w, hw1, hw2⟩ := church_rosser hstrip hParU hParV
  exact ⟨w, stepStar_eq_parStar.mpr hw1, stepStar_eq_parStar.mpr hw2⟩

/--
Proves: a normal form has no proper `StepStar` reduct.
Does not prove: existence of a normal form (that is termination, lane L4).
Relation: `Step`.
Closure: `StepStar`.
Trust: kernel-only.
Scope: every normal term.
-/
theorem isNormal_stepStar {t u : SysTTerm} (hn : IsNormal t) (h : StepStar t u) :
    t = u := by
  induction h with
  | refl => rfl
  | tail hstar hstep ih =>
      cases ih
      exact absurd hstep (hn _)

/--
Proves: normal forms of a term, if they exist, are unique.
Does not prove: that a normal form exists (termination, lane L4).
Relation: `Step`.
Closure: `StepStar`.
Strategy: full.
Trust: kernel-only.
Scope: every pair of `StepStar` reducts that are `IsNormal`.
-/
theorem normalForm_unique {t u v : SysTTerm}
    (hu : StepStar t u) (hv : StepStar t v)
    (nu : IsNormal u) (nv : IsNormal v) : u = v := by
  obtain ⟨w, hw1, hw2⟩ := stepStar_confluent hu hv
  have e1 := isNormal_stepStar nu hw1
  have e2 := isNormal_stepStar nv hw2
  exact e1.trans e2.symm

/-! ## Non-vacuity: a two-redex fork joined by confluence -/

/-- `(λx. succ x) ((λy. y) 0)`. The identity-on-identity example
`app (lam nat (var 0)) (app (lam nat (var 0)) zero)` has coinciding one-step
reducts, so this term is the distinct-reduct witness. -/
def forkSrc : SysTTerm :=
  .app (.lam .nat (.succ (.var 0))) (.app (.lam .nat (.var 0)) .zero)

/-- Outer beta: `succ ((λy. y) 0)`. -/
def forkLeft : SysTTerm := .succ (.app (.lam .nat (.var 0)) .zero)

/-- Inner beta: `(λx. succ x) 0`. -/
def forkRight : SysTTerm := .app (.lam .nat (.succ (.var 0))) .zero

/--
Proves: the outer beta of `forkSrc`.
Does not prove: that this is the only one-step.
Relation: `Step`.
Closure: one step.
Trust: kernel-only.
Scope: the fork fixture.
-/
theorem fork_step_left : Step forkSrc forkLeft :=
  Step.beta .nat (.succ (.var 0)) (.app (.lam .nat (.var 0)) .zero)

/--
Proves: the inner beta of `forkSrc`.
Does not prove: that this is the only one-step.
Relation: `Step`.
Closure: one step.
Trust: kernel-only.
Scope: the fork fixture.
-/
theorem fork_step_right : Step forkSrc forkRight :=
  Step.appR (.lam .nat (.succ (.var 0))) (Step.beta .nat (.var 0) .zero)

/--
Proves: the two one-step reducts of `forkSrc` are distinct terms.
Does not prove: that they are joinable (see `fork_join`).
Relation: equality of `SysTTerm`; not a rewrite relation.
Closure: not applicable.
Trust: kernel-only (`decide` reduction).
Scope: the fork fixture.
-/
theorem fork_left_ne_right : forkLeft ≠ forkRight := by decide

/--
Proves: `succ 0` has no `Step` successor.
Does not prove: that every `succ t` is normal.
Relation: `Step`.
Closure: one step (none exist).
Trust: kernel-only.
Scope: the term `succ zero`.
-/
theorem succ_zero_isNormal : IsNormal (.succ .zero) := by
  intro u h
  cases h with
  | succ h' => cases h'

/--
Proves: both one-step reducts of `forkSrc` reduce to `succ 0`.
Does not prove: that `succ 0` is the only common reduct of a larger peak.
Relation: `Step`.
Closure: `StepStar`.
Trust: kernel-only.
Scope: the fork fixture.
-/
theorem fork_join_succ_zero :
    StepStar forkLeft (.succ .zero) ∧ StepStar forkRight (.succ .zero) := by
  constructor
  · exact ReflTransGen.single (Step.succ (Step.beta .nat (.var 0) .zero))
  · exact ReflTransGen.single (Step.beta .nat (.succ (.var 0)) .zero)

/--
Proves: the two distinct one-step reducts of `forkSrc` are joinable by
`stepStar_confluent`.
Does not prove: a bound on the length of the joining sequences.
Relation: `Step`.
Closure: `StepStar`.
Trust: kernel-only.
Scope: the fork fixture.
-/
theorem fork_join : ∃ w, StepStar forkLeft w ∧ StepStar forkRight w :=
  stepStar_confluent
    (ReflTransGen.single fork_step_left)
    (ReflTransGen.single fork_step_right)

/--
Proves: `forkSrc` reduces to `succ 0`.
Does not prove: uniqueness by itself (see `fork_unique_nf`).
Relation: `Step`.
Closure: `StepStar`.
Trust: kernel-only.
Scope: the fork fixture.
-/
theorem forkSrc_reduces_succ_zero : StepStar forkSrc (SysTTerm.succ SysTTerm.zero) :=
  (ReflTransGen.single fork_step_left).trans fork_join_succ_zero.1

/--
Proves: every normal form of `forkSrc` is `succ 0`.
Does not prove: a general normalizer.
Relation: `Step`.
Closure: `StepStar`.
Trust: kernel-only.
Scope: the fork fixture.
-/
theorem fork_unique_nf {u : SysTTerm}
    (hu : StepStar forkSrc u) (nu : IsNormal u) :
    u = SysTTerm.succ SysTTerm.zero :=
  normalForm_unique hu forkSrc_reduces_succ_zero nu succ_zero_isNormal

end OperatorKO7.HigherOrderRewritingConfluence
