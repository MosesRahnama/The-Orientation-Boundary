import Mathlib

/-!
# Quantitative schema trace kernel

Syntactic substrate for the quantitative laws added to Operational
Inexpressibility.  The distinguished base and payload leaves make terminal
record decoding unambiguous.  The rewrite relation is exactly the root rules
and the `G`-context closure used by the canonical trace.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Recursor.SchemaTraceKernel

inductive SchemaTerm where
  | Z : SchemaTerm
  | S : SchemaTerm -> SchemaTerm
  | base : Nat -> SchemaTerm
  | pay : Nat -> SchemaTerm
  | F : SchemaTerm -> SchemaTerm -> SchemaTerm -> SchemaTerm
  | G : SchemaTerm -> SchemaTerm -> SchemaTerm
deriving DecidableEq, Repr

inductive SStep : SchemaTerm -> SchemaTerm -> Prop where
  | baseRule (x y : SchemaTerm) : SStep (.F x y .Z) x
  | stepRule (x y n : SchemaTerm) :
      SStep (.F x y (.S n)) (.G y (.F x y n))
  | congG (y t t' : SchemaTerm) : SStep t t' -> SStep (.G y t) (.G y t')

def Normal (t : SchemaTerm) : Prop := forall u, Not (SStep t u)

def sPow : Nat -> SchemaTerm
  | 0 => .Z
  | k + 1 => .S (sPow k)

def gPow (y : SchemaTerm) : Nat -> SchemaTerm -> SchemaTerm
  | 0, t => t
  | i + 1, t => .G y (gPow y i t)

def orbitState (a b : SchemaTerm) (k i : Nat) : SchemaTerm :=
  if i <= k then gPow b i (.F a b (sPow (k - i))) else gPow b k a

def wsize (alpha beta gamma phi zeta : Nat) : SchemaTerm -> Nat
  | .Z => zeta
  | .S n => 1 + wsize alpha beta gamma phi zeta n
  | .base _ => alpha
  | .pay _ => beta
  | .F x y n =>
      phi + wsize alpha beta gamma phi zeta x +
        wsize alpha beta gamma phi zeta y +
        wsize alpha beta gamma phi zeta n
  | .G y t =>
      gamma + wsize alpha beta gamma phi zeta y +
        wsize alpha beta gamma phi zeta t

def countG : SchemaTerm -> Nat
  | .Z => 0
  | .S n => countG n
  | .base _ => 0
  | .pay _ => 0
  | .F x y n => countG x + countG y + countG n
  | .G y t => 1 + countG y + countG t

def countPay : SchemaTerm -> Nat
  | .Z => 0
  | .S n => countPay n
  | .base _ => 0
  | .pay _ => 1
  | .F x y n => countPay x + countPay y + countPay n
  | .G y t => countPay y + countPay t

def sHeight : SchemaTerm -> Nat
  | .S n => sHeight n + 1
  | _ => 0

def ctr : SchemaTerm -> Nat
  | .G _ t => ctr t
  | .F _ _ n => sHeight n
  | _ => 0

def hasF : SchemaTerm -> Bool
  | .Z => false
  | .S n => hasF n
  | .base _ => false
  | .pay _ => false
  | .F _ _ _ => true
  | .G _ t => hasF t

theorem sPow_succ (n : Nat) : sPow (n + 1) = .S (sPow n) := rfl

theorem sHeight_sPow (n : Nat) : sHeight (sPow n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sPow, sHeight, ih]

theorem gPow_succ_right (y t : SchemaTerm) (i : Nat) :
    gPow y i (.G y t) = gPow y (i + 1) t := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [gPow, ih]

theorem step_gPow (y : SchemaTerm) {t u : SchemaTerm} (i : Nat)
    (h : SStep t u) : SStep (gPow y i t) (gPow y i u) := by
  induction i with
  | zero => exact h
  | succ i ih => exact SStep.congG y _ _ ih

theorem step_from_gPow (y : SchemaTerm) {t u : SchemaTerm} (i : Nat)
    (h : SStep (gPow y i t) u) :
    Exists fun v => And (SStep t v) (u = gPow y i v) := by
  induction i generalizing u with
  | zero => exact ⟨u, h, rfl⟩
  | succ i ih =>
      cases h with
      | congG _ _ u' hinner =>
          obtain ⟨v, htv, rfl⟩ := ih hinner
          exact ⟨v, htv, rfl⟩

theorem base_pay_normal :
    And (forall ia, Normal (.base ia)) (forall ib, Normal (.pay ib)) := by
  constructor <;> intro i u h <;> cases h

theorem normal_gPow (y t : SchemaTerm) (i : Nat) (ht : Normal t) :
    Normal (gPow y i t) := by
  intro u h
  obtain ⟨v, htv, _⟩ := step_from_gPow y i h
  exact ht v htv

theorem F_sPow_step_unique (a b : SchemaTerm) :
    forall (n : Nat) (u : SchemaTerm), SStep (.F a b (sPow n)) u ->
      u = if n = 0 then a else .G b (.F a b (sPow (n - 1)))
  | 0, u, h => by
      cases h
      rfl
  | n + 1, u, h => by
      cases h
      simp

/-- T0.1: every live canonical state takes its unique next canonical step. -/
theorem orbit_step (a b : SchemaTerm) (k i : Nat) (hi : i <= k) :
    SStep (orbitState a b k i) (orbitState a b k (i + 1)) := by
  by_cases hlt : i < k
  · have hi1 : i + 1 <= k := by omega
    have hsub : k - i = (k - (i + 1)) + 1 := by omega
    rw [orbitState, if_pos hi, orbitState, if_pos hi1, hsub, sPow_succ]
    have hroot :
        SStep (.F a b (.S (sPow (k - (i + 1)))))
          (.G b (.F a b (sPow (k - (i + 1))))) := SStep.stepRule _ _ _
    simpa only [gPow_succ_right] using step_gPow b i hroot
  · have hik : i = k := by omega
    subst i
    rw [orbitState, if_pos (le_refl k), orbitState, if_neg (by omega)]
    simp only [Nat.sub_self, sPow]
    exact step_gPow b k (SStep.baseRule a b)

/-- T0.2: the canonical live state has no alternative rewrite successor. -/
theorem orbit_unique_redex (a b : SchemaTerm) (k i : Nat) (hi : i <= k)
    (u : SchemaTerm) (h : SStep (orbitState a b k i) u) :
    u = orbitState a b k (i + 1) := by
  rw [orbitState, if_pos hi] at h
  obtain ⟨v, hv, rfl⟩ := step_from_gPow b i h
  have huv := F_sPow_step_unique a b (k - i) v hv
  by_cases hlt : i < k
  · have hi1 : i + 1 <= k := by omega
    have hsub : k - i = (k - (i + 1)) + 1 := by omega
    have hne : k - i ≠ 0 := by omega
    rw [orbitState, if_pos hi1, huv, if_neg hne, hsub]
    simp only [Nat.add_sub_cancel, gPow_succ_right]
  · have hik : i = k := by omega
    subst i
    rw [orbitState, if_neg (by omega), huv]
    simp

/-- T0.3: a leaf-instantiated terminal record is normal. -/
theorem orbit_terminal_normal (ia ib k : Nat) :
    Normal (orbitState (.base ia) (.pay ib) k (k + 1)) := by
  rw [orbitState, if_neg (by omega)]
  exact normal_gPow (.pay ib) (.base ia) k (base_pay_normal.1 ia)

theorem wsize_sPow (alpha beta gamma phi zeta n : Nat) :
    wsize alpha beta gamma phi zeta (sPow n) = n + zeta := by
  induction n with
  | zero => simp [sPow, wsize]
  | succ n ih => simp [sPow, wsize, ih, Nat.add_assoc, Nat.add_comm]

theorem wsize_gPow (alpha beta gamma phi zeta : Nat)
    (y t : SchemaTerm) (i : Nat) :
    wsize alpha beta gamma phi zeta (gPow y i t) =
      i * (gamma + wsize alpha beta gamma phi zeta y) +
        wsize alpha beta gamma phi zeta t := by
  induction i with
  | zero => simp [gPow]
  | succ i ih =>
      simp only [gPow, wsize, ih, Nat.succ_mul]
      omega

/-- T0.4: exact weighted size of every live canonical state. -/
theorem wsize_closed_form
    (alpha beta gamma phi zeta ia ib k i : Nat) (hi : i <= k) :
    wsize alpha beta gamma phi zeta
        (orbitState (.base ia) (.pay ib) k i) =
      i * (gamma + beta) + (k - i) + (phi + alpha + beta + zeta) := by
  rw [orbitState, if_pos hi, wsize_gPow]
  simp only [wsize, wsize_sPow]
  omega

theorem wsize_terminal_closed_form
    (alpha beta gamma phi zeta ia ib k : Nat) :
    wsize alpha beta gamma phi zeta
        (orbitState (.base ia) (.pay ib) k (k + 1)) =
      k * (gamma + beta) + alpha := by
  rw [orbitState, if_neg (by omega), wsize_gPow]
  simp [wsize]

theorem countG_gPow (y t : SchemaTerm) (i : Nat) :
    countG (gPow y i t) = i * (1 + countG y) + countG t := by
  induction i with
  | zero => simp [gPow]
  | succ i ih =>
      simp only [gPow, countG, ih, Nat.succ_mul]
      omega

theorem countPay_gPow (y t : SchemaTerm) (i : Nat) :
    countPay (gPow y i t) = i * countPay y + countPay t := by
  induction i with
  | zero => simp [gPow]
  | succ i ih =>
      simp only [gPow, countPay, ih, Nat.succ_mul]
      omega

theorem countG_sPow (n : Nat) : countG (sPow n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [sPow, countG] using ih

theorem countPay_sPow (n : Nat) : countPay (sPow n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [sPow, countPay] using ih

/-- T0.5a: exact `G` count on a live canonical state. -/
theorem countG_closed_form (ia ib k i : Nat) (hi : i <= k) :
    countG (orbitState (.base ia) (.pay ib) k i) = i := by
  rw [orbitState, if_pos hi, countG_gPow]
  simp [countG, countG_sPow]

/-- T0.5b: exact payload-leaf count on a live canonical state. -/
theorem countPay_closed_form (ia ib k i : Nat) (hi : i <= k) :
    countPay (orbitState (.base ia) (.pay ib) k i) = i + 1 := by
  rw [orbitState, if_pos hi, countPay_gPow]
  simp [countPay, countPay_sPow]

theorem countG_terminal (ia ib k : Nat) :
    countG (orbitState (.base ia) (.pay ib) k (k + 1)) = k := by
  rw [orbitState, if_neg (by omega), countG_gPow]
  simp [countG]

theorem countPay_terminal (ia ib k : Nat) :
    countPay (orbitState (.base ia) (.pay ib) k (k + 1)) = k := by
  rw [orbitState, if_neg (by omega), countPay_gPow]
  simp [countPay]

/-- T0.6: exact residual counter height on a live canonical state. -/
theorem ctr_gPow (y t : SchemaTerm) (i : Nat) : ctr (gPow y i t) = ctr t := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [gPow, ctr] using ih

theorem ctr_closed_form (ia ib k i : Nat) (hi : i <= k) :
    ctr (orbitState (.base ia) (.pay ib) k i) = k - i := by
  rw [orbitState, if_pos hi, ctr_gPow]
  simp [ctr, sHeight_sPow]

theorem hasF_gPow (y t : SchemaTerm) (i : Nat) : hasF (gPow y i t) = hasF t := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [gPow, hasF] using ih

theorem hasF_live (ia ib k i : Nat) (hi : i <= k) :
    hasF (orbitState (.base ia) (.pay ib) k i) = true := by
  rw [orbitState, if_pos hi]
  rw [hasF_gPow]
  rfl

theorem hasF_terminal (ia ib k : Nat) :
    hasF (orbitState (.base ia) (.pay ib) k (k + 1)) = false := by
  rw [orbitState, if_neg (by omega)]
  rw [hasF_gPow]
  rfl

/-- Concrete positive witness for the step relation. -/
theorem sample_orbit_step :
    SStep (orbitState (.base 0) (.pay 1) 3 1)
      (orbitState (.base 0) (.pay 1) 3 2) := orbit_step _ _ _ _ (by decide)

/-- Concrete negative witness: the terminal record admits no rewrite. -/
theorem sample_terminal_has_no_step :
    Not (Exists fun u => SStep (orbitState (.base 0) (.pay 1) 3 4) u) := by
  intro h
  obtain ⟨u, hu⟩ := h
  exact orbit_terminal_normal 0 1 3 u hu

end OperatorKO7.Meta.Recursor.SchemaTraceKernel
