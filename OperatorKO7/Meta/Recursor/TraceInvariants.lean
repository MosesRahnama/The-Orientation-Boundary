import OperatorKO7.Meta.Recursor.SchemaTraceKernel

/-!
# Canonical trace invariants

## Formal Scope

The laws concern canonical rewrite-step counts, weighted syntax quantities, payload-occurrence counts, and orbit indexing. Runtime and vector-space dimension are not formalized.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Recursor.TraceInvariants

open SchemaTraceKernel

inductive StepsTo : SchemaTerm -> Nat -> SchemaTerm -> Prop where
  | refl (t : SchemaTerm) : StepsTo t 0 t
  | step {t u v : SchemaTerm} {n : Nat} :
      SStep t u -> StepsTo u n v -> StepsTo t (n + 1) v

theorem SStep.functional {t u v : SchemaTerm}
    (hu : SStep t u) (hv : SStep t v) : u = v := by
  induction hu generalizing v with
  | baseRule x y => cases hv; rfl
  | stepRule x y n => cases hv; rfl
  | congG y t t' h ih =>
      cases hv with
      | congG _ _ v' hv' => exact congrArg (SchemaTerm.G y) (ih hv')

theorem StepsTo.normal_unique {t u v : SchemaTerm} {n m : Nat}
    (h1 : StepsTo t n u) (hu : Normal u)
    (h2 : StepsTo t m v) (hv : Normal v) :
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
          have heq : t' = v' := SStep.functional hstep hstep'
          subst v'
          obtain ⟨hn, huv⟩ := ih hu hrest' hv
          exact ⟨congrArg (fun q => q + 1) hn, huv⟩

theorem canonical_steps_from_aux (a b : SchemaTerm) (k : Nat) :
    forall d i, i <= k -> k - i = d ->
      StepsTo (orbitState a b k i) (d + 1) (orbitState a b k (k + 1)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro i hi hd
      cases d with
      | zero =>
          have hik : i = k := by omega
          subst i
          exact StepsTo.step (orbit_step a b k k (le_refl k)) (StepsTo.refl _)
      | succ d =>
          have hlt : i < k := by omega
          have hi1 : i + 1 <= k := by omega
          have hnext : k - (i + 1) = d := by omega
          have htail := ih d (by omega) (i + 1) hi1 hnext
          exact StepsTo.step (orbit_step a b k i hi) htail

theorem canonical_steps_from (a b : SchemaTerm) (k i : Nat) (hi : i <= k) :
    StepsTo (orbitState a b k i) (k - i + 1)
      (orbitState a b k (k + 1)) :=
  canonical_steps_from_aux a b k (k - i) i hi rfl

/-- Law 1: the canonical computation has directly `k+1` rewrite steps. -/
theorem L1_exact_length (ia ib k : Nat) :
    StepsTo (orbitState (.base ia) (.pay ib) k 0) (k + 1)
      (orbitState (.base ia) (.pay ib) k (k + 1)) := by
  simpa using canonical_steps_from (.base ia) (.pay ib) k 0 (Nat.zero_le k)

/-- Law 1 uniqueness: every maximal derivation has the same length and record. -/
theorem L1_length_unique (ia ib k n : Nat) (u : SchemaTerm)
    (h : StepsTo (orbitState (.base ia) (.pay ib) k 0) n u)
    (hu : Normal u) :
    n = k + 1 ∧ u = orbitState (.base ia) (.pay ib) k (k + 1) := by
  have hcanon := L1_exact_length ia ib k
  have hnormal := orbit_terminal_normal ia ib k
  exact StepsTo.normal_unique h hu hcanon hnormal

/-- Law 1 payload blindness: arbitrary leaf identities share the specified runtime. -/
theorem L1_payload_blind (ia ib ia' ib' k : Nat) :
    StepsTo (orbitState (.base ia) (.pay ib) k 0) (k + 1)
        (orbitState (.base ia) (.pay ib) k (k + 1)) ∧
      StepsTo (orbitState (.base ia') (.pay ib') k 0) (k + 1)
        (orbitState (.base ia') (.pay ib') k (k + 1)) :=
  ⟨L1_exact_length ia ib k, L1_exact_length ia' ib' k⟩

/-- Law 2: each recursive step adds one wrapper cell and consumes one `S`. -/
theorem L2_mass_rate
    (alpha beta gamma phi zeta ia ib k i : Nat) (hi : i < k) :
    wsize alpha beta gamma phi zeta
          (orbitState (.base ia) (.pay ib) k (i + 1)) + 1 =
      wsize alpha beta gamma phi zeta
          (orbitState (.base ia) (.pay ib) k i) + (gamma + beta) := by
  rw [wsize_closed_form _ _ _ _ _ _ _ _ _ (by omega),
    wsize_closed_form _ _ _ _ _ _ _ _ _ (by omega)]
  simp only [Nat.succ_mul]
  omega

/-- Law 2 terminal drop for full syntax size, including the active payload. -/
theorem L2_terminal_drop
    (alpha beta gamma phi zeta ia ib k : Nat) :
    wsize alpha beta gamma phi zeta
        (orbitState (.base ia) (.pay ib) k k) =
      wsize alpha beta gamma phi zeta
          (orbitState (.base ia) (.pay ib) k (k + 1)) +
        (phi + beta + zeta) := by
  rw [wsize_closed_form _ _ _ _ _ _ _ _ _ (le_refl k),
    wsize_terminal_closed_form]
  omega

def istar (k cstar w : Nat) : Nat := (k + cstar + w) / (w + 1)

/-- Law 5 specified integer envelope for the crossover fraction. -/
theorem L5_fraction (k cstar w : Nat) (hw : 1 <= w) :
    k + cstar <= istar k cstar w * (w + 1) ∧
      istar k cstar w * (w + 1) <= k + cstar + w := by
  unfold istar
  have hpos : 0 < w + 1 := by omega
  have hmod : (k + cstar + w) % (w + 1) < w + 1 :=
    Nat.mod_lt _ hpos
  have hdecomp := Nat.mod_add_div (k + cstar + w) (w + 1)
  rw [Nat.mul_comm (w + 1) ((k + cstar + w) / (w + 1))] at hdecomp
  omega

/-- Law 5: the ceiling crossover index reaches wrapper-cell majority. -/
theorem L5_crossover_holds (k cstar w : Nat) (hw : 1 <= w)
    (hbound : istar k cstar w <= k) :
    istar k cstar w * w >= (k - istar k cstar w) + cstar := by
  have hfrac := (L5_fraction k cstar w hw).1
  simp only [Nat.mul_add, Nat.mul_one] at hfrac
  omega

/-- Law 5: every earlier index is strictly below the crossover. -/
theorem L5_crossover_minimal (k cstar w j : Nat) (hw : 1 <= w)
    (hj : j < istar k cstar w) :
    j * w < (k - j) + cstar := by
  have hupper := (L5_fraction k cstar w hw).2
  have hj1 : j + 1 <= istar k cstar w := by omega
  have hmul := Nat.mul_le_mul_right (w + 1) hj1
  simp only [Nat.succ_mul, Nat.mul_add, Nat.mul_one] at hmul hupper
  omega

/-- Law 6: consumed counter and emitted frames conserve the step budget. -/
theorem L6_step_budget (ia ib k i : Nat) (hi : i <= k) :
    ctr (orbitState (.base ia) (.pay ib) k i) +
        countG (orbitState (.base ia) (.pay ib) k i) = k := by
  rw [ctr_closed_form _ _ _ _ hi, countG_closed_form _ _ _ _ hi]
  omega

/-- Law 6: payload occurrences exceed emitted frames by directly one while live. -/
theorem L6_offset (ia ib k i : Nat) (hi : i <= k) :
    countPay (orbitState (.base ia) (.pay ib) k i) =
      countG (orbitState (.base ia) (.pay ib) k i) + 1 := by
  rw [countPay_closed_form _ _ _ _ hi, countG_closed_form _ _ _ _ hi]

/-- Law 7: the retained counter is an specified sufficient statistic for work left. -/
theorem L7_sufficient_statistic (ia ib k i : Nat) (hi : i <= k) :
    StepsTo (orbitState (.base ia) (.pay ib) k i)
      (ctr (orbitState (.base ia) (.pay ib) k i) + 1)
      (orbitState (.base ia) (.pay ib) k (k + 1)) := by
  rw [ctr_closed_form _ _ _ _ hi]
  exact canonical_steps_from (.base ia) (.pay ib) k i hi

/-- Law 7 uniqueness from any live state. -/
theorem L7_sufficient_statistic_unique (ia ib k i n : Nat) (hi : i <= k)
    (u : SchemaTerm) (h : StepsTo (orbitState (.base ia) (.pay ib) k i) n u)
    (hu : Normal u) :
    n = ctr (orbitState (.base ia) (.pay ib) k i) + 1 ∧
      u = orbitState (.base ia) (.pay ib) k (k + 1) := by
  have hcanon := L7_sufficient_statistic ia ib k i hi
  have hnormal := orbit_terminal_normal ia ib k
  exact StepsTo.normal_unique h hu hcanon hnormal

/-- Law 11: the finite canonical orbit is injectively indexed. -/
theorem L11_orbit_injective (ia ib k i j : Nat)
    (hi : i <= k + 1) (hj : j <= k + 1)
    (hEq : orbitState (.base ia) (.pay ib) k i =
      orbitState (.base ia) (.pay ib) k j) : i = j := by
  by_cases hilive : i <= k
  · by_cases hjlive : j <= k
    · have hc := congrArg countG hEq
      rw [countG_closed_form _ _ _ _ hilive,
        countG_closed_form _ _ _ _ hjlive] at hc
      exact hc
    · have hf := congrArg hasF hEq
      rw [hasF_live _ _ _ _ hilive] at hf
      have hjterm : j = k + 1 := by omega
      subst j
      rw [hasF_terminal] at hf
      cases hf
  · have hiterm : i = k + 1 := by omega
    subst i
    by_cases hjlive : j <= k
    · have hf := congrArg hasF hEq
      rw [hasF_terminal, hasF_live _ _ _ _ hjlive] at hf
      cases hf
    · omega

/-- Law 11: live carrier dimension is directly the payload multiplicity. -/
theorem L11_carrier_dimension (ia ib k i : Nat) (hi : i <= k) :
    countPay (orbitState (.base ia) (.pay ib) k i) = i + 1 :=
  countPay_closed_form ia ib k i hi

theorem sample_exact_length :
    StepsTo (orbitState (.base 0) (.pay 1) 3 0) 4
      (orbitState (.base 0) (.pay 1) 3 4) := by
  simpa using L1_exact_length 0 1 3

theorem sample_conservation :
    ctr (orbitState (.base 0) (.pay 1) 3 2) +
      countG (orbitState (.base 0) (.pay 1) 3 2) = 3 := by
  exact L6_step_budget 0 1 3 2 (by decide)

end OperatorKO7.Meta.Recursor.TraceInvariants
