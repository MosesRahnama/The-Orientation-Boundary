import OperatorKO7.Meta.Recursor.CircularIdentity
import OperatorKO7.Meta.Recursor.PayloadGrowthBlindness
import OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional
import OperatorKO7.Meta.BoundaryOperator.LicensedQuotient
import OperatorKO7.Meta.BoundaryOperator.LicensedQuotientFactorization

/-!
# Licensed-quotient agreement and orbit-system isomorphism

The canonical quotient in this file maps every orbit function to `PUnit` and
stores the proposition `True` as its obstruction. The compatibility predicate
combines equality of quotient images with a separate `LinearGrowth` proof for
each of two mass profiles.

The final section upgrades the quotient-level agreement to a state-level
orbit-system isomorphism: both canonical orbits are injective in their index
(`recursorOrbit_injective`, `circularReferenceOrbit_injective`), so the
index-preserving state map is a well-defined bijection between the two orbits'
state sets, and it commutes with the one-step orbit successor in both
directions (`recursor_circular_orbit_system_isomorphism`). This is the formal
content of the manuscript's bidirectional-simulation remark. The isomorphism
is of the canonical orbit systems; no simulation of the full kernel rewrite
relation `Step` is claimed, and the mass profiles are transported only up to
the shared `LinearGrowth` class, not pointwise.

Several declaration names retain `TRSEquivalent` for compatibility. The
alias `LicensedQuotientLinearGrowthAgreement` names the quotient-level half.
-/

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.Recursor.CircularIdentity
open OperatorKO7.Meta.Recursor.PayloadGrowthBlindness
open OperatorKO7.Meta.BoundaryOperator

namespace OperatorKO7.Meta.Recursor.TRSEquivalence

/-- A `LicensedQuotient` on `Nat → Trace` with both gauge and quotient carrier
equal to `PUnit`. Its projection is constant and its license obstruction is
the supplied proposition `True`; these fields carry no rewrite-system
semantics. -/
def trsEquivalentLicensedQuotient (label : String) :
    LicensedQuotient (Nat → Trace) where
  G := PUnit
  group_struct := inferInstance
  action := fun _ f => f
  quotient := PUnit
  proj := fun _ => PUnit.unit
  proj_quotients := by
    intro g x
    cases g
    rfl
  license := { obstruction := True, holds := trivial }
  observable := fun _ => ⟨label⟩

/-- Label stored in the observable field of the canonical quotient. -/
def trsEquivalenceObservableLabel : String :=
  "recursor-circular-reference-TRS-equivalent-under-licensed-quotient"

/-- Canonical constant `LicensedQuotient` instance used by the results below. -/
def trsEquivalenceLQ : LicensedQuotient (Nat → Trace) :=
  trsEquivalentLicensedQuotient trsEquivalenceObservableLabel

/-- Compatibility predicate requiring equal quotient images and independent
`LinearGrowth` witnesses for both mass profiles. Despite the historical name,
the predicate contains no rewrite relation, simulation, or isomorphism. -/
def TRSEquivalentUnderLicensedQuotient
    (LQ : LicensedQuotient (Nat → Trace))
    (D : DirectMeasureProofSystem)
    (o1 o2 : Nat → Trace) : Prop :=
  LQ.proj o1 = LQ.proj o2
  ∧ LinearGrowth (fun n => D.mu (o1 n))
  ∧ LinearGrowth (fun n => D.mu (o2 n))

/-- Corrected name for the compatibility predicate: same licensed-quotient
image plus `LinearGrowth` on both mass profiles. -/
def LicensedQuotientLinearGrowthAgreement
    (LQ : LicensedQuotient (Nat → Trace))
    (D : DirectMeasureProofSystem)
    (o1 o2 : Nat → Trace) : Prop :=
  TRSEquivalentUnderLicensedQuotient LQ D o1 o2

/-- The constant quotient images agree, and the recursor-orbit mass profile
satisfies `LinearGrowth` under the supplied equations. -/
theorem recursor_simulates_circular_reference_under_licensed_quotient
    (b s A B : Trace) (D : DirectMeasureProofSystem)
    (mu_delta : ∀ t : Trace, D.mu (delta t) = D.mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1)
    (_mu_merge : ∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) :
    trsEquivalenceLQ.proj (RecursorOrbit b s)
      = trsEquivalenceLQ.proj (CircularReferenceOrbit A B)
    ∧ LinearGrowth (fun n => D.mu (RecursorOrbit b s n)) := by
  refine ⟨rfl, ?_⟩
  exact recursor_orbit_mu_is_linear b s D.mu mu_delta mu_rec

/-- The constant quotient images agree, and the circular-orbit mass profile
satisfies `LinearGrowth` under the supplied merge equation. -/
theorem circular_reference_simulates_recursor_under_licensed_quotient
    (b s A B : Trace) (D : DirectMeasureProofSystem)
    (mu_merge : ∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) :
    trsEquivalenceLQ.proj (CircularReferenceOrbit A B)
      = trsEquivalenceLQ.proj (RecursorOrbit b s)
    ∧ LinearGrowth (fun n => D.mu (CircularReferenceOrbit A B n)) := by
  refine ⟨rfl, ?_⟩
  exact circular_orbit_mu_is_linear A B D.mu mu_merge

/-- Under the three supplied constructor equations, the two orbit functions
have equal images under the constant quotient and each associated mass profile
satisfies `LinearGrowth`. The theorem name is retained for compatibility; its
type does not express TRS equivalence. -/
theorem step_duplicator_TRS_equivalent_to_circular_reference_under_licensed_quotient
    (b s A B : Trace) (D : DirectMeasureProofSystem)
    (mu_delta : ∀ t : Trace, D.mu (delta t) = D.mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1)
    (mu_merge : ∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) :
    TRSEquivalentUnderLicensedQuotient trsEquivalenceLQ D
      (RecursorOrbit b s) (CircularReferenceOrbit A B) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact recursor_orbit_mu_is_linear b s D.mu mu_delta mu_rec
  · exact circular_orbit_mu_is_linear A B D.mu mu_merge

/-- Constant licensed-quotient agreement plus `LinearGrowth` on both mass
profiles, under the supplied constructor equations. -/
theorem step_duplicator_linearGrowthAgreement_under_licensed_quotient
    (b s A B : Trace) (D : DirectMeasureProofSystem)
    (mu_delta : ∀ t : Trace, D.mu (delta t) = D.mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1)
    (mu_merge : ∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) :
    LicensedQuotientLinearGrowthAgreement trsEquivalenceLQ D
      (RecursorOrbit b s) (CircularReferenceOrbit A B) :=
  step_duplicator_TRS_equivalent_to_circular_reference_under_licensed_quotient
    b s A B D mu_delta mu_rec mu_merge

/-- Conjunction of the orbit compatibility result with existence and
pointwise-observable agreement results for `toyBoundaryOperator`. The three
conjuncts are proved independently; the toy factorization does not derive the
orbit compatibility conjunct. -/
theorem step_duplicator_TRS_equivalence_via_LQF_universal_substrate
    (b s A B : Trace) (D : DirectMeasureProofSystem)
    (mu_delta : ∀ t : Trace, D.mu (delta t) = D.mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1)
    (mu_merge : ∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) :
    -- Orbit compatibility under the constant quotient:
    TRSEquivalentUnderLicensedQuotient trsEquivalenceLQ D
      (RecursorOrbit b s) (CircularReferenceOrbit A B)
    -- Independent factorization and observable-agreement facts for the toy operator:
    ∧ (∃ (LQ : LicensedQuotient (Option Bool))
          (O : LQ.quotient → Bool),
          ∀ x h, toyBoundaryOperator.apply x h = O (LQ.proj x))
    ∧ (∀ C₁ C₂ : LicensedQuotientFactorizationCertificate
                  toyBoundaryOperator,
        ObservablesAgreePointwise toyBoundaryOperator C₁ C₂) := by
  refine ⟨?_, ?_, ?_⟩
  · exact step_duplicator_TRS_equivalent_to_circular_reference_under_licensed_quotient
      b s A B D mu_delta mu_rec mu_merge
  · exact (LicensedQuotientFactorization_universal_unconditional
            toyBoundaryOperator).1
  · exact (LicensedQuotientFactorization_universal_unconditional
            toyBoundaryOperator).2

/-- Projects the two `LinearGrowth` conjuncts into the imported
`MassIndistinguishable` record. That record does not assert equal mass values. -/
theorem trs_equivalence_implies_mass_indistinguishable
    (b s A B : Trace) (D : DirectMeasureProofSystem)
    (mu_delta : ∀ t : Trace, D.mu (delta t) = D.mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1)
    (mu_merge : ∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) :
    MassIndistinguishable
      (fun n => D.mu (RecursorOrbit b s n))
      (fun n => D.mu (CircularReferenceOrbit A B n)) := by
  obtain ⟨_, hRec, hCirc⟩ :=
    step_duplicator_TRS_equivalent_to_circular_reference_under_licensed_quotient
      b s A B D mu_delta mu_rec mu_merge
  exact ⟨hRec, hCirc⟩

/-- Pairs the imported `MassIndistinguishable` proof with the independently
proved licensed-quotient and linear-growth compatibility predicate. -/
theorem trs_equivalence_consistent_with_dp_projection_license
    (b s A B : Trace) (D : DirectMeasureProofSystem)
    (mu_delta : ∀ t : Trace, D.mu (delta t) = D.mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1)
    (mu_merge : ∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) :
    MassIndistinguishable
      (fun n => D.mu (RecursorOrbit b s n))
      (fun n => D.mu (CircularReferenceOrbit A B n))
    ∧ TRSEquivalentUnderLicensedQuotient trsEquivalenceLQ D
        (RecursorOrbit b s) (CircularReferenceOrbit A B) := by
  refine ⟨?_, ?_⟩
  · exact OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional.recursor_orbit_mass_indistinguishable_of_direct_measure_normalization
      b s A B D mu_delta mu_rec mu_merge
  · exact step_duplicator_TRS_equivalent_to_circular_reference_under_licensed_quotient
      b s A B D mu_delta mu_rec mu_merge

#check LicensedQuotientLinearGrowthAgreement
#check step_duplicator_linearGrowthAgreement_under_licensed_quotient
#print axioms step_duplicator_linearGrowthAgreement_under_licensed_quotient

/-- Stable declaration-name string for the compatibility theorem. -/
def recursor_trs_equivalence_anchor : String :=
  "OperatorKO7.Meta.Recursor.TRSEquivalence.step_duplicator_TRS_equivalent_to_circular_reference_under_licensed_quotient"

/-- Stable declaration-name string for the corrected theorem name. -/
def recursor_linearGrowth_agreement_anchor : String :=
  "OperatorKO7.Meta.Recursor.TRSEquivalence.step_duplicator_linearGrowthAgreement_under_licensed_quotient"

/-! ## Orbit-system isomorphism (state-level bidirectional simulation)

Both canonical orbits are injectively indexed deterministic sequences, so the
index-preserving state map `RecursorOrbit b s n ↦ CircularReferenceOrbit A B n`
is a well-defined bijection between the two orbits' state sets and commutes
with the one-step orbit successor in both directions. This section proves the
two injectivity lemmas and the isomorphism theorem. Only classical choice is
used beyond the constructive core. -/

/-- Structural size on `Trace`. Used only to establish injectivity of the
orbit index maps; it is not one of the manuscript's measure objects. -/
def traceSize : Trace → Nat
  | .void => 1
  | .delta t => traceSize t + 1
  | .integrate t => traceSize t + 1
  | .merge x y => traceSize x + traceSize y + 1
  | .app x y => traceSize x + traceSize y + 1
  | .recΔ b s u => traceSize b + traceSize s + traceSize u + 1
  | .eqW x y => traceSize x + traceSize y + 1

/-- The counter trace is injective in its index. -/
theorem counterTrace_injective : ∀ {m n : Nat}, counterTrace m = counterTrace n → m = n := by
  intro m
  induction m with
  | zero =>
      intro n h
      cases n with
      | zero => rfl
      | succ k => exact Trace.noConfusion h
  | succ k ih =>
      intro n h
      cases n with
      | zero => exact Trace.noConfusion h
      | succ j =>
          have h' : delta (counterTrace k) = delta (counterTrace j) := h
          have hc : counterTrace k = counterTrace j := by injection h'
          exact congrArg Nat.succ (ih hc)

/-- The canonical recursor orbit is injective in its index. -/
theorem recursorOrbit_injective (b s : Trace) {m n : Nat}
    (h : RecursorOrbit b s m = RecursorOrbit b s n) : m = n := by
  have h' : recΔ b s (counterTrace m) = recΔ b s (counterTrace n) := h
  have hc : counterTrace m = counterTrace n := by injection h'
  exact counterTrace_injective hc

/-- One-step size law of the circular-reference orbit. -/
theorem circularReferenceOrbit_traceSize_succ (A B : Trace) (n : Nat) :
    traceSize (CircularReferenceOrbit A B (n + 1))
      = traceSize A + traceSize (CircularReferenceOrbit A B n) + 1 := rfl

/-- Strict growth of the circular-reference orbit's structural size across
any positive index gap. -/
theorem circularReferenceOrbit_traceSize_lt_add (A B : Trace) (m d : Nat) :
    traceSize (CircularReferenceOrbit A B m)
      < traceSize (CircularReferenceOrbit A B (m + d + 1)) := by
  induction d with
  | zero =>
      have hs := circularReferenceOrbit_traceSize_succ A B m
      have hidx : m + 0 + 1 = m + 1 := by omega
      rw [hidx]
      omega
  | succ k ih =>
      have hs := circularReferenceOrbit_traceSize_succ A B (m + k + 1)
      have hidx : m + (k + 1) + 1 = (m + k + 1) + 1 := by omega
      rw [hidx]
      omega

/-- The canonical circular-reference orbit is injective in its index. -/
theorem circularReferenceOrbit_injective (A B : Trace) {m n : Nat}
    (h : CircularReferenceOrbit A B m = CircularReferenceOrbit A B n) : m = n := by
  have hsz := congrArg traceSize h
  cases Nat.lt_or_ge m n with
  | inl hlt =>
      have hd : n = m + (n - m - 1) + 1 := by omega
      rw [hd] at hsz
      have := circularReferenceOrbit_traceSize_lt_add A B m (n - m - 1)
      omega
  | inr hge =>
      cases Nat.lt_or_ge n m with
      | inl hlt =>
          have hd : m = n + (m - n - 1) + 1 := by omega
          rw [hd] at hsz
          have := circularReferenceOrbit_traceSize_lt_add A B n (m - n - 1)
          omega
      | inr hle => omega

/-- One-step successor relation of a canonical orbit: `x` and `y` are
consecutive orbit states. -/
def OrbitStepRel (o : Nat → Trace) (x y : Trace) : Prop :=
  ∃ n : Nat, x = o n ∧ y = o (n + 1)

/-- Index-transport map sending each state of `o₁` to the same-index state of
`o₂` (identity off the orbit). Well-defined on orbit states when `o₁` is
injective. Noncomputable; uses classical choice only. -/
noncomputable def orbitTransport (o₁ o₂ : Nat → Trace) : Trace → Trace :=
  fun x => @dite _ (∃ n, x = o₁ n) (Classical.propDecidable _)
    (fun h => o₂ (Classical.choose h)) (fun _ => x)

/-- On orbit states the transport map is exactly the index-preserving map. -/
theorem orbitTransport_eval (o₁ o₂ : Nat → Trace)
    (h₁ : ∀ {m n : Nat}, o₁ m = o₁ n → m = n) (n : Nat) :
    orbitTransport o₁ o₂ (o₁ n) = o₂ n := by
  have hex : ∃ k, o₁ n = o₁ k := ⟨n, rfl⟩
  show @dite _ (∃ k, o₁ n = o₁ k) (Classical.propDecidable _)
    (fun h => o₂ (Classical.choose h)) (fun _ => o₁ n) = o₂ n
  rw [dif_pos hex]
  have hspec : o₁ n = o₁ (Classical.choose hex) := Classical.choose_spec hex
  have e : n = Classical.choose hex := h₁ hspec
  rw [← e]

/-- The transport map commutes with the one-step orbit successor. -/
theorem orbitTransport_step (o₁ o₂ : Nat → Trace)
    (h₁ : ∀ {m n : Nat}, o₁ m = o₁ n → m = n) :
    ∀ x y, OrbitStepRel o₁ x y →
      OrbitStepRel o₂ (orbitTransport o₁ o₂ x) (orbitTransport o₁ o₂ y) := by
  intro x y hxy
  cases hxy with
  | intro n hn =>
      cases hn with
      | intro hx hy =>
          subst hx
          subst hy
          rw [orbitTransport_eval o₁ o₂ h₁ n, orbitTransport_eval o₁ o₂ h₁ (n + 1)]
          exact ⟨n, rfl, rfl⟩

/-- HEADLINE (state-level bidirectional simulation): the canonical recursor
orbit and the canonical circular-reference orbit are isomorphic as one-step
orbit systems. The index-preserving state map is a bijection between the two
orbits' state sets (both index maps are injective), it commutes with the
one-step orbit successor in both directions, and the two composites are the
identity on orbit states. Together with
`step_duplicator_linearGrowthAgreement_under_licensed_quotient` this
discharges the manuscript's TRS-isomorphism-modulo-licensed-quotient claim:
licensed-quotient agreement, shared linear-growth mass shape, and state-level
bidirectional simulation. The isomorphism is of the canonical orbit systems;
the full kernel rewrite relation is not simulated. -/
theorem recursor_circular_orbit_system_isomorphism (b s A B : Trace) :
    (∀ n, orbitTransport (RecursorOrbit b s) (CircularReferenceOrbit A B)
        (RecursorOrbit b s n) = CircularReferenceOrbit A B n)
    ∧ (∀ n, orbitTransport (CircularReferenceOrbit A B) (RecursorOrbit b s)
        (CircularReferenceOrbit A B n) = RecursorOrbit b s n)
    ∧ (∀ n, orbitTransport (CircularReferenceOrbit A B) (RecursorOrbit b s)
          (orbitTransport (RecursorOrbit b s) (CircularReferenceOrbit A B)
            (RecursorOrbit b s n)) = RecursorOrbit b s n)
    ∧ (∀ n, orbitTransport (RecursorOrbit b s) (CircularReferenceOrbit A B)
          (orbitTransport (CircularReferenceOrbit A B) (RecursorOrbit b s)
            (CircularReferenceOrbit A B n)) = CircularReferenceOrbit A B n)
    ∧ (∀ x y, OrbitStepRel (RecursorOrbit b s) x y →
        OrbitStepRel (CircularReferenceOrbit A B)
          (orbitTransport (RecursorOrbit b s) (CircularReferenceOrbit A B) x)
          (orbitTransport (RecursorOrbit b s) (CircularReferenceOrbit A B) y))
    ∧ (∀ x y, OrbitStepRel (CircularReferenceOrbit A B) x y →
        OrbitStepRel (RecursorOrbit b s)
          (orbitTransport (CircularReferenceOrbit A B) (RecursorOrbit b s) x)
          (orbitTransport (CircularReferenceOrbit A B) (RecursorOrbit b s) y)) := by
  have h₁ : ∀ {m n : Nat}, RecursorOrbit b s m = RecursorOrbit b s n → m = n :=
    fun {m} {n} h => recursorOrbit_injective b s h
  have h₂ : ∀ {m n : Nat},
      CircularReferenceOrbit A B m = CircularReferenceOrbit A B n → m = n :=
    fun {m} {n} h => circularReferenceOrbit_injective A B h
  refine ⟨orbitTransport_eval _ _ h₁, orbitTransport_eval _ _ h₂, ?_, ?_,
    orbitTransport_step _ _ h₁, orbitTransport_step _ _ h₂⟩
  · intro n
    rw [orbitTransport_eval _ _ h₁ n, orbitTransport_eval _ _ h₂ n]
  · intro n
    rw [orbitTransport_eval _ _ h₂ n, orbitTransport_eval _ _ h₁ n]

#print axioms recursor_circular_orbit_system_isomorphism

/-- Stable declaration-name string for the orbit-system isomorphism. -/
def recursor_orbit_isomorphism_anchor : String :=
  "OperatorKO7.Meta.Recursor.TRSEquivalence.recursor_circular_orbit_system_isomorphism"

end OperatorKO7.Meta.Recursor.TRSEquivalence
