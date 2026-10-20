import OperatorKO7.Meta.BoundaryObserver.DemandComplex
import OperatorKO7.Meta.LCELAnnotatedReimport
import OperatorKO7.Meta.LicensedBoundaryCalculus.Integrated.SemanticNoGo

set_option autoImplicit false

/-!
# Demand and annotation sentences of the Boundary-Observation Principle

Four statements of the sections on demand problems, annotated derivations and operations that no earlier
declaration states in the words of the paper: the readout family of a downward-closed family is
nonempty exactly when the family holds the empty set; the selector and coloring alphabets of a
finite retained set agree and have the least-value characterization for an arbitrary demand set;
the bijection of annotated derivations with their payloads commutes with relabeling; and no
function of the morphism and the event trace alone returns the fixed-length certificate floor of
every operation on one fixed two-state reduction system.

Relation: none; the statements concern sets of demands, alphabets in `ℕ∞` and sums of types.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleDemand

open UniversalObservation.Demand

/-- The readout family of a downward-closed family is nonempty if and only if the family holds the
empty set. -/
theorem booleanFamily_nonempty_iff {I : Type*} (K : Set (Set I)) (hK : Downward K) :
    (booleanFamily K).Nonempty ↔ (∅ : Set I) ∈ K := by
  constructor
  · rintro ⟨f, hf⟩
    exact hK ∅ _ (Set.empty_subset _) hf
  · intro h0
    refine ⟨fun _ => true, ?_⟩
    change {i | true = false} ∈ K
    simpa using h0

/-- For a finite retained set and an arbitrary demand set, the least feasible selector alphabet
equals the least licensed coloring alphabet; both are infinite if and only if no finite alphabet
succeeds, and a finite value `k` is the least number of selector values that succeeds. -/
theorem licensed_selector_least_alphabet_of_finite {I : Type*} {W : Type*} (P : Problem I W)
    (menu : RepairMenu I W P) {D : Set I} (hD : D.Finite) :
    licensedMinimumAlphabet P menu D = licensedColoringAlphabet P menu D ∧
      ((∀ k, ¬ RepairFeasible P menu D k) ↔
        licensedMinimumAlphabet P menu D = ⊤ ∧ licensedColoringAlphabet P menu D = ⊤) ∧
      ∀ k : ℕ, licensedMinimumAlphabet P menu D = (k : ℕ∞) ↔
        RepairFeasible P menu D k ∧ ∀ j, j < k → ¬ RepairFeasible P menu D j := by
  have he := licensedMinimumAlphabet_eq_coloring_of_finite P menu hD
  refine ⟨he, ?_, licensedMinimumAlphabet_eq_coe_iff P menu D⟩
  rw [← he, and_self, licensedMinimumAlphabet_eq_top_iff]

open OperatorKO7.Meta.LCELAnnotatedReimport
open OperatorKO7.Meta.LCELTypedDerivations

/-- The bijection of annotated derivations with their payloads commutes with relabeling: relabeling
an annotated derivation along `f` and then taking its payload is taking its payload and relabeling
the license coordinate along `f`. -/
theorem annotatedPayload_relabel_comm {T U : TypedTheory} {embed : TheoryExtension T U}
    {License License' : Type*} {phi : T.Sentence} (f : License → License')
    (d : AnnotatedDerivation T U embed License phi) :
    annotatedDerivationEquivPayload (mapLicense f d) =
      Sum.map id (Prod.map f id) (annotatedDerivationEquivPayload d) := by
  cases d <;> rfl

open OperatorKO7.Meta.LicensedBoundaryCalculus
  OperatorKO7.Meta.LicensedBoundaryCalculus.IntegratedBuilders in
/-- Proposition `prop:typed-resource-composition`, the certificate floor: no function of the
morphism and the event trace alone returns the fixed-length certificate floor of every operation,
already on the two-state chain system. The two orientation transactions share morphism and trace,
and their floors are `0` and `1`. -/
theorem no_morphism_trace_only_certificateFloor :
    ¬ (∃ extract :
        PartialLicensedReductionMorphism chainARS_fixture chainARS_fixture → EventTrace → ℕ,
      ∀ transaction :
          IntegratedBoundaryTransaction chainARS_fixture chainARS_fixture Unit Unit,
        extract transaction.morphism transaction.eventTrace =
          transaction.semanticProfile.fixedLengthCertificateFloor) := by
  rintro ⟨extract, hextract⟩
  have horiginal := hextract orientationTransaction_fixture
  have htwo := hextract orientationTransaction_twoAlternatives_fixture
  have hzero :
      orientationTransaction_fixture.semanticProfile.fixedLengthCertificateFloor = 0 := by
    rw [orientation_transaction_profile_exact]
    rfl
  rw [orientation_twoAlternatives_same_morphism_fixture,
    orientation_twoAlternatives_same_trace_fixture, horiginal, hzero,
    orientation_twoAlternatives_fixedLengthFloor_eq_one] at htwo
  exact absurd htwo (by decide)

end OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleDemand
