import OperatorKO7.Meta.InformationalIncompleteness.CarrierCapacity

set_option autoImplicit false

/-!
# Explicit addressability premise for carrier-capacity bounds

The earlier carrier-capacity theorem proves growth of `carrierRaw`; it does not
by itself show that every certificate must pay that cost.  This module makes the
missing premise an explicit property of a certificate interface.  The premise
has both an inhabitant and a counterexample, so it cannot be silently treated as
automatic.

Audit scope (LASOT): these are natural-number code-length statements.  They do
not prove that a concrete termination-certificate format is individually
addressable; a client must supply `IndividuallyAddressable` for that format.
-/

namespace OperatorKO7.Meta.InformationalIncompleteness.CarrierAddressability

open OperatorKO7.Meta.InformationalIncompleteness

/-- A certificate interface with a canonical certificate at every recursor
depth and an exact bit-length accounting law for that certificate. -/
structure CertificateInterface where
  Certificate : Nat -> Type
  encode : ∀ K, Certificate K -> List Bool
  canonical : ∀ K, Certificate K
  certificateLength : Nat -> Nat
  canonical_length : ∀ K,
    (encode K (canonical K)).length = certificateLength K

/-- The addressability premise omitted by the old carrier-capacity statement:
the canonical code must be at least as long as the raw per-occurrence carrier
count at every depth. -/
structure IndividuallyAddressable
    (I : CertificateInterface) (payloadLength : Nat) : Prop where
  raw_le_certificate : ∀ K,
    CarrierBurden.carrierRaw payloadLength K ≤ I.certificateLength K

/-- An explicit interface whose canonical code contains exactly one bit slot
for every unit counted by `carrierRaw`. -/
def rawCarrierInterface (payloadLength : Nat) : CertificateInterface where
  Certificate := fun _ => Unit
  encode := fun K _ =>
    List.replicate (CarrierBurden.carrierRaw payloadLength K) false
  canonical := fun _ => ()
  certificateLength := CarrierBurden.carrierRaw payloadLength
  canonical_length := by
    intro K
    simp

/-- The raw-carrier interface witnesses that the addressability premise is
inhabited. -/
theorem rawCarrierInterface_individuallyAddressable (payloadLength : Nat) :
    IndividuallyAddressable
      (rawCarrierInterface payloadLength) payloadLength where
  raw_le_certificate := fun _ => le_rfl

/-- A fixed-budget certificate interface, used as the negative witness. -/
def fixedBudgetInterface (budget : Nat) : CertificateInterface where
  Certificate := fun _ => Unit
  encode := fun _ _ => List.replicate budget false
  canonical := fun _ => ()
  certificateLength := fun _ => budget
  canonical_length := by
    intro K
    simp

/-- For positive payload length, no fixed-budget interface satisfies the
individual-addressability premise. -/
theorem fixedBudgetInterface_not_individuallyAddressable
    (payloadLength : Nat) (hpositive : 1 ≤ payloadLength) (budget : Nat) :
    ¬ IndividuallyAddressable
      (fixedBudgetInterface budget) payloadLength := by
  intro H
  obtain ⟨K, hraw⟩ :=
    CarrierCapacity.carrier_capacity_asymptotic_shortfall
      payloadLength hpositive budget
  exact (Nat.not_lt_of_ge (H.raw_le_certificate K)) hraw

/-- Conditional carrier-capacity theorem with the previously implicit premise
visible in the type: every individually addressable interface eventually
exceeds every fixed bit budget. -/
theorem individuallyAddressable_exceeds_fixed_budget
    (I : CertificateInterface)
    (payloadLength : Nat) (hpositive : 1 ≤ payloadLength)
    (H : IndividuallyAddressable I payloadLength)
    (budget : Nat) :
    ∃ K, budget < I.certificateLength K := by
  obtain ⟨K, hraw⟩ :=
    CarrierCapacity.carrier_capacity_asymptotic_shortfall
      payloadLength hpositive budget
  exact ⟨K, lt_of_lt_of_le hraw (H.raw_le_certificate K)⟩

/-- The addressability hypothesis is nontrivial: it has an inhabitant and, for
positive payloads, a concrete non-inhabitant. -/
theorem addressability_hypothesis_nonvacuous
    (payloadLength : Nat) (hpositive : 1 ≤ payloadLength) :
    IndividuallyAddressable
        (rawCarrierInterface payloadLength) payloadLength ∧
      ¬ IndividuallyAddressable
        (fixedBudgetInterface 0) payloadLength :=
  ⟨rawCarrierInterface_individuallyAddressable payloadLength,
    fixedBudgetInterface_not_individuallyAddressable
      payloadLength hpositive 0⟩

section AuditChecks

#check @CertificateInterface
#check @IndividuallyAddressable
#check @rawCarrierInterface
#check @fixedBudgetInterface
#check @rawCarrierInterface_individuallyAddressable
#check @fixedBudgetInterface_not_individuallyAddressable
#check @individuallyAddressable_exceeds_fixed_budget
#check @addressability_hypothesis_nonvacuous

#print axioms rawCarrierInterface_individuallyAddressable
#print axioms fixedBudgetInterface_not_individuallyAddressable
#print axioms individuallyAddressable_exceeds_fixed_budget
#print axioms addressability_hypothesis_nonvacuous

end AuditChecks

end OperatorKO7.Meta.InformationalIncompleteness.CarrierAddressability
