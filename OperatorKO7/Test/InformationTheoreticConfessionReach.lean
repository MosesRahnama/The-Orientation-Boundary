import OperatorKO7.Meta.InformationTheoreticConfession

namespace InformationTheoreticConfessionReach

open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Meta.GenericConfessionMove
open OperatorKO7.Meta.GenericConfessionMove.GenericConfessionMove
open OperatorKO7.Meta.InformationTheoreticConfession

def toyVerdict (n : Nat) : Prop := n = 0

def toyMove : GenericConfessionMove Nat toyVerdict Unit where
  licenseWitness := ()
  sourceBarrier := toyVerdict
  Quotient := Nat
  projection := id
  residualObstruction := toyVerdict
  Certificate := Nat
  certificateOf := id
  verifier := toyVerdict
  verifier_sound := by
    intro q h
    exact h
  barrier_covers_residual := by
    intro x h
    exact h
  soundness := by
    intro x h
    exact h
  verdictSufficient := by
    intro x x' h
    simpa [toyVerdict] using congrArg (fun n => n = 0) h

def toyInfo : InformationTheoreticConfession toyMove where
  PreConfessionInformation := Nat
  PostVerdictInformation := Nat
  DiscardedInformation := Nat
  preEncode := id
  postEncode := id
  discardEncode := id
  discardedBits := id
  canonicalDiscardedBits := 2

def toyCharacterizationData :
    UniversalConfessionCharacterizationData toyMove toyMove where
  factorization := GenericConfessionMove.Refines.refl toyMove

def toyOptimalityData : OptimalityData toyMove toyMove where
  factorization := toyCharacterizationData
  uniqueness := by
    intro _
    exact ⟨id, by intro x; rfl⟩

def toyMinimalityData :
    DiscardedInformationMinimalityData toyInfo toyInfo where
  canonical_le_candidate := by decide

#check InformationTheoreticConfession
#check UniversalConfessionCharacterizationData
#check ConfessionConverges
#check OptimalityData
#check DiscardedInformationMinimalityData
#check universal_confession_characterization_of_data
#check universal_confession_characterization
#check confession_convergence_iff_H_equivalent
#check optimal_confession_universal_property_of_data
#check optimal_confession_universal_property
#check canonical_confession_minimizes_discarded_information_of_data
#check canonical_confession_minimizes_discarded_information
#check gauge_fixing_identity

example : GenericConfessionMove.Refines toyMove toyMove :=
  universal_confession_characterization_of_data toyCharacterizationData

example : ConfessionConverges toyMove toyMove ↔ GenericConfessionMove.HEquivalent toyMove toyMove :=
  confession_convergence_iff_H_equivalent

example : GenericConfessionMove.Refines toyMove toyMove := by
  exact (optimal_confession_universal_property_of_data toyOptimalityData).1

example : toyInfo.canonicalDiscardedBits ≤ toyInfo.canonicalDiscardedBits :=
  canonical_confession_minimizes_discarded_information_of_data toyMinimalityData

example : GenericConfessionMove.Refines
    (ko7MethodToGenericConfessionMove counterProjectionConfession counterProjection_eq_dp_rank)
    ko7CanonicalConfessionMove :=
  universal_confession_characterization
    (method := counterProjectionConfession)
    (by simp [allConfessionMethods])

example : GenericConfessionMove.Refines
    (ko7MethodToGenericConfessionMove argumentFilteringConfession argumentFiltering_eq_dp_rank)
    ko7CanonicalConfessionMove := by
  exact (optimal_confession_universal_property
    (method := argumentFilteringConfession)
    (by simp [allConfessionMethods])).1

example : ko7CanonicalInformationTheoreticConfession.canonicalDiscardedBits ≤
    (ko7MethodToInformationTheoreticConfession
      sctConfession
      sct_eq_dp_rank).canonicalDiscardedBits :=
  canonical_confession_minimizes_discarded_information
    (method := sctConfession)
    (by simp [allConfessionMethods])

example : GenericConfessionMove.Refines toyMove toyMove ∧ GenericConfessionMove.Refines toyMove toyMove := by
  exact gauge_fixing_identity (GenericConfessionMove.HEquivalent.refl toyMove)

end InformationTheoreticConfessionReach
