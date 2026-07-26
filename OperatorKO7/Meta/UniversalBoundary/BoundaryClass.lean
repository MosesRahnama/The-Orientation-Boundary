import OperatorKO7.Meta.LicensedBoundaryCalculus.Machine
import OperatorKO7.Meta.LicensedBoundaryCalculus.PlugInstance
import OperatorKO7.Meta.UniversalBoundary.WitnessTower

/-!
This module bundles a MachineSpec, WitnessTower, and rank as independent fields. Its theorems
project checker acceptance, apply a supplied BoundaryAt proof, and show the fallback halt
verdict when all offered evidence fails its checker. Semantic coherence among the bundled fields
requires additional structure.


























-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniversalBoundary

open OperatorKO7.Meta.LicensedBoundaryCalculus.Machine

universe u

/-- Data record whose requirements are the fields displayed below.
-/
structure BoundaryClass where
  spec : MachineSpec.{u}
  tower : WitnessTower
  boundaryRank : Nat

namespace BoundaryClass

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem no_unsupported_yes (B : BoundaryClass.{u}) (i : SupervisorInput B.spec)
    (h : (supervise B.spec i).verdict = .yes) :
    ∃ c : B.spec.Certificate, B.spec.checkYes c = true :=
  supervise_yes_has_verified_certificate i h

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem no_cheap_witness (B : BoundaryClass.{u}) (hb : B.tower.BoundaryAt B.boundaryRank)
    (l : B.tower.Level) (hl : B.tower.rank l ≤ B.boundaryRank) :
    ¬ B.tower.has l :=
  WitnessTower.boundary_no_cheap_witness B.tower B.boundaryRank hb l hl

end BoundaryClass

/-! Declarations for the section below. -/

/-- The displayed proposition follows from the stated hypotheses. -/
theorem haltOutput_verdict {S : MachineSpec.{u}} (p : S.Problem) (ledger : S.Ledger)
    (audit? : Option S.HaltAudit) :
    (haltOutput S p ledger audit?).verdict = .halt := by
  cases audit? with
  | none => rfl
  | some a =>
      by_cases ha : S.checkHalt a = true <;> simp [haltOutput, ha]

/-- The displayed proposition follows from the stated hypotheses.


-/
theorem supervise_halts_without_checked_evidence {S : MachineSpec.{u}} (i : SupervisorInput S)
    (hy : ∀ c, i.yesCertificate? = some c → S.checkYes c = false)
    (hn : ∀ w, i.noCounterWitness? = some w → S.checkNo w = false)
    (hu : ∀ u, i.impossibilityWitness? = some u → S.checkImpossible u = false) :
    (supervise S i).verdict = .halt := by
  unfold supervise
  cases hyc : i.yesCertificate? with
  | some c =>
      have hcf : S.checkYes c = false := hy c hyc
      simp only [hcf, Bool.false_eq_true, dite_false]
      cases hnc : i.noCounterWitness? with
      | some w =>
          have hwf : S.checkNo w = false := hn w hnc
          simp only [hwf, Bool.false_eq_true, dite_false]
          cases huc : i.impossibilityWitness? with
          | some u =>
              have huf : S.checkImpossible u = false := hu u huc
              simp only [huf, Bool.false_eq_true, dite_false]
              exact haltOutput_verdict _ _ _
          | none => exact haltOutput_verdict _ _ _
      | none =>
          cases huc : i.impossibilityWitness? with
          | some u =>
              have huf : S.checkImpossible u = false := hu u huc
              simp only [huf, Bool.false_eq_true, dite_false]
              exact haltOutput_verdict _ _ _
          | none => exact haltOutput_verdict _ _ _
  | none =>
      cases hnc : i.noCounterWitness? with
      | some w =>
          have hwf : S.checkNo w = false := hn w hnc
          simp only [hwf, Bool.false_eq_true, dite_false]
          cases huc : i.impossibilityWitness? with
          | some u =>
              have huf : S.checkImpossible u = false := hu u huc
              simp only [huf, Bool.false_eq_true, dite_false]
              exact haltOutput_verdict _ _ _
          | none => exact haltOutput_verdict _ _ _
      | none =>
          cases huc : i.impossibilityWitness? with
          | some u =>
              have huf : S.checkImpossible u = false := hu u huc
              simp only [huf, Bool.false_eq_true, dite_false]
              exact haltOutput_verdict _ _ _
          | none => exact haltOutput_verdict _ _ _

/-! Declarations for the section below. -/

open OperatorKO7.Meta.LicensedBoundaryCalculus.PlugInstance in
/-- Definition with formal content given by the displayed type and body.
-/
def evidenceGatedBoundary : BoundaryClass :=
  { spec := evidenceGatedSpec
    tower := WitnessTower.directBlockedTower
    boundaryRank := 0 }

theorem evidenceGatedBoundary_boundary :
    evidenceGatedBoundary.tower.BoundaryAt evidenceGatedBoundary.boundaryRank :=
  WitnessTower.directBlockedTower_boundary_at_zero

--
#print axioms BoundaryClass.no_unsupported_yes
#print axioms haltOutput_verdict
#print axioms supervise_halts_without_checked_evidence
#print axioms evidenceGatedBoundary_boundary

end OperatorKO7.Meta.UniversalBoundary
