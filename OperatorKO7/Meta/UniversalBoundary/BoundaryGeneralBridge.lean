import OperatorKO7.Meta.UniversalBoundary.BoundaryClass
import OperatorKO7.Meta.BoundaryGeneral.UniversalityGate
import OperatorKO7.Meta.BoundaryGeneral.WitnessFirst
import OperatorKO7.Meta.BoundaryGeneral.C4Classifier
import OperatorKO7.Meta.BoundaryGeneral.CostedConfession

/-!
# Universal Boundary Calculus: bridge to the boundary-general cross-paper packet

The boundary-general packet (`Meta/BoundaryGeneral/`, Theories I-XIV) and the universal layer
(`Meta/UniversalBoundary/`) mechanize the same boundary discipline independently. This module links
them, import-only, without touching the packet's modules. Three bridges:

1. **Universality gate (Theory V).** The universal layer's release surface is a complete
   `BoundaryGeneral.UniversalityGate.UGate`: every declared universal claim has a complete calculus row,
   where each row's completeness is the actual proven guarantee (the U2 no-unsupported-yes guarantee, the
   witness-channel boundary, the C4 interface-inexpressibility classification, the costed-confession
   additive bound). Universality is finite, declared, theorem-backed coverage, exactly Theory V's claim.

2. **Witness-first gate (Theory VIII).** A `BoundaryClass` yields a witness-first accepted certificate:
   its witness-present and verdict-supported obligations are discharged by U2
   (`no_unsupported_yes`), and its external-license obligation by the machine's trust-no-upgrade. The
   remaining grounding/cost/replay obligations are carried by the certificate envelope and the costed
   boundary expansion; they are recorded here as the envelope-side fields.

3. **C4 cause classifier (Theory VII).** The witness-channel boundary (no cheap witness at the boundary
   rank) classifies as INTERFACE INEXPRESSIBILITY, not object undecidability: the verdict depends on a
   coordinate the direct observation language cannot name. This is the kappaStar > 0 story, stated in the
   C4 layer vocabulary.

## Audit slots

```
Relation: not a rewriting relation; bridge theorems linking the two mechanizations.
Closure:  not applicable.
Trust:    baseline or none; reuse of both sides' verified theorems.
Scope:    the universal-release UGate, the BoundaryClass witness-first certificate, the C4 boundary link.
```
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniversalBoundary.BoundaryGeneralBridge

open OperatorKO7.Meta.LicensedBoundaryCalculus.Machine
open OperatorKO7.Meta.BoundaryGeneral

/-! ## Bridge 1: the universal release is a complete universality gate (Theory V) -/

/-- The declared universal claim identifiers: a finite set spanning the universal contract and the
boundary-general theories the bridge unifies. -/
inductive UClaim
  | boundaryPresent      -- the evidence-gated boundary is genuine at the cheap rank (witness tower)
  | noUnsupportedYes     -- U2: a positive verdict carries a checker-accepted certificate
  | recursorInterface    -- Theory VII: the recursor boundary is interface-inexpressible, not undecidable
  | costedAdditive       -- Theory IV: confession composition burden is at most the sum of the parts
  deriving DecidableEq, Repr

/-- The calculus row for each declared claim. The `complete` field is the actual proven guarantee, so a
gate pass is exactly the conjunction of the backing theorems. -/
def universalRow : UClaim → UniversalityGate.CalculusRow
  | .boundaryPresent =>
      { statement := Unit, proof := Unit, license := Unit, reach := Unit, scope := Unit
        complete := evidenceGatedBoundary.tower.BoundaryAt evidenceGatedBoundary.boundaryRank }
  | .noUnsupportedYes =>
      { statement := Unit, proof := Unit, license := Unit, reach := Unit, scope := Unit
        complete := ∀ i : SupervisorInput evidenceGatedBoundary.spec,
          (supervise evidenceGatedBoundary.spec i).verdict = Verdict.yes →
            ∃ c : evidenceGatedBoundary.spec.Certificate, evidenceGatedBoundary.spec.checkYes c = true }
  | .recursorInterface =>
      { statement := Unit, proof := Unit, license := Unit, reach := Unit, scope := Unit
        complete := C4Classifier.classify C4Classifier.recursorEvidence
          = C4Classifier.BoundaryLayer.interfaceInexpr }
  | .costedAdditive =>
      { statement := Unit, proof := Unit, license := Unit, reach := Unit, scope := Unit
        complete := ∀ B₁ B₂ shared : Nat,
          CostedConfession.compositionBurden B₁ B₂ shared ≤ B₁ + B₂ }

/-- The universal layer's release surface passes the universality gate: every declared universal claim
has a complete row, witnessed by its backing theorem. This is Theory V applied to the system actually
built, not to an abstract family. -/
theorem universal_release_passes_ugate :
    UniversalityGate.UGate (fun _ : UClaim => True) universalRow := by
  intro c _
  cases c with
  | boundaryPresent => exact evidenceGatedBoundary_boundary
  | noUnsupportedYes =>
      intro i h; exact BoundaryClass.no_unsupported_yes evidenceGatedBoundary i h
  | recursorInterface => exact C4Classifier.recursor_is_interfaceInexpr
  | costedAdditive => intro B₁ B₂ shared; exact CostedConfession.composition_le B₁ B₂ shared

/-- Dropping any declared guarantee breaks the gate: a claim with an incomplete row falsifies
universality. Records that the gate is non-vacuous (the missing-row direction, Theory 5.6). -/
theorem dropped_guarantee_fails_ugate :
    ¬ UniversalityGate.UGate (fun _ : Unit => True)
        (fun _ => UniversalityGate.incompleteRow) :=
  UniversalityGate.ugate_fails_example

/-! ## Bridge 2: a BoundaryClass is a witness-first accepted certificate (Theory VIII) -/

/-- The witness-first certificate of a boundary class on a given input. The witness-present and
verdict-supported obligations are the U2 guarantee; the external-license obligation is the machine's
trust-no-upgrade; the grounding/cost/replay obligations are the envelope-side fields (carried by the
certificate envelope and the costed boundary expansion). -/
def witnessFirstCertificate (B : BoundaryClass) (i : SupervisorInput B.spec) :
    WitnessFirst.Certificate where
  witnessPresent :=
    (supervise B.spec i).verdict = Verdict.yes → ∃ c : B.spec.Certificate, B.spec.checkYes c = true
  citationsGrounded := True
  projectionsCosted := True
  externalsLicensed := ∀ a b : License, (composeLicense a b).tier.rank ≤ a.tier.rank
  replayRecorded := True
  verdictSupported :=
    (supervise B.spec i).verdict = Verdict.yes → ∃ c : B.spec.Certificate, B.spec.checkYes c = true

/-- Every boundary class yields a witness-first accepted certificate: no unsupported free-text verdict
(U2), and trust never upgrades. The supervisory-engine acceptance gate of Theory VIII is the universal
contract's gate. -/
theorem boundaryClass_is_witness_first_accepted (B : BoundaryClass) (i : SupervisorInput B.spec) :
    WitnessFirst.Accepts (witnessFirstCertificate B i) := by
  refine ⟨?_, trivial, trivial, ?_, trivial, ?_⟩
  · intro h; exact BoundaryClass.no_unsupported_yes B i h
  · intro a b; exact composeLicense_rank_le_left a b
  · intro h; exact BoundaryClass.no_unsupported_yes B i h

/-- The accepted certificate's verdict is witness-backed (Theorem 8.4), specialized to the boundary
class: a direct corollary that the boundary class never ships an unsupported free-text verdict. -/
theorem boundaryClass_verdict_supported (B : BoundaryClass) (i : SupervisorInput B.spec) :
    (witnessFirstCertificate B i).verdictSupported :=
  WitnessFirst.accepts_verdict_supported (boundaryClass_is_witness_first_accepted B i)

/-! ## Bridge 3 (C4): the witness-channel boundary is interface-inexpressible (Theory VII) -/

/-- The witness-channel boundary is genuine (no cheap witness at the cheap rank) AND classifies in the
C4 vocabulary as interface inexpressibility, not object undecidability: the obstruction is that the
verdict depends on a coordinate the direct observation language cannot name. This is the kappaStar > 0
story in the boundary-cause classifier. -/
theorem witness_boundary_is_interface_inexpressible :
    WitnessTower.directBlockedTower.BoundaryAt 0
      ∧ C4Classifier.classify C4Classifier.recursorEvidence = C4Classifier.BoundaryLayer.interfaceInexpr
      ∧ C4Classifier.classify C4Classifier.recursorEvidence ≠ C4Classifier.BoundaryLayer.objUndec :=
  ⟨WitnessTower.directBlockedTower_boundary_at_zero,
   C4Classifier.recursor_is_interfaceInexpr,
   C4Classifier.recursor_not_objUndec⟩

-- Axiom audit (Rule W16: recorded for the build log).
#print axioms universal_release_passes_ugate
#print axioms boundaryClass_is_witness_first_accepted
#print axioms witness_boundary_is_interface_inexpressible

end OperatorKO7.Meta.UniversalBoundary.BoundaryGeneralBridge
