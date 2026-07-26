import OperatorKO7.Meta.LicensedBoundaryCalculus.Machine

/-!
# Boolean certificate fixture for the Licensed Boundary Calculus machine

`evidenceGatedSpec` uses `Bool` for certificates and defines `checkYes` as the identity. Certificate
acceptance therefore depends solely on the Boolean value, independently of the problem string.
The main theorem projects the generic machine invariant that a `yes` result has some accepted
certificate. The two inputs demonstrate acceptance of `true` and rejection of `false`. The identifiers
`w2Input` and `w0Input` do not encode W2 or W0 semantic witnesses.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.PlugInstance

open OperatorKO7.Meta.LicensedBoundaryCalculus.Machine

/-- Machine fixture with Boolean certificates and identity Boolean checkers. -/
def evidenceGatedSpec : MachineSpec where
  Problem := String
  Certificate := Bool
  CounterWitness := Bool
  ImpossibilityWitness := Bool
  HaltAudit := Unit
  Ledger := Unit
  checkYes := fun c => c
  checkNo := fun w => w
  checkImpossible := fun u => u
  checkHalt := fun _ => true
  defaultHalt := ()
  defaultHalt_valid := rfl
  defaultLedger := ()

/--
If the fixture emits `yes`, some Boolean certificate is accepted by the identity checker. This is a
specialization of `Machine.supervise_yes_has_verified_certificate` at Boolean acceptance semantics.
-/
theorem evidenceGated_no_unsupported_yes (i : SupervisorInput evidenceGatedSpec)
    (h : (supervise evidenceGatedSpec i).verdict = .yes) :
    ∃ c : evidenceGatedSpec.Certificate, evidenceGatedSpec.checkYes c = true :=
  supervise_yes_has_verified_certificate i h

/-- Input named `w2Input` that carries the accepted Boolean value `true`. -/
def w2Input : SupervisorInput evidenceGatedSpec :=
  { problem := "answerable with a grounded citation", yesCertificate? := some true }

/-- Input named `w0Input` that carries the rejected Boolean value `false`. -/
def w0Input : SupervisorInput evidenceGatedSpec :=
  { problem := "model confidence only", yesCertificate? := some false }

theorem w2Input_yields_yes : (supervise evidenceGatedSpec w2Input).verdict = .yes := by decide

theorem w0Input_halts : (supervise evidenceGatedSpec w0Input).verdict = .halt := by decide

-- Print the axiom dependencies of the three theorem declarations.
#print axioms evidenceGated_no_unsupported_yes
#print axioms w2Input_yields_yes
#print axioms w0Input_halts

end OperatorKO7.Meta.LicensedBoundaryCalculus.PlugInstance
