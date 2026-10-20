import OperatorKO7.Meta.BoundaryQuantitative.Profile

/-!
# Licensed quantitative boundary transactions

Relation: coordinatewise obstruction reduction plus explicit transaction cost.
Closure: composition of adjacent finite transactions.
Trust: PROVEN-IN-LEAN, baseline arithmetic and product reasoning.
Scope: shared transaction layer. It proves reduction of profiles, not recovery
of discarded raw payload.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryQuantitative

/-- Transaction-side cost profile, kept separate from obstruction coordinates. -/
structure TransactionCost where
  certificateBits : Nat
  ledgerBits : Nat
  externalAssumptions : Nat
deriving Repr, DecidableEq

/-- Total natural-number transaction cost. -/
def TransactionCost.total (c : TransactionCost) : Nat :=
  c.certificateBits + c.ledgerBits + c.externalAssumptions

/-- Additive combination of transaction costs. -/
def TransactionCost.add (c d : TransactionCost) : TransactionCost where
  certificateBits := c.certificateBits + d.certificateBits
  ledgerBits := c.ledgerBits + d.ledgerBits
  externalAssumptions := c.externalAssumptions + d.externalAssumptions

theorem TransactionCost.total_add (c d : TransactionCost) :
    (c.add d).total = c.total + d.total := by
  cases c
  cases d
  simp [TransactionCost.add, TransactionCost.total]
  omega

/-- Weak licensed transaction: the after-profile is coordinatewise no worse. -/
structure BoundaryTransaction where
  before : ObstructionProfile
  after : ObstructionProfile
  cost : TransactionCost
  coordinateReduction : CoordinateLe after before

/-- Strong licensed transaction: the after-profile is strictly better in at
least one obstruction coordinate. -/
structure StrictBoundaryTransaction extends BoundaryTransaction where
  strictReduction : StrictlyReduces after before

theorem boundaryTransaction_reduces (T : BoundaryTransaction) :
    CoordinateLe T.after T.before := T.coordinateReduction

theorem strictBoundaryTransaction_reduces (T : StrictBoundaryTransaction) :
    StrictlyReduces T.after T.before := T.strictReduction

/-- Compose adjacent transactions. The equality argument is explicit so the
composition cannot silently identify unrelated profiles. -/
def BoundaryTransaction.comp (T U : BoundaryTransaction)
    (h : T.after = U.before) : BoundaryTransaction where
  before := T.before
  after := U.after
  cost := T.cost.add U.cost
  coordinateReduction := by
    exact coordinateLe_trans (by simpa [h] using U.coordinateReduction) T.coordinateReduction

theorem BoundaryTransaction.comp_cost_total (T U : BoundaryTransaction)
    (h : T.after = U.before) :
    (T.comp U h).cost.total = T.cost.total + U.cost.total := by
  exact TransactionCost.total_add T.cost U.cost

/-- Concrete strict transaction witness. -/
def sampleStrictTransaction : StrictBoundaryTransaction where
  before := sampleRawProfile
  after := sampleLicensedProfile
  cost := { certificateBits := 2, ledgerBits := 1, externalAssumptions := 1 }
  coordinateReduction := sampleLicensedProfile_reduces.1
  strictReduction := sampleLicensedProfile_reduces

theorem sampleStrictTransaction_cost_total :
    sampleStrictTransaction.cost.total = 4 := rfl

#print axioms TransactionCost.total_add
#print axioms boundaryTransaction_reduces
#print axioms strictBoundaryTransaction_reduces
#print axioms BoundaryTransaction.comp_cost_total
#print axioms sampleStrictTransaction_cost_total

end OperatorKO7.Meta.BoundaryQuantitative
