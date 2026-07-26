import OperatorKO7.Meta.BoundaryOperator.UniversalDecidableW0
import OperatorKO7.Meta.Plugs.LawUSStateCA.Routes
import OperatorKO7.Meta.Plugs.PharmaUSFda.Routes
import OperatorKO7.Meta.Plugs.QuantumQecPilot.Routes

/-!
# Three-tier certification-chain interface

`CertificationChain` stores a W0 carrier and matrix, finite W1 and W2 catalogs,
catalog-completeness fields, and duplicate-freedom fields. Its projection
theorems expose those stored obligations:

* W0 values satisfy the imported three-class cardinality trichotomy;
* every W1 and W2 value belongs to its supplied catalog;
* the three enum ranks satisfy W0 < W1 < W2.

`lawChain`, `pharmaChain`, and `qecChain` are the three supplied fixtures. The
module proves projections for those fixtures; it carries no quantification over
an external universe of plugs.
-/

namespace OperatorKO7.Meta.BoundaryOperator.UniversalCertificationChain

open OperatorKO7.Meta.Universal.ClassifyUniversal
open OperatorKO7.Meta.BoundaryOperator.UniversalDecidableW0
open OperatorKO7.Meta.Plugs.LawUSStateCA
open OperatorKO7.Meta.Plugs.LawUSStateCA.DecidableW0
open OperatorKO7.Meta.Plugs.PharmaUSFda
open OperatorKO7.Meta.Plugs.PharmaUSFda.DecidableW0
open OperatorKO7.Meta.Plugs.QuantumQecPilot
open OperatorKO7.Meta.Plugs.QuantumQecPilot.DecidableW0

/-- The three witness tiers of a certification chain. -/
inductive CertTier
  | w0
  | w1
  | w2
  deriving DecidableEq, Repr

/-- Tier rank making the chain ordering explicit. -/
def CertTier.rank : CertTier → Nat
  | .w0 => 0
  | .w1 => 1
  | .w2 => 2

/-- The three enum ranks satisfy W0 < W1 < W2. -/
theorem cert_tiers_strictly_ascend :
    CertTier.w0.rank < CertTier.w1.rank ∧ CertTier.w1.rank < CertTier.w2.rank := by
  decide

/-- Interface storing W0 matrix data, finite W1 and W2 catalogs, completeness
proofs for those catalogs, and duplicate-freedom proofs. -/
structure CertificationChain where
  W0 : Type
  W1 : Type
  W2 : Type
  w0Matrix : W0 → FiniteInformationMatrix
  w1Catalog : List W1
  w2Catalog : List W2
  w1_complete : ∀ r : W1, r ∈ w1Catalog
  w2_complete : ∀ r : W2, r ∈ w2Catalog
  w1_nodup : w1Catalog.Nodup
  w2_nodup : w2Catalog.Nodup

namespace CertificationChain

/-- Every W0 value in a supplied chain satisfies the imported cardinality trichotomy. -/
theorem chain_w0_trichotomy (C : CertificationChain) (w : C.W0) :
    (classifyUniversal (C.w0Matrix w)).worstClass = CardinalityClass.plainTextApplication ∨
    (classifyUniversal (C.w0Matrix w)).worstClass = CardinalityClass.noMapping ∨
    (classifyUniversal (C.w0Matrix w)).worstClass = CardinalityClass.ambiguityDuplication :=
  universal_w0_trichotomy (C.w0Matrix w)

/-- Project the supplied W1 catalog-completeness field. -/
theorem chain_w1_closed (C : CertificationChain) (r : C.W1) : r ∈ C.w1Catalog :=
  C.w1_complete r

/-- Project the supplied W2 catalog-completeness field. -/
theorem chain_w2_closed (C : CertificationChain) (r : C.W2) : r ∈ C.w2Catalog :=
  C.w2_complete r

end CertificationChain

/-- LawUSStateCA certification chain instance. -/
def lawChain : CertificationChain where
  W0 := LawUSStateCAW0Carrier
  W1 := LawUSStateCAW1Route
  W2 := LawUSStateCAW2Route
  w0Matrix := lawUSStateCAW0Matrix
  w1Catalog := lawUSStateCAW1Routes
  w2Catalog := lawUSStateCAW2Routes
  w1_complete := by intro r; cases r <;> decide
  w2_complete := by intro r; cases r <;> decide
  w1_nodup := lawUSStateCAW1Routes_nodup
  w2_nodup := lawUSStateCAW2Routes_nodup

/-- PharmaUSFda certification chain instance. -/
def pharmaChain : CertificationChain where
  W0 := PharmaUSFdaW0Carrier
  W1 := PharmaUSFdaW1Route
  W2 := PharmaUSFdaW2Route
  w0Matrix := pharmaUSFdaW0Matrix
  w1Catalog := pharmaUSFdaW1Routes
  w2Catalog := pharmaUSFdaW2Routes
  w1_complete := by intro r; cases r <;> decide
  w2_complete := by intro r; cases r <;> decide
  w1_nodup := pharmaUSFdaW1Routes_nodup
  w2_nodup := pharmaUSFdaW2Routes_nodup

/-- QuantumQecPilot certification chain instance. -/
def qecChain : CertificationChain where
  W0 := QuantumQecPilotW0Carrier
  W1 := QuantumQecPilotW1Route
  W2 := QuantumQecPilotW2Route
  w0Matrix := quantumQecPilotW0Matrix
  w1Catalog := quantumQecPilotW1Routes
  w2Catalog := quantumQecPilotW2Routes
  w1_complete := by intro r; cases r <;> decide
  w2_complete := by intro r; cases r <;> decide
  w1_nodup := quantumQecPilotW1Routes_nodup
  w2_nodup := quantumQecPilotW2Routes_nodup

/-- Project W1 catalog completeness for the Law fixture. -/
theorem lawChain_w1_closed (r : LawUSStateCAW1Route) : r ∈ lawChain.w1Catalog :=
  lawChain.chain_w1_closed r

/-- Project W2 catalog completeness for the Pharma fixture. -/
theorem pharmaChain_w2_closed (r : PharmaUSFdaW2Route) : r ∈ pharmaChain.w2Catalog :=
  pharmaChain.chain_w2_closed r

/-- Apply the imported W0 trichotomy to the QEC fixture. -/
theorem qecChain_w0_trichotomy (w : QuantumQecPilotW0Carrier) :
    (classifyUniversal (qecChain.w0Matrix w)).worstClass = CardinalityClass.plainTextApplication ∨
    (classifyUniversal (qecChain.w0Matrix w)).worstClass = CardinalityClass.noMapping ∨
    (classifyUniversal (qecChain.w0Matrix w)).worstClass = CardinalityClass.ambiguityDuplication :=
  qecChain.chain_w0_trichotomy w

/-- The Law fixture has five W1 rows and three W2 rows. -/
theorem lawChain_catalog_sizes :
    lawChain.w1Catalog.length = 5 ∧ lawChain.w2Catalog.length = 3 :=
  ⟨lawUSStateCAW1Routes_length, lawUSStateCAW2Routes_length⟩

/-- String identifier for the W1 completeness projection. -/
def universal_certification_chain_anchor : String :=
  "OperatorKO7.Meta.BoundaryOperator.UniversalCertificationChain.CertificationChain.chain_w1_closed"

end OperatorKO7.Meta.BoundaryOperator.UniversalCertificationChain
