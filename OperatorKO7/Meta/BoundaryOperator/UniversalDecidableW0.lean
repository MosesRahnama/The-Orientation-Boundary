import OperatorKO7.Meta.Universal.ClassifyUniversal
import OperatorKO7.Meta.Plugs.LawUSStateCA.DecidableW0
import OperatorKO7.Meta.Plugs.PharmaUSFda.DecidableW0
import OperatorKO7.Meta.Plugs.QuantumQecPilot.DecidableW0

/-!
# Universal decidable W0 classifier (T13.BB-9)

The three finite plug fixtures (Law, Pharma, and QEC in
`Meta/Plugs/*/DecidableW0.lean`) use the scan
`classifyUniversal : FiniteInformationMatrix → ClassificationResult`. This
module states the associated decidability results using decidable equality on
the three cardinality constructors:

* `universalW0PointwiseDecidable`: any single matrix's class is decidable.
* `universalW0WorstClassDecidable` / `universalW0BlockedDecidable`: for any finite
  (`Fintype`) carrier, the whole-carrier W0 decision is decidable in one shot.
* `universal_w0_trichotomy`: every matrix satisfies an inclusive disjunction
  over the three cardinality classes (the W0-level escape / boundary / barrier
  classification:
  `plainTextApplication` escapes, `noMapping` and `ambiguityDuplication` block).

The per-plug corollaries classify the supplied finite rows: every Law row is
unblocked, while one Pharma row and one QEC row have blocking classifications.
These fixture results make no exhaustiveness claim about their application
domains.
-/

namespace OperatorKO7.Meta.BoundaryOperator.UniversalDecidableW0

open OperatorKO7.Meta.Universal.ClassifyUniversal
open OperatorKO7.Meta.Plugs.LawUSStateCA.DecidableW0
open OperatorKO7.Meta.Plugs.PharmaUSFda.DecidableW0
open OperatorKO7.Meta.Plugs.QuantumQecPilot.DecidableW0

/-- For any finite-information matrix, equality of its worst class with a
specified target is decidable from `CardinalityClass` decidable equality. -/
def universalW0PointwiseDecidable
    (m : FiniteInformationMatrix) (target : CardinalityClass) :
    Decidable ((classifyUniversal m).worstClass = target) :=
  inferInstance

/-- Universal constructive W0 decidability (worst-class form): for any finite
carrier with a finite-information-matrix assignment, whether every case attains a
specified target class is decidable in one shot. Constructive: the witness is
`Fintype.decidableForallFintype` over decidable `CardinalityClass` equality. -/
def universalW0WorstClassDecidable {C : Type} [Fintype C]
    (matrix : C → FiniteInformationMatrix) (target : C → CardinalityClass) :
    Decidable (∀ c, (classifyUniversal (matrix c)).worstClass = target c) :=
  Fintype.decidableForallFintype

/-- Universal constructive W0 decidability (blocked form): whether every case in a
finite carrier is W0-unblocked is decidable, constructively. -/
def universalW0BlockedDecidable {C : Type} [Fintype C]
    (matrix : C → FiniteInformationMatrix) :
    Decidable (∀ c, (classifyUniversal (matrix c)).blocked = false) :=
  Fintype.decidableForallFintype

/-- Every finite-information matrix satisfies the inclusive three-constructor
classification supplied by `classifyUniversal_complete`. -/
theorem universal_w0_trichotomy (m : FiniteInformationMatrix) :
    (classifyUniversal m).worstClass = CardinalityClass.plainTextApplication ∨
    (classifyUniversal m).worstClass = CardinalityClass.noMapping ∨
    (classifyUniversal m).worstClass = CardinalityClass.ambiguityDuplication := by
  rcases classifyUniversal_complete m with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

/-- Every row in the supplied twelve-constructor Law fixture is W0-unblocked,
proved by carrier case analysis. -/
theorem law_w0_all_unblocked :
    ∀ c : LawUSStateCAW0Carrier,
      (classifyUniversal (lawUSStateCAW0Matrix c)).blocked = false := by
  intro c; cases c <;> rfl

/-- The advisory-committee row in the supplied Pharma fixture classifies as
`ambiguityDuplication`, yielding a blocking witness. -/
theorem pharma_w0_blocks_on_advisory :
    (classifyUniversal
        (pharmaUSFdaW0Matrix .AdvisoryCommitteeRecommendationEscapeCase)).blocked = true := by
  decide

/-- The abstention-aware row in the supplied QEC fixture classifies as
`noMapping`, yielding a blocking witness. -/
theorem qec_w0_blocks_on_abstention :
    (classifyUniversal
        (quantumQecPilotW0Matrix .AbstentionAwareDecoder)).blocked = true := by
  decide

/-- Package pointwise decidability and finite-carrier blocked decidability. -/
def universal_decidable_w0_anchor : String :=
  "OperatorKO7.Meta.BoundaryOperator.UniversalDecidableW0.universalW0WorstClassDecidable"

end OperatorKO7.Meta.BoundaryOperator.UniversalDecidableW0
