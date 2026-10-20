import OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleProtocols
import OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleLogic

/-!
# The one-bit terminal gap of the halt-loop pair at every horizon

Manuscript: the terminal-gap paragraph of Proposition `prop:m44-bounded-records`.

At every budget `b` a halting code `c₊` and a diverging code `c₋` share the entry
`Eval_b(c, b) = none` of the bounded record. A protocol whose readings see a code only through
that entry has rows of discrimination zero at the pair, so under the fair prior it acquires zero
information about the pair at every horizon and in the limit, and the terminal gap
`H(Z) - I(Z; T_n)` stays at one bit at every horizon. The resolving channel outside the bounded
records and the `log₂ m` gap on `m` terminals are `haltLoop_resolving_gap_zero` and
`haltLoop_omega_not_uniform`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
open OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleProtocols
open OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleLogic

namespace OperatorKO7.Meta.BoundaryObserver.HaltingTerminalGap

/-- A protocol on the halt-loop pair whose readings see a code only through the entry
`Eval_b(c, b)` of its bounded record. -/
structure BoundedRecordProtocol (A Y : Type) [Fintype A] [Fintype Y] where
  policy : List (A × Y) → FiniteLaw A
  kernel : List (A × Y) → A → Option ℕ → FiniteLaw Y
  stop : List (A × Y) → Bool
  cost : List (A × Y) → A → ℝ
  cost_nonnegative : ∀ h a, 0 ≤ cost h a

variable {A Y : Type} [Fintype A] [Fintype Y]

/-- The protocol on the pair `c₊, c₋` at budget `b` under the fair prior: the target `true` is the
halting code and `false` the diverging one. -/
noncomputable def toProtocol (b : ℕ) (cPos cNeg : Nat.Partrec.Code)
    (R : BoundedRecordProtocol A Y) : FiniteProtocol Bool A Y where
  prior := binaryPriorLaw (1 / 2) (by norm_num) (by norm_num)
  policy := R.policy
  observation h a z := R.kernel h a (Nat.Partrec.Code.evaln b (if z then cPos else cNeg) b)
  stop := R.stop
  cost := R.cost
  cost_nonnegative := R.cost_nonnegative

/-- The fair prior carries one bit. -/
theorem fair_entropy : entropy (binaryPrior (1 / 2)) = 1 := by
  rw [entropy, binaryPrior_entropy, show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.binEntropy_two_inv,
    div_self (Real.log_pos one_lt_two).ne']

/-- Rows read from the shared entry of the bounded record have discrimination zero. -/
theorem boundedRecord_rows_zero (b : ℕ) (cPos cNeg : Nat.Partrec.Code)
    (epos : Nat.Partrec.Code.evaln b cPos b = none)
    (eneg : Nat.Partrec.Code.evaln b cNeg b = none) (R : BoundedRecordProtocol A Y)
    (h : List (A × Y)) (a : A) :
    discrimination ((toProtocol b cPos cNeg R).observation h a true).mass
      ((toProtocol b cPos cNeg R).observation h a false).mass = 0 := by
  have heq : (toProtocol b cPos cNeg R).observation h a true =
      (toProtocol b cPos cNeg R).observation h a false := by
    show R.kernel h a (Nat.Partrec.Code.evaln b cPos b) =
      R.kernel h a (Nat.Partrec.Code.evaln b cNeg b)
    rw [epos, eneg]
  rw [heq]
  exact (discrimination_eq_zero_iff _ _ (fun y => (R.kernel h a _).nonnegative y)
    (fun y => (R.kernel h a _).nonnegative y)).2 rfl

/-- **The one-bit terminal gap at every horizon.** At every budget `b` there are a halting code
and a diverging code such that every protocol reading the entry `Eval_b(c, b)` of the bounded
record acquires zero information about the pair at every horizon and in the limit, so the terminal
gap `H(Z) - I(Z; T_n)` is one bit at every horizon. -/
theorem halting_terminal_gap (b : ℕ) :
    ∃ cPos cNeg : Nat.Partrec.Code, (cPos.eval b).Dom ∧ ¬ (cNeg.eval b).Dom ∧
      Nat.Partrec.Code.evaln b cPos b = Nat.Partrec.Code.evaln b cNeg b ∧
      ∀ {A Y : Type} [Fintype A] [Fintype Y] (R : BoundedRecordProtocol A Y),
        (∀ n bank, HistoryBank n bank →
          terminalMI (toProtocol b cPos cNeg R) n bank = 0 ∧
            entropy (toProtocol b cPos cNeg R).prior.mass -
              terminalMI (toProtocol b cPos cNeg R) n bank = 1) ∧
        informationLimit (toProtocol b cPos cNeg R) = 0 := by
  obtain ⟨cPos, cNeg, hpos, hneg, epos, eneg⟩ := bounded_records_opposite_statuses b
  refine ⟨cPos, cNeg, hpos, hneg, epos.trans eneg.symm, fun R => ?_⟩
  obtain ⟨hmi, hlim⟩ := zeroRows_zero_information (toProtocol b cPos cNeg R)
    (boundedRecord_rows_zero b cPos cNeg epos eneg R)
  refine ⟨fun n bank hb => ⟨hmi n bank hb, ?_⟩, hlim⟩
  rw [hmi n bank hb, sub_zero]
  exact fair_entropy

end OperatorKO7.Meta.BoundaryObserver.HaltingTerminalGap
