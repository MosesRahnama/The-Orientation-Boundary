import OperatorKO7.Meta.ReverseMathOmega3WellOrdering
import OperatorKO7.Meta.DependencyPairs_Works

/-!
# Natural-number measure descent for the KO7 dependency-pair relation

The formal principle in this module is generic natural-number measure descent. It is not a
formalization of external SCT soundness or the Arts-Giesl dependency-pair theorem.

* `SctDescentSoundness` is the natural-number measure-descent principle:
  any `ℕ`-valued measure that strictly decreases along a relation certifies well-foundedness. Its
  proof embeds the natural-number measure below the separately defined `ω³` carrier.
* `actualSctSoundness_certifies_ko7_recursor` instantiates that principle at the KO7 recursor's
  dependency-pair rank `dpRank`, yielding `WellFounded DPPairRev`.

## Relation orientation

`OperatorKO7.MetaDependencyPairs.DPPairRev` is the converse of the forward dependency pair `DPPair`
(`dpPairRev_sub_rank : DPPairRev x y → dpRank x < dpRank y`). The termination target used here is
`WellFounded DPPairRev`, with `dpRank` decreasing along reverse-DP descending chains. Applying an
additional converse would instead target `WellFounded DPPair`.
-/

set_option autoImplicit false

universe u

namespace OperatorKO7.ReverseMath

open OperatorKO7.ReverseMathOmega3 (nat_measure_terminates_within_omega3)

/-- Any `ℕ`-valued measure `μ` that
strictly decreases along `R` (`R a b → μ b < μ a`) certifies that the reversed relation
`fun a b => R b a` is well-founded. -/
def SctDescentSoundness : Prop :=
  ∀ {α : Type u} (μ : α → Nat) (R : α → α → Prop),
    (∀ a b, R a b → μ b < μ a) → WellFounded (fun a b => R b a)

/-- The natural-number measure principle follows by embedding each measure value below `ω³`. -/
theorem sctDescentSoundness_holds : SctDescentSoundness.{u} :=
  fun μ _R hdesc => nat_measure_terminates_within_omega3 μ hdesc

/-- Instantiate the natural-number measure principle at `dpRank` to obtain well-foundedness of the
reverse dependency-pair relation `DPPairRev`. -/
theorem actualSctSoundness_certifies_ko7_recursor (h : SctDescentSoundness.{0}) :
    WellFounded OperatorKO7.MetaDependencyPairs.DPPairRev :=
  h OperatorKO7.MetaDependencyPairs.dpRank
    (fun x y => OperatorKO7.MetaDependencyPairs.DPPairRev y x)
    (fun _ _ hab => OperatorKO7.MetaDependencyPairs.dpPairRev_sub_rank hab)

/-- Well-foundedness of `DPPairRev` obtained from `dpRank` through the natural-number measure
principle. -/
theorem ko7_recursor_terminates_via_sct :
    WellFounded OperatorKO7.MetaDependencyPairs.DPPairRev :=
  actualSctSoundness_certifies_ko7_recursor sctDescentSoundness_holds

#check sctDescentSoundness_holds
#print axioms sctDescentSoundness_holds
#check actualSctSoundness_certifies_ko7_recursor
#print axioms actualSctSoundness_certifies_ko7_recursor
#check ko7_recursor_terminates_via_sct
#print axioms ko7_recursor_terminates_via_sct

end OperatorKO7.ReverseMath
