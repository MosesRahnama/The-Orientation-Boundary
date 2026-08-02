import OperatorKO7.Meta.InformationTheoreticConfession
import OperatorKO7.Meta.ConfessionMethod_UniversalInstances

/-!
# Licensed carrier-factorisation surface (Informational Incompleteness, Section 9)

Section 9 of `Rahnama_Informational_Incompleteness.tex` imports the confession
universal-quotient surface as the licensed-carrier-factorisation language:
`thm:universal-char` (universal characterisation of confession routes),
the forward direction of `thm:gauge-fixing-imported` (gauge-fixing), and the
four-route H-equivalence. This module re-exports those already-mechanized
theorems into the Informational Incompleteness namespace as the confession-side
INGREDIENTS of the escape (`UniversalDeficit.universal_witnessChannel_deficit` is
the direct-interface deficit side).

SCOPE (do not overclaim, Gate R3): this module re-exports ingredients only. It
does NOT prove `cor:univ-deficit-via-char` (`thm:universal-deficit` clause (3)),
which is a statement about the witness-channel DEFICIT obtained by combining the
H-equivalence below with the duality chain (`WitnessChannelBoundary`) through a
confession-move <-> witness-tower bridge. That combined corollary is a separate,
not-yet-built target (`MASTER_ROADMAP` T14.II-T10b). The re-exported
`all_existing_confession_routes_are_HEquivalent_to_canonical` is purely about
H-equivalence of confession moves and asserts nothing about the deficit by itself.

Re-exports use the `export` command, so the re-exported names refer to the exact
upstream declarations with no restatement and no risk of statement drift
(Bible R3 / W3). The confession surface is heavily parameterized
(`GenericConfessionMove X P License`), so `export` is the correct re-export
mechanism (a value alias would have to reproduce the full binder structure).

Re-exported into `OperatorKO7.Meta.InformationalIncompleteness.LicensedFactorisation`:

* `universal_confession_characterization`: `method ∈ allConfessionMethods →
  Refines (method move) canonical` (`thm:universal-char` factorization direction)
* `gauge_fixing_identity`: `HEquivalent M₁ M₂ → Refines M₁ M₂ ∧ Refines M₂ M₁`
  (FORWARD direction of `thm:gauge-fixing-imported`; the paper states the
  biconditional, the upstream Lean proves the forward implication)
* `confession_cost_floor` (per-bit Landauer floor on released heat)
* `canonical_confession_minimizes_discarded_information`
* `optimal_confession_universal_property`
* `all_existing_confession_routes_are_HEquivalent_to_canonical`: the four routes
  DP / counter-projection / SCT / argument-filtering are each `HEquivalent` to the
  canonical move (H-equivalence INGREDIENT behind clause (3), NOT the deficit
  statement)

## Audit slots

```
Relation: confession-move surface (universal-quotient); not a rewriting relation.
Closure:  not applicable.
Trust:    kernel-only re-exports (`export`) of upstream confession theorems.
Scope:    the canonical confession move and its H-equivalence class.
```
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.InformationalIncompleteness.LicensedFactorisation

export OperatorKO7.Meta.InformationTheoreticConfession
  (universal_confession_characterization
   gauge_fixing_identity
   confession_cost_floor
   canonical_confession_minimizes_discarded_information
   optimal_confession_universal_property)

export OperatorKO7.Meta.ConfessionMethodUniversalInstances
  (all_existing_confession_routes_are_HEquivalent_to_canonical)

/-- Audit anchor for the licensed-carrier-factorisation surface. -/
def licensed_factorisation_anchor : String :=
  "OperatorKO7.Meta.InformationalIncompleteness.LicensedFactorisation.universal_confession_characterization"

end OperatorKO7.Meta.InformationalIncompleteness.LicensedFactorisation
