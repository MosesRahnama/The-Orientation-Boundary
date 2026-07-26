import Lean
import Lean.Util.CollectAxioms

/-!
# Build-time manuscript-anchor verification

This module supplies a term elaborator for resolving a requested declaration
by fully qualified name or by a unique declaration-name suffix. Successful
resolution records the `Lean.Name`, the pretty-printer rendering of its type,
the result of `Lean.collectAxioms`, and whether the declaration type is a
proposition. Missing or ambiguous requests elaborate to `none`.

## Formal scope

Relation: manuscript anchor spelling to a live declaration in the imported environment.
Closure: fully qualified-name or unique-suffix resolution, rendered type, and collected axioms.
Trust: build-time metaprogramming over the imported environment.
Scope: declaration liveness and metaprogram output; manuscript-prose equivalence is outside this check.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.Audit

open Lean Elab Term Meta

/-- Coarse declaration shape captured from the live declaration type. -/
inductive LeanDeclarationKind
  | proposition
  | data
  deriving DecidableEq, Repr

/-- Statement-carrying build-time receipt for one resolved manuscript anchor. -/
structure LeanAnchorVerification where
  requested : String
  requested_nonempty : requested ≠ ""
  resolvedSpelling : String
  resolvedName : Lean.Name
  resolvedName_eq_spelling : resolvedName = resolvedSpelling.toName
  resolvedSpelling_matches_requested :
    resolvedSpelling = requested ∨
      resolvedSpelling.endsWith ("." ++ requested) = true
  prettyType : String
  prettyType_nonempty : prettyType ≠ ""
  axiomReceipt : List String
  declarationKind : LeanDeclarationKind
  deriving Repr

private def suffixMatches (candidate : Lean.Name) (requested : String) : Bool :=
  let full := candidate.toString
  full == requested || full.endsWith ("." ++ requested)

private def uniqueSuffixResolution
    (env : Environment) (requested : String) : Option Lean.Name :=
  let exact := requested.toName
  if env.contains exact then
    some exact
  else
    let candidates := env.constants.map₂.foldl (init := []) fun found name _ =>
      if suffixMatches name requested then name :: found else found
    match candidates with
    | [name] => some name
    | _ => none

/--
`resolved_manuscript_anchor% "name"` elaborates to a liveness, rendered-type,
and collected-axiom receipt, or to `none` when the requested spelling is
missing or ambiguous.
-/
elab (name := resolvedManuscriptAnchorTerm)
    "resolved_manuscript_anchor% " requestedSyntax:str : term => do
  let requested := requestedSyntax.getString
  let env <- getEnv
  match if requested = "" then none else uniqueSuffixResolution env requested with
  | none =>
      elabTerm (← `(none)) none
  | some resolved =>
      let info := env.constants.find! resolved
      let renderedType := (← ppExpr info.type).pretty
      let typeSort ← inferType info.type
      let kindName :=
        if typeSort.isProp then
          ``LeanDeclarationKind.proposition
        else
          ``LeanDeclarationKind.data
      let axioms ← Lean.collectAxioms resolved
      let axiomStrings := axioms.toList.map Lean.Name.toString
      let requestedLit : TSyntax `term := ⟨Syntax.mkStrLit requested⟩
      let resolvedLit : TSyntax `term := ⟨Syntax.mkStrLit resolved.toString⟩
      let typeLit : TSyntax `term := ⟨Syntax.mkStrLit renderedType⟩
      let axiomLits : Array (TSyntax `term) :=
        axiomStrings.toArray.map fun value => ⟨Syntax.mkStrLit value⟩
      let kindIdent := mkIdent kindName
      let receipt ← `(
        some
          { requested := $requestedLit
            requested_nonempty := by decide
            resolvedSpelling := $resolvedLit
            resolvedName := ($resolvedLit : String).toName
            resolvedName_eq_spelling := by rfl
            resolvedSpelling_matches_requested := by decide
            prettyType := $typeLit
            prettyType_nonempty := by decide
            axiomReceipt := [$[$axiomLits],*]
            declarationKind := $kindIdent })
      elabTerm receipt none

/-- Self-resolution fixture for the public `LeanAnchorVerification` declaration. -/
def anchorVerification_fixture : Option LeanAnchorVerification :=
  resolved_manuscript_anchor%
    "OperatorKO7.Meta.LicensedBoundaryCalculus.Audit.LeanAnchorVerification"

theorem anchorVerification_fixture_resolved :
    anchorVerification_fixture.isSome = true := by
  rfl

#check anchorVerification_fixture_resolved
#print axioms anchorVerification_fixture_resolved

end OperatorKO7.Meta.LicensedBoundaryCalculus.Audit
