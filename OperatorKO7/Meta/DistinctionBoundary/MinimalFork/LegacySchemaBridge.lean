import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.NormalVerdictBreaker
import OperatorKO7.Meta.SafeStep.GenericDiagonalFork

/-!
# Compatibility bridge to the legacy generic diagonal-fork schema

The legacy schema stores an arbitrary `RStar`. Exact-to-legacy conversion fixes
that field to `Reach R`. Reverse semantic transport is licensed only by a
*two-sided* exact-closure certificate.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u
variable {T : Type u}

/-- Exact schema as a legacy schema whose closure is literally `Reach`. -/
def ExactDiagonalForkSchema.toLegacy (S : ExactDiagonalForkSchema T) :
    OperatorKO7.Meta.SafeStep.GenericDiagonalFork.DiagonalForkSchema T where
  R := S.R
  RStar := Reach S.R
  E := S.E
  Z := S.Z
  D := S.D
  refl_rule := S.refl_rule
  diff_rule := S.diff_rule
  rstar_refl := reach_refl
  rstar_single := fun h => reach_step h

/-- Roadmap-stable exact-to-legacy conversion name. The legacy closure field
is definitionally the actual reflexive-transitive closure `Reach S.R`. -/
def exactSchema_to_legacy (S : ExactDiagonalForkSchema T) :
    OperatorKO7.Meta.SafeStep.GenericDiagonalFork.DiagonalForkSchema T :=
  S.toLegacy

/-- Reverse transport requires equality of the legacy closure with the actual
reflexive-transitive closure of its one-step relation. -/
structure ExactClosureCertificate (S : OperatorKO7.Meta.SafeStep.GenericDiagonalFork.DiagonalForkSchema T) : Prop where
  exact : ∀ x y, S.RStar x y ↔ Reach S.R x y

/-- Forget the legacy closure field and retain its one-step verdict architecture. -/
def ExactDiagonalForkSchema.fromLegacy (S : OperatorKO7.Meta.SafeStep.GenericDiagonalFork.DiagonalForkSchema T) :
    ExactDiagonalForkSchema T where
  R := S.R
  E := S.E
  Z := S.Z
  D := S.D
  refl_rule := S.refl_rule
  diff_rule := S.diff_rule

/-- Exact schemas satisfy the reverse-transport closure certificate definitionally. -/
theorem toLegacy_exactClosureCertificate (S : ExactDiagonalForkSchema T) :
    ExactClosureCertificate S.toLegacy := by
  constructor
  intro x y
  rfl

/-- Verdict joinability agrees across a certified legacy/exact bridge. -/
theorem legacy_diagonalVerdictsJoin_iff
    (S : OperatorKO7.Meta.SafeStep.GenericDiagonalFork.DiagonalForkSchema T) (hclose : ExactClosureCertificate S)
    (a : T) :
    OperatorKO7.Meta.SafeStep.GenericDiagonalFork.DiagonalVerdictsJoin S a ↔
      DiagonalVerdictsJoin (ExactDiagonalForkSchema.fromLegacy S) a := by
  constructor
  · rintro ⟨d, hz, hd⟩
    exact ⟨d, (hclose.exact _ _).mp hz, (hclose.exact _ _).mp hd⟩
  · rintro ⟨d, hz, hd⟩
    exact ⟨d, (hclose.exact _ _).mpr hz, (hclose.exact _ _).mpr hd⟩

/-- Local one-step joinability agrees across a certified legacy/exact bridge. -/
theorem legacy_localJoinAt_iff
    (S : OperatorKO7.Meta.SafeStep.GenericDiagonalFork.DiagonalForkSchema T) (hclose : ExactClosureCertificate S)
    (source : T) :
    OperatorKO7.Meta.SafeStep.GenericDiagonalFork.LocalJoinAt S source ↔
      LocalJoinAt (ExactDiagonalForkSchema.fromLegacy S) source := by
  constructor
  · intro hlocal l r hl hr
    rcases hlocal hl hr with ⟨d, hld, hrd⟩
    exact ⟨d, (hclose.exact _ _).mp hld, (hclose.exact _ _).mp hrd⟩
  · intro hlocal l r hl hr
    rcases hlocal hl hr with ⟨d, hld, hrd⟩
    exact ⟨d, (hclose.exact _ _).mpr hld, (hclose.exact _ _).mpr hrd⟩

/-- A proof-bearing upgrade package from a legacy schema to the exact schema.
It records both predicate equivalences, so no arbitrary legacy closure can be
silently treated as reflexive-transitive reachability. -/
structure LegacyExactUpgrade
    (S : OperatorKO7.Meta.SafeStep.GenericDiagonalFork.DiagonalForkSchema T) where
  exactSchema : ExactDiagonalForkSchema T
  exactSchema_eq : exactSchema = ExactDiagonalForkSchema.fromLegacy S
  verdictsJoin_iff : ∀ a,
    OperatorKO7.Meta.SafeStep.GenericDiagonalFork.DiagonalVerdictsJoin S a ↔
      DiagonalVerdictsJoin exactSchema a
  localJoinAt_iff : ∀ source,
    OperatorKO7.Meta.SafeStep.GenericDiagonalFork.LocalJoinAt S source ↔
      LocalJoinAt exactSchema source

/-- A two-sided exact-closure certificate upgrades a legacy schema and transports
both verdict joinability and local one-step joinability exactly. -/
def legacy_to_exact_of_certificate
    (S : OperatorKO7.Meta.SafeStep.GenericDiagonalFork.DiagonalForkSchema T)
    (hclose : ExactClosureCertificate S) : LegacyExactUpgrade S where
  exactSchema := ExactDiagonalForkSchema.fromLegacy S
  exactSchema_eq := rfl
  verdictsJoin_iff := legacy_diagonalVerdictsJoin_iff S hclose
  localJoinAt_iff := legacy_localJoinAt_iff S hclose

/-- Terminal exact data discharges the legacy theorem's opaque nonjoinability
premise when the legacy object came from an exact schema. -/
theorem toLegacy_verdicts_not_join
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) :
    ¬ OperatorKO7.Meta.SafeStep.GenericDiagonalFork.DiagonalVerdictsJoin S.toLegacy a :=
  terminalDiagonal_verdicts_unjoinable S a hterm

/-- The existing generic breaker is recovered as a compatibility corollary of
terminal/distinct exact data. -/
theorem legacy_breaker_of_terminal_distinct
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) :
    ¬ OperatorKO7.Meta.SafeStep.GenericDiagonalFork.LocalJoinAt S.toLegacy (S.E a a) :=
  OperatorKO7.Meta.SafeStep.GenericDiagonalFork.localConfluence_fails_at_diagonal S.toLegacy a
    (toLegacy_verdicts_not_join S a hterm)

/-- Conversely, under exact closure, a legacy terminal certificate yields the
same exact local failure theorem. -/
theorem exact_breaker_from_certified_legacy
    (S : OperatorKO7.Meta.SafeStep.GenericDiagonalFork.DiagonalForkSchema T)
    (hclose : ExactClosureCertificate S) (a : T)
    (hterm : TerminalDiagonal (ExactDiagonalForkSchema.fromLegacy S) a) :
    ¬ OperatorKO7.Meta.SafeStep.GenericDiagonalFork.LocalJoinAt S (S.E a a) := by
  intro hlegacy
  have hexact :
      LocalJoinAt (ExactDiagonalForkSchema.fromLegacy S) (S.E a a) :=
    (legacy_localJoinAt_iff S hclose (S.E a a)).mp hlegacy
  exact localConfluence_fails_of_terminal_distinct
    (ExactDiagonalForkSchema.fromLegacy S) a hterm hexact

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork

