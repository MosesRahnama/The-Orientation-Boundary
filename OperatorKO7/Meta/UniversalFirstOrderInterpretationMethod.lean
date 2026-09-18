import Mathlib.Logic.ExistsUnique
import Mathlib.Tactic.Cases

/-!
# Universal First-Order Interpretation Method Tags

## Formal Scope

The ten constructors are unrestricted tagged cases and universalMethodVerdict is assigned by pattern matching. The file does not import or connect the cited method substrates, and admitsStepsUnconditionally is defined from the verdict rather than independent orientation evidence.
-/

set_option linter.dupNamespace false

namespace OperatorKO7.UniversalFirstOrderInterpretationMethod

/-! ## Carrier -/

/-- Unrestricted natural-number tag used by the direct-schema constructor.
This abbreviation does not enforce a finite index range. -/
abbrev DirectSchemaBarrierIndex : Type := Nat

/-- Four verdict tags assigned by `universalMethodVerdict`. The constructors
carry labels only; their names do not provide termination, orientation,
licensing, or external-certificate evidence. -/
inductive UniversalMethodVerdict
  | w0_blocked
  | w1_licensed
  | w2_licensed
  | externally_certified
  deriving DecidableEq, Repr

/-- Ten tagged constructor families. Every constructor carries an unrestricted
natural-number index, and this type contains no substrate object or proof that
the tags exhaust an external method universe. -/
inductive UniversalFirstOrderInterpretationMethod : Type
  /-- A direct-schema-barrier tag. -/
  | directSchemaBarrier (idx : DirectSchemaBarrierIndex)
  /-- A transparent-polynomial nonlinear tag. -/
  | transparentNonlinearMember (idx : Nat)
  /-- An unconstrained nonlinear tag. -/
  | unconstrainedNonlinearMember (idx : Nat)
  /-- An FBI-family tag. -/
  | fbiGenericMember (idx : Nat)
  /-- An unrestricted-matrix tag. -/
  | matrixUnrestrictedMember (idx : Nat)
  /-- A generic dependency-pair tag. -/
  | genericDPMember (idx : Nat)
  /-- A semantic-method tag. -/
  | semanticMember (idx : Nat)
  /-- A W_1-license tag. -/
  | w1LicensedEscape (idx : Nat)
  /-- A W_2-license tag. -/
  | w2LicensedEscape (idx : Nat)
  /-- An external-certificate tag. -/
  | ko7CertifiedExternal (idx : Nat)
  deriving DecidableEq, Repr

/-! ## Tag Projection -/

/-- Constructor-to-verdict tag projection. The first seven constructors map to
`w0_blocked`; the final three map to their correspondingly named tags. This is
a definition by cases, not a proof about an external method substrate. -/
def universalMethodVerdict :
    UniversalFirstOrderInterpretationMethod → UniversalMethodVerdict
  | .directSchemaBarrier _         => .w0_blocked
  | .transparentNonlinearMember _  => .w0_blocked
  | .unconstrainedNonlinearMember _ => .w0_blocked
  | .fbiGenericMember _            => .w0_blocked
  | .matrixUnrestrictedMember _    => .w0_blocked
  | .genericDPMember _             => .w0_blocked
  | .semanticMember _              => .w0_blocked
  | .w1LicensedEscape _            => .w1_licensed
  | .w2LicensedEscape _            => .w2_licensed
  | .ko7CertifiedExternal _        => .externally_certified

/-- Every tagged constructor has the unique value returned by
`universalMethodVerdict`. -/
theorem universal_first_order_method_classification
    (m : UniversalFirstOrderInterpretationMethod) :
    ∃! verdict : UniversalMethodVerdict,
      universalMethodVerdict m = verdict := by
  refine ⟨universalMethodVerdict m, rfl, ?_⟩
  intros y hy
  exact hy.symm

/-! ## Auxiliary Predicates -/

/-- The method's verdict is `w0_blocked`. -/
def isW0Blocked (m : UniversalFirstOrderInterpretationMethod) : Prop :=
  universalMethodVerdict m = .w0_blocked

/-- The method's verdict is one of `w1_licensed`, `w2_licensed`,
or `externally_certified`. The "licensed-via-something" disjunction
that the dichotomy theorem consumes. -/
def isLicensedViaW1W2OrExternal
    (m : UniversalFirstOrderInterpretationMethod) : Prop :=
  universalMethodVerdict m = .w1_licensed ∨
    universalMethodVerdict m = .w2_licensed ∨
    universalMethodVerdict m = .externally_certified

/-! ## Verdict-Inequality Alias -/

/-- Historical API name for the proposition that a tag is not `w0_blocked`.
The definition contains no rewrite relation or orientation witness. -/
def admitsStepsUnconditionally
    (m : UniversalFirstOrderInterpretationMethod) : Prop :=
  universalMethodVerdict m ≠ .w0_blocked

/-- The dichotomy at the verdict layer: every method either is
`w0_blocked` OR is licensed via W_1 / W_2 / external. -/
theorem universal_method_verdict_dichotomy
    (m : UniversalFirstOrderInterpretationMethod) :
    isW0Blocked m ∨ isLicensedViaW1W2OrExternal m := by
  unfold isW0Blocked isLicensedViaW1W2OrExternal
  cases m <;> simp [universalMethodVerdict]

/-- The verdicts `w0_blocked` and any of the licensed variants are
mutually exclusive (different enum constructors). -/
theorem isW0Blocked_iff_not_licensed
    (m : UniversalFirstOrderInterpretationMethod) :
    isW0Blocked m ↔ ¬ isLicensedViaW1W2OrExternal m := by
  unfold isW0Blocked isLicensedViaW1W2OrExternal
  cases m <;> simp [universalMethodVerdict]

theorem admitsStepsUnconditionally_iff_licensed
    (m : UniversalFirstOrderInterpretationMethod) :
    admitsStepsUnconditionally m ↔ isLicensedViaW1W2OrExternal m := by
  unfold admitsStepsUnconditionally isLicensedViaW1W2OrExternal
  cases m <;> simp [universalMethodVerdict]

end OperatorKO7.UniversalFirstOrderInterpretationMethod
