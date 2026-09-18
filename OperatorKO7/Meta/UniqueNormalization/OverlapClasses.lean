import OperatorKO7.Meta.UniqueNormalization.UNStatement
import OperatorKO7.Meta.UniqueNormalization.RationalUnification

/-!
# The overlap classes of RTA open problem #79

Campaign: `Roadmaps\klop\ROADMAP.md`, WP-K1.
Definition freeze: `Roadmaps\klop\definitions.md` (D4, D6, campaign convention CC1).

## Fidelity block (frozen `definitions.md`, D6)

> "The standard notion of non-overlapping TRSs is based on the notion of
> unifiability, and it can be simplified for Constructor TRSs. A Constructor TRS
> is non-overlapping iff the left-hand sides of any two different rules are not
> unifiable. Replacing 'unifiability' in that setting with 'omega-unifiability'
> provides the analogous (stronger) notion of non-omega-overlapping. A similar
> notion is that of almost non-omega-overlapping TRSs, which means that
> non-variable proper subterms of left-hand sides of rules are not
> omega-unifiable with left-hand sides of rules, and that root-step is
> deterministic."

The constructor-signature forms are `ConstructorNonOverlapping` and
`ConstructorNonOmegaOverlapping`. The general forms follow frozen campaign
convention CC1:

> "A TRS `R` is non-omega-overlapping when for every pair of rules
> `l1 -> r1`, `l2 -> r2` of `R` taken with disjoint variable sets, and every
> position `p` of `l1` with `l1|p` not a variable, `l1|p` and `l2` are not
> omega-unifiable, except when the two rules are the same rule and `p` is the
> root position."

Positions are carried here by the subterm relation rather than by position
strings. The two agree for this condition: a repeated subterm at two positions
gives the same unifiability question, and the root position is singled out by
`s = r1.lhs` instead of by `p = []`.

`OmegaUnifiable` is represented computationally by the union/find-style
certificate from `RationalUnification.lean`. That module now proves
`omegaUnifiable_iff_infinite`, identifying the certificate exactly with
substitution into potentially infinite first-order M-type terms. Consequently
`NonOmegaOverlapping` below has the paper's infinitary meaning, while retaining
the finite certificate as its proof-engine representation.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Unifiability -/

/-- Unifiability in the two-substitution form of frozen definition D4: the two
terms are taken over disjoint variable sets, so a separate substitution acts on
each side. -/
def Unifiable (s t : Term sigma nu) : Prop :=
  ∃ a b : Subst sigma nu, Subst.apply a s = Subst.apply b t

/-- Frozen D4, final sentence: "Unifiability implies omega-unifiability, as all
finite terms inhabit the infinite term universe as well." -/
theorem OmegaUnifiable.of_unifiable {s t : Term sigma nu} (h : Unifiable s t) :
    OmegaUnifiable s t :=
  let ⟨a, b, hab⟩ := h
  omegaUnifiable_of_unifier a b hab

/-! ## Subterms -/

/-- `Subterm s t` holds when `s` occurs as a subterm of `t`, the improper case
`s = t` included. This carries the position quantifier of convention CC1. -/
inductive Subterm : Term sigma nu → Term sigma nu → Prop
  | refl (t : Term sigma nu) : Subterm t t
  | arg {s a : Term sigma nu} {f : sigma} {args : List (Term sigma nu)} :
      a ∈ args → Subterm s a → Subterm s (.app f args)

/-- `s` is a proper subterm of `t`: a subterm of one of `t`'s arguments. -/
def ProperSubterm (s t : Term sigma nu) : Prop :=
  ∃ (f : sigma) (args : List (Term sigma nu)) (a : Term sigma nu),
    t = .app f args ∧ a ∈ args ∧ Subterm s a

theorem Subterm.of_properSubterm {s t : Term sigma nu} (h : ProperSubterm s t) :
    Subterm s t := by
  obtain ⟨f, args, a, rfl, ha, hsa⟩ := h
  exact Subterm.arg ha hsa

/-- A subterm of a variable is that variable. -/
theorem Subterm.eq_of_var {s : Term sigma nu} {x : nu}
    (h : Subterm s (.var x)) : s = .var x := by
  cases h with
  | refl => rfl

/-- A subterm is no larger than the term carrying it. -/
theorem Subterm.size_le {s t : Term sigma nu} (h : Subterm s t) : s.size ≤ t.size := by
  induction h with
  | refl => exact Nat.le_refl _
  | @arg _ _ _ hmem _ ih =>
      exact le_of_lt (lt_of_le_of_lt ih (Term.size_lt_of_mem hmem))

/-- A proper subterm is strictly smaller than the term carrying it. -/
theorem ProperSubterm.size_lt {s t : Term sigma nu} (h : ProperSubterm s t) :
    s.size < t.size := by
  obtain ⟨f, args, a, rfl, ha, hsa⟩ := h
  exact lt_of_le_of_lt hsa.size_le (Term.size_lt_of_mem ha)

/-- A subterm of `t` is either `t` itself or a proper subterm of `t`. -/
theorem Subterm.eq_or_properSubterm {s t : Term sigma nu} (h : Subterm s t) :
    s = t ∨ ProperSubterm s t := by
  cases h with
  | refl => exact Or.inl rfl
  | arg ha hsa => exact Or.inr ⟨_, _, _, rfl, ha, hsa⟩

/-! ## The classes -/

/-- **Non-overlapping**, campaign convention CC1 with finite unifiability: the
only unifiable pair of a non-variable subterm of a left-hand side with a
left-hand side is a rule with itself, at the root. -/
def NonOverlapping (R : TRS sigma nu) : Prop :=
  ∀ r₁ ∈ R, ∀ r₂ ∈ R, ∀ s : Term sigma nu,
    Subterm s r₁.lhs → s.isApp = true → Unifiable s r₂.lhs → r₁ = r₂ ∧ s = r₁.lhs

/-- **Non-omega-overlapping**, campaign convention CC1. `OmegaUnifiable` is the
finite certificate representation proved equivalent to explicit potentially
infinite-term substitution semantics by `omegaUnifiable_iff_infinite`. -/
def NonOmegaOverlapping (R : TRS sigma nu) : Prop :=
  ∀ r₁ ∈ R, ∀ r₂ ∈ R, ∀ s : Term sigma nu,
    Subterm s r₁.lhs → s.isApp = true → OmegaUnifiable s r₂.lhs → r₁ = r₂ ∧ s = r₁.lhs

/-- The root step is deterministic: one term has at most one root contraction. -/
def Deterministic (R : TRS sigma nu) : Prop :=
  ∀ s t u : Term sigma nu, rootStep R s t → rootStep R s u → t = u

/-- **Almost non-omega-overlapping**, frozen D6: no non-variable proper subterm
of a left-hand side omega-unifies with a left-hand side, and the root step is
deterministic. -/
def AlmostNonOmegaOverlapping (R : TRS sigma nu) : Prop :=
  (∀ r₁ ∈ R, ∀ r₂ ∈ R, ∀ s : Term sigma nu,
      ProperSubterm s r₁.lhs → s.isApp = true → ¬ OmegaUnifiable s r₂.lhs)
    ∧ Deterministic R

/-- **Non-overlapping for a Constructor TRS**, frozen D6: "the left-hand sides
of any two different rules are not unifiable". -/
def ConstructorNonOverlapping (R : TRS sigma nu) : Prop :=
  ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ ≠ r₂ → ¬ Unifiable r₁.lhs r₂.lhs

/-- **Non-omega-overlapping for a Constructor TRS**, frozen D6. -/
def ConstructorNonOmegaOverlapping (R : TRS sigma nu) : Prop :=
  ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ ≠ r₂ → ¬ OmegaUnifiable r₁.lhs r₂.lhs

/-! ## The inclusions that hold unconditionally -/

/-- Omega-unifiability is the weaker requirement to refute, so the
omega-condition is the stronger class: every non-omega-overlapping TRS is
non-overlapping. -/
theorem NonOverlapping.of_nonOmegaOverlapping {R : TRS sigma nu}
    (h : NonOmegaOverlapping R) : NonOverlapping R :=
  fun r₁ h₁ r₂ h₂ s hsub happ hu =>
    h r₁ h₁ r₂ h₂ s hsub happ (OmegaUnifiable.of_unifiable hu)

/-- The same inclusion in the constructor-signature form. -/
theorem ConstructorNonOverlapping.of_nonOmegaOverlapping {R : TRS sigma nu}
    (h : ConstructorNonOmegaOverlapping R) : ConstructorNonOverlapping R :=
  fun r₁ h₁ r₂ h₂ hne hu => h r₁ h₁ r₂ h₂ hne (OmegaUnifiable.of_unifiable hu)

/-- The proper-subterm half of `AlmostNonOmegaOverlapping` follows from
convention CC1 with no side condition: a proper subterm of a left-hand side is
never the left-hand side itself, so CC1's single exception cannot apply to it. -/
theorem properSubterm_clause_of_nonOmegaOverlapping {R : TRS sigma nu}
    (h : NonOmegaOverlapping R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, ∀ s : Term sigma nu,
      ProperSubterm s r₁.lhs → s.isApp = true → ¬ OmegaUnifiable s r₂.lhs := by
  intro r₁ h₁ r₂ h₂ s hprop happ hu
  obtain ⟨-, hs⟩ := h r₁ h₁ r₂ h₂ s (Subterm.of_properSubterm hprop) happ hu
  -- `s = r₁.lhs` contradicts `s` being a proper subterm of `r₁.lhs`, because a
  -- proper subterm is strictly smaller.
  have hlt := hprop.size_lt
  rw [hs] at hlt
  omega

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.Unifiable
#check @OperatorKO7.Meta.UniqueNormalization.Subterm
#check @OperatorKO7.Meta.UniqueNormalization.ProperSubterm
#check @OperatorKO7.Meta.UniqueNormalization.NonOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.NonOmegaOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.Deterministic
#check @OperatorKO7.Meta.UniqueNormalization.AlmostNonOmegaOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorNonOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.ConstructorNonOmegaOverlapping

#print axioms OperatorKO7.Meta.UniqueNormalization.OmegaUnifiable.of_unifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.Subterm.eq_or_properSubterm
#print axioms OperatorKO7.Meta.UniqueNormalization.NonOverlapping.of_nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.ConstructorNonOverlapping.of_nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.properSubterm_clause_of_nonOmegaOverlapping
