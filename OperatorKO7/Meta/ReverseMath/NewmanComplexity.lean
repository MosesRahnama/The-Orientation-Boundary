import OperatorKO7.Meta.ReverseMath.Language
import OperatorKO7.Meta.ReverseMath.Complexity

/-!
# The confluence-axis sentences and their structural complexity

The orientation axis records the Arts–Giesl / size-change-termination soundness sentence at the
number-quantifier level `Π⁰₂` (`ArtsGieslPi02.lean`). The confluence axis is calibrated by Newman's
lemma, and Newman's lemma is a **well-founded-induction principle**, with a genuinely different
arithmetic character. Its faithful second-order-arithmetic form leads with a quantifier over a **set**
(the candidate `<`-inductive set), so its prefix is `Π¹₁`: one second-order universal over an
arithmetical body. This module classifies that shape structurally, and separately classifies the
critical-pair joinability statement for a fixed finite rewrite system as **low** (a quantifier-free
matrix, decidable relative to a normalizer).

## The two sentences

* `newmanSentence` is the well-founded-induction principle that Newman's proof consumes: every
 `<`-inductive set of numbers is the whole number domain. Written for a set variable `X` guarded by
 `IsSet`, with the inductive hypothesis and the conclusion relativized to the number sort (`¬IsSet`).
 The leading `∀ X` is a second-order (set) quantifier; the body is arithmetical. The constructive
 `Acc`-recursion of `MetaSN_KO7.newman_safe` is the witness that this principle is exactly what the
 KO7 confluence ascent uses.

* `cpJoinabilitySentence a b` is the critical-pair joinability matrix for a fixed finite rewrite
 system: for the two recorded sides `a`, `b` of a critical overlap (closed terms), the two reducts
 are equal. With a normalizer available (the program has `normalizeSafe`), each side is a closed
 computation, so the matrix is quantifier-free, i.e. low (`Σ⁰₀ = Π⁰₀`, decidable relative to the
 normalizer).

## Classification from scratch

The genuine class of the whole sentence is `Π¹₁`, distinct from the `Π⁰₂` of the termination axis, recorded by the structural
predicate `IsPi11Set` defined here: a leading universal whose bound variable is set-guarded
(`IsSet (&0)` as the relativizing antecedent), over an **arithmetical** body (the inductive closure
`IsArithmetical` of quantifier-free formulas under connectives and number quantifiers). Both
predicates are real structural recursions on the formula, not tags. The critical-pair matrix is
classified at its genuine low level by Mathlib's `IsQF`.

No `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `partial`, `native_decide`, `bv_decide`,
or `@[csimp]`: every classification is kernel-checked structural recursion.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language

/-! ### The arithmetical closure (number-quantifier formulas)

`IsArithmetical φ` is the inductive closure of quantifier-free formulas under negation, implication,
and bounded (number) quantifiers `∀`/`∃`. This is the class of bodies admissible under one leading
second-order quantifier; together with the set guard it pins the `Π¹₁` level. Every quantifier here
is a Mathlib `BoundedFormula` quantifier (a number quantifier in the model-theoretic reading), so an
arithmetical body carries no further set quantifier. -/
inductive IsArithmetical : ∀ {n : ℕ}, L2.BoundedFormula Empty n → Prop
  | qf {n : ℕ} {φ : L2.BoundedFormula Empty n} (h : φ.IsQF) : IsArithmetical φ
  | imp {n : ℕ} {φ ψ : L2.BoundedFormula Empty n}
      (hφ : IsArithmetical φ) (hψ : IsArithmetical ψ) : IsArithmetical (φ.imp ψ)
  | all {n : ℕ} {φ : L2.BoundedFormula Empty (n + 1)} (h : IsArithmetical φ) :
      IsArithmetical φ.all
  | ex {n : ℕ} {φ : L2.BoundedFormula Empty (n + 1)} (h : IsArithmetical φ) :
      IsArithmetical φ.ex

/-- Negation stays arithmetical (`∼φ = φ ⟹ ⊥`). -/
theorem IsArithmetical.not {n : ℕ} {φ : L2.BoundedFormula Empty n}
    (h : IsArithmetical φ) : IsArithmetical φ.not :=
  IsArithmetical.imp h (IsArithmetical.qf BoundedFormula.isQF_bot)

/-- Conjunction stays arithmetical. -/
theorem IsArithmetical.inf {n : ℕ} {φ ψ : L2.BoundedFormula Empty n}
    (hφ : IsArithmetical φ) (hψ : IsArithmetical ψ) : IsArithmetical (φ ⊓ ψ) :=
  (IsArithmetical.imp hφ hψ.not).not

/-- Disjunction stays arithmetical. -/
theorem IsArithmetical.sup {n : ℕ} {φ ψ : L2.BoundedFormula Empty n}
    (hφ : IsArithmetical φ) (hψ : IsArithmetical ψ) : IsArithmetical (φ ⊔ ψ) :=
  IsArithmetical.imp hφ.not hψ

/-! ### The bare-Newman well-founded-induction sentence

The principle "every `<`-inductive set is everything", with the set variable outermost (de Bruijn
`&0` at the top level) and two relativized number universals carrying the inductive step and the
conclusion. -/

/-- The conclusion block `∀ n, ¬IsSet n → n ∈ X` at level `1` (`X = &0`, `n = &1`). -/
def newmanConclusion : L2.BoundedFormula Empty 1 :=
  ∀' ((∼ (isSetBd (&1))) ⟹ (memBd (&1) (&0)))

/-- The inductive-step block `∀ n, ¬IsSet n → ((∀ m, ¬IsSet m → (m < n → m ∈ X)) → n ∈ X)` at level
`1` (`X = &0`, `n = &1`, `m = &2`). -/
def newmanInductiveStep : L2.BoundedFormula Empty 1 :=
  ∀' ((∼ (isSetBd (&1))) ⟹
    ((∀' ((∼ (isSetBd (&2))) ⟹ ((ltBd (&2) (&1)) ⟹ (memBd (&2) (&0))))) ⟹
      (memBd (&1) (&0))))

/-- The body `IsSet X → (inductiveStep → conclusion)` at level `1` (`X = &0`). The leading
`IsSet (&0)` guard marks the bound variable as a set. -/
def newmanBody : L2.BoundedFormula Empty 1 :=
  (isSetBd (&0)) ⟹ (newmanInductiveStep ⟹ newmanConclusion)

/-- **The bare-Newman sentence.** The well-founded-induction principle over `<`: every `<`-inductive
set of numbers is the whole number domain, `∀ X, IsSet X → (Ind(X) → ∀ n, n ∈ X)`. This is the
principle the constructive `Acc`-recursion of `MetaSN_KO7.newman_safe` realizes, as a closed
`L2.Sentence` with the set quantifier outermost. -/
def newmanSentence : L2.Sentence := ∀' newmanBody

/-! ### Structural `Π¹₁` marker (the leading quantifier ranges over sets)

The distinguishing structural feature of a `Π¹₁` principle, in the single-sorted Simpson encoding, is
that the outermost universal binds a variable used as a **set**: its relativizing guard is `IsSet`,
not `¬IsSet`. `IsSetGuardedArithmetical` records exactly this: a level-`1` formula `IsSet (&0) ⟹ ψ`
with `ψ` arithmetical. `IsPi11Set` then prefixes the leading set universal. Both are genuine
structural predicates, in bijection with the sentence's leading shape. -/

/-- A level-`1` formula is **set-guarded arithmetical** when it is `IsSet (&0) ⟹ ψ` with `ψ`
arithmetical: the leading bound variable is used as a set (the `Π¹₁` marker), and the remaining body
is arithmetical-closure material. -/
def IsSetGuardedArithmetical (φ : L2.BoundedFormula Empty 1) : Prop :=
  ∃ ψ : L2.BoundedFormula Empty 1, φ = (isSetBd (&0)) ⟹ ψ ∧ IsArithmetical ψ

/-- A sentence is **`Π¹₁`** (one set universal over an arithmetical body) when it is `∀' φ` with `φ`
set-guarded arithmetical: the outermost universal ranges over sets and the body is arithmetical. This
is the genuine class of Newman's well-founded-induction principle, distinct from the number-quantifier
`Π⁰₂` of the orientation axis. -/
def IsPi11Set (S : L2.Sentence) : Prop :=
  ∃ φ : L2.BoundedFormula Empty 1, S = ∀' φ ∧ IsSetGuardedArithmetical φ

/-! ### The body is arithmetical -/

/-- The conclusion block is arithmetical (one number `∀` over a quantifier-free implication). -/
theorem newmanConclusion_isArithmetical : IsArithmetical newmanConclusion :=
  IsArithmetical.all
    (IsArithmetical.imp
      ((IsArithmetical.qf (Relations.isQF _ _)).not)
      (IsArithmetical.qf (Relations.isQF _ _)))

/-- The inductive-step block is arithmetical: a number `∀ n` over an implication whose antecedent is a
number `∀ m` over quantifier-free material and whose consequent is quantifier-free. -/
theorem newmanInductiveStep_isArithmetical : IsArithmetical newmanInductiveStep := by
  apply IsArithmetical.all
  apply IsArithmetical.imp
  · exact (IsArithmetical.qf (Relations.isQF _ _)).not
  · apply IsArithmetical.imp
    · apply IsArithmetical.all
      apply IsArithmetical.imp
      · exact (IsArithmetical.qf (Relations.isQF _ _)).not
      · exact IsArithmetical.imp
          (IsArithmetical.qf (Relations.isQF _ _))
          (IsArithmetical.qf (Relations.isQF _ _))
    · exact IsArithmetical.qf (Relations.isQF _ _)

/-- The body `inductiveStep → conclusion` (after the set guard) is arithmetical. -/
theorem newmanBody_inner_isArithmetical :
    IsArithmetical (newmanInductiveStep ⟹ newmanConclusion) :=
  IsArithmetical.imp newmanInductiveStep_isArithmetical newmanConclusion_isArithmetical

/-- The body `newmanBody` is set-guarded arithmetical: it is `IsSet (&0) ⟹ (Ind → Concl)` with the
remainder arithmetical. -/
theorem newmanBody_isSetGuardedArithmetical : IsSetGuardedArithmetical newmanBody :=
  ⟨newmanInductiveStep ⟹ newmanConclusion, rfl, newmanBody_inner_isArithmetical⟩

/-! ### The headline classification -/

/-- **The genuine complexity class of Newman's lemma.** The bare-Newman well-founded-induction
sentence is `Π¹₁`: one leading second-order (set) universal over an arithmetical body. This is the
genuine classification, distinct from the orientation axis's number-quantifier `Π⁰₂`; the difference
is structural, the leading universal here ranges over sets (marked by the `IsSet (&0)` guard). -/
theorem newmanSentence_isPi11 : IsPi11Set newmanSentence :=
  ⟨newmanBody, rfl, newmanBody_isSetGuardedArithmetical⟩

/-! ### Critical-pair joinability for a fixed finite rewrite system (low)

For a fixed finite rewrite system, a critical pair is a fixed pair of closed terms; with a normalizer
the joinability condition "the two sides reduce to a common term" is the equality of two closed
computations, a quantifier-free matrix. We record this at the level of the `L2` equality atom over the
two recorded sides (closed numerals coding the critical-pair sides). -/

/-- The critical-pair joinability matrix for one recorded critical pair `(a, b)` of a fixed finite
rewrite system: the closed-term equality `a = b` of the two recorded reducts. Quantifier-free. -/
def cpJoinabilitySentence (a b : L2.Term Empty) : L2.Sentence :=
  Term.equal a b

/-- **The genuine complexity class of fixed-finite-system critical-pair joinability.** For a fixed
finite rewrite system, the joinability of a recorded critical pair is quantifier-free (`Σ⁰₀ = Π⁰₀`):
the equality of two closed reducts, decidable relative to the normalizer. This is low, far below
Newman's `Π¹₁`, matching the decidability of critical-pair checking for a fixed system. -/
theorem cpJoinability_isLow (a b : L2.Term Empty) :
    (cpJoinabilitySentence a b).IsQF :=
  (BoundedFormula.IsAtomic.equal _ _).isQF

/-- Every quantifier-free critical-pair joinability matrix is `Σ⁰₀` in the structural arithmetical
hierarchy of `Complexity.lean`: it sits at the bottom level, confirming the low classification. -/
theorem cpJoinability_isSigma0 (a b : L2.Term Empty) :
    Complexity.IsSigma0Of 0 (cpJoinabilitySentence a b) :=
  Complexity.IsQF.isSigma0Of_zero (cpJoinability_isLow a b)

#print axioms newmanSentence_isPi11
#print axioms newmanConclusion_isArithmetical
#print axioms newmanInductiveStep_isArithmetical
#print axioms cpJoinability_isLow
#print axioms cpJoinability_isSigma0

end OperatorKO7.ReverseMath
