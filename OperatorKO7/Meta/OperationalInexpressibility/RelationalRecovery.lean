import OperatorKO7.Meta.OperationalInexpressibility.ObserverTargetCore

/-!
# Set-valued recovery through an observer

A proof task can admit more than one certificate at a state. The observer succeeds
when one certificate is admissible for every state in each observer fiber. This
strictly generalizes function-valued target recovery.

Relation: equality on observer fibers.
Property: existence of common admissible certificates and language-restricted recovery.
Trust: kernel-only; the quotient-decoder construction uses classical choice.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.RelationalRecovery

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary

universe u v w

/-- Every realized observer fiber admits one certificate valid for the whole fiber. -/
def FiberCommonWitness {X : Type u} {Q : Type v} {W : Type w}
    (q : X → Q) (admissible : X → W → Prop) : Prop :=
  ∀ x, ∃ witness, ∀ y, q y = q x → admissible y witness

/-- A decoder on the observer quotient returns a certificate admissible for each source state. -/
def QuotientRelationalRecovery {X : Type u} {Q : Type v} {W : Type w}
    (q : X → Q) (admissible : X → W → Prop) : Prop :=
  ∃ decode : ObserverQuotient q → W,
    ∀ x, admissible x (decode (quotientMap q x))

/-- Quotient recovery exists exactly when every realized observer fiber has a common witness. -/
theorem quotientRelationalRecovery_iff_fiberCommonWitness
    {X : Type u} {Q : Type v} {W : Type w}
    (q : X → Q) (admissible : X → W → Prop) :
    QuotientRelationalRecovery q admissible ↔ FiberCommonWitness q admissible := by
  classical
  constructor
  · rintro ⟨decode, hdecode⟩ x
    refine ⟨decode (quotientMap q x), ?_⟩
    intro y hy
    have hquot : quotientMap q y = quotientMap q x :=
      (quotientMap_eq_iff q y x).2 hy
    simpa [hquot] using hdecode y
  · intro hcommon
    have hclass : ∀ c : ObserverQuotient q,
        ∃ witness, ∀ x, quotientMap q x = c → admissible x witness := by
      intro c
      refine Quotient.inductionOn c ?_
      intro x
      obtain ⟨witness, hwitness⟩ := hcommon x
      refine ⟨witness, ?_⟩
      intro y hy
      have hqy : q y = q x := (quotientMap_eq_iff q y x).1 hy
      exact hwitness y hqy
    let decode : ObserverQuotient q → W := fun c => Classical.choose (hclass c)
    refine ⟨decode, ?_⟩
    intro x
    exact Classical.choose_spec (hclass (quotientMap q x)) x rfl

/-- Two states in one observer fiber conflict when they have no common admissible certificate. -/
def PairConflictAt {X : Type u} {Q : Type v} {W : Type w}
    (q : X → Q) (admissible : X → W → Prop) (x y : X) : Prop :=
  q x = q y ∧ ∀ witness, ¬ (admissible x witness ∧ admissible y witness)

/-- A conflicting pair refutes quotient recovery constructively. -/
theorem pairConflictAt_refutes_quotientRelationalRecovery
    {X : Type u} {Q : Type v} {W : Type w}
    {q : X → Q} {admissible : X → W → Prop} {x y : X}
    (hconflict : PairConflictAt q admissible x y) :
    ¬ QuotientRelationalRecovery q admissible := by
  rintro ⟨decode, hdecode⟩
  have hquot : quotientMap q x = quotientMap q y :=
    (quotientMap_eq_iff q x y).2 hconflict.1
  have hx := hdecode x
  have hy := hdecode y
  exact hconflict.2 (decode (quotientMap q x))
    ⟨hx, by simpa [hquot] using hy⟩

/-- Pairwise compatibility checks only two states at a time. -/
def PairwiseFiberCompatible {X : Type u} {Q : Type v} {W : Type w}
    (q : X → Q) (admissible : X → W → Prop) : Prop :=
  ∀ x y, q x = q y → ∃ witness, admissible x witness ∧ admissible y witness

/-- A common witness on every fiber implies pairwise compatibility. -/
theorem fiberCommonWitness_implies_pairwiseFiberCompatible
    {X : Type u} {Q : Type v} {W : Type w}
    {q : X → Q} {admissible : X → W → Prop}
    (hcommon : FiberCommonWitness q admissible) :
    PairwiseFiberCompatible q admissible := by
  intro x y hxy
  obtain ⟨witness, hwitness⟩ := hcommon x
  exact ⟨witness, hwitness x rfl, hwitness y hxy.symm⟩

/-- Singleton admissibility embeds the function-valued target problem into relational recovery. -/
def SingletonAdmissible {X : Type u} {W : Type w}
    (target : X → W) (x : X) (witness : W) : Prop :=
  witness = target x

/-- The relational theorem reduces to ordinary quotient factorization for singleton targets. -/
theorem singleton_relationalRecovery_iff_quotientFactorization
    {X : Type u} {Q : Type v} {W : Type w}
    (q : X → Q) (target : X → W) :
    QuotientRelationalRecovery q (SingletonAdmissible target) ↔
      QuotientFactorization q target := by
  rfl

/-- Information-level recovery by a total decoder on the observation alphabet. -/
def DirectRelationalRecovery {X : Type u} {Q : Type v} {W : Type w}
    (q : X → Q) (admissible : X → W → Prop) : Prop :=
  ∃ decode : Q → W, ∀ x, admissible x (decode (q x))

/-- Recovery through a declared decoder language. -/
def LanguageRelationalRecovery {X : Type u} {Q : Type v} {W : Type w}
    (q : X → Q) (admissible : X → W → Prop)
    (language : (Q → W) → Prop) : Prop :=
  ∃ decode : Q → W, language decode ∧ ∀ x, admissible x (decode (q x))

/-- A language-restricted decoder is also an information-level decoder. -/
theorem languageRelationalRecovery_implies_direct
    {X : Type u} {Q : Type v} {W : Type w}
    {q : X → Q} {admissible : X → W → Prop}
    {language : (Q → W) → Prop}
    (h : LanguageRelationalRecovery q admissible language) :
    DirectRelationalRecovery q admissible := by
  rcases h with ⟨decode, _, hdecode⟩
  exact ⟨decode, hdecode⟩

/-! ## Controls separating pairwise, global, and language restrictions -/

/-- Three states share one observation. A witness is admissible at a state exactly when it is a
 different index. Every pair has a common witness, while all three together do not. -/
def threeWayAdmissible (x witness : Fin 3) : Prop := witness ≠ x

/-- All three states have the same observation. -/
def threeWayObserver (_ : Fin 3) : Unit := ()

/-- A computable witness distinct from both endpoints of a pair in `Fin 3`. -/
def thirdWitness (x y : Fin 3) : Fin 3 :=
  if x ≠ 0 ∧ y ≠ 0 then 0
  else if x ≠ 1 ∧ y ≠ 1 then 1
  else 2

/-- The computed third witness differs from the first endpoint. -/
theorem thirdWitness_ne_left (x y : Fin 3) : thirdWitness x y ≠ x := by
  fin_cases x <;> fin_cases y <;> simp [thirdWitness]

/-- The computed third witness differs from the second endpoint. -/
theorem thirdWitness_ne_right (x y : Fin 3) : thirdWitness x y ≠ y := by
  fin_cases x <;> fin_cases y <;> simp [thirdWitness]

/-- Pairwise compatibility holds on the three-state fixture. -/
theorem threeWay_pairwiseFiberCompatible :
    PairwiseFiberCompatible threeWayObserver threeWayAdmissible := by
  intro x y _
  exact ⟨thirdWitness x y,
    thirdWitness_ne_left x y,
    thirdWitness_ne_right x y⟩

/-- The three-state fixture has no common witness for its single observer fiber. -/
theorem threeWay_not_fiberCommonWitness :
    ¬ FiberCommonWitness threeWayObserver threeWayAdmissible := by
  intro hcommon
  obtain ⟨witness, hwitness⟩ := hcommon 0
  have hself : threeWayAdmissible witness witness := hwitness witness rfl
  exact hself rfl

/-- Pairwise compatibility is insufficient for set-valued recovery. -/
theorem pairwiseFiberCompatible_not_sufficient :
    PairwiseFiberCompatible threeWayObserver threeWayAdmissible ∧
      ¬ QuotientRelationalRecovery threeWayObserver threeWayAdmissible := by
  refine ⟨threeWay_pairwiseFiberCompatible, ?_⟩
  rw [quotientRelationalRecovery_iff_fiberCommonWitness]
  exact threeWay_not_fiberCommonWitness

/-- Identity observation with identity certificates has complete information. -/
def boolIdentityAdmissible (x witness : Bool) : Prop := witness = x

/-- The identity decoder recovers the admissible certificate. -/
theorem boolIdentity_directRelationalRecovery :
    DirectRelationalRecovery (fun x : Bool => x) boolIdentityAdmissible := by
  exact ⟨id, by intro x; rfl⟩

/-- A decoder language containing only the constant-false decoder. -/
def FalseOnlyLanguage (decode : Bool → Bool) : Prop := ∀ q, decode q = false

/-- The information is present, but the constant-false decoder language cannot recover it. -/
theorem boolIdentity_falseOnlyLanguage_fails :
    ¬ LanguageRelationalRecovery (fun x : Bool => x) boolIdentityAdmissible FalseOnlyLanguage := by
  rintro ⟨decode, hlanguage, hdecode⟩
  have htrue : decode true = true := hdecode true
  have hfalse : decode true = false := hlanguage true
  rw [hfalse] at htrue
  cases htrue

end OperatorKO7.Meta.OperationalInexpressibility.RelationalRecovery
