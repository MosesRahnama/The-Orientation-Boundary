import OperatorKO7.Meta.OperationalInexpressibility.ObserverTargetCore

/-!
# Observer-target license core

The license is kernel inclusion: every equality created by the observer must preserve the target.
The results here quantify over arbitrary types and carry no recursor or concrete rewrite-system import.

Relation: observer-kernel refinement.
Property: target licensing, collision, refinement, and one-way loss under coarsening.
Trust: kernel-only; classical reasoning is localized to the fixed-codomain converse.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

universe u v w u'

/-- The license criterion: the observer's kernel is contained in the target's kernel. -/
def Licensed {X : Type u} {Q : Type v} {V : Type w} (q : X → Q) (P : X → V) : Prop :=
  ∀ x y : X, q x = q y → P x = P y

/-- The criterion is observer-fiber constancy. -/
theorem licensed_iff_factorsThrough {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) : Licensed q P ↔ FactorsThrough q P := by
  constructor
  · intro h x y hxy
    exact h x y hxy
  · intro h x y hxy
    exact h hxy

/-- The criterion is factorization through the actual observer quotient. -/
theorem licensed_iff_quotientFactorization {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) : Licensed q P ↔ QuotientFactorization q P := by
  rw [licensed_iff_factorsThrough, quotientFactorization_iff_factorsThrough]

/-- **Failure of the license is an operational-inexpressibility collision.** -/
theorem unlicensed_iff_collision {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) :
    ¬ Licensed q P ↔ ∃ w1 w2, OperationallyInexpressibleAt q P w1 w2 := by
  rw [licensed_iff_factorsThrough]
  exact not_factorsThrough_iff_exists_collision q P

/-- Observer refinement: `qFine` is at least as informative as `qCoarse` when every
fiber of `qFine` is contained in a fiber of `qCoarse`. Equivalently, the coarse observer
factors through the fine observer's kernel. -/
def ObserverRefines {X : Type u} {QFine : Type v} {QCoarse : Type u'}
    (qFine : X → QFine) (qCoarse : X → QCoarse) : Prop :=
  FactorsThrough qFine qCoarse

/-- **License-theory representation theorem.** An observer refines another exactly when
it licenses every target, in the coarse observer's universe, that the coarser observer
licenses. The reverse implication needs no cardinality, finiteness, surjectivity, or
inhabitance hypothesis: choose the coarse observer itself as the target. -/
theorem observerRefines_iff_licenseTheory_inclusion
    {X : Type u} {QFine : Type v} {QCoarse : Type u'}
    (qFine : X → QFine) (qCoarse : X → QCoarse) :
    ObserverRefines qFine qCoarse ↔
      ∀ {V : Type u'} (P : X → V), Licensed qCoarse P → Licensed qFine P := by
  constructor
  · intro href V P hlic x y hxy
    exact hlic x y (href hxy)
  · intro hall
    have hself : Licensed qCoarse qCoarse := by
      intro x y hxy
      exact hxy
    have hlicensed : Licensed qFine qCoarse := hall qCoarse hself
    show FactorsThrough qFine qCoarse
    exact (licensed_iff_factorsThrough qFine qCoarse).1 hlicensed

/-- Observer refinement is reflexive. -/
theorem ObserverRefines.refl
    {X : Type u} {Q : Type v} (q : X → Q) : ObserverRefines q q := by
  intro x y hxy
  exact hxy

/-- Observer refinement is transitive. -/
theorem ObserverRefines.trans
    {X : Type u} {Q₁ : Type v} {Q₂ : Type u'} {Q₃ : Type w}
    {q₁ : X → Q₁} {q₂ : X → Q₂} {q₃ : X → Q₃}
    (h12 : ObserverRefines q₁ q₂) (h23 : ObserverRefines q₂ q₃) :
    ObserverRefines q₁ q₃ := by
  intro x y hxy
  exact h23 (h12 hxy)

/-- A target licensed by a coarser observer remains licensed after observer refinement. -/
theorem Licensed.of_refinement
    {X : Type u} {QFine : Type v} {QCoarse : Type u'} {V : Type w}
    {qFine : X → QFine} {qCoarse : X → QCoarse} {P : X → V}
    (href : ObserverRefines qFine qCoarse) (hlic : Licensed qCoarse P) :
    Licensed qFine P := by
  intro x y hxy
  exact hlic x y (href hxy)

/-- Contrapositive monotonicity: if a finer observer cannot license a target, no coarser
observer can license it either. -/
theorem not_licensed_coarse_of_not_licensed_fine
    {X : Type u} {QFine : Type v} {QCoarse : Type u'} {V : Type w}
    {qFine : X → QFine} {qCoarse : X → QCoarse} {P : X → V}
    (href : ObserverRefines qFine qCoarse) (hbad : ¬ Licensed qFine P) :
    ¬ Licensed qCoarse P := by
  intro hcoarse
  exact hbad (hcoarse.of_refinement href)

/-- An observer licenses the identity target exactly when it is injective. This is the
sharp endpoint of the license-theory order: injective observation preserves every source
state distinction. -/
theorem licensed_identity_iff_injective
    {X : Type u} {Q : Type v} (q : X → Q) :
    Licensed q (fun x : X => x) ↔ Function.Injective q := by
  constructor
  · intro h x y hxy
    exact h x y hxy
  · intro h x y hxy
    exact h hxy

/-- Every target is licensed by an injective observer. -/
theorem licensed_of_injective
    {X : Type u} {Q : Type v} {V : Type w} {q : X → Q} (hq : Function.Injective q)
    (P : X → V) : Licensed q P := by
  intro x y hxy
  rw [hq hxy]

/-- Mutual refinement is exactly equality of observer kernels. -/
theorem mutual_refinement_iff_same_kernel
    {X : Type u} {Q₁ : Type v} {Q₂ : Type u'} (q₁ : X → Q₁) (q₂ : X → Q₂) :
    (ObserverRefines q₁ q₂ ∧ ObserverRefines q₂ q₁) ↔
      ∀ x y, q₁ x = q₁ y ↔ q₂ x = q₂ y := by
  constructor
  · rintro ⟨h12, h21⟩ x y
    exact ⟨fun h => h12 h, fun h => h21 h⟩
  · intro h
    exact ⟨fun hxy => (h _ _).1 hxy, fun hxy => (h _ _).2 hxy⟩

/-- **The license is lost at most once along a coarsening.** If the coarser observer
`h ∘ q'` is licensed then so is the finer observer `q'`. -/
theorem license_of_coarser {X : Type u} {Q : Type v} {Q' : Type u'} {V : Type w}
    (h : Q' → Q) (q' : X → Q') (P : X → V)
    (hlic : Licensed (fun x => h (q' x)) P) : Licensed q' P := by
  intro x y hxy
  exact hlic x y (by simp [hxy])

/-- Along a chain `qs (n+1) = hs n ∘ qs n`, a license at stage `m` holds at every earlier
stage. -/
theorem license_chain_lost_once {X : Type u} {Q : Type v} {V : Type w}
    (qs : Nat → X → Q) (hs : Nat → Q → Q)
    (hchain : ∀ n x, qs (n + 1) x = hs n (qs n x)) (P : X → V) :
    ∀ m, Licensed (qs m) P → ∀ n, n ≤ m → Licensed (qs n) P := by
  intro m hm n hnm
  induction m with
  | zero =>
      have h0 : n = 0 := by omega
      subst h0
      exact hm
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · have hprev : Licensed (qs m) P := by
          have hcoarse : Licensed (fun x => hs m (qs m x)) P := by
            intro x y hxy
            exact hm x y (by rw [hchain m x, hchain m y]; exact hxy)
          exact license_of_coarser (hs m) (qs m) P hcoarse
        exact ih hprev (by omega)
      · have h0 : n = m + 1 := by omega
        subst h0
        exact hm


/-! ## A fixed target codomain -/

/-- License-theory inclusion is codomain triviality or observer refinement. -/
theorem fixedTarget_licenseTheory_inclusion_iff
    {X : Type u} {QFine : Type v} {QCoarse : Type u'}
    (V : Type w) (qFine : X → QFine) (qCoarse : X → QCoarse) :
    (∀ P : X → V, Licensed qCoarse P → Licensed qFine P) ↔
      Subsingleton V ∨ ObserverRefines qFine qCoarse := by
  classical
  constructor
  · intro hall
    by_cases hV : Subsingleton V
    · exact Or.inl hV
    · right
      have hpair : ∃ a b : V, a ≠ b := by
        by_contra h
        apply hV
        constructor
        intro a b
        by_contra hab
        exact h ⟨a, b, hab⟩
      obtain ⟨a, b, hab⟩ := hpair
      intro x y hxy
      by_contra hne
      let P : X → V := fun z => if qCoarse z = qCoarse x then a else b
      have hlic : Licensed qCoarse P := by
        intro z t hzt
        dsimp [P]
        rw [hzt]
      have hvalues := hall P hlic x y hxy
      have heq : a = b := by simpa [P, Ne.symm hne] using hvalues
      exact hab heq
  · rintro (hV | href) P hP
    · intro x y _
      exact hV.elim (P x) (P y)
    · exact hP.of_refinement href

/-- Boolean targets suffice, independently of the source and observer universes. -/
theorem observerRefines_iff_binary_licenseTheory
    {X : Type u} {QFine : Type v} {QCoarse : Type u'}
    (qFine : X → QFine) (qCoarse : X → QCoarse) :
    ObserverRefines qFine qCoarse ↔
      ∀ P : X → Bool, Licensed qCoarse P → Licensed qFine P := by
  constructor
  · intro href P hP
    exact hP.of_refinement href
  · intro hall
    rcases (fixedTarget_licenseTheory_inclusion_iff Bool qFine qCoarse).mp hall with
      hsub | href
    · have hbad : (false : Bool) = true := hsub.elim false true
      cases hbad
    · exact href

/-- Equality of Boolean license theories determines the observer kernel. -/
theorem same_binary_licenseTheory_iff_same_kernel
    {X : Type u} {Q₁ : Type v} {Q₂ : Type u'}
    (q₁ : X → Q₁) (q₂ : X → Q₂) :
    (∀ P : X → Bool, Licensed q₁ P ↔ Licensed q₂ P) ↔
      ∀ x y, q₁ x = q₁ y ↔ q₂ x = q₂ y := by
  rw [← mutual_refinement_iff_same_kernel]
  constructor
  · intro hall
    constructor
    · apply (observerRefines_iff_binary_licenseTheory q₁ q₂).mpr
      intro P hP
      exact (hall P).mpr hP
    · apply (observerRefines_iff_binary_licenseTheory q₂ q₁).mpr
      intro P hP
      exact (hall P).mp hP
  · rintro ⟨h12, h21⟩ P
    exact ⟨fun h => h.of_refinement h21, fun h => h.of_refinement h12⟩

/-- A one-value codomain does not detect a lost distinction. -/
theorem singleton_targets_do_not_detect_refinement :
    (∀ P : Bool → Unit, Licensed (fun _ : Bool => ()) P) ∧
      ¬ ObserverRefines (fun _ : Bool => ()) (id : Bool → Bool) := by
  constructor
  · intro P x y _
    exact Subsingleton.elim _ _
  · intro h
    have hbad : (false : Bool) = true := @h false true rfl
    cases hbad


/-! ## Exact loss time for stage-dependent observations -/

/-- Refinement composes across a sequence whose observation types may vary. -/
theorem coarsening_refines_of_le
    {X : Type u} {Q : Nat → Type v} (qs : (n : Nat) → X → Q n)
    (hcoarse : ∀ n, ObserverRefines (qs n) (qs (n + 1))) :
    ∀ n m, n ≤ m → ObserverRefines (qs n) (qs m) := by
  intro n m hnm
  induction hnm with
  | refl => exact ObserverRefines.refl _
  | @step m _ ih => exact ih.trans (hcoarse m)

theorem licensed_of_coarsening_later
    {X : Type u} {Q : Nat → Type v} {V : Type w}
    (qs : (n : Nat) → X → Q n)
    (hcoarse : ∀ n, ObserverRefines (qs n) (qs (n + 1))) (P : X → V)
    {n m : Nat} (hnm : n ≤ m) (hm : Licensed (qs m) P) :
    Licensed (qs n) P :=
  hm.of_refinement (coarsening_refines_of_le qs hcoarse n m hnm)

theorem unlicensed_of_coarsening_earlier
    {X : Type u} {Q : Nat → Type v} {V : Type w}
    (qs : (n : Nat) → X → Q n)
    (hcoarse : ∀ n, ObserverRefines (qs n) (qs (n + 1))) (P : X → V)
    {n m : Nat} (hnm : n ≤ m) (hn : ¬ Licensed (qs n) P) :
    ¬ Licensed (qs m) P :=
  fun hm => hn (licensed_of_coarsening_later qs hcoarse P hnm hm)

/-- Any failure has a first stage, and that stage determines all license statuses. -/
theorem first_license_loss_exists
    {X : Type u} {Q : Nat → Type v} {V : Type w}
    (qs : (n : Nat) → X → Q n)
    (hcoarse : ∀ n, ObserverRefines (qs n) (qs (n + 1))) (P : X → V)
    (hbad : ∃ n, ¬ Licensed (qs n) P) :
    ∃ n, ∀ m, Licensed (qs m) P ↔ m < n := by
  classical
  let n := Nat.find hbad
  have hn : ¬ Licensed (qs n) P := Nat.find_spec hbad
  refine ⟨n, ?_⟩
  intro m
  constructor
  · intro hm
    by_contra hlt
    exact hn (licensed_of_coarsening_later qs hcoarse P (by omega) hm)
  · intro hmn
    by_contra hm
    exact Nat.find_min hbad hmn hm

/-- Two exact loss cutoffs coincide, independently of the observer sequence. -/
theorem first_license_loss_unique
    {X : Type u} {Q : Nat → Type v} {V : Type w}
    (qs : (n : Nat) → X → Q n) (P : X → V)
    {n m : Nat}
    (hn : ∀ k, Licensed (qs k) P ↔ k < n)
    (hm : ∀ k, Licensed (qs k) P ↔ k < m) : n = m := by
  by_contra hne
  by_cases hlt : n < m
  · exact Nat.lt_irrefl n ((hn n).mp ((hm n).mpr hlt))
  · have hgt : m < n := by omega
    exact Nat.lt_irrefl m ((hm m).mp ((hn m).mpr hgt))

/-- One actual pair distinguishes every earlier stage from every later stage. -/
theorem license_cutoff_witness
    {X : Type u} {Q : Nat → Type v} {V : Type w}
    (qs : (n : Nat) → X → Q n)
    (hcoarse : ∀ n, ObserverRefines (qs n) (qs (n + 1))) (P : X → V)
    {n : Nat} (hcut : ∀ m, Licensed (qs m) P ↔ m < n) :
    ∃ x y, P x ≠ P y ∧
      (∀ m, m < n → qs m x ≠ qs m y) ∧
      (∀ m, n ≤ m → qs m x = qs m y) := by
  classical
  have hbad : ¬ Licensed (qs n) P :=
    fun h => Nat.lt_irrefl n ((hcut n).mp h)
  obtain ⟨x, y, hxy⟩ := (unlicensed_iff_collision (qs n) P).mp hbad
  refine ⟨x, y, hxy.2, ?_, ?_⟩
  · intro m hmn heq
    exact hxy.2 ((hcut m).mpr hmn x y heq)
  · intro m hnm
    exact coarsening_refines_of_le qs hcoarse n m hnm hxy.1

/-- Every coarsening either preserves the license forever or has one exact loss
time with a fixed pair of inputs witnessing the loss at all subsequent stages. -/
theorem license_coarsening_dichotomy
    {X : Type u} {Q : Nat → Type v} {V : Type w}
    (qs : (n : Nat) → X → Q n)
    (hcoarse : ∀ n, ObserverRefines (qs n) (qs (n + 1))) (P : X → V) :
    (∀ n, Licensed (qs n) P) ∨
      ∃ n, (∀ m, Licensed (qs m) P ↔ m < n) ∧
        ∃ x y, P x ≠ P y ∧
          (∀ m, m < n → qs m x ≠ qs m y) ∧
          (∀ m, n ≤ m → qs m x = qs m y) := by
  classical
  by_cases hall : ∀ n, Licensed (qs n) P
  · exact Or.inl hall
  · right
    have hbad : ∃ n, ¬ Licensed (qs n) P := by
      by_contra hnone
      apply hall
      intro n
      by_contra hn
      exact hnone ⟨n, hn⟩
    obtain ⟨n, hcut⟩ := first_license_loss_exists qs hcoarse P hbad
    exact ⟨n, hcut, license_cutoff_witness qs hcoarse P hcut⟩


end OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
