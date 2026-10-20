import OperatorKO7.Meta.OperationalInexpressibility.ObserverTargetCore
import Mathlib.Data.Nat.Log

/-!
# Finite observer-target fiber capacity

For a finite source, this module computes the largest number of target values inside one observer
fiber and proves the minimum finite side-alphabet and fixed-width binary capacity needed for zero-error recovery.
It has no concrete rewrite-system, recursor, or Fork3 dependency.

Relation: equality on observer fibers.
Property: zero-error finite recovery and minimum side-channel capacity.
Trust: kernel-only with classical choice used by the optimal code construction.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit

open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

universe u v w u' v'

section Definitions

variable {X : Type u} {Q : Type v} {V : Type w} [Fintype X] [DecidableEq Q] [DecidableEq V]

/-- The target values realized inside the observer fiber over `u`. -/
def fiberVerdicts (q : X → Q) (P : X → V) (u : Q) : Finset V :=
  (Finset.univ.filter (fun x => q x = u)).image P

/-- The largest number of distinct target values inside one observer fiber. -/
def fiberMultiplicity (q : X → Q) (P : X → V) : Nat :=
  (Finset.univ.image q).sup (fun u => (fiberVerdicts q P u).card)

/-- The integer zero-error fiber code deficit in bits: `⌈log₂ m⌉`. This is a
fixed-length code-capacity quantity, not Shannon entropy. The historical name `fiberDeficit`
is retained because it is already used by the surrounding bridge API. -/
def fiberDeficit (q : X → Q) (P : X → V) : Nat :=
  Nat.clog 2 (fiberMultiplicity q P)

/-- Precise alias exposing the coding convention carried by `fiberDeficit`. -/
abbrev fiberCodeDeficit (q : X → Q) (P : X → V) : Nat := fiberDeficit q P

theorem mem_fiberVerdicts {q : X → Q} {P : X → V} {u : Q} {v : V} :
    v ∈ fiberVerdicts q P u ↔ ∃ x, q x = u ∧ P x = v := by
  unfold fiberVerdicts
  simp [Finset.mem_image, Finset.mem_filter]

theorem fiberVerdicts_card_le_of_mem {q : X → Q} {P : X → V} {u : Q}
    (hu : u ∈ Finset.univ.image q) :
    (fiberVerdicts q P u).card ≤ fiberMultiplicity q P :=
  Finset.le_sup (f := fun u => (fiberVerdicts q P u).card) hu

/-- Every fiber has at most one verdict iff the target factors through the observer. -/
theorem fiberVerdicts_card_le_one_iff (q : X → Q) (P : X → V) :
    (∀ u, (fiberVerdicts q P u).card ≤ 1) ↔ FactorsThrough q P := by
  constructor
  · intro h x y hxy
    have hx : P x ∈ fiberVerdicts q P (q x) := mem_fiberVerdicts.2 ⟨x, rfl, rfl⟩
    have hy : P y ∈ fiberVerdicts q P (q x) := mem_fiberVerdicts.2 ⟨y, hxy.symm, rfl⟩
    exact Finset.card_le_one.1 (h (q x)) _ hx _ hy
  · intro h u
    apply Finset.card_le_one.2
    intro a ha b hb
    obtain ⟨x, hxu, rfl⟩ := mem_fiberVerdicts.1 ha
    obtain ⟨y, hyu, rfl⟩ := mem_fiberVerdicts.1 hb
    exact h (hxu.trans hyu.symm)

/-- The fiber multiplicity is at most one iff the target factors through the observer. -/
theorem fiberMultiplicity_le_one_iff (q : X → Q) (P : X → V) :
    fiberMultiplicity q P ≤ 1 ↔ FactorsThrough q P := by
  rw [← fiberVerdicts_card_le_one_iff]
  unfold fiberMultiplicity
  rw [Finset.sup_le_iff]
  constructor
  · intro h u
    by_cases hu : u ∈ Finset.univ.image q
    · exact h u hu
    · apply Finset.card_le_one.2
      intro a ha _ _
      obtain ⟨x, hxu, _⟩ := mem_fiberVerdicts.1 ha
      exact absurd (Finset.mem_image.2 ⟨x, Finset.mem_univ x, hxu⟩) hu
  · intro h u _
    exact h u

/-- **Zero deficit is factorization.** -/
theorem fiberDeficit_eq_zero_iff_factorsThrough (q : X → Q) (P : X → V) :
    fiberDeficit q P = 0 ↔ FactorsThrough q P := by
  rw [← fiberMultiplicity_le_one_iff]
  unfold fiberDeficit
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have := Nat.clog_pos (b := 2) (n := fiberMultiplicity q P) (by norm_num) hlt
    omega
  · intro h
    exact Nat.clog_of_right_le_one h 2

/-- **Positive deficit is an operational-inexpressibility collision.** -/
theorem fiberDeficit_pos_iff_collision (q : X → Q) (P : X → V) :
    0 < fiberDeficit q P ↔ ∃ w1 w2, OperationallyInexpressibleAt q P w1 w2 := by
  rw [← not_factorsThrough_iff_exists_collision, ← fiberDeficit_eq_zero_iff_factorsThrough]
  omega

/-- **Additional-channel lower bound.** If the joint observer `(q, r)` makes the target
readable, the added channel has at least `m(q, P)` values. -/
theorem additional_channel_card_lower_bound {R : Type u'} [Fintype R]
    (q : X → Q) (P : X → V) (r : X → R)
    (h : FactorsThrough (fun x => (q x, r x)) P) :
    fiberMultiplicity q P ≤ Fintype.card R := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · unfold fiberMultiplicity
    apply Finset.sup_le
    intro u hu
    exact absurd hu (by simp)
  · obtain ⟨x0⟩ := hX
    unfold fiberMultiplicity
    apply Finset.sup_le
    intro u _
    have hcard : (fiberVerdicts q P u).card ≤ (Finset.univ : Finset R).card := by
      apply Finset.card_le_card_of_injOn
        (fun v => if hv : ∃ x, q x = u ∧ P x = v then r (Classical.choose hv) else r x0)
      · intro v _
        exact Finset.mem_univ _
      · intro v1 hv1 v2 hv2 heq
        have hv1' : ∃ x, q x = u ∧ P x = v1 := mem_fiberVerdicts.1 hv1
        have hv2' : ∃ x, q x = u ∧ P x = v2 := mem_fiberVerdicts.1 hv2
        simp only [dif_pos hv1', dif_pos hv2'] at heq
        obtain ⟨h1u, h1v⟩ := Classical.choose_spec hv1'
        obtain ⟨h2u, h2v⟩ := Classical.choose_spec hv2'
        have hpair : (fun x => (q x, r x)) (Classical.choose hv1') =
            (fun x => (q x, r x)) (Classical.choose hv2') := by
          simp only [Prod.mk.injEq]
          exact ⟨h1u.trans h2u.symm, heq⟩
        have := h hpair
        rw [h1v, h2v] at this
        exact this
    simpa using hcard

/-- The deficit lower bound in bits: an added channel with `card R` values carries at least
`δ(q, P)` bits of ceiling-log capacity. -/
theorem additional_channel_bits_lower_bound {R : Type u'} [Fintype R]
    (q : X → Q) (P : X → V) (r : X → R)
    (h : FactorsThrough (fun x => (q x, r x)) P) :
    fiberDeficit q P ≤ Nat.clog 2 (Fintype.card R) :=
  Nat.clog_mono_right 2 (additional_channel_card_lower_bound q P r h)

/-- Every observer fiber has target multiplicity bounded by the global maximum, including
unrealized observer values whose fiber is empty. -/
theorem fiberVerdicts_card_le (q : X → Q) (P : X → V) (u : Q) :
    (fiberVerdicts q P u).card ≤ fiberMultiplicity q P := by
  by_cases hu : u ∈ Finset.univ.image q
  · exact fiberVerdicts_card_le_of_mem hu
  · have hempty : fiberVerdicts q P u = ∅ := by
      ext v
      simp only [Finset.notMem_empty, iff_false]
      intro hv
      obtain ⟨x, hxu, _⟩ := mem_fiberVerdicts.1 hv
      exact hu (Finset.mem_image.2 ⟨x, Finset.mem_univ x, hxu⟩)
    simp [hempty]

/-- A classical injective local code from the target values realized in one observer fiber
into the globally minimal alphabet `Fin (fiberMultiplicity q P)`. -/
noncomputable def fiberCodeEmbedding (q : X → Q) (P : X → V) (u : Q) :
    {v // v ∈ fiberVerdicts q P u} ↪ Fin (fiberMultiplicity q P) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_coe, Fintype.card_fin]
    exact fiberVerdicts_card_le q P u))

/-- Totalized local fiber code. The default branch is never used on an actual world; the
positivity hypothesis supplies a value only for target values outside the selected fiber. -/
noncomputable def fiberCode (q : X → Q) (P : X → V)
    (hM : 0 < fiberMultiplicity q P) (u : Q) (v : V) : Fin (fiberMultiplicity q P) :=
  if hv : v ∈ fiberVerdicts q P u then
    fiberCodeEmbedding q P u ⟨v, hv⟩
  else ⟨0, hM⟩

/-- The local code is injective on every realized target fiber. -/
theorem fiberCode_injective_on_fiber (q : X → Q) (P : X → V)
    (hM : 0 < fiberMultiplicity q P) (u : Q) {v₁ v₂ : V}
    (hv₁ : v₁ ∈ fiberVerdicts q P u) (hv₂ : v₂ ∈ fiberVerdicts q P u)
    (hc : fiberCode q P hM u v₁ = fiberCode q P hM u v₂) : v₁ = v₂ := by
  classical
  simp only [fiberCode, dif_pos hv₁, dif_pos hv₂] at hc
  have hsub := (fiberCodeEmbedding q P u).injective hc
  exact congrArg Subtype.val hsub

/-- **Tight additional-channel theorem.** For every finite observer/target pair there exists
an added channel whose alphabet has exactly `m(q,P)` values and whose joint observation with
`q` determines `P`. The empty-world case is handled without a positivity assumption; every
inhabited world has `m(q,P) > 0` automatically. -/
theorem exists_optimal_side_channel (q : X → Q) (P : X → V) :
    ∃ r : X → Fin (fiberMultiplicity q P), FactorsThrough (fun x => (q x, r x)) P := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · let r : X → Fin (fiberMultiplicity q P) := fun x => isEmptyElim x
    exact ⟨r, by intro x; exact isEmptyElim x⟩
  · let x0 : X := Classical.choice hX
    have hv0 : P x0 ∈ fiberVerdicts q P (q x0) := mem_fiberVerdicts.2 ⟨x0, rfl, rfl⟩
    have hcardpos : 0 < (fiberVerdicts q P (q x0)).card := Finset.card_pos.mpr ⟨P x0, hv0⟩
    have hcardle := fiberVerdicts_card_le q P (q x0)
    have hM : 0 < fiberMultiplicity q P := lt_of_lt_of_le hcardpos hcardle
    let r : X → Fin (fiberMultiplicity q P) := fun x => fiberCode q P hM (q x) (P x)
    refine ⟨r, ?_⟩
    intro x y hxy
    have hq : q x = q y := congrArg Prod.fst hxy
    have hc : r x = r y := congrArg Prod.snd hxy
    have hvx : P x ∈ fiberVerdicts q P (q x) := mem_fiberVerdicts.2 ⟨x, rfl, rfl⟩
    have hvy : P y ∈ fiberVerdicts q P (q x) := mem_fiberVerdicts.2 ⟨y, hq.symm, rfl⟩
    apply fiberCode_injective_on_fiber q P hM (q x) hvx hvy
    dsimp [r] at hc ⊢
    simpa [hq] using hc

/-- **Exact optimality of fiber multiplicity.** The bound is achievable by a channel with
exactly `m(q,P)` symbols, and every finite channel that licenses the target has cardinality at
least `m(q,P)`. -/
theorem fiberMultiplicity_is_minimum_side_channel_cardinality (q : X → Q) (P : X → V) :
    (∃ r : X → Fin (fiberMultiplicity q P), FactorsThrough (fun x => (q x, r x)) P) ∧
      ∀ {R : Type u'} [Fintype R] (r : X → R),
        FactorsThrough (fun x => (q x, r x)) P → fiberMultiplicity q P ≤ Fintype.card R :=
  ⟨exists_optimal_side_channel q P, fun r h => additional_channel_card_lower_bound q P r h⟩

/-- A binary alphabet of exactly `2^δ` symbols is large enough for the optimal side
channel. Thus the ceiling-log deficit is not merely a lower bound: `δ(q,P)` fixed-length
binary bits suffice. -/
theorem exists_binary_side_channel_at_fiberCodeDeficit (q : X → Q) (P : X → V) :
    ∃ r : X → Fin (2 ^ fiberCodeDeficit q P),
      FactorsThrough (fun x => (q x, r x)) P := by
  classical
  obtain ⟨r, hr⟩ := exists_optimal_side_channel q P
  have hcap : fiberMultiplicity q P ≤ 2 ^ fiberCodeDeficit q P := by
    exact Nat.le_pow_clog (by omega : 1 < 2) (fiberMultiplicity q P)
  let rBinary : X → Fin (2 ^ fiberCodeDeficit q P) := fun x => Fin.castLE hcap (r x)
  refine ⟨rBinary, ?_⟩
  intro x y hxy
  have hq : q x = q y := congrArg Prod.fst hxy
  have hbin : rBinary x = rBinary y := congrArg Prod.snd hxy
  have hcode : r x = r y := by
    apply Fin.castLE_injective hcap
    simpa [rBinary] using hbin
  exact hr (Prod.ext hq hcode)

/-- **Exact optimality in fixed-length bits.** Exactly `δ(q,P)` binary bits suffice, and
no finite licensing channel has smaller ceiling-log capacity. -/
theorem fiberCodeDeficit_is_minimum_fixedLength_bits (q : X → Q) (P : X → V) :
    (∃ r : X → Fin (2 ^ fiberCodeDeficit q P),
        FactorsThrough (fun x => (q x, r x)) P) ∧
      ∀ {R : Type u'} [Fintype R] (r : X → R),
        FactorsThrough (fun x => (q x, r x)) P →
          fiberCodeDeficit q P ≤ Nat.clog 2 (Fintype.card R) :=
  ⟨exists_binary_side_channel_at_fiberCodeDeficit q P,
    fun r h => additional_channel_bits_lower_bound q P r h⟩

/-- **Kernel-refinement monotonicity.** Whenever every fiber of `qFine` is contained in a
fiber of `qCoarse`, the finer observer has no larger target multiplicity. No explicit map
between the two observation alphabets is required. -/
theorem fiberMultiplicity_le_of_kernel_refines {QFine : Type v'} [DecidableEq QFine]
    (qFine : X → QFine) (qCoarse : X → Q) (P : X → V)
    (href : FactorsThrough qFine qCoarse) :
    fiberMultiplicity qFine P ≤ fiberMultiplicity qCoarse P := by
  unfold fiberMultiplicity
  apply Finset.sup_le
  intro uFine huFine
  obtain ⟨x, _, hxu⟩ := Finset.mem_image.1 huFine
  have hmem : qCoarse x ∈ Finset.univ.image qCoarse :=
    Finset.mem_image.2 ⟨x, Finset.mem_univ x, rfl⟩
  refine le_trans ?_ (Finset.le_sup (f := fun u => (fiberVerdicts qCoarse P u).card) hmem)
  apply Finset.card_le_card
  intro v hv
  obtain ⟨y, hyu, hyv⟩ := mem_fiberVerdicts.1 hv
  have hqFine : qFine y = qFine x := hyu.trans hxu.symm
  exact mem_fiberVerdicts.2 ⟨y, href hqFine, hyv⟩

/-- Kernel refinement never raises the fixed-length code deficit. -/
theorem fiberDeficit_le_of_kernel_refines {QFine : Type v'} [DecidableEq QFine]
    (qFine : X → QFine) (qCoarse : X → Q) (P : X → V)
    (href : FactorsThrough qFine qCoarse) :
    fiberDeficit qFine P ≤ fiberDeficit qCoarse P :=
  Nat.clog_mono_right 2 (fiberMultiplicity_le_of_kernel_refines qFine qCoarse P href)

/-- **Explicit-composition refinement** is the concrete special case of kernel refinement. -/
theorem fiberMultiplicity_le_of_refines {Q' : Type v'} [DecidableEq Q']
    (h : Q' → Q) (q' : X → Q') (P : X → V) :
    fiberMultiplicity q' P ≤ fiberMultiplicity (fun x => h (q' x)) P := by
  apply fiberMultiplicity_le_of_kernel_refines q' (fun x => h (q' x)) P
  intro x y hxy
  exact congrArg h hxy

/-- Explicit-composition refinement never raises the deficit. -/
theorem fiberDeficit_le_of_refines {Q' : Type v'} [DecidableEq Q']
    (h : Q' → Q) (q' : X → Q') (P : X → V) :
    fiberDeficit q' P ≤ fiberDeficit (fun x => h (q' x)) P :=
  Nat.clog_mono_right 2 (fiberMultiplicity_le_of_refines h q' P)

end Definitions

end OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit
