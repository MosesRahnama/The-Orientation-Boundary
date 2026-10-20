import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax
import OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
import OperatorKO7.Meta.UniversalBoundary.HammingBoundCapacity
import OperatorKO7.Meta.OperationalInexpressibility.ObserverTargetCore
import OperatorKO7.Meta.OperationalInexpressibility.FiberDeficitCore
import OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Syndrome bound as a fiber-capacity instance

The syndrome form of the binary linear-code sphere-packing bound is established here as an
instance of the observer/fiber-capacity law. The syndrome is the cheap observer, the error
pattern is the verdict, and syndrome decoding licenses that verdict on a bounded Hamming ball.
The numerical bound is the classical syndrome bound (Hamming 1950; MacWilliams-Sloane 1977,
Chapter 1), formalized here rather than claimed as new.

Relation: equality on syndrome fibers, with Licensed and FactorsThrough.
Closure: not a rewriting closure.
Strategy: syndrome decoding on the radius-t error ball; H74 by column injectivity; Hbad as TypedBoundary.
Trust: kernel-only, with imported baseline axioms restricted to {propext, Classical.choice, Quot.sound}.
Scope: binary vectors over ZMod 2, parity-check matrices, radius-bounded errors, and the
       syndrome-capacity inequality.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniversalBoundary.SyndromeBoundCapacity

open OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit
open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.Confusability
open OperatorKO7.Meta.UniversalBoundary.HammingBoundCapacity

/-! ## NameGate -/

#check @TypedBoundary
#check @TypedBoundary.verdict_not_observation_function
#check @OperationallyInexpressibleAt
#check @FactorsThrough
#check @not_factorsThrough_of_collision
#check @fiberMultiplicity
#check @additional_channel_card_lower_bound
#check @fiberMultiplicity_const
#check @Licensed
#check @licensed_iff_factorsThrough
#check @augmentObserver
#check @hammingNorm
#check @Matrix.mulVec
#check @Fintype.card
#check @Fintype.card_fun
#check @Fintype.card_fin
#check @Fintype.card_coe
#check @ZMod.card
#check @ball
#check @Pi.single
#check @Matrix.mulVec_single_one
#check @Matrix.col
#check @Matrix.mulVec_zero

/-- Binary length-n error vectors over ZMod 2. -/
abbrev Vec (n : Nat) := Fin n → ZMod 2

/-- Radius-t error ball over binary vectors. L24 is imported for its Hamming-bound
infrastructure; this ZMod 2 ball is the coefficient-equivalent syndrome-side carrier. -/
def synBall (n t : Nat) : Finset (Vec n) :=
  Finset.univ.filter (fun e => hammingNorm e ≤ t)

/-- Syndrome of an error vector under a parity-check matrix. -/
def syndrome {n r : Nat} (H : Matrix (Fin r) (Fin n) (ZMod 2)) (e : Vec n) :
    Fin r → ZMod 2 :=
  H.mulVec e

/-- The state space is the radius-t error ball. -/
abbrev Err (n t : Nat) := {e : Vec n // e ∈ synBall n t}

/-- Syndrome observer on the bounded error state space. -/
def syn {n r t : Nat} (H : Matrix (Fin r) (Fin n) (ZMod 2)) :
    Err n t → (Fin r → ZMod 2) :=
  fun e => syndrome H e.1

/-- Error-vector verdict on the bounded error state space. -/
def err {n t : Nat} : Err n t → Vec n :=
  Subtype.val

/-- The syndrome licenses recovery of the error throughout the radius-t ball. -/
def CorrectsBySyndrome {n r : Nat} (H : Matrix (Fin r) (Fin n) (ZMod 2)) (t : Nat) : Prop :=
  Licensed (syn H (t := t)) err

/--
Proves: syndrome decoding licenses the error exactly when syndrome is injective on the radius-t ball.
Does not prove: existence of a decoder outside the radius-t ball.
Relation: Licensed on Err n t and Set.InjOn of syndrome H on synBall n t.
Closure: not a rewriting closure.
Strategy: subtype introduction/elimination identifies ball states with their underlying errors.
Trust: kernel-only.
Scope: every binary parity-check matrix H and radius t.
-/
theorem correctsBySyndrome_iff_injOn {n r : Nat}
    (H : Matrix (Fin r) (Fin n) (ZMod 2)) (t : Nat) :
    CorrectsBySyndrome H t ↔
      Set.InjOn (syndrome H) (synBall n t : Set (Vec n)) := by
  constructor
  · intro h x hx y hy hxy
    exact h ⟨x, hx⟩ ⟨y, hy⟩ hxy
  · intro h x y hxy
    exact h x.2 y.2 hxy

/--
Proves: a correcting syndrome, added to a constant base observer, licenses the full bounded-error state.
Does not prove: that the syndrome is injective on all vectors outside the ball.
Relation: Licensed (augmentObserver (fun _ => ()) (syn H)) id.
Closure: not a rewriting closure.
Strategy: project equality of the added syndrome component and use the correction license.
Trust: kernel-only.
Scope: every H and t satisfying CorrectsBySyndrome H t.
-/
theorem syn_licenses_state {n r t : Nat} {H : Matrix (Fin r) (Fin n) (ZMod 2)}
    (h : CorrectsBySyndrome H t) :
    Licensed (augmentObserver (fun _ : Err n t => ()) (syn H))
      (id : Err n t → Err n t) := by
  intro x y hxy
  apply Subtype.ext
  exact h x y (congrArg Prod.snd hxy)

/--
Proves: under a constant observer, the fiber multiplicity of the identity target is the number of ball states.
Does not prove: the syndrome bound.
Relation: fiberMultiplicity_const applied to id on Err n t.
Closure: not a rewriting closure.
Strategy: exhibit the zero vector in the ball and use injectivity of id.
Trust: kernel-only.
Scope: every length n and radius t.
-/
theorem fiberMultiplicity_const_id (n t : Nat) :
    fiberMultiplicity (fun _ : Err n t => ()) (id : Err n t → Err n t) =
      Fintype.card (Err n t) := by
  haveI : Nonempty (Err n t) := ⟨⟨0, by simp [synBall]⟩⟩
  rw [fiberMultiplicity_const () (id : Err n t → Err n t),
    Finset.card_image_of_injective _ Function.injective_id, Finset.card_univ]

/--
Proves: if H corrects every radius-t error by syndrome, then card (synBall n t) ≤ 2^r.
Does not prove: a new coding bound; this is the established syndrome sphere-packing bound.
Relation: additional_channel_card_lower_bound with constant base observer, identity target, and syndrome side channel.
Closure: not a rewriting closure.
Strategy: consume the framework capacity law, then compute the state and syndrome-alphabet cardinalities.
Trust: kernel-only; established coding criterion from Hamming 1950 and MacWilliams-Sloane 1977, Chapter 1.
Scope: binary linear-code error vectors under any r-by-n parity-check matrix.
-/
theorem syndrome_bound {n r : Nat} (H : Matrix (Fin r) (Fin n) (ZMod 2)) (t : Nat)
    (h : CorrectsBySyndrome H t) : (synBall n t).card ≤ 2 ^ r := by
  have hcap :
      fiberMultiplicity (fun _ : Err n t => ()) (id : Err n t → Err n t) ≤
        Fintype.card (Fin r → ZMod 2) :=
    additional_channel_card_lower_bound
      (q := fun _ : Err n t => ()) (P := (id : Err n t → Err n t)) (r := syn H)
      ((licensed_iff_factorsThrough _ _).1 (syn_licenses_state h))
  rw [fiberMultiplicity_const_id] at hcap
  have hstates : Fintype.card (Err n t) = (synBall n t).card := by
    exact Fintype.card_coe (synBall n t)
  have hsyndromes : Fintype.card (Fin r → ZMod 2) = 2 ^ r := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [hstates, hsyndromes] at hcap
  exact hcap

/-! ## Radius-one ball, Hamming [7,4], and a colliding parity-check matrix -/

private theorem zero_mem_synBall (n t : Nat) : (0 : Vec n) ∈ synBall n t := by
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  rw [hammingNorm_zero]
  exact Nat.zero_le t

private theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

private theorem hammingNorm_piSingle_one {n : Nat} (i : Fin n) :
    hammingNorm (Pi.single i (1 : ZMod 2) : Vec n) = 1 := by
  unfold hammingNorm
  have hfilter :
      (Finset.univ.filter fun j : Fin n =>
        (Pi.single i (1 : ZMod 2) : Vec n) j ≠ 0) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and]
    by_cases hj : j = i
    · subst hj
      simp [Pi.single_eq_same, one_ne_zero]
    · rw [Pi.single_eq_of_ne hj]
      simp [hj]
  rw [hfilter, Finset.card_singleton]

private theorem mem_synBall_one_iff {n : Nat} {e : Vec n} :
    e ∈ synBall n 1 ↔ e = 0 ∨ ∃ i : Fin n, e = Pi.single i (1 : ZMod 2) := by
  constructor
  · intro he
    have hle : hammingNorm e ≤ 1 := (Finset.mem_filter.1 he).2
    have hcases : hammingNorm e = 0 ∨ hammingNorm e = 1 := by omega
    rcases hcases with h0 | h1
    · exact Or.inl (hammingNorm_eq_zero.1 h0)
    · right
      let s : Finset (Fin n) := Finset.univ.filter fun k => e k ≠ 0
      have hs : s.card = 1 := h1
      rcases Finset.card_eq_one.1 hs with ⟨i0, hi⟩
      refine ⟨i0, ?_⟩
      funext j
      by_cases hji : i0 = j
      · subst hji
        have hine : i0 ∈ s := by simp [hi]
        have hne : e i0 ≠ 0 := (Finset.mem_filter.1 hine).2
        rcases zmod2_eq_zero_or_one (e i0) with hzero | hone
        · exact (hne hzero).elim
        · rw [hone, Pi.single_eq_same]
      · have hz : e j = 0 := by
          by_contra hne
          have hmem : j ∈ s := Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩
          have : j = i0 := by simpa [hi] using hmem
          exact hji this.symm
        rw [hz, Pi.single_eq_of_ne (M := fun _ : Fin n => ZMod 2) (Ne.symm hji)]
  · intro h
    rcases h with rfl | ⟨i, rfl⟩
    · exact zero_mem_synBall n 1
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [hammingNorm_piSingle_one]

private theorem synBall_one_card (n : Nat) : (synBall n 1).card = n + 1 := by
  have hset :
      synBall n 1 =
        insert (0 : Vec n)
          ((Finset.univ : Finset (Fin n)).image fun i =>
            (Pi.single i (1 : ZMod 2) : Vec n)) := by
    ext e
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
    rw [mem_synBall_one_iff]
    exact or_congr_right (exists_congr fun _ => eq_comm)
  rw [hset]
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective]
    · simp [Finset.card_univ, Fintype.card_fin]
    · intro i j hij
      have hii : (Pi.single i (1 : ZMod 2) : Vec n) i =
          (Pi.single j (1 : ZMod 2) : Vec n) i := congrFun hij i
      simp only [Pi.single_eq_same] at hii
      by_cases hij' : i = j
      · exact hij'
      · have hz : (Pi.single j (1 : ZMod 2) : Vec n) i = 0 :=
          Pi.single_eq_of_ne (M := fun _ : Fin n => ZMod 2) hij' (1 : ZMod 2)
        rw [hz] at hii
        exact absurd hii one_ne_zero
  · intro hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 hmem
    have hnorm : hammingNorm (0 : Vec n) = 1 := by
      rw [← hi, hammingNorm_piSingle_one]
    simp [hammingNorm_zero] at hnorm

private theorem syndrome_zero {n r : Nat} (H : Matrix (Fin r) (Fin n) (ZMod 2)) :
    syndrome H 0 = 0 := by
  simp [syndrome]

private theorem syndrome_single {n r : Nat} (H : Matrix (Fin r) (Fin n) (ZMod 2)) (i : Fin n) :
    syndrome H (Pi.single i 1) = H.col i :=
  Matrix.mulVec_single_one H i

/-- Hamming [7, 4] parity-check matrix: columns are the binary numbers 1 through 7. -/
def H74 : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  !![0, 0, 0, 1, 1, 1, 1;
     0, 1, 1, 0, 0, 1, 1;
     1, 0, 1, 0, 1, 0, 1]

set_option maxRecDepth 4096

private theorem H74_col_ne_zero (i : Fin 7) : H74.col i ≠ 0 := by
  decide +revert

private theorem H74_col_injective : Function.Injective fun i : Fin 7 => H74.col i := by
  decide +revert

/--
Proves: the Hamming [7,4] parity-check matrix licenses every radius-1 error by its syndrome.
Does not prove: correction of two or more errors, or a statement about every [7,4] generator.
Relation: CorrectsBySyndrome H74 1, equivalently InjOn of syndrome H74 on synBall 7 1.
Closure: not a rewriting closure.
Strategy: classify the radius-1 ball as zero and weight-one singles, then use injectivity of H74 columns.
Trust: kernel-only; column distinctness is a finite decide; Hamming 1950 remains ESTABLISHED citation.
Scope: the concrete matrix H74 at radius t = 1.
-/
theorem H74_corrects_one : CorrectsBySyndrome H74 1 := by
  rw [correctsBySyndrome_iff_injOn]
  intro x hx y hy hxy
  have hx' := mem_synBall_one_iff.1 hx
  have hy' := mem_synBall_one_iff.1 hy
  rcases hx' with hx0 | ⟨i, hi⟩ <;> rcases hy' with hy0 | ⟨j, hj⟩
  · exact hx0.trans hy0.symm
  · subst hx0
    subst hj
    have hcol : (0 : Fin 3 → ZMod 2) = H74.col j := by
      rw [← syndrome_zero H74, ← syndrome_single H74 j]
      exact hxy
    exact (H74_col_ne_zero j hcol.symm).elim
  · subst hy0
    subst hi
    have hcol : H74.col i = 0 := by
      rw [← syndrome_single H74 i, ← syndrome_zero H74]
      exact hxy
    exact (H74_col_ne_zero i hcol).elim
  · subst hi
    subst hj
    have hcol : H74.col i = H74.col j := by
      rw [← syndrome_single H74 i, ← syndrome_single H74 j]
      exact hxy
    exact congrArg (fun k : Fin 7 => Pi.single k (1 : ZMod 2)) (H74_col_injective hcol)

/--
Proves: the radius-1 binary ball of length 7 has eight vectors, matching 2^3 syndromes.
Does not prove: that every perfect code arises this way, or the Hamming bound for nonlinear codes.
Relation: (synBall 7 1).card = 2 ^ 3, via the radius-one count n + 1.
Closure: not a rewriting closure.
Strategy: card of {0} union the n weight-one singles; decide the resulting numeral 8 = 8.
Trust: kernel-only; the perfect Hamming-code count is ESTABLISHED (Hamming 1950; MacWilliams-Sloane 1977, Chapter 1).
Scope: length 7 and radius 1.
-/
theorem H74_perfect : (synBall 7 1).card = 2 ^ 3 := by
  rw [synBall_one_card]
  decide

/-- Two equal columns, so two distinct weight-one errors share a syndrome. -/
def Hbad : Matrix (Fin 2) (Fin 3) (ZMod 2) :=
  !![1, 1, 0;
     0, 0, 1]

/-- Weight-one error supported at coordinate 0. -/
def e₀ : Vec 3 := Pi.single 0 1

/-- Weight-one error supported at coordinate 1. -/
def e₁ : Vec 3 := Pi.single 1 1

private theorem e₀_mem_synBall : e₀ ∈ synBall 3 1 :=
  mem_synBall_one_iff.2 (Or.inr ⟨(0 : Fin 3), rfl⟩)

private theorem e₁_mem_synBall : e₁ ∈ synBall 3 1 :=
  mem_synBall_one_iff.2 (Or.inr ⟨(1 : Fin 3), rfl⟩)

/-- Failure of one-error correction for `Hbad` is a `TypedBoundary`: the shared syndrome is the
cheap observation, and the error pattern is the verdict the observation cannot retain. -/
def syndromeBoundary : TypedBoundary where
  State := Err 3 1
  Obs := Fin 2 → ZMod 2
  Verdict := Vec 3
  observe := syn Hbad
  verdict := err
  s₁ := ⟨e₀, e₀_mem_synBall⟩
  s₂ := ⟨e₁, e₁_mem_synBall⟩
  obs_eq := by decide
  verdict_ne := by decide

/--
Proves: at syndromeBoundary, the error vector is not a function of the syndrome.
Does not prove: a statement about every colliding parity-check matrix.
Relation: TypedBoundary.verdict_not_observation_function.
Closure: not a rewriting closure.
Strategy: instantiate the universal boundary law on the two equal-column weight-one errors.
Trust: kernel-only.
Scope: Hbad at radius t = 1.
-/
theorem syndromeBoundary_obeys_law :
    ¬ ∃ f : syndromeBoundary.Obs → syndromeBoundary.Verdict,
      ∀ s : syndromeBoundary.State,
        syndromeBoundary.verdict s = f (syndromeBoundary.observe s) :=
  TypedBoundary.verdict_not_observation_function syndromeBoundary

/--
Proves: Hbad does not correct one error by syndrome.
Does not prove: a statement about every 2-by-3 parity-check matrix.
Relation: Licensed (syn Hbad) err refuted by syndromeBoundary.
Closure: not a rewriting closure.
Strategy: the two TypedBoundary states share a syndrome and differ as errors.
Trust: kernel-only.
Scope: Hbad at radius t = 1.
-/
theorem Hbad_not_corrects_one : ¬ CorrectsBySyndrome Hbad 1 := by
  intro h
  exact syndromeBoundary.verdict_ne
    (h syndromeBoundary.s₁ syndromeBoundary.s₂ syndromeBoundary.obs_eq)

end OperatorKO7.Meta.UniversalBoundary.SyndromeBoundCapacity
