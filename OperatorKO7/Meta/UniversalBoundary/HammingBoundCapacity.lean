import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
import OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse

/-!
# The Hamming bound as a fiber-capacity instance

The sphere-packing (Hamming) bound for binary block codes is the framework fiber-capacity
law: the received word is the cheap observer, the (codeword, error) pair is the verdict, and
"the code corrects `t` errors" is the statement that the received word licenses that pair.
The capacity law then forces `card Code * card (ball t) ≤ 2 ^ n`. A code that fails to
correct `t` errors is a `TypedBoundary`. The Hamming bound (Hamming 1950) and the standard
error-correction criterion are ESTABLISHED; this module proves the bound inside the
framework and cites Hamming, and does not claim a new bound. The syndrome form of the same
bound for linear codes is the same fiber count with the syndrome as observer and is left
to a later lane.

```
Relation: Licensed / FactorsThrough on (received, sent) and on the constant-base joint
          observer ((), received); TypedBoundary when correction fails.
Closure:  not a rewriting closure.
Strategy: not applicable.
Trust:    kernel-only; axiom footprint is the join of the imported license and fiber-capacity
          theorems and stays inside {propext, Classical.choice, Quot.sound}.
Scope:    binary block codes as Finset (Word n); correction radius t; Hamming 1950 packing
          as additional_channel_card_lower_bound, not a new numerical bound.
```
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniversalBoundary.HammingBoundCapacity

open OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit
open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
open OperatorKO7.Meta.OperationalInexpressibility.Confusability

/-! ## NameGate: Hamming, license, fiber-capacity, and boundary API -/

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
#check @hammingDist
#check @hammingNorm
#check @hammingDist_comm
#check @hammingDist_triangle
#check @hammingNorm_zero
#check @hammingDist_eq_zero
#check @hammingDist_zero_right
#check @Bool.xor_self
#check @Bool.xor_comm
#check @Bool.xor_assoc
#check @Bool.xor_false
#check @Fintype.card_fun
#check @Fintype.card_bool
#check @Fintype.card_fin
#check @Fintype.card_prod
#check @Fintype.card_coe
#check @Fintype.card_congr
#check @Equiv.subtypeProdEquivProd
#check @Finset.card_image_of_injective
#check @Function.injective_id

/-- Binary words of length `n`, as functions `Fin n → Bool`. -/
abbrev Word (n : Nat) := Fin n → Bool

/-- Coordinatewise exclusive-or of two words. -/
def xorWord {n : Nat} (a b : Word n) : Word n := fun i => xor (a i) (b i)

/--
Proves: `xorWord a a` is the zero word.
Does not prove: any Hamming-distance identity.
Relation: coordinatewise `Bool.xor`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; `Bool.xor_self`.
Scope: every length `n`.
-/
theorem xorWord_self {n : Nat} (a : Word n) : xorWord a a = fun _ => false := by
  funext i
  exact Bool.xor_self (a i)

/--
Proves: coordinatewise exclusive-or is associative.
Does not prove: a group law beyond this associativity.
Relation: coordinatewise `xor`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; `Bool.xor_assoc`.
Scope: every length `n`.
-/
theorem xorWord_assoc {n : Nat} (a b c : Word n) :
    xorWord (xorWord a b) c = xorWord a (xorWord b c) := by
  funext i
  exact Bool.xor_assoc (a i) (b i) (c i)

/--
Proves: coordinatewise exclusive-or is commutative.
Does not prove: any cancellation identity.
Relation: coordinatewise `xor`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; `Bool.xor_comm`.
Scope: every length `n`.
-/
theorem xorWord_comm {n : Nat} (a b : Word n) : xorWord a b = xorWord b a := by
  funext i
  exact Bool.xor_comm (a i) (b i)

/--
Proves: `xorWord (xorWord a b) b = a`.
Does not prove: the opposite cancellation `xorWord a (xorWord a b) = b` (derived below).
Relation: coordinatewise `xor`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; `Bool.xor_assoc`, `Bool.xor_self`, `Bool.xor_false`.
Scope: every length `n`.
-/
theorem xorWord_xorWord_cancel {n : Nat} (a b : Word n) : xorWord (xorWord a b) b = a := by
  funext i
  calc
    xor (xor (a i) (b i)) (b i) = xor (a i) (xor (b i) (b i)) := Bool.xor_assoc (a i) (b i) (b i)
    _ = xor (a i) false := congrArg (xor (a i)) (Bool.xor_self (b i))
    _ = a i := Bool.xor_false (a i)

/--
Proves: `xorWord a (xorWord a b) = b`.
Does not prove: uniqueness of inverses beyond this identity.
Relation: coordinatewise `xor`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; `xorWord_comm`, `xorWord_xorWord_cancel`.
Scope: every length `n`.
-/
theorem xorWord_left_cancel {n : Nat} (a b : Word n) : xorWord a (xorWord a b) = b := by
  rw [xorWord_comm a (xorWord a b), xorWord_comm a b]
  exact xorWord_xorWord_cancel b a

/--
Proves: Hamming distance from `a` to `xorWord a b` equals the Hamming weight of `b`.
Does not prove: the triangle inequality.
Relation: `hammingDist` and `hammingNorm`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; coordinatewise Bool case analysis.
Scope: every length `n`.
-/
theorem hammingDist_xorWord {n : Nat} (a b : Word n) :
    hammingDist a (xorWord a b) = hammingNorm b := by
  unfold hammingDist hammingNorm xorWord
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (a i ≠ xor (a i) (b i)) ↔ (b i ≠ 0)
  cases a i <;> cases b i <;> decide

/-- Hamming ball of radius `t` in `{0,1}^n`. -/
def ball (n t : Nat) : Finset (Word n) :=
  Finset.univ.filter (fun e => hammingNorm e ≤ t)

/--
Proves: the zero word lies in every radius-`t` ball.
Does not prove: a cardinality formula for the ball.
Relation: `hammingNorm`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; `hammingNorm_zero`.
Scope: every length `n` and every radius `t`.
-/
theorem zero_mem_ball (n t : Nat) : (fun _ => false) ∈ ball n t := by
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  have h0 : (fun _ : Fin n => false) = (0 : Word n) := rfl
  rw [h0, hammingNorm_zero]
  exact Nat.zero_le t

/--
Proves: membership in `ball n t` is the Hamming-weight bound `hammingNorm e ≤ t`.
Does not prove: that the ball is a metric ball in any other metric.
Relation: `Finset.mem_filter` on `hammingNorm`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every length `n` and every radius `t`.
-/
theorem mem_ball_iff {n t : Nat} {e : Word n} : e ∈ ball n t ↔ hammingNorm e ≤ t := by
  simp [ball]

/-- Codeword-error states for a finite binary code `C` and correction radius `t`. -/
abbrev St {n : Nat} (C : Finset (Word n)) (t : Nat) :=
  {p : Word n × Word n // p.1 ∈ C ∧ p.2 ∈ ball n t}

/-- Received word: codeword exclusive-or error. This is the cheap observer. -/
def received {n : Nat} {C : Finset (Word n)} {t : Nat} : St C t → Word n :=
  fun p => xorWord p.1.1 p.1.2

/-- Sent codeword: the first coordinate of the state. This is the verdict. -/
def sent {n : Nat} {C : Finset (Word n)} {t : Nat} : St C t → Word n :=
  fun p => p.1.1

/--
The code `C` corrects `t` errors: two transmissions with the same received word
came from the same codeword. ESTABLISHED as the standard nearest-neighbour
correction criterion; formalized here as `Licensed received sent`.
-/
def Corrects {n : Nat} (C : Finset (Word n)) (t : Nat) : Prop :=
  Licensed (received (C := C) (t := t)) sent

/--
Proves: minimum distance `2 t + 1` implies `Corrects C t`, via the Hamming triangle
inequality `hammingDist c c' ≤ hammingNorm e + hammingNorm e' ≤ 2 * t`.
Does not prove: the converse (a code may correct `t` errors with a smaller minimum
distance under a different decoder), and does not prove the packing bound.
Relation: `hammingDist_triangle` and `Licensed received sent`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; Hamming 1950 packing is not used here.
Scope: every finite binary code `C ⊆ Word n` and every radius `t`.
-/
theorem corrects_of_minDist {n : Nat} {C : Finset (Word n)} {t : Nat}
    (hmin : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → 2 * t + 1 ≤ hammingDist c c') :
    Corrects C t := by
  intro p q hrecv
  let c := p.1.1
  let e := p.1.2
  let c' := q.1.1
  let e' := q.1.2
  have heq : xorWord c e = xorWord c' e' := hrecv
  have htri : hammingDist c c' ≤ hammingNorm e + hammingNorm e' := by
    calc
      hammingDist c c'
          ≤ hammingDist c (xorWord c e) + hammingDist (xorWord c e) c' :=
            hammingDist_triangle c (xorWord c e) c'
      _ = hammingNorm e + hammingDist (xorWord c' e') c' := by
            rw [hammingDist_xorWord, heq]
      _ = hammingNorm e + hammingNorm e' := by
            rw [hammingDist_comm, hammingDist_xorWord]
  have he : hammingNorm e ≤ t := (mem_ball_iff.1 p.2.2)
  have he' : hammingNorm e' ≤ t := (mem_ball_iff.1 q.2.2)
  have hpack : hammingDist c c' ≤ 2 * t :=
    htri.trans ((Nat.add_le_add he he').trans_eq (Nat.two_mul t).symm)
  by_cases hcc : c = c'
  · exact hcc
  · have hge : 2 * t + 1 ≤ hammingDist c c' := hmin c p.2.1 c' q.2.1 hcc
    exact (Nat.not_succ_le_self (2 * t) (hge.trans hpack)).elim

/--
Proves: if the code corrects `t` errors, then the joint observer `((), received)`
licenses the full state `id`, because `sent` plus `received` recover the error by
`xorWord_xorWord_cancel`.
Does not prove: injectivity of `received` alone, and does not prove the packing bound.
Relation: `Licensed (augmentObserver (fun _ => ()) received) id`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `C` and `t` with `Corrects C t`.
-/
theorem received_licenses_state {n : Nat} {C : Finset (Word n)} {t : Nat}
    (h : Corrects C t) :
    Licensed (augmentObserver (fun _ : St C t => ()) received) (id : St C t → St C t) := by
  intro p q hpq
  have hr : received p = received q := congrArg Prod.snd hpq
  have hs : sent p = sent q := h p q hr
  have herr (s : St C t) : s.1.2 = xorWord (sent s) (received s) :=
    (xorWord_left_cancel s.1.1 s.1.2).symm
  change p = q
  refine Subtype.ext ?_
  refine Prod.ext hs ?_
  have hx : xorWord (sent p) (received p) = xorWord (sent q) (received q) := by
    rw [hs, hr]
  exact (herr p).trans (hx.trans (herr q).symm)

/--
Proves: under the constant observer, `fiberMultiplicity` of `id` is `Fintype.card (St C t)`.
Does not prove: the packing bound.
Relation: `fiberMultiplicity_const` and `Finset.card_image_of_injective`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; empty-state case is the empty-supremum identity.
Scope: every finite code `C` and radius `t`, including the empty code.
-/
theorem fiberMultiplicity_const_id {n : Nat} (C : Finset (Word n)) (t : Nat) :
    fiberMultiplicity (fun _ : St C t => ()) (id : St C t → St C t) =
      Fintype.card (St C t) := by
  rcases isEmpty_or_nonempty (St C t) with hEmpty | hNE
  · have hcard : Fintype.card (St C t) = 0 := Fintype.card_eq_zero
    have hmul :
        fiberMultiplicity (fun _ : St C t => ()) (id : St C t → St C t) = 0 := by
      unfold fiberMultiplicity
      simp [Finset.univ_eq_empty]
    rw [hmul, hcard]
  · rw [fiberMultiplicity_const () (id : St C t → St C t),
      Finset.card_image_of_injective _ Function.injective_id, Finset.card_univ]

/--
Proves: `Fintype.card (Word n) = 2 ^ n`.
Does not prove: any coding bound.
Relation: `Fintype.card_fun`, `Fintype.card_bool`, `Fintype.card_fin`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every length `n`.
-/
theorem card_Word (n : Nat) : Fintype.card (Word n) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/--
Proves: if `C` corrects `t` errors, then `Fintype.card (St C t) ≤ 2 ^ n`, as the
fiber-capacity law `additional_channel_card_lower_bound` applied to the constant
base observer and the received-word side channel.
Does not prove: a new numerical bound; this is the Hamming 1950 sphere-packing bound
inside the framework (ESTABLISHED).
Relation: `additional_channel_card_lower_bound` on `(fun _ => (), id, received)`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; consumes `additional_channel_card_lower_bound`.
Scope: every finite binary code that corrects `t` errors.
-/
theorem hamming_bound {n : Nat} (C : Finset (Word n)) (t : Nat) (h : Corrects C t) :
    Fintype.card (St C t) ≤ 2 ^ n := by
  rw [← card_Word, ← fiberMultiplicity_const_id C t]
  exact additional_channel_card_lower_bound
    (q := fun _ : St C t => ()) (P := (id : St C t → St C t)) (r := received)
    ((licensed_iff_factorsThrough _ _).1 (received_licenses_state h))

/--
Proves: `Fintype.card (St C t) = C.card * (ball n t).card`.
Does not prove: the packing bound.
Relation: `Equiv.subtypeProdEquivProd` of the two membership predicates.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every finite code `C` and radius `t`.
-/
theorem card_St {n : Nat} (C : Finset (Word n)) (t : Nat) :
    Fintype.card (St C t) = C.card * (ball n t).card := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivProd
      (p := fun c : Word n => c ∈ C) (q := fun e : Word n => e ∈ ball n t)),
    Fintype.card_prod, Fintype.card_coe, Fintype.card_coe]

/--
Proves: `Corrects C t` implies the Hamming packing product `C.card * (ball n t).card ≤ 2 ^ n`.
Does not prove: a new bound, nor the linear-code syndrome form of the same count.
Relation: `hamming_bound` after `card_St`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; Hamming 1950 (ESTABLISHED) as a fiber-capacity instance.
Scope: every finite binary code that corrects `t` errors.
-/
theorem hamming_bound_product {n : Nat} {C : Finset (Word n)} {t : Nat}
    (h : Corrects C t) : C.card * (ball n t).card ≤ 2 ^ n := by
  rw [← card_St]
  exact hamming_bound C t h

/-! ## Length-3 repetition code: correction, boundary, and perfect packing -/

/-- The binary length-3 repetition code `{000, 111}`. -/
def rep3 : Finset (Word 3) := {fun _ => false, fun _ => true}

def word000 : Word 3 := fun _ => false
def word111 : Word 3 := fun _ => true
def word110 : Word 3 := fun i => decide (i.1 ≠ 2)
def word001 : Word 3 := fun i => decide (i.1 = 2)

/--
Proves: the two distinct repetition-code words are at Hamming distance 3.
Does not prove: a general formula for constant-weight distances.
Relation: `hammingDist`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; finite filter cardinality.
Scope: the two words of `rep3`.
-/
theorem hammingDist_word000_word111 : hammingDist word000 word111 = 3 := by
  unfold hammingDist word000 word111
  simp

/--
Proves: `rep3` has minimum distance 3, hence corrects one error.
Does not prove: that it corrects two errors (it does not).
Relation: `corrects_of_minDist` with `hammingDist_word000_word111`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: `rep3` at radius `t = 1`.
-/
theorem rep3_corrects_one : Corrects rep3 1 :=
  corrects_of_minDist (by
    intro c hc c' hc' hne
    simp only [rep3, Finset.mem_insert, Finset.mem_singleton] at hc hc'
    rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
    · exact (hne rfl).elim
    · have hdist : hammingDist (fun _ : Fin 3 => false) (fun _ => true) = 3 :=
        hammingDist_word000_word111
      simp [hdist]
    · have hdist : hammingDist (fun _ : Fin 3 => true) (fun _ => false) = 3 := by
        rw [hammingDist_comm]
        exact hammingDist_word000_word111
      simp [hdist]
    · exact (hne rfl).elim)

/--
Proves: `word000` is a codeword of `rep3`.
Does not prove: uniqueness.
Relation: `Finset` membership.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: `rep3`.
-/
theorem word000_mem_rep3 : word000 ∈ rep3 := by
  unfold word000
  simp [rep3]

/--
Proves: `word111` is a codeword of `rep3`.
Does not prove: uniqueness.
Relation: `Finset` membership.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: `rep3`.
-/
theorem word111_mem_rep3 : word111 ∈ rep3 := by
  unfold word111
  simp [rep3]

/--
Proves: `word110` has Hamming weight 2, so it lies in the radius-2 ball.
Does not prove: a general weight formula.
Relation: `hammingNorm`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; finite decision.
Scope: the concrete word `110`.
-/
theorem word110_mem_ball2 : word110 ∈ ball 3 2 := by
  refine mem_ball_iff.2 ?_
  decide

/--
Proves: `word001` has Hamming weight 1, so it lies in the radius-2 ball.
Does not prove: a general weight formula.
Relation: `hammingNorm`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; finite decision.
Scope: the concrete word `001`.
-/
theorem word001_mem_ball2 : word001 ∈ ball 3 2 := by
  refine mem_ball_iff.2 ?_
  decide

/-- State `(000, 110)` in `St rep3 2`. -/
def rep3_s1 : St rep3 2 := ⟨(word000, word110), ⟨word000_mem_rep3, word110_mem_ball2⟩⟩

/-- State `(111, 001)` in `St rep3 2`. -/
def rep3_s2 : St rep3 2 := ⟨(word111, word001), ⟨word111_mem_rep3, word001_mem_ball2⟩⟩

/--
Proves: both exhibited states are received as `110`.
Does not prove: uniqueness of the preimage.
Relation: `received` as `xorWord`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; finite exclusive-or.
Scope: `rep3_s1` and `rep3_s2`.
-/
theorem rep3_received_eq : received rep3_s1 = received rep3_s2 := by
  unfold received rep3_s1 rep3_s2 xorWord word000 word111 word110 word001
  funext i
  fin_cases i <;> decide

/--
Proves: the two exhibited states were sent as different codewords.
Does not prove: a general collision lemma.
Relation: `sent`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: `rep3_s1` and `rep3_s2`.
-/
theorem rep3_sent_ne : sent rep3_s1 ≠ sent rep3_s2 := by
  intro h
  have hbit : false = true := congrFun h ⟨0, Nat.succ_pos 2⟩
  cases hbit

/-- Failure of two-error correction for `rep3` is a `TypedBoundary`: the received word
`110` is the cheap observation, and the sent codeword is the verdict the observation
cannot retain. -/
def rep3Boundary : TypedBoundary where
  State := St rep3 2
  Obs := Word 3
  Verdict := Word 3
  observe := received
  verdict := sent
  s₁ := rep3_s1
  s₂ := rep3_s2
  obs_eq := rep3_received_eq
  verdict_ne := rep3_sent_ne

/--
Proves: at `rep3Boundary`, the sent codeword is not a function of the received word.
Does not prove: anything about other codes or radii.
Relation: `TypedBoundary.verdict_not_observation_function`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the length-3 repetition code at radius 2.
-/
theorem rep3Boundary_obeys_law :
    ¬ ∃ f : rep3Boundary.Obs → rep3Boundary.Verdict,
      ∀ s : rep3Boundary.State, rep3Boundary.verdict s = f (rep3Boundary.observe s) :=
  TypedBoundary.verdict_not_observation_function rep3Boundary

/--
Proves: `rep3` does not correct two errors.
Does not prove: a statement about every code of length 3.
Relation: `Licensed received sent` refuted by `rep3Boundary`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: `rep3` at radius `t = 2`.
-/
theorem rep3_not_corrects_two : ¬ Corrects rep3 2 := by
  intro h
  exact rep3Boundary.verdict_ne (h rep3Boundary.s₁ rep3Boundary.s₂ rep3Boundary.obs_eq)

/--
Proves: `rep3` at `t = 1` attains the Hamming bound (`2 * 4 = 8`).
Does not prove: that every perfect code arises this way, and does not prove the
syndrome form of the bound.
Relation: `Finset.card` of `rep3` and `ball 3 1`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; finite decision of the two cardinalities (Q49: `2*4=8` on this
instance; the Hamming product at `t = 0` is `2 * 1 = 2 ≤ 8`).
Scope: `rep3` at radius 1, the unique perfect binary repetition code of length 3.
-/
theorem rep3_perfect : rep3.card * (ball 3 1).card = 2 ^ 3 := by
  decide

#print axioms xorWord_xorWord_cancel
#print axioms corrects_of_minDist
#print axioms received_licenses_state
#print axioms fiberMultiplicity_const_id
#print axioms hamming_bound
#print axioms hamming_bound_product
#print axioms card_St
#print axioms rep3_corrects_one
#print axioms rep3Boundary_obeys_law
#print axioms rep3_not_corrects_two
#print axioms rep3_perfect

end OperatorKO7.Meta.UniversalBoundary.HammingBoundCapacity
