import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.UniversalEmbedding

/-!
# Indexed relations and recursor progress

Injective indexed families have relation-isomorphic images for any relation on
their common index type. The quotient of the two images identifies precisely
equal indices. It is nonconstant when the index type has two elements.

The recursor instance uses the actual transformed-call relation. Increasing its
counter reverses that relation. Forward countdowns instead correspond to finite
prefixes of wrapper expansion; infinite expansion cannot simulate forward calls.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.ProgressOrbitEquivalence

open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork

universe u v w

local notation "OrbitRelIso" => OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso

structure IndexedOrbitSystem (I : Type u) (A : Type v) where
  state : I → A
  injective : Function.Injective state

namespace IndexedOrbitSystem

variable {I : Type u} {A : Type v} {B : Type w}

def State (O : IndexedOrbitSystem I A) := {a : A // ∃ i, O.state i = a}

def point (O : IndexedOrbitSystem I A) (i : I) : O.State := ⟨O.state i, i, rfl⟩

noncomputable def indexEquiv (O : IndexedOrbitSystem I A) : I ≃ O.State where
  toFun := O.point
  invFun x := Classical.choose x.property
  left_inv i := O.injective (Classical.choose_spec (O.point i).property)
  right_inv x := Subtype.ext (Classical.choose_spec x.property)

noncomputable def progressObservation (O : IndexedOrbitSystem I A) : O.State → I :=
  O.indexEquiv.symm

@[simp] theorem progressObservation_state (O : IndexedOrbitSystem I A) (i : I) :
    O.progressObservation (O.point i) = i := O.indexEquiv.left_inv i

@[simp] theorem state_progressObservation (O : IndexedOrbitSystem I A) (x : O.State) :
    O.point (O.progressObservation x) = x := O.indexEquiv.right_inv x

theorem progressObservation_nonconstant (O : IndexedOrbitSystem I A)
    {i j : I} (hij : i ≠ j) :
    O.progressObservation (O.point i) ≠ O.progressObservation (O.point j) := by
  simpa only [progressObservation_state] using hij

def GeneratedStep (O : IndexedOrbitSystem I A) (J : I → I → Prop)
    (x y : O.State) : Prop := ∃ i j, J i j ∧ O.point i = x ∧ O.point j = y

theorem generatedStep_iff (O : IndexedOrbitSystem I A) (J : I → I → Prop)
    (x y : O.State) :
    O.GeneratedStep J x y ↔ J (O.progressObservation x) (O.progressObservation y) := by
  constructor
  · rintro ⟨i, j, hij, rfl, rfl⟩
    simpa only [progressObservation_state] using hij
  · intro h
    exact ⟨_, _, h, O.state_progressObservation x, O.state_progressObservation y⟩

noncomputable def indexRelationIso (O : IndexedOrbitSystem I A) (J : I → I → Prop) :
    OrbitRelIso J (O.GeneratedStep J) where
  toEquiv := O.indexEquiv
  map_rel_iff := by
    intro i j
    change J i j ↔ O.GeneratedStep J (O.point i) (O.point j)
    rw [generatedStep_iff, progressObservation_state, progressObservation_state]

/-- An independently supplied ambient relation agrees on the image exactly
when it agrees at each pair of indexed states. -/
theorem generatedStep_iff_ambient (O : IndexedOrbitSystem I A)
    (J : I → I → Prop) (R : A → A → Prop)
    (hR : ∀ i j, R (O.state i) (O.state j) ↔ J i j) (x y : O.State) :
    O.GeneratedStep J x y ↔ R x.val y.val := by
  obtain ⟨i, hi⟩ := x.property
  obtain ⟨j, hj⟩ := y.property
  have hx : O.point i = x := Subtype.ext hi
  have hy : O.point j = y := Subtype.ext hj
  subst x
  subst y
  rw [O.generatedStep_iff, progressObservation_state, progressObservation_state]
  exact (hR i j).symm

noncomputable def ambientRelationIso (O : IndexedOrbitSystem I A)
    (J : I → I → Prop) (R : A → A → Prop)
    (hR : ∀ i j, R (O.state i) (O.state j) ↔ J i j) :
    OrbitRelIso J (fun x y : O.State => R x.val y.val) where
  toEquiv := O.indexEquiv
  map_rel_iff := by intro i j; exact (hR i j).symm

end IndexedOrbitSystem

variable {I : Type u} {A : Type v} {B : Type w}

noncomputable def indexedOrbitSystem_equiv_nat (O : IndexedOrbitSystem Nat A) :
    O.State ≃ Nat := O.indexEquiv.symm

noncomputable def indexed_orbit_system_isomorphism_of_injective
    (O : IndexedOrbitSystem I A) (P : IndexedOrbitSystem I B) (J : I → I → Prop) :
    OrbitRelIso (O.GeneratedStep J) (P.GeneratedStep J) :=
  (O.indexRelationIso J).symm.trans (P.indexRelationIso J)

/-- The observation on the union of both image carriers. -/
noncomputable def commonProgress (O : IndexedOrbitSystem I A)
    (P : IndexedOrbitSystem I B) : O.State ⊕ P.State → I
  | .inl x => O.progressObservation x
  | .inr x => P.progressObservation x

noncomputable def progressSetoid (O : IndexedOrbitSystem I A)
    (P : IndexedOrbitSystem I B) : Setoid (O.State ⊕ P.State) :=
  Setoid.ker (commonProgress O P)

/-- The equivalence relation identifies the two systems only at equal progress. -/
def progressLicensedQuotient (O : IndexedOrbitSystem I A)
    (P : IndexedOrbitSystem I B) := Quotient (progressSetoid O P)

noncomputable def progressQuotientEquiv (O : IndexedOrbitSystem I A)
    (P : IndexedOrbitSystem I B) : progressLicensedQuotient O P ≃ I where
  toFun := Quotient.lift (commonProgress O P) (fun _ _ h => h)
  invFun i := Quotient.mk (progressSetoid O P) (.inl (O.point i))
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    apply Quotient.sound
    change O.progressObservation (O.point (commonProgress O P x)) = commonProgress O P x
    exact O.progressObservation_state _
  right_inv i := O.progressObservation_state i

theorem progress_quotient_equal_iff (O : IndexedOrbitSystem I A)
    (P : IndexedOrbitSystem I B) (i j : I) :
    Quotient.mk (progressSetoid O P) (.inl (O.point i)) =
      Quotient.mk (progressSetoid O P) (.inr (P.point j)) ↔ i = j := by
  rw [Quotient.eq]
  change O.progressObservation (O.point i) = P.progressObservation (P.point j) ↔ i = j
  simp only [IndexedOrbitSystem.progressObservation_state]

def UnionStep (O : IndexedOrbitSystem I A) (P : IndexedOrbitSystem I B)
    (J : I → I → Prop) : O.State ⊕ P.State → O.State ⊕ P.State → Prop
  | .inl x, .inl y => O.GeneratedStep J x y
  | .inr x, .inr y => P.GeneratedStep J x y
  | _, _ => False

/-- An edge of the quotient has representatives related in one of the two systems. -/
def QuotientStep (O : IndexedOrbitSystem I A) (P : IndexedOrbitSystem I B)
    (J : I → I → Prop) (q r : progressLicensedQuotient O P) : Prop :=
  ∃ x y, UnionStep O P J x y ∧
    Quotient.mk (progressSetoid O P) x = q ∧ Quotient.mk (progressSetoid O P) y = r

theorem quotientStep_iff (O : IndexedOrbitSystem I A) (P : IndexedOrbitSystem I B)
    (J : I → I → Prop) (q r : progressLicensedQuotient O P) :
    QuotientStep O P J q r ↔ J (progressQuotientEquiv O P q) (progressQuotientEquiv O P r) := by
  constructor
  · rintro ⟨x, y, h, rfl, rfl⟩
    cases x with
    | inl x =>
        cases y with
        | inl y => exact (O.generatedStep_iff J x y).mp h
        | inr y => exact h.elim
    | inr x =>
        cases y with
        | inl y => exact h.elim
        | inr y => exact (P.generatedStep_iff J x y).mp h
  · intro h
    refine ⟨.inl (O.point (progressQuotientEquiv O P q)),
      .inl (O.point (progressQuotientEquiv O P r)), ?_, ?_, ?_⟩
    · exact ⟨_, _, h, rfl, rfl⟩
    · exact (progressQuotientEquiv O P).symm_apply_apply q
    · exact (progressQuotientEquiv O P).symm_apply_apply r

noncomputable def progressQuotientRelationIso (O : IndexedOrbitSystem I A)
    (P : IndexedOrbitSystem I B) (J : I → I → Prop) : OrbitRelIso (QuotientStep O P J) J where
  toEquiv := progressQuotientEquiv O P
  map_rel_iff := quotientStep_iff O P J _ _

def counter : Nat → RecursorTerm
  | 0 => .void
  | n + 1 => .delta (counter n)

def recursorState (b s : RecursorTerm) (n : Nat) : RecursorTerm :=
  .recR b s (counter n)

@[simp] theorem counter_prefix (n : Nat) : deltaPrefix (counter n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [counter, deltaPrefix, ih]

@[simp] theorem recursorState_rank (b s : RecursorTerm) (n : Nat) :
    dpRank (recursorState b s n) = n := counter_prefix n

theorem recursorState_injective (b s : RecursorTerm) :
    Function.Injective (recursorState b s) := by
  intro m n h
  simpa only [recursorState_rank] using congrArg dpRank h

theorem dp_recursorState_iff (b s : RecursorTerm) (m n : Nat) :
    FreeRecursorDPPair (recursorState b s m) (recursorState b s n) ↔ m = n + 1 := by
  constructor
  · intro h
    simpa only [recursorState_rank] using freeRecursor_dp_rank_exact h
  · rintro rfl
    exact .succ b s (counter n)

def recursorOrbit (b s : RecursorTerm) : IndexedOrbitSystem Nat RecursorTerm :=
  ⟨recursorState b s, recursorState_injective b s⟩

def circularState (payload base : RecursorTerm) : Nat → RecursorTerm
  | 0 => base
  | n + 1 => .app payload (circularState payload base n)

theorem circularState_weight (payload base : RecursorTerm) (n : Nat) :
    rootWeight (circularState payload base n) =
      rootWeight base + (rootWeight payload + 1) * n := by
  induction n with
  | zero => simp [circularState]
  | succ n ih => simp only [circularState, rootWeight, ih]; ring

theorem circularState_injective (payload base : RecursorTerm) :
    Function.Injective (circularState payload base) := by
  intro m n h
  have heq := congrArg rootWeight h
  rw [circularState_weight, circularState_weight] at heq
  exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ _) (Nat.add_left_cancel heq)

def circularOrbit (payload base : RecursorTerm) : IndexedOrbitSystem Nat RecursorTerm :=
  ⟨circularState payload base, circularState_injective payload base⟩

/-- This transition adds one wrapper to its actual input term. -/
def WrapExpansion (payload : RecursorTerm) (a b : RecursorTerm) : Prop := b = .app payload a

theorem wrap_circularState_iff (payload base : RecursorTerm) (m n : Nat) :
    WrapExpansion payload (circularState payload base m) (circularState payload base n) ↔
      n = m + 1 := by
  change circularState payload base n = circularState payload base (m + 1) ↔ _
  exact ⟨fun h => circularState_injective payload base h, fun h => congrArg _ h⟩

/-- Increasing recursor indices are the converse of actual transformed calls. -/
noncomputable def recursor_circular_reverse_dp_iso (b s payload base : RecursorTerm) :
    OrbitRelIso (fun x y : (recursorOrbit b s).State => FreeRecursorDPPair y.val x.val)
      (fun x y : (circularOrbit payload base).State => WrapExpansion payload x.val y.val) :=
  ((recursorOrbit b s).ambientRelationIso (fun m n => n = m + 1)
    (fun a c => FreeRecursorDPPair c a) (fun m n => dp_recursorState_iff b s n m)).symm.trans
    ((circularOrbit payload base).ambientRelationIso (fun m n => n = m + 1)
      (WrapExpansion payload) (wrap_circularState_iff payload base))

theorem recursor_circular_progress_quotient_eq (b s payload base : RecursorTerm) (n : Nat) :
    Quotient.mk (progressSetoid (recursorOrbit b s) (circularOrbit payload base))
        (.inl ((recursorOrbit b s).point n)) =
      Quotient.mk (progressSetoid (recursorOrbit b s) (circularOrbit payload base))
        (.inr ((circularOrbit payload base).point n)) :=
  (progress_quotient_equal_iff _ _ n n).mpr rfl

theorem recursor_progress_nonconstant (b s : RecursorTerm) :
    (recursorOrbit b s).progressObservation ((recursorOrbit b s).point 0) ≠
      (recursorOrbit b s).progressObservation ((recursorOrbit b s).point 1) :=
  (recursorOrbit b s).progressObservation_nonconstant (by decide)

theorem no_infinite_dp_execution (f : Nat → RecursorTerm) :
    ¬ ∀ n, FreeRecursorDPPair (f n) (f (n + 1)) := by
  intro h
  have hsum : ∀ n, dpRank (f n) + n = dpRank (f 0) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
        have hh := freeRecursor_dp_rank_exact (h n)
        omega
  have := hsum (dpRank (f 0) + 1)
  omega

/-- No map, injective or otherwise, preserves all wrapper steps as forward calls. -/
theorem no_wrap_to_dp_simulation (payload : RecursorTerm) (f : RecursorTerm → RecursorTerm) :
    ¬ ∀ a b, WrapExpansion payload a b → FreeRecursorDPPair (f a) (f b) := by
  intro h
  apply no_infinite_dp_execution (fun n => f (circularState payload .void n))
  intro n
  exact h _ _ rfl

def countdownOrbit (b s : RecursorTerm) (N : Nat) :
    IndexedOrbitSystem (Fin (N + 1)) RecursorTerm where
  state k := recursorState b s (N - k.val)
  injective := by
    intro i j h
    have hi := i.isLt
    have hj := j.isLt
    apply Fin.ext
    have heq := recursorState_injective b s h
    omega

def circularPrefix (payload base : RecursorTerm) (N : Nat) :
    IndexedOrbitSystem (Fin (N + 1)) RecursorTerm where
  state k := circularState payload base k.val
  injective := fun _ _ h => Fin.ext (circularState_injective payload base h)

def PrefixStep (N : Nat) (i j : Fin (N + 1)) : Prop := j.val = i.val + 1

theorem countdown_dp_iff (b s : RecursorTerm) (N : Nat) (i j : Fin (N + 1)) :
    FreeRecursorDPPair ((countdownOrbit b s N).state i) ((countdownOrbit b s N).state j) ↔
      PrefixStep N i j := by
  change FreeRecursorDPPair (recursorState b s (N - i.val))
    (recursorState b s (N - j.val)) ↔ j.val = i.val + 1
  rw [dp_recursorState_iff]
  have hi := i.isLt
  have hj := j.isLt
  omega

theorem circularPrefix_step_iff (payload base : RecursorTerm) (N : Nat)
    (i j : Fin (N + 1)) :
    WrapExpansion payload ((circularPrefix payload base N).state i)
      ((circularPrefix payload base N).state j) ↔ PrefixStep N i j :=
  wrap_circularState_iff payload base i.val j.val

/-- Actual forward calls match a bounded expansion prefix, including N = 0.
The expansion relation is restricted to the displayed prefix carrier. -/
noncomputable def finite_countdown_circular_prefix_iso
    (b s payload base : RecursorTerm) (N : Nat) :
    OrbitRelIso (fun x y : (countdownOrbit b s N).State => FreeRecursorDPPair x.val y.val)
      (fun x y : (circularPrefix payload base N).State => WrapExpansion payload x.val y.val) :=
  ((countdownOrbit b s N).ambientRelationIso (PrefixStep N) FreeRecursorDPPair
    (countdown_dp_iff b s N)).symm.trans
    ((circularPrefix payload base N).ambientRelationIso (PrefixStep N) (WrapExpansion payload)
      (circularPrefix_step_iff payload base N))

theorem circular_prefix_not_outgoing_closed (payload base : RecursorTerm) (N : Nat) :
    ∃ a, a ∈ Set.range (circularPrefix payload base N).state ∧
      ∃ b, WrapExpansion payload a b ∧
        b ∉ Set.range (circularPrefix payload base N).state := by
  refine ⟨circularState payload base N, ⟨⟨N, Nat.lt_succ_self N⟩, rfl⟩,
    circularState payload base (N + 1), rfl, ?_⟩
  rintro ⟨k, hk⟩
  have heq : k.val = N + 1 := circularState_injective payload base hk
  have := k.isLt
  omega

end OperatorKO7.Meta.OperationalInexpressibility.ProgressOrbitEquivalence
