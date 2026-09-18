import OperatorKO7.Meta.Methods.OrientationClosure.ObserverRanks
import OperatorKO7.Meta.Methods.OrientationClosure.SourceChainSoundness
import OperatorKO7.Meta.Rewriting.RankOrderClassification
import OperatorKO7.Meta.OperationalInexpressibility.TargetKernelQuotient
import Mathlib.Tactic

/-!
# Which observers of a countdown license a well-founded rank

An observer `q` of a relation `R` licenses a rank when the attained observed relation
`ObservedRev R q` is well-founded. By `ObserverRanks.lean` this holds exactly when some rank
into a well-founded relation factors through `q`. This module compares licensing observers
with the counter of a counter system (`RankOrderClassification.CounterSystem`, arbitrary
carrier) and with the counter `recursiveCallRank` of the transformed recursive-call relation
of the free recursor.

* (a) An observer `g ∘ counter` licenses a rank exactly when `g` is injective, which is exactly
  when its kernel equals the counter kernel. Merging two counter values closes an observed
  cycle along the attained countdown.
* (b) The claim "the counter is the coarsest licensing observer" is false. On the free call
  relation two licensing observers identify counter values in different base fibers, neither
  refines the other or the counter, and every observer coarser than both licenses no rank.
  Hence no licensing observer is coarser than all natural-valued licensing observers.
* (c) The observers sufficient for the counter are exactly the observers whose kernel refines
  the counter kernel (`targetKernelQuotient_coarsest_sufficient` at target `counter`); each of
  them licenses a rank, and the counter kernel quotient is isomorphic to `Nat` by the unique
  equivalence that commutes with the two projections.
* (d) Natural-valued ranks constant on counter fibers are the strict recodings of the counter
  (`counter_order_classification`), while the free call relation has infinitely many rank
  orders once fiber constancy is dropped.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.ObserverSufficiency

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.ObserverRanks
open OperatorKO7.Methods.OrientationClosure.SourceChainSoundness
open OperatorKO7.Meta.Rewriting.RankOrderClassification
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.TargetKernel

universe u v w

/-! ## Licensing -/

/-- An observer licenses a rank when the attained observed relation is reverse
well-founded. -/
def LicensesRank {A : Type u} {B : Type v} (R : A → A → Prop) (q : A → B) : Prop :=
  WellFounded (ObservedRev R q)

/-- Licensing is the existence of a factored rank into a well-founded relation on the
observer carrier. -/
theorem licensesRank_iff_factoredRank {A : Type u} {B : Type v}
    (R : A → A → Prop) (q : A → B) :
    LicensesRank R q ↔
      ∃ lt : B → B → Prop, ∃ rank : B → B, WellFounded lt ∧ FactoredRank R q lt rank := by
  constructor
  · intro h
    exact ⟨ObservedRev R q, id, h, identity_factoredRank_of_observedRev_wellFounded h⟩
  · rintro ⟨lt, rank, hlt, hrank⟩
    exact observedRev_wellFounded_of_factoredRank hlt hrank

/-- A factored rank into any well-founded target licenses the observer. -/
theorem licensesRank_of_factoredRank {A : Type u} {B : Type v} {C : Type w}
    {R : A → A → Prop} {q : A → B} {lt : C → C → Prop} {rank : B → C}
    (hlt : WellFounded lt) (h : FactoredRank R q lt rank) : LicensesRank R q :=
  observedRev_wellFounded_of_factoredRank hlt h

/-- A cycle of attained observed steps rules out licensing. -/
theorem not_licensesRank_of_cycle {A : Type u} {B : Type v} {R : A → A → Prop}
    {q : A → B} {b : B} (h : Relation.TransGen (ObservedStep R q) b b) :
    ¬ LicensesRank R q := by
  intro hwf
  have hwf' : WellFounded (ObservedRev R q) := hwf
  have h' : Relation.TransGen (ObservedRev R q) b b := h.swap
  exact ((WellFounded.transGen hwf').asymmetric b b h') h'

/-! ## (a) Observers that factor through the counter -/

/-- Through any observer of the counter, the attained countdown steps give a path from the
image of `m + k + 1` to the image of `m`. -/
theorem countdown_observed_path {A : Type u} (C : CounterSystem A) {B : Type v}
    (g : Nat → B) (m k : Nat) :
    Relation.TransGen (ObservedStep C.Step (fun x => g (C.counter x)))
      (g (m + k + 1)) (g m) := by
  induction k with
  | zero =>
      exact Relation.TransGen.single
        ⟨C.state (m + 1), C.state m, C.step_succ m, by simp [C.counter_state],
          by simp [C.counter_state]⟩
  | succ k ih =>
      have e : m + (k + 1) + 1 = m + k + 1 + 1 := by omega
      rw [e]
      exact Relation.TransGen.head
        ⟨C.state (m + k + 1 + 1), C.state (m + k + 1), C.step_succ (m + k + 1),
          by simp [C.counter_state], by simp [C.counter_state]⟩ ih

/-- (a) An observer that factors through the counter licenses a rank exactly when the
factoring map is injective on the attained countdown, which here is every natural number. -/
theorem counterFactored_licensesRank_iff_injective {A : Type u} (C : CounterSystem A)
    {B : Type v} (g : Nat → B) :
    LicensesRank C.Step (fun x => g (C.counter x)) ↔ Function.Injective g := by
  constructor
  · intro hwf m k hmk
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hpath := countdown_observed_path C g m (k - m - 1)
      have e : m + (k - m - 1) + 1 = k := by omega
      rw [e, ← hmk] at hpath
      exact not_licensesRank_of_cycle hpath hwf
    · have hpath := countdown_observed_path C g k (m - k - 1)
      have e : k + (m - k - 1) + 1 = m := by omega
      rw [e, hmk] at hpath
      exact not_licensesRank_of_cycle hpath hwf
  · intro hinj
    show WellFounded (ObservedRev C.Step (fun x => g (C.counter x)))
    apply Subrelation.wf (r := InvImage (· < ·) (Function.invFun g))
    · intro c b hcb
      rcases hcb with ⟨x, y, hxy, hx, hy⟩
      subst hx
      subst hy
      have h1 := Function.leftInverse_invFun hinj (C.counter x)
      have h2 := Function.leftInverse_invFun hinj (C.counter y)
      show Function.invFun g (g (C.counter y)) < Function.invFun g (g (C.counter x))
      rw [h1, h2]
      exact C.decreases hxy
    · exact InvImage.wf _ Nat.lt_wfRel.wf

/-- (a), kernel form: a counter-factored observer licenses a rank exactly when its kernel is
the counter kernel. -/
theorem counterFactored_licensesRank_iff_same_kernel {A : Type u} (C : CounterSystem A)
    {B : Type v} (g : Nat → B) :
    LicensesRank C.Step (fun x => g (C.counter x)) ↔
      ∀ x y, g (C.counter x) = g (C.counter y) ↔ C.counter x = C.counter y := by
  rw [counterFactored_licensesRank_iff_injective]
  constructor
  · intro hinj x y
    exact ⟨fun h => hinj h, fun h => by rw [h]⟩
  · intro h m k hmk
    have hc := (h (C.state m) (C.state k)).1 (by simpa [C.counter_state] using hmk)
    simpa [C.counter_state] using hc

/-! ## (c) Observers sufficient for the counter -/

/-- (c) The OI coarsest-sufficient theorem at target `counter`: the counter kernel quotient is
sufficient, and every sufficient observer refines it. -/
theorem counter_target_coarsest_sufficient {A : Type u} (C : CounterSystem A) :
    Licensed (targetKernelQuotientMap C.counter) C.counter ∧
      ∀ {Q : Type w} (q : A → Q), Licensed q C.counter →
        ObserverRefines q (targetKernelQuotientMap C.counter) :=
  targetKernelQuotient_coarsest_sufficient C.counter

/-- (c) The observers sufficient for the counter are exactly the observers whose kernel
refines the counter kernel. -/
theorem sufficient_iff_refines_counter_kernel {A : Type u} (C : CounterSystem A)
    {Q : Type w} (q : A → Q) :
    Licensed q C.counter ↔ ObserverRefines q (targetKernelQuotientMap C.counter) :=
  licensed_iff_refines_targetKernelQuotient q C.counter

/-- (c) Every observer sufficient for the counter licenses a rank. -/
theorem sufficient_observer_licensesRank {A : Type u} (C : CounterSystem A)
    {Q : Type w} (q : A → Q) (hq : Licensed q C.counter) :
    LicensesRank C.Step q := by
  classical
  let rank : Q → Nat := fun b =>
    if h : ∃ x, q x = b then C.counter (Classical.choose h) else 0
  have hrank : ∀ x, rank (q x) = C.counter x := by
    intro x
    have hex : ∃ x', q x' = q x := ⟨x, rfl⟩
    simp only [rank, dif_pos hex]
    exact hq _ _ (Classical.choose_spec hex)
  show WellFounded (ObservedRev C.Step q)
  apply Subrelation.wf (r := InvImage (· < ·) rank)
  · intro c b hcb
    rcases hcb with ⟨x, y, hxy, hx, hy⟩
    subst hx
    subst hy
    show rank (q y) < rank (q x)
    rw [hrank, hrank]
    exact C.decreases hxy
  · exact InvImage.wf _ Nat.lt_wfRel.wf

/-- (c) The counter kernel quotient is isomorphic to `Nat`: the decoder is an equivalence
because every counter value is attained. -/
def counterKernelQuotientEquivNat {A : Type u} (C : CounterSystem A) :
    TargetKernelQuotient C.counter ≃ Nat where
  toFun := targetKernelDecoder C.counter
  invFun n := targetKernelQuotientMap C.counter (C.state n)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    show targetKernelQuotientMap C.counter (C.state (C.counter x)) =
      targetKernelQuotientMap C.counter x
    exact (targetKernelQuotientMap_eq_iff C.counter _ _).2 (C.counter_state _)
  right_inv n := C.counter_state n

/-- (c) The hom-set of equivalences between the counter kernel quotient and `Nat` that commute
with the projections from the carrier has exactly one element. -/
theorem counterKernelQuotientEquivNat_unique {A : Type u} (C : CounterSystem A)
    (e : TargetKernelQuotient C.counter ≃ Nat)
    (he : ∀ x, e (targetKernelQuotientMap C.counter x) = C.counter x) :
    e = counterKernelQuotientEquivNat C := by
  apply Equiv.ext
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact he x

/-! ## The free recursor call relation as a counter system -/

/-- Leading-successor tower `succ^n zero`. -/
def succTower {ν : Type u} : Nat → FreeTerm ν
  | 0 => .zero
  | n + 1 => .succ (succTower n)

theorem succDepth_succTower {ν : Type u} (n : Nat) :
    succDepth (succTower n : FreeTerm ν) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show succDepth (succTower n : FreeTerm ν) + 1 = n + 1
      rw [ih]

/-- Recursor state with base `zero`, step `zero` and counter tower of height `n`. -/
def zeroBaseState {ν : Type u} (n : Nat) : FreeTerm ν :=
  .recur .zero .zero (succTower n)

/-- Recursor state with base `succ zero`, step `zero` and counter tower of height `n`. -/
def succBaseState {ν : Type u} (n : Nat) : FreeTerm ν :=
  .recur (.succ .zero) .zero (succTower n)

theorem recursiveCallRank_zeroBaseState {ν : Type u} (n : Nat) :
    recursiveCallRank (zeroBaseState n : FreeTerm ν) = n := by
  have h := succDepth_succTower (ν := ν) n
  have h0 : recursiveCallRank (FreeTerm.zero : FreeTerm ν) = 0 := rfl
  show succDepth (succTower n : FreeTerm ν) + recursiveCallRank (FreeTerm.zero : FreeTerm ν) = n
  omega

theorem recursiveCallRank_succBaseState {ν : Type u} (n : Nat) :
    recursiveCallRank (succBaseState n : FreeTerm ν) = n := by
  have h := succDepth_succTower (ν := ν) n
  have h0 : recursiveCallRank (FreeTerm.succ FreeTerm.zero : FreeTerm ν) = 0 := rfl
  show succDepth (succTower n : FreeTerm ν) +
    recursiveCallRank (FreeTerm.succ FreeTerm.zero : FreeTerm ν) = n
  omega

theorem zeroBaseState_call {ν : Type u} (n : Nat) :
    FreeRecursiveCallPair (zeroBaseState (n + 1) : FreeTerm ν) (zeroBaseState n) := by
  show FreeRecursiveCallPair (FreeTerm.recur .zero .zero (.succ (succTower n)) : FreeTerm ν)
    (FreeTerm.recur .zero .zero (succTower n))
  exact .successor _ _ _

/-- The transformed-call relation of the free recursor as a counter system: the counter is
`recursiveCallRank`, and the states `zeroBaseState n` attain every value. -/
def freeCallCounterSystem (ν : Type u) : CounterSystem (FreeTerm ν) where
  Step := FreeRecursiveCallPair
  counter := recursiveCallRank
  decreases := fun h => freeRecursiveCallPair_rank_decreases h
  state n := zeroBaseState n
  counter_state n := recursiveCallRank_zeroBaseState n
  step_succ n := zeroBaseState_call n

/-- (a) on the free call relation: an observer of the call counter licenses a rank exactly when
the factoring map is injective. -/
theorem freeCall_counterFactored_licensesRank_iff_injective (ν : Type u) {B : Type v}
    (g : Nat → B) :
    LicensesRank (FreeRecursiveCallPair (ν := ν)) (fun t => g (recursiveCallRank t)) ↔
      Function.Injective g :=
  counterFactored_licensesRank_iff_injective (freeCallCounterSystem ν) g

/-- (c) on the free call relation: sufficient observers for the call counter are exactly the
observers refining its kernel, and each licenses a rank. -/
theorem freeCall_sufficient_observers (ν : Type u) {Q : Type w} (q : FreeTerm ν → Q) :
    (Licensed q (recursiveCallRank (ν := ν)) ↔
        ObserverRefines q (targetKernelQuotientMap (recursiveCallRank (ν := ν)))) ∧
      (Licensed q (recursiveCallRank (ν := ν)) →
        LicensesRank (FreeRecursiveCallPair (ν := ν)) q) :=
  ⟨sufficient_iff_refines_counter_kernel (freeCallCounterSystem ν) q,
    sufficient_observer_licensesRank (freeCallCounterSystem ν) q⟩

/-! ## (b) No coarsest licensing observer -/

/-- Base flag: one on recursor states whose base is `zero`, zero elsewhere. -/
def zeroBaseFlag {ν : Type u} : FreeTerm ν → Nat
  | .recur .zero _ _ => 1
  | _ => 0

/-- Call counter raised by one on the zero-base fiber. -/
def zeroBaseRaised {ν : Type u} (t : FreeTerm ν) : Nat :=
  recursiveCallRank t + zeroBaseFlag t

/-- Call counter raised by one off the zero-base fiber. -/
def otherBaseRaised {ν : Type u} (t : FreeTerm ν) : Nat :=
  recursiveCallRank t + (1 - zeroBaseFlag t)

theorem zeroBaseFlag_call {ν : Type u} {a c : FreeTerm ν}
    (h : FreeRecursiveCallPair a c) : zeroBaseFlag a = zeroBaseFlag c := by
  cases h with
  | successor b s n => cases b <;> rfl

theorem recursiveCallRank_call {ν : Type u} {a c : FreeTerm ν}
    (h : FreeRecursiveCallPair a c) : recursiveCallRank a = recursiveCallRank c + 1 := by
  cases h with
  | successor b s n =>
      simp only [recursiveCallRank, succDepth]
      omega

/-- An observer that drops by exactly one along every call pair licenses a rank. -/
theorem licensesRank_of_call_drop {ν : Type u} {q : FreeTerm ν → Nat}
    (hq : ∀ {a c : FreeTerm ν}, FreeRecursiveCallPair a c → q a = q c + 1) :
    LicensesRank (FreeRecursiveCallPair (ν := ν)) q := by
  show WellFounded (ObservedRev FreeRecursiveCallPair q)
  apply Subrelation.wf (r := fun c b : Nat => c < b)
  · intro c b hcb
    rcases hcb with ⟨x, y, hxy, hx, hy⟩
    subst hx
    subst hy
    have hd := hq hxy
    omega
  · exact Nat.lt_wfRel.wf

theorem zeroBaseRaised_licensesRank (ν : Type u) :
    LicensesRank (FreeRecursiveCallPair (ν := ν)) zeroBaseRaised := by
  apply licensesRank_of_call_drop
  intro a c h
  have h1 := recursiveCallRank_call h
  have h2 := zeroBaseFlag_call h
  unfold zeroBaseRaised
  omega

theorem otherBaseRaised_licensesRank (ν : Type u) :
    LicensesRank (FreeRecursiveCallPair (ν := ν)) otherBaseRaised := by
  apply licensesRank_of_call_drop
  intro a c h
  have h1 := recursiveCallRank_call h
  have h2 := zeroBaseFlag_call h
  unfold otherBaseRaised
  omega

theorem zeroBaseRaised_zeroBaseState {ν : Type u} (n : Nat) :
    zeroBaseRaised (zeroBaseState n : FreeTerm ν) = n + 1 := by
  have h1 := recursiveCallRank_zeroBaseState (ν := ν) n
  have h2 : zeroBaseFlag (zeroBaseState n : FreeTerm ν) = 1 := rfl
  unfold zeroBaseRaised
  omega

theorem zeroBaseRaised_succBaseState {ν : Type u} (n : Nat) :
    zeroBaseRaised (succBaseState n : FreeTerm ν) = n := by
  have h1 := recursiveCallRank_succBaseState (ν := ν) n
  have h2 : zeroBaseFlag (succBaseState n : FreeTerm ν) = 0 := rfl
  unfold zeroBaseRaised
  omega

theorem otherBaseRaised_zeroBaseState {ν : Type u} (n : Nat) :
    otherBaseRaised (zeroBaseState n : FreeTerm ν) = n := by
  have h1 := recursiveCallRank_zeroBaseState (ν := ν) n
  have h2 : zeroBaseFlag (zeroBaseState n : FreeTerm ν) = 1 := rfl
  unfold otherBaseRaised
  omega

theorem otherBaseRaised_succBaseState {ν : Type u} (n : Nat) :
    otherBaseRaised (succBaseState n : FreeTerm ν) = n + 1 := by
  have h1 := recursiveCallRank_succBaseState (ν := ν) n
  have h2 : zeroBaseFlag (succBaseState n : FreeTerm ν) = 0 := rfl
  unfold otherBaseRaised
  omega

/-- Neither raised observer refines the call counter. -/
theorem raised_observers_not_refine_counter (ν : Type u) :
    ¬ ObserverRefines (zeroBaseRaised (ν := ν)) recursiveCallRank ∧
      ¬ ObserverRefines (otherBaseRaised (ν := ν)) recursiveCallRank := by
  constructor
  · intro h
    have hq : zeroBaseRaised (zeroBaseState 0 : FreeTerm ν) =
        zeroBaseRaised (succBaseState 1 : FreeTerm ν) := by
      have a := zeroBaseRaised_zeroBaseState (ν := ν) 0
      have b := zeroBaseRaised_succBaseState (ν := ν) 1
      omega
    have hc := h hq
    have a := recursiveCallRank_zeroBaseState (ν := ν) 0
    have b := recursiveCallRank_succBaseState (ν := ν) 1
    omega
  · intro h
    have hq : otherBaseRaised (succBaseState 0 : FreeTerm ν) =
        otherBaseRaised (zeroBaseState 1 : FreeTerm ν) := by
      have a := otherBaseRaised_succBaseState (ν := ν) 0
      have b := otherBaseRaised_zeroBaseState (ν := ν) 1
      omega
    have hc := h hq
    have a := recursiveCallRank_succBaseState (ν := ν) 0
    have b := recursiveCallRank_zeroBaseState (ν := ν) 1
    omega

/-- The two raised observers are incomparable in the refinement order. -/
theorem raised_observers_incomparable (ν : Type u) :
    ¬ ObserverRefines (zeroBaseRaised (ν := ν)) otherBaseRaised ∧
      ¬ ObserverRefines (otherBaseRaised (ν := ν)) zeroBaseRaised := by
  constructor
  · intro h
    have hq : zeroBaseRaised (zeroBaseState 0 : FreeTerm ν) =
        zeroBaseRaised (succBaseState 1 : FreeTerm ν) := by
      have a := zeroBaseRaised_zeroBaseState (ν := ν) 0
      have b := zeroBaseRaised_succBaseState (ν := ν) 1
      omega
    have hc := h hq
    have a := otherBaseRaised_zeroBaseState (ν := ν) 0
    have b := otherBaseRaised_succBaseState (ν := ν) 1
    omega
  · intro h
    have hq : otherBaseRaised (succBaseState 0 : FreeTerm ν) =
        otherBaseRaised (zeroBaseState 1 : FreeTerm ν) := by
      have a := otherBaseRaised_succBaseState (ν := ν) 0
      have b := otherBaseRaised_zeroBaseState (ν := ν) 1
      omega
    have hc := h hq
    have a := zeroBaseRaised_succBaseState (ν := ν) 0
    have b := zeroBaseRaised_zeroBaseState (ν := ν) 1
    omega

/-- Every observer coarser than both raised observers identifies the zero-base states at
counters `0` and `2`, closes an observed cycle, and licenses no rank. -/
theorem common_coarsening_not_licensing {ν : Type u} {Q : Type w} (r : FreeTerm ν → Q)
    (h1 : ObserverRefines (zeroBaseRaised (ν := ν)) r)
    (h2 : ObserverRefines (otherBaseRaised (ν := ν)) r) :
    ¬ LicensesRank (FreeRecursiveCallPair (ν := ν)) r := by
  have e1 : r (zeroBaseState 0) = r (succBaseState 1) := by
    apply h1
    have a := zeroBaseRaised_zeroBaseState (ν := ν) 0
    have b := zeroBaseRaised_succBaseState (ν := ν) 1
    omega
  have e2 : r (succBaseState 1) = r (zeroBaseState 2) := by
    apply h2
    have a := otherBaseRaised_succBaseState (ν := ν) 1
    have b := otherBaseRaised_zeroBaseState (ν := ν) 2
    omega
  have hpath : Relation.TransGen (ObservedStep FreeRecursiveCallPair r)
      (r (zeroBaseState 2)) (r (zeroBaseState 0)) :=
    Relation.TransGen.head ⟨zeroBaseState 2, zeroBaseState 1, zeroBaseState_call 1, rfl, rfl⟩
      (Relation.TransGen.single
        ⟨zeroBaseState 1, zeroBaseState 0, zeroBaseState_call 0, rfl, rfl⟩)
  rw [e1, e2] at hpath
  exact not_licensesRank_of_cycle hpath

/-- (b) REFUTED_EXTENSION of "the counter is the coarsest licensing observer": on the free
call relation no licensing observer is coarser than every natural-valued licensing observer. -/
theorem no_coarsest_licensing_observer (ν : Type u) {Q : Type w} :
    ¬ ∃ κ : FreeTerm ν → Q, LicensesRank (FreeRecursiveCallPair (ν := ν)) κ ∧
      ∀ q : FreeTerm ν → Nat, LicensesRank (FreeRecursiveCallPair (ν := ν)) q →
        ObserverRefines q κ := by
  rintro ⟨κ, hκ, hall⟩
  exact common_coarsening_not_licensing κ (hall _ (zeroBaseRaised_licensesRank ν))
    (hall _ (otherBaseRaised_licensesRank ν)) hκ

/-- (b) The two-observer witness in one statement. -/
theorem counter_not_coarsest_licensing_observer (ν : Type u) :
    (LicensesRank (FreeRecursiveCallPair (ν := ν)) zeroBaseRaised ∧
        LicensesRank (FreeRecursiveCallPair (ν := ν)) otherBaseRaised) ∧
      (¬ ObserverRefines (zeroBaseRaised (ν := ν)) recursiveCallRank ∧
        ¬ ObserverRefines (otherBaseRaised (ν := ν)) recursiveCallRank) ∧
      (¬ ObserverRefines (zeroBaseRaised (ν := ν)) otherBaseRaised ∧
        ¬ ObserverRefines (otherBaseRaised (ν := ν)) zeroBaseRaised) ∧
      ∀ r : FreeTerm ν → Nat, ObserverRefines (zeroBaseRaised (ν := ν)) r →
        ObserverRefines (otherBaseRaised (ν := ν)) r →
          ¬ LicensesRank (FreeRecursiveCallPair (ν := ν)) r :=
  ⟨⟨zeroBaseRaised_licensesRank ν, otherBaseRaised_licensesRank ν⟩,
    raised_observers_not_refine_counter ν, raised_observers_incomparable ν,
    fun r h1 h2 => common_coarsening_not_licensing r h1 h2⟩

/-! ## (d) Rankings constant on counter fibers -/

/-- (d) `counter_order_classification` for the free call relation. -/
theorem freeCall_counter_order_classification (ν : Type u) :
    Nonempty ((freeCallCounterSystem ν).CounterRank ≃ CounterSystem.StrictRecoding) ∧
      Nonempty ((freeCallCounterSystem ν).OrderQuotient ≃ PUnit) ∧
      ∀ f : NaturalRank (freeCallCounterSystem ν).Step,
        (freeCallCounterSystem ν).FiberConstant f.1 ↔
          RankSameOrder f (freeCallCounterSystem ν).rank :=
  (freeCallCounterSystem ν).counter_order_classification

/-- Depth of the base argument of a recursor state. -/
def baseDepth {ν : Type u} : FreeTerm ν → Nat
  | .recur b _ _ => succDepth b
  | _ => 0

theorem baseDepth_call {ν : Type u} {a c : FreeTerm ν}
    (h : FreeRecursiveCallPair a c) : baseDepth a = baseDepth c := by
  cases h
  rfl

/-- (d) Without fiber constancy the free call relation has infinitely many rank orders: the
base depth is a call invariant with a positive value and a zero fiber attaining every
counter value. -/
theorem freeCall_rank_orders_infinite (ν : Type u) :
    Infinite (RankOrderQuotient (FreeRecursiveCallPair (ν := ν))) :=
  rankOrderQuotient_infinite_of_axis_witnesses (freeCallCounterSystem ν).rank baseDepth
    (fun h => baseDepth_call h) ⟨succBaseState 0, Nat.zero_lt_one⟩
    (fun n => ⟨zeroBaseState n, recursiveCallRank_zeroBaseState n, rfl⟩)

end OperatorKO7.Methods.OrientationClosure.ObserverSufficiency
