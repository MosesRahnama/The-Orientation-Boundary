import OperatorKO7.Meta.OperationalInexpressibility.FaithfulRecursorRealization
import OperatorKO7.Meta.OperationalInexpressibility.ConstructionConfessionModuli
import OperatorKO7.Meta.Rewriting.RankOrderClassification

/-!
# Rank classification in every faithful recursor realization

Both generated root steps and transformed calls admit infinitely many full
strict orders on represented states. Among all transformed-call ranks, those
constant on counter fibers are precisely the strictly increasing recodings of
the counter. Their full-order quotient has one class. This classification
quantifies over rank functions, not a catalog of method names.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.FaithfulRecursorRanks

open OperatorKO7
open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.Recursor.RecursorFreeAlgebra
open OperatorKO7.Meta.OperationalInexpressibility.FaithfulRecursorRealization
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
open OperatorKO7.Meta.OperationalInexpressibility.ConstructionConfessionModuli
open OperatorKO7.PolyInterpretation.Family
open OperatorKO7.Meta.Rewriting.RankOrderClassification

universe u

variable {X : Type u}

/-- This equivalence concerns constructor syntax. It does not identify the
two-rule recursor relation with the full eight-rule KO7 relation. -/
noncomputable def traceEquiv (e : FaithfulRealization X) : Trace ≃ e.State where
  toFun t := e.point (ofTrace t)
  invFun x := ko7Realization.encode (e.decode x)
  left_inv t := by simp only [e.decode_point, ko7_encode_ofTrace]
  right_inv x := by
    change e.point (ofTrace (RecursorTerm.fold ko7Algebra (e.decode x))) = x
    rw [ofTrace_fold, e.point_decode]

@[simp] theorem traceEquiv_apply (e : FaithfulRealization X) (t : Trace) :
    traceEquiv e t = e.point (ofTrace t) := rfl

@[simp] theorem traceEquiv_symm_apply (e : FaithfulRealization X) (x : e.State) :
    (traceEquiv e).symm x = ko7Realization.encode (e.decode x) := rfl

def RootState (e : FaithfulRealization X) (x y : e.State) : Prop := e.Root x.1 y.1

def DPState (e : FaithfulRealization X) (x y : e.State) : Prop := e.DP x.1 y.1

theorem rootState_iff (e : FaithfulRealization X) (x y : e.State) :
    RootState e x y ↔ KO7RecursorStep ((traceEquiv e).symm x) ((traceEquiv e).symm y) := by
  change e.Realized FreeRecursorStep x.val y.val ↔ _
  rw [e.realized_state_iff]
  exact (ko7Realization.freeRecursor_step_iff_realized_step _ _).trans
    (ko7_root_exact _ _)

theorem dpState_iff (e : FaithfulRealization X) (x y : e.State) :
    DPState e x y ↔ MetaDependencyPairs.DPPair
      ((traceEquiv e).symm x) ((traceEquiv e).symm y) := by
  change e.Realized FreeRecursorDPPair x.val y.val ↔ _
  rw [e.realized_state_iff]
  exact (ko7Realization.freeRecursor_dp_iff_realized_dp _ _).trans
    (ko7_dp_exact _ _)

noncomputable def rootRankFamily (e : FaithfulRealization X) (k : Nat) :
    NaturalRank (RootState e) :=
  ⟨fun x => Wam (k + 1) 1 ((traceEquiv e).symm x), fun h =>
    Wam_orients_step (by omega) (by decide)
      (ko7RecursorStep_sub_fullStep ((rootState_iff e _ _).mp h))⟩

noncomputable def dpRankFamily (e : FaithfulRealization X) (k : Nat) :
    NaturalRank (DPState e) :=
  ⟨fun x => baseSensitiveDPRank k ((traceEquiv e).symm x), fun h =>
    baseSensitiveDPRank_decreases k ((dpState_iff e _ _).mp h)⟩

theorem rootRankFamily_same_order_iff (e : FaithfulRealization X) (k l : Nat) :
    RankSameOrder (rootRankFamily e k) (rootRankFamily e l) ↔ k = l := by
  constructor
  · intro h
    have horder : SameFullOrder (Wam (k + 1) 1) (Wam (l + 1) 1) := by
      intro x y
      simpa only [rootRankFamily, Equiv.symm_apply_apply] using
        h (traceEquiv e x) (traceEquiv e y)
    have hkl := (Wam_same_full_order_iff (by decide) (by decide)).mp horder
    omega
  · rintro rfl
    exact fun _ _ => Iff.rfl

theorem dpRankFamily_same_order_iff (e : FaithfulRealization X) (k l : Nat) :
    RankSameOrder (dpRankFamily e k) (dpRankFamily e l) ↔ k = l := by
  constructor
  · intro h
    apply baseSensitiveDPFullOrderClass_injective
    apply (dpReductionPairFullOrderClass_eq_iff _ _).mpr
    intro x y
    simpa only [dpRankFamily, Equiv.symm_apply_apply] using
      h (traceEquiv e x) (traceEquiv e y)
  · rintro rfl
    exact fun _ _ => Iff.rfl

theorem rootRankOrderClass_injective (e : FaithfulRealization X) :
    Function.Injective (fun k => rankOrderClass (rootRankFamily e k)) := by
  intro k l h
  exact (rootRankFamily_same_order_iff e k l).mp ((rankOrderClass_eq_iff _ _).mp h)

theorem dpRankOrderClass_injective (e : FaithfulRealization X) :
    Function.Injective (fun k => rankOrderClass (dpRankFamily e k)) := by
  intro k l h
  exact (dpRankFamily_same_order_iff e k l).mp ((rankOrderClass_eq_iff _ _).mp h)

theorem rootRankOrderQuotient_infinite (e : FaithfulRealization X) :
    Infinite (RankOrderQuotient (RootState e)) :=
  Infinite.of_injective _ (rootRankOrderClass_injective e)

theorem dpRankOrderQuotient_infinite (e : FaithfulRealization X) :
    Infinite (RankOrderQuotient (DPState e)) :=
  Infinite.of_injective _ (dpRankOrderClass_injective e)

/-! ## Every counter-determined rank, without a method catalog -/

noncomputable def counter (e : FaithfulRealization X) (x : e.State) : Nat :=
  MetaDependencyPairs.dpRank ((traceEquiv e).symm x)

noncomputable def counterState (e : FaithfulRealization X) (n : Nat) : e.State :=
  traceEquiv e (MetaDependencyPairs.dpCounterEncoding n)

@[simp] theorem counter_counterState (e : FaithfulRealization X) (n : Nat) :
    counter e (counterState e n) = n := by
  simp only [counter, counterState, Equiv.symm_apply_apply,
    MetaDependencyPairs.dpRank_dpCounterEncoding]

theorem counter_surjective (e : FaithfulRealization X) : Function.Surjective (counter e) :=
  fun n => ⟨counterState e n, counter_counterState e n⟩

theorem counterState_succ_step (e : FaithfulRealization X) (n : Nat) :
    DPState e (counterState e (n + 1)) (counterState e n) := by
  apply (dpState_iff e _ _).mpr
  simpa only [counterState, Equiv.symm_apply_apply] using
    MetaDependencyPairs.dpCounterEncoding_succ_pairRev n

noncomputable def counterRank (e : FaithfulRealization X) : NaturalRank (DPState e) :=
  ⟨counter e, fun h => MetaDependencyPairs.dpPair_decreases ((dpState_iff e _ _).mp h)⟩

/-- The general system interface is discharged by actual represented calls. -/
noncomputable def counterSystem (e : FaithfulRealization X) : CounterSystem e.State where
  Step := DPState e
  counter := counter e
  decreases := (counterRank e).2
  state := counterState e
  counter_state := counter_counterState e
  step_succ := counterState_succ_step e

/-- The rank discards every distinction not present in the counter. -/
def CounterDetermined (e : FaithfulRealization X) (f : e.State → Nat) : Prop :=
  ∀ x y, counter e x = counter e y → f x = f y

def CounterRank (e : FaithfulRealization X) :=
  {f : NaturalRank (DPState e) // CounterDetermined e f.1}

noncomputable def canonicalCounterRank (e : FaithfulRealization X) : CounterRank e :=
  ⟨counterRank e, fun _ _ h => h⟩

noncomputable def rankRecoding (e : FaithfulRealization X) (f : CounterRank e) : Nat → Nat :=
  fun n => f.1.1 (counterState e n)

theorem rankRecoding_strictMono (e : FaithfulRealization X) (f : CounterRank e) :
    StrictMono (rankRecoding e f) := by
  exact (counterSystem e).recoding_strictMono f

theorem counterRank_factors (e : FaithfulRealization X) (f : CounterRank e) (x : e.State) :
    f.1.1 x = rankRecoding e f (counter e x) := by
  exact (counterSystem e).rank_factors f x

/-- Decrease on actual calls forces strict monotonicity; exact order agreement
is derived rather than included in the definition of a counter-determined rank. -/
theorem counterRank_same_order (e : FaithfulRealization X) (f : CounterRank e) :
    RankSameOrder f.1 (counterRank e) := by
  intro x y
  rw [counterRank_factors e f x, counterRank_factors e f y]
  exact (rankRecoding_strictMono e f).lt_iff_lt

theorem counterDetermined_iff_same_order (e : FaithfulRealization X)
    (f : NaturalRank (DPState e)) :
    CounterDetermined e f.1 ↔ RankSameOrder f (counterRank e) := by
  constructor
  · intro hf
    exact counterRank_same_order e ⟨f, hf⟩
  · intro h x y hxy
    apply Nat.le_antisymm
    · apply Nat.le_of_not_gt
      intro hlt
      have hh := (h y x).mp hlt
      change counter e y < counter e x at hh
      omega
    · apply Nat.le_of_not_gt
      intro hlt
      have hh := (h x y).mp hlt
      change counter e x < counter e y at hh
      omega

def StrictNatRecoding := {g : Nat → Nat // StrictMono g}

noncomputable def counterRankOfRecoding (e : FaithfulRealization X)
    (g : StrictNatRecoding) : CounterRank e :=
  ⟨⟨fun x => g.1 (counter e x), fun h => g.2 ((counterRank e).2 h)⟩,
    fun _ _ h => congrArg g.1 h⟩

/-- All counter-determined ranks are classified by increasing maps of Nat.
The inverse reads the rank on actual recursive calls of every counter height. -/
noncomputable def counterRanksEquivStrictNatRecoding (e : FaithfulRealization X) :
    CounterRank e ≃ StrictNatRecoding :=
  (counterSystem e).ranksEquivStrictRecoding

def counterRankOrderSetoid (e : FaithfulRealization X) : Setoid (CounterRank e) where
  r f g := RankSameOrder f.1 g.1
  iseqv := ⟨fun _ _ _ => Iff.rfl, fun h x y => (h x y).symm,
    fun h g x y => (h x y).trans (g x y)⟩

abbrev CounterRankOrderQuotient (e : FaithfulRealization X) :=
  Quotient (counterRankOrderSetoid e)

theorem all_counterRanks_same_order (e : FaithfulRealization X) (f g : CounterRank e) :
    RankSameOrder f.1 g.1 := by
  intro x y
  exact (counterRank_same_order e f x y).trans (counterRank_same_order e g x y).symm

instance counterRankOrderQuotient_subsingleton (e : FaithfulRealization X) :
    Subsingleton (CounterRankOrderQuotient e) where
  allEq q r := by
    refine Quotient.inductionOn₂ q r ?_
    intro f g
    exact Quotient.sound (all_counterRanks_same_order e f g)

noncomputable def counterRankOrderQuotientEquivPUnit (e : FaithfulRealization X) :
    CounterRankOrderQuotient e ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := Quotient.mk _ (canonicalCounterRank e)
  left_inv _ := Subsingleton.elim _ _
  right_inv x := by cases x; rfl

/-- Nonuniqueness of all admissible orders and uniqueness of the counter-only
order hold in the same realization, for its actual transformed-call relation. -/
theorem faithful_rank_classification (e : FaithfulRealization X) :
    Infinite (RankOrderQuotient (RootState e)) ∧
    Infinite (RankOrderQuotient (DPState e)) ∧
    Nonempty (CounterRank e ≃ StrictNatRecoding) ∧
    Nonempty (CounterRankOrderQuotient e ≃ PUnit) :=
  ⟨rootRankOrderQuotient_infinite e, dpRankOrderQuotient_infinite e,
    ⟨counterRanksEquivStrictNatRecoding e⟩, ⟨counterRankOrderQuotientEquivPUnit e⟩⟩

end OperatorKO7.Meta.OperationalInexpressibility.FaithfulRecursorRanks
