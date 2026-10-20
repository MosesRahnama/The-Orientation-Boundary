import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Monotone.Basic

/-!
# Counter-only and invariant-sensitive ranks for arbitrary relations

The source type and transition relation are arbitrary. A counter system has a
decreasing counter and actual transitions realizing every adjacent natural
countdown. Its counter-only ranks are precisely increasing recodings of that
counter. Independently variable invariant coordinates give infinitely many
admissible full orders. No recursor syntax or KO7 relation is imported.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting.RankOrderClassification

universe u

def NaturalRank {A : Type u} (R : A → A → Prop) :=
  {f : A → Nat // ∀ {x y}, R x y → f y < f x}

def RankSameOrder {A : Type u} {R : A → A → Prop}
    (f g : NaturalRank R) : Prop :=
  ∀ x y, f.1 x < f.1 y ↔ g.1 x < g.1 y

def rankOrderSetoid {A : Type u} (R : A → A → Prop) : Setoid (NaturalRank R) where
  r := RankSameOrder
  iseqv := ⟨fun _ _ _ => Iff.rfl, fun h x y => (h x y).symm,
    fun h g x y => (h x y).trans (g x y)⟩

abbrev RankOrderQuotient {A : Type u} (R : A → A → Prop) :=
  Quotient (rankOrderSetoid R)

def rankOrderClass {A : Type u} {R : A → A → Prop}
    (f : NaturalRank R) : RankOrderQuotient R := Quotient.mk _ f

theorem rankOrderClass_eq_iff {A : Type u} {R : A → A → Prop}
    (f g : NaturalRank R) : rankOrderClass f = rankOrderClass g ↔ RankSameOrder f g :=
  Quotient.eq_iff_equiv

/-- The fields specify actual counter values and actual transitions. Neither
rank uniqueness nor comparison between arbitrary states is assumed. -/
structure CounterSystem (A : Type u) where
  Step : A → A → Prop
  counter : A → Nat
  decreases : ∀ {x y}, Step x y → counter y < counter x
  state : Nat → A
  counter_state : ∀ n, counter (state n) = n
  step_succ : ∀ n, Step (state (n + 1)) (state n)

namespace CounterSystem

variable {A : Type u} (C : CounterSystem A)

def rank : NaturalRank C.Step := ⟨C.counter, C.decreases⟩

def FiberConstant (f : A → Nat) : Prop :=
  ∀ x y, C.counter x = C.counter y → f x = f y

def CounterRank := {f : NaturalRank C.Step // C.FiberConstant f.1}

def canonicalRank : C.CounterRank := ⟨C.rank, fun _ _ h => h⟩

def recoding (f : C.CounterRank) : Nat → Nat := fun n => f.1.1 (C.state n)

theorem recoding_strictMono (f : C.CounterRank) : StrictMono (C.recoding f) :=
  strictMono_nat_of_lt_succ fun n => f.1.2 (C.step_succ n)

theorem rank_factors (f : C.CounterRank) (x : A) :
    f.1.1 x = C.recoding f (C.counter x) :=
  f.2 x (C.state (C.counter x)) (C.counter_state _).symm

theorem counterRank_same_order (f : C.CounterRank) : RankSameOrder f.1 C.rank := by
  intro x y
  rw [C.rank_factors f x, C.rank_factors f y]
  exact (C.recoding_strictMono f).lt_iff_lt

theorem fiberConstant_iff_same_order (f : NaturalRank C.Step) :
    C.FiberConstant f.1 ↔ RankSameOrder f C.rank := by
  constructor
  · intro hf
    exact C.counterRank_same_order ⟨f, hf⟩
  · intro h x y hxy
    apply Nat.le_antisymm
    · apply Nat.le_of_not_gt
      intro hlt
      have hh := (h y x).mp hlt
      change C.counter y < C.counter x at hh
      omega
    · apply Nat.le_of_not_gt
      intro hlt
      have hh := (h x y).mp hlt
      change C.counter x < C.counter y at hh
      omega

def StrictRecoding := {g : Nat → Nat // StrictMono g}

def rankOfRecoding (g : StrictRecoding) : C.CounterRank :=
  ⟨⟨fun x => g.1 (C.counter x), fun h => g.2 (C.decreases h)⟩,
    fun _ _ h => congrArg g.1 h⟩

def ranksEquivStrictRecoding : C.CounterRank ≃ StrictRecoding where
  toFun f := ⟨C.recoding f, C.recoding_strictMono f⟩
  invFun := C.rankOfRecoding
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact (C.rank_factors f x).symm
  right_inv g := by
    apply Subtype.ext
    funext n
    change g.1 (C.counter (C.state n)) = g.1 n
    rw [C.counter_state]

/-- An arbitrary recoding decreases on every actual edge iff it is strictly
increasing. The reverse implication uses the concrete countdown transitions. -/
theorem recoding_decreases_iff (g : Nat → Nat) :
    (∀ {x y}, C.Step x y → g (C.counter y) < g (C.counter x)) ↔ StrictMono g := by
  constructor
  · intro hg
    apply strictMono_nat_of_lt_succ
    intro n
    simpa only [C.counter_state] using hg (C.step_succ n)
  · intro hg x y h
    exact hg (C.decreases h)

def orderSetoid : Setoid C.CounterRank where
  r f g := RankSameOrder f.1 g.1
  iseqv := ⟨fun _ _ _ => Iff.rfl, fun h x y => (h x y).symm,
    fun h g x y => (h x y).trans (g x y)⟩

abbrev OrderQuotient := Quotient C.orderSetoid

theorem all_counterRanks_same_order (f g : C.CounterRank) : RankSameOrder f.1 g.1 :=
  fun x y => (C.counterRank_same_order f x y).trans (C.counterRank_same_order g x y).symm

instance orderQuotient_subsingleton : Subsingleton C.OrderQuotient where
  allEq q r := by
    refine Quotient.inductionOn₂ q r ?_
    intro f g
    exact Quotient.sound (C.all_counterRanks_same_order f g)

def orderQuotientEquivPUnit : C.OrderQuotient ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := Quotient.mk _ C.canonicalRank
  left_inv _ := Subsingleton.elim _ _
  right_inv x := by cases x; rfl

theorem counter_order_classification :
    Nonempty (C.CounterRank ≃ StrictRecoding) ∧
      Nonempty (C.OrderQuotient ≃ PUnit) ∧
      ∀ f : NaturalRank C.Step, C.FiberConstant f.1 ↔ RankSameOrder f C.rank :=
  ⟨⟨C.ranksEquivStrictRecoding⟩, ⟨C.orderQuotientEquivPUnit⟩,
    C.fiberConstant_iff_same_order⟩

end CounterSystem

/-! ## Arbitrary systems with an independently variable invariant coordinate -/

variable {A : Type u} {R : A → A → Prop}

/-- Adding a multiple of an edge-invariant coordinate preserves strict decrease. -/
def rankWithInvariant (f : NaturalRank R) (b : A → Nat)
    (hb : ∀ {x y}, R x y → b x = b y) (k : Nat) : NaturalRank R :=
  ⟨fun x => f.1 x + k * b x, by
    intro x y h
    have hd := f.2 h
    change f.1 y + k * b y < f.1 x + k * b x
    rw [hb h]
    exact Nat.add_lt_add_right hd _⟩

theorem invariant_ranks_separate (f : NaturalRank R) (b : A → Nat)
    (hb : ∀ {x y}, R x y → b x = b y)
    (hjoint : Function.Surjective (fun x => (f.1 x, b x))) {k l : Nat} (hkl : k < l) :
    ¬ RankSameOrder (rankWithInvariant f b hb k) (rankWithInvariant f b hb l) := by
  obtain ⟨x, hx⟩ := hjoint (0, 1)
  obtain ⟨y, hy⟩ := hjoint (k + 1, 0)
  have hfx := congrArg Prod.fst hx
  have hbx := congrArg Prod.snd hx
  have hfy := congrArg Prod.fst hy
  have hby := congrArg Prod.snd hy
  dsimp only at hfx hbx hfy hby
  intro h
  have hxy := h x y
  simp only [rankWithInvariant, hfx, hbx, hfy, hby, Nat.mul_one,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero] at hxy
  have hh := hxy.mp (Nat.lt_succ_self k)
  omega

theorem invariant_rank_classes_injective (f : NaturalRank R) (b : A → Nat)
    (hb : ∀ {x y}, R x y → b x = b y)
    (hjoint : Function.Surjective (fun x => (f.1 x, b x))) :
    Function.Injective (fun k => rankOrderClass (rankWithInvariant f b hb k)) := by
  intro k l h
  have ho := (rankOrderClass_eq_iff _ _).mp h
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · exact False.elim (invariant_ranks_separate f b hb hjoint hkl ho)
  · exact hkl
  · exact False.elim (invariant_ranks_separate f b hb hjoint hlk
      (fun x y => (ho x y).symm))

/-- Full independence of the two coordinates is unnecessary: one positive
invariant value and every rank value on the zero-invariant fiber suffice. -/
theorem rankOrderQuotient_infinite_of_axis_witnesses
    (f : NaturalRank R) (b : A → Nat)
    (hb : ∀ {x y}, R x y → b x = b y)
    (hpositive : ∃ x, 0 < b x)
    (hzero : ∀ n, ∃ y, f.1 y = n ∧ b y = 0) :
    Infinite (RankOrderQuotient R) := by
  obtain ⟨x, hbx⟩ := hpositive
  have separates : ∀ {k l : Nat}, k < l →
      ¬ RankSameOrder (rankWithInvariant f b hb k) (rankWithInvariant f b hb l) := by
    intro k l hkl horder
    obtain ⟨y, hfy, hby⟩ := hzero (f.1 x + k * b x + 1)
    have hmul := Nat.mul_lt_mul_of_pos_right hkl hbx
    have hsmall : (rankWithInvariant f b hb k).1 x <
        (rankWithInvariant f b hb k).1 y := by
      simp only [rankWithInvariant, hfy, hby, Nat.mul_zero, Nat.add_zero]
      omega
    have hlarge := (horder x y).mp hsmall
    simp only [rankWithInvariant, hfy, hby, Nat.mul_zero, Nat.add_zero] at hlarge
    omega
  apply Infinite.of_injective (fun k => rankOrderClass (rankWithInvariant f b hb k))
  intro k l h
  have horder := (rankOrderClass_eq_iff _ _).mp h
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · exact False.elim (separates hkl horder)
  · exact hkl
  · exact False.elim (separates hlk (fun x y => (horder x y).symm))

theorem rankOrderQuotient_infinite_of_independent_invariant
    (f : NaturalRank R) (b : A → Nat)
    (hb : ∀ {x y}, R x y → b x = b y)
    (hjoint : Function.Surjective (fun x => (f.1 x, b x))) :
    Infinite (RankOrderQuotient R) := by
  apply rankOrderQuotient_infinite_of_axis_witnesses f b hb
  · obtain ⟨x, hx⟩ := hjoint (0, 1)
    have hh := congrArg Prod.snd hx
    exact ⟨x, by dsimp only at hh; omega⟩
  · intro n
    obtain ⟨y, hy⟩ := hjoint (n, 0)
    exact ⟨y, congrArg Prod.fst hy, congrArg Prod.snd hy⟩

/-! ## An inhabited non-recursor system and a missing-transition counterexample -/

def productCountdown : CounterSystem (Nat × Nat) where
  Step x y := x.1 = y.1 + 1 ∧ x.2 = y.2
  counter := Prod.fst
  decreases := by intro x y h; omega
  state n := (n, 0)
  counter_state _ := rfl
  step_succ _ := ⟨rfl, rfl⟩

theorem productCountdown_all_order_quotient_infinite :
    Infinite (RankOrderQuotient productCountdown.Step) :=
  rankOrderQuotient_infinite_of_independent_invariant productCountdown.rank
    Prod.snd (fun h => h.2) (fun x => ⟨x, rfl⟩)

theorem productCountdown_counter_order_unique :
    Nonempty (productCountdown.OrderQuotient ≃ PUnit) :=
  ⟨productCountdown.orderQuotientEquivPUnit⟩

/-- Soundness alone does not compare states between which no step is required. -/
def emptyBoolRank (reverse : Bool) : NaturalRank (fun _ _ : Bool => False) :=
  ⟨fun x => if x = reverse then 0 else 1, fun h => False.elim h⟩

theorem empty_relation_has_distinct_orders :
    ¬ RankSameOrder (emptyBoolRank false) (emptyBoolRank true) := by
  intro h
  have hh := h false true
  simp [emptyBoolRank] at hh

end OperatorKO7.Meta.Rewriting.RankOrderClassification
