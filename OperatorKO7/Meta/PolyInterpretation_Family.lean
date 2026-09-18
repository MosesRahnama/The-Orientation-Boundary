import OperatorKO7.Meta.PolyInterpretation_FullStep
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring

/-!
# An unbounded discrete family of polynomial orienters for full KO7 `Step`

Relation: `Step` (the full unguarded eight-rule root relation).
Closure: root, one step; well-foundedness of the reverse root relation.
Strategy: root-only.
Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`.

`Wa a` changes only the recursor clause of the published interpretation `W`, replacing
the additive constant `1` by a parameter `a ≥ 1`:

`Wa a (recΔ b s n) = (Wa a n + 1) * (Wa a s + Wa a b + a)`.

On the duplicating rule the margin is `Wa a b + a − 1 ≥ 1`, so every member with `a ≥ 1`
strictly orients all eight root rules.  `W` is the member `a = 1` (`Wa_one_eq_W`).  The
family is injective in `a` and no two distinct `a`-members are scalar multiples, so for
every `N` there are `N` pairwise distinct orienters of the same system. The parameter order
is exactly the pointwise order on the family, with `Wa 1 = W` its least orienting member.
The two-parameter scaling family `Wam a m = m * Wa a` is classified exactly below: positive
`m` preserves orientation and makes the literal functions distinct, but contributes no new
projective shape. Two positive-scale members are projectively equivalent exactly when their
`a` parameters agree. The full-order quotient of the actual root orienters is infinite,
whereas the quotient that observes only rewrite edges has one class on this family. Thus the
proved structure is an unbounded discrete, projectively nontrivial construction family,
without conflating scale multiplicity with geometric dimension.
-/

set_option autoImplicit false

namespace OperatorKO7.PolyInterpretation.Family

open OperatorKO7 Trace

/-- Parametric nonlinear interpretation; `a` is the recursor offset. -/
@[simp] def Wa (a : Nat) : Trace → Nat
  | void => 1
  | delta t => Wa a t + 1
  | integrate t => Wa a t + 1
  | merge x y => Wa a x + Wa a y + 1
  | app x y => Wa a x + Wa a y + 1
  | recΔ b s n => (Wa a n + 1) * (Wa a s + Wa a b + a)
  | eqW x y => Wa a x + Wa a y + 3

/-- Every value is at least one. -/
theorem Wa_pos (a : Nat) (t : Trace) : 1 ≤ Wa a t := by
  induction t with
  | void => simp [Wa]
  | delta _ ih => simp only [Wa]; omega
  | integrate _ ih => simp only [Wa]; omega
  | merge _ _ iha ihb => simp only [Wa]; omega
  | app _ _ iha ihb => simp only [Wa]; omega
  | recΔ b s n ihb ihs ihn =>
      have hn : 1 ≤ Wa a n + 1 := by omega
      have hs : 1 ≤ Wa a s + Wa a b + a := by omega
      have hmul : 1 * 1 ≤ (Wa a n + 1) * (Wa a s + Wa a b + a) := Nat.mul_le_mul hn hs
      simpa [Wa] using hmul
  | eqW _ _ iha ihb => simp only [Wa]; omega

/-- **Every member with `a ≥ 1` strictly orients every root step of full `Step`.** -/
theorem Wa_orients_step {a : Nat} (ha : 1 ≤ a) :
    ∀ {x y : Trace}, Step x y → Wa a y < Wa a x
  | _, _, Step.R_int_delta t => by
      simp only [Wa]
      omega
  | _, _, Step.R_merge_void_left t => by
      simp only [Wa]
      omega
  | _, _, Step.R_merge_void_right t => by
      simp only [Wa]
      omega
  | _, _, Step.R_merge_cancel t => by
      have ht := Wa_pos a t
      simp only [Wa]
      omega
  | _, _, Step.R_rec_zero b s => by
      have hs := Wa_pos a s
      have hb := Wa_pos a b
      simp only [Wa]
      nlinarith
  | _, _, Step.R_rec_succ b s n => by
      have hb := Wa_pos a b
      simp only [Wa]
      nlinarith
  | _, _, Step.R_eq_refl x => by
      have hx := Wa_pos a x
      simp only [Wa]
      omega
  | _, _, Step.R_eq_diff x y => by
      simp only [Wa]
      omega

/-- The reverse root relation is well founded under every member with `a ≥ 1`. -/
theorem wf_StepRev_Wa {a : Nat} (ha : 1 ≤ a) :
    WellFounded (fun x y : Trace => Step y x) := by
  have wf_measure : WellFounded (fun x y : Trace => Wa a x < Wa a y) :=
    InvImage.wf (f := Wa a) Nat.lt_wfRel.wf
  have hsub : Subrelation (fun x y : Trace => Step y x)
      (fun x y : Trace => Wa a x < Wa a y) := by
    intro x y hxy
    exact Wa_orients_step ha hxy
  exact Subrelation.wf hsub wf_measure

/-- The family is monotone in its recursor-offset parameter at every term. -/
theorem Wa_mono_parameter {a a' : Nat} (haa' : a ≤ a') (t : Trace) :
    Wa a t ≤ Wa a' t := by
  induction t with
  | void => rfl
  | delta _ ih => simp only [Wa]; omega
  | integrate _ ih => simp only [Wa]; omega
  | merge _ _ ihx ihy => simp only [Wa]; omega
  | app _ _ ihx ihy => simp only [Wa]; omega
  | recΔ b s n ihb ihs ihn =>
      simp only [Wa]
      have hleft : Wa a n + 1 ≤ Wa a' n + 1 := by omega
      have hright : Wa a s + Wa a b + a ≤ Wa a' s + Wa a' b + a' := by omega
      exact Nat.mul_le_mul hleft hright
  | eqW _ _ ihx ihy => simp only [Wa]; omega

/-- The parameter order is completely reflected by pointwise order on the family. -/
theorem Wa_parameter_le_iff_pointwise_le (a a' : Nat) :
    a ≤ a' ↔ ∀ t : Trace, Wa a t ≤ Wa a' t := by
  constructor
  · intro h t
    exact Wa_mono_parameter h t
  · intro h
    have hsep := h (recΔ void void void)
    simp only [Wa] at hsep
    omega

/-- At the separating recursor term, strict parameter growth is strict value growth. -/
theorem Wa_recΔ_void_strict {a a' : Nat} (h : a < a') :
    Wa a (recΔ void void void) < Wa a' (recΔ void void void) := by
  simp only [Wa]
  omega

/-- `Wa 1` is pointwise least among all members that satisfy the orienting condition
`1 ≤ a`. -/
theorem Wa_one_pointwise_le {a : Nat} (ha : 1 ≤ a) (t : Trace) : Wa 1 t ≤ Wa a t :=
  Wa_mono_parameter ha t

/-- The published interpretation is the member `a = 1`. -/
theorem Wa_one_eq_W (t : Trace) : Wa 1 t = W t := by
  induction t with
  | void => rfl
  | delta _ ih => simp [Wa, W, ih]
  | integrate _ ih => simp [Wa, W, ih]
  | merge _ _ iha ihb => simp [Wa, W, iha, ihb]
  | app _ _ iha ihb => simp [Wa, W, iha, ihb]
  | recΔ _ _ _ ihb ihs ihn => simp [Wa, W, ihb, ihs, ihn]
  | eqW _ _ iha ihb => simp [Wa, W, iha, ihb]

/-- The separating term: the value at `recΔ void void void` is `2 * (2 + a)`. -/
theorem Wa_recΔ_void (a : Nat) : Wa a (recΔ void void void) = 2 * (2 + a) := by
  simp [Wa]

/-- The family is injective in the parameter. -/
theorem Wa_injective : Function.Injective Wa := by
  intro a a' h
  have := congrFun h (recΔ void void void)
  rw [Wa_recΔ_void, Wa_recΔ_void] at this
  omega

/-- No member is a natural scalar multiple of a different member. -/
theorem Wa_not_proportional {a a' : Nat} (h : a ≠ a') (m : Nat) :
    (fun t => m * Wa a t) ≠ Wa a' := by
  intro heq
  have h0 := congrFun heq void
  have h1 := congrFun heq (recΔ void void void)
  simp only [Wa] at h0
  rw [Wa_recΔ_void, Wa_recΔ_void] at h1
  have hm : m = 1 := by omega
  subst hm
  omega

/-! ## Exact classification of the positive scaling family -/

/-- A positive integer rescaling of `Wa`. This is the literal two-parameter family suggested
by the licensing roadmap. -/
def Wam (a m : Nat) (t : Trace) : Nat := m * Wa a t

/-- Every positive rescaling of an orienting `Wa` remains a strict orienter of full `Step`. -/
theorem Wam_orients_step {a m : Nat} (ha : 1 ≤ a) (hm : 1 ≤ m) :
    ∀ {x y : Trace}, Step x y → Wam a m y < Wam a m x := by
  intro x y hxy
  unfold Wam
  exact Nat.mul_lt_mul_of_pos_left (Wa_orients_step ha hxy) (by omega)

/-- Exact parameter classification for root orientation. The single concrete
`R_rec_succ void void void` edge forces both the recursor offset and the scale
to be positive; those conditions are also sufficient for every root rule. -/
theorem Wam_orients_all_steps_iff (a m : Nat) :
    (∀ {x y : Trace}, Step x y → Wam a m y < Wam a m x) ↔
      1 ≤ a ∧ 1 ≤ m := by
  constructor
  · intro h
    have hrec := h (Step.R_rec_succ void void void)
    have hm : 1 ≤ m := by
      by_contra hm0
      have : m = 0 := by omega
      subst m
      simp [Wam] at hrec
    have ha : 1 ≤ a := by
      by_contra ha0
      have : a = 0 := by omega
      subst a
      simp [Wam, Wa] at hrec
    exact ⟨ha, hm⟩
  · rintro ⟨ha, hm⟩
    exact Wam_orients_step ha hm

/-- At positive scale, the literal `Wam` functions remember both parameters exactly. -/
theorem Wam_eq_iff {a a' m m' : Nat} (hm : 1 ≤ m) :
    Wam a m = Wam a' m' ↔ a = a' ∧ m = m' := by
  constructor
  · intro h
    have h0 := congrFun h void
    have h1 := congrFun h (recΔ void void void)
    simp only [Wam, Wa, Nat.mul_one] at h0
    simp only [Wam, Wa] at h1
    have hmm : m = m' := h0
    subst m'
    have hfactor : 2 * (2 + a) = 2 * (2 + a') :=
      Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) h1
    exact ⟨by omega, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Projective equivalence over natural-valued interpretations: positive integer rescalings
of the two functions agree pointwise. -/
def NatProjectivelyEquivalent (f g : Trace → Nat) : Prop :=
  ∃ k l : Nat, 1 ≤ k ∧ 1 ≤ l ∧ ∀ t, k * f t = l * g t

/-- **Exact projective classification.** Positive-scale `Wam` members are projectively
equivalent exactly when they have the same recursor-offset parameter `a`. Consequently the
scale parameter `m` produces new literal functions but no new projective orienter class. -/
theorem Wam_projectivelyEquivalent_iff {a a' m m' : Nat} (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    NatProjectivelyEquivalent (Wam a m) (Wam a' m') ↔ a = a' := by
  constructor
  · rintro ⟨k, l, hk, hl, h⟩
    have h0 := h void
    have h1 := h (recΔ void void void)
    simp only [Wam, Wa, Nat.mul_one] at h0
    simp only [Wam, Wa] at h1
    have h1' : (k * m) * (2 * (2 + a)) = (l * m') * (2 * (2 + a')) := by
      simpa [Nat.mul_assoc] using h1
    rw [h0] at h1'
    have hfactor : 2 * (2 + a) = 2 * (2 + a') :=
      Nat.eq_of_mul_eq_mul_left (by positivity : 0 < l * m') h1'
    omega
  · intro haa
    subst a'
    refine ⟨m', m, hm', hm, ?_⟩
    intro t
    simp only [Wam]
    ac_rfl

/-- Different recursor offsets are never projectively equivalent, at any positive scales. -/
theorem Wam_not_projectivelyEquivalent_of_ne {a a' m m' : Nat}
    (hm : 1 ≤ m) (hm' : 1 ≤ m') (haa' : a ≠ a') :
    ¬ NatProjectivelyEquivalent (Wam a m) (Wam a' m') := by
  intro h
  exact haa' ((Wam_projectivelyEquivalent_iff hm hm').1 h)

/-- **Unbounded discrete construction family.** For every `N` there is an injective
`N`-indexed family of Nat-valued interpretations, each strictly orienting every root step
of full `Step`. Together with `Wa_not_proportional`, this proves unbounded multiplicity
without conflating discrete cardinal growth with geometric dimension. -/
theorem w1_orienting_family (N : Nat) :
    ∃ f : Fin N → (Trace → Nat),
      Function.Injective f ∧
        ∀ i : Fin N, ∀ {x y : Trace}, Step x y → f i y < f i x := by
  refine ⟨fun i => Wa (i.val + 1), ?_, ?_⟩
  · intro i j hij
    have h := Wa_injective hij
    exact Fin.ext (by omega)
  · intro i x y hxy
    exact Wa_orients_step (by omega) hxy

/-- Non-vacuity at `N = 2`: two distinct orienters, neither a multiple of the other. -/
theorem two_nonproportional_orienters :
    Wa 1 ≠ Wa 2 ∧ (∀ m : Nat, (fun t => m * Wa 1 t) ≠ Wa 2) ∧
      (∀ {x y : Trace}, Step x y → Wa 1 y < Wa 1 x) ∧
        (∀ {x y : Trace}, Step x y → Wa 2 y < Wa 2 x) :=
  ⟨fun h => by have := Wa_injective h; omega,
    fun m => Wa_not_proportional (by omega) m,
    fun h => Wa_orients_step (by omega) h,
    fun h => Wa_orients_step (by omega) h⟩

/-! ## Exact quotient by the induced strict order -/

/-- Two rankings induce the same strict comparison on every pair of terms. -/
def SameFullOrder (f g : Trace → Nat) : Prop :=
  ∀ x y, f x < f y ↔ g x < g y

theorem sameFullOrder_refl (f : Trace → Nat) : SameFullOrder f f :=
  fun _ _ => Iff.rfl

theorem sameFullOrder_symm {f g : Trace → Nat} (h : SameFullOrder f g) :
    SameFullOrder g f :=
  fun x y => (h x y).symm

theorem sameFullOrder_trans {f g h : Trace → Nat}
    (hfg : SameFullOrder f g) (hgh : SameFullOrder g h) : SameFullOrder f h :=
  fun x y => (hfg x y).trans (hgh x y)

/-- Quotient of Nat-valued rankings by their complete induced strict order. -/
def fullOrderSetoid : Setoid (Trace → Nat) where
  r := SameFullOrder
  iseqv := ⟨sameFullOrder_refl, sameFullOrder_symm, sameFullOrder_trans⟩

abbrev FullOrderQuotient := Quotient fullOrderSetoid

def fullOrderClass (f : Trace → Nat) : FullOrderQuotient :=
  Quotient.mk fullOrderSetoid f

theorem fullOrderClass_eq_iff (f g : Trace → Nat) :
    fullOrderClass f = fullOrderClass g ↔ SameFullOrder f g := by
  exact Quotient.eq_iff_equiv

/-- Iterating `delta` adds exactly the iteration count to every `Wa` value. -/
theorem Wa_delta_iterate (a n : Nat) (t : Trace) :
    Wa a ((delta^[n]) t) = Wa a t + n := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply', Wa, ih]
      omega

theorem Wa_delta_iterate_void (a n : Nat) :
    Wa a ((delta^[n]) void) = n + 1 := by
  rw [Wa_delta_iterate]
  simp only [Wa]
  omega

/-- If `a < a'`, one explicit pair is ordered in opposite directions by `Wa a`
and `Wa a'`. -/
theorem Wa_full_order_separating_pair {a a' : Nat} (haa' : a < a') :
    let t := recΔ void void void
    let u := (delta^[2 * a + 4]) void
    Wa a t < Wa a u ∧ Wa a' u < Wa a' t := by
  dsimp only
  rw [Wa_recΔ_void, Wa_delta_iterate_void, Wa_delta_iterate_void,
    Wa_recΔ_void]
  omega

/-- Positive rescaling preserves the separating pair. -/
theorem Wam_full_order_separating_pair {a a' m m' : Nat}
    (haa' : a < a') (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    let t := recΔ void void void
    let u := (delta^[2 * a + 4]) void
    Wam a m t < Wam a m u ∧ Wam a' m' u < Wam a' m' t := by
  obtain ⟨hleft, hright⟩ := Wa_full_order_separating_pair haa'
  exact ⟨Nat.mul_lt_mul_of_pos_left hleft (by omega),
    Nat.mul_lt_mul_of_pos_left hright (by omega)⟩

/-- Positive-scale members induce the same full order exactly when their recursor
offsets agree. Scale contributes no full-order class. -/
theorem Wam_same_full_order_iff {a a' m m' : Nat} (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    SameFullOrder (Wam a m) (Wam a' m') ↔ a = a' := by
  constructor
  · intro horder
    rcases lt_trichotomy a a' with haa' | haa' | haa'
    · obtain ⟨hsmall, hlarge⟩ := Wam_full_order_separating_pair haa' hm hm'
      have := (horder _ _).mp hsmall
      omega
    · exact haa'
    · obtain ⟨hsmall, hlarge⟩ := Wam_full_order_separating_pair haa' hm' hm
      have := (horder _ _).mpr hsmall
      omega
  · rintro rfl
    intro x y
    change m * Wa a x < m * Wa a y ↔ m' * Wa a x < m' * Wa a y
    rw [Nat.mul_lt_mul_left (by omega), Nat.mul_lt_mul_left (by omega)]

/-- The full-order quotient contains an injective Nat-indexed family. -/
def WamFullOrderClass (a : Nat) : FullOrderQuotient :=
  fullOrderClass (Wam a 1)

theorem WamFullOrderClass_injective : Function.Injective WamFullOrderClass := by
  intro a a' h
  exact (Wam_same_full_order_iff (by decide) (by decide)).mp
    ((fullOrderClass_eq_iff _ _).mp h)

theorem fullOrderQuotient_infinite : Infinite FullOrderQuotient :=
  Infinite.of_injective WamFullOrderClass WamFullOrderClass_injective

/-! ## The full-order quotient of actual root orienters -/

/-- Nat-valued functions that strictly orient every root edge of the full
unguarded eight-rule relation. -/
def RootOrienter :=
  { f : Trace → Nat // ∀ {x y : Trace}, Step x y → f y < f x }

/-- Full-order equivalence restricted to actual root orienters. -/
def SameRootOrienterFullOrder (f g : RootOrienter) : Prop :=
  SameFullOrder f.1 g.1

theorem sameRootOrienterFullOrder_refl (f : RootOrienter) :
    SameRootOrienterFullOrder f f :=
  sameFullOrder_refl f.1

theorem sameRootOrienterFullOrder_symm {f g : RootOrienter}
    (h : SameRootOrienterFullOrder f g) : SameRootOrienterFullOrder g f :=
  sameFullOrder_symm h

theorem sameRootOrienterFullOrder_trans {f g h : RootOrienter}
    (hfg : SameRootOrienterFullOrder f g)
    (hgh : SameRootOrienterFullOrder g h) : SameRootOrienterFullOrder f h :=
  sameFullOrder_trans hfg hgh

def rootOrienterFullOrderSetoid : Setoid RootOrienter where
  r := SameRootOrienterFullOrder
  iseqv := ⟨sameRootOrienterFullOrder_refl, sameRootOrienterFullOrder_symm,
    sameRootOrienterFullOrder_trans⟩

abbrev RootOrienterFullOrderQuotient := Quotient rootOrienterFullOrderSetoid

def rootOrienterFullOrderClass (f : RootOrienter) :
    RootOrienterFullOrderQuotient :=
  Quotient.mk rootOrienterFullOrderSetoid f

theorem rootOrienterFullOrderClass_eq_iff (f g : RootOrienter) :
    rootOrienterFullOrderClass f = rootOrienterFullOrderClass g ↔
      SameRootOrienterFullOrder f g := by
  exact Quotient.eq_iff_equiv

/-- The positive-offset, unit-scale member at index `a`. -/
def WamRootOrienter (a : Nat) : RootOrienter :=
  ⟨Wam (a + 1) 1, Wam_orients_step (by omega) (by decide)⟩

def WamRootOrienterClass (a : Nat) : RootOrienterFullOrderQuotient :=
  rootOrienterFullOrderClass (WamRootOrienter a)

theorem WamRootOrienterClass_injective : Function.Injective WamRootOrienterClass := by
  intro a a' h
  have horder : SameFullOrder (Wam (a + 1) 1) (Wam (a' + 1) 1) :=
    (rootOrienterFullOrderClass_eq_iff _ _).mp h
  have haa : a + 1 = a' + 1 :=
    (Wam_same_full_order_iff (by decide) (by decide)).mp horder
  omega

/-- There are infinitely many inequivalent full strict orders among functions
that actually orient every root edge of `Step`. -/
theorem rootOrienterFullOrderQuotient_infinite :
    Infinite RootOrienterFullOrderQuotient :=
  Infinite.of_injective WamRootOrienterClass WamRootOrienterClass_injective

/-- A recoding is strict when one strict monotone Nat map recovers the second
ranking from the first on every term. -/
def StrictlyRecodes (f g : Trace → Nat) : Prop :=
  ∃ e : Nat → Nat, StrictMono e ∧ ∀ t, g t = e (f t)

theorem strictlyRecodes_sameFullOrder {f g : Trace → Nat}
    (h : StrictlyRecodes f g) : SameFullOrder f g := by
  rcases h with ⟨e, he, hfg⟩
  intro x y
  rw [hfg x, hfg y]
  exact he.lt_iff_lt.symm

/-- Distinct recursor offsets cannot be related by a strict monotone recoding in
either direction. -/
theorem Wam_not_strictlyRecodes_of_ne {a a' m m' : Nat}
    (hm : 1 ≤ m) (hm' : 1 ≤ m') (haa' : a ≠ a') :
    ¬ StrictlyRecodes (Wam a m) (Wam a' m') ∧
      ¬ StrictlyRecodes (Wam a' m') (Wam a m) := by
  constructor
  · intro h
    exact haa' ((Wam_same_full_order_iff hm hm').mp
      (strictlyRecodes_sameFullOrder h))
  · intro h
    exact haa' ((Wam_same_full_order_iff hm hm').mp
      (sameFullOrder_symm (strictlyRecodes_sameFullOrder h)))

/-- Two rankings agree on the rewrite-edge order when they make the same strict
comparison on every actual root step. -/
def SameStepOrder (f g : Trace → Nat) : Prop :=
  ∀ {x y}, Step x y → (f y < f x ↔ g y < g x)

theorem sameStepOrder_refl (f : Trace → Nat) : SameStepOrder f f :=
  fun _ => Iff.rfl

theorem sameStepOrder_symm {f g : Trace → Nat} (h : SameStepOrder f g) :
    SameStepOrder g f :=
  fun hxy => (h hxy).symm

theorem sameStepOrder_trans {f g h : Trace → Nat}
    (hfg : SameStepOrder f g) (hgh : SameStepOrder g h) : SameStepOrder f h :=
  fun hxy => (hfg hxy).trans (hgh hxy)

def stepOrderSetoid : Setoid (Trace → Nat) where
  r := SameStepOrder
  iseqv := ⟨sameStepOrder_refl, sameStepOrder_symm, sameStepOrder_trans⟩

abbrev StepOrderQuotient := Quotient stepOrderSetoid

def stepOrderClass (f : Trace → Nat) : StepOrderQuotient :=
  Quotient.mk stepOrderSetoid f

theorem stepOrderClass_eq_iff (f g : Trace → Nat) :
    stepOrderClass f = stepOrderClass g ↔ SameStepOrder f g := by
  exact Quotient.eq_iff_equiv

/-- All orienting members occupy one rewrite-edge-order class. -/
theorem Wam_same_step_order {a a' m m' : Nat}
    (ha : 1 ≤ a) (ha' : 1 ≤ a') (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    SameStepOrder (Wam a m) (Wam a' m') := by
  intro x y hxy
  exact iff_of_true (Wam_orients_step ha hm hxy) (Wam_orients_step ha' hm' hxy)

theorem Wam_stepOrderClass_eq {a a' m m' : Nat}
    (ha : 1 ≤ a) (ha' : 1 ≤ a') (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    stepOrderClass (Wam a m) = stepOrderClass (Wam a' m') :=
  (stepOrderClass_eq_iff _ _).mpr (Wam_same_step_order ha ha' hm hm')

end OperatorKO7.PolyInterpretation.Family
