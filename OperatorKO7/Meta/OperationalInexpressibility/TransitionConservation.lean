import OperatorKO7.Meta.FiniteGraphReachability
import OperatorKO7.Meta.Recursor.TraceConservation
import OperatorKO7.Meta.Recursor.RaryDuplicator
import OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel

/-!
# Transition conservation on finite coordinate observations

A linear reading is constant from a selected source exactly when its coefficient
vector annihilates every transition increment reachable from that source.  The
statement is relation-generic and finite dimensional.  A finite executable
checker reports a violating reachable edge when one exists.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation

open Relation
open OperatorKO7.FiniteGraphReachability
open OperatorKO7.Meta.Recursor.TraceConservation
open OperatorKO7.Meta.Recursor.RaryDuplicator
open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem

universe u v

/-- Integer dot product on a finite coordinate family. -/
def dot {d : Nat} (c x : Fin d → Int) : Int :=
  ∑ i, c i * x i

/-- Coordinate increment from `s` to `t`. -/
def increment {S : Type u} {d : Nat} (obs : S → Fin d → Int) (s t : S) : Fin d → Int :=
  fun i => obs t i - obs s i

/-- Affine reading of a finite coordinate observation. -/
def reading {S : Type u} {d : Nat}
    (coeff : Fin d → Int) (offset : Int) (obs : S → Fin d → Int) (s : S) : Int :=
  offset + dot coeff (obs s)

/-- A one-step increment identity. -/
theorem reading_sub_eq_dot_increment
    {S : Type u} {d : Nat}
    (coeff : Fin d → Int) (offset : Int) (obs : S → Fin d → Int) (s t : S) :
    reading coeff offset obs t - reading coeff offset obs s =
      dot coeff (increment obs s t) := by
  simp only [reading, dot, increment, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Reading is constant on every state reachable from `source`. -/
def ConstantFrom {S : Type u} {d : Nat} (R : S → S → Prop) (source : S)
    (coeff : Fin d → Int) (offset : Int) (obs : S → Fin d → Int) : Prop :=
  ∀ t, ReflTransGen R source t → reading coeff offset obs t = reading coeff offset obs source

/-- Every reachable transition increment is annihilated by the coefficients. -/
def AnnihilatesReachableIncrements {S : Type u} {d : Nat}
    (R : S → S → Prop) (source : S)
    (coeff : Fin d → Int) (obs : S → Fin d → Int) : Prop :=
  ∀ s t, ReflTransGen R source s → R s t → dot coeff (increment obs s t) = 0

/-- Main conservation criterion. -/
theorem constantFrom_iff_annihilatesReachableIncrements
    {S : Type u} {d : Nat}
    (R : S → S → Prop) (source : S)
    (coeff : Fin d → Int) (offset : Int) (obs : S → Fin d → Int) :
    ConstantFrom R source coeff offset obs ↔
      AnnihilatesReachableIncrements R source coeff obs := by
  constructor
  · intro h s t hs hst
    have ht : ReflTransGen R source t := hs.tail hst
    have hreadS := h s hs
    have hreadT := h t ht
    have hzero : reading coeff offset obs t - reading coeff offset obs s = 0 := by
      rw [hreadT, hreadS]
      ring
    rw [reading_sub_eq_dot_increment] at hzero
    exact hzero
  · intro h t ht
    induction ht with
    | refl => rfl
    | @tail s t hsource hstep ih =>
        have hzero := h s t hsource hstep
        have hdiff := reading_sub_eq_dot_increment coeff offset obs s t
        rw [hzero] at hdiff
        linarith

/-- Pointwise coefficient difference. -/
def coeffDiff {d : Nat} (c₁ c₂ : Fin d → Int) : Fin d → Int :=
  fun i => c₁ i - c₂ i

/-- Difference of two affine readings is itself an affine reading. -/
theorem reading_sub_reading_eq_diff
    {S : Type u} {d : Nat}
    (c₁ c₂ : Fin d → Int) (o₁ o₂ : Int) (obs : S → Fin d → Int) (s : S) :
    reading c₁ o₁ obs s - reading c₂ o₂ obs s =
      reading (coeffDiff c₁ c₂) (o₁ - o₂) obs s := by
  simp only [reading, coeffDiff, dot, sub_mul, Finset.sum_sub_distrib]
  ring

/-- Two affine readings agree on every reachable state. -/
def ReadingsAgreeFrom {S : Type u} {d : Nat} (R : S → S → Prop) (source : S)
    (c₁ c₂ : Fin d → Int) (o₁ o₂ : Int) (obs : S → Fin d → Int) : Prop :=
  ∀ t, ReflTransGen R source t → reading c₁ o₁ obs t = reading c₂ o₂ obs t

/-- Classification of equality between two affine readings: equality at the
initial state plus annihilation of every reachable transition by the coefficient
difference. -/
theorem readingsAgreeFrom_iff_initial_and_increment_difference
    {S : Type u} {d : Nat}
    (R : S → S → Prop) (source : S)
    (c₁ c₂ : Fin d → Int) (o₁ o₂ : Int) (obs : S → Fin d → Int) :
    ReadingsAgreeFrom R source c₁ c₂ o₁ o₂ obs ↔
      reading c₁ o₁ obs source = reading c₂ o₂ obs source ∧
      AnnihilatesReachableIncrements R source (coeffDiff c₁ c₂) obs := by
  constructor
  · intro h
    have hsource := h source .refl
    refine ⟨hsource, ?_⟩
    have hconst : ConstantFrom R source (coeffDiff c₁ c₂) (o₁ - o₂) obs := by
      intro t ht
      rw [← reading_sub_reading_eq_diff c₁ c₂ o₁ o₂ obs t,
        ← reading_sub_reading_eq_diff c₁ c₂ o₁ o₂ obs source,
        h t ht, hsource]
      simp
    exact (constantFrom_iff_annihilatesReachableIncrements R source
      (coeffDiff c₁ c₂) (o₁ - o₂) obs).1 hconst
  · rintro ⟨hsource, hinc⟩
    have hconst := (constantFrom_iff_annihilatesReachableIncrements R source
      (coeffDiff c₁ c₂) (o₁ - o₂) obs).2 hinc
    intro t ht
    have heq := hconst t ht
    rw [← reading_sub_reading_eq_diff c₁ c₂ o₁ o₂ obs t,
      ← reading_sub_reading_eq_diff c₁ c₂ o₁ o₂ obs source, hsource] at heq
    linarith

section FiniteChecker

variable {S : Type u} [DecidableEq S]

/-- The supplied duplicate-free complete enumeration gives an executable
equivalence between the carrier and a universe-zero finite index type. -/
def enumerationEquiv (E : Enumeration S) : Fin E.items.length ≃ S :=
  List.Nodup.getEquivOfForallMemList E.items E.nodup E.complete

/-- Relation transported to the finite index type determined by `E`. -/
def indexedRelation (E : Enumeration S) (R : S → S → Prop) :
    Fin E.items.length → Fin E.items.length → Prop :=
  fun i j => R (enumerationEquiv E i) (enumerationEquiv E j)

instance indexedRelationDecidable (E : Enumeration S) (R : S → S → Prop)
    [DecidableRel R] : DecidableRel (indexedRelation E R) :=
  fun i j => by
    change Decidable (R (enumerationEquiv E i) (enumerationEquiv E j))
    infer_instance

/-- Reflexive transitive closure transports along any relation homomorphism. -/
theorem reflTransGen_map
    {A : Type u} {B : Type v} {R : A → A → Prop} {Q : B → B → Prop}
    (f : A → B) (hmap : ∀ {a b}, R a b → Q (f a) (f b))
    {a b : A} (h : ReflTransGen R a b) : ReflTransGen Q (f a) (f b) := by
  induction h with
  | refl => exact .refl
  | tail hab hbc ih => exact ih.tail (hmap hbc)

/-- Closure of the indexed relation is exactly closure of the original
relation, in every carrier universe. -/
theorem indexed_reflTransGen_iff
    (E : Enumeration S) (R : S → S → Prop) (source target : S) :
    ReflTransGen (indexedRelation E R)
        ((enumerationEquiv E).symm source) ((enumerationEquiv E).symm target) ↔
      ReflTransGen R source target := by
  constructor
  · intro h
    have hm := reflTransGen_map (enumerationEquiv E)
      (fun {i j} (hij : indexedRelation E R i j) => hij) h
    simpa [indexedRelation] using hm
  · intro h
    have hm := reflTransGen_map (Q := indexedRelation E R) (enumerationEquiv E).symm
      (fun {s t} (hst : R s t) => by simpa [indexedRelation] using hst) h
    simpa using hm

/-- Executable reachability through the finite index presentation. -/
def reachableFromB (E : Enumeration S) (R : S → S → Prop) [DecidableRel R]
    (source target : S) : Bool :=
  letI : DecidableRel (indexedRelation E R) := indexedRelationDecidable E R
  decide (((enumerationEquiv E).symm target) ∈
    reachIter (indexedRelation E R) ((enumerationEquiv E).symm source)
      (Fintype.card (Fin E.items.length)))

/-- The executable reachability bit is exact. -/
@[simp] theorem reachableFromB_eq_true_iff
    (E : Enumeration S) (R : S → S → Prop) [DecidableRel R]
    (source target : S) :
    reachableFromB E R source target = true ↔ ReflTransGen R source target := by
  have hindexed :
      Reachable (indexedRelation E R)
          ((enumerationEquiv E).symm source) ((enumerationEquiv E).symm target) ↔
        ReflTransGen R source target :=
    (reachable_iff_reflTransGen (R := indexedRelation E R)).trans
      (indexed_reflTransGen_iff E R source target)
  simpa only [reachableFromB, decide_eq_true_eq, Reachable] using hindexed

/-- Every ordered carrier pair, in the order induced by `E`. -/
def enumeratedPairs (E : Enumeration S) : List (S × S) :=
  E.items.flatMap fun s => E.items.map fun t => (s, t)

/-- Every carrier pair occurs in the executable pair list. -/
theorem pair_mem_enumeratedPairs (E : Enumeration S) (s t : S) :
    (s, t) ∈ enumeratedPairs E := by
  simp [enumeratedPairs, E.complete]

/-- A finite reachable edge whose increment violates conservation. -/
def IsViolatingEdge {d : Nat} (R : S → S → Prop)
    (source : S) (coeff : Fin d → Int) (obs : S → Fin d → Int) (e : S × S) : Prop :=
  ReflTransGen R source e.1 ∧ R e.1 e.2 ∧
    dot coeff (increment obs e.1 e.2) ≠ 0

/-- Executable predicate for a violating reachable edge. -/
def violatingEdgeB {d : Nat} (E : Enumeration S) (R : S → S → Prop)
    [DecidableRel R] (source : S) (coeff : Fin d → Int)
    (obs : S → Fin d → Int) (e : S × S) : Bool :=
  reachableFromB E R source e.1 && decide (R e.1 e.2) &&
    decide (dot coeff (increment obs e.1 e.2) ≠ 0)

/-- The executable edge predicate has the exact mathematical meaning. -/
@[simp] theorem violatingEdgeB_eq_true_iff {d : Nat}
    (E : Enumeration S) (R : S → S → Prop) [DecidableRel R]
    (source : S) (coeff : Fin d → Int) (obs : S → Fin d → Int)
    (e : S × S) :
    violatingEdgeB E R source coeff obs e = true ↔
      IsViolatingEdge R source coeff obs e := by
  simp [violatingEdgeB, IsViolatingEdge, reachableFromB_eq_true_iff, and_assoc]

instance isViolatingEdgeDecidable {d : Nat}
    (E : Enumeration S) (R : S → S → Prop) [DecidableRel R]
    (source : S) (coeff : Fin d → Int) (obs : S → Fin d → Int) :
    DecidablePred (IsViolatingEdge R source coeff obs) := fun e =>
  if h : violatingEdgeB E R source coeff obs e = true then
    isTrue ((violatingEdgeB_eq_true_iff E R source coeff obs e).1 h)
  else
    isFalse fun he => h ((violatingEdgeB_eq_true_iff E R source coeff obs e).2 he)

/-- Executable search for the first violating reachable edge in the finite
enumeration. -/
def failingReachableEdge? {d : Nat}
    (E : Enumeration S) (R : S → S → Prop) [DecidableRel R]
    (source : S) (coeff : Fin d → Int) (obs : S → Fin d → Int) : Option (S × S) :=
  (enumeratedPairs E).find? (violatingEdgeB E R source coeff obs)

/-- Executable conservation decision on a finite carrier. It takes no reading
offset because `conservedFromB_eq_true_iff` matches its verdict with
`ConstantFrom` at every offset. -/
def conservedFromB {d : Nat}
    (E : Enumeration S) (R : S → S → Prop) [DecidableRel R]
    (source : S) (coeff : Fin d → Int)
    (obs : S → Fin d → Int) : Bool :=
  decide (failingReachableEdge? E R source coeff obs = none)

/-- Every returned edge is a genuine reachable conservation failure. -/
theorem failingReachableEdge?_sound {d : Nat}
    (E : Enumeration S) (R : S → S → Prop) [DecidableRel R]
    (source : S) (coeff : Fin d → Int) (obs : S → Fin d → Int)
    {e : S × S}
    (h : failingReachableEdge? E R source coeff obs = some e) :
    IsViolatingEdge R source coeff obs e := by
  have he := List.find?_some h
  exact (violatingEdgeB_eq_true_iff E R source coeff obs e).1 he

/-- The checker returns no edge exactly when every reachable transition
increment is annihilated. -/
theorem failingReachableEdge?_eq_none_iff {d : Nat}
    (E : Enumeration S) (R : S → S → Prop) [DecidableRel R]
    (source : S) (coeff : Fin d → Int) (obs : S → Fin d → Int) :
    failingReachableEdge? E R source coeff obs = none ↔
      AnnihilatesReachableIncrements R source coeff obs := by
  simp only [failingReachableEdge?, List.find?_eq_none]
  constructor
  · intro h s t hs hst
    by_contra hne
    have hbad : violatingEdgeB E R source coeff obs (s, t) = true :=
      (violatingEdgeB_eq_true_iff E R source coeff obs (s, t)).2
        ⟨hs, hst, hne⟩
    exact h (s, t) (pair_mem_enumeratedPairs E s t) hbad
  · intro h e _ hbad
    have he := (violatingEdgeB_eq_true_iff E R source coeff obs e).1 hbad
    exact he.2.2 (h e.1 e.2 he.1 he.2.1)

/-- The finite Boolean checker agrees with the relation-generic conservation
criterion at every reading offset. -/
theorem conservedFromB_eq_true_iff {d : Nat}
    (E : Enumeration S) (R : S → S → Prop) [DecidableRel R]
    (source : S) (coeff : Fin d → Int) (offset : Int)
    (obs : S → Fin d → Int) :
    conservedFromB E R source coeff obs = true ↔
      ConstantFrom R source coeff offset obs := by
  simp [conservedFromB, failingReachableEdge?_eq_none_iff E,
    constantFrom_iff_annihilatesReachableIncrements]

end FiniteChecker

/-! ## Recursor specializations -/

/-- The established three-coordinate trace theorem is recovered unchanged. -/
theorem binary_trace_conservation_classification (a b c : Int) (k : Nat) :
    (k = 0 ∨ a = b + c) ↔
      ConservedAlong a b c k := by
  simpa [or_comm] using (conservedAlong_iff_zeroDepth_or_balance a b c k).symm

/-- Existing full-affine classification, re-exported on the OI surface. -/
theorem binary_full_affine_conservation_classification (a b c d : Int) :
    FullAffineConservedEverywhere a b c d ↔ a = b + c :=
  fullAffineConservedEverywhere_iff a b c d

/-- Existing trace-equivalence classification. The trace determines `a`,
`b+c`, and `b+d`; individual `b,c,d` coefficients retain the known offset
ambiguity. -/
theorem binary_trace_equivalence_classification
    (a b c d a' b' c' d' : Int) :
    TraceEquivalent a b c d a' b' c' d' ↔
      a = a' ∧ b + c = b' + c' ∧ b + d = b' + d' :=
  traceEquivalent_iff a b c d a' b' c' d'

/-- Equivalent parameterization of the same ambiguity by one integer offset. -/
theorem binary_trace_equivalence_offset_shift
    (a b c d a' b' c' d' : Int) :
    TraceEquivalent a b c d a' b' c' d' ↔
      ∃ z : Int, a' = a ∧ b' = b + z ∧ c' = c - z ∧ d' = d - z :=
  traceEquivalent_iff_offsetShift a b c d a' b' c' d'

/-- Three-coordinate affine reading along an `r`-ary live recursor orbit:
remaining counter, live payload multiplicity, and wrapper depth. -/
def raryAffineCoordinate
    (a b c : Int) (k arity i : Nat) : Int :=
  a * ((k - i : Nat) : Int) +
    b * ((arity * i + 1 : Nat) : Int) + c * (i : Int)

/-- Conservation on every live transition of a selected `r`-ary depth. -/
def RaryConservedAlong
    (a b c : Int) (k arity : Nat) : Prop :=
  ∀ i, i < k →
    raryAffineCoordinate a b c k arity (i + 1) =
      raryAffineCoordinate a b c k arity i

/-- One live stage changes an `r`-ary affine reading by `-a + r*b + c`. -/
theorem raryAffineCoordinate_step
    (a b c : Int) {k arity i : Nat} (hik : i < k) :
    raryAffineCoordinate a b c k arity (i + 1) =
      raryAffineCoordinate a b c k arity i - a + (arity : Int) * b + c := by
  have hcounter : ((k - (i + 1) : Nat) : Int) = ((k - i : Nat) : Int) - 1 := by
    omega
  unfold raryAffineCoordinate
  rw [hcounter]
  push_cast
  ring

/-- Arbitrary-arity conservation classification, including the vacuous
zero-depth case. -/
theorem raryConservedAlong_iff_zeroDepth_or_balance
    (a b c : Int) (k arity : Nat) :
    RaryConservedAlong a b c k arity ↔
      k = 0 ∨ a = (arity : Int) * b + c := by
  constructor
  · intro h
    by_cases hk : k = 0
    · exact Or.inl hk
    · right
      have h0 := h 0 (Nat.pos_of_ne_zero hk)
      rw [raryAffineCoordinate_step a b c (Nat.pos_of_ne_zero hk)] at h0
      linarith
  · rintro (rfl | hbal)
    · intro i hi
      omega
    · intro i hi
      rw [raryAffineCoordinate_step a b c hi, hbal]
      ring

/-- Additive-offset form of the arbitrary-arity reading. -/
def raryFullAffineCoordinate
    (a b c d : Int) (k arity i : Nat) : Int :=
  raryAffineCoordinate a b c k arity i + d

/-- Equality of two full affine readings on every depth and stage at one fixed
arity. -/
def RaryTraceEquivalent
    (arity : Nat) (a b c d a' b' c' d' : Int) : Prop :=
  ∀ k i, i ≤ k →
    raryFullAffineCoordinate a b c d k arity i =
      raryFullAffineCoordinate a' b' c' d' k arity i

/-- The fixed-arity trace determines three observation parameters: `a`, the
initial value `b+d`, and the live-step combination `r*b+c`. -/
theorem raryTraceEquivalent_iff
    (arity : Nat) (a b c d a' b' c' d' : Int) :
    RaryTraceEquivalent arity a b c d a' b' c' d' ↔
      a = a' ∧ b + d = b' + d' ∧
        (arity : Int) * b + c = (arity : Int) * b' + c' := by
  constructor
  · intro h
    have h00 := h 0 0 (by omega)
    have h10 := h 1 0 (by omega)
    have h11 := h 1 1 (by omega)
    norm_num [raryFullAffineCoordinate, raryAffineCoordinate] at h00 h10 h11
    constructor
    · linarith
    · constructor <;> linarith
  · rintro ⟨ha, hbd, hrc⟩ k i hik
    unfold raryFullAffineCoordinate raryAffineCoordinate
    have hi : ((i : Nat) : Int) = (i : Int) := rfl
    rw [ha]
    push_cast
    have hk : ((k - i : Nat) : Int) = (k : Int) - i := by omega
    rw [hk]
    nlinarith

/-- Equivalent coefficient descriptions differ by one integer offset in `b`,
compensated in the constant and wrapper coefficients. -/
theorem raryTraceEquivalent_iff_offsetShift
    (arity : Nat) (a b c d a' b' c' d' : Int) :
    RaryTraceEquivalent arity a b c d a' b' c' d' ↔
      ∃ z : Int, a' = a ∧ b' = b + z ∧
        c' = c - (arity : Int) * z ∧ d' = d - z := by
  rw [raryTraceEquivalent_iff]
  constructor
  · rintro ⟨ha, hbd, hrc⟩
    refine ⟨b' - b, ha.symm, by ring, ?_, ?_⟩
    · nlinarith
    · nlinarith
  · rintro ⟨z, ha, hb, hc, hd⟩
    subst a'
    subst b'
    subst c'
    subst d'
    constructor
    · rfl
    · constructor <;> ring

/-- The arbitrary-arity live recursor exposes payload multiplicity `arity*i+1`.
This is the actual execution coordinate used by the generic conservation
checker when payload multiplicity is selected as an observation. -/
theorem rary_payload_observation_is_affine
    (ia ib k arity i : Nat) (hi : i ≤ k) :
    countPayR (rOrbit (.base ia) (.pay ib) k arity i) = arity * i + 1 :=
  L10_trace_law_r ia ib k arity i hi

/-- The arbitrary-arity affine coordinate uses the payload multiplicity of the
actual live `RStep` orbit. -/
theorem raryAffineCoordinate_eq_live_payload
    (a b c : Int) (ia ib k arity i : Nat) (hi : i ≤ k) :
    raryAffineCoordinate a b c k arity i =
      a * ((k - i : Nat) : Int) +
        b * (countPayR (rOrbit (.base ia) (.pay ib) k arity i) : Int) +
        c * (i : Int) := by
  rw [rary_payload_observation_is_affine ia ib k arity i hi]
  rfl

/-- At depth zero the single observed reading retains only the payload
coefficient `b`; the `a` and `c` descriptions are unconstrained by that point. -/
theorem zero_depth_reading_eq_iff
    (a b c a' b' c' : Int) :
    affineCoordinate a b c 0 0 = affineCoordinate a' b' c' 0 0 ↔ b = b' := by
  simp [affineCoordinate, trace_ctr, trace_pay, trace_wraps]

/-- Distinct `a` and `c` coefficients with the same `b` therefore give the same
zero-depth reading. -/
theorem zero_depth_duplicate_description
    (a b c a' c' : Int) :
    affineCoordinate a b c 0 0 = affineCoordinate a' b c' 0 0 := by
  exact (zero_depth_reading_eq_iff a b c a' b c').2 rfl

/-! ## Actual three-coordinate r-ary orbit adapter -/

/-- Number of successor constructors in an `RTerm`. -/
def countSuccR : RTerm → Nat
  | .Z => 0
  | .S n => countSuccR n + 1
  | .base _ => 0
  | .pay _ => 0
  | .F x y n => countSuccR x + countSuccR y + countSuccR n
  | .G ys t => (ys.map countSuccR).sum + countSuccR t

/-- Number of emitted `G` wrappers in an `RTerm`. -/
def countWrapR : RTerm → Nat
  | .Z => 0
  | .S n => countWrapR n
  | .base _ => 0
  | .pay _ => 0
  | .F x y n => countWrapR x + countWrapR y + countWrapR n
  | .G ys t => 1 + (ys.map countWrapR).sum + countWrapR t

@[simp] theorem countSuccR_rSPow (n : Nat) : countSuccR (rSPow n) = n := by
  induction n with
  | zero => simp [rSPow, countSuccR]
  | succ n ih => simp [rSPow, countSuccR, ih]

@[simp] theorem countWrapR_rSPow (n : Nat) : countWrapR (rSPow n) = 0 := by
  induction n with
  | zero => simp [rSPow, countWrapR]
  | succ n ih => simp [rSPow, countWrapR, ih]

@[simp] theorem countSuccR_replicate_pay (ib arity : Nat) :
    ((List.replicate arity (.pay ib)).map countSuccR).sum = 0 := by
  simp [countSuccR]

@[simp] theorem countWrapR_replicate_pay (ib arity : Nat) :
    ((List.replicate arity (.pay ib)).map countWrapR).sum = 0 := by
  simp [countWrapR]

/-- Wrapper iteration does not change the remaining successor count when the
frame payload contains no successors. -/
theorem countSuccR_rGPow_pay (ib arity i : Nat) (t : RTerm) :
    countSuccR (rGPow (List.replicate arity (.pay ib)) i t) = countSuccR t := by
  induction i with
  | zero => rfl
  | succ i ih => simp [rGPow, countSuccR, ih]

/-- Each r-ary wrapper iteration adds exactly one `G` wrapper on the canonical
payload frames. -/
theorem countWrapR_rGPow_pay (ib arity i : Nat) (t : RTerm) :
    countWrapR (rGPow (List.replicate arity (.pay ib)) i t) = i + countWrapR t := by
  induction i with
  | zero => simp [rGPow]
  | succ i ih => simp [rGPow, countWrapR, ih, Nat.add_assoc, Nat.add_left_comm]

/-- The live r-ary orbit exposes the actual remaining counter. -/
theorem rary_remaining_counter_observation
    (ia ib k arity i : Nat) (hi : i ≤ k) :
    countSuccR (rOrbit (.base ia) (.pay ib) k arity i) = k - i := by
  rw [rOrbit, if_pos hi, countSuccR_rGPow_pay]
  simp [countSuccR, countSuccR_rSPow]

/-- The live r-ary orbit exposes exactly the number of emitted wrappers. -/
theorem rary_wrapper_observation
    (ia ib k arity i : Nat) (hi : i ≤ k) :
    countWrapR (rOrbit (.base ia) (.pay ib) k arity i) = i := by
  rw [rOrbit, if_pos hi, countWrapR_rGPow_pay]
  simp [countWrapR, countWrapR_rSPow]

/-- Affine reading computed from all three coordinates of the actual r-ary
execution term. -/
def actualRaryReading
    (a b c : Int) (ia ib k arity i : Nat) : Int :=
  let t := rOrbit (.base ia) (.pay ib) k arity i
  a * (countSuccR t : Int) + b * (countPayR t : Int) + c * (countWrapR t : Int)

/-- The abstract affine coordinate is exactly the reading of the three actual
execution coordinates at every live stage. -/
theorem actualRaryReading_eq_affine
    (a b c : Int) (ia ib k arity i : Nat) (hi : i ≤ k) :
    actualRaryReading a b c ia ib k arity i =
      raryAffineCoordinate a b c k arity i := by
  dsimp only [actualRaryReading, raryAffineCoordinate]
  rw [rary_remaining_counter_observation ia ib k arity i hi,
    rary_payload_observation_is_affine ia ib k arity i hi,
    rary_wrapper_observation ia ib k arity i hi]

/-- Conservation stated directly on the actual r-ary orbit. -/
def ActualRaryConservedAlong
    (a b c : Int) (ia ib k arity : Nat) : Prop :=
  ∀ i, i < k →
    actualRaryReading a b c ia ib k arity (i + 1) =
      actualRaryReading a b c ia ib k arity i

/-- Actual-orbit conservation has the same complete zero-depth/balance
classification, including arity zero. -/
theorem actualRaryConservedAlong_iff_zeroDepth_or_balance
    (a b c : Int) (ia ib k arity : Nat) :
    ActualRaryConservedAlong a b c ia ib k arity ↔
      k = 0 ∨ a = (arity : Int) * b + c := by
  constructor
  · intro h
    apply (raryConservedAlong_iff_zeroDepth_or_balance a b c k arity).1
    intro i hi
    have hi0 : i ≤ k := Nat.le_of_lt hi
    have hi1 : i + 1 ≤ k := hi
    rw [← actualRaryReading_eq_affine a b c ia ib k arity i hi0,
      ← actualRaryReading_eq_affine a b c ia ib k arity (i + 1) hi1]
    exact h i hi
  · intro h i hi
    have habs := (raryConservedAlong_iff_zeroDepth_or_balance a b c k arity).2 h i hi
    have hi0 : i ≤ k := Nat.le_of_lt hi
    have hi1 : i + 1 ≤ k := hi
    rw [actualRaryReading_eq_affine a b c ia ib k arity (i + 1) hi1,
      actualRaryReading_eq_affine a b c ia ib k arity i hi0]
    exact habs

/-- Full affine actual-orbit reading. -/
def actualRaryFullReading
    (a b c d : Int) (ia ib k arity i : Nat) : Int :=
  actualRaryReading a b c ia ib k arity i + d

/-- Equality of two full readings over every live actual r-ary orbit stage. -/
def ActualRaryTraceEquivalent
    (arity : Nat) (a b c d a' b' c' d' : Int) : Prop :=
  ∀ ia ib k i, i ≤ k →
    actualRaryFullReading a b c d ia ib k arity i =
      actualRaryFullReading a' b' c' d' ia ib k arity i

/-- The actual three-coordinate orbit recovers the existing complete
fixed-arity equality classification. -/
theorem actualRaryTraceEquivalent_iff
    (arity : Nat) (a b c d a' b' c' d' : Int) :
    ActualRaryTraceEquivalent arity a b c d a' b' c' d' ↔
      a = a' ∧ b + d = b' + d' ∧
        (arity : Int) * b + c = (arity : Int) * b' + c' := by
  rw [← raryTraceEquivalent_iff arity a b c d a' b' c' d']
  constructor
  · intro h k i hi
    have hh := h 0 0 k i hi
    dsimp only [actualRaryFullReading, raryFullAffineCoordinate] at hh ⊢
    rw [actualRaryReading_eq_affine a b c 0 0 k arity i hi,
      actualRaryReading_eq_affine a' b' c' 0 0 k arity i hi] at hh
    exact hh
  · intro h ia ib k i hi
    have hh := h k i hi
    dsimp only [actualRaryFullReading, raryFullAffineCoordinate]
    rw [actualRaryReading_eq_affine a b c ia ib k arity i hi,
      actualRaryReading_eq_affine a' b' c' ia ib k arity i hi]
    exact hh

end OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation
