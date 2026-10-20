import Mathlib.Tactic

/-!
# Observer-relative well-founded rankings

The relation seen through an observer is defined by attained source transitions.
A ranking through that observer exists in an arbitrary well-founded target only
if the reverse observed relation is well-founded. Conversely the observed
carrier itself supplies a target whenever that reverse relation is well-founded.
Natural-valued ranks impose the stronger condition that every finite path from a
state has a uniform natural bound.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.ObserverRanks

universe u v w x

/-- A transition between observer values is attained by one source transition. -/
def ObservedStep {A : Type u} {B : Type v}
    (R : A → A → Prop) (q : A → B) (b c : B) : Prop :=
  ∃ x y, R x y ∧ q x = b ∧ q y = c

/-- Reverse observed relation, the orientation used for well-foundedness. -/
def ObservedRev {A : Type u} {B : Type v}
    (R : A → A → Prop) (q : A → B) (c b : B) : Prop :=
  ObservedStep R q b c

/-- A rank on observer values into an arbitrary target relation. -/
def FactoredRank {A : Type u} {B : Type v} {C : Type w}
    (R : A → A → Prop) (q : A → B)
    (lt : C → C → Prop) (rank : B → C) : Prop :=
  ∀ {x y}, R x y → lt (rank (q y)) (rank (q x))

/-- A factored rank decreases on every attained observer transition. -/
theorem factoredRank_observed
    {A : Type u} {B : Type v} {C : Type w}
    {R : A → A → Prop} {q : A → B}
    {lt : C → C → Prop} {rank : B → C}
    (h : FactoredRank R q lt rank) :
    ∀ {b c}, ObservedStep R q b c → lt (rank c) (rank b) := by
  rintro b c ⟨x, y, hxy, rfl, rfl⟩
  exact h hxy

/-- Any observer-factored rank into a well-founded relation proves that the
reverse observed relation is well-founded. -/
theorem observedRev_wellFounded_of_factoredRank
    {A : Type u} {B : Type v} {C : Type w}
    {R : A → A → Prop} {q : A → B}
    {lt : C → C → Prop} {rank : B → C}
    (hlt : WellFounded lt) (h : FactoredRank R q lt rank) :
    WellFounded (ObservedRev R q) := by
  apply Subrelation.wf
    (r := InvImage lt rank)
  · intro c b hcb
    rcases hcb with ⟨x, y, hxy, hqx, hqy⟩
    have hd := h hxy
    rw [hqx, hqy] at hd
    exact hd
  · exact InvImage.wf rank hlt

/-- If the reverse observed relation is well-founded, the identity map on the
observer carrier is already a factored rank. -/
theorem identity_factoredRank_of_observedRev_wellFounded
    {A : Type u} {B : Type v}
    {R : A → A → Prop} {q : A → B}
    (_h : WellFounded (ObservedRev R q)) :
    FactoredRank R q (ObservedRev R q) id := by
  intro x y hxy
  exact ⟨x, y, hxy, rfl, rfl⟩

/-- Observer-rank existence can therefore be tested on the observed carrier
itself. -/
theorem observedRev_wellFounded_iff_identity_rank
    {A : Type u} {B : Type v}
    {R : A → A → Prop} {q : A → B} :
    WellFounded (ObservedRev R q) ↔
      WellFounded (ObservedRev R q) ∧
        FactoredRank R q (ObservedRev R q) id := by
  constructor
  · intro h
    exact ⟨h, identity_factoredRank_of_observedRev_wellFounded h⟩
  · exact And.left

/-- A factorization through a coarser observer is also a factorization through
any finer observer from which the coarser one is computed. -/
theorem factoredRank_refines
    {A : Type u} {Fine : Type v} {Coarse : Type w} {C : Type x}
    {R : A → A → Prop}
    (qFine : A → Fine) (qCoarse : A → Coarse) (collapse : Fine → Coarse)
    (hfactor : ∀ x, qCoarse x = collapse (qFine x))
    (lt : C → C → Prop) (rank : Coarse → C)
    (h : FactoredRank R qCoarse lt rank) :
    FactoredRank R qFine lt (rank ∘ collapse) := by
  intro x y hxy
  change lt (rank (collapse (qFine y))) (rank (collapse (qFine x)))
  rw [← hfactor y, ← hfactor x]
  exact h hxy

/-- Exact-length paths for relation-level height arguments. -/
inductive Steps {A : Type u} (R : A → A → Prop) : Nat → A → A → Prop where
  | refl (x : A) : Steps R 0 x x
  | cons {n : Nat} {x y z : A} : R x y → Steps R n y z → Steps R (n + 1) x z

/-- A natural-valued rank strictly decreasing on source transitions. -/
structure NatRank {A : Type u} (R : A → A → Prop) where
  rank : A → Nat
  decreases : ∀ {x y}, R x y → rank y < rank x

/-- Every natural rank bounds the length of every finite path from its source. -/
theorem NatRank.bounds_steps
    {A : Type u} {R : A → A → Prop} (r : NatRank R)
    {n : Nat} {x y : A} (h : Steps R n x y) :
    r.rank y + n ≤ r.rank x := by
  induction h with
  | refl x => simp
  | cons hxy hrest ih =>
      have hd := r.decreases hxy
      omega

/-- A natural rank on observer values is an ordinary natural rank of the
attained observed relation. -/
def NatFactoredRank {A : Type u} {B : Type v}
    (R : A → A → Prop) (q : A → B) :=
  NatRank (ObservedStep R q)

/-- A natural observer rank supplies a local finite path bound at every observer
value. -/
theorem natFactoredRank_bounds_observed_paths
    {A : Type u} {B : Type v} {R : A → A → Prop} {q : A → B}
    (r : NatFactoredRank R q) {n : Nat} {b c : B}
    (h : Steps (ObservedStep R q) n b c) :
    r.rank c + n ≤ r.rank b :=
  r.bounds_steps h

/-- A rank on observer values can be pulled back to the source states. -/
def pullbackNatRank
    {A : Type u} {B : Type v} {R : A → A → Prop} {q : A → B}
    (r : NatFactoredRank R q) : NatRank R where
  rank := r.rank ∘ q
  decreases := by
    intro x y hxy
    exact r.decreases ⟨x, y, hxy, rfl, rfl⟩

/-! ## Well-founded relation with no natural-height rank -/

/-- A root above finite countdowns of every length. -/
inductive TopCountdown where
  | top
  | node (n : Nat)
  deriving DecidableEq, Repr

/-- The root can choose any finite countdown, followed by unit countdown steps. -/
inductive TopCountdownStep : TopCountdown → TopCountdown → Prop where
  | fromTop (n : Nat) : TopCountdownStep .top (.node n)
  | down (n : Nat) : TopCountdownStep (.node (n + 1)) (.node n)

/-- Each finite countdown node is accessible in the reverse relation. -/
theorem topCountdown_node_acc :
    ∀ n : Nat, Acc (fun y x => TopCountdownStep x y) (.node n)
  | 0 => by
      constructor
      intro y h
      cases h
  | n + 1 => by
      constructor
      intro y h
      cases h with
      | down _ => exact topCountdown_node_acc n

/-- The top state is accessible because each of its successors is a finite
countdown node. -/
theorem topCountdown_top_acc :
    Acc (fun y x => TopCountdownStep x y) .top := by
  constructor
  intro y h
  cases h with
  | fromTop n => exact topCountdown_node_acc n

/-- The reverse countdown relation is well-founded. -/
theorem topCountdown_reverse_wellFounded :
    WellFounded (fun y x => TopCountdownStep x y) := by
  refine ⟨?_⟩
  intro x
  cases x with
  | top => exact topCountdown_top_acc
  | node n => exact topCountdown_node_acc n

/-- A node at height `n` has an exact path of length `n` to node zero. -/
theorem topCountdown_node_steps_zero :
    ∀ n : Nat, Steps TopCountdownStep n (.node n) (.node 0)
  | 0 => Steps.refl _
  | n + 1 => Steps.cons (.down n) (topCountdown_node_steps_zero n)

/-- The top state has finite paths of every positive length. -/
theorem topCountdown_top_steps_zero (n : Nat) :
    Steps TopCountdownStep (n + 1) .top (.node 0) :=
  Steps.cons (.fromTop n) (topCountdown_node_steps_zero n)

/-- The well-founded top-countdown relation admits no natural-valued strict
ranking because the top state has paths of unbounded finite length. -/
theorem topCountdown_no_natRank : ¬ Nonempty (NatRank TopCountdownStep) := by
  rintro ⟨r⟩
  have h := r.bounds_steps (topCountdown_top_steps_zero (r.rank .top))
  omega

/-- Identity observation leaves the attained relation unchanged. -/
theorem observedStep_id_iff {A : Type u} (R : A → A → Prop) (x y : A) :
    ObservedStep R id x y ↔ R x y := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [id_eq] at ha hb
    subst x
    subst y
    exact hab
  · intro h
    exact ⟨x, y, h, rfl, rfl⟩

/-- The counterexample is observer-relative: the identity observer has a
well-founded reverse relation but no natural observer rank. -/
theorem observed_wellFounded_does_not_imply_nat_height :
    WellFounded (ObservedRev TopCountdownStep id) ∧
      ¬ Nonempty (NatFactoredRank TopCountdownStep id) := by
  constructor
  · apply Subrelation.wf
      (r := fun y x => TopCountdownStep x y)
    · intro y x h
      exact (observedStep_id_iff TopCountdownStep x y).1 h
    · exact topCountdown_reverse_wellFounded
  · intro h
    rcases h with ⟨r⟩
    apply topCountdown_no_natRank
    exact ⟨pullbackNatRank r⟩


/-! ## Natural ranks and bounded heights -/

/-- Every state bounds the lengths of the finite paths that start from it. -/
def BoundedHeights {A : Type u} (R : A → A → Prop) : Prop :=
  ∀ x : A, ∃ N : Nat, ∀ n y, Steps R n x y → n ≤ N

/-- A natural rank exists exactly when every state bounds the lengths of its paths. The
rank of a state is the least such bound. -/
theorem natRank_iff_boundedHeights {A : Type u} (R : A → A → Prop) :
    Nonempty (NatRank R) ↔ BoundedHeights R := by
  classical
  constructor
  · rintro ⟨r⟩ x
    refine ⟨r.rank x, ?_⟩
    intro n y h
    have hb := r.bounds_steps h
    omega
  · intro hb
    refine ⟨⟨fun x => Nat.find (hb x), ?_⟩⟩
    intro x y hxy
    show Nat.find (hb y) < Nat.find (hb x)
    have hx := Nat.find_spec (hb x)
    have hone : 1 ≤ Nat.find (hb x) := hx 1 y (Steps.cons hxy (Steps.refl y))
    have hy : ∀ n z, Steps R n y z → n ≤ Nat.find (hb x) - 1 := by
      intro n z h
      have hlen := hx (n + 1) z (Steps.cons hxy h)
      omega
    have hmin := Nat.find_min' (hb y) hy
    omega

/-- The observer form: a natural observer rank exists exactly when every observation bounds
the lengths of attained observed paths. -/
theorem natFactoredRank_iff_boundedHeights {A : Type u} {B : Type v}
    (R : A → A → Prop) (q : A → B) :
    Nonempty (NatFactoredRank R q) ↔ BoundedHeights (ObservedStep R q) :=
  natRank_iff_boundedHeights (ObservedStep R q)

/-! ## Controls C18 and C23 and the collapsed observer -/

/-- Positive rescaling of a natural rank. -/
def NatRank.scale {A : Type u} {R : A → A → Prop} (r : NatRank R) (k : Nat) (hk : 1 ≤ k) :
    NatRank R where
  rank x := k * r.rank x
  decreases h := Nat.mul_lt_mul_of_pos_left (r.decreases h) (by omega)

/-- A positive rescaling induces exactly the comparisons of the original rank. -/
theorem NatRank.scale_same_order {A : Type u} {R : A → A → Prop} (r : NatRank R)
    (k : Nat) (hk : 1 ≤ k) (x y : A) :
    (r.scale k hk).rank x < (r.scale k hk).rank y ↔ r.rank x < r.rank y := by
  show k * r.rank x < k * r.rank y ↔ r.rank x < r.rank y
  constructor
  · intro h
    by_contra h'
    have hle : r.rank y ≤ r.rank x := by omega
    have hmul := Nat.mul_le_mul_left k hle
    omega
  · intro h
    exact Nat.mul_lt_mul_of_pos_left h (by omega)

/-- The identity rank of the natural countdown `n + 1 → n`. -/
def countdownNatRank : NatRank (fun x y : Nat => x = y + 1) where
  rank x := x
  decreases h := by omega

/-- C18: doubling the countdown rank changes the function and keeps every comparison. -/
theorem rescaled_rank_control :
    (countdownNatRank.scale 2 (by omega)).rank ≠ countdownNatRank.rank ∧
      ∀ x y, (countdownNatRank.scale 2 (by omega)).rank x <
          (countdownNatRank.scale 2 (by omega)).rank y ↔
        countdownNatRank.rank x < countdownNatRank.rank y := by
  refine ⟨?_, countdownNatRank.scale_same_order 2 (by omega)⟩
  intro h
  have h1 := congrFun h 1
  simp [NatRank.scale, countdownNatRank] at h1

/-- Two disjoint one-step source chains `0 → 1` and `2 → 3` on `Fin 4`. -/
def TwoChainStep (x y : Fin 4) : Prop := (x = 0 ∧ y = 1) ∨ (x = 2 ∧ y = 3)

/-- An observation that identifies the end of each chain with the start of the other. -/
def twoChainObserver (x : Fin 4) : Bool := decide (x = 1 ∨ x = 2)

/-- The two-chain source relation is reverse well-founded. -/
theorem twoChainStep_reverse_wellFounded :
    WellFounded (fun y x : Fin 4 => TwoChainStep x y) := by
  apply Subrelation.wf (r := fun y x : Fin 4 => (y.val + 1) % 2 < (x.val + 1) % 2)
  · intro y x h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · exact InvImage.wf (fun x : Fin 4 => (x.val + 1) % 2) Nat.lt_wfRel.wf

/-- C23: the observed relation of the terminating two-chain source contains a two-cycle. -/
theorem twoChain_observation_cycle :
    WellFounded (fun y x : Fin 4 => TwoChainStep x y) ∧
      ¬ WellFounded (ObservedRev TwoChainStep twoChainObserver) := by
  refine ⟨twoChainStep_reverse_wellFounded, ?_⟩
  intro hwf
  have h1 : ObservedRev TwoChainStep twoChainObserver true false :=
    ⟨0, 1, Or.inl ⟨rfl, rfl⟩, by decide, by decide⟩
  have h2 : ObservedRev TwoChainStep twoChainObserver false true :=
    ⟨2, 3, Or.inr ⟨rfl, rfl⟩, by decide, by decide⟩
  exact (hwf.asymmetric true false h1) h2

/-- C23: source termination does not give a rank factoring through the observation, into any
well-founded relation. -/
theorem twoChain_no_factoredRank {C : Type w} (lt : C → C → Prop) (rank : Bool → C)
    (hlt : WellFounded lt) : ¬ FactoredRank TwoChainStep twoChainObserver lt rank := by
  intro h
  exact twoChain_observation_cycle.2 (observedRev_wellFounded_of_factoredRank hlt h)

/-- A constant observation of the countdown has an observed self-loop, so it licenses no
rank, while the identity observation does. The converse of `factoredRank_refines` fails for
collapsed observations. -/
theorem collapsed_observer_self_loop :
    WellFounded (ObservedRev (fun x y : Nat => x = y + 1) id) ∧
      ¬ WellFounded (ObservedRev (fun x y : Nat => x = y + 1) (fun _ => ())) := by
  constructor
  · exact observedRev_wellFounded_of_factoredRank (lt := (· < ·)) (rank := id)
      Nat.lt_wfRel.wf (fun {x y} h => by simp; omega)
  · intro hwf
    have hloop : ObservedRev (fun x y : Nat => x = y + 1) (fun _ => ()) () () :=
      ⟨1, 0, rfl, rfl, rfl⟩
    exact (hwf.asymmetric () () hloop) hloop

end OperatorKO7.Methods.OrientationClosure.ObserverRanks
