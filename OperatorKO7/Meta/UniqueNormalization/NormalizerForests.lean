import OperatorKO7.Meta.UniqueNormalization.NormalizerRealization
import OperatorKO7.Meta.UniqueNormalization.NormalFormSaturation
import OperatorKO7.Meta.UniqueNormalization.NormalizationDomains
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Card

/-!
# Minimal realizations and shortest-distance restrictions

Relation: arbitrary realizing relations and their finite paths with natural lengths.
Property: minimality, shortest root paths and strong normalization.
The distance function is a classical minimum, not an executable search procedure.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.Normalization

universe u v
variable {X : Type u} {Y : Type v}

/-- Finite reduction paths with their actual number of edges. -/
inductive PathLen (R : X → X → Prop) : Nat → X → X → Prop
  | nil (x : X) : PathLen R 0 x x
  | cons {k : Nat} {x y z : X} (step : R x y) (tail : PathLen R k y z) :
      PathLen R (k + 1) x z

variable {R S : X → X → Prop} {n : X → X} {x y z : X} {k : Nat}

theorem PathLen.toStar (p : PathLen R k x y) : Star R x y := by
  induction p with
  | nil a => exact .refl
  | cons h _ ih => exact .head h ih

theorem PathLen.mono (hRS : Subrel R S) (p : PathLen R k x y) :
    PathLen S k x y := by
  induction p with
  | nil a => exact .nil a
  | cons h _ ih => exact .cons (hRS h) ih

theorem PathLen.map (f : X → Y) {T : Y → Y → Prop}
    (hf : ∀ ⦃a b⦄, R a b → T (f a) (f b)) (p : PathLen R k x y) :
    PathLen T k (f x) (f y) := by
  induction p with
  | nil a => exact .nil (f a)
  | cons h _ ih => exact .cons (hf h) ih

theorem PathLen.snoc (p : PathLen R k x y) (h : R y z) :
    PathLen R (k + 1) x z := by
  induction p generalizing z with
  | nil a => exact .cons h (.nil z)
  | cons hab _ ih => exact .cons hab (ih h)

theorem star_iff_exists_pathLen : Star R x y ↔ ∃ k, PathLen R k x y := by
  constructor
  · intro p
    induction p with
    | refl => exact ⟨0, .nil _⟩
    | tail _ h ih =>
        obtain ⟨k, p⟩ := ih
        exact ⟨k + 1, p.snoc h⟩
  · rintro ⟨k, p⟩
    exact p.toStar

theorem pathLen_zero_iff : PathLen R 0 x y ↔ x = y := by
  constructor
  · intro p
    cases p
    rfl
  · intro h
    subst y
    exact .nil x

theorem PathLen.first (p : PathLen R (k + 1) x z) :
    ∃ y, R x y ∧ PathLen R k y z := by
  cases p with
  | cons h p => exact ⟨_, h, p⟩

/-- The minimum root-path length, with zero as the default for an absent path. -/
noncomputable def RootDistance (R : X → X → Prop) (n : X → X) (x : X) : Nat := by
  classical
  exact if h : ∃ k, PathLen R k x (n x) then Nat.find h else 0

theorem rootDistance_spec (h : Star R x (n x)) :
    PathLen R (RootDistance R n x) x (n x) := by
  classical
  have hp := star_iff_exists_pathLen.mp h
  simp only [RootDistance, dif_pos hp]
  exact Nat.find_spec hp

theorem rootDistance_le (p : PathLen R k x (n x)) : RootDistance R n x ≤ k := by
  classical
  have hp : ∃ k, PathLen R k x (n x) := ⟨k, p⟩
  simp only [RootDistance, dif_pos hp]
  exact Nat.find_min' hp p

theorem rootDistance_eq_zero_iff (h : Star R x (n x)) :
    RootDistance R n x = 0 ↔ x = n x := by
  constructor
  · intro hd
    have p := rootDistance_spec h
    rw [hd] at p
    exact pathLen_zero_iff.mp p
  · intro hx
    exact Nat.le_zero.mp (rootDistance_le (pathLen_zero_iff.mpr hx))

/-- Retained edges lower the minimum root distance by exactly one. -/
def ShortestRel (R : X → X → Prop) (n : X → X) (x y : X) : Prop :=
  R x y ∧ RootDistance R n x = RootDistance R n y + 1

theorem shortestRel_subrel : Subrel (ShortestRel R n) R := fun _ _ h => h.1

theorem rootDistance_step_le (hR : Realizes R n) (hxy : R x y) :
    RootDistance R n x ≤ RootDistance R n y + 1 := by
  have py : PathLen R (RootDistance R n y) y (n x) := by
    rw [hR.step_invariant hxy]
    exact rootDistance_spec (hR.reaches y)
  exact rootDistance_le (.cons hxy py)

theorem shortestRel_successor (hR : Realizes R n) (hx : x ≠ n x) :
    ∃ y, ShortestRel R n x y := by
  have p := rootDistance_spec (hR.reaches x)
  generalize hd : RootDistance R n x = d at p
  cases d with
  | zero => exact False.elim (hx (pathLen_zero_iff.mp p))
  | succ k =>
      obtain ⟨y, hxy, py⟩ := p.first
      have py' : PathLen R k y (n y) := by
        rw [← hR.step_invariant hxy]
        exact py
      have hle := rootDistance_le py'
      have hge := rootDistance_step_le hR hxy
      rw [hd] at hge
      have heq : RootDistance R n y = k :=
        Nat.le_antisymm hle (Nat.le_of_succ_le_succ hge)
      refine ⟨y, hxy, ?_⟩
      rw [heq]
      exact hd

/-- The natural-valued edge condition supplies strong normalization without realization. -/
theorem shortestRel_sn : SN (ShortestRel R n) := by
  have aux : ∀ d, ∀ x, RootDistance R n x = d →
      Acc (fun y x => ShortestRel R n x y) x := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro x hx
        apply Acc.intro x
        intro y hy
        apply ih (RootDistance R n y) ?_ y rfl
        rw [← hx, hy.2]
        exact Nat.lt_succ_self _
  exact ⟨fun x => aux _ x rfl⟩

theorem shortestRel_realizes (hR : Realizes R n) : Realizes (ShortestRel R n) n := by
  classical
  apply realizes_of_subrel_maxRel (fun _ _ h => hR.subrel_maxRel h.1)
  intro x
  obtain ⟨r, hr, hxr⟩ := wn_of_sn (shortestRel_sn (R := R) (n := n)) x
  have hfix : r = n r := by
    apply Classical.byContradiction
    intro hne
    obtain ⟨y, hy⟩ := shortestRel_successor hR hne
    exact hr y hy
  have hi := hR.star_invariant (star_mono shortestRel_subrel hxr)
  exact (hfix.trans hi.symm) ▸ hxr

theorem shortest_path_preserved (hR : Realizes R n)
    (p : PathLen R k x (n x)) (hk : k = RootDistance R n x) :
    PathLen (ShortestRel R n) k x (n x) := by
  induction k generalizing x with
  | zero => exact pathLen_zero_iff.mpr (pathLen_zero_iff.mp p)
  | succ k ih =>
      obtain ⟨y, hxy, py⟩ := p.first
      have hi := hR.step_invariant hxy
      have py' : PathLen R k y (n y) := by
        rw [← hi]
        exact py
      have hle := rootDistance_le py'
      have hge := rootDistance_step_le hR hxy
      rw [← hk] at hge
      have heq : RootDistance R n y = k :=
        Nat.le_antisymm hle (Nat.le_of_succ_le_succ hge)
      have hedge : ShortestRel R n x y :=
        ⟨hxy, hk.symm.trans (congrArg (fun j => j + 1) heq.symm)⟩
      have tail := ih py' heq.symm
      have tail' : PathLen (ShortestRel R n) k y (n x) := by
        rw [hi]
        exact tail
      exact .cons hedge tail'

theorem rootDistance_shortest_eq (hR : Realizes R n) (x : X) :
    RootDistance (ShortestRel R n) n x = RootDistance R n x := by
  apply Nat.le_antisymm
  · exact rootDistance_le (shortest_path_preserved hR
      (rootDistance_spec (hR.reaches x)) rfl)
  · exact rootDistance_le ((rootDistance_spec ((shortestRel_realizes hR).reaches x)).mono
      shortestRel_subrel)

theorem shortestRel_idempotent (hR : Realizes R n) :
    ShortestRel (ShortestRel R n) n = ShortestRel R n := by
  funext x y
  apply propext
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rw [rootDistance_shortest_eq hR x, rootDistance_shortest_eq hR y]
    exact h.2

theorem PathLen.distance_eq (p : PathLen (ShortestRel R n) k x y) :
    RootDistance R n x = RootDistance R n y + k := by
  induction p with
  | nil a => exact (Nat.add_zero _).symm
  | @cons k a b c h _ ih =>
      calc
        RootDistance R n a = RootDistance R n b + 1 := h.2
        _ = (RootDistance R n c + k) + 1 := congrArg (fun j => j + 1) ih
        _ = RootDistance R n c + (k + 1) := Nat.add_assoc _ _ _

theorem shortest_complete_length (hR : Realizes R n)
    (p : PathLen (ShortestRel R n) k x (n x)) : k = RootDistance R n x := by
  have hzero := (rootDistance_eq_zero_iff (hR.reaches (n x))).mpr (hR.idem x).symm
  have hlen := p.distance_eq
  rw [hzero, Nat.zero_add] at hlen
  exact hlen.symm

theorem shortest_path_to_normal_length (hR : Realizes R n)
    (p : PathLen (ShortestRel R n) k x y) (hy : NF (ShortestRel R n) y) :
    k = RootDistance R n x := by
  have heq := ((shortestRel_realizes hR).nf_star_iff x y).mp ⟨hy, p.toStar⟩
  subst y
  exact shortest_complete_length hR p

/-- At most one successor is retained at each source. -/
def FunctionalRel (R : X → X → Prop) : Prop :=
  ∀ ⦃x y z⦄, R x y → R x z → y = z

/-- Inclusion-minimality inside the order of all realizations of the same map. -/
def MinimalRealizes (R : X → X → Prop) (n : X → X) : Prop :=
  Realizes R n ∧ ∀ S : X → X → Prop,
    Realizes S n → Subrel S R → Subrel R S

/-- The least relation in the entire order of realizations of the same map. -/
def LeastRealizes (R : X → X → Prop) (n : X → X) : Prop :=
  Realizes R n ∧ ∀ S : X → X → Prop, Realizes S n → Subrel R S

theorem exists_functional_realization_subrel (hR : Realizes R n) :
    ∃ T : X → X → Prop, Realizes T n ∧ Subrel T R ∧
      FunctionalRel T ∧ SN T := by
  classical
  let f : {a : X // a ≠ n a} → X :=
    fun a => Classical.choose (shortestRel_successor hR a.2)
  have hf (a : {a : X // a ≠ n a}) : ShortestRel R n a.1 (f a) :=
    Classical.choose_spec (shortestRel_successor hR a.2)
  let T : X → X → Prop := fun a b => ∃ ha : a ≠ n a, b = f ⟨a, ha⟩
  have hTG : Subrel T (ShortestRel R n) := by
    intro a b h
    obtain ⟨ha, hb⟩ := h
    exact hb.symm ▸ hf ⟨a, ha⟩
  have ht : SN T := sn_subrel hTG shortestRel_sn
  have hreal : Realizes T n :=
    realizes_of_sn_subrel_maxRel (fun _ _ h => hR.subrel_maxRel (hTG h).1) ht
      (fun a ha => ⟨f ⟨a, ha⟩, ha, rfl⟩)
  refine ⟨T, hreal, fun _ _ h => (hTG h).1, ?_, ht⟩
  intro a b c hab hac
  obtain ⟨ha, hb⟩ := hab
  obtain ⟨ha', hc⟩ := hac
  exact hb.trans hc.symm

theorem minimalRealizes_of_functional (hR : Realizes R n)
    (hf : FunctionalRel R) : MinimalRealizes R n := by
  refine ⟨hR, ?_⟩
  intro S hS hSR x y hxy
  have hx : x ≠ n x := (hR.subrel_maxRel hxy).1
  obtain ⟨z, hxz, _⟩ := star_first (hS.reaches x) hx
  have hzy : z = y := hf (hSR hxz) hxy
  exact hzy ▸ hxz

theorem minimalRealizes_iff :
    MinimalRealizes R n ↔ Realizes R n ∧ FunctionalRel R := by
  constructor
  · rintro ⟨hR, hmin⟩
    obtain ⟨T, hT, hTR, hf, _⟩ := exists_functional_realization_subrel hR
    have hRT := hmin T hT hTR
    exact ⟨hR, fun _ _ _ hxy hxz => hf (hRT hxy) (hRT hxz)⟩
  · exact fun h => minimalRealizes_of_functional h.1 h.2

theorem exists_minimal_realization_subrel (hR : Realizes R n) :
    ∃ T : X → X → Prop, MinimalRealizes T n ∧ Subrel T R := by
  obtain ⟨T, hT, hTR, hf, _⟩ := exists_functional_realization_subrel hR
  exact ⟨T, minimalRealizes_of_functional hT hf, hTR⟩

theorem functional_realizes_subrel_shortest (hR : Realizes R n)
    (hf : FunctionalRel R) : Subrel R (ShortestRel R n) := by
  intro x y hxy
  obtain ⟨z, hxz⟩ := shortestRel_successor hR (hR.subrel_maxRel hxy).1
  have hzy : z = y := hf hxz.1 hxy
  exact hzy ▸ hxz

theorem functional_realizes_sn (hR : Realizes R n)
    (hf : FunctionalRel R) : SN R :=
  sn_subrel (functional_realizes_subrel_shortest hR hf) shortestRel_sn

theorem MinimalRealizes.sn (h : MinimalRealizes R n) : SN R :=
  functional_realizes_sn h.1 (minimalRealizes_iff.mp h).2

theorem minimalRealizes_iff_unique_successor :
    MinimalRealizes R n ↔ Realizes R n ∧
      ∀ x, x ≠ n x → ∃! y, R x y := by
  rw [minimalRealizes_iff]
  constructor
  · rintro ⟨hR, hf⟩
    refine ⟨hR, ?_⟩
    intro x hx
    obtain ⟨y, hxy, _⟩ := star_first (hR.reaches x) hx
    exact ⟨y, hxy, fun z hxz => hf hxz hxy⟩
  · rintro ⟨hR, hu⟩
    refine ⟨hR, ?_⟩
    intro x y z hxy hxz
    obtain ⟨a, _, ha⟩ := hu x (hR.subrel_maxRel hxy).1
    exact (ha y hxy).trans (ha z hxz).symm

theorem LeastRealizes.minimal (h : LeastRealizes R n) : MinimalRealizes R n :=
  ⟨h.1, fun S hS _ => h.2 S hS⟩

theorem leastRealizes_unique (hR : LeastRealizes R n)
    (hS : LeastRealizes S n) : R = S := by
  funext x y
  exact propext ⟨fun h => hR.2 S hS.1 h, fun h => hS.2 R hR.1 h⟩

/-- Every nonfixed source has its single direct edge to its prescribed root. -/
def RootStar (n : X → X) (x y : X) : Prop := x ≠ n x ∧ y = n x

theorem rootStar_realizes (hn : ∀ x, n (n x) = n x) :
    Realizes (RootStar n) n := by
  apply realizes_of_subrel_maxRel
  · intro x y h
    refine ⟨h.1, ?_⟩
    rw [h.2, hn x]
  · intro x
    by_cases hx : x = n x
    · simpa only [← hx] using (show Star (RootStar n) x x from .refl)
    · exact .single ⟨hx, rfl⟩

theorem rootStar_functional : FunctionalRel (RootStar n) :=
  fun _ _ _ hxy hxz => hxy.2.trans hxz.2.symm

theorem rootStar_minimal (hn : ∀ x, n (n x) = n x) :
    MinimalRealizes (RootStar n) n :=
  minimalRealizes_of_functional (rootStar_realizes hn) rootStar_functional

theorem rootStar_sn (hn : ∀ x, n (n x) = n x) : SN (RootStar n) :=
  functional_realizes_sn (rootStar_realizes hn) rootStar_functional

theorem rootStar_irrefl (x : X) : ¬ RootStar n x x := fun h => h.1 h.2

/-- Every three points in one fiber contain an equal pair. -/
def FibersAtMostTwo (n : X → X) : Prop :=
  ∀ r x y z, n x = r → n y = r → n z = r → x = y ∨ x = z ∨ y = z

theorem fibersAtMostTwo_iff (hn : ∀ x, n (n x) = n x) :
    FibersAtMostTwo n ↔
      ∀ x y, n x = n y → x = n x ∨ y = n y ∨ x = y := by
  constructor
  · intro hf x y hxy
    rcases hf (n x) x y (n x) rfl hxy.symm (hn x) with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl (h.trans hxy))
  · intro hp r x y z hx hy hz
    rcases hp x y (hx.trans hy.symm) with hxf | hyf | hxy
    · rcases hp y z (hy.trans hz.symm) with hyf | hzf | hyz
      · exact Or.inl (hxf.trans ((hx.trans hy.symm).trans hyf.symm))
      · exact Or.inr (Or.inl (hxf.trans ((hx.trans hz.symm).trans hzf.symm)))
      · exact Or.inr (Or.inr hyz)
    · rcases hp x z (hx.trans hz.symm) with hxf | hzf | hxz
      · exact Or.inl (hxf.trans ((hx.trans hy.symm).trans hyf.symm))
      · exact Or.inr (Or.inr (hyf.trans ((hy.trans hz.symm).trans hzf.symm)))
      · exact Or.inr (Or.inl hxz)
    · exact Or.inl hxy

theorem rootStar_subrel_of_fibersAtMostTwo (hR : Realizes R n)
    (hf : FibersAtMostTwo n) : Subrel (RootStar n) R := by
  intro x y hxy
  obtain ⟨z, hxz⟩ := shortestRel_successor hR hxy.1
  have hne : x ≠ z := by
    intro h
    subst z
    exact (Nat.ne_of_lt (Nat.lt_succ_self (RootDistance R n x))) hxz.2
  have hi := hR.step_invariant hxz.1
  rcases hf (n x) x z (n x) rfl hi.symm (hR.idem x) with h | h | h
  · exact False.elim (hne h)
  · exact False.elim (hxy.1 h)
  · exact (h.trans hxy.2.symm) ▸ hxz.1

theorem rootStar_least (hn : ∀ x, n (n x) = n x) (hf : FibersAtMostTwo n) :
    LeastRealizes (RootStar n) n :=
  ⟨rootStar_realizes hn, fun _ hR => rootStar_subrel_of_fibersAtMostTwo hR hf⟩

/-- A direct-root relation with the edge from a rerouted through b. -/
def Reroute (n : X → X) (a b x y : X) : Prop :=
  (x = a ∧ y = b) ∨ (x ≠ a ∧ RootStar n x y)

theorem reroute_realizes (hn : ∀ x, n (n x) = n x) {a b : X}
    (ha : a ≠ n a) (hb : b ≠ n b) (hab : a ≠ b) (hi : n a = n b) :
    Realizes (Reroute n a b) n := by
  classical
  apply realizes_of_subrel_maxRel
  · intro x y hxy
    rcases hxy with ⟨hxa, hyb⟩ | ⟨_, hroot⟩
    · subst x
      subst y
      exact ⟨ha, hi⟩
    · exact (rootStar_realizes hn).subrel_maxRel hroot
  · intro x
    by_cases hxa : x = a
    · subst x
      have hab' : Reroute n a b a b := Or.inl ⟨rfl, rfl⟩
      have hbr : Reroute n a b b (n a) := Or.inr ⟨Ne.symm hab, hb, hi⟩
      exact .head hab' (.single hbr)
    · by_cases hx : x = n x
      · simpa only [← hx] using (show Star (Reroute n a b) x x from .refl)
      · exact .single (Or.inr ⟨hxa, hx, rfl⟩)

theorem no_common_realization_rootStar_reroute {a b : X}
    (ha : a ≠ n a) (hb : b ≠ n b) (hi : n a = n b)
    (hR : Realizes R n) (hrs : Subrel R (RootStar n))
    (hrr : Subrel R (Reroute n a b)) : False := by
  obtain ⟨y, hay, _⟩ := star_first (hR.reaches a) ha
  have hy : y = n a := (hrs hay).2
  rcases hrr hay with h | h
  · exact hb (h.2.symm.trans (hy.trans hi))
  · exact h.1 rfl

theorem LeastRealizes.nonroot_unique (hR : LeastRealizes R n) {a b : X}
    (hi : n a = n b) (ha : a ≠ n a) (hb : b ≠ n b) : a = b := by
  classical
  apply Classical.byContradiction
  intro hab
  have hs := rootStar_realizes hR.1.idem
  have ht := reroute_realizes hR.1.idem ha hb hab hi
  exact no_common_realization_rootStar_reroute ha hb hi hR.1
    (hR.2 _ hs) (hR.2 _ ht)

theorem LeastRealizes.small_fibers (hR : LeastRealizes R n) :
    FibersAtMostTwo n := by
  classical
  apply (fibersAtMostTwo_iff hR.1.idem).mpr
  intro x y hi
  by_cases hx : x = n x
  · exact Or.inl hx
  · by_cases hy : y = n y
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr (hR.nonroot_unique hi hx hy))

theorem exists_leastRealizes_iff :
    (∃ R : X → X → Prop, LeastRealizes R n) ↔
      (∀ x, n (n x) = n x) ∧ FibersAtMostTwo n := by
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨hR.1.idem, hR.small_fibers⟩
  · rintro ⟨hn, hf⟩
    exact ⟨RootStar n, rootStar_least hn hf⟩

theorem leastRealizes_iff :
    LeastRealizes R n ↔ (∀ x, n (n x) = n x) ∧ FibersAtMostTwo n ∧ R = RootStar n := by
  constructor
  · intro hR
    exact ⟨hR.1.idem, hR.small_fibers,
      leastRealizes_unique hR (rootStar_least hR.1.idem hR.small_fibers)⟩
  · rintro ⟨hn, hf, hR⟩
    subst R
    exact rootStar_least hn hf

/-- In a functional realization, taking the source bijects edges with nonfixed points. -/
noncomputable def edgeSourceEquiv (hR : Realizes R n) (hf : FunctionalRel R) :
    {p : X × X // R p.1 p.2} ≃ {x : X // x ≠ n x} := by
  classical
  let pick : {x : X // x ≠ n x} → X :=
    fun x => Classical.choose (star_first (hR.reaches x.1) x.2)
  have hpick (x : {x : X // x ≠ n x}) : R x.1 (pick x) :=
    (Classical.choose_spec (star_first (hR.reaches x.1) x.2)).1
  refine
    { toFun := fun e => ⟨e.1.1, (hR.subrel_maxRel e.2).1⟩
      invFun := fun x => ⟨(x.1, pick x), hpick x⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact hf (hpick ⟨e.1.1, (hR.subrel_maxRel e.2).1⟩) e.2
  · intro x
    apply Subtype.ext
    rfl

theorem functional_realizes_edge_count [Fintype X]
    [Fintype {p : X × X // R p.1 p.2}] [Fintype {x : X // x = n x}]
    (hR : Realizes R n) (hf : FunctionalRel R) :
    Fintype.card {p : X × X // R p.1 p.2} =
      Fintype.card X - Fintype.card {x : X // x = n x} := by
  classical
  calc
    Fintype.card {p : X × X // R p.1 p.2} =
        Fintype.card {x : X // x ≠ n x} := Fintype.card_congr (edgeSourceEquiv hR hf)
    _ = Fintype.card X - Fintype.card {x : X // x = n x} :=
      Fintype.card_subtype_compl (fun x : X => x = n x)

theorem MinimalRealizes.edge_count [Fintype X]
    [Fintype {p : X × X // R p.1 p.2}] [Fintype {x : X // x = n x}]
    (hR : MinimalRealizes R n) :
    Fintype.card {p : X × X // R p.1 p.2} =
      Fintype.card X - Fintype.card {x : X // x = n x} :=
  functional_realizes_edge_count hR.1 (minimalRealizes_iff.mp hR).2

theorem saturate_realizes_eq_maxRel (hR : Realizes R n) :
    Saturate R = MaxRel n := by
  funext x y
  apply propext
  constructor
  · intro h
    exact ⟨fun hx => h.1 ((hR.nf_iff x).mpr hx), hR.conv_iff.mp h.2⟩
  · intro h
    exact ⟨fun hx => h.1 ((hR.nf_iff x).mp hx), hR.conv_iff.mpr h.2⟩

theorem saturate_realizes (hR : Realizes R n) : Realizes (Saturate R) n := by
  rw [saturate_realizes_eq_maxRel hR]
  exact maxRel_realizes hR.idem

theorem saturate_shortest_eq_maxRel (hR : Realizes R n) :
    Saturate (ShortestRel R n) = MaxRel n :=
  saturate_realizes_eq_maxRel (shortestRel_realizes hR)

theorem rootDistance_maxRel_nonfixed (hn : ∀ x, n (n x) = n x) (hx : x ≠ n x) :
    RootDistance (MaxRel n) n x = 1 := by
  have hp : PathLen (MaxRel n) 1 x (n x) :=
    .cons ⟨hx, (hn x).symm⟩ (.nil (n x))
  have hne : RootDistance (MaxRel n) n x ≠ 0 :=
    fun hz => hx ((rootDistance_eq_zero_iff ((maxRel_realizes hn).reaches x)).mp hz)
  exact Nat.le_antisymm (rootDistance_le hp) (Nat.one_le_iff_ne_zero.mpr hne)

theorem shortestRel_maxRel_eq_rootStar (hn : ∀ x, n (n x) = n x) :
    ShortestRel (MaxRel n) n = RootStar n := by
  funext x y
  apply propext
  constructor
  · intro h
    have hdx := rootDistance_maxRel_nonfixed hn h.1.1
    have hdy : RootDistance (MaxRel n) n y = 0 :=
      Nat.succ.inj (h.2.symm.trans hdx)
    have hy := (rootDistance_eq_zero_iff ((maxRel_realizes hn).reaches y)).mp hdy
    exact ⟨h.1.1, hy.trans h.1.2.symm⟩
  · intro h
    refine ⟨(rootStar_realizes hn).subrel_maxRel h, ?_⟩
    have hdx := rootDistance_maxRel_nonfixed hn h.1
    have hy : y = n y := by rw [h.2, hn x]
    have hdy := (rootDistance_eq_zero_iff ((maxRel_realizes hn).reaches y)).mpr hy
    rw [hdx, hdy]

theorem shortestRel_saturate_eq_rootStar (hR : Realizes R n) :
    ShortestRel (Saturate R) n = RootStar n := by
  rw [saturate_realizes_eq_maxRel hR]
  exact shortestRel_maxRel_eq_rootStar hR.idem

theorem maxRel_eq_rootStar_iff : MaxRel n = RootStar n ↔ n = id := by
  classical
  constructor
  · intro heq
    funext x
    apply Classical.byContradiction
    intro hx
    have hm : MaxRel n x x := ⟨Ne.symm hx, rfl⟩
    have hs : RootStar n x x := by rw [← heq]; exact hm
    exact rootStar_irrefl x hs
  · intro hn
    subst n
    funext x y
    apply propext
    exact ⟨fun h => False.elim (h.1 rfl), fun h => False.elim (h.1 rfl)⟩

theorem saturate_shortest_commute_iff (hR : Realizes R n) :
    Saturate (ShortestRel R n) = ShortestRel (Saturate R) n ↔ n = id := by
  rw [saturate_shortest_eq_maxRel hR, shortestRel_saturate_eq_rootStar hR]
  exact maxRel_eq_rootStar_iff

/-- The saturation on classes containing a normal form realizes the class label. -/
theorem convertible_saturate_eq_maxRel (hu : UNC R) :
    ConvertibleRestriction R (Saturate R) = MaxRel (classLabel R) := by
  funext a b
  apply propext
  constructor
  · intro h
    exact ⟨fun ha => h.1 ((classLabel_fixed_iff hu a).mpr ha),
      (classLabel_eq_iff_conv hu a b).mpr h.2⟩
  · intro h
    exact ⟨fun ha => h.1 ((classLabel_fixed_iff hu a).mp ha),
      (classLabel_eq_iff_conv hu a b).mp h.2⟩

theorem convertible_saturate_realizes (hu : UNC R) :
    Realizes (ConvertibleRestriction R (Saturate R)) (classLabel R) := by
  rw [convertible_saturate_eq_maxRel hu]
  exact maxRel_realizes (classLabel_idempotent hu)

end OperatorKO7.Meta.UniqueNormalization.Normalization
