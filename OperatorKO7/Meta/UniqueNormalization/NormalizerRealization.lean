import OperatorKO7.Meta.UniqueNormalization.NormalizationCore

/-!
# Relations realizing a prescribed normalizer

Relation: an arbitrary binary relation R and its finite reduction Star R.
Property: normal forms, weak normalization, confluence and conversion.
The empty relation with the identity map supplies a model on every carrier.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.Normalization

universe u v
variable {X : Type u}

/-- A relation has confluence and reaches the prescribed normal form at every input. -/
def Realizes (R : X → X → Prop) (n : X → X) : Prop :=
  CR R ∧ ∀ x, Star R x (n x) ∧ NF R (n x)

/-- Compatible edges preserve the prescribed value and have a nonfixed source. -/
def MaxRel (n : X → X) (x y : X) : Prop :=
  x ≠ n x ∧ n x = n y

variable {R S : X → X → Prop} {n : X → X} {x y : X}

theorem Realizes.cr (h : Realizes R n) : CR R := h.1

theorem Realizes.reaches (h : Realizes R n) (x : X) : Star R x (n x) :=
  (h.2 x).1

theorem Realizes.normal (h : Realizes R n) (x : X) : NF R (n x) :=
  (h.2 x).2

theorem Realizes.wn (h : Realizes R n) : WN R :=
  fun x => ⟨n x, h.normal x, h.reaches x⟩

theorem Realizes.idem (h : Realizes R n) (x : X) : n (n x) = n x :=
  nf_star_eq (h.normal x) (h.reaches (n x))

theorem Realizes.step_invariant (h : Realizes R n) (hxy : R x y) :
    n x = n y :=
  unr_of_unc (unc_of_cr h.cr) (h.normal x) (h.normal y)
    (h.reaches x) ((show Star R x y from .single hxy).trans (h.reaches y))

theorem Realizes.subrel_maxRel (h : Realizes R n) : Subrel R (MaxRel n) := by
  intro x y hxy
  refine ⟨?_, h.step_invariant hxy⟩
  intro hx
  exact h.normal x y (hx ▸ hxy)

theorem Realizes.nf_iff (h : Realizes R n) (x : X) :
    NF R x ↔ x = n x := by
  constructor
  · intro hx
    exact (nf_star_eq hx (h.reaches x)).symm
  · intro hx
    exact hx.symm ▸ h.normal x

theorem Realizes.conv_iff (h : Realizes R n) :
    Conv R x y ↔ n x = n y := by
  constructor
  · exact conv_invariant n (fun _ _ hp => h.step_invariant hp)
  · intro hxy
    refine conv_of_join ⟨n x, h.reaches x, ?_⟩
    rw [hxy]
    exact h.reaches y

/-- Compatible edges and reachable roots already force idempotence. -/
theorem realizes_of_subrel_maxRel
    (hs : Subrel R (MaxRel n)) (hr : ∀ x, Star R x (n x)) :
    Realizes R n := by
  have hi : ∀ ⦃x y⦄, R x y → n x = n y := fun _ _ hp => (hs hp).2
  have hn : ∀ x, n (n x) = n x :=
    fun x => (star_invariant n hi (hr x)).symm
  have hnf : ∀ x, NF R (n x) := by
    intro x y hxy
    exact (hs hxy).1 (hn x).symm
  refine ⟨?_, fun x => ⟨hr x, hnf x⟩⟩
  intro x y z hxy hxz
  refine ⟨n x, ?_, ?_⟩
  · rw [star_invariant n hi hxy]
    exact hr y
  · rw [star_invariant n hi hxz]
    exact hr z

/-- The realization criterion has no separate idempotence premise. -/
theorem realizes_iff :
    Realizes R n ↔ Subrel R (MaxRel n) ∧ ∀ x, Star R x (n x) :=
  ⟨fun h => ⟨h.subrel_maxRel, h.reaches⟩,
    fun h => realizes_of_subrel_maxRel h.1 h.2⟩

theorem maxRel_realizes (hn : ∀ x, n (n x) = n x) :
    Realizes (MaxRel n) n := by
  apply realizes_of_subrel_maxRel (fun _ _ h => h)
  intro x
  by_cases hx : x = n x
  · simpa only [← hx] using (show Star (MaxRel n) x x from .refl)
  · exact .single ⟨hx, (hn x).symm⟩

theorem exists_realizes_iff :
    (∃ R : X → X → Prop, Realizes R n) ↔ (∀ x, n (n x) = n x) :=
  ⟨fun ⟨_, h⟩ => h.idem, fun hn => ⟨MaxRel n, maxRel_realizes hn⟩⟩

theorem empty_realizes_id : Realizes (fun (_ _ : X) => False) id :=
  ⟨empty_cr, fun _ => ⟨.refl, fun _ h => h⟩⟩

theorem empty_realizes_iff :
    Realizes (fun (_ _ : X) => False) n ↔ n = id := by
  constructor
  · intro h
    funext x
    exact nf_star_eq (fun _ h => h) (h.reaches x)
  · intro h
    subst n
    exact empty_realizes_id

/-- Weak normalization and confluence exactly characterize relations admitting a normalizer. -/
theorem exists_normalizer_iff_wn_cr :
    (∃ n : X → X, Realizes R n) ↔ WN R ∧ CR R := by
  classical
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨hn.wn, hn.cr⟩
  · rintro ⟨hw, hc⟩
    exact ⟨fun x => Classical.choose (hw x), hc,
      fun x => ⟨(Classical.choose_spec (hw x)).2, (Classical.choose_spec (hw x)).1⟩⟩

theorem Realizes.star_invariant (h : Realizes R n) (p : Star R x y) :
    n x = n y :=
  OperatorKO7.Meta.UniqueNormalization.Normalization.star_invariant n
    (fun _ _ hp => h.step_invariant hp) p

theorem Realizes.conv_invariant (h : Realizes R n) (p : Conv R x y) :
    n x = n y := h.conv_iff.mp p

theorem Realizes.nf_star_iff (h : Realizes R n) (x r : X) :
    NF R r ∧ Star R x r ↔ r = n x := by
  constructor
  · intro hr
    exact unr_of_unc (unc_of_cr h.cr) hr.1 (h.normal x) hr.2 (h.reaches x)
  · intro hr
    subst r
    exact ⟨h.normal x, h.reaches x⟩

theorem realizes_normalizer_unique {m : X → X}
    (hn : Realizes R n) (hm : Realizes R m) : n = m := by
  funext x
  exact unr_of_unc (unc_of_cr hn.cr) (hn.normal x) (hm.normal x)
    (hn.reaches x) (hm.reaches x)

theorem realizes_mono (hR : Realizes R n) (hRS : Subrel R S)
    (hS : Subrel S (MaxRel n)) : Realizes S n :=
  realizes_of_subrel_maxRel hS (fun x => star_mono hRS (hR.reaches x))

theorem realizes_of_sn_subrel_maxRel (hs : Subrel R (MaxRel n)) (ht : SN R)
    (hlive : ∀ x, x ≠ n x → ∃ y, R x y) : Realizes R n := by
  classical
  apply realizes_of_subrel_maxRel hs
  intro x
  obtain ⟨r, hr, hxr⟩ := wn_of_sn ht x
  have hfix : r = n r := by
    apply Classical.byContradiction
    intro hne
    obtain ⟨y, hy⟩ := hlive r hne
    exact hr y hy
  have hi := star_invariant n (fun _ _ hp => (hs hp).2) hxr
  exact (hfix.trans hi.symm) ▸ hxr

theorem realizes_union_iff (hR : Realizes R n) :
    Realizes (fun x y => R x y ∨ S x y) n ↔ Subrel S (MaxRel n) := by
  constructor
  · intro h x y hxy
    exact h.subrel_maxRel (Or.inr hxy)
  · intro hS
    apply realizes_mono hR (fun _ _ h => Or.inl h)
    intro x y hxy
    exact hxy.elim (fun h => hR.subrel_maxRel h) (fun h => hS h)

theorem realizes_iUnion {I : Sort v} (A : I → X → X → Prop)
    (hi : Nonempty I) (hA : ∀ i, Realizes (A i) n) :
    Realizes (fun x y => ∃ i, A i x y) n := by
  obtain ⟨i⟩ := hi
  apply realizes_mono (hA i) (fun _ _ h => ⟨i, h⟩)
  intro x y hxy
  obtain ⟨j, hj⟩ := hxy
  exact (hA j).subrel_maxRel hj

theorem realizes_iInter_iff {I : Sort v} (A : I → X → X → Prop)
    (hs : Subrel (fun x y => ∀ i, A i x y) (MaxRel n)) :
    Realizes (fun x y => ∀ i, A i x y) n ↔
      ∃ T : X → X → Prop, Realizes T n ∧ ∀ i, Subrel T (A i) := by
  constructor
  · intro h
    exact ⟨_, h, fun i _ _ hxy => hxy i⟩
  · rintro ⟨T, hT, hTA⟩
    exact realizes_mono hT (fun _ _ h i => hTA i h) hs

theorem realizes_nonempty_iInter_iff {I : Sort v} (A : I → X → X → Prop)
    (hi : Nonempty I) (hA : ∀ i, Realizes (A i) n) :
    Realizes (fun x y => ∀ i, A i x y) n ↔
      ∃ T : X → X → Prop, Realizes T n ∧ ∀ i, Subrel T (A i) := by
  obtain ⟨i⟩ := hi
  exact realizes_iInter_iff A (fun _ _ h => (hA i).subrel_maxRel (h i))

theorem realizes_intersection_iff (hR : Realizes R n) :
    Realizes (fun x y => R x y ∧ S x y) n ↔
      ∃ T : X → X → Prop, Realizes T n ∧ Subrel T R ∧ Subrel T S := by
  constructor
  · intro h
    exact ⟨_, h, fun _ _ hp => hp.1, fun _ _ hp => hp.2⟩
  · rintro ⟨T, hT, hTR, hTS⟩
    exact realizes_mono hT (fun _ _ hp => ⟨hTR hp, hTS hp⟩)
      (fun _ _ hp => hR.subrel_maxRel hp.1)

/-- Edges permitted by an ambient relation and by the prescribed normalizer. -/
def AllowedRel (A : X → X → Prop) (n : X → X) : X → X → Prop :=
  fun x y => A x y ∧ MaxRel n x y

theorem Realizes.subrel_allowed {A : X → X → Prop}
    (hR : Realizes R n) (hRA : Subrel R A) : Subrel R (AllowedRel A n) :=
  fun _ _ hp => ⟨hRA hp, hR.subrel_maxRel hp⟩

theorem allowed_realizes_iff (A : X → X → Prop) :
    Realizes (AllowedRel A n) n ↔ ∀ x, Star (AllowedRel A n) x (n x) :=
  ⟨Realizes.reaches, realizes_of_subrel_maxRel (fun _ _ h => h.2)⟩

theorem exists_realizes_subrel_iff (A : X → X → Prop) :
    (∃ R : X → X → Prop, Realizes R n ∧ Subrel R A) ↔
      ∀ x, Star (AllowedRel A n) x (n x) := by
  constructor
  · rintro ⟨R, hR, hRA⟩ x
    exact star_mono (hR.subrel_allowed hRA) (hR.reaches x)
  · intro h
    exact ⟨AllowedRel A n, (allowed_realizes_iff A).mpr h, fun _ _ hp => hp.1⟩

/-- A cut contains no fixed point of the prescribed map. -/
def RootFree (n : X → X) (U : X → Prop) : Prop :=
  ∀ x, U x → x ≠ n x

/-- An edge leaves a predicate-defined cut. -/
def Exits (R : X → X → Prop) (U : X → Prop) : Prop :=
  ∃ x y, U x ∧ R x y ∧ ¬ U y

def AllCuts (R : X → X → Prop) (n : X → X) : Prop :=
  ∀ U : X → Prop, (∃ x, U x) → RootFree n U → Exits R U

def FiberCuts (R : X → X → Prop) (n : X → X) : Prop :=
  ∀ (r : X) (U : X → Prop), (∃ x, U x) → RootFree n U →
    (∀ x, U x → n x = r) → Exits R U

theorem exits_of_star {U : X → Prop} (p : Star R x y)
    (hx : U x) (hy : ¬ U y) : Exits R U := by
  classical
  induction p with
  | refl => exact False.elim (hy hx)
  | @tail b c p h ih =>
      by_cases hb : U b
      · exact ⟨b, c, hb, h, hy⟩
      · exact ih hb

theorem root_reach_iff_cuts (hs : Subrel R (MaxRel n)) :
    (∀ x, Star R x (n x)) ↔ AllCuts R n := by
  classical
  constructor
  · intro hr U hU hf
    obtain ⟨x, hx⟩ := hU
    have hn := idempotent_of_reachable_invariant n (fun _ _ hp => (hs hp).2) hr
    exact exits_of_star (hr x) hx (fun hnx => hf (n x) hnx (hn x).symm)
  · intro hc x
    apply Classical.byContradiction
    intro hroot
    have hf : RootFree n (fun y => Star R x y) := by
      intro y hxy hy
      have hi := star_invariant n (fun _ _ hp => (hs hp).2) hxy
      have hyr : y = n x := hy.trans hi.symm
      exact hroot (hyr ▸ hxy)
    obtain ⟨a, b, hxa, hab, hxb⟩ := hc (fun y => Star R x y) ⟨x, .refl⟩ hf
    exact hxb (hxa.tail hab)

theorem root_reach_iff_fiber_cuts (hs : Subrel R (MaxRel n)) :
    (∀ x, Star R x (n x)) ↔ FiberCuts R n := by
  classical
  constructor
  · intro hr r U hU hf _
    exact (root_reach_iff_cuts hs).mp hr U hU hf
  · intro hc x
    apply Classical.byContradiction
    intro hroot
    have hf : RootFree n (fun y => Star R x y) := by
      intro y hxy hy
      have hi := star_invariant n (fun _ _ hp => (hs hp).2) hxy
      exact hroot ((hy.trans hi.symm) ▸ hxy)
    have hi : ∀ y, Star R x y → n y = n x :=
      fun y hy => (star_invariant n (fun _ _ hp => (hs hp).2) hy).symm
    obtain ⟨a, b, hxa, hab, hxb⟩ :=
      hc (n x) (fun y => Star R x y) ⟨x, .refl⟩ hf hi
    exact hxb (hxa.tail hab)

theorem realizes_iff_cuts :
    Realizes R n ↔ Subrel R (MaxRel n) ∧ AllCuts R n := by
  constructor
  · intro h
    exact ⟨h.subrel_maxRel, (root_reach_iff_cuts h.subrel_maxRel).mp h.reaches⟩
  · rintro ⟨hs, hc⟩
    exact realizes_of_subrel_maxRel hs ((root_reach_iff_cuts hs).mpr hc)

theorem realizes_iff_fiber_cuts :
    Realizes R n ↔ Subrel R (MaxRel n) ∧ FiberCuts R n := by
  constructor
  · intro h
    exact ⟨h.subrel_maxRel, (root_reach_iff_fiber_cuts h.subrel_maxRel).mp h.reaches⟩
  · rintro ⟨hs, hc⟩
    exact realizes_of_subrel_maxRel hs ((root_reach_iff_fiber_cuts hs).mpr hc)

theorem not_realizes_iff_closed_rootFree (hs : Subrel R (MaxRel n)) :
    ¬ Realizes R n ↔ ∃ U : X → Prop,
      (∃ x, U x) ∧ RootFree n U ∧ ∀ x y, U x → R x y → U y := by
  classical
  constructor
  · intro hnot
    apply Classical.byContradiction
    intro hnone
    apply hnot
    apply realizes_of_subrel_maxRel hs
    intro x
    apply Classical.byContradiction
    intro hroot
    apply hnone
    refine ⟨fun y => Star R x y, ⟨x, .refl⟩, ?_, ?_⟩
    · intro y hxy hy
      have hi := star_invariant n (fun _ _ hp => (hs hp).2) hxy
      exact hroot ((hy.trans hi.symm) ▸ hxy)
    · intro a b hxa hab
      exact hxa.tail hab
  · rintro ⟨U, hU, hf, hc⟩ hR
    obtain ⟨x, y, hx, hxy, hy⟩ :=
      (root_reach_iff_cuts hs).mp hR.reaches U hU hf
    exact hy (hc x y hx hxy)

end OperatorKO7.Meta.UniqueNormalization.Normalization
