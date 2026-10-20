import OperatorKO7.Meta.UniqueNormalization.NormalizerRealization
import OperatorKO7.Meta.UniqueNormalization.NormalizerForests
import OperatorKO7.Meta.UniqueNormalization.NormalizationDomains
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Hom.Basic

/-!
# Observation on attained images and transport of normalization
Relation: arbitrary source and target reductions. Observation is relative to
a specified target, and normalization transport separates source normal forms
after target normalization. Conjugation uses an explicit carrier equivalence.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.Normalization

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}

/-- The actual image, with no arbitrary values assigned off the image. -/
def Attained (q : X → Y) := {y : Y // ∃ x, q x = y}

def attained (q : X → Y) (x : X) : Attained q := ⟨q x, x, rfl⟩

theorem attained_surjective (q : X → Y) : Function.Surjective (attained q) := by
  rintro ⟨y, x, rfl⟩
  exact ⟨x, rfl⟩

/-- A target can be recovered exactly when equal observations have equal targets. -/
theorem image_decoder_iff (q : X → Y) (g : X → Z) :
    (∃! d : Attained q → Z, ∀ x, d (attained q x) = g x) ↔
    ∀ x y, q x = q y → g x = g y := by
  classical
  constructor
  · rintro ⟨d, hd, _⟩ x y hxy
    have h : attained q x = attained q y := Subtype.ext hxy
    exact (hd x).symm.trans ((congrArg d h).trans (hd y))
  · intro h
    let d : Attained q → Z := fun a => g (Classical.choose a.property)
    have hd : ∀ x, d (attained q x) = g x := by
      intro x
      exact h _ x (Classical.choose_spec (attained q x).property)
    refine ⟨d, hd, ?_⟩
    intro e he
    funext a
    obtain ⟨x, rfl⟩ := attained_surjective q a
    exact (he x).trans (hd x).symm

theorem identity_decoder_iff (q : X → Y) :
    (∃! d : Attained q → X, ∀ x, d (attained q x) = x) ↔
    Function.Injective q := image_decoder_iff q id

/-- Invariance is needed for bijection with the target, in addition to recovery. -/
noncomputable def observation_equiv_fixed
    (n : X → X) (hn : ∀ x, n (n x) = n x) (q : X → Y)
    (hq : ∀ x, q (n x) = q x)
    (hadequate : ∀ x y, q x = q y → n x = n y) :
    Attained q ≃ {r : X // n r = r} where
  toFun a := ⟨n (Classical.choose a.property), hn _⟩
  invFun r := attained q r.val
  left_inv a := by
    apply Subtype.ext
    exact (hq _).trans (Classical.choose_spec a.property)
  right_inv r := by
    apply Subtype.ext
    exact (hadequate _ r.val (Classical.choose_spec (attained q r.val).property)).trans r.property

theorem invariant_adequacy_iff_kernel
    {R : X → X → Prop} (n : X → X) (q : X → Y)
    (hk : ∀ x y, n x = n y ↔ Conv R x y)
    (hi : ∀ ⦃x y⦄, R x y → q x = q y) :
    (∀ x y, q x = q y → n x = n y) ↔
    (∀ x y, q x = q y ↔ Conv R x y) := by
  constructor
  · intro ha x y
    exact ⟨fun h => (hk x y).mp (ha x y h), fun h => conv_invariant q hi h⟩
  · intro he x y h
    exact (hk x y).mpr ((he x y).mp h)

/-- Recovery is formulated on the actual normalizable carrier and actual image. -/
theorem normal_form_decoder_iff {R : X → X → Prop} (hu : UNR R)
    (q : NormalizingCarrier R → Y) :
    (∃! d : Attained q → NormalFormCarrier R,
      ∀ a, d (attained q a) = chosenNF R a) ↔
    ∀ a b, q a = q b → Conv (NormalizingCore R) a b := by
  rw [image_decoder_iff]
  constructor
  · intro ha a b hab
    exact (chosenNF_eq_iff_core_conv hu a b).mp (ha a b hab)
  · intro ha a b hab
    exact (chosenNF_eq_iff_core_conv hu a b).mpr (ha a b hab)

theorem invariant_normal_form_decoder_iff {R : X → X → Prop} (hu : UNR R)
    (q : NormalizingCarrier R → Y)
    (hi : ∀ ⦃a b⦄, NormalizingCore R a b → q a = q b) :
    (∃! d : Attained q → NormalFormCarrier R,
      ∀ a, d (attained q a) = chosenNF R a) ↔
    ∀ a b, q a = q b ↔ Conv (NormalizingCore R) a b := by
  rw [normal_form_decoder_iff hu]
  constructor
  · intro ha a b
    exact ⟨ha a b, fun hab => conv_invariant q hi hab⟩
  · intro ha a b hab
    exact (ha a b).mp hab

/-- Ambient conversion replaces internal conversion uniformly exactly under UNC. -/
theorem normal_form_ambient_replacement_iff {R : X → X → Prop} (hu : UNR R) :
    (∀ a b : NormalizingCarrier R,
      Conv (NormalizingCore R) a b ↔ Conv R a.val b.val) ↔ UNC R := by
  constructor
  · intro he
    apply (core_reflection_iff_unc hu).mp
    intro a b hab
    exact (he a b).mpr hab
  · exact core_conv_iff_of_unc

theorem chosenNF_of_normal {R : X → X → Prop} (r : NormalFormCarrier R) :
    chosenNF R ⟨r.val, normalizes_of_nf r.property⟩ = r := by
  apply Subtype.ext
  exact nf_star_eq r.property
    (chosenNF_reaches R ⟨r.val, normalizes_of_nf r.property⟩)

/-- The inverse is the observation of a normal form itself. -/
noncomputable def normalFormObservationEquiv {R : X → X → Prop} (hu : UNR R)
    (q : NormalizingCarrier R → Y)
    (hi : ∀ ⦃a b⦄, NormalizingCore R a b → q a = q b)
    (ha : ∀ a b, q a = q b → Conv (NormalizingCore R) a b) :
    Attained q ≃ NormalFormCarrier R where
  toFun a := chosenNF R (Classical.choose a.property)
  invFun r := attained q ⟨r.val, normalizes_of_nf r.property⟩
  left_inv a := by
    apply Subtype.ext
    let x := Classical.choose a.property
    let r : NormalizingCarrier R :=
      ⟨(chosenNF R x).val, normalizes_of_nf (chosenNF R x).property⟩
    have hp : Star (NormalizingCore R) x r :=
      core_star_lift (chosenNF_reaches R x) r.property x.property
    exact (star_invariant q hi hp).symm.trans (Classical.choose_spec a.property)
  right_inv r := by
    have he := (chosenNF_eq_iff_core_conv hu
      (Classical.choose (attained q ⟨r.val, normalizes_of_nf r.property⟩).property)
      ⟨r.val, normalizes_of_nf r.property⟩).mpr
      (ha _ _ (Classical.choose_spec
        (attained q ⟨r.val, normalizes_of_nf r.property⟩).property))
    exact he.trans (chosenNF_of_normal r)

theorem normalFormObservationEquiv_apply {R : X → X → Prop} (hu : UNR R)
    (q : NormalizingCarrier R → Y)
    (hi : ∀ ⦃a b⦄, NormalizingCore R a b → q a = q b)
    (ha : ∀ a b, q a = q b → Conv (NormalizingCore R) a b)
    (x : NormalizingCarrier R) :
    normalFormObservationEquiv hu q hi ha (attained q x) = chosenNF R x :=
  (chosenNF_eq_iff_core_conv hu _ x).mpr
    (ha _ x (Classical.choose_spec (attained q x).property))

/-- A target invariant need not leave the image of source normal forms fixed. -/
theorem unc_of_normalized_transport
    {R : X → X → Prop} {S : Y → Y → Prop} (f : X → Y) (n : Y → Z)
    (hf : ∀ ⦃x y⦄, R x y → Star S (f x) (f y))
    (hn : ∀ ⦃a b⦄, S a b → n a = n b)
    (hsep : ∀ ⦃r s⦄, NF R r → NF R s → n (f r) = n (f s) → r = s) :
    UNC R := by
  intro r s hr hs hrs
  apply hsep hr hs
  exact conv_invariant (fun x => n (f x)) (fun {_ _} h => star_invariant n hn (hf h)) hrs

theorem cr_of_normalized_transport
    {R : X → X → Prop} {S : Y → Y → Prop} (f : X → Y) (n : Y → Z)
    (hw : WN R)
    (hf : ∀ ⦃x y⦄, R x y → Star S (f x) (f y))
    (hn : ∀ ⦃a b⦄, S a b → n a = n b)
    (hsep : ∀ ⦃r s⦄, NF R r → NF R s → n (f r) = n (f s) → r = s) :
    CR R := cr_of_wn_unr hw (unr_of_unc (unc_of_normalized_transport f n hf hn hsep))

/-- Transport of the actual edge relation through a carrier equivalence. -/
def Conjugate (h : X ≃ Y) (R : X → X → Prop) (a b : Y) : Prop :=
  R (h.symm a) (h.symm b)

def ConjugateMap (h : X ≃ Y) (n : X → X) (y : Y) : Y :=
  h (n (h.symm y))

theorem conjugate_apply (h : X ≃ Y) (R : X → X → Prop) (x y : X) :
    Conjugate h R (h x) (h y) ↔ R x y := by
  simp [Conjugate]

theorem conjugate_star (h : X ≃ Y) (R : X → X → Prop) (a b : Y) :
    Star (Conjugate h R) a b ↔ Star R (h.symm a) (h.symm b) := by
  constructor
  · exact star_map h.symm (fun {_ _} hp => hp)
  · intro hp
    have ht := star_map h (fun {x y} hx => (conjugate_apply h R x y).mpr hx) hp
    simpa using ht

theorem conjugate_conv (h : X ≃ Y) (R : X → X → Prop) (a b : Y) :
    Conv (Conjugate h R) a b ↔ Conv R (h.symm a) (h.symm b) := by
  constructor
  · exact conv_map h.symm (fun {_ _} hp => .rel _ _ hp)
  · intro hp
    have ht := conv_map h
      (fun {x y} hx => Relation.EqvGen.rel _ _ ((conjugate_apply h R x y).mpr hx)) hp
    simpa using ht

theorem conjugate_nf (h : X ≃ Y) (R : X → X → Prop) (a : Y) :
    NF (Conjugate h R) a ↔ NF R (h.symm a) := by
  constructor
  · intro ha x hx
    apply ha (h x)
    simpa [Conjugate] using hx
  · intro ha b hab
    exact ha (h.symm b) hab

theorem conjugate_saturate (h : X ≃ Y) (R : X → X → Prop) :
    Conjugate h (Saturate R) = Saturate (Conjugate h R) := by
  funext a b
  change (¬ NF R (h.symm a) ∧ Conv R (h.symm a) (h.symm b)) =
    (¬ NF (Conjugate h R) a ∧ Conv (Conjugate h R) a b)
  rw [conjugate_nf, conjugate_conv]

theorem conjugate_cr (h : X ≃ Y) (R : X → X → Prop) :
    CR (Conjugate h R) ↔ CR R := by
  constructor
  · intro hc x y z hxy hxz
    have hxy' : Star (Conjugate h R) (h x) (h y) :=
      (conjugate_star h R _ _).mpr (by simpa using hxy)
    have hxz' : Star (Conjugate h R) (h x) (h z) :=
      (conjugate_star h R _ _).mpr (by simpa using hxz)
    obtain ⟨w, hyw, hzw⟩ := hc hxy' hxz'
    exact ⟨h.symm w, by simpa using (conjugate_star h R _ _).mp hyw,
      by simpa using (conjugate_star h R _ _).mp hzw⟩
  · intro hc x y z hxy hxz
    obtain ⟨w, hyw, hzw⟩ :=
      hc ((conjugate_star h R _ _).mp hxy) ((conjugate_star h R _ _).mp hxz)
    exact ⟨h w, (conjugate_star h R _ _).mpr (by simpa using hyw),
      (conjugate_star h R _ _).mpr (by simpa using hzw)⟩

theorem conjugate_acc (h : X ≃ Y) (R : X → X → Prop) (a : Y)
    (ha : Acc (fun y x => R x y) (h.symm a)) :
    Acc (fun y x => Conjugate h R x y) a := by
  generalize he : h.symm a = x at ha
  induction ha generalizing a with
  | intro x _ ih =>
      apply Acc.intro
      intro b hab
      apply ih (h.symm b)
      · simpa [Conjugate, he] using hab
      · rfl

theorem conjugate_sn (h : X ≃ Y) (R : X → X → Prop) :
    SN (Conjugate h R) ↔ SN R := by
  constructor
  · intro hs
    have hh : Conjugate h.symm (Conjugate h R) = R := by
      funext x y
      simp [Conjugate]
    rw [← hh]
    exact ⟨fun x => conjugate_acc h.symm (Conjugate h R) x (hs.apply (h x))⟩
  · intro hs
    exact ⟨fun a => conjugate_acc h R a (hs.apply (h.symm a))⟩

theorem conjugate_subrel (h : X ≃ Y) (R S : X → X → Prop) :
    Subrel (Conjugate h R) (Conjugate h S) ↔ Subrel R S := by
  constructor
  · intro ht x y hxy
    exact (conjugate_apply h S x y).mp (ht ((conjugate_apply h R x y).mpr hxy))
  · intro ht _ _ hxy
    exact ht hxy

def relationConjugacy (h : X ≃ Y) : (X → X → Prop) ≃o (Y → Y → Prop) where
  toFun := Conjugate h
  invFun := Conjugate h.symm
  left_inv R := by
    funext x y
    simp [Conjugate]
  right_inv S := by
    funext x y
    simp [Conjugate]
  map_rel_iff' := by
    intro R S
    exact conjugate_subrel h R S


/-- The path and normality requirements of realization both transport. -/
theorem conjugate_realizes (h : X ≃ Y) (R : X → X → Prop) (n : X → X) :
    Realizes (Conjugate h R) (ConjugateMap h n) ↔ Realizes R n := by
  constructor
  · rintro ⟨hc, hn⟩
    refine ⟨(conjugate_cr h R).mp hc, ?_⟩
    intro x
    obtain ⟨hp, hf⟩ := hn (h x)
    constructor
    · simpa [ConjugateMap] using (conjugate_star h R _ _).mp hp
    · simpa [ConjugateMap] using (conjugate_nf h R _).mp hf
  · rintro ⟨hc, hn⟩
    refine ⟨(conjugate_cr h R).mpr hc, ?_⟩
    intro y
    obtain ⟨hp, hf⟩ := hn (h.symm y)
    constructor
    · apply (conjugate_star h R _ _).mpr
      simpa [ConjugateMap] using hp
    · apply (conjugate_nf h R _).mpr
      simpa [ConjugateMap] using hf

theorem conjugate_map_eq (h : X ≃ Y) (n : X → X) (m : Y → Y)
    (hc : ∀ x, h (n x) = m (h x)) : ConjugateMap h n = m := by
  funext y
  simpa [ConjugateMap] using hc (h.symm y)

theorem conjugacy_symm (h : X ≃ Y) (n : X → X) (m : Y → Y)
    (hc : ∀ x, h (n x) = m (h x)) :
    ∀ y, h.symm (m y) = n (h.symm y) := by
  intro y
  apply h.injective
  simpa using (hc (h.symm y)).symm

theorem realizes_conjugate_iff (h : X ≃ Y) (n : X → X) (m : Y → Y)
    (hc : ∀ x, h (n x) = m (h x)) (R : X → X → Prop) :
    Realizes (Conjugate h R) m ↔ Realizes R n := by
  rw [← conjugate_map_eq h n m hc]
  exact conjugate_realizes h R n

/-- An explicit order isomorphism of the complete realizing-relation families. -/
def realizationConjugacy (h : X ≃ Y) (n : X → X) (m : Y → Y)
    (hc : ∀ x, h (n x) = m (h x)) :
    {R : X → X → Prop // Realizes R n} ≃o
      {S : Y → Y → Prop // Realizes S m} where
  toFun R := ⟨Conjugate h R.val, (realizes_conjugate_iff h n m hc R.val).mpr R.property⟩
  invFun S := ⟨Conjugate h.symm S.val,
    (realizes_conjugate_iff h.symm m n (conjugacy_symm h n m hc) S.val).mpr S.property⟩
  left_inv R := by
    apply Subtype.ext
    funext x y
    simp [Conjugate]
  right_inv S := by
    apply Subtype.ext
    funext x y
    simp [Conjugate]
  map_rel_iff' := by
    intro R S
    exact conjugate_subrel h R.val S.val

theorem conjugate_max_rel (h : X ≃ Y) (n : X → X) (m : Y → Y)
    (hc : ∀ x, h (n x) = m (h x)) :
    Conjugate h (MaxRel n) = MaxRel m := by
  funext a b
  apply propext
  constructor
  · rintro ⟨hne, he⟩
    constructor
    · intro haf
      apply hne
      apply h.injective
      simpa [hc] using haf
    · have hh := congrArg h he
      simpa [hc] using hh
  · rintro ⟨hne, he⟩
    constructor
    · intro haf
      apply hne
      have hh := congrArg h haf
      simpa [hc] using hh
    · apply h.injective
      simpa [hc] using he

/-- Edge conjugation preserves the actual length of every finite path. -/
theorem conjugate_pathLen (h : X ≃ Y) (R : X → X → Prop)
    (k : Nat) (a b : Y) :
    PathLen (Conjugate h R) k a b ↔ PathLen R k (h.symm a) (h.symm b) := by
  constructor
  · exact PathLen.map h.symm (fun {_ _} hp => hp)
  · intro hp
    have ht := PathLen.map h
      (fun {x y} hx => (conjugate_apply h R x y).mpr hx) hp
    simpa using ht

/-- The distance statement also covers the defined zero value for absent paths. -/
theorem conjugate_rootDistance (h : X ≃ Y) (R : X → X → Prop)
    (n : X → X) (a : Y) :
    RootDistance (Conjugate h R) (ConjugateMap h n) a =
      RootDistance R n (h.symm a) := by
  classical
  simp only [RootDistance, conjugate_pathLen, ConjugateMap, Equiv.symm_apply_apply]

theorem conjugate_shortestRel (h : X ≃ Y) (R : X → X → Prop)
    (n : X → X) :
    Conjugate h (ShortestRel R n) =
      ShortestRel (Conjugate h R) (ConjugateMap h n) := by
  funext a b
  change (R (h.symm a) (h.symm b) ∧
    RootDistance R n (h.symm a) = RootDistance R n (h.symm b) + 1) =
    (Conjugate h R a b ∧ RootDistance (Conjugate h R) (ConjugateMap h n) a =
      RootDistance (Conjugate h R) (ConjugateMap h n) b + 1)
  rw [conjugate_rootDistance, conjugate_rootDistance]
  rfl

theorem conjugate_rootDistance_of_intertwining (h : X ≃ Y)
    (R : X → X → Prop) (n : X → X) (m : Y → Y)
    (hc : ∀ x, h (n x) = m (h x)) (a : Y) :
    RootDistance (Conjugate h R) m a = RootDistance R n (h.symm a) := by
  rw [← conjugate_map_eq h n m hc]
  exact conjugate_rootDistance h R n a

theorem conjugate_shortestRel_of_intertwining (h : X ≃ Y)
    (R : X → X → Prop) (n : X → X) (m : Y → Y)
    (hc : ∀ x, h (n x) = m (h x)) :
    Conjugate h (ShortestRel R n) = ShortestRel (Conjugate h R) m := by
  rw [← conjugate_map_eq h n m hc]
  exact conjugate_shortestRel h R n

theorem conjugate_functional (h : X ≃ Y) (R : X → X → Prop) :
    FunctionalRel (Conjugate h R) ↔ FunctionalRel R := by
  constructor
  · intro hf x y z hxy hxz
    apply h.injective
    exact hf ((conjugate_apply h R x y).mpr hxy)
      ((conjugate_apply h R x z).mpr hxz)
  · intro hf a b c hab hac
    apply h.symm.injective
    exact hf hab hac

theorem conjugate_minimalRealizes (h : X ≃ Y) (n : X → X) (m : Y → Y)
    (hc : ∀ x, h (n x) = m (h x)) (R : X → X → Prop) :
    MinimalRealizes (Conjugate h R) m ↔ MinimalRealizes R n := by
  rw [minimalRealizes_iff, minimalRealizes_iff,
    realizes_conjugate_iff h n m hc, conjugate_functional]

theorem conjugate_leastRealizes (h : X ≃ Y) (n : X → X) (m : Y → Y)
    (hc : ∀ x, h (n x) = m (h x)) (R : X → X → Prop) :
    LeastRealizes (Conjugate h R) m ↔ LeastRealizes R n := by
  constructor
  · rintro ⟨hR, hl⟩
    refine ⟨(realizes_conjugate_iff h n m hc R).mp hR, ?_⟩
    intro S hS
    exact (conjugate_subrel h R S).mp
      (hl (Conjugate h S) ((realizes_conjugate_iff h n m hc S).mpr hS))
  · rintro ⟨hR, hl⟩
    refine ⟨(realizes_conjugate_iff h n m hc R).mpr hR, ?_⟩
    intro S hS a b hab
    have hs : Realizes (Conjugate h.symm S) n :=
      (realizes_conjugate_iff h.symm m n (conjugacy_symm h n m hc) S).mpr hS
    have he := hl (Conjugate h.symm S) hs hab
    simpa only [Conjugate, Equiv.symm_symm, Equiv.apply_symm_apply] using he

theorem conjugate_exists_leastRealizes (h : X ≃ Y) (n : X → X) (m : Y → Y)
    (hc : ∀ x, h (n x) = m (h x)) :
    (∃ R : X → X → Prop, LeastRealizes R n) ↔
      ∃ S : Y → Y → Prop, LeastRealizes S m := by
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨Conjugate h R, (conjugate_leastRealizes h n m hc R).mpr hR⟩
  · rintro ⟨S, hS⟩
    exact ⟨Conjugate h.symm S,
      (conjugate_leastRealizes h.symm m n (conjugacy_symm h n m hc) S).mpr hS⟩

end OperatorKO7.Meta.UniqueNormalization.Normalization

