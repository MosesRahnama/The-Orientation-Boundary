import OperatorKO7.Meta.UniqueNormalization.NormalizationCore
import Mathlib.Logic.Equiv.Defs

/-!
# Normalizable domains and internal conversion

Relation: arbitrary R and its restriction to normalizable states.
Property: finite paths, normal forms, WN, UNR and CR.
Proof-graph nodes D and Q. The empty relation supplies a model.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.Normalization

universe u
variable {X : Type u}

def ConvertsToNF (R : X → X → Prop) (x : X) : Prop :=
  ∃ r, NF R r ∧ Conv R x r

def HereditarilyNormalizes (R : X → X → Prop) (x : X) : Prop :=
  ∀ y, Star R x y → Normalizes R y

abbrev NormalizingCarrier (R : X → X → Prop) :=
  {x : X // Normalizes R x}

def NormalizingCore (R : X → X → Prop) :
    NormalizingCarrier R → NormalizingCarrier R → Prop :=
  fun x y => R x.val y.val

def ForwardInvariant (R : X → X → Prop) (P : X → Prop) : Prop :=
  ∀ ⦃x y⦄, P x → R x y → P y

def CRAt (R : X → X → Prop) (x : X) : Prop :=
  ∀ ⦃y z⦄, Star R x y → Star R x z →
    ∃ w, Star R y w ∧ Star R z w

def ReflectsNormalizingConversion (R : X → X → Prop) : Prop :=
  ∀ x y : NormalizingCarrier R,
    Conv R x.val y.val → Conv (NormalizingCore R) x y

variable {R : X → X → Prop} {x y z : X}

theorem core_star_lift (p : Star R x y) :
    ∀ (hy : Normalizes R y) (hx : Normalizes R x),
      Star (NormalizingCore R) ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction p with
  | refl =>
      intro hy hx
      exact .refl
  | @tail b c p h ih =>
      intro hc hx
      have hb : Normalizes R b := normalizes_backward (.single h) hc
      exact (ih hb hx).tail h

theorem core_star_iff {a b : NormalizingCarrier R} :
    Star (NormalizingCore R) a b ↔ Star R a.val b.val := by
  constructor
  · intro p
    exact star_map (fun t : NormalizingCarrier R => t.val)
      (fun {_ _} h => h) p
  · intro p
    exact core_star_lift p b.property a.property

theorem core_conv_project {a b : NormalizingCarrier R}
    (p : Conv (NormalizingCore R) a b) : Conv R a.val b.val :=
  conv_map (fun t : NormalizingCarrier R => t.val)
    (fun {_ _} h => .rel _ _ h) p

theorem core_nf_of_nf {a : NormalizingCarrier R}
    (ha : NF R a.val) : NF (NormalizingCore R) a :=
  fun b hab => ha b.val hab

theorem core_wn (R : X → X → Prop) : WN (NormalizingCore R) := by
  intro a
  obtain ⟨r, hr, har⟩ := a.property
  let b : NormalizingCarrier R := ⟨r, normalizes_of_nf hr⟩
  exact ⟨b, core_nf_of_nf hr, core_star_lift har b.property a.property⟩

theorem core_nf_iff {a : NormalizingCarrier R} :
    NF (NormalizingCore R) a ↔ NF R a.val := by
  constructor
  · intro ha
    obtain ⟨r, hr, har⟩ := a.property
    let b : NormalizingCarrier R := ⟨r, normalizes_of_nf hr⟩
    have hba : b = a :=
      nf_star_eq ha (core_star_lift har b.property a.property)
    have hra : r = a.val := congrArg Subtype.val hba
    exact hra ▸ hr
  · exact core_nf_of_nf

theorem core_unr_of_unr (hu : UNR R) : UNR (NormalizingCore R) := by
  intro a r s hr hs har has
  apply Subtype.ext
  exact hu (core_nf_iff.mp hr) (core_nf_iff.mp hs)
    (core_star_iff.mp har) (core_star_iff.mp has)

theorem unr_of_core_unr (hu : UNR (NormalizingCore R)) : UNR R := by
  intro a r s hr hs har has
  let a' : NormalizingCarrier R := ⟨a, ⟨r, hr, har⟩⟩
  let r' : NormalizingCarrier R := ⟨r, normalizes_of_nf hr⟩
  let s' : NormalizingCarrier R := ⟨s, normalizes_of_nf hs⟩
  have heq : r' = s' := hu (core_nf_of_nf hr) (core_nf_of_nf hs)
    (core_star_lift har r'.property a'.property)
    (core_star_lift has s'.property a'.property)
  exact congrArg Subtype.val heq

theorem unr_iff_core_cr : UNR R ↔ CR (NormalizingCore R) := by
  constructor
  · intro hu
    exact cr_of_wn_unr (core_wn R) (core_unr_of_unr hu)
  · intro hc
    exact unr_of_core_unr (unr_of_unc (unc_of_cr hc))

abbrev NormalFormCarrier (R : X → X → Prop) := {r : X // NF R r}

noncomputable def chosenNF (R : X → X → Prop)
    (a : NormalizingCarrier R) : NormalFormCarrier R :=
  ⟨Classical.choose a.property, (Classical.choose_spec a.property).1⟩

theorem chosenNF_reaches (R : X → X → Prop) (a : NormalizingCarrier R) :
    Star R a.val (chosenNF R a).val :=
  (Classical.choose_spec a.property).2

theorem chosenNF_unique (hu : UNR R) (a : NormalizingCarrier R)
    {r : X} (hr : NF R r) (har : Star R a.val r) :
    (chosenNF R a).val = r :=
  hu (chosenNF R a).property hr (chosenNF_reaches R a) har

theorem chosenNF_step (hu : UNR R) {a b : NormalizingCarrier R}
    (hab : NormalizingCore R a b) : chosenNF R a = chosenNF R b := by
  apply Subtype.ext
  exact chosenNF_unique hu a (chosenNF R b).property
    (.head hab (chosenNF_reaches R b))

theorem chosenNF_eq_iff_core_conv (hu : UNR R)
    (a b : NormalizingCarrier R) :
    chosenNF R a = chosenNF R b ↔ Conv (NormalizingCore R) a b := by
  constructor
  · intro heq
    let r : NormalizingCarrier R :=
      ⟨(chosenNF R a).val, normalizes_of_nf (chosenNF R a).property⟩
    have hbr : Star R b.val r.val := by
      change Star R b.val (chosenNF R a).val
      rw [congrArg Subtype.val heq]
      exact chosenNF_reaches R b
    exact conv_of_join ⟨r,
      core_star_lift (chosenNF_reaches R a) r.property a.property,
      core_star_lift hbr r.property b.property⟩
  · intro hab
    exact conv_invariant (chosenNF R) (fun {_ _} h => chosenNF_step hu h) hab

theorem core_reflection_of_unc (hu : UNC R) :
    ReflectsNormalizingConversion R := by
  intro a b hab
  apply (chosenNF_eq_iff_core_conv (unr_of_unc hu) a b).mp
  apply Subtype.ext
  exact hu (chosenNF R a).property (chosenNF R b).property
    (.trans _ a.val _ (.symm _ _ (conv_of_star (chosenNF_reaches R a)))
      (.trans _ b.val _ hab (conv_of_star (chosenNF_reaches R b))))

theorem unc_iff_core_cr_and_reflection :
    UNC R ↔ CR (NormalizingCore R) ∧ ReflectsNormalizingConversion R := by
  constructor
  · intro hu
    exact ⟨unr_iff_core_cr.mp (unr_of_unc hu), core_reflection_of_unc hu⟩
  · rintro ⟨hc, href⟩
    intro r s hr hs hrs
    let r' : NormalizingCarrier R := ⟨r, normalizes_of_nf hr⟩
    let s' : NormalizingCarrier R := ⟨s, normalizes_of_nf hs⟩
    have heq : r' = s' := (unc_of_cr hc) (core_nf_of_nf hr)
      (core_nf_of_nf hs) (href r' s' hrs)
    exact congrArg Subtype.val heq

theorem core_reflection_iff_unc (hu : UNR R) :
    ReflectsNormalizingConversion R ↔ UNC R :=
  ⟨fun h => unc_iff_core_cr_and_reflection.mpr ⟨unr_iff_core_cr.mp hu, h⟩,
    core_reflection_of_unc⟩

theorem core_conv_iff_of_unc (hu : UNC R) (a b : NormalizingCarrier R) :
    Conv (NormalizingCore R) a b ↔ Conv R a.val b.val :=
  ⟨core_conv_project, core_reflection_of_unc hu a b⟩

theorem convertsToNF_of_normalizes (hx : Normalizes R x) : ConvertsToNF R x := by
  obtain ⟨r, hr, hxr⟩ := hx
  exact ⟨r, hr, conv_of_star hxr⟩

theorem convertsToNF_of_conv (hxy : Conv R x y) (hy : ConvertsToNF R y) :
    ConvertsToNF R x := by
  obtain ⟨r, hr, hyr⟩ := hy
  exact ⟨r, hr, .trans x y r hxy hyr⟩

theorem convertsToNF_conv_iff (hxy : Conv R x y) :
    ConvertsToNF R x ↔ ConvertsToNF R y :=
  ⟨convertsToNF_of_conv (.symm x y hxy), convertsToNF_of_conv hxy⟩

theorem hereditary_normalizes_self (hx : HereditarilyNormalizes R x) :
    Normalizes R x := hx x .refl

theorem hereditary_forward_star (hx : HereditarilyNormalizes R x)
    (hxy : Star R x y) : HereditarilyNormalizes R y :=
  fun z hyz => hx z (hxy.trans hyz)

theorem hereditary_forward_invariant (R : X → X → Prop) :
    ForwardInvariant R (HereditarilyNormalizes R) :=
  fun {_ _} hx hxy => hereditary_forward_star hx (.single hxy)

theorem forwardInvariant_star {P : X → Prop}
    (hi : ForwardInvariant R P) (hxy : Star R x y) (hx : P x) : P y := by
  induction hxy with
  | refl => exact hx
  | tail _ h ih => exact hi ih h

theorem hereditary_greatest {P : X → Prop}
    (hn : ∀ x, P x → Normalizes R x) (hi : ForwardInvariant R P) :
    ∀ x, P x → HereditarilyNormalizes R x :=
  fun _ hx y hxy => hn y (forwardInvariant_star hi hxy hx)

theorem normalizes_conv_iff_of_forward_invariant
    (hi : ForwardInvariant R (Normalizes R)) (hxy : Conv R x y) :
    Normalizes R x ↔ Normalizes R y := by
  have heq : Normalizes R x = Normalizes R y :=
    conv_invariant (Normalizes R)
      (fun {_ _} h => propext ⟨fun ha => hi ha h,
        fun hb => normalizes_backward (.single h) hb⟩) hxy
  constructor
  · intro hx; exact heq ▸ hx
  · intro hy; exact heq.symm ▸ hy

theorem hereditary_eq_normalizes_iff :
    HereditarilyNormalizes R = Normalizes R ↔
      Normalizes R = ConvertsToNF R := by
  constructor
  · intro hdn
    have hi : ForwardInvariant R (Normalizes R) := by
      intro a b ha hab
      have hd : HereditarilyNormalizes R a := by rw [hdn]; exact ha
      exact hd b (.single hab)
    funext a
    apply propext
    constructor
    · exact convertsToNF_of_normalizes
    · rintro ⟨r, hr, har⟩
      exact (normalizes_conv_iff_of_forward_invariant hi har).mpr
        (normalizes_of_nf hr)
  · intro hnc
    funext a
    apply propext
    constructor
    · exact hereditary_normalizes_self
    · intro ha b hab
      have hac : ConvertsToNF R a := by rw [← hnc]; exact ha
      rw [hnc]
      exact convertsToNF_of_conv (.symm a b (conv_of_star hab)) hac

theorem hereditary_iff_normalizes_and_crAt (hu : UNR R) :
    HereditarilyNormalizes R x ↔ Normalizes R x ∧ CRAt R x := by
  constructor
  · intro hd
    refine ⟨hereditary_normalizes_self hd, ?_⟩
    intro y z hxy hxz
    obtain ⟨r, hr, hyr⟩ := hd y hxy
    obtain ⟨s, hs, hzs⟩ := hd z hxz
    have hrs : r = s := hu hr hs (hxy.trans hyr) (hxz.trans hzs)
    subst s
    exact ⟨r, hyr, hzs⟩
  · rintro ⟨⟨r, hr, hxr⟩, hc⟩ y hxy
    obtain ⟨w, hyw, hrw⟩ := hc hxy hxr
    have hwr := nf_star_eq hr hrw
    subst w
    exact ⟨r, hr, hyw⟩

theorem normalizes_eq_convertsToNF_of_nfp (hn : NFP R) :
    Normalizes R = ConvertsToNF R := by
  funext a
  apply propext
  constructor
  · exact convertsToNF_of_normalizes
  · rintro ⟨r, hr, har⟩
    exact ⟨r, hr, hn hr har⟩

theorem nfp_iff_normalizes_eq_convertsToNF (hu : UNC R) :
    NFP R ↔ Normalizes R = ConvertsToNF R := by
  constructor
  · exact normalizes_eq_convertsToNF_of_nfp
  · intro hnc a r hr har
    have ha : Normalizes R a := by
      rw [hnc]
      exact ⟨r, hr, har⟩
    obtain ⟨s, hs, has⟩ := ha
    have hsr : s = r := hu hs hr
      (.trans s a r (.symm a s (conv_of_star has)) har)
    subst s
    exact has

theorem nfp_iff_hereditary_eq_normalizes (hu : UNC R) :
    NFP R ↔ HereditarilyNormalizes R = Normalizes R :=
  (nfp_iff_normalizes_eq_convertsToNF hu).trans hereditary_eq_normalizes_iff.symm

theorem nf_hereditarily_normalizes (hx : NF R x) :
    HereditarilyNormalizes R x := by
  intro y hxy
  have hyx := nf_star_eq hx hxy
  subst y
  exact normalizes_of_nf hx

abbrev ConvertibleCarrier (R : X → X → Prop) := {x : X // ConvertsToNF R x}

def ConvertibleRestriction (R S : X → X → Prop) :
    ConvertibleCarrier R → ConvertibleCarrier R → Prop :=
  fun x y => S x.val y.val

noncomputable def classNF (R : X → X → Prop)
    (a : ConvertibleCarrier R) : NormalFormCarrier R :=
  ⟨Classical.choose a.property, (Classical.choose_spec a.property).1⟩

theorem classNF_converts (R : X → X → Prop) (a : ConvertibleCarrier R) :
    Conv R a.val (classNF R a).val := (Classical.choose_spec a.property).2

theorem classNF_unique (hu : UNC R) (a : ConvertibleCarrier R)
    {r : X} (hr : NF R r) (har : Conv R a.val r) :
    (classNF R a).val = r :=
  hu (classNF R a).property hr
    (.trans _ a.val r (.symm _ _ (classNF_converts R a)) har)

theorem classNF_eq_iff_conv (hu : UNC R) (a b : ConvertibleCarrier R) :
    classNF R a = classNF R b ↔ Conv R a.val b.val := by
  constructor
  · intro heq
    have hbr : Conv R b.val (classNF R a).val := by
      rw [congrArg Subtype.val heq]
      exact classNF_converts R b
    exact .trans _ _ _ (classNF_converts R a) (.symm _ _ hbr)
  · intro hab
    apply Subtype.ext
    exact classNF_unique hu a (classNF R b).property
      (.trans _ _ _ hab (classNF_converts R b))

theorem classNF_eq_self_iff (hu : UNC R) (a : ConvertibleCarrier R) :
    (classNF R a).val = a.val ↔ NF R a.val := by
  constructor
  · intro h; exact h ▸ (classNF R a).property
  · intro h; exact classNF_unique hu a h (.refl _)

noncomputable def classLabel (R : X → X → Prop)
    (a : ConvertibleCarrier R) : ConvertibleCarrier R :=
  ⟨(classNF R a).val, ⟨(classNF R a).val, (classNF R a).property, .refl _⟩⟩

theorem classLabel_eq_iff_conv (hu : UNC R) (a b : ConvertibleCarrier R) :
    classLabel R a = classLabel R b ↔ Conv R a.val b.val := by
  constructor
  · intro h
    apply (classNF_eq_iff_conv hu a b).mp
    apply Subtype.ext
    exact congrArg (fun t : ConvertibleCarrier R => t.val) h
  · intro h
    apply Subtype.ext
    exact congrArg (fun t : NormalFormCarrier R => t.val)
      ((classNF_eq_iff_conv hu a b).mpr h)

theorem classLabel_fixed_iff (hu : UNC R) (a : ConvertibleCarrier R) :
    NF R a.val ↔ a = classLabel R a := by
  constructor
  · intro h
    apply Subtype.ext
    exact ((classNF_eq_self_iff hu a).mpr h).symm
  · intro h
    apply (classNF_eq_self_iff hu a).mp
    exact (congrArg Subtype.val h).symm

theorem classLabel_idempotent (hu : UNC R) :
    ∀ a : ConvertibleCarrier R, classLabel R (classLabel R a) = classLabel R a := by
  intro a
  apply Subtype.ext
  exact classNF_unique hu (classLabel R a) (classNF R a).property (.refl _)

def conversionSetoid (R : X → X → Prop) : Setoid X where
  r := Conv R
  iseqv := ⟨fun a => .refl a, fun h => .symm _ _ h,
    fun h₁ h₂ => .trans _ _ _ h₁ h₂⟩

def ambientNormalSetoid (R : X → X → Prop) : Setoid (ConvertibleCarrier R) where
  r := fun a b => Conv R a.val b.val
  iseqv := ⟨fun a => .refl a.val, fun h => .symm _ _ h,
    fun h₁ h₂ => .trans _ _ _ h₁ h₂⟩

abbrev CoreQuotient (R : X → X → Prop) :=
  Quotient (conversionSetoid (NormalizingCore R))

abbrev AmbientNormalQuotient (R : X → X → Prop) :=
  Quotient (ambientNormalSetoid R)

def normalizingToConvertible (R : X → X → Prop)
    (a : NormalizingCarrier R) : ConvertibleCarrier R :=
  ⟨a.val, convertsToNF_of_normalizes a.property⟩

def normalFormToCoreQuotient (R : X → X → Prop)
    (r : NormalFormCarrier R) : CoreQuotient R :=
  Quotient.mk _ ⟨r.val, normalizes_of_nf r.property⟩

def coreToAmbientQuotient (R : X → X → Prop) :
    CoreQuotient R → AmbientNormalQuotient R :=
  Quotient.lift
    (fun a => Quotient.mk _ (normalizingToConvertible R a))
    (by
      intro a b hab
      apply Quotient.sound
      exact core_conv_project hab)

def normalFormToAmbientQuotient (R : X → X → Prop) :
    NormalFormCarrier R → AmbientNormalQuotient R :=
  fun r => coreToAmbientQuotient R (normalFormToCoreQuotient R r)

theorem quotient_maps_compose (R : X → X → Prop) :
    normalFormToAmbientQuotient R =
      coreToAmbientQuotient R ∘ normalFormToCoreQuotient R := rfl

theorem normalFormToCoreQuotient_surjective (R : X → X → Prop) :
    Function.Surjective (normalFormToCoreQuotient R) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro a
  obtain ⟨r, hr, har⟩ := a.property
  refine ⟨⟨r, hr⟩, ?_⟩
  apply Quotient.sound
  exact .symm a ⟨r, normalizes_of_nf hr⟩
    (conv_of_star (core_star_lift har (normalizes_of_nf hr) a.property))

theorem coreToAmbientQuotient_surjective (R : X → X → Prop) :
    Function.Surjective (coreToAmbientQuotient R) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro a
  obtain ⟨r, hr, har⟩ := a.property
  refine ⟨normalFormToCoreQuotient R ⟨r, hr⟩, ?_⟩
  apply Quotient.sound
  exact .symm a.val r har

theorem normalFormToAmbientQuotient_surjective (R : X → X → Prop) :
    Function.Surjective (normalFormToAmbientQuotient R) := by
  intro q
  obtain ⟨p, hp⟩ := coreToAmbientQuotient_surjective R q
  obtain ⟨r, hr⟩ := normalFormToCoreQuotient_surjective R p
  exact ⟨r, (congrArg (coreToAmbientQuotient R) hr).trans hp⟩

theorem normalFormToCoreQuotient_injective_iff :
    Function.Injective (normalFormToCoreQuotient R) ↔ UNR R := by
  constructor
  · intro hi a r s hr hs har has
    have ha : Normalizes R a := ⟨r, hr, har⟩
    have har' : Star (NormalizingCore R) ⟨a, ha⟩
        ⟨r, normalizes_of_nf hr⟩ :=
      core_star_lift har (normalizes_of_nf hr) ha
    have has' : Star (NormalizingCore R) ⟨a, ha⟩
        ⟨s, normalizes_of_nf hs⟩ :=
      core_star_lift has (normalizes_of_nf hs) ha
    have heq : normalFormToCoreQuotient R ⟨r, hr⟩ =
        normalFormToCoreQuotient R ⟨s, hs⟩ := by
      apply Quotient.sound
      exact .trans _ _ _ (.symm _ _ (conv_of_star har')) (conv_of_star has')
    exact congrArg Subtype.val (hi heq)
  · intro hu a b hab
    apply Subtype.ext
    have hc : CR (NormalizingCore R) := unr_iff_core_cr.mp hu
    have heq := unc_of_cr hc (core_nf_of_nf a.property)
      (core_nf_of_nf b.property) (Quotient.exact hab)
    exact congrArg (fun t : NormalizingCarrier R => t.val) heq

theorem coreToAmbientQuotient_injective_iff :
    Function.Injective (coreToAmbientQuotient R) ↔
      ReflectsNormalizingConversion R := by
  constructor
  · intro hi a b hab
    have heq : coreToAmbientQuotient R (Quotient.mk _ a) =
        coreToAmbientQuotient R (Quotient.mk _ b) := by
      apply Quotient.sound
      exact hab
    exact Quotient.exact (hi heq)
  · intro hr p q
    refine Quotient.inductionOn₂ p q ?_
    intro a b hab
    apply Quotient.sound
    exact hr a b (Quotient.exact hab)

theorem normalFormToAmbientQuotient_injective_iff :
    Function.Injective (normalFormToAmbientQuotient R) ↔ UNC R := by
  constructor
  · intro hi a b ha hb hab
    have heq : normalFormToAmbientQuotient R ⟨a, ha⟩ =
        normalFormToAmbientQuotient R ⟨b, hb⟩ := by
      apply Quotient.sound
      exact hab
    exact congrArg Subtype.val (hi heq)
  · intro hu a b hab
    apply Subtype.ext
    exact hu a.property b.property (Quotient.exact hab)

noncomputable def normalFormCoreEquiv (hu : UNR R) :
    NormalFormCarrier R ≃ CoreQuotient R :=
  Equiv.ofBijective (normalFormToCoreQuotient R)
    ⟨normalFormToCoreQuotient_injective_iff.mpr hu,
      normalFormToCoreQuotient_surjective R⟩

noncomputable def coreAmbientEquiv (hu : UNC R) :
    CoreQuotient R ≃ AmbientNormalQuotient R :=
  Equiv.ofBijective (coreToAmbientQuotient R)
    ⟨coreToAmbientQuotient_injective_iff.mpr (core_reflection_of_unc hu),
      coreToAmbientQuotient_surjective R⟩

noncomputable def normalFormAmbientEquiv (hu : UNC R) :
    NormalFormCarrier R ≃ AmbientNormalQuotient R :=
  Equiv.ofBijective (normalFormToAmbientQuotient R)
    ⟨normalFormToAmbientQuotient_injective_iff.mpr hu,
      normalFormToAmbientQuotient_surjective R⟩

end OperatorKO7.Meta.UniqueNormalization.Normalization
