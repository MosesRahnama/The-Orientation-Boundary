import OperatorKO7.Meta.UniqueNormalization.NormalizationDomains

/-!
# Conversion saturation with preserved normal forms

The saturation adds every conversion edge whose source is not normal.
It preserves precisely the original normal forms and conversion classes.
All declarations concern arbitrary binary relations.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.Normalization

universe u v
variable {X : Type u} {Y : Type v}
variable {R S T : X → X → Prop} {x y z : X}

def Saturate (R : X → X → Prop) (x y : X) : Prop :=
  ¬ NF R x ∧ Conv R x y

theorem sat_iff : Saturate R x y ↔ ¬ NF R x ∧ Conv R x y := Iff.rfl

theorem sat_extensive : Subrel R (Saturate R) := by
  intro a b hab
  exact ⟨fun ha => ha b hab, .rel a b hab⟩

theorem sat_nf_iff : NF (Saturate R) x ↔ NF R x := by
  constructor
  · intro hx y hxy
    exact hx y (sat_extensive hxy)
  · intro hx y hxy
    exact hxy.1 hx

theorem sat_conv_iff : Conv (Saturate R) x y ↔ Conv R x y := by
  constructor
  · intro h
    exact conv_map (fun a => a) (fun {_ _} hab => hab.2) h
  · exact conv_mono sat_extensive

theorem sat_mono (h : Subrel R S) : Subrel (Saturate R) (Saturate S) := by
  intro a b hab
  refine ⟨?_, conv_mono h hab.2⟩
  intro ha
  exact hab.1 (fun c hac => ha c (h hac))

theorem sat_idempotent (R : X → X → Prop) :
    Saturate (Saturate R) = Saturate R := by
  funext a b
  apply propext
  constructor
  · intro hab
    exact ⟨fun ha => hab.1 (sat_nf_iff.mpr ha), sat_conv_iff.mp hab.2⟩
  · intro hab
    exact ⟨fun ha => hab.1 (sat_nf_iff.mp ha), sat_conv_iff.mpr hab.2⟩

theorem sat_greatest
    (hn : ∀ a, NF S a ↔ NF R a)
    (hc : ∀ a b, Conv S a b ↔ Conv R a b) :
    Subrel S (Saturate R) := by
  intro a b hab
  exact ⟨fun ha => (hn a).mpr ha b hab, (hc a b).mp (.rel a b hab)⟩

theorem sat_trans (hxy : Saturate R x y) (hyz : Saturate R y z) :
    Saturate R x z :=
  ⟨hxy.1, .trans x y z hxy.2 hyz.2⟩

theorem sat_self_iff : Saturate R x x ↔ ¬ NF R x :=
  ⟨fun h => h.1, fun h => ⟨h, .refl x⟩⟩

theorem sat_star_iff : Star (Saturate R) x y ↔ x = y ∨ Saturate R x y := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @tail b c _ hbc ih =>
        rcases ih with hab | hab
        · subst b
          exact Or.inr hbc
        · exact Or.inr (sat_trans hab hbc)
  · intro h
    rcases h with h | h
    · subst y
      exact .refl
    · exact .single h

theorem sat_pair_comparable (hu : UNC R) (hxy : Conv R x y) :
    x = y ∨ Saturate R x y ∨ Saturate R y x := by
  classical
  by_cases hx : NF R x
  · by_cases hy : NF R y
    · exact Or.inl (hu hx hy hxy)
    · exact Or.inr (Or.inr ⟨hy, .symm x y hxy⟩)
  · exact Or.inr (Or.inl ⟨hx, hxy⟩)

theorem sat_join_one_step (hu : UNC R) (hxy : Conv R x y) :
    ∃ w, (x = w ∨ Saturate R x w) ∧ (y = w ∨ Saturate R y w) := by
  rcases sat_pair_comparable hu hxy with h | h | h
  · subst y
    exact ⟨x, Or.inl rfl, Or.inl rfl⟩
  · exact ⟨y, Or.inr h, Or.inl rfl⟩
  · exact ⟨x, Or.inl rfl, Or.inr h⟩

theorem sat_cr_iff_unc : CR (Saturate R) ↔ UNC R := by
  constructor
  · intro hc a b ha hb hab
    exact unc_of_cr hc (sat_nf_iff.mpr ha) (sat_nf_iff.mpr hb)
      (sat_conv_iff.mpr hab)
  · intro hu a b c hab hac
    have hbc : Conv R b c := sat_conv_iff.mp
      (.trans b a c (.symm a b (conv_of_star hab)) (conv_of_star hac))
    obtain ⟨w, hbw, hcw⟩ := sat_join_one_step hu hbc
    exact ⟨w, sat_star_iff.mpr hbw, sat_star_iff.mpr hcw⟩

theorem unc_iff_exists_confluent_extension :
    UNC R ↔ ∃ S : X → X → Prop, Subrel R S ∧
      (∀ a, NF S a ↔ NF R a) ∧
      (∀ a b, Conv S a b ↔ Conv R a b) ∧ CR S := by
  constructor
  · intro hu
    exact ⟨Saturate R, sat_extensive, fun _ => sat_nf_iff,
      fun _ _ => sat_conv_iff, sat_cr_iff_unc.mpr hu⟩
  · rintro ⟨S, _, hn, hc, hs⟩ a b ha hb hab
    exact unc_of_cr hs ((hn a).mpr ha) ((hn b).mpr hb) ((hc a b).mpr hab)

theorem sat_map (f : X → Y) {T : Y → Y → Prop}
    (h : ∀ ⦃a b⦄, R a b → T (f a) (f b))
    (hxy : Saturate R x y) : Saturate T (f x) (f y) := by
  refine ⟨?_, conv_map f (fun {_ _} hab => .rel _ _ (h hab)) hxy.2⟩
  intro hx
  exact hxy.1 (fun b hxb => hx (f b) (h hxb))

theorem sat_normalizes_iff : Normalizes (Saturate R) x ↔ ConvertsToNF R x := by
  classical
  constructor
  · rintro ⟨r, hr, hxr⟩
    exact ⟨r, sat_nf_iff.mp hr, sat_conv_iff.mp (conv_of_star hxr)⟩
  · rintro ⟨r, hr, hxr⟩
    by_cases hx : NF R x
    · exact normalizes_of_nf (sat_nf_iff.mpr hx)
    · exact ⟨r, sat_nf_iff.mpr hr, .single ⟨hx, hxr⟩⟩

theorem sat_convertsToNF_iff : ConvertsToNF (Saturate R) x ↔ ConvertsToNF R x := by
  constructor
  · rintro ⟨r, hr, hxr⟩
    exact ⟨r, sat_nf_iff.mp hr, sat_conv_iff.mp hxr⟩
  · rintro ⟨r, hr, hxr⟩
    exact ⟨r, sat_nf_iff.mpr hr, sat_conv_iff.mpr hxr⟩

theorem sat_hereditary_iff :
    HereditarilyNormalizes (Saturate R) x ↔ ConvertsToNF R x := by
  constructor
  · intro hx
    exact sat_normalizes_iff.mp (hereditary_normalizes_self hx)
  · intro hx y hxy
    apply sat_normalizes_iff.mpr
    exact convertsToNF_of_conv
      (.symm x y (sat_conv_iff.mp (conv_of_star hxy))) hx

theorem sat_sn_iff_empty :
    SN (Saturate R) ↔ ∀ a b, ¬ R a b := by
  constructor
  · intro hs a b hab
    exact sn_irrefl hs a ⟨fun ha => ha b hab, .refl a⟩
  · intro h
    apply sn_subrel (R := fun (_ _ : X) => False) (S := Saturate R)
    · intro a b hab
      exact hab.1 (h a)
    · exact empty_sn

def SameNormalFormReductions (R S : X → X → Prop) : Prop :=
  ∀ x r, (NF R r ∧ Star R x r) ↔ (NF S r ∧ Star S x r)

def NonnormalNFP (R : X → X → Prop) : Prop :=
  ∀ ⦃x r⦄, ¬ NF R x → NF R r → Conv R x r → Star R x r

theorem same_nf_reductions_sat_iff_nonnormal_nfp :
    SameNormalFormReductions R (Saturate R) ↔ NonnormalNFP R := by
  constructor
  · intro heq a r ha hr har
    exact ((heq a r).mpr ⟨sat_nf_iff.mpr hr, .single ⟨ha, har⟩⟩).2
  · intro hn a r
    constructor
    · rintro ⟨hr, har⟩
      exact ⟨sat_nf_iff.mpr hr, star_mono sat_extensive har⟩
    · rintro ⟨hr, har⟩
      have hr' : NF R r := sat_nf_iff.mp hr
      refine ⟨hr', ?_⟩
      rcases sat_star_iff.mp har with har | har
      · subst r
        exact .refl
      · exact hn har.1 hr' har.2

theorem nfp_iff_unc_and_nonnormal_nfp :
    NFP R ↔ UNC R ∧ NonnormalNFP R := by
  classical
  constructor
  · intro hn
    constructor
    · intro a b ha hb hab
      exact (nf_star_eq ha (hn hb hab)).symm
    · intro a r _ hr har
      exact hn hr har
  · rintro ⟨hu, hn⟩ a r hr har
    by_cases ha : NF R a
    · have heq : a = r := hu ha hr har
      subst r
      exact .refl
    · exact hn ha hr har

theorem nfp_iff_unc_and_same_nf_reductions_sat :
    NFP R ↔ UNC R ∧ SameNormalFormReductions R (Saturate R) := by
  rw [nfp_iff_unc_and_nonnormal_nfp,
    same_nf_reductions_sat_iff_nonnormal_nfp]

theorem same_nf_reductions_sat_iff_nfp (hu : UNC R) :
    SameNormalFormReductions R (Saturate R) ↔ NFP R := by
  constructor
  · intro h
    exact nfp_iff_unc_and_same_nf_reductions_sat.mpr ⟨hu, h⟩
  · intro h
    exact (nfp_iff_unc_and_same_nf_reductions_sat.mp h).2

theorem same_nf_reductions_sat_iff_domains_equal (hu : UNC R) :
    SameNormalFormReductions R (Saturate R) ↔
      HereditarilyNormalizes R = Normalizes R ∧
      Normalizes R = ConvertsToNF R := by
  constructor
  · intro h
    have hn := (same_nf_reductions_sat_iff_nfp hu).mp h
    exact ⟨(nfp_iff_hereditary_eq_normalizes hu).mp hn,
      (nfp_iff_normalizes_eq_convertsToNF hu).mp hn⟩
  · rintro ⟨_, h⟩
    exact (same_nf_reductions_sat_iff_nfp hu).mpr
      ((nfp_iff_normalizes_eq_convertsToNF hu).mpr h)

def SourceSupport (R : X → X → Prop) (x : X) : Prop := ∃ y, R x y

theorem sourceSupport_iff_not_nf : SourceSupport R x ↔ ¬ NF R x := by
  classical
  constructor
  · rintro ⟨y, hxy⟩ hx
    exact hx y hxy
  · intro hx
    by_contra hs
    exact hx (fun y hxy => hs ⟨y, hxy⟩)

/-- Source activity and an equivalence relation, ordered componentwise below. -/
structure RelationSignature (X : Type u) where
  active : X → Prop
  equivalence : Setoid X

def SignatureLE (A B : RelationSignature X) : Prop :=
  (∀ x, A.active x → B.active x) ∧
  (∀ x y, A.equivalence.r x y → B.equivalence.r x y)

def relationSigma (R : X → X → Prop) : RelationSignature X where
  active := fun x => ¬ NF R x
  equivalence := conversionSetoid R

def relationGamma (A : RelationSignature X) (x y : X) : Prop :=
  A.active x ∧ A.equivalence.r x y

theorem signatureLE_refl (A : RelationSignature X) : SignatureLE A A :=
  ⟨fun _ h => h, fun _ _ h => h⟩

theorem signatureLE_trans {A B C : RelationSignature X}
    (hab : SignatureLE A B) (hbc : SignatureLE B C) : SignatureLE A C :=
  ⟨fun x hx => hbc.1 x (hab.1 x hx),
    fun x y hxy => hbc.2 x y (hab.2 x y hxy)⟩

theorem signatureLE_antisymm {A B : RelationSignature X}
    (hab : SignatureLE A B) (hba : SignatureLE B A) : A = B := by
  cases A with
  | mk pa qa =>
      cases B with
      | mk pb qb =>
          have hp : pa = pb := funext (fun x =>
            propext ⟨hab.1 x, hba.1 x⟩)
          have hq : qa = qb := by
            have hr : qa.r = qb.r := funext (fun x => funext (fun y =>
              propext ⟨hab.2 x y, hba.2 x y⟩))
            cases qa with
            | mk ra ha =>
                cases qb with
                | mk rb hb =>
                    dsimp at hr
                    cases hr
                    rfl
          cases hp
          cases hq
          rfl

theorem relationSigma_mono (h : Subrel R S) :
    SignatureLE (relationSigma R) (relationSigma S) := by
  constructor
  · intro a ha hs
    exact ha (fun b hab => hs b (h hab))
  · intro a b hab
    exact conv_mono h hab

theorem relationGamma_mono {A B : RelationSignature X} (h : SignatureLE A B) :
    Subrel (relationGamma A) (relationGamma B) := by
  intro a b hab
  exact ⟨h.1 a hab.1, h.2 a b hab.2⟩

theorem relation_adjunction (R : X → X → Prop) (A : RelationSignature X) :
    SignatureLE (relationSigma R) A ↔ Subrel R (relationGamma A) := by
  classical
  constructor
  · intro h a b hab
    exact ⟨h.1 a (fun ha => ha b hab), h.2 a b (.rel a b hab)⟩
  · intro h
    constructor
    · intro a ha
      by_contra hpa
      exact ha (fun b hab => hpa (h hab).1)
    · intro a b hab
      induction hab with
      | rel a b hab => exact (h hab).2
      | refl a => exact A.equivalence.iseqv.refl a
      | symm a b _ ih => exact A.equivalence.iseqv.symm ih
      | trans a b c _ _ ih₁ ih₂ => exact A.equivalence.iseqv.trans ih₁ ih₂

theorem relationGammaSigma (R : X → X → Prop) :
    relationGamma (relationSigma R) = Saturate R := rfl

theorem relation_adjunction_unit (R : X → X → Prop) :
    Subrel R (relationGamma (relationSigma R)) := sat_extensive

theorem relation_adjunction_counit (A : RelationSignature X) :
    SignatureLE (relationSigma (relationGamma A)) A :=
  (relation_adjunction (relationGamma A) A).mpr (fun {_ _} h => h)

theorem sat_le_iff_signature_le :
    Subrel (Saturate R) (Saturate S) ↔
      SignatureLE (relationSigma R) (relationSigma S) := by
  constructor
  · intro h
    apply (relation_adjunction R (relationSigma S)).mpr
    intro a b hab
    exact h (sat_extensive hab)
  · intro h
    exact relationGamma_mono h

end OperatorKO7.Meta.UniqueNormalization.Normalization
