import Mathlib.Logic.Relation

/-!
# Arbitrary-relation vocabulary for normalization

Relation: an arbitrary binary relation R, with finite reduction Star R and
equivalence closure Conv R. Property: normal forms, WN, SN, UNR, UNC and CR.
The definitions keep reduction, conversion and normality distinct.
The empty relation supplies a nonvacuous model on every carrier.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.Normalization

universe u v
variable {X : Type u} {Y : Type v}

abbrev Star (R : X → X → Prop) := Relation.ReflTransGen R
abbrev Conv (R : X → X → Prop) := Relation.EqvGen R

def Subrel (R S : X → X → Prop) : Prop :=
  ∀ ⦃x y⦄, R x y → S x y

def NF (R : X → X → Prop) (x : X) : Prop :=
  ∀ y, ¬ R x y

def Normalizes (R : X → X → Prop) (x : X) : Prop :=
  ∃ r, NF R r ∧ Star R x r

def WN (R : X → X → Prop) : Prop := ∀ x, Normalizes R x

def UNR (R : X → X → Prop) : Prop :=
  ∀ ⦃x r s⦄, NF R r → NF R s → Star R x r → Star R x s → r = s

def UNC (R : X → X → Prop) : Prop :=
  ∀ ⦃r s⦄, NF R r → NF R s → Conv R r s → r = s

def CR (R : X → X → Prop) : Prop :=
  ∀ ⦃x y z⦄, Star R x y → Star R x z →
    ∃ w, Star R y w ∧ Star R z w

def NFP (R : X → X → Prop) : Prop :=
  ∀ ⦃x r⦄, NF R r → Conv R x r → Star R x r

def SN (R : X → X → Prop) : Prop :=
  WellFounded (fun y x => R x y)

variable {R S : X → X → Prop} {x y z : X}

theorem star_mono (h : Subrel R S) (p : Star R x y) : Star S x y :=
  p.mono (fun _ _ hp => h hp)

theorem star_map (f : X → Y) {T : Y → Y → Prop}
    (h : ∀ ⦃a b⦄, R a b → T (f a) (f b)) (p : Star R x y) :
    Star T (f x) (f y) :=
  p.lift f (fun _ _ hp => h hp)

theorem conv_of_star (p : Star R x y) : Conv R x y := by
  induction p with
  | refl => exact .refl _
  | tail _ h ih => exact .trans _ _ _ ih (.rel _ _ h)

theorem conv_mono (h : Subrel R S) (p : Conv R x y) : Conv S x y := by
  induction p with
  | rel a b hab => exact .rel a b (h hab)
  | refl a => exact .refl a
  | symm a b _ ih => exact .symm a b ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans a b c ih₁ ih₂

theorem conv_map (f : X → Y) {T : Y → Y → Prop}
    (h : ∀ ⦃a b⦄, R a b → Conv T (f a) (f b)) (p : Conv R x y) :
    Conv T (f x) (f y) := by
  induction p with
  | rel a b hab => exact h hab
  | refl a => exact .refl (f a)
  | symm a b _ ih => exact .symm (f a) (f b) ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans (f a) (f b) (f c) ih₁ ih₂

theorem conv_of_join (h : ∃ w, Star R x w ∧ Star R y w) : Conv R x y := by
  obtain ⟨w, hx, hy⟩ := h
  exact .trans x w y (conv_of_star hx) (.symm y w (conv_of_star hy))

theorem nf_star_eq (hx : NF R x) (p : Star R x y) : y = x := by
  induction p with
  | refl => rfl
  | @tail b c _ h ih => exact False.elim (hx c (ih ▸ h))

theorem star_from_nf_iff (hx : NF R x) : Star R x y ↔ x = y := by
  constructor
  · intro h; exact (nf_star_eq hx h).symm
  · intro h; subst y; exact .refl

theorem normalizes_of_nf (hx : NF R x) : Normalizes R x :=
  ⟨x, hx, .refl⟩

theorem normalizes_backward (h : Star R x y) (hy : Normalizes R y) :
    Normalizes R x := by
  obtain ⟨r, hr, hyr⟩ := hy
  exact ⟨r, hr, h.trans hyr⟩

theorem star_first (p : Star R x y) (hne : x ≠ y) :
    ∃ z, R x z ∧ Star R z y := by
  induction p with
  | refl => exact False.elim (hne rfl)
  | @tail b c p h ih =>
      by_cases hxb : x = b
      · subst b; exact ⟨c, h, .refl⟩
      · obtain ⟨a, hxa, hab⟩ := ih hxb
        exact ⟨a, hxa, hab.tail h⟩

theorem star_invariant (f : X → Y)
    (h : ∀ ⦃a b⦄, R a b → f a = f b) (p : Star R x y) : f x = f y := by
  induction p with
  | refl => rfl
  | tail _ hab ih => exact ih.trans (h hab)

theorem conv_invariant (f : X → Y)
    (h : ∀ ⦃a b⦄, R a b → f a = f b) (p : Conv R x y) : f x = f y := by
  induction p with
  | rel a b hab => exact h hab
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem unr_of_unc (h : UNC R) : UNR R := by
  intro x r s hr hs hxr hxs
  exact h hr hs (.trans r x s (.symm x r (conv_of_star hxr)) (conv_of_star hxs))

theorem cr_of_wn_unr (hn : WN R) (hu : UNR R) : CR R := by
  intro x y z hxy hxz
  obtain ⟨r, hr, hyr⟩ := hn y
  obtain ⟨s, hs, hzs⟩ := hn z
  have hrs := hu hr hs (hxy.trans hyr) (hxz.trans hzs)
  subst s
  exact ⟨r, hyr, hzs⟩

theorem join_trans (hc : CR R)
    (hxy : ∃ w, Star R x w ∧ Star R y w)
    (hyz : ∃ w, Star R y w ∧ Star R z w) :
    ∃ w, Star R x w ∧ Star R z w := by
  obtain ⟨a, hxa, hya⟩ := hxy
  obtain ⟨b, hyb, hzb⟩ := hyz
  obtain ⟨c, hac, hbc⟩ := hc hya hyb
  exact ⟨c, hxa.trans hac, hzb.trans hbc⟩

theorem join_of_conv (hc : CR R) (p : Conv R x y) :
    ∃ w, Star R x w ∧ Star R y w := by
  induction p with
  | rel a b hab => exact ⟨b, .single hab, .refl⟩
  | refl a => exact ⟨a, .refl, .refl⟩
  | symm a b _ ih =>
      obtain ⟨c, hac, hbc⟩ := ih
      exact ⟨c, hbc, hac⟩
  | trans a b c _ _ ih₁ ih₂ => exact join_trans hc ih₁ ih₂

theorem unc_of_cr (hc : CR R) : UNC R := by
  intro r s hr hs hrs
  obtain ⟨w, hrw, hsw⟩ := join_of_conv hc hrs
  exact (nf_star_eq hr hrw).symm.trans (nf_star_eq hs hsw)

theorem nfp_of_cr (hc : CR R) : NFP R := by
  intro x r hr hxr
  obtain ⟨w, hxw, hrw⟩ := join_of_conv hc hxr
  have hwr := nf_star_eq hr hrw
  subst w
  exact hxw

theorem cr_iff_unc_of_wn (hn : WN R) : CR R ↔ UNC R :=
  ⟨unc_of_cr, fun hu => cr_of_wn_unr hn (unr_of_unc hu)⟩

theorem cr_iff_unr_of_wn (hn : WN R) : CR R ↔ UNR R :=
  ⟨fun hc => unr_of_unc (unc_of_cr hc), cr_of_wn_unr hn⟩

theorem acc_normalizes (ha : Acc (fun y x => R x y) x) : Normalizes R x := by
  classical
  induction ha with
  | intro x _ ih =>
      by_cases hs : ∃ y, R x y
      · obtain ⟨y, hxy⟩ := hs
        obtain ⟨r, hr, hyr⟩ := ih y hxy
        exact ⟨r, hr, .head hxy hyr⟩
      · exact ⟨x, fun y h => hs ⟨y, h⟩, .refl⟩

theorem wn_of_sn (h : SN R) : WN R :=
  fun x => acc_normalizes (h.apply x)

theorem sn_subrel (h : Subrel S R) (hsn : SN R) : SN S := by
  constructor
  intro x
  have ha := hsn.apply x
  induction ha with
  | intro x _ ih => exact Acc.intro x (fun y hy => ih y (h hy))

theorem sn_irrefl (hsn : SN R) (x : X) : ¬ R x x := by
  have ha := hsn.apply x
  induction ha with
  | intro x _ ih =>
      intro h
      exact ih x h h

theorem empty_wn : WN (fun (_ _ : X) => False) :=
  fun x => ⟨x, fun _ h => h, .refl⟩

theorem empty_cr : CR (fun (_ _ : X) => False) := by
  intro x y z hxy hxz
  have hy := nf_star_eq (fun _ h => h) hxy
  have hz := nf_star_eq (fun _ h => h) hxz
  subst y; subst z
  exact ⟨x, .refl, .refl⟩

theorem empty_sn : SN (fun (_ _ : X) => False) :=
  ⟨fun x => Acc.intro x (fun _ h => False.elim h)⟩


/-- Confluence needs an invariant reachable value; that value need not be normal. -/
theorem cr_of_reachable_invariant (n : X → X)
    (hi : ∀ ⦃a b⦄, R a b → n a = n b)
    (hr : ∀ a, Star R a (n a)) : CR R := by
  intro x y z hxy hxz
  have hyz : n y = n z :=
    (star_invariant n hi hxy).symm.trans (star_invariant n hi hxz)
  refine ⟨n y, hr y, ?_⟩
  rw [hyz]
  exact hr z

theorem idempotent_of_reachable_invariant (n : X → X)
    (hi : ∀ ⦃a b⦄, R a b → n a = n b)
    (hr : ∀ a, Star R a (n a)) : ∀ a, n (n a) = n a :=
  fun a => (star_invariant n hi (hr a)).symm

theorem sn_no_two_cycle (hs : SN R) (a b : X) (hab : R a b) (hba : R b a) :
    False := by
  have bad : ∀ x, Acc (fun y x => R x y) x →
      ∀ y, R x y → R y x → False := by
    intro x hx
    induction hx with
    | intro x _ ih =>
        intro y hxy hyx
        exact ih y hxy x hyx hxy
  exact bad a (hs.apply a) b hab hba

end OperatorKO7.Meta.UniqueNormalization.Normalization

