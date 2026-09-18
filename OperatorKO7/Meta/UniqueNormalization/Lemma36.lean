import OperatorKO7.Meta.UniqueNormalization.DownRelation

/-!
# Lemma 36 without an infinitary carrier

Campaign: `Roadmaps\klop\ROADMAP.md`, wave 5. Source: Kahrs and Smith, FSCD 2016,
Lemma 36, with Proposition 32 replaced by a finite certificate.

## What the source does, and what this module does instead

Lemma 36 concludes that two rules whose instances meet around a
constructor-compatible equivalence have omega-unifiable left-hand sides. Its
proof runs through Proposition 32, the function `U(=rho)` from the coalgebra into
`Ter^infinity(Sigma, empty)`. That function is corecursive, its range contains
genuinely infinite terms, and building it needs a well-ordering of the
equivalence classes.

Frozen definition D4 records the paper's remark that omega-unifiability of
finite terms coincides with unifiability over rational terms. The current Lean
stack does not yet define rational trees; `RationalUnification.lean` instead
uses the finite union/find-style certificate `OmegaUnifiable`, whose forward
bridge from ordinary finite unification is proved there. This module builds that
certificate directly from the constructor-compatible equivalence, so no term of
infinite depth is ever formed and Proposition 32 is not needed for the
certificate-level Lemma 36. Identifying that certificate with a separately
mechanized rational-tree semantics is a distinct representation theorem and is
not smuggled into this lemma.

## The certificate

Write `L` and `Rt` for the renamed-apart copies of the two left-hand sides. The
closure is

* two constructor terms whose instances the equivalence relates, or
* the diagonal, or
* the single pair `(L, Rt)` and its converse.

Transitivity survives the added pair for one reason: `L` and `Rt` are
destructor-headed, so the first clause never mentions them, and a chain through
`L` or `Rt` can only be a chain of added pairs. Decomposition at the added pair
is the root step of the lemma, and decomposition below it is constructor
compatibility.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v w w' w''

variable {sigma : Type u} {nu : Type v}

/-! ## Substitution across a change of variable type

`Subst.apply` is homogeneous. Reading a renamed-apart term back through the two
original substitutions needs a map out of the tagged variable type, which is what
`valuate` supplies. -/

mutual
/-- Replace each variable of `t` by its image under `h`, which may leave the
original variable type. -/
def valuate {mu : Type w} (h : mu → Term sigma nu) : Term sigma mu → Term sigma nu
  | .var x => h x
  | .app f args => .app f (valuateList h args)
/-- `valuate` across an argument list. -/
def valuateList {mu : Type w} (h : mu → Term sigma nu) :
    List (Term sigma mu) → List (Term sigma nu)
  | [] => []
  | a :: as => valuate h a :: valuateList h as
end

@[simp] theorem valuate_var {mu : Type w} (h : mu → Term sigma nu) (x : mu) :
    valuate h (.var x) = h x := rfl

@[simp] theorem valuate_app {mu : Type w} (h : mu → Term sigma nu) (f : sigma)
    (args : List (Term sigma mu)) :
    valuate h (.app f args) = .app f (valuateList h args) := rfl

@[simp] theorem valuateList_nil {mu : Type w} (h : mu → Term sigma nu) :
    valuateList h ([] : List (Term sigma mu)) = [] := rfl

@[simp] theorem valuateList_cons {mu : Type w} (h : mu → Term sigma nu)
    (a : Term sigma mu) (as : List (Term sigma mu)) :
    valuateList h (a :: as) = valuate h a :: valuateList h as := rfl

/-- `valuateList` is the `List.map` of `valuate`. -/
theorem valuateList_eq_map {mu : Type w} (h : mu → Term sigma nu)
    (args : List (Term sigma mu)) : valuateList h args = args.map (valuate h) := by
  induction args with
  | nil => simp
  | cons a as ih => simp [ih]

/-- Renaming and then valuating is substitution by the composite. -/
theorem valuate_mapVar {mu : Type w} (g : nu → mu) (h : mu → Term sigma nu)
    (t : Term sigma nu) :
    valuate h (Term.mapVar g t) = Subst.apply (fun x => h (g x)) t := by
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
      simp only [Term.mapVar_app, valuate_app, Subst.apply_app, Term.mapVarList_eq_map,
        valuateList_eq_map, Subst.applyList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left (fun a ha => ih a ha)

/-! ## More list plumbing -/

/-- Read a pointwise relation off an argumentwise relation between two maps of
two different lists. -/
theorem forall₂_of_map₂ {alpha : Type u} {beta : Type v} {gamma : Type w}
    {delta : Type w'} {r : gamma → delta → Prop} {f : alpha → gamma} {g : beta → delta} :
    ∀ {l₁ : List alpha} {l₂ : List beta}, List.Forall₂ r (l₁.map f) (l₂.map g) →
      List.Forall₂ (fun x y => r (f x) (g y)) l₁ l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ h
      cases l₂ with
      | nil => exact List.Forall₂.nil
      | cons b bs => simp at h
  | cons a as ih =>
      intro l₂ h
      cases l₂ with
      | nil => simp at h
      | cons b bs =>
          rw [List.map_cons, List.map_cons] at h
          cases h with
          | cons hhead htail => exact List.Forall₂.cons hhead (ih htail)

/-- Push a pointwise relation forward through two maps. -/
theorem forall₂_map₂_of {alpha : Type u} {beta : Type v} {gamma : Type w}
    {delta : Type w'} {r : gamma → delta → Prop} {f : alpha → gamma} {g : beta → delta} :
    ∀ {l₁ : List alpha} {l₂ : List beta},
      List.Forall₂ (fun x y => r (f x) (g y)) l₁ l₂ →
      List.Forall₂ r (l₁.map f) (l₂.map g) := by
  intro l₁ l₂ h
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih => exact List.Forall₂.cons hab ih

/-- Carry membership side conditions along an argumentwise relation. -/
theorem forall₂_and_mem {alpha : Type u} {beta : Type v} {r : alpha → beta → Prop}
    {P : alpha → Prop} {Q : beta → Prop} :
    ∀ {xs : List alpha} {ys : List beta}, List.Forall₂ r xs ys →
      (∀ x ∈ xs, P x) → (∀ y ∈ ys, Q y) →
      List.Forall₂ (fun x y => P x ∧ Q y ∧ r x y) xs ys := by
  intro xs ys h
  induction h with
  | nil => intro _ _; exact List.Forall₂.nil
  | @cons a b as bs hab _ ih =>
      intro hP hQ
      refine List.Forall₂.cons
        ⟨hP a (List.mem_cons_self ..), hQ b (List.mem_cons_self ..), hab⟩ ?_
      exact ih (fun x hx => hP x (List.mem_cons_of_mem _ hx))
        (fun y hy => hQ y (List.mem_cons_of_mem _ hy))

/-! ## Constructor terms under renaming -/

/-- A destructor-headed application is not a constructor term. -/
theorem not_conOnly_destructor {d : sigma} (args : List (Term (sigma ⊕ sigma) nu)) :
    ¬ ConOnly (Term.app (Sum.inr d) args) := by
  intro h
  obtain ⟨c, hc, -⟩ := h.app_inv
  exact absurd hc (by simp)

/-- Renaming preserves constructor terms. -/
theorem ConOnly.mapVar {mu : Type w} (g : nu → mu) :
    ∀ {t : Term (sigma ⊕ sigma) nu}, ConOnly t → ConOnly (Term.mapVar g t) := by
  intro t h
  induction h with
  | var x => exact ConOnly.var (g x)
  | app c args _ ih =>
      refine ConOnly.app c _ ?_
      intro q hq
      rw [Term.mapVarList_eq_map] at hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      exact ih p hp

/-! ## The certificate -/

/-- The three added pairs: the diagonal, the pair of renamed left-hand sides, and
its converse. -/
def LinkRel (L Rt p q : Term (sigma ⊕ sigma) (nu ⊕ nu)) : Prop :=
  p = q ∨ (p = L ∧ q = Rt) ∨ (p = Rt ∧ q = L)

theorem LinkRel.refl (L Rt p : Term (sigma ⊕ sigma) (nu ⊕ nu)) : LinkRel L Rt p p :=
  Or.inl rfl

theorem LinkRel.symm {L Rt p q : Term (sigma ⊕ sigma) (nu ⊕ nu)}
    (h : LinkRel L Rt p q) : LinkRel L Rt q p := by
  rcases h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

theorem LinkRel.trans {L Rt p q r : Term (sigma ⊕ sigma) (nu ⊕ nu)}
    (h₁ : LinkRel L Rt p q) (h₂ : LinkRel L Rt q r) : LinkRel L Rt p r := by
  rcases h₁ with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h₂
  · rcases h₂ with rfl | ⟨hq, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl (by rw [hq])
    · exact Or.inl rfl
  · rcases h₂ with rfl | ⟨-, rfl⟩ | ⟨hq, rfl⟩
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inl (by rw [← hq])

/-- The unification closure built from a constructor-compatible equivalence: two
constructor terms whose valuations the equivalence relates, together with the
three added pairs. -/
def Cert36 (S : CRel sigma nu) (h : nu ⊕ nu → Term (sigma ⊕ sigma) nu)
    (L Rt p q : Term (sigma ⊕ sigma) (nu ⊕ nu)) : Prop :=
  (ConOnly p ∧ ConOnly q ∧ S (valuate h p) (valuate h q)) ∨ LinkRel L Rt p q

/-- **Lemma 36, reformulated.** A constructor-compatible equivalence relating the
direct subterm instances of two Constructor-TRS left-hand sides with one shared
root symbol makes those left-hand sides omega-unifiable.

No infinite term is built. The witness is the finite closure `Cert36`. -/
theorem lemma36 {S : CRel sigma nu}
    (hsymm : ∀ x y, S x y → S y x)
    (htrans : ∀ x y z, S x y → S y z → S x z)
    (hCC : ConstructorCompatible S)
    {F : sigma} {ps qs : List (Term (sigma ⊕ sigma) nu)}
    (hps : ∀ p ∈ ps, ConOnly p) (hqs : ∀ q ∈ qs, ConOnly q)
    {a b : Subst (sigma ⊕ sigma) nu}
    (hall : List.Forall₂ S (ps.map (Subst.apply a)) (qs.map (Subst.apply b))) :
    OmegaUnifiable (Term.app (Sum.inr F) ps) (Term.app (Sum.inr F) qs) := by
  classical
  set h : nu ⊕ nu → Term (sigma ⊕ sigma) nu := Sum.elim a b with hdef
  set L : Term (sigma ⊕ sigma) (nu ⊕ nu) := leftCopy (Term.app (Sum.inr F) ps) with hL
  set Rt : Term (sigma ⊕ sigma) (nu ⊕ nu) := rightCopy (Term.app (Sum.inr F) qs) with hRt
  -- The two renamed left-hand sides, in application form.
  have hLapp : L = Term.app (Sum.inr F) (ps.map (Term.mapVar Sum.inl)) := by
    rw [hL, leftCopy, Term.mapVar_app, Term.mapVarList_eq_map]
  have hRtapp : Rt = Term.app (Sum.inr F) (qs.map (Term.mapVar Sum.inr)) := by
    rw [hRt, rightCopy, Term.mapVar_app, Term.mapVarList_eq_map]
  have hLnot : ¬ ConOnly L := by rw [hLapp]; exact not_conOnly_destructor _
  have hRtnot : ¬ ConOnly Rt := by rw [hRtapp]; exact not_conOnly_destructor _
  -- Valuating a renamed copy is the original substitution.
  have hvalL : ∀ t : Term (sigma ⊕ sigma) nu,
      valuate h (Term.mapVar Sum.inl t) = Subst.apply a t := by
    intro t; rw [valuate_mapVar]; simp [hdef]
  have hvalR : ∀ t : Term (sigma ⊕ sigma) nu,
      valuate h (Term.mapVar Sum.inr t) = Subst.apply b t := by
    intro t; rw [valuate_mapVar]; simp [hdef]
  -- The argument pairs of the two left-hand sides sit in the certificate.
  have hargs : List.Forall₂ (Cert36 S h L Rt)
      (ps.map (Term.mapVar Sum.inl)) (qs.map (Term.mapVar Sum.inr)) := by
    refine forall₂_map₂_of ?_
    refine forall₂_mono ?_ (forall₂_and_mem (forall₂_of_map₂ hall) hps hqs)
    intro p q hpq
    obtain ⟨hp, hq, hS⟩ := hpq
    refine Or.inl ⟨hp.mapVar Sum.inl, hq.mapVar Sum.inr, ?_⟩
    rw [hvalL, hvalR]
    exact hS
  refine ⟨Cert36 S h L Rt, ⟨?_, ?_, ?_, ?_⟩, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  · -- reflexivity
    intro t
    exact Or.inr (LinkRel.refl L Rt t)
  · -- symmetry
    intro s t hst
    rcases hst with ⟨hs, ht, hS⟩ | hlink
    · exact Or.inl ⟨ht, hs, hsymm _ _ hS⟩
    · exact Or.inr hlink.symm
  · -- transitivity
    intro s t r hst htr
    rcases hst with ⟨hs, ht, hS⟩ | hlink₁
    · rcases htr with ⟨-, hr, hS'⟩ | hlink₂
      · exact Or.inl ⟨hs, hr, htrans _ _ _ hS hS'⟩
      · rcases hlink₂ with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨hs, ht, hS⟩
        · exact absurd ht hLnot
        · exact absurd ht hRtnot
    · rcases htr with ⟨ht, hr, hS'⟩ | hlink₂
      · rcases hlink₁ with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨ht, hr, hS'⟩
        · exact absurd ht hRtnot
        · exact absurd ht hLnot
      · exact Or.inr (hlink₁.trans hlink₂)
  · -- decomposition
    intro f g xs ys hxy
    rcases hxy with ⟨hx, hy, hS⟩ | hlink
    · obtain ⟨c, rfl, hxs⟩ := hx.app_inv
      obtain ⟨c', rfl, hys⟩ := hy.app_inv
      simp only [valuate_app, valuateList_eq_map] at hS
      rcases hCC _ _ (ConTopped.app c _) (ConTopped.app c' _) hS with
        ⟨z, hz, -⟩ | ⟨e, XS, YS, hxe, hye, hforall⟩
      · exact absurd hz (by simp)
      · simp only [Term.app.injEq] at hxe hye
        obtain ⟨hce, hXS⟩ := hxe
        obtain ⟨hce', hYS⟩ := hye
        subst hXS
        subst hYS
        have hce₁ : c = e := by simpa using hce
        have hce₂ : c' = e := by simpa using hce'
        have hcc : c = c' := by rw [hce₁, hce₂]
        subst hcc
        refine ⟨rfl, ?_⟩
        refine forall₂_mono ?_
          (forall₂_and_mem (forall₂_of_map₂ hforall) hxs hys)
        intro p q hpq
        exact Or.inl ⟨hpq.1, hpq.2.1, hpq.2.2⟩
    · rcases hlink with heq | ⟨hxL, hyRt⟩ | ⟨hxRt, hyL⟩
      · -- the diagonal
        simp only [Term.app.injEq] at heq
        obtain ⟨hfg, hxsys⟩ := heq
        subst hxsys
        exact ⟨hfg, forall₂_self (r := Cert36 S h L Rt) (fun t => Or.inr (LinkRel.refl L Rt t)) xs⟩
      · -- the added pair, decomposed at the shared destructor root
        rw [hLapp] at hxL
        rw [hRtapp] at hyRt
        simp only [Term.app.injEq] at hxL hyRt
        obtain ⟨hf, hxs⟩ := hxL
        obtain ⟨hg, hys⟩ := hyRt
        subst hxs
        subst hys
        exact ⟨by rw [hf, hg], hargs⟩
      · -- the converse of the added pair
        rw [hRtapp] at hxRt
        rw [hLapp] at hyL
        simp only [Term.app.injEq] at hxRt hyL
        obtain ⟨hf, hxs⟩ := hxRt
        obtain ⟨hg, hys⟩ := hyL
        subst hxs
        subst hys
        refine ⟨by rw [hf, hg], ?_⟩
        refine forall₂_flip (forall₂_mono ?_ hargs)
        intro p q hpq
        rcases hpq with ⟨hp, hq, hS⟩ | hlink
        · exact Or.inl ⟨hq, hp, hsymm _ _ hS⟩
        · exact Or.inr hlink.symm

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.valuate
#check @OperatorKO7.Meta.UniqueNormalization.Cert36

#print axioms OperatorKO7.Meta.UniqueNormalization.valuate_mapVar
#print axioms OperatorKO7.Meta.UniqueNormalization.ConOnly.mapVar
#print axioms OperatorKO7.Meta.UniqueNormalization.LinkRel.trans
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma36
