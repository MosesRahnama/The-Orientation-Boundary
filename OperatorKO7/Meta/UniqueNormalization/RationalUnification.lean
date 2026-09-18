import OperatorKO7.Meta.UniqueNormalization.TermMaps
import Mathlib.Data.PFunctor.Univariate.M

/-!
# Omega-unifiability: finite certificate and infinite-term semantics

Campaign: `Roadmaps\klop\ROADMAP.md`, WP-K1.
Definition freeze: `Roadmaps\klop\definitions.md` (D4).

## Fidelity block (frozen `definitions.md`, D4)

> "Two terms t in Ter(Sigma, V), u in Ter(Sigma, W) are said to be unifiable iff
> there is a pair of substitutions sigma : V -> Ter(Sigma, X),
> theta : W -> Ter(Sigma, X) such that sigma(t) = theta(u). A pair of terms is
> said to be omega-unifiable if these conditions hold for substitutions with
> infinite terms in their codomain. Unifiability implies omega-unifiability, as
> all finite terms inhabit the infinite term universe as well."

> "As an aside, omega-unifiability of finite terms coincides with their
> unifiability w.r.t. substitutions with rational terms. This was first studied
> by Huet, and is these days usually implemented via union/find structures."

The finite predicate `OmegaUnifiable` is carried by the union/find invariant:
an equivalence relation on finite terms, closed under decomposition of related
applications. This module now also constructs the source definition's infinite
term universe explicitly as the M-type of the polynomial functor with variable
leaves and finite-arity application nodes. `omegaUnifiableShared_iff_infinite`
and `omegaUnifiable_iff_infinite` prove that the finite certificate and this
infinite-term substitution semantics coincide. The reverse direction is
constructive at the semantic level: quotient the certificate relation, choose
an application representative whenever a class contains one, and corecursively
unfold the quotient through Mathlib's final-coalgebra `PFunctor.M`.

The paper's additional observation that finite-term omega-unifiability also
coincides with rational-tree unifiability remains historical provenance; it is
no longer load-bearing for the campaign because the paper's primary infinite-
term definition is mechanized directly here.

Concretely, `UnifClosure E` says `E` is an equivalence and that whenever `E`
relates two applications they carry the same function symbol and their argument
lists are related pointwise. A symbol clash inside one class is therefore
impossible, and the absence of an occurs check is visible in what is **not**
required: a variable may be related to a term containing it.

`Term.mapVar` supplies the rename-apart of D4's two-substitution form: the left
term is tagged by `Sum.inl` and the right by `Sum.inr`, so shared variable names
in the two terms do not accidentally identify.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v w

variable {sigma : Type u} {nu : Type v} {mu : Type w}

/-! ## The certificate -/

/-- A **unification closure**: an equivalence relation on terms under which any
two related applications share their function symbol and have pointwise related
arguments.

No occurs check appears: `E (var x) t` is permitted for a `t` containing `x`,
and that is precisely the extra freedom rational (equivalently, infinite)
substitutions provide over finite ones. -/
structure UnifClosure (E : Term sigma nu → Term sigma nu → Prop) : Prop where
  /-- `E` is reflexive. -/
  rfl' : ∀ t, E t t
  /-- `E` is symmetric. -/
  symm' : ∀ {s t}, E s t → E t s
  /-- `E` is transitive. -/
  trans' : ∀ {s t u}, E s t → E t u → E s u
  /-- Related applications agree on their symbol and are related argumentwise. -/
  decomp : ∀ {f g : sigma} {xs ys : List (Term sigma nu)},
    E (.app f xs) (.app g ys) → f = g ∧ List.Forall₂ E xs ys

/-- Two terms are omega-unifiable **without renaming**, that is treating their
variables as shared. -/
def OmegaUnifiableShared (s t : Term sigma nu) : Prop :=
  ∃ E : Term sigma nu → Term sigma nu → Prop, UnifClosure E ∧ E s t

/-- The left copy of a term under rename-apart. -/
def leftCopy (t : Term sigma nu) : Term sigma (nu ⊕ nu) := Term.mapVar Sum.inl t

/-- The right copy of a term under rename-apart. -/
def rightCopy (t : Term sigma nu) : Term sigma (nu ⊕ nu) := Term.mapVar Sum.inr t

/-- **Certificate-level omega-unifiability used by this development.** The two
terms are taken with disjoint variable sets and a unification closure relates the
two copies. The section below proves this finite union/find representation
extensionally equivalent to explicit substitutions into potentially infinite
M-type terms. -/
def OmegaUnifiable (s t : Term sigma nu) : Prop :=
  OmegaUnifiableShared (leftCopy s) (rightCopy t)

/-! ## Explicit infinite-term semantics -/

/-- Polynomial functor for first-order terms with variable leaves and
finite-arity application nodes. Its M-type is the source paper's potentially
infinite term universe. -/
def infTermP (sigma : Type u) (nu : Type v) : PFunctor where
  A := nu ⊕ (sigma × Nat)
  B
    | .inl _ => Fin 0
    | .inr (_, n) => Fin n

/-- Potentially infinite first-order terms, as the final coalgebra of `infTermP`. -/
abbrev InfTerm (sigma : Type u) (nu : Type v) := PFunctor.M (infTermP sigma nu)

namespace InfTerm

/-- Variable leaf in the infinite-term carrier. -/
def var (x : nu) : InfTerm sigma nu :=
  PFunctor.M.mk ⟨Sum.inl x, fun i => Fin.elim0 i⟩

/-- Finite-arity application node in the infinite-term carrier. -/
def app (f : sigma) (xs : List (InfTerm sigma nu)) : InfTerm sigma nu :=
  PFunctor.M.mk ⟨Sum.inr (f, xs.length), fun i => xs.get i⟩

@[simp] theorem dest_var (x : nu) :
    PFunctor.M.dest (var (sigma := sigma) x) =
      (⟨Sum.inl x, fun i => Fin.elim0 i⟩ : (infTermP sigma nu) (InfTerm sigma nu)) := by
  rfl

@[simp] theorem dest_app (f : sigma) (xs : List (InfTerm sigma nu)) :
    PFunctor.M.dest (app f xs) =
      (⟨Sum.inr (f, xs.length), fun i => xs.get i⟩ : (infTermP sigma nu) (InfTerm sigma nu)) := by
  rfl

/-- Equality of application nodes forces the same symbol and pointwise-equal
children. This is the infinite-term counterpart of `UnifClosure.decomp`. -/
theorem app_inj {f g : sigma} {xs ys : List (InfTerm sigma nu)}
    (h : app f xs = app g ys) :
    f = g ∧ List.Forall₂ (fun x y => x = y) xs ys := by
  have hd := congrArg PFunctor.M.dest h
  rw [dest_app, dest_app] at hd
  have hparts := (Sigma.mk.inj_iff).1 hd
  have hs : (f, xs.length) = (g, ys.length) := Sum.inr_injective hparts.1
  have hfg : f = g := congrArg Prod.fst hs
  have hlen : xs.length = ys.length := congrArg Prod.snd hs
  have hchildren := (Fin.heq_fun_iff hlen).1 hparts.2
  refine ⟨hfg, (List.forall₂_iff_get).2 ⟨hlen, ?_⟩⟩
  intro i hix hiy
  simpa using hchildren ⟨i, hix⟩

end InfTerm

/-- Infinite-term substitution. -/
abbrev InfSubst (sigma : Type u) (nu : Type v) (mu : Type w) :=
  nu → InfTerm sigma mu

/-- Homomorphic application of an infinite-term substitution to a finite term. -/
def InfApply (r : InfSubst sigma nu mu) : Term sigma nu → InfTerm sigma mu
  | .var x => r x
  | .app f xs => InfTerm.app f (xs.map (InfApply r))

/-- Canonical infinite-term unifiability without renaming. `Unit` is sufficient
as a target variable alphabet because the reverse construction below unfolds
certificate classes directly and needs only one residual variable leaf. -/
def InfiniteOmegaUnifiableShared (s t : Term sigma nu) : Prop :=
  ∃ r : InfSubst sigma nu Unit, InfApply r s = InfApply r t

/-- D4's rename-apart two-substitution semantics on explicit infinite terms. -/
def InfiniteOmegaUnifiable (s t : Term sigma nu) : Prop :=
  InfiniteOmegaUnifiableShared (leftCopy s) (rightCopy t)

/-- An infinite-term unifier over **any** target variable type induces the
finite union/find certificate. Thus the canonical `Unit` presentation loses no
solutions from D4's arbitrary-target formulation. -/
theorem omegaUnifiableShared_of_infiniteSubst {mu : Type w} {s t : Term sigma nu}
    (r : InfSubst sigma nu mu) (hst : InfApply r s = InfApply r t) :
    OmegaUnifiableShared s t := by
  let E : Term sigma nu → Term sigma nu → Prop := fun a b => InfApply r a = InfApply r b
  refine ⟨E, ?_, hst⟩
  refine ⟨fun _ => rfl, fun hab => hab.symm, fun hab hbc => hab.trans hbc, ?_⟩
  intro f g xs ys hab
  change InfApply r (.app f xs) = InfApply r (.app g ys) at hab
  simp only [InfApply] at hab
  have hdecomp := InfTerm.app_inj hab
  refine ⟨hdecomp.1, ?_⟩
  have hargs := hdecomp.2
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff] at hargs
  exact hargs

/-- Every canonical infinite-term unifier induces the finite certificate. -/
theorem omegaUnifiableShared_of_infinite {s t : Term sigma nu}
    (h : InfiniteOmegaUnifiableShared s t) : OmegaUnifiableShared s t := by
  rcases h with ⟨r, hst⟩
  exact omegaUnifiableShared_of_infiniteSubst r hst

/-- Infinite-term omega-unifiability implies the rename-apart certificate. -/
theorem omegaUnifiable_of_infinite {s t : Term sigma nu}
    (h : InfiniteOmegaUnifiable s t) : OmegaUnifiable s t :=
  omegaUnifiableShared_of_infinite h

/-- Setoid carried by a finite unification certificate. -/
def unifSetoid {E : Term sigma nu → Term sigma nu → Prop}
    (hE : UnifClosure E) : Setoid (Term sigma nu) where
  r := E
  iseqv := ⟨hE.rfl', hE.symm', hE.trans'⟩

/-- A certificate equivalence class. -/
abbrev UClass {E : Term sigma nu → Term sigma nu → Prop}
    (hE : UnifClosure E) := Quotient (unifSetoid hE)

/-- Application representative of one certificate class. -/
structure QAppRep {E : Term sigma nu → Term sigma nu → Prop}
    (hE : UnifClosure E) (q : UClass hE) where
  head : sigma
  args : List (Term sigma nu)
  class_eq : Quotient.mk (unifSetoid hE) (.app head args) = q

noncomputable def chooseQAppRep {E : Term sigma nu → Term sigma nu → Prop}
    {hE : UnifClosure E} {q : UClass hE} (h : Nonempty (QAppRep hE q)) : QAppRep hE q :=
  Classical.choice h

/-- Coalgebra structure on certificate classes. A class containing an
application exposes an application representative; a variable-only class is one
residual `Unit` leaf. -/
noncomputable def closureViewQ {E : Term sigma nu → Term sigma nu → Prop}
    (hE : UnifClosure E) (q : UClass hE) : (infTermP sigma Unit) (UClass hE) := by
  classical
  exact if h : Nonempty (QAppRep hE q) then
    let r := chooseQAppRep h
    ⟨Sum.inr (r.head, r.args.length),
      fun i => Quotient.mk (unifSetoid hE) (r.args.get i)⟩
  else
    ⟨Sum.inl (), fun i => Fin.elim0 i⟩

/-- Corecursive infinite tree represented by one certificate class. -/
noncomputable def unfoldQ {E : Term sigma nu → Term sigma nu → Prop}
    (hE : UnifClosure E) (t : Term sigma nu) : InfTerm sigma Unit :=
  PFunctor.M.corec (closureViewQ hE) (Quotient.mk (unifSetoid hE) t)

/-- Related finite terms unfold to the same infinite tree. -/
theorem unfoldQ_eq_of_rel {E : Term sigma nu → Term sigma nu → Prop}
    (hE : UnifClosure E) {s t : Term sigma nu} (hst : E s t) :
    unfoldQ hE s = unfoldQ hE t := by
  apply congrArg (PFunctor.M.corec (closureViewQ hE))
  exact Quotient.sound hst

/-- At an application class, the chosen coalgebra representative has exactly the
same symbol and child classes as the application itself. -/
lemma closureViewQ_app {E : Term sigma nu → Term sigma nu → Prop}
    (hE : UnifClosure E) (f : sigma) (xs : List (Term sigma nu)) :
    closureViewQ hE (Quotient.mk (unifSetoid hE) (.app f xs)) =
      (⟨Sum.inr (f, xs.length),
        fun i => Quotient.mk (unifSetoid hE) (xs.get i)⟩ :
        (infTermP sigma Unit) (UClass hE)) := by
  classical
  let q : UClass hE := Quotient.mk (unifSetoid hE) (.app f xs)
  have hq : Nonempty (QAppRep hE q) := ⟨⟨f, xs, rfl⟩⟩
  let r : QAppRep hE q := chooseQAppRep hq
  have hrel : E (.app r.head r.args) (.app f xs) :=
    (Quotient.eq).1 r.class_eq
  have hd := hE.decomp hrel
  have hhead : r.head = f := hd.1
  have hargs : List.Forall₂ E r.args xs := hd.2
  have hlen : r.args.length = xs.length := hargs.length_eq
  change closureViewQ hE q = _
  rw [closureViewQ]
  simp only [dif_pos hq]
  change (⟨Sum.inr (r.head, r.args.length),
    fun i => Quotient.mk (unifSetoid hE) (r.args.get i)⟩ :
    (infTermP sigma Unit) (UClass hE)) = _
  apply Sigma.ext
  · exact congrArg Sum.inr (Prod.ext hhead hlen)
  · apply (Fin.heq_fun_iff hlen).2
    intro i
    exact Quotient.sound (hargs.get i.2 (hlen ▸ i.2))

/-- Corecursive unfolding is homomorphic on finite application nodes. -/
lemma unfoldQ_app {E : Term sigma nu → Term sigma nu → Prop}
    (hE : UnifClosure E) (f : sigma) (xs : List (Term sigma nu)) :
    unfoldQ hE (.app f xs) = InfTerm.app f (xs.map (unfoldQ hE)) := by
  rw [unfoldQ, PFunctor.M.corec_def, closureViewQ_app]
  change PFunctor.M.mk _ = PFunctor.M.mk _
  apply congrArg PFunctor.M.mk
  change (⟨Sum.inr (f, xs.length),
    PFunctor.M.corec (closureViewQ hE) ∘ fun i => Quotient.mk (unifSetoid hE) (xs.get i)⟩ :
      (infTermP sigma Unit) (InfTerm sigma Unit)) = _
  apply Sigma.ext
  · simp
  · apply (Fin.heq_fun_iff (by simp)).2
    intro i
    simp [unfoldQ]

/-- Applying the substitution extracted from a certificate is exactly class
unfolding. -/
lemma infApply_unfoldQ {E : Term sigma nu → Term sigma nu → Prop}
    (hE : UnifClosure E) (t : Term sigma nu) :
    InfApply (fun x => unfoldQ hE (.var x)) t = unfoldQ hE t := by
  induction t using Term.rec' with
  | hvar x => simp only [InfApply]
  | happ f args ih =>
      simp only [InfApply]
      rw [unfoldQ_app]
      congr 1
      exact List.map_congr_left (fun a ha => ih a ha)

/-- Every finite union/find certificate has an explicit infinite-term unifier. -/
theorem infinite_of_omegaUnifiableShared {s t : Term sigma nu}
    (h : OmegaUnifiableShared s t) : InfiniteOmegaUnifiableShared s t := by
  rcases h with ⟨E, hE, hst⟩
  refine ⟨fun x => unfoldQ hE (.var x), ?_⟩
  rw [infApply_unfoldQ hE, infApply_unfoldQ hE]
  exact unfoldQ_eq_of_rel hE hst

/-- The finite certificate and explicit infinite-term semantics coincide. -/
theorem omegaUnifiableShared_iff_infinite (s t : Term sigma nu) :
    OmegaUnifiableShared s t ↔ InfiniteOmegaUnifiableShared s t :=
  ⟨infinite_of_omegaUnifiableShared, omegaUnifiableShared_of_infinite⟩

/-- D4's rename-apart omega-unifiability is exactly the explicit infinite-term
semantics. This removes the certificate/provenance gap from the summit. -/
theorem omegaUnifiable_iff_infinite (s t : Term sigma nu) :
    OmegaUnifiable s t ↔ InfiniteOmegaUnifiable s t :=
  omegaUnifiableShared_iff_infinite (leftCopy s) (rightCopy t)

/-! ## Clash: the negative instrument -/

/-- Inside a unification closure, related applications carry the same symbol.
Every non-omega-unifiability proof in the campaign ends at this lemma. -/
theorem UnifClosure.symbol_eq {E : Term sigma nu → Term sigma nu → Prop}
    (hE : UnifClosure E) {f g : sigma} {xs ys : List (Term sigma nu)}
    (h : E (.app f xs) (.app g ys)) : f = g :=
  (hE.decomp h).1

/-- When two **applications** are related inside a unification closure, their
argument lists are related pointwise. Variable-to-application pairs are
intentionally permitted: they are precisely what omitting the occurs check adds,
as the `OccursCheck` fixture below demonstrates. Thus this theorem is an
application/application decomposition instrument, not a variable/application
clash rule. -/
theorem UnifClosure.args_forall₂ {E : Term sigma nu → Term sigma nu → Prop}
    (hE : UnifClosure E) {f g : sigma} {xs ys : List (Term sigma nu)}
    (h : E (.app f xs) (.app g ys)) : List.Forall₂ E xs ys :=
  (hE.decomp h).2

/-! ## Finite unifiers give omega-unifiers -/

/-- A list map equality is a pointwise relation under the map's kernel. -/
theorem forall₂_of_map_eq {alpha : Type u} {beta : Type v} {f : alpha → beta} :
    ∀ {xs ys : List alpha}, xs.map f = ys.map f →
      List.Forall₂ (fun a b => f a = f b) xs ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => exact List.Forall₂.nil
      | cons b bs => simp at h
  | cons a as ih =>
      intro ys h
      cases ys with
      | nil => simp at h
      | cons b bs =>
          simp only [List.map_cons, List.cons.injEq] at h
          exact List.Forall₂.cons h.1 (ih h.2)

/-- A single substitution that equates two terms is a unification closure
certificate: the kernel of `Subst.apply r` is one. -/
theorem omegaUnifiableShared_of_subst {s t : Term sigma nu} (r : Subst sigma nu)
    (h : Subst.apply r s = Subst.apply r t) : OmegaUnifiableShared s t := by
  refine ⟨fun a b => Subst.apply r a = Subst.apply r b, ⟨fun _ => rfl, fun hst => hst.symm,
    fun hst htu => hst.trans htu, ?_⟩, h⟩
  intro f g xs ys hab
  simp only [Subst.apply_app, Term.app.injEq] at hab
  obtain ⟨hfg, hargs⟩ := hab
  refine ⟨hfg, ?_⟩
  rw [Subst.applyList_eq_map, Subst.applyList_eq_map] at hargs
  exact forall₂_of_map_eq hargs

/-- **Unifiability implies omega-unifiability** (frozen D4, final sentence), in
D4's two-substitution form: `a` acts on the left term's variables, `b` on the
right term's, and the two images agree. -/
theorem omegaUnifiable_of_unifier {s t : Term sigma nu} (a b : Subst sigma nu)
    (h : Subst.apply a s = Subst.apply b t) : OmegaUnifiable s t := by
  refine omegaUnifiableShared_of_subst
    (fun v => Sum.elim (fun x => Term.mapVar Sum.inl (a x))
      (fun y => Term.mapVar Sum.inl (b y)) v) ?_
  have hl : Subst.apply (fun v => Sum.elim (fun x => Term.mapVar Sum.inl (a x))
      (fun y => Term.mapVar Sum.inl (b y)) v) (leftCopy s)
      = Term.mapVar Sum.inl (Subst.apply a s) :=
    Term.apply_mapVar_of (g := Sum.inl) (h := Sum.inl) (s := a) (fun _ => rfl) s
  have hr : Subst.apply (fun v => Sum.elim (fun x => Term.mapVar Sum.inl (a x))
      (fun y => Term.mapVar Sum.inl (b y)) v) (rightCopy t)
      = Term.mapVar Sum.inl (Subst.apply b t) :=
    Term.apply_mapVar_of (g := Sum.inr) (h := Sum.inl) (s := b) (fun _ => rfl) t
  rw [hl, hr, h]

/-! ## Building certificates from a finite list of classes -/

/-- The relation "equal, or jointly inside one of the listed classes". Every
positive omega-unifiability witness in the campaign is presented this way. -/
def classesRel (Cs : List (List (Term sigma nu))) (a b : Term sigma nu) : Prop :=
  a = b ∨ ∃ C ∈ Cs, a ∈ C ∧ b ∈ C

theorem forall₂_classesRel_refl (Cs : List (List (Term sigma nu)))
    (xs : List (Term sigma nu)) : List.Forall₂ (classesRel Cs) xs xs := by
  induction xs with
  | nil => exact List.Forall₂.nil
  | cons a as ih => exact List.Forall₂.cons (Or.inl rfl) ih

/-- A list of classes gives a unification closure as soon as (i) two classes
sharing a member have the same members, and (ii) any two applications inside one
class agree on their symbol and have argumentwise related arguments. -/
theorem unifClosure_classesRel (Cs : List (List (Term sigma nu)))
    (hdisj : ∀ C ∈ Cs, ∀ D ∈ Cs, ∀ t : Term sigma nu,
      t ∈ C → t ∈ D → ∀ u : Term sigma nu, u ∈ D → u ∈ C)
    (hdec : ∀ C ∈ Cs, ∀ (f g : sigma) (xs ys : List (Term sigma nu)),
      Term.app f xs ∈ C → Term.app g ys ∈ C →
      f = g ∧ List.Forall₂ (classesRel Cs) xs ys) :
    UnifClosure (classesRel Cs) := by
  refine ⟨fun _ => Or.inl rfl, ?_, ?_, ?_⟩
  · rintro s t (rfl | ⟨C, hC, hs, ht⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨C, hC, ht, hs⟩
  · rintro s t u (rfl | ⟨C, hC, hs, ht⟩) h2
    · exact h2
    · rcases h2 with rfl | ⟨D, hD, ht', hu⟩
      · exact Or.inr ⟨C, hC, hs, ht⟩
      · exact Or.inr ⟨C, hC, hs, hdisj C hC D hD _ ht ht' _ hu⟩
  · rintro f g xs ys (heq | ⟨C, hC, ha, hb⟩)
    · obtain ⟨hfg, hargs⟩ := Term.app.injEq f xs g ys ▸ heq
      subst hfg; subst hargs
      exact ⟨rfl, forall₂_classesRel_refl Cs xs⟩
    · exact hdec C hC f g xs ys ha hb

/-! ## Worked example 1: the occurs check

`x` and `f(x)` share the variable `x`. The source-level rational-tree reading
solves this equation by the regular infinite tree `f(f(f(...)))`. The finite
certificate below gives the single class `{x, f(x)}`; the new semantic bridge
then corecursively unfolds that class to an explicit M-type infinite unifier.
No finite substitution unifies them, because a finite unifier would have to
satisfy `r x = f (r x)`, which no finite term does. Thus the fixture separates
finite unification from omega-unifiability on the same Lean carrier. -/

namespace OccursCheck

/-- The variable `x`. -/
def xTm : Term Nat Nat := .var 0

/-- The term `f(x)`, with `f` the symbol `0`. -/
def fxTm : Term Nat Nat := .app 0 [.var 0]

/-- The single-class certificate `{x, f(x)}`. -/
def cert : List (List (Term Nat Nat)) := [[xTm, fxTm]]

/-- The certificate is a unification closure. The only application in the class
is `f(x)`, so the decomposition condition is the reflexive case. -/
theorem cert_closure : UnifClosure (classesRel cert) := by
  refine unifClosure_classesRel cert ?_ ?_
  · intro C hC D hD t _ _ u hu
    simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hC hD
    subst hC; subst hD; exact hu
  · intro C hC f g xs ys ha hb
    simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hC
    subst hC
    simp only [xTm, fxTm, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      simp_all only [reduceCtorEq, Term.app.injEq]
    exact ⟨by trivial, forall₂_classesRel_refl cert _⟩

/-- `x` and `f(x)` are omega-unifiable although they share the variable `x`. -/
theorem omegaUnifiableShared : OmegaUnifiableShared xTm fxTm :=
  ⟨classesRel cert, cert_closure,
    Or.inr ⟨[xTm, fxTm], List.Mem.head _, List.Mem.head _,
      List.Mem.tail _ (List.Mem.head _)⟩⟩

/-- The occurs-check fixture has an explicit infinite-term substitution witness. -/
theorem infiniteOmegaUnifiableShared : InfiniteOmegaUnifiableShared xTm fxTm :=
  (omegaUnifiableShared_iff_infinite xTm fxTm).mp omegaUnifiableShared

/-- No finite substitution unifies `x` with `f(x)`: the occurs check. The size of
`r x` would have to exceed itself. -/
theorem not_unifiable : ¬ ∃ r : Subst Nat Nat, Subst.apply r xTm = Subst.apply r fxTm := by
  rintro ⟨r, h⟩
  simp only [xTm, fxTm, Subst.apply_var, Subst.apply_app, Subst.applyList_cons,
    Subst.applyList_nil] at h
  have hsize := congrArg Term.size h
  simp only [Term.size_app, Term.sizeList_cons, Term.sizeList_nil] at hsize
  omega

end OccursCheck

/-! ## Worked example 2: Huet's system, the paper's Example 1

> "By Huet: { F(x, x) -> A, F(x, G(x)) -> B, C -> G(C) }. The term F(C, C)
> possesses two distinct normal forms, A and B. However, in a certain sense the
> first two rules overlap semantically: the infinite term G(G(...)) provides such
> an overlap." (frozen `definitions.md` source, p.1)

The two left-hand sides are **not** unifiable, so the system is non-overlapping,
and they **are** omega-unifiable, so it is omega-overlapping. That pair of facts
is exactly why Huet's system fails UN= without contradicting the theorem of
RTA #79, and both halves are proved here.

Symbols: `F = 1`, `G = 2`. Variables after rename-apart: `x1 = inl 0` on the
left, `x2 = inr 0` on the right. -/

namespace Huet

/-- `F(x, x)`, the first rule's left-hand side. -/
def lhs₁ : Term Nat Nat := .app 1 [.var 0, .var 0]

/-- `F(x, G(x))`, the second rule's left-hand side. -/
def lhs₂ : Term Nat Nat := .app 1 [.var 0, .app 2 [.var 0]]

/-- The left copy `F(x1, x1)`. -/
def L : Term Nat (Nat ⊕ Nat) := leftCopy lhs₁

/-- The right copy `F(x2, G(x2))`. -/
def Rt : Term Nat (Nat ⊕ Nat) := rightCopy lhs₂

/-- The lower class: the two renamed-apart variables together with the rational
overlap `G(x2)`. Its only application is `G(x2)`. -/
def lowClass : List (Term Nat (Nat ⊕ Nat)) :=
  [.var (.inl 0), .var (.inr 0), .app 2 [.var (.inr 0)]]

/-- The two-class certificate: the lower class, and the class holding the two
left-hand sides. -/
def cert : List (List (Term Nat (Nat ⊕ Nat))) := [lowClass, [L, Rt]]

theorem L_eq : L = .app 1 [.var (.inl 0), .var (.inl 0)] := rfl
theorem Rt_eq : Rt = .app 1 [.var (.inr 0), .app 2 [.var (.inr 0)]] := rfl

/-- Any two members of the lower class are related by the certificate. -/
theorem low_rel {p q : Term Nat (Nat ⊕ Nat)} (hp : p ∈ lowClass) (hq : q ∈ lowClass) :
    classesRel cert p q :=
  Or.inr ⟨lowClass, List.Mem.head _, hp, hq⟩

/-- The certificate is a unification closure. The lower class contains one
application, `G(x2)`; the upper class contains two, and their arguments are
pairwise inside the lower class. -/
theorem cert_closure : UnifClosure (classesRel cert) := by
  refine unifClosure_classesRel cert ?_ ?_
  · intro C hC D hD t htC htD u hu
    simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hC hD
    rcases hC with rfl | rfl <;> rcases hD with rfl | rfl
    · exact hu
    · revert htC htD
      simp only [lowClass, List.mem_cons, List.not_mem_nil, or_false, L_eq, Rt_eq]
      rintro (rfl | rfl | rfl) (h | h) <;> simp_all
    · revert htC htD
      simp only [lowClass, List.mem_cons, List.not_mem_nil, or_false, L_eq, Rt_eq]
      rintro (rfl | rfl) (h | h | h) <;> simp_all
    · exact hu
  · intro C hC f g xs ys ha hb
    simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · -- lower class: the only application is `G(x2)`
      simp only [lowClass, List.mem_cons, List.not_mem_nil, or_false] at ha hb
      rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
        simp_all only [reduceCtorEq, Term.app.injEq]
      exact ⟨by trivial, forall₂_classesRel_refl cert _⟩
    · -- upper class: `F(x1, x1)` and `F(x2, G(x2))`
      simp only [List.mem_cons, List.not_mem_nil, or_false, L_eq, Rt_eq] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb <;>
        injection ha with hf hxs <;> injection hb with hg hys <;>
        subst hf <;> subst hxs <;> subst hg <;> subst hys <;>
        refine ⟨rfl, ?_⟩ <;>
        exact List.Forall₂.cons (low_rel (by simp [lowClass]) (by simp [lowClass]))
          (List.Forall₂.cons (low_rel (by simp [lowClass]) (by simp [lowClass]))
            List.Forall₂.nil)

/-- **Huet's two left-hand sides are omega-unifiable.** -/
theorem lhs_omegaUnifiable : OmegaUnifiable lhs₁ lhs₂ :=
  ⟨classesRel cert, cert_closure,
    Or.inr ⟨[L, Rt], List.Mem.tail _ (List.Mem.head _),
      List.Mem.head _, List.Mem.tail _ (List.Mem.head _)⟩⟩

/-- Huet's overlap has an explicit infinite-term substitution witness. -/
theorem lhs_infiniteOmegaUnifiable : InfiniteOmegaUnifiable lhs₁ lhs₂ :=
  (omegaUnifiable_iff_infinite lhs₁ lhs₂).mp lhs_omegaUnifiable

/-- **Huet's two left-hand sides are not unifiable.** A unifier would force
`a x = b x` and `a x = G(b x)`, so `a x` would have to be strictly larger than
itself. Huet's system is therefore non-overlapping in the finite sense. -/
theorem lhs_not_unifiable :
    ¬ ∃ a b : Subst Nat Nat, Subst.apply a lhs₁ = Subst.apply b lhs₂ := by
  rintro ⟨a, b, h⟩
  simp only [lhs₁, lhs₂, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
    Subst.apply_var, Term.app.injEq, List.cons.injEq, and_true] at h
  obtain ⟨-, h1, h2⟩ := h
  rw [h1] at h2
  have hsize := congrArg Term.size h2
  simp only [Term.size_app, Term.sizeList_cons, Term.sizeList_nil] at hsize
  omega

end Huet

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.UnifClosure
#check @OperatorKO7.Meta.UniqueNormalization.OmegaUnifiableShared
#check @OperatorKO7.Meta.UniqueNormalization.OmegaUnifiable
#check @OperatorKO7.Meta.UniqueNormalization.leftCopy
#check @OperatorKO7.Meta.UniqueNormalization.rightCopy
#check @OperatorKO7.Meta.UniqueNormalization.classesRel
#check @OperatorKO7.Meta.UniqueNormalization.InfTerm
#check @OperatorKO7.Meta.UniqueNormalization.InfiniteOmegaUnifiableShared
#check @OperatorKO7.Meta.UniqueNormalization.InfiniteOmegaUnifiable
#check @OperatorKO7.Meta.UniqueNormalization.omegaUnifiableShared_iff_infinite
#check @OperatorKO7.Meta.UniqueNormalization.omegaUnifiable_iff_infinite

#print axioms OperatorKO7.Meta.UniqueNormalization.InfTerm.app_inj
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiableShared_of_infiniteSubst
#print axioms OperatorKO7.Meta.UniqueNormalization.infinite_of_omegaUnifiableShared
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiableShared_iff_infinite
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiable_iff_infinite
#print axioms OperatorKO7.Meta.UniqueNormalization.OccursCheck.infiniteOmegaUnifiableShared
#print axioms OperatorKO7.Meta.UniqueNormalization.Huet.lhs_infiniteOmegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.UnifClosure.symbol_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiableShared_of_subst
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiable_of_unifier
#print axioms OperatorKO7.Meta.UniqueNormalization.unifClosure_classesRel
#print axioms OperatorKO7.Meta.UniqueNormalization.OccursCheck.omegaUnifiableShared
#print axioms OperatorKO7.Meta.UniqueNormalization.OccursCheck.not_unifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.Huet.lhs_omegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.Huet.lhs_not_unifiable

#check @OperatorKO7.Meta.UniqueNormalization.forall₂_of_map_eq

#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_of_map_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.InfTerm
#print axioms OperatorKO7.Meta.UniqueNormalization.InfSubst
#print axioms OperatorKO7.Meta.UniqueNormalization.UClass
