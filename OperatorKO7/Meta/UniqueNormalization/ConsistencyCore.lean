import OperatorKO7.Meta.UniqueNormalization.ConstructorCompatibility
import OperatorKO7.Meta.UniqueNormalization.GroundUnification

/-!
# The consistency core: tilde algebra, sigma-closure, and Corollary 35

Campaign: `Roadmaps\klop\ROADMAP.md`, wave 5. Source: Kahrs and Smith, FSCD 2016,
Section 5, transcribed in `Roadmaps\klop\definitions.md` at D10, D11, D12.

This module carries the part of Section 5 that the campaign audit reported as
blocked, and the block is now removed. Amendment A3 of the frozen definitions
records that Definition 30's middle factor carries a destructor-tilde underline
which PDF text extraction drops. Under the corrected reading the two redexes of a
semantical critical pair share their root symbol and have argumentwise related
direct subterms, which is precisely the input Corollary 35's proof consumes when
it says "its direct subterms are constructor terms. Thus Lemma 33 applies".

`cor35` below is that step, machine-checked.

## Fidelity block (frozen `definitions.md`, D10, the tilde construction)

> "if R is contained in A x B, where A and B are term-coalgebras then R-tilde is
> contained in A x B and is defined as follows: for all t in A, for all u in B,
> t R-tilde u iff there exist F in Sigma, a_1 ... a_n in A, b_1 ... b_n in B with
> t = F(a_1, ..., a_n) and u = F(b_1, ..., b_n) and for all i, a_i R b_i"

> "we modified it slightly by removing the reflexivity case. For constructor
> signatures, we use the notations [R with underline] and [R with hat] to mean
> R-tilde for the subsignatures Sigma_d and Sigma_c, respectively."

> "A relation R between term-coalgebras is called Sigma-closed iff R-tilde is
> contained in R." (Definition 24)

> "Let V be the set of relations between term-coalgebras A and B. Then the
> function CT is defined by CT(R) = mu x. R union x-tilde. Thus CT(R) is the
> smallest Sigma-closed relation containing R." (Definition 25)

`tildeOn` takes the symbol predicate as a parameter, so `hatRel` and `barRel` are
its two instances and the reflexivity case is absent by construction: both sides
of a tilde are applications sharing a root symbol.

`CT` is defined by its universal property, as the intersection of every
Sigma-closed relation containing the argument. That is the least fixed point of
the monotone operator of Definition 25, and it yields the three facts the source
uses (contains, Sigma-closed, least) without a recursor.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v w w'

variable {sigma : Type u} {nu : Type v}

/-! ## List plumbing

Two directions of the same fact: an argumentwise relation between two images of
one list under two maps is the pointwise relation on the list's members. -/

/-- Build an argumentwise relation between two maps of one list. -/
theorem forall₂_of_pointwise {alpha : Type u} {beta : Type v} {gamma : Type w}
    {r : beta → gamma → Prop} {f : alpha → beta} {g : alpha → gamma} :
    ∀ {l : List alpha}, (∀ a ∈ l, r (f a) (g a)) →
      List.Forall₂ r (l.map f) (l.map g) := by
  intro l
  induction l with
  | nil => intro _; exact List.Forall₂.nil
  | cons a as ih =>
      intro h
      exact List.Forall₂.cons (h a (List.mem_cons_self ..))
        (ih (fun q hq => h q (List.mem_cons_of_mem _ hq)))

/-- Read a pointwise relation off an argumentwise relation between two maps. -/
theorem pointwise_of_forall₂ {alpha : Type u} {beta : Type v} {gamma : Type w}
    {r : beta → gamma → Prop} {f : alpha → beta} {g : alpha → gamma} :
    ∀ {l : List alpha}, List.Forall₂ r (l.map f) (l.map g) →
      ∀ a ∈ l, r (f a) (g a) := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons a as ih =>
      intro h q hq
      rw [List.map_cons, List.map_cons] at h
      cases h with
      | cons hhead htail =>
          rcases List.mem_cons.mp hq with rfl | hmem
          · exact hhead
          · exact ih htail q hmem

/-- Argumentwise relations transfer along an implication. -/
theorem forall₂_mono {alpha : Type u} {beta : Type v} {r s : alpha → beta → Prop}
    (h : ∀ a b, r a b → s a b) :
    ∀ {l₁ : List alpha} {l₂ : List beta}, List.Forall₂ r l₁ l₂ → List.Forall₂ s l₁ l₂ := by
  intro l₁ l₂ hr
  induction hr with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih => exact List.Forall₂.cons (h _ _ hab) ih

/-- Argumentwise relations reverse when the relation itself is reversed. -/
theorem forall₂_flip {alpha : Type u} {beta : Type v} {r : alpha → beta → Prop} :
    ∀ {l₁ : List alpha} {l₂ : List beta}, List.Forall₂ r l₁ l₂ →
      List.Forall₂ (fun b a => r a b) l₂ l₁ := by
  intro l₁ l₂ h
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih => exact List.Forall₂.cons hab ih

/-- Argumentwise relations reverse under a symmetric relation. -/
theorem forall₂_swap {alpha : Type u} {r : alpha → alpha → Prop}
    (hsymm : ∀ a b, r a b → r b a) :
    ∀ {l₁ l₂ : List alpha}, List.Forall₂ r l₁ l₂ → List.Forall₂ r l₂ l₁ := by
  intro l₁ l₂ hr
  induction hr with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih => exact List.Forall₂.cons (hsymm _ _ hab) ih

/-- A reflexive relation relates a list to itself argumentwise. -/
theorem forall₂_self {alpha : Type u} {r : alpha → alpha → Prop}
    (hrefl : ∀ a, r a a) (l : List alpha) : List.Forall₂ r l l := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a as ih => exact List.Forall₂.cons (hrefl a) ih

/-! ## Relations on the doubled signature -/

/-- A relation between terms of the doubled signature. -/
abbrev CRel (sigma : Type u) (nu : Type v) :=
  Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu → Prop

/-! ## The tilde construction, frozen definition D10

The reflexivity case is absent: both sides are applications with one shared root
symbol, and the symbol satisfies the predicate `P`. -/

/-- `tildeOn P E` relates two applications whose shared root symbol satisfies `P`
and whose arguments are argumentwise related by `E`. -/
def tildeOn (P : sigma ⊕ sigma → Prop) (E : CRel sigma nu) : CRel sigma nu :=
  fun t u => ∃ (f : sigma ⊕ sigma) (as bs : List (Term (sigma ⊕ sigma) nu)),
    P f ∧ t = .app f as ∧ u = .app f bs ∧ List.Forall₂ E as bs

/-- The tilde over the whole signature. -/
def tildeAll (E : CRel sigma nu) : CRel sigma nu := tildeOn (fun _ => True) E

/-- The tilde over the constructor subsignature, written with a hat in the
source. -/
def hatRel (E : CRel sigma nu) : CRel sigma nu :=
  tildeOn (fun f => ∃ c : sigma, f = Sum.inl c) E

/-- The tilde over the destructor subsignature, written with an underline in the
source. This is the relation amendment A3 restores to Definition 30. -/
def barRel (E : CRel sigma nu) : CRel sigma nu :=
  tildeOn (fun f => ∃ d : sigma, f = Sum.inr d) E

/-! ## Proposition 23, the relational-algebra laws -/

/-- The tilde is monotone in its relation argument. -/
theorem tildeOn_mono {P : sigma ⊕ sigma → Prop} {E E' : CRel sigma nu}
    (h : ∀ a b, E a b → E' a b) {t u : Term (sigma ⊕ sigma) nu}
    (ht : tildeOn P E t u) : tildeOn P E' t u := by
  obtain ⟨f, as, bs, hP, hta, hub, hall⟩ := ht
  exact ⟨f, as, bs, hP, hta, hub, forall₂_mono h hall⟩

/-- The tilde is monotone in its symbol predicate. -/
theorem tildeOn_mono_pred {P Q : sigma ⊕ sigma → Prop} (h : ∀ f, P f → Q f)
    {E : CRel sigma nu} {t u : Term (sigma ⊕ sigma) nu}
    (ht : tildeOn P E t u) : tildeOn Q E t u := by
  obtain ⟨f, as, bs, hP, hta, hub, hall⟩ := ht
  exact ⟨f, as, bs, h f hP, hta, hub, hall⟩

/-- The constructor tilde is part of the full tilde. -/
theorem tildeAll_of_hatRel {E : CRel sigma nu} {t u : Term (sigma ⊕ sigma) nu}
    (h : hatRel E t u) : tildeAll E t u :=
  tildeOn_mono_pred (fun _ _ => trivial) h

/-- The destructor tilde is part of the full tilde. -/
theorem tildeAll_of_barRel {E : CRel sigma nu} {t u : Term (sigma ⊕ sigma) nu}
    (h : barRel E t u) : tildeAll E t u :=
  tildeOn_mono_pred (fun _ _ => trivial) h

/-- The full tilde splits into its two halves, since every symbol of the doubled
signature is a constructor or a destructor. -/
theorem hatRel_or_barRel_of_tildeAll {E : CRel sigma nu} {t u : Term (sigma ⊕ sigma) nu}
    (h : tildeAll E t u) : hatRel E t u ∨ barRel E t u := by
  obtain ⟨f, as, bs, -, hta, hub, hall⟩ := h
  cases f with
  | inl c => exact Or.inl ⟨.inl c, as, bs, ⟨c, rfl⟩, hta, hub, hall⟩
  | inr d => exact Or.inr ⟨.inr d, as, bs, ⟨d, rfl⟩, hta, hub, hall⟩

/-- The tilde commutes with converse. -/
theorem tildeOn_flip {P : sigma ⊕ sigma → Prop} {E : CRel sigma nu}
    {t u : Term (sigma ⊕ sigma) nu}
    (h : tildeOn P (fun a b => E b a) t u) : tildeOn P E u t := by
  obtain ⟨f, as, bs, hP, hta, hub, hall⟩ := h
  exact ⟨f, bs, as, hP, hub, hta, forall₂_flip hall⟩

/-! ## Sigma-closure and `CT`, frozen definitions D10 (Definition 24, 25) -/

/-- **Definition 24.** A relation is Sigma-closed when the tilde of the relation
is part of the relation. -/
def SigmaClosed (E : CRel sigma nu) : Prop :=
  ∀ t u : Term (sigma ⊕ sigma) nu, tildeAll E t u → E t u

/-- **Definition 25.** `CT E` is the smallest Sigma-closed relation containing
`E`, presented by its universal property. -/
def CT (E : CRel sigma nu) : CRel sigma nu :=
  fun t u => ∀ S : CRel sigma nu,
    (∀ a b, E a b → S a b) → SigmaClosed S → S t u

/-- `CT E` contains `E`. -/
theorem CT.base {E : CRel sigma nu} {a b : Term (sigma ⊕ sigma) nu} (h : E a b) :
    CT E a b :=
  fun _ hsub _ => hsub a b h

/-- `CT E` is contained in every Sigma-closed relation containing `E`. -/
theorem CT.least {E S : CRel sigma nu} (hsub : ∀ a b, E a b → S a b)
    (hcl : SigmaClosed S) {a b : Term (sigma ⊕ sigma) nu} (h : CT E a b) : S a b :=
  h S hsub hcl

/-- `CT E` is Sigma-closed. -/
theorem CT.sigmaClosed {E : CRel sigma nu} : SigmaClosed (CT E) := by
  intro t u ht S hsub hcl
  refine hcl t u (tildeOn_mono ?_ ht)
  intro a b hab
  exact hab S hsub hcl

/-- The application clause of `CT E`, read off Sigma-closure. -/
theorem CT.app {E : CRel sigma nu} {f : sigma ⊕ sigma}
    {as bs : List (Term (sigma ⊕ sigma) nu)} (h : List.Forall₂ (CT E) as bs) :
    CT E (.app f as) (.app f bs) :=
  CT.sigmaClosed _ _ ⟨f, as, bs, trivial, rfl, rfl, h⟩

/-- `CT` is monotone. -/
theorem CT.mono {E E' : CRel sigma nu} (h : ∀ a b, E a b → E' a b)
    {a b : Term (sigma ⊕ sigma) nu} (hab : CT E a b) : CT E' a b :=
  CT.least (fun p q hpq => CT.base (h p q hpq)) CT.sigmaClosed hab

/-! ## Lemma 29, closure properties of constructor compatibility -/

/-- **Lemma 29, converse half.** The converse of a constructor-compatible
relation is constructor-compatible. -/
theorem constructorCompatible_flip {E : CRel sigma nu} (h : ConstructorCompatible E) :
    ConstructorCompatible (fun a b => E b a) := by
  intro a b hca hcb hab
  rcases h b a hcb hca hab with ⟨x, hbx, hax⟩ | ⟨f, xs, ys, hbx, hay, hall⟩
  · exact Or.inl ⟨x, hax, hbx⟩
  · exact Or.inr ⟨f, ys, xs, hay, hbx, forall₂_flip hall⟩

/-- **Lemma 29, union half.** An arbitrary union of constructor-compatible
relations is constructor-compatible. The decomposition happens inside a single
member of the family, and argumentwise relatedness then transfers to the
union. -/
theorem constructorCompatible_iSup {iota : Type w} (E : iota → CRel sigma nu)
    (h : ∀ i, ConstructorCompatible (E i)) :
    ConstructorCompatible (fun a b => ∃ i, E i a b) := by
  intro a b hca hcb hab
  obtain ⟨i, hi⟩ := hab
  rcases h i a b hca hcb hi with hvar | ⟨f, xs, ys, hax, hby, hall⟩
  · exact Or.inl hvar
  · exact Or.inr ⟨f, xs, ys, hax, hby, forall₂_mono (fun _ _ hx => ⟨i, hx⟩) hall⟩


/-! ## Context closure and constructor decomposition -/

/-- Context closure is the least fixed point of adjoining application pairs. -/
theorem CT.unfold {E : CRel sigma nu} {a b : Term (sigma ⊕ sigma) nu} :
    CT E a b ↔ E a b ∨ tildeAll (CT E) a b := by
  constructor
  · intro hab
    apply CT.least (S := fun p q => E p q ∨ tildeAll (CT E) p q)
      (fun _ _ h => Or.inl h) ?_ hab
    intro p q hpq
    exact Or.inr (tildeOn_mono
      (fun _ _ h => h.elim CT.base (CT.sigmaClosed _ _)) hpq)
  · intro h
    exact h.elim CT.base (CT.sigmaClosed _ _)

/-- A relation already closed under every symbol is its own context closure. -/
theorem CT.eq_of_sigmaClosed {E : CRel sigma nu} (hE : SigmaClosed E)
    {a b : Term (sigma ⊕ sigma) nu} : CT E a b ↔ E a b :=
  ⟨CT.least (fun _ _ h => h) hE, CT.base⟩

theorem CT.idempotent {E : CRel sigma nu} {a b : Term (sigma ⊕ sigma) nu} :
    CT (CT E) a b ↔ CT E a b :=
  CT.eq_of_sigmaClosed CT.sigmaClosed

theorem CT.refl {E : CRel sigma nu} (hE : ∀ a, E a a)
    (a : Term (sigma ⊕ sigma) nu) : CT E a a :=
  CT.base (hE a)

/-- Context closure commutes with reversal of the base relation. -/
theorem CT.flip {E : CRel sigma nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : CT (fun p q => E q p) a b) : CT E b a := by
  apply CT.least (S := fun p q => CT E q p)
    (fun _ _ hE => CT.base hE) ?_ h
  intro p q hpq
  exact CT.sigmaClosed q p (tildeOn_flip hpq)

theorem CT.symm {E : CRel sigma nu} (hE : ∀ a b, E a b → E b a)
    {a b : Term (sigma ⊕ sigma) nu} (h : CT E a b) : CT E b a :=
  CT.flip (CT.mono hE h)

/-- Context closure adds no pair with a variable at the left endpoint. -/
theorem CT.var_left_iff {E : CRel sigma nu} {x : nu}
    {b : Term (sigma ⊕ sigma) nu} : CT E (.var x) b ↔ E (.var x) b := by
  constructor
  · intro h
    rcases CT.unfold.mp h with hbase | ⟨f, xs, ys, _, hvar, _, _⟩
    · exact hbase
    · cases hvar
  · exact CT.base

/-- Context closure adds no pair with a variable at the right endpoint. -/
theorem CT.var_right_iff {E : CRel sigma nu} {x : nu}
    {a : Term (sigma ⊕ sigma) nu} : CT E a (.var x) ↔ E a (.var x) := by
  constructor
  · intro h
    rcases CT.unfold.mp h with hbase | ⟨f, xs, ys, _, _, hvar, _⟩
    · exact hbase
    · cases hvar
  · exact CT.base

/-- Context closure preserves constructor compatibility without an equivalence,
transitivity, or rewrite-system premise. -/
theorem CT.constructorCompatible {E : CRel sigma nu}
    (hE : ConstructorCompatible E) : ConstructorCompatible (CT E) := by
  let S : CRel sigma nu := fun a b =>
    CT E a b ∧ (ConTopped a → ConTopped b →
      (∃ x : nu, a = .var x ∧ b = .var x) ∨
      (∃ (f : sigma) (xs ys : List (Term (sigma ⊕ sigma) nu)),
        a = .app (.inl f) xs ∧ b = .app (.inl f) ys ∧
          List.Forall₂ (CT E) xs ys))
  have hsub : ∀ a b, E a b → S a b := by
    intro a b hab
    refine ⟨CT.base hab, ?_⟩
    intro hca hcb
    rcases hE a b hca hcb hab with hvar | ⟨f, xs, ys, ha, hb, hargs⟩
    · exact Or.inl hvar
    · exact Or.inr ⟨f, xs, ys, ha, hb,
        forall₂_mono (fun _ _ h => CT.base h) hargs⟩
  have hcl : SigmaClosed S := by
    rintro a b ⟨f, xs, ys, _, rfl, rfl, hargs⟩
    have hct : List.Forall₂ (CT E) xs ys :=
      forall₂_mono (fun _ _ h => h.1) hargs
    refine ⟨CT.app hct, ?_⟩
    intro hca _
    cases f with
    | inl c => exact Or.inr ⟨c, xs, ys, rfl, rfl, hct⟩
    | inr d =>
        rcases hca with ⟨x, hx⟩ | ⟨c, args, heq⟩
        · cases hx
        · cases heq
  intro a b hca hcb hab
  exact (CT.least hsub hcl hab).2 hca hcb

/-- Constructor-headed context pairs have exactly matching symbols and
argumentwise context pairs. -/
theorem CT.constructor_apps_iff {E : CRel sigma nu}
    (hE : ConstructorCompatible E) {f g : sigma}
    {xs ys : List (Term (sigma ⊕ sigma) nu)} :
    CT E (.app (.inl f) xs) (.app (.inl g) ys) ↔
      f = g ∧ List.Forall₂ (CT E) xs ys := by
  constructor
  · intro h
    rcases CT.constructorCompatible hE _ _ (ConTopped.app f xs)
        (ConTopped.app g ys) h with
      ⟨x, hx, _⟩ | ⟨c, as, bs, hl, hr, hargs⟩
    · cases hx
    · simp only [Term.app.injEq, Sum.inl.injEq] at hl hr
      rcases hl with ⟨rfl, rfl⟩
      rcases hr with ⟨rfl, rfl⟩
      exact ⟨rfl, hargs⟩
  · rintro ⟨rfl, hargs⟩
    exact CT.app hargs

/-! ## Composition inside a subterm-closed carrier -/

/-- Compose argument relations using hypotheses for the actual three list members. -/
theorem forall₂_compose_of_mem {alpha : Type u} {beta : Type v} {gamma : Type w}
    {r : alpha → beta → Prop} {s : beta → gamma → Prop} {t : alpha → gamma → Prop} :
    ∀ {xs : List alpha} {ys : List beta} {zs : List gamma},
      List.Forall₂ r xs ys → List.Forall₂ s ys zs →
      (∀ a ∈ xs, ∀ b ∈ ys, ∀ c ∈ zs, r a b → s b c → t a c) →
      List.Forall₂ t xs zs := by
  intro xs ys zs hxy
  induction hxy generalizing zs with
  | nil =>
      intro hyz _
      cases hyz
      exact List.Forall₂.nil
  | @cons a b xs ys hab hrest ih =>
      intro hyz hcomp
      cases hyz with
      | cons hbc htail =>
          exact List.Forall₂.cons
            (hcomp _ (List.mem_cons_self ..) _ (List.mem_cons_self ..)
              _ (List.mem_cons_self ..) hab hbc)
            (ih htail (fun x hx y hy z hz hxy hyz =>
              hcomp x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
                z (List.mem_cons_of_mem _ hz) hxy hyz))

/-- Absorbing one base pair on either side suffices for context transitivity.
The induction is on the middle finite term, not on rewrite targets. -/
theorem CT.transitiveOn_of_base_absorption {E : CRel sigma nu}
    (C : Term (sigma ⊕ sigma) nu → Prop)
    (hC : ∀ f args, C (.app f args) → ∀ a ∈ args, C a)
    (hleft : ∀ a b c, C a → C b → C c → E a b → CT E b c → CT E a c)
    (hright : ∀ a b c, C a → C b → C c → CT E a b → E b c → CT E a c) :
    ∀ a b c, C a → C b → C c → CT E a b → CT E b c → CT E a c := by
  have main : ∀ b, C b → ∀ a c, C a → C c → CT E a b → CT E b c → CT E a c := by
    intro b
    induction b using Term.rec' with
    | hvar x =>
        intro hb a c ha hc hab hbc
        exact hleft a (.var x) c ha hb hc (CT.var_right_iff.mp hab) hbc
    | happ f bs ih =>
        intro hb a c ha hc hab hbc
        rcases CT.unfold.mp hab with hbase | hctx
        · exact hleft a (.app f bs) c ha hb hc hbase hbc
        rcases CT.unfold.mp hbc with hbase | hctx'
        · exact hright a (.app f bs) c ha hb hc hab hbase
        rcases hctx with ⟨g, xs, ys, _, rfl, hmid, hxy⟩
        have hfg : f = g := (Term.app.inj hmid).1
        have hbys : bs = ys := (Term.app.inj hmid).2
        subst g
        subst ys
        rcases hctx' with ⟨k, us, zs, _, hmid', rfl, hyz⟩
        have hfk : f = k := (Term.app.inj hmid').1
        have hbus : bs = us := (Term.app.inj hmid').2
        subst k
        subst us
        apply CT.app
        exact forall₂_compose_of_mem hxy hyz
          (fun x hx y hy z hz hxy hyz =>
            ih y hy (hC f bs hb y hy) x z
              (hC f xs ha x hx) (hC f zs hc z hz) hxy hyz)
  intro a b c ha hb hc hab hbc
  exact main b hb a c ha hc hab hbc

/-- For a symmetric transitive base, only a base-pair/context-pair composition
needs a separate argument. Every endpoint remains inside the declared carrier. -/
theorem CT.transitiveOn_of_base_context {E : CRel sigma nu}
    (C : Term (sigma ⊕ sigma) nu → Prop)
    (hC : ∀ f args, C (.app f args) → ∀ a ∈ args, C a)
    (hsymm : ∀ a b, E a b → E b a)
    (htrans : ∀ a b c, E a b → E b c → E a c)
    (habsorb : ∀ a b c, C a → C b → C c →
      E a b → tildeAll (CT E) b c → CT E a c) :
    ∀ a b c, C a → C b → C c → CT E a b → CT E b c → CT E a c := by
  have hleft : ∀ a b c, C a → C b → C c → E a b → CT E b c → CT E a c := by
    intro a b c ha hb hc hab hbc
    rcases CT.unfold.mp hbc with hbase | hctx
    · exact CT.base (htrans a b c hab hbase)
    · exact habsorb a b c ha hb hc hab hctx
  apply CT.transitiveOn_of_base_absorption C hC hleft
  intro a b c ha hb hc hab hbc
  exact CT.symm hsymm (hleft c b a hc hb ha (hsymm b c hbc) (CT.symm hsymm hab))

/-- Exact carrier-relative criterion; no claim concerns contexts outside C. -/
theorem CT.transitiveOn_iff_base_context {E : CRel sigma nu}
    (C : Term (sigma ⊕ sigma) nu → Prop)
    (hC : ∀ f args, C (.app f args) → ∀ a ∈ args, C a)
    (hsymm : ∀ a b, E a b → E b a)
    (htrans : ∀ a b c, E a b → E b c → E a c) :
    (∀ a b c, C a → C b → C c → CT E a b → CT E b c → CT E a c) ↔
      (∀ a b c, C a → C b → C c → E a b →
        tildeAll (CT E) b c → CT E a c) := by
  constructor
  · intro h a b c ha hb hc hab hbc
    exact h a b c ha hb hc (CT.base hab) (CT.sigmaClosed b c hbc)
  · exact CT.transitiveOn_of_base_context C hC hsymm htrans

/-- The whole finite-term universe is one instance of the carrier criterion. -/
theorem CT.transitive_iff_base_context {E : CRel sigma nu}
    (hsymm : ∀ a b, E a b → E b a)
    (htrans : ∀ a b c, E a b → E b c → E a c) :
    (∀ a b c, CT E a b → CT E b c → CT E a c) ↔
      (∀ a b c, E a b → tildeAll (CT E) b c → CT E a c) := by
  constructor
  · intro h a b c hab hbc
    exact h a b c (CT.base hab) (CT.sigmaClosed b c hbc)
  · intro h a b c hab hbc
    exact CT.transitiveOn_of_base_context (fun _ => True)
      (fun _ _ _ _ _ => trivial) hsymm htrans
      (fun p q r _ _ _ hpq hqr => h p q r hpq hqr)
      a b c trivial trivial trivial hab hbc

/-! ## Constructor terms

A **constructor term** carries only constructor symbols. Variables count, since
frozen definition D9 makes a variable a nullary constructor. Every direct
subterm of a Constructor-TRS left-hand side is one, by frozen definition D5. -/

/-- Every symbol of the term is a constructor symbol. -/
inductive ConOnly : Term (sigma ⊕ sigma) nu → Prop
  | var (x : nu) : ConOnly (.var x)
  | app (c : sigma) (args : List (Term (sigma ⊕ sigma) nu)) :
      (∀ a ∈ args, ConOnly a) → ConOnly (.app (Sum.inl c) args)

/-- Inversion for a constructor term headed by an application. -/
theorem ConOnly.app_inv {f : sigma ⊕ sigma} {args : List (Term (sigma ⊕ sigma) nu)}
    (h : ConOnly (.app f args)) :
    ∃ c : sigma, f = Sum.inl c ∧ ∀ q ∈ args, ConOnly q := by
  cases h with
  | app c as has => exact ⟨c, rfl, has⟩

/-- The constructor labelling of any term is a constructor term. This is what
makes every pattern of a constructor translation eligible for Lemma 33. -/
theorem ConOnly.constructorLabel (t : Term sigma nu) :
    ConOnly (OperatorKO7.Meta.UniqueNormalization.constructorLabel t) := by
  induction t using Term.rec' with
  | hvar x => exact ConOnly.var x
  | happ f args ih =>
      refine ConOnly.app f _ ?_
      intro a ha
      rw [Term.mapSymList_eq_map] at ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      exact ih q hq

/-! ## Lemma 33, the matching invariant -/

/-- **Lemma 33.** If a constructor-compatible relation relates two instances of
one constructor term, it relates the two substitutions at every variable of that
term.

The induction is on the constructor term. At a variable the conclusion is the
hypothesis. At an application both instances are constructor-topped, so
constructor compatibility decomposes them and the induction hypothesis applies to
the argument carrying the occurrence. -/
theorem lemma33 {S : CRel sigma nu} (hS : ConstructorCompatible S)
    {a b : Subst (sigma ⊕ sigma) nu} :
    ∀ p : Term (sigma ⊕ sigma) nu, ConOnly p →
      S (Subst.apply a p) (Subst.apply b p) →
      ∀ x : nu, VarOccurs x p → S (a x) (b x) := by
  intro p
  induction p using Term.rec' with
  | hvar y =>
      intro _ h x hx
      cases hx with
      | here => simpa using h
  | happ f args ih =>
      intro hcon h x hx
      obtain ⟨c, rfl, hargs⟩ := hcon.app_inv
      simp only [Subst.apply_app, Subst.applyList_eq_map] at h
      rcases hS _ _ (ConTopped.app c _) (ConTopped.app c _) h with
        ⟨y, hy, -⟩ | ⟨c', xs, ys, hax, hby, hall⟩
      · exact absurd hy (by simp)
      · simp only [Term.app.injEq] at hax hby
        obtain ⟨-, hxs⟩ := hax
        obtain ⟨-, hys⟩ := hby
        subst hxs
        subst hys
        obtain ⟨q, hq, hxq⟩ := hx.app_inv
        exact ih q hq (hargs q hq) (pointwise_of_forall₂ hall q hq) x hxq

/-! ## Lemma 34, the substitution lift -/

/-- **Lemma 34.** A Sigma-closed relation lifts a pointwise relation between two
substitutions to their instances of any term.

No reflexivity is needed: a constant is handled by Sigma-closure applied to the
empty argument list. -/
theorem lemma34 {S : CRel sigma nu} (hS : SigmaClosed S)
    {a b : Subst (sigma ⊕ sigma) nu} :
    ∀ t : Term (sigma ⊕ sigma) nu, (∀ x : nu, VarOccurs x t → S (a x) (b x)) →
      S (Subst.apply a t) (Subst.apply b t) := by
  intro t
  induction t using Term.rec' with
  | hvar y => intro h; simpa using h y VarOccurs.here
  | happ f args ih =>
      intro h
      have hall : List.Forall₂ S (args.map (Subst.apply a)) (args.map (Subst.apply b)) :=
        forall₂_of_pointwise (fun q hq => ih q hq (fun x hx => h x (VarOccurs.arg hq hx)))
      refine hS _ _ ⟨f, args.map (Subst.apply a), args.map (Subst.apply b), trivial, ?_, ?_, hall⟩
      · simp [Subst.applyList_eq_map]
      · simp [Subst.applyList_eq_map]

/-! ## Corollary 35

The step the campaign audit reported as blocked. The block was a transcription
defect, recorded as amendment A3: the middle factor of Definition 30 is the
destructor tilde, so a semantical critical pair arrives with its two redexes
sharing a root symbol and with argumentwise related direct subterms. That
argumentwise relation is `hbar` below, and it is exactly what Lemma 33 consumes.

The right-hand side condition `hvar` is amendment A1: without it Theorem 68 is
false, as `FreshRhs.variable_condition_necessary` shows. -/

/-- **Corollary 35.** Two root contractions of one rule, taken around a
destructor tilde of a constructor-compatible relation, land inside `CT S`.

The rule is a Constructor-TRS rule: a destructor root `F` over direct subterms
`ps` that are constructor terms, with every right-hand side variable occurring on
the left. -/
theorem cor35 {S : CRel sigma nu} (hS : ConstructorCompatible S)
    {F : sigma} {ps : List (Term (sigma ⊕ sigma) nu)}
    (hps : ∀ p ∈ ps, ConOnly p)
    {r : Term (sigma ⊕ sigma) nu}
    (hvar : ∀ x : nu, VarOccurs x r → VarOccurs x (.app (Sum.inr F) ps))
    {a b : Subst (sigma ⊕ sigma) nu}
    (hbar : List.Forall₂ S (ps.map (Subst.apply a)) (ps.map (Subst.apply b))) :
    CT S (Subst.apply a r) (Subst.apply b r) := by
  refine lemma34 CT.sigmaClosed r ?_
  intro x hx
  obtain ⟨p, hp, hxp⟩ := (hvar x hx).app_inv
  exact CT.base (lemma33 hS p (hps p hp) (pointwise_of_forall₂ hbar p hp) x hxp)

/-- Corollary 35 in the shape Theorem 37 consumes: the hypothesis is a destructor
tilde of `S` between the two redexes, rather than an argumentwise relation
supplied by hand. -/
theorem cor35_of_barRel {S : CRel sigma nu} (hS : ConstructorCompatible S)
    {F : sigma} {ps : List (Term (sigma ⊕ sigma) nu)}
    (hps : ∀ p ∈ ps, ConOnly p)
    {r : Term (sigma ⊕ sigma) nu}
    (hvar : ∀ x : nu, VarOccurs x r → VarOccurs x (.app (Sum.inr F) ps))
    {a b : Subst (sigma ⊕ sigma) nu}
    (hbar : barRel S (Subst.apply a (.app (Sum.inr F) ps))
      (Subst.apply b (.app (Sum.inr F) ps))) :
    CT S (Subst.apply a r) (Subst.apply b r) := by
  obtain ⟨f, as, bs, -, hta, hub, hall⟩ := hbar
  simp only [Subst.apply_app, Subst.applyList_eq_map, Term.app.injEq] at hta hub
  obtain ⟨-, has⟩ := hta
  obtain ⟨-, hbs⟩ := hub
  subst has
  subst hbs
  exact cor35 hS hps hvar hall

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.tildeOn
#check @OperatorKO7.Meta.UniqueNormalization.hatRel
#check @OperatorKO7.Meta.UniqueNormalization.barRel
#check @OperatorKO7.Meta.UniqueNormalization.SigmaClosed
#check @OperatorKO7.Meta.UniqueNormalization.CT
#check @OperatorKO7.Meta.UniqueNormalization.ConOnly

#print axioms OperatorKO7.Meta.UniqueNormalization.CT.base
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.least
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.sigmaClosed
#print axioms OperatorKO7.Meta.UniqueNormalization.CT.app
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorCompatible_flip
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorCompatible_iSup
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma33
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma34
#print axioms OperatorKO7.Meta.UniqueNormalization.cor35
#print axioms OperatorKO7.Meta.UniqueNormalization.cor35_of_barRel
