import OperatorKO7.Meta.UniqueNormalization.Summit

/-!
# Term-coalgebras and the relativized invariant

Campaign: `Roadmaps\klop\ROADMAP.md`, wave 6. Source: Kahrs and Smith, FSCD 2016,
Definition 5 and Definition 40, transcribed in `Roadmaps\klop\definitions.md` at
D9 and D13.

## Fidelity block (frozen `definitions.md`, D9, Definition 5)

> "Given a signature Sigma, a term-coalgebra is a set A contained in
> Ter^infinity(Sigma, empty) which is closed under subterms. It is called finite
> if it is a finite set, and strongly finite if in addition A is contained in
> Ter(Sigma, empty)."

The campaign builds no infinitary carrier, so every coalgebra here is strongly
finite by construction: a `List` of finite terms, closed under subterms. Variables
are frozen as nullary constructors, per D9, which the `Subterm` relation already
respects.

## The relativized invariant

`DownOn A R` is Definition 40 read on the coalgebra `A`: every clause carries
membership of both endpoints, and the composition clauses carry membership of the
intermediate node. Section 7 of the source works entirely inside such an `A`,
because its completion argument needs the carrier to be finite.

`DownOn.toDown` is Lemma 41 in the form this development uses: a smaller carrier
gives a smaller relation, and the full term universe is the largest carrier.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Coalgebras -/

/-- A **term-coalgebra**: a list of terms closed under subterms. Finiteness is
carried by the list itself, which is what Proposition 55 of the source needs. -/
def Coalgebra (A : List (Term (sigma ⊕ sigma) nu)) : Prop :=
  ∀ t ∈ A, ∀ s : Term (sigma ⊕ sigma) nu, Subterm s t → s ∈ A

/-- Every argument of a member application is a member. -/
theorem Coalgebra.arg {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {f : sigma ⊕ sigma} {args : List (Term (sigma ⊕ sigma) nu)}
    (hmem : Term.app f args ∈ A) {a : Term (sigma ⊕ sigma) nu} (ha : a ∈ args) :
    a ∈ A :=
  hA _ hmem a (Subterm.arg ha (Subterm.refl _))

/-! ## Definition 40 on a coalgebra -/

/-- One unfolding of the operator whose least fixed point is the invariant on `A`.
Both endpoints and every intermediate node are members. -/
def DownStepOn (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (E : CRel sigma nu) : CRel sigma nu :=
  fun a b => a ∈ A ∧ b ∈ A ∧
    (a = b
    ∨ E b a
    ∨ (∃ c : Term (sigma ⊕ sigma) nu, c ∈ A ∧ rootStep R a c ∧ E c b)
    ∨ (∃ (d : sigma) (as cs : List (Term (sigma ⊕ sigma) nu)),
        a = .app (Sum.inr d) as ∧ List.Forall₂ E as cs ∧
        Term.app (Sum.inr d) cs ∈ A ∧ E (.app (Sum.inr d) cs) b)
    ∨ hatRel E a b
    ∨ barRel E a b)

/-- The operator is monotone. -/
theorem DownStepOn_mono {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {E E' : CRel sigma nu} (h : ∀ a b, E a b → E' a b)
    {p q : Term (sigma ⊕ sigma) nu} (hpq : DownStepOn A R E p q) :
    DownStepOn A R E' p q := by
  obtain ⟨hp, hq, hbody⟩ := hpq
  refine ⟨hp, hq, ?_⟩
  rcases hbody with heq | hinv | ⟨c, hc, hr, hcb⟩ | ⟨d, as, cs, ha, hall, hmem, hcb⟩ | hhat | hbar
  · exact Or.inl heq
  · exact Or.inr (Or.inl (h _ _ hinv))
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hr, h _ _ hcb⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨d, as, cs, ha, forall₂_mono h hall, hmem, h _ _ hcb⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (tildeOn_mono h hhat)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (tildeOn_mono h hbar)))))

/-- **Definition 40 on a coalgebra.** -/
def DownOn (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu) :
    CRel sigma nu :=
  fun a b => ∀ E : CRel sigma nu, (∀ p q, DownStepOn A R E p q → E p q) → E a b

theorem DownOn.least {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {E : CRel sigma nu} (hE : ∀ p q, DownStepOn A R E p q → E p q)
    {a b : Term (sigma ⊕ sigma) nu} (h : DownOn A R a b) : E a b :=
  h E hE

theorem DownOn.closed {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (p q : Term (sigma ⊕ sigma) nu) (h : DownStepOn A R (DownOn A R) p q) :
    DownOn A R p q := by
  intro E hE
  exact hE p q (DownStepOn_mono (fun x y hxy => hxy E hE) h)

/-- Induction over the relativized invariant. -/
theorem DownOn.induction {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {P : CRel sigma nu}
    (hstep : ∀ p q, DownStepOn A R (fun x y => DownOn A R x y ∧ P x y) p q → P p q)
    {a b : Term (sigma ⊕ sigma) nu} (h : DownOn A R a b) : P a b := by
  have hclosed : ∀ p q, DownStepOn A R (fun x y => DownOn A R x y ∧ P x y) p q →
      (DownOn A R p q ∧ P p q) := by
    intro p q hpq
    exact ⟨DownOn.closed p q (DownStepOn_mono (fun x y hxy => hxy.1) hpq), hstep p q hpq⟩
  exact (DownOn.least hclosed h).2

/-! ### Membership and the introduction rules -/

/-- Both endpoints of the relativized invariant are members. -/
theorem DownOn.mem {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} (h : DownOn A R a b) : a ∈ A ∧ b ∈ A := by
  refine DownOn.induction (P := fun p q => p ∈ A ∧ q ∈ A) ?_ h
  intro p q hpq
  exact ⟨hpq.1, hpq.2.1⟩

theorem DownOn.refl {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) : DownOn A R a a :=
  DownOn.closed a a ⟨ha, ha, Or.inl rfl⟩

theorem DownOn.symm {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} (h : DownOn A R a b) : DownOn A R b a :=
  DownOn.closed b a ⟨h.mem.2, h.mem.1, Or.inr (Or.inl h)⟩

theorem DownOn.rootComp {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a c b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hc : c ∈ A)
    (h₁ : rootStep R a c) (h₂ : DownOn A R c b) : DownOn A R a b :=
  DownOn.closed a b ⟨ha, h₂.mem.2, Or.inr (Or.inr (Or.inl ⟨c, hc, h₁, h₂⟩))⟩

theorem DownOn.barComp {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {d : sigma} {as cs : List (Term (sigma ⊕ sigma) nu)} {b : Term (sigma ⊕ sigma) nu}
    (ha : Term.app (Sum.inr d) as ∈ A)
    (h₁ : List.Forall₂ (DownOn A R) as cs) (h₂ : DownOn A R (.app (Sum.inr d) cs) b) :
    DownOn A R (.app (Sum.inr d) as) b :=
  DownOn.closed _ b ⟨ha, h₂.mem.2,
    Or.inr (Or.inr (Or.inr (Or.inl ⟨d, as, cs, rfl, h₁, h₂.mem.1, h₂⟩)))⟩

theorem DownOn.hatCl {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {c : sigma} {as bs : List (Term (sigma ⊕ sigma) nu)}
    (ha : Term.app (Sum.inl c) as ∈ A) (hb : Term.app (Sum.inl c) bs ∈ A)
    (h : List.Forall₂ (DownOn A R) as bs) :
    DownOn A R (.app (Sum.inl c) as) (.app (Sum.inl c) bs) :=
  DownOn.closed _ _ ⟨ha, hb, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨.inl c, as, bs, ⟨c, rfl⟩, rfl, rfl, h⟩))))⟩

theorem DownOn.barCl {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {d : sigma} {as bs : List (Term (sigma ⊕ sigma) nu)}
    (ha : Term.app (Sum.inr d) as ∈ A) (hb : Term.app (Sum.inr d) bs ∈ A)
    (h : List.Forall₂ (DownOn A R) as bs) :
    DownOn A R (.app (Sum.inr d) as) (.app (Sum.inr d) bs) :=
  DownOn.closed _ _ ⟨ha, hb, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨.inr d, as, bs, ⟨d, rfl⟩, rfl, rfl, h⟩))))⟩

/-- Either tilde, chosen by the root symbol. -/
theorem DownOn.tildeCl {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {f : sigma ⊕ sigma} {as bs : List (Term (sigma ⊕ sigma) nu)}
    (ha : Term.app f as ∈ A) (hb : Term.app f bs ∈ A)
    (h : List.Forall₂ (DownOn A R) as bs) :
    DownOn A R (.app f as) (.app f bs) := by
  cases f with
  | inl c => exact DownOn.hatCl ha hb h
  | inr d => exact DownOn.barCl ha hb h

/-! ## Lemma 41, in the form this development uses -/

/-- **Lemma 41.** The invariant on a coalgebra is part of the invariant on the
whole term universe. Every clause of the relativized operator is a clause of the
unrelativized one with its membership side conditions discarded. -/
theorem DownOn.toDown {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} (h : DownOn A R a b) : Down R a b := by
  refine DownOn.induction (P := fun p q => Down R p q) ?_ h
  intro p q hpq
  obtain ⟨-, -, hbody⟩ := hpq
  rcases hbody with rfl | hinv | ⟨c, -, hr, hcb⟩ | ⟨d, as, cs, rfl, hall, -, hcb⟩ | hhat | hbar
  · exact Down.refl p
  · exact Down.symm hinv.2
  · exact Down.rootComp hr hcb.2
  · exact Down.barComp (forall₂_mono (fun _ _ hx => hx.2) hall) hcb.2
  · obtain ⟨f, as, bs, -, rfl, rfl, hall⟩ := hhat
    exact Down.tildeCl (forall₂_mono (fun _ _ hx => hx.2) hall)
  · obtain ⟨f, as, bs, -, rfl, rfl, hall⟩ := hbar
    exact Down.tildeCl (forall₂_mono (fun _ _ hx => hx.2) hall)

/-! ## Rewrite steps inside a coalgebra -/

/-- Reflexivity on the members of one list. -/
theorem forall₂_self_of {alpha : Type u} {r : alpha → alpha → Prop} :
    ∀ {l : List alpha}, (∀ a ∈ l, r a a) → List.Forall₂ r l l := by
  intro l
  induction l with
  | nil => intro _; exact List.Forall₂.nil
  | cons a as ih =>
      intro h
      exact List.Forall₂.cons (h a (List.mem_cons_self ..))
        (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- A one-position replacement, with reflexivity assumed only on the members of
the two surrounding segments. -/
theorem forall₂_append_middle_of {alpha : Type u} {r : alpha → alpha → Prop} :
    ∀ (pre post : List alpha) {a b : alpha},
      (∀ x ∈ pre, r x x) → (∀ x ∈ post, r x x) → r a b →
      List.Forall₂ r (pre ++ a :: post) (pre ++ b :: post) := by
  intro pre
  induction pre with
  | nil =>
      intro post _ _ _ hpost hab
      exact List.Forall₂.cons hab (forall₂_self_of hpost)
  | cons p ps ih =>
      intro post _ _ hpre hpost hab
      exact List.Forall₂.cons (hpre p (List.mem_cons_self ..))
        (ih post (fun x hx => hpre x (List.mem_cons_of_mem _ hx)) hpost hab)

/-- A rewrite step between two members of a coalgebra is part of the relativized
invariant. Subterm closure supplies the membership of every intermediate node. -/
theorem DownOn.of_step {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} :
    ∀ {a b : Term (sigma ⊕ sigma) nu}, Step R a b → a ∈ A → b ∈ A → DownOn A R a b := by
  intro a b h
  induction h with
  | @root s t hr =>
      intro hs ht
      exact DownOn.rootComp hs ht hr (DownOn.refl ht)
  | @arg f pre post x y _ ih =>
      intro hs ht
      have hrefl : ∀ z ∈ pre ++ x :: post, DownOn A R z z := fun z hz =>
        DownOn.refl (hA _ hs z (Subterm.arg hz (Subterm.refl _)))
      refine DownOn.tildeCl hs ht (forall₂_append_middle_of pre post ?_ ?_ ?_)
      · exact fun z hz => hrefl z (List.mem_append_left _ hz)
      · exact fun z hz => hrefl z (List.mem_append_right _ (List.mem_cons_of_mem _ hz))
      · exact ih (hA _ hs x (Subterm.arg (List.mem_append_right _ (List.mem_cons_self ..))
            (Subterm.refl _)))
          (hA _ ht y (Subterm.arg (List.mem_append_right _ (List.mem_cons_self ..))
            (Subterm.refl _)))

/-! ## Building a coalgebra

Theorem 66 of the source closes a finite conversion sequence under subterms. The
construction below is that closure, and it is where the finiteness Section 7 needs
comes from. -/

/-- Inversion for a subterm of an application. -/
theorem Subterm.app_inv {s : Term sigma nu} {f : sigma} {args : List (Term sigma nu)}
    (h : Subterm s (.app f args)) :
    s = .app f args ∨ ∃ a ∈ args, Subterm s a := by
  cases h with
  | refl => exact Or.inl rfl
  | arg hmem hsa => exact Or.inr ⟨_, hmem, hsa⟩

/-- Subterm transitivity. -/
theorem Subterm.trans {s t u : Term sigma nu} (h₁ : Subterm s t) (h₂ : Subterm t u) :
    Subterm s u := by
  induction h₂ with
  | refl => exact h₁
  | @arg f args a hmem _ ih => exact Subterm.arg hmem ih

mutual
/-- Every subterm of a term, the term itself included. -/
def subterms : Term sigma nu → List (Term sigma nu)
  | .var x => [.var x]
  | .app f args => .app f args :: subtermsList args
/-- Every subterm of every member of an argument list. -/
def subtermsList : List (Term sigma nu) → List (Term sigma nu)
  | [] => []
  | a :: as => subterms a ++ subtermsList as
end

@[simp] theorem subterms_var (x : nu) :
    subterms (sigma := sigma) (.var x) = [.var x] := rfl

@[simp] theorem subterms_app (f : sigma) (args : List (Term sigma nu)) :
    subterms (.app f args) = .app f args :: subtermsList args := rfl

@[simp] theorem subtermsList_nil :
    subtermsList ([] : List (Term sigma nu)) = [] := rfl

@[simp] theorem subtermsList_cons (a : Term sigma nu) (as : List (Term sigma nu)) :
    subtermsList (a :: as) = subterms a ++ subtermsList as := rfl

/-- Membership in the argument-list closure. -/
theorem mem_subtermsList {s : Term sigma nu} :
    ∀ {args : List (Term sigma nu)},
      s ∈ subtermsList args ↔ ∃ a ∈ args, s ∈ subterms a := by
  intro args
  induction args with
  | nil => simp
  | cons a as ih =>
      constructor
      · intro h
        rcases List.mem_append.mp h with h' | h'
        · exact ⟨a, List.mem_cons_self .., h'⟩
        · obtain ⟨b, hb, hs⟩ := ih.mp h'
          exact ⟨b, List.mem_cons_of_mem _ hb, hs⟩
      · rintro ⟨b, hb, hs⟩
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact List.mem_append_left _ hs
        · exact List.mem_append_right _ (ih.mpr ⟨b, hb', hs⟩)

/-- The list of subterms is exactly the subterm relation. -/
theorem mem_subterms_iff {s : Term sigma nu} :
    ∀ t : Term sigma nu, s ∈ subterms t ↔ Subterm s t := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
      constructor
      · intro h
        have hsx : s = Term.var x := by simpa using h
        subst hsx
        exact Subterm.refl _
      · intro h
        have hsx : s = Term.var x := Subterm.eq_of_var h
        subst hsx
        simp
  | happ f args ih =>
      constructor
      · intro h
        rcases List.mem_cons.mp (by simpa using h) with rfl | h'
        · exact Subterm.refl _
        · obtain ⟨a, ha, hs⟩ := mem_subtermsList.mp h'
          exact Subterm.arg ha ((ih a ha).mp hs)
      · intro h
        rcases h.app_inv with rfl | ⟨a, hmem, hsa⟩
        · simp
        · exact List.mem_cons_of_mem _
            (mem_subtermsList.mpr ⟨a, hmem, (ih a hmem).mpr hsa⟩)

/-- The subterm closure of a list of terms. -/
def coalgebraOf (l : List (Term (sigma ⊕ sigma) nu)) : List (Term (sigma ⊕ sigma) nu) :=
  l.flatMap subterms

/-- Every member of the list is in its closure. -/
theorem mem_coalgebraOf {l : List (Term (sigma ⊕ sigma) nu)}
    {t : Term (sigma ⊕ sigma) nu} (h : t ∈ l) : t ∈ coalgebraOf l :=
  List.mem_flatMap.mpr ⟨t, h, (mem_subterms_iff t).mpr (Subterm.refl t)⟩

/-- The closure is a coalgebra. -/
theorem coalgebra_coalgebraOf (l : List (Term (sigma ⊕ sigma) nu)) :
    Coalgebra (coalgebraOf l) := by
  intro t ht s hs
  obtain ⟨u, hu, htu⟩ := List.mem_flatMap.mp ht
  exact List.mem_flatMap.mpr ⟨u, hu, (mem_subterms_iff u).mpr
    (hs.trans ((mem_subterms_iff u).mp htu))⟩


/-! ## Finite supports for global Down proofs -/

theorem Coalgebra.nil : Coalgebra ([] : List (Term (sigma ⊕ sigma) nu)) := by
  intro _ h
  exact (List.not_mem_nil h).elim

theorem Coalgebra.append {A B : List (Term (sigma ⊕ sigma) nu)}
    (hA : Coalgebra A) (hB : Coalgebra B) : Coalgebra (A ++ B) := by
  intro t ht s hs
  rcases List.mem_append.mp ht with ht | ht
  · exact List.mem_append_left _ (hA t ht s hs)
  · exact List.mem_append_right _ (hB t ht s hs)

/-- Enlarging a carrier preserves each actual DownOn derivation. -/
theorem DownOn.mono {A B : List (Term (sigma ⊕ sigma) nu)}
    (hAB : ∀ t, t ∈ A → t ∈ B) {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} (h : DownOn A R a b) : DownOn B R a b := by
  refine DownOn.induction (P := fun p q => DownOn B R p q) ?_ h
  intro p q hpq
  obtain ⟨hp, hq, hbody⟩ := hpq
  rcases hbody with heq | hinv | ⟨c, hc, hpc, hcb⟩ |
      ⟨d, xs, ys, hpShape, hargs, _, hmb⟩ | hhat | hbar
  · subst q
    exact DownOn.refl (hAB p hp)
  · exact DownOn.symm hinv.2
  · exact DownOn.rootComp (hAB p hp) (hAB c hc) hpc hcb.2
  · subst p
    exact DownOn.barComp (hAB _ hp)
      (forall₂_mono (fun _ _ h => h.2) hargs) hmb.2
  · rcases hhat with ⟨f, xs, ys, _, rfl, rfl, hargs⟩
    exact DownOn.tildeCl (hAB _ hp) (hAB _ hq)
      (forall₂_mono (fun _ _ h => h.2) hargs)
  · rcases hbar with ⟨f, xs, ys, _, rfl, rfl, hargs⟩
    exact DownOn.tildeCl (hAB _ hp) (hAB _ hq)
      (forall₂_mono (fun _ _ h => h.2) hargs)

theorem DownOn.append_left {A : List (Term (sigma ⊕ sigma) nu)}
    (B : List (Term (sigma ⊕ sigma) nu)) {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} (h : DownOn A R a b) :
    DownOn (A ++ B) R a b :=
  h.mono (fun _ hm => List.mem_append_left _ hm)

theorem DownOn.append_right (A : List (Term (sigma ⊕ sigma) nu))
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} (h : DownOn B R a b) :
    DownOn (A ++ B) R a b :=
  h.mono (fun _ hm => List.mem_append_right _ hm)

/-- Finitely many argument proofs have one finite subterm-closed support. -/
theorem forall₂_downOn_exists {R : TRS (sigma ⊕ sigma) nu}
    {xs ys : List (Term (sigma ⊕ sigma) nu)}
    (h : List.Forall₂ (fun a b => ∃ A, Coalgebra A ∧ DownOn A R a b) xs ys) :
    ∃ A, Coalgebra A ∧ List.Forall₂ (DownOn A R) xs ys := by
  induction h with
  | nil => exact ⟨[], Coalgebra.nil, List.Forall₂.nil⟩
  | cons hab _ ih =>
      obtain ⟨A, hA, hab⟩ := hab
      obtain ⟨B, hB, hrest⟩ := ih
      exact ⟨A ++ B, hA.append hB, List.Forall₂.cons (hab.append_left B)
        (forall₂_mono (fun _ _ h => h.append_right A) hrest)⟩

/-- Every global Down proof occurs on a finite subterm-closed carrier.
No constructor, overlap, equality-decision, or termination assumption is used. -/
theorem Down.exists_finite_coalgebra {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} (h : Down R a b) :
    ∃ A, Coalgebra A ∧ DownOn A R a b := by
  refine Down.induction (P := fun p q => ∃ A, Coalgebra A ∧ DownOn A R p q) ?_ h
  intro p q hpq
  rcases hpq with heq | hinv | ⟨c, hpc, hcb⟩ |
      ⟨d, xs, ys, hpShape, hargs, hmb⟩ | hhat | hbar
  · subst q
    exact ⟨coalgebraOf [p], coalgebra_coalgebraOf [p],
      DownOn.refl (mem_coalgebraOf (List.mem_cons_self ..))⟩
  · obtain ⟨A, hA, hqp⟩ := hinv.2
    exact ⟨A, hA, DownOn.symm hqp⟩
  · obtain ⟨A, _, hcq⟩ := hcb.2
    let B := coalgebraOf (p :: A)
    have hAB : ∀ t, t ∈ A → t ∈ B :=
      fun _ ht => mem_coalgebraOf (List.mem_cons_of_mem p ht)
    have htail : DownOn B R c q := hcq.mono hAB
    exact ⟨B, coalgebra_coalgebraOf _, DownOn.rootComp
      (mem_coalgebraOf (List.mem_cons_self ..)) htail.mem.1 hpc htail⟩
  · subst p
    obtain ⟨A, _, hargsA⟩ :=
      forall₂_downOn_exists (forall₂_mono (fun _ _ h => h.2) hargs)
    obtain ⟨B, _, htailB⟩ := hmb.2
    let C := coalgebraOf (Term.app (.inr d) xs :: (A ++ B))
    have hAC : ∀ t, t ∈ A → t ∈ C :=
      fun _ ht => mem_coalgebraOf (List.mem_cons_of_mem _ (List.mem_append_left _ ht))
    have hBC : ∀ t, t ∈ B → t ∈ C :=
      fun _ ht => mem_coalgebraOf (List.mem_cons_of_mem _ (List.mem_append_right _ ht))
    exact ⟨C, coalgebra_coalgebraOf _, DownOn.barComp
      (mem_coalgebraOf (List.mem_cons_self ..))
      (forall₂_mono (fun _ _ h => h.mono hAC) hargsA) (htailB.mono hBC)⟩
  · rcases hhat with ⟨f, xs, ys, _, rfl, rfl, hargs⟩
    obtain ⟨A, _, hargsA⟩ :=
      forall₂_downOn_exists (forall₂_mono (fun _ _ h => h.2) hargs)
    let B := coalgebraOf (Term.app f xs :: Term.app f ys :: A)
    have hAB : ∀ t, t ∈ A → t ∈ B :=
      fun _ ht => mem_coalgebraOf (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht))
    exact ⟨B, coalgebra_coalgebraOf _, DownOn.tildeCl
      (mem_coalgebraOf (List.mem_cons_self ..))
      (mem_coalgebraOf (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (forall₂_mono (fun _ _ h => h.mono hAB) hargsA)⟩
  · rcases hbar with ⟨f, xs, ys, _, rfl, rfl, hargs⟩
    obtain ⟨A, _, hargsA⟩ :=
      forall₂_downOn_exists (forall₂_mono (fun _ _ h => h.2) hargs)
    let B := coalgebraOf (Term.app f xs :: Term.app f ys :: A)
    have hAB : ∀ t, t ∈ A → t ∈ B :=
      fun _ ht => mem_coalgebraOf (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht))
    exact ⟨B, coalgebra_coalgebraOf _, DownOn.tildeCl
      (mem_coalgebraOf (List.mem_cons_self ..))
      (mem_coalgebraOf (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (forall₂_mono (fun _ _ h => h.mono hAB) hargsA)⟩

theorem Down.iff_exists_finite_coalgebra {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} :
    Down R a b ↔ ∃ A, Coalgebra A ∧ DownOn A R a b :=
  ⟨Down.exists_finite_coalgebra, fun ⟨_, _, h⟩ => h.toDown⟩

/-- Two composable global proofs have one common finite support. -/
theorem Down.pair_exists_finite_coalgebra {R : TRS (sigma ⊕ sigma) nu}
    {a b c : Term (sigma ⊕ sigma) nu} (hab : Down R a b) (hbc : Down R b c) :
    ∃ A, Coalgebra A ∧ DownOn A R a b ∧ DownOn A R b c := by
  obtain ⟨A, hA, hab⟩ := hab.exists_finite_coalgebra
  obtain ⟨B, hB, hbc⟩ := hbc.exists_finite_coalgebra
  exact ⟨A ++ B, hA.append hB, hab.append_left B, hbc.append_right A⟩

/-- Transitivity on each finite coalgebra suffices for global transitivity. -/
theorem Down.trans_of_finite_coalgebras {R : TRS (sigma ⊕ sigma) nu}
    (hlocal : ∀ A, Coalgebra A → ∀ a b c,
      DownOn A R a b → DownOn A R b c → DownOn A R a c) :
    ∀ a b c, Down R a b → Down R b c → Down R a c := by
  intro a b c hab hbc
  obtain ⟨A, hA, habA, hbcA⟩ := Down.pair_exists_finite_coalgebra hab hbc
  exact (hlocal A hA a b c habA hbcA).toDown


end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.Coalgebra
#check @OperatorKO7.Meta.UniqueNormalization.DownOn

#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.closed
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.induction
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.mem
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.toDown
#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.of_step
