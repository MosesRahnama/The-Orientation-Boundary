import OperatorKO7.Meta.UniqueNormalization.Coalgebra

/-!
# Forests, and the relativized invariant's constructor compatibility

Campaign: `Roadmaps\klop\ROADMAP.md`, wave 6. Source: Kahrs and Smith, FSCD 2016,
Section 7, transcribed in `Roadmaps\klop\definitions.md` at D14.

## Why a parent function

Conditions 2 and 3 of Definition 46 say that a proof graph is deterministic and
terminating, and the explanation calls the result "a forest of trees (a union/find
structure)". A deterministic relation is a partial function, so this development
carries the graph as `par : Term -> Option Term` and gets determinism by
construction. Termination is the well-foundedness of the parent step.

`Reach` is the chain of parents, and `EqvOn` is the valley form: two nodes are
related when their chains meet. Under determinism and termination that is the
equivalence closure of the edges, and having the valley built into the definition
is what makes Lemma 52 an induction on chain length.

## What this module proves

The forest facts every later argument uses: chains from one node are comparable,
`EqvOn` is an equivalence containing the edges, and well-foundedness survives the
one edge Corollary 53 adds. Plus Proposition 44 for the relativized invariant.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## The constructor tilde with frozen variables

Frozen definition D9 makes a variable a nullary constructor, so the constructor
tilde relates two occurrences of one variable. `hatEq` is that relation, and it is
exactly the conclusion shape of `ConstructorCompatible`. -/

/-- The constructor tilde, with variables frozen as nullary constructors. -/
def hatEq (E : CRel sigma nu) : CRel sigma nu :=
  fun a b => (∃ x : nu, a = .var x ∧ b = .var x) ∨ hatRel E a b

theorem hatEq.mono {E E' : CRel sigma nu} (h : ∀ a b, E a b → E' a b)
    {a b : Term (sigma ⊕ sigma) nu} (hab : hatEq E a b) : hatEq E' a b := by
  rcases hab with hvar | hhat
  · exact Or.inl hvar
  · exact Or.inr (tildeOn_mono h hhat)

/-- A frozen-variable constructor tilde has a constructor-topped source. -/
theorem ConTopped.of_hatEq {E : CRel sigma nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : hatEq E a b) : ConTopped a := by
  rcases h with ⟨x, rfl, -⟩ | ⟨f, as, bs, ⟨c, rfl⟩, rfl, -, -⟩
  · exact ConTopped.var x
  · exact ConTopped.app c as

/-! ## Proposition 44 for the relativized invariant -/

/-- **Proposition 44 on a coalgebra.** The relativized invariant is
constructor-compatible. The proof is the unrelativized one with membership
bookkeeping: reflexivity of the arguments needs them to be members, which subterm
closure supplies. -/
theorem DownOn.constructorCompatible {A : List (Term (sigma ⊕ sigma) nu)}
    (hA : Coalgebra A) {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R) :
    ConstructorCompatible (DownOn A R) := by
  intro a b hca hcb hab
  revert hca hcb
  refine DownOn.induction (P := fun p q => ConTopped p → ConTopped q →
    (∃ x : nu, p = .var x ∧ q = .var x) ∨
    (∃ (f : sigma) (xs ys : List (Term (sigma ⊕ sigma) nu)),
      p = .app (.inl f) xs ∧ q = .app (.inl f) ys ∧
        List.Forall₂ (DownOn A R) xs ys)) ?_ hab
  intro p q hpq
  obtain ⟨hpA, hqA, hbody⟩ := hpq
  rcases hbody with heq | hinv | ⟨c, -, hroot, -⟩ | ⟨d, as, cs, hpd, -, -, -⟩ | hhat | hbar
  · subst heq
    intro hcp _
    rcases hcp with ⟨x, rfl⟩ | ⟨f, args, rfl⟩
    · exact Or.inl ⟨x, rfl, rfl⟩
    · refine Or.inr ⟨f, args, args, rfl, rfl, forall₂_self_of ?_⟩
      intro z hz
      exact DownOn.refl (Coalgebra.arg hA hpA hz)
  · intro hcp hcq
    rcases hinv.2 hcq hcp with ⟨x, hq, hp⟩ | ⟨f, xs, ys, hq, hp, hall⟩
    · exact Or.inl ⟨x, hp, hq⟩
    · exact Or.inr ⟨f, ys, xs, hp, hq, forall₂_swap (fun _ _ hx => DownOn.symm hx) hall⟩
  · intro hcp _
    obtain ⟨d, args, rfl⟩ := rootStep_source_destructor hR hroot
    exact absurd hcp (not_conTopped_destructor args)
  · intro hcp _
    subst hpd
    exact absurd hcp (not_conTopped_destructor as)
  · obtain ⟨f, as, bs, ⟨c, rfl⟩, rfl, rfl, hall⟩ := hhat
    intro _ _
    exact Or.inr ⟨c, as, bs, rfl, rfl, forall₂_mono (fun _ _ hx => hx.1) hall⟩
  · obtain ⟨f, as, bs, ⟨d, rfl⟩, rfl, rfl, -⟩ := hbar
    intro hcp _
    exact absurd hcp (not_conTopped_destructor as)

/-- The constructor-compatibility conclusion, packaged as `hatEq`. -/
theorem DownOn.hatEq_of_conTopped {A : List (Term (sigma ⊕ sigma) nu)}
    (hA : Coalgebra A) {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {a b : Term (sigma ⊕ sigma) nu} (hca : ConTopped a) (hcb : ConTopped b)
    (h : DownOn A R a b) : hatEq (DownOn A R) a b := by
  rcases DownOn.constructorCompatible hA hR a b hca hcb h with hvar | ⟨f, xs, ys, ha, hb, hall⟩
  · exact Or.inl hvar
  · exact Or.inr ⟨.inl f, xs, ys, ⟨f, rfl⟩, ha, hb, hall⟩

/-! ## Parent chains -/

/-- One parent step. -/
def Up (g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)) :
    CRel sigma nu :=
  fun a b => g a = some b

/-- The chain of parents, reflexive and transitive, built head first so that
induction peels the first edge. -/
inductive Reach (g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)) :
    Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu → Prop
  | refl (a : Term (sigma ⊕ sigma) nu) : Reach g a a
  | head {a b c : Term (sigma ⊕ sigma) nu} :
      g a = some b → Reach g b c → Reach g a c

/-- Termination of the parent step. -/
def Terminating (g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)) : Prop :=
  WellFounded (fun b a => g a = some b)

theorem Reach.trans {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a b c : Term (sigma ⊕ sigma) nu} (h₁ : Reach g a b) (h₂ : Reach g b c) :
    Reach g a c := by
  induction h₁ with
  | refl => exact h₂
  | head hedge _ ih => exact Reach.head hedge (ih h₂)

/-- Inversion for a parent chain. -/
theorem Reach.head_inv {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a t : Term (sigma ⊕ sigma) nu} (h : Reach g a t) :
    a = t ∨ ∃ b, g a = some b ∧ Reach g b t := by
  cases h with
  | refl => exact Or.inl rfl
  | head he ht => exact Or.inr ⟨_, he, ht⟩

/-- Two chains out of one node are comparable, because the parent step is a
function. -/
theorem Reach.comparable {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)} :
    ∀ {a s : Term (sigma ⊕ sigma) nu}, Reach g a s →
      ∀ {t : Term (sigma ⊕ sigma) nu}, Reach g a t →
      Reach g s t ∨ Reach g t s := by
  intro a s h₁
  induction h₁ with
  | refl a => intro t h₂; exact Or.inl h₂
  | @head a b s hedge htail ih =>
      intro t h₂
      rcases h₂.head_inv with rfl | ⟨b', hedge', htail'⟩
      · exact Or.inr (Reach.head hedge htail)
      · have hbb : b = b' := Option.some.inj (hedge.symm.trans hedge')
        subst hbb
        exact ih htail'

/-! ## The equivalence a forest represents -/

/-- Two members whose parent chains meet. Under determinism and termination this
is the equivalence closure of the edges, in valley form. -/
def EqvOn (A : List (Term (sigma ⊕ sigma) nu))
    (g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)) : CRel sigma nu :=
  fun a b => a ∈ A ∧ b ∈ A ∧ ∃ s, Reach g a s ∧ Reach g b s

theorem EqvOn.mem {A : List (Term (sigma ⊕ sigma) nu)}
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a b : Term (sigma ⊕ sigma) nu} (h : EqvOn A g a b) : a ∈ A ∧ b ∈ A :=
  ⟨h.1, h.2.1⟩

theorem EqvOn.refl {A : List (Term (sigma ⊕ sigma) nu)}
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) : EqvOn A g a a :=
  ⟨ha, ha, a, Reach.refl a, Reach.refl a⟩

theorem EqvOn.symm {A : List (Term (sigma ⊕ sigma) nu)}
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a b : Term (sigma ⊕ sigma) nu} (h : EqvOn A g a b) : EqvOn A g b a := by
  obtain ⟨ha, hb, s, has, hbs⟩ := h
  exact ⟨hb, ha, s, hbs, has⟩

theorem EqvOn.trans {A : List (Term (sigma ⊕ sigma) nu)}
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a b c : Term (sigma ⊕ sigma) nu} (h₁ : EqvOn A g a b) (h₂ : EqvOn A g b c) :
    EqvOn A g a c := by
  obtain ⟨ha, -, s, has, hbs⟩ := h₁
  obtain ⟨-, hc, t, hbt, hct⟩ := h₂
  rcases hbs.comparable hbt with hst | hts
  · exact ⟨ha, hc, t, has.trans hst, hct⟩
  · exact ⟨ha, hc, s, has, hct.trans hts⟩

/-- A parent chain inside the coalgebra is an `EqvOn` pair. -/
theorem EqvOn.of_reach {A : List (Term (sigma ⊕ sigma) nu)}
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A) (h : Reach g a b) :
    EqvOn A g a b :=
  ⟨ha, hb, b, h, Reach.refl b⟩

/-! ## Adding one edge -/

open scoped Classical in
/-- The forest with one edge added at `a`. -/
noncomputable def extendPar
    (g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    (a b : Term (sigma ⊕ sigma) nu) :
    Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu) :=
  fun x => if x = a then some b else g x

open scoped Classical in
@[simp] theorem extendPar_self
    (g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    (a b : Term (sigma ⊕ sigma) nu) : extendPar g a b a = some b := by
  simp [extendPar]

open scoped Classical in
theorem extendPar_of_ne
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a b x : Term (sigma ⊕ sigma) nu} (h : x ≠ a) : extendPar g a b x = g x := by
  simp [extendPar, h]

/-- Edges of the extension are old edges or the new one. -/
theorem extendPar_edge
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a b x y : Term (sigma ⊕ sigma) nu} (h : extendPar g a b x = some y) :
    (x = a ∧ y = b) ∨ g x = some y := by
  by_cases hx : x = a
  · subst hx
    rw [extendPar_self] at h
    exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  · rw [extendPar_of_ne hx] at h
    exact Or.inr h

/-- Old chains survive as long as they avoid the new source. -/
theorem Reach.extend_of_not_reach
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a b : Term (sigma ⊕ sigma) nu} {x y : Term (sigma ⊕ sigma) nu}
    (h : Reach g x y) : Reach (extendPar g a b) x y ∨ Reach g x a := by
  induction h with
  | refl x => exact Or.inl (Reach.refl x)
  | @head p q r hedge _ ih =>
      by_cases hp : p = a
      · exact Or.inr (by rw [hp]; exact Reach.refl a)
      · rcases ih with hnew | hold
        · exact Or.inl (Reach.head (by rw [extendPar_of_ne hp]; exact hedge) hnew)
        · exact Or.inr (Reach.head hedge hold)

/-- Replacing one parent preserves termination when its new target cannot return
to its source along the old parent relation. -/
theorem terminating_extendPar_of_no_return
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hwf : Terminating g) {a b : Term (sigma ⊕ sigma) nu}
    (hnr : ¬ Reach g b a) : Terminating (extendPar g a b) := by
  classical
  set g' := extendPar g a b with hg'
  -- every node that does not reach `a` keeps its old chain, hence is accessible
  have key : ∀ z : Term (sigma ⊕ sigma) nu, ¬ Reach g z a →
      Acc (fun y x => g' x = some y) z := by
    intro z
    induction z using hwf.induction with
    | _ z ih =>
        intro hz
        refine Acc.intro z ?_
        intro y hy
        rcases extendPar_edge hy with ⟨rfl, -⟩ | hold
        · exact absurd (Reach.refl z) hz
        · refine ih y hold ?_
          intro hya
          exact hz (Reach.head hold hya)
  have hb : Acc (fun y x => g' x = some y) b := key b hnr
  have hacc : ∀ z : Term (sigma ⊕ sigma) nu, Acc (fun y x => g' x = some y) z := by
    intro z
    induction z using hwf.induction with
    | _ z ih =>
        refine Acc.intro z ?_
        intro y hy
        rcases extendPar_edge hy with ⟨rfl, rfl⟩ | hold
        · exact hb
        · exact ih y hold
  exact ⟨hacc⟩

/-- The original root-extension interface follows from parent replacement. -/
theorem terminating_extendPar
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hwf : Terminating g) {a b : Term (sigma ⊕ sigma) nu}
    (_ha : g a = none) (hnr : ¬ Reach g b a) : Terminating (extendPar g a b) :=
  terminating_extendPar_of_no_return hwf hnr

/-! ## Parent replacement on an arbitrary carrier -/

namespace ParentReplacement

universe w

variable {α : Type w}

/-- A finite chain of parent edges. -/
inductive Path (g : α → Option α) : α → α → Prop
  | refl (a : α) : Path g a a
  | head {a b c : α} : g a = some b → Path g b c → Path g a c

/-- Well-foundedness of the reversed parent relation. -/
def Terminating (g : α → Option α) : Prop :=
  WellFounded (fun b a => g a = some b)

open scoped Classical in
/-- Replace the parent of one node. -/
noncomputable def replace (g : α → Option α) (a b : α) : α → Option α :=
  fun x => if x = a then some b else g x

open scoped Classical in
/-- Remove the parent of one node. -/
noncomputable def cut (g : α → Option α) (a : α) : α → Option α :=
  fun x => if x = a then none else g x

@[simp] theorem replace_self (g : α → Option α) (a b : α) :
    replace g a b a = some b := by
  classical
  simp [replace]

theorem replace_of_ne {g : α → Option α} {a b x : α} (h : x ≠ a) :
    replace g a b x = g x := by
  classical
  simp [replace, h]

theorem replace_edge {g : α → Option α} {a b x y : α}
    (h : replace g a b x = some y) : (x = a ∧ y = b) ∨ g x = some y := by
  by_cases hx : x = a
  · subst x
    rw [replace_self] at h
    exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  · exact Or.inr ((replace_of_ne hx).symm.trans h)

theorem cut_edge {g : α → Option α} {a x y : α}
    (h : cut g a x = some y) : x ≠ a ∧ g x = some y := by
  classical
  by_cases hx : x = a
  · simp [cut, hx] at h
  · exact ⟨hx, by simpa [cut, hx] using h⟩

theorem Path.mono {g h : α → Option α}
    (hsub : ∀ {x y : α}, g x = some y → h x = some y)
    {a b : α} (hab : Path g a b) : Path h a b := by
  induction hab with
  | refl a => exact Path.refl a
  | head he _ ih => exact Path.head (hsub he) ih

theorem Path.eq_of_none {g : α → Option α} {a b : α}
    (h : Path g a b) (ha : g a = none) : a = b := by
  cases h with
  | refl => rfl
  | head he _ => rw [ha] at he; cases he

theorem Path.toReflTransGenRev {g : α → Option α} {a b : α}
    (h : Path g a b) : Relation.ReflTransGen (fun y x => g x = some y) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | head he _ ih => exact Relation.ReflTransGen.tail ih he

theorem Terminating.no_cycle {g : α → Option α} (hwf : Terminating g)
    {a b : α} (he : g a = some b) (hp : Path g b a) : False := by
  let r : α → α → Prop := fun y x => g x = some y
  have hrev : Relation.ReflTransGen r a b := hp.toReflTransGenRev
  have hback : Relation.TransGen r b a := Relation.TransGen.single he
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hrev with hEq | hf
  · subst b
    exact hwf.transGen.asymmetric a a hback hback
  · exact hwf.transGen.asymmetric a b hf hback

/-- A path ending at the modified node survives by stopping at its first visit. -/
theorem Path.replace_to_source {g : α → Option α} {a b x : α}
    (h : Path g x a) : Path (replace g a b) x a := by
  induction h with
  | refl x => exact Path.refl x
  | @head p q r he _ ih =>
      by_cases hp : p = r
      · subst p
        exact Path.refl r
      · exact Path.head (by rw [replace_of_ne hp]; exact he) ih

theorem Path.cut_to_source {g : α → Option α} {a x : α}
    (h : Path g x a) : Path (cut g a) x a := by
  classical
  induction h with
  | refl x => exact Path.refl x
  | @head p q r he _ ih =>
      by_cases hp : p = r
      · subst p
        exact Path.refl r
      · exact Path.head (by simpa [cut, hp] using he) ih

theorem path_cut_to_source_iff {g : α → Option α} {a x : α} :
    Path (cut g a) x a ↔ Path g x a :=
  ⟨fun h => h.mono (fun he => (cut_edge he).2), Path.cut_to_source⟩

theorem terminating_replace_of_no_return {g : α → Option α}
    (hwf : Terminating g) {a b : α} (hnr : ¬ Path g b a) :
    Terminating (replace g a b) := by
  have key : ∀ z : α, ¬ Path g z a →
      Acc (fun y x => replace g a b x = some y) z := by
    intro z
    induction z using hwf.induction with
    | _ z ih =>
        intro hz
        refine Acc.intro z ?_
        intro y hy
        rcases replace_edge hy with ⟨rfl, -⟩ | hold
        · exact hz (Path.refl z) |>.elim
        · exact ih y hold (fun hya => hz (Path.head hold hya))
  have hb := key b hnr
  refine ⟨?_⟩
  intro z
  induction z using hwf.induction with
  | _ z ih =>
      refine Acc.intro z ?_
      intro y hy
      rcases replace_edge hy with ⟨rfl, rfl⟩ | hold
      · exact hb
      · exact ih y hold

/-- Replacing an edge of a terminating parent graph creates exactly the old
return paths from its new target to its source. -/
theorem terminating_replace_iff {g : α → Option α}
    (hwf : Terminating g) {a b : α} :
    Terminating (replace g a b) ↔ ¬ Path g b a := by
  constructor
  · intro h hba
    exact h.no_cycle (replace_self g a b) hba.replace_to_source
  · exact terminating_replace_of_no_return hwf

theorem terminating_cut_of_replace {g : α → Option α} {a b : α}
    (h : Terminating (replace g a b)) : Terminating (cut g a) := by
  have hsub : Subrelation (fun y x => cut g a x = some y)
      (fun y x => replace g a b x = some y) := by
    intro y x he
    obtain ⟨hne, hold⟩ := cut_edge he
    rw [replace_of_ne hne]
    exact hold
  exact Subrelation.wf hsub h

theorem replace_cut (g : α → Option α) (a b : α) :
    replace (cut g a) a b = replace g a b := by
  classical
  funext x
  by_cases hx : x = a <;> simp [replace, cut, hx]

/-- The criterion applies even when the original graph is not terminating. -/
theorem terminating_replace_iff_cut {g : α → Option α} {a b : α} :
    Terminating (replace g a b) ↔ Terminating (cut g a) ∧ ¬ Path g b a := by
  constructor
  · intro h
    exact ⟨terminating_cut_of_replace h,
      fun hba => h.no_cycle (replace_self g a b) hba.replace_to_source⟩
  · rintro ⟨hcut, hnr⟩
    have hnr' : ¬ Path (cut g a) b a :=
      fun hba => hnr (path_cut_to_source_iff.mp hba)
    simpa only [replace_cut] using terminating_replace_of_no_return hcut hnr'

/-- The usual finite descent on natural numbers. -/
def descendingParent : Nat → Option Nat
  | 0 => none
  | n + 1 => some n

theorem descendingParent_terminating : Terminating descendingParent := by
  have hsub : Subrelation (fun y x => descendingParent x = some y) Nat.lt := by
    intro y x he
    cases x with
    | zero => simp [descendingParent] at he
    | succ n =>
        have hny : n = y := Option.some.inj he
        subst y
        exact Nat.lt_succ_self n
  exact Subrelation.wf hsub Nat.lt_wfRel.wf

/-- A non-root parent can be replaced without losing termination. -/
theorem non_root_replacement_terminates :
    descendingParent 2 = some 1 ∧ Terminating (replace descendingParent 2 0) := by
  refine ⟨rfl, (terminating_replace_iff descendingParent_terminating).2 ?_⟩
  intro h
  have hbad : (0 : Nat) = 2 := h.eq_of_none rfl
  omega

/-- Reversing an existing descent creates a cycle. -/
theorem backward_replacement_not_terminating :
    ¬ Terminating (replace descendingParent 1 2) := by
  intro h
  exact (terminating_replace_iff descendingParent_terminating).1 h
    (Path.head rfl (Path.refl 1))

/-- A graph containing one self-loop and otherwise no edges. -/
def selfLoopParent (n : Nat) : Option Nat := if n = 1 then some 1 else none

theorem selfLoopParent_not_terminating : ¬ Terminating selfLoopParent := by
  intro h
  exact h.no_cycle (a := 1) (b := 1) (by decide) (Path.refl 1)

/-- Replacing the self-loop by an edge to a terminal node repairs termination. -/
theorem selfLoop_replacement_terminates : Terminating (replace selfLoopParent 1 0) := by
  apply terminating_replace_iff_cut.mpr
  have hcut : cut selfLoopParent 1 = fun _ => none := by
    classical
    funext x
    by_cases hx : x = 1 <;> simp [cut, selfLoopParent, hx]
  refine ⟨?_, ?_⟩
  · rw [hcut]
    exact ⟨fun x => Acc.intro x (fun _ h => by cases h)⟩
  · intro h
    have hbad : (0 : Nat) = 1 := h.eq_of_none rfl
    omega

end ParentReplacement

/-- The generic replacement and term-specific interface are extensionally equal. -/
theorem extendPar_eq_replace
    (g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    (a b : Term (sigma ⊕ sigma) nu) :
    extendPar g a b = ParentReplacement.replace g a b := by
  classical
  funext x
  by_cases hx : x = a <;> simp [extendPar, ParentReplacement.replace, hx]

theorem Reach.toParentPath
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a b : Term (sigma ⊕ sigma) nu} (h : Reach g a b) :
    ParentReplacement.Path g a b := by
  induction h with
  | refl a => exact ParentReplacement.Path.refl a
  | head he _ ih => exact ParentReplacement.Path.head he ih

theorem ParentReplacement.Path.toReach
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a b : Term (sigma ⊕ sigma) nu} (h : ParentReplacement.Path g a b) :
    Reach g a b := by
  induction h with
  | refl a => exact Reach.refl a
  | head he _ ih => exact Reach.head he ih

/-- The term-graph interface has the same necessary and sufficient criterion. -/
theorem terminating_extendPar_iff
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hwf : Terminating g) {a b : Term (sigma ⊕ sigma) nu} :
    Terminating (extendPar g a b) ↔ ¬ Reach g b a := by
  rw [extendPar_eq_replace]
  constructor
  · intro h hba
    exact (ParentReplacement.terminating_replace_iff hwf).1 h hba.toParentPath
  · intro h
    exact (ParentReplacement.terminating_replace_iff hwf).2 (fun hp => h hp.toReach)

/-- The term-graph criterion also covers repairs of a nonterminating old graph. -/
theorem terminating_extendPar_iff_cut
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a b : Term (sigma ⊕ sigma) nu} :
    Terminating (extendPar g a b) ↔
      Terminating (ParentReplacement.cut g a) ∧ ¬ Reach g b a := by
  rw [extendPar_eq_replace]
  constructor
  · intro h
    obtain ⟨hc, hn⟩ := ParentReplacement.terminating_replace_iff_cut.mp h
    exact ⟨hc, fun hp => hn hp.toParentPath⟩
  · rintro ⟨hc, hn⟩
    exact ParentReplacement.terminating_replace_iff_cut.mpr
      ⟨hc, fun hp => hn hp.toReach⟩

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.hatEq
#check @OperatorKO7.Meta.UniqueNormalization.EqvOn

#print axioms OperatorKO7.Meta.UniqueNormalization.DownOn.constructorCompatible
#print axioms OperatorKO7.Meta.UniqueNormalization.Reach.comparable
#print axioms OperatorKO7.Meta.UniqueNormalization.EqvOn.trans
#print axioms OperatorKO7.Meta.UniqueNormalization.terminating_extendPar
