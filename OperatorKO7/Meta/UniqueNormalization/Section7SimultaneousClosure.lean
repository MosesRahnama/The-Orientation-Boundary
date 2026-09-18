import Mathlib.Data.Fintype.Pigeonhole
import OperatorKO7.Meta.UniqueNormalization.Section7TightClosure
import OperatorKO7.Meta.UniqueNormalization.Proposition22

/-!
# Section 7 simultaneous closure

This module records the exact root rewrite occurrences inside a relativized
Down derivation. A Down pair missed by a locally signature-closed equivalence
contains a missed root rewrite in that same derivation. For a complete targeted
proof graph, every missed root rewrite therefore has a successor missed root
rewrite reached through its concrete aligned-argument obstruction.
-/

set_option autoImplicit false

namespace List

universe u v

/-- Argumentwise evidence with one distinguished pair carrying a stronger
predicate. The marked pair can occur at any list position. -/
inductive Forall₂Marked {alpha : Type u} {beta : Type v}
    (P Q : alpha -> beta -> Prop) : List alpha -> List beta -> Prop where
  | head {a b as bs} : Q a b -> List.Forall₂ P as bs ->
      Forall₂Marked P Q (a :: as) (b :: bs)
  | tail {a b as bs} : P a b -> Forall₂Marked P Q as bs ->
      Forall₂Marked P Q (a :: as) (b :: bs)

/-- Forget which pair was marked. -/
theorem Forall₂Marked.toForall₂
    {alpha : Type u} {beta : Type v} {P Q : alpha -> beta -> Prop}
    (hQ : forall a b, Q a b -> P a b) :
    forall {as bs}, Forall₂Marked P Q as bs -> List.Forall₂ P as bs := by
  intro as bs h
  induction h with
  | head hhead htail => exact List.Forall₂.cons (hQ _ _ hhead) htail
  | tail hhead _ ih => exact List.Forall₂.cons hhead ih

/-- A marked argument relation has an exact prefix, marked pair, and suffix
decomposition. -/
theorem Forall₂Marked.exists_split
    {alpha : Type u} {beta : Type v} {P Q : alpha -> beta -> Prop} :
    forall {as bs}, Forall₂Marked P Q as bs ->
      ∃ xp yp a b xt yt,
        as = xp ++ a :: xt ∧ bs = yp ++ b :: yt ∧
        List.Forall₂ P xp yp ∧ Q a b ∧ List.Forall₂ P xt yt := by
  intro as bs h
  induction h with
  | @head a b as bs hab htail =>
      exact ⟨[], [], a, b, as, bs, rfl, rfl, List.Forall₂.nil, hab, htail⟩
  | @tail a b as bs hab _ ih =>
      obtain ⟨xp, yp, x, y, xt, yt, hxs, hys, hpre, hxy, hsuf⟩ := ih
      exact ⟨a :: xp, b :: yp, x, y, xt, yt,
        by simp [hxs], by simp [hys], List.Forall₂.cons hab hpre, hxy, hsuf⟩

end List

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Root occurrences inside Down derivations -/

/-- A specific root rewrite occurs in a derivation of one relativized Down
pair. Congruence constructors expose the exact marked argument directly, so the
recursive occurrence is never hidden inside a nested inductive parameter. -/
inductive DownRootOccurrence
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (p q : Term (sigma ⊕ sigma) nu) :
    Term (sigma ⊕ sigma) nu -> Term (sigma ⊕ sigma) nu -> Prop where
  | here {b}
      (hp : p ∈ A) (hq : q ∈ A) (hroot : rootStep R p q)
      (hqb : DownOn A R q b) : DownRootOccurrence A R p q p b
  | symm {a b}
      (hab : DownOn A R a b) (occ : DownRootOccurrence A R p q a b) :
      DownRootOccurrence A R p q b a
  | rootTail {a c b}
      (ha : a ∈ A) (hc : c ∈ A) (hroot : rootStep R a c)
      (hcb : DownOn A R c b) (occ : DownRootOccurrence A R p q c b) :
      DownRootOccurrence A R p q a b
  | barCompArg {d : sigma}
      {xp yp : List (Term (sigma ⊕ sigma) nu)}
      {x y : Term (sigma ⊕ sigma) nu}
      {xt yt : List (Term (sigma ⊕ sigma) nu)} {b}
      (ha : Term.app (.inr d) (xp ++ x :: xt) ∈ A)
      (hpre : List.Forall₂ (DownOn A R) xp yp)
      (hxy : DownOn A R x y) (occ : DownRootOccurrence A R p q x y)
      (hsuf : List.Forall₂ (DownOn A R) xt yt)
      (hcb : DownOn A R (Term.app (.inr d) (yp ++ y :: yt)) b) :
      DownRootOccurrence A R p q (Term.app (.inr d) (xp ++ x :: xt)) b
  | barCompTail {d : sigma} {as cs : List (Term (sigma ⊕ sigma) nu)} {b}
      (ha : Term.app (.inr d) as ∈ A)
      (hargs : List.Forall₂ (DownOn A R) as cs)
      (hcb : DownOn A R (Term.app (.inr d) cs) b)
      (occ : DownRootOccurrence A R p q (Term.app (.inr d) cs) b) :
      DownRootOccurrence A R p q (Term.app (.inr d) as) b
  | tildeArg {f : sigma ⊕ sigma}
      {xp yp : List (Term (sigma ⊕ sigma) nu)}
      {x y : Term (sigma ⊕ sigma) nu}
      {xt yt : List (Term (sigma ⊕ sigma) nu)}
      (ha : Term.app f (xp ++ x :: xt) ∈ A)
      (hb : Term.app f (yp ++ y :: yt) ∈ A)
      (hpre : List.Forall₂ (DownOn A R) xp yp)
      (hxy : DownOn A R x y) (occ : DownRootOccurrence A R p q x y)
      (hsuf : List.Forall₂ (DownOn A R) xt yt) :
      DownRootOccurrence A R p q
        (Term.app f (xp ++ x :: xt)) (Term.app f (yp ++ y :: yt))

/-- Every occurrence certificate projects to the Down pair in which it occurs. -/
theorem DownRootOccurrence.toDownOn
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {p q a b : Term (sigma ⊕ sigma) nu}
    (h : DownRootOccurrence A R p q a b) : DownOn A R a b := by
  cases h with
  | here hp hq hroot hqb => exact DownOn.rootComp hp hq hroot hqb
  | symm hab _ => exact DownOn.symm hab
  | rootTail ha hc hroot hcb _ => exact DownOn.rootComp ha hc hroot hcb
  | barCompArg ha hpre hxy _ hsuf hcb =>
      exact DownOn.barComp ha
        (List.rel_append hpre (List.Forall₂.cons hxy hsuf)) hcb
  | barCompTail ha hargs hcb _ => exact DownOn.barComp ha hargs hcb
  | tildeArg ha hb hpre hxy _ hsuf =>
      exact DownOn.tildeCl ha hb
        (List.rel_append hpre (List.Forall₂.cons hxy hsuf))

/-- The marked pair is an actual root rewrite between carrier members. -/
theorem DownRootOccurrence.rootWitness
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {p q a b : Term (sigma ⊕ sigma) nu}
    (h : DownRootOccurrence A R p q a b) :
    p ∈ A ∧ q ∈ A ∧ rootStep R p q := by
  induction h with
  | here hp hq hroot _ => exact ⟨hp, hq, hroot⟩
  | symm _ _ ih => exact ih
  | rootTail _ _ _ _ _ ih => exact ih
  | barCompArg _ _ _ _ _ _ ih => exact ih
  | barCompTail _ _ _ _ ih => exact ih
  | tildeArg _ _ _ _ _ _ ih => exact ih

/-- If a reflexive, symmetric, transitive, locally signature-closed relation
misses a Down pair, the same Down derivation contains a root rewrite that the
relation misses. The occurrence certificate retains its exact derivation path. -/
theorem DownOn.exists_occurring_missing_rootStep_of_sigmaClosedOn
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {E : CRel sigma nu}
    (hrefl : forall a, a ∈ A -> E a a)
    (hsymm : forall a b, E a b -> E b a)
    (htrans : forall a b c, E a b -> E b c -> E a c)
    (hclosed : SigmaClosedOn A E)
    {a b : Term (sigma ⊕ sigma) nu} (hdown : DownOn A R a b)
    (hmissing : ¬ E a b) :
    ∃ p q, p ∈ A ∧ q ∈ A ∧ rootStep R p q ∧ ¬ E p q ∧
      DownRootOccurrence A R p q a b := by
  refine DownOn.induction
    (P := fun x y => ¬ E x y ->
      ∃ p q, p ∈ A ∧ q ∈ A ∧ rootStep R p q ∧ ¬ E p q ∧
        DownRootOccurrence A R p q x y) ?_ hdown hmissing
  intro x y hstep hxyMissing
  have splitArgs : forall {xs ys : List (Term (sigma ⊕ sigma) nu)},
      List.Forall₂
        (fun s t => DownOn A R s t ∧
          (¬ E s t ->
            ∃ p q, p ∈ A ∧ q ∈ A ∧ rootStep R p q ∧ ¬ E p q ∧
              DownRootOccurrence A R p q s t)) xs ys ->
      List.Forall₂ E xs ys ∨
        ∃ p q, p ∈ A ∧ q ∈ A ∧ rootStep R p q ∧ ¬ E p q ∧
          List.Forall₂Marked (DownOn A R)
            (fun s t => DownOn A R s t ∧ DownRootOccurrence A R p q s t)
            xs ys := by
    intro xs ys hall
    induction hall with
    | nil => exact Or.inl List.Forall₂.nil
    | @cons s t ss ts hst htail ih =>
        by_cases hE : E s t
        · rcases ih with hrest | ⟨p, q, hp, hq, hpq, hpqMissing, hmarked⟩
          · exact Or.inl (List.Forall₂.cons hE hrest)
          · exact Or.inr ⟨p, q, hp, hq, hpq, hpqMissing,
              List.Forall₂Marked.tail hst.1 hmarked⟩
        · obtain ⟨p, q, hp, hq, hpq, hpqMissing, hocc⟩ := hst.2 hE
          exact Or.inr ⟨p, q, hp, hq, hpq, hpqMissing,
            List.Forall₂Marked.head ⟨hst.1, hocc⟩
              (forall₂_mono (fun _ _ hpair => hpair.1) htail)⟩
  obtain ⟨hx, hy, hbody⟩ := hstep
  rcases hbody with rfl | hinv | ⟨c, hc, hroot, htail⟩ |
      ⟨d, as, cs, rfl, hargs, hmid, htail⟩ | hhat | hbar
  · exact (hxyMissing (hrefl x hx)).elim
  · have hbackMissing : ¬ E y x := fun h => hxyMissing (hsymm _ _ h)
    obtain ⟨p, q, hp, hq, hpq, hpqMissing, hocc⟩ := hinv.2 hbackMissing
    exact ⟨p, q, hp, hq, hpq, hpqMissing,
      DownRootOccurrence.symm hinv.1 hocc⟩
  · by_cases hxc : E x c
    · have htailMissing : ¬ E c y := fun hcy => hxyMissing (htrans _ _ _ hxc hcy)
      obtain ⟨p, q, hp, hq, hpq, hpqMissing, hocc⟩ := htail.2 htailMissing
      exact ⟨p, q, hp, hq, hpq, hpqMissing,
        DownRootOccurrence.rootTail hx hc hroot htail.1 hocc⟩
    · exact ⟨x, c, hx, hc, hroot, hxc,
        DownRootOccurrence.here hx hc hroot htail.1⟩
  · rcases splitArgs hargs with hargsE |
        ⟨p, q, hp, hq, hpq, hpqMissing, hmarked⟩
    · have hheadE : E (Term.app (.inr d) as) (Term.app (.inr d) cs) :=
        hclosed _ _ hx hmid ⟨.inr d, as, cs, trivial, rfl, rfl, hargsE⟩
      have htailMissing : ¬ E (Term.app (.inr d) cs) y :=
        fun hcy => hxyMissing (htrans _ _ _ hheadE hcy)
      obtain ⟨p, q, hp, hq, hpq, hpqMissing, hocc⟩ := htail.2 htailMissing
      exact ⟨p, q, hp, hq, hpq, hpqMissing,
        DownRootOccurrence.barCompTail hx
          (forall₂_mono (fun _ _ hpair => hpair.1) hargs) htail.1 hocc⟩
    · obtain ⟨xp, yp, x', y', xt, yt, rfl, rfl,
          hpre, hpair, hsuf⟩ := hmarked.exists_split
      exact ⟨p, q, hp, hq, hpq, hpqMissing,
        DownRootOccurrence.barCompArg hx hpre hpair.1 hpair.2 hsuf htail.1⟩
  · obtain ⟨f, as, bs, _, rfl, rfl, hargs⟩ := hhat
    rcases splitArgs hargs with hargsE |
        ⟨p, q, hp, hq, hpq, hpqMissing, hmarked⟩
    · exact (hxyMissing
        (hclosed _ _ hx hy ⟨f, as, bs, trivial, rfl, rfl, hargsE⟩)).elim
    · obtain ⟨xp, yp, x', y', xt, yt, rfl, rfl,
          hpre, hpair, hsuf⟩ := hmarked.exists_split
      exact ⟨p, q, hp, hq, hpq, hpqMissing,
        DownRootOccurrence.tildeArg hx hy hpre hpair.1 hpair.2 hsuf⟩
  · obtain ⟨f, as, bs, _, rfl, rfl, hargs⟩ := hbar
    rcases splitArgs hargs with hargsE |
        ⟨p, q, hp, hq, hpq, hpqMissing, hmarked⟩
    · exact (hxyMissing
        (hclosed _ _ hx hy ⟨f, as, bs, trivial, rfl, rfl, hargsE⟩)).elim
    · obtain ⟨xp, yp, x', y', xt, yt, rfl, rfl,
          hpre, hpair, hsuf⟩ := hmarked.exists_split
      exact ⟨p, q, hp, hq, hpq, hpqMissing,
        DownRootOccurrence.tildeArg hx hy hpre hpair.1 hpair.2 hsuf⟩

/-- Graph equality specialization of the exact occurrence theorem. -/
theorem PGraph.missing_downOn_has_occurring_missing_rootStep
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (hclosed : SigmaClosedOn A (EqvOn A rho.par))
    {a b : Term (sigma ⊕ sigma) nu} (hdown : DownOn A R a b)
    (hmissing : ¬ EqvOn A rho.par a b) :
    ∃ p q, p ∈ A ∧ q ∈ A ∧ rootStep R p q ∧
      ¬ EqvOn A rho.par p q ∧ DownRootOccurrence A R p q a b :=
  DownOn.exists_occurring_missing_rootStep_of_sigmaClosedOn
    (fun _ hx => EqvOn.refl hx)
    (fun _ _ h => EqvOn.symm h)
    (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂)
    hclosed hdown hmissing

/-! ## The finite missing-root dependency system -/

/-- A root rewrite inside the finite carrier that one proof graph does not
represent. -/
def RootFailure
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (rho : PGraph A R)
    (e : Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu) : Prop :=
  e.1 ∈ A ∧ e.2 ∈ A ∧ rootStep R e.1 e.2 ∧
    ¬ EqvOn A rho.par e.1 e.2

/-- Exact dependency from one missing root rewrite to a missing root rewrite
occurring inside its concrete aligned-argument Down obstruction. -/
def MissingRootArgumentDependency
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : TermTargetedPGraph A R)
    (a b p q : Term (sigma ⊕ sigma) nu) : Prop :=
  RootFailure A R rho.graph (a, b) ∧ RootFailure A R rho.graph (p, q) ∧
    ∃ d, rho.graph.par (rho.target.pick a) = some d ∧
      rootStep R (rho.target.pick a) d ∧ EqvOn A rho.graph.par a d ∧
      ¬ EqvOn A rho.graph.par b d ∧
      ∃ u v, BarReachOn A R a u ∧ BarStepOn A R u v ∧
        BarReachOn A R v (rho.target.pick a) ∧
        ∃ f xp yp x y xt yt,
          u = .app (.inr f) (xp ++ x :: xt) ∧
          v = .app (.inr f) (yp ++ y :: yt) ∧
          xp.length = yp.length ∧ DownOn A R x y ∧
          ¬ EqvOn A rho.graph.par x y ∧ DownRootOccurrence A R p q x y

/-- Every missing root rewrite of an equality-complete targeted graph has an
exact successor missing root rewrite in its aligned-argument obstruction. -/
theorem TermTargetedPGraph.rootFailure_has_dependency
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    (rho : TermTargetedPGraph A R) (hmax : rho.graph.EqualityComplete)
    {a b : Term (sigma ⊕ sigma) nu}
    (hfailure : RootFailure A R rho.graph (a, b)) :
    ∃ p q, MissingRootArgumentDependency rho a b p q := by
  obtain ⟨ha, hb, hroot, hmissing⟩ := hfailure
  obtain ⟨d, htarget, htargetRoot, had, hbd,
      u, v, hpre, hstep, hsuf, f, xp, yp, x, y, xt, yt,
      hu, hv, hlen, hdown, hxyMissing⟩ :=
    rho.missing_root_has_unrepresented_argument
      hA hR hstrong hmax ha hb hroot hmissing
  have hclosed := rho.sigmaClosedOn_of_complete hA hR hmax.complete
  obtain ⟨p, q, hp, hq, hpq, hpqMissing, hocc⟩ :=
    rho.graph.missing_downOn_has_occurring_missing_rootStep
      hclosed hdown hxyMissing
  exact ⟨p, q, ⟨⟨ha, hb, hroot, hmissing⟩,
    ⟨hp, hq, hpq, hpqMissing⟩,
    d, htarget, htargetRoot, had, hbd,
    u, v, hpre, hstep, hsuf,
    f, xp, yp, x, y, xt, yt, hu, hv, hlen, hdown, hxyMissing, hocc⟩⟩

open scoped Classical in
/-- The finite set of root rewrites in the carrier missed by a proof graph. -/
noncomputable def missingRootPairs
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (rho : PGraph A R) :
    Finset (Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu) :=
  (A.toFinset.product A.toFinset).filter
    (fun e => rootStep R e.1 e.2 ∧ ¬ EqvOn A rho.par e.1 e.2)

/-- Membership in missingRootPairs is exactly the RootFailure predicate. -/
theorem mem_missingRootPairs_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R}
    {e : Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu} :
    e ∈ missingRootPairs A R rho ↔ RootFailure A R rho e := by
  classical
  constructor
  · intro he
    have h := Finset.mem_filter.mp he
    have hmem := Finset.mem_product.mp h.1
    exact ⟨List.mem_toFinset.mp hmem.1, List.mem_toFinset.mp hmem.2,
      h.2.1, h.2.2⟩
  · rintro ⟨ha, hb, hroot, hmissing⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨List.mem_toFinset.mpr ha, List.mem_toFinset.mpr hb⟩,
      hroot, hmissing⟩

/-- The missing-root set is empty exactly when every root rewrite in the
carrier is represented. -/
theorem missingRootPairs_eq_empty_iff_rootStepsRepresented
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) :
    missingRootPairs A R rho = ∅ ↔ RootStepsRepresented A R rho := by
  classical
  constructor
  · intro hempty a b ha hb hroot
    by_contra hmissing
    have hmem : (a, b) ∈ missingRootPairs A R rho :=
      mem_missingRootPairs_iff.mpr ⟨ha, hb, hroot, hmissing⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  · intro hrepresented
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hfailure := mem_missingRootPairs_iff.mp he
    exact hfailure.2.2.2
      (hrepresented hfailure.1 hfailure.2.1 hfailure.2.2.1)

/-- On the finite missing-root set, the exact dependency relation is total. -/
theorem TermTargetedPGraph.missingRootPairs_dependency_total
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    (rho : TermTargetedPGraph A R) (hmax : rho.graph.EqualityComplete)
    {e : Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu}
    (he : e ∈ missingRootPairs A R rho.graph) :
    ∃ e', e' ∈ missingRootPairs A R rho.graph ∧
      MissingRootArgumentDependency rho e.1 e.2 e'.1 e'.2 := by
  obtain ⟨p, q, hdependency⟩ :=
    rho.rootFailure_has_dependency hA hR hstrong hmax
      (mem_missingRootPairs_iff.mp he)
  exact ⟨(p, q), mem_missingRootPairs_iff.mpr hdependency.2.1, hdependency⟩

/-! ## Exact finite cycle classification -/

/-- Following a total relation for a positive finite number of iterates gives
a nonempty relation path. -/
theorem iterate_transGen_of_lt
    {alpha : Type u} {r : alpha -> alpha -> Prop} {f : alpha -> alpha}
    (hf : ∀ x, r x (f x)) (x : alpha) {m n : Nat} (hmn : m < n) :
    Relation.TransGen r ((f^[m]) x) ((f^[n]) x) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hmn)
  have hk : k ≠ 0 := by omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hstep : ∀ i : Nat,
      r ((f^[m + i]) x) ((f^[m + (i + 1)]) x) := by
    intro i
    rw [show m + (i + 1) = (m + i) + 1 by omega,
      Function.iterate_succ_apply']
    exact hf ((f^[m + i]) x)
  have hpath : ∀ i : Nat,
      Relation.TransGen r ((f^[m]) x) ((f^[m + (i + 1)]) x) := by
    intro i
    induction i with
    | zero => simpa using Relation.TransGen.single (hstep 0)
    | succ i ih =>
        exact ih.tail (by simpa [Nat.add_assoc] using hstep (i + 1))
  simpa [Nat.add_assoc] using hpath j

/-- Every total relation on a nonempty finite type contains a directed cycle.
The result retains the full nonempty transitive closure, not only repeated
endpoints of a chosen sequence. -/
theorem finite_total_relation_has_transGen_cycle
    {alpha : Type u} [Finite alpha] [Nonempty alpha]
    {r : alpha -> alpha -> Prop} (htotal : ∀ x, ∃ y, r x y) :
    ∃ x, Relation.TransGen r x x := by
  classical
  let f : alpha -> alpha := fun x => Classical.choose (htotal x)
  have hf : ∀ x, r x (f x) := fun x => Classical.choose_spec (htotal x)
  let x : alpha := Classical.choice inferInstance
  obtain ⟨m, n, hmn, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k : Nat => (f^[k]) x)
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · have hpath := iterate_transGen_of_lt hf x hlt
    have hcycle : Relation.TransGen r ((f^[n]) x) ((f^[n]) x) := by
      simpa only [heq] using hpath
    exact ⟨(f^[n]) x, hcycle⟩
  · have hpath := iterate_transGen_of_lt hf x hlt
    have hcycle : Relation.TransGen r ((f^[m]) x) ((f^[m]) x) := by
      simpa only [heq] using hpath
    exact ⟨(f^[m]) x, hcycle⟩

/-- The finite carrier of root failures of one targeted proof graph. -/
def MissingRootNode
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : TermTargetedPGraph A R) :=
  ↥(missingRootPairs A R rho.graph)

/-- The exact aligned-argument dependency restricted to actual missing root
rewrites. -/
def MissingRootDependency
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : TermTargetedPGraph A R) :
    MissingRootNode rho -> MissingRootNode rho -> Prop :=
  fun e e' => MissingRootArgumentDependency rho
    e.1.1 e.1.2 e'.1.1 e'.1.2

/-- A closed chain of concrete missing root rewrites, with every edge carrying
the aligned-argument occurrence data of `MissingRootArgumentDependency`. -/
def HasMissingRootDependencyCycle
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : TermTargetedPGraph A R) : Prop :=
  ∃ e, Relation.TransGen (MissingRootDependency rho) e e

/-- Equality completeness and the strong overlap condition make the restricted
missing-root dependency total. -/
theorem TermTargetedPGraph.missingRootDependency_total
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    (rho : TermTargetedPGraph A R) (hmax : rho.graph.EqualityComplete) :
    ∀ e : MissingRootNode rho, ∃ e', MissingRootDependency rho e e' := by
  intro e
  obtain ⟨e', he', hdep⟩ :=
    rho.missingRootPairs_dependency_total hA hR hstrong hmax e.2
  exact ⟨⟨e', he'⟩, hdep⟩

/-- Every nonempty missing-root set of an equality-complete targeted graph has
a dependency cycle. -/
theorem TermTargetedPGraph.hasMissingRootDependencyCycle_of_nonempty
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    (rho : TermTargetedPGraph A R) (hmax : rho.graph.EqualityComplete)
    (hnonempty : (missingRootPairs A R rho.graph).Nonempty) :
    HasMissingRootDependencyCycle rho := by
  classical
  let e : MissingRootNode rho := ⟨hnonempty.choose, hnonempty.choose_spec⟩
  letI : Fintype (MissingRootNode rho) :=
    inferInstanceAs (Fintype ↑(missingRootPairs A R rho.graph))
  letI : Nonempty (MissingRootNode rho) := ⟨e⟩
  exact finite_total_relation_has_transGen_cycle
    (rho.missingRootDependency_total hA hR hstrong hmax)

/-- For an equality-complete targeted graph, failure of root representation is
equivalent to a closed chain of exact missing-root argument dependencies. -/
theorem TermTargetedPGraph.not_rootStepsRepresented_iff_dependencyCycle
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    (rho : TermTargetedPGraph A R) (hmax : rho.graph.EqualityComplete) :
    ¬ RootStepsRepresented A R rho.graph ↔ HasMissingRootDependencyCycle rho := by
  classical
  constructor
  · intro hmissing
    apply rho.hasMissingRootDependencyCycle_of_nonempty hA hR hstrong hmax
    exact Finset.nonempty_iff_ne_empty.mpr (fun hempty =>
      hmissing ((missingRootPairs_eq_empty_iff_rootStepsRepresented rho.graph).mp hempty))
  · rintro ⟨e, _⟩ hrepresented
    have hfailure : RootFailure A R rho.graph e.1 :=
      mem_missingRootPairs_iff.mp e.2
    exact hfailure.2.2.2
      (hrepresented hfailure.1 hfailure.2.1 hfailure.2.2.1)

/-- Exact finite classification: root rewrites are all represented, or the
failure data contain a dependency cycle. -/
theorem TermTargetedPGraph.rootStepsRepresented_or_dependencyCycle
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    (rho : TermTargetedPGraph A R) (hmax : rho.graph.EqualityComplete) :
    RootStepsRepresented A R rho.graph ∨ HasMissingRootDependencyCycle rho := by
  classical
  by_cases hrepresented : RootStepsRepresented A R rho.graph
  · exact Or.inl hrepresented
  · exact Or.inr ((rho.not_rootStepsRepresented_iff_dependencyCycle
      hA hR hstrong hmax).mp hrepresented)

/-! ## Parent replacement and independently proved equations -/

/-- A new parent joining different old classes cannot create a parent cycle.
The changed source need not be a normal form. -/
theorem PGraph.replacement_terminating
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b) :
    Terminating (extendPar rho.par a b) := by
  apply terminating_extendPar_of_no_return rho.term
  intro hba
  exact hne (EqvOn.symm (EqvOn.of_reach hb ha hba))

/-- Parent replacement keeps both endpoints of every edge in the carrier. -/
theorem PGraph.replacement_mem
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) {x y : Term (sigma ⊕ sigma) nu}
    (hxy : extendPar rho.par a b x = some y) : x ∈ A ∧ y ∈ A := by
  by_cases hxa : x = a
  · subst x
    have hby : b = y := Option.some.inj ((extendPar_self rho.par a b).symm.trans hxy)
    exact ⟨ha, hby ▸ hb⟩
  · exact rho.mem_edge ((extendPar_of_ne hxa).symm.trans hxy)

/-- Every temporary edge uses the old graph's grey relation. This does not
assert that the temporary parent map satisfies its own grey condition. -/
theorem PGraph.replacement_greyOld
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (hab : Grey A R (EqvOn A rho.par) a b)
    {x y : Term (sigma ⊕ sigma) nu}
    (hxy : extendPar rho.par a b x = some y) :
    Grey A R (EqvOn A rho.par) x y := by
  by_cases hxa : x = a
  · subst x
    have hby : b = y := Option.some.inj ((extendPar_self rho.par a b).symm.trans hxy)
    exact hby ▸ hab
  · exact rho.grey ((extendPar_of_ne hxa).symm.trans hxy)

/-- All temporary equalities are sound, and every constructor equality
decomposes into old graph equalities. Neither a normal-form premise nor an
overlap premise is required. -/
theorem PGraph.replacement_sound
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b)
    (hab : Grey A R (EqvOn A rho.par) a b)
    {x y : Term (sigma ⊕ sigma) nu}
    (hxy : EqvOn A (extendPar rho.par a b) x y) :
    DownOn A R x y ∧
      (ConTopped x → ConTopped y → hatEq (EqvOn A rho.par) x y) :=
  lemma52 hA hR rho (rho.replacement_terminating ha hb hne)
    (fun h => rho.replacement_mem ha hb h)
    (fun h => rho.replacement_greyOld hab h) hxy

/-- Sound seed equations from the original graph or its temporary replacement.
No transitive closure of this union is taken. -/
def PGraph.ReplacementSeed
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a b : Term (sigma ⊕ sigma) nu) : CRel sigma nu :=
  fun x y => EqvOn A rho.par x y ∨ EqvOn A (extendPar rho.par a b) x y

theorem PGraph.replacementSeed_sound
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b)
    (hab : Grey A R (EqvOn A rho.par) a b)
    {x y : Term (sigma ⊕ sigma) nu} (hxy : rho.ReplacementSeed a b x y) :
    DownOn A R x y := by
  rcases hxy with hold | hnew
  · exact rho.sub hold
  · exact (rho.replacement_sound hA hR ha hb hne hab hnew).1

/-- Constructor pairs in either forest decompose into old graph equalities. -/
theorem PGraph.replacementSeed_constructor_decomposition
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b)
    (hab : Grey A R (EqvOn A rho.par) a b)
    {x y : Term (sigma ⊕ sigma) nu} (hx : ConTopped x) (hy : ConTopped y)
    (hxy : rho.ReplacementSeed a b x y) : hatEq (EqvOn A rho.par) x y := by
  rcases hxy with hold | hnew
  · exact rho.constructorCompatible hA hR hx hy hold
  · exact (rho.replacement_sound hA hR ha hb hne hab hnew).2 hx hy

/-- The union of old and temporary equalities is constructor-compatible;
its transitivity is not required. -/
theorem PGraph.replacementSeed_constructorCompatible
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b)
    (hab : Grey A R (EqvOn A rho.par) a b) :
    ConstructorCompatible (rho.ReplacementSeed a b) := by
  intro x y hx hy hxy
  rcases rho.replacementSeed_constructor_decomposition hA hR ha hb hne hab hx hy hxy with
      hvar | ⟨f, xs, ys, ⟨c, hfc⟩, hleft, hright, hargs⟩
  · exact Or.inl hvar
  · subst f
    exact Or.inr ⟨c, xs, ys, hleft, hright,
      forall₂_mono (fun _ _ h => Or.inl h) hargs⟩

/-- Context formation retains the proved seed's constructor compatibility. -/
theorem PGraph.replacementSeed_context_constructorCompatible
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b)
    (hab : Grey A R (EqvOn A rho.par) a b) :
    ConstructorCompatible (CT (rho.ReplacementSeed a b)) :=
  CT.constructorCompatible (rho.replacementSeed_constructorCompatible hA hR ha hb hne hab)

/-- The seed includes the requested new equation on the actual changed edge. -/
theorem PGraph.replacementSeed_new
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) : rho.ReplacementSeed a b a b :=
  Or.inr (EqvOn.of_reach ha hb
    (Reach.head (extendPar_self rho.par a b) (Reach.refl b)))

/-- Context formation preserves any independently proved seed relation on a
subterm-closed carrier. No composition rule is added. -/
theorem CT.downOn_of_sound_base
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} {E : CRel sigma nu}
    (hE : ∀ {x y}, E x y → DownOn A R x y)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hab : CT E a b) : DownOn A R a b := by
  let S : CRel sigma nu := fun x y => x ∈ A → y ∈ A → DownOn A R x y
  have hsub : ∀ x y, E x y → S x y := fun _ _ h _ _ => hE h
  have hclosed : SigmaClosed S := by
    rintro x y ⟨f, xs, ys, _, rfl, rfl, hargs⟩ hx hy
    apply DownOn.tildeCl hx hy
    exact forall₂_compose_of_mem hargs
      (forall₂_self (r := fun (p q : Term (sigma ⊕ sigma) nu) => p = q)
        (fun _ => rfl) ys)
      (fun p hp q hq r _ hpq hqr => by
        subst r
        exact hpq (hA.arg hx hp) (hA.arg hy hq))
  exact (CT.least hsub hclosed hab) ha hb

/-- A self-grey terminating forest is a proof graph whenever every
constructor-topped equality it creates already lies in the context closure of
an independently sound seed. Cyclic constructor dependencies require no
well-foundedness argument under this stronger, directly checkable condition. -/
def PGraph.of_contextGeneratedConstructorSlice
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    (hmem : ∀ {a b}, g a = some b → a ∈ A ∧ b ∈ A)
    (hterm : Terminating g)
    (hgrey : ∀ {a b}, g a = some b → Grey A R (EqvOn A g) a b)
    {seed : CRel sigma nu}
    (hseed : ∀ {a b}, seed a b → DownOn A R a b)
    (hslice : ∀ {a b}, ConTopped a → ConTopped b →
      EqvOn A g a b → CT seed a b) : PGraph A R :=
  PGraph.of_constructorSlice hR g hmem hterm hgrey
    (fun ha hb hab => CT.downOn_of_sound_base hA hseed hab.mem.1 hab.mem.2
      (hslice ha hb hab))

/-- If a self-grey forest equality is unsound, then the same two parent paths
reach a constructor-topped equality outside the context closure of every sound
seed. This is the exact obstruction to the context-generated construction. -/
theorem EqvOn.exists_reachable_constructor_outside_contextClosure
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hmem : ∀ {a b}, g a = some b → a ∈ A ∧ b ∈ A)
    (hgrey : ∀ {a b}, g a = some b → Grey A R (EqvOn A g) a b)
    {seed : CRel sigma nu}
    (hseed : ∀ {a b}, seed a b → DownOn A R a b)
    {a b : Term (sigma ⊕ sigma) nu} (hab : EqvOn A g a b)
    (hbad : ¬ DownOn A R a b) :
    ∃ x y, Reach g a x ∧ Reach g b y ∧ ConTopped x ∧ ConTopped y ∧
      EqvOn A g x y ∧ ¬ CT seed x y := by
  obtain ⟨x, y, hax, hby, hcx, hcy, hxy, hxyBad⟩ :=
    hab.exists_reachable_constructor_failure hR hmem hgrey hbad
  refine ⟨x, y, hax, hby, hcx, hcy, hxy, ?_⟩
  intro hct
  exact hxyBad (CT.downOn_of_sound_base hA hseed hxy.mem.1 hxy.mem.2 hct)

/-- Old and temporary equations can be combined in distinct arguments of the
same context, with soundness derived from both source forests. -/
theorem PGraph.replacementSeed_context_sound
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b)
    (hab : Grey A R (EqvOn A rho.par) a b)
    {x y : Term (sigma ⊕ sigma) nu} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : CT (rho.ReplacementSeed a b) x y) : DownOn A R x y :=
  CT.downOn_of_sound_base hA
    (fun h => rho.replacementSeed_sound hA hR ha hb hne hab h) hx hy hxy

/-- A final parent map representing every temporary edge preserves all old
equations exactly when it recovers the single displaced parent equation. -/
theorem PGraph.replacement_preserves_iff_displaced_edge
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a b : Term (sigma ⊕ sigma) nu)
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hnew : ∀ {x y}, extendPar rho.par a b x = some y → EqvOn A g x y) :
    (∀ {x y}, EqvOn A rho.par x y → EqvOn A g x y) ↔
      (∀ c, rho.par a = some c → EqvOn A g a c) := by
  constructor
  · intro h c hac
    exact h (EqvOn.of_reach (rho.mem_edge hac).1 (rho.mem_edge hac).2
      (Reach.head hac (Reach.refl c)))
  · intro h x y hxy
    apply EqvOn.mono_of_parent_eqv (g := rho.par) (h := g) ?_ hxy
    intro p q hpq
    by_cases hpa : p = a
    · subst p
      exact h q hpq
    · exact hnew ((extendPar_of_ne hpa).trans hpq)

/-- Recovering the displaced edge preserves each old root equation in the
same final parent map that represents the new edge. -/
theorem PGraph.replacement_recovers_roots
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (hroot : RootStepsRepresented A R rho)
    (a b : Term (sigma ⊕ sigma) nu)
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hnew : ∀ {x y}, extendPar rho.par a b x = some y → EqvOn A g x y)
    (hold : ∀ c, rho.par a = some c → EqvOn A g a c) :
    EqvOn A g a b ∧
      (∀ {x y}, x ∈ A → y ∈ A → rootStep R x y → EqvOn A g x y) := by
  refine ⟨hnew (extendPar_self rho.par a b), ?_⟩
  intro x y hx hy hxy
  exact (rho.replacement_preserves_iff_displaced_edge a b hnew).mpr hold
    (hroot hx hy hxy)

/-! ## Residuals of the actual constructor translation -/

/-- Constructor-pattern instances related below their roots give an actual
omega-unifier of the two left-hand sides. -/
theorem omegaUnifiable_of_constructor_bar
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {E : CRel sigma nu} (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hCC : ConstructorCompatible E)
    {r₁ r₂ : Rule (sigma ⊕ sigma) nu} (hr₁ : r₁ ∈ R) (hr₂ : r₂ ∈ R)
    {s t : Subst (sigma ⊕ sigma) nu}
    (hbar : barRel E (Subst.apply s r₁.lhs) (Subst.apply t r₂.lhs)) :
    OmegaUnifiable r₁.lhs r₂.lhs := by
  obtain ⟨F, ps, hl₁, hps⟩ := hR r₁ hr₁
  obtain ⟨G, qs, hl₂, hqs⟩ := hR r₂ hr₂
  rw [hl₁, hl₂] at hbar ⊢
  obtain ⟨f, xs, ys, _, hx, hy, hargs⟩ := hbar
  simp only [Subst.apply_app, Subst.applyList_eq_map, Term.app.injEq] at hx hy
  obtain ⟨hF, hxs⟩ := hx
  obtain ⟨hG, hys⟩ := hy
  have hFG : F = G := Sum.inr.inj (hF.trans hG.symm)
  subst G
  rw [← hxs, ← hys] at hargs
  exact lemma36 hsymm htrans hCC hps hqs hargs

/-- Matching the same constructor pattern relates every variable occurrence
in that pattern, before taking any context closure. -/
theorem variables_related_of_constructor_bar
    {E : CRel sigma nu} (hCC : ConstructorCompatible E)
    {F : sigma} {ps : List (Term (sigma ⊕ sigma) nu)}
    (hps : ∀ p ∈ ps, ConOnly p) {s t : Subst (sigma ⊕ sigma) nu}
    (hbar : barRel E (Subst.apply s (.app (.inr F) ps))
      (Subst.apply t (.app (.inr F) ps)))
    {x : nu} (hx : VarOccurs x (.app (.inr F) ps)) : E (s x) (t x) := by
  obtain ⟨f, xs, ys, _, hleft, hright, hargs⟩ := hbar
  simp only [Subst.apply_app, Subst.applyList_eq_map, Term.app.injEq] at hleft hright
  obtain ⟨_, hxs⟩ := hleft
  obtain ⟨_, hys⟩ := hright
  rw [← hxs, ← hys] at hargs
  obtain ⟨p, hp, hxp⟩ := hx.app_inv
  exact lemma33 hCC p (hps p hp) (pointwise_of_forall₂ hargs p hp) x hxp

/-- An active translated right-hand side is either a variable, whose images
are E-related, or a destructor application with context-related arguments. -/
theorem destructorLabel_instances_residual
    {E : CRel sigma nu} {s t : Subst (sigma ⊕ sigma) nu}
    (r : Term sigma nu)
    (hvars : ∀ x, VarOccurs x (destructorLabel r) → E (s x) (t x)) :
    E (Subst.apply s (destructorLabel r)) (Subst.apply t (destructorLabel r)) ∨
      barRel (CT E) (Subst.apply s (destructorLabel r))
        (Subst.apply t (destructorLabel r)) := by
  cases r with
  | var x => exact Or.inl (hvars x VarOccurs.here)
  | app f args =>
      let qs := Term.mapSymList (Sum.inr : sigma → sigma ⊕ sigma) args
      have hargs : List.Forall₂ (CT E)
          (qs.map (Subst.apply s)) (qs.map (Subst.apply t)) := by
        apply forall₂_of_pointwise
        intro q hq
        apply lemma34 CT.sigmaClosed q
        intro x hx
        exact CT.base (hvars x (VarOccurs.arg hq hx))
      apply Or.inr
      exact ⟨.inr f, qs.map (Subst.apply s), qs.map (Subst.apply t),
        ⟨f, rfl⟩, by simp [destructorLabel_app, Subst.applyList_eq_map, qs],
        by simp [destructorLabel_app, Subst.applyList_eq_map, qs], hargs⟩

/-- Pattern rules change only the root label, so their output arguments
retain the input relation exactly, even for distinct patterns. -/
theorem patternRule_instances_hat
    {E : CRel sigma nu} {s t : Subst (sigma ⊕ sigma) nu}
    (n m : sigma × List (Term sigma nu))
    (hbar : barRel E (Subst.apply s (patternRuleOf n).lhs)
      (Subst.apply t (patternRuleOf m).lhs)) :
    hatRel E (Subst.apply s (patternRuleOf n).rhs)
      (Subst.apply t (patternRuleOf m).rhs) := by
  obtain ⟨f, xs, ys, _, hleft, hright, hargs⟩ := hbar
  simp only [patternRuleOf, Subst.apply_app, Subst.applyList_eq_map,
    Term.app.injEq] at hleft hright
  obtain ⟨hn, hxs⟩ := hleft
  obtain ⟨hm, hys⟩ := hright
  have hnm : n.1 = m.1 := Sum.inr.inj (hn.trans hm.symm)
  refine ⟨.inl n.1, xs, ys, ⟨n.1, rfl⟩, ?_, ?_, hargs⟩
  · simpa only [patternRuleOf, Subst.apply_app, Subst.applyList_eq_map]
      using congrArg (Term.app (.inl n.1)) hxs
  · simpa only [patternRuleOf, Subst.apply_app, Subst.applyList_eq_map, hnm]
      using congrArg (Term.app (.inl n.1)) hys

/-- The ambient relation identifies the rules; the residual retains the
smaller constructor-compatible seed without requiring its transitivity. -/
theorem translated_seed_fork_destructor_residual
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {E : CRel sigma nu} (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hCC : ConstructorCompatible E)
    {S : CRel sigma nu} (hSE : ∀ x y, S x y → E x y)
    (hSCC : ConstructorCompatible S)
    {a b c d : Term (sigma ⊕ sigma) nu}
    (hab : rootStep (constructorTranslation R) a b)
    (hac : barRel S a c) (hcd : rootStep (constructorTranslation R) c d) :
    S b d ∨ barRel (DCT S) b d ∨ hatRel S b d := by
  obtain ⟨r₁, hr₁, s, ha, hb⟩ := hab
  obtain ⟨r₂, hr₂, t, hc, hd⟩ := hcd
  rw [ha, hc] at hac
  rw [hb, hd]
  have hou := omegaUnifiable_of_constructor_bar
    (constructorRules_constructorTranslation R) hsymm htrans hCC hr₁ hr₂
      (tildeOn_mono hSE hac)
  rcases mem_constructorTranslation hr₁ with ⟨r, hr, rfl⟩ | ⟨n, hn, rfl⟩
  · rcases mem_constructorTranslation hr₂ with ⟨r', hr', rfl⟩ | ⟨m, hm, rfl⟩
    · have hOU : OmegaUnifiable r.lhs r'.lhs :=
        omegaUnifiable_of_destructorPattern hou
      obtain ⟨heq, _⟩ := hno r hr r' hr' r.lhs (Subterm.refl _) r.lhs_isApp hOU
      subst r'
      obtain ⟨F, ps, hl, hps⟩ :=
        constructorRules_constructorTranslation R (transRule r) (transRule_mem hr)
      have hvars : ∀ x, VarOccurs x (destructorLabel r.rhs) → S (s x) (t x) := by
        intro x hx
        have hxl := transRule_occurs (hvar r hr) hx
        rw [hl] at hxl
        exact variables_related_of_constructor_bar hSCC hps
          (by simpa only [hl] using hac) hxl
      rcases destructorLabel_instances_destructor_residual r.rhs
          (fun x hx => hvars x (hx.mapSym Sum.inr)) with hE | hbar
      · exact Or.inl hE
      · exact Or.inr (Or.inl hbar)
    · exact (prop22_rule_pattern hno hr hm hou).elim
  · rcases mem_constructorTranslation hr₂ with ⟨r, hr, rfl⟩ | ⟨m, hm, rfl⟩
    · exact (prop22_rule_pattern hno hr hn hou.symm).elim
    · exact Or.inr (Or.inr (patternRule_instances_hat n m hac))

/-- Active translated rules use destructor contexts only; pattern rules
retain one constructor congruence of the original relation. -/
theorem translated_semantic_fork_destructor_residual
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {E : CRel sigma nu} (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hCC : ConstructorCompatible E)
    {a b c d : Term (sigma ⊕ sigma) nu}
    (hab : rootStep (constructorTranslation R) a b)
    (hac : barRel E a c) (hcd : rootStep (constructorTranslation R) c d) :
    E b d ∨ barRel (DCT E) b d ∨ hatRel E b d :=
  translated_seed_fork_destructor_residual hno hvar hsymm htrans hCC
    (fun _ _ h => h) hCC hab hac hcd

theorem translated_seed_fork_context
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {E : CRel sigma nu} (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hCC : ConstructorCompatible E)
    {S : CRel sigma nu} (hSE : ∀ x y, S x y → E x y)
    (hSCC : ConstructorCompatible S)
    {a b c d : Term (sigma ⊕ sigma) nu}
    (hab : rootStep (constructorTranslation R) a b)
    (hac : barRel S a c) (hcd : rootStep (constructorTranslation R) c d) :
    CT S b d := by
  rcases translated_seed_fork_destructor_residual hno hvar hsymm htrans hCC
      hSE hSCC hab hac hcd with hs | hbar | hhat
  · exact CT.base hs
  · exact DCT.toCT (DCT.barClosed hbar)
  · exact CT.sigmaClosed _ _
      (tildeAll_of_hatRel (tildeOn_mono (fun _ _ => CT.base) hhat))

/-- Constructor compatibility is preserved by intersection; neither relation
needs to be transitive. -/
theorem constructorCompatible_intersection
    {E S : CRel sigma nu} (hE : ConstructorCompatible E) (hS : ConstructorCompatible S) :
    ConstructorCompatible (fun x y => E x y ∧ S x y) := by
  intro x y hx hy hxy
  rcases hE x y hx hy hxy.1 with hv | ⟨f, xs, ys, rfl, rfl, hargs⟩
  · exact Or.inl hv
  · rcases hS _ _ hx hy hxy.2 with ⟨z, hz, _⟩ | ⟨g, us, vs, hl, hr, hargs'⟩
    · cases hz
    · have hfg' : f = g := Sum.inl.inj (Term.app.inj hl).1
      subst g
      have hxs : xs = us := (Term.app.inj hl).2
      have hys : ys = vs := (Term.app.inj hr).2
      subst us
      subst vs
      refine Or.inr ⟨f, xs, ys, rfl, rfl, ?_⟩
      clear hx hy hxy hl hr
      revert hargs'
      induction hargs with
      | nil => intro _; exact List.Forall₂.nil
      | cons h _ ih =>
          intro hargs'
          cases hargs' with
          | cons h' hs => exact List.Forall₂.cons ⟨h, h'⟩ (ih hs)

/-- A proposed constructor-compatible equivalence certifies rule identity;
the output derivation uses only its independently sound argument pairs. -/
theorem translated_fork_sound_in_constructor_equivalence
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {E : CRel sigma nu} (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hCC : ConstructorCompatible E)
    {a b c d : Term (sigma ⊕ sigma) nu} (hb : b ∈ A) (hd : d ∈ A)
    (hab : rootStep (constructorTranslation R) a b)
    (hac : barRel (fun x y => DownOn A (constructorTranslation R) x y ∧ E x y) a c)
    (hcd : rootStep (constructorTranslation R) c d) :
    DownOn A (constructorTranslation R) b d := by
  apply CT.downOn_of_sound_base (E := fun x y =>
    DownOn A (constructorTranslation R) x y ∧ E x y) hA (fun h => h.1) hb hd
  exact translated_seed_fork_context hno hvar hsymm htrans hCC
    (fun _ _ h => h.2)
    (constructorCompatible_intersection
      (DownOn.constructorCompatible hA (constructorRules_constructorTranslation R)) hCC)
    hab hac hcd

/-- An ambient equivalence identifies the translated rules; the actual old
and temporary forests supply the output derivation. -/
theorem PGraph.translated_replacementSeed_fork_sound
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    (rho : PGraph A (constructorTranslation R))
    {p q : Term (sigma ⊕ sigma) nu} (hp : p ∈ A) (hq : q ∈ A)
    (hne : ¬ EqvOn A rho.par p q)
    (hpq : Grey A (constructorTranslation R) (EqvOn A rho.par) p q)
    {E : CRel sigma nu} (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hCC : ConstructorCompatible E)
    (hSE : ∀ x y, rho.ReplacementSeed p q x y → E x y)
    {a b c d : Term (sigma ⊕ sigma) nu} (hb : b ∈ A) (hd : d ∈ A)
    (hab : rootStep (constructorTranslation R) a b)
    (hac : barRel (rho.ReplacementSeed p q) a c)
    (hcd : rootStep (constructorTranslation R) c d) :
    DownOn A (constructorTranslation R) b d := by
  apply rho.replacementSeed_context_sound hA
    (constructorRules_constructorTranslation R) hp hq hne hpq hb hd
  exact translated_seed_fork_context hno hvar hsymm htrans hCC hSE
    (rho.replacementSeed_constructorCompatible hA
      (constructorRules_constructorTranslation R) hp hq hne hpq) hab hac hcd

/-- The destructor-only result implies the previous unrestricted-context
statement without changing its public type. -/
theorem translated_semantic_fork_residual
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {E : CRel sigma nu} (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hCC : ConstructorCompatible E)
    {a b c d : Term (sigma ⊕ sigma) nu}
    (hab : rootStep (constructorTranslation R) a b)
    (hac : barRel E a c) (hcd : rootStep (constructorTranslation R) c d) :
    E b d ∨ barRel (CT E) b d ∨ hatRel E b d := by
  rcases translated_semantic_fork_destructor_residual hno hvar hsymm htrans hCC
    hab hac hcd with he | hbar | hhat
  · exact Or.inl he
  · exact Or.inr (Or.inl (tildeOn_mono (fun _ _ h => DCT.toCT h) hbar))
  · exact Or.inr (Or.inr hhat)

/-- The translation satisfies semantic critical-pair context closure for
arbitrary variable types, without constructing fresh-variable generalisations. -/
theorem translated_semantic_fork_context
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {E : CRel sigma nu} (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hCC : ConstructorCompatible E)
    {a b c d : Term (sigma ⊕ sigma) nu}
    (hab : rootStep (constructorTranslation R) a b)
    (hac : barRel E a c) (hcd : rootStep (constructorTranslation R) c d) :
    CT E b d := by
  rcases translated_semantic_fork_residual hno hvar hsymm htrans hCC hab hac hcd with
    hE | hbar | hhat
  · exact CT.base hE
  · exact CT.sigmaClosed _ _ (tildeOn_mono_pred (fun _ _ => True.intro) hbar)
  · exact CT.sigmaClosed _ _
      (tildeOn_mono_pred (fun _ _ => True.intro)
        (tildeOn_mono (fun _ _ h => CT.base h) hhat))

/-- The actual constructor translation has a consistency invariant without
an infinite-variable premise. -/
theorem constructorTranslation_consistencyInvariant
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) :
    ConsistencyInvariant (constructorTranslation R) (Down (constructorTranslation R)) :=
  ⟨fun _ _ h => Down.consistent (constructorRules_constructorTranslation R) h,
    Down.sigmaClosed _,
    fun _ _ hsymm htrans hCC _ _ _ _ h₁ h₂ h₃ =>
      translated_semantic_fork_context hno hvar hsymm htrans hCC h₁ h₂ h₃⟩

/-- The actual translation determines every root contractum even when the
variable type is finite. -/
theorem constructorTranslation_deterministic
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) :
    Deterministic (constructorTranslation R) := by
  intro a b d hab had
  obtain ⟨f, args, rfl⟩ := rootStep_source_destructor
    (constructorRules_constructorTranslation R) hab
  apply (CT_equality_iff b d).mp
  apply translated_semantic_fork_context (E := (· = ·)) hno hvar
    (fun _ _ h => h.symm) (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    constructorCompatible_equality hab ?_ had
  exact ⟨.inr f, args, args, ⟨f, rfl⟩, rfl, rfl,
    forall₂_self_of (fun _ _ => rfl)⟩

/-- The finite-root almost condition holds for the actual translation without
requiring an infinite supply for syntactic common generalisations. -/
theorem constructorTranslation_almost
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) :
    AlmostNonOmegaOverlapping (constructorTranslation R) :=
  ⟨prop22_root_overlaps, constructorTranslation_deterministic hno hvar⟩

/-! ## Fixed-old destructor residuals -/

/-- A missing old pair is one destructor congruence on the fixed represented
equality of a proof graph that the same equality does not yet contain. -/
def PGraph.MissingOld
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R)
    (p : Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu) : Prop :=
  p.1 ∈ A ∧ p.2 ∈ A ∧ barRel (EqvOn A rho.par) p.1 p.2 ∧
    ¬ EqvOn A rho.par p.1 p.2

/-- A residual keeps the old graph fixed. It records both missing destructor
pairs, both first-root paths, the semantic critical-pair residual, and the
subterm occurrence of the successor inside the two contracta. -/
def PGraph.ResidualOld
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R)
    (p q : Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu) : Prop :=
  rho.MissingOld p ∧ rho.MissingOld q ∧
    ∃ x y z w,
      TightNonRootReach rho p.1 x ∧ rho.par x = some y ∧ rootStep R x y ∧
      TightNonRootReach rho p.2 z ∧ rho.par z = some w ∧ rootStep R z w ∧
      barRel (EqvOn A rho.par) x z ∧ CT (EqvOn A rho.par) y w ∧
      ¬ EqvOn A rho.par y w ∧ Subterm q.1 y ∧ Subterm q.2 w

/-! ### Finite fixed-old residual saturation -/

/-- A pair of terms over the doubled signature. -/
abbrev PGraph.ResidualPair (sigma : Type u) (nu : Type v) :=
  Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu

open scoped Classical in
/-- The number of distinct terms in a finite carrier, with classical equality
hidden so the theorem interfaces retain arbitrary symbol and variable types. -/
noncomputable def PGraph.residualCarrierCard
    (A : List (Term (sigma ⊕ sigma) nu)) : Nat :=
  A.toFinset.card

open scoped Classical in
/-- The finite carrier square with classical equality hidden behind a
noncomputable definition, so all mathematical theorems remain polymorphic over
arbitrary symbol and variable types. -/
noncomputable def PGraph.residualPairUniverse
    (A : List (Term (sigma ⊕ sigma) nu)) :
    Finset (PGraph.ResidualPair sigma nu) :=
  A.toFinset.product A.toFinset

/-- Membership in the residual pair universe is exactly membership of both
endpoints in the finite coalgebra. -/
theorem PGraph.mem_residualPairUniverse_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {p : PGraph.ResidualPair sigma nu} :
    p ∈ PGraph.residualPairUniverse A ↔ p.1 ∈ A ∧ p.2 ∈ A := by
  classical
  simp [PGraph.residualPairUniverse]

/-- The residual pair universe has the exact square cardinality. -/
theorem PGraph.card_residualPairUniverse
    (A : List (Term (sigma ⊕ sigma) nu)) :
    (PGraph.residualPairUniverse A).card = PGraph.residualCarrierCard A ^ 2 := by
  classical
  simp [PGraph.residualPairUniverse, PGraph.residualCarrierCard, pow_two]

open scoped Classical in
/-- One saturation round adds every residual successor that remains in the
finite carrier. The old proof graph is fixed throughout the construction. -/
noncomputable def PGraph.residualSuccSet
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (S : Finset (PGraph.ResidualPair sigma nu)) :
    Finset (PGraph.ResidualPair sigma nu) :=
  S ∪ (PGraph.residualPairUniverse A).filter
    (fun q => ∃ p ∈ S, rho.ResidualOld p q)

open scoped Classical in
/-- Iterated fixed-old residual saturation from one selected missing pair. -/
noncomputable def PGraph.residualIter
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (p : PGraph.ResidualPair sigma nu) :
    Nat → Finset (PGraph.ResidualPair sigma nu)
  | 0 => {p}
  | n + 1 => rho.residualSuccSet (rho.residualIter p n)

/-- Exact membership in one saturation round. -/
theorem PGraph.mem_residualSuccSet_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {S : Finset (PGraph.ResidualPair sigma nu)}
    {q : PGraph.ResidualPair sigma nu} :
    q ∈ rho.residualSuccSet S ↔
      q ∈ S ∨ q ∈ PGraph.residualPairUniverse A ∧
        ∃ p ∈ S, rho.ResidualOld p q := by
  classical
  simp only [PGraph.residualSuccSet, Finset.mem_union, Finset.mem_filter]

/-- Every residual iteration is contained in the next one. -/
theorem PGraph.residualIter_mono_succ
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (p : PGraph.ResidualPair sigma nu) (n : Nat) :
    rho.residualIter p n ⊆ rho.residualIter p (n + 1) := by
  intro q hq
  exact (PGraph.mem_residualSuccSet_iff).2 (Or.inl hq)

/-- Fixed-old residual saturation is monotone in the number of rounds. -/
theorem PGraph.residualIter_mono
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (p : PGraph.ResidualPair sigma nu) {m n : Nat}
    (hmn : m ≤ n) : rho.residualIter p m ⊆ rho.residualIter p n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => exact fun _ h => h
  | succ k ih =>
      intro q hq
      apply rho.residualIter_mono_succ p (m + k)
      exact ih (by omega) hq

/-- Starting from a missing old pair, every residual iterate stays in the
finite pair carrier. -/
theorem PGraph.residualIter_subset_pairUniverse
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu}
    (hp : rho.MissingOld p) :
    ∀ n, rho.residualIter p n ⊆ PGraph.residualPairUniverse A := by
  classical
  intro n
  induction n with
  | zero =>
      intro q hq
      have hqp : q = p := by simpa [PGraph.residualIter] using hq
      subst q
      exact PGraph.mem_residualPairUniverse_iff.mpr ⟨hp.1, hp.2.1⟩
  | succ n ih =>
      intro q hq
      rcases PGraph.mem_residualSuccSet_iff.mp hq with hq | ⟨hqA, _⟩
      · exact ih hq
      · exact hqA

/-- Starting from a missing old pair, every member reached by saturation is
another missing old pair for the same fixed graph. -/
theorem PGraph.residualIter_all_missing
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu}
    (hp : rho.MissingOld p) :
    ∀ n q, q ∈ rho.residualIter p n → rho.MissingOld q := by
  classical
  intro n
  induction n with
  | zero =>
      intro q hq
      have hqp : q = p := by simpa [PGraph.residualIter] using hq
      simpa [hqp] using hp
  | succ n ih =>
      intro q hq
      rcases PGraph.mem_residualSuccSet_iff.mp hq with hq | ⟨_, r, hr, hrq⟩
      · exact ih q hq
      · exact hrq.2.1

/-- Once an iteration is stable, every later iteration is stable. -/
theorem PGraph.residualIter_eq_succ_of_eq_succ_at
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu} {n k : Nat}
    (h : rho.residualIter p n = rho.residualIter p (n + 1)) :
    rho.residualIter p (n + k) = rho.residualIter p (n + k + 1) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have hs := congrArg rho.residualSuccSet ih
      simpa [Nat.add_assoc, PGraph.residualIter] using hs

/-- Stability at one round propagates to every later round. -/
theorem PGraph.residualIter_eq_succ_of_eq_succ_of_le
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu} {m n : Nat}
    (h : rho.residualIter p m = rho.residualIter p (m + 1)) (hmn : m ≤ n) :
    rho.residualIter p n = rho.residualIter p (n + 1) := by
  have hk : n = m + (n - m) := by omega
  rw [hk]
  simpa using rho.residualIter_eq_succ_of_eq_succ_at
    (p := p) (n := m) (k := n - m) h

/-- If every earlier round grows strictly, round `n` contains at least `n+1`
distinct pairs. -/
theorem PGraph.card_residualIter_ge_of_strict_prefix
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (p : PGraph.ResidualPair sigma nu) :
    ∀ n,
      (∀ m, m < n → rho.residualIter p m ≠ rho.residualIter p (m + 1)) →
      n + 1 ≤ (rho.residualIter p n).card
  | 0, _ => by simp [PGraph.residualIter]
  | n + 1, hstrict => by
      have hprefix : ∀ m, m < n →
          rho.residualIter p m ≠ rho.residualIter p (m + 1) := by
        intro m hm
        exact hstrict m (lt_trans hm (Nat.lt_succ_self n))
      have ih := rho.card_residualIter_ge_of_strict_prefix p n hprefix
      have hsub : rho.residualIter p n ⊆ rho.residualIter p (n + 1) :=
        rho.residualIter_mono_succ p n
      have hne : rho.residualIter p n ≠ rho.residualIter p (n + 1) :=
        hstrict n (Nat.lt_succ_self n)
      have hssub : rho.residualIter p n ⊂ rho.residualIter p (n + 1) := by
        refine ⟨hsub, ?_⟩
        intro hback
        exact hne (Finset.Subset.antisymm hsub hback)
      have hcard : (rho.residualIter p n).card <
          (rho.residualIter p (n + 1)).card := Finset.card_lt_card hssub
      omega

/-- Fixed-old residual saturation stabilizes after at most the cardinality of
the finite pair carrier. -/
theorem PGraph.residualIter_stabilizes_at_pairUniverse_card
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu}
    (hp : rho.MissingOld p) :
    rho.residualIter p (PGraph.residualPairUniverse A).card =
      rho.residualIter p ((PGraph.residualPairUniverse A).card + 1) := by
  classical
  by_contra hne
  have hprefix : ∀ m, m < (PGraph.residualPairUniverse A).card + 1 →
      rho.residualIter p m ≠ rho.residualIter p (m + 1) := by
    intro m hm hmEq
    exact hne (rho.residualIter_eq_succ_of_eq_succ_of_le
      (p := p) hmEq (by omega))
  have hlower := rho.card_residualIter_ge_of_strict_prefix p
    ((PGraph.residualPairUniverse A).card + 1) hprefix
  have hupper : (rho.residualIter p ((PGraph.residualPairUniverse A).card + 1)).card ≤
      (PGraph.residualPairUniverse A).card :=
    Finset.card_le_card (rho.residualIter_subset_pairUniverse hp _)
  omega

open scoped Classical in
/-- The finite batch generated from one missing old pair. The cardinal bound is
part of the definition: saturation stops after `|A × A|` rounds. -/
noncomputable def PGraph.oldResidualBatch
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (p : PGraph.ResidualPair sigma nu) :
    Finset (PGraph.ResidualPair sigma nu) :=
  rho.residualIter p (PGraph.residualPairUniverse A).card

/-- The generating missing pair belongs to its residual batch. -/
theorem PGraph.oldResidualBatch_seed
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (p : PGraph.ResidualPair sigma nu) :
    p ∈ rho.oldResidualBatch p := by
  classical
  exact rho.residualIter_mono (p := p) (Nat.zero_le _) (by
    simp [PGraph.residualIter])

/-- Every batch member is missing from the same old graph. -/
theorem PGraph.oldResidualBatch_all_missing
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p q : PGraph.ResidualPair sigma nu}
    (hp : rho.MissingOld p) (hq : q ∈ rho.oldResidualBatch p) :
    rho.MissingOld q := by
  exact rho.residualIter_all_missing hp _ q hq

/-- The finite residual batch is closed under every fixed-old residual. -/
theorem PGraph.oldResidualBatch_closed
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p q r : PGraph.ResidualPair sigma nu}
    (hp : rho.MissingOld p) (hq : q ∈ rho.oldResidualBatch p)
    (hqr : rho.ResidualOld q r) : r ∈ rho.oldResidualBatch p := by
  classical
  have hrMissing : rho.MissingOld r := hqr.2.1
  have hrA : r ∈ PGraph.residualPairUniverse A :=
    PGraph.mem_residualPairUniverse_iff.mpr ⟨hrMissing.1, hrMissing.2.1⟩
  have hrNext : r ∈ rho.residualIter p
      ((PGraph.residualPairUniverse A).card + 1) := by
    exact PGraph.mem_residualSuccSet_iff.mpr
      (Or.inr ⟨hrA, q, hq, hqr⟩)
  have hstable := rho.residualIter_stabilizes_at_pairUniverse_card hp
  rw [← hstable] at hrNext
  exact hrNext

/-- The batch is the least predicate containing the seed and closed under every
fixed-old residual successor. -/
theorem PGraph.oldResidualBatch_least
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu}
    {P : PGraph.ResidualPair sigma nu → Prop}
    (hseed : P p) (hclosed : ∀ {q r}, P q → rho.ResidualOld q r → P r) :
    ∀ {q}, q ∈ rho.oldResidualBatch p → P q := by
  classical
  have hiter : ∀ n q, q ∈ rho.residualIter p n → P q := by
    intro n
    induction n with
    | zero =>
        intro q hq
        have hqp : q = p := by simpa [PGraph.residualIter] using hq
        simpa [hqp] using hseed
    | succ n ih =>
        intro q hq
        rcases PGraph.mem_residualSuccSet_iff.mp hq with hq | ⟨_, r, hr, hrq⟩
        · exact ih q hq
        · exact hclosed (ih r hr) hrq
  intro q hq
  exact hiter _ q hq

/-- The residual batch reaches a fixed point at the explicit `|A × A|`
bound. -/
theorem PGraph.residualSuccSet_oldResidualBatch
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu}
    (hp : rho.MissingOld p) :
    rho.residualSuccSet (rho.oldResidualBatch p) = rho.oldResidualBatch p := by
  classical
  apply Finset.Subset.antisymm
  · intro q hq
    rcases PGraph.mem_residualSuccSet_iff.mp hq with hq | ⟨_, r, hr, hrq⟩
    · exact hq
    · exact rho.oldResidualBatch_closed hp hr hrq
  · intro q hq
    exact PGraph.mem_residualSuccSet_iff.mpr (Or.inl hq)

/-- The residual batch contains at most the square of the number of carrier
terms. -/
theorem PGraph.oldResidualBatch_card_le
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu}
    (hp : rho.MissingOld p) :
    (rho.oldResidualBatch p).card ≤ PGraph.residualCarrierCard A ^ 2 := by
  classical
  calc
    (rho.oldResidualBatch p).card ≤ (PGraph.residualPairUniverse A).card :=
      Finset.card_le_card (rho.residualIter_subset_pairUniverse hp _)
    _ = PGraph.residualCarrierCard A ^ 2 := PGraph.card_residualPairUniverse A

/-- Complete specification of the finite fixed-old residual batch. -/
structure PGraph.ResidualBatchSpec
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (p : PGraph.ResidualPair sigma nu)
    (O : Finset (PGraph.ResidualPair sigma nu)) : Prop where
  seed_mem : p ∈ O
  every_missing : ∀ {q}, q ∈ O → rho.MissingOld q
  residual_closed : ∀ {q r}, q ∈ O → rho.ResidualOld q r → r ∈ O
  least : ∀ {P : PGraph.ResidualPair sigma nu → Prop}, P p →
    (∀ {q r}, P q → rho.ResidualOld q r → P r) → ∀ {q}, q ∈ O → P q
  fixed_point : rho.residualSuccSet O = O
  card_le : O.card ≤ PGraph.residualCarrierCard A ^ 2

/-- The explicit `|A × A|`-round construction satisfies the full residual
batch contract. -/
theorem PGraph.old_residual_batch_spec
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu}
    (hp : rho.MissingOld p) :
    rho.ResidualBatchSpec p (rho.oldResidualBatch p) :=
  ⟨rho.oldResidualBatch_seed p,
    fun hq => rho.oldResidualBatch_all_missing hp hq,
    fun hq hqr => rho.oldResidualBatch_closed hp hq hqr,
    fun {P} hseed hclosed {_q} hq =>
      rho.oldResidualBatch_least (P := P) hseed hclosed hq,
    rho.residualSuccSet_oldResidualBatch hp,
    rho.oldResidualBatch_card_le hp⟩

/-! ### Independently sound simultaneous batch seed -/

/-- Every missing old destructor pair is already related by the invariant.
The proof uses only the old proof graph and context formation; it does not use
the equality relation of any repaired graph. -/
theorem PGraph.missingOld_downOn
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} {rho : PGraph A R}
    {p : PGraph.ResidualPair sigma nu} (hp : rho.MissingOld p) :
    DownOn A R p.1 p.2 := by
  apply CT.downOn_of_sound_base hA (fun h => rho.sub h) hp.1 hp.2.1
  exact CT.sigmaClosed _ _
    (tildeAll_of_barRel (tildeOn_mono (fun _ _ h => CT.base h) hp.2.2.1))

/-- The semantic seed for a simultaneous residual-batch repair contains every
old graph equality and both directions of every selected missing pair. It does
not take a transitive closure. -/
def PGraph.ResidualBatchSeed
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (O : Finset (PGraph.ResidualPair sigma nu)) :
    CRel sigma nu :=
  fun x y => EqvOn A rho.par x y ∨
    ∃ p ∈ O, (x = p.1 ∧ y = p.2) ∨ (x = p.2 ∧ y = p.1)

/-- Every old equality belongs to the simultaneous batch seed. -/
theorem PGraph.residualBatchSeed_old
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (O : Finset (PGraph.ResidualPair sigma nu))
    {x y : Term (sigma ⊕ sigma) nu} (hxy : EqvOn A rho.par x y) :
    rho.ResidualBatchSeed O x y :=
  Or.inl hxy

/-- Each selected batch pair belongs to the seed in its listed direction. -/
theorem PGraph.residualBatchSeed_pair
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {O : Finset (PGraph.ResidualPair sigma nu)}
    {p : PGraph.ResidualPair sigma nu} (hp : p ∈ O) :
    rho.ResidualBatchSeed O p.1 p.2 :=
  Or.inr ⟨p, hp, Or.inl ⟨rfl, rfl⟩⟩

/-- Each selected batch pair belongs to the seed in the reverse direction. -/
theorem PGraph.residualBatchSeed_pair_symm
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {O : Finset (PGraph.ResidualPair sigma nu)}
    {p : PGraph.ResidualPair sigma nu} (hp : p ∈ O) :
    rho.ResidualBatchSeed O p.2 p.1 :=
  Or.inr ⟨p, hp, Or.inr ⟨rfl, rfl⟩⟩

/-- The simultaneous batch seed is symmetric. -/
theorem PGraph.residualBatchSeed_symm
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {O : Finset (PGraph.ResidualPair sigma nu)}
    {x y : Term (sigma ⊕ sigma) nu} (hxy : rho.ResidualBatchSeed O x y) :
    rho.ResidualBatchSeed O y x := by
  rcases hxy with hxy | ⟨p, hp, hxy | hxy⟩
  · exact Or.inl (EqvOn.symm hxy)
  · exact Or.inr ⟨p, hp, Or.inr ⟨hxy.2, hxy.1⟩⟩
  · exact Or.inr ⟨p, hp, Or.inl ⟨hxy.2, hxy.1⟩⟩

/-- Every endpoint of the simultaneous seed remains in the finite carrier. -/
theorem PGraph.ResidualBatchSpec.residualBatchSeed_mem
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu}
    {O : Finset (PGraph.ResidualPair sigma nu)}
    (hO : rho.ResidualBatchSpec p O)
    {x y : Term (sigma ⊕ sigma) nu} (hxy : rho.ResidualBatchSeed O x y) :
    x ∈ A ∧ y ∈ A := by
  rcases hxy with hxy | ⟨q, hq, hxy | hxy⟩
  · exact hxy.mem
  · obtain ⟨rfl, rfl⟩ := hxy
    have hmissing := hO.every_missing hq
    exact ⟨hmissing.1, hmissing.2.1⟩
  · obtain ⟨rfl, rfl⟩ := hxy
    have hmissing := hO.every_missing hq
    exact ⟨hmissing.2.1, hmissing.1⟩

/-- Every equation in the simultaneous batch seed is independently sound for
the invariant of the original rewrite system. -/
theorem PGraph.ResidualBatchSpec.residualBatchSeed_sound
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu}
    {O : Finset (PGraph.ResidualPair sigma nu)}
    (hO : rho.ResidualBatchSpec p O)
    {x y : Term (sigma ⊕ sigma) nu} (hxy : rho.ResidualBatchSeed O x y) :
    DownOn A R x y := by
  rcases hxy with hxy | ⟨q, hq, hxy | hxy⟩
  · exact rho.sub hxy
  · obtain ⟨rfl, rfl⟩ := hxy
    exact rho.missingOld_downOn hA (hO.every_missing hq)
  · obtain ⟨rfl, rfl⟩ := hxy
    exact DownOn.symm (rho.missingOld_downOn hA (hO.every_missing hq))

/-- Context formation over the whole simultaneous seed remains sound on the
subterm-closed carrier. -/
theorem PGraph.ResidualBatchSpec.residualBatchContext_sound
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu}
    {O : Finset (PGraph.ResidualPair sigma nu)}
    (hO : rho.ResidualBatchSpec p O)
    {x y : Term (sigma ⊕ sigma) nu} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : CT (rho.ResidualBatchSeed O) x y) : DownOn A R x y :=
  CT.downOn_of_sound_base hA (fun h => hO.residualBatchSeed_sound hA h) hx hy hxy

/-- Every old context equation embeds into the simultaneous batch context. -/
theorem PGraph.residualBatchContext_of_old
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (O : Finset (PGraph.ResidualPair sigma nu))
    {x y : Term (sigma ⊕ sigma) nu} (hxy : CT (EqvOn A rho.par) x y) :
    CT (rho.ResidualBatchSeed O) x y :=
  CT.mono (fun _ _ h => rho.residualBatchSeed_old O h) hxy

/-- Every selected pair has both contextual directions in the simultaneous
seed. -/
theorem PGraph.residualBatchContext_pair
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {O : Finset (PGraph.ResidualPair sigma nu)}
    {q : PGraph.ResidualPair sigma nu} (hq : q ∈ O) :
    CT (rho.ResidualBatchSeed O) q.1 q.2 ∧
      CT (rho.ResidualBatchSeed O) q.2 q.1 :=
  ⟨CT.base (rho.residualBatchSeed_pair hq),
    CT.base (rho.residualBatchSeed_pair_symm hq)⟩

/-- A fixed-old residual successor stays inside the batch, and its two first
root contracta are related both by the simultaneous seed context and by the
original invariant. -/
theorem PGraph.ResidualBatchSpec.residual_contracta_supported
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p q r : PGraph.ResidualPair sigma nu}
    {O : Finset (PGraph.ResidualPair sigma nu)}
    (hO : rho.ResidualBatchSpec p O) (hq : q ∈ O)
    (hqr : rho.ResidualOld q r) :
    r ∈ O ∧ ∃ x y z w,
      TightNonRootReach rho q.1 x ∧ rho.par x = some y ∧ rootStep R x y ∧
      TightNonRootReach rho q.2 z ∧ rho.par z = some w ∧ rootStep R z w ∧
      barRel (EqvOn A rho.par) x z ∧
      CT (rho.ResidualBatchSeed O) y w ∧ DownOn A R y w ∧
      ¬ EqvOn A rho.par y w ∧ Subterm r.1 y ∧ Subterm r.2 w := by
  refine ⟨hO.residual_closed hq hqr, ?_⟩
  obtain ⟨_, _, x, y, z, w, hqx, hxy, hrootXY, hqz, hzw, hrootZW,
      hbar, hct, hne, hrY, hrW⟩ := hqr
  have hseedCT : CT (rho.ResidualBatchSeed O) y w :=
    rho.residualBatchContext_of_old O hct
  have hdown : DownOn A R y w :=
    hO.residualBatchContext_sound hA (rho.mem_edge hxy).2
      (rho.mem_edge hzw).2 hseedCT
  exact ⟨x, y, z, w, hqx, hxy, hrootXY, hqz, hzw, hrootZW,
    hbar, hseedCT, hdown, hne, hrY, hrW⟩

/-- The explicitly constructed old residual batch carries simultaneous,
independently sound equations for all of its members and all their contexts. -/
theorem PGraph.oldResidualBatch_semantic_support
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu}
    (hp : rho.MissingOld p) :
    (∀ q ∈ rho.oldResidualBatch p,
      rho.ResidualBatchSeed (rho.oldResidualBatch p) q.1 q.2 ∧
      rho.ResidualBatchSeed (rho.oldResidualBatch p) q.2 q.1 ∧
      DownOn A R q.1 q.2) ∧
    (∀ {x y}, x ∈ A → y ∈ A →
      CT (rho.ResidualBatchSeed (rho.oldResidualBatch p)) x y → DownOn A R x y) := by
  let hO := rho.old_residual_batch_spec hp
  constructor
  · intro q hq
    exact ⟨rho.residualBatchSeed_pair hq, rho.residualBatchSeed_pair_symm hq,
      rho.missingOld_downOn hA (hO.every_missing hq)⟩
  · intro x y hx hy hxy
    exact hO.residualBatchContext_sound hA hx hy hxy

/-! ### Root-peeled simultaneous support -/

/-- Adding missing old destructor pairs does not enlarge the old context
closure: every added pair already belongs to that closure. -/
theorem PGraph.residualBatchContext_iff_old
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {O : Finset (PGraph.ResidualPair sigma nu)}
    (hO : ∀ q ∈ O, rho.MissingOld q)
    {x y : Term (sigma ⊕ sigma) nu} :
    CT (rho.ResidualBatchSeed O) x y ↔ CT (EqvOn A rho.par) x y := by
  constructor
  · intro hxy
    apply CT.least (S := CT (EqvOn A rho.par)) ?_ CT.sigmaClosed hxy
    intro a b hab
    rcases hab with hab | ⟨q, hq, hab | hab⟩
    · exact CT.base hab
    · obtain ⟨rfl, rfl⟩ := hab
      exact CT.sigmaClosed _ _
        (tildeAll_of_barRel
          (tildeOn_mono (fun _ _ h => CT.base h) (hO q hq).2.2.1))
    · obtain ⟨rfl, rfl⟩ := hab
      apply CT.symm (fun _ _ h => EqvOn.symm h)
      exact CT.sigmaClosed _ _
        (tildeAll_of_barRel
          (tildeOn_mono (fun _ _ h => CT.base h) (hO q hq).2.2.1))
  · exact rho.residualBatchContext_of_old O

/-- Extensional form of `residualBatchContext_iff_old`. -/
theorem PGraph.residualBatchContext_eq_old
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {O : Finset (PGraph.ResidualPair sigma nu)}
    (hO : ∀ q ∈ O, rho.MissingOld q) :
    CT (rho.ResidualBatchSeed O) = CT (EqvOn A rho.par) := by
  funext x y
  exact propext (rho.residualBatchContext_iff_old hO)

/-- A finite sequence of root contractions whose nodes remain in the finite
carrier. -/
inductive RootPeelPath
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu) :
    Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu → Prop where
  | refl (a : Term (sigma ⊕ sigma) nu) (ha : a ∈ A) : RootPeelPath A R a a
  | head {a b c : Term (sigma ⊕ sigma) nu} (ha : a ∈ A)
      (hab : rootStep R a b) (hbc : RootPeelPath A R b c) : RootPeelPath A R a c

theorem RootPeelPath.mem_left
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} (h : RootPeelPath A R a b) : a ∈ A := by
  cases h with
  | refl _ ha => exact ha
  | head ha _ _ => exact ha

theorem RootPeelPath.mem_right
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} (h : RootPeelPath A R a b) : b ∈ A := by
  induction h with
  | refl _ ha => exact ha
  | head _ _ _ ih => exact ih

theorem RootPeelPath.trans
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b c : Term (sigma ⊕ sigma) nu}
    (hab : RootPeelPath A R a b) (hbc : RootPeelPath A R b c) :
    RootPeelPath A R a c := by
  induction hab with
  | refl => exact hbc
  | head ha hxy _ ih => exact .head ha hxy (ih hbc)

/-- Root contractions can be peeled before an independently established
invariant derivation. -/
theorem RootPeelPath.downOn_comp
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b c : Term (sigma ⊕ sigma) nu}
    (hab : RootPeelPath A R a b) (hbc : DownOn A R b c) : DownOn A R a c := by
  induction hab with
  | refl => exact hbc
  | head ha hxy hrest ih =>
      exact DownOn.rootComp ha hrest.mem_left hxy (ih hbc)

theorem RootPeelPath.toDownOn
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} (hab : RootPeelPath A R a b) :
    DownOn A R a b :=
  hab.downOn_comp (DownOn.refl hab.mem_right)

/-- The root-peeled seed relates two terms when root contractions take them to
one independently context-supported pair. -/
def RootPeeledSeed
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (seed : CRel sigma nu) : CRel sigma nu :=
  fun x y => ∃ r s, RootPeelPath A R x r ∧ RootPeelPath A R y s ∧ CT seed r s

theorem RootPeeledSeed.mem
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {seed : CRel sigma nu} {x y : Term (sigma ⊕ sigma) nu}
    (hxy : RootPeeledSeed A R seed x y) : x ∈ A ∧ y ∈ A := by
  obtain ⟨r, s, hxr, hys, _⟩ := hxy
  exact ⟨hxr.mem_left, hys.mem_left⟩

theorem RootPeeledSeed.of_context
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {seed : CRel sigma nu} {x y : Term (sigma ⊕ sigma) nu}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : CT seed x y) :
    RootPeeledSeed A R seed x y :=
  ⟨x, y, .refl x hx, .refl y hy, hxy⟩

theorem RootPeeledSeed.symm
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {seed : CRel sigma nu} (hseed : ∀ a b, seed a b → seed b a)
    {x y : Term (sigma ⊕ sigma) nu} (hxy : RootPeeledSeed A R seed x y) :
    RootPeeledSeed A R seed y x := by
  obtain ⟨r, s, hxr, hys, hrs⟩ := hxy
  exact ⟨s, r, hys, hxr, CT.symm hseed hrs⟩

theorem RootPeeledSeed.root_left
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {seed : CRel sigma nu} {x y z : Term (sigma ⊕ sigma) nu}
    (hx : x ∈ A) (hxy : rootStep R x y)
    (hyz : RootPeeledSeed A R seed y z) : RootPeeledSeed A R seed x z := by
  obtain ⟨r, s, hyr, hzs, hrs⟩ := hyz
  exact ⟨r, s, .head hx hxy hyr, hzs, hrs⟩

theorem RootPeeledSeed.root_right
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {seed : CRel sigma nu} {x y z : Term (sigma ⊕ sigma) nu}
    (hy : y ∈ A) (hyz : rootStep R y z)
    (hxz : RootPeeledSeed A R seed x z) : RootPeeledSeed A R seed x y := by
  obtain ⟨r, s, hxr, hzs, hrs⟩ := hxz
  exact ⟨r, s, hxr, .head hy hyz hzs, hrs⟩

/-- Root peeling preserves semantic soundness without using transitivity of
the invariant. -/
theorem RootPeeledSeed.sound
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} {seed : CRel sigma nu}
    (hseed : ∀ {x y}, seed x y → DownOn A R x y)
    {x y : Term (sigma ⊕ sigma) nu} (hxy : RootPeeledSeed A R seed x y) :
    DownOn A R x y := by
  obtain ⟨r, s, hxr, hys, hrs⟩ := hxy
  have hrsDown : DownOn A R r s :=
    CT.downOn_of_sound_base hA hseed hxr.mem_right hys.mem_right hrs
  have hxs : DownOn A R x s := hxr.downOn_comp hrsDown
  have hyx : DownOn A R y x := hys.downOn_comp (DownOn.symm hxs)
  exact DownOn.symm hyx

/-- Context formation over the root-peeled seed remains independently sound. -/
theorem RootPeeledSeed.context_sound
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} {seed : CRel sigma nu}
    (hseed : ∀ {x y}, seed x y → DownOn A R x y)
    {x y : Term (sigma ⊕ sigma) nu} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : CT (RootPeeledSeed A R seed) x y) : DownOn A R x y :=
  CT.downOn_of_sound_base hA (fun h => RootPeeledSeed.sound hA hseed h) hx hy hxy

/-- A self-grey terminating forest is sound when every constructor equality
decomposes into argument pairs supported by root peeling from an independently
sound seed. The statement is uniform in the signature, variables, rewrite
system, carrier, parent function, and seed. -/
def PGraph.of_rootPeeledConstructorArguments
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    (hmem : ∀ {a b}, g a = some b → a ∈ A ∧ b ∈ A)
    (hterm : Terminating g)
    (hgrey : ∀ {a b}, g a = some b → Grey A R (EqvOn A g) a b)
    {seed : CRel sigma nu}
    (hseed : ∀ {a b}, seed a b → DownOn A R a b)
    (hargs : ∀ {c : sigma} {xs ys : List (Term (sigma ⊕ sigma) nu)},
      EqvOn A g (.app (.inl c) xs) (.app (.inl c) ys) →
        List.Forall₂ (RootPeeledSeed A R seed) xs ys) : PGraph A R :=
  PGraph.of_constructorSlice hR g hmem hterm hgrey (by
    intro a b ha hb hab
    rcases constructorCompatible_eqvOn_of_selfGrey hA hR hmem hgrey
        a b ha hb hab with hvar | happ
    · obtain ⟨x, rfl, rfl⟩ := hvar
      exact DownOn.refl hab.mem.1
    · obtain ⟨c, xs, ys, hax, hby, _⟩ := happ
      subst a
      subst b
      apply RootPeeledSeed.context_sound hA hseed hab.mem.1 hab.mem.2
      exact CT.app (forall₂_mono (fun _ _ h => CT.base h) (hargs hab)))

/-- The residual batch instantiates the root-peeled support relation over an
arbitrary rewrite system. -/
theorem PGraph.ResidualBatchSpec.rootPeeledBatchSeed_sound
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu}
    {O : Finset (PGraph.ResidualPair sigma nu)}
    (hO : rho.ResidualBatchSpec p O)
    {x y : Term (sigma ⊕ sigma) nu}
    (hxy : RootPeeledSeed A R (rho.ResidualBatchSeed O) x y) :
    DownOn A R x y :=
  RootPeeledSeed.sound hA (fun h => hO.residualBatchSeed_sound hA h) hxy

/-- The context closure of the root-peeled residual seed is sound on the
finite carrier. -/
theorem PGraph.ResidualBatchSpec.rootPeeledBatchContext_sound
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {p : PGraph.ResidualPair sigma nu}
    {O : Finset (PGraph.ResidualPair sigma nu)}
    (hO : rho.ResidualBatchSpec p O)
    {x y : Term (sigma ⊕ sigma) nu} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : CT (RootPeeledSeed A R (rho.ResidualBatchSeed O)) x y) :
    DownOn A R x y :=
  RootPeeledSeed.context_sound hA (fun h => hO.residualBatchSeed_sound hA h) hx hy hxy

/-- A node of the finite residual batch. -/
noncomputable def PGraph.ResidualBatchNode
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (p : PGraph.ResidualPair sigma nu) :=
  ↑(rho.oldResidualBatch p)

/-- The fixed-old residual relation restricted to its finite generated batch. -/
noncomputable def PGraph.ResidualBatchEdge
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (p : PGraph.ResidualPair sigma nu) :
    rho.ResidualBatchNode p → rho.ResidualBatchNode p → Prop :=
  fun q r => rho.ResidualOld q.1 r.1

/-- A closed fixed-old residual chain in the generated finite batch. -/
noncomputable def PGraph.HasResidualOldCycle
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (p : PGraph.ResidualPair sigma nu) : Prop :=
  ∃ q, Relation.TransGen (rho.ResidualBatchEdge p) q q

/-- For the constructor translation of an arbitrary non-omega-overlapping
system, every missing old destructor pair has two concrete first-root paths
whose contracta have a missing context residual. No cardinality assumption on
the variable type is used. -/
theorem PGraph.TightEqualityComplete.translated_missing_barRel_has_root_residual
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph A (constructorTranslation R)}
    (hmax : rho.TightEqualityComplete) (htight : rho.Tight)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hbar : barRel (EqvOn A rho.par) a b)
    (hmissing : ¬ EqvOn A rho.par a b) :
    ∃ x y z w, TightNonRootReach rho a x ∧ rho.par x = some y ∧
      rootStep (constructorTranslation R) x y ∧ TightNonRootReach rho b z ∧
      rho.par z = some w ∧ rootStep (constructorTranslation R) z w ∧
      barRel (EqvOn A rho.par) x z ∧ CT (EqvOn A rho.par) y w ∧
      ¬ EqvOn A rho.par y w := by
  have hRc : ConstructorRules (constructorTranslation R) :=
    constructorRules_constructorTranslation R
  have haShape : ∃ d args, a = .app (.inr d) args := by
    obtain ⟨f, xs, ys, ⟨d, hfd⟩, hax, _, _⟩ := hbar
    exact ⟨d, xs, hax.trans (congrArg (fun g => Term.app g xs) hfd)⟩
  have hbShape : ∃ d args, b = .app (.inr d) args := by
    obtain ⟨f, xs, ys, ⟨d, hfd⟩, _, hby, _⟩ := hbar
    exact ⟨d, ys, hby.trans (congrArg (fun g => Term.app g ys) hfd)⟩
  have hbarBA : barRel (EqvOn A rho.par) b a :=
    tildeOn_flip (tildeOn_mono (fun _ _ h => EqvOn.symm h) hbar)
  rcases htight.destructorRoute hA ha haShape with ⟨r, har, hr⟩ |
      ⟨x, y, hax, hxy, hrootXY, hbarAX⟩
  · exact (hmissing (hmax.eqvOn_of_nonRootReach_tightEdge hA hRc htight ha hb
      har hr (Or.inr (Or.inl hbar)))).elim
  rcases htight.destructorRoute hA hb hbShape with ⟨r, hbr, hr⟩ |
      ⟨z, w, hbz, hzw, hrootZW, hbarBZ⟩
  · exact (hmissing (EqvOn.symm
      (hmax.eqvOn_of_nonRootReach_tightEdge hA hRc htight hb ha
        hbr hr (Or.inr (Or.inl hbarBA))))).elim
  have hbarXA : barRel (EqvOn A rho.par) x a :=
    tildeOn_flip (tildeOn_mono (fun _ _ h => EqvOn.symm h) hbarAX)
  have hbarXZ : barRel (EqvOn A rho.par) x z :=
    barRel_eqvOn_trans (barRel_eqvOn_trans hbarXA hbar) hbarBZ
  have hres : CT (EqvOn A rho.par) y w :=
    translated_semantic_fork_context (E := EqvOn A rho.par) hno hvar
      (fun _ _ h => EqvOn.symm h)
      (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂)
      (rho.constructorCompatible_eqvOn hA hRc) hrootXY hbarXZ hrootZW
  have hay : EqvOn A rho.par a y :=
    EqvOn.of_reach ha (rho.mem_edge hxy).2
      (hax.toReach.trans (Reach.head hxy (Reach.refl y)))
  have hbw : EqvOn A rho.par b w :=
    EqvOn.of_reach hb (rho.mem_edge hzw).2
      (hbz.toReach.trans (Reach.head hzw (Reach.refl w)))
  refine ⟨x, y, z, w, hax, hxy, hrootXY, hbz, hzw, hrootZW, hbarXZ, hres, ?_⟩
  intro hyw
  exact hmissing (EqvOn.trans (EqvOn.trans hay hyw) (EqvOn.symm hbw))

/-- Every translated missing old pair has a missing old successor inside the
two first-root contracta. The relation is total on missing old pairs and keeps
the starting graph fixed. -/
theorem PGraph.TightEqualityComplete.translated_residualOld_total
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph A (constructorTranslation R)}
    (hmax : rho.TightEqualityComplete) (htight : rho.Tight)
    {p : Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu}
    (hp : rho.MissingOld p) : ∃ q, rho.ResidualOld p q := by
  obtain ⟨hpA, hpB, hpbar, hpne⟩ := hp
  obtain ⟨x, y, z, w, hpx, hxy, hrootXY, hpz, hzw, hrootZW,
      hbarXZ, hct, hneYW⟩ :=
    hmax.translated_missing_barRel_has_root_residual hA hno hvar htight
      hpA hpB hpbar hpne
  obtain ⟨u, v, huy, hvw, hu, hv, huv, hneUV⟩ :=
    CT.exists_missing_barRel_of_constructorClosed hA
      (fun _ _ hx hy hh => hmax.constructorClosed hA
        (constructorRules_constructorTranslation R) htight hx hy hh)
      (rho.mem_edge hxy).2 (rho.mem_edge hzw).2 hct hneYW
  refine ⟨(u, v), ⟨hpA, hpB, hpbar, hpne⟩,
    ⟨hu, hv, huv, hneUV⟩, x, y, z, w, hpx, hxy, hrootXY, hpz, hzw,
    hrootZW, hbarXZ, hct, hneYW, huy, hvw⟩

/-- On the generated finite batch, translated fixed-old residuals form a total
relation. -/
theorem PGraph.TightEqualityComplete.translated_residualBatchEdge_total
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph A (constructorTranslation R)}
    (hmax : rho.TightEqualityComplete) (htight : rho.Tight)
    {p : PGraph.ResidualPair sigma nu} (hp : rho.MissingOld p) :
    ∀ q : rho.ResidualBatchNode p, ∃ r, rho.ResidualBatchEdge p q r := by
  intro q
  have hqMissing : rho.MissingOld q.1 :=
    rho.oldResidualBatch_all_missing hp q.2
  obtain ⟨r, hqr⟩ :=
    hmax.translated_residualOld_total hA hno hvar htight hqMissing
  have hr : r ∈ rho.oldResidualBatch p :=
    rho.oldResidualBatch_closed hp q.2 hqr
  exact ⟨⟨r, hr⟩, hqr⟩

/-- Every translated missing old pair generates a concrete residual cycle in
its finite fixed-old batch. This is the exact finite strongly connected
component that a simultaneous repair must discharge. -/
theorem PGraph.TightEqualityComplete.translated_missingOld_has_residualCycle
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph A (constructorTranslation R)}
    (hmax : rho.TightEqualityComplete) (htight : rho.Tight)
    {p : PGraph.ResidualPair sigma nu} (hp : rho.MissingOld p) :
    rho.HasResidualOldCycle p := by
  classical
  let q : rho.ResidualBatchNode p := ⟨p, rho.oldResidualBatch_seed p⟩
  letI : Fintype (rho.ResidualBatchNode p) :=
    inferInstanceAs (Fintype ↑(rho.oldResidualBatch p))
  letI : Nonempty (rho.ResidualBatchNode p) := ⟨q⟩
  exact finite_total_relation_has_transGen_cycle
    (hmax.translated_residualBatchEdge_total hA hno hvar htight hp)

/-- A finite coalgebra has an equality-complete graph representing every
translated root step, for arbitrary symbol and variable types. -/
theorem exists_equalityComplete_rootStepsRepresented_constructorTranslation
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) :
    ∃ rho : PGraph A (constructorTranslation R), rho.EqualityComplete ∧
      RootStepsRepresented A (constructorTranslation R) rho :=
  exists_equalityComplete_rootStepsRepresented hA
    (constructorRules_constructorTranslation R)
    (fun {_ _ _} h₁ h₂ => constructorTranslation_deterministic hno hvar _ _ _ h₁ h₂)

/-- A maximal tight graph closes the base and constructor cases; every missed
translated fork therefore has a destructor-only residual. -/
theorem PGraph.TightEqualityComplete.translated_missing_fork_destructor
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph A (constructorTranslation R)}
    (hmax : rho.TightEqualityComplete) (htight : rho.Tight)
    {a b c d : Term (sigma ⊕ sigma) nu}
    (hb : b ∈ A) (hd : d ∈ A)
    (hab : rootStep (constructorTranslation R) a b)
    (hac : barRel (EqvOn A rho.par) a c)
    (hcd : rootStep (constructorTranslation R) c d)
    (hmissing : ¬ EqvOn A rho.par b d) :
    barRel (DCT (EqvOn A rho.par)) b d := by
  rcases translated_semantic_fork_destructor_residual (E := EqvOn A rho.par)
    hno hvar (fun _ _ h => EqvOn.symm h)
    (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂)
    (rho.constructorCompatible_eqvOn hA (constructorRules_constructorTranslation R))
    hab hac hcd with he | hbar | hhat
  · exact (hmissing he).elim
  · exact hbar
  · exact (hmissing (hmax.constructorClosed hA
      (constructorRules_constructorTranslation R) htight hb hd (Or.inr hhat))).elim

/-- A constructor-topped output forces represented equality in every maximal
tight graph of the translation, including finite variable types. -/
theorem PGraph.TightEqualityComplete.translated_fork_constructor_eqv
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph A (constructorTranslation R)}
    (hmax : rho.TightEqualityComplete) (htight : rho.Tight)
    {a b c d : Term (sigma ⊕ sigma) nu}
    (hb : b ∈ A) (hd : d ∈ A)
    (hab : rootStep (constructorTranslation R) a b)
    (hac : barRel (EqvOn A rho.par) a c)
    (hcd : rootStep (constructorTranslation R) c d)
    (hcon : ConTopped b ∨ ConTopped d) : EqvOn A rho.par b d := by
  by_contra hmissing
  obtain ⟨f, xs, ys, ⟨g, rfl⟩, rfl, rfl, _⟩ :=
    hmax.translated_missing_fork_destructor hA hno hvar htight hb hd hab hac hcd hmissing
  exact hcon.elim (not_conTopped_destructor xs) (not_conTopped_destructor ys)

/-- In a finite proof graph, the translated residual is already represented
or is one old-grey edge. Recursive context closure is absent from this output. -/
theorem PGraph.translated_semantic_fork_eqv_or_grey
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    (rho : PGraph A (constructorTranslation R))
    {a b c d : Term (sigma ⊕ sigma) nu}
    (hb : b ∈ A) (hd : d ∈ A)
    (hab : rootStep (constructorTranslation R) a b)
    (hac : barRel (EqvOn A rho.par) a c)
    (hcd : rootStep (constructorTranslation R) c d) :
    EqvOn A rho.par b d ∨ Grey A (constructorTranslation R) (EqvOn A rho.par) b d := by
  rcases translated_semantic_fork_residual (E := EqvOn A rho.par) hno hvar
      (fun _ _ h => EqvOn.symm h) (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂)
      (rho.constructorCompatible_eqvOn hA (constructorRules_constructorTranslation R))
      hab hac hcd with hE | hbar | hhat
  · exact Or.inl hE
  · obtain ⟨f, xs, ys, hdes, rfl, rfl, hargs⟩ := hbar
    apply Or.inr
    apply Or.inr
    apply Or.inl
    refine ⟨f, xs, ys, hdes, rfl, rfl, ?_⟩
    exact forall₂_compose_of_mem hargs
      (forall₂_self (r := fun (p q : Term (sigma ⊕ sigma) nu) => p = q)
        (fun _ => rfl) ys)
      (fun p hp q hq r _ hpq hqr => by
        subst r
        exact CT.downOn_of_sound_base hA (fun h => rho.sub h)
          (hA.arg hb hp) (hA.arg hd hq) hpq)
  · exact Or.inr (Or.inr (Or.inr (Or.inr hhat)))

/-! ## Initial attachments of one new term -/

/-- A destructor class containing a constructor term has an actual first root
contraction on its old parent path. -/
theorem PGraph.Tight.first_root_of_eqv_constructor
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {rho : PGraph B R} (htight : rho.Tight)
    {x c : Term (sigma ⊕ sigma) nu}
    (hshape : ∃ d args, x = .app (.inr d) args)
    (hxc : EqvOn B rho.par x c) (hc : ConTopped c) :
    ∃ y z, TightNonRootReach rho x y ∧ rho.par y = some z ∧
      rootStep R y z ∧ barRel (EqvOn B rho.par) x y ∧
      EqvOn B rho.par x z := by
  rcases (rho.normalRoot_spec x).1.tightNonRoot_or_firstRoot with hfree |
      ⟨y, z, hprefix, hyz, hroot⟩
  · have hbar := hfree.barRel_eqvOn hB htight hxc.1 hshape
    have hnormal := (rho.eqvOn_iff_normalRoot_eq hxc.1 hxc.2.1).mp hxc
    have hcRoot : ConTopped (rho.normalRoot x) := by
      rw [hnormal]
      exact conTopped_of_reach hR (fun h => rho.grey h)
        (rho.normalRoot_spec c).1 hc
    obtain ⟨f, xs, ys, ⟨d, rfl⟩, _, hr, _⟩ := hbar
    rw [hr] at hcRoot
    exact (not_conTopped_destructor ys hcRoot).elim
  · exact ⟨y, z, hprefix, hyz, hroot,
      hprefix.barRel_eqvOn hB htight hxc.1 hshape,
      EqvOn.of_reach hxc.1 (rho.mem_edge hyz).2
        (hprefix.toReach.trans (Reach.head hyz (Reach.refl z)))⟩

/-- An incoming root from a constructor-bearing old class supplies an old
context representative of its target. -/
theorem PGraph.Tight.incoming_constructor_class_representative
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph B (constructorTranslation R)} (htight : rho.Tight)
    {x a c : Term (sigma ⊕ sigma) nu}
    (hroot : rootStep (constructorTranslation R) x a)
    (hxc : EqvOn B rho.par x c) (hc : ConTopped c) :
    ∃ r, r ∈ B ∧ EqvOn B rho.par x r ∧ CT (EqvOn B rho.par) a r := by
  obtain ⟨y, r, _, hyr, hyrRoot, hbar, hxr⟩ :=
    htight.first_root_of_eqv_constructor hB (constructorRules_constructorTranslation R)
      (rootStep_source_destructor (constructorRules_constructorTranslation R) hroot) hxc hc
  refine ⟨r, (rho.mem_edge hyr).2, hxr, ?_⟩
  exact translated_semantic_fork_context (E := EqvOn B rho.par) hno hvar
    (fun _ _ h => EqvOn.symm h) (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂)
    (rho.constructorCompatible_eqvOn hB (constructorRules_constructorTranslation R))
    hroot hbar hyrRoot

/-- An outgoing root agrees with any constructor-bearing old representative
of the new application's argument tuple. -/
theorem PGraph.Tight.new_root_eq_old_constructor_class
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph B (constructorTranslation R)} (htight : rho.Tight)
    (hcl : SigmaClosedOn B (EqvOn B rho.par))
    {f : sigma ⊕ sigma} {xs : List (Term (sigma ⊕ sigma) nu)}
    (hnew : Term.app f xs ∉ B) (hxs : ∀ x ∈ xs, x ∈ B)
    {b r c : Term (sigma ⊕ sigma) nu} (hb : b ∈ B)
    (hroot : rootStep (constructorTranslation R) (.app f xs) b)
    (hrep : CT (EqvOn B rho.par) (.app f xs) r)
    (hrc : EqvOn B rho.par r c) (hc : ConTopped c) : EqvOn B rho.par b r := by
  have htilde := (CT.one_new_app_iff hB hcl (fun h => h.mem)
    hnew hxs hrc.1).mp hrep
  have hbar : barRel (EqvOn B rho.par) (.app f xs) r := by
    rcases hatRel_or_barRel_of_tildeAll htilde with hh | hd
    · obtain ⟨d, args, ha⟩ :=
        rootStep_source_destructor (constructorRules_constructorTranslation R) hroot
      have hcon := ConTopped.of_hatEq (Or.inr hh)
      rw [ha] at hcon
      exact (not_conTopped_destructor args hcon).elim
    · exact hd
  have hrShape : ∃ d args, r = .app (.inr d) args := by
    obtain ⟨g, us, ys, ⟨d, rfl⟩, _, hy, _⟩ := hbar
    exact ⟨d, ys, hy⟩
  obtain ⟨y, z, _, hyz, hyzRoot, hry, hrz⟩ :=
    htight.first_root_of_eqv_constructor hB (constructorRules_constructorTranslation R)
      hrShape hrc hc
  have hbz : CT (EqvOn B rho.par) b z :=
    translated_semantic_fork_context (E := EqvOn B rho.par) hno hvar
      (fun _ _ h => EqvOn.symm h) (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂)
      (rho.constructorCompatible_eqvOn hB (constructorRules_constructorTranslation R))
      hroot (barRel_eqvOn_trans hbar hry) hyzRoot
  exact EqvOn.trans (hcl.eq_of_CT hB hb (rho.mem_edge hyz).2 hbz) (EqvOn.symm hrz)

/-- Initial edges connect the new term to old terms by actual root steps or
one application congruence over the old graph equality. -/
def PGraph.InitialAttachment
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) (a b : Term (sigma ⊕ sigma) nu) : Prop :=
  b ∈ B ∧ (rootStep R a b ∨ rootStep R b a ∨ tildeAll (EqvOn B rho.par) a b)

/-- The attached set contains the new term and the whole old class of each
initial endpoint. -/
def PGraph.InitiallyAttached
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) (a x : Term (sigma ⊕ sigma) nu) : Prop :=
  x = a ∨ ∃ b, rho.InitialAttachment a b ∧ EqvOn B rho.par x b

/-- Initial attachment merges exactly the attached old classes and the new
term; all other old classes retain their previous equality. -/
def PGraph.InitialMerge
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) (a : Term (sigma ⊕ sigma) nu) : CRel sigma nu :=
  fun x y => EqvOn B rho.par x y ∨ rho.InitiallyAttached a x ∧ rho.InitiallyAttached a y

theorem PGraph.initiallyAttached_of_eqv
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) {a x y : Term (sigma ⊕ sigma) nu} (hnew : a ∉ B)
    (hxy : EqvOn B rho.par x y) (hy : rho.InitiallyAttached a y) :
    rho.InitiallyAttached a x := by
  rcases hy with rfl | ⟨b, hb, hyb⟩
  · exact (hnew hxy.2.1).elim
  · exact Or.inr ⟨b, hb, EqvOn.trans hxy hyb⟩

theorem PGraph.initialMerge_mem
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) {a x y : Term (sigma ⊕ sigma) nu}
    (h : rho.InitialMerge a x y) : x ∈ a :: B ∧ y ∈ a :: B := by
  have mem : ∀ {z}, rho.InitiallyAttached a z → z ∈ a :: B := by
    rintro z (rfl | ⟨b, _, hzb⟩)
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hzb.1
  rcases h with h | ⟨hx, hy⟩
  · exact ⟨List.mem_cons_of_mem _ h.1, List.mem_cons_of_mem _ h.2.1⟩
  · exact ⟨mem hx, mem hy⟩

theorem PGraph.initialMerge_refl
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) {a x : Term (sigma ⊕ sigma) nu} (hx : x ∈ a :: B) :
    rho.InitialMerge a x x := by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Or.inr ⟨Or.inl rfl, Or.inl rfl⟩
  · exact Or.inl (EqvOn.refl hx)

theorem PGraph.initialMerge_symm
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) {a x y : Term (sigma ⊕ sigma) nu}
    (h : rho.InitialMerge a x y) : rho.InitialMerge a y x := by
  rcases h with h | ⟨hx, hy⟩
  · exact Or.inl (EqvOn.symm h)
  · exact Or.inr ⟨hy, hx⟩

theorem PGraph.initialMerge_trans
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) {a x y z : Term (sigma ⊕ sigma) nu} (hnew : a ∉ B)
    (hxy : rho.InitialMerge a x y) (hyz : rho.InitialMerge a y z) :
    rho.InitialMerge a x z := by
  rcases hxy with hxy | ⟨hx, hy⟩
  · rcases hyz with hyz | ⟨hy, hz⟩
    · exact Or.inl (EqvOn.trans hxy hyz)
    · exact Or.inr ⟨rho.initiallyAttached_of_eqv hnew hxy hy, hz⟩
  · rcases hyz with hyz | ⟨_, hz⟩
    · exact Or.inr ⟨hx, rho.initiallyAttached_of_eqv hnew (EqvOn.symm hyz) hy⟩
    · exact Or.inr ⟨hx, hz⟩

theorem PGraph.initialMerge_attachment
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) {a b : Term (sigma ⊕ sigma) nu}
    (h : rho.InitialAttachment a b) : rho.InitialMerge a a b :=
  Or.inr ⟨Or.inl rfl, Or.inr ⟨b, h, EqvOn.refl h.1⟩⟩

/-- This is the least equivalence on the enlarged carrier containing the old
equality and the declared initial attachments. -/
theorem PGraph.initialMerge_least
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) {a : Term (sigma ⊕ sigma) nu} {S : CRel sigma nu}
    (hsymm : ∀ x y, S x y → S y x)
    (htrans : ∀ x y z, S x y → S y z → S x z)
    (hdiag : S a a) (hold : ∀ {x y}, EqvOn B rho.par x y → S x y)
    (hattach : ∀ b, rho.InitialAttachment a b → S a b)
    {x y : Term (sigma ⊕ sigma) nu} (h : rho.InitialMerge a x y) : S x y := by
  have to_new : ∀ {z}, rho.InitiallyAttached a z → S z a := by
    rintro z (rfl | ⟨b, hb, hzb⟩)
    · exact hdiag
    · exact htrans z b a (hold hzb) (hsymm a b (hattach b hb))
  rcases h with h | ⟨hx, hy⟩
  · exact hold h
  · exact htrans x a y (to_new hx) (hsymm y a (to_new hy))

/-- A constructor-bearing initial class contains either the outgoing root
target or an old context representative of the new term. -/
theorem PGraph.Tight.initiallyAttached_constructor_cases
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph B (constructorTranslation R)} (htight : rho.Tight)
    {a c : Term (sigma ⊕ sigma) nu} (hnew : a ∉ B) (hcB : c ∈ B)
    (hc : ConTopped c) (hattach : rho.InitiallyAttached a c) :
    (∃ b, rootStep (constructorTranslation R) a b ∧ EqvOn B rho.par b c) ∨
      ∃ r, r ∈ B ∧ CT (EqvOn B rho.par) a r ∧ EqvOn B rho.par r c := by
  rcases hattach with rfl | ⟨b, ⟨hb, hattach⟩, hcb⟩
  · exact (hnew hcB).elim
  · rcases hattach with hout | hin | hctx
    · exact Or.inl ⟨b, hout, EqvOn.symm hcb⟩
    · obtain ⟨r, hr, hbr, har⟩ :=
        htight.incoming_constructor_class_representative hB hno hvar hin (EqvOn.symm hcb) hc
      exact Or.inr ⟨r, hr, har, EqvOn.trans (EqvOn.symm hbr) (EqvOn.symm hcb)⟩
    · exact Or.inr ⟨b, hb,
        CT.sigmaClosed _ _ (tildeOn_mono (fun _ _ => CT.base) hctx), EqvOn.symm hcb⟩

/-- Initial attachment cannot identify two previously distinct old constructor
classes, for arbitrary source signatures and variable types. -/
theorem PGraph.Tight.initiallyAttached_constructors_eq
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph B (constructorTranslation R)} (htight : rho.Tight)
    (hcl : SigmaClosedOn B (EqvOn B rho.par))
    {f : sigma ⊕ sigma} {xs : List (Term (sigma ⊕ sigma) nu)}
    (hnew : Term.app f xs ∉ B) (hxs : ∀ x ∈ xs, x ∈ B)
    {c d : Term (sigma ⊕ sigma) nu} (hcB : c ∈ B) (hdB : d ∈ B)
    (hc : ConTopped c) (hd : ConTopped d)
    (hac : rho.InitiallyAttached (.app f xs) c)
    (had : rho.InitiallyAttached (.app f xs) d) : EqvOn B rho.par c d := by
  rcases htight.initiallyAttached_constructor_cases hB hno hvar hnew hcB hc hac with
      ⟨b, hab, hbc⟩ | ⟨r, hr, har, hrc⟩
  · rcases htight.initiallyAttached_constructor_cases hB hno hvar hnew hdB hd had with
        ⟨b', hab', hbd⟩ | ⟨s, hs, has, hsd⟩
    · have hbb : b = b' := constructorTranslation_deterministic hno hvar _ _ _ hab hab'
      subst b'
      exact EqvOn.trans (EqvOn.symm hbc) hbd
    · have hbs := htight.new_root_eq_old_constructor_class hB hno hvar hcl
        hnew hxs hbc.1 hab has hsd hd
      exact EqvOn.trans (EqvOn.trans (EqvOn.symm hbc) hbs) hsd
  · rcases htight.initiallyAttached_constructor_cases hB hno hvar hnew hdB hd had with
        ⟨b, hab, hbd⟩ | ⟨s, hs, has, hsd⟩
    · have hbr := htight.new_root_eq_old_constructor_class hB hno hvar hcl
        hnew hxs hbd.1 hab har hrc hc
      exact EqvOn.trans (EqvOn.trans (EqvOn.symm hrc) (EqvOn.symm hbr)) hbd
    · have hrs := CT.one_new_representatives_eq hB hcl (fun h => h.mem)
        (fun _ _ h => EqvOn.symm h) (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂)
        hnew hxs hr hs har has
      exact EqvOn.trans (EqvOn.trans (EqvOn.symm hrc) hrs) hsd

theorem PGraph.Tight.initialMerge_old_constructor_iff
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph B (constructorTranslation R)} (htight : rho.Tight)
    (hcl : SigmaClosedOn B (EqvOn B rho.par))
    {f : sigma ⊕ sigma} {xs : List (Term (sigma ⊕ sigma) nu)}
    (hnew : Term.app f xs ∉ B) (hxs : ∀ x ∈ xs, x ∈ B)
    {c d : Term (sigma ⊕ sigma) nu} (hcB : c ∈ B) (hdB : d ∈ B)
    (hc : ConTopped c) (hd : ConTopped d) :
    rho.InitialMerge (.app f xs) c d ↔ EqvOn B rho.par c d := by
  constructor
  · rintro (h | ⟨hac, had⟩)
    · exact h
    · exact htight.initiallyAttached_constructors_eq hB hno hvar hcl
        hnew hxs hcB hdB hc hd hac had
  · exact Or.inl

/-- A new constructor term is context-related to every old constructor in its
initial class; the conclusion is derived from the actual attachment cases. -/
theorem PGraph.Tight.initialMerge_new_constructor_context
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph B (constructorTranslation R)} (htight : rho.Tight)
    (hcl : SigmaClosedOn B (EqvOn B rho.par))
    {f : sigma} {xs : List (Term (sigma ⊕ sigma) nu)}
    (hnew : Term.app (.inl f) xs ∉ B) (hxs : ∀ x ∈ xs, x ∈ B)
    {c : Term (sigma ⊕ sigma) nu} (hcB : c ∈ B) (hc : ConTopped c)
    (hmerge : rho.InitialMerge (.app (.inl f) xs) (.app (.inl f) xs) c) :
    CT (EqvOn B rho.par) (.app (.inl f) xs) c := by
  rcases hmerge with h | ⟨_, hattach⟩
  · exact (hnew h.1).elim
  · rcases htight.initiallyAttached_constructor_cases hB hno hvar hnew hcB hc hattach with
        ⟨b, hab, _⟩ | ⟨r, hr, har, hrc⟩
    · obtain ⟨d, args, ha⟩ :=
        rootStep_source_destructor (constructorRules_constructorTranslation R) hab
      have hbad := Term.app.inj ha
      cases hbad.1
    · have htilde := (CT.one_new_app_iff hB hcl (fun h => h.mem)
        hnew hxs hr).mp har
      obtain ⟨g, us, ys, _, ha, rfl, hargs⟩ := htilde
      obtain ⟨rfl, rfl⟩ := Term.app.inj ha
      have hhat := rho.constructorCompatible hB (constructorRules_constructorTranslation R)
        (ConTopped.app f ys) hc hrc
      have hjoined : hatEq (EqvOn B rho.par) (.app (.inl f) xs) c :=
        hatEq.trans (fun x y z (h₁ : EqvOn B rho.par x y)
          (h₂ : EqvOn B rho.par y z) => h₁.trans h₂)
          (Or.inr ⟨.inl f, xs, ys, ⟨f, rfl⟩, rfl, rfl, hargs⟩) hhat
      rcases hjoined with ⟨z, hz, _⟩ | hjoined
      · cases hz
      · exact CT.sigmaClosed _ _
          (tildeAll_of_hatRel (tildeOn_mono (fun _ _ => CT.base) hjoined))

/-- Every constructor equality produced by the initial merger has an actual
finite invariant derivation on the enlarged carrier. -/
theorem PGraph.Tight.initialMerge_constructor_sound
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph B (constructorTranslation R)} (htight : rho.Tight)
    (hcl : SigmaClosedOn B (EqvOn B rho.par))
    {f : sigma ⊕ sigma} {xs : List (Term (sigma ⊕ sigma) nu)}
    (hnew : Term.app f xs ∉ B) (hxs : ∀ x ∈ xs, x ∈ B)
    {x y : Term (sigma ⊕ sigma) nu} (hx : ConTopped x) (hy : ConTopped y)
    (hmerge : rho.InitialMerge (.app f xs) x y) :
    DownOn (.app f xs :: B) (constructorTranslation R) x y := by
  have hA : Coalgebra (.app f xs :: B) := by
    intro t ht s hst
    rcases List.mem_cons.mp ht with rfl | ht
    · cases hst with
      | refl => exact List.mem_cons_self
      | arg hp hsp => exact List.mem_cons_of_mem _ (hB _ (hxs _ hp) _ hsp)
    · exact List.mem_cons_of_mem _ (hB t ht s hst)
  have hnewSound : ∀ {c}, c ∈ B → ConTopped c → ConTopped (.app f xs) →
      rho.InitialMerge (.app f xs) (.app f xs) c →
        DownOn (.app f xs :: B) (constructorTranslation R) (.app f xs) c := by
    intro c hcB hc ha hac
    cases f with
    | inl d =>
        apply CT.downOn_of_sound_base hA
          (fun h => (rho.sub h).mono (fun _ hm => List.mem_cons_of_mem _ hm))
          List.mem_cons_self (List.mem_cons_of_mem _ hcB)
        exact htight.initialMerge_new_constructor_context hB hno hvar hcl hnew hxs hcB hc hac
    | inr d => exact (not_conTopped_destructor xs ha).elim
  have hmem := rho.initialMerge_mem hmerge
  rcases List.mem_cons.mp hmem.1 with rfl | hxB
  · rcases List.mem_cons.mp hmem.2 with rfl | hyB
    · exact DownOn.refl List.mem_cons_self
    · exact hnewSound hyB hy hx hmerge
  · rcases List.mem_cons.mp hmem.2 with rfl | hyB
    · exact DownOn.symm (hnewSound hxB hx hy (rho.initialMerge_symm hmerge))
    · exact (rho.sub ((htight.initialMerge_old_constructor_iff hB hno hvar hcl
        hnew hxs hxB hyB hx hy).mp hmerge)).mono
        (fun _ hm => List.mem_cons_of_mem _ hm)

/-! ## Directed paths and class-constant sinks -/

namespace ClassSink

universe w

variable {α : Type w}

/-- A finite path in an arbitrary directed relation. -/
inductive Path (L : α → α → Prop) : α → α → Prop where
  | refl (x) : Path L x x
  | head {x y z} : L x y → Path L y z → Path L x z

theorem Path.trans {L : α → α → Prop} {x y z : α}
    (hxy : Path L x y) (hyz : Path L y z) : Path L x z := by
  induction hxy with
  | refl => exact hyz
  | head h _ ih => exact Path.head h (ih hyz)

theorem Path.single {L : α → α → Prop} {x y : α} (h : L x y) : Path L x y :=
  Path.head h (Path.refl y)

/-- A directed path with its number of edges. -/
inductive PathN (L : α → α → Prop) : Nat → α → α → Prop where
  | refl (x) : PathN L 0 x x
  | head {n x y z} : L x y → PathN L n y z → PathN L (n + 1) x z

theorem Path.toPathN {L : α → α → Prop} {x y : α} (h : Path L x y) :
    ∃ n, PathN L n x y := by
  induction h with
  | refl x => exact ⟨0, PathN.refl x⟩
  | head h _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, PathN.head h hn⟩

/-- Shortest paths to a class-constant sink define a terminating parent
function with exactly the given equivalence, on any carrier. -/
theorem exists_parent
    (A : α → Prop) (E L : α → α → Prop)
    (hmem : ∀ {x y}, E x y → A x ∧ A y)
    (hrefl : ∀ x, A x → E x x)
    (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hedge : ∀ {x y}, L x y → E x y)
    (sink : α → α) (hsink : ∀ {x y}, E x y → sink x = sink y)
    (hroute : ∀ x, A x → Path L x (sink x)) :
    ∃ g : α → Option α,
      WellFounded (fun y x => g x = some y) ∧
      (∀ {x y}, g x = some y → L x y) ∧
      (∀ x, A x → ParentReplacement.Path g x (sink x)) ∧
      (∀ x y, E x y ↔ A x ∧ A y ∧
        ∃ z, ParentReplacement.Path g x z ∧ ParentReplacement.Path g y z) := by
  classical
  let dist : α → Nat := fun x => if hx : A x then Nat.find (hroute x hx).toPathN else 0
  have spec : ∀ x (hx : A x), PathN L (dist x) x (sink x) := by
    intro x hx
    simpa only [dist, dif_pos hx] using Nat.find_spec (hroute x hx).toPathN
  have path_zero : ∀ {x y}, PathN L 0 x y → x = y := by
    intro x y hp
    cases hp
    rfl
  have zero : ∀ x (hx : A x), dist x = 0 → x = sink x := by
    intro x hx hz
    have hp := spec x hx
    rw [hz] at hp
    exact path_zero hp
  have step : ∀ x, A x → x ≠ sink x → ∃ y, L x y ∧ dist y < dist x := by
    intro x hx hne
    have hpos : 0 < dist x := Nat.pos_of_ne_zero (fun hz => hne (zero x hx hz))
    obtain ⟨n, hn⟩ : ∃ n, dist x = n + 1 := ⟨dist x - 1, by omega⟩
    have hp := spec x hx
    rw [hn] at hp
    cases hp with
    | @head _ _ y _ hxy htail =>
        have hy : A y := (hmem (hedge hxy)).2
        have hs := hsink (hedge hxy)
        have hcand : PathN L n y (sink y) := by rw [← hs]; exact htail
        have hle : dist y ≤ n := by
          simp only [dist, dif_pos hy]
          exact Nat.find_min' (hroute y hy).toPathN hcand
        exact ⟨y, hxy, by omega⟩
  let next (x : α) (hx : A x) (hne : x ≠ sink x) : α :=
    Classical.choose (step x hx hne)
  have next_spec (x : α) (hx : A x) (hne : x ≠ sink x) :
      L x (next x hx hne) ∧ dist (next x hx hne) < dist x :=
    Classical.choose_spec (step x hx hne)
  let g : α → Option α := fun x =>
    if hx : A x then if hne : x = sink x then none else some (next x hx hne) else none
  have edge : ∀ {x y}, g x = some y → L x y ∧ dist y < dist x := by
    intro x y h
    dsimp only [g] at h
    split at h <;> rename_i hx
    · split at h <;> rename_i hne
      · cases h
      · have heq := Option.some.inj h
        rw [← heq]
        exact next_spec x hx hne
    · cases h
  have wf : WellFounded (fun y x => g x = some y) :=
    Subrelation.wf (fun {_ _} h => (edge h).2)
      (InvImage.wf (f := dist) Nat.lt_wfRel.wf)
  have reach : ∀ x, A x → ParentReplacement.Path g x (sink x) := by
    intro x
    induction x using wf.induction with
    | _ x ih =>
        intro hx
        by_cases heq : x = sink x
        · rw [← heq]
          exact ParentReplacement.Path.refl x
        · have hp : g x = some (next x hx heq) := by simp only [g, dif_pos hx, dif_neg heq]
          have hxy := (next_spec x hx heq).1
          have hy := (hmem (hedge hxy)).2
          refine ParentReplacement.Path.head hp ?_
          rw [hsink (hedge hxy)]
          exact ih _ hp hy
  have path_eq : ∀ {x y}, A x → ParentReplacement.Path g x y → E x y := by
    intro x y hx hp
    revert hx
    induction hp with
    | refl x => intro hx; exact hrefl x hx
    | @head x z y hxz _ ih =>
        intro hx
        have h := hedge (edge hxz).1
        exact htrans _ _ _ h (ih (hmem h).2)
  refine ⟨g, wf, fun h => (edge h).1, reach, ?_⟩
  intro x y
  constructor
  · intro h
    refine ⟨(hmem h).1, (hmem h).2, sink x, reach x (hmem h).1, ?_⟩
    rw [hsink h]
    exact reach y (hmem h).2
  · rintro ⟨hx, hy, z, hxz, hyz⟩
    exact htrans _ _ _ (path_eq hx hxz) (hsymm _ _ (path_eq hy hyz))

end ClassSink

/-- The directed edges used for initial insertion. Only old non-root edges
may be reversed; every root attachment retains its rewrite direction. -/
inductive PGraph.InitialEdge
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) (a : Term (sigma ⊕ sigma) nu) : CRel sigma nu where
  | old {x y} : rho.par x = some y → InitialEdge rho a x y
  | reverse {x y} : rho.par y = some x → ¬ rootStep R y x → InitialEdge rho a x y
  | out {y} : y ∈ B → rootStep R a y → InitialEdge rho a a y
  | into {x} : x ∈ B → rootStep R x a → InitialEdge rho a x a
  | contextOut {y} : y ∈ B → tildeAll (EqvOn B rho.par) a y → InitialEdge rho a a y
  | contextInto {x} : x ∈ B → tildeAll (EqvOn B rho.par) a x → InitialEdge rho a x a

theorem PGraph.InitialEdge.initialMerge
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph B R} {a x y : Term (sigma ⊕ sigma) nu}
    (h : rho.InitialEdge a x y) : rho.InitialMerge a x y := by
  cases h with
  | old h => exact Or.inl (EqvOn.of_reach (rho.mem_edge h).1 (rho.mem_edge h).2
      (Reach.head h (Reach.refl _)))
  | reverse h _ => exact Or.inl (EqvOn.symm (EqvOn.of_reach
      (rho.mem_edge h).1 (rho.mem_edge h).2 (Reach.head h (Reach.refl _))))
  | out hy h => exact rho.initialMerge_attachment ⟨hy, Or.inl h⟩
  | into hx h =>
      exact rho.initialMerge_symm (rho.initialMerge_attachment ⟨hx, Or.inr (Or.inl h)⟩)
  | contextOut hy h => exact rho.initialMerge_attachment ⟨hy, Or.inr (Or.inr h)⟩
  | contextInto hx h =>
      exact rho.initialMerge_symm (rho.initialMerge_attachment ⟨hx, Or.inr (Or.inr h)⟩)

theorem PGraph.InitialEdge.tightOld
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph B R} (ht : rho.Tight) {a x y : Term (sigma ⊕ sigma) nu}
    (h : rho.InitialEdge a x y) : TightEdge R (EqvOn B rho.par) x y := by
  have context : ∀ {p q}, tildeAll (EqvOn B rho.par) p q →
      TightEdge R (EqvOn B rho.par) p q := by
    intro p q hpq
    rcases hatRel_or_barRel_of_tildeAll hpq with hh | hb
    · exact Or.inr (Or.inr (Or.inr hh))
    · exact Or.inr (Or.inl hb)
  cases h with
  | old h => exact ht h
  | reverse h hn => exact (ht h).symm_of_not_root (fun _ _ h => EqvOn.symm h) hn
  | out _ h => exact Or.inl h
  | into _ h => exact Or.inl h
  | contextOut _ h => exact context h
  | contextInto _ h =>
      exact context (tildeOn_flip (tildeOn_mono (fun _ _ h => EqvOn.symm h) h))

theorem PGraph.initialPath_of_reach
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) (a : Term (sigma ⊕ sigma) nu)
    {x y : Term (sigma ⊕ sigma) nu} (h : Reach rho.par x y) :
    ClassSink.Path (rho.InitialEdge a) x y := by
  induction h with
  | refl => exact ClassSink.Path.refl _
  | head h _ ih => exact ClassSink.Path.head (.old h) ih

theorem PGraph.initialPath_reverse_nonRoot
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) (a : Term (sigma ⊕ sigma) nu)
    {x y : Term (sigma ⊕ sigma) nu} (h : TightNonRootReach rho x y) :
    ClassSink.Path (rho.InitialEdge a) y x := by
  induction h with
  | refl => exact ClassSink.Path.refl _
  | head h hn _ ih => exact ih.trans (ClassSink.Path.single (.reverse h hn))

theorem PGraph.initialPath_class_to_normalRoot
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) (a : Term (sigma ⊕ sigma) nu)
    {x y : Term (sigma ⊕ sigma) nu} (h : EqvOn B rho.par x y) :
    ClassSink.Path (rho.InitialEdge a) x (rho.normalRoot y) := by
  rw [← (rho.eqvOn_iff_normalRoot_eq h.1 h.2.1).mp h]
  exact rho.initialPath_of_reach a (rho.normalRoot_spec x).1

theorem PGraph.initialPath_class_via_nonRoot
    {B : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) (a : Term (sigma ⊕ sigma) nu)
    {x y : Term (sigma ⊕ sigma) nu} (h : EqvOn B rho.par x y)
    (hf : TightNonRootReach rho y (rho.normalRoot y)) :
    ClassSink.Path (rho.InitialEdge a) x y :=
  (rho.initialPath_class_to_normalRoot a h).trans (rho.initialPath_reverse_nonRoot a hf)

/-- An incoming root either has a reversible old route or supplies an old
context representative in the same old class. -/
theorem PGraph.Tight.incoming_initial_route
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph B (constructorTranslation R)} (ht : rho.Tight)
    {x a : Term (sigma ⊕ sigma) nu} (hx : x ∈ B)
    (hroot : rootStep (constructorTranslation R) x a) :
    TightNonRootReach rho x (rho.normalRoot x) ∨
      ∃ r, r ∈ B ∧ EqvOn B rho.par x r ∧ CT (EqvOn B rho.par) a r := by
  rcases (rho.normalRoot_spec x).1.tightNonRoot_or_firstRoot with hf |
      ⟨y, r, hp, hyr, hrootYR⟩
  · exact Or.inl hf
  · refine Or.inr ⟨r, (rho.mem_edge hyr).2,
      EqvOn.of_reach hx (rho.mem_edge hyr).2
        (hp.toReach.trans (Reach.head hyr (Reach.refl r))), ?_⟩
    exact translated_semantic_fork_context (E := EqvOn B rho.par) hno hvar
      (fun _ _ h => EqvOn.symm h) (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂)
      (rho.constructorCompatible_eqvOn hB (constructorRules_constructorTranslation R))
      hroot (hp.barRel_eqvOn hB ht hx
        (rootStep_source_destructor (constructorRules_constructorTranslation R) hroot)) hrootYR

/-- The route from an old context representative is reversible unless its
class already contains the outgoing contractum. -/
theorem PGraph.Tight.outgoing_context_initial_route
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph B (constructorTranslation R)} (ht : rho.Tight)
    (hcl : SigmaClosedOn B (EqvOn B rho.par))
    {f : sigma ⊕ sigma} {xs : List (Term (sigma ⊕ sigma) nu)}
    (hnew : Term.app f xs ∉ B) (hxs : ∀ x ∈ xs, x ∈ B)
    {b p : Term (sigma ⊕ sigma) nu} (hb : b ∈ B) (hp : p ∈ B)
    (hout : rootStep (constructorTranslation R) (.app f xs) b)
    (hcontext : CT (EqvOn B rho.par) (.app f xs) p) :
    TightNonRootReach rho p (rho.normalRoot p) ∨ EqvOn B rho.par p b := by
  rcases (rho.normalRoot_spec p).1.tightNonRoot_or_firstRoot with hf |
      ⟨y, z, hprefix, hyz, hroot⟩
  · exact Or.inl hf
  · have htilde := (CT.one_new_app_iff hB hcl (fun h => h.mem) hnew hxs hp).mp hcontext
    have hbar : barRel (EqvOn B rho.par) (.app f xs) p := by
      rcases hatRel_or_barRel_of_tildeAll htilde with hhat | hbar
      · obtain ⟨d, args, heq⟩ :=
          rootStep_source_destructor (constructorRules_constructorTranslation R) hout
        have hc := ConTopped.of_hatEq (Or.inr hhat)
        rw [heq] at hc
        exact (not_conTopped_destructor args hc).elim
      · exact hbar
    have hpShape : ∃ d args, p = .app (.inr d) args := by
      obtain ⟨g, us, vs, ⟨d, rfl⟩, _, heq, _⟩ := hbar
      exact ⟨d, vs, heq⟩
    have hbz : CT (EqvOn B rho.par) b z :=
      translated_semantic_fork_context (E := EqvOn B rho.par) hno hvar
        (fun _ _ h => EqvOn.symm h) (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂)
        (rho.constructorCompatible_eqvOn hB (constructorRules_constructorTranslation R))
        hout (barRel_eqvOn_trans hbar (hprefix.barRel_eqvOn hB ht hp hpShape)) hroot
    have hpz := EqvOn.of_reach hp (rho.mem_edge hyz).2
      (hprefix.toReach.trans (Reach.head hyz (Reach.refl z)))
    exact Or.inr (EqvOn.trans hpz (EqvOn.symm
      (hcl.eq_of_CT hB hb (rho.mem_edge hyz).2 hbz)))

/-- Routes from the outgoing and context classes determine a route from
every initially attached node, including incoming-root classes. -/
theorem PGraph.Tight.initiallyAttached_path
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph B (constructorTranslation R)} (ht : rho.Tight)
    {a s : Term (sigma ⊕ sigma) nu}
    (has : ClassSink.Path (rho.InitialEdge a) a s)
    (hout : ∀ b, b ∈ B → rootStep (constructorTranslation R) a b →
      ∀ x, EqvOn B rho.par x b → ClassSink.Path (rho.InitialEdge a) x s)
    (hcontext : ∀ p, p ∈ B → CT (EqvOn B rho.par) a p →
      ∀ x, EqvOn B rho.par x p → ClassSink.Path (rho.InitialEdge a) x s)
    {x : Term (sigma ⊕ sigma) nu} (hx : rho.InitiallyAttached a x) :
    ClassSink.Path (rho.InitialEdge a) x s := by
  rcases hx with rfl | ⟨b, ⟨hb, hattach⟩, hxb⟩
  · exact has
  · rcases hattach with hroot | hroot | hctx
    · exact hout b hb hroot x hxb
    · rcases ht.incoming_initial_route hB hno hvar hb hroot with hf |
        ⟨p, hp, hbp, hap⟩
      · exact (rho.initialPath_class_via_nonRoot a hxb hf).trans
          (ClassSink.Path.head (.into hb hroot) has)
      · exact hcontext p hp hap x (EqvOn.trans hxb hbp)
    · exact hcontext b hb (CT.sigmaClosed _ _
        (tildeOn_mono (fun _ _ => CT.base) hctx)) x hxb

/-- All initially attached nodes reach one sink using actual root edges and
old congruences; no ordering or termination assumption on the TRS is required. -/
theorem PGraph.Tight.exists_initial_app_class_sink
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph B (constructorTranslation R)} (ht : rho.Tight)
    (hcl : SigmaClosedOn B (EqvOn B rho.par))
    {f : sigma ⊕ sigma} {xs : List (Term (sigma ⊕ sigma) nu)}
    (hnew : Term.app f xs ∉ B) (hxs : ∀ x ∈ xs, x ∈ B) :
    ∃ s, s ∈ .app f xs :: B ∧ ∀ x, rho.InitiallyAttached (.app f xs) x →
      ClassSink.Path (rho.InitialEdge (.app f xs)) x s := by
  classical
  by_cases hout : ∃ b ∈ B, rootStep (constructorTranslation R) (.app f xs) b
  · obtain ⟨b, hb, hab⟩ := hout
    have hnewRoute : ClassSink.Path (rho.InitialEdge (.app f xs))
        (.app f xs) (rho.normalRoot b) :=
      ClassSink.Path.head (.out hb hab)
        (rho.initialPath_of_reach _ (rho.normalRoot_spec b).1)
    refine ⟨rho.normalRoot b, List.mem_cons_of_mem _ (rho.normalRoot_mem hb), ?_⟩
    intro x hx
    apply ht.initiallyAttached_path hB hno hvar hnewRoute ?_ ?_ hx
    · intro c _ hac y hyc
      have hcb : c = b := constructorTranslation_deterministic hno hvar _ _ _ hac hab
      subst c
      exact rho.initialPath_class_to_normalRoot _ hyc
    · intro p hp hctx y hyp
      rcases ht.outgoing_context_initial_route hB hno hvar hcl hnew hxs hb hp hab hctx
          with hf | hpb
      · exact (rho.initialPath_class_via_nonRoot _ hyp hf).trans
          (ClassSink.Path.head (.contextInto hp
            ((CT.one_new_app_iff hB hcl (fun h => h.mem) hnew hxs hp).mp hctx)) hnewRoute)
      · exact rho.initialPath_class_to_normalRoot _ (EqvOn.trans hyp hpb)
  · by_cases hcontext : ∃ p ∈ B, CT (EqvOn B rho.par) (.app f xs) p
    · obtain ⟨p, hp, hap⟩ := hcontext
      have hnewRoute : ClassSink.Path (rho.InitialEdge (.app f xs))
          (.app f xs) (rho.normalRoot p) :=
        ClassSink.Path.head (.contextOut hp
          ((CT.one_new_app_iff hB hcl (fun h => h.mem) hnew hxs hp).mp hap))
          (rho.initialPath_of_reach _ (rho.normalRoot_spec p).1)
      refine ⟨rho.normalRoot p, List.mem_cons_of_mem _ (rho.normalRoot_mem hp), ?_⟩
      intro x hx
      apply ht.initiallyAttached_path hB hno hvar hnewRoute ?_ ?_ hx
      · intro b hb hab
        exact (hout ⟨b, hb, hab⟩).elim
      · intro q hq haq y hyq
        have hqp := CT.one_new_representatives_eq hB hcl (fun h => h.mem)
          (fun _ _ h => EqvOn.symm h) (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂)
          hnew hxs hq hp haq hap
        exact rho.initialPath_class_to_normalRoot _ (EqvOn.trans hyq hqp)
    · refine ⟨.app f xs, List.mem_cons_self, ?_⟩
      intro x hx
      apply ht.initiallyAttached_path hB hno hvar (ClassSink.Path.refl _) ?_ ?_ hx
      · intro b hb hab
        exact (hout ⟨b, hb, hab⟩).elim
      · intro p hp hap
        exact (hcontext ⟨p, hp, hap⟩).elim

/-- The initial-class sink construction includes fresh variables as well as
applications, on arbitrary finite term coalgebras. -/
theorem PGraph.Tight.exists_initial_class_sink
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {a : Term (sigma ⊕ sigma) nu} (hA : Coalgebra (a :: B))
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph B (constructorTranslation R)} (ht : rho.Tight)
    (hcl : SigmaClosedOn B (EqvOn B rho.par)) (hnew : a ∉ B) :
    ∃ s, s ∈ a :: B ∧ ∀ x, rho.InitiallyAttached a x →
      ClassSink.Path (rho.InitialEdge a) x s := by
  cases a with
  | app f xs =>
      apply ht.exists_initial_app_class_sink hB hno hvar hcl hnew
      intro x hx
      rcases List.mem_cons.mp
          (hA.arg (f := f) (args := xs) (List.mem_cons_self ..) hx) with heq | hold
      · have hlt := Term.size_lt_of_mem (f := f) hx
        rw [heq] at hlt
        exact (Nat.lt_irrefl _ hlt).elim
      · exact hold
  | var z =>
      refine ⟨.var z, List.mem_cons_self, ?_⟩
      intro x hx
      apply ht.initiallyAttached_path hB hno hvar (ClassSink.Path.refl _) ?_ ?_ hx
      · intro b _ hab
        obtain ⟨d, args, heq⟩ :=
          rootStep_source_destructor (constructorRules_constructorTranslation R) hab
        cases heq
      · intro p _ hp
        exact (hnew (CT.var_left_iff.mp hp).mem.1).elim

/-- Each initial-equivalence class has a directed sink. The merged class
uses the constructed sink; every other class uses its old graph normal root. -/
theorem PGraph.Tight.initial_class_sinks
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {a : Term (sigma ⊕ sigma) nu} (hA : Coalgebra (a :: B))
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph B (constructorTranslation R)} (ht : rho.Tight)
    (hcl : SigmaClosedOn B (EqvOn B rho.par)) (hnew : a ∉ B) :
    ∃ sink : Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu,
      (∀ {x y}, rho.InitialMerge a x y → sink x = sink y) ∧
      (∀ x, x ∈ a :: B → ClassSink.Path (rho.InitialEdge a) x (sink x)) := by
  classical
  obtain ⟨s, _, hs⟩ := ht.exists_initial_class_sink hB hA hno hvar hcl hnew
  let sink := fun x => if rho.InitiallyAttached a x then s else rho.normalRoot x
  refine ⟨sink, ?_, ?_⟩
  · intro x y hxy
    rcases hxy with hold | ⟨hx, hy⟩
    · by_cases hx : rho.InitiallyAttached a x
      · have hy := rho.initiallyAttached_of_eqv hnew (EqvOn.symm hold) hx
        simp only [sink, if_pos hx, if_pos hy]
      · have hy : ¬ rho.InitiallyAttached a y :=
          fun hy => hx (rho.initiallyAttached_of_eqv hnew hold hy)
        simpa only [sink, if_neg hx, if_neg hy] using
          (rho.eqvOn_iff_normalRoot_eq hold.1 hold.2.1).mp hold
    · simp only [sink, if_pos hx, if_pos hy]
  · intro x hx
    by_cases hatt : rho.InitiallyAttached a x
    · simpa only [sink, if_pos hatt] using hs x hatt
    · simpa only [sink, if_neg hatt] using
        rho.initialPath_of_reach a (rho.normalRoot_spec x).1

/-- Insert one fresh term and every incident root or old-context attachment.
The actual terminating proof graph represents exactly the initial merger. -/
theorem PGraph.Tight.exists_initialInsertion
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {a : Term (sigma ⊕ sigma) nu} (hA : Coalgebra (a :: B))
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph B (constructorTranslation R)} (ht : rho.Tight)
    (hcl : SigmaClosedOn B (EqvOn B rho.par)) (hnew : a ∉ B) :
    ∃ beta : PGraph (a :: B) (constructorTranslation R),
      beta.Tight ∧
      (∀ x y, EqvOn (a :: B) beta.par x y ↔ rho.InitialMerge a x y) ∧
      (∀ {x y}, beta.par x = some y → rho.InitialEdge a x y) := by
  obtain ⟨sink, hsink, hroute⟩ := ht.initial_class_sinks hB hA hno hvar hcl hnew
  obtain ⟨g, hgterm, hgedge, _, hgeq⟩ := ClassSink.exists_parent
    (fun x => x ∈ a :: B) (rho.InitialMerge a) (rho.InitialEdge a)
    (fun h => rho.initialMerge_mem h) (fun _ hx => rho.initialMerge_refl hx)
    (fun _ _ h => rho.initialMerge_symm h)
    (fun _ _ _ h₁ h₂ => rho.initialMerge_trans hnew h₁ h₂)
    (fun h => h.initialMerge) sink (fun h => hsink h) hroute
  have heq : ∀ x y, EqvOn (a :: B) g x y ↔ rho.InitialMerge a x y := by
    intro x y
    constructor
    · rintro ⟨hx, hy, z, hxz, hyz⟩
      exact (hgeq x y).mpr ⟨hx, hy, z, hxz.toParentPath, hyz.toParentPath⟩
    · intro h
      obtain ⟨hx, hy, z, hxz, hyz⟩ := (hgeq x y).mp h
      exact ⟨hx, hy, z, hxz.toReach, hyz.toReach⟩
  let alpha := rho.liftCarrier (fun x hx => List.mem_cons_of_mem a hx)
  have hmem : ∀ {x y}, g x = some y → x ∈ a :: B ∧ y ∈ a :: B :=
    fun h => rho.initialMerge_mem (hgedge h).initialMerge
  have hold : ∀ x y, EqvOn B rho.par x y → EqvOn (a :: B) g x y :=
    fun x y h => (heq x y).mpr (Or.inl h)
  have hgreyOld : ∀ {x y}, g x = some y →
      Grey (a :: B) (constructorTranslation R) (EqvOn (a :: B) alpha.par) x y := by
    intro x y h
    apply TightEdge.toGrey alpha
    exact ((hgedge h).tightOld ht).mono (fun _ _ h =>
      (rho.eqvOn_largerCarrier_iff (fun x hx => List.mem_cons_of_mem a hx)).mpr (Or.inr h))
  have halpha : ∀ x y, EqvOn (a :: B) alpha.par x y → EqvOn (a :: B) g x y := by
    intro x y h
    rcases (rho.eqvOn_largerCarrier_iff
      (fun x hx => List.mem_cons_of_mem a hx)).mp h with ⟨rfl, hx⟩ | h
    · exact EqvOn.refl hx
    · exact hold x y h
  let beta : PGraph (a :: B) (constructorTranslation R) :=
    { par := g
      mem_edge := hmem
      term := hgterm
      sub := fun h => (lemma52 hA (constructorRules_constructorTranslation R)
        alpha hgterm hmem hgreyOld h).1
      grey := by
        intro x y h
        rcases hgreyOld h with hroot | hbar | hhat
        · exact Or.inl hroot
        · exact Or.inr (Or.inl hbar)
        · exact Or.inr (Or.inr (hatEq.mono halpha hhat)) }
  exact ⟨beta, fun _ _ h => ((hgedge h).tightOld ht).mono hold, heq, hgedge⟩

/-- Initial merger equality has an actual invariant derivation on the
enlarged coalgebra, including all constructor and destructor endpoint cases. -/
theorem PGraph.Tight.initialMerge_sound
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {a : Term (sigma ⊕ sigma) nu} (hA : Coalgebra (a :: B))
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph B (constructorTranslation R)} (ht : rho.Tight)
    (hcl : SigmaClosedOn B (EqvOn B rho.par)) (hnew : a ∉ B)
    {x y : Term (sigma ⊕ sigma) nu} (hxy : rho.InitialMerge a x y) :
    DownOn (a :: B) (constructorTranslation R) x y := by
  obtain ⟨beta, _, heq, _⟩ := ht.exists_initialInsertion hB hA hno hvar hcl hnew
  exact beta.sub ((heq x y).mpr hxy)

/-- Initial insertion retains every old represented root and includes every
root with the new term as either endpoint. -/
theorem PGraph.initialMerge_represents_roots
    {B : List (Term (sigma ⊕ sigma) nu)} {a : Term (sigma ⊕ sigma) nu}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph B R)
    (hroot : RootStepsRepresented B R rho)
    {x y : Term (sigma ⊕ sigma) nu} (hx : x ∈ a :: B) (hy : y ∈ a :: B)
    (hxy : rootStep R x y) : rho.InitialMerge a x y := by
  rcases List.mem_cons.mp hx with rfl | hxB
  · rcases List.mem_cons.mp hy with rfl | hyB
    · exact rho.initialMerge_refl List.mem_cons_self
    · exact rho.initialMerge_attachment ⟨hyB, Or.inl hxy⟩
  · rcases List.mem_cons.mp hy with rfl | hyB
    · exact rho.initialMerge_symm (rho.initialMerge_attachment ⟨hxB, Or.inr (Or.inl hxy)⟩)
    · exact Or.inl (hroot hxB hyB hxy)

/-- Root representation extends to the larger coalgebra on the constructed
graph, with every old represented equality retained. -/
theorem PGraph.Tight.exists_initialInsertion_roots
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {a : Term (sigma ⊕ sigma) nu} (hA : Coalgebra (a :: B))
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {rho : PGraph B (constructorTranslation R)} (ht : rho.Tight)
    (hcl : SigmaClosedOn B (EqvOn B rho.par)) (hnew : a ∉ B)
    (hroot : RootStepsRepresented B (constructorTranslation R) rho) :
    ∃ beta : PGraph (a :: B) (constructorTranslation R), beta.Tight ∧
      RootStepsRepresented (a :: B) (constructorTranslation R) beta ∧
      (∀ {x y}, EqvOn B rho.par x y → EqvOn (a :: B) beta.par x y) ∧
      (∀ x y, EqvOn (a :: B) beta.par x y ↔ rho.InitialMerge a x y) := by
  obtain ⟨beta, hb, heq, _⟩ := ht.exists_initialInsertion hB hA hno hvar hcl hnew
  refine ⟨beta, hb, ?_, ?_, heq⟩
  · intro x y hx hy hxy
    exact (heq x y).mpr (rho.initialMerge_represents_roots hroot hx hy hxy)
  · intro x y hxy
    exact (heq x y).mpr (Or.inl hxy)

/-! ## Constructor-decomposition closure on arbitrary term carriers -/

/-- The observable constructor shape includes frozen variable identity and
constructor arity; destructor-headed terms have no constructor shape. -/
def constructorShape : Term (sigma ⊕ sigma) nu → Option (nu ⊕ (sigma × Nat))
  | .var x => some (.inl x)
  | .app (.inl f) xs => some (.inr (f, xs.length))
  | .app (.inr _) _ => none

/-- Equivalence closure with repeated constructor-argument decomposition.
The signature, variables, and seed relation can all be infinite. -/
inductive ConstructorEqClosure (S : CRel sigma nu) : CRel sigma nu where
  | seed {a b} : S a b → ConstructorEqClosure S a b
  | refl (a) : ConstructorEqClosure S a a
  | symm {a b} : ConstructorEqClosure S a b → ConstructorEqClosure S b a
  | trans {a b c} : ConstructorEqClosure S a b → ConstructorEqClosure S b c →
      ConstructorEqClosure S a c
  | argument {f g : sigma} {xs ys : List (Term (sigma ⊕ sigma) nu)}
      (h : ConstructorEqClosure S (.app (.inl f) xs) (.app (.inl g) ys))
      (i : Nat) (hx : i < xs.length) (hy : i < ys.length) :
      ConstructorEqClosure S (xs.get ⟨i, hx⟩) (ys.get ⟨i, hy⟩)

/-- A clash records the related terms and their distinct constructor shapes. -/
def ConstructorClash (E : CRel sigma nu) : Prop :=
  ∃ a b, ConTopped a ∧ ConTopped b ∧ E a b ∧ constructorShape a ≠ constructorShape b

theorem ConstructorCompatible.shape_eq {E : CRel sigma nu}
    (hE : ConstructorCompatible E) {a b : Term (sigma ⊕ sigma) nu}
    (ha : ConTopped a) (hb : ConTopped b) (hab : E a b) :
    constructorShape a = constructorShape b := by
  rcases hE a b ha hb hab with ⟨x, rfl, rfl⟩ | ⟨f, xs, ys, rfl, rfl, hargs⟩
  · rfl
  · simp only [constructorShape, hargs.length_eq]

theorem ConstructorCompatible.argument {E : CRel sigma nu}
    (hE : ConstructorCompatible E) {f g : sigma}
    {xs ys : List (Term (sigma ⊕ sigma) nu)}
    (h : E (.app (.inl f) xs) (.app (.inl g) ys))
    (i : Nat) (hx : i < xs.length) (hy : i < ys.length) :
    E (xs.get ⟨i, hx⟩) (ys.get ⟨i, hy⟩) := by
  rcases hE _ _ (ConTopped.app f xs) (ConTopped.app g ys) h with
      ⟨x, heq, _⟩ | ⟨k, us, vs, hx', hy', hargs⟩
  · cases heq
  · rcases Term.app.inj hx' with ⟨_, rfl⟩
    rcases Term.app.inj hy' with ⟨_, rfl⟩
    exact hargs.get hx hy

theorem ConstructorCompatible.no_clash {E : CRel sigma nu}
    (hE : ConstructorCompatible E) : ¬ ConstructorClash E := by
  rintro ⟨a, b, ha, hb, hab, hne⟩
  exact hne (hE.shape_eq ha hb hab)

theorem ConstructorEqClosure.equivalence (S : CRel sigma nu) :
    Equivalence (ConstructorEqClosure S) :=
  ⟨ConstructorEqClosure.refl, fun h => .symm h, fun h₁ h₂ => .trans h₁ h₂⟩

/-- Every compatible equivalence containing the seed contains the constructed
closure, including each equality forced by constructor decomposition. -/
theorem ConstructorEqClosure.least {S E : CRel sigma nu}
    (hEq : Equivalence E) (hE : ConstructorCompatible E)
    (hS : ∀ a b, S a b → E a b)
    {a b : Term (sigma ⊕ sigma) nu} (h : ConstructorEqClosure S a b) : E a b := by
  induction h with
  | seed h => exact hS _ _ h
  | refl a => exact hEq.refl a
  | symm _ ih => exact hEq.symm ih
  | trans _ _ ih₁ ih₂ => exact hEq.trans ih₁ ih₂
  | argument _ i hx hy ih => exact hE.argument ih i hx hy

theorem ConstructorEqClosure.mono {S T : CRel sigma nu}
    (hST : ∀ a b, S a b → T a b)
    {a b : Term (sigma ⊕ sigma) nu} (h : ConstructorEqClosure S a b) :
    ConstructorEqClosure T a b := by
  induction h with
  | seed h => exact .seed (hST _ _ h)
  | refl a => exact .refl a
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | argument _ i hx hy ih => exact .argument ih i hx hy

theorem ConstructorEqClosure.idempotent {S : CRel sigma nu}
    {a b : Term (sigma ⊕ sigma) nu} :
    ConstructorEqClosure (ConstructorEqClosure S) a b ↔ ConstructorEqClosure S a b := by
  constructor
  · intro h
    induction h with
    | seed h => exact h
    | refl a => exact .refl a
    | symm _ ih => exact .symm ih
    | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
    | argument _ i hx hy ih => exact .argument ih i hx hy
  · exact ConstructorEqClosure.seed

/-- Absence of shape clashes proves all constructor compatibility laws of the
constructed relation, rather than assuming a compatible extension. -/
theorem ConstructorEqClosure.compatible_of_no_clash {S : CRel sigma nu}
    (hS : ¬ ConstructorClash (ConstructorEqClosure S)) :
    ConstructorCompatible (ConstructorEqClosure S) := by
  classical
  intro a b ha hb hab
  have hshape : constructorShape a = constructorShape b := by
    by_contra hne
    exact hS ⟨a, b, ha, hb, hab, hne⟩
  rcases ha with ⟨x, rfl⟩ | ⟨f, xs, rfl⟩
  · rcases hb with ⟨y, rfl⟩ | ⟨g, ys, rfl⟩
    · have hxy : x = y := by simpa only [constructorShape, Option.some.injEq,
        Sum.inl.injEq] using hshape
      subst y
      exact Or.inl ⟨x, rfl, rfl⟩
    · simp [constructorShape] at hshape
  · rcases hb with ⟨y, rfl⟩ | ⟨g, ys, rfl⟩
    · simp [constructorShape] at hshape
    · have hfg : f = g ∧ xs.length = ys.length := by
        simpa only [constructorShape, Option.some.injEq, Sum.inr.injEq,
          Prod.mk.injEq] using hshape
      rcases hfg with ⟨rfl, hlen⟩
      exact Or.inr ⟨f, xs, ys, rfl, rfl,
        List.forall₂_of_length_eq_of_get hlen (fun i hx hy => .argument hab i hx hy)⟩

/-- A compatible ambient equivalence exists exactly when the explicit
constructor-decomposition closure has no variable, symbol, or arity clash. -/
theorem exists_constructorCompatible_equivalence_iff (S : CRel sigma nu) :
    (∃ E : CRel sigma nu, Equivalence E ∧ ConstructorCompatible E ∧
      ∀ a b, S a b → E a b) ↔ ¬ ConstructorClash (ConstructorEqClosure S) := by
  constructor
  · rintro ⟨E, hEq, hE, hSE⟩ ⟨a, b, ha, hb, hab, hne⟩
    exact hne (hE.shape_eq ha hb (hab.least hEq hE hSE))
  · intro h
    exact ⟨ConstructorEqClosure S, ConstructorEqClosure.equivalence S,
      ConstructorEqClosure.compatible_of_no_clash h, fun _ _ hs => .seed hs⟩

/-- Failure of the ambient-equivalence requirement has an explicit clash in
the least decomposition closure. -/
theorem no_constructorCompatible_equivalence_iff (S : CRel sigma nu) :
    (¬ ∃ E : CRel sigma nu, Equivalence E ∧ ConstructorCompatible E ∧
      ∀ a b, S a b → E a b) ↔ ConstructorClash (ConstructorEqClosure S) := by
  classical
  rw [exists_constructorCompatible_equivalence_iff, not_not]

/-- A finite list of seed equations interpreted on the full term carrier. -/
def equationListRel (F : List (Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu)) :
    CRel sigma nu := fun a b => (a, b) ∈ F

/-- Every derived equation uses finitely many actual seed equations. -/
theorem ConstructorEqClosure.finite_support {S : CRel sigma nu}
    {a b : Term (sigma ⊕ sigma) nu} (h : ConstructorEqClosure S a b) :
    ∃ F : List (Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu),
      (∀ x y, equationListRel F x y → S x y) ∧
      ConstructorEqClosure (equationListRel F) a b := by
  induction h with
  | @seed a b h =>
      refine ⟨[(a, b)], ?_, .seed (List.mem_singleton_self _)⟩
      intro x y hxy
      have heq : (x, y) = (a, b) := List.mem_singleton.mp hxy
      cases heq
      exact h
  | refl a =>
      refine ⟨[], ?_, .refl a⟩
      intro x y hxy
      cases hxy
  | symm _ ih =>
      obtain ⟨F, hF, h⟩ := ih
      exact ⟨F, hF, .symm h⟩
  | trans _ _ ih₁ ih₂ =>
      obtain ⟨F, hF, hf⟩ := ih₁
      obtain ⟨G, hG, hg⟩ := ih₂
      refine ⟨F ++ G, ?_, .trans (hf.mono ?_) (hg.mono ?_)⟩
      · intro x y hxy
        rcases List.mem_append.mp hxy with hf | hg
        · exact hF x y hf
        · exact hG x y hg
      · intro x y hxy
        exact List.mem_append.mpr (Or.inl hxy)
      · intro x y hxy
        exact List.mem_append.mpr (Or.inr hxy)
  | argument _ i hx hy ih =>
      obtain ⟨F, hF, h⟩ := ih
      exact ⟨F, hF, .argument h i hx hy⟩

/-- Every obstruction to a compatible equivalence is already an obstruction
for a finite subset of the original seed equations. -/
theorem constructorClash_iff_finite_seed (S : CRel sigma nu) :
    ConstructorClash (ConstructorEqClosure S) ↔
      ∃ F : List (Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu),
        (∀ x y, equationListRel F x y → S x y) ∧
        ConstructorClash (ConstructorEqClosure (equationListRel F)) := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, hne⟩
    obtain ⟨F, hF, h⟩ := hab.finite_support
    exact ⟨F, hF, a, b, ha, hb, h, hne⟩
  · rintro ⟨F, hF, a, b, ha, hb, hab, hne⟩
    exact ⟨a, b, ha, hb, hab.mono hF, hne⟩

/-- Compatible equivalence extensions satisfy finite character, for arbitrary
signatures, variable types, and possibly infinite seed relations. -/
theorem constructorCompatible_equivalence_finite_character (S : CRel sigma nu) :
    (∃ E : CRel sigma nu, Equivalence E ∧ ConstructorCompatible E ∧
      ∀ a b, S a b → E a b) ↔
    ∀ F : List (Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu),
      (∀ a b, equationListRel F a b → S a b) →
      ∃ E : CRel sigma nu, Equivalence E ∧ ConstructorCompatible E ∧
        ∀ a b, equationListRel F a b → E a b := by
  constructor
  · rintro ⟨E, hEq, hE, hSE⟩ F hF
    exact ⟨E, hEq, hE, fun a b h => hSE a b (hF a b h)⟩
  · intro h
    apply (exists_constructorCompatible_equivalence_iff S).mpr
    intro hclash
    obtain ⟨F, hF, hbad⟩ := (constructorClash_iff_finite_seed S).mp hclash
    exact (exists_constructorCompatible_equivalence_iff (equationListRel F)).mp
      (h F hF) hbad

/-! ## Ambient closure of an actual parent replacement -/

/-- A replacement ambient is one equivalence on the full translated-term
carrier that contains both the old and temporary forest equalities and
decomposes related constructor applications argumentwise. -/
def PGraph.ReplacementAmbient
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a b : Term (sigma ⊕ sigma) nu) : Prop :=
  ∃ E : CRel sigma nu, Equivalence E ∧ ConstructorCompatible E ∧
    ∀ x y, rho.ReplacementSeed a b x y → E x y

/-- The ambient certificate for an actual parent replacement exists exactly
when its explicit constructor-decomposition closure contains no shape clash. -/
theorem PGraph.replacementAmbient_iff_no_clash
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a b : Term (sigma ⊕ sigma) nu) :
    rho.ReplacementAmbient a b ↔
      ¬ ConstructorClash (ConstructorEqClosure (rho.ReplacementSeed a b)) := by
  exact exists_constructorCompatible_equivalence_iff (rho.ReplacementSeed a b)

/-- Replacement ambient existence has finite character even when the
signature, variable type, and full seed relation are infinite. -/
theorem PGraph.replacementAmbient_finite_character
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a b : Term (sigma ⊕ sigma) nu) :
    rho.ReplacementAmbient a b ↔
      ∀ F : List (Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu),
        (∀ x y, equationListRel F x y → rho.ReplacementSeed a b x y) →
        ∃ E : CRel sigma nu, Equivalence E ∧ ConstructorCompatible E ∧
          ∀ x y, equationListRel F x y → E x y := by
  exact constructorCompatible_equivalence_finite_character (rho.ReplacementSeed a b)

/-- Every actual parent replacement has either a compatible ambient
equivalence or a finite list of its own seed equations witnessing a constructor
shape clash. -/
theorem PGraph.replacementAmbient_or_finite_clash
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a b : Term (sigma ⊕ sigma) nu) :
    rho.ReplacementAmbient a b ∨
      ∃ F : List (Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu),
        (∀ x y, equationListRel F x y → rho.ReplacementSeed a b x y) ∧
        ConstructorClash (ConstructorEqClosure (equationListRel F)) := by
  classical
  by_cases h : rho.ReplacementAmbient a b
  · exact Or.inl h
  · apply Or.inr
    have hbad : ConstructorClash
        (ConstructorEqClosure (rho.ReplacementSeed a b)) := by
      apply (no_constructorCompatible_equivalence_iff
        (rho.ReplacementSeed a b)).mp
      exact h
    exact (constructorClash_iff_finite_seed (rho.ReplacementSeed a b)).mp hbad

/-- Semantic closure required after replacing one parent: every translated
root/context/root fork over the actual replacement seed has related outputs. -/
def PGraph.ReplacementForkSound
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS sigma nu}
    (rho : PGraph A (constructorTranslation R))
    (p q : Term (sigma ⊕ sigma) nu) : Prop :=
  ∀ {a b c d : Term (sigma ⊕ sigma) nu}, b ∈ A → d ∈ A →
    rootStep (constructorTranslation R) a b →
    barRel (rho.ReplacementSeed p q) a c →
    rootStep (constructorTranslation R) c d →
    DownOn A (constructorTranslation R) b d

/-- A replacement ambient converts the semantic critical-pair theorem into
soundness of every fork generated by that concrete replacement. -/
theorem PGraph.translated_replacementSeed_fork_sound_of_ambient
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    (rho : PGraph A (constructorTranslation R))
    {p q : Term (sigma ⊕ sigma) nu} (hp : p ∈ A) (hq : q ∈ A)
    (hne : ¬ EqvOn A rho.par p q)
    (hpq : Grey A (constructorTranslation R) (EqvOn A rho.par) p q)
    (hambient : rho.ReplacementAmbient p q) : rho.ReplacementForkSound p q := by
  rcases hambient with ⟨E, hEq, hCC, hSE⟩
  intro a b c d hb hd hab hac hcd
  exact rho.translated_replacementSeed_fork_sound (E := E) hA hno hvar hp hq hne hpq
    (fun _ _ h => hEq.symm h) (fun _ _ _ h1 h2 => hEq.trans h1 h2)
    hCC hSE hb hd hab hac hcd

/-- Absence of a constructor clash in the least explicit closure is sufficient
for soundness of every translated replacement fork. -/
theorem PGraph.translated_replacementSeed_fork_sound_of_no_clash
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    (rho : PGraph A (constructorTranslation R))
    {p q : Term (sigma ⊕ sigma) nu} (hp : p ∈ A) (hq : q ∈ A)
    (hne : ¬ EqvOn A rho.par p q)
    (hpq : Grey A (constructorTranslation R) (EqvOn A rho.par) p q)
    (hnoclash : ¬ ConstructorClash
      (ConstructorEqClosure (rho.ReplacementSeed p q))) :
    rho.ReplacementForkSound p q :=
  rho.translated_replacementSeed_fork_sound_of_ambient hA hno hvar hp hq hne hpq
    ((rho.replacementAmbient_iff_no_clash p q).mpr hnoclash)

/-- It is enough to solve every finite subproblem of the replacement seed;
finite character then supplies one ambient for the whole possibly infinite
term carrier. -/
theorem PGraph.translated_replacementSeed_fork_sound_of_finite_ambients
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    (rho : PGraph A (constructorTranslation R))
    {p q : Term (sigma ⊕ sigma) nu} (hp : p ∈ A) (hq : q ∈ A)
    (hne : ¬ EqvOn A rho.par p q)
    (hpq : Grey A (constructorTranslation R) (EqvOn A rho.par) p q)
    (hfinite :
      ∀ F : List (Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu),
        (∀ x y, equationListRel F x y → rho.ReplacementSeed p q x y) →
        ∃ E : CRel sigma nu, Equivalence E ∧ ConstructorCompatible E ∧
          ∀ x y, equationListRel F x y → E x y) :
    rho.ReplacementForkSound p q :=
  rho.translated_replacementSeed_fork_sound_of_ambient hA hno hvar hp hq hne hpq
    ((rho.replacementAmbient_finite_character p q).mpr hfinite)

/-- For every concrete replacement in the translated system, either all of
its semantic forks are sound or a finite subset of its seed equations records
the exact constructor clash blocking the ambient construction. -/
theorem PGraph.translated_replacement_forkSound_or_finite_clash
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    (rho : PGraph A (constructorTranslation R))
    {p q : Term (sigma ⊕ sigma) nu} (hp : p ∈ A) (hq : q ∈ A)
    (hne : ¬ EqvOn A rho.par p q)
    (hpq : Grey A (constructorTranslation R) (EqvOn A rho.par) p q) :
    rho.ReplacementForkSound p q ∨
      ∃ F : List (Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu),
        (∀ x y, equationListRel F x y → rho.ReplacementSeed p q x y) ∧
        ConstructorClash (ConstructorEqClosure (equationListRel F)) := by
  rcases rho.replacementAmbient_or_finite_clash p q with hambient | hclash
  · exact Or.inl (rho.translated_replacementSeed_fork_sound_of_ambient
      hA hno hvar hp hq hne hpq hambient)
  · exact Or.inr hclash

end OperatorKO7.Meta.UniqueNormalization
