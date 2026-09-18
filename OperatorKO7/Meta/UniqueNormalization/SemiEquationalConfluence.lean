import OperatorKO7.Meta.UniqueNormalization.Transfer
import OperatorKO7.Meta.UniqueNormalization.HubLinearization

/-!
# Confluence of left-linear semi-equational systems without feasible overlaps

Campaign: RTA open problem 79, route R2 (conditional linearization), after the
2026-09-11 failure analysis in
`Audit/worktree-lean-publication-audit/klop-status-assessment.md`.

A semi-equational conditional system fires a rule only when every condition pair
is convertible in the system itself. `ConditionalTRS.lean` resolves that
self-reference by levels. This module shows that the levels can be dropped: a
step at some level is the same as a step whose conditions hold in the system's
own conversion (`cstep_iff_cstepE_cconv`). With the conversion held fixed as an
oracle, the redexes are the rule instances whose conditions are true, and the
parallel-moves argument of Tait, Martin-Lof and Takahashi applies:

* `CPar C E`, parallel reduction whose root contractions need their condition
  instances in the oracle `E`;
* `cpar_pattern_decompose`, a parallel step out of an instance of a left-linear
  pattern with no oracle redex at a non-variable position gives an instance of
  the same pattern;
* `cpar_exists_target`, every term has one parallel reduct that each of its
  parallel reducts reaches in one parallel step, by induction on the size of the
  source term;
* `cstepE_relConfluent`, hence confluence, with no termination hypothesis.

For the semi-equational oracle the conditions are stable under the system's own
steps, because every step lies inside the conversion (`oracleStable_cconv`). The
result is confluence of every left-linear semi-equational system with the
variable condition whose rules never overlap with both condition sets convertible
(`cconfluent_of_noFeasibleOverlap`). Syntactic non-overlap implies that
hypothesis; that case corresponds to the orthogonal semi-equational systems of
Bergstra and Klop (1986), cited secondhand: the primary source was not opened in
this campaign, and the Lean class also allows condition variables outside the
left-hand side.

Through the transfer theorem of `Transfer.lean`, a confluent linearization gives
unique normal forms of the original system, for systems with the variable
condition:

* `UNconv_of_linHub_nonOverlapping`: UN= when the hub linearization is
  non-overlapping, the strongly non-overlapping class of the literature, cited
  secondhand (Chew's own definition is open item 1 in `skeleton-mano-ogawa.md`);
* `UNconv_of_linHub_noFeasibleOverlap`: UN= when the hub linearization has no
  feasible overlap;
* `KlopSystem.UNconv_trs`: Klop's system has unique normal forms, although it is
  not confluent;
* `InfeasibleOverlap`: a system whose linearization overlaps but whose overlap
  never fires, so the theorem covers more than syntactic non-overlap.

Proves: confluence of `CStep C` for left-linear `C` with the variable condition
and `NoFeasibleOverlap C (cconv C)`; UN= of every `R` with the variable condition
and such a linearization.
Does not prove: `NoFeasibleOverlap (linHub R) (cconv (linHub R))` for
non-omega-overlapping `R`. That hypothesis quantifies over conversions of `R`
itself and contains instances of UN=: for `f(x, x) -> a` beside `f(c, d) -> b` it
holds exactly when `c` and `d` are not convertible. It restates the missing
theorem as a statement about overlaps of the linearization (ledger row F63); it
is not a smaller problem.
Relation: `CStep` of a conditional system and `Step` of the original system.
Closure: context closure, reflexive-transitive closure, conversion.
Strategy: full rewriting.
Trust: kernel checked; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe` or `opaque`. Axiom footprints are printed at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Occurrence lists -/

/-- The occurrence list of a variable is that variable. -/
theorem varOccurrences_var_eq (x : nu) :
    OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences
      (Term.var x : Term sigma nu) = [x] := by
  simp [OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences]

/-- The occurrence list of an application concatenates the lists of its
arguments. -/
theorem varOccurrences_app_eq (f : sigma) (args : List (Term sigma nu)) :
    OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences (Term.app f args) =
      args.flatMap OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences := by
  simp [OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences]

/-- A variable occurs in a term exactly when the term's occurrence list
contains it. -/
theorem varOccurs_iff_mem_varOccurrences {x : nu} :
    ∀ (t : Term sigma nu), VarOccurs x t ↔
      x ∈ OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences t := by
  intro t
  induction t using Term.rec' with
  | hvar y =>
      rw [varOccurrences_var_eq, List.mem_singleton]
      constructor
      · intro h
        cases h
        rfl
      · intro h
        subst h
        exact VarOccurs.here
  | happ f args ih =>
      rw [varOccurrences_app_eq, List.mem_flatMap]
      constructor
      · intro h
        obtain ⟨a, ha, hxa⟩ := h.app_inv
        exact ⟨a, ha, (ih a ha).1 hxa⟩
      · rintro ⟨a, ha, hxa⟩
        exact VarOccurs.arg ha ((ih a ha).2 hxa)

/-! ## Substitutions and renamings -/

/-- Two substitutions with the same instance of a term agree on every variable
occurring in the term. -/
theorem agree_on_occurs_of_apply_eq {s s' : Subst sigma nu} :
    ∀ (t : Term sigma nu), Subst.apply s t = Subst.apply s' t →
      ∀ x, VarOccurs x t → s x = s' x := by
  intro t
  induction t using Term.rec' with
  | hvar y =>
      intro h x hx
      cases hx
      simpa using h
  | happ f args ih =>
      intro h x hx
      obtain ⟨a, ha, hxa⟩ := hx.app_inv
      simp only [Subst.apply_app, Subst.applyList_eq_map, Term.app.injEq, true_and] at h
      exact ih a ha ((List.map_eq_map_iff.mp h) a ha) x hxa

/-- Every variable of a renamed term is the image of a variable of the original
term. -/
theorem varOccurs_mapVar_inv {rho : nu → nu} {x : nu} :
    ∀ (t : Term sigma nu), VarOccurs x (Term.mapVar rho t) →
      ∃ w, VarOccurs w t ∧ rho w = x := by
  intro t
  induction t using Term.rec' with
  | hvar y =>
      intro h
      rw [Term.mapVar_var] at h
      cases h
      exact ⟨y, VarOccurs.here, rfl⟩
  | happ f args ih =>
      intro h
      rw [Term.mapVar_app, Term.mapVarList_eq_map] at h
      obtain ⟨a', ha', hxa'⟩ := h.app_inv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ha'
      obtain ⟨w, hw, hrw⟩ := ih a ha hxa'
      exact ⟨w, VarOccurs.arg ha hw, hrw⟩

/-! ## The levels collapse into one oracle -/

/-- A conversion of the system is a conversion built from the steps of one level. -/
theorem exists_level_of_cconv {C : CTRS sigma nu} {a b : Term sigma nu}
    (h : cconv C a b) : ∃ n, relConv (CStepLevel C n) a b := by
  induction h with
  | refl => exact ⟨0, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
      obtain ⟨n, hn⟩ := ih
      rcases hbc with ⟨m, hm⟩ | ⟨m, hm⟩
      · refine ⟨max n m, ?_⟩
        refine Relation.ReflTransGen.tail
          (relConv.mono (fun x y hxy => CStepLevel.mono_of_le C (le_max_left n m) hxy) hn) ?_
        exact Or.inl (CStepLevel.mono_of_le C (le_max_right n m) hm)
      · refine ⟨max n m, ?_⟩
        refine Relation.ReflTransGen.tail
          (relConv.mono (fun x y hxy => CStepLevel.mono_of_le C (le_max_left n m) hxy) hn) ?_
        exact Or.inr (CStepLevel.mono_of_le C (le_max_right n m) hm)

/-- Finitely many condition instances that hold in the conversion all hold at one
common level. -/
theorem exists_level_of_conds {C : CTRS sigma nu} {σ : Subst sigma nu} :
    ∀ (ps : List (Term sigma nu × Term sigma nu)),
      (∀ p ∈ ps, cconv C (Subst.apply σ p.1) (Subst.apply σ p.2)) →
      ∃ n, ∀ p ∈ ps, relConv (CStepLevel C n) (Subst.apply σ p.1) (Subst.apply σ p.2) := by
  intro ps
  induction ps with
  | nil => intro _; exact ⟨0, fun p hp => by cases hp⟩
  | cons q qs ih =>
      intro h
      obtain ⟨n, hn⟩ := exists_level_of_cconv (h q List.mem_cons_self)
      obtain ⟨m, hm⟩ := ih (fun p hp => h p (List.mem_cons_of_mem q hp))
      refine ⟨max n m, fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact relConv.mono (fun x y hxy => CStepLevel.mono_of_le C (le_max_left n m) hxy) hn
      · exact relConv.mono (fun x y hxy => CStepLevel.mono_of_le C (le_max_right n m) hxy)
          (hm p hp')

/-- A step at some level has its conditions in the system's own conversion. -/
theorem cstepE_cconv_of_cstep {C : CTRS sigma nu} {s t : Term sigma nu}
    (h : CStep C s t) : CStepE C (cconv C) s t := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => exact hn.elim
  | succ m =>
      have hm : CStepE C (relConv (CStepLevel C m)) s t := hn
      exact CStepE.mono (fun a b hab => cconv_of_relConv_level m hab) hm

/-- A step whose conditions hold in the system's conversion is a step at some
level. -/
theorem cstep_of_cstepE_cconv {C : CTRS sigma nu} :
    ∀ {s t : Term sigma nu}, CStepE C (cconv C) s t → CStep C s t := by
  intro s t h
  induction h with
  | root hr =>
      obtain ⟨crule, hmem, σ, hs, ht, hconds⟩ := hr
      obtain ⟨n, hn⟩ := exists_level_of_conds crule.conds hconds
      exact ⟨n + 1, CStepE.root ⟨crule, hmem, σ, hs, ht, hn⟩⟩
  | arg f pre post _ ih => exact CStep.arg C f pre post ih

/-- **The oracle characterization.** A step of the level-stratified system is
exactly a step whose condition instances are convertible in the system itself.

Relation: `CStep C` against `CStepE C (cconv C)`.
Closure: context closure of the root step, in both relations.
Strategy: full rewriting.
Trust: kernel checked. -/
theorem cstep_iff_cstepE_cconv (C : CTRS sigma nu) (s t : Term sigma nu) :
    CStep C s t ↔ CStepE C (cconv C) s t :=
  ⟨cstepE_cconv_of_cstep, cstep_of_cstepE_cconv⟩

/-- A reduction of the oracle system with the conversion as oracle stays inside
the conversion. -/
theorem cconv_of_cstepEStar {C : CTRS sigma nu} {a b : Term sigma nu}
    (h : Relation.ReflTransGen (CStepE C (cconv C)) a b) : cconv C a b := by
  induction h with
  | refl => exact relConv.refl a
  | tail _ hlast ih => exact relConv.trans ih (relConv.single (cstep_of_cstepE_cconv hlast))

/-! ## Congruence of oracle reduction -/

/-- Oracle reduction lifts through one argument position. -/
theorem cstepEStar_arg {C : CTRS sigma nu} {E : Term sigma nu → Term sigma nu → Prop}
    (f : sigma) (pre post : List (Term sigma nu)) {a b : Term sigma nu}
    (h : Relation.ReflTransGen (CStepE C E) a b) :
    Relation.ReflTransGen (CStepE C E) (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post)) :=
  Relation.ReflTransGen.lift (fun a => Term.app f (pre ++ a :: post))
    (fun _ _ hs => CStepE.arg f pre post hs) h

/-- Oracle reduction lifts through a suffix of an argument list. -/
theorem cstepEStar_args_append {C : CTRS sigma nu} {E : Term sigma nu → Term sigma nu → Prop}
    (f : sigma) :
    ∀ (pre : List (Term sigma nu)) {xs ys : List (Term sigma nu)},
      List.Forall₂ (Relation.ReflTransGen (CStepE C E)) xs ys →
      Relation.ReflTransGen (CStepE C E) (.app f (pre ++ xs)) (.app f (pre ++ ys)) := by
  intro pre xs
  induction xs generalizing pre with
  | nil =>
      intro ys h
      cases h
      exact Relation.ReflTransGen.refl
  | cons a as ih =>
      intro ys h
      cases h with
      | cons hab habs =>
          rename_i b _
          refine (cstepEStar_arg f pre as hab).trans ?_
          simpa using ih (pre ++ [b]) habs

/-- Pointwise oracle reduction of a substitution gives oracle reduction of every
instance. -/
theorem cstepEStar_apply_pointwise {C : CTRS sigma nu}
    {E : Term sigma nu → Term sigma nu → Prop} {σ τ : Subst sigma nu}
    (hpt : ∀ z, Relation.ReflTransGen (CStepE C E) (σ z) (τ z)) :
    ∀ (t : Term sigma nu),
      Relation.ReflTransGen (CStepE C E) (Subst.apply σ t) (Subst.apply τ t) := by
  intro t
  induction t using Term.rec' with
  | hvar x => simpa using hpt x
  | happ f args ih =>
      simp only [Subst.apply_app, Subst.applyList_eq_map]
      simpa using cstepEStar_args_append (C := C) (E := E) f [] (forall₂_map_map ih)

/-! ## Parallel reduction with an oracle -/

mutual
/-- Parallel reduction of the conditional system `C` with oracle `E`. A variable
reduces to itself, an application reduces argument by argument, and a rule
instance whose condition instances hold in `E` contracts at the root while its
substituted terms reduce in parallel. -/
inductive CPar (C : CTRS sigma nu) (E : Term sigma nu → Term sigma nu → Prop) :
    Term sigma nu → Term sigma nu → Prop
  | var (x : nu) : CPar C E (.var x) (.var x)
  | app (f : sigma) {args args' : List (Term sigma nu)} :
      CParList C E args args' → CPar C E (.app f args) (.app f args')
  | root {crule : CRule sigma nu} (hmem : crule ∈ C) (σ σ' : Subst sigma nu)
      (hconds : ∀ p ∈ crule.conds, E (Subst.apply σ p.1) (Subst.apply σ p.2))
      (h : ∀ x, CPar C E (σ x) (σ' x)) :
      CPar C E (Subst.apply σ crule.lhs) (Subst.apply σ' crule.rhs)
/-- Position-wise parallel reduction of argument lists, the list companion of
`CPar`. -/
inductive CParList (C : CTRS sigma nu) (E : Term sigma nu → Term sigma nu → Prop) :
    List (Term sigma nu) → List (Term sigma nu) → Prop
  | nil : CParList C E [] []
  | cons {a a' : Term sigma nu} {as as' : List (Term sigma nu)} :
      CPar C E a a' → CParList C E as as' → CParList C E (a :: as) (a' :: as')
end

mutual
/-- Every term parallel-reduces to itself. -/
theorem CPar.refl (C : CTRS sigma nu) (E : Term sigma nu → Term sigma nu → Prop) :
    ∀ (t : Term sigma nu), CPar C E t t
  | .var x => CPar.var x
  | .app f args => CPar.app f (CParList.refl C E args)
/-- Every argument list parallel-reduces to itself. -/
theorem CParList.refl (C : CTRS sigma nu) (E : Term sigma nu → Term sigma nu → Prop) :
    ∀ (args : List (Term sigma nu)), CParList C E args args
  | [] => CParList.nil
  | a :: as => CParList.cons (CPar.refl C E a) (CParList.refl C E as)
end

/-- A parallel step in one argument position, with the other positions fixed. -/
theorem CParList.of_slot {C : CTRS sigma nu} {E : Term sigma nu → Term sigma nu → Prop}
    (pre post : List (Term sigma nu)) {a b : Term sigma nu} (h : CPar C E a b) :
    CParList C E (pre ++ a :: post) (pre ++ b :: post) := by
  induction pre with
  | nil => exact CParList.cons h (CParList.refl C E post)
  | cons c cs ih => exact CParList.cons (CPar.refl C E c) ih

/-- Pointwise parallel steps along one list give a list step. -/
theorem CParList.of_map {C : CTRS sigma nu} {E : Term sigma nu → Term sigma nu → Prop}
    {F G : Term sigma nu → Term sigma nu} :
    ∀ {xs : List (Term sigma nu)}, (∀ a ∈ xs, CPar C E (F a) (G a)) →
      CParList C E (xs.map F) (xs.map G) := by
  intro xs
  induction xs with
  | nil => intro _; exact CParList.nil
  | cons a as ih =>
      intro h
      exact CParList.cons (h a List.mem_cons_self)
        (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- Every oracle step is a parallel step. -/
theorem CPar.of_cstepE {C : CTRS sigma nu} {E : Term sigma nu → Term sigma nu → Prop} :
    ∀ {s t : Term sigma nu}, CStepE C E s t → CPar C E s t := by
  intro s t h
  induction h with
  | root hr =>
      obtain ⟨crule, hmem, σ, hs, ht, hconds⟩ := hr
      rw [hs, ht]
      exact CPar.root hmem σ σ hconds (fun x => CPar.refl C E (σ x))
  | arg f pre post _ ih => exact CPar.app f (CParList.of_slot pre post ih)

/-- The only parallel reduct of a variable is the variable itself: a left-hand
side is an application, so no rule contracts a variable. -/
theorem CPar.var_inv {C : CTRS sigma nu} {E : Term sigma nu → Term sigma nu → Prop}
    {x : nu} {u : Term sigma nu} (h : CPar C E (.var x) u) : u = .var x := by
  refine CPar.rec (C := C) (E := E)
    (motive_1 := fun t u _ => ∀ y : nu, t = .var y → u = .var y)
    (motive_2 := fun _ _ _ => True)
    ?var ?app ?root trivial (fun _ _ _ _ => trivial) h x rfl
  · intro z y hz; exact hz
  · intro f args args' _ _ y hy; exact absurd hy (by simp)
  · intro crule hmem σ σ' _ _ _ y hy
    have happ := crule.lhs_isApp
    cases hl : crule.lhs with
    | var z => rw [hl] at happ; simp at happ
    | app g gargs => rw [hl, Subst.apply_app] at hy; simp at hy

/-- A parallel step out of an application either reduces the arguments or
contracts a rule instance at the root. -/
theorem CPar.app_inv {C : CTRS sigma nu} {E : Term sigma nu → Term sigma nu → Prop}
    {f : sigma} {args : List (Term sigma nu)} {u : Term sigma nu}
    (h : CPar C E (.app f args) u) :
    (∃ args', u = .app f args' ∧ CParList C E args args') ∨
      (∃ crule ∈ C, ∃ σ σ' : Subst sigma nu,
        (Term.app f args : Term sigma nu) = Subst.apply σ crule.lhs ∧
        u = Subst.apply σ' crule.rhs ∧
        (∀ p ∈ crule.conds, E (Subst.apply σ p.1) (Subst.apply σ p.2)) ∧
        ∀ x, CPar C E (σ x) (σ' x)) := by
  refine CPar.rec (C := C) (E := E)
    (motive_1 := fun t u _ => ∀ (g : sigma) (as : List (Term sigma nu)), t = .app g as →
      (∃ as', u = .app g as' ∧ CParList C E as as') ∨
        (∃ crule ∈ C, ∃ σ σ' : Subst sigma nu,
          (Term.app g as : Term sigma nu) = Subst.apply σ crule.lhs ∧
          u = Subst.apply σ' crule.rhs ∧
          (∀ p ∈ crule.conds, E (Subst.apply σ p.1) (Subst.apply σ p.2)) ∧
          ∀ x, CPar C E (σ x) (σ' x)))
    (motive_2 := fun _ _ _ => True)
    ?var ?app ?root trivial (fun _ _ _ _ => trivial) h f args rfl
  · intro x g as hx; exact absurd hx (by simp)
  · intro g args0 args0' hlist _ g' as has
    rw [Term.app.injEq] at has
    obtain ⟨hgg, haa⟩ := has
    subst hgg; subst haa
    exact Or.inl ⟨args0', rfl, hlist⟩
  · intro crule hmem σ σ' hconds hpt _ g as has
    exact Or.inr ⟨crule, hmem, σ, σ', has.symm, rfl, hconds, hpt⟩

/-- A list step out of the empty list gives the empty list. -/
theorem CParList.nil_inv {C : CTRS sigma nu} {E : Term sigma nu → Term sigma nu → Prop}
    {us : List (Term sigma nu)} (h : CParList C E [] us) : us = [] := by
  cases h
  rfl

/-- A list step out of a nonempty list steps its head and its tail. -/
theorem CParList.cons_inv {C : CTRS sigma nu} {E : Term sigma nu → Term sigma nu → Prop}
    {a : Term sigma nu} {as us : List (Term sigma nu)} (h : CParList C E (a :: as) us) :
    ∃ u us', us = u :: us' ∧ CPar C E a u ∧ CParList C E as us' := by
  cases h with
  | cons ha has => exact ⟨_, _, rfl, ha, has⟩

/-- Substitutions related by parallel steps on the variables of a term give a
parallel step between the two instances of that term. -/
theorem CPar.apply_pointwise {C : CTRS sigma nu} {E : Term sigma nu → Term sigma nu → Prop}
    {σ τ : Subst sigma nu} :
    ∀ (t : Term sigma nu), (∀ x, VarOccurs x t → CPar C E (σ x) (τ x)) →
      CPar C E (Subst.apply σ t) (Subst.apply τ t) := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
      intro h
      simpa using h x VarOccurs.here
  | happ f args ih =>
      intro h
      simp only [Subst.apply_app, Subst.applyList_eq_map]
      exact CPar.app f (CParList.of_map (fun a ha =>
        ih a ha (fun x hx => h x (VarOccurs.arg ha hx))))

/-- A parallel step is a finite oracle reduction. -/
theorem cstepEStar_of_cpar {C : CTRS sigma nu} {E : Term sigma nu → Term sigma nu → Prop}
    {s t : Term sigma nu} (h : CPar C E s t) : Relation.ReflTransGen (CStepE C E) s t := by
  refine CPar.rec (C := C) (E := E)
    (motive_1 := fun a a' _ => Relation.ReflTransGen (CStepE C E) a a')
    (motive_2 := fun as as' _ => ∀ (f : sigma) (done : List (Term sigma nu)),
      Relation.ReflTransGen (CStepE C E) (.app f (done ++ as)) (.app f (done ++ as')))
    ?var ?app ?root ?nil ?cons h
  · intro x; exact Relation.ReflTransGen.refl
  · intro g _ _ _ ih
    simpa using ih g []
  · intro crule hmem σ σ' hconds _ ih
    have hroot : Relation.ReflTransGen (CStepE C E)
        (Subst.apply σ crule.lhs) (Subst.apply σ crule.rhs) :=
      Relation.ReflTransGen.single (CStepE.root ⟨crule, hmem, σ, rfl, rfl, hconds⟩)
    exact hroot.trans (cstepEStar_apply_pointwise ih crule.rhs)
  · intro f done; exact Relation.ReflTransGen.refl
  · intro a a' as as' _ _ ihHead ihTail f done
    have h1 := cstepEStar_arg f done as ihHead
    have h2 := ihTail f (done ++ [a'])
    have he1 : done ++ a' :: as = (done ++ [a']) ++ as := by simp
    have he2 : (done ++ [a']) ++ as' = done ++ a' :: as' := by simp
    rw [he1] at h1
    rw [he2] at h2
    exact h1.trans h2

/-- A sequence of parallel steps is a finite oracle reduction. -/
theorem cstepEStar_of_cparStar {C : CTRS sigma nu} {E : Term sigma nu → Term sigma nu → Prop}
    {s t : Term sigma nu} (h : Relation.ReflTransGen (CPar C E) s t) :
    Relation.ReflTransGen (CStepE C E) s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih => exact ih.trans (cstepEStar_of_cpar hlast)

/-! ## The hypotheses -/

/-- `s` is an instance of a rule's left-hand side whose condition instances all
hold in the oracle `E`. -/
def IsOracleRedex (C : CTRS sigma nu) (E : Term sigma nu → Term sigma nu → Prop)
    (s : Term sigma nu) : Prop :=
  ∃ crule ∈ C, ∃ τ : Subst sigma nu, s = Subst.apply τ crule.lhs ∧
    ∀ p ∈ crule.conds, E (Subst.apply τ p.1) (Subst.apply τ p.2)

/-- Every conditional left-hand side is left-linear. -/
def CLeftLinear (C : CTRS sigma nu) : Prop :=
  ∀ crule ∈ C, OperatorKO7.Meta.UniqueNormalization.Term.LeftLinear crule.lhs

/-- Every variable of a right-hand side occurs in the left-hand side of its rule. -/
def CVarCondition (C : CTRS sigma nu) : Prop :=
  ∀ crule ∈ C, ∀ x, VarOccurs x crule.rhs → VarOccurs x crule.lhs

/-- **No feasible overlap.** Whenever a non-variable subterm of one left-hand side
and a second left-hand side have a common instance, under substitutions for which
both condition sets hold in `E`, the two rules coincide and the subterm is the
whole left-hand side. The two substitutions are independent, so the rules are
renamed apart. -/
def NoFeasibleOverlap (C : CTRS sigma nu) (E : Term sigma nu → Term sigma nu → Prop) :
    Prop :=
  ∀ r₁ ∈ C, ∀ r₂ ∈ C, ∀ q : Term sigma nu, Subterm q r₁.lhs → q.isApp = true →
    ∀ σ₁ σ₂ : Subst sigma nu, Subst.apply σ₁ q = Subst.apply σ₂ r₂.lhs →
      (∀ p ∈ r₁.conds, E (Subst.apply σ₁ p.1) (Subst.apply σ₁ p.2)) →
      (∀ p ∈ r₂.conds, E (Subst.apply σ₂ p.1) (Subst.apply σ₂ p.2)) →
      r₁ = r₂ ∧ q = r₁.lhs

/-- Syntactic non-overlap of the conditional left-hand sides, conditions ignored. -/
def CNonOverlapping (C : CTRS sigma nu) : Prop :=
  ∀ r₁ ∈ C, ∀ r₂ ∈ C, ∀ q : Term sigma nu, Subterm q r₁.lhs → q.isApp = true →
    ∀ σ₁ σ₂ : Subst sigma nu, Subst.apply σ₁ q = Subst.apply σ₂ r₂.lhs →
      r₁ = r₂ ∧ q = r₁.lhs

/-- The oracle is preserved when both of its arguments take a parallel step. -/
def OracleStable (C : CTRS sigma nu) (E : Term sigma nu → Term sigma nu → Prop) : Prop :=
  ∀ a b a' b' : Term sigma nu, E a b → CPar C E a a' → CPar C E b b' → E a' b'

/-- Syntactic non-overlap gives no feasible overlap for every oracle. -/
theorem noFeasibleOverlap_of_nonOverlapping {C : CTRS sigma nu}
    (E : Term sigma nu → Term sigma nu → Prop) (h : CNonOverlapping C) :
    NoFeasibleOverlap C E :=
  fun r₁ h₁ r₂ h₂ q hq happ σ₁ σ₂ heq _ _ => h r₁ h₁ r₂ h₂ q hq happ σ₁ σ₂ heq

/-- **The semi-equational oracle is stable.** Every parallel step with the
system's conversion as oracle is a conversion, so conversion of the endpoints
survives it. -/
theorem oracleStable_cconv (C : CTRS sigma nu) : OracleStable C (cconv C) := by
  intro a b a' b' hab ha hb
  have haa : cconv C a a' := cconv_of_cstepEStar (cstepEStar_of_cpar ha)
  have hbb : cconv C b b' := cconv_of_cstepEStar (cstepEStar_of_cpar hb)
  exact relConv.trans (relConv.trans (relConv.symm haa) hab) hbb

/-- A method-faithful linearization has left-linear conditional left-hand sides. -/
theorem cLeftLinear_of_isMethodLinearization {R : TRS sigma nu} {C : CTRS sigma nu}
    (h : IsMethodLinearization R C) : CLeftLinear C := by
  intro crule hc
  obtain ⟨rule, -, hw⟩ := h.1 crule hc
  exact hw.leftLinear

/-- A linearization of a system with the variable condition has the variable
condition: the conditional right-hand side is the original one, and every
variable of the original left-hand side survives in the conditional one, either
fixed by the collapse or as the hub of a condition. -/
theorem cVarCondition_of_isLinearization {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C)
    (hvar : ∀ rule ∈ R, ∀ x, VarOccurs x rule.rhs → VarOccurs x rule.lhs) :
    CVarCondition C := by
  intro crule hc x hx
  obtain ⟨rule, hr, hrhs, rho, hcollapse, hconds, hlhs, -⟩ := hlin.1 crule hc
  have hxr : VarOccurs x rule.rhs := by rw [← hrhs]; exact hx
  have hxl : VarOccurs x (Term.mapVar rho crule.lhs) := by
    rw [hcollapse]; exact hvar rule hr x hxr
  obtain ⟨w, hw, hrw⟩ := varOccurs_mapVar_inv crule.lhs hxl
  rcases hlhs w hw with hfix | hpair
  · rw [hfix] at hrw
    subst hrw
    exact hw
  · obtain ⟨a, b, hp, _, _, ha, _⟩ := hconds _ hpair
    simp only [Prod.mk.injEq, Term.var.injEq] at hp
    rw [← hrw, hp.1]
    exact ha

/-! ## Decomposition of a parallel step out of a pattern instance -/

/-- **Pattern decomposition, list form.** If each pattern of a list decomposes,
the patterns share no variable, and no oracle redex sits at a non-variable
position of any of them, then a list step out of the instances gives instances of
the same patterns under one substitution. That substitution differs from the
original only on the patterns' variables, where each new image is a parallel
reduct of the old one. -/
theorem cparList_pattern_decompose {C : CTRS sigma nu}
    {E : Term sigma nu → Term sigma nu → Prop} (σ : Subst sigma nu) :
    ∀ (ps : List (Term sigma nu)),
      (∀ p ∈ ps, (OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences p).Nodup →
        (∀ q, Subterm q p → q.isApp = true → ¬ IsOracleRedex C E (Subst.apply σ q)) →
        ∀ u, CPar C E (Subst.apply σ p) u →
          ∃ σ' : Subst sigma nu, u = Subst.apply σ' p ∧
            (∀ x, VarOccurs x p → CPar C E (σ x) (σ' x)) ∧
            (∀ x, ¬ VarOccurs x p → σ' x = σ x)) →
      (ps.flatMap OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences).Nodup →
      (∀ p ∈ ps, ∀ q, Subterm q p → q.isApp = true →
        ¬ IsOracleRedex C E (Subst.apply σ q)) →
      ∀ us, CParList C E (Subst.applyList σ ps) us →
        ∃ σ' : Subst sigma nu, us = Subst.applyList σ' ps ∧
          (∀ x, (∃ p ∈ ps, VarOccurs x p) → CPar C E (σ x) (σ' x)) ∧
          (∀ x, (¬ ∃ p ∈ ps, VarOccurs x p) → σ' x = σ x) := by
  intro ps
  induction ps with
  | nil =>
      intro _ _ _ us hlist
      rw [Subst.applyList_nil] at hlist
      refine ⟨σ, ?_, ?_, fun _ _ => rfl⟩
      · rw [CParList.nil_inv hlist, Subst.applyList_nil]
      · intro x hx
        obtain ⟨p, hp, -⟩ := hx
        cases hp
  | cons p ps ih =>
      intro hterm hnd hno us hlist
      rw [Subst.applyList_cons] at hlist
      obtain ⟨u, us', rfl, hu, hlist'⟩ := CParList.cons_inv hlist
      rw [List.flatMap_cons, List.nodup_append] at hnd
      obtain ⟨hndp, hndps, hdisj⟩ := hnd
      obtain ⟨σp, hup, hptp, hfixp⟩ :=
        hterm p List.mem_cons_self hndp (hno p List.mem_cons_self) u hu
      obtain ⟨σs, husp, hpts, hfixs⟩ :=
        ih (fun q hq => hterm q (List.mem_cons_of_mem p hq)) hndps
          (fun q hq => hno q (List.mem_cons_of_mem p hq)) us' hlist'
      classical
      -- a variable of `p` occurs in no later pattern
      have hsep : ∀ x, VarOccurs x p → ¬ ∃ q ∈ ps, VarOccurs x q := by
        rintro x hxp ⟨q, hq, hxq⟩
        exact hdisj x ((varOccurs_iff_mem_varOccurrences p).1 hxp) x
          (List.mem_flatMap.2 ⟨q, hq, (varOccurs_iff_mem_varOccurrences q).1 hxq⟩) rfl
      refine ⟨fun z => if VarOccurs z p then σp z else σs z, ?_, ?_, ?_⟩
      · rw [Subst.applyList_cons]
        congr 1
        · rw [hup]
          exact apply_eq_of_occurs_agree p (fun x hx => by simp [hx])
        · rw [husp, Subst.applyList_eq_map, Subst.applyList_eq_map]
          apply List.map_congr_left
          intro q hq
          exact apply_eq_of_occurs_agree q (fun x hx => by
            have hxp : ¬ VarOccurs x p := fun h => hsep x h ⟨q, hq, hx⟩
            simp [hxp])
      · rintro x ⟨q, hq, hxq⟩
        by_cases hxp : VarOccurs x p
        · simp only [if_pos hxp]
          exact hptp x hxp
        · simp only [if_neg hxp]
          rcases List.mem_cons.1 hq with rfl | hq'
          · exact absurd hxq hxp
          · exact hpts x ⟨q, hq', hxq⟩
      · intro x hx
        have hxp : ¬ VarOccurs x p := fun h => hx ⟨p, List.mem_cons_self, h⟩
        simp only [if_neg hxp]
        exact hfixs x (fun ⟨q, hq, hxq⟩ => hx ⟨q, List.mem_cons_of_mem p hq, hxq⟩)

/-- **Pattern decomposition.** A parallel step out of an instance of a left-linear
pattern, with no oracle redex at a non-variable position of the pattern, gives an
instance of the same pattern. The new substitution differs from the old one only
on the pattern's variables, where each new image is a parallel reduct of the old
one. -/
theorem cpar_pattern_decompose {C : CTRS sigma nu}
    {E : Term sigma nu → Term sigma nu → Prop} (σ : Subst sigma nu) :
    ∀ (p : Term sigma nu),
      (OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences p).Nodup →
      (∀ q, Subterm q p → q.isApp = true → ¬ IsOracleRedex C E (Subst.apply σ q)) →
      ∀ u, CPar C E (Subst.apply σ p) u →
        ∃ σ' : Subst sigma nu, u = Subst.apply σ' p ∧
          (∀ x, VarOccurs x p → CPar C E (σ x) (σ' x)) ∧
          (∀ x, ¬ VarOccurs x p → σ' x = σ x) := by
  intro p
  induction p using Term.rec' with
  | hvar y =>
      intro _ _ u hu
      classical
      refine ⟨fun z => if z = y then u else σ z, ?_, ?_, ?_⟩
      · simp
      · intro x hx
        cases hx
        simpa using hu
      · intro x hx
        have hxy : x ≠ y := fun h => hx (by subst h; exact VarOccurs.here)
        simp [hxy]
  | happ f ps ih =>
      intro hnd hno u hu
      rw [Subst.apply_app] at hu
      rcases CPar.app_inv hu with ⟨us, rfl, hlist⟩ | ⟨crule, hmem, τ, τ', hsrc, -, hconds, -⟩
      · have hnd' : (ps.flatMap OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences).Nodup := by
          rw [← varOccurrences_app_eq f ps]
          exact hnd
        obtain ⟨σ', hus, hpt, hfix⟩ := cparList_pattern_decompose σ ps ih hnd'
          (fun q hq r hr happ => hno r (Subterm.arg hq hr) happ) us hlist
        refine ⟨σ', ?_, ?_, ?_⟩
        · rw [Subst.apply_app, hus]
        · intro x hx
          obtain ⟨q, hq, hxq⟩ := hx.app_inv
          exact hpt x ⟨q, hq, hxq⟩
        · intro x hx
          exact hfix x (fun ⟨q, hq, hxq⟩ => hx (VarOccurs.arg hq hxq))
      · exact (hno _ (Subterm.refl _) rfl ⟨crule, hmem, τ, hsrc, hconds⟩).elim

/-! ## Parallel moves -/

/-- Common parallel reducts of the members of a list give a common list reduct. -/
theorem cparList_exists_target {C : CTRS sigma nu}
    {E : Term sigma nu → Term sigma nu → Prop} :
    ∀ {args : List (Term sigma nu)},
      (∀ a ∈ args, ∃ a' : Term sigma nu, ∀ u, CPar C E a u → CPar C E u a') →
      ∃ args' : List (Term sigma nu), ∀ us, CParList C E args us → CParList C E us args' := by
  intro args
  induction args with
  | nil =>
      intro _
      exact ⟨[], fun us h => by rw [CParList.nil_inv h]; exact CParList.nil⟩
  | cons a as ih =>
      intro h
      obtain ⟨a', ha'⟩ := h a List.mem_cons_self
      obtain ⟨as', has'⟩ := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
      refine ⟨a' :: as', fun us hus => ?_⟩
      obtain ⟨u, us', rfl, hu, hus'⟩ := CParList.cons_inv hus
      exact CParList.cons (ha' u hu) (has' us' hus')

/-- **Parallel moves.** For a left-linear system with the variable condition, no
feasible overlap and a stable oracle, every term has a parallel reduct that each
of its parallel reducts reaches in one parallel step.

The induction is on the size of the source term. At an oracle redex the target
contracts the redex with the targets of the matched images. A root contraction of
the same source uses the same rule (no feasible overlap at the root), with images
that agree on the left-hand-side variables. An argument step keeps the
left-hand-side pattern (`cpar_pattern_decompose`), and the stable oracle keeps
the conditions true. Every copy that a duplicating right-hand side makes of a
matched image parallel-reduces to the target of that image.

Relation: `CPar C E`, one parallel step.
Closure: context closure through `CPar.app`.
Strategy: full rewriting.
Trust: kernel checked; `Classical.choice` selects the image targets. -/
theorem cpar_exists_target {C : CTRS sigma nu} {E : Term sigma nu → Term sigma nu → Prop}
    (hlin : CLeftLinear C) (hvar : CVarCondition C) (hno : NoFeasibleOverlap C E)
    (hstab : OracleStable C E) :
    ∀ t : Term sigma nu, ∃ t' : Term sigma nu, ∀ u, CPar C E t u → CPar C E u t' := by
  intro t
  induction hn : Term.size t using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    subst hn
    classical
    by_cases hred : IsOracleRedex C E t
    · -- the source is an oracle redex: contract it with targets of the images
      obtain ⟨crule, hmem, σ, hsrc, hconds⟩ := hred
      obtain ⟨g, ps, hl⟩ : ∃ g ps, crule.lhs = Term.app g ps := by
        have happ := crule.lhs_isApp
        cases hcl : crule.lhs with
        | var z => rw [hcl] at happ; simp at happ
        | app g ps => exact ⟨g, ps, rfl⟩
      have himg : ∀ x, VarOccurs x crule.lhs →
          ∃ w : Term sigma nu, ∀ u, CPar C E (σ x) u → CPar C E u w := by
        intro x hx
        have hlt : (σ x).size < t.size := by
          rw [hsrc]
          exact hx.size_apply_lt_of_isApp crule.lhs_isApp σ
        exact ih _ hlt (σ x) rfl
      obtain ⟨σs, hσs_in, hσs_out⟩ : ∃ σs : Subst sigma nu,
          (∀ x, VarOccurs x crule.lhs → ∀ u, CPar C E (σ x) u → CPar C E u (σs x)) ∧
          (∀ x, ¬ VarOccurs x crule.lhs → σs x = σ x) := by
        refine ⟨fun x => if hx : VarOccurs x crule.lhs then Classical.choose (himg x hx)
          else σ x, ?_, ?_⟩
        · intro x hx w hw
          simp only [dif_pos hx]
          exact Classical.choose_spec (himg x hx) w hw
        · intro x hx
          simp only [dif_neg hx]
      refine ⟨Subst.apply σs crule.rhs, ?_⟩
      intro u hu
      have hu' : CPar C E (Term.app g (Subst.applyList σ ps)) u := by
        rw [hsrc, hl, Subst.apply_app] at hu
        exact hu
      rcases CPar.app_inv hu' with ⟨us, rfl, hlist⟩ |
          ⟨crule₂, hmem₂, τ, τ', hsrc₂, rfl, hconds₂, hpt₂⟩
      · -- the arguments stepped: decompose, then contract the same redex
        have hnd : (ps.flatMap OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences).Nodup := by
          have h0 : OperatorKO7.Meta.UniqueNormalization.Term.LeftLinear crule.lhs :=
            hlin crule hmem
          unfold OperatorKO7.Meta.UniqueNormalization.Term.LeftLinear at h0
          rw [hl, varOccurrences_app_eq] at h0
          exact h0
        have hinner : ∀ p ∈ ps, ∀ q, Subterm q p → q.isApp = true →
            ¬ IsOracleRedex C E (Subst.apply σ q) := by
          intro p hp q hq happ hqred
          obtain ⟨crule₃, hmem₃, τ₃, heq₃, hconds₃⟩ := hqred
          have hsub : Subterm q crule.lhs := by
            rw [hl]
            exact Subterm.arg hp hq
          obtain ⟨-, hqeq⟩ :=
            hno crule hmem crule₃ hmem₃ q hsub happ σ τ₃ heq₃ hconds hconds₃
          have hle : q.size ≤ p.size := hq.size_le
          have hlt : p.size < (Term.app g ps).size := Term.size_lt_of_mem hp
          rw [hqeq, hl] at hle
          omega
        obtain ⟨σ', hus, hpt, hfix⟩ := cparList_pattern_decompose σ ps
          (fun p _ => cpar_pattern_decompose σ p) hnd hinner us hlist
        have hocc : ∀ x, VarOccurs x crule.lhs ↔ ∃ p ∈ ps, VarOccurs x p := by
          intro x
          rw [hl]
          constructor
          · intro h
            exact h.app_inv
          · rintro ⟨p, hp, hxp⟩
            exact VarOccurs.arg hp hxp
        have hall : ∀ x, CPar C E (σ x) (σ' x) := by
          intro x
          by_cases hx : VarOccurs x crule.lhs
          · exact hpt x ((hocc x).1 hx)
          · rw [hfix x (fun h => hx ((hocc x).2 h))]
            exact CPar.refl C E (σ x)
        have hsrc' : Term.app g us = Subst.apply σ' crule.lhs := by
          rw [hl, Subst.apply_app, hus]
        rw [hsrc']
        refine CPar.root hmem σ' σs ?_ ?_
        · intro p hp
          exact hstab _ _ _ _ (hconds p hp)
            (CPar.apply_pointwise p.1 (fun x _ => hall x))
            (CPar.apply_pointwise p.2 (fun x _ => hall x))
        · intro x
          by_cases hx : VarOccurs x crule.lhs
          · exact hσs_in x hx (σ' x) (hall x)
          · rw [hfix x (fun h => hx ((hocc x).2 h)), hσs_out x hx]
            exact CPar.refl C E (σ x)
      · -- a root contraction of the same source uses the same rule
        have heq : Subst.apply σ crule.lhs = Subst.apply τ crule₂.lhs := by
          rw [hl, Subst.apply_app]
          exact hsrc₂
        obtain ⟨hrr, -⟩ := hno crule hmem crule₂ hmem₂ crule.lhs (Subterm.refl _)
          crule.lhs_isApp σ τ heq hconds hconds₂
        rw [← hrr] at heq
        rw [← hrr]
        have hag := agree_on_occurs_of_apply_eq crule.lhs heq
        refine CPar.apply_pointwise crule.rhs (fun x hx => ?_)
        have hxl : VarOccurs x crule.lhs := hvar crule hmem x hx
        have hστ : CPar C E (σ x) (τ' x) := by
          rw [hag x hxl]
          exact hpt₂ x
        exact hσs_in x hxl (τ' x) hστ
    · -- the source is not an oracle redex: reduce the arguments to their targets
      cases t with
      | var x =>
          refine ⟨Term.var x, fun u hu => ?_⟩
          rw [CPar.var_inv hu]
          exact CPar.var x
      | app f args =>
          have hargs : ∀ a ∈ args,
              ∃ w : Term sigma nu, ∀ u, CPar C E a u → CPar C E u w :=
            fun a ha => ih _ (Term.size_lt_of_mem ha) a rfl
          obtain ⟨targs, htargs⟩ := cparList_exists_target hargs
          refine ⟨Term.app f targs, fun u hu => ?_⟩
          rcases CPar.app_inv hu with ⟨us, rfl, hlist⟩ |
              ⟨crule, hmem, τ, τ', hsrc, -, hconds, -⟩
          · exact CPar.app f (htargs us hlist)
          · exact (hred ⟨crule, hmem, τ, hsrc, hconds⟩).elim

/-! ## Confluence -/

/-- **Confluence of oracle rewriting.** Under the hypotheses of the parallel
moves, the oracle step relation is confluent, with no termination hypothesis.

Relation: `CStepE C E`.
Closure: reflexive-transitive.
Strategy: full rewriting.
Trust: kernel checked. -/
theorem cstepE_relConfluent {C : CTRS sigma nu} {E : Term sigma nu → Term sigma nu → Prop}
    (hlin : CLeftLinear C) (hvar : CVarCondition C) (hno : NoFeasibleOverlap C E)
    (hstab : OracleStable C E) : relConfluent (CStepE C E) := by
  intro a b c hab hac
  have hab' : Relation.ReflTransGen (CPar C E) a b :=
    Relation.ReflTransGen.mono (fun _ _ h => CPar.of_cstepE h) hab
  have hac' : Relation.ReflTransGen (CPar C E) a c :=
    Relation.ReflTransGen.mono (fun _ _ h => CPar.of_cstepE h) hac
  obtain ⟨d, hbd, hcd⟩ := Relation.church_rosser (fun x y z hxy hxz => by
      obtain ⟨w, hw⟩ := cpar_exists_target hlin hvar hno hstab x
      exact ⟨w, Relation.ReflGen.single (hw y hxy), Relation.ReflTransGen.single (hw z hxz)⟩)
    hab' hac'
  exact ⟨d, cstepEStar_of_cparStar hbd, cstepEStar_of_cparStar hcd⟩

/-- **Confluence of semi-equational systems without feasible overlaps.** A
left-linear semi-equational conditional system with the variable condition, in
which no two rules overlap with both condition sets convertible (except a rule
with itself at the root), is confluent. Syntactic non-overlap is the case of
orthogonal semi-equational systems (Bergstra and Klop 1986, cited secondhand).

Relation: `CStep C`, the level-stratified semi-equational step relation.
Closure: reflexive-transitive.
Strategy: full rewriting.
Trust: kernel checked.
Scope: arbitrary signature and variable type; the hypothesis
`NoFeasibleOverlap C (cconv C)` mentions the conversion of `C` itself. -/
theorem cconfluent_of_noFeasibleOverlap {C : CTRS sigma nu}
    (hlin : CLeftLinear C) (hvar : CVarCondition C)
    (hno : NoFeasibleOverlap C (cconv C)) : cconfluent C := by
  have hconf := cstepE_relConfluent hlin hvar hno (oracleStable_cconv C)
  intro a b c hab hac
  obtain ⟨d, hbd, hcd⟩ := hconf a b c
    (Relation.ReflTransGen.mono (fun _ _ h => cstepE_cconv_of_cstep h) hab)
    (Relation.ReflTransGen.mono (fun _ _ h => cstepE_cconv_of_cstep h) hac)
  exact ⟨d, Relation.ReflTransGen.mono (fun _ _ h => cstep_of_cstepE_cconv h) hbd,
    Relation.ReflTransGen.mono (fun _ _ h => cstep_of_cstepE_cconv h) hcd⟩

/-- Syntactic non-overlap suffices. -/
theorem cconfluent_of_nonOverlapping {C : CTRS sigma nu}
    (hlin : CLeftLinear C) (hvar : CVarCondition C) (hno : CNonOverlapping C) :
    cconfluent C :=
  cconfluent_of_noFeasibleOverlap hlin hvar (noFeasibleOverlap_of_nonOverlapping _ hno)

/-! ## Unique normal forms of the original system -/

/-- **UN= from a linearization without feasible overlaps.**

Relation: `Step R`, through `CStep C`.
Closure: conversion.
Strategy: full rewriting.
Trust: kernel checked. -/
theorem UNconv_of_linearization_noFeasibleOverlap {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlinR : IsLinearization R C) (hll : CLeftLinear C) (hvar : CVarCondition C)
    (hno : NoFeasibleOverlap C (cconv C)) : UNconv R :=
  UNconv_of_cconfluent_linearization hlinR (cconfluent_of_noFeasibleOverlap hll hvar hno)

/-- UN-> from a linearization without feasible overlaps. -/
theorem UNred_of_linearization_noFeasibleOverlap {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlinR : IsLinearization R C) (hll : CLeftLinear C) (hvar : CVarCondition C)
    (hno : NoFeasibleOverlap C (cconv C)) : UNred R :=
  UNred_of_UNconv (UNconv_of_linearization_noFeasibleOverlap hlinR hll hvar hno)

/-- **UN= from a hub linearization without feasible overlaps.** For an arbitrary
system over `Nat` variables with the variable condition, UN= follows when the
canonical hub linearization `linHub R` has no overlap whose two condition sets
are convertible.

The hypothesis quantifies over conversions of `R` and contains instances of UN=:
for `f(x, x) -> a` beside `f(c, d) -> b` it holds exactly when `c` and `d` are not
convertible. For non-omega-overlapping `R` it restates the open part of problem
79 as a statement about the overlaps of the linearization (ledger row F63); it
is not a smaller problem.

Relation: `Step R`, through `CStep (linHub R)`.
Closure: conversion.
Strategy: full rewriting.
Trust: kernel checked.
Scope: `Nat` variables, arbitrary signature, arbitrary finite rule list. -/
theorem UNconv_of_linHub_noFeasibleOverlap {R : TRS sigma Nat}
    (hvar : ∀ rule ∈ R, ∀ x, VarOccurs x rule.rhs → VarOccurs x rule.lhs)
    (hno : NoFeasibleOverlap (linHub R) (cconv (linHub R))) : UNconv R :=
  UNconv_of_linearization_noFeasibleOverlap (isLinearization_linHub R)
    (cLeftLinear_of_isMethodLinearization (isMethodLinearization_linHub R))
    (cVarCondition_of_isLinearization (isLinearization_linHub R) hvar) hno

/-- The same statement for UN->. -/
theorem UNred_of_linHub_noFeasibleOverlap {R : TRS sigma Nat}
    (hvar : ∀ rule ∈ R, ∀ x, VarOccurs x rule.rhs → VarOccurs x rule.lhs)
    (hno : NoFeasibleOverlap (linHub R) (cconv (linHub R))) : UNred R :=
  UNred_of_UNconv (UNconv_of_linHub_noFeasibleOverlap hvar hno)

/-- **UN= for strongly non-overlapping systems.** A system with the variable
condition whose hub linearization is non-overlapping has unique normal forms with
respect to conversion. This is the strongly non-overlapping class of the
literature, cited secondhand.

Relation: `Step R`.
Closure: conversion.
Strategy: full rewriting.
Trust: kernel checked. -/
theorem UNconv_of_linHub_nonOverlapping {R : TRS sigma Nat}
    (hvar : ∀ rule ∈ R, ∀ x, VarOccurs x rule.rhs → VarOccurs x rule.lhs)
    (hno : CNonOverlapping (linHub R)) : UNconv R :=
  UNconv_of_linHub_noFeasibleOverlap hvar (noFeasibleOverlap_of_nonOverlapping _ hno)

/-! ## Flat left-hand sides -/

/-- A linearization of a flat rule is flat with the same root symbol: renaming
variables back recovers the original left-hand side, so the conditional
left-hand side is the same symbol applied to variables. -/
theorem lhs_flat_of_linearizesRule {rule : Rule sigma nu} {crule : CRule sigma nu}
    (h : LinearizesRule rule crule) {f : sigma} {args : List (Term sigma nu)}
    (hl : rule.lhs = Term.app f args) (hflat : ∀ a ∈ args, ∃ x, a = Term.var x) :
    ∃ args' : List (Term sigma nu), crule.lhs = Term.app f args' ∧
      ∀ a ∈ args', ∃ x, a = Term.var x := by
  obtain ⟨-, rho, hcollapse, -⟩ := h
  cases hcl : crule.lhs with
  | var z =>
      rw [hcl, Term.mapVar_var, hl] at hcollapse
      exact absurd hcollapse (by simp)
  | app g args' =>
      rw [hcl, Term.mapVar_app, Term.mapVarList_eq_map, hl, Term.app.injEq] at hcollapse
      obtain ⟨hg, hmap⟩ := hcollapse
      refine ⟨args', by rw [hg], fun a ha => ?_⟩
      have hmem : Term.mapVar rho a ∈ args := by
        rw [← hmap]
        exact List.mem_map_of_mem ha
      obtain ⟨x, hx⟩ := hflat _ hmem
      cases a with
      | var y => exact ⟨y, rfl⟩
      | app g' as' =>
          rw [Term.mapVar_app] at hx
          exact absurd hx (by simp)

/-- Flat left-hand sides with pairwise different root symbols do not overlap. -/
theorem cNonOverlapping_of_flat {C : CTRS sigma nu}
    (hflat : ∀ crule ∈ C, ∃ (f : sigma) (args : List (Term sigma nu)),
      crule.lhs = Term.app f args ∧ ∀ a ∈ args, ∃ x, a = Term.var x)
    (hhead : ∀ r₁ ∈ C, ∀ r₂ ∈ C, ∀ (f : sigma) (args₁ args₂ : List (Term sigma nu)),
      r₁.lhs = Term.app f args₁ → r₂.lhs = Term.app f args₂ → r₁ = r₂) :
    CNonOverlapping C := by
  intro r₁ h₁ r₂ h₂ q hq happ σ₁ σ₂ heq
  obtain ⟨f₁, args₁, hl₁, hfl₁⟩ := hflat r₁ h₁
  obtain ⟨f₂, args₂, hl₂, -⟩ := hflat r₂ h₂
  rw [hl₁] at hq
  have hq' : q = Term.app f₁ args₁ := ClassExamples.flat_app_subterm_eq hfl₁ hq happ
  rw [hq', hl₂, Subst.apply_app, Subst.apply_app] at heq
  have hf : f₁ = f₂ := (Term.app.inj heq).1
  exact ⟨hhead r₁ h₁ r₂ h₂ f₁ args₁ args₂ hl₁ (by rw [hf]; exact hl₂),
    hq'.trans hl₁.symm⟩

/-- The hub linearization of a system with flat left-hand sides and pairwise
different root symbols is non-overlapping. -/
theorem cNonOverlapping_linHub_of_flat {R : TRS sigma Nat}
    (hflat : ∀ rule ∈ R, ∃ (f : sigma) (args : List (Term sigma Nat)),
      rule.lhs = Term.app f args ∧ ∀ a ∈ args, ∃ x, a = Term.var x)
    (hhead : ∀ r₁ ∈ R, ∀ r₂ ∈ R, ∀ (f : sigma) (args₁ args₂ : List (Term sigma Nat)),
      r₁.lhs = Term.app f args₁ → r₂.lhs = Term.app f args₂ → r₁ = r₂) :
    CNonOverlapping (linHub R) := by
  apply cNonOverlapping_of_flat
  · intro crule hc
    obtain ⟨rule, hr, rfl⟩ := List.mem_map.1 hc
    obtain ⟨f, args, hl, hfl⟩ := hflat rule hr
    obtain ⟨args', h1, h2⟩ := lhs_flat_of_linearizesRule (hubCRule_linearizesRule rule) hl hfl
    exact ⟨f, args', h1, h2⟩
  · intro c₁ hc₁ c₂ hc₂ f args₁ args₂ hl₁ hl₂
    obtain ⟨r₁, hr₁, rfl⟩ := List.mem_map.1 hc₁
    obtain ⟨r₂, hr₂, rfl⟩ := List.mem_map.1 hc₂
    obtain ⟨-, rho₁, hcol₁, -⟩ := hubCRule_linearizesRule r₁
    obtain ⟨-, rho₂, hcol₂, -⟩ := hubCRule_linearizesRule r₂
    rw [hl₁, Term.mapVar_app] at hcol₁
    rw [hl₂, Term.mapVar_app] at hcol₂
    rw [hhead r₁ hr₁ r₂ hr₂ f _ _ hcol₁.symm hcol₂.symm]

/-! ## Klop's system has unique normal forms -/

namespace KlopSystem

/-- A hand-built conditional linearization of Klop's system. `A -> C(A)` and
`C(x) -> D(x, C(x))` are left-linear and stay unchanged; `D(x, x) -> E` becomes
`D(x, y) -> E` under the condition `x ~ y`, with the fresh variable `9`. -/
def linKlop : CTRS Nat Nat :=
  [ ⟨.app 0 [], .app 1 [.app 0 []], [], rfl⟩,
    ⟨.app 1 [.var 0], .app 2 [.var 0, .app 1 [.var 0]], [], rfl⟩,
    ⟨.app 2 [.var 0, .var 9], .app 3 [], [(.var 0, .var 9)], rfl⟩ ]

/-- `linKlop` is a conditional linearization of Klop's system. -/
theorem isLin_klop : IsLinearization trs linKlop := by
  have hD : LinearizesRule ruleD
      ⟨.app 2 [.var 0, .var 9], .app 3 [], [(.var 0, .var 9)], rfl⟩ :=
    linearizesRule_binaryDiagonal 2 0 9 (.app 3 [])
      (fun h => by rcases h.app_inv with ⟨a, ha, -⟩; simp at ha)
  constructor
  · intro crule hc
    simp only [linKlop, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨ruleA, List.Mem.head _, linearizesRule_self ruleA⟩
    · exact ⟨ruleC, List.Mem.tail _ (List.Mem.head _), linearizesRule_self ruleC⟩
    · exact ⟨ruleD, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), hD⟩
  · intro rule hr
    simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.Mem.head _, linearizesRule_self ruleA⟩
    · exact ⟨_, List.Mem.tail _ (List.Mem.head _), linearizesRule_self ruleC⟩
    · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), hD⟩

/-- The left-hand sides of `linKlop` are left-linear. -/
theorem linKlop_leftLinear : CLeftLinear linKlop := by
  intro crule hc
  simp only [linKlop, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;>
    simp [OperatorKO7.Meta.UniqueNormalization.Term.LeftLinear,
      OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences, List.nodup_cons]

/-- The left-hand sides of `linKlop` do not overlap: they are flat applications
with three different root symbols. -/
theorem linKlop_nonOverlapping : CNonOverlapping linKlop := by
  intro r₁ h₁ r₂ h₂ q hq happ σ₁ σ₂ heq
  simp only [linKlop, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl | rfl
  · have hq' := ClassExamples.flat_app_subterm_eq (by simp) hq happ
    subst hq'
    rcases h₂ with rfl | rfl | rfl <;> first
      | exact ⟨rfl, rfl⟩
      | simp at heq
  · have hq' := ClassExamples.flat_app_subterm_eq (by simp) hq happ
    subst hq'
    rcases h₂ with rfl | rfl | rfl <;> first
      | exact ⟨rfl, rfl⟩
      | simp at heq
  · have hq' := ClassExamples.flat_app_subterm_eq (by simp) hq happ
    subst hq'
    rcases h₂ with rfl | rfl | rfl <;> first
      | exact ⟨rfl, rfl⟩
      | simp at heq

/-- Klop's system satisfies the variable condition. -/
theorem trs_varCondition :
    ∀ rule ∈ trs, ∀ x, VarOccurs x rule.rhs → VarOccurs x rule.lhs := by
  intro rule hr x hx
  simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [varOccurs_iff_mem_varOccurrences] at hx ⊢
  rcases hr with rfl | rfl | rfl
  · simp [ruleA, OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences] at hx
  · simpa [ruleC, OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences] using hx
  · simp [ruleD, OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences] at hx

/-- `linKlop` satisfies the variable condition. -/
theorem linKlop_varCondition : CVarCondition linKlop :=
  cVarCondition_of_isLinearization isLin_klop trs_varCondition

/-- The hand-built linearization of Klop's system is confluent, although the
system itself is not. -/
theorem linKlop_cconfluent : cconfluent linKlop :=
  cconfluent_of_nonOverlapping linKlop_leftLinear linKlop_varCondition
    linKlop_nonOverlapping

/-- The left-hand sides of Klop's system are flat. -/
theorem trs_lhs_flat : ∀ rule ∈ trs, ∃ (f : Nat) (args : List (Term Nat Nat)),
    rule.lhs = Term.app f args ∧ ∀ a ∈ args, ∃ x, a = Term.var x := by
  intro rule hr
  simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨0, [], rfl, by simp⟩
  · exact ⟨1, [.var 0], rfl, by simp⟩
  · exact ⟨2, [.var 0, .var 0], rfl, by simp⟩

/-- Different rules of Klop's system have different root symbols. -/
theorem trs_lhs_head_injective :
    ∀ r₁ ∈ trs, ∀ r₂ ∈ trs, ∀ (f : Nat) (args₁ args₂ : List (Term Nat Nat)),
      r₁.lhs = Term.app f args₁ → r₂.lhs = Term.app f args₂ → r₁ = r₂ := by
  intro r₁ h₁ r₂ h₂ f args₁ args₂ hl₁ hl₂
  simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl <;> first
    | rfl
    | (simp only [ruleA, ruleC, ruleD, Term.app.injEq] at hl₁ hl₂
       exact absurd (hl₁.1.trans hl₂.1.symm) (by decide))

/-- The hub linearization of Klop's system is non-overlapping. -/
theorem linHub_trs_nonOverlapping : CNonOverlapping (linHub trs) :=
  cNonOverlapping_linHub_of_flat trs_lhs_flat trs_lhs_head_injective

/-- **The hub linearization of Klop's system is confluent**, although the system
itself is not. -/
theorem linHub_trs_cconfluent : cconfluent (linHub trs) :=
  cconfluent_of_nonOverlapping
    (cLeftLinear_of_isMethodLinearization (isMethodLinearization_linHub trs))
    (cVarCondition_of_isLinearization (isLinearization_linHub trs) trs_varCondition)
    linHub_trs_nonOverlapping

/-- **Klop's system has unique normal forms with respect to conversion**, through
the generic hub linearization. -/
theorem UNconv_trs : UNconv trs :=
  UNconv_of_linHub_nonOverlapping trs_varCondition linHub_trs_nonOverlapping

/-- Klop's system from Example 3 of Kahrs and Smith: unique normal forms hold
(this module) and confluence fails (`not_confluent` in `Examples.lean`). -/
theorem UNconv_trs_and_not_confluent :
    UNconv trs ∧ ¬ OperatorKO7.Meta.UniqueNormalization.confluent trs :=
  ⟨UNconv_trs, not_confluent⟩

end KlopSystem

/-! ## An overlap that never fires -/

namespace InfeasibleOverlap

/-- `f(x, x) -> a` beside `f(c, d) -> b`, with `f = 1`, `c = 2`, `d = 3`, `a = 4`
and `b = 5`. -/
def trs : TRS Nat Nat :=
  [ ⟨.app 1 [.var 0, .var 0], .app 4 [], rfl⟩,
    ⟨.app 1 [.app 2 [], .app 3 []], .app 5 [], rfl⟩ ]

/-- Its linearization: `f(x, y) -> a` under `x ~ y`, and `f(c, d) -> b`. -/
def lin : CTRS Nat Nat :=
  [ ⟨.app 1 [.var 0, .var 9], .app 4 [], [(.var 0, .var 9)], rfl⟩,
    ⟨.app 1 [.app 2 [], .app 3 []], .app 5 [], [], rfl⟩ ]

/-- `lin` is a conditional linearization of `trs`. -/
theorem isLin : IsLinearization trs lin := by
  have h1 : LinearizesRule (⟨.app 1 [.var 0, .var 0], .app 4 [], rfl⟩ : Rule Nat Nat)
      ⟨.app 1 [.var 0, .var 9], .app 4 [], [(.var 0, .var 9)], rfl⟩ :=
    linearizesRule_binaryDiagonal 1 0 9 (.app 4 [])
      (fun h => by rcases h.app_inv with ⟨a, ha, -⟩; simp at ha)
  have h2 : LinearizesRule (⟨.app 1 [.app 2 [], .app 3 []], .app 5 [], rfl⟩ : Rule Nat Nat)
      ⟨.app 1 [.app 2 [], .app 3 []], .app 5 [], [], rfl⟩ :=
    linearizesRule_self _
  constructor
  · intro crule hc
    simp only [lin, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_, List.Mem.head _, h1⟩
    · exact ⟨_, List.Mem.tail _ (List.Mem.head _), h2⟩
  · intro rule hr
    simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.Mem.head _, h1⟩
    · exact ⟨_, List.Mem.tail _ (List.Mem.head _), h2⟩

/-- The two left-hand sides of `trs` have no common instance: `x` cannot be both
`c` and `d`. -/
theorem trs_lhs_not_unifiable :
    ¬ Unifiable (Term.app 1 [Term.var 0, Term.var 0] : Term Nat Nat)
      (Term.app 1 [Term.app 2 [], Term.app 3 []]) := by
  rintro ⟨a, b, h⟩
  simp only [Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil, Subst.apply_var,
    Term.app.injEq, List.cons.injEq, and_true, true_and] at h
  exact absurd (h.1.symm.trans h.2) (by simp)

/-- The left-hand sides of `lin` are left-linear. -/
theorem lin_leftLinear : CLeftLinear lin := by
  intro crule hc
  simp only [lin, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;>
    simp [OperatorKO7.Meta.UniqueNormalization.Term.LeftLinear,
      OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences, List.nodup_cons]

/-- The right-hand sides of `lin` are ground. -/
theorem lin_varCondition : CVarCondition lin := by
  intro crule hc x hx
  simp only [lin, List.mem_cons, List.not_mem_nil, or_false] at hc
  rw [varOccurs_iff_mem_varOccurrences] at hx
  rcases hc with rfl | rfl <;>
    simp [OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences] at hx

/-- `lin` is not syntactically non-overlapping: `f(x, y)` and `f(c, d)` have the
common instance `f(c, d)`. -/
theorem lin_not_nonOverlapping : ¬ CNonOverlapping lin := by
  intro h
  have hbad := h ⟨.app 1 [.var 0, .var 9], .app 4 [], [(.var 0, .var 9)], rfl⟩
    (List.Mem.head _)
    ⟨.app 1 [.app 2 [], .app 3 []], .app 5 [], [], rfl⟩
    (List.Mem.tail _ (List.Mem.head _))
    (.app 1 [.var 0, .var 9]) (Subterm.refl _) rfl
    (fun v => if v = 0 then .app 2 [] else .app 3 []) (fun _ => .var 0) (by simp)
  simp at hbad

/-- The subterms of `f(c, d)`. -/
theorem subterm_cd_cases {q : Term Nat Nat}
    (hq : Subterm q (Term.app 1 [Term.app 2 [], Term.app 3 []])) :
    q = Term.app 1 [Term.app 2 [], Term.app 3 []] ∨ q = Term.app 2 [] ∨
      q = Term.app 3 [] := by
  cases hq with
  | refl => exact Or.inl rfl
  | arg ha hsa =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · cases hsa with
        | refl => exact Or.inr (Or.inl rfl)
        | arg hb _ => simp at hb
      · cases hsa with
        | refl => exact Or.inr (Or.inr rfl)
        | arg hb _ => simp at hb

/-- No conditional step leaves or enters `c`: no left-hand side and no right-hand
side is `c`, and `c` has no arguments. -/
theorem no_cstep_c (t : Term Nat Nat) :
    ¬ CStep lin (Term.app 2 []) t ∧ ¬ CStep lin t (Term.app 2 []) := by
  have hends : ∀ (E : Term Nat Nat → Term Nat Nat → Prop) (s u : Term Nat Nat),
      CStepE lin E s u → s ≠ Term.app 2 [] ∧ u ≠ Term.app 2 [] := by
    intro E s u h
    cases h with
    | root hr =>
        obtain ⟨crule, hmem, σ, hs, hu, -⟩ := hr
        simp only [lin, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl <;> (subst hs; subst hu; simp)
    | arg f pre post _ =>
        constructor <;> (intro h; simp at h)
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact hn.elim
    | succ m =>
        have hm : CStepE lin (relConv (CStepLevel lin m)) (Term.app 2 []) t := hn
        exact (hends _ _ _ hm).1 rfl
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact hn.elim
    | succ m =>
        have hm : CStepE lin (relConv (CStepLevel lin m)) t (Term.app 2 []) := hn
        exact (hends _ _ _ hm).2 rfl

/-- `c` and `d` are not convertible in `lin`: `c` has no incident step. -/
theorem not_cconv_c_d : ¬ cconv lin (Term.app 2 []) (Term.app 3 []) := by
  intro h
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨e, hce, -⟩
  · simp at heq
  · rcases hce with hce | hce
    · exact (no_cstep_c e).1 hce
    · exact (no_cstep_c e).2 hce

/-- **The overlap never fires.** The only overlap between the two rules of `lin`
asks `c ~ d`, which fails. -/
theorem lin_noFeasibleOverlap : NoFeasibleOverlap lin (cconv lin) := by
  intro r₁ h₁ r₂ h₂ q hq happ σ₁ σ₂ heq hc₁ hc₂
  simp only [lin, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl
  · -- the first rule, whose left-hand side is flat
    have hq' := ClassExamples.flat_app_subterm_eq (by simp) hq happ
    subst hq'
    rcases h₂ with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · simp only [Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
        Subst.apply_var, Term.app.injEq, List.cons.injEq, and_true, true_and] at heq
      have hc := hc₁ (.var 0, .var 9) (List.Mem.head _)
      simp only [Subst.apply_var] at hc
      rw [heq.1, heq.2] at hc
      exact absurd hc not_cconv_c_d
  · -- the second rule: its whole left-hand side, `c` or `d`
    rcases subterm_cd_cases hq with rfl | rfl | rfl
    · rcases h₂ with rfl | rfl
      · simp only [Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
          Subst.apply_var, Term.app.injEq, List.cons.injEq, and_true, true_and] at heq
        have hc := hc₂ (.var 0, .var 9) (List.Mem.head _)
        simp only [Subst.apply_var] at hc
        rw [← heq.1, ← heq.2] at hc
        exact absurd hc not_cconv_c_d
      · exact ⟨rfl, rfl⟩
    · rcases h₂ with rfl | rfl <;> simp at heq
    · rcases h₂ with rfl | rfl <;> simp at heq

/-- **A confluent linearization with an overlap.** `lin` is confluent although
its left-hand sides overlap. -/
theorem lin_cconfluent : cconfluent lin :=
  cconfluent_of_noFeasibleOverlap lin_leftLinear lin_varCondition lin_noFeasibleOverlap

/-- `trs` has unique normal forms with respect to conversion. -/
theorem UNconv_trs : UNconv trs :=
  UNconv_of_linearization_noFeasibleOverlap isLin lin_leftLinear lin_varCondition
    lin_noFeasibleOverlap

end InfeasibleOverlap

/-! ## Controls: the hypothesis fails where unique normal forms fail -/

namespace Controls

/-- The left-hand sides of the linearization of Huet's system are left-linear. -/
theorem linHuet_leftLinear : CLeftLinear linHuet := by
  intro crule hc
  simp only [linHuet, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;>
    simp [OperatorKO7.Meta.UniqueNormalization.Term.LeftLinear,
      OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences, List.nodup_cons]

/-- The right-hand sides of the linearization of Huet's system are ground. -/
theorem linHuet_varCondition : CVarCondition linHuet := by
  intro crule hc x hx
  simp only [linHuet, List.mem_cons, List.not_mem_nil, or_false] at hc
  rw [varOccurs_iff_mem_varOccurrences] at hx
  rcases hc with rfl | rfl | rfl <;>
    simp [OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences] at hx

/-- **Huet's linearization has a feasible overlap.** Its other hypotheses hold,
and it fails confluence, so the overlap of `F(x, y)` and `F(x, G(z))` is
feasible. -/
theorem linHuet_feasibleOverlap : ¬ NoFeasibleOverlap linHuet (cconv linHuet) :=
  fun h => linHuet_not_cconfluent
    (cconfluent_of_noFeasibleOverlap linHuet_leftLinear linHuet_varCondition h)

/-- The left-hand sides of the linearization of the KO7 kernel are left-linear. -/
theorem linKO7_leftLinear : CLeftLinear linKO7 := by
  intro crule hc
  simp only [linKO7, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [OperatorKO7.Meta.UniqueNormalization.Term.LeftLinear,
      OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences, List.nodup_cons]

/-- The linearization of the KO7 kernel satisfies the variable condition. -/
theorem linKO7_varCondition : CVarCondition linKO7 := by
  intro crule hc x hx
  simp only [linKO7, List.mem_cons, List.not_mem_nil, or_false] at hc
  rw [varOccurs_iff_mem_varOccurrences] at hx ⊢
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences] at hx ⊢ <;> omega

/-- **The KO7 kernel's linearization has a feasible overlap.** The diagonal fork
of the Distinction Boundary survives linearization as an overlap whose conditions
are convertible. -/
theorem linKO7_feasibleOverlap : ¬ NoFeasibleOverlap linKO7 (cconv linKO7) :=
  fun h => linKO7_not_cconfluent
    (cconfluent_of_noFeasibleOverlap linKO7_leftLinear linKO7_varCondition h)

end Controls

end OperatorKO7.Meta.UniqueNormalization

/-! ## Axiom audit -/

#print axioms OperatorKO7.Meta.UniqueNormalization.cstep_iff_cstepE_cconv
#print axioms OperatorKO7.Meta.UniqueNormalization.cpar_pattern_decompose
#print axioms OperatorKO7.Meta.UniqueNormalization.cpar_exists_target
#print axioms OperatorKO7.Meta.UniqueNormalization.cstepE_relConfluent
#print axioms OperatorKO7.Meta.UniqueNormalization.cconfluent_of_noFeasibleOverlap
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_linHub_noFeasibleOverlap
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_linHub_nonOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.cNonOverlapping_linHub_of_flat
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.linHub_trs_cconfluent
#print axioms OperatorKO7.Meta.UniqueNormalization.KlopSystem.UNconv_trs_and_not_confluent
#print axioms OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.lin_cconfluent
#print axioms OperatorKO7.Meta.UniqueNormalization.InfeasibleOverlap.UNconv_trs
#print axioms OperatorKO7.Meta.UniqueNormalization.Controls.linHuet_feasibleOverlap
#print axioms OperatorKO7.Meta.UniqueNormalization.Controls.linKO7_feasibleOverlap
