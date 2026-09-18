import OperatorKO7.Meta.UniqueNormalization.Summit
import OperatorKO7.Meta.UniqueNormalization.UnificationTransport
import OperatorKO7.Meta.UniqueNormalization.Examples
import Mathlib.Data.Fintype.EquivFin

/-!
# Proposition 22: the constructor translation is strongly almost non-omega-overlapping

Campaign: `Roadmaps\klop\ROADMAP.md`, wave 7. Source: Kahrs and Smith, FSCD 2016,
Proposition 22, p.7: "the constructor translation of an almost non-omega-overlapping
TRS is strongly almost non-omega-overlapping". Theorem 68 (p.16) consumes it in
that form.

The theorem `prop22` below assumes `NonOmegaOverlapping` and the variable condition.
The locally defined `AlmostNonOmegaOverlapping`, which tests determinism only on
finite root steps, cannot replace this assumption: `HuetTranslation` proves the
counterexample for these exact Lean objects, without a verdict on the external definition.

## Fidelity block (frozen `definitions.md`, D8, Definition 20)

> "A TRS is called strongly almost non-omega-overlapping iff (i) all omega-overlaps
> are in root position, (ii) whenever two left-hand sides are omega-unifiable then
> their rules have a common generalisation."

## The variable supply

Clause (ii) for two `R'_c` rules built from omega-unifiable patterns `G(p̄)` and
`G(q̄)` needs the generalisation `G_d(z̄) → G_c(z̄)` with `n` distinct fresh
variables; `G(x, b)` against `G(b, x)` already needs two. The source works over an
infinite variable set (D2, D3), and this module carries that as `[Infinite nu]`.
Over a one-element variable type the proposition is false.

## Transport of omega-unifiability across the translation

The constructor translation labels every symbol, so an omega-unifier of two
translated left-hand sides is a closure over the doubled signature. Convention CC1
speaks about the original signature. `omegaUnifiable_of_destructorPattern` moves
a closure across by erasing the labels, through `UnificationTransport.lean`.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v w

variable {sigma : Type u} {nu : Type v}

/-! ## Variable occurrence under relabelling -/

theorem VarOccurs.mapSym {tau : Type w} (f : sigma → tau) {x : nu} :
    ∀ {t : Term sigma nu}, VarOccurs x t → VarOccurs x (Term.mapSym f t) := by
  intro t h
  induction h with
  | here => exact VarOccurs.here
  | @arg g args a ha _ ih =>
      refine VarOccurs.arg (f := f g) ?_ ih
      rw [Term.mapSymList_eq_map]
      exact List.mem_map_of_mem ha

theorem VarOccurs.of_mapSym {tau : Type w} (f : sigma → tau) {x : nu} :
    ∀ {t : Term sigma nu}, VarOccurs x (Term.mapSym f t) → VarOccurs x t := by
  intro t
  induction t using Term.rec' with
  | hvar y =>
      intro h
      simp only [Term.mapSym_var] at h
      cases h
      exact VarOccurs.here
  | happ g args ih =>
      intro h
      simp only [Term.mapSym_app] at h
      obtain ⟨a', ha', hx⟩ := h.app_inv
      rw [Term.mapSymList_eq_map] at ha'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
      exact VarOccurs.arg ha (ih a ha hx)

theorem varOccurs_destructorPattern {x : nu} :
    ∀ {t : Term sigma nu}, VarOccurs x t → VarOccurs x (destructorPattern t) := by
  intro t h
  cases h with
  | here => exact VarOccurs.here
  | @arg g args a ha hx =>
      simp only [destructorPattern_app]
      refine VarOccurs.arg (f := Sum.inr g) ?_ (hx.mapSym Sum.inl)
      rw [Term.mapSymList_eq_map]
      exact List.mem_map_of_mem ha

theorem varOccurs_of_destructorPattern {x : nu} :
    ∀ {t : Term sigma nu}, VarOccurs x (destructorPattern t) → VarOccurs x t := by
  intro t h
  cases t with
  | var y =>
      have h' : VarOccurs x (Term.var (sigma := sigma ⊕ sigma) y) := h
      cases h'
      exact VarOccurs.here
  | app g args =>
      rw [destructorPattern_app] at h
      obtain ⟨a', ha', hx⟩ := h.app_inv
      rw [Term.mapSymList_eq_map] at ha'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
      exact VarOccurs.arg ha (VarOccurs.of_mapSym Sum.inl hx)

/-! ## Agreement on occurring variables -/

theorem map_eq_map_pointwise {alpha : Type u} {beta : Type v} {f g : alpha → beta} :
    ∀ {l : List alpha}, l.map f = l.map g → ∀ c ∈ l, f c = g c := by
  intro l
  induction l with
  | nil => intro _ c hc; simp at hc
  | cons a as ih =>
      intro h c hc
      simp only [List.map_cons, List.cons.injEq] at h
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact h.1
      · exact ih h.2 c hc'

/-- Substitutions agreeing on a term agree on every variable occurring in it. -/
theorem agree_of_apply_eq_occurs {a b : Subst sigma nu} :
    ∀ (t : Term sigma nu), Subst.apply a t = Subst.apply b t →
      ∀ x, VarOccurs x t → a x = b x := by
  intro t
  induction t using Term.rec' with
  | hvar y =>
      intro h x hx
      cases hx
      simpa using h
  | happ f args ih =>
      intro h x hx
      simp only [Subst.apply_app, Subst.applyList_eq_map, Term.app.injEq, true_and] at h
      obtain ⟨c, hc, hxc⟩ := hx.app_inv
      exact ih c hc (map_eq_map_pointwise h c hc) x hxc

/-- Occurrence inclusion gives the variable condition. -/
theorem determinedBy_of_occurs_subset {r l : Term sigma nu}
    (h : ∀ x, VarOccurs x r → VarOccurs x l) : Term.DeterminedBy r l :=
  fun _ _ hab => apply_eq_of_occurs_agree r
    (fun x hx => agree_of_apply_eq_occurs l hab x (h x hx))

/-! ## The variable condition gives occurrence inclusion

A substitution that grows one variable strictly enlarges every term in which that
variable occurs, and leaves every other term alone. -/

/-- A substitution never shrinks a term. -/
theorem size_le_size_apply (s : Subst sigma nu) :
    ∀ t : Term sigma nu, t.size ≤ (Subst.apply s t).size := by
  intro t
  induction t using Term.rec' with
  | hvar x => simpa using Term.one_le_size (s x)
  | happ f args ih =>
      simp only [Subst.apply_app, Subst.applyList_eq_map, Term.size_app]
      have hl : ∀ (l : List (Term sigma nu)), (∀ c ∈ l, c.size ≤ (Subst.apply s c).size) →
          Term.sizeList l ≤ Term.sizeList (l.map (Subst.apply s)) := by
        intro l
        induction l with
        | nil => intro _; simp
        | cons c cs ihl =>
            intro hmem
            simp only [List.map_cons, Term.sizeList_cons]
            have h1 := hmem c (List.mem_cons_self ..)
            have h2 := ihl (fun q hq => hmem q (List.mem_cons_of_mem _ hq))
            omega
      have := hl args ih
      omega

/-- A substitution never shrinks an argument list. -/
theorem sizeList_le_sizeList_map (s : Subst sigma nu) :
    ∀ l : List (Term sigma nu), Term.sizeList l ≤ Term.sizeList (l.map (Subst.apply s)) := by
  intro l
  induction l with
  | nil => simp
  | cons c cs ih =>
      simp only [List.map_cons, Term.sizeList_cons]
      have := size_le_size_apply s c
      omega

open scoped Classical in
/-- The substitution sending `x` to `f(x)` and fixing every other variable. -/
noncomputable def growAt (x : nu) (f : sigma) : Subst sigma nu :=
  fun y => if y = x then Term.app f [Term.var x] else Term.var y

open scoped Classical in
theorem growAt_self (x : nu) (f : sigma) : growAt x f x = Term.app f [Term.var x] := by
  simp [growAt]

open scoped Classical in
theorem growAt_of_ne {x y : nu} (f : sigma) (h : y ≠ x) : growAt x f y = Term.var y := by
  simp [growAt, h]

theorem size_lt_size_apply_growAt {x : nu} (f : sigma) :
    ∀ {t : Term sigma nu}, VarOccurs x t → t.size < (Subst.apply (growAt x f) t).size := by
  intro t h
  induction h with
  | here =>
      rw [Subst.apply_var, growAt_self]
      simp
  | @arg g args a ha _ ih =>
      simp only [Subst.apply_app, Subst.applyList_eq_map, Term.size_app]
      have hl : ∀ (l : List (Term sigma nu)), a ∈ l →
          Term.sizeList l < Term.sizeList (l.map (Subst.apply (growAt x f))) := by
        intro l
        induction l with
        | nil => intro h; simp at h
        | cons c cs ihl =>
            intro hmem
            simp only [List.map_cons, Term.sizeList_cons]
            rcases List.mem_cons.mp hmem with rfl | hmem'
            · have h2 := sizeList_le_sizeList_map (growAt x f) cs
              omega
            · have h1 := size_le_size_apply (growAt x f) c
              have h2 := ihl hmem'
              omega
      have := hl args ha
      omega

/-- The variable condition forces every right-hand side variable to occur on the
left. The symbol `f` supplies a term other than the variable itself. -/
theorem occurs_of_determinedBy (f : sigma) {r l : Term sigma nu}
    (h : Term.DeterminedBy r l) {x : nu} (hx : VarOccurs x r) : VarOccurs x l := by
  classical
  by_contra hnl
  have hagree : Subst.apply Subst.id l = Subst.apply (growAt x f) l := by
    refine apply_eq_of_occurs_agree l ?_
    intro y hy
    have hyx : y ≠ x := fun hyx => hnl (hyx ▸ hy)
    rw [growAt_of_ne f hyx]
    rfl
  have heq := h _ _ hagree
  rw [Subst.id_apply] at heq
  have hlt := size_lt_size_apply_growAt (x := x) f hx
  rw [← heq] at hlt
  exact lt_irrefl _ hlt

/-! ## The variable condition survives the translation -/

/-- A rule's left-hand side is an application. -/
theorem Rule.lhs_app (rule : Rule sigma nu) :
    ∃ (f : sigma) (args : List (Term sigma nu)), rule.lhs = .app f args := by
  have h := rule.lhs_isApp
  cases hl : rule.lhs with
  | var x => rw [hl] at h; simp at h
  | app f args => exact ⟨f, args, rfl⟩

theorem transRule_occurs {rule : Rule sigma nu} (h : Rule.RhsDetermined rule) {x : nu}
    (hx : VarOccurs x (transRule rule).rhs) : VarOccurs x (transRule rule).lhs := by
  obtain ⟨f, args, hl⟩ := Rule.lhs_app rule
  have hr : VarOccurs x rule.rhs := VarOccurs.of_mapSym Sum.inr hx
  exact varOccurs_destructorPattern (occurs_of_determinedBy f h hr)

theorem transRule_rhsDetermined {rule : Rule sigma nu} (h : Rule.RhsDetermined rule) :
    Rule.RhsDetermined (transRule rule) :=
  determinedBy_of_occurs_subset (fun _ hx => transRule_occurs h hx)

/-! ## Pattern nodes are proper subterms -/

theorem subterm_of_mem_appNodes {n : sigma × List (Term sigma nu)} :
    ∀ {t : Term sigma nu}, n ∈ appNodes t → Subterm (Term.app n.1 n.2) t := by
  intro t
  induction t using Term.rec' with
  | hvar x => intro h; simp at h
  | happ f args ih =>
      intro h
      simp only [appNodes_app, List.mem_cons] at h
      rcases h with rfl | h'
      · exact Subterm.refl _
      · have : ∃ a ∈ args, n ∈ appNodes a := by
          clear ih
          induction args with
          | nil => simp at h'
          | cons b bs ihb =>
              simp only [appNodesList_cons, List.mem_append] at h'
              rcases h' with h1 | h2
              · exact ⟨b, List.mem_cons_self .., h1⟩
              · obtain ⟨a, ha, hn⟩ := ihb h2
                exact ⟨a, List.mem_cons_of_mem _ ha, hn⟩
        obtain ⟨a, ha, hn⟩ := this
        exact Subterm.arg ha (ih a ha hn)

theorem properSubterm_of_mem_properAppNodes {n : sigma × List (Term sigma nu)}
    {t : Term sigma nu} (h : n ∈ properAppNodes t) : ProperSubterm (Term.app n.1 n.2) t := by
  cases t with
  | var x => simp [properAppNodes] at h
  | app f args =>
      simp only [properAppNodes_app] at h
      have : ∃ a ∈ args, n ∈ appNodes a := by
        induction args with
        | nil => simp at h
        | cons b bs ihb =>
            simp only [appNodesList_cons, List.mem_append] at h
            rcases h with h1 | h2
            · exact ⟨b, List.mem_cons_self .., h1⟩
            · obtain ⟨a, ha, hn⟩ := ihb h2
              exact ⟨a, List.mem_cons_of_mem _ ha, hn⟩
      obtain ⟨a, ha, hn⟩ := this
      exact ⟨f, args, a, rfl, ha, subterm_of_mem_appNodes hn⟩

theorem exists_rule_of_mem_patternNodes {R : TRS sigma nu}
    {n : sigma × List (Term sigma nu)} (h : n ∈ patternNodes R) :
    ∃ rule ∈ R, ProperSubterm (Term.app n.1 n.2) rule.lhs := by
  induction R with
  | nil => simp [patternNodes] at h
  | cons r rest ih =>
      simp only [patternNodes, List.mem_append] at h
      rcases h with h1 | h2
      · exact ⟨r, List.mem_cons_self .., properSubterm_of_mem_properAppNodes h1⟩
      · obtain ⟨rule, hmem, hp⟩ := ih h2
        exact ⟨rule, List.mem_cons_of_mem _ hmem, hp⟩


/-! ## Subterms of constructor terms -/

theorem ConOnly.subterm {s : Term (sigma ⊕ sigma) nu} :
    ∀ {t : Term (sigma ⊕ sigma) nu}, Subterm s t → ConOnly t → ConOnly s := by
  intro t h
  induction h with
  | refl => exact id
  | @arg a f args hmem _ ih =>
      intro ht
      obtain ⟨c, -, hargs⟩ := ht.app_inv
      exact ih (hargs a hmem)

/-! ## Omega-unifiability descends from the translated left-hand sides -/

theorem omegaUnifiable_of_destructorPattern {l l' : Term sigma nu}
    (h : OmegaUnifiable (destructorPattern l) (destructorPattern l')) :
    OmegaUnifiable l l' := by
  have := omegaUnifiable_eraseLabel h
  rwa [eraseLabel_destructorPattern, eraseLabel_destructorPattern] at this

/-! ## Clause (i): every omega-overlap of the translation sits at the root -/

theorem prop22_root_overlaps {R : TRS sigma nu} :
    ∀ r₁ ∈ constructorTranslation R, ∀ r₂ ∈ constructorTranslation R,
      ∀ s : Term (sigma ⊕ sigma) nu, ProperSubterm s r₁.lhs → s.isApp = true →
        ¬ OmegaUnifiable s r₂.lhs := by
  intro r₁ h₁ r₂ h₂ s hsub happ hou
  obtain ⟨F, ps, hlhs₁, hps⟩ := constructorRules_constructorTranslation R r₁ h₁
  obtain ⟨G, qs, hlhs₂, -⟩ := constructorRules_constructorTranslation R r₂ h₂
  obtain ⟨f, args, a, hr, ha, hsa⟩ := hsub
  rw [hlhs₁] at hr
  simp only [Term.app.injEq] at hr
  obtain ⟨-, hargs⟩ := hr
  subst hargs
  have hcon : ConOnly s := ConOnly.subterm hsa (hps a ha)
  cases s with
  | var x => simp at happ
  | app g xs =>
      obtain ⟨c, rfl, -⟩ := hcon.app_inv
      rw [hlhs₂] at hou
      have := root_eq_of_omegaUnifiable hou
      simp at this

/-! ## Clause (ii), two translated rules: the same rule twice -/

theorem prop22_rule_rule {R : TRS sigma nu} (hno : NonOmegaOverlapping R)
    (hvar : TRS.RhsDetermined R) {r r' : Rule sigma nu} (hr : r ∈ R) (hr' : r' ∈ R)
    (h : OmegaUnifiable (transRule r).lhs (transRule r').lhs) :
    ∃ g : CommonGeneralisation (transRule r) (transRule r'),
      ∀ x : nu, VarOccurs x g.gr → VarOccurs x g.gl := by
  have hou : OmegaUnifiable r.lhs r'.lhs := omegaUnifiable_of_destructorPattern h
  obtain ⟨rfl, -⟩ := hno r hr r' hr' r.lhs (Subterm.refl _) r.lhs_isApp hou
  exact ⟨CommonGeneralisation.self _ (transRule_rhsDetermined (hvar r hr)),
    fun _ hx => transRule_occurs (hvar r hr) hx⟩

/-! ## Clause (ii), a translated rule against a pattern rule: impossible -/

theorem prop22_rule_pattern {R : TRS sigma nu} (hno : NonOmegaOverlapping R)
    {r : Rule sigma nu} (hr : r ∈ R) {n : sigma × List (Term sigma nu)}
    (hn : n ∈ patternNodes R)
    (h : OmegaUnifiable (transRule r).lhs (patternRuleOf n).lhs) : False := by
  obtain ⟨r'', hr'', hprop⟩ := exists_rule_of_mem_patternNodes hn
  have hpat : (patternRuleOf n).lhs = destructorPattern (Term.app n.1 n.2) := rfl
  rw [hpat] at h
  have hou : OmegaUnifiable r.lhs (Term.app n.1 n.2) := omegaUnifiable_of_destructorPattern h
  obtain ⟨-, heq⟩ :=
    hno r'' hr'' r hr (Term.app n.1 n.2) (Subterm.of_properSubterm hprop) rfl hou.symm
  have hlt := hprop.size_lt
  rw [heq] at hlt
  exact lt_irrefl _ hlt

/-! ## Clause (ii), two pattern rules: a generalisation over fresh variables -/

/-- A substitution reading its values off a list, indexed through an injection of
the naturals into the variables. -/
noncomputable def listSubst [Nonempty nu] (emb : ℕ → nu)
    (L : List (Term (sigma ⊕ sigma) nu)) : Subst (sigma ⊕ sigma) nu :=
  fun z => L.getD (Function.invFun emb z) (Term.var z)

theorem map_listSubst_range [Nonempty nu] {emb : ℕ → nu} (hinj : Function.Injective emb)
    (L : List (Term (sigma ⊕ sigma) nu)) :
    ((List.range L.length).map emb).map (listSubst emb L) = L := by
  rw [List.map_map]
  refine List.ext_getElem ?_ ?_
  · simp [List.length_range]
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, listSubst]
    rw [Function.leftInverse_invFun hinj i, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h₂]
    rfl

/-- The fresh-variable list. -/
noncomputable def freshVars (emb : ℕ → nu) (k : ℕ) : List (Term (sigma ⊕ sigma) nu) :=
  ((List.range k).map emb).map Term.var

theorem apply_freshVars (emb : ℕ → nu) (k : ℕ) (s : Subst (sigma ⊕ sigma) nu) :
    Subst.applyList s (freshVars (sigma := sigma) emb k) = ((List.range k).map emb).map s := by
  rw [Subst.applyList_eq_map, freshVars, List.map_map]
  rfl

theorem varOccurs_app_of_app {x : nu} {f g : sigma ⊕ sigma}
    {args : List (Term (sigma ⊕ sigma) nu)} (h : VarOccurs x (Term.app f args)) :
    VarOccurs x (Term.app g args) := by
  obtain ⟨a, ha, hx⟩ := h.app_inv
  exact VarOccurs.arg ha hx

theorem length_eq_of_omegaUnifiable {f g : sigma ⊕ sigma}
    {xs ys : List (Term (sigma ⊕ sigma) nu)}
    (h : OmegaUnifiable (Term.app f xs) (Term.app g ys)) : xs.length = ys.length := by
  obtain ⟨E, hE, hst⟩ := h
  unfold leftCopy rightCopy at hst
  simp only [Term.mapVar_app, Term.mapVarList_eq_map] at hst
  have := (hE.args_forall₂ hst).length_eq
  simpa using this

theorem prop22_pattern_pattern [Infinite nu] {n m : sigma × List (Term sigma nu)}
    (h : OmegaUnifiable (patternRuleOf n).lhs (patternRuleOf m).lhs) :
    ∃ g : CommonGeneralisation (patternRuleOf n) (patternRuleOf m),
      ∀ x : nu, VarOccurs x g.gr → VarOccurs x g.gl := by
  have hroot := root_eq_of_omegaUnifiable h
  have hG : n.1 = m.1 := by simpa using hroot
  have hlen : (Term.mapSymList Sum.inl n.2).length = (Term.mapSymList Sum.inl m.2).length :=
    length_eq_of_omegaUnifiable h
  let emb : ℕ → nu := Infinite.natEmbedding nu
  have hinj : Function.Injective emb := (Infinite.natEmbedding nu).injective
  haveI : Nonempty nu := ⟨emb 0⟩
  set L₁ : List (Term (sigma ⊕ sigma) nu) := Term.mapSymList Sum.inl n.2 with hL₁
  set L₂ : List (Term (sigma ⊕ sigma) nu) := Term.mapSymList Sum.inl m.2 with hL₂
  set k := L₁.length with hk
  have hk₂ : L₂.length = k := hlen.symm
  have hmap₁ : ((List.range k).map emb).map (listSubst emb L₁) = L₁ :=
    map_listSubst_range hinj L₁
  have hmap₂ : ((List.range k).map emb).map (listSubst emb L₂) = L₂ := by
    rw [← hk₂]; exact map_listSubst_range hinj L₂
  refine ⟨{ gl := Term.app (Sum.inr n.1) (freshVars emb k)
            gr := Term.app (Sum.inl n.1) (freshVars emb k)
            s₁ := listSubst emb L₁
            s₂ := listSubst emb L₂
            apply_gl₁ := ?_
            apply_gl₂ := ?_
            apply_gr₁ := ?_
            apply_gr₂ := ?_
            determined := determinedBy_of_occurs_subset (fun _ hx => varOccurs_app_of_app hx) },
    fun _ hx => varOccurs_app_of_app hx⟩
  · show Term.app (Sum.inr n.1) (Subst.applyList _ _) = Term.app (Sum.inr n.1) L₁
    rw [apply_freshVars, hmap₁]
  · show Term.app (Sum.inr n.1) (Subst.applyList _ _) = Term.app (Sum.inr m.1) L₂
    rw [apply_freshVars, hmap₂, hG]
  · show Term.app (Sum.inl n.1) (Subst.applyList _ _) = Term.app (Sum.inl n.1) L₁
    rw [apply_freshVars, hmap₁]
  · show Term.app (Sum.inl n.1) (Subst.applyList _ _) = Term.app (Sum.inl m.1) L₂
    rw [apply_freshVars, hmap₂, hG]

/-! ## Proposition 22 -/

/-- **Proposition 22.** The constructor translation of a non-omega-overlapping
system meeting the variable condition is strongly almost non-omega-overlapping.
The variable supply `[Infinite nu]` is the source's infinite variable set. -/
theorem prop22 [Infinite nu] {R : TRS sigma nu} (hno : NonOmegaOverlapping R)
    (hvar : TRS.RhsDetermined R) :
    StronglyAlmostNonOmegaOverlapping (constructorTranslation R) := by
  refine ⟨prop22_root_overlaps, ?_⟩
  intro r₁ h₁ r₂ h₂ hou
  rcases mem_constructorTranslation h₁ with ⟨r, hr, rfl⟩ | ⟨n, hn, rfl⟩
  · rcases mem_constructorTranslation h₂ with ⟨r', hr', rfl⟩ | ⟨m, hm, rfl⟩
    · exact prop22_rule_rule hno hvar hr hr' hou
    · exact (prop22_rule_pattern hno hr hm hou).elim
  · rcases mem_constructorTranslation h₂ with ⟨r', hr', rfl⟩ | ⟨m, hm, rfl⟩
    · exact (prop22_rule_pattern hno hr' hn hou.symm).elim
    · exact prop22_pattern_pattern hou

/-- **Corollary 45 on the constructor translation.** With Proposition 22, `⇓` is a
consistency invariant on the constructor translation of every system in the
class. -/
theorem consistencyInvariant_constructorTranslation [Infinite nu] {R : TRS sigma nu}
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) :
    ConsistencyInvariant (constructorTranslation R) (Down (constructorTranslation R)) :=
  cor45 (constructorRules_constructorTranslation R) (prop22 hno hvar)

/-! ## The finite-root almost predicate does not suffice for this translation -/

namespace HuetTranslation

/-- Destructor label for F, constructor labels for the symbols inside its arguments. -/
def rootRoleLabel (n : Nat) : Nat ⊕ Nat :=
  if n = 1 then .inr n else .inl n

theorem map_lhs_AA :
    Term.mapSym rootRoleLabel HuetSystem.ruleAA.lhs = (transRule HuetSystem.ruleAA).lhs :=
  rfl

theorem map_lhs_AB :
    Term.mapSym rootRoleLabel HuetSystem.ruleAB.lhs = (transRule HuetSystem.ruleAB).lhs :=
  rfl

theorem translated_lhs_omegaUnifiable :
    OmegaUnifiable (transRule HuetSystem.ruleAA).lhs (transRule HuetSystem.ruleAB).lhs := by
  have h := omegaUnifiable_mapSym rootRoleLabel Huet.lhs_omegaUnifiable
  change OmegaUnifiable (Term.mapSym rootRoleLabel HuetSystem.ruleAA.lhs)
    (Term.mapSym rootRoleLabel HuetSystem.ruleAB.lhs) at h
  rw [map_lhs_AA, map_lhs_AB] at h
  exact h

theorem translated_rules_no_common_generalisation :
    ¬ Nonempty (CommonGeneralisation (transRule HuetSystem.ruleAA)
      (transRule HuetSystem.ruleAB)) := by
  refine ClassExamples.noCommonGeneralisation_of_distinct_nullary_rhs
    (f := Sum.inr 3) (g := Sum.inr 4) (by decide) rfl rfl ?_
  intro hs
  have heq := ClassExamples.flat_app_subterm_eq
    (fun a ha => ⟨0, by simpa using ha⟩) hs rfl
  change (Term.app (Sum.inr 3) [] : Term (Nat ⊕ Nat) Nat) =
    .app (Sum.inr 1) [.var 0, .var 0] at heq
  simp at heq

theorem not_stronglyAlmostNonOmegaOverlapping :
    ¬ StronglyAlmostNonOmegaOverlapping (constructorTranslation HuetSystem.trs) := by
  intro h
  obtain ⟨cg, _⟩ := h.2 (transRule HuetSystem.ruleAA)
    (transRule_mem (by simp [HuetSystem.trs])) (transRule HuetSystem.ruleAB)
    (transRule_mem (by simp [HuetSystem.trs])) translated_lhs_omegaUnifiable
  exact translated_rules_no_common_generalisation ⟨cg⟩

/-- A counterexample about the current Lean finite-root predicate, not a
refutation of an externally specified almost class. -/
theorem finite_root_almost_counterexample :
    AlmostNonOmegaOverlapping HuetSystem.trs ∧ TRS.RhsDetermined HuetSystem.trs ∧
      ¬ StronglyAlmostNonOmegaOverlapping (constructorTranslation HuetSystem.trs) :=
  ⟨HuetSystem.almostNonOmegaOverlapping, HuetSystem.rhsDetermined,
    not_stronglyAlmostNonOmegaOverlapping⟩

theorem current_almost_translation_implication_false :
    ¬ (∀ R : TRS Nat Nat, AlmostNonOmegaOverlapping R → TRS.RhsDetermined R →
      StronglyAlmostNonOmegaOverlapping (constructorTranslation R)) := by
  intro h
  exact not_stronglyAlmostNonOmegaOverlapping
    (h HuetSystem.trs HuetSystem.almostNonOmegaOverlapping HuetSystem.rhsDetermined)

end HuetTranslation

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.prop22
#check @OperatorKO7.Meta.UniqueNormalization.consistencyInvariant_constructorTranslation

#print axioms OperatorKO7.Meta.UniqueNormalization.prop22_root_overlaps
#print axioms OperatorKO7.Meta.UniqueNormalization.prop22_rule_rule
#print axioms OperatorKO7.Meta.UniqueNormalization.prop22_rule_pattern
#print axioms OperatorKO7.Meta.UniqueNormalization.prop22_pattern_pattern
#print axioms OperatorKO7.Meta.UniqueNormalization.prop22
#print axioms OperatorKO7.Meta.UniqueNormalization.consistencyInvariant_constructorTranslation
