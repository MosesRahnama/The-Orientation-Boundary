import OperatorKO7.Meta.UniqueNormalization.SignatureExtension
import OperatorKO7.Meta.UniqueNormalization.Section7TightClosure
import OperatorKO7.Meta.UniqueNormalization.CertificateCarrierClassification
import OperatorKO7.Meta.UniqueNormalization.Fence

/-!
# Unique normal forms for the descending subclass of Problem 79

The tight-closure consistency theorem supplies a consistent equational theory
for constructor systems whose right-hand-side destructor symbols strictly
descend. This module lifts that fact through constructor translation and the
Theorem 69 signature extension, so a non-omega-overlapping, right-variable-safe
source system whose constructor translation is descending has unique normal
forms under conversion.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting
open CertificateCapacity

universe u u' v

variable {sigma : Type u} {nu : Type v}

/-! ## Occurrence of a function symbol -/

/-- A function symbol heads some application node of the term. -/
def SymbolOccurs (g : sigma) (t : Term sigma nu) : Prop :=
  ∃ args, (g, args) ∈ appNodes t

theorem SymbolOccurs.here {g : sigma} {args : List (Term sigma nu)} :
    SymbolOccurs g (.app g args) :=
  ⟨args, List.Mem.head _⟩

theorem SymbolOccurs.of_arg {g f : sigma} {args : List (Term sigma nu)}
    {a : Term sigma nu} (ha : a ∈ args) (h : SymbolOccurs g a) :
    SymbolOccurs g (.app f args) := by
  obtain ⟨as, hmem⟩ := h
  exact ⟨as, List.mem_cons_of_mem _ (mem_appNodesList_of_mem ha hmem)⟩

/-! ## Lift of a well-founded order to the Theorem 69 signature -/

/-- On old symbols the order is the source order; every pair that mentions a
frozen variable or the fresh symbol is empty. -/
def extLt (lt : sigma → sigma → Prop) : ExtSym sigma nu → ExtSym sigma nu → Prop
  | .inl a, .inl b => lt a b
  | _, _ => False

/-- Accessibility on `Sum.inl` follows accessibility of `lt`; every `Sum.inr`
symbol has no predecessor. -/
theorem wellFounded_extLt {lt : sigma → sigma → Prop} (hwf : WellFounded lt) :
    WellFounded (extLt (nu := nu) lt) := by
  have acc_inl : ∀ a, Acc lt a → Acc (extLt (nu := nu) lt) (Sum.inl a) := by
    intro a ha
    induction ha with
    | intro a _ ih =>
        refine Acc.intro (Sum.inl a) (fun y hy => ?_)
        cases y with
        | inl b => exact ih b hy
        | inr _ => exact False.elim hy
  refine ⟨fun x => ?_⟩
  cases x with
  | inl a => exact acc_inl a (hwf.apply a)
  | inr z =>
      refine Acc.intro (Sum.inr z) (fun y hy => ?_)
      cases y with
      | inl _ => exact False.elim hy
      | inr _ => exact False.elim hy

/-! ## Uniqueness from consistency of one extension -/

/--
Proves: unique normal forms under conversion, from consistency of the Theorem 69
extension of each pair of distinct convertible normal forms.
Does not prove: uniqueness from a universal consistency theorem on every system
of the class; the class hypothesis is applied to that extension alone.
Relation: `conv R`.
Closure: full contextual rewriting.
Strategy: full rewriting.
Trust: kernel-only.
Scope: two distinct variables; the extension is `extSystem` on `ExtSym`.
-/
theorem UNconv_of_extension_consistent [Nontrivial nu] {R : TRS sigma nu}
    (hclass : ∀ t u : Term sigma nu, NormalForm R t → NormalForm R u →
      conv R t u → t ≠ u →
      ∃ x y : nu, x ≠ y ∧
        NonOmegaOverlapping (extSystem R t u x y) ∧
        TRS.RhsDetermined (extSystem R t u x y) ∧
        Consistent (extSystem R t u x y)) :
    UNconv R := by
  intro t u ht hu hconv
  by_contra hne
  obtain ⟨x, y, hxy, _hnoE, _hvarE, hcon⟩ := hclass t u ht hu hconv hne
  exact hxy (hcon x y (conv_var_var_ext x y hconv))

/-- The same per-extension consistency hypothesis gives unique normal forms
with respect to reduction. -/
theorem UNred_of_extension_consistent [Nontrivial nu] {R : TRS sigma nu}
    (hclass : ∀ t u : Term sigma nu, NormalForm R t → NormalForm R u →
      conv R t u → t ≠ u →
      ∃ x y : nu, x ≠ y ∧
        NonOmegaOverlapping (extSystem R t u x y) ∧
        TRS.RhsDetermined (extSystem R t u x y) ∧
        Consistent (extSystem R t u x y)) :
    UNred R :=
  UNred_of_UNconv (UNconv_of_extension_consistent hclass)

/-! ## Transport of syntactic descent along the signature inclusion -/

private theorem destructorLabel_mapSym_inl (t : Term sigma nu) :
    destructorLabel (Term.mapSym (Sum.inl : sigma → ExtSym sigma nu) t) =
      Term.mapSym (Sum.map (Sum.inl : sigma → ExtSym sigma nu) Sum.inl)
        (destructorLabel t) := by
  simp only [destructorLabel, Term.mapSym_mapSym]
  rfl

private theorem SymbolsSatisfy.mapSym_sumMap {tau : Type u'}
    {P : sigma ⊕ sigma → Prop} {Q : tau ⊕ tau → Prop} (f : sigma → tau)
    (hPQ : ∀ s, P s → Q (Sum.map f f s)) :
    ∀ t : Term (sigma ⊕ sigma) nu,
      SymbolsSatisfy P t → SymbolsSatisfy Q (Term.mapSym (Sum.map f f) t) := by
  intro t ht
  induction t using Term.rec' with
  | hvar x =>
      cases ht
      exact .var x
  | happ g args ih =>
      obtain ⟨hg, hargs⟩ := SymbolsSatisfy.app_iff.mp ht
      rw [Term.mapSym_app]
      refine .app (hPQ g hg) ?_
      intro a ha
      rw [Term.mapSymList_eq_map] at ha
      obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
      exact ih a0 ha0 (hargs a0 ha0)

private theorem symbolsSatisfy_destructorLabel_lift
    {P : sigma ⊕ sigma → Prop}
    {Q : ExtSym sigma nu ⊕ ExtSym sigma nu → Prop}
    (hQin : ∀ c, Q (.inl c))
    (hPQ : ∀ g, P (.inr g) → Q (.inr (.inl g)))
    {t : Term sigma nu}
    (h : SymbolsSatisfy P (destructorLabel t)) :
    SymbolsSatisfy Q (destructorLabel (Term.mapSym (Sum.inl : sigma → ExtSym sigma nu) t)) := by
  rw [destructorLabel_mapSym_inl]
  refine SymbolsSatisfy.mapSym_sumMap (Sum.inl : sigma → ExtSym sigma nu) ?_ _ h
  intro s hs
  cases s with
  | inl c => exact hQin _
  | inr e => exact hPQ e hs

private theorem transRule_mapInl_rhs (r : Rule sigma nu) :
    (transRule (Rule.mapSym (Sum.inl : sigma → ExtSym sigma nu) r)).rhs =
      destructorLabel (Term.mapSym Sum.inl r.rhs) :=
  rfl

private theorem transRule_mapInl_lhs {r : Rule sigma nu} {f : sigma}
    {args : List (Term sigma nu)} (hlhs : r.lhs = .app f args) :
    (transRule (Rule.mapSym (Sum.inl : sigma → ExtSym sigma nu) r)).lhs =
      .app (.inr (.inl f))
        (Term.mapSymList Sum.inl (args.map (Term.mapSym Sum.inl))) := by
  simp only [transRule, Rule.mapSym, hlhs, Term.mapSym_app, destructorPattern_app,
    Term.mapSymList_eq_map]

private theorem transRule_freshL_lhs (t : Term sigma nu) (x y : nu) :
    (transRule (extRuleFreshL (sigma := sigma) t x y)).lhs =
      .app (.inr (freshSym (sigma := sigma) (nu := nu)))
        (Term.mapSymList Sum.inl [freeze t, .var x, .var y]) := rfl

private theorem transRule_freshR_lhs (u : Term sigma nu) (x y : nu) :
    (transRule (extRuleFreshR (sigma := sigma) u x y)).lhs =
      .app (.inr (freshSym (sigma := sigma) (nu := nu)))
        (Term.mapSymList Sum.inl [freeze u, .var x, .var y]) := rfl

private theorem transRule_freshL_rhs (t : Term sigma nu) (x y : nu) :
    (transRule (extRuleFreshL (sigma := sigma) t x y)).rhs = .var x :=
  rfl

private theorem transRule_freshR_rhs (u : Term sigma nu) (x y : nu) :
    (transRule (extRuleFreshR (sigma := sigma) u x y)).rhs = .var y :=
  rfl

private theorem conOnly_patternRuleOf_rhs {n : sigma × List (Term sigma nu)} :
    ConOnly (patternRuleOf n).rhs :=
  ConOnly.constructorLabel (.app n.1 n.2)

/--
Proves: the constructor translation of the Theorem 69 extension of `R` is
syntactically descending in the lifted order `extLt lt`.
Does not prove: descent of an arbitrary super-system of `R`.
Relation: `RhsSymbolsDescend` on `constructorTranslation (extSystem R t u x y)`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: translated old rules inherit `hdesc`; the two `F` rules have variable
right-hand sides; pattern rules are constructor-only.
-/
theorem rhsSymbolsDescend_constructorTranslation_extendedTRS
    {R : TRS sigma nu} {lt : sigma → sigma → Prop}
    (hdesc : RhsSymbolsDescend (constructorTranslation R) lt)
    (t u : Term sigma nu) (x y : nu) :
    RhsSymbolsDescend (constructorTranslation (extSystem R t u x y))
      (extLt (nu := nu) lt) := by
  intro rule hr d ps hlhs
  rcases mem_constructorTranslation hr with ⟨r0, hr0, rfl⟩ | ⟨n, hn, rfl⟩
  · rcases mem_extSystem hr0 with ⟨r, hrR, rfl⟩ | rfl | rfl
    · obtain ⟨f, args, hflhs⟩ := Rule.lhs_app r
      have hlift := transRule_mapInl_lhs (r := r) hflhs
      rw [hlift] at hlhs
      obtain ⟨hd, _⟩ := Term.app.inj hlhs
      have hd' : d = Sum.inl f := (Sum.inr.inj hd).symm
      subst d
      have horig : (transRule r).lhs =
          .app (.inr f) (Term.mapSymList Sum.inl args) := by
        simp only [transRule, hflhs, destructorPattern_app]
      have hsat := hdesc (transRule r) (transRule_mem hrR) f
        (Term.mapSymList Sum.inl args) horig
      rw [transRule_mapInl_rhs]
      exact symbolsSatisfy_destructorLabel_lift (fun _ => True.intro)
        (fun _ hg => hg) hsat
    · rw [transRule_freshL_lhs] at hlhs
      rw [transRule_freshL_rhs]
      exact SymbolsSatisfy.var x
    · rw [transRule_freshR_lhs] at hlhs
      rw [transRule_freshR_rhs]
      exact SymbolsSatisfy.var y
  · exact SymbolsSatisfy.of_conOnly (fun _ => True.intro)
      (conOnly_patternRuleOf_rhs (n := n))

/-- Consistency of the Theorem 69 extension, from descent of the source
translation, Proposition 22, and Corollary 16. -/
theorem consistent_extSystem_of_rhsSymbolsDescend [Infinite nu]
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {t u : Term sigma nu} (ht : NormalForm R t) (hu : NormalForm R u)
    (hne : t ≠ u) (x y : nu) {lt : sigma → sigma → Prop} (hwf : WellFounded lt)
    (hdesc : RhsSymbolsDescend (constructorTranslation R) lt) :
    Consistent (extSystem R t u x y) :=
  (cor16 (extSystem R t u x y)).mpr
    (consistent_of_rhsSymbolsDescend
      (constructorRules_constructorTranslation _)
      (prop22 (nonOmegaOverlapping_ext hno ht hu hne x y)
        (rhsDetermined_ext hvar t u x y))
      (wellFounded_extLt hwf)
      (rhsSymbolsDescend_constructorTranslation_extendedTRS hdesc t u x y))

/--
Intent: unique normal forms under conversion for a non-omega-overlapping, right-variable-safe system whose constructor translation has descending right-hand-side destructor symbols.
Relation: conv R (conversion of the source system); Down on the constructor translation of each extension.
Closure: full contextual rewriting.
Strategy: full rewriting.
External trust: none.
Non-vacuity witness: descendingClass_nonvacuous below.
-/
theorem UNconv_of_translation_rhsSymbolsDescend [Infinite nu] {R : TRS sigma nu}
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {lt : sigma → sigma → Prop} (hwf : WellFounded lt)
    (hdesc : RhsSymbolsDescend (constructorTranslation R) lt) : UNconv R :=
  UNconv_of_extension_consistent fun t u ht hu hconv hne => by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne nu
    refine ⟨x, y, hxy,
      nonOmegaOverlapping_ext hno ht hu hne x y,
      rhsDetermined_ext hvar t u x y, ?_⟩
    exact consistent_extSystem_of_rhsSymbolsDescend hno hvar ht hu hne x y hwf hdesc

/-- The same hypotheses give unique normal forms with respect to reduction. -/
theorem UNred_of_translation_rhsSymbolsDescend [Infinite nu] {R : TRS sigma nu}
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {lt : sigma → sigma → Prop} (hwf : WellFounded lt)
    (hdesc : RhsSymbolsDescend (constructorTranslation R) lt) : UNred R :=
  UNred_of_UNconv (UNconv_of_translation_rhsSymbolsDescend hno hvar hwf hdesc)

/-! ## Source-level corollary matching `transRule` -/

/-- `transRule` sends `l → r` to `destructorPattern l → destructorLabel r`.
The left-hand side is destructor-headed at the original root, so source-level
descent of every right-hand-side symbol below that root is exactly the content
of `RhsSymbolsDescend` on the translated rules; pattern rules are constructor-only. -/
theorem SymbolsSatisfy.destructorLabel_of_occurs {lt : sigma → sigma → Prop}
    {f : sigma} :
    ∀ t : Term sigma nu,
      (∀ g, SymbolOccurs g t → lt g f) →
      SymbolsSatisfy (fun s => match s with | .inl _ => True | .inr e => lt e f)
        (destructorLabel t) := by
  intro t hocc
  induction t using Term.rec' with
  | hvar x => exact .var x
  | happ g args ih =>
      rw [destructorLabel_app]
      refine .app (hocc g .here) ?_
      intro a ha
      rw [Term.mapSymList_eq_map] at ha
      obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
      exact ih a0 ha0 (fun e he => hocc e (.of_arg ha0 he))

/--
Proves: syntactic descent of the constructor translation from a source-level
bound: every function symbol of a right-hand side lies strictly below the
left-hand-side root.
Does not prove: the bound for an arbitrary labelling other than `transRule`.
Relation: `RhsSymbolsDescend (constructorTranslation R)`.
Trust: kernel-only.
-/
theorem rhsSymbolsDescend_of_rhs_symbols_below_root
    {R : TRS sigma nu} {lt : sigma → sigma → Prop}
    (h : ∀ rule ∈ R, ∀ f ps, rule.lhs = .app f ps →
      ∀ g, SymbolOccurs g rule.rhs → lt g f) :
    RhsSymbolsDescend (constructorTranslation R) lt := by
  intro rule hr d ps hlhs
  rcases mem_constructorTranslation hr with ⟨r, hrR, rfl⟩ | ⟨n, hn, rfl⟩
  · obtain ⟨f, args, hflhs⟩ := Rule.lhs_app r
    have hl : (transRule r).lhs =
        .app (.inr f) (Term.mapSymList Sum.inl args) := by
      simp only [transRule, hflhs, destructorPattern_app]
    rw [hl] at hlhs
    obtain ⟨hd, _⟩ := Term.app.inj hlhs
    have hd' : d = f := (Sum.inr.inj hd).symm
    subst d
    simpa [transRule] using
      SymbolsSatisfy.destructorLabel_of_occurs r.rhs (h r hrR f args hflhs)
  · exact SymbolsSatisfy.of_conOnly (fun _ => True.intro)
      (conOnly_patternRuleOf_rhs (n := n))

/--
Proves: unique normal forms under conversion from a source-level descent bound
matching `transRule`.
Does not prove: uniqueness without the overlap and variable-condition hypotheses.
Relation: `conv R`.
Closure: full contextual rewriting.
Strategy: full rewriting.
Trust: kernel-only.
Non-vacuity witness: `descendingClass_nonvacuous`.
-/
theorem UNconv_of_rhs_symbols_below_root [Infinite nu] {R : TRS sigma nu}
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {lt : sigma → sigma → Prop} (hwf : WellFounded lt)
    (hbelow : ∀ rule ∈ R, ∀ f ps, rule.lhs = .app f ps →
      ∀ g, SymbolOccurs g rule.rhs → lt g f) : UNconv R :=
  UNconv_of_translation_rhsSymbolsDescend hno hvar hwf
    (rhsSymbolsDescend_of_rhs_symbols_below_root hbelow)

/-- Reduction uniqueness from the same source-level bound. -/
theorem UNred_of_rhs_symbols_below_root [Infinite nu] {R : TRS sigma nu}
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {lt : sigma → sigma → Prop} (hwf : WellFounded lt)
    (hbelow : ∀ rule ∈ R, ∀ f ps, rule.lhs = .app f ps →
      ∀ g, SymbolOccurs g rule.rhs → lt g f) : UNred R :=
  UNred_of_UNconv (UNconv_of_rhs_symbols_below_root hno hvar hwf hbelow)

/-! ## Non-vacuity: the capacity system, and the KO7 fence as negative control -/

/-- `A < H` and `B < H` on the capacity signature (`A = 3`, `B = 4`, `H = 7`). -/
def capacityLt (a b : Nat) : Prop := (a = 3 ∨ a = 4) ∧ b = 7

theorem capacityLt_wf : WellFounded capacityLt :=
  ⟨fun n => Acc.intro n (fun m hm =>
    Acc.intro m (fun k hk => by
      obtain ⟨hmval, rfl⟩ := hm
      obtain ⟨_, hm7⟩ := hk
      rcases hmval with h3 | h4
      · subst h3; cases hm7
      · subst h4; cases hm7))⟩

theorem capacity_rhs_symbols_below_root :
    ∀ rule ∈ capacity_rules, ∀ f ps, rule.lhs = .app f ps →
      ∀ g, SymbolOccurs g rule.rhs → capacityLt g f := by
  intro rule hr f ps hlhs g hg
  simp only [capacity_rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · obtain ⟨args, hmem⟩ := hg
    simp [ruleP] at hmem
  · injection hlhs with hf _
    subst f
    obtain ⟨args, hmem⟩ := hg
    simp [ruleH] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact ⟨Or.inl rfl, rfl⟩
  · injection hlhs with hf _
    subst f
    obtain ⟨args, hmem⟩ := hg
    simp [ruleHC] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact ⟨Or.inr rfl, rfl⟩

theorem capacity_rhsSymbolsDescend :
    RhsSymbolsDescend (constructorTranslation capacity_rules) capacityLt :=
  rhsSymbolsDescend_of_rhs_symbols_below_root capacity_rhs_symbols_below_root

theorem capacity_rhs_carries_symbol :
    ∃ rule ∈ capacity_rules, ∃ g : Nat, SymbolOccurs g rule.rhs :=
  ⟨ruleH, List.Mem.tail _ (List.Mem.head _), 3, ⟨[], by simp [ruleH]⟩⟩

/-- The descending class is inhabited: the capacity system is non-omega-overlapping,
right-variable-safe, and syntactically descending, and one of its right-hand
sides carries a function symbol. -/
theorem descendingClass_nonvacuous :
    NonOmegaOverlapping capacity_rules ∧
    TRS.RhsDetermined capacity_rules ∧
    WellFounded capacityLt ∧
    RhsSymbolsDescend (constructorTranslation capacity_rules) capacityLt ∧
    ∃ rule ∈ capacity_rules, ∃ g : Nat, SymbolOccurs g rule.rhs :=
  ⟨capacity_nonOmegaOverlapping, capacity_rhsDetermined, capacityLt_wf,
    capacity_rhsSymbolsDescend, capacity_rhs_carries_symbol⟩

/-- Unique normal forms for the capacity system by the descending-class
theorem; `capacity_UNconv` proves the same statement by the certificate route. -/
theorem descendingClass_UNconv : UNconv capacity_rules :=
  UNconv_of_translation_rhsSymbolsDescend
    capacity_nonOmegaOverlapping capacity_rhsDetermined
    capacityLt_wf capacity_rhsSymbolsDescend

/-- The KO7 kernel fails the overlap hypothesis of the descending-class
theorem, so the theorem does not apply to the calculus the paper places
outside the class. -/
theorem descendingClass_excludes_ko7 :
    ¬ NonOmegaOverlapping KO7Fence.ko7TRS :=
  KO7Fence.not_nonOmegaOverlapping

end OperatorKO7.Meta.UniqueNormalization
