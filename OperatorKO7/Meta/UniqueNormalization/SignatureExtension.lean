import OperatorKO7.Meta.UniqueNormalization.Proposition22
import OperatorKO7.Meta.UniqueNormalization.Coalgebra

/-!
# Theorem 69 with its signature extension

Campaign: `Roadmaps\klop\ROADMAP.md`, wave 7. Source: Kahrs and Smith, FSCD 2016,
Theorem 69, p.16, whose proof is quoted in full in `Theorem69.lean`.

## Fidelity block (frozen `definitions.md`, D15)

> "Then they remain normal forms in the TRS
> U = (Sigma + X + {F}, R union F(t, x, y) -> x, F(u, x, y) -> y). The system U is
> also non-omega-overlapping, as the new rules do not omega-overlap with each other
> or any old rule."

The extended signature is `sigma ⊕ (nu ⊕ Unit)`: the old symbols, one constant
for every variable, and the fresh symbol `F`. `freeze` sends a term of the old
signature to the extended one with every variable turned into its constant, so
the two normal forms become ground. That is the `X` half of the extension, and
`FreezingNeeded` in `Theorem69.lean` shows it cannot be dropped.

What this module proves, in the order the source proof uses it:

* `normalForm_freeze`: a normal form stays a normal form after freezing;
* `conv_var_var_ext`: the extension identifies the two chosen variables;
* `nonOmegaOverlapping_ext`: the extension is non-omega-overlapping;
* `rhsDetermined_ext`: the extension meets the variable condition;
* `UNconv_of_theorem68`: **Theorem 69**, from Theorem 68 quantified over systems
  on the extended signature.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u u' v

variable {sigma : Type u} {nu : Type v}

/-! ## Rewriting along a signature morphism -/

/-- A rule relabelled along a signature morphism. -/
def Rule.mapSym {tau : Type u'} (f : sigma → tau) (r : Rule sigma nu) : Rule tau nu where
  lhs := Term.mapSym f r.lhs
  rhs := Term.mapSym f r.rhs
  lhs_isApp := by rw [Term.isApp_mapSym]; exact r.lhs_isApp

/-- A rewrite step survives relabelling. -/
theorem Step.mapSym {tau : Type u'} (f : sigma → tau) {R : TRS sigma nu} :
    ∀ {s t : Term sigma nu}, Step R s t →
      Step (R.map (Rule.mapSym f)) (Term.mapSym f s) (Term.mapSym f t) := by
  intro s t h
  induction h with
  | root hr =>
      obtain ⟨rule, hmem, sb, hs, ht⟩ := hr
      refine Step.root ⟨Rule.mapSym f rule, List.mem_map_of_mem hmem, Term.mapSubstSym f sb, ?_, ?_⟩
      · rw [hs]; exact Term.mapSym_apply f sb rule.lhs
      · rw [ht]; exact Term.mapSym_apply f sb rule.rhs
  | arg g pre post _ ih =>
      simp only [Term.mapSym_app, Term.mapSymList_eq_map, List.map_append, List.map_cons]
      exact Step.arg (f g) _ _ ih

/-- A conversion survives relabelling. -/
theorem conv.mapSym {tau : Type u'} (f : sigma → tau) {R : TRS sigma nu}
    {s t : Term sigma nu} (h : conv R s t) :
    conv (R.map (Rule.mapSym f)) (Term.mapSym f s) (Term.mapSym f t) := by
  induction h with
  | refl => exact conv.refl _ _
  | tail _ hlast ih =>
      refine conv.trans ih (conv.single ?_)
      rcases hlast with hstep | hstep
      · exact Or.inl (Step.mapSym f hstep)
      · exact Or.inr (Step.mapSym f hstep)

/-- A conversion survives a substitution. -/
theorem conv.subst {R : TRS sigma nu} (sb : Subst sigma nu) {s t : Term sigma nu}
    (h : conv R s t) : conv R (Subst.apply sb s) (Subst.apply sb t) := by
  induction h with
  | refl => exact conv.refl _ _
  | tail _ hlast ih =>
      refine conv.trans ih (conv.single ?_)
      rcases hlast with hstep | hstep
      · exact Or.inl (Step.subst sb hstep)
      · exact Or.inr (Step.subst sb hstep)

/-! ## The extended signature -/

/-- The extended signature: old symbols, one constant per variable, and `F`. -/
abbrev ExtSym (sigma : Type u) (nu : Type v) := sigma ⊕ (nu ⊕ Unit)

/-- The constant standing for a frozen variable. -/
def frozenVar (x : nu) : ExtSym sigma nu := Sum.inr (Sum.inl x)

/-- The fresh symbol. -/
def freshSym : ExtSym sigma nu := Sum.inr (Sum.inr ())

/-- A term of the old signature, read in the extended one. -/
def liftTerm (t : Term sigma nu) : Term (ExtSym sigma nu) nu := Term.mapSym Sum.inl t

/-- The substitution turning every variable into its constant. -/
def freezeSubst : Subst (ExtSym sigma nu) nu := fun x => Term.app (frozenVar x) []

/-- A term with its variables turned into constants. -/
def freeze (t : Term sigma nu) : Term (ExtSym sigma nu) nu :=
  Subst.apply freezeSubst (liftTerm t)

theorem freeze_var (x : nu) : freeze (sigma := sigma) (Term.var x) = Term.app (frozenVar x) [] := rfl

theorem freeze_app (f : sigma) (args : List (Term sigma nu)) :
    freeze (Term.app f args) = Term.app (Sum.inl f) (args.map freeze) := by
  show Subst.apply freezeSubst (Term.mapSym Sum.inl (Term.app f args)) = _
  rw [Term.mapSym_app, Subst.apply_app, Subst.applyList_eq_map, Term.mapSymList_eq_map,
    List.map_map]
  rfl

/-- A variable occurring in an instance occurs in the image of a variable of the
term. -/
theorem VarOccurs.of_apply {x : nu} {sb : Subst sigma nu} :
    ∀ {t : Term sigma nu}, VarOccurs x (Subst.apply sb t) →
      ∃ y, VarOccurs y t ∧ VarOccurs x (sb y) := by
  intro t
  induction t using Term.rec' with
  | hvar y => intro h; exact ⟨y, VarOccurs.here, h⟩
  | happ f args ih =>
      intro h
      rw [Subst.apply_app, Subst.applyList_eq_map] at h
      obtain ⟨a', ha', hx⟩ := h.app_inv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
      obtain ⟨y, hy, hxy⟩ := ih a ha hx
      exact ⟨y, VarOccurs.arg ha hy, hxy⟩

/-- A frozen term is ground. -/
theorem ground_freeze (t : Term sigma nu) : Ground (freeze t) := by
  intro x hx
  obtain ⟨y, -, hxy⟩ := VarOccurs.of_apply hx
  obtain ⟨a, ha, -⟩ := hxy.app_inv
  simp at ha

/-! ## Reading a frozen term back -/

mutual
/-- The inverse of freezing on the image, with `f₀` standing in for `F`. -/
def unfreeze (f₀ : sigma) : Term (ExtSym sigma nu) nu → Term sigma nu
  | .var x => .var x
  | .app (Sum.inl f) args => .app f (unfreezeList f₀ args)
  | .app (Sum.inr (Sum.inl x)) _ => .var x
  | .app (Sum.inr (Sum.inr _)) args => .app f₀ (unfreezeList f₀ args)
/-- `unfreeze` across an argument list. -/
def unfreezeList (f₀ : sigma) : List (Term (ExtSym sigma nu) nu) → List (Term sigma nu)
  | [] => []
  | a :: as => unfreeze f₀ a :: unfreezeList f₀ as
end

theorem unfreezeList_eq_map (f₀ : sigma) (args : List (Term (ExtSym sigma nu) nu)) :
    unfreezeList f₀ args = args.map (unfreeze f₀) := by
  induction args with
  | nil => rfl
  | cons a as ih => simp only [unfreezeList, ih, List.map_cons]

theorem unfreeze_freeze (f₀ : sigma) : ∀ t : Term sigma nu, unfreeze f₀ (freeze t) = t := by
  intro t
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
      rw [freeze_app]
      simp only [unfreeze, unfreezeList_eq_map, List.map_map]
      congr 1
      exact (List.map_congr_left (fun a ha => ih a ha)).trans (List.map_id'' (fun _ => rfl) ..)

theorem freeze_injective (f₀ : sigma) {s t : Term sigma nu} (h : freeze s = freeze t) : s = t := by
  have := congrArg (unfreeze f₀) h
  rwa [unfreeze_freeze, unfreeze_freeze] at this

/-- Unfreezing an instance of a lifted term is an instance of the term. -/
theorem unfreeze_apply_lift (f₀ : sigma) (sb : Subst (ExtSym sigma nu) nu) :
    ∀ l : Term sigma nu,
      unfreeze f₀ (Subst.apply sb (liftTerm l)) = Subst.apply (fun x => unfreeze f₀ (sb x)) l := by
  intro l
  induction l using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
      show unfreeze f₀ (Subst.apply sb (Term.mapSym Sum.inl (Term.app f args))) = _
      rw [Term.mapSym_app, Subst.apply_app, Term.mapSymList_eq_map, Subst.applyList_eq_map,
        List.map_map]
      simp only [unfreeze, unfreezeList_eq_map, List.map_map, Subst.apply_app,
        Subst.applyList_eq_map]
      congr 1
      exact List.map_congr_left (fun a ha => ih a ha)

/-! ## The extended system -/

/-- `F(t, x, y) -> x`. -/
def extRuleFreshL (t : Term sigma nu) (x y : nu) : Rule (ExtSym sigma nu) nu where
  lhs := .app freshSym [freeze t, .var x, .var y]
  rhs := .var x
  lhs_isApp := rfl

/-- `F(u, x, y) -> y`. -/
def extRuleFreshR (u : Term sigma nu) (x y : nu) : Rule (ExtSym sigma nu) nu where
  lhs := .app freshSym [freeze u, .var x, .var y]
  rhs := .var y
  lhs_isApp := rfl

/-- **The system `U` of Theorem 69**, over the extended signature. -/
def extSystem (R : TRS sigma nu) (t u : Term sigma nu) (x y : nu) : TRS (ExtSym sigma nu) nu :=
  R.map (Rule.mapSym Sum.inl) ++ [extRuleFreshL t x y, extRuleFreshR u x y]

theorem mem_extSystem {R : TRS sigma nu} {t u : Term sigma nu} {x y : nu}
    {r : Rule (ExtSym sigma nu) nu} (h : r ∈ extSystem R t u x y) :
    (∃ r₀ ∈ R, r = Rule.mapSym Sum.inl r₀) ∨ r = extRuleFreshL t x y ∨ r = extRuleFreshR u x y := by
  rcases List.mem_append.mp h with h' | h'
  · obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp h'
    exact Or.inl ⟨r₀, hr₀, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    exact Or.inr h'

theorem lifted_mem_extSystem {R : TRS sigma nu} {t u : Term sigma nu} {x y : nu}
    {r₀ : Rule sigma nu} (h : r₀ ∈ R) : Rule.mapSym Sum.inl r₀ ∈ extSystem R t u x y :=
  List.mem_append_left _ (List.mem_map_of_mem h)

/-! ## Normal forms survive freezing -/

/-- A frozen constant admits no step. -/
theorem not_step_frozenVar {R : TRS sigma nu} {t u : Term sigma nu} {x y : nu} (z : nu)
    {w : Term (ExtSym sigma nu) nu} : ¬ Step (extSystem R t u x y) (Term.app (frozenVar z) []) w := by
  intro h
  rcases Step.app_inv h with hroot | ⟨pre, post, a, b, hargs, -, -⟩
  · obtain ⟨rule, hmem, sb, hsrc, -⟩ := hroot
    rcases mem_extSystem hmem with ⟨r₀, -, rfl⟩ | rfl | rfl
    · obtain ⟨f, args, hl⟩ := Rule.lhs_app r₀
      simp only [Rule.mapSym, hl, Term.mapSym_app, Subst.apply_app, Term.app.injEq] at hsrc
      exact absurd hsrc.1 (by simp [frozenVar])
    · simp only [extRuleFreshL, Subst.apply_app, Term.app.injEq] at hsrc
      exact absurd hsrc.1 (by simp [frozenVar, freshSym])
    · simp only [extRuleFreshR, Subst.apply_app, Term.app.injEq] at hsrc
      exact absurd hsrc.1 (by simp [frozenVar, freshSym])
  · exact absurd hargs.symm (by simp)

/-- **Frozen normal forms stay normal forms.** Source: "they remain normal forms in
the TRS U". A root contraction by a lifted rule would unfreeze to a root
contraction of the original, and no other rule can match. -/
theorem normalForm_freeze {R : TRS sigma nu} {t u : Term sigma nu} {x y : nu} :
    ∀ s : Term sigma nu, NormalForm R s → NormalForm (extSystem R t u x y) (freeze s) := by
  intro s
  induction s using Term.rec' with
  | hvar z =>
      intro _ w hw
      rw [freeze_var] at hw
      exact not_step_frozenVar z hw
  | happ f args ih =>
      intro hnf w hw
      rw [freeze_app] at hw
      rcases Step.app_inv hw with hroot | ⟨pre, post, a, b, hargs, -, hab⟩
      · obtain ⟨rule, hmem, sb, hsrc, -⟩ := hroot
        rcases mem_extSystem hmem with ⟨r₀, hr₀, rfl⟩ | rfl | rfl
        · -- a lifted rule: unfreeze the match
          have hsrc' : Subst.apply sb (liftTerm r₀.lhs) = freeze (Term.app f args) := by
            rw [freeze_app]; exact hsrc.symm
          have hmatch := congrArg (unfreeze f) hsrc'
          rw [unfreeze_apply_lift, unfreeze_freeze] at hmatch
          exact hnf _ (Step.root ⟨r₀, hr₀, _, hmatch.symm, rfl⟩)
        · simp only [extRuleFreshL, Subst.apply_app, Term.app.injEq] at hsrc
          exact absurd hsrc.1 (by simp [freshSym])
        · simp only [extRuleFreshR, Subst.apply_app, Term.app.injEq] at hsrc
          exact absurd hsrc.1 (by simp [freshSym])
      · -- an argument step: the argument is a frozen normal form
        have hmem : a ∈ args.map freeze := by
          rw [hargs]; exact List.mem_append_right _ (List.Mem.head _)
        obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp hmem
        exact ih a₀ ha₀ (hnf.subterm (Subterm.arg ha₀ (Subterm.refl _))) b hab

/-! ## The extension identifies the two variables -/

theorem step_extFreshL (R : TRS sigma nu) (t u : Term sigma nu) (x y : nu) :
    Step (extSystem R t u x y) (.app freshSym [freeze t, .var x, .var y]) (.var x) :=
  Step.root ⟨extRuleFreshL t x y,
    List.mem_append_right _ (List.Mem.head _), Subst.id,
    (Subst.id_apply _).symm, (Subst.id_apply _).symm⟩

theorem step_extFreshR (R : TRS sigma nu) (t u : Term sigma nu) (x y : nu) :
    Step (extSystem R t u x y) (.app freshSym [freeze u, .var x, .var y]) (.var y) :=
  Step.root ⟨extRuleFreshR u x y,
    List.mem_append_right _ (List.Mem.tail _ (List.Mem.head _)), Subst.id,
    (Subst.id_apply _).symm, (Subst.id_apply _).symm⟩

/-- Frozen convertible terms are convertible in the extension. -/
theorem conv_freeze {R : TRS sigma nu} {t u : Term sigma nu} (x y : nu) (h : conv R t u) :
    conv (extSystem R t u x y) (freeze t) (freeze u) := by
  have h₁ := conv.mapSym (Sum.inl : sigma → ExtSym sigma nu) h
  have h₂ : conv (extSystem R t u x y) (liftTerm t) (liftTerm u) :=
    conv.mono (R := R.map (Rule.mapSym Sum.inl)) (R' := extSystem R t u x y)
      (fun _ hr => List.mem_append_left _ hr) h₁
  exact conv.subst freezeSubst h₂

/-- Source: "x =_U F(t, x, y) =_U F(u, x, y) =_U y". -/
theorem conv_var_var_ext {R : TRS sigma nu} {t u : Term sigma nu} (x y : nu) (h : conv R t u) :
    conv (extSystem R t u x y) (.var x) (.var y) :=
  conv.trans
    (conv.symm (conv.of_step (step_extFreshL R t u x y)))
    (conv.trans
      (conv.arg_congr _ freshSym [] [.var x, .var y] (conv_freeze x y h))
      (conv.of_step (step_extFreshR R t u x y)))

/-! ## Subterms of lifted and frozen terms -/

theorem Subterm.mapSym {tau : Type u'} (g : sigma → tau) {a b : Term sigma nu}
    (h : Subterm a b) : Subterm (Term.mapSym g a) (Term.mapSym g b) := by
  induction h with
  | refl => exact Subterm.refl _
  | @arg _ f args hmem _ ih =>
      rw [Term.mapSym_app]
      refine Subterm.arg ?_ ih
      rw [Term.mapSymList_eq_map]
      exact List.mem_map_of_mem hmem

theorem subterm_of_mapSym {tau : Type u'} {g : sigma → tau} {s : Term tau nu} :
    ∀ {l : Term sigma nu}, Subterm s (Term.mapSym g l) →
      ∃ s₀ : Term sigma nu, Subterm s₀ l ∧ s = Term.mapSym g s₀ := by
  intro l
  induction l using Term.rec' with
  | hvar x =>
      intro h
      rw [Term.mapSym_var] at h
      exact ⟨Term.var x, Subterm.refl _, h.eq_of_var⟩
  | happ f args ih =>
      intro h
      rw [Term.mapSym_app] at h
      rcases h.app_inv with rfl | ⟨a', ha', hsa⟩
      · exact ⟨Term.app f args, Subterm.refl _, by rw [Term.mapSym_app]⟩
      · rw [Term.mapSymList_eq_map] at ha'
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
        obtain ⟨s₀, hs₀, rfl⟩ := ih a ha hsa
        exact ⟨s₀, Subterm.arg ha hs₀, rfl⟩

theorem subterm_of_freeze {s : Term (ExtSym sigma nu) nu} :
    ∀ {t : Term sigma nu}, Subterm s (freeze t) → ∃ s₀ : Term sigma nu, Subterm s₀ t ∧ s = freeze s₀ := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
      intro h
      rw [freeze_var] at h
      rcases h.app_inv with rfl | ⟨a, ha, -⟩
      · exact ⟨Term.var x, Subterm.refl _, rfl⟩
      · simp at ha
  | happ f args ih =>
      intro h
      rw [freeze_app] at h
      rcases h.app_inv with rfl | ⟨a', ha', hsa⟩
      · exact ⟨Term.app f args, Subterm.refl _, by rw [freeze_app]⟩
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
        obtain ⟨s₀, hs₀, rfl⟩ := ih a ha hsa
        exact ⟨s₀, Subterm.arg ha hs₀, rfl⟩

/-- A subterm of a frozen term is never headed by the fresh symbol. -/
theorem subterm_freeze_root {s : Term (ExtSym sigma nu) nu} {t : Term sigma nu}
    (h : Subterm s (freeze t)) {args : List (Term (ExtSym sigma nu) nu)}
    (hs : s = Term.app freshSym args) : False := by
  obtain ⟨s₀, -, rfl⟩ := subterm_of_freeze h
  cases s₀ with
  | var z =>
      rw [freeze_var] at hs
      simp only [Term.app.injEq] at hs
      exact absurd hs.1 (by simp [frozenVar, freshSym])
  | app f as =>
      rw [freeze_app] at hs
      simp only [Term.app.injEq] at hs
      exact absurd hs.1 (by simp [freshSym])

theorem freeze_injective' : ∀ {s t : Term sigma nu}, freeze s = freeze t → s = t := by
  intro s
  induction s using Term.rec' with
  | hvar x =>
      intro t h
      cases t with
      | var y =>
          rw [freeze_var, freeze_var] at h
          simp only [Term.app.injEq, and_true] at h
          have : x = y := by simpa [frozenVar] using h
          rw [this]
      | app g bs =>
          rw [freeze_var, freeze_app] at h
          simp only [Term.app.injEq] at h
          exact absurd h.1 (by simp [frozenVar])
  | happ f args ih =>
      intro t h
      cases t with
      | var y =>
          rw [freeze_app, freeze_var] at h
          simp only [Term.app.injEq] at h
          exact absurd h.1 (by simp [frozenVar])
      | app g bs =>
          rw [freeze_app, freeze_app] at h
          simp only [Term.app.injEq] at h
          obtain ⟨hfg, hargs⟩ := h
          have hfg' : f = g := by simpa using hfg
          subst hfg'
          congr 1
          have hl : ∀ (as : List (Term sigma nu)), (∀ a ∈ as, ∀ b, freeze a = freeze b → a = b) →
              ∀ bs : List (Term sigma nu), as.map freeze = bs.map freeze → as = bs := by
            intro as
            induction as with
            | nil => intro _ bs h; cases bs with | nil => rfl | cons _ _ => simp at h
            | cons a as iha =>
                intro hmem bs h
                cases bs with
                | nil => simp at h
                | cons b bs =>
                    simp only [List.map_cons, List.cons.injEq] at h
                    rw [hmem a (List.mem_cons_self ..) b h.1,
                      iha (fun q hq => hmem q (List.mem_cons_of_mem _ hq)) bs h.2]
          exact hl args (fun a ha b hb => ih a ha hb) bs hargs

/-! ## The unlifting morphism -/

/-- Symbols of the extended signature read back into the old one, with `f₀`
standing in for the constants and for `F`. -/
def unliftSym (f₀ : sigma) : ExtSym sigma nu → sigma := Sum.elim id (fun _ => f₀)

theorem mapSym_unlift_mapSym (f₀ : sigma) (l : Term sigma nu) :
    Term.mapSym (unliftSym (nu := nu) f₀) (Term.mapSym Sum.inl l) = l := by
  rw [Term.mapSym_mapSym]
  exact Term.mapSym_id l

/-! ## Omega-unifiability on the first arguments -/

theorem omegaUnifiable_head {f g : ExtSym sigma nu} {a b : Term (ExtSym sigma nu) nu}
    {xs ys : List (Term (ExtSym sigma nu) nu)}
    (h : OmegaUnifiable (Term.app f (a :: xs)) (Term.app g (b :: ys))) : OmegaUnifiable a b := by
  obtain ⟨E, hE, hst⟩ := h
  unfold leftCopy rightCopy at hst
  simp only [Term.mapVar_app, Term.mapVarList_cons] at hst
  have hargs := hE.args_forall₂ hst
  cases hargs with
  | cons hab _ => exact ⟨E, hE, hab⟩

/-! ## The three kinds of left-hand side -/

theorem subterm_freshLhs {s : Term (ExtSym sigma nu) nu} {v : Term sigma nu} {x y : nu}
    (h : Subterm s (Term.app freshSym [freeze v, Term.var x, Term.var y])) (happ : s.isApp = true) :
    s = Term.app freshSym [freeze v, Term.var x, Term.var y] ∨ Subterm s (freeze v) := by
  rcases h.app_inv with rfl | ⟨a, ha, hsa⟩
  · exact Or.inl rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact Or.inr hsa
    · rw [hsa.eq_of_var] at happ; simp at happ
    · rw [hsa.eq_of_var] at happ; simp at happ

/-- A subterm of a frozen normal form omega-unifies with no lifted left-hand
side. -/
theorem not_omegaUnifiable_freeze_lifted {R : TRS sigma nu} {t u v : Term sigma nu} {x y : nu}
    (hv : NormalForm R v) {s : Term (ExtSym sigma nu) nu} (hs : Subterm s (freeze v))
    {r : Rule sigma nu} (hr : r ∈ R) :
    ¬ OmegaUnifiable s (Rule.mapSym Sum.inl r).lhs :=
  subterm_not_omegaUnifiable_of_ground_normalForm
    (normalForm_freeze (t := t) (u := u) (x := x) (y := y) v hv) (ground_freeze v) hs
    (lifted_mem_extSystem hr)

/-- A subterm of a frozen term omega-unifies with no `F`-rooted term. -/
theorem not_omegaUnifiable_freeze_fresh {v : Term sigma nu} {s : Term (ExtSym sigma nu) nu}
    (hs : Subterm s (freeze v)) (happ : s.isApp = true)
    {args : List (Term (ExtSym sigma nu) nu)} :
    ¬ OmegaUnifiable s (Term.app freshSym args) := by
  intro h
  cases s with
  | var z => simp at happ
  | app g as =>
      have := root_eq_of_omegaUnifiable h
      exact subterm_freeze_root hs (by rw [this])

/-! ## The extension is non-omega-overlapping -/

/-- Source: "The system U is also non-omega-overlapping, as the new rules do not
omega-overlap with each other or any old rule." Old against old descends along the
unlifting morphism to convention CC1; every mixed pair clashes at the root; the two
new rules against each other would make the two frozen normal forms equal. -/
theorem nonOmegaOverlapping_ext {R : TRS sigma nu} (hno : NonOmegaOverlapping R)
    {t u : Term sigma nu} (ht : NormalForm R t) (hu : NormalForm R u) (hne : t ≠ u)
    (x y : nu) : NonOmegaOverlapping (extSystem R t u x y) := by
  intro r₁ h₁ r₂ h₂ s hsub happ hou
  rcases mem_extSystem h₁ with ⟨r, hr, rfl⟩ | rfl | rfl
  · -- r₁ lifted
    obtain ⟨s₀, hs₀, rfl⟩ := subterm_of_mapSym (g := Sum.inl) hsub
    have happ₀ : s₀.isApp = true := by rwa [Term.isApp_mapSym] at happ
    rcases mem_extSystem h₂ with ⟨r', hr', rfl⟩ | rfl | rfl
    · obtain ⟨f₀, -, -⟩ := Rule.lhs_app r
      have hpush := omegaUnifiable_mapSym (unliftSym (nu := nu) f₀) hou
      simp only [Rule.mapSym] at hpush
      rw [mapSym_unlift_mapSym, mapSym_unlift_mapSym] at hpush
      obtain ⟨rfl, hs⟩ := hno r hr r' hr' s₀ hs₀ happ₀ hpush
      exact ⟨rfl, by rw [hs]; rfl⟩
    · exfalso
      cases s₀ with
      | var z => simp at happ₀
      | app g as =>
          rw [Term.mapSym_app] at hou
          have := root_eq_of_omegaUnifiable hou
          exact absurd this (by simp [freshSym])
    · exfalso
      cases s₀ with
      | var z => simp at happ₀
      | app g as =>
          rw [Term.mapSym_app] at hou
          have := root_eq_of_omegaUnifiable hou
          exact absurd this (by simp [freshSym])
  · -- r₁ is F(t, x, y) -> x
    rcases subterm_freshLhs hsub happ with rfl | hs
    · rcases mem_extSystem h₂ with ⟨r', hr', rfl⟩ | rfl | rfl
      · exfalso
        obtain ⟨g, as, hl⟩ := Rule.lhs_app r'
        simp only [Rule.mapSym, hl, Term.mapSym_app] at hou
        have := root_eq_of_omegaUnifiable hou
        exact absurd this (by simp [freshSym])
      · exact ⟨rfl, rfl⟩
      · exfalso
        have hfu := omegaUnifiable_head hou
        have := eq_of_ground_omegaUnifiable (ground_freeze t) (ground_freeze u) hfu
        exact hne (freeze_injective' this)
    · exfalso
      rcases mem_extSystem h₂ with ⟨r', hr', rfl⟩ | rfl | rfl
      · exact not_omegaUnifiable_freeze_lifted (t := t) (u := u) (x := x) (y := y) ht hs hr' hou
      · exact not_omegaUnifiable_freeze_fresh hs happ hou
      · exact not_omegaUnifiable_freeze_fresh hs happ hou
  · -- r₁ is F(u, x, y) -> y
    rcases subterm_freshLhs hsub happ with rfl | hs
    · rcases mem_extSystem h₂ with ⟨r', hr', rfl⟩ | rfl | rfl
      · exfalso
        obtain ⟨g, as, hl⟩ := Rule.lhs_app r'
        simp only [Rule.mapSym, hl, Term.mapSym_app] at hou
        have := root_eq_of_omegaUnifiable hou
        exact absurd this (by simp [freshSym])
      · exfalso
        have hfu := omegaUnifiable_head hou
        have := eq_of_ground_omegaUnifiable (ground_freeze u) (ground_freeze t) hfu
        exact hne (freeze_injective' this).symm
      · exact ⟨rfl, rfl⟩
    · exfalso
      rcases mem_extSystem h₂ with ⟨r', hr', rfl⟩ | rfl | rfl
      · exact not_omegaUnifiable_freeze_lifted (t := t) (u := u) (x := x) (y := y) hu hs hr' hou
      · exact not_omegaUnifiable_freeze_fresh hs happ hou
      · exact not_omegaUnifiable_freeze_fresh hs happ hou

/-! ## The extension meets the variable condition -/

theorem rhsDetermined_lift {r : Rule sigma nu} (h : Rule.RhsDetermined r) :
    Rule.RhsDetermined (Rule.mapSym (Sum.inl : sigma → ExtSym sigma nu) r) := by
  obtain ⟨f, args, -⟩ := Rule.lhs_app r
  refine determinedBy_of_occurs_subset ?_
  intro z hz
  have hz' : VarOccurs z r.rhs := VarOccurs.of_mapSym Sum.inl hz
  exact VarOccurs.mapSym Sum.inl (occurs_of_determinedBy f h hz')

theorem rhsDetermined_ext {R : TRS sigma nu} (hvar : TRS.RhsDetermined R)
    (t u : Term sigma nu) (x y : nu) : TRS.RhsDetermined (extSystem R t u x y) := by
  intro r hr
  rcases mem_extSystem hr with ⟨r₀, hr₀, rfl⟩ | rfl | rfl
  · exact rhsDetermined_lift (hvar r₀ hr₀)
  · refine determinedBy_of_occurs_subset ?_
    intro z hz
    cases hz
    exact VarOccurs.arg (List.Mem.tail _ (List.Mem.head _)) VarOccurs.here
  · refine determinedBy_of_occurs_subset ?_
    intro z hz
    cases hz
    exact VarOccurs.arg (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) VarOccurs.here

/-! ## Theorem 69 -/

/-- **Theorem 69**, from Theorem 68 quantified over systems on the extended
signature. Source proof, verbatim: were two distinct normal forms convertible,
the extension would be non-omega-overlapping, hence consistent, while it identifies
the two chosen variables. -/
theorem UNconv_of_theorem68_nontrivial [Nontrivial nu] {R : TRS sigma nu}
    (h68 : ∀ S : TRS (ExtSym sigma nu) nu,
      NonOmegaOverlapping S → TRS.RhsDetermined S → Consistent S)
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) : UNconv R := by
  intro t u ht hu hconv
  by_contra hne
  obtain ⟨x, y, hxy⟩ := exists_pair_ne nu
  have hcon := h68 (extSystem R t u x y)
    (nonOmegaOverlapping_ext hno ht hu hne x y) (rhsDetermined_ext hvar t u _ _)
  exact hxy (hcon _ _ (conv_var_var_ext _ _ hconv))

/-- Compatibility interface for an infinite variable supply. -/
theorem UNconv_of_theorem68 [Infinite nu] {R : TRS sigma nu}
    (h68 : ∀ S : TRS (ExtSym sigma nu) nu,
      NonOmegaOverlapping S → TRS.RhsDetermined S → Consistent S)
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) : UNconv R :=
  UNconv_of_theorem68_nontrivial h68 hno hvar

/-- Two distinct variables suffice for reduction-based uniqueness as well. -/
theorem UNred_of_theorem68_nontrivial [Nontrivial nu] {R : TRS sigma nu}
    (h68 : ∀ S : TRS (ExtSym sigma nu) nu,
      NonOmegaOverlapping S → TRS.RhsDetermined S → Consistent S)
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) : UNred R :=
  UNred_of_UNconv (UNconv_of_theorem68_nontrivial h68 hno hvar)

/-- The same input gives unique normal forms with respect to reduction. -/
theorem UNred_of_theorem68 [Infinite nu] {R : TRS sigma nu}
    (h68 : ∀ S : TRS (ExtSym sigma nu) nu,
      NonOmegaOverlapping S → TRS.RhsDetermined S → Consistent S)
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) : UNred R :=
  UNred_of_UNconv (UNconv_of_theorem68 h68 hno hvar)

/-! ## The summit, with Section 7 as the only hypothesis -/

/-- **Theorem 68 from transitivity of `⇓`.** For a system on any signature, if `⇓`
is transitive on its constructor translation then its equational theory is
consistent: Proposition 44 makes `⇓` constructor-compatible, transitivity makes
conversion coincide with `⇓`, Lemma 28 gives consistency of the translation, and
Corollary 16 brings it back. -/
theorem consistent_of_down_trans {tau : Type u'} {S : TRS tau nu}
    (htrans : ∀ p q r : Term (tau ⊕ tau) nu,
      Down (constructorTranslation S) p q → Down (constructorTranslation S) q r →
        Down (constructorTranslation S) p r) : Consistent S :=
  Consistent_of_translation_constructorCompatible S
    (constructorCompatible_conv_of_down_trans htrans)

/-- The Section 7 reduction requires two distinct variables. -/
theorem UNconv_of_section7_nontrivial [Nontrivial nu] {R : TRS sigma nu}
    (htrans : ∀ S : TRS (ExtSym sigma nu) nu, NonOmegaOverlapping S → TRS.RhsDetermined S →
      ∀ p q r : Term (ExtSym sigma nu ⊕ ExtSym sigma nu) nu,
        Down (constructorTranslation S) p q → Down (constructorTranslation S) q r →
          Down (constructorTranslation S) p r)
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) : UNconv R :=
  UNconv_of_theorem68_nontrivial
    (fun S hS hv => consistent_of_down_trans (htrans S hS hv)) hno hvar

/-- The same two-variable reduction gives reduction-based uniqueness. -/
theorem UNred_of_section7_nontrivial [Nontrivial nu] {R : TRS sigma nu}
    (htrans : ∀ S : TRS (ExtSym sigma nu) nu, NonOmegaOverlapping S → TRS.RhsDetermined S →
      ∀ p q r : Term (ExtSym sigma nu ⊕ ExtSym sigma nu) nu,
        Down (constructorTranslation S) p q → Down (constructorTranslation S) q r →
          Down (constructorTranslation S) p r)
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) : UNred R :=
  UNred_of_UNconv (UNconv_of_section7_nontrivial htrans hno hvar)

/-- **RTA open problem #79 from Section 7 alone.** The one hypothesis is the
conclusion of Kahrs and Smith's Section 7 on the constructor translation of every
non-omega-overlapping system meeting the variable condition, over the extended
signature. Everything else, Sections 3, 5, 6 and 8, Proposition 22, and the
signature extension of Theorem 69, is machine-checked. -/
theorem UNconv_of_section7 [Infinite nu] {R : TRS sigma nu}
    (htrans : ∀ S : TRS (ExtSym sigma nu) nu, NonOmegaOverlapping S → TRS.RhsDetermined S →
      ∀ p q r : Term (ExtSym sigma nu ⊕ ExtSym sigma nu) nu,
        Down (constructorTranslation S) p q → Down (constructorTranslation S) q r →
          Down (constructorTranslation S) p r)
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) : UNconv R :=
  UNconv_of_theorem68 (fun S hS hv => consistent_of_down_trans (htrans S hS hv)) hno hvar

/-- The same hypothesis gives unique normal forms with respect to reduction. -/
theorem UNred_of_section7 [Infinite nu] {R : TRS sigma nu}
    (htrans : ∀ S : TRS (ExtSym sigma nu) nu, NonOmegaOverlapping S → TRS.RhsDetermined S →
      ∀ p q r : Term (ExtSym sigma nu ⊕ ExtSym sigma nu) nu,
        Down (constructorTranslation S) p q → Down (constructorTranslation S) q r →
          Down (constructorTranslation S) p r)
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) : UNred R :=
  UNred_of_UNconv (UNconv_of_section7 htrans hno hvar)

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.extSystem
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_theorem68

#print axioms OperatorKO7.Meta.UniqueNormalization.normalForm_freeze
#print axioms OperatorKO7.Meta.UniqueNormalization.conv_var_var_ext
#print axioms OperatorKO7.Meta.UniqueNormalization.nonOmegaOverlapping_ext
#print axioms OperatorKO7.Meta.UniqueNormalization.rhsDetermined_ext
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_theorem68
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_theorem68
#print axioms OperatorKO7.Meta.UniqueNormalization.consistent_of_down_trans
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_section7
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_section7
