import OperatorKO7.Meta.Methods.OrientationClosure.ProcessorSemantics
import OperatorKO7.Meta.Methods.OrientationClosure.FreeDerivationalComplexity
import Mathlib.Tactic

/-!
# Labelling, match-bound, forward-closure and quasi-decreasingness method rows

Nine rows of the method universe. The labelling rows are stated over the generic first-order
library and instantiated at the free recursor `freeRecursorTRS`; the match-bound,
raise-consistency, left-linear, predictive-labelling and forward-closure rows are stated
below over the free schema `FreeTerm` with its contextual relation `ContextStep`.

Labelling rows. A labelled term carries, at every symbol, the label computed from the values of its
arguments in an algebra (`lab`); every source step lifts to a labelled step when the algebra is a
model (`lab_lift_model`), so termination of the labelled system transfers back
(`acc_of_lab_model`). The four variants differ in data and theorems: semantic labelling uses a
model of all rules; root labelling uses the root algebra, which is a model only of the closure under
flat contexts; self-labelling labels a symbol by the class of the term it heads in the quotient by an
equational theory; predictive labelling needs the quasi-model condition only for the usable rules
and computes labels from predicted values of terminating terms.
The rows over the free schema implement the raised match-bound certificate with source soundness
and the Geser-Hofbauer-Waldmann complexity transport, raise consistency and its role in the
native soundness proof, the left-linear scope with the actual tree automaton, the predictive
labelling transformation, and the forward-closure right-linearity criterion.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness
open OperatorKO7.Methods.OrientationClosure.ProcessorSemantics

universe u v w w'

/-! ## Context closure -/

section Ctx

variable {sigma : Type u} {nu : Type v}

/-- The closure of a root relation under one-hole application contexts. -/
inductive CtxClosure (P : Term sigma nu → Term sigma nu → Prop) :
    Term sigma nu → Term sigma nu → Prop
  | root {s t : Term sigma nu} : P s t → CtxClosure P s t
  | arg (f : sigma) (pre post : List (Term sigma nu)) {a b : Term sigma nu} :
      CtxClosure P a b → CtxClosure P (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post))

theorem ctxClosure_mono {P Q : Term sigma nu → Term sigma nu → Prop}
    (hPQ : ∀ s t, P s t → Q s t) {s t : Term sigma nu} (h : CtxClosure P s t) :
    CtxClosure Q s t := by
  induction h with
  | root h => exact .root (hPQ _ _ h)
  | arg f pre post _ ih => exact .arg f pre post ih

theorem step_iff_ctxClosure (R : TRS sigma nu) (s t : Term sigma nu) :
    Step R s t ↔ CtxClosure (rootStep R) s t := by
  constructor
  · intro h
    induction h with
    | root h => exact .root h
    | arg f pre post _ ih => exact .arg f pre post ih
  · intro h
    induction h with
    | root h => exact Step.root h
    | arg f pre post _ ih => exact Step.arg f pre post ih

/-- A measure that decreases on root steps and is strictly monotone in every argument decreases
on every contextual step. -/
theorem ctxClosure_measure {P : Term sigma nu → Term sigma nu → Prop} (W : Term sigma nu → ℕ)
    (hroot : ∀ s t, P s t → W t < W s)
    (hmono : ∀ (f : sigma) (pre post : List (Term sigma nu)) (a b : Term sigma nu),
      W a < W b → W (.app f (pre ++ a :: post)) < W (.app f (pre ++ b :: post)))
    {s t : Term sigma nu} (h : CtxClosure P s t) : W t < W s := by
  induction h with
  | root h => exact hroot _ _ h
  | arg f pre post _ ih => exact hmono f pre post _ _ ih

theorem ctxClosure_wf_of_measure {P : Term sigma nu → Term sigma nu → Prop}
    (W : Term sigma nu → ℕ) (hroot : ∀ s t, P s t → W t < W s)
    (hmono : ∀ (f : sigma) (pre post : List (Term sigma nu)) (a b : Term sigma nu),
      W a < W b → W (.app f (pre ++ a :: post)) < W (.app f (pre ++ b :: post))) :
    WellFounded (fun t s => CtxClosure P s t) :=
  Subrelation.wf (fun {_ _} h => ctxClosure_measure W hroot hmono h)
    (InvImage.wf W Nat.lt_wfRel.wf)

end Ctx

/-! ## Algebras -/

/-- An algebra over a signature: one operation on argument lists per symbol. -/
structure Alg (sigma : Type u) (A : Type w) where
  interp : sigma → List A → A

namespace Alg

variable {sigma : Type u} {nu : Type v} {A : Type w}

mutual
/-- Evaluation of a term under a valuation of its variables. -/
def eval (I : Alg sigma A) (α : nu → A) : Term sigma nu → A
  | .var x => α x
  | .app f args => I.interp f (evalList I α args)
/-- Evaluation of an argument list. -/
def evalList (I : Alg sigma A) (α : nu → A) : List (Term sigma nu) → List A
  | [] => []
  | t :: ts => eval I α t :: evalList I α ts
end

theorem evalList_eq_map (I : Alg sigma A) (α : nu → A) (ts : List (Term sigma nu)) :
    evalList I α ts = ts.map (eval I α) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    show eval I α t :: evalList I α ts = _
    rw [ih]
    rfl

@[simp] theorem eval_var (I : Alg sigma A) (α : nu → A) (x : nu) :
    eval I α (.var x) = α x := rfl

@[simp] theorem eval_app (I : Alg sigma A) (α : nu → A) (f : sigma)
    (args : List (Term sigma nu)) : eval I α (.app f args) = I.interp f (args.map (eval I α)) := by
  rw [← evalList_eq_map]
  rfl

/-- Evaluation of a substituted term is evaluation under the induced valuation. -/
theorem eval_subst (I : Alg sigma A) (α : nu → A) (σ : Subst sigma nu) (t : Term sigma nu) :
    eval I α (Subst.apply σ t) = eval I (fun x => eval I α (σ x)) t := by
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
    rw [Subst.apply_app, eval_app, eval_app, Subst.applyList_eq_map, List.map_map]
    congr 1
    exact List.map_congr_left (fun a ha => ih a ha)

end Alg

/-! ## Symbol maps -/

section MapSym

variable {sigma : Type u} {nu : Type v} {sigma' : Type w}

mutual
/-- Rename every symbol of a term. -/
def mapSym (g : sigma → sigma') : Term sigma nu → Term sigma' nu
  | .var x => .var x
  | .app f args => .app (g f) (mapSymList g args)
/-- Rename every symbol of an argument list. -/
def mapSymList (g : sigma → sigma') : List (Term sigma nu) → List (Term sigma' nu)
  | [] => []
  | t :: ts => mapSym g t :: mapSymList g ts
end

theorem mapSymList_eq_map (g : sigma → sigma') (ts : List (Term sigma nu)) :
    mapSymList g ts = ts.map (mapSym g) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    show mapSym g t :: mapSymList g ts = _
    rw [ih]
    rfl

@[simp] theorem mapSym_var (g : sigma → sigma') (x : nu) :
    mapSym g (.var x : Term sigma nu) = .var x := rfl

@[simp] theorem mapSym_app (g : sigma → sigma') (f : sigma) (args : List (Term sigma nu)) :
    mapSym g (.app f args) = .app (g f) (args.map (mapSym g)) := by
  rw [← mapSymList_eq_map]
  rfl

theorem mapSym_subst (g : sigma → sigma') (τ : Subst sigma nu) (t : Term sigma nu) :
    mapSym g (Subst.apply τ t) = Subst.apply (fun x => mapSym g (τ x)) (mapSym g t) := by
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
    rw [Subst.apply_app, mapSym_app, mapSym_app, Subst.apply_app, Subst.applyList_eq_map,
      Subst.applyList_eq_map, List.map_map, List.map_map]
    congr 1
    exact List.map_congr_left (fun a ha => ih a ha)

/-- The root symbol of a term. -/
def rootSym : Term sigma nu → Option sigma
  | .var _ => none
  | .app f _ => some f

end MapSym

/-! ## Linear forms -/

/-- `coef i * xs[i]` summed from position `i`. -/
def linSum (coef : ℕ → ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | i, a :: as => coef i * a + linSum coef (i + 1) as

/-- The linear form `c0 + Σ coef i * xs[i]`. -/
def linForm (c0 : ℕ) (coef : ℕ → ℕ) (xs : List ℕ) : ℕ := c0 + linSum coef 0 xs

theorem linSum_lt (coef : ℕ → ℕ) (hc : ∀ i, 1 ≤ coef i) :
    ∀ (i : ℕ) (pre post : List ℕ) (a b : ℕ), a < b →
      linSum coef i (pre ++ a :: post) < linSum coef i (pre ++ b :: post) := by
  intro i pre post a b hab
  induction pre generalizing i with
  | nil =>
    simp only [List.nil_append, linSum]
    have h1 := hc i
    have : coef i * a < coef i * b := Nat.mul_lt_mul_of_pos_left hab (by omega)
    omega
  | cons x pre ih =>
    simp only [List.cons_append, linSum]
    have := ih (i + 1)
    omega

theorem linForm_lt (c0 : ℕ) (coef : ℕ → ℕ) (hc : ∀ i, 1 ≤ coef i) (pre post : List ℕ)
    (a b : ℕ) (hab : a < b) : linForm c0 coef (pre ++ a :: post) < linForm c0 coef (pre ++ b :: post) := by
  have := linSum_lt coef hc 0 pre post a b hab
  simp only [linForm]
  omega

/-- The algebra of linear forms with symbol-dependent constants and coefficients. -/
def linAlg {G : Type u} (c0 : G → ℕ) (coef : G → ℕ → ℕ) : Alg G ℕ where
  interp g xs := linForm (c0 g) (coef g) xs

theorem linAlg_mono {G : Type u} (c0 : G → ℕ) (coef : G → ℕ → ℕ) (hc : ∀ g i, 1 ≤ coef g i)
    (g : G) (pre post : List ℕ) (a b : ℕ) (hab : a < b) :
    (linAlg c0 coef).interp g (pre ++ a :: post) < (linAlg c0 coef).interp g (pre ++ b :: post) :=
  linForm_lt (c0 g) (coef g) (hc g) pre post a b hab

/-! ## Rule sets and labelled terms -/

section Labelling

variable {sigma : Type u} {nu : Type v} {A : Type w} {L : Type w'}

/-- A set of rewrite rules, given by the pairs of its sides. -/
abbrev RulesP (sigma : Type u) (nu : Type v) := Term sigma nu → Term sigma nu → Prop

/-- Root instances of a rule set. -/
def PRoot (P : RulesP sigma nu) (s t : Term sigma nu) : Prop :=
  ∃ l r, P l r ∧ ∃ σ : Subst sigma nu, s = Subst.apply σ l ∧ t = Subst.apply σ r

/-- Rewriting with a possibly infinite rule set. -/
abbrev PStep (P : RulesP sigma nu) : Term sigma nu → Term sigma nu → Prop := CtxClosure (PRoot P)

/-- The rules of a finite rewrite system. -/
def inR (R : TRS sigma nu) : RulesP sigma nu := fun l r => ∃ rule ∈ R, rule.lhs = l ∧ rule.rhs = r

theorem step_iff_pStep (R : TRS sigma nu) (s t : Term sigma nu) :
    Step R s t ↔ PStep (inR R) s t := by
  rw [step_iff_ctxClosure]
  constructor
  · exact ctxClosure_mono fun s t ⟨rule, hrule, σ, hs, ht⟩ =>
      ⟨rule.lhs, rule.rhs, ⟨rule, hrule, rfl, rfl⟩, σ, hs, ht⟩
  · exact ctxClosure_mono fun s t ⟨l, r, ⟨rule, hrule, hl, hr⟩, σ, hs, ht⟩ =>
      ⟨rule, hrule, σ, by rw [hl]; exact hs, by rw [hr]; exact ht⟩

theorem acc_step_of_acc_pStep (R : TRS sigma nu) (t : Term sigma nu)
    (h : Acc (fun y x => PStep (inR R) x y) t) : SN R t :=
  Subrelation.accessible (fun {_ _} hxy => (step_iff_pStep R _ _).1 hxy) h

mutual
/-- Semantic labelling: every symbol receives the label computed from the values `E` of its
arguments; symbols without a labelling function receive `none`. -/
def lab (E : Term sigma nu → A) (ℓ : sigma → Option (List A → L)) :
    Term sigma nu → Term (sigma × Option L) nu
  | .var x => .var x
  | .app f args => .app (f, (ℓ f).map (fun g => g (args.map E))) (labList E ℓ args)
/-- Labelling of an argument list. -/
def labList (E : Term sigma nu → A) (ℓ : sigma → Option (List A → L)) :
    List (Term sigma nu) → List (Term (sigma × Option L) nu)
  | [] => []
  | t :: ts => lab E ℓ t :: labList E ℓ ts
end

theorem labList_eq_map (E : Term sigma nu → A) (ℓ : sigma → Option (List A → L))
    (ts : List (Term sigma nu)) : labList E ℓ ts = ts.map (lab E ℓ) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    show lab E ℓ t :: labList E ℓ ts = _
    rw [ih]
    rfl

@[simp] theorem lab_var (E : Term sigma nu → A) (ℓ : sigma → Option (List A → L)) (x : nu) :
    lab E ℓ (.var x) = .var x := rfl

@[simp] theorem lab_app (E : Term sigma nu → A) (ℓ : sigma → Option (List A → L)) (f : sigma)
    (args : List (Term sigma nu)) :
    lab E ℓ (.app f args) = .app (f, (ℓ f).map (fun g => g (args.map E))) (args.map (lab E ℓ)) := by
  rw [← labList_eq_map]
  rfl

/-- The labelling of a substituted term is the substituted labelling of the term under the induced
valuation: a labelled rule instance. -/
theorem lab_subst (I : Alg sigma A) (ℓ : sigma → Option (List A → L)) (α : nu → A)
    (σ : Subst sigma nu) (t : Term sigma nu) :
    lab (Alg.eval I α) ℓ (Subst.apply σ t) =
      Subst.apply (fun x => lab (Alg.eval I α) ℓ (σ x))
        (lab (Alg.eval I (fun x => Alg.eval I α (σ x))) ℓ t) := by
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
    have hvals : (args.map (Subst.apply σ)).map (Alg.eval I α) =
        args.map (Alg.eval I (fun x => Alg.eval I α (σ x))) := by
      rw [List.map_map]
      exact List.map_congr_left (fun a _ => Alg.eval_subst I α σ a)
    rw [Subst.apply_app, lab_app, lab_app, Subst.apply_app, Subst.applyList_eq_map,
      Subst.applyList_eq_map, hvals, List.map_map, List.map_map]
    congr 1
    exact List.map_congr_left (fun a ha => ih a ha)

/-- Erasing the labels of a labelled term gives the term back. -/
theorem erase_lab (E : Term sigma nu → A) (ℓ : sigma → Option (List A → L)) (t : Term sigma nu) :
    mapSym Prod.fst (lab E ℓ t) = t := by
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
    rw [lab_app, mapSym_app, List.map_map]
    congr 1
    conv_rhs => rw [← List.map_id args]
    exact List.map_congr_left (fun a ha => ih a ha)

/-- A base interpretation that ignores labels. -/
def blindAlg (K : Alg sigma ℕ) : Alg (sigma × Option L) ℕ := ⟨fun g xs => K.interp g.1 xs⟩

theorem eval_lab_blind (K : Alg sigma ℕ) (E : Term sigma nu → A)
    (ℓ : sigma → Option (List A → L)) (β : nu → ℕ) (t : Term sigma nu) :
    Alg.eval (blindAlg K) β (lab E ℓ t) = Alg.eval K β t := by
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
    rw [lab_app, Alg.eval_app, Alg.eval_app, List.map_map]
    show K.interp f _ = K.interp f _
    congr 1
    exact List.map_congr_left (fun a ha => ih a ha)

/-- Root steps of a labelled system: instances of the labelled rules `lab α l → lab α r` for every
valuation `α`, and label-decreasing steps `f_a(xs) → f_b(xs)` for `decRel a b`. -/
inductive LRoot (I : Alg sigma A) (ℓ : sigma → Option (List A → L)) (P : RulesP sigma nu)
    (decRel : L → L → Prop) : Term (sigma × Option L) nu → Term (sigma × Option L) nu → Prop
  | rule {l r : Term sigma nu} (h : P l r) (α : nu → A) (τ : Subst (sigma × Option L) nu) :
      LRoot I ℓ P decRel (Subst.apply τ (lab (Alg.eval I α) ℓ l))
        (Subst.apply τ (lab (Alg.eval I α) ℓ r))
  | decr (f : sigma) {a b : L} (h : decRel a b) (args : List (Term (sigma × Option L) nu)) :
      LRoot I ℓ P decRel (.app (f, some a) args) (.app (f, some b) args)

/-- The labelled rewrite relation. -/
abbrev LStep (I : Alg sigma A) (ℓ : sigma → Option (List A → L)) (P : RulesP sigma nu)
    (decRel : L → L → Prop) := CtxClosure (LRoot I ℓ P decRel)

/-- An algebra is a model of a rule set when both sides of every rule have equal values under every
valuation. -/
def IsModel (I : Alg sigma A) (P : RulesP sigma nu) : Prop :=
  ∀ l r, P l r → ∀ α : nu → A, Alg.eval I α l = Alg.eval I α r

theorem eval_eq_of_pStep {I : Alg sigma A} {P : RulesP sigma nu} (hM : IsModel I P)
    (α : nu → A) {s t : Term sigma nu} (h : PStep P s t) : Alg.eval I α s = Alg.eval I α t := by
  induction h with
  | root h =>
    obtain ⟨l, r, hlr, σ, rfl, rfl⟩ := h
    rw [Alg.eval_subst, Alg.eval_subst]
    exact hM l r hlr _
  | arg f pre post _ ih =>
    rw [Alg.eval_app, Alg.eval_app, List.map_append, List.map_append, List.map_cons,
      List.map_cons, ih]

/-- Zantema's lifting lemma for models: every source step lifts to one labelled step. -/
theorem lab_lift_model {I : Alg sigma A} {ℓ : sigma → Option (List A → L)}
    {P : RulesP sigma nu} {decRel : L → L → Prop} (hM : IsModel I P) (α : nu → A)
    {s t : Term sigma nu} (h : PStep P s t) :
    LStep I ℓ P decRel (lab (Alg.eval I α) ℓ s) (lab (Alg.eval I α) ℓ t) := by
  induction h with
  | root h =>
    obtain ⟨l, r, hlr, σ, rfl, rfl⟩ := h
    rw [lab_subst, lab_subst]
    exact .root (.rule hlr _ _)
  | @arg f pre post a b hab ih =>
    have hv : Alg.eval I α a = Alg.eval I α b := eval_eq_of_pStep hM α hab
    have hmap : (pre ++ a :: post).map (Alg.eval I α) = (pre ++ b :: post).map (Alg.eval I α) := by
      simp [hv]
    rw [lab_app, lab_app, hmap]
    simp only [List.map_append, List.map_cons]
    exact .arg _ _ _ ih

/-- Termination transfer: accessibility of the labelled image gives accessibility of the term. -/
theorem acc_of_lab_model {I : Alg sigma A} {ℓ : sigma → Option (List A → L)}
    {P : RulesP sigma nu} {decRel : L → L → Prop} (hM : IsModel I P) (α : nu → A)
    (t : Term sigma nu)
    (hacc : Acc (fun y x => LStep I ℓ P decRel x y) (lab (Alg.eval I α) ℓ t)) :
    Acc (fun y x => PStep P x y) t := by
  have h1 : Acc (InvImage (fun y x => LStep I ℓ P decRel x y) (lab (Alg.eval I α) ℓ)) t :=
    InvImage.accessible _ hacc
  exact Subrelation.accessible (fun {_ _} hxy => lab_lift_model hM α hxy) h1

/-- Unlabelling: erasing labels maps every step of a labelled system without label-decreasing rules
to a source step (Sternagel and Thiemann, RTA 2011, Lemma 2.2(3)). -/
theorem erase_lstep {I : Alg sigma A} {ℓ : sigma → Option (List A → L)} {P : RulesP sigma nu}
    {x y : Term (sigma × Option L) nu} (h : LStep I ℓ P (fun _ _ => False) x y) :
    PStep P (mapSym Prod.fst x) (mapSym Prod.fst y) := by
  induction h with
  | root h =>
    cases h with
    | rule hlr α τ =>
      rw [mapSym_subst, mapSym_subst, erase_lab, erase_lab]
      exact .root ⟨_, _, hlr, _, rfl, rfl⟩
    | decr f h args => exact h.elim
  | arg g pre post _ ih =>
    rw [mapSym_app, mapSym_app]
    simp only [List.map_append, List.map_cons]
    exact .arg _ _ _ ih

/-- A strictly monotone natural-number algebra on the labelled signature that decreases on every
labelled rule instance and on every label-decreasing step proves termination of the labelled
system. -/
theorem lstep_wf_of_interp (I : Alg sigma A) (ℓ : sigma → Option (List A → L))
    (P : RulesP sigma nu) (decRel : L → L → Prop) (J : Alg (sigma × Option L) ℕ) (β0 : nu → ℕ)
    (hmono : ∀ (g : sigma × Option L) (pre post : List ℕ) (a b : ℕ), a < b →
      J.interp g (pre ++ a :: post) < J.interp g (pre ++ b :: post))
    (hrule : ∀ l r, P l r → ∀ (α : nu → A) (β : nu → ℕ),
      Alg.eval J β (lab (Alg.eval I α) ℓ r) < Alg.eval J β (lab (Alg.eval I α) ℓ l))
    (hdec : ∀ (f : sigma) (a b : L) (xs : List ℕ), decRel a b →
      J.interp (f, some b) xs < J.interp (f, some a) xs) :
    WellFounded (fun y x => LStep I ℓ P decRel x y) := by
  refine ctxClosure_wf_of_measure (Alg.eval J β0) ?_ ?_
  · intro s t h
    cases h with
    | rule hlr α τ =>
      rw [Alg.eval_subst, Alg.eval_subst]
      exact hrule _ _ hlr α _
    | decr f h args =>
      rw [Alg.eval_app, Alg.eval_app]
      exact hdec f _ _ _ h
  · intro g pre post a b hab
    rw [Alg.eval_app, Alg.eval_app, List.map_append, List.map_append, List.map_cons,
      List.map_cons]
    exact hmono g _ _ _ _ hab

/-- Soundness of semantic labelling with a model and a base interpretation of the labelled
signature (Zantema, Fundamenta Informaticae 24, 1995, model version, as restated in
Hirokawa-Middeldorp, RTA 2006, Theorem 2, soundness direction). -/
theorem sn_of_model_labelling (R : TRS sigma nu) (I : Alg sigma A)
    (ℓ : sigma → Option (List A → L)) (J : Alg (sigma × Option L) ℕ) (α0 : nu → A)
    (hM : IsModel I (inR R))
    (hmono : ∀ (g : sigma × Option L) (pre post : List ℕ) (a b : ℕ), a < b →
      J.interp g (pre ++ a :: post) < J.interp g (pre ++ b :: post))
    (hrule : ∀ rule ∈ R, ∀ (α : nu → A) (β : nu → ℕ),
      Alg.eval J β (lab (Alg.eval I α) ℓ rule.rhs) < Alg.eval J β (lab (Alg.eval I α) ℓ rule.lhs)) :
    ∀ t : Term sigma nu, SN R t := by
  have hwf : WellFounded (fun y x => LStep I ℓ (inR R) (fun _ _ : L => False) x y) :=
    lstep_wf_of_interp I ℓ (inR R) (fun _ _ => False) J (fun _ => 0) hmono
      (fun l r ⟨rule, hmem, hl, hr⟩ α β => by rw [← hl, ← hr]; exact hrule rule hmem α β)
      (fun _ _ _ _ h => h.elim)
  intro t
  exact acc_step_of_acc_pStep R t (acc_of_lab_model hM α0 t (hwf.apply _))

end Labelling

/-! ## The free recursor -/

theorem mem_freeRecursorTRS {rule : Rule FreeSym Nat} :
    rule ∈ freeRecursorTRS ↔ rule = zeroRule ∨ rule = succRule := by
  simp [freeRecursorTRS]

/-- Termination of the free recursor. -/
def FreeTerminates : Prop := ∀ t : Term FreeSym Nat, SN freeRecursorTRS t

/-! ## Row: semanticLabeling -/

/-- Native data of semantic labelling on the free recursor: an algebra over `ℕ`, a labelling, and a
linear base interpretation of the labelled signature. -/
structure SemLabData where
  I : Alg FreeSym ℕ
  ℓ : FreeSym → Option (List ℕ → ℕ)
  c0 : FreeSym × Option ℕ → ℕ
  coef : FreeSym × Option ℕ → ℕ → ℕ

abbrev semanticLabelingData : Type := SemLabData

/-- The base interpretation of the labelled signature. -/
def SemLabData.base (M : SemLabData) : Alg (FreeSym × Option ℕ) ℕ := linAlg M.c0 M.coef

/-- Zantema (Termination of term rewriting by semantic labelling, Fundamenta Informaticae 24, 1995,
model version; restated as Theorem 2 of Hirokawa and Middeldorp, Predictive labeling, RTA 2006):
the algebra is a model of every rule; the base interpretation is strictly monotone. -/
def semanticLabelingLaws (M : semanticLabelingData) : Prop :=
  IsModel M.I (inR freeRecursorTRS) ∧ ∀ g i, 1 ≤ M.coef g i

/-- The base interpretation orients every labelled rule instance of the free recursor. -/
def semanticLabelingAccepts (M : semanticLabelingData) : Prop :=
  ∀ rule ∈ freeRecursorTRS, ∀ (α β : Nat → ℕ),
    Alg.eval M.base β (lab (Alg.eval M.I α) M.ℓ rule.rhs) <
      Alg.eval M.base β (lab (Alg.eval M.I α) M.ℓ rule.lhs)

/-- Verdict: escape. -/
def semanticLabelingResult (M : semanticLabelingData) : Prop :=
  semanticLabelingAccepts M ∧ FreeTerminates

theorem semanticLabeling_sound :
    ∀ M, semanticLabelingLaws M → semanticLabelingAccepts M → FreeTerminates :=
  fun M hM hA => sn_of_model_labelling freeRecursorTRS M.I M.ℓ M.base (fun _ => 0) hM.1
    (fun g pre post a b hab => linAlg_mono M.c0 M.coef hM.2 g pre post a b hab) hA

/-- The counter model: `zero = 0`, `succ x = x + 1`, `wrap x y = y`, `recur b s n = b`. -/
def counterModel : Alg FreeSym ℕ where
  interp f xs := match f with
    | .zero => 0
    | .succ => xs.headD 0 + 1
    | .wrap => xs.getD 1 0
    | .recur => xs.headD 0

/-- Label the recursor by the value of its counter. -/
def counterLab : FreeSym → Option (List ℕ → ℕ)
  | .recur => some (fun xs => xs.getD 2 0)
  | _ => none

/-- Base constants: `recur_k(b, s, n) = (k + 1) + b + (k + 1) s + n`, `wrap(x, y) = 1 + x + y`,
`succ(x) = 1 + x`, `zero = 0`. -/
def counterC0 : FreeSym × Option ℕ → ℕ
  | (.recur, some k) => k + 1
  | (.zero, _) => 0
  | _ => 1

/-- Base coefficients: the payload coefficient of `recur_k` is `k + 1`, all others are `1`. -/
def counterCoef : FreeSym × Option ℕ → ℕ → ℕ
  | (.recur, some k), 1 => k + 1
  | _, _ => 1

theorem counterCoef_pos : ∀ g i, 1 ≤ counterCoef g i := by
  intro g i
  rcases g with ⟨f, o⟩
  cases f <;> cases o <;> rcases i with _ | _ | i <;> simp [counterCoef]

def semanticLabelingWitness : semanticLabelingData :=
  ⟨counterModel, counterLab, counterC0, counterCoef⟩

theorem counterModel_isModel : IsModel counterModel (inR freeRecursorTRS) := by
  rintro l r ⟨rule, hrule, rfl, rfl⟩ α
  rcases mem_freeRecursorTRS.1 hrule with rfl | rfl
  · simp [zeroRule, counterModel]
  · simp [succRule, counterModel]

theorem semanticLabelingWitness_laws : semanticLabelingLaws semanticLabelingWitness :=
  ⟨counterModel_isModel, counterCoef_pos⟩

theorem semanticLabelingWitness_accepts : semanticLabelingAccepts semanticLabelingWitness := by
  intro rule hrule α β
  rcases mem_freeRecursorTRS.1 hrule with rfl | rfl
  · simp [semanticLabelingWitness, SemLabData.base, linAlg, linForm, linSum, zeroRule,
      counterModel, counterLab, counterC0, counterCoef]
    omega
  · simp [semanticLabelingWitness, SemLabData.base, linAlg, linForm, linSum, succRule,
      counterModel, counterLab, counterC0, counterCoef]
    nlinarith

theorem semanticLabelingWitness_result : semanticLabelingResult semanticLabelingWitness :=
  ⟨semanticLabelingWitness_accepts,
    semanticLabeling_sound _ semanticLabelingWitness_laws semanticLabelingWitness_accepts⟩

/-- Concrete free terms. -/
def fz : Term FreeSym Nat := .app .zero []

def fs (t : Term FreeSym Nat) : Term FreeSym Nat := .app .succ [t]

def fw (s t : Term FreeSym Nat) : Term FreeSym Nat := .app .wrap [s, t]

def fr (b s n : Term FreeSym Nat) : Term FreeSym Nat := .app .recur [b, s, n]

/-- The substitution `0 ↦ b`, `1 ↦ s`, `2 ↦ n`. -/
def sub3 (b s n : Term FreeSym Nat) : Subst FreeSym Nat :=
  fun i => if i = 0 then b else if i = 1 then s else n

theorem step_zero (b s : Term FreeSym Nat) : Step freeRecursorTRS (fr b s fz) b :=
  Step.root ⟨zeroRule, by simp [freeRecursorTRS], sub3 b s fz, by simp [zeroRule, sub3, fr, fz],
    by simp [zeroRule, sub3]⟩

theorem step_succ (b s n : Term FreeSym Nat) :
    Step freeRecursorTRS (fr b s (fs n)) (fw s (fr b s n)) :=
  Step.root ⟨succRule, by simp [freeRecursorTRS], sub3 b s n, by simp [succRule, sub3, fr, fs],
    by simp [succRule, sub3, fw, fr]⟩

/-- The counter labels are nonconstant; a step inside the counter of a labelled recursor keeps its
label, because the counter model gives the redex and its contractum the same value; a substituted
rule instance is a labelled rule instance; every source step lifts to a labelled step. -/
theorem semanticLabelingWitness_feature :
    rootSym (lab (Alg.eval counterModel (fun _ => 0)) counterLab (fr fz fz (fs (fs fz)))) =
        some (FreeSym.recur, some 2) ∧
      rootSym (lab (Alg.eval counterModel (fun _ => 0)) counterLab (fr fz fz (fs fz))) =
        some (FreeSym.recur, some 1) ∧
      Step freeRecursorTRS (fr fz fz (fr (fs fz) fz fz)) (fr fz fz (fs fz)) ∧
      rootSym (lab (Alg.eval counterModel (fun _ => 0)) counterLab (fr fz fz (fr (fs fz) fz fz))) =
        some (FreeSym.recur, some 1) ∧
      (∀ (σ : Subst FreeSym Nat) (α : Nat → ℕ) (t : Term FreeSym Nat),
        lab (Alg.eval counterModel α) counterLab (Subst.apply σ t) =
          Subst.apply (fun x => lab (Alg.eval counterModel α) counterLab (σ x))
            (lab (Alg.eval counterModel (fun x => Alg.eval counterModel α (σ x))) counterLab t)) ∧
      (∀ (α : Nat → ℕ) (s t : Term FreeSym Nat), Step freeRecursorTRS s t →
        LStep counterModel counterLab (inR freeRecursorTRS) (fun _ _ : ℕ => False)
          (lab (Alg.eval counterModel α) counterLab s) (lab (Alg.eval counterModel α) counterLab t)) :=
  ⟨by simp [rootSym, fr, fs, fz, counterLab, counterModel],
    by simp [rootSym, fr, fs, fz, counterLab, counterModel],
    Step.arg FreeSym.recur [fz, fz] [] (step_zero (fs fz) fz),
    by simp [rootSym, fr, fs, fz, counterLab, counterModel],
    fun σ α t => lab_subst counterModel counterLab α σ t,
    fun α _ _ h => lab_lift_model counterModel_isModel α ((step_iff_pStep _ _ _).1 h)⟩

/-- The constant labelling of the recursor. -/
def constLab : FreeSym → Option (List ℕ → ℕ)
  | .recur => some (fun _ => 0)
  | _ => none

/-- The witness with the counter labelling replaced by the constant labelling. -/
def semanticLabelingMutation : semanticLabelingData :=
  ⟨counterModel, constLab, counterC0, counterCoef⟩

/-- Replacing the counter labelling by the constant labelling keeps the laws and loses acceptance:
all recursors then carry the label `0` and the linear base cannot absorb the payload copy. -/
theorem semanticLabeling_mutation :
    semanticLabelingLaws semanticLabelingMutation ∧
      ¬ semanticLabelingAccepts semanticLabelingMutation := by
  refine ⟨⟨counterModel_isModel, counterCoef_pos⟩, fun h => ?_⟩
  have := h succRule (by simp [freeRecursorTRS]) (fun _ => 0) (fun _ => 0)
  simp [semanticLabelingMutation, SemLabData.base, linAlg, linForm, linSum, succRule,
    counterModel, constLab, counterC0, counterCoef] at this

/-! ## Row: rootLabeling -/

section RootLabelling

variable {sigma : Type u} {nu : Type v}

/-- The root algebra: a term evaluates to its root symbol (Sternagel and Thiemann, Modular and
certified semantic labeling and unlabeling, RTA 2011, Definition 3.13, restating Sternagel and
Middeldorp, Root-labeling, RTA 2008). -/
def rootAlg : Alg sigma sigma := ⟨fun f _ => f⟩

/-- Root labelling: every symbol is labelled by the tuple of the root symbols of its arguments. -/
def rootLab : sigma → Option (List sigma → List sigma) := fun _ => some id

@[simp] theorem rootAlg_interp (f : sigma) (xs : List sigma) :
    (rootAlg : Alg sigma sigma).interp f xs = f := rfl

theorem rootAlg_eval_app (α : nu → sigma) (f : sigma) (args : List (Term sigma nu)) :
    Alg.eval (rootAlg : Alg sigma sigma) α (.app f args) = f := by
  rw [Alg.eval_app]
  rfl

/-- A rule changes its root when its right-hand side is a variable or has another root symbol. -/
def RootChanges (rule : Rule sigma nu) : Prop :=
  ∀ f largs, rule.lhs = .app f largs → ∀ g rargs, rule.rhs = .app g rargs → g ≠ f

/-- The closure under flat contexts (Sternagel and Thiemann, RTA 2011, Definition 3.14), given by the
instances of its rules: the rules of `R` that keep their root, and every instance
`f(us, σ l, vs) → f(us, σ r, vs)` of a root-changing rule `l → r`. The instances generate the same
rewrite relation as the flat contexts with fresh variables. -/
def fcRules (R : TRS sigma nu) : RulesP sigma nu := fun l r =>
  (∃ rule ∈ R, ¬ RootChanges rule ∧ l = rule.lhs ∧ r = rule.rhs) ∨
    ∃ rule ∈ R, RootChanges rule ∧ ∃ (f : sigma) (us vs : List (Term sigma nu))
      (σ : Subst sigma nu), l = .app f (us ++ Subst.apply σ rule.lhs :: vs) ∧
        r = .app f (us ++ Subst.apply σ rule.rhs :: vs)

/-- The root algebra is a model of the closure under flat contexts. -/
theorem rootAlg_model_fc (R : TRS sigma nu) :
    IsModel (rootAlg : Alg sigma sigma) (fcRules R) := by
  intro l r h α
  rcases h with ⟨rule, _, hch, rfl, rfl⟩ | ⟨rule, _, _, f, us, vs, σ, rfl, rfl⟩
  · unfold RootChanges at hch
    push_neg at hch
    obtain ⟨f, largs, hl, g, rargs, hr, hgf⟩ := hch
    rw [hl, hr, rootAlg_eval_app, rootAlg_eval_app, hgf]
  · rw [rootAlg_eval_app, rootAlg_eval_app]

/-- Steps of the flat-context closure are steps of `R`. -/
theorem step_of_fcStep (R : TRS sigma nu) {s t : Term sigma nu} (h : PStep (fcRules R) s t) :
    Step R s t := by
  induction h with
  | root h =>
    obtain ⟨l, r, hlr, τ, rfl, rfl⟩ := h
    rcases hlr with ⟨rule, hrule, _, rfl, rfl⟩ | ⟨rule, hrule, _, f, us, vs, σ, rfl, rfl⟩
    · exact Step.root ⟨rule, hrule, τ, rfl, rfl⟩
    · simp only [Subst.apply_app, Subst.applyList_eq_map, List.map_append, List.map_cons]
      rw [← Subst.apply_comp, ← Subst.apply_comp]
      exact Step.arg f _ _ (Step.root ⟨rule, hrule, Subst.comp τ σ, rfl, rfl⟩)
  | arg f pre post _ ih => exact Step.arg f pre post ih

/-- Every step of `R` is a step of the flat-context closure inside any flat context. -/
theorem fcStep_of_step (R : TRS sigma nu) {s t : Term sigma nu} (h : Step R s t) :
    ∀ (f : sigma) (us vs : List (Term sigma nu)),
      PStep (fcRules R) (.app f (us ++ s :: vs)) (.app f (us ++ t :: vs)) := by
  induction h with
  | root h =>
    obtain ⟨rule, hrule, σ, rfl, rfl⟩ := h
    intro f us vs
    by_cases hch : RootChanges rule
    · exact .root ⟨_, _, Or.inr ⟨rule, hrule, hch, f, us, vs, σ, rfl, rfl⟩, Subst.id,
        (Subst.id_apply _).symm, (Subst.id_apply _).symm⟩
    · exact .arg f us vs (.root ⟨_, _, Or.inl ⟨rule, hrule, hch, rfl, rfl⟩, σ, rfl, rfl⟩)
  | arg g pre post _ ih =>
    intro f us vs
    exact .arg f us vs (ih g pre post)

/-- Termination of the flat-context closure gives termination of `R`: every step of `R` is a step
of the closure inside the flat context `f0(□)`. -/
theorem sn_of_fc_sn (R : TRS sigma nu) (f0 : sigma)
    (h : ∀ t, Acc (fun y x => PStep (fcRules R) x y) t) (t : Term sigma nu) : SN R t := by
  have h1 : Acc (InvImage (fun y x => PStep (fcRules R) x y)
      (fun t : Term sigma nu => Term.app f0 ([] ++ t :: []))) t :=
    InvImage.accessible _ (h _)
  exact Subrelation.accessible (fun {_ _} hxy => fcStep_of_step R hxy f0 [] []) h1

/-- Soundness of root labelling: a strictly monotone base interpretation that orients every
root-labelled instance of the flat-context closure proves termination of `R`. -/
theorem sn_of_rootLabelling (R : TRS sigma nu) (f0 : sigma) (α0 : nu → sigma)
    (J : Alg (sigma × Option (List sigma)) ℕ)
    (hmono : ∀ (g : sigma × Option (List sigma)) (pre post : List ℕ) (a b : ℕ), a < b →
      J.interp g (pre ++ a :: post) < J.interp g (pre ++ b :: post))
    (hrule : ∀ l r, fcRules R l r → ∀ (α : nu → sigma) (β : nu → ℕ),
      Alg.eval J β (lab (Alg.eval rootAlg α) rootLab r) <
        Alg.eval J β (lab (Alg.eval rootAlg α) rootLab l)) :
    ∀ t : Term sigma nu, SN R t := by
  have hwf := lstep_wf_of_interp rootAlg rootLab (fcRules R) (fun _ _ : List sigma => False) J
    (fun _ => 0) hmono hrule (fun _ _ _ _ h => h.elim)
  exact sn_of_fc_sn R f0 (fun t => acc_of_lab_model (rootAlg_model_fc R) α0 t (hwf.apply _))

end RootLabelling

/-- The coupled polynomial on argument lists: `recur(xs) = (1 + Σ xs) * (xs[2] + 1)`, every other
symbol `1 + Σ xs`. -/
def cpAlg : Alg FreeSym ℕ where
  interp f xs := match f with
    | .recur => (1 + xs.sum) * (xs.getD 2 0 + 1)
    | _ => 1 + xs.sum

theorem sum_lt_of_lt (pre post : List ℕ) {a b : ℕ} (h : a < b) :
    (pre ++ a :: post).sum < (pre ++ b :: post).sum := by
  simp only [List.sum_append, List.sum_cons]
  omega

theorem getD_le_of_le (pre post : List ℕ) {a b : ℕ} (h : a ≤ b) (i : ℕ) :
    (pre ++ a :: post).getD i 0 ≤ (pre ++ b :: post).getD i 0 := by
  induction pre generalizing i with
  | nil =>
    cases i with
    | zero => simpa using h
    | succ i => simp
  | cons x pre ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

theorem cpAlg_mono (f : FreeSym) (pre post : List ℕ) (a b : ℕ) (hab : a < b) :
    cpAlg.interp f (pre ++ a :: post) < cpAlg.interp f (pre ++ b :: post) := by
  have hs := sum_lt_of_lt pre post hab
  cases f with
  | recur =>
    have hg := getD_le_of_le pre post hab.le 2
    show (1 + (pre ++ a :: post).sum) * ((pre ++ a :: post).getD 2 0 + 1) <
      (1 + (pre ++ b :: post).sum) * ((pre ++ b :: post).getD 2 0 + 1)
    calc (1 + (pre ++ a :: post).sum) * ((pre ++ a :: post).getD 2 0 + 1)
        ≤ (1 + (pre ++ a :: post).sum) * ((pre ++ b :: post).getD 2 0 + 1) :=
          Nat.mul_le_mul_left _ (by omega)
      _ < (1 + (pre ++ b :: post).sum) * ((pre ++ b :: post).getD 2 0 + 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  | zero =>
    show 1 + (pre ++ a :: post).sum < 1 + (pre ++ b :: post).sum
    omega
  | succ =>
    show 1 + (pre ++ a :: post).sum < 1 + (pre ++ b :: post).sum
    omega
  | wrap =>
    show 1 + (pre ++ a :: post).sum < 1 + (pre ++ b :: post).sum
    omega

/-- The coupled polynomial orients both rules of the free recursor at every valuation. -/
theorem cpAlg_orients (rule : Rule FreeSym Nat) (hrule : rule ∈ freeRecursorTRS) (β : Nat → ℕ) :
    Alg.eval cpAlg β rule.rhs < Alg.eval cpAlg β rule.lhs := by
  rcases mem_freeRecursorTRS.1 hrule with rfl | rfl
  · simp [zeroRule, cpAlg]
    nlinarith
  · simp [succRule, cpAlg]
    nlinarith

/-- Native data of root labelling on the free recursor: a base interpretation of the root-labelled
signature. The root algebra, the labels and the flat-context closure are fixed by the method. -/
abbrev rootLabelingData : Type := Alg (FreeSym × Option (List FreeSym)) ℕ

/-- Sternagel and Middeldorp (Root-labeling, RTA 2008), as restated by Sternagel and Thiemann (RTA
2011, Definitions 3.13 and 3.14): the root algebra and the argument-root labels are applied to the
closure under flat contexts; the base interpretation is strictly monotone in every argument. -/
def rootLabelingLaws (J : rootLabelingData) : Prop :=
  ∀ (g : FreeSym × Option (List FreeSym)) (pre post : List ℕ) (a b : ℕ), a < b →
    J.interp g (pre ++ a :: post) < J.interp g (pre ++ b :: post)

/-- The base interpretation orients every root-labelled instance of the flat-context closure of the
free recursor. -/
def rootLabelingAccepts (J : rootLabelingData) : Prop :=
  ∀ l r, fcRules freeRecursorTRS l r → ∀ (α : Nat → FreeSym) (β : Nat → ℕ),
    Alg.eval J β (lab (Alg.eval rootAlg α) rootLab r) <
      Alg.eval J β (lab (Alg.eval rootAlg α) rootLab l)

/-- Verdict: escape. The base of the witness is label-blind and nonlinear; no label-indexed linear
base succeeds (`rootLabeling_linear_barrier`). -/
def rootLabelingResult (J : rootLabelingData) : Prop := rootLabelingAccepts J ∧ FreeTerminates

theorem rootLabeling_sound :
    ∀ J, rootLabelingLaws J → rootLabelingAccepts J → FreeTerminates :=
  fun J hL hA => sn_of_rootLabelling freeRecursorTRS FreeSym.succ (fun _ => FreeSym.zero) J hL hA

def rootLabelingWitness : rootLabelingData := blindAlg cpAlg

theorem rootLabelingWitness_laws : rootLabelingLaws rootLabelingWitness :=
  fun g pre post a b hab => cpAlg_mono g.1 pre post a b hab

theorem rootLabelingWitness_accepts : rootLabelingAccepts rootLabelingWitness := by
  intro l r h α β
  show Alg.eval (blindAlg cpAlg) β _ < Alg.eval (blindAlg cpAlg) β _
  rw [eval_lab_blind, eval_lab_blind]
  rcases h with ⟨rule, hrule, _, rfl, rfl⟩ | ⟨rule, hrule, _, f, us, vs, σ, rfl, rfl⟩
  · exact cpAlg_orients rule hrule β
  · simp only [Alg.eval_app, List.map_append, List.map_cons, Alg.eval_subst]
    exact cpAlg_mono f _ _ _ _ (cpAlg_orients rule hrule _)

theorem rootLabelingWitness_result : rootLabelingResult rootLabelingWitness :=
  ⟨rootLabelingWitness_accepts,
    rootLabeling_sound _ rootLabelingWitness_laws rootLabelingWitness_accepts⟩

theorem succRule_rootChanges : RootChanges succRule := by
  intro f largs hl g rargs hr
  simp only [succRule, Term.app.injEq] at hl hr
  rw [← hl.1, ← hr.1]
  decide

theorem zeroRule_rootChanges : RootChanges zeroRule := by
  intro f largs _ g rargs hr
  simp [zeroRule] at hr

/-- The root algebra is not a model of the free recursor: the successor rule changes the root from
the recursor to the wrapper. -/
theorem rootAlg_not_model : ¬ IsModel (rootAlg : Alg FreeSym FreeSym) (inR freeRecursorTRS) := by
  intro h
  have := h succRule.lhs succRule.rhs ⟨succRule, by simp [freeRecursorTRS], rfl, rfl⟩
    (fun _ => FreeSym.zero)
  simp [succRule] at this

/-- No label-indexed linear base orients the root-labelled flat-context closure of the free
recursor. In the wrapper context, with the payload and the sibling valued in the same root and the
counter valued in `succ`, the labelled successor rule carries the same wrapper label and the same
recursor label on both sides, so the second payload copy is not compensated. -/
theorem rootLabeling_linear_barrier (c0 : FreeSym × Option (List FreeSym) → ℕ)
    (coef : FreeSym × Option (List FreeSym) → ℕ → ℕ) (hc : ∀ g i, 1 ≤ coef g i) :
    ¬ rootLabelingAccepts (linAlg c0 coef) := by
  intro h
  obtain ⟨S, hS⟩ : ∃ S, coef (FreeSym.wrap, some [FreeSym.zero, FreeSym.recur]) 1 *
      (coef (FreeSym.recur, some [FreeSym.zero, FreeSym.zero, FreeSym.succ]) 2 *
        c0 (FreeSym.succ, some [FreeSym.succ])) < S := ⟨_, Nat.lt_succ_self _⟩
  have hfc : fcRules freeRecursorTRS (fw (.var 3) (fr (.var 0) (.var 1) (fs (.var 2))))
      (fw (.var 3) (fw (.var 1) (fr (.var 0) (.var 1) (.var 2)))) :=
    Or.inr ⟨succRule, by simp [freeRecursorTRS], succRule_rootChanges, FreeSym.wrap, [.var 3], [],
      Subst.id, by simp [succRule, fw, fr, fs, Subst.id], by simp [succRule, fw, fr, Subst.id]⟩
  have key := h _ _ hfc (fun n => if n = 2 then FreeSym.succ else FreeSym.zero)
    (fun n => if n = 1 then S else 0)
  simp [fw, fr, fs, linAlg, linForm, linSum, rootLab] at key
  have hp : S ≤ coef (FreeSym.wrap, some [FreeSym.zero, FreeSym.recur]) 0 * S :=
    Nat.le_mul_of_pos_left S (hc _ 0)
  have hX := Nat.le_mul_of_pos_left
    (c0 (FreeSym.wrap, some [FreeSym.zero, FreeSym.recur]) +
      coef (FreeSym.wrap, some [FreeSym.zero, FreeSym.recur]) 0 * S +
        coef (FreeSym.wrap, some [FreeSym.zero, FreeSym.recur]) 1 *
          (c0 (FreeSym.recur, some [FreeSym.zero, FreeSym.zero, FreeSym.succ]) +
            coef (FreeSym.recur, some [FreeSym.zero, FreeSym.zero, FreeSym.succ]) 1 * S))
    (hc (FreeSym.wrap, some [FreeSym.zero, FreeSym.wrap]) 1)
  nlinarith

/-- The label-blind linear interpretation `1 + Σ xs` of every symbol. -/
def cpLinAlg : Alg FreeSym ℕ := ⟨fun _ xs => 1 + xs.sum⟩

theorem linSum_one (i : ℕ) (xs : List ℕ) : linSum (fun _ => 1) i xs = xs.sum := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simp [linSum, ih]

theorem blind_cpLinAlg : (blindAlg cpLinAlg : rootLabelingData) = linAlg (fun _ => 1) (fun _ _ => 1) := by
  show (⟨fun g xs => 1 + xs.sum⟩ : rootLabelingData) = ⟨fun g xs => linForm 1 (fun _ => 1) xs⟩
  congr 1
  funext g xs
  simp [linForm, linSum_one]

/-- Replacing the recursor interpretation of the witness by the linear form `1 + Σ xs` keeps the laws
and loses acceptance. -/
theorem rootLabeling_mutation :
    rootLabelingLaws (blindAlg cpLinAlg) ∧ ¬ rootLabelingAccepts (blindAlg cpLinAlg) := by
  rw [blind_cpLinAlg]
  exact ⟨fun g pre post a b hab => linAlg_mono _ _ (fun _ _ => le_rfl) g pre post a b hab,
    rootLabeling_linear_barrier _ _ (fun _ _ => le_rfl)⟩

/-- The root algebra is a model of the flat-context closure and not of the free recursor; in a
successor context the root label of the enclosing symbol changes with the step; and no
label-indexed linear base orients the root-labelled closure. -/
theorem rootLabelingWitness_feature :
    ¬ IsModel (rootAlg : Alg FreeSym FreeSym) (inR freeRecursorTRS) ∧
      IsModel (rootAlg : Alg FreeSym FreeSym) (fcRules freeRecursorTRS) ∧
      (∀ α : Nat → FreeSym,
        rootSym (lab (Alg.eval rootAlg α) rootLab (.app FreeSym.succ [succRule.lhs])) =
            some (FreeSym.succ, some [FreeSym.recur]) ∧
          rootSym (lab (Alg.eval rootAlg α) rootLab (.app FreeSym.succ [succRule.rhs])) =
            some (FreeSym.succ, some [FreeSym.wrap])) ∧
      (∀ c0 coef, (∀ g i, 1 ≤ coef g i) → ¬ rootLabelingAccepts (linAlg c0 coef)) :=
  ⟨rootAlg_not_model, rootAlg_model_fc _,
    fun α => ⟨by simp [succRule, rootLab, rootSym],
      by simp [succRule, rootLab, rootSym]⟩,
    rootLabeling_linear_barrier⟩

/-! ## Row: selfLabelingEquational -/

section Equational

variable {sigma : Type u} {nu : Type v}

theorem pStep_subst {P : RulesP sigma nu} (σ : Subst sigma nu) {s t : Term sigma nu}
    (h : PStep P s t) : PStep P (Subst.apply σ s) (Subst.apply σ t) := by
  induction h with
  | root h =>
    obtain ⟨l, r, hlr, τ, rfl, rfl⟩ := h
    exact .root ⟨l, r, hlr, Subst.comp σ τ, (Subst.apply_comp σ τ l).symm,
      (Subst.apply_comp σ τ r).symm⟩
  | arg f pre post _ ih =>
    simp only [Subst.apply_app, Subst.applyList_eq_map, List.map_append, List.map_cons]
    exact .arg f _ _ ih

/-- The congruence generated by the equations `E`. -/
def EqCongr (E : List (Term sigma nu × Term sigma nu)) : Term sigma nu → Term sigma nu → Prop :=
  Relation.EqvGen (PStep (fun l r => (l, r) ∈ E))

theorem eqCongr_subst (E : List (Term sigma nu × Term sigma nu)) (σ : Subst sigma nu)
    {s t : Term sigma nu} (h : EqCongr E s t) : EqCongr E (Subst.apply σ s) (Subst.apply σ t) := by
  unfold EqCongr at h ⊢
  induction h with
  | rel x y hxy => exact .rel _ _ (pStep_subst σ hxy)
  | refl x => exact .refl _
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

theorem eqCongr_arg (E : List (Term sigma nu × Term sigma nu)) (f : sigma)
    (pre post : List (Term sigma nu)) {a b : Term sigma nu} (h : EqCongr E a b) :
    EqCongr E (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post)) := by
  unfold EqCongr at h ⊢
  induction h with
  | rel x y hxy => exact .rel _ _ (.arg f pre post hxy)
  | refl x => exact .refl _
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

theorem eqCongr_args (E : List (Term sigma nu × Term sigma nu)) (f : sigma) :
    ∀ (pre xs ys : List (Term sigma nu)), List.Forall₂ (EqCongr E) xs ys →
      EqCongr E (.app f (pre ++ xs)) (.app f (pre ++ ys)) := by
  intro pre xs ys h
  induction h generalizing pre with
  | nil => exact Relation.EqvGen.refl _
  | @cons x y xs ys hxy _ ih =>
    have h1 : EqCongr E (.app f (pre ++ x :: xs)) (.app f (pre ++ y :: xs)) :=
      eqCongr_arg E f pre xs hxy
    have h2 := ih (pre ++ [y])
    simp only [List.append_assoc, List.singleton_append] at h2
    exact Relation.EqvGen.trans _ _ _ h1 h2

/-- The setoid of the congruence. -/
def eqSetoid (E : List (Term sigma nu × Term sigma nu)) : Setoid (Term sigma nu) :=
  ⟨EqCongr E, Relation.EqvGen.is_equivalence _⟩

/-- Classes of terms modulo the equations `E`. -/
abbrev EqClass (E : List (Term sigma nu × Term sigma nu)) : Type (max u v) :=
  Quotient (eqSetoid E)

/-- The quotient term algebra: an operation acts on representatives. -/
noncomputable def quotAlg (E : List (Term sigma nu × Term sigma nu)) : Alg sigma (EqClass E) where
  interp f cs := Quotient.mk _ (.app f (cs.map Quotient.out))

theorem forall₂_map_of {α β γ : Type _} {R : β → γ → Prop} (f : α → β) (g : α → γ) :
    ∀ l : List α, (∀ a ∈ l, R (f a) (g a)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => .nil
  | a :: l, h => .cons (h a List.mem_cons_self)
      (forall₂_map_of f g l (fun b hb => h b (List.mem_cons_of_mem _ hb)))

/-- A term evaluates in the quotient algebra to the class of its instance by representatives. -/
theorem quotAlg_eval (E : List (Term sigma nu × Term sigma nu)) (α : nu → EqClass E)
    (t : Term sigma nu) :
    Alg.eval (quotAlg E) α t = Quotient.mk _ (Subst.apply (fun x => (α x).out) t) := by
  induction t using Term.rec' with
  | hvar x => simp
  | happ f args ih =>
    rw [Alg.eval_app, Subst.apply_app, Subst.applyList_eq_map]
    show Quotient.mk (eqSetoid E)
      (Term.app f ((args.map (Alg.eval (quotAlg E) α)).map Quotient.out)) = _
    apply Quotient.sound
    rw [List.map_map]
    have h := eqCongr_args E f [] (args.map (Quotient.out ∘ Alg.eval (quotAlg E) α))
      (args.map (Subst.apply (fun x => (α x).out)))
      (forall₂_map_of _ _ args (fun a ha => by
        show EqCongr E (Quotient.out (Alg.eval (quotAlg E) α a)) _
        rw [ih a ha]
        exact Quotient.mk_out (s := eqSetoid E) _))
    simp only [List.nil_append] at h
    exact h

/-- The quotient algebra is a model of every rule that is a consequence of the equations. -/
theorem quotAlg_model (E : List (Term sigma nu × Term sigma nu)) (R : TRS sigma nu)
    (hE : ∀ rule ∈ R, EqCongr E rule.lhs rule.rhs) : IsModel (quotAlg E) (inR R) := by
  rintro l r ⟨rule, hrule, rfl, rfl⟩ α
  rw [quotAlg_eval, quotAlg_eval]
  exact Quotient.sound (eqCongr_subst E _ (hE rule hrule))

/-- Self-labelling: every symbol is labelled by the class of the term it heads. -/
noncomputable def selfLab (E : List (Term sigma nu × Term sigma nu)) :
    sigma → Option (List (EqClass E) → EqClass E) :=
  fun f => some ((quotAlg E).interp f)

theorem pStep_nil_false {s t : Term sigma nu}
    (h : PStep (fun l r => (l, r) ∈ ([] : List (Term sigma nu × Term sigma nu))) s t) : False := by
  induction h with
  | root h =>
    obtain ⟨l, r, hmem, _⟩ := h
    simp at hmem
  | arg _ _ _ _ ih => exact ih

theorem eqCongr_nil {s t : Term sigma nu} (h : EqCongr [] s t) : s = t := by
  unfold EqCongr at h
  induction h with
  | rel x y hxy => exact (pStep_nil_false hxy).elim
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

end Equational

/-- The equations of the free recursor: its two rules read as equations. -/
def freeEqs : List (Term FreeSym Nat × Term FreeSym Nat) :=
  freeRecursorTRS.map (fun rule => (rule.lhs, rule.rhs))

/-- A model of the free recursor on pairs. The first component is the counter model; the second
counts the wrappers the recursors will produce: `recur(b, s, n) ↦ (b₁, b₂ + n₁)`,
`wrap(x, y) ↦ (y₁, y₂ + 1)`, `succ(x) ↦ (x₁ + 1, x₂)`, `zero ↦ (0, 0)`. -/
def vdAlg : Alg FreeSym (ℕ × ℕ) where
  interp f xs := match f with
    | .zero => (0, 0)
    | .succ => ((xs.headD (0, 0)).1 + 1, (xs.headD (0, 0)).2)
    | .wrap => ((xs.getD 1 (0, 0)).1, (xs.getD 1 (0, 0)).2 + 1)
    | .recur => ((xs.headD (0, 0)).1, (xs.headD (0, 0)).2 + (xs.getD 2 (0, 0)).1)

theorem vdAlg_model : IsModel vdAlg (fun l r => (l, r) ∈ freeEqs) := by
  intro l r h α
  simp only [freeEqs, freeRecursorTRS, List.map_cons, List.map_nil, List.mem_cons,
    Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rfl

/-- The value of a term in the pair model at the zero valuation. -/
def vd (t : Term FreeSym Nat) : ℕ × ℕ := Alg.eval vdAlg (fun _ => (0, 0)) t

theorem vd_invariant {s t : Term FreeSym Nat} (h : EqCongr freeEqs s t) : vd s = vd t := by
  unfold EqCongr at h
  induction h with
  | rel x y hxy => exact eval_eq_of_pStep vdAlg_model _ hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem vd_mk_out (t : Term FreeSym Nat) : vd (Quotient.mk (eqSetoid freeEqs) t).out = vd t :=
  vd_invariant (Quotient.mk_out (s := eqSetoid freeEqs) t)

theorem vd_quot_recur (a b d : EqClass freeEqs) :
    vd ((quotAlg freeEqs).interp .recur [a, b, d]).out =
      ((vd a.out).1, (vd a.out).2 + (vd d.out).1) := by
  show vd (Quotient.mk _ (.app .recur ([a, b, d].map Quotient.out))).out = _
  rw [vd_mk_out]
  simp [vd, vdAlg]

theorem vd_quot_succ (d : EqClass freeEqs) :
    vd ((quotAlg freeEqs).interp .succ [d]).out = ((vd d.out).1 + 1, (vd d.out).2) := by
  show vd (Quotient.mk _ (.app .succ ([d].map Quotient.out))).out = _
  rw [vd_mk_out]
  simp [vd, vdAlg]

/-- Native data of self-labelling on the free recursor: an equational theory, whose quotient algebra
supplies the labels, and a numerical reading `Φ` of the classes used by the base interpretation. -/
structure SelfLabData where
  E : List (Term FreeSym Nat × Term FreeSym Nat)
  Φ : Term FreeSym Nat → ℕ

abbrev selfLabelingEquationalData : Type := SelfLabData

/-- The base interpretation of the self-labelled signature: `recur_c(b, s, n) = k + b + k s + n`
with `k = Φ(c) + 1`, every other symbol `1 + Σ xs`. -/
noncomputable def SelfLabData.base (D : SelfLabData) : Alg (FreeSym × Option (EqClass D.E)) ℕ where
  interp g xs := match g with
    | (.recur, some c) =>
        linForm (D.Φ c.out + 1) (fun i => if i = 1 then D.Φ c.out + 1 else 1) xs
    | _ => linForm 1 (fun _ => 1) xs

theorem SelfLabData.base_mono (D : SelfLabData) (g : FreeSym × Option (EqClass D.E))
    (pre post : List ℕ) (a b : ℕ) (hab : a < b) :
    D.base.interp g (pre ++ a :: post) < D.base.interp g (pre ++ b :: post) := by
  rcases g with ⟨f, o⟩
  cases f <;> cases o <;>
    first
    | exact linForm_lt _ _ (fun _ => le_rfl) _ _ _ _ hab
    | exact linForm_lt _ _ (fun i => by split_ifs <;> omega) _ _ _ _ hab

/-- Self-labelling (Middeldorp, Ohsaki and Zantema, Transforming termination by self-labelling,
CADE-13, LNAI 1104, 1996; the construction is summarised in Hirokawa and Middeldorp, RTA 2006,
Section 2; the 1996 definition number is not pinned, its text was not accessible): every symbol is
labelled by the value of the term it heads, here in the quotient algebra of an equational theory
`E`; the quotient is a model because every rule is an `E`-consequence. -/
def selfLabelingEquationalLaws (D : selfLabelingEquationalData) : Prop :=
  ∀ rule ∈ freeRecursorTRS, EqCongr D.E rule.lhs rule.rhs

/-- The base interpretation orients every self-labelled rule instance of the free recursor. -/
def selfLabelingEquationalAccepts (D : selfLabelingEquationalData) : Prop :=
  ∀ rule ∈ freeRecursorTRS, ∀ (α : Nat → EqClass D.E) (β : Nat → ℕ),
    Alg.eval D.base β (lab (Alg.eval (quotAlg D.E) α) (selfLab D.E) rule.rhs) <
      Alg.eval D.base β (lab (Alg.eval (quotAlg D.E) α) (selfLab D.E) rule.lhs)

/-- Verdict: escape. -/
def selfLabelingEquationalResult (D : selfLabelingEquationalData) : Prop :=
  selfLabelingEquationalAccepts D ∧ FreeTerminates

theorem selfLabelingEquational_sound :
    ∀ D, selfLabelingEquationalLaws D → selfLabelingEquationalAccepts D → FreeTerminates :=
  fun D hL hA => sn_of_model_labelling freeRecursorTRS (quotAlg D.E) (selfLab D.E) D.base
    (fun x => Quotient.mk _ (.var x)) (quotAlg_model D.E _ hL) D.base_mono hA

/-- The rules of the free recursor as equations, with the wrapper count `Φ = vd₂` as reading. -/
def selfLabelingEquationalWitness : selfLabelingEquationalData := ⟨freeEqs, fun t => (vd t).2⟩

theorem selfLabelingEquationalWitness_laws :
    selfLabelingEquationalLaws selfLabelingEquationalWitness := by
  intro rule hrule
  exact Relation.EqvGen.rel _ _ (.root ⟨rule.lhs, rule.rhs, List.mem_map.2 ⟨rule, hrule, rfl⟩,
    Subst.id, (Subst.id_apply _).symm, (Subst.id_apply _).symm⟩)

theorem selfLabelingEquationalWitness_accepts :
    selfLabelingEquationalAccepts selfLabelingEquationalWitness := by
  intro rule hrule α β
  rcases mem_freeRecursorTRS.1 hrule with rfl | rfl
  · simp [selfLabelingEquationalWitness, SelfLabData.base, zeroRule, selfLab, linForm, linSum]
    omega
  · simp [selfLabelingEquationalWitness, SelfLabData.base, succRule, selfLab, linForm, linSum,
      vd_quot_recur, vd_quot_succ]
    nlinarith

theorem selfLabelingEquationalWitness_result :
    selfLabelingEquationalResult selfLabelingEquationalWitness :=
  ⟨selfLabelingEquationalWitness_accepts,
    selfLabelingEquational_sound _ selfLabelingEquationalWitness_laws
      selfLabelingEquationalWitness_accepts⟩

/-- Self labels are nontrivial (the classes of `recur(zero, zero, succ zero)` and `zero` differ);
every source step keeps the class of the term, so the labels of all enclosing symbols survive the
step; erasing labels gives the term back; source steps lift to labelled steps and labelled steps
erase to source steps. -/
theorem selfLabelingEquationalWitness_feature :
    (Quotient.mk (eqSetoid freeEqs) (fr fz fz (fs fz)) ≠ Quotient.mk (eqSetoid freeEqs) fz) ∧
      (∀ s t : Term FreeSym Nat, Step freeRecursorTRS s t →
        Quotient.mk (eqSetoid freeEqs) s = Quotient.mk (eqSetoid freeEqs) t) ∧
      (∀ (α : Nat → EqClass freeEqs) (t : Term FreeSym Nat),
        mapSym Prod.fst (lab (Alg.eval (quotAlg freeEqs) α) (selfLab freeEqs) t) = t) ∧
      (∀ (α : Nat → EqClass freeEqs) (s t : Term FreeSym Nat), Step freeRecursorTRS s t →
        LStep (quotAlg freeEqs) (selfLab freeEqs) (inR freeRecursorTRS)
          (fun _ _ : EqClass freeEqs => False)
          (lab (Alg.eval (quotAlg freeEqs) α) (selfLab freeEqs) s)
          (lab (Alg.eval (quotAlg freeEqs) α) (selfLab freeEqs) t)) ∧
      (∀ x y : Term (FreeSym × Option (EqClass freeEqs)) Nat,
        LStep (quotAlg freeEqs) (selfLab freeEqs) (inR freeRecursorTRS)
          (fun _ _ : EqClass freeEqs => False) x y →
        Step freeRecursorTRS (mapSym Prod.fst x) (mapSym Prod.fst y)) := by
  have hmodel := quotAlg_model freeEqs freeRecursorTRS selfLabelingEquationalWitness_laws
  refine ⟨fun h => ?_, fun s t h => ?_, fun α t => erase_lab _ _ t,
    fun α s t h => lab_lift_model hmodel α ((step_iff_pStep _ _ _).1 h),
    fun x y h => (step_iff_pStep _ _ _).2 (erase_lstep h)⟩
  · have h1 := vd_invariant (Quotient.exact h)
    simp [vd, vdAlg, fr, fs, fz] at h1
  · apply Quotient.sound
    show EqCongr freeEqs s t
    exact Relation.EqvGen.rel _ _ (ctxClosure_mono
      (fun a b ⟨l, r, ⟨rule, hmem, hl, hr⟩, σ, ha, hb⟩ =>
        ⟨l, r, by rw [← hl, ← hr]; exact List.mem_map.2 ⟨rule, hmem, rfl⟩, σ, ha, hb⟩)
      ((step_iff_pStep _ _ _).1 h))

/-- With the empty equational theory the quotient is syntactic equality, which is not a model of the
free recursor: the laws fail. -/
theorem selfLabelingEquational_mutation :
    ¬ selfLabelingEquationalLaws ⟨[], fun t => (vd t).2⟩ := by
  intro h
  have := eqCongr_nil (h succRule (by simp [freeRecursorTRS]))
  simp [succRule] at this

/-! ## Row: quasiDecreasingness -/

theorem acc_not_self {α : Type _} {r : α → α → Prop} {a : α} (h : Acc r a) : ¬ r a a := by
  induction h with
  | intro x _ ih => exact fun hxx => ih x hxx hxx

theorem le_sum_of_mem' {xs : List ℕ} {x : ℕ} (h : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h
      omega

section Conditional

variable {sigma : Type u} {nu : Type v}

/-- An oriented conditional rule `l → r ⇐ s₁ ≈ t₁, …, sₙ ≈ tₙ`; a condition `s ≈ t` holds for a
substitution `σ` when `σ s` reduces to `σ t`. -/
structure CRule (sigma : Type u) (nu : Type v) where
  lhs : Term sigma nu
  rhs : Term sigma nu
  conds : List (Term sigma nu × Term sigma nu)

/-- A conditional rewrite system. -/
abbrev CTRS (sigma : Type u) (nu : Type v) := List (CRule sigma nu)

/-- Rewriting at level `n` (Sternagel and Sternagel, A characterization of quasi-decreasingness,
WST 2016, Section 2): level `0` is empty; level `n + 1` contracts an instance `σ l → σ r` of a rule
in context when every condition `σ s →* σ t` holds at level `n`. -/
def CStepN (R : CTRS sigma nu) : ℕ → Term sigma nu → Term sigma nu → Prop
  | 0 => fun _ _ => False
  | n + 1 => CtxClosure (fun s t => ∃ rule ∈ R, ∃ σ : Subst sigma nu,
      s = Subst.apply σ rule.lhs ∧ t = Subst.apply σ rule.rhs ∧
        ∀ c ∈ rule.conds, Relation.ReflTransGen (CStepN R n) (Subst.apply σ c.1)
          (Subst.apply σ c.2))

/-- The rewrite relation of a conditional system: the union of its levels. -/
def CStep (R : CTRS sigma nu) (s t : Term sigma nu) : Prop := ∃ n, CStepN R n s t

/-- Quasi-decreasingness of a conditional system, witnessed by `gt` (`gt a b` reads `a ≻ b`): `≻`
is well founded, `≻ = (≻ ∪ ▷)⁺`, `→_R ⊆ ≻`, and for every rule, substitution and index `i` of a
condition, if the conditions before `i` hold then `σ l ≻ σ sᵢ` (Sternagel and Sternagel, WST 2016,
Section 2; Ohlebusch, Advanced Topics in Term Rewriting, Springer 2002, Definition 7.2.39). -/
structure QuasiDecreasingBy (R : CTRS sigma nu) (gt : Term sigma nu → Term sigma nu → Prop) :
    Prop where
  wf : WellFounded (fun b a => gt a b)
  closure : ∀ a b, gt a b ↔ Relation.TransGen (fun x y => gt x y ∨ ProperSubterm y x) a b
  step : ∀ a b, CStep R a b → gt a b
  cond : ∀ rule ∈ R, ∀ (σ : Subst sigma nu) (i : ℕ) (hi : i < rule.conds.length),
    (∀ c ∈ rule.conds.take i, Relation.ReflTransGen (CStep R) (Subst.apply σ c.1)
      (Subst.apply σ c.2)) →
      gt (Subst.apply σ rule.lhs) (Subst.apply σ (rule.conds[i]'hi).1)

/-- Quasi-decreasingness. -/
def QuasiDecreasing (R : CTRS sigma nu) : Prop := ∃ gt, QuasiDecreasingBy R gt

/-- A quasi-decreasing system terminates. -/
theorem QuasiDecreasingBy.terminating {R : CTRS sigma nu}
    {gt : Term sigma nu → Term sigma nu → Prop} (h : QuasiDecreasingBy R gt) :
    WellFounded (fun b a => CStep R a b) :=
  Subrelation.wf (fun {_ _} hab => h.step _ _ hab) h.wf

/-- One evaluation call of a conditional system: a rewrite step, a passage to a proper subterm, or
the evaluation of the next condition of a rule instance whose earlier conditions hold. -/
def CallRel (R : CTRS sigma nu) (a b : Term sigma nu) : Prop :=
  CStep R a b ∨ ProperSubterm b a ∨
    ∃ rule ∈ R, ∃ (σ : Subst sigma nu) (i : ℕ) (hi : i < rule.conds.length),
      (∀ c ∈ rule.conds.take i, Relation.ReflTransGen (CStep R) (Subst.apply σ c.1)
        (Subst.apply σ c.2)) ∧
        a = Subst.apply σ rule.lhs ∧ b = Subst.apply σ (rule.conds[i]'hi).1

theorem transGen_of_transGen_or {α : Type _} {r s : α → α → Prop}
    (hs : ∀ x y, s x y → Relation.TransGen r x y) {a b : α}
    (h : Relation.TransGen (fun x y => Relation.TransGen r x y ∨ s x y) a b) :
    Relation.TransGen r a b := by
  induction h with
  | single h =>
    rcases h with h | h
    · exact h
    · exact hs _ _ h
  | tail _ h ih =>
    rcases h with h | h
    · exact ih.trans h
    · exact ih.trans (hs _ _ h)

/-- Quasi-decreasingness is well-foundedness of the evaluation calls: every rewrite step, every
passage to a proper subterm and every evaluation of a next condition descends. -/
theorem quasiDecreasing_iff_callRel_wf (R : CTRS sigma nu) :
    QuasiDecreasing R ↔ WellFounded (fun b a => CallRel R a b) := by
  constructor
  · rintro ⟨gt, h⟩
    refine Subrelation.wf (fun {b a} hab => ?_) h.wf
    rcases hab with hs | hp | ⟨rule, hrule, σ, i, hi, hc, rfl, rfl⟩
    · exact h.step _ _ hs
    · exact (h.closure _ _).2 (.single (Or.inr hp))
    · exact h.cond rule hrule σ i hi hc
  · intro hwf
    refine ⟨fun a b => Relation.TransGen (CallRel R) a b, ⟨?_, ?_, ?_, ?_⟩⟩
    · exact Subrelation.wf (fun {_ _} h => Relation.transGen_swap.2 h) hwf.transGen
    · intro a b
      constructor
      · intro h
        exact .single (Or.inl h)
      · exact transGen_of_transGen_or (s := fun x y => ProperSubterm y x)
          (fun x y hxy => .single (Or.inr (Or.inl hxy)))
    · intro a b h
      exact .single (Or.inl h)
    · intro rule hrule σ i hi hc
      exact .single (Or.inr (Or.inr ⟨rule, hrule, σ, i, hi, hc, rfl, rfl⟩))

/-- A rewrite system read as a conditional system without conditions. -/
def ofTRS (R : TRS sigma nu) : CTRS sigma nu := R.map (fun rule => ⟨rule.lhs, rule.rhs, []⟩)

theorem cStepN_succ_ofTRS_iff (R : TRS sigma nu) (n : ℕ) (s t : Term sigma nu) :
    CStepN (ofTRS R) (n + 1) s t ↔ Step R s t := by
  show CtxClosure _ s t ↔ _
  rw [step_iff_ctxClosure]
  constructor
  · intro h
    exact ctxClosure_mono (fun s t ⟨rule, hrule, σ, hs, ht, _⟩ => by
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hrule
      exact ⟨r0, hr0, σ, hs, ht⟩) h
  · intro h
    exact ctxClosure_mono (fun s t ⟨rule, hrule, σ, hs, ht⟩ =>
      ⟨⟨rule.lhs, rule.rhs, []⟩, List.mem_map.2 ⟨rule, hrule, rfl⟩, σ, hs, ht,
        fun c hc => by simp at hc⟩) h

/-- Without conditions the conditional rewrite relation is the rewrite relation. -/
theorem cStep_ofTRS_iff (R : TRS sigma nu) (s t : Term sigma nu) :
    CStep (ofTRS R) s t ↔ Step R s t := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact False.elim hn
    | succ n => exact (cStepN_succ_ofTRS_iff R n s t).1 hn
  · intro h
    exact ⟨1, (cStepN_succ_ofTRS_iff R 0 s t).2 h⟩

/-- The unconditional specialization: for a system without conditions, quasi-decreasingness is
termination. -/
theorem quasiDecreasing_ofTRS_iff (R : TRS sigma nu) :
    QuasiDecreasing (ofTRS R) ↔ ∀ t, SN R t := by
  constructor
  · rintro ⟨gt, h⟩ t
    exact (Subrelation.wf (fun {_ _} hab => (cStep_ofTRS_iff R _ _).2 hab) h.terminating).apply t
  · intro hsn
    refine ⟨Relation.TransGen (fun x y => StepOrSub R y x), ⟨?_, ?_, ?_, ?_⟩⟩
    · refine ⟨fun a => ?_⟩
      have h1 : Acc (Relation.TransGen (StepOrSub R)) a := (acc_stepOrSub_of_sn (hsn a)).transGen
      exact Subrelation.accessible (fun {_ _} h => Relation.transGen_swap.1 h) h1
    · intro a b
      constructor
      · intro h
        exact .single (Or.inl h)
      · exact transGen_of_transGen_or (s := fun x y => ProperSubterm y x)
          (fun x y hxy => Relation.transGen_swap.2 (ProperSubterm.transGen (R := R) hxy))
    · intro a b h
      exact .single (Or.inl ((cStep_ofTRS_iff R a b).1 h))
    · intro rule hrule σ i hi _
      obtain ⟨r0, _, rfl⟩ := List.mem_map.1 hrule
      simp at hi

/-- The order of a natural-number algebra: `a ≻ b` when `b` has the smaller value at every
valuation. -/
def algGt (K : Alg sigma ℕ) (a b : Term sigma nu) : Prop :=
  ∀ β : nu → ℕ, Alg.eval K β b < Alg.eval K β a

theorem algGt_wf (K : Alg sigma ℕ) : WellFounded (fun b a : Term sigma nu => algGt K a b) :=
  Subrelation.wf (fun {_ _} h => h (fun _ => 0)) (InvImage.wf (Alg.eval K (fun _ => 0))
    Nat.lt_wfRel.wf)

theorem algGt_of_properSubterm (K : Alg sigma ℕ)
    (hsub : ∀ (f : sigma) (xs : List ℕ) (x : ℕ), x ∈ xs → x < K.interp f xs)
    {w t : Term sigma nu} (h : ProperSubterm w t) : algGt K t w := by
  have hle : ∀ {w t : Term sigma nu}, IsSubterm w t → ∀ β, Alg.eval K β w ≤ Alg.eval K β t := by
    intro w t h β
    induction h with
    | refl => exact le_rfl
    | arg f args hmem _ ih =>
      rw [Alg.eval_app]
      exact le_trans ih (hsub f _ _ (List.mem_map_of_mem hmem)).le
  intro β
  cases h with
  | arg f args hmem hs =>
    rw [Alg.eval_app]
    exact lt_of_le_of_lt (hle hs β) (hsub f _ _ (List.mem_map_of_mem hmem))

/-- With the subterm property, the algebra order satisfies `≻ = (≻ ∪ ▷)⁺`. -/
theorem algGt_closure (K : Alg sigma ℕ)
    (hsub : ∀ (f : sigma) (xs : List ℕ) (x : ℕ), x ∈ xs → x < K.interp f xs)
    (a b : Term sigma nu) :
    algGt K a b ↔ Relation.TransGen (fun x y => algGt K x y ∨ ProperSubterm y x) a b := by
  constructor
  · intro h
    exact .single (Or.inl h)
  · intro h
    induction h with
    | single h =>
      rcases h with h | h
      · exact h
      · exact algGt_of_properSubterm K hsub h
    | tail _ h ih =>
      intro β
      rcases h with h | h
      · exact lt_trans (h β) (ih β)
      · exact lt_trans (algGt_of_properSubterm K hsub h β) (ih β)

/-- A strictly monotone algebra that orients every rule, conditions ignored, contains the
conditional rewrite relation in its order. -/
theorem algGt_of_cStep (K : Alg sigma ℕ) (R : CTRS sigma nu)
    (hmono : ∀ (f : sigma) (pre post : List ℕ) (a b : ℕ), a < b →
      K.interp f (pre ++ a :: post) < K.interp f (pre ++ b :: post))
    (hrule : ∀ rule ∈ R, ∀ β : nu → ℕ, Alg.eval K β rule.rhs < Alg.eval K β rule.lhs)
    {a b : Term sigma nu} (h : CStep R a b) : algGt K a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => exact False.elim hn
  | succ n =>
    unfold CStepN at hn
    intro β
    induction hn generalizing β with
    | root h =>
      obtain ⟨rule, hrule', σ, rfl, rfl, _⟩ := h
      rw [Alg.eval_subst, Alg.eval_subst]
      exact hrule rule hrule' _
    | arg f pre post _ ih =>
      rw [Alg.eval_app, Alg.eval_app]
      simp only [List.map_append, List.map_cons]
      exact hmono f _ _ _ _ (ih β)

theorem ctxClosure_app_inv {P : Term sigma nu → Term sigma nu → Prop} {f : sigma}
    {args : List (Term sigma nu)} {u : Term sigma nu} (h : CtxClosure P (.app f args) u) :
    P (.app f args) u ∨ ∃ (pre post : List (Term sigma nu)) (a b : Term sigma nu),
      args = pre ++ a :: post ∧ CtxClosure P a b := by
  generalize hs : Term.app f args = s at h
  cases h with
  | root h => exact Or.inl (hs ▸ h)
  | arg g pre post h' =>
    simp only [Term.app.injEq] at hs
    exact Or.inr ⟨pre, post, _, _, hs.2, h'⟩

theorem isSubterm_trans {w a t : Term sigma nu} (h1 : IsSubterm w a) (h2 : IsSubterm a t) :
    IsSubterm w t := by
  induction h2 with
  | refl => exact h1
  | arg f args hmem _ ih => exact .arg f args hmem ih

theorem isSubterm_size_le {w t : Term sigma nu} (h : IsSubterm w t) : Term.size w ≤ Term.size t := by
  induction h with
  | refl => exact le_rfl
  | arg f args hmem _ ih => exact le_trans ih (Term.size_lt_of_mem hmem).le

theorem properSubterm_size_lt {w t : Term sigma nu} (h : ProperSubterm w t) :
    Term.size w < Term.size t := by
  cases h with
  | arg f args hmem hs => exact lt_of_le_of_lt (isSubterm_size_le hs) (Term.size_lt_of_mem hmem)

theorem properSubterm_trans {c b a : Term sigma nu} (h1 : ProperSubterm c b)
    (h2 : ProperSubterm b a) : ProperSubterm c a := by
  have h1' : IsSubterm c b := by
    cases h1 with
    | arg f args hmem hs => exact .arg f args hmem hs
  cases h2 with
  | arg f args hmem hs => exact .arg f args hmem (isSubterm_trans h1' hs)

end Conditional

/-- The free recursor as a conditional system without conditions. -/
def freeCTRS : CTRS FreeSym Nat := ofTRS freeRecursorTRS

/-- Native data of quasi-decreasingness on the free recursor: the order that witnesses it. -/
abbrev quasiDecreasingnessData : Type := Term FreeSym Nat → Term FreeSym Nat → Prop

/-- Ohlebusch (Advanced Topics in Term Rewriting, Springer 2002, Definition 7.2.39), as stated by
Sternagel and Sternagel (A characterization of quasi-decreasingness, WST 2016, Section 2): the
order is well founded and `≻ = (≻ ∪ ▷)⁺`. -/
def quasiDecreasingnessLaws (gt : quasiDecreasingnessData) : Prop :=
  WellFounded (fun b a => gt a b) ∧
    ∀ a b, gt a b ↔ Relation.TransGen (fun x y => gt x y ∨ ProperSubterm y x) a b

/-- The order contains the rewrite relation of the free recursor, read as a conditional system, and
dominates every condition source whose earlier conditions hold. -/
def quasiDecreasingnessAccepts (gt : quasiDecreasingnessData) : Prop :=
  (∀ a b, CStep freeCTRS a b → gt a b) ∧
    ∀ rule ∈ freeCTRS, ∀ (σ : Subst FreeSym Nat) (i : ℕ) (hi : i < rule.conds.length),
      (∀ c ∈ rule.conds.take i, Relation.ReflTransGen (CStep freeCTRS) (Subst.apply σ c.1)
        (Subst.apply σ c.2)) →
        gt (Subst.apply σ rule.lhs) (Subst.apply σ (rule.conds[i]'hi).1)

/-- Verdict: escape. -/
def quasiDecreasingnessResult (gt : quasiDecreasingnessData) : Prop :=
  quasiDecreasingnessAccepts gt ∧ FreeTerminates

theorem quasiDecreasingness_sound :
    ∀ gt, quasiDecreasingnessLaws gt → quasiDecreasingnessAccepts gt → FreeTerminates := by
  intro gt hL hA t
  have h : QuasiDecreasingBy freeCTRS gt := ⟨hL.1, hL.2, hA.1, hA.2⟩
  exact (Subrelation.wf (fun {_ _} hab => (cStep_ofTRS_iff freeRecursorTRS _ _).2 hab)
    h.terminating).apply t

/-- The subterm property of the coupled polynomial. -/
theorem cpAlg_sub (f : FreeSym) (xs : List ℕ) (x : ℕ) (h : x ∈ xs) : x < cpAlg.interp f xs := by
  have hx := le_sum_of_mem' h
  cases f with
  | recur =>
    show x < (1 + xs.sum) * (xs.getD 2 0 + 1)
    have : 1 + xs.sum ≤ (1 + xs.sum) * (xs.getD 2 0 + 1) := Nat.le_mul_of_pos_right _ (by omega)
    exact lt_of_lt_of_le (by omega) this
  | zero =>
    show x < 1 + xs.sum
    omega
  | succ =>
    show x < 1 + xs.sum
    omega
  | wrap =>
    show x < 1 + xs.sum
    omega

/-- The order of the coupled polynomial. -/
def quasiDecreasingnessWitness : quasiDecreasingnessData := algGt cpAlg

theorem quasiDecreasingnessWitness_laws : quasiDecreasingnessLaws quasiDecreasingnessWitness :=
  ⟨algGt_wf cpAlg, algGt_closure cpAlg cpAlg_sub⟩

theorem quasiDecreasingnessWitness_accepts :
    quasiDecreasingnessAccepts quasiDecreasingnessWitness := by
  refine ⟨fun a b h => algGt_of_cStep cpAlg freeCTRS cpAlg_mono ?_ h, ?_⟩
  · intro rule hrule β
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hrule
    exact cpAlg_orients r0 hr0 β
  · intro rule hrule σ i hi _
    obtain ⟨r0, _, rfl⟩ := List.mem_map.1 hrule
    simp at hi

theorem quasiDecreasingnessWitness_result :
    quasiDecreasingnessResult quasiDecreasingnessWitness :=
  ⟨quasiDecreasingnessWitness_accepts,
    quasiDecreasingness_sound _ quasiDecreasingnessWitness_laws
      quasiDecreasingnessWitness_accepts⟩

/-! ### Live conditions -/

/-- Symbols of the conditional examples. -/
inductive CSym
  | a
  | b
  | c
  | f
  | g
  | h
  deriving DecidableEq

/-- `h(a) → a`. -/
def liveH : CRule CSym Nat := ⟨.app .h [.app .a []], .app .a [], []⟩

/-- `g(x) → c ⇐ h(x) ≈ a`. -/
def liveG : CRule CSym Nat := ⟨.app .g [.var 0], .app .c [], [(.app .h [.var 0], .app .a [])]⟩

/-- A conditional system with a live condition: `g(t) → c` exactly when `h(t)` reduces to `a`. -/
def liveCTRS : CTRS CSym Nat := [liveH, liveG]

/-- Constants `h ↦ 2`, `g ↦ 3`, all other symbols `1`. -/
def liveC0 : CSym → ℕ
  | .h => 2
  | .g => 3
  | _ => 1

/-- The interpretation `f(xs) = c_f + Σ xs`. -/
def liveAlg : Alg CSym ℕ := linAlg liveC0 (fun _ _ => 1)

theorem liveAlg_interp (k : CSym) (xs : List ℕ) : liveAlg.interp k xs = liveC0 k + xs.sum := by
  show linForm _ _ xs = _
  simp [linForm, linSum_one]

theorem liveAlg_eval_app (β : Nat → ℕ) (k : CSym) (args : List (Term CSym Nat)) :
    Alg.eval liveAlg β (.app k args) = liveC0 k + (args.map (Alg.eval liveAlg β)).sum := by
  rw [Alg.eval_app, liveAlg_interp]

theorem liveAlg_sub (k : CSym) (xs : List ℕ) (x : ℕ) (h : x ∈ xs) : x < liveAlg.interp k xs := by
  rw [liveAlg_interp]
  have h1 := le_sum_of_mem' h
  have h2 : 1 ≤ liveC0 k := by cases k <;> simp [liveC0]
  omega

theorem liveAlg_mono (k : CSym) (pre post : List ℕ) (a b : ℕ) (hab : a < b) :
    liveAlg.interp k (pre ++ a :: post) < liveAlg.interp k (pre ++ b :: post) :=
  linAlg_mono liveC0 (fun _ _ => 1) (fun _ _ => le_rfl) k pre post a b hab

/-- The live system is quasi-decreasing: the order of `liveAlg` dominates the condition source
`h(x)` by the rule's left-hand side `g(x)`. -/
theorem live_quasiDecreasing : QuasiDecreasingBy liveCTRS (algGt liveAlg) := by
  refine ⟨algGt_wf liveAlg, algGt_closure liveAlg liveAlg_sub,
    fun a b h => algGt_of_cStep liveAlg liveCTRS liveAlg_mono ?_ h, ?_⟩
  · intro rule hrule β
    simp only [liveCTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
    rcases hrule with rfl | rfl
    · simp only [liveH, liveAlg_eval_app, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, liveC0]
      omega
    · simp only [liveG, liveAlg_eval_app, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Alg.eval_var, liveC0]
      omega
  · intro rule hrule σ i hi _
    simp only [liveCTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
    rcases hrule with rfl | rfl
    · simp [liveH] at hi
    · have hi0 : i = 0 := by
        simp [liveG] at hi
        omega
      subst hi0
      intro β
      show Alg.eval liveAlg β (Subst.apply σ (.app CSym.h [.var 0])) <
        Alg.eval liveAlg β (Subst.apply σ (.app CSym.g [.var 0]))
      simp only [Subst.apply_app, Subst.applyList_eq_map, List.map_cons, List.map_nil,
        Subst.apply_var, liveAlg_eval_app, List.sum_cons, List.sum_nil, liveC0]
      omega

/-- The condition fires at `g(a)`: `h(a) → a`. -/
theorem live_step_ga : CStep liveCTRS (.app .g [.app .a []]) (.app .c []) := by
  refine ⟨2, CtxClosure.root ⟨liveG, by simp [liveCTRS], fun _ => .app .a [], rfl, rfl, ?_⟩⟩
  intro c hc
  simp only [liveG, List.mem_singleton] at hc
  subst hc
  exact Relation.ReflTransGen.single (CtxClosure.root ⟨liveH, by simp [liveCTRS],
    fun _ => .app .a [], rfl, rfl, fun c hc => by simp [liveH] at hc⟩)

theorem liveCTRS_no_step_b (n : ℕ) (u : Term CSym Nat) :
    ¬ CStepN liveCTRS n (.app .b []) u := by
  intro h
  cases n with
  | zero => exact h
  | succ n =>
    unfold CStepN at h
    rcases ctxClosure_app_inv h with ⟨rule, hrule, σ, hs, _, _⟩ | ⟨pre, post, _, _, hargs, _⟩
    · simp only [liveCTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
      rcases hrule with rfl | rfl
      · simp [liveH] at hs
      · simp [liveG] at hs
    · simp at hargs

theorem liveCTRS_no_step_hb (n : ℕ) (u : Term CSym Nat) :
    ¬ CStepN liveCTRS n (.app .h [.app .b []]) u := by
  intro h
  cases n with
  | zero => exact h
  | succ n =>
    unfold CStepN at h
    rcases ctxClosure_app_inv h with ⟨rule, hrule, σ, hs, _, _⟩ | ⟨pre, post, a, b, hargs, hab⟩
    · simp only [liveCTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
      rcases hrule with rfl | rfl
      · simp [liveH] at hs
      · simp [liveG] at hs
    · have ha : a = .app .b [] := by
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hargs
          exact hargs.1.symm
        | cons p pre' => simp at hargs
      subst ha
      exact liveCTRS_no_step_b (n + 1) b hab

/-- The condition blocks at `g(b)`: `h(b)` is a normal form other than `a`. -/
theorem live_no_step_gb : ¬ CStep liveCTRS (.app .g [.app .b []]) (.app .c []) := by
  rintro ⟨n, h⟩
  cases n with
  | zero => exact h
  | succ n =>
    unfold CStepN at h
    rcases ctxClosure_app_inv h with ⟨rule, hrule, σ, hs, _, hc⟩ | ⟨pre, post, a, b, hargs, hab⟩
    · simp only [liveCTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
      rcases hrule with rfl | rfl
      · simp [liveH] at hs
      · have hσ : σ 0 = .app .b [] := by
          simp only [liveG, Subst.apply_app, Subst.applyList_eq_map, List.map_cons, List.map_nil,
            Subst.apply_var, Term.app.injEq, List.cons.injEq, true_and, and_true] at hs
          exact hs.symm
        have hc0 := hc _ List.mem_cons_self
        simp only [Subst.apply_app, Subst.applyList_eq_map, List.map_cons, List.map_nil,
          Subst.apply_var, hσ] at hc0
        rcases hc0.cases_head with heq | ⟨w, hw, _⟩
        · simp at heq
        · exact liveCTRS_no_step_hb n w hw
    · have ha : a = .app .b [] := by
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hargs
          exact hargs.1.symm
        | cons p pre' => simp at hargs
      subst ha
      exact liveCTRS_no_step_b (n + 1) b hab

/-- `f(x) → x ⇐ f(x) ≈ c`: the condition evaluates the left-hand side itself. -/
def loopRule : CRule CSym Nat := ⟨.app .f [.var 0], .var 0, [(.app .f [.var 0], .app .c [])]⟩

def loopCTRS : CTRS CSym Nat := [loopRule]

theorem loopCTRS_no_step : ∀ n (s t : Term CSym Nat), ¬ CStepN loopCTRS n s t := by
  intro n
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih =>
    intro s t h
    unfold CStepN at h
    induction h with
    | root h =>
      obtain ⟨rule, hrule, σ, rfl, _, hc⟩ := h
      simp only [loopCTRS, List.mem_singleton] at hrule
      subst hrule
      have hc0 := hc _ List.mem_cons_self
      rcases hc0.cases_head with heq | ⟨w, hw, _⟩
      · simp at heq
      · exact ih _ _ hw
    | arg _ _ _ _ ih' => exact ih'

/-- The looping condition gives an empty, hence terminating, rewrite relation. -/
theorem loopCTRS_terminating : WellFounded (fun b a => CStep loopCTRS a b) :=
  ⟨fun a => Acc.intro a fun _ ⟨n, h⟩ => absurd h (loopCTRS_no_step n _ _)⟩

/-- The looping system is not quasi-decreasing: its left-hand side would have to be above itself. -/
theorem loopCTRS_not_quasiDecreasing : ¬ QuasiDecreasing loopCTRS := by
  rintro ⟨gt, h⟩
  have hgt : gt (.app CSym.f [.var 0]) (.app CSym.f [.var 0]) := by
    simpa [loopRule] using h.cond loopRule (by simp [loopCTRS]) Subst.id 0 (by simp [loopRule])
      (by simp)
  exact acc_not_self (h.wf.apply _) hgt

/-- Live conditions versus the unconditional specialization: without conditions quasi-decreasingness
is termination; with a live condition the order must dominate the condition source, the condition
fires at `g(a)` and blocks at `g(b)`; a self-referential condition gives a terminating system that
is not quasi-decreasing; and quasi-decreasingness is well-foundedness of the evaluation calls. -/
theorem quasiDecreasingnessWitness_feature :
    (∀ R : TRS FreeSym Nat, QuasiDecreasing (ofTRS R) ↔ ∀ t, SN R t) ∧
      QuasiDecreasingBy liveCTRS (algGt liveAlg) ∧
      CStep liveCTRS (.app .g [.app .a []]) (.app .c []) ∧
      ¬ CStep liveCTRS (.app .g [.app .b []]) (.app .c []) ∧
      WellFounded (fun b a => CStep loopCTRS a b) ∧ ¬ QuasiDecreasing loopCTRS ∧
      (∀ R : CTRS FreeSym Nat, QuasiDecreasing R ↔ WellFounded (fun b a => CallRel R a b)) :=
  ⟨quasiDecreasing_ofTRS_iff, live_quasiDecreasing, live_step_ga, live_no_step_gb,
    loopCTRS_terminating, loopCTRS_not_quasiDecreasing, quasiDecreasing_iff_callRel_wf⟩

/-- The strict subterm order: `a ≻ b` when `b` is a proper subterm of `a`. -/
def subtermGt (a b : Term FreeSym Nat) : Prop := ProperSubterm b a

/-- Replacing the witness order by the strict subterm order keeps the laws and loses acceptance: the
successor step builds a larger term. -/
theorem quasiDecreasingness_mutation :
    quasiDecreasingnessLaws subtermGt ∧ ¬ quasiDecreasingnessAccepts subtermGt := by
  refine ⟨⟨Subrelation.wf (fun {_ _} h => properSubterm_size_lt h)
      (InvImage.wf Term.size Nat.lt_wfRel.wf), fun a b => ⟨fun h => .single (Or.inl h), fun h => ?_⟩⟩,
    fun h => ?_⟩
  · induction h with
    | single h =>
      rcases h with h | h
      · exact h
      · exact h
    | tail _ h ih =>
      rcases h with h | h
      · exact properSubterm_trans h ih
      · exact properSubterm_trans h ih
  · have hstep := h.1 _ _ ((cStep_ofTRS_iff freeRecursorTRS _ _).2 (step_succ fz fz fz))
    have := properSubterm_size_lt hstep
    simp [fw, fr, fs, fz] at this

/-! ## Raised-term rows over the free schema -/

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.ProcessorSemantics
open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate
open OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity

/-- Terms over the raised (labelled) signature: every constructor occurrence carries its match
height. -/
inductive RaisedTerm (ν : Type) where
  | var (x : ν)
  | zero (h : ℕ)
  | succ (h : ℕ) (t : RaisedTerm ν)
  | wrap (h : ℕ) (s t : RaisedTerm ν)
  | recur (h : ℕ) (b s n : RaisedTerm ν)
  deriving DecidableEq

namespace RaisedTerm

variable {ν : Type}

/-- Erase the match heights. -/
def erase : RaisedTerm ν → FreeTerm ν
  | .var x => .var x
  | .zero _ => .zero
  | .succ _ t => .succ (erase t)
  | .wrap _ s t => .wrap (erase s) (erase t)
  | .recur _ b s n => .recur (erase b) (erase s) (erase n)

/-- Size of a raised term. -/
def size : RaisedTerm ν → ℕ
  | .var _ => 1
  | .zero _ => 1
  | .succ _ t => size t + 1
  | .wrap _ s t => size s + size t + 1
  | .recur _ b s n => size b + size s + size n + 1

end RaisedTerm

/-- Raise a free term, labelling every constructor occurrence with the weight of the subterm it
heads. -/
def raiseQW : FreeTerm Nat → RaisedTerm Nat
  | .var x => .var x
  | .zero => .zero 1
  | .succ t => .succ (qw (.succ t)) (raiseQW t)
  | .wrap s t => .wrap (qw (.wrap s t)) (raiseQW s) (raiseQW t)
  | .recur b s n => .recur (qw (.recur b s n)) (raiseQW b) (raiseQW s) (raiseQW n)

@[simp] theorem erase_raiseQW (t : FreeTerm Nat) : (raiseQW t).erase = t := by
  induction t with
  | var x => rfl
  | zero => rfl
  | succ t ih => simp [raiseQW, RaisedTerm.erase, ih]
  | wrap s t ihs iht => simp [raiseQW, RaisedTerm.erase, ihs, iht]
  | recur b s n ihb ihs ihn => simp [raiseQW, RaisedTerm.erase, ihb, ihs, ihn]

@[simp] theorem size_raiseQW (t : FreeTerm Nat) : (raiseQW t).size = termSize t := by
  induction t with
  | var x => rfl
  | zero => rfl
  | succ t ih => simp [raiseQW, RaisedTerm.size, termSize, ih]
  | wrap s t ihs iht => simp [raiseQW, RaisedTerm.size, termSize, ihs, iht]
  | recur b s n ihb ihs ihn => simp [raiseQW, RaisedTerm.size, termSize, ihb, ihs, ihn]

/-- Counted derivations lift through a raising map when every source step raises. -/
theorem relPow_raise {base : FreeTerm Nat → RaisedTerm Nat}
    {r : RaisedTerm Nat → RaisedTerm Nat → Prop}
    (hstep : ∀ {s t : FreeTerm Nat}, ContextStep s t → r (base s) (base t)) :
    ∀ {n : Nat} {s t : FreeTerm Nat},
      RelPow ContextStep n s t → RelPow r n (base s) (base t) := by
  intro n s t h
  induction h with
  | zero a => exact RelPow.zero _
  | succ hp hst ih => exact RelPow.succ ih (hstep hst)

/-- Counted derivations of a height-decreasing raised system are bounded by the initial height. -/
theorem relPow_le_height {r : RaisedTerm Nat → RaisedTerm Nat → Prop} {h : RaisedTerm Nat → Nat}
    (hdec : ∀ {a b}, r a b → h b + 1 ≤ h a) :
    ∀ {n : Nat} {a b : RaisedTerm Nat}, RelPow r n a b → n + h b ≤ h a := by
  intro n a b hp
  induction hp with
  | zero a => simp
  | succ hp hst ih =>
      have hd := hdec hst
      omega

/-- Termination statement of the free schema's contextual relation. -/
abbrev FreeSchemaTerminates : Prop := WellFounded (fun u t : FreeTerm Nat => ContextStep t u)

/-- The free schema's contextual relation is well founded; the weight `qw` is a decreasing
measure. -/
theorem freeSchemaTerminates : FreeSchemaTerminates :=
  Subrelation.wf (fun {_ _} h => qw_contextStep h) (InvImage.wf qw Nat.lt_wfRel.wf)

/-- A raised height that strictly drops on every contextual step proves termination of the free
schema, by the counted-derivation bound. -/
theorem freeSchemaTerminates_of_raisedHeight {height : RaisedTerm Nat → Nat}
    {raiseT : FreeTerm Nat → RaisedTerm Nat}
    (hstep : ∀ {s t : FreeTerm Nat}, ContextStep s t →
      height (raiseT t) + 1 ≤ height (raiseT s)) :
    FreeSchemaTerminates := by
  have key : ∀ n (t : FreeTerm Nat), height (raiseT t) ≤ n →
      Acc (fun u t => ContextStep t u) t := by
    intro n
    induction n with
    | zero =>
        intro t ht
        refine Acc.intro t fun u htu => ?_
        have := hstep htu
        omega
    | succ n ih =>
        intro t ht
        refine Acc.intro t fun u htu => ?_
        exact ih u (by have := hstep htu; omega)
  exact ⟨fun t => key _ t le_rfl⟩

theorem one_le_two_pow (n : Nat) : 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      nlinarith

theorem self_lt_two_pow (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have h1 : 1 ≤ 2 ^ n := one_le_two_pow n
      nlinarith

/-- For every linear constant there is a nesting depth whose linear bound is below `2 ^ d`. -/
theorem exists_linear_lt_pow : ∀ C : Nat, ∃ d, C * (5 * d + 4) < 2 ^ d := by
  intro C
  induction C with
  | zero => exact ⟨1, by norm_num⟩
  | succ C ih =>
      obtain ⟨d, hd⟩ := ih
      refine ⟨2 * d + 12, ?_⟩
      have hpow : 2 ^ (2 * d + 12) = 4096 * (2 ^ d) ^ 2 := by
        have h2 : 2 ^ (2 * d) = (2 ^ d) ^ 2 := by
          rw [show 2 * d = d * 2 by ring, ← pow_mul]
        rw [pow_add, h2]
        ring
      rw [hpow]
      nlinarith [hd, one_le_two_pow d, self_lt_two_pow d]

/-- The single-exponential lower family excludes every raised certificate with a linear height
bound: a source-sound raised system whose steps consume one height unit cannot close a linear
bound for the free two-rule system (Geser, Hofbauer and Waldmann 2004, Proposition 2,
contrapositive). -/
theorem no_linear_raised_certificate {bound : Nat} {raiseT : FreeTerm Nat → RaisedTerm Nat}
    {raised : RaisedTerm Nat → RaisedTerm Nat → Prop} {height : RaisedTerm Nat → Nat}
    (hsound : ∀ {s t : FreeTerm Nat}, ContextStep s t → raised (raiseT s) (raiseT t))
    (hdec : ∀ {a b : RaisedTerm Nat}, raised a b → height b + 1 ≤ height a)
    (hbound : ∀ t : FreeTerm Nat, height (raiseT t) ≤ bound * termSize t) : False := by
  obtain ⟨d, hd⟩ := exists_linear_lt_pow bound
  obtain ⟨m, u, hm, hder⟩ := nest_long_derivation 2 d
  have hlift : RelPow raised m (raiseT (nest 2 d)) (raiseT u) :=
    relPow_raise (base := raiseT) (r := raised) (fun h => hsound h) hder
  have hlen := relPow_le_height (r := raised) (h := height) (fun h => hdec h) hlift
  have hb := hbound (nest 2 d)
  have hsize : termSize (nest 2 d) = 5 * d + 4 := by
    rw [termSize_nest]
    ring
  rw [hsize] at hb
  omega

/-! ### Row: matchBounds -/

/-- Native data of the match-bound row: the source system, the linear constant, the raising map
into the labelled signature, the raised system over labelled symbols, and the raised height. -/
structure matchBoundsData where
  sys : FreeTerm Nat → FreeTerm Nat → Prop
  bound : Nat
  raiseT : FreeTerm Nat → RaisedTerm Nat
  raised : RaisedTerm Nat → RaisedTerm Nat → Prop
  height : RaisedTerm Nat → Nat

/-- Admissibility of the raised match-bound certificate (Geser, Hofbauer and Waldmann,
`Match-bounded string rewriting systems`, AAECC 15(3-4), 2004, Definition 1 (match-bounded) and
Proposition 2 (linear derivational complexity); the free-schema term instance): source soundness
(every source transition raises) and transition decrease (every raised transition consumes one
height unit). -/
def matchBoundsLaws (M : matchBoundsData) : Prop :=
  (∀ {s t : FreeTerm Nat}, M.sys s t → M.raised (M.raiseT s) (M.raiseT t)) ∧
    (∀ {a b : RaisedTerm Nat}, M.raised a b → M.height b + 1 ≤ M.height a)

/-- The method accepts the free two-rule system when the certificate covers it through the adapter
`sys ↔ ContextStep` and closes the linear height bound at `bound`. -/
def matchBoundsAccepts (M : matchBoundsData) : Prop :=
  (∀ s t : FreeTerm Nat, M.sys s t ↔ ContextStep s t) ∧
    (∀ t : FreeTerm Nat, M.height (M.raiseT t) ≤ M.bound * termSize t)

/-- The free two-rule system is not match-bounded: no raised certificate covers it with a linear
height bound, because its contextual derivational complexity is single-exponential and every
match-bounded system has linear derivational complexity (Geser, Hofbauer and Waldmann 2004,
Proposition 2, contrapositive).
Verdict: barrier. -/
def matchBoundsResult (M : matchBoundsData) : Prop :=
  ¬ matchBoundsAccepts M

theorem matchBounds_universal : ∀ M : matchBoundsData,
    matchBoundsLaws M → matchBoundsResult M := by
  intro M hL hA
  obtain ⟨hcov, hbound⟩ := hA
  exact no_linear_raised_certificate
    (fun {s t} h => hL.1 ((hcov s t).mpr h)) (fun h => hL.2 h) hbound

/-- The witness raises every constructor occurrence to the weight of the subterm it heads and
lifts the free contextual steps; the raised height is the weight of the erasure. -/
def matchBoundsWitness : matchBoundsData where
  sys := ContextStep
  bound := 0
  raiseT := raiseQW
  raised := fun a b => ∃ s t : FreeTerm Nat, ContextStep s t ∧ a = raiseQW s ∧ b = raiseQW t
  height := fun a => qw a.erase

theorem matchBoundsWitness_laws : matchBoundsLaws matchBoundsWitness := by
  refine ⟨?_, ?_⟩
  · intro s t h
    exact ⟨s, t, h, rfl, rfl⟩
  · rintro a b ⟨s, t, hst, rfl, rfl⟩
    have hq := qw_contextStep hst
    show qw (raiseQW t).erase + 1 ≤ qw (raiseQW s).erase
    rw [erase_raiseQW, erase_raiseQW]
    omega

theorem matchBoundsWitness_result : matchBoundsResult matchBoundsWitness :=
  matchBounds_universal _ matchBoundsWitness_laws

/-- The countdown control: the successor chain `succ t → t` carries a nontrivial raised
certificate that closes the height bound with constant one. -/
def matchBoundsCountdown : matchBoundsData where
  sys := fun s t => s = .succ t
  bound := 1
  raiseT := raiseQW
  raised := fun a b => ∃ s t : FreeTerm Nat, s = .succ t ∧ a = raiseQW s ∧ b = raiseQW t
  height := fun a => a.size

theorem matchBoundsCountdown_laws : matchBoundsLaws matchBoundsCountdown := by
  refine ⟨?_, ?_⟩
  · intro s t hst
    exact ⟨s, t, hst, rfl, rfl⟩
  · rintro a b ⟨s, t, hst, rfl, rfl⟩
    subst hst
    show (raiseQW t).size + 1 ≤ (raiseQW (FreeTerm.succ t)).size
    rw [size_raiseQW, size_raiseQW]
    show termSize t + 1 ≤ termSize (FreeTerm.succ t)
    rw [show termSize (FreeTerm.succ t) = termSize t + 1 from rfl]

theorem matchBoundsCountdown_bound : ∀ t : FreeTerm Nat,
    matchBoundsCountdown.height (matchBoundsCountdown.raiseT t) ≤
      matchBoundsCountdown.bound * termSize t := by
  intro t
  show (raiseQW t).size ≤ 1 * termSize t
  rw [size_raiseQW]
  omega

/-- The defining features of the row: the raise computes nontrivial match heights, the duplicating
rule has an actual lifted step whose height strictly drops, and the countdown system carries a
nontrivial accepted certificate closing the same conditions; acceptance therefore rests on a
native raised certificate, not on a renamed generic linear rank. -/
theorem matchBoundsWitness_feature :
    matchBoundsWitness.raiseT (FreeTerm.recur .zero .zero (.succ .zero)) =
        RaisedTerm.recur 10 (.zero 1) (.zero 1) (.succ 2 (.zero 1)) ∧
      matchBoundsWitness.raised
        (matchBoundsWitness.raiseT (FreeTerm.recur .zero .zero (.succ .zero)))
        (matchBoundsWitness.raiseT (FreeTerm.wrap .zero (FreeTerm.recur .zero .zero .zero))) ∧
      matchBoundsWitness.height
          (matchBoundsWitness.raiseT (FreeTerm.wrap .zero (FreeTerm.recur .zero .zero .zero))) + 1 ≤
        matchBoundsWitness.height
          (matchBoundsWitness.raiseT (FreeTerm.recur .zero .zero (.succ .zero))) ∧
      matchBoundsLaws matchBoundsCountdown ∧
      (∀ t : FreeTerm Nat,
        matchBoundsCountdown.height (matchBoundsCountdown.raiseT t) ≤
          matchBoundsCountdown.bound * termSize t) ∧
      matchBoundsCountdown.raised (matchBoundsCountdown.raiseT (.succ .zero))
        (matchBoundsCountdown.raiseT .zero) := by
  refine ⟨by decide, ⟨_, _, rootStep_contextStep (.recurSucc .zero .zero .zero), rfl, rfl⟩,
    by decide, matchBoundsCountdown_laws, matchBoundsCountdown_bound, ⟨_, _, rfl, rfl, rfl⟩⟩

/-- Changing the raised height to the renamed generic linear rank (the constant zero) leaves a
raised step whose transition law fails. -/
theorem matchBounds_mutation :
    ¬ matchBoundsLaws { matchBoundsWitness with height := fun _ => 0 } := by
  intro hL
  have hstep := hL.1 (rootStep_contextStep (.recurSucc .zero .zero .zero))
  have hdec : (0 : Nat) + 1 ≤ 0 := hL.2 hstep
  omega

/-! ### Row: raiseConsistencyMatchBounds -/

/-- Native data of the raise-consistency row: the source system, the linear constant, the raising
map into the labelled signature, the raised system over labelled symbols, and the raised
height. -/
structure raiseConsistencyMatchBoundsData where
  sys : FreeTerm Nat → FreeTerm Nat → Prop
  bound : Nat
  raiseT : FreeTerm Nat → RaisedTerm Nat
  raised : RaisedTerm Nat → RaisedTerm Nat → Prop
  height : RaisedTerm Nat → Nat

/-- Admissibility of the raised certificate with actual raise consistency (Geser, Hofbauer and
Waldmann, `Match-bounded string rewriting systems`, AAECC 15(3-4), 2004, Definition 1; the
raise-consistency conditions the native soundness proof consumes): source soundness, no raised
transition raises the height by more than one unit, and every source transition consumes one
height unit of the raise. -/
def raiseConsistencyMatchBoundsLaws (M : raiseConsistencyMatchBoundsData) : Prop :=
  (∀ {s t : FreeTerm Nat}, M.sys s t → M.raised (M.raiseT s) (M.raiseT t)) ∧
    (∀ {a b : RaisedTerm Nat}, M.raised a b → M.height b ≤ M.height a + 1) ∧
    (∀ {s t : FreeTerm Nat}, M.sys s t → M.height (M.raiseT t) + 1 ≤ M.height (M.raiseT s))

/-- The method accepts the free two-rule system through the adapter `sys ↔ ContextStep`. -/
def raiseConsistencyMatchBoundsAccepts (M : raiseConsistencyMatchBoundsData) : Prop :=
  ∀ s t : FreeTerm Nat, M.sys s t ↔ ContextStep s t

/-- Raise consistency gives the native soundness proof: the raised height of every source term
strictly drops on every step, so the free two-rule system terminates.
Verdict: escape. -/
def raiseConsistencyMatchBoundsResult (M : raiseConsistencyMatchBoundsData) : Prop :=
  raiseConsistencyMatchBoundsAccepts M ∧ FreeSchemaTerminates

/-- Raise consistency as a consequence of strict consumption: the derived form the native
soundness proof uses. -/
theorem raiseConsistencyMatchBounds_consistency (M : raiseConsistencyMatchBoundsData)
    (hL : raiseConsistencyMatchBoundsLaws M) {s t : FreeTerm Nat} (h : M.sys s t) :
    M.height (M.raiseT t) ≤ M.height (M.raiseT s) := by
  have := hL.2.2 h
  omega

theorem raiseConsistencyMatchBounds_sound : ∀ M : raiseConsistencyMatchBoundsData,
    raiseConsistencyMatchBoundsLaws M → raiseConsistencyMatchBoundsAccepts M →
      FreeSchemaTerminates := by
  intro M hL hA
  exact freeSchemaTerminates_of_raisedHeight
    (fun {s t} h => hL.2.2 ((hA s t).mpr h))

/-- The witness raises every constructor occurrence to the weight of the subterm it heads and
lifts the free contextual steps; the raised height is the weight of the erasure. -/
def raiseConsistencyMatchBoundsWitness : raiseConsistencyMatchBoundsData where
  sys := ContextStep
  bound := 0
  raiseT := raiseQW
  raised := fun a b => ∃ s t : FreeTerm Nat, ContextStep s t ∧ a = raiseQW s ∧ b = raiseQW t
  height := fun a => qw a.erase

theorem raiseConsistencyMatchBoundsWitness_laws :
    raiseConsistencyMatchBoundsLaws raiseConsistencyMatchBoundsWitness := by
  refine ⟨?_, ?_, ?_⟩
  · intro s t h
    exact ⟨s, t, h, rfl, rfl⟩
  · rintro a b ⟨s, t, hst, rfl, rfl⟩
    have hq := qw_contextStep hst
    show qw (raiseQW t).erase ≤ qw (raiseQW s).erase + 1
    rw [erase_raiseQW, erase_raiseQW]
    omega
  · intro s t h
    have hq := qw_contextStep h
    show qw (raiseQW t).erase + 1 ≤ qw (raiseQW s).erase
    rw [erase_raiseQW, erase_raiseQW]
    omega

theorem raiseConsistencyMatchBoundsWitness_result :
    raiseConsistencyMatchBoundsResult raiseConsistencyMatchBoundsWitness :=
  ⟨fun _ _ => Iff.rfl,
    raiseConsistencyMatchBounds_sound _ raiseConsistencyMatchBoundsWitness_laws
      (fun _ _ => Iff.rfl)⟩

/-- The defining features of the row: the raise computes nontrivial match heights, and the derived
raise-consistency statement holds on the actual lifted step of the duplicating rule together with
strict consumption. -/
theorem raiseConsistencyMatchBoundsWitness_feature :
    raiseConsistencyMatchBoundsWitness.raiseT (FreeTerm.recur .zero .zero (.succ .zero)) =
        RaisedTerm.recur 10 (.zero 1) (.zero 1) (.succ 2 (.zero 1)) ∧
      (raiseConsistencyMatchBoundsWitness.height
          (raiseConsistencyMatchBoundsWitness.raiseT
            (FreeTerm.wrap .zero (FreeTerm.recur .zero .zero .zero))) ≤
        raiseConsistencyMatchBoundsWitness.height
          (raiseConsistencyMatchBoundsWitness.raiseT
            (FreeTerm.recur .zero .zero (.succ .zero)))) ∧
      (raiseConsistencyMatchBoundsWitness.height
          (raiseConsistencyMatchBoundsWitness.raiseT
            (FreeTerm.wrap .zero (FreeTerm.recur .zero .zero .zero))) + 1 ≤
        raiseConsistencyMatchBoundsWitness.height
          (raiseConsistencyMatchBoundsWitness.raiseT
            (FreeTerm.recur .zero .zero (.succ .zero)))) := by
  refine ⟨by decide,
    raiseConsistencyMatchBounds_consistency _ raiseConsistencyMatchBoundsWitness_laws
      (rootStep_contextStep (.recurSucc .zero .zero .zero)),
    by decide⟩

/-- Changing the raised system by adding a jump transition on a concrete pair, everything else
fixed, breaks raise consistency at that raised step. -/
theorem raiseConsistencyMatchBounds_mutation :
    ¬ raiseConsistencyMatchBoundsLaws
      { raiseConsistencyMatchBoundsWitness with
        raised := fun a b =>
          (∃ s t : FreeTerm Nat, ContextStep s t ∧ a = raiseQW s ∧ b = raiseQW t) ∨
            (a = raiseQW .zero ∧ b = raiseQW (.recur .zero .zero .zero)) } := by
  intro hL
  have hcons := hL.2.1 (Or.inr ⟨rfl, rfl⟩)
  have hcons' : qw (raiseQW (FreeTerm.recur .zero .zero .zero)).erase ≤
      qw (raiseQW .zero).erase + 1 := hcons
  rw [erase_raiseQW, erase_raiseQW] at hcons'
  simp only [qw] at hcons'
  omega

/-! ### Row: leftLinearMatchBounds -/

/-- The left-hand side of the zero rule of the free schema. -/
def schemaLhsZero : FreeTerm Nat := .recur (.var 0) (.var 1) .zero

/-- The left-hand side of the duplicating rule of the free schema. -/
def schemaLhsSucc : FreeTerm Nat := .recur (.var 0) (.var 1) (.succ (.var 2))

/-- The right-hand side of the duplicating rule of the free schema. -/
def schemaRhsSucc : FreeTerm Nat := .wrap (.var 1) (.recur (.var 0) (.var 1) (.var 2))

/-- The tags of the raised constructors. -/
inductive SymTag where
  | zero
  | succ
  | wrap
  | recur

/-- A bottom-up deterministic tree automaton over the raised signature: a finite state type, a
state for variables, and one transition per constructor tag. -/
structure MatchAutomaton where
  Q : Type
  fintype : Fintype Q
  varState : Q
  trans : SymTag → Nat → List Q → Q

namespace MatchAutomaton

/-- Bottom-up run of the automaton on a raised term. -/
def run (A : MatchAutomaton) : RaisedTerm Nat → A.Q
  | .var _ => A.varState
  | .zero l => A.trans .zero l []
  | .succ l t => A.trans .succ l [run A t]
  | .wrap l s t => A.trans .wrap l [run A s, run A t]
  | .recur l b s n => A.trans .recur l [run A b, run A s, run A n]

end MatchAutomaton

/-- The concrete match-height automaton: two states, the root-label test `label ≠ 0` on a `recur`
occurrence and the accepting state otherwise. -/
def matchHeightAutomaton : MatchAutomaton where
  Q := Fin 2
  fintype := inferInstance
  varState := 0
  trans := fun tag l _ =>
    match tag with
    | .recur => if l = 0 then 0 else 1
    | .zero => 0
    | .succ => 0
    | .wrap => 0

/-- Native data of the left-linear row: the matched left-hand side, the source system, the linear
constant, the raising map, the raised system, the raised height and the actual automaton. -/
structure leftLinearMatchBoundsData where
  lhs : FreeTerm Nat
  sys : FreeTerm Nat → FreeTerm Nat → Prop
  bound : Nat
  raiseT : FreeTerm Nat → RaisedTerm Nat
  raised : RaisedTerm Nat → RaisedTerm Nat → Prop
  height : RaisedTerm Nat → Nat
  automaton : MatchAutomaton

/-- Admissibility at the actual source scope of the left-linear tree-automaton method (Geser,
Hofbauer and Waldmann, `Match-bounded string rewriting systems`, AAECC 15(3-4), 2004, Definition 1
(match-bounded), at the left-linear scope of Geser, Hofbauer, Waldmann and Zantema, `On Tree
Automata that Certify Termination of Left-Linear Term Rewriting Systems`, RTA 2005, LNCS 3467;
journal version Information and Computation 205(4), 2007): the matched left-hand side is
left-linear (no variable repeats on it), every source transition raises, and every raised
transition consumes one height unit. -/
def leftLinearMatchBoundsLaws (M : leftLinearMatchBoundsData) : Prop :=
  (freeVars M.lhs).Nodup ∧
    (∀ {s t : FreeTerm Nat}, M.sys s t → M.raised (M.raiseT s) (M.raiseT t)) ∧
    (∀ {a b : RaisedTerm Nat}, M.raised a b → M.height b + 1 ≤ M.height a)

/-- The method accepts the free two-rule system through the adapter `sys ↔ ContextStep` when the
linear height bound closes at `bound`. -/
def leftLinearMatchBoundsAccepts (M : leftLinearMatchBoundsData) : Prop :=
  (∀ s t : FreeTerm Nat, M.sys s t ↔ ContextStep s t) ∧
    (∀ t : FreeTerm Nat, M.height (M.raiseT t) ≤ M.bound * termSize t)

/-- The duplicating rule is left-linear, so the method applies syntactically, and it then fails by
the same complexity transport: the free schema's contextual complexity is single-exponential and
excludes every linear raised certificate.
Verdict: barrier. -/
def leftLinearMatchBoundsResult (M : leftLinearMatchBoundsData) : Prop :=
  ¬ leftLinearMatchBoundsAccepts M

theorem leftLinearMatchBounds_universal : ∀ M : leftLinearMatchBoundsData,
    leftLinearMatchBoundsLaws M → leftLinearMatchBoundsResult M := by
  intro M hL hA
  obtain ⟨hcov, hbound⟩ := hA
  exact no_linear_raised_certificate
    (fun {s t} h => hL.2.1 ((hcov s t).mpr h)) (fun h => hL.2.2 h) hbound

/-- The witness matches the duplicating left-hand side, raises every constructor occurrence to the
weight of the subterm it heads, lifts the free contextual steps, and carries the concrete
automaton. -/
def leftLinearMatchBoundsWitness : leftLinearMatchBoundsData where
  lhs := schemaLhsSucc
  sys := ContextStep
  bound := 0
  raiseT := raiseQW
  raised := fun a b => ∃ s t : FreeTerm Nat, ContextStep s t ∧ a = raiseQW s ∧ b = raiseQW t
  height := fun a => qw a.erase
  automaton := matchHeightAutomaton

theorem leftLinearMatchBoundsWitness_laws :
    leftLinearMatchBoundsLaws leftLinearMatchBoundsWitness := by
  refine ⟨by decide, ?_, ?_⟩
  · intro s t h
    exact ⟨s, t, h, rfl, rfl⟩
  · rintro a b ⟨s, t, hst, rfl, rfl⟩
    have hq := qw_contextStep hst
    show qw (raiseQW t).erase + 1 ≤ qw (raiseQW s).erase
    rw [erase_raiseQW, erase_raiseQW]
    omega

theorem leftLinearMatchBoundsWitness_result :
    leftLinearMatchBoundsResult leftLinearMatchBoundsWitness :=
  leftLinearMatchBounds_universal _ leftLinearMatchBoundsWitness_laws

/-- The defining features of the row: the duplicating left-hand side is left-linear while its
right-hand side duplicates the payload variable, a nonlinear left-hand side lies outside the
scope, and the actual automaton has two distinct states on raised terms. -/
theorem leftLinearMatchBoundsWitness_feature :
    (freeVars schemaLhsSucc).Nodup ∧
      ¬ (freeVars schemaRhsSucc).Nodup ∧
      ¬ (freeVars (FreeTerm.wrap (.var 0) (.var 0))).Nodup ∧
      ((matchHeightAutomaton.run (raiseQW (FreeTerm.recur .zero .zero .zero)) : Fin 2) =
        ⟨1, by decide⟩) ∧
      ((matchHeightAutomaton.run (raiseQW .zero) : Fin 2) = ⟨0, by decide⟩) := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · rfl
  · rfl

/-- Changing the matched left-hand side to a nonlinear pattern, everything else fixed, breaks the
left-linearity scope law. -/
theorem leftLinearMatchBounds_mutation :
    ¬ leftLinearMatchBoundsLaws
      { leftLinearMatchBoundsWitness with lhs := FreeTerm.wrap (.var 0) (.var 0) } := by
  intro hL
  exact absurd hL.1 (by decide)

/-! ### Row: predictiveLabeling -/

/-- Native predictive data: the predicted Boolean value of terms, the source system, the labelled
system, and the labelled height. -/
structure predictiveLabelingData where
  predict : FreeTerm Nat → Bool
  sys : FreeTerm Nat → FreeTerm Nat → Prop
  labelled : RaisedTerm Nat → RaisedTerm Nat → Prop
  height : RaisedTerm Nat → Nat

/-- The predictive labelling: every constructor occurrence is labelled by the prediction of the
subterm it heads, with labels in `{0,1}`; variables are unchanged. -/
def labelPredict (predict : FreeTerm Nat → Bool) : FreeTerm Nat → RaisedTerm Nat
  | .var x => .var x
  | .zero => .zero (if predict .zero then 1 else 0)
  | .succ t => .succ (if predict (.succ t) then 1 else 0) (labelPredict predict t)
  | .wrap s t => .wrap (if predict (.wrap s t) then 1 else 0)
      (labelPredict predict s) (labelPredict predict t)
  | .recur b s n => .recur (if predict (.recur b s n) then 1 else 0)
      (labelPredict predict b) (labelPredict predict s) (labelPredict predict n)

/-- The predictive labelling of a data instance. -/
def predictiveLabel (M : predictiveLabelingData) : FreeTerm Nat → RaisedTerm Nat :=
  labelPredict M.predict

/-- Admissibility of predictive labelling (Hirokawa and Middeldorp, `Predictive Labeling`, RTA
2006, LNCS 4098, Definition 5 for the usable rules and Theorem 18 for the soundness direction):
the prediction is consistent on both rule schemas at every valuation, the labelled system is
source-sound through the predictive labelling, and the labelled height drops strictly on every
labelled step. -/
def predictiveLabelingLaws (M : predictiveLabelingData) : Prop :=
  (∀ σ : Nat → FreeTerm Nat,
    M.predict (FreeTerm.subst σ (.recur (.var 0) (.var 1) (.succ (.var 2)))) =
        M.predict (FreeTerm.subst σ (.wrap (.var 1) (.recur (.var 0) (.var 1) (.var 2)))) ∧
      M.predict (FreeTerm.subst σ (.recur (.var 0) (.var 1) .zero)) =
        M.predict (FreeTerm.subst σ (.var 0))) ∧
  (∀ {s t : FreeTerm Nat}, M.sys s t →
    M.labelled (predictiveLabel M s) (predictiveLabel M t)) ∧
  (∀ {a b : RaisedTerm Nat}, M.labelled a b → M.height b + 1 ≤ M.height a)

/-- The method accepts the free two-rule system through the labelling adapter. -/
def predictiveLabelingAccepts (M : predictiveLabelingData) : Prop :=
  ∀ s t : FreeTerm Nat, M.sys s t ↔ ContextStep s t

/-- Consistency makes the predictive labelling source-linked, and the labelled height drop carries
the soundness proof: termination of the labelled system yields termination of the free two-rule
system (Hirokawa and Middeldorp 2006, Theorem 18).
Verdict: escape. -/
def predictiveLabelingResult (M : predictiveLabelingData) : Prop :=
  predictiveLabelingAccepts M ∧ FreeSchemaTerminates

theorem predictiveLabeling_sound : ∀ M : predictiveLabelingData,
    predictiveLabelingLaws M → predictiveLabelingAccepts M → FreeSchemaTerminates := by
  intro M hL hA
  exact freeSchemaTerminates_of_raisedHeight (raiseT := predictiveLabel M)
    (fun {s t} h => hL.2.2 (hL.2.1 ((hA s t).mpr h)))

@[simp] theorem erase_labelPredict (predict : FreeTerm Nat → Bool) (t : FreeTerm Nat) :
    (labelPredict predict t).erase = t := by
  induction t with
  | var x => rfl
  | zero => rfl
  | succ t ih => simp [labelPredict, RaisedTerm.erase, ih]
  | wrap s t ihs iht => simp [labelPredict, RaisedTerm.erase, ihs, iht]
  | recur b s n ihb ihs ihn => simp [labelPredict, RaisedTerm.erase, ihb, ihs, ihn]

/-- The witness predicts every term as `true` (the maximal prediction), labels by it, lifts the
free contextual steps, and takes the weight of the erasure as the labelled height. -/
def predictiveLabelingWitness : predictiveLabelingData where
  predict := fun _ => true
  sys := ContextStep
  labelled := fun a b => ∃ s t : FreeTerm Nat, ContextStep s t ∧
    a = labelPredict (fun _ => true) s ∧ b = labelPredict (fun _ => true) t
  height := fun a => qw a.erase

theorem predictiveLabelingWitness_laws : predictiveLabelingLaws predictiveLabelingWitness := by
  refine ⟨?_, ?_, ?_⟩
  · intro σ
    exact ⟨rfl, rfl⟩
  · intro s t h
    exact ⟨s, t, h, rfl, rfl⟩
  · rintro a b ⟨s, t, hst, rfl, rfl⟩
    have hq := qw_contextStep hst
    show qw (labelPredict (fun _ => true) t).erase + 1 ≤
      qw (labelPredict (fun _ => true) s).erase
    rw [erase_labelPredict, erase_labelPredict]
    omega

theorem predictiveLabelingWitness_result :
    predictiveLabelingResult predictiveLabelingWitness :=
  ⟨fun _ _ => Iff.rfl,
    predictiveLabeling_sound _ predictiveLabelingWitness_laws (fun _ _ => Iff.rfl)⟩

/-- Number of occurrences of variable `x` in a raised term. -/
def payloadCount (x : Nat) : RaisedTerm Nat → Nat
  | .var y => if y = x then 1 else 0
  | .zero _ => 0
  | .succ _ t => payloadCount x t
  | .wrap _ s t => payloadCount x s + payloadCount x t
  | .recur _ b s n => payloadCount x b + payloadCount x s + payloadCount x n

/-- The defining features of the row: the predictive labelling is source-linked (its erasure is
exact for every prediction), the payload variable has multiplicity one on the duplicating
left-hand side and two on the right-hand side even under labels, and consistency holds at an
arbitrary changed valuation. -/
theorem predictiveLabelingWitness_feature :
    (∀ predict : FreeTerm Nat → Bool, (labelPredict predict schemaLhsSucc).erase = schemaLhsSucc) ∧
      payloadCount 1 (labelPredict (fun _ => true) schemaLhsSucc) = 1 ∧
      payloadCount 1 (labelPredict (fun _ => true) schemaRhsSucc) = 2 ∧
      (∀ σ : Nat → FreeTerm Nat,
        predictiveLabelingWitness.predict (FreeTerm.subst σ schemaLhsSucc) =
          predictiveLabelingWitness.predict (FreeTerm.subst σ schemaRhsSucc)) := by
  refine ⟨fun predict => erase_labelPredict predict schemaLhsSucc, by decide, by decide,
    fun σ => rfl⟩

/-- Changing the prediction to the incorrect one that recognizes only recursor-rooted terms,
everything else fixed, breaks prediction consistency on the rule schema. -/
theorem predictiveLabeling_mutation :
    ¬ predictiveLabelingLaws
      { predictiveLabelingWitness with
        predict := fun t =>
          match t with
          | .recur _ _ _ => true
          | _ => false } := by
  intro hL
  have hcons := (hL.1 (fun x => FreeTerm.var x)).1
  rw [FreeTerm.subst_id, FreeTerm.subst_id] at hcons
  change (match FreeTerm.recur (.var 0) (.var 1) (.succ (.var 2)) with
      | .recur _ _ _ => true
      | _ => false) =
    (match FreeTerm.wrap (.var 1) (FreeTerm.recur (.var 0) (.var 1) (.var 2)) with
      | .recur _ _ _ => true
      | _ => false) at hcons
  rw [show (match FreeTerm.recur (.var 0) (.var 1) (.succ (.var 2)) with
      | .recur _ _ _ => true
      | _ => false) = true from rfl,
    show (match FreeTerm.wrap (.var 1) (FreeTerm.recur (.var 0) (.var 1) (.var 2)) with
      | .recur _ _ _ => true
      | _ => false) = false from rfl] at hcons
  exact Bool.noConfusion hcons

/-! ### Row: forwardClosures -/

/-- The right-hand side of the zero rule of the free schema. -/
def schemaRhsZero : FreeTerm Nat := .var 0

/-- Native data of the forward-closure row: the certified rule patterns, the source system, and
the right-forward closure of the rule right-hand sides. -/
structure forwardClosuresData where
  lhs : FreeTerm Nat
  rhs : FreeTerm Nat
  sys : FreeTerm Nat → FreeTerm Nat → Prop
  closure : FreeTerm Nat → Prop

/-- Admissibility of the right-forward closure criterion (Dershowitz, `Termination of linear
rewriting systems`, ICALP 1981, LNCS 115, pp. 448-458, the right-linear case; Thiemann, Hofbauer,
Le Huitouze and Waldmann, `Termination Restricted to Right-Forward Closures`, Archive of Formal
Proofs 2026, theory `Right-Forward-Closure`, the definition `right_forw_closure` and the theorem
`right_linear_SN_rstep_RFC`; the right-forward closure is generated from the right-hand-side
instances of the system and is closed under the system): the certified right-hand side is
right-linear, every rule right-hand-side instance lies in the closure, the closure is closed under
the system, and the system is a subsystem of the free schema's contextual relation. -/
def forwardClosuresLaws (M : forwardClosuresData) : Prop :=
  (freeVars M.rhs).Nodup ∧
    (∀ {s t : FreeTerm Nat}, M.sys s t → ContextStep s t) ∧
    (∀ σ : Nat → FreeTerm Nat, M.closure (FreeTerm.subst σ M.rhs)) ∧
    (∀ {s t : FreeTerm Nat}, M.sys s t → M.closure s → M.closure t)

/-- The method accepts the free two-rule system when the certified right-hand side is the
duplicating one and the adapter covers the free schema's contextual steps. -/
def forwardClosuresAccepts (M : forwardClosuresData) : Prop :=
  M.rhs = schemaRhsSucc ∧ (∀ s t : FreeTerm Nat, M.sys s t ↔ ContextStep s t)

/-- The duplicating right-hand side is not right-linear, so the right-linear forward-closure
criterion does not apply: no admissible right-linear certificate certifies the free duplicating
rule (Dershowitz 1981, right-linearity hypothesis; the payload variable occurs twice on the
right).
Verdict: barrier. -/
def forwardClosuresResult (M : forwardClosuresData) : Prop :=
  ¬ forwardClosuresAccepts M

theorem forwardClosures_universal : ∀ M : forwardClosuresData,
    forwardClosuresLaws M → forwardClosuresResult M := by
  intro M hL hA
  exact absurd (hA.1 ▸ hL.1) (by decide)

/-- The witness certifies the right-linear zero-rule right-hand side and takes the full carrier
as the closure. -/
def forwardClosuresWitness : forwardClosuresData where
  lhs := schemaLhsZero
  rhs := schemaRhsZero
  sys := ContextStep
  closure := fun _ => True

theorem forwardClosuresWitness_laws : forwardClosuresLaws forwardClosuresWitness := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro s t h
    exact h
  · intro σ
    trivial
  · intro s t _ _
    trivial

theorem forwardClosuresWitness_result : forwardClosuresResult forwardClosuresWitness :=
  forwardClosures_universal _ forwardClosuresWitness_laws

/-- The nontrivial admitted system: the ground zero-rule step `recur 0 0 0 → 0` is a right-linear
system whose right-hand side lies in the closure and whose closure is closed under it. -/
def forwardClosuresChained : forwardClosuresData where
  lhs := schemaLhsZero
  rhs := schemaRhsZero
  sys := fun s t => s = FreeTerm.recur .zero .zero .zero ∧ t = .zero
  closure := fun _ => True

theorem forwardClosuresChained_laws : forwardClosuresLaws forwardClosuresChained := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rintro s t ⟨rfl, rfl⟩
    exact rootStep_contextStep (.recurZero .zero .zero)
  · intro σ
    trivial
  · intro s t _ _
    trivial

/-- The consequence for the right-linear theorem on the admitted system: the system is well
founded, so the closure restriction terminates. -/
theorem forwardClosuresChained_wf :
    WellFounded (fun u t : FreeTerm Nat => forwardClosuresChained.sys t u) := by
  refine Subrelation.wf (fun {u t} h => ?_) (InvImage.wf qw Nat.lt_wfRel.wf)
  obtain ⟨rfl, rfl⟩ := h
  show qw (.zero : FreeTerm Nat) < qw (FreeTerm.recur .zero .zero .zero)
  simp only [qw]
  omega

/-- The defining features of the row: the duplicating right-hand side is not right-linear, the
zero-rule right-hand side is, and the nontrivial admitted system satisfies the closure laws and is
well founded. -/
theorem forwardClosuresWitness_feature :
    ¬ (freeVars schemaRhsSucc).Nodup ∧
      (freeVars schemaRhsZero).Nodup ∧
      forwardClosuresLaws forwardClosuresChained ∧
      (∃ s t : FreeTerm Nat, forwardClosuresChained.sys s t) ∧
      WellFounded (fun u t : FreeTerm Nat => forwardClosuresChained.sys t u) :=
  ⟨by decide, by decide, forwardClosuresChained_laws,
    ⟨.recur .zero .zero .zero, .zero, rfl, rfl⟩, forwardClosuresChained_wf⟩

/-- Changing the certified right-hand side to the duplicating one, everything else fixed, breaks
the right-linearity law of the criterion. -/
theorem forwardClosures_mutation :
    ¬ forwardClosuresLaws { forwardClosuresWitness with rhs := schemaRhsSucc } := by
  intro hL
  exact absurd hL.1 (by decide)

end OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds
