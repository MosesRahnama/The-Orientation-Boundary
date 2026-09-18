import OperatorKO7.Meta.OperationalInexpressibility.FaithfulRecursorRealization
import OperatorKO7.Meta.Methods.OrientationClosure.SignatureInstances
import OperatorKO7.Meta.Methods.OrientationClosure.CouplingTheorem
import OperatorKO7.Meta.Methods.OrientationClosure.CellClassification
import OperatorKO7.Meta.Methods.OrientationClosure.FreePolynomialTermination
import Mathlib.Tactic

/-!
# Goedel's System T on the Orientation Boundary (row B1)

System T is written in locally nameless raw syntax: free variables, bound variables, zero,
successor, application, abstraction, the iterator `It` and the recursor `R`. One step of
reduction (`TStep`) is beta, the two iterator rules, the two recursor rules, or a step inside any
constructor.

Iterator shape. The constructor fold `iterFold` sends `wrap` to application and `recur` to `It`.
It is injective and its image is exactly the terms without abstraction, bound variables and
recursor (`mem_range_iterFold_iff`). Full System T reduction from an image term stays in the image
and is the fold of the free contextual step (`contextStep_iff_tStep`, `tStep_iterFold_closed`), so
the fold is a closed relation embedding and a relation isomorphism onto its image
(`iterEmbedding`, `iterRelIso`). The image is a step-duplicating schema isomorphic to the free
schema (`iterImageIso`); the exact criterion, the coupling inequality and the barrier cell hold on
it as instances, and every image term is strongly normalizing under full System T reduction
(`iterFold_acc`, transported from the free contextual termination theorem). Hom-set: a schema
morphism out of the free schema is the fold of its variable assignment (`schemaHom_eq_foldWith`);
the assignment of a beta redex to a variable gives a schema morphism that does not reflect steps
(`betaAssignment_not_reflecting`).

Recursor shape. `R b s (S n) -> s n (R b s n)` duplicates the step and the counter. No two-hole
wrapper context realizes it (`no_two_hole_wrapper_realizes_recursor`); the three-place wrapper
`app (app s n) y` does (`recursorSchema_rule`). For three-place wrappers the coupling inequality
carries the retained counter (`retained_wrapper3_forces_counter_coupled_gain`) and a gain bounded
independently of the counter is excluded (`no_orientation3_of_counter_bounded_gain`). The free
schema's polynomial escape orients the iterator and fails on the recursor exactly when the counter
outweighs the base (`schemaWeight_recursor_iff`), and the barrier excludes it uniformly
(`schemaWeight_not_orients_recursor`). Adding the squared counter to the recursor clause orients
both shapes (`tWeight_orients_recursor`), so every abstraction-free System T term is strongly
normalizing (`lamFree_acc`).
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.SystemTRecursor

open OperatorKO7.StepDuplicating
open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.SignatureInstances
open OperatorKO7.Methods.OrientationClosure.CouplingTheorem
open OperatorKO7.Methods.OrientationClosure.CellClassification

/-! ## System T syntax and reduction -/

/-- Raw System T syntax in locally nameless form. -/
inductive TTerm (ν : Type) where
  | fvar (x : ν)
  | bvar (i : Nat)
  | zero
  | succ (t : TTerm ν)
  | app (f a : TTerm ν)
  | lam (t : TTerm ν)
  | iter (b s n : TTerm ν)
  | recR (b s n : TTerm ν)

variable {ν : Type}

/-- Replace the bound variable of index `k` by `u`. -/
def TTerm.openAt (u : TTerm ν) : Nat → TTerm ν → TTerm ν
  | _, .fvar x => .fvar x
  | k, .bvar i => if i = k then u else .bvar i
  | _, .zero => .zero
  | k, .succ t => .succ (TTerm.openAt u k t)
  | k, .app f a => .app (TTerm.openAt u k f) (TTerm.openAt u k a)
  | k, .lam t => .lam (TTerm.openAt u (k + 1) t)
  | k, .iter b s n => .iter (TTerm.openAt u k b) (TTerm.openAt u k s) (TTerm.openAt u k n)
  | k, .recR b s n => .recR (TTerm.openAt u k b) (TTerm.openAt u k s) (TTerm.openAt u k n)

/-- One step of System T reduction: beta, the iterator rules, the recursor rules, and a step
inside any constructor. -/
inductive TStep : TTerm ν → TTerm ν → Prop where
  | beta (t u : TTerm ν) : TStep (.app (.lam t) u) (TTerm.openAt u 0 t)
  | itZero (b s : TTerm ν) : TStep (.iter b s .zero) b
  | itSucc (b s n : TTerm ν) : TStep (.iter b s (.succ n)) (.app s (.iter b s n))
  | recZero (b s : TTerm ν) : TStep (.recR b s .zero) b
  | recSucc (b s n : TTerm ν) : TStep (.recR b s (.succ n)) (.app (.app s n) (.recR b s n))
  | succ {t t' : TTerm ν} : TStep t t' → TStep (.succ t) (.succ t')
  | appL {f f' : TTerm ν} (a : TTerm ν) : TStep f f' → TStep (.app f a) (.app f' a)
  | appR (f : TTerm ν) {a a' : TTerm ν} : TStep a a' → TStep (.app f a) (.app f a')
  | lam {t t' : TTerm ν} : TStep t t' → TStep (.lam t) (.lam t')
  | itB {b b' : TTerm ν} (s n : TTerm ν) : TStep b b' → TStep (.iter b s n) (.iter b' s n)
  | itS (b : TTerm ν) {s s' : TTerm ν} (n : TTerm ν) : TStep s s' → TStep (.iter b s n) (.iter b s' n)
  | itN (b s : TTerm ν) {n n' : TTerm ν} : TStep n n' → TStep (.iter b s n) (.iter b s n')
  | recB {b b' : TTerm ν} (s n : TTerm ν) : TStep b b' → TStep (.recR b s n) (.recR b' s n)
  | recS (b : TTerm ν) {s s' : TTerm ν} (n : TTerm ν) :
      TStep s s' → TStep (.recR b s n) (.recR b s' n)
  | recN (b s : TTerm ν) {n n' : TTerm ν} : TStep n n' → TStep (.recR b s n) (.recR b s n')

/-- System T with the iterator reading of the schema: `wrap` is application, `recur` is `It`. -/
def iteratorSchema (ν : Type) : StepDuplicatingSchema where
  T := TTerm ν
  base := .zero
  succ := .succ
  wrap := .app
  recur := .iter

/-! ## The iterator fold -/

/-- The fold of the free schema into System T with a variable assignment. -/
def foldWith (σ : ν → TTerm ν) : FreeTerm ν → TTerm ν
  | .var x => σ x
  | .zero => .zero
  | .succ t => .succ (foldWith σ t)
  | .wrap s y => .app (foldWith σ s) (foldWith σ y)
  | .recur b s n => .iter (foldWith σ b) (foldWith σ s) (foldWith σ n)

/-- The iterator fold: variables to free variables, `wrap` to application, `recur` to `It`. -/
def iterFold : FreeTerm ν → TTerm ν
  | .var x => .fvar x
  | .zero => .zero
  | .succ t => .succ (iterFold t)
  | .wrap s y => .app (iterFold s) (iterFold y)
  | .recur b s n => .iter (iterFold b) (iterFold s) (iterFold n)

theorem iterFold_eq_foldWith (t : FreeTerm ν) : iterFold t = foldWith TTerm.fvar t := by
  induction t <;> simp_all [iterFold, foldWith]

/-- Read a System T term as a free term. Abstraction, bound variables and the recursor lie
outside the image of the fold and are read by a fixed convention. -/
def unfoldT : TTerm ν → FreeTerm ν
  | .fvar x => .var x
  | .bvar _ => .zero
  | .zero => .zero
  | .succ t => .succ (unfoldT t)
  | .app f a => .wrap (unfoldT f) (unfoldT a)
  | .lam t => unfoldT t
  | .iter b s n => .recur (unfoldT b) (unfoldT s) (unfoldT n)
  | .recR b s n => .recur (unfoldT b) (unfoldT s) (unfoldT n)

theorem unfoldT_iterFold (t : FreeTerm ν) : unfoldT (iterFold t) = t := by
  induction t <;> simp_all [iterFold, unfoldT]

theorem iterFold_injective : Function.Injective (iterFold : FreeTerm ν → TTerm ν) :=
  Function.LeftInverse.injective unfoldT_iterFold

/-- System T terms without abstraction, bound variables or recursor. -/
inductive IterFree : TTerm ν → Prop
  | fvar (x : ν) : IterFree (.fvar x)
  | zero : IterFree .zero
  | succ {t : TTerm ν} : IterFree t → IterFree (.succ t)
  | app {f a : TTerm ν} : IterFree f → IterFree a → IterFree (.app f a)
  | iter {b s n : TTerm ν} : IterFree b → IterFree s → IterFree n → IterFree (.iter b s n)

theorem iterFree_iterFold (t : FreeTerm ν) : IterFree (iterFold t) := by
  induction t with
  | var x => exact .fvar x
  | zero => exact .zero
  | succ t ih => exact .succ ih
  | wrap s y ihs ihy => exact .app ihs ihy
  | recur b s n ihb ihs ihn => exact .iter ihb ihs ihn

theorem iterFold_unfoldT {u : TTerm ν} (h : IterFree u) : iterFold (unfoldT u) = u := by
  induction h with
  | fvar x => rfl
  | zero => rfl
  | succ _ ih => simp only [unfoldT, iterFold, ih]
  | app _ _ ihf iha => simp only [unfoldT, iterFold, ihf, iha]
  | iter _ _ _ ihb ihs ihn => simp only [unfoldT, iterFold, ihb, ihs, ihn]

/-- The image of the fold is exactly the terms without abstraction, bound variables and
recursor. -/
theorem mem_range_iterFold_iff (u : TTerm ν) :
    u ∈ Set.range (iterFold : FreeTerm ν → TTerm ν) ↔ IterFree u :=
  ⟨fun ⟨t, ht⟩ => ht ▸ iterFree_iterFold t, fun h => ⟨unfoldT u, iterFold_unfoldT h⟩⟩

/-! ## Reduction on the image -/

/-- The fold carries a step through any constructor context. -/
theorem tStep_plug {t u : FreeTerm ν} (h : TStep (iterFold t) (iterFold u)) :
    ∀ C : FreeContext ν, TStep (iterFold (C.plug t)) (iterFold (C.plug u)) := by
  intro C
  induction C with
  | hole => exact h
  | succ C ih => exact .succ ih
  | wrapLeft C r ih => exact .appL _ ih
  | wrapRight l C ih => exact .appR _ ih
  | recurBase C s n ih => exact .itB _ _ ih
  | recurStep b C n ih => exact .itS _ _ ih
  | recurCounter b s C ih => exact .itN _ _ ih

theorem tStep_of_rootStep {t u : FreeTerm ν} (h : RootStep t u) :
    TStep (iterFold t) (iterFold u) := by
  cases h with
  | recurZero b s => exact .itZero _ _
  | recurSucc b s n => exact .itSucc _ _ _

theorem tStep_of_contextStep {t u : FreeTerm ν} (h : ContextStep t u) :
    TStep (iterFold t) (iterFold u) := by
  cases h with
  | lift C hr => exact tStep_plug (tStep_of_rootStep hr) C

/-- Reduction from a term without abstraction, bound variables or recursor stays in that class,
and its reading is a free contextual step. -/
theorem iterFree_step {t u : TTerm ν} (h : TStep t u) :
    IterFree t → IterFree u ∧ ContextStep (unfoldT t) (unfoldT u) := by
  induction h with
  | beta t u =>
      intro ht
      cases ht with
      | app hf _ => cases hf
  | itZero b s =>
      intro ht
      cases ht with
      | iter hb _ _ => exact ⟨hb, rootStep_contextStep (.recurZero _ _)⟩
  | itSucc b s n =>
      intro ht
      cases ht with
      | iter hb hs hn =>
          cases hn with
          | succ hn' => exact ⟨.app hs (.iter hb hs hn'), rootStep_contextStep (.recurSucc _ _ _)⟩
  | recZero b s =>
      intro ht
      cases ht
  | recSucc b s n =>
      intro ht
      cases ht
  | succ _ ih =>
      intro ht
      cases ht with
      | succ ht' =>
          obtain ⟨hu, hc⟩ := ih ht'
          exact ⟨.succ hu, hc.outer (.succ .hole)⟩
  | appL a _ ih =>
      intro ht
      cases ht with
      | app hf ha =>
          obtain ⟨hu, hc⟩ := ih hf
          exact ⟨.app hu ha, hc.outer (.wrapLeft .hole _)⟩
  | appR f _ ih =>
      intro ht
      cases ht with
      | app hf ha =>
          obtain ⟨hu, hc⟩ := ih ha
          exact ⟨.app hf hu, hc.outer (.wrapRight _ .hole)⟩
  | lam _ _ =>
      intro ht
      cases ht
  | itB s n _ ih =>
      intro ht
      cases ht with
      | iter hb hs hn =>
          obtain ⟨hu, hc⟩ := ih hb
          exact ⟨.iter hu hs hn, hc.outer (.recurBase .hole _ _)⟩
  | itS b n _ ih =>
      intro ht
      cases ht with
      | iter hb hs hn =>
          obtain ⟨hu, hc⟩ := ih hs
          exact ⟨.iter hb hu hn, hc.outer (.recurStep _ .hole _)⟩
  | itN b s _ ih =>
      intro ht
      cases ht with
      | iter hb hs hn =>
          obtain ⟨hu, hc⟩ := ih hn
          exact ⟨.iter hb hs hu, hc.outer (.recurCounter _ _ .hole)⟩
  | recB s n _ _ =>
      intro ht
      cases ht
  | recS b n _ _ =>
      intro ht
      cases ht
  | recN b s _ _ =>
      intro ht
      cases ht

/-- System T reduction from an image term stays in the image. -/
theorem tStep_iterFold_closed {t : FreeTerm ν} {u : TTerm ν} (h : TStep (iterFold t) u) :
    ∃ t', iterFold t' = u :=
  ⟨unfoldT u, iterFold_unfoldT (iterFree_step h (iterFree_iterFold t)).1⟩

/-- Full System T reduction between image terms is exactly the free contextual step. -/
theorem contextStep_iff_tStep (t u : FreeTerm ν) :
    ContextStep t u ↔ TStep (iterFold t) (iterFold u) := by
  constructor
  · exact tStep_of_contextStep
  · intro h
    have hc := (iterFree_step h (iterFree_iterFold t)).2
    rwa [unfoldT_iterFold, unfoldT_iterFold] at hc

/-- The fold is a closed relation embedding of the free contextual step into full System T
reduction. -/
def iterEmbedding (ν : Type) :
    OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile.ClosedRelationEmbedding
      (@ContextStep ν) (@TStep ν) where
  map := ⟨iterFold, iterFold_injective⟩
  step_iff := fun {t u} => contextStep_iff_tStep t u
  forward_closed := fun {_ _} h => tStep_iterFold_closed h

/-- The fold is a relation isomorphism from the free contextual step onto System T reduction
restricted to the image. -/
noncomputable def iterRelIso (ν : Type) :
    OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso (@ContextStep ν)
      (fun x y : Set.range (iterFold : FreeTerm ν → TTerm ν) => TStep x.val y.val) where
  toEquiv := Equiv.ofInjective iterFold iterFold_injective
  map_rel_iff := fun {t u} => contextStep_iff_tStep t u

/-- Every image term is strongly normalizing under full System T reduction: the free contextual
termination theorem transported along the closed embedding. -/
theorem iterFold_acc (t : FreeTerm ν) : Acc (fun u v : TTerm ν => TStep v u) (iterFold t) :=
  (OperatorKO7.Meta.OperationalInexpressibility.FaithfulRecursorRealization.closedEmbedding_acc_iff
    (iterEmbedding ν) t).1
    ((OperatorKO7.Methods.OrientationClosure.FreePolynomialTermination.main_free_contextual_termination
      ν).apply t)

theorem iterFree_acc {u : TTerm ν} (h : IterFree u) : Acc (fun u v : TTerm ν => TStep v u) u :=
  iterFold_unfoldT h ▸ iterFold_acc (unfoldT u)

/-! ## Transport of the orientation results to the image -/

/-- The image of the fold as a step-duplicating schema. -/
def iterImageSchema (ν : Type) : StepDuplicatingSchema where
  T := {u : TTerm ν // IterFree u}
  base := ⟨.zero, .zero⟩
  succ := fun t => ⟨.succ t.1, .succ t.2⟩
  wrap := fun x y => ⟨.app x.1 y.1, .app x.2 y.2⟩
  recur := fun b s n => ⟨.iter b.1 s.1 n.1, .iter b.2 s.2 n.2⟩

/-- The free schema is isomorphic to the image of the fold. -/
def iterImageIso (ν : Type) : SchemaIso (freeSchema ν) (iterImageSchema ν) where
  toEquiv :=
    { toFun := fun t => ⟨iterFold t, iterFree_iterFold t⟩
      invFun := fun u => unfoldT u.1
      left_inv := fun t => unfoldT_iterFold t
      right_inv := fun u => Subtype.ext (iterFold_unfoldT u.2) }
  map_base := rfl
  map_succ _ := rfl
  map_wrap _ _ := rfl
  map_recur _ _ _ := rfl

/-- Orientation of the duplicating rule on the image is orientation on the free schema. -/
theorem iterImage_orients_iff (M : (iterImageSchema ν).T → Nat) :
    (∀ b s n : (freeSchema ν).T,
        M ((iterImageIso ν).toEquiv ((freeSchema ν).wrap s ((freeSchema ν).recur b s n))) <
          M ((iterImageIso ν).toEquiv ((freeSchema ν).recur b s ((freeSchema ν).succ n)))) ↔
      ∀ b s n : (iterImageSchema ν).T,
        M ((iterImageSchema ν).wrap s ((iterImageSchema ν).recur b s n)) <
          M ((iterImageSchema ν).recur b s ((iterImageSchema ν).succ n)) :=
  SchemaIso.orients_iff (iterImageIso ν) M

/-- The exact criterion on System T iterator terms. -/
theorem iterImage_exact_criterion (M : (iterImageSchema ν).T → Nat) :
    (∀ b s n : (iterImageSchema ν).T,
        M ((iterImageSchema ν).wrap s ((iterImageSchema ν).recur b s n)) <
          M ((iterImageSchema ν).recur b s ((iterImageSchema ν).succ n))) ↔
      ∀ b s n : (iterImageSchema ν).T,
        wrapperCostZ (S := iterImageSchema ν) M b s n < counterGainZ (S := iterImageSchema ν) M b s n :=
  orients_all_iff_wrapperCost_lt_counterGain (S := iterImageSchema ν) M

/-- The coupling inequality on System T iterator terms. -/
theorem iterImage_coupling (M : (iterImageSchema ν).T → Nat) (c_w : Nat)
    (hretain : ∀ x y : (iterImageSchema ν).T, c_w + M x + M y ≤ M ((iterImageSchema ν).wrap x y))
    (horient : ∀ b s n : (iterImageSchema ν).T,
      M ((iterImageSchema ν).wrap s ((iterImageSchema ν).recur b s n)) <
        M ((iterImageSchema ν).recur b s ((iterImageSchema ν).succ n))) :
    ∀ b s n : (iterImageSchema ν).T,
      (M s : Int) + (c_w : Int) < counterGainZ (S := iterImageSchema ν) M b s n :=
  retained_wrapper_forces_payload_coupled_gain (S := iterImageSchema ν) M c_w hretain horient

/-- The barrier cell on System T iterator terms. -/
theorem iterImage_barrier_cell (M : (iterImageSchema ν).T → Nat) (b n : (iterImageSchema ν).T)
    (hw : WrapUnboundedAt (S := iterImageSchema ν) M b n)
    (hg : GainBoundedAt (S := iterImageSchema ν) M b n) :
    ¬ ∀ s : (iterImageSchema ν).T,
      M ((iterImageSchema ν).wrap s ((iterImageSchema ν).recur b s n)) <
        M ((iterImageSchema ν).recur b s ((iterImageSchema ν).succ n)) :=
  barrier_cell_excludes_orientation (S := iterImageSchema ν) M b n hw hg

/-! ## The hom-set of the fold -/

/-- A map of schema carriers commuting with the four operations. -/
structure SchemaHom (S S' : StepDuplicatingSchema) where
  map : S.T → S'.T
  map_base : map S.base = S'.base
  map_succ : ∀ t, map (S.succ t) = S'.succ (map t)
  map_wrap : ∀ x y, map (S.wrap x y) = S'.wrap (map x) (map y)
  map_recur : ∀ b s n, map (S.recur b s n) = S'.recur (map b) (map s) (map n)

/-- The fold with any variable assignment is a schema morphism into the iterator schema. -/
def foldWithHom (σ : ν → TTerm ν) : SchemaHom (freeSchema ν) (iteratorSchema ν) where
  map := foldWith σ
  map_base := rfl
  map_succ _ := rfl
  map_wrap _ _ := rfl
  map_recur _ _ _ := rfl

theorem foldWithHom_var (σ : ν → TTerm ν) (x : ν) : (foldWithHom σ).map (.var x) = σ x := rfl

/-- The hom-set: every schema morphism from the free schema to the iterator schema is the fold of
its variable assignment, so the morphisms correspond to the maps `ν → TTerm ν`. -/
theorem schemaHom_eq_foldWith (g : SchemaHom (freeSchema ν) (iteratorSchema ν)) :
    g.map = foldWith (fun x => g.map (.var x)) := by
  funext t
  induction t with
  | var x => rfl
  | zero => exact g.map_base
  | succ t ih => exact (g.map_succ t).trans (congrArg TTerm.succ ih)
  | wrap s y ihs ihy => exact (g.map_wrap s y).trans (by rw [ihs, ihy]; rfl)
  | recur b s n ihb ihs ihn => exact (g.map_recur b s n).trans (by rw [ihb, ihs, ihn]; rfl)

/-- A variable of the free schema has no contextual step. -/
theorem var_irreducible (x : ν) (u : FreeTerm ν) : ¬ ContextStep (.var x) u := by
  intro h
  generalize hv : (FreeTerm.var x : FreeTerm ν) = v at h
  cases h with
  | lift C hr =>
    cases C with
    | hole =>
      simp only [FreeContext.plug] at hv
      subst hv
      cases hr
    | succ C => simp [FreeContext.plug] at hv
    | wrapLeft C r => simp [FreeContext.plug] at hv
    | wrapRight l C => simp [FreeContext.plug] at hv
    | recurBase C s n => simp [FreeContext.plug] at hv
    | recurStep b C n => simp [FreeContext.plug] at hv
    | recurCounter b s C => simp [FreeContext.plug] at hv

/-- Another element of the hom-set: sending every variable to a beta redex is a schema morphism,
and it does not reflect steps, since the image of a variable reduces while the variable does
not. -/
theorem betaAssignment_not_reflecting (x : ν) :
    TStep ((foldWithHom (fun _ => .app (.lam (.bvar 0)) .zero)).map (.var x)) .zero ∧
      ∀ u : FreeTerm ν, ¬ ContextStep (.var x) u := by
  refine ⟨?_, var_irreducible x⟩
  have h := TStep.beta (ν := ν) (.bvar 0) .zero
  simpa [TTerm.openAt] using h

/-! ## The recursor shape -/

/-- Fill a two-hole wrapper context: the free variable `false` is the step argument and `true`
the recursive value. -/
def fill2 (s y : TTerm ν) : TTerm Bool → TTerm ν
  | .fvar false => s
  | .fvar true => y
  | .bvar i => .bvar i
  | .zero => .zero
  | .succ t => .succ (fill2 s y t)
  | .app f a => .app (fill2 s y f) (fill2 s y a)
  | .lam t => .lam (fill2 s y t)
  | .iter b s' n => .iter (fill2 s y b) (fill2 s y s') (fill2 s y n)
  | .recR b s' n => .recR (fill2 s y b) (fill2 s y s') (fill2 s y n)

/-- The iterator rule is the free rule under the two-hole wrapper `app hole₁ hole₂`. -/
theorem iterator_wrapper_realizes :
    ∃ W : TTerm Bool, ∀ b s n : TTerm ν, fill2 s (.iter b s n) W = .app s (.iter b s n) :=
  ⟨.app (.fvar false) (.fvar true), fun _ _ _ => rfl⟩

/-- No two-hole wrapper context realizes the recursor rule: its right side carries the counter
outside the recursive call. -/
theorem no_two_hole_wrapper_realizes_recursor :
    ¬ ∃ W : TTerm Bool, ∀ b s n : TTerm Nat,
      fill2 s (.recR b s n) W = .app (.app s n) (.recR b s n) := by
  rintro ⟨W, hW⟩
  have h := hW (.fvar 0) (.fvar 1) (.fvar 2)
  cases W with
  | fvar x => cases x <;> simp [fill2] at h
  | bvar i => simp [fill2] at h
  | zero => simp [fill2] at h
  | succ t => simp [fill2] at h
  | lam t => simp [fill2] at h
  | iter b s n => simp [fill2] at h
  | recR b s n => simp [fill2] at h
  | app W₁ W₂ =>
    simp only [fill2, TTerm.app.injEq] at h
    obtain ⟨h₁, -⟩ := h
    cases W₁ with
    | fvar x => cases x <;> simp [fill2] at h₁
    | bvar i => simp [fill2] at h₁
    | zero => simp [fill2] at h₁
    | succ t => simp [fill2] at h₁
    | lam t => simp [fill2] at h₁
    | iter b s n => simp [fill2] at h₁
    | recR b s n => simp [fill2] at h₁
    | app V₁ V₂ =>
      simp only [fill2, TTerm.app.injEq] at h₁
      obtain ⟨-, h₂⟩ := h₁
      cases V₂ with
      | fvar x => cases x <;> simp [fill2] at h₂
      | bvar i => simp [fill2] at h₂
      | zero => simp [fill2] at h₂
      | succ t => simp [fill2] at h₂
      | app f a => simp [fill2] at h₂
      | lam t => simp [fill2] at h₂
      | iter b s n => simp [fill2] at h₂
      | recR b s n => simp [fill2] at h₂

/-- A constructor interface whose wrapper also receives the counter. -/
structure CounterWrapSchema where
  T : Type
  base : T
  succ : T → T
  wrap3 : T → T → T → T
  recur : T → T → T → T

/-- System T with the recursor reading: the wrapper is `app (app s n) y`. -/
def recursorSchema (ν : Type) : CounterWrapSchema where
  T := TTerm ν
  base := .zero
  succ := .succ
  wrap3 := fun s n y => .app (.app s n) y
  recur := .recR

/-- The recursor rule is the duplicating rule of the three-place schema. -/
theorem recursorSchema_rule (b s n : TTerm ν) :
    TStep ((recursorSchema ν).recur b s ((recursorSchema ν).succ n))
      ((recursorSchema ν).wrap3 s n ((recursorSchema ν).recur b s n)) :=
  TStep.recSucc b s n

/-- Every two-place schema is the three-place schema whose wrapper ignores the counter. -/
def counterBlind (S : StepDuplicatingSchema) : CounterWrapSchema where
  T := S.T
  base := S.base
  succ := S.succ
  wrap3 := fun s _ y => S.wrap s y
  recur := S.recur

/-- The duplicating rule instance of a counter-blind schema is the two-place rule instance. -/
theorem counterBlind_rule (S : StepDuplicatingSchema) (b s n : S.T) :
    (counterBlind S).wrap3 s n ((counterBlind S).recur b s n) = S.wrap s (S.recur b s n) := rfl

/-- Integer wrapper cost of a three-place wrapper at one rule instance. -/
def wrapperCost3Z (S : CounterWrapSchema) (M : S.T → Nat) (b s n : S.T) : Int :=
  (M (S.wrap3 s n (S.recur b s n)) : Int) - (M (S.recur b s n) : Int)

/-- Integer counter gain at one rule instance of a three-place schema. -/
def counterGain3Z (S : CounterWrapSchema) (M : S.T → Nat) (b s n : S.T) : Int :=
  (M (S.recur b s (S.succ n)) : Int) - (M (S.recur b s n) : Int)

/-- The exact criterion for three-place wrappers. -/
theorem orients3_all_iff (S : CounterWrapSchema) (M : S.T → Nat) :
    (∀ b s n : S.T, M (S.wrap3 s n (S.recur b s n)) < M (S.recur b s (S.succ n))) ↔
      ∀ b s n : S.T, wrapperCost3Z S M b s n < counterGain3Z S M b s n := by
  constructor
  · intro h b s n
    have := h b s n
    simp only [wrapperCost3Z, counterGain3Z]
    omega
  · intro h b s n
    have := h b s n
    simp only [wrapperCost3Z, counterGain3Z] at this
    omega

/-- The coupling inequality for three-place wrappers: retention of the step argument, the counter
and the recursive value forces the gain above all three retained quantities. -/
theorem retained_wrapper3_forces_counter_coupled_gain (S : CounterWrapSchema) (M : S.T → Nat)
    (c_w : Nat) (hretain : ∀ x m y : S.T, c_w + M x + M m + M y ≤ M (S.wrap3 x m y))
    (horient : ∀ b s n : S.T, M (S.wrap3 s n (S.recur b s n)) < M (S.recur b s (S.succ n))) :
    ∀ b s n : S.T, (M s : Int) + (M n : Int) + (c_w : Int) < counterGain3Z S M b s n := by
  intro b s n
  have hr := hretain s n (S.recur b s n)
  have ho := horient b s n
  simp only [counterGain3Z]
  omega

/-- The counter-direction barrier: with retention and unbounded counter values, no gain bounded
independently of the counter orients the rule. -/
theorem no_orientation3_of_counter_bounded_gain (S : CounterWrapSchema) (M : S.T → Nat)
    (c_w : Nat) (G : S.T → S.T → Nat)
    (hretain : ∀ x m y : S.T, c_w + M x + M m + M y ≤ M (S.wrap3 x m y))
    (hgain : ∀ b s n : S.T, M (S.recur b s (S.succ n)) ≤ M (S.recur b s n) + G b s)
    (hunbounded : ∀ K : Nat, ∃ n : S.T, K ≤ M n) :
    ¬ ∀ b s n : S.T, M (S.wrap3 s n (S.recur b s n)) < M (S.recur b s (S.succ n)) := by
  intro horient
  obtain ⟨n, hn⟩ := hunbounded (G S.base S.base + 1)
  have hc := retained_wrapper3_forces_counter_coupled_gain S M c_w hretain horient S.base S.base n
  have hg := hgain S.base S.base n
  simp only [counterGain3Z] at hc
  omega

/-- The payload-direction barrier for three-place wrappers. -/
theorem no_orientation3_of_payload_bounded_gain (S : CounterWrapSchema) (M : S.T → Nat)
    (c_w g : Nat)
    (hretain : ∀ x m y : S.T, c_w + M x + M m + M y ≤ M (S.wrap3 x m y))
    (hgain : ∀ b s n : S.T, M (S.recur b s (S.succ n)) ≤ M (S.recur b s n) + g)
    (hunbounded : ∀ K : Nat, ∃ s : S.T, K ≤ M s) :
    ¬ ∀ b s n : S.T, M (S.wrap3 s n (S.recur b s n)) < M (S.recur b s (S.succ n)) := by
  intro horient
  obtain ⟨s, hs⟩ := hunbounded (g + 1)
  have hc := retained_wrapper3_forces_counter_coupled_gain S M c_w hretain horient S.base s S.base
  have hg := hgain S.base s S.base
  simp only [counterGain3Z] at hc
  omega

/-! ## Polynomial escapes on System T -/

/-- The free schema's polynomial escape read on System T: application `f + a + 1`, successor
`t + 1`, and both `It` and `R` read as `(n + 1)(s + b + 2)`. -/
def schemaWeight : TTerm ν → Nat
  | .fvar _ => 1
  | .bvar _ => 1
  | .zero => 1
  | .succ t => schemaWeight t + 1
  | .app f a => schemaWeight f + schemaWeight a + 1
  | .lam t => schemaWeight t + 1
  | .iter b s n => (schemaWeight n + 1) * (schemaWeight s + schemaWeight b + 2)
  | .recR b s n => (schemaWeight n + 1) * (schemaWeight s + schemaWeight b + 2)

/-- The schema's escape orients every iterator rule instance. -/
theorem schemaWeight_orients_iterator (b s n : TTerm ν) :
    schemaWeight (.app s (.iter b s n)) < schemaWeight (.iter b s (.succ n)) := by
  simp only [schemaWeight]
  nlinarith

/-- On the recursor rule the schema's escape decreases exactly when the counter weighs less than
the base. -/
theorem schemaWeight_recursor_iff (b s n : TTerm ν) :
    schemaWeight (.app (.app s n) (.recR b s n)) < schemaWeight (.recR b s (.succ n)) ↔
      schemaWeight n < schemaWeight b := by
  simp only [schemaWeight]
  constructor <;> intro h <;> nlinarith

/-- The numeral `S^k 0`, of schema weight `k + 1`. -/
def numeral : Nat → TTerm ν
  | 0 => .zero
  | k + 1 => .succ (numeral k)

theorem schemaWeight_numeral (k : Nat) : schemaWeight (numeral (ν := ν) k) = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [numeral, schemaWeight, ih]

/-- The counter-direction barrier excludes the schema's escape on the recursor rule: its gain
`s + b + 2` is bounded independently of the counter. -/
theorem schemaWeight_not_orients_recursor :
    ¬ ∀ b s n : TTerm ν,
      schemaWeight (.app (.app s n) (.recR b s n)) < schemaWeight (.recR b s (.succ n)) := by
  have h := no_orientation3_of_counter_bounded_gain (recursorSchema ν) schemaWeight 2
    (fun b s => schemaWeight s + schemaWeight b + 2)
    (fun x m y => by simp only [recursorSchema, schemaWeight]; omega)
    (fun b s n => by simp only [recursorSchema, schemaWeight]; nlinarith)
    (fun K => ⟨numeral K, by rw [schemaWeight_numeral]; omega⟩)
  exact h

/-- The recursor escape: the schema polynomial with the squared counter added to `R`. -/
def tWeight : TTerm ν → Nat
  | .fvar _ => 1
  | .bvar _ => 1
  | .zero => 1
  | .succ t => tWeight t + 1
  | .app f a => tWeight f + tWeight a + 1
  | .lam t => tWeight t + 1
  | .iter b s n => (tWeight n + 1) * (tWeight s + tWeight b + 2)
  | .recR b s n => (tWeight n + 1) * (tWeight s + tWeight b + 2) + tWeight n * tWeight n

/-- The recursor escape orients every recursor rule instance. -/
theorem tWeight_orients_recursor (b s n : TTerm ν) :
    tWeight (.app (.app s n) (.recR b s n)) < tWeight (.recR b s (.succ n)) := by
  simp only [tWeight]
  nlinarith

/-- The recursor escape retains the three wrapper arguments at cost two, and its gain grows with
the counter. -/
theorem tWeight_retains3_and_gain (b s n : TTerm ν) :
    (∀ x m y : TTerm ν, 2 + tWeight x + tWeight m + tWeight y ≤
      tWeight ((recursorSchema ν).wrap3 x m y)) ∧
      counterGain3Z (recursorSchema ν) tWeight b s n =
        (tWeight s : Int) + (tWeight b : Int) + 2 * (tWeight n : Int) + 3 := by
  refine ⟨fun x m y => by simp only [recursorSchema, tWeight]; omega, ?_⟩
  simp only [counterGain3Z, recursorSchema, tWeight]
  push_cast
  ring

/-- System T terms without abstraction. -/
inductive LamFree : TTerm ν → Prop
  | fvar (x : ν) : LamFree (.fvar x)
  | bvar (i : Nat) : LamFree (.bvar i)
  | zero : LamFree .zero
  | succ {t : TTerm ν} : LamFree t → LamFree (.succ t)
  | app {f a : TTerm ν} : LamFree f → LamFree a → LamFree (.app f a)
  | iter {b s n : TTerm ν} : LamFree b → LamFree s → LamFree n → LamFree (.iter b s n)
  | recR {b s n : TTerm ν} : LamFree b → LamFree s → LamFree n → LamFree (.recR b s n)

/-- Every System T step from an abstraction-free term stays abstraction free and decreases the
recursor escape. -/
theorem lamFree_step {t u : TTerm ν} (h : TStep t u) :
    LamFree t → LamFree u ∧ tWeight u < tWeight t := by
  induction h with
  | beta t u =>
      intro ht
      cases ht with
      | app hf _ => cases hf
  | itZero b s =>
      intro ht
      cases ht with
      | iter hb _ _ => exact ⟨hb, by simp only [tWeight]; nlinarith⟩
  | itSucc b s n =>
      intro ht
      cases ht with
      | iter hb hs hn =>
          cases hn with
          | succ hn' => exact ⟨.app hs (.iter hb hs hn'), by simp only [tWeight]; nlinarith⟩
  | recZero b s =>
      intro ht
      cases ht with
      | recR hb _ _ => exact ⟨hb, by simp only [tWeight]; nlinarith⟩
  | recSucc b s n =>
      intro ht
      cases ht with
      | recR hb hs hn =>
          cases hn with
          | succ hn' =>
              exact ⟨.app (.app hs hn') (.recR hb hs hn'), by simp only [tWeight]; nlinarith⟩
  | succ _ ih =>
      intro ht
      cases ht with
      | succ ht' =>
          obtain ⟨hu, hl⟩ := ih ht'
          exact ⟨.succ hu, by simp only [tWeight]; omega⟩
  | appL a _ ih =>
      intro ht
      cases ht with
      | app hf ha =>
          obtain ⟨hu, hl⟩ := ih hf
          exact ⟨.app hu ha, by simp only [tWeight]; omega⟩
  | appR f _ ih =>
      intro ht
      cases ht with
      | app hf ha =>
          obtain ⟨hu, hl⟩ := ih ha
          exact ⟨.app hf hu, by simp only [tWeight]; omega⟩
  | lam _ _ =>
      intro ht
      cases ht
  | itB s n _ ih =>
      intro ht
      cases ht with
      | iter hb hs hn =>
          obtain ⟨hu, hl⟩ := ih hb
          exact ⟨.iter hu hs hn, by simp only [tWeight]; nlinarith⟩
  | itS b n _ ih =>
      intro ht
      cases ht with
      | iter hb hs hn =>
          obtain ⟨hu, hl⟩ := ih hs
          exact ⟨.iter hb hu hn, by simp only [tWeight]; nlinarith⟩
  | itN b s _ ih =>
      intro ht
      cases ht with
      | iter hb hs hn =>
          obtain ⟨hu, hl⟩ := ih hn
          exact ⟨.iter hb hs hu, by simp only [tWeight]; nlinarith⟩
  | recB s n _ ih =>
      intro ht
      cases ht with
      | recR hb hs hn =>
          obtain ⟨hu, hl⟩ := ih hb
          exact ⟨.recR hu hs hn, by simp only [tWeight]; nlinarith⟩
  | recS b n _ ih =>
      intro ht
      cases ht with
      | recR hb hs hn =>
          obtain ⟨hu, hl⟩ := ih hs
          exact ⟨.recR hb hu hn, by simp only [tWeight]; nlinarith⟩
  | recN b s _ ih =>
      intro ht
      cases ht with
      | recR hb hs hn =>
          obtain ⟨hu, hl⟩ := ih hn
          exact ⟨.recR hb hs hu, by simp only [tWeight]; nlinarith⟩

theorem lamFree_acc_aux : ∀ (k : Nat) (t : TTerm ν), tWeight t = k → LamFree t →
    Acc (fun u v : TTerm ν => TStep v u) t := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro t hk ht
    refine Acc.intro t fun u hu => ?_
    obtain ⟨hu', hlt⟩ := lamFree_step hu ht
    exact ih (tWeight u) (hk ▸ hlt) u rfl hu'

/-- Every abstraction-free System T term is strongly normalizing under full System T reduction
with both the iterator and the recursor rules. -/
theorem lamFree_acc {t : TTerm ν} (ht : LamFree t) : Acc (fun u v : TTerm ν => TStep v u) t :=
  lamFree_acc_aux _ t rfl ht

end OperatorKO7.Methods.OrientationClosure.SystemTRecursor
