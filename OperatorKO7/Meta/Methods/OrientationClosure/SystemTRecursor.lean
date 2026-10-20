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
it as instances, the whole four-cell theorem holds on it (`iterImage_four_cells`: coverage, a
strict reversal in the barrier cell, and an orienter and a non-orienter in each other cell, the
last pulled back from the free-schema catalog along the variable-closing morphism and the
isomorphism), and every image term is strongly normalizing under full System T reduction
(`iterFold_acc`, transported from the free contextual termination theorem). Hom-set: a schema
morphism out of the free schema is the fold of its variable assignment (`schemaHom_eq_foldWith`);
the assignment of a beta redex to a variable gives a schema morphism that does not reflect steps
(`betaAssignment_not_reflecting`).

Recursor shape. `R b s (S n) -> s n (R b s n)` duplicates the step and the counter. No two-hole
context realizes it, whatever further free variables it carries and however they are filled
(`no_two_hole_context_realizes_recursor`); the closed two-hole statement
`no_two_hole_wrapper_realizes_recursor` is its instance with no further variable. The three-place
wrapper `app (app s n) y` realizes it (`recursorSchema_rule`). For three-place wrappers the coupling inequality
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

/-! ## The four-cell theorem on the iterator image -/

/-- The verdict content of item (iii) of the four-cell theorem on a schema: each of the three
non-barrier growth cells holds, at some base and counter pair, a measure that orients the
duplicating rule and a measure that fails to orient it.

Proves: (structure) six existential fields, one per non-barrier cell and verdict.
Does not prove: a statement about the barrier cell; `iterImage_four_cells` adds coverage and the
strict reversal in the barrier cell.
Relation: the duplicating rule of the schema, one instance per triple `b s n`.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: an arbitrary step-duplicating schema `S`. -/
structure NonBarrierCellVerdicts (S : StepDuplicatingSchema) : Prop where
  boundedBoundedOrienter : ∃ (M : S.T → Nat) (b n : S.T),
    WrapBoundedAt (S := S) M b n ∧ GainBoundedAt (S := S) M b n ∧
      ∀ b s n : S.T, M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n))
  boundedBoundedNonorienter : ∃ (M : S.T → Nat) (b n : S.T),
    WrapBoundedAt (S := S) M b n ∧ GainBoundedAt (S := S) M b n ∧
      ¬ ∀ b s n : S.T, M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n))
  unboundedUnboundedOrienter : ∃ (M : S.T → Nat) (b n : S.T),
    WrapUnboundedAt (S := S) M b n ∧ GainUnboundedAt (S := S) M b n ∧
      ∀ b s n : S.T, M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n))
  unboundedUnboundedNonorienter : ∃ (M : S.T → Nat) (b n : S.T),
    WrapUnboundedAt (S := S) M b n ∧ GainUnboundedAt (S := S) M b n ∧
      ¬ ∀ b s n : S.T, M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n))
  boundedUnboundedOrienter : ∃ (M : S.T → Nat) (b n : S.T),
    WrapBoundedAt (S := S) M b n ∧ GainUnboundedAt (S := S) M b n ∧
      ∀ b s n : S.T, M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n))
  boundedUnboundedNonorienter : ∃ (M : S.T → Nat) (b n : S.T),
    WrapBoundedAt (S := S) M b n ∧ GainUnboundedAt (S := S) M b n ∧
      ¬ ∀ b s n : S.T, M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n))

namespace SchemaHom

variable {S S' : StepDuplicatingSchema}

/-- A bounded wrapper margin pulls back along a schema morphism.

Proves: `WrapBoundedAt M (h.map b) (h.map n) → WrapBoundedAt (M ∘ h.map) b n`.
Does not prove: the converse.
Relation: the duplicating rule of the two schemas.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: every schema morphism `h`, measure `M` and pair `b n`. -/
theorem wrapBoundedAt_pullback (h : SchemaHom S S') {M : S'.T → Nat} {b n : S.T}
    (hw : WrapBoundedAt (S := S') M (h.map b) (h.map n)) :
    WrapBoundedAt (S := S) (fun t => M (h.map t)) b n := by
  obtain ⟨K, hK⟩ := hw
  refine ⟨K, fun s => ?_⟩
  have e₁ : h.map (S.wrap s (S.recur b s n)) =
      S'.wrap (h.map s) (S'.recur (h.map b) (h.map s) (h.map n)) := by
    rw [h.map_wrap, h.map_recur]
  have e₂ : h.map (S.recur b s n) = S'.recur (h.map b) (h.map s) (h.map n) := h.map_recur b s n
  show M (h.map (S.wrap s (S.recur b s n))) ≤ M (h.map (S.recur b s n)) + K
  rw [e₁, e₂]
  exact hK (h.map s)

/-- A bounded counter gain pulls back along a schema morphism.

Proves: `GainBoundedAt M (h.map b) (h.map n) → GainBoundedAt (M ∘ h.map) b n`.
Does not prove: the converse.
Relation: the duplicating rule of the two schemas.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: every schema morphism `h`, measure `M` and pair `b n`. -/
theorem gainBoundedAt_pullback (h : SchemaHom S S') {M : S'.T → Nat} {b n : S.T}
    (hg : GainBoundedAt (S := S') M (h.map b) (h.map n)) :
    GainBoundedAt (S := S) (fun t => M (h.map t)) b n := by
  obtain ⟨K, hK⟩ := hg
  refine ⟨K, fun s => ?_⟩
  have e₁ : h.map (S.recur b s (S.succ n)) =
      S'.recur (h.map b) (h.map s) (S'.succ (h.map n)) := by
    rw [h.map_recur, h.map_succ]
  have e₂ : h.map (S.recur b s n) = S'.recur (h.map b) (h.map s) (h.map n) := h.map_recur b s n
  show M (h.map (S.recur b s (S.succ n))) ≤ M (h.map (S.recur b s n)) + K
  rw [e₁, e₂]
  exact hK (h.map s)

/-- An unbounded wrapper margin pulls back along a surjective schema morphism.

Proves: for surjective `h.map`, `WrapUnboundedAt M (h.map b) (h.map n) →
WrapUnboundedAt (M ∘ h.map) b n`.
Does not prove: the statement without surjectivity.
Relation: the duplicating rule of the two schemas.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: every surjective schema morphism `h`, measure `M` and pair `b n`. -/
theorem wrapUnboundedAt_pullback (h : SchemaHom S S') (hsurj : Function.Surjective h.map)
    {M : S'.T → Nat} {b n : S.T} (hw : WrapUnboundedAt (S := S') M (h.map b) (h.map n)) :
    WrapUnboundedAt (S := S) (fun t => M (h.map t)) b n := by
  intro K
  obtain ⟨s', hs'⟩ := hw K
  obtain ⟨s, rfl⟩ := hsurj s'
  refine ⟨s, ?_⟩
  have e₁ : h.map (S.wrap s (S.recur b s n)) =
      S'.wrap (h.map s) (S'.recur (h.map b) (h.map s) (h.map n)) := by
    rw [h.map_wrap, h.map_recur]
  have e₂ : h.map (S.recur b s n) = S'.recur (h.map b) (h.map s) (h.map n) := h.map_recur b s n
  show M (h.map (S.recur b s n)) + K < M (h.map (S.wrap s (S.recur b s n)))
  rw [e₁, e₂]
  exact hs'

/-- An unbounded counter gain pulls back along a surjective schema morphism.

Proves: for surjective `h.map`, `GainUnboundedAt M (h.map b) (h.map n) →
GainUnboundedAt (M ∘ h.map) b n`.
Does not prove: the statement without surjectivity.
Relation: the duplicating rule of the two schemas.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: every surjective schema morphism `h`, measure `M` and pair `b n`. -/
theorem gainUnboundedAt_pullback (h : SchemaHom S S') (hsurj : Function.Surjective h.map)
    {M : S'.T → Nat} {b n : S.T} (hg : GainUnboundedAt (S := S') M (h.map b) (h.map n)) :
    GainUnboundedAt (S := S) (fun t => M (h.map t)) b n := by
  intro K
  obtain ⟨s', hs'⟩ := hg K
  obtain ⟨s, rfl⟩ := hsurj s'
  refine ⟨s, ?_⟩
  have e₁ : h.map (S.recur b s (S.succ n)) =
      S'.recur (h.map b) (h.map s) (S'.succ (h.map n)) := by
    rw [h.map_recur, h.map_succ]
  have e₂ : h.map (S.recur b s n) = S'.recur (h.map b) (h.map s) (h.map n) := h.map_recur b s n
  show M (h.map (S.recur b s n)) + K < M (h.map (S.recur b s (S.succ n)))
  rw [e₁, e₂]
  exact hs'

/-- Orientation of the duplicating rule pulls back along a schema morphism.

Proves: if `M` orients every duplicating instance of `S'`, then `M ∘ h.map` orients every
duplicating instance of `S`.
Does not prove: the converse; `not_orients_pullback` gives the converse for surjective maps.
Relation: the duplicating rule of the two schemas.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: every schema morphism `h` and measure `M`. -/
theorem orients_pullback (h : SchemaHom S S') {M : S'.T → Nat}
    (ho : ∀ b s n : S'.T, M (S'.wrap s (S'.recur b s n)) < M (S'.recur b s (S'.succ n))) :
    ∀ b s n : S.T, M (h.map (S.wrap s (S.recur b s n))) < M (h.map (S.recur b s (S.succ n))) := by
  intro b s n
  have e₁ : h.map (S.wrap s (S.recur b s n)) =
      S'.wrap (h.map s) (S'.recur (h.map b) (h.map s) (h.map n)) := by
    rw [h.map_wrap, h.map_recur]
  have e₂ : h.map (S.recur b s (S.succ n)) =
      S'.recur (h.map b) (h.map s) (S'.succ (h.map n)) := by
    rw [h.map_recur, h.map_succ]
  rw [e₁, e₂]
  exact ho (h.map b) (h.map s) (h.map n)

/-- Failure of orientation pulls back along a surjective schema morphism.

Proves: for surjective `h.map`, if `M` fails to orient the duplicating rule of `S'`, then
`M ∘ h.map` fails to orient the duplicating rule of `S`.
Does not prove: the statement without surjectivity.
Relation: the duplicating rule of the two schemas.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: every surjective schema morphism `h` and measure `M`. -/
theorem not_orients_pullback (h : SchemaHom S S') (hsurj : Function.Surjective h.map)
    {M : S'.T → Nat}
    (hno : ¬ ∀ b s n : S'.T, M (S'.wrap s (S'.recur b s n)) < M (S'.recur b s (S'.succ n))) :
    ¬ ∀ b s n : S.T,
      M (h.map (S.wrap s (S.recur b s n))) < M (h.map (S.recur b s (S.succ n))) := by
  intro ho
  apply hno
  intro b' s' n'
  obtain ⟨b, rfl⟩ := hsurj b'
  obtain ⟨s, rfl⟩ := hsurj s'
  obtain ⟨n, rfl⟩ := hsurj n'
  have e₁ : h.map (S.wrap s (S.recur b s n)) =
      S'.wrap (h.map s) (S'.recur (h.map b) (h.map s) (h.map n)) := by
    rw [h.map_wrap, h.map_recur]
  have e₂ : h.map (S.recur b s (S.succ n)) =
      S'.recur (h.map b) (h.map s) (S'.succ (h.map n)) := by
    rw [h.map_recur, h.map_succ]
  have := ho b s n
  rw [e₁, e₂] at this
  exact this

end SchemaHom

/-- The six non-barrier verdicts pull back along a surjective schema morphism.

Proves: `NonBarrierCellVerdicts S' → NonBarrierCellVerdicts S` for every schema morphism
`h : SchemaHom S S'` with surjective map; the witnesses are the composites `M ∘ h.map` at preimages
of the witness pairs.
Does not prove: the statement without surjectivity.
Relation: the duplicating rule of the two schemas.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: every pair of step-duplicating schemas. -/
theorem NonBarrierCellVerdicts.pullback {S S' : StepDuplicatingSchema} (h : SchemaHom S S')
    (hsurj : Function.Surjective h.map) (V : NonBarrierCellVerdicts S') :
    NonBarrierCellVerdicts S where
  boundedBoundedOrienter := by
    obtain ⟨M, b', n', hw, hg, ho⟩ := V.boundedBoundedOrienter
    obtain ⟨b, rfl⟩ := hsurj b'
    obtain ⟨n, rfl⟩ := hsurj n'
    exact ⟨fun t => M (h.map t), b, n, h.wrapBoundedAt_pullback hw, h.gainBoundedAt_pullback hg,
      h.orients_pullback ho⟩
  boundedBoundedNonorienter := by
    obtain ⟨M, b', n', hw, hg, ho⟩ := V.boundedBoundedNonorienter
    obtain ⟨b, rfl⟩ := hsurj b'
    obtain ⟨n, rfl⟩ := hsurj n'
    exact ⟨fun t => M (h.map t), b, n, h.wrapBoundedAt_pullback hw, h.gainBoundedAt_pullback hg,
      h.not_orients_pullback hsurj ho⟩
  unboundedUnboundedOrienter := by
    obtain ⟨M, b', n', hw, hg, ho⟩ := V.unboundedUnboundedOrienter
    obtain ⟨b, rfl⟩ := hsurj b'
    obtain ⟨n, rfl⟩ := hsurj n'
    exact ⟨fun t => M (h.map t), b, n, h.wrapUnboundedAt_pullback hsurj hw,
      h.gainUnboundedAt_pullback hsurj hg, h.orients_pullback ho⟩
  unboundedUnboundedNonorienter := by
    obtain ⟨M, b', n', hw, hg, ho⟩ := V.unboundedUnboundedNonorienter
    obtain ⟨b, rfl⟩ := hsurj b'
    obtain ⟨n, rfl⟩ := hsurj n'
    exact ⟨fun t => M (h.map t), b, n, h.wrapUnboundedAt_pullback hsurj hw,
      h.gainUnboundedAt_pullback hsurj hg, h.not_orients_pullback hsurj ho⟩
  boundedUnboundedOrienter := by
    obtain ⟨M, b', n', hw, hg, ho⟩ := V.boundedUnboundedOrienter
    obtain ⟨b, rfl⟩ := hsurj b'
    obtain ⟨n, rfl⟩ := hsurj n'
    exact ⟨fun t => M (h.map t), b, n, h.wrapBoundedAt_pullback hw,
      h.gainUnboundedAt_pullback hsurj hg, h.orients_pullback ho⟩
  boundedUnboundedNonorienter := by
    obtain ⟨M, b', n', hw, hg, ho⟩ := V.boundedUnboundedNonorienter
    obtain ⟨b, rfl⟩ := hsurj b'
    obtain ⟨n, rfl⟩ := hsurj n'
    exact ⟨fun t => M (h.map t), b, n, h.wrapBoundedAt_pullback hw,
      h.gainUnboundedAt_pullback hsurj hg, h.not_orients_pullback hsurj ho⟩

/-- The six-witness catalog of `CellClassification` as verdicts on the closed free schema.

Proves: `NonBarrierCellVerdicts (freeSchema Empty)`, with the six named measures of
`nonbarrier_cells_have_both_verdicts` as witnesses.
Does not prove: a statement at another schema; the pullbacks below transport it.
Relation: the free duplicating root rule.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: closed free terms. -/
theorem freeSchema_empty_nonBarrierCellVerdicts : NonBarrierCellVerdicts (freeSchema Empty) where
  boundedBoundedOrienter :=
    ⟨AblationComparisons.counterRank, FreeTerm.zero, FreeTerm.zero,
      nonbarrier_cells_have_both_verdicts.boundedBoundedOrienter⟩
  boundedBoundedNonorienter :=
    ⟨zeroMeasure (ν := Empty), FreeTerm.zero, FreeTerm.zero,
      nonbarrier_cells_have_both_verdicts.boundedBoundedNonorienter⟩
  unboundedUnboundedOrienter :=
    ⟨coupledClosedMeasure, FreeTerm.zero, FreeTerm.zero,
      nonbarrier_cells_have_both_verdicts.unboundedUnboundedOrienter⟩
  unboundedUnboundedNonorienter :=
    ⟨doubledWrapperMeasure, FreeTerm.zero, FreeTerm.zero,
      nonbarrier_cells_have_both_verdicts.unboundedUnboundedNonorienter⟩
  boundedUnboundedOrienter :=
    ⟨boundedWrapperMeasure, FreeTerm.zero, FreeTerm.zero,
      nonbarrier_cells_have_both_verdicts.boundedUnboundedOrienter⟩
  boundedUnboundedNonorienter :=
    ⟨alternatingGainMeasure, FreeTerm.zero, FreeTerm.succ FreeTerm.zero,
      nonbarrier_cells_have_both_verdicts.boundedUnboundedNonorienter⟩

/-- The schema morphism that closes a free term by replacing every variable with `zero`.

Proves: (definition) `map = FreeTerm.subst (fun _ => zero)`, which commutes with `base`, `succ`,
`wrap` and `recur` by `rfl`.
Does not prove: injectivity (two variables close to the same term).
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
def closeVarsHom (ν : Type) : SchemaHom (freeSchema ν) (freeSchema Empty) where
  map := FreeTerm.subst (fun _ => (FreeTerm.zero : FreeTerm Empty))
  map_base := rfl
  map_succ _ := rfl
  map_wrap _ _ := rfl
  map_recur _ _ _ := rfl

/-- The closing morphism is surjective: every closed free term is its own image.

Proves: `Function.Surjective (closeVarsHom ν).map`.
Does not prove: injectivity.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`, the empty type included. -/
theorem closeVarsHom_surjective (ν : Type) : Function.Surjective (closeVarsHom ν).map := by
  show ∀ t : FreeTerm Empty, ∃ a : FreeTerm ν, (closeVarsHom ν).map a = t
  intro t
  induction t with
  | var x => exact x.elim
  | zero => exact ⟨FreeTerm.zero, rfl⟩
  | succ t ih =>
    obtain ⟨t', ht'⟩ := ih
    exact ⟨FreeTerm.succ t', by subst ht'; rfl⟩
  | wrap s t ihs iht =>
    obtain ⟨s', hs'⟩ := ihs
    obtain ⟨t', ht'⟩ := iht
    exact ⟨FreeTerm.wrap s' t', by subst hs'; subst ht'; rfl⟩
  | recur b s n ihb ihs ihn =>
    obtain ⟨b', hb'⟩ := ihb
    obtain ⟨s', hs'⟩ := ihs
    obtain ⟨n', hn'⟩ := ihn
    exact ⟨FreeTerm.recur b' s' n', by subst hb'; subst hs'; subst hn'; rfl⟩

/-- Item (iii) of the four-cell theorem on the free schema at every variable type.

Proves: `NonBarrierCellVerdicts (freeSchema ν)`, by pulling the closed catalog back along
`closeVarsHom ν`.
Does not prove: a statement about the barrier cell.
Relation: the free duplicating root rule.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem freeSchema_nonBarrierCellVerdicts (ν : Type) : NonBarrierCellVerdicts (freeSchema ν) :=
  freeSchema_empty_nonBarrierCellVerdicts.pullback (closeVarsHom ν) (closeVarsHom_surjective ν)

/-- The inverse of a schema isomorphism as a schema morphism.

Proves: (definition) `map = e.toEquiv.symm`, with the four commutation laws from those of `e`.
Does not prove: anything beyond the four laws.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every schema isomorphism `e`. -/
def schemaIsoSymmHom {S S' : StepDuplicatingSchema} (e : SchemaIso S S') : SchemaHom S' S where
  map := e.toEquiv.symm
  map_base := by rw [Equiv.symm_apply_eq, e.map_base]
  map_succ t := by rw [Equiv.symm_apply_eq, e.map_succ, Equiv.apply_symm_apply]
  map_wrap x y := by
    rw [Equiv.symm_apply_eq, e.map_wrap, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  map_recur b s n := by
    rw [Equiv.symm_apply_eq, e.map_recur, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]

/-- Item (iii) of the four-cell theorem on the System T iterator image: each of the three
non-barrier cells holds an orienting and a non-orienting measure.

Proves: `NonBarrierCellVerdicts (iterImageSchema ν)`, by pulling the free-schema verdicts back
along the inverse of `iterImageIso ν`.
Does not prove: a statement about terms outside the image (abstraction, bound variables, `R`).
Relation: the iterator rule `It b s (S n) → s (It b s n)` on the image.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem iterImage_nonbarrier_cells_have_both_verdicts (ν : Type) :
    NonBarrierCellVerdicts (iterImageSchema ν) :=
  (freeSchema_nonBarrierCellVerdicts ν).pullback (schemaIsoSymmHom (iterImageIso ν))
    (iterImageIso ν).toEquiv.symm.surjective

/-- The four-cell theorem on the System T iterator image: every measure lies in one of the four
growth cells at every pair, a measure in the barrier cell has a payload at which the right side
strictly exceeds the left side, and each other cell holds an orienter and a non-orienter.

Proves: the conjunction of coverage, the strict reversal in the barrier cell, and
`NonBarrierCellVerdicts (iterImageSchema ν)`.
Does not prove: a statement about terms outside the image.
Relation: the iterator rule on the image.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`, every measure and every pair. -/
theorem iterImage_four_cells (ν : Type) :
    (∀ (M : (iterImageSchema ν).T → Nat) (b n : (iterImageSchema ν).T),
      (WrapUnboundedAt (S := iterImageSchema ν) M b n ∧
          GainBoundedAt (S := iterImageSchema ν) M b n) ∨
        (WrapUnboundedAt (S := iterImageSchema ν) M b n ∧
          GainUnboundedAt (S := iterImageSchema ν) M b n) ∨
        (WrapBoundedAt (S := iterImageSchema ν) M b n ∧
          GainBoundedAt (S := iterImageSchema ν) M b n) ∨
        (WrapBoundedAt (S := iterImageSchema ν) M b n ∧
          GainUnboundedAt (S := iterImageSchema ν) M b n)) ∧
      (∀ (M : (iterImageSchema ν).T → Nat) (b n : (iterImageSchema ν).T),
        WrapUnboundedAt (S := iterImageSchema ν) M b n →
          GainBoundedAt (S := iterImageSchema ν) M b n →
            ∃ s, M ((iterImageSchema ν).recur b s ((iterImageSchema ν).succ n)) <
              M ((iterImageSchema ν).wrap s ((iterImageSchema ν).recur b s n))) ∧
      NonBarrierCellVerdicts (iterImageSchema ν) := by
  refine ⟨fun M b n => four_cell_coverage (S := iterImageSchema ν) M b n,
    fun M b n hw hg => ?_, iterImage_nonbarrier_cells_have_both_verdicts ν⟩
  obtain ⟨K, hK⟩ := hg
  obtain ⟨s, hs⟩ := hw K
  exact ⟨s, lt_of_le_of_lt (hK s) hs⟩

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

/-- Fill a two-hole context that may carry further free variables: the free variable `inl false`
is the step argument, `inl true` the recursive value, and `inr x` is read through a fixed
assignment `ρ`.

Proves: (definition) `fill2With ρ s y` sends `fvar (inl false)` to `s`, `fvar (inl true)` to `y`
and `fvar (inr x)` to `ρ x`, and is structural on every other constructor; each hole may occur any
number of times, including zero.
Does not prove: any realization fact.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every type `κ` of further free variables, every assignment `ρ` and every target variable
type `ν`. -/
def fill2With {κ : Type} (ρ : κ → TTerm ν) (s y : TTerm ν) : TTerm (Bool ⊕ κ) → TTerm ν
  | .fvar (.inl false) => s
  | .fvar (.inl true) => y
  | .fvar (.inr x) => ρ x
  | .bvar i => .bvar i
  | .zero => .zero
  | .succ t => .succ (fill2With ρ s y t)
  | .app f a => .app (fill2With ρ s y f) (fill2With ρ s y a)
  | .lam t => .lam (fill2With ρ s y t)
  | .iter b s' n => .iter (fill2With ρ s y b) (fill2With ρ s y s') (fill2With ρ s y n)
  | .recR b s' n => .recR (fill2With ρ s y b) (fill2With ρ s y s') (fill2With ρ s y n)

/-- The size of a System T term: the number of its constructors.

Proves: (definition) each leaf has size one and each constructor adds one to the sizes of its
arguments.
Does not prove: any reduction fact.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
def tTermSize : TTerm ν → Nat
  | .fvar _ => 1
  | .bvar _ => 1
  | .zero => 1
  | .succ t => tTermSize t + 1
  | .app f a => tTermSize f + tTermSize a + 1
  | .lam t => tTermSize t + 1
  | .iter b s n => tTermSize b + tTermSize s + tTermSize n + 1
  | .recR b s n => tTermSize b + tTermSize s + tTermSize n + 1

/-- A filled context either does not depend on the recursive value or is at least as large as it.

Proves: `(∀ y', fill2With ρ s y' W = fill2With ρ s y W) ∨`
`tTermSize y ≤ tTermSize (fill2With ρ s y W)`.
Does not prove: the disjunct that holds for a given context.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every context `W`, assignment `ρ`, step argument `s` and value `y`. -/
theorem fill2With_indep_or_size_le {κ : Type} (ρ : κ → TTerm ν) (s y : TTerm ν)
    (W : TTerm (Bool ⊕ κ)) :
    (∀ y' : TTerm ν, fill2With ρ s y' W = fill2With ρ s y W) ∨
      tTermSize y ≤ tTermSize (fill2With ρ s y W) := by
  induction W with
  | fvar x =>
    rcases x with c | x
    · cases c
      · exact Or.inl (fun _ => rfl)
      · exact Or.inr le_rfl
    · exact Or.inl (fun _ => rfl)
  | bvar i => exact Or.inl (fun _ => rfl)
  | zero => exact Or.inl (fun _ => rfl)
  | succ t ih =>
    rcases ih with h | h
    · exact Or.inl (fun y' => by simp only [fill2With, h y'])
    · exact Or.inr (by simp only [fill2With, tTermSize]; omega)
  | app f a ihf iha =>
    rcases ihf with hf | hf
    · rcases iha with ha | ha
      · exact Or.inl (fun y' => by simp only [fill2With, hf y', ha y'])
      · exact Or.inr (by simp only [fill2With, tTermSize]; omega)
    · exact Or.inr (by simp only [fill2With, tTermSize]; omega)
  | lam t ih =>
    rcases ih with h | h
    · exact Or.inl (fun y' => by simp only [fill2With, h y'])
    · exact Or.inr (by simp only [fill2With, tTermSize]; omega)
  | iter b s' n ihb ihs ihn =>
    rcases ihb with hb | hb
    · rcases ihs with hs | hs
      · rcases ihn with hn | hn
        · exact Or.inl (fun y' => by simp only [fill2With, hb y', hs y', hn y'])
        · exact Or.inr (by simp only [fill2With, tTermSize]; omega)
      · exact Or.inr (by simp only [fill2With, tTermSize]; omega)
    · exact Or.inr (by simp only [fill2With, tTermSize]; omega)
  | recR b s' n ihb ihs ihn =>
    rcases ihb with hb | hb
    · rcases ihs with hs | hs
      · rcases ihn with hn | hn
        · exact Or.inl (fun y' => by simp only [fill2With, hb y', hs y', hn y'])
        · exact Or.inr (by simp only [fill2With, tTermSize]; omega)
      · exact Or.inr (by simp only [fill2With, tTermSize]; omega)
    · exact Or.inr (by simp only [fill2With, tTermSize]; omega)

/-- No two-hole context realizes the recursor rule, whatever further free variables it carries:
the right side carries the counter outside the recursive call, and a context position that yields
the counter for every counter must contain the recursive-value hole, which makes it larger than
the counter.

Proves: for every type `κ` of further free variables and every assignment `ρ : κ → TTerm ν`, no
`W : TTerm (Bool ⊕ κ)` satisfies `fill2With ρ s (R b s n) W = s n (R b s n)` for all `b s n`.
Does not prove: a statement about three-place wrappers; `recursorSchema_rule` realizes the rule
with one.
Relation: TStep, the recursor rule `R b s (S n) → s n (R b s n)`.
Closure: root (the right side of one rule instance).
Strategy: not applicable.
Trust: kernel-only.
Scope: every target variable type `ν` (the empty type included), every `κ` and every `ρ`; each
hole may occur any number of times. -/
theorem no_two_hole_context_realizes_recursor {κ : Type} (ρ : κ → TTerm ν) :
    ¬ ∃ W : TTerm (Bool ⊕ κ), ∀ b s n : TTerm ν,
      fill2With ρ s (.recR b s n) W = .app (.app s n) (.recR b s n) := by
  rintro ⟨W, hW⟩
  have h₀ := hW .zero .zero .zero
  have h₁ := hW .zero .zero (.succ .zero)
  cases W with
  | app W₁ W₂ =>
    cases W₁ with
    | app V₁ V₂ =>
      have hV : ∀ n : TTerm ν, fill2With ρ .zero (.recR .zero .zero n) V₂ = n := by
        intro n
        have h := hW .zero .zero n
        simp only [fill2With, TTerm.app.injEq] at h
        exact h.1.2
      rcases fill2With_indep_or_size_le ρ .zero (.recR .zero .zero .zero) V₂ with hind | hsz
      · have e := hV (.succ .zero)
        rw [hind, hV .zero] at e
        cases e
      · rw [hV .zero] at hsz
        simp [tTermSize] at hsz
    | fvar x =>
      rcases x with c | x
      · cases c <;> simp [fill2With] at h₀
      · simp only [fill2With, TTerm.app.injEq] at h₀ h₁
        rw [h₀.1] at h₁
        simp at h₁
    | bvar i => simp [fill2With] at h₀
    | zero => simp [fill2With] at h₀
    | succ t => simp [fill2With] at h₀
    | lam t => simp [fill2With] at h₀
    | iter b s n => simp [fill2With] at h₀
    | recR b s n => simp [fill2With] at h₀
  | fvar x =>
    rcases x with c | x
    · cases c <;> simp [fill2With] at h₀
    · simp only [fill2With] at h₀ h₁
      rw [h₀] at h₁
      simp at h₁
  | bvar i => simp [fill2With] at h₀
  | zero => simp [fill2With] at h₀
  | succ t => simp [fill2With] at h₀
  | lam t => simp [fill2With] at h₀
  | iter b s n => simp [fill2With] at h₀
  | recR b s n => simp [fill2With] at h₀

/-- The form of `no_two_hole_context_realizes_recursor` in which the further free variables of the
context are free variables of the target syntax.

Proves: no `W : TTerm (Bool ⊕ ν)` satisfies `fill2With fvar s (R b s n) W = s n (R b s n)` for all
`b s n : TTerm ν`.
Does not prove: a statement about three-place wrappers.
Relation: TStep, the recursor rule.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem no_two_hole_context_with_free_variables_realizes_recursor :
    ¬ ∃ W : TTerm (Bool ⊕ ν), ∀ b s n : TTerm ν,
      fill2With TTerm.fvar s (.recR b s n) W = .app (.app s n) (.recR b s n) :=
  no_two_hole_context_realizes_recursor TTerm.fvar

/-- Read a context over the two holes alone as a context over the holes and further variables.

Proves: (definition) `liftHoles (fvar c) = fvar (inl c)`, structural on every other constructor.
Does not prove: any realization fact.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every type `κ` of further free variables. -/
def liftHoles {κ : Type} : TTerm Bool → TTerm (Bool ⊕ κ)
  | .fvar c => .fvar (.inl c)
  | .bvar i => .bvar i
  | .zero => .zero
  | .succ t => .succ (liftHoles t)
  | .app f a => .app (liftHoles f) (liftHoles a)
  | .lam t => .lam (liftHoles t)
  | .iter b s n => .iter (liftHoles b) (liftHoles s) (liftHoles n)
  | .recR b s n => .recR (liftHoles b) (liftHoles s) (liftHoles n)

/-- Filling a lifted two-hole context is filling the original context.

Proves: `fill2With ρ s y (liftHoles W) = fill2 s y W`.
Does not prove: any realization fact.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `κ`, `ρ`, `s`, `y` and `W`. -/
theorem fill2With_liftHoles {κ : Type} (ρ : κ → TTerm ν) (s y : TTerm ν) (W : TTerm Bool) :
    fill2With ρ s y (liftHoles W) = fill2 s y W := by
  induction W with
  | fvar c => cases c <;> rfl
  | bvar i => rfl
  | zero => rfl
  | succ t ih => simp only [liftHoles, fill2With, fill2, ih]
  | app f a ihf iha => simp only [liftHoles, fill2With, fill2, ihf, iha]
  | lam t ih => simp only [liftHoles, fill2With, fill2, ih]
  | iter b s' n ihb ihs ihn => simp only [liftHoles, fill2With, fill2, ihb, ihs, ihn]
  | recR b s' n ihb ihs ihn => simp only [liftHoles, fill2With, fill2, ihb, ihs, ihn]

/-- No two-hole wrapper context realizes the recursor rule: its right side carries the counter
outside the recursive call.

Proves: no `W : TTerm Bool` satisfies `fill2 s (R b s n) W = s n (R b s n)` for all
`b s n : TTerm Nat`.
Does not prove: the statement for contexts with further free variables;
`no_two_hole_context_realizes_recursor` is the general form, and this theorem is its instance with
no further variable (`κ := Empty`) at natural-number variables.
Relation: TStep, the recursor rule.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: natural-number variables, contexts over the two holes alone. -/
theorem no_two_hole_wrapper_realizes_recursor :
    ¬ ∃ W : TTerm Bool, ∀ b s n : TTerm Nat,
      fill2 s (.recR b s n) W = .app (.app s n) (.recR b s n) := by
  rintro ⟨W, hW⟩
  exact no_two_hole_context_realizes_recursor (κ := Empty) (ν := Nat) Empty.elim
    ⟨liftHoles W, fun b s n => (fill2With_liftHoles Empty.elim s (.recR b s n) W).trans (hW b s n)⟩

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
