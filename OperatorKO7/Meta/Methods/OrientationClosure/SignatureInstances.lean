import OperatorKO7.Meta.Methods.OrientationClosure.SignatureGeneric
import OperatorKO7.Meta.CompositionalMeasure_Impossibility
import Mathlib.Tactic

/-!
# The free schema and KO7 as instances of the signature schema

`SignatureGeneric` states the barrier cell, the coupling inequality and the context lift over every
first-order signature containing the four schema symbols. This module identifies the two named
instances.

A schema isomorphism is a bijection of carriers that commutes with `base`, `succ`, `wrap` and
`recur`; orientation of the duplicating rule transfers along it in both directions
(`SchemaIso.orients_iff`).

The free schema is the signature with no inert symbol (`freeSigIso`). KO7 is the seven-symbol
instance: `void`, `delta`, `app` and `recΔ` are the schema symbols, and `integrate` (arity 1),
`merge` and `eqW` (arity 2) are inert (`ko7SigIso`). Under this isomorphism the two recursor rules
of KO7 are exactly the root rules of the signature schema (`ko7_recursor_rules_iff`), and every such
root step between images is a KO7 step (`step_of_sigRootStep`).
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.SignatureInstances

open OperatorKO7.StepDuplicating
open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.SignatureGeneric
open OperatorKO7.CompositionalImpossibility

/-- A bijection of carriers commuting with the four schema operations. -/
structure SchemaIso (S S' : StepDuplicatingSchema) where
  toEquiv : S.T ≃ S'.T
  map_base : toEquiv S.base = S'.base
  map_succ : ∀ t, toEquiv (S.succ t) = S'.succ (toEquiv t)
  map_wrap : ∀ x y, toEquiv (S.wrap x y) = S'.wrap (toEquiv x) (toEquiv y)
  map_recur : ∀ b s n, toEquiv (S.recur b s n) = S'.recur (toEquiv b) (toEquiv s) (toEquiv n)

/-- Orientation of the duplicating rule transfers along a schema isomorphism. -/
theorem SchemaIso.orients_iff {S S' : StepDuplicatingSchema} (e : SchemaIso S S')
    (M : S'.T → Nat) :
    (∀ b s n : S.T, M (e.toEquiv (S.wrap s (S.recur b s n))) <
        M (e.toEquiv (S.recur b s (S.succ n)))) ↔
      (∀ b s n : S'.T, M (S'.wrap s (S'.recur b s n)) < M (S'.recur b s (S'.succ n))) := by
  constructor
  · intro h b s n
    have := h (e.toEquiv.symm b) (e.toEquiv.symm s) (e.toEquiv.symm n)
    simpa only [e.map_wrap, e.map_recur, e.map_succ, Equiv.apply_symm_apply] using this
  · intro h b s n
    simpa only [e.map_wrap, e.map_recur, e.map_succ] using
      h (e.toEquiv b) (e.toEquiv s) (e.toEquiv n)

/-! ## The free schema is the signature with no inert symbol -/

/-- Read a signature term without inert symbols as a free term. -/
def unembed {ν : Type} : SigTerm Empty Empty.elim ν → FreeTerm ν
  | .var x => .var x
  | .zero => .zero
  | .succ t => .succ (unembed t)
  | .wrap s t => .wrap (unembed s) (unembed t)
  | .recur b s n => .recur (unembed b) (unembed s) (unembed n)
  | .inert f _ => f.elim

theorem unembed_embed {ν : Type} (t : FreeTerm ν) :
    unembed (embed (ι := Empty) (arity := Empty.elim) t) = t := by
  induction t with
  | var x => rfl
  | zero => rfl
  | succ t ih => simp only [embed, unembed, ih]
  | wrap s t ihs iht => simp only [embed, unembed, ihs, iht]
  | recur b s n ihb ihs ihn => simp only [embed, unembed, ihb, ihs, ihn]

theorem embed_unembed {ν : Type} (u : SigTerm Empty Empty.elim ν) : embed (unembed u) = u := by
  induction u with
  | var x => rfl
  | zero => rfl
  | succ t ih => simp only [unembed, embed, ih]
  | wrap s t ihs iht => simp only [unembed, embed, ihs, iht]
  | recur b s n ihb ihs ihn => simp only [unembed, embed, ihb, ihs, ihn]
  | inert f _ _ => exact f.elim

/-- The free schema is the minimal instance: the signature schema with no inert symbol. -/
def freeSigIso (ν : Type) : SchemaIso (freeSchema ν) (sigSchema Empty Empty.elim ν) where
  toEquiv := ⟨embed, unembed, unembed_embed, embed_unembed⟩
  map_base := rfl
  map_succ _ := rfl
  map_wrap _ _ := rfl
  map_recur _ _ _ := rfl

/-! ## KO7 is the seven-symbol instance -/

/-- The three KO7 symbols outside the schema. -/
inductive KO7Inert where
  | integrate
  | merge
  | eqW
  deriving DecidableEq

/-- Their arities. -/
abbrev ko7InertArity : KO7Inert → Nat
  | .integrate => 1
  | .merge => 2
  | .eqW => 2

/-- Ground terms over the KO7 signature. -/
abbrev KO7SigTerm : Type := SigTerm KO7Inert ko7InertArity Empty

/-- KO7 traces as signature terms. -/
def toSig : Trace → KO7SigTerm
  | .void => .zero
  | .delta t => .succ (toSig t)
  | .integrate t => .inert .integrate (fun _ => toSig t)
  | .merge a b => .inert .merge ![toSig a, toSig b]
  | .app a b => .wrap (toSig a) (toSig b)
  | .recΔ b s n => .recur (toSig b) (toSig s) (toSig n)
  | .eqW a b => .inert .eqW ![toSig a, toSig b]

/-- Signature terms as KO7 traces. -/
def ofSig : KO7SigTerm → Trace
  | .var x => x.elim
  | .zero => .void
  | .succ t => .delta (ofSig t)
  | .wrap s t => .app (ofSig s) (ofSig t)
  | .recur b s n => .recΔ (ofSig b) (ofSig s) (ofSig n)
  | .inert .integrate args => .integrate (ofSig (args ⟨0, by decide⟩))
  | .inert .merge args => .merge (ofSig (args ⟨0, by decide⟩)) (ofSig (args ⟨1, by decide⟩))
  | .inert .eqW args => .eqW (ofSig (args ⟨0, by decide⟩)) (ofSig (args ⟨1, by decide⟩))

theorem ofSig_toSig (t : Trace) : ofSig (toSig t) = t := by
  induction t with
  | void => rfl
  | delta t ih => simp only [toSig, ofSig, ih]
  | integrate t ih => simp only [toSig, ofSig, ih]
  | merge a b iha ihb =>
    simp only [toSig, ofSig]
    rw [show (![toSig a, toSig b] : Fin 2 → KO7SigTerm) ⟨0, by decide⟩ = toSig a from rfl,
      show (![toSig a, toSig b] : Fin 2 → KO7SigTerm) ⟨1, by decide⟩ = toSig b from rfl, iha, ihb]
  | app a b iha ihb => simp only [toSig, ofSig, iha, ihb]
  | recΔ b s n ihb ihs ihn => simp only [toSig, ofSig, ihb, ihs, ihn]
  | eqW a b iha ihb =>
    simp only [toSig, ofSig]
    rw [show (![toSig a, toSig b] : Fin 2 → KO7SigTerm) ⟨0, by decide⟩ = toSig a from rfl,
      show (![toSig a, toSig b] : Fin 2 → KO7SigTerm) ⟨1, by decide⟩ = toSig b from rfl, iha, ihb]

theorem fin2_eta {α : Type} (args : Fin 2 → α) :
    (![args ⟨0, by decide⟩, args ⟨1, by decide⟩] : Fin 2 → α) = args := by
  funext i
  fin_cases i <;> rfl

theorem toSig_ofSig (u : KO7SigTerm) : toSig (ofSig u) = u := by
  induction u with
  | var x => exact x.elim
  | zero => rfl
  | succ t ih => simp only [ofSig, toSig, ih]
  | wrap s t ihs iht => simp only [ofSig, toSig, ihs, iht]
  | recur b s n ihb ihs ihn => simp only [ofSig, toSig, ihb, ihs, ihn]
  | inert f args ih =>
    cases f with
    | integrate =>
      simp only [ofSig, toSig, ih]
      congr 1
      funext i
      exact congrArg args (Subsingleton.elim _ _)
    | merge =>
      simp only [ofSig, toSig, ih]
      exact congrArg _ (fin2_eta args)
    | eqW =>
      simp only [ofSig, toSig, ih]
      exact congrArg _ (fin2_eta args)

/-- KO7 is the seven-symbol instance of the signature schema. -/
def ko7SigIso : SchemaIso ko7Schema (sigSchema KO7Inert ko7InertArity Empty) where
  toEquiv := ⟨toSig, ofSig, ofSig_toSig, toSig_ofSig⟩
  map_base := rfl
  map_succ _ := rfl
  map_wrap _ _ := rfl
  map_recur _ _ _ := rfl

/-- Under the isomorphism, the recursor rules of KO7 are exactly the root rules of the signature
schema. -/
theorem ko7_recursor_rules_iff (x y : Trace) :
    ((∃ b s n, x = .recΔ b s (.delta n) ∧ y = .app s (.recΔ b s n)) ∨
        (∃ b s, x = .recΔ b s .void ∧ y = b)) ↔
      SigRootStep (toSig x) (toSig y) := by
  constructor
  · rintro (⟨b, s, n, rfl, rfl⟩ | ⟨b, s, rfl, hy⟩)
    · exact SigRootStep.recurSucc (toSig b) (toSig s) (toSig n)
    · rw [hy]
      exact SigRootStep.recurZero (toSig b) (toSig s)
  · intro h
    have hx := ofSig_toSig x
    have hy := ofSig_toSig y
    generalize toSig x = X at h hx
    generalize toSig y = Y at h hy
    cases h with
    | recurZero =>
      right
      exact ⟨_, _, hx.symm, hy.symm⟩
    | recurSucc =>
      left
      exact ⟨_, _, _, hx.symm, hy.symm⟩

/-- Every root step of the signature schema between images of traces is a KO7 step. -/
theorem step_of_sigRootStep {x y : Trace} (h : SigRootStep (toSig x) (toSig y)) : Step x y := by
  rcases (ko7_recursor_rules_iff x y).2 h with ⟨b, s, n, rfl, rfl⟩ | ⟨b, s, rfl, hy⟩
  · exact Step.R_rec_succ b s n
  · rw [hy]
    exact Step.R_rec_zero b s

/-- Orientation of the KO7 duplicating rule by `M` is orientation of the signature duplicating rule by
`M ∘ ofSig`, so every signature-level orientation theorem is a KO7 theorem. -/
theorem ko7_orients_iff_sig (M : Trace → Nat) :
    (∀ b s n : Trace, M (.app s (.recΔ b s n)) < M (.recΔ b s (.delta n))) ↔
      (∀ b s n : KO7SigTerm,
        M (ofSig (.wrap s (.recur b s n))) < M (ofSig (.recur b s (.succ n)))) := by
  have key := (SchemaIso.orients_iff ko7SigIso (fun u => M (ofSig u)))
  simp only [ko7SigIso, Equiv.coe_fn_mk, ofSig_toSig] at key
  exact key

/-! ## The image of the embedding and the two hom-sets

The image of the free schema in the signature schema is exactly the terms without inert symbols
(`mem_range_embed_iff`). Any two schema isomorphisms agree on the elements generated from `base`
by the four operations (`SchemaIso.eq_on_generated`). At the empty variable type every free term
is generated, so `freeSigIso Empty` is the only isomorphism (`freeSigIso_unique`); a permutation of
the variables that moves one variable gives a second isomorphism (`freeSigIso_not_unique`). The
generated KO7 traces are those without `integrate`, `merge` and `eqW` (`ko7_generated_iff`); there
every isomorphism agrees with `ko7SigIso`, and the exchange of `merge` and `eqW` gives a second
isomorphism (`ko7SigIso_not_unique`). The polynomial decision procedure holds over every signature
as `PolynomialOrientationDecision.sig_decideRootUnit_iff`. -/

/-- Signature terms that use no inert symbol. -/
inductive InertFree {ι : Type} {arity : ι → Nat} {ν : Type} : SigTerm ι arity ν → Prop
  | var (x : ν) : InertFree (.var x)
  | zero : InertFree .zero
  | succ {t : SigTerm ι arity ν} : InertFree t → InertFree (.succ t)
  | wrap {s t : SigTerm ι arity ν} : InertFree s → InertFree t → InertFree (.wrap s t)
  | recur {b s n : SigTerm ι arity ν} : InertFree b → InertFree s → InertFree n →
      InertFree (.recur b s n)

/-- The image of the free schema in the signature schema is exactly the inert-free terms. -/
theorem mem_range_embed_iff {ι : Type} {arity : ι → Nat} {ν : Type} (u : SigTerm ι arity ν) :
    u ∈ Set.range (embed : FreeTerm ν → SigTerm ι arity ν) ↔ InertFree u := by
  constructor
  · rintro ⟨t, rfl⟩
    induction t with
    | var x => exact .var x
    | zero => exact .zero
    | succ t ih => exact .succ ih
    | wrap s t ihs iht => exact .wrap ihs iht
    | recur b s n ihb ihs ihn => exact .recur ihb ihs ihn
  · intro h
    induction h with
    | var x => exact ⟨.var x, rfl⟩
    | zero => exact ⟨.zero, rfl⟩
    | succ _ ih =>
      obtain ⟨t₀, rfl⟩ := ih
      exact ⟨.succ t₀, rfl⟩
    | wrap _ _ ihs iht =>
      obtain ⟨s₀, rfl⟩ := ihs
      obtain ⟨t₀, rfl⟩ := iht
      exact ⟨.wrap s₀ t₀, rfl⟩
    | recur _ _ _ ihb ihs ihn =>
      obtain ⟨b₀, rfl⟩ := ihb
      obtain ⟨s₀, rfl⟩ := ihs
      obtain ⟨n₀, rfl⟩ := ihn
      exact ⟨.recur b₀ s₀ n₀, rfl⟩

/-- Composition of schema isomorphisms. -/
def SchemaIso.trans {S S' S'' : StepDuplicatingSchema} (e : SchemaIso S S')
    (e' : SchemaIso S' S'') : SchemaIso S S'' where
  toEquiv := e.toEquiv.trans e'.toEquiv
  map_base := by simp only [Equiv.trans_apply, e.map_base, e'.map_base]
  map_succ t := by simp only [Equiv.trans_apply, e.map_succ, e'.map_succ]
  map_wrap x y := by simp only [Equiv.trans_apply, e.map_wrap, e'.map_wrap]
  map_recur b s n := by simp only [Equiv.trans_apply, e.map_recur, e'.map_recur]

/-- The elements of a schema generated from `base` by the four operations. -/
inductive SchemaGenerated (S : StepDuplicatingSchema) : S.T → Prop
  | base : SchemaGenerated S S.base
  | succ {t : S.T} : SchemaGenerated S t → SchemaGenerated S (S.succ t)
  | wrap {x y : S.T} : SchemaGenerated S x → SchemaGenerated S y → SchemaGenerated S (S.wrap x y)
  | recur {b s n : S.T} : SchemaGenerated S b → SchemaGenerated S s → SchemaGenerated S n →
      SchemaGenerated S (S.recur b s n)

/-- Any two schema isomorphisms agree on every generated element. -/
theorem SchemaIso.eq_on_generated {S S' : StepDuplicatingSchema} (e e' : SchemaIso S S')
    {t : S.T} (h : SchemaGenerated S t) : e.toEquiv t = e'.toEquiv t := by
  induction h with
  | base => rw [e.map_base, e'.map_base]
  | succ _ ih => rw [e.map_succ, e'.map_succ, ih]
  | wrap _ _ ihx ihy => rw [e.map_wrap, e'.map_wrap, ihx, ihy]
  | recur _ _ _ ihb ihs ihn => rw [e.map_recur, e'.map_recur, ihb, ihs, ihn]

/-- At the empty variable type every free term is generated. -/
theorem free_generated_empty (t : FreeTerm Empty) : SchemaGenerated (freeSchema Empty) t := by
  induction t with
  | var x => exact x.elim
  | zero => exact .base
  | succ t ih => exact .succ ih
  | wrap s t ihs iht => exact .wrap ihs iht
  | recur b s n ihb ihs ihn => exact .recur ihb ihs ihn

/-- At the empty variable type the isomorphism from the free schema to the signature schema
without inert symbols is unique. -/
theorem freeSigIso_unique (e : SchemaIso (freeSchema Empty) (sigSchema Empty Empty.elim Empty)) :
    e.toEquiv = (freeSigIso Empty).toEquiv :=
  Equiv.ext fun t => SchemaIso.eq_on_generated e (freeSigIso Empty) (free_generated_empty t)

/-- Renaming of variables in free terms. -/
def renameVars {ν : Type} (σ : ν → ν) : FreeTerm ν → FreeTerm ν
  | .var x => .var (σ x)
  | .zero => .zero
  | .succ t => .succ (renameVars σ t)
  | .wrap s t => .wrap (renameVars σ s) (renameVars σ t)
  | .recur b s n => .recur (renameVars σ b) (renameVars σ s) (renameVars σ n)

theorem renameVars_renameVars {ν : Type} (σ τ : ν → ν) (h : ∀ x, τ (σ x) = x) (t : FreeTerm ν) :
    renameVars τ (renameVars σ t) = t := by
  induction t with
  | var x => simp only [renameVars, h]
  | zero => rfl
  | succ t ih => simp only [renameVars, ih]
  | wrap s t ihs iht => simp only [renameVars, ihs, iht]
  | recur b s n ihb ihs ihn => simp only [renameVars, ihb, ihs, ihn]

/-- A permutation of the variables is an automorphism of the free schema. -/
def renameIso {ν : Type} (σ : ν ≃ ν) : SchemaIso (freeSchema ν) (freeSchema ν) where
  toEquiv := ⟨renameVars σ, renameVars σ.symm, renameVars_renameVars σ σ.symm σ.symm_apply_apply,
    renameVars_renameVars σ.symm σ σ.apply_symm_apply⟩
  map_base := rfl
  map_succ _ := rfl
  map_wrap _ _ := rfl
  map_recur _ _ _ := rfl

/-- A permutation that moves a variable gives a second isomorphism from the free schema to the
signature schema. -/
theorem freeSigIso_not_unique {ν : Type} (σ : ν ≃ ν) (x : ν) (hx : σ x ≠ x) :
    ((renameIso σ).trans (freeSigIso ν)).toEquiv (.var x) ≠ (freeSigIso ν).toEquiv (.var x) := by
  intro h
  have h' : (SigTerm.var (σ x) : SigTerm Empty Empty.elim ν) = .var x := h
  exact hx (SigTerm.var.inj h')

theorem inertFree_toSig_of_generated {t : ko7Schema.T} (h : SchemaGenerated ko7Schema t) :
    InertFree (toSig t) := by
  induction h with
  | base => exact .zero
  | succ _ ih => exact .succ ih
  | wrap _ _ ihx ihy => exact .wrap ihx ihy
  | recur _ _ _ ihb ihs ihn => exact .recur ihb ihs ihn

/-- The generated KO7 traces are exactly those without `integrate`, `merge` and `eqW`. -/
theorem ko7_generated_iff (t : Trace) : SchemaGenerated ko7Schema t ↔ InertFree (toSig t) := by
  constructor
  · exact inertFree_toSig_of_generated
  · intro h
    induction t with
    | void => exact .base
    | delta t ih =>
      cases h with
      | succ h => exact .succ (ih h)
    | integrate t _ => cases h
    | merge a b _ _ => cases h
    | app a b iha ihb =>
      cases h with
      | wrap ha hb => exact .wrap (iha ha) (ihb hb)
    | recΔ b s n ihb ihs ihn =>
      cases h with
      | recur hb hs hn => exact .recur (ihb hb) (ihs hs) (ihn hn)
    | eqW a b _ _ => cases h

/-- Exchange of the labels `merge` and `eqW`, which have the same arity. -/
def swapInert : KO7SigTerm → KO7SigTerm
  | .var x => x.elim
  | .zero => .zero
  | .succ t => .succ (swapInert t)
  | .wrap s t => .wrap (swapInert s) (swapInert t)
  | .recur b s n => .recur (swapInert b) (swapInert s) (swapInert n)
  | .inert .integrate args => .inert .integrate (fun i => swapInert (args i))
  | .inert .merge args => .inert .eqW (fun i => swapInert (args i))
  | .inert .eqW args => .inert .merge (fun i => swapInert (args i))

theorem swapInert_swapInert (u : KO7SigTerm) : swapInert (swapInert u) = u := by
  induction u with
  | var x => exact x.elim
  | zero => rfl
  | succ t ih => simp only [swapInert, ih]
  | wrap s t ihs iht => simp only [swapInert, ihs, iht]
  | recur b s n ihb ihs ihn => simp only [swapInert, ihb, ihs, ihn]
  | inert f args ih => cases f <;> simp only [swapInert, ih]

/-- The exchange of `merge` and `eqW` is an automorphism of the KO7 signature schema. -/
def swapIso : SchemaIso (sigSchema KO7Inert ko7InertArity Empty)
    (sigSchema KO7Inert ko7InertArity Empty) where
  toEquiv := ⟨swapInert, swapInert, swapInert_swapInert, swapInert_swapInert⟩
  map_base := rfl
  map_succ _ := rfl
  map_wrap _ _ := rfl
  map_recur _ _ _ := rfl

theorem swapInert_moves_merge :
    swapInert (toSig (.merge .void .void)) ≠ toSig (.merge .void .void) := by
  simp [toSig, swapInert]

/-- A second isomorphism from KO7 to its signature schema: it differs from `ko7SigIso` at
`merge void void`. -/
theorem ko7SigIso_not_unique :
    (ko7SigIso.trans swapIso).toEquiv (.merge .void .void) ≠
      ko7SigIso.toEquiv (.merge .void .void) := by
  intro h
  exact swapInert_moves_merge h

end OperatorKO7.Methods.OrientationClosure.SignatureInstances
