import OperatorKO7.Meta.Methods.OrientationClosure.CellClassification
import OperatorKO7.Meta.Methods.OrientationClosure.CouplingTheorem
import OperatorKO7.Meta.Methods.OrientationClosure.FreePolynomialTermination
import Mathlib.Tactic

/-!
# The recursor schema over an arbitrary first-order signature

A signature for the Orientation Boundary has the four schema symbols `zero`, `succ`, `wrap`,
`recur` and any family of inert symbols `f : ι` with arity `arity f`. This module defines terms,
substitution, one-hole contexts and the two root rules over such a signature.

* The free schema of `SchemaCore.lean` embeds injectively. The image is closed under root and
  contextual rewriting: every step out of an embedded term lands on an embedded term, and the
  steps between embedded terms are exactly the embedded free steps.
* The barrier cell of `CellClassification.lean`, its context form, and the coupling inequality
  of `CouplingTheorem.lean` hold for the signature schema, because both theorems are stated for
  every `StepDuplicatingSchema`.
* An interpretation of the four schema symbols extends to the signature by any operation per
  inert symbol. Root orientation does not depend on the extension. With strictly monotone inert
  operations, strict context laws and root orientation give termination of the full contextual
  relation; the coupled polynomial with `1 + sum` on inert symbols proves it for every signature.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.SignatureGeneric

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.InterpretationLaws
open OperatorKO7.Methods.OrientationClosure.CellClassification
open OperatorKO7.Methods.OrientationClosure.CouplingTheorem
open OperatorKO7.Methods.OrientationClosure.FreePolynomialTermination

universe u v w

/-! ## Terms, substitution, contexts and rules -/

/-- Terms over the four schema symbols and inert symbols `f : ι` of arity `arity f`. -/
inductive SigTerm (ι : Type u) (arity : ι → Nat) (ν : Type v) : Type (max u v) where
  | var (x : ν)
  | zero
  | succ (t : SigTerm ι arity ν)
  | wrap (s t : SigTerm ι arity ν)
  | recur (b s n : SigTerm ι arity ν)
  | inert (f : ι) (args : Fin (arity f) → SigTerm ι arity ν)

/-- First-order substitution. -/
def SigTerm.subst {ι : Type u} {arity : ι → Nat} {ν : Type v} {μ : Type w}
    (σ : ν → SigTerm ι arity μ) : SigTerm ι arity ν → SigTerm ι arity μ
  | .var x => σ x
  | .zero => .zero
  | .succ t => .succ (SigTerm.subst σ t)
  | .wrap s t => .wrap (SigTerm.subst σ s) (SigTerm.subst σ t)
  | .recur b s n => .recur (SigTerm.subst σ b) (SigTerm.subst σ s) (SigTerm.subst σ n)
  | .inert f args => .inert f (fun i => SigTerm.subst σ (args i))

/-- One-hole contexts, including every argument position of every inert symbol. -/
inductive SigContext (ι : Type u) (arity : ι → Nat) (ν : Type v) : Type (max u v) where
  | hole
  | succ (C : SigContext ι arity ν)
  | wrapLeft (C : SigContext ι arity ν) (t : SigTerm ι arity ν)
  | wrapRight (s : SigTerm ι arity ν) (C : SigContext ι arity ν)
  | recurBase (C : SigContext ι arity ν) (s n : SigTerm ι arity ν)
  | recurStep (b : SigTerm ι arity ν) (C : SigContext ι arity ν) (n : SigTerm ι arity ν)
  | recurCounter (b s : SigTerm ι arity ν) (C : SigContext ι arity ν)
  | inertAt (f : ι) (i : Fin (arity f)) (args : Fin (arity f) → SigTerm ι arity ν)
      (C : SigContext ι arity ν)

/-- Insert a term into the hole; at an inert position the other arguments are kept. -/
def SigContext.plug {ι : Type u} {arity : ι → Nat} {ν : Type v} :
    SigContext ι arity ν → SigTerm ι arity ν → SigTerm ι arity ν
  | .hole, t => t
  | .succ C, t => .succ (SigContext.plug C t)
  | .wrapLeft C r, t => .wrap (SigContext.plug C t) r
  | .wrapRight l C, t => .wrap l (SigContext.plug C t)
  | .recurBase C s n, t => .recur (SigContext.plug C t) s n
  | .recurStep b C n, t => .recur b (SigContext.plug C t) n
  | .recurCounter b s C, t => .recur b s (SigContext.plug C t)
  | .inertAt f i args C, t => .inert f (Function.update args i (SigContext.plug C t))

/-- The two root rules of the recursor over the signature. -/
inductive SigRootStep {ι : Type u} {arity : ι → Nat} {ν : Type v} :
    SigTerm ι arity ν → SigTerm ι arity ν → Prop where
  | recurZero (b s : SigTerm ι arity ν) : SigRootStep (.recur b s .zero) b
  | recurSucc (b s n : SigTerm ι arity ν) :
      SigRootStep (.recur b s (.succ n)) (.wrap s (.recur b s n))

/-- Constructor-context closure of the root rules over the signature. -/
inductive SigContextStep {ι : Type u} {arity : ι → Nat} {ν : Type v} :
    SigTerm ι arity ν → SigTerm ι arity ν → Prop where
  | lift (C : SigContext ι arity ν) {t u : SigTerm ι arity ν} (h : SigRootStep t u) :
      SigContextStep (C.plug t) (C.plug u)

/-- Root rewriting over the signature is stable under substitution. -/
theorem SigRootStep.subst {ι : Type u} {arity : ι → Nat} {ν : Type v} {μ : Type w}
    {t u : SigTerm ι arity ν} (h : SigRootStep t u) (σ : ν → SigTerm ι arity μ) :
    SigRootStep (SigTerm.subst σ t) (SigTerm.subst σ u) := by
  cases h with
  | recurZero b s => exact .recurZero _ _
  | recurSucc b s n => exact .recurSucc _ _ _

/-- The signature terms as a step-duplicating schema. -/
def sigSchema (κ : Type) (ar : κ → Nat) (ν : Type) :
    OperatorKO7.StepDuplicating.StepDuplicatingSchema where
  T := SigTerm κ ar ν
  base := .zero
  succ := .succ
  wrap := .wrap
  recur := .recur

/-! ## The free schema embeds, with an image closed under both relations -/

/-- The embedding of the free schema, which uses no inert symbol. -/
def embed {ι : Type u} {arity : ι → Nat} {ν : Type v} : FreeTerm ν → SigTerm ι arity ν
  | .var x => .var x
  | .zero => .zero
  | .succ t => .succ (embed t)
  | .wrap s t => .wrap (embed s) (embed t)
  | .recur b s n => .recur (embed b) (embed s) (embed n)

/-- The embedding of free contexts. -/
def embedCtx {ι : Type u} {arity : ι → Nat} {ν : Type v} : FreeContext ν → SigContext ι arity ν
  | .hole => .hole
  | .succ C => .succ (embedCtx C)
  | .wrapLeft C r => .wrapLeft (embedCtx C) (embed r)
  | .wrapRight l C => .wrapRight (embed l) (embedCtx C)
  | .recurBase C s n => .recurBase (embedCtx C) (embed s) (embed n)
  | .recurStep b C n => .recurStep (embed b) (embedCtx C) (embed n)
  | .recurCounter b s C => .recurCounter (embed b) (embed s) (embedCtx C)

theorem embed_eq_zero {ι : Type u} {arity : ι → Nat} {ν : Type v} {t : FreeTerm ν}
    (h : (embed t : SigTerm ι arity ν) = .zero) : t = .zero := by
  cases t <;> simp_all [embed]

theorem embed_eq_succ {ι : Type u} {arity : ι → Nat} {ν : Type v} {t : FreeTerm ν}
    {x : SigTerm ι arity ν} (h : embed t = .succ x) : ∃ m, t = .succ m ∧ x = embed m := by
  cases t <;> simp [embed] at h
  case succ m => exact ⟨m, rfl, h.symm⟩

theorem embed_eq_wrap {ι : Type u} {arity : ι → Nat} {ν : Type v} {t : FreeTerm ν}
    {x y : SigTerm ι arity ν} (h : embed t = .wrap x y) :
    ∃ s₀ t₀, t = .wrap s₀ t₀ ∧ x = embed s₀ ∧ y = embed t₀ := by
  cases t <;> simp [embed] at h
  case wrap s₀ t₀ => exact ⟨s₀, t₀, rfl, h.1.symm, h.2.symm⟩

theorem embed_eq_recur {ι : Type u} {arity : ι → Nat} {ν : Type v} {t : FreeTerm ν}
    {b s n : SigTerm ι arity ν} (h : embed t = .recur b s n) :
    ∃ b₀ s₀ n₀, t = .recur b₀ s₀ n₀ ∧ b = embed b₀ ∧ s = embed s₀ ∧ n = embed n₀ := by
  cases t <;> simp [embed] at h
  case recur b₀ s₀ n₀ => exact ⟨b₀, s₀, n₀, rfl, h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem embed_ne_inert {ι : Type u} {arity : ι → Nat} {ν : Type v} (t : FreeTerm ν) (f : ι)
    (args : Fin (arity f) → SigTerm ι arity ν) : embed t ≠ .inert f args := by
  cases t <;> simp [embed]

/-- The embedding is injective. -/
theorem embed_injective {ι : Type u} {arity : ι → Nat} {ν : Type v} :
    Function.Injective (embed : FreeTerm ν → SigTerm ι arity ν) := by
  intro a b h
  induction a generalizing b with
  | var x =>
      cases b <;> simp [embed] at h
      subst h
      rfl
  | zero => exact (embed_eq_zero h.symm).symm
  | succ t ih =>
      obtain ⟨m, rfl, hm⟩ := embed_eq_succ h.symm
      rw [ih hm]
  | wrap s t ihs iht =>
      obtain ⟨s₀, t₀, rfl, hs, ht⟩ := embed_eq_wrap h.symm
      rw [ihs hs, iht ht]
  | recur b s n ihb ihs ihn =>
      obtain ⟨b₀, s₀, n₀, rfl, hb, hs, hn⟩ := embed_eq_recur h.symm
      rw [ihb hb, ihs hs, ihn hn]

/-- Embedding commutes with plugging. -/
theorem embed_plug {ι : Type u} {arity : ι → Nat} {ν : Type v} (C : FreeContext ν)
    (t : FreeTerm ν) :
    (embed (C.plug t) : SigTerm ι arity ν) = (embedCtx C).plug (embed t) := by
  induction C <;> simp [FreeContext.plug, SigContext.plug, embedCtx, embed, *]

/-- Embedding commutes with substitution. -/
theorem embed_subst {ι : Type u} {arity : ι → Nat} {ν : Type v} {μ : Type v}
    (σ : ν → FreeTerm μ) (t : FreeTerm ν) :
    (embed (FreeTerm.subst σ t) : SigTerm ι arity μ) =
      SigTerm.subst (fun x => embed (σ x)) (embed t) := by
  induction t <;> simp [FreeTerm.subst, SigTerm.subst, embed, *]

/-- Free root steps embed as signature root steps. -/
theorem embed_rootStep {ι : Type u} {arity : ι → Nat} {ν : Type v} {t u : FreeTerm ν}
    (h : RootStep t u) : SigRootStep (embed t : SigTerm ι arity ν) (embed u) := by
  cases h with
  | recurZero b s => exact .recurZero _ _
  | recurSucc b s n => exact .recurSucc _ _ _

/-- Every signature root step out of an embedded term is an embedded free root step. -/
theorem rootStep_of_embed {ι : Type u} {arity : ι → Nat} {ν : Type v} {t : FreeTerm ν}
    {u' : SigTerm ι arity ν} (h : SigRootStep (embed t) u') :
    ∃ u, u' = embed u ∧ RootStep t u := by
  generalize ht : (embed t : SigTerm ι arity ν) = t' at h
  cases h with
  | recurZero b s =>
      obtain ⟨b₀, s₀, n₀, rfl, rfl, rfl, hn⟩ := embed_eq_recur ht
      have hn₀ : n₀ = .zero := embed_eq_zero hn.symm
      subst hn₀
      exact ⟨b₀, rfl, .recurZero _ _⟩
  | recurSucc b s n =>
      obtain ⟨b₀, s₀, n₀, rfl, rfl, rfl, hn⟩ := embed_eq_recur ht
      obtain ⟨m, rfl, rfl⟩ := embed_eq_succ hn.symm
      exact ⟨.wrap s₀ (.recur b₀ s₀ m), rfl, .recurSucc _ _ _⟩

/-- Free contextual steps embed as signature contextual steps. -/
theorem embed_contextStep {ι : Type u} {arity : ι → Nat} {ν : Type v} {t u : FreeTerm ν}
    (h : ContextStep t u) : SigContextStep (embed t : SigTerm ι arity ν) (embed u) := by
  cases h with
  | lift C hroot =>
      rw [embed_plug, embed_plug]
      exact SigContextStep.lift (embedCtx C) (embed_rootStep hroot)

/-- A context whose plug is an embedded term is an embedded context around an embedded term. -/
theorem plug_eq_embed {ι : Type u} {arity : ι → Nat} {ν : Type v}
    {C : SigContext ι arity ν} {a : SigTerm ι arity ν} {t : FreeTerm ν}
    (h : C.plug a = embed t) :
    ∃ C₀ a₀, C = embedCtx C₀ ∧ a = embed a₀ ∧ t = C₀.plug a₀ := by
  induction C generalizing t with
  | hole => exact ⟨.hole, t, rfl, h, rfl⟩
  | succ C ih =>
      obtain ⟨m, rfl, hm⟩ := embed_eq_succ h.symm
      obtain ⟨C₀, a₀, rfl, rfl, rfl⟩ := ih hm
      exact ⟨.succ C₀, a₀, rfl, rfl, rfl⟩
  | wrapLeft C r ih =>
      obtain ⟨s₀, t₀, rfl, hx, rfl⟩ := embed_eq_wrap h.symm
      obtain ⟨C₀, a₀, rfl, rfl, rfl⟩ := ih hx
      exact ⟨.wrapLeft C₀ t₀, a₀, rfl, rfl, rfl⟩
  | wrapRight l C ih =>
      obtain ⟨s₀, t₀, rfl, rfl, hy⟩ := embed_eq_wrap h.symm
      obtain ⟨C₀, a₀, rfl, rfl, rfl⟩ := ih hy
      exact ⟨.wrapRight s₀ C₀, a₀, rfl, rfl, rfl⟩
  | recurBase C s n ih =>
      obtain ⟨b₀, s₀, n₀, rfl, hb, rfl, rfl⟩ := embed_eq_recur h.symm
      obtain ⟨C₀, a₀, rfl, rfl, rfl⟩ := ih hb
      exact ⟨.recurBase C₀ s₀ n₀, a₀, rfl, rfl, rfl⟩
  | recurStep b C n ih =>
      obtain ⟨b₀, s₀, n₀, rfl, rfl, hs, rfl⟩ := embed_eq_recur h.symm
      obtain ⟨C₀, a₀, rfl, rfl, rfl⟩ := ih hs
      exact ⟨.recurStep b₀ C₀ n₀, a₀, rfl, rfl, rfl⟩
  | recurCounter b s C ih =>
      obtain ⟨b₀, s₀, n₀, rfl, rfl, rfl, hn⟩ := embed_eq_recur h.symm
      obtain ⟨C₀, a₀, rfl, rfl, rfl⟩ := ih hn
      exact ⟨.recurCounter b₀ s₀ C₀, a₀, rfl, rfl, rfl⟩
  | inertAt f i args C ih =>
      exact absurd h.symm (embed_ne_inert t f _)

/-- Every signature contextual step out of an embedded term is an embedded free step. -/
theorem contextStep_of_embed {ι : Type u} {arity : ι → Nat} {ν : Type v} {t : FreeTerm ν}
    {u' : SigTerm ι arity ν} (h : SigContextStep (embed t) u') :
    ∃ u, u' = embed u ∧ ContextStep t u := by
  generalize ht : (embed t : SigTerm ι arity ν) = t' at h
  cases h with
  | lift C hroot =>
      obtain ⟨C₀, a₀, rfl, rfl, rfl⟩ := plug_eq_embed ht.symm
      obtain ⟨u₀, rfl, hu⟩ := rootStep_of_embed hroot
      exact ⟨C₀.plug u₀, (embed_plug C₀ u₀).symm, ContextStep.lift C₀ hu⟩

/-- Between embedded terms, the signature contextual steps are exactly the free ones. -/
theorem embed_contextStep_iff {ι : Type u} {arity : ι → Nat} {ν : Type v} (t u : FreeTerm ν) :
    SigContextStep (embed t : SigTerm ι arity ν) (embed u) ↔ ContextStep t u := by
  constructor
  · intro h
    obtain ⟨u₀, hu, hstep⟩ := contextStep_of_embed h
    rw [embed_injective hu]
    exact hstep
  · exact embed_contextStep

/-! ## Transport of the barrier cell and the coupling inequality -/

/-- The barrier cell excludes orientation over every signature. -/
theorem sig_barrier_cell_excludes_orientation {κ : Type} {ar : κ → Nat} {ν : Type}
    (M : SigTerm κ ar ν → Nat) (b n : SigTerm κ ar ν)
    (hw : WrapUnboundedAt (S := sigSchema κ ar ν) M b n)
    (hg : GainBoundedAt (S := sigSchema κ ar ν) M b n) :
    ¬ ∀ s : SigTerm κ ar ν, M (.wrap s (.recur b s n)) < M (.recur b s (.succ n)) :=
  barrier_cell_excludes_orientation (S := sigSchema κ ar ν) M b n hw hg

/-- The barrier cell also excludes orientation of the contextual relation over every
signature. -/
theorem sig_barrier_cell_excludes_context_orientation {κ : Type} {ar : κ → Nat} {ν : Type}
    (M : SigTerm κ ar ν → Nat) (b n : SigTerm κ ar ν)
    (hw : WrapUnboundedAt (S := sigSchema κ ar ν) M b n)
    (hg : GainBoundedAt (S := sigSchema κ ar ν) M b n) :
    ¬ ∀ {a c : SigTerm κ ar ν}, SigContextStep a c → M c < M a := by
  intro hctx
  apply barrier_cell_excludes_orientation (S := sigSchema κ ar ν) M b n hw hg
  intro s
  exact hctx (SigContextStep.lift .hole (SigRootStep.recurSucc b s n))

/-- The coupling inequality holds over every signature. -/
theorem sig_retained_wrapper_forces_payload_coupled_gain {κ : Type} {ar : κ → Nat} {ν : Type}
    (M : SigTerm κ ar ν → Nat) (c_w : Nat)
    (hretain : ∀ x y : SigTerm κ ar ν, c_w + M x + M y ≤ M (.wrap x y))
    (horient : ∀ b s n : SigTerm κ ar ν,
      M (.wrap s (.recur b s n)) < M (.recur b s (.succ n))) :
    ∀ b s n : SigTerm κ ar ν,
      (M s : Int) + (c_w : Int) < counterGainZ (S := sigSchema κ ar ν) M b s n :=
  retained_wrapper_forces_payload_coupled_gain (S := sigSchema κ ar ν) M c_w hretain horient

/-! ## Interpretations of the signature -/

/-- An interpretation of the four schema symbols with one operation per inert symbol. -/
structure SigInterpretation (ι : Type u) (arity : ι → Nat) (α : Type w)
    extends Interpretation α where
  inertOp : (f : ι) → (Fin (arity f) → α) → α

/-- Evaluation of signature terms. -/
def SigInterpretation.eval {ι : Type u} {arity : ι → Nat} {α : Type w} {ν : Type v}
    (I : SigInterpretation ι arity α) (ρ : ν → α) : SigTerm ι arity ν → α
  | .var x => ρ x
  | .zero => I.zero
  | .succ t => I.succ (SigInterpretation.eval I ρ t)
  | .wrap s t => I.wrap (SigInterpretation.eval I ρ s) (SigInterpretation.eval I ρ t)
  | .recur b s n =>
      I.recur (SigInterpretation.eval I ρ b) (SigInterpretation.eval I ρ s)
        (SigInterpretation.eval I ρ n)
  | .inert f args => I.inertOp f (fun i => SigInterpretation.eval I ρ (args i))

/-- On embedded terms, signature evaluation is free evaluation. -/
theorem SigInterpretation.eval_embed {ι : Type u} {arity : ι → Nat} {α : Type w} {ν : Type v}
    (I : SigInterpretation ι arity α) (ρ : ν → α) (t : FreeTerm ν) :
    I.eval ρ (embed t) = I.toInterpretation.eval ρ t := by
  induction t <;> simp [SigInterpretation.eval, embed, Interpretation.eval, *]

/-- Root orientation of the four schema symbols orients every signature root step, for every
interpretation of the inert symbols. -/
theorem sig_eval_rootStep_decreases {ι : Type u} {arity : ι → Nat} {α : Type w} {ν : Type v}
    (I : SigInterpretation ι arity α) {lt : α → α → Prop}
    (hroot : RootRuleOrients I.toInterpretation lt) (ρ : ν → α)
    {t u : SigTerm ι arity ν} (h : SigRootStep t u) : lt (I.eval ρ u) (I.eval ρ t) := by
  cases h with
  | recurZero b s => exact hroot.recurZero _ _
  | recurSucc b s n => exact hroot.recurSucc _ _ _

/-- Strict monotonicity in every argument of every symbol of the signature. -/
structure SigStrictContextLaws {ι : Type u} {arity : ι → Nat} {α : Type w}
    (I : SigInterpretation ι arity α) (lt : α → α → Prop) : Prop
    extends StrictContextLaws I.toInterpretation lt where
  inertArg : ∀ (f : ι) (args : Fin (arity f) → α) (i : Fin (arity f)) {x y : α},
    lt x y → lt (I.inertOp f (Function.update args i x)) (I.inertOp f (Function.update args i y))

/-- Strict laws transport a strict comparison through any signature context. -/
theorem sig_eval_plug_strict {ι : Type u} {arity : ι → Nat} {α : Type w} {ν : Type v}
    {I : SigInterpretation ι arity α} {lt : α → α → Prop}
    (hlaws : SigStrictContextLaws I lt) (ρ : ν → α) (C : SigContext ι arity ν)
    {t u : SigTerm ι arity ν} (h : lt (I.eval ρ u) (I.eval ρ t)) :
    lt (I.eval ρ (C.plug u)) (I.eval ρ (C.plug t)) := by
  induction C with
  | hole => simpa [SigContext.plug] using h
  | succ C ih =>
      simpa [SigContext.plug, SigInterpretation.eval] using hlaws.succ ih
  | wrapLeft C r ih =>
      simpa [SigContext.plug, SigInterpretation.eval] using hlaws.wrapLeft (I.eval ρ r) ih
  | wrapRight l C ih =>
      simpa [SigContext.plug, SigInterpretation.eval] using hlaws.wrapRight (I.eval ρ l) ih
  | recurBase C s n ih =>
      simpa [SigContext.plug, SigInterpretation.eval] using
        hlaws.recurBase (I.eval ρ s) (I.eval ρ n) ih
  | recurStep b C n ih =>
      simpa [SigContext.plug, SigInterpretation.eval] using
        hlaws.recurStep (I.eval ρ b) (I.eval ρ n) ih
  | recurCounter b s C ih =>
      simpa [SigContext.plug, SigInterpretation.eval] using
        hlaws.recurCounter (I.eval ρ b) (I.eval ρ s) ih
  | inertAt f i args C ih =>
      have key : ∀ v : SigTerm ι arity ν,
          (fun j => I.eval ρ (Function.update args i v j)) =
            Function.update (fun j => I.eval ρ (args j)) i (I.eval ρ v) := by
        intro v
        funext j
        simp only [Function.update_apply]
        split_ifs <;> rfl
      show lt (I.inertOp f (fun j => I.eval ρ (Function.update args i (C.plug u) j)))
        (I.inertOp f (fun j => I.eval ρ (Function.update args i (C.plug t) j)))
      rw [key, key]
      exact hlaws.inertArg f (fun j => I.eval ρ (args j)) i ih

/-- Root orientation and strict signature laws orient every contextual step. -/
theorem sig_eval_contextStep_decreases {ι : Type u} {arity : ι → Nat} {α : Type w} {ν : Type v}
    {I : SigInterpretation ι arity α} {lt : α → α → Prop}
    (hroot : RootRuleOrients I.toInterpretation lt) (hlaws : SigStrictContextLaws I lt)
    (ρ : ν → α) {t u : SigTerm ι arity ν} (h : SigContextStep t u) :
    lt (I.eval ρ u) (I.eval ρ t) := by
  cases h with
  | lift C hstep => exact sig_eval_plug_strict hlaws ρ C (sig_eval_rootStep_decreases I hroot ρ hstep)

/-- A well-founded comparison, root orientation and strict signature laws prove termination of
the contextual relation over the signature. -/
theorem sig_contextStep_reverse_wellFounded {ι : Type u} {arity : ι → Nat} {α : Type w}
    {ν : Type v} {I : SigInterpretation ι arity α} {lt : α → α → Prop}
    (hroot : RootRuleOrients I.toInterpretation lt) (hlaws : SigStrictContextLaws I lt)
    (hlt : WellFounded lt) (ρ : ν → α) :
    WellFounded (fun u t : SigTerm ι arity ν => SigContextStep t u) := by
  apply Subrelation.wf (r := fun u t : SigTerm ι arity ν => lt (I.eval ρ u) (I.eval ρ t))
  · intro u t h
    exact sig_eval_contextStep_decreases hroot hlaws ρ h
  · exact InvImage.wf (fun t => I.eval ρ t) hlt

/-- The coupled polynomial of `FreePolynomialTermination.lean` with `1 + sum` on every inert
symbol. -/
def coupledSigInterpretation (ι : Type u) (arity : ι → Nat) : SigInterpretation ι arity Nat where
  toInterpretation := coupledInterpretation 1 2
  inertOp := fun _ args => (∑ i, args i) + 1

/-- The coupled signature interpretation is strictly monotone in every argument. -/
theorem coupledSig_strictContextLaws (ι : Type u) (arity : ι → Nat) :
    SigStrictContextLaws (coupledSigInterpretation ι arity) (fun x y : Nat => x < y) where
  toStrictContextLaws := coupled_strictContextLaws (α := 1) (β := 2) (by decide) (by decide)
  inertArg := by
    intro f args i x y hxy
    show (∑ j, Function.update args i x j) + 1 < (∑ j, Function.update args i y j) + 1
    rw [Finset.sum_update_of_mem (Finset.mem_univ i),
      Finset.sum_update_of_mem (Finset.mem_univ i)]
    omega

/-- Contextual termination of the recursor over every first-order signature: the coupled
polynomial with `1 + sum` on the inert symbols decreases on every contextual step. -/
theorem sig_free_contextual_termination (ι : Type u) (arity : ι → Nat) (ν : Type v) :
    WellFounded (fun u t : SigTerm ι arity ν => SigContextStep t u) :=
  sig_contextStep_reverse_wellFounded (I := coupledSigInterpretation ι arity)
    (coupled_rootRuleOrients (α := 1) (β := 2) (by decide) (by decide))
    (coupledSig_strictContextLaws ι arity) Nat.lt_wfRel.wf (fun _ => 0)

end OperatorKO7.Methods.OrientationClosure.SignatureGeneric
