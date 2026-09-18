import OperatorKO7.Meta.UniqueNormalization.ModelInfeasibility
import OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Certificate carriers: a rule system whose certificates need an infinite model

Campaign: `COMMAND-CENTER/design/RESEARCH-ROADMAP.md`, package DC-1 of the Distinction
certificate closeout.

A model certificate for a rule system `R` (`HasCertificate R M`) is an interpretation of
the signature in a carrier `M` under which every rule of `R` holds and which refutes every
non-trivial overlap of the actual hub linearization `linHub R`
(`ModelRefutesOverlaps`, `ModelInfeasibility.lean`). This module fixes the three rules

  `P(S(x)) → x`,  `H(x, x) → A`,  `H(C, S(P(C))) → B`

with symbol codes `A = 3`, `B = 4`, `S = 5`, `P = 6`, `H = 7`, `C = 8` (the codes of `A` and
`B` agree with `F45Certificate`, so package DC-2 can adjoin that system), and proves that a
carrier admits a certificate exactly when it is infinite
(`capacity_certificate_iff_infinite`).

Extraction. Rule preservation makes `P` a left inverse of `S` (`capacity_leftInverse`). The
root overlap of the two `H` rules in `linHub` has the single condition `C ~ S(P(C))`; if the
model satisfied it, the certificate would identify two different rules, so every
certificate separates `C` from `S(P(C))` (`capacity_certificate_separates`). Hence `C` lies
outside the image of `S`, the orbit of `C` under `S` is injective, and every certificate
carrier receives an embedding of `Nat` (`capacity_embedding`). The finite argument is also
given directly: on a finite carrier the left inverse is two-sided, so the condition holds
(`capacity_no_finite_certificate_direct`).

Construction. An infinite carrier carries a split ray (`SplitRay.ofEmbedding`), and every
split ray yields an interpretation satisfying the rules and refuting every overlap of the
hub linearization, checked by enumerating all rule pairs and all non-variable subterms
(`SplitRay.interp_rulesHold`, `SplitRay.interp_refutes`).

Unary-algebra interface. Products, closed subsets and surjective homomorphic images of
interpretations whose `S`/`P` reduct satisfies `S (P x) = x` keep that law, and every
interpretation with that law fails the certificate (`not_certificate_of_sectionLaw`).

Proves: the carrier classification for this fixed rule system and fixed certificate format;
the class membership of the system (non-omega-overlapping, right-hand sides determined); its
unique normal forms with respect to conversion from the countable certificate.
Does not prove: certificate existence for other systems, or any statement about finite proofs,
partial interpretations, or finite support coalgebras.
Relation: `Step capacity_rules`, through `CStep (linHub capacity_rules)`.
Closure: conversion.
Strategy: full rewriting.
Trust: kernel checked; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`, `unsafe` or
`opaque`. `Classical.choice` enters through the split-ray construction and the equality test
of the `H` interpretation. Axiom footprints are printed by the paired reach file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.CertificateCapacity

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

universe u v

/-! ## The certificate format -/

/-- A model certificate for `R` on the carrier `M`: an interpretation under which every rule of
`R` holds and which refutes every non-trivial overlap of the hub linearization `linHub R`. -/
def HasCertificate (R : TRS Nat Nat) (M : Type u) : Prop :=
  ∃ I : SymbolInterp Nat M, I.RulesHold R ∧ ModelRefutesOverlaps (linHub R) I

/-- The carrier classification specification: a carrier has a certificate exactly when it is
infinite. -/
def CarrierClassificationGoal (R : TRS Nat Nat) : Prop :=
  ∀ M : Type u, HasCertificate R M ↔ Infinite M

/-- The extraction specification: every certificate carrier receives an embedding of `Nat`. -/
def CarrierEmbeddingGoal (R : TRS Nat Nat) : Prop :=
  ∀ M : Type u, HasCertificate R M → Nonempty (Nat ↪ M)

/-- Two conditional rules with equal left-hand sides, right-hand sides and condition lists are
equal. -/
theorem crule_ext {sigma : Type u} {nu : Type v} {r s : CRule sigma nu} (hl : r.lhs = s.lhs)
    (hr : r.rhs = s.rhs) (hc : r.conds = s.conds) : r = s := by
  cases r
  cases s
  cases hl
  cases hr
  cases hc
  rfl

/-! ## The rules and their hub linearization -/

/-- `P(S(x)) → x`. -/
def ruleP : Rule Nat Nat := ⟨.app 6 [.app 5 [.var 0]], .var 0, rfl⟩

/-- `H(x, x) → A`. -/
def ruleH : Rule Nat Nat := ⟨.app 7 [.var 0, .var 0], .app 3 [], rfl⟩

/-- `H(C, S(P(C))) → B`. -/
def ruleHC : Rule Nat Nat := ⟨.app 7 [.app 8 [], .app 5 [.app 6 [.app 8 []]]], .app 4 [], rfl⟩

/-- The three rules of the capacity system `R_∞`. -/
def capacity_rules : TRS Nat Nat := [ruleP, ruleH, ruleHC]

/-- The hub image of `P(S(x)) → x`: the left-hand side is linear, so nothing changes. -/
def hubP : CRule Nat Nat := ⟨.app 6 [.app 5 [.var 0]], .var 0, [], rfl⟩

/-- The hub image of `H(x, x) → A`: the second occurrence becomes the fresh variable `2`, with
the condition `x ~ 2`. -/
def hubH : CRule Nat Nat := ⟨.app 7 [.var 0, .var 2], .app 3 [], [(.var 0, .var 2)], rfl⟩

/-- The hub image of the ground rule `H(C, S(P(C))) → B`. -/
def hubHC : CRule Nat Nat :=
  ⟨.app 7 [.app 8 [], .app 5 [.app 6 [.app 8 []]]], .app 4 [], [], rfl⟩

/-- The generated hub rules, every fresh variable and condition pair included. -/
def capacity_hub_rules : CTRS Nat Nat := [hubP, hubH, hubHC]

/-- The fresh base of `P(S(x)) → x` is `1`. -/
theorem ruleFreshBase_ruleP : ruleFreshBase ruleP = 1 := by
  simp [ruleFreshBase, ruleP, maxNatList, Term.varOccurrences]

/-- The fresh base of `H(x, x) → A` is `1`. -/
theorem ruleFreshBase_ruleH : ruleFreshBase ruleH = 1 := by
  simp [ruleFreshBase, ruleH, maxNatList, Term.varOccurrences]

/-- The fresh base of the ground rule is `1`. -/
theorem ruleFreshBase_ruleHC : ruleFreshBase ruleHC = 1 := by
  simp [ruleFreshBase, ruleHC, maxNatList, Term.varOccurrences]

/-- The hub transform of `P(S(x)) → x`. -/
theorem hubCRule_ruleP : hubCRule ruleP = hubP := by
  apply crule_ext
  · rw [hubCRule_lhs, ruleFreshBase_ruleP]
    simp [ruleP, hubP, hubSplitTerm, hubSplitTermAux, hubSplitListAux]
  · rfl
  · rw [hubCRule_conds, ruleFreshBase_ruleP]
    simp [ruleP, hubP, hubSplitConditions, hubSplitTermAux, hubSplitListAux]

/-- The hub transform of `H(x, x) → A` splits the second occurrence to the fresh code `2`. -/
theorem hubCRule_ruleH : hubCRule ruleH = hubH := by
  apply crule_ext
  · rw [hubCRule_lhs, ruleFreshBase_ruleH]
    simp [ruleH, hubH, hubSplitTerm, hubSplitTermAux, hubSplitListAux, hubFresh, Nat.pair]
  · rfl
  · rw [hubCRule_conds, ruleFreshBase_ruleH]
    simp [ruleH, hubH, hubSplitConditions, hubSplitTermAux, hubSplitListAux, hubFresh,
      Nat.pair]

/-- The hub transform of the ground rule. -/
theorem hubCRule_ruleHC : hubCRule ruleHC = hubHC := by
  apply crule_ext
  · rw [hubCRule_lhs, ruleFreshBase_ruleHC]
    simp [ruleHC, hubHC, hubSplitTerm, hubSplitTermAux, hubSplitListAux]
  · rfl
  · rw [hubCRule_conds, ruleFreshBase_ruleHC]
    simp [ruleHC, hubHC, hubSplitConditions, hubSplitTermAux, hubSplitListAux]

/-- **The actual hub linearization of `R_∞`.** -/
theorem capacity_hub_rules_eq : linHub capacity_rules = capacity_hub_rules := by
  simp [linHub, capacity_rules, capacity_hub_rules, hubCRule_ruleP, hubCRule_ruleH,
    hubCRule_ruleHC]

/-! ## Named operations of an interpretation -/

section Operations

variable {M : Type u}

/-- The action of `S`. -/
def succOp (I : SymbolInterp Nat M) (m : M) : M := I.op 5 [m]

/-- The action of `P`. -/
def predOp (I : SymbolInterp Nat M) (m : M) : M := I.op 6 [m]

/-- The value of `C`. -/
def baseOp (I : SymbolInterp Nat M) : M := I.op 8 []

/-- Rule preservation for `P(S(x)) → x`, in any system containing that rule, makes `P` a left
inverse of `S`. -/
theorem leftInverse_of_ruleP_mem {R : TRS Nat Nat} (hP : ruleP ∈ R) {I : SymbolInterp Nat M}
    (hR : I.RulesHold R) : Function.LeftInverse (predOp I) (succOp I) := by
  intro m
  have h := hR ruleP hP (fun _ => m)
  simpa [ruleP, predOp, succOp] using h

/-- Rule preservation for `P(S(x)) → x` makes `P` a left inverse of `S`. -/
theorem capacity_leftInverse {I : SymbolInterp Nat M} (hR : I.RulesHold capacity_rules) :
    Function.LeftInverse (predOp I) (succOp I) :=
  leftInverse_of_ruleP_mem (List.Mem.head _) hR

/-- Rule preservation for `H(x, x) → A`. -/
theorem capacity_rule_H {I : SymbolInterp Nat M} (hR : I.RulesHold capacity_rules) (m : M) :
    I.op 7 [m, m] = I.op 3 [] := by
  have h := hR ruleH (List.Mem.tail _ (List.Mem.head _)) (fun _ => m)
  simpa [ruleH] using h

/-- Rule preservation for `H(C, S(P(C))) → B`. -/
theorem capacity_rule_HC {I : SymbolInterp Nat M} (hR : I.RulesHold capacity_rules) :
    I.op 7 [baseOp I, succOp I (predOp I (baseOp I))] = I.op 4 [] := by
  have h := hR ruleHC (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (fun _ => baseOp I)
  simpa [ruleHC, baseOp, succOp, predOp] using h

end Operations

/-! ## Extraction: every certificate separates `C` from `S(P(C))` -/

section Extraction

variable {M : Type u}

/-- **Separation from the actual hub overlap**, for any conditional system containing both hub
`H` rules. If a model satisfied `C = S(P(C))`, the root overlap of `H(x, 2)` (condition `x ~ 2`)
with `H(C, S(P(C)))` would have every condition satisfied, and the certificate would identify the
two different rules. Rule preservation is not needed. -/
theorem separation_of_hub_members {C : CTRS Nat Nat} (hH : hubH ∈ C) (hHC : hubHC ∈ C)
    {I : SymbolInterp Nat M} (hcert : ModelRefutesOverlaps C I) :
    baseOp I ≠ succOp I (predOp I (baseOp I)) := by
  intro hsep
  have h := hcert hubH hH hubHC hHC hubH.lhs (Subterm.refl _) rfl
    (fun v => if v = 0 then .app 8 [] else .app 5 [.app 6 [.app 8 []]]) Subst.id
    (by simp [hubH, hubHC])
    (by
      intro p hp ρ
      simp only [hubH, List.mem_singleton] at hp
      subst hp
      simpa [baseOp, succOp, predOp] using hsep)
    (by
      intro p hp
      simp [hubHC] at hp)
  have hrhs := congrArg CRule.rhs h.1
  simp [hubH, hubHC] at hrhs

/-- **Separation for `R_∞`.** Every certificate separates `C` from `S(P(C))`. -/
theorem capacity_certificate_separates {I : SymbolInterp Nat M}
    (hcert : ModelRefutesOverlaps (linHub capacity_rules) I) :
    baseOp I ≠ succOp I (predOp I (baseOp I)) := by
  rw [capacity_hub_rules_eq] at hcert
  exact separation_of_hub_members (List.Mem.tail _ (List.Mem.head _))
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) hcert

/-- **Left inversion and separation put `C` outside the image of `S`.** If `S m = C`, then
`P C = m`, so `S (P C) = C`. -/
theorem base_outside_of_separation {I : SymbolInterp Nat M}
    (hinv : Function.LeftInverse (predOp I) (succOp I))
    (hsep : baseOp I ≠ succOp I (predOp I (baseOp I))) : ∀ m, succOp I m ≠ baseOp I := by
  intro m hm
  apply hsep
  have hp : predOp I (baseOp I) = m := by
    rw [← hm]
    exact hinv m
  rw [hp, hm]

/-- **`C` lies outside the image of `S`.** -/
theorem capacity_base_outside_range {I : SymbolInterp Nat M}
    (hR : I.RulesHold capacity_rules) (hcert : ModelRefutesOverlaps (linHub capacity_rules) I) :
    ∀ m, succOp I m ≠ baseOp I :=
  base_outside_of_separation (capacity_leftInverse hR) (capacity_certificate_separates hcert)

/-- Every certificate inhabits its carrier through the value of `C`. -/
theorem capacity_certificate_nonempty (h : HasCertificate capacity_rules M) : Nonempty M := by
  obtain ⟨I, -, -⟩ := h
  exact ⟨baseOp I⟩

end Extraction

/-! ## Split rays -/

/-- A split ray: an injective-style successor with a left inverse and a base point outside the
image of the successor. -/
structure SplitRay (M : Type u) where
  /-- The successor. -/
  next : M → M
  /-- The predecessor. -/
  prev : M → M
  /-- The base point. -/
  base : M
  /-- The predecessor undoes the successor. -/
  prev_next : Function.LeftInverse prev next
  /-- The base point is never a successor. -/
  base_outside : ∀ x, next x ≠ base

namespace SplitRay

variable {M : Type u}

/-- The orbit of the base point under the successor. -/
def orbit (ray : SplitRay M) (n : Nat) : M := ray.next^[n] ray.base

/-- **The orbit is injective.** Cancelling the common successors of `next^[n] base` and
`next^[n+k+1] base` would put the base point in the image of the successor. -/
theorem orbit_injective (ray : SplitRay M) : Function.Injective ray.orbit := by
  have hinj : Function.Injective ray.next := ray.prev_next.injective
  have key : ∀ n k, ray.next^[n] ray.base ≠ ray.next^[n + (k + 1)] ray.base := by
    intro n k h
    rw [Function.iterate_add_apply] at h
    have h2 := (hinj.iterate n) h
    rw [Function.iterate_succ_apply'] at h2
    exact ray.base_outside _ h2.symm
  intro n m h
  rcases lt_trichotomy n m with hlt | heq | hgt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact absurd h (key n k)
  · exact heq
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    exact absurd h.symm (key m k)

/-- The embedding of `Nat` along the orbit. -/
def embedding (ray : SplitRay M) : Nat ↪ M := ⟨ray.orbit, ray.orbit_injective⟩

/-- A split ray makes its carrier infinite. -/
theorem infinite (ray : SplitRay M) : Infinite M :=
  Infinite.of_injective ray.orbit ray.orbit_injective

/-- **The split ray on `Nat`**: successor, truncated predecessor, base `0`. -/
def natRay : SplitRay Nat where
  next := Nat.succ
  prev := Nat.pred
  base := 0
  prev_next := fun _ => rfl
  base_outside := Nat.succ_ne_zero

end SplitRay

/-! ## From an embedding to a split ray -/

section OfEmbedding

variable {M : Type u} (e : Nat ↪ M)

open Classical in
/-- The successor along the embedded ray; points outside the image are fixed. -/
noncomputable def rayNext (x : M) : M :=
  if h : ∃ n, e n = x then e (Classical.choose h + 1) else x

open Classical in
/-- The predecessor along the embedded ray, fixing `e 0` and every point outside the image. -/
noncomputable def rayPrev (x : M) : M :=
  if h : ∃ n, e n = x then e (Classical.choose h - 1) else x

/-- The successor moves `e n` to `e (n + 1)`. -/
theorem rayNext_apply (n : Nat) : rayNext e (e n) = e (n + 1) := by
  have h : ∃ k, e k = e n := ⟨n, rfl⟩
  unfold rayNext
  rw [dif_pos h, e.injective (Classical.choose_spec h)]

/-- The predecessor moves `e n` to `e (n - 1)`. -/
theorem rayPrev_apply (n : Nat) : rayPrev e (e n) = e (n - 1) := by
  have h : ∃ k, e k = e n := ⟨n, rfl⟩
  unfold rayPrev
  rw [dif_pos h, e.injective (Classical.choose_spec h)]

/-- Points outside the image are fixed by the successor. -/
theorem rayNext_of_not_mem {x : M} (hx : ¬ ∃ n, e n = x) : rayNext e x = x := by
  unfold rayNext
  rw [dif_neg hx]

/-- Points outside the image are fixed by the predecessor. -/
theorem rayPrev_of_not_mem {x : M} (hx : ¬ ∃ n, e n = x) : rayPrev e x = x := by
  unfold rayPrev
  rw [dif_neg hx]

/-- **The split ray of an embedding of `Nat`.** Classical selection of the index is used. -/
noncomputable def SplitRay.ofEmbedding : SplitRay M where
  next := rayNext e
  prev := rayPrev e
  base := e 0
  prev_next := by
    intro x
    by_cases hx : ∃ n, e n = x
    · obtain ⟨n, rfl⟩ := hx
      rw [rayNext_apply, rayPrev_apply, Nat.add_sub_cancel]
    · rw [rayNext_of_not_mem e hx, rayPrev_of_not_mem e hx]
  base_outside := by
    intro x
    by_cases hx : ∃ n, e n = x
    · obtain ⟨n, rfl⟩ := hx
      rw [rayNext_apply]
      intro h
      exact Nat.succ_ne_zero n (e.injective h)
    · rw [rayNext_of_not_mem e hx]
      intro h
      exact hx ⟨0, h.symm⟩

end OfEmbedding

/-- **Every infinite carrier has a split ray.** -/
theorem splitRay_of_infinite {M : Type u} [Infinite M] : Nonempty (SplitRay M) :=
  ⟨SplitRay.ofEmbedding (Infinite.natEmbedding M)⟩

/-! ## The certificate from a split ray -/

namespace SplitRay

variable {M : Type u}

open Classical in
/-- **The interpretation of a split ray.** `S` is the successor, `P` the predecessor,
`A = C = base`, `B = S(P(base))`, and `H(u, v)` is `A` when `u = v` and `B` otherwise. Every
other symbol, and every symbol at a different arity, takes the value `base`. -/
noncomputable def interp (ray : SplitRay M) : SymbolInterp Nat M where
  op := fun f args =>
    match f, args with
    | 3, [] => ray.base
    | 4, [] => ray.next (ray.prev ray.base)
    | 5, [u] => ray.next u
    | 6, [u] => ray.prev u
    | 7, [u, w] => if u = w then ray.base else ray.next (ray.prev ray.base)
    | 8, [] => ray.base
    | _, _ => ray.base

/-- `A` is the base point. -/
theorem interp_A (ray : SplitRay M) : ray.interp.op 3 [] = ray.base := rfl

/-- `B` is `S(P(base))`. -/
theorem interp_B (ray : SplitRay M) : ray.interp.op 4 [] = ray.next (ray.prev ray.base) := rfl

/-- `S` is the successor. -/
theorem interp_S (ray : SplitRay M) (u : M) : ray.interp.op 5 [u] = ray.next u := rfl

/-- `P` is the predecessor. -/
theorem interp_P (ray : SplitRay M) (u : M) : ray.interp.op 6 [u] = ray.prev u := rfl

/-- `C` is the base point. -/
theorem interp_C (ray : SplitRay M) : ray.interp.op 8 [] = ray.base := rfl

open Classical in
/-- `H` on equal arguments is `A`. -/
theorem interp_H_eq (ray : SplitRay M) (u : M) : ray.interp.op 7 [u, u] = ray.base := by
  change (if u = u then ray.base else ray.next (ray.prev ray.base)) = ray.base
  rw [if_pos rfl]

open Classical in
/-- `H` on different arguments is `B`. -/
theorem interp_H_ne (ray : SplitRay M) {u w : M} (h : u ≠ w) :
    ray.interp.op 7 [u, w] = ray.next (ray.prev ray.base) := by
  change (if u = w then ray.base else ray.next (ray.prev ray.base)) = _
  rw [if_neg h]

/-- Default branch: `S` at arity zero. -/
theorem interp_default_S_nil (ray : SplitRay M) : ray.interp.op 5 [] = ray.base := rfl

/-- Default branch: `H` at arity one. -/
theorem interp_default_H_one (ray : SplitRay M) (u : M) : ray.interp.op 7 [u] = ray.base := rfl

/-- Default branch: an unused symbol. -/
theorem interp_default_unused (ray : SplitRay M) (u : M) :
    ray.interp.op 9 [u] = ray.base := rfl

/-- `A` and `B` are different values. -/
theorem interp_A_ne_B (ray : SplitRay M) : ray.base ≠ ray.next (ray.prev ray.base) :=
  fun h => ray.base_outside _ h.symm

/-- **Every rule of `R_∞` holds in the split-ray interpretation.** -/
theorem interp_rulesHold (ray : SplitRay M) : ray.interp.RulesHold capacity_rules := by
  intro rule hr val
  simp only [capacity_rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simp only [ruleP, SymbolInterp.eval_app, SymbolInterp.evalList_cons,
      SymbolInterp.evalList_nil, SymbolInterp.eval_var, interp_S, interp_P]
    exact ray.prev_next _
  · simp only [ruleH, SymbolInterp.eval_app, SymbolInterp.evalList_cons,
      SymbolInterp.evalList_nil, SymbolInterp.eval_var, interp_H_eq, interp_A]
  · simp only [ruleHC, SymbolInterp.eval_app, SymbolInterp.evalList_cons,
      SymbolInterp.evalList_nil, interp_C, interp_S, interp_P, interp_B]
    exact ray.interp_H_ne ray.interp_A_ne_B

end SplitRay

/-! ## Subterm enumeration of the hub rules -/

/-- The non-variable subterms of `P(S(x))`. -/
theorem hubP_subterm_cases {q : Term Nat Nat} (hq : Subterm q hubP.lhs)
    (happ : q.isApp = true) : q = hubP.lhs ∨ q = .app 5 [.var 0] := by
  change Subterm q (.app 6 [.app 5 [.var 0]]) at hq
  cases hq with
  | refl => exact Or.inl rfl
  | arg ha hsa =>
      simp only [List.mem_singleton] at ha
      subst ha
      cases hsa with
      | refl => exact Or.inr rfl
      | arg hb hsb =>
          simp only [List.mem_singleton] at hb
          subst hb
          rw [hsb.eq_of_var] at happ
          simp at happ

/-- The only non-variable subterm of `H(x, 2)` is the whole left-hand side. -/
theorem hubH_subterm_eq {q : Term Nat Nat} (hq : Subterm q hubH.lhs)
    (happ : q.isApp = true) : q = hubH.lhs :=
  ClassExamples.flat_app_subterm_eq
    (fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩) hq happ

/-- The non-variable subterms of `H(C, S(P(C)))`. -/
theorem hubHC_subterm_cases {q : Term Nat Nat} (hq : Subterm q hubHC.lhs)
    (happ : q.isApp = true) :
    q = hubHC.lhs ∨ q = .app 8 [] ∨ q = .app 5 [.app 6 [.app 8 []]] ∨
      q = .app 6 [.app 8 []] := by
  change Subterm q (.app 7 [.app 8 [], .app 5 [.app 6 [.app 8 []]]]) at hq
  cases hq with
  | refl => exact Or.inl rfl
  | arg ha hsa =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · cases hsa with
        | refl => exact Or.inr (Or.inl rfl)
        | arg hb _ => simp at hb
      · cases hsa with
        | refl => exact Or.inr (Or.inr (Or.inl rfl))
        | arg hb hsb =>
            simp only [List.mem_singleton] at hb
            subst hb
            cases hsb with
            | refl => exact Or.inr (Or.inr (Or.inr rfl))
            | arg hc hsc =>
                simp only [List.mem_singleton] at hc
                subst hc
                cases hsc with
                | refl => exact Or.inr (Or.inl rfl)
                | arg hd _ => simp at hd

/-- **Every interpretation separating `C` from `S(P(C))` refutes every non-trivial overlap of the
hub rules of `R_∞`.** All nine ordered rule pairs and every non-variable subterm are enumerated.
The only overlaps whose left-hand sides match are the root overlaps of the two `H` rules, in both
orders; their condition forces `C = S(P(C))`. Every other candidate fails by a clash of fixed
symbols. Rule preservation is not used. -/
theorem capacity_hub_refutes_of_separation {M : Type u} (I : SymbolInterp Nat M)
    (hsep : baseOp I ≠ succOp I (predOp I (baseOp I))) :
    ModelRefutesOverlaps capacity_hub_rules I := by
  intro r₁ h₁ r₂ h₂ q hq happ σ₁ σ₂ heq hc₁ hc₂
  simp only [capacity_hub_rules, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl | rfl
  · rcases hubP_subterm_cases hq happ with rfl | rfl
    · rcases h₂ with rfl | rfl | rfl
      · exact ⟨rfl, rfl⟩
      · exfalso
        simp [hubP, hubH] at heq
      · exfalso
        simp [hubP, hubHC] at heq
    · exfalso
      rcases h₂ with rfl | rfl | rfl <;> simp [hubP, hubH, hubHC] at heq
  · have hq' := hubH_subterm_eq hq happ
    subst hq'
    rcases h₂ with rfl | rfl | rfl
    · exfalso
      simp [hubP, hubH] at heq
    · exact ⟨rfl, rfl⟩
    · exfalso
      simp [hubH, hubHC] at heq
      obtain ⟨h0, h2⟩ := heq
      have hc := hc₁ (.var 0, .var 2) (List.Mem.head _) (fun _ => baseOp I)
      simp only [Subst.apply_var] at hc
      rw [h0, h2] at hc
      simp only [SymbolInterp.eval_app, SymbolInterp.evalList_cons,
        SymbolInterp.evalList_nil] at hc
      exact hsep hc
  · rcases hubHC_subterm_cases hq happ with rfl | rfl | rfl | rfl
    · rcases h₂ with rfl | rfl | rfl
      · exfalso
        simp [hubP, hubHC] at heq
      · exfalso
        simp [hubH, hubHC] at heq
        obtain ⟨h0, h2⟩ := heq
        have hc := hc₂ (.var 0, .var 2) (List.Mem.head _) (fun _ => baseOp I)
        simp only [Subst.apply_var] at hc
        rw [← h0, ← h2] at hc
        simp only [SymbolInterp.eval_app, SymbolInterp.evalList_cons,
          SymbolInterp.evalList_nil] at hc
        exact hsep hc
      · exact ⟨rfl, rfl⟩
    · exfalso
      rcases h₂ with rfl | rfl | rfl <;> simp [hubP, hubH, hubHC] at heq
    · exfalso
      rcases h₂ with rfl | rfl | rfl <;> simp [hubP, hubH, hubHC] at heq
    · exfalso
      rcases h₂ with rfl | rfl | rfl <;> simp [hubP, hubH, hubHC] at heq

/-- **A certificate is exactly a rule model separating `C` from `S(P(C))`.** -/
theorem capacity_refutes_iff_separation {M : Type u} (I : SymbolInterp Nat M) :
    ModelRefutesOverlaps (linHub capacity_rules) I ↔
      baseOp I ≠ succOp I (predOp I (baseOp I)) := by
  constructor
  · exact capacity_certificate_separates
  · intro hsep
    rw [capacity_hub_rules_eq]
    exact capacity_hub_refutes_of_separation I hsep

namespace SplitRay

variable {M : Type u}

/-- **The split-ray interpretation refutes every non-trivial overlap of `linHub R_∞`.** -/
theorem interp_refutes (ray : SplitRay M) :
    ModelRefutesOverlaps (linHub capacity_rules) ray.interp :=
  (capacity_refutes_iff_separation ray.interp).2 ray.interp_A_ne_B

end SplitRay

/-! ## The classification -/

section Classification

variable {M : Type u}

/-- **Construction: every split ray gives a certificate.** -/
theorem capacity_certificate_of_splitRay (ray : SplitRay M) :
    HasCertificate capacity_rules M :=
  ⟨ray.interp, ray.interp_rulesHold, ray.interp_refutes⟩

/-- **Extraction: the carrier record of a certificate.** `S`, `P` and `C` of any certificate form
a split ray. -/
def certificateRay (I : SymbolInterp Nat M) (hR : I.RulesHold capacity_rules)
    (hcert : ModelRefutesOverlaps (linHub capacity_rules) I) : SplitRay M where
  next := succOp I
  prev := predOp I
  base := baseOp I
  prev_next := capacity_leftInverse hR
  base_outside := capacity_base_outside_range hR hcert

/-- The orbit of `C` under `S` in a certificate. -/
def capacityOrbit (I : SymbolInterp Nat M) (n : Nat) : M := (succOp I)^[n] (baseOp I)

/-- **The orbit of `C` in every certificate is injective.** -/
theorem capacity_orbit_injective {I : SymbolInterp Nat M} (hR : I.RulesHold capacity_rules)
    (hcert : ModelRefutesOverlaps (linHub capacity_rules) I) :
    Function.Injective (capacityOrbit I) :=
  (certificateRay I hR hcert).orbit_injective

/-- **Every certificate carrier receives an embedding of `Nat`.** -/
theorem capacity_embedding (h : HasCertificate capacity_rules M) : Nonempty (Nat ↪ M) := by
  obtain ⟨I, hR, hcert⟩ := h
  exact ⟨⟨capacityOrbit I, capacity_orbit_injective hR hcert⟩⟩

/-- A certificate exists exactly when the carrier has a split ray. -/
theorem capacity_certificate_iff_splitRay :
    HasCertificate capacity_rules M ↔ Nonempty (SplitRay M) := by
  constructor
  · rintro ⟨I, hR, hcert⟩
    exact ⟨certificateRay I hR hcert⟩
  · rintro ⟨ray⟩
    exact capacity_certificate_of_splitRay ray

/-- **No finite carrier has a certificate**, through the embedding of `Nat`. -/
theorem capacity_no_finite_certificate [Finite M] : ¬ HasCertificate capacity_rules M := by
  intro h
  obtain ⟨e⟩ := capacity_embedding h
  haveI : Infinite M := Infinite.of_injective e e.injective
  exact not_finite M

/-- On a finite carrier, rule preservation makes `P` a two-sided inverse of `S`: the injective
map `S` is surjective. -/
theorem capacity_finite_rightInverse [Finite M] {I : SymbolInterp Nat M}
    (hR : I.RulesHold capacity_rules) : Function.RightInverse (predOp I) (succOp I) := by
  have hsurj : Function.Surjective (succOp I) :=
    Finite.injective_iff_surjective.mp (capacity_leftInverse hR).injective
  intro m
  obtain ⟨m', rfl⟩ := hsurj m
  rw [capacity_leftInverse hR m']

/-- **The direct finite argument.** On a finite carrier `C = S(P(C))` holds, so the certificate
condition is satisfied and the certificate fails. -/
theorem capacity_no_finite_certificate_direct [Finite M] :
    ¬ HasCertificate capacity_rules M := by
  rintro ⟨I, hR, hcert⟩
  exact capacity_certificate_separates hcert (capacity_finite_rightInverse hR (baseOp I)).symm

/-- **Certificate iff infinite carrier**, for every carrier type in every universe. -/
theorem capacity_certificate_iff_infinite (M : Type u) :
    HasCertificate capacity_rules M ↔ Infinite M := by
  constructor
  · intro h
    obtain ⟨e⟩ := capacity_embedding h
    exact Infinite.of_injective e e.injective
  · intro _
    obtain ⟨ray⟩ := splitRay_of_infinite (M := M)
    exact capacity_certificate_of_splitRay ray

/-- The classification specification holds for `R_∞`. -/
theorem capacity_carrierClassificationGoal : CarrierClassificationGoal.{u} capacity_rules :=
  capacity_certificate_iff_infinite

/-- The extraction specification holds for `R_∞`. -/
theorem capacity_carrierEmbeddingGoal : CarrierEmbeddingGoal.{u} capacity_rules :=
  fun _ h => capacity_embedding h

end Classification

/-! ## The countable minimum -/

/-- **The countable certificate** on `Nat`: `S` successor, `P` truncated predecessor, `A = C = 0`,
`B = 1`, `H` the equality test. -/
theorem capacity_countable_certificate : HasCertificate capacity_rules Nat :=
  capacity_certificate_of_splitRay SplitRay.natRay

/-- On the `Nat` certificate, `A = C = 0` and `B = 1`. -/
theorem natRay_values :
    SplitRay.natRay.interp.op 3 [] = 0 ∧ SplitRay.natRay.interp.op 8 [] = 0 ∧
      SplitRay.natRay.interp.op 4 [] = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- **The countable minimum through embeddings.** `Nat` carries a certificate, and `Nat` embeds
into every certificate carrier. -/
theorem capacity_minimal_carrier :
    HasCertificate capacity_rules Nat ∧
      ∀ M : Type u, HasCertificate capacity_rules M → Nonempty (Nat ↪ M) :=
  ⟨capacity_countable_certificate, fun _ h => capacity_embedding h⟩

/-! ## Controls -/

/-- The one-element interpretation. -/
def unitInterp : SymbolInterp Nat Unit := ⟨fun _ _ => ()⟩

/-- **The one-element total model satisfies every rule.** -/
theorem unit_rulesHold : unitInterp.RulesHold capacity_rules :=
  fun _ _ _ => rfl

/-- **The one-element model fails the certificate.** -/
theorem unit_not_certificate : ¬ ModelRefutesOverlaps (linHub capacity_rules) unitInterp :=
  fun hcert => capacity_certificate_separates hcert rfl

/-- `Unit` has no certificate. -/
theorem unit_no_certificate : ¬ HasCertificate capacity_rules Unit :=
  capacity_no_finite_certificate

/-! ## Class membership and unique normal forms -/

/-- The non-variable subterms of the original left-hand sides. -/
theorem capacity_lhs_subterm_cases {r : Rule Nat Nat} (hr : r ∈ capacity_rules)
    {q : Term Nat Nat} (hq : Subterm q r.lhs) (happ : q.isApp = true) :
    q = r.lhs ∨ q = .app 5 [.var 0] ∨ q = .app 8 [] ∨ q = .app 5 [.app 6 [.app 8 []]] ∨
      q = .app 6 [.app 8 []] := by
  simp only [capacity_rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hubP_subterm_cases hq happ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inl (ClassExamples.flat_app_subterm_eq
      (fun a ha => ⟨0, by simpa using ha⟩) hq happ)
  · rcases hubHC_subterm_cases hq happ with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- `H(x, x)` and `H(C, S(P(C)))` are not omega-unifiable: the shared variable would relate `C`
to `S(P(C))`. -/
theorem H_diag_not_omega_HC : ¬ OmegaUnifiable ruleH.lhs ruleHC.lhs := by
  rintro ⟨E, hE, hst⟩
  simp only [ruleH, ruleHC, leftCopy, rightCopy, Term.mapVar_app, Term.mapVarList_cons,
    Term.mapVarList_nil, Term.mapVar_var] at hst
  obtain ⟨-, hargs⟩ := hE.decomp hst
  simp only [List.forall₂_cons] at hargs
  obtain ⟨h1, h2, -⟩ := hargs
  exact absurd (hE.decomp (hE.trans' (hE.symm' h1) h2)).1 (by decide)

/-- The same pair in the other order. -/
theorem HC_not_omega_H_diag : ¬ OmegaUnifiable ruleHC.lhs ruleH.lhs := by
  rintro ⟨E, hE, hst⟩
  simp only [ruleH, ruleHC, leftCopy, rightCopy, Term.mapVar_app, Term.mapVarList_cons,
    Term.mapVarList_nil, Term.mapVar_var] at hst
  obtain ⟨-, hargs⟩ := hE.decomp hst
  simp only [List.forall₂_cons] at hargs
  obtain ⟨h1, h2, -⟩ := hargs
  exact absurd (hE.decomp (hE.trans' h1 (hE.symm' h2))).1 (by decide)

/-- `P(C)` and `P(S(x))` are not omega-unifiable: `C` would meet `S`. -/
theorem PC_not_omega_P : ¬ OmegaUnifiable (.app 6 [.app 8 []]) ruleP.lhs := by
  rintro ⟨E, hE, hst⟩
  simp only [ruleP, leftCopy, rightCopy, Term.mapVar_app, Term.mapVarList_cons,
    Term.mapVarList_nil, Term.mapVar_var] at hst
  obtain ⟨-, hargs⟩ := hE.decomp hst
  simp only [List.forall₂_cons] at hargs
  exact absurd (hE.decomp hargs.1).1 (by decide)

/-- **`R_∞` is non-omega-overlapping.** -/
theorem capacity_nonOmegaOverlapping : NonOmegaOverlapping capacity_rules := by
  intro r₁ h₁ r₂ h₂ q hq happ hu
  have h₁' := h₁
  have h₂' := h₂
  simp only [capacity_rules, List.mem_cons, List.not_mem_nil, or_false] at h₁' h₂'
  rcases capacity_lhs_subterm_cases h₁ hq happ with hroot | h | h | h | h
  · subst hroot
    rcases h₁' with rfl | rfl | rfl <;> rcases h₂' with rfl | rfl | rfl
    all_goals first
      | exact ⟨rfl, rfl⟩
      | exact absurd (ClassExamples.omega_head_eq hu) (by decide)
      | exact absurd hu H_diag_not_omega_HC
      | exact absurd hu HC_not_omega_H_diag
  · subst h
    exfalso
    rcases h₂' with rfl | rfl | rfl <;>
      exact absurd (ClassExamples.omega_head_eq hu) (by decide)
  · subst h
    exfalso
    rcases h₂' with rfl | rfl | rfl <;>
      exact absurd (ClassExamples.omega_head_eq hu) (by decide)
  · subst h
    exfalso
    rcases h₂' with rfl | rfl | rfl <;>
      exact absurd (ClassExamples.omega_head_eq hu) (by decide)
  · subst h
    exfalso
    rcases h₂' with rfl | rfl | rfl
    · exact PC_not_omega_P hu
    · exact absurd (ClassExamples.omega_head_eq hu) (by decide)
    · exact absurd (ClassExamples.omega_head_eq hu) (by decide)

/-- **Every right-hand side of `R_∞` is determined by its left-hand side.** -/
theorem capacity_rhsDetermined : TRS.RhsDetermined capacity_rules := by
  intro r hr
  simp only [capacity_rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · intro a b hab
    simpa [ruleP] using hab
  · intro a b _
    rfl
  · intro a b _
    rfl

/-- The occurrence form of the variable condition for `R_∞`. -/
theorem capacity_varCondition :
    ∀ rule ∈ capacity_rules, ∀ x, VarOccurs x rule.rhs → VarOccurs x rule.lhs := by
  intro r hr x hx
  simp only [capacity_rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · change VarOccurs x (Term.var 0) at hx
    cases hx
    exact VarOccurs.arg (List.Mem.head _) (VarOccurs.arg (List.Mem.head _) VarOccurs.here)
  · change VarOccurs x (Term.app 3 []) at hx
    rcases hx.app_inv with ⟨a, ha, -⟩
    simp at ha
  · change VarOccurs x (Term.app 4 []) at hx
    rcases hx.app_inv with ⟨a, ha, -⟩
    simp at ha

/-- **`R_∞` has unique normal forms with respect to conversion**, from the countable certificate.

Relation: `Step capacity_rules`. Closure: conversion. Strategy: full rewriting. -/
theorem capacity_UNconv : UNconv capacity_rules :=
  UNconv_of_linHub_model capacity_varCondition SplitRay.natRay.interp
    SplitRay.natRay.interp_rulesHold SplitRay.natRay.interp_refutes

/-- The class hypotheses and the uniqueness conclusion together. -/
theorem capacity_class_and_UNconv :
    NonOmegaOverlapping capacity_rules ∧ TRS.RhsDetermined capacity_rules ∧
      UNconv capacity_rules :=
  ⟨capacity_nonOmegaOverlapping, capacity_rhsDetermined, capacity_UNconv⟩

/-! ## The unary-algebra interface: products, closed subsets and images -/

/-- The reduct of an interpretation to `S`, `P` and `C`. -/
structure UnaryReduct (M : Type u) where
  /-- The action of `S`. -/
  next : M → M
  /-- The action of `P`. -/
  prev : M → M
  /-- The value of `C`. -/
  base : M

namespace UnaryReduct

variable {M : Type u} {N : Type v}

/-- The section law `S (P x) = x`. -/
def SectionLaw (A : UnaryReduct M) : Prop := ∀ x, A.next (A.prev x) = x

/-- The product of two reducts. -/
def prod (A : UnaryReduct M) (B : UnaryReduct N) : UnaryReduct (M × N) :=
  ⟨Prod.map A.next B.next, Prod.map A.prev B.prev, (A.base, B.base)⟩

/-- **Products keep the section law.** -/
theorem sectionLaw_prod {A : UnaryReduct M} {B : UnaryReduct N} (hA : A.SectionLaw)
    (hB : B.SectionLaw) : (A.prod B).SectionLaw := by
  rintro ⟨x, y⟩
  simp only [prod, Prod.map_apply, hA x, hB y]

/-- A subset closed under `S` and `P` and containing `C`. -/
structure Closed (A : UnaryReduct M) (S : Set M) : Prop where
  /-- Closure under `S`. -/
  next_mem : ∀ x ∈ S, A.next x ∈ S
  /-- Closure under `P`. -/
  prev_mem : ∀ x ∈ S, A.prev x ∈ S
  /-- `C` belongs to the subset. -/
  base_mem : A.base ∈ S

/-- The restriction of a reduct to a closed subset. -/
def restrict (A : UnaryReduct M) (S : Set M) (hS : A.Closed S) : UnaryReduct S :=
  ⟨fun x => ⟨A.next x, hS.next_mem x x.2⟩, fun x => ⟨A.prev x, hS.prev_mem x x.2⟩,
    ⟨A.base, hS.base_mem⟩⟩

/-- **Closed subsets keep the section law.** -/
theorem sectionLaw_restrict {A : UnaryReduct M} {S : Set M} (hS : A.Closed S)
    (hA : A.SectionLaw) : (A.restrict S hS).SectionLaw := by
  intro x
  apply Subtype.ext
  exact hA x.1

/-- A homomorphism of reducts. -/
structure Hom (A : UnaryReduct M) (B : UnaryReduct N) where
  /-- The underlying map. -/
  toFun : M → N
  /-- `S` is preserved. -/
  map_next : ∀ x, toFun (A.next x) = B.next (toFun x)
  /-- `P` is preserved. -/
  map_prev : ∀ x, toFun (A.prev x) = B.prev (toFun x)
  /-- `C` is preserved. -/
  map_base : toFun A.base = B.base

/-- **Surjective homomorphic images keep the section law.** -/
theorem sectionLaw_image {A : UnaryReduct M} {B : UnaryReduct N} (h : A.Hom B)
    (hs : Function.Surjective h.toFun) (hA : A.SectionLaw) : B.SectionLaw := by
  intro y
  obtain ⟨x, rfl⟩ := hs y
  rw [← h.map_prev, ← h.map_next, hA x]

end UnaryReduct

section Interface

variable {M : Type u} {N : Type v}

/-- The `S`/`P`/`C` reduct of an interpretation. -/
def reductOf (I : SymbolInterp Nat M) : UnaryReduct M := ⟨succOp I, predOp I, baseOp I⟩

/-- **The section law excludes the certificate.** -/
theorem not_certificate_of_sectionLaw {I : SymbolInterp Nat M}
    (h : (reductOf I).SectionLaw) : ¬ ModelRefutesOverlaps (linHub capacity_rules) I :=
  fun hcert => capacity_certificate_separates hcert (h (baseOp I)).symm

/-- Finite rule models satisfy the section law. -/
theorem sectionLaw_of_finite [Finite M] {I : SymbolInterp Nat M}
    (hR : I.RulesHold capacity_rules) : (reductOf I).SectionLaw :=
  capacity_finite_rightInverse hR

/-- The product interpretation, symbolwise on both coordinates. -/
def prodInterp (I : SymbolInterp Nat M) (J : SymbolInterp Nat N) : SymbolInterp Nat (M × N) :=
  ⟨fun f xs => (I.op f (xs.map Prod.fst), J.op f (xs.map Prod.snd))⟩

/-- Evaluation in the product interpretation is the pair of evaluations. -/
theorem prodInterp_eval (I : SymbolInterp Nat M) (J : SymbolInterp Nat N) (ρ : Nat → M × N)
    (t : Term Nat Nat) :
    (prodInterp I J).eval ρ t = (I.eval (fun x => (ρ x).1) t, J.eval (fun x => (ρ x).2) t) := by
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
      have h1 : args.map (fun a => ((prodInterp I J).eval ρ a).1) =
          args.map (I.eval (fun x => (ρ x).1)) :=
        List.map_congr_left (fun a ha => by rw [ih a ha])
      have h2 : args.map (fun a => ((prodInterp I J).eval ρ a).2) =
          args.map (J.eval (fun x => (ρ x).2)) :=
        List.map_congr_left (fun a ha => by rw [ih a ha])
      simp only [SymbolInterp.eval_app, SymbolInterp.evalList_eq_map]
      show (I.op f ((args.map ((prodInterp I J).eval ρ)).map Prod.fst),
          J.op f ((args.map ((prodInterp I J).eval ρ)).map Prod.snd)) = _
      rw [List.map_map, List.map_map]
      exact congrArg₂ Prod.mk (congrArg (I.op f) h1) (congrArg (J.op f) h2)

/-- The product of two models of the rules is a model of the rules. -/
theorem prodInterp_rulesHold {R : TRS Nat Nat} {I : SymbolInterp Nat M} {J : SymbolInterp Nat N}
    (hI : I.RulesHold R) (hJ : J.RulesHold R) : (prodInterp I J).RulesHold R := by
  intro rule hr ρ
  rw [prodInterp_eval, prodInterp_eval, hI rule hr, hJ rule hr]

/-- The reduct of a product is the product of the reducts. -/
theorem reductOf_prodInterp (I : SymbolInterp Nat M) (J : SymbolInterp Nat N) :
    reductOf (prodInterp I J) = (reductOf I).prod (reductOf J) := rfl

/-- **Products of section-law models fail the certificate.** -/
theorem prodInterp_not_certificate {I : SymbolInterp Nat M} {J : SymbolInterp Nat N}
    (hI : (reductOf I).SectionLaw) (hJ : (reductOf J).SectionLaw) :
    ¬ ModelRefutesOverlaps (linHub capacity_rules) (prodInterp I J) := by
  apply not_certificate_of_sectionLaw
  rw [reductOf_prodInterp]
  exact UnaryReduct.sectionLaw_prod hI hJ

/-- A subset closed under every operation of an interpretation. -/
def OpClosed (I : SymbolInterp Nat M) (S : Set M) : Prop :=
  ∀ f (xs : List M), (∀ x ∈ xs, x ∈ S) → I.op f xs ∈ S

/-- The interpretation restricted to an operation-closed subset. -/
def restrictInterp (I : SymbolInterp Nat M) (S : Set M) (hS : OpClosed I S) :
    SymbolInterp Nat S :=
  ⟨fun f xs => ⟨I.op f (xs.map Subtype.val), hS f _ (fun x hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact y.2)⟩⟩

/-- An operation-closed subset is closed for the reduct. -/
theorem OpClosed.reductClosed {I : SymbolInterp Nat M} {S : Set M} (hS : OpClosed I S) :
    (reductOf I).Closed S :=
  ⟨fun x hx => hS 5 [x] (by simpa using hx), fun x hx => hS 6 [x] (by simpa using hx),
    hS 8 [] (by simp)⟩

/-- The reduct of a restriction is the restriction of the reduct. -/
theorem reductOf_restrictInterp (I : SymbolInterp Nat M) (S : Set M) (hS : OpClosed I S) :
    reductOf (restrictInterp I S hS) = (reductOf I).restrict S hS.reductClosed := rfl

/-- **Closed subsets of section-law models fail the certificate.** -/
theorem restrictInterp_not_certificate {I : SymbolInterp Nat M} {S : Set M} (hS : OpClosed I S)
    (hI : (reductOf I).SectionLaw) :
    ¬ ModelRefutesOverlaps (linHub capacity_rules) (restrictInterp I S hS) := by
  apply not_certificate_of_sectionLaw
  rw [reductOf_restrictInterp]
  exact UnaryReduct.sectionLaw_restrict hS.reductClosed hI

/-- A homomorphism of interpretations. -/
def IsInterpHom (I : SymbolInterp Nat M) (J : SymbolInterp Nat N) (h : M → N) : Prop :=
  ∀ f (xs : List M), h (I.op f xs) = J.op f (xs.map h)

/-- An interpretation homomorphism restricts to a reduct homomorphism. -/
def IsInterpHom.toReductHom {I : SymbolInterp Nat M} {J : SymbolInterp Nat N} {h : M → N}
    (hh : IsInterpHom I J h) : (reductOf I).Hom (reductOf J) :=
  ⟨h, fun x => hh 5 [x], fun x => hh 6 [x], hh 8 []⟩

/-- **Surjective images of section-law models fail the certificate.** -/
theorem image_not_certificate {I : SymbolInterp Nat M} {J : SymbolInterp Nat N} {h : M → N}
    (hh : IsInterpHom I J h) (hs : Function.Surjective h) (hI : (reductOf I).SectionLaw) :
    ¬ ModelRefutesOverlaps (linHub capacity_rules) J :=
  not_certificate_of_sectionLaw (UnaryReduct.sectionLaw_image hh.toReductHom hs hI)

/-- **Finite rule models, their products, closed subsets and surjective images all fail the
certificate.** -/
theorem finite_constructions_not_certificate [Finite M] [Finite N] {I : SymbolInterp Nat M}
    {J : SymbolInterp Nat N} (hI : I.RulesHold capacity_rules) (hJ : J.RulesHold capacity_rules) :
    ¬ ModelRefutesOverlaps (linHub capacity_rules) (prodInterp I J) ∧
      (∀ (S : Set M) (hS : OpClosed I S),
        ¬ ModelRefutesOverlaps (linHub capacity_rules) (restrictInterp I S hS)) ∧
      (∀ {K : Type v} (L : SymbolInterp Nat K) (h : M → K), IsInterpHom I L h →
        Function.Surjective h → ¬ ModelRefutesOverlaps (linHub capacity_rules) L) :=
  ⟨prodInterp_not_certificate (sectionLaw_of_finite hI) (sectionLaw_of_finite hJ),
    fun _ hS => restrictInterp_not_certificate hS (sectionLaw_of_finite hI),
    fun _ _ hh hs => image_not_certificate hh hs (sectionLaw_of_finite hI)⟩

end Interface

end OperatorKO7.Meta.UniqueNormalization.CertificateCapacity
