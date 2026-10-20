import OperatorKO7.Meta.Methods.OrientationClosure.ProcessorSemantics
import OperatorKO7.Meta.Methods.OrientationClosure.FreePolynomialTermination
import Mathlib.Tactic

/-!
# Substrate-change method rows

Four rows of the method universe prove termination on a changed substrate: string rewriting, cycle
rewriting, rewriting modulo equations, and term graph rewriting under maximal sharing. Each
substrate is defined here on its own objects and applied to the free recursor.

A string or cycle rewriting step changes the length of a word by at most a constant fixed by the
finite system (`srsStep_length_le`, `cycleStep_length_le`). Under a string encoding of free terms
with compositional length, the duplicating step changes the length by an amount that grows with
the payload, so no finite string or cycle system performs the duplicating rule as one step
(`stringRewritingInapplicability_universal`, `cycleRewritingInapplicability_universal`). The prefix
encoding is injective (`polish_injective`): the restriction concerns one-step simulation, not
representability. Cycle termination implies string termination (`srs_wf_of_cycle_wf`), and the
rule `01 → 10` terminates on strings and loops on cycles (`cycleRewriting_feature`).

Rewriting modulo equations is sound for termination of the free system (`wf_of_modStep_wf`). With
commutativity of the wrapper the quotient terminates and identifies two distinct normal forms
(`comm_merges_normal_forms`); one ground equation makes the quotient loop while the free system
terminates (`equationalQuotientNonConservativity_mutation`).

Maximal sharing contracts every occurrence of one redex at once. Every shared step is a nonempty
sequence of term steps (`sharedStep_simulates`), so the free system terminates under sharing
(`sharingNonConservativity_universal`). One shared step can replace two term steps and no single
term step (`sharing_cost_control`), and on Toyama's system sharing terminates from a term whose term
rewriting loops (`toyama_sharing_nonconservative`).
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.ProcessorSemantics
open OperatorKO7.Methods.OrientationClosure.FreePolynomialTermination

deriving instance DecidableEq for FreeTerm

/-! ## String and cycle rewriting -/

/-- A string rule. -/
structure SRule (A : Type) where
  lhs : List A
  rhs : List A

/-- One string rewriting step (Book and Otto, String-Rewriting Systems, 1993, Chapter 2): an
occurrence of a left-hand side inside a two-sided context is replaced by the right-hand side. -/
def SRSStep {A : Type} (R : List (SRule A)) (u v : List A) : Prop :=
  ∃ rule ∈ R, ∃ x y : List A, u = x ++ rule.lhs ++ y ∧ v = x ++ rule.rhs ++ y

theorem srsStep_length {A : Type} {R : List (SRule A)} {u v : List A} (h : SRSStep R u v) :
    ∃ rule ∈ R, v.length + rule.lhs.length = u.length + rule.rhs.length := by
  obtain ⟨rule, hr, x, y, rfl, rfl⟩ := h
  refine ⟨rule, hr, ?_⟩
  simp only [List.length_append]
  omega

/-- Sum of the right-hand-side lengths of a finite string system. -/
def sumRhs {A : Type} (R : List (SRule A)) : Nat :=
  (R.map fun rule => rule.rhs.length).sum

theorem rhs_length_le_sumRhs {A : Type} {R : List (SRule A)} {rule : SRule A} (h : rule ∈ R) :
    rule.rhs.length ≤ sumRhs R := by
  induction R with
  | nil => cases h
  | cons r R ih =>
    simp only [sumRhs, List.map_cons, List.sum_cons] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h
      omega

/-- A string step lengthens a word by at most `sumRhs R`. -/
theorem srsStep_length_le {A : Type} {R : List (SRule A)} {u v : List A} (h : SRSStep R u v) :
    v.length ≤ u.length + sumRhs R := by
  obtain ⟨rule, hr, hlen⟩ := srsStep_length h
  have := rhs_length_le_sumRhs hr
  omega

/-- Two words are rotations of each other. -/
def Rotation {A : Type} (u v : List A) : Prop :=
  ∃ p q : List A, u = p ++ q ∧ v = q ++ p

theorem rotation_length {A : Type} {u v : List A} (h : Rotation u v) : v.length = u.length := by
  obtain ⟨p, q, rfl, rfl⟩ := h
  simp only [List.length_append]
  omega

theorem rotation_refl {A : Type} (u : List A) : Rotation u u :=
  ⟨[], u, by simp, by simp⟩

/-- One cycle rewriting step (Zantema, König and Bruggink, Termination of cycle rewriting,
RTA-TLCA 2014): a string step on words read up to rotation. -/
def CycleStep {A : Type} (R : List (SRule A)) (u v : List A) : Prop :=
  ∃ u' v', Rotation u u' ∧ SRSStep R u' v' ∧ Rotation v' v

/-- A cycle step lengthens a word by at most `sumRhs R`. -/
theorem cycleStep_length_le {A : Type} {R : List (SRule A)} {u v : List A}
    (h : CycleStep R u v) : v.length ≤ u.length + sumRhs R := by
  obtain ⟨u', v', h1, h2, h3⟩ := h
  have hs := srsStep_length_le h2
  have e1 := rotation_length h1
  have e3 := rotation_length h3
  omega

theorem cycleStep_of_srsStep {A : Type} {R : List (SRule A)} {u v : List A}
    (h : SRSStep R u v) : CycleStep R u v :=
  ⟨u, v, rotation_refl u, h, rotation_refl v⟩

/-- Cycle termination implies string termination. -/
theorem srs_wf_of_cycle_wf {A : Type} (R : List (SRule A))
    (h : WellFounded (fun v u => CycleStep R u v)) : WellFounded (fun v u => SRSStep R u v) :=
  Subrelation.wf (fun {_ _} hs => cycleStep_of_srsStep hs) h

/-! ### The rule `01 → 10` -/

/-- The single rule `01 → 10`. -/
def swapRules : List (SRule Nat) := [⟨[0, 1], [1, 0]⟩]

/-- Number of letters `1`. -/
def ones : List Nat → Nat
  | [] => 0
  | a :: l => (if a = 1 then 1 else 0) + ones l

/-- Number of pairs of positions carrying `0` before `1`. -/
def inv01 : List Nat → Nat
  | [] => 0
  | a :: l => (if a = 0 then ones l else 0) + inv01 l

theorem ones_append (l₁ l₂ : List Nat) : ones (l₁ ++ l₂) = ones l₁ + ones l₂ := by
  induction l₁ with
  | nil => simp only [List.nil_append, ones, Nat.zero_add]
  | cons a l ih =>
    simp only [List.cons_append, ones, ih]
    omega

theorem inv01_zero_cons (l : List Nat) : inv01 (0 :: l) = ones l + inv01 l := by
  simp [inv01]

theorem inv01_one_cons (l : List Nat) : inv01 (1 :: l) = inv01 l := by
  simp [inv01]

theorem ones_one_cons (l : List Nat) : ones (1 :: l) = 1 + ones l := by
  simp [ones]

theorem ones_zero_cons (l : List Nat) : ones (0 :: l) = ones l := by
  simp [ones]

theorem inv01_append_swap (x y : List Nat) :
    inv01 (x ++ [0, 1] ++ y) = inv01 (x ++ [1, 0] ++ y) + 1 := by
  induction x with
  | nil =>
    simp only [List.nil_append, List.cons_append]
    rw [inv01_zero_cons, inv01_one_cons, inv01_one_cons, inv01_zero_cons, ones_one_cons]
    omega
  | cons a x ih =>
    have hones : ones (x ++ [0, 1] ++ y) = ones (x ++ [1, 0] ++ y) := by
      rw [ones_append, ones_append, ones_append, ones_append]
      simp only [ones]
      omega
    simp only [List.cons_append, inv01]
    rw [hones, ih]
    omega

theorem swap_srs_decreases {u v : List Nat} (h : SRSStep swapRules u v) : inv01 v < inv01 u := by
  obtain ⟨rule, hr, x, y, rfl, rfl⟩ := h
  simp only [swapRules, List.mem_singleton] at hr
  subst hr
  have := inv01_append_swap x y
  dsimp only
  omega

/-- String rewriting with `01 → 10` terminates. -/
theorem swap_srs_terminates : WellFounded (fun v u => SRSStep swapRules u v) :=
  Subrelation.wf (fun {_ _} h => swap_srs_decreases h) (InvImage.wf inv01 Nat.lt_wfRel.wf)

/-- Cycle rewriting with `01 → 10` has a self-loop on the cycle `01`. -/
theorem swap_cycle_loop : CycleStep swapRules [0, 1] [0, 1] :=
  ⟨[0, 1], [1, 0], rotation_refl _,
    ⟨⟨[0, 1], [1, 0]⟩, by simp [swapRules], [], [], rfl, rfl⟩, ⟨[1], [0], rfl, rfl⟩⟩

theorem swap_cycle_not_terminating : ¬ WellFounded (fun v u => CycleStep swapRules u v) :=
  fun h => (h.asymmetric _ _ swap_cycle_loop) swap_cycle_loop

/-- The defining feature of cycle rewriting: rotation turns a terminating string system into a
nonterminating cycle system. -/
theorem cycleRewriting_feature :
    WellFounded (fun v u => SRSStep swapRules u v) ∧
      ¬ WellFounded (fun v u => CycleStep swapRules u v) :=
  ⟨swap_srs_terminates, swap_cycle_not_terminating⟩

/-- Deleting the letter `0`. -/
def deleteRules : List (SRule Nat) := [⟨[0], []⟩]

theorem delete_cycle_decreases {u v : List Nat} (h : CycleStep deleteRules u v) :
    v.length < u.length := by
  obtain ⟨u', v', h1, h2, h3⟩ := h
  obtain ⟨rule, hr, hlen⟩ := srsStep_length h2
  simp only [deleteRules, List.mem_singleton] at hr
  subst hr
  have e1 := rotation_length h1
  have e3 := rotation_length h3
  simp only [List.length_cons, List.length_nil] at hlen
  omega

/-- An admitted cycle system: deleting a letter terminates on cycles. -/
theorem delete_cycle_terminates : WellFounded (fun v u => CycleStep deleteRules u v) :=
  Subrelation.wf (fun {_ _} h => delete_cycle_decreases h)
    (InvImage.wf List.length Nat.lt_wfRel.wf)

/-! ### String encodings of free terms -/

/-- Data of a string-based method applied to the free recursor: a finite string system over the
letters `Nat`, an encoding of ground free terms, and the length constants of the encoding. -/
structure StringMethodData where
  rules : List (SRule Nat)
  enc : FreeTerm Empty → List Nat
  cz : Nat
  cs : Nat
  cw : Nat
  cr : Nat

/-- The encoding has compositional length and a nonempty code for `zero`. -/
def CompositionalLength (M : StringMethodData) : Prop :=
  1 ≤ M.cz ∧ (M.enc .zero).length = M.cz ∧
    (∀ t, (M.enc (.succ t)).length = M.cs + (M.enc t).length) ∧
    (∀ s t, (M.enc (.wrap s t)).length = M.cw + (M.enc s).length + (M.enc t).length) ∧
    (∀ b s n, (M.enc (.recur b s n)).length =
      M.cr + (M.enc b).length + (M.enc s).length + (M.enc n).length)

/-- Wrapper chains with `k + 1` leaves. -/
def leafChain : Nat → FreeTerm Empty
  | 0 => .zero
  | k + 1 => .wrap .zero (leafChain k)

theorem leafChain_length (M : StringMethodData) (hM : CompositionalLength M) (k : Nat) :
    k + 1 ≤ (M.enc (leafChain k)).length := by
  obtain ⟨hcz, hz, -, hw, -⟩ := hM
  induction k with
  | zero =>
    simp only [leafChain]
    omega
  | succ k ih =>
    simp only [leafChain]
    rw [hw, hz]
    omega

/-- The duplicating step at payload `s` lengthens the code by `cw + |enc s| - cs`. -/
theorem dup_length_gap (M : StringMethodData) (hM : CompositionalLength M) (s : FreeTerm Empty) :
    (M.enc (.wrap s (.recur .zero s .zero))).length + M.cs =
      (M.enc (.recur .zero s (.succ .zero))).length + M.cw + (M.enc s).length := by
  obtain ⟨-, -, hs, hw, hr⟩ := hM
  simp only [hw, hr, hs]
  omega

/-- No relation that lengthens words by a bounded amount performs every ground duplicating step
under an encoding with compositional length. -/
theorem encoding_barrier (M : StringMethodData) (hM : CompositionalLength M) (K : Nat)
    (step : List Nat → List Nat → Prop) (hK : ∀ {u v}, step u v → v.length ≤ u.length + K)
    (hsim : ∀ b s n : FreeTerm Empty,
      step (M.enc (.recur b s (.succ n))) (M.enc (.wrap s (.recur b s n)))) : False := by
  have hlen := leafChain_length M hM (K + M.cs)
  have hstep := hK (hsim .zero (leafChain (K + M.cs)) .zero)
  have hgap := dup_length_gap M hM (leafChain (K + M.cs))
  omega

/-- The prefix (Polish) code of a ground free term. -/
def polish : FreeTerm Empty → List Nat
  | .var x => nomatch x
  | .zero => [0]
  | .succ t => 1 :: polish t
  | .wrap s t => 2 :: (polish s ++ polish t)
  | .recur b s n => 3 :: (polish b ++ polish s ++ polish n)

theorem polish_append_inj (t : FreeTerm Empty) :
    ∀ (t' : FreeTerm Empty) (l l' : List Nat), polish t ++ l = polish t' ++ l' → t = t' ∧ l = l' := by
  induction t with
  | var x => exact nomatch x
  | zero =>
    intro t' l l' h
    cases t' with
    | var x => exact nomatch x
    | zero =>
      simp only [polish, List.cons_append, List.nil_append] at h
      exact ⟨rfl, (List.cons.inj h).2⟩
    | succ u => simp [polish] at h
    | wrap s u => simp [polish] at h
    | recur b s n => simp [polish] at h
  | succ u ih =>
    intro t' l l' h
    cases t' with
    | var x => exact nomatch x
    | zero => simp [polish] at h
    | succ u' =>
      simp only [polish, List.cons_append] at h
      obtain ⟨rfl, rfl⟩ := ih u' l l' (List.cons.inj h).2
      exact ⟨rfl, rfl⟩
    | wrap s u' => simp [polish] at h
    | recur b s n => simp [polish] at h
  | wrap s u ihs ihu =>
    intro t' l l' h
    cases t' with
    | var x => exact nomatch x
    | zero => simp [polish] at h
    | succ u' => simp [polish] at h
    | wrap s' u' =>
      simp only [polish, List.cons_append, List.append_assoc] at h
      obtain ⟨rfl, h2⟩ := ihs s' _ _ (List.cons.inj h).2
      obtain ⟨rfl, rfl⟩ := ihu u' l l' h2
      exact ⟨rfl, rfl⟩
    | recur b s' n => simp [polish] at h
  | recur b s n ihb ihs ihn =>
    intro t' l l' h
    cases t' with
    | var x => exact nomatch x
    | zero => simp [polish] at h
    | succ u' => simp [polish] at h
    | wrap s' u' => simp [polish] at h
    | recur b' s' n' =>
      simp only [polish, List.cons_append, List.append_assoc] at h
      obtain ⟨rfl, h2⟩ := ihb b' _ _ (List.cons.inj h).2
      obtain ⟨rfl, h3⟩ := ihs s' _ _ h2
      obtain ⟨rfl, rfl⟩ := ihn n' l l' h3
      exact ⟨rfl, rfl⟩

/-- Free terms are representable as words: the prefix code is injective. -/
theorem polish_injective : Function.Injective polish := fun t t' h =>
  (polish_append_inj t t' [] [] (by simpa using h)).1

/-- The unary rule `succ (succ x) → succ x` as a string rule on prefix codes. -/
def unaryRules : List (SRule Nat) := [⟨[1, 1], [1]⟩]

/-- `k` successors on top of a term. -/
def succPow : Nat → FreeTerm Empty → FreeTerm Empty
  | 0, t => t
  | k + 1, t => .succ (succPow k t)

theorem polish_succPow (k : Nat) (t : FreeTerm Empty) :
    polish (succPow k t) = List.replicate k 1 ++ polish t := by
  induction k with
  | zero => simp [succPow]
  | succ k ih => simp [succPow, polish, ih, List.replicate_succ]

/-- On the unary fragment the string rule performs the term rule exactly. -/
theorem unary_rule_simulated (k : Nat) :
    SRSStep unaryRules (polish (succPow (k + 2) .zero)) (polish (succPow (k + 1) .zero)) := by
  refine ⟨⟨[1, 1], [1]⟩, by simp [unaryRules], [], List.replicate k 1 ++ [0], ?_, ?_⟩
  · rw [polish_succPow]
    simp [List.replicate_succ, polish]
  · rw [polish_succPow]
    simp [List.replicate_succ, polish]

theorem unary_srs_decreases {u v : List Nat} (h : SRSStep unaryRules u v) :
    v.length < u.length := by
  obtain ⟨rule, hr, hlen⟩ := srsStep_length h
  simp only [unaryRules, List.mem_singleton] at hr
  subst hr
  simp only [List.length_cons, List.length_nil] at hlen
  omega

/-- An admitted string system: the unary rule terminates. -/
theorem unary_srs_terminates : WellFounded (fun v u => SRSStep unaryRules u v) :=
  Subrelation.wf (fun {_ _} h => unary_srs_decreases h) (InvImage.wf List.length Nat.lt_wfRel.wf)

/-- The prefix code with the unary string system. -/
def polishData : StringMethodData where
  rules := unaryRules
  enc := polish
  cz := 1
  cs := 1
  cw := 1
  cr := 1

theorem polishData_laws : CompositionalLength polishData := by
  refine ⟨le_rfl, rfl, ?_, ?_, ?_⟩
  · intro t
    simp only [polishData, polish, List.length_cons]
    omega
  · intro s t
    simp only [polishData, polish, List.length_cons, List.length_append]
    omega
  · intro b s n
    simp only [polishData, polish, List.length_cons, List.length_append]
    omega

/-- The degenerate encoding: every term is the empty word, with the empty rule. -/
def degenerateStringData : StringMethodData where
  rules := [⟨[], []⟩]
  enc := fun _ => []
  cz := 0
  cs := 0
  cw := 0
  cr := 0

/-! ### Row: stringRewritingInapplicability -/

/-- Native data: a finite string system with a string encoding of the free terms. -/
abbrev stringRewritingInapplicabilityData : Type := StringMethodData

/-- String rewriting (Book and Otto 1993, Chapter 2) applied through an encoding with
compositional length and a nonempty code for `zero`. -/
def stringRewritingInapplicabilityLaws (M : stringRewritingInapplicabilityData) : Prop :=
  CompositionalLength M

/-- The method performs every ground duplicating step as one string step. -/
def stringRewritingInapplicabilityAccepts (M : stringRewritingInapplicabilityData) : Prop :=
  ∀ b s n : FreeTerm Empty,
    SRSStep M.rules (M.enc (.recur b s (.succ n))) (M.enc (.wrap s (.recur b s n)))

/-- Verdict: barrier (one-step string simulation of the duplicating rule is impossible). -/
def stringRewritingInapplicabilityResult (M : stringRewritingInapplicabilityData) : Prop :=
  ¬ stringRewritingInapplicabilityAccepts M

theorem stringRewritingInapplicability_universal :
    ∀ M, stringRewritingInapplicabilityLaws M → stringRewritingInapplicabilityResult M :=
  fun M hM hacc => encoding_barrier M hM (sumRhs M.rules) (SRSStep M.rules)
    (fun h => srsStep_length_le h) hacc

def stringRewritingInapplicabilityWitness : stringRewritingInapplicabilityData := polishData

theorem stringRewritingInapplicabilityWitness_laws :
    stringRewritingInapplicabilityLaws stringRewritingInapplicabilityWitness :=
  polishData_laws

theorem stringRewritingInapplicabilityWitness_result :
    stringRewritingInapplicabilityResult stringRewritingInapplicabilityWitness :=
  stringRewritingInapplicability_universal _ stringRewritingInapplicabilityWitness_laws

/-- The witness code is injective, and its unary fragment performs the unary term rule exactly with
a terminating string system. -/
theorem stringRewritingInapplicabilityWitness_feature :
    Function.Injective stringRewritingInapplicabilityWitness.enc ∧
      (∀ k, SRSStep stringRewritingInapplicabilityWitness.rules
        (stringRewritingInapplicabilityWitness.enc (succPow (k + 2) .zero))
        (stringRewritingInapplicabilityWitness.enc (succPow (k + 1) .zero))) ∧
      WellFounded (fun v u => SRSStep stringRewritingInapplicabilityWitness.rules u v) :=
  ⟨polish_injective, unary_rule_simulated, unary_srs_terminates⟩

/-- Changing the code of `zero` to the empty word (all other lengths follow) breaks the law
`1 ≤ cz`, and the degenerate encoding is then accepted. -/
theorem stringRewritingInapplicability_mutation :
    ¬ stringRewritingInapplicabilityLaws degenerateStringData ∧
      stringRewritingInapplicabilityAccepts degenerateStringData := by
  refine ⟨fun h => ?_, fun b s n => ?_⟩
  · have := h.1
    simp [degenerateStringData] at this
  · exact ⟨⟨[], []⟩, by simp [degenerateStringData], [], [], rfl, rfl⟩

/-! ### Row: cycleRewritingInapplicability -/

/-- Native data: a finite cycle system with a string encoding of the free terms. -/
abbrev cycleRewritingInapplicabilityData : Type := StringMethodData

/-- Cycle rewriting (Zantema, König and Bruggink 2014) applied through an encoding with
compositional length and a nonempty code for `zero`. -/
def cycleRewritingInapplicabilityLaws (M : cycleRewritingInapplicabilityData) : Prop :=
  CompositionalLength M

/-- The method performs every ground duplicating step as one cycle step. -/
def cycleRewritingInapplicabilityAccepts (M : cycleRewritingInapplicabilityData) : Prop :=
  ∀ b s n : FreeTerm Empty,
    CycleStep M.rules (M.enc (.recur b s (.succ n))) (M.enc (.wrap s (.recur b s n)))

/-- Verdict: barrier (one-step cycle simulation of the duplicating rule is impossible). -/
def cycleRewritingInapplicabilityResult (M : cycleRewritingInapplicabilityData) : Prop :=
  ¬ cycleRewritingInapplicabilityAccepts M

theorem cycleRewritingInapplicability_universal :
    ∀ M, cycleRewritingInapplicabilityLaws M → cycleRewritingInapplicabilityResult M :=
  fun M hM hacc => encoding_barrier M hM (sumRhs M.rules) (CycleStep M.rules)
    (fun h => cycleStep_length_le h) hacc

def cycleRewritingInapplicabilityWitness : cycleRewritingInapplicabilityData := polishData

theorem cycleRewritingInapplicabilityWitness_laws :
    cycleRewritingInapplicabilityLaws cycleRewritingInapplicabilityWitness :=
  polishData_laws

theorem cycleRewritingInapplicabilityWitness_result :
    cycleRewritingInapplicabilityResult cycleRewritingInapplicabilityWitness :=
  cycleRewritingInapplicability_universal _ cycleRewritingInapplicabilityWitness_laws

/-- Rotation separates cycle from string termination, and a deleting cycle system is admitted. -/
theorem cycleRewritingInapplicabilityWitness_feature :
    (WellFounded (fun v u => SRSStep swapRules u v) ∧
      ¬ WellFounded (fun v u => CycleStep swapRules u v)) ∧
      WellFounded (fun v u => CycleStep deleteRules u v) :=
  ⟨cycleRewriting_feature, delete_cycle_terminates⟩

theorem cycleRewritingInapplicability_mutation :
    ¬ cycleRewritingInapplicabilityLaws degenerateStringData ∧
      cycleRewritingInapplicabilityAccepts degenerateStringData :=
  ⟨stringRewritingInapplicability_mutation.1,
    fun b s n => cycleStep_of_srsStep (stringRewritingInapplicability_mutation.2 b s n)⟩

/-! ## Rewriting modulo equations -/

/-- One replacement by an instance of an equation of `E`, inside a context. -/
inductive EqStep (E : List (FreeTerm Nat × FreeTerm Nat)) : FreeTerm Nat → FreeTerm Nat → Prop
  | lift (C : FreeContext Nat) (σ : Nat → FreeTerm Nat) {l r : FreeTerm Nat} (h : (l, r) ∈ E) :
      EqStep E (C.plug (l.subst σ)) (C.plug (r.subst σ))

/-- The congruence generated by `E`. -/
def ECongr (E : List (FreeTerm Nat × FreeTerm Nat)) : FreeTerm Nat → FreeTerm Nat → Prop :=
  Relation.EqvGen (EqStep E)

/-- Rewriting modulo `E` (Jouannaud and Kirchner, SIAM J. Comput. 1986): a free step between
`E`-equivalent terms. -/
def ModStep (E : List (FreeTerm Nat × FreeTerm Nat)) (t u : FreeTerm Nat) : Prop :=
  ∃ t' u', ECongr E t t' ∧ ContextStep t' u' ∧ ECongr E u' u

theorem modStep_of_contextStep (E : List (FreeTerm Nat × FreeTerm Nat)) {t u : FreeTerm Nat}
    (h : ContextStep t u) : ModStep E t u :=
  ⟨t, u, Relation.EqvGen.refl t, h, Relation.EqvGen.refl u⟩

/-- Termination modulo `E` gives termination of the free system. -/
theorem wf_of_modStep_wf (E : List (FreeTerm Nat × FreeTerm Nat))
    (h : WellFounded (fun u t => ModStep E t u)) :
    WellFounded (fun u t : FreeTerm Nat => ContextStep t u) :=
  Subrelation.wf (fun {_ _} hs => modStep_of_contextStep E hs) h

/-- Variables of a free term. -/
def freeVars : FreeTerm Nat → List Nat
  | .var x => [x]
  | .zero => []
  | .succ t => freeVars t
  | .wrap s t => freeVars s ++ freeVars t
  | .recur b s n => freeVars b ++ freeVars s ++ freeVars n

/-- Regular equations: both sides carry the same variables. -/
def RegularEquations (E : List (FreeTerm Nat × FreeTerm Nat)) : Prop :=
  ∀ p ∈ E, ∀ x, x ∈ freeVars p.1 ↔ x ∈ freeVars p.2

/-- A polynomial weight on free terms that is symmetric in the wrapper. -/
def qw : FreeTerm Nat → Nat
  | .var _ => 0
  | .zero => 1
  | .succ t => qw t + 1
  | .wrap s t => qw s + qw t + 1
  | .recur b s n => qw b + (qw s + 2) * (qw n + 1)

theorem qw_rootStep {t u : FreeTerm Nat} (h : RootStep t u) : qw u < qw t := by
  cases h with
  | recurZero b s =>
    simp only [qw]
    nlinarith
  | recurSucc b s n =>
    simp only [qw]
    nlinarith

theorem qw_plug_lt (C : FreeContext Nat) {a b : FreeTerm Nat} (h : qw b < qw a) :
    qw (C.plug b) < qw (C.plug a) := by
  induction C with
  | hole => simpa using h
  | succ C ih =>
    simp only [FreeContext.plug, qw]
    omega
  | wrapLeft C r ih =>
    simp only [FreeContext.plug, qw]
    omega
  | wrapRight l C ih =>
    simp only [FreeContext.plug, qw]
    omega
  | recurBase C s n ih =>
    simp only [FreeContext.plug, qw]
    omega
  | recurStep x C n ih =>
    simp only [FreeContext.plug, qw]
    have hpos : 0 < qw n + 1 := Nat.succ_pos _
    nlinarith
  | recurCounter x s C ih =>
    simp only [FreeContext.plug, qw]
    have hpos : 0 < qw s + 2 := by omega
    nlinarith

theorem qw_contextStep {t u : FreeTerm Nat} (h : ContextStep t u) : qw u < qw t := by
  cases h with
  | lift C hr => exact qw_plug_lt C (qw_rootStep hr)

theorem qw_plug_eq (C : FreeContext Nat) {a b : FreeTerm Nat} (h : qw a = qw b) :
    qw (C.plug a) = qw (C.plug b) := by
  induction C with
  | hole => simpa using h
  | succ C ih => simp only [FreeContext.plug, qw, ih]
  | wrapLeft C r ih => simp only [FreeContext.plug, qw, ih]
  | wrapRight l C ih => simp only [FreeContext.plug, qw, ih]
  | recurBase C s n ih => simp only [FreeContext.plug, qw, ih]
  | recurStep x C n ih => simp only [FreeContext.plug, qw, ih]
  | recurCounter x s C ih => simp only [FreeContext.plug, qw, ih]

/-- Commutativity of the wrapper. -/
def commEquations : List (FreeTerm Nat × FreeTerm Nat) :=
  [(.wrap (.var 0) (.var 1), .wrap (.var 1) (.var 0))]

theorem qw_eqStep_comm {t u : FreeTerm Nat} (h : EqStep commEquations t u) : qw t = qw u := by
  cases h with
  | lift C σ hmem =>
    simp only [commEquations, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    apply qw_plug_eq
    simp only [FreeTerm.subst, qw]
    omega

theorem qw_eCongr_comm {t u : FreeTerm Nat} (h : ECongr commEquations t u) : qw t = qw u := by
  unfold ECongr at h
  induction h with
  | rel x y h => exact qw_eqStep_comm h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem qw_modStep_comm {t u : FreeTerm Nat} (h : ModStep commEquations t u) : qw u < qw t := by
  obtain ⟨t', u', h1, h2, h3⟩ := h
  have e1 := qw_eCongr_comm h1
  have e3 := qw_eCongr_comm h3
  have := qw_contextStep h2
  omega

/-- The free system terminates modulo commutativity of the wrapper. -/
theorem comm_modStep_wf : WellFounded (fun u t => ModStep commEquations t u) :=
  Subrelation.wf (fun {_ _} h => qw_modStep_comm h) (InvImage.wf qw Nat.lt_wfRel.wf)

/-- Terms without a recursor node. -/
def RecurFree : FreeTerm Nat → Prop
  | .var _ => True
  | .zero => True
  | .succ t => RecurFree t
  | .wrap s t => RecurFree s ∧ RecurFree t
  | .recur _ _ _ => False

theorem recurFree_plug {C : FreeContext Nat} {a : FreeTerm Nat} (h : RecurFree (C.plug a)) :
    RecurFree a := by
  induction C with
  | hole => simpa using h
  | succ C ih => exact ih h
  | wrapLeft C r ih => exact ih h.1
  | wrapRight l C ih => exact ih h.2
  | recurBase C s n ih => exact h.elim
  | recurStep x C n ih => exact h.elim
  | recurCounter x s C ih => exact h.elim

theorem not_contextStep_of_recurFree {t u : FreeTerm Nat} (ht : RecurFree t) :
    ¬ ContextStep t u := by
  intro h
  cases h with
  | lift C hr =>
    have ha := recurFree_plug ht
    cases hr <;> exact ha

/-- Two distinct normal forms of the free system. -/
def nfLeft : FreeTerm Nat := .wrap .zero (.succ .zero)

def nfRight : FreeTerm Nat := .wrap (.succ .zero) .zero

/-- Commutativity identifies two distinct normal forms of the free system. -/
theorem comm_merges_normal_forms :
    nfLeft ≠ nfRight ∧ (∀ u, ¬ ContextStep nfLeft u) ∧ (∀ u, ¬ ContextStep nfRight u) ∧
      ECongr commEquations nfLeft nfRight := by
  refine ⟨by decide, fun u => not_contextStep_of_recurFree (by simp [nfLeft, RecurFree]),
    fun u => not_contextStep_of_recurFree (by simp [nfRight, RecurFree]), ?_⟩
  apply Relation.EqvGen.rel
  have h := EqStep.lift (E := commEquations) FreeContext.hole
    (fun x => if x = 0 then (FreeTerm.zero : FreeTerm Nat) else .succ .zero)
    (l := .wrap (.var 0) (.var 1)) (r := .wrap (.var 1) (.var 0)) (by simp [commEquations])
  simpa [nfLeft, nfRight] using h

/-- One ground equation that returns `zero` to a recursor redex. -/
def loopEquations : List (FreeTerm Nat × FreeTerm Nat) := [(.zero, .recur .zero .zero .zero)]

theorem commEquations_regular : RegularEquations commEquations := by
  intro p hp x
  simp only [commEquations, List.mem_singleton] at hp
  subst hp
  simp only [freeVars, List.mem_append, List.mem_singleton]
  tauto

theorem loopEquations_regular : RegularEquations loopEquations := by
  intro p hp x
  simp only [loopEquations, List.mem_singleton] at hp
  subst hp
  simp [freeVars]

theorem loop_modStep : ModStep loopEquations .zero .zero := by
  refine ⟨.recur .zero .zero .zero, .zero, ?_, rootStep_contextStep (.recurZero _ _),
    Relation.EqvGen.refl _⟩
  apply Relation.EqvGen.rel
  have h := EqStep.lift (E := loopEquations) FreeContext.hole (fun _ => FreeTerm.zero)
    (l := .zero) (r := .recur .zero .zero .zero) (by simp [loopEquations])
  simpa using h

/-! ### Row: equationalQuotientNonConservativity -/

/-- Native data: a finite list of equations over the free signature. -/
abbrev equationalQuotientNonConservativityData : Type := List (FreeTerm Nat × FreeTerm Nat)

/-- Rewriting modulo a set of regular equations (Jouannaud and Kirchner 1986). -/
def equationalQuotientNonConservativityLaws (E : equationalQuotientNonConservativityData) :
    Prop :=
  RegularEquations E

/-- The quotient system terminates. -/
def equationalQuotientNonConservativityAccepts (E : equationalQuotientNonConservativityData) :
    Prop :=
  WellFounded (fun u t => ModStep E t u)

/-- Verdict: escape on the quotient, nonconservative over the free system. -/
def equationalQuotientNonConservativityResult (E : equationalQuotientNonConservativityData) :
    Prop :=
  equationalQuotientNonConservativityAccepts E ∧
    WellFounded (fun u t : FreeTerm Nat => ContextStep t u)

/-- Soundness: termination of the quotient gives termination of the free system. -/
theorem equationalQuotientNonConservativity_sound :
    ∀ E, equationalQuotientNonConservativityLaws E →
      equationalQuotientNonConservativityAccepts E →
        WellFounded (fun u t : FreeTerm Nat => ContextStep t u) :=
  fun E _ h => wf_of_modStep_wf E h

def equationalQuotientNonConservativityWitness : equationalQuotientNonConservativityData :=
  commEquations

theorem equationalQuotientNonConservativityWitness_laws :
    equationalQuotientNonConservativityLaws equationalQuotientNonConservativityWitness :=
  commEquations_regular

theorem equationalQuotientNonConservativityWitness_result :
    equationalQuotientNonConservativityResult equationalQuotientNonConservativityWitness :=
  ⟨comm_modStep_wf, main_free_contextual_termination Nat⟩

/-- The witness quotient identifies two distinct normal forms of the free system. -/
theorem equationalQuotientNonConservativityWitness_feature :
    nfLeft ≠ nfRight ∧ (∀ u, ¬ ContextStep nfLeft u) ∧ (∀ u, ¬ ContextStep nfRight u) ∧
      ECongr equationalQuotientNonConservativityWitness nfLeft nfRight :=
  comm_merges_normal_forms

/-- Replacing the equation by one regular ground equation makes the quotient loop while the free
system terminates. -/
theorem equationalQuotientNonConservativity_mutation :
    equationalQuotientNonConservativityLaws loopEquations ∧
      ¬ equationalQuotientNonConservativityAccepts loopEquations ∧
      WellFounded (fun u t : FreeTerm Nat => ContextStep t u) :=
  ⟨loopEquations_regular, fun h => (h.asymmetric _ _ loop_modStep) loop_modStep,
    main_free_contextual_termination Nat⟩

/-! ## Term graph rewriting under maximal sharing -/

/-- Replace every occurrence of `a` by `b`; on a maximally shared term graph this is one redirection
of the node `a`. -/
def replaceAll (a b : FreeTerm Nat) : FreeTerm Nat → FreeTerm Nat
  | .var x => if FreeTerm.var x = a then b else .var x
  | .zero => if FreeTerm.zero = a then b else .zero
  | .succ t => if FreeTerm.succ t = a then b else .succ (replaceAll a b t)
  | .wrap s t => if FreeTerm.wrap s t = a then b else .wrap (replaceAll a b s) (replaceAll a b t)
  | .recur x s n =>
      if FreeTerm.recur x s n = a then b else
        .recur (replaceAll a b x) (replaceAll a b s) (replaceAll a b n)

/-- `a` occurs in `t`. -/
def Occurs (a t : FreeTerm Nat) : Prop := ∃ C : FreeContext Nat, t = C.plug a

/-- One step of term graph rewriting under maximal sharing (Plump, Term graph rewriting, Handbook
of Graph Grammars 1999): every occurrence of one redex is contracted at once. -/
def SharedStep (t u : FreeTerm Nat) : Prop :=
  ∃ a b, RootStep a b ∧ Occurs a t ∧ u = replaceAll a b t

theorem rtg_plug (C : FreeContext Nat) {x y : FreeTerm Nat}
    (h : Relation.ReflTransGen ContextStep x y) :
    Relation.ReflTransGen ContextStep (C.plug x) (C.plug y) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (hst.outer C)

theorem tg_plug (C : FreeContext Nat) {x y : FreeTerm Nat}
    (h : Relation.TransGen ContextStep x y) :
    Relation.TransGen ContextStep (C.plug x) (C.plug y) := by
  induction h with
  | single hst => exact .single (hst.outer C)
  | tail _ hst ih => exact ih.tail (hst.outer C)

theorem tg_of_rtg_tg {α : Type} {r : α → α → Prop} {a b c : α}
    (h₁ : Relation.ReflTransGen r a b) (h₂ : Relation.TransGen r b c) :
    Relation.TransGen r a c := by
  induction h₂ with
  | single hbc => exact Relation.TransGen.tail' h₁ hbc
  | tail _ hcd ih => exact ih.tail hcd

theorem replaceAll_rtg {a b : FreeTerm Nat} (hab : RootStep a b) (t : FreeTerm Nat) :
    Relation.ReflTransGen ContextStep t (replaceAll a b t) := by
  induction t with
  | var x =>
    simp only [replaceAll]
    split_ifs with h
    · subst h
      exact .single (rootStep_contextStep hab)
    · exact .refl
  | zero =>
    simp only [replaceAll]
    split_ifs with h
    · subst h
      exact .single (rootStep_contextStep hab)
    · exact .refl
  | succ t ih =>
    simp only [replaceAll]
    split_ifs with h
    · subst h
      exact .single (rootStep_contextStep hab)
    · exact rtg_plug (.succ .hole) ih
  | wrap s t ihs iht =>
    simp only [replaceAll]
    split_ifs with h
    · subst h
      exact .single (rootStep_contextStep hab)
    · exact (rtg_plug (.wrapLeft .hole t) ihs).trans
        (rtg_plug (.wrapRight (replaceAll a b s) .hole) iht)
  | recur x s n ihx ihs ihn =>
    simp only [replaceAll]
    split_ifs with h
    · subst h
      exact .single (rootStep_contextStep hab)
    · exact ((rtg_plug (.recurBase .hole s n) ihx).trans
        (rtg_plug (.recurStep (replaceAll a b x) .hole n) ihs)).trans
        (rtg_plug (.recurCounter (replaceAll a b x) (replaceAll a b s) .hole) ihn)

theorem occurs_var {a : FreeTerm Nat} {x : Nat} (h : Occurs a (.var x)) : FreeTerm.var x = a := by
  obtain ⟨C, hC⟩ := h
  cases C with
  | hole => exact hC
  | succ C => simp [FreeContext.plug] at hC
  | wrapLeft C r => simp [FreeContext.plug] at hC
  | wrapRight l C => simp [FreeContext.plug] at hC
  | recurBase C s n => simp [FreeContext.plug] at hC
  | recurStep y C n => simp [FreeContext.plug] at hC
  | recurCounter y s C => simp [FreeContext.plug] at hC

theorem occurs_zero {a : FreeTerm Nat} (h : Occurs a .zero) : FreeTerm.zero = a := by
  obtain ⟨C, hC⟩ := h
  cases C with
  | hole => exact hC
  | succ C => simp [FreeContext.plug] at hC
  | wrapLeft C r => simp [FreeContext.plug] at hC
  | wrapRight l C => simp [FreeContext.plug] at hC
  | recurBase C s n => simp [FreeContext.plug] at hC
  | recurStep y C n => simp [FreeContext.plug] at hC
  | recurCounter y s C => simp [FreeContext.plug] at hC

theorem occurs_succ {a t : FreeTerm Nat} (h : Occurs a (.succ t)) :
    FreeTerm.succ t = a ∨ Occurs a t := by
  obtain ⟨C, hC⟩ := h
  cases C with
  | hole => exact Or.inl hC
  | succ C => exact Or.inr ⟨C, by simpa [FreeContext.plug] using hC⟩
  | wrapLeft C r => simp [FreeContext.plug] at hC
  | wrapRight l C => simp [FreeContext.plug] at hC
  | recurBase C s n => simp [FreeContext.plug] at hC
  | recurStep y C n => simp [FreeContext.plug] at hC
  | recurCounter y s C => simp [FreeContext.plug] at hC

theorem occurs_wrap {a s t : FreeTerm Nat} (h : Occurs a (.wrap s t)) :
    FreeTerm.wrap s t = a ∨ Occurs a s ∨ Occurs a t := by
  obtain ⟨C, hC⟩ := h
  cases C with
  | hole => exact Or.inl hC
  | succ C => simp [FreeContext.plug] at hC
  | wrapLeft C r =>
    simp only [FreeContext.plug, FreeTerm.wrap.injEq] at hC
    exact Or.inr (Or.inl ⟨C, hC.1⟩)
  | wrapRight l C =>
    simp only [FreeContext.plug, FreeTerm.wrap.injEq] at hC
    exact Or.inr (Or.inr ⟨C, hC.2⟩)
  | recurBase C s n => simp [FreeContext.plug] at hC
  | recurStep y C n => simp [FreeContext.plug] at hC
  | recurCounter y s C => simp [FreeContext.plug] at hC

theorem occurs_recur {a x s n : FreeTerm Nat} (h : Occurs a (.recur x s n)) :
    FreeTerm.recur x s n = a ∨ Occurs a x ∨ Occurs a s ∨ Occurs a n := by
  obtain ⟨C, hC⟩ := h
  cases C with
  | hole => exact Or.inl hC
  | succ C => simp [FreeContext.plug] at hC
  | wrapLeft C r => simp [FreeContext.plug] at hC
  | wrapRight l C => simp [FreeContext.plug] at hC
  | recurBase C s' n' =>
    simp only [FreeContext.plug, FreeTerm.recur.injEq] at hC
    exact Or.inr (Or.inl ⟨C, hC.1⟩)
  | recurStep y C n' =>
    simp only [FreeContext.plug, FreeTerm.recur.injEq] at hC
    exact Or.inr (Or.inr (Or.inl ⟨C, hC.2.1⟩))
  | recurCounter y s' C =>
    simp only [FreeContext.plug, FreeTerm.recur.injEq] at hC
    exact Or.inr (Or.inr (Or.inr ⟨C, hC.2.2⟩))

/-- Contracting every occurrence of a redex that occurs performs at least one term step. -/
theorem replaceAll_tg {a b : FreeTerm Nat} (hab : RootStep a b) :
    ∀ t : FreeTerm Nat, Occurs a t → Relation.TransGen ContextStep t (replaceAll a b t) := by
  intro t
  induction t with
  | var x =>
    intro hocc
    simp only [replaceAll]
    split_ifs with h
    · subst h
      exact .single (rootStep_contextStep hab)
    · exact absurd (occurs_var hocc) h
  | zero =>
    intro hocc
    simp only [replaceAll]
    split_ifs with h
    · subst h
      exact .single (rootStep_contextStep hab)
    · exact absurd (occurs_zero hocc) h
  | succ t ih =>
    intro hocc
    simp only [replaceAll]
    split_ifs with h
    · subst h
      exact .single (rootStep_contextStep hab)
    · rcases occurs_succ hocc with h' | h'
      · exact absurd h' h
      · exact tg_plug (.succ .hole) (ih h')
  | wrap s t ihs iht =>
    intro hocc
    simp only [replaceAll]
    split_ifs with h
    · subst h
      exact .single (rootStep_contextStep hab)
    · rcases occurs_wrap hocc with h' | h' | h'
      · exact absurd h' h
      · exact Relation.TransGen.trans_left (tg_plug (.wrapLeft .hole t) (ihs h'))
          (rtg_plug (.wrapRight (replaceAll a b s) .hole) (replaceAll_rtg hab t))
      · exact tg_of_rtg_tg (rtg_plug (.wrapLeft .hole t) (replaceAll_rtg hab s))
          (tg_plug (.wrapRight (replaceAll a b s) .hole) (iht h'))
  | recur x s n ihx ihs ihn =>
    intro hocc
    simp only [replaceAll]
    split_ifs with h
    · subst h
      exact .single (rootStep_contextStep hab)
    · have rx := rtg_plug (.recurBase .hole s n) (replaceAll_rtg hab x)
      have rs := rtg_plug (.recurStep (replaceAll a b x) .hole n) (replaceAll_rtg hab s)
      have rn := rtg_plug (.recurCounter (replaceAll a b x) (replaceAll a b s) .hole)
        (replaceAll_rtg hab n)
      rcases occurs_recur hocc with h' | h' | h' | h'
      · exact absurd h' h
      · exact Relation.TransGen.trans_left
          (Relation.TransGen.trans_left (tg_plug (.recurBase .hole s n) (ihx h')) rs) rn
      · exact Relation.TransGen.trans_left
          (tg_of_rtg_tg rx (tg_plug (.recurStep (replaceAll a b x) .hole n) (ihs h'))) rn
      · exact tg_of_rtg_tg (rx.trans rs)
          (tg_plug (.recurCounter (replaceAll a b x) (replaceAll a b s) .hole) (ihn h'))

/-- Every shared step is a nonempty sequence of term steps. -/
theorem sharedStep_simulates : Simulates ContextStep SharedStep id := by
  intro t u h
  obtain ⟨a, b, hab, hocc, rfl⟩ := h
  exact replaceAll_tg hab t hocc

/-- The free system terminates under maximal sharing. -/
theorem sharedStep_wellFounded : WellFounded (fun u t : FreeTerm Nat => SharedStep t u) :=
  wf_of_simulates sharedStep_simulates (main_free_contextual_termination Nat)

theorem contextStep_iff {t u : FreeTerm Nat} :
    ContextStep t u ↔ ∃ C a b, RootStep a b ∧ t = FreeContext.plug C a ∧ u = FreeContext.plug C b := by
  constructor
  · rintro ⟨C, h⟩
    exact ⟨C, _, _, h, rfl, rfl⟩
  · rintro ⟨C, a, b, h, rfl, rfl⟩
    exact .lift C h

/-- A recursor redex and its contractum. -/
def costRedex : FreeTerm Nat := .recur .zero .zero (.succ .zero)

def costContractum : FreeTerm Nat := .wrap .zero (.recur .zero .zero .zero)

theorem cost_rootStep : RootStep costRedex costContractum := RootStep.recurSucc _ _ _

/-- Sharing changes step counts: one shared step contracts both copies of a redex, which takes two
term steps and cannot be done in one. -/
theorem sharing_cost_control :
    SharedStep (.wrap costRedex costRedex) (.wrap costContractum costContractum) ∧
      ¬ ContextStep (.wrap costRedex costRedex) (.wrap costContractum costContractum) ∧
      RelPow ContextStep 2 (.wrap costRedex costRedex) (.wrap costContractum costContractum) := by
  refine ⟨⟨costRedex, costContractum, cost_rootStep, ⟨.wrapLeft .hole costRedex, rfl⟩, by decide⟩,
    ?_, ?_⟩
  · rw [contextStep_iff]
    rintro ⟨C, a, b, hr, h1, h2⟩
    cases C with
    | hole =>
      simp only [FreeContext.plug] at h1
      subst h1
      cases hr
    | succ C => simp [FreeContext.plug] at h1
    | wrapLeft C r =>
      simp only [FreeContext.plug, FreeTerm.wrap.injEq] at h1 h2
      exact absurd (h1.2.trans h2.2.symm) (by decide)
    | wrapRight l C =>
      simp only [FreeContext.plug, FreeTerm.wrap.injEq] at h1 h2
      exact absurd (h1.1.trans h2.1.symm) (by decide)
    | recurBase C s n => simp [FreeContext.plug] at h1
    | recurStep x C n => simp [FreeContext.plug] at h1
    | recurCounter x s C => simp [FreeContext.plug] at h1
  · have s1 : ContextStep (.wrap costRedex costRedex) (.wrap costContractum costRedex) :=
      ContextStep.lift (.wrapLeft .hole costRedex) cost_rootStep
    have s2 : ContextStep (.wrap costContractum costRedex) (.wrap costContractum costContractum) :=
      ContextStep.lift (.wrapRight costContractum .hole) cost_rootStep
    exact RelPow.succ (RelPow.succ (RelPow.zero _) s1) s2

/-! ### Toyama's system -/

/-- Terms of Toyama's system `f(0, 1, x) → f(x, x, x)`, `g(x, y) → x`, `g(x, y) → y`. -/
inductive ToyamaTerm where
  | zero
  | one
  | g (a b : ToyamaTerm)
  | f (a b c : ToyamaTerm)
  deriving DecidableEq

/-- Root rules of Toyama's system. -/
inductive ToyamaRoot : ToyamaTerm → ToyamaTerm → Prop where
  | fRule (x : ToyamaTerm) : ToyamaRoot (.f .zero .one x) (.f x x x)
  | gLeft (x y : ToyamaTerm) : ToyamaRoot (.g x y) x
  | gRight (x y : ToyamaTerm) : ToyamaRoot (.g x y) y

/-- Term rewriting in Toyama's system. -/
inductive ToyamaStep : ToyamaTerm → ToyamaTerm → Prop where
  | root {t u : ToyamaTerm} : ToyamaRoot t u → ToyamaStep t u
  | g1 {a a' : ToyamaTerm} (b : ToyamaTerm) : ToyamaStep a a' → ToyamaStep (.g a b) (.g a' b)
  | g2 (a : ToyamaTerm) {b b' : ToyamaTerm} : ToyamaStep b b' → ToyamaStep (.g a b) (.g a b')
  | f1 {a a' : ToyamaTerm} (b c : ToyamaTerm) :
      ToyamaStep a a' → ToyamaStep (.f a b c) (.f a' b c)
  | f2 (a : ToyamaTerm) {b b' : ToyamaTerm} (c : ToyamaTerm) :
      ToyamaStep b b' → ToyamaStep (.f a b c) (.f a b' c)
  | f3 (a b : ToyamaTerm) {c c' : ToyamaTerm} :
      ToyamaStep c c' → ToyamaStep (.f a b c) (.f a b c')

/-- Replace every occurrence of `a` by `b`. -/
def toyamaReplaceAll (a b : ToyamaTerm) : ToyamaTerm → ToyamaTerm
  | .zero => if ToyamaTerm.zero = a then b else .zero
  | .one => if ToyamaTerm.one = a then b else .one
  | .g x y => if ToyamaTerm.g x y = a then b else .g (toyamaReplaceAll a b x) (toyamaReplaceAll a b y)
  | .f x y z =>
      if ToyamaTerm.f x y z = a then b else
        .f (toyamaReplaceAll a b x) (toyamaReplaceAll a b y) (toyamaReplaceAll a b z)

/-- Occurrence of a subterm. -/
inductive ToyamaOccurs (a : ToyamaTerm) : ToyamaTerm → Prop where
  | here : ToyamaOccurs a a
  | g1 {x : ToyamaTerm} (y : ToyamaTerm) : ToyamaOccurs a x → ToyamaOccurs a (.g x y)
  | g2 (x : ToyamaTerm) {y : ToyamaTerm} : ToyamaOccurs a y → ToyamaOccurs a (.g x y)
  | f1 {x : ToyamaTerm} (y z : ToyamaTerm) : ToyamaOccurs a x → ToyamaOccurs a (.f x y z)
  | f2 (x : ToyamaTerm) {y : ToyamaTerm} (z : ToyamaTerm) :
      ToyamaOccurs a y → ToyamaOccurs a (.f x y z)
  | f3 (x y : ToyamaTerm) {z : ToyamaTerm} : ToyamaOccurs a z → ToyamaOccurs a (.f x y z)

/-- Maximally shared rewriting in Toyama's system. -/
def ToyamaShared (t u : ToyamaTerm) : Prop :=
  ∃ a b, ToyamaRoot a b ∧ ToyamaOccurs a t ∧ u = toyamaReplaceAll a b t

/-- The start term `f(g(0, 1), g(0, 1), g(0, 1))`. -/
def toyamaStart : ToyamaTerm := .f (.g .zero .one) (.g .zero .one) (.g .zero .one)

theorem acc_irrefl {α : Type} {r : α → α → Prop} {a : α} (h : Acc r a) : ¬ r a a := by
  induction h with
  | intro x _ ih => exact fun hxx => ih x hxx hxx

/-- Term rewriting loops from the start term. -/
theorem toyama_term_not_acc : ¬ Acc (fun u t => ToyamaStep t u) toyamaStart := by
  intro hacc
  have s1 : ToyamaStep toyamaStart (.f .zero (.g .zero .one) (.g .zero .one)) :=
    .f1 _ _ (.root (.gLeft _ _))
  have s2 : ToyamaStep (.f .zero (.g .zero .one) (.g .zero .one))
      (.f .zero .one (.g .zero .one)) :=
    .f2 _ _ (.root (.gRight _ _))
  have s3 : ToyamaStep (.f .zero .one (.g .zero .one)) toyamaStart := .root (.fRule _)
  have h1 : Relation.TransGen (fun u t => ToyamaStep t u) toyamaStart
      (.f .zero .one (.g .zero .one)) :=
    Relation.TransGen.single s3
  have h2 : Relation.TransGen (fun u t => ToyamaStep t u) toyamaStart
      (.f .zero (.g .zero .one) (.g .zero .one)) :=
    h1.tail s2
  have hcyc : Relation.TransGen (fun u t => ToyamaStep t u) toyamaStart toyamaStart :=
    h2.tail s1
  exact acc_irrefl hacc.transGen hcyc

theorem toyama_leaf_occurs {a x : ToyamaTerm} (hx : x = .zero ∨ x = .one)
    (h : ToyamaOccurs a x) : a = x := by
  rcases hx with rfl | rfl <;> cases h <;> rfl

theorem toyama_leaf_not_root {x b : ToyamaTerm} (hx : x = .zero ∨ x = .one) :
    ¬ ToyamaRoot x b := by
  rcases hx with rfl | rfl <;> intro h <;> cases h

/-- A term `f(x, y, z)` with leaf arguments and not of the shape `f(0, 1, _)` is a shared normal
form. -/
theorem toyama_leaves_normal {x y z : ToyamaTerm} (hx : x = .zero ∨ x = .one)
    (hy : y = .zero ∨ y = .one) (hz : z = .zero ∨ z = .one)
    (hxy : ¬ (x = .zero ∧ y = .one)) (u : ToyamaTerm) : ¬ ToyamaShared (.f x y z) u := by
  rintro ⟨a, b, hr, hocc, -⟩
  cases hocc with
  | here =>
    cases hr with
    | fRule w => exact hxy ⟨rfl, rfl⟩
  | f1 _ _ h => exact toyama_leaf_not_root hx (toyama_leaf_occurs hx h ▸ hr)
  | f2 _ _ h => exact toyama_leaf_not_root hy (toyama_leaf_occurs hy h ▸ hr)
  | f3 _ _ h => exact toyama_leaf_not_root hz (toyama_leaf_occurs hz h ▸ hr)

theorem toyama_g01_case {a b : ToyamaTerm} (h : ToyamaOccurs a (.g .zero .one))
    (hr : ToyamaRoot a b) :
    toyamaReplaceAll a b toyamaStart = .f .zero .zero .zero ∨
      toyamaReplaceAll a b toyamaStart = .f .one .one .one := by
  cases h with
  | here =>
    cases hr with
    | gLeft => exact Or.inl (by decide)
    | gRight => exact Or.inr (by decide)
  | g1 _ h' =>
    cases h'
    cases hr
  | g2 _ h' =>
    cases h'
    cases hr

theorem toyama_shared_succ {u : ToyamaTerm} (h : ToyamaShared toyamaStart u) :
    u = .f .zero .zero .zero ∨ u = .f .one .one .one := by
  obtain ⟨a, b, hr, hocc, rfl⟩ := h
  have hocc' : ToyamaOccurs a (.f (.g .zero .one) (.g .zero .one) (.g .zero .one)) := hocc
  cases hocc' with
  | here => cases hr
  | f1 _ _ h' => exact toyama_g01_case h' hr
  | f2 _ _ h' => exact toyama_g01_case h' hr
  | f3 _ _ h' => exact toyama_g01_case h' hr

/-- Maximally shared rewriting terminates from the start term. -/
theorem toyama_shared_acc : Acc (fun u t => ToyamaShared t u) toyamaStart := by
  refine Acc.intro _ fun u hu => ?_
  rcases toyama_shared_succ hu with rfl | rfl
  · exact Acc.intro _ fun v hv =>
      absurd hv (toyama_leaves_normal (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (by simp) v)
  · exact Acc.intro _ fun v hv =>
      absurd hv (toyama_leaves_normal (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (by simp) v)

/-- Termination under sharing does not transfer back to term rewriting. -/
theorem toyama_sharing_nonconservative :
    Acc (fun u t => ToyamaShared t u) toyamaStart ∧ ¬ Acc (fun u t => ToyamaStep t u) toyamaStart :=
  ⟨toyama_shared_acc, toyama_term_not_acc⟩

/-! ### Row: sharingNonConservativity -/

/-- Sharing policies on the free terms: tree rewriting, maximal sharing, and a representation
change that keeps the readback and performs no rewrite step. -/
inductive SharingPolicy where
  | tree
  | maximal
  | stutter
  deriving DecidableEq

/-- The step relation of a sharing policy, read back on free terms. -/
def policyStep : SharingPolicy → FreeTerm Nat → FreeTerm Nat → Prop
  | .tree => ContextStep
  | .maximal => SharedStep
  | .stutter => fun t u => u = t

/-- Native data: a sharing policy. -/
abbrev sharingNonConservativityData : Type := SharingPolicy

/-- Term graph rewriting (Plump 1999): each step of the policy reads back to a nonempty sequence of
term steps. -/
def sharingNonConservativityLaws (M : sharingNonConservativityData) : Prop :=
  Simulates ContextStep (policyStep M) id

/-- The free system terminates under the policy. -/
def sharingNonConservativityAccepts (M : sharingNonConservativityData) : Prop :=
  WellFounded (fun u t => policyStep M t u)

/-- Verdict: escape (termination transfers from terms to shared graphs; the converse transfer and
step counts are not conserved). -/
def sharingNonConservativityResult (M : sharingNonConservativityData) : Prop :=
  sharingNonConservativityAccepts M

theorem sharingNonConservativity_universal :
    ∀ M, sharingNonConservativityLaws M → sharingNonConservativityResult M :=
  fun _ h => wf_of_simulates h (main_free_contextual_termination Nat)

def sharingNonConservativityWitness : sharingNonConservativityData := .maximal

theorem sharingNonConservativityWitness_laws :
    sharingNonConservativityLaws sharingNonConservativityWitness :=
  sharedStep_simulates

theorem sharingNonConservativityWitness_result :
    sharingNonConservativityResult sharingNonConservativityWitness :=
  sharingNonConservativity_universal _ sharingNonConservativityWitness_laws

/-- Maximal sharing contracts two copies in one step, and on Toyama's system its termination does not
transfer back to term rewriting. -/
theorem sharingNonConservativityWitness_feature :
    policyStep sharingNonConservativityWitness (.wrap costRedex costRedex)
        (.wrap costContractum costContractum) ∧
      ¬ ContextStep (.wrap costRedex costRedex) (.wrap costContractum costContractum) ∧
      (Acc (fun u t => ToyamaShared t u) toyamaStart ∧
        ¬ Acc (fun u t => ToyamaStep t u) toyamaStart) :=
  ⟨sharing_cost_control.1, sharing_cost_control.2.1, toyama_sharing_nonconservative⟩

/-- The stutter policy keeps the readback and performs no rewrite step: the simulation law fails and
the policy loops. -/
theorem sharingNonConservativity_mutation :
    ¬ sharingNonConservativityLaws .stutter ∧ ¬ sharingNonConservativityResult .stutter := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hloop : Relation.TransGen ContextStep FreeTerm.zero FreeTerm.zero :=
      h (s := FreeTerm.zero) (s' := FreeTerm.zero) rfl
    have hacc := ((main_free_contextual_termination Nat).apply FreeTerm.zero).transGen
    exact acc_irrefl hacc (Relation.transGen_swap.2 hloop)
  · exact (h.asymmetric FreeTerm.zero FreeTerm.zero rfl) rfl

end OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate
