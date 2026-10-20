import OperatorKO7.Meta.Methods.OrientationClosure.FreeDerivationalComplexity
import OperatorKO7.Meta.MPO_FullStep
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.SetTheory.Ordinal.FixedPoint
import Mathlib.Tactic

/-!
# Ordinal calibration of the escapes on the free schema

Natural-valued ranks. If a natural-valued function strictly decreases along a well-founded
relation, the ordinal height of every element is at most its value (`rank_le_natRank`), so every
height is finite. The heights of a well-founded relation form an initial segment of the ordinals:
an element of height at least `o` forces an element of height exactly `o`
(`exists_rank_eq_of_le_rank`).

On free recursor syntax over every variable type the polynomial escape is natural-valued (the
weight `freeWeight` drops on every contextual step), and so is the dependency-pair escape (the call
rank drops by one on every recursive call). Both relations reach every finite height, so the
heights are exactly the natural numbers (`range_ctxHeight_eq_range_natCast`,
`range_callHeight_eq_range_natCast`) and each relation has height exactly `ω`
(`ctx_height_exact_omega`, `call_height_exact_omega`). The natural-number statements of the
earlier version are the instances at `Nat`.

The MPO escape. `MPO_FullStep.lean` ranks KO7 traces by `veblen (precedence) (payload)`. The same
path order and ranking at the four schema symbols, with precedence `zero < succ < wrap < recur`,
orient both free root rules (`freeMpo_orients_rootStep`); every comparison of the path order
decreases the ranking (`freeMpoOrd_strict_of_mpo`); every value lies below `veblen 4 0`
(`freeMpoOrd_lt_veblen_four`), and the values are cofinal in it (`iSup_freeMpoOrd`), because
`veblen 4 0` is the least fixed point of `veblen 3` and the tower
`recur (recur (... zero) zero zero) zero zero` passes every iterate of `veblen 3` at `0`.
The bound is a property of the ranking that the MPO proof uses, not of the height of the root
relation.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.FreeOrdinalCalibration

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.ProcessorSemantics
open OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate
open OperatorKO7.Methods.OrientationClosure.SourceChainSoundness
open OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity
open OperatorKO7.MetaMPO (pairPayload triplePayload left_lt_pairPayload right_lt_pairPayload
  pairPayload_lt_of_lt first_lt_triplePayload second_lt_triplePayload third_lt_triplePayload
  triplePayload_lt_of_lt triplePayload_strictMono_right veblen_fixed_of_pos veblen_gt_one_of_pos
  veblen_isSuccLimit_of_pos lt_veblen_of_nonlimit)
open scoped Ordinal

universe u

/-! ## Natural-valued ranks -/

section NatRank

variable {α : Type u} (r : α → α → Prop) [IsWellFounded α r]

/-- A natural-valued function that strictly decreases along `r` bounds the ordinal height.

Proves: `IsWellFounded.rank r a ≤ f a` when `r a b → f a < f b` for all `a`, `b`.
Does not prove: a lower bound on the height.
Relation: an arbitrary well-founded relation `r`.
Closure: the rank of `r` (its well-founded height).
Strategy: not applicable.
Trust: kernel-only.
Scope: every type `α` in every universe. -/
theorem rank_le_natRank (f : α → Nat) (hf : ∀ a b, r a b → f a < f b) (a : α) :
    IsWellFounded.rank r a ≤ (f a : Ordinal) := by
  refine IsWellFounded.induction r (C := fun a => IsWellFounded.rank r a ≤ (f a : Ordinal)) a
    (fun x ih => ?_)
  show IsWellFounded.rank r x ≤ (f x : Ordinal)
  rw [IsWellFounded.rank_eq]
  refine Ordinal.iSup_le fun y => ?_
  have h1 : IsWellFounded.rank r y.1 ≤ (f y.1 : Ordinal) := ih y.1 y.2
  have h2 : ((f y.1 : Nat) : Ordinal) < (f x : Ordinal) := by exact_mod_cast hf y.1 x y.2
  exact Order.succ_le_of_lt (h1.trans_lt h2)

/-- Under a natural-valued decreasing function every height is finite.

Proves: `IsWellFounded.rank r a < ω` under the hypothesis of `rank_le_natRank`.
Does not prove: a lower bound on the height.
Relation: an arbitrary well-founded relation `r`.
Closure: the rank of `r`.
Strategy: not applicable.
Trust: kernel-only.
Scope: every type `α` in every universe. -/
theorem rank_lt_omega_of_natRank (f : α → Nat) (hf : ∀ a b, r a b → f a < f b) (a : α) :
    IsWellFounded.rank r a < ω :=
  (rank_le_natRank r f hf a).trans_lt (Ordinal.nat_lt_omega0 _)

/-- A chain of `m` steps from `a` to `c` lifts the height of `a` at least `m` above that of `c`.

Proves: an `m`-step `R`-path from `a` to `c`, with every `R`-step a reversed `r`-step, gives
`rank r c + m ≤ rank r a`.
Does not prove: an upper bound on the height.
Relation: `R`, contained in the reverse of `r`.
Closure: exactly `m` steps (`RelPow`).
Strategy: not applicable.
Trust: kernel-only.
Scope: every type `α` in every universe. -/
theorem rank_add_le_of_relPow {R : α → α → Prop} (hR : ∀ a b, R a b → r b a) {m : Nat} {a c : α}
    (h : RelPow R m a c) : IsWellFounded.rank r c + (m : Ordinal) ≤ IsWellFounded.rank r a := by
  induction h with
  | zero => simp
  | @succ n a' b' c' _ hbc ih =>
    have h1 : IsWellFounded.rank r c' + 1 ≤ IsWellFounded.rank r b' := by
      rw [Ordinal.add_one_eq_succ]
      exact Order.succ_le_of_lt (IsWellFounded.rank_lt_of_rel (hR b' c' hbc))
    calc IsWellFounded.rank r c' + ((n + 1 : Nat) : Ordinal)
        = IsWellFounded.rank r c' + 1 + (n : Ordinal) := by
          rw [add_assoc, Ordinal.one_add_natCast, Order.succ_eq_add_one]
      _ ≤ IsWellFounded.rank r b' + (n : Ordinal) := add_le_add_right h1 _
      _ ≤ IsWellFounded.rank r a' := ih

/-- The heights of a well-founded relation form an initial segment of the ordinals: an element of
height at least `o` forces an element of height exactly `o`.

Proves: `o ≤ IsWellFounded.rank r a → ∃ b, IsWellFounded.rank r b = o`.
Does not prove: that the element of height `o` is related to `a`.
Relation: an arbitrary well-founded relation `r`.
Closure: the rank of `r`.
Strategy: not applicable.
Trust: kernel-only; the proof is `IsWellFounded.mem_range_rank_of_le` of Mathlib, which inducts
along `r` through `IsWellFounded.rank_eq`.
Scope: every type `α` in every universe and every ordinal `o`. -/
theorem exists_rank_eq_of_le_rank {o : Ordinal.{u}} {a : α} (h : o ≤ IsWellFounded.rank r a) :
    ∃ b, IsWellFounded.rank r b = o :=
  IsWellFounded.mem_range_rank_of_le h

end NatRank

section Heights

variable {ν : Type u}

/-! ## The polynomial escape is calibrated at `ω` -/

/-- The reversed contextual relation of the free recursor.

Proves: (definition) `CtxRev u t ↔ ContextStep t u`.
Does not prove: well-foundedness; `ctxRev_isWellFounded` supplies it.
Relation: ContextStep, reversed.
Closure: context.
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`. -/
def CtxRev (u t : FreeTerm ν) : Prop := ContextStep t u

/-- The reversed contextual relation is well founded: the free contextual termination theorem.

Proves: `IsWellFounded (FreeTerm ν) CtxRev`.
Does not prove: a bound on heights; `ctxHeight_lt_omega` gives it.
Relation: ContextStep, reversed.
Closure: context.
Strategy: full.
Trust: kernel-only; the witness is `FreePolynomialTermination.main_free_contextual_termination`.
Scope: every variable type `ν`. -/
instance ctxRev_isWellFounded : IsWellFounded (FreeTerm ν) CtxRev :=
  ⟨FreePolynomialTermination.main_free_contextual_termination ν⟩

/-- The height of a free term under contextual rewriting.

Proves: (definition) `ctxHeight t = IsWellFounded.rank CtxRev t`.
Does not prove: any value; the theorems below compute the range.
Relation: ContextStep, reversed.
Closure: the well-founded rank of the contextual relation.
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`. -/
noncomputable def ctxHeight (t : FreeTerm ν) : Ordinal.{u} := IsWellFounded.rank CtxRev t

/-- The contextual height is at most the polynomial weight.

Proves: `ctxHeight t ≤ freeWeight t`.
Does not prove: a lower bound.
Relation: ContextStep, reversed.
Closure: the well-founded rank of the contextual relation.
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem ctxHeight_le_freeWeight (t : FreeTerm ν) : ctxHeight t ≤ (freeWeight t : Ordinal) :=
  rank_le_natRank CtxRev freeWeight (fun _ _ h => freeWeight_contextStep h) t

/-- The contextual height is at most the weight `qw` at natural-number variables.

Proves: the instance of `ctxHeight_le_freeWeight` at `Nat`, stated with `qw`.
Does not prove: a statement at another variable type; `ctxHeight_le_freeWeight` is the general
form.
Relation: ContextStep, reversed.
Closure: the well-founded rank of the contextual relation.
Strategy: full.
Trust: kernel-only.
Scope: natural-number variables. -/
theorem ctxHeight_le_qw (t : FreeTerm Nat) : ctxHeight t ≤ (qw t : Ordinal) := by
  rw [← freeWeight_eq_qw]
  exact ctxHeight_le_freeWeight t

/-- Every contextual height is finite.

Proves: `ctxHeight t < ω`.
Does not prove: that a given finite height occurs; `ctxHeight_attains` gives it.
Relation: ContextStep, reversed.
Closure: the well-founded rank of the contextual relation.
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν` and every term. -/
theorem ctxHeight_lt_omega (t : FreeTerm ν) : ctxHeight t < ω :=
  rank_lt_omega_of_natRank CtxRev freeWeight (fun _ _ h => freeWeight_contextStep h) t

/-- A derivation of `m` steps from `t` puts the height of `t` at least `m`.

Proves: `RelPow ContextStep m t u → m ≤ ctxHeight t`.
Does not prove: an upper bound.
Relation: ContextStep.
Closure: exactly `m` steps (`RelPow`).
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem le_ctxHeight_of_relPow {m : Nat} {t u : FreeTerm ν} (h : RelPow ContextStep m t u) :
    (m : Ordinal) ≤ ctxHeight t :=
  (Ordinal.le_add_left _ _).trans (rank_add_le_of_relPow CtxRev (fun _ _ hs => hs) h)

/-- A natural number is at most two to its power.

Proves: `n ≤ 2 ^ n`.
Does not prove: any rewriting fact.
Relation: none.
Closure: none.
Strategy: not applicable.
Trust: kernel-only.
Scope: every natural number. -/
theorem le_two_pow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < 2 ^ k := by positivity
    rw [pow_succ]
    omega

/-- The nested payload family reaches every finite contextual height.

Proves: for every `n` some term `t` has `n ≤ ctxHeight t` (the term is `nestFamily 2 n`).
Does not prove: exact attainment; `ctxHeight_attains` gives it.
Relation: ContextStep, reversed.
Closure: the well-founded rank of the contextual relation.
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem ctxHeight_unbounded (n : Nat) : ∃ t : FreeTerm ν, (n : Ordinal) ≤ ctxHeight t := by
  obtain ⟨m, u, hm, hd⟩ := nestFamily_long_derivation (ν := ν) 2 n
  refine ⟨nestFamily 2 n, ?_⟩
  have h2 : ((n : Nat) : Ordinal) ≤ (m : Ordinal) := by exact_mod_cast (le_two_pow n).trans hm
  exact h2.trans (le_ctxHeight_of_relPow hd)

/-- The polynomial escape is calibrated at `ω`: every contextual height is finite and the heights
exceed every natural number.

Proves: `(∀ t, ctxHeight t < ω) ∧ ∀ n : Nat, ∃ t, n ≤ ctxHeight t`.
Does not prove: exact attainment; `ctx_height_exact_omega` states the exact range.
Relation: ContextStep, reversed.
Closure: the well-founded rank of the contextual relation.
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`; at `Nat` it is the natural-number statement. -/
theorem ctx_calibrated_omega :
    (∀ t : FreeTerm ν, ctxHeight t < ω) ∧
      ∀ n : Nat, ∃ t : FreeTerm ν, (n : Ordinal) ≤ ctxHeight t :=
  ⟨ctxHeight_lt_omega, ctxHeight_unbounded⟩

/-- The height of the free contextual relation is exactly `ω`.

Proves: `⨆ t, ctxHeight t = ω`.
Does not prove: that each finite height occurs; `ctxHeight_attains` gives it.
Relation: ContextStep, reversed.
Closure: the well-founded rank of the contextual relation.
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem iSup_ctxHeight : ⨆ t : FreeTerm ν, ctxHeight t = ω := by
  apply le_antisymm
  · exact Ordinal.iSup_le fun t => (ctxHeight_lt_omega t).le
  · refine le_of_forall_lt fun o ho => ?_
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 ho
    obtain ⟨t, ht⟩ := ctxHeight_unbounded (ν := ν) (n + 1)
    rw [Ordinal.lt_iSup_iff]
    refine ⟨t, lt_of_lt_of_le ?_ ht⟩
    exact_mod_cast Nat.lt_succ_self n

/-- Every natural number is the contextual height of some term.

Proves: `∀ n : Nat, ∃ t, ctxHeight t = n`.
Does not prove: uniqueness of the term.
Relation: ContextStep, reversed.
Closure: the well-founded rank of the contextual relation.
Strategy: full.
Trust: kernel-only; the proof combines `ctxHeight_unbounded` with the initial-segment property
`exists_rank_eq_of_le_rank`.
Scope: every variable type `ν`, the empty type included. -/
theorem ctxHeight_attains (n : Nat) : ∃ t : FreeTerm ν, ctxHeight t = n := by
  obtain ⟨t, ht⟩ := ctxHeight_unbounded (ν := ν) n
  exact exists_rank_eq_of_le_rank CtxRev ht

/-- The contextual heights are exactly the natural numbers.

Proves: `Set.range ctxHeight = Set.range (fun n : Nat => (n : Ordinal))`: every height is a
natural number and every natural number is a height.
Does not prove: the supremum; `iSup_ctxHeight` gives it.
Relation: ContextStep, reversed.
Closure: the well-founded rank of the contextual relation.
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem range_ctxHeight_eq_range_natCast :
    Set.range (ctxHeight (ν := ν)) = Set.range (fun n : Nat => (n : Ordinal.{u})) := by
  ext o
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 (ctxHeight_lt_omega t)
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, rfl⟩
    exact ctxHeight_attains n

/-- Item (i) of `thm:free-ordinal-height` in the paper for the contextual relation: the heights are
exactly the natural numbers and their supremum is `ω`.

Proves: `Set.range ctxHeight = Set.range (fun n : Nat => (n : Ordinal)) ∧ ⨆ t, ctxHeight t = ω`.
Does not prove: a closed form for the height of a given term.
Relation: ContextStep, reversed.
Closure: the well-founded rank of the contextual relation.
Strategy: full.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem ctx_height_exact_omega :
    Set.range (ctxHeight (ν := ν)) = Set.range (fun n : Nat => (n : Ordinal.{u})) ∧
      ⨆ t : FreeTerm ν, ctxHeight t = ω :=
  ⟨range_ctxHeight_eq_range_natCast, iSup_ctxHeight⟩

/-! ## The dependency-pair escape is calibrated at `ω` -/

/-- The reversed recursive-call relation.

Proves: (definition) `CallRev c a ↔ FreeRecursiveCallPair a c`.
Does not prove: well-foundedness; `callRev_isWellFounded` supplies it.
Relation: FreeRecursiveCallPair, reversed.
Closure: one call.
Strategy: not applicable (a dependency-pair relation).
Trust: kernel-only.
Scope: every variable type `ν`. -/
def CallRev (c a : FreeTerm ν) : Prop := FreeRecursiveCallPair a c

/-- A recursive call lowers the call rank.

Proves: `CallRev c a → recursiveCallRank c < recursiveCallRank a`.
Does not prove: any statement about contextual rewriting.
Relation: FreeRecursiveCallPair, reversed.
Closure: one call.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem callRank_lt {c a : FreeTerm ν} (h : CallRev c a) :
    recursiveCallRank c < recursiveCallRank a := by
  have := ObserverSufficiency.recursiveCallRank_call (show FreeRecursiveCallPair a c from h)
  omega

/-- The reversed recursive-call relation is well founded through the call rank.

Proves: `IsWellFounded (FreeTerm ν) CallRev`.
Does not prove: a bound on heights; `callHeight_lt_omega` gives it.
Relation: FreeRecursiveCallPair, reversed.
Closure: one call.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
instance callRev_isWellFounded : IsWellFounded (FreeTerm ν) CallRev :=
  ⟨Subrelation.wf (r := InvImage (· < ·) recursiveCallRank) (fun h => callRank_lt h)
    (InvImage.wf recursiveCallRank Nat.lt_wfRel.wf)⟩

/-- The height of a free term under recursive calls.

Proves: (definition) `callHeight t = IsWellFounded.rank CallRev t`.
Does not prove: any value; the theorems below compute the range.
Relation: FreeRecursiveCallPair, reversed.
Closure: the well-founded rank of the call relation.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
noncomputable def callHeight (t : FreeTerm ν) : Ordinal.{u} := IsWellFounded.rank CallRev t

/-- The call height is at most the call rank.

Proves: `callHeight t ≤ recursiveCallRank t`.
Does not prove: a lower bound.
Relation: FreeRecursiveCallPair, reversed.
Closure: the well-founded rank of the call relation.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem callHeight_le (t : FreeTerm ν) : callHeight t ≤ (recursiveCallRank t : Ordinal) :=
  rank_le_natRank CallRev recursiveCallRank (fun _ _ h => callRank_lt h) t

/-- Every call height is finite.

Proves: `callHeight t < ω`.
Does not prove: that a given finite height occurs; `callHeight_attains` gives it.
Relation: FreeRecursiveCallPair, reversed.
Closure: the well-founded rank of the call relation.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν` and every term. -/
theorem callHeight_lt_omega (t : FreeTerm ν) : callHeight t < ω :=
  (callHeight_le t).trans_lt (Ordinal.nat_lt_omega0 _)

/-- A counter of `k` successors gives a chain of `k` recursive calls.

Proves: `RelPow FreeRecursiveCallPair k (recur b s (succ^k zero)) (recur b s zero)`.
Does not prove: any statement about contextual rewriting.
Relation: FreeRecursiveCallPair.
Closure: exactly `k` calls.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`, every `b`, `s` and `k`. -/
theorem callChain (b s : FreeTerm ν) :
    ∀ k : Nat, RelPow FreeRecursiveCallPair k (.recur b s (sucOn k .zero)) (.recur b s .zero)
  | 0 => RelPow.zero _
  | k + 1 => by
    have h1 : RelPow FreeRecursiveCallPair 1 (.recur b s (sucOn (k + 1) .zero))
        (.recur b s (sucOn k .zero)) :=
      RelPow.succ (RelPow.zero _) (.successor b s (sucOn k .zero))
    have h2 := h1.append (callChain b s k)
    rw [Nat.add_comm 1 k] at h2
    exact h2

/-- A chain of `m` recursive calls from `a` puts the call height of `a` at least `m`.

Proves: `RelPow FreeRecursiveCallPair m a c → m ≤ callHeight a`.
Does not prove: an upper bound.
Relation: FreeRecursiveCallPair.
Closure: exactly `m` calls.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem le_callHeight_of_relPow {m : Nat} {a c : FreeTerm ν}
    (h : RelPow FreeRecursiveCallPair m a c) : (m : Ordinal) ≤ callHeight a :=
  (Ordinal.le_add_left _ _).trans (rank_add_le_of_relPow CallRev (fun _ _ hs => hs) h)

/-- The call heights exceed every natural number.

Proves: for every `n` some term `t` has `n ≤ callHeight t` (the term is
`recur zero zero (succ^n zero)`).
Does not prove: exact attainment; `callHeight_attains` gives it.
Relation: FreeRecursiveCallPair, reversed.
Closure: the well-founded rank of the call relation.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem callHeight_unbounded (n : Nat) : ∃ t : FreeTerm ν, (n : Ordinal) ≤ callHeight t :=
  ⟨_, le_callHeight_of_relPow (callChain (ν := ν) .zero .zero n)⟩

/-- The dependency-pair escape is calibrated at `ω`: every call height is finite and the heights
exceed every natural number.

Proves: `(∀ t, callHeight t < ω) ∧ ∀ n : Nat, ∃ t, n ≤ callHeight t`.
Does not prove: exact attainment; `call_height_exact_omega` states the exact range.
Relation: FreeRecursiveCallPair, reversed.
Closure: the well-founded rank of the call relation.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`; at `Nat` it is the natural-number statement. -/
theorem call_calibrated_omega :
    (∀ t : FreeTerm ν, callHeight t < ω) ∧
      ∀ n : Nat, ∃ t : FreeTerm ν, (n : Ordinal) ≤ callHeight t :=
  ⟨callHeight_lt_omega, callHeight_unbounded⟩

/-- The height of the recursive-call relation is exactly `ω`.

Proves: `⨆ t, callHeight t = ω`.
Does not prove: that each finite height occurs; `callHeight_attains` gives it.
Relation: FreeRecursiveCallPair, reversed.
Closure: the well-founded rank of the call relation.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem iSup_callHeight : ⨆ t : FreeTerm ν, callHeight t = ω := by
  apply le_antisymm
  · exact Ordinal.iSup_le fun t => (callHeight_lt_omega t).le
  · refine le_of_forall_lt fun o ho => ?_
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 ho
    obtain ⟨t, ht⟩ := callHeight_unbounded (ν := ν) (n + 1)
    rw [Ordinal.lt_iSup_iff]
    refine ⟨t, lt_of_lt_of_le ?_ ht⟩
    exact_mod_cast Nat.lt_succ_self n

/-- Every natural number is the call height of some term.

Proves: `∀ n : Nat, ∃ t, callHeight t = n`.
Does not prove: uniqueness of the term.
Relation: FreeRecursiveCallPair, reversed.
Closure: the well-founded rank of the call relation.
Strategy: not applicable.
Trust: kernel-only; the proof combines `callHeight_unbounded` with the initial-segment property
`exists_rank_eq_of_le_rank`.
Scope: every variable type `ν`, the empty type included. -/
theorem callHeight_attains (n : Nat) : ∃ t : FreeTerm ν, callHeight t = n := by
  obtain ⟨t, ht⟩ := callHeight_unbounded (ν := ν) n
  exact exists_rank_eq_of_le_rank CallRev ht

/-- The call heights are exactly the natural numbers.

Proves: `Set.range callHeight = Set.range (fun n : Nat => (n : Ordinal))`: every call height is a
natural number and every natural number is a call height.
Does not prove: the supremum; `iSup_callHeight` gives it.
Relation: FreeRecursiveCallPair, reversed.
Closure: the well-founded rank of the call relation.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem range_callHeight_eq_range_natCast :
    Set.range (callHeight (ν := ν)) = Set.range (fun n : Nat => (n : Ordinal.{u})) := by
  ext o
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 (callHeight_lt_omega t)
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, rfl⟩
    exact callHeight_attains n

/-- Item (i) of `thm:free-ordinal-height` in the paper for the recursive-call relation: the heights
are exactly the natural numbers and their supremum is `ω`.

Proves: `Set.range callHeight = Set.range (fun n : Nat => (n : Ordinal)) ∧ ⨆ t, callHeight t = ω`.
Does not prove: a closed form for the height of a given term.
Relation: FreeRecursiveCallPair, reversed.
Closure: the well-founded rank of the call relation.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type `ν`. -/
theorem call_height_exact_omega :
    Set.range (callHeight (ν := ν)) = Set.range (fun n : Nat => (n : Ordinal.{u})) ∧
      ⨆ t : FreeTerm ν, callHeight t = ω :=
  ⟨range_callHeight_eq_range_natCast, iSup_callHeight⟩

end Heights

/-! ## The MPO escape at the four schema symbols -/

/-- Precedence of the head symbol: variables and `zero` 0, `succ` 1, `wrap` 2, `recur` 3. -/
def headRank {ν : Type} : FreeTerm ν → Nat
  | .var _ => 0
  | .zero => 0
  | .succ _ => 1
  | .wrap _ _ => 2
  | .recur _ _ _ => 3

/-- Immediate arguments. -/
def freeArgs {ν : Type} : FreeTerm ν → List (FreeTerm ν)
  | .var _ => []
  | .zero => []
  | .succ t => [t]
  | .wrap s t => [s, t]
  | .recur b s n => [b, s, n]

/-- The path order of `MPO_FullStep.lean` at the four schema symbols: subterm, precedence with
dominated arguments, and decrease in the counter under the same `recur` head. -/
inductive FreeMPO {ν : Type} : FreeTerm ν → FreeTerm ν → Prop
  | subEq {s u : FreeTerm ν} : u ∈ freeArgs s → FreeMPO s u
  | subGt {s u t : FreeTerm ν} : u ∈ freeArgs s → FreeMPO u t → FreeMPO s t
  | byPrec {s t : FreeTerm ν} :
      headRank t < headRank s → (∀ u ∈ freeArgs t, FreeMPO s u) → FreeMPO s t
  | recArg {b s n n' : FreeTerm ν} : FreeMPO n' n → FreeMPO (.recur b s n') (.recur b s n)

theorem freeMpo_recurZero {ν : Type} (b s : FreeTerm ν) : FreeMPO (.recur b s .zero) b :=
  .subEq (by simp [freeArgs])

theorem freeMpo_recurSucc {ν : Type} (b s n : FreeTerm ν) :
    FreeMPO (.recur b s (.succ n)) (.wrap s (.recur b s n)) := by
  refine .byPrec (by simp [headRank]) ?_
  intro u hu
  simp [freeArgs] at hu
  rcases hu with rfl | rfl
  · exact .subEq (by simp [freeArgs])
  · exact .recArg (.subEq (by simp [freeArgs]))

/-- The path order orients both free root rules. -/
theorem freeMpo_orients_rootStep {ν : Type} {t u : FreeTerm ν} (h : RootStep t u) :
    FreeMPO t u := by
  cases h with
  | recurZero => exact freeMpo_recurZero _ _
  | recurSucc => exact freeMpo_recurSucc _ _ _

/-- The KO7 MPO ranking at the four schema symbols. -/
noncomputable def freeMpoOrd {ν : Type} : FreeTerm ν → Ordinal.{0}
  | .var _ => Ordinal.veblen 0 0
  | .zero => Ordinal.veblen 0 0
  | .succ t => Ordinal.veblen 1 (Order.succ (freeMpoOrd t))
  | .wrap s t => Ordinal.veblen 2 (pairPayload (freeMpoOrd s) (freeMpoOrd t))
  | .recur b s n =>
      Ordinal.veblen 3 (triplePayload (freeMpoOrd b) (freeMpoOrd s) (freeMpoOrd n))

/-- The payload under the Veblen head. -/
noncomputable def freePayloadOrd {ν : Type} : FreeTerm ν → Ordinal.{0}
  | .var _ => 0
  | .zero => 0
  | .succ t => Order.succ (freeMpoOrd t)
  | .wrap s t => pairPayload (freeMpoOrd s) (freeMpoOrd t)
  | .recur b s n => triplePayload (freeMpoOrd b) (freeMpoOrd s) (freeMpoOrd n)

theorem freeMpoOrd_eq_veblen {ν : Type} (t : FreeTerm ν) :
    freeMpoOrd t = Ordinal.veblen (headRank t : Ordinal.{0}) (freePayloadOrd t) := by
  cases t <;> simp [freeMpoOrd, freePayloadOrd, headRank]

theorem freeMpoOrd_limit {ν : Type} {t : FreeTerm ν} (h : 0 < headRank t) :
    Order.IsSuccLimit (freeMpoOrd t) := by
  rw [freeMpoOrd_eq_veblen]
  exact veblen_isSuccLimit_of_pos (by exact_mod_cast h)

theorem freeMpoOrd_fixed {ν : Type} {t : FreeTerm ν} (h : 0 < headRank t) :
    (ω : Ordinal.{0}) ^ freeMpoOrd t = freeMpoOrd t := by
  rw [freeMpoOrd_eq_veblen]
  exact veblen_fixed_of_pos (by exact_mod_cast h)

theorem one_lt_freeMpoOrd {ν : Type} {t : FreeTerm ν} (h : 0 < headRank t) :
    1 < freeMpoOrd t := by
  rw [freeMpoOrd_eq_veblen]
  exact veblen_gt_one_of_pos (by exact_mod_cast h)

theorem freeMpoOrd_lt_succ {ν : Type} (t : FreeTerm ν) : freeMpoOrd t < freeMpoOrd (.succ t) := by
  have h : Order.succ (freeMpoOrd t) < Ordinal.veblen 1 (Order.succ (freeMpoOrd t)) :=
    lt_veblen_of_nonlimit (by exact_mod_cast (show 0 < (1 : Nat) by decide))
      (Order.not_isSuccLimit_succ _)
  exact (Order.lt_succ _).trans h

theorem pair_lt_freeMpoOrd_wrap {ν : Type} (s t : FreeTerm ν) :
    pairPayload (freeMpoOrd s) (freeMpoOrd t) < freeMpoOrd (.wrap s t) :=
  lt_veblen_of_nonlimit (by exact_mod_cast (show 0 < (2 : Nat) by decide))
    (Order.not_isSuccLimit_succ _)

theorem triple_lt_freeMpoOrd_recur {ν : Type} (b s n : FreeTerm ν) :
    triplePayload (freeMpoOrd b) (freeMpoOrd s) (freeMpoOrd n) < freeMpoOrd (.recur b s n) :=
  lt_veblen_of_nonlimit (by exact_mod_cast (show 0 < (3 : Nat) by decide))
    (Order.not_isSuccLimit_succ _)

theorem freeMpoOrd_arg_lt {ν : Type} {s u : FreeTerm ν} (h : u ∈ freeArgs s) :
    freeMpoOrd u < freeMpoOrd s := by
  cases s with
  | var x => simp [freeArgs] at h
  | zero => simp [freeArgs] at h
  | succ t =>
    have hu : u = t := by simpa [freeArgs] using h
    subst hu
    exact freeMpoOrd_lt_succ _
  | wrap a b =>
    have hu : u = a ∨ u = b := by simpa [freeArgs] using h
    rcases hu with rfl | rfl
    · exact (left_lt_pairPayload _ _).trans (pair_lt_freeMpoOrd_wrap _ _)
    · exact (right_lt_pairPayload _ _).trans (pair_lt_freeMpoOrd_wrap _ _)
  | recur b m n =>
    have hu : u = b ∨ u = m ∨ u = n := by simpa [freeArgs] using h
    rcases hu with rfl | rfl | rfl
    · exact (first_lt_triplePayload _ _ _).trans (triple_lt_freeMpoOrd_recur _ _ _)
    · exact (second_lt_triplePayload _ _ _).trans (triple_lt_freeMpoOrd_recur _ _ _)
    · exact (third_lt_triplePayload _ _ _).trans (triple_lt_freeMpoOrd_recur _ _ _)

theorem freePayloadOrd_lt {ν : Type} {s t : FreeTerm ν} (hs : 0 < headRank s)
    (hargs : ∀ u ∈ freeArgs t, freeMpoOrd u < freeMpoOrd s) : freePayloadOrd t < freeMpoOrd s := by
  have hlim := freeMpoOrd_limit hs
  have hfix := freeMpoOrd_fixed hs
  cases t with
  | var x => exact zero_lt_one.trans (one_lt_freeMpoOrd hs)
  | zero => exact zero_lt_one.trans (one_lt_freeMpoOrd hs)
  | succ u => exact Order.IsSuccLimit.succ_lt hlim (hargs u (by simp [freeArgs]))
  | wrap a b =>
    exact pairPayload_lt_of_lt (hargs a (by simp [freeArgs])) (hargs b (by simp [freeArgs]))
      hlim hfix
  | recur b m n =>
    exact triplePayload_lt_of_lt (hargs b (by simp [freeArgs])) (hargs m (by simp [freeArgs]))
      (hargs n (by simp [freeArgs])) hlim hfix

theorem freeMpoOrd_lt_of_byPrec {ν : Type} {s t : FreeTerm ν} (hprec : headRank t < headRank s)
    (hargs : ∀ u ∈ freeArgs t, freeMpoOrd u < freeMpoOrd s) : freeMpoOrd t < freeMpoOrd s := by
  have hs : 0 < headRank s := Nat.zero_lt_of_lt hprec
  have hpay := freePayloadOrd_lt hs hargs
  have hprecOrd : (headRank t : Ordinal.{0}) < headRank s := by exact_mod_cast hprec
  rw [freeMpoOrd_eq_veblen t, freeMpoOrd_eq_veblen s]
  rw [freeMpoOrd_eq_veblen s] at hpay
  exact Ordinal.veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨hprecOrd, hpay⟩))

/-- Every comparison of the path order decreases the ranking. -/
theorem freeMpoOrd_strict_of_mpo {ν : Type} {a b : FreeTerm ν} (h : FreeMPO a b) :
    freeMpoOrd b < freeMpoOrd a := by
  induction h with
  | subEq hmem => exact freeMpoOrd_arg_lt hmem
  | subGt hmem _ ih => exact ih.trans (freeMpoOrd_arg_lt hmem)
  | byPrec hprec _ ih => exact freeMpoOrd_lt_of_byPrec hprec (fun u hu => ih u hu)
  | recArg _ ih => exact Ordinal.veblen_lt_veblen_iff_right.2 (triplePayload_strictMono_right _ _ ih)

theorem veblen_four_isSuccLimit : Order.IsSuccLimit (Ordinal.veblen 4 0 : Ordinal.{0}) :=
  veblen_isSuccLimit_of_pos (by exact_mod_cast (show 0 < (4 : Nat) by decide))

theorem veblen_four_fixed : (ω : Ordinal.{0}) ^ Ordinal.veblen 4 0 = Ordinal.veblen 4 0 :=
  veblen_fixed_of_pos (by exact_mod_cast (show 0 < (4 : Nat) by decide))

theorem veblen_lt_veblen_four {k p : Ordinal.{0}} (hk : k < 4) (hp : p < Ordinal.veblen 4 0) :
    Ordinal.veblen k p < Ordinal.veblen 4 0 :=
  Ordinal.veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨hk, hp⟩))

/-- Every value of the ranking lies below `veblen 4 0`. -/
theorem freeMpoOrd_lt_veblen_four {ν : Type} : ∀ t : FreeTerm ν, freeMpoOrd t < Ordinal.veblen 4 0
  | .var _ =>
      Ordinal.veblen_zero_lt_veblen_zero.2 (by exact_mod_cast (show 0 < (4 : Nat) by decide))
  | .zero =>
      Ordinal.veblen_zero_lt_veblen_zero.2 (by exact_mod_cast (show 0 < (4 : Nat) by decide))
  | .succ t =>
      veblen_lt_veblen_four (by exact_mod_cast (show 1 < (4 : Nat) by decide))
        (veblen_four_isSuccLimit.succ_lt (freeMpoOrd_lt_veblen_four t))
  | .wrap s t =>
      veblen_lt_veblen_four (by exact_mod_cast (show 2 < (4 : Nat) by decide))
        (pairPayload_lt_of_lt (freeMpoOrd_lt_veblen_four s) (freeMpoOrd_lt_veblen_four t)
          veblen_four_isSuccLimit veblen_four_fixed)
  | .recur b s n =>
      veblen_lt_veblen_four (by exact_mod_cast (show 3 < (4 : Nat) by decide))
        (triplePayload_lt_of_lt (freeMpoOrd_lt_veblen_four b) (freeMpoOrd_lt_veblen_four s)
          (freeMpoOrd_lt_veblen_four n) veblen_four_isSuccLimit veblen_four_fixed)

/-- The tower `recur (recur (... zero) zero zero) zero zero`. -/
def recurTower {ν : Type} : Nat → FreeTerm ν
  | 0 => .zero
  | k + 1 => .recur (recurTower k) .zero .zero

theorem iterate_le_freeMpoOrd_tower {ν : Type} :
    ∀ k : Nat, (Ordinal.veblen 3)^[k] 0 ≤ freeMpoOrd (recurTower (ν := ν) k)
  | 0 => Ordinal.zero_le _
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    have ih := iterate_le_freeMpoOrd_tower (ν := ν) k
    have h1 : freeMpoOrd (recurTower (ν := ν) k) <
        triplePayload (freeMpoOrd (recurTower (ν := ν) k)) (freeMpoOrd (.zero : FreeTerm ν))
          (freeMpoOrd (.zero : FreeTerm ν)) :=
      first_lt_triplePayload _ _ _
    calc Ordinal.veblen 3 ((Ordinal.veblen 3)^[k] 0)
        ≤ Ordinal.veblen 3 (freeMpoOrd (recurTower (ν := ν) k)) :=
          Ordinal.veblen_le_veblen_iff_right.2 ih
      _ ≤ Ordinal.veblen 3 (triplePayload (freeMpoOrd (recurTower (ν := ν) k))
            (freeMpoOrd (.zero : FreeTerm ν)) (freeMpoOrd (.zero : FreeTerm ν))) :=
          Ordinal.veblen_le_veblen_iff_right.2 h1.le
      _ = freeMpoOrd (recurTower (ν := ν) (k + 1)) := rfl

theorem veblen_four_zero_eq_nfp :
    (Ordinal.veblen 4 0 : Ordinal.{0}) = Ordinal.nfp (Ordinal.veblen 3) 0 := by
  have h : Order.succ (3 : Ordinal.{0}) = 4 := by
    rw [← Ordinal.add_one_eq_succ]
    norm_num
  rw [← h, Ordinal.veblen_succ, Ordinal.deriv_zero_right]

/-- The ranking is cofinal in `veblen 4 0`. -/
theorem freeMpoOrd_cofinal {ν : Type} {β : Ordinal.{0}} (hβ : β < Ordinal.veblen 4 0) :
    ∃ t : FreeTerm ν, β < freeMpoOrd t := by
  rw [veblen_four_zero_eq_nfp, Ordinal.lt_nfp_iff] at hβ
  obtain ⟨k, hk⟩ := hβ
  exact ⟨recurTower k, hk.trans_le (iterate_le_freeMpoOrd_tower k)⟩

/-- The MPO bound at the four schema symbols is exact: the supremum of the ranking is
`veblen 4 0`. -/
theorem iSup_freeMpoOrd {ν : Type} : ⨆ t : FreeTerm ν, freeMpoOrd t = Ordinal.veblen 4 0 := by
  apply le_antisymm
  · exact Ordinal.iSup_le fun t => (freeMpoOrd_lt_veblen_four t).le
  · refine le_of_forall_lt fun β hβ => ?_
    obtain ⟨t, ht⟩ := freeMpoOrd_cofinal (ν := ν) hβ
    exact ht.trans_le (Ordinal.le_iSup _ t)

/-- The MPO escape at the four schema symbols: the path order orients both root rules, every
comparison decreases the ranking, every value lies below `veblen 4 0`, and the supremum is
`veblen 4 0`. -/
theorem mpo_calibration {ν : Type} :
    (∀ {t u : FreeTerm ν}, RootStep t u → FreeMPO t u) ∧
      (∀ {a b : FreeTerm ν}, FreeMPO a b → freeMpoOrd b < freeMpoOrd a) ∧
      (∀ t : FreeTerm ν, freeMpoOrd t < Ordinal.veblen 4 0) ∧
      ⨆ t : FreeTerm ν, freeMpoOrd t = Ordinal.veblen 4 0 :=
  ⟨freeMpo_orients_rootStep, freeMpoOrd_strict_of_mpo, freeMpoOrd_lt_veblen_four,
    iSup_freeMpoOrd⟩

end OperatorKO7.Methods.OrientationClosure.FreeOrdinalCalibration
