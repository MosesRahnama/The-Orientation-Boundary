import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore
import Mathlib.Tactic

/-!
# Typing-discipline method rows

Four Tier C rows whose native language is a typing discipline: the guard condition of fixpoint
definitions (`coqGuardAdmittance`), safe recursion with normal and safe positions
(`bellantoniCookSplit`), resource typing in linear logic (`linearLogicTypingBarrier`), and tiered
(ramified) recurrence (`ramifiedRecursionTypingBarrier`). Each row implements the discipline's
own judgment for the free recursor `recur(b, s, zero) → b`,
`recur(b, s, succ n) → wrap(s, recur(b, s, n))` of `SchemaCore`, proves admission or rejection
from that judgment, and names the omitted part of the source in `<row>_scope`.

Relation: `SchemaCore.RootStep` (the two free root rules) read through the stated adapter of each
row. External trust: none. Mathlib only.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines

open OperatorKO7.Methods.OrientationClosure.SchemaCore

/-! ## The free recursor rules as rule schemata -/

/-- The three variables of the free recursor rules: base, step (payload), counter. -/
inductive RV where
  | b
  | s
  | n
  deriving DecidableEq, Repr

/-- Left side of the successor rule `recur(b, s, succ n)`. -/
def succLhs : FreeTerm RV := .recur (.var .b) (.var .s) (.succ (.var .n))

/-- Right side of the successor rule `wrap(s, recur(b, s, n))`. -/
def succRhs : FreeTerm RV := .wrap (.var .s) (.recur (.var .b) (.var .s) (.var .n))

/-- The successor rule schema is the free duplicating root rule `RootStep.recurSucc`. -/
theorem succRule_rootStep : RootStep succLhs succRhs := RootStep.recurSucc _ _ _

/-- Every instance of `RootStep.recurSucc` is a substitution instance of the schema. -/
theorem recurSucc_instance {μ : Type} (b s n : FreeTerm μ) :
    FreeTerm.subst (fun x => match x with | .b => b | .s => s | .n => n) succLhs =
        .recur b s (.succ n) ∧
      FreeTerm.subst (fun x => match x with | .b => b | .s => s | .n => n) succRhs =
        .wrap s (.recur b s n) := ⟨rfl, rfl⟩

/-- Number of occurrences of a variable in a free term. -/
def occ {ν : Type} [DecidableEq ν] (x : ν) : FreeTerm ν → Nat
  | .var y => if y = x then 1 else 0
  | .zero => 0
  | .succ t => occ x t
  | .wrap u v => occ x u + occ x v
  | .recur b s n => occ x b + occ x s + occ x n

theorem occ_succLhs : occ .b succLhs = 1 ∧ occ .s succLhs = 1 ∧ occ .n succLhs = 1 := by
  decide

theorem occ_succRhs : occ .b succRhs = 1 ∧ occ .s succRhs = 2 ∧ occ .n succRhs = 1 := by
  decide

/-- Duplication count of the successor rule: the right-side occurrences in excess of the left-side
occurrences, summed over the rule's variables. -/
def dupCount : Nat :=
  (occ .b succRhs - occ .b succLhs) + (occ .s succRhs - occ .s succLhs) +
    (occ .n succRhs - occ .n succLhs)

theorem dupCount_eq_one : dupCount = 1 := by decide

/-! ## Row `linearLogicTypingBarrier`

Girard, *Linear logic*, Theoretical Computer Science 50 (1987) 1-102. Definition 1.15 gives the
sequent calculus with "the dumping of structural rules": only exchange is left, weakening and
contraction are forbidden. Definition 1.21 adds the exponential rules: dereliction `D?`,
weakening `W?`, contraction `C?`, and of course `!`. A one-sided `?A` corresponds to a left-hand
`!A⊥`; the fragment below is the two-sided, term-annotated reading used to type first-order
rewrite rules: contexts are multisets of typed variables (exchange is implicit), function symbols
carry linear signatures, and weakening, contraction and dereliction act only on context entries of
type `!A`. -/

/-- Formulas of the fragment: atoms, linear implication, tensor, and the exponential `!`. -/
inductive LTy where
  | atom (i : Nat)
  | lolli (A B : LTy)
  | tensor (A B : LTy)
  | bang (A : LTy)
  deriving DecidableEq, Repr

/-- A formula contains no exponential. -/
def LTy.ExpFree : LTy → Prop
  | .atom _ => True
  | .lolli A B => A.ExpFree ∧ B.ExpFree
  | .tensor A B => A.ExpFree ∧ B.ExpFree
  | .bang _ => False

/-- A formula is of the form `!A`. -/
def LTy.IsBang : LTy → Prop
  | .bang _ => True
  | _ => False

theorem LTy.not_isBang_of_expFree {A : LTy} (h : A.ExpFree) : ¬ A.IsBang := by
  cases A <;> simp_all [LTy.ExpFree, LTy.IsBang]

/-- Linear signatures of the four free symbols: argument formulas and result formula. -/
structure LSig where
  zeroTy : LTy
  succArg : LTy
  succTy : LTy
  wrapArg₁ : LTy
  wrapArg₂ : LTy
  wrapTy : LTy
  recurArg₁ : LTy
  recurArg₂ : LTy
  recurArg₃ : LTy
  recurTy : LTy

/-- Typing derivations of the fragment. Symbol rules split the context multiplicatively; the three
structural rules exist only for entries of type `!A`; promotion needs an all-`!` context. -/
inductive LDeriv {ν : Type} (G : LSig) : Multiset (ν × LTy) → FreeTerm ν → LTy → Type where
  | ax (x : ν) (A : LTy) : LDeriv G {(x, A)} (.var x) A
  | zero : LDeriv G 0 .zero G.zeroTy
  | succ {Γ : Multiset (ν × LTy)} {t : FreeTerm ν} :
      LDeriv G Γ t G.succArg → LDeriv G Γ (.succ t) G.succTy
  | wrap {Γ Δ : Multiset (ν × LTy)} {u v : FreeTerm ν} :
      LDeriv G Γ u G.wrapArg₁ → LDeriv G Δ v G.wrapArg₂ → LDeriv G (Γ + Δ) (.wrap u v) G.wrapTy
  | recur {Γ Δ Θ : Multiset (ν × LTy)} {b s n : FreeTerm ν} :
      LDeriv G Γ b G.recurArg₁ → LDeriv G Δ s G.recurArg₂ → LDeriv G Θ n G.recurArg₃ →
        LDeriv G (Γ + Δ + Θ) (.recur b s n) G.recurTy
  | weaken {Γ : Multiset (ν × LTy)} {t : FreeTerm ν} {B : LTy} (x : ν) (A : LTy) :
      LDeriv G Γ t B → LDeriv G ((x, .bang A) ::ₘ Γ) t B
  | contract {Γ : Multiset (ν × LTy)} {t : FreeTerm ν} {B : LTy} (x : ν) (A : LTy) :
      LDeriv G ((x, .bang A) ::ₘ (x, .bang A) ::ₘ Γ) t B → LDeriv G ((x, .bang A) ::ₘ Γ) t B
  | derelict {Γ : Multiset (ν × LTy)} {t : FreeTerm ν} {B : LTy} (x : ν) (A : LTy) :
      LDeriv G ((x, A) ::ₘ Γ) t B → LDeriv G ((x, .bang A) ::ₘ Γ) t B
  | promote {Γ : Multiset (ν × LTy)} {t : FreeTerm ν} {A : LTy} :
      (∀ e ∈ Γ, e.2.IsBang) → LDeriv G Γ t A → LDeriv G Γ t (.bang A)

namespace LDeriv

variable {ν : Type} [DecidableEq ν] {G : LSig}

/-- Contractions on the variable `x` in a derivation. -/
def contrOn (x : ν) : {Γ : Multiset (ν × LTy)} → {t : FreeTerm ν} → {A : LTy} →
    LDeriv G Γ t A → Nat
  | _, _, _, .ax _ _ => 0
  | _, _, _, .zero => 0
  | _, _, _, .succ d => contrOn x d
  | _, _, _, .wrap d e => contrOn x d + contrOn x e
  | _, _, _, .recur d e f => contrOn x d + contrOn x e + contrOn x f
  | _, _, _, .weaken _ _ d => contrOn x d
  | _, _, _, .contract y _ d => contrOn x d + if y = x then 1 else 0
  | _, _, _, .derelict _ _ d => contrOn x d
  | _, _, _, .promote _ d => contrOn x d

/-- Weakenings on the variable `x` in a derivation. -/
def weakOn (x : ν) : {Γ : Multiset (ν × LTy)} → {t : FreeTerm ν} → {A : LTy} →
    LDeriv G Γ t A → Nat
  | _, _, _, .ax _ _ => 0
  | _, _, _, .zero => 0
  | _, _, _, .succ d => weakOn x d
  | _, _, _, .wrap d e => weakOn x d + weakOn x e
  | _, _, _, .recur d e f => weakOn x d + weakOn x e + weakOn x f
  | _, _, _, .weaken y _ d => weakOn x d + if y = x then 1 else 0
  | _, _, _, .contract _ _ d => weakOn x d
  | _, _, _, .derelict _ _ d => weakOn x d
  | _, _, _, .promote _ d => weakOn x d

end LDeriv

/-- Total number of contraction inferences in a derivation. -/
def LDeriv.contrCount {ν : Type} {G : LSig} : {Γ : Multiset (ν × LTy)} → {t : FreeTerm ν} →
    {A : LTy} → LDeriv G Γ t A → Nat
  | _, _, _, .ax _ _ => 0
  | _, _, _, .zero => 0
  | _, _, _, .succ d => d.contrCount
  | _, _, _, .wrap d e => d.contrCount + e.contrCount
  | _, _, _, .recur d e f => d.contrCount + e.contrCount + f.contrCount
  | _, _, _, .weaken _ _ d => d.contrCount
  | _, _, _, .contract _ _ d => d.contrCount + 1
  | _, _, _, .derelict _ _ d => d.contrCount
  | _, _, _, .promote _ d => d.contrCount

/-- Total number of weakening inferences in a derivation. -/
def LDeriv.weakCount {ν : Type} {G : LSig} : {Γ : Multiset (ν × LTy)} → {t : FreeTerm ν} →
    {A : LTy} → LDeriv G Γ t A → Nat
  | _, _, _, .ax _ _ => 0
  | _, _, _, .zero => 0
  | _, _, _, .succ d => d.weakCount
  | _, _, _, .wrap d e => d.weakCount + e.weakCount
  | _, _, _, .recur d e f => d.weakCount + e.weakCount + f.weakCount
  | _, _, _, .weaken _ _ d => d.weakCount + 1
  | _, _, _, .contract _ _ d => d.weakCount
  | _, _, _, .derelict _ _ d => d.weakCount
  | _, _, _, .promote _ d => d.weakCount

/-- Number of context entries on the variable `x`. -/
def ctxCount {ν : Type} [DecidableEq ν] (x : ν) (Γ : Multiset (ν × LTy)) : Nat :=
  Multiset.countP (fun e : ν × LTy => e.1 = x) Γ

theorem countP_single {α : Type} (p : α → Prop) [DecidablePred p] (a : α) :
    Multiset.countP p {a} = if p a then 1 else 0 := by
  rw [← Multiset.cons_zero, Multiset.countP_cons, Multiset.countP_zero, Nat.zero_add]

/-- **Resource balance.** In every derivation, the occurrences of a variable in the subject plus
the weakenings on it equal its context entries plus the contractions on it. Dereliction and
promotion do not change the count; no other rule creates or deletes a resource. -/
theorem LDeriv.balance {ν : Type} [DecidableEq ν] {G : LSig} {Γ : Multiset (ν × LTy)}
    {t : FreeTerm ν} {A : LTy} (d : LDeriv G Γ t A) (x : ν) :
    occ x t + d.weakOn x = ctxCount x Γ + d.contrOn x := by
  induction d with
  | ax y B =>
      by_cases h : y = x <;>
        simp [occ, ctxCount, LDeriv.weakOn, LDeriv.contrOn, countP_single, h]
  | zero => simp [occ, ctxCount, LDeriv.weakOn, LDeriv.contrOn]
  | succ d ih => simpa [occ, LDeriv.weakOn, LDeriv.contrOn] using ih
  | wrap d e ihd ihe =>
      simp only [occ, LDeriv.weakOn, LDeriv.contrOn, ctxCount, Multiset.countP_add] at ihd ihe ⊢
      omega
  | recur d e f ihd ihe ihf =>
      simp only [occ, LDeriv.weakOn, LDeriv.contrOn, ctxCount, Multiset.countP_add] at ihd ihe ihf ⊢
      omega
  | weaken y B d ih =>
      simp only [LDeriv.weakOn, LDeriv.contrOn, ctxCount, Multiset.countP_cons] at ih ⊢
      split_ifs at ih ⊢ <;> omega
  | contract y B d ih =>
      simp only [LDeriv.weakOn, LDeriv.contrOn, ctxCount, Multiset.countP_cons] at ih ⊢
      split_ifs at ih ⊢ <;> omega
  | derelict y B d ih =>
      simp only [LDeriv.weakOn, LDeriv.contrOn, ctxCount, Multiset.countP_cons] at ih ⊢
      exact ih
  | promote _ d ih => simpa [LDeriv.weakOn, LDeriv.contrOn] using ih

/-- **No structural rule without exponentials.** Over a context with no `!` entry, a derivation
uses no weakening and no contraction. -/
theorem LDeriv.noStructural {ν : Type} [DecidableEq ν] {G : LSig} {Γ : Multiset (ν × LTy)}
    {t : FreeTerm ν} {A : LTy} (d : LDeriv G Γ t A) (hΓ : ∀ e ∈ Γ, ¬ e.2.IsBang) (x : ν) :
    d.weakOn x = 0 ∧ d.contrOn x = 0 := by
  induction d with
  | ax y B => exact ⟨rfl, rfl⟩
  | zero => exact ⟨rfl, rfl⟩
  | succ d ih => exact ih hΓ
  | wrap d e ihd ihe =>
      have h1 := ihd (fun e he => hΓ e (Multiset.mem_add.2 (Or.inl he)))
      have h2 := ihe (fun e' he => hΓ e' (Multiset.mem_add.2 (Or.inr he)))
      simp only [LDeriv.weakOn, LDeriv.contrOn]
      omega
  | recur d e f ihd ihe ihf =>
      have h1 := ihd (fun e he => hΓ e (Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inl he)))))
      have h2 := ihe (fun e' he => hΓ e' (Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inr he)))))
      have h3 := ihf (fun e' he => hΓ e' (Multiset.mem_add.2 (Or.inr he)))
      simp only [LDeriv.weakOn, LDeriv.contrOn]
      omega
  | weaken y B d _ => exact absurd trivial (hΓ (y, .bang B) (Multiset.mem_cons_self _ _))
  | contract y B d _ => exact absurd trivial (hΓ (y, .bang B) (Multiset.mem_cons_self _ _))
  | derelict y B d _ => exact absurd trivial (hΓ (y, .bang B) (Multiset.mem_cons_self _ _))
  | promote _ d ih => exact ih hΓ

/-- Over an `!`-free context, typing preserves every variable's occurrence count exactly. -/
theorem LDeriv.occ_eq_ctxCount {ν : Type} [DecidableEq ν] {G : LSig} {Γ : Multiset (ν × LTy)}
    {t : FreeTerm ν} {A : LTy} (d : LDeriv G Γ t A) (hΓ : ∀ e ∈ Γ, ¬ e.2.IsBang) (x : ν) :
    occ x t = ctxCount x Γ := by
  have hb := d.balance x
  have hn := d.noStructural hΓ x
  omega

/-- **Generic barrier.** A rewrite rule `l → r` typed on both sides in one `!`-free context
preserves the occurrence count of every variable; a rule that changes a count is rejected. -/
theorem linearRuleTyping_occ_eq {ν : Type} [DecidableEq ν] {G : LSig} {Γ : Multiset (ν × LTy)}
    {l r : FreeTerm ν} {T : LTy} (dl : LDeriv G Γ l T) (dr : LDeriv G Γ r T)
    (hΓ : ∀ e ∈ Γ, ¬ e.2.IsBang) (x : ν) : occ x l = occ x r := by
  rw [dl.occ_eq_ctxCount hΓ x, dr.occ_eq_ctxCount hΓ x]

/-- The rule context: each variable of the left side once, with its assigned formula. -/
def ruleCtx (τ : RV → LTy) : Multiset (RV × LTy) :=
  (RV.s, τ .s) ::ₘ (RV.b, τ .b) ::ₘ (RV.n, τ .n) ::ₘ 0

theorem ctxCount_ruleCtx (τ : RV → LTy) (x : RV) : ctxCount x (ruleCtx τ) = 1 := by
  cases x <;> simp [ctxCount, ruleCtx, countP_single]

/-- Native data of `linearLogicTypingBarrier`: the linear signature of the free symbols, the
formula of each rule variable, and the formula of both sides of the rule. -/
structure linearLogicTypingBarrierData where
  sig : LSig
  ctx : RV → LTy
  res : LTy

/-- Girard 1987, Definition 1.15: the exponential-free calculus, in which weakening and contraction
are forbidden. The laws place the rule context in that fragment: no variable formula contains `!`. -/
def linearLogicTypingBarrierLaws (M : linearLogicTypingBarrierData) : Prop :=
  ∀ x : RV, (M.ctx x).ExpFree

/-- The discipline accepts the successor rule when both sides are derivable at the same formula in
the rule context (subject reduction of the typed rule). Adapter: the rule schema `succLhs →
succRhs` of `RootStep.recurSucc` over the three rule variables. -/
def linearLogicTypingBarrierAccepts (M : linearLogicTypingBarrierData) : Prop :=
  Nonempty (LDeriv M.sig (ruleCtx M.ctx) succLhs M.res) ∧
    Nonempty (LDeriv M.sig (ruleCtx M.ctx) succRhs M.res)

/-- Verdict: fragment barrier. No exponential-free typing derives the successor rule: its step
variable occurs once on the left and twice on the right. -/
def linearLogicTypingBarrierResult (M : linearLogicTypingBarrierData) : Prop :=
  ¬ linearLogicTypingBarrierAccepts M

/-- Every exponential-free typing rejects the successor rule, derived from the rules through the
resource balance and the absence of structural rules. -/
theorem linearLogicTypingBarrier_universal :
    ∀ M, linearLogicTypingBarrierLaws M → linearLogicTypingBarrierResult M := by
  intro M hL hA
  obtain ⟨⟨dl⟩, ⟨dr⟩⟩ := hA
  have hΓ : ∀ e ∈ ruleCtx M.ctx, ¬ e.2.IsBang := by
    intro e he
    simp only [ruleCtx, Multiset.mem_cons, Multiset.notMem_zero, or_false] at he
    rcases he with rfl | rfl | rfl <;> exact LTy.not_isBang_of_expFree (hL _)
  have h := linearRuleTyping_occ_eq dl dr hΓ RV.s
  rw [occ_succLhs.2.1, occ_succRhs.2.1] at h
  exact absurd h (by decide)

/-- The atoms of the witness: `A` for the result, `B` for the payload, `N` for the counter. -/
def atA : LTy := .atom 0
def atB : LTy := .atom 1
def atN : LTy := .atom 2

/-- The linear signature `zero : N`, `succ : N ⊸ N`, `wrap : B ⊸ A ⊸ A`,
`recur : A ⊸ B ⊸ N ⊸ A`. -/
def witnessSig : LSig where
  zeroTy := atN
  succArg := atN
  succTy := atN
  wrapArg₁ := atB
  wrapArg₂ := atA
  wrapTy := atA
  recurArg₁ := atA
  recurArg₂ := atB
  recurArg₃ := atN
  recurTy := atA

/-- The linear variable formulas `b : A`, `s : B`, `n : N`. -/
def linearCtx : RV → LTy
  | .b => atA
  | .s => atB
  | .n => atN

/-- The reusable payload: `s : !B`, the other two unchanged. -/
def reusableCtx : RV → LTy
  | .b => atA
  | .s => .bang atB
  | .n => atN

def linearLogicTypingBarrierWitness : linearLogicTypingBarrierData where
  sig := witnessSig
  ctx := linearCtx
  res := atA

theorem linearLogicTypingBarrierWitness_laws :
    linearLogicTypingBarrierLaws linearLogicTypingBarrierWitness := by
  intro x
  cases x <;> trivial

theorem linearLogicTypingBarrierWitness_result :
    linearLogicTypingBarrierResult linearLogicTypingBarrierWitness :=
  linearLogicTypingBarrier_universal _ linearLogicTypingBarrierWitness_laws

/-- Transport of a derivation along an equality of contexts. -/
def LDeriv.recast {ν : Type} {G : LSig} {Γ Γ' : Multiset (ν × LTy)} {t : FreeTerm ν} {A : LTy} :
    Γ = Γ' → LDeriv G Γ t A → LDeriv G Γ' t A
  | rfl, d => d

theorem LDeriv.contrCount_recast {ν : Type} {G : LSig} {Γ Γ' : Multiset (ν × LTy)}
    {t : FreeTerm ν} {A : LTy} (h : Γ = Γ') (d : LDeriv G Γ t A) :
    (d.recast h).contrCount = d.contrCount := by
  subst h
  rfl

theorem LDeriv.weakCount_recast {ν : Type} {G : LSig} {Γ Γ' : Multiset (ν × LTy)}
    {t : FreeTerm ν} {A : LTy} (h : Γ = Γ') (d : LDeriv G Γ t A) :
    (d.recast h).weakCount = d.weakCount := by
  subst h
  rfl

/-- The context `b : A, n : N`. -/
def ctx0 : Multiset (RV × LTy) := (RV.b, atA) ::ₘ (RV.n, atN) ::ₘ 0

/-- The recursive call `recur(b, s, n)` typed linearly. -/
def recCallDeriv : LDeriv witnessSig ({(RV.b, atA)} + {(RV.s, atB)} + {(RV.n, atN)})
    (.recur (.var RV.b) (.var RV.s) (.var RV.n)) atA :=
  .recur (.ax RV.b atA) (.ax RV.s atB) (.ax RV.n atN)

/-- The left side typed linearly. -/
def lhsLinDeriv : LDeriv witnessSig ({(RV.b, atA)} + {(RV.s, atB)} + {(RV.n, atN)}) succLhs atA :=
  .recur (.ax RV.b atA) (.ax RV.s atB) (.succ (.ax RV.n atN))

/-- The right side typed with two linear copies of `s`. -/
def rhsLinDeriv :
    LDeriv witnessSig ({(RV.s, atB)} + ({(RV.b, atA)} + {(RV.s, atB)} + {(RV.n, atN)})) succRhs
      atA :=
  .wrap (.ax RV.s atB) recCallDeriv

theorem ctx_lhs_eq :
    ({(RV.b, atA)} + {(RV.s, atB)} + {(RV.n, atN)} : Multiset (RV × LTy)) = (RV.s, atB) ::ₘ ctx0 := by
  decide

theorem ctx_rhs_eq :
    ({(RV.s, atB)} + ({(RV.b, atA)} + {(RV.s, atB)} + {(RV.n, atN)}) : Multiset (RV × LTy)) =
      (RV.s, atB) ::ₘ (RV.s, atB) ::ₘ ctx0 := by
  decide

theorem ctx_swap :
    ((RV.s, LTy.bang atB) ::ₘ (RV.s, atB) ::ₘ ctx0 : Multiset (RV × LTy)) =
      (RV.s, atB) ::ₘ (RV.s, LTy.bang atB) ::ₘ ctx0 :=
  Multiset.cons_swap _ _ _

/-- The left side typed in the reusable context: one dereliction on `s`. -/
def reusableLhsDeriv : LDeriv witnessSig (ruleCtx reusableCtx) succLhs atA :=
  LDeriv.derelict RV.s atB (lhsLinDeriv.recast ctx_lhs_eq)

/-- The right side typed in the reusable context: one contraction and two derelictions on `s`. -/
def reusableRhsDeriv : LDeriv witnessSig (ruleCtx reusableCtx) succRhs atA :=
  LDeriv.contract RV.s atB
    (LDeriv.derelict RV.s atB
      ((LDeriv.derelict RV.s atB (rhsLinDeriv.recast ctx_rhs_eq)).recast ctx_swap))

theorem reusableRhsDeriv_contrCount : reusableRhsDeriv.contrCount = 1 := by
  simp [reusableRhsDeriv, LDeriv.contrCount_recast, LDeriv.contrCount, rhsLinDeriv, recCallDeriv]

theorem reusableLhsDeriv_contrCount : reusableLhsDeriv.contrCount = 0 := by
  simp [reusableLhsDeriv, LDeriv.contrCount_recast, LDeriv.contrCount, lhsLinDeriv]

theorem reusableRhsDeriv_weakCount : reusableRhsDeriv.weakCount = 0 := by
  simp [reusableRhsDeriv, LDeriv.weakCount_recast, LDeriv.weakCount, rhsLinDeriv, recCallDeriv]

theorem reusableLhsDeriv_weakCount : reusableLhsDeriv.weakCount = 0 := by
  simp [reusableLhsDeriv, LDeriv.weakCount_recast, LDeriv.weakCount, lhsLinDeriv]

/-- Over the rule variables, the total contraction count is the sum of the per-variable counts. -/
theorem LDeriv.contrCount_eq_sum {G : LSig} {Γ : Multiset (RV × LTy)} {t : FreeTerm RV} {A : LTy}
    (d : LDeriv G Γ t A) : d.contrCount = d.contrOn .b + d.contrOn .s + d.contrOn .n := by
  induction d with
  | ax => rfl
  | zero => rfl
  | succ d ih => simpa [LDeriv.contrCount, LDeriv.contrOn] using ih
  | wrap d e ihd ihe =>
      simp only [LDeriv.contrCount, LDeriv.contrOn, ihd, ihe]
      omega
  | recur d e f ihd ihe ihf =>
      simp only [LDeriv.contrCount, LDeriv.contrOn, ihd, ihe, ihf]
      omega
  | weaken y B d ih => simpa [LDeriv.contrCount, LDeriv.contrOn] using ih
  | contract y B d ih =>
      simp only [LDeriv.contrCount, LDeriv.contrOn, ih]
      cases y <;> simp <;> omega
  | derelict y B d ih => simpa [LDeriv.contrCount, LDeriv.contrOn] using ih
  | promote _ d ih => simpa [LDeriv.contrCount, LDeriv.contrOn] using ih

/-- Over the rule variables, the total weakening count is the sum of the per-variable counts. -/
theorem LDeriv.weakCount_eq_sum {G : LSig} {Γ : Multiset (RV × LTy)} {t : FreeTerm RV} {A : LTy}
    (d : LDeriv G Γ t A) : d.weakCount = d.weakOn .b + d.weakOn .s + d.weakOn .n := by
  induction d with
  | ax => rfl
  | zero => rfl
  | succ d ih => simpa [LDeriv.weakCount, LDeriv.weakOn] using ih
  | wrap d e ihd ihe =>
      simp only [LDeriv.weakCount, LDeriv.weakOn, ihd, ihe]
      omega
  | recur d e f ihd ihe ihf =>
      simp only [LDeriv.weakCount, LDeriv.weakOn, ihd, ihe, ihf]
      omega
  | weaken y B d ih =>
      simp only [LDeriv.weakCount, LDeriv.weakOn, ih]
      cases y <;> simp <;> omega
  | contract y B d ih => simpa [LDeriv.weakCount, LDeriv.weakOn] using ih
  | derelict y B d ih => simpa [LDeriv.weakCount, LDeriv.weakOn] using ih
  | promote _ d ih => simpa [LDeriv.weakCount, LDeriv.weakOn] using ih

/-- **Contractions equal the duplication count** (anchor of the linear-logic sentence of the
related-work section, control B2). For every typing of the successor rule, under any signature and
any variable formulas, the contractions of both derivations equal the duplication count of the
rule plus the weakenings; so every typing needs at least `dupCount = 1` contraction, and a
weakening-free typing uses exactly `dupCount`. -/
theorem succRule_contractions_eq_dupCount (G : LSig) (τ : RV → LTy) (T : LTy)
    (dl : LDeriv G (ruleCtx τ) succLhs T) (dr : LDeriv G (ruleCtx τ) succRhs T) :
    dl.contrCount + dr.contrCount = dupCount + dl.weakCount + dr.weakCount := by
  rw [dl.contrCount_eq_sum, dr.contrCount_eq_sum, dl.weakCount_eq_sum, dr.weakCount_eq_sum,
    dupCount_eq_one]
  have lb := dl.balance .b
  have ls := dl.balance .s
  have ln := dl.balance .n
  have rb := dr.balance .b
  have rs := dr.balance .s
  have rn := dr.balance .n
  rw [ctxCount_ruleCtx] at lb ls ln rb rs rn
  rw [occ_succLhs.1] at lb
  rw [occ_succLhs.2.1] at ls
  rw [occ_succLhs.2.2] at ln
  rw [occ_succRhs.1] at rb
  rw [occ_succRhs.2.1] at rs
  rw [occ_succRhs.2.2] at rn
  omega

/-- Every typing of the successor rule needs at least `dupCount` contractions. -/
theorem succRule_contractions_ge (G : LSig) (τ : RV → LTy) (T : LTy)
    (dl : LDeriv G (ruleCtx τ) succLhs T) (dr : LDeriv G (ruleCtx τ) succRhs T) :
    dupCount ≤ dl.contrCount + dr.contrCount := by
  have := succRule_contractions_eq_dupCount G τ T dl dr
  omega

/-- **Defining feature.** A reusable payload `s : !B` makes the successor rule typable with
exactly `dupCount = 1` contraction, the minimum over all typings; the linear call
`recur(b, s, succ n) → recur(b, s, n)` is typable without exponentials. -/
theorem linearLogicTypingBarrierWitness_feature :
    linearLogicTypingBarrierAccepts { linearLogicTypingBarrierWitness with ctx := reusableCtx } ∧
      reusableLhsDeriv.contrCount + reusableRhsDeriv.contrCount = dupCount ∧
      (∀ (dl : LDeriv witnessSig (ruleCtx reusableCtx) succLhs atA)
          (dr : LDeriv witnessSig (ruleCtx reusableCtx) succRhs atA),
        reusableLhsDeriv.contrCount + reusableRhsDeriv.contrCount ≤
          dl.contrCount + dr.contrCount) ∧
      Nonempty (LDeriv witnessSig (ruleCtx linearCtx) succLhs atA) ∧
      Nonempty (LDeriv witnessSig (ruleCtx linearCtx)
        (.recur (.var RV.b) (.var RV.s) (.var RV.n)) atA) := by
  refine ⟨⟨⟨reusableLhsDeriv⟩, ⟨reusableRhsDeriv⟩⟩, ?_, ?_, ?_, ?_⟩
  · rw [reusableLhsDeriv_contrCount, reusableRhsDeriv_contrCount, dupCount_eq_one]
  · intro dl dr
    rw [reusableLhsDeriv_contrCount, reusableRhsDeriv_contrCount]
    have := succRule_contractions_ge witnessSig reusableCtx atA dl dr
    rw [dupCount_eq_one] at this
    omega
  · exact ⟨lhsLinDeriv.recast ctx_lhs_eq⟩
  · exact ⟨recCallDeriv.recast ctx_lhs_eq⟩

/-- **Mutation.** Making the payload formula `!B`, everything else fixed, breaks the
exponential-free law and the barrier: the rule is then accepted. -/
theorem linearLogicTypingBarrier_mutation :
    ¬ linearLogicTypingBarrierLaws { linearLogicTypingBarrierWitness with ctx := reusableCtx } ∧
      ¬ linearLogicTypingBarrierResult
        { linearLogicTypingBarrierWitness with ctx := reusableCtx } :=
  ⟨fun h => h .s, fun h => h linearLogicTypingBarrierWitness_feature.1⟩

/-- **Scope of the fragment.** Omitted from Girard 1987: the cut rule, the additive and quantifier
rules, the one-sided classical presentation (the fragment is its two-sided term reading), proof
nets, and the phase semantics of Theorem 1.22. The statement named here is the omitted cut rule in
its term form, admissibility of a cut on a formula that is not `!` against a variable that is fresh
in the other context; it is the cut-elimination content of the source for this fragment and is not
proved in this module. -/
def linearLogicTypingBarrier_scope : Prop :=
  ∀ (G : LSig) (Γ Δ : Multiset (RV × LTy)) (u v : FreeTerm RV) (x : RV) (A B : LTy),
    ¬ A.IsBang → (∀ e ∈ Δ, e.1 ≠ x) → LDeriv G Γ u A → LDeriv G ((x, A) ::ₘ Δ) v B →
      Nonempty (LDeriv G (Γ + Δ) (FreeTerm.subst (fun y => if y = x then u else .var y) v) B)

/-! ## Values of the free algebra

The three definitional disciplines below compute on the closed constructor terms of the free
signature: `zero`, `succ`, `wrap`. -/

/-- Closed constructor terms of the free signature. -/
inductive Val where
  | zero
  | succ (v : Val)
  | wrap (u v : Val)
  deriving DecidableEq, Repr

/-- Number of constructors. -/
def Val.size : Val → Nat
  | .zero => 1
  | .succ v => v.size + 1
  | .wrap u v => u.size + v.size + 1

/-- Height of the constructor tree (`zero` has height `0`). -/
def Val.hgt : Val → Nat
  | .zero => 0
  | .succ v => v.hgt + 1
  | .wrap u v => max u.hgt v.hgt + 1

/-- Unary numerals. -/
def numeral : Nat → Val
  | 0 => .zero
  | k + 1 => .succ (numeral k)

/-- The free recursor on values: `recur(b, s, numeral k)` normalizes to `k` wrappers of `s`
around `b`. -/
def recurVal (b s : Val) : Nat → Val
  | 0 => b
  | k + 1 => .wrap s (recurVal b s k)

theorem Val.size_pos (v : Val) : 1 ≤ v.size := by
  cases v <;> simp [Val.size]

/-- Iteration of a recurrence along a counter value: one case per constructor. -/
def recIter (fb : Val) (fs : Val → Val → Val) (fw : Val → Val → Val → Val → Val) : Val → Val
  | .zero => fb
  | .succ c => fs c (recIter fb fs fw c)
  | .wrap u w => fw u w (recIter fb fs fw u) (recIter fb fs fw w)

/-! ## Row `ramifiedRecursionTypingBarrier`

Leivant, *Ramified recurrence and computational complexity I: Word recurrence and poly-time*,
in Clote and Remmel (eds.), Feasible Mathematics II, Birkhäuser 1995, 320-343, with Leivant and
Marion, *Lambda calculus characterizations of poly-time*, Fundamenta Informaticae 19 (1993)
167-184. The clauses implemented are those of tiered recursion over a free algebra as restated by
Dal Lago, Martini and Zorzi (*General ramified recurrence is sound for polynomial time*, 2010,
Section 2): constructors have tiers `(i, …, i) → i`, projections return the tier of their
argument, composition substitutes only at equal tiers, and a recurrence whose result has tier `i`
must recur on an argument of tier `j > i`. Inputs may be used any number of times at their tier;
the fragment inserts no linearity condition. Here the recurrence is a term former `rec` with one
case per constructor of the free algebra `{zero, succ, wrap}`; its step cases see the constructor
arguments (tier `j`), the recursive results (tier `i`), and the enclosing variables. -/

/-- Expressions of tiered recurrence, with de Bruijn variables. In `rec ctr base stepS stepW`,
`stepS` sees `pred, r` in front of the enclosing variables and `stepW` sees `u, w, ru, rw`. -/
inductive REx where
  | var (k : Nat)
  | zero
  | succ (e : REx)
  | wrap (e₁ e₂ : REx)
  | recur (ctr base stepS stepW : REx)
  deriving DecidableEq, Repr

/-- Evaluation of tiered expressions. -/
def reval : REx → List Val → Val
  | .var k, ρ => ρ.getD k .zero
  | .zero, _ => .zero
  | .succ e, ρ => .succ (reval e ρ)
  | .wrap e₁ e₂, ρ => .wrap (reval e₁ ρ) (reval e₂ ρ)
  | .recur ctr base stepS stepW, ρ =>
      recIter (reval base ρ) (fun c r => reval stepS (c :: r :: ρ))
        (fun u w ru rw => reval stepW (u :: w :: ru :: rw :: ρ)) (reval ctr ρ)

/-- The tier judgment `Γ ⊢ e : i` of tiered recursion (`Γ` lists the tiers of the variables). -/
inductive RTy : List Nat → REx → Nat → Prop where
  | var {Γ : List Nat} {k i : Nat} : Γ[k]? = some i → RTy Γ (.var k) i
  | zero {Γ : List Nat} {i : Nat} : RTy Γ .zero i
  | succ {Γ : List Nat} {e : REx} {i : Nat} : RTy Γ e i → RTy Γ (.succ e) i
  | wrap {Γ : List Nat} {e₁ e₂ : REx} {i : Nat} : RTy Γ e₁ i → RTy Γ e₂ i → RTy Γ (.wrap e₁ e₂) i
  | recur {Γ : List Nat} {ctr base stepS stepW : REx} {i j : Nat} : i < j → RTy Γ ctr j →
      RTy Γ base i → RTy (j :: i :: Γ) stepS i → RTy (j :: j :: i :: i :: Γ) stepW i →
      RTy Γ (.recur ctr base stepS stepW) i

/-- Largest height of a variable whose tier is above `i`. -/
def hAbove : List Nat → List Val → Nat → Nat
  | t :: Γ, v :: ρ, i => max (if i < t then v.hgt else 0) (hAbove Γ ρ i)
  | _, _, _ => 0

/-- Largest height of a variable whose tier is exactly `i`. -/
def hAt : List Nat → List Val → Nat → Nat
  | t :: Γ, v :: ρ, i => max (if t = i then v.hgt else 0) (hAt Γ ρ i)
  | _, _, _ => 0

theorem hgt_getD_le_hAt : ∀ (Γ : List Nat) (ρ : List Val) (k i : Nat), Γ[k]? = some i →
    (ρ.getD k .zero).hgt ≤ hAt Γ ρ i
  | [], _, _, _, h => by simp at h
  | t :: Γ, [], k, i, _ => by cases k <;> simp [Val.hgt]
  | t :: Γ, v :: ρ, 0, i, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [hAt]
  | t :: Γ, v :: ρ, k + 1, i, h => by
      simp only [List.getElem?_cons_succ] at h
      have := hgt_getD_le_hAt Γ ρ k i h
      simp only [List.getD_cons_succ, hAt]
      omega

theorem hAbove_le_of_lt : ∀ (Γ : List Nat) (ρ : List Val) {i j : Nat}, i < j →
    hAbove Γ ρ j ≤ hAbove Γ ρ i ∧ hAt Γ ρ j ≤ hAbove Γ ρ i
  | [], _, _, _, _ => by simp [hAbove, hAt]
  | _ :: _, [], _, _, _ => by simp [hAbove, hAt]
  | t :: Γ, v :: ρ, i, j, hij => by
      have ih := hAbove_le_of_lt Γ ρ hij
      simp only [hAbove, hAt]
      constructor
      · by_cases h1 : j < t
        · have h2 : i < t := by omega
          simp only [h1, h2, if_true]
          omega
        · simp only [h1, if_false]
          split_ifs <;> omega
      · by_cases h1 : t = j
        · have h2 : i < t := by omega
          simp only [h1, if_true, show i < j from hij]
          omega
        · simp only [h1, if_false]
          split_ifs <;> omega

theorem hAbove_cons_lt {i t : Nat} (h : i < t) (Γ : List Nat) (v : Val) (ρ : List Val) :
    hAbove (t :: Γ) (v :: ρ) i = max v.hgt (hAbove Γ ρ i) := by
  simp [hAbove, h]

theorem hAbove_cons_self (i : Nat) (Γ : List Nat) (v : Val) (ρ : List Val) :
    hAbove (i :: Γ) (v :: ρ) i = hAbove Γ ρ i := by
  simp [hAbove]

theorem hAt_cons_self (i : Nat) (Γ : List Nat) (v : Val) (ρ : List Val) :
    hAt (i :: Γ) (v :: ρ) i = max v.hgt (hAt Γ ρ i) := by
  simp [hAt]

theorem hAt_cons_ne {i t : Nat} (h : t ≠ i) (Γ : List Nat) (v : Val) (ρ : List Val) :
    hAt (t :: Γ) (v :: ρ) i = hAt Γ ρ i := by
  simp [hAt, h]

/-- The height budget of an expression: a polynomial in the heights above the result tier. -/
def RB : REx → Nat → Nat
  | .var _, _ => 0
  | .zero, _ => 0
  | .succ e, H => RB e H + 1
  | .wrap e₁ e₂, H => RB e₁ H + RB e₂ H + 1
  | .recur ctr base stepS stepW, H =>
      (RB ctr H + H) * (RB stepS (RB ctr H + H) + RB stepW (RB ctr H + H) + 1) + RB base H

theorem RB_mono : ∀ (e : REx) {H H' : Nat}, H ≤ H' → RB e H ≤ RB e H'
  | .var _, _, _, _ => le_rfl
  | .zero, _, _, _ => le_rfl
  | .succ e, _, _, h => by simp only [RB]; have := RB_mono e h; omega
  | .wrap e₁ e₂, _, _, h => by
      simp only [RB]; have := RB_mono e₁ h; have := RB_mono e₂ h; omega
  | .recur ctr base stepS stepW, H, H', h => by
      simp only [RB]
      have hc := RB_mono ctr h
      have hb := RB_mono base h
      have hC : RB ctr H + H ≤ RB ctr H' + H' := by omega
      have hs := RB_mono stepS hC
      have hw := RB_mono stepW hC
      exact Nat.add_le_add (Nat.mul_le_mul hC (by omega)) hb

/-- The height budget is a polynomial with natural coefficients. -/
theorem RB_polynomial : ∀ e : REx, ∃ p : Polynomial ℕ, ∀ H, RB e H = p.eval H
  | .var _ => ⟨0, fun _ => by simp [RB]⟩
  | .zero => ⟨0, fun _ => by simp [RB]⟩
  | .succ e => by
      obtain ⟨p, hp⟩ := RB_polynomial e
      exact ⟨p + 1, fun H => by simp [RB, hp]⟩
  | .wrap e₁ e₂ => by
      obtain ⟨p₁, h₁⟩ := RB_polynomial e₁
      obtain ⟨p₂, h₂⟩ := RB_polynomial e₂
      exact ⟨p₁ + p₂ + 1, fun H => by simp [RB, h₁, h₂]⟩
  | .recur ctr base stepS stepW => by
      obtain ⟨pc, hc⟩ := RB_polynomial ctr
      obtain ⟨pb, hb⟩ := RB_polynomial base
      obtain ⟨ps, hs⟩ := RB_polynomial stepS
      obtain ⟨pw, hw⟩ := RB_polynomial stepW
      refine ⟨(pc + Polynomial.X) * (ps.comp (pc + Polynomial.X) + pw.comp (pc + Polynomial.X) + 1)
        + pb, fun H => ?_⟩
      simp [RB, hc, hb, hs, hw, Polynomial.eval_comp]

/-- **Soundness of tiering (height form).** A value of tier `i` is no higher than a polynomial in
the heights of the variables above tier `i`, plus the largest height at tier `i`. The ramification
condition `i < j` places the counter among the variables above `i`; the recursive results enter
only through the maximum at tier `i`. -/
theorem RTy.hgt_bound {Γ : List Nat} {e : REx} {i : Nat} (h : RTy Γ e i) :
    ∀ ρ : List Val, (reval e ρ).hgt ≤ RB e (hAbove Γ ρ i) + hAt Γ ρ i := by
  induction h with
  | var hk =>
      intro ρ
      simp only [reval, RB, Nat.zero_add]
      exact hgt_getD_le_hAt _ ρ _ _ hk
  | zero => intro ρ; simp [reval, Val.hgt]
  | succ _ ih =>
      intro ρ
      have := ih ρ
      simp only [reval, Val.hgt, RB]
      omega
  | wrap _ _ ih₁ ih₂ =>
      intro ρ
      have h1 := ih₁ ρ
      have h2 := ih₂ ρ
      simp only [reval, Val.hgt, RB]
      omega
  | @recur Γ ctr base stepS stepW i j hij _ _ _ _ ihc ihb ihs ihw =>
      intro ρ
      set H := hAbove Γ ρ i with hH
      set M := hAt Γ ρ i with hM
      set C := RB ctr H + H with hCdef
      set K := RB stepS C + RB stepW C + 1 with hK
      have hmon := hAbove_le_of_lt Γ ρ hij
      have hc : (reval ctr ρ).hgt ≤ C := by
        have h1 := ihc ρ
        have h2 : RB ctr (hAbove Γ ρ j) ≤ RB ctr H := RB_mono ctr hmon.1
        have h3 : hAt Γ ρ j ≤ H := hmon.2
        omega
      have key : ∀ c : Val, c.hgt ≤ C →
          (recIter (reval base ρ) (fun c r => reval stepS (c :: r :: ρ))
            (fun u w ru rw => reval stepW (u :: w :: ru :: rw :: ρ)) c).hgt ≤
            c.hgt * K + RB base H + M := by
        intro c
        induction c with
        | zero =>
            intro _
            have := ihb ρ
            simp only [recIter, Val.hgt, Nat.zero_mul, Nat.zero_add]
            exact this
        | succ c ihc' =>
            intro hcC
            simp only [Val.hgt] at hcC
            have hr := ihc' (by omega)
            have hs := ihs (c :: recIter (reval base ρ) (fun c r => reval stepS (c :: r :: ρ))
              (fun u w ru rw => reval stepW (u :: w :: ru :: rw :: ρ)) c :: ρ)
            have hA : hAbove (j :: i :: Γ) (c :: recIter (reval base ρ)
                (fun c r => reval stepS (c :: r :: ρ))
                (fun u w ru rw => reval stepW (u :: w :: ru :: rw :: ρ)) c :: ρ) i ≤ C := by
              rw [hAbove_cons_lt hij, hAbove_cons_self]
              exact max_le (by omega) (by omega)
            have hM' : hAt (j :: i :: Γ) (c :: recIter (reval base ρ)
                (fun c r => reval stepS (c :: r :: ρ))
                (fun u w ru rw => reval stepW (u :: w :: ru :: rw :: ρ)) c :: ρ) i ≤
                c.hgt * K + RB base H + M := by
              rw [hAt_cons_ne (Nat.ne_of_gt hij), hAt_cons_self]
              exact max_le hr (by omega)
            have hsC := RB_mono stepS hA
            simp only [recIter, Val.hgt]
            have hKs : RB stepS C ≤ K := by omega
            have : c.hgt * K + K = (c.hgt + 1) * K := by ring
            omega
        | wrap u w ihu ihw' =>
            intro hcC
            simp only [Val.hgt] at hcC
            have hu : u.hgt ≤ C := (le_max_left u.hgt w.hgt).trans (by omega)
            have hw : w.hgt ≤ C := (le_max_right u.hgt w.hgt).trans (by omega)
            have hru := ihu hu
            have hrw := ihw' hw
            have hs := ihw (u :: w ::
              recIter (reval base ρ) (fun c r => reval stepS (c :: r :: ρ))
                (fun u w ru rw => reval stepW (u :: w :: ru :: rw :: ρ)) u ::
              recIter (reval base ρ) (fun c r => reval stepS (c :: r :: ρ))
                (fun u w ru rw => reval stepW (u :: w :: ru :: rw :: ρ)) w :: ρ)
            have hA : hAbove (j :: j :: i :: i :: Γ) (u :: w ::
                recIter (reval base ρ) (fun c r => reval stepS (c :: r :: ρ))
                  (fun u w ru rw => reval stepW (u :: w :: ru :: rw :: ρ)) u ::
                recIter (reval base ρ) (fun c r => reval stepS (c :: r :: ρ))
                  (fun u w ru rw => reval stepW (u :: w :: ru :: rw :: ρ)) w :: ρ) i ≤ C := by
              rw [hAbove_cons_lt hij, hAbove_cons_lt hij, hAbove_cons_self, hAbove_cons_self]
              exact max_le hu (max_le hw (by omega))
            have h1 : u.hgt * K ≤ (max u.hgt w.hgt) * K :=
              Nat.mul_le_mul_right _ (le_max_left _ _)
            have h2 : w.hgt * K ≤ (max u.hgt w.hgt) * K :=
              Nat.mul_le_mul_right _ (le_max_right _ _)
            have hM' : hAt (j :: j :: i :: i :: Γ) (u :: w ::
                recIter (reval base ρ) (fun c r => reval stepS (c :: r :: ρ))
                  (fun u w ru rw => reval stepW (u :: w :: ru :: rw :: ρ)) u ::
                recIter (reval base ρ) (fun c r => reval stepS (c :: r :: ρ))
                  (fun u w ru rw => reval stepW (u :: w :: ru :: rw :: ρ)) w :: ρ) i ≤
                (max u.hgt w.hgt) * K + RB base H + M := by
              rw [hAt_cons_ne (Nat.ne_of_gt hij), hAt_cons_ne (Nat.ne_of_gt hij), hAt_cons_self,
                hAt_cons_self]
              exact max_le (by omega) (max_le (by omega) (by omega))
            have hwC := RB_mono stepW hA
            simp only [recIter, Val.hgt]
            have hKw : RB stepW C ≤ K := by omega
            have : (max u.hgt w.hgt) * K + K = (max u.hgt w.hgt + 1) * K := by ring
            omega
      have hfin := key (reval ctr ρ) hc
      have hmul : (reval ctr ρ).hgt * K ≤ C * K := Nat.mul_le_mul_right _ hc
      have hQ : RB (.recur ctr base stepS stepW) H = C * K + RB base H := by
        simp only [RB]
        rw [hK, hCdef]
      rw [hQ]
      simp only [reval]
      omega

/-- The free recursor as a tiered recurrence over the variables `b, s, n` (de Bruijn `0, 1, 2`):
`rec n b (wrap s r) b`. Adapter: the case of a `wrap`-rooted counter, on which the free recursor
has no rule, returns the base. -/
def recursorR : REx := .recur (.var 2) (.var 0) (.wrap (.var 3) (.var 1)) (.var 4)

/-- On numerals the tiered recurrence computes the free recursor. -/
theorem reval_recursorR (b s : Val) (k : Nat) :
    reval recursorR [b, s, numeral k] = recurVal b s k := by
  show recIter b (fun _ r => .wrap s r) (fun _ _ _ _ => b) (numeral k) = recurVal b s k
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (Val.wrap s) ih

/-- Native data of `ramifiedRecursionTypingBarrier`: the tiers of the variables `b, s, n` of the
recursor and the tier of its result. -/
structure ramifiedRecursionTypingBarrierData where
  tier : RV → Nat
  out : Nat

/-- The tier context of the recursor's variables. -/
def rvTiers (M : ramifiedRecursionTypingBarrierData) : List Nat :=
  [M.tier .b, M.tier .s, M.tier .n]

/-- Leivant 1995 (ramified recurrence): the recurrence argument has a tier above the tier of the
result. -/
def ramifiedRecursionTypingBarrierLaws (M : ramifiedRecursionTypingBarrierData) : Prop :=
  M.out < M.tier .n

/-- The discipline accepts the recursor definition when its tier judgment is derivable. Adapter:
`recursorR`, the free recursor as a recurrence over its three variables. -/
def ramifiedRecursionTypingBarrierAccepts (M : ramifiedRecursionTypingBarrierData) : Prop :=
  RTy (rvTiers M) recursorR M.out

/-- Verdict: fragment escape. The ramified recurrence admits the free recursor with the payload at
the result tier, although the payload is duplicated; the yield is the polynomial height bound of
tiered soundness. (The row name records the landed barrier, which inserted a no-duplication clause
absent from the source; the true verdict is admission.) -/
def ramifiedRecursionTypingBarrierResult (M : ramifiedRecursionTypingBarrierData) : Prop :=
  ramifiedRecursionTypingBarrierAccepts M ∧
    ∃ p : Polynomial ℕ, ∀ b s n : Val,
      (reval recursorR [b, s, n]).hgt ≤
        p.eval (hAbove (rvTiers M) [b, s, n] M.out) + hAt (rvTiers M) [b, s, n] M.out

/-- Soundness: the tier derivation yields the polynomial height bound. -/
theorem ramifiedRecursionTypingBarrier_sound :
    ∀ M, ramifiedRecursionTypingBarrierLaws M → ramifiedRecursionTypingBarrierAccepts M →
      ramifiedRecursionTypingBarrierResult M := by
  intro M _ hA
  obtain ⟨p, hp⟩ := RB_polynomial recursorR
  refine ⟨hA, p, fun b s n => ?_⟩
  rw [← hp]
  exact RTy.hgt_bound hA [b, s, n]

/-- The tier judgment of the recursor, read off its rules. -/
theorem ramified_accepts_iff (M : ramifiedRecursionTypingBarrierData) :
    ramifiedRecursionTypingBarrierAccepts M ↔
      M.out < M.tier .n ∧ M.tier .b = M.out ∧ M.tier .s = M.out := by
  constructor
  · intro h
    cases h with
    | recur hij hctr hbase hstepS hstepW =>
        cases hctr with
        | var hk =>
            cases hbase with
            | var hb =>
                cases hstepS with
                | wrap h1 h2 =>
                    cases h1 with
                    | var hs =>
                        simp [rvTiers] at hk hb hs
                        exact ⟨hk ▸ hij, hb, hs⟩
  · rintro ⟨hn, hb, hs⟩
    refine RTy.recur hn (RTy.var (by simp [rvTiers])) (RTy.var (by simp [rvTiers, hb]))
      (RTy.wrap (RTy.var (by simp [rvTiers, hs])) (RTy.var (by simp)))
      (RTy.var (by simp [rvTiers, hb]))

/-- Witness: payload and base at tier `0`, counter at tier `1`, result at tier `0`. -/
def ramifiedRecursionTypingBarrierWitness : ramifiedRecursionTypingBarrierData where
  tier := fun x => match x with | .b => 0 | .s => 0 | .n => 1
  out := 0

theorem ramifiedRecursionTypingBarrierWitness_laws :
    ramifiedRecursionTypingBarrierLaws ramifiedRecursionTypingBarrierWitness := by
  show 0 < 1
  omega

theorem ramifiedRecursionTypingBarrierWitness_accepts :
    ramifiedRecursionTypingBarrierAccepts ramifiedRecursionTypingBarrierWitness :=
  (ramified_accepts_iff _).2 ⟨by decide, rfl, rfl⟩

theorem ramifiedRecursionTypingBarrierWitness_result :
    ramifiedRecursionTypingBarrierResult ramifiedRecursionTypingBarrierWitness :=
  ramifiedRecursionTypingBarrier_sound _ ramifiedRecursionTypingBarrierWitness_laws
    ramifiedRecursionTypingBarrierWitness_accepts

/-- Recursion on the output of a recursion: `rec n (succ zero) (rec r zero (succ (succ r')) zero)
zero`, the doubling recursion applied to the recursive result. -/
def expProg : REx :=
  .recur (.var 0) (.succ .zero) (.recur (.var 1) .zero (.succ (.succ (.var 1))) .zero) .zero

/-- The forbidden recursion has no tier judgment at any tiers: the inner recurrence would recur on a
result of its own tier. -/
theorem expProg_untypable : ∀ t i : Nat, ¬ RTy [t] expProg i := by
  intro t i h
  cases h with
  | recur _ _ _ hstepS _ =>
      cases hstepS with
      | recur hij' hctr' _ _ _ =>
          cases hctr' with
          | var hk =>
              simp at hk
              omega

/-- **Defining feature.** Lower-tier duplication is admitted (`wrap(x, x)` at the tier of `x`, and
the recursor, whose unfolding copies the payload `k` times); recursion on the output of a
recursion is rejected at every tier assignment. -/
theorem ramifiedRecursionTypingBarrierWitness_feature :
    RTy [0] (.wrap (.var 0) (.var 0)) 0 ∧
      (∀ b s k, reval recursorR [b, s, numeral k] = recurVal b s k) ∧
      recurVal .zero (.succ .zero) 2 = .wrap (.succ .zero) (.wrap (.succ .zero) .zero) ∧
      (∀ t i : Nat, ¬ RTy [t] expProg i) :=
  ⟨RTy.wrap (RTy.var rfl) (RTy.var rfl), reval_recursorR, rfl, expProg_untypable⟩

/-- **Mutation.** The counter at the result tier, everything else fixed: the ramification law and
the tier judgment both fail. -/
theorem ramifiedRecursionTypingBarrier_mutation :
    ¬ ramifiedRecursionTypingBarrierLaws
        { ramifiedRecursionTypingBarrierWitness with
          tier := fun x => match x with | .b => 0 | .s => 0 | .n => 0 } ∧
      ¬ ramifiedRecursionTypingBarrierAccepts
        { ramifiedRecursionTypingBarrierWitness with
          tier := fun x => match x with | .b => 0 | .s => 0 | .n => 0 } := by
  refine ⟨fun h => Nat.lt_irrefl 0 h, fun h => ?_⟩
  exact Nat.lt_irrefl 0 ((ramified_accepts_iff _).1 h).1

/-- The doubling tree `rec n zero (wrap r r) zero`, admitted with the counter at tier `1`. -/
def dupTreeProg : REx := .recur (.var 0) .zero (.wrap (.var 1) (.var 1)) .zero

theorem dupTreeProg_typed : RTy [1] dupTreeProg 0 :=
  RTy.recur (by decide) (RTy.var rfl) RTy.zero (RTy.wrap (RTy.var rfl) (RTy.var rfl)) RTy.zero

theorem dupTreeProg_size : ∀ k, 2 ^ k ≤ (reval dupTreeProg [numeral k]).size := by
  have h : ∀ k, reval dupTreeProg [numeral k] =
      recIter .zero (fun _ r => .wrap r r) (fun _ _ _ _ => .zero) (numeral k) := fun _ => rfl
  intro k
  rw [h]
  induction k with
  | zero => simp [numeral, recIter, Val.size]
  | succ k ih =>
      simp only [numeral, recIter, Val.size]
      rw [pow_succ]
      omega

/-- **Scope of the fragment.** The fragment proves the height form of tiered soundness. Omitted from
the source: Leivant's poly-time theorem (register-machine simulation, the two-tier normal form) and
the time bound for general free algebras, which needs a shared representation (Dal Lago, Martini
and Zorzi 2010); flat recurrence and the word algebra with two successors. The theorem below
records why the omitted time bound is not a tree-size bound: an admitted definition has tree size
exponential in its counter while its height is linear. -/
theorem ramifiedRecursionTypingBarrier_scope :
    RTy [1] dupTreeProg 0 ∧ ∀ k, 2 ^ k ≤ (reval dupTreeProg [numeral k]).size :=
  ⟨dupTreeProg_typed, dupTreeProg_size⟩

/-! ## Row `bellantoniCookSplit`

Bellantoni and Cook, *A new recursion-theoretic characterization of the polytime functions*,
Computational Complexity 2 (1992) 97-110, Section 2: inputs are normal or safe, written
`f(x; a)`; the class `B` is closed under predicative recursion on notation (vi),
`f(0, x; a) = g(x; a)`, `f(yi, x; a) = h_i(y, x; a, f(y, x; a))`, whose recursive value sits in a
safe position, and safe composition (vii), `f(x; a) = h(r(x;); t(x; a))`, whose normal arguments
use no safe input. Lemma 4.1: `|f(x; a)| ≤ q_f(|x|) + max_i |a_i|` for a monotone polynomial
`q_f`. The fragment works over the free algebra `{zero, succ, wrap}` with unary notation for the
counter: `succ(; a)` is the successor, `wrap(x; a)` is the free binary constructor with its first
argument normal (the base bound `|f| ≤ 1 + Σ|x| + max|a|` of the proof of Lemma 4.1 forbids a
second safe argument), and the recurrence has one case per constructor. -/

/-- Expressions of the fragment: normal and safe variables (de Bruijn, in separate lists), the
initial functions, and predicative recursion. `stepS` sees the predecessor in front of the normal
list and the recursive value in front of the safe list; `stepW` sees `u, w` and `ru, rw`. -/
inductive BEx where
  | nvar (k : Nat)
  | svar (k : Nat)
  | zero
  | succ (e : BEx)
  | wrap (e₁ e₂ : BEx)
  | recur (ctr base stepS stepW : BEx)
  deriving DecidableEq, Repr

/-- Evaluation: `beval e ν σ` with normal inputs `ν` and safe inputs `σ`. -/
def beval : BEx → List Val → List Val → Val
  | .nvar k, ν, _ => ν.getD k .zero
  | .svar k, _, σ => σ.getD k .zero
  | .zero, _, _ => .zero
  | .succ e, ν, σ => .succ (beval e ν σ)
  | .wrap e₁ e₂, ν, σ => .wrap (beval e₁ ν σ) (beval e₂ ν σ)
  | .recur ctr base stepS stepW, ν, σ =>
      recIter (beval base ν σ) (fun c r => beval stepS (c :: ν) (r :: σ))
        (fun u w ru rw => beval stepW (u :: w :: ν) (ru :: rw :: σ)) (beval ctr ν σ)

/-- No safe variable of the enclosing context occurs (safe variables below depth `d` are the ones
bound by recursion inside the expression). -/
def nsf : Nat → BEx → Prop
  | _, .nvar _ => True
  | d, .svar k => k < d
  | _, .zero => True
  | d, .succ e => nsf d e
  | d, .wrap e₁ e₂ => nsf d e₁ ∧ nsf d e₂
  | d, .recur ctr base stepS stepW => nsf d ctr ∧ nsf d base ∧ nsf (d + 1) stepS ∧ nsf (d + 2) stepW

/-- The admissibility check of the class `B`: every normal position (the first argument of `wrap`
and the recurrence argument) is filled by an expression with no safe input (safe composition,
vii; recursion on a normal input, vi). -/
def BSafe : BEx → Prop
  | .nvar _ => True
  | .svar _ => True
  | .zero => True
  | .succ e => BSafe e
  | .wrap e₁ e₂ => nsf 0 e₁ ∧ BSafe e₁ ∧ BSafe e₂
  | .recur ctr base stepS stepW => nsf 0 ctr ∧ BSafe ctr ∧ BSafe base ∧ BSafe stepS ∧ BSafe stepW

/-- An expression reads only its safe variables below depth `d`. -/
theorem beval_safe_indep : ∀ (e : BEx) (d : Nat) (ν σ σ' : List Val), nsf d e →
    (∀ k, k < d → σ.getD k .zero = σ'.getD k .zero) → beval e ν σ = beval e ν σ'
  | .nvar _, _, _, _, _, _, _ => rfl
  | .svar k, _, _, _, _, h, hag => hag k h
  | .zero, _, _, _, _, _, _ => rfl
  | .succ e, d, ν, σ, σ', h, hag => by
      simp only [beval]
      rw [beval_safe_indep e d ν σ σ' h hag]
  | .wrap e₁ e₂, d, ν, σ, σ', h, hag => by
      simp only [beval]
      rw [beval_safe_indep e₁ d ν σ σ' h.1 hag, beval_safe_indep e₂ d ν σ σ' h.2 hag]
  | .recur ctr base stepS stepW, d, ν, σ, σ', h, hag => by
      obtain ⟨hc, hb, hs, hw⟩ := h
      have hfs : (fun c r => beval stepS (c :: ν) (r :: σ)) =
          (fun c r => beval stepS (c :: ν) (r :: σ')) := by
        funext c r
        refine beval_safe_indep stepS (d + 1) (c :: ν) (r :: σ) (r :: σ') hs ?_
        intro k hk
        cases k with
        | zero => rfl
        | succ k => exact hag k (by omega)
      have hfw : (fun u w ru rw => beval stepW (u :: w :: ν) (ru :: rw :: σ)) =
          (fun u w ru rw => beval stepW (u :: w :: ν) (ru :: rw :: σ')) := by
        funext u w ru rw
        refine beval_safe_indep stepW (d + 2) (u :: w :: ν) (ru :: rw :: σ) (ru :: rw :: σ') hw ?_
        intro k hk
        rcases k with _ | _ | k
        · rfl
        · rfl
        · exact hag k (by omega)
      simp only [beval]
      rw [beval_safe_indep ctr d ν σ σ' hc hag, beval_safe_indep base d ν σ σ' hb hag, hfs, hfw]

theorem beval_nsf_zero {e : BEx} (h : nsf 0 e) (ν σ : List Val) : beval e ν σ = beval e ν [] :=
  beval_safe_indep e 0 ν σ [] h (fun k hk => absurd hk (Nat.not_lt_zero k))

/-- Largest size in a list of inputs (at least `1`, the size of the default `zero`). -/
def mxs : List Val → Nat
  | [] => 1
  | v :: σ => max v.size (mxs σ)

theorem one_le_mxs : ∀ σ : List Val, 1 ≤ mxs σ
  | [] => le_rfl
  | v :: σ => by
      have := one_le_mxs σ
      simp only [mxs]
      omega

theorem size_getD_le_mxs : ∀ (σ : List Val) (k : Nat), (σ.getD k .zero).size ≤ mxs σ
  | [], k => by simp [mxs, Val.size]
  | v :: σ, 0 => by simp [mxs]
  | v :: σ, k + 1 => by
      have := size_getD_le_mxs σ k
      simp only [List.getD_cons_succ, mxs]
      omega

/-- The normal budget of an expression: a polynomial in the largest normal input. -/
def QB : BEx → Nat → Nat
  | .nvar _, N => N
  | .svar _, _ => 0
  | .zero, _ => 0
  | .succ e, N => QB e N + 1
  | .wrap e₁ e₂, N => QB e₁ N + QB e₂ N + 2
  | .recur ctr base stepS stepW, N =>
      (QB ctr N + 1) * (QB stepS (QB ctr N + 1 + N) + QB stepW (QB ctr N + 1 + N) + 1) + QB base N

theorem QB_mono : ∀ (e : BEx) {N N' : Nat}, N ≤ N' → QB e N ≤ QB e N'
  | .nvar _, _, _, h => h
  | .svar _, _, _, _ => le_rfl
  | .zero, _, _, _ => le_rfl
  | .succ e, _, _, h => by simp only [QB]; have := QB_mono e h; omega
  | .wrap e₁ e₂, _, _, h => by
      simp only [QB]; have := QB_mono e₁ h; have := QB_mono e₂ h; omega
  | .recur ctr base stepS stepW, N, N', h => by
      simp only [QB]
      have hc := QB_mono ctr h
      have hb := QB_mono base h
      have hC : QB ctr N + 1 + N ≤ QB ctr N' + 1 + N' := by omega
      have hs := QB_mono stepS hC
      have hw := QB_mono stepW hC
      exact Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) hb

theorem QB_polynomial : ∀ e : BEx, ∃ p : Polynomial ℕ, ∀ N, QB e N = p.eval N
  | .nvar _ => ⟨Polynomial.X, fun _ => by simp [QB]⟩
  | .svar _ => ⟨0, fun _ => by simp [QB]⟩
  | .zero => ⟨0, fun _ => by simp [QB]⟩
  | .succ e => by
      obtain ⟨p, hp⟩ := QB_polynomial e
      exact ⟨p + 1, fun N => by simp [QB, hp]⟩
  | .wrap e₁ e₂ => by
      obtain ⟨p₁, h₁⟩ := QB_polynomial e₁
      obtain ⟨p₂, h₂⟩ := QB_polynomial e₂
      exact ⟨p₁ + p₂ + 2, fun N => by simp [QB, h₁, h₂]⟩
  | .recur ctr base stepS stepW => by
      obtain ⟨pc, hc⟩ := QB_polynomial ctr
      obtain ⟨pb, hb⟩ := QB_polynomial base
      obtain ⟨ps, hs⟩ := QB_polynomial stepS
      obtain ⟨pw, hw⟩ := QB_polynomial stepW
      refine ⟨(pc + 1) * (ps.comp (pc + 1 + Polynomial.X) + pw.comp (pc + 1 + Polynomial.X) + 1)
        + pb, fun N => ?_⟩
      simp [QB, hc, hb, hs, hw, Polynomial.eval_comp]

/-- **Lemma 4.1 for the fragment.** For every admissible expression, the output size is at most a
polynomial in the largest normal input plus the largest safe input. -/
theorem bsafe_size_bound : ∀ (e : BEx), BSafe e → ∀ ν σ : List Val,
    (beval e ν σ).size ≤ QB e (mxs ν) + mxs σ
  | .nvar k, _, ν, σ => by
      have := size_getD_le_mxs ν k
      simp only [beval, QB]
      omega
  | .svar k, _, ν, σ => by
      have := size_getD_le_mxs σ k
      simp only [beval, QB]
      omega
  | .zero, _, _, σ => by
      have := one_le_mxs σ
      simp only [beval, QB, Val.size]
      omega
  | .succ e, h, ν, σ => by
      have := bsafe_size_bound e h ν σ
      simp only [beval, QB, Val.size]
      omega
  | .wrap e₁ e₂, h, ν, σ => by
      obtain ⟨h0, h1, h2⟩ := h
      have hb1 := bsafe_size_bound e₁ h1 ν []
      have hb2 := bsafe_size_bound e₂ h2 ν σ
      rw [← beval_nsf_zero h0 ν σ] at hb1
      simp only [mxs] at hb1
      simp only [beval, QB, Val.size]
      omega
  | .recur ctr base stepS stepW, h, ν, σ => by
      obtain ⟨h0, hc, hb, hs, hw⟩ := h
      set N := mxs ν with hN
      set C0 := QB ctr N + 1 with hC0
      set C := C0 + N with hC
      set K := QB stepS C + QB stepW C + 1 with hK
      have hctr : (beval ctr ν σ).size ≤ C0 := by
        have h1 : (beval ctr ν []).size ≤ QB ctr N + mxs [] := bsafe_size_bound ctr hc ν []
        rw [← beval_nsf_zero h0 ν σ] at h1
        simp only [mxs] at h1
        omega
      have key : ∀ c : Val, c.size ≤ C0 →
          (recIter (beval base ν σ) (fun c r => beval stepS (c :: ν) (r :: σ))
            (fun u w ru rw => beval stepW (u :: w :: ν) (ru :: rw :: σ)) c).size ≤
            c.size * K + QB base N + mxs σ := by
        intro c
        induction c with
        | zero =>
            intro _
            have hb0 : (beval base ν σ).size ≤ QB base N + mxs σ := bsafe_size_bound base hb ν σ
            simp only [recIter]
            have : 0 ≤ Val.zero.size * K := Nat.zero_le _
            omega
        | succ c ihc =>
            intro hcC
            simp only [Val.size] at hcC
            have hr := ihc (by omega)
            have hstep := bsafe_size_bound stepS hs (c :: ν)
              (recIter (beval base ν σ) (fun c r => beval stepS (c :: ν) (r :: σ))
                (fun u w ru rw => beval stepW (u :: w :: ν) (ru :: rw :: σ)) c :: σ)
            have hN' : mxs (c :: ν) ≤ C := by
              show max c.size (mxs ν) ≤ C
              exact max_le (by omega) (by omega)
            have hq := QB_mono stepS hN'
            have hS' : mxs (recIter (beval base ν σ) (fun c r => beval stepS (c :: ν) (r :: σ))
                (fun u w ru rw => beval stepW (u :: w :: ν) (ru :: rw :: σ)) c :: σ) ≤
                c.size * K + QB base N + mxs σ := by
              show max _ (mxs σ) ≤ _
              exact max_le hr (by omega)
            simp only [recIter, Val.size]
            have : (c.size + 1) * K = c.size * K + K := by ring
            omega
        | wrap u w ihu ihw =>
            intro hcC
            simp only [Val.size] at hcC
            have hru := ihu (by omega)
            have hrw := ihw (by omega)
            have hstep := bsafe_size_bound stepW hw (u :: w :: ν)
              (recIter (beval base ν σ) (fun c r => beval stepS (c :: ν) (r :: σ))
                (fun u w ru rw => beval stepW (u :: w :: ν) (ru :: rw :: σ)) u ::
               recIter (beval base ν σ) (fun c r => beval stepS (c :: ν) (r :: σ))
                (fun u w ru rw => beval stepW (u :: w :: ν) (ru :: rw :: σ)) w :: σ)
            have hN' : mxs (u :: w :: ν) ≤ C := by
              show max u.size (max w.size (mxs ν)) ≤ C
              exact max_le (by omega) (max_le (by omega) (by omega))
            have hq := QB_mono stepW hN'
            have e1 : u.size * K ≤ (u.size + w.size) * K := Nat.mul_le_mul_right _ (by omega)
            have e2 : w.size * K ≤ (u.size + w.size) * K := Nat.mul_le_mul_right _ (by omega)
            have hS' : mxs (recIter (beval base ν σ) (fun c r => beval stepS (c :: ν) (r :: σ))
                  (fun u w ru rw => beval stepW (u :: w :: ν) (ru :: rw :: σ)) u ::
                recIter (beval base ν σ) (fun c r => beval stepS (c :: ν) (r :: σ))
                  (fun u w ru rw => beval stepW (u :: w :: ν) (ru :: rw :: σ)) w :: σ) ≤
                (u.size + w.size) * K + QB base N + mxs σ := by
              show max _ (max _ (mxs σ)) ≤ _
              exact max_le (by omega) (max_le (by omega) (by omega))
            simp only [recIter, Val.size]
            have : (u.size + w.size + 1) * K = (u.size + w.size) * K + K := by ring
            omega
      have hfin := key (beval ctr ν σ) hctr
      have hmul : (beval ctr ν σ).size * K ≤ C0 * K := Nat.mul_le_mul_right _ hctr
      have hQ : QB (.recur ctr base stepS stepW) N = C0 * K + QB base N := by
        simp only [QB]
        rw [hK, hC, hC0]
      rw [hQ]
      simp only [beval]
      omega

/-- Normal or safe input position. -/
inductive Pos where
  | normal
  | safe
  deriving DecidableEq, Repr

/-- Native data of `bellantoniCookSplit`: the normal/safe classification of the recursor's inputs
`b, s, n`. -/
structure bellantoniCookSplitData where
  pos : RV → Pos

/-- `1` for a normal input, `0` for a safe one. -/
def isN (M : bellantoniCookSplitData) (x : RV) : Nat := if M.pos x = .normal then 1 else 0

/-- Position of an input in the normal list (inputs in the order `b, s, n`). -/
def idxN (M : bellantoniCookSplitData) : RV → Nat
  | .b => 0
  | .s => isN M .b
  | .n => isN M .b + isN M .s

/-- Position of an input in the safe list. -/
def idxS (M : bellantoniCookSplitData) : RV → Nat
  | .b => 0
  | .s => 1 - isN M .b
  | .n => (1 - isN M .b) + (1 - isN M .s)

/-- Reference to an input under `k` enclosing binders of each list. -/
def bref (M : bellantoniCookSplitData) (x : RV) (k : Nat) : BEx :=
  if M.pos x = .normal then .nvar (k + idxN M x) else .svar (k + idxS M x)

/-- The free recursor as a definition by predicative recursion on `n`: base `b`, step
`wrap(s; r)`. Adapter: a `wrap`-rooted counter returns the base. -/
def recursorB (M : bellantoniCookSplitData) : BEx :=
  .recur (bref M .n 0) (bref M .b 0) (.wrap (bref M .s 1) (.svar 0)) (bref M .b 2)

/-- The normal inputs, in the order `b, s, n`. -/
def nlist (M : bellantoniCookSplitData) (b s n : Val) : List Val :=
  (if M.pos .b = .normal then [b] else []) ++ (if M.pos .s = .normal then [s] else []) ++
    (if M.pos .n = .normal then [n] else [])

/-- The safe inputs, in the order `b, s, n`. -/
def slist (M : bellantoniCookSplitData) (b s n : Val) : List Val :=
  (if M.pos .b = .normal then [] else [b]) ++ (if M.pos .s = .normal then [] else [s]) ++
    (if M.pos .n = .normal then [] else [n])

theorem nsf_bref (M : bellantoniCookSplitData) (x : RV) (k : Nat) :
    nsf 0 (bref M x k) ↔ M.pos x = .normal := by
  unfold bref
  split_ifs with h
  · simp [nsf, h]
  · simp [nsf, h]

theorem BSafe_bref (M : bellantoniCookSplitData) (x : RV) (k : Nat) : BSafe (bref M x k) := by
  unfold bref
  split_ifs <;> trivial

/-- Bellantoni and Cook 1992, scheme vi: predicative recursion recurs on a normal input. -/
def bellantoniCookSplitLaws (M : bellantoniCookSplitData) : Prop :=
  M.pos .n = .normal

/-- The class `B` admits the recursor definition: `recursorB M` passes the safe-composition
check. Adapter: `recursorB`, the free recursor as a predicative recursion under the split `M`. -/
def bellantoniCookSplitAccepts (M : bellantoniCookSplitData) : Prop :=
  BSafe (recursorB M)

/-- Verdict: fragment escape. The class `B` admits the free recursor with the counter and the
payload normal and the base safe: the payload is duplicated as a normal parameter and the recursive
value stays in the safe position of `wrap`. The yield is the bound of Lemma 4.1. (The landed row
claimed a barrier; the true verdict is admission.) -/
def bellantoniCookSplitResult (M : bellantoniCookSplitData) : Prop :=
  bellantoniCookSplitAccepts M ∧
    ∃ p : Polynomial ℕ, ∀ b s n : Val,
      (beval (recursorB M) (nlist M b s n) (slist M b s n)).size ≤
        p.eval (mxs (nlist M b s n)) + mxs (slist M b s n)

/-- Soundness: the admissibility check yields the bound of Lemma 4.1. -/
theorem bellantoniCookSplit_sound :
    ∀ M, bellantoniCookSplitLaws M → bellantoniCookSplitAccepts M → bellantoniCookSplitResult M := by
  intro M _ hA
  obtain ⟨p, hp⟩ := QB_polynomial (recursorB M)
  refine ⟨hA, p, fun b s n => ?_⟩
  rw [← hp]
  exact bsafe_size_bound (recursorB M) hA _ _

/-- The check, read off the rules: the counter and the payload are normal. -/
theorem bellantoniCook_accepts_iff (M : bellantoniCookSplitData) :
    bellantoniCookSplitAccepts M ↔ M.pos .n = .normal ∧ M.pos .s = .normal := by
  simp only [bellantoniCookSplitAccepts, recursorB, BSafe, nsf_bref, BSafe_bref, and_true,
    true_and]

/-- Witness: counter and payload normal, base safe. -/
def bellantoniCookSplitWitness : bellantoniCookSplitData where
  pos := fun x => match x with | .b => .safe | .s => .normal | .n => .normal

theorem bellantoniCookSplitWitness_laws : bellantoniCookSplitLaws bellantoniCookSplitWitness := rfl

theorem bellantoniCookSplitWitness_accepts :
    bellantoniCookSplitAccepts bellantoniCookSplitWitness :=
  (bellantoniCook_accepts_iff _).2 ⟨rfl, rfl⟩

theorem bellantoniCookSplitWitness_result :
    bellantoniCookSplitResult bellantoniCookSplitWitness :=
  bellantoniCookSplit_sound _ bellantoniCookSplitWitness_laws bellantoniCookSplitWitness_accepts

theorem recursorB_witness :
    recursorB bellantoniCookSplitWitness =
      .recur (.nvar 1) (.svar 0) (.wrap (.nvar 1) (.svar 0)) (.svar 2) := by
  decide

/-- On numerals the admitted definition computes the free recursor. -/
theorem beval_recursorB_witness (b s : Val) (k : Nat) :
    beval (recursorB bellantoniCookSplitWitness)
        (nlist bellantoniCookSplitWitness b s (numeral k))
        (slist bellantoniCookSplitWitness b s (numeral k)) = recurVal b s k := by
  rw [recursorB_witness]
  show recIter b (fun _ r => .wrap s r) (fun _ _ _ _ => b) (numeral k) = recurVal b s k
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (Val.wrap s) ih

/-- **Defining feature.** The recursive value is placed in the safe position of `wrap` and the
payload in its normal position; the payload, a normal parameter, is duplicated by the recursion
(two copies at counter `2`): safe and normal positions do not exclude duplication. -/
theorem bellantoniCookSplitWitness_feature :
    recursorB bellantoniCookSplitWitness =
        .recur (.nvar 1) (.svar 0) (.wrap (.nvar 1) (.svar 0)) (.svar 2) ∧
      (∀ b s k, beval (recursorB bellantoniCookSplitWitness)
          (nlist bellantoniCookSplitWitness b s (numeral k))
          (slist bellantoniCookSplitWitness b s (numeral k)) = recurVal b s k) ∧
      recurVal .zero (.succ .zero) 2 = .wrap (.succ .zero) (.wrap (.succ .zero) .zero) :=
  ⟨recursorB_witness, beval_recursorB_witness, rfl⟩

theorem size_numeral : ∀ k, (numeral k).size = k + 1
  | 0 => rfl
  | k + 1 => by simp [numeral, Val.size, size_numeral k]

/-- The split with a safe payload. -/
def safePayloadSplit : bellantoniCookSplitData :=
  { bellantoniCookSplitWitness with
    pos := fun x => match x with | .b => .safe | .s => .safe | .n => .normal }

/-- **Mutation.** Making the payload safe, everything else fixed, fails the check; the function
the unchecked definition computes violates the bound of Lemma 4.1 for every bounding function, so
the rejection is forced by the source. -/
theorem bellantoniCookSplit_mutation :
    ¬ bellantoniCookSplitAccepts safePayloadSplit ∧
      ¬ ∃ q : Nat → Nat, ∀ b s n : Val,
        (beval (recursorB safePayloadSplit) (nlist safePayloadSplit b s n)
            (slist safePayloadSplit b s n)).size ≤
          q (mxs (nlist safePayloadSplit b s n)) + mxs (slist safePayloadSplit b s n) := by
  refine ⟨fun h => ?_, fun ⟨q, hq⟩ => ?_⟩
  · have := ((bellantoniCook_accepts_iff _).1 h).2
    cases this
  · have h := hq .zero (numeral (q 3 + 3)) (numeral 2)
    have hev : beval (recursorB safePayloadSplit) (nlist safePayloadSplit .zero
        (numeral (q 3 + 3)) (numeral 2)) (slist safePayloadSplit .zero (numeral (q 3 + 3))
          (numeral 2)) = .wrap (numeral (q 3 + 3)) (.wrap (numeral (q 3 + 3)) .zero) := rfl
    have hn : nlist safePayloadSplit .zero (numeral (q 3 + 3)) (numeral 2) = [numeral 2] := rfl
    have hs : slist safePayloadSplit .zero (numeral (q 3 + 3)) (numeral 2) =
        [.zero, numeral (q 3 + 3)] := rfl
    have hs1 : (numeral (q 3 + 3)).size = q 3 + 4 := size_numeral _
    have hm1 : mxs [Val.zero, numeral (q 3 + 3)] = q 3 + 4 := by
      simp only [mxs, hs1, Val.size]
      rw [Nat.max_eq_left (by omega : 1 ≤ q 3 + 4), Nat.max_eq_right (by omega : 1 ≤ q 3 + 4)]
    have hm2 : mxs [numeral 2] = 3 := rfl
    rw [hev, hn, hs, hm2, hm1] at h
    simp only [Val.size, hs1] at h
    omega

/-- **Scope of the fragment.** Omitted from Bellantoni and Cook 1992: binary notation (the two
successors), the predecessor and conditional initial functions, Theorem 3.3 (every polytime
function is in `B`) and Theorem 4.2 (every function of `B` is polytime). The counter of the
fragment is unary, so the bound is polynomial in the size of the unary numeral; the theorem below
gives the exact output size of the admitted recursor. -/
theorem bellantoniCookSplit_scope (b s : Val) : ∀ k, (recurVal b s k).size = b.size + k * (s.size + 1)
  | 0 => by simp [recurVal]
  | k + 1 => by
      simp only [recurVal, Val.size, bellantoniCookSplit_scope b s k]
      ring

/-! ## Row `coqGuardAdmittance`

Giménez, *Codifying guarded definitions with recursive schemes*, in Types for Proofs and Programs
(TYPES '94), LNCS 996, Springer 1995, 39-59. The clauses implemented are the guard condition as the
Rocq reference manual restates it from that paper (section "Fixpoint definitions"): a fixpoint
declares the index `k` of its decreasing parameter, which has an inductive type; every recursive
call must give, as its `k`-th argument, a term structurally smaller than that parameter; the
variables bound by a case analysis on the parameter, or on a variable already smaller, at the
recursive arguments of the constructor are structurally smaller. The fragment has one inductive
type, the free algebra `{zero, succ, wrap}` (both `succ` and `wrap` have only recursive
arguments), fixpoints of three parameters named `0, 1, 2`, named variables, exhaustive case
analysis on a variable, and call-by-value evaluation. -/

/-- Bodies of fixpoint definitions. `caseOf x ez p es q r ew` matches the variable `x`:
`zero ⇒ ez | succ p ⇒ es | wrap q r ⇒ ew`. -/
inductive GExp where
  | var (x : Nat)
  | zero
  | succ (e : GExp)
  | wrap (e₁ e₂ : GExp)
  | call (e₀ e₁ e₂ : GExp)
  | caseOf (x : Nat) (ez : GExp) (p : Nat) (es : GExp) (q r : Nat) (ew : GExp)
  deriving DecidableEq, Repr

/-- A fixpoint definition: the index of its decreasing parameter and its body. -/
structure GFix where
  dec : Nat
  body : GExp

/-- Environment update. -/
def upd (ρ : Nat → Val) (x : Nat) (v : Val) : Nat → Val := fun z => if z = x then v else ρ z

theorem upd_same (ρ : Nat → Val) (x : Nat) (v : Val) : upd ρ x v x = v := by
  simp [upd]

theorem upd_other (ρ : Nat → Val) {x z : Nat} (v : Val) (h : z ≠ x) : upd ρ x v z = ρ z := by
  simp [upd, h]

/-- The parameters `0, 1, 2` bound to the arguments of a call. -/
def params (a₀ a₁ a₂ : Val) : Nat → Val :=
  fun z => if z = 0 then a₀ else if z = 1 then a₁ else if z = 2 then a₂ else .zero

/-- The argument at a parameter index. -/
def argAt : Nat → GExp → GExp → GExp → GExp
  | 0, e₀, _, _ => e₀
  | 1, _, e₁, _ => e₁
  | _ + 2, _, _, e₂ => e₂

/-- The value at a parameter index. -/
def valAt : Nat → Val → Val → Val → Val
  | 0, a₀, _, _ => a₀
  | 1, _, a₁, _ => a₁
  | _ + 2, _, _, a₂ => a₂

theorem params_dec (a₀ a₁ a₂ : Val) : ∀ d, d < 3 → params a₀ a₁ a₂ d = valAt d a₀ a₁ a₂
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | _ + 3, h => absurd h (by omega)

/-- Call-by-value evaluation of a fixpoint body in an environment. -/
inductive GEval (F : GFix) : (Nat → Val) → GExp → Val → Prop where
  | var (ρ : Nat → Val) (x : Nat) : GEval F ρ (.var x) (ρ x)
  | zero (ρ : Nat → Val) : GEval F ρ .zero .zero
  | succ {ρ : Nat → Val} {e : GExp} {v : Val} : GEval F ρ e v → GEval F ρ (.succ e) (.succ v)
  | wrap {ρ : Nat → Val} {e₁ e₂ : GExp} {v₁ v₂ : Val} :
      GEval F ρ e₁ v₁ → GEval F ρ e₂ v₂ → GEval F ρ (.wrap e₁ e₂) (.wrap v₁ v₂)
  | call {ρ : Nat → Val} {e₀ e₁ e₂ : GExp} {a₀ a₁ a₂ v : Val} :
      GEval F ρ e₀ a₀ → GEval F ρ e₁ a₁ → GEval F ρ e₂ a₂ →
        GEval F (params a₀ a₁ a₂) F.body v → GEval F ρ (.call e₀ e₁ e₂) v
  | caseZ {ρ : Nat → Val} {x : Nat} {ez : GExp} {p : Nat} {es : GExp} {q r : Nat} {ew : GExp}
      {v : Val} : ρ x = .zero → GEval F ρ ez v → GEval F ρ (.caseOf x ez p es q r ew) v
  | caseS {ρ : Nat → Val} {x : Nat} {ez : GExp} {p : Nat} {es : GExp} {q r : Nat} {ew : GExp}
      {u v : Val} : ρ x = .succ u → GEval F (upd ρ p u) es v →
        GEval F ρ (.caseOf x ez p es q r ew) v
  | caseW {ρ : Nat → Val} {x : Nat} {ez : GExp} {p : Nat} {es : GExp} {q r : Nat} {ew : GExp}
      {u w v : Val} : ρ x = .wrap u w → GEval F (upd (upd ρ q u) r w) ew v →
        GEval F ρ (.caseOf x ez p es q r ew) v

theorem GEval_var_inv {F : GFix} {ρ : Nat → Val} {x : Nat} {v : Val}
    (h : GEval F ρ (.var x) v) : v = ρ x := by
  cases h
  rfl

theorem GEval.at_dec {F : GFix} {ρ : Nat → Val} {e₀ e₁ e₂ : GExp} {a₀ a₁ a₂ : Val}
    (h₀ : GEval F ρ e₀ a₀) (h₁ : GEval F ρ e₁ a₁) (h₂ : GEval F ρ e₂ a₂) :
    ∀ d, GEval F ρ (argAt d e₀ e₁ e₂) (valAt d a₀ a₁ a₂)
  | 0 => h₀
  | 1 => h₁
  | _ + 2 => h₂

/-- Add a name to a set of names. -/
def insP (p : Nat) (P : Nat → Prop) : Nat → Prop := fun z => z = p ∨ P z

/-- Remove a name from a set of names (a pattern variable shadows it). -/
def delP (p : Nat) (P : Nat → Prop) : Nat → Prop := fun z => z ≠ p ∧ P z

/-- The guard condition with decreasing parameter `d`. `L` holds the names bound to the decreasing
parameter or to a term structurally smaller than it, `S` the names bound to a strictly smaller term.
A call is guarded when its `d`-th argument is a name in `S`; a case analysis on a name in `L` puts its
pattern variables into `L` and `S`, any other case analysis removes them. -/
inductive Guarded (d : Nat) : (Nat → Prop) → (Nat → Prop) → GExp → Prop where
  | var (L S : Nat → Prop) (x : Nat) : Guarded d L S (.var x)
  | zero (L S : Nat → Prop) : Guarded d L S .zero
  | succ {L S : Nat → Prop} {e : GExp} : Guarded d L S e → Guarded d L S (.succ e)
  | wrap {L S : Nat → Prop} {e₁ e₂ : GExp} :
      Guarded d L S e₁ → Guarded d L S e₂ → Guarded d L S (.wrap e₁ e₂)
  | call {L S : Nat → Prop} {e₀ e₁ e₂ : GExp} (z : Nat) :
      Guarded d L S e₀ → Guarded d L S e₁ → Guarded d L S e₂ →
        argAt d e₀ e₁ e₂ = .var z → S z → Guarded d L S (.call e₀ e₁ e₂)
  | caseIn {L S : Nat → Prop} {x : Nat} {ez : GExp} {p : Nat} {es : GExp} {q r : Nat}
      {ew : GExp} : L x → Guarded d L S ez → Guarded d (insP p L) (insP p S) es →
        Guarded d (insP r (insP q L)) (insP r (insP q S)) ew →
          Guarded d L S (.caseOf x ez p es q r ew)
  | caseOut {L S : Nat → Prop} {x : Nat} {ez : GExp} {p : Nat} {es : GExp} {q r : Nat}
      {ew : GExp} : ¬ L x → Guarded d L S ez → Guarded d (delP p L) (delP p S) es →
        Guarded d (delP r (delP q L)) (delP r (delP q S)) ew →
          Guarded d L S (.caseOf x ez p es q r ew)

/-- The guard check of a fixpoint: only the decreasing parameter is in `L`, nothing is in `S`. -/
def GuardOK (F : GFix) : Prop := Guarded F.dec (fun z => z = F.dec) (fun _ => False) F.body

/-- Evaluation of a guarded body terminates whenever the recursive calls on strictly smaller
decreasing arguments do: the invariant is that names in `L` hold values no larger than the
decreasing argument `A` and names in `S` hold strictly smaller values. -/
theorem guarded_eval_total (F : GFix) (A : Val)
    (IH : ∀ b₀ b₁ b₂ : Val, (valAt F.dec b₀ b₁ b₂).size < A.size →
      ∃ v, GEval F (params b₀ b₁ b₂) F.body v)
    {L S : Nat → Prop} {e : GExp} (h : Guarded F.dec L S e) :
    ∀ ρ : Nat → Val, (∀ z, L z → (ρ z).size ≤ A.size) → (∀ z, S z → (ρ z).size < A.size) →
      ∃ v, GEval F ρ e v := by
  induction h with
  | var L S x => intro ρ _ _; exact ⟨ρ x, .var ρ x⟩
  | zero L S => intro ρ _ _; exact ⟨.zero, .zero ρ⟩
  | succ _ ih =>
      intro ρ hL hS
      obtain ⟨v, hv⟩ := ih ρ hL hS
      exact ⟨.succ v, .succ hv⟩
  | wrap _ _ ih₁ ih₂ =>
      intro ρ hL hS
      obtain ⟨v₁, h₁⟩ := ih₁ ρ hL hS
      obtain ⟨v₂, h₂⟩ := ih₂ ρ hL hS
      exact ⟨.wrap v₁ v₂, .wrap h₁ h₂⟩
  | call z _ _ _ hz hSz ih₀ ih₁ ih₂ =>
      intro ρ hL hS
      obtain ⟨a₀, h₀⟩ := ih₀ ρ hL hS
      obtain ⟨a₁, h₁⟩ := ih₁ ρ hL hS
      obtain ⟨a₂, h₂⟩ := ih₂ ρ hL hS
      have hd := GEval.at_dec h₀ h₁ h₂ F.dec
      rw [hz] at hd
      have hv := GEval_var_inv hd
      obtain ⟨v, hb⟩ := IH a₀ a₁ a₂ (by rw [hv]; exact hS z hSz)
      exact ⟨v, .call h₀ h₁ h₂ hb⟩
  | @caseIn L S x ez p es q r ew hLx _ _ _ ihz ihs ihw =>
      intro ρ hL hS
      cases hρ : ρ x with
      | zero =>
          obtain ⟨v, hv⟩ := ihz ρ hL hS
          exact ⟨v, .caseZ hρ hv⟩
      | succ u =>
          have hx := hL x hLx
          rw [hρ] at hx
          simp only [Val.size] at hx
          have hL' : ∀ z, insP p L z → (upd ρ p u z).size ≤ A.size := by
            intro z hz
            by_cases hzp : z = p
            · subst hzp
              rw [upd_same]
              omega
            · rw [upd_other ρ u hzp]
              rcases hz with hz | hz
              · exact absurd hz hzp
              · exact hL z hz
          have hS' : ∀ z, insP p S z → (upd ρ p u z).size < A.size := by
            intro z hz
            by_cases hzp : z = p
            · subst hzp
              rw [upd_same]
              omega
            · rw [upd_other ρ u hzp]
              rcases hz with hz | hz
              · exact absurd hz hzp
              · exact hS z hz
          obtain ⟨v, hv⟩ := ihs (upd ρ p u) hL' hS'
          exact ⟨v, .caseS hρ hv⟩
      | wrap u w =>
          have hx := hL x hLx
          rw [hρ] at hx
          simp only [Val.size] at hx
          have hL' : ∀ z, insP r (insP q L) z → (upd (upd ρ q u) r w z).size ≤ A.size := by
            intro z hz
            by_cases hzr : z = r
            · subst hzr
              rw [upd_same]
              omega
            · rw [upd_other _ w hzr]
              by_cases hzq : z = q
              · subst hzq
                rw [upd_same]
                omega
              · rw [upd_other ρ u hzq]
                rcases hz with hz | hz | hz
                · exact absurd hz hzr
                · exact absurd hz hzq
                · exact hL z hz
          have hS' : ∀ z, insP r (insP q S) z → (upd (upd ρ q u) r w z).size < A.size := by
            intro z hz
            by_cases hzr : z = r
            · subst hzr
              rw [upd_same]
              omega
            · rw [upd_other _ w hzr]
              by_cases hzq : z = q
              · subst hzq
                rw [upd_same]
                omega
              · rw [upd_other ρ u hzq]
                rcases hz with hz | hz | hz
                · exact absurd hz hzr
                · exact absurd hz hzq
                · exact hS z hz
          obtain ⟨v, hv⟩ := ihw (upd (upd ρ q u) r w) hL' hS'
          exact ⟨v, .caseW hρ hv⟩
  | @caseOut L S x ez p es q r ew _ _ _ _ ihz ihs ihw =>
      intro ρ hL hS
      cases hρ : ρ x with
      | zero =>
          obtain ⟨v, hv⟩ := ihz ρ hL hS
          exact ⟨v, .caseZ hρ hv⟩
      | succ u =>
          have hL' : ∀ z, delP p L z → (upd ρ p u z).size ≤ A.size := fun z hz => by
            rw [upd_other ρ u hz.1]
            exact hL z hz.2
          have hS' : ∀ z, delP p S z → (upd ρ p u z).size < A.size := fun z hz => by
            rw [upd_other ρ u hz.1]
            exact hS z hz.2
          obtain ⟨v, hv⟩ := ihs (upd ρ p u) hL' hS'
          exact ⟨v, .caseS hρ hv⟩
      | wrap u w =>
          have hL' : ∀ z, delP r (delP q L) z → (upd (upd ρ q u) r w z).size ≤ A.size :=
            fun z hz => by
              rw [upd_other _ w hz.1, upd_other ρ u hz.2.1]
              exact hL z hz.2.2
          have hS' : ∀ z, delP r (delP q S) z → (upd (upd ρ q u) r w z).size < A.size :=
            fun z hz => by
              rw [upd_other _ w hz.1, upd_other ρ u hz.2.1]
              exact hS z hz.2.2
          obtain ⟨v, hv⟩ := ihw (upd (upd ρ q u) r w) hL' hS'
          exact ⟨v, .caseW hρ hv⟩

/-- **Soundness of the guard in the fragment.** Every guarded fixpoint whose decreasing index names
a parameter evaluates on all arguments: its evaluation relation terminates. The proof is by
induction on the size of the decreasing argument, carried by the guard derivation. -/
theorem guarded_total (F : GFix) (hd : F.dec < 3) (hF : GuardOK F) :
    ∀ a₀ a₁ a₂ : Val, ∃ v, GEval F (params a₀ a₁ a₂) F.body v := by
  have key : ∀ n a₀ a₁ a₂, (valAt F.dec a₀ a₁ a₂).size = n →
      ∃ v, GEval F (params a₀ a₁ a₂) F.body v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a₀ a₁ a₂ hn
        refine guarded_eval_total F (valAt F.dec a₀ a₁ a₂)
          (fun b₀ b₁ b₂ hb => ih _ (hn ▸ hb) b₀ b₁ b₂ rfl) hF (params a₀ a₁ a₂) ?_ ?_
        · intro z hz
          have hz' : z = F.dec := hz
          subst hz'
          exact le_of_eq (congrArg Val.size (params_dec a₀ a₁ a₂ _ hd))
        · intro z hz
          exact hz.elim
  exact fun a₀ a₁ a₂ => key _ a₀ a₁ a₂ rfl

/-- The free recursor as a fixpoint over `b = 0, s = 1, n = 2`: `match n with zero ⇒ b |
succ m ⇒ wrap(s, recur(b, s, m)) | wrap _ _ ⇒ b`. Adapter: the exhaustive match adds the
`wrap` case, on which the free recursor has no rule, returning the base. -/
def recursorBody : GExp :=
  .caseOf 2 (.var 0) 3 (.wrap (.var 1) (.call (.var 0) (.var 1) (.var 3))) 3 4 (.var 0)

/-- Native data of `coqGuardAdmittance`: the declared decreasing parameter (`{struct k}`). -/
structure coqGuardAdmittanceData where
  structArg : Nat

/-- The fixpoint `recursorBody` with the declared decreasing parameter. -/
def coqGuardFix (M : coqGuardAdmittanceData) : GFix := ⟨M.structArg, recursorBody⟩

/-- Giménez 1995 (as restated in the Rocq manual, "Fixpoint definitions"): the declared decreasing
parameter is a parameter of the fixpoint, of the inductive type. -/
def coqGuardAdmittanceLaws (M : coqGuardAdmittanceData) : Prop := M.structArg < 3

/-- The guard check accepts the recursor definition. Adapter: `recursorBody`. -/
def coqGuardAdmittanceAccepts (M : coqGuardAdmittanceData) : Prop := GuardOK (coqGuardFix M)

/-- Verdict: fragment escape. The guard admits the recursor on its counter, and the yield is
termination of the evaluation of the definition on all arguments. -/
def coqGuardAdmittanceResult (M : coqGuardAdmittanceData) : Prop :=
  coqGuardAdmittanceAccepts M ∧
    ∀ a₀ a₁ a₂ : Val, ∃ v, GEval (coqGuardFix M) (params a₀ a₁ a₂) recursorBody v

/-- Soundness: the guard derivation yields termination of evaluation. -/
theorem coqGuardAdmittance_sound :
    ∀ M, coqGuardAdmittanceLaws M → coqGuardAdmittanceAccepts M → coqGuardAdmittanceResult M := by
  intro M hL hA
  exact ⟨hA, guarded_total (coqGuardFix M) hL hA⟩

/-- Witness: the declared decreasing parameter is the counter. -/
def coqGuardAdmittanceWitness : coqGuardAdmittanceData := ⟨2⟩

theorem coqGuardAdmittanceWitness_laws : coqGuardAdmittanceLaws coqGuardAdmittanceWitness := by
  show 2 < 3
  omega

theorem coqGuardAdmittanceWitness_accepts :
    coqGuardAdmittanceAccepts coqGuardAdmittanceWitness :=
  Guarded.caseIn rfl (Guarded.var _ _ _)
    (Guarded.wrap (Guarded.var _ _ _)
      (Guarded.call 3 (Guarded.var _ _ _) (Guarded.var _ _ _) (Guarded.var _ _ _) rfl (Or.inl rfl)))
    (Guarded.var _ _ _)

theorem coqGuardAdmittanceWitness_result : coqGuardAdmittanceResult coqGuardAdmittanceWitness :=
  coqGuardAdmittance_sound _ coqGuardAdmittanceWitness_laws coqGuardAdmittanceWitness_accepts

/-- The admitted definition computes the free recursor on numerals. -/
theorem eval_recursorBody (b s : Val) : ∀ k,
    GEval (coqGuardFix coqGuardAdmittanceWitness) (params b s (numeral k)) recursorBody
      (recurVal b s k)
  | 0 => GEval.caseZ rfl (GEval.var _ 0)
  | k + 1 => GEval.caseS rfl (GEval.wrap (GEval.var _ 1)
      (GEval.call (GEval.var _ 0) (GEval.var _ 1) (GEval.var _ 3) (eval_recursorBody b s k)))

/-- A recursive call on the matched counter itself. -/
def loopBody : GExp :=
  .caseOf 2 (.var 0) 3 (.call (.var 0) (.var 1) (.var 2)) 3 4 (.var 0)

theorem loop_not_guarded : ¬ GuardOK ⟨2, loopBody⟩ := by
  intro h
  cases h with
  | caseIn _ _ hes _ =>
      cases hes with
      | call z _ _ _ hz hS =>
          change GExp.var 2 = GExp.var z at hz
          injection hz with hz
          subst hz
          rcases hS with h3 | h3
          · exact absurd h3 (by decide)
          · exact h3
  | caseOut hL _ _ _ => exact hL rfl

/-- The unguarded call has no evaluation on a successor counter: every evaluation would contain a
smaller evaluation of the same call. -/
theorem loop_diverges {ρ : Nat → Val} {e : GExp} {v : Val} (h : GEval ⟨2, loopBody⟩ ρ e v) :
    (e = loopBody ∨ e = .call (.var 0) (.var 1) (.var 2)) → ∀ u, ρ 2 = .succ u → False := by
  induction h with
  | var => intro he; simp [loopBody] at he
  | zero => intro he; simp [loopBody] at he
  | succ _ _ => intro he; simp [loopBody] at he
  | wrap _ _ _ _ => intro he; simp [loopBody] at he
  | @call ρ e₀ e₁ e₂ a₀ a₁ a₂ w _ _ h₂ _ _ _ _ ihb =>
      intro he u hu
      rcases he with he | he
      · simp [loopBody] at he
      · obtain ⟨rfl, rfl, rfl⟩ := GExp.call.inj he
        have ha₂ : a₂ = ρ 2 := GEval_var_inv h₂
        exact ihb (Or.inl rfl) u (by simp [params, ha₂, hu])
  | @caseZ ρ x ez p es q r ew w hx _ _ =>
      intro he u hu
      rcases he with he | he
      · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := GExp.caseOf.inj he
        rw [hu] at hx
        cases hx
      · cases he
  | @caseS ρ x ez p es q r ew u' w hx _ ih =>
      intro he u hu
      rcases he with he | he
      · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := GExp.caseOf.inj he
        exact ih (Or.inr rfl) u (by rw [upd_other ρ u' (by decide)]; exact hu)
      · cases he
  | @caseW ρ x ez p es q r ew u' w' w hx _ _ =>
      intro he u hu
      rcases he with he | he
      · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := GExp.caseOf.inj he
        rw [hu] at hx
        cases hx
      · cases he

/-- A nested recursive call: `f(b, s, succ m) = f(b, s, f(zero, zero, m))`. -/
def nestedBody : GExp :=
  .caseOf 2 (.var 0) 3 (.call (.var 0) (.var 1) (.call .zero .zero (.var 3))) 3 4 (.var 0)

theorem nested_not_guarded : ¬ GuardOK ⟨2, nestedBody⟩ := by
  intro h
  cases h with
  | caseIn _ _ hes _ =>
      cases hes with
      | call z _ _ _ hz _ =>
          change GExp.call .zero .zero (.var 3) = GExp.var z at hz
          cases hz
  | caseOut hL _ _ _ => exact hL rfl

/-- The nested definition terminates on every argument (it returns its base), although the guard
rejects it. -/
theorem nested_total : ∀ n b s : Val, GEval ⟨2, nestedBody⟩ (params b s n) nestedBody b := by
  intro n
  induction n with
  | zero => intro b s; exact GEval.caseZ rfl (GEval.var _ 0)
  | succ m ih =>
      intro b s
      exact GEval.caseS rfl (GEval.call (GEval.var _ 0) (GEval.var _ 1)
        (GEval.call (GEval.zero _) (GEval.zero _) (GEval.var _ 3) (ih .zero .zero))
        (GEval.caseZ rfl (GEval.var _ 0)))
  | wrap _ _ _ _ => intro b s; exact GEval.caseW rfl (GEval.var _ 0)

/-- **Defining feature.** The structural definition is accepted and computes the free recursor; a
call on the matched counter itself is rejected and has no evaluation; a nested call in the
decreasing position is rejected although that definition terminates (the guard is a syntactic
condition on recursive arguments). -/
theorem coqGuardAdmittanceWitness_feature :
    (∀ b s k, GEval (coqGuardFix coqGuardAdmittanceWitness) (params b s (numeral k))
        recursorBody (recurVal b s k)) ∧
      ¬ GuardOK ⟨2, loopBody⟩ ∧
      (∀ a₀ a₁ u v, ¬ GEval ⟨2, loopBody⟩ (params a₀ a₁ (.succ u)) loopBody v) ∧
      ¬ GuardOK ⟨2, nestedBody⟩ ∧
      (∀ n b s : Val, GEval ⟨2, nestedBody⟩ (params b s n) nestedBody b) :=
  ⟨eval_recursorBody, loop_not_guarded,
    fun _ _ u _ h => loop_diverges h (Or.inl rfl) u rfl, nested_not_guarded, nested_total⟩

/-- **Mutation.** Declaring the payload as the decreasing parameter, everything else fixed: the law
holds and the guard rejects the recursive call. -/
theorem coqGuardAdmittance_mutation :
    coqGuardAdmittanceLaws ⟨1⟩ ∧ ¬ coqGuardAdmittanceAccepts ⟨1⟩ := by
  refine ⟨by show 1 < 3; omega, fun h => ?_⟩
  cases h with
  | caseIn hL _ _ _ => exact absurd (show (2 : Nat) = 1 from hL) (by decide)
  | caseOut _ _ hes _ =>
      cases hes with
      | wrap _ hcall =>
          cases hcall with
          | call z _ _ _ _ hS => exact hS.2

/-- **Scope of the fragment.** Omitted from Giménez 1995: λ-abstraction and higher-order
parameters, dependent types, mutual and nested inductive types, cofixpoints and their guard, case
analysis on terms that are not variables, and strong normalization of the whole calculus. The
statement named here is the paper's main theorem for this fragment, codification of guarded
definitions by a recursion scheme (the recurrence syntax `REx`); it is ESTABLISHED in the source
and not proved in this module. -/
def coqGuardAdmittance_scope : Prop :=
  ∀ F : GFix, F.dec < 3 → GuardOK F →
    ∃ E : REx, ∀ a₀ a₁ a₂ v, GEval F (params a₀ a₁ a₂) F.body v → reval E [a₀, a₁, a₂] = v

end OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines
