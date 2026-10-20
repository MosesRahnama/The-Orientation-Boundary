import Mathlib.Order.WellFounded
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange

set_option autoImplicit false

/-!
# Generic transitive lexicographic path order

Nat-valued precedence on a first-order signature. `LPO` is the one-step
subterm/precedence/lexicographic generator with **full lexicographic status**: the argument
positions before some position `k` agree, position `k` drops, and each later position is
dominated by the source term. The earlier equal-tail clause is the special case in which that
domination is the subterm clause, and it survives as the theorem `lpo_lex_equal_tail`.
`LPOOrder` is the transitive closure, which is the actual strict order exported to clients.
Stability and arbitrary one-hole context closure lift from the generator. Well-foundedness is
nested `Acc`: strong induction on precedence rank, the accessibility-restricted lexicographic
order on argument tuples (`acc_ArgLexAcc`), and a structural measure on the right-hand side
(`termSize_arg_lt`). No Kruskal, no minimal bad sequence.

Trust: kernel-only. No `sorry`/`admit`/`axiom`/`native_decide`.
-/

namespace OperatorKO7.LPOSchema

/-- Arity-indexed first-order signature with a Nat-valued strict precedence. The symbol type may
be infinite; the order proof uses only the rank assigned to each symbol. -/
structure FOSig where
  σ : Type
  arity : σ → Nat
  rank : σ → Nat

/-- First-order terms over `S`. Variables are indexed by `Nat`. -/
inductive FOTerm (S : FOSig) : Type
  | var : Nat → FOTerm S
  | app : (f : S.σ) → (Fin (S.arity f) → FOTerm S) → FOTerm S

open FOTerm

/-- One-step generator for the lexicographic path order. -/
inductive LPO (S : FOSig) : FOTerm S → FOTerm S → Prop
  | subEq {f : S.σ} {args : Fin (S.arity f) → FOTerm S} {i : Fin (S.arity f)} :
      LPO S (app f args) (args i)
  | subGt {f : S.σ} {args : Fin (S.arity f) → FOTerm S} {t : FOTerm S}
      {i : Fin (S.arity f)} :
      LPO S (args i) t → LPO S (app f args) t
  | prec {f g : S.σ} {ss : Fin (S.arity f) → FOTerm S}
      {ts : Fin (S.arity g) → FOTerm S} :
      S.rank g < S.rank f →
      (∀ j : Fin (S.arity g), LPO S (app f ss) (ts j)) →
      LPO S (app f ss) (app g ts)
  | lexFull {f : S.σ} {ss ts : Fin (S.arity f) → FOTerm S} {k : Fin (S.arity f)} :
      (∀ i : Fin (S.arity f), i.val < k.val → ss i = ts i) →
      LPO S (ss k) (ts k) →
      (∀ j : Fin (S.arity f), k.val < j.val → LPO S (app f ss) (ts j)) →
      LPO S (app f ss) (app f ts)

variable {S : FOSig}

/-- Structural size of a first-order term: one plus the sum of the argument sizes. It supplies
the measure for the recursion in the well-foundedness proof. -/
def termSize : FOTerm S → Nat
  | var _ => 1
  | app f args =>
      1 + (List.finRange (S.arity f)).foldr (fun i acc => termSize (args i) + acc) 0

theorem le_foldr_sum {n : Nat} (g : Fin n → Nat) :
    ∀ (l : List (Fin n)) {a : Fin n}, a ∈ l → g a ≤ l.foldr (fun x acc => g x + acc) 0
  | [], _, hmem => absurd hmem (by simp)
  | x :: xs, a, hmem => by
      rcases List.mem_cons.1 hmem with h | h
      · subst h
        simp
      · have hle := le_foldr_sum g xs h
        simp only [List.foldr_cons]
        omega

theorem termSize_pos (t : FOTerm S) : 0 < termSize t := by
  cases t with
  | var _ => simp [termSize]
  | app f args =>
      simp only [termSize]
      omega

/-- Every argument is strictly smaller than the application. -/
theorem termSize_arg_lt {f : S.σ} (args : Fin (S.arity f) → FOTerm S) (i : Fin (S.arity f)) :
    termSize (args i) < termSize (app f args) := by
  have hle :
      termSize (args i) ≤
        (List.finRange (S.arity f)).foldr (fun j acc => termSize (args j) + acc) 0 :=
    le_foldr_sum (fun j => termSize (args j)) (List.finRange (S.arity f)) (List.mem_finRange i)
  simp only [termSize]
  omega

theorem lpo_subterm {f : S.σ} (args : Fin (S.arity f) → FOTerm S)
    (i : Fin (S.arity f)) : LPO S (app f args) (args i) :=
  LPO.subEq

/-- **The equal-tail clause is a subrelation of the full lexicographic clause.** The order this
module exports uses full lexicographic status: the prefix agrees, one position strictly drops, and
the tail is arbitrary provided the source dominates each tail entry. When the tail is equal that
domination is the subterm clause, so every equal-tail step of the earlier order is a step of the
general one, and nothing that was provable before is lost. -/
theorem lpo_lex_equal_tail {f : S.σ} {ss ts : Fin (S.arity f) → FOTerm S}
    {k : Fin (S.arity f)}
    (hpref : ∀ i : Fin (S.arity f), i.val < k.val → ss i = ts i)
    (hcut : LPO S (ss k) (ts k))
    (htail : ∀ i : Fin (S.arity f), k.val < i.val → ss i = ts i) :
    LPO S (app f ss) (app f ts) :=
  LPO.lexFull hpref hcut (fun j hj => (htail j hj) ▸ LPO.subEq)

def subst (σmap : Nat → FOTerm S) : FOTerm S → FOTerm S
  | var n => σmap n
  | app f args => app f (fun i => subst σmap (args i))

theorem lpo_stable {s t : FOTerm S} (h : LPO S s t) (σmap : Nat → FOTerm S) :
    LPO S (subst σmap s) (subst σmap t) := by
  induction h with
  | subEq =>
      exact LPO.subEq
  | subGt h ih =>
      exact LPO.subGt ih
  | prec hrank _ ih =>
      exact LPO.prec hrank (fun j => ih j)
  | lexFull hpref _ _ ihcut ihdom =>
      refine LPO.lexFull ?_ ihcut ?_
      · intro i hi
        simpa [subst] using congrArg (subst σmap) (hpref i hi)
      · intro j hj
        simpa [subst] using ihdom j hj

def updateArg {f : S.σ} (args : Fin (S.arity f) → FOTerm S) (i : Fin (S.arity f))
    (u : FOTerm S) : Fin (S.arity f) → FOTerm S :=
  Function.update args i u

theorem lpo_monotone {f : S.σ} {args : Fin (S.arity f) → FOTerm S}
    {i : Fin (S.arity f)} {s t : FOTerm S} (h : LPO S s t) :
    LPO S (app f (updateArg args i s)) (app f (updateArg args i t)) := by
  refine lpo_lex_equal_tail (k := i) ?_ ?_ ?_
  · intro j hj
    have hne : j ≠ i := fun hEq => Nat.lt_irrefl _ (hEq ▸ hj)
    simp [updateArg, Function.update_of_ne hne]
  · simpa [updateArg, Function.update_self] using h
  · intro j hj
    have hne : j ≠ i := fun hEq => Nat.lt_irrefl _ (hEq ▸ hj)
    simp [updateArg, Function.update_of_ne hne]

/-- The strict path order exported to clients: transitive closure of the
subterm/precedence/equal-tail generator. -/
def LPOOrder (S : FOSig) : FOTerm S → FOTerm S → Prop :=
  Relation.TransGen (LPO S)

theorem lpo_to_lpoOrder {s t : FOTerm S} (h : LPO S s t) : LPOOrder S s t :=
  Relation.TransGen.single h

theorem lpoOrder_transitive : Transitive (LPOOrder S) :=
  Relation.transitive_transGen

theorem lpoOrder_subterm {f : S.σ} (args : Fin (S.arity f) → FOTerm S)
    (i : Fin (S.arity f)) : LPOOrder S (app f args) (args i) :=
  lpo_to_lpoOrder (lpo_subterm args i)

theorem lpoOrder_stable {s t : FOTerm S} (h : LPOOrder S s t)
    (σmap : Nat → FOTerm S) :
    LPOOrder S (subst σmap s) (subst σmap t) :=
  h.lift (subst σmap) (fun _ _ hst => lpo_stable hst σmap)

theorem lpoOrder_monotone {f : S.σ} {args : Fin (S.arity f) → FOTerm S}
    {i : Fin (S.arity f)} {s t : FOTerm S} (h : LPOOrder S s t) :
    LPOOrder S (app f (updateArg args i s)) (app f (updateArg args i t)) :=
  h.lift (fun u => app f (updateArg args i u))
    (fun _ _ hst => lpo_monotone hst)

/-- A first-order term with one distinguished hole. -/
inductive FOContext (S : FOSig) : Type
  | hole : FOContext S
  | app (f : S.σ) (args : Fin (S.arity f) → FOTerm S)
      (i : Fin (S.arity f)) (inner : FOContext S) : FOContext S

namespace FOContext

def plug : FOContext S → FOTerm S → FOTerm S
  | hole, t => t
  | app f args i inner, t =>
      FOTerm.app f (updateArg args i (plug inner t))

end FOContext

/-- The transitive path order is monotone under every finite one-hole context. -/
theorem lpoOrder_context_monotone (C : FOContext S) {s t : FOTerm S}
    (h : LPOOrder S s t) : LPOOrder S (C.plug s) (C.plug t) := by
  induction C with
  | hole => exact h
  | app f args i inner ih =>
      exact lpoOrder_monotone ih

/-- Reverse LPO: predecessors are strictly smaller terms. -/
def LPORev (a b : FOTerm S) : Prop := LPO S b a

/-- Reverse transitive path order. -/
def LPOOrderRev (a b : FOTerm S) : Prop := LPOOrder S b a

/-- One lexicographic descent on an argument tuple: the prefix agrees and one coordinate drops.
The tail is unconstrained, which is what full lexicographic status means. -/
private def ArgLex {n : Nat} (w v : Fin n → FOTerm S) : Prop :=
  ∃ k : Fin n, (∀ i : Fin n, i.val < k.val → w i = v i) ∧ LPO S (v k) (w k)

/-- The lexicographic descent restricted to tuples whose entries are already accessible. The
restriction is what makes the order well founded without Kruskal: the tail of a predecessor is
arbitrary as a term, but its accessibility travels with the step. -/
private def ArgLexAcc {n : Nat} (w v : Fin n → FOTerm S) : Prop :=
  (∀ i : Fin n, Acc LPORev (w i)) ∧ ArgLex w v

private def consTerm {n : Nat} (x : FOTerm S) (p : Fin n → FOTerm S) :
    Fin (n + 1) → FOTerm S :=
  fun i => i.cases x p

private def tailTerm {n : Nat} (v : Fin (n + 1) → FOTerm S) : Fin n → FOTerm S :=
  fun i => v i.succ

private theorem consTerm_zero {n : Nat} (x : FOTerm S) (p : Fin n → FOTerm S) :
    consTerm x p 0 = x :=
  rfl

private theorem consTerm_succ {n : Nat} (x : FOTerm S) (p : Fin n → FOTerm S)
    (i : Fin n) : consTerm x p i.succ = p i :=
  rfl

private theorem consTerm_self_tail {n : Nat} (v : Fin (n + 1) → FOTerm S) :
    consTerm (v 0) (tailTerm v) = v := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

private theorem acc_ArgLexAcc_cons {n : Nat}
    (ih : ∀ p : Fin n → FOTerm S, (∀ i, Acc LPORev (p i)) → Acc ArgLexAcc p)
    {x : FOTerm S} (hx : Acc LPORev x) :
    ∀ {p : Fin n → FOTerm S}, Acc ArgLexAcc p → Acc ArgLexAcc (consTerm x p) := by
  induction hx with
  | intro x _ ihx =>
    intro p hp
    induction hp with
    | intro p _ ihp =>
      refine Acc.intro (consTerm x p) fun w hw => ?_
      obtain ⟨hwAcc, k, hpref, hlt⟩ := hw
      cases k using Fin.cases with
      | zero =>
          have hLPO : LPORev (w 0) x := by
            change LPO S x (w 0)
            simpa [consTerm_zero] using hlt
          have hTail : Acc ArgLexAcc (tailTerm w) :=
            ih (tailTerm w) (fun i => hwAcc i.succ)
          have hAcc := ihx (w 0) hLPO hTail
          simpa [consTerm_self_tail] using hAcc
      | succ k =>
          have hxw : w 0 = x := by
            simpa [consTerm_zero] using hpref 0 (Nat.succ_pos k.val)
          have htailStep : ArgLexAcc (tailTerm w) p := by
            refine ⟨fun i => hwAcc i.succ, k, ?_, ?_⟩
            · intro i hi
              have : i.succ.val < k.succ.val := by
                simpa [Fin.val_succ] using Nat.succ_lt_succ hi
              simpa [tailTerm, consTerm_succ] using hpref i.succ this
            · simpa [consTerm_succ, tailTerm] using hlt
          have hAcc := ihp (tailTerm w) htailStep
          have hwEq : w = consTerm x (tailTerm w) :=
            (consTerm_self_tail w).symm.trans
              (congrArg (fun h => consTerm h (tailTerm w)) hxw)
          exact hwEq ▸ hAcc

/-- **Well-foundedness of the lexicographic argument order, without Kruskal.** A tuple whose
entries are accessible is accessible for the accessibility-restricted lexicographic descent. The
proof is a nested `Acc` induction: the head component uses the reverse path order, the tail uses
the same statement at the shorter length. -/
private theorem acc_ArgLexAcc :
    ∀ (n : Nat) (v : Fin n → FOTerm S), (∀ i, Acc LPORev (v i)) → Acc ArgLexAcc v := by
  intro n
  induction n with
  | zero =>
      intro v _
      refine Acc.intro _ fun w hw => ?_
      obtain ⟨-, k, -, -⟩ := hw
      exact k.elim0
  | succ n ih =>
      intro v hv
      have hcons :=
        acc_ArgLexAcc_cons ih (hv 0) (ih (tailTerm v) (fun i => hv i.succ))
      simpa [consTerm_self_tail] using hcons

/-- Every right-hand side of a path-order step out of `app f args` is accessible, given that the
arguments are accessible, that every lower-precedence application with accessible arguments is
accessible, and that every lexicographic descendant of the argument tuple is accessible. The
recursion is on `termSize` of the right-hand side: the precedence clause and the full
lexicographic clause recurse only into arguments of that term. No Kruskal, no minimal bad
sequence. -/
private theorem acc_rhs_of_lpo_aux {f : S.σ} {args : Fin (S.arity f) → FOTerm S}
    (hargs : ∀ i, Acc LPORev (args i))
    (hLower :
      ∀ (g : S.σ) (us : Fin (S.arity g) → FOTerm S),
        S.rank g < S.rank f →
        (∀ i, Acc LPORev (us i)) → Acc LPORev (app g us))
    (ihLex : ∀ ts, ArgLexAcc ts args → Acc LPORev (app f ts)) :
    ∀ (n : Nat) (t : FOTerm S), termSize t ≤ n → LPO S (app f args) t → Acc LPORev t := by
  intro n
  induction n with
  | zero =>
      intro t hle _
      have := termSize_pos t
      omega
  | succ n ih =>
      intro t hle ht
      cases ht with
      | subEq => exact hargs _
      | subGt h => exact Acc.inv (hargs _) h
      | @prec _ _ _ us hrank hdom =>
          refine hLower _ _ hrank (fun j => ih (us j) ?_ (hdom j))
          have hlt := termSize_arg_lt us j
          omega
      | @lexFull _ _ us k hpref hcut hdom =>
          have hAccTs : ∀ i, Acc LPORev (us i) := by
            intro i
            by_cases hlt : i.val < k.val
            · exact (hpref i hlt) ▸ hargs i
            · by_cases hgt : k.val < i.val
              · refine ih (us i) ?_ (hdom i hgt)
                have hsz := termSize_arg_lt us i
                omega
              · have hki : k = i :=
                  Fin.eq_of_val_eq (Nat.le_antisymm (Nat.not_lt.mp hlt) (Nat.not_lt.mp hgt))
                exact hki ▸ Acc.inv (hargs k) hcut
          exact ihLex us ⟨hAccTs, k, fun i hi => (hpref i hi).symm, hcut⟩

private theorem acc_rhs_of_lpo {f : S.σ} {args : Fin (S.arity f) → FOTerm S}
    (hargs : ∀ i, Acc LPORev (args i))
    (hLower :
      ∀ (g : S.σ) (us : Fin (S.arity g) → FOTerm S),
        S.rank g < S.rank f →
        (∀ i, Acc LPORev (us i)) → Acc LPORev (app g us))
    (ihLex : ∀ ts, ArgLexAcc ts args → Acc LPORev (app f ts))
    {t : FOTerm S} (ht : LPO S (app f args) t) : Acc LPORev t :=
  acc_rhs_of_lpo_aux hargs hLower ihLex (termSize t) t (le_refl _) ht

private theorem acc_fun_core (f : S.σ)
    (hLower :
      ∀ (g : S.σ) (us : Fin (S.arity g) → FOTerm S),
        S.rank g < S.rank f →
        (∀ i, Acc LPORev (us i)) → Acc LPORev (app g us))
    (args : Fin (S.arity f) → FOTerm S)
    (hargs : ∀ i, Acc LPORev (args i)) : Acc LPORev (app f args) := by
  have hA := acc_ArgLexAcc (S.arity f) args hargs
  revert hargs
  induction hA with
  | intro args _ ihLex =>
    intro hargs
    refine Acc.intro (app f args) fun t ht =>
      acc_rhs_of_lpo hargs hLower (fun ts hts => ihLex ts hts hts.1) ht

private theorem acc_fun_rank :
    ∀ (n : Nat) (f : S.σ), S.rank f = n →
      ∀ args, (∀ i, Acc LPORev (args i)) → Acc LPORev (app f args) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ihn =>
    intro f hf args hargs
    refine acc_fun_core f ?_ args hargs
    intro g us hlt hAcc
    have hltn : S.rank g < n := hf ▸ hlt
    exact ihn (S.rank g) hltn g rfl us hAcc

private theorem acc_fun (f : S.σ) (args : Fin (S.arity f) → FOTerm S)
    (hargs : ∀ i, Acc LPORev (args i)) : Acc LPORev (app f args) :=
  acc_fun_rank (S.rank f) f rfl args hargs

private theorem acc_term : ∀ t : FOTerm S, Acc LPORev t
  | var _ =>
      Acc.intro _ fun _ ht => by cases ht
  | app f args =>
      acc_fun f args fun i => acc_term (args i)

/-- LPO is well-founded in reverse. Nested `Acc`, no Kruskal. -/
theorem lpo_wellFounded : WellFounded (@LPORev S) :=
  ⟨acc_term⟩

/-- The exported transitive path order is well-founded in reverse. -/
theorem lpoOrder_wellFounded : WellFounded (@LPOOrderRev S) := by
  have hwf : WellFounded (Relation.TransGen (@LPORev S)) :=
    lpo_wellFounded.transGen
  apply Subrelation.wf ?_ hwf
  intro a b hab
  change Relation.TransGen (LPO S) b a at hab
  simpa [LPORev] using hab.swap

end OperatorKO7.LPOSchema
