import OperatorKO7.Meta.DistinctionBoundary.GodelPrimitiveRecursiveClosure

set_option autoImplicit false

/-!
# Primitive-recursive tagged-syntax accessors

This module closes the arithmetic decoder layer that the earlier
`GodelPrimitiveRecursiveClosure.lean` deliberately left open.  The polynomial
pairing inverse `uncpair` is implemented by a bounded primitive recursion in its
search parameter.  Consequently the head/tail accessors for every positive
`ccons` code are primitive recursive.

These accessors are the load-bearing interface for the recursive substitution
and proof-checker closure modules.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- Predicate tested at one shell of the square pairing inverse. -/
def shellOk (n s : Nat) : Prop :=
  s * s ≤ n ∧ n - s * s ≤ s

instance shellOkDecidable (n s : Nat) : Decidable (shellOk n s) := by
  unfold shellOk
  infer_instance

/-- Output reconstructed from one successful shell. -/
def shellOut (n s : Nat) : Nat × Nat :=
  (s - (n - s * s), n - s * s)

/-- One primitive-recursion step for `uncpairGo`; the second component stores
`(shellIndex, previousResult)`. -/
def uncpairStep (n : Nat) (si : Nat × (Nat × Nat)) : Nat × Nat :=
  if shellOk n si.1 then shellOut n si.1 else si.2

/-- The shell predicate is primitive recursive. -/
theorem shellOk_primrec : PrimrecRel shellOk := by
  change PrimrecPred (fun p : Nat × Nat => shellOk p.1 p.2)
  have hn : Primrec (fun p : Nat × Nat => p.1) := Primrec.fst
  have hs : Primrec (fun p : Nat × Nat => p.2) := Primrec.snd
  have hss : Primrec (fun p : Nat × Nat => p.2 * p.2) :=
    Primrec.nat_mul.comp hs hs
  have hres : Primrec (fun p : Nat × Nat => p.1 - p.2 * p.2) :=
    Primrec.nat_sub.comp hn hss
  exact PrimrecPred.and
    (Primrec.nat_le.comp hss hn)
    (Primrec.nat_le.comp hres hs)

/-- The shell output map is primitive recursive. -/
theorem shellOut_primrec : Primrec₂ shellOut := by
  have hn : Primrec (fun p : Nat × Nat => p.1) := Primrec.fst
  have hs : Primrec (fun p : Nat × Nat => p.2) := Primrec.snd
  have hss : Primrec (fun p : Nat × Nat => p.2 * p.2) :=
    Primrec.nat_mul.comp hs hs
  have hres : Primrec (fun p : Nat × Nat => p.1 - p.2 * p.2) :=
    Primrec.nat_sub.comp hn hss
  have hleft : Primrec (fun p : Nat × Nat => p.2 - (p.1 - p.2 * p.2)) :=
    Primrec.nat_sub.comp hs hres
  have hp : Primrec (fun p : Nat × Nat => shellOut p.1 p.2) :=
    hleft.pair hres
  exact hp.to₂.of_eq (fun _ _ => rfl)

/-- One inverse-search step is primitive recursive. -/
theorem uncpairStep_primrec : Primrec₂ uncpairStep := by
  let X := Nat × (Nat × (Nat × Nat))
  have hn : Primrec (fun p : X => p.1) := Primrec.fst
  have hs : Primrec (fun p : X => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hprev : Primrec (fun p : X => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hp : PrimrecPred (fun p : X => shellOk p.1 p.2.1) :=
    shellOk_primrec.comp hn hs
  have hout : Primrec (fun p : X => shellOut p.1 p.2.1) :=
    shellOut_primrec.comp hn hs
  have hstep : Primrec (fun p : X => uncpairStep p.1 p.2) :=
    Primrec.ite hp hout hprev
  exact hstep.to₂.of_eq (fun _ _ => rfl)

/-- The bounded downward inverse search is primitive recursive in both the
coded value and its search fuel. -/
theorem uncpairGo_primrec : Primrec₂ (fun n s => uncpairGo s n) := by
  have hbase : Primrec (fun _ : Nat => (0, 0)) := Primrec.const (0, 0)
  have hrec := Primrec.nat_rec hbase uncpairStep_primrec
  exact hrec.of_eq fun n s => by
    induction s with
    | zero => rfl
    | succ s ih =>
        change uncpairStep n (s, Nat.rec (0, 0)
          (fun k prev => uncpairStep n (k, prev)) s) = uncpairGo (s + 1) n
        rw [ih]
        rfl

/-- The live inverse of the polynomial pairing is primitive recursive. -/
theorem uncpair_primrec : Primrec uncpair := by
  have h := uncpairGo_primrec.comp Primrec.id Primrec.succ
  exact h.of_eq fun n => rfl

/-- Head of a positive `ccons` code; zero maps to zero. -/
def cHead (n : Nat) : Nat :=
  if n = 0 then 0 else (uncpair (n - 1)).1

/-- Tail of a positive `ccons` code; zero maps to zero. -/
def cTail (n : Nat) : Nat :=
  if n = 0 then 0 else (uncpair (n - 1)).2

/-- `cHead` is primitive recursive. -/
theorem cHead_primrec : Primrec cHead := by
  have hun : Primrec (fun n : Nat => uncpair (n - 1)) :=
    uncpair_primrec.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))
  have hfst : Primrec (fun n : Nat => (uncpair (n - 1)).1) :=
    Primrec.fst.comp hun
  have hz : PrimrecPred (fun n : Nat => n = 0) :=
    Primrec.nat_le.comp Primrec.id (Primrec.const 0) |>
      fun h => h.of_eq (fun n => by simp)
  exact (Primrec.ite hz (Primrec.const 0) hfst).of_eq fun n => by
    simp [cHead]

/-- `cTail` is primitive recursive. -/
theorem cTail_primrec : Primrec cTail := by
  have hun : Primrec (fun n : Nat => uncpair (n - 1)) :=
    uncpair_primrec.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))
  have hsnd : Primrec (fun n : Nat => (uncpair (n - 1)).2) :=
    Primrec.snd.comp hun
  have hz : PrimrecPred (fun n : Nat => n = 0) :=
    Primrec.nat_le.comp Primrec.id (Primrec.const 0) |>
      fun h => h.of_eq (fun n => by simp)
  exact (Primrec.ite hz (Primrec.const 0) hsnd).of_eq fun n => by
    simp [cTail]

/-- Accessors compute exactly on a constructor code. -/
theorem cHead_ccons (h t : Nat) : cHead (ccons h t) = h := by
  simp [cHead, ccons_ne_zero, uncpair_pred_ccons]

/-- Tail accessor computes exactly on a constructor code. -/
theorem cTail_ccons (h t : Nat) : cTail (ccons h t) = t := by
  simp [cTail, ccons_ne_zero, uncpair_pred_ccons]

/-- Closed syntax-accessor package. -/
structure PrimitiveRecursiveSyntaxAccessors : Prop where
  pairPR : Primrec₂ cpair
  consPR : Primrec₂ ccons
  unpairPR : Primrec uncpair
  headPR : Primrec cHead
  tailPR : Primrec cTail

/-- The live tagged-code algebra has primitive-recursive constructor and
accessor operations. -/
theorem primitiveRecursiveSyntaxAccessors : PrimitiveRecursiveSyntaxAccessors :=
  ⟨cpair_primrec, ccons_primrec, uncpair_primrec,
    cHead_primrec, cTail_primrec⟩

#check @shellOk_primrec
#check @shellOut_primrec
#check @uncpairStep_primrec
#check @uncpairGo_primrec
#check @uncpair_primrec
#check @cHead_primrec
#check @cTail_primrec
#check @primitiveRecursiveSyntaxAccessors
#print axioms shellOk_primrec
#print axioms uncpairGo_primrec
#print axioms uncpair_primrec
#print axioms cHead_primrec
#print axioms cTail_primrec
#print axioms primitiveRecursiveSyntaxAccessors

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
