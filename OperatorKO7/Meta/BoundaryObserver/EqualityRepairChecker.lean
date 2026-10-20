import OperatorKO7.Meta.BoundaryObserver.EqualityRepair
import OperatorKO7.Meta.DistinctionBoundary.GodelPrimitiveRecursiveProofTreeChecker

/-!
# The numeric proof relation of the repaired checker

Manuscript: the sentence "Its proof relation is primitive recursive" of Theorem
`thm:godel-equality-repair` of the Observation-Boundary Principle.

The code pairing `cpair a b = (a + b)² + b` is not onto, so a number can parse as a term, formula or
proof code without being the code of one. The recognizers `isTermCodeB`, `isFormulaCodeB` and
`isProofCodeCB` check at every node that the number is the pairing of its parts, and accept exactly
the canonical codes. The five equality schemes are recognized on codes by comparison with code
templates built from the extracted subcodes. The numeric checker `checkProofCodeE` is the numeric
checker of `T_0` with the axiom test extended by the equality schemes. The Boolean relation
`proofRelE n m` holds exactly when `n` is the canonical code of a `T_E` proof with conclusion code
`m`; it is primitive recursive, and `∃ n, proofRelE n ⌜φ⌝ = true` holds exactly when `T_E ⊢ φ`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.EqualityRepairChecker

open OperatorKO7.Meta.DistinctionBoundary.GodelArith
open OperatorKO7.Meta.BoundaryObserver.EqualityRepair

/-! ## Code arithmetic -/

theorem ccons_inj {a b c d : Nat} : ccons a b = ccons c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h' := congrArg (fun n => uncpair (n - 1)) h
    simp only [uncpair_pred_ccons, Prod.mk.injEq] at h'
    exact h'
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem codeEqB_iff {a b : Nat} : codeEqB a b = true ↔ a = b := by
  simp [codeEqB]

theorem codeEqB_self (a : Nat) : codeEqB a a = true := codeEqB_iff.2 rfl

theorem ccP {α : Type} [Primcodable α] {f g : α → Nat} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => ccons (f x) (g x)) :=
  ccons_primrec.comp hf hg

/-! ## Inversion of codes -/

theorem encodeTerm_succ_inv {u : Term} {x : Nat} (h : encodeTerm u = ccons 1 x) :
    ∃ t, u = Term.succ t ∧ encodeTerm t = x := by
  cases u <;> simp only [encodeTerm, ccons_inj] at h <;> try omega
  exact ⟨_, rfl, h.2⟩

theorem encodeTerm_add_inv {u : Term} {x y : Nat} (h : encodeTerm u = ccons 2 (ccons x y)) :
    ∃ s t, u = Term.add s t ∧ encodeTerm s = x ∧ encodeTerm t = y := by
  cases u <;> simp only [encodeTerm, ccons_inj] at h <;> try omega
  exact ⟨_, _, rfl, h.2.1, h.2.2⟩

theorem encodeTerm_mul_inv {u : Term} {x y : Nat} (h : encodeTerm u = ccons 3 (ccons x y)) :
    ∃ s t, u = Term.mul s t ∧ encodeTerm s = x ∧ encodeTerm t = y := by
  cases u <;> simp only [encodeTerm, ccons_inj] at h <;> try omega
  exact ⟨_, _, rfl, h.2.1, h.2.2⟩

theorem encodeFormula_eq_inv {φ : Formula} {x y : Nat} (h : encodeFormula φ = ccons 0 (ccons x y)) :
    ∃ s t, φ = Formula.eq s t ∧ encodeTerm s = x ∧ encodeTerm t = y := by
  cases φ <;> simp only [encodeFormula, ccons_inj] at h <;> try omega
  exact ⟨_, _, rfl, h.2.1, h.2.2⟩

theorem encodeFormula_imp_inv {φ : Formula} {x y : Nat}
    (h : encodeFormula φ = ccons 2 (ccons x y)) :
    ∃ A B, φ = Formula.imp A B ∧ encodeFormula A = x ∧ encodeFormula B = y := by
  cases φ <;> simp only [encodeFormula, ccons_inj] at h <;> try omega
  exact ⟨_, _, rfl, h.2.1, h.2.2⟩

/-! ## Code templates of the equality schemes -/

def eqCode (a b : Nat) : Nat := ccons 0 (ccons a b)
def impCode (a b : Nat) : Nat := ccons 2 (ccons a b)

def symT (a b : Nat) : Nat := impCode (eqCode a b) (eqCode b a)
def transT (a b u : Nat) : Nat := impCode (eqCode a b) (impCode (eqCode b u) (eqCode a u))
def succT (a b : Nat) : Nat := impCode (eqCode a b) (eqCode (ccons 1 a) (ccons 1 b))
def addT (a a' b b' : Nat) : Nat :=
  impCode (eqCode a a') (impCode (eqCode b b') (eqCode (ccons 2 (ccons a b)) (ccons 2 (ccons a' b'))))
def mulT (a a' b b' : Nat) : Nat :=
  impCode (eqCode a a') (impCode (eqCode b b') (eqCode (ccons 3 (ccons a b)) (ccons 3 (ccons a' b'))))

/-- First term code of the antecedent equation. -/
def cA (c : Nat) : Nat := codeLeft (codeLeft c)
/-- Second term code of the antecedent equation. -/
def cB (c : Nat) : Nat := codeRight (codeLeft c)
/-- First term code of the second antecedent equation. -/
def cC (c : Nat) : Nat := codeLeft (codeLeft (codeRight c))
/-- Second term code of the second antecedent equation. -/
def cD (c : Nat) : Nat := codeRight (codeLeft (codeRight c))

def isEqSymCodeB (c : Nat) : Bool := codeEqB c (symT (cA c) (cB c))
def isEqTransCodeB (c : Nat) : Bool := codeEqB c (transT (cA c) (cB c) (cD c))
def isEqSuccCodeB (c : Nat) : Bool := codeEqB c (succT (cA c) (cB c))
def isEqAddCodeB (c : Nat) : Bool := codeEqB c (addT (cA c) (cB c) (cC c) (cD c))
def isEqMulCodeB (c : Nat) : Bool := codeEqB c (mulT (cA c) (cB c) (cC c) (cD c))

def isEqAxiomCodeB (c : Nat) : Bool :=
  isEqSymCodeB c || isEqTransCodeB c || isEqSuccCodeB c || isEqAddCodeB c || isEqMulCodeB c

def isAxiomCodeEB (c : Nat) : Bool := isAxiomCodeB c || isEqAxiomCodeB c

theorem cA_primrec : Primrec cA := codeLeft_primrec.comp codeLeft_primrec
theorem cB_primrec : Primrec cB := codeRight_primrec.comp codeLeft_primrec
theorem cC_primrec : Primrec cC := codeLeft_primrec.comp (codeLeft_primrec.comp codeRight_primrec)
theorem cD_primrec : Primrec cD := codeRight_primrec.comp (codeLeft_primrec.comp codeRight_primrec)

theorem isEqAxiomCodeB_primrec : Primrec isEqAxiomCodeB := by
  have c0 : Primrec (fun _ : Nat => (0 : Nat)) := Primrec.const 0
  have c1 : Primrec (fun _ : Nat => (1 : Nat)) := Primrec.const 1
  have c2 : Primrec (fun _ : Nat => (2 : Nat)) := Primrec.const 2
  have c3 : Primrec (fun _ : Nat => (3 : Nat)) := Primrec.const 3
  have hA := cA_primrec
  have hB := cB_primrec
  have hC := cC_primrec
  have hD := cD_primrec
  have eqP : ∀ {f g : Nat → Nat}, Primrec f → Primrec g → Primrec (fun c => eqCode (f c) (g c)) :=
    fun hf hg => ccP c0 (ccP hf hg)
  have impP : ∀ {f g : Nat → Nat}, Primrec f → Primrec g → Primrec (fun c => impCode (f c) (g c)) :=
    fun hf hg => ccP c2 (ccP hf hg)
  have hsym : Primrec isEqSymCodeB :=
    codeEqB_primrec.comp Primrec.id (impP (eqP hA hB) (eqP hB hA))
  have htrans : Primrec isEqTransCodeB :=
    codeEqB_primrec.comp Primrec.id (impP (eqP hA hB) (impP (eqP hB hD) (eqP hA hD)))
  have hsucc : Primrec isEqSuccCodeB :=
    codeEqB_primrec.comp Primrec.id (impP (eqP hA hB) (eqP (ccP c1 hA) (ccP c1 hB)))
  have hadd : Primrec isEqAddCodeB :=
    codeEqB_primrec.comp Primrec.id (impP (eqP hA hB) (impP (eqP hC hD)
      (eqP (ccP c2 (ccP hA hC)) (ccP c2 (ccP hB hD)))))
  have hmul : Primrec isEqMulCodeB :=
    codeEqB_primrec.comp Primrec.id (impP (eqP hA hB) (impP (eqP hC hD)
      (eqP (ccP c3 (ccP hA hC)) (ccP c3 (ccP hB hD)))))
  exact Primrec.or.comp (Primrec.or.comp (Primrec.or.comp (Primrec.or.comp hsym htrans) hsucc) hadd)
    hmul

theorem isAxiomCodeEB_primrec : Primrec isAxiomCodeEB :=
  Primrec.or.comp isAxiomCodeB_primrec isEqAxiomCodeB_primrec

/-! ## Shapes of the equality schemes -/

theorem isEqSym_iff (φ : Formula) :
    isEqSym φ = true ↔ ∃ s t, φ = Formula.imp (Formula.eq s t) (Formula.eq t s) := by
  constructor
  · intro h
    unfold isEqSym at h
    split at h
    · simp only [decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, _, rfl⟩
    · exact absurd h Bool.false_ne_true
  · rintro ⟨s, t, rfl⟩
    simp [isEqSym]

theorem isEqTrans_iff (φ : Formula) :
    isEqTrans φ = true ↔ ∃ s t u, φ = Formula.imp (Formula.eq s t)
      (Formula.imp (Formula.eq t u) (Formula.eq s u)) := by
  constructor
  · intro h
    unfold isEqTrans at h
    split at h
    · simp only [decide_eq_true_eq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨_, _, _, rfl⟩
    · exact absurd h Bool.false_ne_true
  · rintro ⟨s, t, u, rfl⟩
    simp [isEqTrans]

theorem isEqSucc_iff (φ : Formula) :
    isEqSucc φ = true ↔ ∃ s t, φ = Formula.imp (Formula.eq s t)
      (Formula.eq (Term.succ s) (Term.succ t)) := by
  constructor
  · intro h
    unfold isEqSucc at h
    split at h
    · simp only [decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, _, rfl⟩
    · exact absurd h Bool.false_ne_true
  · rintro ⟨s, t, rfl⟩
    simp [isEqSucc]

theorem isEqAdd_iff (φ : Formula) :
    isEqAdd φ = true ↔ ∃ s s' t t', φ = Formula.imp (Formula.eq s s')
      (Formula.imp (Formula.eq t t') (Formula.eq (Term.add s t) (Term.add s' t'))) := by
  constructor
  · intro h
    unfold isEqAdd at h
    split at h
    · simp only [decide_eq_true_eq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨_, _, _, _, rfl⟩
    · exact absurd h Bool.false_ne_true
  · rintro ⟨s, s', t, t', rfl⟩
    simp [isEqAdd]

theorem isEqMul_iff (φ : Formula) :
    isEqMul φ = true ↔ ∃ s s' t t', φ = Formula.imp (Formula.eq s s')
      (Formula.imp (Formula.eq t t') (Formula.eq (Term.mul s t) (Term.mul s' t'))) := by
  constructor
  · intro h
    unfold isEqMul at h
    split at h
    · simp only [decide_eq_true_eq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨_, _, _, _, rfl⟩
    · exact absurd h Bool.false_ne_true
  · rintro ⟨s, s', t, t', rfl⟩
    simp [isEqMul]

/-! ## The scheme recognizers on canonical codes -/

theorem codeLeft_ccons (a b c : Nat) : codeLeft (ccons a (ccons b c)) = b := by
  simp [codeLeft, cHead_ccons, cTail_ccons]

theorem codeRight_ccons (a b c : Nat) : codeRight (ccons a (ccons b c)) = c := by
  simp [codeRight, cTail_ccons]

theorem isEqSymCodeB_encode (φ : Formula) : isEqSymCodeB (encodeFormula φ) = isEqSym φ := by
  apply Bool.eq_iff_iff.2
  rw [isEqSym_iff]
  constructor
  · intro h
    have hc := codeEqB_iff.1 h
    generalize cA (encodeFormula φ) = a at hc
    generalize cB (encodeFormula φ) = b at hc
    obtain ⟨A, B, rfl, hA, hB⟩ := encodeFormula_imp_inv hc
    obtain ⟨s, t, rfl, hs, ht⟩ := encodeFormula_eq_inv hA
    obtain ⟨t', s', rfl, ht', hs'⟩ := encodeFormula_eq_inv hB
    obtain rfl : s' = s := encodeTerm_injective (hs'.trans hs.symm)
    obtain rfl : t' = t := encodeTerm_injective (ht'.trans ht.symm)
    exact ⟨_, _, rfl⟩
  · rintro ⟨s, t, rfl⟩
    simp only [isEqSymCodeB, cA, cB, encodeFormula, codeLeft_ccons, codeRight_ccons]
    exact codeEqB_self _

theorem isEqTransCodeB_encode (φ : Formula) :
    isEqTransCodeB (encodeFormula φ) = isEqTrans φ := by
  apply Bool.eq_iff_iff.2
  rw [isEqTrans_iff]
  constructor
  · intro h
    have hc := codeEqB_iff.1 h
    generalize cA (encodeFormula φ) = a at hc
    generalize cB (encodeFormula φ) = b at hc
    generalize cD (encodeFormula φ) = u at hc
    obtain ⟨A, B, rfl, hA, hB⟩ := encodeFormula_imp_inv hc
    obtain ⟨s, t, rfl, hs, ht⟩ := encodeFormula_eq_inv hA
    obtain ⟨B1, B2, rfl, hB1, hB2⟩ := encodeFormula_imp_inv hB
    obtain ⟨t', u', rfl, ht', hu'⟩ := encodeFormula_eq_inv hB1
    obtain ⟨s', u'', rfl, hs', hu''⟩ := encodeFormula_eq_inv hB2
    obtain rfl : t' = t := encodeTerm_injective (ht'.trans ht.symm)
    obtain rfl : s' = s := encodeTerm_injective (hs'.trans hs.symm)
    obtain rfl : u'' = u' := encodeTerm_injective (hu''.trans hu'.symm)
    exact ⟨_, _, _, rfl⟩
  · rintro ⟨s, t, u, rfl⟩
    simp only [isEqTransCodeB, cA, cB, cD, encodeFormula, codeLeft_ccons, codeRight_ccons]
    exact codeEqB_self _

theorem isEqSuccCodeB_encode (φ : Formula) : isEqSuccCodeB (encodeFormula φ) = isEqSucc φ := by
  apply Bool.eq_iff_iff.2
  rw [isEqSucc_iff]
  constructor
  · intro h
    have hc := codeEqB_iff.1 h
    generalize cA (encodeFormula φ) = a at hc
    generalize cB (encodeFormula φ) = b at hc
    obtain ⟨A, B, rfl, hA, hB⟩ := encodeFormula_imp_inv hc
    obtain ⟨s, t, rfl, hs, ht⟩ := encodeFormula_eq_inv hA
    obtain ⟨u, v, rfl, hu, hv⟩ := encodeFormula_eq_inv hB
    obtain ⟨s', rfl, hs'⟩ := encodeTerm_succ_inv (hu.trans (by rw [← hs]))
    obtain ⟨t', rfl, ht'⟩ := encodeTerm_succ_inv (hv.trans (by rw [← ht]))
    obtain rfl : s' = s := encodeTerm_injective hs'
    obtain rfl : t' = t := encodeTerm_injective ht'
    exact ⟨s', t', rfl⟩
  · rintro ⟨s, t, rfl⟩
    simp only [isEqSuccCodeB, cA, cB, encodeFormula, encodeTerm, codeLeft_ccons, codeRight_ccons]
    exact codeEqB_self _

theorem isEqAddCodeB_encode (φ : Formula) : isEqAddCodeB (encodeFormula φ) = isEqAdd φ := by
  apply Bool.eq_iff_iff.2
  rw [isEqAdd_iff]
  constructor
  · intro h
    have hc := codeEqB_iff.1 h
    generalize cA (encodeFormula φ) = a at hc
    generalize cB (encodeFormula φ) = a' at hc
    generalize cC (encodeFormula φ) = b at hc
    generalize cD (encodeFormula φ) = b' at hc
    obtain ⟨A, B, rfl, hA, hB⟩ := encodeFormula_imp_inv hc
    obtain ⟨s, s', rfl, hs, hs'⟩ := encodeFormula_eq_inv hA
    obtain ⟨B1, B2, rfl, hB1, hB2⟩ := encodeFormula_imp_inv hB
    obtain ⟨t, t', rfl, ht, ht'⟩ := encodeFormula_eq_inv hB1
    obtain ⟨l, r, rfl, hl, hr⟩ := encodeFormula_eq_inv hB2
    obtain ⟨l1, l2, rfl, hl1, hl2⟩ := encodeTerm_add_inv (hl.trans (by rw [← hs, ← ht]))
    obtain ⟨r1, r2, rfl, hr1, hr2⟩ := encodeTerm_add_inv (hr.trans (by rw [← hs', ← ht']))
    obtain rfl : l1 = s := encodeTerm_injective hl1
    obtain rfl : l2 = t := encodeTerm_injective hl2
    obtain rfl : r1 = s' := encodeTerm_injective hr1
    obtain rfl : r2 = t' := encodeTerm_injective hr2
    exact ⟨l1, r1, l2, r2, rfl⟩
  · rintro ⟨s, s', t, t', rfl⟩
    simp only [isEqAddCodeB, cA, cB, cC, cD, encodeFormula, encodeTerm, codeLeft_ccons,
      codeRight_ccons]
    exact codeEqB_self _

theorem isEqMulCodeB_encode (φ : Formula) : isEqMulCodeB (encodeFormula φ) = isEqMul φ := by
  apply Bool.eq_iff_iff.2
  rw [isEqMul_iff]
  constructor
  · intro h
    have hc := codeEqB_iff.1 h
    generalize cA (encodeFormula φ) = a at hc
    generalize cB (encodeFormula φ) = a' at hc
    generalize cC (encodeFormula φ) = b at hc
    generalize cD (encodeFormula φ) = b' at hc
    obtain ⟨A, B, rfl, hA, hB⟩ := encodeFormula_imp_inv hc
    obtain ⟨s, s', rfl, hs, hs'⟩ := encodeFormula_eq_inv hA
    obtain ⟨B1, B2, rfl, hB1, hB2⟩ := encodeFormula_imp_inv hB
    obtain ⟨t, t', rfl, ht, ht'⟩ := encodeFormula_eq_inv hB1
    obtain ⟨l, r, rfl, hl, hr⟩ := encodeFormula_eq_inv hB2
    obtain ⟨l1, l2, rfl, hl1, hl2⟩ := encodeTerm_mul_inv (hl.trans (by rw [← hs, ← ht]))
    obtain ⟨r1, r2, rfl, hr1, hr2⟩ := encodeTerm_mul_inv (hr.trans (by rw [← hs', ← ht']))
    obtain rfl : l1 = s := encodeTerm_injective hl1
    obtain rfl : l2 = t := encodeTerm_injective hl2
    obtain rfl : r1 = s' := encodeTerm_injective hr1
    obtain rfl : r2 = t' := encodeTerm_injective hr2
    exact ⟨l1, r1, l2, r2, rfl⟩
  · rintro ⟨s, s', t, t', rfl⟩
    simp only [isEqMulCodeB, cA, cB, cC, cD, encodeFormula, encodeTerm, codeLeft_ccons,
      codeRight_ccons]
    exact codeEqB_self _

theorem isEqAxiomCodeB_encode (φ : Formula) : isEqAxiomCodeB (encodeFormula φ) = isEqAxiom φ := by
  simp only [isEqAxiomCodeB, isEqAxiom, isEqSymCodeB_encode, isEqTransCodeB_encode,
    isEqSuccCodeB_encode, isEqAddCodeB_encode, isEqMulCodeB_encode]

theorem isAxiomCodeEB_encode (φ : Formula) : isAxiomCodeEB (encodeFormula φ) = isAxiomE φ := by
  simp only [isAxiomCodeEB, isAxiomE, isAxiomCodeB_encode, isEqAxiomCodeB_encode]

/-! ## Canonical term, formula and proof codes -/

/-- Recognizer of canonical term codes. -/
def isTermCodeB (n : Nat) : Bool :=
  if h : n = 0 then false
  else
    let p := uncpair (n - 1)
    codeEqB (ccons p.1 p.2) n &&
    match p.1 with
    | 0 => codeEqB p.2 0
    | 1 => isTermCodeB p.2
    | 2 =>
      if hp : p.2 = 0 then false
      else
        let q := uncpair (p.2 - 1)
        codeEqB (ccons q.1 q.2) p.2 && (isTermCodeB q.1 && isTermCodeB q.2)
    | 3 =>
      if hp : p.2 = 0 then false
      else
        let q := uncpair (p.2 - 1)
        codeEqB (ccons q.1 q.2) p.2 && (isTermCodeB q.1 && isTermCodeB q.2)
    | 4 => true
    | _ => false
termination_by n
decreasing_by
  · exact (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt p.2 hp).1 (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt p.2 hp).1 (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2

/-- Recognizer of canonical formula codes. -/
def isFormulaCodeB (n : Nat) : Bool :=
  if h : n = 0 then false
  else
    let p := uncpair (n - 1)
    codeEqB (ccons p.1 p.2) n &&
    match p.1 with
    | 0 =>
      if hp : p.2 = 0 then false
      else
        let q := uncpair (p.2 - 1)
        codeEqB (ccons q.1 q.2) p.2 && (isTermCodeB q.1 && isTermCodeB q.2)
    | 1 => isFormulaCodeB p.2
    | 2 =>
      if hp : p.2 = 0 then false
      else
        let q := uncpair (p.2 - 1)
        codeEqB (ccons q.1 q.2) p.2 && (isFormulaCodeB q.1 && isFormulaCodeB q.2)
    | 3 =>
      if hp : p.2 = 0 then false
      else
        let q := uncpair (p.2 - 1)
        codeEqB (ccons q.1 q.2) p.2 && isFormulaCodeB q.2
    | _ => false
termination_by n
decreasing_by
  · exact (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt p.2 hp).1 (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2

/-- Recognizer of canonical proof-tree codes. -/
def isProofCodeCB (n : Nat) : Bool :=
  if h : n = 0 then false
  else
    let p := uncpair (n - 1)
    codeEqB (ccons p.1 p.2) n &&
    match p.1 with
    | 0 => isFormulaCodeB p.2
    | 1 =>
      if hp : p.2 = 0 then false
      else
        let q := uncpair (p.2 - 1)
        codeEqB (ccons q.1 q.2) p.2 && (isProofCodeCB q.1 && isProofCodeCB q.2)
    | 2 =>
      if hp : p.2 = 0 then false
      else
        let q := uncpair (p.2 - 1)
        codeEqB (ccons q.1 q.2) p.2 && isProofCodeCB q.2
    | 3 =>
      if hp : p.2 = 0 then false
      else
        let q := uncpair (p.2 - 1)
        if hq : q.2 = 0 then false
        else
          let r := uncpair (q.2 - 1)
          codeEqB (ccons q.1 q.2) p.2 && (codeEqB (ccons r.1 r.2) q.2 &&
            (isTermCodeB r.1 && isProofCodeCB r.2))
    | _ => false
termination_by n
decreasing_by
  · exact Nat.lt_trans (uncpair_lt p.2 hp).1 (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt q.2 hq).2
      (Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2)

theorem isTermCodeB_encode (t : Term) : isTermCodeB (encodeTerm t) = true := by
  induction t with
  | zero => simp [isTermCodeB, encodeTerm, ccons_ne_zero, uncpair_pred_ccons, codeEqB]
  | succ t ih => simp [isTermCodeB, encodeTerm, ccons_ne_zero, uncpair_pred_ccons, codeEqB, ih]
  | add s t ihs iht =>
      simp [isTermCodeB, encodeTerm, ccons_ne_zero, uncpair_pred_ccons, codeEqB, ihs, iht]
  | mul s t ihs iht =>
      simp [isTermCodeB, encodeTerm, ccons_ne_zero, uncpair_pred_ccons, codeEqB, ihs, iht]
  | var x => simp [isTermCodeB, encodeTerm, ccons_ne_zero, uncpair_pred_ccons, codeEqB]

theorem isFormulaCodeB_encode (φ : Formula) : isFormulaCodeB (encodeFormula φ) = true := by
  induction φ with
  | eq s t =>
      simp [isFormulaCodeB, encodeFormula, ccons_ne_zero, uncpair_pred_ccons, codeEqB,
        isTermCodeB_encode]
  | not φ ih => simp [isFormulaCodeB, encodeFormula, ccons_ne_zero, uncpair_pred_ccons, codeEqB, ih]
  | imp φ ψ ihφ ihψ =>
      simp [isFormulaCodeB, encodeFormula, ccons_ne_zero, uncpair_pred_ccons, codeEqB, ihφ, ihψ]
  | all x φ ih =>
      simp [isFormulaCodeB, encodeFormula, ccons_ne_zero, uncpair_pred_ccons, codeEqB, ih]

theorem isProofCodeCB_encode (p : ProofTree) : isProofCodeCB (encodeProof p) = true := by
  induction p with
  | ax φ =>
      simp [isProofCodeCB, encodeProof, ccons_ne_zero, uncpair_pred_ccons, codeEqB,
        isFormulaCodeB_encode]
  | mp p q ihp ihq =>
      simp [isProofCodeCB, encodeProof, ccons_ne_zero, uncpair_pred_ccons, codeEqB, ihp, ihq]
  | gen x p ih =>
      simp [isProofCodeCB, encodeProof, ccons_ne_zero, uncpair_pred_ccons, codeEqB, ih]
  | spec x t p ih =>
      simp [isProofCodeCB, encodeProof, ccons_ne_zero, uncpair_pred_ccons, codeEqB, ih,
        isTermCodeB_encode]

/-- Every accepted number is the canonical code of a term. -/
theorem isTermCodeB_sound (n : Nat) : isTermCodeB n = true → ∃ t, encodeTerm t = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h
    rw [isTermCodeB] at h
    by_cases hn : n = 0
    · simp [hn] at h
    have hlt := uncpair_lt n hn
    simp only [hn, ↓reduceDIte, Bool.and_eq_true, codeEqB_iff] at h
    obtain ⟨hc, h⟩ := h
    generalize hp : uncpair (n - 1) = p at hc h hlt
    obtain ⟨tag, pay⟩ := p
    simp only at hc h hlt
    split at h
    · exact ⟨Term.zero, by rw [codeEqB_iff] at h; rw [← hc, h]; rfl⟩
    · obtain ⟨t, ht⟩ := ih pay hlt.2 h
      exact ⟨Term.succ t, by rw [← hc, ← ht]; rfl⟩
    · by_cases hz : pay = 0
      · simp [hz] at h
      have hq := uncpair_lt pay hz
      simp only [hz, ↓reduceDIte, Bool.and_eq_true, codeEqB_iff] at h
      obtain ⟨hqc, h1, h2⟩ := h
      generalize hqq : uncpair (pay - 1) = q at hqc h1 h2 hq
      obtain ⟨qa, qb⟩ := q
      simp only at hqc h1 h2 hq
      obtain ⟨s, hs⟩ := ih qa (Nat.lt_trans hq.1 hlt.2) h1
      obtain ⟨t, ht⟩ := ih qb (Nat.lt_trans hq.2 hlt.2) h2
      exact ⟨Term.add s t, by rw [← hc, ← hqc, ← hs, ← ht]; rfl⟩
    · by_cases hz : pay = 0
      · simp [hz] at h
      have hq := uncpair_lt pay hz
      simp only [hz, ↓reduceDIte, Bool.and_eq_true, codeEqB_iff] at h
      obtain ⟨hqc, h1, h2⟩ := h
      generalize hqq : uncpair (pay - 1) = q at hqc h1 h2 hq
      obtain ⟨qa, qb⟩ := q
      simp only at hqc h1 h2 hq
      obtain ⟨s, hs⟩ := ih qa (Nat.lt_trans hq.1 hlt.2) h1
      obtain ⟨t, ht⟩ := ih qb (Nat.lt_trans hq.2 hlt.2) h2
      exact ⟨Term.mul s t, by rw [← hc, ← hqc, ← hs, ← ht]; rfl⟩
    · exact ⟨Term.var pay, by rw [← hc]; rfl⟩
    · exact absurd h Bool.false_ne_true

/-- Every accepted number is the canonical code of a formula. -/
theorem isFormulaCodeB_sound (n : Nat) : isFormulaCodeB n = true → ∃ φ, encodeFormula φ = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h
    rw [isFormulaCodeB] at h
    by_cases hn : n = 0
    · simp [hn] at h
    have hlt := uncpair_lt n hn
    simp only [hn, ↓reduceDIte, Bool.and_eq_true, codeEqB_iff] at h
    obtain ⟨hc, h⟩ := h
    generalize hp : uncpair (n - 1) = p at hc h hlt
    obtain ⟨tag, pay⟩ := p
    simp only at hc h hlt
    split at h
    · by_cases hz : pay = 0
      · simp [hz] at h
      simp only [hz, ↓reduceDIte, Bool.and_eq_true, codeEqB_iff] at h
      obtain ⟨hqc, h1, h2⟩ := h
      generalize hqq : uncpair (pay - 1) = q at hqc h1 h2
      obtain ⟨qa, qb⟩ := q
      simp only at hqc h1 h2
      obtain ⟨s, hs⟩ := isTermCodeB_sound qa h1
      obtain ⟨t, ht⟩ := isTermCodeB_sound qb h2
      exact ⟨Formula.eq s t, by rw [← hc, ← hqc, ← hs, ← ht]; rfl⟩
    · obtain ⟨φ, hφ⟩ := ih pay hlt.2 h
      exact ⟨Formula.not φ, by rw [← hc, ← hφ]; rfl⟩
    · by_cases hz : pay = 0
      · simp [hz] at h
      have hq := uncpair_lt pay hz
      simp only [hz, ↓reduceDIte, Bool.and_eq_true, codeEqB_iff] at h
      obtain ⟨hqc, h1, h2⟩ := h
      generalize hqq : uncpair (pay - 1) = q at hqc h1 h2 hq
      obtain ⟨qa, qb⟩ := q
      simp only at hqc h1 h2 hq
      obtain ⟨φ, hφ⟩ := ih qa (Nat.lt_trans hq.1 hlt.2) h1
      obtain ⟨ψ, hψ⟩ := ih qb (Nat.lt_trans hq.2 hlt.2) h2
      exact ⟨Formula.imp φ ψ, by rw [← hc, ← hqc, ← hφ, ← hψ]; rfl⟩
    · by_cases hz : pay = 0
      · simp [hz] at h
      have hq := uncpair_lt pay hz
      simp only [hz, ↓reduceDIte, Bool.and_eq_true, codeEqB_iff] at h
      obtain ⟨hqc, h2⟩ := h
      generalize hqq : uncpair (pay - 1) = q at hqc h2 hq
      obtain ⟨qa, qb⟩ := q
      simp only at hqc h2 hq
      obtain ⟨φ, hφ⟩ := ih qb (Nat.lt_trans hq.2 hlt.2) h2
      exact ⟨Formula.all qa φ, by rw [← hc, ← hqc, ← hφ]; rfl⟩
    · exact absurd h Bool.false_ne_true

/-- Every accepted number is the canonical code of a proof tree. -/
theorem isProofCodeCB_sound (n : Nat) : isProofCodeCB n = true → ∃ P, encodeProof P = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h
    rw [isProofCodeCB] at h
    by_cases hn : n = 0
    · simp [hn] at h
    have hlt := uncpair_lt n hn
    simp only [hn, ↓reduceDIte, Bool.and_eq_true, codeEqB_iff] at h
    obtain ⟨hc, h⟩ := h
    generalize hp : uncpair (n - 1) = p at hc h hlt
    obtain ⟨tag, pay⟩ := p
    simp only at hc h hlt
    split at h
    · obtain ⟨φ, hφ⟩ := isFormulaCodeB_sound pay h
      exact ⟨ProofTree.ax φ, by rw [← hc, ← hφ]; rfl⟩
    · by_cases hz : pay = 0
      · simp [hz] at h
      have hq := uncpair_lt pay hz
      simp only [hz, ↓reduceDIte, Bool.and_eq_true, codeEqB_iff] at h
      obtain ⟨hqc, h1, h2⟩ := h
      generalize hqq : uncpair (pay - 1) = q at hqc h1 h2 hq
      obtain ⟨qa, qb⟩ := q
      simp only at hqc h1 h2 hq
      obtain ⟨P, hP⟩ := ih qa (Nat.lt_trans hq.1 hlt.2) h1
      obtain ⟨Q, hQ⟩ := ih qb (Nat.lt_trans hq.2 hlt.2) h2
      exact ⟨ProofTree.mp P Q, by rw [← hc, ← hqc, ← hP, ← hQ]; rfl⟩
    · by_cases hz : pay = 0
      · simp [hz] at h
      have hq := uncpair_lt pay hz
      simp only [hz, ↓reduceDIte, Bool.and_eq_true, codeEqB_iff] at h
      obtain ⟨hqc, h2⟩ := h
      generalize hqq : uncpair (pay - 1) = q at hqc h2 hq
      obtain ⟨qa, qb⟩ := q
      simp only at hqc h2 hq
      obtain ⟨P, hP⟩ := ih qb (Nat.lt_trans hq.2 hlt.2) h2
      exact ⟨ProofTree.gen qa P, by rw [← hc, ← hqc, ← hP]; rfl⟩
    · by_cases hz : pay = 0
      · simp [hz] at h
      have hq := uncpair_lt pay hz
      simp only [hz, ↓reduceDIte] at h
      generalize hqq : uncpair (pay - 1) = q at h hq
      obtain ⟨qa, qb⟩ := q
      simp only at h hq
      by_cases hz2 : qb = 0
      · simp [hz2] at h
      have hr := uncpair_lt qb hz2
      simp only [hz2, ↓reduceDIte, Bool.and_eq_true, codeEqB_iff] at h
      obtain ⟨hqc, hrc, h1, h2⟩ := h
      generalize hrr : uncpair (qb - 1) = r at hrc h1 h2 hr
      obtain ⟨ra, rb⟩ := r
      simp only at hrc h1 h2 hr
      obtain ⟨t, ht⟩ := isTermCodeB_sound ra h1
      obtain ⟨P, hP⟩ := ih rb (Nat.lt_trans hr.2 (Nat.lt_trans hq.2 hlt.2)) h2
      exact ⟨ProofTree.spec qa t P, by rw [← hc, ← hqc, ← hrc, ← ht, ← hP]; rfl⟩
    · exact absurd h Bool.false_ne_true

/-! ## Primitive recursion of the canonical recognizers -/

private theorem eqZeroP {α : Type} [Primcodable α] {f : α → Nat} (hf : Primrec f) :
    PrimrecPred (fun x => f x = 0) :=
  Primrec.eq.comp hf (Primrec.const 0)

private theorem natEqP {α : Type} [Primcodable α] {f g : α → Nat} (hf : Primrec f)
    (hg : Primrec g) : PrimrecPred (fun x => f x = g x) :=
  Primrec.eq.comp hf hg

private theorem boolTrueP {α : Type} [Primcodable α] {f : α → Bool} (hf : Primrec f) :
    PrimrecPred (fun x => f x = true) :=
  Primrec.eq.comp hf (Primrec.const true)

/-- Course-of-values step of `isTermCodeB`. -/
def termCodeStep (prev : List Bool) : Bool :=
  if prev.length = 0 then false
  else
    codeEqB (ccons (uncpair (prev.length - 1)).1 (uncpair (prev.length - 1)).2) prev.length &&
    (if (uncpair (prev.length - 1)).1 = 0 then codeEqB (uncpair (prev.length - 1)).2 0
    else if (uncpair (prev.length - 1)).1 = 1 then prevBoolGet prev (uncpair (prev.length - 1)).2
    else if (uncpair (prev.length - 1)).1 = 2 then
      (if (uncpair (prev.length - 1)).2 = 0 then false
      else codeEqB (ccons (uncpair ((uncpair (prev.length - 1)).2 - 1)).1
          (uncpair ((uncpair (prev.length - 1)).2 - 1)).2) (uncpair (prev.length - 1)).2 &&
        (prevBoolGet prev (uncpair ((uncpair (prev.length - 1)).2 - 1)).1 &&
          prevBoolGet prev (uncpair ((uncpair (prev.length - 1)).2 - 1)).2))
    else if (uncpair (prev.length - 1)).1 = 3 then
      (if (uncpair (prev.length - 1)).2 = 0 then false
      else codeEqB (ccons (uncpair ((uncpair (prev.length - 1)).2 - 1)).1
          (uncpair ((uncpair (prev.length - 1)).2 - 1)).2) (uncpair (prev.length - 1)).2 &&
        (prevBoolGet prev (uncpair ((uncpair (prev.length - 1)).2 - 1)).1 &&
          prevBoolGet prev (uncpair ((uncpair (prev.length - 1)).2 - 1)).2))
    else if (uncpair (prev.length - 1)).1 = 4 then true
    else false)

theorem termCodeStep_correct (n : Nat) :
    termCodeStep ((List.range n).map isTermCodeB) = isTermCodeB n := by
  cases n with
  | zero => simp [termCodeStep, isTermCodeB]
  | succ n =>
      have hnz : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have hpLt := uncpair_lt (n + 1) hnz
      rw [isTermCodeB]
      simp only [termCodeStep, List.length_map, List.length_range, Nat.succ_ne_zero, ↓reduceDIte,
        ↓reduceIte, Nat.add_sub_cancel]
      generalize hp : uncpair n = p at hpLt ⊢
      rcases p with ⟨tag, payload⟩
      have hpay : payload < n + 1 := by simpa [hp] using hpLt.2
      congr 1
      rcases tag with _ | tag
      · simp
      · rcases tag with _ | tag
        · simp [prevBoolGet_range_map hpay]
        · rcases tag with _ | tag
          · by_cases hz : payload = 0
            · simp [hz]
            · have hq := uncpair_lt payload hz
              generalize hqu : uncpair (payload - 1) = q at hq ⊢
              rcases q with ⟨qa, qb⟩
              have hqa : qa < n + 1 := Nat.lt_trans hq.1 hpay
              have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
              simp [hz, prevBoolGet_range_map hqa, prevBoolGet_range_map hqb]
          · rcases tag with _ | tag
            · by_cases hz : payload = 0
              · simp [hz]
              · have hq := uncpair_lt payload hz
                generalize hqu : uncpair (payload - 1) = q at hq ⊢
                rcases q with ⟨qa, qb⟩
                have hqa : qa < n + 1 := Nat.lt_trans hq.1 hpay
                have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
                simp [hz, prevBoolGet_range_map hqa, prevBoolGet_range_map hqb]
            · rcases tag with _ | tag
              · simp
              · simp

theorem termCodeStep_primrec : Primrec termCodeStep := by
  let X := List Bool
  have hprev : Primrec (fun xs : X => xs) := Primrec.id
  have hn : Primrec (fun xs : X => xs.length) := Primrec.list_length
  have hn1 : Primrec (fun xs : X => xs.length - 1) := Primrec.nat_sub.comp hn (Primrec.const 1)
  have hp : Primrec (fun xs : X => uncpair (xs.length - 1)) := uncpair_primrec.comp hn1
  have htag : Primrec (fun xs : X => (uncpair (xs.length - 1)).1) := Primrec.fst.comp hp
  have hpay : Primrec (fun xs : X => (uncpair (xs.length - 1)).2) := Primrec.snd.comp hp
  have hq : Primrec (fun xs : X => uncpair ((uncpair (xs.length - 1)).2 - 1)) :=
    uncpair_primrec.comp (Primrec.nat_sub.comp hpay (Primrec.const 1))
  have hqa : Primrec (fun xs : X => (uncpair ((uncpair (xs.length - 1)).2 - 1)).1) :=
    Primrec.fst.comp hq
  have hqb : Primrec (fun xs : X => (uncpair ((uncpair (xs.length - 1)).2 - 1)).2) :=
    Primrec.snd.comp hq
  have hcc : Primrec (fun xs : X =>
      codeEqB (ccons (uncpair (xs.length - 1)).1 (uncpair (xs.length - 1)).2) xs.length) :=
    codeEqB_primrec.comp (ccP htag hpay) hn
  have hcq : Primrec (fun xs : X =>
      codeEqB (ccons (uncpair ((uncpair (xs.length - 1)).2 - 1)).1
        (uncpair ((uncpair (xs.length - 1)).2 - 1)).2) (uncpair (xs.length - 1)).2) :=
    codeEqB_primrec.comp (ccP hqa hqb) hpay
  have hgetPay := prevBoolGet_primrec.comp hprev hpay
  have hgetA := prevBoolGet_primrec.comp hprev hqa
  have hgetB := prevBoolGet_primrec.comp hprev hqb
  have hbin : Primrec (fun xs : X =>
      codeEqB (ccons (uncpair ((uncpair (xs.length - 1)).2 - 1)).1
        (uncpair ((uncpair (xs.length - 1)).2 - 1)).2) (uncpair (xs.length - 1)).2 &&
      (prevBoolGet xs (uncpair ((uncpair (xs.length - 1)).2 - 1)).1 &&
        prevBoolGet xs (uncpair ((uncpair (xs.length - 1)).2 - 1)).2)) :=
    Primrec.and.comp hcq (Primrec.and.comp hgetA hgetB)
  have hfalse : Primrec (fun _ : X => false) := Primrec.const false
  have htrue : Primrec (fun _ : X => true) := Primrec.const true
  have heq0 := eqZeroP hn
  have hpay0 := eqZeroP hpay
  have htagEq (k : Nat) := natEqP htag (Primrec.const (α := X) k)
  have h0out : Primrec (fun xs : X => codeEqB (uncpair (xs.length - 1)).2 0) :=
    codeEqB_primrec.comp hpay (Primrec.const 0)
  have hcase2 := Primrec.ite hpay0 hfalse hbin
  have hcase3 := Primrec.ite hpay0 hfalse hbin
  have htags := Primrec.ite (htagEq 0) h0out
    (Primrec.ite (htagEq 1) hgetPay
      (Primrec.ite (htagEq 2) hcase2
        (Primrec.ite (htagEq 3) hcase3
          (Primrec.ite (htagEq 4) htrue hfalse))))
  exact (Primrec.ite heq0 hfalse (Primrec.and.comp hcc htags)).of_eq (fun xs => by rfl)

theorem isTermCodeB_primrec : Primrec isTermCodeB := by
  have hg₁ : Primrec (fun p : Bool × List Bool => some (termCodeStep p.2)) :=
    Primrec.option_some.comp (termCodeStep_primrec.comp Primrec.snd)
  have hg : Primrec₂ (fun _ : Bool => fun xs : List Bool => some (termCodeStep xs)) :=
    hg₁.to₂.of_eq (fun _ _ => rfl)
  have h₂ : Primrec₂ (fun _ : Bool => fun n => isTermCodeB n) := by
    apply Primrec.nat_strong_rec (fun _ : Bool => fun n => isTermCodeB n) hg
    intro _ n
    simp [termCodeStep_correct]
  exact h₂.comp (Primrec.const false) Primrec.id

/-- Course-of-values step of `isFormulaCodeB`. -/
def formulaCodeStep (prev : List Bool) : Bool :=
  if prev.length = 0 then false
  else
    codeEqB (ccons (uncpair (prev.length - 1)).1 (uncpair (prev.length - 1)).2) prev.length &&
    (if (uncpair (prev.length - 1)).1 = 0 then
      (if (uncpair (prev.length - 1)).2 = 0 then false
      else codeEqB (ccons (uncpair ((uncpair (prev.length - 1)).2 - 1)).1
          (uncpair ((uncpair (prev.length - 1)).2 - 1)).2) (uncpair (prev.length - 1)).2 &&
        (isTermCodeB (uncpair ((uncpair (prev.length - 1)).2 - 1)).1 &&
          isTermCodeB (uncpair ((uncpair (prev.length - 1)).2 - 1)).2))
    else if (uncpair (prev.length - 1)).1 = 1 then prevBoolGet prev (uncpair (prev.length - 1)).2
    else if (uncpair (prev.length - 1)).1 = 2 then
      (if (uncpair (prev.length - 1)).2 = 0 then false
      else codeEqB (ccons (uncpair ((uncpair (prev.length - 1)).2 - 1)).1
          (uncpair ((uncpair (prev.length - 1)).2 - 1)).2) (uncpair (prev.length - 1)).2 &&
        (prevBoolGet prev (uncpair ((uncpair (prev.length - 1)).2 - 1)).1 &&
          prevBoolGet prev (uncpair ((uncpair (prev.length - 1)).2 - 1)).2))
    else if (uncpair (prev.length - 1)).1 = 3 then
      (if (uncpair (prev.length - 1)).2 = 0 then false
      else codeEqB (ccons (uncpair ((uncpair (prev.length - 1)).2 - 1)).1
          (uncpair ((uncpair (prev.length - 1)).2 - 1)).2) (uncpair (prev.length - 1)).2 &&
        prevBoolGet prev (uncpair ((uncpair (prev.length - 1)).2 - 1)).2)
    else false)

theorem formulaCodeStep_correct (n : Nat) :
    formulaCodeStep ((List.range n).map isFormulaCodeB) = isFormulaCodeB n := by
  cases n with
  | zero => simp [formulaCodeStep, isFormulaCodeB]
  | succ n =>
      have hnz : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have hpLt := uncpair_lt (n + 1) hnz
      rw [isFormulaCodeB]
      simp only [formulaCodeStep, List.length_map, List.length_range, Nat.succ_ne_zero,
        ↓reduceDIte, ↓reduceIte, Nat.add_sub_cancel]
      generalize hp : uncpair n = p at hpLt ⊢
      rcases p with ⟨tag, payload⟩
      have hpay : payload < n + 1 := by simpa [hp] using hpLt.2
      congr 1
      rcases tag with _ | tag
      · by_cases hz : payload = 0
        · simp [hz]
        · simp [hz]
      · rcases tag with _ | tag
        · simp [prevBoolGet_range_map hpay]
        · rcases tag with _ | tag
          · by_cases hz : payload = 0
            · simp [hz]
            · have hq := uncpair_lt payload hz
              generalize hqu : uncpair (payload - 1) = q at hq ⊢
              rcases q with ⟨qa, qb⟩
              have hqa : qa < n + 1 := Nat.lt_trans hq.1 hpay
              have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
              simp [hz, prevBoolGet_range_map hqa, prevBoolGet_range_map hqb]
          · rcases tag with _ | tag
            · by_cases hz : payload = 0
              · simp [hz]
              · have hq := uncpair_lt payload hz
                generalize hqu : uncpair (payload - 1) = q at hq ⊢
                rcases q with ⟨qa, qb⟩
                have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
                simp [hz, prevBoolGet_range_map hqb]
            · simp

theorem formulaCodeStep_primrec : Primrec formulaCodeStep := by
  let X := List Bool
  have hprev : Primrec (fun xs : X => xs) := Primrec.id
  have hn : Primrec (fun xs : X => xs.length) := Primrec.list_length
  have hn1 : Primrec (fun xs : X => xs.length - 1) := Primrec.nat_sub.comp hn (Primrec.const 1)
  have hp : Primrec (fun xs : X => uncpair (xs.length - 1)) := uncpair_primrec.comp hn1
  have htag : Primrec (fun xs : X => (uncpair (xs.length - 1)).1) := Primrec.fst.comp hp
  have hpay : Primrec (fun xs : X => (uncpair (xs.length - 1)).2) := Primrec.snd.comp hp
  have hq : Primrec (fun xs : X => uncpair ((uncpair (xs.length - 1)).2 - 1)) :=
    uncpair_primrec.comp (Primrec.nat_sub.comp hpay (Primrec.const 1))
  have hqa : Primrec (fun xs : X => (uncpair ((uncpair (xs.length - 1)).2 - 1)).1) :=
    Primrec.fst.comp hq
  have hqb : Primrec (fun xs : X => (uncpair ((uncpair (xs.length - 1)).2 - 1)).2) :=
    Primrec.snd.comp hq
  have hcc : Primrec (fun xs : X =>
      codeEqB (ccons (uncpair (xs.length - 1)).1 (uncpair (xs.length - 1)).2) xs.length) :=
    codeEqB_primrec.comp (ccP htag hpay) hn
  have hcq : Primrec (fun xs : X =>
      codeEqB (ccons (uncpair ((uncpair (xs.length - 1)).2 - 1)).1
        (uncpair ((uncpair (xs.length - 1)).2 - 1)).2) (uncpair (xs.length - 1)).2) :=
    codeEqB_primrec.comp (ccP hqa hqb) hpay
  have hgetPay := prevBoolGet_primrec.comp hprev hpay
  have hgetA := prevBoolGet_primrec.comp hprev hqa
  have hgetB := prevBoolGet_primrec.comp hprev hqb
  have htA := isTermCodeB_primrec.comp hqa
  have htB := isTermCodeB_primrec.comp hqb
  have heqcase := Primrec.and.comp hcq (Primrec.and.comp htA htB)
  have hbin := Primrec.and.comp hcq (Primrec.and.comp hgetA hgetB)
  have hall := Primrec.and.comp hcq hgetB
  have hfalse : Primrec (fun _ : X => false) := Primrec.const false
  have heq0 := eqZeroP hn
  have hpay0 := eqZeroP hpay
  have htagEq (k : Nat) := natEqP htag (Primrec.const (α := X) k)
  have htags := Primrec.ite (htagEq 0) (Primrec.ite hpay0 hfalse heqcase)
    (Primrec.ite (htagEq 1) hgetPay
      (Primrec.ite (htagEq 2) (Primrec.ite hpay0 hfalse hbin)
        (Primrec.ite (htagEq 3) (Primrec.ite hpay0 hfalse hall) hfalse)))
  exact (Primrec.ite heq0 hfalse (Primrec.and.comp hcc htags)).of_eq (fun xs => by rfl)

theorem isFormulaCodeB_primrec : Primrec isFormulaCodeB := by
  have hg₁ : Primrec (fun p : Bool × List Bool => some (formulaCodeStep p.2)) :=
    Primrec.option_some.comp (formulaCodeStep_primrec.comp Primrec.snd)
  have hg : Primrec₂ (fun _ : Bool => fun xs : List Bool => some (formulaCodeStep xs)) :=
    hg₁.to₂.of_eq (fun _ _ => rfl)
  have h₂ : Primrec₂ (fun _ : Bool => fun n => isFormulaCodeB n) := by
    apply Primrec.nat_strong_rec (fun _ : Bool => fun n => isFormulaCodeB n) hg
    intro _ n
    simp [formulaCodeStep_correct]
  exact h₂.comp (Primrec.const false) Primrec.id

/-- Course-of-values step of `isProofCodeCB`. -/
def proofCodeStep (prev : List Bool) : Bool :=
  if prev.length = 0 then false
  else
    codeEqB (ccons (uncpair (prev.length - 1)).1 (uncpair (prev.length - 1)).2) prev.length &&
    (if (uncpair (prev.length - 1)).1 = 0 then isFormulaCodeB (uncpair (prev.length - 1)).2
    else if (uncpair (prev.length - 1)).1 = 1 then
      (if (uncpair (prev.length - 1)).2 = 0 then false
      else codeEqB (ccons (uncpair ((uncpair (prev.length - 1)).2 - 1)).1
          (uncpair ((uncpair (prev.length - 1)).2 - 1)).2) (uncpair (prev.length - 1)).2 &&
        (prevBoolGet prev (uncpair ((uncpair (prev.length - 1)).2 - 1)).1 &&
          prevBoolGet prev (uncpair ((uncpair (prev.length - 1)).2 - 1)).2))
    else if (uncpair (prev.length - 1)).1 = 2 then
      (if (uncpair (prev.length - 1)).2 = 0 then false
      else codeEqB (ccons (uncpair ((uncpair (prev.length - 1)).2 - 1)).1
          (uncpair ((uncpair (prev.length - 1)).2 - 1)).2) (uncpair (prev.length - 1)).2 &&
        prevBoolGet prev (uncpair ((uncpair (prev.length - 1)).2 - 1)).2)
    else if (uncpair (prev.length - 1)).1 = 3 then
      (if (uncpair (prev.length - 1)).2 = 0 then false
      else if (uncpair ((uncpair (prev.length - 1)).2 - 1)).2 = 0 then false
      else codeEqB (ccons (uncpair ((uncpair (prev.length - 1)).2 - 1)).1
          (uncpair ((uncpair (prev.length - 1)).2 - 1)).2) (uncpair (prev.length - 1)).2 &&
        (codeEqB (ccons (uncpair ((uncpair ((uncpair (prev.length - 1)).2 - 1)).2 - 1)).1
            (uncpair ((uncpair ((uncpair (prev.length - 1)).2 - 1)).2 - 1)).2)
            (uncpair ((uncpair (prev.length - 1)).2 - 1)).2 &&
          (isTermCodeB (uncpair ((uncpair ((uncpair (prev.length - 1)).2 - 1)).2 - 1)).1 &&
            prevBoolGet prev (uncpair ((uncpair ((uncpair (prev.length - 1)).2 - 1)).2 - 1)).2)))
    else false)

theorem proofCodeStep_correct (n : Nat) :
    proofCodeStep ((List.range n).map isProofCodeCB) = isProofCodeCB n := by
  cases n with
  | zero => simp [proofCodeStep, isProofCodeCB]
  | succ n =>
      have hnz : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have hpLt := uncpair_lt (n + 1) hnz
      rw [isProofCodeCB]
      simp only [proofCodeStep, List.length_map, List.length_range, Nat.succ_ne_zero,
        ↓reduceDIte, ↓reduceIte, Nat.add_sub_cancel]
      generalize hp : uncpair n = p at hpLt ⊢
      rcases p with ⟨tag, payload⟩
      have hpay : payload < n + 1 := by simpa [hp] using hpLt.2
      congr 1
      rcases tag with _ | tag
      · simp
      · rcases tag with _ | tag
        · by_cases hz : payload = 0
          · simp [hz]
          · have hq := uncpair_lt payload hz
            generalize hqu : uncpair (payload - 1) = q at hq ⊢
            rcases q with ⟨qa, qb⟩
            have hqa : qa < n + 1 := Nat.lt_trans hq.1 hpay
            have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
            simp [hz, prevBoolGet_range_map hqa, prevBoolGet_range_map hqb]
        · rcases tag with _ | tag
          · by_cases hz : payload = 0
            · simp [hz]
            · have hq := uncpair_lt payload hz
              generalize hqu : uncpair (payload - 1) = q at hq ⊢
              rcases q with ⟨qa, qb⟩
              have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
              simp [hz, prevBoolGet_range_map hqb]
          · rcases tag with _ | tag
            · by_cases hz : payload = 0
              · simp [hz]
              · have hq := uncpair_lt payload hz
                generalize hqu : uncpair (payload - 1) = q at hq ⊢
                rcases q with ⟨qa, qb⟩
                have hqbPay : qb < n + 1 := Nat.lt_trans hq.2 hpay
                by_cases hqb0 : qb = 0
                · simp [hz, hqb0]
                · have hr := uncpair_lt qb hqb0
                  generalize hru : uncpair (qb - 1) = r at hr ⊢
                  rcases r with ⟨ra, rb⟩
                  have hrb : rb < n + 1 := Nat.lt_trans hr.2 hqbPay
                  simp [hz, hqb0, prevBoolGet_range_map hrb]
            · simp

theorem proofCodeStep_primrec : Primrec proofCodeStep := by
  let X := List Bool
  have hprev : Primrec (fun xs : X => xs) := Primrec.id
  have hn : Primrec (fun xs : X => xs.length) := Primrec.list_length
  have hn1 : Primrec (fun xs : X => xs.length - 1) := Primrec.nat_sub.comp hn (Primrec.const 1)
  have hp : Primrec (fun xs : X => uncpair (xs.length - 1)) := uncpair_primrec.comp hn1
  have htag : Primrec (fun xs : X => (uncpair (xs.length - 1)).1) := Primrec.fst.comp hp
  have hpay : Primrec (fun xs : X => (uncpair (xs.length - 1)).2) := Primrec.snd.comp hp
  have hq : Primrec (fun xs : X => uncpair ((uncpair (xs.length - 1)).2 - 1)) :=
    uncpair_primrec.comp (Primrec.nat_sub.comp hpay (Primrec.const 1))
  have hqa : Primrec (fun xs : X => (uncpair ((uncpair (xs.length - 1)).2 - 1)).1) :=
    Primrec.fst.comp hq
  have hqb : Primrec (fun xs : X => (uncpair ((uncpair (xs.length - 1)).2 - 1)).2) :=
    Primrec.snd.comp hq
  have hr : Primrec (fun xs : X =>
      uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)) :=
    uncpair_primrec.comp (Primrec.nat_sub.comp hqb (Primrec.const 1))
  have hra : Primrec (fun xs : X =>
      (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).1) := Primrec.fst.comp hr
  have hrb : Primrec (fun xs : X =>
      (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2) := Primrec.snd.comp hr
  have hcc : Primrec (fun xs : X =>
      codeEqB (ccons (uncpair (xs.length - 1)).1 (uncpair (xs.length - 1)).2) xs.length) :=
    codeEqB_primrec.comp (ccP htag hpay) hn
  have hcq : Primrec (fun xs : X =>
      codeEqB (ccons (uncpair ((uncpair (xs.length - 1)).2 - 1)).1
        (uncpair ((uncpair (xs.length - 1)).2 - 1)).2) (uncpair (xs.length - 1)).2) :=
    codeEqB_primrec.comp (ccP hqa hqb) hpay
  have hcr : Primrec (fun xs : X =>
      codeEqB (ccons (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).1
        (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2)
        (uncpair ((uncpair (xs.length - 1)).2 - 1)).2) :=
    codeEqB_primrec.comp (ccP hra hrb) hqb
  have hgetA := prevBoolGet_primrec.comp hprev hqa
  have hgetB := prevBoolGet_primrec.comp hprev hqb
  have hgetR := prevBoolGet_primrec.comp hprev hrb
  have hfPay := isFormulaCodeB_primrec.comp hpay
  have htR := isTermCodeB_primrec.comp hra
  have hmp := Primrec.and.comp hcq (Primrec.and.comp hgetA hgetB)
  have hgen := Primrec.and.comp hcq hgetB
  have hspec := Primrec.and.comp hcq (Primrec.and.comp hcr (Primrec.and.comp htR hgetR))
  have hfalse : Primrec (fun _ : X => false) := Primrec.const false
  have heq0 := eqZeroP hn
  have hpay0 := eqZeroP hpay
  have hqb0 := eqZeroP hqb
  have htagEq (k : Nat) := natEqP htag (Primrec.const (α := X) k)
  have htags := Primrec.ite (htagEq 0) hfPay
    (Primrec.ite (htagEq 1) (Primrec.ite hpay0 hfalse hmp)
      (Primrec.ite (htagEq 2) (Primrec.ite hpay0 hfalse hgen)
        (Primrec.ite (htagEq 3) (Primrec.ite hpay0 hfalse (Primrec.ite hqb0 hfalse hspec))
          hfalse)))
  exact (Primrec.ite heq0 hfalse (Primrec.and.comp hcc htags)).of_eq (fun xs => by rfl)

theorem isProofCodeCB_primrec : Primrec isProofCodeCB := by
  have hg₁ : Primrec (fun p : Bool × List Bool => some (proofCodeStep p.2)) :=
    Primrec.option_some.comp (proofCodeStep_primrec.comp Primrec.snd)
  have hg : Primrec₂ (fun _ : Bool => fun xs : List Bool => some (proofCodeStep xs)) :=
    hg₁.to₂.of_eq (fun _ _ => rfl)
  have h₂ : Primrec₂ (fun _ : Bool => fun n => isProofCodeCB n) := by
    apply Primrec.nat_strong_rec (fun _ : Bool => fun n => isProofCodeCB n) hg
    intro _ n
    simp [proofCodeStep_correct]
  exact h₂.comp (Primrec.const false) Primrec.id

/-! ## The numeric checker of `T_E` -/

/-- Encode the result of `checkE`, using `0` for rejection. -/
def checkResultCodeE (p : ProofTree) : Nat :=
  match checkE p with
  | none => 0
  | some φ => encodeFormula φ

set_option linter.unusedVariables false in
/-- Numeric proof-tree checker of `T_E`: the numeric checker of `T_0` with the equality schemes. -/
def checkProofCodeE (n : Nat) : Nat :=
  if h : n = 0 then 0
  else
    let p := uncpair (n - 1)
    match p.1 with
    | 0 => if isAxiomCodeEB p.2 then p.2 else 0
    | 1 =>
      if hp : p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        let fp := checkProofCodeE q.1
        let fq := checkProofCodeE q.2
        if fp = 0 then 0
        else if fq = 0 then 0
        else if codeEqB (codeTag fp) 2 && codeEqB (codeLeft fp) fq then
          codeRight fp
        else 0
    | 2 =>
      if hp : p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        let fp := checkProofCodeE q.2
        if fp = 0 then 0 else ccons 3 (ccons q.1 fp)
    | 3 =>
      if hp : p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        if hq : q.2 = 0 then 0
        else
          let r := uncpair (q.2 - 1)
          let fp := checkProofCodeE r.2
          if fp = 0 then 0
          else if codeEqB (codeTag fp) 3 &&
              codeEqB q.1 (codeLeft fp) && isClosedTermCodeB r.1 then
            substFormAtCode q.1 r.1 (codeRight fp)
          else 0
    | _ => 0
termination_by n
decreasing_by
  · exact Nat.lt_trans (uncpair_lt p.2 hp).1 (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt q.2 hq).2
      (Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2)

/-- On canonical proof codes the numeric checker computes `checkE`. -/
theorem checkProofCodeE_encode (p : ProofTree) :
    checkProofCodeE (encodeProof p) = checkResultCodeE p := by
  induction p with
  | ax φ =>
      by_cases hax : isAxiomE φ = true
      · simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
          uncpair_pred_ccons, isAxiomCodeEB_encode, hax]
      · simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
          uncpair_pred_ccons, isAxiomCodeEB_encode, hax]
  | mp p q ihp ihq =>
      cases hp : checkE p with
      | none =>
          have ihp0 : checkProofCodeE (encodeProof p) = 0 := by
            simpa [checkResultCodeE, hp] using ihp
          simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
            uncpair_pred_ccons, hp, ihp0]
      | some φ =>
          cases hq : checkE q with
          | none =>
              have ihq0 : checkProofCodeE (encodeProof q) = 0 := by
                simpa [checkResultCodeE, hq] using ihq
              have ihpφ : checkProofCodeE (encodeProof p) = encodeFormula φ := by
                simpa [checkResultCodeE, hp] using ihp
              simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
                uncpair_pred_ccons, hp, hq, ihpφ, ihq0, encodeFormula_ne_zero]
          | some ψ =>
              have ihpφ : checkProofCodeE (encodeProof p) = encodeFormula φ := by
                simpa [checkResultCodeE, hp] using ihp
              have ihqψ : checkProofCodeE (encodeProof q) = encodeFormula ψ := by
                simpa [checkResultCodeE, hq] using ihq
              cases φ with
              | imp a b =>
                  by_cases hab : a = ψ
                  · subst ψ
                    simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
                      uncpair_pred_ccons, hp, hq, ihpφ, ihqψ, encodeFormula_ne_zero, codeEqB]
                  · have hcode : encodeFormula a ≠ encodeFormula ψ :=
                      fun he => hab (encodeFormula_injective he)
                    simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
                      uncpair_pred_ccons, hp, hq, ihpφ, ihqψ, encodeFormula_ne_zero,
                      codeEqB, hab, hcode]
              | eq s t =>
                  simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
                    uncpair_pred_ccons, hp, hq, ihpφ, ihqψ, encodeFormula_ne_zero, codeEqB]
              | not a =>
                  simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
                    uncpair_pred_ccons, hp, hq, ihpφ, ihqψ, encodeFormula_ne_zero, codeEqB]
              | all x a =>
                  simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
                    uncpair_pred_ccons, hp, hq, ihpφ, ihqψ, encodeFormula_ne_zero, codeEqB]
  | gen x p ih =>
      cases hp : checkE p with
      | none =>
          have ih0 : checkProofCodeE (encodeProof p) = 0 := by
            simpa [checkResultCodeE, hp] using ih
          simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
            uncpair_pred_ccons, hp, ih0]
      | some φ =>
          have ihφ : checkProofCodeE (encodeProof p) = encodeFormula φ := by
            simpa [checkResultCodeE, hp] using ih
          simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
            uncpair_pred_ccons, hp, ihφ, encodeFormula_ne_zero, encodeFormula]
  | spec x t p ih =>
      cases hp : checkE p with
      | none =>
          have ih0 : checkProofCodeE (encodeProof p) = 0 := by
            simpa [checkResultCodeE, hp] using ih
          simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
            uncpair_pred_ccons, hp, ih0]
      | some φ =>
          have ihφ : checkProofCodeE (encodeProof p) = encodeFormula φ := by
            simpa [checkResultCodeE, hp] using ih
          cases φ with
          | all y a =>
              by_cases hxy : x = y
              · subst y
                cases hc : isClosedTerm t with
                | false =>
                    simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
                      uncpair_pred_ccons, hp, ihφ, encodeFormula_ne_zero, codeEqB,
                      isClosedTermCodeB_encode, hc]
                | true =>
                    simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
                      uncpair_pred_ccons, hp, ihφ, encodeFormula_ne_zero, codeEqB,
                      isClosedTermCodeB_encode, hc, substFormAtCode_encode]
              · simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
                  uncpair_pred_ccons, hp, ihφ, encodeFormula_ne_zero, codeEqB,
                  isClosedTermCodeB_encode, hxy]
          | eq s u =>
              simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
                uncpair_pred_ccons, hp, ihφ, encodeFormula_ne_zero, codeEqB]
          | not a =>
              simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
                uncpair_pred_ccons, hp, ihφ, encodeFormula_ne_zero, codeEqB]
          | imp a b =>
              simp [checkProofCodeE, checkResultCodeE, encodeProof, checkE, ccons_ne_zero,
                uncpair_pred_ccons, hp, ihφ, encodeFormula_ne_zero, codeEqB]

/-- Course-of-values step of `checkProofCodeE`. -/
def checkProofCodeEStep (prev : List Nat) : Nat :=
  let n := prev.length
  if n = 0 then 0
  else
    let p := uncpair (n - 1)
    if p.1 = 0 then
      if isAxiomCodeEB p.2 then p.2 else 0
    else if p.1 = 1 then
      if p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        let fp := prevGet prev q.1
        let fq := prevGet prev q.2
        if fp = 0 then 0
        else if fq = 0 then 0
        else if codeTag fp = 2 ∧ codeLeft fp = fq then codeRight fp else 0
    else if p.1 = 2 then
      if p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        let fp := prevGet prev q.2
        if fp = 0 then 0 else ccons 3 (ccons q.1 fp)
    else if p.1 = 3 then
      if p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        if q.2 = 0 then 0
        else
          let r := uncpair (q.2 - 1)
          let fp := prevGet prev r.2
          if fp = 0 then 0
          else if (codeTag fp = 3 ∧ q.1 = codeLeft fp) ∧ isClosedTermCodeB r.1 = true then
            substFormAtCode q.1 r.1 (codeRight fp)
          else 0
    else 0

theorem checkProofCodeEStep_correct (n : Nat) :
    checkProofCodeEStep ((List.range n).map checkProofCodeE) = checkProofCodeE n := by
  cases n with
  | zero => simp [checkProofCodeEStep, checkProofCodeE]
  | succ n =>
      have hnz : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have hpLt := uncpair_lt (n + 1) hnz
      rw [checkProofCodeE]
      simp only [checkProofCodeEStep, List.length_map, List.length_range,
        Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
      generalize hp : uncpair n = p at hpLt ⊢
      rcases p with ⟨tag, payload⟩
      have hpay : payload < n + 1 := by simpa [hp] using hpLt.2
      rcases tag with _ | tag
      · simp
      · rcases tag with _ | tag
        · by_cases hz : payload = 0
          · simp [hz]
          · have hq := uncpair_lt payload hz
            generalize hqu : uncpair (payload - 1) = q at hq ⊢
            rcases q with ⟨qa, qb⟩
            have hqa : qa < n + 1 := Nat.lt_trans hq.1 hpay
            have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
            simp [hz, prevGet_range_map hqa, prevGet_range_map hqb, codeEqB]
        · rcases tag with _ | tag
          · by_cases hz : payload = 0
            · simp [hz]
            · have hq := uncpair_lt payload hz
              generalize hqu : uncpair (payload - 1) = q at hq ⊢
              rcases q with ⟨qa, qb⟩
              have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
              simp [hz, prevGet_range_map hqb]
          · rcases tag with _ | tag
            · by_cases hz : payload = 0
              · simp [hz]
              · have hq := uncpair_lt payload hz
                generalize hqu : uncpair (payload - 1) = q at hq ⊢
                rcases q with ⟨qa, qb⟩
                have hqbPay : qb < n + 1 := Nat.lt_trans hq.2 hpay
                by_cases hqb0 : qb = 0
                · simp [hz, hqb0]
                · have hr := uncpair_lt qb hqb0
                  generalize hru : uncpair (qb - 1) = r at hr ⊢
                  rcases r with ⟨ra, rb⟩
                  have hrb : rb < n + 1 := Nat.lt_trans hr.2 hqbPay
                  simp [hz, hqb0, prevGet_range_map hrb, codeEqB]
            · cases tag <;> simp

theorem checkProofCodeEStep_primrec : Primrec checkProofCodeEStep := by
  let X := List Nat
  have hprev : Primrec (fun xs : X => xs) := Primrec.id
  have hn : Primrec (fun xs : X => xs.length) := Primrec.list_length
  have hn1 : Primrec (fun xs : X => xs.length - 1) :=
    Primrec.nat_sub.comp hn (Primrec.const 1)
  have hp : Primrec (fun xs : X => uncpair (xs.length - 1)) := uncpair_primrec.comp hn1
  have htag : Primrec (fun xs : X => (uncpair (xs.length - 1)).1) := Primrec.fst.comp hp
  have hpay : Primrec (fun xs : X => (uncpair (xs.length - 1)).2) := Primrec.snd.comp hp
  have hpayPred : Primrec (fun xs : X => (uncpair (xs.length - 1)).2 - 1) :=
    Primrec.nat_sub.comp hpay (Primrec.const 1)
  have hq : Primrec (fun xs : X => uncpair ((uncpair (xs.length - 1)).2 - 1)) :=
    uncpair_primrec.comp hpayPred
  have hqa : Primrec (fun xs : X => (uncpair ((uncpair (xs.length - 1)).2 - 1)).1) :=
    Primrec.fst.comp hq
  have hqb : Primrec (fun xs : X => (uncpair ((uncpair (xs.length - 1)).2 - 1)).2) :=
    Primrec.snd.comp hq
  have hfp : Primrec (fun xs : X => prevGet xs
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).1) := prevGet_primrec.comp hprev hqa
  have hfq : Primrec (fun xs : X => prevGet xs
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).2) := prevGet_primrec.comp hprev hqb
  have hqbPred : Primrec (fun xs : X =>
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1) :=
    Primrec.nat_sub.comp hqb (Primrec.const 1)
  have hr : Primrec (fun xs : X =>
      uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)) :=
    uncpair_primrec.comp hqbPred
  have hra : Primrec (fun xs : X =>
      (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).1) := Primrec.fst.comp hr
  have hrb : Primrec (fun xs : X =>
      (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2) := Primrec.snd.comp hr
  have hfpr : Primrec (fun xs : X => prevGet xs
      (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2) :=
    prevGet_primrec.comp hprev hrb
  have hzero : Primrec (fun _ : X => 0) := Primrec.const 0
  have heq0 : PrimrecPred (fun xs : X => xs.length = 0) := eqZeroP hn
  have hpay0 : PrimrecPred (fun xs : X => (uncpair (xs.length - 1)).2 = 0) := eqZeroP hpay
  have hqb0 : PrimrecPred (fun xs : X =>
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).2 = 0) := eqZeroP hqb
  have hfp0 : PrimrecPred (fun xs : X => prevGet xs
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).1 = 0) := eqZeroP hfp
  have hfq0 : PrimrecPred (fun xs : X => prevGet xs
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).2 = 0) := eqZeroP hfq
  have hfpr0 : PrimrecPred (fun xs : X => prevGet xs
      (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2 = 0) := eqZeroP hfpr
  have htagEq (k : Nat) : PrimrecPred (fun xs : X => (uncpair (xs.length - 1)).1 = k) :=
    natEqP htag (Primrec.const k)
  have hax : Primrec (fun xs : X => isAxiomCodeEB (uncpair (xs.length - 1)).2) :=
    isAxiomCodeEB_primrec.comp hpay
  have haxTrue : PrimrecPred (fun xs : X => isAxiomCodeEB (uncpair (xs.length - 1)).2 = true) :=
    boolTrueP hax
  have hcase0 : Primrec (fun xs : X =>
      if isAxiomCodeEB (uncpair (xs.length - 1)).2 then (uncpair (xs.length - 1)).2 else 0) :=
    (Primrec.ite haxTrue hpay hzero).of_eq (fun xs => by
      cases h : isAxiomCodeEB (uncpair (xs.length - 1)).2 <;> simp)
  have hfpTag : Primrec (fun xs : X => codeTag (prevGet xs
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).1)) := codeTag_primrec.comp hfp
  have hfpLeft : Primrec (fun xs : X => codeLeft (prevGet xs
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).1)) := codeLeft_primrec.comp hfp
  have hfpRight : Primrec (fun xs : X => codeRight (prevGet xs
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).1)) := codeRight_primrec.comp hfp
  have hmpGood : PrimrecPred (fun xs : X =>
      codeTag (prevGet xs (uncpair ((uncpair (xs.length - 1)).2 - 1)).1) = 2 ∧
      codeLeft (prevGet xs (uncpair ((uncpair (xs.length - 1)).2 - 1)).1) =
        prevGet xs (uncpair ((uncpair (xs.length - 1)).2 - 1)).2) :=
    PrimrecPred.and (natEqP hfpTag (Primrec.const 2)) (natEqP hfpLeft hfq)
  have hcase1 := Primrec.ite hfp0 hzero
    (Primrec.ite hfq0 hzero (Primrec.ite hmpGood hfpRight hzero))
  have hgenOut : Primrec (fun xs : X => ccons 3 (ccons
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).1
      (prevGet xs (uncpair ((uncpair (xs.length - 1)).2 - 1)).2))) :=
    ccP (Primrec.const 3) (ccP hqa hfq)
  have hcase2 := Primrec.ite hfq0 hzero hgenOut
  have hfprTag : Primrec (fun xs : X => codeTag (prevGet xs
      (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2)) :=
    codeTag_primrec.comp hfpr
  have hfprLeft : Primrec (fun xs : X => codeLeft (prevGet xs
      (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2)) :=
    codeLeft_primrec.comp hfpr
  have hfprRight : Primrec (fun xs : X => codeRight (prevGet xs
      (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2)) :=
    codeRight_primrec.comp hfpr
  have hclosed : Primrec (fun xs : X => isClosedTermCodeB
      (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).1) :=
    isClosedTermCodeB_primrec.comp hra
  have hspecGood : PrimrecPred (fun xs : X =>
      (codeTag (prevGet xs (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2) = 3 ∧
       (uncpair ((uncpair (xs.length - 1)).2 - 1)).1 =
        codeLeft (prevGet xs (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2)) ∧
      isClosedTermCodeB (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).1 = true) :=
    PrimrecPred.and (PrimrecPred.and (natEqP hfprTag (Primrec.const 3)) (natEqP hqa hfprLeft))
      (boolTrueP hclosed)
  have hxu : Primrec (fun xs : X =>
      ((uncpair ((uncpair (xs.length - 1)).2 - 1)).1,
       (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).1)) := hqa.pair hra
  have hspecOut : Primrec (fun xs : X => substFormAtCode
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).1
      (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).1
      (codeRight (prevGet xs
        (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2))) :=
    substFormAtCode_primrec.comp hxu hfprRight
  have hcase3core := Primrec.ite hqb0 hzero
    (Primrec.ite hfpr0 hzero (Primrec.ite hspecGood hspecOut hzero))
  have htags := Primrec.ite (htagEq 0) hcase0
    (Primrec.ite (htagEq 1) (Primrec.ite hpay0 hzero hcase1)
      (Primrec.ite (htagEq 2) (Primrec.ite hpay0 hzero hcase2)
        (Primrec.ite (htagEq 3) (Primrec.ite hpay0 hzero hcase3core) hzero)))
  exact (Primrec.ite heq0 hzero htags).of_eq (fun xs => by rfl)

theorem checkProofCodeE_primrec : Primrec checkProofCodeE := by
  have hg₁ : Primrec (fun p : Bool × List Nat => some (checkProofCodeEStep p.2)) :=
    Primrec.option_some.comp (checkProofCodeEStep_primrec.comp Primrec.snd)
  have hg : Primrec₂ (fun _ : Bool => fun xs : List Nat => some (checkProofCodeEStep xs)) :=
    hg₁.to₂.of_eq (fun _ _ => rfl)
  have h₂ : Primrec₂ (fun _ : Bool => fun n => checkProofCodeE n) := by
    apply Primrec.nat_strong_rec (fun _ : Bool => fun n => checkProofCodeE n) hg
    intro _ n
    simp [checkProofCodeEStep_correct]
  exact h₂.comp (Primrec.const false) Primrec.id

/-! ## The proof relation of `T_E` -/

/-- `n` is the canonical code of a `T_E` proof with conclusion code `m`. -/
def proofRelE (n m : Nat) : Bool :=
  isProofCodeCB n && (codeEqB (checkProofCodeE n) m && !(codeEqB m 0))

/-- **The proof relation of `T_E` is primitive recursive.** -/
theorem proofRelE_primrec : Primrec₂ proofRelE := by
  have hc : Primrec₂ (fun n _m : Nat => isProofCodeCB n) := isProofCodeCB_primrec.comp₂ Primrec₂.left
  have hl : Primrec₂ (fun n m : Nat => codeEqB (checkProofCodeE n) m) :=
    codeEqB_primrec.comp₂ (checkProofCodeE_primrec.comp₂ Primrec₂.left) Primrec₂.right
  have hz : Primrec₂ (fun _n m : Nat => !(codeEqB m 0)) :=
    Primrec.not.comp₂ (codeEqB_primrec.comp₂ Primrec₂.right (Primrec₂.const 0))
  exact Primrec.and.comp₂ hc (Primrec.and.comp₂ hl hz)

/-- **The proof relation of `T_E` defines `T_E`-provability.** -/
theorem exists_proofRelE_iff (φ : Formula) :
    (∃ n, proofRelE n (encodeFormula φ) = true) ↔ ProvableE φ := by
  constructor
  · rintro ⟨n, hn⟩
    simp only [proofRelE, Bool.and_eq_true, codeEqB_iff, Bool.not_eq_true'] at hn
    obtain ⟨hcan, hres, _⟩ := hn
    obtain ⟨P, rfl⟩ := isProofCodeCB_sound n hcan
    rw [checkProofCodeE_encode] at hres
    cases hP : checkE P with
    | none =>
        simp [checkResultCodeE, hP] at hres
        exact absurd hres.symm (encodeFormula_ne_zero φ)
    | some ψ =>
        simp only [checkResultCodeE, hP] at hres
        exact ⟨P, by rw [hP, encodeFormula_injective hres]⟩
  · rintro ⟨P, hP⟩
    refine ⟨encodeProof P, ?_⟩
    simp only [proofRelE, isProofCodeCB_encode, checkProofCodeE_encode, checkResultCodeE, hP,
      codeEqB_self, Bool.true_and]
    simp [codeEqB, encodeFormula_ne_zero]

end OperatorKO7.Meta.BoundaryObserver.EqualityRepairChecker
