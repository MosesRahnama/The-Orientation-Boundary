import OperatorKO7.Meta.DistinctionBoundary.GodelRobinsonQ
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false
open scoped Function

/-!
# Arithmetized substitution and Hilbert-sequence proof relation

Object-language graphs use `{0,S,+,×,=,¬,→,∀}` and polynomial `ccons`.
No `substApp`, `quoteNat`, or `prf` constructors. Gödel β-coding of
Hilbert sequences makes the proof relation a single first-order formula.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

open Term

def cconsTerm (h t : Term) : Term :=
  succ (add (mul (add h t) (add h t)) t)

theorem eval_cconsTerm (env : Nat → Nat) (h t : Term) :
    evalTerm env (cconsTerm h t) =
      ccons (evalTerm env h) (evalTerm env t) := by
  simp [cconsTerm, evalTerm, ccons, cpair]

theorem termHasVar_cconsTerm (x : Nat) (h t : Term) :
    termHasVar x (cconsTerm h t) = (termHasVar x h || termHasVar x t) := by
  simp [cconsTerm, termHasVar]

def eqCcons (n h t : Term) : Formula :=
  Formula.eq n (cconsTerm h t)

theorem eval_eqCcons (env : Nat → Nat) (n h t : Term) :
    evalForm env (eqCcons n h t) ↔
      evalTerm env n = ccons (evalTerm env h) (evalTerm env t) := by
  simp [eqCcons, evalForm, eval_cconsTerm]

def env0 : Nat → Nat := fun _ => 0

theorem evalForm_substNum (env : Nat → Nat) (n : Nat) (φ : Formula) :
    evalForm env (substNum φ n) ↔
      evalForm (envUpdate env 0 n) φ := by
  have := evalForm_subst_closed env 0 (numeral n) (isClosedTerm_numeral n) φ
  simpa [evalTerm_numeral, substNum] using this

theorem eval_existsF (env : Nat → Nat) (x : Nat) (φ : Formula) :
    evalForm env (existsF x φ) ↔
      ∃ n : Nat, evalForm (fun y => if y = x then n else env y) φ := by
  dsimp [existsF, evalForm]
  constructor
  · intro h
    rcases Classical.not_forall.mp h with ⟨n, hn⟩
    exact ⟨n, Classical.not_not.mp hn⟩
  · intro ⟨n, hn⟩ hall
    exact hall n hn

theorem eval_andF (env : Nat → Nat) (φ ψ : Formula) :
    evalForm env (andF φ ψ) ↔ evalForm env φ ∧ evalForm env ψ := by
  dsimp [andF, evalForm]
  constructor
  · intro h
    constructor
    · by_contra hφ
      exact h fun hφ' => False.elim (hφ hφ')
    · by_contra hψ
      exact h fun _ => hψ
  · intro ⟨hφ, hψ⟩ himp
    exact himp hφ hψ

theorem eval_orF (env : Nat → Nat) (φ ψ : Formula) :
    evalForm env (orF φ ψ) ↔ evalForm env φ ∨ evalForm env ψ := by
  dsimp [orF, evalForm]
  constructor
  · intro h
    by_cases hφ : evalForm env φ
    · exact Or.inl hφ
    · exact Or.inr (h hφ)
  · intro h hφ
    exact h.elim (fun hp => False.elim (hφ hp)) id

theorem evalTerm_fresh (x : Nat) :
    ∀ t : Term, termHasVar x t = false →
      ∀ env n, evalTerm (fun y => if y = x then n else env y) t = evalTerm env t
  | zero, _, env, n => rfl
  | succ t, ht, env, n => by
    simp [termHasVar] at ht
    simp [evalTerm, evalTerm_fresh x t ht env n]
  | add s t, ht, env, n => by
    simp [termHasVar, Bool.or_eq_false_iff] at ht
    simp [evalTerm, evalTerm_fresh x s ht.1 env n, evalTerm_fresh x t ht.2 env n]
  | mul s t, ht, env, n => by
    simp [termHasVar, Bool.or_eq_false_iff] at ht
    simp [evalTerm, evalTerm_fresh x s ht.1 env n, evalTerm_fresh x t ht.2 env n]
  | var y, ht, env, n => by
    simp [termHasVar, decide_eq_false_iff_not] at ht
    simp [evalTerm, ht]

def codeSubstNat (x y : Nat) : Nat :=
  match decodeFormula? x with
  | some φ => formulaCode (substNum φ y)
  | none => 0

theorem codeSubstNat_encode (φ : Formula) (y : Nat) :
    codeSubstNat (encodeFormula φ) y = formulaCode (substNum φ y) := by
  simp [codeSubstNat, decodeFormula?_encode]

theorem codeSubstNat_formulaCode (φ : Formula) (y : Nat) :
    codeSubstNat (formulaCode φ) y = formulaCode (substNum φ y) := by
  simp only [codeSubstNat]
  rw [decodeFormula?_formulaCode]

def isAxiomCode (m : Nat) : Bool :=
  match decodeFormula? m with
  | some φ => isAxiom φ
  | none => false

theorem isAxiomCode_encode (φ : Formula) :
    isAxiomCode (encodeFormula φ) = isAxiom φ := by
  simp [isAxiomCode, decodeFormula?_encode]

def isImpCode (c a b : Nat) : Bool :=
  decide (c = ccons 2 (ccons a b))

def isGenCode (c x a : Nat) : Bool :=
  decide (c = ccons 3 (ccons x a))

def extractTerm (x : Nat) : Term → Term → Option Term
  | var y, u => if y = x then some u else none
  | zero, zero => none
  | succ s, succ t => extractTerm x s t
  | add s1 s2, add t1 t2 =>
      match extractTerm x s1 t1 with
      | some u => some u
      | none => extractTerm x s2 t2
  | mul s1 s2, mul t1 t2 =>
      match extractTerm x s1 t1 with
      | some u => some u
      | none => extractTerm x s2 t2
  | _, _ => none

def extractClosedSubst (x : Nat) : Formula → Formula → Option Term
  | Formula.eq s t, Formula.eq s' t' =>
      match extractTerm x s s' with
      | some u => some u
      | none => extractTerm x t t'
  | Formula.not φ, Formula.not ψ => extractClosedSubst x φ ψ
  | Formula.imp a b, Formula.imp a' b' =>
      match extractClosedSubst x a a' with
      | some u => some u
      | none => extractClosedSubst x b b'
  | Formula.all y φ, Formula.all y' ψ =>
      if y = x then none
      else if y = y' then extractClosedSubst x φ ψ else none
  | _, _ => none

def isSpecInstance (univ conc : Nat) : Bool :=
  match decodeFormula? univ, decodeFormula? conc with
  | some (Formula.all x φ), some ψ =>
      if formHasVar x φ = false then decide (φ = ψ)
      else
        match extractClosedSubst x φ ψ with
        | some t => isClosedTerm t && decide (substForm x t φ = ψ)
        | none => false
  | _, _ => false

def lineJustified (prev : List Nat) (c : Nat) : Bool :=
  isAxiomCode c ||
    prev.any (fun a => prev.any (fun b => isImpCode a b c)) ||
    prev.any (fun a => (List.range (c + 1)).any (fun x => isGenCode c x a)) ||
    prev.any (fun a => isSpecInstance a c)

def isHilbertSeq : List Nat → Bool
  | [] => false
  | xs =>
      (List.range xs.length).all (fun i =>
        lineJustified (xs.take i) (xs.getD i 0))

def seqProves (codes : List Nat) (conc : Nat) : Bool :=
  isHilbertSeq codes && decide (codes.getLast? = some conc)

theorem flatten_ax {φ : Formula} (h : isAxiom φ = true) :
    seqProves [encodeFormula φ] (encodeFormula φ) = true := by
  simp [seqProves, isHilbertSeq, lineJustified, isAxiomCode,
    decodeFormula?_encode, h]

/-! ## Gödel β and the object-language proof relation -/

def beta (c d i : Nat) : Nat :=
  c % (1 + (i + 1) * d)

def leF (a b : Term) : Formula :=
  existsF 50 (Formula.eq (add a (Term.var 50)) b)

def ltF (a b : Term) : Formula :=
  existsF 51 (Formula.eq (add (succ a) (Term.var 51)) b)

def remF (c m r : Term) : Formula :=
  andF (ltF r m) (existsF 52 (Formula.eq c (add (mul (Term.var 52) m) r)))

def betaF (c d i a : Term) : Formula :=
  remF c (succ (mul (succ i) d)) a

theorem eval_leF (env : Nat → Nat) (a b : Term)
    (ha : termHasVar 50 a = false) (hb : termHasVar 50 b = false) :
    evalForm env (leF a b) ↔ evalTerm env a ≤ evalTerm env b := by
  unfold leF
  rw [eval_existsF]
  constructor
  · intro ⟨n, hn⟩
    have heq : evalTerm env a + n = evalTerm env b := by
      simp [evalForm, evalTerm, evalTerm_fresh 50 a ha env n,
        evalTerm_fresh 50 b hb env n] at hn
      exact hn
    rw [← heq]
    exact Nat.le_add_right _ _
  · intro hle
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    refine ⟨k, ?_⟩
    simp [evalForm, evalTerm, evalTerm_fresh 50 a ha env k,
      evalTerm_fresh 50 b hb env k, hk, Nat.add_comm]

theorem eval_ltF (env : Nat → Nat) (a b : Term)
    (ha : termHasVar 51 a = false) (hb : termHasVar 51 b = false) :
    evalForm env (ltF a b) ↔ evalTerm env a < evalTerm env b := by
  unfold ltF
  rw [eval_existsF]
  constructor
  · intro ⟨n, hn⟩
    have heq : evalTerm env a + 1 + n = evalTerm env b := by
      simp [evalForm, evalTerm, evalTerm_fresh 51 a ha env n,
        evalTerm_fresh 51 b hb env n] at hn
      exact hn
    have : evalTerm env a + 1 ≤ evalTerm env b := by
      rw [← heq]
      exact Nat.le_add_right _ _
    exact Nat.succ_le_iff.mp this
  · intro hlt
    have hle : evalTerm env a + 1 ≤ evalTerm env b := Nat.succ_le_iff.mpr hlt
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    refine ⟨k, ?_⟩
    simp [evalForm, evalTerm, evalTerm_fresh 51 a ha env k,
      evalTerm_fresh 51 b hb env k, hk, Nat.add_comm]

theorem eval_betaF (env : Nat → Nat) (c d i a : Term)
    (h51i : termHasVar 51 i = false) (h51d : termHasVar 51 d = false)
    (h51a : termHasVar 51 a = false)
    (h52c : termHasVar 52 c = false) (h52i : termHasVar 52 i = false)
    (h52d : termHasVar 52 d = false) (h52a : termHasVar 52 a = false) :
    evalForm env (betaF c d i a) ↔
      evalTerm env a = beta (evalTerm env c) (evalTerm env d) (evalTerm env i) := by
  have hm51 : termHasVar 51 (succ (mul (succ i) d)) = false := by
    simp [termHasVar, h51i, h51d]
  have hm52 : termHasVar 52 (succ (mul (succ i) d)) = false := by
    simp [termHasVar, h52i, h52d]
  unfold betaF remF
  rw [eval_andF, eval_ltF env a (succ (mul (succ i) d)) h51a hm51, eval_existsF]
  set m := 1 + (evalTerm env i + 1) * evalTerm env d with hmDef
  have hmEval : evalTerm env (succ (mul (succ i) d)) = m := by
    simp [evalTerm, m, Nat.add_comm]
  have hpos : 0 < m := Nat.add_pos_left (by decide) _
  constructor
  · intro ⟨hlt, q, hq⟩
    have heq : evalTerm env c = q * m + evalTerm env a := by
      simp [evalForm, evalTerm, evalTerm_fresh 52 c h52c env q,
        evalTerm_fresh 52 i h52i env q, evalTerm_fresh 52 d h52d env q,
        evalTerm_fresh 52 a h52a env q] at hq
      simpa [hmEval, m, Nat.add_comm] using hq
    have hlt' : evalTerm env a < m := by
      simpa [hmEval] using hlt
    unfold beta
    rw [heq, Nat.add_comm (q * m), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt']
  · intro hbeta
    have hmod : evalTerm env a = evalTerm env c % m := by
      simpa [beta, m] using hbeta
    have hlt : evalTerm env a < m := by
      rw [hmod]
      exact Nat.mod_lt _ hpos
    refine ⟨by simpa [hmEval] using hlt, evalTerm env c / m, ?_⟩
    set q := evalTerm env c / m
    let env' := fun y => if y = 52 then q else env y
    have hc' := evalTerm_fresh 52 c h52c env q
    have ha' := evalTerm_fresh 52 a h52a env q
    have hm' := evalTerm_fresh 52 (succ (mul (succ i) d)) hm52 env q
    change evalTerm env' c =
      evalTerm env' (Term.var 52) * evalTerm env' (succ (mul (succ i) d)) +
        evalTerm env' a
    simp [env', evalTerm, hc', ha', hmod]
    rw [evalTerm_fresh 52 i h52i env q, evalTerm_fresh 52 d h52d env q]
    have : (evalTerm env i + 1) * evalTerm env d + 1 = m := by
      simp [m, Nat.add_comm]
    rw [this, Nat.mul_comm q]
    exact (Nat.div_add_mod (evalTerm env c) m).symm

def boundMax : Nat → (Nat → Nat) → Nat
  | 0, f => f 0
  | n + 1, f => Nat.max (boundMax n f) (f (n + 1))

theorem le_boundMax (L : Nat) (f : Nat → Nat) :
    ∀ i, i ≤ L → f i ≤ boundMax L f := by
  induction L with
  | zero =>
    intro i hi
    have : i = 0 := Nat.eq_zero_of_le_zero hi
    subst this
    exact Nat.le_refl _
  | succ L ih =>
    intro i hi
    cases Nat.lt_or_eq_of_le hi with
    | inl hlt =>
      exact Nat.le_trans (ih i (Nat.le_of_lt_succ hlt)) (Nat.le_max_left _ _)
    | inr heq =>
      subst heq
      exact Nat.le_max_right _ _

def betaModulus (d i : Nat) : Nat := 1 + (i + 1) * d

theorem gcd_one_add_mul_self (d i : Nat) :
    Nat.gcd (1 + (i + 1) * d) d = 1 := by
  have h := Nat.gcd_add_mul_right_left 1 d (i + 1)
  simpa [Nat.gcd_one_left] using h

theorem gcd_one_mod (n : Nat) (hn : 0 < n) : Nat.gcd (1 % n) n = 1 := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
    cases n with
    | zero => simp
    | succ n =>
      have hlt : 1 < n + 2 := Nat.succ_lt_succ (Nat.succ_pos n)
      rw [Nat.mod_eq_of_lt hlt, Nat.gcd_one_left]

theorem coprime_beta_moduli {d i j : Nat} (hij : i < j)
    (hd : (j - i) ∣ d) :
    Nat.Coprime (betaModulus d i) (betaModulus d j) := by
  unfold betaModulus Nat.Coprime
  have hsum :
      1 + (j + 1) * d = (1 + (i + 1) * d) + (j - i) * d := by
    have h : i + 1 + (j - i) = j + 1 := by omega
    rw [← h, Nat.add_mul, Nat.add_assoc]
  rw [hsum]
  have hgcd :
      Nat.gcd (1 + (i + 1) * d) ((1 + (i + 1) * d) + (j - i) * d) =
        Nat.gcd (1 + (i + 1) * d) ((j - i) * d) := by
    have h :=
      Nat.gcd_add_mul_right_right (1 + (i + 1) * d) ((j - i) * d) 1
    simpa [Nat.mul_one, Nat.add_comm] using h
  rw [hgcd]
  have ha : Nat.Coprime (1 + (i + 1) * d) d := gcd_one_add_mul_self d i
  have hmul :
      Nat.gcd (1 + (i + 1) * d) ((j - i) * d) =
        Nat.gcd (1 + (i + 1) * d) (j - i) := by
    rw [Nat.gcd_comm, ha.symm.gcd_mul_right_cancel (j - i), Nat.gcd_comm]
  rw [hmul]
  rw [Nat.gcd_comm (1 + (i + 1) * d) (j - i), Nat.gcd_rec]
  have hpos : 0 < j - i := Nat.sub_pos_of_lt hij
  have hmod : (1 + (i + 1) * d) % (j - i) = 1 % (j - i) := by
    have hdiv : (j - i) ∣ (i + 1) * d := by
      obtain ⟨t, ht⟩ := hd
      refine ⟨(i + 1) * t, ?_⟩
      rw [ht, Nat.mul_left_comm]
    have hz : (i + 1) * d % (j - i) = 0 := Nat.mod_eq_zero_of_dvd hdiv
    rw [Nat.add_mod, hz, Nat.add_zero, Nat.mod_mod]
  rw [hmod]
  exact gcd_one_mod (j - i) hpos

def numCode : Nat → Nat
  | 0 => ccons 0 0
  | n + 1 => ccons 1 (numCode n)

theorem encodeTerm_numeral_eq_numCode :
    ∀ n : Nat, encodeTerm (numeral n) = numCode n
  | 0 => rfl
  | n + 1 => by simp [numeral, encodeTerm, numCode, encodeTerm_numeral_eq_numCode n]

theorem uncpairGo_le_arg : ∀ s n : Nat, (uncpairGo s n).1 ≤ n ∧ (uncpairGo s n).2 ≤ n
  | 0, n => by simp [uncpairGo]
  | s + 1, n => by
    simp [uncpairGo]
    split_ifs with h
    · have hs : s ≤ n := by
        cases s with
        | zero => exact Nat.zero_le n
        | succ t =>
          have hmul : t + 1 ≤ (t + 1) * (t + 1) :=
            Nat.le_mul_of_pos_right (t + 1) (Nat.succ_pos t)
          exact Nat.le_trans hmul h.1
      exact ⟨Nat.le_trans (Nat.sub_le _ _) hs, Nat.sub_le n (s * s)⟩
    · exact uncpairGo_le_arg s n

theorem uncpair_lt (n : Nat) (hn : n ≠ 0) :
    (uncpair (n - 1)).1 < n ∧ (uncpair (n - 1)).2 < n := by
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  have heq : uncpair (n - 1) = uncpairGo n (n - 1) := by
    simp [uncpair, Nat.sub_add_cancel hpos]
  rw [heq]
  have hle := uncpairGo_le_arg n (n - 1)
  exact ⟨Nat.lt_of_le_of_lt hle.1 (Nat.pred_lt hn),
    Nat.lt_of_le_of_lt hle.2 (Nat.pred_lt hn)⟩

def substTermCode (y n : Nat) : Nat :=
  if h : n = 0 then 0
  else
    let p := uncpair (n - 1)
    match p.1 with
    | 0 => if p.2 = 0 then ccons 0 0 else 0
    | 1 => ccons 1 (substTermCode y p.2)
    | 2 =>
      if p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        ccons 2 (ccons (substTermCode y q.1) (substTermCode y q.2))
    | 3 =>
      if p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        ccons 3 (ccons (substTermCode y q.1) (substTermCode y q.2))
    | 4 => if p.2 = 0 then numCode y else n
    | _ => 0
termination_by n
decreasing_by
  · exact (uncpair_lt n h).2
  · have hp : p.2 ≠ 0 := by
      intro hz
      simp [hz] at ‹¬p.2 = 0›
    exact Nat.lt_trans (uncpair_lt p.2 hp).1 (uncpair_lt n h).2
  · have hp : p.2 ≠ 0 := by
      intro hz
      simp [hz] at ‹¬p.2 = 0›
    exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2
  · have hp : p.2 ≠ 0 := by
      intro hz
      simp [hz] at ‹¬p.2 = 0›
    exact Nat.lt_trans (uncpair_lt p.2 hp).1 (uncpair_lt n h).2
  · have hp : p.2 ≠ 0 := by
      intro hz
      simp [hz] at ‹¬p.2 = 0›
    exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2

def substFormCode (y n : Nat) : Nat :=
  if h : n = 0 then 0
  else
    let p := uncpair (n - 1)
    match p.1 with
    | 0 =>
      if p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        ccons 0 (ccons (substTermCode y q.1) (substTermCode y q.2))
    | 1 => ccons 1 (substFormCode y p.2)
    | 2 =>
      if p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        ccons 2 (ccons (substFormCode y q.1) (substFormCode y q.2))
    | 3 =>
      if p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        if q.1 = 0 then n
        else ccons 3 (ccons q.1 (substFormCode y q.2))
    | _ => 0
termination_by n
decreasing_by
  · exact (uncpair_lt n h).2
  · have hp : p.2 ≠ 0 := by
      intro hz
      simp [hz] at ‹¬p.2 = 0›
    exact Nat.lt_trans (uncpair_lt p.2 hp).1 (uncpair_lt n h).2
  · have hp : p.2 ≠ 0 := by
      intro hz
      simp [hz] at ‹¬p.2 = 0›
    exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2
  · have hp : p.2 ≠ 0 := by
      intro hz
      simp [hz] at ‹¬p.2 = 0›
    exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2

/-- Numeral-code graph: `z = numCode y`, as a first-order β-trace. -/
def numCodeRel (y z : Term) : Formula :=
  existsF 80 (existsF 81
    (andF (betaF (Term.var 80) (Term.var 81) (numeral 0)
        (cconsTerm (numeral 0) (numeral 0)))
      (andF (betaF (Term.var 80) (Term.var 81) y z)
        (Formula.all 82 (Formula.imp (ltF (Term.var 82) y)
          (existsF 83
            (andF (betaF (Term.var 80) (Term.var 81) (Term.var 82) (Term.var 83))
              (betaF (Term.var 80) (Term.var 81) (succ (Term.var 82))
                (cconsTerm (numeral 1) (Term.var 83))))))))))

theorem pairwise_beta_moduli (L d : Nat)
    (hd : ∀ k, 0 < k → k ≤ L → k ∣ d) :
    (List.range (L + 1)).Pairwise (Nat.Coprime on fun i => betaModulus d i) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < L + 1 := by simpa [List.length_range] using hi
  have hj' : j < L + 1 := by simpa [List.length_range] using hj
  simp [List.getElem_range]
  exact coprime_beta_moduli hij
    (hd (j - i) (Nat.sub_pos_of_lt hij)
      (Nat.le_trans (Nat.sub_le j i) (Nat.le_of_lt_succ hj')))

theorem beta_exists (L : Nat) (f : Nat → Nat) :
    ∃ c d, ∀ i, i ≤ L → beta c d i = f i := by
  let d := Nat.factorial (L + 1) * (boundMax L f + 1)
  have hdvd : ∀ k, 0 < k → k ≤ L → k ∣ d := by
    intro k hk0 hkL
    have : k ∣ Nat.factorial (L + 1) :=
      Nat.dvd_factorial hk0 (Nat.le_trans hkL (Nat.le_succ L))
    obtain ⟨t, ht⟩ := this
    dsimp [d]
    exact ⟨t * (boundMax L f + 1), by rw [ht, Nat.mul_assoc]⟩
  have hLsucc : ∀ k, 0 < k → k ≤ L + 1 → k ∣ d := by
    intro k hk0 hkL
    have : k ∣ Nat.factorial (L + 1) := Nat.dvd_factorial hk0 hkL
    obtain ⟨t, ht⟩ := this
    dsimp [d]
    exact ⟨t * (boundMax L f + 1), by rw [ht, Nat.mul_assoc]⟩
  have co :
      (List.range (L + 1)).Pairwise (Nat.Coprime on fun i => betaModulus d i) :=
    pairwise_beta_moduli L d (fun k hk0 hkL => hLsucc k hk0 (Nat.le_succ_of_le hkL))
  let k := Nat.chineseRemainderOfList f (fun i => betaModulus d i) (List.range (L + 1)) co
  refine ⟨k.1, d, ?_⟩
  intro i hi
  have himem : i ∈ List.range (L + 1) := List.mem_range.mpr (Nat.lt_succ_of_le hi)
  have hmod : (k : Nat) ≡ f i [MOD betaModulus d i] := k.2 i himem
  have hlt : f i < betaModulus d i := by
    have hle := le_boundMax L f i hi
    have hpos : 0 < boundMax L f + 1 := Nat.succ_pos _
    have : boundMax L f + 1 ≤ d := by
      have hfac : 1 ≤ Nat.factorial (L + 1) := Nat.succ_le_of_lt (Nat.factorial_pos _)
      exact Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    have : f i + 1 ≤ d := Nat.succ_le_succ hle |>.trans this
    unfold betaModulus
    have : d ≤ (i + 1) * d := Nat.le_mul_of_pos_left _ (Nat.succ_pos i)
    omega
  have : (k : Nat) % betaModulus d i = f i % betaModulus d i := hmod
  rw [Nat.mod_eq_of_lt hlt] at this
  simpa [beta, betaModulus] using this

def isEqReflF (n : Term) : Formula :=
  existsF 53 (eqCcons n (numeral 0) (cconsTerm (Term.var 53) (Term.var 53)))

def isAxIdF (n : Term) : Formula :=
  existsF 53 (eqCcons n (numeral 2) (cconsTerm (Term.var 53) (Term.var 53)))

def isAxKF (n : Term) : Formula :=
  existsF 53 (existsF 54
    (eqCcons n (numeral 2)
      (cconsTerm (Term.var 53)
        (cconsTerm (numeral 2) (cconsTerm (Term.var 54) (Term.var 53))))))

def isQ1F (n : Term) : Formula :=
  (existsF 300 (existsF 301 (existsF 302 (existsF 303 (existsF 304 (existsF 305 (existsF 306 (existsF 307 (andF (andF (andF (andF (andF (andF (andF (andF (Formula.eq n (Term.var 307)) (eqCcons (Term.var 300) (numeral 4) (numeral 0))) (eqCcons (Term.var 301) (numeral 1) (Term.var 300))) (eqCcons (Term.var 302) (numeral 0) (numeral 0))) (Formula.eq (Term.var 303) (cconsTerm (Term.var 301) (Term.var 302)))) (eqCcons (Term.var 304) (numeral 0) (Term.var 303))) (eqCcons (Term.var 305) (numeral 1) (Term.var 304))) (Formula.eq (Term.var 306) (cconsTerm (numeral 0) (Term.var 305)))) (eqCcons (Term.var 307) (numeral 3) (Term.var 306)))))))))))

def isQ2F (n : Term) : Formula :=
  (existsF 300 (existsF 301 (existsF 302 (existsF 303 (existsF 304 (existsF 305 (existsF 306 (existsF 307 (existsF 308 (existsF 309 (existsF 310 (existsF 311 (existsF 312 (existsF 313 (existsF 314 (existsF 315 (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (Formula.eq n (Term.var 315)) (eqCcons (Term.var 300) (numeral 4) (numeral 0))) (eqCcons (Term.var 301) (numeral 1) (Term.var 300))) (eqCcons (Term.var 302) (numeral 4) (numeral 1))) (eqCcons (Term.var 303) (numeral 1) (Term.var 302))) (Formula.eq (Term.var 304) (cconsTerm (Term.var 301) (Term.var 303)))) (eqCcons (Term.var 305) (numeral 0) (Term.var 304))) (eqCcons (Term.var 306) (numeral 4) (numeral 0))) (eqCcons (Term.var 307) (numeral 4) (numeral 1))) (Formula.eq (Term.var 308) (cconsTerm (Term.var 306) (Term.var 307)))) (eqCcons (Term.var 309) (numeral 0) (Term.var 308))) (Formula.eq (Term.var 310) (cconsTerm (Term.var 305) (Term.var 309)))) (eqCcons (Term.var 311) (numeral 2) (Term.var 310))) (Formula.eq (Term.var 312) (cconsTerm (numeral 1) (Term.var 311)))) (eqCcons (Term.var 313) (numeral 3) (Term.var 312))) (Formula.eq (Term.var 314) (cconsTerm (numeral 0) (Term.var 313)))) (eqCcons (Term.var 315) (numeral 3) (Term.var 314)))))))))))))))))))

def isQ3F (n : Term) : Formula :=
  (existsF 300 (existsF 301 (existsF 302 (existsF 303 (existsF 304 (existsF 305 (existsF 306 (existsF 307 (existsF 308 (andF (andF (andF (andF (andF (andF (andF (andF (andF (Formula.eq n (Term.var 308)) (eqCcons (Term.var 300) (numeral 4) (numeral 0))) (eqCcons (Term.var 301) (numeral 0) (numeral 0))) (Formula.eq (Term.var 302) (cconsTerm (Term.var 300) (Term.var 301)))) (eqCcons (Term.var 303) (numeral 2) (Term.var 302))) (eqCcons (Term.var 304) (numeral 4) (numeral 0))) (Formula.eq (Term.var 305) (cconsTerm (Term.var 303) (Term.var 304)))) (eqCcons (Term.var 306) (numeral 0) (Term.var 305))) (Formula.eq (Term.var 307) (cconsTerm (numeral 0) (Term.var 306)))) (eqCcons (Term.var 308) (numeral 3) (Term.var 307))))))))))))

def isQ4F (n : Term) : Formula :=
  (existsF 300 (existsF 301 (existsF 302 (existsF 303 (existsF 304 (existsF 305 (existsF 306 (existsF 307 (existsF 308 (existsF 309 (existsF 310 (existsF 311 (existsF 312 (existsF 313 (existsF 314 (existsF 315 (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (Formula.eq n (Term.var 315)) (eqCcons (Term.var 300) (numeral 4) (numeral 0))) (eqCcons (Term.var 301) (numeral 4) (numeral 1))) (eqCcons (Term.var 302) (numeral 1) (Term.var 301))) (Formula.eq (Term.var 303) (cconsTerm (Term.var 300) (Term.var 302)))) (eqCcons (Term.var 304) (numeral 2) (Term.var 303))) (eqCcons (Term.var 305) (numeral 4) (numeral 0))) (eqCcons (Term.var 306) (numeral 4) (numeral 1))) (Formula.eq (Term.var 307) (cconsTerm (Term.var 305) (Term.var 306)))) (eqCcons (Term.var 308) (numeral 2) (Term.var 307))) (eqCcons (Term.var 309) (numeral 1) (Term.var 308))) (Formula.eq (Term.var 310) (cconsTerm (Term.var 304) (Term.var 309)))) (eqCcons (Term.var 311) (numeral 0) (Term.var 310))) (Formula.eq (Term.var 312) (cconsTerm (numeral 1) (Term.var 311)))) (eqCcons (Term.var 313) (numeral 3) (Term.var 312))) (Formula.eq (Term.var 314) (cconsTerm (numeral 0) (Term.var 313)))) (eqCcons (Term.var 315) (numeral 3) (Term.var 314)))))))))))))))))))

def isQ5F (n : Term) : Formula :=
  (existsF 300 (existsF 301 (existsF 302 (existsF 303 (existsF 304 (existsF 305 (existsF 306 (existsF 307 (existsF 308 (andF (andF (andF (andF (andF (andF (andF (andF (andF (Formula.eq n (Term.var 308)) (eqCcons (Term.var 300) (numeral 4) (numeral 0))) (eqCcons (Term.var 301) (numeral 0) (numeral 0))) (Formula.eq (Term.var 302) (cconsTerm (Term.var 300) (Term.var 301)))) (eqCcons (Term.var 303) (numeral 3) (Term.var 302))) (eqCcons (Term.var 304) (numeral 0) (numeral 0))) (Formula.eq (Term.var 305) (cconsTerm (Term.var 303) (Term.var 304)))) (eqCcons (Term.var 306) (numeral 0) (Term.var 305))) (Formula.eq (Term.var 307) (cconsTerm (numeral 0) (Term.var 306)))) (eqCcons (Term.var 308) (numeral 3) (Term.var 307))))))))))))

def isQ6F (n : Term) : Formula :=
  (existsF 300 (existsF 301 (existsF 302 (existsF 303 (existsF 304 (existsF 305 (existsF 306 (existsF 307 (existsF 308 (existsF 309 (existsF 310 (existsF 311 (existsF 312 (existsF 313 (existsF 314 (existsF 315 (existsF 316 (existsF 317 (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (Formula.eq n (Term.var 317)) (eqCcons (Term.var 300) (numeral 4) (numeral 0))) (eqCcons (Term.var 301) (numeral 4) (numeral 1))) (eqCcons (Term.var 302) (numeral 1) (Term.var 301))) (Formula.eq (Term.var 303) (cconsTerm (Term.var 300) (Term.var 302)))) (eqCcons (Term.var 304) (numeral 3) (Term.var 303))) (eqCcons (Term.var 305) (numeral 4) (numeral 0))) (eqCcons (Term.var 306) (numeral 4) (numeral 1))) (Formula.eq (Term.var 307) (cconsTerm (Term.var 305) (Term.var 306)))) (eqCcons (Term.var 308) (numeral 3) (Term.var 307))) (eqCcons (Term.var 309) (numeral 4) (numeral 0))) (Formula.eq (Term.var 310) (cconsTerm (Term.var 308) (Term.var 309)))) (eqCcons (Term.var 311) (numeral 2) (Term.var 310))) (Formula.eq (Term.var 312) (cconsTerm (Term.var 304) (Term.var 311)))) (eqCcons (Term.var 313) (numeral 0) (Term.var 312))) (Formula.eq (Term.var 314) (cconsTerm (numeral 1) (Term.var 313)))) (eqCcons (Term.var 315) (numeral 3) (Term.var 314))) (Formula.eq (Term.var 316) (cconsTerm (numeral 0) (Term.var 315)))) (eqCcons (Term.var 317) (numeral 3) (Term.var 316)))))))))))))))))))))

def isQ7F (n : Term) : Formula :=
  (existsF 300 (existsF 301 (existsF 302 (existsF 303 (existsF 304 (existsF 305 (existsF 306 (existsF 307 (existsF 308 (existsF 309 (existsF 310 (existsF 311 (existsF 312 (existsF 313 (existsF 314 (existsF 315 (existsF 316 (existsF 317 (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (andF (Formula.eq n (Term.var 317)) (eqCcons (Term.var 300) (numeral 4) (numeral 0))) (eqCcons (Term.var 301) (numeral 0) (numeral 0))) (Formula.eq (Term.var 302) (cconsTerm (Term.var 300) (Term.var 301)))) (eqCcons (Term.var 303) (numeral 0) (Term.var 302))) (eqCcons (Term.var 304) (numeral 1) (Term.var 303))) (eqCcons (Term.var 305) (numeral 4) (numeral 0))) (eqCcons (Term.var 306) (numeral 4) (numeral 1))) (eqCcons (Term.var 307) (numeral 1) (Term.var 306))) (Formula.eq (Term.var 308) (cconsTerm (Term.var 305) (Term.var 307)))) (eqCcons (Term.var 309) (numeral 0) (Term.var 308))) (eqCcons (Term.var 310) (numeral 1) (Term.var 309))) (Formula.eq (Term.var 311) (cconsTerm (numeral 1) (Term.var 310)))) (eqCcons (Term.var 312) (numeral 3) (Term.var 311))) (eqCcons (Term.var 313) (numeral 1) (Term.var 312))) (Formula.eq (Term.var 314) (cconsTerm (Term.var 304) (Term.var 313)))) (eqCcons (Term.var 315) (numeral 2) (Term.var 314))) (Formula.eq (Term.var 316) (cconsTerm (numeral 0) (Term.var 315)))) (eqCcons (Term.var 317) (numeral 3) (Term.var 316)))))))))))))))))))))

def isQAxiomF (n : Term) : Formula :=
  orF (isQ1F n) (orF (isQ2F n) (orF (isQ3F n) (orF (isQ4F n)
    (orF (isQ5F n) (orF (isQ6F n) (isQ7F n))))))

def isAxDNEF (n : Term) : Formula :=
  existsF 340 (existsF 341 (existsF 342
    (andF (eqCcons (Term.var 341) (numeral 1) (Term.var 340))
      (andF (eqCcons (Term.var 342) (numeral 1) (Term.var 341))
        (eqCcons n (numeral 2)
          (cconsTerm (Term.var 342) (Term.var 340)))))))

def isAxSF (n : Term) : Formula :=
  existsF 350 (existsF 351 (existsF 352 (existsF 353 (existsF 354
    (existsF 355 (existsF 356 (existsF 357 (existsF 358 (existsF 359 (existsF 360
      (andF (Formula.eq (Term.var 353)
          (cconsTerm (Term.var 350)
            (cconsTerm (numeral 2) (cconsTerm (Term.var 351) (Term.var 352)))))
        (andF (eqCcons (Term.var 354) (numeral 2) (Term.var 353))
          (andF (Formula.eq (Term.var 355)
              (cconsTerm (Term.var 350) (Term.var 351)))
            (andF (eqCcons (Term.var 356) (numeral 2) (Term.var 355))
              (andF (Formula.eq (Term.var 357)
                  (cconsTerm (Term.var 350) (Term.var 352)))
                (andF (eqCcons (Term.var 358) (numeral 2) (Term.var 357))
                  (andF (Formula.eq (Term.var 359)
                      (cconsTerm (Term.var 356) (Term.var 358)))
                    (andF (eqCcons (Term.var 360) (numeral 2) (Term.var 359))
                      (eqCcons n (numeral 2)
                        (cconsTerm (Term.var 354) (Term.var 360)))))))))))))))))))))

def isAxiomF (n : Term) : Formula :=
  orF (isQAxiomF n) (orF (isEqReflF n) (orF (isAxIdF n)
    (orF (isAxKF n) (orF (isAxSF n) (isAxDNEF n)))))

def isImpF (a b c : Term) : Formula :=
  eqCcons a (numeral 2) (cconsTerm b c)

def isGenF (c x a : Term) : Formula :=
  eqCcons c (numeral 3) (cconsTerm x a)

/-- Local justification of line `i` in a β-coded Hilbert sequence. -/
def justifiedF (c d i : Term) : Formula :=
  existsF 55
    (andF (betaF c d i (Term.var 55))
      (orF (isAxiomF (Term.var 55)) <|
        orF (existsF 56 (existsF 57 (existsF 58 (existsF 59
              (andF (ltF (Term.var 56) i)
                (andF (ltF (Term.var 57) i)
                  (andF (betaF c d (Term.var 56) (Term.var 58))
                    (andF (betaF c d (Term.var 57) (Term.var 59))
                      (isImpF (Term.var 58) (Term.var 59) (Term.var 55))))))))))
          (existsF 56 (existsF 57
            (andF (ltF (Term.var 56) i)
              (andF (betaF c d (Term.var 56) (Term.var 57))
                (existsF 58 (isGenF (Term.var 55) (Term.var 58) (Term.var 57)))))))))

/-- Recursive term-substitution table matching `substTermCode`. -/
def termSubstZeroCase (inC outC : Term) : Formula :=
  andF (eqCcons inC (numeral 0) (numeral 0))
    (eqCcons outC (numeral 0) (numeral 0))

def termSubstSuccCase (c d i inC outC : Term) : Formula :=
  existsF 231 (existsF 232 (existsF 233
    (andF (eqCcons inC (numeral 1) (Term.var 231))
      (andF (eqCcons outC (numeral 1) (Term.var 232))
        (andF (ltF (Term.var 233) i)
          (betaF c d (Term.var 233)
            (cconsTerm (Term.var 231) (Term.var 232))))))))

def termSubstAddCase (c d i inC outC : Term) : Formula :=
  existsF 231 (existsF 232 (existsF 233 (existsF 234 (existsF 235 (existsF 236
    (andF (eqCcons inC (numeral 2) (cconsTerm (Term.var 231) (Term.var 232)))
      (andF (eqCcons outC (numeral 2) (cconsTerm (Term.var 233) (Term.var 234)))
        (andF (ltF (Term.var 235) i)
          (andF (ltF (Term.var 236) i)
            (andF (betaF c d (Term.var 235)
                (cconsTerm (Term.var 231) (Term.var 233)))
              (betaF c d (Term.var 236)
                (cconsTerm (Term.var 232) (Term.var 234)))))))))))))

def termSubstMulCase (c d i inC outC : Term) : Formula :=
  existsF 231 (existsF 232 (existsF 233 (existsF 234 (existsF 235 (existsF 236
    (andF (eqCcons inC (numeral 3) (cconsTerm (Term.var 231) (Term.var 232)))
      (andF (eqCcons outC (numeral 3) (cconsTerm (Term.var 233) (Term.var 234)))
        (andF (ltF (Term.var 235) i)
          (andF (ltF (Term.var 236) i)
            (andF (betaF c d (Term.var 235)
                (cconsTerm (Term.var 231) (Term.var 233)))
              (betaF c d (Term.var 236)
                (cconsTerm (Term.var 232) (Term.var 234)))))))))))))

def termSubstVarCase (ncode inC outC : Term) : Formula :=
  orF (andF (eqCcons inC (numeral 4) (numeral 0)) (Formula.eq outC ncode))
    (andF (existsF 231 (andF (eqCcons inC (numeral 4) (Term.var 231))
            (ltF (numeral 0) (Term.var 231))))
      (Formula.eq outC inC))

def termSubstJust (c d i ncode inC outC : Term) : Formula :=
  orF (termSubstZeroCase inC outC)
    (orF (termSubstSuccCase c d i inC outC)
      (orF (termSubstAddCase c d i inC outC)
        (orF (termSubstMulCase c d i inC outC)
          (termSubstVarCase ncode inC outC))))

def termSubstClosed (x z ncode : Term) : Formula :=
  existsF 220 (existsF 221 (existsF 222
    (andF (betaF (Term.var 220) (Term.var 221) (Term.var 222)
        (cconsTerm x z))
      (Formula.all 223 (Formula.imp (leF (Term.var 223) (Term.var 222))
        (existsF 224 (existsF 225
          (andF (betaF (Term.var 220) (Term.var 221) (Term.var 223)
              (cconsTerm (Term.var 224) (Term.var 225)))
            (termSubstJust (Term.var 220) (Term.var 221) (Term.var 223)
              ncode (Term.var 224) (Term.var 225))))))))))

def termSubstVarCaseAt (x u inC outC : Term) : Formula :=
  orF (andF (eqCcons inC (numeral 4) x) (Formula.eq outC u))
    (andF (existsF 231 (andF (eqCcons inC (numeral 4) (Term.var 231))
            (Formula.not (Formula.eq (Term.var 231) x))))
      (Formula.eq outC inC))

def termSubstJustAt (c d i x u inC outC : Term) : Formula :=
  orF (termSubstZeroCase inC outC)
    (orF (termSubstSuccCase c d i inC outC)
      (orF (termSubstAddCase c d i inC outC)
        (orF (termSubstMulCase c d i inC outC)
          (termSubstVarCaseAt x u inC outC))))

def termSubstClosedAt (inT outT x u : Term) : Formula :=
  existsF 290 (existsF 291 (existsF 292
    (andF (betaF (Term.var 290) (Term.var 291) (Term.var 292)
        (cconsTerm inT outT))
      (Formula.all 293 (Formula.imp (leF (Term.var 293) (Term.var 292))
        (existsF 294 (existsF 295
          (andF (betaF (Term.var 290) (Term.var 291) (Term.var 293)
              (cconsTerm (Term.var 294) (Term.var 295)))
            (termSubstJustAt (Term.var 290) (Term.var 291) (Term.var 293)
              x u (Term.var 294) (Term.var 295))))))))))

/-- Local justification of a formula-subst table entry `(inC, outC)`
at index `i`, with numeral-code `ncode` already computed. -/
def formSubstEqCase (ncode inC outC : Term) : Formula :=
  existsF 241 (existsF 242 (existsF 243 (existsF 244
    (andF (eqCcons inC (numeral 0) (cconsTerm (Term.var 241) (Term.var 242)))
      (andF (eqCcons outC (numeral 0) (cconsTerm (Term.var 243) (Term.var 244)))
        (andF (termSubstClosed (Term.var 241) (Term.var 243) ncode)
          (termSubstClosed (Term.var 242) (Term.var 244) ncode)))))))

def formSubstNotCase (c d i inC outC : Term) : Formula :=
  existsF 241 (existsF 242 (existsF 243
    (andF (eqCcons inC (numeral 1) (Term.var 241))
      (andF (eqCcons outC (numeral 1) (Term.var 242))
        (andF (ltF (Term.var 243) i)
          (betaF c d (Term.var 243)
            (cconsTerm (Term.var 241) (Term.var 242))))))))

def formSubstImpCase (c d i inC outC : Term) : Formula :=
  existsF 241 (existsF 242 (existsF 243 (existsF 244 (existsF 245 (existsF 246
    (andF (eqCcons inC (numeral 2) (cconsTerm (Term.var 241) (Term.var 242)))
      (andF (eqCcons outC (numeral 2) (cconsTerm (Term.var 243) (Term.var 244)))
        (andF (ltF (Term.var 245) i)
          (andF (ltF (Term.var 246) i)
            (andF (betaF c d (Term.var 245)
                (cconsTerm (Term.var 241) (Term.var 243)))
              (betaF c d (Term.var 246)
                (cconsTerm (Term.var 242) (Term.var 244)))))))))))))

def formSubstAllCase (c d i inC outC : Term) : Formula :=
  existsF 241 (existsF 242 (existsF 243 (existsF 244
    (andF (eqCcons inC (numeral 3) (cconsTerm (Term.var 241) (Term.var 242)))
      (orF (andF (Formula.eq (Term.var 241) (numeral 0)) (Formula.eq outC inC))
        (andF (Formula.not (Formula.eq (Term.var 241) (numeral 0)))
          (andF (eqCcons outC (numeral 3) (cconsTerm (Term.var 241) (Term.var 243)))
            (andF (ltF (Term.var 244) i)
              (betaF c d (Term.var 244)
                (cconsTerm (Term.var 242) (Term.var 243)))))))))))

def formSubstJust (c d i ncode inC outC : Term) : Formula :=
  orF (formSubstEqCase ncode inC outC)
    (orF (formSubstNotCase c d i inC outC)
      (orF (formSubstImpCase c d i inC outC)
        (formSubstAllCase c d i inC outC)))

def formSubstClosed (x z ncode : Term) : Formula :=
  existsF 250 (existsF 251 (existsF 252
    (andF (betaF (Term.var 250) (Term.var 251) (Term.var 252)
        (cconsTerm x z))
      (Formula.all 253 (Formula.imp (leF (Term.var 253) (Term.var 252))
        (existsF 254 (existsF 255
          (andF (betaF (Term.var 250) (Term.var 251) (Term.var 253)
              (cconsTerm (Term.var 254) (Term.var 255)))
            (formSubstJust (Term.var 250) (Term.var 251) (Term.var 253)
              ncode (Term.var 254) (Term.var 255))))))))))

def formSubstEqCaseAt (x u inC outC : Term) : Formula :=
  existsF 261 (existsF 262 (existsF 263 (existsF 264
    (andF (eqCcons inC (numeral 0) (cconsTerm (Term.var 261) (Term.var 262)))
      (andF (eqCcons outC (numeral 0) (cconsTerm (Term.var 263) (Term.var 264)))
        (andF (termSubstClosedAt (Term.var 261) (Term.var 263) x u)
          (termSubstClosedAt (Term.var 262) (Term.var 264) x u)))))))

def formSubstAllCaseAt (c d i x inC outC : Term) : Formula :=
  existsF 261 (existsF 262 (existsF 263 (existsF 264
    (andF (eqCcons inC (numeral 3) (cconsTerm (Term.var 261) (Term.var 262)))
      (orF (andF (Formula.eq (Term.var 261) x) (Formula.eq outC inC))
        (andF (Formula.not (Formula.eq (Term.var 261) x))
          (andF (eqCcons outC (numeral 3) (cconsTerm (Term.var 261) (Term.var 263)))
            (andF (ltF (Term.var 264) i)
              (betaF c d (Term.var 264)
                (cconsTerm (Term.var 262) (Term.var 263)))))))))))

def formSubstJustAt (c d i x u inC outC : Term) : Formula :=
  orF (formSubstEqCaseAt x u inC outC)
    (orF (formSubstNotCase c d i inC outC)
      (orF (formSubstImpCase c d i inC outC)
        (formSubstAllCaseAt c d i x inC outC)))

def formSubstAtClosed (body outC x u : Term) : Formula :=
  existsF 270 (existsF 271 (existsF 272
    (andF (betaF (Term.var 270) (Term.var 271) (Term.var 272)
        (cconsTerm body outC))
      (Formula.all 273 (Formula.imp (leF (Term.var 273) (Term.var 272))
        (existsF 274 (existsF 275
          (andF (betaF (Term.var 270) (Term.var 271) (Term.var 273)
              (cconsTerm (Term.var 274) (Term.var 275)))
            (formSubstJustAt (Term.var 270) (Term.var 271) (Term.var 273)
              x u (Term.var 274) (Term.var 275))))))))))

/-- Subterm table with no variable nodes: the term is closed. -/
def termNodeClosedF (c d i : Term) : Formula :=
  existsF 284
    (andF (betaF c d i (Term.var 284))
      (orF (eqCcons (Term.var 284) (numeral 0) (numeral 0))
        (orF (existsF 285 (existsF 286
              (andF (eqCcons (Term.var 284) (numeral 1) (Term.var 285))
                (andF (ltF (Term.var 286) i)
                  (betaF c d (Term.var 286) (Term.var 285))))))
          (orF (existsF 285 (existsF 286 (existsF 287 (existsF 288
                (andF (eqCcons (Term.var 284) (numeral 2)
                    (cconsTerm (Term.var 285) (Term.var 286)))
                  (andF (ltF (Term.var 287) i)
                    (andF (ltF (Term.var 288) i)
                      (andF (betaF c d (Term.var 287) (Term.var 285))
                        (betaF c d (Term.var 288) (Term.var 286))))))))))
            (existsF 285 (existsF 286 (existsF 287 (existsF 288
              (andF (eqCcons (Term.var 284) (numeral 3)
                  (cconsTerm (Term.var 285) (Term.var 286)))
                (andF (ltF (Term.var 287) i)
                  (andF (ltF (Term.var 288) i)
                    (andF (betaF c d (Term.var 287) (Term.var 285))
                      (betaF c d (Term.var 288) (Term.var 286))))))))))))))

def termClosedPack (t : Term) : Formula :=
  existsF 280 (existsF 281 (existsF 282
    (andF (betaF (Term.var 280) (Term.var 281) (Term.var 282) t)
      (Formula.all 283 (Formula.imp (leF (Term.var 283) (Term.var 282))
        (termNodeClosedF (Term.var 280) (Term.var 281) (Term.var 283)))))))

def specJustF (c d i : Term) : Formula :=
  existsF 55 (existsF 61 (existsF 62 (existsF 63 (existsF 64 (existsF 65
    (andF (betaF c d i (Term.var 55))
      (andF (ltF (Term.var 61) i)
        (andF (betaF c d (Term.var 61) (Term.var 62))
          (andF (eqCcons (Term.var 62) (numeral 3)
              (cconsTerm (Term.var 63) (Term.var 64)))
            (andF (formSubstAtClosed (Term.var 64) (Term.var 55)
                (Term.var 63) (Term.var 65))
              (termClosedPack (Term.var 65))))))))))))

/-- `proofRel s t`: `s` packs β-codes `(c,d,L)` of a Hilbert sequence
ending at `t`, including axiom, MP, generalization, and closed
instantiation. -/
def proofRel (s t : Term) : Formula :=
  existsF 40 (existsF 41 (existsF 42
    (andF (eqCcons s (Term.var 40) (cconsTerm (Term.var 41) (Term.var 42)))
      (andF (betaF (Term.var 40) (Term.var 41) (Term.var 42) t)
        (Formula.all 43 (Formula.imp (leF (Term.var 43) (Term.var 42))
          (orF (justifiedF (Term.var 40) (Term.var 41) (Term.var 43))
            (specJustF (Term.var 40) (Term.var 41) (Term.var 43)))))))))

/-- Graph of `substFormCode` on the standard model. -/
def substRel (x y z : Term) : Formula :=
  existsF 210
    (andF (numCodeRel y (Term.var 210))
      (formSubstClosed x z (Term.var 210)))

def bewOf (φ : Formula) : Formula :=
  existsF 0 (proofRel (Term.var 0) (numeral (formulaCode φ)))

def ConQ : Formula :=
  Formula.not (bewOf falsum)

theorem isProofCode_of_provable {φ : Formula} (h : Provable φ) :
    ∃ n : Nat, isProofCode n (formulaCode φ) = true := by
  rcases h with ⟨p, hp⟩
  exact ⟨encodeProof p, isProofCode_valid hp⟩

theorem provable_of_isProofCode {φ : Formula} {n : Nat}
    (h : isProofCode n (formulaCode φ) = true) : Provable φ := by
  rcases isProofCode_none n (formulaCode φ) h with ⟨p, ψ, _hp, hψ, hchk⟩
  have : ψ = φ := by
    have hφ' : decodeFormula? (formulaCode φ) = some φ := by
      rw [formulaCode_eq]
      exact decodeFormula?_encode φ
    exact Option.some.inj (hψ.symm.trans hφ')
  subst this
  exact ⟨p, hchk⟩

theorem isProofCode_iff_provable (φ : Formula) :
    (∃ n : Nat, isProofCode n (formulaCode φ) = true) ↔ Provable φ := by
  constructor
  · intro ⟨n, hn⟩
    exact provable_of_isProofCode hn
  · exact isProofCode_of_provable

theorem isProofCode_ax (φ : Formula) (h : isAxiom φ = true) :
    isProofCode (encodeProof (.ax φ)) (encodeFormula φ) = true :=
  (isProofCode_iff (.ax φ) φ).2 (by simp [check, h])

/-- Diagonal matrix B(x) = ¬∃p,z. substRel(x,x,z) ∧ proofRel(p,z). -/
def godelMatrix : Formula :=
  Formula.not (existsF 1 (existsF 2
    (andF (substRel (Term.var 0) (Term.var 0) (Term.var 2))
      (proofRel (Term.var 1) (Term.var 2)))))

def godelMatrixCode : Nat :=
  formulaCode godelMatrix

theorem godelMatrixCode_eq : godelMatrixCode = formulaCode godelMatrix :=
  rfl

theorem decode_godelMatrix :
    decodeFormula? godelMatrixCode = some godelMatrix :=
  decodeFormula?_formulaCode godelMatrix

def arithGodelSentence : Formula :=
  substNum godelMatrix godelMatrixCode

theorem arithGodel_code :
    formulaCode arithGodelSentence =
      codeSubstNat godelMatrixCode godelMatrixCode :=
  (codeSubstNat_formulaCode godelMatrix godelMatrixCode).symm

theorem arithGodel_eq_subst :
    arithGodelSentence = substNum godelMatrix godelMatrixCode :=
  rfl

theorem diagonal_code_identity :
    codeSubstNat godelMatrixCode godelMatrixCode =
      formulaCode arithGodelSentence :=
  arithGodel_code.symm

theorem substTermCode_encode (y : Nat) :
    ∀ t : Term, substTermCode y (encodeTerm t) = encodeTerm (substTerm 0 (numeral y) t)
  | zero => by
    have hne : ccons 0 0 ≠ 0 := ccons_ne_zero 0 0
    rw [encodeTerm, substTerm, substTermCode, dif_neg hne]
    simp [uncpair_pred_ccons, encodeTerm]
  | succ t => by
    have hne : ccons 1 (encodeTerm t) ≠ 0 := ccons_ne_zero _ _
    have ih := substTermCode_encode y t
    rw [encodeTerm, substTerm, substTermCode, dif_neg hne]
    simp [uncpair_pred_ccons, ih, encodeTerm]
  | add s t => by
    have hne : ccons 2 (ccons (encodeTerm s) (encodeTerm t)) ≠ 0 := ccons_ne_zero _ _
    have hne2 : ccons (encodeTerm s) (encodeTerm t) ≠ 0 := ccons_ne_zero _ _
    have ihs := substTermCode_encode y s
    have iht := substTermCode_encode y t
    rw [encodeTerm, substTerm, substTermCode, dif_neg hne]
    simp [uncpair_pred_ccons, hne2, ihs, iht, encodeTerm]
  | mul s t => by
    have hne : ccons 3 (ccons (encodeTerm s) (encodeTerm t)) ≠ 0 := ccons_ne_zero _ _
    have hne2 : ccons (encodeTerm s) (encodeTerm t) ≠ 0 := ccons_ne_zero _ _
    have ihs := substTermCode_encode y s
    have iht := substTermCode_encode y t
    rw [encodeTerm, substTerm, substTermCode, dif_neg hne]
    simp [uncpair_pred_ccons, hne2, ihs, iht, encodeTerm]
  | var n => by
    have hne : ccons 4 n ≠ 0 := ccons_ne_zero _ _
    cases n with
    | zero =>
      rw [encodeTerm, substTerm, substTermCode, dif_neg hne]
      simp [uncpair_pred_ccons, encodeTerm_numeral_eq_numCode]
    | succ n =>
      rw [encodeTerm, substTerm, substTermCode, dif_neg hne]
      simp [uncpair_pred_ccons, encodeTerm]

theorem substFormCode_encode (y : Nat) :
    ∀ φ : Formula, substFormCode y (encodeFormula φ) = encodeFormula (substNum φ y)
  | Formula.eq s t => by
    have hne : ccons 0 (ccons (encodeTerm s) (encodeTerm t)) ≠ 0 := ccons_ne_zero _ _
    have hne2 : ccons (encodeTerm s) (encodeTerm t) ≠ 0 := ccons_ne_zero _ _
    rw [encodeFormula, substNum, substForm, substFormCode, dif_neg hne]
    simp [uncpair_pred_ccons, hne2, substTermCode_encode, encodeFormula]
  | Formula.not φ => by
    have hne : ccons 1 (encodeFormula φ) ≠ 0 := ccons_ne_zero _ _
    have ih := substFormCode_encode y φ
    rw [encodeFormula, substNum, substForm, substFormCode, dif_neg hne]
    simp [uncpair_pred_ccons, ih, encodeFormula, substNum]
  | Formula.imp a b => by
    have hne : ccons 2 (ccons (encodeFormula a) (encodeFormula b)) ≠ 0 := ccons_ne_zero _ _
    have hne2 : ccons (encodeFormula a) (encodeFormula b) ≠ 0 := ccons_ne_zero _ _
    have iha := substFormCode_encode y a
    have ihb := substFormCode_encode y b
    rw [encodeFormula, substNum, substForm, substFormCode, dif_neg hne]
    simp [uncpair_pred_ccons, hne2, iha, ihb, encodeFormula, substNum]
  | Formula.all x φ => by
    have hne : ccons 3 (ccons x (encodeFormula φ)) ≠ 0 := ccons_ne_zero _ _
    have hne2 : ccons x (encodeFormula φ) ≠ 0 := ccons_ne_zero _ _
    have ih := substFormCode_encode y φ
    rw [encodeFormula, substNum, substForm, substFormCode, dif_neg hne]
    simp [uncpair_pred_ccons, hne2]
    by_cases hx : x = 0
    · subst hx
      simp [encodeFormula]
    · simp [hx, ih, encodeFormula, substNum]

theorem substFormCode_formulaCode (y : Nat) (φ : Formula) :
    substFormCode y (formulaCode φ) = formulaCode (substNum φ y) := by
  rw [formulaCode_eq, formulaCode_eq]
  exact substFormCode_encode y φ

theorem codeSubstNat_eq_substFormCode (φ : Formula) (y : Nat) :
    codeSubstNat (formulaCode φ) y = substFormCode y (formulaCode φ) := by
  rw [codeSubstNat_formulaCode, substFormCode_formulaCode]

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
