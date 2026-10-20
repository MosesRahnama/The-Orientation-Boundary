set_option autoImplicit false

/-!
# Pairing, sequence codes, a basic combinator fragment, and Nat iteration

Cantor-free injective pairing `npair a b = 2^a * (2b+1)` with an explicit
inverse on the image. The custom `PR` datatype below is only a basic
zero/successor/projection/constant/pair/composition fragment; pairing is a
primitive constructor of that datatype and there is no primitive-recursion
constructor. The separate Lean-level `natIter` supplies an explicit recursion
schema for arithmetic examples. Accordingly this file does not by itself prove
that later syntax/coding functions are primitive recursive in the standard
closure sense. Nothing here is an incompleteness theorem.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- Injective pairing into positive naturals. -/
def npair (a b : Nat) : Nat := 2 ^ a * (2 * b + 1)

theorem npair_pos (a b : Nat) : 0 < npair a b := by
  unfold npair
  have hpow : 0 < 2 ^ a := Nat.pow_pos (by decide : 0 < 2)
  have hodd : 0 < 2 * b + 1 := by omega
  exact Nat.mul_pos hpow hodd

theorem npair_ne_zero (a b : Nat) : npair a b ≠ 0 :=
  Nat.ne_of_gt (npair_pos a b)

def nval2 (n : Nat) : Nat :=
  if h : n = 0 then 0
  else if n % 2 = 0 then nval2 (n / 2) + 1 else 0
termination_by n
decreasing_by
  have hpos : 0 < n := Nat.pos_of_ne_zero h
  exact Nat.div_lt_self hpos (by decide : 1 < 2)

theorem nval2_zero : nval2 0 = 0 := by
  simp [nval2]

theorem nval2_odd (k : Nat) : nval2 (2 * k + 1) = 0 := by
  have hne : 2 * k + 1 ≠ 0 := by omega
  have hodd : ¬ ((2 * k + 1) % 2 = 0) := by omega
  rw [nval2, dif_neg hne, if_neg hodd]

theorem npair_succ_left (a b : Nat) :
    npair (a + 1) b = 2 * npair a b := by
  unfold npair
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]

theorem nval2_npair (a b : Nat) : nval2 (npair a b) = a := by
  induction a with
  | zero =>
    unfold npair
    simp only [Nat.pow_zero, Nat.one_mul]
    exact nval2_odd b
  | succ a ih =>
    have hpos : npair (a + 1) b ≠ 0 := npair_ne_zero (a + 1) b
    have heven : npair (a + 1) b % 2 = 0 := by
      rw [npair_succ_left]
      omega
    have hdiv : npair (a + 1) b / 2 = npair a b := by
      rw [npair_succ_left]
      exact Nat.mul_div_right _ (by decide : 0 < 2)
    rw [nval2, dif_neg hpos, if_pos heven, hdiv, ih]

theorem npair_div_pow (a b : Nat) :
    npair a b / 2 ^ a = 2 * b + 1 := by
  unfold npair
  exact Nat.mul_div_right (2 * b + 1) (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ a)

/-- Inverse of `npair` on its image; `(0,0)` on the missing `0`. -/
def nunpair (n : Nat) : Nat × Nat :=
  if n = 0 then (0, 0)
  else
    let a := nval2 n
    (a, (n / 2 ^ a) / 2)

theorem nunpair_npair (a b : Nat) : nunpair (npair a b) = (a, b) := by
  have hne : npair a b ≠ 0 := npair_ne_zero a b
  simp [nunpair, hne, nval2_npair, npair_div_pow]
  omega

theorem npair_injective {a b c d : Nat}
    (h : npair a b = npair c d) : a = c ∧ b = d := by
  have h1 := congrArg nunpair h
  rw [nunpair_npair, nunpair_npair] at h1
  exact Prod.ext_iff.mp h1

theorem npair_left_injective (b : Nat) (a c : Nat)
    (h : npair a b = npair c b) : a = c :=
  (npair_injective h).1

theorem npair_right_injective (a : Nat) (b d : Nat)
    (h : npair a b = npair a d) : b = d :=
  (npair_injective h).2

/-- Concrete pairing witnesses. -/
def pairWitnessA : Nat := npair 0 0

def pairWitnessB : Nat := npair 1 2

theorem pairWitnessA_eq : pairWitnessA = 1 := by
  simp [pairWitnessA, npair]

theorem pairWitnessB_eq : pairWitnessB = 10 := by
  simp [pairWitnessB, npair]

theorem pairWitnessA_ne_B : pairWitnessA ≠ pairWitnessB := by
  simp [pairWitnessA_eq, pairWitnessB_eq]

theorem nunpair_zero : nunpair 0 = (0, 0) := rfl

/-- Zero is not a pairing code. -/
theorem zero_not_in_npair_image : ∀ a b : Nat, npair a b ≠ 0 :=
  npair_ne_zero

/-- Nested pairing for finite sequences: `ncons head tail`. -/
def ncons (head tail : Nat) : Nat := npair head tail

def nhead (s : Nat) : Nat := (nunpair s).1

def ntail (s : Nat) : Nat := (nunpair s).2

theorem nhead_ncons (h t : Nat) : nhead (ncons h t) = h := by
  simp [nhead, ncons, nunpair_npair]

theorem ntail_ncons (h t : Nat) : ntail (ncons h t) = t := by
  simp [ntail, ncons, nunpair_npair]

/-- `nthSeq s i` walks `i` tails then takes the head. -/
def nthSeq (s i : Nat) : Nat :=
  match i with
  | 0 => nhead s
  | n + 1 => nthSeq (ntail s) n

theorem nthSeq_ncons_zero (h t : Nat) : nthSeq (ncons h t) 0 = h :=
  nhead_ncons h t

theorem nthSeq_ncons_succ (h t i : Nat) :
    nthSeq (ncons h t) (i + 1) = nthSeq t i := by
  simp [nthSeq, ntail_ncons]

/-- Encode a finite list by right-nested pairing, ending at `0`. -/
def encodeList : List Nat → Nat
  | [] => 0
  | x :: xs => ncons x (encodeList xs)

def decodeList : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, s =>
      if s = 0 then []
      else nhead s :: decodeList fuel (ntail s)

theorem decodeList_encodeList :
    ∀ xs : List Nat, decodeList (xs.length + 1) (encodeList xs) = xs
  | [] => rfl
  | x :: xs => by
    have hne : ncons x (encodeList xs) ≠ 0 := npair_ne_zero x (encodeList xs)
    change decodeList (xs.length + 2) (ncons x (encodeList xs)) = x :: xs
    rw [decodeList, if_neg hne, nhead_ncons, ntail_ncons]
    exact congrArg (List.cons x) (decodeList_encodeList xs)

theorem encodeList_injective {xs ys : List Nat}
    (h : encodeList xs = encodeList ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have : False := npair_ne_zero y (encodeList ys) h.symm
      exact this.elim
  | cons x xs ih =>
    cases ys with
    | nil =>
      have : False := npair_ne_zero x (encodeList xs) h
      exact this.elim
    | cons y ys =>
      have hp := npair_injective (by simpa [encodeList, ncons] using h)
      cases hp.1
      exact congrArg (List.cons x) (ih hp.2)

/-! ## Basic combinator fragment (`PR` is a historical mnemonic, not a complete PR algebra) -/

/-- Basic unary/binary combinator syntax on `Nat`; no recursion constructor. -/
inductive PR : Type
  | zero : PR
  | succ : PR
  | proj : Nat → PR
  | const : Nat → PR
  | pair : PR → PR → PR
  | comp : PR → PR → PR
  deriving DecidableEq, Repr

/-- Evaluate a combinator on a finite environment encoded as a list. -/
def evalPR : PR → List Nat → Nat
  | .zero, _ => 0
  | .succ, x :: _ => x + 1
  | .succ, [] => 1
  | .proj i, env => env.getD i 0
  | .const n, _ => n
  | .pair f g, env => npair (evalPR f env) (evalPR g env)
  | .comp f g, env => evalPR f [evalPR g env]

theorem evalPR_zero (env : List Nat) : evalPR .zero env = 0 := rfl

theorem evalPR_succ (x : Nat) (xs : List Nat) :
    evalPR .succ (x :: xs) = x + 1 :=
  rfl

theorem evalPR_const (n : Nat) (env : List Nat) :
    evalPR (.const n) env = n :=
  rfl

theorem evalPR_proj_head (x : Nat) (xs : List Nat) :
    evalPR (.proj 0) (x :: xs) = x :=
  rfl

theorem evalPR_pair (f g : PR) (env : List Nat) :
    evalPR (.pair f g) env = npair (evalPR f env) (evalPR g env) :=
  rfl

/-- Successor as a PR combinator, witnessed on a concrete input. -/
def prSucc : PR := .succ

theorem prSucc_eval (n : Nat) : evalPR prSucc [n] = n + 1 := rfl

/-- Pairing is PR. -/
def prPair : PR := .pair (.proj 0) (.proj 1)

theorem prPair_eval (a b : Nat) : evalPR prPair [a, b] = npair a b := rfl

/-- The identity combinator. -/
def prId : PR := .proj 0

theorem prId_eval (n : Nat) : evalPR prId [n] = n := rfl

/-- Composition of successor with itself is PR and equals plus-two. -/
def prPlusTwo : PR := .comp .succ .succ

theorem prPlusTwo_eval (n : Nat) : evalPR prPlusTwo [n] = n + 2 := rfl

/-- Primitive recursion schema on `Nat`, the meta-level recursor. -/
def natIter (base : Nat) (step : Nat → Nat) : Nat → Nat
  | 0 => base
  | n + 1 => step (natIter base step n)

theorem natIter_zero (base : Nat) (step : Nat → Nat) :
    natIter base step 0 = base :=
  rfl

theorem natIter_succ (base : Nat) (step : Nat → Nat) (n : Nat) :
    natIter base step (n + 1) = step (natIter base step n) :=
  rfl

theorem add_as_natIter (n m : Nat) :
    natIter m Nat.succ n = n + m := by
  induction n with
  | zero => simp [natIter]
  | succ n ih =>
    simp [natIter, ih]
    omega

/-- `npair` is available because pairing is primitive in this custom fragment. -/
theorem npair_in_basic_fragment (a b : Nat) :
    ∃ e : PR, evalPR e [a, b] = npair a b :=
  ⟨prPair, prPair_eval a b⟩

/-- `Nat.succ` is available in the custom basic fragment. -/
theorem succ_in_basic_fragment (n : Nat) :
    ∃ e : PR, evalPR e [n] = n + 1 :=
  ⟨prSucc, prSucc_eval n⟩

/-- Addition is obtained from the separate Lean-level Nat iteration schema. -/
theorem add_via_natIter_schema (n m : Nat) :
    natIter m Nat.succ n = n + m :=
  add_as_natIter n m

/-- Distinct combinators can agree extensionally (projection vs identity). -/
theorem pr_extensional_collision :
    evalPR prId [3] = evalPR (.proj 0) [3] :=
  rfl

/-- Distinct combinators can disagree: successor is not identity. -/
theorem prSucc_ne_prId_at_zero : evalPR prSucc [0] ≠ evalPR prId [0] := by
  decide

/-! ## Polynomial pairing for later object-language representation -/

/-- Injective pairing by squares: `cpair a b = (a+b)² + b`. -/
def cpair (a b : Nat) : Nat := (a + b) * (a + b) + b

theorem sq_ge_self (s : Nat) : s ≤ s * s := by
  cases s with
  | zero => exact Nat.zero_le _
  | succ s => exact Nat.le_mul_of_pos_right (s + 1) (Nat.succ_pos _)

theorem cpair_ge_right (a b : Nat) : b ≤ cpair a b := by
  simp [cpair]

theorem cpair_ge_left (a b : Nat) : a ≤ cpair a b := by
  have h1 : a ≤ a + b := Nat.le_add_right a b
  have h2 : a + b ≤ (a + b) * (a + b) := sq_ge_self (a + b)
  have h3 : (a + b) * (a + b) ≤ cpair a b := Nat.le_add_right _ b
  exact Nat.le_trans h1 (Nat.le_trans h2 h3)

theorem cpair_sum_le (a b : Nat) : a + b ≤ cpair a b := by
  have h2 : a + b ≤ (a + b) * (a + b) := sq_ge_self (a + b)
  have h3 : (a + b) * (a + b) ≤ cpair a b := Nat.le_add_right _ b
  exact Nat.le_trans h2 h3

theorem add_one_sq (s : Nat) : (s + 1) * (s + 1) = s * s + s + s + 1 := by
  rw [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]
  omega

theorem cpair_lt_succ_square (a b : Nat) :
    cpair a b < (a + b + 1) * (a + b + 1) := by
  rw [add_one_sq]
  simp only [cpair]
  have hrhs :
      (a + b) * (a + b) + (a + b) + (a + b) + 1 =
        (a + b) * (a + b) + (a + b + (a + b) + 1) := by
    omega
  have hlt : b < a + b + (a + b) + 1 := by
    have : b ≤ a + b := Nat.le_add_left b a
    exact Nat.lt_succ_of_le (Nat.le_trans this (Nat.le_add_right (a + b) (a + b)))
  rw [hrhs]
  exact Nat.add_lt_add_left hlt ((a + b) * (a + b))

theorem cpair_injective {a b c d : Nat}
    (h : cpair a b = cpair c d) : a = c ∧ b = d := by
  have hn : (a + b) * (a + b) + b = (c + d) * (c + d) + d := by
    simpa [cpair] using h
  have hst : a + b = c + d := by
    cases Nat.lt_trichotomy (a + b) (c + d) with
    | inl hlt =>
      have hmul : (a + b + 1) * (a + b + 1) ≤ (c + d) * (c + d) :=
        Nat.mul_le_mul hlt hlt
      have hlo : (a + b + 1) * (a + b + 1) ≤ (c + d) * (c + d) + d :=
        Nat.le_trans hmul (Nat.le_add_right _ d)
      have hhi : (a + b) * (a + b) + b < (a + b + 1) * (a + b + 1) :=
        cpair_lt_succ_square a b
      exact (Nat.not_le_of_gt hhi (hn.symm ▸ hlo)).elim
    | inr hrest =>
      cases hrest with
      | inl heq => exact heq
      | inr hgt =>
        have hmul : (c + d + 1) * (c + d + 1) ≤ (a + b) * (a + b) :=
          Nat.mul_le_mul hgt hgt
        have hlo : (c + d + 1) * (c + d + 1) ≤ (a + b) * (a + b) + b :=
          Nat.le_trans hmul (Nat.le_add_right _ b)
        have hhi : (c + d) * (c + d) + d < (c + d + 1) * (c + d + 1) :=
          cpair_lt_succ_square c d
        exact (Nat.not_le_of_gt hhi (hn ▸ hlo)).elim
  have hb : b = d := by
    have : (a + b) * (a + b) + b = (a + b) * (a + b) + d := by
      simpa [hst] using hn
    exact Nat.add_left_cancel this
  have ha : a = c := by
    have : a + b = c + b := by simpa [hb] using hst
    exact Nat.add_right_cancel this
  exact ⟨ha, hb⟩

/-- Search downward for the unique `s` with `s² ≤ n` and `n - s² ≤ s`. -/
def uncpairGo : Nat → Nat → Nat × Nat
  | 0, _ => (0, 0)
  | s + 1, n =>
      if _h : s * s ≤ n ∧ n - s * s ≤ s then
        (s - (n - s * s), n - s * s)
      else
        uncpairGo s n

def uncpair (n : Nat) : Nat × Nat :=
  uncpairGo (n + 1) n

theorem uncpairGo_at_sum (a b : Nat) :
    uncpairGo (a + b + 1) (cpair a b) = (a, b) := by
  have hs : (a + b) * (a + b) ≤ cpair a b := Nat.le_add_right _ b
  have hr : cpair a b - (a + b) * (a + b) = b := Nat.add_sub_cancel_left _ b
  have hble : b ≤ a + b := Nat.le_add_left b a
  have hcond : (a + b) * (a + b) ≤ cpair a b ∧
      cpair a b - (a + b) * (a + b) ≤ a + b :=
    ⟨hs, hr.symm ▸ hble⟩
  change (if h : (a + b) * (a + b) ≤ cpair a b ∧
      cpair a b - (a + b) * (a + b) ≤ a + b then
      (a + b - (cpair a b - (a + b) * (a + b)),
        cpair a b - (a + b) * (a + b))
    else uncpairGo (a + b) (cpair a b)) = (a, b)
  rw [dif_pos hcond, hr, Nat.add_sub_cancel]

theorem uncpairGo_skip {a b s : Nat} (hgt : a + b < s) :
    uncpairGo (s + 1) (cpair a b) = uncpairGo s (cpair a b) := by
  have hneg : ¬ ((s * s ≤ cpair a b) ∧ (cpair a b - s * s ≤ s)) := by
    intro hcond
    have hsq := hcond.1
    have hle : a + b + 1 ≤ s := hgt
    have hmul : (a + b + 1) * (a + b + 1) ≤ s * s := Nat.mul_le_mul hle hle
    have : (a + b + 1) * (a + b + 1) ≤ cpair a b := Nat.le_trans hmul hsq
    exact Nat.not_le_of_gt (cpair_lt_succ_square a b) this
  change (if h : (s * s ≤ cpair a b) ∧ (cpair a b - s * s ≤ s) then
      (s - (cpair a b - s * s), cpair a b - s * s)
    else uncpairGo s (cpair a b)) = uncpairGo s (cpair a b)
  rw [dif_neg hneg]

theorem uncpairGo_hit (a b fuel : Nat) (hfuel : a + b < fuel) :
    uncpairGo fuel (cpair a b) = (a, b) := by
  induction fuel with
  | zero => exact (Nat.not_lt_zero _ hfuel).elim
  | succ fuel ih =>
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hfuel) with
    | inl heq =>
      have : fuel = a + b := heq.symm
      subst this
      simpa using uncpairGo_at_sum a b
    | inr hlt =>
      have hskip := uncpairGo_skip (a := a) (b := b) (s := fuel) hlt
      exact hskip.trans (ih hlt)

theorem uncpair_cpair (a b : Nat) : uncpair (cpair a b) = (a, b) :=
  uncpairGo_hit a b (cpair a b + 1) (Nat.lt_succ_of_le (cpair_sum_le a b))

/-- Cons for polynomial list codes; `0` is nil. -/
def ccons (head tail : Nat) : Nat := cpair head tail + 1

theorem ccons_ne_zero (h t : Nat) : ccons h t ≠ 0 := by
  simp [ccons]

theorem ccons_gt_head (h t : Nat) : h < ccons h t :=
  Nat.lt_of_le_of_lt (cpair_ge_left h t) (Nat.lt_succ_self _)

theorem ccons_gt_tail (h t : Nat) : t < ccons h t :=
  Nat.lt_of_le_of_lt (cpair_ge_right h t) (Nat.lt_succ_self _)

theorem ccons_injective {a b c d : Nat}
    (h : ccons a b = ccons c d) : a = c ∧ b = d := by
  have : cpair a b = cpair c d := by
    simp [ccons] at h
    omega
  exact cpair_injective this

theorem uncpair_pred_ccons (h t : Nat) :
    uncpair (ccons h t - 1) = (h, t) := by
  simp [ccons, uncpair_cpair]

def cencodeList : List Nat → Nat
  | [] => 0
  | x :: xs => ccons x (cencodeList xs)

theorem cencodeList_nil : cencodeList [] = 0 := rfl

theorem cencodeList_cons (x : Nat) (xs : List Nat) :
    cencodeList (x :: xs) = ccons x (cencodeList xs) :=
  rfl

theorem cencodeList_injective {xs ys : List Nat}
    (h : cencodeList xs = cencodeList ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have : False := ccons_ne_zero y (cencodeList ys) h.symm
      exact this.elim
  | cons x xs ih =>
    cases ys with
    | nil =>
      have : False := ccons_ne_zero x (cencodeList xs) h
      exact this.elim
    | cons y ys =>
      have hp := cpair_injective (by
        have : cpair x (cencodeList xs) + 1 = cpair y (cencodeList ys) + 1 := by
          simpa [cencodeList, ccons] using h
        exact Nat.succ.inj this)
      cases hp.1
      exact congrArg (List.cons x) (ih hp.2)

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
