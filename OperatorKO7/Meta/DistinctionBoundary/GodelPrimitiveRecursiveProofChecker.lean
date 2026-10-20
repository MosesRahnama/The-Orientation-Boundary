import OperatorKO7.Meta.DistinctionBoundary.GodelPrimitiveRecursiveSubstitution

set_option autoImplicit false

/-!
# Primitive-recursive proof-checker closure

This module completes the recursive arithmetic layer required by the live
proof checker.  It first compiles arbitrary closed-term substitution on the
existing Gödel codes.  It then gives a numeric checker for the exact encoded
proof-tree constructors.  The checker returns `0` on rejection and
`encodeFormula φ + 1` on an accepted proof of `φ`.  The offset makes rejection
disjoint from every formula code.

The canonical theorem compares the numeric checker with `check` on every
encoded `ProofTree`; no malformed-code behavior is used to justify a proof.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-! ## Arbitrary syntactic substitution on codes -/

/-- Replace variable `x` by the already-coded term `u` in a term code. -/
def substTermAtCode (x u n : Nat) : Nat :=
  if h : n = 0 then 0
  else
    let p := uncpair (n - 1)
    match p.1 with
    | 0 => if p.2 = 0 then ccons 0 0 else 0
    | 1 => ccons 1 (substTermAtCode x u p.2)
    | 2 =>
      if p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        ccons 2 (ccons (substTermAtCode x u q.1) (substTermAtCode x u q.2))
    | 3 =>
      if p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        ccons 3 (ccons (substTermAtCode x u q.1) (substTermAtCode x u q.2))
    | 4 => if p.2 = x then u else n
    | _ => 0
termination_by n
decreasing_by
  · exact (uncpair_lt n h).2
  · have hp : p.2 ≠ 0 := by
      intro hz
      simp [hz] at ‹p.2 ≠ 0›
    exact Nat.lt_trans (uncpair_lt p.2 hp).1 (uncpair_lt n h).2
  · have hp : p.2 ≠ 0 := by
      intro hz
      simp [hz] at ‹p.2 ≠ 0›
    exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2
  · have hp : p.2 ≠ 0 := by
      intro hz
      simp [hz] at ‹p.2 ≠ 0›
    exact Nat.lt_trans (uncpair_lt p.2 hp).1 (uncpair_lt n h).2
  · have hp : p.2 ≠ 0 := by
      intro hz
      simp [hz] at ‹p.2 ≠ 0›
    exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2

/-- Replace variable `x` by the already-coded term `u` in a formula code. -/
def substFormAtCode (x u n : Nat) : Nat :=
  if h : n = 0 then 0
  else
    let p := uncpair (n - 1)
    match p.1 with
    | 0 =>
      if p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        ccons 0 (ccons (substTermAtCode x u q.1) (substTermAtCode x u q.2))
    | 1 => ccons 1 (substFormAtCode x u p.2)
    | 2 =>
      if p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        ccons 2 (ccons (substFormAtCode x u q.1) (substFormAtCode x u q.2))
    | 3 =>
      if p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        if q.1 = x then n else ccons 3 (ccons q.1 (substFormAtCode x u q.2))
    | _ => 0
termination_by n
decreasing_by
  · exact (uncpair_lt n h).2
  · have hp : p.2 ≠ 0 := by
      intro hz
      simp [hz] at ‹p.2 ≠ 0›
    exact Nat.lt_trans (uncpair_lt p.2 hp).1 (uncpair_lt n h).2
  · have hp : p.2 ≠ 0 := by
      intro hz
      simp [hz] at ‹p.2 ≠ 0›
    exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2
  · have hp : p.2 ≠ 0 := by
      intro hz
      simp [hz] at ‹p.2 ≠ 0›
    exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2

/-- General term substitution computes the live syntactic substitution on an
encoded term. -/
theorem substTermAtCode_encode (x : Nat) (u t : Term) :
    substTermAtCode x (encodeTerm u) (encodeTerm t) = encodeTerm (substTerm x u t) := by
  induction t with
  | zero => simp [substTermAtCode, encodeTerm, substTerm, ccons_ne_zero, uncpair_pred_ccons]
  | succ t ih => simp [substTermAtCode, encodeTerm, substTerm, ccons_ne_zero, uncpair_pred_ccons, ih]
  | add a b iha ihb =>
      simp [substTermAtCode, encodeTerm, substTerm, ccons_ne_zero, uncpair_pred_ccons, iha, ihb]
  | mul a b iha ihb =>
      simp [substTermAtCode, encodeTerm, substTerm, ccons_ne_zero, uncpair_pred_ccons, iha, ihb]
  | var y =>
      by_cases hxy : y = x
      · subst hxy
        simp [substTermAtCode, encodeTerm, substTerm, ccons_ne_zero, uncpair_pred_ccons]
      · simp [substTermAtCode, encodeTerm, substTerm, ccons_ne_zero, uncpair_pred_ccons, hxy]

/-- General formula substitution computes the live syntactic substitution on
an encoded formula. -/
theorem substFormAtCode_encode (x : Nat) (u : Term) (φ : Formula) :
    substFormAtCode x (encodeTerm u) (encodeFormula φ) = encodeFormula (substForm x u φ) := by
  induction φ with
  | eq a b =>
      simp [substFormAtCode, encodeFormula, substForm, ccons_ne_zero,
        uncpair_pred_ccons, substTermAtCode_encode]
  | not φ ih =>
      simp [substFormAtCode, encodeFormula, substForm, ccons_ne_zero, uncpair_pred_ccons, ih]
  | imp a b iha ihb =>
      simp [substFormAtCode, encodeFormula, substForm, ccons_ne_zero, uncpair_pred_ccons, iha, ihb]
  | all y φ ih =>
      by_cases hyx : y = x
      · subst hyx
        simp [substFormAtCode, encodeFormula, substForm, ccons_ne_zero, uncpair_pred_ccons]
      · simp [substFormAtCode, encodeFormula, substForm, ccons_ne_zero, uncpair_pred_ccons, hyx, ih]

/-- Course-of-values step for arbitrary term substitution. -/
def substTermAtStep (a : Nat × Nat) (prev : List Nat) : Nat :=
  let n := prev.length
  let x := a.1
  let u := a.2
  if n = 0 then 0
  else
    let p := uncpair (n - 1)
    if p.1 = 0 then
      if p.2 = 0 then ccons 0 0 else 0
    else if p.1 = 1 then
      ccons 1 (prevGet prev p.2)
    else if p.1 = 2 then
      if p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        ccons 2 (ccons (prevGet prev q.1) (prevGet prev q.2))
    else if p.1 = 3 then
      if p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        ccons 3 (ccons (prevGet prev q.1) (prevGet prev q.2))
    else if p.1 = 4 then
      if p.2 = x then u else n
    else 0

/-- Strong step agrees with arbitrary term substitution. -/
theorem substTermAtStep_correct (a : Nat × Nat) (n : Nat) :
    substTermAtStep a ((List.range n).map (substTermAtCode a.1 a.2)) =
      substTermAtCode a.1 a.2 n := by
  cases n with
  | zero => simp [substTermAtStep, substTermAtCode]
  | succ n =>
      have hnz : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have hpLt := uncpair_lt (n + 1) hnz
      rw [substTermAtCode]
      simp only [substTermAtStep, List.length_map, List.length_range,
        Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
      generalize hp : uncpair n = p at hpLt ⊢
      rcases p with ⟨tag, payload⟩
      have hpay : payload < n + 1 := by simpa [hp] using hpLt.2
      rcases tag with _ | tag
      · simp [hp]
      · rcases tag with _ | tag
        · simp [hp, prevGet_range_map hpay]
        · rcases tag with _ | tag
          · by_cases hz : payload = 0
            · simp [hp, hz]
            · have hq := uncpair_lt payload hz
              generalize hqu : uncpair (payload - 1) = q at hq ⊢
              rcases q with ⟨qa, qb⟩
              have hqa : qa < n + 1 := Nat.lt_trans hq.1 hpay
              have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
              simp [hp, hz, hqu, prevGet_range_map hqa, prevGet_range_map hqb]
          · rcases tag with _ | tag
            · by_cases hz : payload = 0
              · simp [hp, hz]
              · have hq := uncpair_lt payload hz
                generalize hqu : uncpair (payload - 1) = q at hq ⊢
                rcases q with ⟨qa, qb⟩
                have hqa : qa < n + 1 := Nat.lt_trans hq.1 hpay
                have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
                simp [hp, hz, hqu, prevGet_range_map hqa, prevGet_range_map hqb]
            · rcases tag with _ | tag
              · by_cases heq : payload = a.1 <;> simp [hp, heq]
              · simp [hp]

/-- Primitive-recursive arbitrary term substitution step. -/
theorem substTermAtStep_primrec : Primrec₂ substTermAtStep := by
  let X := (Nat × Nat) × List Nat
  have ha : Primrec (fun p : X => p.1) := Primrec.fst
  have hx : Primrec (fun p : X => p.1.1) := Primrec.fst.comp ha
  have hu : Primrec (fun p : X => p.1.2) := Primrec.snd.comp ha
  have hprev : Primrec (fun p : X => p.2) := Primrec.snd
  have hn : Primrec (fun p : X => p.2.length) := Primrec.list_length.comp hprev
  have hn1 : Primrec (fun p : X => p.2.length - 1) := Primrec.nat_sub.comp hn (Primrec.const 1)
  have hp : Primrec (fun p : X => uncpair (p.2.length - 1)) := uncpair_primrec.comp hn1
  have htag : Primrec (fun p : X => (uncpair (p.2.length - 1)).1) := Primrec.fst.comp hp
  have hpay : Primrec (fun p : X => (uncpair (p.2.length - 1)).2) := Primrec.snd.comp hp
  have hpayPred := Primrec.nat_sub.comp hpay (Primrec.const 1)
  have hq := uncpair_primrec.comp hpayPred
  have hqa := Primrec.fst.comp hq
  have hqb := Primrec.snd.comp hq
  have hgetPay := prevGet_primrec.comp hprev hpay
  have hgetA := prevGet_primrec.comp hprev hqa
  have hgetB := prevGet_primrec.comp hprev hqb
  have hinner := ccons_primrec.comp hgetA hgetB
  have hc1 := ccons_primrec.comp (Primrec.const 1) hgetPay
  have hc2 := ccons_primrec.comp (Primrec.const 2) hinner
  have hc3 := ccons_primrec.comp (Primrec.const 3) hinner
  have heq0 : PrimrecPred (fun p : X => p.2.length = 0) :=
    (Primrec.nat_le.comp hn (Primrec.const 0)).of_eq (fun p => by simp)
  have hpay0 : PrimrecPred (fun p : X => (uncpair (p.2.length - 1)).2 = 0) :=
    (Primrec.nat_le.comp hpay (Primrec.const 0)).of_eq (fun p => by simp)
  have htagEq (k : Nat) : PrimrecPred (fun p : X => (uncpair (p.2.length - 1)).1 = k) :=
    (PrimrecPred.and (Primrec.nat_le.comp htag (Primrec.const k))
      (Primrec.nat_le.comp (Primrec.const k) htag)).of_eq (fun p => by omega)
  have hpayEqX : PrimrecPred (fun p : X => (uncpair (p.2.length - 1)).2 = p.1.1) :=
    Primrec.eq.comp hpay hx
  have hz : Primrec (fun _ : X => 0) := Primrec.const 0
  have hc00 : Primrec (fun _ : X => ccons 0 0) := Primrec.const (ccons 0 0)
  have hcase0 := Primrec.ite hpay0 hc00 hz
  have hcase2 := Primrec.ite hpay0 hz hc2
  have hcase3 := Primrec.ite hpay0 hz hc3
  have hcase4 := Primrec.ite hpayEqX hu hn
  have htags := Primrec.ite (htagEq 0) hcase0
    (Primrec.ite (htagEq 1) hc1
      (Primrec.ite (htagEq 2) hcase2
        (Primrec.ite (htagEq 3) hcase3
          (Primrec.ite (htagEq 4) hcase4 hz))))
  have hall : Primrec (fun p : X => substTermAtStep p.1 p.2) := Primrec.ite heq0 hz htags
  exact hall.to₂.of_eq (fun _ _ => rfl)

/-- General term substitution on codes is primitive recursive. -/
theorem substTermAtCode_primrec : Primrec₂ (fun a : Nat × Nat => substTermAtCode a.1 a.2) := by
  exact Primrec.nat_strong_rec
    (fun a n => substTermAtCode a.1 a.2 n)
    (Primrec.option_some.comp₂ substTermAtStep_primrec)
    (by intro a n; simp [substTermAtStep_correct])

/-- Course-of-values formula-substitution step. -/
def substFormAtStep (a : Nat × Nat) (prev : List Nat) : Nat :=
  let n := prev.length
  let x := a.1
  let u := a.2
  if n = 0 then 0
  else
    let p := uncpair (n - 1)
    if p.1 = 0 then
      if p.2 = 0 then 0 else
        let q := uncpair (p.2 - 1)
        ccons 0 (ccons (substTermAtCode x u q.1) (substTermAtCode x u q.2))
    else if p.1 = 1 then ccons 1 (prevGet prev p.2)
    else if p.1 = 2 then
      if p.2 = 0 then 0 else
        let q := uncpair (p.2 - 1)
        ccons 2 (ccons (prevGet prev q.1) (prevGet prev q.2))
    else if p.1 = 3 then
      if p.2 = 0 then 0 else
        let q := uncpair (p.2 - 1)
        if q.1 = x then n else ccons 3 (ccons q.1 (prevGet prev q.2))
    else 0

/-- Formula strong step agrees with arbitrary substitution. -/
theorem substFormAtStep_correct (a : Nat × Nat) (n : Nat) :
    substFormAtStep a ((List.range n).map (substFormAtCode a.1 a.2)) =
      substFormAtCode a.1 a.2 n := by
  cases n with
  | zero =>
      simp [substFormAtStep]
      rw [substFormAtCode.eq_1]
      simp
  | succ n =>
      have hnz : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have hpLt := uncpair_lt (n + 1) hnz
      rw [substFormAtCode.eq_1]
      simp only [substFormAtStep, List.length_map, List.length_range,
        Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
      generalize hp : uncpair n = p at hpLt ⊢
      rcases p with ⟨tag, payload⟩
      have hpay : payload < n + 1 := by simpa [hp] using hpLt.2
      rcases tag with _ | tag
      · by_cases hz : payload = 0 <;> simp [hp, hz]
      · rcases tag with _ | tag
        · simp [hp, prevGet_range_map hpay]
        · rcases tag with _ | tag
          · by_cases hz : payload = 0
            · simp [hp, hz]
            · have hq := uncpair_lt payload hz
              generalize hqu : uncpair (payload - 1) = q at hq ⊢
              rcases q with ⟨qa, qb⟩
              have hqa : qa < n + 1 := Nat.lt_trans hq.1 hpay
              have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
              simp [hp, hz, hqu, prevGet_range_map hqa, prevGet_range_map hqb]
          · rcases tag with _ | tag
            · by_cases hz : payload = 0
              · simp [hp, hz]
              · have hq := uncpair_lt payload hz
                generalize hqu : uncpair (payload - 1) = q at hq ⊢
                rcases q with ⟨qa, qb⟩
                have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
                by_cases heq : qa = a.1
                · simp [hp, hz, hqu, heq]
                · simp [hp, hz, hqu, heq, prevGet_range_map hqb]
            · simp [hp]

/-- Primitive-recursive arbitrary formula-substitution step. -/
theorem substFormAtStep_primrec : Primrec₂ substFormAtStep := by
  let X := (Nat × Nat) × List Nat
  have ha : Primrec (fun p : X => p.1) := Primrec.fst
  have hx := Primrec.fst.comp ha
  have hu := Primrec.snd.comp ha
  have hprev : Primrec (fun p : X => p.2) := Primrec.snd
  have hn := Primrec.list_length.comp hprev
  have hn1 := Primrec.nat_sub.comp hn (Primrec.const 1)
  have hp := uncpair_primrec.comp hn1
  have htag := Primrec.fst.comp hp
  have hpay := Primrec.snd.comp hp
  have hpayPred := Primrec.nat_sub.comp hpay (Primrec.const 1)
  have hq := uncpair_primrec.comp hpayPred
  have hqa := Primrec.fst.comp hq
  have hqb := Primrec.snd.comp hq
  have hgetPay := prevGet_primrec.comp hprev hpay
  have hgetA := prevGet_primrec.comp hprev hqa
  have hgetB := prevGet_primrec.comp hprev hqb
  have hsubA : Primrec (fun p : X => substTermAtCode p.1.1 p.1.2
      (uncpair ((uncpair (p.2.length - 1)).2 - 1)).1) :=
    substTermAtCode_primrec.comp ha hqa
  have hsubB : Primrec (fun p : X => substTermAtCode p.1.1 p.1.2
      (uncpair ((uncpair (p.2.length - 1)).2 - 1)).2) :=
    substTermAtCode_primrec.comp ha hqb
  have htermPair := ccons_primrec.comp hsubA hsubB
  have hformPair := ccons_primrec.comp hgetA hgetB
  have htag0out := ccons_primrec.comp (Primrec.const 0) htermPair
  have htag1out := ccons_primrec.comp (Primrec.const 1) hgetPay
  have htag2out := ccons_primrec.comp (Primrec.const 2) hformPair
  have hbindInner := ccons_primrec.comp hqa hgetB
  have hbindOut := ccons_primrec.comp (Primrec.const 3) hbindInner
  have heq0 : PrimrecPred (fun p : X => p.2.length = 0) :=
    (Primrec.nat_le.comp hn (Primrec.const 0)).of_eq (fun p => by simp)
  have hpay0 : PrimrecPred (fun p : X => (uncpair (p.2.length - 1)).2 = 0) :=
    (Primrec.nat_le.comp hpay (Primrec.const 0)).of_eq (fun p => by simp)
  have htagEq (k : Nat) : PrimrecPred (fun p : X => (uncpair (p.2.length - 1)).1 = k) :=
    (PrimrecPred.and (Primrec.nat_le.comp htag (Primrec.const k))
      (Primrec.nat_le.comp (Primrec.const k) htag)).of_eq (fun p => by omega)
  have hbindEqX : PrimrecPred (fun p : X =>
      (uncpair ((uncpair (p.2.length - 1)).2 - 1)).1 = p.1.1) := Primrec.eq.comp hqa hx
  have hz : Primrec (fun _ : X => 0) := Primrec.const 0
  have hcase0 := Primrec.ite hpay0 hz htag0out
  have hcase2 := Primrec.ite hpay0 hz htag2out
  have hcase3 := Primrec.ite hpay0 hz (Primrec.ite hbindEqX hn hbindOut)
  have htags := Primrec.ite (htagEq 0) hcase0
    (Primrec.ite (htagEq 1) htag1out
      (Primrec.ite (htagEq 2) hcase2
        (Primrec.ite (htagEq 3) hcase3 hz)))
  have hall : Primrec (fun p : X => substFormAtStep p.1 p.2) := Primrec.ite heq0 hz htags
  exact hall.to₂.of_eq (fun _ _ => rfl)

/-- General formula substitution on codes is primitive recursive. -/
theorem substFormAtCode_primrec : Primrec₂ (fun a : Nat × Nat => substFormAtCode a.1 a.2) := by
  exact Primrec.nat_strong_rec
    (fun a n => substFormAtCode a.1 a.2 n)
    (Primrec.option_some.comp₂ substFormAtStep_primrec)
    (by intro a n; simp [substFormAtStep_correct])

/-! ## Numeric formula and axiom surfaces -/

/-- Formula-code outer tag. -/
def codeTag (n : Nat) : Nat := cHead n

/-- Formula-code outer payload. -/
def codePayload (n : Nat) : Nat := cTail n

/-- Left field of a binary payload. -/
def codeLeft (n : Nat) : Nat := cHead (cTail n)

/-- Right field of a binary payload. -/
def codeRight (n : Nat) : Nat := cTail (cTail n)

/-- Boolean equality on numeric codes. -/
def codeEqB (a b : Nat) : Bool := a == b

/-- Primitive-recursive code tag. -/
theorem codeTag_primrec : Primrec codeTag := cHead_primrec

/-- Primitive-recursive code payload. -/
theorem codePayload_primrec : Primrec codePayload := cTail_primrec

/-- Primitive-recursive left binary field. -/
theorem codeLeft_primrec : Primrec codeLeft := cHead_primrec.comp cTail_primrec

/-- Primitive-recursive right binary field. -/
theorem codeRight_primrec : Primrec codeRight := cTail_primrec.comp cTail_primrec

/-- Primitive-recursive Boolean equality on numeric codes. -/
theorem codeEqB_primrec : Primrec₂ codeEqB := by
  exact Primrec.beq

/-- Numeric-code equality agrees with term equality on canonical term codes. -/
theorem codeEqB_encodeTerm (s t : Term) :
    codeEqB (encodeTerm s) (encodeTerm t) = decide (s = t) := by
  by_cases h : s = t
  · subst t
    simp [codeEqB]
  · have hc : encodeTerm s ≠ encodeTerm t := fun he => h (encodeTerm_injective he)
    simp [codeEqB, h, hc]

/-- Numeric-code equality agrees with formula equality on canonical formula codes. -/
theorem codeEqB_encodeFormula (φ ψ : Formula) :
    codeEqB (encodeFormula φ) (encodeFormula ψ) = decide (φ = ψ) := by
  by_cases h : φ = ψ
  · subst ψ
    simp [codeEqB]
  · have hc : encodeFormula φ ≠ encodeFormula ψ := fun he => h (encodeFormula_injective he)
    simp [codeEqB, h, hc]

/-- Raw equality-reflexivity schema on a formula code. -/
def isEqReflCodeB (c : Nat) : Bool :=
  codeEqB (codeTag c) 0 && codeEqB (codeLeft c) (codeRight c)

/-- Raw identity schema on a formula code. -/
def isAxIdCodeB (c : Nat) : Bool :=
  codeEqB (codeTag c) 2 && codeEqB (codeLeft c) (codeRight c)

/-- Raw K schema on a formula code. -/
def isAxKCodeB (c : Nat) : Bool :=
  let a := codeLeft c
  let rhs := codeRight c
  codeEqB (codeTag c) 2 && codeEqB (codeTag rhs) 2 &&
    codeEqB a (codeRight rhs)

/-- Raw DNE schema on a formula code. -/
def isAxDNECodeB (c : Nat) : Bool :=
  let lhs := codeLeft c
  let n1 := codePayload lhs
  codeEqB (codeTag c) 2 && codeEqB (codeTag lhs) 1 &&
    codeEqB (codeTag n1) 1 && codeEqB (codePayload n1) (codeRight c)

/-- Shape component of the raw S-schema recognizer. -/
def isAxSShapeB (c : Nat) : Bool :=
  let lhs := codeLeft c
  let rhs := codeRight c
  let bc := codeRight lhs
  let ab := codeLeft rhs
  let ac := codeRight rhs
  codeEqB (codeTag c) 2 &&
  codeEqB (codeTag lhs) 2 && codeEqB (codeTag bc) 2 &&
  codeEqB (codeTag rhs) 2 && codeEqB (codeTag ab) 2 && codeEqB (codeTag ac) 2

/-- Equality component of the raw S-schema recognizer. -/
def isAxSEqsB (c : Nat) : Bool :=
  let lhs := codeLeft c
  let rhs := codeRight c
  let a := codeLeft lhs
  let bc := codeRight lhs
  let b := codeLeft bc
  let cc := codeRight bc
  let ab := codeLeft rhs
  let ac := codeRight rhs
  codeEqB a (codeLeft ab) &&
    (codeEqB a (codeLeft ac) &&
      (codeEqB b (codeRight ab) && codeEqB cc (codeRight ac)))

/-- Raw S schema on a formula code. -/
def isAxSCodeB (c : Nat) : Bool :=
  isAxSShapeB c && isAxSEqsB c

/-- Finite Robinson-Q axiom-code recognizer. -/
def isQAxiomCodeB (c : Nat) : Bool :=
  codeEqB c (encodeFormula q1) || codeEqB c (encodeFormula q2) ||
  codeEqB c (encodeFormula q3) || codeEqB c (encodeFormula q4) ||
  codeEqB c (encodeFormula q5) || codeEqB c (encodeFormula q6) ||
  codeEqB c (encodeFormula q7)

/-- Numeric recognizer for the complete axiom surface of the live checker. -/
def isAxiomCodeB (c : Nat) : Bool :=
  isQAxiomCodeB c || isAxKCodeB c || isAxSCodeB c || isAxDNECodeB c ||
    isEqReflCodeB c || isAxIdCodeB c

private theorem boolAnd_comp {α : Type} [Primcodable α]
    {f g : α → Bool} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => f x && g x) := by
  exact Primrec.and.comp hf hg

private theorem boolOr_comp {α : Type} [Primcodable α]
    {f g : α → Bool} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => f x || g x) := by
  exact Primrec.or.comp hf hg

private theorem codeEq_comp {α : Type} [Primcodable α]
    {f g : α → Nat} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => codeEqB (f x) (g x)) :=
  codeEqB_primrec.comp hf hg

/-- Primitive-recursive Q-axiom recognizer. -/
theorem isQAxiomCodeB_primrec : Primrec isQAxiomCodeB := by
  let hq (q : Formula) : Primrec (fun c : Nat => codeEqB c (encodeFormula q)) :=
    codeEqB_primrec.comp Primrec.id (Primrec.const _)
  exact boolOr_comp (boolOr_comp (boolOr_comp (boolOr_comp (boolOr_comp
    (boolOr_comp (hq q1) (hq q2)) (hq q3)) (hq q4)) (hq q5)) (hq q6)) (hq q7)

/-- Primitive-recursive equality-reflexivity recognizer. -/
theorem isEqReflCodeB_primrec : Primrec isEqReflCodeB := by
  exact boolAnd_comp
    (codeEq_comp codeTag_primrec (Primrec.const 0))
    (codeEq_comp codeLeft_primrec codeRight_primrec)

/-- Primitive-recursive identity recognizer. -/
theorem isAxIdCodeB_primrec : Primrec isAxIdCodeB := by
  exact boolAnd_comp
    (codeEq_comp codeTag_primrec (Primrec.const 2))
    (codeEq_comp codeLeft_primrec codeRight_primrec)

/-- Primitive-recursive K recognizer. -/
theorem isAxKCodeB_primrec : Primrec isAxKCodeB := by
  have hr : Primrec (fun c : Nat => codeRight c) := codeRight_primrec
  have hrt : Primrec (fun c : Nat => codeTag (codeRight c)) := codeTag_primrec.comp hr
  have hrr : Primrec (fun c : Nat => codeRight (codeRight c)) := codeRight_primrec.comp hr
  exact boolAnd_comp
    (boolAnd_comp (codeEq_comp codeTag_primrec (Primrec.const 2))
      (codeEq_comp hrt (Primrec.const 2)))
    (codeEq_comp codeLeft_primrec hrr)

/-- Primitive-recursive DNE recognizer. -/
theorem isAxDNECodeB_primrec : Primrec isAxDNECodeB := by
  have hl := codeLeft_primrec
  have hlt := codeTag_primrec.comp hl
  have hn1 := codePayload_primrec.comp hl
  have hn1t := codeTag_primrec.comp hn1
  have hn1p := codePayload_primrec.comp hn1
  exact boolAnd_comp
    (boolAnd_comp
      (boolAnd_comp (codeEq_comp codeTag_primrec (Primrec.const 2))
        (codeEq_comp hlt (Primrec.const 1)))
      (codeEq_comp hn1t (Primrec.const 1)))
    (codeEq_comp hn1p codeRight_primrec)

/-- Primitive-recursive S-shape recognizer. -/
theorem isAxSShapeB_primrec : Primrec isAxSShapeB := by
  have hl := codeLeft_primrec
  have hr := codeRight_primrec
  have hbc := codeRight_primrec.comp hl
  have hab := codeLeft_primrec.comp hr
  have hac := codeRight_primrec.comp hr
  unfold isAxSShapeB
  exact boolAnd_comp
    (boolAnd_comp
      (boolAnd_comp
        (boolAnd_comp
          (boolAnd_comp (codeEq_comp codeTag_primrec (Primrec.const 2))
            (codeEq_comp (codeTag_primrec.comp hl) (Primrec.const 2)))
          (codeEq_comp (codeTag_primrec.comp hbc) (Primrec.const 2)))
        (codeEq_comp (codeTag_primrec.comp hr) (Primrec.const 2)))
      (codeEq_comp (codeTag_primrec.comp hab) (Primrec.const 2)))
    (codeEq_comp (codeTag_primrec.comp hac) (Primrec.const 2))

/-- Primitive-recursive S-equality recognizer. -/
theorem isAxSEqsB_primrec : Primrec isAxSEqsB := by
  have hl := codeLeft_primrec
  have hr := codeRight_primrec
  have ha := codeLeft_primrec.comp hl
  have hbc := codeRight_primrec.comp hl
  have hb := codeLeft_primrec.comp hbc
  have hcc := codeRight_primrec.comp hbc
  have hab := codeLeft_primrec.comp hr
  have hac := codeRight_primrec.comp hr
  unfold isAxSEqsB
  exact boolAnd_comp (codeEq_comp ha (codeLeft_primrec.comp hab))
    (boolAnd_comp (codeEq_comp ha (codeLeft_primrec.comp hac))
      (boolAnd_comp (codeEq_comp hb (codeRight_primrec.comp hab))
        (codeEq_comp hcc (codeRight_primrec.comp hac))))

/-- Primitive-recursive S recognizer. -/
theorem isAxSCodeB_primrec : Primrec isAxSCodeB := by
  unfold isAxSCodeB
  exact boolAnd_comp isAxSShapeB_primrec isAxSEqsB_primrec

/-- Primitive-recursive full axiom recognizer. -/
theorem isAxiomCodeB_primrec : Primrec isAxiomCodeB := by
  exact boolOr_comp (boolOr_comp (boolOr_comp (boolOr_comp (boolOr_comp
    isQAxiomCodeB_primrec isAxKCodeB_primrec) isAxSCodeB_primrec)
    isAxDNECodeB_primrec) isEqReflCodeB_primrec) isAxIdCodeB_primrec

/-- Numeric Q-axiom recognition agrees with the live checker on canonical codes. -/
theorem isQAxiomCodeB_encode (φ : Formula) :
    isQAxiomCodeB (encodeFormula φ) = isQAxiom φ := by
  simp only [isQAxiomCodeB, isQAxiom, codeEqB_encodeFormula]

/-- Numeric equality-reflexivity recognition agrees on canonical formula codes. -/
theorem isEqReflCodeB_encode (φ : Formula) :
    isEqReflCodeB (encodeFormula φ) = isEqRefl φ := by
  cases φ with
  | eq s t =>
      simpa [isEqReflCodeB, codeTag, codeLeft, codeRight, encodeFormula,
        isEqRefl, cHead_ccons, cTail_ccons] using codeEqB_encodeTerm s t
  | not ψ => simp [isEqReflCodeB, codeTag, encodeFormula, isEqRefl, cHead_ccons, codeEqB]
  | imp a b => simp [isEqReflCodeB, codeTag, encodeFormula, isEqRefl, cHead_ccons, codeEqB]
  | all x ψ => simp [isEqReflCodeB, codeTag, encodeFormula, isEqRefl, cHead_ccons, codeEqB]

/-- Numeric identity recognition agrees on canonical formula codes. -/
theorem isAxIdCodeB_encode (φ : Formula) :
    isAxIdCodeB (encodeFormula φ) = isAxId φ := by
  cases φ with
  | imp a b =>
      simpa [isAxIdCodeB, codeTag, codeLeft, codeRight, encodeFormula,
        isAxId, cHead_ccons, cTail_ccons] using codeEqB_encodeFormula a b
  | eq s t => simp [isAxIdCodeB, codeTag, encodeFormula, isAxId, cHead_ccons, codeEqB]
  | not ψ => simp [isAxIdCodeB, codeTag, encodeFormula, isAxId, cHead_ccons, codeEqB]
  | all x ψ => simp [isAxIdCodeB, codeTag, encodeFormula, isAxId, cHead_ccons, codeEqB]

/-- Numeric K recognition agrees on canonical formula codes. -/
theorem isAxKCodeB_encode (φ : Formula) :
    isAxKCodeB (encodeFormula φ) = isAxK φ := by
  cases φ with
  | imp a rhs =>
      cases rhs with
      | imp b c =>
          simpa [isAxKCodeB, codeTag, codeLeft, codeRight, encodeFormula,
            isAxK, cHead_ccons, cTail_ccons] using codeEqB_encodeFormula a c
      | eq s t => simp [isAxKCodeB, codeTag, codeLeft, codeRight, encodeFormula,
          isAxK, cHead_ccons, cTail_ccons, codeEqB]
      | not ψ => simp [isAxKCodeB, codeTag, codeLeft, codeRight, encodeFormula,
          isAxK, cHead_ccons, cTail_ccons, codeEqB]
      | all x ψ => simp [isAxKCodeB, codeTag, codeLeft, codeRight, encodeFormula,
          isAxK, cHead_ccons, cTail_ccons, codeEqB]
  | eq s t => simp [isAxKCodeB, codeTag, encodeFormula, isAxK, cHead_ccons, codeEqB]
  | not ψ => simp [isAxKCodeB, codeTag, encodeFormula, isAxK, cHead_ccons, codeEqB]
  | all x ψ => simp [isAxKCodeB, codeTag, encodeFormula, isAxK, cHead_ccons, codeEqB]

/-- Numeric DNE recognition agrees on canonical formula codes. -/
theorem isAxDNECodeB_encode (φ : Formula) :
    isAxDNECodeB (encodeFormula φ) = isAxDNE φ := by
  cases φ with
  | imp lhs rhs =>
      cases lhs with
      | not inner =>
          cases inner with
          | not a =>
              simpa [isAxDNECodeB, codeTag, codePayload, codeLeft, codeRight,
                encodeFormula, isAxDNE, cHead_ccons, cTail_ccons] using
                codeEqB_encodeFormula a rhs
          | eq s t => simp [isAxDNECodeB, codeTag, codePayload, codeLeft, codeRight,
              encodeFormula, isAxDNE, cHead_ccons, cTail_ccons, codeEqB]
          | imp a b => simp [isAxDNECodeB, codeTag, codePayload, codeLeft, codeRight,
              encodeFormula, isAxDNE, cHead_ccons, cTail_ccons, codeEqB]
          | all x a => simp [isAxDNECodeB, codeTag, codePayload, codeLeft, codeRight,
              encodeFormula, isAxDNE, cHead_ccons, cTail_ccons, codeEqB]
      | eq s t => simp [isAxDNECodeB, codeTag, codePayload, codeLeft, codeRight,
          encodeFormula, isAxDNE, cHead_ccons, cTail_ccons, codeEqB]
      | imp a b => simp [isAxDNECodeB, codeTag, codePayload, codeLeft, codeRight,
          encodeFormula, isAxDNE, cHead_ccons, cTail_ccons, codeEqB]
      | all x a => simp [isAxDNECodeB, codeTag, codePayload, codeLeft, codeRight,
          encodeFormula, isAxDNE, cHead_ccons, cTail_ccons, codeEqB]
  | eq s t => simp [isAxDNECodeB, codeTag, encodeFormula, isAxDNE, cHead_ccons, codeEqB]
  | not ψ => simp [isAxDNECodeB, codeTag, encodeFormula, isAxDNE, cHead_ccons, codeEqB]
  | all x ψ => simp [isAxDNECodeB, codeTag, encodeFormula, isAxDNE, cHead_ccons, codeEqB]

/-- Numeric S recognition agrees on canonical formula codes. -/
theorem isAxSCodeB_encode (φ : Formula) :
    isAxSCodeB (encodeFormula φ) = isAxS φ := by
  cases φ with
  | imp lhs rhs =>
      cases lhs with
      | imp a bc =>
          cases bc with
          | imp b c =>
              cases rhs with
              | imp ab ac =>
                  cases ab with
                  | imp a' b' =>
                      cases ac with
                      | imp a'' c' =>
                          simp only [isAxSCodeB, isAxSShapeB, isAxSEqsB, codeTag,
                            codeLeft, codeRight, encodeFormula, isAxS, cHead_ccons,
                            cTail_ccons, Bool.true_and]
                          rw [codeEqB_encodeFormula a a', codeEqB_encodeFormula a a'',
                            codeEqB_encodeFormula b b', codeEqB_encodeFormula c c']
                          simp [codeEqB]
                      | eq s t => simp [isAxSCodeB, isAxSShapeB, isAxSEqsB, codeTag,
                          codeLeft, codeRight, encodeFormula, isAxS, cHead_ccons,
                          cTail_ccons, codeEqB]
                      | not ψ => simp [isAxSCodeB, isAxSShapeB, isAxSEqsB, codeTag,
                          codeLeft, codeRight, encodeFormula, isAxS, cHead_ccons,
                          cTail_ccons, codeEqB]
                      | all x ψ => simp [isAxSCodeB, isAxSShapeB, isAxSEqsB, codeTag,
                          codeLeft, codeRight, encodeFormula, isAxS, cHead_ccons,
                          cTail_ccons, codeEqB]
                  | eq s t => simp [isAxSCodeB, isAxSShapeB, isAxSEqsB, codeTag,
                      codeLeft, codeRight, encodeFormula, isAxS, cHead_ccons,
                      cTail_ccons, codeEqB]
                  | not ψ => simp [isAxSCodeB, isAxSShapeB, isAxSEqsB, codeTag,
                      codeLeft, codeRight, encodeFormula, isAxS, cHead_ccons,
                      cTail_ccons, codeEqB]
                  | all x ψ => simp [isAxSCodeB, isAxSShapeB, isAxSEqsB, codeTag,
                      codeLeft, codeRight, encodeFormula, isAxS, cHead_ccons,
                      cTail_ccons, codeEqB]
              | eq s t => simp [isAxSCodeB, isAxSShapeB, isAxSEqsB, codeTag,
                  codeLeft, codeRight, encodeFormula, isAxS, cHead_ccons, cTail_ccons, codeEqB]
              | not ψ => simp [isAxSCodeB, isAxSShapeB, isAxSEqsB, codeTag,
                  codeLeft, codeRight, encodeFormula, isAxS, cHead_ccons, cTail_ccons, codeEqB]
              | all x ψ => simp [isAxSCodeB, isAxSShapeB, isAxSEqsB, codeTag,
                  codeLeft, codeRight, encodeFormula, isAxS, cHead_ccons, cTail_ccons, codeEqB]
          | eq s t => simp [isAxSCodeB, isAxSShapeB, isAxSEqsB, codeTag,
              codeLeft, codeRight, encodeFormula, isAxS, cHead_ccons, cTail_ccons, codeEqB]
          | not ψ => simp [isAxSCodeB, isAxSShapeB, isAxSEqsB, codeTag,
              codeLeft, codeRight, encodeFormula, isAxS, cHead_ccons, cTail_ccons, codeEqB]
          | all x ψ => simp [isAxSCodeB, isAxSShapeB, isAxSEqsB, codeTag,
              codeLeft, codeRight, encodeFormula, isAxS, cHead_ccons, cTail_ccons, codeEqB]
      | eq s t => simp [isAxSCodeB, isAxSShapeB, codeTag, codeLeft, codeRight,
          encodeFormula, isAxS, cHead_ccons, cTail_ccons, codeEqB]
      | not ψ => simp [isAxSCodeB, isAxSShapeB, codeTag, codeLeft, codeRight,
          encodeFormula, isAxS, cHead_ccons, cTail_ccons, codeEqB]
      | all x ψ => simp [isAxSCodeB, isAxSShapeB, codeTag, codeLeft, codeRight,
          encodeFormula, isAxS, cHead_ccons, cTail_ccons, codeEqB]
  | eq s t => simp [isAxSCodeB, isAxSShapeB, codeTag, encodeFormula, isAxS, cHead_ccons, codeEqB]
  | not ψ => simp [isAxSCodeB, isAxSShapeB, codeTag, encodeFormula, isAxS, cHead_ccons, codeEqB]
  | all x ψ => simp [isAxSCodeB, isAxSShapeB, codeTag, encodeFormula, isAxS, cHead_ccons, codeEqB]

/-- Numeric axiom recognition agrees with the live checker on every encoded formula. -/
theorem isAxiomCodeB_encode (φ : Formula) :
    isAxiomCodeB (encodeFormula φ) = isAxiom φ := by
  simp only [isAxiomCodeB, isAxiom, isQAxiomCodeB_encode, isAxKCodeB_encode,
    isAxSCodeB_encode, isAxDNECodeB_encode, isEqReflCodeB_encode,
    isAxIdCodeB_encode]

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
