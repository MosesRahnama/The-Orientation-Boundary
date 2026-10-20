import OperatorKO7.Meta.DistinctionBoundary.GodelPrimitiveRecursiveSyntax

set_option autoImplicit false

/-!
# Primitive-recursive substitution on arithmetic syntax codes

The live substitution functions recurse on strict subcodes.  We expose that
course-of-values recursion through `Primrec.nat_strong_rec`.  The previous
values are stored in the canonical list `(List.range n).map f`; `prevGet`
reads the value at any strict subcode.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- Read a previous strong-recursion value, defaulting to zero out of range. -/
def prevGet (xs : List Nat) (k : Nat) : Nat := (xs[k]?).getD 0

/-- Previous-value lookup is primitive recursive. -/
theorem prevGet_primrec : Primrec₂ prevGet := by
  exact (Primrec.option_getD.comp₂ Primrec.list_getElem? (Primrec₂.const 0)).of_eq
    (fun _ _ => rfl)

/-- Lookup in the canonical strong-recursion prefix recovers the function value
at every strict index. -/
theorem prevGet_range_map {f : Nat → Nat} {n k : Nat} (hk : k < n) :
    prevGet ((List.range n).map f) k = f k := by
  simp [prevGet, hk]

/-- Course-of-values step for term substitution. -/
def substTermStep (y : Nat) (prev : List Nat) : Nat :=
  let n := prev.length
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
      if p.2 = 0 then numCode y else n
    else 0

/-- The strong-recursion step agrees with the live term substitution function. -/
theorem substTermStep_correct (y n : Nat) :
    substTermStep y ((List.range n).map (substTermCode y)) = substTermCode y n := by
  cases n with
  | zero => simp [substTermStep, substTermCode]
  | succ n =>
      have hnz : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have hpLt := uncpair_lt (n + 1) hnz
      rw [substTermCode]
      simp only [substTermStep, List.length_map, List.length_range,
        Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
      generalize hp : uncpair n = p at hpLt ⊢
      rcases p with ⟨tag, payload⟩
      have hpay : payload < n + 1 := by
        simpa [Nat.add_sub_cancel, hp] using hpLt.2
      rcases tag with _ | _tag
      · simp [hp]
      · rcases _tag with _ | _tag
        · simp [hp, prevGet_range_map hpay]
        · rcases _tag with _ | _tag
          · by_cases hz : payload = 0
            · simp [hp, hz]
            · have hq := uncpair_lt payload hz
              generalize hqu : uncpair (payload - 1) = q at hq ⊢
              rcases q with ⟨qa, qb⟩
              have hqa : qa < n + 1 := Nat.lt_trans hq.1 hpay
              have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
              simp [hp, hz, hqu, prevGet_range_map hqa, prevGet_range_map hqb]
          · rcases _tag with _ | _tag
            · by_cases hz : payload = 0
              · simp [hp, hz]
              · have hq := uncpair_lt payload hz
                generalize hqu : uncpair (payload - 1) = q at hq ⊢
                rcases q with ⟨qa, qb⟩
                have hqa : qa < n + 1 := Nat.lt_trans hq.1 hpay
                have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
                simp [hp, hz, hqu, prevGet_range_map hqa, prevGet_range_map hqb]
            · rcases _tag with _ | _tag
              · simp [hp]
              · simp [hp]

/-- Primitive-recursive status of the term-substitution strong step. -/
theorem substTermStep_primrec : Primrec₂ substTermStep := by
  -- The step is assembled from list length, primitive-recursive tagged access,
  -- previous-value lookup, constructors, and finite case splits.
  let X := Nat × List Nat
  have hy : Primrec (fun p : X => p.1) := Primrec.fst
  have hprev : Primrec (fun p : X => p.2) := Primrec.snd
  have hn : Primrec (fun p : X => p.2.length) := Primrec.list_length.comp hprev
  have hn1 : Primrec (fun p : X => p.2.length - 1) :=
    Primrec.nat_sub.comp hn (Primrec.const 1)
  have hp : Primrec (fun p : X => uncpair (p.2.length - 1)) :=
    uncpair_primrec.comp hn1
  have htag : Primrec (fun p : X => (uncpair (p.2.length - 1)).1) :=
    Primrec.fst.comp hp
  have hpay : Primrec (fun p : X => (uncpair (p.2.length - 1)).2) :=
    Primrec.snd.comp hp
  have hget : Primrec (fun p : X => prevGet p.2 (uncpair (p.2.length - 1)).2) :=
    prevGet_primrec.comp hprev hpay
  have hnum : Primrec (fun p : X => numCode p.1) := numCode_primrec.comp hy
  have hc10 : Primrec (fun p : X => ccons 1 (prevGet p.2 (uncpair (p.2.length - 1)).2)) :=
    ccons_primrec.comp (Primrec.const 1) hget
  have hpayloadPred : Primrec (fun p : X => (uncpair (p.2.length - 1)).2 - 1) :=
    Primrec.nat_sub.comp hpay (Primrec.const 1)
  have hq : Primrec (fun p : X => uncpair ((uncpair (p.2.length - 1)).2 - 1)) :=
    uncpair_primrec.comp hpayloadPred
  have hqa : Primrec (fun p : X => (uncpair ((uncpair (p.2.length - 1)).2 - 1)).1) :=
    Primrec.fst.comp hq
  have hqb : Primrec (fun p : X => (uncpair ((uncpair (p.2.length - 1)).2 - 1)).2) :=
    Primrec.snd.comp hq
  have hga : Primrec (fun p : X => prevGet p.2
      (uncpair ((uncpair (p.2.length - 1)).2 - 1)).1) :=
    prevGet_primrec.comp hprev hqa
  have hgb : Primrec (fun p : X => prevGet p.2
      (uncpair ((uncpair (p.2.length - 1)).2 - 1)).2) :=
    prevGet_primrec.comp hprev hqb
  have hinner : Primrec (fun p : X => ccons
      (prevGet p.2 (uncpair ((uncpair (p.2.length - 1)).2 - 1)).1)
      (prevGet p.2 (uncpair ((uncpair (p.2.length - 1)).2 - 1)).2)) :=
    ccons_primrec.comp hga hgb
  have hc2 : Primrec (fun p : X => ccons 2 (ccons
      (prevGet p.2 (uncpair ((uncpair (p.2.length - 1)).2 - 1)).1)
      (prevGet p.2 (uncpair ((uncpair (p.2.length - 1)).2 - 1)).2))) :=
    ccons_primrec.comp (Primrec.const 2) hinner
  have hc3 : Primrec (fun p : X => ccons 3 (ccons
      (prevGet p.2 (uncpair ((uncpair (p.2.length - 1)).2 - 1)).1)
      (prevGet p.2 (uncpair ((uncpair (p.2.length - 1)).2 - 1)).2))) :=
    ccons_primrec.comp (Primrec.const 3) hinner
  have heq0 : PrimrecPred (fun p : X => p.2.length = 0) :=
    (Primrec.nat_le.comp hn (Primrec.const 0)).of_eq (fun p => by simp)
  have hpay0 : PrimrecPred (fun p : X => (uncpair (p.2.length - 1)).2 = 0) :=
    (Primrec.nat_le.comp hpay (Primrec.const 0)).of_eq (fun p => by simp)
  have htag0 : PrimrecPred (fun p : X => (uncpair (p.2.length - 1)).1 = 0) :=
    (Primrec.nat_le.comp htag (Primrec.const 0)).of_eq (fun p => by simp)
  have htag1 : PrimrecPred (fun p : X => (uncpair (p.2.length - 1)).1 = 1) := by
    exact PrimrecPred.and
      (Primrec.nat_le.comp htag (Primrec.const 1))
      (Primrec.nat_le.comp (Primrec.const 1) htag) |>
      fun h => h.of_eq (fun p => by omega)
  have htag2 : PrimrecPred (fun p : X => (uncpair (p.2.length - 1)).1 = 2) := by
    exact PrimrecPred.and
      (Primrec.nat_le.comp htag (Primrec.const 2))
      (Primrec.nat_le.comp (Primrec.const 2) htag) |>
      fun h => h.of_eq (fun p => by omega)
  have htag3 : PrimrecPred (fun p : X => (uncpair (p.2.length - 1)).1 = 3) := by
    exact PrimrecPred.and
      (Primrec.nat_le.comp htag (Primrec.const 3))
      (Primrec.nat_le.comp (Primrec.const 3) htag) |>
      fun h => h.of_eq (fun p => by omega)
  have htag4 : PrimrecPred (fun p : X => (uncpair (p.2.length - 1)).1 = 4) := by
    exact PrimrecPred.and
      (Primrec.nat_le.comp htag (Primrec.const 4))
      (Primrec.nat_le.comp (Primrec.const 4) htag) |>
      fun h => h.of_eq (fun p => by omega)
  have hz : Primrec (fun _ : X => 0) := Primrec.const 0
  have hc00 : Primrec (fun _ : X => ccons 0 0) := Primrec.const (ccons 0 0)
  have hcase0 := Primrec.ite hpay0 hc00 hz
  have hcase2 := Primrec.ite hpay0 hz hc2
  have hcase3 := Primrec.ite hpay0 hz hc3
  have hcase4 := Primrec.ite hpay0 hnum hn
  have htags := Primrec.ite htag0 hcase0
    (Primrec.ite htag1 hc10
      (Primrec.ite htag2 hcase2
        (Primrec.ite htag3 hcase3
          (Primrec.ite htag4 hcase4 hz))))
  have hall : Primrec (fun p : X => substTermStep p.1 p.2) :=
    Primrec.ite heq0 hz htags
  exact hall.to₂.of_eq (fun _ _ => rfl)

/-- Option-valued step required by Mathlib's strong-recursion combinator. -/
def substTermStrongStep (y : Nat) (prev : List Nat) : Option Nat :=
  some (substTermStep y prev)

/-- The option-valued strong step is primitive recursive. -/
theorem substTermStrongStep_primrec : Primrec₂ substTermStrongStep := by
  exact Primrec.option_some.comp₂ substTermStep_primrec

/-- Term substitution on the live Gödel codes is primitive recursive. -/
theorem substTermCode_primrec : Primrec₂ substTermCode := by
  apply Primrec.nat_strong_rec substTermCode substTermStrongStep_primrec
  intro y n
  simp [substTermStrongStep, substTermStep_correct]

/-! ## Formula substitution -/

/-- Course-of-values step for formula substitution. -/
def substFormStep (y : Nat) (prev : List Nat) : Nat :=
  let n := prev.length
  if n = 0 then 0
  else
    let p := uncpair (n - 1)
    if p.1 = 0 then
      if p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        ccons 0 (ccons (substTermCode y q.1) (substTermCode y q.2))
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
        if q.1 = 0 then n
        else ccons 3 (ccons q.1 (prevGet prev q.2))
    else 0

/-- The formula strong step agrees with the live substitution function. -/
theorem substFormStep_correct (y n : Nat) :
    substFormStep y ((List.range n).map (substFormCode y)) = substFormCode y n := by
  cases n with
  | zero => simp [substFormStep, substFormCode]
  | succ n =>
      have hnz : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have hpLt := uncpair_lt (n + 1) hnz
      rw [substFormCode]
      simp only [substFormStep, List.length_map, List.length_range,
        Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
      generalize hp : uncpair n = p at hpLt ⊢
      rcases p with ⟨tag, payload⟩
      have hpay : payload < n + 1 := by
        simpa [Nat.add_sub_cancel, hp] using hpLt.2
      rcases tag with _ | tag
      · by_cases hz : payload = 0
        · simp [hz]
        · simp [hz]
      · rcases tag with _ | tag
        · simp [prevGet_range_map hpay]
        · rcases tag with _ | tag
          · by_cases hz : payload = 0
            · simp [hz]
            · have hq := uncpair_lt payload hz
              generalize hqu : uncpair (payload - 1) = q at hq ⊢
              rcases q with ⟨qa, qb⟩
              have hqa : qa < n + 1 := Nat.lt_trans hq.1 hpay
              have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
              simp [hz, hqu, prevGet_range_map hqa, prevGet_range_map hqb]
          · rcases tag with _ | tag
            · by_cases hz : payload = 0
              · simp [hz]
              · have hq := uncpair_lt payload hz
                generalize hqu : uncpair (payload - 1) = q at hq ⊢
                rcases q with ⟨qa, qb⟩
                have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
                by_cases hqa0 : qa = 0
                · simp [hz, hqu, hqa0]
                · simp [hz, hqu, hqa0, prevGet_range_map hqb]
            · simp

/-- Primitive-recursive status of the formula-substitution strong step. -/
theorem substFormStep_primrec : Primrec₂ substFormStep := by
  let X := Nat × List Nat
  have hy : Primrec (fun p : X => p.1) := Primrec.fst
  have hprev : Primrec (fun p : X => p.2) := Primrec.snd
  have hn : Primrec (fun p : X => p.2.length) := Primrec.list_length.comp hprev
  have hn1 : Primrec (fun p : X => p.2.length - 1) :=
    Primrec.nat_sub.comp hn (Primrec.const 1)
  have hp : Primrec (fun p : X => uncpair (p.2.length - 1)) :=
    uncpair_primrec.comp hn1
  have htag : Primrec (fun p : X => (uncpair (p.2.length - 1)).1) := Primrec.fst.comp hp
  have hpay : Primrec (fun p : X => (uncpair (p.2.length - 1)).2) := Primrec.snd.comp hp
  have hpayPred : Primrec (fun p : X => (uncpair (p.2.length - 1)).2 - 1) :=
    Primrec.nat_sub.comp hpay (Primrec.const 1)
  have hq : Primrec (fun p : X => uncpair ((uncpair (p.2.length - 1)).2 - 1)) :=
    uncpair_primrec.comp hpayPred
  have hqa : Primrec (fun p : X => (uncpair ((uncpair (p.2.length - 1)).2 - 1)).1) := Primrec.fst.comp hq
  have hqb : Primrec (fun p : X => (uncpair ((uncpair (p.2.length - 1)).2 - 1)).2) := Primrec.snd.comp hq
  have hgetPay : Primrec (fun p : X => prevGet p.2 (uncpair (p.2.length - 1)).2) :=
    prevGet_primrec.comp hprev hpay
  have hgetA : Primrec (fun p : X => prevGet p.2 (uncpair ((uncpair (p.2.length - 1)).2 - 1)).1) :=
    prevGet_primrec.comp hprev hqa
  have hgetB : Primrec (fun p : X => prevGet p.2 (uncpair ((uncpair (p.2.length - 1)).2 - 1)).2) :=
    prevGet_primrec.comp hprev hqb
  have hsubA : Primrec (fun p : X => substTermCode p.1 (uncpair ((uncpair (p.2.length - 1)).2 - 1)).1) :=
    substTermCode_primrec.comp hy hqa
  have hsubB : Primrec (fun p : X => substTermCode p.1 (uncpair ((uncpair (p.2.length - 1)).2 - 1)).2) :=
    substTermCode_primrec.comp hy hqb
  have htermPair : Primrec (fun p : X => ccons
      (substTermCode p.1 (uncpair ((uncpair (p.2.length - 1)).2 - 1)).1)
      (substTermCode p.1 (uncpair ((uncpair (p.2.length - 1)).2 - 1)).2)) :=
    ccons_primrec.comp hsubA hsubB
  have hformPair : Primrec (fun p : X => ccons
      (prevGet p.2 (uncpair ((uncpair (p.2.length - 1)).2 - 1)).1)
      (prevGet p.2 (uncpair ((uncpair (p.2.length - 1)).2 - 1)).2)) :=
    ccons_primrec.comp hgetA hgetB
  have htag0out := ccons_primrec.comp (Primrec.const 0) htermPair
  have htag1out := ccons_primrec.comp (Primrec.const 1) hgetPay
  have htag2out := ccons_primrec.comp (Primrec.const 2) hformPair
  have hbindInner : Primrec (fun p : X => ccons
      (uncpair ((uncpair (p.2.length - 1)).2 - 1)).1
      (prevGet p.2 (uncpair ((uncpair (p.2.length - 1)).2 - 1)).2)) :=
    ccons_primrec.comp hqa hgetB
  have hbindOut := ccons_primrec.comp (Primrec.const 3) hbindInner
  have heq0 : PrimrecPred (fun p : X => p.2.length = 0) :=
    (Primrec.nat_le.comp hn (Primrec.const 0)).of_eq (fun p => by simp)
  have hpay0 : PrimrecPred (fun p : X => (uncpair (p.2.length - 1)).2 = 0) :=
    (Primrec.nat_le.comp hpay (Primrec.const 0)).of_eq (fun p => by simp)
  have hqa0 : PrimrecPred (fun p : X => (uncpair ((uncpair (p.2.length - 1)).2 - 1)).1 = 0) :=
    (Primrec.nat_le.comp hqa (Primrec.const 0)).of_eq (fun p => by simp)
  have htagEq (k : Nat) : PrimrecPred (fun p : X => (uncpair (p.2.length - 1)).1 = k) :=
    (PrimrecPred.and
      (Primrec.nat_le.comp htag (Primrec.const k))
      (Primrec.nat_le.comp (Primrec.const k) htag)).of_eq (fun p => by omega)
  have hz : Primrec (fun _ : X => 0) := Primrec.const 0
  have hcase0 := Primrec.ite hpay0 hz htag0out
  have hcase2 := Primrec.ite hpay0 hz htag2out
  have hcase3 := Primrec.ite hpay0 hz (Primrec.ite hqa0 hn hbindOut)
  have htags := Primrec.ite (htagEq 0) hcase0
    (Primrec.ite (htagEq 1) htag1out
      (Primrec.ite (htagEq 2) hcase2
        (Primrec.ite (htagEq 3) hcase3 hz)))
  have hall : Primrec (fun p : X => substFormStep p.1 p.2) := Primrec.ite heq0 hz htags
  exact hall.to₂.of_eq (fun _ _ => rfl)

/-- Option-valued formula step for strong recursion. -/
def substFormStrongStep (y : Nat) (prev : List Nat) : Option Nat := some (substFormStep y prev)

/-- The option-valued formula step is primitive recursive. -/
theorem substFormStrongStep_primrec : Primrec₂ substFormStrongStep := by
  exact Primrec.option_some.comp₂ substFormStep_primrec

/-- Formula substitution on the live Gödel codes is primitive recursive. -/
theorem substFormCode_primrec : Primrec₂ substFormCode := by
  apply Primrec.nat_strong_rec substFormCode substFormStrongStep_primrec
  intro y n
  simp [substFormStrongStep, substFormStep_correct]

#check @prevGet_primrec
#check @substTermStep_correct
#check @substTermStep_primrec
#check @substTermStrongStep
#check @substTermStrongStep_primrec
#check @substTermCode_primrec
#print axioms prevGet_primrec
#print axioms substTermStep_correct
#print axioms substTermStep_primrec
#print axioms substTermStrongStep_primrec
#print axioms substTermCode_primrec
#check @substFormStep_correct
#check @substFormStep_primrec
#check @substFormStrongStep_primrec
#check @substFormCode_primrec
#print axioms substFormStep_correct
#print axioms substFormStep_primrec
#print axioms substFormStrongStep_primrec
#print axioms substFormCode_primrec

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
