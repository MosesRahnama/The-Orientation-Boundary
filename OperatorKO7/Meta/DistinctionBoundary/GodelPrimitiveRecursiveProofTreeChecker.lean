import OperatorKO7.Meta.DistinctionBoundary.GodelPrimitiveRecursiveProofChecker

set_option autoImplicit false

/-!
# Primitive-recursive proof-tree checker on Gödel codes

This module removes the remaining decode-then-check detour from the arithmetic
adequacy surface.  Every operation below acts directly on natural-number codes.
The checker result is a formula code; `0` denotes rejection.  Canonical formula
codes are positive, so the sentinel is disjoint from every accepted conclusion.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-! ## Closed-term code recognizer -/

/-- Read a previous Boolean value in a strong-recursion prefix. -/
def prevBoolGet (xs : List Bool) (k : Nat) : Bool := (xs[k]?).getD false

/-- Boolean previous-value lookup is primitive recursive. -/
theorem prevBoolGet_primrec : Primrec₂ prevBoolGet := by
  exact (Primrec.option_getD.comp₂ Primrec.list_getElem? (Primrec₂.const false)).of_eq
    (fun _ _ => rfl)

/-- Prefix lookup recovers a previous Boolean value at each strict index. -/
theorem prevBoolGet_range_map {f : Nat → Bool} {n k : Nat} (hk : k < n) :
    prevBoolGet ((List.range n).map f) k = f k := by
  simp [prevBoolGet, hk]

/-- Direct closed-term recognizer on raw Gödel codes.  Malformed codes are rejected. -/
def isClosedTermCodeB (n : Nat) : Bool :=
  if h : n = 0 then false
  else
    let p := uncpair (n - 1)
    match p.1 with
    | 0 => codeEqB p.2 0
    | 1 => isClosedTermCodeB p.2
    | 2 =>
      if hp : p.2 = 0 then false
      else
        let q := uncpair (p.2 - 1)
        isClosedTermCodeB q.1 && isClosedTermCodeB q.2
    | 3 =>
      if hp : p.2 = 0 then false
      else
        let q := uncpair (p.2 - 1)
        isClosedTermCodeB q.1 && isClosedTermCodeB q.2
    | 4 => false
    | _ => false
termination_by n
decreasing_by
  · exact (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt p.2 hp).1 (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt p.2 hp).1 (uncpair_lt n h).2
  · exact Nat.lt_trans (uncpair_lt p.2 hp).2 (uncpair_lt n h).2

/-- The numeric recognizer agrees with the live syntactic predicate on canonical term codes. -/
theorem isClosedTermCodeB_encode (t : Term) :
    isClosedTermCodeB (encodeTerm t) = isClosedTerm t := by
  induction t with
  | zero => simp [isClosedTermCodeB, encodeTerm, isClosedTerm, ccons_ne_zero,
      uncpair_pred_ccons, codeEqB]
  | succ t ih => simp [isClosedTermCodeB, encodeTerm, isClosedTerm, ccons_ne_zero,
      uncpair_pred_ccons, ih]
  | add s t ihs iht => simp [isClosedTermCodeB, encodeTerm, isClosedTerm, ccons_ne_zero,
      uncpair_pred_ccons, ihs, iht]
  | mul s t ihs iht => simp [isClosedTermCodeB, encodeTerm, isClosedTerm, ccons_ne_zero,
      uncpair_pred_ccons, ihs, iht]
  | var x => simp [isClosedTermCodeB, encodeTerm, isClosedTerm, ccons_ne_zero,
      uncpair_pred_ccons]

/-- Course-of-values step for the raw closed-term recognizer. -/
def closedTermCodeStep (prev : List Bool) : Bool :=
  let n := prev.length
  if n = 0 then false
  else
    let p := uncpair (n - 1)
    if p.1 = 0 then codeEqB p.2 0
    else if p.1 = 1 then prevBoolGet prev p.2
    else if p.1 = 2 then
      if p.2 = 0 then false
      else
        let q := uncpair (p.2 - 1)
        prevBoolGet prev q.1 && prevBoolGet prev q.2
    else if p.1 = 3 then
      if p.2 = 0 then false
      else
        let q := uncpair (p.2 - 1)
        prevBoolGet prev q.1 && prevBoolGet prev q.2
    else false

/-- The strong-recursion step computes `isClosedTermCodeB`. -/
theorem closedTermCodeStep_correct (n : Nat) :
    closedTermCodeStep ((List.range n).map isClosedTermCodeB) = isClosedTermCodeB n := by
  cases n with
  | zero => simp [closedTermCodeStep, isClosedTermCodeB]
  | succ n =>
      have hnz : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have hpLt := uncpair_lt (n + 1) hnz
      rw [isClosedTermCodeB]
      simp only [closedTermCodeStep, List.length_map, List.length_range,
        Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
      generalize hp : uncpair n = p at hpLt ⊢
      rcases p with ⟨tag, payload⟩
      have hpay : payload < n + 1 := by simpa [hp] using hpLt.2
      rcases tag with _ | tag
      · simp [hp, codeEqB]
      · rcases tag with _ | tag
        · simp [hp, prevBoolGet_range_map hpay]
        · rcases tag with _ | tag
          · by_cases hz : payload = 0
            · simp [hp, hz]
            · have hq := uncpair_lt payload hz
              generalize hqu : uncpair (payload - 1) = q at hq ⊢
              rcases q with ⟨qa, qb⟩
              have hqa : qa < n + 1 := Nat.lt_trans hq.1 hpay
              have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
              simp [hp, hz, hqu, prevBoolGet_range_map hqa, prevBoolGet_range_map hqb]
          · rcases tag with _ | tag
            · by_cases hz : payload = 0
              · simp [hp, hz]
              · have hq := uncpair_lt payload hz
                generalize hqu : uncpair (payload - 1) = q at hq ⊢
                rcases q with ⟨qa, qb⟩
                have hqa : qa < n + 1 := Nat.lt_trans hq.1 hpay
                have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
                simp [hp, hz, hqu, prevBoolGet_range_map hqa, prevBoolGet_range_map hqb]
            · cases tag <;> simp [hp]

/-- The course-of-values closed-term step is primitive recursive. -/
theorem closedTermCodeStep_primrec : Primrec closedTermCodeStep := by
  let X := List Bool
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
  have hgetPay : Primrec (fun xs : X => prevBoolGet xs (uncpair (xs.length - 1)).2) :=
    prevBoolGet_primrec.comp hprev hpay
  have hgetA : Primrec (fun xs : X => prevBoolGet xs
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).1) := prevBoolGet_primrec.comp hprev hqa
  have hgetB : Primrec (fun xs : X => prevBoolGet xs
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).2) := prevBoolGet_primrec.comp hprev hqb
  have hboth : Primrec (fun xs : X => prevBoolGet xs
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).1 && prevBoolGet xs
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).2) := Primrec.and.comp hgetA hgetB
  have heq0 : PrimrecPred (fun xs : X => xs.length = 0) :=
    (Primrec.nat_le.comp hn (Primrec.const 0)).of_eq (fun xs => by simp)
  have hpay0 : PrimrecPred (fun xs : X => (uncpair (xs.length - 1)).2 = 0) :=
    (Primrec.nat_le.comp hpay (Primrec.const 0)).of_eq (fun xs => by simp)
  have htagEq (k : Nat) : PrimrecPred (fun xs : X => (uncpair (xs.length - 1)).1 = k) :=
    (PrimrecPred.and
      (Primrec.nat_le.comp htag (Primrec.const k))
      (Primrec.nat_le.comp (Primrec.const k) htag)).of_eq (fun xs => by omega)
  have hfalse : Primrec (fun _ : X => false) := Primrec.const false
  have htag0out : Primrec (fun xs : X => codeEqB (uncpair (xs.length - 1)).2 0) :=
    codeEqB_primrec.comp hpay (Primrec.const 0)
  have hcase2 := Primrec.ite hpay0 hfalse hboth
  have hcase3 := Primrec.ite hpay0 hfalse hboth
  have htags := Primrec.ite (htagEq 0) htag0out
    (Primrec.ite (htagEq 1) hgetPay
      (Primrec.ite (htagEq 2) hcase2
        (Primrec.ite (htagEq 3) hcase3 hfalse)))
  exact (Primrec.ite heq0 hfalse htags).of_eq (fun xs => by rfl)

/-- Raw closed-term recognition is primitive recursive. -/
theorem isClosedTermCodeB_primrec : Primrec isClosedTermCodeB := by
  have hg₁ : Primrec (fun p : Bool × List Bool => some (closedTermCodeStep p.2)) :=
    Primrec.option_some.comp (closedTermCodeStep_primrec.comp Primrec.snd)
  have hg : Primrec₂ (fun _ : Bool => fun xs : List Bool => some (closedTermCodeStep xs)) :=
    hg₁.to₂.of_eq (fun _ _ => rfl)
  have h₂ : Primrec₂ (fun _ : Bool => fun n => isClosedTermCodeB n) := by
    apply Primrec.nat_strong_rec (fun _ : Bool => fun n => isClosedTermCodeB n) hg
    intro _ n
    simp [closedTermCodeStep_correct]
  exact h₂.comp (Primrec.const false) Primrec.id

#check @isClosedTermCodeB_primrec
#print axioms isClosedTermCodeB_primrec

/-! ## Direct proof-tree checker on codes -/

/-- Encode the checker output, using `0` for rejection. -/
def checkResultCode (p : ProofTree) : Nat :=
  match check p with
  | none => 0
  | some φ => encodeFormula φ

/-- Numeric proof-tree checker.  It inspects only tags, numeric child codes,
primitive-recursive axiom tests, the closed-term test, and coded substitution. -/
def checkProofCode (n : Nat) : Nat :=
  if h : n = 0 then 0
  else
    let p := uncpair (n - 1)
    match p.1 with
    | 0 => if isAxiomCodeB p.2 then p.2 else 0
    | 1 =>
      if hp : p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        let fp := checkProofCode q.1
        let fq := checkProofCode q.2
        if fp = 0 then 0
        else if fq = 0 then 0
        else if codeEqB (codeTag fp) 2 && codeEqB (codeLeft fp) fq then
          codeRight fp
        else 0
    | 2 =>
      if hp : p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        let fp := checkProofCode q.2
        if fp = 0 then 0 else ccons 3 (ccons q.1 fp)
    | 3 =>
      if hp : p.2 = 0 then 0
      else
        let q := uncpair (p.2 - 1)
        if hq : q.2 = 0 then 0
        else
          let r := uncpair (q.2 - 1)
          let fp := checkProofCode r.2
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

/-! Canonical formula-code accessors used by the checker correctness proof. -/

@[simp] theorem codeTag_encode_eq (s t : Term) :
    codeTag (encodeFormula (Formula.eq s t)) = 0 := by
  simp [codeTag, encodeFormula, cHead_ccons]

@[simp] theorem codeTag_encode_not (φ : Formula) :
    codeTag (encodeFormula (Formula.not φ)) = 1 := by
  simp [codeTag, encodeFormula, cHead_ccons]

@[simp] theorem codeTag_encode_imp (φ ψ : Formula) :
    codeTag (encodeFormula (Formula.imp φ ψ)) = 2 := by
  simp [codeTag, encodeFormula, cHead_ccons]

@[simp] theorem codeTag_encode_all (x : Nat) (φ : Formula) :
    codeTag (encodeFormula (Formula.all x φ)) = 3 := by
  simp [codeTag, encodeFormula, cHead_ccons]

@[simp] theorem codeLeft_encode_imp (φ ψ : Formula) :
    codeLeft (encodeFormula (Formula.imp φ ψ)) = encodeFormula φ := by
  simp [codeLeft, encodeFormula, cHead_ccons, cTail_ccons]

@[simp] theorem codeRight_encode_imp (φ ψ : Formula) :
    codeRight (encodeFormula (Formula.imp φ ψ)) = encodeFormula ψ := by
  simp [codeRight, encodeFormula, cTail_ccons]

@[simp] theorem codeLeft_encode_all (x : Nat) (φ : Formula) :
    codeLeft (encodeFormula (Formula.all x φ)) = x := by
  simp [codeLeft, encodeFormula, cHead_ccons, cTail_ccons]

@[simp] theorem codeRight_encode_all (x : Nat) (φ : Formula) :
    codeRight (encodeFormula (Formula.all x φ)) = encodeFormula φ := by
  simp [codeRight, encodeFormula, cTail_ccons]

/-- Canonical proof-tree codes are checked with the same result as the live
syntactic checker. -/
theorem checkProofCode_encode (p : ProofTree) :
    checkProofCode (encodeProof p) = checkResultCode p := by
  induction p with
  | ax φ =>
      by_cases hax : isAxiom φ = true
      · simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
          uncpair_pred_ccons, isAxiomCodeB_encode, hax]
      · simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
          uncpair_pred_ccons, isAxiomCodeB_encode, hax]
  | mp p q ihp ihq =>
      cases hp : check p with
      | none =>
          have ihp0 : checkProofCode (encodeProof p) = 0 := by
            simpa [checkResultCode, hp] using ihp
          simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
            uncpair_pred_ccons, hp, ihp0]
      | some φ =>
          cases hq : check q with
          | none =>
              have ihq0 : checkProofCode (encodeProof q) = 0 := by
                simpa [checkResultCode, hq] using ihq
              have ihpφ : checkProofCode (encodeProof p) = encodeFormula φ := by
                simpa [checkResultCode, hp] using ihp
              simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
                uncpair_pred_ccons, hp, hq, ihpφ, ihq0, encodeFormula_ne_zero]
          | some ψ =>
              have ihpφ : checkProofCode (encodeProof p) = encodeFormula φ := by
                simpa [checkResultCode, hp] using ihp
              have ihqψ : checkProofCode (encodeProof q) = encodeFormula ψ := by
                simpa [checkResultCode, hq] using ihq
              cases φ with
              | imp a b =>
                  by_cases hab : a = ψ
                  · subst ψ
                    simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
                      uncpair_pred_ccons, hp, hq, ihpφ, ihqψ, encodeFormula_ne_zero,
                      codeEqB]
                  · have hcode : encodeFormula a ≠ encodeFormula ψ :=
                      fun he => hab (encodeFormula_injective he)
                    simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
                      uncpair_pred_ccons, hp, hq, ihpφ, ihqψ, encodeFormula_ne_zero,
                      codeEqB, hab, hcode]
              | eq s t =>
                  simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
                    uncpair_pred_ccons, hp, hq, ihpφ, ihqψ, encodeFormula_ne_zero,
                    codeEqB]
              | not a =>
                  simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
                    uncpair_pred_ccons, hp, hq, ihpφ, ihqψ, encodeFormula_ne_zero,
                    codeEqB]
              | all x a =>
                  simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
                    uncpair_pred_ccons, hp, hq, ihpφ, ihqψ, encodeFormula_ne_zero,
                    codeEqB]
  | gen x p ih =>
      cases hp : check p with
      | none =>
          have ih0 : checkProofCode (encodeProof p) = 0 := by
            simpa [checkResultCode, hp] using ih
          simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
            uncpair_pred_ccons, hp, ih0]
      | some φ =>
          have ihφ : checkProofCode (encodeProof p) = encodeFormula φ := by
            simpa [checkResultCode, hp] using ih
          simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
            uncpair_pred_ccons, hp, ihφ, encodeFormula_ne_zero, encodeFormula]
  | spec x t p ih =>
      cases hp : check p with
      | none =>
          have ih0 : checkProofCode (encodeProof p) = 0 := by
            simpa [checkResultCode, hp] using ih
          simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
            uncpair_pred_ccons, hp, ih0]
      | some φ =>
          have ihφ : checkProofCode (encodeProof p) = encodeFormula φ := by
            simpa [checkResultCode, hp] using ih
          cases φ with
          | all y a =>
              by_cases hxy : x = y
              · subst y
                cases hc : isClosedTerm t with
                | false =>
                    simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
                      uncpair_pred_ccons, hp, ihφ, encodeFormula_ne_zero, codeEqB,
                      isClosedTermCodeB_encode, hc]
                | true =>
                    simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
                      uncpair_pred_ccons, hp, ihφ, encodeFormula_ne_zero, codeEqB,
                      isClosedTermCodeB_encode, hc, substFormAtCode_encode]
              · simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
                  uncpair_pred_ccons, hp, ihφ, encodeFormula_ne_zero, codeEqB,
                  isClosedTermCodeB_encode, hxy]
          | eq s u =>
              simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
                uncpair_pred_ccons, hp, ihφ, encodeFormula_ne_zero, codeEqB]
          | not a =>
              simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
                uncpair_pred_ccons, hp, ihφ, encodeFormula_ne_zero, codeEqB]
          | imp a b =>
              simp [checkProofCode, checkResultCode, encodeProof, check, ccons_ne_zero,
                uncpair_pred_ccons, hp, ihφ, encodeFormula_ne_zero, codeEqB]

#check @checkProofCode_encode
#print axioms checkProofCode_encode

/-! ## Primitive-recursive closure of the proof checker -/

private theorem primrecEqZeroPred {α : Type} [Primcodable α]
    {f : α → Nat} (hf : Primrec f) : PrimrecPred (fun x => f x = 0) :=
  Primrec.eq.comp hf (Primrec.const 0)

private theorem primrecNatEqPred {α : Type} [Primcodable α]
    {f g : α → Nat} (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred (fun x => f x = g x) :=
  Primrec.eq.comp hf hg

private theorem primrecBoolTruePred {α : Type} [Primcodable α]
    {f : α → Bool} (hf : Primrec f) : PrimrecPred (fun x => f x = true) :=
  Primrec.eq.comp hf (Primrec.const true)

/-- Course-of-values step for the numeric proof checker. -/
def checkProofCodeStep (prev : List Nat) : Nat :=
  let n := prev.length
  if n = 0 then 0
  else
    let p := uncpair (n - 1)
    if p.1 = 0 then
      if isAxiomCodeB p.2 then p.2 else 0
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

/-- The strong-recursion step agrees with `checkProofCode`. -/
theorem checkProofCodeStep_correct (n : Nat) :
    checkProofCodeStep ((List.range n).map checkProofCode) = checkProofCode n := by
  cases n with
  | zero => simp [checkProofCodeStep, checkProofCode]
  | succ n =>
      have hnz : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have hpLt := uncpair_lt (n + 1) hnz
      rw [checkProofCode]
      simp only [checkProofCodeStep, List.length_map, List.length_range,
        Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
      generalize hp : uncpair n = p at hpLt ⊢
      rcases p with ⟨tag, payload⟩
      have hpay : payload < n + 1 := by simpa [hp] using hpLt.2
      rcases tag with _ | tag
      · simp [hp]
      · rcases tag with _ | tag
        · by_cases hz : payload = 0
          · simp [hp, hz]
          · have hq := uncpair_lt payload hz
            generalize hqu : uncpair (payload - 1) = q at hq ⊢
            rcases q with ⟨qa, qb⟩
            have hqa : qa < n + 1 := Nat.lt_trans hq.1 hpay
            have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
            simp [hp, hz, hqu, prevGet_range_map hqa, prevGet_range_map hqb, codeEqB]
        · rcases tag with _ | tag
          · by_cases hz : payload = 0
            · simp [hp, hz]
            · have hq := uncpair_lt payload hz
              generalize hqu : uncpair (payload - 1) = q at hq ⊢
              rcases q with ⟨qa, qb⟩
              have hqb : qb < n + 1 := Nat.lt_trans hq.2 hpay
              simp [hp, hz, hqu, prevGet_range_map hqb]
          · rcases tag with _ | tag
            · by_cases hz : payload = 0
              · simp [hp, hz]
              · have hq := uncpair_lt payload hz
                generalize hqu : uncpair (payload - 1) = q at hq ⊢
                rcases q with ⟨qa, qb⟩
                have hqbPay : qb < n + 1 := Nat.lt_trans hq.2 hpay
                by_cases hqb0 : qb = 0
                · simp [hp, hz, hqu, hqb0]
                · have hr := uncpair_lt qb hqb0
                  generalize hru : uncpair (qb - 1) = r at hr ⊢
                  rcases r with ⟨ra, rb⟩
                  have hrb : rb < n + 1 := Nat.lt_trans hr.2 hqbPay
                  simp [hp, hz, hqu, hqb0, hru, prevGet_range_map hrb, codeEqB]
            · cases tag <;> simp [hp]

/-- The numeric proof-checker step is primitive recursive. -/
theorem checkProofCodeStep_primrec : Primrec checkProofCodeStep := by
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
  have heq0 : PrimrecPred (fun xs : X => xs.length = 0) := primrecEqZeroPred hn
  have hpay0 : PrimrecPred (fun xs : X => (uncpair (xs.length - 1)).2 = 0) :=
    primrecEqZeroPred hpay
  have hqb0 : PrimrecPred (fun xs : X =>
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).2 = 0) := primrecEqZeroPred hqb
  have hfp0 : PrimrecPred (fun xs : X => prevGet xs
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).1 = 0) := primrecEqZeroPred hfp
  have hfq0 : PrimrecPred (fun xs : X => prevGet xs
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).2 = 0) := primrecEqZeroPred hfq
  have hfpr0 : PrimrecPred (fun xs : X => prevGet xs
      (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2 = 0) :=
    primrecEqZeroPred hfpr
  have htagEq (k : Nat) : PrimrecPred (fun xs : X => (uncpair (xs.length - 1)).1 = k) :=
    primrecNatEqPred htag (Primrec.const k)
  have hax : Primrec (fun xs : X => isAxiomCodeB (uncpair (xs.length - 1)).2) :=
    isAxiomCodeB_primrec.comp hpay
  have haxTrue : PrimrecPred (fun xs : X => isAxiomCodeB (uncpair (xs.length - 1)).2 = true) :=
    primrecBoolTruePred hax
  have hcase0 : Primrec (fun xs : X =>
      if isAxiomCodeB (uncpair (xs.length - 1)).2 then (uncpair (xs.length - 1)).2 else 0) :=
    (Primrec.ite haxTrue hpay hzero).of_eq (fun xs => by
      cases h : isAxiomCodeB (uncpair (xs.length - 1)).2 <;> simp [h])
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
    PrimrecPred.and (primrecNatEqPred hfpTag (Primrec.const 2))
      (primrecNatEqPred hfpLeft hfq)
  have hcase1 := Primrec.ite hfp0 hzero
    (Primrec.ite hfq0 hzero (Primrec.ite hmpGood hfpRight hzero))
  have hgenInner : Primrec (fun xs : X => ccons
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).1
      (prevGet xs (uncpair ((uncpair (xs.length - 1)).2 - 1)).2)) :=
    ccons_primrec.comp hqa hfq
  have hgenOut : Primrec (fun xs : X => ccons 3 (ccons
      (uncpair ((uncpair (xs.length - 1)).2 - 1)).1
      (prevGet xs (uncpair ((uncpair (xs.length - 1)).2 - 1)).2))) :=
    ccons_primrec.comp (Primrec.const 3) hgenInner
  have hcase2 := Primrec.ite hfq0 hzero hgenOut
  have hfprTag : Primrec (fun xs : X => codeTag (prevGet xs
      (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2)) := codeTag_primrec.comp hfpr
  have hfprLeft : Primrec (fun xs : X => codeLeft (prevGet xs
      (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2)) := codeLeft_primrec.comp hfpr
  have hfprRight : Primrec (fun xs : X => codeRight (prevGet xs
      (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2)) := codeRight_primrec.comp hfpr
  have hclosed : Primrec (fun xs : X => isClosedTermCodeB
      (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).1) :=
    isClosedTermCodeB_primrec.comp hra
  have hspecGood : PrimrecPred (fun xs : X =>
      (codeTag (prevGet xs (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2) = 3 ∧
       (uncpair ((uncpair (xs.length - 1)).2 - 1)).1 =
        codeLeft (prevGet xs (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).2)) ∧
      isClosedTermCodeB (uncpair ((uncpair ((uncpair (xs.length - 1)).2 - 1)).2 - 1)).1 = true) :=
    PrimrecPred.and
      (PrimrecPred.and (primrecNatEqPred hfprTag (Primrec.const 3))
        (primrecNatEqPred hqa hfprLeft))
      (primrecBoolTruePred hclosed)
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
  have hcase1full := Primrec.ite hpay0 hzero hcase1
  have hcase2full := Primrec.ite hpay0 hzero hcase2
  have hcase3full := Primrec.ite hpay0 hzero hcase3core
  have htags := Primrec.ite (htagEq 0) hcase0
    (Primrec.ite (htagEq 1) hcase1full
      (Primrec.ite (htagEq 2) hcase2full
        (Primrec.ite (htagEq 3) hcase3full hzero)))
  exact (Primrec.ite heq0 hzero htags).of_eq (fun xs => by rfl)

/-- The complete numeric proof-tree checker is primitive recursive. -/
theorem checkProofCode_primrec : Primrec checkProofCode := by
  have hg₁ : Primrec (fun p : Bool × List Nat => some (checkProofCodeStep p.2)) :=
    Primrec.option_some.comp (checkProofCodeStep_primrec.comp Primrec.snd)
  have hg : Primrec₂ (fun _ : Bool => fun xs : List Nat => some (checkProofCodeStep xs)) :=
    hg₁.to₂.of_eq (fun _ _ => rfl)
  have h₂ : Primrec₂ (fun _ : Bool => fun n => checkProofCode n) := by
    apply Primrec.nat_strong_rec (fun _ : Bool => fun n => checkProofCode n) hg
    intro _ n
    simp [checkProofCodeStep_correct]
  exact h₂.comp (Primrec.const false) Primrec.id

/-- Boolean proof relation on raw proof-tree and formula codes. -/
def isProofCodeB (n m : Nat) : Bool :=
  codeEqB (checkProofCode n) m && !(codeEqB m 0)

/-- The raw Boolean proof relation is primitive recursive. -/
theorem isProofCodeB_primrec : Primrec₂ isProofCodeB := by
  have hleft : Primrec₂ (fun n m : Nat => codeEqB (checkProofCode n) m) :=
    codeEqB_primrec.comp₂ (checkProofCode_primrec.comp Primrec.fst) Primrec.snd
  have hzero : Primrec₂ (fun _n m : Nat => codeEqB m 0) :=
    codeEqB_primrec.comp₂ Primrec.snd (Primrec₂.const 0)
  have hnot : Primrec₂ (fun n m : Nat => !(codeEqB m 0)) :=
    Primrec.not.comp₂ hzero
  exact (Primrec.and.comp₂ hleft hnot).of_eq (fun _ _ => rfl)

/-- On canonical proof/formula codes the numeric relation is exactly the live checker. -/
theorem isProofCodeB_encode_iff (p : ProofTree) (φ : Formula) :
    isProofCodeB (encodeProof p) (encodeFormula φ) = true ↔ check p = some φ := by
  rw [isProofCodeB]
  rw [checkProofCode_encode]
  cases hp : check p with
  | none =>
      have hne0 : 0 ≠ encodeFormula φ := fun h => encodeFormula_ne_zero φ h.symm
      simp [checkResultCode, hp, codeEqB, hne0, encodeFormula_ne_zero]
  | some ψ =>
      by_cases hψφ : ψ = φ
      · subst φ
        simp [checkResultCode, hp, codeEqB, encodeFormula_ne_zero]
      · have hc : encodeFormula ψ ≠ encodeFormula φ := fun h => hψφ (encodeFormula_injective h)
        simp [checkResultCode, hp, codeEqB, encodeFormula_ne_zero, hψφ, hc]

/-- Primitive-recursive arithmetic precondition package used by the representability layer. -/
structure AcceptableNumberingPrecondition : Prop where
  pairPR : Primrec₂ cpair
  consPR : Primrec₂ ccons
  unpairPR : Primrec uncpair
  closedTermPR : Primrec isClosedTermCodeB
  numeralSubstPR : Primrec₂ substFormCode
  arbitrarySubstPR : Primrec₂ (fun a : Nat × Nat => substFormAtCode a.1 a.2)
  proofCheckerPR : Primrec₂ isProofCodeB

/-- Every numeric operation consumed by the checker/representability interface is primitive recursive. -/
theorem acceptable_numbering_precondition : AcceptableNumberingPrecondition where
  pairPR := cpair_primrec
  consPR := ccons_primrec
  unpairPR := uncpair_primrec
  closedTermPR := isClosedTermCodeB_primrec
  numeralSubstPR := substFormCode_primrec
  arbitrarySubstPR := substFormAtCode_primrec
  proofCheckerPR := isProofCodeB_primrec

#check @checkProofCode_primrec
#check @isProofCodeB_primrec
#check @isProofCodeB_encode_iff
#check @AcceptableNumberingPrecondition
#check @acceptable_numbering_precondition
#print axioms checkProofCode_primrec
#print axioms isProofCodeB_primrec
#print axioms isProofCodeB_encode_iff
#print axioms acceptable_numbering_precondition

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
