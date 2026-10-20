import OperatorKO7.Meta.DistinctionBoundary.GodelGeneralSemantics
import OperatorKO7.Meta.DistinctionBoundary.GodelInternalDerivability

/-!
# A nonstandard model for the compiled Robinson-Q checker

The carrier is `Option Nat`; finite numbers are `some n` and `none` is one
infinite element. Arithmetic agrees with the natural numbers on the standard
part. The infinite element is absorbing for addition. Multiplication by zero is
zero, including at infinity, while every positive factor times infinity is
infinity.

The seven live Robinson-Q axioms hold. The arithmetized proof relation is then
shown non-functional at the infinite element: an infinite beta-packed sequence
can certify the code of falsity. Therefore the model refutes the internal
consistency sentence, and general model-relative checker soundness yields an
unconditional second-incompleteness theorem for the live compiled checker.

Relation: the live `check` relation and the live arithmetized `proofRel`.
Closure: one checked proof tree and its `Provable` existential closure.
Trust: kernel checked, Mathlib baseline only.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- Successor on the one-infinite-element carrier. -/
def modelInfSucc : Option Nat → Option Nat
  | none => none
  | some n => some (n + 1)

/-- Addition on the one-infinite-element carrier. -/
def modelInfAdd : Option Nat → Option Nat → Option Nat
  | some a, some b => some (a + b)
  | none, _ => none
  | _, none => none

/-- Infinity absorbs on the right for model addition. -/
@[simp] theorem modelInfAdd_none_right (x : Option Nat) :
    modelInfAdd x none = none := by
  cases x <;> rfl

/-- Infinity absorbs on the left for model addition. -/
@[simp] theorem modelInfAdd_none_left (x : Option Nat) :
    modelInfAdd none x = none := by
  cases x <;> rfl
/-- Multiplication on the one-infinite-element carrier. Zero annihilates the
infinite element; every positive finite factor and the infinite element produce
infinity. -/
def modelInfMul : Option Nat → Option Nat → Option Nat
  | some a, some b => some (a * b)
  | some 0, none => some 0
  | some (_a + 1), none => none
  | none, some 0 => some 0
  | none, some (_b + 1) => none
  | none, none => none

/-- A successor value multiplied by infinity is infinity. -/
@[simp] theorem modelInfMul_succ_none (x : Option Nat) :
    modelInfMul (modelInfSucc x) none = none := by
  cases x <;> rfl

/-- Infinity multiplied by infinity is infinity. -/
@[simp] theorem modelInfMul_none_none :
    modelInfMul none none = none :=
  rfl
/-- The one-infinite-element arithmetic structure. -/
def ModelInf : ArithStructure where
  Carrier := Option Nat
  zero := some 0
  succ := modelInfSucc
  add := modelInfAdd
  mul := modelInfMul

/-- The standard-zero environment in the nonstandard model. -/
def env0Inf : Nat → ModelInf.Carrier := fun _ => some 0

/-- Object-language numerals denote their standard finite values in the
nonstandard model. -/
theorem evalTermIn_ModelInf_numeral (env : Nat → ModelInf.Carrier) (n : Nat) :
    evalTermIn ModelInf env (numeral n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change modelInfSucc (evalTermIn ModelInf env (numeral n)) = some (n + 1)
      rw [ih]
      rfl

/-- Evaluation equation for the live sequence constructor term in the
nonstandard model. -/
theorem evalTermIn_ModelInf_cconsTerm (env : Nat → ModelInf.Carrier)
    (h t : Term) :
    evalTermIn ModelInf env (cconsTerm h t) =
      modelInfSucc
        (modelInfAdd
          (modelInfMul
            (modelInfAdd (evalTermIn ModelInf env h) (evalTermIn ModelInf env t))
            (modelInfAdd (evalTermIn ModelInf env h) (evalTermIn ModelInf env t)))
          (evalTermIn ModelInf env t)) :=
  rfl
/-- Q1: successor is never zero. -/
theorem modelInf_q1 (env : Nat → ModelInf.Carrier) :
    evalFormIn ModelInf env q1 := by
  intro a
  cases a <;> simp [evalFormIn, evalTermIn, ModelInf, modelInfSucc]

/-- Q2: successor is injective. -/
theorem modelInf_q2 (env : Nat → ModelInf.Carrier) :
    evalFormIn ModelInf env q2 := by
  intro a b
  cases a <;> cases b <;>
    simp [evalFormIn, evalTermIn, ModelInf, modelInfSucc]

/-- Q3: right addition by zero is identity. -/
theorem modelInf_q3 (env : Nat → ModelInf.Carrier) :
    evalFormIn ModelInf env q3 := by
  intro a
  cases a <;> simp [evalFormIn, evalTermIn, ModelInf, modelInfAdd]

/-- Q4: addition commutes with successor in the second argument. -/
theorem modelInf_q4 (env : Nat → ModelInf.Carrier) :
    evalFormIn ModelInf env q4 := by
  intro a b
  cases a <;> cases b <;>
    simp [evalFormIn, evalTermIn, ModelInf, modelInfSucc, modelInfAdd,
      Nat.add_assoc]

/-- Q5: right multiplication by zero is zero. -/
theorem modelInf_q5 (env : Nat → ModelInf.Carrier) :
    evalFormIn ModelInf env q5 := by
  intro a
  cases a <;> simp [evalFormIn, evalTermIn, ModelInf, modelInfMul]

/-- Q6: multiplication commutes with successor in the second argument. -/
theorem modelInf_q6 (env : Nat → ModelInf.Carrier) :
    evalFormIn ModelInf env q6 := by
  intro a b
  cases a with
  | none =>
      cases b with
      | none => simp [evalFormIn, evalTermIn, ModelInf, modelInfSucc,
          modelInfMul, modelInfAdd]
      | some b =>
          cases b <;> simp [evalFormIn, evalTermIn, ModelInf,
            modelInfSucc, modelInfMul, modelInfAdd]
  | some a =>
      cases a with
      | zero =>
          cases b <;> simp [evalFormIn, evalTermIn, ModelInf,
            modelInfSucc, modelInfMul, modelInfAdd]
      | succ a =>
          cases b with
          | none => simp [evalFormIn, evalTermIn, ModelInf,
              modelInfSucc, modelInfMul, modelInfAdd]
          | some b =>
              simp [evalFormIn, evalTermIn, ModelInf, modelInfSucc,
                modelInfMul, modelInfAdd, Nat.mul_add ]

/-- Q7: every element is zero or a successor; infinity is its own predecessor. -/
theorem modelInf_q7 (env : Nat → ModelInf.Carrier) :
    evalFormIn ModelInf env q7 := by
  intro a
  rw [evalFormIn_orF]
  cases a with
  | none =>
      right
      rw [evalFormIn_existsF]
      refine ⟨none, ?_⟩
      simp [evalFormIn, evalTermIn, ModelInf, modelInfSucc]
  | some n =>
      cases n with
      | zero =>
          left
          simp [evalFormIn, evalTermIn, ModelInf]
      | succ n =>
          right
          rw [evalFormIn_existsF]
          refine ⟨some n, ?_⟩
          simp [evalFormIn, evalTermIn, ModelInf, modelInfSucc]

/-- The one-infinite-element structure models all seven formulas in the live
`qAxioms` list. -/
theorem modelInf_qAxioms : ModelsQ ModelInf := by
  intro phi hphi env
  simp [qAxioms] at hphi
  rcases hphi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact modelInf_q1 env
  · exact modelInf_q2 env
  · exact modelInf_q3 env
  · exact modelInf_q4 env
  · exact modelInf_q5 env
  · exact modelInf_q6 env
  · exact modelInf_q7 env

/-! ## Infinite arithmetic witnesses used by the proof-relation certificate -/

/-- Every carrier element is below infinity in the object-language `leF`
relation. The witness for the additive remainder is infinity itself. -/
theorem modelInf_leF_to_infinity (env : Nat → ModelInf.Carrier)
    (a : Term) {bIndex : Nat} (hb : env bIndex = none)
    (hb50 : bIndex ≠ 50) :
    evalFormIn ModelInf env (leF a (Term.var bIndex)) := by
  unfold leF
  rw [evalFormIn_existsF]
  refine ⟨none, ?_⟩
  simp [evalFormIn, evalTermIn, ModelInf, hb, hb50]

/-- Every carrier element is strictly below infinity in the encoded `ltF`
relation. The witness after successor is again infinity. -/
theorem modelInf_ltF_to_infinity (env : Nat → ModelInf.Carrier)
    (a : Term) {bIndex : Nat} (hb : env bIndex = none)
    (hb51 : bIndex ≠ 51) :
    evalFormIn ModelInf env (ltF a (Term.var bIndex)) := by
  unfold ltF
  rw [evalFormIn_existsF]
  refine ⟨none, ?_⟩
  simp [evalFormIn, evalTermIn, ModelInf, modelInfSucc, hb, hb51]

/-- If the sequence code and beta modulus parameter both denote infinity, the
object-language beta formula accepts every index and every proposed value. -/
theorem modelInf_betaF_infinite (env : Nat → ModelInf.Carrier)
    (c d i a : Term)
    (hc : evalTermIn ModelInf env c = none)
    (hd : evalTermIn ModelInf env d = none)
    (hd51 : termHasVar 51 d = false)
    (hc52 : termHasVar 52 c = false) (hd52 : termHasVar 52 d = false) :
    evalFormIn ModelInf env (betaF c d i a) := by
  unfold betaF remF
  rw [evalFormIn_andF]
  constructor
  · unfold ltF
    rw [evalFormIn_existsF]
    refine ⟨none, ?_⟩
    have hd' :
        evalTermIn ModelInf (fun y => if y = 51 then none else env y) d = none := by
      rw [evalTermIn_fresh ModelInf 51 d hd51 env none, hd]
    change
      modelInfAdd
          (modelInfSucc
            (evalTermIn ModelInf (fun y => if y = 51 then none else env y) a))
          none =
        modelInfSucc
          (modelInfMul
            (modelInfSucc
              (evalTermIn ModelInf (fun y => if y = 51 then none else env y) i))
            (evalTermIn ModelInf (fun y => if y = 51 then none else env y) d))
    rw [hd']
    rw [modelInfMul_succ_none]
    rw [modelInfAdd_none_right]
    rfl
  · rw [evalFormIn_existsF]
    refine ⟨none, ?_⟩
    have hc' :
        evalTermIn ModelInf (fun y => if y = 52 then none else env y) c = none := by
      rw [evalTermIn_fresh ModelInf 52 c hc52 env none, hc]
    have hd' :
        evalTermIn ModelInf (fun y => if y = 52 then none else env y) d = none := by
      rw [evalTermIn_fresh ModelInf 52 d hd52 env none, hd]
    change
      evalTermIn ModelInf (fun y => if y = 52 then none else env y) c =
        modelInfAdd
          (modelInfMul none
            (modelInfSucc
              (modelInfMul
                (modelInfSucc
                  (evalTermIn ModelInf (fun y => if y = 52 then none else env y) i))
                (evalTermIn ModelInf (fun y => if y = 52 then none else env y) d))))
          (evalTermIn ModelInf (fun y => if y = 52 then none else env y) a)
    rw [hc', hd']
    rw [modelInfMul_succ_none]
    rw [show modelInfSucc none = none by rfl]
    rw [modelInfMul_none_none, modelInfAdd_none_left]

/-! ## Infinite axiom and justification witnesses -/

/-- At infinity, the internal equality-reflexivity recognizer accepts the
infinite code. Its existentially decoded term is itself infinite. -/
theorem modelInf_isEqReflF_var55 (env : Nat → ModelInf.Carrier)
    (h55 : env 55 = none) :
    evalFormIn ModelInf env (isEqReflF (Term.var 55)) := by
  unfold isEqReflF
  rw [evalFormIn_existsF]
  refine ⟨none, ?_⟩
  change
    evalTermIn ModelInf (fun y => if y = 53 then none else env y) (Term.var 55) =
      evalTermIn ModelInf (fun y => if y = 53 then none else env y)
        (cconsTerm (numeral 0)
          (cconsTerm (Term.var 53) (Term.var 53)))
  have h55' :
      evalTermIn ModelInf (fun y => if y = 53 then none else env y) (Term.var 55) =
        none := by
    simp [evalTermIn, h55]
  rw [h55']
  simp [evalTermIn_ModelInf_cconsTerm, evalTermIn_ModelInf_numeral,
    evalTermIn, modelInfSucc, modelInfAdd, modelInfMul]

/-- The full live axiom-code formula accepts the infinite line code through its
internal equality-reflexivity branch. -/
theorem modelInf_isAxiomF_var55 (env : Nat → ModelInf.Carrier)
    (h55 : env 55 = none) :
    evalFormIn ModelInf env (isAxiomF (Term.var 55)) := by
  unfold isAxiomF
  rw [evalFormIn_orF]
  right
  rw [evalFormIn_orF]
  left
  exact modelInf_isEqReflF_var55 env h55

/-- With infinite sequence parameters in variables 40 and 41, every indexed
line is justified by an infinite line-code witness in variable 55. -/
theorem modelInf_justifiedF_vars40_41 (env : Nat → ModelInf.Carrier)
    (i : Term) (h40 : env 40 = none) (h41 : env 41 = none) :
    evalFormIn ModelInf env
      (justifiedF (Term.var 40) (Term.var 41) i) := by
  unfold justifiedF
  rw [evalFormIn_existsF]
  refine ⟨none, ?_⟩
  rw [evalFormIn_andF]
  constructor
  · apply modelInf_betaF_infinite
    · simp [evalTermIn, h40]
    · simp [evalTermIn, h41]
    · simp [termHasVar]
    · simp [termHasVar]
    · simp [termHasVar]
  · rw [evalFormIn_orF]
    left
    apply modelInf_isAxiomF_var55
    simp

/-! ## The infinite packed proof certificate -/

/-- The proof-relation sequence header is accepted when variables 0, 40, 41,
and 42 all denote infinity. -/
theorem modelInf_proofHeader (env : Nat → ModelInf.Carrier)
    (h0 : env 0 = none) (h40 : env 40 = none)
    (h41 : env 41 = none) (h42 : env 42 = none) :
    evalFormIn ModelInf env
      (eqCcons (Term.var 0) (Term.var 40)
        (cconsTerm (Term.var 41) (Term.var 42))) := by
  unfold eqCcons
  change
    evalTermIn ModelInf env (Term.var 0) =
      evalTermIn ModelInf env
        (cconsTerm (Term.var 40)
          (cconsTerm (Term.var 41) (Term.var 42)))
  rw [show evalTermIn ModelInf env (Term.var 0) = none by simp [evalTermIn, h0]]
  simp [evalTermIn_ModelInf_cconsTerm, evalTermIn, h40, h41, h42,
    modelInfSucc, modelInfAdd, modelInfMul]

/-- With variable 0 set to infinity, the live proof relation accepts every
proposed conclusion code. The certificate uses infinite values for sequence
code, beta modulus, and last index; every line is justified through the
infinite equality-reflexivity code. -/
theorem modelInf_proofRel_var0 (env : Nat → ModelInf.Carrier)
    (t : Term) (h0 : env 0 = none) :
    evalFormIn ModelInf env (proofRel (Term.var 0) t) := by
  unfold proofRel
  rw [evalFormIn_existsF]
  refine ⟨none, ?_⟩
  rw [evalFormIn_existsF]
  refine ⟨none, ?_⟩
  rw [evalFormIn_existsF]
  refine ⟨none, ?_⟩
  let e : Nat → ModelInf.Carrier :=
    fun y => if y = 42 then none else
      if y = 41 then none else
        if y = 40 then none else env y
  change evalFormIn ModelInf e
    (andF
      (eqCcons (Term.var 0) (Term.var 40)
        (cconsTerm (Term.var 41) (Term.var 42)))
      (andF
        (betaF (Term.var 40) (Term.var 41) (Term.var 42) t)
        (Formula.all 43
          (Formula.imp (leF (Term.var 43) (Term.var 42))
            (orF
              (justifiedF (Term.var 40) (Term.var 41) (Term.var 43))
              (specJustF (Term.var 40) (Term.var 41) (Term.var 43)))))))
  have he0 : e 0 = none := by simp [e, h0]
  have he40 : e 40 = none := by simp [e]
  have he41 : e 41 = none := by simp [e]
  have he42 : e 42 = none := by simp [e]
  rw [evalFormIn_andF]
  constructor
  · exact modelInf_proofHeader e he0 he40 he41 he42
  · rw [evalFormIn_andF]
    constructor
    · apply modelInf_betaF_infinite
      · simp [evalTermIn, he40]
      · simp [evalTermIn, he41]
      · simp [termHasVar]
      · simp [termHasVar]
      · simp [termHasVar]
    · dsimp [evalFormIn]
      intro a43 _hle
      rw [evalFormIn_orF]
      left
      apply modelInf_justifiedF_vars40_41
      · simp [he40]
      · simp [he41]

/-! ## Unconditional Gödel II for the live compiled checker -/

/-- The nonstandard model satisfies the live provability predicate for falsity.
The witness for proof-code variable 0 is infinity. -/
theorem modelInf_bew_falsum :
    evalFormIn ModelInf env0Inf (bewOf falsum) := by
  unfold bewOf
  rw [evalFormIn_existsF]
  refine ⟨none, ?_⟩
  apply modelInf_proofRel_var0
  simp

/-- The nonstandard model refutes the live internal consistency sentence. -/
theorem modelInf_not_conQ :
    ¬ evalFormIn ModelInf env0Inf ConQ := by
  intro h
  exact h modelInf_bew_falsum

/-- Unconditional second incompleteness for the live compiled Robinson-Q
checker: the checker does not prove its own consistency sentence. The proof is
model-theoretic. General checker soundness transports any proposed proof to
`ModelInf`, where `ConQ` is false. -/
theorem godel_second_incompleteness_Q_unconditional :
    ¬ Provable ConQ := by
  intro hprov
  exact modelInf_not_conQ
    (provable_sound_in ModelInf modelInf_qAxioms hprov env0Inf)

/-- The live consistency sentence is independent of the compiled checker. The
positive side is the model-theoretic Gödel-II theorem above; the negative side
is the previously compiled standard-model soundness theorem. -/
theorem conQ_independent :
    ¬ Provable ConQ ∧ ¬ Provable (Formula.not ConQ) :=
  ⟨godel_second_incompleteness_Q_unconditional,
    not_provable_not_conQ_unconditional⟩

/-- Route marker: Gödel II is closed for the compiled checker by a nonstandard
model. This does not claim an internal Hilbert-Bernays-Löb derivation of
`ConQ → arithGodelSentence`; that is a distinct stronger construction. -/
theorem godel_second_incompleteness_Q_model_theoretic_route :
    (ModelsQ ModelInf ∧ ¬ evalFormIn ModelInf env0Inf ConQ) ∧
      (¬ Provable ConQ ∧ ¬ Provable (Formula.not ConQ)) :=
  ⟨⟨modelInf_qAxioms, modelInf_not_conQ⟩, conQ_independent⟩

end OperatorKO7.Meta.DistinctionBoundary.GodelArith

