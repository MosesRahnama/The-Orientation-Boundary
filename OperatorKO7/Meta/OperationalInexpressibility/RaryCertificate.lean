import OperatorKO7.Meta.OperationalInexpressibility.RecursorCertificateSyntax
import OperatorKO7.Meta.Recursor.RaryDuplicator

/-!
# Strict certificates for the r-ary duplicator family

The certificate syntax of `RecursorCertificateSyntax` (a root-rule tag, an
active path, a projection argument, and the ranks before and after the step)
also certifies the root steps of the r-ary duplicator `RaryDuplicator.RStep r`:
the base rule `F x y Z → x` and the step rule `F x y (S n) → G (y^r) (F x y n)`,
whose recursive call sits at position `r` of the `G` frame. The strict checker
over the same compact codec accepts a bitstring exactly when the source and the
right-hand side form an r-ary root step, for every `r`.

`RTerm` nests itself through `List`, and the `DecidableEq` deriving handler
does not accept it, so the checker uses the structural decision procedure
`rtermDecEq` below.
-/

namespace OperatorKO7.Meta.OperationalInexpressibility.RaryCertificate

open OperatorKO7.Meta.OperationalInexpressibility.RecursorCertificateSyntax
open OperatorKO7.Meta.Recursor.RaryDuplicator

mutual
/-- Structural decidable equality of r-ary terms. -/
def rtermDecEq : (a b : RTerm) → Decidable (a = b)
  | .Z, .Z => isTrue rfl
  | .S a, .S b =>
      match rtermDecEq a b with
      | isTrue h => isTrue (congrArg RTerm.S h)
      | isFalse h => isFalse fun e => h (RTerm.S.inj e)
  | .base i, .base j =>
      if h : i = j then isTrue (congrArg RTerm.base h)
      else isFalse fun e => h (RTerm.base.inj e)
  | .pay i, .pay j =>
      if h : i = j then isTrue (congrArg RTerm.pay h)
      else isFalse fun e => h (RTerm.pay.inj e)
  | .F a b c, .F a' b' c' =>
      match rtermDecEq a a', rtermDecEq b b', rtermDecEq c c' with
      | isTrue h1, isTrue h2, isTrue h3 => isTrue (by rw [h1, h2, h3])
      | isFalse h1, _, _ => isFalse fun e => h1 (RTerm.F.inj e).1
      | _, isFalse h2, _ => isFalse fun e => h2 (RTerm.F.inj e).2.1
      | _, _, isFalse h3 => isFalse fun e => h3 (RTerm.F.inj e).2.2
  | .G ys t, .G ys' t' =>
      match rtermListDecEq ys ys', rtermDecEq t t' with
      | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
      | isFalse h1, _ => isFalse fun e => h1 (RTerm.G.inj e).1
      | _, isFalse h2 => isFalse fun e => h2 (RTerm.G.inj e).2
  | .Z, .S _ | .Z, .base _ | .Z, .pay _ | .Z, .F _ _ _ | .Z, .G _ _ =>
      isFalse fun e => RTerm.noConfusion e
  | .S _, .Z | .S _, .base _ | .S _, .pay _ | .S _, .F _ _ _ | .S _, .G _ _ =>
      isFalse fun e => RTerm.noConfusion e
  | .base _, .Z | .base _, .S _ | .base _, .pay _ | .base _, .F _ _ _ | .base _, .G _ _ =>
      isFalse fun e => RTerm.noConfusion e
  | .pay _, .Z | .pay _, .S _ | .pay _, .base _ | .pay _, .F _ _ _ | .pay _, .G _ _ =>
      isFalse fun e => RTerm.noConfusion e
  | .F _ _ _, .Z | .F _ _ _, .S _ | .F _ _ _, .base _ | .F _ _ _, .pay _ | .F _ _ _, .G _ _ =>
      isFalse fun e => RTerm.noConfusion e
  | .G _ _, .Z | .G _ _, .S _ | .G _ _, .base _ | .G _ _, .pay _ | .G _ _, .F _ _ _ =>
      isFalse fun e => RTerm.noConfusion e

/-- Structural decidable equality of lists of r-ary terms. -/
def rtermListDecEq : (as bs : List RTerm) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse fun e => List.noConfusion e
  | _ :: _, [] => isFalse fun e => List.noConfusion e
  | a :: as, b :: bs =>
      match rtermDecEq a b, rtermListDecEq as bs with
      | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
      | isFalse h1, _ => isFalse fun e => h1 (List.cons.inj e).1
      | _, isFalse h2 => isFalse fun e => h2 (List.cons.inj e).2
end

instance : DecidableEq RTerm := rtermDecEq

/-- Root steps of the r-ary duplicator: its two rules applied at the top of the
term. -/
inductive RRootStep (r : Nat) : RTerm → RTerm → Prop where
  | base (x y : RTerm) : RRootStep r (.F x y .Z) x
  | step (x y n : RTerm) : RRootStep r (.F x y (.S n)) (.G (List.replicate r y) (.F x y n))

theorem RRootStep.rStep {r : Nat} {s t : RTerm} (h : RRootStep r s t) : RStep r s t := by
  cases h with
  | base => exact .baseRule _ _
  | step => exact .stepRule _ _ _

/-- Every step of the r-ary duplicator from an `F`-headed term is a root step. -/
theorem rRootStep_of_rStep_F {r : Nat} {x y n t : RTerm} (h : RStep r (.F x y n) t) :
    RRootStep r (.F x y n) t := by
  cases h with
  | baseRule _ _ => exact .base _ _
  | stepRule _ _ m => exact .step _ _ m

/-- Number of leading `S` constructors of a counter. -/
def sDepth : RTerm → Nat
  | .S n => sDepth n + 1
  | _ => 0

/-- Same-input checker for r-ary root steps over the shared certificate syntax. -/
def checkRary (r : Nat) (source rhs : RTerm) (c : ExtractionCertificate) : Bool :=
  match source with
  | .F x y n =>
      match c.rule, n with
      | .zero, .Z =>
          decide (rhs = x ∧ c.activePath = [] ∧ c.projectionArg = 0 ∧
            c.rankBefore = 0 ∧ c.rankAfter = 0)
      | .succ, .S m =>
          decide (rhs = .G (List.replicate r y) (.F x y m) ∧ c.activePath = [r] ∧
            c.projectionArg = 2 ∧ c.rankBefore = sDepth (.S m) ∧ c.rankAfter = sDepth m)
      | _, _ => false
  | _ => false

/-- Certificate for a base-rule step. -/
def raryZeroCertificate : ExtractionCertificate where
  rule := .zero
  activePath := []
  projectionArg := 0
  rankBefore := 0
  rankAfter := 0

/-- Certificate for a step-rule step with counter `S n`: the recursive call is
the last argument, position `r`, of the `G` frame. -/
def rarySuccessorCertificate (r : Nat) (n : RTerm) : ExtractionCertificate where
  rule := .succ
  activePath := [r]
  projectionArg := 2
  rankBefore := sDepth (.S n)
  rankAfter := sDepth n

theorem checkRary_sound {r : Nat} {source rhs : RTerm} {c : ExtractionCertificate}
    (h : checkRary r source rhs c = true) : RRootStep r source rhs := by
  unfold checkRary at h
  split at h
  · split at h
    · simp only [decide_eq_true_eq] at h
      obtain ⟨rfl, -⟩ := h
      exact .base _ _
    · simp only [decide_eq_true_eq] at h
      obtain ⟨rfl, -⟩ := h
      exact .step _ _ _
    · cases h
  · cases h

@[simp] theorem checkRary_zero (r : Nat) (x y : RTerm) :
    checkRary r (.F x y .Z) x raryZeroCertificate = true := by
  simp [checkRary, raryZeroCertificate]

@[simp] theorem checkRary_successor (r : Nat) (x y n : RTerm) :
    checkRary r (.F x y (.S n)) (.G (List.replicate r y) (.F x y n))
      (rarySuccessorCertificate r n) = true := by
  simp [checkRary, rarySuccessorCertificate]

/-- Strict binary checker for r-ary root steps: the compact prefix parser must
consume the whole input. -/
def checkSerializedBitsStrictRary (r : Nat) (source rhs : RTerm) (bits : List Bool) : Bool :=
  match deserializeBitsPrefix bits with
  | some (c, []) => checkRary r source rhs c
  | _ => false

theorem checkSerializedBitsStrictRary_serializeBits (r : Nat) (source rhs : RTerm)
    (c : ExtractionCertificate) :
    checkSerializedBitsStrictRary r source rhs (serializeBits c) = checkRary r source rhs c := by
  unfold checkSerializedBitsStrictRary
  rw [deserializeBitsPrefix_serializeBits]

/-- P4.4: for every arity `r`, a strict compact binary certificate exists
exactly for the r-ary root steps. -/
theorem exists_strict_binary_certificate_iff_rRootStep (r : Nat) (source rhs : RTerm) :
    (∃ bits, checkSerializedBitsStrictRary r source rhs bits = true) ↔
      RRootStep r source rhs := by
  constructor
  · rintro ⟨bits, h⟩
    unfold checkSerializedBitsStrictRary at h
    cases hp : deserializeBitsPrefix bits with
    | none => simp [hp] at h
    | some parsed =>
        rcases parsed with ⟨c, rest⟩
        cases rest with
        | cons b t => simp [hp] at h
        | nil =>
            simp only [hp] at h
            exact checkRary_sound h
  · intro h
    cases h with
    | base =>
        refine ⟨serializeBits raryZeroCertificate, ?_⟩
        rw [checkSerializedBitsStrictRary_serializeBits]
        exact checkRary_zero r _ _
    | step x y n =>
        refine ⟨serializeBits (rarySuccessorCertificate r n), ?_⟩
        rw [checkSerializedBitsStrictRary_serializeBits]
        exact checkRary_successor r x y n

/-- From an `F`-headed source, strict certificate existence is exactly one step
of the r-ary duplicator. -/
theorem exists_strict_binary_certificate_iff_rStep_F (r : Nat) (x y n t : RTerm) :
    (∃ bits, checkSerializedBitsStrictRary r (.F x y n) t bits = true) ↔
      RStep r (.F x y n) t := by
  rw [exists_strict_binary_certificate_iff_rRootStep]
  exact ⟨RRootStep.rStep, rRootStep_of_rStep_F⟩

/-- Control: a congruence step inside a `G` frame has no root certificate. -/
theorem no_strict_certificate_for_G_source (r : Nat) (ys : List RTerm) (t t' : RTerm) :
    ¬ ∃ bits, checkSerializedBitsStrictRary r (.G ys t) t' bits = true := by
  rw [exists_strict_binary_certificate_iff_rRootStep]
  intro h
  cases h

end OperatorKO7.Meta.OperationalInexpressibility.RaryCertificate
