import OperatorKO7.Meta.OperationalInexpressibility.RecursorCertificateSyntax
import Mathlib.Logic.Relation

/-!
# Small-step bit machine for the compact certificate parser

`RecursorCertificateSyntax.deserializeBitsPrefixRuntimeWork` counts bit
inspections inside three recursive decoders. This file defines a machine that
reads its input one cell per step and keeps a counter of consumed cells. On
every input the machine halts within `3 * bits.length + 1` steps with the
parser's result, and the parser's `bitInspections` equals the machine's
consumed-cell count (`runBitMachine_deserialize_eq`).

The machine takes the word decoder as a parameter; the decoder runs once, on
the complete word list. `deserialize` gives the certificate parser.
-/

namespace OperatorKO7.Meta.OperationalInexpressibility.CertificateBitMachine

open OperatorKO7.Meta.OperationalInexpressibility.RecursorCertificateSyntax

universe u

variable {α : Type u}

/-- The compact field under the read head: the word-count field, or a
certificate word with `left` further words after it and the words `acc`
already read. -/
inductive FieldSlot where
  | count
  | word (left : Nat) (acc : List Nat)

/-- Control phase: reading a unary width prefix with `w` ones read so far;
reading `left` more payload cells of a field whose partial value is `value` and
whose next cell has place value `weight`; or halted with an output. -/
inductive BitPhase (α : Type u) where
  | width (slot : FieldSlot) (w : Nat)
  | payload (slot : FieldSlot) (left value weight : Nat)
  | halted (out : Option (α × List Bool))

/-- Machine state: control phase, unread input, and consumed-cell counter. -/
structure BitState (α : Type u) where
  phase : BitPhase α
  input : List Bool
  consumed : Nat

/-- Halted phases. -/
def BitPhase.isHalted : BitPhase α → Bool
  | .halted _ => true
  | _ => false

/-- State with `left` words still to read and the words `acc` read so far.
With no word left, the word decoder runs once on the complete list. -/
def startWords (dec : List Nat → Option α) (left : Nat) (acc : List Nat)
    (rest : List Bool) (k : Nat) : BitState α :=
  match left with
  | 0 => ⟨.halted ((dec acc).map fun c => (c, rest)), rest, k⟩
  | n + 1 => ⟨.width (.word n acc) 0, rest, k⟩

/-- Continuation after a compact field decoded to the word `m`. -/
def fieldDone (dec : List Nat → Option α) : FieldSlot → Nat → List Bool → Nat → BitState α
  | .count, m, rest, k => startWords dec m [] rest k
  | .word left acc, m, rest, k => startWords dec left (acc ++ [m]) rest k

/-- Field completion: a zero raw payload value is rejected, as in
`decodeNatCompact`; a raw value `v` with `v ≠ 0` decodes to the word `v - 1`. -/
def finishField (dec : List Nat → Option α) (slot : FieldSlot) (v : Nat)
    (rest : List Bool) (k : Nat) : BitState α :=
  if v = 0 then ⟨.halted none, rest, k⟩ else fieldDone dec slot (v - 1) rest k

/-- One machine step. A step in a width phase or in a payload phase with cells
left reads the head cell and increments `consumed`. The other steps read no
cell: rejection at the end of the input, field completion, and the halted fixed
point. -/
def bitStep (dec : List Nat → Option α) : BitState α → BitState α
  | ⟨.width _ _, [], k⟩ => ⟨.halted none, [], k⟩
  | ⟨.width slot w, true :: bs, k⟩ => ⟨.width slot (w + 1), bs, k + 1⟩
  | ⟨.width slot w, false :: bs, k⟩ => ⟨.payload slot w 0 1, bs, k + 1⟩
  | ⟨.payload slot 0 v _, bs, k⟩ => finishField dec slot v bs k
  | ⟨.payload _ (_ + 1) _ _, [], k⟩ => ⟨.halted none, [], k⟩
  | ⟨.payload slot (n + 1) v p, b :: bs, k⟩ =>
      ⟨.payload slot n (v + if b then p else 0) (2 * p), bs, k + 1⟩
  | ⟨.halted out, bs, k⟩ => ⟨.halted out, bs, k⟩

/-- Initial state on the input `bits`. -/
def bitInit (bits : List Bool) : BitState α := ⟨.width .count 0, bits, 0⟩

/-- `n` machine steps. -/
def runBits (dec : List Nat → Option α) : Nat → BitState α → BitState α
  | 0, s => s
  | n + 1, s => runBits dec n (bitStep dec s)

/-- The machine run for `3 * bits.length + 1` steps; `runBitMachine_eq_of_wordStream`
shows that it has halted by then on every input. -/
def runBitMachine (dec : List Nat → Option α) (bits : List Bool) : BitState α :=
  runBits dec (3 * bits.length + 1) (bitInit bits)

/-- Small-step reachability. -/
abbrev BitReaches (dec : List Nat → Option α) : BitState α → BitState α → Prop :=
  Relation.ReflTransGen fun s t => bitStep dec s = t

/-- Rank of a phase in the termination measure. -/
def phaseRank : BitPhase α → Nat
  | .width _ _ => 1
  | .payload _ 0 _ _ => 2
  | .payload _ (_ + 1) _ _ => 1
  | .halted _ => 0

/-- Termination measure: three per unread cell plus the phase rank. -/
def bitMeasure (s : BitState α) : Nat := 3 * s.input.length + phaseRank s.phase

/-- Bit-level part of `deserializeBitsPrefixRuntimeWork`: the count field, then
that many words, with the inspection counts of the recursive decoders added. -/
def wordStreamRuntime (bits : List Bool) : Option (List Nat × List Bool) × Nat :=
  let countResult := decodeNatCompactRuntimeCosted bits
  match countResult.1 with
  | none => (none, countResult.2)
  | some (wordCount, rest) =>
      let wordsResult := decodeWordsCompactRuntimeCosted wordCount rest
      (wordsResult.1, countResult.2 + wordsResult.2)

/-- Output of the machine for a parsed word stream. -/
def streamOutput (dec : List Nat → Option α) :
    Option (List Nat × List Bool) → Option (α × List Bool)
  | none => none
  | some (ws, tail) => (dec ws).map fun c => (c, tail)

section Machine

variable (dec : List Nat → Option α)

theorem phaseRank_le_two (ph : BitPhase α) : phaseRank ph ≤ 2 := by
  cases ph with
  | width slot w => show 1 ≤ 2; omega
  | payload slot left v p =>
      cases left with
      | zero => show 2 ≤ 2; omega
      | succ n => show 1 ≤ 2; omega
  | halted out => show 0 ≤ 2; omega

theorem startWords_facts (left : Nat) (acc : List Nat) (rest : List Bool) (k : Nat) :
    (startWords dec left acc rest k).input = rest ∧
      (startWords dec left acc rest k).consumed = k ∧
      phaseRank (startWords dec left acc rest k).phase ≤ 1 := by
  cases left with
  | zero => exact ⟨rfl, rfl, Nat.zero_le 1⟩
  | succ n => exact ⟨rfl, rfl, Nat.le_refl 1⟩

theorem fieldDone_facts (slot : FieldSlot) (m : Nat) (rest : List Bool) (k : Nat) :
    (fieldDone dec slot m rest k).input = rest ∧
      (fieldDone dec slot m rest k).consumed = k ∧
      phaseRank (fieldDone dec slot m rest k).phase ≤ 1 := by
  cases slot with
  | count => exact startWords_facts dec m [] rest k
  | word left acc => exact startWords_facts dec left (acc ++ [m]) rest k

theorem finishField_facts (slot : FieldSlot) (v : Nat) (rest : List Bool) (k : Nat) :
    (finishField dec slot v rest k).input = rest ∧
      (finishField dec slot v rest k).consumed = k ∧
      phaseRank (finishField dec slot v rest k).phase ≤ 1 := by
  by_cases hv : v = 0
  · subst hv
    exact ⟨rfl, rfl, Nat.zero_le 1⟩
  · have e : finishField dec slot v rest k = fieldDone dec slot (v - 1) rest k := if_neg hv
    rw [e]
    exact fieldDone_facts dec slot (v - 1) rest k

/-- Every step that is not at a halted state lowers the measure. -/
theorem bitMeasure_bitStep_lt (s : BitState α) (hs : s.phase.isHalted = false) :
    bitMeasure (bitStep dec s) < bitMeasure s := by
  rcases s with ⟨phase, input, k⟩
  cases phase with
  | width slot w =>
      cases input with
      | nil => show 3 * 0 + 0 < 3 * 0 + 1; omega
      | cons b bs =>
          cases b with
          | true => show 3 * bs.length + 1 < 3 * (bs.length + 1) + 1; omega
          | false =>
              have h := phaseRank_le_two (BitPhase.payload (α := α) slot w 0 1)
              show 3 * bs.length + phaseRank (BitPhase.payload (α := α) slot w 0 1) <
                3 * (bs.length + 1) + 1
              omega
  | payload slot left v p =>
      cases left with
      | zero =>
          obtain ⟨h1, -, h3⟩ := finishField_facts dec slot v input k
          show 3 * (finishField dec slot v input k).input.length +
              phaseRank (finishField dec slot v input k).phase < 3 * input.length + 2
          rw [h1]
          omega
      | succ n =>
          cases input with
          | nil => show 3 * 0 + 0 < 3 * 0 + 1; omega
          | cons b bs =>
              have h := phaseRank_le_two
                (BitPhase.payload (α := α) slot n (v + if b then p else 0) (2 * p))
              show 3 * bs.length +
                  phaseRank (BitPhase.payload (α := α) slot n (v + if b then p else 0) (2 * p)) <
                3 * (bs.length + 1) + 1
              omega
  | halted out => simp [BitPhase.isHalted] at hs

/-- A halted state is a fixed point of the step. -/
theorem bitStep_of_isHalted (s : BitState α) (hs : s.phase.isHalted = true) :
    bitStep dec s = s := by
  rcases s with ⟨phase, input, k⟩
  cases phase with
  | halted out => rfl
  | width slot w => simp [BitPhase.isHalted] at hs
  | payload slot left v p => simp [BitPhase.isHalted] at hs

/-- One step reads at most the head cell: the input loses exactly the cells the
counter gains. -/
theorem bitStep_input (s : BitState α) :
    ∃ pre : List Bool, s.input = pre ++ (bitStep dec s).input ∧
      (bitStep dec s).consumed = s.consumed + pre.length := by
  rcases s with ⟨phase, input, k⟩
  cases phase with
  | width slot w =>
      cases input with
      | nil => exact ⟨[], rfl, rfl⟩
      | cons b bs =>
          cases b with
          | true => exact ⟨[true], rfl, rfl⟩
          | false => exact ⟨[false], rfl, rfl⟩
  | payload slot left v p =>
      cases left with
      | zero =>
          obtain ⟨h1, h2, -⟩ := finishField_facts dec slot v input k
          refine ⟨[], ?_, ?_⟩
          · show input = [] ++ (finishField dec slot v input k).input
            simp [h1]
          · show (finishField dec slot v input k).consumed = k + 0
            simp [h2]
      | succ n =>
          cases input with
          | nil => exact ⟨[], rfl, rfl⟩
          | cons b bs => exact ⟨[b], rfl, rfl⟩
  | halted out => exact ⟨[], rfl, rfl⟩

/-- Along any run, the input read so far is a prefix of the input at the start
and its length is the growth of the consumed-cell counter. -/
theorem bitReaches_input_suffix {s t : BitState α} (h : BitReaches dec s t) :
    ∃ pre : List Bool, s.input = pre ++ t.input ∧ t.consumed = s.consumed + pre.length := by
  induction h with
  | refl => exact ⟨[], rfl, rfl⟩
  | @tail b c _ hstep ih =>
      obtain ⟨pre, hpre, hk⟩ := ih
      have hstep' : bitStep dec b = c := hstep
      subst hstep'
      obtain ⟨pre', hpre', hk'⟩ := bitStep_input dec b
      refine ⟨pre ++ pre', ?_, ?_⟩
      · rw [hpre, hpre', List.append_assoc]
      · rw [hk', hk, List.length_append, Nat.add_assoc]

theorem bitReaches_of_eq {s t : BitState α} (h : s = t) : BitReaches dec s t := by
  subst h
  exact Relation.ReflTransGen.refl

theorem runBits_halted (out : Option (α × List Bool)) (rest : List Bool) (k : Nat) :
    ∀ n, runBits dec n ⟨.halted out, rest, k⟩ = ⟨.halted out, rest, k⟩
  | 0 => rfl
  | n + 1 => runBits_halted out rest k n

/-- A run that reaches a halted state is computed by `runBits` with any fuel at
least the measure of its start. -/
theorem runBits_eq_of_bitReaches {s : BitState α} {out : Option (α × List Bool)}
    {rest : List Bool} {k : Nat} (h : BitReaches dec s ⟨.halted out, rest, k⟩) :
    ∀ n, bitMeasure s ≤ n → runBits dec n s = ⟨.halted out, rest, k⟩ := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun n _ => runBits_halted dec out rest k n
  | @head a c hac _ ih =>
      intro n hn
      have hac' : bitStep dec a = c := hac
      cases hhalt : a.phase.isHalted with
      | true =>
          rw [bitStep_of_isHalted dec a hhalt] at hac'
          subst hac'
          exact ih n hn
      | false =>
          have hlt := bitMeasure_bitStep_lt dec a hhalt
          rw [hac'] at hlt
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          show runBits dec m (bitStep dec a) = _
          rw [hac']
          exact ih m (by omega)

/-! ## Segments of a run -/

theorem bitReaches_width_some (slot : FieldSlot) {bits : List Bool} {w k n : Nat}
    {rest : List Bool} (h : (decodeCompactWidthRuntimeCosted bits).1 = some (n, rest)) :
    BitReaches dec ⟨.width slot w, bits, k⟩
      ⟨.payload slot (w + n) 0 1, rest, k + (decodeCompactWidthRuntimeCosted bits).2⟩ := by
  induction bits generalizing w k n rest with
  | nil => simp [decodeCompactWidthRuntimeCosted] at h
  | cons b bs ih =>
      cases b with
      | false =>
          simp only [decodeCompactWidthRuntimeCosted, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Relation.ReflTransGen.single rfl
      | true =>
          simp only [decodeCompactWidthRuntimeCosted] at h ⊢
          generalize hr : decodeCompactWidthRuntimeCosted bs = r at h ⊢
          rcases r with ⟨result, cost⟩
          cases result with
          | none => simp at h
          | some pair =>
              rcases pair with ⟨m, tail⟩
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hs : (decodeCompactWidthRuntimeCosted bs).1 = some (m, tail) := by rw [hr]
              have key := ih (w := w + 1) (k := k + 1) (n := m) (rest := tail) hs
              rw [hr] at key
              simp only at key
              have e1 : w + 1 + m = w + (m + 1) := by omega
              have e2 : k + 1 + cost = k + (cost + 1) := by omega
              rw [e1, e2] at key
              exact Relation.ReflTransGen.head
                (b := ⟨.width slot (w + 1), bs, k + 1⟩) rfl key

theorem bitReaches_width_none (slot : FieldSlot) {bits : List Bool} {w k : Nat}
    (h : (decodeCompactWidthRuntimeCosted bits).1 = none) :
    BitReaches dec ⟨.width slot w, bits, k⟩
      ⟨.halted none, [], k + (decodeCompactWidthRuntimeCosted bits).2⟩ := by
  induction bits generalizing w k with
  | nil => exact Relation.ReflTransGen.single rfl
  | cons b bs ih =>
      cases b with
      | false => simp [decodeCompactWidthRuntimeCosted] at h
      | true =>
          simp only [decodeCompactWidthRuntimeCosted] at h ⊢
          generalize hr : decodeCompactWidthRuntimeCosted bs = r at h ⊢
          rcases r with ⟨result, cost⟩
          cases result with
          | some pair =>
              rcases pair with ⟨m, tail⟩
              simp at h
          | none =>
              have hs : (decodeCompactWidthRuntimeCosted bs).1 = none := by rw [hr]
              have key := ih (w := w + 1) (k := k + 1) hs
              rw [hr] at key
              simp only at key
              have e : k + 1 + cost = k + (cost + 1) := by omega
              rw [e] at key
              exact Relation.ReflTransGen.head
                (b := ⟨.width slot (w + 1), bs, k + 1⟩) rfl key

private theorem payload_value_step (b : Bool) (v p val : Nat) :
    v + (if b then p else 0) + 2 * p * val = v + p * Nat.bit b val := by
  cases b <;> simp [Nat.bit_val] <;> ring

theorem bitReaches_payload_some (slot : FieldSlot) {width : Nat} {bits : List Bool}
    {v p k val : Nat} {rest : List Bool}
    (h : (decodePayloadRuntimeCosted width bits).1 = some (val, rest)) :
    BitReaches dec ⟨.payload slot width v p, bits, k⟩
      ⟨.payload slot 0 (v + p * val) (p * 2 ^ width), rest,
        k + (decodePayloadRuntimeCosted width bits).2⟩ := by
  induction width generalizing bits v p k val rest with
  | zero =>
      simp only [decodePayloadRuntimeCosted, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact bitReaches_of_eq dec (by simp [decodePayloadRuntimeCosted])
  | succ width ih =>
      cases bits with
      | nil => simp [decodePayloadRuntimeCosted] at h
      | cons b bs =>
          simp only [decodePayloadRuntimeCosted] at h ⊢
          generalize hr : decodePayloadRuntimeCosted width bs = r at h ⊢
          rcases r with ⟨result, cost⟩
          cases result with
          | none => simp at h
          | some pair =>
              rcases pair with ⟨val', tail⟩
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hs : (decodePayloadRuntimeCosted width bs).1 = some (val', tail) := by
                rw [hr]
              have key := ih (bits := bs) (v := v + if b then p else 0) (p := 2 * p)
                (k := k + 1) (val := val') (rest := tail) hs
              rw [hr] at key
              simp only at key
              have e2 : 2 * p * 2 ^ width = p * 2 ^ (width + 1) := by ring
              have e3 : k + 1 + cost = k + (cost + 1) := by omega
              rw [payload_value_step, e2, e3] at key
              exact Relation.ReflTransGen.head
                (b := ⟨.payload slot width (v + if b then p else 0) (2 * p), bs, k + 1⟩) rfl key

theorem bitReaches_payload_none (slot : FieldSlot) {width : Nat} {bits : List Bool}
    {v p k : Nat} (h : (decodePayloadRuntimeCosted width bits).1 = none) :
    BitReaches dec ⟨.payload slot width v p, bits, k⟩
      ⟨.halted none, [], k + (decodePayloadRuntimeCosted width bits).2⟩ := by
  induction width generalizing bits v p k with
  | zero => simp [decodePayloadRuntimeCosted] at h
  | succ width ih =>
      cases bits with
      | nil => exact Relation.ReflTransGen.single rfl
      | cons b bs =>
          simp only [decodePayloadRuntimeCosted] at h ⊢
          generalize hr : decodePayloadRuntimeCosted width bs = r at h ⊢
          rcases r with ⟨result, cost⟩
          cases result with
          | some pair =>
              rcases pair with ⟨a, t⟩
              simp at h
          | none =>
              have hs : (decodePayloadRuntimeCosted width bs).1 = none := by rw [hr]
              have key := ih (bits := bs) (v := v + if b then p else 0) (p := 2 * p)
                (k := k + 1) hs
              rw [hr] at key
              simp only at key
              have e : k + 1 + cost = k + (cost + 1) := by omega
              rw [e] at key
              exact Relation.ReflTransGen.head
                (b := ⟨.payload slot width (v + if b then p else 0) (2 * p), bs, k + 1⟩) rfl key

/-- A compact field that decodes to `m` takes the machine from the start of the
field to the field's continuation, consuming exactly the parser's inspections. -/
theorem bitReaches_field_some (slot : FieldSlot) {bits : List Bool} {k m : Nat}
    {rest : List Bool} (h : (decodeNatCompactRuntimeCosted bits).1 = some (m, rest)) :
    BitReaches dec ⟨.width slot 0, bits, k⟩
      (fieldDone dec slot m rest (k + (decodeNatCompactRuntimeCosted bits).2)) := by
  unfold decodeNatCompactRuntimeCosted at h ⊢
  generalize hw : decodeCompactWidthRuntimeCosted bits = wr at h ⊢
  rcases wr with ⟨wo, wc⟩
  cases wo with
  | none => simp at h
  | some pair =>
      rcases pair with ⟨width, rest0⟩
      simp only at h ⊢
      generalize hp : decodePayloadRuntimeCosted width rest0 = pr at h ⊢
      rcases pr with ⟨po, pc⟩
      cases po with
      | none => simp at h
      | some res =>
          rcases res with ⟨raw, tail⟩
          by_cases hz : raw = 0
          · simp [hz] at h
          · simp [hz] at h
            obtain ⟨rfl, rfl⟩ := h
            have hws : (decodeCompactWidthRuntimeCosted bits).1 = some (width, rest0) := by
              rw [hw]
            have hps : (decodePayloadRuntimeCosted width rest0).1 = some (raw, tail) := by
              rw [hp]
            have s1 := bitReaches_width_some dec slot (w := 0) (k := k) hws
            rw [hw] at s1
            simp only [Nat.zero_add] at s1
            have s2 := bitReaches_payload_some dec slot (v := 0) (p := 1) (k := k + wc) hps
            rw [hp] at s2
            simp only [Nat.zero_add, Nat.one_mul] at s2
            have s3 : BitReaches dec ⟨.payload slot 0 raw (2 ^ width), tail, k + wc + pc⟩
                (fieldDone dec slot (raw - 1) tail (k + (wc + pc))) := by
              refine Relation.ReflTransGen.single ?_
              show finishField dec slot raw tail (k + wc + pc) = _
              rw [finishField, if_neg hz, Nat.add_assoc]
            exact Relation.ReflTransGen.trans (Relation.ReflTransGen.trans s1 s2) s3

/-- A compact field that the parser rejects takes the machine to a rejecting
halted state, consuming exactly the parser's inspections. -/
theorem bitReaches_field_none (slot : FieldSlot) {bits : List Bool} {k : Nat}
    (h : (decodeNatCompactRuntimeCosted bits).1 = none) :
    ∃ rest, BitReaches dec ⟨.width slot 0, bits, k⟩
      ⟨.halted none, rest, k + (decodeNatCompactRuntimeCosted bits).2⟩ := by
  unfold decodeNatCompactRuntimeCosted at h ⊢
  generalize hw : decodeCompactWidthRuntimeCosted bits = wr at h ⊢
  rcases wr with ⟨wo, wc⟩
  cases wo with
  | none =>
      have hwn : (decodeCompactWidthRuntimeCosted bits).1 = none := by rw [hw]
      have s1 := bitReaches_width_none dec slot (w := 0) (k := k) hwn
      rw [hw] at s1
      exact ⟨[], s1⟩
  | some pair =>
      rcases pair with ⟨width, rest0⟩
      simp only at h ⊢
      have hws : (decodeCompactWidthRuntimeCosted bits).1 = some (width, rest0) := by rw [hw]
      have s1 := bitReaches_width_some dec slot (w := 0) (k := k) hws
      rw [hw] at s1
      simp only [Nat.zero_add] at s1
      generalize hp : decodePayloadRuntimeCosted width rest0 = pr at h ⊢
      rcases pr with ⟨po, pc⟩
      cases po with
      | none =>
          have hpn : (decodePayloadRuntimeCosted width rest0).1 = none := by rw [hp]
          have s2 := bitReaches_payload_none dec slot (v := 0) (p := 1) (k := k + wc) hpn
          rw [hp] at s2
          refine ⟨[], Relation.ReflTransGen.trans s1 ?_⟩
          simpa [Nat.add_assoc] using s2
      | some res =>
          rcases res with ⟨raw, tail⟩
          have hz : raw = 0 := by
            by_contra hz
            simp [hz] at h
          subst hz
          have hps : (decodePayloadRuntimeCosted width rest0).1 = some (0, tail) := by rw [hp]
          have s2 := bitReaches_payload_some dec slot (v := 0) (p := 1) (k := k + wc) hps
          rw [hp] at s2
          simp only [Nat.zero_add, Nat.one_mul, Nat.mul_zero] at s2
          refine ⟨tail, Relation.ReflTransGen.trans (Relation.ReflTransGen.trans s1 s2)
            (Relation.ReflTransGen.single ?_)⟩
          show finishField dec slot 0 tail (k + wc + pc) = _
          simp [finishField, Nat.add_assoc]

theorem bitReaches_words_some {count : Nat} {bits : List Bool} {acc : List Nat} {k : Nat}
    {ws : List Nat} {tail : List Bool}
    (h : (decodeWordsCompactRuntimeCosted count bits).1 = some (ws, tail)) :
    BitReaches dec (startWords dec count acc bits k)
      ⟨.halted ((dec (acc ++ ws)).map fun c => (c, tail)), tail,
        k + (decodeWordsCompactRuntimeCosted count bits).2⟩ := by
  induction count generalizing bits acc k ws tail with
  | zero =>
      simp only [decodeWordsCompactRuntimeCosted, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact bitReaches_of_eq dec (by simp [startWords, decodeWordsCompactRuntimeCosted])
  | succ n ih =>
      unfold decodeWordsCompactRuntimeCosted at h ⊢
      generalize hf : decodeNatCompactRuntimeCosted bits = fr at h ⊢
      rcases fr with ⟨fo, fc⟩
      cases fo with
      | none => simp at h
      | some pair =>
          rcases pair with ⟨m, rest⟩
          simp only at h ⊢
          generalize ht : decodeWordsCompactRuntimeCosted n rest = tr at h ⊢
          rcases tr with ⟨tOpt, tc⟩
          cases tOpt with
          | none => simp at h
          | some pair =>
              rcases pair with ⟨ws', tail'⟩
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hfs : (decodeNatCompactRuntimeCosted bits).1 = some (m, rest) := by rw [hf]
              have hts : (decodeWordsCompactRuntimeCosted n rest).1 = some (ws', tail') := by
                rw [ht]
              have s1 := bitReaches_field_some dec (.word n acc) (k := k) hfs
              rw [hf] at s1
              have s2 := ih (bits := rest) (acc := acc ++ [m]) (k := k + fc) (ws := ws')
                (tail := tail') hts
              rw [ht] at s2
              have e1 : acc ++ [m] ++ ws' = acc ++ m :: ws' := by simp
              have e2 : k + fc + (some (ws', tail'), tc).2 = k + (fc + tc) := by
                simp [Nat.add_assoc]
              rw [e1, e2] at s2
              exact Relation.ReflTransGen.trans s1 s2

theorem bitReaches_words_none {count : Nat} {bits : List Bool} {acc : List Nat} {k : Nat}
    (h : (decodeWordsCompactRuntimeCosted count bits).1 = none) :
    ∃ rest, BitReaches dec (startWords dec count acc bits k)
      ⟨.halted none, rest, k + (decodeWordsCompactRuntimeCosted count bits).2⟩ := by
  induction count generalizing bits acc k with
  | zero => simp [decodeWordsCompactRuntimeCosted] at h
  | succ n ih =>
      unfold decodeWordsCompactRuntimeCosted at h ⊢
      generalize hf : decodeNatCompactRuntimeCosted bits = fr at h ⊢
      rcases fr with ⟨fo, fc⟩
      cases fo with
      | none =>
          have hfn : (decodeNatCompactRuntimeCosted bits).1 = none := by rw [hf]
          obtain ⟨rest, s1⟩ := bitReaches_field_none dec (.word n acc) (k := k) hfn
          rw [hf] at s1
          exact ⟨rest, s1⟩
      | some pair =>
          rcases pair with ⟨m, rest⟩
          simp only at h ⊢
          generalize ht : decodeWordsCompactRuntimeCosted n rest = tr at h ⊢
          rcases tr with ⟨tOpt, tc⟩
          cases tOpt with
          | some pair =>
              rcases pair with ⟨a, t⟩
              simp at h
          | none =>
              have hfs : (decodeNatCompactRuntimeCosted bits).1 = some (m, rest) := by rw [hf]
              have htn : (decodeWordsCompactRuntimeCosted n rest).1 = none := by rw [ht]
              have s1 := bitReaches_field_some dec (.word n acc) (k := k) hfs
              rw [hf] at s1
              obtain ⟨rest', s2⟩ := ih (bits := rest) (acc := acc ++ [m]) (k := k + fc) htn
              rw [ht] at s2
              refine ⟨rest', Relation.ReflTransGen.trans s1 ?_⟩
              simpa [Nat.add_assoc] using s2

/-! ## Agreement with the recursive parser -/

/-- Started on any input, the machine reaches the halted state whose output is
the decoder applied to the parsed word stream, with the consumed-cell counter
equal to the recursive decoders' inspection count. -/
theorem bitReaches_wordStream (bits : List Bool) :
    ∃ rest, BitReaches dec (bitInit bits)
      ⟨.halted (streamOutput dec (wordStreamRuntime bits).1), rest,
        (wordStreamRuntime bits).2⟩ := by
  unfold wordStreamRuntime
  generalize hc : decodeNatCompactRuntimeCosted bits = cr
  rcases cr with ⟨co, cc⟩
  cases co with
  | none =>
      have hcn : (decodeNatCompactRuntimeCosted bits).1 = none := by rw [hc]
      obtain ⟨rest, s1⟩ := bitReaches_field_none dec .count (k := 0) hcn
      rw [hc] at s1
      exact ⟨rest, by simpa [streamOutput] using s1⟩
  | some pair =>
      rcases pair with ⟨wordCount, rest⟩
      have hcs : (decodeNatCompactRuntimeCosted bits).1 = some (wordCount, rest) := by rw [hc]
      have s1 := bitReaches_field_some dec .count (k := 0) hcs
      rw [hc] at s1
      simp only
      generalize hw : decodeWordsCompactRuntimeCosted wordCount rest = wr
      rcases wr with ⟨wo, wc⟩
      cases wo with
      | none =>
          have hwn : (decodeWordsCompactRuntimeCosted wordCount rest).1 = none := by rw [hw]
          obtain ⟨rest', s2⟩ := bitReaches_words_none dec (acc := []) (k := 0 + cc) hwn
          rw [hw] at s2
          exact ⟨rest', Relation.ReflTransGen.trans s1 (by simpa [streamOutput] using s2)⟩
      | some pair =>
          rcases pair with ⟨ws, tail⟩
          have hws : (decodeWordsCompactRuntimeCosted wordCount rest).1 = some (ws, tail) := by
            rw [hw]
          have s2 := bitReaches_words_some dec (acc := []) (k := 0 + cc) hws
          rw [hw] at s2
          exact ⟨tail, Relation.ReflTransGen.trans s1 (by simpa [streamOutput] using s2)⟩

/-- The machine run with fuel `3 * bits.length + 1` has halted, with the stream
output, the unread suffix `bits.drop c`, and the consumed count `c` of the
recursive decoders. -/
theorem runBitMachine_eq_of_wordStream (bits : List Bool) :
    runBitMachine dec bits =
      ⟨.halted (streamOutput dec (wordStreamRuntime bits).1),
        bits.drop (wordStreamRuntime bits).2, (wordStreamRuntime bits).2⟩ := by
  obtain ⟨rest, h⟩ := bitReaches_wordStream dec bits
  obtain ⟨pre, hpre, hk⟩ := bitReaches_input_suffix dec h
  change bits = pre ++ rest at hpre
  change (wordStreamRuntime bits).2 = 0 + pre.length at hk
  have hrest : rest = bits.drop (wordStreamRuntime bits).2 := by
    rw [hk, Nat.zero_add, hpre, List.drop_left]
  rw [hrest] at h
  exact runBits_eq_of_bitReaches dec h _ (Nat.le_of_eq rfl)

end Machine

/-! ## The certificate parser -/

/-- `deserializeBitsPrefixRuntimeWork` is the word stream followed by
`deserialize`, and its bit inspections are the word stream's. -/
theorem deserializeBitsPrefixRuntimeWork_eq_wordStream (bits : List Bool) :
    (deserializeBitsPrefixRuntimeWork bits).1 =
        streamOutput deserialize (wordStreamRuntime bits).1 ∧
      (deserializeBitsPrefixRuntimeWork bits).2.bitInspections = (wordStreamRuntime bits).2 := by
  unfold deserializeBitsPrefixRuntimeWork wordStreamRuntime
  generalize decodeNatCompactRuntimeCosted bits = cr
  rcases cr with ⟨co, cc⟩
  cases co with
  | none => exact ⟨rfl, rfl⟩
  | some pair =>
      rcases pair with ⟨wordCount, rest⟩
      simp only
      generalize decodeWordsCompactRuntimeCosted wordCount rest = wr
      rcases wr with ⟨wo, wc⟩
      cases wo with
      | none => exact ⟨rfl, rfl⟩
      | some pair =>
          rcases pair with ⟨ws, tail⟩
          refine ⟨?_, rfl⟩
          show (match (deserializeCosted ws).1 with
              | none => none
              | some c => some (c, tail)) = (deserialize ws).map fun c => (c, tail)
          rw [deserializeCosted_fst]
          cases deserialize ws <;> rfl

theorem bitReaches_deserializeBitsPrefixRuntimeWork (bits : List Bool) :
    ∃ rest, BitReaches deserialize (bitInit bits)
      ⟨.halted (deserializeBitsPrefixRuntimeWork bits).1, rest,
        (deserializeBitsPrefixRuntimeWork bits).2.bitInspections⟩ := by
  obtain ⟨h1, h2⟩ := deserializeBitsPrefixRuntimeWork_eq_wordStream bits
  rw [h1, h2]
  exact bitReaches_wordStream deserialize bits

/-- P4.1: on every input, the machine run for `3 * bits.length + 1` steps has
halted with the recursive parser's result, and the parser's `bitInspections` is
the machine's consumed-cell count; the unread suffix is `bits.drop` of it. -/
theorem runBitMachine_deserialize_eq (bits : List Bool) :
    runBitMachine deserialize bits =
      ⟨.halted (deserializeBitsPrefixRuntimeWork bits).1,
        bits.drop (deserializeBitsPrefixRuntimeWork bits).2.bitInspections,
        (deserializeBitsPrefixRuntimeWork bits).2.bitInspections⟩ := by
  obtain ⟨h1, h2⟩ := deserializeBitsPrefixRuntimeWork_eq_wordStream bits
  rw [h1, h2]
  exact runBitMachine_eq_of_wordStream deserialize bits

theorem deserializeBitsPrefixRuntimeWork_eq_machine (bits : List Bool) :
    (runBitMachine deserialize bits).phase = .halted (deserializeBitsPrefixRuntimeWork bits).1 ∧
      (deserializeBitsPrefixRuntimeWork bits).2.bitInspections =
        (runBitMachine deserialize bits).consumed := by
  rw [runBitMachine_deserialize_eq]
  exact ⟨rfl, rfl⟩

/-- A canonical certificate followed by any suffix: the machine accepts it,
consumes exactly `serializedBinaryBits c` cells, and leaves the suffix unread. -/
theorem runBitMachine_serializeBits_append (c : ExtractionCertificate) (tail : List Bool) :
    runBitMachine deserialize (serializeBits c ++ tail) =
      ⟨.halted (some (c, tail)), tail, serializedBinaryBits c⟩ := by
  rw [runBitMachine_deserialize_eq]
  obtain ⟨h1, h2⟩ := deserializeBitsPrefixRuntimeWork_serializeBits_append c tail
  rw [h1, h2]
  simp only [serializedBinaryBits, List.drop_left]

/-! ## Rejection controls -/

/-- Control: the empty input is rejected with no cell read. -/
theorem runBitMachine_nil :
    runBitMachine deserialize [] = ⟨.halted none, [], 0⟩ := rfl

/-- Control: a zero-width field has raw value zero; one cell is read. -/
theorem runBitMachine_zero_width :
    runBitMachine deserialize [false] = ⟨.halted none, [], 1⟩ := rfl

/-- Control: a width prefix cut off by the end of the input; every cell is read. -/
theorem runBitMachine_truncated_width :
    runBitMachine deserialize [true, true] = ⟨.halted none, [], 2⟩ := rfl

/-- Control: an all-zero payload is rejected after three cells; the last two
cells stay unread. -/
theorem runBitMachine_zero_payload :
    runBitMachine deserialize [true, false, false, true, true] =
      ⟨.halted none, [true, true], 3⟩ := rfl

end OperatorKO7.Meta.OperationalInexpressibility.CertificateBitMachine
